-- Prove2me | solution 1 for syracuse_descends_range_1630514_1632514
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:14:33.315194+00:00
-- url     : https://prove2.me/submissions/3ab1ce8b-2bc4-4bce-a18e-3da339e4869c

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


theorem B5505029 : Blo 1630514 5505029 := bbase (se 4 (by rfl) ⟨516096, by rfl⟩ : syracuseStep 5505029 = 1032193) (by norm_num)
theorem B3670037 : Blo 1630514 3670037 := bbase (se 6 (by rfl) ⟨86016, by rfl⟩ : syracuseStep 3670037 = 172033) (by norm_num)
theorem B1835041 : Blo 1630514 1835041 := bbase (se 2 (by rfl) ⟨688140, by rfl⟩ : syracuseStep 1835041 = 1376281) (by norm_num)
theorem B6193205 : Blo 1630514 6193205 := bbase (se 5 (by rfl) ⟨290306, by rfl⟩ : syracuseStep 6193205 = 580613) (by norm_num)
theorem B1835077 : Blo 1630514 1835077 := bbase (se 4 (by rfl) ⟨172038, by rfl⟩ : syracuseStep 1835077 = 344077) (by norm_num)
theorem B2064457 : Blo 1630514 2064457 := bbase (se 2 (by rfl) ⟨774171, by rfl⟩ : syracuseStep 2064457 = 1548343) (by norm_num)
theorem B2752589 : Blo 1630514 2752589 := bbase (se 3 (by rfl) ⟨516110, by rfl⟩ : syracuseStep 2752589 = 1032221) (by norm_num)
theorem B4128853 : Blo 1630514 4128853 := bbase (se 8 (by rfl) ⟨24192, by rfl⟩ : syracuseStep 4128853 = 48385) (by norm_num)
theorem B5226581 : Blo 1630514 5226581 := bbase (se 8 (by rfl) ⟨30624, by rfl⟩ : syracuseStep 5226581 = 61249) (by norm_num)
theorem B3670109 : Blo 1630514 3670109 := bbase (se 3 (by rfl) ⟨688145, by rfl⟩ : syracuseStep 3670109 = 1376291) (by norm_num)
theorem B1835113 : Blo 1630514 1835113 := bbase (se 2 (by rfl) ⟨688167, by rfl⟩ : syracuseStep 1835113 = 1376335) (by norm_num)
theorem B3096701 : Blo 1630514 3096701 := bbase (se 3 (by rfl) ⟨580631, by rfl⟩ : syracuseStep 3096701 = 1161263) (by norm_num)
theorem B1835149 : Blo 1630514 1835149 := bbase (se 3 (by rfl) ⟨344090, by rfl⟩ : syracuseStep 1835149 = 688181) (by norm_num)
theorem B2941085 : Blo 1630514 2941085 := bbase (se 3 (by rfl) ⟨551453, by rfl⟩ : syracuseStep 2941085 = 1102907) (by norm_num)
theorem B3670181 : Blo 1630514 3670181 := bbase (se 4 (by rfl) ⟨344079, by rfl⟩ : syracuseStep 3670181 = 688159) (by norm_num)
theorem B1835185 : Blo 1630514 1835185 := bbase (se 2 (by rfl) ⟨688194, by rfl⟩ : syracuseStep 1835185 = 1376389) (by norm_num)
theorem B4128965 : Blo 1630514 4128965 := bbase (se 4 (by rfl) ⟨387090, by rfl⟩ : syracuseStep 4128965 = 774181) (by norm_num)
theorem B2752717 : Blo 1630514 2752717 := bbase (se 3 (by rfl) ⟨516134, by rfl⟩ : syracuseStep 2752717 = 1032269) (by norm_num)
theorem B4243661 : Blo 1630514 4243661 := bbase (se 3 (by rfl) ⟨795686, by rfl⟩ : syracuseStep 4243661 = 1591373) (by norm_num)
theorem B1835221 : Blo 1630514 1835221 := bbase (se 7 (by rfl) ⟨21506, by rfl⟩ : syracuseStep 1835221 = 43013) (by norm_num)
theorem B1859809 : Blo 1630514 1859809 := bbase (se 2 (by rfl) ⟨697428, by rfl⟩ : syracuseStep 1859809 = 1394857) (by norm_num)
theorem B3670253 : Blo 1630514 3670253 := bbase (se 3 (by rfl) ⟨688172, by rfl⟩ : syracuseStep 3670253 = 1376345) (by norm_num)
theorem B2515181 : Blo 1630514 2515181 := bbase (se 3 (by rfl) ⟨471596, by rfl⟩ : syracuseStep 2515181 = 943193) (by norm_num)
theorem B2064629 : Blo 1630514 2064629 := bbase (se 5 (by rfl) ⟨96779, by rfl⟩ : syracuseStep 2064629 = 193559) (by norm_num)
theorem B1835257 : Blo 1630514 1835257 := bbase (se 2 (by rfl) ⟨688221, by rfl⟩ : syracuseStep 1835257 = 1376443) (by norm_num)
theorem B1835293 : Blo 1630514 1835293 := bbase (se 3 (by rfl) ⟨344117, by rfl⟩ : syracuseStep 1835293 = 688235) (by norm_num)
theorem B2752805 : Blo 1630514 2752805 := bbase (se 4 (by rfl) ⟨258075, by rfl⟩ : syracuseStep 2752805 = 516151) (by norm_num)
theorem B2064685 : Blo 1630514 2064685 := bbase (se 3 (by rfl) ⟨387128, by rfl⟩ : syracuseStep 2064685 = 774257) (by norm_num)
theorem B3670325 : Blo 1630514 3670325 := bbase (se 5 (by rfl) ⟨172046, by rfl⟩ : syracuseStep 3670325 = 344093) (by norm_num)
theorem B1835329 : Blo 1630514 1835329 := bbase (se 2 (by rfl) ⟨688248, by rfl⟩ : syracuseStep 1835329 = 1376497) (by norm_num)
theorem B6193493 : Blo 1630514 6193493 := bbase (se 10 (by rfl) ⟨9072, by rfl⟩ : syracuseStep 6193493 = 18145) (by norm_num)
theorem B1835365 : Blo 1630514 1835365 := bbase (se 4 (by rfl) ⟨172065, by rfl⟩ : syracuseStep 1835365 = 344131) (by norm_num)
theorem B3670397 : Blo 1630514 3670397 := bbase (se 3 (by rfl) ⟨688199, by rfl⟩ : syracuseStep 3670397 = 1376399) (by norm_num)
theorem B4129157 : Blo 1630514 4129157 := bbase (se 4 (by rfl) ⟨387108, by rfl⟩ : syracuseStep 4129157 = 774217) (by norm_num)
theorem B1835401 : Blo 1630514 1835401 := bbase (se 2 (by rfl) ⟨688275, by rfl⟩ : syracuseStep 1835401 = 1376551) (by norm_num)
theorem B2064781 : Blo 1630514 2064781 := bbase (se 3 (by rfl) ⟨387146, by rfl⟩ : syracuseStep 2064781 = 774293) (by norm_num)
theorem B17629589 : Blo 1630514 17629589 := bbase (se 6 (by rfl) ⟨413193, by rfl⟩ : syracuseStep 17629589 = 826387) (by norm_num)
theorem B2752933 : Blo 1630514 2752933 := bbase (se 4 (by rfl) ⟨258087, by rfl⟩ : syracuseStep 2752933 = 516175) (by norm_num)
theorem B1835437 : Blo 1630514 1835437 := bbase (se 3 (by rfl) ⟨344144, by rfl⟩ : syracuseStep 1835437 = 688289) (by norm_num)
theorem B5505461 : Blo 1630514 5505461 := bbase (se 5 (by rfl) ⟨258068, by rfl⟩ : syracuseStep 5505461 = 516137) (by norm_num)
theorem B2941373 : Blo 1630514 2941373 := bbase (se 3 (by rfl) ⟨551507, by rfl⟩ : syracuseStep 2941373 = 1103015) (by norm_num)
theorem B3670469 : Blo 1630514 3670469 := bbase (se 4 (by rfl) ⟨344106, by rfl⟩ : syracuseStep 3670469 = 688213) (by norm_num)
theorem B2613701 : Blo 1630514 2613701 := bbase (se 4 (by rfl) ⟨245034, by rfl⟩ : syracuseStep 2613701 = 490069) (by norm_num)
theorem B1835473 : Blo 1630514 1835473 := bbase (se 2 (by rfl) ⟨688302, by rfl⟩ : syracuseStep 1835473 = 1376605) (by norm_num)
theorem B1835509 : Blo 1630514 1835509 := bbase (se 5 (by rfl) ⟨86039, by rfl⟩ : syracuseStep 1835509 = 172079) (by norm_num)
theorem B2753021 : Blo 1630514 2753021 := bbase (se 3 (by rfl) ⟨516191, by rfl⟩ : syracuseStep 2753021 = 1032383) (by norm_num)
theorem B3670541 : Blo 1630514 3670541 := bbase (se 3 (by rfl) ⟨688226, by rfl⟩ : syracuseStep 3670541 = 1376453) (by norm_num)
theorem B1835545 : Blo 1630514 1835545 := bbase (se 2 (by rfl) ⟨688329, by rfl⟩ : syracuseStep 1835545 = 1376659) (by norm_num)
theorem B2064953 : Blo 1630514 2064953 := bbase (se 2 (by rfl) ⟨774357, by rfl⟩ : syracuseStep 2064953 = 1548715) (by norm_num)
theorem B1835581 : Blo 1630514 1835581 := bbase (se 3 (by rfl) ⟨344171, by rfl⟩ : syracuseStep 1835581 = 688343) (by norm_num)
theorem B11756117 : Blo 1630514 11756117 := bbase (se 8 (by rfl) ⟨68883, by rfl⟩ : syracuseStep 11756117 = 137767) (by norm_num)
theorem B3670613 : Blo 1630514 3670613 := bbase (se 8 (by rfl) ⟨21507, by rfl⟩ : syracuseStep 3670613 = 43015) (by norm_num)
theorem B1835617 : Blo 1630514 1835617 := bbase (se 2 (by rfl) ⟨688356, by rfl⟩ : syracuseStep 1835617 = 1376713) (by norm_num)
theorem B2065009 : Blo 1630514 2065009 := bbase (se 2 (by rfl) ⟨774378, by rfl⟩ : syracuseStep 2065009 = 1548757) (by norm_num)
theorem B2753149 : Blo 1630514 2753149 := bbase (se 3 (by rfl) ⟨516215, by rfl⟩ : syracuseStep 2753149 = 1032431) (by norm_num)
theorem B1835653 : Blo 1630514 1835653 := bbase (se 4 (by rfl) ⟨172092, by rfl⟩ : syracuseStep 1835653 = 344185) (by norm_num)
theorem B3670685 : Blo 1630514 3670685 := bbase (se 3 (by rfl) ⟨688253, by rfl⟩ : syracuseStep 3670685 = 1376507) (by norm_num)
theorem B1835689 : Blo 1630514 1835689 := bbase (se 2 (by rfl) ⟨688383, by rfl⟩ : syracuseStep 1835689 = 1376767) (by norm_num)
theorem B1835725 : Blo 1630514 1835725 := bbase (se 3 (by rfl) ⟨344198, by rfl⟩ : syracuseStep 1835725 = 688397) (by norm_num)
theorem B2065105 : Blo 1630514 2065105 := bbase (se 2 (by rfl) ⟨774414, by rfl⟩ : syracuseStep 2065105 = 1548829) (by norm_num)
theorem B2753237 : Blo 1630514 2753237 := bbase (se 7 (by rfl) ⟨32264, by rfl⟩ : syracuseStep 2753237 = 64529) (by norm_num)
theorem B4129501 : Blo 1630514 4129501 := bbase (se 3 (by rfl) ⟨774281, by rfl⟩ : syracuseStep 4129501 = 1548563) (by norm_num)
theorem B3670757 : Blo 1630514 3670757 := bbase (se 4 (by rfl) ⟨344133, by rfl⟩ : syracuseStep 3670757 = 688267) (by norm_num)
theorem B2613989 : Blo 1630514 2613989 := bbase (se 4 (by rfl) ⟨245061, by rfl⟩ : syracuseStep 2613989 = 490123) (by norm_num)
theorem B1835761 : Blo 1630514 1835761 := bbase (se 2 (by rfl) ⟨688410, by rfl⟩ : syracuseStep 1835761 = 1376821) (by norm_num)
theorem B5300981 : Blo 1630514 5300981 := bbase (se 5 (by rfl) ⟨248483, by rfl⟩ : syracuseStep 5300981 = 496967) (by norm_num)
theorem B1835797 : Blo 1630514 1835797 := bbase (se 6 (by rfl) ⟨43026, by rfl⟩ : syracuseStep 1835797 = 86053) (by norm_num)
theorem B3670829 : Blo 1630514 3670829 := bbase (se 3 (by rfl) ⟨688280, by rfl⟩ : syracuseStep 3670829 = 1376561) (by norm_num)
theorem B1835833 : Blo 1630514 1835833 := bbase (se 2 (by rfl) ⟨688437, by rfl⟩ : syracuseStep 1835833 = 1376875) (by norm_num)
theorem B4129613 : Blo 1630514 4129613 := bbase (se 3 (by rfl) ⟨774302, by rfl⟩ : syracuseStep 4129613 = 1548605) (by norm_num)
theorem B2753365 : Blo 1630514 2753365 := bbase (se 9 (by rfl) ⟨8066, by rfl⟩ : syracuseStep 2753365 = 16133) (by norm_num)
theorem B1835869 : Blo 1630514 1835869 := bbase (se 3 (by rfl) ⟨344225, by rfl⟩ : syracuseStep 1835869 = 688451) (by norm_num)
theorem B5505893 : Blo 1630514 5505893 := bbase (se 4 (by rfl) ⟨516177, by rfl⟩ : syracuseStep 5505893 = 1032355) (by norm_num)
theorem B3097453 : Blo 1630514 3097453 := bbase (se 3 (by rfl) ⟨580772, by rfl⟩ : syracuseStep 3097453 = 1161545) (by norm_num)
theorem B3670901 : Blo 1630514 3670901 := bbase (se 5 (by rfl) ⟨172073, by rfl⟩ : syracuseStep 3670901 = 344147) (by norm_num)
theorem B6972277 : Blo 1630514 6972277 := bbase (se 5 (by rfl) ⟨326825, by rfl⟩ : syracuseStep 6972277 = 653651) (by norm_num)
theorem B2065277 : Blo 1630514 2065277 := bbase (se 3 (by rfl) ⟨387239, by rfl⟩ : syracuseStep 2065277 = 774479) (by norm_num)
theorem B1835905 : Blo 1630514 1835905 := bbase (se 2 (by rfl) ⟨688464, by rfl⟩ : syracuseStep 1835905 = 1376929) (by norm_num)
theorem B6972293 : Blo 1630514 6972293 := bbase (se 4 (by rfl) ⟨653652, by rfl⟩ : syracuseStep 6972293 = 1307305) (by norm_num)
theorem B4645781 : Blo 1630514 4645781 := bbase (se 6 (by rfl) ⟨108885, by rfl⟩ : syracuseStep 4645781 = 217771) (by norm_num)
theorem B1835941 : Blo 1630514 1835941 := bbase (se 4 (by rfl) ⟨172119, by rfl⟩ : syracuseStep 1835941 = 344239) (by norm_num)
theorem B2753453 : Blo 1630514 2753453 := bbase (se 3 (by rfl) ⟨516272, by rfl⟩ : syracuseStep 2753453 = 1032545) (by norm_num)
theorem B2065333 : Blo 1630514 2065333 := bbase (se 5 (by rfl) ⟨96812, by rfl⟩ : syracuseStep 2065333 = 193625) (by norm_num)
theorem B3670973 : Blo 1630514 3670973 := bbase (se 3 (by rfl) ⟨688307, by rfl⟩ : syracuseStep 3670973 = 1376615) (by norm_num)
theorem B1835977 : Blo 1630514 1835977 := bbase (se 2 (by rfl) ⟨688491, by rfl⟩ : syracuseStep 1835977 = 1376983) (by norm_num)
theorem B13943765 : Blo 1630514 13943765 := bbase (se 7 (by rfl) ⟨163403, by rfl⟩ : syracuseStep 13943765 = 326807) (by norm_num)
theorem B1836013 : Blo 1630514 1836013 := bbase (se 3 (by rfl) ⟨344252, by rfl⟩ : syracuseStep 1836013 = 688505) (by norm_num)
theorem B3097597 : Blo 1630514 3097597 := bbase (se 3 (by rfl) ⟨580799, by rfl⟩ : syracuseStep 3097597 = 1161599) (by norm_num)
theorem B3671045 : Blo 1630514 3671045 := bbase (se 4 (by rfl) ⟨344160, by rfl⟩ : syracuseStep 3671045 = 688321) (by norm_num)
theorem B4129805 : Blo 1630514 4129805 := bbase (se 3 (by rfl) ⟨774338, by rfl⟩ : syracuseStep 4129805 = 1548677) (by norm_num)
theorem B1836049 : Blo 1630514 1836049 := bbase (se 2 (by rfl) ⟨688518, by rfl⟩ : syracuseStep 1836049 = 1377037) (by norm_num)
theorem B2065429 : Blo 1630514 2065429 := bbase (se 6 (by rfl) ⟨48408, by rfl⟩ : syracuseStep 2065429 = 96817) (by norm_num)
theorem B8258597 : Blo 1630514 8258597 := bbase (se 4 (by rfl) ⟨774243, by rfl⟩ : syracuseStep 8258597 = 1548487) (by norm_num)
theorem B2753581 : Blo 1630514 2753581 := bbase (se 3 (by rfl) ⟨516296, by rfl⟩ : syracuseStep 2753581 = 1032593) (by norm_num)
theorem B1836085 : Blo 1630514 1836085 := bbase (se 5 (by rfl) ⟨86066, by rfl⟩ : syracuseStep 1836085 = 172133) (by norm_num)
theorem B2204749 : Blo 1630514 2204749 := bbase (se 3 (by rfl) ⟨413390, by rfl⟩ : syracuseStep 2204749 = 826781) (by norm_num)
theorem B3671117 : Blo 1630514 3671117 := bbase (se 3 (by rfl) ⟨688334, by rfl⟩ : syracuseStep 3671117 = 1376669) (by norm_num)
theorem B1836121 : Blo 1630514 1836121 := bbase (se 2 (by rfl) ⟨688545, by rfl⟩ : syracuseStep 1836121 = 1377091) (by norm_num)
theorem B15672437 : Blo 1630514 15672437 := bbase (se 5 (by rfl) ⟨734645, by rfl⟩ : syracuseStep 15672437 = 1469291) (by norm_num)
theorem B1836157 : Blo 1630514 1836157 := bbase (se 3 (by rfl) ⟨344279, by rfl⟩ : syracuseStep 1836157 = 688559) (by norm_num)
theorem B2753669 : Blo 1630514 2753669 := bbase (se 4 (by rfl) ⟨258156, by rfl⟩ : syracuseStep 2753669 = 516313) (by norm_num)
theorem B2614405 : Blo 1630514 2614405 := bbase (se 4 (by rfl) ⟨245100, by rfl⟩ : syracuseStep 2614405 = 490201) (by norm_num)
theorem B3671189 : Blo 1630514 3671189 := bbase (se 6 (by rfl) ⟨86043, by rfl⟩ : syracuseStep 3671189 = 172087) (by norm_num)
theorem B3097757 : Blo 1630514 3097757 := bbase (se 3 (by rfl) ⟨580829, by rfl⟩ : syracuseStep 3097757 = 1161659) (by norm_num)
theorem B1836193 : Blo 1630514 1836193 := bbase (se 2 (by rfl) ⟨688572, by rfl⟩ : syracuseStep 1836193 = 1377145) (by norm_num)
theorem B2065601 : Blo 1630514 2065601 := bbase (se 2 (by rfl) ⟨774600, by rfl⟩ : syracuseStep 2065601 = 1549201) (by norm_num)
theorem B1836229 : Blo 1630514 1836229 := bbase (se 4 (by rfl) ⟨172146, by rfl⟩ : syracuseStep 1836229 = 344293) (by norm_num)
theorem B3671261 : Blo 1630514 3671261 := bbase (se 3 (by rfl) ⟨688361, by rfl⟩ : syracuseStep 3671261 = 1376723) (by norm_num)
theorem B1836265 : Blo 1630514 1836265 := bbase (se 2 (by rfl) ⟨688599, by rfl⟩ : syracuseStep 1836265 = 1377199) (by norm_num)
theorem B4408565 : Blo 1630514 4408565 := bbase (se 5 (by rfl) ⟨206651, by rfl⟩ : syracuseStep 4408565 = 413303) (by norm_num)
theorem B2065657 : Blo 1630514 2065657 := bbase (se 2 (by rfl) ⟨774621, by rfl⟩ : syracuseStep 2065657 = 1549243) (by norm_num)
theorem B2753797 : Blo 1630514 2753797 := bbase (se 4 (by rfl) ⟨258168, by rfl⟩ : syracuseStep 2753797 = 516337) (by norm_num)
theorem B1836301 : Blo 1630514 1836301 := bbase (se 3 (by rfl) ⟨344306, by rfl⟩ : syracuseStep 1836301 = 688613) (by norm_num)
theorem B1959185 : Blo 1630514 1959185 := bbase (se 2 (by rfl) ⟨734694, by rfl⟩ : syracuseStep 1959185 = 1469389) (by norm_num)
theorem B5506325 : Blo 1630514 5506325 := bbase (se 6 (by rfl) ⟨129054, by rfl⟩ : syracuseStep 5506325 = 258109) (by norm_num)
theorem B3671333 : Blo 1630514 3671333 := bbase (se 4 (by rfl) ⟨344187, by rfl⟩ : syracuseStep 3671333 = 688375) (by norm_num)
theorem B3097901 : Blo 1630514 3097901 := bbase (se 3 (by rfl) ⟨580856, by rfl⟩ : syracuseStep 3097901 = 1161713) (by norm_num)
theorem B1836337 : Blo 1630514 1836337 := bbase (se 2 (by rfl) ⟨688626, by rfl⟩ : syracuseStep 1836337 = 1377253) (by norm_num)
theorem B5580085 : Blo 1630514 5580085 := bbase (se 5 (by rfl) ⟨261566, by rfl⟩ : syracuseStep 5580085 = 523133) (by norm_num)
theorem B1836373 : Blo 1630514 1836373 := bbase (se 12 (by rfl) ⟨672, by rfl⟩ : syracuseStep 1836373 = 1345) (by norm_num)
theorem B2065753 : Blo 1630514 2065753 := bbase (se 2 (by rfl) ⟨774657, by rfl⟩ : syracuseStep 2065753 = 1549315) (by norm_num)
theorem B2753885 : Blo 1630514 2753885 := bbase (se 3 (by rfl) ⟨516353, by rfl⟩ : syracuseStep 2753885 = 1032707) (by norm_num)
theorem B4130149 : Blo 1630514 4130149 := bbase (se 4 (by rfl) ⟨387201, by rfl⟩ : syracuseStep 4130149 = 774403) (by norm_num)
theorem B3671405 : Blo 1630514 3671405 := bbase (se 3 (by rfl) ⟨688388, by rfl⟩ : syracuseStep 3671405 = 1376777) (by norm_num)
theorem B1836409 : Blo 1630514 1836409 := bbase (se 2 (by rfl) ⟨688653, by rfl⟩ : syracuseStep 1836409 = 1377307) (by norm_num)
theorem B3483037 : Blo 1630514 3483037 := bbase (se 3 (by rfl) ⟨653069, by rfl⟩ : syracuseStep 3483037 = 1306139) (by norm_num)
theorem B1836445 : Blo 1630514 1836445 := bbase (se 3 (by rfl) ⟨344333, by rfl⟩ : syracuseStep 1836445 = 688667) (by norm_num)
theorem B3671477 : Blo 1630514 3671477 := bbase (se 5 (by rfl) ⟨172100, by rfl⟩ : syracuseStep 3671477 = 344201) (by norm_num)
theorem B1836481 : Blo 1630514 1836481 := bbase (se 2 (by rfl) ⟨688680, by rfl⟩ : syracuseStep 1836481 = 1377361) (by norm_num)
theorem B4130261 : Blo 1630514 4130261 := bbase (se 7 (by rfl) ⟨48401, by rfl⟩ : syracuseStep 4130261 = 96803) (by norm_num)
theorem B2754013 : Blo 1630514 2754013 := bbase (se 3 (by rfl) ⟨516377, by rfl⟩ : syracuseStep 2754013 = 1032755) (by norm_num)
theorem B4408805 : Blo 1630514 4408805 := bbase (se 4 (by rfl) ⟨413325, by rfl⟩ : syracuseStep 4408805 = 826651) (by norm_num)
theorem B1836517 : Blo 1630514 1836517 := bbase (se 4 (by rfl) ⟨172173, by rfl⟩ : syracuseStep 1836517 = 344347) (by norm_num)
theorem B6194677 : Blo 1630514 6194677 := bbase (se 5 (by rfl) ⟨290375, by rfl⟩ : syracuseStep 6194677 = 580751) (by norm_num)
theorem B3671549 : Blo 1630514 3671549 := bbase (se 3 (by rfl) ⟨688415, by rfl⟩ : syracuseStep 3671549 = 1376831) (by norm_num)
theorem B2065925 : Blo 1630514 2065925 := bbase (se 4 (by rfl) ⟨193680, by rfl⟩ : syracuseStep 2065925 = 387361) (by norm_num)
theorem B1836553 : Blo 1630514 1836553 := bbase (se 2 (by rfl) ⟨688707, by rfl⟩ : syracuseStep 1836553 = 1377415) (by norm_num)
theorem B2041357 : Blo 1630514 2041357 := bbase (se 3 (by rfl) ⟨382754, by rfl⟩ : syracuseStep 2041357 = 765509) (by norm_num)
theorem B3581453 : Blo 1630514 3581453 := bbase (se 3 (by rfl) ⟨671522, by rfl⟩ : syracuseStep 3581453 = 1343045) (by norm_num)
theorem B3483157 : Blo 1630514 3483157 := bbase (se 6 (by rfl) ⟨81636, by rfl⟩ : syracuseStep 3483157 = 163273) (by norm_num)
theorem B2754101 : Blo 1630514 2754101 := bbase (se 5 (by rfl) ⟨129098, by rfl⟩ : syracuseStep 2754101 = 258197) (by norm_num)
theorem B2065981 : Blo 1630514 2065981 := bbase (se 3 (by rfl) ⟨387371, by rfl⟩ : syracuseStep 2065981 = 774743) (by norm_num)
theorem B1959493 : Blo 1630514 1959493 := bbase (se 4 (by rfl) ⟨183702, by rfl⟩ : syracuseStep 1959493 = 367405) (by norm_num)
theorem B3671621 : Blo 1630514 3671621 := bbase (se 4 (by rfl) ⟨344214, by rfl⟩ : syracuseStep 3671621 = 688429) (by norm_num)
theorem B3098189 : Blo 1630514 3098189 := bbase (se 3 (by rfl) ⟨580910, by rfl⟩ : syracuseStep 3098189 = 1161821) (by norm_num)
theorem B5883509 : Blo 1630514 5883509 := bbase (se 5 (by rfl) ⟨275789, by rfl⟩ : syracuseStep 5883509 = 551579) (by norm_num)
theorem B3671693 : Blo 1630514 3671693 := bbase (se 3 (by rfl) ⟨688442, by rfl⟩ : syracuseStep 3671693 = 1376885) (by norm_num)
theorem B4130453 : Blo 1630514 4130453 := bbase (se 6 (by rfl) ⟨96807, by rfl⟩ : syracuseStep 4130453 = 193615) (by norm_num)
theorem B2066077 : Blo 1630514 2066077 := bbase (se 3 (by rfl) ⟨387389, by rfl⟩ : syracuseStep 2066077 = 774779) (by norm_num)
theorem B4245157 : Blo 1630514 4245157 := bbase (se 4 (by rfl) ⟨397983, by rfl⟩ : syracuseStep 4245157 = 795967) (by norm_num)
theorem B2754229 : Blo 1630514 2754229 := bbase (se 5 (by rfl) ⟨129104, by rfl⟩ : syracuseStep 2754229 = 258209) (by norm_num)
theorem B5506757 : Blo 1630514 5506757 := bbase (se 4 (by rfl) ⟨516258, by rfl⟩ : syracuseStep 5506757 = 1032517) (by norm_num)
theorem B3671765 : Blo 1630514 3671765 := bbase (se 7 (by rfl) ⟨43028, by rfl⟩ : syracuseStep 3671765 = 86057) (by norm_num)
theorem B3098341 : Blo 1630514 3098341 := bbase (se 4 (by rfl) ⟨290469, by rfl⟩ : syracuseStep 3098341 = 580939) (by norm_num)
theorem B2754317 : Blo 1630514 2754317 := bbase (se 3 (by rfl) ⟨516434, by rfl⟩ : syracuseStep 2754317 = 1032869) (by norm_num)
theorem B3483413 : Blo 1630514 3483413 := bbase (se 6 (by rfl) ⟨81642, by rfl⟩ : syracuseStep 3483413 = 163285) (by norm_num)
theorem B3671837 : Blo 1630514 3671837 := bbase (se 3 (by rfl) ⟨688469, by rfl⟩ : syracuseStep 3671837 = 1376939) (by norm_num)
theorem B6194981 : Blo 1630514 6194981 := bbase (se 4 (by rfl) ⟨580779, by rfl⟩ : syracuseStep 6194981 = 1161559) (by norm_num)
theorem B3671909 : Blo 1630514 3671909 := bbase (se 4 (by rfl) ⟨344241, by rfl⟩ : syracuseStep 3671909 = 688483) (by norm_num)
theorem B2754445 : Blo 1630514 2754445 := bbase (se 3 (by rfl) ⟨516458, by rfl⟩ : syracuseStep 2754445 = 1032917) (by norm_num)
theorem B4532117 : Blo 1630514 4532117 := bbase (se 6 (by rfl) ⟨106221, by rfl⟩ : syracuseStep 4532117 = 212443) (by norm_num)
theorem B3671981 : Blo 1630514 3671981 := bbase (se 3 (by rfl) ⟨688496, by rfl⟩ : syracuseStep 3671981 = 1376993) (by norm_num)
theorem B7841717 : Blo 1630514 7841717 := bbase (se 5 (by rfl) ⟨367580, by rfl⟩ : syracuseStep 7841717 = 735161) (by norm_num)
theorem B1959877 : Blo 1630514 1959877 := bbase (se 4 (by rfl) ⟨183738, by rfl⟩ : syracuseStep 1959877 = 367477) (by norm_num)
theorem B1959881 : Blo 1630514 1959881 := bbase (se 2 (by rfl) ⟨734955, by rfl⟩ : syracuseStep 1959881 = 1469911) (by norm_num)
theorem B2754533 : Blo 1630514 2754533 := bbase (se 4 (by rfl) ⟨258237, by rfl⟩ : syracuseStep 2754533 = 516475) (by norm_num)
theorem B4130797 : Blo 1630514 4130797 := bbase (se 3 (by rfl) ⟨774524, by rfl⟩ : syracuseStep 4130797 = 1549049) (by norm_num)
theorem B3672053 : Blo 1630514 3672053 := bbase (se 5 (by rfl) ⟨172127, by rfl⟩ : syracuseStep 3672053 = 344255) (by norm_num)
theorem B10602485 : Blo 1630514 10602485 := bbase (se 5 (by rfl) ⟨496991, by rfl⟩ : syracuseStep 10602485 = 993983) (by norm_num)
theorem B3098645 : Blo 1630514 3098645 := bbase (se 6 (by rfl) ⟨72624, by rfl⟩ : syracuseStep 3098645 = 145249) (by norm_num)
theorem B4646965 : Blo 1630514 4646965 := bbase (se 5 (by rfl) ⟨217826, by rfl⟩ : syracuseStep 4646965 = 435653) (by norm_num)
theorem B3672125 : Blo 1630514 3672125 := bbase (se 3 (by rfl) ⟨688523, by rfl⟩ : syracuseStep 3672125 = 1377047) (by norm_num)
theorem B3139661 : Blo 1630514 3139661 := bbase (se 3 (by rfl) ⟨588686, by rfl⟩ : syracuseStep 3139661 = 1177373) (by norm_num)
theorem B3917909 : Blo 1630514 3917909 := bbase (se 8 (by rfl) ⟨22956, by rfl⟩ : syracuseStep 3917909 = 45913) (by norm_num)
theorem B3917917 : Blo 1630514 3917917 := bbase (se 3 (by rfl) ⟨734609, by rfl⟩ : syracuseStep 3917917 = 1469219) (by norm_num)
theorem B4130909 : Blo 1630514 4130909 := bbase (se 3 (by rfl) ⟨774545, by rfl⟩ : syracuseStep 4130909 = 1549091) (by norm_num)
theorem B2754661 : Blo 1630514 2754661 := bbase (se 4 (by rfl) ⟨258249, by rfl⟩ : syracuseStep 2754661 = 516499) (by norm_num)
theorem B5507189 : Blo 1630514 5507189 := bbase (se 5 (by rfl) ⟨258149, by rfl⟩ : syracuseStep 5507189 = 516299) (by norm_num)
theorem B3672197 : Blo 1630514 3672197 := bbase (se 4 (by rfl) ⟨344268, by rfl⟩ : syracuseStep 3672197 = 688537) (by norm_num)
theorem B18573461 : Blo 1630514 18573461 := bbase (se 6 (by rfl) ⟨435315, by rfl⟩ : syracuseStep 18573461 = 870631) (by norm_num)
theorem B3582133 : Blo 1630514 3582133 := bbase (se 5 (by rfl) ⟨167912, by rfl⟩ : syracuseStep 3582133 = 335825) (by norm_num)
theorem B2754749 : Blo 1630514 2754749 := bbase (se 3 (by rfl) ⟨516515, by rfl⟩ : syracuseStep 2754749 = 1033031) (by norm_num)
theorem B3672269 : Blo 1630514 3672269 := bbase (se 3 (by rfl) ⟨688550, by rfl⟩ : syracuseStep 3672269 = 1377101) (by norm_num)
theorem B4647125 : Blo 1630514 4647125 := bbase (se 7 (by rfl) ⟨54458, by rfl⟩ : syracuseStep 4647125 = 108917) (by norm_num)
theorem B3672341 : Blo 1630514 3672341 := bbase (se 6 (by rfl) ⟨86070, by rfl⟩ : syracuseStep 3672341 = 172141) (by norm_num)
theorem B4131101 : Blo 1630514 4131101 := bbase (se 3 (by rfl) ⟨774581, by rfl⟩ : syracuseStep 4131101 = 1549163) (by norm_num)
theorem B5228837 : Blo 1630514 5228837 := bbase (se 4 (by rfl) ⟨490203, by rfl⟩ : syracuseStep 5228837 = 980407) (by norm_num)
theorem B8259893 : Blo 1630514 8259893 := bbase (se 5 (by rfl) ⟨387182, by rfl⟩ : syracuseStep 8259893 = 774365) (by norm_num)
theorem B1960285 : Blo 1630514 1960285 := bbase (se 3 (by rfl) ⟨367553, by rfl⟩ : syracuseStep 1960285 = 735107) (by norm_num)
theorem B3672413 : Blo 1630514 3672413 := bbase (se 3 (by rfl) ⟨688577, by rfl⟩ : syracuseStep 3672413 = 1377155) (by norm_num)
theorem B3672485 : Blo 1630514 3672485 := bbase (se 4 (by rfl) ⟨344295, by rfl⟩ : syracuseStep 3672485 = 688591) (by norm_num)
theorem B4647365 : Blo 1630514 4647365 := bbase (se 4 (by rfl) ⟨435690, by rfl⟩ : syracuseStep 4647365 = 871381) (by norm_num)
theorem B3672557 : Blo 1630514 3672557 := bbase (se 3 (by rfl) ⟨688604, by rfl⟩ : syracuseStep 3672557 = 1377209) (by norm_num)
theorem B5507621 : Blo 1630514 5507621 := bbase (se 4 (by rfl) ⟨516339, by rfl⟩ : syracuseStep 5507621 = 1032679) (by norm_num)
theorem B2648621 : Blo 1630514 2648621 := bbase (se 3 (by rfl) ⟨496616, by rfl⟩ : syracuseStep 2648621 = 993233) (by norm_num)
theorem B3672629 : Blo 1630514 3672629 := bbase (se 5 (by rfl) ⟨172154, by rfl⟩ : syracuseStep 3672629 = 344309) (by norm_num)
theorem B3770957 : Blo 1630514 3770957 := bbase (se 3 (by rfl) ⟨707054, by rfl⟩ : syracuseStep 3770957 = 1414109) (by norm_num)
theorem B4131445 : Blo 1630514 4131445 := bbase (se 5 (by rfl) ⟨193661, by rfl⟩ : syracuseStep 4131445 = 387323) (by norm_num)
theorem B3672701 : Blo 1630514 3672701 := bbase (se 3 (by rfl) ⟨688631, by rfl⟩ : syracuseStep 3672701 = 1377263) (by norm_num)
theorem B4647557 : Blo 1630514 4647557 := bbase (se 4 (by rfl) ⟨435708, by rfl⟩ : syracuseStep 4647557 = 871417) (by norm_num)
theorem B3484301 : Blo 1630514 3484301 := bbase (se 3 (by rfl) ⟨653306, by rfl⟩ : syracuseStep 3484301 = 1306613) (by norm_num)
theorem B3672773 : Blo 1630514 3672773 := bbase (se 4 (by rfl) ⟨344322, by rfl⟩ : syracuseStep 3672773 = 688645) (by norm_num)
theorem B4131557 : Blo 1630514 4131557 := bbase (se 4 (by rfl) ⟨387333, by rfl⟩ : syracuseStep 4131557 = 774667) (by norm_num)
theorem B3672845 : Blo 1630514 3672845 := bbase (se 3 (by rfl) ⟨688658, by rfl⟩ : syracuseStep 3672845 = 1377317) (by norm_num)
theorem B2091845 : Blo 1630514 2091845 := bbase (se 4 (by rfl) ⟨196110, by rfl⟩ : syracuseStep 2091845 = 392221) (by norm_num)
theorem B3672917 : Blo 1630514 3672917 := bbase (se 9 (by rfl) ⟨10760, by rfl⟩ : syracuseStep 3672917 = 21521) (by norm_num)
theorem B3484541 : Blo 1630514 3484541 := bbase (se 3 (by rfl) ⟨653351, by rfl⟩ : syracuseStep 3484541 = 1306703) (by norm_num)
theorem B3672989 : Blo 1630514 3672989 := bbase (se 3 (by rfl) ⟨688685, by rfl⟩ : syracuseStep 3672989 = 1377371) (by norm_num)
theorem B4131749 : Blo 1630514 4131749 := bbase (se 4 (by rfl) ⟨387351, by rfl⟩ : syracuseStep 4131749 = 774703) (by norm_num)
theorem B5508053 : Blo 1630514 5508053 := bbase (se 7 (by rfl) ⟨64547, by rfl⟩ : syracuseStep 5508053 = 129095) (by norm_num)
theorem B3673061 : Blo 1630514 3673061 := bbase (se 4 (by rfl) ⟨344349, by rfl⟩ : syracuseStep 3673061 = 688699) (by norm_num)
theorem B3673133 : Blo 1630514 3673133 := bbase (se 3 (by rfl) ⟨688712, by rfl⟩ : syracuseStep 3673133 = 1377425) (by norm_num)
theorem B3533885 : Blo 1630514 3533885 := bbase (se 3 (by rfl) ⟨662603, by rfl⟩ : syracuseStep 3533885 = 1325207) (by norm_num)
theorem B3918917 : Blo 1630514 3918917 := bbase (se 4 (by rfl) ⟨367398, by rfl⟩ : syracuseStep 3918917 = 734797) (by norm_num)
theorem B6966485 : Blo 1630514 6966485 := bbase (se 7 (by rfl) ⟨81638, by rfl⟩ : syracuseStep 6966485 = 163277) (by norm_num)
theorem B7843061 : Blo 1630514 7843061 := bbase (se 5 (by rfl) ⟨367643, by rfl⟩ : syracuseStep 7843061 = 735287) (by norm_num)
theorem B4132093 : Blo 1630514 4132093 := bbase (se 3 (by rfl) ⟨774767, by rfl⟩ : syracuseStep 4132093 = 1549535) (by norm_num)
theorem B4132205 : Blo 1630514 4132205 := bbase (se 3 (by rfl) ⟨774788, by rfl⟩ : syracuseStep 4132205 = 1549577) (by norm_num)
theorem B3485045 : Blo 1630514 3485045 := bbase (se 5 (by rfl) ⟨163361, by rfl⟩ : syracuseStep 3485045 = 326723) (by norm_num)
theorem B3485053 : Blo 1630514 3485053 := bbase (se 3 (by rfl) ⟨653447, by rfl⟩ : syracuseStep 3485053 = 1306895) (by norm_num)
theorem B2321797 : Blo 1630514 2321797 := bbase (se 4 (by rfl) ⟨217668, by rfl⟩ : syracuseStep 2321797 = 435337) (by norm_num)
theorem B5508485 : Blo 1630514 5508485 := bbase (se 4 (by rfl) ⟨516420, by rfl⟩ : syracuseStep 5508485 = 1032841) (by norm_num)
theorem B2092501 : Blo 1630514 2092501 := bbase (se 7 (by rfl) ⟨24521, by rfl⟩ : syracuseStep 2092501 = 49043) (by norm_num)
theorem B8261189 : Blo 1630514 8261189 := bbase (se 4 (by rfl) ⟨774486, by rfl⟩ : syracuseStep 8261189 = 1548973) (by norm_num)
theorem B4648549 : Blo 1630514 4648549 := bbase (se 4 (by rfl) ⟨435801, by rfl⟩ : syracuseStep 4648549 = 871603) (by norm_num)
theorem B7835413 : Blo 1630514 7835413 := bbase (se 6 (by rfl) ⟨183642, by rfl⟩ : syracuseStep 7835413 = 367285) (by norm_num)
theorem B5508917 : Blo 1630514 5508917 := bbase (se 5 (by rfl) ⟨258230, by rfl⟩ : syracuseStep 5508917 = 516461) (by norm_num)
theorem B3919685 : Blo 1630514 3919685 := bbase (se 4 (by rfl) ⟨367470, by rfl⟩ : syracuseStep 3919685 = 734941) (by norm_num)
theorem B6197093 : Blo 1630514 6197093 := bbase (se 4 (by rfl) ⟨580977, by rfl⟩ : syracuseStep 6197093 = 1161955) (by norm_num)
theorem B2322389 : Blo 1630514 2322389 := bbase (se 7 (by rfl) ⟨27215, by rfl⟩ : syracuseStep 2322389 = 54431) (by norm_num)
theorem B2322469 : Blo 1630514 2322469 := bbase (se 4 (by rfl) ⟨217731, by rfl⟩ : syracuseStep 2322469 = 435463) (by norm_num)
theorem B6197381 : Blo 1630514 6197381 := bbase (se 4 (by rfl) ⟨581004, by rfl⟩ : syracuseStep 6197381 = 1162009) (by norm_num)
theorem B2322589 : Blo 1630514 2322589 := bbase (se 3 (by rfl) ⟨435485, by rfl⟩ : syracuseStep 2322589 = 870971) (by norm_num)
theorem B13234357 : Blo 1630514 13234357 := bbase (se 5 (by rfl) ⟨620360, by rfl⟩ : syracuseStep 13234357 = 1240721) (by norm_num)
theorem B5509349 : Blo 1630514 5509349 := bbase (se 4 (by rfl) ⟨516501, by rfl⟩ : syracuseStep 5509349 = 1033003) (by norm_num)
theorem B2093293 : Blo 1630514 2093293 := bbase (se 3 (by rfl) ⟨392492, by rfl⟩ : syracuseStep 2093293 = 784985) (by norm_num)
theorem B4903157 : Blo 1630514 4903157 := bbase (se 5 (by rfl) ⟨229835, by rfl⟩ : syracuseStep 4903157 = 459671) (by norm_num)
theorem B2322685 : Blo 1630514 2322685 := bbase (se 3 (by rfl) ⟨435503, by rfl⟩ : syracuseStep 2322685 = 871007) (by norm_num)
theorem B2789653 : Blo 1630514 2789653 := bbase (se 6 (by rfl) ⟨65382, by rfl⟩ : syracuseStep 2789653 = 130765) (by norm_num)
theorem B4960549 : Blo 1630514 4960549 := bbase (se 4 (by rfl) ⟨465051, by rfl⟩ : syracuseStep 4960549 = 930103) (by norm_num)
theorem B5878133 : Blo 1630514 5878133 := bbase (se 5 (by rfl) ⟨275537, by rfl⟩ : syracuseStep 5878133 = 551075) (by norm_num)
theorem B9925013 : Blo 1630514 9925013 := bbase (se 6 (by rfl) ⟨232617, by rfl⟩ : syracuseStep 9925013 = 465235) (by norm_num)
theorem B7442885 : Blo 1630514 7442885 := bbase (se 4 (by rfl) ⟨697770, by rfl⟩ : syracuseStep 7442885 = 1395541) (by norm_num)
theorem B2445773 : Blo 1630514 2445773 := bbase (se 3 (by rfl) ⟨458582, by rfl⟩ : syracuseStep 2445773 = 917165) (by norm_num)
theorem B2445797 : Blo 1630514 2445797 := bbase (se 4 (by rfl) ⟨229293, by rfl⟩ : syracuseStep 2445797 = 458587) (by norm_num)
theorem B3486181 : Blo 1630514 3486181 := bbase (se 4 (by rfl) ⟨326829, by rfl⟩ : syracuseStep 3486181 = 653659) (by norm_num)
theorem B2445821 : Blo 1630514 2445821 := bbase (se 3 (by rfl) ⟨458591, by rfl⟩ : syracuseStep 2445821 = 917183) (by norm_num)
theorem B2445845 : Blo 1630514 2445845 := bbase (se 6 (by rfl) ⟨57324, by rfl⟩ : syracuseStep 2445845 = 114649) (by norm_num)
theorem B2445869 : Blo 1630514 2445869 := bbase (se 3 (by rfl) ⟨458600, by rfl⟩ : syracuseStep 2445869 = 917201) (by norm_num)
theorem B2445893 : Blo 1630514 2445893 := bbase (se 4 (by rfl) ⟨229302, by rfl⟩ : syracuseStep 2445893 = 458605) (by norm_num)
theorem B2445917 : Blo 1630514 2445917 := bbase (se 3 (by rfl) ⟨458609, by rfl⟩ : syracuseStep 2445917 = 917219) (by norm_num)
theorem B2445941 : Blo 1630514 2445941 := bbase (se 5 (by rfl) ⟨114653, by rfl⟩ : syracuseStep 2445941 = 229307) (by norm_num)
theorem B1741429 : Blo 1630514 1741429 := bbase (se 5 (by rfl) ⟨81629, by rfl⟩ : syracuseStep 1741429 = 163259) (by norm_num)
theorem B1741433 : Blo 1630514 1741433 := bbase (se 2 (by rfl) ⟨653037, by rfl⟩ : syracuseStep 1741433 = 1306075) (by norm_num)
theorem B7844485 : Blo 1630514 7844485 := bbase (se 4 (by rfl) ⟨735420, by rfl⟩ : syracuseStep 7844485 = 1470841) (by norm_num)
theorem B2445965 : Blo 1630514 2445965 := bbase (se 3 (by rfl) ⟨458618, by rfl⟩ : syracuseStep 2445965 = 917237) (by norm_num)
theorem B2445989 : Blo 1630514 2445989 := bbase (se 4 (by rfl) ⟨229311, by rfl⟩ : syracuseStep 2445989 = 458623) (by norm_num)
theorem B2446013 : Blo 1630514 2446013 := bbase (se 3 (by rfl) ⟨458627, by rfl⟩ : syracuseStep 2446013 = 917255) (by norm_num)
theorem B2446037 : Blo 1630514 2446037 := bbase (se 7 (by rfl) ⟨28664, by rfl⟩ : syracuseStep 2446037 = 57329) (by norm_num)
theorem B2446061 : Blo 1630514 2446061 := bbase (se 3 (by rfl) ⟨458636, by rfl⟩ : syracuseStep 2446061 = 917273) (by norm_num)
theorem B2323181 : Blo 1630514 2323181 := bbase (se 3 (by rfl) ⟨435596, by rfl⟩ : syracuseStep 2323181 = 871193) (by norm_num)
theorem B2446085 : Blo 1630514 2446085 := bbase (se 4 (by rfl) ⟨229320, by rfl⟩ : syracuseStep 2446085 = 458641) (by norm_num)
theorem B2446109 : Blo 1630514 2446109 := bbase (se 3 (by rfl) ⟨458645, by rfl⟩ : syracuseStep 2446109 = 917291) (by norm_num)
theorem B2446133 : Blo 1630514 2446133 := bbase (se 5 (by rfl) ⟨114662, by rfl⟩ : syracuseStep 2446133 = 229325) (by norm_num)
theorem B2446157 : Blo 1630514 2446157 := bbase (se 3 (by rfl) ⟨458654, by rfl⟩ : syracuseStep 2446157 = 917309) (by norm_num)
theorem B8262485 : Blo 1630514 8262485 := bbase (se 9 (by rfl) ⟨24206, by rfl⟩ : syracuseStep 8262485 = 48413) (by norm_num)
theorem B3486557 : Blo 1630514 3486557 := bbase (se 3 (by rfl) ⟨653729, by rfl⟩ : syracuseStep 3486557 = 1307459) (by norm_num)
theorem B2446181 : Blo 1630514 2446181 := bbase (se 4 (by rfl) ⟨229329, by rfl⟩ : syracuseStep 2446181 = 458659) (by norm_num)
theorem B2683757 : Blo 1630514 2683757 := bbase (se 3 (by rfl) ⟨503204, by rfl⟩ : syracuseStep 2683757 = 1006409) (by norm_num)
theorem B2446205 : Blo 1630514 2446205 := bbase (se 3 (by rfl) ⟨458663, by rfl⟩ : syracuseStep 2446205 = 917327) (by norm_num)
theorem B2446229 : Blo 1630514 2446229 := bbase (se 6 (by rfl) ⟨57333, by rfl⟩ : syracuseStep 2446229 = 114667) (by norm_num)
theorem B2446253 : Blo 1630514 2446253 := bbase (se 3 (by rfl) ⟨458672, by rfl⟩ : syracuseStep 2446253 = 917345) (by norm_num)
theorem B13595573 : Blo 1630514 13595573 := bbase (se 5 (by rfl) ⟨637292, by rfl⟩ : syracuseStep 13595573 = 1274585) (by norm_num)
theorem B2446277 : Blo 1630514 2446277 := bbase (se 4 (by rfl) ⟨229338, by rfl⟩ : syracuseStep 2446277 = 458677) (by norm_num)
theorem B6968261 : Blo 1630514 6968261 := bbase (se 4 (by rfl) ⟨653274, by rfl⟩ : syracuseStep 6968261 = 1306549) (by norm_num)
theorem B2446301 : Blo 1630514 2446301 := bbase (se 3 (by rfl) ⟨458681, by rfl⟩ : syracuseStep 2446301 = 917363) (by norm_num)
theorem B2446325 : Blo 1630514 2446325 := bbase (se 5 (by rfl) ⟨114671, by rfl⟩ : syracuseStep 2446325 = 229343) (by norm_num)
theorem B1766405 : Blo 1630514 1766405 := bbase (se 4 (by rfl) ⟨165600, by rfl⟩ : syracuseStep 1766405 = 331201) (by norm_num)
theorem B2446349 : Blo 1630514 2446349 := bbase (se 3 (by rfl) ⟨458690, by rfl⟩ : syracuseStep 2446349 = 917381) (by norm_num)
theorem B2446373 : Blo 1630514 2446373 := bbase (se 4 (by rfl) ⟨229347, by rfl⟩ : syracuseStep 2446373 = 458695) (by norm_num)
theorem B2446397 : Blo 1630514 2446397 := bbase (se 3 (by rfl) ⟨458699, by rfl⟩ : syracuseStep 2446397 = 917399) (by norm_num)
theorem B1791041 : Blo 1630514 1791041 := bbase (se 2 (by rfl) ⟨671640, by rfl⟩ : syracuseStep 1791041 = 1343281) (by norm_num)
theorem B2446421 : Blo 1630514 2446421 := bbase (se 8 (by rfl) ⟨14334, by rfl⟩ : syracuseStep 2446421 = 28669) (by norm_num)
theorem B2446445 : Blo 1630514 2446445 := bbase (se 3 (by rfl) ⟨458708, by rfl⟩ : syracuseStep 2446445 = 917417) (by norm_num)
theorem B12391541 : Blo 1630514 12391541 := bbase (se 5 (by rfl) ⟨580853, by rfl⟩ : syracuseStep 12391541 = 1161707) (by norm_num)
theorem B2446469 : Blo 1630514 2446469 := bbase (se 4 (by rfl) ⟨229356, by rfl⟩ : syracuseStep 2446469 = 458713) (by norm_num)
theorem B2446493 : Blo 1630514 2446493 := bbase (se 3 (by rfl) ⟨458717, by rfl⟩ : syracuseStep 2446493 = 917435) (by norm_num)
theorem B1987753 : Blo 1630514 1987753 := bbase (se 2 (by rfl) ⟨745407, by rfl⟩ : syracuseStep 1987753 = 1490815) (by norm_num)
theorem B1741997 : Blo 1630514 1741997 := bbase (se 3 (by rfl) ⟨326624, by rfl⟩ : syracuseStep 1741997 = 653249) (by norm_num)
theorem B2446517 : Blo 1630514 2446517 := bbase (se 5 (by rfl) ⟨114680, by rfl⟩ : syracuseStep 2446517 = 229361) (by norm_num)
theorem B6968501 : Blo 1630514 6968501 := bbase (se 5 (by rfl) ⟨326648, by rfl⟩ : syracuseStep 6968501 = 653297) (by norm_num)
theorem B2446541 : Blo 1630514 2446541 := bbase (se 3 (by rfl) ⟨458726, by rfl⟩ : syracuseStep 2446541 = 917453) (by norm_num)
theorem B2446565 : Blo 1630514 2446565 := bbase (se 4 (by rfl) ⟨229365, by rfl⟩ : syracuseStep 2446565 = 458731) (by norm_num)
theorem B8254709 : Blo 1630514 8254709 := bbase (se 5 (by rfl) ⟨386939, by rfl⟩ : syracuseStep 8254709 = 773879) (by norm_num)
theorem B2446589 : Blo 1630514 2446589 := bbase (se 3 (by rfl) ⟨458735, by rfl⟩ : syracuseStep 2446589 = 917471) (by norm_num)
theorem B2446613 : Blo 1630514 2446613 := bbase (se 6 (by rfl) ⟨57342, by rfl⟩ : syracuseStep 2446613 = 114685) (by norm_num)
theorem B2323733 : Blo 1630514 2323733 := bbase (se 6 (by rfl) ⟨54462, by rfl⟩ : syracuseStep 2323733 = 108925) (by norm_num)
theorem B2479405 : Blo 1630514 2479405 := bbase (se 3 (by rfl) ⟨464888, by rfl⟩ : syracuseStep 2479405 = 929777) (by norm_num)
theorem B2446637 : Blo 1630514 2446637 := bbase (se 3 (by rfl) ⟨458744, by rfl⟩ : syracuseStep 2446637 = 917489) (by norm_num)
theorem B2446661 : Blo 1630514 2446661 := bbase (se 4 (by rfl) ⟨229374, by rfl⟩ : syracuseStep 2446661 = 458749) (by norm_num)
theorem B2446685 : Blo 1630514 2446685 := bbase (se 3 (by rfl) ⟨458753, by rfl⟩ : syracuseStep 2446685 = 917507) (by norm_num)
theorem B1742185 : Blo 1630514 1742185 := bbase (se 2 (by rfl) ⟨653319, by rfl⟩ : syracuseStep 1742185 = 1306639) (by norm_num)
theorem B2446709 : Blo 1630514 2446709 := bbase (se 5 (by rfl) ⟨114689, by rfl⟩ : syracuseStep 2446709 = 229379) (by norm_num)
theorem B2446733 : Blo 1630514 2446733 := bbase (se 3 (by rfl) ⟨458762, by rfl⟩ : syracuseStep 2446733 = 917525) (by norm_num)
theorem B2446757 : Blo 1630514 2446757 := bbase (se 4 (by rfl) ⟨229383, by rfl⟩ : syracuseStep 2446757 = 458767) (by norm_num)
theorem B2446781 : Blo 1630514 2446781 := bbase (se 3 (by rfl) ⟨458771, by rfl⟩ : syracuseStep 2446781 = 917543) (by norm_num)
theorem B2446805 : Blo 1630514 2446805 := bbase (se 7 (by rfl) ⟨28673, by rfl⟩ : syracuseStep 2446805 = 57347) (by norm_num)
theorem B2446829 : Blo 1630514 2446829 := bbase (se 3 (by rfl) ⟨458780, by rfl⟩ : syracuseStep 2446829 = 917561) (by norm_num)
theorem B2446853 : Blo 1630514 2446853 := bbase (se 4 (by rfl) ⟨229392, by rfl⟩ : syracuseStep 2446853 = 458785) (by norm_num)
theorem B12383765 : Blo 1630514 12383765 := bbase (se 6 (by rfl) ⟨290244, by rfl⟩ : syracuseStep 12383765 = 580489) (by norm_num)
theorem B2446877 : Blo 1630514 2446877 := bbase (se 3 (by rfl) ⟨458789, by rfl⟩ : syracuseStep 2446877 = 917579) (by norm_num)
theorem B2446901 : Blo 1630514 2446901 := bbase (se 5 (by rfl) ⟨114698, by rfl⟩ : syracuseStep 2446901 = 229397) (by norm_num)
theorem B2790973 : Blo 1630514 2790973 := bbase (se 3 (by rfl) ⟨523307, by rfl⟩ : syracuseStep 2790973 = 1046615) (by norm_num)
theorem B2446925 : Blo 1630514 2446925 := bbase (se 3 (by rfl) ⟨458798, by rfl⟩ : syracuseStep 2446925 = 917597) (by norm_num)
theorem B3921493 : Blo 1630514 3921493 := bbase (se 8 (by rfl) ⟨22977, by rfl⟩ : syracuseStep 3921493 = 45955) (by norm_num)
theorem B2446949 : Blo 1630514 2446949 := bbase (se 4 (by rfl) ⟨229401, by rfl⟩ : syracuseStep 2446949 = 458803) (by norm_num)
theorem B2446973 : Blo 1630514 2446973 := bbase (se 3 (by rfl) ⟨458807, by rfl⟩ : syracuseStep 2446973 = 917615) (by norm_num)
theorem B2446997 : Blo 1630514 2446997 := bbase (se 6 (by rfl) ⟨57351, by rfl⟩ : syracuseStep 2446997 = 114703) (by norm_num)
theorem B2447021 : Blo 1630514 2447021 := bbase (se 3 (by rfl) ⟨458816, by rfl⟩ : syracuseStep 2447021 = 917633) (by norm_num)
theorem B2447045 : Blo 1630514 2447045 := bbase (se 4 (by rfl) ⟨229410, by rfl⟩ : syracuseStep 2447045 = 458821) (by norm_num)
theorem B2447069 : Blo 1630514 2447069 := bbase (se 3 (by rfl) ⟨458825, by rfl⟩ : syracuseStep 2447069 = 917651) (by norm_num)
theorem B2447093 : Blo 1630514 2447093 := bbase (se 5 (by rfl) ⟨114707, by rfl⟩ : syracuseStep 2447093 = 229415) (by norm_num)
theorem B2447117 : Blo 1630514 2447117 := bbase (se 3 (by rfl) ⟨458834, by rfl⟩ : syracuseStep 2447117 = 917669) (by norm_num)
theorem B9418517 : Blo 1630514 9418517 := bbase (se 6 (by rfl) ⟨220746, by rfl⟩ : syracuseStep 9418517 = 441493) (by norm_num)
theorem B2447141 : Blo 1630514 2447141 := bbase (se 4 (by rfl) ⟨229419, by rfl⟩ : syracuseStep 2447141 = 458839) (by norm_num)
theorem B2447165 : Blo 1630514 2447165 := bbase (se 3 (by rfl) ⟨458843, by rfl⟩ : syracuseStep 2447165 = 917687) (by norm_num)
theorem B2447189 : Blo 1630514 2447189 := bbase (se 9 (by rfl) ⟨7169, by rfl⟩ : syracuseStep 2447189 = 14339) (by norm_num)
theorem B2447213 : Blo 1630514 2447213 := bbase (se 3 (by rfl) ⟨458852, by rfl⟩ : syracuseStep 2447213 = 917705) (by norm_num)
theorem B2447237 : Blo 1630514 2447237 := bbase (se 4 (by rfl) ⟨229428, by rfl⟩ : syracuseStep 2447237 = 458857) (by norm_num)
theorem B2447261 : Blo 1630514 2447261 := bbase (se 3 (by rfl) ⟨458861, by rfl⟩ : syracuseStep 2447261 = 917723) (by norm_num)
theorem B2447285 : Blo 1630514 2447285 := bbase (se 5 (by rfl) ⟨114716, by rfl⟩ : syracuseStep 2447285 = 229433) (by norm_num)
theorem B2447309 : Blo 1630514 2447309 := bbase (se 3 (by rfl) ⟨458870, by rfl⟩ : syracuseStep 2447309 = 917741) (by norm_num)
theorem B2447333 : Blo 1630514 2447333 := bbase (se 4 (by rfl) ⟨229437, by rfl⟩ : syracuseStep 2447333 = 458875) (by norm_num)
theorem B6191093 : Blo 1630514 6191093 := bbase (se 5 (by rfl) ⟨290207, by rfl⟩ : syracuseStep 6191093 = 580415) (by norm_num)
theorem B2447357 : Blo 1630514 2447357 := bbase (se 3 (by rfl) ⟨458879, by rfl⟩ : syracuseStep 2447357 = 917759) (by norm_num)
theorem B4184077 : Blo 1630514 4184077 := bbase (se 3 (by rfl) ⟨784514, by rfl⟩ : syracuseStep 4184077 = 1569029) (by norm_num)
theorem B2447381 : Blo 1630514 2447381 := bbase (se 6 (by rfl) ⟨57360, by rfl⟩ : syracuseStep 2447381 = 114721) (by norm_num)
theorem B2447405 : Blo 1630514 2447405 := bbase (se 3 (by rfl) ⟨458888, by rfl⟩ : syracuseStep 2447405 = 917777) (by norm_num)
theorem B2447429 : Blo 1630514 2447429 := bbase (se 4 (by rfl) ⟨229446, by rfl⟩ : syracuseStep 2447429 = 458893) (by norm_num)
theorem B2447453 : Blo 1630514 2447453 := bbase (se 3 (by rfl) ⟨458897, by rfl⟩ : syracuseStep 2447453 = 917795) (by norm_num)
theorem B3922013 : Blo 1630514 3922013 := bbase (se 3 (by rfl) ⟨735377, by rfl⟩ : syracuseStep 3922013 = 1470755) (by norm_num)
theorem B8263781 : Blo 1630514 8263781 := bbase (se 4 (by rfl) ⟨774729, by rfl⟩ : syracuseStep 8263781 = 1549459) (by norm_num)
theorem B2447477 : Blo 1630514 2447477 := bbase (se 5 (by rfl) ⟨114725, by rfl⟩ : syracuseStep 2447477 = 229451) (by norm_num)
theorem B2447501 : Blo 1630514 2447501 := bbase (se 3 (by rfl) ⟨458906, by rfl⟩ : syracuseStep 2447501 = 917813) (by norm_num)
theorem B1743005 : Blo 1630514 1743005 := bbase (se 3 (by rfl) ⟨326813, by rfl⟩ : syracuseStep 1743005 = 653627) (by norm_num)
theorem B2447525 : Blo 1630514 2447525 := bbase (se 4 (by rfl) ⟨229455, by rfl⟩ : syracuseStep 2447525 = 458911) (by norm_num)
theorem B5879989 : Blo 1630514 5879989 := bbase (se 5 (by rfl) ⟨275624, by rfl⟩ : syracuseStep 5879989 = 551249) (by norm_num)
theorem B2447549 : Blo 1630514 2447549 := bbase (se 3 (by rfl) ⟨458915, by rfl⟩ : syracuseStep 2447549 = 917831) (by norm_num)
theorem B1652945 : Blo 1630514 1652945 := bbase (se 2 (by rfl) ⟨619854, by rfl⟩ : syracuseStep 1652945 = 1239709) (by norm_num)
theorem B2447573 : Blo 1630514 2447573 := bbase (se 7 (by rfl) ⟨28682, by rfl⟩ : syracuseStep 2447573 = 57365) (by norm_num)
theorem B2447597 : Blo 1630514 2447597 := bbase (se 3 (by rfl) ⟨458924, by rfl⟩ : syracuseStep 2447597 = 917849) (by norm_num)
theorem B9296117 : Blo 1630514 9296117 := bbase (se 5 (by rfl) ⟨435755, by rfl⟩ : syracuseStep 9296117 = 871511) (by norm_num)
theorem B5224709 : Blo 1630514 5224709 := bbase (se 4 (by rfl) ⟨489816, by rfl⟩ : syracuseStep 5224709 = 979633) (by norm_num)
theorem B2447621 : Blo 1630514 2447621 := bbase (se 4 (by rfl) ⟨229464, by rfl⟩ : syracuseStep 2447621 = 458929) (by norm_num)
theorem B2447645 : Blo 1630514 2447645 := bbase (se 3 (by rfl) ⟨458933, by rfl⟩ : syracuseStep 2447645 = 917867) (by norm_num)
theorem B2447669 : Blo 1630514 2447669 := bbase (se 5 (by rfl) ⟨114734, by rfl⟩ : syracuseStep 2447669 = 229469) (by norm_num)
theorem B5503301 : Blo 1630514 5503301 := bbase (se 4 (by rfl) ⟨515934, by rfl⟩ : syracuseStep 5503301 = 1031869) (by norm_num)
theorem B2447693 : Blo 1630514 2447693 := bbase (se 3 (by rfl) ⟨458942, by rfl⟩ : syracuseStep 2447693 = 917885) (by norm_num)
theorem B39704917 : Blo 1630514 39704917 := bbase (se 10 (by rfl) ⟨58161, by rfl⟩ : syracuseStep 39704917 = 116323) (by norm_num)
theorem B2447717 : Blo 1630514 2447717 := bbase (se 4 (by rfl) ⟨229473, by rfl⟩ : syracuseStep 2447717 = 458947) (by norm_num)
theorem B9288053 : Blo 1630514 9288053 := bbase (se 5 (by rfl) ⟨435377, by rfl⟩ : syracuseStep 9288053 = 870755) (by norm_num)
theorem B2447741 : Blo 1630514 2447741 := bbase (se 3 (by rfl) ⟨458951, by rfl⟩ : syracuseStep 2447741 = 917903) (by norm_num)
theorem B22329749 : Blo 1630514 22329749 := bbase (se 6 (by rfl) ⟨523353, by rfl⟩ : syracuseStep 22329749 = 1046707) (by norm_num)
theorem B2447765 : Blo 1630514 2447765 := bbase (se 6 (by rfl) ⟨57369, by rfl⟩ : syracuseStep 2447765 = 114739) (by norm_num)
theorem B2447789 : Blo 1630514 2447789 := bbase (se 3 (by rfl) ⟨458960, by rfl⟩ : syracuseStep 2447789 = 917921) (by norm_num)
theorem B2447813 : Blo 1630514 2447813 := bbase (se 4 (by rfl) ⟨229482, by rfl⟩ : syracuseStep 2447813 = 458965) (by norm_num)
theorem B2513357 : Blo 1630514 2513357 := bbase (se 3 (by rfl) ⟨471254, by rfl⟩ : syracuseStep 2513357 = 942509) (by norm_num)
theorem B2447837 : Blo 1630514 2447837 := bbase (se 3 (by rfl) ⟨458969, by rfl⟩ : syracuseStep 2447837 = 917939) (by norm_num)
theorem B3922397 : Blo 1630514 3922397 := bbase (se 3 (by rfl) ⟨735449, by rfl⟩ : syracuseStep 3922397 = 1470899) (by norm_num)
theorem B2447861 : Blo 1630514 2447861 := bbase (se 5 (by rfl) ⟨114743, by rfl⟩ : syracuseStep 2447861 = 229487) (by norm_num)
theorem B8256005 : Blo 1630514 8256005 := bbase (se 4 (by rfl) ⟨774000, by rfl⟩ : syracuseStep 8256005 = 1548001) (by norm_num)
theorem B1653257 : Blo 1630514 1653257 := bbase (se 2 (by rfl) ⟨619971, by rfl⟩ : syracuseStep 1653257 = 1239943) (by norm_num)
theorem B2447885 : Blo 1630514 2447885 := bbase (se 3 (by rfl) ⟨458978, by rfl⟩ : syracuseStep 2447885 = 917957) (by norm_num)
theorem B3922445 : Blo 1630514 3922445 := bbase (se 3 (by rfl) ⟨735458, by rfl⟩ : syracuseStep 3922445 = 1470917) (by norm_num)
theorem B3922453 : Blo 1630514 3922453 := bbase (se 6 (by rfl) ⟨91932, by rfl⟩ : syracuseStep 3922453 = 183865) (by norm_num)
theorem B2447909 : Blo 1630514 2447909 := bbase (se 4 (by rfl) ⟨229491, by rfl⟩ : syracuseStep 2447909 = 458983) (by norm_num)
theorem B2447933 : Blo 1630514 2447933 := bbase (se 3 (by rfl) ⟨458987, by rfl⟩ : syracuseStep 2447933 = 917975) (by norm_num)
theorem B2447957 : Blo 1630514 2447957 := bbase (se 8 (by rfl) ⟨14343, by rfl⟩ : syracuseStep 2447957 = 28687) (by norm_num)
theorem B2447981 : Blo 1630514 2447981 := bbase (se 3 (by rfl) ⟨458996, by rfl⟩ : syracuseStep 2447981 = 917993) (by norm_num)
theorem B2448005 : Blo 1630514 2448005 := bbase (se 4 (by rfl) ⟨229500, by rfl⟩ : syracuseStep 2448005 = 459001) (by norm_num)
theorem B2939533 : Blo 1630514 2939533 := bbase (se 3 (by rfl) ⟨551162, by rfl⟩ : syracuseStep 2939533 = 1102325) (by norm_num)
theorem B2448029 : Blo 1630514 2448029 := bbase (se 3 (by rfl) ⟨459005, by rfl⟩ : syracuseStep 2448029 = 918011) (by norm_num)
theorem B2448053 : Blo 1630514 2448053 := bbase (se 5 (by rfl) ⟨114752, by rfl⟩ : syracuseStep 2448053 = 229505) (by norm_num)
theorem B3668669 : Blo 1630514 3668669 := bbase (se 3 (by rfl) ⟨687875, by rfl⟩ : syracuseStep 3668669 = 1375751) (by norm_num)
theorem B2448077 : Blo 1630514 2448077 := bbase (se 3 (by rfl) ⟨459014, by rfl⟩ : syracuseStep 2448077 = 918029) (by norm_num)
theorem B2448101 : Blo 1630514 2448101 := bbase (se 4 (by rfl) ⟨229509, by rfl⟩ : syracuseStep 2448101 = 459019) (by norm_num)
theorem B5503733 : Blo 1630514 5503733 := bbase (se 5 (by rfl) ⟨257987, by rfl⟩ : syracuseStep 5503733 = 515975) (by norm_num)
theorem B2448125 : Blo 1630514 2448125 := bbase (se 3 (by rfl) ⟨459023, by rfl⟩ : syracuseStep 2448125 = 918047) (by norm_num)
theorem B3668741 : Blo 1630514 3668741 := bbase (se 4 (by rfl) ⟨343944, by rfl⟩ : syracuseStep 3668741 = 687889) (by norm_num)
theorem B2448149 : Blo 1630514 2448149 := bbase (se 6 (by rfl) ⟨57378, by rfl⟩ : syracuseStep 2448149 = 114757) (by norm_num)
theorem B2235181 : Blo 1630514 2235181 := bbase (se 3 (by rfl) ⟨419096, by rfl⟩ : syracuseStep 2235181 = 838193) (by norm_num)
theorem B2448173 : Blo 1630514 2448173 := bbase (se 3 (by rfl) ⟨459032, by rfl⟩ : syracuseStep 2448173 = 918065) (by norm_num)
theorem B4127557 : Blo 1630514 4127557 := bbase (se 4 (by rfl) ⟨386958, by rfl⟩ : syracuseStep 4127557 = 773917) (by norm_num)
theorem B2448197 : Blo 1630514 2448197 := bbase (se 4 (by rfl) ⟨229518, by rfl⟩ : syracuseStep 2448197 = 459037) (by norm_num)
theorem B3668813 : Blo 1630514 3668813 := bbase (se 3 (by rfl) ⟨687902, by rfl⟩ : syracuseStep 3668813 = 1375805) (by norm_num)
theorem B3971917 : Blo 1630514 3971917 := bbase (se 3 (by rfl) ⟨744734, by rfl⟩ : syracuseStep 3971917 = 1489469) (by norm_num)
theorem B2448221 : Blo 1630514 2448221 := bbase (se 3 (by rfl) ⟨459041, by rfl⟩ : syracuseStep 2448221 = 918083) (by norm_num)
theorem B2448245 : Blo 1630514 2448245 := bbase (se 5 (by rfl) ⟨114761, by rfl⟩ : syracuseStep 2448245 = 229523) (by norm_num)
theorem B2448269 : Blo 1630514 2448269 := bbase (se 3 (by rfl) ⟨459050, by rfl⟩ : syracuseStep 2448269 = 918101) (by norm_num)
theorem B3668885 : Blo 1630514 3668885 := bbase (se 6 (by rfl) ⟨85989, by rfl⟩ : syracuseStep 3668885 = 171979) (by norm_num)
theorem B2448293 : Blo 1630514 2448293 := bbase (se 4 (by rfl) ⟨229527, by rfl⟩ : syracuseStep 2448293 = 459055) (by norm_num)
theorem B4127669 : Blo 1630514 4127669 := bbase (se 5 (by rfl) ⟨193484, by rfl⟩ : syracuseStep 4127669 = 386969) (by norm_num)
theorem B2448317 : Blo 1630514 2448317 := bbase (se 3 (by rfl) ⟨459059, by rfl⟩ : syracuseStep 2448317 = 918119) (by norm_num)
theorem B3308485 : Blo 1630514 3308485 := bbase (se 4 (by rfl) ⟨310170, by rfl⟩ : syracuseStep 3308485 = 620341) (by norm_num)
theorem B3095509 : Blo 1630514 3095509 := bbase (se 7 (by rfl) ⟨36275, by rfl⟩ : syracuseStep 3095509 = 72551) (by norm_num)
theorem B3308501 : Blo 1630514 3308501 := bbase (se 7 (by rfl) ⟨38771, by rfl⟩ : syracuseStep 3308501 = 77543) (by norm_num)
theorem B2448341 : Blo 1630514 2448341 := bbase (se 7 (by rfl) ⟨28691, by rfl⟩ : syracuseStep 2448341 = 57383) (by norm_num)
theorem B3668957 : Blo 1630514 3668957 := bbase (se 3 (by rfl) ⟨687929, by rfl⟩ : syracuseStep 3668957 = 1375859) (by norm_num)
theorem B2448365 : Blo 1630514 2448365 := bbase (se 3 (by rfl) ⟨459068, by rfl⟩ : syracuseStep 2448365 = 918137) (by norm_num)
theorem B2448389 : Blo 1630514 2448389 := bbase (se 4 (by rfl) ⟨229536, by rfl⟩ : syracuseStep 2448389 = 459073) (by norm_num)
theorem B2751509 : Blo 1630514 2751509 := bbase (se 6 (by rfl) ⟨64488, by rfl⟩ : syracuseStep 2751509 = 128977) (by norm_num)
theorem B2448413 : Blo 1630514 2448413 := bbase (se 3 (by rfl) ⟨459077, by rfl⟩ : syracuseStep 2448413 = 918155) (by norm_num)
theorem B3669029 : Blo 1630514 3669029 := bbase (se 4 (by rfl) ⟨343971, by rfl⟩ : syracuseStep 3669029 = 687943) (by norm_num)
theorem B2448437 : Blo 1630514 2448437 := bbase (se 5 (by rfl) ⟨114770, by rfl⟩ : syracuseStep 2448437 = 229541) (by norm_num)
theorem B2448461 : Blo 1630514 2448461 := bbase (se 3 (by rfl) ⟨459086, by rfl⟩ : syracuseStep 2448461 = 918173) (by norm_num)
theorem B2939989 : Blo 1630514 2939989 := bbase (se 8 (by rfl) ⟨17226, by rfl⟩ : syracuseStep 2939989 = 34453) (by norm_num)
theorem B1653853 : Blo 1630514 1653853 := bbase (se 3 (by rfl) ⟨310097, by rfl⟩ : syracuseStep 1653853 = 620195) (by norm_num)
theorem B3095653 : Blo 1630514 3095653 := bbase (se 4 (by rfl) ⟨290217, by rfl⟩ : syracuseStep 3095653 = 580435) (by norm_num)
theorem B2448485 : Blo 1630514 2448485 := bbase (se 4 (by rfl) ⟨229545, by rfl⟩ : syracuseStep 2448485 = 459091) (by norm_num)
theorem B3669101 : Blo 1630514 3669101 := bbase (se 3 (by rfl) ⟨687956, by rfl⟩ : syracuseStep 3669101 = 1375913) (by norm_num)
theorem B4127861 : Blo 1630514 4127861 := bbase (se 5 (by rfl) ⟨193493, by rfl⟩ : syracuseStep 4127861 = 386987) (by norm_num)
theorem B1653877 : Blo 1630514 1653877 := bbase (se 5 (by rfl) ⟨77525, by rfl⟩ : syracuseStep 1653877 = 155051) (by norm_num)
theorem B2448509 : Blo 1630514 2448509 := bbase (se 3 (by rfl) ⟨459095, by rfl⟩ : syracuseStep 2448509 = 918191) (by norm_num)
theorem B2751637 : Blo 1630514 2751637 := bbase (se 6 (by rfl) ⟨64491, by rfl⟩ : syracuseStep 2751637 = 128983) (by norm_num)
theorem B2448533 : Blo 1630514 2448533 := bbase (se 6 (by rfl) ⟨57387, by rfl⟩ : syracuseStep 2448533 = 114775) (by norm_num)
theorem B5504165 : Blo 1630514 5504165 := bbase (se 4 (by rfl) ⟨516015, by rfl⟩ : syracuseStep 5504165 = 1032031) (by norm_num)
theorem B2448557 : Blo 1630514 2448557 := bbase (se 3 (by rfl) ⟨459104, by rfl⟩ : syracuseStep 2448557 = 918209) (by norm_num)
theorem B3669173 : Blo 1630514 3669173 := bbase (se 5 (by rfl) ⟨171992, by rfl⟩ : syracuseStep 3669173 = 343985) (by norm_num)
theorem B2448581 : Blo 1630514 2448581 := bbase (se 4 (by rfl) ⟨229554, by rfl⟩ : syracuseStep 2448581 = 459109) (by norm_num)
theorem B2448605 : Blo 1630514 2448605 := bbase (se 3 (by rfl) ⟨459113, by rfl⟩ : syracuseStep 2448605 = 918227) (by norm_num)
theorem B2751725 : Blo 1630514 2751725 := bbase (se 3 (by rfl) ⟨515948, by rfl⟩ : syracuseStep 2751725 = 1031897) (by norm_num)
theorem B2448629 : Blo 1630514 2448629 := bbase (se 5 (by rfl) ⟨114779, by rfl⟩ : syracuseStep 2448629 = 229559) (by norm_num)
theorem B3669245 : Blo 1630514 3669245 := bbase (se 3 (by rfl) ⟨687983, by rfl⟩ : syracuseStep 3669245 = 1375967) (by norm_num)
theorem B3095813 : Blo 1630514 3095813 := bbase (se 4 (by rfl) ⟨290232, by rfl⟩ : syracuseStep 3095813 = 580465) (by norm_num)
theorem B2448653 : Blo 1630514 2448653 := bbase (se 3 (by rfl) ⟨459122, by rfl⟩ : syracuseStep 2448653 = 918245) (by norm_num)
theorem B2448677 : Blo 1630514 2448677 := bbase (se 4 (by rfl) ⟨229563, by rfl⟩ : syracuseStep 2448677 = 459127) (by norm_num)
theorem B2063657 : Blo 1630514 2063657 := bbase (se 2 (by rfl) ⟨773871, by rfl⟩ : syracuseStep 2063657 = 1547743) (by norm_num)
theorem B2448701 : Blo 1630514 2448701 := bbase (se 3 (by rfl) ⟨459131, by rfl⟩ : syracuseStep 2448701 = 918263) (by norm_num)
theorem B3669317 : Blo 1630514 3669317 := bbase (se 4 (by rfl) ⟨343998, by rfl⟩ : syracuseStep 3669317 = 687997) (by norm_num)
theorem B2448725 : Blo 1630514 2448725 := bbase (se 11 (by rfl) ⟨1793, by rfl⟩ : syracuseStep 2448725 = 3587) (by norm_num)
theorem B2063713 : Blo 1630514 2063713 := bbase (se 2 (by rfl) ⟨773892, by rfl⟩ : syracuseStep 2063713 = 1547785) (by norm_num)
theorem B2751853 : Blo 1630514 2751853 := bbase (se 3 (by rfl) ⟨515972, by rfl⟩ : syracuseStep 2751853 = 1031945) (by norm_num)
theorem B2448749 : Blo 1630514 2448749 := bbase (se 3 (by rfl) ⟨459140, by rfl⟩ : syracuseStep 2448749 = 918281) (by norm_num)
theorem B1834357 : Blo 1630514 1834357 := bbase (se 5 (by rfl) ⟨85985, by rfl⟩ : syracuseStep 1834357 = 171971) (by norm_num)
theorem B10452341 : Blo 1630514 10452341 := bbase (se 5 (by rfl) ⟨489953, by rfl⟩ : syracuseStep 10452341 = 979907) (by norm_num)
theorem B3669389 : Blo 1630514 3669389 := bbase (se 3 (by rfl) ⟨688010, by rfl⟩ : syracuseStep 3669389 = 1376021) (by norm_num)
theorem B3095957 : Blo 1630514 3095957 := bbase (se 6 (by rfl) ⟨72561, by rfl⟩ : syracuseStep 3095957 = 145123) (by norm_num)
theorem B9297301 : Blo 1630514 9297301 := bbase (se 6 (by rfl) ⟨217905, by rfl⟩ : syracuseStep 9297301 = 435811) (by norm_num)
theorem B1834393 : Blo 1630514 1834393 := bbase (se 2 (by rfl) ⟨687897, by rfl⟩ : syracuseStep 1834393 = 1375795) (by norm_num)
theorem B6970789 : Blo 1630514 6970789 := bbase (se 4 (by rfl) ⟨653511, by rfl⟩ : syracuseStep 6970789 = 1307023) (by norm_num)
theorem B1834429 : Blo 1630514 1834429 := bbase (se 3 (by rfl) ⟨343955, by rfl⟩ : syracuseStep 1834429 = 687911) (by norm_num)
theorem B2063809 : Blo 1630514 2063809 := bbase (se 2 (by rfl) ⟨773928, by rfl⟩ : syracuseStep 2063809 = 1547857) (by norm_num)
theorem B2751941 : Blo 1630514 2751941 := bbase (se 4 (by rfl) ⟨257994, by rfl⟩ : syracuseStep 2751941 = 515989) (by norm_num)
theorem B4128205 : Blo 1630514 4128205 := bbase (se 3 (by rfl) ⟨774038, by rfl⟩ : syracuseStep 4128205 = 1548077) (by norm_num)
theorem B3669461 : Blo 1630514 3669461 := bbase (se 7 (by rfl) ⟨43001, by rfl⟩ : syracuseStep 3669461 = 86003) (by norm_num)
theorem B53632469 : Blo 1630514 53632469 := bbase (se 7 (by rfl) ⟨628505, by rfl⟩ : syracuseStep 53632469 = 1257011) (by norm_num)
theorem B1834465 : Blo 1630514 1834465 := bbase (se 2 (by rfl) ⟨687924, by rfl⟩ : syracuseStep 1834465 = 1375849) (by norm_num)
theorem B1834501 : Blo 1630514 1834501 := bbase (se 4 (by rfl) ⟨171984, by rfl⟩ : syracuseStep 1834501 = 343969) (by norm_num)
theorem B3669533 : Blo 1630514 3669533 := bbase (se 3 (by rfl) ⟨688037, by rfl⟩ : syracuseStep 3669533 = 1376075) (by norm_num)
theorem B2612765 : Blo 1630514 2612765 := bbase (se 3 (by rfl) ⟨489893, by rfl⟩ : syracuseStep 2612765 = 979787) (by norm_num)
theorem B1834537 : Blo 1630514 1834537 := bbase (se 2 (by rfl) ⟨687951, by rfl⟩ : syracuseStep 1834537 = 1375903) (by norm_num)
theorem B4128317 : Blo 1630514 4128317 := bbase (se 3 (by rfl) ⟨774059, by rfl⟩ : syracuseStep 4128317 = 1548119) (by norm_num)
theorem B2752069 : Blo 1630514 2752069 := bbase (se 4 (by rfl) ⟨258006, by rfl⟩ : syracuseStep 2752069 = 516013) (by norm_num)
theorem B1834573 : Blo 1630514 1834573 := bbase (se 3 (by rfl) ⟨343982, by rfl⟩ : syracuseStep 1834573 = 687965) (by norm_num)
theorem B5504597 : Blo 1630514 5504597 := bbase (se 8 (by rfl) ⟨32253, by rfl⟩ : syracuseStep 5504597 = 64507) (by norm_num)
theorem B3669605 : Blo 1630514 3669605 := bbase (se 4 (by rfl) ⟨344025, by rfl⟩ : syracuseStep 3669605 = 688051) (by norm_num)
theorem B2063981 : Blo 1630514 2063981 := bbase (se 3 (by rfl) ⟨386996, by rfl⟩ : syracuseStep 2063981 = 773993) (by norm_num)
theorem B1834609 : Blo 1630514 1834609 := bbase (se 2 (by rfl) ⟨687978, by rfl⟩ : syracuseStep 1834609 = 1375957) (by norm_num)
theorem B1834645 : Blo 1630514 1834645 := bbase (se 6 (by rfl) ⟨42999, by rfl⟩ : syracuseStep 1834645 = 85999) (by norm_num)
theorem B5226133 : Blo 1630514 5226133 := bbase (se 6 (by rfl) ⟨122487, by rfl⟩ : syracuseStep 5226133 = 244975) (by norm_num)
theorem B2752157 : Blo 1630514 2752157 := bbase (se 3 (by rfl) ⟨516029, by rfl⟩ : syracuseStep 2752157 = 1032059) (by norm_num)
theorem B2612893 : Blo 1630514 2612893 := bbase (se 3 (by rfl) ⟨489917, by rfl⟩ : syracuseStep 2612893 = 979835) (by norm_num)
theorem B2064037 : Blo 1630514 2064037 := bbase (se 4 (by rfl) ⟨193503, by rfl⟩ : syracuseStep 2064037 = 387007) (by norm_num)
theorem B3669677 : Blo 1630514 3669677 := bbase (se 3 (by rfl) ⟨688064, by rfl⟩ : syracuseStep 3669677 = 1376129) (by norm_num)
theorem B3096245 : Blo 1630514 3096245 := bbase (se 5 (by rfl) ⟨145136, by rfl⟩ : syracuseStep 3096245 = 290273) (by norm_num)
theorem B1834681 : Blo 1630514 1834681 := bbase (se 2 (by rfl) ⟨688005, by rfl⟩ : syracuseStep 1834681 = 1376011) (by norm_num)
theorem B1834717 : Blo 1630514 1834717 := bbase (se 3 (by rfl) ⟨344009, by rfl⟩ : syracuseStep 1834717 = 688019) (by norm_num)
theorem B3669749 : Blo 1630514 3669749 := bbase (se 5 (by rfl) ⟨172019, by rfl⟩ : syracuseStep 3669749 = 344039) (by norm_num)
theorem B4128509 : Blo 1630514 4128509 := bbase (se 3 (by rfl) ⟨774095, by rfl⟩ : syracuseStep 4128509 = 1548191) (by norm_num)
theorem B1834753 : Blo 1630514 1834753 := bbase (se 2 (by rfl) ⟨688032, by rfl⟩ : syracuseStep 1834753 = 1376065) (by norm_num)
theorem B2064133 : Blo 1630514 2064133 := bbase (se 4 (by rfl) ⟨193512, by rfl⟩ : syracuseStep 2064133 = 387025) (by norm_num)
theorem B8257301 : Blo 1630514 8257301 := bbase (se 6 (by rfl) ⟨193530, by rfl⟩ : syracuseStep 8257301 = 387061) (by norm_num)
theorem B2752285 : Blo 1630514 2752285 := bbase (se 3 (by rfl) ⟨516053, by rfl⟩ : syracuseStep 2752285 = 1032107) (by norm_num)
theorem B1834789 : Blo 1630514 1834789 := bbase (se 4 (by rfl) ⟨172011, by rfl⟩ : syracuseStep 1834789 = 344023) (by norm_num)
theorem B3669821 : Blo 1630514 3669821 := bbase (se 3 (by rfl) ⟨688091, by rfl⟩ : syracuseStep 3669821 = 1376183) (by norm_num)
theorem B1834825 : Blo 1630514 1834825 := bbase (se 2 (by rfl) ⟨688059, by rfl⟩ : syracuseStep 1834825 = 1376119) (by norm_num)
theorem B3096397 : Blo 1630514 3096397 := bbase (se 3 (by rfl) ⟨580574, by rfl⟩ : syracuseStep 3096397 = 1161149) (by norm_num)
theorem B2236261 : Blo 1630514 2236261 := bbase (se 4 (by rfl) ⟨209649, by rfl⟩ : syracuseStep 2236261 = 419299) (by norm_num)
theorem B1834861 : Blo 1630514 1834861 := bbase (se 3 (by rfl) ⟨344036, by rfl⟩ : syracuseStep 1834861 = 688073) (by norm_num)
theorem B2752373 : Blo 1630514 2752373 := bbase (se 5 (by rfl) ⟨129017, by rfl⟩ : syracuseStep 2752373 = 258035) (by norm_num)
theorem B3669893 : Blo 1630514 3669893 := bbase (se 4 (by rfl) ⟨344052, by rfl⟩ : syracuseStep 3669893 = 688105) (by norm_num)
theorem B1834897 : Blo 1630514 1834897 := bbase (se 2 (by rfl) ⟨688086, by rfl⟩ : syracuseStep 1834897 = 1376173) (by norm_num)
theorem B2064305 : Blo 1630514 2064305 := bbase (se 2 (by rfl) ⟨774114, by rfl⟩ : syracuseStep 2064305 = 1548229) (by norm_num)
theorem B1834933 : Blo 1630514 1834933 := bbase (se 5 (by rfl) ⟨86012, by rfl⟩ : syracuseStep 1834933 = 172025) (by norm_num)
theorem B3669965 : Blo 1630514 3669965 := bbase (se 3 (by rfl) ⟨688118, by rfl⟩ : syracuseStep 3669965 = 1376237) (by norm_num)
theorem B1834969 : Blo 1630514 1834969 := bbase (se 2 (by rfl) ⟨688113, by rfl⟩ : syracuseStep 1834969 = 1376227) (by norm_num)
theorem B2064361 : Blo 1630514 2064361 := bbase (se 2 (by rfl) ⟨774135, by rfl⟩ : syracuseStep 2064361 = 1548271) (by norm_num)
theorem B2752501 : Blo 1630514 2752501 := bbase (se 5 (by rfl) ⟨129023, by rfl⟩ : syracuseStep 2752501 = 258047) (by norm_num)
theorem B2940917 : Blo 1630514 2940917 := bbase (se 5 (by rfl) ⟨137855, by rfl⟩ : syracuseStep 2940917 = 275711) (by norm_num)
theorem B1835005 : Blo 1630514 1835005 := bbase (se 3 (by rfl) ⟨344063, by rfl⟩ : syracuseStep 1835005 = 688127) (by norm_num)
theorem B3670019 : Blo 1630514 3670019 := bstep (se 1 (by rfl) ⟨2752514, by rfl⟩ : syracuseStep 3670019 = 5505029) B5505029
theorem B4710413 : Blo 1630514 4710413 := bstep (se 3 (by rfl) ⟨883202, by rfl⟩ : syracuseStep 4710413 = 1766405) B1766405
theorem B5578769 : Blo 1630514 5578769 := bstep (se 2 (by rfl) ⟨2092038, by rfl⟩ : syracuseStep 5578769 = 4184077) B4184077
theorem B4128803 : Blo 1630514 4128803 := bstep (se 1 (by rfl) ⟨3096602, by rfl⟩ : syracuseStep 4128803 = 6193205) B6193205
theorem B3096625 : Blo 1630514 3096625 := bstep (se 2 (by rfl) ⟨1161234, by rfl⟩ : syracuseStep 3096625 = 2322469) B2322469
theorem B1835059 : Blo 1630514 1835059 := bstep (se 1 (by rfl) ⟨1376294, by rfl⟩ : syracuseStep 1835059 = 2752589) B2752589
theorem B2064467 : Blo 1630514 2064467 := bstep (se 1 (by rfl) ⟨1548350, by rfl⟩ : syracuseStep 2064467 = 3096701) B3096701
theorem B2752609 : Blo 1630514 2752609 := bstep (se 2 (by rfl) ⟨1032228, by rfl⟩ : syracuseStep 2752609 = 2064457) B2064457
theorem B5505137 : Blo 1630514 5505137 := bstep (se 2 (by rfl) ⟨2064426, by rfl⟩ : syracuseStep 5505137 = 4128853) B4128853
theorem B2752643 : Blo 1630514 2752643 := bstep (se 1 (by rfl) ⟨2064482, by rfl⟩ : syracuseStep 2752643 = 4128965) B4128965
theorem B1835203 : Blo 1630514 1835203 := bstep (se 1 (by rfl) ⟨1376402, by rfl⟩ : syracuseStep 1835203 = 2752805) B2752805
theorem B8372429 : Blo 1630514 8372429 := bstep (se 3 (by rfl) ⟨1569830, by rfl⟩ : syracuseStep 8372429 = 3139661) B3139661
theorem B3096785 : Blo 1630514 3096785 := bstep (se 2 (by rfl) ⟨1161294, by rfl⟩ : syracuseStep 3096785 = 2322589) B2322589
theorem B4128995 : Blo 1630514 4128995 := bstep (se 1 (by rfl) ⟨3096746, by rfl⟩ : syracuseStep 4128995 = 6193493) B6193493
theorem B7839985 : Blo 1630514 7839985 := bstep (se 2 (by rfl) ⟨2939994, by rfl⟩ : syracuseStep 7839985 = 5879989) B5879989
theorem B2752771 : Blo 1630514 2752771 := bstep (se 1 (by rfl) ⟨2064578, by rfl⟩ : syracuseStep 2752771 = 4129157) B4129157
theorem B3670289 : Blo 1630514 3670289 := bstep (se 2 (by rfl) ⟨1376358, by rfl⟩ : syracuseStep 3670289 = 2752717) B2752717
theorem B62710037 : Blo 1630514 62710037 := bstep (se 6 (by rfl) ⟨1469766, by rfl⟩ : syracuseStep 62710037 = 2939533) B2939533
theorem B3670307 : Blo 1630514 3670307 := bstep (se 1 (by rfl) ⟨2752730, by rfl⟩ : syracuseStep 3670307 = 5505461) B5505461
theorem B1630515 : Blo 1630514 1630515 := bstep (se 1 (by rfl) ⟨1222886, by rfl⟩ : syracuseStep 1630515 = 2445773) B2445773
theorem B1630531 : Blo 1630514 1630531 := bstep (se 1 (by rfl) ⟨1222898, by rfl⟩ : syracuseStep 1630531 = 2445797) B2445797
theorem B1630547 : Blo 1630514 1630547 := bstep (se 1 (by rfl) ⟨1222910, by rfl⟩ : syracuseStep 1630547 = 2445821) B2445821
theorem B1835347 : Blo 1630514 1835347 := bstep (se 1 (by rfl) ⟨1376510, by rfl⟩ : syracuseStep 1835347 = 2753021) B2753021
theorem B1630563 : Blo 1630514 1630563 := bstep (se 1 (by rfl) ⟨1222922, by rfl⟩ : syracuseStep 1630563 = 2445845) B2445845
theorem B3719537 : Blo 1630514 3719537 := bstep (se 2 (by rfl) ⟨1394826, by rfl⟩ : syracuseStep 3719537 = 2789653) B2789653
theorem B1630579 : Blo 1630514 1630579 := bstep (se 1 (by rfl) ⟨1222934, by rfl⟩ : syracuseStep 1630579 = 2445869) B2445869
theorem B1630595 : Blo 1630514 1630595 := bstep (se 1 (by rfl) ⟨1222946, by rfl⟩ : syracuseStep 1630595 = 2445893) B2445893
theorem B2752913 : Blo 1630514 2752913 := bstep (se 2 (by rfl) ⟨1032342, by rfl⟩ : syracuseStep 2752913 = 2064685) B2064685
theorem B1630611 : Blo 1630514 1630611 := bstep (se 1 (by rfl) ⟨1222958, by rfl⟩ : syracuseStep 1630611 = 2445917) B2445917
theorem B1630627 : Blo 1630514 1630627 := bstep (se 1 (by rfl) ⟨1222970, by rfl⟩ : syracuseStep 1630627 = 2445941) B2445941
theorem B1630643 : Blo 1630514 1630643 := bstep (se 1 (by rfl) ⟨1222982, by rfl⟩ : syracuseStep 1630643 = 2445965) B2445965
theorem B1630659 : Blo 1630514 1630659 := bstep (se 1 (by rfl) ⟨1222994, by rfl⟩ : syracuseStep 1630659 = 2445989) B2445989
theorem B4645325 : Blo 1630514 4645325 := bstep (se 3 (by rfl) ⟨870998, by rfl⟩ : syracuseStep 4645325 = 1741997) B1741997
theorem B2613713 : Blo 1630514 2613713 := bstep (se 2 (by rfl) ⟨980142, by rfl⟩ : syracuseStep 2613713 = 1960285) B1960285
theorem B1630675 : Blo 1630514 1630675 := bstep (se 1 (by rfl) ⟨1223006, by rfl⟩ : syracuseStep 1630675 = 2446013) B2446013
theorem B1630691 : Blo 1630514 1630691 := bstep (se 1 (by rfl) ⟨1223018, by rfl⟩ : syracuseStep 1630691 = 2446037) B2446037
theorem B1835491 : Blo 1630514 1835491 := bstep (se 1 (by rfl) ⟨1376618, by rfl⟩ : syracuseStep 1835491 = 2753237) B2753237
theorem B1630707 : Blo 1630514 1630707 := bstep (se 1 (by rfl) ⟨1223030, by rfl⟩ : syracuseStep 1630707 = 2446061) B2446061
theorem B1630723 : Blo 1630514 1630723 := bstep (se 1 (by rfl) ⟨1223042, by rfl⟩ : syracuseStep 1630723 = 2446085) B2446085
theorem B2753041 : Blo 1630514 2753041 := bstep (se 2 (by rfl) ⟨1032390, by rfl⟩ : syracuseStep 2753041 = 2064781) B2064781
theorem B1630739 : Blo 1630514 1630739 := bstep (se 1 (by rfl) ⟨1223054, by rfl⟩ : syracuseStep 1630739 = 2446109) B2446109
theorem B1630755 : Blo 1630514 1630755 := bstep (se 1 (by rfl) ⟨1223066, by rfl⟩ : syracuseStep 1630755 = 2446133) B2446133
theorem B4407853 : Blo 1630514 4407853 := bstep (se 3 (by rfl) ⟨826472, by rfl⟩ : syracuseStep 4407853 = 1652945) B1652945
theorem B3670577 : Blo 1630514 3670577 := bstep (se 2 (by rfl) ⟨1376466, by rfl⟩ : syracuseStep 3670577 = 2752933) B2752933
theorem B1630771 : Blo 1630514 1630771 := bstep (se 1 (by rfl) ⟨1223078, by rfl⟩ : syracuseStep 1630771 = 2446157) B2446157
theorem B2753075 : Blo 1630514 2753075 := bstep (se 1 (by rfl) ⟨2064806, by rfl⟩ : syracuseStep 2753075 = 4129613) B4129613
theorem B1630787 : Blo 1630514 1630787 := bstep (se 1 (by rfl) ⟨1223090, by rfl⟩ : syracuseStep 1630787 = 2446181) B2446181
theorem B3670595 : Blo 1630514 3670595 := bstep (se 1 (by rfl) ⟨2752946, by rfl⟩ : syracuseStep 3670595 = 5505893) B5505893
theorem B1630803 : Blo 1630514 1630803 := bstep (se 1 (by rfl) ⟨1223102, by rfl⟩ : syracuseStep 1630803 = 2446205) B2446205
theorem B1630819 : Blo 1630514 1630819 := bstep (se 1 (by rfl) ⟨1223114, by rfl⟩ : syracuseStep 1630819 = 2446229) B2446229
theorem B3097187 : Blo 1630514 3097187 := bstep (se 1 (by rfl) ⟨2322890, by rfl⟩ : syracuseStep 3097187 = 4645781) B4645781
theorem B1630835 : Blo 1630514 1630835 := bstep (se 1 (by rfl) ⟨1223126, by rfl⟩ : syracuseStep 1630835 = 2446253) B2446253
theorem B1835635 : Blo 1630514 1835635 := bstep (se 1 (by rfl) ⟨1376726, by rfl⟩ : syracuseStep 1835635 = 2753453) B2753453
theorem B1630851 : Blo 1630514 1630851 := bstep (se 1 (by rfl) ⟨1223138, by rfl⟩ : syracuseStep 1630851 = 2446277) B2446277
theorem B4645507 : Blo 1630514 4645507 := bstep (se 1 (by rfl) ⟨3484130, by rfl⟩ : syracuseStep 4645507 = 6968261) B6968261
theorem B11756173 : Blo 1630514 11756173 := bstep (se 3 (by rfl) ⟨2204282, by rfl⟩ : syracuseStep 11756173 = 4408565) B4408565
theorem B13075085 : Blo 1630514 13075085 := bstep (se 3 (by rfl) ⟨2451578, by rfl⟩ : syracuseStep 13075085 = 4903157) B4903157
theorem B5505677 : Blo 1630514 5505677 := bstep (se 3 (by rfl) ⟨1032314, by rfl⟩ : syracuseStep 5505677 = 2064629) B2064629
theorem B1630867 : Blo 1630514 1630867 := bstep (se 1 (by rfl) ⟨1223150, by rfl⟩ : syracuseStep 1630867 = 2446301) B2446301
theorem B1630883 : Blo 1630514 1630883 := bstep (se 1 (by rfl) ⟨1223162, by rfl⟩ : syracuseStep 1630883 = 2446325) B2446325
theorem B1630899 : Blo 1630514 1630899 := bstep (se 1 (by rfl) ⟨1223174, by rfl⟩ : syracuseStep 1630899 = 2446349) B2446349
theorem B2753203 : Blo 1630514 2753203 := bstep (se 1 (by rfl) ⟨2064902, by rfl⟩ : syracuseStep 2753203 = 4129805) B4129805
theorem B19104437 : Blo 1630514 19104437 := bstep (se 5 (by rfl) ⟨895520, by rfl⟩ : syracuseStep 19104437 = 1791041) B1791041
theorem B1630915 : Blo 1630514 1630915 := bstep (se 1 (by rfl) ⟨1223186, by rfl⟩ : syracuseStep 1630915 = 2446373) B2446373
theorem B5505731 : Blo 1630514 5505731 := bstep (se 1 (by rfl) ⟨4129298, by rfl⟩ : syracuseStep 5505731 = 8258597) B8258597
theorem B1630931 : Blo 1630514 1630931 := bstep (se 1 (by rfl) ⟨1223198, by rfl⟩ : syracuseStep 1630931 = 2446397) B2446397
theorem B1630947 : Blo 1630514 1630947 := bstep (se 1 (by rfl) ⟨1223210, by rfl⟩ : syracuseStep 1630947 = 2446421) B2446421
theorem B1630963 : Blo 1630514 1630963 := bstep (se 1 (by rfl) ⟨1223222, by rfl⟩ : syracuseStep 1630963 = 2446445) B2446445
theorem B1630979 : Blo 1630514 1630979 := bstep (se 1 (by rfl) ⟨1223234, by rfl⟩ : syracuseStep 1630979 = 2446469) B2446469
theorem B1835779 : Blo 1630514 1835779 := bstep (se 1 (by rfl) ⟨1376834, by rfl⟩ : syracuseStep 1835779 = 2753669) B2753669
theorem B1630995 : Blo 1630514 1630995 := bstep (se 1 (by rfl) ⟨1223246, by rfl⟩ : syracuseStep 1630995 = 2446493) B2446493
theorem B2065171 : Blo 1630514 2065171 := bstep (se 1 (by rfl) ⟨1548878, by rfl⟩ : syracuseStep 2065171 = 3097757) B3097757
theorem B1631011 : Blo 1630514 1631011 := bstep (se 1 (by rfl) ⟨1223258, by rfl⟩ : syracuseStep 1631011 = 2446517) B2446517
theorem B4645667 : Blo 1630514 4645667 := bstep (se 1 (by rfl) ⟨3484250, by rfl⟩ : syracuseStep 4645667 = 6968501) B6968501
theorem B1631027 : Blo 1630514 1631027 := bstep (se 1 (by rfl) ⟨1223270, by rfl⟩ : syracuseStep 1631027 = 2446541) B2446541
theorem B2753345 : Blo 1630514 2753345 := bstep (se 2 (by rfl) ⟨1032504, by rfl⟩ : syracuseStep 2753345 = 2065009) B2065009
theorem B1631043 : Blo 1630514 1631043 := bstep (se 1 (by rfl) ⟨1223282, by rfl⟩ : syracuseStep 1631043 = 2446565) B2446565
theorem B3670865 : Blo 1630514 3670865 := bstep (se 2 (by rfl) ⟨1376574, by rfl⟩ : syracuseStep 3670865 = 2753149) B2753149
theorem B1631059 : Blo 1630514 1631059 := bstep (se 1 (by rfl) ⟨1223294, by rfl⟩ : syracuseStep 1631059 = 2446589) B2446589
theorem B1631075 : Blo 1630514 1631075 := bstep (se 1 (by rfl) ⟨1223306, by rfl⟩ : syracuseStep 1631075 = 2446613) B2446613
theorem B3670883 : Blo 1630514 3670883 := bstep (se 1 (by rfl) ⟨2753162, by rfl⟩ : syracuseStep 3670883 = 5506325) B5506325
theorem B1631091 : Blo 1630514 1631091 := bstep (se 1 (by rfl) ⟨1223318, by rfl⟩ : syracuseStep 1631091 = 2446637) B2446637
theorem B2065267 : Blo 1630514 2065267 := bstep (se 1 (by rfl) ⟨1548950, by rfl⟩ : syracuseStep 2065267 = 3097901) B3097901
theorem B1631107 : Blo 1630514 1631107 := bstep (se 1 (by rfl) ⟨1223330, by rfl⟩ : syracuseStep 1631107 = 2446661) B2446661
theorem B1631123 : Blo 1630514 1631123 := bstep (se 1 (by rfl) ⟨1223342, by rfl⟩ : syracuseStep 1631123 = 2446685) B2446685
theorem B1835923 : Blo 1630514 1835923 := bstep (se 1 (by rfl) ⟨1376942, by rfl⟩ : syracuseStep 1835923 = 2753885) B2753885
theorem B1631139 : Blo 1630514 1631139 := bstep (se 1 (by rfl) ⟨1223354, by rfl⟩ : syracuseStep 1631139 = 2446709) B2446709
theorem B1631155 : Blo 1630514 1631155 := bstep (se 1 (by rfl) ⟨1223366, by rfl⟩ : syracuseStep 1631155 = 2446733) B2446733
theorem B2753473 : Blo 1630514 2753473 := bstep (se 2 (by rfl) ⟨1032552, by rfl⟩ : syracuseStep 2753473 = 2065105) B2065105
theorem B1631171 : Blo 1630514 1631171 := bstep (se 1 (by rfl) ⟨1223378, by rfl⟩ : syracuseStep 1631171 = 2446757) B2446757
theorem B70583237 : Blo 1630514 70583237 := bstep (se 4 (by rfl) ⟨6617178, by rfl⟩ : syracuseStep 70583237 = 13234357) B13234357
theorem B19104709 : Blo 1630514 19104709 := bstep (se 4 (by rfl) ⟨1791066, by rfl⟩ : syracuseStep 19104709 = 3582133) B3582133
theorem B5506001 : Blo 1630514 5506001 := bstep (se 2 (by rfl) ⟨2064750, by rfl⟩ : syracuseStep 5506001 = 4129501) B4129501
theorem B1631187 : Blo 1630514 1631187 := bstep (se 1 (by rfl) ⟨1223390, by rfl⟩ : syracuseStep 1631187 = 2446781) B2446781
theorem B1631203 : Blo 1630514 1631203 := bstep (se 1 (by rfl) ⟨1223402, by rfl⟩ : syracuseStep 1631203 = 2446805) B2446805
theorem B2753507 : Blo 1630514 2753507 := bstep (se 1 (by rfl) ⟨2065130, by rfl⟩ : syracuseStep 2753507 = 4130261) B4130261
theorem B1631219 : Blo 1630514 1631219 := bstep (se 1 (by rfl) ⟨1223414, by rfl⟩ : syracuseStep 1631219 = 2446829) B2446829
theorem B1631235 : Blo 1630514 1631235 := bstep (se 1 (by rfl) ⟨1223426, by rfl⟩ : syracuseStep 1631235 = 2446853) B2446853
theorem B1631251 : Blo 1630514 1631251 := bstep (se 1 (by rfl) ⟨1223438, by rfl⟩ : syracuseStep 1631251 = 2446877) B2446877
theorem B1631267 : Blo 1630514 1631267 := bstep (se 1 (by rfl) ⟨1223450, by rfl⟩ : syracuseStep 1631267 = 2446901) B2446901
theorem B1836067 : Blo 1630514 1836067 := bstep (se 1 (by rfl) ⟨1377050, by rfl⟩ : syracuseStep 1836067 = 2754101) B2754101
theorem B1631283 : Blo 1630514 1631283 := bstep (se 1 (by rfl) ⟨1223462, by rfl⟩ : syracuseStep 1631283 = 2446925) B2446925
theorem B1631299 : Blo 1630514 1631299 := bstep (se 1 (by rfl) ⟨1223474, by rfl⟩ : syracuseStep 1631299 = 2446949) B2446949
theorem B1631315 : Blo 1630514 1631315 := bstep (se 1 (by rfl) ⟨1223486, by rfl⟩ : syracuseStep 1631315 = 2446973) B2446973
theorem B1631331 : Blo 1630514 1631331 := bstep (se 1 (by rfl) ⟨1223498, by rfl⟩ : syracuseStep 1631331 = 2446997) B2446997
theorem B2753635 : Blo 1630514 2753635 := bstep (se 1 (by rfl) ⟨2065226, by rfl⟩ : syracuseStep 2753635 = 4130453) B4130453
theorem B3671153 : Blo 1630514 3671153 := bstep (se 2 (by rfl) ⟨1376682, by rfl⟩ : syracuseStep 3671153 = 2753365) B2753365
theorem B1631347 : Blo 1630514 1631347 := bstep (se 1 (by rfl) ⟨1223510, by rfl⟩ : syracuseStep 1631347 = 2447021) B2447021
theorem B1631363 : Blo 1630514 1631363 := bstep (se 1 (by rfl) ⟨1223522, by rfl⟩ : syracuseStep 1631363 = 2447045) B2447045
theorem B3671171 : Blo 1630514 3671171 := bstep (se 1 (by rfl) ⟨2753378, by rfl⟩ : syracuseStep 3671171 = 5506757) B5506757
theorem B4129937 : Blo 1630514 4129937 := bstep (se 2 (by rfl) ⟨1548726, by rfl⟩ : syracuseStep 4129937 = 3097453) B3097453
theorem B1631379 : Blo 1630514 1631379 := bstep (se 1 (by rfl) ⟨1223534, by rfl⟩ : syracuseStep 1631379 = 2447069) B2447069
theorem B1631395 : Blo 1630514 1631395 := bstep (se 1 (by rfl) ⟨1223546, by rfl⟩ : syracuseStep 1631395 = 2447093) B2447093
theorem B1631411 : Blo 1630514 1631411 := bstep (se 1 (by rfl) ⟨1223558, by rfl⟩ : syracuseStep 1631411 = 2447117) B2447117
theorem B1836211 : Blo 1630514 1836211 := bstep (se 1 (by rfl) ⟨1377158, by rfl⟩ : syracuseStep 1836211 = 2754317) B2754317
theorem B1631427 : Blo 1630514 1631427 := bstep (se 1 (by rfl) ⟨1223570, by rfl⟩ : syracuseStep 1631427 = 2447141) B2447141
theorem B4129987 : Blo 1630514 4129987 := bstep (se 1 (by rfl) ⟨3097490, by rfl⟩ : syracuseStep 4129987 = 6194981) B6194981
theorem B1631443 : Blo 1630514 1631443 := bstep (se 1 (by rfl) ⟨1223582, by rfl⟩ : syracuseStep 1631443 = 2447165) B2447165
theorem B1631459 : Blo 1630514 1631459 := bstep (se 1 (by rfl) ⟨1223594, by rfl⟩ : syracuseStep 1631459 = 2447189) B2447189
theorem B2753777 : Blo 1630514 2753777 := bstep (se 2 (by rfl) ⟨1032666, by rfl⟩ : syracuseStep 2753777 = 2065333) B2065333
theorem B1631475 : Blo 1630514 1631475 := bstep (se 1 (by rfl) ⟨1223606, by rfl⟩ : syracuseStep 1631475 = 2447213) B2447213
theorem B1631491 : Blo 1630514 1631491 := bstep (se 1 (by rfl) ⟨1223618, by rfl⟩ : syracuseStep 1631491 = 2447237) B2447237
theorem B1631507 : Blo 1630514 1631507 := bstep (se 1 (by rfl) ⟨1223630, by rfl⟩ : syracuseStep 1631507 = 2447261) B2447261
theorem B1631523 : Blo 1630514 1631523 := bstep (se 1 (by rfl) ⟨1223642, by rfl⟩ : syracuseStep 1631523 = 2447285) B2447285
theorem B5227811 : Blo 1630514 5227811 := bstep (se 1 (by rfl) ⟨3920858, by rfl⟩ : syracuseStep 5227811 = 7841717) B7841717
theorem B1631539 : Blo 1630514 1631539 := bstep (se 1 (by rfl) ⟨1223654, by rfl⟩ : syracuseStep 1631539 = 2447309) B2447309
theorem B1631555 : Blo 1630514 1631555 := bstep (se 1 (by rfl) ⟨1223666, by rfl⟩ : syracuseStep 1631555 = 2447333) B2447333
theorem B12387653 : Blo 1630514 12387653 := bstep (se 4 (by rfl) ⟨1161342, by rfl⟩ : syracuseStep 12387653 = 2322685) B2322685
theorem B1836355 : Blo 1630514 1836355 := bstep (se 1 (by rfl) ⟨1377266, by rfl⟩ : syracuseStep 1836355 = 2754533) B2754533
theorem B4130129 : Blo 1630514 4130129 := bstep (se 2 (by rfl) ⟨1548798, by rfl⟩ : syracuseStep 4130129 = 3097597) B3097597
theorem B1631571 : Blo 1630514 1631571 := bstep (se 1 (by rfl) ⟨1223678, by rfl⟩ : syracuseStep 1631571 = 2447357) B2447357
theorem B1631587 : Blo 1630514 1631587 := bstep (se 1 (by rfl) ⟨1223690, by rfl⟩ : syracuseStep 1631587 = 2447381) B2447381
theorem B2065763 : Blo 1630514 2065763 := bstep (se 1 (by rfl) ⟨1549322, by rfl⟩ : syracuseStep 2065763 = 3098645) B3098645
theorem B4408685 : Blo 1630514 4408685 := bstep (se 3 (by rfl) ⟨826628, by rfl⟩ : syracuseStep 4408685 = 1653257) B1653257
theorem B2753905 : Blo 1630514 2753905 := bstep (se 2 (by rfl) ⟨1032714, by rfl⟩ : syracuseStep 2753905 = 2065429) B2065429
theorem B1631603 : Blo 1630514 1631603 := bstep (se 1 (by rfl) ⟨1223702, by rfl⟩ : syracuseStep 1631603 = 2447405) B2447405
theorem B1631619 : Blo 1630514 1631619 := bstep (se 1 (by rfl) ⟨1223714, by rfl⟩ : syracuseStep 1631619 = 2447429) B2447429
theorem B3671441 : Blo 1630514 3671441 := bstep (se 2 (by rfl) ⟨1376790, by rfl⟩ : syracuseStep 3671441 = 2753581) B2753581
theorem B1631635 : Blo 1630514 1631635 := bstep (se 1 (by rfl) ⟨1223726, by rfl⟩ : syracuseStep 1631635 = 2447453) B2447453
theorem B2753939 : Blo 1630514 2753939 := bstep (se 1 (by rfl) ⟨2065454, by rfl⟩ : syracuseStep 2753939 = 4130909) B4130909
theorem B2614675 : Blo 1630514 2614675 := bstep (se 1 (by rfl) ⟨1961006, by rfl⟩ : syracuseStep 2614675 = 3922013) B3922013
theorem B1631651 : Blo 1630514 1631651 := bstep (se 1 (by rfl) ⟨1223738, by rfl⟩ : syracuseStep 1631651 = 2447477) B2447477
theorem B3671459 : Blo 1630514 3671459 := bstep (se 1 (by rfl) ⟨2753594, by rfl⟩ : syracuseStep 3671459 = 5507189) B5507189
theorem B1631667 : Blo 1630514 1631667 := bstep (se 1 (by rfl) ⟨1223750, by rfl⟩ : syracuseStep 1631667 = 2447501) B2447501
theorem B1631683 : Blo 1630514 1631683 := bstep (se 1 (by rfl) ⟨1223762, by rfl⟩ : syracuseStep 1631683 = 2447525) B2447525
theorem B2205137 : Blo 1630514 2205137 := bstep (se 2 (by rfl) ⟨826926, by rfl⟩ : syracuseStep 2205137 = 1653853) B1653853
theorem B1631699 : Blo 1630514 1631699 := bstep (se 1 (by rfl) ⟨1223774, by rfl⟩ : syracuseStep 1631699 = 2447549) B2447549
theorem B1836499 : Blo 1630514 1836499 := bstep (se 1 (by rfl) ⟨1377374, by rfl⟩ : syracuseStep 1836499 = 2754749) B2754749
theorem B1631715 : Blo 1630514 1631715 := bstep (se 1 (by rfl) ⟨1223786, by rfl⟩ : syracuseStep 1631715 = 2447573) B2447573
theorem B3098083 : Blo 1630514 3098083 := bstep (se 1 (by rfl) ⟨2323562, by rfl⟩ : syracuseStep 3098083 = 4647125) B4647125
theorem B5506541 : Blo 1630514 5506541 := bstep (se 3 (by rfl) ⟨1032476, by rfl⟩ : syracuseStep 5506541 = 2064953) B2064953
theorem B1631731 : Blo 1630514 1631731 := bstep (se 1 (by rfl) ⟨1223798, by rfl⟩ : syracuseStep 1631731 = 2447597) B2447597
theorem B1631747 : Blo 1630514 1631747 := bstep (se 1 (by rfl) ⟨1223810, by rfl⟩ : syracuseStep 1631747 = 2447621) B2447621
theorem B1631763 : Blo 1630514 1631763 := bstep (se 1 (by rfl) ⟨1223822, by rfl⟩ : syracuseStep 1631763 = 2447645) B2447645
theorem B2754067 : Blo 1630514 2754067 := bstep (se 1 (by rfl) ⟨2065550, by rfl⟩ : syracuseStep 2754067 = 4131101) B4131101
theorem B5506595 : Blo 1630514 5506595 := bstep (se 1 (by rfl) ⟨4129946, by rfl⟩ : syracuseStep 5506595 = 8259893) B8259893
theorem B1631779 : Blo 1630514 1631779 := bstep (se 1 (by rfl) ⟨1223834, by rfl⟩ : syracuseStep 1631779 = 2447669) B2447669
theorem B1631795 : Blo 1630514 1631795 := bstep (se 1 (by rfl) ⟨1223846, by rfl⟩ : syracuseStep 1631795 = 2447693) B2447693
theorem B48342581 : Blo 1630514 48342581 := bstep (se 5 (by rfl) ⟨2266058, by rfl⟩ : syracuseStep 48342581 = 4532117) B4532117
theorem B1631811 : Blo 1630514 1631811 := bstep (se 1 (by rfl) ⟨1223858, by rfl⟩ : syracuseStep 1631811 = 2447717) B2447717
theorem B1631827 : Blo 1630514 1631827 := bstep (se 1 (by rfl) ⟨1223870, by rfl⟩ : syracuseStep 1631827 = 2447741) B2447741
theorem B14886499 : Blo 1630514 14886499 := bstep (se 1 (by rfl) ⟨11164874, by rfl⟩ : syracuseStep 14886499 = 22329749) B22329749
theorem B1631843 : Blo 1630514 1631843 := bstep (se 1 (by rfl) ⟨1223882, by rfl⟩ : syracuseStep 1631843 = 2447765) B2447765
theorem B1631859 : Blo 1630514 1631859 := bstep (se 1 (by rfl) ⟨1223894, by rfl⟩ : syracuseStep 1631859 = 2447789) B2447789
theorem B1631875 : Blo 1630514 1631875 := bstep (se 1 (by rfl) ⟨1223906, by rfl⟩ : syracuseStep 1631875 = 2447813) B2447813
theorem B3098243 : Blo 1630514 3098243 := bstep (se 1 (by rfl) ⟨2323682, by rfl⟩ : syracuseStep 3098243 = 4647365) B4647365
theorem B1631891 : Blo 1630514 1631891 := bstep (se 1 (by rfl) ⟨1223918, by rfl⟩ : syracuseStep 1631891 = 2447837) B2447837
theorem B2614931 : Blo 1630514 2614931 := bstep (se 1 (by rfl) ⟨1961198, by rfl⟩ : syracuseStep 2614931 = 3922397) B3922397
theorem B2754209 : Blo 1630514 2754209 := bstep (se 2 (by rfl) ⟨1032828, by rfl⟩ : syracuseStep 2754209 = 2065657) B2065657
theorem B1631907 : Blo 1630514 1631907 := bstep (se 1 (by rfl) ⟨1223930, by rfl⟩ : syracuseStep 1631907 = 2447861) B2447861
theorem B3671729 : Blo 1630514 3671729 := bstep (se 2 (by rfl) ⟨1376898, by rfl⟩ : syracuseStep 3671729 = 2753797) B2753797
theorem B1631923 : Blo 1630514 1631923 := bstep (se 1 (by rfl) ⟨1223942, by rfl⟩ : syracuseStep 1631923 = 2447885) B2447885
theorem B3671747 : Blo 1630514 3671747 := bstep (se 1 (by rfl) ⟨2753810, by rfl⟩ : syracuseStep 3671747 = 5507621) B5507621
theorem B1631939 : Blo 1630514 1631939 := bstep (se 1 (by rfl) ⟨1223954, by rfl⟩ : syracuseStep 1631939 = 2447909) B2447909
theorem B9291469 : Blo 1630514 9291469 := bstep (se 3 (by rfl) ⟨1742150, by rfl⟩ : syracuseStep 9291469 = 3484301) B3484301
theorem B1631955 : Blo 1630514 1631955 := bstep (se 1 (by rfl) ⟨1223966, by rfl⟩ : syracuseStep 1631955 = 2447933) B2447933
theorem B1631971 : Blo 1630514 1631971 := bstep (se 1 (by rfl) ⟨1223978, by rfl⟩ : syracuseStep 1631971 = 2447957) B2447957
theorem B7440113 : Blo 1630514 7440113 := bstep (se 2 (by rfl) ⟨2790042, by rfl⟩ : syracuseStep 7440113 = 5580085) B5580085
theorem B1631987 : Blo 1630514 1631987 := bstep (se 1 (by rfl) ⟨1223990, by rfl⟩ : syracuseStep 1631987 = 2447981) B2447981
theorem B1632003 : Blo 1630514 1632003 := bstep (se 1 (by rfl) ⟨1224002, by rfl⟩ : syracuseStep 1632003 = 2448005) B2448005
theorem B1632019 : Blo 1630514 1632019 := bstep (se 1 (by rfl) ⟨1224014, by rfl⟩ : syracuseStep 1632019 = 2448029) B2448029
theorem B2754337 : Blo 1630514 2754337 := bstep (se 2 (by rfl) ⟨1032876, by rfl⟩ : syracuseStep 2754337 = 2065753) B2065753
theorem B1632035 : Blo 1630514 1632035 := bstep (se 1 (by rfl) ⟨1224026, by rfl⟩ : syracuseStep 1632035 = 2448053) B2448053
theorem B5506865 : Blo 1630514 5506865 := bstep (se 2 (by rfl) ⟨2065074, by rfl⟩ : syracuseStep 5506865 = 4130149) B4130149
theorem B1632051 : Blo 1630514 1632051 := bstep (se 1 (by rfl) ⟨1224038, by rfl⟩ : syracuseStep 1632051 = 2448077) B2448077
theorem B1632067 : Blo 1630514 1632067 := bstep (se 1 (by rfl) ⟨1224050, by rfl⟩ : syracuseStep 1632067 = 2448101) B2448101
theorem B2754371 : Blo 1630514 2754371 := bstep (se 1 (by rfl) ⟨2065778, by rfl⟩ : syracuseStep 2754371 = 4131557) B4131557
theorem B4646737 : Blo 1630514 4646737 := bstep (se 2 (by rfl) ⟨1742526, by rfl⟩ : syracuseStep 4646737 = 3485053) B3485053
theorem B1632083 : Blo 1630514 1632083 := bstep (se 1 (by rfl) ⟨1224062, by rfl⟩ : syracuseStep 1632083 = 2448125) B2448125
theorem B1632099 : Blo 1630514 1632099 := bstep (se 1 (by rfl) ⟨1224074, by rfl⟩ : syracuseStep 1632099 = 2448149) B2448149
theorem B12396401 : Blo 1630514 12396401 := bstep (se 2 (by rfl) ⟨4648650, by rfl⟩ : syracuseStep 12396401 = 9297301) B9297301
theorem B1632115 : Blo 1630514 1632115 := bstep (se 1 (by rfl) ⟨1224086, by rfl⟩ : syracuseStep 1632115 = 2448173) B2448173
theorem B1632131 : Blo 1630514 1632131 := bstep (se 1 (by rfl) ⟨1224098, by rfl⟩ : syracuseStep 1632131 = 2448197) B2448197
theorem B1632147 : Blo 1630514 1632147 := bstep (se 1 (by rfl) ⟨1224110, by rfl⟩ : syracuseStep 1632147 = 2448221) B2448221
theorem B1632163 : Blo 1630514 1632163 := bstep (se 1 (by rfl) ⟨1224122, by rfl⟩ : syracuseStep 1632163 = 2448245) B2448245
theorem B1632179 : Blo 1630514 1632179 := bstep (se 1 (by rfl) ⟨1224134, by rfl⟩ : syracuseStep 1632179 = 2448269) B2448269
theorem B1632195 : Blo 1630514 1632195 := bstep (se 1 (by rfl) ⟨1224146, by rfl⟩ : syracuseStep 1632195 = 2448293) B2448293
theorem B2754499 : Blo 1630514 2754499 := bstep (se 1 (by rfl) ⟨2065874, by rfl⟩ : syracuseStep 2754499 = 4131749) B4131749
theorem B6195149 : Blo 1630514 6195149 := bstep (se 3 (by rfl) ⟨1161590, by rfl⟩ : syracuseStep 6195149 = 2323181) B2323181
theorem B3672017 : Blo 1630514 3672017 := bstep (se 2 (by rfl) ⟨1377006, by rfl⟩ : syracuseStep 3672017 = 2754013) B2754013
theorem B1632211 : Blo 1630514 1632211 := bstep (se 1 (by rfl) ⟨1224158, by rfl⟩ : syracuseStep 1632211 = 2448317) B2448317
theorem B2205667 : Blo 1630514 2205667 := bstep (se 1 (by rfl) ⟨1654250, by rfl⟩ : syracuseStep 2205667 = 3308501) B3308501
theorem B3672035 : Blo 1630514 3672035 := bstep (se 1 (by rfl) ⟨2754026, by rfl⟩ : syracuseStep 3672035 = 5508053) B5508053
theorem B1632227 : Blo 1630514 1632227 := bstep (se 1 (by rfl) ⟨1224170, by rfl⟩ : syracuseStep 1632227 = 2448341) B2448341
theorem B8259569 : Blo 1630514 8259569 := bstep (se 2 (by rfl) ⟨3097338, by rfl⟩ : syracuseStep 8259569 = 6194677) B6194677
theorem B1632243 : Blo 1630514 1632243 := bstep (se 1 (by rfl) ⟨1224182, by rfl⟩ : syracuseStep 1632243 = 2448365) B2448365
theorem B1632259 : Blo 1630514 1632259 := bstep (se 1 (by rfl) ⟨1224194, by rfl⟩ : syracuseStep 1632259 = 2448389) B2448389
theorem B2721809 : Blo 1630514 2721809 := bstep (se 2 (by rfl) ⟨1020678, by rfl⟩ : syracuseStep 2721809 = 2041357) B2041357
theorem B1632275 : Blo 1630514 1632275 := bstep (se 1 (by rfl) ⟨1224206, by rfl⟩ : syracuseStep 1632275 = 2448413) B2448413
theorem B1632291 : Blo 1630514 1632291 := bstep (se 1 (by rfl) ⟨1224218, by rfl⟩ : syracuseStep 1632291 = 2448437) B2448437
theorem B1632307 : Blo 1630514 1632307 := bstep (se 1 (by rfl) ⟨1224230, by rfl⟩ : syracuseStep 1632307 = 2448461) B2448461
theorem B1632323 : Blo 1630514 1632323 := bstep (se 1 (by rfl) ⟨1224242, by rfl⟩ : syracuseStep 1632323 = 2448485) B2448485
theorem B3721297 : Blo 1630514 3721297 := bstep (se 2 (by rfl) ⟨1395486, by rfl⟩ : syracuseStep 3721297 = 2790973) B2790973
theorem B2754641 : Blo 1630514 2754641 := bstep (se 2 (by rfl) ⟨1032990, by rfl⟩ : syracuseStep 2754641 = 2065981) B2065981
theorem B1632339 : Blo 1630514 1632339 := bstep (se 1 (by rfl) ⟨1224254, by rfl⟩ : syracuseStep 1632339 = 2448509) B2448509
theorem B1632355 : Blo 1630514 1632355 := bstep (se 1 (by rfl) ⟨1224266, by rfl⟩ : syracuseStep 1632355 = 2448533) B2448533
theorem B5228657 : Blo 1630514 5228657 := bstep (se 2 (by rfl) ⟨1960746, by rfl⟩ : syracuseStep 5228657 = 3921493) B3921493
theorem B1632371 : Blo 1630514 1632371 := bstep (se 1 (by rfl) ⟨1224278, by rfl⟩ : syracuseStep 1632371 = 2448557) B2448557
theorem B1632387 : Blo 1630514 1632387 := bstep (se 1 (by rfl) ⟨1224290, by rfl⟩ : syracuseStep 1632387 = 2448581) B2448581
theorem B1632403 : Blo 1630514 1632403 := bstep (se 1 (by rfl) ⟨1224302, by rfl⟩ : syracuseStep 1632403 = 2448605) B2448605
theorem B5228707 : Blo 1630514 5228707 := bstep (se 1 (by rfl) ⟨3921530, by rfl⟩ : syracuseStep 5228707 = 7843061) B7843061
theorem B1632419 : Blo 1630514 1632419 := bstep (se 1 (by rfl) ⟨1224314, by rfl⟩ : syracuseStep 1632419 = 2448629) B2448629
theorem B1632435 : Blo 1630514 1632435 := bstep (se 1 (by rfl) ⟨1224326, by rfl⟩ : syracuseStep 1632435 = 2448653) B2448653
theorem B1632451 : Blo 1630514 1632451 := bstep (se 1 (by rfl) ⟨1224338, by rfl⟩ : syracuseStep 1632451 = 2448677) B2448677
theorem B3483857 : Blo 1630514 3483857 := bstep (se 2 (by rfl) ⟨1306446, by rfl⟩ : syracuseStep 3483857 = 2612893) B2612893
theorem B2754769 : Blo 1630514 2754769 := bstep (se 2 (by rfl) ⟨1033038, by rfl⟩ : syracuseStep 2754769 = 2066077) B2066077
theorem B1632467 : Blo 1630514 1632467 := bstep (se 1 (by rfl) ⟨1224350, by rfl⟩ : syracuseStep 1632467 = 2448701) B2448701
theorem B1632483 : Blo 1630514 1632483 := bstep (se 1 (by rfl) ⟨1224362, by rfl⟩ : syracuseStep 1632483 = 2448725) B2448725
theorem B3672305 : Blo 1630514 3672305 := bstep (se 2 (by rfl) ⟨1377114, by rfl⟩ : syracuseStep 3672305 = 2754229) B2754229
theorem B2754803 : Blo 1630514 2754803 := bstep (se 1 (by rfl) ⟨2066102, by rfl⟩ : syracuseStep 2754803 = 4132205) B4132205
theorem B1632499 : Blo 1630514 1632499 := bstep (se 1 (by rfl) ⟨1224374, by rfl⟩ : syracuseStep 1632499 = 2448749) B2448749
theorem B3672323 : Blo 1630514 3672323 := bstep (se 1 (by rfl) ⟨2754242, by rfl⟩ : syracuseStep 3672323 = 5508485) B5508485
theorem B4131121 : Blo 1630514 4131121 := bstep (se 2 (by rfl) ⟨1549170, by rfl⟩ : syracuseStep 4131121 = 3098341) B3098341
theorem B5507405 : Blo 1630514 5507405 := bstep (se 3 (by rfl) ⟨1032638, by rfl⟩ : syracuseStep 5507405 = 2065277) B2065277
theorem B10447217 : Blo 1630514 10447217 := bstep (se 2 (by rfl) ⟨3917706, by rfl⟩ : syracuseStep 10447217 = 7835413) B7835413
theorem B5507459 : Blo 1630514 5507459 := bstep (se 1 (by rfl) ⟨4130594, by rfl⟩ : syracuseStep 5507459 = 8261189) B8261189
theorem B3672593 : Blo 1630514 3672593 := bstep (se 2 (by rfl) ⟨1377222, by rfl⟩ : syracuseStep 3672593 = 2754445) B2754445
theorem B3672611 : Blo 1630514 3672611 := bstep (se 1 (by rfl) ⟨2754458, by rfl⟩ : syracuseStep 3672611 = 5508917) B5508917
theorem B31369781 : Blo 1630514 31369781 := bstep (se 5 (by rfl) ⟨1470458, by rfl⟩ : syracuseStep 31369781 = 2940917) B2940917
theorem B4131395 : Blo 1630514 4131395 := bstep (se 1 (by rfl) ⟨3098546, by rfl⟩ : syracuseStep 4131395 = 6197093) B6197093
theorem B5507729 : Blo 1630514 5507729 := bstep (se 2 (by rfl) ⟨2065398, by rfl⟩ : syracuseStep 5507729 = 4130797) B4130797
theorem B3484387 : Blo 1630514 3484387 := bstep (se 1 (by rfl) ⟨2613290, by rfl⟩ : syracuseStep 3484387 = 5226581) B5226581
theorem B6195953 : Blo 1630514 6195953 := bstep (se 2 (by rfl) ⟨2323482, by rfl⟩ : syracuseStep 6195953 = 4646965) B4646965
theorem B4131587 : Blo 1630514 4131587 := bstep (se 1 (by rfl) ⟨3098690, by rfl⟩ : syracuseStep 4131587 = 6197381) B6197381
theorem B1960723 : Blo 1630514 1960723 := bstep (se 1 (by rfl) ⟨1470542, by rfl⟩ : syracuseStep 1960723 = 2941085) B2941085
theorem B3672881 : Blo 1630514 3672881 := bstep (se 2 (by rfl) ⟨1377330, by rfl⟩ : syracuseStep 3672881 = 2754661) B2754661
theorem B2829107 : Blo 1630514 2829107 := bstep (se 1 (by rfl) ⟨2121830, by rfl⟩ : syracuseStep 2829107 = 4243661) B4243661
theorem B3672899 : Blo 1630514 3672899 := bstep (se 1 (by rfl) ⟨2754674, by rfl⟩ : syracuseStep 3672899 = 5509349) B5509349
theorem B3918755 : Blo 1630514 3918755 := bstep (se 1 (by rfl) ⟨2939066, by rfl⟩ : syracuseStep 3918755 = 5878133) B5878133
theorem B6614065 : Blo 1630514 6614065 := bstep (se 2 (by rfl) ⟨2480274, by rfl⟩ : syracuseStep 6614065 = 4960549) B4960549
theorem B4648013 : Blo 1630514 4648013 := bstep (se 3 (by rfl) ⟨871502, by rfl⟩ : syracuseStep 4648013 = 1743005) B1743005
theorem B52939889 : Blo 1630514 52939889 := bstep (se 2 (by rfl) ⟨19852458, by rfl⟩ : syracuseStep 52939889 = 39704917) B39704917
theorem B3533987 : Blo 1630514 3533987 := bstep (se 1 (by rfl) ⟨2650490, by rfl⟩ : syracuseStep 3533987 = 5300981) B5300981
theorem B5508269 : Blo 1630514 5508269 := bstep (se 3 (by rfl) ⟨1032800, by rfl⟩ : syracuseStep 5508269 = 2065601) B2065601
theorem B5508323 : Blo 1630514 5508323 := bstep (se 1 (by rfl) ⟨4131242, by rfl⟩ : syracuseStep 5508323 = 8262485) B8262485
theorem B1789171 : Blo 1630514 1789171 := bstep (se 1 (by rfl) ⟨1341878, by rfl⟩ : syracuseStep 1789171 = 2683757) B2683757
theorem B4648195 : Blo 1630514 4648195 := bstep (se 1 (by rfl) ⟨3486146, by rfl⟩ : syracuseStep 4648195 = 6972293) B6972293
theorem B4648241 : Blo 1630514 4648241 := bstep (se 2 (by rfl) ⟨1743090, by rfl⟩ : syracuseStep 4648241 = 3486181) B3486181
theorem B5229937 : Blo 1630514 5229937 := bstep (se 2 (by rfl) ⟨1961226, by rfl⟩ : syracuseStep 5229937 = 3922453) B3922453
theorem B6196621 : Blo 1630514 6196621 := bstep (se 3 (by rfl) ⟨1161866, by rfl⟩ : syracuseStep 6196621 = 2323733) B2323733
theorem B10448291 : Blo 1630514 10448291 := bstep (se 1 (by rfl) ⟨7836218, by rfl⟩ : syracuseStep 10448291 = 15672437) B15672437
theorem B8261027 : Blo 1630514 8261027 := bstep (se 1 (by rfl) ⟨6195770, by rfl⟩ : syracuseStep 8261027 = 12391541) B12391541
theorem B5508593 : Blo 1630514 5508593 := bstep (se 2 (by rfl) ⟨2065722, by rfl⟩ : syracuseStep 5508593 = 4131445) B4131445
theorem B9293453 : Blo 1630514 9293453 := bstep (se 3 (by rfl) ⟨1742522, by rfl⟩ : syracuseStep 9293453 = 3485045) B3485045
theorem B5295889 : Blo 1630514 5295889 := bstep (se 2 (by rfl) ⟨1985958, by rfl⟩ : syracuseStep 5295889 = 3971917) B3971917
theorem B7843661 : Blo 1630514 7843661 := bstep (se 3 (by rfl) ⟨1470686, by rfl⟩ : syracuseStep 7843661 = 2941373) B2941373
theorem B2322275 : Blo 1630514 2322275 := bstep (se 1 (by rfl) ⟨1741706, by rfl⟩ : syracuseStep 2322275 = 3483413) B3483413
theorem B6279011 : Blo 1630514 6279011 := bstep (se 1 (by rfl) ⟨4709258, by rfl⟩ : syracuseStep 6279011 = 9418517) B9418517
theorem B4411313 : Blo 1630514 4411313 := bstep (se 2 (by rfl) ⟨1654242, by rfl⟩ : syracuseStep 4411313 = 3308485) B3308485
theorem B5509133 : Blo 1630514 5509133 := bstep (se 3 (by rfl) ⟨1032962, by rfl⟩ : syracuseStep 5509133 = 2065925) B2065925
theorem B5509187 : Blo 1630514 5509187 := bstep (se 1 (by rfl) ⟨4131890, by rfl⟩ : syracuseStep 5509187 = 8263781) B8263781
theorem B12382307 : Blo 1630514 12382307 := bstep (se 1 (by rfl) ⟨9286730, by rfl⟩ : syracuseStep 12382307 = 18573461) B18573461
theorem B3919985 : Blo 1630514 3919985 := bstep (se 2 (by rfl) ⟨1469994, by rfl⟩ : syracuseStep 3919985 = 2939989) B2939989
theorem B6197411 : Blo 1630514 6197411 := bstep (se 1 (by rfl) ⟨4648058, by rfl⟩ : syracuseStep 6197411 = 9296117) B9296117
theorem B3485873 : Blo 1630514 3485873 := bstep (se 2 (by rfl) ⟨1307202, by rfl⟩ : syracuseStep 3485873 = 2614405) B2614405
theorem B3485891 : Blo 1630514 3485891 := bstep (se 1 (by rfl) ⟨2614418, by rfl⟩ : syracuseStep 3485891 = 5228837) B5228837
theorem B10055885 : Blo 1630514 10055885 := bstep (se 3 (by rfl) ⟨1885478, by rfl⟩ : syracuseStep 10055885 = 3770957) B3770957
theorem B8261837 : Blo 1630514 8261837 := bstep (se 3 (by rfl) ⟨1549094, by rfl⟩ : syracuseStep 8261837 = 3098189) B3098189
theorem B2650337 : Blo 1630514 2650337 := bstep (se 2 (by rfl) ⟨993876, by rfl⟩ : syracuseStep 2650337 = 1987753) B1987753
theorem B1675571 : Blo 1630514 1675571 := bstep (se 1 (by rfl) ⟨1256678, by rfl⟩ : syracuseStep 1675571 = 2513357) B2513357
theorem B5509457 : Blo 1630514 5509457 := bstep (se 2 (by rfl) ⟨2066046, by rfl⟩ : syracuseStep 5509457 = 4132093) B4132093
theorem B1765747 : Blo 1630514 1765747 := bstep (se 1 (by rfl) ⟨1324310, by rfl⟩ : syracuseStep 1765747 = 2648621) B2648621
theorem B3305873 : Blo 1630514 3305873 := bstep (se 2 (by rfl) ⟨1239702, by rfl⟩ : syracuseStep 3305873 = 2479405) B2479405
theorem B2445779 : Blo 1630514 2445779 := bstep (se 1 (by rfl) ⟨1834334, by rfl⟩ : syracuseStep 2445779 = 3668669) B3668669
theorem B2322913 : Blo 1630514 2322913 := bstep (se 2 (by rfl) ⟨871092, by rfl⟩ : syracuseStep 2322913 = 1742185) B1742185
theorem B2445809 : Blo 1630514 2445809 := bstep (se 2 (by rfl) ⟨917178, by rfl⟩ : syracuseStep 2445809 = 1834357) B1834357
theorem B2445827 : Blo 1630514 2445827 := bstep (se 1 (by rfl) ⟨1834370, by rfl⟩ : syracuseStep 2445827 = 3668741) B3668741
theorem B2445857 : Blo 1630514 2445857 := bstep (se 2 (by rfl) ⟨917196, by rfl⟩ : syracuseStep 2445857 = 1834393) B1834393
theorem B9294385 : Blo 1630514 9294385 := bstep (se 2 (by rfl) ⟨3485394, by rfl⟩ : syracuseStep 9294385 = 6970789) B6970789
theorem B2445875 : Blo 1630514 2445875 := bstep (se 1 (by rfl) ⟨1834406, by rfl⟩ : syracuseStep 2445875 = 3668813) B3668813
theorem B2445905 : Blo 1630514 2445905 := bstep (se 2 (by rfl) ⟨917214, by rfl⟩ : syracuseStep 2445905 = 1834429) B1834429
theorem B2323027 : Blo 1630514 2323027 := bstep (se 1 (by rfl) ⟨1742270, by rfl⟩ : syracuseStep 2323027 = 3484541) B3484541
theorem B2445923 : Blo 1630514 2445923 := bstep (se 1 (by rfl) ⟨1834442, by rfl⟩ : syracuseStep 2445923 = 3668885) B3668885
theorem B2790001 : Blo 1630514 2790001 := bstep (se 2 (by rfl) ⟨1046250, by rfl⟩ : syracuseStep 2790001 = 2092501) B2092501
theorem B2445953 : Blo 1630514 2445953 := bstep (se 2 (by rfl) ⟨917232, by rfl⟩ : syracuseStep 2445953 = 1834465) B1834465
theorem B2445971 : Blo 1630514 2445971 := bstep (se 1 (by rfl) ⟨1834478, by rfl⟩ : syracuseStep 2445971 = 3668957) B3668957
theorem B2446001 : Blo 1630514 2446001 := bstep (se 2 (by rfl) ⟨917250, by rfl⟩ : syracuseStep 2446001 = 1834501) B1834501
theorem B2446019 : Blo 1630514 2446019 := bstep (se 1 (by rfl) ⟨1834514, by rfl⟩ : syracuseStep 2446019 = 3669029) B3669029
theorem B2355923 : Blo 1630514 2355923 := bstep (se 1 (by rfl) ⟨1766942, by rfl⟩ : syracuseStep 2355923 = 3533885) B3533885
theorem B2446049 : Blo 1630514 2446049 := bstep (se 2 (by rfl) ⟨917268, by rfl⟩ : syracuseStep 2446049 = 1834537) B1834537
theorem B2446067 : Blo 1630514 2446067 := bstep (se 1 (by rfl) ⟨1834550, by rfl⟩ : syracuseStep 2446067 = 3669101) B3669101
theorem B2446097 : Blo 1630514 2446097 := bstep (se 2 (by rfl) ⟨917286, by rfl⟩ : syracuseStep 2446097 = 1834573) B1834573
theorem B2446115 : Blo 1630514 2446115 := bstep (se 1 (by rfl) ⟨1834586, by rfl⟩ : syracuseStep 2446115 = 3669173) B3669173
theorem B6198065 : Blo 1630514 6198065 := bstep (se 2 (by rfl) ⟨2324274, by rfl⟩ : syracuseStep 6198065 = 4648549) B4648549
theorem B2446145 : Blo 1630514 2446145 := bstep (se 2 (by rfl) ⟨917304, by rfl⟩ : syracuseStep 2446145 = 1834609) B1834609
theorem B2446163 : Blo 1630514 2446163 := bstep (se 1 (by rfl) ⟨1834622, by rfl⟩ : syracuseStep 2446163 = 3669245) B3669245
theorem B2446193 : Blo 1630514 2446193 := bstep (se 2 (by rfl) ⟨917322, by rfl⟩ : syracuseStep 2446193 = 1834645) B1834645
theorem B6968177 : Blo 1630514 6968177 := bstep (se 2 (by rfl) ⟨2613066, by rfl⟩ : syracuseStep 6968177 = 5226133) B5226133
theorem B2446211 : Blo 1630514 2446211 := bstep (se 1 (by rfl) ⟨1834658, by rfl⟩ : syracuseStep 2446211 = 3669317) B3669317
theorem B2446241 : Blo 1630514 2446241 := bstep (se 2 (by rfl) ⟨917340, by rfl⟩ : syracuseStep 2446241 = 1834681) B1834681
theorem B6968227 : Blo 1630514 6968227 := bstep (se 1 (by rfl) ⟨5226170, by rfl⟩ : syracuseStep 6968227 = 10452341) B10452341
theorem B2446259 : Blo 1630514 2446259 := bstep (se 1 (by rfl) ⟨1834694, by rfl⟩ : syracuseStep 2446259 = 3669389) B3669389
theorem B2446289 : Blo 1630514 2446289 := bstep (se 2 (by rfl) ⟨917358, by rfl⟩ : syracuseStep 2446289 = 1834717) B1834717
theorem B2446307 : Blo 1630514 2446307 := bstep (se 1 (by rfl) ⟨1834730, by rfl⟩ : syracuseStep 2446307 = 3669461) B3669461
theorem B35754979 : Blo 1630514 35754979 := bstep (se 1 (by rfl) ⟨26816234, by rfl⟩ : syracuseStep 35754979 = 53632469) B53632469
theorem B2446337 : Blo 1630514 2446337 := bstep (se 2 (by rfl) ⟨917376, by rfl⟩ : syracuseStep 2446337 = 1834753) B1834753
theorem B2446355 : Blo 1630514 2446355 := bstep (se 1 (by rfl) ⟨1834766, by rfl⟩ : syracuseStep 2446355 = 3669533) B3669533
theorem B1741843 : Blo 1630514 1741843 := bstep (se 1 (by rfl) ⟨1306382, by rfl⟩ : syracuseStep 1741843 = 2612765) B2612765
theorem B2446385 : Blo 1630514 2446385 := bstep (se 2 (by rfl) ⟨917394, by rfl⟩ : syracuseStep 2446385 = 1834789) B1834789
theorem B2446403 : Blo 1630514 2446403 := bstep (se 1 (by rfl) ⟨1834802, by rfl⟩ : syracuseStep 2446403 = 3669605) B3669605
theorem B2446433 : Blo 1630514 2446433 := bstep (se 2 (by rfl) ⟨917412, by rfl⟩ : syracuseStep 2446433 = 1834825) B1834825
theorem B2446451 : Blo 1630514 2446451 := bstep (se 1 (by rfl) ⟨1834838, by rfl⟩ : syracuseStep 2446451 = 3669677) B3669677
theorem B36254861 : Blo 1630514 36254861 := bstep (se 3 (by rfl) ⟨6797786, by rfl⟩ : syracuseStep 36254861 = 13595573) B13595573
theorem B2446481 : Blo 1630514 2446481 := bstep (se 2 (by rfl) ⟨917430, by rfl⟩ : syracuseStep 2446481 = 1834861) B1834861
theorem B2446499 : Blo 1630514 2446499 := bstep (se 1 (by rfl) ⟨1834874, by rfl⟩ : syracuseStep 2446499 = 3669749) B3669749
theorem B2446529 : Blo 1630514 2446529 := bstep (se 2 (by rfl) ⟨917448, by rfl⟩ : syracuseStep 2446529 = 1834897) B1834897
theorem B2446547 : Blo 1630514 2446547 := bstep (se 1 (by rfl) ⟨1834910, by rfl⟩ : syracuseStep 2446547 = 3669821) B3669821
theorem B2446577 : Blo 1630514 2446577 := bstep (se 2 (by rfl) ⟨917466, by rfl⟩ : syracuseStep 2446577 = 1834933) B1834933
theorem B2446595 : Blo 1630514 2446595 := bstep (se 1 (by rfl) ⟨1834946, by rfl⟩ : syracuseStep 2446595 = 3669893) B3669893
theorem B2446625 : Blo 1630514 2446625 := bstep (se 2 (by rfl) ⟨917484, by rfl⟩ : syracuseStep 2446625 = 1834969) B1834969
theorem B2446643 : Blo 1630514 2446643 := bstep (se 1 (by rfl) ⟨1834982, by rfl⟩ : syracuseStep 2446643 = 3669965) B3669965
theorem B2446673 : Blo 1630514 2446673 := bstep (se 2 (by rfl) ⟨917502, by rfl⟩ : syracuseStep 2446673 = 1835005) B1835005
theorem B2446691 : Blo 1630514 2446691 := bstep (se 1 (by rfl) ⟨1835018, by rfl⟩ : syracuseStep 2446691 = 3670037) B3670037
theorem B2446721 : Blo 1630514 2446721 := bstep (se 2 (by rfl) ⟨917520, by rfl⟩ : syracuseStep 2446721 = 1835041) B1835041
theorem B2446739 : Blo 1630514 2446739 := bstep (se 1 (by rfl) ⟨1835054, by rfl⟩ : syracuseStep 2446739 = 3670109) B3670109
theorem B2446769 : Blo 1630514 2446769 := bstep (se 2 (by rfl) ⟨917538, by rfl⟩ : syracuseStep 2446769 = 1835077) B1835077
theorem B2446787 : Blo 1630514 2446787 := bstep (se 1 (by rfl) ⟨1835090, by rfl⟩ : syracuseStep 2446787 = 3670181) B3670181
theorem B5223889 : Blo 1630514 5223889 := bstep (se 2 (by rfl) ⟨1958958, by rfl⟩ : syracuseStep 5223889 = 3917917) B3917917
theorem B2446817 : Blo 1630514 2446817 := bstep (se 2 (by rfl) ⟨917556, by rfl⟩ : syracuseStep 2446817 = 1835113) B1835113
theorem B2446835 : Blo 1630514 2446835 := bstep (se 1 (by rfl) ⟨1835126, by rfl⟩ : syracuseStep 2446835 = 3670253) B3670253
theorem B2446865 : Blo 1630514 2446865 := bstep (se 2 (by rfl) ⟨917574, by rfl⟩ : syracuseStep 2446865 = 1835149) B1835149
theorem B2446883 : Blo 1630514 2446883 := bstep (se 1 (by rfl) ⟨1835162, by rfl⟩ : syracuseStep 2446883 = 3670325) B3670325
theorem B2446913 : Blo 1630514 2446913 := bstep (se 2 (by rfl) ⟨917592, by rfl⟩ : syracuseStep 2446913 = 1835185) B1835185
theorem B2446931 : Blo 1630514 2446931 := bstep (se 1 (by rfl) ⟨1835198, by rfl⟩ : syracuseStep 2446931 = 3670397) B3670397
theorem B11753059 : Blo 1630514 11753059 := bstep (se 1 (by rfl) ⟨8814794, by rfl⟩ : syracuseStep 11753059 = 17629589) B17629589
theorem B6616675 : Blo 1630514 6616675 := bstep (se 1 (by rfl) ⟨4962506, by rfl⟩ : syracuseStep 6616675 = 9925013) B9925013
theorem B2446961 : Blo 1630514 2446961 := bstep (se 2 (by rfl) ⟨917610, by rfl⟩ : syracuseStep 2446961 = 1835221) B1835221
theorem B2479745 : Blo 1630514 2479745 := bstep (se 2 (by rfl) ⟨929904, by rfl⟩ : syracuseStep 2479745 = 1859809) B1859809
theorem B2446979 : Blo 1630514 2446979 := bstep (se 1 (by rfl) ⟨1835234, by rfl⟩ : syracuseStep 2446979 = 3670469) B3670469
theorem B1742467 : Blo 1630514 1742467 := bstep (se 1 (by rfl) ⟨1306850, by rfl⟩ : syracuseStep 1742467 = 2613701) B2613701
theorem B2791057 : Blo 1630514 2791057 := bstep (se 2 (by rfl) ⟨1046646, by rfl⟩ : syracuseStep 2791057 = 2093293) B2093293
theorem B2447009 : Blo 1630514 2447009 := bstep (se 2 (by rfl) ⟨917628, by rfl⟩ : syracuseStep 2447009 = 1835257) B1835257
theorem B2447027 : Blo 1630514 2447027 := bstep (se 1 (by rfl) ⟨1835270, by rfl⟩ : syracuseStep 2447027 = 3670541) B3670541
theorem B2447057 : Blo 1630514 2447057 := bstep (se 2 (by rfl) ⟨917646, by rfl⟩ : syracuseStep 2447057 = 1835293) B1835293
theorem B7837411 : Blo 1630514 7837411 := bstep (se 1 (by rfl) ⟨5878058, by rfl⟩ : syracuseStep 7837411 = 11756117) B11756117
theorem B2447075 : Blo 1630514 2447075 := bstep (se 1 (by rfl) ⟨1835306, by rfl⟩ : syracuseStep 2447075 = 3670613) B3670613
theorem B2447105 : Blo 1630514 2447105 := bstep (se 2 (by rfl) ⟨917664, by rfl⟩ : syracuseStep 2447105 = 1835329) B1835329
theorem B2447123 : Blo 1630514 2447123 := bstep (se 1 (by rfl) ⟨1835342, by rfl⟩ : syracuseStep 2447123 = 3670685) B3670685
theorem B2447153 : Blo 1630514 2447153 := bstep (se 2 (by rfl) ⟨917682, by rfl⟩ : syracuseStep 2447153 = 1835365) B1835365
theorem B2447171 : Blo 1630514 2447171 := bstep (se 1 (by rfl) ⟨1835378, by rfl⟩ : syracuseStep 2447171 = 3670757) B3670757
theorem B2447201 : Blo 1630514 2447201 := bstep (se 2 (by rfl) ⟨917700, by rfl⟩ : syracuseStep 2447201 = 1835401) B1835401
theorem B2447219 : Blo 1630514 2447219 := bstep (se 1 (by rfl) ⟨1835414, by rfl⟩ : syracuseStep 2447219 = 3670829) B3670829
theorem B2447249 : Blo 1630514 2447249 := bstep (se 2 (by rfl) ⟨917718, by rfl⟩ : syracuseStep 2447249 = 1835437) B1835437
theorem B2324371 : Blo 1630514 2324371 := bstep (se 1 (by rfl) ⟨1743278, by rfl⟩ : syracuseStep 2324371 = 3486557) B3486557
theorem B2447267 : Blo 1630514 2447267 := bstep (se 1 (by rfl) ⟨1835450, by rfl⟩ : syracuseStep 2447267 = 3670901) B3670901
theorem B2447297 : Blo 1630514 2447297 := bstep (se 2 (by rfl) ⟨917736, by rfl⟩ : syracuseStep 2447297 = 1835473) B1835473
theorem B9287621 : Blo 1630514 9287621 := bstep (se 4 (by rfl) ⟨870714, by rfl⟩ : syracuseStep 9287621 = 1741429) B1741429
theorem B8820677 : Blo 1630514 8820677 := bstep (se 4 (by rfl) ⟨826938, by rfl⟩ : syracuseStep 8820677 = 1653877) B1653877
theorem B2447315 : Blo 1630514 2447315 := bstep (se 1 (by rfl) ⟨1835486, by rfl⟩ : syracuseStep 2447315 = 3670973) B3670973
theorem B9295843 : Blo 1630514 9295843 := bstep (se 1 (by rfl) ⟨6971882, by rfl⟩ : syracuseStep 9295843 = 13943765) B13943765
theorem B2447345 : Blo 1630514 2447345 := bstep (se 2 (by rfl) ⟨917754, by rfl⟩ : syracuseStep 2447345 = 1835509) B1835509
theorem B2447363 : Blo 1630514 2447363 := bstep (se 1 (by rfl) ⟨1835522, by rfl⟩ : syracuseStep 2447363 = 3671045) B3671045
theorem B13932557 : Blo 1630514 13932557 := bstep (se 3 (by rfl) ⟨2612354, by rfl⟩ : syracuseStep 13932557 = 5224709) B5224709
theorem B2447393 : Blo 1630514 2447393 := bstep (se 2 (by rfl) ⟨917772, by rfl⟩ : syracuseStep 2447393 = 1835545) B1835545
theorem B5224493 : Blo 1630514 5224493 := bstep (se 3 (by rfl) ⟨979592, by rfl⟩ : syracuseStep 5224493 = 1959185) B1959185
theorem B2447411 : Blo 1630514 2447411 := bstep (se 1 (by rfl) ⟨1835558, by rfl⟩ : syracuseStep 2447411 = 3671117) B3671117
theorem B2447441 : Blo 1630514 2447441 := bstep (se 2 (by rfl) ⟨917790, by rfl⟩ : syracuseStep 2447441 = 1835581) B1835581
theorem B2447459 : Blo 1630514 2447459 := bstep (se 1 (by rfl) ⟨1835594, by rfl⟩ : syracuseStep 2447459 = 3671189) B3671189
theorem B5503085 : Blo 1630514 5503085 := bstep (se 3 (by rfl) ⟨1031828, by rfl⟩ : syracuseStep 5503085 = 2063657) B2063657
theorem B2447489 : Blo 1630514 2447489 := bstep (se 2 (by rfl) ⟨917808, by rfl⟩ : syracuseStep 2447489 = 1835617) B1835617
theorem B2447507 : Blo 1630514 2447507 := bstep (se 1 (by rfl) ⟨1835630, by rfl⟩ : syracuseStep 2447507 = 3671261) B3671261
theorem B5503139 : Blo 1630514 5503139 := bstep (se 1 (by rfl) ⟨4127354, by rfl⟩ : syracuseStep 5503139 = 8254709) B8254709
theorem B2447537 : Blo 1630514 2447537 := bstep (se 2 (by rfl) ⟨917826, by rfl⟩ : syracuseStep 2447537 = 1835653) B1835653
theorem B10459313 : Blo 1630514 10459313 := bstep (se 2 (by rfl) ⟨3922242, by rfl⟩ : syracuseStep 10459313 = 7844485) B7844485
theorem B2447555 : Blo 1630514 2447555 := bstep (se 1 (by rfl) ⟨1835666, by rfl⟩ : syracuseStep 2447555 = 3671333) B3671333
theorem B2447585 : Blo 1630514 2447585 := bstep (se 2 (by rfl) ⟨917844, by rfl⟩ : syracuseStep 2447585 = 1835689) B1835689
theorem B2447603 : Blo 1630514 2447603 := bstep (se 1 (by rfl) ⟨1835702, by rfl⟩ : syracuseStep 2447603 = 3671405) B3671405
theorem B2447633 : Blo 1630514 2447633 := bstep (se 2 (by rfl) ⟨917862, by rfl⟩ : syracuseStep 2447633 = 1835725) B1835725
theorem B2447651 : Blo 1630514 2447651 := bstep (se 1 (by rfl) ⟨1835738, by rfl⟩ : syracuseStep 2447651 = 3671477) B3671477
theorem B2447681 : Blo 1630514 2447681 := bstep (se 2 (by rfl) ⟨917880, by rfl⟩ : syracuseStep 2447681 = 1835761) B1835761
theorem B2939203 : Blo 1630514 2939203 := bstep (se 1 (by rfl) ⟨2204402, by rfl⟩ : syracuseStep 2939203 = 4408805) B4408805
theorem B2447699 : Blo 1630514 2447699 := bstep (se 1 (by rfl) ⟨1835774, by rfl⟩ : syracuseStep 2447699 = 3671549) B3671549
theorem B8255843 : Blo 1630514 8255843 := bstep (se 1 (by rfl) ⟨6191882, by rfl⟩ : syracuseStep 8255843 = 12383765) B12383765
theorem B2447729 : Blo 1630514 2447729 := bstep (se 2 (by rfl) ⟨917898, by rfl⟩ : syracuseStep 2447729 = 1835797) B1835797
theorem B2447747 : Blo 1630514 2447747 := bstep (se 1 (by rfl) ⟨1835810, by rfl⟩ : syracuseStep 2447747 = 3671621) B3671621
theorem B2980241 : Blo 1630514 2980241 := bstep (se 2 (by rfl) ⟨1117590, by rfl⟩ : syracuseStep 2980241 = 2235181) B2235181
theorem B2447777 : Blo 1630514 2447777 := bstep (se 2 (by rfl) ⟨917916, by rfl⟩ : syracuseStep 2447777 = 1835833) B1835833
theorem B3922339 : Blo 1630514 3922339 := bstep (se 1 (by rfl) ⟨2941754, by rfl⟩ : syracuseStep 3922339 = 5883509) B5883509
theorem B5503409 : Blo 1630514 5503409 := bstep (se 2 (by rfl) ⟨2063778, by rfl⟩ : syracuseStep 5503409 = 4127557) B4127557
theorem B2447795 : Blo 1630514 2447795 := bstep (se 1 (by rfl) ⟨1835846, by rfl⟩ : syracuseStep 2447795 = 3671693) B3671693
theorem B2447825 : Blo 1630514 2447825 := bstep (se 2 (by rfl) ⟨917934, by rfl⟩ : syracuseStep 2447825 = 1835869) B1835869
theorem B2447843 : Blo 1630514 2447843 := bstep (se 1 (by rfl) ⟨1835882, by rfl⟩ : syracuseStep 2447843 = 3671765) B3671765
theorem B9296369 : Blo 1630514 9296369 := bstep (se 2 (by rfl) ⟨3486138, by rfl⟩ : syracuseStep 9296369 = 6972277) B6972277
theorem B2447873 : Blo 1630514 2447873 := bstep (se 2 (by rfl) ⟨917952, by rfl⟩ : syracuseStep 2447873 = 1835905) B1835905
theorem B19847693 : Blo 1630514 19847693 := bstep (se 3 (by rfl) ⟨3721442, by rfl⟩ : syracuseStep 19847693 = 7442885) B7442885
theorem B2447891 : Blo 1630514 2447891 := bstep (se 1 (by rfl) ⟨1835918, by rfl⟩ : syracuseStep 2447891 = 3671837) B3671837
theorem B2447921 : Blo 1630514 2447921 := bstep (se 2 (by rfl) ⟨917970, by rfl⟩ : syracuseStep 2447921 = 1835941) B1835941
theorem B2447939 : Blo 1630514 2447939 := bstep (se 1 (by rfl) ⟨1835954, by rfl⟩ : syracuseStep 2447939 = 3671909) B3671909
theorem B2447969 : Blo 1630514 2447969 := bstep (se 2 (by rfl) ⟨917988, by rfl⟩ : syracuseStep 2447969 = 1835977) B1835977
theorem B4127345 : Blo 1630514 4127345 := bstep (se 2 (by rfl) ⟨1547754, by rfl⟩ : syracuseStep 4127345 = 3095509) B3095509
theorem B2447987 : Blo 1630514 2447987 := bstep (se 1 (by rfl) ⟨1835990, by rfl⟩ : syracuseStep 2447987 = 3671981) B3671981
theorem B2448017 : Blo 1630514 2448017 := bstep (se 2 (by rfl) ⟨918006, by rfl⟩ : syracuseStep 2448017 = 1836013) B1836013
theorem B4127395 : Blo 1630514 4127395 := bstep (se 1 (by rfl) ⟨3095546, by rfl⟩ : syracuseStep 4127395 = 6191093) B6191093
theorem B2448035 : Blo 1630514 2448035 := bstep (se 1 (by rfl) ⟨1836026, by rfl⟩ : syracuseStep 2448035 = 3672053) B3672053
theorem B7068323 : Blo 1630514 7068323 := bstep (se 1 (by rfl) ⟨5301242, by rfl⟩ : syracuseStep 7068323 = 10602485) B10602485
theorem B2448065 : Blo 1630514 2448065 := bstep (se 2 (by rfl) ⟨918024, by rfl⟩ : syracuseStep 2448065 = 1836049) B1836049
theorem B9550541 : Blo 1630514 9550541 := bstep (se 3 (by rfl) ⟨1790726, by rfl⟩ : syracuseStep 9550541 = 3581453) B3581453
theorem B10459853 : Blo 1630514 10459853 := bstep (se 3 (by rfl) ⟨1961222, by rfl⟩ : syracuseStep 10459853 = 3922445) B3922445
theorem B2448083 : Blo 1630514 2448083 := bstep (se 1 (by rfl) ⟨1836062, by rfl⟩ : syracuseStep 2448083 = 3672125) B3672125
theorem B2611939 : Blo 1630514 2611939 := bstep (se 1 (by rfl) ⟨1958954, by rfl⟩ : syracuseStep 2611939 = 3917909) B3917909
theorem B2448113 : Blo 1630514 2448113 := bstep (se 2 (by rfl) ⟨918042, by rfl⟩ : syracuseStep 2448113 = 1836085) B1836085
theorem B2448131 : Blo 1630514 2448131 := bstep (se 1 (by rfl) ⟨1836098, by rfl⟩ : syracuseStep 2448131 = 3672197) B3672197
theorem B2939665 : Blo 1630514 2939665 := bstep (se 2 (by rfl) ⟨1102374, by rfl⟩ : syracuseStep 2939665 = 2204749) B2204749
theorem B2448161 : Blo 1630514 2448161 := bstep (se 2 (by rfl) ⟨918060, by rfl⟩ : syracuseStep 2448161 = 1836121) B1836121
theorem B4127537 : Blo 1630514 4127537 := bstep (se 2 (by rfl) ⟨1547826, by rfl⟩ : syracuseStep 4127537 = 3095653) B3095653
theorem B2448179 : Blo 1630514 2448179 := bstep (se 1 (by rfl) ⟨1836134, by rfl⟩ : syracuseStep 2448179 = 3672269) B3672269
theorem B2448209 : Blo 1630514 2448209 := bstep (se 2 (by rfl) ⟨918078, by rfl⟩ : syracuseStep 2448209 = 1836157) B1836157
theorem B2448227 : Blo 1630514 2448227 := bstep (se 1 (by rfl) ⟨1836170, by rfl⟩ : syracuseStep 2448227 = 3672341) B3672341
theorem B3668849 : Blo 1630514 3668849 := bstep (se 2 (by rfl) ⟨1375818, by rfl⟩ : syracuseStep 3668849 = 2751637) B2751637
theorem B2448257 : Blo 1630514 2448257 := bstep (se 2 (by rfl) ⟨918096, by rfl⟩ : syracuseStep 2448257 = 1836193) B1836193
theorem B3668867 : Blo 1630514 3668867 := bstep (se 1 (by rfl) ⟨2751650, by rfl⟩ : syracuseStep 3668867 = 5503301) B5503301
theorem B2448275 : Blo 1630514 2448275 := bstep (se 1 (by rfl) ⟨1836206, by rfl⟩ : syracuseStep 2448275 = 3672413) B3672413
theorem B6192035 : Blo 1630514 6192035 := bstep (se 1 (by rfl) ⟨4644026, by rfl⟩ : syracuseStep 6192035 = 9288053) B9288053
theorem B2448305 : Blo 1630514 2448305 := bstep (se 2 (by rfl) ⟨918114, by rfl⟩ : syracuseStep 2448305 = 1836229) B1836229
theorem B2448323 : Blo 1630514 2448323 := bstep (se 1 (by rfl) ⟨1836242, by rfl⟩ : syracuseStep 2448323 = 3672485) B3672485
theorem B5503949 : Blo 1630514 5503949 := bstep (se 3 (by rfl) ⟨1031990, by rfl⟩ : syracuseStep 5503949 = 2063981) B2063981
theorem B2448353 : Blo 1630514 2448353 := bstep (se 2 (by rfl) ⟨918132, by rfl⟩ : syracuseStep 2448353 = 1836265) B1836265
theorem B4643821 : Blo 1630514 4643821 := bstep (se 3 (by rfl) ⟨870716, by rfl⟩ : syracuseStep 4643821 = 1741433) B1741433
theorem B2448371 : Blo 1630514 2448371 := bstep (se 1 (by rfl) ⟨1836278, by rfl⟩ : syracuseStep 2448371 = 3672557) B3672557
theorem B5504003 : Blo 1630514 5504003 := bstep (se 1 (by rfl) ⟨4128002, by rfl⟩ : syracuseStep 5504003 = 8256005) B8256005
theorem B12393485 : Blo 1630514 12393485 := bstep (se 3 (by rfl) ⟨2323778, by rfl⟩ : syracuseStep 12393485 = 4647557) B4647557
theorem B2448401 : Blo 1630514 2448401 := bstep (se 2 (by rfl) ⟨918150, by rfl⟩ : syracuseStep 2448401 = 1836301) B1836301
theorem B2448419 : Blo 1630514 2448419 := bstep (se 1 (by rfl) ⟨1836314, by rfl⟩ : syracuseStep 2448419 = 3672629) B3672629
theorem B2448449 : Blo 1630514 2448449 := bstep (se 2 (by rfl) ⟨918168, by rfl⟩ : syracuseStep 2448449 = 1836337) B1836337
theorem B2448467 : Blo 1630514 2448467 := bstep (se 1 (by rfl) ⟨1836350, by rfl⟩ : syracuseStep 2448467 = 3672701) B3672701
theorem B2448497 : Blo 1630514 2448497 := bstep (se 2 (by rfl) ⟨918186, by rfl⟩ : syracuseStep 2448497 = 1836373) B1836373
theorem B2751617 : Blo 1630514 2751617 := bstep (se 2 (by rfl) ⟨1031856, by rfl⟩ : syracuseStep 2751617 = 2063713) B2063713
theorem B2448515 : Blo 1630514 2448515 := bstep (se 1 (by rfl) ⟨1836386, by rfl⟩ : syracuseStep 2448515 = 3672773) B3672773
theorem B8256653 : Blo 1630514 8256653 := bstep (se 3 (by rfl) ⟨1548122, by rfl⟩ : syracuseStep 8256653 = 3096245) B3096245
theorem B3669137 : Blo 1630514 3669137 := bstep (se 2 (by rfl) ⟨1375926, by rfl⟩ : syracuseStep 3669137 = 2751853) B2751853
theorem B2448545 : Blo 1630514 2448545 := bstep (se 2 (by rfl) ⟨918204, by rfl⟩ : syracuseStep 2448545 = 1836409) B1836409
theorem B3669155 : Blo 1630514 3669155 := bstep (se 1 (by rfl) ⟨2751866, by rfl⟩ : syracuseStep 3669155 = 5503733) B5503733
theorem B3095729 : Blo 1630514 3095729 := bstep (se 2 (by rfl) ⟨1160898, by rfl⟩ : syracuseStep 3095729 = 2321797) B2321797
theorem B2448563 : Blo 1630514 2448563 := bstep (se 1 (by rfl) ⟨1836422, by rfl⟩ : syracuseStep 2448563 = 3672845) B3672845
theorem B4644049 : Blo 1630514 4644049 := bstep (se 2 (by rfl) ⟨1741518, by rfl⟩ : syracuseStep 4644049 = 3483037) B3483037
theorem B2448593 : Blo 1630514 2448593 := bstep (se 2 (by rfl) ⟨918222, by rfl⟩ : syracuseStep 2448593 = 1836445) B1836445
theorem B2448611 : Blo 1630514 2448611 := bstep (se 1 (by rfl) ⟨1836458, by rfl⟩ : syracuseStep 2448611 = 3672917) B3672917
theorem B2751745 : Blo 1630514 2751745 := bstep (se 2 (by rfl) ⟨1031904, by rfl⟩ : syracuseStep 2751745 = 2063809) B2063809
theorem B2448641 : Blo 1630514 2448641 := bstep (se 2 (by rfl) ⟨918240, by rfl⟩ : syracuseStep 2448641 = 1836481) B1836481
theorem B6970637 : Blo 1630514 6970637 := bstep (se 3 (by rfl) ⟨1306994, by rfl⟩ : syracuseStep 6970637 = 2613989) B2613989
theorem B5504273 : Blo 1630514 5504273 := bstep (se 2 (by rfl) ⟨2064102, by rfl⟩ : syracuseStep 5504273 = 4128205) B4128205
theorem B2448659 : Blo 1630514 2448659 := bstep (se 1 (by rfl) ⟨1836494, by rfl⟩ : syracuseStep 2448659 = 3672989) B3672989
theorem B2751779 : Blo 1630514 2751779 := bstep (se 1 (by rfl) ⟨2063834, by rfl⟩ : syracuseStep 2751779 = 4127669) B4127669
theorem B2448689 : Blo 1630514 2448689 := bstep (se 2 (by rfl) ⟨918258, by rfl⟩ : syracuseStep 2448689 = 1836517) B1836517
theorem B2448707 : Blo 1630514 2448707 := bstep (se 1 (by rfl) ⟨1836530, by rfl⟩ : syracuseStep 2448707 = 3673061) B3673061
theorem B2448737 : Blo 1630514 2448737 := bstep (se 2 (by rfl) ⟨918276, by rfl⟩ : syracuseStep 2448737 = 1836553) B1836553
theorem B1834339 : Blo 1630514 1834339 := bstep (se 1 (by rfl) ⟨1375754, by rfl⟩ : syracuseStep 1834339 = 2751509) B2751509
theorem B4644209 : Blo 1630514 4644209 := bstep (se 2 (by rfl) ⟨1741578, by rfl⟩ : syracuseStep 4644209 = 3483157) B3483157
theorem B2448755 : Blo 1630514 2448755 := bstep (se 1 (by rfl) ⟨1836566, by rfl⟩ : syracuseStep 2448755 = 3673133) B3673133
theorem B2612611 : Blo 1630514 2612611 := bstep (se 1 (by rfl) ⟨1959458, by rfl⟩ : syracuseStep 2612611 = 3918917) B3918917
theorem B2751907 : Blo 1630514 2751907 := bstep (se 1 (by rfl) ⟨2063930, by rfl⟩ : syracuseStep 2751907 = 4127861) B4127861
theorem B3669425 : Blo 1630514 3669425 := bstep (se 2 (by rfl) ⟨1376034, by rfl⟩ : syracuseStep 3669425 = 2752069) B2752069
theorem B2612657 : Blo 1630514 2612657 := bstep (se 2 (by rfl) ⟨979746, by rfl⟩ : syracuseStep 2612657 = 1959493) B1959493
theorem B20905397 : Blo 1630514 20905397 := bstep (se 5 (by rfl) ⟨979940, by rfl⟩ : syracuseStep 20905397 = 1959881) B1959881
theorem B3669443 : Blo 1630514 3669443 := bstep (se 1 (by rfl) ⟨2752082, by rfl⟩ : syracuseStep 3669443 = 5504165) B5504165
theorem B4644323 : Blo 1630514 4644323 := bstep (se 1 (by rfl) ⟨3483242, by rfl⟩ : syracuseStep 4644323 = 6966485) B6966485
theorem B1834483 : Blo 1630514 1834483 := bstep (se 1 (by rfl) ⟨1375862, by rfl⟩ : syracuseStep 1834483 = 2751725) B2751725
theorem B2063875 : Blo 1630514 2063875 := bstep (se 1 (by rfl) ⟨1547906, by rfl⟩ : syracuseStep 2063875 = 3095813) B3095813
theorem B5578253 : Blo 1630514 5578253 := bstep (se 3 (by rfl) ⟨1045922, by rfl⟩ : syracuseStep 5578253 = 2091845) B2091845
theorem B10452493 : Blo 1630514 10452493 := bstep (se 3 (by rfl) ⟨1959842, by rfl⟩ : syracuseStep 10452493 = 3919685) B3919685
theorem B2752049 : Blo 1630514 2752049 := bstep (se 2 (by rfl) ⟨1032018, by rfl⟩ : syracuseStep 2752049 = 2064037) B2064037
theorem B5660209 : Blo 1630514 5660209 := bstep (se 2 (by rfl) ⟨2122578, by rfl⟩ : syracuseStep 5660209 = 4245157) B4245157
theorem B2063971 : Blo 1630514 2063971 := bstep (se 1 (by rfl) ⟨1547978, by rfl⟩ : syracuseStep 2063971 = 3095957) B3095957
theorem B1834627 : Blo 1630514 1834627 := bstep (se 1 (by rfl) ⟨1375970, by rfl⟩ : syracuseStep 1834627 = 2751941) B2751941
theorem B2752177 : Blo 1630514 2752177 := bstep (se 2 (by rfl) ⟨1032066, by rfl⟩ : syracuseStep 2752177 = 2064133) B2064133
theorem B3669713 : Blo 1630514 3669713 := bstep (se 2 (by rfl) ⟨1376142, by rfl⟩ : syracuseStep 3669713 = 2752285) B2752285
theorem B2752211 : Blo 1630514 2752211 := bstep (se 1 (by rfl) ⟨2064158, by rfl⟩ : syracuseStep 2752211 = 4128317) B4128317
theorem B3669731 : Blo 1630514 3669731 := bstep (se 1 (by rfl) ⟨2752298, by rfl⟩ : syracuseStep 3669731 = 5504597) B5504597
theorem B4128529 : Blo 1630514 4128529 := bstep (se 2 (by rfl) ⟨1548198, by rfl⟩ : syracuseStep 4128529 = 3096397) B3096397
theorem B1834771 : Blo 1630514 1834771 := bstep (se 1 (by rfl) ⟨1376078, by rfl⟩ : syracuseStep 1834771 = 2752157) B2752157
theorem B5504813 : Blo 1630514 5504813 := bstep (se 3 (by rfl) ⟨1032152, by rfl⟩ : syracuseStep 5504813 = 2064305) B2064305
theorem B2981681 : Blo 1630514 2981681 := bstep (se 2 (by rfl) ⟨1118130, by rfl⟩ : syracuseStep 2981681 = 2236261) B2236261
theorem B26828597 : Blo 1630514 26828597 := bstep (se 5 (by rfl) ⟨1257590, by rfl⟩ : syracuseStep 26828597 = 2515181) B2515181
theorem B2752339 : Blo 1630514 2752339 := bstep (se 1 (by rfl) ⟨2064254, by rfl⟩ : syracuseStep 2752339 = 4128509) B4128509
theorem B5504867 : Blo 1630514 5504867 := bstep (se 1 (by rfl) ⟨4128650, by rfl⟩ : syracuseStep 5504867 = 8257301) B8257301
theorem B6193037 : Blo 1630514 6193037 := bstep (se 3 (by rfl) ⟨1161194, by rfl⟩ : syracuseStep 6193037 = 2322389) B2322389
theorem B1834915 : Blo 1630514 1834915 := bstep (se 1 (by rfl) ⟨1376186, by rfl⟩ : syracuseStep 1834915 = 2752373) B2752373
theorem B2613169 : Blo 1630514 2613169 := bstep (se 2 (by rfl) ⟨979938, by rfl⟩ : syracuseStep 2613169 = 1959877) B1959877
theorem B2752481 : Blo 1630514 2752481 := bstep (se 2 (by rfl) ⟨1032180, by rfl⟩ : syracuseStep 2752481 = 2064361) B2064361
theorem B3670001 : Blo 1630514 3670001 := bstep (se 2 (by rfl) ⟨1376250, by rfl⟩ : syracuseStep 3670001 = 2752501) B2752501
theorem B3719179 : Blo 1630514 3719179 := bstep (se 1 (by rfl) ⟨2789384, by rfl⟩ : syracuseStep 3719179 = 5578769) B5578769
theorem B2752535 : Blo 1630514 2752535 := bstep (se 1 (by rfl) ⟨2064401, by rfl⟩ : syracuseStep 2752535 = 4128803) B4128803
theorem B7258157 : Blo 1630514 7258157 := bstep (se 3 (by rfl) ⟨1360904, by rfl⟩ : syracuseStep 7258157 = 2721809) B2721809
theorem B4128833 : Blo 1630514 4128833 := bstep (se 2 (by rfl) ⟨1548312, by rfl⟩ : syracuseStep 4128833 = 3096625) B3096625
theorem B3670091 : Blo 1630514 3670091 := bstep (se 1 (by rfl) ⟨2752568, by rfl⟩ : syracuseStep 3670091 = 5505137) B5505137
theorem B2613323 : Blo 1630514 2613323 := bstep (se 1 (by rfl) ⟨1959992, by rfl⟩ : syracuseStep 2613323 = 3919985) B3919985
theorem B1835095 : Blo 1630514 1835095 := bstep (se 1 (by rfl) ⟨1376321, by rfl⟩ : syracuseStep 1835095 = 2752643) B2752643
theorem B9289829 : Blo 1630514 9289829 := bstep (se 4 (by rfl) ⟨870921, by rfl⟩ : syracuseStep 9289829 = 1741843) B1741843
theorem B3670145 : Blo 1630514 3670145 := bstep (se 2 (by rfl) ⟨1376304, by rfl⟩ : syracuseStep 3670145 = 2752609) B2752609
theorem B2064523 : Blo 1630514 2064523 := bstep (se 1 (by rfl) ⟨1548392, by rfl⟩ : syracuseStep 2064523 = 3096785) B3096785
theorem B2752663 : Blo 1630514 2752663 := bstep (se 1 (by rfl) ⟨2064497, by rfl⟩ : syracuseStep 2752663 = 4128995) B4128995
theorem B6971609 : Blo 1630514 6971609 := bstep (se 2 (by rfl) ⟨2614353, by rfl⟩ : syracuseStep 6971609 = 5228707) B5228707
theorem B5505245 : Blo 1630514 5505245 := bstep (se 3 (by rfl) ⟨1032233, by rfl⟩ : syracuseStep 5505245 = 2064467) B2064467
theorem B35275013 : Blo 1630514 35275013 := bstep (se 4 (by rfl) ⟨3307032, by rfl⟩ : syracuseStep 35275013 = 6614065) B6614065
theorem B1835275 : Blo 1630514 1835275 := bstep (se 1 (by rfl) ⟨1376456, by rfl⟩ : syracuseStep 1835275 = 2752913) B2752913
theorem B3096883 : Blo 1630514 3096883 := bstep (se 1 (by rfl) ⟨2322662, by rfl⟩ : syracuseStep 3096883 = 4645325) B4645325
theorem B1630519 : Blo 1630514 1630519 := bstep (se 1 (by rfl) ⟨1222889, by rfl⟩ : syracuseStep 1630519 = 2445779) B2445779
theorem B10453313 : Blo 1630514 10453313 := bstep (se 2 (by rfl) ⟨3919992, by rfl⟩ : syracuseStep 10453313 = 7839985) B7839985
theorem B1630539 : Blo 1630514 1630539 := bstep (se 1 (by rfl) ⟨1222904, by rfl⟩ : syracuseStep 1630539 = 2445809) B2445809
theorem B1630551 : Blo 1630514 1630551 := bstep (se 1 (by rfl) ⟨1222913, by rfl⟩ : syracuseStep 1630551 = 2445827) B2445827
theorem B3670361 : Blo 1630514 3670361 := bstep (se 2 (by rfl) ⟨1376385, by rfl⟩ : syracuseStep 3670361 = 2752771) B2752771
theorem B1630571 : Blo 1630514 1630571 := bstep (se 1 (by rfl) ⟨1222928, by rfl⟩ : syracuseStep 1630571 = 2445857) B2445857
theorem B1630583 : Blo 1630514 1630583 := bstep (se 1 (by rfl) ⟨1222937, by rfl⟩ : syracuseStep 1630583 = 2445875) B2445875
theorem B1835383 : Blo 1630514 1835383 := bstep (se 1 (by rfl) ⟨1376537, by rfl⟩ : syracuseStep 1835383 = 2753075) B2753075
theorem B1630603 : Blo 1630514 1630603 := bstep (se 1 (by rfl) ⟨1222952, by rfl⟩ : syracuseStep 1630603 = 2445905) B2445905
theorem B1630615 : Blo 1630514 1630615 := bstep (se 1 (by rfl) ⟨1222961, by rfl⟩ : syracuseStep 1630615 = 2445923) B2445923
theorem B2064791 : Blo 1630514 2064791 := bstep (se 1 (by rfl) ⟨1548593, by rfl⟩ : syracuseStep 2064791 = 3097187) B3097187
theorem B1630635 : Blo 1630514 1630635 := bstep (se 1 (by rfl) ⟨1222976, by rfl⟩ : syracuseStep 1630635 = 2445953) B2445953
theorem B3670451 : Blo 1630514 3670451 := bstep (se 1 (by rfl) ⟨2752838, by rfl⟩ : syracuseStep 3670451 = 5505677) B5505677
theorem B1630647 : Blo 1630514 1630647 := bstep (se 1 (by rfl) ⟨1222985, by rfl⟩ : syracuseStep 1630647 = 2445971) B2445971
theorem B1630667 : Blo 1630514 1630667 := bstep (se 1 (by rfl) ⟨1223000, by rfl⟩ : syracuseStep 1630667 = 2446001) B2446001
theorem B1630679 : Blo 1630514 1630679 := bstep (se 1 (by rfl) ⟨1223009, by rfl⟩ : syracuseStep 1630679 = 2446019) B2446019
theorem B3670487 : Blo 1630514 3670487 := bstep (se 1 (by rfl) ⟨2752865, by rfl⟩ : syracuseStep 3670487 = 5505731) B5505731
theorem B1630699 : Blo 1630514 1630699 := bstep (se 1 (by rfl) ⟨1223024, by rfl⟩ : syracuseStep 1630699 = 2446049) B2446049
theorem B1630711 : Blo 1630514 1630711 := bstep (se 1 (by rfl) ⟨1223033, by rfl⟩ : syracuseStep 1630711 = 2446067) B2446067
theorem B1630731 : Blo 1630514 1630731 := bstep (se 1 (by rfl) ⟨1223048, by rfl⟩ : syracuseStep 1630731 = 2446097) B2446097
theorem B1630743 : Blo 1630514 1630743 := bstep (se 1 (by rfl) ⟨1223057, by rfl⟩ : syracuseStep 1630743 = 2446115) B2446115
theorem B3097111 : Blo 1630514 3097111 := bstep (se 1 (by rfl) ⟨2322833, by rfl⟩ : syracuseStep 3097111 = 4645667) B4645667
theorem B1630763 : Blo 1630514 1630763 := bstep (se 1 (by rfl) ⟨1223072, by rfl⟩ : syracuseStep 1630763 = 2446145) B2446145
theorem B1835563 : Blo 1630514 1835563 := bstep (se 1 (by rfl) ⟨1376672, by rfl⟩ : syracuseStep 1835563 = 2753345) B2753345
theorem B9290285 : Blo 1630514 9290285 := bstep (se 3 (by rfl) ⟨1741928, by rfl⟩ : syracuseStep 9290285 = 3483857) B3483857
theorem B1630775 : Blo 1630514 1630775 := bstep (se 1 (by rfl) ⟨1223081, by rfl⟩ : syracuseStep 1630775 = 2446163) B2446163
theorem B1630795 : Blo 1630514 1630795 := bstep (se 1 (by rfl) ⟨1223096, by rfl⟩ : syracuseStep 1630795 = 2446193) B2446193
theorem B4645451 : Blo 1630514 4645451 := bstep (se 1 (by rfl) ⟨3484088, by rfl⟩ : syracuseStep 4645451 = 6968177) B6968177
theorem B1630807 : Blo 1630514 1630807 := bstep (se 1 (by rfl) ⟨1223105, by rfl⟩ : syracuseStep 1630807 = 2446211) B2446211
theorem B1630827 : Blo 1630514 1630827 := bstep (se 1 (by rfl) ⟨1223120, by rfl⟩ : syracuseStep 1630827 = 2446241) B2446241
theorem B1630839 : Blo 1630514 1630839 := bstep (se 1 (by rfl) ⟨1223129, by rfl⟩ : syracuseStep 1630839 = 2446259) B2446259
theorem B3097217 : Blo 1630514 3097217 := bstep (se 2 (by rfl) ⟨1161456, by rfl⟩ : syracuseStep 3097217 = 2322913) B2322913
theorem B47055491 : Blo 1630514 47055491 := bstep (se 1 (by rfl) ⟨35291618, by rfl⟩ : syracuseStep 47055491 = 70583237) B70583237
theorem B1630859 : Blo 1630514 1630859 := bstep (se 1 (by rfl) ⟨1223144, by rfl⟩ : syracuseStep 1630859 = 2446289) B2446289
theorem B3670667 : Blo 1630514 3670667 := bstep (se 1 (by rfl) ⟨2753000, by rfl⟩ : syracuseStep 3670667 = 5506001) B5506001
theorem B1630871 : Blo 1630514 1630871 := bstep (se 1 (by rfl) ⟨1223153, by rfl⟩ : syracuseStep 1630871 = 2446307) B2446307
theorem B1835671 : Blo 1630514 1835671 := bstep (se 1 (by rfl) ⟨1376753, by rfl⟩ : syracuseStep 1835671 = 2753507) B2753507
theorem B1630891 : Blo 1630514 1630891 := bstep (se 1 (by rfl) ⟨1223168, by rfl⟩ : syracuseStep 1630891 = 2446337) B2446337
theorem B1630903 : Blo 1630514 1630903 := bstep (se 1 (by rfl) ⟨1223177, by rfl⟩ : syracuseStep 1630903 = 2446355) B2446355
theorem B3670721 : Blo 1630514 3670721 := bstep (se 2 (by rfl) ⟨1376520, by rfl⟩ : syracuseStep 3670721 = 2753041) B2753041
theorem B1630923 : Blo 1630514 1630923 := bstep (se 1 (by rfl) ⟨1223192, by rfl⟩ : syracuseStep 1630923 = 2446385) B2446385
theorem B1630935 : Blo 1630514 1630935 := bstep (se 1 (by rfl) ⟨1223201, by rfl⟩ : syracuseStep 1630935 = 2446403) B2446403
theorem B1630955 : Blo 1630514 1630955 := bstep (se 1 (by rfl) ⟨1223216, by rfl⟩ : syracuseStep 1630955 = 2446433) B2446433
theorem B1630967 : Blo 1630514 1630967 := bstep (se 1 (by rfl) ⟨1223225, by rfl⟩ : syracuseStep 1630967 = 2446451) B2446451
theorem B1630987 : Blo 1630514 1630987 := bstep (se 1 (by rfl) ⟨1223240, by rfl⟩ : syracuseStep 1630987 = 2446481) B2446481
theorem B2753291 : Blo 1630514 2753291 := bstep (se 1 (by rfl) ⟨2064968, by rfl⟩ : syracuseStep 2753291 = 4129937) B4129937
theorem B1630999 : Blo 1630514 1630999 := bstep (se 1 (by rfl) ⟨1223249, by rfl⟩ : syracuseStep 1630999 = 2446499) B2446499
theorem B3097369 : Blo 1630514 3097369 := bstep (se 2 (by rfl) ⟨1161513, by rfl⟩ : syracuseStep 3097369 = 2323027) B2323027
theorem B1631019 : Blo 1630514 1631019 := bstep (se 1 (by rfl) ⟨1223264, by rfl⟩ : syracuseStep 1631019 = 2446529) B2446529
theorem B1631031 : Blo 1630514 1631031 := bstep (se 1 (by rfl) ⟨1223273, by rfl⟩ : syracuseStep 1631031 = 2446547) B2446547
theorem B3720001 : Blo 1630514 3720001 := bstep (se 2 (by rfl) ⟨1395000, by rfl⟩ : syracuseStep 3720001 = 2790001) B2790001
theorem B1631051 : Blo 1630514 1631051 := bstep (se 1 (by rfl) ⟨1223288, by rfl⟩ : syracuseStep 1631051 = 2446577) B2446577
theorem B1835851 : Blo 1630514 1835851 := bstep (se 1 (by rfl) ⟨1376888, by rfl⟩ : syracuseStep 1835851 = 2753777) B2753777
theorem B1631063 : Blo 1630514 1631063 := bstep (se 1 (by rfl) ⟨1223297, by rfl⟩ : syracuseStep 1631063 = 2446595) B2446595
theorem B6194009 : Blo 1630514 6194009 := bstep (se 2 (by rfl) ⟨2322753, by rfl⟩ : syracuseStep 6194009 = 4645507) B4645507
theorem B1631083 : Blo 1630514 1631083 := bstep (se 1 (by rfl) ⟨1223312, by rfl⟩ : syracuseStep 1631083 = 2446625) B2446625
theorem B1631095 : Blo 1630514 1631095 := bstep (se 1 (by rfl) ⟨1223321, by rfl⟩ : syracuseStep 1631095 = 2446643) B2446643
theorem B8258435 : Blo 1630514 8258435 := bstep (se 1 (by rfl) ⟨6193826, by rfl⟩ : syracuseStep 8258435 = 12387653) B12387653
theorem B1631115 : Blo 1630514 1631115 := bstep (se 1 (by rfl) ⟨1223336, by rfl⟩ : syracuseStep 1631115 = 2446673) B2446673
theorem B2753419 : Blo 1630514 2753419 := bstep (se 1 (by rfl) ⟨2065064, by rfl⟩ : syracuseStep 2753419 = 4130129) B4130129
theorem B1631127 : Blo 1630514 1631127 := bstep (se 1 (by rfl) ⟨1223345, by rfl⟩ : syracuseStep 1631127 = 2446691) B2446691
theorem B3670937 : Blo 1630514 3670937 := bstep (se 2 (by rfl) ⟨1376601, by rfl⟩ : syracuseStep 3670937 = 2753203) B2753203
theorem B1631147 : Blo 1630514 1631147 := bstep (se 1 (by rfl) ⟨1223360, by rfl⟩ : syracuseStep 1631147 = 2446721) B2446721
theorem B1631159 : Blo 1630514 1631159 := bstep (se 1 (by rfl) ⟨1223369, by rfl⟩ : syracuseStep 1631159 = 2446739) B2446739
theorem B1835959 : Blo 1630514 1835959 := bstep (se 1 (by rfl) ⟨1376969, by rfl⟩ : syracuseStep 1835959 = 2753939) B2753939
theorem B1631179 : Blo 1630514 1631179 := bstep (se 1 (by rfl) ⟨1223384, by rfl⟩ : syracuseStep 1631179 = 2446769) B2446769
theorem B1631191 : Blo 1630514 1631191 := bstep (se 1 (by rfl) ⟨1223393, by rfl⟩ : syracuseStep 1631191 = 2446787) B2446787
theorem B3482585 : Blo 1630514 3482585 := bstep (se 2 (by rfl) ⟨1305969, by rfl⟩ : syracuseStep 3482585 = 2611939) B2611939
theorem B4645849 : Blo 1630514 4645849 := bstep (se 2 (by rfl) ⟨1742193, by rfl⟩ : syracuseStep 4645849 = 3484387) B3484387
theorem B1631211 : Blo 1630514 1631211 := bstep (se 1 (by rfl) ⟨1223408, by rfl⟩ : syracuseStep 1631211 = 2446817) B2446817
theorem B3671027 : Blo 1630514 3671027 := bstep (se 1 (by rfl) ⟨2753270, by rfl⟩ : syracuseStep 3671027 = 5506541) B5506541
theorem B1631223 : Blo 1630514 1631223 := bstep (se 1 (by rfl) ⟨1223417, by rfl⟩ : syracuseStep 1631223 = 2446835) B2446835
theorem B1631243 : Blo 1630514 1631243 := bstep (se 1 (by rfl) ⟨1223432, by rfl⟩ : syracuseStep 1631243 = 2446865) B2446865
theorem B1631255 : Blo 1630514 1631255 := bstep (se 1 (by rfl) ⟨1223441, by rfl⟩ : syracuseStep 1631255 = 2446883) B2446883
theorem B3671063 : Blo 1630514 3671063 := bstep (se 1 (by rfl) ⟨2753297, by rfl⟩ : syracuseStep 3671063 = 5506595) B5506595
theorem B2753561 : Blo 1630514 2753561 := bstep (se 2 (by rfl) ⟨1032585, by rfl⟩ : syracuseStep 2753561 = 2065171) B2065171
theorem B2614297 : Blo 1630514 2614297 := bstep (se 2 (by rfl) ⟨980361, by rfl⟩ : syracuseStep 2614297 = 1960723) B1960723
theorem B32228387 : Blo 1630514 32228387 := bstep (se 1 (by rfl) ⟨24171290, by rfl⟩ : syracuseStep 32228387 = 48342581) B48342581
theorem B1631275 : Blo 1630514 1631275 := bstep (se 1 (by rfl) ⟨1223456, by rfl⟩ : syracuseStep 1631275 = 2446913) B2446913
theorem B8815661 : Blo 1630514 8815661 := bstep (se 3 (by rfl) ⟨1652936, by rfl⟩ : syracuseStep 8815661 = 3305873) B3305873
theorem B1631287 : Blo 1630514 1631287 := bstep (se 1 (by rfl) ⟨1223465, by rfl⟩ : syracuseStep 1631287 = 2446931) B2446931
theorem B1631307 : Blo 1630514 1631307 := bstep (se 1 (by rfl) ⟨1223480, by rfl⟩ : syracuseStep 1631307 = 2446961) B2446961
theorem B1631319 : Blo 1630514 1631319 := bstep (se 1 (by rfl) ⟨1223489, by rfl⟩ : syracuseStep 1631319 = 2446979) B2446979
theorem B2065495 : Blo 1630514 2065495 := bstep (se 1 (by rfl) ⟨1549121, by rfl⟩ : syracuseStep 2065495 = 3098243) B3098243
theorem B1631339 : Blo 1630514 1631339 := bstep (se 1 (by rfl) ⟨1223504, by rfl⟩ : syracuseStep 1631339 = 2447009) B2447009
theorem B1836139 : Blo 1630514 1836139 := bstep (se 1 (by rfl) ⟨1377104, by rfl⟩ : syracuseStep 1836139 = 2754209) B2754209
theorem B1631351 : Blo 1630514 1631351 := bstep (se 1 (by rfl) ⟨1223513, by rfl⟩ : syracuseStep 1631351 = 2447027) B2447027
theorem B1631371 : Blo 1630514 1631371 := bstep (se 1 (by rfl) ⟨1223528, by rfl⟩ : syracuseStep 1631371 = 2447057) B2447057
theorem B1631383 : Blo 1630514 1631383 := bstep (se 1 (by rfl) ⟨1223537, by rfl⟩ : syracuseStep 1631383 = 2447075) B2447075
theorem B2753689 : Blo 1630514 2753689 := bstep (se 2 (by rfl) ⟨1032633, by rfl⟩ : syracuseStep 2753689 = 2065267) B2065267
theorem B1631403 : Blo 1630514 1631403 := bstep (se 1 (by rfl) ⟨1223552, by rfl⟩ : syracuseStep 1631403 = 2447105) B2447105
theorem B1631415 : Blo 1630514 1631415 := bstep (se 1 (by rfl) ⟨1223561, by rfl⟩ : syracuseStep 1631415 = 2447123) B2447123
theorem B1631435 : Blo 1630514 1631435 := bstep (se 1 (by rfl) ⟨1223576, by rfl⟩ : syracuseStep 1631435 = 2447153) B2447153
theorem B3671243 : Blo 1630514 3671243 := bstep (se 1 (by rfl) ⟨2753432, by rfl⟩ : syracuseStep 3671243 = 5506865) B5506865
theorem B1631447 : Blo 1630514 1631447 := bstep (se 1 (by rfl) ⟨1223585, by rfl⟩ : syracuseStep 1631447 = 2447171) B2447171
theorem B1836247 : Blo 1630514 1836247 := bstep (se 1 (by rfl) ⟨1377185, by rfl⟩ : syracuseStep 1836247 = 2754371) B2754371
theorem B9290969 : Blo 1630514 9290969 := bstep (se 2 (by rfl) ⟨3484113, by rfl⟩ : syracuseStep 9290969 = 6968227) B6968227
theorem B1631467 : Blo 1630514 1631467 := bstep (se 1 (by rfl) ⟨1223600, by rfl⟩ : syracuseStep 1631467 = 2447201) B2447201
theorem B1631479 : Blo 1630514 1631479 := bstep (se 1 (by rfl) ⟨1223609, by rfl⟩ : syracuseStep 1631479 = 2447219) B2447219
theorem B3671297 : Blo 1630514 3671297 := bstep (se 2 (by rfl) ⟨1376736, by rfl⟩ : syracuseStep 3671297 = 2753473) B2753473
theorem B1631499 : Blo 1630514 1631499 := bstep (se 1 (by rfl) ⟨1223624, by rfl⟩ : syracuseStep 1631499 = 2447249) B2447249
theorem B1631511 : Blo 1630514 1631511 := bstep (se 1 (by rfl) ⟨1223633, by rfl⟩ : syracuseStep 1631511 = 2447267) B2447267
theorem B1631531 : Blo 1630514 1631531 := bstep (se 1 (by rfl) ⟨1223648, by rfl⟩ : syracuseStep 1631531 = 2447297) B2447297
theorem B4130099 : Blo 1630514 4130099 := bstep (se 1 (by rfl) ⟨3097574, by rfl⟩ : syracuseStep 4130099 = 6195149) B6195149
theorem B1631543 : Blo 1630514 1631543 := bstep (se 1 (by rfl) ⟨1223657, by rfl⟩ : syracuseStep 1631543 = 2447315) B2447315
theorem B5506379 : Blo 1630514 5506379 := bstep (se 1 (by rfl) ⟨4129784, by rfl⟩ : syracuseStep 5506379 = 8259569) B8259569
theorem B1631563 : Blo 1630514 1631563 := bstep (se 1 (by rfl) ⟨1223672, by rfl⟩ : syracuseStep 1631563 = 2447345) B2447345
theorem B1631575 : Blo 1630514 1631575 := bstep (se 1 (by rfl) ⟨1223681, by rfl⟩ : syracuseStep 1631575 = 2447363) B2447363
theorem B1631595 : Blo 1630514 1631595 := bstep (se 1 (by rfl) ⟨1223696, by rfl⟩ : syracuseStep 1631595 = 2447393) B2447393
theorem B3482995 : Blo 1630514 3482995 := bstep (se 1 (by rfl) ⟨2612246, by rfl⟩ : syracuseStep 3482995 = 5224493) B5224493
theorem B1631607 : Blo 1630514 1631607 := bstep (se 1 (by rfl) ⟨1223705, by rfl⟩ : syracuseStep 1631607 = 2447411) B2447411
theorem B1631627 : Blo 1630514 1631627 := bstep (se 1 (by rfl) ⟨1223720, by rfl⟩ : syracuseStep 1631627 = 2447441) B2447441
theorem B1836427 : Blo 1630514 1836427 := bstep (se 1 (by rfl) ⟨1377320, by rfl⟩ : syracuseStep 1836427 = 2754641) B2754641
theorem B1631639 : Blo 1630514 1631639 := bstep (se 1 (by rfl) ⟨1223729, by rfl⟩ : syracuseStep 1631639 = 2447459) B2447459
theorem B1631659 : Blo 1630514 1631659 := bstep (se 1 (by rfl) ⟨1223744, by rfl⟩ : syracuseStep 1631659 = 2447489) B2447489
theorem B1631671 : Blo 1630514 1631671 := bstep (se 1 (by rfl) ⟨1223753, by rfl⟩ : syracuseStep 1631671 = 2447507) B2447507
theorem B1631691 : Blo 1630514 1631691 := bstep (se 1 (by rfl) ⟨1223768, by rfl⟩ : syracuseStep 1631691 = 2447537) B2447537
theorem B6972875 : Blo 1630514 6972875 := bstep (se 1 (by rfl) ⟨5229656, by rfl⟩ : syracuseStep 6972875 = 10459313) B10459313
theorem B1631703 : Blo 1630514 1631703 := bstep (se 1 (by rfl) ⟨1223777, by rfl⟩ : syracuseStep 1631703 = 2447555) B2447555
theorem B3671513 : Blo 1630514 3671513 := bstep (se 2 (by rfl) ⟨1376817, by rfl⟩ : syracuseStep 3671513 = 2753635) B2753635
theorem B1631723 : Blo 1630514 1631723 := bstep (se 1 (by rfl) ⟨1223792, by rfl⟩ : syracuseStep 1631723 = 2447585) B2447585
theorem B1631735 : Blo 1630514 1631735 := bstep (se 1 (by rfl) ⟨1223801, by rfl⟩ : syracuseStep 1631735 = 2447603) B2447603
theorem B1836535 : Blo 1630514 1836535 := bstep (se 1 (by rfl) ⟨1377401, by rfl⟩ : syracuseStep 1836535 = 2754803) B2754803
theorem B1631755 : Blo 1630514 1631755 := bstep (se 1 (by rfl) ⟨1223816, by rfl⟩ : syracuseStep 1631755 = 2447633) B2447633
theorem B1631767 : Blo 1630514 1631767 := bstep (se 1 (by rfl) ⟨1223825, by rfl⟩ : syracuseStep 1631767 = 2447651) B2447651
theorem B1631787 : Blo 1630514 1631787 := bstep (se 1 (by rfl) ⟨1223840, by rfl⟩ : syracuseStep 1631787 = 2447681) B2447681
theorem B3671603 : Blo 1630514 3671603 := bstep (se 1 (by rfl) ⟨2753702, by rfl⟩ : syracuseStep 3671603 = 5507405) B5507405
theorem B1631799 : Blo 1630514 1631799 := bstep (se 1 (by rfl) ⟨1223849, by rfl⟩ : syracuseStep 1631799 = 2447699) B2447699
theorem B6964811 : Blo 1630514 6964811 := bstep (se 1 (by rfl) ⟨5223608, by rfl⟩ : syracuseStep 6964811 = 10447217) B10447217
theorem B1631819 : Blo 1630514 1631819 := bstep (se 1 (by rfl) ⟨1223864, by rfl⟩ : syracuseStep 1631819 = 2447729) B2447729
theorem B1631831 : Blo 1630514 1631831 := bstep (se 1 (by rfl) ⟨1223873, by rfl⟩ : syracuseStep 1631831 = 2447747) B2447747
theorem B3671639 : Blo 1630514 3671639 := bstep (se 1 (by rfl) ⟨2753729, by rfl⟩ : syracuseStep 3671639 = 5507459) B5507459
theorem B5506649 : Blo 1630514 5506649 := bstep (se 2 (by rfl) ⟨2064993, by rfl⟩ : syracuseStep 5506649 = 4129987) B4129987
theorem B1631851 : Blo 1630514 1631851 := bstep (se 1 (by rfl) ⟨1223888, by rfl⟩ : syracuseStep 1631851 = 2447777) B2447777
theorem B1631863 : Blo 1630514 1631863 := bstep (se 1 (by rfl) ⟨1223897, by rfl⟩ : syracuseStep 1631863 = 2447795) B2447795
theorem B1631883 : Blo 1630514 1631883 := bstep (se 1 (by rfl) ⟨1223912, by rfl⟩ : syracuseStep 1631883 = 2447825) B2447825
theorem B1631895 : Blo 1630514 1631895 := bstep (se 1 (by rfl) ⟨1223921, by rfl⟩ : syracuseStep 1631895 = 2447843) B2447843
theorem B1631915 : Blo 1630514 1631915 := bstep (se 1 (by rfl) ⟨1223936, by rfl⟩ : syracuseStep 1631915 = 2447873) B2447873
theorem B6612653 : Blo 1630514 6612653 := bstep (se 3 (by rfl) ⟨1239872, by rfl⟩ : syracuseStep 6612653 = 2479745) B2479745
theorem B13231795 : Blo 1630514 13231795 := bstep (se 1 (by rfl) ⟨9923846, by rfl⟩ : syracuseStep 13231795 = 19847693) B19847693
theorem B1631927 : Blo 1630514 1631927 := bstep (se 1 (by rfl) ⟨1223945, by rfl⟩ : syracuseStep 1631927 = 2447891) B2447891
theorem B1631947 : Blo 1630514 1631947 := bstep (se 1 (by rfl) ⟨1223960, by rfl⟩ : syracuseStep 1631947 = 2447921) B2447921
theorem B34866893 : Blo 1630514 34866893 := bstep (se 3 (by rfl) ⟨6537542, by rfl⟩ : syracuseStep 34866893 = 13075085) B13075085
theorem B1631959 : Blo 1630514 1631959 := bstep (se 1 (by rfl) ⟨1223969, by rfl⟩ : syracuseStep 1631959 = 2447939) B2447939
theorem B2754263 : Blo 1630514 2754263 := bstep (se 1 (by rfl) ⟨2065697, by rfl⟩ : syracuseStep 2754263 = 4131395) B4131395
theorem B1631979 : Blo 1630514 1631979 := bstep (se 1 (by rfl) ⟨1223984, by rfl⟩ : syracuseStep 1631979 = 2447969) B2447969
theorem B1631991 : Blo 1630514 1631991 := bstep (se 1 (by rfl) ⟨1223993, by rfl⟩ : syracuseStep 1631991 = 2447987) B2447987
theorem B3671819 : Blo 1630514 3671819 := bstep (se 1 (by rfl) ⟨2753864, by rfl⟩ : syracuseStep 3671819 = 5507729) B5507729
theorem B1632011 : Blo 1630514 1632011 := bstep (se 1 (by rfl) ⟨1224008, by rfl⟩ : syracuseStep 1632011 = 2448017) B2448017
theorem B1632023 : Blo 1630514 1632023 := bstep (se 1 (by rfl) ⟨1224017, by rfl⟩ : syracuseStep 1632023 = 2448035) B2448035
theorem B4712215 : Blo 1630514 4712215 := bstep (se 1 (by rfl) ⟨3534161, by rfl⟩ : syracuseStep 4712215 = 7068323) B7068323
theorem B1632043 : Blo 1630514 1632043 := bstep (se 1 (by rfl) ⟨1224032, by rfl⟩ : syracuseStep 1632043 = 2448065) B2448065
theorem B6367027 : Blo 1630514 6367027 := bstep (se 1 (by rfl) ⟨4775270, by rfl⟩ : syracuseStep 6367027 = 9550541) B9550541
theorem B6973235 : Blo 1630514 6973235 := bstep (se 1 (by rfl) ⟨5229926, by rfl⟩ : syracuseStep 6973235 = 10459853) B10459853
theorem B1632055 : Blo 1630514 1632055 := bstep (se 1 (by rfl) ⟨1224041, by rfl⟩ : syracuseStep 1632055 = 2448083) B2448083
theorem B3671873 : Blo 1630514 3671873 := bstep (se 2 (by rfl) ⟨1376952, by rfl⟩ : syracuseStep 3671873 = 2753905) B2753905
theorem B4130635 : Blo 1630514 4130635 := bstep (se 1 (by rfl) ⟨3097976, by rfl⟩ : syracuseStep 4130635 = 6195953) B6195953
theorem B1632075 : Blo 1630514 1632075 := bstep (se 1 (by rfl) ⟨1224056, by rfl⟩ : syracuseStep 1632075 = 2448113) B2448113
theorem B1632087 : Blo 1630514 1632087 := bstep (se 1 (by rfl) ⟨1224065, by rfl⟩ : syracuseStep 1632087 = 2448131) B2448131
theorem B3483481 : Blo 1630514 3483481 := bstep (se 2 (by rfl) ⟨1306305, by rfl⟩ : syracuseStep 3483481 = 2612611) B2612611
theorem B2754391 : Blo 1630514 2754391 := bstep (se 1 (by rfl) ⟨2065793, by rfl⟩ : syracuseStep 2754391 = 4131587) B4131587
theorem B1632107 : Blo 1630514 1632107 := bstep (se 1 (by rfl) ⟨1224080, by rfl⟩ : syracuseStep 1632107 = 2448161) B2448161
theorem B1632119 : Blo 1630514 1632119 := bstep (se 1 (by rfl) ⟨1224089, by rfl⟩ : syracuseStep 1632119 = 2448179) B2448179
theorem B1632139 : Blo 1630514 1632139 := bstep (se 1 (by rfl) ⟨1224104, by rfl⟩ : syracuseStep 1632139 = 2448209) B2448209
theorem B1632151 : Blo 1630514 1632151 := bstep (se 1 (by rfl) ⟨1224113, by rfl⟩ : syracuseStep 1632151 = 2448227) B2448227
theorem B1632171 : Blo 1630514 1632171 := bstep (se 1 (by rfl) ⟨1224128, by rfl⟩ : syracuseStep 1632171 = 2448257) B2448257
theorem B1632183 : Blo 1630514 1632183 := bstep (se 1 (by rfl) ⟨1224137, by rfl⟩ : syracuseStep 1632183 = 2448275) B2448275
theorem B6965185 : Blo 1630514 6965185 := bstep (se 2 (by rfl) ⟨2611944, by rfl⟩ : syracuseStep 6965185 = 5223889) B5223889
theorem B1632203 : Blo 1630514 1632203 := bstep (se 1 (by rfl) ⟨1224152, by rfl⟩ : syracuseStep 1632203 = 2448305) B2448305
theorem B1632215 : Blo 1630514 1632215 := bstep (se 1 (by rfl) ⟨1224161, by rfl⟩ : syracuseStep 1632215 = 2448323) B2448323
theorem B4130777 : Blo 1630514 4130777 := bstep (se 2 (by rfl) ⟨1549041, by rfl⟩ : syracuseStep 4130777 = 3098083) B3098083
theorem B1632235 : Blo 1630514 1632235 := bstep (se 1 (by rfl) ⟨1224176, by rfl⟩ : syracuseStep 1632235 = 2448353) B2448353
theorem B1632247 : Blo 1630514 1632247 := bstep (se 1 (by rfl) ⟨1224185, by rfl⟩ : syracuseStep 1632247 = 2448371) B2448371
theorem B1632267 : Blo 1630514 1632267 := bstep (se 1 (by rfl) ⟨1224200, by rfl⟩ : syracuseStep 1632267 = 2448401) B2448401
theorem B13936657 : Blo 1630514 13936657 := bstep (se 2 (by rfl) ⟨5226246, by rfl⟩ : syracuseStep 13936657 = 10452493) B10452493
theorem B1632279 : Blo 1630514 1632279 := bstep (se 1 (by rfl) ⟨1224209, by rfl⟩ : syracuseStep 1632279 = 2448419) B2448419
theorem B3672089 : Blo 1630514 3672089 := bstep (se 2 (by rfl) ⟨1377033, by rfl⟩ : syracuseStep 3672089 = 2754067) B2754067
theorem B1632299 : Blo 1630514 1632299 := bstep (se 1 (by rfl) ⟨1224224, by rfl⟩ : syracuseStep 1632299 = 2448449) B2448449
theorem B3098675 : Blo 1630514 3098675 := bstep (se 1 (by rfl) ⟨2324006, by rfl⟩ : syracuseStep 3098675 = 4648013) B4648013
theorem B1632311 : Blo 1630514 1632311 := bstep (se 1 (by rfl) ⟨1224233, by rfl⟩ : syracuseStep 1632311 = 2448467) B2448467
theorem B7546945 : Blo 1630514 7546945 := bstep (se 2 (by rfl) ⟨2830104, by rfl⟩ : syracuseStep 7546945 = 5660209) B5660209
theorem B35293259 : Blo 1630514 35293259 := bstep (se 1 (by rfl) ⟨26469944, by rfl⟩ : syracuseStep 35293259 = 52939889) B52939889
theorem B1632331 : Blo 1630514 1632331 := bstep (se 1 (by rfl) ⟨1224248, by rfl⟩ : syracuseStep 1632331 = 2448497) B2448497
theorem B1632343 : Blo 1630514 1632343 := bstep (se 1 (by rfl) ⟨1224257, by rfl⟩ : syracuseStep 1632343 = 2448515) B2448515
theorem B1632363 : Blo 1630514 1632363 := bstep (se 1 (by rfl) ⟨1224272, by rfl⟩ : syracuseStep 1632363 = 2448545) B2448545
theorem B3672179 : Blo 1630514 3672179 := bstep (se 1 (by rfl) ⟨2754134, by rfl⟩ : syracuseStep 3672179 = 5508269) B5508269
theorem B1632375 : Blo 1630514 1632375 := bstep (se 1 (by rfl) ⟨1224281, by rfl⟩ : syracuseStep 1632375 = 2448563) B2448563
theorem B1632395 : Blo 1630514 1632395 := bstep (se 1 (by rfl) ⟨1224296, by rfl⟩ : syracuseStep 1632395 = 2448593) B2448593
theorem B3672215 : Blo 1630514 3672215 := bstep (se 1 (by rfl) ⟨2754161, by rfl⟩ : syracuseStep 3672215 = 5508323) B5508323
theorem B1632407 : Blo 1630514 1632407 := bstep (se 1 (by rfl) ⟨1224305, by rfl⟩ : syracuseStep 1632407 = 2448611) B2448611
theorem B1632427 : Blo 1630514 1632427 := bstep (se 1 (by rfl) ⟨1224320, by rfl⟩ : syracuseStep 1632427 = 2448641) B2448641
theorem B4647091 : Blo 1630514 4647091 := bstep (se 1 (by rfl) ⟨3485318, by rfl⟩ : syracuseStep 4647091 = 6970637) B6970637
theorem B1632439 : Blo 1630514 1632439 := bstep (se 1 (by rfl) ⟨1224329, by rfl⟩ : syracuseStep 1632439 = 2448659) B2448659
theorem B3721409 : Blo 1630514 3721409 := bstep (se 2 (by rfl) ⟨1395528, by rfl⟩ : syracuseStep 3721409 = 2791057) B2791057
theorem B3098827 : Blo 1630514 3098827 := bstep (se 1 (by rfl) ⟨2324120, by rfl⟩ : syracuseStep 3098827 = 4648241) B4648241
theorem B1632459 : Blo 1630514 1632459 := bstep (se 1 (by rfl) ⟨1224344, by rfl⟩ : syracuseStep 1632459 = 2448689) B2448689
theorem B1632471 : Blo 1630514 1632471 := bstep (se 1 (by rfl) ⟨1224353, by rfl⟩ : syracuseStep 1632471 = 2448707) B2448707
theorem B1632491 : Blo 1630514 1632491 := bstep (se 1 (by rfl) ⟨1224368, by rfl⟩ : syracuseStep 1632491 = 2448737) B2448737
theorem B1632503 : Blo 1630514 1632503 := bstep (se 1 (by rfl) ⟨1224377, by rfl⟩ : syracuseStep 1632503 = 2448755) B2448755
theorem B12388625 : Blo 1630514 12388625 := bstep (se 2 (by rfl) ⟨4645734, by rfl⟩ : syracuseStep 12388625 = 9291469) B9291469
theorem B6965527 : Blo 1630514 6965527 := bstep (se 1 (by rfl) ⟨5224145, by rfl⟩ : syracuseStep 6965527 = 10448291) B10448291
theorem B5507351 : Blo 1630514 5507351 := bstep (se 1 (by rfl) ⟨4130513, by rfl⟩ : syracuseStep 5507351 = 8261027) B8261027
theorem B13936931 : Blo 1630514 13936931 := bstep (se 1 (by rfl) ⟨10452698, by rfl⟩ : syracuseStep 13936931 = 20905397) B20905397
theorem B3672395 : Blo 1630514 3672395 := bstep (se 1 (by rfl) ⟨2754296, by rfl⟩ : syracuseStep 3672395 = 5508593) B5508593
theorem B3672449 : Blo 1630514 3672449 := bstep (se 2 (by rfl) ⟨1377168, by rfl⟩ : syracuseStep 3672449 = 2754337) B2754337
theorem B38168981 : Blo 1630514 38168981 := bstep (se 6 (by rfl) ⟨894585, by rfl⟩ : syracuseStep 38168981 = 1789171) B1789171
theorem B6195635 : Blo 1630514 6195635 := bstep (se 1 (by rfl) ⟨4646726, by rfl⟩ : syracuseStep 6195635 = 9293453) B9293453
theorem B6195649 : Blo 1630514 6195649 := bstep (se 2 (by rfl) ⟨2323368, by rfl⟩ : syracuseStep 6195649 = 4646737) B4646737
theorem B3099161 : Blo 1630514 3099161 := bstep (se 2 (by rfl) ⟨1162185, by rfl⟩ : syracuseStep 3099161 = 2324371) B2324371
theorem B17885731 : Blo 1630514 17885731 := bstep (se 1 (by rfl) ⟨13414298, by rfl⟩ : syracuseStep 17885731 = 26828597) B26828597
theorem B5229107 : Blo 1630514 5229107 := bstep (se 1 (by rfl) ⟨3921830, by rfl⟩ : syracuseStep 5229107 = 7843661) B7843661
theorem B3484225 : Blo 1630514 3484225 := bstep (se 2 (by rfl) ⟨1306584, by rfl⟩ : syracuseStep 3484225 = 2613169) B2613169
theorem B3672665 : Blo 1630514 3672665 := bstep (se 2 (by rfl) ⟨1377249, by rfl⟩ : syracuseStep 3672665 = 2754499) B2754499
theorem B3140275 : Blo 1630514 3140275 := bstep (se 1 (by rfl) ⟨2355206, by rfl⟩ : syracuseStep 3140275 = 4710413) B4710413
theorem B3672755 : Blo 1630514 3672755 := bstep (se 1 (by rfl) ⟨2754566, by rfl⟩ : syracuseStep 3672755 = 5509133) B5509133
theorem B3672791 : Blo 1630514 3672791 := bstep (se 1 (by rfl) ⟨2754593, by rfl⟩ : syracuseStep 3672791 = 5509187) B5509187
theorem B4131607 : Blo 1630514 4131607 := bstep (se 1 (by rfl) ⟨3098705, by rfl⟩ : syracuseStep 4131607 = 6197411) B6197411
theorem B5581619 : Blo 1630514 5581619 := bstep (se 1 (by rfl) ⟨4186214, by rfl⟩ : syracuseStep 5581619 = 8372429) B8372429
theorem B5507891 : Blo 1630514 5507891 := bstep (se 1 (by rfl) ⟨4130918, by rfl⟩ : syracuseStep 5507891 = 8261837) B8261837
theorem B41806691 : Blo 1630514 41806691 := bstep (se 1 (by rfl) ⟨31355018, by rfl⟩ : syracuseStep 41806691 = 62710037) B62710037
theorem B3672971 : Blo 1630514 3672971 := bstep (se 1 (by rfl) ⟨2754728, by rfl⟩ : syracuseStep 3672971 = 5509457) B5509457
theorem B3673025 : Blo 1630514 3673025 := bstep (se 2 (by rfl) ⟨1377384, by rfl⟩ : syracuseStep 3673025 = 2754769) B2754769
theorem B5508161 : Blo 1630514 5508161 := bstep (se 2 (by rfl) ⟨2065560, by rfl⟩ : syracuseStep 5508161 = 4131121) B4131121
theorem B3918937 : Blo 1630514 3918937 := bstep (se 2 (by rfl) ⟨1469601, by rfl⟩ : syracuseStep 3918937 = 2939203) B2939203
theorem B9423965 : Blo 1630514 9423965 := bstep (se 3 (by rfl) ⟨1766993, by rfl⟩ : syracuseStep 9423965 = 3533987) B3533987
theorem B2354329 : Blo 1630514 2354329 := bstep (se 2 (by rfl) ⟨882873, by rfl⟩ : syracuseStep 2354329 = 1765747) B1765747
theorem B4132043 : Blo 1630514 4132043 := bstep (se 1 (by rfl) ⟨3099032, by rfl⟩ : syracuseStep 4132043 = 6198065) B6198065
theorem B26815693 : Blo 1630514 26815693 := bstep (se 3 (by rfl) ⟨5027942, by rfl⟩ : syracuseStep 26815693 = 10055885) B10055885
theorem B5229785 : Blo 1630514 5229785 := bstep (se 2 (by rfl) ⟨1961169, by rfl⟩ : syracuseStep 5229785 = 3922339) B3922339
theorem B5877137 : Blo 1630514 5877137 := bstep (se 2 (by rfl) ⟨2203926, by rfl⟩ : syracuseStep 5877137 = 4407853) B4407853
theorem B24169907 : Blo 1630514 24169907 := bstep (se 1 (by rfl) ⟨18127430, by rfl⟩ : syracuseStep 24169907 = 36254861) B36254861
theorem B15674897 : Blo 1630514 15674897 := bstep (se 2 (by rfl) ⟨5878086, by rfl⟩ : syracuseStep 15674897 = 11756173) B11756173
theorem B3485207 : Blo 1630514 3485207 := bstep (se 1 (by rfl) ⟨2613905, by rfl⟩ : syracuseStep 3485207 = 5227811) B5227811
theorem B5508701 : Blo 1630514 5508701 := bstep (se 3 (by rfl) ⟨1032881, by rfl⟩ : syracuseStep 5508701 = 2065763) B2065763
theorem B3919553 : Blo 1630514 3919553 := bstep (se 2 (by rfl) ⟨1469832, by rfl⟩ : syracuseStep 3919553 = 2939665) B2939665
theorem B4960075 : Blo 1630514 4960075 := bstep (se 1 (by rfl) ⟨3720056, by rfl⟩ : syracuseStep 4960075 = 7440113) B7440113
theorem B25472945 : Blo 1630514 25472945 := bstep (se 2 (by rfl) ⟨9552354, by rfl⟩ : syracuseStep 25472945 = 19104709) B19104709
theorem B47673305 : Blo 1630514 47673305 := bstep (se 2 (by rfl) ⟨17877489, by rfl⟩ : syracuseStep 47673305 = 35754979) B35754979
theorem B3485771 : Blo 1630514 3485771 := bstep (se 1 (by rfl) ⟨2614328, by rfl⟩ : syracuseStep 3485771 = 5228657) B5228657
theorem B1986827 : Blo 1630514 1986827 := bstep (se 1 (by rfl) ⟨1490120, by rfl⟩ : syracuseStep 1986827 = 2980241) B2980241
theorem B6197579 : Blo 1630514 6197579 := bstep (se 1 (by rfl) ⟨4648184, by rfl⟩ : syracuseStep 6197579 = 9296369) B9296369
theorem B6197593 : Blo 1630514 6197593 := bstep (se 2 (by rfl) ⟨2324097, by rfl⟩ : syracuseStep 6197593 = 4648195) B4648195
theorem B2445785 : Blo 1630514 2445785 := bstep (se 2 (by rfl) ⟨917169, by rfl⟩ : syracuseStep 2445785 = 1834339) B1834339
theorem B8262161 : Blo 1630514 8262161 := bstep (se 2 (by rfl) ⟨3098310, by rfl⟩ : syracuseStep 8262161 = 6196621) B6196621
theorem B3486233 : Blo 1630514 3486233 := bstep (se 2 (by rfl) ⟨1307337, by rfl⟩ : syracuseStep 3486233 = 2614675) B2614675
theorem B2445899 : Blo 1630514 2445899 := bstep (se 1 (by rfl) ⟨1834424, by rfl⟩ : syracuseStep 2445899 = 3668849) B3668849
theorem B2445911 : Blo 1630514 2445911 := bstep (se 1 (by rfl) ⟨1834433, by rfl⟩ : syracuseStep 2445911 = 3668867) B3668867
theorem B2445977 : Blo 1630514 2445977 := bstep (se 2 (by rfl) ⟨917241, by rfl⟩ : syracuseStep 2445977 = 1834483) B1834483
theorem B8262323 : Blo 1630514 8262323 := bstep (se 1 (by rfl) ⟨6196742, by rfl⟩ : syracuseStep 8262323 = 12393485) B12393485
theorem B2446091 : Blo 1630514 2446091 := bstep (se 1 (by rfl) ⟨1834568, by rfl⟩ : syracuseStep 2446091 = 3669137) B3669137
theorem B2446103 : Blo 1630514 2446103 := bstep (se 1 (by rfl) ⟨1834577, by rfl⟩ : syracuseStep 2446103 = 3669155) B3669155
theorem B2446169 : Blo 1630514 2446169 := bstep (se 2 (by rfl) ⟨917313, by rfl⟩ : syracuseStep 2446169 = 1834627) B1834627
theorem B2323289 : Blo 1630514 2323289 := bstep (se 2 (by rfl) ⟨871233, by rfl⟩ : syracuseStep 2323289 = 1742467) B1742467
theorem B2446283 : Blo 1630514 2446283 := bstep (se 1 (by rfl) ⟨1834712, by rfl⟩ : syracuseStep 2446283 = 3669425) B3669425
theorem B1741771 : Blo 1630514 1741771 := bstep (se 1 (by rfl) ⟨1306328, by rfl⟩ : syracuseStep 1741771 = 2612657) B2612657
theorem B2446295 : Blo 1630514 2446295 := bstep (se 1 (by rfl) ⟨1834721, by rfl⟩ : syracuseStep 2446295 = 3669443) B3669443
theorem B10449881 : Blo 1630514 10449881 := bstep (se 2 (by rfl) ⟨3918705, by rfl⟩ : syracuseStep 10449881 = 7837411) B7837411
theorem B2446361 : Blo 1630514 2446361 := bstep (se 2 (by rfl) ⟨917385, by rfl⟩ : syracuseStep 2446361 = 1834771) B1834771
theorem B2446475 : Blo 1630514 2446475 := bstep (se 1 (by rfl) ⟨1834856, by rfl⟩ : syracuseStep 2446475 = 3669713) B3669713
theorem B2446487 : Blo 1630514 2446487 := bstep (se 1 (by rfl) ⟨1834865, by rfl⟩ : syracuseStep 2446487 = 3669731) B3669731
theorem B1987787 : Blo 1630514 1987787 := bstep (se 1 (by rfl) ⟨1490840, by rfl⟩ : syracuseStep 1987787 = 2981681) B2981681
theorem B2446553 : Blo 1630514 2446553 := bstep (se 2 (by rfl) ⟨917457, by rfl⟩ : syracuseStep 2446553 = 1834915) B1834915
theorem B2446667 : Blo 1630514 2446667 := bstep (se 1 (by rfl) ⟨1835000, by rfl⟩ : syracuseStep 2446667 = 3670001) B3670001
theorem B2446679 : Blo 1630514 2446679 := bstep (se 1 (by rfl) ⟨1835009, by rfl⟩ : syracuseStep 2446679 = 3670019) B3670019
theorem B8254871 : Blo 1630514 8254871 := bstep (se 1 (by rfl) ⟨6191153, by rfl⟩ : syracuseStep 8254871 = 12382307) B12382307
theorem B2446745 : Blo 1630514 2446745 := bstep (se 2 (by rfl) ⟨917529, by rfl⟩ : syracuseStep 2446745 = 1835059) B1835059
theorem B4961729 : Blo 1630514 4961729 := bstep (se 2 (by rfl) ⟨1860648, by rfl⟩ : syracuseStep 4961729 = 3721297) B3721297
theorem B2323927 : Blo 1630514 2323927 := bstep (se 1 (by rfl) ⟨1742945, by rfl⟩ : syracuseStep 2323927 = 3485891) B3485891
theorem B1766891 : Blo 1630514 1766891 := bstep (se 1 (by rfl) ⟨1325168, by rfl⟩ : syracuseStep 1766891 = 2650337) B2650337
theorem B2446859 : Blo 1630514 2446859 := bstep (se 1 (by rfl) ⟨1835144, by rfl⟩ : syracuseStep 2446859 = 3670289) B3670289
theorem B2446871 : Blo 1630514 2446871 := bstep (se 1 (by rfl) ⟨1835153, by rfl⟩ : syracuseStep 2446871 = 3670307) B3670307
theorem B2479691 : Blo 1630514 2479691 := bstep (se 1 (by rfl) ⟨1859768, by rfl⟩ : syracuseStep 2479691 = 3719537) B3719537
theorem B2446937 : Blo 1630514 2446937 := bstep (se 2 (by rfl) ⟨917601, by rfl⟩ : syracuseStep 2446937 = 1835203) B1835203
theorem B2447051 : Blo 1630514 2447051 := bstep (se 1 (by rfl) ⟨1835288, by rfl⟩ : syracuseStep 2447051 = 3670577) B3670577
theorem B2447063 : Blo 1630514 2447063 := bstep (se 1 (by rfl) ⟨1835297, by rfl⟩ : syracuseStep 2447063 = 3670595) B3670595
theorem B2447129 : Blo 1630514 2447129 := bstep (se 2 (by rfl) ⟨917673, by rfl⟩ : syracuseStep 2447129 = 1835347) B1835347
theorem B12736291 : Blo 1630514 12736291 := bstep (se 1 (by rfl) ⟨9552218, by rfl⟩ : syracuseStep 12736291 = 19104437) B19104437
theorem B9295661 : Blo 1630514 9295661 := bstep (se 3 (by rfl) ⟨1742936, by rfl⟩ : syracuseStep 9295661 = 3485873) B3485873
theorem B17872757 : Blo 1630514 17872757 := bstep (se 5 (by rfl) ⟨837785, by rfl⟩ : syracuseStep 17872757 = 1675571) B1675571
theorem B2447243 : Blo 1630514 2447243 := bstep (se 1 (by rfl) ⟨1835432, by rfl⟩ : syracuseStep 2447243 = 3670865) B3670865
theorem B2447255 : Blo 1630514 2447255 := bstep (se 1 (by rfl) ⟨1835441, by rfl⟩ : syracuseStep 2447255 = 3670883) B3670883
theorem B2447321 : Blo 1630514 2447321 := bstep (se 2 (by rfl) ⟨917745, by rfl⟩ : syracuseStep 2447321 = 1835491) B1835491
theorem B12392513 : Blo 1630514 12392513 := bstep (se 2 (by rfl) ⟨4647192, by rfl⟩ : syracuseStep 12392513 = 9294385) B9294385
theorem B2447435 : Blo 1630514 2447435 := bstep (se 1 (by rfl) ⟨1835576, by rfl⟩ : syracuseStep 2447435 = 3671153) B3671153
theorem B2447447 : Blo 1630514 2447447 := bstep (se 1 (by rfl) ⟨1835585, by rfl⟩ : syracuseStep 2447447 = 3671171) B3671171
theorem B2447513 : Blo 1630514 2447513 := bstep (se 2 (by rfl) ⟨917817, by rfl⟩ : syracuseStep 2447513 = 1835635) B1835635
theorem B5503193 : Blo 1630514 5503193 := bstep (se 2 (by rfl) ⟨2063697, by rfl⟩ : syracuseStep 5503193 = 4127395) B4127395
theorem B2939123 : Blo 1630514 2939123 := bstep (se 1 (by rfl) ⟨2204342, by rfl⟩ : syracuseStep 2939123 = 4408685) B4408685
theorem B2447627 : Blo 1630514 2447627 := bstep (se 1 (by rfl) ⟨1835720, by rfl⟩ : syracuseStep 2447627 = 3671441) B3671441
theorem B2447639 : Blo 1630514 2447639 := bstep (se 1 (by rfl) ⟨1835729, by rfl⟩ : syracuseStep 2447639 = 3671459) B3671459
theorem B2447705 : Blo 1630514 2447705 := bstep (se 2 (by rfl) ⟨917889, by rfl⟩ : syracuseStep 2447705 = 1835779) B1835779
theorem B1743287 : Blo 1630514 1743287 := bstep (se 1 (by rfl) ⟨1307465, by rfl⟩ : syracuseStep 1743287 = 2614931) B2614931
theorem B2447819 : Blo 1630514 2447819 := bstep (se 1 (by rfl) ⟨1835864, by rfl⟩ : syracuseStep 2447819 = 3671729) B3671729
theorem B2447831 : Blo 1630514 2447831 := bstep (se 1 (by rfl) ⟨1835873, by rfl⟩ : syracuseStep 2447831 = 3671747) B3671747
theorem B2447897 : Blo 1630514 2447897 := bstep (se 2 (by rfl) ⟨917961, by rfl⟩ : syracuseStep 2447897 = 1835923) B1835923
theorem B5880365 : Blo 1630514 5880365 := bstep (se 3 (by rfl) ⟨1102568, by rfl⟩ : syracuseStep 5880365 = 2205137) B2205137
theorem B6969901 : Blo 1630514 6969901 := bstep (se 3 (by rfl) ⟨1306856, by rfl⟩ : syracuseStep 6969901 = 2613713) B2613713
theorem B8264267 : Blo 1630514 8264267 := bstep (se 1 (by rfl) ⟨6198200, by rfl⟩ : syracuseStep 8264267 = 12396401) B12396401
theorem B6191747 : Blo 1630514 6191747 := bstep (se 1 (by rfl) ⟨4643810, by rfl⟩ : syracuseStep 6191747 = 9287621) B9287621
theorem B5880451 : Blo 1630514 5880451 := bstep (se 1 (by rfl) ⟨4410338, by rfl⟩ : syracuseStep 5880451 = 8820677) B8820677
theorem B2448011 : Blo 1630514 2448011 := bstep (se 1 (by rfl) ⟨1836008, by rfl⟩ : syracuseStep 2448011 = 3672017) B3672017
theorem B6191761 : Blo 1630514 6191761 := bstep (se 2 (by rfl) ⟨2321910, by rfl⟩ : syracuseStep 6191761 = 4643821) B4643821
theorem B2448023 : Blo 1630514 2448023 := bstep (se 1 (by rfl) ⟨1836017, by rfl⟩ : syracuseStep 2448023 = 3672035) B3672035
theorem B9288371 : Blo 1630514 9288371 := bstep (se 1 (by rfl) ⟨6966278, by rfl⟩ : syracuseStep 9288371 = 13932557) B13932557
theorem B2448089 : Blo 1630514 2448089 := bstep (se 2 (by rfl) ⟨918033, by rfl⟩ : syracuseStep 2448089 = 1836067) B1836067
theorem B3668723 : Blo 1630514 3668723 := bstep (se 1 (by rfl) ⟨2751542, by rfl⟩ : syracuseStep 3668723 = 5503085) B5503085
theorem B3668759 : Blo 1630514 3668759 := bstep (se 1 (by rfl) ⟨2751569, by rfl⟩ : syracuseStep 3668759 = 5503139) B5503139
theorem B2448203 : Blo 1630514 2448203 := bstep (se 1 (by rfl) ⟨1836152, by rfl⟩ : syracuseStep 2448203 = 3672305) B3672305
theorem B2448215 : Blo 1630514 2448215 := bstep (se 1 (by rfl) ⟨1836161, by rfl⟩ : syracuseStep 2448215 = 3672323) B3672323
theorem B5503895 : Blo 1630514 5503895 := bstep (se 1 (by rfl) ⟨4127921, by rfl⟩ : syracuseStep 5503895 = 8255843) B8255843
theorem B2448281 : Blo 1630514 2448281 := bstep (se 2 (by rfl) ⟨918105, by rfl⟩ : syracuseStep 2448281 = 1836211) B1836211
theorem B6192065 : Blo 1630514 6192065 := bstep (se 2 (by rfl) ⟨2322024, by rfl⟩ : syracuseStep 6192065 = 4644049) B4644049
theorem B3668939 : Blo 1630514 3668939 := bstep (se 1 (by rfl) ⟨2751704, by rfl⟩ : syracuseStep 3668939 = 5503409) B5503409
theorem B3668993 : Blo 1630514 3668993 := bstep (se 2 (by rfl) ⟨1375872, by rfl⟩ : syracuseStep 3668993 = 2751745) B2751745
theorem B2448395 : Blo 1630514 2448395 := bstep (se 1 (by rfl) ⟨1836296, by rfl⟩ : syracuseStep 2448395 = 3672593) B3672593
theorem B2448407 : Blo 1630514 2448407 := bstep (se 1 (by rfl) ⟨1836305, by rfl⟩ : syracuseStep 2448407 = 3672611) B3672611
theorem B20913187 : Blo 1630514 20913187 := bstep (se 1 (by rfl) ⟨15684890, by rfl⟩ : syracuseStep 20913187 = 31369781) B31369781
theorem B2751563 : Blo 1630514 2751563 := bstep (se 1 (by rfl) ⟨2063672, by rfl⟩ : syracuseStep 2751563 = 4127345) B4127345
theorem B2448473 : Blo 1630514 2448473 := bstep (se 2 (by rfl) ⟨918177, by rfl⟩ : syracuseStep 2448473 = 1836355) B1836355
theorem B2751691 : Blo 1630514 2751691 := bstep (se 1 (by rfl) ⟨2063768, by rfl⟩ : syracuseStep 2751691 = 4127537) B4127537
theorem B2448587 : Blo 1630514 2448587 := bstep (se 1 (by rfl) ⟨1836440, by rfl⟩ : syracuseStep 2448587 = 3672881) B3672881
theorem B2448599 : Blo 1630514 2448599 := bstep (se 1 (by rfl) ⟨1836449, by rfl⟩ : syracuseStep 2448599 = 3672899) B3672899
theorem B3669209 : Blo 1630514 3669209 := bstep (se 2 (by rfl) ⟨1375953, by rfl⟩ : syracuseStep 3669209 = 2751907) B2751907
theorem B6282461 : Blo 1630514 6282461 := bstep (se 3 (by rfl) ⟨1177961, by rfl⟩ : syracuseStep 6282461 = 2355923) B2355923
theorem B27892997 : Blo 1630514 27892997 := bstep (se 4 (by rfl) ⟨2614968, by rfl⟩ : syracuseStep 27892997 = 5229937) B5229937
theorem B4128023 : Blo 1630514 4128023 := bstep (se 1 (by rfl) ⟨3096017, by rfl⟩ : syracuseStep 4128023 = 6192035) B6192035
theorem B2612503 : Blo 1630514 2612503 := bstep (se 1 (by rfl) ⟨1959377, by rfl⟩ : syracuseStep 2612503 = 3918755) B3918755
theorem B2448665 : Blo 1630514 2448665 := bstep (se 2 (by rfl) ⟨918249, by rfl⟩ : syracuseStep 2448665 = 1836499) B1836499
theorem B3669299 : Blo 1630514 3669299 := bstep (se 1 (by rfl) ⟨2751974, by rfl⟩ : syracuseStep 3669299 = 5503949) B5503949
theorem B3669335 : Blo 1630514 3669335 := bstep (se 1 (by rfl) ⟨2752001, by rfl⟩ : syracuseStep 3669335 = 5504003) B5504003
theorem B2751833 : Blo 1630514 2751833 := bstep (se 2 (by rfl) ⟨1031937, by rfl⟩ : syracuseStep 2751833 = 2063875) B2063875
theorem B1834411 : Blo 1630514 1834411 := bstep (se 1 (by rfl) ⟨1375808, by rfl⟩ : syracuseStep 1834411 = 2751617) B2751617
theorem B5504435 : Blo 1630514 5504435 := bstep (se 1 (by rfl) ⟨4128326, by rfl⟩ : syracuseStep 5504435 = 8256653) B8256653
theorem B2063819 : Blo 1630514 2063819 := bstep (se 1 (by rfl) ⟨1547864, by rfl⟩ : syracuseStep 2063819 = 3095729) B3095729
theorem B15670745 : Blo 1630514 15670745 := bstep (se 2 (by rfl) ⟨5876529, by rfl⟩ : syracuseStep 15670745 = 11753059) B11753059
theorem B2751961 : Blo 1630514 2751961 := bstep (se 2 (by rfl) ⟨1031985, by rfl⟩ : syracuseStep 2751961 = 2063971) B2063971
theorem B19848665 : Blo 1630514 19848665 := bstep (se 2 (by rfl) ⟨7443249, by rfl⟩ : syracuseStep 19848665 = 14886499) B14886499
theorem B8822233 : Blo 1630514 8822233 := bstep (se 2 (by rfl) ⟨3308337, by rfl⟩ : syracuseStep 8822233 = 6616675) B6616675
theorem B7544285 : Blo 1630514 7544285 := bstep (se 3 (by rfl) ⟨1414553, by rfl⟩ : syracuseStep 7544285 = 2829107) B2829107
theorem B3669515 : Blo 1630514 3669515 := bstep (se 1 (by rfl) ⟨2752136, by rfl⟩ : syracuseStep 3669515 = 5504273) B5504273
theorem B1834519 : Blo 1630514 1834519 := bstep (se 1 (by rfl) ⟨1375889, by rfl⟩ : syracuseStep 1834519 = 2751779) B2751779
theorem B3669569 : Blo 1630514 3669569 := bstep (se 2 (by rfl) ⟨1376088, by rfl⟩ : syracuseStep 3669569 = 2752177) B2752177
theorem B3096139 : Blo 1630514 3096139 := bstep (se 1 (by rfl) ⟨2322104, by rfl⟩ : syracuseStep 3096139 = 4644209) B4644209
theorem B6192733 : Blo 1630514 6192733 := bstep (se 3 (by rfl) ⟨1161137, by rfl⟩ : syracuseStep 6192733 = 2322275) B2322275
theorem B3096215 : Blo 1630514 3096215 := bstep (se 1 (by rfl) ⟨2322161, by rfl⟩ : syracuseStep 3096215 = 4644323) B4644323
theorem B3718835 : Blo 1630514 3718835 := bstep (se 1 (by rfl) ⟨2789126, by rfl⟩ : syracuseStep 3718835 = 5578253) B5578253
theorem B7061185 : Blo 1630514 7061185 := bstep (se 2 (by rfl) ⟨2647944, by rfl⟩ : syracuseStep 7061185 = 5295889) B5295889
theorem B5504705 : Blo 1630514 5504705 := bstep (se 2 (by rfl) ⟨2064264, by rfl⟩ : syracuseStep 5504705 = 4128529) B4128529
theorem B1834699 : Blo 1630514 1834699 := bstep (se 1 (by rfl) ⟨1376024, by rfl⟩ : syracuseStep 1834699 = 2752049) B2752049
theorem B3669785 : Blo 1630514 3669785 := bstep (se 2 (by rfl) ⟨1376169, by rfl⟩ : syracuseStep 3669785 = 2752339) B2752339
theorem B1834807 : Blo 1630514 1834807 := bstep (se 1 (by rfl) ⟨1376105, by rfl⟩ : syracuseStep 1834807 = 2752211) B2752211
theorem B3669875 : Blo 1630514 3669875 := bstep (se 1 (by rfl) ⟨2752406, by rfl⟩ : syracuseStep 3669875 = 5504813) B5504813
theorem B3669911 : Blo 1630514 3669911 := bstep (se 1 (by rfl) ⟨2752433, by rfl⟩ : syracuseStep 3669911 = 5504867) B5504867
theorem B4186007 : Blo 1630514 4186007 := bstep (se 1 (by rfl) ⟨3139505, by rfl⟩ : syracuseStep 4186007 = 6279011) B6279011
theorem B4128691 : Blo 1630514 4128691 := bstep (se 1 (by rfl) ⟨3096518, by rfl⟩ : syracuseStep 4128691 = 6193037) B6193037
theorem B2940875 : Blo 1630514 2940875 := bstep (se 1 (by rfl) ⟨2205656, by rfl⟩ : syracuseStep 2940875 = 4411313) B4411313
theorem B2940889 : Blo 1630514 2940889 := bstep (se 2 (by rfl) ⟨1102833, by rfl⟩ : syracuseStep 2940889 = 2205667) B2205667
theorem B12394457 : Blo 1630514 12394457 := bstep (se 2 (by rfl) ⟨4647921, by rfl⟩ : syracuseStep 12394457 = 9295843) B9295843
theorem B1834987 : Blo 1630514 1834987 := bstep (se 1 (by rfl) ⟨1376240, by rfl⟩ : syracuseStep 1834987 = 2752481) B2752481
theorem B1835023 : Blo 1630514 1835023 := bstep (se 1 (by rfl) ⟨1376267, by rfl⟩ : syracuseStep 1835023 = 2752535) B2752535
theorem B2752555 : Blo 1630514 2752555 := bstep (se 1 (by rfl) ⟨2064416, by rfl⟩ : syracuseStep 2752555 = 4128833) B4128833
theorem B6193219 : Blo 1630514 6193219 := bstep (se 1 (by rfl) ⟨4644914, by rfl⟩ : syracuseStep 6193219 = 9289829) B9289829
theorem B3670163 : Blo 1630514 3670163 := bstep (se 1 (by rfl) ⟨2752622, by rfl⟩ : syracuseStep 3670163 = 5505245) B5505245
theorem B2752697 : Blo 1630514 2752697 := bstep (se 2 (by rfl) ⟨1032261, by rfl⟩ : syracuseStep 2752697 = 2064523) B2064523
theorem B3670217 : Blo 1630514 3670217 := bstep (se 2 (by rfl) ⟨1376331, by rfl⟩ : syracuseStep 3670217 = 2752663) B2752663
theorem B1630523 : Blo 1630514 1630523 := bstep (se 1 (by rfl) ⟨1222892, by rfl⟩ : syracuseStep 1630523 = 2445785) B2445785
theorem B6193523 : Blo 1630514 6193523 := bstep (se 1 (by rfl) ⟨4645142, by rfl⟩ : syracuseStep 6193523 = 9290285) B9290285
theorem B1630599 : Blo 1630514 1630599 := bstep (se 1 (by rfl) ⟨1222949, by rfl⟩ : syracuseStep 1630599 = 2445899) B2445899
theorem B3096967 : Blo 1630514 3096967 := bstep (se 1 (by rfl) ⟨2322725, by rfl⟩ : syracuseStep 3096967 = 4645451) B4645451
theorem B1630607 : Blo 1630514 1630607 := bstep (se 1 (by rfl) ⟨1222955, by rfl⟩ : syracuseStep 1630607 = 2445911) B2445911
theorem B4129177 : Blo 1630514 4129177 := bstep (se 2 (by rfl) ⟨1548441, by rfl⟩ : syracuseStep 4129177 = 3096883) B3096883
theorem B1630651 : Blo 1630514 1630651 := bstep (se 1 (by rfl) ⟨1222988, by rfl⟩ : syracuseStep 1630651 = 2445977) B2445977
theorem B1630727 : Blo 1630514 1630727 := bstep (se 1 (by rfl) ⟨1223045, by rfl⟩ : syracuseStep 1630727 = 2446091) B2446091
theorem B1835527 : Blo 1630514 1835527 := bstep (se 1 (by rfl) ⟨1376645, by rfl⟩ : syracuseStep 1835527 = 2753291) B2753291
theorem B1630735 : Blo 1630514 1630735 := bstep (se 1 (by rfl) ⟨1223051, by rfl⟩ : syracuseStep 1630735 = 2446103) B2446103
theorem B5300765 : Blo 1630514 5300765 := bstep (se 3 (by rfl) ⟨993893, by rfl⟩ : syracuseStep 5300765 = 1987787) B1987787
theorem B1630779 : Blo 1630514 1630779 := bstep (se 1 (by rfl) ⟨1223084, by rfl⟩ : syracuseStep 1630779 = 2446169) B2446169
theorem B4129339 : Blo 1630514 4129339 := bstep (se 1 (by rfl) ⟨3097004, by rfl⟩ : syracuseStep 4129339 = 6194009) B6194009
theorem B5505623 : Blo 1630514 5505623 := bstep (se 1 (by rfl) ⟨4129217, by rfl⟩ : syracuseStep 5505623 = 8258435) B8258435
theorem B1630855 : Blo 1630514 1630855 := bstep (se 1 (by rfl) ⟨1223141, by rfl⟩ : syracuseStep 1630855 = 2446283) B2446283
theorem B1630863 : Blo 1630514 1630863 := bstep (se 1 (by rfl) ⟨1223147, by rfl⟩ : syracuseStep 1630863 = 2446295) B2446295
theorem B1630907 : Blo 1630514 1630907 := bstep (se 1 (by rfl) ⟨1223180, by rfl⟩ : syracuseStep 1630907 = 2446361) B2446361
theorem B1835707 : Blo 1630514 1835707 := bstep (se 1 (by rfl) ⟨1376780, by rfl⟩ : syracuseStep 1835707 = 2753561) B2753561
theorem B4129481 : Blo 1630514 4129481 := bstep (se 2 (by rfl) ⟨1548555, by rfl⟩ : syracuseStep 4129481 = 3097111) B3097111
theorem B23847641 : Blo 1630514 23847641 := bstep (se 2 (by rfl) ⟨8942865, by rfl⟩ : syracuseStep 23847641 = 17885731) B17885731
theorem B4645633 : Blo 1630514 4645633 := bstep (se 2 (by rfl) ⟨1742112, by rfl⟩ : syracuseStep 4645633 = 3484225) B3484225
theorem B1630983 : Blo 1630514 1630983 := bstep (se 1 (by rfl) ⟨1223237, by rfl⟩ : syracuseStep 1630983 = 2446475) B2446475
theorem B1630991 : Blo 1630514 1630991 := bstep (se 1 (by rfl) ⟨1223243, by rfl⟩ : syracuseStep 1630991 = 2446487) B2446487
theorem B1631035 : Blo 1630514 1631035 := bstep (se 1 (by rfl) ⟨1223276, by rfl⟩ : syracuseStep 1631035 = 2446553) B2446553
theorem B6193979 : Blo 1630514 6193979 := bstep (se 1 (by rfl) ⟨4645484, by rfl⟩ : syracuseStep 6193979 = 9290969) B9290969
theorem B7840601 : Blo 1630514 7840601 := bstep (se 2 (by rfl) ⟨2940225, by rfl⟩ : syracuseStep 7840601 = 5880451) B5880451
theorem B2753399 : Blo 1630514 2753399 := bstep (se 1 (by rfl) ⟨2065049, by rfl⟩ : syracuseStep 2753399 = 4130099) B4130099
theorem B1631111 : Blo 1630514 1631111 := bstep (se 1 (by rfl) ⟨1223333, by rfl⟩ : syracuseStep 1631111 = 2446667) B2446667
theorem B3670919 : Blo 1630514 3670919 := bstep (se 1 (by rfl) ⟨2753189, by rfl⟩ : syracuseStep 3670919 = 5506379) B5506379
theorem B1631119 : Blo 1630514 1631119 := bstep (se 1 (by rfl) ⟨1223339, by rfl⟩ : syracuseStep 1631119 = 2446679) B2446679
theorem B4187033 : Blo 1630514 4187033 := bstep (se 2 (by rfl) ⟨1570137, by rfl⟩ : syracuseStep 4187033 = 3140275) B3140275
theorem B1631163 : Blo 1630514 1631163 := bstep (se 1 (by rfl) ⟨1223372, by rfl⟩ : syracuseStep 1631163 = 2446745) B2446745
theorem B1631239 : Blo 1630514 1631239 := bstep (se 1 (by rfl) ⟨1223429, by rfl⟩ : syracuseStep 1631239 = 2446859) B2446859
theorem B1631247 : Blo 1630514 1631247 := bstep (se 1 (by rfl) ⟨1223435, by rfl⟩ : syracuseStep 1631247 = 2446871) B2446871
theorem B4129825 : Blo 1630514 4129825 := bstep (se 2 (by rfl) ⟨1548684, by rfl⟩ : syracuseStep 4129825 = 3097369) B3097369
theorem B1631291 : Blo 1630514 1631291 := bstep (se 1 (by rfl) ⟨1223468, by rfl⟩ : syracuseStep 1631291 = 2446937) B2446937
theorem B3671099 : Blo 1630514 3671099 := bstep (se 1 (by rfl) ⟨2753324, by rfl⟩ : syracuseStep 3671099 = 5506649) B5506649
theorem B5506109 : Blo 1630514 5506109 := bstep (se 3 (by rfl) ⟨1032395, by rfl⟩ : syracuseStep 5506109 = 2064791) B2064791
theorem B4408435 : Blo 1630514 4408435 := bstep (se 1 (by rfl) ⟨3306326, by rfl⟩ : syracuseStep 4408435 = 6612653) B6612653
theorem B1631367 : Blo 1630514 1631367 := bstep (se 1 (by rfl) ⟨1223525, by rfl⟩ : syracuseStep 1631367 = 2447051) B2447051
theorem B1631375 : Blo 1630514 1631375 := bstep (se 1 (by rfl) ⟨1223531, by rfl⟩ : syracuseStep 1631375 = 2447063) B2447063
theorem B1836175 : Blo 1630514 1836175 := bstep (se 1 (by rfl) ⟨1377131, by rfl⟩ : syracuseStep 1836175 = 2754263) B2754263
theorem B3671225 : Blo 1630514 3671225 := bstep (se 2 (by rfl) ⟨1376709, by rfl⟩ : syracuseStep 3671225 = 2753419) B2753419
theorem B1631419 : Blo 1630514 1631419 := bstep (se 1 (by rfl) ⟨1223564, by rfl⟩ : syracuseStep 1631419 = 2447129) B2447129
theorem B52929773 : Blo 1630514 52929773 := bstep (se 3 (by rfl) ⟨9924332, by rfl⟩ : syracuseStep 52929773 = 19848665) B19848665
theorem B1631495 : Blo 1630514 1631495 := bstep (se 1 (by rfl) ⟨1223621, by rfl⟩ : syracuseStep 1631495 = 2447243) B2447243
theorem B1631503 : Blo 1630514 1631503 := bstep (se 1 (by rfl) ⟨1223627, by rfl⟩ : syracuseStep 1631503 = 2447255) B2447255
theorem B4711709 : Blo 1630514 4711709 := bstep (se 3 (by rfl) ⟨883445, by rfl⟩ : syracuseStep 4711709 = 1766891) B1766891
theorem B6194465 : Blo 1630514 6194465 := bstep (se 2 (by rfl) ⟨2322924, by rfl⟩ : syracuseStep 6194465 = 4645849) B4645849
theorem B1631547 : Blo 1630514 1631547 := bstep (se 1 (by rfl) ⟨1223660, by rfl⟩ : syracuseStep 1631547 = 2447321) B2447321
theorem B2753851 : Blo 1630514 2753851 := bstep (se 1 (by rfl) ⟨2065388, by rfl⟩ : syracuseStep 2753851 = 4130777) B4130777
theorem B1631623 : Blo 1630514 1631623 := bstep (se 1 (by rfl) ⟨1223717, by rfl⟩ : syracuseStep 1631623 = 2447435) B2447435
theorem B23528839 : Blo 1630514 23528839 := bstep (se 1 (by rfl) ⟨17646629, by rfl⟩ : syracuseStep 23528839 = 35293259) B35293259
theorem B1631631 : Blo 1630514 1631631 := bstep (se 1 (by rfl) ⟨1223723, by rfl⟩ : syracuseStep 1631631 = 2447447) B2447447
theorem B1631675 : Blo 1630514 1631675 := bstep (se 1 (by rfl) ⟨1223756, by rfl⟩ : syracuseStep 1631675 = 2447513) B2447513
theorem B2753993 : Blo 1630514 2753993 := bstep (se 2 (by rfl) ⟨1032747, by rfl⟩ : syracuseStep 2753993 = 2065495) B2065495
theorem B1631751 : Blo 1630514 1631751 := bstep (se 1 (by rfl) ⟨1223813, by rfl⟩ : syracuseStep 1631751 = 2447627) B2447627
theorem B8259083 : Blo 1630514 8259083 := bstep (se 1 (by rfl) ⟨6194312, by rfl⟩ : syracuseStep 8259083 = 12388625) B12388625
theorem B1631759 : Blo 1630514 1631759 := bstep (se 1 (by rfl) ⟨1223819, by rfl⟩ : syracuseStep 1631759 = 2447639) B2447639
theorem B3671567 : Blo 1630514 3671567 := bstep (se 1 (by rfl) ⟨2753675, by rfl⟩ : syracuseStep 3671567 = 5507351) B5507351
theorem B9291287 : Blo 1630514 9291287 := bstep (se 1 (by rfl) ⟨6968465, by rfl⟩ : syracuseStep 9291287 = 13936931) B13936931
theorem B6612509 : Blo 1630514 6612509 := bstep (se 3 (by rfl) ⟨1239845, by rfl⟩ : syracuseStep 6612509 = 2479691) B2479691
theorem B3139105 : Blo 1630514 3139105 := bstep (se 2 (by rfl) ⟨1177164, by rfl⟩ : syracuseStep 3139105 = 2354329) B2354329
theorem B3671585 : Blo 1630514 3671585 := bstep (se 2 (by rfl) ⟨1376844, by rfl⟩ : syracuseStep 3671585 = 2753689) B2753689
theorem B1631803 : Blo 1630514 1631803 := bstep (se 1 (by rfl) ⟨1223852, by rfl⟩ : syracuseStep 1631803 = 2447705) B2447705
theorem B25445987 : Blo 1630514 25445987 := bstep (se 1 (by rfl) ⟨19084490, by rfl⟩ : syracuseStep 25445987 = 38168981) B38168981
theorem B4130423 : Blo 1630514 4130423 := bstep (se 1 (by rfl) ⟨3097817, by rfl⟩ : syracuseStep 4130423 = 6195635) B6195635
theorem B1631879 : Blo 1630514 1631879 := bstep (se 1 (by rfl) ⟨1223909, by rfl⟩ : syracuseStep 1631879 = 2447819) B2447819
theorem B1631887 : Blo 1630514 1631887 := bstep (se 1 (by rfl) ⟨1223915, by rfl⟩ : syracuseStep 1631887 = 2447831) B2447831
theorem B8259245 : Blo 1630514 8259245 := bstep (se 3 (by rfl) ⟨1548608, by rfl⟩ : syracuseStep 8259245 = 3097217) B3097217
theorem B1631931 : Blo 1630514 1631931 := bstep (se 1 (by rfl) ⟨1223948, by rfl⟩ : syracuseStep 1631931 = 2447897) B2447897
theorem B3483337 : Blo 1630514 3483337 := bstep (se 2 (by rfl) ⟨1306251, by rfl⟩ : syracuseStep 3483337 = 2612503) B2612503
theorem B1632007 : Blo 1630514 1632007 := bstep (se 1 (by rfl) ⟨1224005, by rfl⟩ : syracuseStep 1632007 = 2448011) B2448011
theorem B1632015 : Blo 1630514 1632015 := bstep (se 1 (by rfl) ⟨1224011, by rfl⟩ : syracuseStep 1632015 = 2448023) B2448023
theorem B1632059 : Blo 1630514 1632059 := bstep (se 1 (by rfl) ⟨1224044, by rfl⟩ : syracuseStep 1632059 = 2448089) B2448089
theorem B3721079 : Blo 1630514 3721079 := bstep (se 1 (by rfl) ⟨2790809, by rfl⟩ : syracuseStep 3721079 = 5581619) B5581619
theorem B3671927 : Blo 1630514 3671927 := bstep (se 1 (by rfl) ⟨2753945, by rfl⟩ : syracuseStep 3671927 = 5507891) B5507891
theorem B1632135 : Blo 1630514 1632135 := bstep (se 1 (by rfl) ⟨1224101, by rfl⟩ : syracuseStep 1632135 = 2448203) B2448203
theorem B1632143 : Blo 1630514 1632143 := bstep (se 1 (by rfl) ⟨1224107, by rfl⟩ : syracuseStep 1632143 = 2448215) B2448215
theorem B27871127 : Blo 1630514 27871127 := bstep (se 1 (by rfl) ⟨20903345, by rfl⟩ : syracuseStep 27871127 = 41806691) B41806691
theorem B1632187 : Blo 1630514 1632187 := bstep (se 1 (by rfl) ⟨1224140, by rfl⟩ : syracuseStep 1632187 = 2448281) B2448281
theorem B3098569 : Blo 1630514 3098569 := bstep (se 2 (by rfl) ⟨1161963, by rfl⟩ : syracuseStep 3098569 = 2323927) B2323927
theorem B1632263 : Blo 1630514 1632263 := bstep (se 1 (by rfl) ⟨1224197, by rfl⟩ : syracuseStep 1632263 = 2448395) B2448395
theorem B1632271 : Blo 1630514 1632271 := bstep (se 1 (by rfl) ⟨1224203, by rfl⟩ : syracuseStep 1632271 = 2448407) B2448407
theorem B3672107 : Blo 1630514 3672107 := bstep (se 1 (by rfl) ⟨2754080, by rfl⟩ : syracuseStep 3672107 = 5508161) B5508161
theorem B1632315 : Blo 1630514 1632315 := bstep (se 1 (by rfl) ⟨1224236, by rfl⟩ : syracuseStep 1632315 = 2448473) B2448473
theorem B1632391 : Blo 1630514 1632391 := bstep (se 1 (by rfl) ⟨1224293, by rfl⟩ : syracuseStep 1632391 = 2448587) B2448587
theorem B2754695 : Blo 1630514 2754695 := bstep (se 1 (by rfl) ⟨2066021, by rfl⟩ : syracuseStep 2754695 = 4132043) B4132043
theorem B1632399 : Blo 1630514 1632399 := bstep (se 1 (by rfl) ⟨1224299, by rfl⟩ : syracuseStep 1632399 = 2448599) B2448599
theorem B4188307 : Blo 1630514 4188307 := bstep (se 1 (by rfl) ⟨3141230, by rfl⟩ : syracuseStep 4188307 = 6282461) B6282461
theorem B1632443 : Blo 1630514 1632443 := bstep (se 1 (by rfl) ⟨1224332, by rfl⟩ : syracuseStep 1632443 = 2448665) B2448665
theorem B6195437 : Blo 1630514 6195437 := bstep (se 3 (by rfl) ⟨1161644, by rfl⟩ : syracuseStep 6195437 = 2323289) B2323289
theorem B9414913 : Blo 1630514 9414913 := bstep (se 2 (by rfl) ⟨3530592, by rfl⟩ : syracuseStep 9414913 = 7061185) B7061185
theorem B3918091 : Blo 1630514 3918091 := bstep (se 1 (by rfl) ⟨2938568, by rfl⟩ : syracuseStep 3918091 = 5877137) B5877137
theorem B10447163 : Blo 1630514 10447163 := bstep (se 1 (by rfl) ⟨7835372, by rfl⟩ : syracuseStep 10447163 = 15670745) B15670745
theorem B3672467 : Blo 1630514 3672467 := bstep (se 1 (by rfl) ⟨2754350, by rfl⟩ : syracuseStep 3672467 = 5508701) B5508701
theorem B8489369 : Blo 1630514 8489369 := bstep (se 2 (by rfl) ⟨3183513, by rfl⟩ : syracuseStep 8489369 = 6367027) B6367027
theorem B6613433 : Blo 1630514 6613433 := bstep (se 2 (by rfl) ⟨2480037, by rfl⟩ : syracuseStep 6613433 = 4960075) B4960075
theorem B5507513 : Blo 1630514 5507513 := bstep (se 2 (by rfl) ⟨2065317, by rfl⟩ : syracuseStep 5507513 = 4130635) B4130635
theorem B3672521 : Blo 1630514 3672521 := bstep (se 2 (by rfl) ⟨1377195, by rfl⟩ : syracuseStep 3672521 = 2754391) B2754391
theorem B1960583 : Blo 1630514 1960583 := bstep (se 1 (by rfl) ⟨1470437, by rfl⟩ : syracuseStep 1960583 = 2940875) B2940875
theorem B18582209 : Blo 1630514 18582209 := bstep (se 2 (by rfl) ⟨6968328, by rfl⟩ : syracuseStep 18582209 = 13936657) B13936657
theorem B19835621 : Blo 1630514 19835621 := bstep (se 4 (by rfl) ⟨1859589, by rfl⟩ : syracuseStep 19835621 = 3719179) B3719179
theorem B10062593 : Blo 1630514 10062593 := bstep (se 2 (by rfl) ⟨3773472, by rfl⟩ : syracuseStep 10062593 = 7546945) B7546945
theorem B4131719 : Blo 1630514 4131719 := bstep (se 1 (by rfl) ⟨3098789, by rfl⟩ : syracuseStep 4131719 = 6197579) B6197579
theorem B6196121 : Blo 1630514 6196121 := bstep (se 2 (by rfl) ⟨2323545, by rfl⟩ : syracuseStep 6196121 = 4647091) B4647091
theorem B4131769 : Blo 1630514 4131769 := bstep (se 2 (by rfl) ⟨1549413, by rfl⟩ : syracuseStep 4131769 = 3098827) B3098827
theorem B5508107 : Blo 1630514 5508107 := bstep (se 1 (by rfl) ⟨4131080, by rfl⟩ : syracuseStep 5508107 = 8262161) B8262161
theorem B31370327 : Blo 1630514 31370327 := bstep (se 1 (by rfl) ⟨23527745, by rfl⟩ : syracuseStep 31370327 = 47055491) B47055491
theorem B5508215 : Blo 1630514 5508215 := bstep (se 1 (by rfl) ⟨4131161, by rfl⟩ : syracuseStep 5508215 = 8262323) B8262323
theorem B18590957 : Blo 1630514 18590957 := bstep (se 3 (by rfl) ⟨3485804, by rfl⟩ : syracuseStep 18590957 = 6971609) B6971609
theorem B8260865 : Blo 1630514 8260865 := bstep (se 2 (by rfl) ⟨3097824, by rfl⟩ : syracuseStep 8260865 = 6195649) B6195649
theorem B2321723 : Blo 1630514 2321723 := bstep (se 1 (by rfl) ⟨1741292, by rfl⟩ : syracuseStep 2321723 = 3482585) B3482585
theorem B6966587 : Blo 1630514 6966587 := bstep (se 1 (by rfl) ⟨5224940, by rfl⟩ : syracuseStep 6966587 = 10449881) B10449881
theorem B5877107 : Blo 1630514 5877107 := bstep (se 1 (by rfl) ⟨4407830, by rfl⟩ : syracuseStep 5877107 = 8815661) B8815661
theorem B9293201 : Blo 1630514 9293201 := bstep (se 2 (by rfl) ⟨3484950, by rfl⟩ : syracuseStep 9293201 = 6969901) B6969901
theorem B4648583 : Blo 1630514 4648583 := bstep (se 1 (by rfl) ⟨3486437, by rfl⟩ : syracuseStep 4648583 = 6972875) B6972875
theorem B5508809 : Blo 1630514 5508809 := bstep (se 2 (by rfl) ⟨2065803, by rfl⟩ : syracuseStep 5508809 = 4131607) B4131607
theorem B4960001 : Blo 1630514 4960001 := bstep (se 2 (by rfl) ⟨1860000, by rfl⟩ : syracuseStep 4960001 = 3720001) B3720001
theorem B4648765 : Blo 1630514 4648765 := bstep (se 3 (by rfl) ⟨871643, by rfl⟩ : syracuseStep 4648765 = 1743287) B1743287
theorem B6197107 : Blo 1630514 6197107 := bstep (se 1 (by rfl) ⟨4647830, by rfl⟩ : syracuseStep 6197107 = 9295661) B9295661
theorem B4648823 : Blo 1630514 4648823 := bstep (se 1 (by rfl) ⟨3486617, by rfl⟩ : syracuseStep 4648823 = 6973235) B6973235
theorem B11915171 : Blo 1630514 11915171 := bstep (se 1 (by rfl) ⟨8936378, by rfl⟩ : syracuseStep 11915171 = 17872757) B17872757
theorem B2322361 : Blo 1630514 2322361 := bstep (se 2 (by rfl) ⟨870885, by rfl⟩ : syracuseStep 2322361 = 1741771) B1741771
theorem B3485729 : Blo 1630514 3485729 := bstep (se 2 (by rfl) ⟨1307148, by rfl⟩ : syracuseStep 3485729 = 2614297) B2614297
theorem B8261675 : Blo 1630514 8261675 := bstep (se 1 (by rfl) ⟨6196256, by rfl⟩ : syracuseStep 8261675 = 12392513) B12392513
theorem B9293885 : Blo 1630514 9293885 := bstep (se 3 (by rfl) ⟨1742603, by rfl⟩ : syracuseStep 9293885 = 3485207) B3485207
theorem B35754257 : Blo 1630514 35754257 := bstep (se 2 (by rfl) ⟨13407846, by rfl⟩ : syracuseStep 35754257 = 26815693) B26815693
theorem B3920243 : Blo 1630514 3920243 := bstep (se 1 (by rfl) ⟨2940182, by rfl⟩ : syracuseStep 3920243 = 5880365) B5880365
theorem B3486071 : Blo 1630514 3486071 := bstep (se 1 (by rfl) ⟨2614553, by rfl⟩ : syracuseStep 3486071 = 5229107) B5229107
theorem B5509511 : Blo 1630514 5509511 := bstep (se 1 (by rfl) ⟨4132133, by rfl⟩ : syracuseStep 5509511 = 8264267) B8264267
theorem B2445815 : Blo 1630514 2445815 := bstep (se 1 (by rfl) ⟨1834361, by rfl⟩ : syracuseStep 2445815 = 3668723) B3668723
theorem B2445839 : Blo 1630514 2445839 := bstep (se 1 (by rfl) ⟨1834379, by rfl⟩ : syracuseStep 2445839 = 3668759) B3668759
theorem B2445881 : Blo 1630514 2445881 := bstep (se 2 (by rfl) ⟨917205, by rfl⟩ : syracuseStep 2445881 = 1834411) B1834411
theorem B2445959 : Blo 1630514 2445959 := bstep (se 1 (by rfl) ⟨1834469, by rfl⟩ : syracuseStep 2445959 = 3668939) B3668939
theorem B2445995 : Blo 1630514 2445995 := bstep (se 1 (by rfl) ⟨1834496, by rfl⟩ : syracuseStep 2445995 = 3668993) B3668993
theorem B2446025 : Blo 1630514 2446025 := bstep (se 2 (by rfl) ⟨917259, by rfl⟩ : syracuseStep 2446025 = 1834519) B1834519
theorem B2446139 : Blo 1630514 2446139 := bstep (se 1 (by rfl) ⟨1834604, by rfl⟩ : syracuseStep 2446139 = 3669209) B3669209
theorem B3486523 : Blo 1630514 3486523 := bstep (se 1 (by rfl) ⟨2614892, by rfl⟩ : syracuseStep 3486523 = 5229785) B5229785
theorem B2446199 : Blo 1630514 2446199 := bstep (se 1 (by rfl) ⟨1834649, by rfl⟩ : syracuseStep 2446199 = 3669299) B3669299
theorem B2446223 : Blo 1630514 2446223 := bstep (se 1 (by rfl) ⟨1834667, by rfl⟩ : syracuseStep 2446223 = 3669335) B3669335
theorem B17642393 : Blo 1630514 17642393 := bstep (se 2 (by rfl) ⟨6615897, by rfl⟩ : syracuseStep 17642393 = 13231795) B13231795
theorem B2446265 : Blo 1630514 2446265 := bstep (se 2 (by rfl) ⟨917349, by rfl⟩ : syracuseStep 2446265 = 1834699) B1834699
theorem B2446343 : Blo 1630514 2446343 := bstep (se 1 (by rfl) ⟨1834757, by rfl⟩ : syracuseStep 2446343 = 3669515) B3669515
theorem B10449931 : Blo 1630514 10449931 := bstep (se 1 (by rfl) ⟨7837448, by rfl⟩ : syracuseStep 10449931 = 15674897) B15674897
theorem B2446379 : Blo 1630514 2446379 := bstep (se 1 (by rfl) ⟨1834784, by rfl⟩ : syracuseStep 2446379 = 3669569) B3669569
theorem B2446409 : Blo 1630514 2446409 := bstep (se 2 (by rfl) ⟨917403, by rfl⟩ : syracuseStep 2446409 = 1834807) B1834807
theorem B2479223 : Blo 1630514 2479223 := bstep (se 1 (by rfl) ⟨1859417, by rfl⟩ : syracuseStep 2479223 = 3718835) B3718835
theorem B2446523 : Blo 1630514 2446523 := bstep (se 1 (by rfl) ⟨1834892, by rfl⟩ : syracuseStep 2446523 = 3669785) B3669785
theorem B2446583 : Blo 1630514 2446583 := bstep (se 1 (by rfl) ⟨1834937, by rfl⟩ : syracuseStep 2446583 = 3669875) B3669875
theorem B9286913 : Blo 1630514 9286913 := bstep (se 2 (by rfl) ⟨3482592, by rfl⟩ : syracuseStep 9286913 = 6965185) B6965185
theorem B2446607 : Blo 1630514 2446607 := bstep (se 1 (by rfl) ⟨1834955, by rfl⟩ : syracuseStep 2446607 = 3669911) B3669911
theorem B2790671 : Blo 1630514 2790671 := bstep (se 1 (by rfl) ⟨2093003, by rfl⟩ : syracuseStep 2790671 = 4186007) B4186007
theorem B3921185 : Blo 1630514 3921185 := bstep (se 2 (by rfl) ⟨1470444, by rfl⟩ : syracuseStep 3921185 = 2940889) B2940889
theorem B2446649 : Blo 1630514 2446649 := bstep (se 2 (by rfl) ⟨917493, by rfl⟩ : syracuseStep 2446649 = 1834987) B1834987
theorem B31782203 : Blo 1630514 31782203 := bstep (se 1 (by rfl) ⟨23836652, by rfl⟩ : syracuseStep 31782203 = 47673305) B47673305
theorem B8262971 : Blo 1630514 8262971 := bstep (se 1 (by rfl) ⟨6197228, by rfl⟩ : syracuseStep 8262971 = 12394457) B12394457
theorem B4838771 : Blo 1630514 4838771 := bstep (se 1 (by rfl) ⟨3629078, by rfl⟩ : syracuseStep 4838771 = 7258157) B7258157
theorem B2446727 : Blo 1630514 2446727 := bstep (se 1 (by rfl) ⟨1835045, by rfl⟩ : syracuseStep 2446727 = 3670091) B3670091
theorem B2323847 : Blo 1630514 2323847 := bstep (se 1 (by rfl) ⟨1742885, by rfl⟩ : syracuseStep 2323847 = 3485771) B3485771
theorem B2446763 : Blo 1630514 2446763 := bstep (se 1 (by rfl) ⟨1835072, by rfl⟩ : syracuseStep 2446763 = 3670145) B3670145
theorem B2446793 : Blo 1630514 2446793 := bstep (se 2 (by rfl) ⟨917547, by rfl⟩ : syracuseStep 2446793 = 1835095) B1835095
theorem B8263133 : Blo 1630514 8263133 := bstep (se 3 (by rfl) ⟨1549337, by rfl⟩ : syracuseStep 8263133 = 3098675) B3098675
theorem B23516675 : Blo 1630514 23516675 := bstep (se 1 (by rfl) ⟨17637506, by rfl⟩ : syracuseStep 23516675 = 35275013) B35275013
theorem B6968861 : Blo 1630514 6968861 := bstep (se 3 (by rfl) ⟨1306661, by rfl⟩ : syracuseStep 6968861 = 2613323) B2613323
theorem B2446907 : Blo 1630514 2446907 := bstep (se 1 (by rfl) ⟨1835180, by rfl⟩ : syracuseStep 2446907 = 3670361) B3670361
theorem B25130573 : Blo 1630514 25130573 := bstep (se 3 (by rfl) ⟨4711982, by rfl⟩ : syracuseStep 25130573 = 9423965) B9423965
theorem B2446967 : Blo 1630514 2446967 := bstep (se 1 (by rfl) ⟨1835225, by rfl⟩ : syracuseStep 2446967 = 3670451) B3670451
theorem B2446991 : Blo 1630514 2446991 := bstep (se 1 (by rfl) ⟨1835243, by rfl⟩ : syracuseStep 2446991 = 3670487) B3670487
theorem B2447033 : Blo 1630514 2447033 := bstep (se 2 (by rfl) ⟨917637, by rfl⟩ : syracuseStep 2447033 = 1835275) B1835275
theorem B2324155 : Blo 1630514 2324155 := bstep (se 1 (by rfl) ⟨1743116, by rfl⟩ : syracuseStep 2324155 = 3486233) B3486233
theorem B9287369 : Blo 1630514 9287369 := bstep (se 2 (by rfl) ⟨3482763, by rfl⟩ : syracuseStep 9287369 = 6965527) B6965527
theorem B2447111 : Blo 1630514 2447111 := bstep (se 1 (by rfl) ⟨1835333, by rfl⟩ : syracuseStep 2447111 = 3670667) B3670667
theorem B8263457 : Blo 1630514 8263457 := bstep (se 2 (by rfl) ⟨3098796, by rfl⟩ : syracuseStep 8263457 = 6197593) B6197593
theorem B2447147 : Blo 1630514 2447147 := bstep (se 1 (by rfl) ⟨1835360, by rfl⟩ : syracuseStep 2447147 = 3670721) B3670721
theorem B2447177 : Blo 1630514 2447177 := bstep (se 2 (by rfl) ⟨917691, by rfl⟩ : syracuseStep 2447177 = 1835383) B1835383
theorem B2447291 : Blo 1630514 2447291 := bstep (se 1 (by rfl) ⟨1835468, by rfl⟩ : syracuseStep 2447291 = 3670937) B3670937
theorem B7837661 : Blo 1630514 7837661 := bstep (se 3 (by rfl) ⟨1469561, by rfl⟩ : syracuseStep 7837661 = 2939123) B2939123
theorem B2447351 : Blo 1630514 2447351 := bstep (se 1 (by rfl) ⟨1835513, by rfl⟩ : syracuseStep 2447351 = 3671027) B3671027
theorem B2447375 : Blo 1630514 2447375 := bstep (se 1 (by rfl) ⟨1835531, by rfl⟩ : syracuseStep 2447375 = 3671063) B3671063
theorem B21485591 : Blo 1630514 21485591 := bstep (se 1 (by rfl) ⟨16114193, by rfl⟩ : syracuseStep 21485591 = 32228387) B32228387
theorem B5298205 : Blo 1630514 5298205 := bstep (se 3 (by rfl) ⟨993413, by rfl⟩ : syracuseStep 5298205 = 1986827) B1986827
theorem B2447417 : Blo 1630514 2447417 := bstep (se 2 (by rfl) ⟨917781, by rfl⟩ : syracuseStep 2447417 = 1835563) B1835563
theorem B2447495 : Blo 1630514 2447495 := bstep (se 1 (by rfl) ⟨1835621, by rfl⟩ : syracuseStep 2447495 = 3671243) B3671243
theorem B2447531 : Blo 1630514 2447531 := bstep (se 1 (by rfl) ⟨1835648, by rfl⟩ : syracuseStep 2447531 = 3671297) B3671297
theorem B27875501 : Blo 1630514 27875501 := bstep (se 3 (by rfl) ⟨5226656, by rfl⟩ : syracuseStep 27875501 = 10453313) B10453313
theorem B8255681 : Blo 1630514 8255681 := bstep (se 2 (by rfl) ⟨3095880, by rfl⟩ : syracuseStep 8255681 = 6191761) B6191761
theorem B2447561 : Blo 1630514 2447561 := bstep (se 2 (by rfl) ⟨917835, by rfl⟩ : syracuseStep 2447561 = 1835671) B1835671
theorem B5503247 : Blo 1630514 5503247 := bstep (se 1 (by rfl) ⟨4127435, by rfl⟩ : syracuseStep 5503247 = 8254871) B8254871
theorem B3307819 : Blo 1630514 3307819 := bstep (se 1 (by rfl) ⟨2480864, by rfl⟩ : syracuseStep 3307819 = 4961729) B4961729
theorem B2447675 : Blo 1630514 2447675 := bstep (se 1 (by rfl) ⟨1835756, by rfl⟩ : syracuseStep 2447675 = 3671513) B3671513
theorem B2447735 : Blo 1630514 2447735 := bstep (se 1 (by rfl) ⟨1835801, by rfl⟩ : syracuseStep 2447735 = 3671603) B3671603
theorem B4643207 : Blo 1630514 4643207 := bstep (se 1 (by rfl) ⟨3482405, by rfl⟩ : syracuseStep 4643207 = 6964811) B6964811
theorem B2447759 : Blo 1630514 2447759 := bstep (se 1 (by rfl) ⟨1835819, by rfl⟩ : syracuseStep 2447759 = 3671639) B3671639
theorem B2447801 : Blo 1630514 2447801 := bstep (se 2 (by rfl) ⟨917925, by rfl⟩ : syracuseStep 2447801 = 1835851) B1835851
theorem B2447879 : Blo 1630514 2447879 := bstep (se 1 (by rfl) ⟨1835909, by rfl⟩ : syracuseStep 2447879 = 3671819) B3671819
theorem B5503517 : Blo 1630514 5503517 := bstep (se 3 (by rfl) ⟨1031909, by rfl⟩ : syracuseStep 5503517 = 2063819) B2063819
theorem B2447915 : Blo 1630514 2447915 := bstep (se 1 (by rfl) ⟨1835936, by rfl⟩ : syracuseStep 2447915 = 3671873) B3671873
theorem B2447945 : Blo 1630514 2447945 := bstep (se 2 (by rfl) ⟨917979, by rfl⟩ : syracuseStep 2447945 = 1835959) B1835959
theorem B2448059 : Blo 1630514 2448059 := bstep (se 1 (by rfl) ⟨1836044, by rfl⟩ : syracuseStep 2448059 = 3672089) B3672089
theorem B27884249 : Blo 1630514 27884249 := bstep (se 2 (by rfl) ⟨10456593, by rfl⟩ : syracuseStep 27884249 = 20913187) B20913187
theorem B8264429 : Blo 1630514 8264429 := bstep (se 3 (by rfl) ⟨1549580, by rfl⟩ : syracuseStep 8264429 = 3099161) B3099161
theorem B2448119 : Blo 1630514 2448119 := bstep (se 1 (by rfl) ⟨1836089, by rfl⟩ : syracuseStep 2448119 = 3672179) B3672179
theorem B2448143 : Blo 1630514 2448143 := bstep (se 1 (by rfl) ⟨1836107, by rfl⟩ : syracuseStep 2448143 = 3672215) B3672215
theorem B5225249 : Blo 1630514 5225249 := bstep (se 2 (by rfl) ⟨1959468, by rfl⟩ : syracuseStep 5225249 = 3918937) B3918937
theorem B2480939 : Blo 1630514 2480939 := bstep (se 1 (by rfl) ⟨1860704, by rfl⟩ : syracuseStep 2480939 = 3721409) B3721409
theorem B2448185 : Blo 1630514 2448185 := bstep (se 2 (by rfl) ⟨918069, by rfl⟩ : syracuseStep 2448185 = 1836139) B1836139
theorem B3668795 : Blo 1630514 3668795 := bstep (se 1 (by rfl) ⟨2751596, by rfl⟩ : syracuseStep 3668795 = 5503193) B5503193
theorem B2448263 : Blo 1630514 2448263 := bstep (se 1 (by rfl) ⟨1836197, by rfl⟩ : syracuseStep 2448263 = 3672395) B3672395
theorem B2448299 : Blo 1630514 2448299 := bstep (se 1 (by rfl) ⟨1836224, by rfl⟩ : syracuseStep 2448299 = 3672449) B3672449
theorem B3668921 : Blo 1630514 3668921 := bstep (se 2 (by rfl) ⟨1375845, by rfl⟩ : syracuseStep 3668921 = 2751691) B2751691
theorem B2448329 : Blo 1630514 2448329 := bstep (se 2 (by rfl) ⟨918123, by rfl⟩ : syracuseStep 2448329 = 1836247) B1836247
theorem B2448443 : Blo 1630514 2448443 := bstep (se 1 (by rfl) ⟨1836332, by rfl⟩ : syracuseStep 2448443 = 3672665) B3672665
theorem B4127831 : Blo 1630514 4127831 := bstep (se 1 (by rfl) ⟨3095873, by rfl⟩ : syracuseStep 4127831 = 6191747) B6191747
theorem B6192247 : Blo 1630514 6192247 := bstep (se 1 (by rfl) ⟨4644185, by rfl⟩ : syracuseStep 6192247 = 9288371) B9288371
theorem B2448503 : Blo 1630514 2448503 := bstep (se 1 (by rfl) ⟨1836377, by rfl⟩ : syracuseStep 2448503 = 3672755) B3672755
theorem B2448527 : Blo 1630514 2448527 := bstep (se 1 (by rfl) ⟨1836395, by rfl⟩ : syracuseStep 2448527 = 3672791) B3672791
theorem B4643993 : Blo 1630514 4643993 := bstep (se 2 (by rfl) ⟨1741497, by rfl⟩ : syracuseStep 4643993 = 3482995) B3482995
theorem B2448569 : Blo 1630514 2448569 := bstep (se 2 (by rfl) ⟨918213, by rfl⟩ : syracuseStep 2448569 = 1836427) B1836427
theorem B92978381 : Blo 1630514 92978381 := bstep (se 3 (by rfl) ⟨17433446, by rfl⟩ : syracuseStep 92978381 = 34866893) B34866893
theorem B2448647 : Blo 1630514 2448647 := bstep (se 1 (by rfl) ⟨1836485, by rfl⟩ : syracuseStep 2448647 = 3672971) B3672971
theorem B3669263 : Blo 1630514 3669263 := bstep (se 1 (by rfl) ⟨2751947, by rfl⟩ : syracuseStep 3669263 = 5503895) B5503895
theorem B3669281 : Blo 1630514 3669281 := bstep (se 2 (by rfl) ⟨1375980, by rfl⟩ : syracuseStep 3669281 = 2751961) B2751961
theorem B11762977 : Blo 1630514 11762977 := bstep (se 2 (by rfl) ⟨4411116, by rfl⟩ : syracuseStep 11762977 = 8822233) B8822233
theorem B4128043 : Blo 1630514 4128043 := bstep (se 1 (by rfl) ⟨3096032, by rfl⟩ : syracuseStep 4128043 = 6192065) B6192065
theorem B2448683 : Blo 1630514 2448683 := bstep (se 1 (by rfl) ⟨1836512, by rfl⟩ : syracuseStep 2448683 = 3673025) B3673025
theorem B2448713 : Blo 1630514 2448713 := bstep (se 2 (by rfl) ⟨918267, by rfl⟩ : syracuseStep 2448713 = 1836535) B1836535
theorem B1834375 : Blo 1630514 1834375 := bstep (se 1 (by rfl) ⟨1375781, by rfl⟩ : syracuseStep 1834375 = 2751563) B2751563
theorem B4128185 : Blo 1630514 4128185 := bstep (se 2 (by rfl) ⟨1548069, by rfl⟩ : syracuseStep 4128185 = 3096139) B3096139
theorem B8256977 : Blo 1630514 8256977 := bstep (se 2 (by rfl) ⟨3096366, by rfl⟩ : syracuseStep 8256977 = 6192733) B6192733
theorem B18595331 : Blo 1630514 18595331 := bstep (se 1 (by rfl) ⟨13946498, by rfl⟩ : syracuseStep 18595331 = 27892997) B27892997
theorem B2752015 : Blo 1630514 2752015 := bstep (se 1 (by rfl) ⟨2064011, by rfl⟩ : syracuseStep 2752015 = 4128023) B4128023
theorem B1834555 : Blo 1630514 1834555 := bstep (se 1 (by rfl) ⟨1375916, by rfl⟩ : syracuseStep 1834555 = 2751833) B2751833
theorem B3669623 : Blo 1630514 3669623 := bstep (se 1 (by rfl) ⟨2752217, by rfl⟩ : syracuseStep 3669623 = 5504435) B5504435
theorem B16113271 : Blo 1630514 16113271 := bstep (se 1 (by rfl) ⟨12084953, by rfl⟩ : syracuseStep 16113271 = 24169907) B24169907
theorem B5029523 : Blo 1630514 5029523 := bstep (se 1 (by rfl) ⟨3772142, by rfl⟩ : syracuseStep 5029523 = 7544285) B7544285
theorem B6282953 : Blo 1630514 6282953 := bstep (se 2 (by rfl) ⟨2356107, by rfl⟩ : syracuseStep 6282953 = 4712215) B4712215
theorem B16981721 : Blo 1630514 16981721 := bstep (se 2 (by rfl) ⟨6368145, by rfl⟩ : syracuseStep 16981721 = 12736291) B12736291
theorem B2064143 : Blo 1630514 2064143 := bstep (se 1 (by rfl) ⟨1548107, by rfl⟩ : syracuseStep 2064143 = 3096215) B3096215
theorem B4644641 : Blo 1630514 4644641 := bstep (se 2 (by rfl) ⟨1741740, by rfl⟩ : syracuseStep 4644641 = 3483481) B3483481
theorem B3669803 : Blo 1630514 3669803 := bstep (se 1 (by rfl) ⟨2752352, by rfl⟩ : syracuseStep 3669803 = 5504705) B5504705
theorem B2613035 : Blo 1630514 2613035 := bstep (se 1 (by rfl) ⟨1959776, by rfl⟩ : syracuseStep 2613035 = 3919553) B3919553
theorem B67927853 : Blo 1630514 67927853 := bstep (se 3 (by rfl) ⟨12736472, by rfl⟩ : syracuseStep 67927853 = 25472945) B25472945
theorem B5504921 : Blo 1630514 5504921 := bstep (se 2 (by rfl) ⟨2064345, by rfl⟩ : syracuseStep 5504921 = 4128691) B4128691
theorem B3670073 : Blo 1630514 3670073 := bstep (se 2 (by rfl) ⟨1376277, by rfl⟩ : syracuseStep 3670073 = 2752555) B2752555
theorem B8257625 : Blo 1630514 8257625 := bstep (se 2 (by rfl) ⟨3096609, by rfl⟩ : syracuseStep 8257625 = 6193219) B6193219
theorem B1835131 : Blo 1630514 1835131 := bstep (se 1 (by rfl) ⟨1376348, by rfl⟩ : syracuseStep 1835131 = 2752697) B2752697
theorem B4129015 : Blo 1630514 4129015 := bstep (se 1 (by rfl) ⟨3096761, by rfl⟩ : syracuseStep 4129015 = 6193523) B6193523
theorem B1630543 : Blo 1630514 1630543 := bstep (se 1 (by rfl) ⟨1222907, by rfl⟩ : syracuseStep 1630543 = 2445815) B2445815
theorem B1630559 : Blo 1630514 1630559 := bstep (se 1 (by rfl) ⟨1222919, by rfl⟩ : syracuseStep 1630559 = 2445839) B2445839
theorem B1630587 : Blo 1630514 1630587 := bstep (se 1 (by rfl) ⟨1222940, by rfl⟩ : syracuseStep 1630587 = 2445881) B2445881
theorem B3670415 : Blo 1630514 3670415 := bstep (se 1 (by rfl) ⟨2752811, by rfl⟩ : syracuseStep 3670415 = 5505623) B5505623
theorem B1630639 : Blo 1630514 1630639 := bstep (se 1 (by rfl) ⟨1222979, by rfl⟩ : syracuseStep 1630639 = 2445959) B2445959
theorem B1630663 : Blo 1630514 1630663 := bstep (se 1 (by rfl) ⟨1222997, by rfl⟩ : syracuseStep 1630663 = 2445995) B2445995
theorem B1630683 : Blo 1630514 1630683 := bstep (se 1 (by rfl) ⟨1223012, by rfl⟩ : syracuseStep 1630683 = 2446025) B2446025
theorem B2752987 : Blo 1630514 2752987 := bstep (se 1 (by rfl) ⟨2064740, by rfl⟩ : syracuseStep 2752987 = 4129481) B4129481
theorem B4129289 : Blo 1630514 4129289 := bstep (se 2 (by rfl) ⟨1548483, by rfl⟩ : syracuseStep 4129289 = 3096967) B3096967
theorem B5505569 : Blo 1630514 5505569 := bstep (se 2 (by rfl) ⟨2064588, by rfl⟩ : syracuseStep 5505569 = 4129177) B4129177
theorem B1630759 : Blo 1630514 1630759 := bstep (se 1 (by rfl) ⟨1223069, by rfl⟩ : syracuseStep 1630759 = 2446139) B2446139
theorem B4129319 : Blo 1630514 4129319 := bstep (se 1 (by rfl) ⟨3096989, by rfl⟩ : syracuseStep 4129319 = 6193979) B6193979
theorem B5227067 : Blo 1630514 5227067 := bstep (se 1 (by rfl) ⟨3920300, by rfl⟩ : syracuseStep 5227067 = 7840601) B7840601
theorem B1630799 : Blo 1630514 1630799 := bstep (se 1 (by rfl) ⟨1223099, by rfl⟩ : syracuseStep 1630799 = 2446199) B2446199
theorem B1835599 : Blo 1630514 1835599 := bstep (se 1 (by rfl) ⟨1376699, by rfl⟩ : syracuseStep 1835599 = 2753399) B2753399
theorem B1630815 : Blo 1630514 1630815 := bstep (se 1 (by rfl) ⟨1223111, by rfl⟩ : syracuseStep 1630815 = 2446223) B2446223
theorem B23511653 : Blo 1630514 23511653 := bstep (se 4 (by rfl) ⟨2204217, by rfl⟩ : syracuseStep 23511653 = 4408435) B4408435
theorem B1630843 : Blo 1630514 1630843 := bstep (se 1 (by rfl) ⟨1223132, by rfl⟩ : syracuseStep 1630843 = 2446265) B2446265
theorem B1630895 : Blo 1630514 1630895 := bstep (se 1 (by rfl) ⟨1223171, by rfl⟩ : syracuseStep 1630895 = 2446343) B2446343
theorem B1630919 : Blo 1630514 1630919 := bstep (se 1 (by rfl) ⟨1223189, by rfl⟩ : syracuseStep 1630919 = 2446379) B2446379
theorem B3670739 : Blo 1630514 3670739 := bstep (se 1 (by rfl) ⟨2753054, by rfl⟩ : syracuseStep 3670739 = 5506109) B5506109
theorem B1630939 : Blo 1630514 1630939 := bstep (se 1 (by rfl) ⟨1223204, by rfl⟩ : syracuseStep 1630939 = 2446409) B2446409
theorem B5505785 : Blo 1630514 5505785 := bstep (se 2 (by rfl) ⟨2064669, by rfl⟩ : syracuseStep 5505785 = 4129339) B4129339
theorem B1631015 : Blo 1630514 1631015 := bstep (se 1 (by rfl) ⟨1223261, by rfl⟩ : syracuseStep 1631015 = 2446523) B2446523
theorem B1631055 : Blo 1630514 1631055 := bstep (se 1 (by rfl) ⟨1223291, by rfl⟩ : syracuseStep 1631055 = 2446583) B2446583
theorem B1631071 : Blo 1630514 1631071 := bstep (se 1 (by rfl) ⟨1223303, by rfl⟩ : syracuseStep 1631071 = 2446607) B2446607
theorem B4129643 : Blo 1630514 4129643 := bstep (se 1 (by rfl) ⟨3097232, by rfl⟩ : syracuseStep 4129643 = 6194465) B6194465
theorem B2614123 : Blo 1630514 2614123 := bstep (se 1 (by rfl) ⟨1960592, by rfl⟩ : syracuseStep 2614123 = 3921185) B3921185
theorem B1631099 : Blo 1630514 1631099 := bstep (se 1 (by rfl) ⟨1223324, by rfl⟩ : syracuseStep 1631099 = 2446649) B2446649
theorem B1631151 : Blo 1630514 1631151 := bstep (se 1 (by rfl) ⟨1223363, by rfl⟩ : syracuseStep 1631151 = 2446727) B2446727
theorem B1631175 : Blo 1630514 1631175 := bstep (se 1 (by rfl) ⟨1223381, by rfl⟩ : syracuseStep 1631175 = 2446763) B2446763
theorem B1631195 : Blo 1630514 1631195 := bstep (se 1 (by rfl) ⟨1223396, by rfl⟩ : syracuseStep 1631195 = 2446793) B2446793
theorem B1835995 : Blo 1630514 1835995 := bstep (se 1 (by rfl) ⟨1376996, by rfl⟩ : syracuseStep 1835995 = 2753993) B2753993
theorem B10453981 : Blo 1630514 10453981 := bstep (se 3 (by rfl) ⟨1960121, by rfl⟩ : syracuseStep 10453981 = 3920243) B3920243
theorem B6194177 : Blo 1630514 6194177 := bstep (se 2 (by rfl) ⟨2322816, by rfl⟩ : syracuseStep 6194177 = 4645633) B4645633
theorem B5506055 : Blo 1630514 5506055 := bstep (se 1 (by rfl) ⟨4129541, by rfl⟩ : syracuseStep 5506055 = 8259083) B8259083
theorem B6194191 : Blo 1630514 6194191 := bstep (se 1 (by rfl) ⟨4645643, by rfl⟩ : syracuseStep 6194191 = 9291287) B9291287
theorem B4408339 : Blo 1630514 4408339 := bstep (se 1 (by rfl) ⟨3306254, by rfl⟩ : syracuseStep 4408339 = 6612509) B6612509
theorem B4645907 : Blo 1630514 4645907 := bstep (se 1 (by rfl) ⟨3484430, by rfl⟩ : syracuseStep 4645907 = 6968861) B6968861
theorem B1631271 : Blo 1630514 1631271 := bstep (se 1 (by rfl) ⟨1223453, by rfl⟩ : syracuseStep 1631271 = 2446907) B2446907
theorem B16753715 : Blo 1630514 16753715 := bstep (se 1 (by rfl) ⟨12565286, by rfl⟩ : syracuseStep 16753715 = 25130573) B25130573
theorem B1631311 : Blo 1630514 1631311 := bstep (se 1 (by rfl) ⟨1223483, by rfl⟩ : syracuseStep 1631311 = 2446967) B2446967
theorem B2753615 : Blo 1630514 2753615 := bstep (se 1 (by rfl) ⟨2065211, by rfl⟩ : syracuseStep 2753615 = 4130423) B4130423
theorem B1631327 : Blo 1630514 1631327 := bstep (se 1 (by rfl) ⟨1223495, by rfl⟩ : syracuseStep 1631327 = 2446991) B2446991
theorem B5506163 : Blo 1630514 5506163 := bstep (se 1 (by rfl) ⟨4129622, by rfl⟩ : syracuseStep 5506163 = 8259245) B8259245
theorem B1631355 : Blo 1630514 1631355 := bstep (se 1 (by rfl) ⟨1223516, by rfl⟩ : syracuseStep 1631355 = 2447033) B2447033
theorem B1631407 : Blo 1630514 1631407 := bstep (se 1 (by rfl) ⟨1223555, by rfl⟩ : syracuseStep 1631407 = 2447111) B2447111
theorem B1631431 : Blo 1630514 1631431 := bstep (se 1 (by rfl) ⟨1223573, by rfl⟩ : syracuseStep 1631431 = 2447147) B2447147
theorem B1631451 : Blo 1630514 1631451 := bstep (se 1 (by rfl) ⟨1223588, by rfl⟩ : syracuseStep 1631451 = 2447177) B2447177
theorem B18580751 : Blo 1630514 18580751 := bstep (se 1 (by rfl) ⟨13935563, by rfl⟩ : syracuseStep 18580751 = 27871127) B27871127
theorem B1631527 : Blo 1630514 1631527 := bstep (se 1 (by rfl) ⟨1223645, by rfl⟩ : syracuseStep 1631527 = 2447291) B2447291
theorem B1631567 : Blo 1630514 1631567 := bstep (se 1 (by rfl) ⟨1223675, by rfl⟩ : syracuseStep 1631567 = 2447351) B2447351
theorem B1631583 : Blo 1630514 1631583 := bstep (se 1 (by rfl) ⟨1223687, by rfl⟩ : syracuseStep 1631583 = 2447375) B2447375
theorem B1631611 : Blo 1630514 1631611 := bstep (se 1 (by rfl) ⟨1223708, by rfl⟩ : syracuseStep 1631611 = 2447417) B2447417
theorem B5506433 : Blo 1630514 5506433 := bstep (se 2 (by rfl) ⟨2064912, by rfl⟩ : syracuseStep 5506433 = 4129825) B4129825
theorem B1631663 : Blo 1630514 1631663 := bstep (se 1 (by rfl) ⟨1223747, by rfl⟩ : syracuseStep 1631663 = 2447495) B2447495
theorem B1836463 : Blo 1630514 1836463 := bstep (se 1 (by rfl) ⟨1377347, by rfl⟩ : syracuseStep 1836463 = 2754695) B2754695
theorem B1631687 : Blo 1630514 1631687 := bstep (se 1 (by rfl) ⟨1223765, by rfl⟩ : syracuseStep 1631687 = 2447531) B2447531
theorem B1631707 : Blo 1630514 1631707 := bstep (se 1 (by rfl) ⟨1223780, by rfl⟩ : syracuseStep 1631707 = 2447561) B2447561
theorem B4130291 : Blo 1630514 4130291 := bstep (se 1 (by rfl) ⟨3097718, by rfl⟩ : syracuseStep 4130291 = 6195437) B6195437
theorem B6964775 : Blo 1630514 6964775 := bstep (se 1 (by rfl) ⟨5223581, by rfl⟩ : syracuseStep 6964775 = 10447163) B10447163
theorem B1631783 : Blo 1630514 1631783 := bstep (se 1 (by rfl) ⟨1223837, by rfl⟩ : syracuseStep 1631783 = 2447675) B2447675
theorem B1631823 : Blo 1630514 1631823 := bstep (se 1 (by rfl) ⟨1223867, by rfl⟩ : syracuseStep 1631823 = 2447735) B2447735
theorem B1631839 : Blo 1630514 1631839 := bstep (se 1 (by rfl) ⟨1223879, by rfl⟩ : syracuseStep 1631839 = 2447759) B2447759
theorem B4408955 : Blo 1630514 4408955 := bstep (se 1 (by rfl) ⟨3306716, by rfl⟩ : syracuseStep 4408955 = 6613433) B6613433
theorem B3671675 : Blo 1630514 3671675 := bstep (se 1 (by rfl) ⟨2753756, by rfl⟩ : syracuseStep 3671675 = 5507513) B5507513
theorem B1631867 : Blo 1630514 1631867 := bstep (se 1 (by rfl) ⟨1223900, by rfl⟩ : syracuseStep 1631867 = 2447801) B2447801
theorem B1631919 : Blo 1630514 1631919 := bstep (se 1 (by rfl) ⟨1223939, by rfl⟩ : syracuseStep 1631919 = 2447879) B2447879
theorem B5228221 : Blo 1630514 5228221 := bstep (se 3 (by rfl) ⟨980291, by rfl⟩ : syracuseStep 5228221 = 1960583) B1960583
theorem B1631943 : Blo 1630514 1631943 := bstep (se 1 (by rfl) ⟨1223957, by rfl⟩ : syracuseStep 1631943 = 2447915) B2447915
theorem B1631963 : Blo 1630514 1631963 := bstep (se 1 (by rfl) ⟨1223972, by rfl⟩ : syracuseStep 1631963 = 2447945) B2447945
theorem B3671801 : Blo 1630514 3671801 := bstep (se 2 (by rfl) ⟨1376925, by rfl⟩ : syracuseStep 3671801 = 2753851) B2753851
theorem B1632039 : Blo 1630514 1632039 := bstep (se 1 (by rfl) ⟨1224029, by rfl⟩ : syracuseStep 1632039 = 2448059) B2448059
theorem B12388139 : Blo 1630514 12388139 := bstep (se 1 (by rfl) ⟨9291104, by rfl⟩ : syracuseStep 12388139 = 18582209) B18582209
theorem B18589499 : Blo 1630514 18589499 := bstep (se 1 (by rfl) ⟨13942124, by rfl⟩ : syracuseStep 18589499 = 27884249) B27884249
theorem B13223747 : Blo 1630514 13223747 := bstep (se 1 (by rfl) ⟨9917810, by rfl⟩ : syracuseStep 13223747 = 19835621) B19835621
theorem B1632079 : Blo 1630514 1632079 := bstep (se 1 (by rfl) ⟨1224059, by rfl⟩ : syracuseStep 1632079 = 2448119) B2448119
theorem B1632095 : Blo 1630514 1632095 := bstep (se 1 (by rfl) ⟨1224071, by rfl⟩ : syracuseStep 1632095 = 2448143) B2448143
theorem B3483499 : Blo 1630514 3483499 := bstep (se 1 (by rfl) ⟨2612624, by rfl⟩ : syracuseStep 3483499 = 5225249) B5225249
theorem B1632123 : Blo 1630514 1632123 := bstep (se 1 (by rfl) ⟨1224092, by rfl⟩ : syracuseStep 1632123 = 2448185) B2448185
theorem B1632175 : Blo 1630514 1632175 := bstep (se 1 (by rfl) ⟨1224131, by rfl⟩ : syracuseStep 1632175 = 2448263) B2448263
theorem B2754479 : Blo 1630514 2754479 := bstep (se 1 (by rfl) ⟨2065859, by rfl⟩ : syracuseStep 2754479 = 4131719) B4131719
theorem B4130747 : Blo 1630514 4130747 := bstep (se 1 (by rfl) ⟨3098060, by rfl⟩ : syracuseStep 4130747 = 6196121) B6196121
theorem B1632199 : Blo 1630514 1632199 := bstep (se 1 (by rfl) ⟨1224149, by rfl⟩ : syracuseStep 1632199 = 2448299) B2448299
theorem B1632219 : Blo 1630514 1632219 := bstep (se 1 (by rfl) ⟨1224164, by rfl⟩ : syracuseStep 1632219 = 2448329) B2448329
theorem B3672071 : Blo 1630514 3672071 := bstep (se 1 (by rfl) ⟨2754053, by rfl⟩ : syracuseStep 3672071 = 5508107) B5508107
theorem B1632295 : Blo 1630514 1632295 := bstep (se 1 (by rfl) ⟨1224221, by rfl⟩ : syracuseStep 1632295 = 2448443) B2448443
theorem B3672143 : Blo 1630514 3672143 := bstep (se 1 (by rfl) ⟨2754107, by rfl⟩ : syracuseStep 3672143 = 5508215) B5508215
theorem B1632335 : Blo 1630514 1632335 := bstep (se 1 (by rfl) ⟨1224251, by rfl⟩ : syracuseStep 1632335 = 2448503) B2448503
theorem B1632351 : Blo 1630514 1632351 := bstep (se 1 (by rfl) ⟨1224263, by rfl⟩ : syracuseStep 1632351 = 2448527) B2448527
theorem B1632379 : Blo 1630514 1632379 := bstep (se 1 (by rfl) ⟨1224284, by rfl⟩ : syracuseStep 1632379 = 2448569) B2448569
theorem B5507243 : Blo 1630514 5507243 := bstep (se 1 (by rfl) ⟨4130432, by rfl⟩ : syracuseStep 5507243 = 8260865) B8260865
theorem B1632431 : Blo 1630514 1632431 := bstep (se 1 (by rfl) ⟨1224323, by rfl⟩ : syracuseStep 1632431 = 2448647) B2448647
theorem B1632455 : Blo 1630514 1632455 := bstep (se 1 (by rfl) ⟨1224341, by rfl⟩ : syracuseStep 1632455 = 2448683) B2448683
theorem B1632475 : Blo 1630514 1632475 := bstep (se 1 (by rfl) ⟨1224356, by rfl⟩ : syracuseStep 1632475 = 2448713) B2448713
theorem B3918071 : Blo 1630514 3918071 := bstep (se 1 (by rfl) ⟨2938553, by rfl⟩ : syracuseStep 3918071 = 5877107) B5877107
theorem B3098873 : Blo 1630514 3098873 := bstep (se 2 (by rfl) ⟨1162077, by rfl⟩ : syracuseStep 3098873 = 2324155) B2324155
theorem B6195467 : Blo 1630514 6195467 := bstep (se 1 (by rfl) ⟨4646600, by rfl⟩ : syracuseStep 6195467 = 9293201) B9293201
theorem B12396887 : Blo 1630514 12396887 := bstep (se 1 (by rfl) ⟨9297665, by rfl⟩ : syracuseStep 12396887 = 18595331) B18595331
theorem B3099055 : Blo 1630514 3099055 := bstep (se 1 (by rfl) ⟨2324291, by rfl⟩ : syracuseStep 3099055 = 4648583) B4648583
theorem B3353015 : Blo 1630514 3353015 := bstep (se 1 (by rfl) ⟨2514761, by rfl⟩ : syracuseStep 3353015 = 5029523) B5029523
theorem B3672539 : Blo 1630514 3672539 := bstep (se 1 (by rfl) ⟨2754404, by rfl⟩ : syracuseStep 3672539 = 5508809) B5508809
theorem B4188635 : Blo 1630514 4188635 := bstep (se 1 (by rfl) ⟨3141476, by rfl⟩ : syracuseStep 4188635 = 6282953) B6282953
theorem B20900429 : Blo 1630514 20900429 := bstep (se 3 (by rfl) ⟨3918830, by rfl⟩ : syracuseStep 20900429 = 7837661) B7837661
theorem B3099215 : Blo 1630514 3099215 := bstep (se 1 (by rfl) ⟨2324411, by rfl⟩ : syracuseStep 3099215 = 4648823) B4648823
theorem B4131425 : Blo 1630514 4131425 := bstep (se 2 (by rfl) ⟨1549284, by rfl⟩ : syracuseStep 4131425 = 3098569) B3098569
theorem B5507783 : Blo 1630514 5507783 := bstep (se 1 (by rfl) ⟨4130837, by rfl⟩ : syracuseStep 5507783 = 8261675) B8261675
theorem B7064273 : Blo 1630514 7064273 := bstep (se 2 (by rfl) ⟨2649102, by rfl⟩ : syracuseStep 7064273 = 5298205) B5298205
theorem B6195923 : Blo 1630514 6195923 := bstep (se 1 (by rfl) ⟨4646942, by rfl⟩ : syracuseStep 6195923 = 9293885) B9293885
theorem B3673007 : Blo 1630514 3673007 := bstep (se 1 (by rfl) ⟨2754755, by rfl⟩ : syracuseStep 3673007 = 5509511) B5509511
theorem B12553217 : Blo 1630514 12553217 := bstep (se 2 (by rfl) ⟨4707456, by rfl⟩ : syracuseStep 12553217 = 9414913) B9414913
theorem B3533843 : Blo 1630514 3533843 := bstep (se 1 (by rfl) ⟨2650382, by rfl⟩ : syracuseStep 3533843 = 5300765) B5300765
theorem B4410425 : Blo 1630514 4410425 := bstep (se 2 (by rfl) ⟨1653909, by rfl⟩ : syracuseStep 4410425 = 3307819) B3307819
theorem B7441789 : Blo 1630514 7441789 := bstep (se 3 (by rfl) ⟨1395335, by rfl⟩ : syracuseStep 7441789 = 2790671) B2790671
theorem B35286515 : Blo 1630514 35286515 := bstep (se 1 (by rfl) ⟨26464886, by rfl⟩ : syracuseStep 35286515 = 52929773) B52929773
theorem B21188135 : Blo 1630514 21188135 := bstep (se 1 (by rfl) ⟨15891101, by rfl⟩ : syracuseStep 21188135 = 31782203) B31782203
theorem B5508647 : Blo 1630514 5508647 := bstep (se 1 (by rfl) ⟨4131485, by rfl⟩ : syracuseStep 5508647 = 8262971) B8262971
theorem B5508755 : Blo 1630514 5508755 := bstep (se 1 (by rfl) ⟨4131566, by rfl⟩ : syracuseStep 5508755 = 8263133) B8263133
theorem B6196925 : Blo 1630514 6196925 := bstep (se 3 (by rfl) ⟨1161923, by rfl⟩ : syracuseStep 6196925 = 2323847) B2323847
theorem B4648697 : Blo 1630514 4648697 := bstep (se 2 (by rfl) ⟨1743261, by rfl⟩ : syracuseStep 4648697 = 3486523) B3486523
theorem B5508971 : Blo 1630514 5508971 := bstep (se 1 (by rfl) ⟨4131728, by rfl⟩ : syracuseStep 5508971 = 8263457) B8263457
theorem B5509025 : Blo 1630514 5509025 := bstep (se 2 (by rfl) ⟨2065884, by rfl⟩ : syracuseStep 5509025 = 4131769) B4131769
theorem B14323727 : Blo 1630514 14323727 := bstep (se 1 (by rfl) ⟨10742795, by rfl⟩ : syracuseStep 14323727 = 21485591) B21485591
theorem B18583667 : Blo 1630514 18583667 := bstep (se 1 (by rfl) ⟨13937750, by rfl⟩ : syracuseStep 18583667 = 27875501) B27875501
theorem B15683969 : Blo 1630514 15683969 := bstep (se 2 (by rfl) ⟨5881488, by rfl⟩ : syracuseStep 15683969 = 11762977) B11762977
theorem B5509619 : Blo 1630514 5509619 := bstep (se 1 (by rfl) ⟨4132214, by rfl⟩ : syracuseStep 5509619 = 8264429) B8264429
theorem B2445833 : Blo 1630514 2445833 := bstep (se 2 (by rfl) ⟨917187, by rfl⟩ : syracuseStep 2445833 = 1834375) B1834375
theorem B31371785 : Blo 1630514 31371785 := bstep (se 2 (by rfl) ⟨11764419, by rfl⟩ : syracuseStep 31371785 = 23528839) B23528839
theorem B2445863 : Blo 1630514 2445863 := bstep (se 1 (by rfl) ⟨1834397, by rfl⟩ : syracuseStep 2445863 = 3668795) B3668795
theorem B2445947 : Blo 1630514 2445947 := bstep (se 1 (by rfl) ⟨1834460, by rfl⟩ : syracuseStep 2445947 = 3668921) B3668921
theorem B13226669 : Blo 1630514 13226669 := bstep (se 3 (by rfl) ⟨2480000, by rfl⟩ : syracuseStep 13226669 = 4960001) B4960001
theorem B2446073 : Blo 1630514 2446073 := bstep (se 2 (by rfl) ⟨917277, by rfl⟩ : syracuseStep 2446073 = 1834555) B1834555
theorem B61985587 : Blo 1630514 61985587 := bstep (se 1 (by rfl) ⟨46489190, by rfl⟩ : syracuseStep 61985587 = 92978381) B92978381
theorem B21484361 : Blo 1630514 21484361 := bstep (se 2 (by rfl) ⟨8056635, by rfl⟩ : syracuseStep 21484361 = 16113271) B16113271
theorem B2446175 : Blo 1630514 2446175 := bstep (se 1 (by rfl) ⟨1834631, by rfl⟩ : syracuseStep 2446175 = 3669263) B3669263
theorem B2446187 : Blo 1630514 2446187 := bstep (se 1 (by rfl) ⟨1834640, by rfl⟩ : syracuseStep 2446187 = 3669281) B3669281
theorem B2446415 : Blo 1630514 2446415 := bstep (se 1 (by rfl) ⟨1834811, by rfl⟩ : syracuseStep 2446415 = 3669623) B3669623
theorem B6198353 : Blo 1630514 6198353 := bstep (se 2 (by rfl) ⟨2324382, by rfl⟩ : syracuseStep 6198353 = 4648765) B4648765
theorem B8262809 : Blo 1630514 8262809 := bstep (se 2 (by rfl) ⟨3098553, by rfl⟩ : syracuseStep 8262809 = 6197107) B6197107
theorem B2446535 : Blo 1630514 2446535 := bstep (se 1 (by rfl) ⟨1834901, by rfl⟩ : syracuseStep 2446535 = 3669803) B3669803
theorem B1742023 : Blo 1630514 1742023 := bstep (se 1 (by rfl) ⟨1306517, by rfl⟩ : syracuseStep 1742023 = 2613035) B2613035
theorem B7943447 : Blo 1630514 7943447 := bstep (se 1 (by rfl) ⟨5957585, by rfl⟩ : syracuseStep 7943447 = 11915171) B11915171
theorem B2446697 : Blo 1630514 2446697 := bstep (se 2 (by rfl) ⟨917511, by rfl⟩ : syracuseStep 2446697 = 1835023) B1835023
theorem B2323819 : Blo 1630514 2323819 := bstep (se 1 (by rfl) ⟨1742864, by rfl⟩ : syracuseStep 2323819 = 3485729) B3485729
theorem B2446775 : Blo 1630514 2446775 := bstep (se 1 (by rfl) ⟨1835081, by rfl⟩ : syracuseStep 2446775 = 3670163) B3670163
theorem B2446811 : Blo 1630514 2446811 := bstep (se 1 (by rfl) ⟨1835108, by rfl⟩ : syracuseStep 2446811 = 3670217) B3670217
theorem B5584409 : Blo 1630514 5584409 := bstep (se 2 (by rfl) ⟨2094153, by rfl⟩ : syracuseStep 5584409 = 4188307) B4188307
theorem B2324047 : Blo 1630514 2324047 := bstep (se 1 (by rfl) ⟨1743035, by rfl⟩ : syracuseStep 2324047 = 3486071) B3486071
theorem B5224121 : Blo 1630514 5224121 := bstep (se 2 (by rfl) ⟨1959045, by rfl⟩ : syracuseStep 5224121 = 3918091) B3918091
theorem B15898427 : Blo 1630514 15898427 := bstep (se 1 (by rfl) ⟨11923820, by rfl⟩ : syracuseStep 15898427 = 23847641) B23847641
theorem B2447279 : Blo 1630514 2447279 := bstep (se 1 (by rfl) ⟨1835459, by rfl⟩ : syracuseStep 2447279 = 3670919) B3670919
theorem B11761595 : Blo 1630514 11761595 := bstep (se 1 (by rfl) ⟨8821196, by rfl⟩ : syracuseStep 11761595 = 17642393) B17642393
theorem B2791355 : Blo 1630514 2791355 := bstep (se 1 (by rfl) ⟨2093516, by rfl⟩ : syracuseStep 2791355 = 4187033) B4187033
theorem B2447369 : Blo 1630514 2447369 := bstep (se 2 (by rfl) ⟨917763, by rfl⟩ : syracuseStep 2447369 = 1835527) B1835527
theorem B2447399 : Blo 1630514 2447399 := bstep (se 1 (by rfl) ⟨1835549, by rfl⟩ : syracuseStep 2447399 = 3671099) B3671099
theorem B95344685 : Blo 1630514 95344685 := bstep (se 3 (by rfl) ⟨17877128, by rfl⟩ : syracuseStep 95344685 = 35754257) B35754257
theorem B12564557 : Blo 1630514 12564557 := bstep (se 3 (by rfl) ⟨2355854, by rfl⟩ : syracuseStep 12564557 = 4711709) B4711709
theorem B1652815 : Blo 1630514 1652815 := bstep (se 1 (by rfl) ⟨1239611, by rfl⟩ : syracuseStep 1652815 = 2479223) B2479223
theorem B2447483 : Blo 1630514 2447483 := bstep (se 1 (by rfl) ⟨1835612, by rfl⟩ : syracuseStep 2447483 = 3671225) B3671225
theorem B6191261 : Blo 1630514 6191261 := bstep (se 3 (by rfl) ⟨1160861, by rfl⟩ : syracuseStep 6191261 = 2321723) B2321723
theorem B6191275 : Blo 1630514 6191275 := bstep (se 1 (by rfl) ⟨4643456, by rfl⟩ : syracuseStep 6191275 = 9286913) B9286913
theorem B3225847 : Blo 1630514 3225847 := bstep (se 1 (by rfl) ⟨2419385, by rfl⟩ : syracuseStep 3225847 = 4838771) B4838771
theorem B2447609 : Blo 1630514 2447609 := bstep (se 2 (by rfl) ⟨917853, by rfl⟩ : syracuseStep 2447609 = 1835707) B1835707
theorem B15677783 : Blo 1630514 15677783 := bstep (se 1 (by rfl) ⟨11758337, by rfl⟩ : syracuseStep 15677783 = 23516675) B23516675
theorem B2447711 : Blo 1630514 2447711 := bstep (se 1 (by rfl) ⟨1835783, by rfl⟩ : syracuseStep 2447711 = 3671567) B3671567
theorem B2447723 : Blo 1630514 2447723 := bstep (se 1 (by rfl) ⟨1835792, by rfl⟩ : syracuseStep 2447723 = 3671585) B3671585
theorem B16963991 : Blo 1630514 16963991 := bstep (se 1 (by rfl) ⟨12722993, by rfl⟩ : syracuseStep 16963991 = 25445987) B25445987
theorem B6191579 : Blo 1630514 6191579 := bstep (se 1 (by rfl) ⟨4643684, by rfl⟩ : syracuseStep 6191579 = 9287369) B9287369
theorem B2480719 : Blo 1630514 2480719 := bstep (se 1 (by rfl) ⟨1860539, by rfl⟩ : syracuseStep 2480719 = 3721079) B3721079
theorem B2447951 : Blo 1630514 2447951 := bstep (se 1 (by rfl) ⟨1835963, by rfl⟩ : syracuseStep 2447951 = 3671927) B3671927
theorem B13933241 : Blo 1630514 13933241 := bstep (se 2 (by rfl) ⟨5224965, by rfl⟩ : syracuseStep 13933241 = 10449931) B10449931
theorem B2448071 : Blo 1630514 2448071 := bstep (se 1 (by rfl) ⟨1836053, by rfl⟩ : syracuseStep 2448071 = 3672107) B3672107
theorem B5503787 : Blo 1630514 5503787 := bstep (se 1 (by rfl) ⟨4127840, by rfl⟩ : syracuseStep 5503787 = 8255681) B8255681
theorem B8256329 : Blo 1630514 8256329 := bstep (se 2 (by rfl) ⟨3096123, by rfl⟩ : syracuseStep 8256329 = 6192247) B6192247
theorem B3668831 : Blo 1630514 3668831 := bstep (se 1 (by rfl) ⟨2751623, by rfl⟩ : syracuseStep 3668831 = 5503247) B5503247
theorem B2448233 : Blo 1630514 2448233 := bstep (se 2 (by rfl) ⟨918087, by rfl⟩ : syracuseStep 2448233 = 1836175) B1836175
theorem B3095471 : Blo 1630514 3095471 := bstep (se 1 (by rfl) ⟨2321603, by rfl⟩ : syracuseStep 3095471 = 4643207) B4643207
theorem B2448311 : Blo 1630514 2448311 := bstep (se 1 (by rfl) ⟨1836233, by rfl⟩ : syracuseStep 2448311 = 3672467) B3672467
theorem B5659579 : Blo 1630514 5659579 := bstep (se 1 (by rfl) ⟨4244684, by rfl⟩ : syracuseStep 5659579 = 8489369) B8489369
theorem B2448347 : Blo 1630514 2448347 := bstep (se 1 (by rfl) ⟨1836260, by rfl⟩ : syracuseStep 2448347 = 3672521) B3672521
theorem B3669011 : Blo 1630514 3669011 := bstep (se 1 (by rfl) ⟨2751758, by rfl⟩ : syracuseStep 3669011 = 5503517) B5503517
theorem B5504057 : Blo 1630514 5504057 := bstep (se 2 (by rfl) ⟨2064021, by rfl⟩ : syracuseStep 5504057 = 4128043) B4128043
theorem B6708395 : Blo 1630514 6708395 := bstep (se 1 (by rfl) ⟨5031296, by rfl⟩ : syracuseStep 6708395 = 10062593) B10062593
theorem B1653959 : Blo 1630514 1653959 := bstep (se 1 (by rfl) ⟨1240469, by rfl⟩ : syracuseStep 1653959 = 2480939) B2480939
theorem B3669353 : Blo 1630514 3669353 := bstep (se 2 (by rfl) ⟨1376007, by rfl⟩ : syracuseStep 3669353 = 2752015) B2752015
theorem B5504381 : Blo 1630514 5504381 := bstep (se 3 (by rfl) ⟨1032071, by rfl⟩ : syracuseStep 5504381 = 2064143) B2064143
theorem B4185473 : Blo 1630514 4185473 := bstep (se 2 (by rfl) ⟨1569552, by rfl⟩ : syracuseStep 4185473 = 3139105) B3139105
theorem B2751887 : Blo 1630514 2751887 := bstep (se 1 (by rfl) ⟨2063915, by rfl⟩ : syracuseStep 2751887 = 4127831) B4127831
theorem B20913551 : Blo 1630514 20913551 := bstep (se 1 (by rfl) ⟨15685163, by rfl⟩ : syracuseStep 20913551 = 31370327) B31370327
theorem B12385709 : Blo 1630514 12385709 := bstep (se 3 (by rfl) ⟨2322320, by rfl⟩ : syracuseStep 12385709 = 4644641) B4644641
theorem B3095995 : Blo 1630514 3095995 := bstep (se 1 (by rfl) ⟨2321996, by rfl⟩ : syracuseStep 3095995 = 4643993) B4643993
theorem B181140941 : Blo 1630514 181140941 := bstep (se 3 (by rfl) ⟨33963926, by rfl⟩ : syracuseStep 181140941 = 67927853) B67927853
theorem B12393971 : Blo 1630514 12393971 := bstep (se 1 (by rfl) ⟨9295478, by rfl⟩ : syracuseStep 12393971 = 18590957) B18590957
theorem B4644391 : Blo 1630514 4644391 := bstep (se 1 (by rfl) ⟨3483293, by rfl⟩ : syracuseStep 4644391 = 6966587) B6966587
theorem B4644449 : Blo 1630514 4644449 := bstep (se 2 (by rfl) ⟨1741668, by rfl⟩ : syracuseStep 4644449 = 3483337) B3483337
theorem B2752123 : Blo 1630514 2752123 := bstep (se 1 (by rfl) ⟨2064092, by rfl⟩ : syracuseStep 2752123 = 4128185) B4128185
theorem B5504651 : Blo 1630514 5504651 := bstep (se 1 (by rfl) ⟨4128488, by rfl⟩ : syracuseStep 5504651 = 8256977) B8256977
theorem B11321147 : Blo 1630514 11321147 := bstep (se 1 (by rfl) ⟨8490860, by rfl⟩ : syracuseStep 11321147 = 16981721) B16981721
theorem B3096481 : Blo 1630514 3096481 := bstep (se 2 (by rfl) ⟨1161180, by rfl⟩ : syracuseStep 3096481 = 2322361) B2322361
theorem B3669947 : Blo 1630514 3669947 := bstep (se 1 (by rfl) ⟨2752460, by rfl⟩ : syracuseStep 3669947 = 5504921) B5504921
theorem B5505083 : Blo 1630514 5505083 := bstep (se 1 (by rfl) ⟨4128812, by rfl⟩ : syracuseStep 5505083 = 8257625) B8257625
theorem B5505353 : Blo 1630514 5505353 := bstep (se 2 (by rfl) ⟨2064507, by rfl⟩ : syracuseStep 5505353 = 4129015) B4129015
theorem B4301129 : Blo 1630514 4301129 := bstep (se 2 (by rfl) ⟨1612923, by rfl⟩ : syracuseStep 4301129 = 3225847) B3225847
theorem B1630555 : Blo 1630514 1630555 := bstep (se 1 (by rfl) ⟨1222916, by rfl⟩ : syracuseStep 1630555 = 2445833) B2445833
theorem B2752859 : Blo 1630514 2752859 := bstep (se 1 (by rfl) ⟨2064644, by rfl⟩ : syracuseStep 2752859 = 4129289) B4129289
theorem B20914523 : Blo 1630514 20914523 := bstep (se 1 (by rfl) ⟨15685892, by rfl⟩ : syracuseStep 20914523 = 31371785) B31371785
theorem B3670379 : Blo 1630514 3670379 := bstep (se 1 (by rfl) ⟨2752784, by rfl⟩ : syracuseStep 3670379 = 5505569) B5505569
theorem B1630575 : Blo 1630514 1630575 := bstep (se 1 (by rfl) ⟨1222931, by rfl⟩ : syracuseStep 1630575 = 2445863) B2445863
theorem B2752879 : Blo 1630514 2752879 := bstep (se 1 (by rfl) ⟨2064659, by rfl⟩ : syracuseStep 2752879 = 4129319) B4129319
theorem B8815013 : Blo 1630514 8815013 := bstep (se 4 (by rfl) ⟨826407, by rfl⟩ : syracuseStep 8815013 = 1652815) B1652815
theorem B1630631 : Blo 1630514 1630631 := bstep (se 1 (by rfl) ⟨1222973, by rfl⟩ : syracuseStep 1630631 = 2445947) B2445947
theorem B1630715 : Blo 1630514 1630715 := bstep (se 1 (by rfl) ⟨1223036, by rfl⟩ : syracuseStep 1630715 = 2446073) B2446073
theorem B3670523 : Blo 1630514 3670523 := bstep (se 1 (by rfl) ⟨2752892, by rfl⟩ : syracuseStep 3670523 = 5505785) B5505785
theorem B1630783 : Blo 1630514 1630783 := bstep (se 1 (by rfl) ⟨1223087, by rfl⟩ : syracuseStep 1630783 = 2446175) B2446175
theorem B1630791 : Blo 1630514 1630791 := bstep (se 1 (by rfl) ⟨1223093, by rfl⟩ : syracuseStep 1630791 = 2446187) B2446187
theorem B2753095 : Blo 1630514 2753095 := bstep (se 1 (by rfl) ⟨2064821, by rfl⟩ : syracuseStep 2753095 = 4129643) B4129643
theorem B3670649 : Blo 1630514 3670649 := bstep (se 2 (by rfl) ⟨1376493, by rfl⟩ : syracuseStep 3670649 = 2752987) B2752987
theorem B4129451 : Blo 1630514 4129451 := bstep (se 1 (by rfl) ⟨3097088, by rfl⟩ : syracuseStep 4129451 = 6194177) B6194177
theorem B3670703 : Blo 1630514 3670703 := bstep (se 1 (by rfl) ⟨2753027, by rfl⟩ : syracuseStep 3670703 = 5506055) B5506055
theorem B3097271 : Blo 1630514 3097271 := bstep (se 1 (by rfl) ⟨2322953, by rfl⟩ : syracuseStep 3097271 = 4645907) B4645907
theorem B1630943 : Blo 1630514 1630943 := bstep (se 1 (by rfl) ⟨1223207, by rfl⟩ : syracuseStep 1630943 = 2446415) B2446415
theorem B1835743 : Blo 1630514 1835743 := bstep (se 1 (by rfl) ⟨1376807, by rfl⟩ : syracuseStep 1835743 = 2753615) B2753615
theorem B3670775 : Blo 1630514 3670775 := bstep (se 1 (by rfl) ⟨2753081, by rfl⟩ : syracuseStep 3670775 = 5506163) B5506163
theorem B1631023 : Blo 1630514 1631023 := bstep (se 1 (by rfl) ⟨1223267, by rfl⟩ : syracuseStep 1631023 = 2446535) B2446535
theorem B12387167 : Blo 1630514 12387167 := bstep (se 1 (by rfl) ⟨9290375, by rfl⟩ : syracuseStep 12387167 = 18580751) B18580751
theorem B1631131 : Blo 1630514 1631131 := bstep (se 1 (by rfl) ⟨1223348, by rfl⟩ : syracuseStep 1631131 = 2446697) B2446697
theorem B3670955 : Blo 1630514 3670955 := bstep (se 1 (by rfl) ⟨2753216, by rfl⟩ : syracuseStep 3670955 = 5506433) B5506433
theorem B1631183 : Blo 1630514 1631183 := bstep (se 1 (by rfl) ⟨1223387, by rfl⟩ : syracuseStep 1631183 = 2446775) B2446775
theorem B1631207 : Blo 1630514 1631207 := bstep (se 1 (by rfl) ⟨1223405, by rfl⟩ : syracuseStep 1631207 = 2446811) B2446811
theorem B2753527 : Blo 1630514 2753527 := bstep (se 1 (by rfl) ⟨2065145, by rfl⟩ : syracuseStep 2753527 = 4130291) B4130291
theorem B3482747 : Blo 1630514 3482747 := bstep (se 1 (by rfl) ⟨2612060, by rfl⟩ : syracuseStep 3482747 = 5224121) B5224121
theorem B8258759 : Blo 1630514 8258759 := bstep (se 1 (by rfl) ⟨6194069, by rfl⟩ : syracuseStep 8258759 = 12388139) B12388139
theorem B7546105 : Blo 1630514 7546105 := bstep (se 2 (by rfl) ⟨2829789, by rfl⟩ : syracuseStep 7546105 = 5659579) B5659579
theorem B1631519 : Blo 1630514 1631519 := bstep (se 1 (by rfl) ⟨1223639, by rfl⟩ : syracuseStep 1631519 = 2447279) B2447279
theorem B1836319 : Blo 1630514 1836319 := bstep (se 1 (by rfl) ⟨1377239, by rfl⟩ : syracuseStep 1836319 = 2754479) B2754479
theorem B7841063 : Blo 1630514 7841063 := bstep (se 1 (by rfl) ⟨5880797, by rfl⟩ : syracuseStep 7841063 = 11761595) B11761595
theorem B2753831 : Blo 1630514 2753831 := bstep (se 1 (by rfl) ⟨2065373, by rfl⟩ : syracuseStep 2753831 = 4130747) B4130747
theorem B1631579 : Blo 1630514 1631579 := bstep (se 1 (by rfl) ⟨1223684, by rfl⟩ : syracuseStep 1631579 = 2447369) B2447369
theorem B8258921 : Blo 1630514 8258921 := bstep (se 2 (by rfl) ⟨3097095, by rfl⟩ : syracuseStep 8258921 = 6194191) B6194191
theorem B1631599 : Blo 1630514 1631599 := bstep (se 1 (by rfl) ⟨1223699, by rfl⟩ : syracuseStep 1631599 = 2447399) B2447399
theorem B63563123 : Blo 1630514 63563123 := bstep (se 1 (by rfl) ⟨47672342, by rfl⟩ : syracuseStep 63563123 = 95344685) B95344685
theorem B1631655 : Blo 1630514 1631655 := bstep (se 1 (by rfl) ⟨1223741, by rfl⟩ : syracuseStep 1631655 = 2447483) B2447483
theorem B3671495 : Blo 1630514 3671495 := bstep (se 1 (by rfl) ⟨2753621, by rfl⟩ : syracuseStep 3671495 = 5507243) B5507243
theorem B1631739 : Blo 1630514 1631739 := bstep (se 1 (by rfl) ⟨1223804, by rfl⟩ : syracuseStep 1631739 = 2447609) B2447609
theorem B2065915 : Blo 1630514 2065915 := bstep (se 1 (by rfl) ⟨1549436, by rfl⟩ : syracuseStep 2065915 = 3098873) B3098873
theorem B4130311 : Blo 1630514 4130311 := bstep (se 1 (by rfl) ⟨3097733, by rfl⟩ : syracuseStep 4130311 = 6195467) B6195467
theorem B1631807 : Blo 1630514 1631807 := bstep (se 1 (by rfl) ⟨1223855, by rfl⟩ : syracuseStep 1631807 = 2447711) B2447711
theorem B1631815 : Blo 1630514 1631815 := bstep (se 1 (by rfl) ⟨1223861, by rfl⟩ : syracuseStep 1631815 = 2447723) B2447723
theorem B1631967 : Blo 1630514 1631967 := bstep (se 1 (by rfl) ⟨1223975, by rfl⟩ : syracuseStep 1631967 = 2447951) B2447951
theorem B2066143 : Blo 1630514 2066143 := bstep (se 1 (by rfl) ⟨1549607, by rfl⟩ : syracuseStep 2066143 = 3099215) B3099215
theorem B2754283 : Blo 1630514 2754283 := bstep (se 1 (by rfl) ⟨2065712, by rfl⟩ : syracuseStep 2754283 = 4131425) B4131425
theorem B3671855 : Blo 1630514 3671855 := bstep (se 1 (by rfl) ⟨2753891, by rfl⟩ : syracuseStep 3671855 = 5507783) B5507783
theorem B1632047 : Blo 1630514 1632047 := bstep (se 1 (by rfl) ⟨1224035, by rfl⟩ : syracuseStep 1632047 = 2448071) B2448071
theorem B4130615 : Blo 1630514 4130615 := bstep (se 1 (by rfl) ⟨3097961, by rfl⟩ : syracuseStep 4130615 = 6195923) B6195923
theorem B3098425 : Blo 1630514 3098425 := bstep (se 2 (by rfl) ⟨1161909, by rfl⟩ : syracuseStep 3098425 = 2323819) B2323819
theorem B9922385 : Blo 1630514 9922385 := bstep (se 2 (by rfl) ⟨3720894, by rfl⟩ : syracuseStep 9922385 = 7441789) B7441789
theorem B1632155 : Blo 1630514 1632155 := bstep (se 1 (by rfl) ⟨1224116, by rfl⟩ : syracuseStep 1632155 = 2448233) B2448233
theorem B1632207 : Blo 1630514 1632207 := bstep (se 1 (by rfl) ⟨1224155, by rfl⟩ : syracuseStep 1632207 = 2448311) B2448311
theorem B1632231 : Blo 1630514 1632231 := bstep (se 1 (by rfl) ⟨1224173, by rfl⟩ : syracuseStep 1632231 = 2448347) B2448347
theorem B3098729 : Blo 1630514 3098729 := bstep (se 2 (by rfl) ⟨1162023, by rfl⟩ : syracuseStep 3098729 = 2324047) B2324047
theorem B30189725 : Blo 1630514 30189725 := bstep (se 3 (by rfl) ⟨5660573, by rfl⟩ : syracuseStep 30189725 = 11321147) B11321147
theorem B120760627 : Blo 1630514 120760627 := bstep (se 1 (by rfl) ⟨90570470, by rfl⟩ : syracuseStep 120760627 = 181140941) B181140941
theorem B14125423 : Blo 1630514 14125423 := bstep (se 1 (by rfl) ⟨10594067, by rfl⟩ : syracuseStep 14125423 = 21188135) B21188135
theorem B3672431 : Blo 1630514 3672431 := bstep (se 1 (by rfl) ⟨2754323, by rfl⟩ : syracuseStep 3672431 = 5508647) B5508647
theorem B3672503 : Blo 1630514 3672503 := bstep (se 1 (by rfl) ⟨2754377, by rfl⟩ : syracuseStep 3672503 = 5508755) B5508755
theorem B4131283 : Blo 1630514 4131283 := bstep (se 1 (by rfl) ⟨3098462, by rfl⟩ : syracuseStep 4131283 = 6196925) B6196925
theorem B3099131 : Blo 1630514 3099131 := bstep (se 1 (by rfl) ⟨2324348, by rfl⟩ : syracuseStep 3099131 = 4648697) B4648697
theorem B3672647 : Blo 1630514 3672647 := bstep (se 1 (by rfl) ⟨2754485, by rfl⟩ : syracuseStep 3672647 = 5508971) B5508971
theorem B3672683 : Blo 1630514 3672683 := bstep (se 1 (by rfl) ⟨2754512, by rfl⟩ : syracuseStep 3672683 = 5509025) B5509025
theorem B12389111 : Blo 1630514 12389111 := bstep (se 1 (by rfl) ⟨9291833, by rfl⟩ : syracuseStep 12389111 = 18583667) B18583667
theorem B10455979 : Blo 1630514 10455979 := bstep (se 1 (by rfl) ⟨7841984, by rfl⟩ : syracuseStep 10455979 = 15683969) B15683969
theorem B3673079 : Blo 1630514 3673079 := bstep (se 1 (by rfl) ⟨2754809, by rfl⟩ : syracuseStep 3673079 = 5509619) B5509619
theorem B3484711 : Blo 1630514 3484711 := bstep (se 1 (by rfl) ⟨2613533, by rfl⟩ : syracuseStep 3484711 = 5227067) B5227067
theorem B15674435 : Blo 1630514 15674435 := bstep (se 1 (by rfl) ⟨11755826, by rfl⟩ : syracuseStep 15674435 = 23511653) B23511653
theorem B8817779 : Blo 1630514 8817779 := bstep (se 1 (by rfl) ⟨6613334, by rfl⟩ : syracuseStep 8817779 = 13226669) B13226669
theorem B4410557 : Blo 1630514 4410557 := bstep (se 3 (by rfl) ⟨826979, by rfl⟩ : syracuseStep 4410557 = 1653959) B1653959
theorem B4132073 : Blo 1630514 4132073 := bstep (se 2 (by rfl) ⟨1549527, by rfl⟩ : syracuseStep 4132073 = 3099055) B3099055
theorem B10448189 : Blo 1630514 10448189 := bstep (se 3 (by rfl) ⟨1959035, by rfl⟩ : syracuseStep 10448189 = 3918071) B3918071
theorem B11169143 : Blo 1630514 11169143 := bstep (se 1 (by rfl) ⟨8376857, by rfl⟩ : syracuseStep 11169143 = 16753715) B16753715
theorem B4132235 : Blo 1630514 4132235 := bstep (se 1 (by rfl) ⟨3099176, by rfl⟩ : syracuseStep 4132235 = 6198353) B6198353
theorem B5508539 : Blo 1630514 5508539 := bstep (se 1 (by rfl) ⟨4131404, by rfl⟩ : syracuseStep 5508539 = 8262809) B8262809
theorem B5295631 : Blo 1630514 5295631 := bstep (se 1 (by rfl) ⟨3971723, by rfl⟩ : syracuseStep 5295631 = 7943447) B7943447
theorem B11161261 : Blo 1630514 11161261 := bstep (se 3 (by rfl) ⟨2092736, by rfl⟩ : syracuseStep 11161261 = 4185473) B4185473
theorem B3722939 : Blo 1630514 3722939 := bstep (se 1 (by rfl) ⟨2792204, by rfl⟩ : syracuseStep 3722939 = 5584409) B5584409
theorem B8941373 : Blo 1630514 8941373 := bstep (se 3 (by rfl) ⟨1676507, by rfl⟩ : syracuseStep 8941373 = 3353015) B3353015
theorem B13938641 : Blo 1630514 13938641 := bstep (se 2 (by rfl) ⟨5226990, by rfl⟩ : syracuseStep 13938641 = 10453981) B10453981
theorem B5877785 : Blo 1630514 5877785 := bstep (se 2 (by rfl) ⟨2204169, by rfl⟩ : syracuseStep 5877785 = 4408339) B4408339
theorem B8376371 : Blo 1630514 8376371 := bstep (se 1 (by rfl) ⟨6282278, by rfl⟩ : syracuseStep 8376371 = 12564557) B12564557
theorem B2322697 : Blo 1630514 2322697 := bstep (se 2 (by rfl) ⟨871011, by rfl⟩ : syracuseStep 2322697 = 1742023) B1742023
theorem B11309327 : Blo 1630514 11309327 := bstep (se 1 (by rfl) ⟨8481995, by rfl⟩ : syracuseStep 11309327 = 16963991) B16963991
theorem B2445887 : Blo 1630514 2445887 := bstep (se 1 (by rfl) ⟨1834415, by rfl⟩ : syracuseStep 2445887 = 3668831) B3668831
theorem B8368811 : Blo 1630514 8368811 := bstep (se 1 (by rfl) ⟨6276608, by rfl⟩ : syracuseStep 8368811 = 12553217) B12553217
theorem B2446007 : Blo 1630514 2446007 := bstep (se 1 (by rfl) ⟨1834505, by rfl⟩ : syracuseStep 2446007 = 3669011) B3669011
theorem B2355895 : Blo 1630514 2355895 := bstep (se 1 (by rfl) ⟨1766921, by rfl⟩ : syracuseStep 2355895 = 3533843) B3533843
theorem B35263325 : Blo 1630514 35263325 := bstep (se 3 (by rfl) ⟨6611873, by rfl⟩ : syracuseStep 35263325 = 13223747) B13223747
theorem B57291629 : Blo 1630514 57291629 := bstep (se 3 (by rfl) ⟨10742180, by rfl⟩ : syracuseStep 57291629 = 21484361) B21484361
theorem B2446235 : Blo 1630514 2446235 := bstep (se 1 (by rfl) ⟨1834676, by rfl⟩ : syracuseStep 2446235 = 3669353) B3669353
theorem B23524343 : Blo 1630514 23524343 := bstep (se 1 (by rfl) ⟨17643257, by rfl⟩ : syracuseStep 23524343 = 35286515) B35286515
theorem B8262647 : Blo 1630514 8262647 := bstep (se 1 (by rfl) ⟨6196985, by rfl⟩ : syracuseStep 8262647 = 12393971) B12393971
theorem B7443613 : Blo 1630514 7443613 := bstep (se 3 (by rfl) ⟨1395677, by rfl⟩ : syracuseStep 7443613 = 2791355) B2791355
theorem B2446631 : Blo 1630514 2446631 := bstep (se 1 (by rfl) ⟨1834973, by rfl⟩ : syracuseStep 2446631 = 3669947) B3669947
theorem B2446715 : Blo 1630514 2446715 := bstep (se 1 (by rfl) ⟨1835036, by rfl⟩ : syracuseStep 2446715 = 3670073) B3670073
theorem B38196605 : Blo 1630514 38196605 := bstep (se 3 (by rfl) ⟨7161863, by rfl⟩ : syracuseStep 38196605 = 14323727) B14323727
theorem B2446841 : Blo 1630514 2446841 := bstep (se 2 (by rfl) ⟨917565, by rfl⟩ : syracuseStep 2446841 = 1835131) B1835131
theorem B8255033 : Blo 1630514 8255033 := bstep (se 2 (by rfl) ⟨3095637, by rfl⟩ : syracuseStep 8255033 = 6191275) B6191275
theorem B2446943 : Blo 1630514 2446943 := bstep (se 1 (by rfl) ⟨1835207, by rfl⟩ : syracuseStep 2446943 = 3670415) B3670415
theorem B2447159 : Blo 1630514 2447159 := bstep (se 1 (by rfl) ⟨1835369, by rfl⟩ : syracuseStep 2447159 = 3670739) B3670739
theorem B3307625 : Blo 1630514 3307625 := bstep (se 2 (by rfl) ⟨1240359, by rfl⟩ : syracuseStep 3307625 = 2480719) B2480719
theorem B2447465 : Blo 1630514 2447465 := bstep (se 2 (by rfl) ⟨917799, by rfl⟩ : syracuseStep 2447465 = 1835599) B1835599
theorem B4643183 : Blo 1630514 4643183 := bstep (se 1 (by rfl) ⟨3482387, by rfl⟩ : syracuseStep 4643183 = 6964775) B6964775
theorem B82647449 : Blo 1630514 82647449 := bstep (se 2 (by rfl) ⟨30992793, by rfl⟩ : syracuseStep 82647449 = 61985587) B61985587
theorem B2939303 : Blo 1630514 2939303 := bstep (se 1 (by rfl) ⟨2204477, by rfl⟩ : syracuseStep 2939303 = 4408955) B4408955
theorem B2447783 : Blo 1630514 2447783 := bstep (se 1 (by rfl) ⟨1835837, by rfl⟩ : syracuseStep 2447783 = 3671675) B3671675
theorem B2447867 : Blo 1630514 2447867 := bstep (se 1 (by rfl) ⟨1835900, by rfl⟩ : syracuseStep 2447867 = 3671801) B3671801
theorem B10598951 : Blo 1630514 10598951 := bstep (se 1 (by rfl) ⟨7949213, by rfl⟩ : syracuseStep 10598951 = 15898427) B15898427
theorem B12392999 : Blo 1630514 12392999 := bstep (se 1 (by rfl) ⟨9294749, by rfl⟩ : syracuseStep 12392999 = 18589499) B18589499
theorem B2447993 : Blo 1630514 2447993 := bstep (se 2 (by rfl) ⟨917997, by rfl⟩ : syracuseStep 2447993 = 1835995) B1835995
theorem B2448047 : Blo 1630514 2448047 := bstep (se 1 (by rfl) ⟨1836035, by rfl⟩ : syracuseStep 2448047 = 3672071) B3672071
theorem B2448095 : Blo 1630514 2448095 := bstep (se 1 (by rfl) ⟨1836071, by rfl⟩ : syracuseStep 2448095 = 3672143) B3672143
theorem B4127507 : Blo 1630514 4127507 := bstep (se 1 (by rfl) ⟨3095630, by rfl⟩ : syracuseStep 4127507 = 6191261) B6191261
theorem B10451855 : Blo 1630514 10451855 := bstep (se 1 (by rfl) ⟨7838891, by rfl⟩ : syracuseStep 10451855 = 15677783) B15677783
theorem B8264591 : Blo 1630514 8264591 := bstep (se 1 (by rfl) ⟨6198443, by rfl⟩ : syracuseStep 8264591 = 12396887) B12396887
theorem B4127719 : Blo 1630514 4127719 := bstep (se 1 (by rfl) ⟨3095789, by rfl⟩ : syracuseStep 4127719 = 6191579) B6191579
theorem B2448359 : Blo 1630514 2448359 := bstep (se 1 (by rfl) ⟨1836269, by rfl⟩ : syracuseStep 2448359 = 3672539) B3672539
theorem B2792423 : Blo 1630514 2792423 := bstep (se 1 (by rfl) ⟨2094317, by rfl⟩ : syracuseStep 2792423 = 4188635) B4188635
theorem B13933619 : Blo 1630514 13933619 := bstep (se 1 (by rfl) ⟨10450214, by rfl⟩ : syracuseStep 13933619 = 20900429) B20900429
theorem B9288827 : Blo 1630514 9288827 := bstep (se 1 (by rfl) ⟨6966620, by rfl⟩ : syracuseStep 9288827 = 13933241) B13933241
theorem B4709515 : Blo 1630514 4709515 := bstep (se 1 (by rfl) ⟨3532136, by rfl⟩ : syracuseStep 4709515 = 7064273) B7064273
theorem B3669191 : Blo 1630514 3669191 := bstep (se 1 (by rfl) ⟨2751893, by rfl⟩ : syracuseStep 3669191 = 5503787) B5503787
theorem B5504219 : Blo 1630514 5504219 := bstep (se 1 (by rfl) ⟨4128164, by rfl⟩ : syracuseStep 5504219 = 8256329) B8256329
theorem B13941989 : Blo 1630514 13941989 := bstep (se 4 (by rfl) ⟨1307061, by rfl⟩ : syracuseStep 13941989 = 2614123) B2614123
theorem B2448617 : Blo 1630514 2448617 := bstep (se 2 (by rfl) ⟨918231, by rfl⟩ : syracuseStep 2448617 = 1836463) B1836463
theorem B4127993 : Blo 1630514 4127993 := bstep (se 2 (by rfl) ⟨1547997, by rfl⟩ : syracuseStep 4127993 = 3095995) B3095995
theorem B2063647 : Blo 1630514 2063647 := bstep (se 1 (by rfl) ⟨1547735, by rfl⟩ : syracuseStep 2063647 = 3095471) B3095471
theorem B2448671 : Blo 1630514 2448671 := bstep (se 1 (by rfl) ⟨1836503, by rfl⟩ : syracuseStep 2448671 = 3673007) B3673007
theorem B3669371 : Blo 1630514 3669371 := bstep (se 1 (by rfl) ⟨2752028, by rfl⟩ : syracuseStep 3669371 = 5504057) B5504057
theorem B2940283 : Blo 1630514 2940283 := bstep (se 1 (by rfl) ⟨2205212, by rfl⟩ : syracuseStep 2940283 = 4410425) B4410425
theorem B6192521 : Blo 1630514 6192521 := bstep (se 2 (by rfl) ⟨2322195, by rfl⟩ : syracuseStep 6192521 = 4644391) B4644391
theorem B4472263 : Blo 1630514 4472263 := bstep (se 1 (by rfl) ⟨3354197, by rfl⟩ : syracuseStep 4472263 = 6708395) B6708395
theorem B3669497 : Blo 1630514 3669497 := bstep (se 2 (by rfl) ⟨1376061, by rfl⟩ : syracuseStep 3669497 = 2752123) B2752123
theorem B6970961 : Blo 1630514 6970961 := bstep (se 2 (by rfl) ⟨2614110, by rfl⟩ : syracuseStep 6970961 = 5228221) B5228221
theorem B3669587 : Blo 1630514 3669587 := bstep (se 1 (by rfl) ⟨2752190, by rfl⟩ : syracuseStep 3669587 = 5504381) B5504381
theorem B1834591 : Blo 1630514 1834591 := bstep (se 1 (by rfl) ⟨1375943, by rfl⟩ : syracuseStep 1834591 = 2751887) B2751887
theorem B13942367 : Blo 1630514 13942367 := bstep (se 1 (by rfl) ⟨10456775, by rfl⟩ : syracuseStep 13942367 = 20913551) B20913551
theorem B8257139 : Blo 1630514 8257139 := bstep (se 1 (by rfl) ⟨6192854, by rfl⟩ : syracuseStep 8257139 = 12385709) B12385709
theorem B3096299 : Blo 1630514 3096299 := bstep (se 1 (by rfl) ⟨2322224, by rfl⟩ : syracuseStep 3096299 = 4644449) B4644449
theorem B3669767 : Blo 1630514 3669767 := bstep (se 1 (by rfl) ⟨2752325, by rfl⟩ : syracuseStep 3669767 = 5504651) B5504651
theorem B4644665 : Blo 1630514 4644665 := bstep (se 2 (by rfl) ⟨1741749, by rfl⟩ : syracuseStep 4644665 = 3483499) B3483499
theorem B4128641 : Blo 1630514 4128641 := bstep (se 2 (by rfl) ⟨1548240, by rfl⟩ : syracuseStep 4128641 = 3096481) B3096481
theorem B3670055 : Blo 1630514 3670055 := bstep (se 1 (by rfl) ⟨2752541, by rfl⟩ : syracuseStep 3670055 = 5505083) B5505083
theorem B3670235 : Blo 1630514 3670235 := bstep (se 1 (by rfl) ⟨2752676, by rfl⟩ : syracuseStep 3670235 = 5505353) B5505353
theorem B2867419 : Blo 1630514 2867419 := bstep (se 1 (by rfl) ⟨2150564, by rfl⟩ : syracuseStep 2867419 = 4301129) B4301129
theorem B1835239 : Blo 1630514 1835239 := bstep (se 1 (by rfl) ⟨1376429, by rfl⟩ : syracuseStep 1835239 = 2752859) B2752859
theorem B13943015 : Blo 1630514 13943015 := bstep (se 1 (by rfl) ⟨10457261, by rfl⟩ : syracuseStep 13943015 = 20914523) B20914523
theorem B3096929 : Blo 1630514 3096929 := bstep (se 2 (by rfl) ⟨1161348, by rfl⟩ : syracuseStep 3096929 = 2322697) B2322697
theorem B1630591 : Blo 1630514 1630591 := bstep (se 1 (by rfl) ⟨1222943, by rfl⟩ : syracuseStep 1630591 = 2445887) B2445887
theorem B161014169 : Blo 1630514 161014169 := bstep (se 2 (by rfl) ⟨60380313, by rfl⟩ : syracuseStep 161014169 = 120760627) B120760627
theorem B5579207 : Blo 1630514 5579207 := bstep (se 1 (by rfl) ⟨4184405, by rfl⟩ : syracuseStep 5579207 = 8368811) B8368811
theorem B2752967 : Blo 1630514 2752967 := bstep (se 1 (by rfl) ⟨2064725, by rfl⟩ : syracuseStep 2752967 = 4129451) B4129451
theorem B1630671 : Blo 1630514 1630671 := bstep (se 1 (by rfl) ⟨1223003, by rfl⟩ : syracuseStep 1630671 = 2446007) B2446007
theorem B2064847 : Blo 1630514 2064847 := bstep (se 1 (by rfl) ⟨1548635, by rfl⟩ : syracuseStep 2064847 = 3097271) B3097271
theorem B18833897 : Blo 1630514 18833897 := bstep (se 2 (by rfl) ⟨7062711, by rfl⟩ : syracuseStep 18833897 = 14125423) B14125423
theorem B3670505 : Blo 1630514 3670505 := bstep (se 2 (by rfl) ⟨1376439, by rfl⟩ : syracuseStep 3670505 = 2752879) B2752879
theorem B8258111 : Blo 1630514 8258111 := bstep (se 1 (by rfl) ⟨6193583, by rfl⟩ : syracuseStep 8258111 = 12387167) B12387167
theorem B1630823 : Blo 1630514 1630823 := bstep (se 1 (by rfl) ⟨1223117, by rfl⟩ : syracuseStep 1630823 = 2446235) B2446235
theorem B3670793 : Blo 1630514 3670793 := bstep (se 2 (by rfl) ⟨1376547, by rfl⟩ : syracuseStep 3670793 = 2753095) B2753095
theorem B5505839 : Blo 1630514 5505839 := bstep (se 1 (by rfl) ⟨4129379, by rfl⟩ : syracuseStep 5505839 = 8258759) B8258759
theorem B1631087 : Blo 1630514 1631087 := bstep (se 1 (by rfl) ⟨1223315, by rfl⟩ : syracuseStep 1631087 = 2446631) B2446631
theorem B5227375 : Blo 1630514 5227375 := bstep (se 1 (by rfl) ⟨3920531, by rfl⟩ : syracuseStep 5227375 = 7841063) B7841063
theorem B1835887 : Blo 1630514 1835887 := bstep (se 1 (by rfl) ⟨1376915, by rfl⟩ : syracuseStep 1835887 = 2753831) B2753831
theorem B5505947 : Blo 1630514 5505947 := bstep (se 1 (by rfl) ⟨4129460, by rfl⟩ : syracuseStep 5505947 = 8258921) B8258921
theorem B1631143 : Blo 1630514 1631143 := bstep (se 1 (by rfl) ⟨1223357, by rfl⟩ : syracuseStep 1631143 = 2446715) B2446715
theorem B1631227 : Blo 1630514 1631227 := bstep (se 1 (by rfl) ⟨1223420, by rfl⟩ : syracuseStep 1631227 = 2446841) B2446841
theorem B1631295 : Blo 1630514 1631295 := bstep (se 1 (by rfl) ⟨1223471, by rfl⟩ : syracuseStep 1631295 = 2446943) B2446943
theorem B1631439 : Blo 1630514 1631439 := bstep (se 1 (by rfl) ⟨1223579, by rfl⟩ : syracuseStep 1631439 = 2447159) B2447159
theorem B2753743 : Blo 1630514 2753743 := bstep (se 1 (by rfl) ⟨2065307, by rfl⟩ : syracuseStep 2753743 = 4130615) B4130615
theorem B3671369 : Blo 1630514 3671369 := bstep (se 2 (by rfl) ⟨1376763, by rfl⟩ : syracuseStep 3671369 = 2753527) B2753527
theorem B2205083 : Blo 1630514 2205083 := bstep (se 1 (by rfl) ⟨1653812, by rfl⟩ : syracuseStep 2205083 = 3307625) B3307625
theorem B1631643 : Blo 1630514 1631643 := bstep (se 1 (by rfl) ⟨1223732, by rfl⟩ : syracuseStep 1631643 = 2447465) B2447465
theorem B2065819 : Blo 1630514 2065819 := bstep (se 1 (by rfl) ⟨1549364, by rfl⟩ : syracuseStep 2065819 = 3098729) B3098729
theorem B1959535 : Blo 1630514 1959535 := bstep (se 1 (by rfl) ⟨1469651, by rfl⟩ : syracuseStep 1959535 = 2939303) B2939303
theorem B1631855 : Blo 1630514 1631855 := bstep (se 1 (by rfl) ⟨1223891, by rfl⟩ : syracuseStep 1631855 = 2447783) B2447783
theorem B1631911 : Blo 1630514 1631911 := bstep (se 1 (by rfl) ⟨1223933, by rfl⟩ : syracuseStep 1631911 = 2447867) B2447867
theorem B2066087 : Blo 1630514 2066087 := bstep (se 1 (by rfl) ⟨1549565, by rfl⟩ : syracuseStep 2066087 = 3099131) B3099131
theorem B1631995 : Blo 1630514 1631995 := bstep (se 1 (by rfl) ⟨1223996, by rfl⟩ : syracuseStep 1631995 = 2447993) B2447993
theorem B1632031 : Blo 1630514 1632031 := bstep (se 1 (by rfl) ⟨1224023, by rfl⟩ : syracuseStep 1632031 = 2448047) B2448047
theorem B1632063 : Blo 1630514 1632063 := bstep (se 1 (by rfl) ⟨1224047, by rfl⟩ : syracuseStep 1632063 = 2448095) B2448095
theorem B8259407 : Blo 1630514 8259407 := bstep (se 1 (by rfl) ⟨6194555, by rfl⟩ : syracuseStep 8259407 = 12389111) B12389111
theorem B15681509 : Blo 1630514 15681509 := bstep (se 4 (by rfl) ⟨1470141, by rfl⟩ : syracuseStep 15681509 = 2940283) B2940283
theorem B1632239 : Blo 1630514 1632239 := bstep (se 1 (by rfl) ⟨1224179, by rfl⟩ : syracuseStep 1632239 = 2448359) B2448359
theorem B1861615 : Blo 1630514 1861615 := bstep (se 1 (by rfl) ⟨1396211, by rfl⟩ : syracuseStep 1861615 = 2792423) B2792423
theorem B2754553 : Blo 1630514 2754553 := bstep (se 2 (by rfl) ⟨1032957, by rfl⟩ : syracuseStep 2754553 = 2065915) B2065915
theorem B5507081 : Blo 1630514 5507081 := bstep (se 2 (by rfl) ⟨2065155, by rfl⟩ : syracuseStep 5507081 = 4130311) B4130311
theorem B1632411 : Blo 1630514 1632411 := bstep (se 1 (by rfl) ⟨1224308, by rfl⟩ : syracuseStep 1632411 = 2448617) B2448617
theorem B2754715 : Blo 1630514 2754715 := bstep (se 1 (by rfl) ⟨2066036, by rfl⟩ : syracuseStep 2754715 = 4132073) B4132073
theorem B1632447 : Blo 1630514 1632447 := bstep (se 1 (by rfl) ⟨1224335, by rfl⟩ : syracuseStep 1632447 = 2448671) B2448671
theorem B6965459 : Blo 1630514 6965459 := bstep (se 1 (by rfl) ⟨5224094, by rfl⟩ : syracuseStep 6965459 = 10448189) B10448189
theorem B2754823 : Blo 1630514 2754823 := bstep (se 1 (by rfl) ⟨2066117, by rfl⟩ : syracuseStep 2754823 = 4132235) B4132235
theorem B3672359 : Blo 1630514 3672359 := bstep (se 1 (by rfl) ⟨2754269, by rfl⟩ : syracuseStep 3672359 = 5508539) B5508539
theorem B2754857 : Blo 1630514 2754857 := bstep (se 2 (by rfl) ⟨1033071, by rfl⟩ : syracuseStep 2754857 = 2066143) B2066143
theorem B3672377 : Blo 1630514 3672377 := bstep (se 2 (by rfl) ⟨1377141, by rfl⟩ : syracuseStep 3672377 = 2754283) B2754283
theorem B4647307 : Blo 1630514 4647307 := bstep (se 1 (by rfl) ⟨3485480, by rfl⟩ : syracuseStep 4647307 = 6970961) B6970961
theorem B4131233 : Blo 1630514 4131233 := bstep (se 2 (by rfl) ⟨1549212, by rfl⟩ : syracuseStep 4131233 = 3098425) B3098425
theorem B9292427 : Blo 1630514 9292427 := bstep (se 1 (by rfl) ⟨6969320, by rfl⟩ : syracuseStep 9292427 = 13938641) B13938641
theorem B15674093 : Blo 1630514 15674093 := bstep (se 3 (by rfl) ⟨2938892, by rfl⟩ : syracuseStep 15674093 = 5877785) B5877785
theorem B7539551 : Blo 1630514 7539551 := bstep (se 1 (by rfl) ⟨5654663, by rfl⟩ : syracuseStep 7539551 = 11309327) B11309327
theorem B5876675 : Blo 1630514 5876675 := bstep (se 1 (by rfl) ⟨4407506, by rfl⟩ : syracuseStep 5876675 = 8815013) B8815013
theorem B23514077 : Blo 1630514 23514077 := bstep (se 3 (by rfl) ⟨4408889, by rfl⟩ : syracuseStep 23514077 = 8817779) B8817779
theorem B5508377 : Blo 1630514 5508377 := bstep (se 2 (by rfl) ⟨2065641, by rfl⟩ : syracuseStep 5508377 = 4131283) B4131283
theorem B15682895 : Blo 1630514 15682895 := bstep (se 1 (by rfl) ⟨11762171, by rfl⟩ : syracuseStep 15682895 = 23524343) B23524343
theorem B5508431 : Blo 1630514 5508431 := bstep (se 1 (by rfl) ⟨4131323, by rfl⟩ : syracuseStep 5508431 = 8262647) B8262647
theorem B2321831 : Blo 1630514 2321831 := bstep (se 1 (by rfl) ⟨1741373, by rfl⟩ : syracuseStep 2321831 = 3482747) B3482747
theorem B3141193 : Blo 1630514 3141193 := bstep (se 2 (by rfl) ⟨1177947, by rfl⟩ : syracuseStep 3141193 = 2355895) B2355895
theorem B25464403 : Blo 1630514 25464403 := bstep (se 1 (by rfl) ⟨19098302, by rfl⟩ : syracuseStep 25464403 = 38196605) B38196605
theorem B12381821 : Blo 1630514 12381821 := bstep (se 3 (by rfl) ⟨2321591, by rfl⟩ : syracuseStep 12381821 = 4643183) B4643183
theorem B6279353 : Blo 1630514 6279353 := bstep (se 2 (by rfl) ⟨2354757, by rfl⟩ : syracuseStep 6279353 = 4709515) B4709515
theorem B9924817 : Blo 1630514 9924817 := bstep (se 2 (by rfl) ⟨3721806, by rfl⟩ : syracuseStep 9924817 = 7443613) B7443613
theorem B7065967 : Blo 1630514 7065967 := bstep (se 1 (by rfl) ⟨5299475, by rfl⟩ : syracuseStep 7065967 = 10598951) B10598951
theorem B8261999 : Blo 1630514 8261999 := bstep (se 1 (by rfl) ⟨6196499, by rfl⟩ : syracuseStep 8261999 = 12392999) B12392999
theorem B6967903 : Blo 1630514 6967903 := bstep (se 1 (by rfl) ⟨5225927, by rfl⟩ : syracuseStep 6967903 = 10451855) B10451855
theorem B5509727 : Blo 1630514 5509727 := bstep (se 1 (by rfl) ⟨4132295, by rfl⟩ : syracuseStep 5509727 = 8264591) B8264591
theorem B10449623 : Blo 1630514 10449623 := bstep (se 1 (by rfl) ⟨7837217, by rfl⟩ : syracuseStep 10449623 = 15674435) B15674435
theorem B2446121 : Blo 1630514 2446121 := bstep (se 2 (by rfl) ⟨917295, by rfl⟩ : syracuseStep 2446121 = 1834591) B1834591
theorem B2446127 : Blo 1630514 2446127 := bstep (se 1 (by rfl) ⟨1834595, by rfl⟩ : syracuseStep 2446127 = 3669191) B3669191
theorem B9294659 : Blo 1630514 9294659 := bstep (se 1 (by rfl) ⟨6970994, by rfl⟩ : syracuseStep 9294659 = 13941989) B13941989
theorem B14881681 : Blo 1630514 14881681 := bstep (se 2 (by rfl) ⟨5580630, by rfl⟩ : syracuseStep 14881681 = 11161261) B11161261
theorem B2446247 : Blo 1630514 2446247 := bstep (se 1 (by rfl) ⟨1834685, by rfl⟩ : syracuseStep 2446247 = 3669371) B3669371
theorem B152777677 : Blo 1630514 152777677 := bstep (se 3 (by rfl) ⟨28645814, by rfl⟩ : syracuseStep 152777677 = 57291629) B57291629
theorem B2446331 : Blo 1630514 2446331 := bstep (se 1 (by rfl) ⟨1834748, by rfl⟩ : syracuseStep 2446331 = 3669497) B3669497
theorem B2446391 : Blo 1630514 2446391 := bstep (se 1 (by rfl) ⟨1834793, by rfl⟩ : syracuseStep 2446391 = 3669587) B3669587
theorem B9294911 : Blo 1630514 9294911 := bstep (se 1 (by rfl) ⟨6971183, by rfl⟩ : syracuseStep 9294911 = 13942367) B13942367
theorem B2446511 : Blo 1630514 2446511 := bstep (se 1 (by rfl) ⟨1834883, by rfl⟩ : syracuseStep 2446511 = 3669767) B3669767
theorem B5960915 : Blo 1630514 5960915 := bstep (se 1 (by rfl) ⟨4470686, by rfl⟩ : syracuseStep 5960915 = 8941373) B8941373
theorem B5584247 : Blo 1630514 5584247 := bstep (se 1 (by rfl) ⟨4188185, by rfl⟩ : syracuseStep 5584247 = 8376371) B8376371
theorem B18585125 : Blo 1630514 18585125 := bstep (se 4 (by rfl) ⟨1742355, by rfl⟩ : syracuseStep 18585125 = 3484711) B3484711
theorem B2446919 : Blo 1630514 2446919 := bstep (se 1 (by rfl) ⟨1835189, by rfl⟩ : syracuseStep 2446919 = 3670379) B3670379
theorem B2447015 : Blo 1630514 2447015 := bstep (se 1 (by rfl) ⟨1835261, by rfl⟩ : syracuseStep 2447015 = 3670523) B3670523
theorem B2447099 : Blo 1630514 2447099 := bstep (se 1 (by rfl) ⟨1835324, by rfl⟩ : syracuseStep 2447099 = 3670649) B3670649
theorem B2447135 : Blo 1630514 2447135 := bstep (se 1 (by rfl) ⟨1835351, by rfl⟩ : syracuseStep 2447135 = 3670703) B3670703
theorem B2447183 : Blo 1630514 2447183 := bstep (se 1 (by rfl) ⟨1835387, by rfl⟩ : syracuseStep 2447183 = 3670775) B3670775
theorem B23508883 : Blo 1630514 23508883 := bstep (se 1 (by rfl) ⟨17631662, by rfl⟩ : syracuseStep 23508883 = 35263325) B35263325
theorem B2447303 : Blo 1630514 2447303 := bstep (se 1 (by rfl) ⟨1835477, by rfl⟩ : syracuseStep 2447303 = 3670955) B3670955
theorem B42375415 : Blo 1630514 42375415 := bstep (se 1 (by rfl) ⟨31781561, by rfl⟩ : syracuseStep 42375415 = 63563123) B63563123
theorem B2447657 : Blo 1630514 2447657 := bstep (se 2 (by rfl) ⟨917871, by rfl⟩ : syracuseStep 2447657 = 1835743) B1835743
theorem B2447663 : Blo 1630514 2447663 := bstep (se 1 (by rfl) ⟨1835747, by rfl⟩ : syracuseStep 2447663 = 3671495) B3671495
theorem B5503355 : Blo 1630514 5503355 := bstep (se 1 (by rfl) ⟨4127516, by rfl⟩ : syracuseStep 5503355 = 8255033) B8255033
theorem B2447903 : Blo 1630514 2447903 := bstep (se 1 (by rfl) ⟨1835927, by rfl⟩ : syracuseStep 2447903 = 3671855) B3671855
theorem B13941305 : Blo 1630514 13941305 := bstep (se 2 (by rfl) ⟨5227989, by rfl⟩ : syracuseStep 13941305 = 10455979) B10455979
theorem B40245893 : Blo 1630514 40245893 := bstep (se 4 (by rfl) ⟨3773052, by rfl⟩ : syracuseStep 40245893 = 7546105) B7546105
theorem B5503625 : Blo 1630514 5503625 := bstep (se 2 (by rfl) ⟨2063859, by rfl⟩ : syracuseStep 5503625 = 4127719) B4127719
theorem B20126483 : Blo 1630514 20126483 := bstep (se 1 (by rfl) ⟨15094862, by rfl⟩ : syracuseStep 20126483 = 30189725) B30189725
theorem B2448287 : Blo 1630514 2448287 := bstep (se 1 (by rfl) ⟨1836215, by rfl⟩ : syracuseStep 2448287 = 3672431) B3672431
theorem B55098299 : Blo 1630514 55098299 := bstep (se 1 (by rfl) ⟨41323724, by rfl⟩ : syracuseStep 55098299 = 82647449) B82647449
theorem B2448335 : Blo 1630514 2448335 := bstep (se 1 (by rfl) ⟨1836251, by rfl⟩ : syracuseStep 2448335 = 3672503) B3672503
theorem B2751529 : Blo 1630514 2751529 := bstep (se 2 (by rfl) ⟨1031823, by rfl⟩ : syracuseStep 2751529 = 2063647) B2063647
theorem B2448425 : Blo 1630514 2448425 := bstep (se 2 (by rfl) ⟨918159, by rfl⟩ : syracuseStep 2448425 = 1836319) B1836319
theorem B2448431 : Blo 1630514 2448431 := bstep (se 1 (by rfl) ⟨1836323, by rfl⟩ : syracuseStep 2448431 = 3672647) B3672647
theorem B2448455 : Blo 1630514 2448455 := bstep (se 1 (by rfl) ⟨1836341, by rfl⟩ : syracuseStep 2448455 = 3672683) B3672683
theorem B2751671 : Blo 1630514 2751671 := bstep (se 1 (by rfl) ⟨2063753, by rfl⟩ : syracuseStep 2751671 = 4127507) B4127507
theorem B5963017 : Blo 1630514 5963017 := bstep (se 2 (by rfl) ⟨2236131, by rfl⟩ : syracuseStep 5963017 = 4472263) B4472263
theorem B2448719 : Blo 1630514 2448719 := bstep (se 1 (by rfl) ⟨1836539, by rfl⟩ : syracuseStep 2448719 = 3673079) B3673079
theorem B7060841 : Blo 1630514 7060841 := bstep (se 2 (by rfl) ⟨2647815, by rfl⟩ : syracuseStep 7060841 = 5295631) B5295631
theorem B9289079 : Blo 1630514 9289079 := bstep (se 1 (by rfl) ⟨6966809, by rfl⟩ : syracuseStep 9289079 = 13933619) B13933619
theorem B6192551 : Blo 1630514 6192551 := bstep (se 1 (by rfl) ⟨4644413, by rfl⟩ : syracuseStep 6192551 = 9288827) B9288827
theorem B2940371 : Blo 1630514 2940371 := bstep (se 1 (by rfl) ⟨2205278, by rfl⟩ : syracuseStep 2940371 = 4410557) B4410557
theorem B3669479 : Blo 1630514 3669479 := bstep (se 1 (by rfl) ⟨2752109, by rfl⟩ : syracuseStep 3669479 = 5504219) B5504219
theorem B2751995 : Blo 1630514 2751995 := bstep (se 1 (by rfl) ⟨2063996, by rfl⟩ : syracuseStep 2751995 = 4127993) B4127993
theorem B26459693 : Blo 1630514 26459693 := bstep (se 3 (by rfl) ⟨4961192, by rfl⟩ : syracuseStep 26459693 = 9922385) B9922385
theorem B7446095 : Blo 1630514 7446095 := bstep (se 1 (by rfl) ⟨5584571, by rfl⟩ : syracuseStep 7446095 = 11169143) B11169143
theorem B4128347 : Blo 1630514 4128347 := bstep (se 1 (by rfl) ⟨3096260, by rfl⟩ : syracuseStep 4128347 = 6192521) B6192521
theorem B5504759 : Blo 1630514 5504759 := bstep (se 1 (by rfl) ⟨4128569, by rfl⟩ : syracuseStep 5504759 = 8257139) B8257139
theorem B2481959 : Blo 1630514 2481959 := bstep (se 1 (by rfl) ⟨1861469, by rfl⟩ : syracuseStep 2481959 = 3722939) B3722939
theorem B2064199 : Blo 1630514 2064199 := bstep (se 1 (by rfl) ⟨1548149, by rfl⟩ : syracuseStep 2064199 = 3096299) B3096299
theorem B3096443 : Blo 1630514 3096443 := bstep (se 1 (by rfl) ⟨2322332, by rfl⟩ : syracuseStep 3096443 = 4644665) B4644665
theorem B2752427 : Blo 1630514 2752427 := bstep (se 1 (by rfl) ⟨2064320, by rfl⟩ : syracuseStep 2752427 = 4128641) B4128641
theorem B4186235 : Blo 1630514 4186235 := bstep (se 1 (by rfl) ⟨3139676, by rfl⟩ : syracuseStep 4186235 = 6279353) B6279353
theorem B2064619 : Blo 1630514 2064619 := bstep (se 1 (by rfl) ⟨1548464, by rfl⟩ : syracuseStep 2064619 = 3096929) B3096929
theorem B3719471 : Blo 1630514 3719471 := bstep (se 1 (by rfl) ⟨2789603, by rfl⟩ : syracuseStep 3719471 = 5579207) B5579207
theorem B1835311 : Blo 1630514 1835311 := bstep (se 1 (by rfl) ⟨1376483, by rfl⟩ : syracuseStep 1835311 = 2752967) B2752967
theorem B56500553 : Blo 1630514 56500553 := bstep (se 2 (by rfl) ⟨21187707, by rfl⟩ : syracuseStep 56500553 = 42375415) B42375415
theorem B5505407 : Blo 1630514 5505407 := bstep (se 1 (by rfl) ⟨4129055, by rfl⟩ : syracuseStep 5505407 = 8258111) B8258111
theorem B9421289 : Blo 1630514 9421289 := bstep (se 2 (by rfl) ⟨3532983, by rfl⟩ : syracuseStep 9421289 = 7065967) B7065967
theorem B1630747 : Blo 1630514 1630747 := bstep (se 1 (by rfl) ⟨1223060, by rfl⟩ : syracuseStep 1630747 = 2446121) B2446121
theorem B1630751 : Blo 1630514 1630751 := bstep (se 1 (by rfl) ⟨1223063, by rfl⟩ : syracuseStep 1630751 = 2446127) B2446127
theorem B3670559 : Blo 1630514 3670559 := bstep (se 1 (by rfl) ⟨2752919, by rfl⟩ : syracuseStep 3670559 = 5505839) B5505839
theorem B3670631 : Blo 1630514 3670631 := bstep (se 1 (by rfl) ⟨2752973, by rfl⟩ : syracuseStep 3670631 = 5505947) B5505947
theorem B2753129 : Blo 1630514 2753129 := bstep (se 2 (by rfl) ⟨1032423, by rfl⟩ : syracuseStep 2753129 = 2064847) B2064847
theorem B1630831 : Blo 1630514 1630831 := bstep (se 1 (by rfl) ⟨1223123, by rfl⟩ : syracuseStep 1630831 = 2446247) B2446247
theorem B1630887 : Blo 1630514 1630887 := bstep (se 1 (by rfl) ⟨1223165, by rfl⟩ : syracuseStep 1630887 = 2446331) B2446331
theorem B1630927 : Blo 1630514 1630927 := bstep (se 1 (by rfl) ⟨1223195, by rfl⟩ : syracuseStep 1630927 = 2446391) B2446391
theorem B1631007 : Blo 1630514 1631007 := bstep (se 1 (by rfl) ⟨1223255, by rfl⟩ : syracuseStep 1631007 = 2446511) B2446511
theorem B9290537 : Blo 1630514 9290537 := bstep (se 2 (by rfl) ⟨3483951, by rfl⟩ : syracuseStep 9290537 = 6967903) B6967903
theorem B3973943 : Blo 1630514 3973943 := bstep (se 1 (by rfl) ⟨2980457, by rfl⟩ : syracuseStep 3973943 = 5960915) B5960915
theorem B1631279 : Blo 1630514 1631279 := bstep (se 1 (by rfl) ⟨1223459, by rfl⟩ : syracuseStep 1631279 = 2446919) B2446919
theorem B1631343 : Blo 1630514 1631343 := bstep (se 1 (by rfl) ⟨1223507, by rfl⟩ : syracuseStep 1631343 = 2447015) B2447015
theorem B1631399 : Blo 1630514 1631399 := bstep (se 1 (by rfl) ⟨1223549, by rfl⟩ : syracuseStep 1631399 = 2447099) B2447099
theorem B1631423 : Blo 1630514 1631423 := bstep (se 1 (by rfl) ⟨1223567, by rfl⟩ : syracuseStep 1631423 = 2447135) B2447135
theorem B19842241 : Blo 1630514 19842241 := bstep (se 2 (by rfl) ⟨7440840, by rfl⟩ : syracuseStep 19842241 = 14881681) B14881681
theorem B1631455 : Blo 1630514 1631455 := bstep (se 1 (by rfl) ⟨1223591, by rfl⟩ : syracuseStep 1631455 = 2447183) B2447183
theorem B5506271 : Blo 1630514 5506271 := bstep (se 1 (by rfl) ⟨4129703, by rfl⟩ : syracuseStep 5506271 = 8259407) B8259407
theorem B203703569 : Blo 1630514 203703569 := bstep (se 2 (by rfl) ⟨76388838, by rfl⟩ : syracuseStep 203703569 = 152777677) B152777677
theorem B1631535 : Blo 1630514 1631535 := bstep (se 1 (by rfl) ⟨1223651, by rfl⟩ : syracuseStep 1631535 = 2447303) B2447303
theorem B10454339 : Blo 1630514 10454339 := bstep (se 1 (by rfl) ⟨7840754, by rfl⟩ : syracuseStep 10454339 = 15681509) B15681509
theorem B3671387 : Blo 1630514 3671387 := bstep (se 1 (by rfl) ⟨2753540, by rfl⟩ : syracuseStep 3671387 = 5507081) B5507081
theorem B1631771 : Blo 1630514 1631771 := bstep (se 1 (by rfl) ⟨1223828, by rfl⟩ : syracuseStep 1631771 = 2447657) B2447657
theorem B1836571 : Blo 1630514 1836571 := bstep (se 1 (by rfl) ⟨1377428, by rfl⟩ : syracuseStep 1836571 = 2754857) B2754857
theorem B1631775 : Blo 1630514 1631775 := bstep (se 1 (by rfl) ⟨1223831, by rfl⟩ : syracuseStep 1631775 = 2447663) B2447663
theorem B3671657 : Blo 1630514 3671657 := bstep (se 2 (by rfl) ⟨1376871, by rfl⟩ : syracuseStep 3671657 = 2753743) B2753743
theorem B2754155 : Blo 1630514 2754155 := bstep (se 1 (by rfl) ⟨2065616, by rfl⟩ : syracuseStep 2754155 = 4131233) B4131233
theorem B1631935 : Blo 1630514 1631935 := bstep (se 1 (by rfl) ⟨1223951, by rfl⟩ : syracuseStep 1631935 = 2447903) B2447903
theorem B26830595 : Blo 1630514 26830595 := bstep (se 1 (by rfl) ⟨20122946, by rfl⟩ : syracuseStep 26830595 = 40245893) B40245893
theorem B6194951 : Blo 1630514 6194951 := bstep (se 1 (by rfl) ⟨4646213, by rfl⟩ : syracuseStep 6194951 = 9292427) B9292427
theorem B2754425 : Blo 1630514 2754425 := bstep (se 2 (by rfl) ⟨1032909, by rfl⟩ : syracuseStep 2754425 = 2065819) B2065819
theorem B1632191 : Blo 1630514 1632191 := bstep (se 1 (by rfl) ⟨1224143, by rfl⟩ : syracuseStep 1632191 = 2448287) B2448287
theorem B3917783 : Blo 1630514 3917783 := bstep (se 1 (by rfl) ⟨2938337, by rfl⟩ : syracuseStep 3917783 = 5876675) B5876675
theorem B1632223 : Blo 1630514 1632223 := bstep (se 1 (by rfl) ⟨1224167, by rfl⟩ : syracuseStep 1632223 = 2448335) B2448335
theorem B1632283 : Blo 1630514 1632283 := bstep (se 1 (by rfl) ⟨1224212, by rfl⟩ : syracuseStep 1632283 = 2448425) B2448425
theorem B1632287 : Blo 1630514 1632287 := bstep (se 1 (by rfl) ⟨1224215, by rfl⟩ : syracuseStep 1632287 = 2448431) B2448431
theorem B1632303 : Blo 1630514 1632303 := bstep (se 1 (by rfl) ⟨1224227, by rfl⟩ : syracuseStep 1632303 = 2448455) B2448455
theorem B4188257 : Blo 1630514 4188257 := bstep (se 2 (by rfl) ⟨1570596, by rfl⟩ : syracuseStep 4188257 = 3141193) B3141193
theorem B3672251 : Blo 1630514 3672251 := bstep (se 1 (by rfl) ⟨2754188, by rfl⟩ : syracuseStep 3672251 = 5508377) B5508377
theorem B10455263 : Blo 1630514 10455263 := bstep (se 1 (by rfl) ⟨7841447, by rfl⟩ : syracuseStep 10455263 = 15682895) B15682895
theorem B3672287 : Blo 1630514 3672287 := bstep (se 1 (by rfl) ⟨2754215, by rfl⟩ : syracuseStep 3672287 = 5508431) B5508431
theorem B1632479 : Blo 1630514 1632479 := bstep (se 1 (by rfl) ⟨1224359, by rfl⟩ : syracuseStep 1632479 = 2448719) B2448719
theorem B1960247 : Blo 1630514 1960247 := bstep (se 1 (by rfl) ⟨1470185, by rfl⟩ : syracuseStep 1960247 = 2940371) B2940371
theorem B17639795 : Blo 1630514 17639795 := bstep (se 1 (by rfl) ⟨13229846, by rfl⟩ : syracuseStep 17639795 = 26459693) B26459693
theorem B31345177 : Blo 1630514 31345177 := bstep (se 2 (by rfl) ⟨11754441, by rfl⟩ : syracuseStep 31345177 = 23508883) B23508883
theorem B3672737 : Blo 1630514 3672737 := bstep (se 2 (by rfl) ⟨1377276, by rfl⟩ : syracuseStep 3672737 = 2754553) B2754553
theorem B3672953 : Blo 1630514 3672953 := bstep (se 2 (by rfl) ⟨1377357, by rfl⟩ : syracuseStep 3672953 = 2754715) B2754715
theorem B5507999 : Blo 1630514 5507999 := bstep (se 1 (by rfl) ⟨4130999, by rfl⟩ : syracuseStep 5507999 = 8261999) B8261999
theorem B107342779 : Blo 1630514 107342779 := bstep (se 1 (by rfl) ⟨80507084, by rfl⟩ : syracuseStep 107342779 = 161014169) B161014169
theorem B13233089 : Blo 1630514 13233089 := bstep (se 2 (by rfl) ⟨4962408, by rfl⟩ : syracuseStep 13233089 = 9924817) B9924817
theorem B3673097 : Blo 1630514 3673097 := bstep (se 2 (by rfl) ⟨1377411, by rfl⟩ : syracuseStep 3673097 = 2754823) B2754823
theorem B3673151 : Blo 1630514 3673151 := bstep (se 1 (by rfl) ⟨2754863, by rfl⟩ : syracuseStep 3673151 = 5509727) B5509727
theorem B6966415 : Blo 1630514 6966415 := bstep (se 1 (by rfl) ⟨5224811, by rfl⟩ : syracuseStep 6966415 = 10449623) B10449623
theorem B6196409 : Blo 1630514 6196409 := bstep (se 2 (by rfl) ⟨2323653, by rfl⟩ : syracuseStep 6196409 = 4647307) B4647307
theorem B6196439 : Blo 1630514 6196439 := bstep (se 1 (by rfl) ⟨4647329, by rfl⟩ : syracuseStep 6196439 = 9294659) B9294659
theorem B6196607 : Blo 1630514 6196607 := bstep (se 1 (by rfl) ⟨4647455, by rfl⟩ : syracuseStep 6196607 = 9294911) B9294911
theorem B3722831 : Blo 1630514 3722831 := bstep (se 1 (by rfl) ⟨2792123, by rfl⟩ : syracuseStep 3722831 = 5584247) B5584247
theorem B12390083 : Blo 1630514 12390083 := bstep (se 1 (by rfl) ⟨9292562, by rfl⟩ : syracuseStep 12390083 = 18585125) B18585125
theorem B7950689 : Blo 1630514 7950689 := bstep (se 2 (by rfl) ⟨2981508, by rfl⟩ : syracuseStep 7950689 = 5963017) B5963017
theorem B9294203 : Blo 1630514 9294203 := bstep (se 1 (by rfl) ⟨6970652, by rfl⟩ : syracuseStep 9294203 = 13941305) B13941305
theorem B5509565 : Blo 1630514 5509565 := bstep (se 3 (by rfl) ⟨1033043, by rfl⟩ : syracuseStep 5509565 = 2066087) B2066087
theorem B10449395 : Blo 1630514 10449395 := bstep (se 1 (by rfl) ⟨7837046, by rfl⟩ : syracuseStep 10449395 = 15674093) B15674093
theorem B5026367 : Blo 1630514 5026367 := bstep (se 1 (by rfl) ⟨3769775, by rfl⟩ : syracuseStep 5026367 = 7539551) B7539551
theorem B15676051 : Blo 1630514 15676051 := bstep (se 1 (by rfl) ⟨11757038, by rfl⟩ : syracuseStep 15676051 = 23514077) B23514077
theorem B33952537 : Blo 1630514 33952537 := bstep (se 2 (by rfl) ⟨12732201, by rfl⟩ : syracuseStep 33952537 = 25464403) B25464403
theorem B4707227 : Blo 1630514 4707227 := bstep (se 1 (by rfl) ⟨3530420, by rfl⟩ : syracuseStep 4707227 = 7060841) B7060841
theorem B2446319 : Blo 1630514 2446319 := bstep (se 1 (by rfl) ⟨1834739, by rfl⟩ : syracuseStep 2446319 = 3669479) B3669479
theorem B8254547 : Blo 1630514 8254547 := bstep (se 1 (by rfl) ⟨6190910, by rfl⟩ : syracuseStep 8254547 = 12381821) B12381821
theorem B2446703 : Blo 1630514 2446703 := bstep (se 1 (by rfl) ⟨1835027, by rfl⟩ : syracuseStep 2446703 = 3670055) B3670055
theorem B2446823 : Blo 1630514 2446823 := bstep (se 1 (by rfl) ⟨1835117, by rfl⟩ : syracuseStep 2446823 = 3670235) B3670235
theorem B9295343 : Blo 1630514 9295343 := bstep (se 1 (by rfl) ⟨6971507, by rfl⟩ : syracuseStep 9295343 = 13943015) B13943015
theorem B2446985 : Blo 1630514 2446985 := bstep (se 2 (by rfl) ⟨917619, by rfl⟩ : syracuseStep 2446985 = 1835239) B1835239
theorem B12555931 : Blo 1630514 12555931 := bstep (se 1 (by rfl) ⟨9416948, by rfl⟩ : syracuseStep 12555931 = 18833897) B18833897
theorem B2447003 : Blo 1630514 2447003 := bstep (se 1 (by rfl) ⟨1835252, by rfl⟩ : syracuseStep 2447003 = 3670505) B3670505
theorem B2447195 : Blo 1630514 2447195 := bstep (se 1 (by rfl) ⟨1835396, by rfl⟩ : syracuseStep 2447195 = 3670793) B3670793
theorem B10450853 : Blo 1630514 10450853 := bstep (se 4 (by rfl) ⟨979767, by rfl⟩ : syracuseStep 10450853 = 1959535) B1959535
theorem B2447579 : Blo 1630514 2447579 := bstep (se 1 (by rfl) ⟨1835684, by rfl⟩ : syracuseStep 2447579 = 3671369) B3671369
theorem B5880221 : Blo 1630514 5880221 := bstep (se 3 (by rfl) ⟨1102541, by rfl⟩ : syracuseStep 5880221 = 2205083) B2205083
theorem B6191549 : Blo 1630514 6191549 := bstep (se 3 (by rfl) ⟨1160915, by rfl⟩ : syracuseStep 6191549 = 2321831) B2321831
theorem B15292901 : Blo 1630514 15292901 := bstep (se 4 (by rfl) ⟨1433709, by rfl⟩ : syracuseStep 15292901 = 2867419) B2867419
theorem B6969833 : Blo 1630514 6969833 := bstep (se 2 (by rfl) ⟨2613687, by rfl⟩ : syracuseStep 6969833 = 5227375) B5227375
theorem B2447849 : Blo 1630514 2447849 := bstep (se 2 (by rfl) ⟨917943, by rfl⟩ : syracuseStep 2447849 = 1835887) B1835887
theorem B3668705 : Blo 1630514 3668705 := bstep (se 2 (by rfl) ⟨1375764, by rfl⟩ : syracuseStep 3668705 = 2751529) B2751529
theorem B4643639 : Blo 1630514 4643639 := bstep (se 1 (by rfl) ⟨3482729, by rfl⟩ : syracuseStep 4643639 = 6965459) B6965459
theorem B2448239 : Blo 1630514 2448239 := bstep (se 1 (by rfl) ⟨1836179, by rfl⟩ : syracuseStep 2448239 = 3672359) B3672359
theorem B2448251 : Blo 1630514 2448251 := bstep (se 1 (by rfl) ⟨1836188, by rfl⟩ : syracuseStep 2448251 = 3672377) B3672377
theorem B3668903 : Blo 1630514 3668903 := bstep (se 1 (by rfl) ⟨2751677, by rfl⟩ : syracuseStep 3668903 = 5503355) B5503355
theorem B3669083 : Blo 1630514 3669083 := bstep (se 1 (by rfl) ⟨2751812, by rfl⟩ : syracuseStep 3669083 = 5503625) B5503625
theorem B13417655 : Blo 1630514 13417655 := bstep (se 1 (by rfl) ⟨10063241, by rfl⟩ : syracuseStep 13417655 = 20126483) B20126483
theorem B36732199 : Blo 1630514 36732199 := bstep (se 1 (by rfl) ⟨27549149, by rfl⟩ : syracuseStep 36732199 = 55098299) B55098299
theorem B6618557 : Blo 1630514 6618557 := bstep (se 3 (by rfl) ⟨1240979, by rfl⟩ : syracuseStep 6618557 = 2481959) B2481959
theorem B1834447 : Blo 1630514 1834447 := bstep (se 1 (by rfl) ⟨1375835, by rfl⟩ : syracuseStep 1834447 = 2751671) B2751671
theorem B6192719 : Blo 1630514 6192719 := bstep (se 1 (by rfl) ⟨4644539, by rfl⟩ : syracuseStep 6192719 = 9289079) B9289079
theorem B4128367 : Blo 1630514 4128367 := bstep (se 1 (by rfl) ⟨3096275, by rfl⟩ : syracuseStep 4128367 = 6192551) B6192551
theorem B1834663 : Blo 1630514 1834663 := bstep (se 1 (by rfl) ⟨1375997, by rfl⟩ : syracuseStep 1834663 = 2751995) B2751995
theorem B4964063 : Blo 1630514 4964063 := bstep (se 1 (by rfl) ⟨3723047, by rfl⟩ : syracuseStep 4964063 = 7446095) B7446095
theorem B2752231 : Blo 1630514 2752231 := bstep (se 1 (by rfl) ⟨2064173, by rfl⟩ : syracuseStep 2752231 = 4128347) B4128347
theorem B2752265 : Blo 1630514 2752265 := bstep (se 2 (by rfl) ⟨1032099, by rfl⟩ : syracuseStep 2752265 = 2064199) B2064199
theorem B3669839 : Blo 1630514 3669839 := bstep (se 1 (by rfl) ⟨2752379, by rfl⟩ : syracuseStep 3669839 = 5504759) B5504759
theorem B9928613 : Blo 1630514 9928613 := bstep (se 4 (by rfl) ⟨930807, by rfl⟩ : syracuseStep 9928613 = 1861615) B1861615
theorem B2064295 : Blo 1630514 2064295 := bstep (se 1 (by rfl) ⟨1548221, by rfl⟩ : syracuseStep 2064295 = 3096443) B3096443
theorem B1834951 : Blo 1630514 1834951 := bstep (se 1 (by rfl) ⟨1376213, by rfl⟩ : syracuseStep 1834951 = 2752427) B2752427
theorem B37667035 : Blo 1630514 37667035 := bstep (se 1 (by rfl) ⟨28250276, by rfl⟩ : syracuseStep 37667035 = 56500553) B56500553
theorem B3670271 : Blo 1630514 3670271 := bstep (se 1 (by rfl) ⟨2752703, by rfl⟩ : syracuseStep 3670271 = 5505407) B5505407
theorem B2752825 : Blo 1630514 2752825 := bstep (se 2 (by rfl) ⟨1032309, by rfl⟩ : syracuseStep 2752825 = 2064619) B2064619
theorem B3350911 : Blo 1630514 3350911 := bstep (se 1 (by rfl) ⟨2513183, by rfl⟩ : syracuseStep 3350911 = 5026367) B5026367
theorem B1835419 : Blo 1630514 1835419 := bstep (se 1 (by rfl) ⟨1376564, by rfl⟩ : syracuseStep 1835419 = 2753129) B2753129
theorem B39674357 : Blo 1630514 39674357 := bstep (se 5 (by rfl) ⟨1859735, by rfl⟩ : syracuseStep 39674357 = 3719471) B3719471
theorem B6193691 : Blo 1630514 6193691 := bstep (se 1 (by rfl) ⟨4645268, by rfl⟩ : syracuseStep 6193691 = 9290537) B9290537
theorem B3138151 : Blo 1630514 3138151 := bstep (se 1 (by rfl) ⟨2353613, by rfl⟩ : syracuseStep 3138151 = 4707227) B4707227
theorem B1630879 : Blo 1630514 1630879 := bstep (se 1 (by rfl) ⟨1223159, by rfl⟩ : syracuseStep 1630879 = 2446319) B2446319
theorem B5227325 : Blo 1630514 5227325 := bstep (se 3 (by rfl) ⟨980123, by rfl⟩ : syracuseStep 5227325 = 1960247) B1960247
theorem B3670847 : Blo 1630514 3670847 := bstep (se 1 (by rfl) ⟨2753135, by rfl⟩ : syracuseStep 3670847 = 5506271) B5506271
theorem B1631135 : Blo 1630514 1631135 := bstep (se 1 (by rfl) ⟨1223351, by rfl⟩ : syracuseStep 1631135 = 2446703) B2446703
theorem B47039453 : Blo 1630514 47039453 := bstep (se 3 (by rfl) ⟨8819897, by rfl⟩ : syracuseStep 47039453 = 17639795) B17639795
theorem B1631215 : Blo 1630514 1631215 := bstep (se 1 (by rfl) ⟨1223411, by rfl⟩ : syracuseStep 1631215 = 2446823) B2446823
theorem B1836103 : Blo 1630514 1836103 := bstep (se 1 (by rfl) ⟨1377077, by rfl⟩ : syracuseStep 1836103 = 2754155) B2754155
theorem B1631323 : Blo 1630514 1631323 := bstep (se 1 (by rfl) ⟨1223492, by rfl⟩ : syracuseStep 1631323 = 2446985) B2446985
theorem B1631335 : Blo 1630514 1631335 := bstep (se 1 (by rfl) ⟨1223501, by rfl⟩ : syracuseStep 1631335 = 2447003) B2447003
theorem B4129967 : Blo 1630514 4129967 := bstep (se 1 (by rfl) ⟨3097475, by rfl⟩ : syracuseStep 4129967 = 6194951) B6194951
theorem B1631463 : Blo 1630514 1631463 := bstep (se 1 (by rfl) ⟨1223597, by rfl⟩ : syracuseStep 1631463 = 2447195) B2447195
theorem B1836283 : Blo 1630514 1836283 := bstep (se 1 (by rfl) ⟨1377212, by rfl⟩ : syracuseStep 1836283 = 2754425) B2754425
theorem B143123705 : Blo 1630514 143123705 := bstep (se 2 (by rfl) ⟨53671389, by rfl⟩ : syracuseStep 143123705 = 107342779) B107342779
theorem B1631719 : Blo 1630514 1631719 := bstep (se 1 (by rfl) ⟨1223789, by rfl⟩ : syracuseStep 1631719 = 2447579) B2447579
theorem B4646555 : Blo 1630514 4646555 := bstep (se 1 (by rfl) ⟨3484916, by rfl⟩ : syracuseStep 4646555 = 6969833) B6969833
theorem B1631899 : Blo 1630514 1631899 := bstep (se 1 (by rfl) ⟨1223924, by rfl⟩ : syracuseStep 1631899 = 2447849) B2447849
theorem B1632159 : Blo 1630514 1632159 := bstep (se 1 (by rfl) ⟨1224119, by rfl⟩ : syracuseStep 1632159 = 2448239) B2448239
theorem B1632167 : Blo 1630514 1632167 := bstep (se 1 (by rfl) ⟨1224125, by rfl⟩ : syracuseStep 1632167 = 2448251) B2448251
theorem B3671999 : Blo 1630514 3671999 := bstep (se 1 (by rfl) ⟨2753999, by rfl⟩ : syracuseStep 3671999 = 5507999) B5507999
theorem B4130939 : Blo 1630514 4130939 := bstep (se 1 (by rfl) ⟨3098204, by rfl⟩ : syracuseStep 4130939 = 6196409) B6196409
theorem B4130959 : Blo 1630514 4130959 := bstep (se 1 (by rfl) ⟨3098219, by rfl⟩ : syracuseStep 4130959 = 6196439) B6196439
theorem B4131071 : Blo 1630514 4131071 := bstep (se 1 (by rfl) ⟨3098303, by rfl⟩ : syracuseStep 4131071 = 6196607) B6196607
theorem B8260055 : Blo 1630514 8260055 := bstep (se 1 (by rfl) ⟨6195041, by rfl⟩ : syracuseStep 8260055 = 12390083) B12390083
theorem B6196135 : Blo 1630514 6196135 := bstep (se 1 (by rfl) ⟨4647101, by rfl⟩ : syracuseStep 6196135 = 9294203) B9294203
theorem B3673043 : Blo 1630514 3673043 := bstep (se 1 (by rfl) ⟨2754782, by rfl⟩ : syracuseStep 3673043 = 5509565) B5509565
theorem B6966263 : Blo 1630514 6966263 := bstep (se 1 (by rfl) ⟨5224697, by rfl⟩ : syracuseStep 6966263 = 10449395) B10449395
theorem B2649295 : Blo 1630514 2649295 := bstep (se 1 (by rfl) ⟨1986971, by rfl⟩ : syracuseStep 2649295 = 3973943) B3973943
theorem B135802379 : Blo 1630514 135802379 := bstep (se 1 (by rfl) ⟨101851784, by rfl⟩ : syracuseStep 135802379 = 203703569) B203703569
theorem B20901401 : Blo 1630514 20901401 := bstep (se 2 (by rfl) ⟨7838025, by rfl⟩ : syracuseStep 20901401 = 15676051) B15676051
theorem B6196895 : Blo 1630514 6196895 := bstep (se 1 (by rfl) ⟨4647671, by rfl⟩ : syracuseStep 6196895 = 9295343) B9295343
theorem B17649485 : Blo 1630514 17649485 := bstep (se 3 (by rfl) ⟨3309278, by rfl⟩ : syracuseStep 17649485 = 6618557) B6618557
theorem B17887063 : Blo 1630514 17887063 := bstep (se 1 (by rfl) ⟨13415297, by rfl⟩ : syracuseStep 17887063 = 26830595) B26830595
theorem B6967235 : Blo 1630514 6967235 := bstep (se 1 (by rfl) ⟨5225426, by rfl⟩ : syracuseStep 6967235 = 10450853) B10450853
theorem B181080197 : Blo 1630514 181080197 := bstep (se 4 (by rfl) ⟨16976268, by rfl⟩ : syracuseStep 181080197 = 33952537) B33952537
theorem B26456321 : Blo 1630514 26456321 := bstep (se 2 (by rfl) ⟨9921120, by rfl⟩ : syracuseStep 26456321 = 19842241) B19842241
theorem B3920147 : Blo 1630514 3920147 := bstep (se 1 (by rfl) ⟨2940110, by rfl⟩ : syracuseStep 3920147 = 5880221) B5880221
theorem B10195267 : Blo 1630514 10195267 := bstep (se 1 (by rfl) ⟨7646450, by rfl⟩ : syracuseStep 10195267 = 15292901) B15292901
theorem B48976265 : Blo 1630514 48976265 := bstep (se 2 (by rfl) ⟨18366099, by rfl⟩ : syracuseStep 48976265 = 36732199) B36732199
theorem B2445803 : Blo 1630514 2445803 := bstep (se 1 (by rfl) ⟨1834352, by rfl⟩ : syracuseStep 2445803 = 3668705) B3668705
theorem B2445929 : Blo 1630514 2445929 := bstep (se 2 (by rfl) ⟨917223, by rfl⟩ : syracuseStep 2445929 = 1834447) B1834447
theorem B2445935 : Blo 1630514 2445935 := bstep (se 1 (by rfl) ⟨1834451, by rfl⟩ : syracuseStep 2445935 = 3668903) B3668903
theorem B2446055 : Blo 1630514 2446055 := bstep (se 1 (by rfl) ⟨1834541, by rfl⟩ : syracuseStep 2446055 = 3669083) B3669083
theorem B16741241 : Blo 1630514 16741241 := bstep (se 2 (by rfl) ⟨6277965, by rfl⟩ : syracuseStep 16741241 = 12555931) B12555931
theorem B2446217 : Blo 1630514 2446217 := bstep (se 2 (by rfl) ⟨917331, by rfl⟩ : syracuseStep 2446217 = 1834663) B1834663
theorem B35288237 : Blo 1630514 35288237 := bstep (se 3 (by rfl) ⟨6616544, by rfl⟩ : syracuseStep 35288237 = 13233089) B13233089
theorem B2446559 : Blo 1630514 2446559 := bstep (se 1 (by rfl) ⟨1834919, by rfl⟩ : syracuseStep 2446559 = 3669839) B3669839
theorem B2446601 : Blo 1630514 2446601 := bstep (se 2 (by rfl) ⟨917475, by rfl⟩ : syracuseStep 2446601 = 1834951) B1834951
theorem B2790823 : Blo 1630514 2790823 := bstep (se 1 (by rfl) ⟨2093117, by rfl⟩ : syracuseStep 2790823 = 4186235) B4186235
theorem B6280859 : Blo 1630514 6280859 := bstep (se 1 (by rfl) ⟨4710644, by rfl⟩ : syracuseStep 6280859 = 9421289) B9421289
theorem B2447039 : Blo 1630514 2447039 := bstep (se 1 (by rfl) ⟨1835279, by rfl⟩ : syracuseStep 2447039 = 3670559) B3670559
theorem B2447081 : Blo 1630514 2447081 := bstep (se 2 (by rfl) ⟨917655, by rfl⟩ : syracuseStep 2447081 = 1835311) B1835311
theorem B2447087 : Blo 1630514 2447087 := bstep (se 1 (by rfl) ⟨1835315, by rfl⟩ : syracuseStep 2447087 = 3670631) B3670631
theorem B35780413 : Blo 1630514 35780413 := bstep (se 3 (by rfl) ⟨6708827, by rfl⟩ : syracuseStep 35780413 = 13417655) B13417655
theorem B41793569 : Blo 1630514 41793569 := bstep (se 2 (by rfl) ⟨15672588, by rfl⟩ : syracuseStep 41793569 = 31345177) B31345177
theorem B5503031 : Blo 1630514 5503031 := bstep (se 1 (by rfl) ⟨4127273, by rfl⟩ : syracuseStep 5503031 = 8254547) B8254547
theorem B6969559 : Blo 1630514 6969559 := bstep (se 1 (by rfl) ⟨5227169, by rfl⟩ : syracuseStep 6969559 = 10454339) B10454339
theorem B2447591 : Blo 1630514 2447591 := bstep (se 1 (by rfl) ⟨1835693, by rfl⟩ : syracuseStep 2447591 = 3671387) B3671387
theorem B2447771 : Blo 1630514 2447771 := bstep (se 1 (by rfl) ⟨1835828, by rfl⟩ : syracuseStep 2447771 = 3671657) B3671657
theorem B2611855 : Blo 1630514 2611855 := bstep (se 1 (by rfl) ⟨1958891, by rfl⟩ : syracuseStep 2611855 = 3917783) B3917783
theorem B339229397 : Blo 1630514 339229397 := bstep (se 7 (by rfl) ⟨3975344, by rfl⟩ : syracuseStep 339229397 = 7950689) B7950689
theorem B2792171 : Blo 1630514 2792171 := bstep (se 1 (by rfl) ⟨2094128, by rfl⟩ : syracuseStep 2792171 = 4188257) B4188257
theorem B2448167 : Blo 1630514 2448167 := bstep (se 1 (by rfl) ⟨1836125, by rfl⟩ : syracuseStep 2448167 = 3672251) B3672251
theorem B6970175 : Blo 1630514 6970175 := bstep (se 1 (by rfl) ⟨5227631, by rfl⟩ : syracuseStep 6970175 = 10455263) B10455263
theorem B2448191 : Blo 1630514 2448191 := bstep (se 1 (by rfl) ⟨1836143, by rfl⟩ : syracuseStep 2448191 = 3672287) B3672287
theorem B9288553 : Blo 1630514 9288553 := bstep (se 2 (by rfl) ⟨3483207, by rfl⟩ : syracuseStep 9288553 = 6966415) B6966415
theorem B4127699 : Blo 1630514 4127699 := bstep (se 1 (by rfl) ⟨3095774, by rfl⟩ : syracuseStep 4127699 = 6191549) B6191549
theorem B2448491 : Blo 1630514 2448491 := bstep (se 1 (by rfl) ⟨1836368, by rfl⟩ : syracuseStep 2448491 = 3672737) B3672737
theorem B3095759 : Blo 1630514 3095759 := bstep (se 1 (by rfl) ⟨2321819, by rfl⟩ : syracuseStep 3095759 = 4643639) B4643639
theorem B2448635 : Blo 1630514 2448635 := bstep (se 1 (by rfl) ⟨1836476, by rfl⟩ : syracuseStep 2448635 = 3672953) B3672953
theorem B13237501 : Blo 1630514 13237501 := bstep (se 3 (by rfl) ⟨2482031, by rfl⟩ : syracuseStep 13237501 = 4964063) B4964063
theorem B2448731 : Blo 1630514 2448731 := bstep (se 1 (by rfl) ⟨1836548, by rfl⟩ : syracuseStep 2448731 = 3673097) B3673097
theorem B2448761 : Blo 1630514 2448761 := bstep (se 2 (by rfl) ⟨918285, by rfl⟩ : syracuseStep 2448761 = 1836571) B1836571
theorem B2448767 : Blo 1630514 2448767 := bstep (se 1 (by rfl) ⟨1836575, by rfl⟩ : syracuseStep 2448767 = 3673151) B3673151
theorem B5504489 : Blo 1630514 5504489 := bstep (se 2 (by rfl) ⟨2064183, by rfl⟩ : syracuseStep 5504489 = 4128367) B4128367
theorem B3669641 : Blo 1630514 3669641 := bstep (se 2 (by rfl) ⟨1376115, by rfl⟩ : syracuseStep 3669641 = 2752231) B2752231
theorem B4128479 : Blo 1630514 4128479 := bstep (se 1 (by rfl) ⟨3096359, by rfl⟩ : syracuseStep 4128479 = 6192719) B6192719
theorem B2481887 : Blo 1630514 2481887 := bstep (se 1 (by rfl) ⟨1861415, by rfl⟩ : syracuseStep 2481887 = 3722831) B3722831
theorem B26476301 : Blo 1630514 26476301 := bstep (se 3 (by rfl) ⟨4964306, by rfl⟩ : syracuseStep 26476301 = 9928613) B9928613
theorem B1834843 : Blo 1630514 1834843 := bstep (se 1 (by rfl) ⟨1376132, by rfl⟩ : syracuseStep 1834843 = 2752265) B2752265
theorem B2752393 : Blo 1630514 2752393 := bstep (se 2 (by rfl) ⟨1032147, by rfl⟩ : syracuseStep 2752393 = 2064295) B2064295
theorem B17637547 : Blo 1630514 17637547 := bstep (se 1 (by rfl) ⟨13228160, by rfl⟩ : syracuseStep 17637547 = 26456321) B26456321
theorem B2613431 : Blo 1630514 2613431 := bstep (se 1 (by rfl) ⟨1960073, by rfl⟩ : syracuseStep 2613431 = 3920147) B3920147
theorem B1630535 : Blo 1630514 1630535 := bstep (se 1 (by rfl) ⟨1222901, by rfl⟩ : syracuseStep 1630535 = 2445803) B2445803
theorem B4129127 : Blo 1630514 4129127 := bstep (se 1 (by rfl) ⟨3096845, by rfl⟩ : syracuseStep 4129127 = 6193691) B6193691
theorem B1630619 : Blo 1630514 1630619 := bstep (se 1 (by rfl) ⟨1222964, by rfl⟩ : syracuseStep 1630619 = 2445929) B2445929
theorem B1630623 : Blo 1630514 1630623 := bstep (se 1 (by rfl) ⟨1222967, by rfl⟩ : syracuseStep 1630623 = 2445935) B2445935
theorem B3670433 : Blo 1630514 3670433 := bstep (se 2 (by rfl) ⟨1376412, by rfl⟩ : syracuseStep 3670433 = 2752825) B2752825
theorem B1630703 : Blo 1630514 1630703 := bstep (se 1 (by rfl) ⟨1223027, by rfl⟩ : syracuseStep 1630703 = 2446055) B2446055
theorem B1630811 : Blo 1630514 1630811 := bstep (se 1 (by rfl) ⟨1223108, by rfl⟩ : syracuseStep 1630811 = 2446217) B2446217
theorem B31359635 : Blo 1630514 31359635 := bstep (se 1 (by rfl) ⟨23519726, by rfl⟩ : syracuseStep 31359635 = 47039453) B47039453
theorem B2753311 : Blo 1630514 2753311 := bstep (se 1 (by rfl) ⟨2064983, by rfl⟩ : syracuseStep 2753311 = 4129967) B4129967
theorem B1631039 : Blo 1630514 1631039 := bstep (se 1 (by rfl) ⟨1223279, by rfl⟩ : syracuseStep 1631039 = 2446559) B2446559
theorem B1631067 : Blo 1630514 1631067 := bstep (se 1 (by rfl) ⟨1223300, by rfl⟩ : syracuseStep 1631067 = 2446601) B2446601
theorem B3097703 : Blo 1630514 3097703 := bstep (se 1 (by rfl) ⟨2323277, by rfl⟩ : syracuseStep 3097703 = 4646555) B4646555
theorem B1631359 : Blo 1630514 1631359 := bstep (se 1 (by rfl) ⟨1223519, by rfl⟩ : syracuseStep 1631359 = 2447039) B2447039
theorem B1631387 : Blo 1630514 1631387 := bstep (se 1 (by rfl) ⟨1223540, by rfl⟩ : syracuseStep 1631387 = 2447081) B2447081
theorem B1631391 : Blo 1630514 1631391 := bstep (se 1 (by rfl) ⟨1223543, by rfl⟩ : syracuseStep 1631391 = 2447087) B2447087
theorem B27862379 : Blo 1630514 27862379 := bstep (se 1 (by rfl) ⟨20896784, by rfl⟩ : syracuseStep 27862379 = 41793569) B41793569
theorem B2753959 : Blo 1630514 2753959 := bstep (se 1 (by rfl) ⟨2065469, by rfl⟩ : syracuseStep 2753959 = 4130939) B4130939
theorem B1631727 : Blo 1630514 1631727 := bstep (se 1 (by rfl) ⟨1223795, by rfl⟩ : syracuseStep 1631727 = 2447591) B2447591
theorem B2754047 : Blo 1630514 2754047 := bstep (se 1 (by rfl) ⟨2065535, by rfl⟩ : syracuseStep 2754047 = 4131071) B4131071
theorem B1631847 : Blo 1630514 1631847 := bstep (se 1 (by rfl) ⟨1223885, by rfl⟩ : syracuseStep 1631847 = 2447771) B2447771
theorem B3532393 : Blo 1630514 3532393 := bstep (se 2 (by rfl) ⟨1324647, by rfl⟩ : syracuseStep 3532393 = 2649295) B2649295
theorem B5506703 : Blo 1630514 5506703 := bstep (se 1 (by rfl) ⟨4130027, by rfl⟩ : syracuseStep 5506703 = 8260055) B8260055
theorem B1632111 : Blo 1630514 1632111 := bstep (se 1 (by rfl) ⟨1224083, by rfl⟩ : syracuseStep 1632111 = 2448167) B2448167
theorem B4646783 : Blo 1630514 4646783 := bstep (se 1 (by rfl) ⟨3485087, by rfl⟩ : syracuseStep 4646783 = 6970175) B6970175
theorem B1632127 : Blo 1630514 1632127 := bstep (se 1 (by rfl) ⟨1224095, by rfl⟩ : syracuseStep 1632127 = 2448191) B2448191
theorem B3721097 : Blo 1630514 3721097 := bstep (se 2 (by rfl) ⟨1395411, by rfl⟩ : syracuseStep 3721097 = 2790823) B2790823
theorem B1632327 : Blo 1630514 1632327 := bstep (se 1 (by rfl) ⟨1224245, by rfl⟩ : syracuseStep 1632327 = 2448491) B2448491
theorem B1632423 : Blo 1630514 1632423 := bstep (se 1 (by rfl) ⟨1224317, by rfl⟩ : syracuseStep 1632423 = 2448635) B2448635
theorem B1632487 : Blo 1630514 1632487 := bstep (se 1 (by rfl) ⟨1224365, by rfl⟩ : syracuseStep 1632487 = 2448731) B2448731
theorem B1632507 : Blo 1630514 1632507 := bstep (se 1 (by rfl) ⟨1224380, by rfl⟩ : syracuseStep 1632507 = 2448761) B2448761
theorem B1632511 : Blo 1630514 1632511 := bstep (se 1 (by rfl) ⟨1224383, by rfl⟩ : syracuseStep 1632511 = 2448767) B2448767
theorem B4131263 : Blo 1630514 4131263 := bstep (se 1 (by rfl) ⟨3098447, by rfl⟩ : syracuseStep 4131263 = 6196895) B6196895
theorem B23849417 : Blo 1630514 23849417 := bstep (se 2 (by rfl) ⟨8943531, by rfl⟩ : syracuseStep 23849417 = 17887063) B17887063
theorem B11766323 : Blo 1630514 11766323 := bstep (se 1 (by rfl) ⟨8824742, by rfl⟩ : syracuseStep 11766323 = 17649485) B17649485
theorem B120720131 : Blo 1630514 120720131 := bstep (se 1 (by rfl) ⟨90540098, by rfl⟩ : syracuseStep 120720131 = 181080197) B181080197
theorem B5507945 : Blo 1630514 5507945 := bstep (se 2 (by rfl) ⟨2065479, by rfl⟩ : syracuseStep 5507945 = 4130959) B4130959
theorem B9292745 : Blo 1630514 9292745 := bstep (se 2 (by rfl) ⟨3484779, by rfl⟩ : syracuseStep 9292745 = 6969559) B6969559
theorem B13593689 : Blo 1630514 13593689 := bstep (se 2 (by rfl) ⟨5097633, by rfl⟩ : syracuseStep 13593689 = 10195267) B10195267
theorem B4467881 : Blo 1630514 4467881 := bstep (se 2 (by rfl) ⟨1675455, by rfl⟩ : syracuseStep 4467881 = 3350911) B3350911
theorem B3484883 : Blo 1630514 3484883 := bstep (se 1 (by rfl) ⟨2613662, by rfl⟩ : syracuseStep 3484883 = 5227325) B5227325
theorem B11160827 : Blo 1630514 11160827 := bstep (se 1 (by rfl) ⟨8370620, by rfl⟩ : syracuseStep 11160827 = 16741241) B16741241
theorem B13929893 : Blo 1630514 13929893 := bstep (se 4 (by rfl) ⟨1305927, by rfl⟩ : syracuseStep 13929893 = 2611855) B2611855
theorem B95415803 : Blo 1630514 95415803 := bstep (se 1 (by rfl) ⟨71561852, by rfl⟩ : syracuseStep 95415803 = 143123705) B143123705
theorem B8261513 : Blo 1630514 8261513 := bstep (se 2 (by rfl) ⟨3098067, by rfl⟩ : syracuseStep 8261513 = 6196135) B6196135
theorem B17650001 : Blo 1630514 17650001 := bstep (se 2 (by rfl) ⟨6618750, by rfl⟩ : syracuseStep 17650001 = 13237501) B13237501
theorem B16748957 : Blo 1630514 16748957 := bstep (se 3 (by rfl) ⟨3140429, by rfl⟩ : syracuseStep 16748957 = 6280859) B6280859
theorem B226152931 : Blo 1630514 226152931 := bstep (se 1 (by rfl) ⟨169614698, by rfl⟩ : syracuseStep 226152931 = 339229397) B339229397
theorem B90534919 : Blo 1630514 90534919 := bstep (se 1 (by rfl) ⟨67901189, by rfl⟩ : syracuseStep 90534919 = 135802379) B135802379
theorem B47707217 : Blo 1630514 47707217 := bstep (se 2 (by rfl) ⟨17890206, by rfl⟩ : syracuseStep 47707217 = 35780413) B35780413
theorem B2446427 : Blo 1630514 2446427 := bstep (se 1 (by rfl) ⟨1834820, by rfl⟩ : syracuseStep 2446427 = 3669641) B3669641
theorem B2446457 : Blo 1630514 2446457 := bstep (se 2 (by rfl) ⟨917421, by rfl⟩ : syracuseStep 2446457 = 1834843) B1834843
theorem B17650867 : Blo 1630514 17650867 := bstep (se 1 (by rfl) ⟨13238150, by rfl⟩ : syracuseStep 17650867 = 26476301) B26476301
theorem B2446847 : Blo 1630514 2446847 := bstep (se 1 (by rfl) ⟨1835135, by rfl⟩ : syracuseStep 2446847 = 3670271) B3670271
theorem B50222713 : Blo 1630514 50222713 := bstep (se 2 (by rfl) ⟨18833517, by rfl⟩ : syracuseStep 50222713 = 37667035) B37667035
theorem B26449571 : Blo 1630514 26449571 := bstep (se 1 (by rfl) ⟨19837178, by rfl⟩ : syracuseStep 26449571 = 39674357) B39674357
theorem B2447225 : Blo 1630514 2447225 := bstep (se 2 (by rfl) ⟨917709, by rfl⟩ : syracuseStep 2447225 = 1835419) B1835419
theorem B8255357 : Blo 1630514 8255357 := bstep (se 3 (by rfl) ⟨1547879, by rfl⟩ : syracuseStep 8255357 = 3095759) B3095759
theorem B2447231 : Blo 1630514 2447231 := bstep (se 1 (by rfl) ⟨1835423, by rfl⟩ : syracuseStep 2447231 = 3670847) B3670847
theorem B23525491 : Blo 1630514 23525491 := bstep (se 1 (by rfl) ⟨17644118, by rfl⟩ : syracuseStep 23525491 = 35288237) B35288237
theorem B4184201 : Blo 1630514 4184201 := bstep (se 2 (by rfl) ⟨1569075, by rfl⟩ : syracuseStep 4184201 = 3138151) B3138151
theorem B130603373 : Blo 1630514 130603373 := bstep (se 3 (by rfl) ⟨24488132, by rfl⟩ : syracuseStep 130603373 = 48976265) B48976265
theorem B12384737 : Blo 1630514 12384737 := bstep (se 2 (by rfl) ⟨4644276, by rfl⟩ : syracuseStep 12384737 = 9288553) B9288553
theorem B2447999 : Blo 1630514 2447999 := bstep (se 1 (by rfl) ⟨1835999, by rfl⟩ : syracuseStep 2447999 = 3671999) B3671999
theorem B3668687 : Blo 1630514 3668687 := bstep (se 1 (by rfl) ⟨2751515, by rfl⟩ : syracuseStep 3668687 = 5503031) B5503031
theorem B2448137 : Blo 1630514 2448137 := bstep (se 2 (by rfl) ⟨918051, by rfl⟩ : syracuseStep 2448137 = 1836103) B1836103
theorem B2448377 : Blo 1630514 2448377 := bstep (se 2 (by rfl) ⟨918141, by rfl⟩ : syracuseStep 2448377 = 1836283) B1836283
theorem B7445789 : Blo 1630514 7445789 := bstep (se 3 (by rfl) ⟨1396085, by rfl⟩ : syracuseStep 7445789 = 2792171) B2792171
theorem B2751799 : Blo 1630514 2751799 := bstep (se 1 (by rfl) ⟨2063849, by rfl⟩ : syracuseStep 2751799 = 4127699) B4127699
theorem B2448695 : Blo 1630514 2448695 := bstep (se 1 (by rfl) ⟨1836521, by rfl⟩ : syracuseStep 2448695 = 3673043) B3673043
theorem B4644175 : Blo 1630514 4644175 := bstep (se 1 (by rfl) ⟨3483131, by rfl⟩ : syracuseStep 4644175 = 6966263) B6966263
theorem B3669659 : Blo 1630514 3669659 := bstep (se 1 (by rfl) ⟨2752244, by rfl⟩ : syracuseStep 3669659 = 5504489) B5504489
theorem B13934267 : Blo 1630514 13934267 := bstep (se 1 (by rfl) ⟨10450700, by rfl⟩ : syracuseStep 13934267 = 20901401) B20901401
theorem B2752319 : Blo 1630514 2752319 := bstep (se 1 (by rfl) ⟨2064239, by rfl⟩ : syracuseStep 2752319 = 4128479) B4128479
theorem B1654591 : Blo 1630514 1654591 := bstep (se 1 (by rfl) ⟨1240943, by rfl⟩ : syracuseStep 1654591 = 2481887) B2481887
theorem B18579293 : Blo 1630514 18579293 := bstep (se 3 (by rfl) ⟨3483617, by rfl⟩ : syracuseStep 18579293 = 6967235) B6967235
theorem B3669857 : Blo 1630514 3669857 := bstep (se 2 (by rfl) ⟨1376196, by rfl⟩ : syracuseStep 3669857 = 2752393) B2752393
theorem B31367321 : Blo 1630514 31367321 := bstep (se 2 (by rfl) ⟨11762745, by rfl⟩ : syracuseStep 31367321 = 23525491) B23525491
theorem B2752751 : Blo 1630514 2752751 := bstep (se 1 (by rfl) ⟨2064563, by rfl⟩ : syracuseStep 2752751 = 4129127) B4129127
theorem B11157869 : Blo 1630514 11157869 := bstep (se 3 (by rfl) ⟨2092100, by rfl⟩ : syracuseStep 11157869 = 4184201) B4184201
theorem B20906423 : Blo 1630514 20906423 := bstep (se 1 (by rfl) ⟨15679817, by rfl⟩ : syracuseStep 20906423 = 31359635) B31359635
theorem B1630951 : Blo 1630514 1630951 := bstep (se 1 (by rfl) ⟨1223213, by rfl⟩ : syracuseStep 1630951 = 2446427) B2446427
theorem B1630971 : Blo 1630514 1630971 := bstep (se 1 (by rfl) ⟨1223228, by rfl⟩ : syracuseStep 1630971 = 2446457) B2446457
theorem B1631231 : Blo 1630514 1631231 := bstep (se 1 (by rfl) ⟨1223423, by rfl⟩ : syracuseStep 1631231 = 2446847) B2446847
theorem B1836031 : Blo 1630514 1836031 := bstep (se 1 (by rfl) ⟨1377023, by rfl⟩ : syracuseStep 1836031 = 2754047) B2754047
theorem B3671081 : Blo 1630514 3671081 := bstep (se 2 (by rfl) ⟨1376655, by rfl⟩ : syracuseStep 3671081 = 2753311) B2753311
theorem B44663885 : Blo 1630514 44663885 := bstep (se 3 (by rfl) ⟨8374478, by rfl⟩ : syracuseStep 44663885 = 16748957) B16748957
theorem B3671135 : Blo 1630514 3671135 := bstep (se 1 (by rfl) ⟨2753351, by rfl⟩ : syracuseStep 3671135 = 5506703) B5506703
theorem B1631483 : Blo 1630514 1631483 := bstep (se 1 (by rfl) ⟨1223612, by rfl⟩ : syracuseStep 1631483 = 2447225) B2447225
theorem B1631487 : Blo 1630514 1631487 := bstep (se 1 (by rfl) ⟨1223615, by rfl⟩ : syracuseStep 1631487 = 2447231) B2447231
theorem B3097855 : Blo 1630514 3097855 := bstep (se 1 (by rfl) ⟨2323391, by rfl⟩ : syracuseStep 3097855 = 4646783) B4646783
theorem B2754175 : Blo 1630514 2754175 := bstep (se 1 (by rfl) ⟨2065631, by rfl⟩ : syracuseStep 2754175 = 4131263) B4131263
theorem B1631999 : Blo 1630514 1631999 := bstep (se 1 (by rfl) ⟨1223999, by rfl⟩ : syracuseStep 1631999 = 2447999) B2447999
theorem B80480087 : Blo 1630514 80480087 := bstep (se 1 (by rfl) ⟨60360065, by rfl⟩ : syracuseStep 80480087 = 120720131) B120720131
theorem B1632091 : Blo 1630514 1632091 := bstep (se 1 (by rfl) ⟨1224068, by rfl⟩ : syracuseStep 1632091 = 2448137) B2448137
theorem B3671945 : Blo 1630514 3671945 := bstep (se 2 (by rfl) ⟨1376979, by rfl⟩ : syracuseStep 3671945 = 2753959) B2753959
theorem B3671963 : Blo 1630514 3671963 := bstep (se 1 (by rfl) ⟨2753972, by rfl⟩ : syracuseStep 3671963 = 5507945) B5507945
theorem B6195163 : Blo 1630514 6195163 := bstep (se 1 (by rfl) ⟨4646372, by rfl⟩ : syracuseStep 6195163 = 9292745) B9292745
theorem B1632251 : Blo 1630514 1632251 := bstep (se 1 (by rfl) ⟨1224188, by rfl⟩ : syracuseStep 1632251 = 2448377) B2448377
theorem B9062459 : Blo 1630514 9062459 := bstep (se 1 (by rfl) ⟨6796844, by rfl⟩ : syracuseStep 9062459 = 13593689) B13593689
theorem B66963617 : Blo 1630514 66963617 := bstep (se 2 (by rfl) ⟨25111356, by rfl⟩ : syracuseStep 66963617 = 50222713) B50222713
theorem B7440551 : Blo 1630514 7440551 := bstep (se 1 (by rfl) ⟨5580413, by rfl⟩ : syracuseStep 7440551 = 11160827) B11160827
theorem B1632463 : Blo 1630514 1632463 := bstep (se 1 (by rfl) ⟨1224347, by rfl⟩ : syracuseStep 1632463 = 2448695) B2448695
theorem B9922925 : Blo 1630514 9922925 := bstep (se 3 (by rfl) ⟨1860548, by rfl⟩ : syracuseStep 9922925 = 3721097) B3721097
theorem B2206121 : Blo 1630514 2206121 := bstep (se 2 (by rfl) ⟨827295, by rfl⟩ : syracuseStep 2206121 = 1654591) B1654591
theorem B5507675 : Blo 1630514 5507675 := bstep (se 1 (by rfl) ⟨4130756, by rfl⟩ : syracuseStep 5507675 = 8261513) B8261513
theorem B8260541 : Blo 1630514 8260541 := bstep (se 3 (by rfl) ⟨1548851, by rfl⟩ : syracuseStep 8260541 = 3097703) B3097703
theorem B31804811 : Blo 1630514 31804811 := bstep (se 1 (by rfl) ⟨23853608, by rfl⟩ : syracuseStep 31804811 = 47707217) B47707217
theorem B47066669 : Blo 1630514 47066669 := bstep (se 3 (by rfl) ⟨8825000, by rfl⟩ : syracuseStep 47066669 = 17650001) B17650001
theorem B18574919 : Blo 1630514 18574919 := bstep (se 1 (by rfl) ⟨13931189, by rfl⟩ : syracuseStep 18574919 = 27862379) B27862379
theorem B17633047 : Blo 1630514 17633047 := bstep (se 1 (by rfl) ⟨13224785, by rfl⟩ : syracuseStep 17633047 = 26449571) B26449571
theorem B120713225 : Blo 1630514 120713225 := bstep (se 2 (by rfl) ⟨45267459, by rfl⟩ : syracuseStep 120713225 = 90534919) B90534919
theorem B87068915 : Blo 1630514 87068915 := bstep (se 1 (by rfl) ⟨65301686, by rfl⟩ : syracuseStep 87068915 = 130603373) B130603373
theorem B7844215 : Blo 1630514 7844215 := bstep (se 1 (by rfl) ⟨5883161, by rfl⟩ : syracuseStep 7844215 = 11766323) B11766323
theorem B2445791 : Blo 1630514 2445791 := bstep (se 1 (by rfl) ⟨1834343, by rfl⟩ : syracuseStep 2445791 = 3668687) B3668687
theorem B2978587 : Blo 1630514 2978587 := bstep (se 1 (by rfl) ⟨2233940, by rfl⟩ : syracuseStep 2978587 = 4467881) B4467881
theorem B2323255 : Blo 1630514 2323255 := bstep (se 1 (by rfl) ⟨1742441, by rfl⟩ : syracuseStep 2323255 = 3484883) B3484883
theorem B9286595 : Blo 1630514 9286595 := bstep (se 1 (by rfl) ⟨6964946, by rfl⟩ : syracuseStep 9286595 = 13929893) B13929893
theorem B2446439 : Blo 1630514 2446439 := bstep (se 1 (by rfl) ⟨1834829, by rfl⟩ : syracuseStep 2446439 = 3669659) B3669659
theorem B2446571 : Blo 1630514 2446571 := bstep (se 1 (by rfl) ⟨1834928, by rfl⟩ : syracuseStep 2446571 = 3669857) B3669857
theorem B23516729 : Blo 1630514 23516729 := bstep (se 2 (by rfl) ⟨8818773, by rfl⟩ : syracuseStep 23516729 = 17637547) B17637547
theorem B2446955 : Blo 1630514 2446955 := bstep (se 1 (by rfl) ⟨1835216, by rfl⟩ : syracuseStep 2446955 = 3670433) B3670433
theorem B6969149 : Blo 1630514 6969149 := bstep (se 3 (by rfl) ⟨1306715, by rfl⟩ : syracuseStep 6969149 = 2613431) B2613431
theorem B301537241 : Blo 1630514 301537241 := bstep (se 2 (by rfl) ⟨113076465, by rfl⟩ : syracuseStep 301537241 = 226152931) B226152931
theorem B5503571 : Blo 1630514 5503571 := bstep (se 1 (by rfl) ⟨4127678, by rfl⟩ : syracuseStep 5503571 = 8255357) B8255357
theorem B23534489 : Blo 1630514 23534489 := bstep (se 2 (by rfl) ⟨8825433, by rfl⟩ : syracuseStep 23534489 = 17650867) B17650867
theorem B15899611 : Blo 1630514 15899611 := bstep (se 1 (by rfl) ⟨11924708, by rfl⟩ : syracuseStep 15899611 = 23849417) B23849417
theorem B8256491 : Blo 1630514 8256491 := bstep (se 1 (by rfl) ⟨6192368, by rfl⟩ : syracuseStep 8256491 = 12384737) B12384737
theorem B3669065 : Blo 1630514 3669065 := bstep (se 2 (by rfl) ⟨1375899, by rfl⟩ : syracuseStep 3669065 = 2751799) B2751799
theorem B6192233 : Blo 1630514 6192233 := bstep (se 2 (by rfl) ⟨2322087, by rfl⟩ : syracuseStep 6192233 = 4644175) B4644175
theorem B4709857 : Blo 1630514 4709857 := bstep (se 2 (by rfl) ⟨1766196, by rfl⟩ : syracuseStep 4709857 = 3532393) B3532393
theorem B4963859 : Blo 1630514 4963859 := bstep (se 1 (by rfl) ⟨3722894, by rfl⟩ : syracuseStep 4963859 = 7445789) B7445789
theorem B63610535 : Blo 1630514 63610535 := bstep (se 1 (by rfl) ⟨47707901, by rfl⟩ : syracuseStep 63610535 = 95415803) B95415803
theorem B9289511 : Blo 1630514 9289511 := bstep (se 1 (by rfl) ⟨6967133, by rfl⟩ : syracuseStep 9289511 = 13934267) B13934267
theorem B1834879 : Blo 1630514 1834879 := bstep (se 1 (by rfl) ⟨1376159, by rfl⟩ : syracuseStep 1834879 = 2752319) B2752319
theorem B12386195 : Blo 1630514 12386195 := bstep (se 1 (by rfl) ⟨9289646, by rfl⟩ : syracuseStep 12386195 = 18579293) B18579293
theorem B1835167 : Blo 1630514 1835167 := bstep (se 1 (by rfl) ⟨1376375, by rfl⟩ : syracuseStep 1835167 = 2752751) B2752751
theorem B1630527 : Blo 1630514 1630527 := bstep (se 1 (by rfl) ⟨1222895, by rfl⟩ : syracuseStep 1630527 = 2445791) B2445791
theorem B1630959 : Blo 1630514 1630959 := bstep (se 1 (by rfl) ⟨1223219, by rfl⟩ : syracuseStep 1630959 = 2446439) B2446439
theorem B1631047 : Blo 1630514 1631047 := bstep (se 1 (by rfl) ⟨1223285, by rfl⟩ : syracuseStep 1631047 = 2446571) B2446571
theorem B29754317 : Blo 1630514 29754317 := bstep (se 3 (by rfl) ⟨5578934, by rfl⟩ : syracuseStep 29754317 = 11157869) B11157869
theorem B1631303 : Blo 1630514 1631303 := bstep (se 1 (by rfl) ⟨1223477, by rfl⟩ : syracuseStep 1631303 = 2446955) B2446955
theorem B3097673 : Blo 1630514 3097673 := bstep (se 2 (by rfl) ⟨1161627, by rfl⟩ : syracuseStep 3097673 = 2323255) B2323255
theorem B5882989 : Blo 1630514 5882989 := bstep (se 3 (by rfl) ⟨1103060, by rfl⟩ : syracuseStep 5882989 = 2206121) B2206121
theorem B4646099 : Blo 1630514 4646099 := bstep (se 1 (by rfl) ⟨3484574, by rfl⟩ : syracuseStep 4646099 = 6969149) B6969149
theorem B201024827 : Blo 1630514 201024827 := bstep (se 1 (by rfl) ⟨150768620, by rfl⟩ : syracuseStep 201024827 = 301537241) B301537241
theorem B4130473 : Blo 1630514 4130473 := bstep (se 2 (by rfl) ⟨1548927, by rfl⟩ : syracuseStep 4130473 = 3097855) B3097855
theorem B3671783 : Blo 1630514 3671783 := bstep (se 1 (by rfl) ⟨2753837, by rfl⟩ : syracuseStep 3671783 = 5507675) B5507675
theorem B15689659 : Blo 1630514 15689659 := bstep (se 1 (by rfl) ⟨11767244, by rfl⟩ : syracuseStep 15689659 = 23534489) B23534489
theorem B5507027 : Blo 1630514 5507027 := bstep (se 1 (by rfl) ⟨4130270, by rfl⟩ : syracuseStep 5507027 = 8260541) B8260541
theorem B100476949 : Blo 1630514 100476949 := bstep (se 6 (by rfl) ⟨2354928, by rfl⟩ : syracuseStep 100476949 = 4709857) B4709857
theorem B3672233 : Blo 1630514 3672233 := bstep (se 2 (by rfl) ⟨1377087, by rfl⟩ : syracuseStep 3672233 = 2754175) B2754175
theorem B21203207 : Blo 1630514 21203207 := bstep (se 1 (by rfl) ⟨15902405, by rfl⟩ : syracuseStep 21203207 = 31804811) B31804811
theorem B31377779 : Blo 1630514 31377779 := bstep (se 1 (by rfl) ⟨23533334, by rfl⟩ : syracuseStep 31377779 = 47066669) B47066669
theorem B8260217 : Blo 1630514 8260217 := bstep (se 2 (by rfl) ⟨3097581, by rfl⟩ : syracuseStep 8260217 = 6195163) B6195163
theorem B13937615 : Blo 1630514 13937615 := bstep (se 1 (by rfl) ⟨10453211, by rfl⟩ : syracuseStep 13937615 = 20906423) B20906423
theorem B53653391 : Blo 1630514 53653391 := bstep (se 1 (by rfl) ⟨40240043, by rfl⟩ : syracuseStep 53653391 = 80480087) B80480087
theorem B6041639 : Blo 1630514 6041639 := bstep (se 1 (by rfl) ⟨4531229, by rfl⟩ : syracuseStep 6041639 = 9062459) B9062459
theorem B44642411 : Blo 1630514 44642411 := bstep (se 1 (by rfl) ⟨33481808, by rfl⟩ : syracuseStep 44642411 = 66963617) B66963617
theorem B4960367 : Blo 1630514 4960367 := bstep (se 1 (by rfl) ⟨3720275, by rfl⟩ : syracuseStep 4960367 = 7440551) B7440551
theorem B6615283 : Blo 1630514 6615283 := bstep (se 1 (by rfl) ⟨4961462, by rfl⟩ : syracuseStep 6615283 = 9922925) B9922925
theorem B2446043 : Blo 1630514 2446043 := bstep (se 1 (by rfl) ⟨1834532, by rfl⟩ : syracuseStep 2446043 = 3669065) B3669065
theorem B12383279 : Blo 1630514 12383279 := bstep (se 1 (by rfl) ⟨9287459, by rfl⟩ : syracuseStep 12383279 = 18574919) B18574919
theorem B42407023 : Blo 1630514 42407023 := bstep (se 1 (by rfl) ⟨31805267, by rfl⟩ : syracuseStep 42407023 = 63610535) B63610535
theorem B2446505 : Blo 1630514 2446505 := bstep (se 2 (by rfl) ⟨917439, by rfl⟩ : syracuseStep 2446505 = 1834879) B1834879
theorem B321901933 : Blo 1630514 321901933 := bstep (se 3 (by rfl) ⟨60356612, by rfl⟩ : syracuseStep 321901933 = 120713225) B120713225
theorem B20911547 : Blo 1630514 20911547 := bstep (se 1 (by rfl) ⟨15683660, by rfl⟩ : syracuseStep 20911547 = 31367321) B31367321
theorem B58045943 : Blo 1630514 58045943 := bstep (se 1 (by rfl) ⟨43534457, by rfl⟩ : syracuseStep 58045943 = 87068915) B87068915
theorem B10458953 : Blo 1630514 10458953 := bstep (se 2 (by rfl) ⟨3922107, by rfl⟩ : syracuseStep 10458953 = 7844215) B7844215
theorem B6191063 : Blo 1630514 6191063 := bstep (se 1 (by rfl) ⟨4643297, by rfl⟩ : syracuseStep 6191063 = 9286595) B9286595
theorem B2447387 : Blo 1630514 2447387 := bstep (se 1 (by rfl) ⟨1835540, by rfl⟩ : syracuseStep 2447387 = 3671081) B3671081
theorem B29775923 : Blo 1630514 29775923 := bstep (se 1 (by rfl) ⟨22331942, by rfl⟩ : syracuseStep 29775923 = 44663885) B44663885
theorem B2447423 : Blo 1630514 2447423 := bstep (se 1 (by rfl) ⟨1835567, by rfl⟩ : syracuseStep 2447423 = 3671135) B3671135
theorem B3971449 : Blo 1630514 3971449 := bstep (se 2 (by rfl) ⟨1489293, by rfl⟩ : syracuseStep 3971449 = 2978587) B2978587
theorem B15677819 : Blo 1630514 15677819 := bstep (se 1 (by rfl) ⟨11758364, by rfl⟩ : syracuseStep 15677819 = 23516729) B23516729
theorem B2447963 : Blo 1630514 2447963 := bstep (se 1 (by rfl) ⟨1835972, by rfl⟩ : syracuseStep 2447963 = 3671945) B3671945
theorem B2447975 : Blo 1630514 2447975 := bstep (se 1 (by rfl) ⟨1835981, by rfl⟩ : syracuseStep 2447975 = 3671963) B3671963
theorem B21199481 : Blo 1630514 21199481 := bstep (se 2 (by rfl) ⟨7949805, by rfl⟩ : syracuseStep 21199481 = 15899611) B15899611
theorem B2448041 : Blo 1630514 2448041 := bstep (se 2 (by rfl) ⟨918015, by rfl⟩ : syracuseStep 2448041 = 1836031) B1836031
theorem B3669047 : Blo 1630514 3669047 := bstep (se 1 (by rfl) ⟨2751785, by rfl⟩ : syracuseStep 3669047 = 5503571) B5503571
theorem B5504327 : Blo 1630514 5504327 := bstep (se 1 (by rfl) ⟨4128245, by rfl⟩ : syracuseStep 5504327 = 8256491) B8256491
theorem B4128155 : Blo 1630514 4128155 := bstep (se 1 (by rfl) ⟨3096116, by rfl⟩ : syracuseStep 4128155 = 6192233) B6192233
theorem B3309239 : Blo 1630514 3309239 := bstep (se 1 (by rfl) ⟨2481929, by rfl⟩ : syracuseStep 3309239 = 4963859) B4963859
theorem B23510729 : Blo 1630514 23510729 := bstep (se 2 (by rfl) ⟨8816523, by rfl⟩ : syracuseStep 23510729 = 17633047) B17633047
theorem B6193007 : Blo 1630514 6193007 := bstep (se 1 (by rfl) ⟨4644755, by rfl⟩ : syracuseStep 6193007 = 9289511) B9289511
theorem B8257463 : Blo 1630514 8257463 := bstep (se 1 (by rfl) ⟨6193097, by rfl⟩ : syracuseStep 8257463 = 12386195) B12386195
theorem B29761607 : Blo 1630514 29761607 := bstep (se 1 (by rfl) ⟨22321205, by rfl⟩ : syracuseStep 29761607 = 44642411) B44642411
theorem B1630695 : Blo 1630514 1630695 := bstep (se 1 (by rfl) ⟨1223021, by rfl⟩ : syracuseStep 1630695 = 2446043) B2446043
theorem B2065115 : Blo 1630514 2065115 := bstep (se 1 (by rfl) ⟨1548836, by rfl⟩ : syracuseStep 2065115 = 3097673) B3097673
theorem B1631003 : Blo 1630514 1631003 := bstep (se 1 (by rfl) ⟨1223252, by rfl⟩ : syracuseStep 1631003 = 2446505) B2446505
theorem B6972635 : Blo 1630514 6972635 := bstep (se 1 (by rfl) ⟨5229476, by rfl⟩ : syracuseStep 6972635 = 10458953) B10458953
theorem B3671351 : Blo 1630514 3671351 := bstep (se 1 (by rfl) ⟨2753513, by rfl⟩ : syracuseStep 3671351 = 5507027) B5507027
theorem B154789181 : Blo 1630514 154789181 := bstep (se 3 (by rfl) ⟨29022971, by rfl⟩ : syracuseStep 154789181 = 58045943) B58045943
theorem B1631591 : Blo 1630514 1631591 := bstep (se 1 (by rfl) ⟨1223693, by rfl⟩ : syracuseStep 1631591 = 2447387) B2447387
theorem B19850615 : Blo 1630514 19850615 := bstep (se 1 (by rfl) ⟨14887961, by rfl⟩ : syracuseStep 19850615 = 29775923) B29775923
theorem B1631615 : Blo 1630514 1631615 := bstep (se 1 (by rfl) ⟨1223711, by rfl⟩ : syracuseStep 1631615 = 2447423) B2447423
theorem B56542697 : Blo 1630514 56542697 := bstep (se 2 (by rfl) ⟨21203511, by rfl⟩ : syracuseStep 56542697 = 42407023) B42407023
theorem B1631975 : Blo 1630514 1631975 := bstep (se 1 (by rfl) ⟨1223981, by rfl⟩ : syracuseStep 1631975 = 2447963) B2447963
theorem B1631983 : Blo 1630514 1631983 := bstep (se 1 (by rfl) ⟨1223987, by rfl⟩ : syracuseStep 1631983 = 2447975) B2447975
theorem B5506811 : Blo 1630514 5506811 := bstep (se 1 (by rfl) ⟨4130108, by rfl⟩ : syracuseStep 5506811 = 8260217) B8260217
theorem B14132987 : Blo 1630514 14132987 := bstep (se 1 (by rfl) ⟨10599740, by rfl⟩ : syracuseStep 14132987 = 21199481) B21199481
theorem B1632027 : Blo 1630514 1632027 := bstep (se 1 (by rfl) ⟨1224020, by rfl⟩ : syracuseStep 1632027 = 2448041) B2448041
theorem B9291743 : Blo 1630514 9291743 := bstep (se 1 (by rfl) ⟨6968807, by rfl⟩ : syracuseStep 9291743 = 13937615) B13937615
theorem B5507297 : Blo 1630514 5507297 := bstep (se 2 (by rfl) ⟨2065236, by rfl⟩ : syracuseStep 5507297 = 4130473) B4130473
theorem B2206159 : Blo 1630514 2206159 := bstep (se 1 (by rfl) ⟨1654619, by rfl⟩ : syracuseStep 2206159 = 3309239) B3309239
theorem B15673819 : Blo 1630514 15673819 := bstep (se 1 (by rfl) ⟨11755364, by rfl⟩ : syracuseStep 15673819 = 23510729) B23510729
theorem B35768927 : Blo 1630514 35768927 := bstep (se 1 (by rfl) ⟨26826695, by rfl⟩ : syracuseStep 35768927 = 53653391) B53653391
theorem B12389597 : Blo 1630514 12389597 := bstep (se 3 (by rfl) ⟨2323049, by rfl⟩ : syracuseStep 12389597 = 4646099) B4646099
theorem B19836211 : Blo 1630514 19836211 := bstep (se 1 (by rfl) ⟨14877158, by rfl⟩ : syracuseStep 19836211 = 29754317) B29754317
theorem B134016551 : Blo 1630514 134016551 := bstep (se 1 (by rfl) ⟨100512413, by rfl⟩ : syracuseStep 134016551 = 201024827) B201024827
theorem B7843985 : Blo 1630514 7843985 := bstep (se 2 (by rfl) ⟨2941494, by rfl⟩ : syracuseStep 7843985 = 5882989) B5882989
theorem B14135471 : Blo 1630514 14135471 := bstep (se 1 (by rfl) ⟨10601603, by rfl⟩ : syracuseStep 14135471 = 21203207) B21203207
theorem B20918519 : Blo 1630514 20918519 := bstep (se 1 (by rfl) ⟨15688889, by rfl⟩ : syracuseStep 20918519 = 31377779) B31377779
theorem B21181061 : Blo 1630514 21181061 := bstep (se 4 (by rfl) ⟨1985724, by rfl⟩ : syracuseStep 21181061 = 3971449) B3971449
theorem B2446031 : Blo 1630514 2446031 := bstep (se 1 (by rfl) ⟨1834523, by rfl⟩ : syracuseStep 2446031 = 3669047) B3669047
theorem B20919545 : Blo 1630514 20919545 := bstep (se 2 (by rfl) ⟨7844829, by rfl⟩ : syracuseStep 20919545 = 15689659) B15689659
theorem B133969265 : Blo 1630514 133969265 := bstep (se 2 (by rfl) ⟨50238474, by rfl⟩ : syracuseStep 133969265 = 100476949) B100476949
theorem B3306911 : Blo 1630514 3306911 := bstep (se 1 (by rfl) ⟨2480183, by rfl⟩ : syracuseStep 3306911 = 4960367) B4960367
theorem B16111037 : Blo 1630514 16111037 := bstep (se 3 (by rfl) ⟨3020819, by rfl⟩ : syracuseStep 16111037 = 6041639) B6041639
theorem B2446889 : Blo 1630514 2446889 := bstep (se 2 (by rfl) ⟨917583, by rfl⟩ : syracuseStep 2446889 = 1835167) B1835167
theorem B8820377 : Blo 1630514 8820377 := bstep (se 2 (by rfl) ⟨3307641, by rfl⟩ : syracuseStep 8820377 = 6615283) B6615283
theorem B8255519 : Blo 1630514 8255519 := bstep (se 1 (by rfl) ⟨6191639, by rfl⟩ : syracuseStep 8255519 = 12383279) B12383279
theorem B13941031 : Blo 1630514 13941031 := bstep (se 1 (by rfl) ⟨10455773, by rfl⟩ : syracuseStep 13941031 = 20911547) B20911547
theorem B2447855 : Blo 1630514 2447855 := bstep (se 1 (by rfl) ⟨1835891, by rfl⟩ : syracuseStep 2447855 = 3671783) B3671783
theorem B4127375 : Blo 1630514 4127375 := bstep (se 1 (by rfl) ⟨3095531, by rfl⟩ : syracuseStep 4127375 = 6191063) B6191063
theorem B2448155 : Blo 1630514 2448155 := bstep (se 1 (by rfl) ⟨1836116, by rfl⟩ : syracuseStep 2448155 = 3672233) B3672233
theorem B10451879 : Blo 1630514 10451879 := bstep (se 1 (by rfl) ⟨7838909, by rfl⟩ : syracuseStep 10451879 = 15677819) B15677819
theorem B429202577 : Blo 1630514 429202577 := bstep (se 2 (by rfl) ⟨160950966, by rfl⟩ : syracuseStep 429202577 = 321901933) B321901933
theorem B3669551 : Blo 1630514 3669551 := bstep (se 1 (by rfl) ⟨2752163, by rfl⟩ : syracuseStep 3669551 = 5504327) B5504327
theorem B2752103 : Blo 1630514 2752103 := bstep (se 1 (by rfl) ⟨2064077, by rfl⟩ : syracuseStep 2752103 = 4128155) B4128155
theorem B4128671 : Blo 1630514 4128671 := bstep (se 1 (by rfl) ⟨3096503, by rfl⟩ : syracuseStep 4128671 = 6193007) B6193007
theorem B5504975 : Blo 1630514 5504975 := bstep (se 1 (by rfl) ⟨4128731, by rfl⟩ : syracuseStep 5504975 = 8257463) B8257463
theorem B79364285 : Blo 1630514 79364285 := bstep (se 3 (by rfl) ⟨14880803, by rfl⟩ : syracuseStep 79364285 = 29761607) B29761607
theorem B18588041 : Blo 1630514 18588041 := bstep (se 2 (by rfl) ⟨6970515, by rfl⟩ : syracuseStep 18588041 = 13941031) B13941031
theorem B1630687 : Blo 1630514 1630687 := bstep (se 1 (by rfl) ⟨1223015, by rfl⟩ : syracuseStep 1630687 = 2446031) B2446031
theorem B20898425 : Blo 1630514 20898425 := bstep (se 2 (by rfl) ⟨7836909, by rfl⟩ : syracuseStep 20898425 = 15673819) B15673819
theorem B10740691 : Blo 1630514 10740691 := bstep (se 1 (by rfl) ⟨8055518, by rfl⟩ : syracuseStep 10740691 = 16111037) B16111037
theorem B1631259 : Blo 1630514 1631259 := bstep (se 1 (by rfl) ⟨1223444, by rfl⟩ : syracuseStep 1631259 = 2446889) B2446889
theorem B3671207 : Blo 1630514 3671207 := bstep (se 1 (by rfl) ⟨2753405, by rfl⟩ : syracuseStep 3671207 = 5506811) B5506811
theorem B9421991 : Blo 1630514 9421991 := bstep (se 1 (by rfl) ⟨7066493, by rfl⟩ : syracuseStep 9421991 = 14132987) B14132987
theorem B6194495 : Blo 1630514 6194495 := bstep (se 1 (by rfl) ⟨4645871, by rfl⟩ : syracuseStep 6194495 = 9291743) B9291743
theorem B3671531 : Blo 1630514 3671531 := bstep (se 1 (by rfl) ⟨2753648, by rfl⟩ : syracuseStep 3671531 = 5507297) B5507297
theorem B1631903 : Blo 1630514 1631903 := bstep (se 1 (by rfl) ⟨1223927, by rfl⟩ : syracuseStep 1631903 = 2447855) B2447855
theorem B1632103 : Blo 1630514 1632103 := bstep (se 1 (by rfl) ⟨1224077, by rfl⟩ : syracuseStep 1632103 = 2448155) B2448155
theorem B5506973 : Blo 1630514 5506973 := bstep (se 3 (by rfl) ⟨1032557, by rfl⟩ : syracuseStep 5506973 = 2065115) B2065115
theorem B8259731 : Blo 1630514 8259731 := bstep (se 1 (by rfl) ⟨6194798, by rfl⟩ : syracuseStep 8259731 = 12389597) B12389597
theorem B89344367 : Blo 1630514 89344367 := bstep (se 1 (by rfl) ⟨67008275, by rfl⟩ : syracuseStep 89344367 = 134016551) B134016551
theorem B11766181 : Blo 1630514 11766181 := bstep (se 4 (by rfl) ⟨1103079, by rfl⟩ : syracuseStep 11766181 = 2206159) B2206159
theorem B5229323 : Blo 1630514 5229323 := bstep (se 1 (by rfl) ⟨3921992, by rfl⟩ : syracuseStep 5229323 = 7843985) B7843985
theorem B9423647 : Blo 1630514 9423647 := bstep (se 1 (by rfl) ⟨7067735, by rfl⟩ : syracuseStep 9423647 = 14135471) B14135471
theorem B13945679 : Blo 1630514 13945679 := bstep (se 1 (by rfl) ⟨10459259, by rfl⟩ : syracuseStep 13945679 = 20918519) B20918519
theorem B1144540205 : Blo 1630514 1144540205 := bstep (se 3 (by rfl) ⟨214601288, by rfl⟩ : syracuseStep 1144540205 = 429202577) B429202577
theorem B4648423 : Blo 1630514 4648423 := bstep (se 1 (by rfl) ⟨3486317, by rfl⟩ : syracuseStep 4648423 = 6972635) B6972635
theorem B13946363 : Blo 1630514 13946363 := bstep (se 1 (by rfl) ⟨10459772, by rfl⟩ : syracuseStep 13946363 = 20919545) B20919545
theorem B89312843 : Blo 1630514 89312843 := bstep (se 1 (by rfl) ⟨66984632, by rfl⟩ : syracuseStep 89312843 = 133969265) B133969265
theorem B13233743 : Blo 1630514 13233743 := bstep (se 1 (by rfl) ⟨9925307, by rfl⟩ : syracuseStep 13233743 = 19850615) B19850615
theorem B37695131 : Blo 1630514 37695131 := bstep (se 1 (by rfl) ⟨28271348, by rfl⟩ : syracuseStep 37695131 = 56542697) B56542697
theorem B8818429 : Blo 1630514 8818429 := bstep (se 3 (by rfl) ⟨1653455, by rfl⟩ : syracuseStep 8818429 = 3306911) B3306911
theorem B26448281 : Blo 1630514 26448281 := bstep (se 2 (by rfl) ⟨9918105, by rfl⟩ : syracuseStep 26448281 = 19836211) B19836211
theorem B6967919 : Blo 1630514 6967919 := bstep (se 1 (by rfl) ⟨5225939, by rfl⟩ : syracuseStep 6967919 = 10451879) B10451879
theorem B2446367 : Blo 1630514 2446367 := bstep (se 1 (by rfl) ⟨1834775, by rfl⟩ : syracuseStep 2446367 = 3669551) B3669551
theorem B2447567 : Blo 1630514 2447567 := bstep (se 1 (by rfl) ⟨1835675, by rfl⟩ : syracuseStep 2447567 = 3671351) B3671351
theorem B103192787 : Blo 1630514 103192787 := bstep (se 1 (by rfl) ⟨77394590, by rfl⟩ : syracuseStep 103192787 = 154789181) B154789181
theorem B5880251 : Blo 1630514 5880251 := bstep (se 1 (by rfl) ⟨4410188, by rfl⟩ : syracuseStep 5880251 = 8820377) B8820377
theorem B5503679 : Blo 1630514 5503679 := bstep (se 1 (by rfl) ⟨4127759, by rfl⟩ : syracuseStep 5503679 = 8255519) B8255519
theorem B56482829 : Blo 1630514 56482829 := bstep (se 3 (by rfl) ⟨10590530, by rfl⟩ : syracuseStep 56482829 = 21181061) B21181061
theorem B23845951 : Blo 1630514 23845951 := bstep (se 1 (by rfl) ⟨17884463, by rfl⟩ : syracuseStep 23845951 = 35768927) B35768927
theorem B2751583 : Blo 1630514 2751583 := bstep (se 1 (by rfl) ⟨2063687, by rfl⟩ : syracuseStep 2751583 = 4127375) B4127375
theorem B1834735 : Blo 1630514 1834735 := bstep (se 1 (by rfl) ⟨1376051, by rfl⟩ : syracuseStep 1834735 = 2752103) B2752103
theorem B2752447 : Blo 1630514 2752447 := bstep (se 1 (by rfl) ⟨2064335, by rfl⟩ : syracuseStep 2752447 = 4128671) B4128671
theorem B3669983 : Blo 1630514 3669983 := bstep (se 1 (by rfl) ⟨2752487, by rfl⟩ : syracuseStep 3669983 = 5504975) B5504975
theorem B4645279 : Blo 1630514 4645279 := bstep (se 1 (by rfl) ⟨3483959, by rfl⟩ : syracuseStep 4645279 = 6967919) B6967919
theorem B15688241 : Blo 1630514 15688241 := bstep (se 2 (by rfl) ⟨5883090, by rfl⟩ : syracuseStep 15688241 = 11766181) B11766181
theorem B1630911 : Blo 1630514 1630911 := bstep (se 1 (by rfl) ⟨1223183, by rfl⟩ : syracuseStep 1630911 = 2446367) B2446367
theorem B4129663 : Blo 1630514 4129663 := bstep (se 1 (by rfl) ⟨3097247, by rfl⟩ : syracuseStep 4129663 = 6194495) B6194495
theorem B3671315 : Blo 1630514 3671315 := bstep (se 1 (by rfl) ⟨2753486, by rfl⟩ : syracuseStep 3671315 = 5506973) B5506973
theorem B14320921 : Blo 1630514 14320921 := bstep (se 2 (by rfl) ⟨5370345, by rfl⟩ : syracuseStep 14320921 = 10740691) B10740691
theorem B31794601 : Blo 1630514 31794601 := bstep (se 2 (by rfl) ⟨11922975, by rfl⟩ : syracuseStep 31794601 = 23845951) B23845951
theorem B5506487 : Blo 1630514 5506487 := bstep (se 1 (by rfl) ⟨4129865, by rfl⟩ : syracuseStep 5506487 = 8259731) B8259731
theorem B1631711 : Blo 1630514 1631711 := bstep (se 1 (by rfl) ⟨1223783, by rfl⟩ : syracuseStep 1631711 = 2447567) B2447567
theorem B11757905 : Blo 1630514 11757905 := bstep (se 2 (by rfl) ⟨4409214, by rfl⟩ : syracuseStep 11757905 = 8818429) B8818429
theorem B59541895 : Blo 1630514 59541895 := bstep (se 1 (by rfl) ⟨44656421, by rfl⟩ : syracuseStep 59541895 = 89312843) B89312843
theorem B17632187 : Blo 1630514 17632187 := bstep (se 1 (by rfl) ⟨13224140, by rfl⟩ : syracuseStep 17632187 = 26448281) B26448281
theorem B3920167 : Blo 1630514 3920167 := bstep (se 1 (by rfl) ⟨2940125, by rfl⟩ : syracuseStep 3920167 = 5880251) B5880251
theorem B3486215 : Blo 1630514 3486215 := bstep (se 1 (by rfl) ⟨2614661, by rfl⟩ : syracuseStep 3486215 = 5229323) B5229323
theorem B6197897 : Blo 1630514 6197897 := bstep (se 2 (by rfl) ⟨2324211, by rfl⟩ : syracuseStep 6197897 = 4648423) B4648423
theorem B37655219 : Blo 1630514 37655219 := bstep (se 1 (by rfl) ⟨28241414, by rfl⟩ : syracuseStep 37655219 = 56482829) B56482829
theorem B2446313 : Blo 1630514 2446313 := bstep (se 2 (by rfl) ⟨917367, by rfl⟩ : syracuseStep 2446313 = 1834735) B1834735
theorem B25130087 : Blo 1630514 25130087 := bstep (se 1 (by rfl) ⟨18847565, by rfl⟩ : syracuseStep 25130087 = 37695131) B37695131
theorem B2446655 : Blo 1630514 2446655 := bstep (se 1 (by rfl) ⟨1834991, by rfl⟩ : syracuseStep 2446655 = 3669983) B3669983
theorem B52909523 : Blo 1630514 52909523 := bstep (se 1 (by rfl) ⟨39682142, by rfl⟩ : syracuseStep 52909523 = 79364285) B79364285
theorem B12392027 : Blo 1630514 12392027 := bstep (se 1 (by rfl) ⟨9294020, by rfl⟩ : syracuseStep 12392027 = 18588041) B18588041
theorem B13932283 : Blo 1630514 13932283 := bstep (se 1 (by rfl) ⟨10449212, by rfl⟩ : syracuseStep 13932283 = 20898425) B20898425
theorem B2447471 : Blo 1630514 2447471 := bstep (se 1 (by rfl) ⟨1835603, by rfl⟩ : syracuseStep 2447471 = 3671207) B3671207
theorem B6281327 : Blo 1630514 6281327 := bstep (se 1 (by rfl) ⟨4710995, by rfl⟩ : syracuseStep 6281327 = 9421991) B9421991
theorem B2447687 : Blo 1630514 2447687 := bstep (se 1 (by rfl) ⟨1835765, by rfl⟩ : syracuseStep 2447687 = 3671531) B3671531
theorem B3668777 : Blo 1630514 3668777 := bstep (se 2 (by rfl) ⟨1375791, by rfl⟩ : syracuseStep 3668777 = 2751583) B2751583
theorem B68795191 : Blo 1630514 68795191 := bstep (se 1 (by rfl) ⟨51596393, by rfl⟩ : syracuseStep 68795191 = 103192787) B103192787
theorem B59562911 : Blo 1630514 59562911 := bstep (se 1 (by rfl) ⟨44672183, by rfl⟩ : syracuseStep 59562911 = 89344367) B89344367
theorem B3669119 : Blo 1630514 3669119 := bstep (se 1 (by rfl) ⟨2751839, by rfl⟩ : syracuseStep 3669119 = 5503679) B5503679
theorem B6282431 : Blo 1630514 6282431 := bstep (se 1 (by rfl) ⟨4711823, by rfl⟩ : syracuseStep 6282431 = 9423647) B9423647
theorem B9297119 : Blo 1630514 9297119 := bstep (se 1 (by rfl) ⟨6972839, by rfl⟩ : syracuseStep 9297119 = 13945679) B13945679
theorem B763026803 : Blo 1630514 763026803 := bstep (se 1 (by rfl) ⟨572270102, by rfl⟩ : syracuseStep 763026803 = 1144540205) B1144540205
theorem B9297575 : Blo 1630514 9297575 := bstep (se 1 (by rfl) ⟨6973181, by rfl⟩ : syracuseStep 9297575 = 13946363) B13946363
theorem B8822495 : Blo 1630514 8822495 := bstep (se 1 (by rfl) ⟨6616871, by rfl⟩ : syracuseStep 8822495 = 13233743) B13233743
theorem B3669929 : Blo 1630514 3669929 := bstep (se 2 (by rfl) ⟨1376223, by rfl⟩ : syracuseStep 3669929 = 2752447) B2752447
theorem B5226889 : Blo 1630514 5226889 := bstep (se 2 (by rfl) ⟨1960083, by rfl⟩ : syracuseStep 5226889 = 3920167) B3920167
theorem B79389193 : Blo 1630514 79389193 := bstep (se 2 (by rfl) ⟨29770947, by rfl⟩ : syracuseStep 79389193 = 59541895) B59541895
theorem B6193705 : Blo 1630514 6193705 := bstep (se 2 (by rfl) ⟨2322639, by rfl⟩ : syracuseStep 6193705 = 4645279) B4645279
theorem B1630875 : Blo 1630514 1630875 := bstep (se 1 (by rfl) ⟨1223156, by rfl⟩ : syracuseStep 1630875 = 2446313) B2446313
theorem B16753391 : Blo 1630514 16753391 := bstep (se 1 (by rfl) ⟨12565043, by rfl⟩ : syracuseStep 16753391 = 25130087) B25130087
theorem B1631103 : Blo 1630514 1631103 := bstep (se 1 (by rfl) ⟨1223327, by rfl⟩ : syracuseStep 1631103 = 2446655) B2446655
theorem B3670991 : Blo 1630514 3670991 := bstep (se 1 (by rfl) ⟨2753243, by rfl⟩ : syracuseStep 3670991 = 5506487) B5506487
theorem B91726921 : Blo 1630514 91726921 := bstep (se 2 (by rfl) ⟨34397595, by rfl⟩ : syracuseStep 91726921 = 68795191) B68795191
theorem B5506217 : Blo 1630514 5506217 := bstep (se 2 (by rfl) ⟨2064831, by rfl⟩ : syracuseStep 5506217 = 4129663) B4129663
theorem B1631647 : Blo 1630514 1631647 := bstep (se 1 (by rfl) ⟨1223735, by rfl⟩ : syracuseStep 1631647 = 2447471) B2447471
theorem B4187551 : Blo 1630514 4187551 := bstep (se 1 (by rfl) ⟨3140663, by rfl⟩ : syracuseStep 4187551 = 6281327) B6281327
theorem B1631791 : Blo 1630514 1631791 := bstep (se 1 (by rfl) ⟨1223843, by rfl⟩ : syracuseStep 1631791 = 2447687) B2447687
theorem B4188287 : Blo 1630514 4188287 := bstep (se 1 (by rfl) ⟨3141215, by rfl⟩ : syracuseStep 4188287 = 6282431) B6282431
theorem B508684535 : Blo 1630514 508684535 := bstep (se 1 (by rfl) ⟨381513401, by rfl⟩ : syracuseStep 508684535 = 763026803) B763026803
theorem B4131931 : Blo 1630514 4131931 := bstep (se 1 (by rfl) ⟨3098948, by rfl⟩ : syracuseStep 4131931 = 6197897) B6197897
theorem B25103479 : Blo 1630514 25103479 := bstep (se 1 (by rfl) ⟨18827609, by rfl⟩ : syracuseStep 25103479 = 37655219) B37655219
theorem B8261351 : Blo 1630514 8261351 := bstep (se 1 (by rfl) ⟨6196013, by rfl⟩ : syracuseStep 8261351 = 12392027) B12392027
theorem B2445851 : Blo 1630514 2445851 := bstep (se 1 (by rfl) ⟨1834388, by rfl⟩ : syracuseStep 2445851 = 3668777) B3668777
theorem B2446079 : Blo 1630514 2446079 := bstep (se 1 (by rfl) ⟨1834559, by rfl⟩ : syracuseStep 2446079 = 3669119) B3669119
theorem B6198079 : Blo 1630514 6198079 := bstep (se 1 (by rfl) ⟨4648559, by rfl⟩ : syracuseStep 6198079 = 9297119) B9297119
theorem B18576377 : Blo 1630514 18576377 := bstep (se 2 (by rfl) ⟨6966141, by rfl⟩ : syracuseStep 18576377 = 13932283) B13932283
theorem B6198383 : Blo 1630514 6198383 := bstep (se 1 (by rfl) ⟨4648787, by rfl⟩ : syracuseStep 6198383 = 9297575) B9297575
theorem B2446619 : Blo 1630514 2446619 := bstep (se 1 (by rfl) ⟨1834964, by rfl⟩ : syracuseStep 2446619 = 3669929) B3669929
theorem B2324143 : Blo 1630514 2324143 := bstep (se 1 (by rfl) ⟨1743107, by rfl⟩ : syracuseStep 2324143 = 3486215) B3486215
theorem B10458827 : Blo 1630514 10458827 := bstep (se 1 (by rfl) ⟨7844120, by rfl⟩ : syracuseStep 10458827 = 15688241) B15688241
theorem B2447543 : Blo 1630514 2447543 := bstep (se 1 (by rfl) ⟨1835657, by rfl⟩ : syracuseStep 2447543 = 3671315) B3671315
theorem B35273015 : Blo 1630514 35273015 := bstep (se 1 (by rfl) ⟨26454761, by rfl⟩ : syracuseStep 35273015 = 52909523) B52909523
theorem B7838603 : Blo 1630514 7838603 := bstep (se 1 (by rfl) ⟨5878952, by rfl⟩ : syracuseStep 7838603 = 11757905) B11757905
theorem B19094561 : Blo 1630514 19094561 := bstep (se 2 (by rfl) ⟨7160460, by rfl⟩ : syracuseStep 19094561 = 14320921) B14320921
theorem B42392801 : Blo 1630514 42392801 := bstep (se 2 (by rfl) ⟨15897300, by rfl⟩ : syracuseStep 42392801 = 31794601) B31794601
theorem B11754791 : Blo 1630514 11754791 := bstep (se 1 (by rfl) ⟨8816093, by rfl⟩ : syracuseStep 11754791 = 17632187) B17632187
theorem B158834429 : Blo 1630514 158834429 := bstep (se 3 (by rfl) ⟨29781455, by rfl⟩ : syracuseStep 158834429 = 59562911) B59562911
theorem B5881663 : Blo 1630514 5881663 := bstep (se 1 (by rfl) ⟨4411247, by rfl⟩ : syracuseStep 5881663 = 8822495) B8822495
theorem B1630567 : Blo 1630514 1630567 := bstep (se 1 (by rfl) ⟨1222925, by rfl⟩ : syracuseStep 1630567 = 2445851) B2445851
theorem B1630719 : Blo 1630514 1630719 := bstep (se 1 (by rfl) ⟨1223039, by rfl⟩ : syracuseStep 1630719 = 2446079) B2446079
theorem B8258273 : Blo 1630514 8258273 := bstep (se 2 (by rfl) ⟨3096852, by rfl⟩ : syracuseStep 8258273 = 6193705) B6193705
theorem B3670811 : Blo 1630514 3670811 := bstep (se 1 (by rfl) ⟨2753108, by rfl⟩ : syracuseStep 3670811 = 5506217) B5506217
theorem B1631079 : Blo 1630514 1631079 := bstep (se 1 (by rfl) ⟨1223309, by rfl⟩ : syracuseStep 1631079 = 2446619) B2446619
theorem B12395429 : Blo 1630514 12395429 := bstep (se 4 (by rfl) ⟨1162071, by rfl⟩ : syracuseStep 12395429 = 2324143) B2324143
theorem B6972551 : Blo 1630514 6972551 := bstep (se 1 (by rfl) ⟨5229413, by rfl⟩ : syracuseStep 6972551 = 10458827) B10458827
theorem B1631695 : Blo 1630514 1631695 := bstep (se 1 (by rfl) ⟨1223771, by rfl⟩ : syracuseStep 1631695 = 2447543) B2447543
theorem B7842217 : Blo 1630514 7842217 := bstep (se 2 (by rfl) ⟨2940831, by rfl⟩ : syracuseStep 7842217 = 5881663) B5881663
theorem B5507567 : Blo 1630514 5507567 := bstep (se 1 (by rfl) ⟨4130675, by rfl⟩ : syracuseStep 5507567 = 8261351) B8261351
theorem B11168765 : Blo 1630514 11168765 := bstep (se 3 (by rfl) ⟨2094143, by rfl⟩ : syracuseStep 11168765 = 4188287) B4188287
theorem B11168927 : Blo 1630514 11168927 := bstep (se 1 (by rfl) ⟨8376695, by rfl⟩ : syracuseStep 11168927 = 16753391) B16753391
theorem B105852257 : Blo 1630514 105852257 := bstep (se 2 (by rfl) ⟨39694596, by rfl⟩ : syracuseStep 105852257 = 79389193) B79389193
theorem B4132255 : Blo 1630514 4132255 := bstep (se 1 (by rfl) ⟨3099191, by rfl⟩ : syracuseStep 4132255 = 6198383) B6198383
theorem B122302561 : Blo 1630514 122302561 := bstep (se 2 (by rfl) ⟨45863460, by rfl⟩ : syracuseStep 122302561 = 91726921) B91726921
theorem B5509241 : Blo 1630514 5509241 := bstep (se 2 (by rfl) ⟨2065965, by rfl⟩ : syracuseStep 5509241 = 4131931) B4131931
theorem B23515343 : Blo 1630514 23515343 := bstep (se 1 (by rfl) ⟨17636507, by rfl⟩ : syracuseStep 23515343 = 35273015) B35273015
theorem B5583401 : Blo 1630514 5583401 := bstep (se 2 (by rfl) ⟨2093775, by rfl⟩ : syracuseStep 5583401 = 4187551) B4187551
theorem B7836527 : Blo 1630514 7836527 := bstep (se 1 (by rfl) ⟨5877395, by rfl⟩ : syracuseStep 7836527 = 11754791) B11754791
theorem B6969185 : Blo 1630514 6969185 := bstep (se 2 (by rfl) ⟨2613444, by rfl⟩ : syracuseStep 6969185 = 5226889) B5226889
theorem B2447327 : Blo 1630514 2447327 := bstep (se 1 (by rfl) ⟨1835495, by rfl⟩ : syracuseStep 2447327 = 3670991) B3670991
theorem B12384251 : Blo 1630514 12384251 := bstep (se 1 (by rfl) ⟨9288188, by rfl⟩ : syracuseStep 12384251 = 18576377) B18576377
theorem B8264105 : Blo 1630514 8264105 := bstep (se 2 (by rfl) ⟨3099039, by rfl⟩ : syracuseStep 8264105 = 6198079) B6198079
theorem B33471305 : Blo 1630514 33471305 := bstep (se 2 (by rfl) ⟨12551739, by rfl⟩ : syracuseStep 33471305 = 25103479) B25103479
theorem B339123023 : Blo 1630514 339123023 := bstep (se 1 (by rfl) ⟨254342267, by rfl⟩ : syracuseStep 339123023 = 508684535) B508684535
theorem B5225735 : Blo 1630514 5225735 := bstep (se 1 (by rfl) ⟨3919301, by rfl⟩ : syracuseStep 5225735 = 7838603) B7838603
theorem B12729707 : Blo 1630514 12729707 := bstep (se 1 (by rfl) ⟨9547280, by rfl⟩ : syracuseStep 12729707 = 19094561) B19094561
theorem B28261867 : Blo 1630514 28261867 := bstep (se 1 (by rfl) ⟨21196400, by rfl⟩ : syracuseStep 28261867 = 42392801) B42392801
theorem B105889619 : Blo 1630514 105889619 := bstep (se 1 (by rfl) ⟨79417214, by rfl⟩ : syracuseStep 105889619 = 158834429) B158834429
theorem B163070081 : Blo 1630514 163070081 := bstep (se 2 (by rfl) ⟨61151280, by rfl⟩ : syracuseStep 163070081 = 122302561) B122302561
theorem B5505515 : Blo 1630514 5505515 := bstep (se 1 (by rfl) ⟨4129136, by rfl⟩ : syracuseStep 5505515 = 8258273) B8258273
theorem B4646123 : Blo 1630514 4646123 := bstep (se 1 (by rfl) ⟨3484592, by rfl⟩ : syracuseStep 4646123 = 6969185) B6969185
theorem B1631551 : Blo 1630514 1631551 := bstep (se 1 (by rfl) ⟨1223663, by rfl⟩ : syracuseStep 1631551 = 2447327) B2447327
theorem B3671711 : Blo 1630514 3671711 := bstep (se 1 (by rfl) ⟨2753783, by rfl⟩ : syracuseStep 3671711 = 5507567) B5507567
theorem B3483823 : Blo 1630514 3483823 := bstep (se 1 (by rfl) ⟨2612867, by rfl⟩ : syracuseStep 3483823 = 5225735) B5225735
theorem B70568171 : Blo 1630514 70568171 := bstep (se 1 (by rfl) ⟨52926128, by rfl⟩ : syracuseStep 70568171 = 105852257) B105852257
theorem B70593079 : Blo 1630514 70593079 := bstep (se 1 (by rfl) ⟨52944809, by rfl⟩ : syracuseStep 70593079 = 105889619) B105889619
theorem B3672827 : Blo 1630514 3672827 := bstep (se 1 (by rfl) ⟨2754620, by rfl⟩ : syracuseStep 3672827 = 5509241) B5509241
theorem B3722267 : Blo 1630514 3722267 := bstep (se 1 (by rfl) ⟨2791700, by rfl⟩ : syracuseStep 3722267 = 5583401) B5583401
theorem B10456289 : Blo 1630514 10456289 := bstep (se 2 (by rfl) ⟨3921108, by rfl⟩ : syracuseStep 10456289 = 7842217) B7842217
theorem B4648367 : Blo 1630514 4648367 := bstep (se 1 (by rfl) ⟨3486275, by rfl⟩ : syracuseStep 4648367 = 6972551) B6972551
theorem B5509403 : Blo 1630514 5509403 := bstep (se 1 (by rfl) ⟨4132052, by rfl⟩ : syracuseStep 5509403 = 8264105) B8264105
theorem B5509673 : Blo 1630514 5509673 := bstep (se 2 (by rfl) ⟨2066127, by rfl⟩ : syracuseStep 5509673 = 4132255) B4132255
theorem B15676895 : Blo 1630514 15676895 := bstep (se 1 (by rfl) ⟨11757671, by rfl⟩ : syracuseStep 15676895 = 23515343) B23515343
theorem B2447207 : Blo 1630514 2447207 := bstep (se 1 (by rfl) ⟨1835405, by rfl⟩ : syracuseStep 2447207 = 3670811) B3670811
theorem B5224351 : Blo 1630514 5224351 := bstep (se 1 (by rfl) ⟨3918263, by rfl⟩ : syracuseStep 5224351 = 7836527) B7836527
theorem B8263619 : Blo 1630514 8263619 := bstep (se 1 (by rfl) ⟨6197714, by rfl⟩ : syracuseStep 8263619 = 12395429) B12395429
theorem B8256167 : Blo 1630514 8256167 := bstep (se 1 (by rfl) ⟨6192125, by rfl⟩ : syracuseStep 8256167 = 12384251) B12384251
theorem B22314203 : Blo 1630514 22314203 := bstep (se 1 (by rfl) ⟨16735652, by rfl⟩ : syracuseStep 22314203 = 33471305) B33471305
theorem B226082015 : Blo 1630514 226082015 := bstep (se 1 (by rfl) ⟨169561511, by rfl⟩ : syracuseStep 226082015 = 339123023) B339123023
theorem B37682489 : Blo 1630514 37682489 := bstep (se 2 (by rfl) ⟨14130933, by rfl⟩ : syracuseStep 37682489 = 28261867) B28261867
theorem B7445843 : Blo 1630514 7445843 := bstep (se 1 (by rfl) ⟨5584382, by rfl⟩ : syracuseStep 7445843 = 11168765) B11168765
theorem B7445951 : Blo 1630514 7445951 := bstep (se 1 (by rfl) ⟨5584463, by rfl⟩ : syracuseStep 7445951 = 11168927) B11168927
theorem B8486471 : Blo 1630514 8486471 := bstep (se 1 (by rfl) ⟨6364853, by rfl⟩ : syracuseStep 8486471 = 12729707) B12729707
theorem B4645097 : Blo 1630514 4645097 := bstep (se 2 (by rfl) ⟨1741911, by rfl⟩ : syracuseStep 4645097 = 3483823) B3483823
theorem B3670343 : Blo 1630514 3670343 := bstep (se 1 (by rfl) ⟨2752757, by rfl⟩ : syracuseStep 3670343 = 5505515) B5505515
theorem B3097415 : Blo 1630514 3097415 := bstep (se 1 (by rfl) ⟨2323061, by rfl⟩ : syracuseStep 3097415 = 4646123) B4646123
theorem B1631471 : Blo 1630514 1631471 := bstep (se 1 (by rfl) ⟨1223603, by rfl⟩ : syracuseStep 1631471 = 2447207) B2447207
theorem B3098911 : Blo 1630514 3098911 := bstep (se 1 (by rfl) ⟨2324183, by rfl⟩ : syracuseStep 3098911 = 4648367) B4648367
theorem B6965801 : Blo 1630514 6965801 := bstep (se 2 (by rfl) ⟨2612175, by rfl⟩ : syracuseStep 6965801 = 5224351) B5224351
theorem B3672935 : Blo 1630514 3672935 := bstep (se 1 (by rfl) ⟨2754701, by rfl⟩ : syracuseStep 3672935 = 5509403) B5509403
theorem B3673115 : Blo 1630514 3673115 := bstep (se 1 (by rfl) ⟨2754836, by rfl⟩ : syracuseStep 3673115 = 5509673) B5509673
theorem B5509079 : Blo 1630514 5509079 := bstep (se 1 (by rfl) ⟨4131809, by rfl⟩ : syracuseStep 5509079 = 8263619) B8263619
theorem B150721343 : Blo 1630514 150721343 := bstep (se 1 (by rfl) ⟨113041007, by rfl⟩ : syracuseStep 150721343 = 226082015) B226082015
theorem B25121659 : Blo 1630514 25121659 := bstep (se 1 (by rfl) ⟨18841244, by rfl⟩ : syracuseStep 25121659 = 37682489) B37682489
theorem B5657647 : Blo 1630514 5657647 := bstep (se 1 (by rfl) ⟨4243235, by rfl⟩ : syracuseStep 5657647 = 8486471) B8486471
theorem B108713387 : Blo 1630514 108713387 := bstep (se 1 (by rfl) ⟨81535040, by rfl⟩ : syracuseStep 108713387 = 163070081) B163070081
theorem B94124105 : Blo 1630514 94124105 := bstep (se 2 (by rfl) ⟨35296539, by rfl⟩ : syracuseStep 94124105 = 70593079) B70593079
theorem B10451263 : Blo 1630514 10451263 := bstep (se 1 (by rfl) ⟨7838447, by rfl⟩ : syracuseStep 10451263 = 15676895) B15676895
theorem B2447807 : Blo 1630514 2447807 := bstep (se 1 (by rfl) ⟨1835855, by rfl⟩ : syracuseStep 2447807 = 3671711) B3671711
theorem B47045447 : Blo 1630514 47045447 := bstep (se 1 (by rfl) ⟨35284085, by rfl⟩ : syracuseStep 47045447 = 70568171) B70568171
theorem B5504111 : Blo 1630514 5504111 := bstep (se 1 (by rfl) ⟨4128083, by rfl⟩ : syracuseStep 5504111 = 8256167) B8256167
theorem B2448551 : Blo 1630514 2448551 := bstep (se 1 (by rfl) ⟨1836413, by rfl⟩ : syracuseStep 2448551 = 3672827) B3672827
theorem B2481511 : Blo 1630514 2481511 := bstep (se 1 (by rfl) ⟨1861133, by rfl⟩ : syracuseStep 2481511 = 3722267) B3722267
theorem B14876135 : Blo 1630514 14876135 := bstep (se 1 (by rfl) ⟨11157101, by rfl⟩ : syracuseStep 14876135 = 22314203) B22314203
theorem B6970859 : Blo 1630514 6970859 := bstep (se 1 (by rfl) ⟨5228144, by rfl⟩ : syracuseStep 6970859 = 10456289) B10456289
theorem B4963895 : Blo 1630514 4963895 := bstep (se 1 (by rfl) ⟨3722921, by rfl⟩ : syracuseStep 4963895 = 7445843) B7445843
theorem B4963967 : Blo 1630514 4963967 := bstep (se 1 (by rfl) ⟨3722975, by rfl⟩ : syracuseStep 4963967 = 7445951) B7445951
theorem B3096731 : Blo 1630514 3096731 := bstep (se 1 (by rfl) ⟨2322548, by rfl⟩ : syracuseStep 3096731 = 4645097) B4645097
theorem B13935017 : Blo 1630514 13935017 := bstep (se 2 (by rfl) ⟨5225631, by rfl⟩ : syracuseStep 13935017 = 10451263) B10451263
theorem B2064943 : Blo 1630514 2064943 := bstep (se 1 (by rfl) ⟨1548707, by rfl⟩ : syracuseStep 2064943 = 3097415) B3097415
theorem B1631871 : Blo 1630514 1631871 := bstep (se 1 (by rfl) ⟨1223903, by rfl⟩ : syracuseStep 1631871 = 2447807) B2447807
theorem B1632367 : Blo 1630514 1632367 := bstep (se 1 (by rfl) ⟨1224275, by rfl⟩ : syracuseStep 1632367 = 2448551) B2448551
theorem B4647239 : Blo 1630514 4647239 := bstep (se 1 (by rfl) ⟨3485429, by rfl⟩ : syracuseStep 4647239 = 6970859) B6970859
theorem B3672719 : Blo 1630514 3672719 := bstep (se 1 (by rfl) ⟨2754539, by rfl⟩ : syracuseStep 3672719 = 5509079) B5509079
theorem B4131881 : Blo 1630514 4131881 := bstep (se 2 (by rfl) ⟨1549455, by rfl⟩ : syracuseStep 4131881 = 3098911) B3098911
theorem B289902365 : Blo 1630514 289902365 := bstep (se 3 (by rfl) ⟨54356693, by rfl⟩ : syracuseStep 289902365 = 108713387) B108713387
theorem B31363631 : Blo 1630514 31363631 := bstep (se 1 (by rfl) ⟨23522723, by rfl⟩ : syracuseStep 31363631 = 47045447) B47045447
theorem B9917423 : Blo 1630514 9917423 := bstep (se 1 (by rfl) ⟨7438067, by rfl⟩ : syracuseStep 9917423 = 14876135) B14876135
theorem B2446895 : Blo 1630514 2446895 := bstep (se 1 (by rfl) ⟨1835171, by rfl⟩ : syracuseStep 2446895 = 3670343) B3670343
theorem B100480895 : Blo 1630514 100480895 := bstep (se 1 (by rfl) ⟨75360671, by rfl⟩ : syracuseStep 100480895 = 150721343) B150721343
theorem B33495545 : Blo 1630514 33495545 := bstep (se 2 (by rfl) ⟨12560829, by rfl⟩ : syracuseStep 33495545 = 25121659) B25121659
theorem B62749403 : Blo 1630514 62749403 := bstep (se 1 (by rfl) ⟨47062052, by rfl⟩ : syracuseStep 62749403 = 94124105) B94124105
theorem B7543529 : Blo 1630514 7543529 := bstep (se 2 (by rfl) ⟨2828823, by rfl⟩ : syracuseStep 7543529 = 5657647) B5657647
theorem B4643867 : Blo 1630514 4643867 := bstep (se 1 (by rfl) ⟨3482900, by rfl⟩ : syracuseStep 4643867 = 6965801) B6965801
theorem B3308681 : Blo 1630514 3308681 := bstep (se 2 (by rfl) ⟨1240755, by rfl⟩ : syracuseStep 3308681 = 2481511) B2481511
theorem B2448623 : Blo 1630514 2448623 := bstep (se 1 (by rfl) ⟨1836467, by rfl⟩ : syracuseStep 2448623 = 3672935) B3672935
theorem B2448743 : Blo 1630514 2448743 := bstep (se 1 (by rfl) ⟨1836557, by rfl⟩ : syracuseStep 2448743 = 3673115) B3673115
theorem B3669407 : Blo 1630514 3669407 := bstep (se 1 (by rfl) ⟨2752055, by rfl⟩ : syracuseStep 3669407 = 5504111) B5504111
theorem B3309263 : Blo 1630514 3309263 := bstep (se 1 (by rfl) ⟨2481947, by rfl⟩ : syracuseStep 3309263 = 4963895) B4963895
theorem B3309311 : Blo 1630514 3309311 := bstep (se 1 (by rfl) ⟨2481983, by rfl⟩ : syracuseStep 3309311 = 4963967) B4963967
theorem B9290011 : Blo 1630514 9290011 := bstep (se 1 (by rfl) ⟨6967508, by rfl⟩ : syracuseStep 9290011 = 13935017) B13935017
theorem B8257949 : Blo 1630514 8257949 := bstep (se 3 (by rfl) ⟨1548365, by rfl⟩ : syracuseStep 8257949 = 3096731) B3096731
theorem B6611615 : Blo 1630514 6611615 := bstep (se 1 (by rfl) ⟨4958711, by rfl⟩ : syracuseStep 6611615 = 9917423) B9917423
theorem B2753257 : Blo 1630514 2753257 := bstep (se 2 (by rfl) ⟨1032471, by rfl⟩ : syracuseStep 2753257 = 2064943) B2064943
theorem B1631263 : Blo 1630514 1631263 := bstep (se 1 (by rfl) ⟨1223447, by rfl⟩ : syracuseStep 1631263 = 2446895) B2446895
theorem B66987263 : Blo 1630514 66987263 := bstep (se 1 (by rfl) ⟨50240447, by rfl⟩ : syracuseStep 66987263 = 100480895) B100480895
theorem B3098159 : Blo 1630514 3098159 := bstep (se 1 (by rfl) ⟨2323619, by rfl⟩ : syracuseStep 3098159 = 4647239) B4647239
theorem B2754587 : Blo 1630514 2754587 := bstep (se 1 (by rfl) ⟨2065940, by rfl⟩ : syracuseStep 2754587 = 4131881) B4131881
theorem B2205787 : Blo 1630514 2205787 := bstep (se 1 (by rfl) ⟨1654340, by rfl⟩ : syracuseStep 2205787 = 3308681) B3308681
theorem B1632415 : Blo 1630514 1632415 := bstep (se 1 (by rfl) ⟨1224311, by rfl⟩ : syracuseStep 1632415 = 2448623) B2448623
theorem B1632495 : Blo 1630514 1632495 := bstep (se 1 (by rfl) ⟨1224371, by rfl⟩ : syracuseStep 1632495 = 2448743) B2448743
theorem B2206175 : Blo 1630514 2206175 := bstep (se 1 (by rfl) ⟨1654631, by rfl⟩ : syracuseStep 2206175 = 3309263) B3309263
theorem B2206207 : Blo 1630514 2206207 := bstep (se 1 (by rfl) ⟨1654655, by rfl⟩ : syracuseStep 2206207 = 3309311) B3309311
theorem B193268243 : Blo 1630514 193268243 := bstep (se 1 (by rfl) ⟨144951182, by rfl⟩ : syracuseStep 193268243 = 289902365) B289902365
theorem B20909087 : Blo 1630514 20909087 := bstep (se 1 (by rfl) ⟨15681815, by rfl⟩ : syracuseStep 20909087 = 31363631) B31363631
theorem B41832935 : Blo 1630514 41832935 := bstep (se 1 (by rfl) ⟨31374701, by rfl⟩ : syracuseStep 41832935 = 62749403) B62749403
theorem B2446271 : Blo 1630514 2446271 := bstep (se 1 (by rfl) ⟨1834703, by rfl⟩ : syracuseStep 2446271 = 3669407) B3669407
theorem B22330363 : Blo 1630514 22330363 := bstep (se 1 (by rfl) ⟨16747772, by rfl⟩ : syracuseStep 22330363 = 33495545) B33495545
theorem B2448479 : Blo 1630514 2448479 := bstep (se 1 (by rfl) ⟨1836359, by rfl⟩ : syracuseStep 2448479 = 3672719) B3672719
theorem B5029019 : Blo 1630514 5029019 := bstep (se 1 (by rfl) ⟨3771764, by rfl⟩ : syracuseStep 5029019 = 7543529) B7543529
theorem B3095911 : Blo 1630514 3095911 := bstep (se 1 (by rfl) ⟨2321933, by rfl⟩ : syracuseStep 3095911 = 4643867) B4643867
theorem B2941049 : Blo 1630514 2941049 := bstep (se 2 (by rfl) ⟨1102893, by rfl⟩ : syracuseStep 2941049 = 2205787) B2205787
theorem B5505299 : Blo 1630514 5505299 := bstep (se 1 (by rfl) ⟨4128974, by rfl⟩ : syracuseStep 5505299 = 8257949) B8257949
theorem B12386681 : Blo 1630514 12386681 := bstep (se 2 (by rfl) ⟨4645005, by rfl⟩ : syracuseStep 12386681 = 9290011) B9290011
theorem B4407743 : Blo 1630514 4407743 := bstep (se 1 (by rfl) ⟨3305807, by rfl⟩ : syracuseStep 4407743 = 6611615) B6611615
theorem B1630847 : Blo 1630514 1630847 := bstep (se 1 (by rfl) ⟨1223135, by rfl⟩ : syracuseStep 1630847 = 2446271) B2446271
theorem B3671009 : Blo 1630514 3671009 := bstep (se 2 (by rfl) ⟨1376628, by rfl⟩ : syracuseStep 3671009 = 2753257) B2753257
theorem B2065439 : Blo 1630514 2065439 := bstep (se 1 (by rfl) ⟨1549079, by rfl⟩ : syracuseStep 2065439 = 3098159) B3098159
theorem B5883133 : Blo 1630514 5883133 := bstep (se 3 (by rfl) ⟨1103087, by rfl⟩ : syracuseStep 5883133 = 2206175) B2206175
theorem B1836391 : Blo 1630514 1836391 := bstep (se 1 (by rfl) ⟨1377293, by rfl⟩ : syracuseStep 1836391 = 2754587) B2754587
theorem B128845495 : Blo 1630514 128845495 := bstep (se 1 (by rfl) ⟨96634121, by rfl⟩ : syracuseStep 128845495 = 193268243) B193268243
theorem B1632319 : Blo 1630514 1632319 := bstep (se 1 (by rfl) ⟨1224239, by rfl⟩ : syracuseStep 1632319 = 2448479) B2448479
theorem B3352679 : Blo 1630514 3352679 := bstep (se 1 (by rfl) ⟨2514509, by rfl⟩ : syracuseStep 3352679 = 5029019) B5029019
theorem B11766437 : Blo 1630514 11766437 := bstep (se 4 (by rfl) ⟨1103103, by rfl⟩ : syracuseStep 11766437 = 2206207) B2206207
theorem B27888623 : Blo 1630514 27888623 := bstep (se 1 (by rfl) ⟨20916467, by rfl⟩ : syracuseStep 27888623 = 41832935) B41832935
theorem B44658175 : Blo 1630514 44658175 := bstep (se 1 (by rfl) ⟨33493631, by rfl⟩ : syracuseStep 44658175 = 66987263) B66987263
theorem B29773817 : Blo 1630514 29773817 := bstep (se 2 (by rfl) ⟨11165181, by rfl⟩ : syracuseStep 29773817 = 22330363) B22330363
theorem B13939391 : Blo 1630514 13939391 := bstep (se 1 (by rfl) ⟨10454543, by rfl⟩ : syracuseStep 13939391 = 20909087) B20909087
theorem B4127881 : Blo 1630514 4127881 := bstep (se 2 (by rfl) ⟨1547955, by rfl⟩ : syracuseStep 4127881 = 3095911) B3095911
theorem B3670199 : Blo 1630514 3670199 := bstep (se 1 (by rfl) ⟨2752649, by rfl⟩ : syracuseStep 3670199 = 5505299) B5505299
theorem B8257787 : Blo 1630514 8257787 := bstep (se 1 (by rfl) ⟨6193340, by rfl⟩ : syracuseStep 8257787 = 12386681) B12386681
theorem B1960699 : Blo 1630514 1960699 := bstep (se 1 (by rfl) ⟨1470524, by rfl⟩ : syracuseStep 1960699 = 2941049) B2941049
theorem B5507837 : Blo 1630514 5507837 := bstep (se 3 (by rfl) ⟨1032719, by rfl⟩ : syracuseStep 5507837 = 2065439) B2065439
theorem B9292927 : Blo 1630514 9292927 := bstep (se 1 (by rfl) ⟨6969695, by rfl⟩ : syracuseStep 9292927 = 13939391) B13939391
theorem B7844177 : Blo 1630514 7844177 := bstep (se 2 (by rfl) ⟨2941566, by rfl⟩ : syracuseStep 7844177 = 5883133) B5883133
theorem B7844291 : Blo 1630514 7844291 := bstep (se 1 (by rfl) ⟨5883218, by rfl⟩ : syracuseStep 7844291 = 11766437) B11766437
theorem B18592415 : Blo 1630514 18592415 := bstep (se 1 (by rfl) ⟨13944311, by rfl⟩ : syracuseStep 18592415 = 27888623) B27888623
theorem B59544233 : Blo 1630514 59544233 := bstep (se 2 (by rfl) ⟨22329087, by rfl⟩ : syracuseStep 59544233 = 44658175) B44658175
theorem B2447339 : Blo 1630514 2447339 := bstep (se 1 (by rfl) ⟨1835504, by rfl⟩ : syracuseStep 2447339 = 3671009) B3671009
theorem B687175973 : Blo 1630514 687175973 := bstep (se 4 (by rfl) ⟨64422747, by rfl⟩ : syracuseStep 687175973 = 128845495) B128845495
theorem B11753981 : Blo 1630514 11753981 := bstep (se 3 (by rfl) ⟨2203871, by rfl⟩ : syracuseStep 11753981 = 4407743) B4407743
theorem B2235119 : Blo 1630514 2235119 := bstep (se 1 (by rfl) ⟨1676339, by rfl⟩ : syracuseStep 2235119 = 3352679) B3352679
theorem B5503841 : Blo 1630514 5503841 := bstep (se 2 (by rfl) ⟨2063940, by rfl⟩ : syracuseStep 5503841 = 4127881) B4127881
theorem B2448521 : Blo 1630514 2448521 := bstep (se 2 (by rfl) ⟨918195, by rfl⟩ : syracuseStep 2448521 = 1836391) B1836391
theorem B19849211 : Blo 1630514 19849211 := bstep (se 1 (by rfl) ⟨14886908, by rfl⟩ : syracuseStep 19849211 = 29773817) B29773817
theorem B5505191 : Blo 1630514 5505191 := bstep (se 1 (by rfl) ⟨4128893, by rfl⟩ : syracuseStep 5505191 = 8257787) B8257787
theorem B12394943 : Blo 1630514 12394943 := bstep (se 1 (by rfl) ⟨9296207, by rfl⟩ : syracuseStep 12394943 = 18592415) B18592415
theorem B2614265 : Blo 1630514 2614265 := bstep (se 2 (by rfl) ⟨980349, by rfl⟩ : syracuseStep 2614265 = 1960699) B1960699
theorem B1631559 : Blo 1630514 1631559 := bstep (se 1 (by rfl) ⟨1223669, by rfl⟩ : syracuseStep 1631559 = 2447339) B2447339
theorem B3671891 : Blo 1630514 3671891 := bstep (se 1 (by rfl) ⟨2753918, by rfl⟩ : syracuseStep 3671891 = 5507837) B5507837
theorem B1632347 : Blo 1630514 1632347 := bstep (se 1 (by rfl) ⟨1224260, by rfl⟩ : syracuseStep 1632347 = 2448521) B2448521
theorem B13232807 : Blo 1630514 13232807 := bstep (se 1 (by rfl) ⟨9924605, by rfl⟩ : syracuseStep 13232807 = 19849211) B19849211
theorem B5229451 : Blo 1630514 5229451 := bstep (se 1 (by rfl) ⟨3922088, by rfl⟩ : syracuseStep 5229451 = 7844177) B7844177
theorem B5229527 : Blo 1630514 5229527 := bstep (se 1 (by rfl) ⟨3922145, by rfl⟩ : syracuseStep 5229527 = 7844291) B7844291
theorem B12390569 : Blo 1630514 12390569 := bstep (se 2 (by rfl) ⟨4646463, by rfl⟩ : syracuseStep 12390569 = 9292927) B9292927
theorem B458117315 : Blo 1630514 458117315 := bstep (se 1 (by rfl) ⟨343587986, by rfl⟩ : syracuseStep 458117315 = 687175973) B687175973
theorem B7835987 : Blo 1630514 7835987 := bstep (se 1 (by rfl) ⟨5876990, by rfl⟩ : syracuseStep 7835987 = 11753981) B11753981
theorem B5960317 : Blo 1630514 5960317 := bstep (se 3 (by rfl) ⟨1117559, by rfl⟩ : syracuseStep 5960317 = 2235119) B2235119
theorem B2446799 : Blo 1630514 2446799 := bstep (se 1 (by rfl) ⟨1835099, by rfl⟩ : syracuseStep 2446799 = 3670199) B3670199
theorem B39696155 : Blo 1630514 39696155 := bstep (se 1 (by rfl) ⟨29772116, by rfl⟩ : syracuseStep 39696155 = 59544233) B59544233
theorem B3669227 : Blo 1630514 3669227 := bstep (se 1 (by rfl) ⟨2751920, by rfl⟩ : syracuseStep 3669227 = 5503841) B5503841
theorem B3670127 : Blo 1630514 3670127 := bstep (se 1 (by rfl) ⟨2752595, by rfl⟩ : syracuseStep 3670127 = 5505191) B5505191
theorem B7947089 : Blo 1630514 7947089 := bstep (se 2 (by rfl) ⟨2980158, by rfl⟩ : syracuseStep 7947089 = 5960317) B5960317
theorem B1631199 : Blo 1630514 1631199 := bstep (se 1 (by rfl) ⟨1223399, by rfl⟩ : syracuseStep 1631199 = 2446799) B2446799
theorem B6972601 : Blo 1630514 6972601 := bstep (se 2 (by rfl) ⟨2614725, by rfl⟩ : syracuseStep 6972601 = 5229451) B5229451
theorem B13945405 : Blo 1630514 13945405 := bstep (se 3 (by rfl) ⟨2614763, by rfl⟩ : syracuseStep 13945405 = 5229527) B5229527
theorem B8260379 : Blo 1630514 8260379 := bstep (se 1 (by rfl) ⟨6195284, by rfl⟩ : syracuseStep 8260379 = 12390569) B12390569
theorem B26464103 : Blo 1630514 26464103 := bstep (se 1 (by rfl) ⟨19848077, by rfl⟩ : syracuseStep 26464103 = 39696155) B39696155
theorem B2446151 : Blo 1630514 2446151 := bstep (se 1 (by rfl) ⟨1834613, by rfl⟩ : syracuseStep 2446151 = 3669227) B3669227
theorem B305411543 : Blo 1630514 305411543 := bstep (se 1 (by rfl) ⟨229058657, by rfl⟩ : syracuseStep 305411543 = 458117315) B458117315
theorem B8263295 : Blo 1630514 8263295 := bstep (se 1 (by rfl) ⟨6197471, by rfl⟩ : syracuseStep 8263295 = 12394943) B12394943
theorem B1742843 : Blo 1630514 1742843 := bstep (se 1 (by rfl) ⟨1307132, by rfl⟩ : syracuseStep 1742843 = 2614265) B2614265
theorem B20895965 : Blo 1630514 20895965 := bstep (se 3 (by rfl) ⟨3917993, by rfl⟩ : syracuseStep 20895965 = 7835987) B7835987
theorem B2447927 : Blo 1630514 2447927 := bstep (se 1 (by rfl) ⟨1835945, by rfl⟩ : syracuseStep 2447927 = 3671891) B3671891
theorem B8821871 : Blo 1630514 8821871 := bstep (se 1 (by rfl) ⟨6616403, by rfl⟩ : syracuseStep 8821871 = 13232807) B13232807
theorem B1630767 : Blo 1630514 1630767 := bstep (se 1 (by rfl) ⟨1223075, by rfl⟩ : syracuseStep 1630767 = 2446151) B2446151
theorem B1631951 : Blo 1630514 1631951 := bstep (se 1 (by rfl) ⟨1223963, by rfl⟩ : syracuseStep 1631951 = 2447927) B2447927
theorem B5506919 : Blo 1630514 5506919 := bstep (se 1 (by rfl) ⟨4130189, by rfl⟩ : syracuseStep 5506919 = 8260379) B8260379
theorem B4647581 : Blo 1630514 4647581 := bstep (se 3 (by rfl) ⟨871421, by rfl⟩ : syracuseStep 4647581 = 1742843) B1742843
theorem B203607695 : Blo 1630514 203607695 := bstep (se 1 (by rfl) ⟨152705771, by rfl⟩ : syracuseStep 203607695 = 305411543) B305411543
theorem B5508863 : Blo 1630514 5508863 := bstep (se 1 (by rfl) ⟨4131647, by rfl⟩ : syracuseStep 5508863 = 8263295) B8263295
theorem B13930643 : Blo 1630514 13930643 := bstep (se 1 (by rfl) ⟨10447982, by rfl⟩ : syracuseStep 13930643 = 20895965) B20895965
theorem B17642735 : Blo 1630514 17642735 := bstep (se 1 (by rfl) ⟨13232051, by rfl⟩ : syracuseStep 17642735 = 26464103) B26464103
theorem B2446751 : Blo 1630514 2446751 := bstep (se 1 (by rfl) ⟨1835063, by rfl⟩ : syracuseStep 2446751 = 3670127) B3670127
theorem B5298059 : Blo 1630514 5298059 := bstep (se 1 (by rfl) ⟨3973544, by rfl⟩ : syracuseStep 5298059 = 7947089) B7947089
theorem B18593873 : Blo 1630514 18593873 := bstep (se 2 (by rfl) ⟨6972702, by rfl⟩ : syracuseStep 18593873 = 13945405) B13945405
theorem B9296801 : Blo 1630514 9296801 := bstep (se 2 (by rfl) ⟨3486300, by rfl⟩ : syracuseStep 9296801 = 6972601) B6972601
theorem B5881247 : Blo 1630514 5881247 := bstep (se 1 (by rfl) ⟨4410935, by rfl⟩ : syracuseStep 5881247 = 8821871) B8821871
theorem B1631167 : Blo 1630514 1631167 := bstep (se 1 (by rfl) ⟨1223375, by rfl⟩ : syracuseStep 1631167 = 2446751) B2446751
theorem B3671279 : Blo 1630514 3671279 := bstep (se 1 (by rfl) ⟨2753459, by rfl⟩ : syracuseStep 3671279 = 5506919) B5506919
theorem B12395915 : Blo 1630514 12395915 := bstep (se 1 (by rfl) ⟨9296936, by rfl⟩ : syracuseStep 12395915 = 18593873) B18593873
theorem B3098387 : Blo 1630514 3098387 := bstep (se 1 (by rfl) ⟨2323790, by rfl⟩ : syracuseStep 3098387 = 4647581) B4647581
theorem B3672575 : Blo 1630514 3672575 := bstep (se 1 (by rfl) ⟨2754431, by rfl⟩ : syracuseStep 3672575 = 5508863) B5508863
theorem B6197867 : Blo 1630514 6197867 := bstep (se 1 (by rfl) ⟨4648400, by rfl⟩ : syracuseStep 6197867 = 9296801) B9296801
theorem B3920831 : Blo 1630514 3920831 := bstep (se 1 (by rfl) ⟨2940623, by rfl⟩ : syracuseStep 3920831 = 5881247) B5881247
theorem B14128157 : Blo 1630514 14128157 := bstep (se 3 (by rfl) ⟨2649029, by rfl⟩ : syracuseStep 14128157 = 5298059) B5298059
theorem B135738463 : Blo 1630514 135738463 := bstep (se 1 (by rfl) ⟨101803847, by rfl⟩ : syracuseStep 135738463 = 203607695) B203607695
theorem B9287095 : Blo 1630514 9287095 := bstep (se 1 (by rfl) ⟨6965321, by rfl⟩ : syracuseStep 9287095 = 13930643) B13930643
theorem B11761823 : Blo 1630514 11761823 := bstep (se 1 (by rfl) ⟨8821367, by rfl⟩ : syracuseStep 11761823 = 17642735) B17642735
theorem B2613887 : Blo 1630514 2613887 := bstep (se 1 (by rfl) ⟨1960415, by rfl⟩ : syracuseStep 2613887 = 3920831) B3920831
theorem B2065591 : Blo 1630514 2065591 := bstep (se 1 (by rfl) ⟨1549193, by rfl⟩ : syracuseStep 2065591 = 3098387) B3098387
theorem B7841215 : Blo 1630514 7841215 := bstep (se 1 (by rfl) ⟨5880911, by rfl⟩ : syracuseStep 7841215 = 11761823) B11761823
theorem B4131911 : Blo 1630514 4131911 := bstep (se 1 (by rfl) ⟨3098933, by rfl⟩ : syracuseStep 4131911 = 6197867) B6197867
theorem B12382793 : Blo 1630514 12382793 := bstep (se 2 (by rfl) ⟨4643547, by rfl⟩ : syracuseStep 12382793 = 9287095) B9287095
theorem B9418771 : Blo 1630514 9418771 := bstep (se 1 (by rfl) ⟨7064078, by rfl⟩ : syracuseStep 9418771 = 14128157) B14128157
theorem B2447519 : Blo 1630514 2447519 := bstep (se 1 (by rfl) ⟨1835639, by rfl⟩ : syracuseStep 2447519 = 3671279) B3671279
theorem B8263943 : Blo 1630514 8263943 := bstep (se 1 (by rfl) ⟨6197957, by rfl⟩ : syracuseStep 8263943 = 12395915) B12395915
theorem B180984617 : Blo 1630514 180984617 := bstep (se 2 (by rfl) ⟨67869231, by rfl⟩ : syracuseStep 180984617 = 135738463) B135738463
theorem B2448383 : Blo 1630514 2448383 := bstep (se 1 (by rfl) ⟨1836287, by rfl⟩ : syracuseStep 2448383 = 3672575) B3672575
theorem B50233445 : Blo 1630514 50233445 := bstep (se 4 (by rfl) ⟨4709385, by rfl⟩ : syracuseStep 50233445 = 9418771) B9418771
theorem B1631679 : Blo 1630514 1631679 := bstep (se 1 (by rfl) ⟨1223759, by rfl⟩ : syracuseStep 1631679 = 2447519) B2447519
theorem B2754121 : Blo 1630514 2754121 := bstep (se 2 (by rfl) ⟨1032795, by rfl⟩ : syracuseStep 2754121 = 2065591) B2065591
theorem B1632255 : Blo 1630514 1632255 := bstep (se 1 (by rfl) ⟨1224191, by rfl⟩ : syracuseStep 1632255 = 2448383) B2448383
theorem B2754607 : Blo 1630514 2754607 := bstep (se 1 (by rfl) ⟨2065955, by rfl⟩ : syracuseStep 2754607 = 4131911) B4131911
theorem B5509295 : Blo 1630514 5509295 := bstep (se 1 (by rfl) ⟨4131971, by rfl⟩ : syracuseStep 5509295 = 8263943) B8263943
theorem B120656411 : Blo 1630514 120656411 := bstep (se 1 (by rfl) ⟨90492308, by rfl⟩ : syracuseStep 120656411 = 180984617) B180984617
theorem B8255195 : Blo 1630514 8255195 := bstep (se 1 (by rfl) ⟨6191396, by rfl⟩ : syracuseStep 8255195 = 12382793) B12382793
theorem B1742591 : Blo 1630514 1742591 := bstep (se 1 (by rfl) ⟨1306943, by rfl⟩ : syracuseStep 1742591 = 2613887) B2613887
theorem B41819813 : Blo 1630514 41819813 := bstep (se 4 (by rfl) ⟨3920607, by rfl⟩ : syracuseStep 41819813 = 7841215) B7841215
theorem B33488963 : Blo 1630514 33488963 := bstep (se 1 (by rfl) ⟨25116722, by rfl⟩ : syracuseStep 33488963 = 50233445) B50233445
theorem B80437607 : Blo 1630514 80437607 := bstep (se 1 (by rfl) ⟨60328205, by rfl⟩ : syracuseStep 80437607 = 120656411) B120656411
theorem B4646909 : Blo 1630514 4646909 := bstep (se 3 (by rfl) ⟨871295, by rfl⟩ : syracuseStep 4646909 = 1742591) B1742591
theorem B3672161 : Blo 1630514 3672161 := bstep (se 2 (by rfl) ⟨1377060, by rfl⟩ : syracuseStep 3672161 = 2754121) B2754121
theorem B27879875 : Blo 1630514 27879875 := bstep (se 1 (by rfl) ⟨20909906, by rfl⟩ : syracuseStep 27879875 = 41819813) B41819813
theorem B3672809 : Blo 1630514 3672809 := bstep (se 2 (by rfl) ⟨1377303, by rfl⟩ : syracuseStep 3672809 = 2754607) B2754607
theorem B3672863 : Blo 1630514 3672863 := bstep (se 1 (by rfl) ⟨2754647, by rfl⟩ : syracuseStep 3672863 = 5509295) B5509295
theorem B5503463 : Blo 1630514 5503463 := bstep (se 1 (by rfl) ⟨4127597, by rfl⟩ : syracuseStep 5503463 = 8255195) B8255195
theorem B53625071 : Blo 1630514 53625071 := bstep (se 1 (by rfl) ⟨40218803, by rfl⟩ : syracuseStep 53625071 = 80437607) B80437607
theorem B3097939 : Blo 1630514 3097939 := bstep (se 1 (by rfl) ⟨2323454, by rfl⟩ : syracuseStep 3097939 = 4646909) B4646909
theorem B22325975 : Blo 1630514 22325975 := bstep (se 1 (by rfl) ⟨16744481, by rfl⟩ : syracuseStep 22325975 = 33488963) B33488963
theorem B2448107 : Blo 1630514 2448107 := bstep (se 1 (by rfl) ⟨1836080, by rfl⟩ : syracuseStep 2448107 = 3672161) B3672161
theorem B18586583 : Blo 1630514 18586583 := bstep (se 1 (by rfl) ⟨13939937, by rfl⟩ : syracuseStep 18586583 = 27879875) B27879875
theorem B3668975 : Blo 1630514 3668975 := bstep (se 1 (by rfl) ⟨2751731, by rfl⟩ : syracuseStep 3668975 = 5503463) B5503463
theorem B2448539 : Blo 1630514 2448539 := bstep (se 1 (by rfl) ⟨1836404, by rfl⟩ : syracuseStep 2448539 = 3672809) B3672809
theorem B2448575 : Blo 1630514 2448575 := bstep (se 1 (by rfl) ⟨1836431, by rfl⟩ : syracuseStep 2448575 = 3672863) B3672863
theorem B35750047 : Blo 1630514 35750047 := bstep (se 1 (by rfl) ⟨26812535, by rfl⟩ : syracuseStep 35750047 = 53625071) B53625071
theorem B4130585 : Blo 1630514 4130585 := bstep (se 2 (by rfl) ⟨1548969, by rfl⟩ : syracuseStep 4130585 = 3097939) B3097939
theorem B1632071 : Blo 1630514 1632071 := bstep (se 1 (by rfl) ⟨1224053, by rfl⟩ : syracuseStep 1632071 = 2448107) B2448107
theorem B1632359 : Blo 1630514 1632359 := bstep (se 1 (by rfl) ⟨1224269, by rfl⟩ : syracuseStep 1632359 = 2448539) B2448539
theorem B1632383 : Blo 1630514 1632383 := bstep (se 1 (by rfl) ⟨1224287, by rfl⟩ : syracuseStep 1632383 = 2448575) B2448575
theorem B12391055 : Blo 1630514 12391055 := bstep (se 1 (by rfl) ⟨9293291, by rfl⟩ : syracuseStep 12391055 = 18586583) B18586583
theorem B2445983 : Blo 1630514 2445983 := bstep (se 1 (by rfl) ⟨1834487, by rfl⟩ : syracuseStep 2445983 = 3668975) B3668975
theorem B14883983 : Blo 1630514 14883983 := bstep (se 1 (by rfl) ⟨11162987, by rfl⟩ : syracuseStep 14883983 = 22325975) B22325975
theorem B1630655 : Blo 1630514 1630655 := bstep (se 1 (by rfl) ⟨1222991, by rfl⟩ : syracuseStep 1630655 = 2445983) B2445983
theorem B2753723 : Blo 1630514 2753723 := bstep (se 1 (by rfl) ⟨2065292, by rfl⟩ : syracuseStep 2753723 = 4130585) B4130585
theorem B9922655 : Blo 1630514 9922655 := bstep (se 1 (by rfl) ⟨7441991, by rfl⟩ : syracuseStep 9922655 = 14883983) B14883983
theorem B8260703 : Blo 1630514 8260703 := bstep (se 1 (by rfl) ⟨6195527, by rfl⟩ : syracuseStep 8260703 = 12391055) B12391055
theorem B47666729 : Blo 1630514 47666729 := bstep (se 2 (by rfl) ⟨17875023, by rfl⟩ : syracuseStep 47666729 = 35750047) B35750047
theorem B1835815 : Blo 1630514 1835815 := bstep (se 1 (by rfl) ⟨1376861, by rfl⟩ : syracuseStep 1835815 = 2753723) B2753723
theorem B5507135 : Blo 1630514 5507135 := bstep (se 1 (by rfl) ⟨4130351, by rfl⟩ : syracuseStep 5507135 = 8260703) B8260703
theorem B6615103 : Blo 1630514 6615103 := bstep (se 1 (by rfl) ⟨4961327, by rfl⟩ : syracuseStep 6615103 = 9922655) B9922655
theorem B127111277 : Blo 1630514 127111277 := bstep (se 3 (by rfl) ⟨23833364, by rfl⟩ : syracuseStep 127111277 = 47666729) B47666729
theorem B3671423 : Blo 1630514 3671423 := bstep (se 1 (by rfl) ⟨2753567, by rfl⟩ : syracuseStep 3671423 = 5507135) B5507135
theorem B84740851 : Blo 1630514 84740851 := bstep (se 1 (by rfl) ⟨63555638, by rfl⟩ : syracuseStep 84740851 = 127111277) B127111277
theorem B8820137 : Blo 1630514 8820137 := bstep (se 2 (by rfl) ⟨3307551, by rfl⟩ : syracuseStep 8820137 = 6615103) B6615103
theorem B2447753 : Blo 1630514 2447753 := bstep (se 2 (by rfl) ⟨917907, by rfl⟩ : syracuseStep 2447753 = 1835815) B1835815
theorem B23520365 : Blo 1630514 23520365 := bstep (se 3 (by rfl) ⟨4410068, by rfl⟩ : syracuseStep 23520365 = 8820137) B8820137
theorem B1631835 : Blo 1630514 1631835 := bstep (se 1 (by rfl) ⟨1223876, by rfl⟩ : syracuseStep 1631835 = 2447753) B2447753
theorem B112987801 : Blo 1630514 112987801 := bstep (se 2 (by rfl) ⟨42370425, by rfl⟩ : syracuseStep 112987801 = 84740851) B84740851
theorem B2447615 : Blo 1630514 2447615 := bstep (se 1 (by rfl) ⟨1835711, by rfl⟩ : syracuseStep 2447615 = 3671423) B3671423
theorem B15680243 : Blo 1630514 15680243 := bstep (se 1 (by rfl) ⟨11760182, by rfl⟩ : syracuseStep 15680243 = 23520365) B23520365
theorem B1631743 : Blo 1630514 1631743 := bstep (se 1 (by rfl) ⟨1223807, by rfl⟩ : syracuseStep 1631743 = 2447615) B2447615
theorem B150650401 : Blo 1630514 150650401 := bstep (se 2 (by rfl) ⟨56493900, by rfl⟩ : syracuseStep 150650401 = 112987801) B112987801
theorem B10453495 : Blo 1630514 10453495 := bstep (se 1 (by rfl) ⟨7840121, by rfl⟩ : syracuseStep 10453495 = 15680243) B15680243
theorem B200867201 : Blo 1630514 200867201 := bstep (se 2 (by rfl) ⟨75325200, by rfl⟩ : syracuseStep 200867201 = 150650401) B150650401
theorem B13937993 : Blo 1630514 13937993 := bstep (se 2 (by rfl) ⟨5226747, by rfl⟩ : syracuseStep 13937993 = 10453495) B10453495
theorem B133911467 : Blo 1630514 133911467 := bstep (se 1 (by rfl) ⟨100433600, by rfl⟩ : syracuseStep 133911467 = 200867201) B200867201
theorem B9291995 : Blo 1630514 9291995 := bstep (se 1 (by rfl) ⟨6968996, by rfl⟩ : syracuseStep 9291995 = 13937993) B13937993
theorem B89274311 : Blo 1630514 89274311 := bstep (se 1 (by rfl) ⟨66955733, by rfl⟩ : syracuseStep 89274311 = 133911467) B133911467
theorem B59516207 : Blo 1630514 59516207 := bstep (se 1 (by rfl) ⟨44637155, by rfl⟩ : syracuseStep 59516207 = 89274311) B89274311
theorem B6194663 : Blo 1630514 6194663 := bstep (se 1 (by rfl) ⟨4645997, by rfl⟩ : syracuseStep 6194663 = 9291995) B9291995
theorem B4129775 : Blo 1630514 4129775 := bstep (se 1 (by rfl) ⟨3097331, by rfl⟩ : syracuseStep 4129775 = 6194663) B6194663
theorem B39677471 : Blo 1630514 39677471 := bstep (se 1 (by rfl) ⟨29758103, by rfl⟩ : syracuseStep 39677471 = 59516207) B59516207
theorem B2753183 : Blo 1630514 2753183 := bstep (se 1 (by rfl) ⟨2064887, by rfl⟩ : syracuseStep 2753183 = 4129775) B4129775
theorem B26451647 : Blo 1630514 26451647 := bstep (se 1 (by rfl) ⟨19838735, by rfl⟩ : syracuseStep 26451647 = 39677471) B39677471
theorem B1835455 : Blo 1630514 1835455 := bstep (se 1 (by rfl) ⟨1376591, by rfl⟩ : syracuseStep 1835455 = 2753183) B2753183
theorem B17634431 : Blo 1630514 17634431 := bstep (se 1 (by rfl) ⟨13225823, by rfl⟩ : syracuseStep 17634431 = 26451647) B26451647
theorem B11756287 : Blo 1630514 11756287 := bstep (se 1 (by rfl) ⟨8817215, by rfl⟩ : syracuseStep 11756287 = 17634431) B17634431
theorem B2447273 : Blo 1630514 2447273 := bstep (se 2 (by rfl) ⟨917727, by rfl⟩ : syracuseStep 2447273 = 1835455) B1835455
theorem B1631515 : Blo 1630514 1631515 := bstep (se 1 (by rfl) ⟨1223636, by rfl⟩ : syracuseStep 1631515 = 2447273) B2447273
theorem B15675049 : Blo 1630514 15675049 := bstep (se 2 (by rfl) ⟨5878143, by rfl⟩ : syracuseStep 15675049 = 11756287) B11756287
theorem B20900065 : Blo 1630514 20900065 := bstep (se 2 (by rfl) ⟨7837524, by rfl⟩ : syracuseStep 20900065 = 15675049) B15675049
theorem B27866753 : Blo 1630514 27866753 := bstep (se 2 (by rfl) ⟨10450032, by rfl⟩ : syracuseStep 27866753 = 20900065) B20900065
theorem B18577835 : Blo 1630514 18577835 := bstep (se 1 (by rfl) ⟨13933376, by rfl⟩ : syracuseStep 18577835 = 27866753) B27866753
theorem B12385223 : Blo 1630514 12385223 := bstep (se 1 (by rfl) ⟨9288917, by rfl⟩ : syracuseStep 12385223 = 18577835) B18577835
theorem B8256815 : Blo 1630514 8256815 := bstep (se 1 (by rfl) ⟨6192611, by rfl⟩ : syracuseStep 8256815 = 12385223) B12385223
theorem B5504543 : Blo 1630514 5504543 := bstep (se 1 (by rfl) ⟨4128407, by rfl⟩ : syracuseStep 5504543 = 8256815) B8256815
theorem B3669695 : Blo 1630514 3669695 := bstep (se 1 (by rfl) ⟨2752271, by rfl⟩ : syracuseStep 3669695 = 5504543) B5504543
theorem B2446463 : Blo 1630514 2446463 := bstep (se 1 (by rfl) ⟨1834847, by rfl⟩ : syracuseStep 2446463 = 3669695) B3669695
theorem B1630975 : Blo 1630514 1630975 := bstep (se 1 (by rfl) ⟨1223231, by rfl⟩ : syracuseStep 1630975 = 2446463) B2446463

theorem C0 (j : ℕ) (h1 : 407628 ≤ j) (h2 : j ≤ 408127) : Blo 1630514 (4 * j + 3) := by
  interval_cases j
  · exact B1630515
  · exact B1630519
  · exact B1630523
  · exact B1630527
  · exact B1630531
  · exact B1630535
  · exact B1630539
  · exact B1630543
  · exact B1630547
  · exact B1630551
  · exact B1630555
  · exact B1630559
  · exact B1630563
  · exact B1630567
  · exact B1630571
  · exact B1630575
  · exact B1630579
  · exact B1630583
  · exact B1630587
  · exact B1630591
  · exact B1630595
  · exact B1630599
  · exact B1630603
  · exact B1630607
  · exact B1630611
  · exact B1630615
  · exact B1630619
  · exact B1630623
  · exact B1630627
  · exact B1630631
  · exact B1630635
  · exact B1630639
  · exact B1630643
  · exact B1630647
  · exact B1630651
  · exact B1630655
  · exact B1630659
  · exact B1630663
  · exact B1630667
  · exact B1630671
  · exact B1630675
  · exact B1630679
  · exact B1630683
  · exact B1630687
  · exact B1630691
  · exact B1630695
  · exact B1630699
  · exact B1630703
  · exact B1630707
  · exact B1630711
  · exact B1630715
  · exact B1630719
  · exact B1630723
  · exact B1630727
  · exact B1630731
  · exact B1630735
  · exact B1630739
  · exact B1630743
  · exact B1630747
  · exact B1630751
  · exact B1630755
  · exact B1630759
  · exact B1630763
  · exact B1630767
  · exact B1630771
  · exact B1630775
  · exact B1630779
  · exact B1630783
  · exact B1630787
  · exact B1630791
  · exact B1630795
  · exact B1630799
  · exact B1630803
  · exact B1630807
  · exact B1630811
  · exact B1630815
  · exact B1630819
  · exact B1630823
  · exact B1630827
  · exact B1630831
  · exact B1630835
  · exact B1630839
  · exact B1630843
  · exact B1630847
  · exact B1630851
  · exact B1630855
  · exact B1630859
  · exact B1630863
  · exact B1630867
  · exact B1630871
  · exact B1630875
  · exact B1630879
  · exact B1630883
  · exact B1630887
  · exact B1630891
  · exact B1630895
  · exact B1630899
  · exact B1630903
  · exact B1630907
  · exact B1630911
  · exact B1630915
  · exact B1630919
  · exact B1630923
  · exact B1630927
  · exact B1630931
  · exact B1630935
  · exact B1630939
  · exact B1630943
  · exact B1630947
  · exact B1630951
  · exact B1630955
  · exact B1630959
  · exact B1630963
  · exact B1630967
  · exact B1630971
  · exact B1630975
  · exact B1630979
  · exact B1630983
  · exact B1630987
  · exact B1630991
  · exact B1630995
  · exact B1630999
  · exact B1631003
  · exact B1631007
  · exact B1631011
  · exact B1631015
  · exact B1631019
  · exact B1631023
  · exact B1631027
  · exact B1631031
  · exact B1631035
  · exact B1631039
  · exact B1631043
  · exact B1631047
  · exact B1631051
  · exact B1631055
  · exact B1631059
  · exact B1631063
  · exact B1631067
  · exact B1631071
  · exact B1631075
  · exact B1631079
  · exact B1631083
  · exact B1631087
  · exact B1631091
  · exact B1631095
  · exact B1631099
  · exact B1631103
  · exact B1631107
  · exact B1631111
  · exact B1631115
  · exact B1631119
  · exact B1631123
  · exact B1631127
  · exact B1631131
  · exact B1631135
  · exact B1631139
  · exact B1631143
  · exact B1631147
  · exact B1631151
  · exact B1631155
  · exact B1631159
  · exact B1631163
  · exact B1631167
  · exact B1631171
  · exact B1631175
  · exact B1631179
  · exact B1631183
  · exact B1631187
  · exact B1631191
  · exact B1631195
  · exact B1631199
  · exact B1631203
  · exact B1631207
  · exact B1631211
  · exact B1631215
  · exact B1631219
  · exact B1631223
  · exact B1631227
  · exact B1631231
  · exact B1631235
  · exact B1631239
  · exact B1631243
  · exact B1631247
  · exact B1631251
  · exact B1631255
  · exact B1631259
  · exact B1631263
  · exact B1631267
  · exact B1631271
  · exact B1631275
  · exact B1631279
  · exact B1631283
  · exact B1631287
  · exact B1631291
  · exact B1631295
  · exact B1631299
  · exact B1631303
  · exact B1631307
  · exact B1631311
  · exact B1631315
  · exact B1631319
  · exact B1631323
  · exact B1631327
  · exact B1631331
  · exact B1631335
  · exact B1631339
  · exact B1631343
  · exact B1631347
  · exact B1631351
  · exact B1631355
  · exact B1631359
  · exact B1631363
  · exact B1631367
  · exact B1631371
  · exact B1631375
  · exact B1631379
  · exact B1631383
  · exact B1631387
  · exact B1631391
  · exact B1631395
  · exact B1631399
  · exact B1631403
  · exact B1631407
  · exact B1631411
  · exact B1631415
  · exact B1631419
  · exact B1631423
  · exact B1631427
  · exact B1631431
  · exact B1631435
  · exact B1631439
  · exact B1631443
  · exact B1631447
  · exact B1631451
  · exact B1631455
  · exact B1631459
  · exact B1631463
  · exact B1631467
  · exact B1631471
  · exact B1631475
  · exact B1631479
  · exact B1631483
  · exact B1631487
  · exact B1631491
  · exact B1631495
  · exact B1631499
  · exact B1631503
  · exact B1631507
  · exact B1631511
  · exact B1631515
  · exact B1631519
  · exact B1631523
  · exact B1631527
  · exact B1631531
  · exact B1631535
  · exact B1631539
  · exact B1631543
  · exact B1631547
  · exact B1631551
  · exact B1631555
  · exact B1631559
  · exact B1631563
  · exact B1631567
  · exact B1631571
  · exact B1631575
  · exact B1631579
  · exact B1631583
  · exact B1631587
  · exact B1631591
  · exact B1631595
  · exact B1631599
  · exact B1631603
  · exact B1631607
  · exact B1631611
  · exact B1631615
  · exact B1631619
  · exact B1631623
  · exact B1631627
  · exact B1631631
  · exact B1631635
  · exact B1631639
  · exact B1631643
  · exact B1631647
  · exact B1631651
  · exact B1631655
  · exact B1631659
  · exact B1631663
  · exact B1631667
  · exact B1631671
  · exact B1631675
  · exact B1631679
  · exact B1631683
  · exact B1631687
  · exact B1631691
  · exact B1631695
  · exact B1631699
  · exact B1631703
  · exact B1631707
  · exact B1631711
  · exact B1631715
  · exact B1631719
  · exact B1631723
  · exact B1631727
  · exact B1631731
  · exact B1631735
  · exact B1631739
  · exact B1631743
  · exact B1631747
  · exact B1631751
  · exact B1631755
  · exact B1631759
  · exact B1631763
  · exact B1631767
  · exact B1631771
  · exact B1631775
  · exact B1631779
  · exact B1631783
  · exact B1631787
  · exact B1631791
  · exact B1631795
  · exact B1631799
  · exact B1631803
  · exact B1631807
  · exact B1631811
  · exact B1631815
  · exact B1631819
  · exact B1631823
  · exact B1631827
  · exact B1631831
  · exact B1631835
  · exact B1631839
  · exact B1631843
  · exact B1631847
  · exact B1631851
  · exact B1631855
  · exact B1631859
  · exact B1631863
  · exact B1631867
  · exact B1631871
  · exact B1631875
  · exact B1631879
  · exact B1631883
  · exact B1631887
  · exact B1631891
  · exact B1631895
  · exact B1631899
  · exact B1631903
  · exact B1631907
  · exact B1631911
  · exact B1631915
  · exact B1631919
  · exact B1631923
  · exact B1631927
  · exact B1631931
  · exact B1631935
  · exact B1631939
  · exact B1631943
  · exact B1631947
  · exact B1631951
  · exact B1631955
  · exact B1631959
  · exact B1631963
  · exact B1631967
  · exact B1631971
  · exact B1631975
  · exact B1631979
  · exact B1631983
  · exact B1631987
  · exact B1631991
  · exact B1631995
  · exact B1631999
  · exact B1632003
  · exact B1632007
  · exact B1632011
  · exact B1632015
  · exact B1632019
  · exact B1632023
  · exact B1632027
  · exact B1632031
  · exact B1632035
  · exact B1632039
  · exact B1632043
  · exact B1632047
  · exact B1632051
  · exact B1632055
  · exact B1632059
  · exact B1632063
  · exact B1632067
  · exact B1632071
  · exact B1632075
  · exact B1632079
  · exact B1632083
  · exact B1632087
  · exact B1632091
  · exact B1632095
  · exact B1632099
  · exact B1632103
  · exact B1632107
  · exact B1632111
  · exact B1632115
  · exact B1632119
  · exact B1632123
  · exact B1632127
  · exact B1632131
  · exact B1632135
  · exact B1632139
  · exact B1632143
  · exact B1632147
  · exact B1632151
  · exact B1632155
  · exact B1632159
  · exact B1632163
  · exact B1632167
  · exact B1632171
  · exact B1632175
  · exact B1632179
  · exact B1632183
  · exact B1632187
  · exact B1632191
  · exact B1632195
  · exact B1632199
  · exact B1632203
  · exact B1632207
  · exact B1632211
  · exact B1632215
  · exact B1632219
  · exact B1632223
  · exact B1632227
  · exact B1632231
  · exact B1632235
  · exact B1632239
  · exact B1632243
  · exact B1632247
  · exact B1632251
  · exact B1632255
  · exact B1632259
  · exact B1632263
  · exact B1632267
  · exact B1632271
  · exact B1632275
  · exact B1632279
  · exact B1632283
  · exact B1632287
  · exact B1632291
  · exact B1632295
  · exact B1632299
  · exact B1632303
  · exact B1632307
  · exact B1632311
  · exact B1632315
  · exact B1632319
  · exact B1632323
  · exact B1632327
  · exact B1632331
  · exact B1632335
  · exact B1632339
  · exact B1632343
  · exact B1632347
  · exact B1632351
  · exact B1632355
  · exact B1632359
  · exact B1632363
  · exact B1632367
  · exact B1632371
  · exact B1632375
  · exact B1632379
  · exact B1632383
  · exact B1632387
  · exact B1632391
  · exact B1632395
  · exact B1632399
  · exact B1632403
  · exact B1632407
  · exact B1632411
  · exact B1632415
  · exact B1632419
  · exact B1632423
  · exact B1632427
  · exact B1632431
  · exact B1632435
  · exact B1632439
  · exact B1632443
  · exact B1632447
  · exact B1632451
  · exact B1632455
  · exact B1632459
  · exact B1632463
  · exact B1632467
  · exact B1632471
  · exact B1632475
  · exact B1632479
  · exact B1632483
  · exact B1632487
  · exact B1632491
  · exact B1632495
  · exact B1632499
  · exact B1632503
  · exact B1632507
  · exact B1632511

theorem solution (m : ℕ) (hlo : 1630514 ≤ m) (hhi : m ≤ 1632514) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 407628 ≤ j := by omega
    have hj2 : j ≤ 408127 := by omega
    have hb : Blo 1630514 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
