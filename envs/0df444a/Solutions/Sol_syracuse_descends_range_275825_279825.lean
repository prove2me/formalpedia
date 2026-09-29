-- Prove2me | solution 1 for syracuse_descends_range_275825_279825
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:44:11.484681+00:00
-- url     : https://prove2.me/submissions/de42f5a8-06df-4452-a526-c47303a7e998

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


theorem B524333 : Blo 275825 524333 := bbase (se 3 (by rfl) ⟨98312, by rfl⟩ : syracuseStep 524333 = 196625) (by norm_num)
theorem B622637 : Blo 275825 622637 := bbase (se 3 (by rfl) ⟨116744, by rfl⟩ : syracuseStep 622637 = 233489) (by norm_num)
theorem B1769525 : Blo 275825 1769525 := bbase (se 5 (by rfl) ⟨82946, by rfl⟩ : syracuseStep 1769525 = 165893) (by norm_num)
theorem B622709 : Blo 275825 622709 := bbase (se 5 (by rfl) ⟨29189, by rfl⟩ : syracuseStep 622709 = 58379) (by norm_num)
theorem B393341 : Blo 275825 393341 := bbase (se 3 (by rfl) ⟨73751, by rfl⟩ : syracuseStep 393341 = 147503) (by norm_num)
theorem B295049 : Blo 275825 295049 := bbase (se 2 (by rfl) ⟨110643, by rfl⟩ : syracuseStep 295049 = 221287) (by norm_num)
theorem B786581 : Blo 275825 786581 := bbase (se 6 (by rfl) ⟨18435, by rfl⟩ : syracuseStep 786581 = 36871) (by norm_num)
theorem B950453 : Blo 275825 950453 := bbase (se 5 (by rfl) ⟨44552, by rfl⟩ : syracuseStep 950453 = 89105) (by norm_num)
theorem B622781 : Blo 275825 622781 := bbase (se 3 (by rfl) ⟨116771, by rfl⟩ : syracuseStep 622781 = 233543) (by norm_num)
theorem B524485 : Blo 275825 524485 := bbase (se 4 (by rfl) ⟨49170, by rfl⟩ : syracuseStep 524485 = 98341) (by norm_num)
theorem B1409237 : Blo 275825 1409237 := bbase (se 7 (by rfl) ⟨16514, by rfl⟩ : syracuseStep 1409237 = 33029) (by norm_num)
theorem B622853 : Blo 275825 622853 := bbase (se 4 (by rfl) ⟨58392, by rfl⟩ : syracuseStep 622853 = 116785) (by norm_num)
theorem B590141 : Blo 275825 590141 := bbase (se 3 (by rfl) ⟨110651, by rfl⟩ : syracuseStep 590141 = 221303) (by norm_num)
theorem B622925 : Blo 275825 622925 := bbase (se 3 (by rfl) ⟨116798, by rfl⟩ : syracuseStep 622925 = 233597) (by norm_num)
theorem B2359637 : Blo 275825 2359637 := bbase (se 10 (by rfl) ⟨3456, by rfl⟩ : syracuseStep 2359637 = 6913) (by norm_num)
theorem B786773 : Blo 275825 786773 := bbase (se 10 (by rfl) ⟨1152, by rfl⟩ : syracuseStep 786773 = 2305) (by norm_num)
theorem B622997 : Blo 275825 622997 := bbase (se 6 (by rfl) ⟨14601, by rfl⟩ : syracuseStep 622997 = 29203) (by norm_num)
theorem B590285 : Blo 275825 590285 := bbase (se 3 (by rfl) ⟨110678, by rfl⟩ : syracuseStep 590285 = 221357) (by norm_num)
theorem B623069 : Blo 275825 623069 := bbase (se 3 (by rfl) ⟨116825, by rfl⟩ : syracuseStep 623069 = 233651) (by norm_num)
theorem B524789 : Blo 275825 524789 := bbase (se 5 (by rfl) ⟨24599, by rfl⟩ : syracuseStep 524789 = 49199) (by norm_num)
theorem B623141 : Blo 275825 623141 := bbase (se 4 (by rfl) ⟨58419, by rfl⟩ : syracuseStep 623141 = 116839) (by norm_num)
theorem B295493 : Blo 275825 295493 := bbase (se 4 (by rfl) ⟨27702, by rfl⟩ : syracuseStep 295493 = 55405) (by norm_num)
theorem B623213 : Blo 275825 623213 := bbase (se 3 (by rfl) ⟨116852, by rfl⟩ : syracuseStep 623213 = 233705) (by norm_num)
theorem B623285 : Blo 275825 623285 := bbase (se 5 (by rfl) ⟨29216, by rfl⟩ : syracuseStep 623285 = 58433) (by norm_num)
theorem B623357 : Blo 275825 623357 := bbase (se 3 (by rfl) ⟨116879, by rfl⟩ : syracuseStep 623357 = 233759) (by norm_num)
theorem B1049381 : Blo 275825 1049381 := bbase (se 4 (by rfl) ⟨98379, by rfl⟩ : syracuseStep 1049381 = 196759) (by norm_num)
theorem B590645 : Blo 275825 590645 := bbase (se 5 (by rfl) ⟨27686, by rfl⟩ : syracuseStep 590645 = 55373) (by norm_num)
theorem B295741 : Blo 275825 295741 := bbase (se 3 (by rfl) ⟨55451, by rfl⟩ : syracuseStep 295741 = 110903) (by norm_num)
theorem B623429 : Blo 275825 623429 := bbase (se 4 (by rfl) ⟨58446, by rfl⟩ : syracuseStep 623429 = 116893) (by norm_num)
theorem B394093 : Blo 275825 394093 := bbase (se 3 (by rfl) ⟨73892, by rfl⟩ : syracuseStep 394093 = 147785) (by norm_num)
theorem B623501 : Blo 275825 623501 := bbase (se 3 (by rfl) ⟨116906, by rfl⟩ : syracuseStep 623501 = 233813) (by norm_num)
theorem B951205 : Blo 275825 951205 := bbase (se 4 (by rfl) ⟨89175, by rfl⟩ : syracuseStep 951205 = 178351) (by norm_num)
theorem B623573 : Blo 275825 623573 := bbase (se 7 (by rfl) ⟨7307, by rfl⟩ : syracuseStep 623573 = 14615) (by norm_num)
theorem B623645 : Blo 275825 623645 := bbase (se 3 (by rfl) ⟨116933, by rfl⟩ : syracuseStep 623645 = 233867) (by norm_num)
theorem B1049669 : Blo 275825 1049669 := bbase (se 4 (by rfl) ⟨98406, by rfl⟩ : syracuseStep 1049669 = 196813) (by norm_num)
theorem B623717 : Blo 275825 623717 := bbase (se 4 (by rfl) ⟨58473, by rfl⟩ : syracuseStep 623717 = 116947) (by norm_num)
theorem B623789 : Blo 275825 623789 := bbase (se 3 (by rfl) ⟨116960, by rfl⟩ : syracuseStep 623789 = 233921) (by norm_num)
theorem B885941 : Blo 275825 885941 := bbase (se 5 (by rfl) ⟨41528, by rfl⟩ : syracuseStep 885941 = 83057) (by norm_num)
theorem B525541 : Blo 275825 525541 := bbase (se 4 (by rfl) ⟨49269, by rfl⟩ : syracuseStep 525541 = 98539) (by norm_num)
theorem B820469 : Blo 275825 820469 := bbase (se 5 (by rfl) ⟨38459, by rfl⟩ : syracuseStep 820469 = 76919) (by norm_num)
theorem B623861 : Blo 275825 623861 := bbase (se 5 (by rfl) ⟨29243, by rfl⟩ : syracuseStep 623861 = 58487) (by norm_num)
theorem B296185 : Blo 275825 296185 := bbase (se 2 (by rfl) ⟨111069, by rfl⟩ : syracuseStep 296185 = 222139) (by norm_num)
theorem B1803541 : Blo 275825 1803541 := bbase (se 6 (by rfl) ⟨42270, by rfl⟩ : syracuseStep 1803541 = 84541) (by norm_num)
theorem B886069 : Blo 275825 886069 := bbase (se 5 (by rfl) ⟨41534, by rfl⟩ : syracuseStep 886069 = 83069) (by norm_num)
theorem B787765 : Blo 275825 787765 := bbase (se 5 (by rfl) ⟨36926, by rfl⟩ : syracuseStep 787765 = 73853) (by norm_num)
theorem B296245 : Blo 275825 296245 := bbase (se 5 (by rfl) ⟨13886, by rfl⟩ : syracuseStep 296245 = 27773) (by norm_num)
theorem B623933 : Blo 275825 623933 := bbase (se 3 (by rfl) ⟨116987, by rfl⟩ : syracuseStep 623933 = 233975) (by norm_num)
theorem B525685 : Blo 275825 525685 := bbase (se 5 (by rfl) ⟨24641, by rfl⟩ : syracuseStep 525685 = 49283) (by norm_num)
theorem B624005 : Blo 275825 624005 := bbase (se 4 (by rfl) ⟨58500, by rfl⟩ : syracuseStep 624005 = 117001) (by norm_num)
theorem B361865 : Blo 275825 361865 := bbase (se 2 (by rfl) ⟨135699, by rfl⟩ : syracuseStep 361865 = 271399) (by norm_num)
theorem B624077 : Blo 275825 624077 := bbase (se 3 (by rfl) ⟨117014, by rfl⟩ : syracuseStep 624077 = 234029) (by norm_num)
theorem B1410533 : Blo 275825 1410533 := bbase (se 4 (by rfl) ⟨132237, by rfl⟩ : syracuseStep 1410533 = 264475) (by norm_num)
theorem B525845 : Blo 275825 525845 := bbase (se 6 (by rfl) ⟨12324, by rfl⟩ : syracuseStep 525845 = 24649) (by norm_num)
theorem B624149 : Blo 275825 624149 := bbase (se 6 (by rfl) ⟨14628, by rfl⟩ : syracuseStep 624149 = 29257) (by norm_num)
theorem B624221 : Blo 275825 624221 := bbase (se 3 (by rfl) ⟨117041, by rfl⟩ : syracuseStep 624221 = 234083) (by norm_num)
theorem B296561 : Blo 275825 296561 := bbase (se 2 (by rfl) ⟨111210, by rfl⟩ : syracuseStep 296561 = 222421) (by norm_num)
theorem B394885 : Blo 275825 394885 := bbase (se 4 (by rfl) ⟨37020, by rfl⟩ : syracuseStep 394885 = 74041) (by norm_num)
theorem B1574549 : Blo 275825 1574549 := bbase (se 6 (by rfl) ⟨36903, by rfl⟩ : syracuseStep 1574549 = 73807) (by norm_num)
theorem B525989 : Blo 275825 525989 := bbase (se 4 (by rfl) ⟨49311, by rfl⟩ : syracuseStep 525989 = 98623) (by norm_num)
theorem B624293 : Blo 275825 624293 := bbase (se 4 (by rfl) ⟨58527, by rfl⟩ : syracuseStep 624293 = 117055) (by norm_num)
theorem B591533 : Blo 275825 591533 := bbase (se 3 (by rfl) ⟨110912, by rfl⟩ : syracuseStep 591533 = 221825) (by norm_num)
theorem B624365 : Blo 275825 624365 := bbase (se 3 (by rfl) ⟨117068, by rfl⟩ : syracuseStep 624365 = 234137) (by norm_num)
theorem B624437 : Blo 275825 624437 := bbase (se 5 (by rfl) ⟨29270, by rfl⟩ : syracuseStep 624437 = 58541) (by norm_num)
theorem B624509 : Blo 275825 624509 := bbase (se 3 (by rfl) ⟨117095, by rfl⟩ : syracuseStep 624509 = 234191) (by norm_num)
theorem B591781 : Blo 275825 591781 := bbase (se 4 (by rfl) ⟨55479, by rfl⟩ : syracuseStep 591781 = 110959) (by norm_num)
theorem B526277 : Blo 275825 526277 := bbase (se 4 (by rfl) ⟨49338, by rfl⟩ : syracuseStep 526277 = 98677) (by norm_num)
theorem B624581 : Blo 275825 624581 := bbase (se 4 (by rfl) ⟨58554, by rfl⟩ : syracuseStep 624581 = 117109) (by norm_num)
theorem B395221 : Blo 275825 395221 := bbase (se 7 (by rfl) ⟨4631, by rfl⟩ : syracuseStep 395221 = 9263) (by norm_num)
theorem B3213269 : Blo 275825 3213269 := bbase (se 7 (by rfl) ⟨37655, by rfl⟩ : syracuseStep 3213269 = 75311) (by norm_num)
theorem B624653 : Blo 275825 624653 := bbase (se 3 (by rfl) ⟨117122, by rfl⟩ : syracuseStep 624653 = 234245) (by norm_num)
theorem B297005 : Blo 275825 297005 := bbase (se 3 (by rfl) ⟨55688, by rfl⟩ : syracuseStep 297005 = 111377) (by norm_num)
theorem B624725 : Blo 275825 624725 := bbase (se 8 (by rfl) ⟨3660, by rfl⟩ : syracuseStep 624725 = 7321) (by norm_num)
theorem B526429 : Blo 275825 526429 := bbase (se 3 (by rfl) ⟨98705, by rfl⟩ : syracuseStep 526429 = 197411) (by norm_num)
theorem B297065 : Blo 275825 297065 := bbase (se 2 (by rfl) ⟨111399, by rfl⟩ : syracuseStep 297065 = 222799) (by norm_num)
theorem B624797 : Blo 275825 624797 := bbase (se 3 (by rfl) ⟨117149, by rfl⟩ : syracuseStep 624797 = 234299) (by norm_num)
theorem B395437 : Blo 275825 395437 := bbase (se 3 (by rfl) ⟨74144, by rfl⟩ : syracuseStep 395437 = 148289) (by norm_num)
theorem B1050853 : Blo 275825 1050853 := bbase (se 4 (by rfl) ⟨98517, by rfl⟩ : syracuseStep 1050853 = 197035) (by norm_num)
theorem B624869 : Blo 275825 624869 := bbase (se 4 (by rfl) ⟨58581, by rfl⟩ : syracuseStep 624869 = 117163) (by norm_num)
theorem B297193 : Blo 275825 297193 := bbase (se 2 (by rfl) ⟨111447, by rfl⟩ : syracuseStep 297193 = 222895) (by norm_num)
theorem B624941 : Blo 275825 624941 := bbase (se 3 (by rfl) ⟨117176, by rfl⟩ : syracuseStep 624941 = 234353) (by norm_num)
theorem B625013 : Blo 275825 625013 := bbase (se 5 (by rfl) ⟨29297, by rfl⟩ : syracuseStep 625013 = 58595) (by norm_num)
theorem B788869 : Blo 275825 788869 := bbase (se 4 (by rfl) ⟨73956, by rfl⟩ : syracuseStep 788869 = 147913) (by norm_num)
theorem B526733 : Blo 275825 526733 := bbase (se 3 (by rfl) ⟨98762, by rfl⟩ : syracuseStep 526733 = 197525) (by norm_num)
theorem B592285 : Blo 275825 592285 := bbase (se 3 (by rfl) ⟨111053, by rfl⟩ : syracuseStep 592285 = 222107) (by norm_num)
theorem B625085 : Blo 275825 625085 := bbase (se 3 (by rfl) ⟨117203, by rfl⟩ : syracuseStep 625085 = 234407) (by norm_num)
theorem B559565 : Blo 275825 559565 := bbase (se 3 (by rfl) ⟨104918, by rfl⟩ : syracuseStep 559565 = 209837) (by norm_num)
theorem B625157 : Blo 275825 625157 := bbase (se 4 (by rfl) ⟨58608, by rfl⟩ : syracuseStep 625157 = 117217) (by norm_num)
theorem B1051157 : Blo 275825 1051157 := bbase (se 6 (by rfl) ⟨24636, by rfl⟩ : syracuseStep 1051157 = 49273) (by norm_num)
theorem B395813 : Blo 275825 395813 := bbase (se 4 (by rfl) ⟨37107, by rfl⟩ : syracuseStep 395813 = 74215) (by norm_num)
theorem B625229 : Blo 275825 625229 := bbase (se 3 (by rfl) ⟨117230, by rfl⟩ : syracuseStep 625229 = 234461) (by norm_num)
theorem B625301 : Blo 275825 625301 := bbase (se 6 (by rfl) ⟨14655, by rfl⟩ : syracuseStep 625301 = 29311) (by norm_num)
theorem B297637 : Blo 275825 297637 := bbase (se 4 (by rfl) ⟨27903, by rfl⟩ : syracuseStep 297637 = 55807) (by norm_num)
theorem B625373 : Blo 275825 625373 := bbase (se 3 (by rfl) ⟨117257, by rfl⟩ : syracuseStep 625373 = 234515) (by norm_num)
theorem B1411829 : Blo 275825 1411829 := bbase (se 5 (by rfl) ⟨66179, by rfl⟩ : syracuseStep 1411829 = 132359) (by norm_num)
theorem B297757 : Blo 275825 297757 := bbase (se 3 (by rfl) ⟨55829, by rfl⟩ : syracuseStep 297757 = 111659) (by norm_num)
theorem B625445 : Blo 275825 625445 := bbase (se 4 (by rfl) ⟨58635, by rfl⟩ : syracuseStep 625445 = 117271) (by norm_num)
theorem B1575733 : Blo 275825 1575733 := bbase (se 5 (by rfl) ⟨73862, by rfl⟩ : syracuseStep 1575733 = 147725) (by norm_num)
theorem B625517 : Blo 275825 625517 := bbase (se 3 (by rfl) ⟨117284, by rfl⟩ : syracuseStep 625517 = 234569) (by norm_num)
theorem B625589 : Blo 275825 625589 := bbase (se 5 (by rfl) ⟨29324, by rfl⟩ : syracuseStep 625589 = 58649) (by norm_num)
theorem B625661 : Blo 275825 625661 := bbase (se 3 (by rfl) ⟨117311, by rfl⟩ : syracuseStep 625661 = 234623) (by norm_num)
theorem B298009 : Blo 275825 298009 := bbase (se 2 (by rfl) ⟨111753, by rfl⟩ : syracuseStep 298009 = 223507) (by norm_num)
theorem B298013 : Blo 275825 298013 := bbase (se 3 (by rfl) ⟨55877, by rfl⟩ : syracuseStep 298013 = 111755) (by norm_num)
theorem B1182757 : Blo 275825 1182757 := bbase (se 4 (by rfl) ⟨110883, by rfl⟩ : syracuseStep 1182757 = 221767) (by norm_num)
theorem B560197 : Blo 275825 560197 := bbase (se 4 (by rfl) ⟨52518, by rfl⟩ : syracuseStep 560197 = 105037) (by norm_num)
theorem B625733 : Blo 275825 625733 := bbase (se 4 (by rfl) ⟨58662, by rfl⟩ : syracuseStep 625733 = 117325) (by norm_num)
theorem B527485 : Blo 275825 527485 := bbase (se 3 (by rfl) ⟨98903, by rfl⟩ : syracuseStep 527485 = 197807) (by norm_num)
theorem B625805 : Blo 275825 625805 := bbase (se 3 (by rfl) ⟨117338, by rfl⟩ : syracuseStep 625805 = 234677) (by norm_num)
theorem B625877 : Blo 275825 625877 := bbase (se 7 (by rfl) ⟨7334, by rfl⟩ : syracuseStep 625877 = 14669) (by norm_num)
theorem B527629 : Blo 275825 527629 := bbase (se 3 (by rfl) ⟨98930, by rfl⟩ : syracuseStep 527629 = 197861) (by norm_num)
theorem B593173 : Blo 275825 593173 := bbase (se 6 (by rfl) ⟨13902, by rfl⟩ : syracuseStep 593173 = 27805) (by norm_num)
theorem B625949 : Blo 275825 625949 := bbase (se 3 (by rfl) ⟨117365, by rfl⟩ : syracuseStep 625949 = 234731) (by norm_num)
theorem B626021 : Blo 275825 626021 := bbase (se 4 (by rfl) ⟨58689, by rfl⟩ : syracuseStep 626021 = 117379) (by norm_num)
theorem B527789 : Blo 275825 527789 := bbase (se 3 (by rfl) ⟨98960, by rfl⟩ : syracuseStep 527789 = 197921) (by norm_num)
theorem B626093 : Blo 275825 626093 := bbase (se 3 (by rfl) ⟨117392, by rfl⟩ : syracuseStep 626093 = 234785) (by norm_num)
theorem B626165 : Blo 275825 626165 := bbase (se 5 (by rfl) ⟨29351, by rfl⟩ : syracuseStep 626165 = 58703) (by norm_num)
theorem B527933 : Blo 275825 527933 := bbase (se 3 (by rfl) ⟨98987, by rfl⟩ : syracuseStep 527933 = 197975) (by norm_num)
theorem B626237 : Blo 275825 626237 := bbase (se 3 (by rfl) ⟨117419, by rfl⟩ : syracuseStep 626237 = 234839) (by norm_num)
theorem B298577 : Blo 275825 298577 := bbase (se 2 (by rfl) ⟨111966, by rfl⟩ : syracuseStep 298577 = 223933) (by norm_num)
theorem B560765 : Blo 275825 560765 := bbase (se 3 (by rfl) ⟨105143, by rfl⟩ : syracuseStep 560765 = 210287) (by norm_num)
theorem B626309 : Blo 275825 626309 := bbase (se 4 (by rfl) ⟨58716, by rfl⟩ : syracuseStep 626309 = 117433) (by norm_num)
theorem B626381 : Blo 275825 626381 := bbase (se 3 (by rfl) ⟨117446, by rfl⟩ : syracuseStep 626381 = 234893) (by norm_num)
theorem B593669 : Blo 275825 593669 := bbase (se 4 (by rfl) ⟨55656, by rfl⟩ : syracuseStep 593669 = 111313) (by norm_num)
theorem B298765 : Blo 275825 298765 := bbase (se 3 (by rfl) ⟨56018, by rfl⟩ : syracuseStep 298765 = 112037) (by norm_num)
theorem B626453 : Blo 275825 626453 := bbase (se 6 (by rfl) ⟨14682, by rfl⟩ : syracuseStep 626453 = 29365) (by norm_num)
theorem B528221 : Blo 275825 528221 := bbase (se 3 (by rfl) ⟨99041, by rfl⟩ : syracuseStep 528221 = 198083) (by norm_num)
theorem B626525 : Blo 275825 626525 := bbase (se 3 (by rfl) ⟨117473, by rfl⟩ : syracuseStep 626525 = 234947) (by norm_num)
theorem B790373 : Blo 275825 790373 := bbase (se 4 (by rfl) ⟨74097, by rfl⟩ : syracuseStep 790373 = 148195) (by norm_num)
theorem B2723701 : Blo 275825 2723701 := bbase (se 5 (by rfl) ⟨127673, by rfl⟩ : syracuseStep 2723701 = 255347) (by norm_num)
theorem B331661 : Blo 275825 331661 := bbase (se 3 (by rfl) ⟨62186, by rfl⟩ : syracuseStep 331661 = 124373) (by norm_num)
theorem B626597 : Blo 275825 626597 := bbase (se 4 (by rfl) ⟨58743, by rfl⟩ : syracuseStep 626597 = 117487) (by norm_num)
theorem B397237 : Blo 275825 397237 := bbase (se 5 (by rfl) ⟨18620, by rfl⟩ : syracuseStep 397237 = 37241) (by norm_num)
theorem B626669 : Blo 275825 626669 := bbase (se 3 (by rfl) ⟨117500, by rfl⟩ : syracuseStep 626669 = 235001) (by norm_num)
theorem B528373 : Blo 275825 528373 := bbase (se 5 (by rfl) ⟨24767, by rfl⟩ : syracuseStep 528373 = 49535) (by norm_num)
theorem B1413125 : Blo 275825 1413125 := bbase (se 4 (by rfl) ⟨132480, by rfl⟩ : syracuseStep 1413125 = 264961) (by norm_num)
theorem B626741 : Blo 275825 626741 := bbase (se 5 (by rfl) ⟨29378, by rfl⟩ : syracuseStep 626741 = 58757) (by norm_num)
theorem B626813 : Blo 275825 626813 := bbase (se 3 (by rfl) ⟨117527, by rfl⟩ : syracuseStep 626813 = 235055) (by norm_num)
theorem B888965 : Blo 275825 888965 := bbase (se 4 (by rfl) ⟨83340, by rfl⟩ : syracuseStep 888965 = 166681) (by norm_num)
theorem B626885 : Blo 275825 626885 := bbase (se 4 (by rfl) ⟨58770, by rfl⟩ : syracuseStep 626885 = 117541) (by norm_num)
theorem B331997 : Blo 275825 331997 := bbase (se 3 (by rfl) ⟨62249, by rfl⟩ : syracuseStep 331997 = 124499) (by norm_num)
theorem B626957 : Blo 275825 626957 := bbase (se 3 (by rfl) ⟨117554, by rfl⟩ : syracuseStep 626957 = 235109) (by norm_num)
theorem B528677 : Blo 275825 528677 := bbase (se 4 (by rfl) ⟨49563, by rfl⟩ : syracuseStep 528677 = 99127) (by norm_num)
theorem B332113 : Blo 275825 332113 := bbase (se 2 (by rfl) ⟨124542, by rfl⟩ : syracuseStep 332113 = 249085) (by norm_num)
theorem B2003285 : Blo 275825 2003285 := bbase (se 10 (by rfl) ⟨2934, by rfl⟩ : syracuseStep 2003285 = 5869) (by norm_num)
theorem B627029 : Blo 275825 627029 := bbase (se 10 (by rfl) ⟨918, by rfl⟩ : syracuseStep 627029 = 1837) (by norm_num)
theorem B332185 : Blo 275825 332185 := bbase (se 2 (by rfl) ⟨124569, by rfl⟩ : syracuseStep 332185 = 249139) (by norm_num)
theorem B627101 : Blo 275825 627101 := bbase (se 3 (by rfl) ⟨117581, by rfl⟩ : syracuseStep 627101 = 235163) (by norm_num)
theorem B332209 : Blo 275825 332209 := bbase (se 2 (by rfl) ⟨124578, by rfl⟩ : syracuseStep 332209 = 249157) (by norm_num)
theorem B627173 : Blo 275825 627173 := bbase (se 4 (by rfl) ⟨58797, by rfl⟩ : syracuseStep 627173 = 117595) (by norm_num)
theorem B397829 : Blo 275825 397829 := bbase (se 4 (by rfl) ⟨37296, by rfl⟩ : syracuseStep 397829 = 74593) (by norm_num)
theorem B627245 : Blo 275825 627245 := bbase (se 3 (by rfl) ⟨117608, by rfl⟩ : syracuseStep 627245 = 235217) (by norm_num)
theorem B332353 : Blo 275825 332353 := bbase (se 2 (by rfl) ⟨124632, by rfl⟩ : syracuseStep 332353 = 249265) (by norm_num)
theorem B1053269 : Blo 275825 1053269 := bbase (se 8 (by rfl) ⟨6171, by rfl⟩ : syracuseStep 1053269 = 12343) (by norm_num)
theorem B397909 : Blo 275825 397909 := bbase (se 8 (by rfl) ⟨2331, by rfl⟩ : syracuseStep 397909 = 4663) (by norm_num)
theorem B627317 : Blo 275825 627317 := bbase (se 5 (by rfl) ⟨29405, by rfl⟩ : syracuseStep 627317 = 58811) (by norm_num)
theorem B594557 : Blo 275825 594557 := bbase (se 3 (by rfl) ⟨111479, by rfl⟩ : syracuseStep 594557 = 222959) (by norm_num)
theorem B627389 : Blo 275825 627389 := bbase (se 3 (by rfl) ⟨117635, by rfl⟩ : syracuseStep 627389 = 235271) (by norm_num)
theorem B398029 : Blo 275825 398029 := bbase (se 3 (by rfl) ⟨74630, by rfl⟩ : syracuseStep 398029 = 149261) (by norm_num)
theorem B1577717 : Blo 275825 1577717 := bbase (se 5 (by rfl) ⟨73955, by rfl⟩ : syracuseStep 1577717 = 147911) (by norm_num)
theorem B594677 : Blo 275825 594677 := bbase (se 5 (by rfl) ⟨27875, by rfl⟩ : syracuseStep 594677 = 55751) (by norm_num)
theorem B627461 : Blo 275825 627461 := bbase (se 4 (by rfl) ⟨58824, by rfl⟩ : syracuseStep 627461 = 117649) (by norm_num)
theorem B398125 : Blo 275825 398125 := bbase (se 3 (by rfl) ⟨74648, by rfl⟩ : syracuseStep 398125 = 149297) (by norm_num)
theorem B627533 : Blo 275825 627533 := bbase (se 3 (by rfl) ⟨117662, by rfl⟩ : syracuseStep 627533 = 235325) (by norm_num)
theorem B1053557 : Blo 275825 1053557 := bbase (se 5 (by rfl) ⟨49385, by rfl⟩ : syracuseStep 1053557 = 98771) (by norm_num)
theorem B627605 : Blo 275825 627605 := bbase (se 6 (by rfl) ⟨14709, by rfl⟩ : syracuseStep 627605 = 29419) (by norm_num)
theorem B627677 : Blo 275825 627677 := bbase (se 3 (by rfl) ⟨117689, by rfl⟩ : syracuseStep 627677 = 235379) (by norm_num)
theorem B3052565 : Blo 275825 3052565 := bbase (se 6 (by rfl) ⟨71544, by rfl⟩ : syracuseStep 3052565 = 143089) (by norm_num)
theorem B529429 : Blo 275825 529429 := bbase (se 6 (by rfl) ⟨12408, by rfl⟩ : syracuseStep 529429 = 24817) (by norm_num)
theorem B627749 : Blo 275825 627749 := bbase (se 4 (by rfl) ⟨58851, by rfl⟩ : syracuseStep 627749 = 117703) (by norm_num)
theorem B627821 : Blo 275825 627821 := bbase (se 3 (by rfl) ⟨117716, by rfl⟩ : syracuseStep 627821 = 235433) (by norm_num)
theorem B529573 : Blo 275825 529573 := bbase (se 4 (by rfl) ⟨49647, by rfl⟩ : syracuseStep 529573 = 99295) (by norm_num)
theorem B627893 : Blo 275825 627893 := bbase (se 5 (by rfl) ⟨29432, by rfl⟩ : syracuseStep 627893 = 58865) (by norm_num)
theorem B627965 : Blo 275825 627965 := bbase (se 3 (by rfl) ⟨117743, by rfl⟩ : syracuseStep 627965 = 235487) (by norm_num)
theorem B1414421 : Blo 275825 1414421 := bbase (se 6 (by rfl) ⟨33150, by rfl⟩ : syracuseStep 1414421 = 66301) (by norm_num)
theorem B300349 : Blo 275825 300349 := bbase (se 3 (by rfl) ⟨56315, by rfl⟩ : syracuseStep 300349 = 112631) (by norm_num)
theorem B529733 : Blo 275825 529733 := bbase (se 4 (by rfl) ⟨49662, by rfl⟩ : syracuseStep 529733 = 99325) (by norm_num)
theorem B628037 : Blo 275825 628037 := bbase (se 4 (by rfl) ⟨58878, by rfl⟩ : syracuseStep 628037 = 117757) (by norm_num)
theorem B595309 : Blo 275825 595309 := bbase (se 3 (by rfl) ⟨111620, by rfl⟩ : syracuseStep 595309 = 223241) (by norm_num)
theorem B628109 : Blo 275825 628109 := bbase (se 3 (by rfl) ⟨117770, by rfl⟩ : syracuseStep 628109 = 235541) (by norm_num)
theorem B791957 : Blo 275825 791957 := bbase (se 6 (by rfl) ⟨18561, by rfl⟩ : syracuseStep 791957 = 37123) (by norm_num)
theorem B529877 : Blo 275825 529877 := bbase (se 7 (by rfl) ⟨6209, by rfl⟩ : syracuseStep 529877 = 12419) (by norm_num)
theorem B628181 : Blo 275825 628181 := bbase (se 7 (by rfl) ⟨7361, by rfl⟩ : syracuseStep 628181 = 14723) (by norm_num)
theorem B1218053 : Blo 275825 1218053 := bbase (se 4 (by rfl) ⟨114192, by rfl⟩ : syracuseStep 1218053 = 228385) (by norm_num)
theorem B955925 : Blo 275825 955925 := bbase (se 6 (by rfl) ⟨22404, by rfl⟩ : syracuseStep 955925 = 44809) (by norm_num)
theorem B628253 : Blo 275825 628253 := bbase (se 3 (by rfl) ⟨117797, by rfl⟩ : syracuseStep 628253 = 235595) (by norm_num)
theorem B628325 : Blo 275825 628325 := bbase (se 4 (by rfl) ⟨58905, by rfl⟩ : syracuseStep 628325 = 117811) (by norm_num)
theorem B628397 : Blo 275825 628397 := bbase (se 3 (by rfl) ⟨117824, by rfl⟩ : syracuseStep 628397 = 235649) (by norm_num)
theorem B530165 : Blo 275825 530165 := bbase (se 5 (by rfl) ⟨24851, by rfl⟩ : syracuseStep 530165 = 49703) (by norm_num)
theorem B628469 : Blo 275825 628469 := bbase (se 5 (by rfl) ⟨29459, by rfl⟩ : syracuseStep 628469 = 58919) (by norm_num)
theorem B333569 : Blo 275825 333569 := bbase (se 2 (by rfl) ⟨125088, by rfl⟩ : syracuseStep 333569 = 250177) (by norm_num)
theorem B628541 : Blo 275825 628541 := bbase (se 3 (by rfl) ⟨117851, by rfl⟩ : syracuseStep 628541 = 235703) (by norm_num)
theorem B628613 : Blo 275825 628613 := bbase (se 4 (by rfl) ⟨58932, by rfl⟩ : syracuseStep 628613 = 117865) (by norm_num)
theorem B530317 : Blo 275825 530317 := bbase (se 3 (by rfl) ⟨99434, by rfl⟩ : syracuseStep 530317 = 198869) (by norm_num)
theorem B628685 : Blo 275825 628685 := bbase (se 3 (by rfl) ⟨117878, by rfl⟩ : syracuseStep 628685 = 235757) (by norm_num)
theorem B1185749 : Blo 275825 1185749 := bbase (se 7 (by rfl) ⟨13895, by rfl⟩ : syracuseStep 1185749 = 27791) (by norm_num)
theorem B1054741 : Blo 275825 1054741 := bbase (se 6 (by rfl) ⟨24720, by rfl⟩ : syracuseStep 1054741 = 49441) (by norm_num)
theorem B628757 : Blo 275825 628757 := bbase (se 6 (by rfl) ⟨14736, by rfl⟩ : syracuseStep 628757 = 29473) (by norm_num)
theorem B333877 : Blo 275825 333877 := bbase (se 5 (by rfl) ⟨15650, by rfl⟩ : syracuseStep 333877 = 31301) (by norm_num)
theorem B792629 : Blo 275825 792629 := bbase (se 5 (by rfl) ⟨37154, by rfl⟩ : syracuseStep 792629 = 74309) (by norm_num)
theorem B628829 : Blo 275825 628829 := bbase (se 3 (by rfl) ⟨117905, by rfl⟩ : syracuseStep 628829 = 235811) (by norm_num)
theorem B333977 : Blo 275825 333977 := bbase (se 2 (by rfl) ⟨125241, by rfl⟩ : syracuseStep 333977 = 250483) (by norm_num)
theorem B628901 : Blo 275825 628901 := bbase (se 4 (by rfl) ⟨58959, by rfl⟩ : syracuseStep 628901 = 117919) (by norm_num)
theorem B530621 : Blo 275825 530621 := bbase (se 3 (by rfl) ⟨99491, by rfl⟩ : syracuseStep 530621 = 198983) (by norm_num)
theorem B596197 : Blo 275825 596197 := bbase (se 4 (by rfl) ⟨55893, by rfl⟩ : syracuseStep 596197 = 111787) (by norm_num)
theorem B628973 : Blo 275825 628973 := bbase (se 3 (by rfl) ⟨117932, by rfl⟩ : syracuseStep 628973 = 235865) (by norm_num)
theorem B891157 : Blo 275825 891157 := bbase (se 6 (by rfl) ⟨20886, by rfl⟩ : syracuseStep 891157 = 41773) (by norm_num)
theorem B629045 : Blo 275825 629045 := bbase (se 5 (by rfl) ⟨29486, by rfl⟩ : syracuseStep 629045 = 58973) (by norm_num)
theorem B1055045 : Blo 275825 1055045 := bbase (se 4 (by rfl) ⟨98910, by rfl⟩ : syracuseStep 1055045 = 197821) (by norm_num)
theorem B596317 : Blo 275825 596317 := bbase (se 3 (by rfl) ⟨111809, by rfl⟩ : syracuseStep 596317 = 223619) (by norm_num)
theorem B629117 : Blo 275825 629117 := bbase (se 3 (by rfl) ⟨117959, by rfl⟩ : syracuseStep 629117 = 235919) (by norm_num)
theorem B629189 : Blo 275825 629189 := bbase (se 4 (by rfl) ⟨58986, by rfl⟩ : syracuseStep 629189 = 117973) (by norm_num)
theorem B793061 : Blo 275825 793061 := bbase (se 4 (by rfl) ⟨74349, by rfl⟩ : syracuseStep 793061 = 148699) (by norm_num)
theorem B629261 : Blo 275825 629261 := bbase (se 3 (by rfl) ⟨117986, by rfl⟩ : syracuseStep 629261 = 235973) (by norm_num)
theorem B1415717 : Blo 275825 1415717 := bbase (se 4 (by rfl) ⟨132723, by rfl⟩ : syracuseStep 1415717 = 265447) (by norm_num)
theorem B498221 : Blo 275825 498221 := bbase (se 3 (by rfl) ⟨93416, by rfl⟩ : syracuseStep 498221 = 186833) (by norm_num)
theorem B334381 : Blo 275825 334381 := bbase (se 3 (by rfl) ⟨62696, by rfl⟩ : syracuseStep 334381 = 125393) (by norm_num)
theorem B465493 : Blo 275825 465493 := bbase (se 8 (by rfl) ⟨2727, by rfl⟩ : syracuseStep 465493 = 5455) (by norm_num)
theorem B2103893 : Blo 275825 2103893 := bbase (se 8 (by rfl) ⟨12327, by rfl⟩ : syracuseStep 2103893 = 24655) (by norm_num)
theorem B629333 : Blo 275825 629333 := bbase (se 8 (by rfl) ⟨3687, by rfl⟩ : syracuseStep 629333 = 7375) (by norm_num)
theorem B596573 : Blo 275825 596573 := bbase (se 3 (by rfl) ⟨111857, by rfl⟩ : syracuseStep 596573 = 223715) (by norm_num)
theorem B629405 : Blo 275825 629405 := bbase (se 3 (by rfl) ⟨118013, by rfl⟩ : syracuseStep 629405 = 236027) (by norm_num)
theorem B465581 : Blo 275825 465581 := bbase (se 3 (by rfl) ⟨87296, by rfl⟩ : syracuseStep 465581 = 174593) (by norm_num)
theorem B629477 : Blo 275825 629477 := bbase (se 4 (by rfl) ⟨59013, by rfl⟩ : syracuseStep 629477 = 118027) (by norm_num)
theorem B465709 : Blo 275825 465709 := bbase (se 3 (by rfl) ⟨87320, by rfl⟩ : syracuseStep 465709 = 174641) (by norm_num)
theorem B629549 : Blo 275825 629549 := bbase (se 3 (by rfl) ⟨118040, by rfl⟩ : syracuseStep 629549 = 236081) (by norm_num)
theorem B1121141 : Blo 275825 1121141 := bbase (se 5 (by rfl) ⟨52553, by rfl⟩ : syracuseStep 1121141 = 105107) (by norm_num)
theorem B465797 : Blo 275825 465797 := bbase (se 4 (by rfl) ⟨43668, by rfl⟩ : syracuseStep 465797 = 87337) (by norm_num)
theorem B1579925 : Blo 275825 1579925 := bbase (se 6 (by rfl) ⟨37029, by rfl⟩ : syracuseStep 1579925 = 74059) (by norm_num)
theorem B334765 : Blo 275825 334765 := bbase (se 3 (by rfl) ⟨62768, by rfl⟩ : syracuseStep 334765 = 125537) (by norm_num)
theorem B1186757 : Blo 275825 1186757 := bbase (se 4 (by rfl) ⟨111258, by rfl⟩ : syracuseStep 1186757 = 222517) (by norm_num)
theorem B465925 : Blo 275825 465925 := bbase (se 4 (by rfl) ⟨43680, by rfl⟩ : syracuseStep 465925 = 87361) (by norm_num)
theorem B891989 : Blo 275825 891989 := bbase (se 8 (by rfl) ⟨5226, by rfl⟩ : syracuseStep 891989 = 10453) (by norm_num)
theorem B466013 : Blo 275825 466013 := bbase (se 3 (by rfl) ⟨87377, by rfl⟩ : syracuseStep 466013 = 174755) (by norm_num)
theorem B793813 : Blo 275825 793813 := bbase (se 7 (by rfl) ⟨9302, by rfl⟩ : syracuseStep 793813 = 18605) (by norm_num)
theorem B466141 : Blo 275825 466141 := bbase (se 3 (by rfl) ⟨87401, by rfl⟩ : syracuseStep 466141 = 174803) (by norm_num)
theorem B466229 : Blo 275825 466229 := bbase (se 5 (by rfl) ⟨21854, by rfl⟩ : syracuseStep 466229 = 43709) (by norm_num)
theorem B302393 : Blo 275825 302393 := bbase (se 2 (by rfl) ⟨113397, by rfl⟩ : syracuseStep 302393 = 226795) (by norm_num)
theorem B466357 : Blo 275825 466357 := bbase (se 5 (by rfl) ⟨21860, by rfl⟩ : syracuseStep 466357 = 43721) (by norm_num)
theorem B597461 : Blo 275825 597461 := bbase (se 7 (by rfl) ⟨7001, by rfl⟩ : syracuseStep 597461 = 14003) (by norm_num)
theorem B466445 : Blo 275825 466445 := bbase (se 3 (by rfl) ⟨87458, by rfl⟩ : syracuseStep 466445 = 174917) (by norm_num)
theorem B663149 : Blo 275825 663149 := bbase (se 3 (by rfl) ⟨124340, by rfl⟩ : syracuseStep 663149 = 248681) (by norm_num)
theorem B564869 : Blo 275825 564869 := bbase (se 4 (by rfl) ⟨52956, by rfl⟩ : syracuseStep 564869 = 105913) (by norm_num)
theorem B466573 : Blo 275825 466573 := bbase (se 3 (by rfl) ⟨87482, by rfl⟩ : syracuseStep 466573 = 174965) (by norm_num)
theorem B466661 : Blo 275825 466661 := bbase (se 4 (by rfl) ⟨43749, by rfl⟩ : syracuseStep 466661 = 87499) (by norm_num)
theorem B335621 : Blo 275825 335621 := bbase (se 4 (by rfl) ⟨31464, by rfl⟩ : syracuseStep 335621 = 62929) (by norm_num)
theorem B466789 : Blo 275825 466789 := bbase (se 4 (by rfl) ⟨43761, by rfl⟩ : syracuseStep 466789 = 87523) (by norm_num)
theorem B466877 : Blo 275825 466877 := bbase (se 3 (by rfl) ⟨87539, by rfl⟩ : syracuseStep 466877 = 175079) (by norm_num)
theorem B1777621 : Blo 275825 1777621 := bbase (se 7 (by rfl) ⟨20831, by rfl⟩ : syracuseStep 1777621 = 41663) (by norm_num)
theorem B663533 : Blo 275825 663533 := bbase (se 3 (by rfl) ⟨124412, by rfl⟩ : syracuseStep 663533 = 248825) (by norm_num)
theorem B1122341 : Blo 275825 1122341 := bbase (se 4 (by rfl) ⟨105219, by rfl⟩ : syracuseStep 1122341 = 210439) (by norm_num)
theorem B335929 : Blo 275825 335929 := bbase (se 2 (by rfl) ⟨125973, by rfl⟩ : syracuseStep 335929 = 251947) (by norm_num)
theorem B467005 : Blo 275825 467005 := bbase (se 3 (by rfl) ⟨87563, by rfl⟩ : syracuseStep 467005 = 175127) (by norm_num)
theorem B467093 : Blo 275825 467093 := bbase (se 6 (by rfl) ⟨10947, by rfl⟩ : syracuseStep 467093 = 21895) (by norm_num)
theorem B2367701 : Blo 275825 2367701 := bbase (se 7 (by rfl) ⟨27746, by rfl⟩ : syracuseStep 2367701 = 55493) (by norm_num)
theorem B565501 : Blo 275825 565501 := bbase (se 3 (by rfl) ⟨106031, by rfl⟩ : syracuseStep 565501 = 212063) (by norm_num)
theorem B336145 : Blo 275825 336145 := bbase (se 2 (by rfl) ⟨126054, by rfl⟩ : syracuseStep 336145 = 252109) (by norm_num)
theorem B467221 : Blo 275825 467221 := bbase (se 6 (by rfl) ⟨10950, by rfl⟩ : syracuseStep 467221 = 21901) (by norm_num)
theorem B12165461 : Blo 275825 12165461 := bbase (se 10 (by rfl) ⟨17820, by rfl⟩ : syracuseStep 12165461 = 35641) (by norm_num)
theorem B467309 : Blo 275825 467309 := bbase (se 3 (by rfl) ⟨87620, by rfl⟩ : syracuseStep 467309 = 175241) (by norm_num)
theorem B1057157 : Blo 275825 1057157 := bbase (se 4 (by rfl) ⟨99108, by rfl⟩ : syracuseStep 1057157 = 198217) (by norm_num)
theorem B467437 : Blo 275825 467437 := bbase (se 3 (by rfl) ⟨87644, by rfl⟩ : syracuseStep 467437 = 175289) (by norm_num)
theorem B467525 : Blo 275825 467525 := bbase (se 4 (by rfl) ⟨43830, by rfl⟩ : syracuseStep 467525 = 87661) (by norm_num)
theorem B1679957 : Blo 275825 1679957 := bbase (se 8 (by rfl) ⟨9843, by rfl⟩ : syracuseStep 1679957 = 19687) (by norm_num)
theorem B1057445 : Blo 275825 1057445 := bbase (se 4 (by rfl) ⟨99135, by rfl⟩ : syracuseStep 1057445 = 198271) (by norm_num)
theorem B1188533 : Blo 275825 1188533 := bbase (se 5 (by rfl) ⟨55712, by rfl⟩ : syracuseStep 1188533 = 111425) (by norm_num)
theorem B467653 : Blo 275825 467653 := bbase (se 4 (by rfl) ⟨43842, by rfl⟩ : syracuseStep 467653 = 87685) (by norm_num)
theorem B402149 : Blo 275825 402149 := bbase (se 4 (by rfl) ⟨37701, by rfl⟩ : syracuseStep 402149 = 75403) (by norm_num)
theorem B467741 : Blo 275825 467741 := bbase (se 3 (by rfl) ⟨87701, by rfl⟩ : syracuseStep 467741 = 175403) (by norm_num)
theorem B3449749 : Blo 275825 3449749 := bbase (se 6 (by rfl) ⟨80853, by rfl⟩ : syracuseStep 3449749 = 161707) (by norm_num)
theorem B467869 : Blo 275825 467869 := bbase (se 3 (by rfl) ⟨87725, by rfl⟩ : syracuseStep 467869 = 175451) (by norm_num)
theorem B893861 : Blo 275825 893861 := bbase (se 4 (by rfl) ⟨83799, by rfl⟩ : syracuseStep 893861 = 167599) (by norm_num)
theorem B467957 : Blo 275825 467957 := bbase (se 5 (by rfl) ⟨21935, by rfl⟩ : syracuseStep 467957 = 43871) (by norm_num)
theorem B468085 : Blo 275825 468085 := bbase (se 5 (by rfl) ⟨21941, by rfl⟩ : syracuseStep 468085 = 43883) (by norm_num)
theorem B468173 : Blo 275825 468173 := bbase (se 3 (by rfl) ⟨87782, by rfl⟩ : syracuseStep 468173 = 175565) (by norm_num)
theorem B1123541 : Blo 275825 1123541 := bbase (se 7 (by rfl) ⟨13166, by rfl⟩ : syracuseStep 1123541 = 26333) (by norm_num)
theorem B468301 : Blo 275825 468301 := bbase (se 3 (by rfl) ⟨87806, by rfl⟩ : syracuseStep 468301 = 175613) (by norm_num)
theorem B599381 : Blo 275825 599381 := bbase (se 12 (by rfl) ⟨219, by rfl⟩ : syracuseStep 599381 = 439) (by norm_num)
theorem B566669 : Blo 275825 566669 := bbase (se 3 (by rfl) ⟨106250, by rfl⟩ : syracuseStep 566669 = 212501) (by norm_num)
theorem B468389 : Blo 275825 468389 := bbase (se 4 (by rfl) ⟨43911, by rfl⟩ : syracuseStep 468389 = 87823) (by norm_num)
theorem B468517 : Blo 275825 468517 := bbase (se 4 (by rfl) ⟨43923, by rfl⟩ : syracuseStep 468517 = 87847) (by norm_num)
theorem B468605 : Blo 275825 468605 := bbase (se 3 (by rfl) ⟨87863, by rfl⟩ : syracuseStep 468605 = 175727) (by norm_num)
theorem B337589 : Blo 275825 337589 := bbase (se 5 (by rfl) ⟨15824, by rfl⟩ : syracuseStep 337589 = 31649) (by norm_num)
theorem B665293 : Blo 275825 665293 := bbase (se 3 (by rfl) ⟨124742, by rfl⟩ : syracuseStep 665293 = 249485) (by norm_num)
theorem B468733 : Blo 275825 468733 := bbase (se 3 (by rfl) ⟨87887, by rfl⟩ : syracuseStep 468733 = 175775) (by norm_num)
theorem B1058629 : Blo 275825 1058629 := bbase (se 4 (by rfl) ⟨99246, by rfl⟩ : syracuseStep 1058629 = 198493) (by norm_num)
theorem B468821 : Blo 275825 468821 := bbase (se 9 (by rfl) ⟨1373, by rfl⟩ : syracuseStep 468821 = 2747) (by norm_num)
theorem B468949 : Blo 275825 468949 := bbase (se 7 (by rfl) ⟨5495, by rfl⟩ : syracuseStep 468949 = 10991) (by norm_num)
theorem B698341 : Blo 275825 698341 := bbase (se 4 (by rfl) ⟨65469, by rfl⟩ : syracuseStep 698341 = 130939) (by norm_num)
theorem B796661 : Blo 275825 796661 := bbase (se 5 (by rfl) ⟨37343, by rfl⟩ : syracuseStep 796661 = 74687) (by norm_num)
theorem B469037 : Blo 275825 469037 := bbase (se 3 (by rfl) ⟨87944, by rfl⟩ : syracuseStep 469037 = 175889) (by norm_num)
theorem B698453 : Blo 275825 698453 := bbase (se 8 (by rfl) ⟨4092, by rfl⟩ : syracuseStep 698453 = 8185) (by norm_num)
theorem B1058933 : Blo 275825 1058933 := bbase (se 5 (by rfl) ⟨49637, by rfl⟩ : syracuseStep 1058933 = 99275) (by norm_num)
theorem B469165 : Blo 275825 469165 := bbase (se 3 (by rfl) ⟨87968, by rfl⟩ : syracuseStep 469165 = 175937) (by norm_num)
theorem B469253 : Blo 275825 469253 := bbase (se 4 (by rfl) ⟨43992, by rfl⟩ : syracuseStep 469253 = 87985) (by norm_num)
theorem B698645 : Blo 275825 698645 := bbase (se 6 (by rfl) ⟨16374, by rfl⟩ : syracuseStep 698645 = 32749) (by norm_num)
theorem B567685 : Blo 275825 567685 := bbase (se 4 (by rfl) ⟨53220, by rfl⟩ : syracuseStep 567685 = 106441) (by norm_num)
theorem B469381 : Blo 275825 469381 := bbase (se 4 (by rfl) ⟨44004, by rfl⟩ : syracuseStep 469381 = 88009) (by norm_num)
theorem B502205 : Blo 275825 502205 := bbase (se 3 (by rfl) ⟨94163, by rfl⟩ : syracuseStep 502205 = 188327) (by norm_num)
theorem B338369 : Blo 275825 338369 := bbase (se 2 (by rfl) ⟨126888, by rfl⟩ : syracuseStep 338369 = 253777) (by norm_num)
theorem B469469 : Blo 275825 469469 := bbase (se 3 (by rfl) ⟨88025, by rfl⟩ : syracuseStep 469469 = 176051) (by norm_num)
theorem B469597 : Blo 275825 469597 := bbase (se 3 (by rfl) ⟨88049, by rfl⟩ : syracuseStep 469597 = 176099) (by norm_num)
theorem B698989 : Blo 275825 698989 := bbase (se 3 (by rfl) ⟨131060, by rfl⟩ : syracuseStep 698989 = 262121) (by norm_num)
theorem B2009717 : Blo 275825 2009717 := bbase (se 5 (by rfl) ⟨94205, by rfl⟩ : syracuseStep 2009717 = 188411) (by norm_num)
theorem B469685 : Blo 275825 469685 := bbase (se 5 (by rfl) ⟨22016, by rfl⟩ : syracuseStep 469685 = 44033) (by norm_num)
theorem B666301 : Blo 275825 666301 := bbase (se 3 (by rfl) ⟨124931, by rfl⟩ : syracuseStep 666301 = 249863) (by norm_num)
theorem B699101 : Blo 275825 699101 := bbase (se 3 (by rfl) ⟨131081, by rfl⟩ : syracuseStep 699101 = 262163) (by norm_num)
theorem B666397 : Blo 275825 666397 := bbase (se 3 (by rfl) ⟨124949, by rfl⟩ : syracuseStep 666397 = 249899) (by norm_num)
theorem B469813 : Blo 275825 469813 := bbase (se 5 (by rfl) ⟨22022, by rfl⟩ : syracuseStep 469813 = 44045) (by norm_num)
theorem B502661 : Blo 275825 502661 := bbase (se 4 (by rfl) ⟨47124, by rfl⟩ : syracuseStep 502661 = 94249) (by norm_num)
theorem B469901 : Blo 275825 469901 := bbase (se 3 (by rfl) ⟨88106, by rfl⟩ : syracuseStep 469901 = 176213) (by norm_num)
theorem B699293 : Blo 275825 699293 := bbase (se 3 (by rfl) ⟨131117, by rfl⟩ : syracuseStep 699293 = 262235) (by norm_num)
theorem B1518581 : Blo 275825 1518581 := bbase (se 5 (by rfl) ⟨71183, by rfl⟩ : syracuseStep 1518581 = 142367) (by norm_num)
theorem B470029 : Blo 275825 470029 := bbase (se 3 (by rfl) ⟨88130, by rfl⟩ : syracuseStep 470029 = 176261) (by norm_num)
theorem B470117 : Blo 275825 470117 := bbase (se 4 (by rfl) ⟨44073, by rfl⟩ : syracuseStep 470117 = 88147) (by norm_num)
theorem B470245 : Blo 275825 470245 := bbase (se 4 (by rfl) ⟨44085, by rfl⟩ : syracuseStep 470245 = 88171) (by norm_num)
theorem B699637 : Blo 275825 699637 := bbase (se 5 (by rfl) ⟨32795, by rfl⟩ : syracuseStep 699637 = 65591) (by norm_num)
theorem B666917 : Blo 275825 666917 := bbase (se 4 (by rfl) ⟨62523, by rfl⟩ : syracuseStep 666917 = 125047) (by norm_num)
theorem B470333 : Blo 275825 470333 := bbase (se 3 (by rfl) ⟨88187, by rfl⟩ : syracuseStep 470333 = 176375) (by norm_num)
theorem B699749 : Blo 275825 699749 := bbase (se 4 (by rfl) ⟨65601, by rfl⟩ : syracuseStep 699749 = 131203) (by norm_num)
theorem B470461 : Blo 275825 470461 := bbase (se 3 (by rfl) ⟨88211, by rfl⟩ : syracuseStep 470461 = 176423) (by norm_num)
theorem B1125845 : Blo 275825 1125845 := bbase (se 7 (by rfl) ⟨13193, by rfl⟩ : syracuseStep 1125845 = 26387) (by norm_num)
theorem B470549 : Blo 275825 470549 := bbase (se 6 (by rfl) ⟨11028, by rfl⟩ : syracuseStep 470549 = 22057) (by norm_num)
theorem B699941 : Blo 275825 699941 := bbase (se 4 (by rfl) ⟨65619, by rfl⟩ : syracuseStep 699941 = 131239) (by norm_num)
theorem B4763285 : Blo 275825 4763285 := bbase (se 6 (by rfl) ⟨111639, by rfl⟩ : syracuseStep 4763285 = 223279) (by norm_num)
theorem B470677 : Blo 275825 470677 := bbase (se 6 (by rfl) ⟨11031, by rfl⟩ : syracuseStep 470677 = 22063) (by norm_num)
theorem B798389 : Blo 275825 798389 := bbase (se 5 (by rfl) ⟨37424, by rfl⟩ : syracuseStep 798389 = 74849) (by norm_num)
theorem B536285 : Blo 275825 536285 := bbase (se 3 (by rfl) ⟨100553, by rfl⟩ : syracuseStep 536285 = 201107) (by norm_num)
theorem B470765 : Blo 275825 470765 := bbase (se 3 (by rfl) ⟨88268, by rfl⟩ : syracuseStep 470765 = 176537) (by norm_num)
theorem B1421077 : Blo 275825 1421077 := bbase (se 6 (by rfl) ⟨33306, by rfl⟩ : syracuseStep 1421077 = 66613) (by norm_num)
theorem B667445 : Blo 275825 667445 := bbase (se 5 (by rfl) ⟨31286, by rfl⟩ : syracuseStep 667445 = 62573) (by norm_num)
theorem B3977045 : Blo 275825 3977045 := bbase (se 9 (by rfl) ⟨11651, by rfl⟩ : syracuseStep 3977045 = 23303) (by norm_num)
theorem B470893 : Blo 275825 470893 := bbase (se 3 (by rfl) ⟨88292, by rfl⟩ : syracuseStep 470893 = 176585) (by norm_num)
theorem B1781621 : Blo 275825 1781621 := bbase (se 5 (by rfl) ⟨83513, by rfl⟩ : syracuseStep 1781621 = 167027) (by norm_num)
theorem B700285 : Blo 275825 700285 := bbase (se 3 (by rfl) ⟨131303, by rfl⟩ : syracuseStep 700285 = 262607) (by norm_num)
theorem B470981 : Blo 275825 470981 := bbase (se 4 (by rfl) ⟨44154, by rfl⟩ : syracuseStep 470981 = 88309) (by norm_num)
theorem B700397 : Blo 275825 700397 := bbase (se 3 (by rfl) ⟨131324, by rfl⟩ : syracuseStep 700397 = 262649) (by norm_num)
theorem B667685 : Blo 275825 667685 := bbase (se 4 (by rfl) ⟨62595, by rfl⟩ : syracuseStep 667685 = 125191) (by norm_num)
theorem B634949 : Blo 275825 634949 := bbase (se 4 (by rfl) ⟨59526, by rfl⟩ : syracuseStep 634949 = 119053) (by norm_num)
theorem B471109 : Blo 275825 471109 := bbase (se 4 (by rfl) ⟨44166, by rfl⟩ : syracuseStep 471109 = 88333) (by norm_num)
theorem B471197 : Blo 275825 471197 := bbase (se 3 (by rfl) ⟨88349, by rfl⟩ : syracuseStep 471197 = 176699) (by norm_num)
theorem B700589 : Blo 275825 700589 := bbase (se 3 (by rfl) ⟨131360, by rfl⟩ : syracuseStep 700589 = 262721) (by norm_num)
theorem B1061045 : Blo 275825 1061045 := bbase (se 5 (by rfl) ⟨49736, by rfl⟩ : syracuseStep 1061045 = 99473) (by norm_num)
theorem B2699477 : Blo 275825 2699477 := bbase (se 7 (by rfl) ⟨31634, by rfl⟩ : syracuseStep 2699477 = 63269) (by norm_num)
theorem B471325 : Blo 275825 471325 := bbase (se 3 (by rfl) ⟨88373, by rfl⟩ : syracuseStep 471325 = 176747) (by norm_num)
theorem B471413 : Blo 275825 471413 := bbase (se 5 (by rfl) ⟨22097, by rfl⟩ : syracuseStep 471413 = 44195) (by norm_num)
theorem B504181 : Blo 275825 504181 := bbase (se 5 (by rfl) ⟨23633, by rfl⟩ : syracuseStep 504181 = 47267) (by norm_num)
theorem B1061333 : Blo 275825 1061333 := bbase (se 7 (by rfl) ⟨12437, by rfl⟩ : syracuseStep 1061333 = 24875) (by norm_num)
theorem B471541 : Blo 275825 471541 := bbase (se 5 (by rfl) ⟨22103, by rfl⟩ : syracuseStep 471541 = 44207) (by norm_num)
theorem B700933 : Blo 275825 700933 := bbase (se 4 (by rfl) ⟨65712, by rfl⟩ : syracuseStep 700933 = 131425) (by norm_num)
theorem B602653 : Blo 275825 602653 := bbase (se 3 (by rfl) ⟨112997, by rfl⟩ : syracuseStep 602653 = 225995) (by norm_num)
theorem B471629 : Blo 275825 471629 := bbase (se 3 (by rfl) ⟨88430, by rfl⟩ : syracuseStep 471629 = 176861) (by norm_num)
theorem B701045 : Blo 275825 701045 := bbase (se 5 (by rfl) ⟨32861, by rfl⟩ : syracuseStep 701045 = 65723) (by norm_num)
theorem B471757 : Blo 275825 471757 := bbase (se 3 (by rfl) ⟨88454, by rfl⟩ : syracuseStep 471757 = 176909) (by norm_num)
theorem B471845 : Blo 275825 471845 := bbase (se 4 (by rfl) ⟨44235, by rfl⟩ : syracuseStep 471845 = 88471) (by norm_num)
theorem B799541 : Blo 275825 799541 := bbase (se 5 (by rfl) ⟨37478, by rfl⟩ : syracuseStep 799541 = 74957) (by norm_num)
theorem B701237 : Blo 275825 701237 := bbase (se 5 (by rfl) ⟨32870, by rfl⟩ : syracuseStep 701237 = 65741) (by norm_num)
theorem B1192805 : Blo 275825 1192805 := bbase (se 4 (by rfl) ⟨111825, by rfl⟩ : syracuseStep 1192805 = 223651) (by norm_num)
theorem B471941 : Blo 275825 471941 := bbase (se 4 (by rfl) ⟨44244, by rfl⟩ : syracuseStep 471941 = 88489) (by norm_num)
theorem B471973 : Blo 275825 471973 := bbase (se 4 (by rfl) ⟨44247, by rfl⟩ : syracuseStep 471973 = 88495) (by norm_num)
theorem B471997 : Blo 275825 471997 := bbase (se 3 (by rfl) ⟨88499, by rfl⟩ : syracuseStep 471997 = 176999) (by norm_num)
theorem B472061 : Blo 275825 472061 := bbase (se 3 (by rfl) ⟨88511, by rfl⟩ : syracuseStep 472061 = 177023) (by norm_num)
theorem B472189 : Blo 275825 472189 := bbase (se 3 (by rfl) ⟨88535, by rfl⟩ : syracuseStep 472189 = 177071) (by norm_num)
theorem B701581 : Blo 275825 701581 := bbase (se 3 (by rfl) ⟨131546, by rfl⟩ : syracuseStep 701581 = 263093) (by norm_num)
theorem B931013 : Blo 275825 931013 := bbase (se 4 (by rfl) ⟨87282, by rfl⟩ : syracuseStep 931013 = 174565) (by norm_num)
theorem B701693 : Blo 275825 701693 := bbase (se 3 (by rfl) ⟨131567, by rfl⟩ : syracuseStep 701693 = 263135) (by norm_num)
theorem B701885 : Blo 275825 701885 := bbase (se 3 (by rfl) ⟨131603, by rfl⟩ : syracuseStep 701885 = 263207) (by norm_num)
theorem B6305365 : Blo 275825 6305365 := bbase (se 8 (by rfl) ⟨36945, by rfl⟩ : syracuseStep 6305365 = 73891) (by norm_num)
theorem B931445 : Blo 275825 931445 := bbase (se 5 (by rfl) ⟨43661, by rfl⟩ : syracuseStep 931445 = 87323) (by norm_num)
theorem B669397 : Blo 275825 669397 := bbase (se 7 (by rfl) ⟨7844, by rfl⟩ : syracuseStep 669397 = 15689) (by norm_num)
theorem B2668277 : Blo 275825 2668277 := bbase (se 5 (by rfl) ⟨125075, by rfl⟩ : syracuseStep 2668277 = 250151) (by norm_num)
theorem B702229 : Blo 275825 702229 := bbase (se 6 (by rfl) ⟨16458, by rfl⟩ : syracuseStep 702229 = 32917) (by norm_num)
theorem B505685 : Blo 275825 505685 := bbase (se 9 (by rfl) ⟨1481, by rfl⟩ : syracuseStep 505685 = 2963) (by norm_num)
theorem B702341 : Blo 275825 702341 := bbase (se 4 (by rfl) ⟨65844, by rfl⟩ : syracuseStep 702341 = 131689) (by norm_num)
theorem B931877 : Blo 275825 931877 := bbase (se 4 (by rfl) ⟨87363, by rfl⟩ : syracuseStep 931877 = 174727) (by norm_num)
theorem B702533 : Blo 275825 702533 := bbase (se 4 (by rfl) ⟨65862, by rfl⟩ : syracuseStep 702533 = 131725) (by norm_num)
theorem B2111669 : Blo 275825 2111669 := bbase (se 5 (by rfl) ⟨98984, by rfl⟩ : syracuseStep 2111669 = 197969) (by norm_num)
theorem B899381 : Blo 275825 899381 := bbase (se 5 (by rfl) ⟨42158, by rfl⟩ : syracuseStep 899381 = 84317) (by norm_num)
theorem B702877 : Blo 275825 702877 := bbase (se 3 (by rfl) ⟨131789, by rfl⟩ : syracuseStep 702877 = 263579) (by norm_num)
theorem B932309 : Blo 275825 932309 := bbase (se 7 (by rfl) ⟨10925, by rfl⟩ : syracuseStep 932309 = 21851) (by norm_num)
theorem B506341 : Blo 275825 506341 := bbase (se 4 (by rfl) ⟨47469, by rfl⟩ : syracuseStep 506341 = 94939) (by norm_num)
theorem B637429 : Blo 275825 637429 := bbase (se 5 (by rfl) ⟨29879, by rfl⟩ : syracuseStep 637429 = 59759) (by norm_num)
theorem B702989 : Blo 275825 702989 := bbase (se 3 (by rfl) ⟨131810, by rfl⟩ : syracuseStep 702989 = 263621) (by norm_num)
theorem B1194581 : Blo 275825 1194581 := bbase (se 8 (by rfl) ⟨6999, by rfl⟩ : syracuseStep 1194581 = 13999) (by norm_num)
theorem B1522357 : Blo 275825 1522357 := bbase (se 5 (by rfl) ⟨71360, by rfl⟩ : syracuseStep 1522357 = 142721) (by norm_num)
theorem B703181 : Blo 275825 703181 := bbase (se 3 (by rfl) ⟨131846, by rfl⟩ : syracuseStep 703181 = 263693) (by norm_num)
theorem B1194821 : Blo 275825 1194821 := bbase (se 4 (by rfl) ⟨112014, by rfl⟩ : syracuseStep 1194821 = 224029) (by norm_num)
theorem B932741 : Blo 275825 932741 := bbase (se 4 (by rfl) ⟨87444, by rfl⟩ : syracuseStep 932741 = 174889) (by norm_num)
theorem B703525 : Blo 275825 703525 := bbase (se 4 (by rfl) ⟨65955, by rfl⟩ : syracuseStep 703525 = 131911) (by norm_num)
theorem B310333 : Blo 275825 310333 := bbase (se 3 (by rfl) ⟨58187, by rfl⟩ : syracuseStep 310333 = 116375) (by norm_num)
theorem B310369 : Blo 275825 310369 := bbase (se 2 (by rfl) ⟨116388, by rfl⟩ : syracuseStep 310369 = 232777) (by norm_num)
theorem B670837 : Blo 275825 670837 := bbase (se 5 (by rfl) ⟨31445, by rfl⟩ : syracuseStep 670837 = 62891) (by norm_num)
theorem B310405 : Blo 275825 310405 := bbase (se 4 (by rfl) ⟨29100, by rfl⟩ : syracuseStep 310405 = 58201) (by norm_num)
theorem B703637 : Blo 275825 703637 := bbase (se 6 (by rfl) ⟨16491, by rfl⟩ : syracuseStep 703637 = 32983) (by norm_num)
theorem B310441 : Blo 275825 310441 := bbase (se 2 (by rfl) ⟨116415, by rfl⟩ : syracuseStep 310441 = 232831) (by norm_num)
theorem B310477 : Blo 275825 310477 := bbase (se 3 (by rfl) ⟨58214, by rfl⟩ : syracuseStep 310477 = 116429) (by norm_num)
theorem B310513 : Blo 275825 310513 := bbase (se 2 (by rfl) ⟨116442, by rfl⟩ : syracuseStep 310513 = 232885) (by norm_num)
theorem B310549 : Blo 275825 310549 := bbase (se 6 (by rfl) ⟨7278, by rfl⟩ : syracuseStep 310549 = 14557) (by norm_num)
theorem B1359125 : Blo 275825 1359125 := bbase (se 6 (by rfl) ⟨31854, by rfl⟩ : syracuseStep 1359125 = 63709) (by norm_num)
theorem B933173 : Blo 275825 933173 := bbase (se 5 (by rfl) ⟨43742, by rfl⟩ : syracuseStep 933173 = 87485) (by norm_num)
theorem B310585 : Blo 275825 310585 := bbase (se 2 (by rfl) ⟨116469, by rfl⟩ : syracuseStep 310585 = 232939) (by norm_num)
theorem B7585109 : Blo 275825 7585109 := bbase (se 11 (by rfl) ⟨5555, by rfl⟩ : syracuseStep 7585109 = 11111) (by norm_num)
theorem B703829 : Blo 275825 703829 := bbase (se 11 (by rfl) ⟨515, by rfl⟩ : syracuseStep 703829 = 1031) (by norm_num)
theorem B310621 : Blo 275825 310621 := bbase (se 3 (by rfl) ⟨58241, by rfl⟩ : syracuseStep 310621 = 116483) (by norm_num)
theorem B310657 : Blo 275825 310657 := bbase (se 2 (by rfl) ⟨116496, by rfl⟩ : syracuseStep 310657 = 232993) (by norm_num)
theorem B638357 : Blo 275825 638357 := bbase (se 6 (by rfl) ⟨14961, by rfl⟩ : syracuseStep 638357 = 29923) (by norm_num)
theorem B310693 : Blo 275825 310693 := bbase (se 4 (by rfl) ⟨29127, by rfl⟩ : syracuseStep 310693 = 58255) (by norm_num)
theorem B310729 : Blo 275825 310729 := bbase (se 2 (by rfl) ⟨116523, by rfl⟩ : syracuseStep 310729 = 233047) (by norm_num)
theorem B310765 : Blo 275825 310765 := bbase (se 3 (by rfl) ⟨58268, by rfl⟩ : syracuseStep 310765 = 116537) (by norm_num)
theorem B2145781 : Blo 275825 2145781 := bbase (se 5 (by rfl) ⟨100583, by rfl⟩ : syracuseStep 2145781 = 201167) (by norm_num)
theorem B310801 : Blo 275825 310801 := bbase (se 2 (by rfl) ⟨116550, by rfl⟩ : syracuseStep 310801 = 233101) (by norm_num)
theorem B310837 : Blo 275825 310837 := bbase (se 5 (by rfl) ⟨14570, by rfl⟩ : syracuseStep 310837 = 29141) (by norm_num)
theorem B310873 : Blo 275825 310873 := bbase (se 2 (by rfl) ⟨116577, by rfl⟩ : syracuseStep 310873 = 233155) (by norm_num)
theorem B310909 : Blo 275825 310909 := bbase (se 3 (by rfl) ⟨58295, by rfl⟩ : syracuseStep 310909 = 116591) (by norm_num)
theorem B310945 : Blo 275825 310945 := bbase (se 2 (by rfl) ⟨116604, by rfl⟩ : syracuseStep 310945 = 233209) (by norm_num)
theorem B704173 : Blo 275825 704173 := bbase (se 3 (by rfl) ⟨132032, by rfl⟩ : syracuseStep 704173 = 264065) (by norm_num)
theorem B310981 : Blo 275825 310981 := bbase (se 4 (by rfl) ⟨29154, by rfl⟩ : syracuseStep 310981 = 58309) (by norm_num)
theorem B376525 : Blo 275825 376525 := bbase (se 3 (by rfl) ⟨70598, by rfl⟩ : syracuseStep 376525 = 141197) (by norm_num)
theorem B671453 : Blo 275825 671453 := bbase (se 3 (by rfl) ⟨125897, by rfl⟩ : syracuseStep 671453 = 251795) (by norm_num)
theorem B933605 : Blo 275825 933605 := bbase (se 4 (by rfl) ⟨87525, by rfl⟩ : syracuseStep 933605 = 175051) (by norm_num)
theorem B311017 : Blo 275825 311017 := bbase (se 2 (by rfl) ⟨116631, by rfl⟩ : syracuseStep 311017 = 233263) (by norm_num)
theorem B442093 : Blo 275825 442093 := bbase (se 3 (by rfl) ⟨82892, by rfl⟩ : syracuseStep 442093 = 165785) (by norm_num)
theorem B311053 : Blo 275825 311053 := bbase (se 3 (by rfl) ⟨58322, by rfl⟩ : syracuseStep 311053 = 116645) (by norm_num)
theorem B704285 : Blo 275825 704285 := bbase (se 3 (by rfl) ⟨132053, by rfl⟩ : syracuseStep 704285 = 264107) (by norm_num)
theorem B311089 : Blo 275825 311089 := bbase (se 2 (by rfl) ⟨116658, by rfl⟩ : syracuseStep 311089 = 233317) (by norm_num)
theorem B311125 : Blo 275825 311125 := bbase (se 9 (by rfl) ⟨911, by rfl⟩ : syracuseStep 311125 = 1823) (by norm_num)
theorem B311161 : Blo 275825 311161 := bbase (se 2 (by rfl) ⟨116685, by rfl⟩ : syracuseStep 311161 = 233371) (by norm_num)
theorem B311197 : Blo 275825 311197 := bbase (se 3 (by rfl) ⟨58349, by rfl⟩ : syracuseStep 311197 = 116699) (by norm_num)
theorem B671645 : Blo 275825 671645 := bbase (se 3 (by rfl) ⟨125933, by rfl⟩ : syracuseStep 671645 = 251867) (by norm_num)
theorem B376741 : Blo 275825 376741 := bbase (se 4 (by rfl) ⟨35319, by rfl⟩ : syracuseStep 376741 = 70639) (by norm_num)
theorem B311233 : Blo 275825 311233 := bbase (se 2 (by rfl) ⟨116712, by rfl⟩ : syracuseStep 311233 = 233425) (by norm_num)
theorem B704477 : Blo 275825 704477 := bbase (se 3 (by rfl) ⟨132089, by rfl⟩ : syracuseStep 704477 = 264179) (by norm_num)
theorem B311269 : Blo 275825 311269 := bbase (se 4 (by rfl) ⟨29181, by rfl⟩ : syracuseStep 311269 = 58363) (by norm_num)
theorem B311305 : Blo 275825 311305 := bbase (se 2 (by rfl) ⟨116739, by rfl⟩ : syracuseStep 311305 = 233479) (by norm_num)
theorem B311341 : Blo 275825 311341 := bbase (se 3 (by rfl) ⟨58376, by rfl⟩ : syracuseStep 311341 = 116753) (by norm_num)
theorem B311377 : Blo 275825 311377 := bbase (se 2 (by rfl) ⟨116766, by rfl⟩ : syracuseStep 311377 = 233533) (by norm_num)
theorem B311413 : Blo 275825 311413 := bbase (se 5 (by rfl) ⟨14597, by rfl⟩ : syracuseStep 311413 = 29195) (by norm_num)
theorem B934037 : Blo 275825 934037 := bbase (se 6 (by rfl) ⟨21891, by rfl⟩ : syracuseStep 934037 = 43783) (by norm_num)
theorem B1130645 : Blo 275825 1130645 := bbase (se 6 (by rfl) ⟨26499, by rfl⟩ : syracuseStep 1130645 = 52999) (by norm_num)
theorem B311449 : Blo 275825 311449 := bbase (se 2 (by rfl) ⟨116793, by rfl⟩ : syracuseStep 311449 = 233587) (by norm_num)
theorem B311485 : Blo 275825 311485 := bbase (se 3 (by rfl) ⟨58403, by rfl⟩ : syracuseStep 311485 = 116807) (by norm_num)
theorem B671933 : Blo 275825 671933 := bbase (se 3 (by rfl) ⟨125987, by rfl⟩ : syracuseStep 671933 = 251975) (by norm_num)
theorem B311521 : Blo 275825 311521 := bbase (se 2 (by rfl) ⟨116820, by rfl⟩ : syracuseStep 311521 = 233641) (by norm_num)
theorem B311557 : Blo 275825 311557 := bbase (se 4 (by rfl) ⟨29208, by rfl⟩ : syracuseStep 311557 = 58417) (by norm_num)
theorem B311593 : Blo 275825 311593 := bbase (se 2 (by rfl) ⟨116847, by rfl⟩ : syracuseStep 311593 = 233695) (by norm_num)
theorem B475445 : Blo 275825 475445 := bbase (se 5 (by rfl) ⟨22286, by rfl⟩ : syracuseStep 475445 = 44573) (by norm_num)
theorem B704821 : Blo 275825 704821 := bbase (se 5 (by rfl) ⟨33038, by rfl⟩ : syracuseStep 704821 = 66077) (by norm_num)
theorem B311629 : Blo 275825 311629 := bbase (se 3 (by rfl) ⟨58430, by rfl⟩ : syracuseStep 311629 = 116861) (by norm_num)
theorem B311665 : Blo 275825 311665 := bbase (se 2 (by rfl) ⟨116874, by rfl⟩ : syracuseStep 311665 = 233749) (by norm_num)
theorem B442765 : Blo 275825 442765 := bbase (se 3 (by rfl) ⟨83018, by rfl⟩ : syracuseStep 442765 = 166037) (by norm_num)
theorem B311701 : Blo 275825 311701 := bbase (se 6 (by rfl) ⟨7305, by rfl⟩ : syracuseStep 311701 = 14611) (by norm_num)
theorem B704933 : Blo 275825 704933 := bbase (se 4 (by rfl) ⟨66087, by rfl⟩ : syracuseStep 704933 = 132175) (by norm_num)
theorem B311737 : Blo 275825 311737 := bbase (se 2 (by rfl) ⟨116901, by rfl⟩ : syracuseStep 311737 = 233803) (by norm_num)
theorem B311773 : Blo 275825 311773 := bbase (se 3 (by rfl) ⟨58457, by rfl⟩ : syracuseStep 311773 = 116915) (by norm_num)
theorem B573941 : Blo 275825 573941 := bbase (se 5 (by rfl) ⟨26903, by rfl⟩ : syracuseStep 573941 = 53807) (by norm_num)
theorem B377341 : Blo 275825 377341 := bbase (se 3 (by rfl) ⟨70751, by rfl⟩ : syracuseStep 377341 = 141503) (by norm_num)
theorem B311809 : Blo 275825 311809 := bbase (se 2 (by rfl) ⟨116928, by rfl⟩ : syracuseStep 311809 = 233857) (by norm_num)
theorem B311845 : Blo 275825 311845 := bbase (se 4 (by rfl) ⟨29235, by rfl⟩ : syracuseStep 311845 = 58471) (by norm_num)
theorem B1589813 : Blo 275825 1589813 := bbase (se 5 (by rfl) ⟨74522, by rfl⟩ : syracuseStep 1589813 = 149045) (by norm_num)
theorem B934469 : Blo 275825 934469 := bbase (se 4 (by rfl) ⟨87606, by rfl⟩ : syracuseStep 934469 = 175213) (by norm_num)
theorem B311881 : Blo 275825 311881 := bbase (se 2 (by rfl) ⟨116955, by rfl⟩ : syracuseStep 311881 = 233911) (by norm_num)
theorem B475733 : Blo 275825 475733 := bbase (se 8 (by rfl) ⟨2787, by rfl⟩ : syracuseStep 475733 = 5575) (by norm_num)
theorem B705125 : Blo 275825 705125 := bbase (se 4 (by rfl) ⟨66105, by rfl⟩ : syracuseStep 705125 = 132211) (by norm_num)
theorem B311917 : Blo 275825 311917 := bbase (se 3 (by rfl) ⟨58484, by rfl⟩ : syracuseStep 311917 = 116969) (by norm_num)
theorem B311953 : Blo 275825 311953 := bbase (se 2 (by rfl) ⟨116982, by rfl⟩ : syracuseStep 311953 = 233965) (by norm_num)
theorem B311989 : Blo 275825 311989 := bbase (se 5 (by rfl) ⟨14624, by rfl⟩ : syracuseStep 311989 = 29249) (by norm_num)
theorem B1000133 : Blo 275825 1000133 := bbase (se 4 (by rfl) ⟨93762, by rfl⟩ : syracuseStep 1000133 = 187525) (by norm_num)
theorem B312025 : Blo 275825 312025 := bbase (se 2 (by rfl) ⟨117009, by rfl⟩ : syracuseStep 312025 = 234019) (by norm_num)
theorem B312061 : Blo 275825 312061 := bbase (se 3 (by rfl) ⟨58511, by rfl⟩ : syracuseStep 312061 = 117023) (by norm_num)
theorem B312097 : Blo 275825 312097 := bbase (se 2 (by rfl) ⟨117036, by rfl⟩ : syracuseStep 312097 = 234073) (by norm_num)
theorem B312133 : Blo 275825 312133 := bbase (se 4 (by rfl) ⟨29262, by rfl⟩ : syracuseStep 312133 = 58525) (by norm_num)
theorem B312169 : Blo 275825 312169 := bbase (se 2 (by rfl) ⟨117063, by rfl⟩ : syracuseStep 312169 = 234127) (by norm_num)
theorem B312205 : Blo 275825 312205 := bbase (se 3 (by rfl) ⟨58538, by rfl⟩ : syracuseStep 312205 = 117077) (by norm_num)
theorem B312241 : Blo 275825 312241 := bbase (se 2 (by rfl) ⟨117090, by rfl⟩ : syracuseStep 312241 = 234181) (by norm_num)
theorem B705469 : Blo 275825 705469 := bbase (se 3 (by rfl) ⟨132275, by rfl⟩ : syracuseStep 705469 = 264551) (by norm_num)
theorem B312277 : Blo 275825 312277 := bbase (se 7 (by rfl) ⟨3659, by rfl⟩ : syracuseStep 312277 = 7319) (by norm_num)
theorem B934901 : Blo 275825 934901 := bbase (se 5 (by rfl) ⟨43823, by rfl⟩ : syracuseStep 934901 = 87647) (by norm_num)
theorem B312313 : Blo 275825 312313 := bbase (se 2 (by rfl) ⟨117117, by rfl⟩ : syracuseStep 312313 = 234235) (by norm_num)
theorem B312349 : Blo 275825 312349 := bbase (se 3 (by rfl) ⟨58565, by rfl⟩ : syracuseStep 312349 = 117131) (by norm_num)
theorem B705581 : Blo 275825 705581 := bbase (se 3 (by rfl) ⟨132296, by rfl⟩ : syracuseStep 705581 = 264593) (by norm_num)
theorem B312385 : Blo 275825 312385 := bbase (se 2 (by rfl) ⟨117144, by rfl⟩ : syracuseStep 312385 = 234289) (by norm_num)
theorem B312421 : Blo 275825 312421 := bbase (se 4 (by rfl) ⟨29289, by rfl⟩ : syracuseStep 312421 = 58579) (by norm_num)
theorem B312457 : Blo 275825 312457 := bbase (se 2 (by rfl) ⟨117171, by rfl⟩ : syracuseStep 312457 = 234343) (by norm_num)
theorem B312493 : Blo 275825 312493 := bbase (se 3 (by rfl) ⟨58592, by rfl⟩ : syracuseStep 312493 = 117185) (by norm_num)
theorem B312529 : Blo 275825 312529 := bbase (se 2 (by rfl) ⟨117198, by rfl⟩ : syracuseStep 312529 = 234397) (by norm_num)
theorem B705773 : Blo 275825 705773 := bbase (se 3 (by rfl) ⟨132332, by rfl⟩ : syracuseStep 705773 = 264665) (by norm_num)
theorem B312565 : Blo 275825 312565 := bbase (se 5 (by rfl) ⟨14651, by rfl⟩ : syracuseStep 312565 = 29303) (by norm_num)
theorem B312601 : Blo 275825 312601 := bbase (se 2 (by rfl) ⟨117225, by rfl⟩ : syracuseStep 312601 = 234451) (by norm_num)
theorem B345385 : Blo 275825 345385 := bbase (se 2 (by rfl) ⟨129519, by rfl⟩ : syracuseStep 345385 = 259039) (by norm_num)
theorem B312637 : Blo 275825 312637 := bbase (se 3 (by rfl) ⟨58619, by rfl⟩ : syracuseStep 312637 = 117239) (by norm_num)
theorem B312673 : Blo 275825 312673 := bbase (se 2 (by rfl) ⟨117252, by rfl⟩ : syracuseStep 312673 = 234505) (by norm_num)
theorem B443765 : Blo 275825 443765 := bbase (se 5 (by rfl) ⟨20801, by rfl⟩ : syracuseStep 443765 = 41603) (by norm_num)
theorem B312709 : Blo 275825 312709 := bbase (se 4 (by rfl) ⟨29316, by rfl⟩ : syracuseStep 312709 = 58633) (by norm_num)
theorem B935333 : Blo 275825 935333 := bbase (se 4 (by rfl) ⟨87687, by rfl⟩ : syracuseStep 935333 = 175375) (by norm_num)
theorem B312745 : Blo 275825 312745 := bbase (se 2 (by rfl) ⟨117279, by rfl⟩ : syracuseStep 312745 = 234559) (by norm_num)
theorem B312781 : Blo 275825 312781 := bbase (se 3 (by rfl) ⟨58646, by rfl⟩ : syracuseStep 312781 = 117293) (by norm_num)
theorem B312817 : Blo 275825 312817 := bbase (se 2 (by rfl) ⟨117306, by rfl⟩ : syracuseStep 312817 = 234613) (by norm_num)
theorem B312853 : Blo 275825 312853 := bbase (se 6 (by rfl) ⟨7332, by rfl⟩ : syracuseStep 312853 = 14665) (by norm_num)
theorem B476717 : Blo 275825 476717 := bbase (se 3 (by rfl) ⟨89384, by rfl⟩ : syracuseStep 476717 = 178769) (by norm_num)
theorem B312889 : Blo 275825 312889 := bbase (se 2 (by rfl) ⟨117333, by rfl⟩ : syracuseStep 312889 = 234667) (by norm_num)
theorem B706117 : Blo 275825 706117 := bbase (se 4 (by rfl) ⟨66198, by rfl⟩ : syracuseStep 706117 = 132397) (by norm_num)
theorem B312925 : Blo 275825 312925 := bbase (se 3 (by rfl) ⟨58673, by rfl⟩ : syracuseStep 312925 = 117347) (by norm_num)
theorem B312961 : Blo 275825 312961 := bbase (se 2 (by rfl) ⟨117360, by rfl⟩ : syracuseStep 312961 = 234721) (by norm_num)
theorem B312997 : Blo 275825 312997 := bbase (se 4 (by rfl) ⟨29343, by rfl⟩ : syracuseStep 312997 = 58687) (by norm_num)
theorem B706229 : Blo 275825 706229 := bbase (se 5 (by rfl) ⟨33104, by rfl⟩ : syracuseStep 706229 = 66209) (by norm_num)
theorem B313033 : Blo 275825 313033 := bbase (se 2 (by rfl) ⟨117387, by rfl⟩ : syracuseStep 313033 = 234775) (by norm_num)
theorem B313069 : Blo 275825 313069 := bbase (se 3 (by rfl) ⟨58700, by rfl⟩ : syracuseStep 313069 = 117401) (by norm_num)
theorem B313105 : Blo 275825 313105 := bbase (se 2 (by rfl) ⟨117414, by rfl⟩ : syracuseStep 313105 = 234829) (by norm_num)
theorem B1787669 : Blo 275825 1787669 := bbase (se 6 (by rfl) ⟨41898, by rfl⟩ : syracuseStep 1787669 = 83797) (by norm_num)
theorem B313141 : Blo 275825 313141 := bbase (se 5 (by rfl) ⟨14678, by rfl⟩ : syracuseStep 313141 = 29357) (by norm_num)
theorem B935765 : Blo 275825 935765 := bbase (se 9 (by rfl) ⟨2741, by rfl⟩ : syracuseStep 935765 = 5483) (by norm_num)
theorem B313177 : Blo 275825 313177 := bbase (se 2 (by rfl) ⟨117441, by rfl⟩ : syracuseStep 313177 = 234883) (by norm_num)
theorem B706421 : Blo 275825 706421 := bbase (se 5 (by rfl) ⟨33113, by rfl⟩ : syracuseStep 706421 = 66227) (by norm_num)
theorem B313213 : Blo 275825 313213 := bbase (se 3 (by rfl) ⟨58727, by rfl⟩ : syracuseStep 313213 = 117455) (by norm_num)
theorem B313249 : Blo 275825 313249 := bbase (se 2 (by rfl) ⟨117468, by rfl⟩ : syracuseStep 313249 = 234937) (by norm_num)
theorem B313285 : Blo 275825 313285 := bbase (se 4 (by rfl) ⟨29370, by rfl⟩ : syracuseStep 313285 = 58741) (by norm_num)
theorem B280541 : Blo 275825 280541 := bbase (se 3 (by rfl) ⟨52601, by rfl⟩ : syracuseStep 280541 = 105203) (by norm_num)
theorem B313321 : Blo 275825 313321 := bbase (se 2 (by rfl) ⟨117495, by rfl⟩ : syracuseStep 313321 = 234991) (by norm_num)
theorem B280577 : Blo 275825 280577 := bbase (se 2 (by rfl) ⟨105216, by rfl⟩ : syracuseStep 280577 = 210433) (by norm_num)
theorem B313357 : Blo 275825 313357 := bbase (se 3 (by rfl) ⟨58754, by rfl⟩ : syracuseStep 313357 = 117509) (by norm_num)
theorem B313393 : Blo 275825 313393 := bbase (se 2 (by rfl) ⟨117522, by rfl⟩ : syracuseStep 313393 = 235045) (by norm_num)
theorem B12863573 : Blo 275825 12863573 := bbase (se 8 (by rfl) ⟨75372, by rfl⟩ : syracuseStep 12863573 = 150745) (by norm_num)
theorem B313429 : Blo 275825 313429 := bbase (se 8 (by rfl) ⟨1836, by rfl⟩ : syracuseStep 313429 = 3673) (by norm_num)
theorem B313465 : Blo 275825 313465 := bbase (se 2 (by rfl) ⟨117549, by rfl⟩ : syracuseStep 313465 = 235099) (by norm_num)
theorem B1230997 : Blo 275825 1230997 := bbase (se 6 (by rfl) ⟨28851, by rfl⟩ : syracuseStep 1230997 = 57703) (by norm_num)
theorem B313501 : Blo 275825 313501 := bbase (se 3 (by rfl) ⟨58781, by rfl⟩ : syracuseStep 313501 = 117563) (by norm_num)
theorem B313537 : Blo 275825 313537 := bbase (se 2 (by rfl) ⟨117576, by rfl⟩ : syracuseStep 313537 = 235153) (by norm_num)
theorem B477389 : Blo 275825 477389 := bbase (se 3 (by rfl) ⟨89510, by rfl⟩ : syracuseStep 477389 = 179021) (by norm_num)
theorem B706765 : Blo 275825 706765 := bbase (se 3 (by rfl) ⟨132518, by rfl⟩ : syracuseStep 706765 = 265037) (by norm_num)
theorem B313573 : Blo 275825 313573 := bbase (se 4 (by rfl) ⟨29397, by rfl⟩ : syracuseStep 313573 = 58795) (by norm_num)
theorem B936197 : Blo 275825 936197 := bbase (se 4 (by rfl) ⟨87768, by rfl⟩ : syracuseStep 936197 = 175537) (by norm_num)
theorem B1132805 : Blo 275825 1132805 := bbase (se 4 (by rfl) ⟨106200, by rfl⟩ : syracuseStep 1132805 = 212401) (by norm_num)
theorem B313609 : Blo 275825 313609 := bbase (se 2 (by rfl) ⟨117603, by rfl⟩ : syracuseStep 313609 = 235207) (by norm_num)
theorem B313645 : Blo 275825 313645 := bbase (se 3 (by rfl) ⟨58808, by rfl⟩ : syracuseStep 313645 = 117617) (by norm_num)
theorem B706877 : Blo 275825 706877 := bbase (se 3 (by rfl) ⟨132539, by rfl⟩ : syracuseStep 706877 = 265079) (by norm_num)
theorem B313681 : Blo 275825 313681 := bbase (se 2 (by rfl) ⟨117630, by rfl⟩ : syracuseStep 313681 = 235261) (by norm_num)
theorem B313717 : Blo 275825 313717 := bbase (se 5 (by rfl) ⟨14705, by rfl⟩ : syracuseStep 313717 = 29411) (by norm_num)
theorem B313753 : Blo 275825 313753 := bbase (se 2 (by rfl) ⟨117657, by rfl⟩ : syracuseStep 313753 = 235315) (by norm_num)
theorem B313789 : Blo 275825 313789 := bbase (se 3 (by rfl) ⟨58835, by rfl⟩ : syracuseStep 313789 = 117671) (by norm_num)
theorem B1329605 : Blo 275825 1329605 := bbase (se 4 (by rfl) ⟨124650, by rfl⟩ : syracuseStep 1329605 = 249301) (by norm_num)
theorem B313825 : Blo 275825 313825 := bbase (se 2 (by rfl) ⟨117684, by rfl⟩ : syracuseStep 313825 = 235369) (by norm_num)
theorem B707069 : Blo 275825 707069 := bbase (se 3 (by rfl) ⟨132575, by rfl⟩ : syracuseStep 707069 = 265151) (by norm_num)
theorem B313861 : Blo 275825 313861 := bbase (se 4 (by rfl) ⟨29424, by rfl⟩ : syracuseStep 313861 = 58849) (by norm_num)
theorem B313897 : Blo 275825 313897 := bbase (se 2 (by rfl) ⟨117711, by rfl⟩ : syracuseStep 313897 = 235423) (by norm_num)
theorem B313933 : Blo 275825 313933 := bbase (se 3 (by rfl) ⟨58862, by rfl⟩ : syracuseStep 313933 = 117725) (by norm_num)
theorem B313969 : Blo 275825 313969 := bbase (se 2 (by rfl) ⟨117738, by rfl⟩ : syracuseStep 313969 = 235477) (by norm_num)
theorem B314005 : Blo 275825 314005 := bbase (se 6 (by rfl) ⟨7359, by rfl⟩ : syracuseStep 314005 = 14719) (by norm_num)
theorem B510637 : Blo 275825 510637 := bbase (se 3 (by rfl) ⟨95744, by rfl⟩ : syracuseStep 510637 = 191489) (by norm_num)
theorem B936629 : Blo 275825 936629 := bbase (se 5 (by rfl) ⟨43904, by rfl⟩ : syracuseStep 936629 = 87809) (by norm_num)
theorem B314041 : Blo 275825 314041 := bbase (se 2 (by rfl) ⟨117765, by rfl⟩ : syracuseStep 314041 = 235531) (by norm_num)
theorem B314077 : Blo 275825 314077 := bbase (se 3 (by rfl) ⟨58889, by rfl⟩ : syracuseStep 314077 = 117779) (by norm_num)
theorem B314113 : Blo 275825 314113 := bbase (se 2 (by rfl) ⟨117792, by rfl⟩ : syracuseStep 314113 = 235585) (by norm_num)
theorem B314149 : Blo 275825 314149 := bbase (se 4 (by rfl) ⟨29451, by rfl⟩ : syracuseStep 314149 = 58903) (by norm_num)
theorem B969509 : Blo 275825 969509 := bbase (se 4 (by rfl) ⟨90891, by rfl⟩ : syracuseStep 969509 = 181783) (by norm_num)
theorem B314185 : Blo 275825 314185 := bbase (se 2 (by rfl) ⟨117819, by rfl⟩ : syracuseStep 314185 = 235639) (by norm_num)
theorem B707413 : Blo 275825 707413 := bbase (se 9 (by rfl) ⟨2072, by rfl⟩ : syracuseStep 707413 = 4145) (by norm_num)
theorem B445277 : Blo 275825 445277 := bbase (se 3 (by rfl) ⟨83489, by rfl⟩ : syracuseStep 445277 = 166979) (by norm_num)
theorem B314221 : Blo 275825 314221 := bbase (se 3 (by rfl) ⟨58916, by rfl⟩ : syracuseStep 314221 = 117833) (by norm_num)
theorem B314257 : Blo 275825 314257 := bbase (se 2 (by rfl) ⟨117846, by rfl⟩ : syracuseStep 314257 = 235693) (by norm_num)
theorem B576437 : Blo 275825 576437 := bbase (se 5 (by rfl) ⟨27020, by rfl⟩ : syracuseStep 576437 = 54041) (by norm_num)
theorem B314293 : Blo 275825 314293 := bbase (se 5 (by rfl) ⟨14732, by rfl⟩ : syracuseStep 314293 = 29465) (by norm_num)
theorem B707525 : Blo 275825 707525 := bbase (se 4 (by rfl) ⟨66330, by rfl⟩ : syracuseStep 707525 = 132661) (by norm_num)
theorem B314329 : Blo 275825 314329 := bbase (se 2 (by rfl) ⟨117873, by rfl⟩ : syracuseStep 314329 = 235747) (by norm_num)
theorem B314365 : Blo 275825 314365 := bbase (se 3 (by rfl) ⟨58943, by rfl⟩ : syracuseStep 314365 = 117887) (by norm_num)
theorem B314401 : Blo 275825 314401 := bbase (se 2 (by rfl) ⟨117900, by rfl⟩ : syracuseStep 314401 = 235801) (by norm_num)
theorem B1002565 : Blo 275825 1002565 := bbase (se 4 (by rfl) ⟨93990, by rfl⟩ : syracuseStep 1002565 = 187981) (by norm_num)
theorem B314437 : Blo 275825 314437 := bbase (se 4 (by rfl) ⟨29478, by rfl⟩ : syracuseStep 314437 = 58957) (by norm_num)
theorem B937061 : Blo 275825 937061 := bbase (se 4 (by rfl) ⟨87849, by rfl⟩ : syracuseStep 937061 = 175699) (by norm_num)
theorem B314473 : Blo 275825 314473 := bbase (se 2 (by rfl) ⟨117927, by rfl⟩ : syracuseStep 314473 = 235855) (by norm_num)
theorem B707717 : Blo 275825 707717 := bbase (se 4 (by rfl) ⟨66348, by rfl⟩ : syracuseStep 707717 = 132697) (by norm_num)
theorem B314509 : Blo 275825 314509 := bbase (se 3 (by rfl) ⟨58970, by rfl⟩ : syracuseStep 314509 = 117941) (by norm_num)
theorem B314545 : Blo 275825 314545 := bbase (se 2 (by rfl) ⟨117954, by rfl⟩ : syracuseStep 314545 = 235909) (by norm_num)
theorem B314581 : Blo 275825 314581 := bbase (se 7 (by rfl) ⟨3686, by rfl⟩ : syracuseStep 314581 = 7373) (by norm_num)
theorem B314617 : Blo 275825 314617 := bbase (se 2 (by rfl) ⟨117981, by rfl⟩ : syracuseStep 314617 = 235963) (by norm_num)
theorem B314653 : Blo 275825 314653 := bbase (se 3 (by rfl) ⟨58997, by rfl⟩ : syracuseStep 314653 = 117995) (by norm_num)
theorem B445733 : Blo 275825 445733 := bbase (se 4 (by rfl) ⟨41787, by rfl⟩ : syracuseStep 445733 = 83575) (by norm_num)
theorem B314689 : Blo 275825 314689 := bbase (se 2 (by rfl) ⟨118008, by rfl⟩ : syracuseStep 314689 = 236017) (by norm_num)
theorem B314725 : Blo 275825 314725 := bbase (se 4 (by rfl) ⟨29505, by rfl⟩ : syracuseStep 314725 = 59011) (by norm_num)
theorem B314761 : Blo 275825 314761 := bbase (se 2 (by rfl) ⟨118035, by rfl⟩ : syracuseStep 314761 = 236071) (by norm_num)
theorem B314797 : Blo 275825 314797 := bbase (se 3 (by rfl) ⟨59024, by rfl⟩ : syracuseStep 314797 = 118049) (by norm_num)
theorem B282053 : Blo 275825 282053 := bbase (se 4 (by rfl) ⟨26442, by rfl⟩ : syracuseStep 282053 = 52885) (by norm_num)
theorem B708061 : Blo 275825 708061 := bbase (se 3 (by rfl) ⟨132761, by rfl⟩ : syracuseStep 708061 = 265523) (by norm_num)
theorem B937493 : Blo 275825 937493 := bbase (se 6 (by rfl) ⟨21972, by rfl⟩ : syracuseStep 937493 = 43945) (by norm_num)
theorem B1134101 : Blo 275825 1134101 := bbase (se 6 (by rfl) ⟨26580, by rfl⟩ : syracuseStep 1134101 = 53161) (by norm_num)
theorem B708173 : Blo 275825 708173 := bbase (se 3 (by rfl) ⟨132782, by rfl⟩ : syracuseStep 708173 = 265565) (by norm_num)
theorem B282313 : Blo 275825 282313 := bbase (se 2 (by rfl) ⟨105867, by rfl⟩ : syracuseStep 282313 = 211735) (by norm_num)
theorem B5820245 : Blo 275825 5820245 := bbase (se 9 (by rfl) ⟨17051, by rfl⟩ : syracuseStep 5820245 = 34103) (by norm_num)
theorem B937925 : Blo 275825 937925 := bbase (se 4 (by rfl) ⟨87930, by rfl⟩ : syracuseStep 937925 = 175861) (by norm_num)
theorem B577573 : Blo 275825 577573 := bbase (se 4 (by rfl) ⟨54147, by rfl⟩ : syracuseStep 577573 = 108295) (by norm_num)
theorem B413741 : Blo 275825 413741 := bbase (se 3 (by rfl) ⟨77576, by rfl⟩ : syracuseStep 413741 = 155153) (by norm_num)
theorem B413765 : Blo 275825 413765 := bbase (se 4 (by rfl) ⟨38790, by rfl⟩ : syracuseStep 413765 = 77581) (by norm_num)
theorem B413789 : Blo 275825 413789 := bbase (se 3 (by rfl) ⟨77585, by rfl⟩ : syracuseStep 413789 = 155171) (by norm_num)
theorem B413813 : Blo 275825 413813 := bbase (se 5 (by rfl) ⟨19397, by rfl⟩ : syracuseStep 413813 = 38795) (by norm_num)
theorem B413837 : Blo 275825 413837 := bbase (se 3 (by rfl) ⟨77594, by rfl⟩ : syracuseStep 413837 = 155189) (by norm_num)
theorem B413861 : Blo 275825 413861 := bbase (se 4 (by rfl) ⟨38799, by rfl⟩ : syracuseStep 413861 = 77599) (by norm_num)
theorem B413885 : Blo 275825 413885 := bbase (se 3 (by rfl) ⟨77603, by rfl⟩ : syracuseStep 413885 = 155207) (by norm_num)
theorem B413909 : Blo 275825 413909 := bbase (se 7 (by rfl) ⟨4850, by rfl⟩ : syracuseStep 413909 = 9701) (by norm_num)
theorem B413933 : Blo 275825 413933 := bbase (se 3 (by rfl) ⟨77612, by rfl⟩ : syracuseStep 413933 = 155225) (by norm_num)
theorem B413957 : Blo 275825 413957 := bbase (se 4 (by rfl) ⟨38808, by rfl⟩ : syracuseStep 413957 = 77617) (by norm_num)
theorem B446725 : Blo 275825 446725 := bbase (se 4 (by rfl) ⟨41880, by rfl⟩ : syracuseStep 446725 = 83761) (by norm_num)
theorem B413981 : Blo 275825 413981 := bbase (se 3 (by rfl) ⟨77621, by rfl⟩ : syracuseStep 413981 = 155243) (by norm_num)
theorem B414005 : Blo 275825 414005 := bbase (se 5 (by rfl) ⟨19406, by rfl⟩ : syracuseStep 414005 = 38813) (by norm_num)
theorem B414029 : Blo 275825 414029 := bbase (se 3 (by rfl) ⟨77630, by rfl⟩ : syracuseStep 414029 = 155261) (by norm_num)
theorem B414053 : Blo 275825 414053 := bbase (se 4 (by rfl) ⟨38817, by rfl⟩ : syracuseStep 414053 = 77635) (by norm_num)
theorem B938357 : Blo 275825 938357 := bbase (se 5 (by rfl) ⟨43985, by rfl⟩ : syracuseStep 938357 = 87971) (by norm_num)
theorem B414077 : Blo 275825 414077 := bbase (se 3 (by rfl) ⟨77639, by rfl⟩ : syracuseStep 414077 = 155279) (by norm_num)
theorem B414101 : Blo 275825 414101 := bbase (se 6 (by rfl) ⟨9705, by rfl⟩ : syracuseStep 414101 = 19411) (by norm_num)
theorem B709021 : Blo 275825 709021 := bbase (se 3 (by rfl) ⟨132941, by rfl⟩ : syracuseStep 709021 = 265883) (by norm_num)
theorem B414125 : Blo 275825 414125 := bbase (se 3 (by rfl) ⟨77648, by rfl⟩ : syracuseStep 414125 = 155297) (by norm_num)
theorem B414149 : Blo 275825 414149 := bbase (se 4 (by rfl) ⟨38826, by rfl⟩ : syracuseStep 414149 = 77653) (by norm_num)
theorem B414173 : Blo 275825 414173 := bbase (se 3 (by rfl) ⟨77657, by rfl⟩ : syracuseStep 414173 = 155315) (by norm_num)
theorem B414197 : Blo 275825 414197 := bbase (se 5 (by rfl) ⟨19415, by rfl⟩ : syracuseStep 414197 = 38831) (by norm_num)
theorem B414221 : Blo 275825 414221 := bbase (se 3 (by rfl) ⟨77666, by rfl⟩ : syracuseStep 414221 = 155333) (by norm_num)
theorem B414245 : Blo 275825 414245 := bbase (se 4 (by rfl) ⟨38835, by rfl⟩ : syracuseStep 414245 = 77671) (by norm_num)
theorem B709165 : Blo 275825 709165 := bbase (se 3 (by rfl) ⟨132968, by rfl⟩ : syracuseStep 709165 = 265937) (by norm_num)
theorem B414269 : Blo 275825 414269 := bbase (se 3 (by rfl) ⟨77675, by rfl⟩ : syracuseStep 414269 = 155351) (by norm_num)
theorem B414293 : Blo 275825 414293 := bbase (se 8 (by rfl) ⟨2427, by rfl⟩ : syracuseStep 414293 = 4855) (by norm_num)
theorem B414317 : Blo 275825 414317 := bbase (se 3 (by rfl) ⟨77684, by rfl⟩ : syracuseStep 414317 = 155369) (by norm_num)
theorem B414341 : Blo 275825 414341 := bbase (se 4 (by rfl) ⟨38844, by rfl⟩ : syracuseStep 414341 = 77689) (by norm_num)
theorem B414365 : Blo 275825 414365 := bbase (se 3 (by rfl) ⟨77693, by rfl⟩ : syracuseStep 414365 = 155387) (by norm_num)
theorem B414389 : Blo 275825 414389 := bbase (se 5 (by rfl) ⟨19424, by rfl⟩ : syracuseStep 414389 = 38849) (by norm_num)
theorem B414413 : Blo 275825 414413 := bbase (se 3 (by rfl) ⟨77702, by rfl⟩ : syracuseStep 414413 = 155405) (by norm_num)
theorem B414437 : Blo 275825 414437 := bbase (se 4 (by rfl) ⟨38853, by rfl⟩ : syracuseStep 414437 = 77707) (by norm_num)
theorem B414461 : Blo 275825 414461 := bbase (se 3 (by rfl) ⟨77711, by rfl⟩ : syracuseStep 414461 = 155423) (by norm_num)
theorem B414485 : Blo 275825 414485 := bbase (se 6 (by rfl) ⟨9714, by rfl⟩ : syracuseStep 414485 = 19429) (by norm_num)
theorem B938789 : Blo 275825 938789 := bbase (se 4 (by rfl) ⟨88011, by rfl⟩ : syracuseStep 938789 = 176023) (by norm_num)
theorem B414509 : Blo 275825 414509 := bbase (se 3 (by rfl) ⟨77720, by rfl⟩ : syracuseStep 414509 = 155441) (by norm_num)
theorem B1397573 : Blo 275825 1397573 := bbase (se 4 (by rfl) ⟨131022, by rfl⟩ : syracuseStep 1397573 = 262045) (by norm_num)
theorem B414533 : Blo 275825 414533 := bbase (se 4 (by rfl) ⟨38862, by rfl⟩ : syracuseStep 414533 = 77725) (by norm_num)
theorem B414557 : Blo 275825 414557 := bbase (se 3 (by rfl) ⟨77729, by rfl⟩ : syracuseStep 414557 = 155459) (by norm_num)
theorem B414581 : Blo 275825 414581 := bbase (se 5 (by rfl) ⟨19433, by rfl⟩ : syracuseStep 414581 = 38867) (by norm_num)
theorem B414605 : Blo 275825 414605 := bbase (se 3 (by rfl) ⟨77738, by rfl⟩ : syracuseStep 414605 = 155477) (by norm_num)
theorem B447373 : Blo 275825 447373 := bbase (se 3 (by rfl) ⟨83882, by rfl⟩ : syracuseStep 447373 = 167765) (by norm_num)
theorem B414629 : Blo 275825 414629 := bbase (se 4 (by rfl) ⟨38871, by rfl⟩ : syracuseStep 414629 = 77743) (by norm_num)
theorem B349105 : Blo 275825 349105 := bbase (se 2 (by rfl) ⟨130914, by rfl⟩ : syracuseStep 349105 = 261829) (by norm_num)
theorem B414653 : Blo 275825 414653 := bbase (se 3 (by rfl) ⟨77747, by rfl⟩ : syracuseStep 414653 = 155495) (by norm_num)
theorem B414677 : Blo 275825 414677 := bbase (se 7 (by rfl) ⟨4859, by rfl⟩ : syracuseStep 414677 = 9719) (by norm_num)
theorem B414701 : Blo 275825 414701 := bbase (se 3 (by rfl) ⟨77756, by rfl⟩ : syracuseStep 414701 = 155513) (by norm_num)
theorem B414725 : Blo 275825 414725 := bbase (se 4 (by rfl) ⟨38880, by rfl⟩ : syracuseStep 414725 = 77761) (by norm_num)
theorem B349201 : Blo 275825 349201 := bbase (se 2 (by rfl) ⟨130950, by rfl⟩ : syracuseStep 349201 = 261901) (by norm_num)
theorem B414749 : Blo 275825 414749 := bbase (se 3 (by rfl) ⟨77765, by rfl⟩ : syracuseStep 414749 = 155531) (by norm_num)
theorem B414773 : Blo 275825 414773 := bbase (se 5 (by rfl) ⟨19442, by rfl⟩ : syracuseStep 414773 = 38885) (by norm_num)
theorem B1332293 : Blo 275825 1332293 := bbase (se 4 (by rfl) ⟨124902, by rfl⟩ : syracuseStep 1332293 = 249805) (by norm_num)
theorem B316489 : Blo 275825 316489 := bbase (se 2 (by rfl) ⟨118683, by rfl⟩ : syracuseStep 316489 = 237367) (by norm_num)
theorem B414797 : Blo 275825 414797 := bbase (se 3 (by rfl) ⟨77774, by rfl⟩ : syracuseStep 414797 = 155549) (by norm_num)
theorem B414821 : Blo 275825 414821 := bbase (se 4 (by rfl) ⟨38889, by rfl⟩ : syracuseStep 414821 = 77779) (by norm_num)
theorem B414845 : Blo 275825 414845 := bbase (se 3 (by rfl) ⟨77783, by rfl⟩ : syracuseStep 414845 = 155567) (by norm_num)
theorem B414869 : Blo 275825 414869 := bbase (se 6 (by rfl) ⟨9723, by rfl⟩ : syracuseStep 414869 = 19447) (by norm_num)
theorem B414893 : Blo 275825 414893 := bbase (se 3 (by rfl) ⟨77792, by rfl⟩ : syracuseStep 414893 = 155585) (by norm_num)
theorem B349373 : Blo 275825 349373 := bbase (se 3 (by rfl) ⟨65507, by rfl⟩ : syracuseStep 349373 = 131015) (by norm_num)
theorem B414917 : Blo 275825 414917 := bbase (se 4 (by rfl) ⟨38898, by rfl⟩ : syracuseStep 414917 = 77797) (by norm_num)
theorem B939221 : Blo 275825 939221 := bbase (se 7 (by rfl) ⟨11006, by rfl⟩ : syracuseStep 939221 = 22013) (by norm_num)
theorem B414941 : Blo 275825 414941 := bbase (se 3 (by rfl) ⟨77801, by rfl⟩ : syracuseStep 414941 = 155603) (by norm_num)
theorem B349429 : Blo 275825 349429 := bbase (se 5 (by rfl) ⟨16379, by rfl⟩ : syracuseStep 349429 = 32759) (by norm_num)
theorem B414965 : Blo 275825 414965 := bbase (se 5 (by rfl) ⟨19451, by rfl⟩ : syracuseStep 414965 = 38903) (by norm_num)
theorem B414989 : Blo 275825 414989 := bbase (se 3 (by rfl) ⟨77810, by rfl⟩ : syracuseStep 414989 = 155621) (by norm_num)
theorem B415013 : Blo 275825 415013 := bbase (se 4 (by rfl) ⟨38907, by rfl⟩ : syracuseStep 415013 = 77815) (by norm_num)
theorem B415037 : Blo 275825 415037 := bbase (se 3 (by rfl) ⟨77819, by rfl⟩ : syracuseStep 415037 = 155639) (by norm_num)
theorem B382277 : Blo 275825 382277 := bbase (se 4 (by rfl) ⟨35838, by rfl⟩ : syracuseStep 382277 = 71677) (by norm_num)
theorem B349525 : Blo 275825 349525 := bbase (se 20 (by rfl) ⟨0, by rfl⟩ : syracuseStep 349525 = 1) (by norm_num)
theorem B415061 : Blo 275825 415061 := bbase (se 16 (by rfl) ⟨9, by rfl⟩ : syracuseStep 415061 = 19) (by norm_num)
theorem B415085 : Blo 275825 415085 := bbase (se 3 (by rfl) ⟨77828, by rfl⟩ : syracuseStep 415085 = 155657) (by norm_num)
theorem B513389 : Blo 275825 513389 := bbase (se 3 (by rfl) ⟨96260, by rfl⟩ : syracuseStep 513389 = 192521) (by norm_num)
theorem B415109 : Blo 275825 415109 := bbase (se 4 (by rfl) ⟨38916, by rfl⟩ : syracuseStep 415109 = 77833) (by norm_num)
theorem B415133 : Blo 275825 415133 := bbase (se 3 (by rfl) ⟨77837, by rfl⟩ : syracuseStep 415133 = 155675) (by norm_num)
theorem B284077 : Blo 275825 284077 := bbase (se 3 (by rfl) ⟨53264, by rfl⟩ : syracuseStep 284077 = 106529) (by norm_num)
theorem B415157 : Blo 275825 415157 := bbase (se 5 (by rfl) ⟨19460, by rfl⟩ : syracuseStep 415157 = 38921) (by norm_num)
theorem B415181 : Blo 275825 415181 := bbase (se 3 (by rfl) ⟨77846, by rfl⟩ : syracuseStep 415181 = 155693) (by norm_num)
theorem B2840021 : Blo 275825 2840021 := bbase (se 7 (by rfl) ⟨33281, by rfl⟩ : syracuseStep 2840021 = 66563) (by norm_num)
theorem B415205 : Blo 275825 415205 := bbase (se 4 (by rfl) ⟨38925, by rfl⟩ : syracuseStep 415205 = 77851) (by norm_num)
theorem B415229 : Blo 275825 415229 := bbase (se 3 (by rfl) ⟨77855, by rfl⟩ : syracuseStep 415229 = 155711) (by norm_num)
theorem B349697 : Blo 275825 349697 := bbase (se 2 (by rfl) ⟨131136, by rfl⟩ : syracuseStep 349697 = 262273) (by norm_num)
theorem B415253 : Blo 275825 415253 := bbase (se 6 (by rfl) ⟨9732, by rfl⟩ : syracuseStep 415253 = 19465) (by norm_num)
theorem B415277 : Blo 275825 415277 := bbase (se 3 (by rfl) ⟨77864, by rfl⟩ : syracuseStep 415277 = 155729) (by norm_num)
theorem B349753 : Blo 275825 349753 := bbase (se 2 (by rfl) ⟨131157, by rfl⟩ : syracuseStep 349753 = 262315) (by norm_num)
theorem B415301 : Blo 275825 415301 := bbase (se 4 (by rfl) ⟨38934, by rfl⟩ : syracuseStep 415301 = 77869) (by norm_num)
theorem B415325 : Blo 275825 415325 := bbase (se 3 (by rfl) ⟨77873, by rfl⟩ : syracuseStep 415325 = 155747) (by norm_num)
theorem B415349 : Blo 275825 415349 := bbase (se 5 (by rfl) ⟨19469, by rfl⟩ : syracuseStep 415349 = 38939) (by norm_num)
theorem B939653 : Blo 275825 939653 := bbase (se 4 (by rfl) ⟨88092, by rfl⟩ : syracuseStep 939653 = 176185) (by norm_num)
theorem B415373 : Blo 275825 415373 := bbase (se 3 (by rfl) ⟨77882, by rfl⟩ : syracuseStep 415373 = 155765) (by norm_num)
theorem B349849 : Blo 275825 349849 := bbase (se 2 (by rfl) ⟨131193, by rfl⟩ : syracuseStep 349849 = 262387) (by norm_num)
theorem B415397 : Blo 275825 415397 := bbase (se 4 (by rfl) ⟨38943, by rfl⟩ : syracuseStep 415397 = 77887) (by norm_num)
theorem B415421 : Blo 275825 415421 := bbase (se 3 (by rfl) ⟨77891, by rfl⟩ : syracuseStep 415421 = 155783) (by norm_num)
theorem B415445 : Blo 275825 415445 := bbase (se 7 (by rfl) ⟨4868, by rfl⟩ : syracuseStep 415445 = 9737) (by norm_num)
theorem B415469 : Blo 275825 415469 := bbase (se 3 (by rfl) ⟨77900, by rfl⟩ : syracuseStep 415469 = 155801) (by norm_num)
theorem B415493 : Blo 275825 415493 := bbase (se 4 (by rfl) ⟨38952, by rfl⟩ : syracuseStep 415493 = 77905) (by norm_num)
theorem B2119445 : Blo 275825 2119445 := bbase (se 6 (by rfl) ⟨49674, by rfl⟩ : syracuseStep 2119445 = 99349) (by norm_num)
theorem B415517 : Blo 275825 415517 := bbase (se 3 (by rfl) ⟨77909, by rfl⟩ : syracuseStep 415517 = 155819) (by norm_num)
theorem B415541 : Blo 275825 415541 := bbase (se 5 (by rfl) ⟨19478, by rfl⟩ : syracuseStep 415541 = 38957) (by norm_num)
theorem B350021 : Blo 275825 350021 := bbase (se 4 (by rfl) ⟨32814, by rfl⟩ : syracuseStep 350021 = 65629) (by norm_num)
theorem B415565 : Blo 275825 415565 := bbase (se 3 (by rfl) ⟨77918, by rfl⟩ : syracuseStep 415565 = 155837) (by norm_num)
theorem B415589 : Blo 275825 415589 := bbase (se 4 (by rfl) ⟨38961, by rfl⟩ : syracuseStep 415589 = 77923) (by norm_num)
theorem B350077 : Blo 275825 350077 := bbase (se 3 (by rfl) ⟨65639, by rfl⟩ : syracuseStep 350077 = 131279) (by norm_num)
theorem B415613 : Blo 275825 415613 := bbase (se 3 (by rfl) ⟨77927, by rfl⟩ : syracuseStep 415613 = 155855) (by norm_num)
theorem B415637 : Blo 275825 415637 := bbase (se 6 (by rfl) ⟨9741, by rfl⟩ : syracuseStep 415637 = 19483) (by norm_num)
theorem B415661 : Blo 275825 415661 := bbase (se 3 (by rfl) ⟨77936, by rfl⟩ : syracuseStep 415661 = 155873) (by norm_num)
theorem B415685 : Blo 275825 415685 := bbase (se 4 (by rfl) ⟨38970, by rfl⟩ : syracuseStep 415685 = 77941) (by norm_num)
theorem B350173 : Blo 275825 350173 := bbase (se 3 (by rfl) ⟨65657, by rfl⟩ : syracuseStep 350173 = 131315) (by norm_num)
theorem B415709 : Blo 275825 415709 := bbase (se 3 (by rfl) ⟨77945, by rfl⟩ : syracuseStep 415709 = 155891) (by norm_num)
theorem B415733 : Blo 275825 415733 := bbase (se 5 (by rfl) ⟨19487, by rfl⟩ : syracuseStep 415733 = 38975) (by norm_num)
theorem B415757 : Blo 275825 415757 := bbase (se 3 (by rfl) ⟨77954, by rfl⟩ : syracuseStep 415757 = 155909) (by norm_num)
theorem B415781 : Blo 275825 415781 := bbase (se 4 (by rfl) ⟨38979, by rfl⟩ : syracuseStep 415781 = 77959) (by norm_num)
theorem B940085 : Blo 275825 940085 := bbase (se 5 (by rfl) ⟨44066, by rfl⟩ : syracuseStep 940085 = 88133) (by norm_num)
theorem B415805 : Blo 275825 415805 := bbase (se 3 (by rfl) ⟨77963, by rfl⟩ : syracuseStep 415805 = 155927) (by norm_num)
theorem B1398869 : Blo 275825 1398869 := bbase (se 8 (by rfl) ⟨8196, by rfl⟩ : syracuseStep 1398869 = 16393) (by norm_num)
theorem B415829 : Blo 275825 415829 := bbase (se 8 (by rfl) ⟨2436, by rfl⟩ : syracuseStep 415829 = 4873) (by norm_num)
theorem B415853 : Blo 275825 415853 := bbase (se 3 (by rfl) ⟨77972, by rfl⟩ : syracuseStep 415853 = 155945) (by norm_num)
theorem B415877 : Blo 275825 415877 := bbase (se 4 (by rfl) ⟨38988, by rfl⟩ : syracuseStep 415877 = 77977) (by norm_num)
theorem B350345 : Blo 275825 350345 := bbase (se 2 (by rfl) ⟨131379, by rfl⟩ : syracuseStep 350345 = 262759) (by norm_num)
theorem B415901 : Blo 275825 415901 := bbase (se 3 (by rfl) ⟨77981, by rfl⟩ : syracuseStep 415901 = 155963) (by norm_num)
theorem B415925 : Blo 275825 415925 := bbase (se 5 (by rfl) ⟨19496, by rfl⟩ : syracuseStep 415925 = 38993) (by norm_num)
theorem B350401 : Blo 275825 350401 := bbase (se 2 (by rfl) ⟨131400, by rfl⟩ : syracuseStep 350401 = 262801) (by norm_num)
theorem B415949 : Blo 275825 415949 := bbase (se 3 (by rfl) ⟨77990, by rfl⟩ : syracuseStep 415949 = 155981) (by norm_num)
theorem B415973 : Blo 275825 415973 := bbase (se 4 (by rfl) ⟨38997, by rfl⟩ : syracuseStep 415973 = 77995) (by norm_num)
theorem B415997 : Blo 275825 415997 := bbase (se 3 (by rfl) ⟨77999, by rfl⟩ : syracuseStep 415997 = 155999) (by norm_num)
theorem B612613 : Blo 275825 612613 := bbase (se 4 (by rfl) ⟨57432, by rfl⟩ : syracuseStep 612613 = 114865) (by norm_num)
theorem B416021 : Blo 275825 416021 := bbase (se 6 (by rfl) ⟨9750, by rfl⟩ : syracuseStep 416021 = 19501) (by norm_num)
theorem B317725 : Blo 275825 317725 := bbase (se 3 (by rfl) ⟨59573, by rfl⟩ : syracuseStep 317725 = 119147) (by norm_num)
theorem B350497 : Blo 275825 350497 := bbase (se 2 (by rfl) ⟨131436, by rfl⟩ : syracuseStep 350497 = 262873) (by norm_num)
theorem B416045 : Blo 275825 416045 := bbase (se 3 (by rfl) ⟨78008, by rfl⟩ : syracuseStep 416045 = 156017) (by norm_num)
theorem B416069 : Blo 275825 416069 := bbase (se 4 (by rfl) ⟨39006, by rfl⟩ : syracuseStep 416069 = 78013) (by norm_num)
theorem B416093 : Blo 275825 416093 := bbase (se 3 (by rfl) ⟨78017, by rfl⟩ : syracuseStep 416093 = 156035) (by norm_num)
theorem B416117 : Blo 275825 416117 := bbase (se 5 (by rfl) ⟨19505, by rfl⟩ : syracuseStep 416117 = 39011) (by norm_num)
theorem B416141 : Blo 275825 416141 := bbase (se 3 (by rfl) ⟨78026, by rfl⟩ : syracuseStep 416141 = 156053) (by norm_num)
theorem B416165 : Blo 275825 416165 := bbase (se 4 (by rfl) ⟨39015, by rfl⟩ : syracuseStep 416165 = 78031) (by norm_num)
theorem B416189 : Blo 275825 416189 := bbase (se 3 (by rfl) ⟨78035, by rfl⟩ : syracuseStep 416189 = 156071) (by norm_num)
theorem B350669 : Blo 275825 350669 := bbase (se 3 (by rfl) ⟨65750, by rfl⟩ : syracuseStep 350669 = 131501) (by norm_num)
theorem B416213 : Blo 275825 416213 := bbase (se 7 (by rfl) ⟨4877, by rfl⟩ : syracuseStep 416213 = 9755) (by norm_num)
theorem B940517 : Blo 275825 940517 := bbase (se 4 (by rfl) ⟨88173, by rfl⟩ : syracuseStep 940517 = 176347) (by norm_num)
theorem B416237 : Blo 275825 416237 := bbase (se 3 (by rfl) ⟨78044, by rfl⟩ : syracuseStep 416237 = 156089) (by norm_num)
theorem B350725 : Blo 275825 350725 := bbase (se 4 (by rfl) ⟨32880, by rfl⟩ : syracuseStep 350725 = 65761) (by norm_num)
theorem B416261 : Blo 275825 416261 := bbase (se 4 (by rfl) ⟨39024, by rfl⟩ : syracuseStep 416261 = 78049) (by norm_num)
theorem B711197 : Blo 275825 711197 := bbase (se 3 (by rfl) ⟨133349, by rfl⟩ : syracuseStep 711197 = 266699) (by norm_num)
theorem B416285 : Blo 275825 416285 := bbase (se 3 (by rfl) ⟨78053, by rfl⟩ : syracuseStep 416285 = 156107) (by norm_num)
theorem B416309 : Blo 275825 416309 := bbase (se 5 (by rfl) ⟨19514, by rfl⟩ : syracuseStep 416309 = 39029) (by norm_num)
theorem B416333 : Blo 275825 416333 := bbase (se 3 (by rfl) ⟨78062, by rfl⟩ : syracuseStep 416333 = 156125) (by norm_num)
theorem B6085205 : Blo 275825 6085205 := bbase (se 8 (by rfl) ⟨35655, by rfl⟩ : syracuseStep 6085205 = 71311) (by norm_num)
theorem B350821 : Blo 275825 350821 := bbase (se 4 (by rfl) ⟨32889, by rfl⟩ : syracuseStep 350821 = 65779) (by norm_num)
theorem B416357 : Blo 275825 416357 := bbase (se 4 (by rfl) ⟨39033, by rfl⟩ : syracuseStep 416357 = 78067) (by norm_num)
theorem B416381 : Blo 275825 416381 := bbase (se 3 (by rfl) ⟨78071, by rfl⟩ : syracuseStep 416381 = 156143) (by norm_num)
theorem B416405 : Blo 275825 416405 := bbase (se 6 (by rfl) ⟨9759, by rfl⟩ : syracuseStep 416405 = 19519) (by norm_num)
theorem B416429 : Blo 275825 416429 := bbase (se 3 (by rfl) ⟨78080, by rfl⟩ : syracuseStep 416429 = 156161) (by norm_num)
theorem B416453 : Blo 275825 416453 := bbase (se 4 (by rfl) ⟨39042, by rfl⟩ : syracuseStep 416453 = 78085) (by norm_num)
theorem B416477 : Blo 275825 416477 := bbase (se 3 (by rfl) ⟨78089, by rfl⟩ : syracuseStep 416477 = 156179) (by norm_num)
theorem B416501 : Blo 275825 416501 := bbase (se 5 (by rfl) ⟨19523, by rfl⟩ : syracuseStep 416501 = 39047) (by norm_num)
theorem B416525 : Blo 275825 416525 := bbase (se 3 (by rfl) ⟨78098, by rfl⟩ : syracuseStep 416525 = 156197) (by norm_num)
theorem B350993 : Blo 275825 350993 := bbase (se 2 (by rfl) ⟨131622, by rfl⟩ : syracuseStep 350993 = 263245) (by norm_num)
theorem B416549 : Blo 275825 416549 := bbase (se 4 (by rfl) ⟨39051, by rfl⟩ : syracuseStep 416549 = 78103) (by norm_num)
theorem B416573 : Blo 275825 416573 := bbase (se 3 (by rfl) ⟨78107, by rfl⟩ : syracuseStep 416573 = 156215) (by norm_num)
theorem B908101 : Blo 275825 908101 := bbase (se 4 (by rfl) ⟨85134, by rfl⟩ : syracuseStep 908101 = 170269) (by norm_num)
theorem B351049 : Blo 275825 351049 := bbase (se 2 (by rfl) ⟨131643, by rfl⟩ : syracuseStep 351049 = 263287) (by norm_num)
theorem B416597 : Blo 275825 416597 := bbase (se 9 (by rfl) ⟨1220, by rfl⟩ : syracuseStep 416597 = 2441) (by norm_num)
theorem B416621 : Blo 275825 416621 := bbase (se 3 (by rfl) ⟨78116, by rfl⟩ : syracuseStep 416621 = 156233) (by norm_num)
theorem B416645 : Blo 275825 416645 := bbase (se 4 (by rfl) ⟨39060, by rfl⟩ : syracuseStep 416645 = 78121) (by norm_num)
theorem B940949 : Blo 275825 940949 := bbase (se 6 (by rfl) ⟨22053, by rfl⟩ : syracuseStep 940949 = 44107) (by norm_num)
theorem B416669 : Blo 275825 416669 := bbase (se 3 (by rfl) ⟨78125, by rfl⟩ : syracuseStep 416669 = 156251) (by norm_num)
theorem B351145 : Blo 275825 351145 := bbase (se 2 (by rfl) ⟨131679, by rfl⟩ : syracuseStep 351145 = 263359) (by norm_num)
theorem B416693 : Blo 275825 416693 := bbase (se 5 (by rfl) ⟨19532, by rfl⟩ : syracuseStep 416693 = 39065) (by norm_num)
theorem B416717 : Blo 275825 416717 := bbase (se 3 (by rfl) ⟨78134, by rfl⟩ : syracuseStep 416717 = 156269) (by norm_num)
theorem B416741 : Blo 275825 416741 := bbase (se 4 (by rfl) ⟨39069, by rfl⟩ : syracuseStep 416741 = 78139) (by norm_num)
theorem B416765 : Blo 275825 416765 := bbase (se 3 (by rfl) ⟨78143, by rfl⟩ : syracuseStep 416765 = 156287) (by norm_num)
theorem B416789 : Blo 275825 416789 := bbase (se 6 (by rfl) ⟨9768, by rfl⟩ : syracuseStep 416789 = 19537) (by norm_num)
theorem B416813 : Blo 275825 416813 := bbase (se 3 (by rfl) ⟨78152, by rfl⟩ : syracuseStep 416813 = 156305) (by norm_num)
theorem B416837 : Blo 275825 416837 := bbase (se 4 (by rfl) ⟨39078, by rfl⟩ : syracuseStep 416837 = 78157) (by norm_num)
theorem B351317 : Blo 275825 351317 := bbase (se 8 (by rfl) ⟨2058, by rfl⟩ : syracuseStep 351317 = 4117) (by norm_num)
theorem B416861 : Blo 275825 416861 := bbase (se 3 (by rfl) ⟨78161, by rfl⟩ : syracuseStep 416861 = 156323) (by norm_num)
theorem B416885 : Blo 275825 416885 := bbase (se 5 (by rfl) ⟨19541, by rfl⟩ : syracuseStep 416885 = 39083) (by norm_num)
theorem B351373 : Blo 275825 351373 := bbase (se 3 (by rfl) ⟨65882, by rfl⟩ : syracuseStep 351373 = 131765) (by norm_num)
theorem B416909 : Blo 275825 416909 := bbase (se 3 (by rfl) ⟨78170, by rfl⟩ : syracuseStep 416909 = 156341) (by norm_num)
theorem B416933 : Blo 275825 416933 := bbase (se 4 (by rfl) ⟨39087, by rfl⟩ : syracuseStep 416933 = 78175) (by norm_num)
theorem B416957 : Blo 275825 416957 := bbase (se 3 (by rfl) ⟨78179, by rfl⟩ : syracuseStep 416957 = 156359) (by norm_num)
theorem B416981 : Blo 275825 416981 := bbase (se 7 (by rfl) ⟨4886, by rfl⟩ : syracuseStep 416981 = 9773) (by norm_num)
theorem B351469 : Blo 275825 351469 := bbase (se 3 (by rfl) ⟨65900, by rfl⟩ : syracuseStep 351469 = 131801) (by norm_num)
theorem B417005 : Blo 275825 417005 := bbase (se 3 (by rfl) ⟨78188, by rfl⟩ : syracuseStep 417005 = 156377) (by norm_num)
theorem B417029 : Blo 275825 417029 := bbase (se 4 (by rfl) ⟨39096, by rfl⟩ : syracuseStep 417029 = 78193) (by norm_num)
theorem B417053 : Blo 275825 417053 := bbase (se 3 (by rfl) ⟨78197, by rfl⟩ : syracuseStep 417053 = 156395) (by norm_num)
theorem B417077 : Blo 275825 417077 := bbase (se 5 (by rfl) ⟨19550, by rfl⟩ : syracuseStep 417077 = 39101) (by norm_num)
theorem B941381 : Blo 275825 941381 := bbase (se 4 (by rfl) ⟨88254, by rfl⟩ : syracuseStep 941381 = 176509) (by norm_num)
theorem B417101 : Blo 275825 417101 := bbase (se 3 (by rfl) ⟨78206, by rfl⟩ : syracuseStep 417101 = 156413) (by norm_num)
theorem B15621461 : Blo 275825 15621461 := bbase (se 11 (by rfl) ⟨11441, by rfl⟩ : syracuseStep 15621461 = 22883) (by norm_num)
theorem B1400165 : Blo 275825 1400165 := bbase (se 4 (by rfl) ⟨131265, by rfl⟩ : syracuseStep 1400165 = 262531) (by norm_num)
theorem B417125 : Blo 275825 417125 := bbase (se 4 (by rfl) ⟨39105, by rfl⟩ : syracuseStep 417125 = 78211) (by norm_num)
theorem B417149 : Blo 275825 417149 := bbase (se 3 (by rfl) ⟨78215, by rfl⟩ : syracuseStep 417149 = 156431) (by norm_num)
theorem B417173 : Blo 275825 417173 := bbase (se 6 (by rfl) ⟨9777, by rfl⟩ : syracuseStep 417173 = 19555) (by norm_num)
theorem B351641 : Blo 275825 351641 := bbase (se 2 (by rfl) ⟨131865, by rfl⟩ : syracuseStep 351641 = 263731) (by norm_num)
theorem B417197 : Blo 275825 417197 := bbase (se 3 (by rfl) ⟨78224, by rfl⟩ : syracuseStep 417197 = 156449) (by norm_num)
theorem B417221 : Blo 275825 417221 := bbase (se 4 (by rfl) ⟨39114, by rfl⟩ : syracuseStep 417221 = 78229) (by norm_num)
theorem B351697 : Blo 275825 351697 := bbase (se 2 (by rfl) ⟨131886, by rfl⟩ : syracuseStep 351697 = 263773) (by norm_num)
theorem B417245 : Blo 275825 417245 := bbase (se 3 (by rfl) ⟨78233, by rfl⟩ : syracuseStep 417245 = 156467) (by norm_num)
theorem B417269 : Blo 275825 417269 := bbase (se 5 (by rfl) ⟨19559, by rfl⟩ : syracuseStep 417269 = 39119) (by norm_num)
theorem B417293 : Blo 275825 417293 := bbase (se 3 (by rfl) ⟨78242, by rfl⟩ : syracuseStep 417293 = 156485) (by norm_num)
theorem B417317 : Blo 275825 417317 := bbase (se 4 (by rfl) ⟨39123, by rfl⟩ : syracuseStep 417317 = 78247) (by norm_num)
theorem B351793 : Blo 275825 351793 := bbase (se 2 (by rfl) ⟨131922, by rfl⟩ : syracuseStep 351793 = 263845) (by norm_num)
theorem B417341 : Blo 275825 417341 := bbase (se 3 (by rfl) ⟨78251, by rfl⟩ : syracuseStep 417341 = 156503) (by norm_num)
theorem B417365 : Blo 275825 417365 := bbase (se 8 (by rfl) ⟨2445, by rfl⟩ : syracuseStep 417365 = 4891) (by norm_num)
theorem B417389 : Blo 275825 417389 := bbase (se 3 (by rfl) ⟨78260, by rfl⟩ : syracuseStep 417389 = 156521) (by norm_num)
theorem B417413 : Blo 275825 417413 := bbase (se 4 (by rfl) ⟨39132, by rfl⟩ : syracuseStep 417413 = 78265) (by norm_num)
theorem B417437 : Blo 275825 417437 := bbase (se 3 (by rfl) ⟨78269, by rfl⟩ : syracuseStep 417437 = 156539) (by norm_num)
theorem B417461 : Blo 275825 417461 := bbase (se 5 (by rfl) ⟨19568, by rfl⟩ : syracuseStep 417461 = 39137) (by norm_num)
theorem B417485 : Blo 275825 417485 := bbase (se 3 (by rfl) ⟨78278, by rfl⟩ : syracuseStep 417485 = 156557) (by norm_num)
theorem B351965 : Blo 275825 351965 := bbase (se 3 (by rfl) ⟨65993, by rfl⟩ : syracuseStep 351965 = 131987) (by norm_num)
theorem B417509 : Blo 275825 417509 := bbase (se 4 (by rfl) ⟨39141, by rfl⟩ : syracuseStep 417509 = 78283) (by norm_num)
theorem B941813 : Blo 275825 941813 := bbase (se 5 (by rfl) ⟨44147, by rfl⟩ : syracuseStep 941813 = 88295) (by norm_num)
theorem B417533 : Blo 275825 417533 := bbase (se 3 (by rfl) ⟨78287, by rfl⟩ : syracuseStep 417533 = 156575) (by norm_num)
theorem B352021 : Blo 275825 352021 := bbase (se 6 (by rfl) ⟨8250, by rfl⟩ : syracuseStep 352021 = 16501) (by norm_num)
theorem B417557 : Blo 275825 417557 := bbase (se 6 (by rfl) ⟨9786, by rfl⟩ : syracuseStep 417557 = 19573) (by norm_num)
theorem B417581 : Blo 275825 417581 := bbase (se 3 (by rfl) ⟨78296, by rfl⟩ : syracuseStep 417581 = 156593) (by norm_num)
theorem B417605 : Blo 275825 417605 := bbase (se 4 (by rfl) ⟨39150, by rfl⟩ : syracuseStep 417605 = 78301) (by norm_num)
theorem B417629 : Blo 275825 417629 := bbase (se 3 (by rfl) ⟨78305, by rfl⟩ : syracuseStep 417629 = 156611) (by norm_num)
theorem B352117 : Blo 275825 352117 := bbase (se 5 (by rfl) ⟨16505, by rfl⟩ : syracuseStep 352117 = 33011) (by norm_num)
theorem B417653 : Blo 275825 417653 := bbase (se 5 (by rfl) ⟨19577, by rfl⟩ : syracuseStep 417653 = 39155) (by norm_num)
theorem B417677 : Blo 275825 417677 := bbase (se 3 (by rfl) ⟨78314, by rfl⟩ : syracuseStep 417677 = 156629) (by norm_num)
theorem B417701 : Blo 275825 417701 := bbase (se 4 (by rfl) ⟨39159, by rfl⟩ : syracuseStep 417701 = 78319) (by norm_num)
theorem B417725 : Blo 275825 417725 := bbase (se 3 (by rfl) ⟨78323, by rfl⟩ : syracuseStep 417725 = 156647) (by norm_num)
theorem B417749 : Blo 275825 417749 := bbase (se 7 (by rfl) ⟨4895, by rfl⟩ : syracuseStep 417749 = 9791) (by norm_num)
theorem B417773 : Blo 275825 417773 := bbase (se 3 (by rfl) ⟨78332, by rfl⟩ : syracuseStep 417773 = 156665) (by norm_num)
theorem B417797 : Blo 275825 417797 := bbase (se 4 (by rfl) ⟨39168, by rfl⟩ : syracuseStep 417797 = 78337) (by norm_num)
theorem B417821 : Blo 275825 417821 := bbase (se 3 (by rfl) ⟨78341, by rfl⟩ : syracuseStep 417821 = 156683) (by norm_num)
theorem B352289 : Blo 275825 352289 := bbase (se 2 (by rfl) ⟨132108, by rfl⟩ : syracuseStep 352289 = 264217) (by norm_num)
theorem B417845 : Blo 275825 417845 := bbase (se 5 (by rfl) ⟨19586, by rfl⟩ : syracuseStep 417845 = 39173) (by norm_num)
theorem B417869 : Blo 275825 417869 := bbase (se 3 (by rfl) ⟨78350, by rfl⟩ : syracuseStep 417869 = 156701) (by norm_num)
theorem B352345 : Blo 275825 352345 := bbase (se 2 (by rfl) ⟨132129, by rfl⟩ : syracuseStep 352345 = 264259) (by norm_num)
theorem B417893 : Blo 275825 417893 := bbase (se 4 (by rfl) ⟨39177, by rfl⟩ : syracuseStep 417893 = 78355) (by norm_num)
theorem B417917 : Blo 275825 417917 := bbase (se 3 (by rfl) ⟨78359, by rfl⟩ : syracuseStep 417917 = 156719) (by norm_num)
theorem B1597589 : Blo 275825 1597589 := bbase (se 6 (by rfl) ⟨37443, by rfl⟩ : syracuseStep 1597589 = 74887) (by norm_num)
theorem B417941 : Blo 275825 417941 := bbase (se 6 (by rfl) ⟨9795, by rfl⟩ : syracuseStep 417941 = 19591) (by norm_num)
theorem B942245 : Blo 275825 942245 := bbase (se 4 (by rfl) ⟨88335, by rfl⟩ : syracuseStep 942245 = 176671) (by norm_num)
theorem B417965 : Blo 275825 417965 := bbase (se 3 (by rfl) ⟨78368, by rfl⟩ : syracuseStep 417965 = 156737) (by norm_num)
theorem B352441 : Blo 275825 352441 := bbase (se 2 (by rfl) ⟨132165, by rfl⟩ : syracuseStep 352441 = 264331) (by norm_num)
theorem B417989 : Blo 275825 417989 := bbase (se 4 (by rfl) ⟨39186, by rfl⟩ : syracuseStep 417989 = 78373) (by norm_num)
theorem B418013 : Blo 275825 418013 := bbase (se 3 (by rfl) ⟨78377, by rfl⟩ : syracuseStep 418013 = 156755) (by norm_num)
theorem B418037 : Blo 275825 418037 := bbase (se 5 (by rfl) ⟨19595, by rfl⟩ : syracuseStep 418037 = 39191) (by norm_num)
theorem B418061 : Blo 275825 418061 := bbase (se 3 (by rfl) ⟨78386, by rfl⟩ : syracuseStep 418061 = 156773) (by norm_num)
theorem B418085 : Blo 275825 418085 := bbase (se 4 (by rfl) ⟨39195, by rfl⟩ : syracuseStep 418085 = 78391) (by norm_num)
theorem B418109 : Blo 275825 418109 := bbase (se 3 (by rfl) ⟨78395, by rfl⟩ : syracuseStep 418109 = 156791) (by norm_num)
theorem B418133 : Blo 275825 418133 := bbase (se 10 (by rfl) ⟨612, by rfl⟩ : syracuseStep 418133 = 1225) (by norm_num)
theorem B352613 : Blo 275825 352613 := bbase (se 4 (by rfl) ⟨33057, by rfl⟩ : syracuseStep 352613 = 66115) (by norm_num)
theorem B680293 : Blo 275825 680293 := bbase (se 4 (by rfl) ⟨63777, by rfl⟩ : syracuseStep 680293 = 127555) (by norm_num)
theorem B418157 : Blo 275825 418157 := bbase (se 3 (by rfl) ⟨78404, by rfl⟩ : syracuseStep 418157 = 156809) (by norm_num)
theorem B418181 : Blo 275825 418181 := bbase (se 4 (by rfl) ⟨39204, by rfl⟩ : syracuseStep 418181 = 78409) (by norm_num)
theorem B352669 : Blo 275825 352669 := bbase (se 3 (by rfl) ⟨66125, by rfl⟩ : syracuseStep 352669 = 132251) (by norm_num)
theorem B418205 : Blo 275825 418205 := bbase (se 3 (by rfl) ⟨78413, by rfl⟩ : syracuseStep 418205 = 156827) (by norm_num)
theorem B418229 : Blo 275825 418229 := bbase (se 5 (by rfl) ⟨19604, by rfl⟩ : syracuseStep 418229 = 39209) (by norm_num)
theorem B418253 : Blo 275825 418253 := bbase (se 3 (by rfl) ⟨78422, by rfl⟩ : syracuseStep 418253 = 156845) (by norm_num)
theorem B418277 : Blo 275825 418277 := bbase (se 4 (by rfl) ⟨39213, by rfl⟩ : syracuseStep 418277 = 78427) (by norm_num)
theorem B1008101 : Blo 275825 1008101 := bbase (se 4 (by rfl) ⟨94509, by rfl⟩ : syracuseStep 1008101 = 189019) (by norm_num)
theorem B352765 : Blo 275825 352765 := bbase (se 3 (by rfl) ⟨66143, by rfl⟩ : syracuseStep 352765 = 132287) (by norm_num)
theorem B418301 : Blo 275825 418301 := bbase (se 3 (by rfl) ⟨78431, by rfl⟩ : syracuseStep 418301 = 156863) (by norm_num)
theorem B2679317 : Blo 275825 2679317 := bbase (se 6 (by rfl) ⟨62796, by rfl⟩ : syracuseStep 2679317 = 125593) (by norm_num)
theorem B418325 : Blo 275825 418325 := bbase (se 6 (by rfl) ⟨9804, by rfl⟩ : syracuseStep 418325 = 19609) (by norm_num)
theorem B418349 : Blo 275825 418349 := bbase (se 3 (by rfl) ⟨78440, by rfl⟩ : syracuseStep 418349 = 156881) (by norm_num)
theorem B418373 : Blo 275825 418373 := bbase (se 4 (by rfl) ⟨39222, by rfl⟩ : syracuseStep 418373 = 78445) (by norm_num)
theorem B942677 : Blo 275825 942677 := bbase (se 8 (by rfl) ⟨5523, by rfl⟩ : syracuseStep 942677 = 11047) (by norm_num)
theorem B418397 : Blo 275825 418397 := bbase (se 3 (by rfl) ⟨78449, by rfl⟩ : syracuseStep 418397 = 156899) (by norm_num)
theorem B1401461 : Blo 275825 1401461 := bbase (se 5 (by rfl) ⟨65693, by rfl⟩ : syracuseStep 1401461 = 131387) (by norm_num)
theorem B418421 : Blo 275825 418421 := bbase (se 5 (by rfl) ⟨19613, by rfl⟩ : syracuseStep 418421 = 39227) (by norm_num)
theorem B418445 : Blo 275825 418445 := bbase (se 3 (by rfl) ⟨78458, by rfl⟩ : syracuseStep 418445 = 156917) (by norm_num)
theorem B418469 : Blo 275825 418469 := bbase (se 4 (by rfl) ⟨39231, by rfl⟩ : syracuseStep 418469 = 78463) (by norm_num)
theorem B352937 : Blo 275825 352937 := bbase (se 2 (by rfl) ⟨132351, by rfl⟩ : syracuseStep 352937 = 264703) (by norm_num)
theorem B418493 : Blo 275825 418493 := bbase (se 3 (by rfl) ⟨78467, by rfl⟩ : syracuseStep 418493 = 156935) (by norm_num)
theorem B418517 : Blo 275825 418517 := bbase (se 7 (by rfl) ⟨4904, by rfl⟩ : syracuseStep 418517 = 9809) (by norm_num)
theorem B352993 : Blo 275825 352993 := bbase (se 2 (by rfl) ⟨132372, by rfl⟩ : syracuseStep 352993 = 264745) (by norm_num)
theorem B418541 : Blo 275825 418541 := bbase (se 3 (by rfl) ⟨78476, by rfl⟩ : syracuseStep 418541 = 156953) (by norm_num)
theorem B418565 : Blo 275825 418565 := bbase (se 4 (by rfl) ⟨39240, by rfl⟩ : syracuseStep 418565 = 78481) (by norm_num)
theorem B418589 : Blo 275825 418589 := bbase (se 3 (by rfl) ⟨78485, by rfl⟩ : syracuseStep 418589 = 156971) (by norm_num)
theorem B418613 : Blo 275825 418613 := bbase (se 5 (by rfl) ⟨19622, by rfl⟩ : syracuseStep 418613 = 39245) (by norm_num)
theorem B353089 : Blo 275825 353089 := bbase (se 2 (by rfl) ⟨132408, by rfl⟩ : syracuseStep 353089 = 264817) (by norm_num)
theorem B418637 : Blo 275825 418637 := bbase (se 3 (by rfl) ⟨78494, by rfl⟩ : syracuseStep 418637 = 156989) (by norm_num)
theorem B418661 : Blo 275825 418661 := bbase (se 4 (by rfl) ⟨39249, by rfl⟩ : syracuseStep 418661 = 78499) (by norm_num)
theorem B418685 : Blo 275825 418685 := bbase (se 3 (by rfl) ⟨78503, by rfl⟩ : syracuseStep 418685 = 157007) (by norm_num)
theorem B418709 : Blo 275825 418709 := bbase (se 6 (by rfl) ⟨9813, by rfl⟩ : syracuseStep 418709 = 19627) (by norm_num)
theorem B418733 : Blo 275825 418733 := bbase (se 3 (by rfl) ⟨78512, by rfl⟩ : syracuseStep 418733 = 157025) (by norm_num)
theorem B418757 : Blo 275825 418757 := bbase (se 4 (by rfl) ⟨39258, by rfl⟩ : syracuseStep 418757 = 78517) (by norm_num)
theorem B3793877 : Blo 275825 3793877 := bbase (se 7 (by rfl) ⟨44459, by rfl⟩ : syracuseStep 3793877 = 88919) (by norm_num)
theorem B418781 : Blo 275825 418781 := bbase (se 3 (by rfl) ⟨78521, by rfl⟩ : syracuseStep 418781 = 157043) (by norm_num)
theorem B353261 : Blo 275825 353261 := bbase (se 3 (by rfl) ⟨66236, by rfl⟩ : syracuseStep 353261 = 132473) (by norm_num)
theorem B418805 : Blo 275825 418805 := bbase (se 5 (by rfl) ⟨19631, by rfl⟩ : syracuseStep 418805 = 39263) (by norm_num)
theorem B943109 : Blo 275825 943109 := bbase (se 4 (by rfl) ⟨88416, by rfl⟩ : syracuseStep 943109 = 176833) (by norm_num)
theorem B418829 : Blo 275825 418829 := bbase (se 3 (by rfl) ⟨78530, by rfl⟩ : syracuseStep 418829 = 157061) (by norm_num)
theorem B353317 : Blo 275825 353317 := bbase (se 4 (by rfl) ⟨33123, by rfl⟩ : syracuseStep 353317 = 66247) (by norm_num)
theorem B418853 : Blo 275825 418853 := bbase (se 4 (by rfl) ⟨39267, by rfl⟩ : syracuseStep 418853 = 78535) (by norm_num)
theorem B418877 : Blo 275825 418877 := bbase (se 3 (by rfl) ⟨78539, by rfl⟩ : syracuseStep 418877 = 157079) (by norm_num)
theorem B418901 : Blo 275825 418901 := bbase (se 8 (by rfl) ⟨2454, by rfl⟩ : syracuseStep 418901 = 4909) (by norm_num)
theorem B418925 : Blo 275825 418925 := bbase (se 3 (by rfl) ⟨78548, by rfl⟩ : syracuseStep 418925 = 157097) (by norm_num)
theorem B353413 : Blo 275825 353413 := bbase (se 4 (by rfl) ⟨33132, by rfl⟩ : syracuseStep 353413 = 66265) (by norm_num)
theorem B418949 : Blo 275825 418949 := bbase (se 4 (by rfl) ⟨39276, by rfl⟩ : syracuseStep 418949 = 78553) (by norm_num)
theorem B418973 : Blo 275825 418973 := bbase (se 3 (by rfl) ⟨78557, by rfl⟩ : syracuseStep 418973 = 157115) (by norm_num)
theorem B418997 : Blo 275825 418997 := bbase (se 5 (by rfl) ⟨19640, by rfl⟩ : syracuseStep 418997 = 39281) (by norm_num)
theorem B419021 : Blo 275825 419021 := bbase (se 3 (by rfl) ⟨78566, by rfl⟩ : syracuseStep 419021 = 157133) (by norm_num)
theorem B419045 : Blo 275825 419045 := bbase (se 4 (by rfl) ⟨39285, by rfl⟩ : syracuseStep 419045 = 78571) (by norm_num)
theorem B419069 : Blo 275825 419069 := bbase (se 3 (by rfl) ⟨78575, by rfl⟩ : syracuseStep 419069 = 157151) (by norm_num)
theorem B419093 : Blo 275825 419093 := bbase (se 6 (by rfl) ⟨9822, by rfl⟩ : syracuseStep 419093 = 19645) (by norm_num)
theorem B419117 : Blo 275825 419117 := bbase (se 3 (by rfl) ⟨78584, by rfl⟩ : syracuseStep 419117 = 157169) (by norm_num)
theorem B353585 : Blo 275825 353585 := bbase (se 2 (by rfl) ⟨132594, by rfl⟩ : syracuseStep 353585 = 265189) (by norm_num)
theorem B419141 : Blo 275825 419141 := bbase (se 4 (by rfl) ⟨39294, by rfl⟩ : syracuseStep 419141 = 78589) (by norm_num)
theorem B419165 : Blo 275825 419165 := bbase (se 3 (by rfl) ⟨78593, by rfl⟩ : syracuseStep 419165 = 157187) (by norm_num)
theorem B353641 : Blo 275825 353641 := bbase (se 2 (by rfl) ⟨132615, by rfl⟩ : syracuseStep 353641 = 265231) (by norm_num)
theorem B419189 : Blo 275825 419189 := bbase (se 5 (by rfl) ⟨19649, by rfl⟩ : syracuseStep 419189 = 39299) (by norm_num)
theorem B419213 : Blo 275825 419213 := bbase (se 3 (by rfl) ⟨78602, by rfl⟩ : syracuseStep 419213 = 157205) (by norm_num)
theorem B419237 : Blo 275825 419237 := bbase (se 4 (by rfl) ⟨39303, by rfl⟩ : syracuseStep 419237 = 78607) (by norm_num)
theorem B943541 : Blo 275825 943541 := bbase (se 5 (by rfl) ⟨44228, by rfl⟩ : syracuseStep 943541 = 88457) (by norm_num)
theorem B419261 : Blo 275825 419261 := bbase (se 3 (by rfl) ⟨78611, by rfl⟩ : syracuseStep 419261 = 157223) (by norm_num)
theorem B353737 : Blo 275825 353737 := bbase (se 2 (by rfl) ⟨132651, by rfl⟩ : syracuseStep 353737 = 265303) (by norm_num)
theorem B419285 : Blo 275825 419285 := bbase (se 7 (by rfl) ⟨4913, by rfl⟩ : syracuseStep 419285 = 9827) (by norm_num)
theorem B419309 : Blo 275825 419309 := bbase (se 3 (by rfl) ⟨78620, by rfl⟩ : syracuseStep 419309 = 157241) (by norm_num)
theorem B419333 : Blo 275825 419333 := bbase (se 4 (by rfl) ⟨39312, by rfl⟩ : syracuseStep 419333 = 78625) (by norm_num)
theorem B419357 : Blo 275825 419357 := bbase (se 3 (by rfl) ⟨78629, by rfl⟩ : syracuseStep 419357 = 157259) (by norm_num)
theorem B419381 : Blo 275825 419381 := bbase (se 5 (by rfl) ⟨19658, by rfl⟩ : syracuseStep 419381 = 39317) (by norm_num)
theorem B419405 : Blo 275825 419405 := bbase (se 3 (by rfl) ⟨78638, by rfl⟩ : syracuseStep 419405 = 157277) (by norm_num)
theorem B419429 : Blo 275825 419429 := bbase (se 4 (by rfl) ⟨39321, by rfl⟩ : syracuseStep 419429 = 78643) (by norm_num)
theorem B353909 : Blo 275825 353909 := bbase (se 5 (by rfl) ⟨16589, by rfl⟩ : syracuseStep 353909 = 33179) (by norm_num)
theorem B419453 : Blo 275825 419453 := bbase (se 3 (by rfl) ⟨78647, by rfl⟩ : syracuseStep 419453 = 157295) (by norm_num)
theorem B419477 : Blo 275825 419477 := bbase (se 6 (by rfl) ⟨9831, by rfl⟩ : syracuseStep 419477 = 19663) (by norm_num)
theorem B419501 : Blo 275825 419501 := bbase (se 3 (by rfl) ⟨78656, by rfl⟩ : syracuseStep 419501 = 157313) (by norm_num)
theorem B353965 : Blo 275825 353965 := bbase (se 3 (by rfl) ⟨66368, by rfl⟩ : syracuseStep 353965 = 132737) (by norm_num)
theorem B353977 : Blo 275825 353977 := bbase (se 2 (by rfl) ⟨132741, by rfl⟩ : syracuseStep 353977 = 265483) (by norm_num)
theorem B419525 : Blo 275825 419525 := bbase (se 4 (by rfl) ⟨39330, by rfl⟩ : syracuseStep 419525 = 78661) (by norm_num)
theorem B419549 : Blo 275825 419549 := bbase (se 3 (by rfl) ⟨78665, by rfl⟩ : syracuseStep 419549 = 157331) (by norm_num)
theorem B419573 : Blo 275825 419573 := bbase (se 5 (by rfl) ⟨19667, by rfl⟩ : syracuseStep 419573 = 39335) (by norm_num)
theorem B419597 : Blo 275825 419597 := bbase (se 3 (by rfl) ⟨78674, by rfl⟩ : syracuseStep 419597 = 157349) (by norm_num)
theorem B354061 : Blo 275825 354061 := bbase (se 3 (by rfl) ⟨66386, by rfl⟩ : syracuseStep 354061 = 132773) (by norm_num)
theorem B419621 : Blo 275825 419621 := bbase (se 4 (by rfl) ⟨39339, by rfl⟩ : syracuseStep 419621 = 78679) (by norm_num)
theorem B419645 : Blo 275825 419645 := bbase (se 3 (by rfl) ⟨78683, by rfl⟩ : syracuseStep 419645 = 157367) (by norm_num)
theorem B1206101 : Blo 275825 1206101 := bbase (se 9 (by rfl) ⟨3533, by rfl⟩ : syracuseStep 1206101 = 7067) (by norm_num)
theorem B419669 : Blo 275825 419669 := bbase (se 9 (by rfl) ⟨1229, by rfl⟩ : syracuseStep 419669 = 2459) (by norm_num)
theorem B943973 : Blo 275825 943973 := bbase (se 4 (by rfl) ⟨88497, by rfl⟩ : syracuseStep 943973 = 176995) (by norm_num)
theorem B419693 : Blo 275825 419693 := bbase (se 3 (by rfl) ⟨78692, by rfl⟩ : syracuseStep 419693 = 157385) (by norm_num)
theorem B1402757 : Blo 275825 1402757 := bbase (se 4 (by rfl) ⟨131508, by rfl⟩ : syracuseStep 1402757 = 263017) (by norm_num)
theorem B419717 : Blo 275825 419717 := bbase (se 4 (by rfl) ⟨39348, by rfl⟩ : syracuseStep 419717 = 78697) (by norm_num)
theorem B321509 : Blo 275825 321509 := bbase (se 4 (by rfl) ⟨30141, by rfl⟩ : syracuseStep 321509 = 60283) (by norm_num)
theorem B944405 : Blo 275825 944405 := bbase (se 6 (by rfl) ⟨22134, by rfl⟩ : syracuseStep 944405 = 44269) (by norm_num)
theorem B1600469 : Blo 275825 1600469 := bbase (se 7 (by rfl) ⟨18755, by rfl⟩ : syracuseStep 1600469 = 37511) (by norm_num)
theorem B1404053 : Blo 275825 1404053 := bbase (se 6 (by rfl) ⟨32907, by rfl⟩ : syracuseStep 1404053 = 65815) (by norm_num)
theorem B1338581 : Blo 275825 1338581 := bbase (se 7 (by rfl) ⟨15686, by rfl⟩ : syracuseStep 1338581 = 31373) (by norm_num)
theorem B421133 : Blo 275825 421133 := bbase (se 3 (by rfl) ⟨78962, by rfl⟩ : syracuseStep 421133 = 157925) (by norm_num)
theorem B1338677 : Blo 275825 1338677 := bbase (se 5 (by rfl) ⟨62750, by rfl⟩ : syracuseStep 1338677 = 125501) (by norm_num)
theorem B716197 : Blo 275825 716197 := bbase (se 4 (by rfl) ⟨67143, by rfl⟩ : syracuseStep 716197 = 134287) (by norm_num)
theorem B421741 : Blo 275825 421741 := bbase (se 3 (by rfl) ⟨79076, by rfl⟩ : syracuseStep 421741 = 158153) (by norm_num)
theorem B1503157 : Blo 275825 1503157 := bbase (se 5 (by rfl) ⟨70460, by rfl⟩ : syracuseStep 1503157 = 140921) (by norm_num)
theorem B356333 : Blo 275825 356333 := bbase (se 3 (by rfl) ⟨66812, by rfl⟩ : syracuseStep 356333 = 133625) (by norm_num)
theorem B356665 : Blo 275825 356665 := bbase (se 2 (by rfl) ⟨133749, by rfl⟩ : syracuseStep 356665 = 267499) (by norm_num)
theorem B1405349 : Blo 275825 1405349 := bbase (se 4 (by rfl) ⟨131751, by rfl⟩ : syracuseStep 1405349 = 263503) (by norm_num)
theorem B356933 : Blo 275825 356933 := bbase (se 4 (by rfl) ⟨33462, by rfl⟩ : syracuseStep 356933 = 66925) (by norm_num)
theorem B1504021 : Blo 275825 1504021 := bbase (se 6 (by rfl) ⟨35250, by rfl⟩ : syracuseStep 1504021 = 70501) (by norm_num)
theorem B750389 : Blo 275825 750389 := bbase (se 5 (by rfl) ⟨35174, by rfl⟩ : syracuseStep 750389 = 70349) (by norm_num)
theorem B1340597 : Blo 275825 1340597 := bbase (se 5 (by rfl) ⟨62840, by rfl⟩ : syracuseStep 1340597 = 125681) (by norm_num)
theorem B2684117 : Blo 275825 2684117 := bbase (se 7 (by rfl) ⟨31454, by rfl⟩ : syracuseStep 2684117 = 62909) (by norm_num)
theorem B423245 : Blo 275825 423245 := bbase (se 3 (by rfl) ⟨79358, by rfl⟩ : syracuseStep 423245 = 158717) (by norm_num)
theorem B357733 : Blo 275825 357733 := bbase (se 4 (by rfl) ⟨33537, by rfl⟩ : syracuseStep 357733 = 67075) (by norm_num)
theorem B5338709 : Blo 275825 5338709 := bbase (se 8 (by rfl) ⟨31281, by rfl⟩ : syracuseStep 5338709 = 62563) (by norm_num)
theorem B1406645 : Blo 275825 1406645 := bbase (se 5 (by rfl) ⟨65936, by rfl⟩ : syracuseStep 1406645 = 131873) (by norm_num)
theorem B849637 : Blo 275825 849637 := bbase (se 4 (by rfl) ⟨79653, by rfl⟩ : syracuseStep 849637 = 159307) (by norm_num)
theorem B358225 : Blo 275825 358225 := bbase (se 2 (by rfl) ⟨134334, by rfl⟩ : syracuseStep 358225 = 268669) (by norm_num)
theorem B5699413 : Blo 275825 5699413 := bbase (se 9 (by rfl) ⟨16697, by rfl⟩ : syracuseStep 5699413 = 33395) (by norm_num)
theorem B948181 : Blo 275825 948181 := bbase (se 7 (by rfl) ⟨11111, by rfl⟩ : syracuseStep 948181 = 22223) (by norm_num)
theorem B620621 : Blo 275825 620621 := bbase (se 3 (by rfl) ⟨116366, by rfl⟩ : syracuseStep 620621 = 232733) (by norm_num)
theorem B620693 : Blo 275825 620693 := bbase (se 6 (by rfl) ⟨14547, by rfl⟩ : syracuseStep 620693 = 29095) (by norm_num)
theorem B620765 : Blo 275825 620765 := bbase (se 3 (by rfl) ⟨116393, by rfl⟩ : syracuseStep 620765 = 232787) (by norm_num)
theorem B620837 : Blo 275825 620837 := bbase (se 4 (by rfl) ⟨58203, by rfl⟩ : syracuseStep 620837 = 116407) (by norm_num)
theorem B620909 : Blo 275825 620909 := bbase (se 3 (by rfl) ⟨116420, by rfl⟩ : syracuseStep 620909 = 232841) (by norm_num)
theorem B620981 : Blo 275825 620981 := bbase (se 5 (by rfl) ⟨29108, by rfl⟩ : syracuseStep 620981 = 58217) (by norm_num)
theorem B621053 : Blo 275825 621053 := bbase (se 3 (by rfl) ⟨116447, by rfl⟩ : syracuseStep 621053 = 232895) (by norm_num)
theorem B3176981 : Blo 275825 3176981 := bbase (se 6 (by rfl) ⟨74460, by rfl⟩ : syracuseStep 3176981 = 148921) (by norm_num)
theorem B621125 : Blo 275825 621125 := bbase (se 4 (by rfl) ⟨58230, by rfl⟩ : syracuseStep 621125 = 116461) (by norm_num)
theorem B1342021 : Blo 275825 1342021 := bbase (se 4 (by rfl) ⟨125814, by rfl⟩ : syracuseStep 1342021 = 251629) (by norm_num)
theorem B326273 : Blo 275825 326273 := bbase (se 2 (by rfl) ⟨122352, by rfl⟩ : syracuseStep 326273 = 244705) (by norm_num)
theorem B621197 : Blo 275825 621197 := bbase (se 3 (by rfl) ⟨116474, by rfl⟩ : syracuseStep 621197 = 232949) (by norm_num)
theorem B5307029 : Blo 275825 5307029 := bbase (se 6 (by rfl) ⟨124383, by rfl⟩ : syracuseStep 5307029 = 248767) (by norm_num)
theorem B621269 : Blo 275825 621269 := bbase (se 7 (by rfl) ⟨7280, by rfl⟩ : syracuseStep 621269 = 14561) (by norm_num)
theorem B621341 : Blo 275825 621341 := bbase (se 3 (by rfl) ⟨116501, by rfl⟩ : syracuseStep 621341 = 233003) (by norm_num)
theorem B621413 : Blo 275825 621413 := bbase (se 4 (by rfl) ⟨58257, by rfl⟩ : syracuseStep 621413 = 116515) (by norm_num)
theorem B621485 : Blo 275825 621485 := bbase (se 3 (by rfl) ⟨116528, by rfl⟩ : syracuseStep 621485 = 233057) (by norm_num)
theorem B1407941 : Blo 275825 1407941 := bbase (se 4 (by rfl) ⟨131994, by rfl⟩ : syracuseStep 1407941 = 263989) (by norm_num)
theorem B883685 : Blo 275825 883685 := bbase (se 4 (by rfl) ⟨82845, by rfl⟩ : syracuseStep 883685 = 165691) (by norm_num)
theorem B2096117 : Blo 275825 2096117 := bbase (se 5 (by rfl) ⟨98255, by rfl⟩ : syracuseStep 2096117 = 196511) (by norm_num)
theorem B621557 : Blo 275825 621557 := bbase (se 5 (by rfl) ⟨29135, by rfl⟩ : syracuseStep 621557 = 58271) (by norm_num)
theorem B621629 : Blo 275825 621629 := bbase (se 3 (by rfl) ⟨116555, by rfl⟩ : syracuseStep 621629 = 233111) (by norm_num)
theorem B1178725 : Blo 275825 1178725 := bbase (se 4 (by rfl) ⟨110505, by rfl⟩ : syracuseStep 1178725 = 221011) (by norm_num)
theorem B621701 : Blo 275825 621701 := bbase (se 4 (by rfl) ⟨58284, by rfl⟩ : syracuseStep 621701 = 116569) (by norm_num)
theorem B621773 : Blo 275825 621773 := bbase (se 3 (by rfl) ⟨116582, by rfl⟩ : syracuseStep 621773 = 233165) (by norm_num)
theorem B621845 : Blo 275825 621845 := bbase (se 6 (by rfl) ⟨14574, by rfl⟩ : syracuseStep 621845 = 29149) (by norm_num)
theorem B425245 : Blo 275825 425245 := bbase (se 3 (by rfl) ⟨79733, by rfl⟩ : syracuseStep 425245 = 159467) (by norm_num)
theorem B621917 : Blo 275825 621917 := bbase (se 3 (by rfl) ⟨116609, by rfl⟩ : syracuseStep 621917 = 233219) (by norm_num)
theorem B621989 : Blo 275825 621989 := bbase (se 4 (by rfl) ⟨58311, by rfl⟩ : syracuseStep 621989 = 116623) (by norm_num)
theorem B523741 : Blo 275825 523741 := bbase (se 3 (by rfl) ⟨98201, by rfl⟩ : syracuseStep 523741 = 196403) (by norm_num)
theorem B622061 : Blo 275825 622061 := bbase (se 3 (by rfl) ⟨116636, by rfl⟩ : syracuseStep 622061 = 233273) (by norm_num)
theorem B622133 : Blo 275825 622133 := bbase (se 5 (by rfl) ⟨29162, by rfl⟩ : syracuseStep 622133 = 58325) (by norm_num)
theorem B392789 : Blo 275825 392789 := bbase (se 8 (by rfl) ⟨2301, by rfl⟩ : syracuseStep 392789 = 4603) (by norm_num)
theorem B523901 : Blo 275825 523901 := bbase (se 3 (by rfl) ⟨98231, by rfl⟩ : syracuseStep 523901 = 196463) (by norm_num)
theorem B622205 : Blo 275825 622205 := bbase (se 3 (by rfl) ⟨116663, by rfl⟩ : syracuseStep 622205 = 233327) (by norm_num)
theorem B622277 : Blo 275825 622277 := bbase (se 4 (by rfl) ⟨58338, by rfl⟩ : syracuseStep 622277 = 116677) (by norm_num)
theorem B786181 : Blo 275825 786181 := bbase (se 4 (by rfl) ⟨73704, by rfl⟩ : syracuseStep 786181 = 147409) (by norm_num)
theorem B524045 : Blo 275825 524045 := bbase (se 3 (by rfl) ⟨98258, by rfl⟩ : syracuseStep 524045 = 196517) (by norm_num)
theorem B622349 : Blo 275825 622349 := bbase (se 3 (by rfl) ⟨116690, by rfl⟩ : syracuseStep 622349 = 233381) (by norm_num)
theorem B294673 : Blo 275825 294673 := bbase (se 2 (by rfl) ⟨110502, by rfl⟩ : syracuseStep 294673 = 221005) (by norm_num)
theorem B1179461 : Blo 275825 1179461 := bbase (se 4 (by rfl) ⟨110574, by rfl⟩ : syracuseStep 1179461 = 221149) (by norm_num)
theorem B622421 : Blo 275825 622421 := bbase (se 9 (by rfl) ⟨1823, by rfl⟩ : syracuseStep 622421 = 3647) (by norm_num)
theorem B294797 : Blo 275825 294797 := bbase (se 3 (by rfl) ⟨55274, by rfl⟩ : syracuseStep 294797 = 110549) (by norm_num)
theorem B622493 : Blo 275825 622493 := bbase (se 3 (by rfl) ⟨116717, by rfl⟩ : syracuseStep 622493 = 233435) (by norm_num)
theorem B786341 : Blo 275825 786341 := bbase (se 4 (by rfl) ⟨73719, by rfl⟩ : syracuseStep 786341 = 147439) (by norm_num)
theorem B5046229 : Blo 275825 5046229 := bbase (se 7 (by rfl) ⟨59135, by rfl⟩ : syracuseStep 5046229 = 118271) (by norm_num)
theorem B622565 : Blo 275825 622565 := bbase (se 4 (by rfl) ⟨58365, by rfl⟩ : syracuseStep 622565 = 116731) (by norm_num)
theorem B1179683 : Blo 275825 1179683 := bstep (se 1 (by rfl) ⟨884762, by rfl⟩ : syracuseStep 1179683 = 1769525) B1769525
theorem B622673 : Blo 275825 622673 := bstep (se 2 (by rfl) ⟨233502, by rfl⟩ : syracuseStep 622673 = 467005) B467005
theorem B524387 : Blo 275825 524387 := bstep (se 1 (by rfl) ⟨393290, by rfl⟩ : syracuseStep 524387 = 786581) B786581
theorem B622691 : Blo 275825 622691 := bstep (se 1 (by rfl) ⟨467018, by rfl⟩ : syracuseStep 622691 = 934037) B934037
theorem B393427 : Blo 275825 393427 := bstep (se 1 (by rfl) ⟨295070, by rfl⟩ : syracuseStep 393427 = 590141) B590141
theorem B1573091 : Blo 275825 1573091 := bstep (se 1 (by rfl) ⟨1179818, by rfl⟩ : syracuseStep 1573091 = 2359637) B2359637
theorem B1048909 : Blo 275825 1048909 := bstep (se 3 (by rfl) ⟨196670, by rfl⟩ : syracuseStep 1048909 = 393341) B393341
theorem B754001 : Blo 275825 754001 := bstep (se 2 (by rfl) ⟨282750, by rfl⟩ : syracuseStep 754001 = 565501) B565501
theorem B786797 : Blo 275825 786797 := bstep (se 3 (by rfl) ⟨147524, by rfl⟩ : syracuseStep 786797 = 295049) B295049
theorem B622961 : Blo 275825 622961 := bstep (se 2 (by rfl) ⟨233610, by rfl⟩ : syracuseStep 622961 = 467221) B467221
theorem B622979 : Blo 275825 622979 := bstep (se 1 (by rfl) ⟨467234, by rfl⟩ : syracuseStep 622979 = 934469) B934469
theorem B3015053 : Blo 275825 3015053 := bstep (se 3 (by rfl) ⟨565322, by rfl⟩ : syracuseStep 3015053 = 1130645) B1130645
theorem B393763 : Blo 275825 393763 := bstep (se 1 (by rfl) ⟨295322, by rfl⟩ : syracuseStep 393763 = 590645) B590645
theorem B885325 : Blo 275825 885325 := bstep (se 3 (by rfl) ⟨165998, by rfl⟩ : syracuseStep 885325 = 331997) B331997
theorem B623249 : Blo 275825 623249 := bstep (se 2 (by rfl) ⟨233718, by rfl⟩ : syracuseStep 623249 = 467437) B467437
theorem B623267 : Blo 275825 623267 := bstep (se 1 (by rfl) ⟨467450, by rfl⟩ : syracuseStep 623267 = 934901) B934901
theorem B12321557 : Blo 275825 12321557 := bstep (se 6 (by rfl) ⟨288786, by rfl⟩ : syracuseStep 12321557 = 577573) B577573
theorem B590627 : Blo 275825 590627 := bstep (se 1 (by rfl) ⟨442970, by rfl⟩ : syracuseStep 590627 = 885941) B885941
theorem B2098061 : Blo 275825 2098061 := bstep (se 3 (by rfl) ⟨393386, by rfl⟩ : syracuseStep 2098061 = 786773) B786773
theorem B623537 : Blo 275825 623537 := bstep (se 2 (by rfl) ⟨233826, by rfl⟩ : syracuseStep 623537 = 467653) B467653
theorem B623555 : Blo 275825 623555 := bstep (se 1 (by rfl) ⟨467666, by rfl⟩ : syracuseStep 623555 = 935333) B935333
theorem B394321 : Blo 275825 394321 := bstep (se 2 (by rfl) ⟨147870, by rfl⟩ : syracuseStep 394321 = 295741) B295741
theorem B1049699 : Blo 275825 1049699 := bstep (se 1 (by rfl) ⟨787274, by rfl⟩ : syracuseStep 1049699 = 1574549) B1574549
theorem B394355 : Blo 275825 394355 := bstep (se 1 (by rfl) ⟨295766, by rfl⟩ : syracuseStep 394355 = 591533) B591533
theorem B525457 : Blo 275825 525457 := bstep (se 2 (by rfl) ⟨197046, by rfl⟩ : syracuseStep 525457 = 394093) B394093
theorem B1574093 : Blo 275825 1574093 := bstep (se 3 (by rfl) ⟨295142, by rfl⟩ : syracuseStep 1574093 = 590285) B590285
theorem B623825 : Blo 275825 623825 := bstep (se 2 (by rfl) ⟨233934, by rfl⟩ : syracuseStep 623825 = 467869) B467869
theorem B623843 : Blo 275825 623843 := bstep (se 1 (by rfl) ⟨467882, by rfl⟩ : syracuseStep 623843 = 935765) B935765
theorem B624113 : Blo 275825 624113 := bstep (se 2 (by rfl) ⟨234042, by rfl⟩ : syracuseStep 624113 = 468085) B468085
theorem B624131 : Blo 275825 624131 := bstep (se 1 (by rfl) ⟨468098, by rfl⟩ : syracuseStep 624131 = 936197) B936197
theorem B755203 : Blo 275825 755203 := bstep (se 1 (by rfl) ⟨566402, by rfl⟩ : syracuseStep 755203 = 1132805) B1132805
theorem B787981 : Blo 275825 787981 := bstep (se 3 (by rfl) ⟨147746, by rfl⟩ : syracuseStep 787981 = 295493) B295493
theorem B951821 : Blo 275825 951821 := bstep (se 3 (by rfl) ⟨178466, by rfl⟩ : syracuseStep 951821 = 356933) B356933
theorem B886403 : Blo 275825 886403 := bstep (se 1 (by rfl) ⟨664802, by rfl⟩ : syracuseStep 886403 = 1329605) B1329605
theorem B394913 : Blo 275825 394913 := bstep (se 2 (by rfl) ⟨148092, by rfl⟩ : syracuseStep 394913 = 296185) B296185
theorem B460513 : Blo 275825 460513 := bstep (se 2 (by rfl) ⟨172692, by rfl⟩ : syracuseStep 460513 = 345385) B345385
theorem B1181425 : Blo 275825 1181425 := bstep (se 2 (by rfl) ⟨443034, by rfl⟩ : syracuseStep 1181425 = 886069) B886069
theorem B1050353 : Blo 275825 1050353 := bstep (se 2 (by rfl) ⟨393882, by rfl⟩ : syracuseStep 1050353 = 787765) B787765
theorem B394993 : Blo 275825 394993 := bstep (se 2 (by rfl) ⟨148122, by rfl⟩ : syracuseStep 394993 = 296245) B296245
theorem B624401 : Blo 275825 624401 := bstep (se 2 (by rfl) ⟨234150, by rfl⟩ : syracuseStep 624401 = 468301) B468301
theorem B624419 : Blo 275825 624419 := bstep (se 1 (by rfl) ⟨468314, by rfl⟩ : syracuseStep 624419 = 936629) B936629
theorem B624689 : Blo 275825 624689 := bstep (se 2 (by rfl) ⟨234258, by rfl⟩ : syracuseStep 624689 = 468517) B468517
theorem B624707 : Blo 275825 624707 := bstep (se 1 (by rfl) ⟨468530, by rfl⟩ : syracuseStep 624707 = 937061) B937061
theorem B2361413 : Blo 275825 2361413 := bstep (se 4 (by rfl) ⟨221382, by rfl⟩ : syracuseStep 2361413 = 442765) B442765
theorem B2001037 : Blo 275825 2001037 := bstep (se 3 (by rfl) ⟨375194, by rfl⟩ : syracuseStep 2001037 = 750389) B750389
theorem B526513 : Blo 275825 526513 := bstep (se 2 (by rfl) ⟨197442, by rfl⟩ : syracuseStep 526513 = 394885) B394885
theorem B297155 : Blo 275825 297155 := bstep (se 1 (by rfl) ⟨222866, by rfl⟩ : syracuseStep 297155 = 445733) B445733
theorem B887057 : Blo 275825 887057 := bstep (se 2 (by rfl) ⟨332646, by rfl⟩ : syracuseStep 887057 = 665293) B665293
theorem B624977 : Blo 275825 624977 := bstep (se 2 (by rfl) ⟨234366, by rfl⟩ : syracuseStep 624977 = 468733) B468733
theorem B624995 : Blo 275825 624995 := bstep (se 1 (by rfl) ⟨468746, by rfl⟩ : syracuseStep 624995 = 937493) B937493
theorem B756067 : Blo 275825 756067 := bstep (se 1 (by rfl) ⟨567050, by rfl⟩ : syracuseStep 756067 = 1134101) B1134101
theorem B1411505 : Blo 275825 1411505 := bstep (se 2 (by rfl) ⟨529314, by rfl⟩ : syracuseStep 1411505 = 1058629) B1058629
theorem B395779 : Blo 275825 395779 := bstep (se 1 (by rfl) ⟨296834, by rfl⟩ : syracuseStep 395779 = 593669) B593669
theorem B789041 : Blo 275825 789041 := bstep (se 2 (by rfl) ⟨295890, by rfl⟩ : syracuseStep 789041 = 591781) B591781
theorem B526915 : Blo 275825 526915 := bstep (se 1 (by rfl) ⟨395186, by rfl⟩ : syracuseStep 526915 = 790373) B790373
theorem B526961 : Blo 275825 526961 := bstep (se 2 (by rfl) ⟨197610, by rfl⟩ : syracuseStep 526961 = 395221) B395221
theorem B625265 : Blo 275825 625265 := bstep (se 2 (by rfl) ⟨234474, by rfl⟩ : syracuseStep 625265 = 468949) B468949
theorem B625283 : Blo 275825 625283 := bstep (se 1 (by rfl) ⟨468962, by rfl⟩ : syracuseStep 625283 = 937925) B937925
theorem B592643 : Blo 275825 592643 := bstep (se 1 (by rfl) ⟨444482, by rfl⟩ : syracuseStep 592643 = 888965) B888965
theorem B1641329 : Blo 275825 1641329 := bstep (se 2 (by rfl) ⟨615498, by rfl⟩ : syracuseStep 1641329 = 1230997) B1230997
theorem B527249 : Blo 275825 527249 := bstep (se 2 (by rfl) ⟨197718, by rfl⟩ : syracuseStep 527249 = 395437) B395437
theorem B625553 : Blo 275825 625553 := bstep (se 2 (by rfl) ⟨234582, by rfl⟩ : syracuseStep 625553 = 469165) B469165
theorem B625571 : Blo 275825 625571 := bstep (se 1 (by rfl) ⟨469178, by rfl⟩ : syracuseStep 625571 = 938357) B938357
theorem B396257 : Blo 275825 396257 := bstep (se 2 (by rfl) ⟨148596, by rfl⟩ : syracuseStep 396257 = 297193) B297193
theorem B1772549 : Blo 275825 1772549 := bstep (se 4 (by rfl) ⟨166176, by rfl⟩ : syracuseStep 1772549 = 332353) B332353
theorem B396371 : Blo 275825 396371 := bstep (se 1 (by rfl) ⟨297278, by rfl⟩ : syracuseStep 396371 = 594557) B594557
theorem B3574925 : Blo 275825 3574925 := bstep (se 3 (by rfl) ⟨670298, by rfl⟩ : syracuseStep 3574925 = 1340597) B1340597
theorem B1051811 : Blo 275825 1051811 := bstep (se 1 (by rfl) ⟨788858, by rfl⟩ : syracuseStep 1051811 = 1577717) B1577717
theorem B396451 : Blo 275825 396451 := bstep (se 1 (by rfl) ⟨297338, by rfl⟩ : syracuseStep 396451 = 594677) B594677
theorem B756913 : Blo 275825 756913 := bstep (se 2 (by rfl) ⟨283842, by rfl⟩ : syracuseStep 756913 = 567685) B567685
theorem B1051825 : Blo 275825 1051825 := bstep (se 2 (by rfl) ⟨394434, by rfl⟩ : syracuseStep 1051825 = 788869) B788869
theorem B625841 : Blo 275825 625841 := bstep (se 2 (by rfl) ⟨234690, by rfl⟩ : syracuseStep 625841 = 469381) B469381
theorem B625859 : Blo 275825 625859 := bstep (se 1 (by rfl) ⟨469394, by rfl⟩ : syracuseStep 625859 = 938789) B938789
theorem B789713 : Blo 275825 789713 := bstep (se 2 (by rfl) ⟨296142, by rfl⟩ : syracuseStep 789713 = 592285) B592285
theorem B2035043 : Blo 275825 2035043 := bstep (se 1 (by rfl) ⟨1526282, by rfl⟩ : syracuseStep 2035043 = 3052565) B3052565
theorem B626129 : Blo 275825 626129 := bstep (se 2 (by rfl) ⟨234798, by rfl⟩ : syracuseStep 626129 = 469597) B469597
theorem B626147 : Blo 275825 626147 := bstep (se 1 (by rfl) ⟨469610, by rfl⟩ : syracuseStep 626147 = 939221) B939221
theorem B1019405 : Blo 275825 1019405 := bstep (se 3 (by rfl) ⟨191138, by rfl⟩ : syracuseStep 1019405 = 382277) B382277
theorem B888401 : Blo 275825 888401 := bstep (se 2 (by rfl) ⟨333150, by rfl⟩ : syracuseStep 888401 = 666301) B666301
theorem B527971 : Blo 275825 527971 := bstep (se 1 (by rfl) ⟨395978, by rfl⟩ : syracuseStep 527971 = 791957) B791957
theorem B1183373 : Blo 275825 1183373 := bstep (se 3 (by rfl) ⟨221882, by rfl⟩ : syracuseStep 1183373 = 443765) B443765
theorem B397009 : Blo 275825 397009 := bstep (se 2 (by rfl) ⟨148878, by rfl⟩ : syracuseStep 397009 = 297757) B297757
theorem B2100977 : Blo 275825 2100977 := bstep (se 2 (by rfl) ⟨787866, by rfl⟩ : syracuseStep 2100977 = 1575733) B1575733
theorem B626417 : Blo 275825 626417 := bstep (se 2 (by rfl) ⟨234906, by rfl⟩ : syracuseStep 626417 = 469813) B469813
theorem B626435 : Blo 275825 626435 := bstep (se 1 (by rfl) ⟨469826, by rfl⟩ : syracuseStep 626435 = 939653) B939653
theorem B1412963 : Blo 275825 1412963 := bstep (se 1 (by rfl) ⟨1059722, by rfl⟩ : syracuseStep 1412963 = 2119445) B2119445
theorem B790499 : Blo 275825 790499 := bstep (se 1 (by rfl) ⟨592874, by rfl⟩ : syracuseStep 790499 = 1185749) B1185749
theorem B626705 : Blo 275825 626705 := bstep (se 2 (by rfl) ⟨235014, by rfl⟩ : syracuseStep 626705 = 470029) B470029
theorem B528419 : Blo 275825 528419 := bstep (se 1 (by rfl) ⟨396314, by rfl⟩ : syracuseStep 528419 = 792629) B792629
theorem B626723 : Blo 275825 626723 := bstep (se 1 (by rfl) ⟨470042, by rfl⟩ : syracuseStep 626723 = 940085) B940085
theorem B1577009 : Blo 275825 1577009 := bstep (se 2 (by rfl) ⟨591378, by rfl⟩ : syracuseStep 1577009 = 1182757) B1182757
theorem B790829 : Blo 275825 790829 := bstep (se 3 (by rfl) ⟨148280, by rfl⟩ : syracuseStep 790829 = 296561) B296561
theorem B626993 : Blo 275825 626993 := bstep (se 2 (by rfl) ⟨235122, by rfl⟩ : syracuseStep 626993 = 470245) B470245
theorem B528707 : Blo 275825 528707 := bstep (se 1 (by rfl) ⟨396530, by rfl⟩ : syracuseStep 528707 = 793061) B793061
theorem B627011 : Blo 275825 627011 := bstep (se 1 (by rfl) ⟨470258, by rfl⟩ : syracuseStep 627011 = 940517) B940517
theorem B790897 : Blo 275825 790897 := bstep (se 2 (by rfl) ⟨296586, by rfl⟩ : syracuseStep 790897 = 593173) B593173
theorem B332147 : Blo 275825 332147 := bstep (se 1 (by rfl) ⟨249110, by rfl⟩ : syracuseStep 332147 = 498221) B498221
theorem B397715 : Blo 275825 397715 := bstep (se 1 (by rfl) ⟨298286, by rfl⟩ : syracuseStep 397715 = 596573) B596573
theorem B954929 : Blo 275825 954929 := bstep (se 2 (by rfl) ⟨358098, by rfl⟩ : syracuseStep 954929 = 716197) B716197
theorem B627281 : Blo 275825 627281 := bstep (se 2 (by rfl) ⟨235230, by rfl⟩ : syracuseStep 627281 = 470461) B470461
theorem B1053283 : Blo 275825 1053283 := bstep (se 1 (by rfl) ⟨789962, by rfl⟩ : syracuseStep 1053283 = 1579925) B1579925
theorem B627299 : Blo 275825 627299 := bstep (se 1 (by rfl) ⟨470474, by rfl⟩ : syracuseStep 627299 = 940949) B940949
theorem B791171 : Blo 275825 791171 := bstep (se 1 (by rfl) ⟨593378, by rfl⟩ : syracuseStep 791171 = 1186757) B1186757
theorem B1413773 : Blo 275825 1413773 := bstep (se 3 (by rfl) ⟨265082, by rfl⟩ : syracuseStep 1413773 = 530165) B530165
theorem B889517 : Blo 275825 889517 := bstep (se 3 (by rfl) ⟨166784, by rfl⟩ : syracuseStep 889517 = 333569) B333569
theorem B3609269 : Blo 275825 3609269 := bstep (se 5 (by rfl) ⟨169184, by rfl⟩ : syracuseStep 3609269 = 338369) B338369
theorem B594659 : Blo 275825 594659 := bstep (se 1 (by rfl) ⟨445994, by rfl⟩ : syracuseStep 594659 = 891989) B891989
theorem B627569 : Blo 275825 627569 := bstep (se 2 (by rfl) ⟨235338, by rfl⟩ : syracuseStep 627569 = 470677) B470677
theorem B627587 : Blo 275825 627587 := bstep (se 1 (by rfl) ⟨470690, by rfl⟩ : syracuseStep 627587 = 941381) B941381
theorem B3216269 : Blo 275825 3216269 := bstep (se 3 (by rfl) ⟨603050, by rfl⟩ : syracuseStep 3216269 = 1206101) B1206101
theorem B398353 : Blo 275825 398353 := bstep (se 2 (by rfl) ⟨149382, by rfl⟩ : syracuseStep 398353 = 298765) B298765
theorem B562321 : Blo 275825 562321 := bstep (se 2 (by rfl) ⟨210870, by rfl⟩ : syracuseStep 562321 = 421741) B421741
theorem B627857 : Blo 275825 627857 := bstep (se 2 (by rfl) ⟨235446, by rfl⟩ : syracuseStep 627857 = 470893) B470893
theorem B627875 : Blo 275825 627875 := bstep (se 1 (by rfl) ⟨470906, by rfl⟩ : syracuseStep 627875 = 941813) B941813
theorem B2004209 : Blo 275825 2004209 := bstep (se 2 (by rfl) ⟨751578, by rfl⟩ : syracuseStep 2004209 = 1503157) B1503157
theorem B529649 : Blo 275825 529649 := bstep (se 2 (by rfl) ⟨198618, by rfl⟩ : syracuseStep 529649 = 397237) B397237
theorem B857357 : Blo 275825 857357 := bstep (se 3 (by rfl) ⟨160754, by rfl⟩ : syracuseStep 857357 = 321509) B321509
theorem B628145 : Blo 275825 628145 := bstep (se 2 (by rfl) ⟨235554, by rfl⟩ : syracuseStep 628145 = 471109) B471109
theorem B628163 : Blo 275825 628163 := bstep (se 1 (by rfl) ⟨471122, by rfl⟩ : syracuseStep 628163 = 942245) B942245
theorem B792013 : Blo 275825 792013 := bstep (se 3 (by rfl) ⟨148502, by rfl⟩ : syracuseStep 792013 = 297005) B297005
theorem B1578467 : Blo 275825 1578467 := bstep (se 1 (by rfl) ⟨1183850, by rfl⟩ : syracuseStep 1578467 = 2367701) B2367701
theorem B792173 : Blo 275825 792173 := bstep (se 3 (by rfl) ⟨148532, by rfl⟩ : syracuseStep 792173 = 297065) B297065
theorem B628433 : Blo 275825 628433 := bstep (se 2 (by rfl) ⟨235662, by rfl⟩ : syracuseStep 628433 = 471325) B471325
theorem B1119971 : Blo 275825 1119971 := bstep (se 1 (by rfl) ⟨839978, by rfl⟩ : syracuseStep 1119971 = 1679957) B1679957
theorem B628451 : Blo 275825 628451 := bstep (se 1 (by rfl) ⟨471338, by rfl⟩ : syracuseStep 628451 = 942677) B942677
theorem B890605 : Blo 275825 890605 := bstep (se 3 (by rfl) ⟨166988, by rfl⟩ : syracuseStep 890605 = 333977) B333977
theorem B792355 : Blo 275825 792355 := bstep (se 1 (by rfl) ⟨594266, by rfl⟩ : syracuseStep 792355 = 1188533) B1188533
theorem B5084981 : Blo 275825 5084981 := bstep (se 5 (by rfl) ⟨238358, by rfl⟩ : syracuseStep 5084981 = 476717) B476717
theorem B595907 : Blo 275825 595907 := bstep (se 1 (by rfl) ⟨446930, by rfl⟩ : syracuseStep 595907 = 893861) B893861
theorem B2529251 : Blo 275825 2529251 := bstep (se 1 (by rfl) ⟨1896938, by rfl⟩ : syracuseStep 2529251 = 3793877) B3793877
theorem B628721 : Blo 275825 628721 := bstep (se 2 (by rfl) ⟨235770, by rfl⟩ : syracuseStep 628721 = 471541) B471541
theorem B628739 : Blo 275825 628739 := bstep (se 1 (by rfl) ⟨471554, by rfl⟩ : syracuseStep 628739 = 943109) B943109
theorem B530545 : Blo 275825 530545 := bstep (se 2 (by rfl) ⟨198954, by rfl⟩ : syracuseStep 530545 = 397909) B397909
theorem B2398349 : Blo 275825 2398349 := bstep (se 3 (by rfl) ⟨449690, by rfl⟩ : syracuseStep 2398349 = 899381) B899381
theorem B399587 : Blo 275825 399587 := bstep (se 1 (by rfl) ⟨299690, by rfl⟩ : syracuseStep 399587 = 599381) B599381
theorem B530705 : Blo 275825 530705 := bstep (se 2 (by rfl) ⟨199014, by rfl⟩ : syracuseStep 530705 = 398029) B398029
theorem B629009 : Blo 275825 629009 := bstep (se 2 (by rfl) ⟨235878, by rfl⟩ : syracuseStep 629009 = 471757) B471757
theorem B629027 : Blo 275825 629027 := bstep (se 1 (by rfl) ⟨471770, by rfl⟩ : syracuseStep 629027 = 943541) B943541
theorem B2005361 : Blo 275825 2005361 := bstep (se 2 (by rfl) ⟨752010, by rfl⟩ : syracuseStep 2005361 = 1504021) B1504021
theorem B596497 : Blo 275825 596497 := bstep (se 2 (by rfl) ⟨223686, by rfl⟩ : syracuseStep 596497 = 447373) B447373
theorem B629297 : Blo 275825 629297 := bstep (se 2 (by rfl) ⟨235986, by rfl⟩ : syracuseStep 629297 = 471973) B471973
theorem B465473 : Blo 275825 465473 := bstep (se 2 (by rfl) ⟨174552, by rfl⟩ : syracuseStep 465473 = 349105) B349105
theorem B629315 : Blo 275825 629315 := bstep (se 1 (by rfl) ⟨471986, by rfl⟩ : syracuseStep 629315 = 943973) B943973
theorem B629329 : Blo 275825 629329 := bstep (se 2 (by rfl) ⟨235998, by rfl⟩ : syracuseStep 629329 = 471997) B471997
theorem B531107 : Blo 275825 531107 := bstep (se 1 (by rfl) ⟨398330, by rfl⟩ : syracuseStep 531107 = 796661) B796661
theorem B3480245 : Blo 275825 3480245 := bstep (se 5 (by rfl) ⟨163136, by rfl⟩ : syracuseStep 3480245 = 326273) B326273
theorem B465601 : Blo 275825 465601 := bstep (se 2 (by rfl) ⟨174600, by rfl⟩ : syracuseStep 465601 = 349201) B349201
theorem B465635 : Blo 275825 465635 := bstep (se 1 (by rfl) ⟨349226, by rfl⟩ : syracuseStep 465635 = 698453) B698453
theorem B1055501 : Blo 275825 1055501 := bstep (se 3 (by rfl) ⟨197906, by rfl⟩ : syracuseStep 1055501 = 395813) B395813
theorem B629585 : Blo 275825 629585 := bstep (se 2 (by rfl) ⟨236094, by rfl⟩ : syracuseStep 629585 = 472189) B472189
theorem B465763 : Blo 275825 465763 := bstep (se 1 (by rfl) ⟨349322, by rfl⟩ : syracuseStep 465763 = 698645) B698645
theorem B629603 : Blo 275825 629603 := bstep (se 1 (by rfl) ⟨472202, by rfl⟩ : syracuseStep 629603 = 944405) B944405
theorem B465905 : Blo 275825 465905 := bstep (se 2 (by rfl) ⟨174714, by rfl⟩ : syracuseStep 465905 = 349429) B349429
theorem B400465 : Blo 275825 400465 := bstep (se 2 (by rfl) ⟨150174, by rfl⟩ : syracuseStep 400465 = 300349) B300349
theorem B466033 : Blo 275825 466033 := bstep (se 2 (by rfl) ⟨174762, by rfl⟩ : syracuseStep 466033 = 349525) B349525
theorem B793745 : Blo 275825 793745 := bstep (se 2 (by rfl) ⟨297654, by rfl⟩ : syracuseStep 793745 = 595309) B595309
theorem B466067 : Blo 275825 466067 := bstep (se 1 (by rfl) ⟨349550, by rfl⟩ : syracuseStep 466067 = 699101) B699101
theorem B335107 : Blo 275825 335107 := bstep (se 1 (by rfl) ⟨251330, by rfl⟩ : syracuseStep 335107 = 502661) B502661
theorem B466195 : Blo 275825 466195 := bstep (se 1 (by rfl) ⟨349646, by rfl⟩ : syracuseStep 466195 = 699293) B699293
theorem B466337 : Blo 275825 466337 := bstep (se 2 (by rfl) ⟨174876, by rfl⟩ : syracuseStep 466337 = 349753) B349753
theorem B892387 : Blo 275825 892387 := bstep (se 1 (by rfl) ⟨669290, by rfl⟩ : syracuseStep 892387 = 1338581) B1338581
theorem B466465 : Blo 275825 466465 := bstep (se 2 (by rfl) ⟨174924, by rfl⟩ : syracuseStep 466465 = 349849) B349849
theorem B892451 : Blo 275825 892451 := bstep (se 1 (by rfl) ⟨669338, by rfl⟩ : syracuseStep 892451 = 1338677) B1338677
theorem B466499 : Blo 275825 466499 := bstep (se 1 (by rfl) ⟨349874, by rfl⟩ : syracuseStep 466499 = 699749) B699749
theorem B1187405 : Blo 275825 1187405 := bstep (se 3 (by rfl) ⟨222638, by rfl⟩ : syracuseStep 1187405 = 445277) B445277
theorem B892529 : Blo 275825 892529 := bstep (se 2 (by rfl) ⟨334698, by rfl⟩ : syracuseStep 892529 = 669397) B669397
theorem B466627 : Blo 275825 466627 := bstep (se 1 (by rfl) ⟨349970, by rfl⟩ : syracuseStep 466627 = 699941) B699941
theorem B532259 : Blo 275825 532259 := bstep (se 1 (by rfl) ⟨399194, by rfl⟩ : syracuseStep 532259 = 798389) B798389
theorem B466769 : Blo 275825 466769 := bstep (se 2 (by rfl) ⟨175038, by rfl⟩ : syracuseStep 466769 = 350077) B350077
theorem B1187747 : Blo 275825 1187747 := bstep (se 1 (by rfl) ⟨890810, by rfl⟩ : syracuseStep 1187747 = 1781621) B1781621
theorem B466897 : Blo 275825 466897 := bstep (se 2 (by rfl) ⟨175086, by rfl⟩ : syracuseStep 466897 = 350173) B350173
theorem B466931 : Blo 275825 466931 := bstep (se 1 (by rfl) ⟨350198, by rfl⟩ : syracuseStep 466931 = 700397) B700397
theorem B794701 : Blo 275825 794701 := bstep (se 3 (by rfl) ⟨149006, by rfl⟩ : syracuseStep 794701 = 298013) B298013
theorem B467059 : Blo 275825 467059 := bstep (se 1 (by rfl) ⟨350294, by rfl⟩ : syracuseStep 467059 = 700589) B700589
theorem B467201 : Blo 275825 467201 := bstep (se 2 (by rfl) ⟨175200, by rfl⟩ : syracuseStep 467201 = 350401) B350401
theorem B794929 : Blo 275825 794929 := bstep (se 2 (by rfl) ⟨298098, by rfl⟩ : syracuseStep 794929 = 596197) B596197
theorem B1188209 : Blo 275825 1188209 := bstep (se 2 (by rfl) ⟨445578, by rfl⟩ : syracuseStep 1188209 = 891157) B891157
theorem B467329 : Blo 275825 467329 := bstep (se 2 (by rfl) ⟨175248, by rfl⟩ : syracuseStep 467329 = 350497) B350497
theorem B467363 : Blo 275825 467363 := bstep (se 1 (by rfl) ⟨350522, by rfl⟩ : syracuseStep 467363 = 701045) B701045
theorem B795089 : Blo 275825 795089 := bstep (se 2 (by rfl) ⟨298158, by rfl⟩ : syracuseStep 795089 = 596317) B596317
theorem B533027 : Blo 275825 533027 := bstep (se 1 (by rfl) ⟨399770, by rfl⟩ : syracuseStep 533027 = 799541) B799541
theorem B467491 : Blo 275825 467491 := bstep (se 1 (by rfl) ⟨350618, by rfl⟩ : syracuseStep 467491 = 701237) B701237
theorem B795203 : Blo 275825 795203 := bstep (se 1 (by rfl) ⟨596402, by rfl⟩ : syracuseStep 795203 = 1192805) B1192805
theorem B467633 : Blo 275825 467633 := bstep (se 2 (by rfl) ⟨175362, by rfl⟩ : syracuseStep 467633 = 350725) B350725
theorem B1123021 : Blo 275825 1123021 := bstep (se 3 (by rfl) ⟨210566, by rfl⟩ : syracuseStep 1123021 = 421133) B421133
theorem B467761 : Blo 275825 467761 := bstep (se 2 (by rfl) ⟨175410, by rfl⟩ : syracuseStep 467761 = 350821) B350821
theorem B467795 : Blo 275825 467795 := bstep (se 1 (by rfl) ⟨350846, by rfl⟩ : syracuseStep 467795 = 701693) B701693
theorem B467923 : Blo 275825 467923 := bstep (se 1 (by rfl) ⟨350942, by rfl⟩ : syracuseStep 467923 = 701885) B701885
theorem B468065 : Blo 275825 468065 := bstep (se 2 (by rfl) ⟨175524, by rfl⟩ : syracuseStep 468065 = 351049) B351049
theorem B1778851 : Blo 275825 1778851 := bstep (se 1 (by rfl) ⟨1334138, by rfl⟩ : syracuseStep 1778851 = 2668277) B2668277
theorem B468193 : Blo 275825 468193 := bstep (se 2 (by rfl) ⟨175572, by rfl⟩ : syracuseStep 468193 = 351145) B351145
theorem B337123 : Blo 275825 337123 := bstep (se 1 (by rfl) ⟨252842, by rfl⟩ : syracuseStep 337123 = 505685) B505685
theorem B468227 : Blo 275825 468227 := bstep (se 1 (by rfl) ⟨351170, by rfl⟩ : syracuseStep 468227 = 702341) B702341
theorem B468355 : Blo 275825 468355 := bstep (se 1 (by rfl) ⟨351266, by rfl⟩ : syracuseStep 468355 = 702533) B702533
theorem B894449 : Blo 275825 894449 := bstep (se 2 (by rfl) ⟨335418, by rfl⟩ : syracuseStep 894449 = 670837) B670837
theorem B468497 : Blo 275825 468497 := bstep (se 2 (by rfl) ⟨175686, by rfl⟩ : syracuseStep 468497 = 351373) B351373
theorem B796205 : Blo 275825 796205 := bstep (se 3 (by rfl) ⟨149288, by rfl⟩ : syracuseStep 796205 = 298577) B298577
theorem B1058417 : Blo 275825 1058417 := bstep (se 2 (by rfl) ⟨396906, by rfl⟩ : syracuseStep 1058417 = 793813) B793813
theorem B468625 : Blo 275825 468625 := bstep (se 2 (by rfl) ⟨175734, by rfl⟩ : syracuseStep 468625 = 351469) B351469
theorem B468659 : Blo 275825 468659 := bstep (se 1 (by rfl) ⟨351494, by rfl⟩ : syracuseStep 468659 = 702989) B702989
theorem B566993 : Blo 275825 566993 := bstep (se 2 (by rfl) ⟨212622, by rfl⟩ : syracuseStep 566993 = 425245) B425245
theorem B796387 : Blo 275825 796387 := bstep (se 1 (by rfl) ⟨597290, by rfl⟩ : syracuseStep 796387 = 1194581) B1194581
theorem B1910533 : Blo 275825 1910533 := bstep (se 4 (by rfl) ⟨179112, by rfl⟩ : syracuseStep 1910533 = 358225) B358225
theorem B468787 : Blo 275825 468787 := bstep (se 1 (by rfl) ⟨351590, by rfl⟩ : syracuseStep 468787 = 703181) B703181
theorem B796547 : Blo 275825 796547 := bstep (se 1 (by rfl) ⟨597410, by rfl⟩ : syracuseStep 796547 = 1194821) B1194821
theorem B468929 : Blo 275825 468929 := bstep (se 2 (by rfl) ⟨175848, by rfl⟩ : syracuseStep 468929 = 351697) B351697
theorem B698321 : Blo 275825 698321 := bstep (se 2 (by rfl) ⟨261870, by rfl⟩ : syracuseStep 698321 = 523741) B523741
theorem B2861041 : Blo 275825 2861041 := bstep (se 2 (by rfl) ⟨1072890, by rfl⟩ : syracuseStep 2861041 = 2145781) B2145781
theorem B894989 : Blo 275825 894989 := bstep (se 3 (by rfl) ⟨167810, by rfl⟩ : syracuseStep 894989 = 335621) B335621
theorem B469057 : Blo 275825 469057 := bstep (se 2 (by rfl) ⟨175896, by rfl⟩ : syracuseStep 469057 = 351793) B351793
theorem B469091 : Blo 275825 469091 := bstep (se 1 (by rfl) ⟨351818, by rfl⟩ : syracuseStep 469091 = 703637) B703637
theorem B1779853 : Blo 275825 1779853 := bstep (se 3 (by rfl) ⟨333722, by rfl⟩ : syracuseStep 1779853 = 667445) B667445
theorem B2009285 : Blo 275825 2009285 := bstep (se 4 (by rfl) ⟨188370, by rfl⟩ : syracuseStep 2009285 = 376741) B376741
theorem B5056739 : Blo 275825 5056739 := bstep (se 1 (by rfl) ⟨3792554, by rfl⟩ : syracuseStep 5056739 = 7585109) B7585109
theorem B469219 : Blo 275825 469219 := bstep (se 1 (by rfl) ⟨351914, by rfl⟩ : syracuseStep 469219 = 703829) B703829
theorem B502033 : Blo 275825 502033 := bstep (se 2 (by rfl) ⟨188262, by rfl⟩ : syracuseStep 502033 = 376525) B376525
theorem B469361 : Blo 275825 469361 := bstep (se 2 (by rfl) ⟨176010, by rfl⟩ : syracuseStep 469361 = 352021) B352021
theorem B469489 : Blo 275825 469489 := bstep (se 2 (by rfl) ⟨176058, by rfl⟩ : syracuseStep 469489 = 352117) B352117
theorem B469523 : Blo 275825 469523 := bstep (se 1 (by rfl) ⟨352142, by rfl⟩ : syracuseStep 469523 = 704285) B704285
theorem B6728305 : Blo 275825 6728305 := bstep (se 2 (by rfl) ⟨2523114, by rfl⟩ : syracuseStep 6728305 = 5046229) B5046229
theorem B2370161 : Blo 275825 2370161 := bstep (se 2 (by rfl) ⟨888810, by rfl⟩ : syracuseStep 2370161 = 1777621) B1777621
theorem B469651 : Blo 275825 469651 := bstep (se 1 (by rfl) ⟨352238, by rfl⟩ : syracuseStep 469651 = 704477) B704477
theorem B2992909 : Blo 275825 2992909 := bstep (se 3 (by rfl) ⟨561170, by rfl⟩ : syracuseStep 2992909 = 1122341) B1122341
theorem B469793 : Blo 275825 469793 := bstep (se 2 (by rfl) ⟨176172, by rfl⟩ : syracuseStep 469793 = 352345) B352345
theorem B633635 : Blo 275825 633635 := bstep (se 1 (by rfl) ⟨475226, by rfl⟩ : syracuseStep 633635 = 950453) B950453
theorem B469921 : Blo 275825 469921 := bstep (se 2 (by rfl) ⟨176220, by rfl⟩ : syracuseStep 469921 = 352441) B352441
theorem B699313 : Blo 275825 699313 := bstep (se 2 (by rfl) ⟨262242, by rfl⟩ : syracuseStep 699313 = 524485) B524485
theorem B469955 : Blo 275825 469955 := bstep (se 1 (by rfl) ⟨352466, by rfl⟩ : syracuseStep 469955 = 704933) B704933
theorem B1059875 : Blo 275825 1059875 := bstep (se 1 (by rfl) ⟨794906, by rfl⟩ : syracuseStep 1059875 = 1589813) B1589813
theorem B470083 : Blo 275825 470083 := bstep (se 1 (by rfl) ⟨352562, by rfl⟩ : syracuseStep 470083 = 705125) B705125
theorem B666755 : Blo 275825 666755 := bstep (se 1 (by rfl) ⟨500066, by rfl⟩ : syracuseStep 666755 = 1000133) B1000133
theorem B699587 : Blo 275825 699587 := bstep (se 1 (by rfl) ⟨524690, by rfl⟩ : syracuseStep 699587 = 1049381) B1049381
theorem B470225 : Blo 275825 470225 := bstep (se 2 (by rfl) ⟨176334, by rfl⟩ : syracuseStep 470225 = 352669) B352669
theorem B470353 : Blo 275825 470353 := bstep (se 2 (by rfl) ⟨176382, by rfl⟩ : syracuseStep 470353 = 352765) B352765
theorem B470387 : Blo 275825 470387 := bstep (se 1 (by rfl) ⟨352790, by rfl⟩ : syracuseStep 470387 = 705581) B705581
theorem B699779 : Blo 275825 699779 := bstep (se 1 (by rfl) ⟨524834, by rfl⟩ : syracuseStep 699779 = 1049669) B1049669
theorem B470515 : Blo 275825 470515 := bstep (se 1 (by rfl) ⟨352886, by rfl⟩ : syracuseStep 470515 = 705773) B705773
theorem B470657 : Blo 275825 470657 := bstep (se 2 (by rfl) ⟨176496, by rfl⟩ : syracuseStep 470657 = 352993) B352993
theorem B470785 : Blo 275825 470785 := bstep (se 2 (by rfl) ⟨176544, by rfl⟩ : syracuseStep 470785 = 353089) B353089
theorem B470819 : Blo 275825 470819 := bstep (se 1 (by rfl) ⟨353114, by rfl⟩ : syracuseStep 470819 = 706229) B706229
theorem B1191779 : Blo 275825 1191779 := bstep (se 1 (by rfl) ⟨893834, by rfl⟩ : syracuseStep 1191779 = 1787669) B1787669
theorem B4599665 : Blo 275825 4599665 := bstep (se 2 (by rfl) ⟨1724874, by rfl⟩ : syracuseStep 4599665 = 3449749) B3449749
theorem B470947 : Blo 275825 470947 := bstep (se 1 (by rfl) ⟨353210, by rfl⟩ : syracuseStep 470947 = 706421) B706421
theorem B2142179 : Blo 275825 2142179 := bstep (se 1 (by rfl) ⟨1606634, by rfl⟩ : syracuseStep 2142179 = 3213269) B3213269
theorem B1060877 : Blo 275825 1060877 := bstep (se 3 (by rfl) ⟨198914, by rfl⟩ : syracuseStep 1060877 = 397829) B397829
theorem B471089 : Blo 275825 471089 := bstep (se 2 (by rfl) ⟨176658, by rfl⟩ : syracuseStep 471089 = 353317) B353317
theorem B471217 : Blo 275825 471217 := bstep (se 2 (by rfl) ⟨176706, by rfl⟩ : syracuseStep 471217 = 353413) B353413
theorem B471251 : Blo 275825 471251 := bstep (se 1 (by rfl) ⟨353438, by rfl⟩ : syracuseStep 471251 = 706877) B706877
theorem B700721 : Blo 275825 700721 := bstep (se 2 (by rfl) ⟨262770, by rfl⟩ : syracuseStep 700721 = 525541) B525541
theorem B373043 : Blo 275825 373043 := bstep (se 1 (by rfl) ⟨279782, by rfl⟩ : syracuseStep 373043 = 559565) B559565
theorem B471379 : Blo 275825 471379 := bstep (se 1 (by rfl) ⟨353534, by rfl⟩ : syracuseStep 471379 = 707069) B707069
theorem B700771 : Blo 275825 700771 := bstep (se 1 (by rfl) ⟨525578, by rfl⟩ : syracuseStep 700771 = 1051157) B1051157
theorem B2404721 : Blo 275825 2404721 := bstep (se 2 (by rfl) ⟨901770, by rfl⟩ : syracuseStep 2404721 = 1803541) B1803541
theorem B471521 : Blo 275825 471521 := bstep (se 2 (by rfl) ⟨176820, by rfl⟩ : syracuseStep 471521 = 353641) B353641
theorem B700913 : Blo 275825 700913 := bstep (se 2 (by rfl) ⟨262842, by rfl⟩ : syracuseStep 700913 = 525685) B525685
theorem B471649 : Blo 275825 471649 := bstep (se 2 (by rfl) ⟨176868, by rfl⟩ : syracuseStep 471649 = 353737) B353737
theorem B471683 : Blo 275825 471683 := bstep (se 1 (by rfl) ⟨353762, by rfl⟩ : syracuseStep 471683 = 707525) B707525
theorem B471811 : Blo 275825 471811 := bstep (se 1 (by rfl) ⟨353858, by rfl⟩ : syracuseStep 471811 = 707717) B707717
theorem B471953 : Blo 275825 471953 := bstep (se 2 (by rfl) ⟨176982, by rfl⟩ : syracuseStep 471953 = 353965) B353965
theorem B472081 : Blo 275825 472081 := bstep (se 2 (by rfl) ⟨177030, by rfl⟩ : syracuseStep 472081 = 354061) B354061
theorem B472115 : Blo 275825 472115 := bstep (se 1 (by rfl) ⟨354086, by rfl⟩ : syracuseStep 472115 = 708173) B708173
theorem B373843 : Blo 275825 373843 := bstep (se 1 (by rfl) ⟨280382, by rfl⟩ : syracuseStep 373843 = 560765) B560765
theorem B2700485 : Blo 275825 2700485 := bstep (se 4 (by rfl) ⟨253170, by rfl⟩ : syracuseStep 2700485 = 506341) B506341
theorem B3880163 : Blo 275825 3880163 := bstep (se 1 (by rfl) ⟨2910122, by rfl⟩ : syracuseStep 3880163 = 5820245) B5820245
theorem B931121 : Blo 275825 931121 := bstep (se 2 (by rfl) ⟨349170, by rfl⟩ : syracuseStep 931121 = 698341) B698341
theorem B2012485 : Blo 275825 2012485 := bstep (se 4 (by rfl) ⟨188670, by rfl⟩ : syracuseStep 2012485 = 377341) B377341
theorem B275827 : Blo 275825 275827 := bstep (se 1 (by rfl) ⟨206870, by rfl⟩ : syracuseStep 275827 = 413741) B413741
theorem B275843 : Blo 275825 275843 := bstep (se 1 (by rfl) ⟨206882, by rfl⟩ : syracuseStep 275843 = 413765) B413765
theorem B275859 : Blo 275825 275859 := bstep (se 1 (by rfl) ⟨206894, by rfl⟩ : syracuseStep 275859 = 413789) B413789
theorem B275875 : Blo 275825 275875 := bstep (se 1 (by rfl) ⟨206906, by rfl⟩ : syracuseStep 275875 = 413813) B413813
theorem B275891 : Blo 275825 275891 := bstep (se 1 (by rfl) ⟨206918, by rfl⟩ : syracuseStep 275891 = 413837) B413837
theorem B275907 : Blo 275825 275907 := bstep (se 1 (by rfl) ⟨206930, by rfl⟩ : syracuseStep 275907 = 413861) B413861
theorem B701905 : Blo 275825 701905 := bstep (se 2 (by rfl) ⟨263214, by rfl⟩ : syracuseStep 701905 = 526429) B526429
theorem B275923 : Blo 275825 275923 := bstep (se 1 (by rfl) ⟨206942, by rfl⟩ : syracuseStep 275923 = 413885) B413885
theorem B275939 : Blo 275825 275939 := bstep (se 1 (by rfl) ⟨206954, by rfl⟩ : syracuseStep 275939 = 413909) B413909
theorem B275955 : Blo 275825 275955 := bstep (se 1 (by rfl) ⟨206966, by rfl⟩ : syracuseStep 275955 = 413933) B413933
theorem B275971 : Blo 275825 275971 := bstep (se 1 (by rfl) ⟨206978, by rfl⟩ : syracuseStep 275971 = 413957) B413957
theorem B3552781 : Blo 275825 3552781 := bstep (se 3 (by rfl) ⟨666146, by rfl⟩ : syracuseStep 3552781 = 1332293) B1332293
theorem B275987 : Blo 275825 275987 := bstep (se 1 (by rfl) ⟨206990, by rfl⟩ : syracuseStep 275987 = 413981) B413981
theorem B276003 : Blo 275825 276003 := bstep (se 1 (by rfl) ⟨207002, by rfl⟩ : syracuseStep 276003 = 414005) B414005
theorem B276019 : Blo 275825 276019 := bstep (se 1 (by rfl) ⟨207014, by rfl⟩ : syracuseStep 276019 = 414029) B414029
theorem B276035 : Blo 275825 276035 := bstep (se 1 (by rfl) ⟨207026, by rfl⟩ : syracuseStep 276035 = 414053) B414053
theorem B3782213 : Blo 275825 3782213 := bstep (se 4 (by rfl) ⟨354582, by rfl⟩ : syracuseStep 3782213 = 709165) B709165
theorem B276051 : Blo 275825 276051 := bstep (se 1 (by rfl) ⟨207038, by rfl⟩ : syracuseStep 276051 = 414077) B414077
theorem B276067 : Blo 275825 276067 := bstep (se 1 (by rfl) ⟨207050, by rfl⟩ : syracuseStep 276067 = 414101) B414101
theorem B276083 : Blo 275825 276083 := bstep (se 1 (by rfl) ⟨207062, by rfl⟩ : syracuseStep 276083 = 414125) B414125
theorem B276099 : Blo 275825 276099 := bstep (se 1 (by rfl) ⟨207074, by rfl⟩ : syracuseStep 276099 = 414149) B414149
theorem B276115 : Blo 275825 276115 := bstep (se 1 (by rfl) ⟨207086, by rfl⟩ : syracuseStep 276115 = 414173) B414173
theorem B276131 : Blo 275825 276131 := bstep (se 1 (by rfl) ⟨207098, by rfl⟩ : syracuseStep 276131 = 414197) B414197
theorem B276147 : Blo 275825 276147 := bstep (se 1 (by rfl) ⟨207110, by rfl⟩ : syracuseStep 276147 = 414221) B414221
theorem B276163 : Blo 275825 276163 := bstep (se 1 (by rfl) ⟨207122, by rfl⟩ : syracuseStep 276163 = 414245) B414245
theorem B276179 : Blo 275825 276179 := bstep (se 1 (by rfl) ⟨207134, by rfl⟩ : syracuseStep 276179 = 414269) B414269
theorem B276195 : Blo 275825 276195 := bstep (se 1 (by rfl) ⟨207146, by rfl⟩ : syracuseStep 276195 = 414293) B414293
theorem B702179 : Blo 275825 702179 := bstep (se 1 (by rfl) ⟨526634, by rfl⟩ : syracuseStep 702179 = 1053269) B1053269
theorem B276211 : Blo 275825 276211 := bstep (se 1 (by rfl) ⟨207158, by rfl⟩ : syracuseStep 276211 = 414317) B414317
theorem B276227 : Blo 275825 276227 := bstep (se 1 (by rfl) ⟨207170, by rfl⟩ : syracuseStep 276227 = 414341) B414341
theorem B276243 : Blo 275825 276243 := bstep (se 1 (by rfl) ⟨207182, by rfl⟩ : syracuseStep 276243 = 414365) B414365
theorem B276259 : Blo 275825 276259 := bstep (se 1 (by rfl) ⟨207194, by rfl⟩ : syracuseStep 276259 = 414389) B414389
theorem B276275 : Blo 275825 276275 := bstep (se 1 (by rfl) ⟨207206, by rfl⟩ : syracuseStep 276275 = 414413) B414413
theorem B276291 : Blo 275825 276291 := bstep (se 1 (by rfl) ⟨207218, by rfl⟩ : syracuseStep 276291 = 414437) B414437
theorem B931661 : Blo 275825 931661 := bstep (se 3 (by rfl) ⟨174686, by rfl⟩ : syracuseStep 931661 = 349373) B349373
theorem B276307 : Blo 275825 276307 := bstep (se 1 (by rfl) ⟨207230, by rfl⟩ : syracuseStep 276307 = 414461) B414461
theorem B276323 : Blo 275825 276323 := bstep (se 1 (by rfl) ⟨207242, by rfl⟩ : syracuseStep 276323 = 414485) B414485
theorem B276339 : Blo 275825 276339 := bstep (se 1 (by rfl) ⟨207254, by rfl⟩ : syracuseStep 276339 = 414509) B414509
theorem B931715 : Blo 275825 931715 := bstep (se 1 (by rfl) ⟨698786, by rfl⟩ : syracuseStep 931715 = 1397573) B1397573
theorem B276355 : Blo 275825 276355 := bstep (se 1 (by rfl) ⟨207266, by rfl⟩ : syracuseStep 276355 = 414533) B414533
theorem B276371 : Blo 275825 276371 := bstep (se 1 (by rfl) ⟨207278, by rfl⟩ : syracuseStep 276371 = 414557) B414557
theorem B276387 : Blo 275825 276387 := bstep (se 1 (by rfl) ⟨207290, by rfl⟩ : syracuseStep 276387 = 414581) B414581
theorem B702371 : Blo 275825 702371 := bstep (se 1 (by rfl) ⟨526778, by rfl⟩ : syracuseStep 702371 = 1053557) B1053557
theorem B276403 : Blo 275825 276403 := bstep (se 1 (by rfl) ⟨207302, by rfl⟩ : syracuseStep 276403 = 414605) B414605
theorem B276419 : Blo 275825 276419 := bstep (se 1 (by rfl) ⟨207314, by rfl⟩ : syracuseStep 276419 = 414629) B414629
theorem B276435 : Blo 275825 276435 := bstep (se 1 (by rfl) ⟨207326, by rfl⟩ : syracuseStep 276435 = 414653) B414653
theorem B276451 : Blo 275825 276451 := bstep (se 1 (by rfl) ⟨207338, by rfl⟩ : syracuseStep 276451 = 414677) B414677
theorem B276467 : Blo 275825 276467 := bstep (se 1 (by rfl) ⟨207350, by rfl⟩ : syracuseStep 276467 = 414701) B414701
theorem B276483 : Blo 275825 276483 := bstep (se 1 (by rfl) ⟨207362, by rfl⟩ : syracuseStep 276483 = 414725) B414725
theorem B276499 : Blo 275825 276499 := bstep (se 1 (by rfl) ⟨207374, by rfl⟩ : syracuseStep 276499 = 414749) B414749
theorem B276515 : Blo 275825 276515 := bstep (se 1 (by rfl) ⟨207386, by rfl⟩ : syracuseStep 276515 = 414773) B414773
theorem B276531 : Blo 275825 276531 := bstep (se 1 (by rfl) ⟨207398, by rfl⟩ : syracuseStep 276531 = 414797) B414797
theorem B276547 : Blo 275825 276547 := bstep (se 1 (by rfl) ⟨207410, by rfl⟩ : syracuseStep 276547 = 414821) B414821
theorem B276563 : Blo 275825 276563 := bstep (se 1 (by rfl) ⟨207422, by rfl⟩ : syracuseStep 276563 = 414845) B414845
theorem B276579 : Blo 275825 276579 := bstep (se 1 (by rfl) ⟨207434, by rfl⟩ : syracuseStep 276579 = 414869) B414869
theorem B276595 : Blo 275825 276595 := bstep (se 1 (by rfl) ⟨207446, by rfl⟩ : syracuseStep 276595 = 414893) B414893
theorem B276611 : Blo 275825 276611 := bstep (se 1 (by rfl) ⟨207458, by rfl⟩ : syracuseStep 276611 = 414917) B414917
theorem B931985 : Blo 275825 931985 := bstep (se 2 (by rfl) ⟨349494, by rfl⟩ : syracuseStep 931985 = 698989) B698989
theorem B276627 : Blo 275825 276627 := bstep (se 1 (by rfl) ⟨207470, by rfl⟩ : syracuseStep 276627 = 414941) B414941
theorem B276643 : Blo 275825 276643 := bstep (se 1 (by rfl) ⟨207482, by rfl⟩ : syracuseStep 276643 = 414965) B414965
theorem B276659 : Blo 275825 276659 := bstep (se 1 (by rfl) ⟨207494, by rfl⟩ : syracuseStep 276659 = 414989) B414989
theorem B276675 : Blo 275825 276675 := bstep (se 1 (by rfl) ⟨207506, by rfl⟩ : syracuseStep 276675 = 415013) B415013
theorem B1587397 : Blo 275825 1587397 := bstep (se 4 (by rfl) ⟨148818, by rfl⟩ : syracuseStep 1587397 = 297637) B297637
theorem B1128653 : Blo 275825 1128653 := bstep (se 3 (by rfl) ⟨211622, by rfl⟩ : syracuseStep 1128653 = 423245) B423245
theorem B276691 : Blo 275825 276691 := bstep (se 1 (by rfl) ⟨207518, by rfl⟩ : syracuseStep 276691 = 415037) B415037
theorem B276707 : Blo 275825 276707 := bstep (se 1 (by rfl) ⟨207530, by rfl⟩ : syracuseStep 276707 = 415061) B415061
theorem B276723 : Blo 275825 276723 := bstep (se 1 (by rfl) ⟨207542, by rfl⟩ : syracuseStep 276723 = 415085) B415085
theorem B276739 : Blo 275825 276739 := bstep (se 1 (by rfl) ⟨207554, by rfl⟩ : syracuseStep 276739 = 415109) B415109
theorem B276755 : Blo 275825 276755 := bstep (se 1 (by rfl) ⟨207566, by rfl⟩ : syracuseStep 276755 = 415133) B415133
theorem B276771 : Blo 275825 276771 := bstep (se 1 (by rfl) ⟨207578, by rfl⟩ : syracuseStep 276771 = 415157) B415157
theorem B276787 : Blo 275825 276787 := bstep (se 1 (by rfl) ⟨207590, by rfl⟩ : syracuseStep 276787 = 415181) B415181
theorem B276803 : Blo 275825 276803 := bstep (se 1 (by rfl) ⟨207602, by rfl⟩ : syracuseStep 276803 = 415205) B415205
theorem B276819 : Blo 275825 276819 := bstep (se 1 (by rfl) ⟨207614, by rfl⟩ : syracuseStep 276819 = 415229) B415229
theorem B276835 : Blo 275825 276835 := bstep (se 1 (by rfl) ⟨207626, by rfl⟩ : syracuseStep 276835 = 415253) B415253
theorem B637283 : Blo 275825 637283 := bstep (se 1 (by rfl) ⟨477962, by rfl⟩ : syracuseStep 637283 = 955925) B955925
theorem B964973 : Blo 275825 964973 := bstep (se 3 (by rfl) ⟨180932, by rfl⟩ : syracuseStep 964973 = 361865) B361865
theorem B276851 : Blo 275825 276851 := bstep (se 1 (by rfl) ⟨207638, by rfl⟩ : syracuseStep 276851 = 415277) B415277
theorem B276867 : Blo 275825 276867 := bstep (se 1 (by rfl) ⟨207650, by rfl⟩ : syracuseStep 276867 = 415301) B415301
theorem B276883 : Blo 275825 276883 := bstep (se 1 (by rfl) ⟨207662, by rfl⟩ : syracuseStep 276883 = 415325) B415325
theorem B276899 : Blo 275825 276899 := bstep (se 1 (by rfl) ⟨207674, by rfl⟩ : syracuseStep 276899 = 415349) B415349
theorem B276915 : Blo 275825 276915 := bstep (se 1 (by rfl) ⟨207686, by rfl⟩ : syracuseStep 276915 = 415373) B415373
theorem B276931 : Blo 275825 276931 := bstep (se 1 (by rfl) ⟨207698, by rfl⟩ : syracuseStep 276931 = 415397) B415397
theorem B276947 : Blo 275825 276947 := bstep (se 1 (by rfl) ⟨207710, by rfl⟩ : syracuseStep 276947 = 415421) B415421
theorem B276963 : Blo 275825 276963 := bstep (se 1 (by rfl) ⟨207722, by rfl⟩ : syracuseStep 276963 = 415445) B415445
theorem B276979 : Blo 275825 276979 := bstep (se 1 (by rfl) ⟨207734, by rfl⟩ : syracuseStep 276979 = 415469) B415469
theorem B276995 : Blo 275825 276995 := bstep (se 1 (by rfl) ⟨207746, by rfl⟩ : syracuseStep 276995 = 415493) B415493
theorem B277011 : Blo 275825 277011 := bstep (se 1 (by rfl) ⟨207758, by rfl⟩ : syracuseStep 277011 = 415517) B415517
theorem B277027 : Blo 275825 277027 := bstep (se 1 (by rfl) ⟨207770, by rfl⟩ : syracuseStep 277027 = 415541) B415541
theorem B277043 : Blo 275825 277043 := bstep (se 1 (by rfl) ⟨207782, by rfl⟩ : syracuseStep 277043 = 415565) B415565
theorem B277059 : Blo 275825 277059 := bstep (se 1 (by rfl) ⟨207794, by rfl⟩ : syracuseStep 277059 = 415589) B415589
theorem B277075 : Blo 275825 277075 := bstep (se 1 (by rfl) ⟨207806, by rfl⟩ : syracuseStep 277075 = 415613) B415613
theorem B277091 : Blo 275825 277091 := bstep (se 1 (by rfl) ⟨207818, by rfl⟩ : syracuseStep 277091 = 415637) B415637
theorem B277107 : Blo 275825 277107 := bstep (se 1 (by rfl) ⟨207830, by rfl⟩ : syracuseStep 277107 = 415661) B415661
theorem B277123 : Blo 275825 277123 := bstep (se 1 (by rfl) ⟨207842, by rfl⟩ : syracuseStep 277123 = 415685) B415685
theorem B277139 : Blo 275825 277139 := bstep (se 1 (by rfl) ⟨207854, by rfl⟩ : syracuseStep 277139 = 415709) B415709
theorem B277155 : Blo 275825 277155 := bstep (se 1 (by rfl) ⟨207866, by rfl⟩ : syracuseStep 277155 = 415733) B415733
theorem B932525 : Blo 275825 932525 := bstep (se 3 (by rfl) ⟨174848, by rfl⟩ : syracuseStep 932525 = 349697) B349697
theorem B277171 : Blo 275825 277171 := bstep (se 1 (by rfl) ⟨207878, by rfl⟩ : syracuseStep 277171 = 415757) B415757
theorem B277187 : Blo 275825 277187 := bstep (se 1 (by rfl) ⟨207890, by rfl⟩ : syracuseStep 277187 = 415781) B415781
theorem B277203 : Blo 275825 277203 := bstep (se 1 (by rfl) ⟨207902, by rfl⟩ : syracuseStep 277203 = 415805) B415805
theorem B932579 : Blo 275825 932579 := bstep (se 1 (by rfl) ⟨699434, by rfl⟩ : syracuseStep 932579 = 1398869) B1398869
theorem B277219 : Blo 275825 277219 := bstep (se 1 (by rfl) ⟨207914, by rfl⟩ : syracuseStep 277219 = 415829) B415829
theorem B277235 : Blo 275825 277235 := bstep (se 1 (by rfl) ⟨207926, by rfl⟩ : syracuseStep 277235 = 415853) B415853
theorem B277251 : Blo 275825 277251 := bstep (se 1 (by rfl) ⟨207938, by rfl⟩ : syracuseStep 277251 = 415877) B415877
theorem B277267 : Blo 275825 277267 := bstep (se 1 (by rfl) ⟨207950, by rfl⟩ : syracuseStep 277267 = 415901) B415901
theorem B277283 : Blo 275825 277283 := bstep (se 1 (by rfl) ⟨207962, by rfl⟩ : syracuseStep 277283 = 415925) B415925
theorem B277299 : Blo 275825 277299 := bstep (se 1 (by rfl) ⟨207974, by rfl⟩ : syracuseStep 277299 = 415949) B415949
theorem B277315 : Blo 275825 277315 := bstep (se 1 (by rfl) ⟨207986, by rfl⟩ : syracuseStep 277315 = 415973) B415973
theorem B3554117 : Blo 275825 3554117 := bstep (se 4 (by rfl) ⟨333198, by rfl⟩ : syracuseStep 3554117 = 666397) B666397
theorem B703313 : Blo 275825 703313 := bstep (se 2 (by rfl) ⟨263742, by rfl⟩ : syracuseStep 703313 = 527485) B527485
theorem B277331 : Blo 275825 277331 := bstep (se 1 (by rfl) ⟨207998, by rfl⟩ : syracuseStep 277331 = 415997) B415997
theorem B277347 : Blo 275825 277347 := bstep (se 1 (by rfl) ⟨208010, by rfl⟩ : syracuseStep 277347 = 416021) B416021
theorem B277363 : Blo 275825 277363 := bstep (se 1 (by rfl) ⟨208022, by rfl⟩ : syracuseStep 277363 = 416045) B416045
theorem B277379 : Blo 275825 277379 := bstep (se 1 (by rfl) ⟨208034, by rfl⟩ : syracuseStep 277379 = 416069) B416069
theorem B703363 : Blo 275825 703363 := bstep (se 1 (by rfl) ⟨527522, by rfl⟩ : syracuseStep 703363 = 1055045) B1055045
theorem B277395 : Blo 275825 277395 := bstep (se 1 (by rfl) ⟨208046, by rfl⟩ : syracuseStep 277395 = 416093) B416093
theorem B277411 : Blo 275825 277411 := bstep (se 1 (by rfl) ⟨208058, by rfl⟩ : syracuseStep 277411 = 416117) B416117
theorem B277427 : Blo 275825 277427 := bstep (se 1 (by rfl) ⟨208070, by rfl⟩ : syracuseStep 277427 = 416141) B416141
theorem B277443 : Blo 275825 277443 := bstep (se 1 (by rfl) ⟨208082, by rfl⟩ : syracuseStep 277443 = 416165) B416165
theorem B277459 : Blo 275825 277459 := bstep (se 1 (by rfl) ⟨208094, by rfl⟩ : syracuseStep 277459 = 416189) B416189
theorem B277475 : Blo 275825 277475 := bstep (se 1 (by rfl) ⟨208106, by rfl⟩ : syracuseStep 277475 = 416213) B416213
theorem B932849 : Blo 275825 932849 := bstep (se 2 (by rfl) ⟨349818, by rfl⟩ : syracuseStep 932849 = 699637) B699637
theorem B277491 : Blo 275825 277491 := bstep (se 1 (by rfl) ⟨208118, by rfl⟩ : syracuseStep 277491 = 416237) B416237
theorem B277507 : Blo 275825 277507 := bstep (se 1 (by rfl) ⟨208130, by rfl⟩ : syracuseStep 277507 = 416261) B416261
theorem B703505 : Blo 275825 703505 := bstep (se 2 (by rfl) ⟨263814, by rfl⟩ : syracuseStep 703505 = 527629) B527629
theorem B474131 : Blo 275825 474131 := bstep (se 1 (by rfl) ⟨355598, by rfl⟩ : syracuseStep 474131 = 711197) B711197
theorem B277523 : Blo 275825 277523 := bstep (se 1 (by rfl) ⟨208142, by rfl⟩ : syracuseStep 277523 = 416285) B416285
theorem B277539 : Blo 275825 277539 := bstep (se 1 (by rfl) ⟨208154, by rfl⟩ : syracuseStep 277539 = 416309) B416309
theorem B277555 : Blo 275825 277555 := bstep (se 1 (by rfl) ⟨208166, by rfl⟩ : syracuseStep 277555 = 416333) B416333
theorem B277571 : Blo 275825 277571 := bstep (se 1 (by rfl) ⟨208178, by rfl⟩ : syracuseStep 277571 = 416357) B416357
theorem B277587 : Blo 275825 277587 := bstep (se 1 (by rfl) ⟨208190, by rfl⟩ : syracuseStep 277587 = 416381) B416381
theorem B277603 : Blo 275825 277603 := bstep (se 1 (by rfl) ⟨208202, by rfl⟩ : syracuseStep 277603 = 416405) B416405
theorem B310387 : Blo 275825 310387 := bstep (se 1 (by rfl) ⟨232790, by rfl⟩ : syracuseStep 310387 = 465581) B465581
theorem B277619 : Blo 275825 277619 := bstep (se 1 (by rfl) ⟨208214, by rfl⟩ : syracuseStep 277619 = 416429) B416429
theorem B277635 : Blo 275825 277635 := bstep (se 1 (by rfl) ⟨208226, by rfl⟩ : syracuseStep 277635 = 416453) B416453
theorem B277651 : Blo 275825 277651 := bstep (se 1 (by rfl) ⟨208238, by rfl⟩ : syracuseStep 277651 = 416477) B416477
theorem B277667 : Blo 275825 277667 := bstep (se 1 (by rfl) ⟨208250, by rfl⟩ : syracuseStep 277667 = 416501) B416501
theorem B277683 : Blo 275825 277683 := bstep (se 1 (by rfl) ⟨208262, by rfl⟩ : syracuseStep 277683 = 416525) B416525
theorem B277699 : Blo 275825 277699 := bstep (se 1 (by rfl) ⟨208274, by rfl⟩ : syracuseStep 277699 = 416549) B416549
theorem B277715 : Blo 275825 277715 := bstep (se 1 (by rfl) ⟨208286, by rfl⟩ : syracuseStep 277715 = 416573) B416573
theorem B277731 : Blo 275825 277731 := bstep (se 1 (by rfl) ⟨208298, by rfl⟩ : syracuseStep 277731 = 416597) B416597
theorem B277747 : Blo 275825 277747 := bstep (se 1 (by rfl) ⟨208310, by rfl⟩ : syracuseStep 277747 = 416621) B416621
theorem B310531 : Blo 275825 310531 := bstep (se 1 (by rfl) ⟨232898, by rfl⟩ : syracuseStep 310531 = 465797) B465797
theorem B277763 : Blo 275825 277763 := bstep (se 1 (by rfl) ⟨208322, by rfl⟩ : syracuseStep 277763 = 416645) B416645
theorem B277779 : Blo 275825 277779 := bstep (se 1 (by rfl) ⟨208334, by rfl⟩ : syracuseStep 277779 = 416669) B416669
theorem B277795 : Blo 275825 277795 := bstep (se 1 (by rfl) ⟨208346, by rfl⟩ : syracuseStep 277795 = 416693) B416693
theorem B277811 : Blo 275825 277811 := bstep (se 1 (by rfl) ⟨208358, by rfl⟩ : syracuseStep 277811 = 416717) B416717
theorem B5356853 : Blo 275825 5356853 := bstep (se 5 (by rfl) ⟨251102, by rfl⟩ : syracuseStep 5356853 = 502205) B502205
theorem B277827 : Blo 275825 277827 := bstep (se 1 (by rfl) ⟨208370, by rfl⟩ : syracuseStep 277827 = 416741) B416741
theorem B277843 : Blo 275825 277843 := bstep (se 1 (by rfl) ⟨208382, by rfl⟩ : syracuseStep 277843 = 416765) B416765
theorem B277859 : Blo 275825 277859 := bstep (se 1 (by rfl) ⟨208394, by rfl⟩ : syracuseStep 277859 = 416789) B416789
theorem B277875 : Blo 275825 277875 := bstep (se 1 (by rfl) ⟨208406, by rfl⟩ : syracuseStep 277875 = 416813) B416813
theorem B277891 : Blo 275825 277891 := bstep (se 1 (by rfl) ⟨208418, by rfl⟩ : syracuseStep 277891 = 416837) B416837
theorem B310675 : Blo 275825 310675 := bstep (se 1 (by rfl) ⟨233006, by rfl⟩ : syracuseStep 310675 = 466013) B466013
theorem B277907 : Blo 275825 277907 := bstep (se 1 (by rfl) ⟨208430, by rfl⟩ : syracuseStep 277907 = 416861) B416861
theorem B277923 : Blo 275825 277923 := bstep (se 1 (by rfl) ⟨208442, by rfl⟩ : syracuseStep 277923 = 416885) B416885
theorem B277939 : Blo 275825 277939 := bstep (se 1 (by rfl) ⟨208454, by rfl⟩ : syracuseStep 277939 = 416909) B416909
theorem B277955 : Blo 275825 277955 := bstep (se 1 (by rfl) ⟨208466, by rfl⟩ : syracuseStep 277955 = 416933) B416933
theorem B277971 : Blo 275825 277971 := bstep (se 1 (by rfl) ⟨208478, by rfl⟩ : syracuseStep 277971 = 416957) B416957
theorem B277987 : Blo 275825 277987 := bstep (se 1 (by rfl) ⟨208490, by rfl⟩ : syracuseStep 277987 = 416981) B416981
theorem B278003 : Blo 275825 278003 := bstep (se 1 (by rfl) ⟨208502, by rfl⟩ : syracuseStep 278003 = 417005) B417005
theorem B278019 : Blo 275825 278019 := bstep (se 1 (by rfl) ⟨208514, by rfl⟩ : syracuseStep 278019 = 417029) B417029
theorem B933389 : Blo 275825 933389 := bstep (se 3 (by rfl) ⟨175010, by rfl⟩ : syracuseStep 933389 = 350021) B350021
theorem B278035 : Blo 275825 278035 := bstep (se 1 (by rfl) ⟨208526, by rfl⟩ : syracuseStep 278035 = 417053) B417053
theorem B310819 : Blo 275825 310819 := bstep (se 1 (by rfl) ⟨233114, by rfl⟩ : syracuseStep 310819 = 466229) B466229
theorem B278051 : Blo 275825 278051 := bstep (se 1 (by rfl) ⟨208538, by rfl⟩ : syracuseStep 278051 = 417077) B417077
theorem B278067 : Blo 275825 278067 := bstep (se 1 (by rfl) ⟨208550, by rfl⟩ : syracuseStep 278067 = 417101) B417101
theorem B933443 : Blo 275825 933443 := bstep (se 1 (by rfl) ⟨700082, by rfl⟩ : syracuseStep 933443 = 1400165) B1400165
theorem B278083 : Blo 275825 278083 := bstep (se 1 (by rfl) ⟨208562, by rfl⟩ : syracuseStep 278083 = 417125) B417125
theorem B278099 : Blo 275825 278099 := bstep (se 1 (by rfl) ⟨208574, by rfl⟩ : syracuseStep 278099 = 417149) B417149
theorem B376417 : Blo 275825 376417 := bstep (se 2 (by rfl) ⟨141156, by rfl⟩ : syracuseStep 376417 = 282313) B282313
theorem B278115 : Blo 275825 278115 := bstep (se 1 (by rfl) ⟨208586, by rfl⟩ : syracuseStep 278115 = 417173) B417173
theorem B278131 : Blo 275825 278131 := bstep (se 1 (by rfl) ⟨208598, by rfl⟩ : syracuseStep 278131 = 417197) B417197
theorem B278147 : Blo 275825 278147 := bstep (se 1 (by rfl) ⟨208610, by rfl⟩ : syracuseStep 278147 = 417221) B417221
theorem B278163 : Blo 275825 278163 := bstep (se 1 (by rfl) ⟨208622, by rfl⟩ : syracuseStep 278163 = 417245) B417245
theorem B278179 : Blo 275825 278179 := bstep (se 1 (by rfl) ⟨208634, by rfl⟩ : syracuseStep 278179 = 417269) B417269
theorem B310963 : Blo 275825 310963 := bstep (se 1 (by rfl) ⟨233222, by rfl⟩ : syracuseStep 310963 = 466445) B466445
theorem B278195 : Blo 275825 278195 := bstep (se 1 (by rfl) ⟨208646, by rfl⟩ : syracuseStep 278195 = 417293) B417293
theorem B278211 : Blo 275825 278211 := bstep (se 1 (by rfl) ⟨208658, by rfl⟩ : syracuseStep 278211 = 417317) B417317
theorem B278227 : Blo 275825 278227 := bstep (se 1 (by rfl) ⟨208670, by rfl⟩ : syracuseStep 278227 = 417341) B417341
theorem B278243 : Blo 275825 278243 := bstep (se 1 (by rfl) ⟨208682, by rfl⟩ : syracuseStep 278243 = 417365) B417365
theorem B442099 : Blo 275825 442099 := bstep (se 1 (by rfl) ⟨331574, by rfl⟩ : syracuseStep 442099 = 663149) B663149
theorem B278259 : Blo 275825 278259 := bstep (se 1 (by rfl) ⟨208694, by rfl⟩ : syracuseStep 278259 = 417389) B417389
theorem B278275 : Blo 275825 278275 := bstep (se 1 (by rfl) ⟨208706, by rfl⟩ : syracuseStep 278275 = 417413) B417413
theorem B376579 : Blo 275825 376579 := bstep (se 1 (by rfl) ⟨282434, by rfl⟩ : syracuseStep 376579 = 564869) B564869
theorem B278291 : Blo 275825 278291 := bstep (se 1 (by rfl) ⟨208718, by rfl⟩ : syracuseStep 278291 = 417437) B417437
theorem B278307 : Blo 275825 278307 := bstep (se 1 (by rfl) ⟨208730, by rfl⟩ : syracuseStep 278307 = 417461) B417461
theorem B278323 : Blo 275825 278323 := bstep (se 1 (by rfl) ⟨208742, by rfl⟩ : syracuseStep 278323 = 417485) B417485
theorem B311107 : Blo 275825 311107 := bstep (se 1 (by rfl) ⟨233330, by rfl⟩ : syracuseStep 311107 = 466661) B466661
theorem B278339 : Blo 275825 278339 := bstep (se 1 (by rfl) ⟨208754, by rfl⟩ : syracuseStep 278339 = 417509) B417509
theorem B933713 : Blo 275825 933713 := bstep (se 2 (by rfl) ⟨350142, by rfl⟩ : syracuseStep 933713 = 700285) B700285
theorem B278355 : Blo 275825 278355 := bstep (se 1 (by rfl) ⟨208766, by rfl⟩ : syracuseStep 278355 = 417533) B417533
theorem B278371 : Blo 275825 278371 := bstep (se 1 (by rfl) ⟨208778, by rfl⟩ : syracuseStep 278371 = 417557) B417557
theorem B278387 : Blo 275825 278387 := bstep (se 1 (by rfl) ⟨208790, by rfl⟩ : syracuseStep 278387 = 417581) B417581
theorem B278403 : Blo 275825 278403 := bstep (se 1 (by rfl) ⟨208802, by rfl⟩ : syracuseStep 278403 = 417605) B417605
theorem B278419 : Blo 275825 278419 := bstep (se 1 (by rfl) ⟨208814, by rfl⟩ : syracuseStep 278419 = 417629) B417629
theorem B278435 : Blo 275825 278435 := bstep (se 1 (by rfl) ⟨208826, by rfl⟩ : syracuseStep 278435 = 417653) B417653
theorem B278451 : Blo 275825 278451 := bstep (se 1 (by rfl) ⟨208838, by rfl⟩ : syracuseStep 278451 = 417677) B417677
theorem B278467 : Blo 275825 278467 := bstep (se 1 (by rfl) ⟨208850, by rfl⟩ : syracuseStep 278467 = 417701) B417701
theorem B311251 : Blo 275825 311251 := bstep (se 1 (by rfl) ⟨233438, by rfl⟩ : syracuseStep 311251 = 466877) B466877
theorem B278483 : Blo 275825 278483 := bstep (se 1 (by rfl) ⟨208862, by rfl⟩ : syracuseStep 278483 = 417725) B417725
theorem B278499 : Blo 275825 278499 := bstep (se 1 (by rfl) ⟨208874, by rfl⟩ : syracuseStep 278499 = 417749) B417749
theorem B704497 : Blo 275825 704497 := bstep (se 2 (by rfl) ⟨264186, by rfl⟩ : syracuseStep 704497 = 528373) B528373
theorem B442355 : Blo 275825 442355 := bstep (se 1 (by rfl) ⟨331766, by rfl⟩ : syracuseStep 442355 = 663533) B663533
theorem B278515 : Blo 275825 278515 := bstep (se 1 (by rfl) ⟨208886, by rfl⟩ : syracuseStep 278515 = 417773) B417773
theorem B278531 : Blo 275825 278531 := bstep (se 1 (by rfl) ⟨208898, by rfl⟩ : syracuseStep 278531 = 417797) B417797
theorem B278547 : Blo 275825 278547 := bstep (se 1 (by rfl) ⟨208910, by rfl⟩ : syracuseStep 278547 = 417821) B417821
theorem B278563 : Blo 275825 278563 := bstep (se 1 (by rfl) ⟨208922, by rfl⟩ : syracuseStep 278563 = 417845) B417845
theorem B278579 : Blo 275825 278579 := bstep (se 1 (by rfl) ⟨208934, by rfl⟩ : syracuseStep 278579 = 417869) B417869
theorem B278595 : Blo 275825 278595 := bstep (se 1 (by rfl) ⟨208946, by rfl⟩ : syracuseStep 278595 = 417893) B417893
theorem B278611 : Blo 275825 278611 := bstep (se 1 (by rfl) ⟨208958, by rfl⟩ : syracuseStep 278611 = 417917) B417917
theorem B1065059 : Blo 275825 1065059 := bstep (se 1 (by rfl) ⟨798794, by rfl⟩ : syracuseStep 1065059 = 1597589) B1597589
theorem B311395 : Blo 275825 311395 := bstep (se 1 (by rfl) ⟨233546, by rfl⟩ : syracuseStep 311395 = 467093) B467093
theorem B278627 : Blo 275825 278627 := bstep (se 1 (by rfl) ⟨208970, by rfl⟩ : syracuseStep 278627 = 417941) B417941
theorem B278643 : Blo 275825 278643 := bstep (se 1 (by rfl) ⟨208982, by rfl⟩ : syracuseStep 278643 = 417965) B417965
theorem B278659 : Blo 275825 278659 := bstep (se 1 (by rfl) ⟨208994, by rfl⟩ : syracuseStep 278659 = 417989) B417989
theorem B1589381 : Blo 275825 1589381 := bstep (se 4 (by rfl) ⟨149004, by rfl⟩ : syracuseStep 1589381 = 298009) B298009
theorem B278675 : Blo 275825 278675 := bstep (se 1 (by rfl) ⟨209006, by rfl⟩ : syracuseStep 278675 = 418013) B418013
theorem B278691 : Blo 275825 278691 := bstep (se 1 (by rfl) ⟨209018, by rfl⟩ : syracuseStep 278691 = 418037) B418037
theorem B278707 : Blo 275825 278707 := bstep (se 1 (by rfl) ⟨209030, by rfl⟩ : syracuseStep 278707 = 418061) B418061
theorem B278723 : Blo 275825 278723 := bstep (se 1 (by rfl) ⟨209042, by rfl⟩ : syracuseStep 278723 = 418085) B418085
theorem B278739 : Blo 275825 278739 := bstep (se 1 (by rfl) ⟨209054, by rfl⟩ : syracuseStep 278739 = 418109) B418109
theorem B8110307 : Blo 275825 8110307 := bstep (se 1 (by rfl) ⟨6082730, by rfl⟩ : syracuseStep 8110307 = 12165461) B12165461
theorem B278755 : Blo 275825 278755 := bstep (se 1 (by rfl) ⟨209066, by rfl⟩ : syracuseStep 278755 = 418133) B418133
theorem B311539 : Blo 275825 311539 := bstep (se 1 (by rfl) ⟨233654, by rfl⟩ : syracuseStep 311539 = 467309) B467309
theorem B278771 : Blo 275825 278771 := bstep (se 1 (by rfl) ⟨209078, by rfl⟩ : syracuseStep 278771 = 418157) B418157
theorem B704771 : Blo 275825 704771 := bstep (se 1 (by rfl) ⟨528578, by rfl⟩ : syracuseStep 704771 = 1057157) B1057157
theorem B278787 : Blo 275825 278787 := bstep (se 1 (by rfl) ⟨209090, by rfl⟩ : syracuseStep 278787 = 418181) B418181
theorem B278803 : Blo 275825 278803 := bstep (se 1 (by rfl) ⟨209102, by rfl⟩ : syracuseStep 278803 = 418205) B418205
theorem B278819 : Blo 275825 278819 := bstep (se 1 (by rfl) ⟨209114, by rfl⟩ : syracuseStep 278819 = 418229) B418229
theorem B278835 : Blo 275825 278835 := bstep (se 1 (by rfl) ⟨209126, by rfl⟩ : syracuseStep 278835 = 418253) B418253
theorem B278851 : Blo 275825 278851 := bstep (se 1 (by rfl) ⟨209138, by rfl⟩ : syracuseStep 278851 = 418277) B418277
theorem B672067 : Blo 275825 672067 := bstep (se 1 (by rfl) ⟨504050, by rfl⟩ : syracuseStep 672067 = 1008101) B1008101
theorem B278867 : Blo 275825 278867 := bstep (se 1 (by rfl) ⟨209150, by rfl⟩ : syracuseStep 278867 = 418301) B418301
theorem B1786211 : Blo 275825 1786211 := bstep (se 1 (by rfl) ⟨1339658, by rfl⟩ : syracuseStep 1786211 = 2679317) B2679317
theorem B278883 : Blo 275825 278883 := bstep (se 1 (by rfl) ⟨209162, by rfl⟩ : syracuseStep 278883 = 418325) B418325
theorem B934253 : Blo 275825 934253 := bstep (se 3 (by rfl) ⟨175172, by rfl⟩ : syracuseStep 934253 = 350345) B350345
theorem B278899 : Blo 275825 278899 := bstep (se 1 (by rfl) ⟨209174, by rfl⟩ : syracuseStep 278899 = 418349) B418349
theorem B311683 : Blo 275825 311683 := bstep (se 1 (by rfl) ⟨233762, by rfl⟩ : syracuseStep 311683 = 467525) B467525
theorem B278915 : Blo 275825 278915 := bstep (se 1 (by rfl) ⟨209186, by rfl⟩ : syracuseStep 278915 = 418373) B418373
theorem B278931 : Blo 275825 278931 := bstep (se 1 (by rfl) ⟨209198, by rfl⟩ : syracuseStep 278931 = 418397) B418397
theorem B475553 : Blo 275825 475553 := bstep (se 2 (by rfl) ⟨178332, by rfl⟩ : syracuseStep 475553 = 356665) B356665
theorem B934307 : Blo 275825 934307 := bstep (se 1 (by rfl) ⟨700730, by rfl⟩ : syracuseStep 934307 = 1401461) B1401461
theorem B278947 : Blo 275825 278947 := bstep (se 1 (by rfl) ⟨209210, by rfl⟩ : syracuseStep 278947 = 418421) B418421
theorem B278963 : Blo 275825 278963 := bstep (se 1 (by rfl) ⟨209222, by rfl⟩ : syracuseStep 278963 = 418445) B418445
theorem B442817 : Blo 275825 442817 := bstep (se 2 (by rfl) ⟨166056, by rfl⟩ : syracuseStep 442817 = 332113) B332113
theorem B704963 : Blo 275825 704963 := bstep (se 1 (by rfl) ⟨528722, by rfl⟩ : syracuseStep 704963 = 1057445) B1057445
theorem B278979 : Blo 275825 278979 := bstep (se 1 (by rfl) ⟨209234, by rfl⟩ : syracuseStep 278979 = 418469) B418469
theorem B278995 : Blo 275825 278995 := bstep (se 1 (by rfl) ⟨209246, by rfl⟩ : syracuseStep 278995 = 418493) B418493
theorem B279011 : Blo 275825 279011 := bstep (se 1 (by rfl) ⟨209258, by rfl⟩ : syracuseStep 279011 = 418517) B418517
theorem B672241 : Blo 275825 672241 := bstep (se 2 (by rfl) ⟨252090, by rfl⟩ : syracuseStep 672241 = 504181) B504181
theorem B279027 : Blo 275825 279027 := bstep (se 1 (by rfl) ⟨209270, by rfl⟩ : syracuseStep 279027 = 418541) B418541
theorem B279043 : Blo 275825 279043 := bstep (se 1 (by rfl) ⟨209282, by rfl⟩ : syracuseStep 279043 = 418565) B418565
theorem B311827 : Blo 275825 311827 := bstep (se 1 (by rfl) ⟨233870, by rfl⟩ : syracuseStep 311827 = 467741) B467741
theorem B279059 : Blo 275825 279059 := bstep (se 1 (by rfl) ⟨209294, by rfl⟩ : syracuseStep 279059 = 418589) B418589
theorem B442913 : Blo 275825 442913 := bstep (se 2 (by rfl) ⟨166092, by rfl⟩ : syracuseStep 442913 = 332185) B332185
theorem B279075 : Blo 275825 279075 := bstep (se 1 (by rfl) ⟨209306, by rfl⟩ : syracuseStep 279075 = 418613) B418613
theorem B279091 : Blo 275825 279091 := bstep (se 1 (by rfl) ⟨209318, by rfl⟩ : syracuseStep 279091 = 418637) B418637
theorem B442945 : Blo 275825 442945 := bstep (se 2 (by rfl) ⟨166104, by rfl⟩ : syracuseStep 442945 = 332209) B332209
theorem B279107 : Blo 275825 279107 := bstep (se 1 (by rfl) ⟨209330, by rfl⟩ : syracuseStep 279107 = 418661) B418661
theorem B279123 : Blo 275825 279123 := bstep (se 1 (by rfl) ⟨209342, by rfl⟩ : syracuseStep 279123 = 418685) B418685
theorem B279139 : Blo 275825 279139 := bstep (se 1 (by rfl) ⟨209354, by rfl⟩ : syracuseStep 279139 = 418709) B418709
theorem B279155 : Blo 275825 279155 := bstep (se 1 (by rfl) ⟨209366, by rfl⟩ : syracuseStep 279155 = 418733) B418733
theorem B279171 : Blo 275825 279171 := bstep (se 1 (by rfl) ⟨209378, by rfl⟩ : syracuseStep 279171 = 418757) B418757
theorem B279187 : Blo 275825 279187 := bstep (se 1 (by rfl) ⟨209390, by rfl⟩ : syracuseStep 279187 = 418781) B418781
theorem B311971 : Blo 275825 311971 := bstep (se 1 (by rfl) ⟨233978, by rfl⟩ : syracuseStep 311971 = 467957) B467957
theorem B279203 : Blo 275825 279203 := bstep (se 1 (by rfl) ⟨209402, by rfl⟩ : syracuseStep 279203 = 418805) B418805
theorem B934577 : Blo 275825 934577 := bstep (se 2 (by rfl) ⟨350466, by rfl⟩ : syracuseStep 934577 = 700933) B700933
theorem B279219 : Blo 275825 279219 := bstep (se 1 (by rfl) ⟨209414, by rfl⟩ : syracuseStep 279219 = 418829) B418829
theorem B279235 : Blo 275825 279235 := bstep (se 1 (by rfl) ⟨209426, by rfl⟩ : syracuseStep 279235 = 418853) B418853
theorem B803537 : Blo 275825 803537 := bstep (se 2 (by rfl) ⟨301326, by rfl⟩ : syracuseStep 803537 = 602653) B602653
theorem B279251 : Blo 275825 279251 := bstep (se 1 (by rfl) ⟨209438, by rfl⟩ : syracuseStep 279251 = 418877) B418877
theorem B279267 : Blo 275825 279267 := bstep (se 1 (by rfl) ⟨209450, by rfl⟩ : syracuseStep 279267 = 418901) B418901
theorem B279283 : Blo 275825 279283 := bstep (se 1 (by rfl) ⟨209462, by rfl⟩ : syracuseStep 279283 = 418925) B418925
theorem B279299 : Blo 275825 279299 := bstep (se 1 (by rfl) ⟨209474, by rfl⟩ : syracuseStep 279299 = 418949) B418949
theorem B279315 : Blo 275825 279315 := bstep (se 1 (by rfl) ⟨209486, by rfl⟩ : syracuseStep 279315 = 418973) B418973
theorem B279331 : Blo 275825 279331 := bstep (se 1 (by rfl) ⟨209498, by rfl⟩ : syracuseStep 279331 = 418997) B418997
theorem B312115 : Blo 275825 312115 := bstep (se 1 (by rfl) ⟨234086, by rfl⟩ : syracuseStep 312115 = 468173) B468173
theorem B279347 : Blo 275825 279347 := bstep (se 1 (by rfl) ⟨209510, by rfl⟩ : syracuseStep 279347 = 419021) B419021
theorem B279363 : Blo 275825 279363 := bstep (se 1 (by rfl) ⟨209522, by rfl⟩ : syracuseStep 279363 = 419045) B419045
theorem B279379 : Blo 275825 279379 := bstep (se 1 (by rfl) ⟨209534, by rfl⟩ : syracuseStep 279379 = 419069) B419069
theorem B279395 : Blo 275825 279395 := bstep (se 1 (by rfl) ⟨209546, by rfl⟩ : syracuseStep 279395 = 419093) B419093
theorem B279411 : Blo 275825 279411 := bstep (se 1 (by rfl) ⟨209558, by rfl⟩ : syracuseStep 279411 = 419117) B419117
theorem B279427 : Blo 275825 279427 := bstep (se 1 (by rfl) ⟨209570, by rfl⟩ : syracuseStep 279427 = 419141) B419141
theorem B279443 : Blo 275825 279443 := bstep (se 1 (by rfl) ⟨209582, by rfl⟩ : syracuseStep 279443 = 419165) B419165
theorem B279459 : Blo 275825 279459 := bstep (se 1 (by rfl) ⟨209594, by rfl⟩ : syracuseStep 279459 = 419189) B419189
theorem B279475 : Blo 275825 279475 := bstep (se 1 (by rfl) ⟨209606, by rfl⟩ : syracuseStep 279475 = 419213) B419213
theorem B377779 : Blo 275825 377779 := bstep (se 1 (by rfl) ⟨283334, by rfl⟩ : syracuseStep 377779 = 566669) B566669
theorem B312259 : Blo 275825 312259 := bstep (se 1 (by rfl) ⟨234194, by rfl⟩ : syracuseStep 312259 = 468389) B468389
theorem B279491 : Blo 275825 279491 := bstep (se 1 (by rfl) ⟨209618, by rfl⟩ : syracuseStep 279491 = 419237) B419237
theorem B279507 : Blo 275825 279507 := bstep (se 1 (by rfl) ⟨209630, by rfl⟩ : syracuseStep 279507 = 419261) B419261
theorem B279523 : Blo 275825 279523 := bstep (se 1 (by rfl) ⟨209642, by rfl⟩ : syracuseStep 279523 = 419285) B419285
theorem B279539 : Blo 275825 279539 := bstep (se 1 (by rfl) ⟨209654, by rfl⟩ : syracuseStep 279539 = 419309) B419309
theorem B279555 : Blo 275825 279555 := bstep (se 1 (by rfl) ⟨209666, by rfl⟩ : syracuseStep 279555 = 419333) B419333
theorem B279571 : Blo 275825 279571 := bstep (se 1 (by rfl) ⟨209678, by rfl⟩ : syracuseStep 279571 = 419357) B419357
theorem B279587 : Blo 275825 279587 := bstep (se 1 (by rfl) ⟨209690, by rfl⟩ : syracuseStep 279587 = 419381) B419381
theorem B279603 : Blo 275825 279603 := bstep (se 1 (by rfl) ⟨209702, by rfl⟩ : syracuseStep 279603 = 419405) B419405
theorem B279619 : Blo 275825 279619 := bstep (se 1 (by rfl) ⟨209714, by rfl⟩ : syracuseStep 279619 = 419429) B419429
theorem B312403 : Blo 275825 312403 := bstep (se 1 (by rfl) ⟨234302, by rfl⟩ : syracuseStep 312403 = 468605) B468605
theorem B279635 : Blo 275825 279635 := bstep (se 1 (by rfl) ⟨209726, by rfl⟩ : syracuseStep 279635 = 419453) B419453
theorem B279651 : Blo 275825 279651 := bstep (se 1 (by rfl) ⟨209738, by rfl⟩ : syracuseStep 279651 = 419477) B419477
theorem B279667 : Blo 275825 279667 := bstep (se 1 (by rfl) ⟨209750, by rfl⟩ : syracuseStep 279667 = 419501) B419501
theorem B279683 : Blo 275825 279683 := bstep (se 1 (by rfl) ⟨209762, by rfl⟩ : syracuseStep 279683 = 419525) B419525
theorem B279699 : Blo 275825 279699 := bstep (se 1 (by rfl) ⟨209774, by rfl⟩ : syracuseStep 279699 = 419549) B419549
theorem B279715 : Blo 275825 279715 := bstep (se 1 (by rfl) ⟨209786, by rfl⟩ : syracuseStep 279715 = 419573) B419573
theorem B279731 : Blo 275825 279731 := bstep (se 1 (by rfl) ⟨209798, by rfl⟩ : syracuseStep 279731 = 419597) B419597
theorem B279747 : Blo 275825 279747 := bstep (se 1 (by rfl) ⟨209810, by rfl⟩ : syracuseStep 279747 = 419621) B419621
theorem B935117 : Blo 275825 935117 := bstep (se 3 (by rfl) ⟨175334, by rfl⟩ : syracuseStep 935117 = 350669) B350669
theorem B279763 : Blo 275825 279763 := bstep (se 1 (by rfl) ⟨209822, by rfl⟩ : syracuseStep 279763 = 419645) B419645
theorem B312547 : Blo 275825 312547 := bstep (se 1 (by rfl) ⟨234410, by rfl⟩ : syracuseStep 312547 = 468821) B468821
theorem B279779 : Blo 275825 279779 := bstep (se 1 (by rfl) ⟨209834, by rfl⟩ : syracuseStep 279779 = 419669) B419669
theorem B279795 : Blo 275825 279795 := bstep (se 1 (by rfl) ⟨209846, by rfl⟩ : syracuseStep 279795 = 419693) B419693
theorem B935171 : Blo 275825 935171 := bstep (se 1 (by rfl) ⟨701378, by rfl⟩ : syracuseStep 935171 = 1402757) B1402757
theorem B279811 : Blo 275825 279811 := bstep (se 1 (by rfl) ⟨209858, by rfl⟩ : syracuseStep 279811 = 419717) B419717
theorem B705905 : Blo 275825 705905 := bstep (se 2 (by rfl) ⟨264714, by rfl⟩ : syracuseStep 705905 = 529429) B529429
theorem B312691 : Blo 275825 312691 := bstep (se 1 (by rfl) ⟨234518, by rfl⟩ : syracuseStep 312691 = 469037) B469037
theorem B705955 : Blo 275825 705955 := bstep (se 1 (by rfl) ⟨529466, by rfl⟩ : syracuseStep 705955 = 1058933) B1058933
theorem B312835 : Blo 275825 312835 := bstep (se 1 (by rfl) ⟨234626, by rfl⟩ : syracuseStep 312835 = 469253) B469253
theorem B935441 : Blo 275825 935441 := bstep (se 2 (by rfl) ⟨350790, by rfl⟩ : syracuseStep 935441 = 701581) B701581
theorem B706097 : Blo 275825 706097 := bstep (se 2 (by rfl) ⟨264786, by rfl⟩ : syracuseStep 706097 = 529573) B529573
theorem B312979 : Blo 275825 312979 := bstep (se 1 (by rfl) ⟨234734, by rfl⟩ : syracuseStep 312979 = 469469) B469469
theorem B313123 : Blo 275825 313123 := bstep (se 1 (by rfl) ⟨234842, by rfl⟩ : syracuseStep 313123 = 469685) B469685
theorem B476977 : Blo 275825 476977 := bstep (se 2 (by rfl) ⟨178866, by rfl⟩ : syracuseStep 476977 = 357733) B357733
theorem B378769 : Blo 275825 378769 := bstep (se 2 (by rfl) ⟨142038, by rfl⟩ : syracuseStep 378769 = 284077) B284077
theorem B313267 : Blo 275825 313267 := bstep (se 1 (by rfl) ⟨234950, by rfl⟩ : syracuseStep 313267 = 469901) B469901
theorem B1066979 : Blo 275825 1066979 := bstep (se 1 (by rfl) ⟨800234, by rfl⟩ : syracuseStep 1066979 = 1600469) B1600469
theorem B935981 : Blo 275825 935981 := bstep (se 3 (by rfl) ⟨175496, by rfl⟩ : syracuseStep 935981 = 350993) B350993
theorem B313411 : Blo 275825 313411 := bstep (se 1 (by rfl) ⟨235058, by rfl⟩ : syracuseStep 313411 = 470117) B470117
theorem B936035 : Blo 275825 936035 := bstep (se 1 (by rfl) ⟨702026, by rfl⟩ : syracuseStep 936035 = 1404053) B1404053
theorem B8407153 : Blo 275825 8407153 := bstep (se 2 (by rfl) ⟨3152682, by rfl⟩ : syracuseStep 8407153 = 6305365) B6305365
theorem B444611 : Blo 275825 444611 := bstep (se 1 (by rfl) ⟨333458, by rfl⟩ : syracuseStep 444611 = 666917) B666917
theorem B313555 : Blo 275825 313555 := bstep (se 1 (by rfl) ⟨235166, by rfl⟩ : syracuseStep 313555 = 470333) B470333
theorem B1132849 : Blo 275825 1132849 := bstep (se 2 (by rfl) ⟨424818, by rfl⟩ : syracuseStep 1132849 = 849637) B849637
theorem B313699 : Blo 275825 313699 := bstep (se 1 (by rfl) ⟨235274, by rfl⟩ : syracuseStep 313699 = 470549) B470549
theorem B936305 : Blo 275825 936305 := bstep (se 2 (by rfl) ⟨351114, by rfl⟩ : syracuseStep 936305 = 702229) B702229
theorem B313843 : Blo 275825 313843 := bstep (se 1 (by rfl) ⟨235382, by rfl⟩ : syracuseStep 313843 = 470765) B470765
theorem B707089 : Blo 275825 707089 := bstep (se 2 (by rfl) ⟨265158, by rfl⟩ : syracuseStep 707089 = 530317) B530317
theorem B1264241 : Blo 275825 1264241 := bstep (se 2 (by rfl) ⟨474090, by rfl⟩ : syracuseStep 1264241 = 948181) B948181
theorem B313987 : Blo 275825 313987 := bstep (se 1 (by rfl) ⟨235490, by rfl⟩ : syracuseStep 313987 = 470981) B470981
theorem B445123 : Blo 275825 445123 := bstep (se 1 (by rfl) ⟨333842, by rfl⟩ : syracuseStep 445123 = 667685) B667685
theorem B445169 : Blo 275825 445169 := bstep (se 2 (by rfl) ⟨166938, by rfl⟩ : syracuseStep 445169 = 333877) B333877
theorem B314131 : Blo 275825 314131 := bstep (se 1 (by rfl) ⟨235598, by rfl⟩ : syracuseStep 314131 = 471197) B471197
theorem B707363 : Blo 275825 707363 := bstep (se 1 (by rfl) ⟨530522, by rfl⟩ : syracuseStep 707363 = 1061045) B1061045
theorem B936845 : Blo 275825 936845 := bstep (se 3 (by rfl) ⟨175658, by rfl⟩ : syracuseStep 936845 = 351317) B351317
theorem B314275 : Blo 275825 314275 := bstep (se 1 (by rfl) ⟨235706, by rfl⟩ : syracuseStep 314275 = 471413) B471413
theorem B936899 : Blo 275825 936899 := bstep (se 1 (by rfl) ⟨702674, by rfl⟩ : syracuseStep 936899 = 1405349) B1405349
theorem B707555 : Blo 275825 707555 := bstep (se 1 (by rfl) ⟨530666, by rfl⟩ : syracuseStep 707555 = 1061333) B1061333
theorem B314419 : Blo 275825 314419 := bstep (se 1 (by rfl) ⟨235814, by rfl⟩ : syracuseStep 314419 = 471629) B471629
theorem B314563 : Blo 275825 314563 := bstep (se 1 (by rfl) ⟨235922, by rfl⟩ : syracuseStep 314563 = 471845) B471845
theorem B937169 : Blo 275825 937169 := bstep (se 2 (by rfl) ⟨351438, by rfl⟩ : syracuseStep 937169 = 702877) B702877
theorem B314627 : Blo 275825 314627 := bstep (se 1 (by rfl) ⟨235970, by rfl⟩ : syracuseStep 314627 = 471941) B471941
theorem B314707 : Blo 275825 314707 := bstep (se 1 (by rfl) ⟨236030, by rfl⟩ : syracuseStep 314707 = 472061) B472061
theorem B445841 : Blo 275825 445841 := bstep (se 2 (by rfl) ⟨167190, by rfl⟩ : syracuseStep 445841 = 334381) B334381
theorem B1789361 : Blo 275825 1789361 := bstep (se 2 (by rfl) ⟨671010, by rfl⟩ : syracuseStep 1789361 = 1342021) B1342021
theorem B1789411 : Blo 275825 1789411 := bstep (se 1 (by rfl) ⟨1342058, by rfl⟩ : syracuseStep 1789411 = 2684117) B2684117
theorem B806381 : Blo 275825 806381 := bstep (se 3 (by rfl) ⟨151196, by rfl⟩ : syracuseStep 806381 = 302393) B302393
theorem B1887877 : Blo 275825 1887877 := bstep (se 4 (by rfl) ⟨176988, by rfl⟩ : syracuseStep 1887877 = 353977) B353977
theorem B3559139 : Blo 275825 3559139 := bstep (se 1 (by rfl) ⟨2669354, by rfl⟩ : syracuseStep 3559139 = 5338709) B5338709
theorem B937709 : Blo 275825 937709 := bstep (se 3 (by rfl) ⟨175820, by rfl⟩ : syracuseStep 937709 = 351641) B351641
theorem B937763 : Blo 275825 937763 := bstep (se 1 (by rfl) ⟨703322, by rfl⟩ : syracuseStep 937763 = 1406645) B1406645
theorem B1593229 : Blo 275825 1593229 := bstep (se 3 (by rfl) ⟨298730, by rfl⟩ : syracuseStep 1593229 = 597461) B597461
theorem B446353 : Blo 275825 446353 := bstep (se 2 (by rfl) ⟨167382, by rfl⟩ : syracuseStep 446353 = 334765) B334765
theorem B938033 : Blo 275825 938033 := bstep (se 2 (by rfl) ⟨351762, by rfl⟩ : syracuseStep 938033 = 703525) B703525
theorem B413747 : Blo 275825 413747 := bstep (se 1 (by rfl) ⟨310310, by rfl⟩ : syracuseStep 413747 = 620621) B620621
theorem B413777 : Blo 275825 413777 := bstep (se 2 (by rfl) ⟨155166, by rfl⟩ : syracuseStep 413777 = 310333) B310333
theorem B413795 : Blo 275825 413795 := bstep (se 1 (by rfl) ⟨310346, by rfl⟩ : syracuseStep 413795 = 620693) B620693
theorem B413825 : Blo 275825 413825 := bstep (se 2 (by rfl) ⟨155184, by rfl⟩ : syracuseStep 413825 = 310369) B310369
theorem B413843 : Blo 275825 413843 := bstep (se 1 (by rfl) ⟨310382, by rfl⟩ : syracuseStep 413843 = 620765) B620765
theorem B413873 : Blo 275825 413873 := bstep (se 2 (by rfl) ⟨155202, by rfl⟩ : syracuseStep 413873 = 310405) B310405
theorem B413891 : Blo 275825 413891 := bstep (se 1 (by rfl) ⟨310418, by rfl⟩ : syracuseStep 413891 = 620837) B620837
theorem B413921 : Blo 275825 413921 := bstep (se 2 (by rfl) ⟨155220, by rfl⟩ : syracuseStep 413921 = 310441) B310441
theorem B413939 : Blo 275825 413939 := bstep (se 1 (by rfl) ⟨310454, by rfl⟩ : syracuseStep 413939 = 620909) B620909
theorem B413969 : Blo 275825 413969 := bstep (se 2 (by rfl) ⟨155238, by rfl⟩ : syracuseStep 413969 = 310477) B310477
theorem B413987 : Blo 275825 413987 := bstep (se 1 (by rfl) ⟨310490, by rfl⟩ : syracuseStep 413987 = 620981) B620981
theorem B414017 : Blo 275825 414017 := bstep (se 2 (by rfl) ⟨155256, by rfl⟩ : syracuseStep 414017 = 310513) B310513
theorem B414035 : Blo 275825 414035 := bstep (se 1 (by rfl) ⟨310526, by rfl⟩ : syracuseStep 414035 = 621053) B621053
theorem B2117987 : Blo 275825 2117987 := bstep (se 1 (by rfl) ⟨1588490, by rfl⟩ : syracuseStep 2117987 = 3176981) B3176981
theorem B414065 : Blo 275825 414065 := bstep (se 2 (by rfl) ⟨155274, by rfl⟩ : syracuseStep 414065 = 310549) B310549
theorem B414083 : Blo 275825 414083 := bstep (se 1 (by rfl) ⟨310562, by rfl⟩ : syracuseStep 414083 = 621125) B621125
theorem B414113 : Blo 275825 414113 := bstep (se 2 (by rfl) ⟨155292, by rfl⟩ : syracuseStep 414113 = 310585) B310585
theorem B414131 : Blo 275825 414131 := bstep (se 1 (by rfl) ⟨310598, by rfl⟩ : syracuseStep 414131 = 621197) B621197
theorem B414161 : Blo 275825 414161 := bstep (se 2 (by rfl) ⟨155310, by rfl⟩ : syracuseStep 414161 = 310621) B310621
theorem B414179 : Blo 275825 414179 := bstep (se 1 (by rfl) ⟨310634, by rfl⟩ : syracuseStep 414179 = 621269) B621269
theorem B414209 : Blo 275825 414209 := bstep (se 2 (by rfl) ⟨155328, by rfl⟩ : syracuseStep 414209 = 310657) B310657
theorem B414227 : Blo 275825 414227 := bstep (se 1 (by rfl) ⟨310670, by rfl⟩ : syracuseStep 414227 = 621341) B621341
theorem B414257 : Blo 275825 414257 := bstep (se 2 (by rfl) ⟨155346, by rfl⟩ : syracuseStep 414257 = 310693) B310693
theorem B414275 : Blo 275825 414275 := bstep (se 1 (by rfl) ⟨310706, by rfl⟩ : syracuseStep 414275 = 621413) B621413
theorem B938573 : Blo 275825 938573 := bstep (se 3 (by rfl) ⟨175982, by rfl⟩ : syracuseStep 938573 = 351965) B351965
theorem B1430093 : Blo 275825 1430093 := bstep (se 3 (by rfl) ⟨268142, by rfl⟩ : syracuseStep 1430093 = 536285) B536285
theorem B414305 : Blo 275825 414305 := bstep (se 2 (by rfl) ⟨155364, by rfl⟩ : syracuseStep 414305 = 310729) B310729
theorem B414323 : Blo 275825 414323 := bstep (se 1 (by rfl) ⟨310742, by rfl⟩ : syracuseStep 414323 = 621485) B621485
theorem B938627 : Blo 275825 938627 := bstep (se 1 (by rfl) ⟨703970, by rfl⟩ : syracuseStep 938627 = 1407941) B1407941
theorem B414353 : Blo 275825 414353 := bstep (se 2 (by rfl) ⟨155382, by rfl⟩ : syracuseStep 414353 = 310765) B310765
theorem B1397411 : Blo 275825 1397411 := bstep (se 1 (by rfl) ⟨1048058, by rfl⟩ : syracuseStep 1397411 = 2096117) B2096117
theorem B414371 : Blo 275825 414371 := bstep (se 1 (by rfl) ⟨310778, by rfl⟩ : syracuseStep 414371 = 621557) B621557
theorem B414401 : Blo 275825 414401 := bstep (se 2 (by rfl) ⟨155400, by rfl⟩ : syracuseStep 414401 = 310801) B310801
theorem B414419 : Blo 275825 414419 := bstep (se 1 (by rfl) ⟨310814, by rfl⟩ : syracuseStep 414419 = 621629) B621629
theorem B414449 : Blo 275825 414449 := bstep (se 2 (by rfl) ⟨155418, by rfl⟩ : syracuseStep 414449 = 310837) B310837
theorem B414467 : Blo 275825 414467 := bstep (se 1 (by rfl) ⟨310850, by rfl⟩ : syracuseStep 414467 = 621701) B621701
theorem B414497 : Blo 275825 414497 := bstep (se 2 (by rfl) ⟨155436, by rfl⟩ : syracuseStep 414497 = 310873) B310873
theorem B414515 : Blo 275825 414515 := bstep (se 1 (by rfl) ⟨310886, by rfl⟩ : syracuseStep 414515 = 621773) B621773
theorem B414545 : Blo 275825 414545 := bstep (se 2 (by rfl) ⟨155454, by rfl⟩ : syracuseStep 414545 = 310909) B310909
theorem B414563 : Blo 275825 414563 := bstep (se 1 (by rfl) ⟨310922, by rfl⟩ : syracuseStep 414563 = 621845) B621845
theorem B906083 : Blo 275825 906083 := bstep (se 1 (by rfl) ⟨679562, by rfl⟩ : syracuseStep 906083 = 1359125) B1359125
theorem B414593 : Blo 275825 414593 := bstep (se 2 (by rfl) ⟨155472, by rfl⟩ : syracuseStep 414593 = 310945) B310945
theorem B938897 : Blo 275825 938897 := bstep (se 2 (by rfl) ⟨352086, by rfl⟩ : syracuseStep 938897 = 704173) B704173
theorem B414611 : Blo 275825 414611 := bstep (se 1 (by rfl) ⟨310958, by rfl⟩ : syracuseStep 414611 = 621917) B621917
theorem B414641 : Blo 275825 414641 := bstep (se 2 (by rfl) ⟨155490, by rfl⟩ : syracuseStep 414641 = 310981) B310981
theorem B414659 : Blo 275825 414659 := bstep (se 1 (by rfl) ⟨310994, by rfl⟩ : syracuseStep 414659 = 621989) B621989
theorem B414689 : Blo 275825 414689 := bstep (se 2 (by rfl) ⟨155508, by rfl⟩ : syracuseStep 414689 = 311017) B311017
theorem B414707 : Blo 275825 414707 := bstep (se 1 (by rfl) ⟨311030, by rfl⟩ : syracuseStep 414707 = 622061) B622061
theorem B414737 : Blo 275825 414737 := bstep (se 2 (by rfl) ⟨155526, by rfl⟩ : syracuseStep 414737 = 311053) B311053
theorem B414755 : Blo 275825 414755 := bstep (se 1 (by rfl) ⟨311066, by rfl⟩ : syracuseStep 414755 = 622133) B622133
theorem B414785 : Blo 275825 414785 := bstep (se 2 (by rfl) ⟨155544, by rfl⟩ : syracuseStep 414785 = 311089) B311089
theorem B349267 : Blo 275825 349267 := bstep (se 1 (by rfl) ⟨261950, by rfl⟩ : syracuseStep 349267 = 523901) B523901
theorem B414803 : Blo 275825 414803 := bstep (se 1 (by rfl) ⟨311102, by rfl⟩ : syracuseStep 414803 = 622205) B622205
theorem B414833 : Blo 275825 414833 := bstep (se 2 (by rfl) ⟨155562, by rfl⟩ : syracuseStep 414833 = 311125) B311125
theorem B414851 : Blo 275825 414851 := bstep (se 1 (by rfl) ⟨311138, by rfl⟩ : syracuseStep 414851 = 622277) B622277
theorem B447635 : Blo 275825 447635 := bstep (se 1 (by rfl) ⟨335726, by rfl⟩ : syracuseStep 447635 = 671453) B671453
theorem B414881 : Blo 275825 414881 := bstep (se 2 (by rfl) ⟨155580, by rfl⟩ : syracuseStep 414881 = 311161) B311161
theorem B349363 : Blo 275825 349363 := bstep (se 1 (by rfl) ⟨262022, by rfl⟩ : syracuseStep 349363 = 524045) B524045
theorem B414899 : Blo 275825 414899 := bstep (se 1 (by rfl) ⟨311174, by rfl⟩ : syracuseStep 414899 = 622349) B622349
theorem B414929 : Blo 275825 414929 := bstep (se 2 (by rfl) ⟨155598, by rfl⟩ : syracuseStep 414929 = 311197) B311197
theorem B414947 : Blo 275825 414947 := bstep (se 1 (by rfl) ⟨311210, by rfl⟩ : syracuseStep 414947 = 622421) B622421
theorem B414977 : Blo 275825 414977 := bstep (se 2 (by rfl) ⟨155616, by rfl⟩ : syracuseStep 414977 = 311233) B311233
theorem B414995 : Blo 275825 414995 := bstep (se 1 (by rfl) ⟨311246, by rfl⟩ : syracuseStep 414995 = 622493) B622493
theorem B447763 : Blo 275825 447763 := bstep (se 1 (by rfl) ⟨335822, by rfl⟩ : syracuseStep 447763 = 671645) B671645
theorem B415025 : Blo 275825 415025 := bstep (se 2 (by rfl) ⟨155634, by rfl⟩ : syracuseStep 415025 = 311269) B311269
theorem B415043 : Blo 275825 415043 := bstep (se 1 (by rfl) ⟨311282, by rfl⟩ : syracuseStep 415043 = 622565) B622565
theorem B415073 : Blo 275825 415073 := bstep (se 2 (by rfl) ⟨155652, by rfl⟩ : syracuseStep 415073 = 311305) B311305
theorem B415091 : Blo 275825 415091 := bstep (se 1 (by rfl) ⟨311318, by rfl⟩ : syracuseStep 415091 = 622637) B622637
theorem B415121 : Blo 275825 415121 := bstep (se 2 (by rfl) ⟨155670, by rfl⟩ : syracuseStep 415121 = 311341) B311341
theorem B447905 : Blo 275825 447905 := bstep (se 2 (by rfl) ⟨167964, by rfl⟩ : syracuseStep 447905 = 335929) B335929
theorem B415139 : Blo 275825 415139 := bstep (se 1 (by rfl) ⟨311354, by rfl⟩ : syracuseStep 415139 = 622709) B622709
theorem B939437 : Blo 275825 939437 := bstep (se 3 (by rfl) ⟨176144, by rfl⟩ : syracuseStep 939437 = 352289) B352289
theorem B415169 : Blo 275825 415169 := bstep (se 2 (by rfl) ⟨155688, by rfl⟩ : syracuseStep 415169 = 311377) B311377
theorem B1398221 : Blo 275825 1398221 := bstep (se 3 (by rfl) ⟨262166, by rfl⟩ : syracuseStep 1398221 = 524333) B524333
theorem B415187 : Blo 275825 415187 := bstep (se 1 (by rfl) ⟨311390, by rfl⟩ : syracuseStep 415187 = 622781) B622781
theorem B939491 : Blo 275825 939491 := bstep (se 1 (by rfl) ⟨704618, by rfl⟩ : syracuseStep 939491 = 1409237) B1409237
theorem B415217 : Blo 275825 415217 := bstep (se 2 (by rfl) ⟨155706, by rfl⟩ : syracuseStep 415217 = 311413) B311413
theorem B415235 : Blo 275825 415235 := bstep (se 1 (by rfl) ⟨311426, by rfl⟩ : syracuseStep 415235 = 622853) B622853
theorem B415265 : Blo 275825 415265 := bstep (se 2 (by rfl) ⟨155724, by rfl⟩ : syracuseStep 415265 = 311449) B311449
theorem B316963 : Blo 275825 316963 := bstep (se 1 (by rfl) ⟨237722, by rfl⟩ : syracuseStep 316963 = 475445) B475445
theorem B415283 : Blo 275825 415283 := bstep (se 1 (by rfl) ⟨311462, by rfl⟩ : syracuseStep 415283 = 622925) B622925
theorem B415313 : Blo 275825 415313 := bstep (se 2 (by rfl) ⟨155742, by rfl⟩ : syracuseStep 415313 = 311485) B311485
theorem B415331 : Blo 275825 415331 := bstep (se 1 (by rfl) ⟨311498, by rfl⟩ : syracuseStep 415331 = 622997) B622997
theorem B415361 : Blo 275825 415361 := bstep (se 2 (by rfl) ⟨155760, by rfl⟩ : syracuseStep 415361 = 311521) B311521
theorem B415379 : Blo 275825 415379 := bstep (se 1 (by rfl) ⟨311534, by rfl⟩ : syracuseStep 415379 = 623069) B623069
theorem B349859 : Blo 275825 349859 := bstep (se 1 (by rfl) ⟨262394, by rfl⟩ : syracuseStep 349859 = 524789) B524789
theorem B382627 : Blo 275825 382627 := bstep (se 1 (by rfl) ⟨286970, by rfl⟩ : syracuseStep 382627 = 573941) B573941
theorem B415409 : Blo 275825 415409 := bstep (se 2 (by rfl) ⟨155778, by rfl⟩ : syracuseStep 415409 = 311557) B311557
theorem B448193 : Blo 275825 448193 := bstep (se 2 (by rfl) ⟨168072, by rfl⟩ : syracuseStep 448193 = 336145) B336145
theorem B415427 : Blo 275825 415427 := bstep (se 1 (by rfl) ⟨311570, by rfl⟩ : syracuseStep 415427 = 623141) B623141
theorem B415457 : Blo 275825 415457 := bstep (se 2 (by rfl) ⟨155796, by rfl⟩ : syracuseStep 415457 = 311593) B311593
theorem B939761 : Blo 275825 939761 := bstep (se 2 (by rfl) ⟨352410, by rfl⟩ : syracuseStep 939761 = 704821) B704821
theorem B415475 : Blo 275825 415475 := bstep (se 1 (by rfl) ⟨311606, by rfl⟩ : syracuseStep 415475 = 623213) B623213
theorem B415505 : Blo 275825 415505 := bstep (se 2 (by rfl) ⟨155814, by rfl⟩ : syracuseStep 415505 = 311629) B311629
theorem B415523 : Blo 275825 415523 := bstep (se 1 (by rfl) ⟨311642, by rfl⟩ : syracuseStep 415523 = 623285) B623285
theorem B907057 : Blo 275825 907057 := bstep (se 2 (by rfl) ⟨340146, by rfl⟩ : syracuseStep 907057 = 680293) B680293
theorem B415553 : Blo 275825 415553 := bstep (se 2 (by rfl) ⟨155832, by rfl⟩ : syracuseStep 415553 = 311665) B311665
theorem B1791821 : Blo 275825 1791821 := bstep (se 3 (by rfl) ⟨335966, by rfl⟩ : syracuseStep 1791821 = 671933) B671933
theorem B415571 : Blo 275825 415571 := bstep (se 1 (by rfl) ⟨311678, by rfl⟩ : syracuseStep 415571 = 623357) B623357
theorem B415601 : Blo 275825 415601 := bstep (se 2 (by rfl) ⟨155850, by rfl⟩ : syracuseStep 415601 = 311701) B311701
theorem B415619 : Blo 275825 415619 := bstep (se 1 (by rfl) ⟨311714, by rfl⟩ : syracuseStep 415619 = 623429) B623429
theorem B415649 : Blo 275825 415649 := bstep (se 2 (by rfl) ⟨155868, by rfl⟩ : syracuseStep 415649 = 311737) B311737
theorem B415667 : Blo 275825 415667 := bstep (se 1 (by rfl) ⟨311750, by rfl⟩ : syracuseStep 415667 = 623501) B623501
theorem B415697 : Blo 275825 415697 := bstep (se 2 (by rfl) ⟨155886, by rfl⟩ : syracuseStep 415697 = 311773) B311773
theorem B415715 : Blo 275825 415715 := bstep (se 1 (by rfl) ⟨311786, by rfl⟩ : syracuseStep 415715 = 623573) B623573
theorem B415745 : Blo 275825 415745 := bstep (se 2 (by rfl) ⟨155904, by rfl⟩ : syracuseStep 415745 = 311809) B311809
theorem B415763 : Blo 275825 415763 := bstep (se 1 (by rfl) ⟨311822, by rfl⟩ : syracuseStep 415763 = 623645) B623645
theorem B415793 : Blo 275825 415793 := bstep (se 2 (by rfl) ⟨155922, by rfl⟩ : syracuseStep 415793 = 311845) B311845
theorem B415811 : Blo 275825 415811 := bstep (se 1 (by rfl) ⟨311858, by rfl⟩ : syracuseStep 415811 = 623717) B623717
theorem B415841 : Blo 275825 415841 := bstep (se 2 (by rfl) ⟨155940, by rfl⟩ : syracuseStep 415841 = 311881) B311881
theorem B415859 : Blo 275825 415859 := bstep (se 1 (by rfl) ⟨311894, by rfl⟩ : syracuseStep 415859 = 623789) B623789
theorem B415889 : Blo 275825 415889 := bstep (se 2 (by rfl) ⟨155958, by rfl⟩ : syracuseStep 415889 = 311917) B311917
theorem B415907 : Blo 275825 415907 := bstep (se 1 (by rfl) ⟨311930, by rfl⟩ : syracuseStep 415907 = 623861) B623861
theorem B415937 : Blo 275825 415937 := bstep (se 2 (by rfl) ⟨155976, by rfl⟩ : syracuseStep 415937 = 311953) B311953
theorem B415955 : Blo 275825 415955 := bstep (se 1 (by rfl) ⟨311966, by rfl⟩ : syracuseStep 415955 = 623933) B623933
theorem B415985 : Blo 275825 415985 := bstep (se 2 (by rfl) ⟨155994, by rfl⟩ : syracuseStep 415985 = 311989) B311989
theorem B416003 : Blo 275825 416003 := bstep (se 1 (by rfl) ⟨312002, by rfl⟩ : syracuseStep 416003 = 624005) B624005
theorem B940301 : Blo 275825 940301 := bstep (se 3 (by rfl) ⟨176306, by rfl⟩ : syracuseStep 940301 = 352613) B352613
theorem B416033 : Blo 275825 416033 := bstep (se 2 (by rfl) ⟨156012, by rfl⟩ : syracuseStep 416033 = 312025) B312025
theorem B416051 : Blo 275825 416051 := bstep (se 1 (by rfl) ⟨312038, by rfl⟩ : syracuseStep 416051 = 624077) B624077
theorem B940355 : Blo 275825 940355 := bstep (se 1 (by rfl) ⟨705266, by rfl⟩ : syracuseStep 940355 = 1410533) B1410533
theorem B416081 : Blo 275825 416081 := bstep (se 2 (by rfl) ⟨156030, by rfl⟩ : syracuseStep 416081 = 312061) B312061
theorem B350563 : Blo 275825 350563 := bstep (se 1 (by rfl) ⟨262922, by rfl⟩ : syracuseStep 350563 = 525845) B525845
theorem B416099 : Blo 275825 416099 := bstep (se 1 (by rfl) ⟨312074, by rfl⟩ : syracuseStep 416099 = 624149) B624149
theorem B416129 : Blo 275825 416129 := bstep (se 2 (by rfl) ⟨156048, by rfl⟩ : syracuseStep 416129 = 312097) B312097
theorem B416147 : Blo 275825 416147 := bstep (se 1 (by rfl) ⟨312110, by rfl⟩ : syracuseStep 416147 = 624221) B624221
theorem B416177 : Blo 275825 416177 := bstep (se 2 (by rfl) ⟨156066, by rfl⟩ : syracuseStep 416177 = 312133) B312133
theorem B350659 : Blo 275825 350659 := bstep (se 1 (by rfl) ⟨262994, by rfl⟩ : syracuseStep 350659 = 525989) B525989
theorem B416195 : Blo 275825 416195 := bstep (se 1 (by rfl) ⟨312146, by rfl⟩ : syracuseStep 416195 = 624293) B624293
theorem B416225 : Blo 275825 416225 := bstep (se 2 (by rfl) ⟨156084, by rfl⟩ : syracuseStep 416225 = 312169) B312169
theorem B416243 : Blo 275825 416243 := bstep (se 1 (by rfl) ⟨312182, by rfl⟩ : syracuseStep 416243 = 624365) B624365
theorem B416273 : Blo 275825 416273 := bstep (se 2 (by rfl) ⟨156102, by rfl⟩ : syracuseStep 416273 = 312205) B312205
theorem B416291 : Blo 275825 416291 := bstep (se 1 (by rfl) ⟨312218, by rfl⟩ : syracuseStep 416291 = 624437) B624437
theorem B1268273 : Blo 275825 1268273 := bstep (se 2 (by rfl) ⟨475602, by rfl⟩ : syracuseStep 1268273 = 951205) B951205
theorem B416321 : Blo 275825 416321 := bstep (se 2 (by rfl) ⟨156120, by rfl⟩ : syracuseStep 416321 = 312241) B312241
theorem B940625 : Blo 275825 940625 := bstep (se 2 (by rfl) ⟨352734, by rfl⟩ : syracuseStep 940625 = 705469) B705469
theorem B416339 : Blo 275825 416339 := bstep (se 1 (by rfl) ⟨312254, by rfl⟩ : syracuseStep 416339 = 624509) B624509
theorem B416369 : Blo 275825 416369 := bstep (se 2 (by rfl) ⟨156138, by rfl⟩ : syracuseStep 416369 = 312277) B312277
theorem B416387 : Blo 275825 416387 := bstep (se 1 (by rfl) ⟨312290, by rfl⟩ : syracuseStep 416387 = 624581) B624581
theorem B416417 : Blo 275825 416417 := bstep (se 2 (by rfl) ⟨156156, by rfl⟩ : syracuseStep 416417 = 312313) B312313
theorem B416435 : Blo 275825 416435 := bstep (se 1 (by rfl) ⟨312326, by rfl⟩ : syracuseStep 416435 = 624653) B624653
theorem B2382533 : Blo 275825 2382533 := bstep (se 4 (by rfl) ⟨223362, by rfl⟩ : syracuseStep 2382533 = 446725) B446725
theorem B416465 : Blo 275825 416465 := bstep (se 2 (by rfl) ⟨156174, by rfl⟩ : syracuseStep 416465 = 312349) B312349
theorem B416483 : Blo 275825 416483 := bstep (se 1 (by rfl) ⟨312362, by rfl⟩ : syracuseStep 416483 = 624725) B624725
theorem B8575715 : Blo 275825 8575715 := bstep (se 1 (by rfl) ⟨6431786, by rfl⟩ : syracuseStep 8575715 = 12863573) B12863573
theorem B416513 : Blo 275825 416513 := bstep (se 2 (by rfl) ⟨156192, by rfl⟩ : syracuseStep 416513 = 312385) B312385
theorem B416531 : Blo 275825 416531 := bstep (se 1 (by rfl) ⟨312398, by rfl⟩ : syracuseStep 416531 = 624797) B624797
theorem B416561 : Blo 275825 416561 := bstep (se 2 (by rfl) ⟨156210, by rfl⟩ : syracuseStep 416561 = 312421) B312421
theorem B318259 : Blo 275825 318259 := bstep (se 1 (by rfl) ⟨238694, by rfl⟩ : syracuseStep 318259 = 477389) B477389
theorem B416579 : Blo 275825 416579 := bstep (se 1 (by rfl) ⟨312434, by rfl⟩ : syracuseStep 416579 = 624869) B624869
theorem B1694533 : Blo 275825 1694533 := bstep (se 4 (by rfl) ⟨158862, by rfl⟩ : syracuseStep 1694533 = 317725) B317725
theorem B416609 : Blo 275825 416609 := bstep (se 2 (by rfl) ⟨156228, by rfl⟩ : syracuseStep 416609 = 312457) B312457
theorem B416627 : Blo 275825 416627 := bstep (se 1 (by rfl) ⟨312470, by rfl⟩ : syracuseStep 416627 = 624941) B624941
theorem B1268621 : Blo 275825 1268621 := bstep (se 3 (by rfl) ⟨237866, by rfl⟩ : syracuseStep 1268621 = 475733) B475733
theorem B416657 : Blo 275825 416657 := bstep (se 2 (by rfl) ⟨156246, by rfl⟩ : syracuseStep 416657 = 312493) B312493
theorem B416675 : Blo 275825 416675 := bstep (se 1 (by rfl) ⟨312506, by rfl⟩ : syracuseStep 416675 = 625013) B625013
theorem B351155 : Blo 275825 351155 := bstep (se 1 (by rfl) ⟨263366, by rfl⟩ : syracuseStep 351155 = 526733) B526733
theorem B416705 : Blo 275825 416705 := bstep (se 2 (by rfl) ⟨156264, by rfl⟩ : syracuseStep 416705 = 312529) B312529
theorem B416723 : Blo 275825 416723 := bstep (se 1 (by rfl) ⟨312542, by rfl⟩ : syracuseStep 416723 = 625085) B625085
theorem B416753 : Blo 275825 416753 := bstep (se 2 (by rfl) ⟨156282, by rfl⟩ : syracuseStep 416753 = 312565) B312565
theorem B416771 : Blo 275825 416771 := bstep (se 1 (by rfl) ⟨312578, by rfl⟩ : syracuseStep 416771 = 625157) B625157
theorem B416801 : Blo 275825 416801 := bstep (se 2 (by rfl) ⟨156300, by rfl⟩ : syracuseStep 416801 = 312601) B312601
theorem B416819 : Blo 275825 416819 := bstep (se 1 (by rfl) ⟨312614, by rfl⟩ : syracuseStep 416819 = 625229) B625229
theorem B416849 : Blo 275825 416849 := bstep (se 2 (by rfl) ⟨156318, by rfl⟩ : syracuseStep 416849 = 312637) B312637
theorem B416867 : Blo 275825 416867 := bstep (se 1 (by rfl) ⟨312650, by rfl⟩ : syracuseStep 416867 = 625301) B625301
theorem B941165 : Blo 275825 941165 := bstep (se 3 (by rfl) ⟨176468, by rfl⟩ : syracuseStep 941165 = 352937) B352937
theorem B416897 : Blo 275825 416897 := bstep (se 2 (by rfl) ⟨156336, by rfl⟩ : syracuseStep 416897 = 312673) B312673
theorem B416915 : Blo 275825 416915 := bstep (se 1 (by rfl) ⟨312686, by rfl⟩ : syracuseStep 416915 = 625373) B625373
theorem B941219 : Blo 275825 941219 := bstep (se 1 (by rfl) ⟨705914, by rfl⟩ : syracuseStep 941219 = 1411829) B1411829
theorem B416945 : Blo 275825 416945 := bstep (se 2 (by rfl) ⟨156354, by rfl⟩ : syracuseStep 416945 = 312709) B312709
theorem B416963 : Blo 275825 416963 := bstep (se 1 (by rfl) ⟨312722, by rfl⟩ : syracuseStep 416963 = 625445) B625445
theorem B646339 : Blo 275825 646339 := bstep (se 1 (by rfl) ⟨484754, by rfl⟩ : syracuseStep 646339 = 969509) B969509
theorem B416993 : Blo 275825 416993 := bstep (se 2 (by rfl) ⟨156372, by rfl⟩ : syracuseStep 416993 = 312745) B312745
theorem B417011 : Blo 275825 417011 := bstep (se 1 (by rfl) ⟨312758, by rfl⟩ : syracuseStep 417011 = 625517) B625517
theorem B1072397 : Blo 275825 1072397 := bstep (se 3 (by rfl) ⟨201074, by rfl⟩ : syracuseStep 1072397 = 402149) B402149
theorem B417041 : Blo 275825 417041 := bstep (se 2 (by rfl) ⟨156390, by rfl⟩ : syracuseStep 417041 = 312781) B312781
theorem B417059 : Blo 275825 417059 := bstep (se 1 (by rfl) ⟨312794, by rfl⟩ : syracuseStep 417059 = 625589) B625589
theorem B417089 : Blo 275825 417089 := bstep (se 2 (by rfl) ⟨156408, by rfl⟩ : syracuseStep 417089 = 312817) B312817
theorem B417107 : Blo 275825 417107 := bstep (se 1 (by rfl) ⟨312830, by rfl⟩ : syracuseStep 417107 = 625661) B625661
theorem B417137 : Blo 275825 417137 := bstep (se 2 (by rfl) ⟨156426, by rfl⟩ : syracuseStep 417137 = 312853) B312853
theorem B417155 : Blo 275825 417155 := bstep (se 1 (by rfl) ⟨312866, by rfl⟩ : syracuseStep 417155 = 625733) B625733
theorem B417185 : Blo 275825 417185 := bstep (se 2 (by rfl) ⟨156444, by rfl⟩ : syracuseStep 417185 = 312889) B312889
theorem B941489 : Blo 275825 941489 := bstep (se 2 (by rfl) ⟨353058, by rfl⟩ : syracuseStep 941489 = 706117) B706117
theorem B417203 : Blo 275825 417203 := bstep (se 1 (by rfl) ⟨312902, by rfl⟩ : syracuseStep 417203 = 625805) B625805
theorem B417233 : Blo 275825 417233 := bstep (se 2 (by rfl) ⟨156462, by rfl⟩ : syracuseStep 417233 = 312925) B312925
theorem B417251 : Blo 275825 417251 := bstep (se 1 (by rfl) ⟨312938, by rfl⟩ : syracuseStep 417251 = 625877) B625877
theorem B417281 : Blo 275825 417281 := bstep (se 2 (by rfl) ⟨156480, by rfl⟩ : syracuseStep 417281 = 312961) B312961
theorem B417299 : Blo 275825 417299 := bstep (se 1 (by rfl) ⟨312974, by rfl⟩ : syracuseStep 417299 = 625949) B625949
theorem B417329 : Blo 275825 417329 := bstep (se 2 (by rfl) ⟨156498, by rfl⟩ : syracuseStep 417329 = 312997) B312997
theorem B417347 : Blo 275825 417347 := bstep (se 1 (by rfl) ⟨313010, by rfl⟩ : syracuseStep 417347 = 626021) B626021
theorem B417377 : Blo 275825 417377 := bstep (se 2 (by rfl) ⟨156516, by rfl⟩ : syracuseStep 417377 = 313033) B313033
theorem B351859 : Blo 275825 351859 := bstep (se 1 (by rfl) ⟨263894, by rfl⟩ : syracuseStep 351859 = 527789) B527789
theorem B417395 : Blo 275825 417395 := bstep (se 1 (by rfl) ⟨313046, by rfl⟩ : syracuseStep 417395 = 626093) B626093
theorem B417425 : Blo 275825 417425 := bstep (se 2 (by rfl) ⟨156534, by rfl⟩ : syracuseStep 417425 = 313069) B313069
theorem B417443 : Blo 275825 417443 := bstep (se 1 (by rfl) ⟨313082, by rfl⟩ : syracuseStep 417443 = 626165) B626165
theorem B417473 : Blo 275825 417473 := bstep (se 2 (by rfl) ⟨156552, by rfl⟩ : syracuseStep 417473 = 313105) B313105
theorem B351955 : Blo 275825 351955 := bstep (se 1 (by rfl) ⟨263966, by rfl⟩ : syracuseStep 351955 = 527933) B527933
theorem B417491 : Blo 275825 417491 := bstep (se 1 (by rfl) ⟨313118, by rfl⟩ : syracuseStep 417491 = 626237) B626237
theorem B417521 : Blo 275825 417521 := bstep (se 2 (by rfl) ⟨156570, by rfl⟩ : syracuseStep 417521 = 313141) B313141
theorem B417539 : Blo 275825 417539 := bstep (se 1 (by rfl) ⟨313154, by rfl⟩ : syracuseStep 417539 = 626309) B626309
theorem B417569 : Blo 275825 417569 := bstep (se 2 (by rfl) ⟨156588, by rfl⟩ : syracuseStep 417569 = 313177) B313177
theorem B417587 : Blo 275825 417587 := bstep (se 1 (by rfl) ⟨313190, by rfl⟩ : syracuseStep 417587 = 626381) B626381
theorem B417617 : Blo 275825 417617 := bstep (se 2 (by rfl) ⟨156606, by rfl⟩ : syracuseStep 417617 = 313213) B313213
theorem B417635 : Blo 275825 417635 := bstep (se 1 (by rfl) ⟨313226, by rfl⟩ : syracuseStep 417635 = 626453) B626453
theorem B417665 : Blo 275825 417665 := bstep (se 2 (by rfl) ⟨156624, by rfl⟩ : syracuseStep 417665 = 313249) B313249
theorem B417683 : Blo 275825 417683 := bstep (se 1 (by rfl) ⟨313262, by rfl⟩ : syracuseStep 417683 = 626525) B626525
theorem B417713 : Blo 275825 417713 := bstep (se 2 (by rfl) ⟨156642, by rfl⟩ : syracuseStep 417713 = 313285) B313285
theorem B417731 : Blo 275825 417731 := bstep (se 1 (by rfl) ⟨313298, by rfl⟩ : syracuseStep 417731 = 626597) B626597
theorem B942029 : Blo 275825 942029 := bstep (se 3 (by rfl) ⟨176630, by rfl⟩ : syracuseStep 942029 = 353261) B353261
theorem B417761 : Blo 275825 417761 := bstep (se 2 (by rfl) ⟨156660, by rfl⟩ : syracuseStep 417761 = 313321) B313321
theorem B417779 : Blo 275825 417779 := bstep (se 1 (by rfl) ⟨313334, by rfl⟩ : syracuseStep 417779 = 626669) B626669
theorem B942083 : Blo 275825 942083 := bstep (se 1 (by rfl) ⟨706562, by rfl⟩ : syracuseStep 942083 = 1413125) B1413125
theorem B417809 : Blo 275825 417809 := bstep (se 2 (by rfl) ⟨156678, by rfl⟩ : syracuseStep 417809 = 313357) B313357
theorem B417827 : Blo 275825 417827 := bstep (se 1 (by rfl) ⟨313370, by rfl⟩ : syracuseStep 417827 = 626741) B626741
theorem B417857 : Blo 275825 417857 := bstep (se 2 (by rfl) ⟨156696, by rfl⟩ : syracuseStep 417857 = 313393) B313393
theorem B417875 : Blo 275825 417875 := bstep (se 1 (by rfl) ⟨313406, by rfl⟩ : syracuseStep 417875 = 626813) B626813
theorem B417905 : Blo 275825 417905 := bstep (se 2 (by rfl) ⟨156714, by rfl⟩ : syracuseStep 417905 = 313429) B313429
theorem B417923 : Blo 275825 417923 := bstep (se 1 (by rfl) ⟨313442, by rfl⟩ : syracuseStep 417923 = 626885) B626885
theorem B417953 : Blo 275825 417953 := bstep (se 2 (by rfl) ⟨156732, by rfl⟩ : syracuseStep 417953 = 313465) B313465
theorem B417971 : Blo 275825 417971 := bstep (se 1 (by rfl) ⟨313478, by rfl⟩ : syracuseStep 417971 = 626957) B626957
theorem B352451 : Blo 275825 352451 := bstep (se 1 (by rfl) ⟨264338, by rfl⟩ : syracuseStep 352451 = 528677) B528677
theorem B418001 : Blo 275825 418001 := bstep (se 2 (by rfl) ⟨156750, by rfl⟩ : syracuseStep 418001 = 313501) B313501
theorem B1335523 : Blo 275825 1335523 := bstep (se 1 (by rfl) ⟨1001642, by rfl⟩ : syracuseStep 1335523 = 2003285) B2003285
theorem B418019 : Blo 275825 418019 := bstep (se 1 (by rfl) ⟨313514, by rfl⟩ : syracuseStep 418019 = 627029) B627029
theorem B418049 : Blo 275825 418049 := bstep (se 2 (by rfl) ⟨156768, by rfl⟩ : syracuseStep 418049 = 313537) B313537
theorem B942353 : Blo 275825 942353 := bstep (se 2 (by rfl) ⟨353382, by rfl⟩ : syracuseStep 942353 = 706765) B706765
theorem B418067 : Blo 275825 418067 := bstep (se 1 (by rfl) ⟨313550, by rfl⟩ : syracuseStep 418067 = 627101) B627101
theorem B1401137 : Blo 275825 1401137 := bstep (se 2 (by rfl) ⟨525426, by rfl⟩ : syracuseStep 1401137 = 1050853) B1050853
theorem B418097 : Blo 275825 418097 := bstep (se 2 (by rfl) ⟨156786, by rfl⟩ : syracuseStep 418097 = 313573) B313573
theorem B418115 : Blo 275825 418115 := bstep (se 1 (by rfl) ⟨313586, by rfl⟩ : syracuseStep 418115 = 627173) B627173
theorem B418145 : Blo 275825 418145 := bstep (se 2 (by rfl) ⟨156804, by rfl⟩ : syracuseStep 418145 = 313609) B313609
theorem B418163 : Blo 275825 418163 := bstep (se 1 (by rfl) ⟨313622, by rfl⟩ : syracuseStep 418163 = 627245) B627245
theorem B418193 : Blo 275825 418193 := bstep (se 2 (by rfl) ⟨156822, by rfl⟩ : syracuseStep 418193 = 313645) B313645
theorem B418211 : Blo 275825 418211 := bstep (se 1 (by rfl) ⟨313658, by rfl⟩ : syracuseStep 418211 = 627317) B627317
theorem B418241 : Blo 275825 418241 := bstep (se 2 (by rfl) ⟨156840, by rfl⟩ : syracuseStep 418241 = 313681) B313681
theorem B418259 : Blo 275825 418259 := bstep (se 1 (by rfl) ⟨313694, by rfl⟩ : syracuseStep 418259 = 627389) B627389
theorem B418289 : Blo 275825 418289 := bstep (se 2 (by rfl) ⟨156858, by rfl⟩ : syracuseStep 418289 = 313717) B313717
theorem B418307 : Blo 275825 418307 := bstep (se 1 (by rfl) ⟨313730, by rfl⟩ : syracuseStep 418307 = 627461) B627461
theorem B418337 : Blo 275825 418337 := bstep (se 2 (by rfl) ⟨156876, by rfl⟩ : syracuseStep 418337 = 313753) B313753
theorem B418355 : Blo 275825 418355 := bstep (se 1 (by rfl) ⟨313766, by rfl⟩ : syracuseStep 418355 = 627533) B627533
theorem B418385 : Blo 275825 418385 := bstep (se 2 (by rfl) ⟨156894, by rfl⟩ : syracuseStep 418385 = 313789) B313789
theorem B418403 : Blo 275825 418403 := bstep (se 1 (by rfl) ⟨313802, by rfl⟩ : syracuseStep 418403 = 627605) B627605
theorem B418433 : Blo 275825 418433 := bstep (se 2 (by rfl) ⟨156912, by rfl⟩ : syracuseStep 418433 = 313825) B313825
theorem B2187917 : Blo 275825 2187917 := bstep (se 3 (by rfl) ⟨410234, by rfl⟩ : syracuseStep 2187917 = 820469) B820469
theorem B418451 : Blo 275825 418451 := bstep (se 1 (by rfl) ⟨313838, by rfl⟩ : syracuseStep 418451 = 627677) B627677
theorem B418481 : Blo 275825 418481 := bstep (se 2 (by rfl) ⟨156930, by rfl⟩ : syracuseStep 418481 = 313861) B313861
theorem B418499 : Blo 275825 418499 := bstep (se 1 (by rfl) ⟨313874, by rfl⟩ : syracuseStep 418499 = 627749) B627749
theorem B418529 : Blo 275825 418529 := bstep (se 2 (by rfl) ⟨156948, by rfl⟩ : syracuseStep 418529 = 313897) B313897
theorem B418547 : Blo 275825 418547 := bstep (se 1 (by rfl) ⟨313910, by rfl⟩ : syracuseStep 418547 = 627821) B627821
theorem B418577 : Blo 275825 418577 := bstep (se 2 (by rfl) ⟨156966, by rfl⟩ : syracuseStep 418577 = 313933) B313933
theorem B418595 : Blo 275825 418595 := bstep (se 1 (by rfl) ⟨313946, by rfl⟩ : syracuseStep 418595 = 627893) B627893
theorem B942893 : Blo 275825 942893 := bstep (se 3 (by rfl) ⟨176792, by rfl⟩ : syracuseStep 942893 = 353585) B353585
theorem B418625 : Blo 275825 418625 := bstep (se 2 (by rfl) ⟨156984, by rfl⟩ : syracuseStep 418625 = 313969) B313969
theorem B418643 : Blo 275825 418643 := bstep (se 1 (by rfl) ⟨313982, by rfl⟩ : syracuseStep 418643 = 627965) B627965
theorem B942947 : Blo 275825 942947 := bstep (se 1 (by rfl) ⟨707210, by rfl⟩ : syracuseStep 942947 = 1414421) B1414421
theorem B418673 : Blo 275825 418673 := bstep (se 2 (by rfl) ⟨157002, by rfl⟩ : syracuseStep 418673 = 314005) B314005
theorem B353155 : Blo 275825 353155 := bstep (se 1 (by rfl) ⟨264866, by rfl⟩ : syracuseStep 353155 = 529733) B529733
theorem B418691 : Blo 275825 418691 := bstep (se 1 (by rfl) ⟨314018, by rfl⟩ : syracuseStep 418691 = 628037) B628037
theorem B680849 : Blo 275825 680849 := bstep (se 2 (by rfl) ⟨255318, by rfl⟩ : syracuseStep 680849 = 510637) B510637
theorem B418721 : Blo 275825 418721 := bstep (se 2 (by rfl) ⟨157020, by rfl⟩ : syracuseStep 418721 = 314041) B314041
theorem B418739 : Blo 275825 418739 := bstep (se 1 (by rfl) ⟨314054, by rfl⟩ : syracuseStep 418739 = 628109) B628109
theorem B8119237 : Blo 275825 8119237 := bstep (se 4 (by rfl) ⟨761178, by rfl⟩ : syracuseStep 8119237 = 1522357) B1522357
theorem B1369037 : Blo 275825 1369037 := bstep (se 3 (by rfl) ⟨256694, by rfl⟩ : syracuseStep 1369037 = 513389) B513389
theorem B418769 : Blo 275825 418769 := bstep (se 2 (by rfl) ⟨157038, by rfl⟩ : syracuseStep 418769 = 314077) B314077
theorem B1893347 : Blo 275825 1893347 := bstep (se 1 (by rfl) ⟨1420010, by rfl⟩ : syracuseStep 1893347 = 2840021) B2840021
theorem B353251 : Blo 275825 353251 := bstep (se 1 (by rfl) ⟨264938, by rfl⟩ : syracuseStep 353251 = 529877) B529877
theorem B418787 : Blo 275825 418787 := bstep (se 1 (by rfl) ⟨314090, by rfl⟩ : syracuseStep 418787 = 628181) B628181
theorem B418817 : Blo 275825 418817 := bstep (se 2 (by rfl) ⟨157056, by rfl⟩ : syracuseStep 418817 = 314113) B314113
theorem B812035 : Blo 275825 812035 := bstep (se 1 (by rfl) ⟨609026, by rfl⟩ : syracuseStep 812035 = 1218053) B1218053
theorem B418835 : Blo 275825 418835 := bstep (se 1 (by rfl) ⟨314126, by rfl⟩ : syracuseStep 418835 = 628253) B628253
theorem B418865 : Blo 275825 418865 := bstep (se 2 (by rfl) ⟨157074, by rfl⟩ : syracuseStep 418865 = 314149) B314149
theorem B418883 : Blo 275825 418883 := bstep (se 1 (by rfl) ⟨314162, by rfl⟩ : syracuseStep 418883 = 628325) B628325
theorem B418913 : Blo 275825 418913 := bstep (se 2 (by rfl) ⟨157092, by rfl⟩ : syracuseStep 418913 = 314185) B314185
theorem B943217 : Blo 275825 943217 := bstep (se 2 (by rfl) ⟨353706, by rfl⟩ : syracuseStep 943217 = 707413) B707413
theorem B418931 : Blo 275825 418931 := bstep (se 1 (by rfl) ⟨314198, by rfl⟩ : syracuseStep 418931 = 628397) B628397
theorem B418961 : Blo 275825 418961 := bstep (se 2 (by rfl) ⟨157110, by rfl⟩ : syracuseStep 418961 = 314221) B314221
theorem B418979 : Blo 275825 418979 := bstep (se 1 (by rfl) ⟨314234, by rfl⟩ : syracuseStep 418979 = 628469) B628469
theorem B419009 : Blo 275825 419009 := bstep (se 2 (by rfl) ⟨157128, by rfl⟩ : syracuseStep 419009 = 314257) B314257
theorem B419027 : Blo 275825 419027 := bstep (se 1 (by rfl) ⟨314270, by rfl⟩ : syracuseStep 419027 = 628541) B628541
theorem B419057 : Blo 275825 419057 := bstep (se 2 (by rfl) ⟨157146, by rfl⟩ : syracuseStep 419057 = 314293) B314293
theorem B419075 : Blo 275825 419075 := bstep (se 1 (by rfl) ⟨314306, by rfl⟩ : syracuseStep 419075 = 628613) B628613
theorem B419105 : Blo 275825 419105 := bstep (se 2 (by rfl) ⟨157164, by rfl⟩ : syracuseStep 419105 = 314329) B314329
theorem B419123 : Blo 275825 419123 := bstep (se 1 (by rfl) ⟨314342, by rfl⟩ : syracuseStep 419123 = 628685) B628685
theorem B419153 : Blo 275825 419153 := bstep (se 2 (by rfl) ⟨157182, by rfl⟩ : syracuseStep 419153 = 314365) B314365
theorem B419171 : Blo 275825 419171 := bstep (se 1 (by rfl) ⟨314378, by rfl⟩ : syracuseStep 419171 = 628757) B628757
theorem B419201 : Blo 275825 419201 := bstep (se 2 (by rfl) ⟨157200, by rfl⟩ : syracuseStep 419201 = 314401) B314401
theorem B419219 : Blo 275825 419219 := bstep (se 1 (by rfl) ⟨314414, by rfl⟩ : syracuseStep 419219 = 628829) B628829
theorem B746929 : Blo 275825 746929 := bstep (se 2 (by rfl) ⟨280098, by rfl⟩ : syracuseStep 746929 = 560197) B560197
theorem B1336753 : Blo 275825 1336753 := bstep (se 2 (by rfl) ⟨501282, by rfl⟩ : syracuseStep 1336753 = 1002565) B1002565
theorem B419249 : Blo 275825 419249 := bstep (se 2 (by rfl) ⟨157218, by rfl⟩ : syracuseStep 419249 = 314437) B314437
theorem B419267 : Blo 275825 419267 := bstep (se 1 (by rfl) ⟨314450, by rfl⟩ : syracuseStep 419267 = 628901) B628901
theorem B353747 : Blo 275825 353747 := bstep (se 1 (by rfl) ⟨265310, by rfl⟩ : syracuseStep 353747 = 530621) B530621
theorem B419297 : Blo 275825 419297 := bstep (se 2 (by rfl) ⟨157236, by rfl⟩ : syracuseStep 419297 = 314473) B314473
theorem B419315 : Blo 275825 419315 := bstep (se 1 (by rfl) ⟨314486, by rfl⟩ : syracuseStep 419315 = 628973) B628973
theorem B419345 : Blo 275825 419345 := bstep (se 2 (by rfl) ⟨157254, by rfl⟩ : syracuseStep 419345 = 314509) B314509
theorem B419363 : Blo 275825 419363 := bstep (se 1 (by rfl) ⟨314522, by rfl⟩ : syracuseStep 419363 = 629045) B629045
theorem B6809141 : Blo 275825 6809141 := bstep (se 5 (by rfl) ⟨319178, by rfl⟩ : syracuseStep 6809141 = 638357) B638357
theorem B419393 : Blo 275825 419393 := bstep (se 2 (by rfl) ⟨157272, by rfl⟩ : syracuseStep 419393 = 314545) B314545
theorem B2123333 : Blo 275825 2123333 := bstep (se 4 (by rfl) ⟨199062, by rfl⟩ : syracuseStep 2123333 = 398125) B398125
theorem B419411 : Blo 275825 419411 := bstep (se 1 (by rfl) ⟨314558, by rfl⟩ : syracuseStep 419411 = 629117) B629117
theorem B419441 : Blo 275825 419441 := bstep (se 2 (by rfl) ⟨157290, by rfl⟩ : syracuseStep 419441 = 314581) B314581
theorem B419459 : Blo 275825 419459 := bstep (se 1 (by rfl) ⟨314594, by rfl⟩ : syracuseStep 419459 = 629189) B629189
theorem B943757 : Blo 275825 943757 := bstep (se 3 (by rfl) ⟨176954, by rfl⟩ : syracuseStep 943757 = 353909) B353909
theorem B419489 : Blo 275825 419489 := bstep (se 2 (by rfl) ⟨157308, by rfl⟩ : syracuseStep 419489 = 314617) B314617
theorem B419507 : Blo 275825 419507 := bstep (se 1 (by rfl) ⟨314630, by rfl⟩ : syracuseStep 419507 = 629261) B629261
theorem B943811 : Blo 275825 943811 := bstep (se 1 (by rfl) ⟨707858, by rfl⟩ : syracuseStep 943811 = 1415717) B1415717
theorem B419537 : Blo 275825 419537 := bstep (se 2 (by rfl) ⟨157326, by rfl⟩ : syracuseStep 419537 = 314653) B314653
theorem B1402595 : Blo 275825 1402595 := bstep (se 1 (by rfl) ⟨1051946, by rfl⟩ : syracuseStep 1402595 = 2103893) B2103893
theorem B4056803 : Blo 275825 4056803 := bstep (se 1 (by rfl) ⟨3042602, by rfl⟩ : syracuseStep 4056803 = 6085205) B6085205
theorem B419555 : Blo 275825 419555 := bstep (se 1 (by rfl) ⟨314666, by rfl⟩ : syracuseStep 419555 = 629333) B629333
theorem B419585 : Blo 275825 419585 := bstep (se 2 (by rfl) ⟨157344, by rfl⟩ : syracuseStep 419585 = 314689) B314689
theorem B419603 : Blo 275825 419603 := bstep (se 1 (by rfl) ⟨314702, by rfl⟩ : syracuseStep 419603 = 629405) B629405
theorem B419633 : Blo 275825 419633 := bstep (se 2 (by rfl) ⟨157362, by rfl⟩ : syracuseStep 419633 = 314725) B314725
theorem B419651 : Blo 275825 419651 := bstep (se 1 (by rfl) ⟨314738, by rfl⟩ : syracuseStep 419651 = 629477) B629477
theorem B419681 : Blo 275825 419681 := bstep (se 2 (by rfl) ⟨157380, by rfl⟩ : syracuseStep 419681 = 314761) B314761
theorem B419699 : Blo 275825 419699 := bstep (se 1 (by rfl) ⟨314774, by rfl⟩ : syracuseStep 419699 = 629549) B629549
theorem B419729 : Blo 275825 419729 := bstep (se 2 (by rfl) ⟨157398, by rfl⟩ : syracuseStep 419729 = 314797) B314797
theorem B747427 : Blo 275825 747427 := bstep (se 1 (by rfl) ⟨560570, by rfl⟩ : syracuseStep 747427 = 1121141) B1121141
theorem B944081 : Blo 275825 944081 := bstep (se 2 (by rfl) ⟨354030, by rfl⟩ : syracuseStep 944081 = 708061) B708061
theorem B10414307 : Blo 275825 10414307 := bstep (se 1 (by rfl) ⟨7810730, by rfl⟩ : syracuseStep 10414307 = 15621461) B15621461
theorem B1894769 : Blo 275825 1894769 := bstep (se 2 (by rfl) ⟨710538, by rfl⟩ : syracuseStep 1894769 = 1421077) B1421077
theorem B3631601 : Blo 275825 3631601 := bstep (se 2 (by rfl) ⟨1361850, by rfl⟩ : syracuseStep 3631601 = 2723701) B2723701
theorem B1403405 : Blo 275825 1403405 := bstep (se 3 (by rfl) ⟨263138, by rfl⟩ : syracuseStep 1403405 = 526277) B526277
theorem B748109 : Blo 275825 748109 := bstep (se 3 (by rfl) ⟨140270, by rfl⟩ : syracuseStep 748109 = 280541) B280541
theorem B748205 : Blo 275825 748205 := bstep (se 3 (by rfl) ⟨140288, by rfl⟩ : syracuseStep 748205 = 280577) B280577
theorem B945361 : Blo 275825 945361 := bstep (se 2 (by rfl) ⟨354510, by rfl⟩ : syracuseStep 945361 = 709021) B709021
theorem B749027 : Blo 275825 749027 := bstep (se 1 (by rfl) ⟨561770, by rfl⟩ : syracuseStep 749027 = 1123541) B1123541
theorem B421985 : Blo 275825 421985 := bstep (se 2 (by rfl) ⟨158244, by rfl⟩ : syracuseStep 421985 = 316489) B316489
theorem B1339811 : Blo 275825 1339811 := bstep (se 1 (by rfl) ⟨1004858, by rfl⟩ : syracuseStep 1339811 = 2009717) B2009717
theorem B3600949 : Blo 275825 3600949 := bstep (se 5 (by rfl) ⟨168794, by rfl⟩ : syracuseStep 3600949 = 337589) B337589
theorem B1012387 : Blo 275825 1012387 := bstep (se 1 (by rfl) ⟨759290, by rfl⟩ : syracuseStep 1012387 = 1518581) B1518581
theorem B750563 : Blo 275825 750563 := bstep (se 1 (by rfl) ⟨562922, by rfl⟩ : syracuseStep 750563 = 1125845) B1125845
theorem B3175523 : Blo 275825 3175523 := bstep (se 1 (by rfl) ⟨2381642, by rfl⟩ : syracuseStep 3175523 = 4763285) B4763285
theorem B7599217 : Blo 275825 7599217 := bstep (se 2 (by rfl) ⟨2849706, by rfl⟩ : syracuseStep 7599217 = 5699413) B5699413
theorem B1537165 : Blo 275825 1537165 := bstep (se 3 (by rfl) ⟨288218, by rfl⟩ : syracuseStep 1537165 = 576437) B576437
theorem B2651363 : Blo 275825 2651363 := bstep (se 1 (by rfl) ⟨1988522, by rfl⟩ : syracuseStep 2651363 = 3977045) B3977045
theorem B1406321 : Blo 275825 1406321 := bstep (se 2 (by rfl) ⟨527370, by rfl⟩ : syracuseStep 1406321 = 1054741) B1054741
theorem B423299 : Blo 275825 423299 := bstep (se 1 (by rfl) ⟨317474, by rfl⟩ : syracuseStep 423299 = 634949) B634949
theorem B1799651 : Blo 275825 1799651 := bstep (se 1 (by rfl) ⟨1349738, by rfl⟩ : syracuseStep 1799651 = 2699477) B2699477
theorem B816817 : Blo 275825 816817 := bstep (se 2 (by rfl) ⟨306306, by rfl⟩ : syracuseStep 816817 = 612613) B612613
theorem B849905 : Blo 275825 849905 := bstep (se 2 (by rfl) ⟨318714, by rfl⟩ : syracuseStep 849905 = 637429) B637429
theorem B620657 : Blo 275825 620657 := bstep (se 2 (by rfl) ⟨232746, by rfl⟩ : syracuseStep 620657 = 465493) B465493
theorem B620675 : Blo 275825 620675 := bstep (se 1 (by rfl) ⟨465506, by rfl⟩ : syracuseStep 620675 = 931013) B931013
theorem B620945 : Blo 275825 620945 := bstep (se 2 (by rfl) ⟨232854, by rfl⟩ : syracuseStep 620945 = 465709) B465709
theorem B620963 : Blo 275825 620963 := bstep (se 1 (by rfl) ⟨465722, by rfl⟩ : syracuseStep 620963 = 931445) B931445
theorem B1210801 : Blo 275825 1210801 := bstep (se 2 (by rfl) ⟨454050, by rfl⟩ : syracuseStep 1210801 = 908101) B908101
theorem B752141 : Blo 275825 752141 := bstep (se 3 (by rfl) ⟨141026, by rfl⟩ : syracuseStep 752141 = 282053) B282053
theorem B621233 : Blo 275825 621233 := bstep (se 2 (by rfl) ⟨232962, by rfl⟩ : syracuseStep 621233 = 465925) B465925
theorem B621251 : Blo 275825 621251 := bstep (se 1 (by rfl) ⟨465938, by rfl⟩ : syracuseStep 621251 = 931877) B931877
theorem B1407779 : Blo 275825 1407779 := bstep (se 1 (by rfl) ⟨1055834, by rfl⟩ : syracuseStep 1407779 = 2111669) B2111669
theorem B1571633 : Blo 275825 1571633 := bstep (se 2 (by rfl) ⟨589362, by rfl⟩ : syracuseStep 1571633 = 1178725) B1178725
theorem B1047437 : Blo 275825 1047437 := bstep (se 3 (by rfl) ⟨196394, by rfl⟩ : syracuseStep 1047437 = 392789) B392789
theorem B621521 : Blo 275825 621521 := bstep (se 2 (by rfl) ⟨233070, by rfl⟩ : syracuseStep 621521 = 466141) B466141
theorem B621539 : Blo 275825 621539 := bstep (se 1 (by rfl) ⟨466154, by rfl⟩ : syracuseStep 621539 = 932309) B932309
theorem B3538019 : Blo 275825 3538019 := bstep (se 1 (by rfl) ⟨2653514, by rfl⟩ : syracuseStep 3538019 = 5307029) B5307029
theorem B621809 : Blo 275825 621809 := bstep (se 2 (by rfl) ⟨233178, by rfl⟩ : syracuseStep 621809 = 466357) B466357
theorem B621827 : Blo 275825 621827 := bstep (se 1 (by rfl) ⟨466370, by rfl⟩ : syracuseStep 621827 = 932741) B932741
theorem B589123 : Blo 275825 589123 := bstep (se 1 (by rfl) ⟨441842, by rfl⟩ : syracuseStep 589123 = 883685) B883685
theorem B622097 : Blo 275825 622097 := bstep (se 2 (by rfl) ⟨233286, by rfl⟩ : syracuseStep 622097 = 466573) B466573
theorem B622115 : Blo 275825 622115 := bstep (se 1 (by rfl) ⟨466586, by rfl⟩ : syracuseStep 622115 = 933173) B933173
theorem B1408589 : Blo 275825 1408589 := bstep (se 3 (by rfl) ⟨264110, by rfl⟩ : syracuseStep 1408589 = 528221) B528221
theorem B589457 : Blo 275825 589457 := bstep (se 2 (by rfl) ⟨221046, by rfl⟩ : syracuseStep 589457 = 442093) B442093
theorem B1048241 : Blo 275825 1048241 := bstep (se 2 (by rfl) ⟨393090, by rfl⟩ : syracuseStep 1048241 = 786181) B786181
theorem B392897 : Blo 275825 392897 := bstep (se 2 (by rfl) ⟨147336, by rfl⟩ : syracuseStep 392897 = 294673) B294673
theorem B786125 : Blo 275825 786125 := bstep (se 3 (by rfl) ⟨147398, by rfl⟩ : syracuseStep 786125 = 294797) B294797
theorem B884429 : Blo 275825 884429 := bstep (se 3 (by rfl) ⟨165830, by rfl⟩ : syracuseStep 884429 = 331661) B331661
theorem B622385 : Blo 275825 622385 := bstep (se 2 (by rfl) ⟨233394, by rfl⟩ : syracuseStep 622385 = 466789) B466789
theorem B622403 : Blo 275825 622403 := bstep (se 1 (by rfl) ⟨466802, by rfl⟩ : syracuseStep 622403 = 933605) B933605
theorem B786307 : Blo 275825 786307 := bstep (se 1 (by rfl) ⟨589730, by rfl⟩ : syracuseStep 786307 = 1179461) B1179461
theorem B524227 : Blo 275825 524227 := bstep (se 1 (by rfl) ⟨393170, by rfl⟩ : syracuseStep 524227 = 786341) B786341
theorem B950221 : Blo 275825 950221 := bstep (se 3 (by rfl) ⟨178166, by rfl⟩ : syracuseStep 950221 = 356333) B356333
theorem B786455 : Blo 275825 786455 := bstep (se 1 (by rfl) ⟨589841, by rfl⟩ : syracuseStep 786455 = 1179683) B1179683
theorem B1048727 : Blo 275825 1048727 := bstep (se 1 (by rfl) ⟨786545, by rfl⟩ : syracuseStep 1048727 = 1573091) B1573091
theorem B622745 : Blo 275825 622745 := bstep (se 2 (by rfl) ⟨233529, by rfl⟩ : syracuseStep 622745 = 467059) B467059
theorem B524531 : Blo 275825 524531 := bstep (se 1 (by rfl) ⟨393398, by rfl⟩ : syracuseStep 524531 = 786797) B786797
theorem B622835 : Blo 275825 622835 := bstep (se 1 (by rfl) ⟨467126, by rfl⟩ : syracuseStep 622835 = 934253) B934253
theorem B622871 : Blo 275825 622871 := bstep (se 1 (by rfl) ⟨467153, by rfl⟩ : syracuseStep 622871 = 934307) B934307
theorem B524569 : Blo 275825 524569 := bstep (se 2 (by rfl) ⟨196713, by rfl⟩ : syracuseStep 524569 = 393427) B393427
theorem B295211 : Blo 275825 295211 := bstep (se 1 (by rfl) ⟨221408, by rfl⟩ : syracuseStep 295211 = 442817) B442817
theorem B623051 : Blo 275825 623051 := bstep (se 1 (by rfl) ⟨467288, by rfl⟩ : syracuseStep 623051 = 934577) B934577
theorem B623105 : Blo 275825 623105 := bstep (se 2 (by rfl) ⟨233664, by rfl⟩ : syracuseStep 623105 = 467329) B467329
theorem B393751 : Blo 275825 393751 := bstep (se 1 (by rfl) ⟨295313, by rfl⟩ : syracuseStep 393751 = 590627) B590627
theorem B21627485 : Blo 275825 21627485 := bstep (se 3 (by rfl) ⟨4055153, by rfl⟩ : syracuseStep 21627485 = 8110307) B8110307
theorem B525017 : Blo 275825 525017 := bstep (se 2 (by rfl) ⟨196881, by rfl⟩ : syracuseStep 525017 = 393763) B393763
theorem B623321 : Blo 275825 623321 := bstep (se 2 (by rfl) ⟨233745, by rfl⟩ : syracuseStep 623321 = 467491) B467491
theorem B590593 : Blo 275825 590593 := bstep (se 2 (by rfl) ⟨221472, by rfl⟩ : syracuseStep 590593 = 442945) B442945
theorem B1180433 : Blo 275825 1180433 := bstep (se 2 (by rfl) ⟨442662, by rfl⟩ : syracuseStep 1180433 = 885325) B885325
theorem B1049395 : Blo 275825 1049395 := bstep (se 1 (by rfl) ⟨787046, by rfl⟩ : syracuseStep 1049395 = 1574093) B1574093
theorem B623411 : Blo 275825 623411 := bstep (se 1 (by rfl) ⟨467558, by rfl⟩ : syracuseStep 623411 = 935117) B935117
theorem B623447 : Blo 275825 623447 := bstep (se 1 (by rfl) ⟨467585, by rfl⟩ : syracuseStep 623447 = 935171) B935171
theorem B1409885 : Blo 275825 1409885 := bstep (se 3 (by rfl) ⟨264353, by rfl⟩ : syracuseStep 1409885 = 528707) B528707
theorem B885725 : Blo 275825 885725 := bstep (se 3 (by rfl) ⟨166073, by rfl⟩ : syracuseStep 885725 = 332147) B332147
theorem B623627 : Blo 275825 623627 := bstep (se 1 (by rfl) ⟨467720, by rfl⟩ : syracuseStep 623627 = 935441) B935441
theorem B623681 : Blo 275825 623681 := bstep (se 2 (by rfl) ⟨233880, by rfl⟩ : syracuseStep 623681 = 467761) B467761
theorem B590935 : Blo 275825 590935 := bstep (se 1 (by rfl) ⟨443201, by rfl⟩ : syracuseStep 590935 = 886403) B886403
theorem B623897 : Blo 275825 623897 := bstep (se 2 (by rfl) ⟨233961, by rfl⟩ : syracuseStep 623897 = 467923) B467923
theorem B623987 : Blo 275825 623987 := bstep (se 1 (by rfl) ⟨467990, by rfl⟩ : syracuseStep 623987 = 935981) B935981
theorem B1574275 : Blo 275825 1574275 := bstep (se 1 (by rfl) ⟨1180706, by rfl⟩ : syracuseStep 1574275 = 2361413) B2361413
theorem B624023 : Blo 275825 624023 := bstep (se 1 (by rfl) ⟨468017, by rfl⟩ : syracuseStep 624023 = 936035) B936035
theorem B1181101 : Blo 275825 1181101 := bstep (se 3 (by rfl) ⟨221456, by rfl⟩ : syracuseStep 1181101 = 442913) B442913
theorem B525761 : Blo 275825 525761 := bstep (se 2 (by rfl) ⟨197160, by rfl⟩ : syracuseStep 525761 = 394321) B394321
theorem B296407 : Blo 275825 296407 := bstep (se 1 (by rfl) ⟨222305, by rfl⟩ : syracuseStep 296407 = 444611) B444611
theorem B591371 : Blo 275825 591371 := bstep (se 1 (by rfl) ⟨443528, by rfl⟩ : syracuseStep 591371 = 887057) B887057
theorem B624203 : Blo 275825 624203 := bstep (se 1 (by rfl) ⟨468152, by rfl⟩ : syracuseStep 624203 = 936305) B936305
theorem B624257 : Blo 275825 624257 := bstep (se 2 (by rfl) ⟨234096, by rfl⟩ : syracuseStep 624257 = 468193) B468193
theorem B526027 : Blo 275825 526027 := bstep (se 1 (by rfl) ⟨394520, by rfl⟩ : syracuseStep 526027 = 789041) B789041
theorem B296779 : Blo 275825 296779 := bstep (se 1 (by rfl) ⟨222584, by rfl⟩ : syracuseStep 296779 = 445169) B445169
theorem B624473 : Blo 275825 624473 := bstep (se 2 (by rfl) ⟨234177, by rfl⟩ : syracuseStep 624473 = 468355) B468355
theorem B624563 : Blo 275825 624563 := bstep (se 1 (by rfl) ⟨468422, by rfl⟩ : syracuseStep 624563 = 936845) B936845
theorem B624599 : Blo 275825 624599 := bstep (se 1 (by rfl) ⟨468449, by rfl⟩ : syracuseStep 624599 = 936899) B936899
theorem B1181699 : Blo 275825 1181699 := bstep (se 1 (by rfl) ⟨886274, by rfl⟩ : syracuseStep 1181699 = 1772549) B1772549
theorem B1050641 : Blo 275825 1050641 := bstep (se 2 (by rfl) ⟨393990, by rfl⟩ : syracuseStep 1050641 = 787981) B787981
theorem B526475 : Blo 275825 526475 := bstep (se 1 (by rfl) ⟨394856, by rfl⟩ : syracuseStep 526475 = 789713) B789713
theorem B624779 : Blo 275825 624779 := bstep (se 1 (by rfl) ⟨468584, by rfl⟩ : syracuseStep 624779 = 937169) B937169
theorem B624833 : Blo 275825 624833 := bstep (se 2 (by rfl) ⟨234312, by rfl⟩ : syracuseStep 624833 = 468625) B468625
theorem B297227 : Blo 275825 297227 := bstep (se 1 (by rfl) ⟨222920, by rfl⟩ : syracuseStep 297227 = 445841) B445841
theorem B1575233 : Blo 275825 1575233 := bstep (se 2 (by rfl) ⟨590712, by rfl⟩ : syracuseStep 1575233 = 1181425) B1181425
theorem B526657 : Blo 275825 526657 := bstep (se 2 (by rfl) ⟨197496, by rfl⟩ : syracuseStep 526657 = 394993) B394993
theorem B592267 : Blo 275825 592267 := bstep (se 1 (by rfl) ⟨444200, by rfl⟩ : syracuseStep 592267 = 888401) B888401
theorem B625049 : Blo 275825 625049 := bstep (se 2 (by rfl) ⟨234393, by rfl⟩ : syracuseStep 625049 = 468787) B468787
theorem B788915 : Blo 275825 788915 := bstep (se 1 (by rfl) ⟨591686, by rfl⟩ : syracuseStep 788915 = 1183373) B1183373
theorem B625139 : Blo 275825 625139 := bstep (se 1 (by rfl) ⟨468854, by rfl⟩ : syracuseStep 625139 = 937709) B937709
theorem B625175 : Blo 275825 625175 := bstep (se 1 (by rfl) ⟨468881, by rfl⟩ : syracuseStep 625175 = 937763) B937763
theorem B526999 : Blo 275825 526999 := bstep (se 1 (by rfl) ⟨395249, by rfl⟩ : syracuseStep 526999 = 790499) B790499
theorem B1051339 : Blo 275825 1051339 := bstep (se 1 (by rfl) ⟨788504, by rfl⟩ : syracuseStep 1051339 = 1577009) B1577009
theorem B625355 : Blo 275825 625355 := bstep (se 1 (by rfl) ⟨469016, by rfl⟩ : syracuseStep 625355 = 938033) B938033
theorem B625409 : Blo 275825 625409 := bstep (se 2 (by rfl) ⟨234528, by rfl⟩ : syracuseStep 625409 = 469057) B469057
theorem B11209537 : Blo 275825 11209537 := bstep (se 2 (by rfl) ⟨4203576, by rfl⟩ : syracuseStep 11209537 = 8407153) B8407153
theorem B527219 : Blo 275825 527219 := bstep (se 1 (by rfl) ⟨395414, by rfl⟩ : syracuseStep 527219 = 790829) B790829
theorem B1411991 : Blo 275825 1411991 := bstep (se 1 (by rfl) ⟨1058993, by rfl⟩ : syracuseStep 1411991 = 2117987) B2117987
theorem B625625 : Blo 275825 625625 := bstep (se 2 (by rfl) ⟨234609, by rfl⟩ : syracuseStep 625625 = 469219) B469219
theorem B1051613 : Blo 275825 1051613 := bstep (se 3 (by rfl) ⟨197177, by rfl⟩ : syracuseStep 1051613 = 394355) B394355
theorem B625715 : Blo 275825 625715 := bstep (se 1 (by rfl) ⟨469286, by rfl⟩ : syracuseStep 625715 = 938573) B938573
theorem B527447 : Blo 275825 527447 := bstep (se 1 (by rfl) ⟨395585, by rfl⟩ : syracuseStep 527447 = 791171) B791171
theorem B625751 : Blo 275825 625751 := bstep (se 1 (by rfl) ⟨469313, by rfl⟩ : syracuseStep 625751 = 938627) B938627
theorem B593011 : Blo 275825 593011 := bstep (se 1 (by rfl) ⟨444758, by rfl⟩ : syracuseStep 593011 = 889517) B889517
theorem B625931 : Blo 275825 625931 := bstep (se 1 (by rfl) ⟨469448, by rfl⟩ : syracuseStep 625931 = 938897) B938897
theorem B625985 : Blo 275825 625985 := bstep (se 2 (by rfl) ⟨234744, by rfl⟩ : syracuseStep 625985 = 469489) B469489
theorem B527705 : Blo 275825 527705 := bstep (se 2 (by rfl) ⟨197889, by rfl⟩ : syracuseStep 527705 = 395779) B395779
theorem B298423 : Blo 275825 298423 := bstep (se 1 (by rfl) ⟨223817, by rfl⟩ : syracuseStep 298423 = 447635) B447635
theorem B626201 : Blo 275825 626201 := bstep (se 2 (by rfl) ⟨234825, by rfl⟩ : syracuseStep 626201 = 469651) B469651
theorem B593497 : Blo 275825 593497 := bstep (se 2 (by rfl) ⟨222561, by rfl⟩ : syracuseStep 593497 = 445123) B445123
theorem B298603 : Blo 275825 298603 := bstep (se 1 (by rfl) ⟨223952, by rfl⟩ : syracuseStep 298603 = 447905) B447905
theorem B626291 : Blo 275825 626291 := bstep (se 1 (by rfl) ⟨469718, by rfl⟩ : syracuseStep 626291 = 939437) B939437
theorem B1052311 : Blo 275825 1052311 := bstep (se 1 (by rfl) ⟨789233, by rfl⟩ : syracuseStep 1052311 = 1578467) B1578467
theorem B626327 : Blo 275825 626327 := bstep (se 1 (by rfl) ⟨469745, by rfl⟩ : syracuseStep 626327 = 939491) B939491
theorem B528115 : Blo 275825 528115 := bstep (se 1 (by rfl) ⟨396086, by rfl⟩ : syracuseStep 528115 = 792173) B792173
theorem B626507 : Blo 275825 626507 := bstep (se 1 (by rfl) ⟨469880, by rfl⟩ : syracuseStep 626507 = 939761) B939761
theorem B626561 : Blo 275825 626561 := bstep (se 2 (by rfl) ⟨234960, by rfl⟩ : syracuseStep 626561 = 469921) B469921
theorem B397271 : Blo 275825 397271 := bstep (se 1 (by rfl) ⟨297953, by rfl⟩ : syracuseStep 397271 = 595907) B595907
theorem B626777 : Blo 275825 626777 := bstep (se 2 (by rfl) ⟨235041, by rfl⟩ : syracuseStep 626777 = 470083) B470083
theorem B18157709 : Blo 275825 18157709 := bstep (se 3 (by rfl) ⟨3404570, by rfl⟩ : syracuseStep 18157709 = 6809141) B6809141
theorem B626867 : Blo 275825 626867 := bstep (se 1 (by rfl) ⟨470150, by rfl⟩ : syracuseStep 626867 = 940301) B940301
theorem B626903 : Blo 275825 626903 := bstep (se 1 (by rfl) ⟨470177, by rfl⟩ : syracuseStep 626903 = 940355) B940355
theorem B528601 : Blo 275825 528601 := bstep (se 2 (by rfl) ⟨198225, by rfl⟩ : syracuseStep 528601 = 396451) B396451
theorem B627083 : Blo 275825 627083 := bstep (se 1 (by rfl) ⟨470312, by rfl⟩ : syracuseStep 627083 = 940625) B940625
theorem B1053101 : Blo 275825 1053101 := bstep (se 3 (by rfl) ⟨197456, by rfl⟩ : syracuseStep 1053101 = 394913) B394913
theorem B627137 : Blo 275825 627137 := bstep (se 2 (by rfl) ⟨235176, by rfl⟩ : syracuseStep 627137 = 470353) B470353
theorem B627353 : Blo 275825 627353 := bstep (se 2 (by rfl) ⟨235257, by rfl⟩ : syracuseStep 627353 = 470515) B470515
theorem B627443 : Blo 275825 627443 := bstep (se 1 (by rfl) ⟨470582, by rfl⟩ : syracuseStep 627443 = 941165) B941165
theorem B529163 : Blo 275825 529163 := bstep (se 1 (by rfl) ⟨396872, by rfl⟩ : syracuseStep 529163 = 793745) B793745
theorem B627479 : Blo 275825 627479 := bstep (se 1 (by rfl) ⟨470609, by rfl⟩ : syracuseStep 627479 = 941219) B941219
theorem B529345 : Blo 275825 529345 := bstep (se 2 (by rfl) ⟨198504, by rfl⟩ : syracuseStep 529345 = 397009) B397009
theorem B627659 : Blo 275825 627659 := bstep (se 1 (by rfl) ⟨470744, by rfl⟩ : syracuseStep 627659 = 941489) B941489
theorem B627713 : Blo 275825 627713 := bstep (se 2 (by rfl) ⟨235392, by rfl⟩ : syracuseStep 627713 = 470785) B470785
theorem B594967 : Blo 275825 594967 := bstep (se 1 (by rfl) ⟨446225, by rfl⟩ : syracuseStep 594967 = 892451) B892451
theorem B791603 : Blo 275825 791603 := bstep (se 1 (by rfl) ⟨593702, by rfl⟩ : syracuseStep 791603 = 1187405) B1187405
theorem B595019 : Blo 275825 595019 := bstep (se 1 (by rfl) ⟨446264, by rfl⟩ : syracuseStep 595019 = 892529) B892529
theorem B627929 : Blo 275825 627929 := bstep (se 2 (by rfl) ⟨235473, by rfl⟩ : syracuseStep 627929 = 470947) B470947
theorem B791831 : Blo 275825 791831 := bstep (se 1 (by rfl) ⟨593873, by rfl⟩ : syracuseStep 791831 = 1187747) B1187747
theorem B628019 : Blo 275825 628019 := bstep (se 1 (by rfl) ⟨471014, by rfl⟩ : syracuseStep 628019 = 942029) B942029
theorem B628055 : Blo 275825 628055 := bstep (se 1 (by rfl) ⟨471041, by rfl⟩ : syracuseStep 628055 = 942083) B942083
theorem B4330853 : Blo 275825 4330853 := bstep (se 4 (by rfl) ⟨406017, by rfl⟩ : syracuseStep 4330853 = 812035) B812035
theorem B628235 : Blo 275825 628235 := bstep (se 1 (by rfl) ⟨471176, by rfl⟩ : syracuseStep 628235 = 942353) B942353
theorem B628289 : Blo 275825 628289 := bstep (se 2 (by rfl) ⟨235608, by rfl⟩ : syracuseStep 628289 = 471217) B471217
theorem B792139 : Blo 275825 792139 := bstep (se 1 (by rfl) ⟨594104, by rfl⟩ : syracuseStep 792139 = 1188209) B1188209
theorem B530059 : Blo 275825 530059 := bstep (se 1 (by rfl) ⟨397544, by rfl⟩ : syracuseStep 530059 = 795089) B795089
theorem B530135 : Blo 275825 530135 := bstep (se 1 (by rfl) ⟨397601, by rfl⟩ : syracuseStep 530135 = 795203) B795203
theorem B628505 : Blo 275825 628505 := bstep (se 2 (by rfl) ⟨235689, by rfl⟩ : syracuseStep 628505 = 471379) B471379
theorem B1054529 : Blo 275825 1054529 := bstep (se 2 (by rfl) ⟨395448, by rfl⟩ : syracuseStep 1054529 = 790897) B790897
theorem B792413 : Blo 275825 792413 := bstep (se 3 (by rfl) ⟨148577, by rfl⟩ : syracuseStep 792413 = 297155) B297155
theorem B628595 : Blo 275825 628595 := bstep (se 1 (by rfl) ⟨471446, by rfl⟩ : syracuseStep 628595 = 942893) B942893
theorem B628631 : Blo 275825 628631 := bstep (se 1 (by rfl) ⟨471473, by rfl⟩ : syracuseStep 628631 = 942947) B942947
theorem B8198213 : Blo 275825 8198213 := bstep (se 4 (by rfl) ⟨768582, by rfl⟩ : syracuseStep 8198213 = 1537165) B1537165
theorem B628811 : Blo 275825 628811 := bstep (se 1 (by rfl) ⟨471608, by rfl⟩ : syracuseStep 628811 = 943217) B943217
theorem B628865 : Blo 275825 628865 := bstep (se 2 (by rfl) ⟨235824, by rfl⟩ : syracuseStep 628865 = 471649) B471649
theorem B1349849 : Blo 275825 1349849 := bstep (se 2 (by rfl) ⟨506193, by rfl⟩ : syracuseStep 1349849 = 1012387) B1012387
theorem B629081 : Blo 275825 629081 := bstep (se 2 (by rfl) ⟨235905, by rfl⟩ : syracuseStep 629081 = 471811) B471811
theorem B530803 : Blo 275825 530803 := bstep (se 1 (by rfl) ⟨398102, by rfl⟩ : syracuseStep 530803 = 796205) B796205
theorem B1415555 : Blo 275825 1415555 := bstep (se 1 (by rfl) ⟨1061666, by rfl⟩ : syracuseStep 1415555 = 2123333) B2123333
theorem B629171 : Blo 275825 629171 := bstep (se 1 (by rfl) ⟨471878, by rfl⟩ : syracuseStep 629171 = 943757) B943757
theorem B629207 : Blo 275825 629207 := bstep (se 1 (by rfl) ⟨471905, by rfl⟩ : syracuseStep 629207 = 943811) B943811
theorem B531031 : Blo 275825 531031 := bstep (se 1 (by rfl) ⟨398273, by rfl⟩ : syracuseStep 531031 = 796547) B796547
theorem B465547 : Blo 275825 465547 := bstep (se 1 (by rfl) ⟨349160, by rfl⟩ : syracuseStep 465547 = 698321) B698321
theorem B629387 : Blo 275825 629387 := bstep (se 1 (by rfl) ⟨472040, by rfl⟩ : syracuseStep 629387 = 944081) B944081
theorem B596659 : Blo 275825 596659 := bstep (se 1 (by rfl) ⟨447494, by rfl⟩ : syracuseStep 596659 = 894989) B894989
theorem B629441 : Blo 275825 629441 := bstep (se 2 (by rfl) ⟨236040, by rfl⟩ : syracuseStep 629441 = 472081) B472081
theorem B531137 : Blo 275825 531137 := bstep (se 2 (by rfl) ⟨199176, by rfl⟩ : syracuseStep 531137 = 398353) B398353
theorem B465689 : Blo 275825 465689 := bstep (se 2 (by rfl) ⟨174633, by rfl⟩ : syracuseStep 465689 = 349267) B349267
theorem B498457 : Blo 275825 498457 := bstep (se 2 (by rfl) ⟨186921, by rfl⟩ : syracuseStep 498457 = 373843) B373843
theorem B10132289 : Blo 275825 10132289 := bstep (se 2 (by rfl) ⟨3799608, by rfl⟩ : syracuseStep 10132289 = 7599217) B7599217
theorem B465817 : Blo 275825 465817 := bstep (se 2 (by rfl) ⟨174681, by rfl⟩ : syracuseStep 465817 = 349363) B349363
theorem B597017 : Blo 275825 597017 := bstep (se 2 (by rfl) ⟨223881, by rfl⟩ : syracuseStep 597017 = 447763) B447763
theorem B498739 : Blo 275825 498739 := bstep (se 1 (by rfl) ⟨374054, by rfl⟩ : syracuseStep 498739 = 748109) B748109
theorem B1580107 : Blo 275825 1580107 := bstep (se 1 (by rfl) ⟨1185080, by rfl⟩ : syracuseStep 1580107 = 2370161) B2370161
theorem B498803 : Blo 275825 498803 := bstep (se 1 (by rfl) ⟨374102, by rfl⟩ : syracuseStep 498803 = 748205) B748205
theorem B1056017 : Blo 275825 1056017 := bstep (se 2 (by rfl) ⟨396006, by rfl⟩ : syracuseStep 1056017 = 792013) B792013
theorem B1580381 : Blo 275825 1580381 := bstep (se 3 (by rfl) ⟨296321, by rfl⟩ : syracuseStep 1580381 = 592643) B592643
theorem B466391 : Blo 275825 466391 := bstep (se 1 (by rfl) ⟨349793, by rfl⟩ : syracuseStep 466391 = 699587) B699587
theorem B1089089 : Blo 275825 1089089 := bstep (se 2 (by rfl) ⟨408408, by rfl⟩ : syracuseStep 1089089 = 816817) B816817
theorem B466519 : Blo 275825 466519 := bstep (se 1 (by rfl) ⟨349889, by rfl⟩ : syracuseStep 466519 = 699779) B699779
theorem B1187473 : Blo 275825 1187473 := bstep (se 2 (by rfl) ⟨445302, by rfl⟩ : syracuseStep 1187473 = 890605) B890605
theorem B1056473 : Blo 275825 1056473 := bstep (se 2 (by rfl) ⟨396177, by rfl⟩ : syracuseStep 1056473 = 792355) B792355
theorem B794519 : Blo 275825 794519 := bstep (se 1 (by rfl) ⟨595889, by rfl⟩ : syracuseStep 794519 = 1191779) B1191779
theorem B1056685 : Blo 275825 1056685 := bstep (se 3 (by rfl) ⟨198128, by rfl⟩ : syracuseStep 1056685 = 396257) B396257
theorem B39297109 : Blo 275825 39297109 := bstep (se 8 (by rfl) ⟨230256, by rfl⟩ : syracuseStep 39297109 = 460513) B460513
theorem B467147 : Blo 275825 467147 := bstep (se 1 (by rfl) ⟨350360, by rfl⟩ : syracuseStep 467147 = 700721) B700721
theorem B1056989 : Blo 275825 1056989 := bstep (se 3 (by rfl) ⟨198185, by rfl⟩ : syracuseStep 1056989 = 396371) B396371
theorem B893207 : Blo 275825 893207 := bstep (se 1 (by rfl) ⟨669905, by rfl⟩ : syracuseStep 893207 = 1339811) B1339811
theorem B467275 : Blo 275825 467275 := bstep (se 1 (by rfl) ⟨350456, by rfl⟩ : syracuseStep 467275 = 700913) B700913
theorem B467417 : Blo 275825 467417 := bstep (se 2 (by rfl) ⟨175281, by rfl⟩ : syracuseStep 467417 = 350563) B350563
theorem B1614401 : Blo 275825 1614401 := bstep (se 2 (by rfl) ⟨605400, by rfl⟩ : syracuseStep 1614401 = 1210801) B1210801
theorem B467545 : Blo 275825 467545 := bstep (se 2 (by rfl) ⟨175329, by rfl⟩ : syracuseStep 467545 = 350659) B350659
theorem B500375 : Blo 275825 500375 := bstep (se 1 (by rfl) ⟨375281, by rfl⟩ : syracuseStep 500375 = 750563) B750563
theorem B795329 : Blo 275825 795329 := bstep (se 2 (by rfl) ⟨298248, by rfl⟩ : syracuseStep 795329 = 596497) B596497
theorem B2859725 : Blo 275825 2859725 := bstep (se 3 (by rfl) ⟨536198, by rfl⟩ : syracuseStep 2859725 = 1072397) B1072397
theorem B2040677 : Blo 275825 2040677 := bstep (se 4 (by rfl) ⟨191313, by rfl⟩ : syracuseStep 2040677 = 382627) B382627
theorem B468119 : Blo 275825 468119 := bstep (se 1 (by rfl) ⟨351089, by rfl⟩ : syracuseStep 468119 = 702179) B702179
theorem B468247 : Blo 275825 468247 := bstep (se 1 (by rfl) ⟨351185, by rfl⟩ : syracuseStep 468247 = 702371) B702371
theorem B566603 : Blo 275825 566603 := bstep (se 1 (by rfl) ⟨424952, by rfl⟩ : syracuseStep 566603 = 849905) B849905
theorem B533953 : Blo 275825 533953 := bstep (se 2 (by rfl) ⟨200232, by rfl⟩ : syracuseStep 533953 = 400465) B400465
theorem B861785 : Blo 275825 861785 := bstep (se 2 (by rfl) ⟨323169, by rfl⟩ : syracuseStep 861785 = 646339) B646339
theorem B501427 : Blo 275825 501427 := bstep (se 1 (by rfl) ⟨376070, by rfl⟩ : syracuseStep 501427 = 752141) B752141
theorem B2369411 : Blo 275825 2369411 := bstep (se 1 (by rfl) ⟨1777058, by rfl⟩ : syracuseStep 2369411 = 3554117) B3554117
theorem B468875 : Blo 275825 468875 := bstep (se 1 (by rfl) ⟨351656, by rfl⟩ : syracuseStep 468875 = 703313) B703313
theorem B698291 : Blo 275825 698291 := bstep (se 1 (by rfl) ⟨523718, by rfl⟩ : syracuseStep 698291 = 1047437) B1047437
theorem B1189849 : Blo 275825 1189849 := bstep (se 2 (by rfl) ⟨446193, by rfl⟩ : syracuseStep 1189849 = 892387) B892387
theorem B469003 : Blo 275825 469003 := bstep (se 1 (by rfl) ⟨351752, by rfl⟩ : syracuseStep 469003 = 703505) B703505
theorem B501889 : Blo 275825 501889 := bstep (se 2 (by rfl) ⟨188208, by rfl⟩ : syracuseStep 501889 = 376417) B376417
theorem B469145 : Blo 275825 469145 := bstep (se 2 (by rfl) ⟨175929, by rfl⟩ : syracuseStep 469145 = 351859) B351859
theorem B469273 : Blo 275825 469273 := bstep (se 2 (by rfl) ⟨175977, by rfl⟩ : syracuseStep 469273 = 351955) B351955
theorem B502105 : Blo 275825 502105 := bstep (se 2 (by rfl) ⟨188289, by rfl⟩ : syracuseStep 502105 = 376579) B376579
theorem B698827 : Blo 275825 698827 := bstep (se 1 (by rfl) ⟨524120, by rfl⟩ : syracuseStep 698827 = 1048241) B1048241
theorem B698969 : Blo 275825 698969 := bstep (se 2 (by rfl) ⟨262113, by rfl⟩ : syracuseStep 698969 = 524227) B524227
theorem B1059587 : Blo 275825 1059587 := bstep (se 1 (by rfl) ⟨794690, by rfl⟩ : syracuseStep 1059587 = 1589381) B1589381
theorem B1059601 : Blo 275825 1059601 := bstep (se 2 (by rfl) ⟨397350, by rfl⟩ : syracuseStep 1059601 = 794701) B794701
theorem B469847 : Blo 275825 469847 := bstep (se 1 (by rfl) ⟨352385, by rfl⟩ : syracuseStep 469847 = 704771) B704771
theorem B502667 : Blo 275825 502667 := bstep (se 1 (by rfl) ⟨377000, by rfl⟩ : syracuseStep 502667 = 754001) B754001
theorem B1190807 : Blo 275825 1190807 := bstep (se 1 (by rfl) ⟨893105, by rfl⟩ : syracuseStep 1190807 = 1786211) B1786211
theorem B2010035 : Blo 275825 2010035 := bstep (se 1 (by rfl) ⟨1507526, by rfl⟩ : syracuseStep 2010035 = 3015053) B3015053
theorem B469975 : Blo 275825 469975 := bstep (se 1 (by rfl) ⟨352481, by rfl⟩ : syracuseStep 469975 = 704963) B704963
theorem B1780697 : Blo 275825 1780697 := bstep (se 2 (by rfl) ⟨667761, by rfl⟩ : syracuseStep 1780697 = 1335523) B1335523
theorem B1059905 : Blo 275825 1059905 := bstep (se 2 (by rfl) ⟨397464, by rfl⟩ : syracuseStep 1059905 = 794929) B794929
theorem B535691 : Blo 275825 535691 := bstep (se 1 (by rfl) ⟨401768, by rfl⟩ : syracuseStep 535691 = 803537) B803537
theorem B896321 : Blo 275825 896321 := bstep (se 2 (by rfl) ⟨336120, by rfl⟩ : syracuseStep 896321 = 672241) B672241
theorem B699799 : Blo 275825 699799 := bstep (se 1 (by rfl) ⟨524849, by rfl⟩ : syracuseStep 699799 = 1049699) B1049699
theorem B994781 : Blo 275825 994781 := bstep (se 3 (by rfl) ⟨186521, by rfl⟩ : syracuseStep 994781 = 373043) B373043
theorem B470603 : Blo 275825 470603 := bstep (se 1 (by rfl) ⟨352952, by rfl⟩ : syracuseStep 470603 = 705905) B705905
theorem B634547 : Blo 275825 634547 := bstep (se 1 (by rfl) ⟨475910, by rfl⟩ : syracuseStep 634547 = 951821) B951821
theorem B470731 : Blo 275825 470731 := bstep (se 1 (by rfl) ⟨353048, by rfl⟩ : syracuseStep 470731 = 706097) B706097
theorem B1060573 : Blo 275825 1060573 := bstep (se 3 (by rfl) ⟨198857, by rfl⟩ : syracuseStep 1060573 = 397715) B397715
theorem B700235 : Blo 275825 700235 := bstep (se 1 (by rfl) ⟨525176, by rfl⟩ : syracuseStep 700235 = 1050353) B1050353
theorem B470873 : Blo 275825 470873 := bstep (se 2 (by rfl) ⟨176577, by rfl⟩ : syracuseStep 470873 = 353155) B353155
theorem B503705 : Blo 275825 503705 := bstep (se 2 (by rfl) ⟨188889, by rfl⟩ : syracuseStep 503705 = 377779) B377779
theorem B10825649 : Blo 275825 10825649 := bstep (se 2 (by rfl) ⟨4059618, by rfl⟩ : syracuseStep 10825649 = 8119237) B8119237
theorem B471001 : Blo 275825 471001 := bstep (se 2 (by rfl) ⟨176625, by rfl⟩ : syracuseStep 471001 = 353251) B353251
theorem B1421405 : Blo 275825 1421405 := bstep (se 3 (by rfl) ⟨266513, by rfl⟩ : syracuseStep 1421405 = 533027) B533027
theorem B700609 : Blo 275825 700609 := bstep (se 2 (by rfl) ⟨262728, by rfl⟩ : syracuseStep 700609 = 525457) B525457
theorem B3813581 : Blo 275825 3813581 := bstep (se 3 (by rfl) ⟨715046, by rfl⟩ : syracuseStep 3813581 = 1430093) B1430093
theorem B2371801 : Blo 275825 2371801 := bstep (se 2 (by rfl) ⟨889425, by rfl⟩ : syracuseStep 2371801 = 1778851) B1778851
theorem B6041861 : Blo 275825 6041861 := bstep (se 4 (by rfl) ⟨566424, by rfl⟩ : syracuseStep 6041861 = 1132849) B1132849
theorem B3584357 : Blo 275825 3584357 := bstep (se 4 (by rfl) ⟨336033, by rfl⟩ : syracuseStep 3584357 = 672067) B672067
theorem B471575 : Blo 275825 471575 := bstep (se 1 (by rfl) ⟨353681, by rfl⟩ : syracuseStep 471575 = 707363) B707363
theorem B995905 : Blo 275825 995905 := bstep (se 2 (by rfl) ⟨373464, by rfl⟩ : syracuseStep 995905 = 746929) B746929
theorem B1782337 : Blo 275825 1782337 := bstep (se 2 (by rfl) ⟨668376, by rfl⟩ : syracuseStep 1782337 = 1336753) B1336753
theorem B1094219 : Blo 275825 1094219 := bstep (se 1 (by rfl) ⟨820664, by rfl⟩ : syracuseStep 1094219 = 1641329) B1641329
theorem B1585757 : Blo 275825 1585757 := bstep (se 3 (by rfl) ⟨297329, by rfl⟩ : syracuseStep 1585757 = 594659) B594659
theorem B471703 : Blo 275825 471703 := bstep (se 1 (by rfl) ⟨353777, by rfl⟩ : syracuseStep 471703 = 707555) B707555
theorem B701207 : Blo 275825 701207 := bstep (se 1 (by rfl) ⟨525905, by rfl⟩ : syracuseStep 701207 = 1051811) B1051811
theorem B1356695 : Blo 275825 1356695 := bstep (se 1 (by rfl) ⟨1017521, by rfl⟩ : syracuseStep 1356695 = 2035043) B2035043
theorem B1192907 : Blo 275825 1192907 := bstep (se 1 (by rfl) ⟨894680, by rfl⟩ : syracuseStep 1192907 = 1789361) B1789361
theorem B1061849 : Blo 275825 1061849 := bstep (se 2 (by rfl) ⟨398193, by rfl⟩ : syracuseStep 1061849 = 796387) B796387
theorem B537587 : Blo 275825 537587 := bstep (se 1 (by rfl) ⟨403190, by rfl⟩ : syracuseStep 537587 = 806381) B806381
theorem B635969 : Blo 275825 635969 := bstep (se 2 (by rfl) ⟨238488, by rfl⟩ : syracuseStep 635969 = 476977) B476977
theorem B2372759 : Blo 275825 2372759 := bstep (se 1 (by rfl) ⟨1779569, by rfl⟩ : syracuseStep 2372759 = 3559139) B3559139
theorem B505025 : Blo 275825 505025 := bstep (se 2 (by rfl) ⟨189384, by rfl⟩ : syracuseStep 505025 = 378769) B378769
theorem B996569 : Blo 275825 996569 := bstep (se 2 (by rfl) ⟨373713, by rfl⟩ : syracuseStep 996569 = 747427) B747427
theorem B3814721 : Blo 275825 3814721 := bstep (se 2 (by rfl) ⟨1430520, by rfl⟩ : syracuseStep 3814721 = 2861041) B2861041
theorem B275831 : Blo 275825 275831 := bstep (se 1 (by rfl) ⟨206873, by rfl⟩ : syracuseStep 275831 = 413747) B413747
theorem B275851 : Blo 275825 275851 := bstep (se 1 (by rfl) ⟨206888, by rfl⟩ : syracuseStep 275851 = 413777) B413777
theorem B275863 : Blo 275825 275863 := bstep (se 1 (by rfl) ⟨206897, by rfl⟩ : syracuseStep 275863 = 413795) B413795
theorem B275883 : Blo 275825 275883 := bstep (se 1 (by rfl) ⟨206912, by rfl⟩ : syracuseStep 275883 = 413825) B413825
theorem B275895 : Blo 275825 275895 := bstep (se 1 (by rfl) ⟨206921, by rfl⟩ : syracuseStep 275895 = 413843) B413843
theorem B275915 : Blo 275825 275915 := bstep (se 1 (by rfl) ⟨206936, by rfl⟩ : syracuseStep 275915 = 413873) B413873
theorem B275927 : Blo 275825 275927 := bstep (se 1 (by rfl) ⟨206945, by rfl⟩ : syracuseStep 275927 = 413891) B413891
theorem B275947 : Blo 275825 275947 := bstep (se 1 (by rfl) ⟨206960, by rfl⟩ : syracuseStep 275947 = 413921) B413921
theorem B275959 : Blo 275825 275959 := bstep (se 1 (by rfl) ⟨206969, by rfl⟩ : syracuseStep 275959 = 413939) B413939
theorem B275979 : Blo 275825 275979 := bstep (se 1 (by rfl) ⟨206984, by rfl⟩ : syracuseStep 275979 = 413969) B413969
theorem B2668049 : Blo 275825 2668049 := bstep (se 2 (by rfl) ⟨1000518, by rfl⟩ : syracuseStep 2668049 = 2001037) B2001037
theorem B2373137 : Blo 275825 2373137 := bstep (se 2 (by rfl) ⟨889926, by rfl⟩ : syracuseStep 2373137 = 1779853) B1779853
theorem B275991 : Blo 275825 275991 := bstep (se 1 (by rfl) ⟨206993, by rfl⟩ : syracuseStep 275991 = 413987) B413987
theorem B276011 : Blo 275825 276011 := bstep (se 1 (by rfl) ⟨207008, by rfl⟩ : syracuseStep 276011 = 414017) B414017
theorem B276023 : Blo 275825 276023 := bstep (se 1 (by rfl) ⟨207017, by rfl⟩ : syracuseStep 276023 = 414035) B414035
theorem B702017 : Blo 275825 702017 := bstep (se 2 (by rfl) ⟨263256, by rfl⟩ : syracuseStep 702017 = 526513) B526513
theorem B276043 : Blo 275825 276043 := bstep (se 1 (by rfl) ⟨207032, by rfl⟩ : syracuseStep 276043 = 414065) B414065
theorem B276055 : Blo 275825 276055 := bstep (se 1 (by rfl) ⟨207041, by rfl⟩ : syracuseStep 276055 = 414083) B414083
theorem B276075 : Blo 275825 276075 := bstep (se 1 (by rfl) ⟨207056, by rfl⟩ : syracuseStep 276075 = 414113) B414113
theorem B276087 : Blo 275825 276087 := bstep (se 1 (by rfl) ⟨207065, by rfl⟩ : syracuseStep 276087 = 414131) B414131
theorem B276107 : Blo 275825 276107 := bstep (se 1 (by rfl) ⟨207080, by rfl⟩ : syracuseStep 276107 = 414161) B414161
theorem B276119 : Blo 275825 276119 := bstep (se 1 (by rfl) ⟨207089, by rfl⟩ : syracuseStep 276119 = 414179) B414179
theorem B276139 : Blo 275825 276139 := bstep (se 1 (by rfl) ⟨207104, by rfl⟩ : syracuseStep 276139 = 414209) B414209
theorem B276151 : Blo 275825 276151 := bstep (se 1 (by rfl) ⟨207113, by rfl⟩ : syracuseStep 276151 = 414227) B414227
theorem B669377 : Blo 275825 669377 := bstep (se 2 (by rfl) ⟨251016, by rfl⟩ : syracuseStep 669377 = 502033) B502033
theorem B276171 : Blo 275825 276171 := bstep (se 1 (by rfl) ⟨207128, by rfl⟩ : syracuseStep 276171 = 414257) B414257
theorem B636619 : Blo 275825 636619 := bstep (se 1 (by rfl) ⟨477464, by rfl⟩ : syracuseStep 636619 = 954929) B954929
theorem B276183 : Blo 275825 276183 := bstep (se 1 (by rfl) ⟨207137, by rfl⟩ : syracuseStep 276183 = 414275) B414275
theorem B276203 : Blo 275825 276203 := bstep (se 1 (by rfl) ⟨207152, by rfl⟩ : syracuseStep 276203 = 414305) B414305
theorem B276215 : Blo 275825 276215 := bstep (se 1 (by rfl) ⟨207161, by rfl⟩ : syracuseStep 276215 = 414323) B414323
theorem B276235 : Blo 275825 276235 := bstep (se 1 (by rfl) ⟨207176, by rfl⟩ : syracuseStep 276235 = 414353) B414353
theorem B931607 : Blo 275825 931607 := bstep (se 1 (by rfl) ⟨698705, by rfl⟩ : syracuseStep 931607 = 1397411) B1397411
theorem B276247 : Blo 275825 276247 := bstep (se 1 (by rfl) ⟨207185, by rfl⟩ : syracuseStep 276247 = 414371) B414371
theorem B2406179 : Blo 275825 2406179 := bstep (se 1 (by rfl) ⟨1804634, by rfl⟩ : syracuseStep 2406179 = 3609269) B3609269
theorem B276267 : Blo 275825 276267 := bstep (se 1 (by rfl) ⟨207200, by rfl⟩ : syracuseStep 276267 = 414401) B414401
theorem B276279 : Blo 275825 276279 := bstep (se 1 (by rfl) ⟨207209, by rfl⟩ : syracuseStep 276279 = 414419) B414419
theorem B276299 : Blo 275825 276299 := bstep (se 1 (by rfl) ⟨207224, by rfl⟩ : syracuseStep 276299 = 414449) B414449
theorem B276311 : Blo 275825 276311 := bstep (se 1 (by rfl) ⟨207233, by rfl⟩ : syracuseStep 276311 = 414467) B414467
theorem B276331 : Blo 275825 276331 := bstep (se 1 (by rfl) ⟨207248, by rfl⟩ : syracuseStep 276331 = 414497) B414497
theorem B276343 : Blo 275825 276343 := bstep (se 1 (by rfl) ⟨207257, by rfl⟩ : syracuseStep 276343 = 414515) B414515
theorem B276363 : Blo 275825 276363 := bstep (se 1 (by rfl) ⟨207272, by rfl⟩ : syracuseStep 276363 = 414545) B414545
theorem B276375 : Blo 275825 276375 := bstep (se 1 (by rfl) ⟨207281, by rfl⟩ : syracuseStep 276375 = 414563) B414563
theorem B604055 : Blo 275825 604055 := bstep (se 1 (by rfl) ⟨453041, by rfl⟩ : syracuseStep 604055 = 906083) B906083
theorem B276395 : Blo 275825 276395 := bstep (se 1 (by rfl) ⟨207296, by rfl⟩ : syracuseStep 276395 = 414593) B414593
theorem B2144179 : Blo 275825 2144179 := bstep (se 1 (by rfl) ⟨1608134, by rfl⟩ : syracuseStep 2144179 = 3216269) B3216269
theorem B276407 : Blo 275825 276407 := bstep (se 1 (by rfl) ⟨207305, by rfl⟩ : syracuseStep 276407 = 414611) B414611
theorem B276427 : Blo 275825 276427 := bstep (se 1 (by rfl) ⟨207320, by rfl⟩ : syracuseStep 276427 = 414641) B414641
theorem B276439 : Blo 275825 276439 := bstep (se 1 (by rfl) ⟨207329, by rfl⟩ : syracuseStep 276439 = 414659) B414659
theorem B276459 : Blo 275825 276459 := bstep (se 1 (by rfl) ⟨207344, by rfl⟩ : syracuseStep 276459 = 414689) B414689
theorem B276471 : Blo 275825 276471 := bstep (se 1 (by rfl) ⟨207353, by rfl⟩ : syracuseStep 276471 = 414707) B414707
theorem B276491 : Blo 275825 276491 := bstep (se 1 (by rfl) ⟨207368, by rfl⟩ : syracuseStep 276491 = 414737) B414737
theorem B276503 : Blo 275825 276503 := bstep (se 1 (by rfl) ⟨207377, by rfl⟩ : syracuseStep 276503 = 414755) B414755
theorem B276523 : Blo 275825 276523 := bstep (se 1 (by rfl) ⟨207392, by rfl⟩ : syracuseStep 276523 = 414785) B414785
theorem B276535 : Blo 275825 276535 := bstep (se 1 (by rfl) ⟨207401, by rfl⟩ : syracuseStep 276535 = 414803) B414803
theorem B276555 : Blo 275825 276555 := bstep (se 1 (by rfl) ⟨207416, by rfl⟩ : syracuseStep 276555 = 414833) B414833
theorem B276567 : Blo 275825 276567 := bstep (se 1 (by rfl) ⟨207425, by rfl⟩ : syracuseStep 276567 = 414851) B414851
theorem B702553 : Blo 275825 702553 := bstep (se 2 (by rfl) ⟨263457, by rfl⟩ : syracuseStep 702553 = 526915) B526915
theorem B276587 : Blo 275825 276587 := bstep (se 1 (by rfl) ⟨207440, by rfl⟩ : syracuseStep 276587 = 414881) B414881
theorem B276599 : Blo 275825 276599 := bstep (se 1 (by rfl) ⟨207449, by rfl⟩ : syracuseStep 276599 = 414899) B414899
theorem B276619 : Blo 275825 276619 := bstep (se 1 (by rfl) ⟨207464, by rfl⟩ : syracuseStep 276619 = 414929) B414929
theorem B276631 : Blo 275825 276631 := bstep (se 1 (by rfl) ⟨207473, by rfl⟩ : syracuseStep 276631 = 414947) B414947
theorem B276651 : Blo 275825 276651 := bstep (se 1 (by rfl) ⟨207488, by rfl⟩ : syracuseStep 276651 = 414977) B414977
theorem B571571 : Blo 275825 571571 := bstep (se 1 (by rfl) ⟨428678, by rfl⟩ : syracuseStep 571571 = 857357) B857357
theorem B276663 : Blo 275825 276663 := bstep (se 1 (by rfl) ⟨207497, by rfl⟩ : syracuseStep 276663 = 414995) B414995
theorem B276683 : Blo 275825 276683 := bstep (se 1 (by rfl) ⟨207512, by rfl⟩ : syracuseStep 276683 = 415025) B415025
theorem B276695 : Blo 275825 276695 := bstep (se 1 (by rfl) ⟨207521, by rfl⟩ : syracuseStep 276695 = 415043) B415043
theorem B276715 : Blo 275825 276715 := bstep (se 1 (by rfl) ⟨207536, by rfl⟩ : syracuseStep 276715 = 415073) B415073
theorem B276727 : Blo 275825 276727 := bstep (se 1 (by rfl) ⟨207545, by rfl⟩ : syracuseStep 276727 = 415091) B415091
theorem B276747 : Blo 275825 276747 := bstep (se 1 (by rfl) ⟨207560, by rfl⟩ : syracuseStep 276747 = 415121) B415121
theorem B276759 : Blo 275825 276759 := bstep (se 1 (by rfl) ⟨207569, by rfl⟩ : syracuseStep 276759 = 415139) B415139
theorem B276779 : Blo 275825 276779 := bstep (se 1 (by rfl) ⟨207584, by rfl⟩ : syracuseStep 276779 = 415169) B415169
theorem B932147 : Blo 275825 932147 := bstep (se 1 (by rfl) ⟨699110, by rfl⟩ : syracuseStep 932147 = 1398221) B1398221
theorem B276791 : Blo 275825 276791 := bstep (se 1 (by rfl) ⟨207593, by rfl⟩ : syracuseStep 276791 = 415187) B415187
theorem B276811 : Blo 275825 276811 := bstep (se 1 (by rfl) ⟨207608, by rfl⟩ : syracuseStep 276811 = 415217) B415217
theorem B276823 : Blo 275825 276823 := bstep (se 1 (by rfl) ⟨207617, by rfl⟩ : syracuseStep 276823 = 415235) B415235
theorem B276843 : Blo 275825 276843 := bstep (se 1 (by rfl) ⟨207632, by rfl⟩ : syracuseStep 276843 = 415265) B415265
theorem B276855 : Blo 275825 276855 := bstep (se 1 (by rfl) ⟨207641, by rfl⟩ : syracuseStep 276855 = 415283) B415283
theorem B276875 : Blo 275825 276875 := bstep (se 1 (by rfl) ⟨207656, by rfl⟩ : syracuseStep 276875 = 415313) B415313
theorem B276887 : Blo 275825 276887 := bstep (se 1 (by rfl) ⟨207665, by rfl⟩ : syracuseStep 276887 = 415331) B415331
theorem B276907 : Blo 275825 276907 := bstep (se 1 (by rfl) ⟨207680, by rfl⟩ : syracuseStep 276907 = 415361) B415361
theorem B276919 : Blo 275825 276919 := bstep (se 1 (by rfl) ⟨207689, by rfl⟩ : syracuseStep 276919 = 415379) B415379
theorem B276939 : Blo 275825 276939 := bstep (se 1 (by rfl) ⟨207704, by rfl⟩ : syracuseStep 276939 = 415409) B415409
theorem B276951 : Blo 275825 276951 := bstep (se 1 (by rfl) ⟨207713, by rfl⟩ : syracuseStep 276951 = 415427) B415427
theorem B276971 : Blo 275825 276971 := bstep (se 1 (by rfl) ⟨207728, by rfl⟩ : syracuseStep 276971 = 415457) B415457
theorem B276983 : Blo 275825 276983 := bstep (se 1 (by rfl) ⟨207737, by rfl⟩ : syracuseStep 276983 = 415475) B415475
theorem B277003 : Blo 275825 277003 := bstep (se 1 (by rfl) ⟨207752, by rfl⟩ : syracuseStep 277003 = 415505) B415505
theorem B277015 : Blo 275825 277015 := bstep (se 1 (by rfl) ⟨207761, by rfl⟩ : syracuseStep 277015 = 415523) B415523
theorem B3389987 : Blo 275825 3389987 := bstep (se 1 (by rfl) ⟨2542490, by rfl⟩ : syracuseStep 3389987 = 5084981) B5084981
theorem B277035 : Blo 275825 277035 := bstep (se 1 (by rfl) ⟨207776, by rfl⟩ : syracuseStep 277035 = 415553) B415553
theorem B1194547 : Blo 275825 1194547 := bstep (se 1 (by rfl) ⟨895910, by rfl⟩ : syracuseStep 1194547 = 1791821) B1791821
theorem B277047 : Blo 275825 277047 := bstep (se 1 (by rfl) ⟨207785, by rfl⟩ : syracuseStep 277047 = 415571) B415571
theorem B932417 : Blo 275825 932417 := bstep (se 2 (by rfl) ⟨349656, by rfl⟩ : syracuseStep 932417 = 699313) B699313
theorem B277067 : Blo 275825 277067 := bstep (se 1 (by rfl) ⟨207800, by rfl⟩ : syracuseStep 277067 = 415601) B415601
theorem B277079 : Blo 275825 277079 := bstep (se 1 (by rfl) ⟨207809, by rfl⟩ : syracuseStep 277079 = 415619) B415619
theorem B277099 : Blo 275825 277099 := bstep (se 1 (by rfl) ⟨207824, by rfl⟩ : syracuseStep 277099 = 415649) B415649
theorem B277111 : Blo 275825 277111 := bstep (se 1 (by rfl) ⟨207833, by rfl⟩ : syracuseStep 277111 = 415667) B415667
theorem B277131 : Blo 275825 277131 := bstep (se 1 (by rfl) ⟨207848, by rfl⟩ : syracuseStep 277131 = 415697) B415697
theorem B277143 : Blo 275825 277143 := bstep (se 1 (by rfl) ⟨207857, by rfl⟩ : syracuseStep 277143 = 415715) B415715
theorem B1686167 : Blo 275825 1686167 := bstep (se 1 (by rfl) ⟨1264625, by rfl⟩ : syracuseStep 1686167 = 2529251) B2529251
theorem B277163 : Blo 275825 277163 := bstep (se 1 (by rfl) ⟨207872, by rfl⟩ : syracuseStep 277163 = 415745) B415745
theorem B277175 : Blo 275825 277175 := bstep (se 1 (by rfl) ⟨207881, by rfl⟩ : syracuseStep 277175 = 415763) B415763
theorem B277195 : Blo 275825 277195 := bstep (se 1 (by rfl) ⟨207896, by rfl⟩ : syracuseStep 277195 = 415793) B415793
theorem B277207 : Blo 275825 277207 := bstep (se 1 (by rfl) ⟨207905, by rfl⟩ : syracuseStep 277207 = 415811) B415811
theorem B277227 : Blo 275825 277227 := bstep (se 1 (by rfl) ⟨207920, by rfl⟩ : syracuseStep 277227 = 415841) B415841
theorem B277239 : Blo 275825 277239 := bstep (se 1 (by rfl) ⟨207929, by rfl⟩ : syracuseStep 277239 = 415859) B415859
theorem B277259 : Blo 275825 277259 := bstep (se 1 (by rfl) ⟨207944, by rfl⟩ : syracuseStep 277259 = 415889) B415889
theorem B277271 : Blo 275825 277271 := bstep (se 1 (by rfl) ⟨207953, by rfl⟩ : syracuseStep 277271 = 415907) B415907
theorem B277291 : Blo 275825 277291 := bstep (se 1 (by rfl) ⟨207968, by rfl⟩ : syracuseStep 277291 = 415937) B415937
theorem B277303 : Blo 275825 277303 := bstep (se 1 (by rfl) ⟨207977, by rfl⟩ : syracuseStep 277303 = 415955) B415955
theorem B277323 : Blo 275825 277323 := bstep (se 1 (by rfl) ⟨207992, by rfl⟩ : syracuseStep 277323 = 415985) B415985
theorem B277335 : Blo 275825 277335 := bstep (se 1 (by rfl) ⟨208001, by rfl⟩ : syracuseStep 277335 = 416003) B416003
theorem B277355 : Blo 275825 277355 := bstep (se 1 (by rfl) ⟨208016, by rfl⟩ : syracuseStep 277355 = 416033) B416033
theorem B277367 : Blo 275825 277367 := bstep (se 1 (by rfl) ⟨208025, by rfl⟩ : syracuseStep 277367 = 416051) B416051
theorem B277387 : Blo 275825 277387 := bstep (se 1 (by rfl) ⟨208040, by rfl⟩ : syracuseStep 277387 = 416081) B416081
theorem B277399 : Blo 275825 277399 := bstep (se 1 (by rfl) ⟨208049, by rfl⟩ : syracuseStep 277399 = 416099) B416099
theorem B277419 : Blo 275825 277419 := bstep (se 1 (by rfl) ⟨208064, by rfl⟩ : syracuseStep 277419 = 416129) B416129
theorem B277431 : Blo 275825 277431 := bstep (se 1 (by rfl) ⟨208073, by rfl⟩ : syracuseStep 277431 = 416147) B416147
theorem B277451 : Blo 275825 277451 := bstep (se 1 (by rfl) ⟨208088, by rfl⟩ : syracuseStep 277451 = 416177) B416177
theorem B277463 : Blo 275825 277463 := bstep (se 1 (by rfl) ⟨208097, by rfl⟩ : syracuseStep 277463 = 416195) B416195
theorem B277483 : Blo 275825 277483 := bstep (se 1 (by rfl) ⟨208112, by rfl⟩ : syracuseStep 277483 = 416225) B416225
theorem B277495 : Blo 275825 277495 := bstep (se 1 (by rfl) ⟨208121, by rfl⟩ : syracuseStep 277495 = 416243) B416243
theorem B277515 : Blo 275825 277515 := bstep (se 1 (by rfl) ⟨208136, by rfl⟩ : syracuseStep 277515 = 416273) B416273
theorem B277527 : Blo 275825 277527 := bstep (se 1 (by rfl) ⟨208145, by rfl⟩ : syracuseStep 277527 = 416291) B416291
theorem B310315 : Blo 275825 310315 := bstep (se 1 (by rfl) ⟨232736, by rfl⟩ : syracuseStep 310315 = 465473) B465473
theorem B277547 : Blo 275825 277547 := bstep (se 1 (by rfl) ⟨208160, by rfl⟩ : syracuseStep 277547 = 416321) B416321
theorem B277559 : Blo 275825 277559 := bstep (se 1 (by rfl) ⟨208169, by rfl⟩ : syracuseStep 277559 = 416339) B416339
theorem B277579 : Blo 275825 277579 := bstep (se 1 (by rfl) ⟨208184, by rfl⟩ : syracuseStep 277579 = 416369) B416369
theorem B277591 : Blo 275825 277591 := bstep (se 1 (by rfl) ⟨208193, by rfl⟩ : syracuseStep 277591 = 416387) B416387
theorem B932957 : Blo 275825 932957 := bstep (se 3 (by rfl) ⟨174929, by rfl⟩ : syracuseStep 932957 = 349859) B349859
theorem B277611 : Blo 275825 277611 := bstep (se 1 (by rfl) ⟨208208, by rfl⟩ : syracuseStep 277611 = 416417) B416417
theorem B277623 : Blo 275825 277623 := bstep (se 1 (by rfl) ⟨208217, by rfl⟩ : syracuseStep 277623 = 416435) B416435
theorem B1588355 : Blo 275825 1588355 := bstep (se 1 (by rfl) ⟨1191266, by rfl⟩ : syracuseStep 1588355 = 2382533) B2382533
theorem B277643 : Blo 275825 277643 := bstep (se 1 (by rfl) ⟨208232, by rfl⟩ : syracuseStep 277643 = 416465) B416465
theorem B5717143 : Blo 275825 5717143 := bstep (se 1 (by rfl) ⟨4287857, by rfl⟩ : syracuseStep 5717143 = 8575715) B8575715
theorem B310423 : Blo 275825 310423 := bstep (se 1 (by rfl) ⟨232817, by rfl⟩ : syracuseStep 310423 = 465635) B465635
theorem B277655 : Blo 275825 277655 := bstep (se 1 (by rfl) ⟨208241, by rfl⟩ : syracuseStep 277655 = 416483) B416483
theorem B277675 : Blo 275825 277675 := bstep (se 1 (by rfl) ⟨208256, by rfl⟩ : syracuseStep 277675 = 416513) B416513
theorem B1195181 : Blo 275825 1195181 := bstep (se 3 (by rfl) ⟨224096, by rfl⟩ : syracuseStep 1195181 = 448193) B448193
theorem B703667 : Blo 275825 703667 := bstep (se 1 (by rfl) ⟨527750, by rfl⟩ : syracuseStep 703667 = 1055501) B1055501
theorem B277687 : Blo 275825 277687 := bstep (se 1 (by rfl) ⟨208265, by rfl⟩ : syracuseStep 277687 = 416531) B416531
theorem B277707 : Blo 275825 277707 := bstep (se 1 (by rfl) ⟨208280, by rfl⟩ : syracuseStep 277707 = 416561) B416561
theorem B277719 : Blo 275825 277719 := bstep (se 1 (by rfl) ⟨208289, by rfl⟩ : syracuseStep 277719 = 416579) B416579
theorem B277739 : Blo 275825 277739 := bstep (se 1 (by rfl) ⟨208304, by rfl⟩ : syracuseStep 277739 = 416609) B416609
theorem B277751 : Blo 275825 277751 := bstep (se 1 (by rfl) ⟨208313, by rfl⟩ : syracuseStep 277751 = 416627) B416627
theorem B277771 : Blo 275825 277771 := bstep (se 1 (by rfl) ⟨208328, by rfl⟩ : syracuseStep 277771 = 416657) B416657
theorem B277783 : Blo 275825 277783 := bstep (se 1 (by rfl) ⟨208337, by rfl⟩ : syracuseStep 277783 = 416675) B416675
theorem B277803 : Blo 275825 277803 := bstep (se 1 (by rfl) ⟨208352, by rfl⟩ : syracuseStep 277803 = 416705) B416705
theorem B277815 : Blo 275825 277815 := bstep (se 1 (by rfl) ⟨208361, by rfl⟩ : syracuseStep 277815 = 416723) B416723
theorem B310603 : Blo 275825 310603 := bstep (se 1 (by rfl) ⟨232952, by rfl⟩ : syracuseStep 310603 = 465905) B465905
theorem B277835 : Blo 275825 277835 := bstep (se 1 (by rfl) ⟨208376, by rfl⟩ : syracuseStep 277835 = 416753) B416753
theorem B277847 : Blo 275825 277847 := bstep (se 1 (by rfl) ⟨208385, by rfl⟩ : syracuseStep 277847 = 416771) B416771
theorem B277867 : Blo 275825 277867 := bstep (se 1 (by rfl) ⟨208400, by rfl⟩ : syracuseStep 277867 = 416801) B416801
theorem B277879 : Blo 275825 277879 := bstep (se 1 (by rfl) ⟨208409, by rfl⟩ : syracuseStep 277879 = 416819) B416819
theorem B277899 : Blo 275825 277899 := bstep (se 1 (by rfl) ⟨208424, by rfl⟩ : syracuseStep 277899 = 416849) B416849
theorem B277911 : Blo 275825 277911 := bstep (se 1 (by rfl) ⟨208433, by rfl⟩ : syracuseStep 277911 = 416867) B416867
theorem B277931 : Blo 275825 277931 := bstep (se 1 (by rfl) ⟨208448, by rfl⟩ : syracuseStep 277931 = 416897) B416897
theorem B310711 : Blo 275825 310711 := bstep (se 1 (by rfl) ⟨233033, by rfl⟩ : syracuseStep 310711 = 466067) B466067
theorem B277943 : Blo 275825 277943 := bstep (se 1 (by rfl) ⟨208457, by rfl⟩ : syracuseStep 277943 = 416915) B416915
theorem B277963 : Blo 275825 277963 := bstep (se 1 (by rfl) ⟨208472, by rfl⟩ : syracuseStep 277963 = 416945) B416945
theorem B277975 : Blo 275825 277975 := bstep (se 1 (by rfl) ⟨208481, by rfl⟩ : syracuseStep 277975 = 416963) B416963
theorem B703961 : Blo 275825 703961 := bstep (se 2 (by rfl) ⟨263985, by rfl⟩ : syracuseStep 703961 = 527971) B527971
theorem B277995 : Blo 275825 277995 := bstep (se 1 (by rfl) ⟨208496, by rfl⟩ : syracuseStep 277995 = 416993) B416993
theorem B278007 : Blo 275825 278007 := bstep (se 1 (by rfl) ⟨208505, by rfl⟩ : syracuseStep 278007 = 417011) B417011
theorem B278027 : Blo 275825 278027 := bstep (se 1 (by rfl) ⟨208520, by rfl⟩ : syracuseStep 278027 = 417041) B417041
theorem B278039 : Blo 275825 278039 := bstep (se 1 (by rfl) ⟨208529, by rfl⟩ : syracuseStep 278039 = 417059) B417059
theorem B278059 : Blo 275825 278059 := bstep (se 1 (by rfl) ⟨208544, by rfl⟩ : syracuseStep 278059 = 417089) B417089
theorem B278071 : Blo 275825 278071 := bstep (se 1 (by rfl) ⟨208553, by rfl⟩ : syracuseStep 278071 = 417107) B417107
theorem B278091 : Blo 275825 278091 := bstep (se 1 (by rfl) ⟨208568, by rfl⟩ : syracuseStep 278091 = 417137) B417137
theorem B278103 : Blo 275825 278103 := bstep (se 1 (by rfl) ⟨208577, by rfl⟩ : syracuseStep 278103 = 417155) B417155
theorem B310891 : Blo 275825 310891 := bstep (se 1 (by rfl) ⟨233168, by rfl⟩ : syracuseStep 310891 = 466337) B466337
theorem B278123 : Blo 275825 278123 := bstep (se 1 (by rfl) ⟨208592, by rfl⟩ : syracuseStep 278123 = 417185) B417185
theorem B278135 : Blo 275825 278135 := bstep (se 1 (by rfl) ⟨208601, by rfl⟩ : syracuseStep 278135 = 417203) B417203
theorem B278155 : Blo 275825 278155 := bstep (se 1 (by rfl) ⟨208616, by rfl⟩ : syracuseStep 278155 = 417233) B417233
theorem B278167 : Blo 275825 278167 := bstep (se 1 (by rfl) ⟨208625, by rfl⟩ : syracuseStep 278167 = 417251) B417251
theorem B278187 : Blo 275825 278187 := bstep (se 1 (by rfl) ⟨208640, by rfl⟩ : syracuseStep 278187 = 417281) B417281
theorem B278199 : Blo 275825 278199 := bstep (se 1 (by rfl) ⟨208649, by rfl⟩ : syracuseStep 278199 = 417299) B417299
theorem B278219 : Blo 275825 278219 := bstep (se 1 (by rfl) ⟨208664, by rfl⟩ : syracuseStep 278219 = 417329) B417329
theorem B310999 : Blo 275825 310999 := bstep (se 1 (by rfl) ⟨233249, by rfl⟩ : syracuseStep 310999 = 466499) B466499
theorem B278231 : Blo 275825 278231 := bstep (se 1 (by rfl) ⟨208673, by rfl⟩ : syracuseStep 278231 = 417347) B417347
theorem B278251 : Blo 275825 278251 := bstep (se 1 (by rfl) ⟨208688, by rfl⟩ : syracuseStep 278251 = 417377) B417377
theorem B278263 : Blo 275825 278263 := bstep (se 1 (by rfl) ⟨208697, by rfl⟩ : syracuseStep 278263 = 417395) B417395
theorem B278283 : Blo 275825 278283 := bstep (se 1 (by rfl) ⟨208712, by rfl⟩ : syracuseStep 278283 = 417425) B417425
theorem B278295 : Blo 275825 278295 := bstep (se 1 (by rfl) ⟨208721, by rfl⟩ : syracuseStep 278295 = 417443) B417443
theorem B278315 : Blo 275825 278315 := bstep (se 1 (by rfl) ⟨208736, by rfl⟩ : syracuseStep 278315 = 417473) B417473
theorem B278327 : Blo 275825 278327 := bstep (se 1 (by rfl) ⟨208745, by rfl⟩ : syracuseStep 278327 = 417491) B417491
theorem B278347 : Blo 275825 278347 := bstep (se 1 (by rfl) ⟨208760, by rfl⟩ : syracuseStep 278347 = 417521) B417521
theorem B278359 : Blo 275825 278359 := bstep (se 1 (by rfl) ⟨208769, by rfl⟩ : syracuseStep 278359 = 417539) B417539
theorem B278379 : Blo 275825 278379 := bstep (se 1 (by rfl) ⟨208784, by rfl⟩ : syracuseStep 278379 = 417569) B417569
theorem B278391 : Blo 275825 278391 := bstep (se 1 (by rfl) ⟨208793, by rfl⟩ : syracuseStep 278391 = 417587) B417587
theorem B311179 : Blo 275825 311179 := bstep (se 1 (by rfl) ⟨233384, by rfl⟩ : syracuseStep 311179 = 466769) B466769
theorem B278411 : Blo 275825 278411 := bstep (se 1 (by rfl) ⟨208808, by rfl⟩ : syracuseStep 278411 = 417617) B417617
theorem B278423 : Blo 275825 278423 := bstep (se 1 (by rfl) ⟨208817, by rfl⟩ : syracuseStep 278423 = 417635) B417635
theorem B278443 : Blo 275825 278443 := bstep (se 1 (by rfl) ⟨208832, by rfl⟩ : syracuseStep 278443 = 417665) B417665
theorem B278455 : Blo 275825 278455 := bstep (se 1 (by rfl) ⟨208841, by rfl⟩ : syracuseStep 278455 = 417683) B417683
theorem B278475 : Blo 275825 278475 := bstep (se 1 (by rfl) ⟨208856, by rfl⟩ : syracuseStep 278475 = 417713) B417713
theorem B278487 : Blo 275825 278487 := bstep (se 1 (by rfl) ⟨208865, by rfl⟩ : syracuseStep 278487 = 417731) B417731
theorem B278507 : Blo 275825 278507 := bstep (se 1 (by rfl) ⟨208880, by rfl⟩ : syracuseStep 278507 = 417761) B417761
theorem B278519 : Blo 275825 278519 := bstep (se 1 (by rfl) ⟨208889, by rfl⟩ : syracuseStep 278519 = 417779) B417779
theorem B311287 : Blo 275825 311287 := bstep (se 1 (by rfl) ⟨233465, by rfl⟩ : syracuseStep 311287 = 466931) B466931
theorem B278539 : Blo 275825 278539 := bstep (se 1 (by rfl) ⟨208904, by rfl⟩ : syracuseStep 278539 = 417809) B417809
theorem B278551 : Blo 275825 278551 := bstep (se 1 (by rfl) ⟨208913, by rfl⟩ : syracuseStep 278551 = 417827) B417827
theorem B278571 : Blo 275825 278571 := bstep (se 1 (by rfl) ⟨208928, by rfl⟩ : syracuseStep 278571 = 417857) B417857
theorem B278583 : Blo 275825 278583 := bstep (se 1 (by rfl) ⟨208937, by rfl⟩ : syracuseStep 278583 = 417875) B417875
theorem B278603 : Blo 275825 278603 := bstep (se 1 (by rfl) ⟨208952, by rfl⟩ : syracuseStep 278603 = 417905) B417905
theorem B278615 : Blo 275825 278615 := bstep (se 1 (by rfl) ⟨208961, by rfl⟩ : syracuseStep 278615 = 417923) B417923
theorem B278635 : Blo 275825 278635 := bstep (se 1 (by rfl) ⟨208976, by rfl⟩ : syracuseStep 278635 = 417953) B417953
theorem B278647 : Blo 275825 278647 := bstep (se 1 (by rfl) ⟨208985, by rfl⟩ : syracuseStep 278647 = 417971) B417971
theorem B278667 : Blo 275825 278667 := bstep (se 1 (by rfl) ⟨209000, by rfl⟩ : syracuseStep 278667 = 418001) B418001
theorem B278679 : Blo 275825 278679 := bstep (se 1 (by rfl) ⟨209009, by rfl⟩ : syracuseStep 278679 = 418019) B418019
theorem B311467 : Blo 275825 311467 := bstep (se 1 (by rfl) ⟨233600, by rfl⟩ : syracuseStep 311467 = 467201) B467201
theorem B278699 : Blo 275825 278699 := bstep (se 1 (by rfl) ⟨209024, by rfl⟩ : syracuseStep 278699 = 418049) B418049
theorem B278711 : Blo 275825 278711 := bstep (se 1 (by rfl) ⟨209033, by rfl⟩ : syracuseStep 278711 = 418067) B418067
theorem B934091 : Blo 275825 934091 := bstep (se 1 (by rfl) ⟨700568, by rfl⟩ : syracuseStep 934091 = 1401137) B1401137
theorem B278731 : Blo 275825 278731 := bstep (se 1 (by rfl) ⟨209048, by rfl⟩ : syracuseStep 278731 = 418097) B418097
theorem B278743 : Blo 275825 278743 := bstep (se 1 (by rfl) ⟨209057, by rfl⟩ : syracuseStep 278743 = 418115) B418115
theorem B278763 : Blo 275825 278763 := bstep (se 1 (by rfl) ⟨209072, by rfl⟩ : syracuseStep 278763 = 418145) B418145
theorem B278775 : Blo 275825 278775 := bstep (se 1 (by rfl) ⟨209081, by rfl⟩ : syracuseStep 278775 = 418163) B418163
theorem B278795 : Blo 275825 278795 := bstep (se 1 (by rfl) ⟨209096, by rfl⟩ : syracuseStep 278795 = 418193) B418193
theorem B311575 : Blo 275825 311575 := bstep (se 1 (by rfl) ⟨233681, by rfl⟩ : syracuseStep 311575 = 467363) B467363
theorem B278807 : Blo 275825 278807 := bstep (se 1 (by rfl) ⟨209105, by rfl⟩ : syracuseStep 278807 = 418211) B418211
theorem B278827 : Blo 275825 278827 := bstep (se 1 (by rfl) ⟨209120, by rfl⟩ : syracuseStep 278827 = 418241) B418241
theorem B278839 : Blo 275825 278839 := bstep (se 1 (by rfl) ⟨209129, by rfl⟩ : syracuseStep 278839 = 418259) B418259
theorem B278859 : Blo 275825 278859 := bstep (se 1 (by rfl) ⟨209144, by rfl⟩ : syracuseStep 278859 = 418289) B418289
theorem B278871 : Blo 275825 278871 := bstep (se 1 (by rfl) ⟨209153, by rfl⟩ : syracuseStep 278871 = 418307) B418307
theorem B278891 : Blo 275825 278891 := bstep (se 1 (by rfl) ⟨209168, by rfl⟩ : syracuseStep 278891 = 418337) B418337
theorem B278903 : Blo 275825 278903 := bstep (se 1 (by rfl) ⟨209177, by rfl⟩ : syracuseStep 278903 = 418355) B418355
theorem B278923 : Blo 275825 278923 := bstep (se 1 (by rfl) ⟨209192, by rfl⟩ : syracuseStep 278923 = 418385) B418385
theorem B278935 : Blo 275825 278935 := bstep (se 1 (by rfl) ⟨209201, by rfl⟩ : syracuseStep 278935 = 418403) B418403
theorem B278955 : Blo 275825 278955 := bstep (se 1 (by rfl) ⟨209216, by rfl⟩ : syracuseStep 278955 = 418433) B418433
theorem B1458611 : Blo 275825 1458611 := bstep (se 1 (by rfl) ⟨1093958, by rfl⟩ : syracuseStep 1458611 = 2187917) B2187917
theorem B278967 : Blo 275825 278967 := bstep (se 1 (by rfl) ⟨209225, by rfl⟩ : syracuseStep 278967 = 418451) B418451
theorem B311755 : Blo 275825 311755 := bstep (se 1 (by rfl) ⟨233816, by rfl⟩ : syracuseStep 311755 = 467633) B467633
theorem B278987 : Blo 275825 278987 := bstep (se 1 (by rfl) ⟨209240, by rfl⟩ : syracuseStep 278987 = 418481) B418481
theorem B278999 : Blo 275825 278999 := bstep (se 1 (by rfl) ⟨209249, by rfl⟩ : syracuseStep 278999 = 418499) B418499
theorem B934361 : Blo 275825 934361 := bstep (se 2 (by rfl) ⟨350385, by rfl⟩ : syracuseStep 934361 = 700771) B700771
theorem B279019 : Blo 275825 279019 := bstep (se 1 (by rfl) ⟨209264, by rfl⟩ : syracuseStep 279019 = 418529) B418529
theorem B279031 : Blo 275825 279031 := bstep (se 1 (by rfl) ⟨209273, by rfl⟩ : syracuseStep 279031 = 418547) B418547
theorem B279051 : Blo 275825 279051 := bstep (se 1 (by rfl) ⟨209288, by rfl⟩ : syracuseStep 279051 = 418577) B418577
theorem B279063 : Blo 275825 279063 := bstep (se 1 (by rfl) ⟨209297, by rfl⟩ : syracuseStep 279063 = 418595) B418595
theorem B279083 : Blo 275825 279083 := bstep (se 1 (by rfl) ⟨209312, by rfl⟩ : syracuseStep 279083 = 418625) B418625
theorem B311863 : Blo 275825 311863 := bstep (se 1 (by rfl) ⟨233897, by rfl⟩ : syracuseStep 311863 = 467795) B467795
theorem B279095 : Blo 275825 279095 := bstep (se 1 (by rfl) ⟨209321, by rfl⟩ : syracuseStep 279095 = 418643) B418643
theorem B279115 : Blo 275825 279115 := bstep (se 1 (by rfl) ⟨209336, by rfl⟩ : syracuseStep 279115 = 418673) B418673
theorem B279127 : Blo 275825 279127 := bstep (se 1 (by rfl) ⟨209345, by rfl⟩ : syracuseStep 279127 = 418691) B418691
theorem B1065565 : Blo 275825 1065565 := bstep (se 3 (by rfl) ⟨199793, by rfl⟩ : syracuseStep 1065565 = 399587) B399587
theorem B279147 : Blo 275825 279147 := bstep (se 1 (by rfl) ⟨209360, by rfl⟩ : syracuseStep 279147 = 418721) B418721
theorem B279159 : Blo 275825 279159 := bstep (se 1 (by rfl) ⟨209369, by rfl⟩ : syracuseStep 279159 = 418739) B418739
theorem B279179 : Blo 275825 279179 := bstep (se 1 (by rfl) ⟨209384, by rfl⟩ : syracuseStep 279179 = 418769) B418769
theorem B1262231 : Blo 275825 1262231 := bstep (se 1 (by rfl) ⟨946673, by rfl⟩ : syracuseStep 1262231 = 1893347) B1893347
theorem B279191 : Blo 275825 279191 := bstep (se 1 (by rfl) ⟨209393, by rfl⟩ : syracuseStep 279191 = 418787) B418787
theorem B279211 : Blo 275825 279211 := bstep (se 1 (by rfl) ⟨209408, by rfl⟩ : syracuseStep 279211 = 418817) B418817
theorem B279223 : Blo 275825 279223 := bstep (se 1 (by rfl) ⟨209417, by rfl⟩ : syracuseStep 279223 = 418835) B418835
theorem B279243 : Blo 275825 279243 := bstep (se 1 (by rfl) ⟨209432, by rfl⟩ : syracuseStep 279243 = 418865) B418865
theorem B279255 : Blo 275825 279255 := bstep (se 1 (by rfl) ⟨209441, by rfl⟩ : syracuseStep 279255 = 418883) B418883
theorem B312043 : Blo 275825 312043 := bstep (se 1 (by rfl) ⟨234032, by rfl⟩ : syracuseStep 312043 = 468065) B468065
theorem B279275 : Blo 275825 279275 := bstep (se 1 (by rfl) ⟨209456, by rfl⟩ : syracuseStep 279275 = 418913) B418913
theorem B4801265 : Blo 275825 4801265 := bstep (se 2 (by rfl) ⟨1800474, by rfl⟩ : syracuseStep 4801265 = 3600949) B3600949
theorem B279287 : Blo 275825 279287 := bstep (se 1 (by rfl) ⟨209465, by rfl⟩ : syracuseStep 279287 = 418931) B418931
theorem B2999045 : Blo 275825 2999045 := bstep (se 4 (by rfl) ⟨281160, by rfl⟩ : syracuseStep 2999045 = 562321) B562321
theorem B279307 : Blo 275825 279307 := bstep (se 1 (by rfl) ⟨209480, by rfl⟩ : syracuseStep 279307 = 418961) B418961
theorem B279319 : Blo 275825 279319 := bstep (se 1 (by rfl) ⟨209489, by rfl⟩ : syracuseStep 279319 = 418979) B418979
theorem B279339 : Blo 275825 279339 := bstep (se 1 (by rfl) ⟨209504, by rfl⟩ : syracuseStep 279339 = 419009) B419009
theorem B279351 : Blo 275825 279351 := bstep (se 1 (by rfl) ⟨209513, by rfl⟩ : syracuseStep 279351 = 419027) B419027
theorem B279371 : Blo 275825 279371 := bstep (se 1 (by rfl) ⟨209528, by rfl⟩ : syracuseStep 279371 = 419057) B419057
theorem B312151 : Blo 275825 312151 := bstep (se 1 (by rfl) ⟨234113, by rfl⟩ : syracuseStep 312151 = 468227) B468227
theorem B279383 : Blo 275825 279383 := bstep (se 1 (by rfl) ⟨209537, by rfl⟩ : syracuseStep 279383 = 419075) B419075
theorem B279403 : Blo 275825 279403 := bstep (se 1 (by rfl) ⟨209552, by rfl⟩ : syracuseStep 279403 = 419105) B419105
theorem B279415 : Blo 275825 279415 := bstep (se 1 (by rfl) ⟨209561, by rfl⟩ : syracuseStep 279415 = 419123) B419123
theorem B279435 : Blo 275825 279435 := bstep (se 1 (by rfl) ⟨209576, by rfl⟩ : syracuseStep 279435 = 419153) B419153
theorem B279447 : Blo 275825 279447 := bstep (se 1 (by rfl) ⟨209585, by rfl⟩ : syracuseStep 279447 = 419171) B419171
theorem B279467 : Blo 275825 279467 := bstep (se 1 (by rfl) ⟨209600, by rfl⟩ : syracuseStep 279467 = 419201) B419201
theorem B279479 : Blo 275825 279479 := bstep (se 1 (by rfl) ⟨209609, by rfl⟩ : syracuseStep 279479 = 419219) B419219
theorem B279499 : Blo 275825 279499 := bstep (se 1 (by rfl) ⟨209624, by rfl⟩ : syracuseStep 279499 = 419249) B419249
theorem B279511 : Blo 275825 279511 := bstep (se 1 (by rfl) ⟨209633, by rfl⟩ : syracuseStep 279511 = 419267) B419267
theorem B279531 : Blo 275825 279531 := bstep (se 1 (by rfl) ⟨209648, by rfl⟩ : syracuseStep 279531 = 419297) B419297
theorem B279543 : Blo 275825 279543 := bstep (se 1 (by rfl) ⟨209657, by rfl⟩ : syracuseStep 279543 = 419315) B419315
theorem B312331 : Blo 275825 312331 := bstep (se 1 (by rfl) ⟨234248, by rfl⟩ : syracuseStep 312331 = 468497) B468497
theorem B279563 : Blo 275825 279563 := bstep (se 1 (by rfl) ⟨209672, by rfl⟩ : syracuseStep 279563 = 419345) B419345
theorem B279575 : Blo 275825 279575 := bstep (se 1 (by rfl) ⟨209681, by rfl⟩ : syracuseStep 279575 = 419363) B419363
theorem B279595 : Blo 275825 279595 := bstep (se 1 (by rfl) ⟨209696, by rfl⟩ : syracuseStep 279595 = 419393) B419393
theorem B279607 : Blo 275825 279607 := bstep (se 1 (by rfl) ⟨209705, by rfl⟩ : syracuseStep 279607 = 419411) B419411
theorem B705611 : Blo 275825 705611 := bstep (se 1 (by rfl) ⟨529208, by rfl⟩ : syracuseStep 705611 = 1058417) B1058417
theorem B279627 : Blo 275825 279627 := bstep (se 1 (by rfl) ⟨209720, by rfl⟩ : syracuseStep 279627 = 419441) B419441
theorem B279639 : Blo 275825 279639 := bstep (se 1 (by rfl) ⟨209729, by rfl⟩ : syracuseStep 279639 = 419459) B419459
theorem B279659 : Blo 275825 279659 := bstep (se 1 (by rfl) ⟨209744, by rfl⟩ : syracuseStep 279659 = 419489) B419489
theorem B312439 : Blo 275825 312439 := bstep (se 1 (by rfl) ⟨234329, by rfl⟩ : syracuseStep 312439 = 468659) B468659
theorem B279671 : Blo 275825 279671 := bstep (se 1 (by rfl) ⟨209753, by rfl⟩ : syracuseStep 279671 = 419507) B419507
theorem B377995 : Blo 275825 377995 := bstep (se 1 (by rfl) ⟨283496, by rfl⟩ : syracuseStep 377995 = 566993) B566993
theorem B279691 : Blo 275825 279691 := bstep (se 1 (by rfl) ⟨209768, by rfl⟩ : syracuseStep 279691 = 419537) B419537
theorem B935063 : Blo 275825 935063 := bstep (se 1 (by rfl) ⟨701297, by rfl⟩ : syracuseStep 935063 = 1402595) B1402595
theorem B2704535 : Blo 275825 2704535 := bstep (se 1 (by rfl) ⟨2028401, by rfl⟩ : syracuseStep 2704535 = 4056803) B4056803
theorem B279703 : Blo 275825 279703 := bstep (se 1 (by rfl) ⟨209777, by rfl⟩ : syracuseStep 279703 = 419555) B419555
theorem B279723 : Blo 275825 279723 := bstep (se 1 (by rfl) ⟨209792, by rfl⟩ : syracuseStep 279723 = 419585) B419585
theorem B279735 : Blo 275825 279735 := bstep (se 1 (by rfl) ⟨209801, by rfl⟩ : syracuseStep 279735 = 419603) B419603
theorem B279755 : Blo 275825 279755 := bstep (se 1 (by rfl) ⟨209816, by rfl⟩ : syracuseStep 279755 = 419633) B419633
theorem B279767 : Blo 275825 279767 := bstep (se 1 (by rfl) ⟨209825, by rfl⟩ : syracuseStep 279767 = 419651) B419651
theorem B279787 : Blo 275825 279787 := bstep (se 1 (by rfl) ⟨209840, by rfl⟩ : syracuseStep 279787 = 419681) B419681
theorem B279799 : Blo 275825 279799 := bstep (se 1 (by rfl) ⟨209849, by rfl⟩ : syracuseStep 279799 = 419699) B419699
theorem B279819 : Blo 275825 279819 := bstep (se 1 (by rfl) ⟨209864, by rfl⟩ : syracuseStep 279819 = 419729) B419729
theorem B312619 : Blo 275825 312619 := bstep (se 1 (by rfl) ⟨234464, by rfl⟩ : syracuseStep 312619 = 468929) B468929
theorem B9684269 : Blo 275825 9684269 := bstep (se 3 (by rfl) ⟨1815800, by rfl⟩ : syracuseStep 9684269 = 3631601) B3631601
theorem B312727 : Blo 275825 312727 := bstep (se 1 (by rfl) ⟨234545, by rfl⟩ : syracuseStep 312727 = 469091) B469091
theorem B1263179 : Blo 275825 1263179 := bstep (se 1 (by rfl) ⟨947384, by rfl⟩ : syracuseStep 1263179 = 1894769) B1894769
theorem B312907 : Blo 275825 312907 := bstep (se 1 (by rfl) ⟨234680, by rfl⟩ : syracuseStep 312907 = 469361) B469361
theorem B935603 : Blo 275825 935603 := bstep (se 1 (by rfl) ⟨701702, by rfl⟩ : syracuseStep 935603 = 1403405) B1403405
theorem B313015 : Blo 275825 313015 := bstep (se 1 (by rfl) ⟨234761, by rfl⟩ : syracuseStep 313015 = 469523) B469523
theorem B313195 : Blo 275825 313195 := bstep (se 1 (by rfl) ⟨234896, by rfl⟩ : syracuseStep 313195 = 469793) B469793
theorem B935873 : Blo 275825 935873 := bstep (se 2 (by rfl) ⟨350952, by rfl⟩ : syracuseStep 935873 = 701905) B701905
theorem B313303 : Blo 275825 313303 := bstep (se 1 (by rfl) ⟨234977, by rfl⟩ : syracuseStep 313303 = 469955) B469955
theorem B4737041 : Blo 275825 4737041 := bstep (se 2 (by rfl) ⟨1776390, by rfl⟩ : syracuseStep 4737041 = 3552781) B3552781
theorem B706583 : Blo 275825 706583 := bstep (se 1 (by rfl) ⟨529937, by rfl⟩ : syracuseStep 706583 = 1059875) B1059875
theorem B444503 : Blo 275825 444503 := bstep (se 1 (by rfl) ⟨333377, by rfl⟩ : syracuseStep 444503 = 666755) B666755
theorem B313483 : Blo 275825 313483 := bstep (se 1 (by rfl) ⟨235112, by rfl⟩ : syracuseStep 313483 = 470225) B470225
theorem B313591 : Blo 275825 313591 := bstep (se 1 (by rfl) ⟨235193, by rfl⟩ : syracuseStep 313591 = 470387) B470387
theorem B313771 : Blo 275825 313771 := bstep (se 1 (by rfl) ⟨235328, by rfl⟩ : syracuseStep 313771 = 470657) B470657
theorem B936413 : Blo 275825 936413 := bstep (se 3 (by rfl) ⟨175577, by rfl⟩ : syracuseStep 936413 = 351155) B351155
theorem B313879 : Blo 275825 313879 := bstep (se 1 (by rfl) ⟨235409, by rfl⟩ : syracuseStep 313879 = 470819) B470819
theorem B3066443 : Blo 275825 3066443 := bstep (se 1 (by rfl) ⟨2299832, by rfl⟩ : syracuseStep 3066443 = 4599665) B4599665
theorem B1428119 : Blo 275825 1428119 := bstep (se 1 (by rfl) ⟨1071089, by rfl⟩ : syracuseStep 1428119 = 2142179) B2142179
theorem B707251 : Blo 275825 707251 := bstep (se 1 (by rfl) ⟨530438, by rfl⟩ : syracuseStep 707251 = 1060877) B1060877
theorem B314059 : Blo 275825 314059 := bstep (se 1 (by rfl) ⟨235544, by rfl⟩ : syracuseStep 314059 = 471089) B471089
theorem B1264349 : Blo 275825 1264349 := bstep (se 3 (by rfl) ⟨237065, by rfl⟩ : syracuseStep 1264349 = 474131) B474131
theorem B281323 : Blo 275825 281323 := bstep (se 1 (by rfl) ⟨210992, by rfl⟩ : syracuseStep 281323 = 421985) B421985
theorem B314167 : Blo 275825 314167 := bstep (se 1 (by rfl) ⟨235625, by rfl⟩ : syracuseStep 314167 = 471251) B471251
theorem B707393 : Blo 275825 707393 := bstep (se 2 (by rfl) ⟨265272, by rfl⟩ : syracuseStep 707393 = 530545) B530545
theorem B2116529 : Blo 275825 2116529 := bstep (se 2 (by rfl) ⟨793698, by rfl⟩ : syracuseStep 2116529 = 1587397) B1587397
theorem B314347 : Blo 275825 314347 := bstep (se 1 (by rfl) ⟨235760, by rfl⟩ : syracuseStep 314347 = 471521) B471521
theorem B314455 : Blo 275825 314455 := bstep (se 1 (by rfl) ⟨235841, by rfl⟩ : syracuseStep 314455 = 471683) B471683
theorem B314635 : Blo 275825 314635 := bstep (se 1 (by rfl) ⟨235976, by rfl⟩ : syracuseStep 314635 = 471953) B471953
theorem B839005 : Blo 275825 839005 := bstep (se 3 (by rfl) ⟨157313, by rfl⟩ : syracuseStep 839005 = 314627) B314627
theorem B314743 : Blo 275825 314743 := bstep (se 1 (by rfl) ⟨236057, by rfl⟩ : syracuseStep 314743 = 472115) B472115
theorem B2117015 : Blo 275825 2117015 := bstep (se 1 (by rfl) ⟨1587761, by rfl⟩ : syracuseStep 2117015 = 3175523) B3175523
theorem B839105 : Blo 275825 839105 := bstep (se 2 (by rfl) ⟨314664, by rfl⟩ : syracuseStep 839105 = 629329) B629329
theorem B937547 : Blo 275825 937547 := bstep (se 1 (by rfl) ⟨703160, by rfl⟩ : syracuseStep 937547 = 1406321) B1406321
theorem B282199 : Blo 275825 282199 := bstep (se 1 (by rfl) ⟨211649, by rfl⟩ : syracuseStep 282199 = 423299) B423299
theorem B1199767 : Blo 275825 1199767 := bstep (se 1 (by rfl) ⟨899825, by rfl⟩ : syracuseStep 1199767 = 1799651) B1799651
theorem B937817 : Blo 275825 937817 := bstep (se 2 (by rfl) ⟨351681, by rfl⟩ : syracuseStep 937817 = 703363) B703363
theorem B413771 : Blo 275825 413771 := bstep (se 1 (by rfl) ⟨310328, by rfl⟩ : syracuseStep 413771 = 620657) B620657
theorem B413783 : Blo 275825 413783 := bstep (se 1 (by rfl) ⟨310337, by rfl⟩ : syracuseStep 413783 = 620675) B620675
theorem B413849 : Blo 275825 413849 := bstep (se 2 (by rfl) ⟨155193, by rfl⟩ : syracuseStep 413849 = 310387) B310387
theorem B643315 : Blo 275825 643315 := bstep (se 1 (by rfl) ⟨482486, by rfl⟩ : syracuseStep 643315 = 964973) B964973
theorem B4837637 : Blo 275825 4837637 := bstep (se 4 (by rfl) ⟨453528, by rfl⟩ : syracuseStep 4837637 = 907057) B907057
theorem B413963 : Blo 275825 413963 := bstep (se 1 (by rfl) ⟨310472, by rfl⟩ : syracuseStep 413963 = 620945) B620945
theorem B413975 : Blo 275825 413975 := bstep (se 1 (by rfl) ⟨310481, by rfl⟩ : syracuseStep 413975 = 620963) B620963
theorem B414041 : Blo 275825 414041 := bstep (se 2 (by rfl) ⟨155265, by rfl⟩ : syracuseStep 414041 = 310531) B310531
theorem B446809 : Blo 275825 446809 := bstep (se 2 (by rfl) ⟨167553, by rfl⟩ : syracuseStep 446809 = 335107) B335107
theorem B414155 : Blo 275825 414155 := bstep (se 1 (by rfl) ⟨310616, by rfl⟩ : syracuseStep 414155 = 621233) B621233
theorem B414167 : Blo 275825 414167 := bstep (se 1 (by rfl) ⟨310625, by rfl⟩ : syracuseStep 414167 = 621251) B621251
theorem B938519 : Blo 275825 938519 := bstep (se 1 (by rfl) ⟨703889, by rfl⟩ : syracuseStep 938519 = 1407779) B1407779
theorem B414233 : Blo 275825 414233 := bstep (se 2 (by rfl) ⟨155337, by rfl⟩ : syracuseStep 414233 = 310675) B310675
theorem B414347 : Blo 275825 414347 := bstep (se 1 (by rfl) ⟨310760, by rfl⟩ : syracuseStep 414347 = 621521) B621521
theorem B414359 : Blo 275825 414359 := bstep (se 1 (by rfl) ⟨310769, by rfl⟩ : syracuseStep 414359 = 621539) B621539
theorem B414425 : Blo 275825 414425 := bstep (se 2 (by rfl) ⟨155409, by rfl⟩ : syracuseStep 414425 = 310819) B310819
theorem B2380549 : Blo 275825 2380549 := bstep (se 4 (by rfl) ⟨223176, by rfl⟩ : syracuseStep 2380549 = 446353) B446353
theorem B414539 : Blo 275825 414539 := bstep (se 1 (by rfl) ⟨310904, by rfl⟩ : syracuseStep 414539 = 621809) B621809
theorem B414551 : Blo 275825 414551 := bstep (se 1 (by rfl) ⟨310913, by rfl⟩ : syracuseStep 414551 = 621827) B621827
theorem B414617 : Blo 275825 414617 := bstep (se 2 (by rfl) ⟨155481, by rfl⟩ : syracuseStep 414617 = 310963) B310963
theorem B414731 : Blo 275825 414731 := bstep (se 1 (by rfl) ⟨311048, by rfl⟩ : syracuseStep 414731 = 622097) B622097
theorem B414743 : Blo 275825 414743 := bstep (se 1 (by rfl) ⟨311057, by rfl⟩ : syracuseStep 414743 = 622115) B622115
theorem B939059 : Blo 275825 939059 := bstep (se 1 (by rfl) ⟨704294, by rfl⟩ : syracuseStep 939059 = 1408589) B1408589
theorem B414809 : Blo 275825 414809 := bstep (se 2 (by rfl) ⟨155553, by rfl⟩ : syracuseStep 414809 = 311107) B311107
theorem B414923 : Blo 275825 414923 := bstep (se 1 (by rfl) ⟨311192, by rfl⟩ : syracuseStep 414923 = 622385) B622385
theorem B414935 : Blo 275825 414935 := bstep (se 1 (by rfl) ⟨311201, by rfl⟩ : syracuseStep 414935 = 622403) B622403
theorem B1266961 : Blo 275825 1266961 := bstep (se 2 (by rfl) ⟨475110, by rfl⟩ : syracuseStep 1266961 = 950221) B950221
theorem B415001 : Blo 275825 415001 := bstep (se 2 (by rfl) ⟨155625, by rfl⟩ : syracuseStep 415001 = 311251) B311251
theorem B939329 : Blo 275825 939329 := bstep (se 2 (by rfl) ⟨352248, by rfl⟩ : syracuseStep 939329 = 704497) B704497
theorem B415115 : Blo 275825 415115 := bstep (se 1 (by rfl) ⟨311336, by rfl⟩ : syracuseStep 415115 = 622673) B622673
theorem B349591 : Blo 275825 349591 := bstep (se 1 (by rfl) ⟨262193, by rfl⟩ : syracuseStep 349591 = 524387) B524387
theorem B710039 : Blo 275825 710039 := bstep (se 1 (by rfl) ⟨532529, by rfl⟩ : syracuseStep 710039 = 1065059) B1065059
theorem B415127 : Blo 275825 415127 := bstep (se 1 (by rfl) ⟨311345, by rfl⟩ : syracuseStep 415127 = 622691) B622691
theorem B415193 : Blo 275825 415193 := bstep (se 2 (by rfl) ⟨155697, by rfl⟩ : syracuseStep 415193 = 311395) B311395
theorem B415307 : Blo 275825 415307 := bstep (se 1 (by rfl) ⟨311480, by rfl⟩ : syracuseStep 415307 = 622961) B622961
theorem B415319 : Blo 275825 415319 := bstep (se 1 (by rfl) ⟨311489, by rfl⟩ : syracuseStep 415319 = 622979) B622979
theorem B415385 : Blo 275825 415385 := bstep (se 2 (by rfl) ⟨155769, by rfl⟩ : syracuseStep 415385 = 311539) B311539
theorem B415499 : Blo 275825 415499 := bstep (se 1 (by rfl) ⟨311624, by rfl⟩ : syracuseStep 415499 = 623249) B623249
theorem B1398545 : Blo 275825 1398545 := bstep (se 2 (by rfl) ⟨524454, by rfl⟩ : syracuseStep 1398545 = 1048909) B1048909
theorem B415511 : Blo 275825 415511 := bstep (se 1 (by rfl) ⟨311633, by rfl⟩ : syracuseStep 415511 = 623267) B623267
theorem B415577 : Blo 275825 415577 := bstep (se 2 (by rfl) ⟨155841, by rfl⟩ : syracuseStep 415577 = 311683) B311683
theorem B939869 : Blo 275825 939869 := bstep (se 3 (by rfl) ⟨176225, by rfl⟩ : syracuseStep 939869 = 352451) B352451
theorem B8214371 : Blo 275825 8214371 := bstep (se 1 (by rfl) ⟨6160778, by rfl⟩ : syracuseStep 8214371 = 12321557) B12321557
theorem B1398707 : Blo 275825 1398707 := bstep (se 1 (by rfl) ⟨1049030, by rfl⟩ : syracuseStep 1398707 = 2098061) B2098061
theorem B415691 : Blo 275825 415691 := bstep (se 1 (by rfl) ⟨311768, by rfl⟩ : syracuseStep 415691 = 623537) B623537
theorem B415703 : Blo 275825 415703 := bstep (se 1 (by rfl) ⟨311777, by rfl⟩ : syracuseStep 415703 = 623555) B623555
theorem B415769 : Blo 275825 415769 := bstep (se 2 (by rfl) ⟨155913, by rfl⟩ : syracuseStep 415769 = 311827) B311827
theorem B415883 : Blo 275825 415883 := bstep (se 1 (by rfl) ⟨311912, by rfl⟩ : syracuseStep 415883 = 623825) B623825
theorem B415895 : Blo 275825 415895 := bstep (se 1 (by rfl) ⟨311921, by rfl⟩ : syracuseStep 415895 = 623843) B623843
theorem B415961 : Blo 275825 415961 := bstep (se 2 (by rfl) ⟨155985, by rfl⟩ : syracuseStep 415961 = 311971) B311971
theorem B1497361 : Blo 275825 1497361 := bstep (se 2 (by rfl) ⟨561510, by rfl⟩ : syracuseStep 1497361 = 1123021) B1123021
theorem B416075 : Blo 275825 416075 := bstep (se 1 (by rfl) ⟨312056, by rfl⟩ : syracuseStep 416075 = 624113) B624113
theorem B416087 : Blo 275825 416087 := bstep (se 1 (by rfl) ⟨312065, by rfl⟩ : syracuseStep 416087 = 624131) B624131
theorem B416153 : Blo 275825 416153 := bstep (se 2 (by rfl) ⟨156057, by rfl⟩ : syracuseStep 416153 = 312115) B312115
theorem B1268141 : Blo 275825 1268141 := bstep (se 3 (by rfl) ⟨237776, by rfl⟩ : syracuseStep 1268141 = 475553) B475553
theorem B416267 : Blo 275825 416267 := bstep (se 1 (by rfl) ⟨312200, by rfl⟩ : syracuseStep 416267 = 624401) B624401
theorem B416279 : Blo 275825 416279 := bstep (se 1 (by rfl) ⟨312209, by rfl⟩ : syracuseStep 416279 = 624419) B624419
theorem B416345 : Blo 275825 416345 := bstep (se 2 (by rfl) ⟨156129, by rfl⟩ : syracuseStep 416345 = 312259) B312259
theorem B416459 : Blo 275825 416459 := bstep (se 1 (by rfl) ⟨312344, by rfl⟩ : syracuseStep 416459 = 624689) B624689
theorem B416471 : Blo 275825 416471 := bstep (se 1 (by rfl) ⟨312353, by rfl⟩ : syracuseStep 416471 = 624707) B624707
theorem B416537 : Blo 275825 416537 := bstep (se 2 (by rfl) ⟨156201, by rfl⟩ : syracuseStep 416537 = 312403) B312403
theorem B416651 : Blo 275825 416651 := bstep (se 1 (by rfl) ⟨312488, by rfl⟩ : syracuseStep 416651 = 624977) B624977
theorem B416663 : Blo 275825 416663 := bstep (se 1 (by rfl) ⟨312497, by rfl⟩ : syracuseStep 416663 = 624995) B624995
theorem B941003 : Blo 275825 941003 := bstep (se 1 (by rfl) ⟨705752, by rfl⟩ : syracuseStep 941003 = 1411505) B1411505
theorem B449497 : Blo 275825 449497 := bstep (se 2 (by rfl) ⟨168561, by rfl⟩ : syracuseStep 449497 = 337123) B337123
theorem B416729 : Blo 275825 416729 := bstep (se 2 (by rfl) ⟨156273, by rfl⟩ : syracuseStep 416729 = 312547) B312547
theorem B842827 : Blo 275825 842827 := bstep (se 1 (by rfl) ⟨632120, by rfl⟩ : syracuseStep 842827 = 1264241) B1264241
theorem B351307 : Blo 275825 351307 := bstep (se 1 (by rfl) ⟨263480, by rfl⟩ : syracuseStep 351307 = 526961) B526961
theorem B416843 : Blo 275825 416843 := bstep (se 1 (by rfl) ⟨312632, by rfl⟩ : syracuseStep 416843 = 625265) B625265
theorem B416855 : Blo 275825 416855 := bstep (se 1 (by rfl) ⟨312641, by rfl⟩ : syracuseStep 416855 = 625283) B625283
theorem B416921 : Blo 275825 416921 := bstep (se 2 (by rfl) ⟨156345, by rfl⟩ : syracuseStep 416921 = 312691) B312691
theorem B941273 : Blo 275825 941273 := bstep (se 2 (by rfl) ⟨352977, by rfl⟩ : syracuseStep 941273 = 705955) B705955
theorem B417035 : Blo 275825 417035 := bstep (se 1 (by rfl) ⟨312776, by rfl⟩ : syracuseStep 417035 = 625553) B625553
theorem B417047 : Blo 275825 417047 := bstep (se 1 (by rfl) ⟨312785, by rfl⟩ : syracuseStep 417047 = 625571) B625571
theorem B417113 : Blo 275825 417113 := bstep (se 2 (by rfl) ⟨156417, by rfl⟩ : syracuseStep 417113 = 312835) B312835
theorem B1006937 : Blo 275825 1006937 := bstep (se 2 (by rfl) ⟨377601, by rfl⟩ : syracuseStep 1006937 = 755203) B755203
theorem B2383283 : Blo 275825 2383283 := bstep (se 1 (by rfl) ⟨1787462, by rfl⟩ : syracuseStep 2383283 = 3574925) B3574925
theorem B417227 : Blo 275825 417227 := bstep (se 1 (by rfl) ⟨312920, by rfl⟩ : syracuseStep 417227 = 625841) B625841
theorem B417239 : Blo 275825 417239 := bstep (se 1 (by rfl) ⟨312929, by rfl⟩ : syracuseStep 417239 = 625859) B625859
theorem B417305 : Blo 275825 417305 := bstep (se 2 (by rfl) ⟨156489, by rfl⟩ : syracuseStep 417305 = 312979) B312979
theorem B417419 : Blo 275825 417419 := bstep (se 1 (by rfl) ⟨313064, by rfl⟩ : syracuseStep 417419 = 626129) B626129
theorem B417431 : Blo 275825 417431 := bstep (se 1 (by rfl) ⟨313073, by rfl⟩ : syracuseStep 417431 = 626147) B626147
theorem B2547377 : Blo 275825 2547377 := bstep (se 2 (by rfl) ⟨955266, by rfl⟩ : syracuseStep 2547377 = 1910533) B1910533
theorem B679603 : Blo 275825 679603 := bstep (se 1 (by rfl) ⟨509702, by rfl⟩ : syracuseStep 679603 = 1019405) B1019405
theorem B417497 : Blo 275825 417497 := bstep (se 2 (by rfl) ⟨156561, by rfl⟩ : syracuseStep 417497 = 313123) B313123
theorem B1400651 : Blo 275825 1400651 := bstep (se 1 (by rfl) ⟨1050488, by rfl⟩ : syracuseStep 1400651 = 2100977) B2100977
theorem B417611 : Blo 275825 417611 := bstep (se 1 (by rfl) ⟨313208, by rfl⟩ : syracuseStep 417611 = 626417) B626417
theorem B417623 : Blo 275825 417623 := bstep (se 1 (by rfl) ⟨313217, by rfl⟩ : syracuseStep 417623 = 626435) B626435
theorem B941975 : Blo 275825 941975 := bstep (se 1 (by rfl) ⟨706481, by rfl⟩ : syracuseStep 941975 = 1412963) B1412963
theorem B417689 : Blo 275825 417689 := bstep (se 2 (by rfl) ⟨156633, by rfl⟩ : syracuseStep 417689 = 313267) B313267
theorem B417803 : Blo 275825 417803 := bstep (se 1 (by rfl) ⟨313352, by rfl⟩ : syracuseStep 417803 = 626705) B626705
theorem B352279 : Blo 275825 352279 := bstep (se 1 (by rfl) ⟨264209, by rfl⟩ : syracuseStep 352279 = 528419) B528419
theorem B417815 : Blo 275825 417815 := bstep (se 1 (by rfl) ⟨313361, by rfl⟩ : syracuseStep 417815 = 626723) B626723
theorem B417881 : Blo 275825 417881 := bstep (se 2 (by rfl) ⟨156705, by rfl⟩ : syracuseStep 417881 = 313411) B313411
theorem B417995 : Blo 275825 417995 := bstep (se 1 (by rfl) ⟨313496, by rfl⟩ : syracuseStep 417995 = 626993) B626993
theorem B418007 : Blo 275825 418007 := bstep (se 1 (by rfl) ⟨313505, by rfl⟩ : syracuseStep 418007 = 627011) B627011
theorem B418073 : Blo 275825 418073 := bstep (se 2 (by rfl) ⟨156777, by rfl⟩ : syracuseStep 418073 = 313555) B313555
theorem B418187 : Blo 275825 418187 := bstep (se 1 (by rfl) ⟨313640, by rfl⟩ : syracuseStep 418187 = 627281) B627281
theorem B418199 : Blo 275825 418199 := bstep (se 1 (by rfl) ⟨313649, by rfl⟩ : syracuseStep 418199 = 627299) B627299
theorem B942515 : Blo 275825 942515 := bstep (se 1 (by rfl) ⟨706886, by rfl⟩ : syracuseStep 942515 = 1413773) B1413773
theorem B418265 : Blo 275825 418265 := bstep (se 2 (by rfl) ⟨156849, by rfl⟩ : syracuseStep 418265 = 313699) B313699
theorem B1008089 : Blo 275825 1008089 := bstep (se 2 (by rfl) ⟨378033, by rfl⟩ : syracuseStep 1008089 = 756067) B756067
theorem B418379 : Blo 275825 418379 := bstep (se 1 (by rfl) ⟨313784, by rfl⟩ : syracuseStep 418379 = 627569) B627569
theorem B418391 : Blo 275825 418391 := bstep (se 1 (by rfl) ⟨313793, by rfl⟩ : syracuseStep 418391 = 627587) B627587
theorem B418457 : Blo 275825 418457 := bstep (se 2 (by rfl) ⟨156921, by rfl⟩ : syracuseStep 418457 = 313843) B313843
theorem B942785 : Blo 275825 942785 := bstep (se 2 (by rfl) ⟨353544, by rfl⟩ : syracuseStep 942785 = 707089) B707089
theorem B418571 : Blo 275825 418571 := bstep (se 1 (by rfl) ⟨313928, by rfl⟩ : syracuseStep 418571 = 627857) B627857
theorem B418583 : Blo 275825 418583 := bstep (se 1 (by rfl) ⟨313937, by rfl⟩ : syracuseStep 418583 = 627875) B627875
theorem B8971073 : Blo 275825 8971073 := bstep (se 2 (by rfl) ⟨3364152, by rfl⟩ : syracuseStep 8971073 = 6728305) B6728305
theorem B1336139 : Blo 275825 1336139 := bstep (se 1 (by rfl) ⟨1002104, by rfl⟩ : syracuseStep 1336139 = 2004209) B2004209
theorem B353099 : Blo 275825 353099 := bstep (se 1 (by rfl) ⟨264824, by rfl⟩ : syracuseStep 353099 = 529649) B529649
theorem B418649 : Blo 275825 418649 := bstep (se 2 (by rfl) ⟨156993, by rfl⟩ : syracuseStep 418649 = 313987) B313987
theorem B418763 : Blo 275825 418763 := bstep (se 1 (by rfl) ⟨314072, by rfl⟩ : syracuseStep 418763 = 628145) B628145
theorem B418775 : Blo 275825 418775 := bstep (se 1 (by rfl) ⟨314081, by rfl⟩ : syracuseStep 418775 = 628163) B628163
theorem B3990545 : Blo 275825 3990545 := bstep (se 2 (by rfl) ⟨1496454, by rfl⟩ : syracuseStep 3990545 = 2992909) B2992909
theorem B418841 : Blo 275825 418841 := bstep (se 2 (by rfl) ⟨157065, by rfl⟩ : syracuseStep 418841 = 314131) B314131
theorem B418955 : Blo 275825 418955 := bstep (se 1 (by rfl) ⟨314216, by rfl⟩ : syracuseStep 418955 = 628433) B628433
theorem B746647 : Blo 275825 746647 := bstep (se 1 (by rfl) ⟨559985, by rfl⟩ : syracuseStep 746647 = 1119971) B1119971
theorem B418967 : Blo 275825 418967 := bstep (se 1 (by rfl) ⟨314225, by rfl⟩ : syracuseStep 418967 = 628451) B628451
theorem B419033 : Blo 275825 419033 := bstep (se 2 (by rfl) ⟨157137, by rfl⟩ : syracuseStep 419033 = 314275) B314275
theorem B943325 : Blo 275825 943325 := bstep (se 3 (by rfl) ⟨176873, by rfl⟩ : syracuseStep 943325 = 353747) B353747
theorem B2385197 : Blo 275825 2385197 := bstep (se 3 (by rfl) ⟨447224, by rfl⟩ : syracuseStep 2385197 = 894449) B894449
theorem B419147 : Blo 275825 419147 := bstep (se 1 (by rfl) ⟨314360, by rfl⟩ : syracuseStep 419147 = 628721) B628721
theorem B419159 : Blo 275825 419159 := bstep (se 1 (by rfl) ⟨314369, by rfl⟩ : syracuseStep 419159 = 628739) B628739
theorem B419225 : Blo 275825 419225 := bstep (se 2 (by rfl) ⟨157209, by rfl⟩ : syracuseStep 419225 = 314419) B314419
theorem B1598899 : Blo 275825 1598899 := bstep (se 1 (by rfl) ⟨1199174, by rfl⟩ : syracuseStep 1598899 = 2398349) B2398349
theorem B353803 : Blo 275825 353803 := bstep (se 1 (by rfl) ⟨265352, by rfl⟩ : syracuseStep 353803 = 530705) B530705
theorem B419339 : Blo 275825 419339 := bstep (se 1 (by rfl) ⟨314504, by rfl⟩ : syracuseStep 419339 = 629009) B629009
theorem B419351 : Blo 275825 419351 := bstep (se 1 (by rfl) ⟨314513, by rfl⟩ : syracuseStep 419351 = 629027) B629027
theorem B1009217 : Blo 275825 1009217 := bstep (se 2 (by rfl) ⟨378456, by rfl⟩ : syracuseStep 1009217 = 756913) B756913
theorem B1402433 : Blo 275825 1402433 := bstep (se 2 (by rfl) ⟨525912, by rfl⟩ : syracuseStep 1402433 = 1051825) B1051825
theorem B1336907 : Blo 275825 1336907 := bstep (se 1 (by rfl) ⟨1002680, by rfl⟩ : syracuseStep 1336907 = 2005361) B2005361
theorem B419417 : Blo 275825 419417 := bstep (se 2 (by rfl) ⟨157281, by rfl⟩ : syracuseStep 419417 = 314563) B314563
theorem B845515 : Blo 275825 845515 := bstep (se 1 (by rfl) ⟨634136, by rfl⟩ : syracuseStep 845515 = 1268273) B1268273
theorem B419531 : Blo 275825 419531 := bstep (se 1 (by rfl) ⟨314648, by rfl⟩ : syracuseStep 419531 = 629297) B629297
theorem B419543 : Blo 275825 419543 := bstep (se 1 (by rfl) ⟨314657, by rfl⟩ : syracuseStep 419543 = 629315) B629315
theorem B354071 : Blo 275825 354071 := bstep (se 1 (by rfl) ⟨265553, by rfl⟩ : syracuseStep 354071 = 531107) B531107
theorem B419609 : Blo 275825 419609 := bstep (se 2 (by rfl) ⟨157353, by rfl⟩ : syracuseStep 419609 = 314707) B314707
theorem B2320163 : Blo 275825 2320163 := bstep (se 1 (by rfl) ⟨1740122, by rfl⟩ : syracuseStep 2320163 = 3480245) B3480245
theorem B419723 : Blo 275825 419723 := bstep (se 1 (by rfl) ⟨314792, by rfl⟩ : syracuseStep 419723 = 629585) B629585
theorem B419735 : Blo 275825 419735 := bstep (se 1 (by rfl) ⟨314801, by rfl⟩ : syracuseStep 419735 = 629603) B629603
theorem B845747 : Blo 275825 845747 := bstep (se 1 (by rfl) ⟨634310, by rfl⟩ : syracuseStep 845747 = 1268621) B1268621
theorem B2385881 : Blo 275825 2385881 := bstep (se 2 (by rfl) ⟨894705, by rfl⟩ : syracuseStep 2385881 = 1789411) B1789411
theorem B2517169 : Blo 275825 2517169 := bstep (se 2 (by rfl) ⟨943938, by rfl⟩ : syracuseStep 2517169 = 1887877) B1887877
theorem B2124305 : Blo 275825 2124305 := bstep (se 2 (by rfl) ⟨796614, by rfl⟩ : syracuseStep 2124305 = 1593229) B1593229
theorem B354839 : Blo 275825 354839 := bstep (se 1 (by rfl) ⟨266129, by rfl⟩ : syracuseStep 354839 = 532259) B532259
theorem B2845277 : Blo 275825 2845277 := bstep (se 3 (by rfl) ⟨533489, by rfl⟩ : syracuseStep 2845277 = 1066979) B1066979
theorem B453899 : Blo 275825 453899 := bstep (se 1 (by rfl) ⟨340424, by rfl⟩ : syracuseStep 453899 = 680849) B680849
theorem B912691 : Blo 275825 912691 := bstep (se 1 (by rfl) ⟨684518, by rfl⟩ : syracuseStep 912691 = 1369037) B1369037
theorem B1404377 : Blo 275825 1404377 := bstep (se 2 (by rfl) ⟨526641, by rfl⟩ : syracuseStep 1404377 = 1053283) B1053283
theorem B5041925 : Blo 275825 5041925 := bstep (se 4 (by rfl) ⟨472680, by rfl⟩ : syracuseStep 5041925 = 945361) B945361
theorem B1339523 : Blo 275825 1339523 := bstep (se 1 (by rfl) ⟨1004642, by rfl⟩ : syracuseStep 1339523 = 2009285) B2009285
theorem B3371159 : Blo 275825 3371159 := bstep (se 1 (by rfl) ⟨2528369, by rfl⟩ : syracuseStep 3371159 = 5056739) B5056739
theorem B6942871 : Blo 275825 6942871 := bstep (se 1 (by rfl) ⟨5207153, by rfl⟩ : syracuseStep 6942871 = 10414307) B10414307
theorem B3141989 : Blo 275825 3141989 := bstep (se 4 (by rfl) ⟨294561, by rfl⟩ : syracuseStep 3141989 = 589123) B589123
theorem B2683313 : Blo 275825 2683313 := bstep (se 2 (by rfl) ⟨1006242, by rfl⟩ : syracuseStep 2683313 = 2012485) B2012485
theorem B422423 : Blo 275825 422423 := bstep (se 1 (by rfl) ⟨316817, by rfl⟩ : syracuseStep 422423 = 633635) B633635
theorem B422617 : Blo 275825 422617 := bstep (se 2 (by rfl) ⟨158481, by rfl⟩ : syracuseStep 422617 = 316963) B316963
theorem B1405997 : Blo 275825 1405997 := bstep (se 3 (by rfl) ⟨263624, by rfl⟩ : syracuseStep 1405997 = 527249) B527249
theorem B1603147 : Blo 275825 1603147 := bstep (se 1 (by rfl) ⟨1202360, by rfl⟩ : syracuseStep 1603147 = 2404721) B2404721
theorem B1800323 : Blo 275825 1800323 := bstep (se 1 (by rfl) ⟨1350242, by rfl⟩ : syracuseStep 1800323 = 2700485) B2700485
theorem B1767575 : Blo 275825 1767575 := bstep (se 1 (by rfl) ⟨1325681, by rfl⟩ : syracuseStep 1767575 = 2651363) B2651363
theorem B2586775 : Blo 275825 2586775 := bstep (se 1 (by rfl) ⟨1940081, by rfl⟩ : syracuseStep 2586775 = 3880163) B3880163
theorem B620747 : Blo 275825 620747 := bstep (se 1 (by rfl) ⟨465560, by rfl⟩ : syracuseStep 620747 = 931121) B931121
theorem B620801 : Blo 275825 620801 := bstep (se 2 (by rfl) ⟨232800, by rfl⟩ : syracuseStep 620801 = 465601) B465601
theorem B2521475 : Blo 275825 2521475 := bstep (se 1 (by rfl) ⟨1891106, by rfl⟩ : syracuseStep 2521475 = 3782213) B3782213
theorem B424345 : Blo 275825 424345 := bstep (se 2 (by rfl) ⟨159129, by rfl⟩ : syracuseStep 424345 = 318259) B318259
theorem B2259377 : Blo 275825 2259377 := bstep (se 2 (by rfl) ⟨847266, by rfl⟩ : syracuseStep 2259377 = 1694533) B1694533
theorem B621017 : Blo 275825 621017 := bstep (se 2 (by rfl) ⟨232881, by rfl⟩ : syracuseStep 621017 = 465763) B465763
theorem B621107 : Blo 275825 621107 := bstep (se 1 (by rfl) ⟨465830, by rfl⟩ : syracuseStep 621107 = 931661) B931661
theorem B621143 : Blo 275825 621143 := bstep (se 1 (by rfl) ⟨465857, by rfl⟩ : syracuseStep 621143 = 931715) B931715
theorem B1997405 : Blo 275825 1997405 := bstep (se 3 (by rfl) ⟨374513, by rfl⟩ : syracuseStep 1997405 = 749027) B749027
theorem B621323 : Blo 275825 621323 := bstep (se 1 (by rfl) ⟨465992, by rfl⟩ : syracuseStep 621323 = 931985) B931985
theorem B752435 : Blo 275825 752435 := bstep (se 1 (by rfl) ⟨564326, by rfl⟩ : syracuseStep 752435 = 1128653) B1128653
theorem B621377 : Blo 275825 621377 := bstep (se 2 (by rfl) ⟨233016, by rfl⟩ : syracuseStep 621377 = 466033) B466033
theorem B424855 : Blo 275825 424855 := bstep (se 1 (by rfl) ⟨318641, by rfl⟩ : syracuseStep 424855 = 637283) B637283
theorem B621593 : Blo 275825 621593 := bstep (se 2 (by rfl) ⟨233097, by rfl⟩ : syracuseStep 621593 = 466195) B466195
theorem B1571885 : Blo 275825 1571885 := bstep (se 3 (by rfl) ⟨294728, by rfl⟩ : syracuseStep 1571885 = 589457) B589457
theorem B621683 : Blo 275825 621683 := bstep (se 1 (by rfl) ⟨466262, by rfl⟩ : syracuseStep 621683 = 932525) B932525
theorem B621719 : Blo 275825 621719 := bstep (se 1 (by rfl) ⟨466289, by rfl⟩ : syracuseStep 621719 = 932579) B932579
theorem B1047725 : Blo 275825 1047725 := bstep (se 3 (by rfl) ⟨196448, by rfl⟩ : syracuseStep 1047725 = 392897) B392897
theorem B1047755 : Blo 275825 1047755 := bstep (se 1 (by rfl) ⟨785816, by rfl⟩ : syracuseStep 1047755 = 1571633) B1571633
theorem B621899 : Blo 275825 621899 := bstep (se 1 (by rfl) ⟨466424, by rfl⟩ : syracuseStep 621899 = 932849) B932849
theorem B621953 : Blo 275825 621953 := bstep (se 2 (by rfl) ⟨233232, by rfl⟩ : syracuseStep 621953 = 466465) B466465
theorem B2358679 : Blo 275825 2358679 := bstep (se 1 (by rfl) ⟨1769009, by rfl⟩ : syracuseStep 2358679 = 3538019) B3538019
theorem B3571235 : Blo 275825 3571235 := bstep (se 1 (by rfl) ⟨2678426, by rfl⟩ : syracuseStep 3571235 = 5356853) B5356853
theorem B622169 : Blo 275825 622169 := bstep (se 2 (by rfl) ⟨233313, by rfl⟩ : syracuseStep 622169 = 466627) B466627
theorem B589465 : Blo 275825 589465 := bstep (se 2 (by rfl) ⟨221049, by rfl⟩ : syracuseStep 589465 = 442099) B442099
theorem B622259 : Blo 275825 622259 := bstep (se 1 (by rfl) ⟨466694, by rfl⟩ : syracuseStep 622259 = 933389) B933389
theorem B622295 : Blo 275825 622295 := bstep (se 1 (by rfl) ⟨466721, by rfl⟩ : syracuseStep 622295 = 933443) B933443
theorem B524083 : Blo 275825 524083 := bstep (se 1 (by rfl) ⟨393062, by rfl⟩ : syracuseStep 524083 = 786125) B786125
theorem B589619 : Blo 275825 589619 := bstep (se 1 (by rfl) ⟨442214, by rfl⟩ : syracuseStep 589619 = 884429) B884429
theorem B1048409 : Blo 275825 1048409 := bstep (se 2 (by rfl) ⟨393153, by rfl⟩ : syracuseStep 1048409 = 786307) B786307
theorem B622475 : Blo 275825 622475 := bstep (se 1 (by rfl) ⟨466856, by rfl⟩ : syracuseStep 622475 = 933713) B933713
theorem B622529 : Blo 275825 622529 := bstep (se 2 (by rfl) ⟨233448, by rfl⟩ : syracuseStep 622529 = 466897) B466897
theorem B1179613 : Blo 275825 1179613 := bstep (se 3 (by rfl) ⟨221177, by rfl⟩ : syracuseStep 1179613 = 442355) B442355
theorem B524303 : Blo 275825 524303 := bstep (se 1 (by rfl) ⟨393227, by rfl⟩ : syracuseStep 524303 = 786455) B786455
theorem B52396145 : Blo 275825 52396145 := bstep (se 2 (by rfl) ⟨19648554, by rfl⟩ : syracuseStep 52396145 = 39297109) B39297109
theorem B622727 : Blo 275825 622727 := bstep (se 1 (by rfl) ⟨467045, by rfl⟩ : syracuseStep 622727 = 934091) B934091
theorem B622907 : Blo 275825 622907 := bstep (se 1 (by rfl) ⟨467180, by rfl⟩ : syracuseStep 622907 = 934361) B934361
theorem B14418323 : Blo 275825 14418323 := bstep (se 1 (by rfl) ⟨10813742, by rfl⟩ : syracuseStep 14418323 = 21627485) B21627485
theorem B623033 : Blo 275825 623033 := bstep (se 2 (by rfl) ⟨233637, by rfl⟩ : syracuseStep 623033 = 467275) B467275
theorem B1999363 : Blo 275825 1999363 := bstep (se 1 (by rfl) ⟨1499522, by rfl⟩ : syracuseStep 1999363 = 2999045) B2999045
theorem B590483 : Blo 275825 590483 := bstep (se 1 (by rfl) ⟨442862, by rfl⟩ : syracuseStep 590483 = 885725) B885725
theorem B623375 : Blo 275825 623375 := bstep (se 1 (by rfl) ⟨467531, by rfl⟩ : syracuseStep 623375 = 935063) B935063
theorem B1803023 : Blo 275825 1803023 := bstep (se 1 (by rfl) ⟨1352267, by rfl⟩ : syracuseStep 1803023 = 2704535) B2704535
theorem B787229 : Blo 275825 787229 := bstep (se 3 (by rfl) ⟨147605, by rfl⟩ : syracuseStep 787229 = 295211) B295211
theorem B623393 : Blo 275825 623393 := bstep (se 2 (by rfl) ⟨233772, by rfl⟩ : syracuseStep 623393 = 467545) B467545
theorem B6456179 : Blo 275825 6456179 := bstep (se 1 (by rfl) ⟨4842134, by rfl⟩ : syracuseStep 6456179 = 9684269) B9684269
theorem B787457 : Blo 275825 787457 := bstep (se 2 (by rfl) ⟨295296, by rfl⟩ : syracuseStep 787457 = 590593) B590593
theorem B394247 : Blo 275825 394247 := bstep (se 1 (by rfl) ⟨295685, by rfl⟩ : syracuseStep 394247 = 591371) B591371
theorem B623735 : Blo 275825 623735 := bstep (se 1 (by rfl) ⟨467801, by rfl⟩ : syracuseStep 623735 = 935603) B935603
theorem B623915 : Blo 275825 623915 := bstep (se 1 (by rfl) ⟨467936, by rfl⟩ : syracuseStep 623915 = 935873) B935873
theorem B787799 : Blo 275825 787799 := bstep (se 1 (by rfl) ⟨590849, by rfl⟩ : syracuseStep 787799 = 1181699) B1181699
theorem B296335 : Blo 275825 296335 := bstep (se 1 (by rfl) ⟨222251, by rfl⟩ : syracuseStep 296335 = 444503) B444503
theorem B787913 : Blo 275825 787913 := bstep (se 2 (by rfl) ⟨295467, by rfl⟩ : syracuseStep 787913 = 590935) B590935
theorem B1050155 : Blo 275825 1050155 := bstep (se 1 (by rfl) ⟨787616, by rfl⟩ : syracuseStep 1050155 = 1575233) B1575233
theorem B525943 : Blo 275825 525943 := bstep (se 1 (by rfl) ⟨394457, by rfl⟩ : syracuseStep 525943 = 788915) B788915
theorem B624275 : Blo 275825 624275 := bstep (se 1 (by rfl) ⟨468206, by rfl⟩ : syracuseStep 624275 = 936413) B936413
theorem B624329 : Blo 275825 624329 := bstep (se 2 (by rfl) ⟨234123, by rfl⟩ : syracuseStep 624329 = 468247) B468247
theorem B952079 : Blo 275825 952079 := bstep (se 1 (by rfl) ⟨714059, by rfl⟩ : syracuseStep 952079 = 1428119) B1428119
theorem B2099033 : Blo 275825 2099033 := bstep (se 2 (by rfl) ⟨787137, by rfl⟩ : syracuseStep 2099033 = 1574275) B1574275
theorem B6096757 : Blo 275825 6096757 := bstep (se 5 (by rfl) ⟨285785, by rfl⟩ : syracuseStep 6096757 = 571571) B571571
theorem B1574801 : Blo 275825 1574801 := bstep (se 2 (by rfl) ⟨590550, by rfl⟩ : syracuseStep 1574801 = 1181101) B1181101
theorem B2131865 : Blo 275825 2131865 := bstep (se 2 (by rfl) ⟨799449, by rfl⟩ : syracuseStep 2131865 = 1598899) B1598899
theorem B395209 : Blo 275825 395209 := bstep (se 2 (by rfl) ⟨148203, by rfl⟩ : syracuseStep 395209 = 296407) B296407
theorem B1411019 : Blo 275825 1411019 := bstep (se 1 (by rfl) ⟨1058264, by rfl⟩ : syracuseStep 1411019 = 2116529) B2116529
theorem B3147821 : Blo 275825 3147821 := bstep (se 3 (by rfl) ⟨590216, by rfl⟩ : syracuseStep 3147821 = 1180433) B1180433
theorem B1411343 : Blo 275825 1411343 := bstep (se 1 (by rfl) ⟨1058507, by rfl⟩ : syracuseStep 1411343 = 2117015) B2117015
theorem B559403 : Blo 275825 559403 := bstep (se 1 (by rfl) ⟨419552, by rfl⟩ : syracuseStep 559403 = 839105) B839105
theorem B625031 : Blo 275825 625031 := bstep (se 1 (by rfl) ⟨468773, by rfl⟩ : syracuseStep 625031 = 937547) B937547
theorem B395705 : Blo 275825 395705 := bstep (se 2 (by rfl) ⟨148389, by rfl⟩ : syracuseStep 395705 = 296779) B296779
theorem B625211 : Blo 275825 625211 := bstep (se 1 (by rfl) ⟨468908, by rfl⟩ : syracuseStep 625211 = 937817) B937817
theorem B625337 : Blo 275825 625337 := bstep (se 2 (by rfl) ⟨234501, by rfl⟩ : syracuseStep 625337 = 469003) B469003
theorem B2100005 : Blo 275825 2100005 := bstep (se 4 (by rfl) ⟨196875, by rfl⟩ : syracuseStep 2100005 = 393751) B393751
theorem B5311493 : Blo 275825 5311493 := bstep (se 4 (by rfl) ⟨497952, by rfl⟩ : syracuseStep 5311493 = 995905) B995905
theorem B625679 : Blo 275825 625679 := bstep (se 1 (by rfl) ⟨469259, by rfl⟩ : syracuseStep 625679 = 938519) B938519
theorem B625697 : Blo 275825 625697 := bstep (se 2 (by rfl) ⟨234636, by rfl⟩ : syracuseStep 625697 = 469273) B469273
theorem B789689 : Blo 275825 789689 := bstep (se 2 (by rfl) ⟨296133, by rfl⟩ : syracuseStep 789689 = 592267) B592267
theorem B527735 : Blo 275825 527735 := bstep (se 1 (by rfl) ⟨395801, by rfl⟩ : syracuseStep 527735 = 791603) B791603
theorem B626039 : Blo 275825 626039 := bstep (se 1 (by rfl) ⟨469529, by rfl⟩ : syracuseStep 626039 = 939059) B939059
theorem B396679 : Blo 275825 396679 := bstep (se 1 (by rfl) ⟨297509, by rfl⟩ : syracuseStep 396679 = 595019) B595019
theorem B527887 : Blo 275825 527887 := bstep (se 1 (by rfl) ⟨395915, by rfl⟩ : syracuseStep 527887 = 791831) B791831
theorem B626219 : Blo 275825 626219 := bstep (se 1 (by rfl) ⟨469664, by rfl⟩ : syracuseStep 626219 = 939329) B939329
theorem B2887235 : Blo 275825 2887235 := bstep (se 1 (by rfl) ⟨2165426, by rfl⟩ : syracuseStep 2887235 = 4330853) B4330853
theorem B1412801 : Blo 275825 1412801 := bstep (se 2 (by rfl) ⟨529800, by rfl⟩ : syracuseStep 1412801 = 1059601) B1059601
theorem B14946049 : Blo 275825 14946049 := bstep (se 2 (by rfl) ⟨5604768, by rfl⟩ : syracuseStep 14946049 = 11209537) B11209537
theorem B528275 : Blo 275825 528275 := bstep (se 1 (by rfl) ⟨396206, by rfl⟩ : syracuseStep 528275 = 792413) B792413
theorem B626579 : Blo 275825 626579 := bstep (se 1 (by rfl) ⟨469934, by rfl⟩ : syracuseStep 626579 = 939869) B939869
theorem B5476247 : Blo 275825 5476247 := bstep (se 1 (by rfl) ⟨4107185, by rfl⟩ : syracuseStep 5476247 = 8214371) B8214371
theorem B626633 : Blo 275825 626633 := bstep (se 2 (by rfl) ⟨234987, by rfl⟩ : syracuseStep 626633 = 469975) B469975
theorem B790681 : Blo 275825 790681 := bstep (se 2 (by rfl) ⟨296505, by rfl⟩ : syracuseStep 790681 = 593011) B593011
theorem B2691245 : Blo 275825 2691245 := bstep (se 3 (by rfl) ⟨504608, by rfl⟩ : syracuseStep 2691245 = 1009217) B1009217
theorem B1216921 : Blo 275825 1216921 := bstep (se 2 (by rfl) ⟨456345, by rfl⟩ : syracuseStep 1216921 = 912691) B912691
theorem B6754859 : Blo 275825 6754859 := bstep (se 1 (by rfl) ⟨5066144, by rfl⟩ : syracuseStep 6754859 = 10132289) B10132289
theorem B627335 : Blo 275825 627335 := bstep (se 1 (by rfl) ⟨470501, by rfl⟩ : syracuseStep 627335 = 941003) B941003
theorem B2265893 : Blo 275825 2265893 := bstep (se 4 (by rfl) ⟨212427, by rfl⟩ : syracuseStep 2265893 = 424855) B424855
theorem B398137 : Blo 275825 398137 := bstep (se 2 (by rfl) ⟨149301, by rfl⟩ : syracuseStep 398137 = 298603) B298603
theorem B627515 : Blo 275825 627515 := bstep (se 1 (by rfl) ⟨470636, by rfl⟩ : syracuseStep 627515 = 941273) B941273
theorem B1053587 : Blo 275825 1053587 := bstep (se 1 (by rfl) ⟨790190, by rfl⟩ : syracuseStep 1053587 = 1580381) B1580381
theorem B627641 : Blo 275825 627641 := bstep (se 2 (by rfl) ⟨235365, by rfl⟩ : syracuseStep 627641 = 470731) B470731
theorem B1414097 : Blo 275825 1414097 := bstep (se 2 (by rfl) ⟨530286, by rfl⟩ : syracuseStep 1414097 = 1060573) B1060573
theorem B726059 : Blo 275825 726059 := bstep (se 1 (by rfl) ⟨544544, by rfl⟩ : syracuseStep 726059 = 1089089) B1089089
theorem B1610813 : Blo 275825 1610813 := bstep (se 3 (by rfl) ⟨302027, by rfl⟩ : syracuseStep 1610813 = 604055) B604055
theorem B529679 : Blo 275825 529679 := bstep (se 1 (by rfl) ⟨397259, by rfl⟩ : syracuseStep 529679 = 794519) B794519
theorem B627983 : Blo 275825 627983 := bstep (se 1 (by rfl) ⟨470987, by rfl⟩ : syracuseStep 627983 = 941975) B941975
theorem B628001 : Blo 275825 628001 := bstep (se 2 (by rfl) ⟨235500, by rfl⟩ : syracuseStep 628001 = 471001) B471001
theorem B628343 : Blo 275825 628343 := bstep (se 1 (by rfl) ⟨471257, by rfl⟩ : syracuseStep 628343 = 942515) B942515
theorem B857753 : Blo 275825 857753 := bstep (se 2 (by rfl) ⟨321657, by rfl⟩ : syracuseStep 857753 = 643315) B643315
theorem B595745 : Blo 275825 595745 := bstep (se 2 (by rfl) ⟨223404, by rfl⟩ : syracuseStep 595745 = 446809) B446809
theorem B530219 : Blo 275825 530219 := bstep (se 1 (by rfl) ⟨397664, by rfl⟩ : syracuseStep 530219 = 795329) B795329
theorem B628523 : Blo 275825 628523 := bstep (se 1 (by rfl) ⟨471392, by rfl⟩ : syracuseStep 628523 = 942785) B942785
theorem B890759 : Blo 275825 890759 := bstep (se 1 (by rfl) ⟨668069, by rfl⟩ : syracuseStep 890759 = 1336139) B1336139
theorem B2660363 : Blo 275825 2660363 := bstep (se 1 (by rfl) ⟨1995272, by rfl⟩ : syracuseStep 2660363 = 3990545) B3990545
theorem B792605 : Blo 275825 792605 := bstep (se 3 (by rfl) ⟨148613, by rfl⟩ : syracuseStep 792605 = 297227) B297227
theorem B628883 : Blo 275825 628883 := bstep (se 1 (by rfl) ⟨471662, by rfl⟩ : syracuseStep 628883 = 943325) B943325
theorem B628937 : Blo 275825 628937 := bstep (se 2 (by rfl) ⟨235851, by rfl⟩ : syracuseStep 628937 = 471703) B471703
theorem B563489 : Blo 275825 563489 := bstep (se 2 (by rfl) ⟨211308, by rfl⟩ : syracuseStep 563489 = 422617) B422617
theorem B891271 : Blo 275825 891271 := bstep (se 1 (by rfl) ⟨668453, by rfl⟩ : syracuseStep 891271 = 1336907) B1336907
theorem B1546775 : Blo 275825 1546775 := bstep (se 1 (by rfl) ⟨1160081, by rfl⟩ : syracuseStep 1546775 = 2320163) B2320163
theorem B1579607 : Blo 275825 1579607 := bstep (se 1 (by rfl) ⟨1184705, by rfl⟩ : syracuseStep 1579607 = 2369411) B2369411
theorem B465527 : Blo 275825 465527 := bstep (se 1 (by rfl) ⟨349145, by rfl⟩ : syracuseStep 465527 = 698291) B698291
theorem B563831 : Blo 275825 563831 := bstep (se 1 (by rfl) ⟨422873, by rfl⟩ : syracuseStep 563831 = 845747) B845747
theorem B793289 : Blo 275825 793289 := bstep (se 2 (by rfl) ⟨297483, by rfl⟩ : syracuseStep 793289 = 594967) B594967
theorem B1416203 : Blo 275825 1416203 := bstep (se 1 (by rfl) ⟨1062152, by rfl⟩ : syracuseStep 1416203 = 2124305) B2124305
theorem B465979 : Blo 275825 465979 := bstep (se 1 (by rfl) ⟨349484, by rfl⟩ : syracuseStep 465979 = 698969) B698969
theorem B1416365 : Blo 275825 1416365 := bstep (se 3 (by rfl) ⟨265568, by rfl⟩ : syracuseStep 1416365 = 531137) B531137
theorem B466121 : Blo 275825 466121 := bstep (se 2 (by rfl) ⟨174795, by rfl⟩ : syracuseStep 466121 = 349591) B349591
theorem B335111 : Blo 275825 335111 := bstep (se 1 (by rfl) ⟨251333, by rfl⟩ : syracuseStep 335111 = 502667) B502667
theorem B793871 : Blo 275825 793871 := bstep (se 1 (by rfl) ⟨595403, by rfl⟩ : syracuseStep 793871 = 1190807) B1190807
theorem B1187131 : Blo 275825 1187131 := bstep (se 1 (by rfl) ⟨890348, by rfl⟩ : syracuseStep 1187131 = 1780697) B1780697
theorem B1056185 : Blo 275825 1056185 := bstep (se 2 (by rfl) ⟨396069, by rfl⟩ : syracuseStep 1056185 = 792139) B792139
theorem B2137529 : Blo 275825 2137529 := bstep (se 2 (by rfl) ⟨801573, by rfl⟩ : syracuseStep 2137529 = 1603147) B1603147
theorem B302599 : Blo 275825 302599 := bstep (se 1 (by rfl) ⟨226949, by rfl⟩ : syracuseStep 302599 = 453899) B453899
theorem B597547 : Blo 275825 597547 := bstep (se 1 (by rfl) ⟨448160, by rfl⟩ : syracuseStep 597547 = 896321) B896321
theorem B466823 : Blo 275825 466823 := bstep (se 1 (by rfl) ⟨350117, by rfl⟩ : syracuseStep 466823 = 700235) B700235
theorem B2858905 : Blo 275825 2858905 := bstep (se 2 (by rfl) ⟨1072089, by rfl⟩ : syracuseStep 2858905 = 2144179) B2144179
theorem B7217099 : Blo 275825 7217099 := bstep (se 1 (by rfl) ⟨5412824, by rfl⟩ : syracuseStep 7217099 = 10825649) B10825649
theorem B893015 : Blo 275825 893015 := bstep (se 1 (by rfl) ⟨669761, by rfl⟩ : syracuseStep 893015 = 1339523) B1339523
theorem B3449033 : Blo 275825 3449033 := bstep (se 2 (by rfl) ⟨1293387, by rfl⟩ : syracuseStep 3449033 = 2586775) B2586775
theorem B729479 : Blo 275825 729479 := bstep (se 1 (by rfl) ⟨547109, by rfl⟩ : syracuseStep 729479 = 1094219) B1094219
theorem B1057171 : Blo 275825 1057171 := bstep (se 1 (by rfl) ⟨792878, by rfl⟩ : syracuseStep 1057171 = 1585757) B1585757
theorem B467471 : Blo 275825 467471 := bstep (se 1 (by rfl) ⟨350603, by rfl⟩ : syracuseStep 467471 = 701207) B701207
theorem B565793 : Blo 275825 565793 := bstep (se 2 (by rfl) ⟨212172, by rfl⟩ : syracuseStep 565793 = 424345) B424345
theorem B795271 : Blo 275825 795271 := bstep (se 1 (by rfl) ⟨596453, by rfl⟩ : syracuseStep 795271 = 1192907) B1192907
theorem B1581839 : Blo 275825 1581839 := bstep (se 1 (by rfl) ⟨1186379, by rfl⟩ : syracuseStep 1581839 = 2372759) B2372759
theorem B336683 : Blo 275825 336683 := bstep (se 1 (by rfl) ⟨252512, by rfl⟩ : syracuseStep 336683 = 505025) B505025
theorem B664379 : Blo 275825 664379 := bstep (se 1 (by rfl) ⟨498284, by rfl⟩ : syracuseStep 664379 = 996569) B996569
theorem B795545 : Blo 275825 795545 := bstep (se 2 (by rfl) ⟨298329, by rfl⟩ : syracuseStep 795545 = 596659) B596659
theorem B1778699 : Blo 275825 1778699 := bstep (se 1 (by rfl) ⟨1334024, by rfl⟩ : syracuseStep 1778699 = 2668049) B2668049
theorem B1582091 : Blo 275825 1582091 := bstep (se 1 (by rfl) ⟨1186568, by rfl⟩ : syracuseStep 1582091 = 2373137) B2373137
theorem B664609 : Blo 275825 664609 := bstep (se 2 (by rfl) ⟨249228, by rfl⟩ : syracuseStep 664609 = 498457) B498457
theorem B468011 : Blo 275825 468011 := bstep (se 1 (by rfl) ⟨351008, by rfl⟩ : syracuseStep 468011 = 702017) B702017
theorem B599329 : Blo 275825 599329 := bstep (se 2 (by rfl) ⟨224748, by rfl⟩ : syracuseStep 599329 = 449497) B449497
theorem B664985 : Blo 275825 664985 := bstep (se 2 (by rfl) ⟨249369, by rfl⟩ : syracuseStep 664985 = 498739) B498739
theorem B1123769 : Blo 275825 1123769 := bstep (se 2 (by rfl) ⟨421413, by rfl⟩ : syracuseStep 1123769 = 842827) B842827
theorem B2106809 : Blo 275825 2106809 := bstep (se 2 (by rfl) ⟨790053, by rfl⟩ : syracuseStep 2106809 = 1580107) B1580107
theorem B468409 : Blo 275825 468409 := bstep (se 2 (by rfl) ⟨175653, by rfl⟩ : syracuseStep 468409 = 351307) B351307
theorem B1680983 : Blo 275825 1680983 := bstep (se 1 (by rfl) ⟨1260737, by rfl⟩ : syracuseStep 1680983 = 2521475) B2521475
theorem B1124111 : Blo 275825 1124111 := bstep (se 1 (by rfl) ⟨843083, by rfl⟩ : syracuseStep 1124111 = 1686167) B1686167
theorem B501623 : Blo 275825 501623 := bstep (se 1 (by rfl) ⟨376217, by rfl⟩ : syracuseStep 501623 = 752435) B752435
theorem B1058903 : Blo 275825 1058903 := bstep (se 1 (by rfl) ⟨794177, by rfl⟩ : syracuseStep 1058903 = 1588355) B1588355
theorem B698483 : Blo 275825 698483 := bstep (se 1 (by rfl) ⟨523862, by rfl⟩ : syracuseStep 698483 = 1047725) B1047725
theorem B796787 : Blo 275825 796787 := bstep (se 1 (by rfl) ⟨597590, by rfl⟩ : syracuseStep 796787 = 1195181) B1195181
theorem B469111 : Blo 275825 469111 := bstep (se 1 (by rfl) ⟨351833, by rfl⟩ : syracuseStep 469111 = 703667) B703667
theorem B698503 : Blo 275825 698503 := bstep (se 1 (by rfl) ⟨523877, by rfl⟩ : syracuseStep 698503 = 1047755) B1047755
theorem B1583297 : Blo 275825 1583297 := bstep (se 2 (by rfl) ⟨593736, by rfl⟩ : syracuseStep 1583297 = 1187473) B1187473
theorem B469307 : Blo 275825 469307 := bstep (se 1 (by rfl) ⟨351980, by rfl⟩ : syracuseStep 469307 = 703961) B703961
theorem B698777 : Blo 275825 698777 := bstep (se 2 (by rfl) ⟨262041, by rfl⟩ : syracuseStep 698777 = 524083) B524083
theorem B698939 : Blo 275825 698939 := bstep (se 1 (by rfl) ⟨524204, by rfl⟩ : syracuseStep 698939 = 1048409) B1048409
theorem B1059389 : Blo 275825 1059389 := bstep (se 3 (by rfl) ⟨198635, by rfl⟩ : syracuseStep 1059389 = 397271) B397271
theorem B469705 : Blo 275825 469705 := bstep (se 2 (by rfl) ⟨176139, by rfl⟩ : syracuseStep 469705 = 352279) B352279
theorem B699151 : Blo 275825 699151 := bstep (se 1 (by rfl) ⟨524363, by rfl⟩ : syracuseStep 699151 = 1048727) B1048727
theorem B699425 : Blo 275825 699425 := bstep (se 2 (by rfl) ⟨262284, by rfl⟩ : syracuseStep 699425 = 524569) B524569
theorem B470407 : Blo 275825 470407 := bstep (se 1 (by rfl) ⟨352805, by rfl⟩ : syracuseStep 470407 = 705611) B705611
theorem B1420753 : Blo 275825 1420753 := bstep (se 2 (by rfl) ⟨532782, by rfl⟩ : syracuseStep 1420753 = 1065565) B1065565
theorem B700427 : Blo 275825 700427 := bstep (se 1 (by rfl) ⟨525320, by rfl⟩ : syracuseStep 700427 = 1050641) B1050641
theorem B3158027 : Blo 275825 3158027 := bstep (se 1 (by rfl) ⟨2368520, by rfl⟩ : syracuseStep 3158027 = 4737041) B4737041
theorem B471055 : Blo 275825 471055 := bstep (se 1 (by rfl) ⟨353291, by rfl⟩ : syracuseStep 471055 = 706583) B706583
theorem B503993 : Blo 275825 503993 := bstep (se 2 (by rfl) ⟨188997, by rfl⟩ : syracuseStep 503993 = 377995) B377995
theorem B2044295 : Blo 275825 2044295 := bstep (se 1 (by rfl) ⟨1533221, by rfl⟩ : syracuseStep 2044295 = 3066443) B3066443
theorem B471595 : Blo 275825 471595 := bstep (se 1 (by rfl) ⟨353696, by rfl⟩ : syracuseStep 471595 = 707393) B707393
theorem B701075 : Blo 275825 701075 := bstep (se 1 (by rfl) ⟨525806, by rfl⟩ : syracuseStep 701075 = 1051613) B1051613
theorem B471737 : Blo 275825 471737 := bstep (se 2 (by rfl) ⟨176901, by rfl⟩ : syracuseStep 471737 = 353803) B353803
theorem B668569 : Blo 275825 668569 := bstep (se 2 (by rfl) ⟨250713, by rfl⟩ : syracuseStep 668569 = 501427) B501427
theorem B701369 : Blo 275825 701369 := bstep (se 2 (by rfl) ⟨263013, by rfl⟩ : syracuseStep 701369 = 526027) B526027
theorem B1127353 : Blo 275825 1127353 := bstep (se 2 (by rfl) ⟨422757, by rfl⟩ : syracuseStep 1127353 = 845515) B845515
theorem B1586465 : Blo 275825 1586465 := bstep (se 2 (by rfl) ⟨594924, by rfl⟩ : syracuseStep 1586465 = 1189849) B1189849
theorem B275847 : Blo 275825 275847 := bstep (se 1 (by rfl) ⟨206885, by rfl⟩ : syracuseStep 275847 = 413771) B413771
theorem B275855 : Blo 275825 275855 := bstep (se 1 (by rfl) ⟨206891, by rfl⟩ : syracuseStep 275855 = 413783) B413783
theorem B275899 : Blo 275825 275899 := bstep (se 1 (by rfl) ⟨206924, by rfl⟩ : syracuseStep 275899 = 413849) B413849
theorem B669185 : Blo 275825 669185 := bstep (se 2 (by rfl) ⟨250944, by rfl⟩ : syracuseStep 669185 = 501889) B501889
theorem B3225091 : Blo 275825 3225091 := bstep (se 1 (by rfl) ⟨2418818, by rfl⟩ : syracuseStep 3225091 = 4837637) B4837637
theorem B275975 : Blo 275825 275975 := bstep (se 1 (by rfl) ⟨206981, by rfl⟩ : syracuseStep 275975 = 413963) B413963
theorem B275983 : Blo 275825 275983 := bstep (se 1 (by rfl) ⟨206987, by rfl⟩ : syracuseStep 275983 = 413975) B413975
theorem B276027 : Blo 275825 276027 := bstep (se 1 (by rfl) ⟨207020, by rfl⟩ : syracuseStep 276027 = 414041) B414041
theorem B3356225 : Blo 275825 3356225 := bstep (se 2 (by rfl) ⟨1258584, by rfl⟩ : syracuseStep 3356225 = 2517169) B2517169
theorem B702067 : Blo 275825 702067 := bstep (se 1 (by rfl) ⟨526550, by rfl⟩ : syracuseStep 702067 = 1053101) B1053101
theorem B276103 : Blo 275825 276103 := bstep (se 1 (by rfl) ⟨207077, by rfl⟩ : syracuseStep 276103 = 414155) B414155
theorem B276111 : Blo 275825 276111 := bstep (se 1 (by rfl) ⟨207083, by rfl⟩ : syracuseStep 276111 = 414167) B414167
theorem B276155 : Blo 275825 276155 := bstep (se 1 (by rfl) ⟨207116, by rfl⟩ : syracuseStep 276155 = 414233) B414233
theorem B702209 : Blo 275825 702209 := bstep (se 2 (by rfl) ⟨263328, by rfl⟩ : syracuseStep 702209 = 526657) B526657
theorem B276231 : Blo 275825 276231 := bstep (se 1 (by rfl) ⟨207173, by rfl⟩ : syracuseStep 276231 = 414347) B414347
theorem B276239 : Blo 275825 276239 := bstep (se 1 (by rfl) ⟨207179, by rfl⟩ : syracuseStep 276239 = 414359) B414359
theorem B669473 : Blo 275825 669473 := bstep (se 2 (by rfl) ⟨251052, by rfl⟩ : syracuseStep 669473 = 502105) B502105
theorem B276283 : Blo 275825 276283 := bstep (se 1 (by rfl) ⟨207212, by rfl⟩ : syracuseStep 276283 = 414425) B414425
theorem B276359 : Blo 275825 276359 := bstep (se 1 (by rfl) ⟨207269, by rfl⟩ : syracuseStep 276359 = 414539) B414539
theorem B276367 : Blo 275825 276367 := bstep (se 1 (by rfl) ⟨207275, by rfl⟩ : syracuseStep 276367 = 414551) B414551
theorem B931769 : Blo 275825 931769 := bstep (se 2 (by rfl) ⟨349413, by rfl⟩ : syracuseStep 931769 = 698827) B698827
theorem B276411 : Blo 275825 276411 := bstep (se 1 (by rfl) ⟨207308, by rfl⟩ : syracuseStep 276411 = 414617) B414617
theorem B276487 : Blo 275825 276487 := bstep (se 1 (by rfl) ⟨207365, by rfl⟩ : syracuseStep 276487 = 414731) B414731
theorem B276495 : Blo 275825 276495 := bstep (se 1 (by rfl) ⟨207371, by rfl⟩ : syracuseStep 276495 = 414743) B414743
theorem B276539 : Blo 275825 276539 := bstep (se 1 (by rfl) ⟨207404, by rfl⟩ : syracuseStep 276539 = 414809) B414809
theorem B276615 : Blo 275825 276615 := bstep (se 1 (by rfl) ⟨207461, by rfl⟩ : syracuseStep 276615 = 414923) B414923
theorem B276623 : Blo 275825 276623 := bstep (se 1 (by rfl) ⟨207467, by rfl⟩ : syracuseStep 276623 = 414935) B414935
theorem B276667 : Blo 275825 276667 := bstep (se 1 (by rfl) ⟨207500, by rfl⟩ : syracuseStep 276667 = 415001) B415001
theorem B702665 : Blo 275825 702665 := bstep (se 2 (by rfl) ⟨263499, by rfl⟩ : syracuseStep 702665 = 526999) B526999
theorem B276743 : Blo 275825 276743 := bstep (se 1 (by rfl) ⟨207557, by rfl⟩ : syracuseStep 276743 = 415115) B415115
theorem B473359 : Blo 275825 473359 := bstep (se 1 (by rfl) ⟨355019, by rfl⟩ : syracuseStep 473359 = 710039) B710039
theorem B276751 : Blo 275825 276751 := bstep (se 1 (by rfl) ⟨207563, by rfl⟩ : syracuseStep 276751 = 415127) B415127
theorem B276795 : Blo 275825 276795 := bstep (se 1 (by rfl) ⟨207596, by rfl⟩ : syracuseStep 276795 = 415193) B415193
theorem B276871 : Blo 275825 276871 := bstep (se 1 (by rfl) ⟨207653, by rfl⟩ : syracuseStep 276871 = 415307) B415307
theorem B276879 : Blo 275825 276879 := bstep (se 1 (by rfl) ⟨207659, by rfl⟩ : syracuseStep 276879 = 415319) B415319
theorem B276923 : Blo 275825 276923 := bstep (se 1 (by rfl) ⟨207692, by rfl⟩ : syracuseStep 276923 = 415385) B415385
theorem B276999 : Blo 275825 276999 := bstep (se 1 (by rfl) ⟨207749, by rfl⟩ : syracuseStep 276999 = 415499) B415499
theorem B932363 : Blo 275825 932363 := bstep (se 1 (by rfl) ⟨699272, by rfl⟩ : syracuseStep 932363 = 1398545) B1398545
theorem B277007 : Blo 275825 277007 := bstep (se 1 (by rfl) ⟨207755, by rfl⟩ : syracuseStep 277007 = 415511) B415511
theorem B703019 : Blo 275825 703019 := bstep (se 1 (by rfl) ⟨527264, by rfl⟩ : syracuseStep 703019 = 1054529) B1054529
theorem B277051 : Blo 275825 277051 := bstep (se 1 (by rfl) ⟨207788, by rfl⟩ : syracuseStep 277051 = 415577) B415577
theorem B932471 : Blo 275825 932471 := bstep (se 1 (by rfl) ⟨699353, by rfl⟩ : syracuseStep 932471 = 1398707) B1398707
theorem B277127 : Blo 275825 277127 := bstep (se 1 (by rfl) ⟨207845, by rfl⟩ : syracuseStep 277127 = 415691) B415691
theorem B277135 : Blo 275825 277135 := bstep (se 1 (by rfl) ⟨207851, by rfl⟩ : syracuseStep 277135 = 415703) B415703
theorem B277179 : Blo 275825 277179 := bstep (se 1 (by rfl) ⟨207884, by rfl⟩ : syracuseStep 277179 = 415769) B415769
theorem B277255 : Blo 275825 277255 := bstep (se 1 (by rfl) ⟨207941, by rfl⟩ : syracuseStep 277255 = 415883) B415883
theorem B277263 : Blo 275825 277263 := bstep (se 1 (by rfl) ⟨207947, by rfl⟩ : syracuseStep 277263 = 415895) B415895
theorem B277307 : Blo 275825 277307 := bstep (se 1 (by rfl) ⟨207980, by rfl⟩ : syracuseStep 277307 = 415961) B415961
theorem B277383 : Blo 275825 277383 := bstep (se 1 (by rfl) ⟨208037, by rfl⟩ : syracuseStep 277383 = 416075) B416075
theorem B277391 : Blo 275825 277391 := bstep (se 1 (by rfl) ⟨208043, by rfl⟩ : syracuseStep 277391 = 416087) B416087
theorem B277435 : Blo 275825 277435 := bstep (se 1 (by rfl) ⟨208076, by rfl⟩ : syracuseStep 277435 = 416153) B416153
theorem B277511 : Blo 275825 277511 := bstep (se 1 (by rfl) ⟨208133, by rfl⟩ : syracuseStep 277511 = 416267) B416267
theorem B277519 : Blo 275825 277519 := bstep (se 1 (by rfl) ⟨208139, by rfl⟩ : syracuseStep 277519 = 416279) B416279
theorem B277563 : Blo 275825 277563 := bstep (se 1 (by rfl) ⟨208172, by rfl⟩ : syracuseStep 277563 = 416345) B416345
theorem B277639 : Blo 275825 277639 := bstep (se 1 (by rfl) ⟨208229, by rfl⟩ : syracuseStep 277639 = 416459) B416459
theorem B277647 : Blo 275825 277647 := bstep (se 1 (by rfl) ⟨208235, by rfl⟩ : syracuseStep 277647 = 416471) B416471
theorem B310459 : Blo 275825 310459 := bstep (se 1 (by rfl) ⟨232844, by rfl⟩ : syracuseStep 310459 = 465689) B465689
theorem B277691 : Blo 275825 277691 := bstep (se 1 (by rfl) ⟨208268, by rfl⟩ : syracuseStep 277691 = 416537) B416537
theorem B933065 : Blo 275825 933065 := bstep (se 2 (by rfl) ⟨349899, by rfl⟩ : syracuseStep 933065 = 699799) B699799
theorem B277767 : Blo 275825 277767 := bstep (se 1 (by rfl) ⟨208325, by rfl⟩ : syracuseStep 277767 = 416651) B416651
theorem B277775 : Blo 275825 277775 := bstep (se 1 (by rfl) ⟨208331, by rfl⟩ : syracuseStep 277775 = 416663) B416663
theorem B277819 : Blo 275825 277819 := bstep (se 1 (by rfl) ⟨208364, by rfl⟩ : syracuseStep 277819 = 416729) B416729
theorem B277895 : Blo 275825 277895 := bstep (se 1 (by rfl) ⟨208421, by rfl⟩ : syracuseStep 277895 = 416843) B416843
theorem B277903 : Blo 275825 277903 := bstep (se 1 (by rfl) ⟨208427, by rfl⟩ : syracuseStep 277903 = 416855) B416855
theorem B277947 : Blo 275825 277947 := bstep (se 1 (by rfl) ⟨208460, by rfl⟩ : syracuseStep 277947 = 416921) B416921
theorem B376265 : Blo 275825 376265 := bstep (se 2 (by rfl) ⟨141099, by rfl⟩ : syracuseStep 376265 = 282199) B282199
theorem B278023 : Blo 275825 278023 := bstep (se 1 (by rfl) ⟨208517, by rfl⟩ : syracuseStep 278023 = 417035) B417035
theorem B704011 : Blo 275825 704011 := bstep (se 1 (by rfl) ⟨528008, by rfl⟩ : syracuseStep 704011 = 1056017) B1056017
theorem B278031 : Blo 275825 278031 := bstep (se 1 (by rfl) ⟨208523, by rfl⟩ : syracuseStep 278031 = 417047) B417047
theorem B278075 : Blo 275825 278075 := bstep (se 1 (by rfl) ⟨208556, by rfl⟩ : syracuseStep 278075 = 417113) B417113
theorem B671291 : Blo 275825 671291 := bstep (se 1 (by rfl) ⟨503468, by rfl⟩ : syracuseStep 671291 = 1006937) B1006937
theorem B1588855 : Blo 275825 1588855 := bstep (se 1 (by rfl) ⟨1191641, by rfl⟩ : syracuseStep 1588855 = 2383283) B2383283
theorem B278151 : Blo 275825 278151 := bstep (se 1 (by rfl) ⟨208613, by rfl⟩ : syracuseStep 278151 = 417227) B417227
theorem B310927 : Blo 275825 310927 := bstep (se 1 (by rfl) ⟨233195, by rfl⟩ : syracuseStep 310927 = 466391) B466391
theorem B278159 : Blo 275825 278159 := bstep (se 1 (by rfl) ⟨208619, by rfl⟩ : syracuseStep 278159 = 417239) B417239
theorem B704153 : Blo 275825 704153 := bstep (se 2 (by rfl) ⟨264057, by rfl⟩ : syracuseStep 704153 = 528115) B528115
theorem B278203 : Blo 275825 278203 := bstep (se 1 (by rfl) ⟨208652, by rfl⟩ : syracuseStep 278203 = 417305) B417305
theorem B278279 : Blo 275825 278279 := bstep (se 1 (by rfl) ⟨208709, by rfl⟩ : syracuseStep 278279 = 417419) B417419
theorem B278287 : Blo 275825 278287 := bstep (se 1 (by rfl) ⟨208715, by rfl⟩ : syracuseStep 278287 = 417431) B417431
theorem B704315 : Blo 275825 704315 := bstep (se 1 (by rfl) ⟨528236, by rfl⟩ : syracuseStep 704315 = 1056473) B1056473
theorem B278331 : Blo 275825 278331 := bstep (se 1 (by rfl) ⟨208748, by rfl⟩ : syracuseStep 278331 = 417497) B417497
theorem B933767 : Blo 275825 933767 := bstep (se 1 (by rfl) ⟨700325, by rfl⟩ : syracuseStep 933767 = 1400651) B1400651
theorem B278407 : Blo 275825 278407 := bstep (se 1 (by rfl) ⟨208805, by rfl⟩ : syracuseStep 278407 = 417611) B417611
theorem B278415 : Blo 275825 278415 := bstep (se 1 (by rfl) ⟨208811, by rfl⟩ : syracuseStep 278415 = 417623) B417623
theorem B278459 : Blo 275825 278459 := bstep (se 1 (by rfl) ⟨208844, by rfl⟩ : syracuseStep 278459 = 417689) B417689
theorem B278535 : Blo 275825 278535 := bstep (se 1 (by rfl) ⟨208901, by rfl⟩ : syracuseStep 278535 = 417803) B417803
theorem B278543 : Blo 275825 278543 := bstep (se 1 (by rfl) ⟨208907, by rfl⟩ : syracuseStep 278543 = 417815) B417815
theorem B278587 : Blo 275825 278587 := bstep (se 1 (by rfl) ⟨208940, by rfl⟩ : syracuseStep 278587 = 417881) B417881
theorem B311431 : Blo 275825 311431 := bstep (se 1 (by rfl) ⟨233573, by rfl⟩ : syracuseStep 311431 = 467147) B467147
theorem B278663 : Blo 275825 278663 := bstep (se 1 (by rfl) ⟨208997, by rfl⟩ : syracuseStep 278663 = 417995) B417995
theorem B278671 : Blo 275825 278671 := bstep (se 1 (by rfl) ⟨209003, by rfl⟩ : syracuseStep 278671 = 418007) B418007
theorem B704659 : Blo 275825 704659 := bstep (se 1 (by rfl) ⟨528494, by rfl⟩ : syracuseStep 704659 = 1056989) B1056989
theorem B278715 : Blo 275825 278715 := bstep (se 1 (by rfl) ⟨209036, by rfl⟩ : syracuseStep 278715 = 418073) B418073
theorem B9257161 : Blo 275825 9257161 := bstep (se 2 (by rfl) ⟨3471435, by rfl⟩ : syracuseStep 9257161 = 6942871) B6942871
theorem B934145 : Blo 275825 934145 := bstep (se 2 (by rfl) ⟨350304, by rfl⟩ : syracuseStep 934145 = 700609) B700609
theorem B278791 : Blo 275825 278791 := bstep (se 1 (by rfl) ⟨209093, by rfl⟩ : syracuseStep 278791 = 418187) B418187
theorem B278799 : Blo 275825 278799 := bstep (se 1 (by rfl) ⟨209099, by rfl⟩ : syracuseStep 278799 = 418199) B418199
theorem B3162401 : Blo 275825 3162401 := bstep (se 2 (by rfl) ⟨1185900, by rfl⟩ : syracuseStep 3162401 = 2371801) B2371801
theorem B704801 : Blo 275825 704801 := bstep (se 2 (by rfl) ⟨264300, by rfl⟩ : syracuseStep 704801 = 528601) B528601
theorem B311611 : Blo 275825 311611 := bstep (se 1 (by rfl) ⟨233708, by rfl⟩ : syracuseStep 311611 = 467417) B467417
theorem B278843 : Blo 275825 278843 := bstep (se 1 (by rfl) ⟨209132, by rfl⟩ : syracuseStep 278843 = 418265) B418265
theorem B672059 : Blo 275825 672059 := bstep (se 1 (by rfl) ⟨504044, by rfl⟩ : syracuseStep 672059 = 1008089) B1008089
theorem B278919 : Blo 275825 278919 := bstep (se 1 (by rfl) ⟨209189, by rfl⟩ : syracuseStep 278919 = 418379) B418379
theorem B278927 : Blo 275825 278927 := bstep (se 1 (by rfl) ⟨209195, by rfl⟩ : syracuseStep 278927 = 418391) B418391
theorem B278971 : Blo 275825 278971 := bstep (se 1 (by rfl) ⟨209228, by rfl⟩ : syracuseStep 278971 = 418457) B418457
theorem B279047 : Blo 275825 279047 := bstep (se 1 (by rfl) ⟨209285, by rfl⟩ : syracuseStep 279047 = 418571) B418571
theorem B279055 : Blo 275825 279055 := bstep (se 1 (by rfl) ⟨209291, by rfl⟩ : syracuseStep 279055 = 418583) B418583
theorem B5980715 : Blo 275825 5980715 := bstep (se 1 (by rfl) ⟨4485536, by rfl⟩ : syracuseStep 5980715 = 8971073) B8971073
theorem B279099 : Blo 275825 279099 := bstep (se 1 (by rfl) ⟨209324, by rfl⟩ : syracuseStep 279099 = 418649) B418649
theorem B1360451 : Blo 275825 1360451 := bstep (se 1 (by rfl) ⟨1020338, by rfl⟩ : syracuseStep 1360451 = 2040677) B2040677
theorem B279175 : Blo 275825 279175 := bstep (se 1 (by rfl) ⟨209381, by rfl⟩ : syracuseStep 279175 = 418763) B418763
theorem B279183 : Blo 275825 279183 := bstep (se 1 (by rfl) ⟨209387, by rfl⟩ : syracuseStep 279183 = 418775) B418775
theorem B279227 : Blo 275825 279227 := bstep (se 1 (by rfl) ⟨209420, by rfl⟩ : syracuseStep 279227 = 418841) B418841
theorem B2376449 : Blo 275825 2376449 := bstep (se 2 (by rfl) ⟨891168, by rfl⟩ : syracuseStep 2376449 = 1782337) B1782337
theorem B279303 : Blo 275825 279303 := bstep (se 1 (by rfl) ⟨209477, by rfl⟩ : syracuseStep 279303 = 418955) B418955
theorem B312079 : Blo 275825 312079 := bstep (se 1 (by rfl) ⟨234059, by rfl⟩ : syracuseStep 312079 = 468119) B468119
theorem B279311 : Blo 275825 279311 := bstep (se 1 (by rfl) ⟨209483, by rfl⟩ : syracuseStep 279311 = 418967) B418967
theorem B3982117 : Blo 275825 3982117 := bstep (se 4 (by rfl) ⟨373323, by rfl⟩ : syracuseStep 3982117 = 746647) B746647
theorem B279355 : Blo 275825 279355 := bstep (se 1 (by rfl) ⟨209516, by rfl⟩ : syracuseStep 279355 = 419033) B419033
theorem B1590131 : Blo 275825 1590131 := bstep (se 1 (by rfl) ⟨1192598, by rfl⟩ : syracuseStep 1590131 = 2385197) B2385197
theorem B279431 : Blo 275825 279431 := bstep (se 1 (by rfl) ⟨209573, by rfl⟩ : syracuseStep 279431 = 419147) B419147
theorem B377735 : Blo 275825 377735 := bstep (se 1 (by rfl) ⟨283301, by rfl⟩ : syracuseStep 377735 = 566603) B566603
theorem B279439 : Blo 275825 279439 := bstep (se 1 (by rfl) ⟨209579, by rfl⟩ : syracuseStep 279439 = 419159) B419159
theorem B279483 : Blo 275825 279483 := bstep (se 1 (by rfl) ⟨209612, by rfl⟩ : syracuseStep 279483 = 419225) B419225
theorem B279559 : Blo 275825 279559 := bstep (se 1 (by rfl) ⟨209669, by rfl⟩ : syracuseStep 279559 = 419339) B419339
theorem B279567 : Blo 275825 279567 := bstep (se 1 (by rfl) ⟨209675, by rfl⟩ : syracuseStep 279567 = 419351) B419351
theorem B934955 : Blo 275825 934955 := bstep (se 1 (by rfl) ⟨701216, by rfl⟩ : syracuseStep 934955 = 1402433) B1402433
theorem B574523 : Blo 275825 574523 := bstep (se 1 (by rfl) ⟨430892, by rfl⟩ : syracuseStep 574523 = 861785) B861785
theorem B279611 : Blo 275825 279611 := bstep (se 1 (by rfl) ⟨209708, by rfl⟩ : syracuseStep 279611 = 419417) B419417
theorem B279687 : Blo 275825 279687 := bstep (se 1 (by rfl) ⟨209765, by rfl⟩ : syracuseStep 279687 = 419531) B419531
theorem B279695 : Blo 275825 279695 := bstep (se 1 (by rfl) ⟨209771, by rfl⟩ : syracuseStep 279695 = 419543) B419543
theorem B279739 : Blo 275825 279739 := bstep (se 1 (by rfl) ⟨209804, by rfl⟩ : syracuseStep 279739 = 419609) B419609
theorem B705793 : Blo 275825 705793 := bstep (se 2 (by rfl) ⟨264672, by rfl⟩ : syracuseStep 705793 = 529345) B529345
theorem B312583 : Blo 275825 312583 := bstep (se 1 (by rfl) ⟨234437, by rfl⟩ : syracuseStep 312583 = 468875) B468875
theorem B279815 : Blo 275825 279815 := bstep (se 1 (by rfl) ⟨209861, by rfl⟩ : syracuseStep 279815 = 419723) B419723
theorem B279823 : Blo 275825 279823 := bstep (se 1 (by rfl) ⟨209867, by rfl⟩ : syracuseStep 279823 = 419735) B419735
theorem B1590587 : Blo 275825 1590587 := bstep (se 1 (by rfl) ⟨1192940, by rfl⟩ : syracuseStep 1590587 = 2385881) B2385881
theorem B312763 : Blo 275825 312763 := bstep (se 1 (by rfl) ⟨234572, by rfl⟩ : syracuseStep 312763 = 469145) B469145
theorem B1689281 : Blo 275825 1689281 := bstep (se 2 (by rfl) ⟨633480, by rfl⟩ : syracuseStep 1689281 = 1266961) B1266961
theorem B4474693 : Blo 275825 4474693 := bstep (se 4 (by rfl) ⟨419502, by rfl⟩ : syracuseStep 4474693 = 839005) B839005
theorem B706391 : Blo 275825 706391 := bstep (se 1 (by rfl) ⟨529793, by rfl⟩ : syracuseStep 706391 = 1059587) B1059587
theorem B313231 : Blo 275825 313231 := bstep (se 1 (by rfl) ⟨234923, by rfl⟩ : syracuseStep 313231 = 469847) B469847
theorem B706603 : Blo 275825 706603 := bstep (se 1 (by rfl) ⟨529952, by rfl⟩ : syracuseStep 706603 = 1059905) B1059905
theorem B706745 : Blo 275825 706745 := bstep (se 2 (by rfl) ⟨265029, by rfl⟩ : syracuseStep 706745 = 530059) B530059
theorem B1591589 : Blo 275825 1591589 := bstep (se 4 (by rfl) ⟨149211, by rfl⟩ : syracuseStep 1591589 = 298423) B298423
theorem B936251 : Blo 275825 936251 := bstep (se 1 (by rfl) ⟨702188, by rfl⟩ : syracuseStep 936251 = 1404377) B1404377
theorem B313735 : Blo 275825 313735 := bstep (se 1 (by rfl) ⟨235301, by rfl⟩ : syracuseStep 313735 = 470603) B470603
theorem B3361283 : Blo 275825 3361283 := bstep (se 1 (by rfl) ⟨2520962, by rfl⟩ : syracuseStep 3361283 = 5041925) B5041925
theorem B313915 : Blo 275825 313915 := bstep (se 1 (by rfl) ⟨235436, by rfl⟩ : syracuseStep 313915 = 470873) B470873
theorem B1592045 : Blo 275825 1592045 := bstep (se 3 (by rfl) ⟨298508, by rfl⟩ : syracuseStep 1592045 = 597017) B597017
theorem B2247439 : Blo 275825 2247439 := bstep (se 1 (by rfl) ⟨1685579, by rfl⟩ : syracuseStep 2247439 = 3371159) B3371159
theorem B936737 : Blo 275825 936737 := bstep (se 2 (by rfl) ⟨351276, by rfl⟩ : syracuseStep 936737 = 702553) B702553
theorem B2542387 : Blo 275825 2542387 := bstep (se 1 (by rfl) ⟨1906790, by rfl⟩ : syracuseStep 2542387 = 3813581) B3813581
theorem B1788875 : Blo 275825 1788875 := bstep (se 1 (by rfl) ⟨1341656, by rfl⟩ : syracuseStep 1788875 = 2683313) B2683313
theorem B1330141 : Blo 275825 1330141 := bstep (se 3 (by rfl) ⟨249401, by rfl⟩ : syracuseStep 1330141 = 498803) B498803
theorem B281615 : Blo 275825 281615 := bstep (se 1 (by rfl) ⟨211211, by rfl⟩ : syracuseStep 281615 = 422423) B422423
theorem B314383 : Blo 275825 314383 := bstep (se 1 (by rfl) ⟨235787, by rfl⟩ : syracuseStep 314383 = 471575) B471575
theorem B1428509 : Blo 275825 1428509 := bstep (se 3 (by rfl) ⟨267845, by rfl⟩ : syracuseStep 1428509 = 535691) B535691
theorem B3165317 : Blo 275825 3165317 := bstep (se 4 (by rfl) ⟨296748, by rfl⟩ : syracuseStep 3165317 = 593497) B593497
theorem B707737 : Blo 275825 707737 := bstep (se 2 (by rfl) ⟨265401, by rfl⟩ : syracuseStep 707737 = 530803) B530803
theorem B904463 : Blo 275825 904463 := bstep (se 1 (by rfl) ⟨678347, by rfl⟩ : syracuseStep 904463 = 1356695) B1356695
theorem B707899 : Blo 275825 707899 := bstep (se 1 (by rfl) ⟨530924, by rfl⟩ : syracuseStep 707899 = 1061849) B1061849
theorem B937331 : Blo 275825 937331 := bstep (se 1 (by rfl) ⟨702998, by rfl⟩ : syracuseStep 937331 = 1405997) B1405997
theorem B1592729 : Blo 275825 1592729 := bstep (se 2 (by rfl) ⟨597273, by rfl⟩ : syracuseStep 1592729 = 1194547) B1194547
theorem B708041 : Blo 275825 708041 := bstep (se 2 (by rfl) ⟨265515, by rfl⟩ : syracuseStep 708041 = 531031) B531031
theorem B2543147 : Blo 275825 2543147 := bstep (se 1 (by rfl) ⟨1907360, by rfl⟩ : syracuseStep 2543147 = 3814721) B3814721
theorem B446251 : Blo 275825 446251 := bstep (se 1 (by rfl) ⟨334688, by rfl⟩ : syracuseStep 446251 = 669377) B669377
theorem B413753 : Blo 275825 413753 := bstep (se 2 (by rfl) ⟨155157, by rfl⟩ : syracuseStep 413753 = 310315) B310315
theorem B1200215 : Blo 275825 1200215 := bstep (se 1 (by rfl) ⟨900161, by rfl⟩ : syracuseStep 1200215 = 1800323) B1800323
theorem B413831 : Blo 275825 413831 := bstep (se 1 (by rfl) ⟨310373, by rfl⟩ : syracuseStep 413831 = 620747) B620747
theorem B413867 : Blo 275825 413867 := bstep (se 1 (by rfl) ⟨310400, by rfl⟩ : syracuseStep 413867 = 620801) B620801
theorem B413897 : Blo 275825 413897 := bstep (se 2 (by rfl) ⟨155211, by rfl⟩ : syracuseStep 413897 = 310423) B310423
theorem B7622857 : Blo 275825 7622857 := bstep (se 2 (by rfl) ⟨2858571, by rfl⟩ : syracuseStep 7622857 = 5717143) B5717143
theorem B414011 : Blo 275825 414011 := bstep (se 1 (by rfl) ⟨310508, by rfl⟩ : syracuseStep 414011 = 621017) B621017
theorem B414071 : Blo 275825 414071 := bstep (se 1 (by rfl) ⟨310553, by rfl⟩ : syracuseStep 414071 = 621107) B621107
theorem B414095 : Blo 275825 414095 := bstep (se 1 (by rfl) ⟨310571, by rfl⟩ : syracuseStep 414095 = 621143) B621143
theorem B1331603 : Blo 275825 1331603 := bstep (se 1 (by rfl) ⟨998702, by rfl⟩ : syracuseStep 1331603 = 1997405) B1997405
theorem B414137 : Blo 275825 414137 := bstep (se 2 (by rfl) ⟨155301, by rfl⟩ : syracuseStep 414137 = 310603) B310603
theorem B414215 : Blo 275825 414215 := bstep (se 1 (by rfl) ⟨310661, by rfl⟩ : syracuseStep 414215 = 621323) B621323
theorem B414251 : Blo 275825 414251 := bstep (se 1 (by rfl) ⟨310688, by rfl⟩ : syracuseStep 414251 = 621377) B621377
theorem B414281 : Blo 275825 414281 := bstep (se 2 (by rfl) ⟨155355, by rfl⟩ : syracuseStep 414281 = 310711) B310711
theorem B414395 : Blo 275825 414395 := bstep (se 1 (by rfl) ⟨310796, by rfl⟩ : syracuseStep 414395 = 621593) B621593
theorem B414455 : Blo 275825 414455 := bstep (se 1 (by rfl) ⟨310841, by rfl⟩ : syracuseStep 414455 = 621683) B621683
theorem B414479 : Blo 275825 414479 := bstep (se 1 (by rfl) ⟨310859, by rfl⟩ : syracuseStep 414479 = 621719) B621719
theorem B414521 : Blo 275825 414521 := bstep (se 2 (by rfl) ⟨155445, by rfl⟩ : syracuseStep 414521 = 310891) B310891
theorem B414599 : Blo 275825 414599 := bstep (se 1 (by rfl) ⟨310949, by rfl⟩ : syracuseStep 414599 = 621899) B621899
theorem B906137 : Blo 275825 906137 := bstep (se 2 (by rfl) ⟨339801, by rfl⟩ : syracuseStep 906137 = 679603) B679603
theorem B414635 : Blo 275825 414635 := bstep (se 1 (by rfl) ⟨310976, by rfl⟩ : syracuseStep 414635 = 621953) B621953
theorem B414665 : Blo 275825 414665 := bstep (se 2 (by rfl) ⟨155499, by rfl⟩ : syracuseStep 414665 = 310999) B310999
theorem B2380823 : Blo 275825 2380823 := bstep (se 1 (by rfl) ⟨1785617, by rfl⟩ : syracuseStep 2380823 = 3571235) B3571235
theorem B414779 : Blo 275825 414779 := bstep (se 1 (by rfl) ⟨311084, by rfl⟩ : syracuseStep 414779 = 622169) B622169
theorem B414839 : Blo 275825 414839 := bstep (se 1 (by rfl) ⟨311129, by rfl⟩ : syracuseStep 414839 = 622259) B622259
theorem B414863 : Blo 275825 414863 := bstep (se 1 (by rfl) ⟨311147, by rfl⟩ : syracuseStep 414863 = 622295) B622295
theorem B414905 : Blo 275825 414905 := bstep (se 2 (by rfl) ⟨155589, by rfl⟩ : syracuseStep 414905 = 311179) B311179
theorem B414983 : Blo 275825 414983 := bstep (se 1 (by rfl) ⟨311237, by rfl⟩ : syracuseStep 414983 = 622475) B622475
theorem B415019 : Blo 275825 415019 := bstep (se 1 (by rfl) ⟨311264, by rfl⟩ : syracuseStep 415019 = 622529) B622529
theorem B415049 : Blo 275825 415049 := bstep (se 2 (by rfl) ⟨155643, by rfl⟩ : syracuseStep 415049 = 311287) B311287
theorem B415163 : Blo 275825 415163 := bstep (se 1 (by rfl) ⟨311372, by rfl⟩ : syracuseStep 415163 = 622745) B622745
theorem B349687 : Blo 275825 349687 := bstep (se 1 (by rfl) ⟨262265, by rfl⟩ : syracuseStep 349687 = 524531) B524531
theorem B415223 : Blo 275825 415223 := bstep (se 1 (by rfl) ⟨311417, by rfl⟩ : syracuseStep 415223 = 622835) B622835
theorem B415247 : Blo 275825 415247 := bstep (se 1 (by rfl) ⟨311435, by rfl⟩ : syracuseStep 415247 = 622871) B622871
theorem B415289 : Blo 275825 415289 := bstep (se 2 (by rfl) ⟨155733, by rfl⟩ : syracuseStep 415289 = 311467) B311467
theorem B972407 : Blo 275825 972407 := bstep (se 1 (by rfl) ⟨729305, by rfl⟩ : syracuseStep 972407 = 1458611) B1458611
theorem B415367 : Blo 275825 415367 := bstep (se 1 (by rfl) ⟨311525, by rfl⟩ : syracuseStep 415367 = 623051) B623051
theorem B415403 : Blo 275825 415403 := bstep (se 1 (by rfl) ⟨311552, by rfl⟩ : syracuseStep 415403 = 623105) B623105
theorem B415433 : Blo 275825 415433 := bstep (se 2 (by rfl) ⟨155787, by rfl⟩ : syracuseStep 415433 = 311575) B311575
theorem B48420557 : Blo 275825 48420557 := bstep (se 3 (by rfl) ⟨9078854, by rfl⟩ : syracuseStep 48420557 = 18157709) B18157709
theorem B841487 : Blo 275825 841487 := bstep (se 1 (by rfl) ⟨631115, by rfl⟩ : syracuseStep 841487 = 1262231) B1262231
theorem B350011 : Blo 275825 350011 := bstep (se 1 (by rfl) ⟨262508, by rfl⟩ : syracuseStep 350011 = 525017) B525017
theorem B415547 : Blo 275825 415547 := bstep (se 1 (by rfl) ⟨311660, by rfl⟩ : syracuseStep 415547 = 623321) B623321
theorem B3200843 : Blo 275825 3200843 := bstep (se 1 (by rfl) ⟨2400632, by rfl⟩ : syracuseStep 3200843 = 4801265) B4801265
theorem B415607 : Blo 275825 415607 := bstep (se 1 (by rfl) ⟨311705, by rfl⟩ : syracuseStep 415607 = 623411) B623411
theorem B415631 : Blo 275825 415631 := bstep (se 1 (by rfl) ⟨311723, by rfl⟩ : syracuseStep 415631 = 623447) B623447
theorem B939923 : Blo 275825 939923 := bstep (se 1 (by rfl) ⟨704942, by rfl⟩ : syracuseStep 939923 = 1409885) B1409885
theorem B415673 : Blo 275825 415673 := bstep (se 2 (by rfl) ⟨155877, by rfl⟩ : syracuseStep 415673 = 311755) B311755
theorem B415751 : Blo 275825 415751 := bstep (se 1 (by rfl) ⟨311813, by rfl⟩ : syracuseStep 415751 = 623627) B623627
theorem B415787 : Blo 275825 415787 := bstep (se 1 (by rfl) ⟨311840, by rfl⟩ : syracuseStep 415787 = 623681) B623681
theorem B87447605 : Blo 275825 87447605 := bstep (se 5 (by rfl) ⟨4099106, by rfl⟩ : syracuseStep 87447605 = 8198213) B8198213
theorem B2381885 : Blo 275825 2381885 := bstep (se 3 (by rfl) ⟨446603, by rfl⟩ : syracuseStep 2381885 = 893207) B893207
theorem B415817 : Blo 275825 415817 := bstep (se 2 (by rfl) ⟨155931, by rfl⟩ : syracuseStep 415817 = 311863) B311863
theorem B415931 : Blo 275825 415931 := bstep (se 1 (by rfl) ⟨311948, by rfl⟩ : syracuseStep 415931 = 623897) B623897
theorem B415991 : Blo 275825 415991 := bstep (se 1 (by rfl) ⟨311993, by rfl⟩ : syracuseStep 415991 = 623987) B623987
theorem B416015 : Blo 275825 416015 := bstep (se 1 (by rfl) ⟨312011, by rfl⟩ : syracuseStep 416015 = 624023) B624023
theorem B350507 : Blo 275825 350507 := bstep (se 1 (by rfl) ⟨262880, by rfl⟩ : syracuseStep 350507 = 525761) B525761
theorem B416057 : Blo 275825 416057 := bstep (se 2 (by rfl) ⟨156021, by rfl⟩ : syracuseStep 416057 = 312043) B312043
theorem B842119 : Blo 275825 842119 := bstep (se 1 (by rfl) ⟨631589, by rfl⟩ : syracuseStep 842119 = 1263179) B1263179
theorem B416135 : Blo 275825 416135 := bstep (se 1 (by rfl) ⟨312101, by rfl⟩ : syracuseStep 416135 = 624203) B624203
theorem B1399193 : Blo 275825 1399193 := bstep (se 2 (by rfl) ⟨524697, by rfl⟩ : syracuseStep 1399193 = 1049395) B1049395
theorem B416171 : Blo 275825 416171 := bstep (se 1 (by rfl) ⟨312128, by rfl⟩ : syracuseStep 416171 = 624257) B624257
theorem B416201 : Blo 275825 416201 := bstep (se 2 (by rfl) ⟨156075, by rfl⟩ : syracuseStep 416201 = 312151) B312151
theorem B416315 : Blo 275825 416315 := bstep (se 1 (by rfl) ⟨312236, by rfl⟩ : syracuseStep 416315 = 624473) B624473
theorem B416375 : Blo 275825 416375 := bstep (se 1 (by rfl) ⟨312281, by rfl⟩ : syracuseStep 416375 = 624563) B624563
theorem B416399 : Blo 275825 416399 := bstep (se 1 (by rfl) ⟨312299, by rfl⟩ : syracuseStep 416399 = 624599) B624599
theorem B416441 : Blo 275825 416441 := bstep (se 2 (by rfl) ⟨156165, by rfl⟩ : syracuseStep 416441 = 312331) B312331
theorem B350983 : Blo 275825 350983 := bstep (se 1 (by rfl) ⟨263237, by rfl⟩ : syracuseStep 350983 = 526475) B526475
theorem B416519 : Blo 275825 416519 := bstep (se 1 (by rfl) ⟨312389, by rfl⟩ : syracuseStep 416519 = 624779) B624779
theorem B416555 : Blo 275825 416555 := bstep (se 1 (by rfl) ⟨312416, by rfl⟩ : syracuseStep 416555 = 624833) B624833
theorem B416585 : Blo 275825 416585 := bstep (se 2 (by rfl) ⟨156219, by rfl⟩ : syracuseStep 416585 = 312439) B312439
theorem B416699 : Blo 275825 416699 := bstep (se 1 (by rfl) ⟨312524, by rfl⟩ : syracuseStep 416699 = 625049) B625049
theorem B416759 : Blo 275825 416759 := bstep (se 1 (by rfl) ⟨312569, by rfl⟩ : syracuseStep 416759 = 625139) B625139
theorem B416783 : Blo 275825 416783 := bstep (se 1 (by rfl) ⟨312587, by rfl⟩ : syracuseStep 416783 = 625175) B625175
theorem B416825 : Blo 275825 416825 := bstep (se 2 (by rfl) ⟨156309, by rfl⟩ : syracuseStep 416825 = 312619) B312619
theorem B1334333 : Blo 275825 1334333 := bstep (se 3 (by rfl) ⟨250187, by rfl⟩ : syracuseStep 1334333 = 500375) B500375
theorem B416903 : Blo 275825 416903 := bstep (se 1 (by rfl) ⟨312677, by rfl⟩ : syracuseStep 416903 = 625355) B625355
theorem B842899 : Blo 275825 842899 := bstep (se 1 (by rfl) ⟨632174, by rfl⟩ : syracuseStep 842899 = 1264349) B1264349
theorem B416939 : Blo 275825 416939 := bstep (se 1 (by rfl) ⟨312704, by rfl⟩ : syracuseStep 416939 = 625409) B625409
theorem B416969 : Blo 275825 416969 := bstep (se 2 (by rfl) ⟨156363, by rfl⟩ : syracuseStep 416969 = 312727) B312727
theorem B7625933 : Blo 275825 7625933 := bstep (se 3 (by rfl) ⟨1429862, by rfl⟩ : syracuseStep 7625933 = 2859725) B2859725
theorem B351479 : Blo 275825 351479 := bstep (se 1 (by rfl) ⟨263609, by rfl⟩ : syracuseStep 351479 = 527219) B527219
theorem B711937 : Blo 275825 711937 := bstep (se 2 (by rfl) ⟨266976, by rfl⟩ : syracuseStep 711937 = 533953) B533953
theorem B941327 : Blo 275825 941327 := bstep (se 1 (by rfl) ⟨705995, by rfl⟩ : syracuseStep 941327 = 1411991) B1411991
theorem B417083 : Blo 275825 417083 := bstep (se 1 (by rfl) ⟨312812, by rfl⟩ : syracuseStep 417083 = 625625) B625625
theorem B417143 : Blo 275825 417143 := bstep (se 1 (by rfl) ⟨312857, by rfl⟩ : syracuseStep 417143 = 625715) B625715
theorem B351631 : Blo 275825 351631 := bstep (se 1 (by rfl) ⟨263723, by rfl⟩ : syracuseStep 351631 = 527447) B527447
theorem B417167 : Blo 275825 417167 := bstep (se 1 (by rfl) ⟨312875, by rfl⟩ : syracuseStep 417167 = 625751) B625751
theorem B417209 : Blo 275825 417209 := bstep (se 2 (by rfl) ⟨156453, by rfl⟩ : syracuseStep 417209 = 312907) B312907
theorem B417287 : Blo 275825 417287 := bstep (se 1 (by rfl) ⟨312965, by rfl⟩ : syracuseStep 417287 = 625931) B625931
theorem B941597 : Blo 275825 941597 := bstep (se 3 (by rfl) ⟨176549, by rfl⟩ : syracuseStep 941597 = 353099) B353099
theorem B417323 : Blo 275825 417323 := bstep (se 1 (by rfl) ⟨312992, by rfl⟩ : syracuseStep 417323 = 625985) B625985
theorem B351803 : Blo 275825 351803 := bstep (se 1 (by rfl) ⟨263852, by rfl⟩ : syracuseStep 351803 = 527705) B527705
theorem B417353 : Blo 275825 417353 := bstep (se 2 (by rfl) ⟨156507, by rfl⟩ : syracuseStep 417353 = 313015) B313015
theorem B417467 : Blo 275825 417467 := bstep (se 1 (by rfl) ⟨313100, by rfl⟩ : syracuseStep 417467 = 626201) B626201
theorem B417527 : Blo 275825 417527 := bstep (se 1 (by rfl) ⟨313145, by rfl⟩ : syracuseStep 417527 = 626291) B626291
theorem B417551 : Blo 275825 417551 := bstep (se 1 (by rfl) ⟨313163, by rfl⟩ : syracuseStep 417551 = 626327) B626327
theorem B417593 : Blo 275825 417593 := bstep (se 2 (by rfl) ⟨156597, by rfl⟩ : syracuseStep 417593 = 313195) B313195
theorem B417671 : Blo 275825 417671 := bstep (se 1 (by rfl) ⟨313253, by rfl⟩ : syracuseStep 417671 = 626507) B626507
theorem B417707 : Blo 275825 417707 := bstep (se 1 (by rfl) ⟨313280, by rfl⟩ : syracuseStep 417707 = 626561) B626561
theorem B417737 : Blo 275825 417737 := bstep (se 2 (by rfl) ⟨156651, by rfl⟩ : syracuseStep 417737 = 313303) B313303
theorem B417851 : Blo 275825 417851 := bstep (se 1 (by rfl) ⟨313388, by rfl⟩ : syracuseStep 417851 = 626777) B626777
theorem B417911 : Blo 275825 417911 := bstep (se 1 (by rfl) ⟨313433, by rfl⟩ : syracuseStep 417911 = 626867) B626867
theorem B417935 : Blo 275825 417935 := bstep (se 1 (by rfl) ⟨313451, by rfl⟩ : syracuseStep 417935 = 626903) B626903
theorem B1695917 : Blo 275825 1695917 := bstep (se 3 (by rfl) ⟨317984, by rfl⟩ : syracuseStep 1695917 = 635969) B635969
theorem B417977 : Blo 275825 417977 := bstep (se 2 (by rfl) ⟨156741, by rfl⟩ : syracuseStep 417977 = 313483) B313483
theorem B418055 : Blo 275825 418055 := bstep (se 1 (by rfl) ⟨313541, by rfl⟩ : syracuseStep 418055 = 627083) B627083
theorem B418091 : Blo 275825 418091 := bstep (se 1 (by rfl) ⟨313568, by rfl⟩ : syracuseStep 418091 = 627137) B627137
theorem B418121 : Blo 275825 418121 := bstep (se 2 (by rfl) ⟨156795, by rfl⟩ : syracuseStep 418121 = 313591) B313591
theorem B418235 : Blo 275825 418235 := bstep (se 1 (by rfl) ⟨313676, by rfl⟩ : syracuseStep 418235 = 627353) B627353
theorem B418295 : Blo 275825 418295 := bstep (se 1 (by rfl) ⟨313721, by rfl⟩ : syracuseStep 418295 = 627443) B627443
theorem B352775 : Blo 275825 352775 := bstep (se 1 (by rfl) ⟨264581, by rfl⟩ : syracuseStep 352775 = 529163) B529163
theorem B418319 : Blo 275825 418319 := bstep (se 1 (by rfl) ⟨313739, by rfl⟩ : syracuseStep 418319 = 627479) B627479
theorem B418361 : Blo 275825 418361 := bstep (se 2 (by rfl) ⟨156885, by rfl⟩ : syracuseStep 418361 = 313771) B313771
theorem B418439 : Blo 275825 418439 := bstep (se 1 (by rfl) ⟨313829, by rfl⟩ : syracuseStep 418439 = 627659) B627659
theorem B418475 : Blo 275825 418475 := bstep (se 1 (by rfl) ⟨313856, by rfl⟩ : syracuseStep 418475 = 627713) B627713
theorem B418505 : Blo 275825 418505 := bstep (se 2 (by rfl) ⟨156939, by rfl⟩ : syracuseStep 418505 = 313879) B313879
theorem B418619 : Blo 275825 418619 := bstep (se 1 (by rfl) ⟨313964, by rfl⟩ : syracuseStep 418619 = 627929) B627929
theorem B418679 : Blo 275825 418679 := bstep (se 1 (by rfl) ⟨314009, by rfl⟩ : syracuseStep 418679 = 628019) B628019
theorem B418703 : Blo 275825 418703 := bstep (se 1 (by rfl) ⟨314027, by rfl⟩ : syracuseStep 418703 = 628055) B628055
theorem B943001 : Blo 275825 943001 := bstep (se 2 (by rfl) ⟨353625, by rfl⟩ : syracuseStep 943001 = 707251) B707251
theorem B1401785 : Blo 275825 1401785 := bstep (se 2 (by rfl) ⟨525669, by rfl⟩ : syracuseStep 1401785 = 1051339) B1051339
theorem B418745 : Blo 275825 418745 := bstep (se 2 (by rfl) ⟨157029, by rfl⟩ : syracuseStep 418745 = 314059) B314059
theorem B418823 : Blo 275825 418823 := bstep (se 1 (by rfl) ⟨314117, by rfl⟩ : syracuseStep 418823 = 628235) B628235
theorem B418859 : Blo 275825 418859 := bstep (se 1 (by rfl) ⟨314144, by rfl⟩ : syracuseStep 418859 = 628289) B628289
theorem B418889 : Blo 275825 418889 := bstep (se 2 (by rfl) ⟨157083, by rfl⟩ : syracuseStep 418889 = 314167) B314167
theorem B353423 : Blo 275825 353423 := bstep (se 1 (by rfl) ⟨265067, by rfl⟩ : syracuseStep 353423 = 530135) B530135
theorem B419003 : Blo 275825 419003 := bstep (se 1 (by rfl) ⟨314252, by rfl⟩ : syracuseStep 419003 = 628505) B628505
theorem B1500389 : Blo 275825 1500389 := bstep (se 4 (by rfl) ⟨140661, by rfl⟩ : syracuseStep 1500389 = 281323) B281323
theorem B419063 : Blo 275825 419063 := bstep (se 1 (by rfl) ⟨314297, by rfl⟩ : syracuseStep 419063 = 628595) B628595
theorem B419087 : Blo 275825 419087 := bstep (se 1 (by rfl) ⟨314315, by rfl⟩ : syracuseStep 419087 = 628631) B628631
theorem B419129 : Blo 275825 419129 := bstep (se 2 (by rfl) ⟨157173, by rfl⟩ : syracuseStep 419129 = 314347) B314347
theorem B419207 : Blo 275825 419207 := bstep (se 1 (by rfl) ⟨314405, by rfl⟩ : syracuseStep 419207 = 628811) B628811
theorem B419243 : Blo 275825 419243 := bstep (se 1 (by rfl) ⟨314432, by rfl⟩ : syracuseStep 419243 = 628865) B628865
theorem B419273 : Blo 275825 419273 := bstep (se 2 (by rfl) ⟨157227, by rfl⟩ : syracuseStep 419273 = 314455) B314455
theorem B419387 : Blo 275825 419387 := bstep (se 1 (by rfl) ⟨314540, by rfl⟩ : syracuseStep 419387 = 629081) B629081
theorem B943703 : Blo 275825 943703 := bstep (se 1 (by rfl) ⟨707777, by rfl⟩ : syracuseStep 943703 = 1415555) B1415555
theorem B419447 : Blo 275825 419447 := bstep (se 1 (by rfl) ⟨314585, by rfl⟩ : syracuseStep 419447 = 629171) B629171
theorem B419471 : Blo 275825 419471 := bstep (se 1 (by rfl) ⟨314603, by rfl⟩ : syracuseStep 419471 = 629207) B629207
theorem B419513 : Blo 275825 419513 := bstep (se 2 (by rfl) ⟨157317, by rfl⟩ : syracuseStep 419513 = 314635) B314635
theorem B419591 : Blo 275825 419591 := bstep (se 1 (by rfl) ⟨314693, by rfl⟩ : syracuseStep 419591 = 629387) B629387
theorem B419627 : Blo 275825 419627 := bstep (se 1 (by rfl) ⟨314720, by rfl⟩ : syracuseStep 419627 = 629441) B629441
theorem B13526837 : Blo 275825 13526837 := bstep (se 5 (by rfl) ⟨634070, by rfl⟩ : syracuseStep 13526837 = 1268141) B1268141
theorem B419657 : Blo 275825 419657 := bstep (se 2 (by rfl) ⟨157371, by rfl⟩ : syracuseStep 419657 = 314743) B314743
theorem B944189 : Blo 275825 944189 := bstep (se 3 (by rfl) ⟨177035, by rfl⟩ : syracuseStep 944189 = 354071) B354071
theorem B1599689 : Blo 275825 1599689 := bstep (se 2 (by rfl) ⟨599883, by rfl⟩ : syracuseStep 1599689 = 1199767) B1199767
theorem B1403081 : Blo 275825 1403081 := bstep (se 2 (by rfl) ⟨526155, by rfl⟩ : syracuseStep 1403081 = 1052311) B1052311
theorem B1698251 : Blo 275825 1698251 := bstep (se 1 (by rfl) ⟨1273688, by rfl⟩ : syracuseStep 1698251 = 2547377) B2547377
theorem B1076267 : Blo 275825 1076267 := bstep (se 1 (by rfl) ⟨807200, by rfl⟩ : syracuseStep 1076267 = 1614401) B1614401
theorem B3599597 : Blo 275825 3599597 := bstep (se 3 (by rfl) ⟨674924, by rfl⟩ : syracuseStep 3599597 = 1349849) B1349849
theorem B3174065 : Blo 275825 3174065 := bstep (se 2 (by rfl) ⟨1190274, by rfl⟩ : syracuseStep 3174065 = 2380549) B2380549
theorem B946237 : Blo 275825 946237 := bstep (se 3 (by rfl) ⟨177419, by rfl⟩ : syracuseStep 946237 = 354839) B354839
theorem B1896851 : Blo 275825 1896851 := bstep (se 1 (by rfl) ⟨1422638, by rfl⟩ : syracuseStep 1896851 = 2845277) B2845277
theorem B1340023 : Blo 275825 1340023 := bstep (se 1 (by rfl) ⟨1005017, by rfl⟩ : syracuseStep 1340023 = 2010035) B2010035
theorem B848825 : Blo 275825 848825 := bstep (se 2 (by rfl) ⟨318309, by rfl⟩ : syracuseStep 848825 = 636619) B636619
theorem B423031 : Blo 275825 423031 := bstep (se 1 (by rfl) ⟨317273, by rfl⟩ : syracuseStep 423031 = 634547) B634547
theorem B947603 : Blo 275825 947603 := bstep (se 1 (by rfl) ⟨710702, by rfl⟩ : syracuseStep 947603 = 1421405) B1421405
theorem B4027907 : Blo 275825 4027907 := bstep (se 1 (by rfl) ⟨3020930, by rfl⟩ : syracuseStep 4027907 = 6041861) B6041861
theorem B2094659 : Blo 275825 2094659 := bstep (se 1 (by rfl) ⟨1570994, by rfl⟩ : syracuseStep 2094659 = 3141989) B3141989
theorem B2389571 : Blo 275825 2389571 := bstep (se 1 (by rfl) ⟨1792178, by rfl⟩ : syracuseStep 2389571 = 3584357) B3584357
theorem B1996481 : Blo 275825 1996481 := bstep (se 2 (by rfl) ⟨748680, by rfl⟩ : syracuseStep 1996481 = 1497361) B1497361
theorem B358391 : Blo 275825 358391 := bstep (se 1 (by rfl) ⟨268793, by rfl⟩ : syracuseStep 358391 = 537587) B537587
theorem B620729 : Blo 275825 620729 := bstep (se 2 (by rfl) ⟨232773, by rfl⟩ : syracuseStep 620729 = 465547) B465547
theorem B621071 : Blo 275825 621071 := bstep (se 1 (by rfl) ⟨465803, by rfl⟩ : syracuseStep 621071 = 931607) B931607
theorem B1604119 : Blo 275825 1604119 := bstep (se 1 (by rfl) ⟨1203089, by rfl⟩ : syracuseStep 1604119 = 2406179) B2406179
theorem B621089 : Blo 275825 621089 := bstep (se 2 (by rfl) ⟨232908, by rfl⟩ : syracuseStep 621089 = 465817) B465817
theorem B2652749 : Blo 275825 2652749 := bstep (se 3 (by rfl) ⟨497390, by rfl⟩ : syracuseStep 2652749 = 994781) B994781
theorem B1178383 : Blo 275825 1178383 := bstep (se 1 (by rfl) ⟨883787, by rfl⟩ : syracuseStep 1178383 = 1767575) B1767575
theorem B621431 : Blo 275825 621431 := bstep (se 1 (by rfl) ⟨466073, by rfl⟩ : syracuseStep 621431 = 932147) B932147
theorem B1506251 : Blo 275825 1506251 := bstep (se 1 (by rfl) ⟨1129688, by rfl⟩ : syracuseStep 1506251 = 2259377) B2259377
theorem B2259991 : Blo 275825 2259991 := bstep (se 1 (by rfl) ⟨1694993, by rfl⟩ : syracuseStep 2259991 = 3389987) B3389987
theorem B621611 : Blo 275825 621611 := bstep (se 1 (by rfl) ⟨466208, by rfl⟩ : syracuseStep 621611 = 932417) B932417
theorem B3144905 : Blo 275825 3144905 := bstep (se 2 (by rfl) ⟨1179339, by rfl⟩ : syracuseStep 3144905 = 2358679) B2358679
theorem B1047923 : Blo 275825 1047923 := bstep (se 1 (by rfl) ⟨785942, by rfl⟩ : syracuseStep 1047923 = 1571885) B1571885
theorem B621971 : Blo 275825 621971 := bstep (se 1 (by rfl) ⟨466478, by rfl⟩ : syracuseStep 621971 = 932957) B932957
theorem B622025 : Blo 275825 622025 := bstep (se 2 (by rfl) ⟨233259, by rfl⟩ : syracuseStep 622025 = 466519) B466519
theorem B1572317 : Blo 275825 1572317 := bstep (se 3 (by rfl) ⟨294809, by rfl⟩ : syracuseStep 1572317 = 589619) B589619
theorem B785953 : Blo 275825 785953 := bstep (se 2 (by rfl) ⟨294732, by rfl⟩ : syracuseStep 785953 = 589465) B589465
theorem B1343213 : Blo 275825 1343213 := bstep (se 3 (by rfl) ⟨251852, by rfl⟩ : syracuseStep 1343213 = 503705) B503705
theorem B1408913 : Blo 275825 1408913 := bstep (se 2 (by rfl) ⟨528342, by rfl⟩ : syracuseStep 1408913 = 1056685) B1056685
theorem B1572817 : Blo 275825 1572817 := bstep (se 2 (by rfl) ⟨589806, by rfl⟩ : syracuseStep 1572817 = 1179613) B1179613
theorem B34930763 : Blo 275825 34930763 := bstep (se 1 (by rfl) ⟨26198072, by rfl⟩ : syracuseStep 34930763 = 52396145) B52396145
theorem B622763 : Blo 275825 622763 := bstep (se 1 (by rfl) ⟨467072, by rfl⟩ : syracuseStep 622763 = 934145) B934145
theorem B393655 : Blo 275825 393655 := bstep (se 1 (by rfl) ⟨295241, by rfl⟩ : syracuseStep 393655 = 590483) B590483
theorem B524819 : Blo 275825 524819 := bstep (se 1 (by rfl) ⟨393614, by rfl⟩ : syracuseStep 524819 = 787229) B787229
theorem B1409561 : Blo 275825 1409561 := bstep (se 2 (by rfl) ⟨528585, by rfl⟩ : syracuseStep 1409561 = 1057171) B1057171
theorem B932774453 : Blo 275825 932774453 := bstep (se 5 (by rfl) ⟨43723802, by rfl⟩ : syracuseStep 932774453 = 87447605) B87447605
theorem B6128245 : Blo 275825 6128245 := bstep (se 5 (by rfl) ⟨287261, by rfl⟩ : syracuseStep 6128245 = 574523) B574523
theorem B524971 : Blo 275825 524971 := bstep (se 1 (by rfl) ⟨393728, by rfl⟩ : syracuseStep 524971 = 787457) B787457
theorem B623303 : Blo 275825 623303 := bstep (se 1 (by rfl) ⟨467477, by rfl⟩ : syracuseStep 623303 = 934955) B934955
theorem B525199 : Blo 275825 525199 := bstep (se 1 (by rfl) ⟨393899, by rfl⟩ : syracuseStep 525199 = 787799) B787799
theorem B525275 : Blo 275825 525275 := bstep (se 1 (by rfl) ⟨393956, by rfl⟩ : syracuseStep 525275 = 787913) B787913
theorem B5309489 : Blo 275825 5309489 := bstep (se 2 (by rfl) ⟨1991058, by rfl⟩ : syracuseStep 5309489 = 3982117) B3982117
theorem B1049867 : Blo 275825 1049867 := bstep (se 1 (by rfl) ⟨787400, by rfl⟩ : syracuseStep 1049867 = 1574801) B1574801
theorem B2098547 : Blo 275825 2098547 := bstep (se 1 (by rfl) ⟨1573910, by rfl⟩ : syracuseStep 2098547 = 3147821) B3147821
theorem B886145 : Blo 275825 886145 := bstep (se 2 (by rfl) ⟨332304, by rfl⟩ : syracuseStep 886145 = 664609) B664609
theorem B624167 : Blo 275825 624167 := bstep (se 1 (by rfl) ⟨468125, by rfl⟩ : syracuseStep 624167 = 936251) B936251
theorem B395113 : Blo 275825 395113 := bstep (se 2 (by rfl) ⟨148167, by rfl⟩ : syracuseStep 395113 = 296335) B296335
theorem B624491 : Blo 275825 624491 := bstep (se 1 (by rfl) ⟨468368, by rfl⟩ : syracuseStep 624491 = 936737) B936737
theorem B624545 : Blo 275825 624545 := bstep (se 2 (by rfl) ⟨234204, by rfl⟩ : syracuseStep 624545 = 468409) B468409
theorem B3540995 : Blo 275825 3540995 := bstep (se 1 (by rfl) ⟨2655746, by rfl⟩ : syracuseStep 3540995 = 5311493) B5311493
theorem B952339 : Blo 275825 952339 := bstep (se 1 (by rfl) ⟨714254, by rfl⟩ : syracuseStep 952339 = 1428509) B1428509
theorem B4491301 : Blo 275825 4491301 := bstep (se 4 (by rfl) ⟨421059, by rfl⟩ : syracuseStep 4491301 = 842119) B842119
theorem B624887 : Blo 275825 624887 := bstep (se 1 (by rfl) ⟨468665, by rfl⟩ : syracuseStep 624887 = 937331) B937331
theorem B5966257 : Blo 275825 5966257 := bstep (se 2 (by rfl) ⟨2237346, by rfl⟩ : syracuseStep 5966257 = 4474693) B4474693
theorem B8129009 : Blo 275825 8129009 := bstep (se 2 (by rfl) ⟨3048378, by rfl⟩ : syracuseStep 8129009 = 6096757) B6096757
theorem B1051325 : Blo 275825 1051325 := bstep (se 3 (by rfl) ⟨197123, by rfl⟩ : syracuseStep 1051325 = 394247) B394247
theorem B625481 : Blo 275825 625481 := bstep (se 2 (by rfl) ⟨234555, by rfl⟩ : syracuseStep 625481 = 469111) B469111
theorem B4295501 : Blo 275825 4295501 := bstep (se 3 (by rfl) ⟨805406, by rfl⟩ : syracuseStep 4295501 = 1610813) B1610813
theorem B887735 : Blo 275825 887735 := bstep (se 1 (by rfl) ⟨665801, by rfl⟩ : syracuseStep 887735 = 1331603) B1331603
theorem B1510595 : Blo 275825 1510595 := bstep (se 1 (by rfl) ⟨1132946, by rfl⟩ : syracuseStep 1510595 = 2265893) B2265893
theorem B1412477 : Blo 275825 1412477 := bstep (se 3 (by rfl) ⟨264839, by rfl⟩ : syracuseStep 1412477 = 529679) B529679
theorem B626273 : Blo 275825 626273 := bstep (se 2 (by rfl) ⟨234852, by rfl⟩ : syracuseStep 626273 = 469705) B469705
theorem B32280371 : Blo 275825 32280371 := bstep (se 1 (by rfl) ⟨24210278, by rfl⟩ : syracuseStep 32280371 = 48420557) B48420557
theorem B397163 : Blo 275825 397163 := bstep (se 1 (by rfl) ⟨297872, by rfl⟩ : syracuseStep 397163 = 595745) B595745
theorem B593839 : Blo 275825 593839 := bstep (se 1 (by rfl) ⟨445379, by rfl⟩ : syracuseStep 593839 = 890759) B890759
theorem B626615 : Blo 275825 626615 := bstep (se 1 (by rfl) ⟨469961, by rfl⟩ : syracuseStep 626615 = 939923) B939923
theorem B1773521 : Blo 275825 1773521 := bstep (se 2 (by rfl) ⟨665070, by rfl⟩ : syracuseStep 1773521 = 1330141) B1330141
theorem B1773575 : Blo 275825 1773575 := bstep (se 1 (by rfl) ⟨1330181, by rfl⟩ : syracuseStep 1773575 = 2660363) B2660363
theorem B1053071 : Blo 275825 1053071 := bstep (se 1 (by rfl) ⟨789803, by rfl⟩ : syracuseStep 1053071 = 1579607) B1579607
theorem B528859 : Blo 275825 528859 := bstep (se 1 (by rfl) ⟨396644, by rfl⟩ : syracuseStep 528859 = 793289) B793289
theorem B528905 : Blo 275825 528905 := bstep (se 2 (by rfl) ⟨198339, by rfl⟩ : syracuseStep 528905 = 396679) B396679
theorem B627209 : Blo 275825 627209 := bstep (se 2 (by rfl) ⟨235203, by rfl⟩ : syracuseStep 627209 = 470407) B470407
theorem B889555 : Blo 275825 889555 := bstep (se 1 (by rfl) ⟨667166, by rfl⟩ : syracuseStep 889555 = 1334333) B1334333
theorem B5083955 : Blo 275825 5083955 := bstep (se 1 (by rfl) ⟨3812966, by rfl⟩ : syracuseStep 5083955 = 7625933) B7625933
theorem B529247 : Blo 275825 529247 := bstep (se 1 (by rfl) ⟨396935, by rfl⟩ : syracuseStep 529247 = 793871) B793871
theorem B627551 : Blo 275825 627551 := bstep (se 1 (by rfl) ⟨470663, by rfl⟩ : syracuseStep 627551 = 941327) B941327
theorem B19928065 : Blo 275825 19928065 := bstep (se 2 (by rfl) ⟨7473024, by rfl⟩ : syracuseStep 19928065 = 14946049) B14946049
theorem B627731 : Blo 275825 627731 := bstep (se 1 (by rfl) ⟨470798, by rfl⟩ : syracuseStep 627731 = 941597) B941597
theorem B595001 : Blo 275825 595001 := bstep (se 2 (by rfl) ⟨223125, by rfl⟩ : syracuseStep 595001 = 446251) B446251
theorem B955709 : Blo 275825 955709 := bstep (se 3 (by rfl) ⟨179195, by rfl⟩ : syracuseStep 955709 = 358391) B358391
theorem B628073 : Blo 275825 628073 := bstep (se 2 (by rfl) ⟨235527, by rfl⟩ : syracuseStep 628073 = 471055) B471055
theorem B595343 : Blo 275825 595343 := bstep (se 1 (by rfl) ⟨446507, by rfl⟩ : syracuseStep 595343 = 893015) B893015
theorem B2299355 : Blo 275825 2299355 := bstep (se 1 (by rfl) ⟨1724516, by rfl⟩ : syracuseStep 2299355 = 3449033) B3449033
theorem B1054241 : Blo 275825 1054241 := bstep (se 2 (by rfl) ⟨395340, by rfl⟩ : syracuseStep 1054241 = 790681) B790681
theorem B10163809 : Blo 275825 10163809 := bstep (se 2 (by rfl) ⟨3811428, by rfl⟩ : syracuseStep 10163809 = 7622857) B7622857
theorem B1054559 : Blo 275825 1054559 := bstep (se 1 (by rfl) ⟨790919, by rfl⟩ : syracuseStep 1054559 = 1581839) B1581839
theorem B530363 : Blo 275825 530363 := bstep (se 1 (by rfl) ⟨397772, by rfl⟩ : syracuseStep 530363 = 795545) B795545
theorem B628667 : Blo 275825 628667 := bstep (se 1 (by rfl) ⟨471500, by rfl⟩ : syracuseStep 628667 = 943001) B943001
theorem B1185799 : Blo 275825 1185799 := bstep (se 1 (by rfl) ⟨889349, by rfl⟩ : syracuseStep 1185799 = 1778699) B1778699
theorem B1054727 : Blo 275825 1054727 := bstep (se 1 (by rfl) ⟨791045, by rfl⟩ : syracuseStep 1054727 = 1582091) B1582091
theorem B628793 : Blo 275825 628793 := bstep (se 2 (by rfl) ⟨235797, by rfl⟩ : syracuseStep 628793 = 471595) B471595
theorem B1120655 : Blo 275825 1120655 := bstep (se 1 (by rfl) ⟨840491, by rfl⟩ : syracuseStep 1120655 = 1680983) B1680983
theorem B629135 : Blo 275825 629135 := bstep (se 1 (by rfl) ⟨471851, by rfl⟩ : syracuseStep 629135 = 943703) B943703
theorem B530849 : Blo 275825 530849 := bstep (se 2 (by rfl) ⟨199068, by rfl⟩ : syracuseStep 530849 = 398137) B398137
theorem B1055213 : Blo 275825 1055213 := bstep (se 3 (by rfl) ⟨197852, by rfl⟩ : syracuseStep 1055213 = 395705) B395705
theorem B4528669 : Blo 275825 4528669 := bstep (se 3 (by rfl) ⟨849125, by rfl⟩ : syracuseStep 4528669 = 1698251) B1698251
theorem B891425 : Blo 275825 891425 := bstep (se 2 (by rfl) ⟨334284, by rfl⟩ : syracuseStep 891425 = 668569) B668569
theorem B9017891 : Blo 275825 9017891 := bstep (se 1 (by rfl) ⟨6763418, by rfl⟩ : syracuseStep 9017891 = 13526837) B13526837
theorem B334415 : Blo 275825 334415 := bstep (se 1 (by rfl) ⟨250811, by rfl⟩ : syracuseStep 334415 = 501623) B501623
theorem B629459 : Blo 275825 629459 := bstep (se 1 (by rfl) ⟨472094, by rfl⟩ : syracuseStep 629459 = 944189) B944189
theorem B465655 : Blo 275825 465655 := bstep (se 1 (by rfl) ⟨349241, by rfl⟩ : syracuseStep 465655 = 698483) B698483
theorem B531191 : Blo 275825 531191 := bstep (se 1 (by rfl) ⟨398393, by rfl⟩ : syracuseStep 531191 = 796787) B796787
theorem B1055531 : Blo 275825 1055531 := bstep (se 1 (by rfl) ⟨791648, by rfl⟩ : syracuseStep 1055531 = 1583297) B1583297
theorem B564041 : Blo 275825 564041 := bstep (se 2 (by rfl) ⟨211515, by rfl⟩ : syracuseStep 564041 = 423031) B423031
theorem B465851 : Blo 275825 465851 := bstep (se 1 (by rfl) ⟨349388, by rfl⟩ : syracuseStep 465851 = 698777) B698777
theorem B465959 : Blo 275825 465959 := bstep (se 1 (by rfl) ⟨349469, by rfl⟩ : syracuseStep 465959 = 698939) B698939
theorem B466249 : Blo 275825 466249 := bstep (se 2 (by rfl) ⟨174843, by rfl⟩ : syracuseStep 466249 = 349687) B349687
theorem B4300121 : Blo 275825 4300121 := bstep (se 2 (by rfl) ⟨1612545, by rfl⟩ : syracuseStep 4300121 = 3225091) B3225091
theorem B466283 : Blo 275825 466283 := bstep (se 1 (by rfl) ⟨349712, by rfl⟩ : syracuseStep 466283 = 699425) B699425
theorem B466681 : Blo 275825 466681 := bstep (se 2 (by rfl) ⟨175005, by rfl⟩ : syracuseStep 466681 = 350011) B350011
theorem B466951 : Blo 275825 466951 := bstep (se 1 (by rfl) ⟨350213, by rfl⟩ : syracuseStep 466951 = 700427) B700427
theorem B2105351 : Blo 275825 2105351 := bstep (se 1 (by rfl) ⟨1579013, by rfl⟩ : syracuseStep 2105351 = 3158027) B3158027
theorem B335995 : Blo 275825 335995 := bstep (se 1 (by rfl) ⟨251996, by rfl⟩ : syracuseStep 335995 = 503993) B503993
theorem B631145 : Blo 275825 631145 := bstep (se 2 (by rfl) ⟨236679, by rfl⟩ : syracuseStep 631145 = 473359) B473359
theorem B467383 : Blo 275825 467383 := bstep (se 1 (by rfl) ⟨350537, by rfl⟩ : syracuseStep 467383 = 701075) B701075
theorem B2105837 : Blo 275825 2105837 := bstep (se 3 (by rfl) ⟨394844, by rfl⟩ : syracuseStep 2105837 = 789689) B789689
theorem B1188361 : Blo 275825 1188361 := bstep (se 2 (by rfl) ⟨445635, by rfl⟩ : syracuseStep 1188361 = 891271) B891271
theorem B25960981 : Blo 275825 25960981 := bstep (se 6 (by rfl) ⟨608460, by rfl⟩ : syracuseStep 25960981 = 1216921) B1216921
theorem B467579 : Blo 275825 467579 := bstep (se 1 (by rfl) ⟨350684, by rfl⟩ : syracuseStep 467579 = 701369) B701369
theorem B565883 : Blo 275825 565883 := bstep (se 1 (by rfl) ⟨424412, by rfl⟩ : syracuseStep 565883 = 848825) B848825
theorem B893629 : Blo 275825 893629 := bstep (se 3 (by rfl) ⟨167555, by rfl⟩ : syracuseStep 893629 = 335111) B335111
theorem B2138825 : Blo 275825 2138825 := bstep (se 2 (by rfl) ⟨802059, by rfl⟩ : syracuseStep 2138825 = 1604119) B1604119
theorem B1057643 : Blo 275825 1057643 := bstep (se 1 (by rfl) ⟨793232, by rfl⟩ : syracuseStep 1057643 = 1586465) B1586465
theorem B631735 : Blo 275825 631735 := bstep (se 1 (by rfl) ⟨473801, by rfl⟩ : syracuseStep 631735 = 947603) B947603
theorem B467977 : Blo 275825 467977 := bstep (se 2 (by rfl) ⟨175491, by rfl⟩ : syracuseStep 467977 = 350983) B350983
theorem B2237483 : Blo 275825 2237483 := bstep (se 1 (by rfl) ⟨1678112, by rfl⟩ : syracuseStep 2237483 = 3356225) B3356225
theorem B468139 : Blo 275825 468139 := bstep (se 1 (by rfl) ⟨351104, by rfl⟩ : syracuseStep 468139 = 702209) B702209
theorem B468443 : Blo 275825 468443 := bstep (se 1 (by rfl) ⟨351332, by rfl⟩ : syracuseStep 468443 = 702665) B702665
theorem B1123865 : Blo 275825 1123865 := bstep (se 2 (by rfl) ⟨421449, by rfl⟩ : syracuseStep 1123865 = 842899) B842899
theorem B468679 : Blo 275825 468679 := bstep (se 1 (by rfl) ⟨351509, by rfl⟩ : syracuseStep 468679 = 703019) B703019
theorem B1582841 : Blo 275825 1582841 := bstep (se 2 (by rfl) ⟨593565, by rfl⟩ : syracuseStep 1582841 = 1187131) B1187131
theorem B468841 : Blo 275825 468841 := bstep (se 2 (by rfl) ⟨175815, by rfl⟩ : syracuseStep 468841 = 351631) B351631
theorem B403465 : Blo 275825 403465 := bstep (se 2 (by rfl) ⟨151299, by rfl⟩ : syracuseStep 403465 = 302599) B302599
theorem B796729 : Blo 275825 796729 := bstep (se 2 (by rfl) ⟨298773, by rfl⟩ : syracuseStep 796729 = 597547) B597547
theorem B698615 : Blo 275825 698615 := bstep (se 1 (by rfl) ⟨523961, by rfl⟩ : syracuseStep 698615 = 1047923) B1047923
theorem B2107781 : Blo 275825 2107781 := bstep (se 4 (by rfl) ⟨197604, by rfl⟩ : syracuseStep 2107781 = 395209) B395209
theorem B469435 : Blo 275825 469435 := bstep (se 1 (by rfl) ⟨352076, by rfl⟩ : syracuseStep 469435 = 704153) B704153
theorem B895475 : Blo 275825 895475 := bstep (se 1 (by rfl) ⟨671606, by rfl⟩ : syracuseStep 895475 = 1343213) B1343213
theorem B3811873 : Blo 275825 3811873 := bstep (se 2 (by rfl) ⟨1429452, by rfl⟩ : syracuseStep 3811873 = 2858905) B2858905
theorem B469543 : Blo 275825 469543 := bstep (se 1 (by rfl) ⟨352157, by rfl⟩ : syracuseStep 469543 = 704315) B704315
theorem B2108267 : Blo 275825 2108267 := bstep (se 1 (by rfl) ⟨1581200, by rfl⟩ : syracuseStep 2108267 = 3162401) B3162401
theorem B469867 : Blo 275825 469867 := bstep (se 1 (by rfl) ⟨352400, by rfl⟩ : syracuseStep 469867 = 704801) B704801
theorem B9612215 : Blo 275825 9612215 := bstep (se 1 (by rfl) ⟨7209161, by rfl⟩ : syracuseStep 9612215 = 14418323) B14418323
theorem B1584299 : Blo 275825 1584299 := bstep (se 1 (by rfl) ⟨1188224, by rfl⟩ : syracuseStep 1584299 = 2376449) B2376449
theorem B1060087 : Blo 275825 1060087 := bstep (se 1 (by rfl) ⟨795065, by rfl⟩ : syracuseStep 1060087 = 1590131) B1590131
theorem B4304119 : Blo 275825 4304119 := bstep (se 1 (by rfl) ⟨3228089, by rfl⟩ : syracuseStep 4304119 = 6456179) B6456179
theorem B2665817 : Blo 275825 2665817 := bstep (se 2 (by rfl) ⟨999681, by rfl⟩ : syracuseStep 2665817 = 1999363) B1999363
theorem B1060361 : Blo 275825 1060361 := bstep (se 2 (by rfl) ⟨397635, by rfl⟩ : syracuseStep 1060361 = 795271) B795271
theorem B1060391 : Blo 275825 1060391 := bstep (se 1 (by rfl) ⟨795293, by rfl⟩ : syracuseStep 1060391 = 1590587) B1590587
theorem B700103 : Blo 275825 700103 := bstep (se 1 (by rfl) ⟨525077, by rfl⟩ : syracuseStep 700103 = 1050155) B1050155
theorem B1126187 : Blo 275825 1126187 := bstep (se 1 (by rfl) ⟨844640, by rfl⟩ : syracuseStep 1126187 = 1689281) B1689281
theorem B470927 : Blo 275825 470927 := bstep (se 1 (by rfl) ⟨353195, by rfl⟩ : syracuseStep 470927 = 706391) B706391
theorem B1421243 : Blo 275825 1421243 := bstep (se 1 (by rfl) ⟨1065932, by rfl⟩ : syracuseStep 1421243 = 2131865) B2131865
theorem B471163 : Blo 275825 471163 := bstep (se 1 (by rfl) ⟨353372, by rfl⟩ : syracuseStep 471163 = 706745) B706745
theorem B1061059 : Blo 275825 1061059 := bstep (se 1 (by rfl) ⟨795794, by rfl⟩ : syracuseStep 1061059 = 1591589) B1591589
theorem B372935 : Blo 275825 372935 := bstep (se 1 (by rfl) ⟨279701, by rfl⟩ : syracuseStep 372935 = 559403) B559403
theorem B2240855 : Blo 275825 2240855 := bstep (se 1 (by rfl) ⟨1680641, by rfl⟩ : syracuseStep 2240855 = 3361283) B3361283
theorem B799105 : Blo 275825 799105 := bstep (se 2 (by rfl) ⟨299664, by rfl⟩ : syracuseStep 799105 = 599329) B599329
theorem B1061363 : Blo 275825 1061363 := bstep (se 1 (by rfl) ⟨796022, by rfl⟩ : syracuseStep 1061363 = 1592045) B1592045
theorem B1192583 : Blo 275825 1192583 := bstep (se 1 (by rfl) ⟨894437, by rfl⟩ : syracuseStep 1192583 = 1788875) B1788875
theorem B2110211 : Blo 275825 2110211 := bstep (se 1 (by rfl) ⟨1582658, by rfl⟩ : syracuseStep 2110211 = 3165317) B3165317
theorem B897821 : Blo 275825 897821 := bstep (se 3 (by rfl) ⟨168341, by rfl⟩ : syracuseStep 897821 = 336683) B336683
theorem B701257 : Blo 275825 701257 := bstep (se 2 (by rfl) ⟨262971, by rfl⟩ : syracuseStep 701257 = 525943) B525943
theorem B602975 : Blo 275825 602975 := bstep (se 1 (by rfl) ⟨452231, by rfl⟩ : syracuseStep 602975 = 904463) B904463
theorem B1061819 : Blo 275825 1061819 := bstep (se 1 (by rfl) ⟨796364, by rfl⟩ : syracuseStep 1061819 = 1592729) B1592729
theorem B472027 : Blo 275825 472027 := bstep (se 1 (by rfl) ⟨354020, by rfl⟩ : syracuseStep 472027 = 708041) B708041
theorem B3650831 : Blo 275825 3650831 := bstep (se 1 (by rfl) ⟨2738123, by rfl⟩ : syracuseStep 3650831 = 5476247) B5476247
theorem B275835 : Blo 275825 275835 := bstep (se 1 (by rfl) ⟨206876, by rfl⟩ : syracuseStep 275835 = 413753) B413753
theorem B275887 : Blo 275825 275887 := bstep (se 1 (by rfl) ⟨206915, by rfl⟩ : syracuseStep 275887 = 413831) B413831
theorem B275911 : Blo 275825 275911 := bstep (se 1 (by rfl) ⟨206933, by rfl⟩ : syracuseStep 275911 = 413867) B413867
theorem B275931 : Blo 275825 275931 := bstep (se 1 (by rfl) ⟨206948, by rfl⟩ : syracuseStep 275931 = 413897) B413897
theorem B931337 : Blo 275825 931337 := bstep (se 2 (by rfl) ⟨349251, by rfl⟩ : syracuseStep 931337 = 698503) B698503
theorem B276007 : Blo 275825 276007 := bstep (se 1 (by rfl) ⟨207005, by rfl⟩ : syracuseStep 276007 = 414011) B414011
theorem B276047 : Blo 275825 276047 := bstep (se 1 (by rfl) ⟨207035, by rfl⟩ : syracuseStep 276047 = 414071) B414071
theorem B276063 : Blo 275825 276063 := bstep (se 1 (by rfl) ⟨207047, by rfl⟩ : syracuseStep 276063 = 414095) B414095
theorem B276091 : Blo 275825 276091 := bstep (se 1 (by rfl) ⟨207068, by rfl⟩ : syracuseStep 276091 = 414137) B414137
theorem B276143 : Blo 275825 276143 := bstep (se 1 (by rfl) ⟨207107, by rfl⟩ : syracuseStep 276143 = 414215) B414215
theorem B276167 : Blo 275825 276167 := bstep (se 1 (by rfl) ⟨207125, by rfl⟩ : syracuseStep 276167 = 414251) B414251
theorem B4503239 : Blo 275825 4503239 := bstep (se 1 (by rfl) ⟨3377429, by rfl⟩ : syracuseStep 4503239 = 6754859) B6754859
theorem B276187 : Blo 275825 276187 := bstep (se 1 (by rfl) ⟨207140, by rfl⟩ : syracuseStep 276187 = 414281) B414281
theorem B276263 : Blo 275825 276263 := bstep (se 1 (by rfl) ⟨207197, by rfl⟩ : syracuseStep 276263 = 414395) B414395
theorem B276303 : Blo 275825 276303 := bstep (se 1 (by rfl) ⟨207227, by rfl⟩ : syracuseStep 276303 = 414455) B414455
theorem B276319 : Blo 275825 276319 := bstep (se 1 (by rfl) ⟨207239, by rfl⟩ : syracuseStep 276319 = 414479) B414479
theorem B276347 : Blo 275825 276347 := bstep (se 1 (by rfl) ⟨207260, by rfl⟩ : syracuseStep 276347 = 414521) B414521
theorem B276399 : Blo 275825 276399 := bstep (se 1 (by rfl) ⟨207299, by rfl⟩ : syracuseStep 276399 = 414599) B414599
theorem B702391 : Blo 275825 702391 := bstep (se 1 (by rfl) ⟨526793, by rfl⟩ : syracuseStep 702391 = 1053587) B1053587
theorem B604091 : Blo 275825 604091 := bstep (se 1 (by rfl) ⟨453068, by rfl⟩ : syracuseStep 604091 = 906137) B906137
theorem B276423 : Blo 275825 276423 := bstep (se 1 (by rfl) ⟨207317, by rfl⟩ : syracuseStep 276423 = 414635) B414635
theorem B276443 : Blo 275825 276443 := bstep (se 1 (by rfl) ⟨207332, by rfl⟩ : syracuseStep 276443 = 414665) B414665
theorem B1587215 : Blo 275825 1587215 := bstep (se 1 (by rfl) ⟨1190411, by rfl⟩ : syracuseStep 1587215 = 2380823) B2380823
theorem B276519 : Blo 275825 276519 := bstep (se 1 (by rfl) ⟨207389, by rfl⟩ : syracuseStep 276519 = 414779) B414779
theorem B276559 : Blo 275825 276559 := bstep (se 1 (by rfl) ⟨207419, by rfl⟩ : syracuseStep 276559 = 414839) B414839
theorem B276575 : Blo 275825 276575 := bstep (se 1 (by rfl) ⟨207431, by rfl⟩ : syracuseStep 276575 = 414863) B414863
theorem B276603 : Blo 275825 276603 := bstep (se 1 (by rfl) ⟨207452, by rfl⟩ : syracuseStep 276603 = 414905) B414905
theorem B276655 : Blo 275825 276655 := bstep (se 1 (by rfl) ⟨207491, by rfl⟩ : syracuseStep 276655 = 414983) B414983
theorem B276679 : Blo 275825 276679 := bstep (se 1 (by rfl) ⟨207509, by rfl⟩ : syracuseStep 276679 = 415019) B415019
theorem B276699 : Blo 275825 276699 := bstep (se 1 (by rfl) ⟨207524, by rfl⟩ : syracuseStep 276699 = 415049) B415049
theorem B276775 : Blo 275825 276775 := bstep (se 1 (by rfl) ⟨207581, by rfl⟩ : syracuseStep 276775 = 415163) B415163
theorem B276815 : Blo 275825 276815 := bstep (se 1 (by rfl) ⟨207611, by rfl⟩ : syracuseStep 276815 = 415223) B415223
theorem B276831 : Blo 275825 276831 := bstep (se 1 (by rfl) ⟨207623, by rfl⟩ : syracuseStep 276831 = 415247) B415247
theorem B932201 : Blo 275825 932201 := bstep (se 2 (by rfl) ⟨349575, by rfl⟩ : syracuseStep 932201 = 699151) B699151
theorem B2996585 : Blo 275825 2996585 := bstep (se 2 (by rfl) ⟨1123719, by rfl⟩ : syracuseStep 2996585 = 2247439) B2247439
theorem B276859 : Blo 275825 276859 := bstep (se 1 (by rfl) ⟨207644, by rfl⟩ : syracuseStep 276859 = 415289) B415289
theorem B3389849 : Blo 275825 3389849 := bstep (se 2 (by rfl) ⟨1271193, by rfl⟩ : syracuseStep 3389849 = 2542387) B2542387
theorem B276911 : Blo 275825 276911 := bstep (se 1 (by rfl) ⟨207683, by rfl⟩ : syracuseStep 276911 = 415367) B415367
theorem B571835 : Blo 275825 571835 := bstep (se 1 (by rfl) ⟨428876, by rfl⟩ : syracuseStep 571835 = 857753) B857753
theorem B276935 : Blo 275825 276935 := bstep (se 1 (by rfl) ⟨207701, by rfl⟩ : syracuseStep 276935 = 415403) B415403
theorem B276955 : Blo 275825 276955 := bstep (se 1 (by rfl) ⟨207716, by rfl⟩ : syracuseStep 276955 = 415433) B415433
theorem B277031 : Blo 275825 277031 := bstep (se 1 (by rfl) ⟨207773, by rfl⟩ : syracuseStep 277031 = 415547) B415547
theorem B277071 : Blo 275825 277071 := bstep (se 1 (by rfl) ⟨207803, by rfl⟩ : syracuseStep 277071 = 415607) B415607
theorem B277087 : Blo 275825 277087 := bstep (se 1 (by rfl) ⟨207815, by rfl⟩ : syracuseStep 277087 = 415631) B415631
theorem B277115 : Blo 275825 277115 := bstep (se 1 (by rfl) ⟨207836, by rfl⟩ : syracuseStep 277115 = 415673) B415673
theorem B277167 : Blo 275825 277167 := bstep (se 1 (by rfl) ⟨207875, by rfl⟩ : syracuseStep 277167 = 415751) B415751
theorem B277191 : Blo 275825 277191 := bstep (se 1 (by rfl) ⟨207893, by rfl⟩ : syracuseStep 277191 = 415787) B415787
theorem B1587923 : Blo 275825 1587923 := bstep (se 1 (by rfl) ⟨1190942, by rfl⟩ : syracuseStep 1587923 = 2381885) B2381885
theorem B277211 : Blo 275825 277211 := bstep (se 1 (by rfl) ⟨207908, by rfl⟩ : syracuseStep 277211 = 415817) B415817
theorem B277287 : Blo 275825 277287 := bstep (se 1 (by rfl) ⟨207965, by rfl⟩ : syracuseStep 277287 = 415931) B415931
theorem B277327 : Blo 275825 277327 := bstep (se 1 (by rfl) ⟨207995, by rfl⟩ : syracuseStep 277327 = 415991) B415991
theorem B277343 : Blo 275825 277343 := bstep (se 1 (by rfl) ⟨208007, by rfl⟩ : syracuseStep 277343 = 416015) B416015
theorem B375659 : Blo 275825 375659 := bstep (se 1 (by rfl) ⟨281744, by rfl⟩ : syracuseStep 375659 = 563489) B563489
theorem B277371 : Blo 275825 277371 := bstep (se 1 (by rfl) ⟨208028, by rfl⟩ : syracuseStep 277371 = 416057) B416057
theorem B277423 : Blo 275825 277423 := bstep (se 1 (by rfl) ⟨208067, by rfl⟩ : syracuseStep 277423 = 416135) B416135
theorem B932795 : Blo 275825 932795 := bstep (se 1 (by rfl) ⟨699596, by rfl⟩ : syracuseStep 932795 = 1399193) B1399193
theorem B277447 : Blo 275825 277447 := bstep (se 1 (by rfl) ⟨208085, by rfl⟩ : syracuseStep 277447 = 416171) B416171
theorem B277467 : Blo 275825 277467 := bstep (se 1 (by rfl) ⟨208100, by rfl⟩ : syracuseStep 277467 = 416201) B416201
theorem B1031183 : Blo 275825 1031183 := bstep (se 1 (by rfl) ⟨773387, by rfl⟩ : syracuseStep 1031183 = 1546775) B1546775
theorem B277543 : Blo 275825 277543 := bstep (se 1 (by rfl) ⟨208157, by rfl⟩ : syracuseStep 277543 = 416315) B416315
theorem B375887 : Blo 275825 375887 := bstep (se 1 (by rfl) ⟨281915, by rfl⟩ : syracuseStep 375887 = 563831) B563831
theorem B310351 : Blo 275825 310351 := bstep (se 1 (by rfl) ⟨232763, by rfl⟩ : syracuseStep 310351 = 465527) B465527
theorem B277583 : Blo 275825 277583 := bstep (se 1 (by rfl) ⟨208187, by rfl⟩ : syracuseStep 277583 = 416375) B416375
theorem B277599 : Blo 275825 277599 := bstep (se 1 (by rfl) ⟨208199, by rfl⟩ : syracuseStep 277599 = 416399) B416399
theorem B277627 : Blo 275825 277627 := bstep (se 1 (by rfl) ⟨208220, by rfl⟩ : syracuseStep 277627 = 416441) B416441
theorem B277679 : Blo 275825 277679 := bstep (se 1 (by rfl) ⟨208259, by rfl⟩ : syracuseStep 277679 = 416519) B416519
theorem B277703 : Blo 275825 277703 := bstep (se 1 (by rfl) ⟨208277, by rfl⟩ : syracuseStep 277703 = 416555) B416555
theorem B277723 : Blo 275825 277723 := bstep (se 1 (by rfl) ⟨208292, by rfl⟩ : syracuseStep 277723 = 416585) B416585
theorem B277799 : Blo 275825 277799 := bstep (se 1 (by rfl) ⟨208349, by rfl⟩ : syracuseStep 277799 = 416699) B416699
theorem B277839 : Blo 275825 277839 := bstep (se 1 (by rfl) ⟨208379, by rfl⟩ : syracuseStep 277839 = 416759) B416759
theorem B277855 : Blo 275825 277855 := bstep (se 1 (by rfl) ⟨208391, by rfl⟩ : syracuseStep 277855 = 416783) B416783
theorem B703849 : Blo 275825 703849 := bstep (se 2 (by rfl) ⟨263943, by rfl⟩ : syracuseStep 703849 = 527887) B527887
theorem B277883 : Blo 275825 277883 := bstep (se 1 (by rfl) ⟨208412, by rfl⟩ : syracuseStep 277883 = 416825) B416825
theorem B2243965 : Blo 275825 2243965 := bstep (se 3 (by rfl) ⟨420743, by rfl⟩ : syracuseStep 2243965 = 841487) B841487
theorem B2538877 : Blo 275825 2538877 := bstep (se 3 (by rfl) ⟨476039, by rfl⟩ : syracuseStep 2538877 = 952079) B952079
theorem B277935 : Blo 275825 277935 := bstep (se 1 (by rfl) ⟨208451, by rfl⟩ : syracuseStep 277935 = 416903) B416903
theorem B277959 : Blo 275825 277959 := bstep (se 1 (by rfl) ⟨208469, by rfl⟩ : syracuseStep 277959 = 416939) B416939
theorem B310747 : Blo 275825 310747 := bstep (se 1 (by rfl) ⟨233060, by rfl⟩ : syracuseStep 310747 = 466121) B466121
theorem B277979 : Blo 275825 277979 := bstep (se 1 (by rfl) ⟨208484, by rfl⟩ : syracuseStep 277979 = 416969) B416969
theorem B8535581 : Blo 275825 8535581 := bstep (se 3 (by rfl) ⟨1600421, by rfl⟩ : syracuseStep 8535581 = 3200843) B3200843
theorem B278055 : Blo 275825 278055 := bstep (se 1 (by rfl) ⟨208541, by rfl⟩ : syracuseStep 278055 = 417083) B417083
theorem B278095 : Blo 275825 278095 := bstep (se 1 (by rfl) ⟨208571, by rfl⟩ : syracuseStep 278095 = 417143) B417143
theorem B278111 : Blo 275825 278111 := bstep (se 1 (by rfl) ⟨208583, by rfl⟩ : syracuseStep 278111 = 417167) B417167
theorem B704123 : Blo 275825 704123 := bstep (se 1 (by rfl) ⟨528092, by rfl⟩ : syracuseStep 704123 = 1056185) B1056185
theorem B1425019 : Blo 275825 1425019 := bstep (se 1 (by rfl) ⟨1068764, by rfl⟩ : syracuseStep 1425019 = 2137529) B2137529
theorem B278139 : Blo 275825 278139 := bstep (se 1 (by rfl) ⟨208604, by rfl⟩ : syracuseStep 278139 = 417209) B417209
theorem B278191 : Blo 275825 278191 := bstep (se 1 (by rfl) ⟨208643, by rfl⟩ : syracuseStep 278191 = 417287) B417287
theorem B278215 : Blo 275825 278215 := bstep (se 1 (by rfl) ⟨208661, by rfl⟩ : syracuseStep 278215 = 417323) B417323
theorem B278235 : Blo 275825 278235 := bstep (se 1 (by rfl) ⟨208676, by rfl⟩ : syracuseStep 278235 = 417353) B417353
theorem B278311 : Blo 275825 278311 := bstep (se 1 (by rfl) ⟨208733, by rfl⟩ : syracuseStep 278311 = 417467) B417467
theorem B278351 : Blo 275825 278351 := bstep (se 1 (by rfl) ⟨208763, by rfl⟩ : syracuseStep 278351 = 417527) B417527
theorem B278367 : Blo 275825 278367 := bstep (se 1 (by rfl) ⟨208775, by rfl⟩ : syracuseStep 278367 = 417551) B417551
theorem B278395 : Blo 275825 278395 := bstep (se 1 (by rfl) ⟨208796, by rfl⟩ : syracuseStep 278395 = 417593) B417593
theorem B311215 : Blo 275825 311215 := bstep (se 1 (by rfl) ⟨233411, by rfl⟩ : syracuseStep 311215 = 466823) B466823
theorem B278447 : Blo 275825 278447 := bstep (se 1 (by rfl) ⟨208835, by rfl⟩ : syracuseStep 278447 = 417671) B417671
theorem B278471 : Blo 275825 278471 := bstep (se 1 (by rfl) ⟨208853, by rfl⟩ : syracuseStep 278471 = 417707) B417707
theorem B278491 : Blo 275825 278491 := bstep (se 1 (by rfl) ⟨208868, by rfl⟩ : syracuseStep 278491 = 417737) B417737
theorem B278567 : Blo 275825 278567 := bstep (se 1 (by rfl) ⟨208925, by rfl⟩ : syracuseStep 278567 = 417851) B417851
theorem B2113613 : Blo 275825 2113613 := bstep (se 3 (by rfl) ⟨396302, by rfl⟩ : syracuseStep 2113613 = 792605) B792605
theorem B278607 : Blo 275825 278607 := bstep (se 1 (by rfl) ⟨208955, by rfl⟩ : syracuseStep 278607 = 417911) B417911
theorem B1261649 : Blo 275825 1261649 := bstep (se 2 (by rfl) ⟨473118, by rfl⟩ : syracuseStep 1261649 = 946237) B946237
theorem B278623 : Blo 275825 278623 := bstep (se 1 (by rfl) ⟨208967, by rfl⟩ : syracuseStep 278623 = 417935) B417935
theorem B1130611 : Blo 275825 1130611 := bstep (se 1 (by rfl) ⟨847958, by rfl⟩ : syracuseStep 1130611 = 1695917) B1695917
theorem B278651 : Blo 275825 278651 := bstep (se 1 (by rfl) ⟨208988, by rfl⟩ : syracuseStep 278651 = 417977) B417977
theorem B278703 : Blo 275825 278703 := bstep (se 1 (by rfl) ⟨209027, by rfl⟩ : syracuseStep 278703 = 418055) B418055
theorem B278727 : Blo 275825 278727 := bstep (se 1 (by rfl) ⟨209045, by rfl⟩ : syracuseStep 278727 = 418091) B418091
theorem B278747 : Blo 275825 278747 := bstep (se 1 (by rfl) ⟨209060, by rfl⟩ : syracuseStep 278747 = 418121) B418121
theorem B278823 : Blo 275825 278823 := bstep (se 1 (by rfl) ⟨209117, by rfl⟩ : syracuseStep 278823 = 418235) B418235
theorem B278863 : Blo 275825 278863 := bstep (se 1 (by rfl) ⟨209147, by rfl⟩ : syracuseStep 278863 = 418295) B418295
theorem B311647 : Blo 275825 311647 := bstep (se 1 (by rfl) ⟨233735, by rfl⟩ : syracuseStep 311647 = 467471) B467471
theorem B278879 : Blo 275825 278879 := bstep (se 1 (by rfl) ⟨209159, by rfl⟩ : syracuseStep 278879 = 418319) B418319
theorem B377195 : Blo 275825 377195 := bstep (se 1 (by rfl) ⟨282896, by rfl⟩ : syracuseStep 377195 = 565793) B565793
theorem B278907 : Blo 275825 278907 := bstep (se 1 (by rfl) ⟨209180, by rfl⟩ : syracuseStep 278907 = 418361) B418361
theorem B278959 : Blo 275825 278959 := bstep (se 1 (by rfl) ⟨209219, by rfl⟩ : syracuseStep 278959 = 418439) B418439
theorem B278983 : Blo 275825 278983 := bstep (se 1 (by rfl) ⟨209237, by rfl⟩ : syracuseStep 278983 = 418475) B418475
theorem B279003 : Blo 275825 279003 := bstep (se 1 (by rfl) ⟨209252, by rfl⟩ : syracuseStep 279003 = 418505) B418505
theorem B442919 : Blo 275825 442919 := bstep (se 1 (by rfl) ⟨332189, by rfl⟩ : syracuseStep 442919 = 664379) B664379
theorem B279079 : Blo 275825 279079 := bstep (se 1 (by rfl) ⟨209309, by rfl⟩ : syracuseStep 279079 = 418619) B418619
theorem B279119 : Blo 275825 279119 := bstep (se 1 (by rfl) ⟨209339, by rfl⟩ : syracuseStep 279119 = 418679) B418679
theorem B279135 : Blo 275825 279135 := bstep (se 1 (by rfl) ⟨209351, by rfl⟩ : syracuseStep 279135 = 418703) B418703
theorem B934523 : Blo 275825 934523 := bstep (se 1 (by rfl) ⟨700892, by rfl⟩ : syracuseStep 934523 = 1401785) B1401785
theorem B279163 : Blo 275825 279163 := bstep (se 1 (by rfl) ⟨209372, by rfl⟩ : syracuseStep 279163 = 418745) B418745
theorem B279215 : Blo 275825 279215 := bstep (se 1 (by rfl) ⟨209411, by rfl⟩ : syracuseStep 279215 = 418823) B418823
theorem B312007 : Blo 275825 312007 := bstep (se 1 (by rfl) ⟨234005, by rfl⟩ : syracuseStep 312007 = 468011) B468011
theorem B279239 : Blo 275825 279239 := bstep (se 1 (by rfl) ⟨209429, by rfl⟩ : syracuseStep 279239 = 418859) B418859
theorem B279259 : Blo 275825 279259 := bstep (se 1 (by rfl) ⟨209444, by rfl⟩ : syracuseStep 279259 = 418889) B418889
theorem B934685 : Blo 275825 934685 := bstep (se 3 (by rfl) ⟨175253, by rfl⟩ : syracuseStep 934685 = 350507) B350507
theorem B279335 : Blo 275825 279335 := bstep (se 1 (by rfl) ⟨209501, by rfl⟩ : syracuseStep 279335 = 419003) B419003
theorem B1000259 : Blo 275825 1000259 := bstep (se 1 (by rfl) ⟨750194, by rfl⟩ : syracuseStep 1000259 = 1500389) B1500389
theorem B1786697 : Blo 275825 1786697 := bstep (se 2 (by rfl) ⟨670011, by rfl⟩ : syracuseStep 1786697 = 1340023) B1340023
theorem B279375 : Blo 275825 279375 := bstep (se 1 (by rfl) ⟨209531, by rfl⟩ : syracuseStep 279375 = 419063) B419063
theorem B279391 : Blo 275825 279391 := bstep (se 1 (by rfl) ⟨209543, by rfl⟩ : syracuseStep 279391 = 419087) B419087
theorem B279419 : Blo 275825 279419 := bstep (se 1 (by rfl) ⟨209564, by rfl⟩ : syracuseStep 279419 = 419129) B419129
theorem B279471 : Blo 275825 279471 := bstep (se 1 (by rfl) ⟨209603, by rfl⟩ : syracuseStep 279471 = 419207) B419207
theorem B443323 : Blo 275825 443323 := bstep (se 1 (by rfl) ⟨332492, by rfl⟩ : syracuseStep 443323 = 664985) B664985
theorem B279495 : Blo 275825 279495 := bstep (se 1 (by rfl) ⟨209621, by rfl⟩ : syracuseStep 279495 = 419243) B419243
theorem B279515 : Blo 275825 279515 := bstep (se 1 (by rfl) ⟨209636, by rfl⟩ : syracuseStep 279515 = 419273) B419273
theorem B279591 : Blo 275825 279591 := bstep (se 1 (by rfl) ⟨209693, by rfl⟩ : syracuseStep 279591 = 419387) B419387
theorem B279631 : Blo 275825 279631 := bstep (se 1 (by rfl) ⟨209723, by rfl⟩ : syracuseStep 279631 = 419447) B419447
theorem B279647 : Blo 275825 279647 := bstep (se 1 (by rfl) ⟨209735, by rfl⟩ : syracuseStep 279647 = 419471) B419471
theorem B279675 : Blo 275825 279675 := bstep (se 1 (by rfl) ⟨209756, by rfl⟩ : syracuseStep 279675 = 419513) B419513
theorem B279727 : Blo 275825 279727 := bstep (se 1 (by rfl) ⟨209795, by rfl⟩ : syracuseStep 279727 = 419591) B419591
theorem B279751 : Blo 275825 279751 := bstep (se 1 (by rfl) ⟨209813, by rfl⟩ : syracuseStep 279751 = 419627) B419627
theorem B279771 : Blo 275825 279771 := bstep (se 1 (by rfl) ⟨209828, by rfl⟩ : syracuseStep 279771 = 419657) B419657
theorem B705935 : Blo 275825 705935 := bstep (se 1 (by rfl) ⟨529451, by rfl⟩ : syracuseStep 705935 = 1058903) B1058903
theorem B1066459 : Blo 275825 1066459 := bstep (se 1 (by rfl) ⟨799844, by rfl⟩ : syracuseStep 1066459 = 1599689) B1599689
theorem B935387 : Blo 275825 935387 := bstep (se 1 (by rfl) ⟨701540, by rfl⟩ : syracuseStep 935387 = 1403081) B1403081
theorem B312871 : Blo 275825 312871 := bstep (se 1 (by rfl) ⟨234653, by rfl⟩ : syracuseStep 312871 = 469307) B469307
theorem B706259 : Blo 275825 706259 := bstep (se 1 (by rfl) ⟨529694, by rfl⟩ : syracuseStep 706259 = 1059389) B1059389
theorem B936089 : Blo 275825 936089 := bstep (se 2 (by rfl) ⟨351033, by rfl⟩ : syracuseStep 936089 = 702067) B702067
theorem B2116043 : Blo 275825 2116043 := bstep (se 1 (by rfl) ⟨1587032, by rfl⟩ : syracuseStep 2116043 = 3174065) B3174065
theorem B1362863 : Blo 275825 1362863 := bstep (se 1 (by rfl) ⟨1022147, by rfl⟩ : syracuseStep 1362863 = 2044295) B2044295
theorem B1264567 : Blo 275825 1264567 := bstep (se 1 (by rfl) ⟨948425, by rfl⟩ : syracuseStep 1264567 = 1896851) B1896851
theorem B314491 : Blo 275825 314491 := bstep (se 1 (by rfl) ⟨235868, by rfl⟩ : syracuseStep 314491 = 471737) B471737
theorem B937277 : Blo 275825 937277 := bstep (se 3 (by rfl) ⟨175739, by rfl⟩ : syracuseStep 937277 = 351479) B351479
theorem B446123 : Blo 275825 446123 := bstep (se 1 (by rfl) ⟨334592, by rfl⟩ : syracuseStep 446123 = 669185) B669185
theorem B1396439 : Blo 275825 1396439 := bstep (se 1 (by rfl) ⟨1047329, by rfl⟩ : syracuseStep 1396439 = 2094659) B2094659
theorem B1593047 : Blo 275825 1593047 := bstep (se 1 (by rfl) ⟨1194785, by rfl⟩ : syracuseStep 1593047 = 2389571) B2389571
theorem B1330987 : Blo 275825 1330987 := bstep (se 1 (by rfl) ⟨998240, by rfl⟩ : syracuseStep 1330987 = 1996481) B1996481
theorem B446315 : Blo 275825 446315 := bstep (se 1 (by rfl) ⟨334736, by rfl⟩ : syracuseStep 446315 = 669473) B669473
theorem B1003373 : Blo 275825 1003373 := bstep (se 3 (by rfl) ⟨188132, by rfl⟩ : syracuseStep 1003373 = 376265) B376265
theorem B413819 : Blo 275825 413819 := bstep (se 1 (by rfl) ⟨310364, by rfl⟩ : syracuseStep 413819 = 620729) B620729
theorem B938141 : Blo 275825 938141 := bstep (se 3 (by rfl) ⟨175901, by rfl⟩ : syracuseStep 938141 = 351803) B351803
theorem B413945 : Blo 275825 413945 := bstep (se 2 (by rfl) ⟨155229, by rfl⟩ : syracuseStep 413945 = 310459) B310459
theorem B414047 : Blo 275825 414047 := bstep (se 1 (by rfl) ⟨310535, by rfl⟩ : syracuseStep 414047 = 621071) B621071
theorem B414059 : Blo 275825 414059 := bstep (se 1 (by rfl) ⟨310544, by rfl⟩ : syracuseStep 414059 = 621089) B621089
theorem B414287 : Blo 275825 414287 := bstep (se 1 (by rfl) ⟨310715, by rfl⟩ : syracuseStep 414287 = 621431) B621431
theorem B1004167 : Blo 275825 1004167 := bstep (se 1 (by rfl) ⟨753125, by rfl⟩ : syracuseStep 1004167 = 1506251) B1506251
theorem B938681 : Blo 275825 938681 := bstep (se 2 (by rfl) ⟨352005, by rfl⟩ : syracuseStep 938681 = 704011) B704011
theorem B414407 : Blo 275825 414407 := bstep (se 1 (by rfl) ⟨310805, by rfl⟩ : syracuseStep 414407 = 621611) B621611
theorem B2118473 : Blo 275825 2118473 := bstep (se 2 (by rfl) ⟨794427, by rfl⟩ : syracuseStep 2118473 = 1588855) B1588855
theorem B414569 : Blo 275825 414569 := bstep (se 2 (by rfl) ⟨155463, by rfl⟩ : syracuseStep 414569 = 310927) B310927
theorem B414647 : Blo 275825 414647 := bstep (se 1 (by rfl) ⟨310985, by rfl⟩ : syracuseStep 414647 = 621971) B621971
theorem B414683 : Blo 275825 414683 := bstep (se 1 (by rfl) ⟨311012, by rfl⟩ : syracuseStep 414683 = 622025) B622025
theorem B447527 : Blo 275825 447527 := bstep (se 1 (by rfl) ⟨335645, by rfl⟩ : syracuseStep 447527 = 671291) B671291
theorem B939275 : Blo 275825 939275 := bstep (se 1 (by rfl) ⟨704456, by rfl⟩ : syracuseStep 939275 = 1408913) B1408913
theorem B349535 : Blo 275825 349535 := bstep (se 1 (by rfl) ⟨262151, by rfl⟩ : syracuseStep 349535 = 524303) B524303
theorem B415151 : Blo 275825 415151 := bstep (se 1 (by rfl) ⟨311363, by rfl⟩ : syracuseStep 415151 = 622727) B622727
theorem B415241 : Blo 275825 415241 := bstep (se 2 (by rfl) ⟨155715, by rfl⟩ : syracuseStep 415241 = 311431) B311431
theorem B939545 : Blo 275825 939545 := bstep (se 2 (by rfl) ⟨352329, by rfl⟩ : syracuseStep 939545 = 704659) B704659
theorem B415271 : Blo 275825 415271 := bstep (se 1 (by rfl) ⟨311453, by rfl⟩ : syracuseStep 415271 = 622907) B622907
theorem B448039 : Blo 275825 448039 := bstep (se 1 (by rfl) ⟨336029, by rfl⟩ : syracuseStep 448039 = 672059) B672059
theorem B3200573 : Blo 275825 3200573 := bstep (se 3 (by rfl) ⟨600107, by rfl⟩ : syracuseStep 3200573 = 1200215) B1200215
theorem B12342881 : Blo 275825 12342881 := bstep (se 2 (by rfl) ⟨4628580, by rfl⟩ : syracuseStep 12342881 = 9257161) B9257161
theorem B415355 : Blo 275825 415355 := bstep (se 1 (by rfl) ⟨311516, by rfl⟩ : syracuseStep 415355 = 623033) B623033
theorem B3987143 : Blo 275825 3987143 := bstep (se 1 (by rfl) ⟨2990357, by rfl⟩ : syracuseStep 3987143 = 5980715) B5980715
theorem B906967 : Blo 275825 906967 := bstep (se 1 (by rfl) ⟨680225, by rfl⟩ : syracuseStep 906967 = 1360451) B1360451
theorem B415481 : Blo 275825 415481 := bstep (se 2 (by rfl) ⟨155805, by rfl⟩ : syracuseStep 415481 = 311611) B311611
theorem B415583 : Blo 275825 415583 := bstep (se 1 (by rfl) ⟨311687, by rfl⟩ : syracuseStep 415583 = 623375) B623375
theorem B1202015 : Blo 275825 1202015 := bstep (se 1 (by rfl) ⟨901511, by rfl⟩ : syracuseStep 1202015 = 1803023) B1803023
theorem B415595 : Blo 275825 415595 := bstep (se 1 (by rfl) ⟨311696, by rfl⟩ : syracuseStep 415595 = 623393) B623393
theorem B415823 : Blo 275825 415823 := bstep (se 1 (by rfl) ⟨311867, by rfl⟩ : syracuseStep 415823 = 623735) B623735
theorem B415943 : Blo 275825 415943 := bstep (se 1 (by rfl) ⟨311957, by rfl⟩ : syracuseStep 415943 = 623915) B623915
theorem B416105 : Blo 275825 416105 := bstep (se 2 (by rfl) ⟨156039, by rfl⟩ : syracuseStep 416105 = 312079) B312079
theorem B416183 : Blo 275825 416183 := bstep (se 1 (by rfl) ⟨312137, by rfl⟩ : syracuseStep 416183 = 624275) B624275
theorem B416219 : Blo 275825 416219 := bstep (se 1 (by rfl) ⟨312164, by rfl⟩ : syracuseStep 416219 = 624329) B624329
theorem B1399355 : Blo 275825 1399355 := bstep (se 1 (by rfl) ⟨1049516, by rfl⟩ : syracuseStep 1399355 = 2099033) B2099033
theorem B940679 : Blo 275825 940679 := bstep (se 1 (by rfl) ⟨705509, by rfl⟩ : syracuseStep 940679 = 1411019) B1411019
theorem B940733 : Blo 275825 940733 := bstep (se 3 (by rfl) ⟨176387, by rfl⟩ : syracuseStep 940733 = 352775) B352775
theorem B940895 : Blo 275825 940895 := bstep (se 1 (by rfl) ⟨705671, by rfl⟩ : syracuseStep 940895 = 1411343) B1411343
theorem B416687 : Blo 275825 416687 := bstep (se 1 (by rfl) ⟨312515, by rfl⟩ : syracuseStep 416687 = 625031) B625031
theorem B941057 : Blo 275825 941057 := bstep (se 2 (by rfl) ⟨352896, by rfl⟩ : syracuseStep 941057 = 705793) B705793
theorem B416777 : Blo 275825 416777 := bstep (se 2 (by rfl) ⟨156291, by rfl⟩ : syracuseStep 416777 = 312583) B312583
theorem B416807 : Blo 275825 416807 := bstep (se 1 (by rfl) ⟨312605, by rfl⟩ : syracuseStep 416807 = 625211) B625211
theorem B416891 : Blo 275825 416891 := bstep (se 1 (by rfl) ⟨312668, by rfl⟩ : syracuseStep 416891 = 625337) B625337
theorem B1400003 : Blo 275825 1400003 := bstep (se 1 (by rfl) ⟨1050002, by rfl⟩ : syracuseStep 1400003 = 2100005) B2100005
theorem B417017 : Blo 275825 417017 := bstep (se 2 (by rfl) ⟨156381, by rfl⟩ : syracuseStep 417017 = 312763) B312763
theorem B417119 : Blo 275825 417119 := bstep (se 1 (by rfl) ⟨312839, by rfl⟩ : syracuseStep 417119 = 625679) B625679
theorem B417131 : Blo 275825 417131 := bstep (se 1 (by rfl) ⟨312848, by rfl⟩ : syracuseStep 417131 = 625697) B625697
theorem B417359 : Blo 275825 417359 := bstep (se 1 (by rfl) ⟨313019, by rfl⟩ : syracuseStep 417359 = 626039) B626039
theorem B417479 : Blo 275825 417479 := bstep (se 1 (by rfl) ⟨313109, by rfl⟩ : syracuseStep 417479 = 626219) B626219
theorem B1695431 : Blo 275825 1695431 := bstep (se 1 (by rfl) ⟨1271573, by rfl⟩ : syracuseStep 1695431 = 2543147) B2543147
theorem B1924823 : Blo 275825 1924823 := bstep (se 1 (by rfl) ⟨1443617, by rfl⟩ : syracuseStep 1924823 = 2887235) B2887235
theorem B941867 : Blo 275825 941867 := bstep (se 1 (by rfl) ⟨706400, by rfl⟩ : syracuseStep 941867 = 1412801) B1412801
theorem B417641 : Blo 275825 417641 := bstep (se 2 (by rfl) ⟨156615, by rfl⟩ : syracuseStep 417641 = 313231) B313231
theorem B352183 : Blo 275825 352183 := bstep (se 1 (by rfl) ⟨264137, by rfl⟩ : syracuseStep 352183 = 528275) B528275
theorem B417719 : Blo 275825 417719 := bstep (se 1 (by rfl) ⟨313289, by rfl⟩ : syracuseStep 417719 = 626579) B626579
theorem B417755 : Blo 275825 417755 := bstep (se 1 (by rfl) ⟨313316, by rfl⟩ : syracuseStep 417755 = 626633) B626633
theorem B942137 : Blo 275825 942137 := bstep (se 2 (by rfl) ⟨353301, by rfl⟩ : syracuseStep 942137 = 706603) B706603
theorem B1794163 : Blo 275825 1794163 := bstep (se 1 (by rfl) ⟨1345622, by rfl⟩ : syracuseStep 1794163 = 2691245) B2691245
theorem B942461 : Blo 275825 942461 := bstep (se 3 (by rfl) ⟨176711, by rfl⟩ : syracuseStep 942461 = 353423) B353423
theorem B418223 : Blo 275825 418223 := bstep (se 1 (by rfl) ⟨313667, by rfl⟩ : syracuseStep 418223 = 627335) B627335
theorem B418313 : Blo 275825 418313 := bstep (se 2 (by rfl) ⟨156867, by rfl⟩ : syracuseStep 418313 = 313735) B313735
theorem B418343 : Blo 275825 418343 := bstep (se 1 (by rfl) ⟨313757, by rfl⟩ : syracuseStep 418343 = 627515) B627515
theorem B418427 : Blo 275825 418427 := bstep (se 1 (by rfl) ⟨313820, by rfl⟩ : syracuseStep 418427 = 627641) B627641
theorem B942731 : Blo 275825 942731 := bstep (se 1 (by rfl) ⟨707048, by rfl⟩ : syracuseStep 942731 = 1414097) B1414097
theorem B484039 : Blo 275825 484039 := bstep (se 1 (by rfl) ⟨363029, by rfl⟩ : syracuseStep 484039 = 726059) B726059
theorem B418553 : Blo 275825 418553 := bstep (se 2 (by rfl) ⟨156957, by rfl⟩ : syracuseStep 418553 = 313915) B313915
theorem B418655 : Blo 275825 418655 := bstep (se 1 (by rfl) ⟨313991, by rfl⟩ : syracuseStep 418655 = 627983) B627983
theorem B418667 : Blo 275825 418667 := bstep (se 1 (by rfl) ⟨314000, by rfl⟩ : syracuseStep 418667 = 628001) B628001
theorem B648271 : Blo 275825 648271 := bstep (se 1 (by rfl) ⟨486203, by rfl⟩ : syracuseStep 648271 = 972407) B972407
theorem B418895 : Blo 275825 418895 := bstep (se 1 (by rfl) ⟨314171, by rfl⟩ : syracuseStep 418895 = 628343) B628343
theorem B353479 : Blo 275825 353479 := bstep (se 1 (by rfl) ⟨265109, by rfl⟩ : syracuseStep 353479 = 530219) B530219
theorem B419015 : Blo 275825 419015 := bstep (se 1 (by rfl) ⟨314261, by rfl⟩ : syracuseStep 419015 = 628523) B628523
theorem B419177 : Blo 275825 419177 := bstep (se 2 (by rfl) ⟨157191, by rfl⟩ : syracuseStep 419177 = 314383) B314383
theorem B419255 : Blo 275825 419255 := bstep (se 1 (by rfl) ⟨314441, by rfl⟩ : syracuseStep 419255 = 628883) B628883
theorem B419291 : Blo 275825 419291 := bstep (se 1 (by rfl) ⟨314468, by rfl⟩ : syracuseStep 419291 = 628937) B628937
theorem B943649 : Blo 275825 943649 := bstep (se 2 (by rfl) ⟨353868, by rfl⟩ : syracuseStep 943649 = 707737) B707737
theorem B943865 : Blo 275825 943865 := bstep (se 2 (by rfl) ⟨353949, by rfl⟩ : syracuseStep 943865 = 707899) B707899
theorem B1894337 : Blo 275825 1894337 := bstep (se 2 (by rfl) ⟨710376, by rfl⟩ : syracuseStep 1894337 = 1420753) B1420753
theorem B944135 : Blo 275825 944135 := bstep (se 1 (by rfl) ⟨708101, by rfl⟩ : syracuseStep 944135 = 1416203) B1416203
theorem B944243 : Blo 275825 944243 := bstep (se 1 (by rfl) ⟨708182, by rfl⟩ : syracuseStep 944243 = 1416365) B1416365
theorem B4811399 : Blo 275825 4811399 := bstep (se 1 (by rfl) ⟨3608549, by rfl⟩ : syracuseStep 4811399 = 7217099) B7217099
theorem B486319 : Blo 275825 486319 := bstep (se 1 (by rfl) ⟨364739, by rfl⟩ : syracuseStep 486319 = 729479) B729479
theorem B749179 : Blo 275825 749179 := bstep (se 1 (by rfl) ⟨561884, by rfl⟩ : syracuseStep 749179 = 1123769) B1123769
theorem B1404539 : Blo 275825 1404539 := bstep (se 1 (by rfl) ⟨1053404, by rfl⟩ : syracuseStep 1404539 = 2106809) B2106809
theorem B749407 : Blo 275825 749407 := bstep (se 1 (by rfl) ⟨562055, by rfl⟩ : syracuseStep 749407 = 1124111) B1124111
theorem B1503137 : Blo 275825 1503137 := bstep (se 2 (by rfl) ⟨563676, by rfl⟩ : syracuseStep 1503137 = 1127353) B1127353
theorem B717511 : Blo 275825 717511 := bstep (se 1 (by rfl) ⟨538133, by rfl⟩ : syracuseStep 717511 = 1076267) B1076267
theorem B750973 : Blo 275825 750973 := bstep (se 3 (by rfl) ⟨140807, by rfl⟩ : syracuseStep 750973 = 281615) B281615
theorem B9598925 : Blo 275825 9598925 := bstep (se 3 (by rfl) ⟨1799798, by rfl⟩ : syracuseStep 9598925 = 3599597) B3599597
theorem B1407293 : Blo 275825 1407293 := bstep (se 3 (by rfl) ⟨263867, by rfl⟩ : syracuseStep 1407293 = 527735) B527735
theorem B2685271 : Blo 275825 2685271 := bstep (se 1 (by rfl) ⟨2013953, by rfl⟩ : syracuseStep 2685271 = 4027907) B4027907
theorem B1571177 : Blo 275825 1571177 := bstep (se 2 (by rfl) ⟨589191, by rfl⟩ : syracuseStep 1571177 = 1178383) B1178383
theorem B621179 : Blo 275825 621179 := bstep (se 1 (by rfl) ⟨465884, by rfl⟩ : syracuseStep 621179 = 931769) B931769
theorem B3013321 : Blo 275825 3013321 := bstep (se 2 (by rfl) ⟨1129995, by rfl⟩ : syracuseStep 3013321 = 2259991) B2259991
theorem B4029173 : Blo 275825 4029173 := bstep (se 5 (by rfl) ⟨188867, by rfl⟩ : syracuseStep 4029173 = 377735) B377735
theorem B621305 : Blo 275825 621305 := bstep (se 2 (by rfl) ⟨232989, by rfl⟩ : syracuseStep 621305 = 465979) B465979
theorem B949249 : Blo 275825 949249 := bstep (se 2 (by rfl) ⟨355968, by rfl⟩ : syracuseStep 949249 = 711937) B711937
theorem B621575 : Blo 275825 621575 := bstep (se 1 (by rfl) ⟨466181, by rfl⟩ : syracuseStep 621575 = 932363) B932363
theorem B1768499 : Blo 275825 1768499 := bstep (se 1 (by rfl) ⟨1326374, by rfl⟩ : syracuseStep 1768499 = 2652749) B2652749
theorem B621647 : Blo 275825 621647 := bstep (se 1 (by rfl) ⟨466235, by rfl⟩ : syracuseStep 621647 = 932471) B932471
theorem B1047937 : Blo 275825 1047937 := bstep (se 2 (by rfl) ⟨392976, by rfl⟩ : syracuseStep 1047937 = 785953) B785953
theorem B2096603 : Blo 275825 2096603 := bstep (se 1 (by rfl) ⟨1572452, by rfl⟩ : syracuseStep 2096603 = 3144905) B3144905
theorem B622043 : Blo 275825 622043 := bstep (se 1 (by rfl) ⟨466532, by rfl⟩ : syracuseStep 622043 = 933065) B933065
theorem B1048211 : Blo 275825 1048211 := bstep (se 1 (by rfl) ⟨786158, by rfl⟩ : syracuseStep 1048211 = 1572317) B1572317
theorem B622511 : Blo 275825 622511 := bstep (se 1 (by rfl) ⟨466883, by rfl⟩ : syracuseStep 622511 = 933767) B933767
theorem B2097089 : Blo 275825 2097089 := bstep (se 2 (by rfl) ⟨786408, by rfl⟩ : syracuseStep 2097089 = 1572817) B1572817
theorem B622601 : Blo 275825 622601 := bstep (se 2 (by rfl) ⟨233475, by rfl⟩ : syracuseStep 622601 = 466951) B466951
theorem B1409075 : Blo 275825 1409075 := bstep (se 1 (by rfl) ⟨1056806, by rfl⟩ : syracuseStep 1409075 = 2113613) B2113613
theorem B2392217 : Blo 275825 2392217 := bstep (se 2 (by rfl) ⟨897081, by rfl⟩ : syracuseStep 2392217 = 1794163) B1794163
theorem B1507481 : Blo 275825 1507481 := bstep (se 2 (by rfl) ⟨565305, by rfl⟩ : syracuseStep 1507481 = 1130611) B1130611
theorem B623015 : Blo 275825 623015 := bstep (se 1 (by rfl) ⟨467261, by rfl⟩ : syracuseStep 623015 = 934523) B934523
theorem B623123 : Blo 275825 623123 := bstep (se 1 (by rfl) ⟨467342, by rfl⟩ : syracuseStep 623123 = 934685) B934685
theorem B524873 : Blo 275825 524873 := bstep (se 2 (by rfl) ⟨196827, by rfl⟩ : syracuseStep 524873 = 393655) B393655
theorem B623177 : Blo 275825 623177 := bstep (se 2 (by rfl) ⟨233691, by rfl⟩ : syracuseStep 623177 = 467383) B467383
theorem B3539659 : Blo 275825 3539659 := bstep (se 1 (by rfl) ⟨2654744, by rfl⟩ : syracuseStep 3539659 = 5309489) B5309489
theorem B623591 : Blo 275825 623591 := bstep (se 1 (by rfl) ⟨467693, by rfl⟩ : syracuseStep 623591 = 935387) B935387
theorem B2360663 : Blo 275825 2360663 := bstep (se 1 (by rfl) ⟨1770497, by rfl⟩ : syracuseStep 2360663 = 3540995) B3540995
theorem B623969 : Blo 275825 623969 := bstep (se 2 (by rfl) ⟨233988, by rfl⟩ : syracuseStep 623969 = 467977) B467977
theorem B624059 : Blo 275825 624059 := bstep (se 1 (by rfl) ⟨468044, by rfl⟩ : syracuseStep 624059 = 936089) B936089
theorem B1181117 : Blo 275825 1181117 := bstep (se 3 (by rfl) ⟨221459, by rfl⟩ : syracuseStep 1181117 = 442919) B442919
theorem B624185 : Blo 275825 624185 := bstep (se 2 (by rfl) ⟨234069, by rfl⟩ : syracuseStep 624185 = 468139) B468139
theorem B1410695 : Blo 275825 1410695 := bstep (se 1 (by rfl) ⟨1058021, by rfl⟩ : syracuseStep 1410695 = 2116043) B2116043
theorem B591823 : Blo 275825 591823 := bstep (se 1 (by rfl) ⟨443867, by rfl⟩ : syracuseStep 591823 = 887735) B887735
theorem B624851 : Blo 275825 624851 := bstep (se 1 (by rfl) ⟨468638, by rfl⟩ : syracuseStep 624851 = 937277) B937277
theorem B1607933 : Blo 275825 1607933 := bstep (se 3 (by rfl) ⟨301487, by rfl⟩ : syracuseStep 1607933 = 602975) B602975
theorem B624905 : Blo 275825 624905 := bstep (se 2 (by rfl) ⟨234339, by rfl⟩ : syracuseStep 624905 = 468679) B468679
theorem B297415 : Blo 275825 297415 := bstep (se 1 (by rfl) ⟨223061, by rfl⟩ : syracuseStep 297415 = 446123) B446123
theorem B526817 : Blo 275825 526817 := bstep (se 2 (by rfl) ⟨197556, by rfl⟩ : syracuseStep 526817 = 395113) B395113
theorem B625121 : Blo 275825 625121 := bstep (se 2 (by rfl) ⟨234420, by rfl⟩ : syracuseStep 625121 = 468841) B468841
theorem B1182347 : Blo 275825 1182347 := bstep (se 1 (by rfl) ⟨886760, by rfl⟩ : syracuseStep 1182347 = 1773521) B1773521
theorem B1182383 : Blo 275825 1182383 := bstep (se 1 (by rfl) ⟨886787, by rfl⟩ : syracuseStep 1182383 = 1773575) B1773575
theorem B625427 : Blo 275825 625427 := bstep (se 1 (by rfl) ⟨469070, by rfl⟩ : syracuseStep 625427 = 938141) B938141
theorem B625787 : Blo 275825 625787 := bstep (se 1 (by rfl) ⟨469340, by rfl⟩ : syracuseStep 625787 = 938681) B938681
theorem B1412315 : Blo 275825 1412315 := bstep (se 1 (by rfl) ⟨1059236, by rfl⟩ : syracuseStep 1412315 = 2118473) B2118473
theorem B625913 : Blo 275825 625913 := bstep (se 2 (by rfl) ⟨234717, by rfl⟩ : syracuseStep 625913 = 469435) B469435
theorem B298351 : Blo 275825 298351 := bstep (se 1 (by rfl) ⟨223763, by rfl⟩ : syracuseStep 298351 = 447527) B447527
theorem B396667 : Blo 275825 396667 := bstep (se 1 (by rfl) ⟨297500, by rfl⟩ : syracuseStep 396667 = 595001) B595001
theorem B5082497 : Blo 275825 5082497 := bstep (se 2 (by rfl) ⟨1905936, by rfl⟩ : syracuseStep 5082497 = 3811873) B3811873
theorem B626057 : Blo 275825 626057 := bstep (se 2 (by rfl) ⟨234771, by rfl⟩ : syracuseStep 626057 = 469543) B469543
theorem B626183 : Blo 275825 626183 := bstep (se 1 (by rfl) ⟨469637, by rfl⟩ : syracuseStep 626183 = 939275) B939275
theorem B396895 : Blo 275825 396895 := bstep (se 1 (by rfl) ⟨297671, by rfl⟩ : syracuseStep 396895 = 595343) B595343
theorem B2363053 : Blo 275825 2363053 := bstep (se 3 (by rfl) ⟨443072, by rfl⟩ : syracuseStep 2363053 = 886145) B886145
theorem B626363 : Blo 275825 626363 := bstep (se 1 (by rfl) ⟨469772, by rfl⟩ : syracuseStep 626363 = 939545) B939545
theorem B2133715 : Blo 275825 2133715 := bstep (se 1 (by rfl) ⟨1600286, by rfl⟩ : syracuseStep 2133715 = 3200573) B3200573
theorem B8228587 : Blo 275825 8228587 := bstep (se 1 (by rfl) ⟨6171440, by rfl⟩ : syracuseStep 8228587 = 12342881) B12342881
theorem B2658095 : Blo 275825 2658095 := bstep (se 1 (by rfl) ⟨1993571, by rfl⟩ : syracuseStep 2658095 = 3987143) B3987143
theorem B626489 : Blo 275825 626489 := bstep (se 2 (by rfl) ⟨234933, by rfl⟩ : syracuseStep 626489 = 469867) B469867
theorem B1413449 : Blo 275825 1413449 := bstep (se 2 (by rfl) ⟨530043, by rfl⟩ : syracuseStep 1413449 = 1060087) B1060087
theorem B5738825 : Blo 275825 5738825 := bstep (se 2 (by rfl) ⟨2152059, by rfl⟩ : syracuseStep 5738825 = 4304119) B4304119
theorem B627119 : Blo 275825 627119 := bstep (se 1 (by rfl) ⟨470339, by rfl⟩ : syracuseStep 627119 = 940679) B940679
theorem B627155 : Blo 275825 627155 := bstep (se 1 (by rfl) ⟨470366, by rfl⟩ : syracuseStep 627155 = 940733) B940733
theorem B627263 : Blo 275825 627263 := bstep (se 1 (by rfl) ⟨470447, by rfl⟩ : syracuseStep 627263 = 940895) B940895
theorem B627371 : Blo 275825 627371 := bstep (se 1 (by rfl) ⟨470528, by rfl⟩ : syracuseStep 627371 = 941057) B941057
theorem B2364389 : Blo 275825 2364389 := bstep (se 4 (by rfl) ⟨221661, by rfl⟩ : syracuseStep 2364389 = 443323) B443323
theorem B1774649 : Blo 275825 1774649 := bstep (se 2 (by rfl) ⟨665493, by rfl⟩ : syracuseStep 1774649 = 1330987) B1330987
theorem B1283215 : Blo 275825 1283215 := bstep (se 1 (by rfl) ⟨962411, by rfl⟩ : syracuseStep 1283215 = 1924823) B1924823
theorem B627911 : Blo 275825 627911 := bstep (se 1 (by rfl) ⟨470933, by rfl⟩ : syracuseStep 627911 = 941867) B941867
theorem B791785 : Blo 275825 791785 := bstep (se 2 (by rfl) ⟨296919, by rfl⟩ : syracuseStep 791785 = 593839) B593839
theorem B628091 : Blo 275825 628091 := bstep (se 1 (by rfl) ⟨471068, by rfl⟩ : syracuseStep 628091 = 942137) B942137
theorem B628217 : Blo 275825 628217 := bstep (se 2 (by rfl) ⟨235581, by rfl⟩ : syracuseStep 628217 = 471163) B471163
theorem B628307 : Blo 275825 628307 := bstep (se 1 (by rfl) ⟨471230, by rfl⟩ : syracuseStep 628307 = 942461) B942461
theorem B1414745 : Blo 275825 1414745 := bstep (se 2 (by rfl) ⟨530529, by rfl⟩ : syracuseStep 1414745 = 1061059) B1061059
theorem B628487 : Blo 275825 628487 := bstep (se 1 (by rfl) ⟨471365, by rfl⟩ : syracuseStep 628487 = 942731) B942731
theorem B956681 : Blo 275825 956681 := bstep (se 2 (by rfl) ⟨358755, by rfl⟩ : syracuseStep 956681 = 717511) B717511
theorem B1186073 : Blo 275825 1186073 := bstep (se 2 (by rfl) ⟨444777, by rfl⟩ : syracuseStep 1186073 = 889555) B889555
theorem B629099 : Blo 275825 629099 := bstep (se 1 (by rfl) ⟨471824, by rfl⟩ : syracuseStep 629099 = 943649) B943649
theorem B2988413 : Blo 275825 2988413 := bstep (se 3 (by rfl) ⟨560327, by rfl⟩ : syracuseStep 2988413 = 1120655) B1120655
theorem B1055227 : Blo 275825 1055227 := bstep (se 1 (by rfl) ⟨791420, by rfl⟩ : syracuseStep 1055227 = 1582841) B1582841
theorem B629243 : Blo 275825 629243 := bstep (se 1 (by rfl) ⟨471932, by rfl⟩ : syracuseStep 629243 = 943865) B943865
theorem B629369 : Blo 275825 629369 := bstep (se 2 (by rfl) ⟨236013, by rfl⟩ : syracuseStep 629369 = 472027) B472027
theorem B629423 : Blo 275825 629423 := bstep (se 1 (by rfl) ⟨472067, by rfl⟩ : syracuseStep 629423 = 944135) B944135
theorem B629495 : Blo 275825 629495 := bstep (se 1 (by rfl) ⟨472121, by rfl⟩ : syracuseStep 629495 = 944243) B944243
theorem B465743 : Blo 275825 465743 := bstep (se 1 (by rfl) ⟨349307, by rfl⟩ : syracuseStep 465743 = 698615) B698615
theorem B891773 : Blo 275825 891773 := bstep (se 3 (by rfl) ⟨167207, by rfl⟩ : syracuseStep 891773 = 334415) B334415
theorem B596983 : Blo 275825 596983 := bstep (se 1 (by rfl) ⟨447737, by rfl⟩ : syracuseStep 596983 = 895475) B895475
theorem B597385 : Blo 275825 597385 := bstep (se 2 (by rfl) ⟨224019, by rfl⟩ : syracuseStep 597385 = 448039) B448039
theorem B1056199 : Blo 275825 1056199 := bstep (se 1 (by rfl) ⟨792149, by rfl⟩ : syracuseStep 1056199 = 1584299) B1584299
theorem B1777211 : Blo 275825 1777211 := bstep (se 1 (by rfl) ⟨1332908, by rfl⟩ : syracuseStep 1777211 = 2665817) B2665817
theorem B466735 : Blo 275825 466735 := bstep (se 1 (by rfl) ⟨350051, by rfl⟩ : syracuseStep 466735 = 700103) B700103
theorem B1581065 : Blo 275825 1581065 := bstep (se 2 (by rfl) ⟨592899, by rfl⟩ : syracuseStep 1581065 = 1185799) B1185799
theorem B795055 : Blo 275825 795055 := bstep (se 1 (by rfl) ⟨596291, by rfl⟩ : syracuseStep 795055 = 1192583) B1192583
theorem B3580361 : Blo 275825 3580361 := bstep (se 2 (by rfl) ⟨1342635, by rfl⟩ : syracuseStep 3580361 = 2685271) B2685271
theorem B54206981 : Blo 275825 54206981 := bstep (se 4 (by rfl) ⟨5081904, by rfl⟩ : syracuseStep 54206981 = 10163809) B10163809
theorem B598547 : Blo 275825 598547 := bstep (se 1 (by rfl) ⟨448910, by rfl⟩ : syracuseStep 598547 = 897821) B897821
theorem B6038225 : Blo 275825 6038225 := bstep (se 2 (by rfl) ⟨2264334, by rfl⟩ : syracuseStep 6038225 = 4528669) B4528669
theorem B2433887 : Blo 275825 2433887 := bstep (se 1 (by rfl) ⟨1825415, by rfl⟩ : syracuseStep 2433887 = 3650831) B3650831
theorem B4007029 : Blo 275825 4007029 := bstep (se 5 (by rfl) ⟨187829, by rfl⟩ : syracuseStep 4007029 = 375659) B375659
theorem B13477013 : Blo 275825 13477013 := bstep (se 6 (by rfl) ⟨315867, by rfl⟩ : syracuseStep 13477013 = 631735) B631735
theorem B402727 : Blo 275825 402727 := bstep (se 1 (by rfl) ⟨302045, by rfl⟩ : syracuseStep 402727 = 604091) B604091
theorem B6399283 : Blo 275825 6399283 := bstep (se 1 (by rfl) ⟨4799462, by rfl⟩ : syracuseStep 6399283 = 9598925) B9598925
theorem B1058143 : Blo 275825 1058143 := bstep (se 1 (by rfl) ⟨793607, by rfl⟩ : syracuseStep 1058143 = 1587215) B1587215
theorem B1058615 : Blo 275825 1058615 := bstep (se 1 (by rfl) ⟨793961, by rfl⟩ : syracuseStep 1058615 = 1587923) B1587923
theorem B2991953 : Blo 275825 2991953 := bstep (se 2 (by rfl) ⟨1121982, by rfl⟩ : syracuseStep 2991953 = 2243965) B2243965
theorem B3385169 : Blo 275825 3385169 := bstep (se 2 (by rfl) ⟨1269438, by rfl⟩ : syracuseStep 3385169 = 2538877) B2538877
theorem B1190173 : Blo 275825 1190173 := bstep (se 3 (by rfl) ⟨223157, by rfl⟩ : syracuseStep 1190173 = 446315) B446315
theorem B1059101 : Blo 275825 1059101 := bstep (se 3 (by rfl) ⟨198581, by rfl⟩ : syracuseStep 1059101 = 397163) B397163
theorem B469415 : Blo 275825 469415 := bstep (se 1 (by rfl) ⟨352061, by rfl⟩ : syracuseStep 469415 = 704123) B704123
theorem B698807 : Blo 275825 698807 := bstep (se 1 (by rfl) ⟨524105, by rfl⟩ : syracuseStep 698807 = 1048211) B1048211
theorem B469577 : Blo 275825 469577 := bstep (se 2 (by rfl) ⟨176091, by rfl⟩ : syracuseStep 469577 = 352183) B352183
theorem B621849635 : Blo 275825 621849635 := bstep (se 1 (by rfl) ⟨466387226, by rfl⟩ : syracuseStep 621849635 = 932774453) B932774453
theorem B994493 : Blo 275825 994493 := bstep (se 3 (by rfl) ⟨186467, by rfl⟩ : syracuseStep 994493 = 372935) B372935
theorem B666839 : Blo 275825 666839 := bstep (se 1 (by rfl) ⟨500129, by rfl⟩ : syracuseStep 666839 = 1000259) B1000259
theorem B1191131 : Blo 275825 1191131 := bstep (se 1 (by rfl) ⟨893348, by rfl⟩ : syracuseStep 1191131 = 1786697) B1786697
theorem B1584481 : Blo 275825 1584481 := bstep (se 2 (by rfl) ⟨594180, by rfl⟩ : syracuseStep 1584481 = 1188361) B1188361
theorem B34614641 : Blo 275825 34614641 := bstep (se 2 (by rfl) ⟨12980490, by rfl⟩ : syracuseStep 34614641 = 25960981) B25960981
theorem B8170993 : Blo 275825 8170993 := bstep (se 2 (by rfl) ⟨3064122, by rfl⟩ : syracuseStep 8170993 = 6128245) B6128245
theorem B699911 : Blo 275825 699911 := bstep (se 1 (by rfl) ⟨524933, by rfl⟩ : syracuseStep 699911 = 1049867) B1049867
theorem B699961 : Blo 275825 699961 := bstep (se 2 (by rfl) ⟨262485, by rfl⟩ : syracuseStep 699961 = 524971) B524971
theorem B1191505 : Blo 275825 1191505 := bstep (se 2 (by rfl) ⟨446814, by rfl⟩ : syracuseStep 1191505 = 893629) B893629
theorem B470623 : Blo 275825 470623 := bstep (se 1 (by rfl) ⟨352967, by rfl⟩ : syracuseStep 470623 = 705935) B705935
theorem B470839 : Blo 275825 470839 := bstep (se 1 (by rfl) ⟨353129, by rfl⟩ : syracuseStep 470839 = 706259) B706259
theorem B700265 : Blo 275825 700265 := bstep (se 2 (by rfl) ⟨262599, by rfl⟩ : syracuseStep 700265 = 525199) B525199
theorem B864361 : Blo 275825 864361 := bstep (se 2 (by rfl) ⟨324135, by rfl⟩ : syracuseStep 864361 = 648271) B648271
theorem B471305 : Blo 275825 471305 := bstep (se 2 (by rfl) ⟨176739, by rfl⟩ : syracuseStep 471305 = 353479) B353479
theorem B700883 : Blo 275825 700883 := bstep (se 1 (by rfl) ⟨525662, by rfl⟩ : syracuseStep 700883 = 1051325) B1051325
theorem B2863667 : Blo 275825 2863667 := bstep (se 1 (by rfl) ⟨2147750, by rfl⟩ : syracuseStep 2863667 = 4295501) B4295501
theorem B1421945 : Blo 275825 1421945 := bstep (se 2 (by rfl) ⟨533229, by rfl⟩ : syracuseStep 1421945 = 1066459) B1066459
theorem B930959 : Blo 275825 930959 := bstep (se 1 (by rfl) ⟨698219, by rfl⟩ : syracuseStep 930959 = 1396439) B1396439
theorem B1062031 : Blo 275825 1062031 := bstep (se 1 (by rfl) ⟨796523, by rfl⟩ : syracuseStep 1062031 = 1593047) B1593047
theorem B668915 : Blo 275825 668915 := bstep (se 1 (by rfl) ⟨501686, by rfl⟩ : syracuseStep 668915 = 1003373) B1003373
theorem B537953 : Blo 275825 537953 := bstep (se 2 (by rfl) ⟨201732, by rfl⟩ : syracuseStep 537953 = 403465) B403465
theorem B1062305 : Blo 275825 1062305 := bstep (se 2 (by rfl) ⟨398364, by rfl⟩ : syracuseStep 1062305 = 796729) B796729
theorem B275879 : Blo 275825 275879 := bstep (se 1 (by rfl) ⟨206909, by rfl⟩ : syracuseStep 275879 = 413819) B413819
theorem B275963 : Blo 275825 275963 := bstep (se 1 (by rfl) ⟨206972, by rfl⟩ : syracuseStep 275963 = 413945) B413945
theorem B276031 : Blo 275825 276031 := bstep (se 1 (by rfl) ⟨207023, by rfl⟩ : syracuseStep 276031 = 414047) B414047
theorem B276039 : Blo 275825 276039 := bstep (se 1 (by rfl) ⟨207029, by rfl⟩ : syracuseStep 276039 = 414059) B414059
theorem B702047 : Blo 275825 702047 := bstep (se 1 (by rfl) ⟨526535, by rfl⟩ : syracuseStep 702047 = 1053071) B1053071
theorem B276191 : Blo 275825 276191 := bstep (se 1 (by rfl) ⟨207143, by rfl⟩ : syracuseStep 276191 = 414287) B414287
theorem B276271 : Blo 275825 276271 := bstep (se 1 (by rfl) ⟨207203, by rfl⟩ : syracuseStep 276271 = 414407) B414407
theorem B3389303 : Blo 275825 3389303 := bstep (se 1 (by rfl) ⟨2541977, by rfl⟩ : syracuseStep 3389303 = 5083955) B5083955
theorem B276379 : Blo 275825 276379 := bstep (se 1 (by rfl) ⟨207284, by rfl⟩ : syracuseStep 276379 = 414569) B414569
theorem B276431 : Blo 275825 276431 := bstep (se 1 (by rfl) ⟨207323, by rfl⟩ : syracuseStep 276431 = 414647) B414647
theorem B276455 : Blo 275825 276455 := bstep (se 1 (by rfl) ⟨207341, by rfl⟩ : syracuseStep 276455 = 414683) B414683
theorem B637139 : Blo 275825 637139 := bstep (se 1 (by rfl) ⟨477854, by rfl⟩ : syracuseStep 637139 = 955709) B955709
theorem B932093 : Blo 275825 932093 := bstep (se 3 (by rfl) ⟨174767, by rfl⟩ : syracuseStep 932093 = 349535) B349535
theorem B276767 : Blo 275825 276767 := bstep (se 1 (by rfl) ⟨207575, by rfl⟩ : syracuseStep 276767 = 415151) B415151
theorem B276827 : Blo 275825 276827 := bstep (se 1 (by rfl) ⟨207620, by rfl⟩ : syracuseStep 276827 = 415241) B415241
theorem B702827 : Blo 275825 702827 := bstep (se 1 (by rfl) ⟨527120, by rfl⟩ : syracuseStep 702827 = 1054241) B1054241
theorem B276847 : Blo 275825 276847 := bstep (se 1 (by rfl) ⟨207635, by rfl⟩ : syracuseStep 276847 = 415271) B415271
theorem B276903 : Blo 275825 276903 := bstep (se 1 (by rfl) ⟨207677, by rfl⟩ : syracuseStep 276903 = 415355) B415355
theorem B276987 : Blo 275825 276987 := bstep (se 1 (by rfl) ⟨207740, by rfl⟩ : syracuseStep 276987 = 415481) B415481
theorem B277055 : Blo 275825 277055 := bstep (se 1 (by rfl) ⟨207791, by rfl⟩ : syracuseStep 277055 = 415583) B415583
theorem B801343 : Blo 275825 801343 := bstep (se 1 (by rfl) ⟨601007, by rfl⟩ : syracuseStep 801343 = 1202015) B1202015
theorem B703039 : Blo 275825 703039 := bstep (se 1 (by rfl) ⟨527279, by rfl⟩ : syracuseStep 703039 = 1054559) B1054559
theorem B277063 : Blo 275825 277063 := bstep (se 1 (by rfl) ⟨207797, by rfl⟩ : syracuseStep 277063 = 415595) B415595
theorem B1686089 : Blo 275825 1686089 := bstep (se 2 (by rfl) ⟨632283, by rfl⟩ : syracuseStep 1686089 = 1264567) B1264567
theorem B703151 : Blo 275825 703151 := bstep (se 1 (by rfl) ⟨527363, by rfl⟩ : syracuseStep 703151 = 1054727) B1054727
theorem B277215 : Blo 275825 277215 := bstep (se 1 (by rfl) ⟨207911, by rfl⟩ : syracuseStep 277215 = 415823) B415823
theorem B277295 : Blo 275825 277295 := bstep (se 1 (by rfl) ⟨207971, by rfl⟩ : syracuseStep 277295 = 415943) B415943
theorem B277403 : Blo 275825 277403 := bstep (se 1 (by rfl) ⟨208052, by rfl⟩ : syracuseStep 277403 = 416105) B416105
theorem B277455 : Blo 275825 277455 := bstep (se 1 (by rfl) ⟨208091, by rfl⟩ : syracuseStep 277455 = 416183) B416183
theorem B277479 : Blo 275825 277479 := bstep (se 1 (by rfl) ⟨208109, by rfl⟩ : syracuseStep 277479 = 416219) B416219
theorem B703475 : Blo 275825 703475 := bstep (se 1 (by rfl) ⟨527606, by rfl⟩ : syracuseStep 703475 = 1055213) B1055213
theorem B6011927 : Blo 275825 6011927 := bstep (se 1 (by rfl) ⟨4508945, by rfl⟩ : syracuseStep 6011927 = 9017891) B9017891
theorem B932903 : Blo 275825 932903 := bstep (se 1 (by rfl) ⟨699677, by rfl⟩ : syracuseStep 932903 = 1399355) B1399355
theorem B703687 : Blo 275825 703687 := bstep (se 1 (by rfl) ⟨527765, by rfl⟩ : syracuseStep 703687 = 1055531) B1055531
theorem B277791 : Blo 275825 277791 := bstep (se 1 (by rfl) ⟨208343, by rfl⟩ : syracuseStep 277791 = 416687) B416687
theorem B310567 : Blo 275825 310567 := bstep (se 1 (by rfl) ⟨232925, by rfl⟩ : syracuseStep 310567 = 465851) B465851
theorem B277851 : Blo 275825 277851 := bstep (se 1 (by rfl) ⟨208388, by rfl⟩ : syracuseStep 277851 = 416777) B416777
theorem B310639 : Blo 275825 310639 := bstep (se 1 (by rfl) ⟨232979, by rfl⟩ : syracuseStep 310639 = 465959) B465959
theorem B277871 : Blo 275825 277871 := bstep (se 1 (by rfl) ⟨208403, by rfl⟩ : syracuseStep 277871 = 416807) B416807
theorem B277927 : Blo 275825 277927 := bstep (se 1 (by rfl) ⟨208445, by rfl⟩ : syracuseStep 277927 = 416891) B416891
theorem B933335 : Blo 275825 933335 := bstep (se 1 (by rfl) ⟨700001, by rfl⟩ : syracuseStep 933335 = 1400003) B1400003
theorem B998905 : Blo 275825 998905 := bstep (se 2 (by rfl) ⟨374589, by rfl⟩ : syracuseStep 998905 = 749179) B749179
theorem B278011 : Blo 275825 278011 := bstep (se 1 (by rfl) ⟨208508, by rfl⟩ : syracuseStep 278011 = 417017) B417017
theorem B2866747 : Blo 275825 2866747 := bstep (se 1 (by rfl) ⟨2150060, by rfl⟩ : syracuseStep 2866747 = 4300121) B4300121
theorem B278079 : Blo 275825 278079 := bstep (se 1 (by rfl) ⟨208559, by rfl⟩ : syracuseStep 278079 = 417119) B417119
theorem B310855 : Blo 275825 310855 := bstep (se 1 (by rfl) ⟨233141, by rfl⟩ : syracuseStep 310855 = 466283) B466283
theorem B278087 : Blo 275825 278087 := bstep (se 1 (by rfl) ⟨208565, by rfl⟩ : syracuseStep 278087 = 417131) B417131
theorem B278239 : Blo 275825 278239 := bstep (se 1 (by rfl) ⟨208679, by rfl⟩ : syracuseStep 278239 = 417359) B417359
theorem B999209 : Blo 275825 999209 := bstep (se 2 (by rfl) ⟨374703, by rfl⟩ : syracuseStep 999209 = 749407) B749407
theorem B1130287 : Blo 275825 1130287 := bstep (se 1 (by rfl) ⟨847715, by rfl⟩ : syracuseStep 1130287 = 1695431) B1695431
theorem B278319 : Blo 275825 278319 := bstep (se 1 (by rfl) ⟨208739, by rfl⟩ : syracuseStep 278319 = 417479) B417479
theorem B278427 : Blo 275825 278427 := bstep (se 1 (by rfl) ⟨208820, by rfl⟩ : syracuseStep 278427 = 417641) B417641
theorem B278479 : Blo 275825 278479 := bstep (se 1 (by rfl) ⟨208859, by rfl⟩ : syracuseStep 278479 = 417719) B417719
theorem B278503 : Blo 275825 278503 := bstep (se 1 (by rfl) ⟨208877, by rfl⟩ : syracuseStep 278503 = 417755) B417755
theorem B278815 : Blo 275825 278815 := bstep (se 1 (by rfl) ⟨209111, by rfl⟩ : syracuseStep 278815 = 418223) B418223
theorem B278875 : Blo 275825 278875 := bstep (se 1 (by rfl) ⟨209156, by rfl⟩ : syracuseStep 278875 = 418313) B418313
theorem B278895 : Blo 275825 278895 := bstep (se 1 (by rfl) ⟨209171, by rfl⟩ : syracuseStep 278895 = 418343) B418343
theorem B311719 : Blo 275825 311719 := bstep (se 1 (by rfl) ⟨233789, by rfl⟩ : syracuseStep 311719 = 467579) B467579
theorem B278951 : Blo 275825 278951 := bstep (se 1 (by rfl) ⟨209213, by rfl⟩ : syracuseStep 278951 = 418427) B418427
theorem B377255 : Blo 275825 377255 := bstep (se 1 (by rfl) ⟨282941, by rfl⟩ : syracuseStep 377255 = 565883) B565883
theorem B1425883 : Blo 275825 1425883 := bstep (se 1 (by rfl) ⟨1069412, by rfl⟩ : syracuseStep 1425883 = 2138825) B2138825
theorem B279035 : Blo 275825 279035 := bstep (se 1 (by rfl) ⟨209276, by rfl⟩ : syracuseStep 279035 = 418553) B418553
theorem B1065473 : Blo 275825 1065473 := bstep (se 2 (by rfl) ⟨399552, by rfl⟩ : syracuseStep 1065473 = 799105) B799105
theorem B279103 : Blo 275825 279103 := bstep (se 1 (by rfl) ⟨209327, by rfl⟩ : syracuseStep 279103 = 418655) B418655
theorem B705095 : Blo 275825 705095 := bstep (se 1 (by rfl) ⟨528821, by rfl⟩ : syracuseStep 705095 = 1057643) B1057643
theorem B279111 : Blo 275825 279111 := bstep (se 1 (by rfl) ⟨209333, by rfl⟩ : syracuseStep 279111 = 418667) B418667
theorem B705145 : Blo 275825 705145 := bstep (se 2 (by rfl) ⟨264429, by rfl⟩ : syracuseStep 705145 = 528859) B528859
theorem B1491655 : Blo 275825 1491655 := bstep (se 1 (by rfl) ⟨1118741, by rfl⟩ : syracuseStep 1491655 = 2237483) B2237483
theorem B279263 : Blo 275825 279263 := bstep (se 1 (by rfl) ⟨209447, by rfl⟩ : syracuseStep 279263 = 418895) B418895
theorem B279343 : Blo 275825 279343 := bstep (se 1 (by rfl) ⟨209507, by rfl⟩ : syracuseStep 279343 = 419015) B419015
theorem B279451 : Blo 275825 279451 := bstep (se 1 (by rfl) ⟨209588, by rfl⟩ : syracuseStep 279451 = 419177) B419177
theorem B279503 : Blo 275825 279503 := bstep (se 1 (by rfl) ⟨209627, by rfl⟩ : syracuseStep 279503 = 419255) B419255
theorem B312295 : Blo 275825 312295 := bstep (se 1 (by rfl) ⟨234221, by rfl⟩ : syracuseStep 312295 = 468443) B468443
theorem B279527 : Blo 275825 279527 := bstep (se 1 (by rfl) ⟨209645, by rfl⟩ : syracuseStep 279527 = 419291) B419291
theorem B935009 : Blo 275825 935009 := bstep (se 2 (by rfl) ⟨350628, by rfl⟩ : syracuseStep 935009 = 701257) B701257
theorem B1262891 : Blo 275825 1262891 := bstep (se 1 (by rfl) ⟨947168, by rfl⟩ : syracuseStep 1262891 = 1894337) B1894337
theorem B21677357 : Blo 275825 21677357 := bstep (se 3 (by rfl) ⟨4064504, by rfl⟩ : syracuseStep 21677357 = 8129009) B8129009
theorem B2377133 : Blo 275825 2377133 := bstep (se 3 (by rfl) ⟨445712, by rfl⟩ : syracuseStep 2377133 = 891425) B891425
theorem B1001297 : Blo 275825 1001297 := bstep (se 2 (by rfl) ⟨375486, by rfl⟩ : syracuseStep 1001297 = 750973) B750973
theorem B6408143 : Blo 275825 6408143 := bstep (se 1 (by rfl) ⟨4806107, by rfl⟩ : syracuseStep 6408143 = 9612215) B9612215
theorem B706907 : Blo 275825 706907 := bstep (se 1 (by rfl) ⟨530180, by rfl⟩ : syracuseStep 706907 = 1060361) B1060361
theorem B706927 : Blo 275825 706927 := bstep (se 1 (by rfl) ⟨530195, by rfl⟩ : syracuseStep 706927 = 1060391) B1060391
theorem B936359 : Blo 275825 936359 := bstep (se 1 (by rfl) ⟨702269, by rfl⟩ : syracuseStep 936359 = 1404539) B1404539
theorem B936521 : Blo 275825 936521 := bstep (se 2 (by rfl) ⟨351195, by rfl⟩ : syracuseStep 936521 = 702391) B702391
theorem B313951 : Blo 275825 313951 := bstep (se 1 (by rfl) ⟨235463, by rfl⟩ : syracuseStep 313951 = 470927) B470927
theorem B1002091 : Blo 275825 1002091 := bstep (se 1 (by rfl) ⟨751568, by rfl⟩ : syracuseStep 1002091 = 1503137) B1503137
theorem B1002365 : Blo 275825 1002365 := bstep (se 3 (by rfl) ⟨187943, by rfl⟩ : syracuseStep 1002365 = 375887) B375887
theorem B1493903 : Blo 275825 1493903 := bstep (se 1 (by rfl) ⟨1120427, by rfl⟩ : syracuseStep 1493903 = 2240855) B2240855
theorem B707575 : Blo 275825 707575 := bstep (se 1 (by rfl) ⟨530681, by rfl⟩ : syracuseStep 707575 = 1061363) B1061363
theorem B707879 : Blo 275825 707879 := bstep (se 1 (by rfl) ⟨530909, by rfl⟩ : syracuseStep 707879 = 1061819) B1061819
theorem B4017761 : Blo 275825 4017761 := bstep (se 2 (by rfl) ⟨1506660, by rfl⟩ : syracuseStep 4017761 = 3013321) B3013321
theorem B3002159 : Blo 275825 3002159 := bstep (se 1 (by rfl) ⟨2251619, by rfl⟩ : syracuseStep 3002159 = 4503239) B4503239
theorem B1265665 : Blo 275825 1265665 := bstep (se 2 (by rfl) ⟨474624, by rfl⟩ : syracuseStep 1265665 = 949249) B949249
theorem B413801 : Blo 275825 413801 := bstep (se 2 (by rfl) ⟨155175, by rfl⟩ : syracuseStep 413801 = 310351) B310351
theorem B938195 : Blo 275825 938195 := bstep (se 1 (by rfl) ⟨703646, by rfl⟩ : syracuseStep 938195 = 1407293) B1407293
theorem B381223 : Blo 275825 381223 := bstep (se 1 (by rfl) ⟨285917, by rfl⟩ : syracuseStep 381223 = 571835) B571835
theorem B414119 : Blo 275825 414119 := bstep (se 1 (by rfl) ⟨310589, by rfl⟩ : syracuseStep 414119 = 621179) B621179
theorem B938465 : Blo 275825 938465 := bstep (se 2 (by rfl) ⟨351924, by rfl⟩ : syracuseStep 938465 = 703849) B703849
theorem B414203 : Blo 275825 414203 := bstep (se 1 (by rfl) ⟨310652, by rfl⟩ : syracuseStep 414203 = 621305) B621305
theorem B1397249 : Blo 275825 1397249 := bstep (se 2 (by rfl) ⟨523968, by rfl⟩ : syracuseStep 1397249 = 1047937) B1047937
theorem B414329 : Blo 275825 414329 := bstep (se 2 (by rfl) ⟨155373, by rfl⟩ : syracuseStep 414329 = 310747) B310747
theorem B414383 : Blo 275825 414383 := bstep (se 1 (by rfl) ⟨310787, by rfl⟩ : syracuseStep 414383 = 621575) B621575
theorem B414431 : Blo 275825 414431 := bstep (se 1 (by rfl) ⟨310823, by rfl⟩ : syracuseStep 414431 = 621647) B621647
theorem B1397735 : Blo 275825 1397735 := bstep (se 1 (by rfl) ⟨1048301, by rfl⟩ : syracuseStep 1397735 = 2096603) B2096603
theorem B414695 : Blo 275825 414695 := bstep (se 1 (by rfl) ⟨311021, by rfl⟩ : syracuseStep 414695 = 622043) B622043
theorem B5690387 : Blo 275825 5690387 := bstep (se 1 (by rfl) ⟨4267790, by rfl⟩ : syracuseStep 5690387 = 8535581) B8535581
theorem B414953 : Blo 275825 414953 := bstep (se 2 (by rfl) ⟨155607, by rfl⟩ : syracuseStep 414953 = 311215) B311215
theorem B415007 : Blo 275825 415007 := bstep (se 1 (by rfl) ⟨311255, by rfl⟩ : syracuseStep 415007 = 622511) B622511
theorem B1398059 : Blo 275825 1398059 := bstep (se 1 (by rfl) ⟨1048544, by rfl⟩ : syracuseStep 1398059 = 2097089) B2097089
theorem B23287175 : Blo 275825 23287175 := bstep (se 1 (by rfl) ⟨17465381, by rfl⟩ : syracuseStep 23287175 = 34930763) B34930763
theorem B841099 : Blo 275825 841099 := bstep (se 1 (by rfl) ⟨630824, by rfl⟩ : syracuseStep 841099 = 1261649) B1261649
theorem B415175 : Blo 275825 415175 := bstep (se 1 (by rfl) ⟨311381, by rfl⟩ : syracuseStep 415175 = 622763) B622763
theorem B939707 : Blo 275825 939707 := bstep (se 1 (by rfl) ⟨704780, by rfl⟩ : syracuseStep 939707 = 1409561) B1409561
theorem B415529 : Blo 275825 415529 := bstep (se 2 (by rfl) ⟨155823, by rfl⟩ : syracuseStep 415529 = 311647) B311647
theorem B415535 : Blo 275825 415535 := bstep (se 1 (by rfl) ⟨311651, by rfl⟩ : syracuseStep 415535 = 623303) B623303
theorem B1791973 : Blo 275825 1791973 := bstep (se 4 (by rfl) ⟨167997, by rfl⟩ : syracuseStep 1791973 = 335995) B335995
theorem B350183 : Blo 275825 350183 := bstep (se 1 (by rfl) ⟨262637, by rfl⟩ : syracuseStep 350183 = 525275) B525275
theorem B1399031 : Blo 275825 1399031 := bstep (se 1 (by rfl) ⟨1049273, by rfl⟩ : syracuseStep 1399031 = 2098547) B2098547
theorem B416009 : Blo 275825 416009 := bstep (se 2 (by rfl) ⟨156003, by rfl⟩ : syracuseStep 416009 = 312007) B312007
theorem B645385 : Blo 275825 645385 := bstep (se 2 (by rfl) ⟨242019, by rfl⟩ : syracuseStep 645385 = 484039) B484039
theorem B1005853 : Blo 275825 1005853 := bstep (se 3 (by rfl) ⟨188597, by rfl⟩ : syracuseStep 1005853 = 377195) B377195
theorem B416111 : Blo 275825 416111 := bstep (se 1 (by rfl) ⟨312083, by rfl⟩ : syracuseStep 416111 = 624167) B624167
theorem B416327 : Blo 275825 416327 := bstep (se 1 (by rfl) ⟨312245, by rfl⟩ : syracuseStep 416327 = 624491) B624491
theorem B416363 : Blo 275825 416363 := bstep (se 1 (by rfl) ⟨312272, by rfl⟩ : syracuseStep 416363 = 624545) B624545
theorem B1399517 : Blo 275825 1399517 := bstep (se 3 (by rfl) ⟨262409, by rfl⟩ : syracuseStep 1399517 = 524819) B524819
theorem B416591 : Blo 275825 416591 := bstep (se 1 (by rfl) ⟨312443, by rfl⟩ : syracuseStep 416591 = 624887) B624887
theorem B416987 : Blo 275825 416987 := bstep (se 1 (by rfl) ⟨312740, by rfl⟩ : syracuseStep 416987 = 625481) B625481
theorem B417161 : Blo 275825 417161 := bstep (se 2 (by rfl) ⟨156435, by rfl⟩ : syracuseStep 417161 = 312871) B312871
theorem B1007063 : Blo 275825 1007063 := bstep (se 1 (by rfl) ⟨755297, by rfl⟩ : syracuseStep 1007063 = 1510595) B1510595
theorem B941651 : Blo 275825 941651 := bstep (se 1 (by rfl) ⟨706238, by rfl⟩ : syracuseStep 941651 = 1412477) B1412477
theorem B417515 : Blo 275825 417515 := bstep (se 1 (by rfl) ⟨313136, by rfl⟩ : syracuseStep 417515 = 626273) B626273
theorem B21520247 : Blo 275825 21520247 := bstep (se 1 (by rfl) ⟨16140185, by rfl⟩ : syracuseStep 21520247 = 32280371) B32280371
theorem B417743 : Blo 275825 417743 := bstep (se 1 (by rfl) ⟨313307, by rfl⟩ : syracuseStep 417743 = 626615) B626615
theorem B1269785 : Blo 275825 1269785 := bstep (se 2 (by rfl) ⟨476169, by rfl⟩ : syracuseStep 1269785 = 952339) B952339
theorem B5988401 : Blo 275825 5988401 := bstep (se 2 (by rfl) ⟨2245650, by rfl⟩ : syracuseStep 5988401 = 4491301) B4491301
theorem B352603 : Blo 275825 352603 := bstep (se 1 (by rfl) ⟨264452, by rfl⟩ : syracuseStep 352603 = 528905) B528905
theorem B418139 : Blo 275825 418139 := bstep (se 1 (by rfl) ⟨313604, by rfl⟩ : syracuseStep 418139 = 627209) B627209
theorem B352831 : Blo 275825 352831 := bstep (se 1 (by rfl) ⟨264623, by rfl⟩ : syracuseStep 352831 = 529247) B529247
theorem B418367 : Blo 275825 418367 := bstep (se 1 (by rfl) ⟨313775, by rfl⟩ : syracuseStep 418367 = 627551) B627551
theorem B7955009 : Blo 275825 7955009 := bstep (se 2 (by rfl) ⟨2983128, by rfl⟩ : syracuseStep 7955009 = 5966257) B5966257
theorem B418487 : Blo 275825 418487 := bstep (se 1 (by rfl) ⟨313865, by rfl⟩ : syracuseStep 418487 = 627731) B627731
theorem B418715 : Blo 275825 418715 := bstep (se 1 (by rfl) ⟨314036, by rfl⟩ : syracuseStep 418715 = 628073) B628073
theorem B1532903 : Blo 275825 1532903 := bstep (se 1 (by rfl) ⟨1149677, by rfl⟩ : syracuseStep 1532903 = 2299355) B2299355
theorem B648425 : Blo 275825 648425 := bstep (se 2 (by rfl) ⟨243159, by rfl⟩ : syracuseStep 648425 = 486319) B486319
theorem B353575 : Blo 275825 353575 := bstep (se 1 (by rfl) ⟨265181, by rfl⟩ : syracuseStep 353575 = 530363) B530363
theorem B419111 : Blo 275825 419111 := bstep (se 1 (by rfl) ⟨314333, by rfl⟩ : syracuseStep 419111 = 628667) B628667
theorem B419195 : Blo 275825 419195 := bstep (se 1 (by rfl) ⟨314396, by rfl⟩ : syracuseStep 419195 = 628793) B628793
theorem B419321 : Blo 275825 419321 := bstep (se 2 (by rfl) ⟨157245, by rfl⟩ : syracuseStep 419321 = 314491) B314491
theorem B419423 : Blo 275825 419423 := bstep (se 1 (by rfl) ⟨314567, by rfl⟩ : syracuseStep 419423 = 629135) B629135
theorem B353899 : Blo 275825 353899 := bstep (se 1 (by rfl) ⟨265424, by rfl⟩ : syracuseStep 353899 = 530849) B530849
theorem B419639 : Blo 275825 419639 := bstep (se 1 (by rfl) ⟨314729, by rfl⟩ : syracuseStep 419639 = 629459) B629459
theorem B354127 : Blo 275825 354127 := bstep (se 1 (by rfl) ⟨265595, by rfl⟩ : syracuseStep 354127 = 531191) B531191
theorem B1403567 : Blo 275825 1403567 := bstep (se 1 (by rfl) ⟨1052675, by rfl⟩ : syracuseStep 1403567 = 2105351) B2105351
theorem B420763 : Blo 275825 420763 := bstep (se 1 (by rfl) ⟨315572, by rfl⟩ : syracuseStep 420763 = 631145) B631145
theorem B1403891 : Blo 275825 1403891 := bstep (se 1 (by rfl) ⟨1052918, by rfl⟩ : syracuseStep 1403891 = 2105837) B2105837
theorem B1338889 : Blo 275825 1338889 := bstep (se 2 (by rfl) ⟨502083, by rfl⟩ : syracuseStep 1338889 = 1004167) B1004167
theorem B749243 : Blo 275825 749243 := bstep (se 1 (by rfl) ⟨561932, by rfl⟩ : syracuseStep 749243 = 1123865) B1123865
theorem B26570753 : Blo 275825 26570753 := bstep (se 2 (by rfl) ⟨9964032, by rfl⟩ : syracuseStep 26570753 = 19928065) B19928065
theorem B1405187 : Blo 275825 1405187 := bstep (se 1 (by rfl) ⟨1053890, by rfl⟩ : syracuseStep 1405187 = 2107781) B2107781
theorem B3207599 : Blo 275825 3207599 := bstep (se 1 (by rfl) ⟨2405699, by rfl⟩ : syracuseStep 3207599 = 4811399) B4811399
theorem B1405511 : Blo 275825 1405511 := bstep (se 1 (by rfl) ⟨1054133, by rfl⟩ : syracuseStep 1405511 = 2108267) B2108267
theorem B1504109 : Blo 275825 1504109 := bstep (se 3 (by rfl) ⟨282020, by rfl⟩ : syracuseStep 1504109 = 564041) B564041
theorem B1209289 : Blo 275825 1209289 := bstep (se 2 (by rfl) ⟨453483, by rfl⟩ : syracuseStep 1209289 = 906967) B906967
theorem B3634301 : Blo 275825 3634301 := bstep (se 3 (by rfl) ⟨681431, by rfl⟩ : syracuseStep 3634301 = 1362863) B1362863
theorem B750791 : Blo 275825 750791 := bstep (se 1 (by rfl) ⟨563093, by rfl⟩ : syracuseStep 750791 = 1126187) B1126187
theorem B947495 : Blo 275825 947495 := bstep (se 1 (by rfl) ⟨710621, by rfl⟩ : syracuseStep 947495 = 1421243) B1421243
theorem B1406807 : Blo 275825 1406807 := bstep (se 1 (by rfl) ⟨1055105, by rfl⟩ : syracuseStep 1406807 = 2110211) B2110211
theorem B620873 : Blo 275825 620873 := bstep (se 2 (by rfl) ⟨232827, by rfl⟩ : syracuseStep 620873 = 465655) B465655
theorem B620891 : Blo 275825 620891 := bstep (se 1 (by rfl) ⟨465668, by rfl⟩ : syracuseStep 620891 = 931337) B931337
theorem B1047451 : Blo 275825 1047451 := bstep (se 1 (by rfl) ⟨785588, by rfl⟩ : syracuseStep 1047451 = 1571177) B1571177
theorem B621467 : Blo 275825 621467 := bstep (se 1 (by rfl) ⟨466100, by rfl⟩ : syracuseStep 621467 = 932201) B932201
theorem B1997723 : Blo 275825 1997723 := bstep (se 1 (by rfl) ⟨1498292, by rfl⟩ : syracuseStep 1997723 = 2996585) B2996585
theorem B2259899 : Blo 275825 2259899 := bstep (se 1 (by rfl) ⟨1694924, by rfl⟩ : syracuseStep 2259899 = 3389849) B3389849
theorem B621665 : Blo 275825 621665 := bstep (se 2 (by rfl) ⟨233124, by rfl⟩ : syracuseStep 621665 = 466249) B466249
theorem B2686115 : Blo 275825 2686115 := bstep (se 1 (by rfl) ⟨2014586, by rfl⟩ : syracuseStep 2686115 = 4029173) B4029173
theorem B621863 : Blo 275825 621863 := bstep (se 1 (by rfl) ⟨466397, by rfl⟩ : syracuseStep 621863 = 932795) B932795
theorem B687455 : Blo 275825 687455 := bstep (se 1 (by rfl) ⟨515591, by rfl⟩ : syracuseStep 687455 = 1031183) B1031183
theorem B1178999 : Blo 275825 1178999 := bstep (se 1 (by rfl) ⟨884249, by rfl⟩ : syracuseStep 1178999 = 1768499) B1768499
theorem B1900025 : Blo 275825 1900025 := bstep (se 2 (by rfl) ⟨712509, by rfl⟩ : syracuseStep 1900025 = 1425019) B1425019
theorem B622241 : Blo 275825 622241 := bstep (se 2 (by rfl) ⟨233340, by rfl⟩ : syracuseStep 622241 = 466681) B466681
theorem B1901177 : Blo 275825 1901177 := bstep (se 2 (by rfl) ⟨712941, by rfl⟩ : syracuseStep 1901177 = 1425883) B1425883
theorem B623339 : Blo 275825 623339 := bstep (se 1 (by rfl) ⟨467504, by rfl⟩ : syracuseStep 623339 = 935009) B935009
theorem B14451571 : Blo 275825 14451571 := bstep (se 1 (by rfl) ⟨10838678, by rfl⟩ : syracuseStep 14451571 = 21677357) B21677357
theorem B1573775 : Blo 275825 1573775 := bstep (se 1 (by rfl) ⟨1180331, by rfl⟩ : syracuseStep 1573775 = 2360663) B2360663
theorem B4719545 : Blo 275825 4719545 := bstep (se 2 (by rfl) ⟨1769829, by rfl⟩ : syracuseStep 4719545 = 3539659) B3539659
theorem B787411 : Blo 275825 787411 := bstep (se 1 (by rfl) ⟨590558, by rfl⟩ : syracuseStep 787411 = 1181117) B1181117
theorem B5342705 : Blo 275825 5342705 := bstep (se 2 (by rfl) ⟨2003514, by rfl⟩ : syracuseStep 5342705 = 4007029) B4007029
theorem B2033189 : Blo 275825 2033189 := bstep (se 4 (by rfl) ⟨190611, by rfl⟩ : syracuseStep 2033189 = 381223) B381223
theorem B624239 : Blo 275825 624239 := bstep (se 1 (by rfl) ⟨468179, by rfl⟩ : syracuseStep 624239 = 936359) B936359
theorem B624347 : Blo 275825 624347 := bstep (se 1 (by rfl) ⟨468260, by rfl⟩ : syracuseStep 624347 = 936521) B936521
theorem B788231 : Blo 275825 788231 := bstep (se 1 (by rfl) ⟨591173, by rfl⟩ : syracuseStep 788231 = 1182347) B1182347
theorem B788255 : Blo 275825 788255 := bstep (se 1 (by rfl) ⟨591191, by rfl⟩ : syracuseStep 788255 = 1182383) B1182383
theorem B1410857 : Blo 275825 1410857 := bstep (se 2 (by rfl) ⟨529071, by rfl⟩ : syracuseStep 1410857 = 1058143) B1058143
theorem B1772063 : Blo 275825 1772063 := bstep (se 1 (by rfl) ⟨1329047, by rfl⟩ : syracuseStep 1772063 = 2658095) B2658095
theorem B2001439 : Blo 275825 2001439 := bstep (se 1 (by rfl) ⟨1501079, by rfl⟩ : syracuseStep 2001439 = 3002159) B3002159
theorem B789097 : Blo 275825 789097 := bstep (se 2 (by rfl) ⟨295911, by rfl⟩ : syracuseStep 789097 = 591823) B591823
theorem B625463 : Blo 275825 625463 := bstep (se 1 (by rfl) ⟨469097, by rfl⟩ : syracuseStep 625463 = 938195) B938195
theorem B625643 : Blo 275825 625643 := bstep (se 1 (by rfl) ⟨469232, by rfl⟩ : syracuseStep 625643 = 938465) B938465
theorem B1576259 : Blo 275825 1576259 := bstep (se 1 (by rfl) ⟨1182194, by rfl⟩ : syracuseStep 1576259 = 2364389) B2364389
theorem B1183099 : Blo 275825 1183099 := bstep (se 1 (by rfl) ⟨887324, by rfl⟩ : syracuseStep 1183099 = 1774649) B1774649
theorem B2526653 : Blo 275825 2526653 := bstep (se 3 (by rfl) ⟨473747, by rfl⟩ : syracuseStep 2526653 = 947495) B947495
theorem B5738165 : Blo 275825 5738165 := bstep (se 5 (by rfl) ⟨268976, by rfl⟩ : syracuseStep 5738165 = 537953) B537953
theorem B626471 : Blo 275825 626471 := bstep (se 1 (by rfl) ⟨469853, by rfl⟩ : syracuseStep 626471 = 939707) B939707
theorem B561017 : Blo 275825 561017 := bstep (se 2 (by rfl) ⟨210381, by rfl⟩ : syracuseStep 561017 = 420763) B420763
theorem B790715 : Blo 275825 790715 := bstep (se 1 (by rfl) ⟨593036, by rfl⟩ : syracuseStep 790715 = 1186073) B1186073
theorem B397801 : Blo 275825 397801 := bstep (se 2 (by rfl) ⟨149175, by rfl⟩ : syracuseStep 397801 = 298351) B298351
theorem B594515 : Blo 275825 594515 := bstep (se 1 (by rfl) ⟨445886, by rfl⟩ : syracuseStep 594515 = 891773) B891773
theorem B529193 : Blo 275825 529193 := bstep (se 2 (by rfl) ⟨198447, by rfl⟩ : syracuseStep 529193 = 396895) B396895
theorem B627497 : Blo 275825 627497 := bstep (se 2 (by rfl) ⟨235311, by rfl⟩ : syracuseStep 627497 = 470623) B470623
theorem B3150737 : Blo 275825 3150737 := bstep (se 2 (by rfl) ⟨1181526, by rfl⟩ : syracuseStep 3150737 = 2363053) B2363053
theorem B1184807 : Blo 275825 1184807 := bstep (se 1 (by rfl) ⟨888605, by rfl⟩ : syracuseStep 1184807 = 1777211) B1777211
theorem B627767 : Blo 275825 627767 := bstep (se 1 (by rfl) ⟨470825, by rfl⟩ : syracuseStep 627767 = 941651) B941651
theorem B627785 : Blo 275825 627785 := bstep (se 2 (by rfl) ⟨235419, by rfl⟩ : syracuseStep 627785 = 470839) B470839
theorem B1054043 : Blo 275825 1054043 := bstep (se 1 (by rfl) ⟨790532, by rfl⟩ : syracuseStep 1054043 = 1581065) B1581065
theorem B1152481 : Blo 275825 1152481 := bstep (se 2 (by rfl) ⟨432180, by rfl⟩ : syracuseStep 1152481 = 864361) B864361
theorem B8984675 : Blo 275825 8984675 := bstep (se 1 (by rfl) ⟨6738506, by rfl⟩ : syracuseStep 8984675 = 13477013) B13477013
theorem B1612385 : Blo 275825 1612385 := bstep (se 2 (by rfl) ⟨604644, by rfl⟩ : syracuseStep 1612385 = 1209289) B1209289
theorem B1710953 : Blo 275825 1710953 := bstep (se 2 (by rfl) ⟨641607, by rfl⟩ : syracuseStep 1710953 = 1283215) B1283215
theorem B1416041 : Blo 275825 1416041 := bstep (se 2 (by rfl) ⟨531015, by rfl⟩ : syracuseStep 1416041 = 1062031) B1062031
theorem B465871 : Blo 275825 465871 := bstep (se 1 (by rfl) ⟨349403, by rfl⟩ : syracuseStep 465871 = 698807) B698807
theorem B1055713 : Blo 275825 1055713 := bstep (se 2 (by rfl) ⟨395892, by rfl⟩ : syracuseStep 1055713 = 791785) B791785
theorem B1121465 : Blo 275825 1121465 := bstep (se 2 (by rfl) ⟨420549, by rfl⟩ : syracuseStep 1121465 = 841099) B841099
theorem B662995 : Blo 275825 662995 := bstep (se 1 (by rfl) ⟨497246, by rfl⟩ : syracuseStep 662995 = 994493) B994493
theorem B794087 : Blo 275825 794087 := bstep (se 1 (by rfl) ⟨595565, by rfl⟩ : syracuseStep 794087 = 1191131) B1191131
theorem B23076427 : Blo 275825 23076427 := bstep (se 1 (by rfl) ⟨17307320, by rfl⟩ : syracuseStep 23076427 = 34614641) B34614641
theorem B466607 : Blo 275825 466607 := bstep (se 1 (by rfl) ⟨349955, by rfl⟩ : syracuseStep 466607 = 699911) B699911
theorem B499495 : Blo 275825 499495 := bstep (se 1 (by rfl) ⟨374621, by rfl⟩ : syracuseStep 499495 = 749243) B749243
theorem B466843 : Blo 275825 466843 := bstep (se 1 (by rfl) ⟨350132, by rfl⟩ : syracuseStep 466843 = 700265) B700265
theorem B2138399 : Blo 275825 2138399 := bstep (se 1 (by rfl) ⟨1603799, by rfl⟩ : syracuseStep 2138399 = 3207599) B3207599
theorem B467255 : Blo 275825 467255 := bstep (se 1 (by rfl) ⟨350441, by rfl⟩ : syracuseStep 467255 = 700883) B700883
theorem B860513 : Blo 275825 860513 := bstep (se 2 (by rfl) ⟨322692, by rfl⟩ : syracuseStep 860513 = 645385) B645385
theorem B1909111 : Blo 275825 1909111 := bstep (se 1 (by rfl) ⟨1431833, by rfl⟩ : syracuseStep 1909111 = 2863667) B2863667
theorem B1778237 : Blo 275825 1778237 := bstep (se 3 (by rfl) ⟨333419, by rfl⟩ : syracuseStep 1778237 = 666839) B666839
theorem B500527 : Blo 275825 500527 := bstep (se 1 (by rfl) ⟨375395, by rfl⟩ : syracuseStep 500527 = 750791) B750791
theorem B468031 : Blo 275825 468031 := bstep (se 1 (by rfl) ⟨351023, by rfl⟩ : syracuseStep 468031 = 702047) B702047
theorem B795977 : Blo 275825 795977 := bstep (se 2 (by rfl) ⟨298491, by rfl⟩ : syracuseStep 795977 = 596983) B596983
theorem B468551 : Blo 275825 468551 := bstep (se 1 (by rfl) ⟨351413, by rfl⟩ : syracuseStep 468551 = 702827) B702827
theorem B1124059 : Blo 275825 1124059 := bstep (se 1 (by rfl) ⟨843044, by rfl⟩ : syracuseStep 1124059 = 1686089) B1686089
theorem B468767 : Blo 275825 468767 := bstep (se 1 (by rfl) ⟨351575, by rfl⟩ : syracuseStep 468767 = 703151) B703151
theorem B796513 : Blo 275825 796513 := bstep (se 2 (by rfl) ⟨298692, by rfl⟩ : syracuseStep 796513 = 597385) B597385
theorem B468983 : Blo 275825 468983 := bstep (se 1 (by rfl) ⟨351737, by rfl⟩ : syracuseStep 468983 = 703475) B703475
theorem B4007951 : Blo 275825 4007951 := bstep (se 1 (by rfl) ⟨3005963, by rfl⟩ : syracuseStep 4007951 = 6011927) B6011927
theorem B57387325 : Blo 275825 57387325 := bstep (se 3 (by rfl) ⟨10760123, by rfl⟩ : syracuseStep 57387325 = 21520247) B21520247
theorem B666139 : Blo 275825 666139 := bstep (se 1 (by rfl) ⟨499604, by rfl⟩ : syracuseStep 666139 = 999209) B999209
theorem B470063 : Blo 275825 470063 := bstep (se 1 (by rfl) ⟨352547, by rfl⟩ : syracuseStep 470063 = 705095) B705095
theorem B470137 : Blo 275825 470137 := bstep (se 2 (by rfl) ⟨176301, by rfl⟩ : syracuseStep 470137 = 352603) B352603
theorem B1060073 : Blo 275825 1060073 := bstep (se 2 (by rfl) ⟨397527, by rfl⟩ : syracuseStep 1060073 = 795055) B795055
theorem B470441 : Blo 275825 470441 := bstep (se 2 (by rfl) ⟨176415, by rfl⟩ : syracuseStep 470441 = 352831) B352831
theorem B1584755 : Blo 275825 1584755 := bstep (se 1 (by rfl) ⟨1188566, by rfl⟩ : syracuseStep 1584755 = 2377133) B2377133
theorem B667531 : Blo 275825 667531 := bstep (se 1 (by rfl) ⟨500648, by rfl⟩ : syracuseStep 667531 = 1001297) B1001297
theorem B4272095 : Blo 275825 4272095 := bstep (se 1 (by rfl) ⟨3204071, by rfl⟩ : syracuseStep 4272095 = 6408143) B6408143
theorem B471271 : Blo 275825 471271 := bstep (se 1 (by rfl) ⟨353453, by rfl⟩ : syracuseStep 471271 = 706907) B706907
theorem B536969 : Blo 275825 536969 := bstep (se 2 (by rfl) ⟨201363, by rfl⟩ : syracuseStep 536969 = 402727) B402727
theorem B471433 : Blo 275825 471433 := bstep (se 2 (by rfl) ⟨176787, by rfl⟩ : syracuseStep 471433 = 353575) B353575
theorem B8532377 : Blo 275825 8532377 := bstep (se 2 (by rfl) ⟨3199641, by rfl⟩ : syracuseStep 8532377 = 6399283) B6399283
theorem B668243 : Blo 275825 668243 := bstep (se 1 (by rfl) ⟨501182, by rfl⟩ : syracuseStep 668243 = 1002365) B1002365
theorem B995935 : Blo 275825 995935 := bstep (se 1 (by rfl) ⟨746951, by rfl⟩ : syracuseStep 995935 = 1493903) B1493903
theorem B471865 : Blo 275825 471865 := bstep (se 2 (by rfl) ⟨176949, by rfl⟩ : syracuseStep 471865 = 353899) B353899
theorem B471919 : Blo 275825 471919 := bstep (se 1 (by rfl) ⟨353939, by rfl⟩ : syracuseStep 471919 = 707879) B707879
theorem B3388331 : Blo 275825 3388331 := bstep (se 1 (by rfl) ⟨2541248, by rfl⟩ : syracuseStep 3388331 = 5082497) B5082497
theorem B4010957 : Blo 275825 4010957 := bstep (se 3 (by rfl) ⟨752054, by rfl⟩ : syracuseStep 4010957 = 1504109) B1504109
theorem B1586213 : Blo 275825 1586213 := bstep (se 4 (by rfl) ⟨148707, by rfl⟩ : syracuseStep 1586213 = 297415) B297415
theorem B472169 : Blo 275825 472169 := bstep (se 2 (by rfl) ⟨177063, by rfl⟩ : syracuseStep 472169 = 354127) B354127
theorem B275867 : Blo 275825 275867 := bstep (se 1 (by rfl) ⟨206900, by rfl⟩ : syracuseStep 275867 = 413801) B413801
theorem B276079 : Blo 275825 276079 := bstep (se 1 (by rfl) ⟨207059, by rfl⟩ : syracuseStep 276079 = 414119) B414119
theorem B276135 : Blo 275825 276135 := bstep (se 1 (by rfl) ⟨207101, by rfl⟩ : syracuseStep 276135 = 414203) B414203
theorem B931499 : Blo 275825 931499 := bstep (se 1 (by rfl) ⟨698624, by rfl⟩ : syracuseStep 931499 = 1397249) B1397249
theorem B1586897 : Blo 275825 1586897 := bstep (se 2 (by rfl) ⟨595086, by rfl⟩ : syracuseStep 1586897 = 1190173) B1190173
theorem B276219 : Blo 275825 276219 := bstep (se 1 (by rfl) ⟨207164, by rfl⟩ : syracuseStep 276219 = 414329) B414329
theorem B276255 : Blo 275825 276255 := bstep (se 1 (by rfl) ⟨207191, by rfl⟩ : syracuseStep 276255 = 414383) B414383
theorem B276287 : Blo 275825 276287 := bstep (se 1 (by rfl) ⟨207215, by rfl⟩ : syracuseStep 276287 = 414431) B414431
theorem B931823 : Blo 275825 931823 := bstep (se 1 (by rfl) ⟨698867, by rfl⟩ : syracuseStep 931823 = 1397735) B1397735
theorem B276463 : Blo 275825 276463 := bstep (se 1 (by rfl) ⟨207347, by rfl⟩ : syracuseStep 276463 = 414695) B414695
theorem B276635 : Blo 275825 276635 := bstep (se 1 (by rfl) ⟨207476, by rfl⟩ : syracuseStep 276635 = 414953) B414953
theorem B276671 : Blo 275825 276671 := bstep (se 1 (by rfl) ⟨207503, by rfl⟩ : syracuseStep 276671 = 415007) B415007
theorem B932039 : Blo 275825 932039 := bstep (se 1 (by rfl) ⟨699029, by rfl⟩ : syracuseStep 932039 = 1398059) B1398059
theorem B276783 : Blo 275825 276783 := bstep (se 1 (by rfl) ⟨207587, by rfl⟩ : syracuseStep 276783 = 415175) B415175
theorem B277019 : Blo 275825 277019 := bstep (se 1 (by rfl) ⟨207764, by rfl⟩ : syracuseStep 277019 = 415529) B415529
theorem B277023 : Blo 275825 277023 := bstep (se 1 (by rfl) ⟨207767, by rfl⟩ : syracuseStep 277023 = 415535) B415535
theorem B932687 : Blo 275825 932687 := bstep (se 1 (by rfl) ⟨699515, by rfl⟩ : syracuseStep 932687 = 1399031) B1399031
theorem B277339 : Blo 275825 277339 := bstep (se 1 (by rfl) ⟨208004, by rfl⟩ : syracuseStep 277339 = 416009) B416009
theorem B637787 : Blo 275825 637787 := bstep (se 1 (by rfl) ⟨478340, by rfl⟩ : syracuseStep 637787 = 956681) B956681
theorem B277407 : Blo 275825 277407 := bstep (se 1 (by rfl) ⟨208055, by rfl⟩ : syracuseStep 277407 = 416111) B416111
theorem B277551 : Blo 275825 277551 := bstep (se 1 (by rfl) ⟨208163, by rfl⟩ : syracuseStep 277551 = 416327) B416327
theorem B277575 : Blo 275825 277575 := bstep (se 1 (by rfl) ⟨208181, by rfl⟩ : syracuseStep 277575 = 416363) B416363
theorem B2112641 : Blo 275825 2112641 := bstep (se 2 (by rfl) ⟨792240, by rfl⟩ : syracuseStep 2112641 = 1584481) B1584481
theorem B933011 : Blo 275825 933011 := bstep (se 1 (by rfl) ⟨699758, by rfl⟩ : syracuseStep 933011 = 1399517) B1399517
theorem B310495 : Blo 275825 310495 := bstep (se 1 (by rfl) ⟨232871, by rfl⟩ : syracuseStep 310495 = 465743) B465743
theorem B277727 : Blo 275825 277727 := bstep (se 1 (by rfl) ⟨208295, by rfl⟩ : syracuseStep 277727 = 416591) B416591
theorem B10894657 : Blo 275825 10894657 := bstep (se 2 (by rfl) ⟨4085496, by rfl⟩ : syracuseStep 10894657 = 8170993) B8170993
theorem B1785185 : Blo 275825 1785185 := bstep (se 2 (by rfl) ⟨669444, by rfl⟩ : syracuseStep 1785185 = 1338889) B1338889
theorem B933281 : Blo 275825 933281 := bstep (se 2 (by rfl) ⟨349980, by rfl⟩ : syracuseStep 933281 = 699961) B699961
theorem B1588673 : Blo 275825 1588673 := bstep (se 2 (by rfl) ⟨595752, by rfl⟩ : syracuseStep 1588673 = 1191505) B1191505
theorem B277991 : Blo 275825 277991 := bstep (se 1 (by rfl) ⟨208493, by rfl⟩ : syracuseStep 277991 = 416987) B416987
theorem B278107 : Blo 275825 278107 := bstep (se 1 (by rfl) ⟨208580, by rfl⟩ : syracuseStep 278107 = 417161) B417161
theorem B671375 : Blo 275825 671375 := bstep (se 1 (by rfl) ⟨503531, by rfl⟩ : syracuseStep 671375 = 1007063) B1007063
theorem B278343 : Blo 275825 278343 := bstep (se 1 (by rfl) ⟨208757, by rfl⟩ : syracuseStep 278343 = 417515) B417515
theorem B933821 : Blo 275825 933821 := bstep (se 3 (by rfl) ⟨175091, by rfl⟩ : syracuseStep 933821 = 350183) B350183
theorem B278495 : Blo 275825 278495 := bstep (se 1 (by rfl) ⟨208871, by rfl⟩ : syracuseStep 278495 = 417743) B417743
theorem B1687553 : Blo 275825 1687553 := bstep (se 2 (by rfl) ⟨632832, by rfl⟩ : syracuseStep 1687553 = 1265665) B1265665
theorem B278759 : Blo 275825 278759 := bstep (se 1 (by rfl) ⟨209069, by rfl⟩ : syracuseStep 278759 = 418139) B418139
theorem B278911 : Blo 275825 278911 := bstep (se 1 (by rfl) ⟨209183, by rfl⟩ : syracuseStep 278911 = 418367) B418367
theorem B278991 : Blo 275825 278991 := bstep (se 1 (by rfl) ⟨209243, by rfl⟩ : syracuseStep 278991 = 418487) B418487
theorem B1622591 : Blo 275825 1622591 := bstep (se 1 (by rfl) ⟨1216943, by rfl⟩ : syracuseStep 1622591 = 2433887) B2433887
theorem B279143 : Blo 275825 279143 := bstep (se 1 (by rfl) ⟨209357, by rfl⟩ : syracuseStep 279143 = 418715) B418715
theorem B279407 : Blo 275825 279407 := bstep (se 1 (by rfl) ⟨209555, by rfl⟩ : syracuseStep 279407 = 419111) B419111
theorem B279463 : Blo 275825 279463 := bstep (se 1 (by rfl) ⟨209597, by rfl⟩ : syracuseStep 279463 = 419195) B419195
theorem B279547 : Blo 275825 279547 := bstep (se 1 (by rfl) ⟨209660, by rfl⟩ : syracuseStep 279547 = 419321) B419321
theorem B279615 : Blo 275825 279615 := bstep (se 1 (by rfl) ⟨209711, by rfl⟩ : syracuseStep 279615 = 419423) B419423
theorem B705743 : Blo 275825 705743 := bstep (se 1 (by rfl) ⟨529307, by rfl⟩ : syracuseStep 705743 = 1058615) B1058615
theorem B279759 : Blo 275825 279759 := bstep (se 1 (by rfl) ⟨209819, by rfl⟩ : syracuseStep 279759 = 419639) B419639
theorem B706067 : Blo 275825 706067 := bstep (se 1 (by rfl) ⟨529550, by rfl⟩ : syracuseStep 706067 = 1059101) B1059101
theorem B312943 : Blo 275825 312943 := bstep (se 1 (by rfl) ⟨234707, by rfl⟩ : syracuseStep 312943 = 469415) B469415
theorem B313051 : Blo 275825 313051 := bstep (se 1 (by rfl) ⟨234788, by rfl⟩ : syracuseStep 313051 = 469577) B469577
theorem B935711 : Blo 275825 935711 := bstep (se 1 (by rfl) ⟨701783, by rfl⟩ : syracuseStep 935711 = 1403567) B1403567
theorem B2115557 : Blo 275825 2115557 := bstep (se 4 (by rfl) ⟨198333, by rfl⟩ : syracuseStep 2115557 = 396667) B396667
theorem B935927 : Blo 275825 935927 := bstep (se 1 (by rfl) ⟨701945, by rfl⟩ : syracuseStep 935927 = 1403891) B1403891
theorem B414566423 : Blo 275825 414566423 := bstep (se 1 (by rfl) ⟨310924817, by rfl⟩ : syracuseStep 414566423 = 621849635) B621849635
theorem B17713835 : Blo 275825 17713835 := bstep (se 1 (by rfl) ⟨13285376, by rfl⟩ : syracuseStep 17713835 = 26570753) B26570753
theorem B936791 : Blo 275825 936791 := bstep (se 1 (by rfl) ⟨702593, by rfl⟩ : syracuseStep 936791 = 1405187) B1405187
theorem B314203 : Blo 275825 314203 := bstep (se 1 (by rfl) ⟨235652, by rfl⟩ : syracuseStep 314203 = 471305) B471305
theorem B937007 : Blo 275825 937007 := bstep (se 1 (by rfl) ⟨702755, by rfl⟩ : syracuseStep 937007 = 1405511) B1405511
theorem B1068457 : Blo 275825 1068457 := bstep (se 2 (by rfl) ⟨400671, by rfl⟩ : syracuseStep 1068457 = 801343) B801343
theorem B937385 : Blo 275825 937385 := bstep (se 2 (by rfl) ⟨351519, by rfl⟩ : syracuseStep 937385 = 703039) B703039
theorem B445943 : Blo 275825 445943 := bstep (se 1 (by rfl) ⟨334457, by rfl⟩ : syracuseStep 445943 = 668915) B668915
theorem B708203 : Blo 275825 708203 := bstep (se 1 (by rfl) ⟨531152, by rfl⟩ : syracuseStep 708203 = 1062305) B1062305
theorem B1396601 : Blo 275825 1396601 := bstep (se 2 (by rfl) ⟨523725, by rfl⟩ : syracuseStep 1396601 = 1047451) B1047451
theorem B937871 : Blo 275825 937871 := bstep (se 1 (by rfl) ⟨703403, by rfl⟩ : syracuseStep 937871 = 1406807) B1406807
theorem B413915 : Blo 275825 413915 := bstep (se 1 (by rfl) ⟨310436, by rfl⟩ : syracuseStep 413915 = 620873) B620873
theorem B413927 : Blo 275825 413927 := bstep (se 1 (by rfl) ⟨310445, by rfl⟩ : syracuseStep 413927 = 620891) B620891
theorem B938249 : Blo 275825 938249 := bstep (se 2 (by rfl) ⟨351843, by rfl⟩ : syracuseStep 938249 = 703687) B703687
theorem B414089 : Blo 275825 414089 := bstep (se 2 (by rfl) ⟨155283, by rfl⟩ : syracuseStep 414089 = 310567) B310567
theorem B414185 : Blo 275825 414185 := bstep (se 2 (by rfl) ⟨155319, by rfl⟩ : syracuseStep 414185 = 310639) B310639
theorem B414311 : Blo 275825 414311 := bstep (se 1 (by rfl) ⟨310733, by rfl⟩ : syracuseStep 414311 = 621467) B621467
theorem B1331815 : Blo 275825 1331815 := bstep (se 1 (by rfl) ⟨998861, by rfl⟩ : syracuseStep 1331815 = 1997723) B1997723
theorem B1331873 : Blo 275825 1331873 := bstep (se 2 (by rfl) ⟨499452, by rfl⟩ : syracuseStep 1331873 = 998905) B998905
theorem B414443 : Blo 275825 414443 := bstep (se 1 (by rfl) ⟨310832, by rfl⟩ : syracuseStep 414443 = 621665) B621665
theorem B3822329 : Blo 275825 3822329 := bstep (se 2 (by rfl) ⟨1433373, by rfl⟩ : syracuseStep 3822329 = 2866747) B2866747
theorem B414473 : Blo 275825 414473 := bstep (se 2 (by rfl) ⟨155427, by rfl⟩ : syracuseStep 414473 = 310855) B310855
theorem B1790743 : Blo 275825 1790743 := bstep (se 1 (by rfl) ⟨1343057, by rfl⟩ : syracuseStep 1790743 = 2686115) B2686115
theorem B414575 : Blo 275825 414575 := bstep (se 1 (by rfl) ⟨310931, by rfl⟩ : syracuseStep 414575 = 621863) B621863
theorem B1266683 : Blo 275825 1266683 := bstep (se 1 (by rfl) ⟨950012, by rfl⟩ : syracuseStep 1266683 = 1900025) B1900025
theorem B414827 : Blo 275825 414827 := bstep (se 1 (by rfl) ⟨311120, by rfl⟩ : syracuseStep 414827 = 622241) B622241
theorem B415067 : Blo 275825 415067 := bstep (se 1 (by rfl) ⟨311300, by rfl⟩ : syracuseStep 415067 = 622601) B622601
theorem B939383 : Blo 275825 939383 := bstep (se 1 (by rfl) ⟨704537, by rfl⟩ : syracuseStep 939383 = 1409075) B1409075
theorem B1594811 : Blo 275825 1594811 := bstep (se 1 (by rfl) ⟨1196108, by rfl⟩ : syracuseStep 1594811 = 2392217) B2392217
theorem B1004987 : Blo 275825 1004987 := bstep (se 1 (by rfl) ⟨753740, by rfl⟩ : syracuseStep 1004987 = 1507481) B1507481
theorem B415343 : Blo 275825 415343 := bstep (se 1 (by rfl) ⟨311507, by rfl⟩ : syracuseStep 415343 = 623015) B623015
theorem B710315 : Blo 275825 710315 := bstep (se 1 (by rfl) ⟨532736, by rfl⟩ : syracuseStep 710315 = 1065473) B1065473
theorem B415415 : Blo 275825 415415 := bstep (se 1 (by rfl) ⟨311561, by rfl⟩ : syracuseStep 415415 = 623123) B623123
theorem B349915 : Blo 275825 349915 := bstep (se 1 (by rfl) ⟨262436, by rfl⟩ : syracuseStep 349915 = 524873) B524873
theorem B415451 : Blo 275825 415451 := bstep (se 1 (by rfl) ⟨311588, by rfl⟩ : syracuseStep 415451 = 623177) B623177
theorem B415625 : Blo 275825 415625 := bstep (se 2 (by rfl) ⟨155859, by rfl⟩ : syracuseStep 415625 = 311719) B311719
theorem B415727 : Blo 275825 415727 := bstep (se 1 (by rfl) ⟨311795, by rfl⟩ : syracuseStep 415727 = 623591) B623591
theorem B940193 : Blo 275825 940193 := bstep (se 2 (by rfl) ⟨352572, by rfl⟩ : syracuseStep 940193 = 705145) B705145
theorem B841927 : Blo 275825 841927 := bstep (se 1 (by rfl) ⟨631445, by rfl⟩ : syracuseStep 841927 = 1262891) B1262891
theorem B415979 : Blo 275825 415979 := bstep (se 1 (by rfl) ⟨311984, by rfl⟩ : syracuseStep 415979 = 623969) B623969
theorem B1988873 : Blo 275825 1988873 := bstep (se 2 (by rfl) ⟨745827, by rfl⟩ : syracuseStep 1988873 = 1491655) B1491655
theorem B416039 : Blo 275825 416039 := bstep (se 1 (by rfl) ⟨312029, by rfl⟩ : syracuseStep 416039 = 624059) B624059
theorem B416123 : Blo 275825 416123 := bstep (se 1 (by rfl) ⟨312092, by rfl⟩ : syracuseStep 416123 = 624185) B624185
theorem B940463 : Blo 275825 940463 := bstep (se 1 (by rfl) ⟨705347, by rfl⟩ : syracuseStep 940463 = 1410695) B1410695
theorem B1006013 : Blo 275825 1006013 := bstep (se 3 (by rfl) ⟨188627, by rfl⟩ : syracuseStep 1006013 = 377255) B377255
theorem B416393 : Blo 275825 416393 := bstep (se 2 (by rfl) ⟨156147, by rfl⟩ : syracuseStep 416393 = 312295) B312295
theorem B1596125 : Blo 275825 1596125 := bstep (se 3 (by rfl) ⟨299273, by rfl⟩ : syracuseStep 1596125 = 598547) B598547
theorem B416567 : Blo 275825 416567 := bstep (se 1 (by rfl) ⟨312425, by rfl⟩ : syracuseStep 416567 = 624851) B624851
theorem B1071955 : Blo 275825 1071955 := bstep (se 1 (by rfl) ⟨803966, by rfl⟩ : syracuseStep 1071955 = 1607933) B1607933
theorem B416603 : Blo 275825 416603 := bstep (se 1 (by rfl) ⟨312452, by rfl⟩ : syracuseStep 416603 = 624905) B624905
theorem B351211 : Blo 275825 351211 := bstep (se 1 (by rfl) ⟨263408, by rfl⟩ : syracuseStep 351211 = 526817) B526817
theorem B416747 : Blo 275825 416747 := bstep (se 1 (by rfl) ⟨312560, by rfl⟩ : syracuseStep 416747 = 625121) B625121
theorem B416951 : Blo 275825 416951 := bstep (se 1 (by rfl) ⟨312713, by rfl⟩ : syracuseStep 416951 = 625427) B625427
theorem B417191 : Blo 275825 417191 := bstep (se 1 (by rfl) ⟨312893, by rfl⟩ : syracuseStep 417191 = 625787) B625787
theorem B941543 : Blo 275825 941543 := bstep (se 1 (by rfl) ⟨706157, by rfl⟩ : syracuseStep 941543 = 1412315) B1412315
theorem B417275 : Blo 275825 417275 := bstep (se 1 (by rfl) ⟨312956, by rfl⟩ : syracuseStep 417275 = 625913) B625913
theorem B417371 : Blo 275825 417371 := bstep (se 1 (by rfl) ⟨313028, by rfl⟩ : syracuseStep 417371 = 626057) B626057
theorem B417455 : Blo 275825 417455 := bstep (se 1 (by rfl) ⟨313091, by rfl⟩ : syracuseStep 417455 = 626183) B626183
theorem B2678507 : Blo 275825 2678507 := bstep (se 1 (by rfl) ⟨2008880, by rfl⟩ : syracuseStep 2678507 = 4017761) B4017761
theorem B417575 : Blo 275825 417575 := bstep (se 1 (by rfl) ⟨313181, by rfl⟩ : syracuseStep 417575 = 626363) B626363
theorem B417659 : Blo 275825 417659 := bstep (se 1 (by rfl) ⟨313244, by rfl⟩ : syracuseStep 417659 = 626489) B626489
theorem B4087741 : Blo 275825 4087741 := bstep (se 3 (by rfl) ⟨766451, by rfl⟩ : syracuseStep 4087741 = 1532903) B1532903
theorem B942299 : Blo 275825 942299 := bstep (se 1 (by rfl) ⟨706724, by rfl⟩ : syracuseStep 942299 = 1413449) B1413449
theorem B3825883 : Blo 275825 3825883 := bstep (se 1 (by rfl) ⟨2869412, by rfl⟩ : syracuseStep 3825883 = 5738825) B5738825
theorem B418079 : Blo 275825 418079 := bstep (se 1 (by rfl) ⟨313559, by rfl⟩ : syracuseStep 418079 = 627119) B627119
theorem B418103 : Blo 275825 418103 := bstep (se 1 (by rfl) ⟨313577, by rfl⟩ : syracuseStep 418103 = 627155) B627155
theorem B9691469 : Blo 275825 9691469 := bstep (se 3 (by rfl) ⟨1817150, by rfl⟩ : syracuseStep 9691469 = 3634301) B3634301
theorem B418175 : Blo 275825 418175 := bstep (se 1 (by rfl) ⟨313631, by rfl⟩ : syracuseStep 418175 = 627263) B627263
theorem B418247 : Blo 275825 418247 := bstep (se 1 (by rfl) ⟨313685, by rfl⟩ : syracuseStep 418247 = 627371) B627371
theorem B942569 : Blo 275825 942569 := bstep (se 2 (by rfl) ⟨353463, by rfl⟩ : syracuseStep 942569 = 706927) B706927
theorem B1729133 : Blo 275825 1729133 := bstep (se 3 (by rfl) ⟨324212, by rfl⟩ : syracuseStep 1729133 = 648425) B648425
theorem B3793591 : Blo 275825 3793591 := bstep (se 1 (by rfl) ⟨2845193, by rfl⟩ : syracuseStep 3793591 = 5690387) B5690387
theorem B418601 : Blo 275825 418601 := bstep (se 2 (by rfl) ⟨156975, by rfl⟩ : syracuseStep 418601 = 313951) B313951
theorem B418607 : Blo 275825 418607 := bstep (se 1 (by rfl) ⟨313955, by rfl⟩ : syracuseStep 418607 = 627911) B627911
theorem B1336121 : Blo 275825 1336121 := bstep (se 2 (by rfl) ⟨501045, by rfl⟩ : syracuseStep 1336121 = 1002091) B1002091
theorem B418727 : Blo 275825 418727 := bstep (se 1 (by rfl) ⟨314045, by rfl⟩ : syracuseStep 418727 = 628091) B628091
theorem B15524783 : Blo 275825 15524783 := bstep (se 1 (by rfl) ⟨11643587, by rfl⟩ : syracuseStep 15524783 = 23287175) B23287175
theorem B418811 : Blo 275825 418811 := bstep (se 1 (by rfl) ⟨314108, by rfl⟩ : syracuseStep 418811 = 628217) B628217
theorem B418871 : Blo 275825 418871 := bstep (se 1 (by rfl) ⟨314153, by rfl⟩ : syracuseStep 418871 = 628307) B628307
theorem B943163 : Blo 275825 943163 := bstep (se 1 (by rfl) ⟨707372, by rfl⟩ : syracuseStep 943163 = 1414745) B1414745
theorem B418991 : Blo 275825 418991 := bstep (se 1 (by rfl) ⟨314243, by rfl⟩ : syracuseStep 418991 = 628487) B628487
theorem B943433 : Blo 275825 943433 := bstep (se 2 (by rfl) ⟨353787, by rfl⟩ : syracuseStep 943433 = 707575) B707575
theorem B419399 : Blo 275825 419399 := bstep (se 1 (by rfl) ⟨314549, by rfl⟩ : syracuseStep 419399 = 629099) B629099
theorem B1992275 : Blo 275825 1992275 := bstep (se 1 (by rfl) ⟨1494206, by rfl⟩ : syracuseStep 1992275 = 2988413) B2988413
theorem B419495 : Blo 275825 419495 := bstep (se 1 (by rfl) ⟨314621, by rfl⟩ : syracuseStep 419495 = 629243) B629243
theorem B419579 : Blo 275825 419579 := bstep (se 1 (by rfl) ⟨314684, by rfl⟩ : syracuseStep 419579 = 629369) B629369
theorem B419615 : Blo 275825 419615 := bstep (se 1 (by rfl) ⟨314711, by rfl⟩ : syracuseStep 419615 = 629423) B629423
theorem B419663 : Blo 275825 419663 := bstep (se 1 (by rfl) ⟨314747, by rfl⟩ : syracuseStep 419663 = 629495) B629495
theorem B2844953 : Blo 275825 2844953 := bstep (se 2 (by rfl) ⟨1066857, by rfl⟩ : syracuseStep 2844953 = 2133715) B2133715
theorem B10971449 : Blo 275825 10971449 := bstep (se 2 (by rfl) ⟨4114293, by rfl⟩ : syracuseStep 10971449 = 8228587) B8228587
theorem B9038141 : Blo 275825 9038141 := bstep (se 3 (by rfl) ⟨1694651, by rfl⟩ : syracuseStep 9038141 = 3389303) B3389303
theorem B846523 : Blo 275825 846523 := bstep (se 1 (by rfl) ⟨634892, by rfl⟩ : syracuseStep 846523 = 1269785) B1269785
theorem B3992267 : Blo 275825 3992267 := bstep (se 1 (by rfl) ⟨2994200, by rfl⟩ : syracuseStep 3992267 = 5988401) B5988401
theorem B2386907 : Blo 275825 2386907 := bstep (se 1 (by rfl) ⟨1790180, by rfl⟩ : syracuseStep 2386907 = 3580361) B3580361
theorem B36137987 : Blo 275825 36137987 := bstep (se 1 (by rfl) ⟨27103490, by rfl⟩ : syracuseStep 36137987 = 54206981) B54206981
theorem B5303339 : Blo 275825 5303339 := bstep (se 1 (by rfl) ⟨3977504, by rfl⟩ : syracuseStep 5303339 = 7955009) B7955009
theorem B4025483 : Blo 275825 4025483 := bstep (se 1 (by rfl) ⟨3019112, by rfl⟩ : syracuseStep 4025483 = 6038225) B6038225
theorem B1994635 : Blo 275825 1994635 := bstep (se 1 (by rfl) ⟨1495976, by rfl⟩ : syracuseStep 1994635 = 2991953) B2991953
theorem B2256779 : Blo 275825 2256779 := bstep (se 1 (by rfl) ⟨1692584, by rfl⟩ : syracuseStep 2256779 = 3385169) B3385169
theorem B2389297 : Blo 275825 2389297 := bstep (se 2 (by rfl) ⟨895986, by rfl⟩ : syracuseStep 2389297 = 1791973) B1791973
theorem B1341137 : Blo 275825 1341137 := bstep (se 2 (by rfl) ⟨502926, by rfl⟩ : syracuseStep 1341137 = 1005853) B1005853
theorem B947963 : Blo 275825 947963 := bstep (se 1 (by rfl) ⟨710972, by rfl⟩ : syracuseStep 947963 = 1421945) B1421945
theorem B1406969 : Blo 275825 1406969 := bstep (se 2 (by rfl) ⟨527613, by rfl⟩ : syracuseStep 1406969 = 1055227) B1055227
theorem B620639 : Blo 275825 620639 := bstep (se 1 (by rfl) ⟨465479, by rfl⟩ : syracuseStep 620639 = 930959) B930959
theorem B424759 : Blo 275825 424759 := bstep (se 1 (by rfl) ⟨318569, by rfl⟩ : syracuseStep 424759 = 637139) B637139
theorem B621395 : Blo 275825 621395 := bstep (se 1 (by rfl) ⟨466046, by rfl⟩ : syracuseStep 621395 = 932093) B932093
theorem B1408265 : Blo 275825 1408265 := bstep (se 2 (by rfl) ⟨528099, by rfl⟩ : syracuseStep 1408265 = 1056199) B1056199
theorem B1506599 : Blo 275825 1506599 := bstep (se 1 (by rfl) ⟨1129949, by rfl⟩ : syracuseStep 1506599 = 2259899) B2259899
theorem B621935 : Blo 275825 621935 := bstep (se 1 (by rfl) ⟨466451, by rfl⟩ : syracuseStep 621935 = 932903) B932903
theorem B458303 : Blo 275825 458303 := bstep (se 1 (by rfl) ⟨343727, by rfl⟩ : syracuseStep 458303 = 687455) B687455
theorem B785999 : Blo 275825 785999 := bstep (se 1 (by rfl) ⟨589499, by rfl⟩ : syracuseStep 785999 = 1178999) B1178999
theorem B622223 : Blo 275825 622223 := bstep (se 1 (by rfl) ⟨466667, by rfl⟩ : syracuseStep 622223 = 933335) B933335
theorem B622313 : Blo 275825 622313 := bstep (se 2 (by rfl) ⟨233367, by rfl⟩ : syracuseStep 622313 = 466735) B466735
theorem B1507049 : Blo 275825 1507049 := bstep (se 2 (by rfl) ⟨565143, by rfl⟩ : syracuseStep 1507049 = 1130287) B1130287
theorem B1081727 : Blo 275825 1081727 := bstep (se 1 (by rfl) ⟨811295, by rfl⟩ : syracuseStep 1081727 = 1622591) B1622591
theorem B1049183 : Blo 275825 1049183 := bstep (se 1 (by rfl) ⟨786887, by rfl⟩ : syracuseStep 1049183 = 1573775) B1573775
theorem B3146363 : Blo 275825 3146363 := bstep (se 1 (by rfl) ⟨2359772, by rfl⟩ : syracuseStep 3146363 = 4719545) B4719545
theorem B2294701 : Blo 275825 2294701 := bstep (se 3 (by rfl) ⟨430256, by rfl⟩ : syracuseStep 2294701 = 860513) B860513
theorem B19268761 : Blo 275825 19268761 := bstep (se 2 (by rfl) ⟨7225785, by rfl⟩ : syracuseStep 19268761 = 14451571) B14451571
theorem B525503 : Blo 275825 525503 := bstep (se 1 (by rfl) ⟨394127, by rfl⟩ : syracuseStep 525503 = 788255) B788255
theorem B623807 : Blo 275825 623807 := bstep (se 1 (by rfl) ⟨467855, by rfl⟩ : syracuseStep 623807 = 935711) B935711
theorem B1049881 : Blo 275825 1049881 := bstep (se 2 (by rfl) ⟨393705, by rfl⟩ : syracuseStep 1049881 = 787411) B787411
theorem B1410371 : Blo 275825 1410371 := bstep (se 1 (by rfl) ⟨1057778, by rfl⟩ : syracuseStep 1410371 = 2115557) B2115557
theorem B623951 : Blo 275825 623951 := bstep (se 1 (by rfl) ⟨467963, by rfl⟩ : syracuseStep 623951 = 935927) B935927
theorem B624041 : Blo 275825 624041 := bstep (se 2 (by rfl) ⟨234015, by rfl⟩ : syracuseStep 624041 = 468031) B468031
theorem B1181375 : Blo 275825 1181375 := bstep (se 1 (by rfl) ⟨886031, by rfl⟩ : syracuseStep 1181375 = 1772063) B1772063
theorem B624527 : Blo 275825 624527 := bstep (se 1 (by rfl) ⟨468395, by rfl⟩ : syracuseStep 624527 = 936791) B936791
theorem B10192877 : Blo 275825 10192877 := bstep (se 3 (by rfl) ⟨1911164, by rfl⟩ : syracuseStep 10192877 = 3822329) B3822329
theorem B624671 : Blo 275825 624671 := bstep (se 1 (by rfl) ⟨468503, by rfl⟩ : syracuseStep 624671 = 937007) B937007
theorem B1411181 : Blo 275825 1411181 := bstep (se 3 (by rfl) ⟨264596, by rfl⟩ : syracuseStep 1411181 = 529193) B529193
theorem B1050839 : Blo 275825 1050839 := bstep (se 1 (by rfl) ⟨788129, by rfl⟩ : syracuseStep 1050839 = 1576259) B1576259
theorem B624923 : Blo 275825 624923 := bstep (se 1 (by rfl) ⟨468692, by rfl⟩ : syracuseStep 624923 = 937385) B937385
theorem B625247 : Blo 275825 625247 := bstep (se 1 (by rfl) ⟨468935, by rfl⟩ : syracuseStep 625247 = 937871) B937871
theorem B3377821 : Blo 275825 3377821 := bstep (se 3 (by rfl) ⟨633341, by rfl⟩ : syracuseStep 3377821 = 1266683) B1266683
theorem B527143 : Blo 275825 527143 := bstep (se 1 (by rfl) ⟨395357, by rfl⟩ : syracuseStep 527143 = 790715) B790715
theorem B625499 : Blo 275825 625499 := bstep (se 1 (by rfl) ⟨469124, by rfl⟩ : syracuseStep 625499 = 938249) B938249
theorem B396343 : Blo 275825 396343 := bstep (se 1 (by rfl) ⟨297257, by rfl⟩ : syracuseStep 396343 = 594515) B594515
theorem B76516433 : Blo 275825 76516433 := bstep (se 2 (by rfl) ⟨28693662, by rfl⟩ : syracuseStep 76516433 = 57387325) B57387325
theorem B887915 : Blo 275825 887915 := bstep (se 1 (by rfl) ⟨665936, by rfl⟩ : syracuseStep 887915 = 1331873) B1331873
theorem B2100491 : Blo 275825 2100491 := bstep (se 1 (by rfl) ⟨1575368, by rfl⟩ : syracuseStep 2100491 = 3150737) B3150737
theorem B888185 : Blo 275825 888185 := bstep (se 2 (by rfl) ⟨333069, by rfl⟩ : syracuseStep 888185 = 666139) B666139
theorem B1052129 : Blo 275825 1052129 := bstep (se 2 (by rfl) ⟨394548, by rfl⟩ : syracuseStep 1052129 = 789097) B789097
theorem B626255 : Blo 275825 626255 := bstep (se 1 (by rfl) ⟨469691, by rfl⟩ : syracuseStep 626255 = 939383) B939383
theorem B626795 : Blo 275825 626795 := bstep (se 1 (by rfl) ⟨470096, by rfl⟩ : syracuseStep 626795 = 940193) B940193
theorem B626849 : Blo 275825 626849 := bstep (se 2 (by rfl) ⟨235068, by rfl⟩ : syracuseStep 626849 = 470137) B470137
theorem B626975 : Blo 275825 626975 := bstep (se 1 (by rfl) ⟨470231, by rfl⟩ : syracuseStep 626975 = 940463) B940463
theorem B1577465 : Blo 275825 1577465 := bstep (se 2 (by rfl) ⟨591549, by rfl⟩ : syracuseStep 1577465 = 1183099) B1183099
theorem B2101949 : Blo 275825 2101949 := bstep (se 3 (by rfl) ⟨394115, by rfl⟩ : syracuseStep 2101949 = 788231) B788231
theorem B529391 : Blo 275825 529391 := bstep (se 1 (by rfl) ⟨397043, by rfl⟩ : syracuseStep 529391 = 794087) B794087
theorem B627695 : Blo 275825 627695 := bstep (se 1 (by rfl) ⟨470771, by rfl⟩ : syracuseStep 627695 = 941543) B941543
theorem B2659513 : Blo 275825 2659513 := bstep (se 2 (by rfl) ⟨997317, by rfl⟩ : syracuseStep 2659513 = 1994635) B1994635
theorem B890041 : Blo 275825 890041 := bstep (se 2 (by rfl) ⟨333765, by rfl⟩ : syracuseStep 890041 = 667531) B667531
theorem B628199 : Blo 275825 628199 := bstep (se 1 (by rfl) ⟨471149, by rfl⟩ : syracuseStep 628199 = 942299) B942299
theorem B6460979 : Blo 275825 6460979 := bstep (se 1 (by rfl) ⟨4845734, by rfl⟩ : syracuseStep 6460979 = 9691469) B9691469
theorem B628361 : Blo 275825 628361 := bstep (se 2 (by rfl) ⟨235635, by rfl⟩ : syracuseStep 628361 = 471271) B471271
theorem B628379 : Blo 275825 628379 := bstep (se 1 (by rfl) ⟨471284, by rfl⟩ : syracuseStep 628379 = 942569) B942569
theorem B1185491 : Blo 275825 1185491 := bstep (se 1 (by rfl) ⟨889118, by rfl⟩ : syracuseStep 1185491 = 1778237) B1778237
theorem B1152755 : Blo 275825 1152755 := bstep (se 1 (by rfl) ⟨864566, by rfl⟩ : syracuseStep 1152755 = 1729133) B1729133
theorem B628577 : Blo 275825 628577 := bstep (se 2 (by rfl) ⟨235716, by rfl⟩ : syracuseStep 628577 = 471433) B471433
theorem B890747 : Blo 275825 890747 := bstep (se 1 (by rfl) ⟨668060, by rfl⟩ : syracuseStep 890747 = 1336121) B1336121
theorem B530401 : Blo 275825 530401 := bstep (se 2 (by rfl) ⟨198900, by rfl⟩ : syracuseStep 530401 = 397801) B397801
theorem B628775 : Blo 275825 628775 := bstep (se 1 (by rfl) ⟨471581, by rfl⟩ : syracuseStep 628775 = 943163) B943163
theorem B1775753 : Blo 275825 1775753 := bstep (se 2 (by rfl) ⟨665907, by rfl⟩ : syracuseStep 1775753 = 1331815) B1331815
theorem B530651 : Blo 275825 530651 := bstep (se 1 (by rfl) ⟨397988, by rfl⟩ : syracuseStep 530651 = 795977) B795977
theorem B628955 : Blo 275825 628955 := bstep (se 1 (by rfl) ⟨471716, by rfl⟩ : syracuseStep 628955 = 943433) B943433
theorem B629153 : Blo 275825 629153 := bstep (se 2 (by rfl) ⟨235932, by rfl⟩ : syracuseStep 629153 = 471865) B471865
theorem B629225 : Blo 275825 629225 := bstep (se 2 (by rfl) ⟨235959, by rfl⟩ : syracuseStep 629225 = 471919) B471919
theorem B7314299 : Blo 275825 7314299 := bstep (se 1 (by rfl) ⟨5485724, by rfl⟩ : syracuseStep 7314299 = 10971449) B10971449
theorem B3185729 : Blo 275825 3185729 := bstep (se 2 (by rfl) ⟨1194648, by rfl⟩ : syracuseStep 3185729 = 2389297) B2389297
theorem B2661511 : Blo 275825 2661511 := bstep (se 1 (by rfl) ⟨1996133, by rfl⟩ : syracuseStep 2661511 = 3992267) B3992267
theorem B24091991 : Blo 275825 24091991 := bstep (se 1 (by rfl) ⟨18068993, by rfl⟩ : syracuseStep 24091991 = 36137987) B36137987
theorem B466553 : Blo 275825 466553 := bstep (se 2 (by rfl) ⟨174957, by rfl⟩ : syracuseStep 466553 = 349915) B349915
theorem B1056503 : Blo 275825 1056503 := bstep (se 1 (by rfl) ⟨792377, by rfl⟩ : syracuseStep 1056503 = 1584755) B1584755
theorem B1122569 : Blo 275825 1122569 := bstep (se 2 (by rfl) ⟨420963, by rfl⟩ : syracuseStep 1122569 = 841927) B841927
theorem B1057475 : Blo 275825 1057475 := bstep (se 1 (by rfl) ⟨793106, by rfl⟩ : syracuseStep 1057475 = 1586213) B1586213
theorem B566345 : Blo 275825 566345 := bstep (se 2 (by rfl) ⟨212379, by rfl⟩ : syracuseStep 566345 = 424759) B424759
theorem B1057931 : Blo 275825 1057931 := bstep (se 1 (by rfl) ⟨793448, by rfl⟩ : syracuseStep 1057931 = 1586897) B1586897
theorem B894091 : Blo 275825 894091 := bstep (se 1 (by rfl) ⟨670568, by rfl⟩ : syracuseStep 894091 = 1341137) B1341137
theorem B631975 : Blo 275825 631975 := bstep (se 1 (by rfl) ⟨473981, by rfl⟩ : syracuseStep 631975 = 947963) B947963
theorem B468281 : Blo 275825 468281 := bstep (se 2 (by rfl) ⟨175605, by rfl⟩ : syracuseStep 468281 = 351211) B351211
theorem B1189181 : Blo 275825 1189181 := bstep (se 3 (by rfl) ⟨222971, by rfl⟩ : syracuseStep 1189181 = 445943) B445943
theorem B1222141 : Blo 275825 1222141 := bstep (se 3 (by rfl) ⟨229151, by rfl⟩ : syracuseStep 1222141 = 458303) B458303
theorem B14526209 : Blo 275825 14526209 := bstep (se 2 (by rfl) ⟨5447328, by rfl⟩ : syracuseStep 14526209 = 10894657) B10894657
theorem B1190123 : Blo 275825 1190123 := bstep (se 1 (by rfl) ⟨892592, by rfl⟩ : syracuseStep 1190123 = 1785185) B1785185
theorem B1059115 : Blo 275825 1059115 := bstep (se 1 (by rfl) ⟨794336, by rfl⟩ : syracuseStep 1059115 = 1588673) B1588673
theorem B665993 : Blo 275825 665993 := bstep (se 2 (by rfl) ⟨249747, by rfl⟩ : syracuseStep 665993 = 499495) B499495
theorem B5450321 : Blo 275825 5450321 := bstep (se 2 (by rfl) ⟨2043870, by rfl⟩ : syracuseStep 5450321 = 4087741) B4087741
theorem B1125035 : Blo 275825 1125035 := bstep (se 1 (by rfl) ⟨843776, by rfl⟩ : syracuseStep 1125035 = 1687553) B1687553
theorem B470495 : Blo 275825 470495 := bstep (se 1 (by rfl) ⟨352871, by rfl⟩ : syracuseStep 470495 = 705743) B705743
theorem B5058121 : Blo 275825 5058121 := bstep (se 2 (by rfl) ⟨1896795, by rfl⟩ : syracuseStep 5058121 = 3793591) B3793591
theorem B470711 : Blo 275825 470711 := bstep (se 1 (by rfl) ⟨353033, by rfl⟩ : syracuseStep 470711 = 706067) B706067
theorem B1355459 : Blo 275825 1355459 := bstep (se 1 (by rfl) ⟨1016594, by rfl⟩ : syracuseStep 1355459 = 2033189) B2033189
theorem B667369 : Blo 275825 667369 := bstep (se 2 (by rfl) ⟨250263, by rfl⟩ : syracuseStep 667369 = 500527) B500527
theorem B276377615 : Blo 275825 276377615 := bstep (se 1 (by rfl) ⟨207283211, by rfl⟩ : syracuseStep 276377615 = 414566423) B414566423
theorem B11809223 : Blo 275825 11809223 := bstep (se 1 (by rfl) ⟨8856917, by rfl⟩ : syracuseStep 11809223 = 17713835) B17713835
theorem B1684435 : Blo 275825 1684435 := bstep (se 1 (by rfl) ⟨1263326, by rfl⟩ : syracuseStep 1684435 = 2526653) B2526653
theorem B472135 : Blo 275825 472135 := bstep (se 1 (by rfl) ⟨354101, by rfl⟩ : syracuseStep 472135 = 708203) B708203
theorem B1062017 : Blo 275825 1062017 := bstep (se 2 (by rfl) ⟨398256, by rfl⟩ : syracuseStep 1062017 = 796513) B796513
theorem B931067 : Blo 275825 931067 := bstep (se 1 (by rfl) ⟨698300, by rfl⟩ : syracuseStep 931067 = 1396601) B1396601
theorem B3159485 : Blo 275825 3159485 := bstep (se 3 (by rfl) ⟨592403, by rfl⟩ : syracuseStep 3159485 = 1184807) B1184807
theorem B275943 : Blo 275825 275943 := bstep (se 1 (by rfl) ⟨206957, by rfl⟩ : syracuseStep 275943 = 413915) B413915
theorem B275951 : Blo 275825 275951 := bstep (se 1 (by rfl) ⟨206963, by rfl⟩ : syracuseStep 275951 = 413927) B413927
theorem B276059 : Blo 275825 276059 := bstep (se 1 (by rfl) ⟨207044, by rfl⟩ : syracuseStep 276059 = 414089) B414089
theorem B276123 : Blo 275825 276123 := bstep (se 1 (by rfl) ⟨207092, by rfl⟩ : syracuseStep 276123 = 414185) B414185
theorem B276207 : Blo 275825 276207 := bstep (se 1 (by rfl) ⟨207155, by rfl⟩ : syracuseStep 276207 = 414311) B414311
theorem B276295 : Blo 275825 276295 := bstep (se 1 (by rfl) ⟨207221, by rfl⟩ : syracuseStep 276295 = 414443) B414443
theorem B276315 : Blo 275825 276315 := bstep (se 1 (by rfl) ⟨207236, by rfl⟩ : syracuseStep 276315 = 414473) B414473
theorem B276383 : Blo 275825 276383 := bstep (se 1 (by rfl) ⟨207287, by rfl⟩ : syracuseStep 276383 = 414575) B414575
theorem B2668585 : Blo 275825 2668585 := bstep (se 2 (by rfl) ⟨1000719, by rfl⟩ : syracuseStep 2668585 = 2001439) B2001439
theorem B276551 : Blo 275825 276551 := bstep (se 1 (by rfl) ⟨207413, by rfl⟩ : syracuseStep 276551 = 414827) B414827
theorem B276711 : Blo 275825 276711 := bstep (se 1 (by rfl) ⟨207533, by rfl⟩ : syracuseStep 276711 = 415067) B415067
theorem B702695 : Blo 275825 702695 := bstep (se 1 (by rfl) ⟨527021, by rfl⟩ : syracuseStep 702695 = 1054043) B1054043
theorem B1128697 : Blo 275825 1128697 := bstep (se 2 (by rfl) ⟨423261, by rfl⟩ : syracuseStep 1128697 = 846523) B846523
theorem B1063207 : Blo 275825 1063207 := bstep (se 1 (by rfl) ⟨797405, by rfl⟩ : syracuseStep 1063207 = 1594811) B1594811
theorem B276895 : Blo 275825 276895 := bstep (se 1 (by rfl) ⟨207671, by rfl⟩ : syracuseStep 276895 = 415343) B415343
theorem B473543 : Blo 275825 473543 := bstep (se 1 (by rfl) ⟨355157, by rfl⟩ : syracuseStep 473543 = 710315) B710315
theorem B276943 : Blo 275825 276943 := bstep (se 1 (by rfl) ⟨207707, by rfl⟩ : syracuseStep 276943 = 415415) B415415
theorem B276967 : Blo 275825 276967 := bstep (se 1 (by rfl) ⟨207725, by rfl⟩ : syracuseStep 276967 = 415451) B415451
theorem B277083 : Blo 275825 277083 := bstep (se 1 (by rfl) ⟨207812, by rfl⟩ : syracuseStep 277083 = 415625) B415625
theorem B277151 : Blo 275825 277151 := bstep (se 1 (by rfl) ⟨207863, by rfl⟩ : syracuseStep 277151 = 415727) B415727
theorem B277319 : Blo 275825 277319 := bstep (se 1 (by rfl) ⟨207989, by rfl⟩ : syracuseStep 277319 = 415979) B415979
theorem B1325915 : Blo 275825 1325915 := bstep (se 1 (by rfl) ⟨994436, by rfl⟩ : syracuseStep 1325915 = 1988873) B1988873
theorem B277359 : Blo 275825 277359 := bstep (se 1 (by rfl) ⟨208019, by rfl⟩ : syracuseStep 277359 = 416039) B416039
theorem B277415 : Blo 275825 277415 := bstep (se 1 (by rfl) ⟨208061, by rfl⟩ : syracuseStep 277415 = 416123) B416123
theorem B670675 : Blo 275825 670675 := bstep (se 1 (by rfl) ⟨503006, by rfl⟩ : syracuseStep 670675 = 1006013) B1006013
theorem B277595 : Blo 275825 277595 := bstep (se 1 (by rfl) ⟨208196, by rfl⟩ : syracuseStep 277595 = 416393) B416393
theorem B1064083 : Blo 275825 1064083 := bstep (se 1 (by rfl) ⟨798062, by rfl⟩ : syracuseStep 1064083 = 1596125) B1596125
theorem B277711 : Blo 275825 277711 := bstep (se 1 (by rfl) ⟨208283, by rfl⟩ : syracuseStep 277711 = 416567) B416567
theorem B1424609 : Blo 275825 1424609 := bstep (se 2 (by rfl) ⟨534228, by rfl⟩ : syracuseStep 1424609 = 1068457) B1068457
theorem B277735 : Blo 275825 277735 := bstep (se 1 (by rfl) ⟨208301, by rfl⟩ : syracuseStep 277735 = 416603) B416603
theorem B277831 : Blo 275825 277831 := bstep (se 1 (by rfl) ⟨208373, by rfl⟩ : syracuseStep 277831 = 416747) B416747
theorem B277967 : Blo 275825 277967 := bstep (se 1 (by rfl) ⟨208475, by rfl⟩ : syracuseStep 277967 = 416951) B416951
theorem B278127 : Blo 275825 278127 := bstep (se 1 (by rfl) ⟨208595, by rfl⟩ : syracuseStep 278127 = 417191) B417191
theorem B278183 : Blo 275825 278183 := bstep (se 1 (by rfl) ⟨208637, by rfl⟩ : syracuseStep 278183 = 417275) B417275
theorem B278247 : Blo 275825 278247 := bstep (se 1 (by rfl) ⟨208685, by rfl⟩ : syracuseStep 278247 = 417371) B417371
theorem B311071 : Blo 275825 311071 := bstep (se 1 (by rfl) ⟨233303, by rfl⟩ : syracuseStep 311071 = 466607) B466607
theorem B278303 : Blo 275825 278303 := bstep (se 1 (by rfl) ⟨208727, by rfl⟩ : syracuseStep 278303 = 417455) B417455
theorem B1785671 : Blo 275825 1785671 := bstep (se 1 (by rfl) ⟨1339253, by rfl⟩ : syracuseStep 1785671 = 2678507) B2678507
theorem B278383 : Blo 275825 278383 := bstep (se 1 (by rfl) ⟨208787, by rfl⟩ : syracuseStep 278383 = 417575) B417575
theorem B278439 : Blo 275825 278439 := bstep (se 1 (by rfl) ⟨208829, by rfl⟩ : syracuseStep 278439 = 417659) B417659
theorem B1425599 : Blo 275825 1425599 := bstep (se 1 (by rfl) ⟨1069199, by rfl⟩ : syracuseStep 1425599 = 2138399) B2138399
theorem B278719 : Blo 275825 278719 := bstep (se 1 (by rfl) ⟨209039, by rfl⟩ : syracuseStep 278719 = 418079) B418079
theorem B311503 : Blo 275825 311503 := bstep (se 1 (by rfl) ⟨233627, by rfl⟩ : syracuseStep 311503 = 467255) B467255
theorem B278735 : Blo 275825 278735 := bstep (se 1 (by rfl) ⟨209051, by rfl⟩ : syracuseStep 278735 = 418103) B418103
theorem B278783 : Blo 275825 278783 := bstep (se 1 (by rfl) ⟨209087, by rfl⟩ : syracuseStep 278783 = 418175) B418175
theorem B278831 : Blo 275825 278831 := bstep (se 1 (by rfl) ⟨209123, by rfl⟩ : syracuseStep 278831 = 418247) B418247
theorem B279067 : Blo 275825 279067 := bstep (se 1 (by rfl) ⟨209300, by rfl⟩ : syracuseStep 279067 = 418601) B418601
theorem B279071 : Blo 275825 279071 := bstep (se 1 (by rfl) ⟨209303, by rfl⟩ : syracuseStep 279071 = 418607) B418607
theorem B279151 : Blo 275825 279151 := bstep (se 1 (by rfl) ⟨209363, by rfl⟩ : syracuseStep 279151 = 418727) B418727
theorem B279207 : Blo 275825 279207 := bstep (se 1 (by rfl) ⟨209405, by rfl⟩ : syracuseStep 279207 = 418811) B418811
theorem B279247 : Blo 275825 279247 := bstep (se 1 (by rfl) ⟨209435, by rfl⟩ : syracuseStep 279247 = 418871) B418871
theorem B279327 : Blo 275825 279327 := bstep (se 1 (by rfl) ⟨209495, by rfl⟩ : syracuseStep 279327 = 418991) B418991
theorem B1327913 : Blo 275825 1327913 := bstep (se 2 (by rfl) ⟨497967, by rfl⟩ : syracuseStep 1327913 = 995935) B995935
theorem B312367 : Blo 275825 312367 := bstep (se 1 (by rfl) ⟨234275, by rfl⟩ : syracuseStep 312367 = 468551) B468551
theorem B279599 : Blo 275825 279599 := bstep (se 1 (by rfl) ⟨209699, by rfl⟩ : syracuseStep 279599 = 419399) B419399
theorem B1328183 : Blo 275825 1328183 := bstep (se 1 (by rfl) ⟨996137, by rfl⟩ : syracuseStep 1328183 = 1992275) B1992275
theorem B279663 : Blo 275825 279663 := bstep (se 1 (by rfl) ⟨209747, by rfl⟩ : syracuseStep 279663 = 419495) B419495
theorem B279719 : Blo 275825 279719 := bstep (se 1 (by rfl) ⟨209789, by rfl⟩ : syracuseStep 279719 = 419579) B419579
theorem B312511 : Blo 275825 312511 := bstep (se 1 (by rfl) ⟨234383, by rfl⟩ : syracuseStep 312511 = 468767) B468767
theorem B279743 : Blo 275825 279743 := bstep (se 1 (by rfl) ⟨209807, by rfl⟩ : syracuseStep 279743 = 419615) B419615
theorem B279775 : Blo 275825 279775 := bstep (se 1 (by rfl) ⟨209831, by rfl⟩ : syracuseStep 279775 = 419663) B419663
theorem B312655 : Blo 275825 312655 := bstep (se 1 (by rfl) ⟨234491, by rfl⟩ : syracuseStep 312655 = 468983) B468983
theorem B2671967 : Blo 275825 2671967 := bstep (se 1 (by rfl) ⟨2003975, by rfl⟩ : syracuseStep 2671967 = 4007951) B4007951
theorem B1591271 : Blo 275825 1591271 := bstep (se 1 (by rfl) ⟨1193453, by rfl⟩ : syracuseStep 1591271 = 2386907) B2386907
theorem B313375 : Blo 275825 313375 := bstep (se 1 (by rfl) ⟨235031, by rfl⟩ : syracuseStep 313375 = 470063) B470063
theorem B706715 : Blo 275825 706715 := bstep (se 1 (by rfl) ⟨530036, by rfl⟩ : syracuseStep 706715 = 1060073) B1060073
theorem B313627 : Blo 275825 313627 := bstep (se 1 (by rfl) ⟨235220, by rfl⟩ : syracuseStep 313627 = 470441) B470441
theorem B5688251 : Blo 275825 5688251 := bstep (se 1 (by rfl) ⟨4266188, by rfl⟩ : syracuseStep 5688251 = 8532377) B8532377
theorem B445495 : Blo 275825 445495 := bstep (se 1 (by rfl) ⟨334121, by rfl⟩ : syracuseStep 445495 = 668243) B668243
theorem B2673971 : Blo 275825 2673971 := bstep (se 1 (by rfl) ⟨2005478, by rfl⟩ : syracuseStep 2673971 = 4010957) B4010957
theorem B314779 : Blo 275825 314779 := bstep (se 1 (by rfl) ⟨236084, by rfl⟩ : syracuseStep 314779 = 472169) B472169
theorem B1429273 : Blo 275825 1429273 := bstep (se 2 (by rfl) ⟨535977, by rfl⟩ : syracuseStep 1429273 = 1071955) B1071955
theorem B937979 : Blo 275825 937979 := bstep (se 1 (by rfl) ⟨703484, by rfl⟩ : syracuseStep 937979 = 1406969) B1406969
theorem B413759 : Blo 275825 413759 := bstep (se 1 (by rfl) ⟨310319, by rfl⟩ : syracuseStep 413759 = 620639) B620639
theorem B413993 : Blo 275825 413993 := bstep (se 2 (by rfl) ⟨155247, by rfl⟩ : syracuseStep 413993 = 310495) B310495
theorem B1790333 : Blo 275825 1790333 := bstep (se 3 (by rfl) ⟨335687, by rfl⟩ : syracuseStep 1790333 = 671375) B671375
theorem B414263 : Blo 275825 414263 := bstep (se 1 (by rfl) ⟨310697, by rfl⟩ : syracuseStep 414263 = 621395) B621395
theorem B938843 : Blo 275825 938843 := bstep (se 1 (by rfl) ⟨704132, by rfl⟩ : syracuseStep 938843 = 1408265) B1408265
theorem B1004399 : Blo 275825 1004399 := bstep (se 1 (by rfl) ⟨753299, by rfl⟩ : syracuseStep 1004399 = 1506599) B1506599
theorem B414623 : Blo 275825 414623 := bstep (se 1 (by rfl) ⟨310967, by rfl⟩ : syracuseStep 414623 = 621935) B621935
theorem B1496045 : Blo 275825 1496045 := bstep (se 3 (by rfl) ⟨280508, by rfl⟩ : syracuseStep 1496045 = 561017) B561017
theorem B6018077 : Blo 275825 6018077 := bstep (se 3 (by rfl) ⟨1128389, by rfl⟩ : syracuseStep 6018077 = 2256779) B2256779
theorem B414815 : Blo 275825 414815 := bstep (se 1 (by rfl) ⟨311111, by rfl⟩ : syracuseStep 414815 = 622223) B622223
theorem B414875 : Blo 275825 414875 := bstep (se 1 (by rfl) ⟨311156, by rfl⟩ : syracuseStep 414875 = 622313) B622313
theorem B1004699 : Blo 275825 1004699 := bstep (se 1 (by rfl) ⟨753524, by rfl⟩ : syracuseStep 1004699 = 1507049) B1507049
theorem B1267451 : Blo 275825 1267451 := bstep (se 1 (by rfl) ⟨950588, by rfl⟩ : syracuseStep 1267451 = 1901177) B1901177
theorem B415559 : Blo 275825 415559 := bstep (se 1 (by rfl) ⟨311669, by rfl⟩ : syracuseStep 415559 = 623339) B623339
theorem B2545481 : Blo 275825 2545481 := bstep (se 2 (by rfl) ⟨954555, by rfl⟩ : syracuseStep 2545481 = 1909111) B1909111
theorem B3561803 : Blo 275825 3561803 := bstep (se 1 (by rfl) ⟨2671352, by rfl⟩ : syracuseStep 3561803 = 5342705) B5342705
theorem B416159 : Blo 275825 416159 := bstep (se 1 (by rfl) ⟨312119, by rfl⟩ : syracuseStep 416159 = 624239) B624239
theorem B20404709 : Blo 275825 20404709 := bstep (se 4 (by rfl) ⟨1912941, by rfl⟩ : syracuseStep 20404709 = 3825883) B3825883
theorem B416231 : Blo 275825 416231 := bstep (se 1 (by rfl) ⟨312173, by rfl⟩ : syracuseStep 416231 = 624347) B624347
theorem B940571 : Blo 275825 940571 := bstep (se 1 (by rfl) ⟨705428, by rfl⟩ : syracuseStep 940571 = 1410857) B1410857
theorem B416975 : Blo 275825 416975 := bstep (se 1 (by rfl) ⟨312731, by rfl⟩ : syracuseStep 416975 = 625463) B625463
theorem B417095 : Blo 275825 417095 := bstep (se 1 (by rfl) ⟨312821, by rfl⟩ : syracuseStep 417095 = 625643) B625643
theorem B417257 : Blo 275825 417257 := bstep (se 2 (by rfl) ⟨156471, by rfl⟩ : syracuseStep 417257 = 312943) B312943
theorem B417401 : Blo 275825 417401 := bstep (se 2 (by rfl) ⟨156525, by rfl⟩ : syracuseStep 417401 = 313051) B313051
theorem B1498745 : Blo 275825 1498745 := bstep (se 2 (by rfl) ⟨562029, by rfl⟩ : syracuseStep 1498745 = 1124059) B1124059
theorem B3825443 : Blo 275825 3825443 := bstep (se 1 (by rfl) ⟨2869082, by rfl⟩ : syracuseStep 3825443 = 5738165) B5738165
theorem B417647 : Blo 275825 417647 := bstep (se 1 (by rfl) ⟨313235, by rfl⟩ : syracuseStep 417647 = 626471) B626471
theorem B418331 : Blo 275825 418331 := bstep (se 1 (by rfl) ⟨313748, by rfl⟩ : syracuseStep 418331 = 627497) B627497
theorem B418511 : Blo 275825 418511 := bstep (se 1 (by rfl) ⟨313883, by rfl⟩ : syracuseStep 418511 = 627767) B627767
theorem B418523 : Blo 275825 418523 := bstep (se 1 (by rfl) ⟨313892, by rfl⟩ : syracuseStep 418523 = 627785) B627785
theorem B418937 : Blo 275825 418937 := bstep (se 2 (by rfl) ⟨157101, by rfl⟩ : syracuseStep 418937 = 314203) B314203
theorem B2679965 : Blo 275825 2679965 := bstep (se 3 (by rfl) ⟨502493, by rfl⟩ : syracuseStep 2679965 = 1004987) B1004987
theorem B5989783 : Blo 275825 5989783 := bstep (se 1 (by rfl) ⟨4492337, by rfl⟩ : syracuseStep 5989783 = 8984675) B8984675
theorem B1074923 : Blo 275825 1074923 := bstep (se 1 (by rfl) ⟨806192, by rfl⟩ : syracuseStep 1074923 = 1612385) B1612385
theorem B1140635 : Blo 275825 1140635 := bstep (se 1 (by rfl) ⟨855476, by rfl⟩ : syracuseStep 1140635 = 1710953) B1710953
theorem B944027 : Blo 275825 944027 := bstep (se 1 (by rfl) ⟨708020, by rfl⟩ : syracuseStep 944027 = 1416041) B1416041
theorem B747643 : Blo 275825 747643 := bstep (se 1 (by rfl) ⟨560732, by rfl⟩ : syracuseStep 747643 = 1121465) B1121465
theorem B10349855 : Blo 275825 10349855 := bstep (se 1 (by rfl) ⟨7762391, by rfl⟩ : syracuseStep 10349855 = 15524783) B15524783
theorem B2387657 : Blo 275825 2387657 := bstep (se 2 (by rfl) ⟨895371, by rfl⟩ : syracuseStep 2387657 = 1790743) B1790743
theorem B1896635 : Blo 275825 1896635 := bstep (se 1 (by rfl) ⟨1422476, by rfl⟩ : syracuseStep 1896635 = 2844953) B2844953
theorem B6025427 : Blo 275825 6025427 := bstep (se 1 (by rfl) ⟨4519070, by rfl⟩ : syracuseStep 6025427 = 9038141) B9038141
theorem B1536641 : Blo 275825 1536641 := bstep (se 2 (by rfl) ⟨576240, by rfl⟩ : syracuseStep 1536641 = 1152481) B1152481
theorem B3535559 : Blo 275825 3535559 := bstep (se 1 (by rfl) ⟨2651669, by rfl⟩ : syracuseStep 3535559 = 5303339) B5303339
theorem B2683655 : Blo 275825 2683655 := bstep (se 1 (by rfl) ⟨2012741, by rfl⟩ : syracuseStep 2683655 = 4025483) B4025483
theorem B2848063 : Blo 275825 2848063 := bstep (se 1 (by rfl) ⟨2136047, by rfl⟩ : syracuseStep 2848063 = 4272095) B4272095
theorem B357979 : Blo 275825 357979 := bstep (se 1 (by rfl) ⟨268484, by rfl⟩ : syracuseStep 357979 = 536969) B536969
theorem B2258887 : Blo 275825 2258887 := bstep (se 1 (by rfl) ⟨1694165, by rfl⟩ : syracuseStep 2258887 = 3388331) B3388331
theorem B620999 : Blo 275825 620999 := bstep (se 1 (by rfl) ⟨465749, by rfl⟩ : syracuseStep 620999 = 931499) B931499
theorem B621161 : Blo 275825 621161 := bstep (se 2 (by rfl) ⟨232935, by rfl⟩ : syracuseStep 621161 = 465871) B465871
theorem B1407617 : Blo 275825 1407617 := bstep (se 2 (by rfl) ⟨527856, by rfl⟩ : syracuseStep 1407617 = 1055713) B1055713
theorem B621215 : Blo 275825 621215 := bstep (se 1 (by rfl) ⟨465911, by rfl⟩ : syracuseStep 621215 = 931823) B931823
theorem B621359 : Blo 275825 621359 := bstep (se 1 (by rfl) ⟨466019, by rfl⟩ : syracuseStep 621359 = 932039) B932039
theorem B621791 : Blo 275825 621791 := bstep (se 1 (by rfl) ⟨466343, by rfl⟩ : syracuseStep 621791 = 932687) B932687
theorem B425191 : Blo 275825 425191 := bstep (se 1 (by rfl) ⟨318893, by rfl⟩ : syracuseStep 425191 = 637787) B637787
theorem B883993 : Blo 275825 883993 := bstep (se 2 (by rfl) ⟨331497, by rfl⟩ : syracuseStep 883993 = 662995) B662995
theorem B1408427 : Blo 275825 1408427 := bstep (se 1 (by rfl) ⟨1056320, by rfl⟩ : syracuseStep 1408427 = 2112641) B2112641
theorem B622007 : Blo 275825 622007 := bstep (se 1 (by rfl) ⟨466505, by rfl⟩ : syracuseStep 622007 = 933011) B933011
theorem B30768569 : Blo 275825 30768569 := bstep (se 2 (by rfl) ⟨11538213, by rfl⟩ : syracuseStep 30768569 = 23076427) B23076427
theorem B622187 : Blo 275825 622187 := bstep (se 1 (by rfl) ⟨466640, by rfl⟩ : syracuseStep 622187 = 933281) B933281
theorem B523999 : Blo 275825 523999 := bstep (se 1 (by rfl) ⟨392999, by rfl⟩ : syracuseStep 523999 = 785999) B785999
theorem B622457 : Blo 275825 622457 := bstep (se 2 (by rfl) ⟨233421, by rfl⟩ : syracuseStep 622457 = 466843) B466843
theorem B622547 : Blo 275825 622547 := bstep (se 1 (by rfl) ⟨466910, by rfl⟩ : syracuseStep 622547 = 933821) B933821
theorem B950399 : Blo 275825 950399 := bstep (se 1 (by rfl) ⟨712799, by rfl⟩ : syracuseStep 950399 = 1425599) B1425599
theorem B721151 : Blo 275825 721151 := bstep (se 1 (by rfl) ⟨540863, by rfl⟩ : syracuseStep 721151 = 1081727) B1081727
theorem B2097575 : Blo 275825 2097575 := bstep (se 1 (by rfl) ⟨1573181, by rfl⟩ : syracuseStep 2097575 = 3146363) B3146363
theorem B885275 : Blo 275825 885275 := bstep (se 1 (by rfl) ⟨663956, by rfl⟩ : syracuseStep 885275 = 1327913) B1327913
theorem B885455 : Blo 275825 885455 := bstep (se 1 (by rfl) ⟨664091, by rfl⟩ : syracuseStep 885455 = 1328183) B1328183
theorem B787583 : Blo 275825 787583 := bstep (se 1 (by rfl) ⟨590687, by rfl⟩ : syracuseStep 787583 = 1181375) B1181375
theorem B25691681 : Blo 275825 25691681 := bstep (se 2 (by rfl) ⟨9634380, by rfl⟩ : syracuseStep 25691681 = 19268761) B19268761
theorem B591943 : Blo 275825 591943 := bstep (se 1 (by rfl) ⟨443957, by rfl⟩ : syracuseStep 591943 = 887915) B887915
theorem B592123 : Blo 275825 592123 := bstep (se 1 (by rfl) ⟨444092, by rfl⟩ : syracuseStep 592123 = 888185) B888185
theorem B625319 : Blo 275825 625319 := bstep (se 1 (by rfl) ⟨468989, by rfl⟩ : syracuseStep 625319 = 937979) B937979
theorem B1051643 : Blo 275825 1051643 := bstep (se 1 (by rfl) ⟨788732, by rfl⟩ : syracuseStep 1051643 = 1577465) B1577465
theorem B1412153 : Blo 275825 1412153 := bstep (se 2 (by rfl) ⟨529557, by rfl⟩ : syracuseStep 1412153 = 1059115) B1059115
theorem B625895 : Blo 275825 625895 := bstep (se 1 (by rfl) ⟨469421, by rfl⟩ : syracuseStep 625895 = 938843) B938843
theorem B790327 : Blo 275825 790327 := bstep (se 1 (by rfl) ⟨592745, by rfl⟩ : syracuseStep 790327 = 1185491) B1185491
theorem B593831 : Blo 275825 593831 := bstep (se 1 (by rfl) ⟨445373, by rfl⟩ : syracuseStep 593831 = 890747) B890747
theorem B593993 : Blo 275825 593993 := bstep (se 2 (by rfl) ⟨222747, by rfl⟩ : syracuseStep 593993 = 445495) B445495
theorem B528457 : Blo 275825 528457 := bstep (se 2 (by rfl) ⟨198171, by rfl⟩ : syracuseStep 528457 = 396343) B396343
theorem B1183835 : Blo 275825 1183835 := bstep (se 1 (by rfl) ⟨887876, by rfl⟩ : syracuseStep 1183835 = 1775753) B1775753
theorem B13603139 : Blo 275825 13603139 := bstep (se 1 (by rfl) ⟨10202354, by rfl⟩ : syracuseStep 13603139 = 20404709) B20404709
theorem B627047 : Blo 275825 627047 := bstep (se 1 (by rfl) ⟨470285, by rfl⟩ : syracuseStep 627047 = 940571) B940571
theorem B16061327 : Blo 275825 16061327 := bstep (se 1 (by rfl) ⟨12045995, by rfl⟩ : syracuseStep 16061327 = 24091991) B24091991
theorem B889825 : Blo 275825 889825 := bstep (se 2 (by rfl) ⟨333684, by rfl⟩ : syracuseStep 889825 = 667369) B667369
theorem B1905697 : Blo 275825 1905697 := bstep (se 2 (by rfl) ⟨714636, by rfl⟩ : syracuseStep 1905697 = 1429273) B1429273
theorem B1415069 : Blo 275825 1415069 := bstep (se 3 (by rfl) ⟨265325, by rfl⟩ : syracuseStep 1415069 = 530651) B530651
theorem B1775981 : Blo 275825 1775981 := bstep (se 3 (by rfl) ⟨332996, by rfl⟩ : syracuseStep 1775981 = 665993) B665993
theorem B760423 : Blo 275825 760423 := bstep (se 1 (by rfl) ⟨570317, by rfl⟩ : syracuseStep 760423 = 1140635) B1140635
theorem B629351 : Blo 275825 629351 := bstep (se 1 (by rfl) ⟨472013, by rfl⟩ : syracuseStep 629351 = 944027) B944027
theorem B629513 : Blo 275825 629513 := bstep (se 2 (by rfl) ⟨236067, by rfl⟩ : syracuseStep 629513 = 472135) B472135
theorem B793415 : Blo 275825 793415 := bstep (se 1 (by rfl) ⟨595061, by rfl⟩ : syracuseStep 793415 = 1190123) B1190123
theorem B3546017 : Blo 275825 3546017 := bstep (se 2 (by rfl) ⟨1329756, by rfl⟩ : syracuseStep 3546017 = 2659513) B2659513
theorem B1186721 : Blo 275825 1186721 := bstep (se 2 (by rfl) ⟨445020, by rfl⟩ : syracuseStep 1186721 = 890041) B890041
theorem B7872815 : Blo 275825 7872815 := bstep (se 1 (by rfl) ⟨5904611, by rfl⟩ : syracuseStep 7872815 = 11809223) B11809223
theorem B1417609 : Blo 275825 1417609 := bstep (se 2 (by rfl) ⟨531603, by rfl⟩ : syracuseStep 1417609 = 1063207) B1063207
theorem B1024427 : Blo 275825 1024427 := bstep (se 1 (by rfl) ⟨768320, by rfl⟩ : syracuseStep 1024427 = 1536641) B1536641
theorem B2106323 : Blo 275825 2106323 := bstep (se 1 (by rfl) ⟨1579742, by rfl⟩ : syracuseStep 2106323 = 3159485) B3159485
theorem B894233 : Blo 275825 894233 := bstep (se 2 (by rfl) ⟨335337, by rfl⟩ : syracuseStep 894233 = 670675) B670675
theorem B468463 : Blo 275825 468463 := bstep (se 1 (by rfl) ⟨351347, by rfl⟩ : syracuseStep 468463 = 702695) B702695
theorem B3548681 : Blo 275825 3548681 := bstep (se 2 (by rfl) ⟨1330755, by rfl⟩ : syracuseStep 3548681 = 2661511) B2661511
theorem B1418777 : Blo 275825 1418777 := bstep (se 2 (by rfl) ⟨532041, by rfl⟩ : syracuseStep 1418777 = 1064083) B1064083
theorem B566921 : Blo 275825 566921 := bstep (se 2 (by rfl) ⟨212595, by rfl⟩ : syracuseStep 566921 = 425191) B425191
theorem B3614557 : Blo 275825 3614557 := bstep (se 3 (by rfl) ⟨677729, by rfl⟩ : syracuseStep 3614557 = 1355459) B1355459
theorem B698665 : Blo 275825 698665 := bstep (se 2 (by rfl) ⟨261999, by rfl⟩ : syracuseStep 698665 = 523999) B523999
theorem B1190447 : Blo 275825 1190447 := bstep (se 1 (by rfl) ⟨892835, by rfl⟩ : syracuseStep 1190447 = 1785671) B1785671
theorem B699455 : Blo 275825 699455 := bstep (se 1 (by rfl) ⟨524591, by rfl⟩ : syracuseStep 699455 = 1049183) B1049183
theorem B1060847 : Blo 275825 1060847 := bstep (se 1 (by rfl) ⟨795635, by rfl⟩ : syracuseStep 1060847 = 1591271) B1591271
theorem B6795251 : Blo 275825 6795251 := bstep (se 1 (by rfl) ⟨5096438, by rfl⟩ : syracuseStep 6795251 = 10192877) B10192877
theorem B471143 : Blo 275825 471143 := bstep (se 1 (by rfl) ⟨353357, by rfl⟩ : syracuseStep 471143 = 706715) B706715
theorem B700559 : Blo 275825 700559 := bstep (se 1 (by rfl) ⟨525419, by rfl⟩ : syracuseStep 700559 = 1050839) B1050839
theorem B1192121 : Blo 275825 1192121 := bstep (se 2 (by rfl) ⟨447045, by rfl⟩ : syracuseStep 1192121 = 894091) B894091
theorem B1782647 : Blo 275825 1782647 := bstep (se 1 (by rfl) ⟨1336985, by rfl⟩ : syracuseStep 1782647 = 2673971) B2673971
theorem B701419 : Blo 275825 701419 := bstep (se 1 (by rfl) ⟨526064, by rfl⟩ : syracuseStep 701419 = 1052129) B1052129
theorem B275839 : Blo 275825 275839 := bstep (se 1 (by rfl) ⟨206879, by rfl⟩ : syracuseStep 275839 = 413759) B413759
theorem B996857 : Blo 275825 996857 := bstep (se 2 (by rfl) ⟨373821, by rfl⟩ : syracuseStep 996857 = 747643) B747643
theorem B275995 : Blo 275825 275995 := bstep (se 1 (by rfl) ⟨206996, by rfl⟩ : syracuseStep 275995 = 413993) B413993
theorem B1193555 : Blo 275825 1193555 := bstep (se 1 (by rfl) ⟨895166, by rfl⟩ : syracuseStep 1193555 = 1790333) B1790333
theorem B276175 : Blo 275825 276175 := bstep (se 1 (by rfl) ⟨207131, by rfl⟩ : syracuseStep 276175 = 414263) B414263
theorem B669599 : Blo 275825 669599 := bstep (se 1 (by rfl) ⟨502199, by rfl⟩ : syracuseStep 669599 = 1004399) B1004399
theorem B276415 : Blo 275825 276415 := bstep (se 1 (by rfl) ⟨207311, by rfl⟩ : syracuseStep 276415 = 414623) B414623
theorem B997363 : Blo 275825 997363 := bstep (se 1 (by rfl) ⟨748022, by rfl⟩ : syracuseStep 997363 = 1496045) B1496045
theorem B4012051 : Blo 275825 4012051 := bstep (se 1 (by rfl) ⟨3009038, by rfl⟩ : syracuseStep 4012051 = 6018077) B6018077
theorem B276543 : Blo 275825 276543 := bstep (se 1 (by rfl) ⟨207407, by rfl⟩ : syracuseStep 276543 = 414815) B414815
theorem B276583 : Blo 275825 276583 := bstep (se 1 (by rfl) ⟨207437, by rfl⟩ : syracuseStep 276583 = 414875) B414875
theorem B669799 : Blo 275825 669799 := bstep (se 1 (by rfl) ⟨502349, by rfl⟩ : syracuseStep 669799 = 1004699) B1004699
theorem B4503761 : Blo 275825 4503761 := bstep (se 2 (by rfl) ⟨1688910, by rfl⟩ : syracuseStep 4503761 = 3377821) B3377821
theorem B7125245 : Blo 275825 7125245 := bstep (se 3 (by rfl) ⟨1335983, by rfl⟩ : syracuseStep 7125245 = 2671967) B2671967
theorem B702857 : Blo 275825 702857 := bstep (se 2 (by rfl) ⟨263571, by rfl⟩ : syracuseStep 702857 = 527143) B527143
theorem B768503 : Blo 275825 768503 := bstep (se 1 (by rfl) ⟨576377, by rfl⟩ : syracuseStep 768503 = 1152755) B1152755
theorem B277039 : Blo 275825 277039 := bstep (se 1 (by rfl) ⟨207779, by rfl⟩ : syracuseStep 277039 = 415559) B415559
theorem B2374535 : Blo 275825 2374535 := bstep (se 1 (by rfl) ⟨1780901, by rfl⟩ : syracuseStep 2374535 = 3561803) B3561803
theorem B277439 : Blo 275825 277439 := bstep (se 1 (by rfl) ⟨208079, by rfl⟩ : syracuseStep 277439 = 416159) B416159
theorem B277487 : Blo 275825 277487 := bstep (se 1 (by rfl) ⟨208115, by rfl⟩ : syracuseStep 277487 = 416231) B416231
theorem B277983 : Blo 275825 277983 := bstep (se 1 (by rfl) ⟨208487, by rfl⟩ : syracuseStep 277983 = 416975) B416975
theorem B278063 : Blo 275825 278063 := bstep (se 1 (by rfl) ⟨208547, by rfl⟩ : syracuseStep 278063 = 417095) B417095
theorem B278171 : Blo 275825 278171 := bstep (se 1 (by rfl) ⟨208628, by rfl⟩ : syracuseStep 278171 = 417257) B417257
theorem B311035 : Blo 275825 311035 := bstep (se 1 (by rfl) ⟨233276, by rfl⟩ : syracuseStep 311035 = 466553) B466553
theorem B999163 : Blo 275825 999163 := bstep (se 1 (by rfl) ⟨749372, by rfl⟩ : syracuseStep 999163 = 1498745) B1498745
theorem B278267 : Blo 275825 278267 := bstep (se 1 (by rfl) ⟨208700, by rfl⟩ : syracuseStep 278267 = 417401) B417401
theorem B704335 : Blo 275825 704335 := bstep (se 1 (by rfl) ⟨528251, by rfl⟩ : syracuseStep 704335 = 1056503) B1056503
theorem B278431 : Blo 275825 278431 := bstep (se 1 (by rfl) ⟨208823, by rfl⟩ : syracuseStep 278431 = 417647) B417647
theorem B278887 : Blo 275825 278887 := bstep (se 1 (by rfl) ⟨209165, by rfl⟩ : syracuseStep 278887 = 418331) B418331
theorem B704983 : Blo 275825 704983 := bstep (se 1 (by rfl) ⟨528737, by rfl⟩ : syracuseStep 704983 = 1057475) B1057475
theorem B279007 : Blo 275825 279007 := bstep (se 1 (by rfl) ⟨209255, by rfl⟩ : syracuseStep 279007 = 418511) B418511
theorem B279015 : Blo 275825 279015 := bstep (se 1 (by rfl) ⟨209261, by rfl⟩ : syracuseStep 279015 = 418523) B418523
theorem B377563 : Blo 275825 377563 := bstep (se 1 (by rfl) ⟨283172, by rfl⟩ : syracuseStep 377563 = 566345) B566345
theorem B279291 : Blo 275825 279291 := bstep (se 1 (by rfl) ⟨209468, by rfl⟩ : syracuseStep 279291 = 418937) B418937
theorem B705287 : Blo 275825 705287 := bstep (se 1 (by rfl) ⟨528965, by rfl⟩ : syracuseStep 705287 = 1057931) B1057931
theorem B1786643 : Blo 275825 1786643 := bstep (se 1 (by rfl) ⟨1339982, by rfl⟩ : syracuseStep 1786643 = 2679965) B2679965
theorem B312187 : Blo 275825 312187 := bstep (se 1 (by rfl) ⟨234140, by rfl⟩ : syracuseStep 312187 = 468281) B468281
theorem B9684139 : Blo 275825 9684139 := bstep (se 1 (by rfl) ⟨7263104, by rfl⟩ : syracuseStep 9684139 = 14526209) B14526209
theorem B2245913 : Blo 275825 2245913 := bstep (se 2 (by rfl) ⟨842217, by rfl⟩ : syracuseStep 2245913 = 1684435) B1684435
theorem B477305 : Blo 275825 477305 := bstep (se 2 (by rfl) ⟨178989, by rfl⟩ : syracuseStep 477305 = 357979) B357979
theorem B6899903 : Blo 275825 6899903 := bstep (se 1 (by rfl) ⟨5174927, by rfl⟩ : syracuseStep 6899903 = 10349855) B10349855
theorem B313663 : Blo 275825 313663 := bstep (se 1 (by rfl) ⟨235247, by rfl⟩ : syracuseStep 313663 = 470495) B470495
theorem B313807 : Blo 275825 313807 := bstep (se 1 (by rfl) ⟨235355, by rfl⟩ : syracuseStep 313807 = 470711) B470711
theorem B1591771 : Blo 275825 1591771 := bstep (se 1 (by rfl) ⟨1193828, by rfl⟩ : syracuseStep 1591771 = 2387657) B2387657
theorem B707201 : Blo 275825 707201 := bstep (se 2 (by rfl) ⟨265200, by rfl⟩ : syracuseStep 707201 = 530401) B530401
theorem B3558113 : Blo 275825 3558113 := bstep (se 2 (by rfl) ⟨1334292, by rfl⟩ : syracuseStep 3558113 = 2668585) B2668585
theorem B1264423 : Blo 275825 1264423 := bstep (se 1 (by rfl) ⟨948317, by rfl⟩ : syracuseStep 1264423 = 1896635) B1896635
theorem B4016951 : Blo 275825 4016951 := bstep (se 1 (by rfl) ⟨3012713, by rfl⟩ : syracuseStep 4016951 = 6025427) B6025427
theorem B1789103 : Blo 275825 1789103 := bstep (se 1 (by rfl) ⟨1341827, by rfl⟩ : syracuseStep 1789103 = 2683655) B2683655
theorem B708011 : Blo 275825 708011 := bstep (se 1 (by rfl) ⟨531008, by rfl⟩ : syracuseStep 708011 = 1062017) B1062017
theorem B413999 : Blo 275825 413999 := bstep (se 1 (by rfl) ⟨310499, by rfl⟩ : syracuseStep 413999 = 620999) B620999
theorem B315695 : Blo 275825 315695 := bstep (se 1 (by rfl) ⟨236771, by rfl⟩ : syracuseStep 315695 = 473543) B473543
theorem B414107 : Blo 275825 414107 := bstep (se 1 (by rfl) ⟨310580, by rfl⟩ : syracuseStep 414107 = 621161) B621161
theorem B938411 : Blo 275825 938411 := bstep (se 1 (by rfl) ⟨703808, by rfl⟩ : syracuseStep 938411 = 1407617) B1407617
theorem B414143 : Blo 275825 414143 := bstep (se 1 (by rfl) ⟨310607, by rfl⟩ : syracuseStep 414143 = 621215) B621215
theorem B414239 : Blo 275825 414239 := bstep (se 1 (by rfl) ⟨310679, by rfl⟩ : syracuseStep 414239 = 621359) B621359
theorem B414527 : Blo 275825 414527 := bstep (se 1 (by rfl) ⟨310895, by rfl⟩ : syracuseStep 414527 = 621791) B621791
theorem B938951 : Blo 275825 938951 := bstep (se 1 (by rfl) ⟨704213, by rfl⟩ : syracuseStep 938951 = 1408427) B1408427
theorem B414671 : Blo 275825 414671 := bstep (se 1 (by rfl) ⟨311003, by rfl⟩ : syracuseStep 414671 = 622007) B622007
theorem B414761 : Blo 275825 414761 := bstep (se 2 (by rfl) ⟨155535, by rfl⟩ : syracuseStep 414761 = 311071) B311071
theorem B414791 : Blo 275825 414791 := bstep (se 1 (by rfl) ⟨311093, by rfl⟩ : syracuseStep 414791 = 622187) B622187
theorem B414971 : Blo 275825 414971 := bstep (se 1 (by rfl) ⟨311228, by rfl⟩ : syracuseStep 414971 = 622457) B622457
theorem B415031 : Blo 275825 415031 := bstep (se 1 (by rfl) ⟨311273, by rfl⟩ : syracuseStep 415031 = 622547) B622547
theorem B415337 : Blo 275825 415337 := bstep (se 2 (by rfl) ⟨155751, by rfl⟩ : syracuseStep 415337 = 311503) B311503
theorem B350335 : Blo 275825 350335 := bstep (se 1 (by rfl) ⟨262751, by rfl⟩ : syracuseStep 350335 = 525503) B525503
theorem B415871 : Blo 275825 415871 := bstep (se 1 (by rfl) ⟨311903, by rfl⟩ : syracuseStep 415871 = 623807) B623807
theorem B940247 : Blo 275825 940247 := bstep (se 1 (by rfl) ⟨705185, by rfl⟩ : syracuseStep 940247 = 1410371) B1410371
theorem B415967 : Blo 275825 415967 := bstep (se 1 (by rfl) ⟨311975, by rfl⟩ : syracuseStep 415967 = 623951) B623951
theorem B416027 : Blo 275825 416027 := bstep (se 1 (by rfl) ⟨312020, by rfl⟩ : syracuseStep 416027 = 624041) B624041
theorem B416351 : Blo 275825 416351 := bstep (se 1 (by rfl) ⟨312263, by rfl⟩ : syracuseStep 416351 = 624527) B624527
theorem B6019717 : Blo 275825 6019717 := bstep (se 4 (by rfl) ⟨564348, by rfl⟩ : syracuseStep 6019717 = 1128697) B1128697
theorem B416447 : Blo 275825 416447 := bstep (se 1 (by rfl) ⟨312335, by rfl⟩ : syracuseStep 416447 = 624671) B624671
theorem B416489 : Blo 275825 416489 := bstep (se 2 (by rfl) ⟨156183, by rfl⟩ : syracuseStep 416489 = 312367) B312367
theorem B940787 : Blo 275825 940787 := bstep (se 1 (by rfl) ⟨705590, by rfl⟩ : syracuseStep 940787 = 1411181) B1411181
theorem B416615 : Blo 275825 416615 := bstep (se 1 (by rfl) ⟨312461, by rfl⟩ : syracuseStep 416615 = 624923) B624923
theorem B842633 : Blo 275825 842633 := bstep (se 2 (by rfl) ⟨315987, by rfl⟩ : syracuseStep 842633 = 631975) B631975
theorem B416681 : Blo 275825 416681 := bstep (se 2 (by rfl) ⟨156255, by rfl⟩ : syracuseStep 416681 = 312511) B312511
theorem B1399841 : Blo 275825 1399841 := bstep (se 2 (by rfl) ⟨524940, by rfl⟩ : syracuseStep 1399841 = 1049881) B1049881
theorem B416831 : Blo 275825 416831 := bstep (se 1 (by rfl) ⟨312623, by rfl⟩ : syracuseStep 416831 = 625247) B625247
theorem B416873 : Blo 275825 416873 := bstep (se 2 (by rfl) ⟨156327, by rfl⟩ : syracuseStep 416873 = 312655) B312655
theorem B7986377 : Blo 275825 7986377 := bstep (se 2 (by rfl) ⟨2994891, by rfl⟩ : syracuseStep 7986377 = 5989783) B5989783
theorem B416999 : Blo 275825 416999 := bstep (se 1 (by rfl) ⟨312749, by rfl⟩ : syracuseStep 416999 = 625499) B625499
theorem B3792167 : Blo 275825 3792167 := bstep (se 1 (by rfl) ⟨2844125, by rfl⟩ : syracuseStep 3792167 = 5688251) B5688251
theorem B1629521 : Blo 275825 1629521 := bstep (se 2 (by rfl) ⟨611070, by rfl⟩ : syracuseStep 1629521 = 1222141) B1222141
theorem B51010955 : Blo 275825 51010955 := bstep (se 1 (by rfl) ⟨38258216, by rfl⟩ : syracuseStep 51010955 = 76516433) B76516433
theorem B1400327 : Blo 275825 1400327 := bstep (se 1 (by rfl) ⟨1050245, by rfl⟩ : syracuseStep 1400327 = 2100491) B2100491
theorem B417503 : Blo 275825 417503 := bstep (se 1 (by rfl) ⟨313127, by rfl⟩ : syracuseStep 417503 = 626255) B626255
theorem B417833 : Blo 275825 417833 := bstep (se 2 (by rfl) ⟨156687, by rfl⟩ : syracuseStep 417833 = 313375) B313375
theorem B417863 : Blo 275825 417863 := bstep (se 1 (by rfl) ⟨313397, by rfl⟩ : syracuseStep 417863 = 626795) B626795
theorem B417899 : Blo 275825 417899 := bstep (se 1 (by rfl) ⟨313424, by rfl⟩ : syracuseStep 417899 = 626849) B626849
theorem B417983 : Blo 275825 417983 := bstep (se 1 (by rfl) ⟨313487, by rfl⟩ : syracuseStep 417983 = 626975) B626975
theorem B418169 : Blo 275825 418169 := bstep (se 2 (by rfl) ⟨156813, by rfl⟩ : syracuseStep 418169 = 313627) B313627
theorem B1401299 : Blo 275825 1401299 := bstep (se 1 (by rfl) ⟨1050974, by rfl⟩ : syracuseStep 1401299 = 2101949) B2101949
theorem B352927 : Blo 275825 352927 := bstep (se 1 (by rfl) ⟨264695, by rfl⟩ : syracuseStep 352927 = 529391) B529391
theorem B418463 : Blo 275825 418463 := bstep (se 1 (by rfl) ⟨313847, by rfl⟩ : syracuseStep 418463 = 627695) B627695
theorem B3171149 : Blo 275825 3171149 := bstep (se 3 (by rfl) ⟨594590, by rfl⟩ : syracuseStep 3171149 = 1189181) B1189181
theorem B418799 : Blo 275825 418799 := bstep (se 1 (by rfl) ⟨314099, by rfl⟩ : syracuseStep 418799 = 628199) B628199
theorem B418907 : Blo 275825 418907 := bstep (se 1 (by rfl) ⟨314180, by rfl⟩ : syracuseStep 418907 = 628361) B628361
theorem B418919 : Blo 275825 418919 := bstep (se 1 (by rfl) ⟨314189, by rfl⟩ : syracuseStep 418919 = 628379) B628379
theorem B844967 : Blo 275825 844967 := bstep (se 1 (by rfl) ⟨633725, by rfl⟩ : syracuseStep 844967 = 1267451) B1267451
theorem B1696987 : Blo 275825 1696987 := bstep (se 1 (by rfl) ⟨1272740, by rfl⟩ : syracuseStep 1696987 = 2545481) B2545481
theorem B419051 : Blo 275825 419051 := bstep (se 1 (by rfl) ⟨314288, by rfl⟩ : syracuseStep 419051 = 628577) B628577
theorem B419183 : Blo 275825 419183 := bstep (se 1 (by rfl) ⟨314387, by rfl⟩ : syracuseStep 419183 = 628775) B628775
theorem B17229277 : Blo 275825 17229277 := bstep (se 3 (by rfl) ⟨3230489, by rfl⟩ : syracuseStep 17229277 = 6460979) B6460979
theorem B419303 : Blo 275825 419303 := bstep (se 1 (by rfl) ⟨314477, by rfl⟩ : syracuseStep 419303 = 628955) B628955
theorem B419435 : Blo 275825 419435 := bstep (se 1 (by rfl) ⟨314576, by rfl⟩ : syracuseStep 419435 = 629153) B629153
theorem B419483 : Blo 275825 419483 := bstep (se 1 (by rfl) ⟨314612, by rfl⟩ : syracuseStep 419483 = 629225) B629225
theorem B419705 : Blo 275825 419705 := bstep (se 2 (by rfl) ⟨157389, by rfl⟩ : syracuseStep 419705 = 314779) B314779
theorem B4876199 : Blo 275825 4876199 := bstep (se 1 (by rfl) ⟨3657149, by rfl⟩ : syracuseStep 4876199 = 7314299) B7314299
theorem B2123819 : Blo 275825 2123819 := bstep (se 1 (by rfl) ⟨1592864, by rfl⟩ : syracuseStep 2123819 = 3185729) B3185729
theorem B6744161 : Blo 275825 6744161 := bstep (se 2 (by rfl) ⟨2529060, by rfl⟩ : syracuseStep 6744161 = 5058121) B5058121
theorem B2550295 : Blo 275825 2550295 := bstep (se 1 (by rfl) ⟨1912721, by rfl⟩ : syracuseStep 2550295 = 3825443) B3825443
theorem B748379 : Blo 275825 748379 := bstep (se 1 (by rfl) ⟨561284, by rfl⟩ : syracuseStep 748379 = 1122569) B1122569
theorem B716615 : Blo 275825 716615 := bstep (se 1 (by rfl) ⟨537461, by rfl⟩ : syracuseStep 716615 = 1074923) B1074923
theorem B3633547 : Blo 275825 3633547 := bstep (se 1 (by rfl) ⟨2725160, by rfl⟩ : syracuseStep 3633547 = 5450321) B5450321
theorem B3797417 : Blo 275825 3797417 := bstep (se 2 (by rfl) ⟨1424031, by rfl⟩ : syracuseStep 3797417 = 2848063) B2848063
theorem B750023 : Blo 275825 750023 := bstep (se 1 (by rfl) ⟨562517, by rfl⟩ : syracuseStep 750023 = 1125035) B1125035
theorem B3011849 : Blo 275825 3011849 := bstep (se 2 (by rfl) ⟨1129443, by rfl⟩ : syracuseStep 3011849 = 2258887) B2258887
theorem B184251743 : Blo 275825 184251743 := bstep (se 1 (by rfl) ⟨138188807, by rfl⟩ : syracuseStep 184251743 = 276377615) B276377615
theorem B2357039 : Blo 275825 2357039 := bstep (se 1 (by rfl) ⟨1767779, by rfl⟩ : syracuseStep 2357039 = 3535559) B3535559
theorem B620711 : Blo 275825 620711 := bstep (se 1 (by rfl) ⟨465533, by rfl⟩ : syracuseStep 620711 = 931067) B931067
theorem B48953621 : Blo 275825 48953621 := bstep (se 6 (by rfl) ⟨1147350, by rfl⟩ : syracuseStep 48953621 = 2294701) B2294701
theorem B1178657 : Blo 275825 1178657 := bstep (se 2 (by rfl) ⟨441996, by rfl⟩ : syracuseStep 1178657 = 883993) B883993
theorem B883943 : Blo 275825 883943 := bstep (se 1 (by rfl) ⟨662957, by rfl⟩ : syracuseStep 883943 = 1325915) B1325915
theorem B949739 : Blo 275825 949739 := bstep (se 1 (by rfl) ⟨712304, by rfl⟩ : syracuseStep 949739 = 1424609) B1424609
theorem B20512379 : Blo 275825 20512379 := bstep (se 1 (by rfl) ⟨15384284, by rfl⟩ : syracuseStep 20512379 = 30768569) B30768569
theorem B590183 : Blo 275825 590183 := bstep (se 1 (by rfl) ⟨442637, by rfl⟩ : syracuseStep 590183 = 885275) B885275
theorem B590303 : Blo 275825 590303 := bstep (se 1 (by rfl) ⟨442727, by rfl⟩ : syracuseStep 590303 = 885455) B885455
theorem B3572261 : Blo 275825 3572261 := bstep (se 4 (by rfl) ⟨334899, by rfl⟩ : syracuseStep 3572261 = 669799) B669799
theorem B525055 : Blo 275825 525055 := bstep (se 1 (by rfl) ⟨393791, by rfl⟩ : syracuseStep 525055 = 787583) B787583
theorem B12912185 : Blo 275825 12912185 := bstep (se 2 (by rfl) ⟨4842069, by rfl⟩ : syracuseStep 12912185 = 9684139) B9684139
theorem B2262649 : Blo 275825 2262649 := bstep (se 2 (by rfl) ⟨848493, by rfl⟩ : syracuseStep 2262649 = 1696987) B1696987
theorem B22972369 : Blo 275825 22972369 := bstep (se 2 (by rfl) ⟨8614638, by rfl⟩ : syracuseStep 22972369 = 17229277) B17229277
theorem B624617 : Blo 275825 624617 := bstep (se 2 (by rfl) ⟨234231, by rfl⟩ : syracuseStep 624617 = 468463) B468463
theorem B4819409 : Blo 275825 4819409 := bstep (se 2 (by rfl) ⟨1807278, by rfl⟩ : syracuseStep 4819409 = 3614557) B3614557
theorem B789223 : Blo 275825 789223 := bstep (se 1 (by rfl) ⟨591917, by rfl⟩ : syracuseStep 789223 = 1183835) B1183835
theorem B789257 : Blo 275825 789257 := bstep (se 2 (by rfl) ⟨295971, by rfl⟩ : syracuseStep 789257 = 591943) B591943
theorem B625607 : Blo 275825 625607 := bstep (se 1 (by rfl) ⟨469205, by rfl⟩ : syracuseStep 625607 = 938411) B938411
theorem B789497 : Blo 275825 789497 := bstep (se 2 (by rfl) ⟨296061, by rfl⟩ : syracuseStep 789497 = 592123) B592123
theorem B625967 : Blo 275825 625967 := bstep (se 1 (by rfl) ⟨469475, by rfl⟩ : syracuseStep 625967 = 938951) B938951
theorem B626831 : Blo 275825 626831 := bstep (se 1 (by rfl) ⟨470123, by rfl⟩ : syracuseStep 626831 = 940247) B940247
theorem B3182813 : Blo 275825 3182813 := bstep (se 3 (by rfl) ⟨596777, by rfl⟩ : syracuseStep 3182813 = 1193555) B1193555
theorem B1183987 : Blo 275825 1183987 := bstep (se 1 (by rfl) ⟨887990, by rfl⟩ : syracuseStep 1183987 = 1775981) B1775981
theorem B627191 : Blo 275825 627191 := bstep (se 1 (by rfl) ⟨470393, by rfl⟩ : syracuseStep 627191 = 940787) B940787
theorem B528943 : Blo 275825 528943 := bstep (se 1 (by rfl) ⟨396707, by rfl⟩ : syracuseStep 528943 = 793415) B793415
theorem B561755 : Blo 275825 561755 := bstep (se 1 (by rfl) ⟨421316, by rfl⟩ : syracuseStep 561755 = 842633) B842633
theorem B2364011 : Blo 275825 2364011 := bstep (se 1 (by rfl) ⟨1773008, by rfl⟩ : syracuseStep 2364011 = 3546017) B3546017
theorem B791147 : Blo 275825 791147 := bstep (se 1 (by rfl) ⟨593360, by rfl⟩ : syracuseStep 791147 = 1186721) B1186721
theorem B2528111 : Blo 275825 2528111 := bstep (se 1 (by rfl) ⟨1896083, by rfl⟩ : syracuseStep 2528111 = 3792167) B3792167
theorem B1086347 : Blo 275825 1086347 := bstep (se 1 (by rfl) ⟨814760, by rfl⟩ : syracuseStep 1086347 = 1629521) B1629521
theorem B1053769 : Blo 275825 1053769 := bstep (se 2 (by rfl) ⟨395163, by rfl⟩ : syracuseStep 1053769 = 790327) B790327
theorem B5248543 : Blo 275825 5248543 := bstep (se 1 (by rfl) ⟨3936407, by rfl⟩ : syracuseStep 5248543 = 7872815) B7872815
theorem B563311 : Blo 275825 563311 := bstep (se 1 (by rfl) ⟨422483, by rfl⟩ : syracuseStep 563311 = 844967) B844967
theorem B596155 : Blo 275825 596155 := bstep (se 1 (by rfl) ⟨447116, by rfl⟩ : syracuseStep 596155 = 894233) B894233
theorem B2365787 : Blo 275825 2365787 := bstep (se 1 (by rfl) ⟨1774340, by rfl⟩ : syracuseStep 2365787 = 3548681) B3548681
theorem B3250799 : Blo 275825 3250799 := bstep (se 1 (by rfl) ⟨2438099, by rfl⟩ : syracuseStep 3250799 = 4876199) B4876199
theorem B1186433 : Blo 275825 1186433 := bstep (se 2 (by rfl) ⟨444912, by rfl⟩ : syracuseStep 1186433 = 889825) B889825
theorem B1415879 : Blo 275825 1415879 := bstep (se 1 (by rfl) ⟨1061909, by rfl⟩ : syracuseStep 1415879 = 2123819) B2123819
theorem B4496107 : Blo 275825 4496107 := bstep (se 1 (by rfl) ⟨3372080, by rfl⟩ : syracuseStep 4496107 = 6744161) B6744161
theorem B793631 : Blo 275825 793631 := bstep (se 1 (by rfl) ⟨595223, by rfl⟩ : syracuseStep 793631 = 1190447) B1190447
theorem B498919 : Blo 275825 498919 := bstep (se 1 (by rfl) ⟨374189, by rfl⟩ : syracuseStep 498919 = 748379) B748379
theorem B466303 : Blo 275825 466303 := bstep (se 1 (by rfl) ⟨349727, by rfl⟩ : syracuseStep 466303 = 699455) B699455
theorem B4530167 : Blo 275825 4530167 := bstep (se 1 (by rfl) ⟨3397625, by rfl⟩ : syracuseStep 4530167 = 6795251) B6795251
theorem B5349401 : Blo 275825 5349401 := bstep (se 2 (by rfl) ⟨2006025, by rfl⟩ : syracuseStep 5349401 = 4012051) B4012051
theorem B467039 : Blo 275825 467039 := bstep (se 1 (by rfl) ⟨350279, by rfl⟩ : syracuseStep 467039 = 700559) B700559
theorem B794747 : Blo 275825 794747 := bstep (se 1 (by rfl) ⟨596060, by rfl⟩ : syracuseStep 794747 = 1192121) B1192121
theorem B467113 : Blo 275825 467113 := bstep (se 2 (by rfl) ⟨175167, by rfl⟩ : syracuseStep 467113 = 350335) B350335
theorem B2531611 : Blo 275825 2531611 := bstep (se 1 (by rfl) ⟨1898708, by rfl⟩ : syracuseStep 2531611 = 3797417) B3797417
theorem B500015 : Blo 275825 500015 := bstep (se 1 (by rfl) ⟨375011, by rfl⟩ : syracuseStep 500015 = 750023) B750023
theorem B1188431 : Blo 275825 1188431 := bstep (se 1 (by rfl) ⟨891323, by rfl⟩ : syracuseStep 1188431 = 1782647) B1782647
theorem B2007899 : Blo 275825 2007899 := bstep (se 1 (by rfl) ⟨1505924, by rfl⟩ : syracuseStep 2007899 = 3011849) B3011849
theorem B664571 : Blo 275825 664571 := bstep (se 1 (by rfl) ⟨498428, by rfl⟩ : syracuseStep 664571 = 996857) B996857
theorem B2532637 : Blo 275825 2532637 := bstep (se 3 (by rfl) ⟨474869, by rfl⟩ : syracuseStep 2532637 = 949739) B949739
theorem B468571 : Blo 275825 468571 := bstep (se 1 (by rfl) ⟨351428, by rfl⟩ : syracuseStep 468571 = 702857) B702857
theorem B1583023 : Blo 275825 1583023 := bstep (se 1 (by rfl) ⟨1187267, by rfl⟩ : syracuseStep 1583023 = 2374535) B2374535
theorem B13674919 : Blo 275825 13674919 := bstep (se 1 (by rfl) ⟨10256189, by rfl⟩ : syracuseStep 13674919 = 20512379) B20512379
theorem B1583549 : Blo 275825 1583549 := bstep (se 3 (by rfl) ⟨296915, by rfl⟩ : syracuseStep 1583549 = 593831) B593831
theorem B633599 : Blo 275825 633599 := bstep (se 1 (by rfl) ⟨475199, by rfl⟩ : syracuseStep 633599 = 950399) B950399
theorem B1583981 : Blo 275825 1583981 := bstep (se 3 (by rfl) ⟨296996, by rfl⟩ : syracuseStep 1583981 = 593993) B593993
theorem B470191 : Blo 275825 470191 := bstep (se 1 (by rfl) ⟨352643, by rfl⟩ : syracuseStep 470191 = 705287) B705287
theorem B1191095 : Blo 275825 1191095 := bstep (se 1 (by rfl) ⟨893321, by rfl⟩ : syracuseStep 1191095 = 1786643) B1786643
theorem B470569 : Blo 275825 470569 := bstep (se 2 (by rfl) ⟨176463, by rfl⟩ : syracuseStep 470569 = 352927) B352927
theorem B503417 : Blo 275825 503417 := bstep (se 2 (by rfl) ⟨188781, by rfl⟩ : syracuseStep 503417 = 377563) B377563
theorem B2731805 : Blo 275825 2731805 := bstep (se 3 (by rfl) ⟨512213, by rfl⟩ : syracuseStep 2731805 = 1024427) B1024427
theorem B4599935 : Blo 275825 4599935 := bstep (se 1 (by rfl) ⟨3449951, by rfl⟩ : syracuseStep 4599935 = 6899903) B6899903
theorem B471467 : Blo 275825 471467 := bstep (se 1 (by rfl) ⟨353600, by rfl⟩ : syracuseStep 471467 = 707201) B707201
theorem B2372075 : Blo 275825 2372075 := bstep (se 1 (by rfl) ⟨1779056, by rfl⟩ : syracuseStep 2372075 = 3558113) B3558113
theorem B701095 : Blo 275825 701095 := bstep (se 1 (by rfl) ⟨525821, by rfl⟩ : syracuseStep 701095 = 1051643) B1051643
theorem B1192735 : Blo 275825 1192735 := bstep (se 1 (by rfl) ⟨894551, by rfl⟩ : syracuseStep 1192735 = 1789103) B1789103
theorem B472007 : Blo 275825 472007 := bstep (se 1 (by rfl) ⟨354005, by rfl⟩ : syracuseStep 472007 = 708011) B708011
theorem B275999 : Blo 275825 275999 := bstep (se 1 (by rfl) ⟨206999, by rfl⟩ : syracuseStep 275999 = 413999) B413999
theorem B276071 : Blo 275825 276071 := bstep (se 1 (by rfl) ⟨207053, by rfl⟩ : syracuseStep 276071 = 414107) B414107
theorem B276095 : Blo 275825 276095 := bstep (se 1 (by rfl) ⟨207071, by rfl⟩ : syracuseStep 276095 = 414143) B414143
theorem B276159 : Blo 275825 276159 := bstep (se 1 (by rfl) ⟨207119, by rfl⟩ : syracuseStep 276159 = 414239) B414239
theorem B931553 : Blo 275825 931553 := bstep (se 2 (by rfl) ⟨349332, by rfl⟩ : syracuseStep 931553 = 698665) B698665
theorem B276351 : Blo 275825 276351 := bstep (se 1 (by rfl) ⟨207263, by rfl⟩ : syracuseStep 276351 = 414527) B414527
theorem B276447 : Blo 275825 276447 := bstep (se 1 (by rfl) ⟨207335, by rfl⟩ : syracuseStep 276447 = 414671) B414671
theorem B276507 : Blo 275825 276507 := bstep (se 1 (by rfl) ⟨207380, by rfl⟩ : syracuseStep 276507 = 414761) B414761
theorem B276527 : Blo 275825 276527 := bstep (se 1 (by rfl) ⟨207395, by rfl⟩ : syracuseStep 276527 = 414791) B414791
theorem B276647 : Blo 275825 276647 := bstep (se 1 (by rfl) ⟨207485, by rfl⟩ : syracuseStep 276647 = 414971) B414971
theorem B276687 : Blo 275825 276687 := bstep (se 1 (by rfl) ⟨207515, by rfl⟩ : syracuseStep 276687 = 415031) B415031
theorem B1685897 : Blo 275825 1685897 := bstep (se 2 (by rfl) ⟨632211, by rfl⟩ : syracuseStep 1685897 = 1264423) B1264423
theorem B276891 : Blo 275825 276891 := bstep (se 1 (by rfl) ⟨207668, by rfl⟩ : syracuseStep 276891 = 415337) B415337
theorem B277247 : Blo 275825 277247 := bstep (se 1 (by rfl) ⟨207935, by rfl⟩ : syracuseStep 277247 = 415871) B415871
theorem B277311 : Blo 275825 277311 := bstep (se 1 (by rfl) ⟨207983, by rfl⟩ : syracuseStep 277311 = 415967) B415967
theorem B277351 : Blo 275825 277351 := bstep (se 1 (by rfl) ⟨208013, by rfl⟩ : syracuseStep 277351 = 416027) B416027
theorem B277567 : Blo 275825 277567 := bstep (se 1 (by rfl) ⟨208175, by rfl⟩ : syracuseStep 277567 = 416351) B416351
theorem B277631 : Blo 275825 277631 := bstep (se 1 (by rfl) ⟨208223, by rfl⟩ : syracuseStep 277631 = 416447) B416447
theorem B277659 : Blo 275825 277659 := bstep (se 1 (by rfl) ⟨208244, by rfl⟩ : syracuseStep 277659 = 416489) B416489
theorem B277743 : Blo 275825 277743 := bstep (se 1 (by rfl) ⟨208307, by rfl⟩ : syracuseStep 277743 = 416615) B416615
theorem B277787 : Blo 275825 277787 := bstep (se 1 (by rfl) ⟨208340, by rfl⟩ : syracuseStep 277787 = 416681) B416681
theorem B933227 : Blo 275825 933227 := bstep (se 1 (by rfl) ⟨699920, by rfl⟩ : syracuseStep 933227 = 1399841) B1399841
theorem B277887 : Blo 275825 277887 := bstep (se 1 (by rfl) ⟨208415, by rfl⟩ : syracuseStep 277887 = 416831) B416831
theorem B277915 : Blo 275825 277915 := bstep (se 1 (by rfl) ⟨208436, by rfl⟩ : syracuseStep 277915 = 416873) B416873
theorem B5324251 : Blo 275825 5324251 := bstep (se 1 (by rfl) ⟨3993188, by rfl⟩ : syracuseStep 5324251 = 7986377) B7986377
theorem B277999 : Blo 275825 277999 := bstep (se 1 (by rfl) ⟨208499, by rfl⟩ : syracuseStep 277999 = 416999) B416999
theorem B933551 : Blo 275825 933551 := bstep (se 1 (by rfl) ⟨700163, by rfl⟩ : syracuseStep 933551 = 1400327) B1400327
theorem B278335 : Blo 275825 278335 := bstep (se 1 (by rfl) ⟨208751, by rfl⟩ : syracuseStep 278335 = 417503) B417503
theorem B278555 : Blo 275825 278555 := bstep (se 1 (by rfl) ⟨208916, by rfl⟩ : syracuseStep 278555 = 417833) B417833
theorem B278575 : Blo 275825 278575 := bstep (se 1 (by rfl) ⟨208931, by rfl⟩ : syracuseStep 278575 = 417863) B417863
theorem B278599 : Blo 275825 278599 := bstep (se 1 (by rfl) ⟨208949, by rfl⟩ : syracuseStep 278599 = 417899) B417899
theorem B704609 : Blo 275825 704609 := bstep (se 2 (by rfl) ⟨264228, by rfl⟩ : syracuseStep 704609 = 528457) B528457
theorem B278655 : Blo 275825 278655 := bstep (se 1 (by rfl) ⟨208991, by rfl⟩ : syracuseStep 278655 = 417983) B417983
theorem B278779 : Blo 275825 278779 := bstep (se 1 (by rfl) ⟨209084, by rfl⟩ : syracuseStep 278779 = 418169) B418169
theorem B934199 : Blo 275825 934199 := bstep (se 1 (by rfl) ⟨700649, by rfl⟩ : syracuseStep 934199 = 1401299) B1401299
theorem B278975 : Blo 275825 278975 := bstep (se 1 (by rfl) ⟨209231, by rfl⟩ : syracuseStep 278975 = 418463) B418463
theorem B2114099 : Blo 275825 2114099 := bstep (se 1 (by rfl) ⟨1585574, by rfl⟩ : syracuseStep 2114099 = 3171149) B3171149
theorem B279199 : Blo 275825 279199 := bstep (se 1 (by rfl) ⟨209399, by rfl⟩ : syracuseStep 279199 = 418799) B418799
theorem B279271 : Blo 275825 279271 := bstep (se 1 (by rfl) ⟨209453, by rfl⟩ : syracuseStep 279271 = 418907) B418907
theorem B279279 : Blo 275825 279279 := bstep (se 1 (by rfl) ⟨209459, by rfl⟩ : syracuseStep 279279 = 418919) B418919
theorem B279367 : Blo 275825 279367 := bstep (se 1 (by rfl) ⟨209525, by rfl⟩ : syracuseStep 279367 = 419051) B419051
theorem B279455 : Blo 275825 279455 := bstep (se 1 (by rfl) ⟨209591, by rfl⟩ : syracuseStep 279455 = 419183) B419183
theorem B279535 : Blo 275825 279535 := bstep (se 1 (by rfl) ⟨209651, by rfl⟩ : syracuseStep 279535 = 419303) B419303
theorem B279623 : Blo 275825 279623 := bstep (se 1 (by rfl) ⟨209717, by rfl⟩ : syracuseStep 279623 = 419435) B419435
theorem B377947 : Blo 275825 377947 := bstep (se 1 (by rfl) ⟨283460, by rfl⟩ : syracuseStep 377947 = 566921) B566921
theorem B279655 : Blo 275825 279655 := bstep (se 1 (by rfl) ⟨209741, by rfl⟩ : syracuseStep 279655 = 419483) B419483
theorem B279803 : Blo 275825 279803 := bstep (se 1 (by rfl) ⟨209852, by rfl⟩ : syracuseStep 279803 = 419705) B419705
theorem B935225 : Blo 275825 935225 := bstep (se 2 (by rfl) ⟨350709, by rfl⟩ : syracuseStep 935225 = 701419) B701419
theorem B2540929 : Blo 275825 2540929 := bstep (se 2 (by rfl) ⟨952848, by rfl⟩ : syracuseStep 2540929 = 1905697) B1905697
theorem B477743 : Blo 275825 477743 := bstep (se 1 (by rfl) ⟨358307, by rfl⟩ : syracuseStep 477743 = 716615) B716615
theorem B1329817 : Blo 275825 1329817 := bstep (se 2 (by rfl) ⟨498681, by rfl⟩ : syracuseStep 1329817 = 997363) B997363
theorem B707231 : Blo 275825 707231 := bstep (se 1 (by rfl) ⟨530423, by rfl⟩ : syracuseStep 707231 = 1060847) B1060847
theorem B314095 : Blo 275825 314095 := bstep (se 1 (by rfl) ⟨235571, by rfl⟩ : syracuseStep 314095 = 471143) B471143
theorem B122834495 : Blo 275825 122834495 := bstep (se 1 (by rfl) ⟨92125871, by rfl⟩ : syracuseStep 122834495 = 184251743) B184251743
theorem B446399 : Blo 275825 446399 := bstep (se 1 (by rfl) ⟨334799, by rfl⟩ : syracuseStep 446399 = 669599) B669599
theorem B413807 : Blo 275825 413807 := bstep (se 1 (by rfl) ⟨310355, by rfl⟩ : syracuseStep 413807 = 620711) B620711
theorem B3002507 : Blo 275825 3002507 := bstep (se 1 (by rfl) ⟨2251880, by rfl⟩ : syracuseStep 3002507 = 4503761) B4503761
theorem B512335 : Blo 275825 512335 := bstep (se 1 (by rfl) ⟨384251, by rfl⟩ : syracuseStep 512335 = 768503) B768503
theorem B414713 : Blo 275825 414713 := bstep (se 2 (by rfl) ⟨155517, by rfl⟩ : syracuseStep 414713 = 311035) B311035
theorem B1332217 : Blo 275825 1332217 := bstep (se 2 (by rfl) ⟨499581, by rfl⟩ : syracuseStep 1332217 = 999163) B999163
theorem B939113 : Blo 275825 939113 := bstep (se 2 (by rfl) ⟨352167, by rfl⟩ : syracuseStep 939113 = 704335) B704335
theorem B480767 : Blo 275825 480767 := bstep (se 1 (by rfl) ⟨360575, by rfl⟩ : syracuseStep 480767 = 721151) B721151
theorem B1398383 : Blo 275825 1398383 := bstep (se 1 (by rfl) ⟨1048787, by rfl⟩ : syracuseStep 1398383 = 2097575) B2097575
theorem B1890145 : Blo 275825 1890145 := bstep (se 2 (by rfl) ⟨708804, by rfl⟩ : syracuseStep 1890145 = 1417609) B1417609
theorem B939977 : Blo 275825 939977 := bstep (se 2 (by rfl) ⟨352491, by rfl⟩ : syracuseStep 939977 = 704983) B704983
theorem B841853 : Blo 275825 841853 := bstep (se 3 (by rfl) ⟨157847, by rfl⟩ : syracuseStep 841853 = 315695) B315695
theorem B1497275 : Blo 275825 1497275 := bstep (se 1 (by rfl) ⟨1122956, by rfl⟩ : syracuseStep 1497275 = 2245913) B2245913
theorem B17127787 : Blo 275825 17127787 := bstep (se 1 (by rfl) ⟨12845840, by rfl⟩ : syracuseStep 17127787 = 25691681) B25691681
theorem B416249 : Blo 275825 416249 := bstep (se 2 (by rfl) ⟨156093, by rfl⟩ : syracuseStep 416249 = 312187) B312187
theorem B318203 : Blo 275825 318203 := bstep (se 1 (by rfl) ⟨238652, by rfl⟩ : syracuseStep 318203 = 477305) B477305
theorem B416879 : Blo 275825 416879 := bstep (se 1 (by rfl) ⟨312659, by rfl⟩ : syracuseStep 416879 = 625319) B625319
theorem B2677967 : Blo 275825 2677967 := bstep (se 1 (by rfl) ⟨2008475, by rfl⟩ : syracuseStep 2677967 = 4016951) B4016951
theorem B941435 : Blo 275825 941435 := bstep (se 1 (by rfl) ⟨706076, by rfl⟩ : syracuseStep 941435 = 1412153) B1412153
theorem B417263 : Blo 275825 417263 := bstep (se 1 (by rfl) ⟨312947, by rfl⟩ : syracuseStep 417263 = 625895) B625895
theorem B9068759 : Blo 275825 9068759 := bstep (se 1 (by rfl) ⟨6801569, by rfl⟩ : syracuseStep 9068759 = 13603139) B13603139
theorem B418031 : Blo 275825 418031 := bstep (se 1 (by rfl) ⟨313523, by rfl⟩ : syracuseStep 418031 = 627047) B627047
theorem B418217 : Blo 275825 418217 := bstep (se 2 (by rfl) ⟨156831, by rfl⟩ : syracuseStep 418217 = 313663) B313663
theorem B10707551 : Blo 275825 10707551 := bstep (se 1 (by rfl) ⟨8030663, by rfl⟩ : syracuseStep 10707551 = 16061327) B16061327
theorem B418409 : Blo 275825 418409 := bstep (se 2 (by rfl) ⟨156903, by rfl⟩ : syracuseStep 418409 = 313807) B313807
theorem B2122361 : Blo 275825 2122361 := bstep (se 2 (by rfl) ⟨795885, by rfl⟩ : syracuseStep 2122361 = 1591771) B1591771
theorem B3400393 : Blo 275825 3400393 := bstep (se 2 (by rfl) ⟨1275147, by rfl⟩ : syracuseStep 3400393 = 2550295) B2550295
theorem B943379 : Blo 275825 943379 := bstep (se 1 (by rfl) ⟨707534, by rfl⟩ : syracuseStep 943379 = 1415069) B1415069
theorem B419567 : Blo 275825 419567 := bstep (se 1 (by rfl) ⟨314675, by rfl⟩ : syracuseStep 419567 = 629351) B629351
theorem B419675 : Blo 275825 419675 := bstep (se 1 (by rfl) ⟨314756, by rfl⟩ : syracuseStep 419675 = 629513) B629513
theorem B34007303 : Blo 275825 34007303 := bstep (se 1 (by rfl) ⟨25505477, by rfl⟩ : syracuseStep 34007303 = 51010955) B51010955
theorem B4844729 : Blo 275825 4844729 := bstep (se 2 (by rfl) ⟨1816773, by rfl⟩ : syracuseStep 4844729 = 3633547) B3633547
theorem B1404215 : Blo 275825 1404215 := bstep (se 1 (by rfl) ⟨1053161, by rfl⟩ : syracuseStep 1404215 = 2106323) B2106323
theorem B945851 : Blo 275825 945851 := bstep (se 1 (by rfl) ⟨709388, by rfl⟩ : syracuseStep 945851 = 1418777) B1418777
theorem B1013897 : Blo 275825 1013897 := bstep (se 2 (by rfl) ⟨380211, by rfl⟩ : syracuseStep 1013897 = 760423) B760423
theorem B8026289 : Blo 275825 8026289 := bstep (se 2 (by rfl) ⟨3009858, by rfl⟩ : syracuseStep 8026289 = 6019717) B6019717
theorem B1571359 : Blo 275825 1571359 := bstep (se 1 (by rfl) ⟨1178519, by rfl⟩ : syracuseStep 1571359 = 2357039) B2357039
theorem B4750163 : Blo 275825 4750163 := bstep (se 1 (by rfl) ⟨3562622, by rfl⟩ : syracuseStep 4750163 = 7125245) B7125245
theorem B32635747 : Blo 275825 32635747 := bstep (se 1 (by rfl) ⟨24476810, by rfl⟩ : syracuseStep 32635747 = 48953621) B48953621
theorem B785771 : Blo 275825 785771 := bstep (se 1 (by rfl) ⟨589328, by rfl⟩ : syracuseStep 785771 = 1178657) B1178657
theorem B589295 : Blo 275825 589295 := bstep (se 1 (by rfl) ⟨441971, by rfl⟩ : syracuseStep 589295 = 883943) B883943
theorem B622799 : Blo 275825 622799 := bstep (se 1 (by rfl) ⟨467099, by rfl⟩ : syracuseStep 622799 = 934199) B934199
theorem B622817 : Blo 275825 622817 := bstep (se 2 (by rfl) ⟨233556, by rfl⟩ : syracuseStep 622817 = 467113) B467113
theorem B393455 : Blo 275825 393455 := bstep (se 1 (by rfl) ⟨295091, by rfl⟩ : syracuseStep 393455 = 590183) B590183
theorem B393535 : Blo 275825 393535 := bstep (se 1 (by rfl) ⟨295151, by rfl⟩ : syracuseStep 393535 = 590303) B590303
theorem B1409399 : Blo 275825 1409399 := bstep (se 1 (by rfl) ⟨1057049, by rfl⟩ : syracuseStep 1409399 = 2114099) B2114099
theorem B3375481 : Blo 275825 3375481 := bstep (se 2 (by rfl) ⟨1265805, by rfl⟩ : syracuseStep 3375481 = 2531611) B2531611
theorem B623483 : Blo 275825 623483 := bstep (se 1 (by rfl) ⟨467612, by rfl⟩ : syracuseStep 623483 = 935225) B935225
theorem B3212939 : Blo 275825 3212939 := bstep (se 1 (by rfl) ⟨2409704, by rfl⟩ : syracuseStep 3212939 = 4819409) B4819409
theorem B3376849 : Blo 275825 3376849 := bstep (se 2 (by rfl) ⟨1266318, by rfl⟩ : syracuseStep 3376849 = 2532637) B2532637
theorem B526171 : Blo 275825 526171 := bstep (se 1 (by rfl) ⟨394628, by rfl⟩ : syracuseStep 526171 = 789257) B789257
theorem B526331 : Blo 275825 526331 := bstep (se 1 (by rfl) ⟨394748, by rfl⟩ : syracuseStep 526331 = 789497) B789497
theorem B624761 : Blo 275825 624761 := bstep (se 2 (by rfl) ⟨234285, by rfl⟩ : syracuseStep 624761 = 468571) B468571
theorem B3016865 : Blo 275825 3016865 := bstep (se 2 (by rfl) ⟨1131324, by rfl⟩ : syracuseStep 3016865 = 2262649) B2262649
theorem B81889663 : Blo 275825 81889663 := bstep (se 1 (by rfl) ⟨61417247, by rfl⟩ : syracuseStep 81889663 = 122834495) B122834495
theorem B297599 : Blo 275825 297599 := bstep (se 1 (by rfl) ⟨223199, by rfl⟩ : syracuseStep 297599 = 446399) B446399
theorem B1772189 : Blo 275825 1772189 := bstep (se 3 (by rfl) ⟨332285, by rfl⟩ : syracuseStep 1772189 = 664571) B664571
theorem B2001671 : Blo 275825 2001671 := bstep (se 1 (by rfl) ⟨1501253, by rfl⟩ : syracuseStep 2001671 = 3002507) B3002507
theorem B1576007 : Blo 275825 1576007 := bstep (se 1 (by rfl) ⟨1182005, by rfl⟩ : syracuseStep 1576007 = 2364011) B2364011
theorem B724231 : Blo 275825 724231 := bstep (se 1 (by rfl) ⟨543173, by rfl⟩ : syracuseStep 724231 = 1086347) B1086347
theorem B626075 : Blo 275825 626075 := bstep (se 1 (by rfl) ⟨469556, by rfl⟩ : syracuseStep 626075 = 939113) B939113
theorem B1773089 : Blo 275825 1773089 := bstep (se 2 (by rfl) ⟨664908, by rfl⟩ : syracuseStep 1773089 = 1329817) B1329817
theorem B1052297 : Blo 275825 1052297 := bstep (se 2 (by rfl) ⟨394611, by rfl⟩ : syracuseStep 1052297 = 789223) B789223
theorem B626651 : Blo 275825 626651 := bstep (se 1 (by rfl) ⟨469988, by rfl⟩ : syracuseStep 626651 = 939977) B939977
theorem B1577191 : Blo 275825 1577191 := bstep (se 1 (by rfl) ⟨1182893, by rfl⟩ : syracuseStep 1577191 = 2365787) B2365787
theorem B626921 : Blo 275825 626921 := bstep (se 2 (by rfl) ⟨235095, by rfl⟩ : syracuseStep 626921 = 470191) B470191
theorem B2167199 : Blo 275825 2167199 := bstep (se 1 (by rfl) ⟨1625399, by rfl⟩ : syracuseStep 2167199 = 3250799) B3250799
theorem B790955 : Blo 275825 790955 := bstep (se 1 (by rfl) ⟨593216, by rfl⟩ : syracuseStep 790955 = 1186433) B1186433
theorem B529087 : Blo 275825 529087 := bstep (se 1 (by rfl) ⟨396815, by rfl⟩ : syracuseStep 529087 = 793631) B793631
theorem B627425 : Blo 275825 627425 := bstep (se 2 (by rfl) ⟨235284, by rfl⟩ : syracuseStep 627425 = 470569) B470569
theorem B627623 : Blo 275825 627623 := bstep (se 1 (by rfl) ⟨470717, by rfl⟩ : syracuseStep 627623 = 941435) B941435
theorem B3020111 : Blo 275825 3020111 := bstep (se 1 (by rfl) ⟨2265083, by rfl⟩ : syracuseStep 3020111 = 4530167) B4530167
theorem B529831 : Blo 275825 529831 := bstep (se 1 (by rfl) ⟨397373, by rfl⟩ : syracuseStep 529831 = 794747) B794747
theorem B333343 : Blo 275825 333343 := bstep (se 1 (by rfl) ⟨250007, by rfl⟩ : syracuseStep 333343 = 500015) B500015
theorem B1578649 : Blo 275825 1578649 := bstep (se 2 (by rfl) ⟨591993, by rfl⟩ : syracuseStep 1578649 = 1183987) B1183987
theorem B792287 : Blo 275825 792287 := bstep (se 1 (by rfl) ⟨594215, by rfl⟩ : syracuseStep 792287 = 1188431) B1188431
theorem B1414907 : Blo 275825 1414907 := bstep (se 1 (by rfl) ⟨1061180, by rfl⟩ : syracuseStep 1414907 = 2122361) B2122361
theorem B628919 : Blo 275825 628919 := bstep (se 1 (by rfl) ⟨471689, by rfl⟩ : syracuseStep 628919 = 943379) B943379
theorem B1776289 : Blo 275825 1776289 := bstep (se 2 (by rfl) ⟨666108, by rfl⟩ : syracuseStep 1776289 = 1332217) B1332217
theorem B1055699 : Blo 275825 1055699 := bstep (se 1 (by rfl) ⟨791774, by rfl⟩ : syracuseStep 1055699 = 1583549) B1583549
theorem B1055987 : Blo 275825 1055987 := bstep (se 1 (by rfl) ⟨791990, by rfl⟩ : syracuseStep 1055987 = 1583981) B1583981
theorem B794063 : Blo 275825 794063 := bstep (se 1 (by rfl) ⟨595547, by rfl⟩ : syracuseStep 794063 = 1191095) B1191095
theorem B335611 : Blo 275825 335611 := bstep (se 1 (by rfl) ⟨251708, by rfl⟩ : syracuseStep 335611 = 503417) B503417
theorem B794873 : Blo 275825 794873 := bstep (se 2 (by rfl) ⟨298077, by rfl⟩ : syracuseStep 794873 = 596155) B596155
theorem B1581383 : Blo 275825 1581383 := bstep (se 1 (by rfl) ⟨1186037, by rfl⟩ : syracuseStep 1581383 = 2372075) B2372075
theorem B12919277 : Blo 275825 12919277 := bstep (se 3 (by rfl) ⟨2422364, by rfl⟩ : syracuseStep 12919277 = 4844729) B4844729
theorem B5350859 : Blo 275825 5350859 := bstep (se 1 (by rfl) ⟨4013144, by rfl⟩ : syracuseStep 5350859 = 8026289) B8026289
theorem B1123931 : Blo 275825 1123931 := bstep (se 1 (by rfl) ⟨842948, by rfl⟩ : syracuseStep 1123931 = 1685897) B1685897
theorem B665225 : Blo 275825 665225 := bstep (se 2 (by rfl) ⟨249459, by rfl⟩ : syracuseStep 665225 = 498919) B498919
theorem B469739 : Blo 275825 469739 := bstep (se 1 (by rfl) ⟨352304, by rfl⟩ : syracuseStep 469739 = 704609) B704609
theorem B4533857 : Blo 275825 4533857 := bstep (se 2 (by rfl) ⟨1700196, by rfl⟩ : syracuseStep 4533857 = 3400393) B3400393
theorem B700073 : Blo 275825 700073 := bstep (se 2 (by rfl) ⟨262527, by rfl⟩ : syracuseStep 700073 = 525055) B525055
theorem B503929 : Blo 275825 503929 := bstep (se 2 (by rfl) ⟨188973, by rfl⟩ : syracuseStep 503929 = 377947) B377947
theorem B2109725 : Blo 275825 2109725 := bstep (se 3 (by rfl) ⟨395573, by rfl⟩ : syracuseStep 2109725 = 791147) B791147
theorem B2732453 : Blo 275825 2732453 := bstep (se 4 (by rfl) ⟨256167, by rfl⟩ : syracuseStep 2732453 = 512335) B512335
theorem B471487 : Blo 275825 471487 := bstep (se 1 (by rfl) ⟨353615, by rfl⟩ : syracuseStep 471487 = 707231) B707231
theorem B3387905 : Blo 275825 3387905 := bstep (se 2 (by rfl) ⟨1270464, by rfl⟩ : syracuseStep 3387905 = 2540929) B2540929
theorem B2110697 : Blo 275825 2110697 := bstep (se 2 (by rfl) ⟨791511, by rfl⟩ : syracuseStep 2110697 = 1583023) B1583023
theorem B275871 : Blo 275825 275871 := bstep (se 1 (by rfl) ⟨206903, by rfl⟩ : syracuseStep 275871 = 413807) B413807
theorem B18233225 : Blo 275825 18233225 := bstep (se 2 (by rfl) ⟨6837459, by rfl⟩ : syracuseStep 18233225 = 13674919) B13674919
theorem B1685407 : Blo 275825 1685407 := bstep (se 1 (by rfl) ⟨1264055, by rfl⟩ : syracuseStep 1685407 = 2528111) B2528111
theorem B276475 : Blo 275825 276475 := bstep (se 1 (by rfl) ⟨207356, by rfl⟩ : syracuseStep 276475 = 414713) B414713
theorem B932255 : Blo 275825 932255 := bstep (se 1 (by rfl) ⟨699191, by rfl⟩ : syracuseStep 932255 = 1398383) B1398383
theorem B998183 : Blo 275825 998183 := bstep (se 1 (by rfl) ⟨748637, by rfl⟩ : syracuseStep 998183 = 1497275) B1497275
theorem B277499 : Blo 275825 277499 := bstep (se 1 (by rfl) ⟨208124, by rfl⟩ : syracuseStep 277499 = 416249) B416249
theorem B277919 : Blo 275825 277919 := bstep (se 1 (by rfl) ⟨208439, by rfl⟩ : syracuseStep 277919 = 416879) B416879
theorem B1785311 : Blo 275825 1785311 := bstep (se 1 (by rfl) ⟨1338983, by rfl⟩ : syracuseStep 1785311 = 2677967) B2677967
theorem B278175 : Blo 275825 278175 := bstep (se 1 (by rfl) ⟨208631, by rfl⟩ : syracuseStep 278175 = 417263) B417263
theorem B5128181 : Blo 275825 5128181 := bstep (se 5 (by rfl) ⟨240383, by rfl⟩ : syracuseStep 5128181 = 480767) B480767
theorem B311359 : Blo 275825 311359 := bstep (se 1 (by rfl) ⟨233519, by rfl⟩ : syracuseStep 311359 = 467039) B467039
theorem B6045839 : Blo 275825 6045839 := bstep (se 1 (by rfl) ⟨4534379, by rfl⟩ : syracuseStep 6045839 = 9068759) B9068759
theorem B278687 : Blo 275825 278687 := bstep (se 1 (by rfl) ⟨209015, by rfl⟩ : syracuseStep 278687 = 418031) B418031
theorem B278811 : Blo 275825 278811 := bstep (se 1 (by rfl) ⟨209108, by rfl⟩ : syracuseStep 278811 = 418217) B418217
theorem B2244941 : Blo 275825 2244941 := bstep (se 3 (by rfl) ⟨420926, by rfl⟩ : syracuseStep 2244941 = 841853) B841853
theorem B2703725 : Blo 275825 2703725 := bstep (se 3 (by rfl) ⟨506948, by rfl⟩ : syracuseStep 2703725 = 1013897) B1013897
theorem B278939 : Blo 275825 278939 := bstep (se 1 (by rfl) ⟨209204, by rfl⟩ : syracuseStep 278939 = 418409) B418409
theorem B705257 : Blo 275825 705257 := bstep (se 2 (by rfl) ⟨264471, by rfl⟩ : syracuseStep 705257 = 528943) B528943
theorem B934793 : Blo 275825 934793 := bstep (se 2 (by rfl) ⟨350547, by rfl⟩ : syracuseStep 934793 = 701095) B701095
theorem B1590313 : Blo 275825 1590313 := bstep (se 2 (by rfl) ⟨596367, by rfl⟩ : syracuseStep 1590313 = 1192735) B1192735
theorem B279711 : Blo 275825 279711 := bstep (se 1 (by rfl) ⟨209783, by rfl⟩ : syracuseStep 279711 = 419567) B419567
theorem B279783 : Blo 275825 279783 := bstep (se 1 (by rfl) ⟨209837, by rfl⟩ : syracuseStep 279783 = 419675) B419675
theorem B6998057 : Blo 275825 6998057 := bstep (se 2 (by rfl) ⟨2624271, by rfl⟩ : syracuseStep 6998057 = 5248543) B5248543
theorem B936143 : Blo 275825 936143 := bstep (se 1 (by rfl) ⟨702107, by rfl⟩ : syracuseStep 936143 = 1404215) B1404215
theorem B1821203 : Blo 275825 1821203 := bstep (se 1 (by rfl) ⟨1365902, by rfl⟩ : syracuseStep 1821203 = 2731805) B2731805
theorem B3394165 : Blo 275825 3394165 := bstep (se 5 (by rfl) ⟨159101, by rfl⟩ : syracuseStep 3394165 = 318203) B318203
theorem B3066623 : Blo 275825 3066623 := bstep (se 1 (by rfl) ⟨2299967, by rfl⟩ : syracuseStep 3066623 = 4599935) B4599935
theorem B314311 : Blo 275825 314311 := bstep (se 1 (by rfl) ⟨235733, by rfl⟩ : syracuseStep 314311 = 471467) B471467
theorem B314671 : Blo 275825 314671 := bstep (se 1 (by rfl) ⟨236003, by rfl⟩ : syracuseStep 314671 = 472007) B472007
theorem B10080773 : Blo 275825 10080773 := bstep (se 4 (by rfl) ⟨945072, by rfl⟩ : syracuseStep 10080773 = 1890145) B1890145
theorem B3166775 : Blo 275825 3166775 := bstep (se 1 (by rfl) ⟨2375081, by rfl⟩ : syracuseStep 3166775 = 4750163) B4750163
theorem B7099001 : Blo 275825 7099001 := bstep (se 2 (by rfl) ⟨2662125, by rfl⟩ : syracuseStep 7099001 = 5324251) B5324251
theorem B2381507 : Blo 275825 2381507 := bstep (se 1 (by rfl) ⟨1786130, by rfl⟩ : syracuseStep 2381507 = 3572261) B3572261
theorem B8608123 : Blo 275825 8608123 := bstep (se 1 (by rfl) ⟨6456092, by rfl⟩ : syracuseStep 8608123 = 12912185) B12912185
theorem B416411 : Blo 275825 416411 := bstep (se 1 (by rfl) ⟨312308, by rfl⟩ : syracuseStep 416411 = 624617) B624617
theorem B1498013 : Blo 275825 1498013 := bstep (se 3 (by rfl) ⟨280877, by rfl⟩ : syracuseStep 1498013 = 561755) B561755
theorem B417071 : Blo 275825 417071 := bstep (se 1 (by rfl) ⟨312803, by rfl⟩ : syracuseStep 417071 = 625607) B625607
theorem B417311 : Blo 275825 417311 := bstep (se 1 (by rfl) ⟨312983, by rfl⟩ : syracuseStep 417311 = 625967) B625967
theorem B30629825 : Blo 275825 30629825 := bstep (se 2 (by rfl) ⟨11486184, by rfl⟩ : syracuseStep 30629825 = 22972369) B22972369
theorem B417887 : Blo 275825 417887 := bstep (se 1 (by rfl) ⟨313415, by rfl⟩ : syracuseStep 417887 = 626831) B626831
theorem B2121875 : Blo 275825 2121875 := bstep (se 1 (by rfl) ⟨1591406, by rfl⟩ : syracuseStep 2121875 = 3182813) B3182813
theorem B418127 : Blo 275825 418127 := bstep (se 1 (by rfl) ⟨313595, by rfl⟩ : syracuseStep 418127 = 627191) B627191
theorem B418793 : Blo 275825 418793 := bstep (se 2 (by rfl) ⟨157047, by rfl⟩ : syracuseStep 418793 = 314095) B314095
theorem B943919 : Blo 275825 943919 := bstep (se 1 (by rfl) ⟨707939, by rfl⟩ : syracuseStep 943919 = 1415879) B1415879
theorem B3566267 : Blo 275825 3566267 := bstep (se 1 (by rfl) ⟨2674700, by rfl⟩ : syracuseStep 3566267 = 5349401) B5349401
theorem B7138367 : Blo 275825 7138367 := bstep (se 1 (by rfl) ⟨5353775, by rfl⟩ : syracuseStep 7138367 = 10707551) B10707551
theorem B1338599 : Blo 275825 1338599 := bstep (se 1 (by rfl) ⟨1003949, by rfl⟩ : syracuseStep 1338599 = 2007899) B2007899
theorem B1405025 : Blo 275825 1405025 := bstep (se 2 (by rfl) ⟨526884, by rfl⟩ : syracuseStep 1405025 = 1053769) B1053769
theorem B1273981 : Blo 275825 1273981 := bstep (se 3 (by rfl) ⟨238871, by rfl⟩ : syracuseStep 1273981 = 477743) B477743
theorem B22671535 : Blo 275825 22671535 := bstep (se 1 (by rfl) ⟨17003651, by rfl⟩ : syracuseStep 22671535 = 34007303) B34007303
theorem B422399 : Blo 275825 422399 := bstep (se 1 (by rfl) ⟨316799, by rfl⟩ : syracuseStep 422399 = 633599) B633599
theorem B751081 : Blo 275825 751081 := bstep (se 2 (by rfl) ⟨281655, by rfl⟩ : syracuseStep 751081 = 563311) B563311
theorem B22837049 : Blo 275825 22837049 := bstep (se 2 (by rfl) ⟨8563893, by rfl⟩ : syracuseStep 22837049 = 17127787) B17127787
theorem B2095145 : Blo 275825 2095145 := bstep (se 2 (by rfl) ⟨785679, by rfl⟩ : syracuseStep 2095145 = 1571359) B1571359
theorem B5994809 : Blo 275825 5994809 := bstep (se 2 (by rfl) ⟨2248053, by rfl⟩ : syracuseStep 5994809 = 4496107) B4496107
theorem B43514329 : Blo 275825 43514329 := bstep (se 2 (by rfl) ⟨16317873, by rfl⟩ : syracuseStep 43514329 = 32635747) B32635747
theorem B621035 : Blo 275825 621035 := bstep (se 1 (by rfl) ⟨465776, by rfl⟩ : syracuseStep 621035 = 931553) B931553
theorem B2522269 : Blo 275825 2522269 := bstep (se 3 (by rfl) ⟨472925, by rfl⟩ : syracuseStep 2522269 = 945851) B945851
theorem B621737 : Blo 275825 621737 := bstep (se 2 (by rfl) ⟨233151, by rfl⟩ : syracuseStep 621737 = 466303) B466303
theorem B523847 : Blo 275825 523847 := bstep (se 1 (by rfl) ⟨392885, by rfl⟩ : syracuseStep 523847 = 785771) B785771
theorem B622151 : Blo 275825 622151 := bstep (se 1 (by rfl) ⟨466613, by rfl⟩ : syracuseStep 622151 = 933227) B933227
theorem B392863 : Blo 275825 392863 := bstep (se 1 (by rfl) ⟨294647, by rfl⟩ : syracuseStep 392863 = 589295) B589295
theorem B622367 : Blo 275825 622367 := bstep (se 1 (by rfl) ⟨466775, by rfl⟩ : syracuseStep 622367 = 933551) B933551
theorem B4030559 : Blo 275825 4030559 := bstep (se 1 (by rfl) ⟨3022919, by rfl⟩ : syracuseStep 4030559 = 6045839) B6045839
theorem B1802483 : Blo 275825 1802483 := bstep (se 1 (by rfl) ⟨1351862, by rfl⟩ : syracuseStep 1802483 = 2703725) B2703725
theorem B524713 : Blo 275825 524713 := bstep (se 2 (by rfl) ⟨196767, by rfl⟩ : syracuseStep 524713 = 393535) B393535
theorem B623195 : Blo 275825 623195 := bstep (se 1 (by rfl) ⟨467396, by rfl⟩ : syracuseStep 623195 = 934793) B934793
theorem B1049213 : Blo 275825 1049213 := bstep (se 3 (by rfl) ⟨196727, by rfl⟩ : syracuseStep 1049213 = 393455) B393455
theorem B624095 : Blo 275825 624095 := bstep (se 1 (by rfl) ⟨468071, by rfl⟩ : syracuseStep 624095 = 936143) B936143
theorem B1214135 : Blo 275825 1214135 := bstep (se 1 (by rfl) ⟨910601, by rfl⟩ : syracuseStep 1214135 = 1821203) B1821203
theorem B1181459 : Blo 275825 1181459 := bstep (se 1 (by rfl) ⟨886094, by rfl⟩ : syracuseStep 1181459 = 1772189) B1772189
theorem B1050671 : Blo 275825 1050671 := bstep (se 1 (by rfl) ⟨788003, by rfl⟩ : syracuseStep 1050671 = 1576007) B1576007
theorem B1182059 : Blo 275825 1182059 := bstep (se 1 (by rfl) ⟨886544, by rfl⟩ : syracuseStep 1182059 = 1773089) B1773089
theorem B1444799 : Blo 275825 1444799 := bstep (se 1 (by rfl) ⟨1083599, by rfl⟩ : syracuseStep 1444799 = 2167199) B2167199
theorem B527303 : Blo 275825 527303 := bstep (se 1 (by rfl) ⟨395477, by rfl⟩ : syracuseStep 527303 = 790955) B790955
theorem B6720515 : Blo 275825 6720515 := bstep (se 1 (by rfl) ⟨5040386, by rfl⟩ : syracuseStep 6720515 = 10080773) B10080773
theorem B109186217 : Blo 275825 109186217 := bstep (se 2 (by rfl) ⟨40944831, by rfl⟩ : syracuseStep 109186217 = 81889663) B81889663
theorem B4525553 : Blo 275825 4525553 := bstep (se 2 (by rfl) ⟨1697082, by rfl⟩ : syracuseStep 4525553 = 3394165) B3394165
theorem B528191 : Blo 275825 528191 := bstep (se 1 (by rfl) ⟨396143, by rfl⟩ : syracuseStep 528191 = 792287) B792287
theorem B20419883 : Blo 275825 20419883 := bstep (se 1 (by rfl) ⟨15314912, by rfl⟩ : syracuseStep 20419883 = 30629825) B30629825
theorem B1414583 : Blo 275825 1414583 := bstep (se 1 (by rfl) ⟨1060937, by rfl⟩ : syracuseStep 1414583 = 2121875) B2121875
theorem B529915 : Blo 275825 529915 := bstep (se 1 (by rfl) ⟨397436, by rfl⟩ : syracuseStep 529915 = 794873) B794873
theorem B1054255 : Blo 275825 1054255 := bstep (se 1 (by rfl) ⟨790691, by rfl⟩ : syracuseStep 1054255 = 1581383) B1581383
theorem B2102921 : Blo 275825 2102921 := bstep (se 2 (by rfl) ⟨788595, by rfl⟩ : syracuseStep 2102921 = 1577191) B1577191
theorem B628649 : Blo 275825 628649 := bstep (se 2 (by rfl) ⟨235743, by rfl⟩ : syracuseStep 628649 = 471487) B471487
theorem B629279 : Blo 275825 629279 := bstep (se 1 (by rfl) ⟨471959, by rfl⟩ : syracuseStep 629279 = 943919) B943919
theorem B793597 : Blo 275825 793597 := bstep (se 3 (by rfl) ⟨148799, by rfl⟩ : syracuseStep 793597 = 297599) B297599
theorem B4758911 : Blo 275825 4758911 := bstep (se 1 (by rfl) ⟨3569183, by rfl⟩ : syracuseStep 4758911 = 7138367) B7138367
theorem B2661821 : Blo 275825 2661821 := bstep (se 3 (by rfl) ⟨499091, by rfl⟩ : syracuseStep 2661821 = 998183) B998183
theorem B892399 : Blo 275825 892399 := bstep (se 1 (by rfl) ⟨669299, by rfl⟩ : syracuseStep 892399 = 1338599) B1338599
theorem B2104865 : Blo 275825 2104865 := bstep (se 2 (by rfl) ⟨789324, by rfl⟩ : syracuseStep 2104865 = 1578649) B1578649
theorem B3022571 : Blo 275825 3022571 := bstep (se 1 (by rfl) ⟨2266928, by rfl⟩ : syracuseStep 3022571 = 4533857) B4533857
theorem B466715 : Blo 275825 466715 := bstep (se 1 (by rfl) ⟨350036, by rfl⟩ : syracuseStep 466715 = 700073) B700073
theorem B11477497 : Blo 275825 11477497 := bstep (se 2 (by rfl) ⟨4304061, by rfl⟩ : syracuseStep 11477497 = 8608123) B8608123
theorem B2368385 : Blo 275825 2368385 := bstep (se 2 (by rfl) ⟨888144, by rfl⟩ : syracuseStep 2368385 = 1776289) B1776289
theorem B1190207 : Blo 275825 1190207 := bstep (se 1 (by rfl) ⟨892655, by rfl⟩ : syracuseStep 1190207 = 1785311) B1785311
theorem B3418787 : Blo 275825 3418787 := bstep (se 1 (by rfl) ⟨2564090, by rfl⟩ : syracuseStep 3418787 = 5128181) B5128181
theorem B470171 : Blo 275825 470171 := bstep (se 1 (by rfl) ⟨352628, by rfl⟩ : syracuseStep 470171 = 705257) B705257
theorem B4500641 : Blo 275825 4500641 := bstep (se 2 (by rfl) ⟨1687740, by rfl⟩ : syracuseStep 4500641 = 3375481) B3375481
theorem B2141959 : Blo 275825 2141959 := bstep (se 1 (by rfl) ⟨1606469, by rfl⟩ : syracuseStep 2141959 = 3212939) B3212939
theorem B4665371 : Blo 275825 4665371 := bstep (se 1 (by rfl) ⟨3499028, by rfl⟩ : syracuseStep 4665371 = 6998057) B6998057
theorem B2011243 : Blo 275825 2011243 := bstep (se 1 (by rfl) ⟨1508432, by rfl⟩ : syracuseStep 2011243 = 3016865) B3016865
theorem B2044415 : Blo 275825 2044415 := bstep (se 1 (by rfl) ⟨1533311, by rfl⟩ : syracuseStep 2044415 = 3066623) B3066623
theorem B4502465 : Blo 275825 4502465 := bstep (se 2 (by rfl) ⟨1688424, by rfl⟩ : syracuseStep 4502465 = 3376849) B3376849
theorem B701531 : Blo 275825 701531 := bstep (se 1 (by rfl) ⟨526148, by rfl⟩ : syracuseStep 701531 = 1052297) B1052297
theorem B701561 : Blo 275825 701561 := bstep (se 2 (by rfl) ⟨263085, by rfl⟩ : syracuseStep 701561 = 526171) B526171
theorem B2111183 : Blo 275825 2111183 := bstep (se 1 (by rfl) ⟨1583387, by rfl⟩ : syracuseStep 2111183 = 3166775) B3166775
theorem B4732667 : Blo 275825 4732667 := bstep (se 1 (by rfl) ⟨3549500, by rfl⟩ : syracuseStep 4732667 = 7099001) B7099001
theorem B2013407 : Blo 275825 2013407 := bstep (se 1 (by rfl) ⟨1510055, by rfl⟩ : syracuseStep 2013407 = 3020111) B3020111
theorem B1587671 : Blo 275825 1587671 := bstep (se 1 (by rfl) ⟨1190753, by rfl⟩ : syracuseStep 1587671 = 2381507) B2381507
theorem B965641 : Blo 275825 965641 := bstep (se 2 (by rfl) ⟨362115, by rfl⟩ : syracuseStep 965641 = 724231) B724231
theorem B277607 : Blo 275825 277607 := bstep (se 1 (by rfl) ⟨208205, by rfl⟩ : syracuseStep 277607 = 416411) B416411
theorem B998675 : Blo 275825 998675 := bstep (se 1 (by rfl) ⟨749006, by rfl⟩ : syracuseStep 998675 = 1498013) B1498013
theorem B703799 : Blo 275825 703799 := bstep (se 1 (by rfl) ⟨527849, by rfl⟩ : syracuseStep 703799 = 1055699) B1055699
theorem B703991 : Blo 275825 703991 := bstep (se 1 (by rfl) ⟨527993, by rfl⟩ : syracuseStep 703991 = 1055987) B1055987
theorem B278047 : Blo 275825 278047 := bstep (se 1 (by rfl) ⟨208535, by rfl⟩ : syracuseStep 278047 = 417071) B417071
theorem B278207 : Blo 275825 278207 := bstep (se 1 (by rfl) ⟨208655, by rfl⟩ : syracuseStep 278207 = 417311) B417311
theorem B278591 : Blo 275825 278591 := bstep (se 1 (by rfl) ⟨208943, by rfl⟩ : syracuseStep 278591 = 417887) B417887
theorem B671905 : Blo 275825 671905 := bstep (se 2 (by rfl) ⟨251964, by rfl⟩ : syracuseStep 671905 = 503929) B503929
theorem B278751 : Blo 275825 278751 := bstep (se 1 (by rfl) ⟨209063, by rfl⟩ : syracuseStep 278751 = 418127) B418127
theorem B30228713 : Blo 275825 30228713 := bstep (se 2 (by rfl) ⟨11335767, by rfl⟩ : syracuseStep 30228713 = 22671535) B22671535
theorem B279195 : Blo 275825 279195 := bstep (se 1 (by rfl) ⟨209396, by rfl⟩ : syracuseStep 279195 = 418793) B418793
theorem B13452101 : Blo 275825 13452101 := bstep (se 4 (by rfl) ⟨1261134, by rfl⟩ : syracuseStep 13452101 = 2522269) B2522269
theorem B705449 : Blo 275825 705449 := bstep (se 2 (by rfl) ⟨264543, by rfl⟩ : syracuseStep 705449 = 529087) B529087
theorem B443483 : Blo 275825 443483 := bstep (se 1 (by rfl) ⟨332612, by rfl⟩ : syracuseStep 443483 = 665225) B665225
theorem B2377511 : Blo 275825 2377511 := bstep (se 1 (by rfl) ⟨1783133, by rfl⟩ : syracuseStep 2377511 = 3566267) B3566267
theorem B313159 : Blo 275825 313159 := bstep (se 1 (by rfl) ⟨234869, by rfl⟩ : syracuseStep 313159 = 469739) B469739
theorem B706441 : Blo 275825 706441 := bstep (se 2 (by rfl) ⟨264915, by rfl⟩ : syracuseStep 706441 = 529831) B529831
theorem B1001441 : Blo 275825 1001441 := bstep (se 2 (by rfl) ⟨375540, by rfl⟩ : syracuseStep 1001441 = 751081) B751081
theorem B444457 : Blo 275825 444457 := bstep (se 2 (by rfl) ⟨166671, by rfl⟩ : syracuseStep 444457 = 333343) B333343
theorem B2247209 : Blo 275825 2247209 := bstep (se 2 (by rfl) ⟨842703, by rfl⟩ : syracuseStep 2247209 = 1685407) B1685407
theorem B936683 : Blo 275825 936683 := bstep (se 1 (by rfl) ⟨702512, by rfl⟩ : syracuseStep 936683 = 1405025) B1405025
theorem B1821635 : Blo 275825 1821635 := bstep (se 1 (by rfl) ⟨1366226, by rfl⟩ : syracuseStep 1821635 = 2732453) B2732453
theorem B281599 : Blo 275825 281599 := bstep (se 1 (by rfl) ⟨211199, by rfl⟩ : syracuseStep 281599 = 422399) B422399
theorem B58019105 : Blo 275825 58019105 := bstep (se 2 (by rfl) ⟨21757164, by rfl⟩ : syracuseStep 58019105 = 43514329) B43514329
theorem B15224699 : Blo 275825 15224699 := bstep (se 1 (by rfl) ⟨11418524, by rfl⟩ : syracuseStep 15224699 = 22837049) B22837049
theorem B2117501 : Blo 275825 2117501 := bstep (se 3 (by rfl) ⟨397031, by rfl⟩ : syracuseStep 2117501 = 794063) B794063
theorem B1396763 : Blo 275825 1396763 := bstep (se 1 (by rfl) ⟨1047572, by rfl⟩ : syracuseStep 1396763 = 2095145) B2095145
theorem B1396925 : Blo 275825 1396925 := bstep (se 3 (by rfl) ⟨261923, by rfl⟩ : syracuseStep 1396925 = 523847) B523847
theorem B414023 : Blo 275825 414023 := bstep (se 1 (by rfl) ⟨310517, by rfl⟩ : syracuseStep 414023 = 621035) B621035
theorem B414491 : Blo 275825 414491 := bstep (se 1 (by rfl) ⟨310868, by rfl⟩ : syracuseStep 414491 = 621737) B621737
theorem B447481 : Blo 275825 447481 := bstep (se 2 (by rfl) ⟨167805, by rfl⟩ : syracuseStep 447481 = 335611) B335611
theorem B414767 : Blo 275825 414767 := bstep (se 1 (by rfl) ⟨311075, by rfl⟩ : syracuseStep 414767 = 622151) B622151
theorem B414911 : Blo 275825 414911 := bstep (se 1 (by rfl) ⟨311183, by rfl⟩ : syracuseStep 414911 = 622367) B622367
theorem B415145 : Blo 275825 415145 := bstep (se 2 (by rfl) ⟨155679, by rfl⟩ : syracuseStep 415145 = 311359) B311359
theorem B415199 : Blo 275825 415199 := bstep (se 1 (by rfl) ⟨311399, by rfl⟩ : syracuseStep 415199 = 622799) B622799
theorem B415211 : Blo 275825 415211 := bstep (se 1 (by rfl) ⟨311408, by rfl⟩ : syracuseStep 415211 = 622817) B622817
theorem B1496627 : Blo 275825 1496627 := bstep (se 1 (by rfl) ⟨1122470, by rfl⟩ : syracuseStep 1496627 = 2244941) B2244941
theorem B939599 : Blo 275825 939599 := bstep (se 1 (by rfl) ⟨704699, by rfl⟩ : syracuseStep 939599 = 1409399) B1409399
theorem B415655 : Blo 275825 415655 := bstep (se 1 (by rfl) ⟨311741, by rfl⟩ : syracuseStep 415655 = 623483) B623483
theorem B350887 : Blo 275825 350887 := bstep (se 1 (by rfl) ⟨263165, by rfl⟩ : syracuseStep 350887 = 526331) B526331
theorem B2120417 : Blo 275825 2120417 := bstep (se 2 (by rfl) ⟨795156, by rfl⟩ : syracuseStep 2120417 = 1590313) B1590313
theorem B416507 : Blo 275825 416507 := bstep (se 1 (by rfl) ⟨312380, by rfl⟩ : syracuseStep 416507 = 624761) B624761
theorem B1334447 : Blo 275825 1334447 := bstep (se 1 (by rfl) ⟨1000835, by rfl⟩ : syracuseStep 1334447 = 2001671) B2001671
theorem B417383 : Blo 275825 417383 := bstep (se 1 (by rfl) ⟨313037, by rfl⟩ : syracuseStep 417383 = 626075) B626075
theorem B417767 : Blo 275825 417767 := bstep (se 1 (by rfl) ⟨313325, by rfl⟩ : syracuseStep 417767 = 626651) B626651
theorem B417947 : Blo 275825 417947 := bstep (se 1 (by rfl) ⟨313460, by rfl⟩ : syracuseStep 417947 = 626921) B626921
theorem B418283 : Blo 275825 418283 := bstep (se 1 (by rfl) ⟨313712, by rfl⟩ : syracuseStep 418283 = 627425) B627425
theorem B418415 : Blo 275825 418415 := bstep (se 1 (by rfl) ⟨313811, by rfl⟩ : syracuseStep 418415 = 627623) B627623
theorem B943271 : Blo 275825 943271 := bstep (se 1 (by rfl) ⟨707453, by rfl⟩ : syracuseStep 943271 = 1414907) B1414907
theorem B419081 : Blo 275825 419081 := bstep (se 2 (by rfl) ⟨157155, by rfl⟩ : syracuseStep 419081 = 314311) B314311
theorem B419279 : Blo 275825 419279 := bstep (se 1 (by rfl) ⟨314459, by rfl⟩ : syracuseStep 419279 = 628919) B628919
theorem B419561 : Blo 275825 419561 := bstep (se 2 (by rfl) ⟨157335, by rfl⟩ : syracuseStep 419561 = 314671) B314671
theorem B1698641 : Blo 275825 1698641 := bstep (se 2 (by rfl) ⟨636990, by rfl⟩ : syracuseStep 1698641 = 1273981) B1273981
theorem B8612851 : Blo 275825 8612851 := bstep (se 1 (by rfl) ⟨6459638, by rfl⟩ : syracuseStep 8612851 = 12919277) B12919277
theorem B3567239 : Blo 275825 3567239 := bstep (se 1 (by rfl) ⟨2675429, by rfl⟩ : syracuseStep 3567239 = 5350859) B5350859
theorem B749287 : Blo 275825 749287 := bstep (se 1 (by rfl) ⟨561965, by rfl⟩ : syracuseStep 749287 = 1123931) B1123931
theorem B1406483 : Blo 275825 1406483 := bstep (se 1 (by rfl) ⟨1054862, by rfl⟩ : syracuseStep 1406483 = 2109725) B2109725
theorem B2258603 : Blo 275825 2258603 := bstep (se 1 (by rfl) ⟨1693952, by rfl⟩ : syracuseStep 2258603 = 3387905) B3387905
theorem B1407131 : Blo 275825 1407131 := bstep (se 1 (by rfl) ⟨1055348, by rfl⟩ : syracuseStep 1407131 = 2110697) B2110697
theorem B12155483 : Blo 275825 12155483 := bstep (se 1 (by rfl) ⟨9116612, by rfl⟩ : syracuseStep 12155483 = 18233225) B18233225
theorem B3996539 : Blo 275825 3996539 := bstep (se 1 (by rfl) ⟨2997404, by rfl⟩ : syracuseStep 3996539 = 5994809) B5994809
theorem B621503 : Blo 275825 621503 := bstep (se 1 (by rfl) ⟨466127, by rfl⟩ : syracuseStep 621503 = 932255) B932255
theorem B523817 : Blo 275825 523817 := bstep (se 2 (by rfl) ⟨196431, by rfl⟩ : syracuseStep 523817 = 392863) B392863
theorem B2687039 : Blo 275825 2687039 := bstep (se 1 (by rfl) ⟨2015279, by rfl⟩ : syracuseStep 2687039 = 4030559) B4030559
theorem B20152475 : Blo 275825 20152475 := bstep (se 1 (by rfl) ⟨15114356, by rfl⟩ : syracuseStep 20152475 = 30228713) B30228713
theorem B15303329 : Blo 275825 15303329 := bstep (se 2 (by rfl) ⟨5738748, by rfl⟩ : syracuseStep 15303329 = 11477497) B11477497
theorem B295655 : Blo 275825 295655 := bstep (se 1 (by rfl) ⟨221741, by rfl⟩ : syracuseStep 295655 = 443483) B443483
theorem B787639 : Blo 275825 787639 := bstep (se 1 (by rfl) ⟨590729, by rfl⟩ : syracuseStep 787639 = 1181459) B1181459
theorem B788039 : Blo 275825 788039 := bstep (se 1 (by rfl) ⟨591029, by rfl⟩ : syracuseStep 788039 = 1182059) B1182059
theorem B624455 : Blo 275825 624455 := bstep (se 1 (by rfl) ⟨468341, by rfl⟩ : syracuseStep 624455 = 936683) B936683
theorem B1214423 : Blo 275825 1214423 := bstep (se 1 (by rfl) ⟨910817, by rfl⟩ : syracuseStep 1214423 = 1821635) B1821635
theorem B3017035 : Blo 275825 3017035 := bstep (se 1 (by rfl) ⟨2262776, by rfl⟩ : syracuseStep 3017035 = 4525553) B4525553
theorem B1411667 : Blo 275825 1411667 := bstep (se 1 (by rfl) ⟨1058750, by rfl⟩ : syracuseStep 1411667 = 2117501) B2117501
theorem B592609 : Blo 275825 592609 := bstep (se 2 (by rfl) ⟨222228, by rfl⟩ : syracuseStep 592609 = 444457) B444457
theorem B626399 : Blo 275825 626399 := bstep (se 1 (by rfl) ⟨469799, by rfl⟩ : syracuseStep 626399 = 939599) B939599
theorem B1413611 : Blo 275825 1413611 := bstep (se 1 (by rfl) ⟨1060208, by rfl⟩ : syracuseStep 1413611 = 2120417) B2120417
theorem B889631 : Blo 275825 889631 := bstep (se 1 (by rfl) ⟨667223, by rfl⟩ : syracuseStep 889631 = 1334447) B1334447
theorem B1774547 : Blo 275825 1774547 := bstep (se 1 (by rfl) ⟨1330910, by rfl⟩ : syracuseStep 1774547 = 2661821) B2661821
theorem B2855945 : Blo 275825 2855945 := bstep (se 2 (by rfl) ⟨1070979, by rfl⟩ : syracuseStep 2855945 = 2141959) B2141959
theorem B1578923 : Blo 275825 1578923 := bstep (se 1 (by rfl) ⟨1184192, by rfl⟩ : syracuseStep 1578923 = 2368385) B2368385
theorem B628847 : Blo 275825 628847 := bstep (se 1 (by rfl) ⟨471635, by rfl⟩ : syracuseStep 628847 = 943271) B943271
theorem B596641 : Blo 275825 596641 := bstep (se 2 (by rfl) ⟨223740, by rfl⟩ : syracuseStep 596641 = 447481) B447481
theorem B793471 : Blo 275825 793471 := bstep (se 1 (by rfl) ⟨595103, by rfl⟩ : syracuseStep 793471 = 1190207) B1190207
theorem B12001709 : Blo 275825 12001709 := bstep (se 3 (by rfl) ⟨2250320, by rfl⟩ : syracuseStep 12001709 = 4500641) B4500641
theorem B467687 : Blo 275825 467687 := bstep (se 1 (by rfl) ⟨350765, by rfl⟩ : syracuseStep 467687 = 701531) B701531
theorem B467707 : Blo 275825 467707 := bstep (se 1 (by rfl) ⟨350780, by rfl⟩ : syracuseStep 467707 = 701561) B701561
theorem B467849 : Blo 275825 467849 := bstep (se 2 (by rfl) ⟨175443, by rfl⟩ : syracuseStep 467849 = 350887) B350887
theorem B3155111 : Blo 275825 3155111 := bstep (se 1 (by rfl) ⟨2366333, by rfl⟩ : syracuseStep 3155111 = 4732667) B4732667
theorem B1058129 : Blo 275825 1058129 := bstep (se 2 (by rfl) ⟨396798, by rfl⟩ : syracuseStep 1058129 = 793597) B793597
theorem B1287521 : Blo 275825 1287521 := bstep (se 2 (by rfl) ⟨482820, by rfl⟩ : syracuseStep 1287521 = 965641) B965641
theorem B1058447 : Blo 275825 1058447 := bstep (se 1 (by rfl) ⟨793835, by rfl⟩ : syracuseStep 1058447 = 1587671) B1587671
theorem B8103655 : Blo 275825 8103655 := bstep (se 1 (by rfl) ⟨6077741, by rfl⟩ : syracuseStep 8103655 = 12155483) B12155483
theorem B2664359 : Blo 275825 2664359 := bstep (se 1 (by rfl) ⟨1998269, by rfl⟩ : syracuseStep 2664359 = 3996539) B3996539
theorem B1189865 : Blo 275825 1189865 := bstep (se 2 (by rfl) ⟨446199, by rfl⟩ : syracuseStep 1189865 = 892399) B892399
theorem B665783 : Blo 275825 665783 := bstep (se 1 (by rfl) ⟨499337, by rfl⟩ : syracuseStep 665783 = 998675) B998675
theorem B469199 : Blo 275825 469199 := bstep (se 1 (by rfl) ⟨351899, by rfl⟩ : syracuseStep 469199 = 703799) B703799
theorem B469327 : Blo 275825 469327 := bstep (se 1 (by rfl) ⟨351995, by rfl⟩ : syracuseStep 469327 = 703991) B703991
theorem B895873 : Blo 275825 895873 := bstep (se 2 (by rfl) ⟨335952, by rfl⟩ : syracuseStep 895873 = 671905) B671905
theorem B699475 : Blo 275825 699475 := bstep (se 1 (by rfl) ⟨524606, by rfl⟩ : syracuseStep 699475 = 1049213) B1049213
theorem B699617 : Blo 275825 699617 := bstep (se 2 (by rfl) ⟨262356, by rfl⟩ : syracuseStep 699617 = 524713) B524713
theorem B470299 : Blo 275825 470299 := bstep (se 1 (by rfl) ⟨352724, by rfl⟩ : syracuseStep 470299 = 705449) B705449
theorem B1585007 : Blo 275825 1585007 := bstep (se 1 (by rfl) ⟨1188755, by rfl⟩ : syracuseStep 1585007 = 2377511) B2377511
theorem B700447 : Blo 275825 700447 := bstep (se 1 (by rfl) ⟨525335, by rfl⟩ : syracuseStep 700447 = 1050671) B1050671
theorem B963199 : Blo 275825 963199 := bstep (se 1 (by rfl) ⟨722399, by rfl⟩ : syracuseStep 963199 = 1444799) B1444799
theorem B72790811 : Blo 275825 72790811 := bstep (se 1 (by rfl) ⟨54593108, by rfl⟩ : syracuseStep 72790811 = 109186217) B109186217
theorem B38679403 : Blo 275825 38679403 := bstep (se 1 (by rfl) ⟨29009552, by rfl⟩ : syracuseStep 38679403 = 58019105) B58019105
theorem B931175 : Blo 275825 931175 := bstep (se 1 (by rfl) ⟨698381, by rfl⟩ : syracuseStep 931175 = 1396763) B1396763
theorem B931283 : Blo 275825 931283 := bstep (se 1 (by rfl) ⟨698462, by rfl⟩ : syracuseStep 931283 = 1396925) B1396925
theorem B276015 : Blo 275825 276015 := bstep (se 1 (by rfl) ⟨207011, by rfl⟩ : syracuseStep 276015 = 414023) B414023
theorem B276327 : Blo 275825 276327 := bstep (se 1 (by rfl) ⟨207245, by rfl⟩ : syracuseStep 276327 = 414491) B414491
theorem B276511 : Blo 275825 276511 := bstep (se 1 (by rfl) ⟨207383, by rfl⟩ : syracuseStep 276511 = 414767) B414767
theorem B276607 : Blo 275825 276607 := bstep (se 1 (by rfl) ⟨207455, by rfl⟩ : syracuseStep 276607 = 414911) B414911
theorem B13613255 : Blo 275825 13613255 := bstep (se 1 (by rfl) ⟨10209941, by rfl⟩ : syracuseStep 13613255 = 20419883) B20419883
theorem B276763 : Blo 275825 276763 := bstep (se 1 (by rfl) ⟨207572, by rfl⟩ : syracuseStep 276763 = 415145) B415145
theorem B276799 : Blo 275825 276799 := bstep (se 1 (by rfl) ⟨207599, by rfl⟩ : syracuseStep 276799 = 415199) B415199
theorem B276807 : Blo 275825 276807 := bstep (se 1 (by rfl) ⟨207605, by rfl⟩ : syracuseStep 276807 = 415211) B415211
theorem B997751 : Blo 275825 997751 := bstep (se 1 (by rfl) ⟨748313, by rfl⟩ : syracuseStep 997751 = 1496627) B1496627
theorem B277103 : Blo 275825 277103 := bstep (se 1 (by rfl) ⟨207827, by rfl⟩ : syracuseStep 277103 = 415655) B415655
theorem B11483801 : Blo 275825 11483801 := bstep (se 2 (by rfl) ⟨4306425, by rfl⟩ : syracuseStep 11483801 = 8612851) B8612851
theorem B277671 : Blo 275825 277671 := bstep (se 1 (by rfl) ⟨208253, by rfl⟩ : syracuseStep 277671 = 416507) B416507
theorem B999049 : Blo 275825 999049 := bstep (se 2 (by rfl) ⟨374643, by rfl⟩ : syracuseStep 999049 = 749287) B749287
theorem B278255 : Blo 275825 278255 := bstep (se 1 (by rfl) ⟨208691, by rfl⟩ : syracuseStep 278255 = 417383) B417383
theorem B2015047 : Blo 275825 2015047 := bstep (se 1 (by rfl) ⟨1511285, by rfl⟩ : syracuseStep 2015047 = 3022571) B3022571
theorem B311143 : Blo 275825 311143 := bstep (se 1 (by rfl) ⟨233357, by rfl⟩ : syracuseStep 311143 = 466715) B466715
theorem B2670509 : Blo 275825 2670509 := bstep (se 3 (by rfl) ⟨500720, by rfl⟩ : syracuseStep 2670509 = 1001441) B1001441
theorem B278511 : Blo 275825 278511 := bstep (se 1 (by rfl) ⟨208883, by rfl⟩ : syracuseStep 278511 = 417767) B417767
theorem B278631 : Blo 275825 278631 := bstep (se 1 (by rfl) ⟨208973, by rfl⟩ : syracuseStep 278631 = 417947) B417947
theorem B278855 : Blo 275825 278855 := bstep (se 1 (by rfl) ⟨209141, by rfl⟩ : syracuseStep 278855 = 418283) B418283
theorem B278943 : Blo 275825 278943 := bstep (se 1 (by rfl) ⟨209207, by rfl⟩ : syracuseStep 278943 = 418415) B418415
theorem B279387 : Blo 275825 279387 := bstep (se 1 (by rfl) ⟨209540, by rfl⟩ : syracuseStep 279387 = 419081) B419081
theorem B279519 : Blo 275825 279519 := bstep (se 1 (by rfl) ⟨209639, by rfl⟩ : syracuseStep 279519 = 419279) B419279
theorem B279707 : Blo 275825 279707 := bstep (se 1 (by rfl) ⟨209780, by rfl⟩ : syracuseStep 279707 = 419561) B419561
theorem B2279191 : Blo 275825 2279191 := bstep (se 1 (by rfl) ⟨1709393, by rfl⟩ : syracuseStep 2279191 = 3418787) B3418787
theorem B1132427 : Blo 275825 1132427 := bstep (se 1 (by rfl) ⟨849320, by rfl⟩ : syracuseStep 1132427 = 1698641) B1698641
theorem B706553 : Blo 275825 706553 := bstep (se 2 (by rfl) ⟨264957, by rfl⟩ : syracuseStep 706553 = 529915) B529915
theorem B313447 : Blo 275825 313447 := bstep (se 1 (by rfl) ⟨235085, by rfl⟩ : syracuseStep 313447 = 470171) B470171
theorem B2378159 : Blo 275825 2378159 := bstep (se 1 (by rfl) ⟨1783619, by rfl⟩ : syracuseStep 2378159 = 3567239) B3567239
theorem B1362943 : Blo 275825 1362943 := bstep (se 1 (by rfl) ⟨1022207, by rfl⟩ : syracuseStep 1362943 = 2044415) B2044415
theorem B3001643 : Blo 275825 3001643 := bstep (se 1 (by rfl) ⟨2251232, by rfl⟩ : syracuseStep 3001643 = 4502465) B4502465
theorem B937655 : Blo 275825 937655 := bstep (se 1 (by rfl) ⟨703241, by rfl⟩ : syracuseStep 937655 = 1406483) B1406483
theorem B938087 : Blo 275825 938087 := bstep (se 1 (by rfl) ⟨703565, by rfl⟩ : syracuseStep 938087 = 1407131) B1407131
theorem B414335 : Blo 275825 414335 := bstep (se 1 (by rfl) ⟨310751, by rfl⟩ : syracuseStep 414335 = 621503) B621503
theorem B349211 : Blo 275825 349211 := bstep (se 1 (by rfl) ⟨261908, by rfl⟩ : syracuseStep 349211 = 523817) B523817
theorem B12440989 : Blo 275825 12440989 := bstep (se 3 (by rfl) ⟨2332685, by rfl⟩ : syracuseStep 12440989 = 4665371) B4665371
theorem B1201655 : Blo 275825 1201655 := bstep (se 1 (by rfl) ⟨901241, by rfl⟩ : syracuseStep 1201655 = 1802483) B1802483
theorem B415463 : Blo 275825 415463 := bstep (se 1 (by rfl) ⟨311597, by rfl⟩ : syracuseStep 415463 = 623195) B623195
theorem B8968067 : Blo 275825 8968067 := bstep (se 1 (by rfl) ⟨6726050, by rfl⟩ : syracuseStep 8968067 = 13452101) B13452101
theorem B416063 : Blo 275825 416063 := bstep (se 1 (by rfl) ⟨312047, by rfl⟩ : syracuseStep 416063 = 624095) B624095
theorem B809423 : Blo 275825 809423 := bstep (se 1 (by rfl) ⟨607067, by rfl⟩ : syracuseStep 809423 = 1214135) B1214135
theorem B1498139 : Blo 275825 1498139 := bstep (se 1 (by rfl) ⟨1123604, by rfl⟩ : syracuseStep 1498139 = 2247209) B2247209
theorem B351535 : Blo 275825 351535 := bstep (se 1 (by rfl) ⟨263651, by rfl⟩ : syracuseStep 351535 = 527303) B527303
theorem B4480343 : Blo 275825 4480343 := bstep (se 1 (by rfl) ⟨3360257, by rfl⟩ : syracuseStep 4480343 = 6720515) B6720515
theorem B417545 : Blo 275825 417545 := bstep (se 2 (by rfl) ⟨156579, by rfl⟩ : syracuseStep 417545 = 313159) B313159
theorem B941921 : Blo 275825 941921 := bstep (se 2 (by rfl) ⟨353220, by rfl⟩ : syracuseStep 941921 = 706441) B706441
theorem B352127 : Blo 275825 352127 := bstep (se 1 (by rfl) ⟨264095, by rfl⟩ : syracuseStep 352127 = 528191) B528191
theorem B10149799 : Blo 275825 10149799 := bstep (se 1 (by rfl) ⟨7612349, by rfl⟩ : syracuseStep 10149799 = 15224699) B15224699
theorem B943055 : Blo 275825 943055 := bstep (se 1 (by rfl) ⟨707291, by rfl⟩ : syracuseStep 943055 = 1414583) B1414583
theorem B1401947 : Blo 275825 1401947 := bstep (se 1 (by rfl) ⟨1051460, by rfl⟩ : syracuseStep 1401947 = 2102921) B2102921
theorem B419099 : Blo 275825 419099 := bstep (se 1 (by rfl) ⟨314324, by rfl⟩ : syracuseStep 419099 = 628649) B628649
theorem B419519 : Blo 275825 419519 := bstep (se 1 (by rfl) ⟨314639, by rfl⟩ : syracuseStep 419519 = 629279) B629279
theorem B3172607 : Blo 275825 3172607 := bstep (se 1 (by rfl) ⟨2379455, by rfl⟩ : syracuseStep 3172607 = 4758911) B4758911
theorem B1403243 : Blo 275825 1403243 := bstep (se 1 (by rfl) ⟨1052432, by rfl⟩ : syracuseStep 1403243 = 2104865) B2104865
theorem B1501861 : Blo 275825 1501861 := bstep (se 4 (by rfl) ⟨140799, by rfl⟩ : syracuseStep 1501861 = 281599) B281599
theorem B2681657 : Blo 275825 2681657 := bstep (se 2 (by rfl) ⟨1005621, by rfl⟩ : syracuseStep 2681657 = 2011243) B2011243
theorem B1405673 : Blo 275825 1405673 := bstep (se 2 (by rfl) ⟨527127, by rfl⟩ : syracuseStep 1405673 = 1054255) B1054255
theorem B1505735 : Blo 275825 1505735 := bstep (se 1 (by rfl) ⟨1129301, by rfl⟩ : syracuseStep 1505735 = 2258603) B2258603
theorem B1407455 : Blo 275825 1407455 := bstep (se 1 (by rfl) ⟨1055591, by rfl⟩ : syracuseStep 1407455 = 2111183) B2111183
theorem B1342271 : Blo 275825 1342271 := bstep (se 1 (by rfl) ⟨1006703, by rfl⟩ : syracuseStep 1342271 = 2013407) B2013407
theorem B13434983 : Blo 275825 13434983 := bstep (se 1 (by rfl) ⟨10076237, by rfl⟩ : syracuseStep 13434983 = 20152475) B20152475
theorem B623609 : Blo 275825 623609 := bstep (se 2 (by rfl) ⟨233853, by rfl⟩ : syracuseStep 623609 = 467707) B467707
theorem B525359 : Blo 275825 525359 := bstep (se 1 (by rfl) ⟨394019, by rfl⟩ : syracuseStep 525359 = 788039) B788039
theorem B754951 : Blo 275825 754951 := bstep (se 1 (by rfl) ⟨566213, by rfl⟩ : syracuseStep 754951 = 1132427) B1132427
theorem B1050185 : Blo 275825 1050185 := bstep (se 2 (by rfl) ⟨393819, by rfl⟩ : syracuseStep 1050185 = 787639) B787639
theorem B2001095 : Blo 275825 2001095 := bstep (se 1 (by rfl) ⟨1500821, by rfl⟩ : syracuseStep 2001095 = 3001643) B3001643
theorem B625103 : Blo 275825 625103 := bstep (se 1 (by rfl) ⟨468827, by rfl⟩ : syracuseStep 625103 = 937655) B937655
theorem B625391 : Blo 275825 625391 := bstep (se 1 (by rfl) ⟨469043, by rfl⟩ : syracuseStep 625391 = 938087) B938087
theorem B625769 : Blo 275825 625769 := bstep (se 2 (by rfl) ⟨234663, by rfl⟩ : syracuseStep 625769 = 469327) B469327
theorem B593087 : Blo 275825 593087 := bstep (se 1 (by rfl) ⟨444815, by rfl⟩ : syracuseStep 593087 = 889631) B889631
theorem B1183031 : Blo 275825 1183031 := bstep (se 1 (by rfl) ⟨887273, by rfl⟩ : syracuseStep 1183031 = 1774547) B1774547
theorem B2002481 : Blo 275825 2002481 := bstep (se 2 (by rfl) ⟨750930, by rfl⟩ : syracuseStep 2002481 = 1501861) B1501861
theorem B790145 : Blo 275825 790145 := bstep (se 2 (by rfl) ⟨296304, by rfl⟩ : syracuseStep 790145 = 592609) B592609
theorem B1052615 : Blo 275825 1052615 := bstep (se 1 (by rfl) ⟨789461, by rfl⟩ : syracuseStep 1052615 = 1578923) B1578923
theorem B627065 : Blo 275825 627065 := bstep (se 2 (by rfl) ⟨235149, by rfl⟩ : syracuseStep 627065 = 470299) B470299
theorem B2986895 : Blo 275825 2986895 := bstep (se 1 (by rfl) ⟨2240171, by rfl⟩ : syracuseStep 2986895 = 4480343) B4480343
theorem B627947 : Blo 275825 627947 := bstep (se 1 (by rfl) ⟨470960, by rfl⟩ : syracuseStep 627947 = 941921) B941921
theorem B8001139 : Blo 275825 8001139 := bstep (se 1 (by rfl) ⟨6000854, by rfl⟩ : syracuseStep 8001139 = 12001709) B12001709
theorem B628703 : Blo 275825 628703 := bstep (se 1 (by rfl) ⟨471527, by rfl⟩ : syracuseStep 628703 = 943055) B943055
theorem B2103407 : Blo 275825 2103407 := bstep (se 1 (by rfl) ⟨1577555, by rfl⟩ : syracuseStep 2103407 = 3155111) B3155111
theorem B1284265 : Blo 275825 1284265 := bstep (se 2 (by rfl) ⟨481599, by rfl⟩ : syracuseStep 1284265 = 963199) B963199
theorem B858347 : Blo 275825 858347 := bstep (se 1 (by rfl) ⟨643760, by rfl⟩ : syracuseStep 858347 = 1287521) B1287521
theorem B1776239 : Blo 275825 1776239 := bstep (se 1 (by rfl) ⟨1332179, by rfl⟩ : syracuseStep 1776239 = 2664359) B2664359
theorem B793243 : Blo 275825 793243 := bstep (se 1 (by rfl) ⟨594932, by rfl⟩ : syracuseStep 793243 = 1189865) B1189865
theorem B16587985 : Blo 275825 16587985 := bstep (se 2 (by rfl) ⟨6220494, by rfl⟩ : syracuseStep 16587985 = 12440989) B12440989
theorem B466411 : Blo 275825 466411 := bstep (se 1 (by rfl) ⟨349808, by rfl⟩ : syracuseStep 466411 = 699617) B699617
theorem B3579389 : Blo 275825 3579389 := bstep (se 3 (by rfl) ⟨671135, by rfl⟩ : syracuseStep 3579389 = 1342271) B1342271
theorem B3153653 : Blo 275825 3153653 := bstep (se 5 (by rfl) ⟨147827, by rfl⟩ : syracuseStep 3153653 = 295655) B295655
theorem B1056671 : Blo 275825 1056671 := bstep (se 1 (by rfl) ⟨792503, by rfl⟩ : syracuseStep 1056671 = 1585007) B1585007
theorem B795521 : Blo 275825 795521 := bstep (se 2 (by rfl) ⟨298320, by rfl⟩ : syracuseStep 795521 = 596641) B596641
theorem B1057961 : Blo 275825 1057961 := bstep (se 2 (by rfl) ⟨396735, by rfl⟩ : syracuseStep 1057961 = 793471) B793471
theorem B665167 : Blo 275825 665167 := bstep (se 1 (by rfl) ⟨498875, by rfl⟩ : syracuseStep 665167 = 997751) B997751
theorem B468713 : Blo 275825 468713 := bstep (se 2 (by rfl) ⟨175767, by rfl⟩ : syracuseStep 468713 = 351535) B351535
theorem B1780339 : Blo 275825 1780339 := bstep (se 1 (by rfl) ⟨1335254, by rfl⟩ : syracuseStep 1780339 = 2670509) B2670509
theorem B10202219 : Blo 275825 10202219 := bstep (se 1 (by rfl) ⟨7651664, by rfl⟩ : syracuseStep 10202219 = 15303329) B15303329
theorem B471035 : Blo 275825 471035 := bstep (se 1 (by rfl) ⟨353276, by rfl⟩ : syracuseStep 471035 = 706553) B706553
theorem B1585439 : Blo 275825 1585439 := bstep (se 1 (by rfl) ⟨1189079, by rfl⟩ : syracuseStep 1585439 = 2378159) B2378159
theorem B7615853 : Blo 275825 7615853 := bstep (se 3 (by rfl) ⟨1427972, by rfl⟩ : syracuseStep 7615853 = 2855945) B2855945
theorem B931229 : Blo 275825 931229 := bstep (se 3 (by rfl) ⟨174605, by rfl⟩ : syracuseStep 931229 = 349211) B349211
theorem B276223 : Blo 275825 276223 := bstep (se 1 (by rfl) ⟨207167, by rfl⟩ : syracuseStep 276223 = 414335) B414335
theorem B801103 : Blo 275825 801103 := bstep (se 1 (by rfl) ⟨600827, by rfl⟩ : syracuseStep 801103 = 1201655) B1201655
theorem B276975 : Blo 275825 276975 := bstep (se 1 (by rfl) ⟨207731, by rfl⟩ : syracuseStep 276975 = 415463) B415463
theorem B1194497 : Blo 275825 1194497 := bstep (se 2 (by rfl) ⟨447936, by rfl⟩ : syracuseStep 1194497 = 895873) B895873
theorem B5978711 : Blo 275825 5978711 := bstep (se 1 (by rfl) ⟨4484033, by rfl⟩ : syracuseStep 5978711 = 8968067) B8968067
theorem B1817257 : Blo 275825 1817257 := bstep (se 2 (by rfl) ⟨681471, by rfl⟩ : syracuseStep 1817257 = 1362943) B1362943
theorem B932633 : Blo 275825 932633 := bstep (se 2 (by rfl) ⟨349737, by rfl⟩ : syracuseStep 932633 = 699475) B699475
theorem B277375 : Blo 275825 277375 := bstep (se 1 (by rfl) ⟨208031, by rfl⟩ : syracuseStep 277375 = 416063) B416063
theorem B539615 : Blo 275825 539615 := bstep (se 1 (by rfl) ⟨404711, by rfl⟩ : syracuseStep 539615 = 809423) B809423
theorem B998759 : Blo 275825 998759 := bstep (se 1 (by rfl) ⟨749069, by rfl⟩ : syracuseStep 998759 = 1498139) B1498139
theorem B278363 : Blo 275825 278363 := bstep (se 1 (by rfl) ⟨208772, by rfl⟩ : syracuseStep 278363 = 417545) B417545
theorem B933929 : Blo 275825 933929 := bstep (se 2 (by rfl) ⟨350223, by rfl⟩ : syracuseStep 933929 = 700447) B700447
theorem B311791 : Blo 275825 311791 := bstep (se 1 (by rfl) ⟨233843, by rfl⟩ : syracuseStep 311791 = 467687) B467687
theorem B311899 : Blo 275825 311899 := bstep (se 1 (by rfl) ⟨233924, by rfl⟩ : syracuseStep 311899 = 467849) B467849
theorem B934631 : Blo 275825 934631 := bstep (se 1 (by rfl) ⟨700973, by rfl⟩ : syracuseStep 934631 = 1401947) B1401947
theorem B279399 : Blo 275825 279399 := bstep (se 1 (by rfl) ⟨209549, by rfl⟩ : syracuseStep 279399 = 419099) B419099
theorem B705419 : Blo 275825 705419 := bstep (se 1 (by rfl) ⟨529064, by rfl⟩ : syracuseStep 705419 = 1058129) B1058129
theorem B705631 : Blo 275825 705631 := bstep (se 1 (by rfl) ⟨529223, by rfl⟩ : syracuseStep 705631 = 1058447) B1058447
theorem B279679 : Blo 275825 279679 := bstep (se 1 (by rfl) ⟨209759, by rfl⟩ : syracuseStep 279679 = 419519) B419519
theorem B443855 : Blo 275825 443855 := bstep (se 1 (by rfl) ⟨332891, by rfl⟩ : syracuseStep 443855 = 665783) B665783
theorem B312799 : Blo 275825 312799 := bstep (se 1 (by rfl) ⟨234599, by rfl⟩ : syracuseStep 312799 = 469199) B469199
theorem B2115071 : Blo 275825 2115071 := bstep (se 1 (by rfl) ⟨1586303, by rfl⟩ : syracuseStep 2115071 = 3172607) B3172607
theorem B935495 : Blo 275825 935495 := bstep (se 1 (by rfl) ⟨701621, by rfl⟩ : syracuseStep 935495 = 1403243) B1403243
theorem B1787771 : Blo 275825 1787771 := bstep (se 1 (by rfl) ⟨1340828, by rfl⟩ : syracuseStep 1787771 = 2681657) B2681657
theorem B937115 : Blo 275825 937115 := bstep (se 1 (by rfl) ⟨702836, by rfl⟩ : syracuseStep 937115 = 1405673) B1405673
theorem B1003823 : Blo 275825 1003823 := bstep (se 1 (by rfl) ⟨752867, by rfl⟩ : syracuseStep 1003823 = 1505735) B1505735
theorem B938303 : Blo 275825 938303 := bstep (se 1 (by rfl) ⟨703727, by rfl⟩ : syracuseStep 938303 = 1407455) B1407455
theorem B7655867 : Blo 275825 7655867 := bstep (se 1 (by rfl) ⟨5741900, by rfl⟩ : syracuseStep 7655867 = 11483801) B11483801
theorem B1332065 : Blo 275825 1332065 := bstep (se 2 (by rfl) ⟨499524, by rfl⟩ : syracuseStep 1332065 = 999049) B999049
theorem B939005 : Blo 275825 939005 := bstep (se 3 (by rfl) ⟨176063, by rfl⟩ : syracuseStep 939005 = 352127) B352127
theorem B414857 : Blo 275825 414857 := bstep (se 2 (by rfl) ⟨155571, by rfl⟩ : syracuseStep 414857 = 311143) B311143
theorem B1791359 : Blo 275825 1791359 := bstep (se 1 (by rfl) ⟨1343519, by rfl⟩ : syracuseStep 1791359 = 2687039) B2687039
theorem B416303 : Blo 275825 416303 := bstep (se 1 (by rfl) ⟨312227, by rfl⟩ : syracuseStep 416303 = 624455) B624455
theorem B809615 : Blo 275825 809615 := bstep (se 1 (by rfl) ⟨607211, by rfl⟩ : syracuseStep 809615 = 1214423) B1214423
theorem B941111 : Blo 275825 941111 := bstep (se 1 (by rfl) ⟨705833, by rfl⟩ : syracuseStep 941111 = 1411667) B1411667
theorem B3038921 : Blo 275825 3038921 := bstep (se 2 (by rfl) ⟨1139595, by rfl⟩ : syracuseStep 3038921 = 2279191) B2279191
theorem B417599 : Blo 275825 417599 := bstep (se 1 (by rfl) ⟨313199, by rfl⟩ : syracuseStep 417599 = 626399) B626399
theorem B417929 : Blo 275825 417929 := bstep (se 2 (by rfl) ⟨156723, by rfl⟩ : syracuseStep 417929 = 313447) B313447
theorem B942407 : Blo 275825 942407 := bstep (se 1 (by rfl) ⟨706805, by rfl⟩ : syracuseStep 942407 = 1413611) B1413611
theorem B4022713 : Blo 275825 4022713 := bstep (se 2 (by rfl) ⟨1508517, by rfl⟩ : syracuseStep 4022713 = 3017035) B3017035
theorem B419231 : Blo 275825 419231 := bstep (se 1 (by rfl) ⟨314423, by rfl⟩ : syracuseStep 419231 = 628847) B628847
theorem B51572537 : Blo 275825 51572537 := bstep (se 2 (by rfl) ⟨19339701, by rfl⟩ : syracuseStep 51572537 = 38679403) B38679403
theorem B48527207 : Blo 275825 48527207 := bstep (se 1 (by rfl) ⟨36395405, by rfl⟩ : syracuseStep 48527207 = 72790811) B72790811
theorem B620783 : Blo 275825 620783 := bstep (se 1 (by rfl) ⟨465587, by rfl⟩ : syracuseStep 620783 = 931175) B931175
theorem B620855 : Blo 275825 620855 := bstep (se 1 (by rfl) ⟨465641, by rfl⟩ : syracuseStep 620855 = 931283) B931283
theorem B43219493 : Blo 275825 43219493 := bstep (se 4 (by rfl) ⟨4051827, by rfl⟩ : syracuseStep 43219493 = 8103655) B8103655
theorem B9075503 : Blo 275825 9075503 := bstep (se 1 (by rfl) ⟨6806627, by rfl⟩ : syracuseStep 9075503 = 13613255) B13613255
theorem B10746917 : Blo 275825 10746917 := bstep (se 4 (by rfl) ⟨1007523, by rfl⟩ : syracuseStep 10746917 = 2015047) B2015047
theorem B13533065 : Blo 275825 13533065 := bstep (se 2 (by rfl) ⟨5074899, by rfl⟩ : syracuseStep 13533065 = 10149799) B10149799
theorem B622619 : Blo 275825 622619 := bstep (se 1 (by rfl) ⟨466964, by rfl⟩ : syracuseStep 622619 = 933929) B933929
theorem B623087 : Blo 275825 623087 := bstep (se 1 (by rfl) ⟨467315, by rfl⟩ : syracuseStep 623087 = 934631) B934631
theorem B295903 : Blo 275825 295903 := bstep (se 1 (by rfl) ⟨221927, by rfl⟩ : syracuseStep 295903 = 443855) B443855
theorem B1410047 : Blo 275825 1410047 := bstep (se 1 (by rfl) ⟨1057535, by rfl⟩ : syracuseStep 1410047 = 2115071) B2115071
theorem B623663 : Blo 275825 623663 := bstep (se 1 (by rfl) ⟨467747, by rfl⟩ : syracuseStep 623663 = 935495) B935495
theorem B624743 : Blo 275825 624743 := bstep (se 1 (by rfl) ⟨468557, by rfl⟩ : syracuseStep 624743 = 937115) B937115
theorem B886889 : Blo 275825 886889 := bstep (se 2 (by rfl) ⟨332583, by rfl⟩ : syracuseStep 886889 = 665167) B665167
theorem B788687 : Blo 275825 788687 := bstep (se 1 (by rfl) ⟨591515, by rfl⟩ : syracuseStep 788687 = 1183031) B1183031
theorem B7965053 : Blo 275825 7965053 := bstep (se 3 (by rfl) ⟨1493447, by rfl⟩ : syracuseStep 7965053 = 2986895) B2986895
theorem B526763 : Blo 275825 526763 := bstep (se 1 (by rfl) ⟨395072, by rfl⟩ : syracuseStep 526763 = 790145) B790145
theorem B625535 : Blo 275825 625535 := bstep (se 1 (by rfl) ⟨469151, by rfl⟩ : syracuseStep 625535 = 938303) B938303
theorem B888043 : Blo 275825 888043 := bstep (se 1 (by rfl) ⟨666032, by rfl⟩ : syracuseStep 888043 = 1332065) B1332065
theorem B626003 : Blo 275825 626003 := bstep (se 1 (by rfl) ⟨469502, by rfl⟩ : syracuseStep 626003 = 939005) B939005
theorem B1184159 : Blo 275825 1184159 := bstep (se 1 (by rfl) ⟨888119, by rfl⟩ : syracuseStep 1184159 = 1776239) B1776239
theorem B627407 : Blo 275825 627407 := bstep (se 1 (by rfl) ⟨470555, by rfl⟩ : syracuseStep 627407 = 941111) B941111
theorem B2102435 : Blo 275825 2102435 := bstep (se 1 (by rfl) ⟨1576826, by rfl⟩ : syracuseStep 2102435 = 3153653) B3153653
theorem B628271 : Blo 275825 628271 := bstep (se 1 (by rfl) ⟨471203, by rfl⟩ : syracuseStep 628271 = 942407) B942407
theorem B34381691 : Blo 275825 34381691 := bstep (se 1 (by rfl) ⟨25786268, by rfl⟩ : syracuseStep 34381691 = 51572537) B51572537
theorem B1056959 : Blo 275825 1056959 := bstep (se 1 (by rfl) ⟨792719, by rfl⟩ : syracuseStep 1056959 = 1585439) B1585439
theorem B1712353 : Blo 275825 1712353 := bstep (se 2 (by rfl) ⟨642132, by rfl⟩ : syracuseStep 1712353 = 1284265) B1284265
theorem B1581565 : Blo 275825 1581565 := bstep (se 3 (by rfl) ⟨296543, by rfl⟩ : syracuseStep 1581565 = 593087) B593087
theorem B1057657 : Blo 275825 1057657 := bstep (se 2 (by rfl) ⟨396621, by rfl⟩ : syracuseStep 1057657 = 793243) B793243
theorem B32351471 : Blo 275825 32351471 := bstep (se 1 (by rfl) ⟨24263603, by rfl⟩ : syracuseStep 32351471 = 48527207) B48527207
theorem B796331 : Blo 275825 796331 := bstep (se 1 (by rfl) ⟨597248, by rfl⟩ : syracuseStep 796331 = 1194497) B1194497
theorem B28812995 : Blo 275825 28812995 := bstep (se 1 (by rfl) ⟨21609746, by rfl⟩ : syracuseStep 28812995 = 43219493) B43219493
theorem B665839 : Blo 275825 665839 := bstep (se 1 (by rfl) ⟨499379, by rfl⟩ : syracuseStep 665839 = 998759) B998759
theorem B9022043 : Blo 275825 9022043 := bstep (se 1 (by rfl) ⟨6766532, by rfl⟩ : syracuseStep 9022043 = 13533065) B13533065
theorem B8956655 : Blo 275825 8956655 := bstep (se 1 (by rfl) ⟨6717491, by rfl⟩ : syracuseStep 8956655 = 13434983) B13434983
theorem B470279 : Blo 275825 470279 := bstep (se 1 (by rfl) ⟨352709, by rfl⟩ : syracuseStep 470279 = 705419) B705419
theorem B700123 : Blo 275825 700123 := bstep (se 1 (by rfl) ⟨525092, by rfl⟩ : syracuseStep 700123 = 1050185) B1050185
theorem B1191847 : Blo 275825 1191847 := bstep (se 1 (by rfl) ⟨893885, by rfl⟩ : syracuseStep 1191847 = 1787771) B1787771
theorem B701743 : Blo 275825 701743 := bstep (se 1 (by rfl) ⟨526307, by rfl⟩ : syracuseStep 701743 = 1052615) B1052615
theorem B669215 : Blo 275825 669215 := bstep (se 1 (by rfl) ⟨501911, by rfl⟩ : syracuseStep 669215 = 1003823) B1003823
theorem B276571 : Blo 275825 276571 := bstep (se 1 (by rfl) ⟨207428, by rfl⟩ : syracuseStep 276571 = 414857) B414857
theorem B2373785 : Blo 275825 2373785 := bstep (se 2 (by rfl) ⟨890169, by rfl⟩ : syracuseStep 2373785 = 1780339) B1780339
theorem B1194239 : Blo 275825 1194239 := bstep (se 1 (by rfl) ⟨895679, by rfl⟩ : syracuseStep 1194239 = 1791359) B1791359
theorem B572231 : Blo 275825 572231 := bstep (se 1 (by rfl) ⟨429173, by rfl⟩ : syracuseStep 572231 = 858347) B858347
theorem B277535 : Blo 275825 277535 := bstep (se 1 (by rfl) ⟨208151, by rfl⟩ : syracuseStep 277535 = 416303) B416303
theorem B539743 : Blo 275825 539743 := bstep (se 1 (by rfl) ⟨404807, by rfl⟩ : syracuseStep 539743 = 809615) B809615
theorem B278399 : Blo 275825 278399 := bstep (se 1 (by rfl) ⟨208799, by rfl⟩ : syracuseStep 278399 = 417599) B417599
theorem B704447 : Blo 275825 704447 := bstep (se 1 (by rfl) ⟨528335, by rfl⟩ : syracuseStep 704447 = 1056671) B1056671
theorem B278619 : Blo 275825 278619 := bstep (se 1 (by rfl) ⟨208964, by rfl⟩ : syracuseStep 278619 = 417929) B417929
theorem B705307 : Blo 275825 705307 := bstep (se 1 (by rfl) ⟨528980, by rfl⟩ : syracuseStep 705307 = 1057961) B1057961
theorem B279487 : Blo 275825 279487 := bstep (se 1 (by rfl) ⟨209615, by rfl⟩ : syracuseStep 279487 = 419231) B419231
theorem B312475 : Blo 275825 312475 := bstep (se 1 (by rfl) ⟨234356, by rfl⟩ : syracuseStep 312475 = 468713) B468713
theorem B15943229 : Blo 275825 15943229 := bstep (se 3 (by rfl) ⟨2989355, by rfl⟩ : syracuseStep 15943229 = 5978711) B5978711
theorem B6801479 : Blo 275825 6801479 := bstep (se 1 (by rfl) ⟨5101109, by rfl⟩ : syracuseStep 6801479 = 10202219) B10202219
theorem B10668185 : Blo 275825 10668185 := bstep (se 2 (by rfl) ⟨4000569, by rfl⟩ : syracuseStep 10668185 = 8001139) B8001139
theorem B314023 : Blo 275825 314023 := bstep (se 1 (by rfl) ⟨235517, by rfl⟩ : syracuseStep 314023 = 471035) B471035
theorem B1068137 : Blo 275825 1068137 := bstep (se 2 (by rfl) ⟨400551, by rfl⟩ : syracuseStep 1068137 = 801103) B801103
theorem B413855 : Blo 275825 413855 := bstep (se 1 (by rfl) ⟨310391, by rfl⟩ : syracuseStep 413855 = 620783) B620783
theorem B413903 : Blo 275825 413903 := bstep (se 1 (by rfl) ⟨310427, by rfl⟩ : syracuseStep 413903 = 620855) B620855
theorem B6050335 : Blo 275825 6050335 := bstep (se 1 (by rfl) ⟨4537751, by rfl⟩ : syracuseStep 6050335 = 9075503) B9075503
theorem B7164611 : Blo 275825 7164611 := bstep (se 1 (by rfl) ⟨5373458, by rfl⟩ : syracuseStep 7164611 = 10746917) B10746917
theorem B5363617 : Blo 275825 5363617 := bstep (se 2 (by rfl) ⟨2011356, by rfl⟩ : syracuseStep 5363617 = 4022713) B4022713
theorem B415721 : Blo 275825 415721 := bstep (se 2 (by rfl) ⟨155895, by rfl⟩ : syracuseStep 415721 = 311791) B311791
theorem B415739 : Blo 275825 415739 := bstep (se 1 (by rfl) ⟨311804, by rfl⟩ : syracuseStep 415739 = 623609) B623609
theorem B350239 : Blo 275825 350239 := bstep (se 1 (by rfl) ⟨262679, by rfl⟩ : syracuseStep 350239 = 525359) B525359
theorem B415865 : Blo 275825 415865 := bstep (se 2 (by rfl) ⟨155949, by rfl⟩ : syracuseStep 415865 = 311899) B311899
theorem B940841 : Blo 275825 940841 := bstep (se 2 (by rfl) ⟨352815, by rfl⟩ : syracuseStep 940841 = 705631) B705631
theorem B1334063 : Blo 275825 1334063 := bstep (se 1 (by rfl) ⟨1000547, by rfl⟩ : syracuseStep 1334063 = 2001095) B2001095
theorem B416735 : Blo 275825 416735 := bstep (se 1 (by rfl) ⟨312551, by rfl⟩ : syracuseStep 416735 = 625103) B625103
theorem B1006601 : Blo 275825 1006601 := bstep (se 2 (by rfl) ⟨377475, by rfl⟩ : syracuseStep 1006601 = 754951) B754951
theorem B416927 : Blo 275825 416927 := bstep (se 1 (by rfl) ⟨312695, by rfl⟩ : syracuseStep 416927 = 625391) B625391
theorem B417065 : Blo 275825 417065 := bstep (se 2 (by rfl) ⟨156399, by rfl⟩ : syracuseStep 417065 = 312799) B312799
theorem B417179 : Blo 275825 417179 := bstep (se 1 (by rfl) ⟨312884, by rfl⟩ : syracuseStep 417179 = 625769) B625769
theorem B2121389 : Blo 275825 2121389 := bstep (se 3 (by rfl) ⟨397760, by rfl⟩ : syracuseStep 2121389 = 795521) B795521
theorem B1334987 : Blo 275825 1334987 := bstep (se 1 (by rfl) ⟨1001240, by rfl⟩ : syracuseStep 1334987 = 2002481) B2002481
theorem B418043 : Blo 275825 418043 := bstep (se 1 (by rfl) ⟨313532, by rfl⟩ : syracuseStep 418043 = 627065) B627065
theorem B5103911 : Blo 275825 5103911 := bstep (se 1 (by rfl) ⟨3827933, by rfl⟩ : syracuseStep 5103911 = 7655867) B7655867
theorem B418631 : Blo 275825 418631 := bstep (se 1 (by rfl) ⟨313973, by rfl⟩ : syracuseStep 418631 = 627947) B627947
theorem B419135 : Blo 275825 419135 := bstep (se 1 (by rfl) ⟨314351, by rfl⟩ : syracuseStep 419135 = 628703) B628703
theorem B1402271 : Blo 275825 1402271 := bstep (se 1 (by rfl) ⟨1051703, by rfl⟩ : syracuseStep 1402271 = 2103407) B2103407
theorem B2386259 : Blo 275825 2386259 := bstep (se 1 (by rfl) ⟨1789694, by rfl⟩ : syracuseStep 2386259 = 3579389) B3579389
theorem B2025947 : Blo 275825 2025947 := bstep (se 1 (by rfl) ⟨1519460, by rfl⟩ : syracuseStep 2025947 = 3038921) B3038921
theorem B2423009 : Blo 275825 2423009 := bstep (se 2 (by rfl) ⟨908628, by rfl⟩ : syracuseStep 2423009 = 1817257) B1817257
theorem B5077235 : Blo 275825 5077235 := bstep (se 1 (by rfl) ⟨3807926, by rfl⟩ : syracuseStep 5077235 = 7615853) B7615853
theorem B620819 : Blo 275825 620819 := bstep (se 1 (by rfl) ⟨465614, by rfl⟩ : syracuseStep 620819 = 931229) B931229
theorem B22117313 : Blo 275825 22117313 := bstep (se 2 (by rfl) ⟨8293992, by rfl⟩ : syracuseStep 22117313 = 16587985) B16587985
theorem B621755 : Blo 275825 621755 := bstep (se 1 (by rfl) ⟨466316, by rfl⟩ : syracuseStep 621755 = 932633) B932633
theorem B621881 : Blo 275825 621881 := bstep (se 2 (by rfl) ⟨233205, by rfl⟩ : syracuseStep 621881 = 466411) B466411
theorem B359743 : Blo 275825 359743 := bstep (se 1 (by rfl) ⟨269807, by rfl⟩ : syracuseStep 359743 = 539615) B539615
theorem B1410209 : Blo 275825 1410209 := bstep (se 2 (by rfl) ⟨528828, by rfl⟩ : syracuseStep 1410209 = 1057657) B1057657
theorem B7112123 : Blo 275825 7112123 := bstep (se 1 (by rfl) ⟨5334092, by rfl⟩ : syracuseStep 7112123 = 10668185) B10668185
theorem B525791 : Blo 275825 525791 := bstep (se 1 (by rfl) ⟨394343, by rfl⟩ : syracuseStep 525791 = 788687) B788687
theorem B5310035 : Blo 275825 5310035 := bstep (se 1 (by rfl) ⟨3982526, by rfl⟩ : syracuseStep 5310035 = 7965053) B7965053
theorem B789439 : Blo 275825 789439 := bstep (se 1 (by rfl) ⟨592079, by rfl⟩ : syracuseStep 789439 = 1184159) B1184159
theorem B1184057 : Blo 275825 1184057 := bstep (se 2 (by rfl) ⟨444021, by rfl⟩ : syracuseStep 1184057 = 888043) B888043
theorem B627227 : Blo 275825 627227 := bstep (se 1 (by rfl) ⟨470420, by rfl⟩ : syracuseStep 627227 = 940841) B940841
theorem B889375 : Blo 275825 889375 := bstep (se 1 (by rfl) ⟨667031, by rfl⟩ : syracuseStep 889375 = 1334063) B1334063
theorem B1414259 : Blo 275825 1414259 := bstep (se 1 (by rfl) ⟨1060694, by rfl⟩ : syracuseStep 1414259 = 2121389) B2121389
theorem B889991 : Blo 275825 889991 := bstep (se 1 (by rfl) ⟨667493, by rfl⟩ : syracuseStep 889991 = 1334987) B1334987
theorem B1578149 : Blo 275825 1578149 := bstep (se 4 (by rfl) ⟨147951, by rfl⟩ : syracuseStep 1578149 = 295903) B295903
theorem B2365037 : Blo 275825 2365037 := bstep (se 3 (by rfl) ⟨443444, by rfl⟩ : syracuseStep 2365037 = 886889) B886889
theorem B8067113 : Blo 275825 8067113 := bstep (se 2 (by rfl) ⟨3025167, by rfl⟩ : syracuseStep 8067113 = 6050335) B6050335
theorem B21567647 : Blo 275825 21567647 := bstep (se 1 (by rfl) ⟨16175735, by rfl⟩ : syracuseStep 21567647 = 32351471) B32351471
theorem B530887 : Blo 275825 530887 := bstep (se 1 (by rfl) ⟨398165, by rfl⟩ : syracuseStep 530887 = 796331) B796331
theorem B19208663 : Blo 275825 19208663 := bstep (se 1 (by rfl) ⟨14406497, by rfl⟩ : syracuseStep 19208663 = 28812995) B28812995
theorem B1350631 : Blo 275825 1350631 := bstep (se 1 (by rfl) ⟨1012973, by rfl⟩ : syracuseStep 1350631 = 2025947) B2025947
theorem B5971103 : Blo 275825 5971103 := bstep (se 1 (by rfl) ⟨4478327, by rfl⟩ : syracuseStep 5971103 = 8956655) B8956655
theorem B7151489 : Blo 275825 7151489 := bstep (se 2 (by rfl) ⟨2681808, by rfl⟩ : syracuseStep 7151489 = 5363617) B5363617
theorem B466985 : Blo 275825 466985 := bstep (se 2 (by rfl) ⟨175119, by rfl⟩ : syracuseStep 466985 = 350239) B350239
theorem B1582523 : Blo 275825 1582523 := bstep (se 1 (by rfl) ⟨1186892, by rfl⟩ : syracuseStep 1582523 = 2373785) B2373785
theorem B1615339 : Blo 275825 1615339 := bstep (se 1 (by rfl) ⟨1211504, by rfl⟩ : syracuseStep 1615339 = 2423009) B2423009
theorem B3384823 : Blo 275825 3384823 := bstep (se 1 (by rfl) ⟨2538617, by rfl⟩ : syracuseStep 3384823 = 5077235) B5077235
theorem B796159 : Blo 275825 796159 := bstep (se 1 (by rfl) ⟨597119, by rfl⟩ : syracuseStep 796159 = 1194239) B1194239
theorem B469631 : Blo 275825 469631 := bstep (se 1 (by rfl) ⟨352223, by rfl⟩ : syracuseStep 469631 = 704447) B704447
theorem B2108753 : Blo 275825 2108753 := bstep (se 2 (by rfl) ⟨790782, by rfl⟩ : syracuseStep 2108753 = 1581565) B1581565
theorem B10628819 : Blo 275825 10628819 := bstep (se 1 (by rfl) ⟨7971614, by rfl⟩ : syracuseStep 10628819 = 15943229) B15943229
theorem B3551141 : Blo 275825 3551141 := bstep (se 4 (by rfl) ⟨332919, by rfl⟩ : syracuseStep 3551141 = 665839) B665839
theorem B4534319 : Blo 275825 4534319 := bstep (se 1 (by rfl) ⟨3400739, by rfl⟩ : syracuseStep 4534319 = 6801479) B6801479
theorem B275903 : Blo 275825 275903 := bstep (se 1 (by rfl) ⟨206927, by rfl⟩ : syracuseStep 275903 = 413855) B413855
theorem B275935 : Blo 275825 275935 := bstep (se 1 (by rfl) ⟨206951, by rfl⟩ : syracuseStep 275935 = 413903) B413903
theorem B277147 : Blo 275825 277147 := bstep (se 1 (by rfl) ⟨207860, by rfl⟩ : syracuseStep 277147 = 415721) B415721
theorem B277159 : Blo 275825 277159 := bstep (se 1 (by rfl) ⟨207869, by rfl⟩ : syracuseStep 277159 = 415739) B415739
theorem B277243 : Blo 275825 277243 := bstep (se 1 (by rfl) ⟨207932, by rfl⟩ : syracuseStep 277243 = 415865) B415865
theorem B277823 : Blo 275825 277823 := bstep (se 1 (by rfl) ⟨208367, by rfl⟩ : syracuseStep 277823 = 416735) B416735
theorem B277951 : Blo 275825 277951 := bstep (se 1 (by rfl) ⟨208463, by rfl⟩ : syracuseStep 277951 = 416927) B416927
theorem B278043 : Blo 275825 278043 := bstep (se 1 (by rfl) ⟨208532, by rfl⟩ : syracuseStep 278043 = 417065) B417065
theorem B278119 : Blo 275825 278119 := bstep (se 1 (by rfl) ⟨208589, by rfl⟩ : syracuseStep 278119 = 417179) B417179
theorem B933497 : Blo 275825 933497 := bstep (se 2 (by rfl) ⟨350061, by rfl⟩ : syracuseStep 933497 = 700123) B700123
theorem B1589129 : Blo 275825 1589129 := bstep (se 2 (by rfl) ⟨595923, by rfl⟩ : syracuseStep 1589129 = 1191847) B1191847
theorem B22921127 : Blo 275825 22921127 := bstep (se 1 (by rfl) ⟨17190845, by rfl⟩ : syracuseStep 22921127 = 34381691) B34381691
theorem B704639 : Blo 275825 704639 := bstep (se 1 (by rfl) ⟨528479, by rfl⟩ : syracuseStep 704639 = 1056959) B1056959
theorem B278695 : Blo 275825 278695 := bstep (se 1 (by rfl) ⟨209021, by rfl⟩ : syracuseStep 278695 = 418043) B418043
theorem B279087 : Blo 275825 279087 := bstep (se 1 (by rfl) ⟨209315, by rfl⟩ : syracuseStep 279087 = 418631) B418631
theorem B279423 : Blo 275825 279423 := bstep (se 1 (by rfl) ⟨209567, by rfl⟩ : syracuseStep 279423 = 419135) B419135
theorem B934847 : Blo 275825 934847 := bstep (se 1 (by rfl) ⟨701135, by rfl⟩ : syracuseStep 934847 = 1402271) B1402271
theorem B1590839 : Blo 275825 1590839 := bstep (se 1 (by rfl) ⟨1193129, by rfl⟩ : syracuseStep 1590839 = 2386259) B2386259
theorem B6014695 : Blo 275825 6014695 := bstep (se 1 (by rfl) ⟨4511021, by rfl⟩ : syracuseStep 6014695 = 9022043) B9022043
theorem B935657 : Blo 275825 935657 := bstep (se 2 (by rfl) ⟨350871, by rfl⟩ : syracuseStep 935657 = 701743) B701743
theorem B313519 : Blo 275825 313519 := bstep (se 1 (by rfl) ⟨235139, by rfl⟩ : syracuseStep 313519 = 470279) B470279
theorem B1525949 : Blo 275825 1525949 := bstep (se 3 (by rfl) ⟨286115, by rfl⟩ : syracuseStep 1525949 = 572231) B572231
theorem B446143 : Blo 275825 446143 := bstep (se 1 (by rfl) ⟨334607, by rfl⟩ : syracuseStep 446143 = 669215) B669215
theorem B413879 : Blo 275825 413879 := bstep (se 1 (by rfl) ⟨310409, by rfl⟩ : syracuseStep 413879 = 620819) B620819
theorem B479657 : Blo 275825 479657 := bstep (se 2 (by rfl) ⟨179871, by rfl⟩ : syracuseStep 479657 = 359743) B359743
theorem B414503 : Blo 275825 414503 := bstep (se 1 (by rfl) ⟨310877, by rfl⟩ : syracuseStep 414503 = 621755) B621755
theorem B414587 : Blo 275825 414587 := bstep (se 1 (by rfl) ⟨310940, by rfl⟩ : syracuseStep 414587 = 621881) B621881
theorem B415079 : Blo 275825 415079 := bstep (se 1 (by rfl) ⟨311309, by rfl⟩ : syracuseStep 415079 = 622619) B622619
theorem B2283137 : Blo 275825 2283137 := bstep (se 2 (by rfl) ⟨856176, by rfl⟩ : syracuseStep 2283137 = 1712353) B1712353
theorem B415391 : Blo 275825 415391 := bstep (se 1 (by rfl) ⟨311543, by rfl⟩ : syracuseStep 415391 = 623087) B623087
theorem B940031 : Blo 275825 940031 := bstep (se 1 (by rfl) ⟨705023, by rfl⟩ : syracuseStep 940031 = 1410047) B1410047
theorem B415775 : Blo 275825 415775 := bstep (se 1 (by rfl) ⟨311831, by rfl⟩ : syracuseStep 415775 = 623663) B623663
theorem B940409 : Blo 275825 940409 := bstep (se 2 (by rfl) ⟨352653, by rfl⟩ : syracuseStep 940409 = 705307) B705307
theorem B416495 : Blo 275825 416495 := bstep (se 1 (by rfl) ⟨312371, by rfl⟩ : syracuseStep 416495 = 624743) B624743
theorem B416633 : Blo 275825 416633 := bstep (se 2 (by rfl) ⟨156237, by rfl⟩ : syracuseStep 416633 = 312475) B312475
theorem B417023 : Blo 275825 417023 := bstep (se 1 (by rfl) ⟨312767, by rfl⟩ : syracuseStep 417023 = 625535) B625535
theorem B712091 : Blo 275825 712091 := bstep (se 1 (by rfl) ⟨534068, by rfl⟩ : syracuseStep 712091 = 1068137) B1068137
theorem B417335 : Blo 275825 417335 := bstep (se 1 (by rfl) ⟨313001, by rfl⟩ : syracuseStep 417335 = 626003) B626003
theorem B4776407 : Blo 275825 4776407 := bstep (se 1 (by rfl) ⟨3582305, by rfl⟩ : syracuseStep 4776407 = 7164611) B7164611
theorem B418271 : Blo 275825 418271 := bstep (se 1 (by rfl) ⟨313703, by rfl⟩ : syracuseStep 418271 = 627407) B627407
theorem B1401623 : Blo 275825 1401623 := bstep (se 1 (by rfl) ⟨1051217, by rfl⟩ : syracuseStep 1401623 = 2102435) B2102435
theorem B418697 : Blo 275825 418697 := bstep (se 2 (by rfl) ⟨157011, by rfl⟩ : syracuseStep 418697 = 314023) B314023
theorem B418847 : Blo 275825 418847 := bstep (se 1 (by rfl) ⟨314135, by rfl⟩ : syracuseStep 418847 = 628271) B628271
theorem B3402607 : Blo 275825 3402607 := bstep (se 1 (by rfl) ⟨2551955, by rfl⟩ : syracuseStep 3402607 = 5103911) B5103911
theorem B1404701 : Blo 275825 1404701 := bstep (se 3 (by rfl) ⟨263381, by rfl⟩ : syracuseStep 1404701 = 526763) B526763
theorem B2684269 : Blo 275825 2684269 := bstep (se 3 (by rfl) ⟨503300, by rfl⟩ : syracuseStep 2684269 = 1006601) B1006601
theorem B719657 : Blo 275825 719657 := bstep (se 2 (by rfl) ⟨269871, by rfl⟩ : syracuseStep 719657 = 539743) B539743
theorem B14744875 : Blo 275825 14744875 := bstep (se 1 (by rfl) ⟨11058656, by rfl⟩ : syracuseStep 14744875 = 22117313) B22117313
theorem B623231 : Blo 275825 623231 := bstep (se 1 (by rfl) ⟨467423, by rfl⟩ : syracuseStep 623231 = 934847) B934847
theorem B3540023 : Blo 275825 3540023 := bstep (se 1 (by rfl) ⟨2655017, by rfl⟩ : syracuseStep 3540023 = 5310035) B5310035
theorem B623771 : Blo 275825 623771 := bstep (se 1 (by rfl) ⟨467828, by rfl⟩ : syracuseStep 623771 = 935657) B935657
theorem B1017299 : Blo 275825 1017299 := bstep (se 1 (by rfl) ⟨762974, by rfl⟩ : syracuseStep 1017299 = 1525949) B1525949
theorem B789371 : Blo 275825 789371 := bstep (se 1 (by rfl) ⟨592028, by rfl⟩ : syracuseStep 789371 = 1184057) B1184057
theorem B593327 : Blo 275825 593327 := bstep (se 1 (by rfl) ⟨444995, by rfl⟩ : syracuseStep 593327 = 889991) B889991
theorem B1052099 : Blo 275825 1052099 := bstep (se 1 (by rfl) ⟨789074, by rfl⟩ : syracuseStep 1052099 = 1578149) B1578149
theorem B1576691 : Blo 275825 1576691 := bstep (se 1 (by rfl) ⟨1182518, by rfl⟩ : syracuseStep 1576691 = 2365037) B2365037
theorem B1052585 : Blo 275825 1052585 := bstep (se 2 (by rfl) ⟨394719, by rfl⟩ : syracuseStep 1052585 = 789439) B789439
theorem B626687 : Blo 275825 626687 := bstep (se 1 (by rfl) ⟨470015, by rfl⟩ : syracuseStep 626687 = 940031) B940031
theorem B5378075 : Blo 275825 5378075 := bstep (se 1 (by rfl) ⟨4033556, by rfl⟩ : syracuseStep 5378075 = 8067113) B8067113
theorem B626939 : Blo 275825 626939 := bstep (se 1 (by rfl) ⟨470204, by rfl⟩ : syracuseStep 626939 = 940409) B940409
theorem B594857 : Blo 275825 594857 := bstep (se 2 (by rfl) ⟨223071, by rfl⟩ : syracuseStep 594857 = 446143) B446143
theorem B3184271 : Blo 275825 3184271 := bstep (se 1 (by rfl) ⟨2388203, by rfl⟩ : syracuseStep 3184271 = 4776407) B4776407
theorem B57513725 : Blo 275825 57513725 := bstep (se 3 (by rfl) ⟨10783823, by rfl⟩ : syracuseStep 57513725 = 21567647) B21567647
theorem B1185833 : Blo 275825 1185833 := bstep (se 2 (by rfl) ⟨444687, by rfl⟩ : syracuseStep 1185833 = 889375) B889375
theorem B1055015 : Blo 275825 1055015 := bstep (se 1 (by rfl) ⟨791261, by rfl⟩ : syracuseStep 1055015 = 1582523) B1582523
theorem B3579025 : Blo 275825 3579025 := bstep (se 2 (by rfl) ⟨1342134, by rfl⟩ : syracuseStep 3579025 = 2684269) B2684269
theorem B7085879 : Blo 275825 7085879 := bstep (se 1 (by rfl) ⟨5314409, by rfl⟩ : syracuseStep 7085879 = 10628819) B10628819
theorem B2367427 : Blo 275825 2367427 := bstep (se 1 (by rfl) ⟨1775570, by rfl⟩ : syracuseStep 2367427 = 3551141) B3551141
theorem B3022879 : Blo 275825 3022879 := bstep (se 1 (by rfl) ⟨2267159, by rfl⟩ : syracuseStep 3022879 = 4534319) B4534319
theorem B1059419 : Blo 275825 1059419 := bstep (se 1 (by rfl) ⟨794564, by rfl⟩ : syracuseStep 1059419 = 1589129) B1589129
theorem B15280751 : Blo 275825 15280751 := bstep (se 1 (by rfl) ⟨11460563, by rfl⟩ : syracuseStep 15280751 = 22921127) B22921127
theorem B469759 : Blo 275825 469759 := bstep (se 1 (by rfl) ⟨352319, by rfl⟩ : syracuseStep 469759 = 704639) B704639
theorem B1060559 : Blo 275825 1060559 := bstep (se 1 (by rfl) ⟨795419, by rfl⟩ : syracuseStep 1060559 = 1590839) B1590839
theorem B1061545 : Blo 275825 1061545 := bstep (se 2 (by rfl) ⟨398079, by rfl⟩ : syracuseStep 1061545 = 796159) B796159
theorem B275919 : Blo 275825 275919 := bstep (se 1 (by rfl) ⟨206939, by rfl⟩ : syracuseStep 275919 = 413879) B413879
theorem B276335 : Blo 275825 276335 := bstep (se 1 (by rfl) ⟨207251, by rfl⟩ : syracuseStep 276335 = 414503) B414503
theorem B276391 : Blo 275825 276391 := bstep (se 1 (by rfl) ⟨207293, by rfl⟩ : syracuseStep 276391 = 414587) B414587
theorem B276719 : Blo 275825 276719 := bstep (se 1 (by rfl) ⟨207539, by rfl⟩ : syracuseStep 276719 = 415079) B415079
theorem B1522091 : Blo 275825 1522091 := bstep (se 1 (by rfl) ⟨1141568, by rfl⟩ : syracuseStep 1522091 = 2283137) B2283137
theorem B276927 : Blo 275825 276927 := bstep (se 1 (by rfl) ⟨207695, by rfl⟩ : syracuseStep 276927 = 415391) B415391
theorem B4536809 : Blo 275825 4536809 := bstep (se 2 (by rfl) ⟨1701303, by rfl⟩ : syracuseStep 4536809 = 3402607) B3402607
theorem B277183 : Blo 275825 277183 := bstep (se 1 (by rfl) ⟨207887, by rfl⟩ : syracuseStep 277183 = 415775) B415775
theorem B277663 : Blo 275825 277663 := bstep (se 1 (by rfl) ⟨208247, by rfl⟩ : syracuseStep 277663 = 416495) B416495
theorem B277755 : Blo 275825 277755 := bstep (se 1 (by rfl) ⟨208316, by rfl⟩ : syracuseStep 277755 = 416633) B416633
theorem B3980735 : Blo 275825 3980735 := bstep (se 1 (by rfl) ⟨2985551, by rfl⟩ : syracuseStep 3980735 = 5971103) B5971103
theorem B278015 : Blo 275825 278015 := bstep (se 1 (by rfl) ⟨208511, by rfl⟩ : syracuseStep 278015 = 417023) B417023
theorem B278223 : Blo 275825 278223 := bstep (se 1 (by rfl) ⟨208667, by rfl⟩ : syracuseStep 278223 = 417335) B417335
theorem B4767659 : Blo 275825 4767659 := bstep (se 1 (by rfl) ⟨3575744, by rfl⟩ : syracuseStep 4767659 = 7151489) B7151489
theorem B311323 : Blo 275825 311323 := bstep (se 1 (by rfl) ⟨233492, by rfl⟩ : syracuseStep 311323 = 466985) B466985
theorem B278847 : Blo 275825 278847 := bstep (se 1 (by rfl) ⟨209135, by rfl⟩ : syracuseStep 278847 = 418271) B418271
theorem B934415 : Blo 275825 934415 := bstep (se 1 (by rfl) ⟨700811, by rfl⟩ : syracuseStep 934415 = 1401623) B1401623
theorem B279131 : Blo 275825 279131 := bstep (se 1 (by rfl) ⟨209348, by rfl⟩ : syracuseStep 279131 = 418697) B418697
theorem B279231 : Blo 275825 279231 := bstep (se 1 (by rfl) ⟨209423, by rfl⟩ : syracuseStep 279231 = 418847) B418847
theorem B313087 : Blo 275825 313087 := bstep (se 1 (by rfl) ⟨234815, by rfl⟩ : syracuseStep 313087 = 469631) B469631
theorem B936467 : Blo 275825 936467 := bstep (se 1 (by rfl) ⟨702350, by rfl⟩ : syracuseStep 936467 = 1404701) B1404701
theorem B707849 : Blo 275825 707849 := bstep (se 2 (by rfl) ⟨265443, by rfl⟩ : syracuseStep 707849 = 530887) B530887
theorem B479771 : Blo 275825 479771 := bstep (se 1 (by rfl) ⟨359828, by rfl⟩ : syracuseStep 479771 = 719657) B719657
theorem B940139 : Blo 275825 940139 := bstep (se 1 (by rfl) ⟨705104, by rfl⟩ : syracuseStep 940139 = 1410209) B1410209
theorem B4741415 : Blo 275825 4741415 := bstep (se 1 (by rfl) ⟨3556061, by rfl⟩ : syracuseStep 4741415 = 7112123) B7112123
theorem B2153785 : Blo 275825 2153785 := bstep (se 2 (by rfl) ⟨807669, by rfl⟩ : syracuseStep 2153785 = 1615339) B1615339
theorem B4513097 : Blo 275825 4513097 := bstep (se 2 (by rfl) ⟨1692411, by rfl⟩ : syracuseStep 4513097 = 3384823) B3384823
theorem B8019593 : Blo 275825 8019593 := bstep (se 2 (by rfl) ⟨3007347, by rfl⟩ : syracuseStep 8019593 = 6014695) B6014695
theorem B418025 : Blo 275825 418025 := bstep (se 2 (by rfl) ⟨156759, by rfl⟩ : syracuseStep 418025 = 313519) B313519
theorem B319771 : Blo 275825 319771 := bstep (se 1 (by rfl) ⟨239828, by rfl⟩ : syracuseStep 319771 = 479657) B479657
theorem B418151 : Blo 275825 418151 := bstep (se 1 (by rfl) ⟨313613, by rfl⟩ : syracuseStep 418151 = 627227) B627227
theorem B942839 : Blo 275825 942839 := bstep (se 1 (by rfl) ⟨707129, by rfl⟩ : syracuseStep 942839 = 1414259) B1414259
theorem B1402109 : Blo 275825 1402109 := bstep (se 3 (by rfl) ⟨262895, by rfl⟩ : syracuseStep 1402109 = 525791) B525791
theorem B12805775 : Blo 275825 12805775 := bstep (se 1 (by rfl) ⟨9604331, by rfl⟩ : syracuseStep 12805775 = 19208663) B19208663
theorem B1405835 : Blo 275825 1405835 := bstep (se 1 (by rfl) ⟨1054376, by rfl⟩ : syracuseStep 1405835 = 2108753) B2108753
theorem B1898909 : Blo 275825 1898909 := bstep (se 3 (by rfl) ⟨356045, by rfl⟩ : syracuseStep 1898909 = 712091) B712091
theorem B1800841 : Blo 275825 1800841 := bstep (se 2 (by rfl) ⟨675315, by rfl⟩ : syracuseStep 1800841 = 1350631) B1350631
theorem B19659833 : Blo 275825 19659833 := bstep (se 2 (by rfl) ⟨7372437, by rfl⟩ : syracuseStep 19659833 = 14744875) B14744875
theorem B622331 : Blo 275825 622331 := bstep (se 1 (by rfl) ⟨466748, by rfl⟩ : syracuseStep 622331 = 933497) B933497
theorem B4030505 : Blo 275825 4030505 := bstep (se 2 (by rfl) ⟨1511439, by rfl⟩ : syracuseStep 4030505 = 3022879) B3022879
theorem B622943 : Blo 275825 622943 := bstep (se 1 (by rfl) ⟨467207, by rfl⟩ : syracuseStep 622943 = 934415) B934415
theorem B2360015 : Blo 275825 2360015 := bstep (se 1 (by rfl) ⟨1770011, by rfl⟩ : syracuseStep 2360015 = 3540023) B3540023
theorem B1705445 : Blo 275825 1705445 := bstep (se 4 (by rfl) ⟨159885, by rfl⟩ : syracuseStep 1705445 = 319771) B319771
theorem B624311 : Blo 275825 624311 := bstep (se 1 (by rfl) ⟨468233, by rfl⟩ : syracuseStep 624311 = 936467) B936467
theorem B526247 : Blo 275825 526247 := bstep (se 1 (by rfl) ⟨394685, by rfl⟩ : syracuseStep 526247 = 789371) B789371
theorem B395551 : Blo 275825 395551 := bstep (se 1 (by rfl) ⟨296663, by rfl⟩ : syracuseStep 395551 = 593327) B593327
theorem B1051127 : Blo 275825 1051127 := bstep (se 1 (by rfl) ⟨788345, by rfl⟩ : syracuseStep 1051127 = 1576691) B1576691
theorem B396571 : Blo 275825 396571 := bstep (se 1 (by rfl) ⟨297428, by rfl⟩ : syracuseStep 396571 = 594857) B594857
theorem B626345 : Blo 275825 626345 := bstep (se 2 (by rfl) ⟨234879, by rfl⟩ : syracuseStep 626345 = 469759) B469759
theorem B38342483 : Blo 275825 38342483 := bstep (se 1 (by rfl) ⟨28756862, by rfl⟩ : syracuseStep 38342483 = 57513725) B57513725
theorem B790555 : Blo 275825 790555 := bstep (se 1 (by rfl) ⟨592916, by rfl⟩ : syracuseStep 790555 = 1185833) B1185833
theorem B626759 : Blo 275825 626759 := bstep (se 1 (by rfl) ⟨470069, by rfl⟩ : syracuseStep 626759 = 940139) B940139
theorem B5346395 : Blo 275825 5346395 := bstep (se 1 (by rfl) ⟨4009796, by rfl⟩ : syracuseStep 5346395 = 8019593) B8019593
theorem B4723919 : Blo 275825 4723919 := bstep (se 1 (by rfl) ⟨3542939, by rfl⟩ : syracuseStep 4723919 = 7085879) B7085879
theorem B628559 : Blo 275825 628559 := bstep (se 1 (by rfl) ⟨471419, by rfl⟩ : syracuseStep 628559 = 942839) B942839
theorem B1415393 : Blo 275825 1415393 := bstep (se 2 (by rfl) ⟨530772, by rfl⟩ : syracuseStep 1415393 = 1061545) B1061545
theorem B2401121 : Blo 275825 2401121 := bstep (se 2 (by rfl) ⟨900420, by rfl⟩ : syracuseStep 2401121 = 1800841) B1800841
theorem B12034925 : Blo 275825 12034925 := bstep (se 3 (by rfl) ⟨2256548, by rfl⟩ : syracuseStep 12034925 = 4513097) B4513097
theorem B3024539 : Blo 275825 3024539 := bstep (se 1 (by rfl) ⟨2268404, by rfl⟩ : syracuseStep 3024539 = 4536809) B4536809
theorem B3156569 : Blo 275825 3156569 := bstep (se 2 (by rfl) ⟨1183713, by rfl⟩ : syracuseStep 3156569 = 2367427) B2367427
theorem B471899 : Blo 275825 471899 := bstep (se 1 (by rfl) ⟨353924, by rfl⟩ : syracuseStep 471899 = 707849) B707849
theorem B701399 : Blo 275825 701399 := bstep (se 1 (by rfl) ⟨526049, by rfl⟩ : syracuseStep 701399 = 1052099) B1052099
theorem B701723 : Blo 275825 701723 := bstep (se 1 (by rfl) ⟨526292, by rfl⟩ : syracuseStep 701723 = 1052585) B1052585
theorem B3585383 : Blo 275825 3585383 := bstep (se 1 (by rfl) ⟨2689037, by rfl⟩ : syracuseStep 3585383 = 5378075) B5378075
theorem B3160943 : Blo 275825 3160943 := bstep (se 1 (by rfl) ⟨2370707, by rfl⟩ : syracuseStep 3160943 = 4741415) B4741415
theorem B703343 : Blo 275825 703343 := bstep (se 1 (by rfl) ⟨527507, by rfl⟩ : syracuseStep 703343 = 1055015) B1055015
theorem B278683 : Blo 275825 278683 := bstep (se 1 (by rfl) ⟨209012, by rfl⟩ : syracuseStep 278683 = 418025) B418025
theorem B278767 : Blo 275825 278767 := bstep (se 1 (by rfl) ⟨209075, by rfl⟩ : syracuseStep 278767 = 418151) B418151
theorem B934739 : Blo 275825 934739 := bstep (se 1 (by rfl) ⟨701054, by rfl⟩ : syracuseStep 934739 = 1402109) B1402109
theorem B8537183 : Blo 275825 8537183 := bstep (se 1 (by rfl) ⟨6402887, by rfl⟩ : syracuseStep 8537183 = 12805775) B12805775
theorem B706279 : Blo 275825 706279 := bstep (se 1 (by rfl) ⟨529709, by rfl⟩ : syracuseStep 706279 = 1059419) B1059419
theorem B707039 : Blo 275825 707039 := bstep (se 1 (by rfl) ⟨530279, by rfl⟩ : syracuseStep 707039 = 1060559) B1060559
theorem B937223 : Blo 275825 937223 := bstep (se 1 (by rfl) ⟨702917, by rfl⟩ : syracuseStep 937223 = 1405835) B1405835
theorem B4772033 : Blo 275825 4772033 := bstep (se 2 (by rfl) ⟨1789512, by rfl⟩ : syracuseStep 4772033 = 3579025) B3579025
theorem B1265939 : Blo 275825 1265939 := bstep (se 1 (by rfl) ⟨949454, by rfl⟩ : syracuseStep 1265939 = 1898909) B1898909
theorem B2871713 : Blo 275825 2871713 := bstep (se 2 (by rfl) ⟨1076892, by rfl⟩ : syracuseStep 2871713 = 2153785) B2153785
theorem B414887 : Blo 275825 414887 := bstep (se 1 (by rfl) ⟨311165, by rfl⟩ : syracuseStep 414887 = 622331) B622331
theorem B415097 : Blo 275825 415097 := bstep (se 2 (by rfl) ⟨155661, by rfl⟩ : syracuseStep 415097 = 311323) B311323
theorem B415487 : Blo 275825 415487 := bstep (se 1 (by rfl) ⟨311615, by rfl⟩ : syracuseStep 415487 = 623231) B623231
theorem B415847 : Blo 275825 415847 := bstep (se 1 (by rfl) ⟨311885, by rfl⟩ : syracuseStep 415847 = 623771) B623771
theorem B417449 : Blo 275825 417449 := bstep (se 2 (by rfl) ⟨156543, by rfl⟩ : syracuseStep 417449 = 313087) B313087
theorem B417791 : Blo 275825 417791 := bstep (se 1 (by rfl) ⟨313343, by rfl⟩ : syracuseStep 417791 = 626687) B626687
theorem B417959 : Blo 275825 417959 := bstep (se 1 (by rfl) ⟨313469, by rfl⟩ : syracuseStep 417959 = 626939) B626939
theorem B319847 : Blo 275825 319847 := bstep (se 1 (by rfl) ⟨239885, by rfl⟩ : syracuseStep 319847 = 479771) B479771
theorem B2122847 : Blo 275825 2122847 := bstep (se 1 (by rfl) ⟨1592135, by rfl⟩ : syracuseStep 2122847 = 3184271) B3184271
theorem B2712797 : Blo 275825 2712797 := bstep (se 3 (by rfl) ⟨508649, by rfl⟩ : syracuseStep 2712797 = 1017299) B1017299
theorem B10187167 : Blo 275825 10187167 := bstep (se 1 (by rfl) ⟨7640375, by rfl⟩ : syracuseStep 10187167 = 15280751) B15280751
theorem B1014727 : Blo 275825 1014727 := bstep (se 1 (by rfl) ⟨761045, by rfl⟩ : syracuseStep 1014727 = 1522091) B1522091
theorem B13106555 : Blo 275825 13106555 := bstep (se 1 (by rfl) ⟨9829916, by rfl⟩ : syracuseStep 13106555 = 19659833) B19659833
theorem B2653823 : Blo 275825 2653823 := bstep (se 1 (by rfl) ⟨1990367, by rfl⟩ : syracuseStep 2653823 = 3980735) B3980735
theorem B3178439 : Blo 275825 3178439 := bstep (se 1 (by rfl) ⟨2383829, by rfl⟩ : syracuseStep 3178439 = 4767659) B4767659
theorem B2687003 : Blo 275825 2687003 := bstep (se 1 (by rfl) ⟨2015252, by rfl⟩ : syracuseStep 2687003 = 4030505) B4030505
theorem B1573343 : Blo 275825 1573343 := bstep (se 1 (by rfl) ⟨1180007, by rfl⟩ : syracuseStep 1573343 = 2360015) B2360015
theorem B623159 : Blo 275825 623159 := bstep (se 1 (by rfl) ⟨467369, by rfl⟩ : syracuseStep 623159 = 934739) B934739
theorem B852925 : Blo 275825 852925 := bstep (se 3 (by rfl) ⟨159923, by rfl⟩ : syracuseStep 852925 = 319847) B319847
theorem B624815 : Blo 275825 624815 := bstep (se 1 (by rfl) ⟨468611, by rfl⟩ : syracuseStep 624815 = 937223) B937223
theorem B25561655 : Blo 275825 25561655 := bstep (se 1 (by rfl) ⟨19171241, by rfl⟩ : syracuseStep 25561655 = 38342483) B38342483
theorem B3181355 : Blo 275825 3181355 := bstep (se 1 (by rfl) ⟨2386016, by rfl⟩ : syracuseStep 3181355 = 4772033) B4772033
theorem B527401 : Blo 275825 527401 := bstep (se 2 (by rfl) ⟨197775, by rfl⟩ : syracuseStep 527401 = 395551) B395551
theorem B3149279 : Blo 275825 3149279 := bstep (se 1 (by rfl) ⟨2361959, by rfl⟩ : syracuseStep 3149279 = 4723919) B4723919
theorem B528761 : Blo 275825 528761 := bstep (se 2 (by rfl) ⟨198285, by rfl⟩ : syracuseStep 528761 = 396571) B396571
theorem B1054073 : Blo 275825 1054073 := bstep (se 2 (by rfl) ⟨395277, by rfl⟩ : syracuseStep 1054073 = 790555) B790555
theorem B1415231 : Blo 275825 1415231 := bstep (se 1 (by rfl) ⟨1061423, by rfl⟩ : syracuseStep 1415231 = 2122847) B2122847
theorem B1808531 : Blo 275825 1808531 := bstep (se 1 (by rfl) ⟨1356398, by rfl⟩ : syracuseStep 1808531 = 2712797) B2712797
theorem B2104379 : Blo 275825 2104379 := bstep (se 1 (by rfl) ⟨1578284, by rfl⟩ : syracuseStep 2104379 = 3156569) B3156569
theorem B467599 : Blo 275825 467599 := bstep (se 1 (by rfl) ⟨350699, by rfl⟩ : syracuseStep 467599 = 701399) B701399
theorem B467815 : Blo 275825 467815 := bstep (se 1 (by rfl) ⟨350861, by rfl⟩ : syracuseStep 467815 = 701723) B701723
theorem B1352969 : Blo 275825 1352969 := bstep (se 2 (by rfl) ⟨507363, by rfl⟩ : syracuseStep 1352969 = 1014727) B1014727
theorem B2107295 : Blo 275825 2107295 := bstep (se 1 (by rfl) ⟨1580471, by rfl⟩ : syracuseStep 2107295 = 3160943) B3160943
theorem B468895 : Blo 275825 468895 := bstep (se 1 (by rfl) ⟨351671, by rfl⟩ : syracuseStep 468895 = 703343) B703343
theorem B471359 : Blo 275825 471359 := bstep (se 1 (by rfl) ⟨353519, by rfl⟩ : syracuseStep 471359 = 707039) B707039
theorem B700751 : Blo 275825 700751 := bstep (se 1 (by rfl) ⟨525563, by rfl⟩ : syracuseStep 700751 = 1051127) B1051127
theorem B6402989 : Blo 275825 6402989 := bstep (se 3 (by rfl) ⟨1200560, by rfl⟩ : syracuseStep 6402989 = 2401121) B2401121
theorem B1914475 : Blo 275825 1914475 := bstep (se 1 (by rfl) ⟨1435856, by rfl⟩ : syracuseStep 1914475 = 2871713) B2871713
theorem B276591 : Blo 275825 276591 := bstep (se 1 (by rfl) ⟨207443, by rfl⟩ : syracuseStep 276591 = 414887) B414887
theorem B276731 : Blo 275825 276731 := bstep (se 1 (by rfl) ⟨207548, by rfl⟩ : syracuseStep 276731 = 415097) B415097
theorem B276991 : Blo 275825 276991 := bstep (se 1 (by rfl) ⟨207743, by rfl⟩ : syracuseStep 276991 = 415487) B415487
theorem B277231 : Blo 275825 277231 := bstep (se 1 (by rfl) ⟨207923, by rfl⟩ : syracuseStep 277231 = 415847) B415847
theorem B278299 : Blo 275825 278299 := bstep (se 1 (by rfl) ⟨208724, by rfl⟩ : syracuseStep 278299 = 417449) B417449
theorem B278527 : Blo 275825 278527 := bstep (se 1 (by rfl) ⟨208895, by rfl⟩ : syracuseStep 278527 = 417791) B417791
theorem B278639 : Blo 275825 278639 := bstep (se 1 (by rfl) ⟨208979, by rfl⟩ : syracuseStep 278639 = 417959) B417959
theorem B13582889 : Blo 275825 13582889 := bstep (se 2 (by rfl) ⟨5093583, by rfl⟩ : syracuseStep 13582889 = 10187167) B10187167
theorem B2016359 : Blo 275825 2016359 := bstep (se 1 (by rfl) ⟨1512269, by rfl⟩ : syracuseStep 2016359 = 3024539) B3024539
theorem B314599 : Blo 275825 314599 := bstep (se 1 (by rfl) ⟨235949, by rfl⟩ : syracuseStep 314599 = 471899) B471899
theorem B8737703 : Blo 275825 8737703 := bstep (se 1 (by rfl) ⟨6553277, by rfl⟩ : syracuseStep 8737703 = 13106555) B13106555
theorem B2118959 : Blo 275825 2118959 := bstep (se 1 (by rfl) ⟨1589219, by rfl⟩ : syracuseStep 2118959 = 3178439) B3178439
theorem B415295 : Blo 275825 415295 := bstep (se 1 (by rfl) ⟨311471, by rfl⟩ : syracuseStep 415295 = 622943) B622943
theorem B5691455 : Blo 275825 5691455 := bstep (se 1 (by rfl) ⟨4268591, by rfl⟩ : syracuseStep 5691455 = 8537183) B8537183
theorem B1136963 : Blo 275825 1136963 := bstep (se 1 (by rfl) ⟨852722, by rfl⟩ : syracuseStep 1136963 = 1705445) B1705445
theorem B416207 : Blo 275825 416207 := bstep (se 1 (by rfl) ⟨312155, by rfl⟩ : syracuseStep 416207 = 624311) B624311
theorem B350831 : Blo 275825 350831 := bstep (se 1 (by rfl) ⟨263123, by rfl⟩ : syracuseStep 350831 = 526247) B526247
theorem B941705 : Blo 275825 941705 := bstep (se 2 (by rfl) ⟨353139, by rfl⟩ : syracuseStep 941705 = 706279) B706279
theorem B417563 : Blo 275825 417563 := bstep (se 1 (by rfl) ⟨313172, by rfl⟩ : syracuseStep 417563 = 626345) B626345
theorem B417839 : Blo 275825 417839 := bstep (se 1 (by rfl) ⟨313379, by rfl⟩ : syracuseStep 417839 = 626759) B626759
theorem B843959 : Blo 275825 843959 := bstep (se 1 (by rfl) ⟨632969, by rfl⟩ : syracuseStep 843959 = 1265939) B1265939
theorem B3564263 : Blo 275825 3564263 := bstep (se 1 (by rfl) ⟨2673197, by rfl⟩ : syracuseStep 3564263 = 5346395) B5346395
theorem B419039 : Blo 275825 419039 := bstep (se 1 (by rfl) ⟨314279, by rfl⟩ : syracuseStep 419039 = 628559) B628559
theorem B943595 : Blo 275825 943595 := bstep (se 1 (by rfl) ⟨707696, by rfl⟩ : syracuseStep 943595 = 1415393) B1415393
theorem B8023283 : Blo 275825 8023283 := bstep (se 1 (by rfl) ⟨6017462, by rfl⟩ : syracuseStep 8023283 = 12034925) B12034925
theorem B2390255 : Blo 275825 2390255 := bstep (se 1 (by rfl) ⟨1792691, by rfl⟩ : syracuseStep 2390255 = 3585383) B3585383
theorem B1769215 : Blo 275825 1769215 := bstep (se 1 (by rfl) ⟨1326911, by rfl⟩ : syracuseStep 1769215 = 2653823) B2653823
theorem B1048895 : Blo 275825 1048895 := bstep (se 1 (by rfl) ⟨786671, by rfl⟩ : syracuseStep 1048895 = 1573343) B1573343
theorem B1344239 : Blo 275825 1344239 := bstep (se 1 (by rfl) ⟨1008179, by rfl⟩ : syracuseStep 1344239 = 2016359) B2016359
theorem B623465 : Blo 275825 623465 := bstep (se 2 (by rfl) ⟨233799, by rfl⟩ : syracuseStep 623465 = 467599) B467599
theorem B623753 : Blo 275825 623753 := bstep (se 2 (by rfl) ⟨233907, by rfl⟩ : syracuseStep 623753 = 467815) B467815
theorem B17041103 : Blo 275825 17041103 := bstep (se 1 (by rfl) ⟨12780827, by rfl⟩ : syracuseStep 17041103 = 25561655) B25561655
theorem B2099519 : Blo 275825 2099519 := bstep (se 1 (by rfl) ⟨1574639, by rfl⟩ : syracuseStep 2099519 = 3149279) B3149279
theorem B625193 : Blo 275825 625193 := bstep (se 2 (by rfl) ⟨234447, by rfl⟩ : syracuseStep 625193 = 468895) B468895
theorem B1412639 : Blo 275825 1412639 := bstep (se 1 (by rfl) ⟨1059479, by rfl⟩ : syracuseStep 1412639 = 2118959) B2118959
theorem B627803 : Blo 275825 627803 := bstep (se 1 (by rfl) ⟨470852, by rfl⟩ : syracuseStep 627803 = 941705) B941705
theorem B562639 : Blo 275825 562639 := bstep (se 1 (by rfl) ⟨421979, by rfl⟩ : syracuseStep 562639 = 843959) B843959
theorem B629063 : Blo 275825 629063 := bstep (se 1 (by rfl) ⟨471797, by rfl⟩ : syracuseStep 629063 = 943595) B943595
theorem B5348855 : Blo 275825 5348855 := bstep (se 1 (by rfl) ⟨4011641, by rfl⟩ : syracuseStep 5348855 = 8023283) B8023283
theorem B467167 : Blo 275825 467167 := bstep (se 1 (by rfl) ⟨350375, by rfl⟩ : syracuseStep 467167 = 700751) B700751
theorem B4268659 : Blo 275825 4268659 := bstep (se 1 (by rfl) ⟨3201494, by rfl⟩ : syracuseStep 4268659 = 6402989) B6402989
theorem B9055259 : Blo 275825 9055259 := bstep (se 1 (by rfl) ⟨6791444, by rfl⟩ : syracuseStep 9055259 = 13582889) B13582889
theorem B702715 : Blo 275825 702715 := bstep (se 1 (by rfl) ⟨527036, by rfl⟩ : syracuseStep 702715 = 1054073) B1054073
theorem B276863 : Blo 275825 276863 := bstep (se 1 (by rfl) ⟨207647, by rfl⟩ : syracuseStep 276863 = 415295) B415295
theorem B703201 : Blo 275825 703201 := bstep (se 2 (by rfl) ⟨263700, by rfl⟩ : syracuseStep 703201 = 527401) B527401
theorem B277471 : Blo 275825 277471 := bstep (se 1 (by rfl) ⟨208103, by rfl⟩ : syracuseStep 277471 = 416207) B416207
theorem B278375 : Blo 275825 278375 := bstep (se 1 (by rfl) ⟨208781, by rfl⟩ : syracuseStep 278375 = 417563) B417563
theorem B278559 : Blo 275825 278559 := bstep (se 1 (by rfl) ⟨208919, by rfl⟩ : syracuseStep 278559 = 417839) B417839
theorem B2376175 : Blo 275825 2376175 := bstep (se 1 (by rfl) ⟨1782131, by rfl⟩ : syracuseStep 2376175 = 3564263) B3564263
theorem B279359 : Blo 275825 279359 := bstep (se 1 (by rfl) ⟨209519, by rfl⟩ : syracuseStep 279359 = 419039) B419039
theorem B901979 : Blo 275825 901979 := bstep (se 1 (by rfl) ⟨676484, by rfl⟩ : syracuseStep 901979 = 1352969) B1352969
theorem B3031901 : Blo 275825 3031901 := bstep (se 3 (by rfl) ⟨568481, by rfl⟩ : syracuseStep 3031901 = 1136963) B1136963
theorem B935549 : Blo 275825 935549 := bstep (se 3 (by rfl) ⟨175415, by rfl⟩ : syracuseStep 935549 = 350831) B350831
theorem B314239 : Blo 275825 314239 := bstep (se 1 (by rfl) ⟨235679, by rfl⟩ : syracuseStep 314239 = 471359) B471359
theorem B1593503 : Blo 275825 1593503 := bstep (se 1 (by rfl) ⟨1195127, by rfl⟩ : syracuseStep 1593503 = 2390255) B2390255
theorem B1791335 : Blo 275825 1791335 := bstep (se 1 (by rfl) ⟨1343501, by rfl⟩ : syracuseStep 1791335 = 2687003) B2687003
theorem B415439 : Blo 275825 415439 := bstep (se 1 (by rfl) ⟨311579, by rfl⟩ : syracuseStep 415439 = 623159) B623159
theorem B1137233 : Blo 275825 1137233 := bstep (se 2 (by rfl) ⟨426462, by rfl⟩ : syracuseStep 1137233 = 852925) B852925
theorem B416543 : Blo 275825 416543 := bstep (se 1 (by rfl) ⟨312407, by rfl⟩ : syracuseStep 416543 = 624815) B624815
theorem B2120903 : Blo 275825 2120903 := bstep (se 1 (by rfl) ⟨1590677, by rfl⟩ : syracuseStep 2120903 = 3181355) B3181355
theorem B352507 : Blo 275825 352507 := bstep (se 1 (by rfl) ⟨264380, by rfl⟩ : syracuseStep 352507 = 528761) B528761
theorem B5825135 : Blo 275825 5825135 := bstep (se 1 (by rfl) ⟨4368851, by rfl⟩ : syracuseStep 5825135 = 8737703) B8737703
theorem B3794303 : Blo 275825 3794303 := bstep (se 1 (by rfl) ⟨2845727, by rfl⟩ : syracuseStep 3794303 = 5691455) B5691455
theorem B943487 : Blo 275825 943487 := bstep (se 1 (by rfl) ⟨707615, by rfl⟩ : syracuseStep 943487 = 1415231) B1415231
theorem B1205687 : Blo 275825 1205687 := bstep (se 1 (by rfl) ⟨904265, by rfl⟩ : syracuseStep 1205687 = 1808531) B1808531
theorem B419465 : Blo 275825 419465 := bstep (se 2 (by rfl) ⟨157299, by rfl⟩ : syracuseStep 419465 = 314599) B314599
theorem B1402919 : Blo 275825 1402919 := bstep (se 1 (by rfl) ⟨1052189, by rfl⟩ : syracuseStep 1402919 = 2104379) B2104379
theorem B1404863 : Blo 275825 1404863 := bstep (se 1 (by rfl) ⟨1053647, by rfl⟩ : syracuseStep 1404863 = 2107295) B2107295
theorem B2552633 : Blo 275825 2552633 := bstep (se 2 (by rfl) ⟨957237, by rfl⟩ : syracuseStep 2552633 = 1914475) B1914475
theorem B2358953 : Blo 275825 2358953 := bstep (se 2 (by rfl) ⟨884607, by rfl⟩ : syracuseStep 2358953 = 1769215) B1769215
theorem B622889 : Blo 275825 622889 := bstep (se 2 (by rfl) ⟨233583, by rfl⟩ : syracuseStep 622889 = 467167) B467167
theorem B623699 : Blo 275825 623699 := bstep (se 1 (by rfl) ⟨467774, by rfl⟩ : syracuseStep 623699 = 935549) B935549
theorem B15533693 : Blo 275825 15533693 := bstep (se 3 (by rfl) ⟨2912567, by rfl⟩ : syracuseStep 15533693 = 5825135) B5825135
theorem B758155 : Blo 275825 758155 := bstep (se 1 (by rfl) ⟨568616, by rfl⟩ : syracuseStep 758155 = 1137233) B1137233
theorem B1413935 : Blo 275825 1413935 := bstep (se 1 (by rfl) ⟨1060451, by rfl⟩ : syracuseStep 1413935 = 2120903) B2120903
theorem B628991 : Blo 275825 628991 := bstep (se 1 (by rfl) ⟨471743, by rfl⟩ : syracuseStep 628991 = 943487) B943487
theorem B6036839 : Blo 275825 6036839 := bstep (se 1 (by rfl) ⟨4527629, by rfl⟩ : syracuseStep 6036839 = 9055259) B9055259
theorem B699263 : Blo 275825 699263 := bstep (se 1 (by rfl) ⟨524447, by rfl⟩ : syracuseStep 699263 = 1048895) B1048895
theorem B470009 : Blo 275825 470009 := bstep (se 2 (by rfl) ⟨176253, by rfl⟩ : syracuseStep 470009 = 352507) B352507
theorem B896159 : Blo 275825 896159 := bstep (se 1 (by rfl) ⟨672119, by rfl⟩ : syracuseStep 896159 = 1344239) B1344239
theorem B601319 : Blo 275825 601319 := bstep (se 1 (by rfl) ⟨450989, by rfl⟩ : syracuseStep 601319 = 901979) B901979
theorem B1062335 : Blo 275825 1062335 := bstep (se 1 (by rfl) ⟨796751, by rfl⟩ : syracuseStep 1062335 = 1593503) B1593503
theorem B1194223 : Blo 275825 1194223 := bstep (se 1 (by rfl) ⟨895667, by rfl⟩ : syracuseStep 1194223 = 1791335) B1791335
theorem B276959 : Blo 275825 276959 := bstep (se 1 (by rfl) ⟨207719, by rfl⟩ : syracuseStep 276959 = 415439) B415439
theorem B277695 : Blo 275825 277695 := bstep (se 1 (by rfl) ⟨208271, by rfl⟩ : syracuseStep 277695 = 416543) B416543
theorem B803791 : Blo 275825 803791 := bstep (se 1 (by rfl) ⟨602843, by rfl⟩ : syracuseStep 803791 = 1205687) B1205687
theorem B279643 : Blo 275825 279643 := bstep (se 1 (by rfl) ⟨209732, by rfl⟩ : syracuseStep 279643 = 419465) B419465
theorem B935279 : Blo 275825 935279 := bstep (se 1 (by rfl) ⟨701459, by rfl⟩ : syracuseStep 935279 = 1402919) B1402919
theorem B936575 : Blo 275825 936575 := bstep (se 1 (by rfl) ⟨702431, by rfl⟩ : syracuseStep 936575 = 1404863) B1404863
theorem B936953 : Blo 275825 936953 := bstep (se 2 (by rfl) ⟨351357, by rfl⟩ : syracuseStep 936953 = 702715) B702715
theorem B937601 : Blo 275825 937601 := bstep (se 2 (by rfl) ⟨351600, by rfl⟩ : syracuseStep 937601 = 703201) B703201
theorem B2021267 : Blo 275825 2021267 := bstep (se 1 (by rfl) ⟨1515950, by rfl⟩ : syracuseStep 2021267 = 3031901) B3031901
theorem B415643 : Blo 275825 415643 := bstep (se 1 (by rfl) ⟨311732, by rfl⟩ : syracuseStep 415643 = 623465) B623465
theorem B3168233 : Blo 275825 3168233 := bstep (se 2 (by rfl) ⟨1188087, by rfl⟩ : syracuseStep 3168233 = 2376175) B2376175
theorem B415835 : Blo 275825 415835 := bstep (se 1 (by rfl) ⟨311876, by rfl⟩ : syracuseStep 415835 = 623753) B623753
theorem B5691545 : Blo 275825 5691545 := bstep (se 2 (by rfl) ⟨2134329, by rfl⟩ : syracuseStep 5691545 = 4268659) B4268659
theorem B11360735 : Blo 275825 11360735 := bstep (se 1 (by rfl) ⟨8520551, by rfl⟩ : syracuseStep 11360735 = 17041103) B17041103
theorem B1399679 : Blo 275825 1399679 := bstep (se 1 (by rfl) ⟨1049759, by rfl⟩ : syracuseStep 1399679 = 2099519) B2099519
theorem B416795 : Blo 275825 416795 := bstep (se 1 (by rfl) ⟨312596, by rfl⟩ : syracuseStep 416795 = 625193) B625193
theorem B941759 : Blo 275825 941759 := bstep (se 1 (by rfl) ⟨706319, by rfl⟩ : syracuseStep 941759 = 1412639) B1412639
theorem B418535 : Blo 275825 418535 := bstep (se 1 (by rfl) ⟨313901, by rfl⟩ : syracuseStep 418535 = 627803) B627803
theorem B10118141 : Blo 275825 10118141 := bstep (se 3 (by rfl) ⟨1897151, by rfl⟩ : syracuseStep 10118141 = 3794303) B3794303
theorem B418985 : Blo 275825 418985 := bstep (se 2 (by rfl) ⟨157119, by rfl⟩ : syracuseStep 418985 = 314239) B314239
theorem B419375 : Blo 275825 419375 := bstep (se 1 (by rfl) ⟨314531, by rfl⟩ : syracuseStep 419375 = 629063) B629063
theorem B3565903 : Blo 275825 3565903 := bstep (se 1 (by rfl) ⟨2674427, by rfl⟩ : syracuseStep 3565903 = 5348855) B5348855
theorem B750185 : Blo 275825 750185 := bstep (se 2 (by rfl) ⟨281319, by rfl⟩ : syracuseStep 750185 = 562639) B562639
theorem B1701755 : Blo 275825 1701755 := bstep (se 1 (by rfl) ⟨1276316, by rfl⟩ : syracuseStep 1701755 = 2552633) B2552633
theorem B1572635 : Blo 275825 1572635 := bstep (se 1 (by rfl) ⟨1179476, by rfl⟩ : syracuseStep 1572635 = 2358953) B2358953
theorem B623519 : Blo 275825 623519 := bstep (se 1 (by rfl) ⟨467639, by rfl⟩ : syracuseStep 623519 = 935279) B935279
theorem B10355795 : Blo 275825 10355795 := bstep (se 1 (by rfl) ⟨7766846, by rfl⟩ : syracuseStep 10355795 = 15533693) B15533693
theorem B624383 : Blo 275825 624383 := bstep (se 1 (by rfl) ⟨468287, by rfl⟩ : syracuseStep 624383 = 936575) B936575
theorem B624635 : Blo 275825 624635 := bstep (se 1 (by rfl) ⟨468476, by rfl⟩ : syracuseStep 624635 = 936953) B936953
theorem B625067 : Blo 275825 625067 := bstep (se 1 (by rfl) ⟨468800, by rfl⟩ : syracuseStep 625067 = 937601) B937601
theorem B4754537 : Blo 275825 4754537 := bstep (se 2 (by rfl) ⟨1782951, by rfl⟩ : syracuseStep 4754537 = 3565903) B3565903
theorem B1347511 : Blo 275825 1347511 := bstep (se 1 (by rfl) ⟨1010633, by rfl⟩ : syracuseStep 1347511 = 2021267) B2021267
theorem B7573823 : Blo 275825 7573823 := bstep (se 1 (by rfl) ⟨5680367, by rfl⟩ : syracuseStep 7573823 = 11360735) B11360735
theorem B627839 : Blo 275825 627839 := bstep (se 1 (by rfl) ⟨470879, by rfl⟩ : syracuseStep 627839 = 941759) B941759
theorem B466175 : Blo 275825 466175 := bstep (se 1 (by rfl) ⟨349631, by rfl⟩ : syracuseStep 466175 = 699263) B699263
theorem B597439 : Blo 275825 597439 := bstep (se 1 (by rfl) ⟨448079, by rfl⟩ : syracuseStep 597439 = 896159) B896159
theorem B400879 : Blo 275825 400879 := bstep (se 1 (by rfl) ⟨300659, by rfl⟩ : syracuseStep 400879 = 601319) B601319
theorem B500123 : Blo 275825 500123 := bstep (se 1 (by rfl) ⟨375092, by rfl⟩ : syracuseStep 500123 = 750185) B750185
theorem B277095 : Blo 275825 277095 := bstep (se 1 (by rfl) ⟨207821, by rfl⟩ : syracuseStep 277095 = 415643) B415643
theorem B2112155 : Blo 275825 2112155 := bstep (se 1 (by rfl) ⟨1584116, by rfl⟩ : syracuseStep 2112155 = 3168233) B3168233
theorem B277223 : Blo 275825 277223 := bstep (se 1 (by rfl) ⟨207917, by rfl⟩ : syracuseStep 277223 = 415835) B415835
theorem B933119 : Blo 275825 933119 := bstep (se 1 (by rfl) ⟨699839, by rfl⟩ : syracuseStep 933119 = 1399679) B1399679
theorem B277863 : Blo 275825 277863 := bstep (se 1 (by rfl) ⟨208397, by rfl⟩ : syracuseStep 277863 = 416795) B416795
theorem B279023 : Blo 275825 279023 := bstep (se 1 (by rfl) ⟨209267, by rfl⟩ : syracuseStep 279023 = 418535) B418535
theorem B279323 : Blo 275825 279323 := bstep (se 1 (by rfl) ⟨209492, by rfl⟩ : syracuseStep 279323 = 418985) B418985
theorem B279583 : Blo 275825 279583 := bstep (se 1 (by rfl) ⟨209687, by rfl⟩ : syracuseStep 279583 = 419375) B419375
theorem B313339 : Blo 275825 313339 := bstep (se 1 (by rfl) ⟨235004, by rfl⟩ : syracuseStep 313339 = 470009) B470009
theorem B1592297 : Blo 275825 1592297 := bstep (se 2 (by rfl) ⟨597111, by rfl⟩ : syracuseStep 1592297 = 1194223) B1194223
theorem B708223 : Blo 275825 708223 := bstep (se 1 (by rfl) ⟨531167, by rfl⟩ : syracuseStep 708223 = 1062335) B1062335
theorem B1134503 : Blo 275825 1134503 := bstep (se 1 (by rfl) ⟨850877, by rfl⟩ : syracuseStep 1134503 = 1701755) B1701755
theorem B415259 : Blo 275825 415259 := bstep (se 1 (by rfl) ⟨311444, by rfl⟩ : syracuseStep 415259 = 622889) B622889
theorem B415799 : Blo 275825 415799 := bstep (se 1 (by rfl) ⟨311849, by rfl⟩ : syracuseStep 415799 = 623699) B623699
theorem B1071721 : Blo 275825 1071721 := bstep (se 2 (by rfl) ⟨401895, by rfl⟩ : syracuseStep 1071721 = 803791) B803791
theorem B942623 : Blo 275825 942623 := bstep (se 1 (by rfl) ⟨706967, by rfl⟩ : syracuseStep 942623 = 1413935) B1413935
theorem B3794363 : Blo 275825 3794363 := bstep (se 1 (by rfl) ⟨2845772, by rfl⟩ : syracuseStep 3794363 = 5691545) B5691545
theorem B419327 : Blo 275825 419327 := bstep (se 1 (by rfl) ⟨314495, by rfl⟩ : syracuseStep 419327 = 628991) B628991
theorem B4024559 : Blo 275825 4024559 := bstep (se 1 (by rfl) ⟨3018419, by rfl⟩ : syracuseStep 4024559 = 6036839) B6036839
theorem B1010873 : Blo 275825 1010873 := bstep (se 2 (by rfl) ⟨379077, by rfl⟩ : syracuseStep 1010873 = 758155) B758155
theorem B6745427 : Blo 275825 6745427 := bstep (se 1 (by rfl) ⟨5059070, by rfl⟩ : syracuseStep 6745427 = 10118141) B10118141
theorem B1048423 : Blo 275825 1048423 := bstep (se 1 (by rfl) ⟨786317, by rfl⟩ : syracuseStep 1048423 = 1572635) B1572635
theorem B756335 : Blo 275825 756335 := bstep (se 1 (by rfl) ⟨567251, by rfl⟩ : syracuseStep 756335 = 1134503) B1134503
theorem B5049215 : Blo 275825 5049215 := bstep (se 1 (by rfl) ⟨3786911, by rfl⟩ : syracuseStep 5049215 = 7573823) B7573823
theorem B333415 : Blo 275825 333415 := bstep (se 1 (by rfl) ⟨250061, by rfl⟩ : syracuseStep 333415 = 500123) B500123
theorem B628415 : Blo 275825 628415 := bstep (se 1 (by rfl) ⟨471311, by rfl⟩ : syracuseStep 628415 = 942623) B942623
theorem B2529575 : Blo 275825 2529575 := bstep (se 1 (by rfl) ⟨1897181, by rfl⟩ : syracuseStep 2529575 = 3794363) B3794363
theorem B4496951 : Blo 275825 4496951 := bstep (se 1 (by rfl) ⟨3372713, by rfl⟩ : syracuseStep 4496951 = 6745427) B6745427
theorem B3186341 : Blo 275825 3186341 := bstep (se 4 (by rfl) ⟨298719, by rfl⟩ : syracuseStep 3186341 = 597439) B597439
theorem B2138021 : Blo 275825 2138021 := bstep (se 4 (by rfl) ⟨200439, by rfl⟩ : syracuseStep 2138021 = 400879) B400879
theorem B1061531 : Blo 275825 1061531 := bstep (se 1 (by rfl) ⟨796148, by rfl⟩ : syracuseStep 1061531 = 1592297) B1592297
theorem B276839 : Blo 275825 276839 := bstep (se 1 (by rfl) ⟨207629, by rfl⟩ : syracuseStep 276839 = 415259) B415259
theorem B277199 : Blo 275825 277199 := bstep (se 1 (by rfl) ⟨207899, by rfl⟩ : syracuseStep 277199 = 415799) B415799
theorem B310783 : Blo 275825 310783 := bstep (se 1 (by rfl) ⟨233087, by rfl⟩ : syracuseStep 310783 = 466175) B466175
theorem B279551 : Blo 275825 279551 := bstep (se 1 (by rfl) ⟨209663, by rfl⟩ : syracuseStep 279551 = 419327) B419327
theorem B673915 : Blo 275825 673915 := bstep (se 1 (by rfl) ⟨505436, by rfl⟩ : syracuseStep 673915 = 1010873) B1010873
theorem B1428961 : Blo 275825 1428961 := bstep (se 2 (by rfl) ⟨535860, by rfl⟩ : syracuseStep 1428961 = 1071721) B1071721
theorem B1397897 : Blo 275825 1397897 := bstep (se 2 (by rfl) ⟨524211, by rfl⟩ : syracuseStep 1397897 = 1048423) B1048423
theorem B415679 : Blo 275825 415679 := bstep (se 1 (by rfl) ⟨311759, by rfl⟩ : syracuseStep 415679 = 623519) B623519
theorem B6903863 : Blo 275825 6903863 := bstep (se 1 (by rfl) ⟨5177897, by rfl⟩ : syracuseStep 6903863 = 10355795) B10355795
theorem B416255 : Blo 275825 416255 := bstep (se 1 (by rfl) ⟨312191, by rfl⟩ : syracuseStep 416255 = 624383) B624383
theorem B416423 : Blo 275825 416423 := bstep (se 1 (by rfl) ⟨312317, by rfl⟩ : syracuseStep 416423 = 624635) B624635
theorem B416711 : Blo 275825 416711 := bstep (se 1 (by rfl) ⟨312533, by rfl⟩ : syracuseStep 416711 = 625067) B625067
theorem B3169691 : Blo 275825 3169691 := bstep (se 1 (by rfl) ⟨2377268, by rfl⟩ : syracuseStep 3169691 = 4754537) B4754537
theorem B417785 : Blo 275825 417785 := bstep (se 2 (by rfl) ⟨156669, by rfl⟩ : syracuseStep 417785 = 313339) B313339
theorem B418559 : Blo 275825 418559 := bstep (se 1 (by rfl) ⟨313919, by rfl⟩ : syracuseStep 418559 = 627839) B627839
theorem B944297 : Blo 275825 944297 := bstep (se 2 (by rfl) ⟨354111, by rfl⟩ : syracuseStep 944297 = 708223) B708223
theorem B1796681 : Blo 275825 1796681 := bstep (se 2 (by rfl) ⟨673755, by rfl⟩ : syracuseStep 1796681 = 1347511) B1347511
theorem B2683039 : Blo 275825 2683039 := bstep (se 1 (by rfl) ⟨2012279, by rfl⟩ : syracuseStep 2683039 = 4024559) B4024559
theorem B1408103 : Blo 275825 1408103 := bstep (se 1 (by rfl) ⟨1056077, by rfl⟩ : syracuseStep 1408103 = 2112155) B2112155
theorem B622079 : Blo 275825 622079 := bstep (se 1 (by rfl) ⟨466559, by rfl⟩ : syracuseStep 622079 = 933119) B933119
theorem B1905281 : Blo 275825 1905281 := bstep (se 2 (by rfl) ⟨714480, by rfl⟩ : syracuseStep 1905281 = 1428961) B1428961
theorem B3577385 : Blo 275825 3577385 := bstep (se 2 (by rfl) ⟨1341519, by rfl⟩ : syracuseStep 3577385 = 2683039) B2683039
theorem B629531 : Blo 275825 629531 := bstep (se 1 (by rfl) ⟨472148, by rfl⟩ : syracuseStep 629531 = 944297) B944297
theorem B1778213 : Blo 275825 1778213 := bstep (se 4 (by rfl) ⟨166707, by rfl⟩ : syracuseStep 1778213 = 333415) B333415
theorem B898553 : Blo 275825 898553 := bstep (se 2 (by rfl) ⟨336957, by rfl⟩ : syracuseStep 898553 = 673915) B673915
theorem B931931 : Blo 275825 931931 := bstep (se 1 (by rfl) ⟨698948, by rfl⟩ : syracuseStep 931931 = 1397897) B1397897
theorem B277119 : Blo 275825 277119 := bstep (se 1 (by rfl) ⟨207839, by rfl⟩ : syracuseStep 277119 = 415679) B415679
theorem B4602575 : Blo 275825 4602575 := bstep (se 1 (by rfl) ⟨3451931, by rfl⟩ : syracuseStep 4602575 = 6903863) B6903863
theorem B1686383 : Blo 275825 1686383 := bstep (se 1 (by rfl) ⟨1264787, by rfl⟩ : syracuseStep 1686383 = 2529575) B2529575
theorem B277503 : Blo 275825 277503 := bstep (se 1 (by rfl) ⟨208127, by rfl⟩ : syracuseStep 277503 = 416255) B416255
theorem B277615 : Blo 275825 277615 := bstep (se 1 (by rfl) ⟨208211, by rfl⟩ : syracuseStep 277615 = 416423) B416423
theorem B277807 : Blo 275825 277807 := bstep (se 1 (by rfl) ⟨208355, by rfl⟩ : syracuseStep 277807 = 416711) B416711
theorem B2113127 : Blo 275825 2113127 := bstep (se 1 (by rfl) ⟨1584845, by rfl⟩ : syracuseStep 2113127 = 3169691) B3169691
theorem B2997967 : Blo 275825 2997967 := bstep (se 1 (by rfl) ⟨2248475, by rfl⟩ : syracuseStep 2997967 = 4496951) B4496951
theorem B1425347 : Blo 275825 1425347 := bstep (se 1 (by rfl) ⟨1069010, by rfl⟩ : syracuseStep 1425347 = 2138021) B2138021
theorem B278523 : Blo 275825 278523 := bstep (se 1 (by rfl) ⟨208892, by rfl⟩ : syracuseStep 278523 = 417785) B417785
theorem B279039 : Blo 275825 279039 := bstep (se 1 (by rfl) ⟨209279, by rfl⟩ : syracuseStep 279039 = 418559) B418559
theorem B2016893 : Blo 275825 2016893 := bstep (se 3 (by rfl) ⟨378167, by rfl⟩ : syracuseStep 2016893 = 756335) B756335
theorem B1197787 : Blo 275825 1197787 := bstep (se 1 (by rfl) ⟨898340, by rfl⟩ : syracuseStep 1197787 = 1796681) B1796681
theorem B707687 : Blo 275825 707687 := bstep (se 1 (by rfl) ⟨530765, by rfl⟩ : syracuseStep 707687 = 1061531) B1061531
theorem B414377 : Blo 275825 414377 := bstep (se 2 (by rfl) ⟨155391, by rfl⟩ : syracuseStep 414377 = 310783) B310783
theorem B938735 : Blo 275825 938735 := bstep (se 1 (by rfl) ⟨704051, by rfl⟩ : syracuseStep 938735 = 1408103) B1408103
theorem B414719 : Blo 275825 414719 := bstep (se 1 (by rfl) ⟨311039, by rfl⟩ : syracuseStep 414719 = 622079) B622079
theorem B3366143 : Blo 275825 3366143 := bstep (se 1 (by rfl) ⟨2524607, by rfl⟩ : syracuseStep 3366143 = 5049215) B5049215
theorem B418943 : Blo 275825 418943 := bstep (se 1 (by rfl) ⟨314207, by rfl⟩ : syracuseStep 418943 = 628415) B628415
theorem B2124227 : Blo 275825 2124227 := bstep (se 1 (by rfl) ⟨1593170, by rfl⟩ : syracuseStep 2124227 = 3186341) B3186341
theorem B1344595 : Blo 275825 1344595 := bstep (se 1 (by rfl) ⟨1008446, by rfl⟩ : syracuseStep 1344595 = 2016893) B2016893
theorem B625823 : Blo 275825 625823 := bstep (se 1 (by rfl) ⟨469367, by rfl⟩ : syracuseStep 625823 = 938735) B938735
theorem B2396141 : Blo 275825 2396141 := bstep (se 3 (by rfl) ⟨449276, by rfl⟩ : syracuseStep 2396141 = 898553) B898553
theorem B1185475 : Blo 275825 1185475 := bstep (se 1 (by rfl) ⟨889106, by rfl⟩ : syracuseStep 1185475 = 1778213) B1778213
theorem B1416151 : Blo 275825 1416151 := bstep (se 1 (by rfl) ⟨1062113, by rfl⟩ : syracuseStep 1416151 = 2124227) B2124227
theorem B1124255 : Blo 275825 1124255 := bstep (se 1 (by rfl) ⟨843191, by rfl⟩ : syracuseStep 1124255 = 1686383) B1686383
theorem B471791 : Blo 275825 471791 := bstep (se 1 (by rfl) ⟨353843, by rfl⟩ : syracuseStep 471791 = 707687) B707687
theorem B276251 : Blo 275825 276251 := bstep (se 1 (by rfl) ⟨207188, by rfl⟩ : syracuseStep 276251 = 414377) B414377
theorem B276479 : Blo 275825 276479 := bstep (se 1 (by rfl) ⟨207359, by rfl⟩ : syracuseStep 276479 = 414719) B414719
theorem B2244095 : Blo 275825 2244095 := bstep (se 1 (by rfl) ⟨1683071, by rfl⟩ : syracuseStep 2244095 = 3366143) B3366143
theorem B279295 : Blo 275825 279295 := bstep (se 1 (by rfl) ⟨209471, by rfl⟩ : syracuseStep 279295 = 418943) B418943
theorem B3068383 : Blo 275825 3068383 := bstep (se 1 (by rfl) ⟨2301287, by rfl⟩ : syracuseStep 3068383 = 4602575) B4602575
theorem B1597049 : Blo 275825 1597049 := bstep (se 2 (by rfl) ⟨598893, by rfl⟩ : syracuseStep 1597049 = 1197787) B1197787
theorem B1270187 : Blo 275825 1270187 := bstep (se 1 (by rfl) ⟨952640, by rfl⟩ : syracuseStep 1270187 = 1905281) B1905281
theorem B2384923 : Blo 275825 2384923 := bstep (se 1 (by rfl) ⟨1788692, by rfl⟩ : syracuseStep 2384923 = 3577385) B3577385
theorem B419687 : Blo 275825 419687 := bstep (se 1 (by rfl) ⟨314765, by rfl⟩ : syracuseStep 419687 = 629531) B629531
theorem B621287 : Blo 275825 621287 := bstep (se 1 (by rfl) ⟨465965, by rfl⟩ : syracuseStep 621287 = 931931) B931931
theorem B3997289 : Blo 275825 3997289 := bstep (se 2 (by rfl) ⟨1498983, by rfl⟩ : syracuseStep 3997289 = 2997967) B2997967
theorem B1408751 : Blo 275825 1408751 := bstep (se 1 (by rfl) ⟨1056563, by rfl⟩ : syracuseStep 1408751 = 2113127) B2113127
theorem B950231 : Blo 275825 950231 := bstep (se 1 (by rfl) ⟨712673, by rfl⟩ : syracuseStep 950231 = 1425347) B1425347
theorem B3179897 : Blo 275825 3179897 := bstep (se 2 (by rfl) ⟨1192461, by rfl⟩ : syracuseStep 3179897 = 2384923) B2384923
theorem B1580633 : Blo 275825 1580633 := bstep (se 2 (by rfl) ⟨592737, by rfl⟩ : syracuseStep 1580633 = 1185475) B1185475
theorem B2664859 : Blo 275825 2664859 := bstep (se 1 (by rfl) ⟨1998644, by rfl⟩ : syracuseStep 2664859 = 3997289) B3997289
theorem B2533949 : Blo 275825 2533949 := bstep (se 3 (by rfl) ⟨475115, by rfl⟩ : syracuseStep 2533949 = 950231) B950231
theorem B1064699 : Blo 275825 1064699 := bstep (se 1 (by rfl) ⟨798524, by rfl⟩ : syracuseStep 1064699 = 1597049) B1597049
theorem B279791 : Blo 275825 279791 := bstep (se 1 (by rfl) ⟨209843, by rfl⟩ : syracuseStep 279791 = 419687) B419687
theorem B314527 : Blo 275825 314527 := bstep (se 1 (by rfl) ⟨235895, by rfl⟩ : syracuseStep 314527 = 471791) B471791
theorem B1888201 : Blo 275825 1888201 := bstep (se 2 (by rfl) ⟨708075, by rfl⟩ : syracuseStep 1888201 = 1416151) B1416151
theorem B414191 : Blo 275825 414191 := bstep (se 1 (by rfl) ⟨310643, by rfl⟩ : syracuseStep 414191 = 621287) B621287
theorem B1496063 : Blo 275825 1496063 := bstep (se 1 (by rfl) ⟨1122047, by rfl⟩ : syracuseStep 1496063 = 2244095) B2244095
theorem B939167 : Blo 275825 939167 := bstep (se 1 (by rfl) ⟨704375, by rfl⟩ : syracuseStep 939167 = 1408751) B1408751
theorem B1792793 : Blo 275825 1792793 := bstep (se 2 (by rfl) ⟨672297, by rfl⟩ : syracuseStep 1792793 = 1344595) B1344595
theorem B417215 : Blo 275825 417215 := bstep (se 1 (by rfl) ⟨312911, by rfl⟩ : syracuseStep 417215 = 625823) B625823
theorem B1597427 : Blo 275825 1597427 := bstep (se 1 (by rfl) ⟨1198070, by rfl⟩ : syracuseStep 1597427 = 2396141) B2396141
theorem B846791 : Blo 275825 846791 := bstep (se 1 (by rfl) ⟨635093, by rfl⟩ : syracuseStep 846791 = 1270187) B1270187
theorem B4091177 : Blo 275825 4091177 := bstep (se 2 (by rfl) ⟨1534191, by rfl⟩ : syracuseStep 4091177 = 3068383) B3068383
theorem B749503 : Blo 275825 749503 := bstep (se 1 (by rfl) ⟨562127, by rfl⟩ : syracuseStep 749503 = 1124255) B1124255
theorem B626111 : Blo 275825 626111 := bstep (se 1 (by rfl) ⟨469583, by rfl⟩ : syracuseStep 626111 = 939167) B939167
theorem B1053755 : Blo 275825 1053755 := bstep (se 1 (by rfl) ⟨790316, by rfl⟩ : syracuseStep 1053755 = 1580633) B1580633
theorem B564527 : Blo 275825 564527 := bstep (se 1 (by rfl) ⟨423395, by rfl⟩ : syracuseStep 564527 = 846791) B846791
theorem B2727451 : Blo 275825 2727451 := bstep (se 1 (by rfl) ⟨2045588, by rfl⟩ : syracuseStep 2727451 = 4091177) B4091177
theorem B276127 : Blo 275825 276127 := bstep (se 1 (by rfl) ⟨207095, by rfl⟩ : syracuseStep 276127 = 414191) B414191
theorem B3553145 : Blo 275825 3553145 := bstep (se 2 (by rfl) ⟨1332429, by rfl⟩ : syracuseStep 3553145 = 2664859) B2664859
theorem B997375 : Blo 275825 997375 := bstep (se 1 (by rfl) ⟨748031, by rfl⟩ : syracuseStep 997375 = 1496063) B1496063
theorem B278143 : Blo 275825 278143 := bstep (se 1 (by rfl) ⟨208607, by rfl⟩ : syracuseStep 278143 = 417215) B417215
theorem B999337 : Blo 275825 999337 := bstep (se 2 (by rfl) ⟨374751, by rfl⟩ : syracuseStep 999337 = 749503) B749503
theorem B1064951 : Blo 275825 1064951 := bstep (se 1 (by rfl) ⟨798713, by rfl⟩ : syracuseStep 1064951 = 1597427) B1597427
theorem B1689299 : Blo 275825 1689299 := bstep (se 1 (by rfl) ⟨1266974, by rfl⟩ : syracuseStep 1689299 = 2533949) B2533949
theorem B709799 : Blo 275825 709799 := bstep (se 1 (by rfl) ⟨532349, by rfl⟩ : syracuseStep 709799 = 1064699) B1064699
theorem B2119931 : Blo 275825 2119931 := bstep (se 1 (by rfl) ⟨1589948, by rfl⟩ : syracuseStep 2119931 = 3179897) B3179897
theorem B419369 : Blo 275825 419369 := bstep (se 2 (by rfl) ⟨157263, by rfl⟩ : syracuseStep 419369 = 314527) B314527
theorem B2517601 : Blo 275825 2517601 := bstep (se 2 (by rfl) ⟨944100, by rfl⟩ : syracuseStep 2517601 = 1888201) B1888201
theorem B4780781 : Blo 275825 4780781 := bstep (se 3 (by rfl) ⟨896396, by rfl⟩ : syracuseStep 4780781 = 1792793) B1792793
theorem B7571189 : Blo 275825 7571189 := bstep (se 5 (by rfl) ⟨354899, by rfl⟩ : syracuseStep 7571189 = 709799) B709799
theorem B1413287 : Blo 275825 1413287 := bstep (se 1 (by rfl) ⟨1059965, by rfl⟩ : syracuseStep 1413287 = 2119931) B2119931
theorem B3187187 : Blo 275825 3187187 := bstep (se 1 (by rfl) ⟨2390390, by rfl⟩ : syracuseStep 3187187 = 4780781) B4780781
theorem B2368763 : Blo 275825 2368763 := bstep (se 1 (by rfl) ⟨1776572, by rfl⟩ : syracuseStep 2368763 = 3553145) B3553145
theorem B1126199 : Blo 275825 1126199 := bstep (se 1 (by rfl) ⟨844649, by rfl⟩ : syracuseStep 1126199 = 1689299) B1689299
theorem B702503 : Blo 275825 702503 := bstep (se 1 (by rfl) ⟨526877, by rfl⟩ : syracuseStep 702503 = 1053755) B1053755
theorem B3356801 : Blo 275825 3356801 := bstep (se 2 (by rfl) ⟨1258800, by rfl⟩ : syracuseStep 3356801 = 2517601) B2517601
theorem B279579 : Blo 275825 279579 := bstep (se 1 (by rfl) ⟨209684, by rfl⟩ : syracuseStep 279579 = 419369) B419369
theorem B1329833 : Blo 275825 1329833 := bstep (se 2 (by rfl) ⟨498687, by rfl⟩ : syracuseStep 1329833 = 997375) B997375
theorem B1332449 : Blo 275825 1332449 := bstep (se 2 (by rfl) ⟨499668, by rfl⟩ : syracuseStep 1332449 = 999337) B999337
theorem B709967 : Blo 275825 709967 := bstep (se 1 (by rfl) ⟨532475, by rfl⟩ : syracuseStep 709967 = 1064951) B1064951
theorem B417407 : Blo 275825 417407 := bstep (se 1 (by rfl) ⟨313055, by rfl⟩ : syracuseStep 417407 = 626111) B626111
theorem B14546405 : Blo 275825 14546405 := bstep (se 4 (by rfl) ⟨1363725, by rfl⟩ : syracuseStep 14546405 = 2727451) B2727451
theorem B1505405 : Blo 275825 1505405 := bstep (se 3 (by rfl) ⟨282263, by rfl⟩ : syracuseStep 1505405 = 564527) B564527
theorem B886555 : Blo 275825 886555 := bstep (se 1 (by rfl) ⟨664916, by rfl⟩ : syracuseStep 886555 = 1329833) B1329833
theorem B888299 : Blo 275825 888299 := bstep (se 1 (by rfl) ⟨666224, by rfl⟩ : syracuseStep 888299 = 1332449) B1332449
theorem B20189837 : Blo 275825 20189837 := bstep (se 3 (by rfl) ⟨3785594, by rfl⟩ : syracuseStep 20189837 = 7571189) B7571189
theorem B1579175 : Blo 275825 1579175 := bstep (se 1 (by rfl) ⟨1184381, by rfl⟩ : syracuseStep 1579175 = 2368763) B2368763
theorem B468335 : Blo 275825 468335 := bstep (se 1 (by rfl) ⟨351251, by rfl⟩ : syracuseStep 468335 = 702503) B702503
theorem B2237867 : Blo 275825 2237867 := bstep (se 1 (by rfl) ⟨1678400, by rfl⟩ : syracuseStep 2237867 = 3356801) B3356801
theorem B473311 : Blo 275825 473311 := bstep (se 1 (by rfl) ⟨354983, by rfl⟩ : syracuseStep 473311 = 709967) B709967
theorem B278271 : Blo 275825 278271 := bstep (se 1 (by rfl) ⟨208703, by rfl⟩ : syracuseStep 278271 = 417407) B417407
theorem B1003603 : Blo 275825 1003603 := bstep (se 1 (by rfl) ⟨752702, by rfl⟩ : syracuseStep 1003603 = 1505405) B1505405
theorem B942191 : Blo 275825 942191 := bstep (se 1 (by rfl) ⟨706643, by rfl⟩ : syracuseStep 942191 = 1413287) B1413287
theorem B2124791 : Blo 275825 2124791 := bstep (se 1 (by rfl) ⟨1593593, by rfl⟩ : syracuseStep 2124791 = 3187187) B3187187
theorem B750799 : Blo 275825 750799 := bstep (se 1 (by rfl) ⟨563099, by rfl⟩ : syracuseStep 750799 = 1126199) B1126199
theorem B9697603 : Blo 275825 9697603 := bstep (se 1 (by rfl) ⟨7273202, by rfl⟩ : syracuseStep 9697603 = 14546405) B14546405
theorem B592199 : Blo 275825 592199 := bstep (se 1 (by rfl) ⟨444149, by rfl⟩ : syracuseStep 592199 = 888299) B888299
theorem B1052783 : Blo 275825 1052783 := bstep (se 1 (by rfl) ⟨789587, by rfl⟩ : syracuseStep 1052783 = 1579175) B1579175
theorem B628127 : Blo 275825 628127 := bstep (se 1 (by rfl) ⟨471095, by rfl⟩ : syracuseStep 628127 = 942191) B942191
theorem B4004261 : Blo 275825 4004261 := bstep (se 4 (by rfl) ⟨375399, by rfl⟩ : syracuseStep 4004261 = 750799) B750799
theorem B1416527 : Blo 275825 1416527 := bstep (se 1 (by rfl) ⟨1062395, by rfl⟩ : syracuseStep 1416527 = 2124791) B2124791
theorem B631081 : Blo 275825 631081 := bstep (se 2 (by rfl) ⟨236655, by rfl⟩ : syracuseStep 631081 = 473311) B473311
theorem B4728293 : Blo 275825 4728293 := bstep (se 4 (by rfl) ⟨443277, by rfl⟩ : syracuseStep 4728293 = 886555) B886555
theorem B312223 : Blo 275825 312223 := bstep (se 1 (by rfl) ⟨234167, by rfl⟩ : syracuseStep 312223 = 468335) B468335
theorem B1491911 : Blo 275825 1491911 := bstep (se 1 (by rfl) ⟨1118933, by rfl⟩ : syracuseStep 1491911 = 2237867) B2237867
theorem B12930137 : Blo 275825 12930137 := bstep (se 2 (by rfl) ⟨4848801, by rfl⟩ : syracuseStep 12930137 = 9697603) B9697603
theorem B13459891 : Blo 275825 13459891 := bstep (se 1 (by rfl) ⟨10094918, by rfl⟩ : syracuseStep 13459891 = 20189837) B20189837
theorem B1338137 : Blo 275825 1338137 := bstep (se 2 (by rfl) ⟨501801, by rfl⟩ : syracuseStep 1338137 = 1003603) B1003603
theorem B394799 : Blo 275825 394799 := bstep (se 1 (by rfl) ⟨296099, by rfl⟩ : syracuseStep 394799 = 592199) B592199
theorem B8620091 : Blo 275825 8620091 := bstep (se 1 (by rfl) ⟨6465068, by rfl⟩ : syracuseStep 8620091 = 12930137) B12930137
theorem B3152195 : Blo 275825 3152195 := bstep (se 1 (by rfl) ⟨2364146, by rfl⟩ : syracuseStep 3152195 = 4728293) B4728293
theorem B892091 : Blo 275825 892091 := bstep (se 1 (by rfl) ⟨669068, by rfl⟩ : syracuseStep 892091 = 1338137) B1338137
theorem B994607 : Blo 275825 994607 := bstep (se 1 (by rfl) ⟨745955, by rfl⟩ : syracuseStep 994607 = 1491911) B1491911
theorem B701855 : Blo 275825 701855 := bstep (se 1 (by rfl) ⟨526391, by rfl⟩ : syracuseStep 701855 = 1052783) B1052783
theorem B2669507 : Blo 275825 2669507 := bstep (se 1 (by rfl) ⟨2002130, by rfl⟩ : syracuseStep 2669507 = 4004261) B4004261
theorem B841441 : Blo 275825 841441 := bstep (se 2 (by rfl) ⟨315540, by rfl⟩ : syracuseStep 841441 = 631081) B631081
theorem B17946521 : Blo 275825 17946521 := bstep (se 2 (by rfl) ⟨6729945, by rfl⟩ : syracuseStep 17946521 = 13459891) B13459891
theorem B416297 : Blo 275825 416297 := bstep (se 2 (by rfl) ⟨156111, by rfl⟩ : syracuseStep 416297 = 312223) B312223
theorem B418751 : Blo 275825 418751 := bstep (se 1 (by rfl) ⟨314063, by rfl⟩ : syracuseStep 418751 = 628127) B628127
theorem B944351 : Blo 275825 944351 := bstep (se 1 (by rfl) ⟨708263, by rfl⟩ : syracuseStep 944351 = 1416527) B1416527
theorem B11964347 : Blo 275825 11964347 := bstep (se 1 (by rfl) ⟨8973260, by rfl⟩ : syracuseStep 11964347 = 17946521) B17946521
theorem B1052797 : Blo 275825 1052797 := bstep (se 3 (by rfl) ⟨197399, by rfl⟩ : syracuseStep 1052797 = 394799) B394799
theorem B2101463 : Blo 275825 2101463 := bstep (se 1 (by rfl) ⟨1576097, by rfl⟩ : syracuseStep 2101463 = 3152195) B3152195
theorem B629567 : Blo 275825 629567 := bstep (se 1 (by rfl) ⟨472175, by rfl⟩ : syracuseStep 629567 = 944351) B944351
theorem B663071 : Blo 275825 663071 := bstep (se 1 (by rfl) ⟨497303, by rfl⟩ : syracuseStep 663071 = 994607) B994607
theorem B1121921 : Blo 275825 1121921 := bstep (se 2 (by rfl) ⟨420720, by rfl⟩ : syracuseStep 1121921 = 841441) B841441
theorem B467903 : Blo 275825 467903 := bstep (se 1 (by rfl) ⟨350927, by rfl⟩ : syracuseStep 467903 = 701855) B701855
theorem B1779671 : Blo 275825 1779671 := bstep (se 1 (by rfl) ⟨1334753, by rfl⟩ : syracuseStep 1779671 = 2669507) B2669507
theorem B5746727 : Blo 275825 5746727 := bstep (se 1 (by rfl) ⟨4310045, by rfl⟩ : syracuseStep 5746727 = 8620091) B8620091
theorem B277531 : Blo 275825 277531 := bstep (se 1 (by rfl) ⟨208148, by rfl⟩ : syracuseStep 277531 = 416297) B416297
theorem B279167 : Blo 275825 279167 := bstep (se 1 (by rfl) ⟨209375, by rfl⟩ : syracuseStep 279167 = 418751) B418751
theorem B2378909 : Blo 275825 2378909 := bstep (se 3 (by rfl) ⟨446045, by rfl⟩ : syracuseStep 2378909 = 892091) B892091
theorem B1585939 : Blo 275825 1585939 := bstep (se 1 (by rfl) ⟨1189454, by rfl⟩ : syracuseStep 1585939 = 2378909) B2378909
theorem B7976231 : Blo 275825 7976231 := bstep (se 1 (by rfl) ⟨5982173, by rfl⟩ : syracuseStep 7976231 = 11964347) B11964347
theorem B311935 : Blo 275825 311935 := bstep (se 1 (by rfl) ⟨233951, by rfl⟩ : syracuseStep 311935 = 467903) B467903
theorem B1400975 : Blo 275825 1400975 := bstep (se 1 (by rfl) ⟨1050731, by rfl⟩ : syracuseStep 1400975 = 2101463) B2101463
theorem B419711 : Blo 275825 419711 := bstep (se 1 (by rfl) ⟨314783, by rfl⟩ : syracuseStep 419711 = 629567) B629567
theorem B747947 : Blo 275825 747947 := bstep (se 1 (by rfl) ⟨560960, by rfl⟩ : syracuseStep 747947 = 1121921) B1121921
theorem B4745789 : Blo 275825 4745789 := bstep (se 3 (by rfl) ⟨889835, by rfl⟩ : syracuseStep 4745789 = 1779671) B1779671
theorem B1403729 : Blo 275825 1403729 := bstep (se 2 (by rfl) ⟨526398, by rfl⟩ : syracuseStep 1403729 = 1052797) B1052797
theorem B7072757 : Blo 275825 7072757 := bstep (se 5 (by rfl) ⟨331535, by rfl⟩ : syracuseStep 7072757 = 663071) B663071
theorem B3831151 : Blo 275825 3831151 := bstep (se 1 (by rfl) ⟨2873363, by rfl⟩ : syracuseStep 3831151 = 5746727) B5746727
theorem B498631 : Blo 275825 498631 := bstep (se 1 (by rfl) ⟨373973, by rfl⟩ : syracuseStep 498631 = 747947) B747947
theorem B5317487 : Blo 275825 5317487 := bstep (se 1 (by rfl) ⟨3988115, by rfl⟩ : syracuseStep 5317487 = 7976231) B7976231
theorem B933983 : Blo 275825 933983 := bstep (se 1 (by rfl) ⟨700487, by rfl⟩ : syracuseStep 933983 = 1400975) B1400975
theorem B2114585 : Blo 275825 2114585 := bstep (se 2 (by rfl) ⟨792969, by rfl⟩ : syracuseStep 2114585 = 1585939) B1585939
theorem B279807 : Blo 275825 279807 := bstep (se 1 (by rfl) ⟨209855, by rfl⟩ : syracuseStep 279807 = 419711) B419711
theorem B3163859 : Blo 275825 3163859 := bstep (se 1 (by rfl) ⟨2372894, by rfl⟩ : syracuseStep 3163859 = 4745789) B4745789
theorem B935819 : Blo 275825 935819 := bstep (se 1 (by rfl) ⟨701864, by rfl⟩ : syracuseStep 935819 = 1403729) B1403729
theorem B415913 : Blo 275825 415913 := bstep (se 2 (by rfl) ⟨155967, by rfl⟩ : syracuseStep 415913 = 311935) B311935
theorem B5108201 : Blo 275825 5108201 := bstep (se 2 (by rfl) ⟨1915575, by rfl⟩ : syracuseStep 5108201 = 3831151) B3831151
theorem B4715171 : Blo 275825 4715171 := bstep (se 1 (by rfl) ⟨3536378, by rfl⟩ : syracuseStep 4715171 = 7072757) B7072757
theorem B622655 : Blo 275825 622655 := bstep (se 1 (by rfl) ⟨466991, by rfl⟩ : syracuseStep 622655 = 933983) B933983
theorem B1409723 : Blo 275825 1409723 := bstep (se 1 (by rfl) ⟨1057292, by rfl⟩ : syracuseStep 1409723 = 2114585) B2114585
theorem B623879 : Blo 275825 623879 := bstep (se 1 (by rfl) ⟨467909, by rfl⟩ : syracuseStep 623879 = 935819) B935819
theorem B3544991 : Blo 275825 3544991 := bstep (se 1 (by rfl) ⟨2658743, by rfl⟩ : syracuseStep 3544991 = 5317487) B5317487
theorem B664841 : Blo 275825 664841 := bstep (se 2 (by rfl) ⟨249315, by rfl⟩ : syracuseStep 664841 = 498631) B498631
theorem B2109239 : Blo 275825 2109239 := bstep (se 1 (by rfl) ⟨1581929, by rfl⟩ : syracuseStep 2109239 = 3163859) B3163859
theorem B277275 : Blo 275825 277275 := bstep (se 1 (by rfl) ⟨207956, by rfl⟩ : syracuseStep 277275 = 415913) B415913
theorem B3405467 : Blo 275825 3405467 := bstep (se 1 (by rfl) ⟨2554100, by rfl⟩ : syracuseStep 3405467 = 5108201) B5108201
theorem B3143447 : Blo 275825 3143447 := bstep (se 1 (by rfl) ⟨2357585, by rfl⟩ : syracuseStep 3143447 = 4715171) B4715171
theorem B2363327 : Blo 275825 2363327 := bstep (se 1 (by rfl) ⟨1772495, by rfl⟩ : syracuseStep 2363327 = 3544991) B3544991
theorem B2270311 : Blo 275825 2270311 := bstep (se 1 (by rfl) ⟨1702733, by rfl⟩ : syracuseStep 2270311 = 3405467) B3405467
theorem B443227 : Blo 275825 443227 := bstep (se 1 (by rfl) ⟨332420, by rfl⟩ : syracuseStep 443227 = 664841) B664841
theorem B415103 : Blo 275825 415103 := bstep (se 1 (by rfl) ⟨311327, by rfl⟩ : syracuseStep 415103 = 622655) B622655
theorem B939815 : Blo 275825 939815 := bstep (se 1 (by rfl) ⟨704861, by rfl⟩ : syracuseStep 939815 = 1409723) B1409723
theorem B415919 : Blo 275825 415919 := bstep (se 1 (by rfl) ⟨311939, by rfl⟩ : syracuseStep 415919 = 623879) B623879
theorem B1406159 : Blo 275825 1406159 := bstep (se 1 (by rfl) ⟨1054619, by rfl⟩ : syracuseStep 1406159 = 2109239) B2109239
theorem B2095631 : Blo 275825 2095631 := bstep (se 1 (by rfl) ⟨1571723, by rfl⟩ : syracuseStep 2095631 = 3143447) B3143447
theorem B590969 : Blo 275825 590969 := bstep (se 2 (by rfl) ⟨221613, by rfl⟩ : syracuseStep 590969 = 443227) B443227
theorem B1575551 : Blo 275825 1575551 := bstep (se 1 (by rfl) ⟨1181663, by rfl⟩ : syracuseStep 1575551 = 2363327) B2363327
theorem B626543 : Blo 275825 626543 := bstep (se 1 (by rfl) ⟨469907, by rfl⟩ : syracuseStep 626543 = 939815) B939815
theorem B276735 : Blo 275825 276735 := bstep (se 1 (by rfl) ⟨207551, by rfl⟩ : syracuseStep 276735 = 415103) B415103
theorem B277279 : Blo 275825 277279 := bstep (se 1 (by rfl) ⟨207959, by rfl⟩ : syracuseStep 277279 = 415919) B415919
theorem B12108325 : Blo 275825 12108325 := bstep (se 4 (by rfl) ⟨1135155, by rfl⟩ : syracuseStep 12108325 = 2270311) B2270311
theorem B937439 : Blo 275825 937439 := bstep (se 1 (by rfl) ⟨703079, by rfl⟩ : syracuseStep 937439 = 1406159) B1406159
theorem B1397087 : Blo 275825 1397087 := bstep (se 1 (by rfl) ⟨1047815, by rfl⟩ : syracuseStep 1397087 = 2095631) B2095631
theorem B393979 : Blo 275825 393979 := bstep (se 1 (by rfl) ⟨295484, by rfl⟩ : syracuseStep 393979 = 590969) B590969
theorem B1050367 : Blo 275825 1050367 := bstep (se 1 (by rfl) ⟨787775, by rfl⟩ : syracuseStep 1050367 = 1575551) B1575551
theorem B624959 : Blo 275825 624959 := bstep (se 1 (by rfl) ⟨468719, by rfl⟩ : syracuseStep 624959 = 937439) B937439
theorem B931391 : Blo 275825 931391 := bstep (se 1 (by rfl) ⟨698543, by rfl⟩ : syracuseStep 931391 = 1397087) B1397087
theorem B16144433 : Blo 275825 16144433 := bstep (se 2 (by rfl) ⟨6054162, by rfl⟩ : syracuseStep 16144433 = 12108325) B12108325
theorem B417695 : Blo 275825 417695 := bstep (se 1 (by rfl) ⟨313271, by rfl⟩ : syracuseStep 417695 = 626543) B626543
theorem B525305 : Blo 275825 525305 := bstep (se 2 (by rfl) ⟨196989, by rfl⟩ : syracuseStep 525305 = 393979) B393979
theorem B10762955 : Blo 275825 10762955 := bstep (se 1 (by rfl) ⟨8072216, by rfl⟩ : syracuseStep 10762955 = 16144433) B16144433
theorem B278463 : Blo 275825 278463 := bstep (se 1 (by rfl) ⟨208847, by rfl⟩ : syracuseStep 278463 = 417695) B417695
theorem B416639 : Blo 275825 416639 := bstep (se 1 (by rfl) ⟨312479, by rfl⟩ : syracuseStep 416639 = 624959) B624959
theorem B1400489 : Blo 275825 1400489 := bstep (se 2 (by rfl) ⟨525183, by rfl⟩ : syracuseStep 1400489 = 1050367) B1050367
theorem B620927 : Blo 275825 620927 := bstep (se 1 (by rfl) ⟨465695, by rfl⟩ : syracuseStep 620927 = 931391) B931391
theorem B277759 : Blo 275825 277759 := bstep (se 1 (by rfl) ⟨208319, by rfl⟩ : syracuseStep 277759 = 416639) B416639
theorem B933659 : Blo 275825 933659 := bstep (se 1 (by rfl) ⟨700244, by rfl⟩ : syracuseStep 933659 = 1400489) B1400489
theorem B413951 : Blo 275825 413951 := bstep (se 1 (by rfl) ⟨310463, by rfl⟩ : syracuseStep 413951 = 620927) B620927
theorem B1400813 : Blo 275825 1400813 := bstep (se 3 (by rfl) ⟨262652, by rfl⟩ : syracuseStep 1400813 = 525305) B525305
theorem B7175303 : Blo 275825 7175303 := bstep (se 1 (by rfl) ⟨5381477, by rfl⟩ : syracuseStep 7175303 = 10762955) B10762955
theorem B275967 : Blo 275825 275967 := bstep (se 1 (by rfl) ⟨206975, by rfl⟩ : syracuseStep 275967 = 413951) B413951
theorem B933875 : Blo 275825 933875 := bstep (se 1 (by rfl) ⟨700406, by rfl⟩ : syracuseStep 933875 = 1400813) B1400813
theorem B4783535 : Blo 275825 4783535 := bstep (se 1 (by rfl) ⟨3587651, by rfl⟩ : syracuseStep 4783535 = 7175303) B7175303
theorem B622439 : Blo 275825 622439 := bstep (se 1 (by rfl) ⟨466829, by rfl⟩ : syracuseStep 622439 = 933659) B933659
theorem B3189023 : Blo 275825 3189023 := bstep (se 1 (by rfl) ⟨2391767, by rfl⟩ : syracuseStep 3189023 = 4783535) B4783535
theorem B414959 : Blo 275825 414959 := bstep (se 1 (by rfl) ⟨311219, by rfl⟩ : syracuseStep 414959 = 622439) B622439
theorem B622583 : Blo 275825 622583 := bstep (se 1 (by rfl) ⟨466937, by rfl⟩ : syracuseStep 622583 = 933875) B933875
theorem B276639 : Blo 275825 276639 := bstep (se 1 (by rfl) ⟨207479, by rfl⟩ : syracuseStep 276639 = 414959) B414959
theorem B415055 : Blo 275825 415055 := bstep (se 1 (by rfl) ⟨311291, by rfl⟩ : syracuseStep 415055 = 622583) B622583
theorem B2126015 : Blo 275825 2126015 := bstep (se 1 (by rfl) ⟨1594511, by rfl⟩ : syracuseStep 2126015 = 3189023) B3189023
theorem B1417343 : Blo 275825 1417343 := bstep (se 1 (by rfl) ⟨1063007, by rfl⟩ : syracuseStep 1417343 = 2126015) B2126015
theorem B276703 : Blo 275825 276703 := bstep (se 1 (by rfl) ⟨207527, by rfl⟩ : syracuseStep 276703 = 415055) B415055
theorem B3779581 : Blo 275825 3779581 := bstep (se 3 (by rfl) ⟨708671, by rfl⟩ : syracuseStep 3779581 = 1417343) B1417343
theorem B5039441 : Blo 275825 5039441 := bstep (se 2 (by rfl) ⟨1889790, by rfl⟩ : syracuseStep 5039441 = 3779581) B3779581
theorem B3359627 : Blo 275825 3359627 := bstep (se 1 (by rfl) ⟨2519720, by rfl⟩ : syracuseStep 3359627 = 5039441) B5039441
theorem B2239751 : Blo 275825 2239751 := bstep (se 1 (by rfl) ⟨1679813, by rfl⟩ : syracuseStep 2239751 = 3359627) B3359627
theorem B1493167 : Blo 275825 1493167 := bstep (se 1 (by rfl) ⟨1119875, by rfl⟩ : syracuseStep 1493167 = 2239751) B2239751
theorem B1990889 : Blo 275825 1990889 := bstep (se 2 (by rfl) ⟨746583, by rfl⟩ : syracuseStep 1990889 = 1493167) B1493167
theorem B1327259 : Blo 275825 1327259 := bstep (se 1 (by rfl) ⟨995444, by rfl⟩ : syracuseStep 1327259 = 1990889) B1990889
theorem B884839 : Blo 275825 884839 := bstep (se 1 (by rfl) ⟨663629, by rfl⟩ : syracuseStep 884839 = 1327259) B1327259
theorem B1179785 : Blo 275825 1179785 := bstep (se 2 (by rfl) ⟨442419, by rfl⟩ : syracuseStep 1179785 = 884839) B884839
theorem B786523 : Blo 275825 786523 := bstep (se 1 (by rfl) ⟨589892, by rfl⟩ : syracuseStep 786523 = 1179785) B1179785
theorem B1048697 : Blo 275825 1048697 := bstep (se 2 (by rfl) ⟨393261, by rfl⟩ : syracuseStep 1048697 = 786523) B786523
theorem B699131 : Blo 275825 699131 := bstep (se 1 (by rfl) ⟨524348, by rfl⟩ : syracuseStep 699131 = 1048697) B1048697
theorem B466087 : Blo 275825 466087 := bstep (se 1 (by rfl) ⟨349565, by rfl⟩ : syracuseStep 466087 = 699131) B699131
theorem B621449 : Blo 275825 621449 := bstep (se 2 (by rfl) ⟨233043, by rfl⟩ : syracuseStep 621449 = 466087) B466087
theorem B414299 : Blo 275825 414299 := bstep (se 1 (by rfl) ⟨310724, by rfl⟩ : syracuseStep 414299 = 621449) B621449
theorem B276199 : Blo 275825 276199 := bstep (se 1 (by rfl) ⟨207149, by rfl⟩ : syracuseStep 276199 = 414299) B414299

theorem C0 (j : ℕ) (h1 : 68956 ≤ j) (h2 : j ≤ 69655) : Blo 275825 (4 * j + 3) := by
  interval_cases j
  · exact B275827
  · exact B275831
  · exact B275835
  · exact B275839
  · exact B275843
  · exact B275847
  · exact B275851
  · exact B275855
  · exact B275859
  · exact B275863
  · exact B275867
  · exact B275871
  · exact B275875
  · exact B275879
  · exact B275883
  · exact B275887
  · exact B275891
  · exact B275895
  · exact B275899
  · exact B275903
  · exact B275907
  · exact B275911
  · exact B275915
  · exact B275919
  · exact B275923
  · exact B275927
  · exact B275931
  · exact B275935
  · exact B275939
  · exact B275943
  · exact B275947
  · exact B275951
  · exact B275955
  · exact B275959
  · exact B275963
  · exact B275967
  · exact B275971
  · exact B275975
  · exact B275979
  · exact B275983
  · exact B275987
  · exact B275991
  · exact B275995
  · exact B275999
  · exact B276003
  · exact B276007
  · exact B276011
  · exact B276015
  · exact B276019
  · exact B276023
  · exact B276027
  · exact B276031
  · exact B276035
  · exact B276039
  · exact B276043
  · exact B276047
  · exact B276051
  · exact B276055
  · exact B276059
  · exact B276063
  · exact B276067
  · exact B276071
  · exact B276075
  · exact B276079
  · exact B276083
  · exact B276087
  · exact B276091
  · exact B276095
  · exact B276099
  · exact B276103
  · exact B276107
  · exact B276111
  · exact B276115
  · exact B276119
  · exact B276123
  · exact B276127
  · exact B276131
  · exact B276135
  · exact B276139
  · exact B276143
  · exact B276147
  · exact B276151
  · exact B276155
  · exact B276159
  · exact B276163
  · exact B276167
  · exact B276171
  · exact B276175
  · exact B276179
  · exact B276183
  · exact B276187
  · exact B276191
  · exact B276195
  · exact B276199
  · exact B276203
  · exact B276207
  · exact B276211
  · exact B276215
  · exact B276219
  · exact B276223
  · exact B276227
  · exact B276231
  · exact B276235
  · exact B276239
  · exact B276243
  · exact B276247
  · exact B276251
  · exact B276255
  · exact B276259
  · exact B276263
  · exact B276267
  · exact B276271
  · exact B276275
  · exact B276279
  · exact B276283
  · exact B276287
  · exact B276291
  · exact B276295
  · exact B276299
  · exact B276303
  · exact B276307
  · exact B276311
  · exact B276315
  · exact B276319
  · exact B276323
  · exact B276327
  · exact B276331
  · exact B276335
  · exact B276339
  · exact B276343
  · exact B276347
  · exact B276351
  · exact B276355
  · exact B276359
  · exact B276363
  · exact B276367
  · exact B276371
  · exact B276375
  · exact B276379
  · exact B276383
  · exact B276387
  · exact B276391
  · exact B276395
  · exact B276399
  · exact B276403
  · exact B276407
  · exact B276411
  · exact B276415
  · exact B276419
  · exact B276423
  · exact B276427
  · exact B276431
  · exact B276435
  · exact B276439
  · exact B276443
  · exact B276447
  · exact B276451
  · exact B276455
  · exact B276459
  · exact B276463
  · exact B276467
  · exact B276471
  · exact B276475
  · exact B276479
  · exact B276483
  · exact B276487
  · exact B276491
  · exact B276495
  · exact B276499
  · exact B276503
  · exact B276507
  · exact B276511
  · exact B276515
  · exact B276519
  · exact B276523
  · exact B276527
  · exact B276531
  · exact B276535
  · exact B276539
  · exact B276543
  · exact B276547
  · exact B276551
  · exact B276555
  · exact B276559
  · exact B276563
  · exact B276567
  · exact B276571
  · exact B276575
  · exact B276579
  · exact B276583
  · exact B276587
  · exact B276591
  · exact B276595
  · exact B276599
  · exact B276603
  · exact B276607
  · exact B276611
  · exact B276615
  · exact B276619
  · exact B276623
  · exact B276627
  · exact B276631
  · exact B276635
  · exact B276639
  · exact B276643
  · exact B276647
  · exact B276651
  · exact B276655
  · exact B276659
  · exact B276663
  · exact B276667
  · exact B276671
  · exact B276675
  · exact B276679
  · exact B276683
  · exact B276687
  · exact B276691
  · exact B276695
  · exact B276699
  · exact B276703
  · exact B276707
  · exact B276711
  · exact B276715
  · exact B276719
  · exact B276723
  · exact B276727
  · exact B276731
  · exact B276735
  · exact B276739
  · exact B276743
  · exact B276747
  · exact B276751
  · exact B276755
  · exact B276759
  · exact B276763
  · exact B276767
  · exact B276771
  · exact B276775
  · exact B276779
  · exact B276783
  · exact B276787
  · exact B276791
  · exact B276795
  · exact B276799
  · exact B276803
  · exact B276807
  · exact B276811
  · exact B276815
  · exact B276819
  · exact B276823
  · exact B276827
  · exact B276831
  · exact B276835
  · exact B276839
  · exact B276843
  · exact B276847
  · exact B276851
  · exact B276855
  · exact B276859
  · exact B276863
  · exact B276867
  · exact B276871
  · exact B276875
  · exact B276879
  · exact B276883
  · exact B276887
  · exact B276891
  · exact B276895
  · exact B276899
  · exact B276903
  · exact B276907
  · exact B276911
  · exact B276915
  · exact B276919
  · exact B276923
  · exact B276927
  · exact B276931
  · exact B276935
  · exact B276939
  · exact B276943
  · exact B276947
  · exact B276951
  · exact B276955
  · exact B276959
  · exact B276963
  · exact B276967
  · exact B276971
  · exact B276975
  · exact B276979
  · exact B276983
  · exact B276987
  · exact B276991
  · exact B276995
  · exact B276999
  · exact B277003
  · exact B277007
  · exact B277011
  · exact B277015
  · exact B277019
  · exact B277023
  · exact B277027
  · exact B277031
  · exact B277035
  · exact B277039
  · exact B277043
  · exact B277047
  · exact B277051
  · exact B277055
  · exact B277059
  · exact B277063
  · exact B277067
  · exact B277071
  · exact B277075
  · exact B277079
  · exact B277083
  · exact B277087
  · exact B277091
  · exact B277095
  · exact B277099
  · exact B277103
  · exact B277107
  · exact B277111
  · exact B277115
  · exact B277119
  · exact B277123
  · exact B277127
  · exact B277131
  · exact B277135
  · exact B277139
  · exact B277143
  · exact B277147
  · exact B277151
  · exact B277155
  · exact B277159
  · exact B277163
  · exact B277167
  · exact B277171
  · exact B277175
  · exact B277179
  · exact B277183
  · exact B277187
  · exact B277191
  · exact B277195
  · exact B277199
  · exact B277203
  · exact B277207
  · exact B277211
  · exact B277215
  · exact B277219
  · exact B277223
  · exact B277227
  · exact B277231
  · exact B277235
  · exact B277239
  · exact B277243
  · exact B277247
  · exact B277251
  · exact B277255
  · exact B277259
  · exact B277263
  · exact B277267
  · exact B277271
  · exact B277275
  · exact B277279
  · exact B277283
  · exact B277287
  · exact B277291
  · exact B277295
  · exact B277299
  · exact B277303
  · exact B277307
  · exact B277311
  · exact B277315
  · exact B277319
  · exact B277323
  · exact B277327
  · exact B277331
  · exact B277335
  · exact B277339
  · exact B277343
  · exact B277347
  · exact B277351
  · exact B277355
  · exact B277359
  · exact B277363
  · exact B277367
  · exact B277371
  · exact B277375
  · exact B277379
  · exact B277383
  · exact B277387
  · exact B277391
  · exact B277395
  · exact B277399
  · exact B277403
  · exact B277407
  · exact B277411
  · exact B277415
  · exact B277419
  · exact B277423
  · exact B277427
  · exact B277431
  · exact B277435
  · exact B277439
  · exact B277443
  · exact B277447
  · exact B277451
  · exact B277455
  · exact B277459
  · exact B277463
  · exact B277467
  · exact B277471
  · exact B277475
  · exact B277479
  · exact B277483
  · exact B277487
  · exact B277491
  · exact B277495
  · exact B277499
  · exact B277503
  · exact B277507
  · exact B277511
  · exact B277515
  · exact B277519
  · exact B277523
  · exact B277527
  · exact B277531
  · exact B277535
  · exact B277539
  · exact B277543
  · exact B277547
  · exact B277551
  · exact B277555
  · exact B277559
  · exact B277563
  · exact B277567
  · exact B277571
  · exact B277575
  · exact B277579
  · exact B277583
  · exact B277587
  · exact B277591
  · exact B277595
  · exact B277599
  · exact B277603
  · exact B277607
  · exact B277611
  · exact B277615
  · exact B277619
  · exact B277623
  · exact B277627
  · exact B277631
  · exact B277635
  · exact B277639
  · exact B277643
  · exact B277647
  · exact B277651
  · exact B277655
  · exact B277659
  · exact B277663
  · exact B277667
  · exact B277671
  · exact B277675
  · exact B277679
  · exact B277683
  · exact B277687
  · exact B277691
  · exact B277695
  · exact B277699
  · exact B277703
  · exact B277707
  · exact B277711
  · exact B277715
  · exact B277719
  · exact B277723
  · exact B277727
  · exact B277731
  · exact B277735
  · exact B277739
  · exact B277743
  · exact B277747
  · exact B277751
  · exact B277755
  · exact B277759
  · exact B277763
  · exact B277767
  · exact B277771
  · exact B277775
  · exact B277779
  · exact B277783
  · exact B277787
  · exact B277791
  · exact B277795
  · exact B277799
  · exact B277803
  · exact B277807
  · exact B277811
  · exact B277815
  · exact B277819
  · exact B277823
  · exact B277827
  · exact B277831
  · exact B277835
  · exact B277839
  · exact B277843
  · exact B277847
  · exact B277851
  · exact B277855
  · exact B277859
  · exact B277863
  · exact B277867
  · exact B277871
  · exact B277875
  · exact B277879
  · exact B277883
  · exact B277887
  · exact B277891
  · exact B277895
  · exact B277899
  · exact B277903
  · exact B277907
  · exact B277911
  · exact B277915
  · exact B277919
  · exact B277923
  · exact B277927
  · exact B277931
  · exact B277935
  · exact B277939
  · exact B277943
  · exact B277947
  · exact B277951
  · exact B277955
  · exact B277959
  · exact B277963
  · exact B277967
  · exact B277971
  · exact B277975
  · exact B277979
  · exact B277983
  · exact B277987
  · exact B277991
  · exact B277995
  · exact B277999
  · exact B278003
  · exact B278007
  · exact B278011
  · exact B278015
  · exact B278019
  · exact B278023
  · exact B278027
  · exact B278031
  · exact B278035
  · exact B278039
  · exact B278043
  · exact B278047
  · exact B278051
  · exact B278055
  · exact B278059
  · exact B278063
  · exact B278067
  · exact B278071
  · exact B278075
  · exact B278079
  · exact B278083
  · exact B278087
  · exact B278091
  · exact B278095
  · exact B278099
  · exact B278103
  · exact B278107
  · exact B278111
  · exact B278115
  · exact B278119
  · exact B278123
  · exact B278127
  · exact B278131
  · exact B278135
  · exact B278139
  · exact B278143
  · exact B278147
  · exact B278151
  · exact B278155
  · exact B278159
  · exact B278163
  · exact B278167
  · exact B278171
  · exact B278175
  · exact B278179
  · exact B278183
  · exact B278187
  · exact B278191
  · exact B278195
  · exact B278199
  · exact B278203
  · exact B278207
  · exact B278211
  · exact B278215
  · exact B278219
  · exact B278223
  · exact B278227
  · exact B278231
  · exact B278235
  · exact B278239
  · exact B278243
  · exact B278247
  · exact B278251
  · exact B278255
  · exact B278259
  · exact B278263
  · exact B278267
  · exact B278271
  · exact B278275
  · exact B278279
  · exact B278283
  · exact B278287
  · exact B278291
  · exact B278295
  · exact B278299
  · exact B278303
  · exact B278307
  · exact B278311
  · exact B278315
  · exact B278319
  · exact B278323
  · exact B278327
  · exact B278331
  · exact B278335
  · exact B278339
  · exact B278343
  · exact B278347
  · exact B278351
  · exact B278355
  · exact B278359
  · exact B278363
  · exact B278367
  · exact B278371
  · exact B278375
  · exact B278379
  · exact B278383
  · exact B278387
  · exact B278391
  · exact B278395
  · exact B278399
  · exact B278403
  · exact B278407
  · exact B278411
  · exact B278415
  · exact B278419
  · exact B278423
  · exact B278427
  · exact B278431
  · exact B278435
  · exact B278439
  · exact B278443
  · exact B278447
  · exact B278451
  · exact B278455
  · exact B278459
  · exact B278463
  · exact B278467
  · exact B278471
  · exact B278475
  · exact B278479
  · exact B278483
  · exact B278487
  · exact B278491
  · exact B278495
  · exact B278499
  · exact B278503
  · exact B278507
  · exact B278511
  · exact B278515
  · exact B278519
  · exact B278523
  · exact B278527
  · exact B278531
  · exact B278535
  · exact B278539
  · exact B278543
  · exact B278547
  · exact B278551
  · exact B278555
  · exact B278559
  · exact B278563
  · exact B278567
  · exact B278571
  · exact B278575
  · exact B278579
  · exact B278583
  · exact B278587
  · exact B278591
  · exact B278595
  · exact B278599
  · exact B278603
  · exact B278607
  · exact B278611
  · exact B278615
  · exact B278619
  · exact B278623

theorem C1 (j : ℕ) (h1 : 69656 ≤ j) (h2 : j ≤ 69955) : Blo 275825 (4 * j + 3) := by
  interval_cases j
  · exact B278627
  · exact B278631
  · exact B278635
  · exact B278639
  · exact B278643
  · exact B278647
  · exact B278651
  · exact B278655
  · exact B278659
  · exact B278663
  · exact B278667
  · exact B278671
  · exact B278675
  · exact B278679
  · exact B278683
  · exact B278687
  · exact B278691
  · exact B278695
  · exact B278699
  · exact B278703
  · exact B278707
  · exact B278711
  · exact B278715
  · exact B278719
  · exact B278723
  · exact B278727
  · exact B278731
  · exact B278735
  · exact B278739
  · exact B278743
  · exact B278747
  · exact B278751
  · exact B278755
  · exact B278759
  · exact B278763
  · exact B278767
  · exact B278771
  · exact B278775
  · exact B278779
  · exact B278783
  · exact B278787
  · exact B278791
  · exact B278795
  · exact B278799
  · exact B278803
  · exact B278807
  · exact B278811
  · exact B278815
  · exact B278819
  · exact B278823
  · exact B278827
  · exact B278831
  · exact B278835
  · exact B278839
  · exact B278843
  · exact B278847
  · exact B278851
  · exact B278855
  · exact B278859
  · exact B278863
  · exact B278867
  · exact B278871
  · exact B278875
  · exact B278879
  · exact B278883
  · exact B278887
  · exact B278891
  · exact B278895
  · exact B278899
  · exact B278903
  · exact B278907
  · exact B278911
  · exact B278915
  · exact B278919
  · exact B278923
  · exact B278927
  · exact B278931
  · exact B278935
  · exact B278939
  · exact B278943
  · exact B278947
  · exact B278951
  · exact B278955
  · exact B278959
  · exact B278963
  · exact B278967
  · exact B278971
  · exact B278975
  · exact B278979
  · exact B278983
  · exact B278987
  · exact B278991
  · exact B278995
  · exact B278999
  · exact B279003
  · exact B279007
  · exact B279011
  · exact B279015
  · exact B279019
  · exact B279023
  · exact B279027
  · exact B279031
  · exact B279035
  · exact B279039
  · exact B279043
  · exact B279047
  · exact B279051
  · exact B279055
  · exact B279059
  · exact B279063
  · exact B279067
  · exact B279071
  · exact B279075
  · exact B279079
  · exact B279083
  · exact B279087
  · exact B279091
  · exact B279095
  · exact B279099
  · exact B279103
  · exact B279107
  · exact B279111
  · exact B279115
  · exact B279119
  · exact B279123
  · exact B279127
  · exact B279131
  · exact B279135
  · exact B279139
  · exact B279143
  · exact B279147
  · exact B279151
  · exact B279155
  · exact B279159
  · exact B279163
  · exact B279167
  · exact B279171
  · exact B279175
  · exact B279179
  · exact B279183
  · exact B279187
  · exact B279191
  · exact B279195
  · exact B279199
  · exact B279203
  · exact B279207
  · exact B279211
  · exact B279215
  · exact B279219
  · exact B279223
  · exact B279227
  · exact B279231
  · exact B279235
  · exact B279239
  · exact B279243
  · exact B279247
  · exact B279251
  · exact B279255
  · exact B279259
  · exact B279263
  · exact B279267
  · exact B279271
  · exact B279275
  · exact B279279
  · exact B279283
  · exact B279287
  · exact B279291
  · exact B279295
  · exact B279299
  · exact B279303
  · exact B279307
  · exact B279311
  · exact B279315
  · exact B279319
  · exact B279323
  · exact B279327
  · exact B279331
  · exact B279335
  · exact B279339
  · exact B279343
  · exact B279347
  · exact B279351
  · exact B279355
  · exact B279359
  · exact B279363
  · exact B279367
  · exact B279371
  · exact B279375
  · exact B279379
  · exact B279383
  · exact B279387
  · exact B279391
  · exact B279395
  · exact B279399
  · exact B279403
  · exact B279407
  · exact B279411
  · exact B279415
  · exact B279419
  · exact B279423
  · exact B279427
  · exact B279431
  · exact B279435
  · exact B279439
  · exact B279443
  · exact B279447
  · exact B279451
  · exact B279455
  · exact B279459
  · exact B279463
  · exact B279467
  · exact B279471
  · exact B279475
  · exact B279479
  · exact B279483
  · exact B279487
  · exact B279491
  · exact B279495
  · exact B279499
  · exact B279503
  · exact B279507
  · exact B279511
  · exact B279515
  · exact B279519
  · exact B279523
  · exact B279527
  · exact B279531
  · exact B279535
  · exact B279539
  · exact B279543
  · exact B279547
  · exact B279551
  · exact B279555
  · exact B279559
  · exact B279563
  · exact B279567
  · exact B279571
  · exact B279575
  · exact B279579
  · exact B279583
  · exact B279587
  · exact B279591
  · exact B279595
  · exact B279599
  · exact B279603
  · exact B279607
  · exact B279611
  · exact B279615
  · exact B279619
  · exact B279623
  · exact B279627
  · exact B279631
  · exact B279635
  · exact B279639
  · exact B279643
  · exact B279647
  · exact B279651
  · exact B279655
  · exact B279659
  · exact B279663
  · exact B279667
  · exact B279671
  · exact B279675
  · exact B279679
  · exact B279683
  · exact B279687
  · exact B279691
  · exact B279695
  · exact B279699
  · exact B279703
  · exact B279707
  · exact B279711
  · exact B279715
  · exact B279719
  · exact B279723
  · exact B279727
  · exact B279731
  · exact B279735
  · exact B279739
  · exact B279743
  · exact B279747
  · exact B279751
  · exact B279755
  · exact B279759
  · exact B279763
  · exact B279767
  · exact B279771
  · exact B279775
  · exact B279779
  · exact B279783
  · exact B279787
  · exact B279791
  · exact B279795
  · exact B279799
  · exact B279803
  · exact B279807
  · exact B279811
  · exact B279815
  · exact B279819
  · exact B279823

theorem solution (m : ℕ) (hlo : 275825 ≤ m) (hhi : m ≤ 279825) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 68956 ≤ j := by omega
    have hj2 : j ≤ 69955 := by omega
    have hb : Blo 275825 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 69656 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
