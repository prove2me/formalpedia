-- Prove2me | solution 1 for syracuse_descends_range_350755_354755
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:36.581197+00:00
-- url     : https://prove2.me/submissions/8703a5d0-aad8-4eb9-a712-3e08630f822b

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


theorem B753781 : Blo 350755 753781 := bbase (se 5 (by rfl) ⟨35333, by rfl⟩ : syracuseStep 753781 = 70667) (by norm_num)
theorem B2687093 : Blo 350755 2687093 := bbase (se 5 (by rfl) ⟨125957, by rfl⟩ : syracuseStep 2687093 = 251915) (by norm_num)
theorem B426145 : Blo 350755 426145 := bbase (se 2 (by rfl) ⟨159804, by rfl⟩ : syracuseStep 426145 = 319609) (by norm_num)
theorem B458989 : Blo 350755 458989 := bbase (se 3 (by rfl) ⟨86060, by rfl⟩ : syracuseStep 458989 = 172121) (by norm_num)
theorem B426353 : Blo 350755 426353 := bbase (se 2 (by rfl) ⟨159882, by rfl⟩ : syracuseStep 426353 = 319765) (by norm_num)
theorem B754037 : Blo 350755 754037 := bbase (se 5 (by rfl) ⟨35345, by rfl⟩ : syracuseStep 754037 = 70691) (by norm_num)
theorem B1507733 : Blo 350755 1507733 := bbase (se 6 (by rfl) ⟨35337, by rfl⟩ : syracuseStep 1507733 = 70675) (by norm_num)
theorem B1901045 : Blo 350755 1901045 := bbase (se 5 (by rfl) ⟨89111, by rfl⟩ : syracuseStep 1901045 = 178223) (by norm_num)
theorem B950869 : Blo 350755 950869 := bbase (se 8 (by rfl) ⟨5571, by rfl⟩ : syracuseStep 950869 = 11143) (by norm_num)
theorem B1737509 : Blo 350755 1737509 := bbase (se 4 (by rfl) ⟨162891, by rfl⟩ : syracuseStep 1737509 = 325783) (by norm_num)
theorem B951205 : Blo 350755 951205 := bbase (se 4 (by rfl) ⟨89175, by rfl⟩ : syracuseStep 951205 = 178351) (by norm_num)
theorem B1999829 : Blo 350755 1999829 := bbase (se 7 (by rfl) ⟨23435, by rfl⟩ : syracuseStep 1999829 = 46871) (by norm_num)
theorem B951301 : Blo 350755 951301 := bbase (se 4 (by rfl) ⟨89184, by rfl⟩ : syracuseStep 951301 = 178369) (by norm_num)
theorem B754925 : Blo 350755 754925 := bbase (se 3 (by rfl) ⟨141548, by rfl⟩ : syracuseStep 754925 = 283097) (by norm_num)
theorem B1344869 : Blo 350755 1344869 := bbase (se 4 (by rfl) ⟨126081, by rfl⟩ : syracuseStep 1344869 = 252163) (by norm_num)
theorem B394609 : Blo 350755 394609 := bbase (se 2 (by rfl) ⟨147978, by rfl⟩ : syracuseStep 394609 = 295957) (by norm_num)
theorem B394645 : Blo 350755 394645 := bbase (se 6 (by rfl) ⟨9249, by rfl⟩ : syracuseStep 394645 = 18499) (by norm_num)
theorem B394681 : Blo 350755 394681 := bbase (se 2 (by rfl) ⟨148005, by rfl⟩ : syracuseStep 394681 = 296011) (by norm_num)
theorem B394717 : Blo 350755 394717 := bbase (se 3 (by rfl) ⟨74009, by rfl⟩ : syracuseStep 394717 = 148019) (by norm_num)
theorem B755165 : Blo 350755 755165 := bbase (se 3 (by rfl) ⟨141593, by rfl⟩ : syracuseStep 755165 = 283187) (by norm_num)
theorem B394753 : Blo 350755 394753 := bbase (se 2 (by rfl) ⟨148032, by rfl⟩ : syracuseStep 394753 = 296065) (by norm_num)
theorem B394789 : Blo 350755 394789 := bbase (se 4 (by rfl) ⟨37011, by rfl⟩ : syracuseStep 394789 = 74023) (by norm_num)
theorem B394825 : Blo 350755 394825 := bbase (se 2 (by rfl) ⟨148059, by rfl⟩ : syracuseStep 394825 = 296119) (by norm_num)
theorem B394861 : Blo 350755 394861 := bbase (se 3 (by rfl) ⟨74036, by rfl⟩ : syracuseStep 394861 = 148073) (by norm_num)
theorem B1345157 : Blo 350755 1345157 := bbase (se 4 (by rfl) ⟨126108, by rfl⟩ : syracuseStep 1345157 = 252217) (by norm_num)
theorem B394897 : Blo 350755 394897 := bbase (se 2 (by rfl) ⟨148086, by rfl⟩ : syracuseStep 394897 = 296173) (by norm_num)
theorem B1312405 : Blo 350755 1312405 := bbase (se 6 (by rfl) ⟨30759, by rfl⟩ : syracuseStep 1312405 = 61519) (by norm_num)
theorem B394933 : Blo 350755 394933 := bbase (se 5 (by rfl) ⟨18512, by rfl⟩ : syracuseStep 394933 = 37025) (by norm_num)
theorem B362165 : Blo 350755 362165 := bbase (se 5 (by rfl) ⟨16976, by rfl⟩ : syracuseStep 362165 = 33953) (by norm_num)
theorem B394969 : Blo 350755 394969 := bbase (se 2 (by rfl) ⟨148113, by rfl⟩ : syracuseStep 394969 = 296227) (by norm_num)
theorem B395005 : Blo 350755 395005 := bbase (se 3 (by rfl) ⟨74063, by rfl⟩ : syracuseStep 395005 = 148127) (by norm_num)
theorem B395041 : Blo 350755 395041 := bbase (se 2 (by rfl) ⟨148140, by rfl⟩ : syracuseStep 395041 = 296281) (by norm_num)
theorem B526133 : Blo 350755 526133 := bbase (se 5 (by rfl) ⟨24662, by rfl⟩ : syracuseStep 526133 = 49325) (by norm_num)
theorem B395077 : Blo 350755 395077 := bbase (se 4 (by rfl) ⟨37038, by rfl⟩ : syracuseStep 395077 = 74077) (by norm_num)
theorem B526157 : Blo 350755 526157 := bbase (se 3 (by rfl) ⟨98654, by rfl⟩ : syracuseStep 526157 = 197309) (by norm_num)
theorem B526181 : Blo 350755 526181 := bbase (se 4 (by rfl) ⟨49329, by rfl⟩ : syracuseStep 526181 = 98659) (by norm_num)
theorem B395113 : Blo 350755 395113 := bbase (se 2 (by rfl) ⟨148167, by rfl⟩ : syracuseStep 395113 = 296335) (by norm_num)
theorem B526205 : Blo 350755 526205 := bbase (se 3 (by rfl) ⟨98663, by rfl⟩ : syracuseStep 526205 = 197327) (by norm_num)
theorem B395149 : Blo 350755 395149 := bbase (se 3 (by rfl) ⟨74090, by rfl⟩ : syracuseStep 395149 = 148181) (by norm_num)
theorem B526229 : Blo 350755 526229 := bbase (se 6 (by rfl) ⟨12333, by rfl⟩ : syracuseStep 526229 = 24667) (by norm_num)
theorem B526253 : Blo 350755 526253 := bbase (se 3 (by rfl) ⟨98672, by rfl⟩ : syracuseStep 526253 = 197345) (by norm_num)
theorem B395185 : Blo 350755 395185 := bbase (se 2 (by rfl) ⟨148194, by rfl⟩ : syracuseStep 395185 = 296389) (by norm_num)
theorem B526277 : Blo 350755 526277 := bbase (se 4 (by rfl) ⟨49338, by rfl⟩ : syracuseStep 526277 = 98677) (by norm_num)
theorem B395221 : Blo 350755 395221 := bbase (se 7 (by rfl) ⟨4631, by rfl⟩ : syracuseStep 395221 = 9263) (by norm_num)
theorem B755669 : Blo 350755 755669 := bbase (se 7 (by rfl) ⟨8855, by rfl⟩ : syracuseStep 755669 = 17711) (by norm_num)
theorem B526301 : Blo 350755 526301 := bbase (se 3 (by rfl) ⟨98681, by rfl⟩ : syracuseStep 526301 = 197363) (by norm_num)
theorem B755677 : Blo 350755 755677 := bbase (se 3 (by rfl) ⟨141689, by rfl⟩ : syracuseStep 755677 = 283379) (by norm_num)
theorem B526325 : Blo 350755 526325 := bbase (se 5 (by rfl) ⟨24671, by rfl⟩ : syracuseStep 526325 = 49343) (by norm_num)
theorem B395257 : Blo 350755 395257 := bbase (se 2 (by rfl) ⟨148221, by rfl⟩ : syracuseStep 395257 = 296443) (by norm_num)
theorem B526349 : Blo 350755 526349 := bbase (se 3 (by rfl) ⟨98690, by rfl⟩ : syracuseStep 526349 = 197381) (by norm_num)
theorem B3377173 : Blo 350755 3377173 := bbase (se 6 (by rfl) ⟨79152, by rfl⟩ : syracuseStep 3377173 = 158305) (by norm_num)
theorem B395293 : Blo 350755 395293 := bbase (se 3 (by rfl) ⟨74117, by rfl⟩ : syracuseStep 395293 = 148235) (by norm_num)
theorem B526373 : Blo 350755 526373 := bbase (se 4 (by rfl) ⟨49347, by rfl⟩ : syracuseStep 526373 = 98695) (by norm_num)
theorem B526397 : Blo 350755 526397 := bbase (se 3 (by rfl) ⟨98699, by rfl⟩ : syracuseStep 526397 = 197399) (by norm_num)
theorem B395329 : Blo 350755 395329 := bbase (se 2 (by rfl) ⟨148248, by rfl⟩ : syracuseStep 395329 = 296497) (by norm_num)
theorem B591941 : Blo 350755 591941 := bbase (se 4 (by rfl) ⟨55494, by rfl⟩ : syracuseStep 591941 = 110989) (by norm_num)
theorem B526421 : Blo 350755 526421 := bbase (se 8 (by rfl) ⟨3084, by rfl⟩ : syracuseStep 526421 = 6169) (by norm_num)
theorem B395365 : Blo 350755 395365 := bbase (se 4 (by rfl) ⟨37065, by rfl⟩ : syracuseStep 395365 = 74131) (by norm_num)
theorem B526445 : Blo 350755 526445 := bbase (se 3 (by rfl) ⟨98708, by rfl⟩ : syracuseStep 526445 = 197417) (by norm_num)
theorem B526469 : Blo 350755 526469 := bbase (se 4 (by rfl) ⟨49356, by rfl⟩ : syracuseStep 526469 = 98713) (by norm_num)
theorem B1509509 : Blo 350755 1509509 := bbase (se 4 (by rfl) ⟨141516, by rfl⟩ : syracuseStep 1509509 = 283033) (by norm_num)
theorem B395401 : Blo 350755 395401 := bbase (se 2 (by rfl) ⟨148275, by rfl⟩ : syracuseStep 395401 = 296551) (by norm_num)
theorem B526493 : Blo 350755 526493 := bbase (se 3 (by rfl) ⟨98717, by rfl⟩ : syracuseStep 526493 = 197435) (by norm_num)
theorem B395437 : Blo 350755 395437 := bbase (se 3 (by rfl) ⟨74144, by rfl⟩ : syracuseStep 395437 = 148289) (by norm_num)
theorem B526517 : Blo 350755 526517 := bbase (se 5 (by rfl) ⟨24680, by rfl⟩ : syracuseStep 526517 = 49361) (by norm_num)
theorem B592069 : Blo 350755 592069 := bbase (se 4 (by rfl) ⟨55506, by rfl⟩ : syracuseStep 592069 = 111013) (by norm_num)
theorem B526541 : Blo 350755 526541 := bbase (se 3 (by rfl) ⟨98726, by rfl⟩ : syracuseStep 526541 = 197453) (by norm_num)
theorem B395473 : Blo 350755 395473 := bbase (se 2 (by rfl) ⟨148302, by rfl⟩ : syracuseStep 395473 = 296605) (by norm_num)
theorem B526565 : Blo 350755 526565 := bbase (se 4 (by rfl) ⟨49365, by rfl⟩ : syracuseStep 526565 = 98731) (by norm_num)
theorem B395509 : Blo 350755 395509 := bbase (se 5 (by rfl) ⟨18539, by rfl⟩ : syracuseStep 395509 = 37079) (by norm_num)
theorem B526589 : Blo 350755 526589 := bbase (se 3 (by rfl) ⟨98735, by rfl⟩ : syracuseStep 526589 = 197471) (by norm_num)
theorem B526613 : Blo 350755 526613 := bbase (se 6 (by rfl) ⟨12342, by rfl⟩ : syracuseStep 526613 = 24685) (by norm_num)
theorem B395545 : Blo 350755 395545 := bbase (se 2 (by rfl) ⟨148329, by rfl⟩ : syracuseStep 395545 = 296659) (by norm_num)
theorem B592157 : Blo 350755 592157 := bbase (se 3 (by rfl) ⟨111029, by rfl⟩ : syracuseStep 592157 = 222059) (by norm_num)
theorem B526637 : Blo 350755 526637 := bbase (se 3 (by rfl) ⟨98744, by rfl⟩ : syracuseStep 526637 = 197489) (by norm_num)
theorem B395581 : Blo 350755 395581 := bbase (se 3 (by rfl) ⟨74171, by rfl⟩ : syracuseStep 395581 = 148343) (by norm_num)
theorem B526661 : Blo 350755 526661 := bbase (se 4 (by rfl) ⟨49374, by rfl⟩ : syracuseStep 526661 = 98749) (by norm_num)
theorem B526685 : Blo 350755 526685 := bbase (se 3 (by rfl) ⟨98753, by rfl⟩ : syracuseStep 526685 = 197507) (by norm_num)
theorem B395617 : Blo 350755 395617 := bbase (se 2 (by rfl) ⟨148356, by rfl⟩ : syracuseStep 395617 = 296713) (by norm_num)
theorem B526709 : Blo 350755 526709 := bbase (se 5 (by rfl) ⟨24689, by rfl⟩ : syracuseStep 526709 = 49379) (by norm_num)
theorem B1509749 : Blo 350755 1509749 := bbase (se 5 (by rfl) ⟨70769, by rfl⟩ : syracuseStep 1509749 = 141539) (by norm_num)
theorem B395653 : Blo 350755 395653 := bbase (se 4 (by rfl) ⟨37092, by rfl⟩ : syracuseStep 395653 = 74185) (by norm_num)
theorem B526733 : Blo 350755 526733 := bbase (se 3 (by rfl) ⟨98762, by rfl⟩ : syracuseStep 526733 = 197525) (by norm_num)
theorem B592285 : Blo 350755 592285 := bbase (se 3 (by rfl) ⟨111053, by rfl⟩ : syracuseStep 592285 = 222107) (by norm_num)
theorem B526757 : Blo 350755 526757 := bbase (se 4 (by rfl) ⟨49383, by rfl⟩ : syracuseStep 526757 = 98767) (by norm_num)
theorem B395689 : Blo 350755 395689 := bbase (se 2 (by rfl) ⟨148383, by rfl⟩ : syracuseStep 395689 = 296767) (by norm_num)
theorem B526781 : Blo 350755 526781 := bbase (se 3 (by rfl) ⟨98771, by rfl⟩ : syracuseStep 526781 = 197543) (by norm_num)
theorem B395725 : Blo 350755 395725 := bbase (se 3 (by rfl) ⟨74198, by rfl⟩ : syracuseStep 395725 = 148397) (by norm_num)
theorem B526805 : Blo 350755 526805 := bbase (se 7 (by rfl) ⟨6173, by rfl⟩ : syracuseStep 526805 = 12347) (by norm_num)
theorem B526829 : Blo 350755 526829 := bbase (se 3 (by rfl) ⟨98780, by rfl⟩ : syracuseStep 526829 = 197561) (by norm_num)
theorem B395761 : Blo 350755 395761 := bbase (se 2 (by rfl) ⟨148410, by rfl⟩ : syracuseStep 395761 = 296821) (by norm_num)
theorem B592373 : Blo 350755 592373 := bbase (se 5 (by rfl) ⟨27767, by rfl⟩ : syracuseStep 592373 = 55535) (by norm_num)
theorem B526853 : Blo 350755 526853 := bbase (se 4 (by rfl) ⟨49392, by rfl⟩ : syracuseStep 526853 = 98785) (by norm_num)
theorem B395797 : Blo 350755 395797 := bbase (se 6 (by rfl) ⟨9276, by rfl⟩ : syracuseStep 395797 = 18553) (by norm_num)
theorem B526877 : Blo 350755 526877 := bbase (se 3 (by rfl) ⟨98789, by rfl⟩ : syracuseStep 526877 = 197579) (by norm_num)
theorem B526901 : Blo 350755 526901 := bbase (se 5 (by rfl) ⟨24698, by rfl⟩ : syracuseStep 526901 = 49397) (by norm_num)
theorem B2034229 : Blo 350755 2034229 := bbase (se 5 (by rfl) ⟨95354, by rfl⟩ : syracuseStep 2034229 = 190709) (by norm_num)
theorem B395833 : Blo 350755 395833 := bbase (se 2 (by rfl) ⟨148437, by rfl⟩ : syracuseStep 395833 = 296875) (by norm_num)
theorem B526925 : Blo 350755 526925 := bbase (se 3 (by rfl) ⟨98798, by rfl⟩ : syracuseStep 526925 = 197597) (by norm_num)
theorem B395869 : Blo 350755 395869 := bbase (se 3 (by rfl) ⟨74225, by rfl⟩ : syracuseStep 395869 = 148451) (by norm_num)
theorem B526949 : Blo 350755 526949 := bbase (se 4 (by rfl) ⟨49401, by rfl⟩ : syracuseStep 526949 = 98803) (by norm_num)
theorem B592501 : Blo 350755 592501 := bbase (se 5 (by rfl) ⟨27773, by rfl⟩ : syracuseStep 592501 = 55547) (by norm_num)
theorem B526973 : Blo 350755 526973 := bbase (se 3 (by rfl) ⟨98807, by rfl⟩ : syracuseStep 526973 = 197615) (by norm_num)
theorem B395905 : Blo 350755 395905 := bbase (se 2 (by rfl) ⟨148464, by rfl⟩ : syracuseStep 395905 = 296929) (by norm_num)
theorem B526997 : Blo 350755 526997 := bbase (se 6 (by rfl) ⟨12351, by rfl⟩ : syracuseStep 526997 = 24703) (by norm_num)
theorem B395941 : Blo 350755 395941 := bbase (se 4 (by rfl) ⟨37119, by rfl⟩ : syracuseStep 395941 = 74239) (by norm_num)
theorem B527021 : Blo 350755 527021 := bbase (se 3 (by rfl) ⟨98816, by rfl⟩ : syracuseStep 527021 = 197633) (by norm_num)
theorem B527045 : Blo 350755 527045 := bbase (se 4 (by rfl) ⟨49410, by rfl⟩ : syracuseStep 527045 = 98821) (by norm_num)
theorem B395977 : Blo 350755 395977 := bbase (se 2 (by rfl) ⟨148491, by rfl⟩ : syracuseStep 395977 = 296983) (by norm_num)
theorem B592589 : Blo 350755 592589 := bbase (se 3 (by rfl) ⟨111110, by rfl⟩ : syracuseStep 592589 = 222221) (by norm_num)
theorem B527069 : Blo 350755 527069 := bbase (se 3 (by rfl) ⟨98825, by rfl⟩ : syracuseStep 527069 = 197651) (by norm_num)
theorem B396013 : Blo 350755 396013 := bbase (se 3 (by rfl) ⟨74252, by rfl⟩ : syracuseStep 396013 = 148505) (by norm_num)
theorem B527093 : Blo 350755 527093 := bbase (se 5 (by rfl) ⟨24707, by rfl⟩ : syracuseStep 527093 = 49415) (by norm_num)
theorem B789245 : Blo 350755 789245 := bbase (se 3 (by rfl) ⟨147983, by rfl⟩ : syracuseStep 789245 = 295967) (by norm_num)
theorem B527117 : Blo 350755 527117 := bbase (se 3 (by rfl) ⟨98834, by rfl⟩ : syracuseStep 527117 = 197669) (by norm_num)
theorem B396049 : Blo 350755 396049 := bbase (se 2 (by rfl) ⟨148518, by rfl⟩ : syracuseStep 396049 = 297037) (by norm_num)
theorem B527141 : Blo 350755 527141 := bbase (se 4 (by rfl) ⟨49419, by rfl⟩ : syracuseStep 527141 = 98839) (by norm_num)
theorem B1346341 : Blo 350755 1346341 := bbase (se 4 (by rfl) ⟨126219, by rfl⟩ : syracuseStep 1346341 = 252439) (by norm_num)
theorem B396085 : Blo 350755 396085 := bbase (se 5 (by rfl) ⟨18566, by rfl⟩ : syracuseStep 396085 = 37133) (by norm_num)
theorem B527165 : Blo 350755 527165 := bbase (se 3 (by rfl) ⟨98843, by rfl⟩ : syracuseStep 527165 = 197687) (by norm_num)
theorem B789317 : Blo 350755 789317 := bbase (se 4 (by rfl) ⟨73998, by rfl⟩ : syracuseStep 789317 = 147997) (by norm_num)
theorem B1084229 : Blo 350755 1084229 := bbase (se 4 (by rfl) ⟨101646, by rfl⟩ : syracuseStep 1084229 = 203293) (by norm_num)
theorem B592717 : Blo 350755 592717 := bbase (se 3 (by rfl) ⟨111134, by rfl⟩ : syracuseStep 592717 = 222269) (by norm_num)
theorem B527189 : Blo 350755 527189 := bbase (se 9 (by rfl) ⟨1544, by rfl⟩ : syracuseStep 527189 = 3089) (by norm_num)
theorem B396121 : Blo 350755 396121 := bbase (se 2 (by rfl) ⟨148545, by rfl⟩ : syracuseStep 396121 = 297091) (by norm_num)
theorem B527213 : Blo 350755 527213 := bbase (se 3 (by rfl) ⟨98852, by rfl⟩ : syracuseStep 527213 = 197705) (by norm_num)
theorem B396157 : Blo 350755 396157 := bbase (se 3 (by rfl) ⟨74279, by rfl⟩ : syracuseStep 396157 = 148559) (by norm_num)
theorem B527237 : Blo 350755 527237 := bbase (se 4 (by rfl) ⟨49428, by rfl⟩ : syracuseStep 527237 = 98857) (by norm_num)
theorem B789389 : Blo 350755 789389 := bbase (se 3 (by rfl) ⟨148010, by rfl⟩ : syracuseStep 789389 = 296021) (by norm_num)
theorem B527261 : Blo 350755 527261 := bbase (se 3 (by rfl) ⟨98861, by rfl⟩ : syracuseStep 527261 = 197723) (by norm_num)
theorem B396193 : Blo 350755 396193 := bbase (se 2 (by rfl) ⟨148572, by rfl⟩ : syracuseStep 396193 = 297145) (by norm_num)
theorem B592805 : Blo 350755 592805 := bbase (se 4 (by rfl) ⟨55575, by rfl⟩ : syracuseStep 592805 = 111151) (by norm_num)
theorem B527285 : Blo 350755 527285 := bbase (se 5 (by rfl) ⟨24716, by rfl⟩ : syracuseStep 527285 = 49433) (by norm_num)
theorem B396229 : Blo 350755 396229 := bbase (se 4 (by rfl) ⟨37146, by rfl⟩ : syracuseStep 396229 = 74293) (by norm_num)
theorem B527309 : Blo 350755 527309 := bbase (se 3 (by rfl) ⟨98870, by rfl⟩ : syracuseStep 527309 = 197741) (by norm_num)
theorem B789461 : Blo 350755 789461 := bbase (se 7 (by rfl) ⟨9251, by rfl⟩ : syracuseStep 789461 = 18503) (by norm_num)
theorem B527333 : Blo 350755 527333 := bbase (se 4 (by rfl) ⟨49437, by rfl⟩ : syracuseStep 527333 = 98875) (by norm_num)
theorem B396265 : Blo 350755 396265 := bbase (se 2 (by rfl) ⟨148599, by rfl⟩ : syracuseStep 396265 = 297199) (by norm_num)
theorem B527357 : Blo 350755 527357 := bbase (se 3 (by rfl) ⟨98879, by rfl⟩ : syracuseStep 527357 = 197759) (by norm_num)
theorem B396301 : Blo 350755 396301 := bbase (se 3 (by rfl) ⟨74306, by rfl⟩ : syracuseStep 396301 = 148613) (by norm_num)
theorem B527381 : Blo 350755 527381 := bbase (se 6 (by rfl) ⟨12360, by rfl⟩ : syracuseStep 527381 = 24721) (by norm_num)
theorem B789533 : Blo 350755 789533 := bbase (se 3 (by rfl) ⟨148037, by rfl⟩ : syracuseStep 789533 = 296075) (by norm_num)
theorem B592933 : Blo 350755 592933 := bbase (se 4 (by rfl) ⟨55587, by rfl⟩ : syracuseStep 592933 = 111175) (by norm_num)
theorem B527405 : Blo 350755 527405 := bbase (se 3 (by rfl) ⟨98888, by rfl⟩ : syracuseStep 527405 = 197777) (by norm_num)
theorem B396337 : Blo 350755 396337 := bbase (se 2 (by rfl) ⟨148626, by rfl⟩ : syracuseStep 396337 = 297253) (by norm_num)
theorem B887861 : Blo 350755 887861 := bbase (se 5 (by rfl) ⟨41618, by rfl⟩ : syracuseStep 887861 = 83237) (by norm_num)
theorem B527429 : Blo 350755 527429 := bbase (se 4 (by rfl) ⟨49446, by rfl⟩ : syracuseStep 527429 = 98893) (by norm_num)
theorem B756805 : Blo 350755 756805 := bbase (se 4 (by rfl) ⟨70950, by rfl⟩ : syracuseStep 756805 = 141901) (by norm_num)
theorem B396373 : Blo 350755 396373 := bbase (se 8 (by rfl) ⟨2322, by rfl⟩ : syracuseStep 396373 = 4645) (by norm_num)
theorem B1346645 : Blo 350755 1346645 := bbase (se 8 (by rfl) ⟨7890, by rfl⟩ : syracuseStep 1346645 = 15781) (by norm_num)
theorem B527453 : Blo 350755 527453 := bbase (se 3 (by rfl) ⟨98897, by rfl⟩ : syracuseStep 527453 = 197795) (by norm_num)
theorem B789605 : Blo 350755 789605 := bbase (se 4 (by rfl) ⟨74025, by rfl⟩ : syracuseStep 789605 = 148051) (by norm_num)
theorem B527477 : Blo 350755 527477 := bbase (se 5 (by rfl) ⟨24725, by rfl⟩ : syracuseStep 527477 = 49451) (by norm_num)
theorem B396409 : Blo 350755 396409 := bbase (se 2 (by rfl) ⟨148653, by rfl⟩ : syracuseStep 396409 = 297307) (by norm_num)
theorem B593021 : Blo 350755 593021 := bbase (se 3 (by rfl) ⟨111191, by rfl⟩ : syracuseStep 593021 = 222383) (by norm_num)
theorem B527501 : Blo 350755 527501 := bbase (se 3 (by rfl) ⟨98906, by rfl⟩ : syracuseStep 527501 = 197813) (by norm_num)
theorem B2264213 : Blo 350755 2264213 := bbase (se 6 (by rfl) ⟨53067, by rfl⟩ : syracuseStep 2264213 = 106135) (by norm_num)
theorem B396445 : Blo 350755 396445 := bbase (se 3 (by rfl) ⟨74333, by rfl⟩ : syracuseStep 396445 = 148667) (by norm_num)
theorem B527525 : Blo 350755 527525 := bbase (se 4 (by rfl) ⟨49455, by rfl⟩ : syracuseStep 527525 = 98911) (by norm_num)
theorem B789677 : Blo 350755 789677 := bbase (se 3 (by rfl) ⟨148064, by rfl⟩ : syracuseStep 789677 = 296129) (by norm_num)
theorem B527549 : Blo 350755 527549 := bbase (se 3 (by rfl) ⟨98915, by rfl⟩ : syracuseStep 527549 = 197831) (by norm_num)
theorem B396481 : Blo 350755 396481 := bbase (se 2 (by rfl) ⟨148680, by rfl⟩ : syracuseStep 396481 = 297361) (by norm_num)
theorem B527573 : Blo 350755 527573 := bbase (se 7 (by rfl) ⟨6182, by rfl⟩ : syracuseStep 527573 = 12365) (by norm_num)
theorem B396517 : Blo 350755 396517 := bbase (se 4 (by rfl) ⟨37173, by rfl⟩ : syracuseStep 396517 = 74347) (by norm_num)
theorem B527597 : Blo 350755 527597 := bbase (se 3 (by rfl) ⟨98924, by rfl⟩ : syracuseStep 527597 = 197849) (by norm_num)
theorem B789749 : Blo 350755 789749 := bbase (se 5 (by rfl) ⟨37019, by rfl⟩ : syracuseStep 789749 = 74039) (by norm_num)
theorem B593149 : Blo 350755 593149 := bbase (se 3 (by rfl) ⟨111215, by rfl⟩ : syracuseStep 593149 = 222431) (by norm_num)
theorem B527621 : Blo 350755 527621 := bbase (se 4 (by rfl) ⟨49464, by rfl⟩ : syracuseStep 527621 = 98929) (by norm_num)
theorem B396553 : Blo 350755 396553 := bbase (se 2 (by rfl) ⟨148707, by rfl⟩ : syracuseStep 396553 = 297415) (by norm_num)
theorem B527645 : Blo 350755 527645 := bbase (se 3 (by rfl) ⟨98933, by rfl⟩ : syracuseStep 527645 = 197867) (by norm_num)
theorem B396589 : Blo 350755 396589 := bbase (se 3 (by rfl) ⟨74360, by rfl⟩ : syracuseStep 396589 = 148721) (by norm_num)
theorem B527669 : Blo 350755 527669 := bbase (se 5 (by rfl) ⟨24734, by rfl⟩ : syracuseStep 527669 = 49469) (by norm_num)
theorem B789821 : Blo 350755 789821 := bbase (se 3 (by rfl) ⟨148091, by rfl⟩ : syracuseStep 789821 = 296183) (by norm_num)
theorem B527693 : Blo 350755 527693 := bbase (se 3 (by rfl) ⟨98942, by rfl⟩ : syracuseStep 527693 = 197885) (by norm_num)
theorem B396625 : Blo 350755 396625 := bbase (se 2 (by rfl) ⟨148734, by rfl⟩ : syracuseStep 396625 = 297469) (by norm_num)
theorem B593237 : Blo 350755 593237 := bbase (se 11 (by rfl) ⟨434, by rfl⟩ : syracuseStep 593237 = 869) (by norm_num)
theorem B527717 : Blo 350755 527717 := bbase (se 4 (by rfl) ⟨49473, by rfl⟩ : syracuseStep 527717 = 98947) (by norm_num)
theorem B396661 : Blo 350755 396661 := bbase (se 5 (by rfl) ⟨18593, by rfl⟩ : syracuseStep 396661 = 37187) (by norm_num)
theorem B691573 : Blo 350755 691573 := bbase (se 5 (by rfl) ⟨32417, by rfl⟩ : syracuseStep 691573 = 64835) (by norm_num)
theorem B527741 : Blo 350755 527741 := bbase (se 3 (by rfl) ⟨98951, by rfl⟩ : syracuseStep 527741 = 197903) (by norm_num)
theorem B789893 : Blo 350755 789893 := bbase (se 4 (by rfl) ⟨74052, by rfl⟩ : syracuseStep 789893 = 148105) (by norm_num)
theorem B888205 : Blo 350755 888205 := bbase (se 3 (by rfl) ⟨166538, by rfl⟩ : syracuseStep 888205 = 333077) (by norm_num)
theorem B527765 : Blo 350755 527765 := bbase (se 6 (by rfl) ⟨12369, by rfl⟩ : syracuseStep 527765 = 24739) (by norm_num)
theorem B396697 : Blo 350755 396697 := bbase (se 2 (by rfl) ⟨148761, by rfl⟩ : syracuseStep 396697 = 297523) (by norm_num)
theorem B527789 : Blo 350755 527789 := bbase (se 3 (by rfl) ⟨98960, by rfl⟩ : syracuseStep 527789 = 197921) (by norm_num)
theorem B396733 : Blo 350755 396733 := bbase (se 3 (by rfl) ⟨74387, by rfl⟩ : syracuseStep 396733 = 148775) (by norm_num)
theorem B757181 : Blo 350755 757181 := bbase (se 3 (by rfl) ⟨141971, by rfl⟩ : syracuseStep 757181 = 283943) (by norm_num)
theorem B527813 : Blo 350755 527813 := bbase (se 4 (by rfl) ⟨49482, by rfl⟩ : syracuseStep 527813 = 98965) (by norm_num)
theorem B789965 : Blo 350755 789965 := bbase (se 3 (by rfl) ⟨148118, by rfl⟩ : syracuseStep 789965 = 296237) (by norm_num)
theorem B593365 : Blo 350755 593365 := bbase (se 7 (by rfl) ⟨6953, by rfl⟩ : syracuseStep 593365 = 13907) (by norm_num)
theorem B527837 : Blo 350755 527837 := bbase (se 3 (by rfl) ⟨98969, by rfl⟩ : syracuseStep 527837 = 197939) (by norm_num)
theorem B396769 : Blo 350755 396769 := bbase (se 2 (by rfl) ⟨148788, by rfl⟩ : syracuseStep 396769 = 297577) (by norm_num)
theorem B527861 : Blo 350755 527861 := bbase (se 5 (by rfl) ⟨24743, by rfl⟩ : syracuseStep 527861 = 49487) (by norm_num)
theorem B888317 : Blo 350755 888317 := bbase (se 3 (by rfl) ⟨166559, by rfl⟩ : syracuseStep 888317 = 333119) (by norm_num)
theorem B396805 : Blo 350755 396805 := bbase (se 4 (by rfl) ⟨37200, by rfl⟩ : syracuseStep 396805 = 74401) (by norm_num)
theorem B527885 : Blo 350755 527885 := bbase (se 3 (by rfl) ⟨98978, by rfl⟩ : syracuseStep 527885 = 197957) (by norm_num)
theorem B790037 : Blo 350755 790037 := bbase (se 6 (by rfl) ⟨18516, by rfl⟩ : syracuseStep 790037 = 37033) (by norm_num)
theorem B527909 : Blo 350755 527909 := bbase (se 4 (by rfl) ⟨49491, by rfl⟩ : syracuseStep 527909 = 98983) (by norm_num)
theorem B396841 : Blo 350755 396841 := bbase (se 2 (by rfl) ⟨148815, by rfl⟩ : syracuseStep 396841 = 297631) (by norm_num)
theorem B593453 : Blo 350755 593453 := bbase (se 3 (by rfl) ⟨111272, by rfl⟩ : syracuseStep 593453 = 222545) (by norm_num)
theorem B527933 : Blo 350755 527933 := bbase (se 3 (by rfl) ⟨98987, by rfl⟩ : syracuseStep 527933 = 197975) (by norm_num)
theorem B364105 : Blo 350755 364105 := bbase (se 2 (by rfl) ⟨136539, by rfl⟩ : syracuseStep 364105 = 273079) (by norm_num)
theorem B396877 : Blo 350755 396877 := bbase (se 3 (by rfl) ⟨74414, by rfl⟩ : syracuseStep 396877 = 148829) (by norm_num)
theorem B527957 : Blo 350755 527957 := bbase (se 8 (by rfl) ⟨3093, by rfl⟩ : syracuseStep 527957 = 6187) (by norm_num)
theorem B790109 : Blo 350755 790109 := bbase (se 3 (by rfl) ⟨148145, by rfl⟩ : syracuseStep 790109 = 296291) (by norm_num)
theorem B527981 : Blo 350755 527981 := bbase (se 3 (by rfl) ⟨98996, by rfl⟩ : syracuseStep 527981 = 197993) (by norm_num)
theorem B396913 : Blo 350755 396913 := bbase (se 2 (by rfl) ⟨148842, by rfl⟩ : syracuseStep 396913 = 297685) (by norm_num)
theorem B822917 : Blo 350755 822917 := bbase (se 4 (by rfl) ⟨77148, by rfl⟩ : syracuseStep 822917 = 154297) (by norm_num)
theorem B528005 : Blo 350755 528005 := bbase (se 4 (by rfl) ⟨49500, by rfl⟩ : syracuseStep 528005 = 99001) (by norm_num)
theorem B396949 : Blo 350755 396949 := bbase (se 6 (by rfl) ⟨9303, by rfl⟩ : syracuseStep 396949 = 18607) (by norm_num)
theorem B528029 : Blo 350755 528029 := bbase (se 3 (by rfl) ⟨99005, by rfl⟩ : syracuseStep 528029 = 198011) (by norm_num)
theorem B790181 : Blo 350755 790181 := bbase (se 4 (by rfl) ⟨74079, by rfl⟩ : syracuseStep 790181 = 148159) (by norm_num)
theorem B593581 : Blo 350755 593581 := bbase (se 3 (by rfl) ⟨111296, by rfl⟩ : syracuseStep 593581 = 222593) (by norm_num)
theorem B528053 : Blo 350755 528053 := bbase (se 5 (by rfl) ⟨24752, by rfl⟩ : syracuseStep 528053 = 49505) (by norm_num)
theorem B396985 : Blo 350755 396985 := bbase (se 2 (by rfl) ⟨148869, by rfl⟩ : syracuseStep 396985 = 297739) (by norm_num)
theorem B888509 : Blo 350755 888509 := bbase (se 3 (by rfl) ⟨166595, by rfl⟩ : syracuseStep 888509 = 333191) (by norm_num)
theorem B528077 : Blo 350755 528077 := bbase (se 3 (by rfl) ⟨99014, by rfl⟩ : syracuseStep 528077 = 198029) (by norm_num)
theorem B397021 : Blo 350755 397021 := bbase (se 3 (by rfl) ⟨74441, by rfl⟩ : syracuseStep 397021 = 148883) (by norm_num)
theorem B528101 : Blo 350755 528101 := bbase (se 4 (by rfl) ⟨49509, by rfl⟩ : syracuseStep 528101 = 99019) (by norm_num)
theorem B790253 : Blo 350755 790253 := bbase (se 3 (by rfl) ⟨148172, by rfl⟩ : syracuseStep 790253 = 296345) (by norm_num)
theorem B528125 : Blo 350755 528125 := bbase (se 3 (by rfl) ⟨99023, by rfl⟩ : syracuseStep 528125 = 198047) (by norm_num)
theorem B397057 : Blo 350755 397057 := bbase (se 2 (by rfl) ⟨148896, by rfl⟩ : syracuseStep 397057 = 297793) (by norm_num)
theorem B593669 : Blo 350755 593669 := bbase (se 4 (by rfl) ⟨55656, by rfl⟩ : syracuseStep 593669 = 111313) (by norm_num)
theorem B528149 : Blo 350755 528149 := bbase (se 6 (by rfl) ⟨12378, by rfl⟩ : syracuseStep 528149 = 24757) (by norm_num)
theorem B397093 : Blo 350755 397093 := bbase (se 4 (by rfl) ⟨37227, by rfl⟩ : syracuseStep 397093 = 74455) (by norm_num)
theorem B528173 : Blo 350755 528173 := bbase (se 3 (by rfl) ⟨99032, by rfl⟩ : syracuseStep 528173 = 198065) (by norm_num)
theorem B790325 : Blo 350755 790325 := bbase (se 5 (by rfl) ⟨37046, by rfl⟩ : syracuseStep 790325 = 74093) (by norm_num)
theorem B528197 : Blo 350755 528197 := bbase (se 4 (by rfl) ⟨49518, by rfl⟩ : syracuseStep 528197 = 99037) (by norm_num)
theorem B1609541 : Blo 350755 1609541 := bbase (se 4 (by rfl) ⟨150894, by rfl⟩ : syracuseStep 1609541 = 301789) (by norm_num)
theorem B397129 : Blo 350755 397129 := bbase (se 2 (by rfl) ⟨148923, by rfl⟩ : syracuseStep 397129 = 297847) (by norm_num)
theorem B528221 : Blo 350755 528221 := bbase (se 3 (by rfl) ⟨99041, by rfl⟩ : syracuseStep 528221 = 198083) (by norm_num)
theorem B397165 : Blo 350755 397165 := bbase (se 3 (by rfl) ⟨74468, by rfl⟩ : syracuseStep 397165 = 148937) (by norm_num)
theorem B528245 : Blo 350755 528245 := bbase (se 5 (by rfl) ⟨24761, by rfl⟩ : syracuseStep 528245 = 49523) (by norm_num)
theorem B790397 : Blo 350755 790397 := bbase (se 3 (by rfl) ⟨148199, by rfl⟩ : syracuseStep 790397 = 296399) (by norm_num)
theorem B593797 : Blo 350755 593797 := bbase (se 4 (by rfl) ⟨55668, by rfl⟩ : syracuseStep 593797 = 111337) (by norm_num)
theorem B528269 : Blo 350755 528269 := bbase (se 3 (by rfl) ⟨99050, by rfl⟩ : syracuseStep 528269 = 198101) (by norm_num)
theorem B397201 : Blo 350755 397201 := bbase (se 2 (by rfl) ⟨148950, by rfl⟩ : syracuseStep 397201 = 297901) (by norm_num)
theorem B528293 : Blo 350755 528293 := bbase (se 4 (by rfl) ⟨49527, by rfl⟩ : syracuseStep 528293 = 99055) (by norm_num)
theorem B397237 : Blo 350755 397237 := bbase (se 5 (by rfl) ⟨18620, by rfl⟩ : syracuseStep 397237 = 37241) (by norm_num)
theorem B528317 : Blo 350755 528317 := bbase (se 3 (by rfl) ⟨99059, by rfl⟩ : syracuseStep 528317 = 198119) (by norm_num)
theorem B790469 : Blo 350755 790469 := bbase (se 4 (by rfl) ⟨74106, by rfl⟩ : syracuseStep 790469 = 148213) (by norm_num)
theorem B528341 : Blo 350755 528341 := bbase (se 7 (by rfl) ⟨6191, by rfl⟩ : syracuseStep 528341 = 12383) (by norm_num)
theorem B397273 : Blo 350755 397273 := bbase (se 2 (by rfl) ⟨148977, by rfl⟩ : syracuseStep 397273 = 297955) (by norm_num)
theorem B593885 : Blo 350755 593885 := bbase (se 3 (by rfl) ⟨111353, by rfl⟩ : syracuseStep 593885 = 222707) (by norm_num)
theorem B528365 : Blo 350755 528365 := bbase (se 3 (by rfl) ⟨99068, by rfl⟩ : syracuseStep 528365 = 198137) (by norm_num)
theorem B397309 : Blo 350755 397309 := bbase (se 3 (by rfl) ⟨74495, by rfl⟩ : syracuseStep 397309 = 148991) (by norm_num)
theorem B528389 : Blo 350755 528389 := bbase (se 4 (by rfl) ⟨49536, by rfl⟩ : syracuseStep 528389 = 99073) (by norm_num)
theorem B790541 : Blo 350755 790541 := bbase (se 3 (by rfl) ⟨148226, by rfl⟩ : syracuseStep 790541 = 296453) (by norm_num)
theorem B888853 : Blo 350755 888853 := bbase (se 6 (by rfl) ⟨20832, by rfl⟩ : syracuseStep 888853 = 41665) (by norm_num)
theorem B528413 : Blo 350755 528413 := bbase (se 3 (by rfl) ⟨99077, by rfl⟩ : syracuseStep 528413 = 198155) (by norm_num)
theorem B397345 : Blo 350755 397345 := bbase (se 2 (by rfl) ⟨149004, by rfl⟩ : syracuseStep 397345 = 298009) (by norm_num)
theorem B528437 : Blo 350755 528437 := bbase (se 5 (by rfl) ⟨24770, by rfl⟩ : syracuseStep 528437 = 49541) (by norm_num)
theorem B397381 : Blo 350755 397381 := bbase (se 4 (by rfl) ⟨37254, by rfl⟩ : syracuseStep 397381 = 74509) (by norm_num)
theorem B528461 : Blo 350755 528461 := bbase (se 3 (by rfl) ⟨99086, by rfl⟩ : syracuseStep 528461 = 198173) (by norm_num)
theorem B790613 : Blo 350755 790613 := bbase (se 8 (by rfl) ⟨4632, by rfl⟩ : syracuseStep 790613 = 9265) (by norm_num)
theorem B594013 : Blo 350755 594013 := bbase (se 3 (by rfl) ⟨111377, by rfl⟩ : syracuseStep 594013 = 222755) (by norm_num)
theorem B528485 : Blo 350755 528485 := bbase (se 4 (by rfl) ⟨49545, by rfl⟩ : syracuseStep 528485 = 99091) (by norm_num)
theorem B397417 : Blo 350755 397417 := bbase (se 2 (by rfl) ⟨149031, by rfl⟩ : syracuseStep 397417 = 298063) (by norm_num)
theorem B528509 : Blo 350755 528509 := bbase (se 3 (by rfl) ⟨99095, by rfl⟩ : syracuseStep 528509 = 198191) (by norm_num)
theorem B888965 : Blo 350755 888965 := bbase (se 4 (by rfl) ⟨83340, by rfl⟩ : syracuseStep 888965 = 166681) (by norm_num)
theorem B397453 : Blo 350755 397453 := bbase (se 3 (by rfl) ⟨74522, by rfl⟩ : syracuseStep 397453 = 149045) (by norm_num)
theorem B528533 : Blo 350755 528533 := bbase (se 6 (by rfl) ⟨12387, by rfl⟩ : syracuseStep 528533 = 24775) (by norm_num)
theorem B790685 : Blo 350755 790685 := bbase (se 3 (by rfl) ⟨148253, by rfl⟩ : syracuseStep 790685 = 296507) (by norm_num)
theorem B528557 : Blo 350755 528557 := bbase (se 3 (by rfl) ⟨99104, by rfl⟩ : syracuseStep 528557 = 198209) (by norm_num)
theorem B397489 : Blo 350755 397489 := bbase (se 2 (by rfl) ⟨149058, by rfl⟩ : syracuseStep 397489 = 298117) (by norm_num)
theorem B594101 : Blo 350755 594101 := bbase (se 5 (by rfl) ⟨27848, by rfl⟩ : syracuseStep 594101 = 55697) (by norm_num)
theorem B528581 : Blo 350755 528581 := bbase (se 4 (by rfl) ⟨49554, by rfl⟩ : syracuseStep 528581 = 99109) (by norm_num)
theorem B397525 : Blo 350755 397525 := bbase (se 7 (by rfl) ⟨4658, by rfl⟩ : syracuseStep 397525 = 9317) (by norm_num)
theorem B528605 : Blo 350755 528605 := bbase (se 3 (by rfl) ⟨99113, by rfl⟩ : syracuseStep 528605 = 198227) (by norm_num)
theorem B790757 : Blo 350755 790757 := bbase (se 4 (by rfl) ⟨74133, by rfl⟩ : syracuseStep 790757 = 148267) (by norm_num)
theorem B528629 : Blo 350755 528629 := bbase (se 5 (by rfl) ⟨24779, by rfl⟩ : syracuseStep 528629 = 49559) (by norm_num)
theorem B397561 : Blo 350755 397561 := bbase (se 2 (by rfl) ⟨149085, by rfl⟩ : syracuseStep 397561 = 298171) (by norm_num)
theorem B528653 : Blo 350755 528653 := bbase (se 3 (by rfl) ⟨99122, by rfl⟩ : syracuseStep 528653 = 198245) (by norm_num)
theorem B397597 : Blo 350755 397597 := bbase (se 3 (by rfl) ⟨74549, by rfl⟩ : syracuseStep 397597 = 149099) (by norm_num)
theorem B528677 : Blo 350755 528677 := bbase (se 4 (by rfl) ⟨49563, by rfl⟩ : syracuseStep 528677 = 99127) (by norm_num)
theorem B790829 : Blo 350755 790829 := bbase (se 3 (by rfl) ⟨148280, by rfl⟩ : syracuseStep 790829 = 296561) (by norm_num)
theorem B594229 : Blo 350755 594229 := bbase (se 5 (by rfl) ⟨27854, by rfl⟩ : syracuseStep 594229 = 55709) (by norm_num)
theorem B528701 : Blo 350755 528701 := bbase (se 3 (by rfl) ⟨99131, by rfl⟩ : syracuseStep 528701 = 198263) (by norm_num)
theorem B397633 : Blo 350755 397633 := bbase (se 2 (by rfl) ⟨149112, by rfl⟩ : syracuseStep 397633 = 298225) (by norm_num)
theorem B889157 : Blo 350755 889157 := bbase (se 4 (by rfl) ⟨83358, by rfl⟩ : syracuseStep 889157 = 166717) (by norm_num)
theorem B528725 : Blo 350755 528725 := bbase (se 10 (by rfl) ⟨774, by rfl⟩ : syracuseStep 528725 = 1549) (by norm_num)
theorem B397669 : Blo 350755 397669 := bbase (se 4 (by rfl) ⟨37281, by rfl⟩ : syracuseStep 397669 = 74563) (by norm_num)
theorem B528749 : Blo 350755 528749 := bbase (se 3 (by rfl) ⟨99140, by rfl⟩ : syracuseStep 528749 = 198281) (by norm_num)
theorem B790901 : Blo 350755 790901 := bbase (se 5 (by rfl) ⟨37073, by rfl⟩ : syracuseStep 790901 = 74147) (by norm_num)
theorem B528773 : Blo 350755 528773 := bbase (se 4 (by rfl) ⟨49572, by rfl⟩ : syracuseStep 528773 = 99145) (by norm_num)
theorem B397705 : Blo 350755 397705 := bbase (se 2 (by rfl) ⟨149139, by rfl⟩ : syracuseStep 397705 = 298279) (by norm_num)
theorem B594317 : Blo 350755 594317 := bbase (se 3 (by rfl) ⟨111434, by rfl⟩ : syracuseStep 594317 = 222869) (by norm_num)
theorem B528797 : Blo 350755 528797 := bbase (se 3 (by rfl) ⟨99149, by rfl⟩ : syracuseStep 528797 = 198299) (by norm_num)
theorem B1184165 : Blo 350755 1184165 := bbase (se 4 (by rfl) ⟨111015, by rfl⟩ : syracuseStep 1184165 = 222031) (by norm_num)
theorem B397741 : Blo 350755 397741 := bbase (se 3 (by rfl) ⟨74576, by rfl⟩ : syracuseStep 397741 = 149153) (by norm_num)
theorem B528821 : Blo 350755 528821 := bbase (se 5 (by rfl) ⟨24788, by rfl⟩ : syracuseStep 528821 = 49577) (by norm_num)
theorem B790973 : Blo 350755 790973 := bbase (se 3 (by rfl) ⟨148307, by rfl⟩ : syracuseStep 790973 = 296615) (by norm_num)
theorem B528845 : Blo 350755 528845 := bbase (se 3 (by rfl) ⟨99158, by rfl⟩ : syracuseStep 528845 = 198317) (by norm_num)
theorem B397777 : Blo 350755 397777 := bbase (se 2 (by rfl) ⟨149166, by rfl⟩ : syracuseStep 397777 = 298333) (by norm_num)
theorem B430553 : Blo 350755 430553 := bbase (se 2 (by rfl) ⟨161457, by rfl⟩ : syracuseStep 430553 = 322915) (by norm_num)
theorem B528869 : Blo 350755 528869 := bbase (se 4 (by rfl) ⟨49581, by rfl⟩ : syracuseStep 528869 = 99163) (by norm_num)
theorem B397813 : Blo 350755 397813 := bbase (se 5 (by rfl) ⟨18647, by rfl⟩ : syracuseStep 397813 = 37295) (by norm_num)
theorem B528893 : Blo 350755 528893 := bbase (se 3 (by rfl) ⟨99167, by rfl⟩ : syracuseStep 528893 = 198335) (by norm_num)
theorem B791045 : Blo 350755 791045 := bbase (se 4 (by rfl) ⟨74160, by rfl⟩ : syracuseStep 791045 = 148321) (by norm_num)
theorem B594445 : Blo 350755 594445 := bbase (se 3 (by rfl) ⟨111458, by rfl⟩ : syracuseStep 594445 = 222917) (by norm_num)
theorem B528917 : Blo 350755 528917 := bbase (se 6 (by rfl) ⟨12396, by rfl⟩ : syracuseStep 528917 = 24793) (by norm_num)
theorem B397849 : Blo 350755 397849 := bbase (se 2 (by rfl) ⟨149193, by rfl⟩ : syracuseStep 397849 = 298387) (by norm_num)
theorem B528941 : Blo 350755 528941 := bbase (se 3 (by rfl) ⟨99176, by rfl⟩ : syracuseStep 528941 = 198353) (by norm_num)
theorem B397885 : Blo 350755 397885 := bbase (se 3 (by rfl) ⟨74603, by rfl⟩ : syracuseStep 397885 = 149207) (by norm_num)
theorem B528965 : Blo 350755 528965 := bbase (se 4 (by rfl) ⟨49590, by rfl⟩ : syracuseStep 528965 = 99181) (by norm_num)
theorem B791117 : Blo 350755 791117 := bbase (se 3 (by rfl) ⟨148334, by rfl⟩ : syracuseStep 791117 = 296669) (by norm_num)
theorem B528989 : Blo 350755 528989 := bbase (se 3 (by rfl) ⟨99185, by rfl⟩ : syracuseStep 528989 = 198371) (by norm_num)
theorem B397921 : Blo 350755 397921 := bbase (se 2 (by rfl) ⟨149220, by rfl⟩ : syracuseStep 397921 = 298441) (by norm_num)
theorem B594533 : Blo 350755 594533 := bbase (se 4 (by rfl) ⟨55737, by rfl⟩ : syracuseStep 594533 = 111475) (by norm_num)
theorem B1512037 : Blo 350755 1512037 := bbase (se 4 (by rfl) ⟨141753, by rfl⟩ : syracuseStep 1512037 = 283507) (by norm_num)
theorem B529013 : Blo 350755 529013 := bbase (se 5 (by rfl) ⟨24797, by rfl⟩ : syracuseStep 529013 = 49595) (by norm_num)
theorem B397957 : Blo 350755 397957 := bbase (se 4 (by rfl) ⟨37308, by rfl⟩ : syracuseStep 397957 = 74617) (by norm_num)
theorem B529037 : Blo 350755 529037 := bbase (se 3 (by rfl) ⟨99194, by rfl⟩ : syracuseStep 529037 = 198389) (by norm_num)
theorem B791189 : Blo 350755 791189 := bbase (se 6 (by rfl) ⟨18543, by rfl⟩ : syracuseStep 791189 = 37087) (by norm_num)
theorem B889501 : Blo 350755 889501 := bbase (se 3 (by rfl) ⟨166781, by rfl⟩ : syracuseStep 889501 = 333563) (by norm_num)
theorem B529061 : Blo 350755 529061 := bbase (se 4 (by rfl) ⟨49599, by rfl⟩ : syracuseStep 529061 = 99199) (by norm_num)
theorem B397993 : Blo 350755 397993 := bbase (se 2 (by rfl) ⟨149247, by rfl⟩ : syracuseStep 397993 = 298495) (by norm_num)
theorem B529085 : Blo 350755 529085 := bbase (se 3 (by rfl) ⟨99203, by rfl⟩ : syracuseStep 529085 = 198407) (by norm_num)
theorem B398029 : Blo 350755 398029 := bbase (se 3 (by rfl) ⟨74630, by rfl⟩ : syracuseStep 398029 = 149261) (by norm_num)
theorem B529109 : Blo 350755 529109 := bbase (se 7 (by rfl) ⟨6200, by rfl⟩ : syracuseStep 529109 = 12401) (by norm_num)
theorem B791261 : Blo 350755 791261 := bbase (se 3 (by rfl) ⟨148361, by rfl⟩ : syracuseStep 791261 = 296723) (by norm_num)
theorem B594661 : Blo 350755 594661 := bbase (se 4 (by rfl) ⟨55749, by rfl⟩ : syracuseStep 594661 = 111499) (by norm_num)
theorem B529133 : Blo 350755 529133 := bbase (se 3 (by rfl) ⟨99212, by rfl⟩ : syracuseStep 529133 = 198425) (by norm_num)
theorem B398065 : Blo 350755 398065 := bbase (se 2 (by rfl) ⟨149274, by rfl⟩ : syracuseStep 398065 = 298549) (by norm_num)
theorem B529157 : Blo 350755 529157 := bbase (se 4 (by rfl) ⟨49608, by rfl⟩ : syracuseStep 529157 = 99217) (by norm_num)
theorem B889613 : Blo 350755 889613 := bbase (se 3 (by rfl) ⟨166802, by rfl⟩ : syracuseStep 889613 = 333605) (by norm_num)
theorem B398101 : Blo 350755 398101 := bbase (se 6 (by rfl) ⟨9330, by rfl⟩ : syracuseStep 398101 = 18661) (by norm_num)
theorem B529181 : Blo 350755 529181 := bbase (se 3 (by rfl) ⟨99221, by rfl⟩ : syracuseStep 529181 = 198443) (by norm_num)
theorem B791333 : Blo 350755 791333 := bbase (se 4 (by rfl) ⟨74187, by rfl⟩ : syracuseStep 791333 = 148375) (by norm_num)
theorem B529205 : Blo 350755 529205 := bbase (se 5 (by rfl) ⟨24806, by rfl⟩ : syracuseStep 529205 = 49613) (by norm_num)
theorem B398137 : Blo 350755 398137 := bbase (se 2 (by rfl) ⟨149301, by rfl⟩ : syracuseStep 398137 = 298603) (by norm_num)
theorem B594749 : Blo 350755 594749 := bbase (se 3 (by rfl) ⟨111515, by rfl⟩ : syracuseStep 594749 = 223031) (by norm_num)
theorem B529229 : Blo 350755 529229 := bbase (se 3 (by rfl) ⟨99230, by rfl⟩ : syracuseStep 529229 = 198461) (by norm_num)
theorem B1184597 : Blo 350755 1184597 := bbase (se 9 (by rfl) ⟨3470, by rfl⟩ : syracuseStep 1184597 = 6941) (by norm_num)
theorem B398173 : Blo 350755 398173 := bbase (se 3 (by rfl) ⟨74657, by rfl⟩ : syracuseStep 398173 = 149315) (by norm_num)
theorem B529253 : Blo 350755 529253 := bbase (se 4 (by rfl) ⟨49617, by rfl⟩ : syracuseStep 529253 = 99235) (by norm_num)
theorem B791405 : Blo 350755 791405 := bbase (se 3 (by rfl) ⟨148388, by rfl⟩ : syracuseStep 791405 = 296777) (by norm_num)
theorem B529277 : Blo 350755 529277 := bbase (se 3 (by rfl) ⟨99239, by rfl⟩ : syracuseStep 529277 = 198479) (by norm_num)
theorem B398209 : Blo 350755 398209 := bbase (se 2 (by rfl) ⟨149328, by rfl⟩ : syracuseStep 398209 = 298657) (by norm_num)
theorem B529301 : Blo 350755 529301 := bbase (se 6 (by rfl) ⟨12405, by rfl⟩ : syracuseStep 529301 = 24811) (by norm_num)
theorem B398245 : Blo 350755 398245 := bbase (se 4 (by rfl) ⟨37335, by rfl⟩ : syracuseStep 398245 = 74671) (by norm_num)
theorem B529325 : Blo 350755 529325 := bbase (se 3 (by rfl) ⟨99248, by rfl⟩ : syracuseStep 529325 = 198497) (by norm_num)
theorem B791477 : Blo 350755 791477 := bbase (se 5 (by rfl) ⟨37100, by rfl⟩ : syracuseStep 791477 = 74201) (by norm_num)
theorem B594877 : Blo 350755 594877 := bbase (se 3 (by rfl) ⟨111539, by rfl⟩ : syracuseStep 594877 = 223079) (by norm_num)
theorem B529349 : Blo 350755 529349 := bbase (se 4 (by rfl) ⟨49626, by rfl⟩ : syracuseStep 529349 = 99253) (by norm_num)
theorem B398281 : Blo 350755 398281 := bbase (se 2 (by rfl) ⟨149355, by rfl⟩ : syracuseStep 398281 = 298711) (by norm_num)
theorem B889805 : Blo 350755 889805 := bbase (se 3 (by rfl) ⟨166838, by rfl⟩ : syracuseStep 889805 = 333677) (by norm_num)
theorem B529373 : Blo 350755 529373 := bbase (se 3 (by rfl) ⟨99257, by rfl⟩ : syracuseStep 529373 = 198515) (by norm_num)
theorem B398317 : Blo 350755 398317 := bbase (se 3 (by rfl) ⟨74684, by rfl⟩ : syracuseStep 398317 = 149369) (by norm_num)
theorem B529397 : Blo 350755 529397 := bbase (se 5 (by rfl) ⟨24815, by rfl⟩ : syracuseStep 529397 = 49631) (by norm_num)
theorem B791549 : Blo 350755 791549 := bbase (se 3 (by rfl) ⟨148415, by rfl⟩ : syracuseStep 791549 = 296831) (by norm_num)
theorem B529421 : Blo 350755 529421 := bbase (se 3 (by rfl) ⟨99266, by rfl⟩ : syracuseStep 529421 = 198533) (by norm_num)
theorem B398353 : Blo 350755 398353 := bbase (se 2 (by rfl) ⟨149382, by rfl⟩ : syracuseStep 398353 = 298765) (by norm_num)
theorem B3052565 : Blo 350755 3052565 := bbase (se 6 (by rfl) ⟨71544, by rfl⟩ : syracuseStep 3052565 = 143089) (by norm_num)
theorem B594965 : Blo 350755 594965 := bbase (se 6 (by rfl) ⟨13944, by rfl⟩ : syracuseStep 594965 = 27889) (by norm_num)
theorem B529445 : Blo 350755 529445 := bbase (se 4 (by rfl) ⟨49635, by rfl⟩ : syracuseStep 529445 = 99271) (by norm_num)
theorem B398389 : Blo 350755 398389 := bbase (se 5 (by rfl) ⟨18674, by rfl⟩ : syracuseStep 398389 = 37349) (by norm_num)
theorem B529469 : Blo 350755 529469 := bbase (se 3 (by rfl) ⟨99275, by rfl⟩ : syracuseStep 529469 = 198551) (by norm_num)
theorem B791621 : Blo 350755 791621 := bbase (se 4 (by rfl) ⟨74214, by rfl⟩ : syracuseStep 791621 = 148429) (by norm_num)
theorem B529493 : Blo 350755 529493 := bbase (se 8 (by rfl) ⟨3102, by rfl⟩ : syracuseStep 529493 = 6205) (by norm_num)
theorem B398425 : Blo 350755 398425 := bbase (se 2 (by rfl) ⟨149409, by rfl⟩ : syracuseStep 398425 = 298819) (by norm_num)
theorem B529517 : Blo 350755 529517 := bbase (se 3 (by rfl) ⟨99284, by rfl⟩ : syracuseStep 529517 = 198569) (by norm_num)
theorem B398461 : Blo 350755 398461 := bbase (se 3 (by rfl) ⟨74711, by rfl⟩ : syracuseStep 398461 = 149423) (by norm_num)
theorem B529541 : Blo 350755 529541 := bbase (se 4 (by rfl) ⟨49644, by rfl⟩ : syracuseStep 529541 = 99289) (by norm_num)
theorem B791693 : Blo 350755 791693 := bbase (se 3 (by rfl) ⟨148442, by rfl⟩ : syracuseStep 791693 = 296885) (by norm_num)
theorem B595093 : Blo 350755 595093 := bbase (se 6 (by rfl) ⟨13947, by rfl⟩ : syracuseStep 595093 = 27895) (by norm_num)
theorem B529565 : Blo 350755 529565 := bbase (se 3 (by rfl) ⟨99293, by rfl⟩ : syracuseStep 529565 = 198587) (by norm_num)
theorem B398497 : Blo 350755 398497 := bbase (se 2 (by rfl) ⟨149436, by rfl⟩ : syracuseStep 398497 = 298873) (by norm_num)
theorem B529589 : Blo 350755 529589 := bbase (se 5 (by rfl) ⟨24824, by rfl⟩ : syracuseStep 529589 = 49649) (by norm_num)
theorem B398533 : Blo 350755 398533 := bbase (se 4 (by rfl) ⟨37362, by rfl⟩ : syracuseStep 398533 = 74725) (by norm_num)
theorem B529613 : Blo 350755 529613 := bbase (se 3 (by rfl) ⟨99302, by rfl⟩ : syracuseStep 529613 = 198605) (by norm_num)
theorem B791765 : Blo 350755 791765 := bbase (se 7 (by rfl) ⟨9278, by rfl⟩ : syracuseStep 791765 = 18557) (by norm_num)
theorem B529637 : Blo 350755 529637 := bbase (se 4 (by rfl) ⟨49653, by rfl⟩ : syracuseStep 529637 = 99307) (by norm_num)
theorem B398569 : Blo 350755 398569 := bbase (se 2 (by rfl) ⟨149463, by rfl⟩ : syracuseStep 398569 = 298927) (by norm_num)
theorem B595181 : Blo 350755 595181 := bbase (se 3 (by rfl) ⟨111596, by rfl⟩ : syracuseStep 595181 = 223193) (by norm_num)
theorem B529661 : Blo 350755 529661 := bbase (se 3 (by rfl) ⟨99311, by rfl⟩ : syracuseStep 529661 = 198623) (by norm_num)
theorem B1185029 : Blo 350755 1185029 := bbase (se 4 (by rfl) ⟨111096, by rfl⟩ : syracuseStep 1185029 = 222193) (by norm_num)
theorem B398605 : Blo 350755 398605 := bbase (se 3 (by rfl) ⟨74738, by rfl⟩ : syracuseStep 398605 = 149477) (by norm_num)
theorem B529685 : Blo 350755 529685 := bbase (se 6 (by rfl) ⟨12414, by rfl⟩ : syracuseStep 529685 = 24829) (by norm_num)
theorem B791837 : Blo 350755 791837 := bbase (se 3 (by rfl) ⟨148469, by rfl⟩ : syracuseStep 791837 = 296939) (by norm_num)
theorem B890149 : Blo 350755 890149 := bbase (se 4 (by rfl) ⟨83451, by rfl⟩ : syracuseStep 890149 = 166903) (by norm_num)
theorem B529709 : Blo 350755 529709 := bbase (se 3 (by rfl) ⟨99320, by rfl⟩ : syracuseStep 529709 = 198641) (by norm_num)
theorem B398641 : Blo 350755 398641 := bbase (se 2 (by rfl) ⟨149490, by rfl⟩ : syracuseStep 398641 = 298981) (by norm_num)
theorem B529733 : Blo 350755 529733 := bbase (se 4 (by rfl) ⟨49662, by rfl⟩ : syracuseStep 529733 = 99325) (by norm_num)
theorem B398677 : Blo 350755 398677 := bbase (se 14 (by rfl) ⟨36, by rfl⟩ : syracuseStep 398677 = 73) (by norm_num)
theorem B529757 : Blo 350755 529757 := bbase (se 3 (by rfl) ⟨99329, by rfl⟩ : syracuseStep 529757 = 198659) (by norm_num)
theorem B791909 : Blo 350755 791909 := bbase (se 4 (by rfl) ⟨74241, by rfl⟩ : syracuseStep 791909 = 148483) (by norm_num)
theorem B595309 : Blo 350755 595309 := bbase (se 3 (by rfl) ⟨111620, by rfl⟩ : syracuseStep 595309 = 223241) (by norm_num)
theorem B529781 : Blo 350755 529781 := bbase (se 5 (by rfl) ⟨24833, by rfl⟩ : syracuseStep 529781 = 49667) (by norm_num)
theorem B398713 : Blo 350755 398713 := bbase (se 2 (by rfl) ⟨149517, by rfl⟩ : syracuseStep 398713 = 299035) (by norm_num)
theorem B529805 : Blo 350755 529805 := bbase (se 3 (by rfl) ⟨99338, by rfl⟩ : syracuseStep 529805 = 198677) (by norm_num)
theorem B890261 : Blo 350755 890261 := bbase (se 6 (by rfl) ⟨20865, by rfl⟩ : syracuseStep 890261 = 41731) (by norm_num)
theorem B398749 : Blo 350755 398749 := bbase (se 3 (by rfl) ⟨74765, by rfl⟩ : syracuseStep 398749 = 149531) (by norm_num)
theorem B529829 : Blo 350755 529829 := bbase (se 4 (by rfl) ⟨49671, by rfl⟩ : syracuseStep 529829 = 99343) (by norm_num)
theorem B791981 : Blo 350755 791981 := bbase (se 3 (by rfl) ⟨148496, by rfl⟩ : syracuseStep 791981 = 296993) (by norm_num)
theorem B529853 : Blo 350755 529853 := bbase (se 3 (by rfl) ⟨99347, by rfl⟩ : syracuseStep 529853 = 198695) (by norm_num)
theorem B398785 : Blo 350755 398785 := bbase (se 2 (by rfl) ⟨149544, by rfl⟩ : syracuseStep 398785 = 299089) (by norm_num)
theorem B595397 : Blo 350755 595397 := bbase (se 4 (by rfl) ⟨55818, by rfl⟩ : syracuseStep 595397 = 111637) (by norm_num)
theorem B529877 : Blo 350755 529877 := bbase (se 7 (by rfl) ⟨6209, by rfl⟩ : syracuseStep 529877 = 12419) (by norm_num)
theorem B398821 : Blo 350755 398821 := bbase (se 4 (by rfl) ⟨37389, by rfl⟩ : syracuseStep 398821 = 74779) (by norm_num)
theorem B529901 : Blo 350755 529901 := bbase (se 3 (by rfl) ⟨99356, by rfl⟩ : syracuseStep 529901 = 198713) (by norm_num)
theorem B792053 : Blo 350755 792053 := bbase (se 5 (by rfl) ⟨37127, by rfl⟩ : syracuseStep 792053 = 74255) (by norm_num)
theorem B529925 : Blo 350755 529925 := bbase (se 4 (by rfl) ⟨49680, by rfl⟩ : syracuseStep 529925 = 99361) (by norm_num)
theorem B398857 : Blo 350755 398857 := bbase (se 2 (by rfl) ⟨149571, by rfl⟩ : syracuseStep 398857 = 299143) (by norm_num)
theorem B562709 : Blo 350755 562709 := bbase (se 6 (by rfl) ⟨13188, by rfl⟩ : syracuseStep 562709 = 26377) (by norm_num)
theorem B529949 : Blo 350755 529949 := bbase (se 3 (by rfl) ⟨99365, by rfl⟩ : syracuseStep 529949 = 198731) (by norm_num)
theorem B398893 : Blo 350755 398893 := bbase (se 3 (by rfl) ⟨74792, by rfl⟩ : syracuseStep 398893 = 149585) (by norm_num)
theorem B529973 : Blo 350755 529973 := bbase (se 5 (by rfl) ⟨24842, by rfl⟩ : syracuseStep 529973 = 49685) (by norm_num)
theorem B792125 : Blo 350755 792125 := bbase (se 3 (by rfl) ⟨148523, by rfl⟩ : syracuseStep 792125 = 297047) (by norm_num)
theorem B595525 : Blo 350755 595525 := bbase (se 4 (by rfl) ⟨55830, by rfl⟩ : syracuseStep 595525 = 111661) (by norm_num)
theorem B529997 : Blo 350755 529997 := bbase (se 3 (by rfl) ⟨99374, by rfl⟩ : syracuseStep 529997 = 198749) (by norm_num)
theorem B398929 : Blo 350755 398929 := bbase (se 2 (by rfl) ⟨149598, by rfl⟩ : syracuseStep 398929 = 299197) (by norm_num)
theorem B890453 : Blo 350755 890453 := bbase (se 8 (by rfl) ⟨5217, by rfl⟩ : syracuseStep 890453 = 10435) (by norm_num)
theorem B530021 : Blo 350755 530021 := bbase (se 4 (by rfl) ⟨49689, by rfl⟩ : syracuseStep 530021 = 99379) (by norm_num)
theorem B398965 : Blo 350755 398965 := bbase (se 5 (by rfl) ⟨18701, by rfl⟩ : syracuseStep 398965 = 37403) (by norm_num)
theorem B530045 : Blo 350755 530045 := bbase (se 3 (by rfl) ⟨99383, by rfl⟩ : syracuseStep 530045 = 198767) (by norm_num)
theorem B792197 : Blo 350755 792197 := bbase (se 4 (by rfl) ⟨74268, by rfl⟩ : syracuseStep 792197 = 148537) (by norm_num)
theorem B530069 : Blo 350755 530069 := bbase (se 6 (by rfl) ⟨12423, by rfl⟩ : syracuseStep 530069 = 24847) (by norm_num)
theorem B399001 : Blo 350755 399001 := bbase (se 2 (by rfl) ⟨149625, by rfl⟩ : syracuseStep 399001 = 299251) (by norm_num)
theorem B595613 : Blo 350755 595613 := bbase (se 3 (by rfl) ⟨111677, by rfl⟩ : syracuseStep 595613 = 223355) (by norm_num)
theorem B530093 : Blo 350755 530093 := bbase (se 3 (by rfl) ⟨99392, by rfl⟩ : syracuseStep 530093 = 198785) (by norm_num)
theorem B1185461 : Blo 350755 1185461 := bbase (se 5 (by rfl) ⟨55568, by rfl⟩ : syracuseStep 1185461 = 111137) (by norm_num)
theorem B399037 : Blo 350755 399037 := bbase (se 3 (by rfl) ⟨74819, by rfl⟩ : syracuseStep 399037 = 149639) (by norm_num)
theorem B530117 : Blo 350755 530117 := bbase (se 4 (by rfl) ⟨49698, by rfl⟩ : syracuseStep 530117 = 99397) (by norm_num)
theorem B792269 : Blo 350755 792269 := bbase (se 3 (by rfl) ⟨148550, by rfl⟩ : syracuseStep 792269 = 297101) (by norm_num)
theorem B530141 : Blo 350755 530141 := bbase (se 3 (by rfl) ⟨99401, by rfl⟩ : syracuseStep 530141 = 198803) (by norm_num)
theorem B399073 : Blo 350755 399073 := bbase (se 2 (by rfl) ⟨149652, by rfl⟩ : syracuseStep 399073 = 299305) (by norm_num)
theorem B530165 : Blo 350755 530165 := bbase (se 5 (by rfl) ⟨24851, by rfl⟩ : syracuseStep 530165 = 49703) (by norm_num)
theorem B530189 : Blo 350755 530189 := bbase (se 3 (by rfl) ⟨99410, by rfl⟩ : syracuseStep 530189 = 198821) (by norm_num)
theorem B792341 : Blo 350755 792341 := bbase (se 6 (by rfl) ⟨18570, by rfl⟩ : syracuseStep 792341 = 37141) (by norm_num)
theorem B595741 : Blo 350755 595741 := bbase (se 3 (by rfl) ⟨111701, by rfl⟩ : syracuseStep 595741 = 223403) (by norm_num)
theorem B530213 : Blo 350755 530213 := bbase (se 4 (by rfl) ⟨49707, by rfl⟩ : syracuseStep 530213 = 99415) (by norm_num)
theorem B530237 : Blo 350755 530237 := bbase (se 3 (by rfl) ⟨99419, by rfl⟩ : syracuseStep 530237 = 198839) (by norm_num)
theorem B530261 : Blo 350755 530261 := bbase (se 9 (by rfl) ⟨1553, by rfl⟩ : syracuseStep 530261 = 3107) (by norm_num)
theorem B792413 : Blo 350755 792413 := bbase (se 3 (by rfl) ⟨148577, by rfl⟩ : syracuseStep 792413 = 297155) (by norm_num)
theorem B530285 : Blo 350755 530285 := bbase (se 3 (by rfl) ⟨99428, by rfl⟩ : syracuseStep 530285 = 198857) (by norm_num)
theorem B595829 : Blo 350755 595829 := bbase (se 5 (by rfl) ⟨27929, by rfl⟩ : syracuseStep 595829 = 55859) (by norm_num)
theorem B530309 : Blo 350755 530309 := bbase (se 4 (by rfl) ⟨49716, by rfl⟩ : syracuseStep 530309 = 99433) (by norm_num)
theorem B530333 : Blo 350755 530333 := bbase (se 3 (by rfl) ⟨99437, by rfl⟩ : syracuseStep 530333 = 198875) (by norm_num)
theorem B792485 : Blo 350755 792485 := bbase (se 4 (by rfl) ⟨74295, by rfl⟩ : syracuseStep 792485 = 148591) (by norm_num)
theorem B890797 : Blo 350755 890797 := bbase (se 3 (by rfl) ⟨167024, by rfl⟩ : syracuseStep 890797 = 334049) (by norm_num)
theorem B530357 : Blo 350755 530357 := bbase (se 5 (by rfl) ⟨24860, by rfl⟩ : syracuseStep 530357 = 49721) (by norm_num)
theorem B530381 : Blo 350755 530381 := bbase (se 3 (by rfl) ⟨99446, by rfl⟩ : syracuseStep 530381 = 198893) (by norm_num)
theorem B759773 : Blo 350755 759773 := bbase (se 3 (by rfl) ⟨142457, by rfl⟩ : syracuseStep 759773 = 284915) (by norm_num)
theorem B366557 : Blo 350755 366557 := bbase (se 3 (by rfl) ⟨68729, by rfl⟩ : syracuseStep 366557 = 137459) (by norm_num)
theorem B530405 : Blo 350755 530405 := bbase (se 4 (by rfl) ⟨49725, by rfl⟩ : syracuseStep 530405 = 99451) (by norm_num)
theorem B792557 : Blo 350755 792557 := bbase (se 3 (by rfl) ⟨148604, by rfl⟩ : syracuseStep 792557 = 297209) (by norm_num)
theorem B595957 : Blo 350755 595957 := bbase (se 5 (by rfl) ⟨27935, by rfl⟩ : syracuseStep 595957 = 55871) (by norm_num)
theorem B530429 : Blo 350755 530429 := bbase (se 3 (by rfl) ⟨99455, by rfl⟩ : syracuseStep 530429 = 198911) (by norm_num)
theorem B563221 : Blo 350755 563221 := bbase (se 6 (by rfl) ⟨13200, by rfl⟩ : syracuseStep 563221 = 26401) (by norm_num)
theorem B530453 : Blo 350755 530453 := bbase (se 6 (by rfl) ⟨12432, by rfl⟩ : syracuseStep 530453 = 24865) (by norm_num)
theorem B890909 : Blo 350755 890909 := bbase (se 3 (by rfl) ⟨167045, by rfl⟩ : syracuseStep 890909 = 334091) (by norm_num)
theorem B530477 : Blo 350755 530477 := bbase (se 3 (by rfl) ⟨99464, by rfl⟩ : syracuseStep 530477 = 198929) (by norm_num)
theorem B792629 : Blo 350755 792629 := bbase (se 5 (by rfl) ⟨37154, by rfl⟩ : syracuseStep 792629 = 74309) (by norm_num)
theorem B1513525 : Blo 350755 1513525 := bbase (se 5 (by rfl) ⟨70946, by rfl⟩ : syracuseStep 1513525 = 141893) (by norm_num)
theorem B530501 : Blo 350755 530501 := bbase (se 4 (by rfl) ⟨49734, by rfl⟩ : syracuseStep 530501 = 99469) (by norm_num)
theorem B1513541 : Blo 350755 1513541 := bbase (se 4 (by rfl) ⟨141894, by rfl⟩ : syracuseStep 1513541 = 283789) (by norm_num)
theorem B596045 : Blo 350755 596045 := bbase (se 3 (by rfl) ⟨111758, by rfl⟩ : syracuseStep 596045 = 223517) (by norm_num)
theorem B530525 : Blo 350755 530525 := bbase (se 3 (by rfl) ⟨99473, by rfl⟩ : syracuseStep 530525 = 198947) (by norm_num)
theorem B1185893 : Blo 350755 1185893 := bbase (se 4 (by rfl) ⟨111177, by rfl⟩ : syracuseStep 1185893 = 222355) (by norm_num)
theorem B530549 : Blo 350755 530549 := bbase (se 5 (by rfl) ⟨24869, by rfl⟩ : syracuseStep 530549 = 49739) (by norm_num)
theorem B792701 : Blo 350755 792701 := bbase (se 3 (by rfl) ⟨148631, by rfl⟩ : syracuseStep 792701 = 297263) (by norm_num)
theorem B530573 : Blo 350755 530573 := bbase (se 3 (by rfl) ⟨99482, by rfl⟩ : syracuseStep 530573 = 198965) (by norm_num)
theorem B530597 : Blo 350755 530597 := bbase (se 4 (by rfl) ⟨49743, by rfl⟩ : syracuseStep 530597 = 99487) (by norm_num)
theorem B530621 : Blo 350755 530621 := bbase (se 3 (by rfl) ⟨99491, by rfl⟩ : syracuseStep 530621 = 198983) (by norm_num)
theorem B792773 : Blo 350755 792773 := bbase (se 4 (by rfl) ⟨74322, by rfl⟩ : syracuseStep 792773 = 148645) (by norm_num)
theorem B596173 : Blo 350755 596173 := bbase (se 3 (by rfl) ⟨111782, by rfl⟩ : syracuseStep 596173 = 223565) (by norm_num)
theorem B530645 : Blo 350755 530645 := bbase (se 7 (by rfl) ⟨6218, by rfl⟩ : syracuseStep 530645 = 12437) (by norm_num)
theorem B891101 : Blo 350755 891101 := bbase (se 3 (by rfl) ⟨167081, by rfl⟩ : syracuseStep 891101 = 334163) (by norm_num)
theorem B530669 : Blo 350755 530669 := bbase (se 3 (by rfl) ⟨99500, by rfl⟩ : syracuseStep 530669 = 199001) (by norm_num)
theorem B530693 : Blo 350755 530693 := bbase (se 4 (by rfl) ⟨49752, by rfl⟩ : syracuseStep 530693 = 99505) (by norm_num)
theorem B792845 : Blo 350755 792845 := bbase (se 3 (by rfl) ⟨148658, by rfl⟩ : syracuseStep 792845 = 297317) (by norm_num)
theorem B530717 : Blo 350755 530717 := bbase (se 3 (by rfl) ⟨99509, by rfl⟩ : syracuseStep 530717 = 199019) (by norm_num)
theorem B596261 : Blo 350755 596261 := bbase (se 4 (by rfl) ⟨55899, by rfl⟩ : syracuseStep 596261 = 111799) (by norm_num)
theorem B530741 : Blo 350755 530741 := bbase (se 5 (by rfl) ⟨24878, by rfl⟩ : syracuseStep 530741 = 49757) (by norm_num)
theorem B530765 : Blo 350755 530765 := bbase (se 3 (by rfl) ⟨99518, by rfl⟩ : syracuseStep 530765 = 199037) (by norm_num)
theorem B792917 : Blo 350755 792917 := bbase (se 10 (by rfl) ⟨1161, by rfl⟩ : syracuseStep 792917 = 2323) (by norm_num)
theorem B530789 : Blo 350755 530789 := bbase (se 4 (by rfl) ⟨49761, by rfl⟩ : syracuseStep 530789 = 99523) (by norm_num)
theorem B530813 : Blo 350755 530813 := bbase (se 3 (by rfl) ⟨99527, by rfl⟩ : syracuseStep 530813 = 199055) (by norm_num)
theorem B1776005 : Blo 350755 1776005 := bbase (se 4 (by rfl) ⟨166500, by rfl⟩ : syracuseStep 1776005 = 333001) (by norm_num)
theorem B530837 : Blo 350755 530837 := bbase (se 6 (by rfl) ⟨12441, by rfl⟩ : syracuseStep 530837 = 24883) (by norm_num)
theorem B792989 : Blo 350755 792989 := bbase (se 3 (by rfl) ⟨148685, by rfl⟩ : syracuseStep 792989 = 297371) (by norm_num)
theorem B596389 : Blo 350755 596389 := bbase (se 4 (by rfl) ⟨55911, by rfl⟩ : syracuseStep 596389 = 111823) (by norm_num)
theorem B530861 : Blo 350755 530861 := bbase (se 3 (by rfl) ⟨99536, by rfl⟩ : syracuseStep 530861 = 199073) (by norm_num)
theorem B530885 : Blo 350755 530885 := bbase (se 4 (by rfl) ⟨49770, by rfl⟩ : syracuseStep 530885 = 99541) (by norm_num)
theorem B530909 : Blo 350755 530909 := bbase (se 3 (by rfl) ⟨99545, by rfl⟩ : syracuseStep 530909 = 199091) (by norm_num)
theorem B793061 : Blo 350755 793061 := bbase (se 4 (by rfl) ⟨74349, by rfl⟩ : syracuseStep 793061 = 148699) (by norm_num)
theorem B530933 : Blo 350755 530933 := bbase (se 5 (by rfl) ⟨24887, by rfl⟩ : syracuseStep 530933 = 49775) (by norm_num)
theorem B596477 : Blo 350755 596477 := bbase (se 3 (by rfl) ⟨111839, by rfl⟩ : syracuseStep 596477 = 223679) (by norm_num)
theorem B530957 : Blo 350755 530957 := bbase (se 3 (by rfl) ⟨99554, by rfl⟩ : syracuseStep 530957 = 199109) (by norm_num)
theorem B1186325 : Blo 350755 1186325 := bbase (se 6 (by rfl) ⟨27804, by rfl⟩ : syracuseStep 1186325 = 55609) (by norm_num)
theorem B530981 : Blo 350755 530981 := bbase (se 4 (by rfl) ⟨49779, by rfl⟩ : syracuseStep 530981 = 99559) (by norm_num)
theorem B793133 : Blo 350755 793133 := bbase (se 3 (by rfl) ⟨148712, by rfl⟩ : syracuseStep 793133 = 297425) (by norm_num)
theorem B891445 : Blo 350755 891445 := bbase (se 5 (by rfl) ⟨41786, by rfl⟩ : syracuseStep 891445 = 83573) (by norm_num)
theorem B531005 : Blo 350755 531005 := bbase (se 3 (by rfl) ⟨99563, by rfl⟩ : syracuseStep 531005 = 199127) (by norm_num)
theorem B531029 : Blo 350755 531029 := bbase (se 8 (by rfl) ⟨3111, by rfl⟩ : syracuseStep 531029 = 6223) (by norm_num)
theorem B531053 : Blo 350755 531053 := bbase (se 3 (by rfl) ⟨99572, by rfl⟩ : syracuseStep 531053 = 199145) (by norm_num)
theorem B793205 : Blo 350755 793205 := bbase (se 5 (by rfl) ⟨37181, by rfl⟩ : syracuseStep 793205 = 74363) (by norm_num)
theorem B596605 : Blo 350755 596605 := bbase (se 3 (by rfl) ⟨111863, by rfl⟩ : syracuseStep 596605 = 223727) (by norm_num)
theorem B531077 : Blo 350755 531077 := bbase (se 4 (by rfl) ⟨49788, by rfl⟩ : syracuseStep 531077 = 99577) (by norm_num)
theorem B531101 : Blo 350755 531101 := bbase (se 3 (by rfl) ⟨99581, by rfl⟩ : syracuseStep 531101 = 199163) (by norm_num)
theorem B891557 : Blo 350755 891557 := bbase (se 4 (by rfl) ⟨83583, by rfl⟩ : syracuseStep 891557 = 167167) (by norm_num)
theorem B531125 : Blo 350755 531125 := bbase (se 5 (by rfl) ⟨24896, by rfl⟩ : syracuseStep 531125 = 49793) (by norm_num)
theorem B793277 : Blo 350755 793277 := bbase (se 3 (by rfl) ⟨148739, by rfl⟩ : syracuseStep 793277 = 297479) (by norm_num)
theorem B531149 : Blo 350755 531149 := bbase (se 3 (by rfl) ⟨99590, by rfl⟩ : syracuseStep 531149 = 199181) (by norm_num)
theorem B596693 : Blo 350755 596693 := bbase (se 7 (by rfl) ⟨6992, by rfl⟩ : syracuseStep 596693 = 13985) (by norm_num)
theorem B531173 : Blo 350755 531173 := bbase (se 4 (by rfl) ⟨49797, by rfl⟩ : syracuseStep 531173 = 99595) (by norm_num)
theorem B531197 : Blo 350755 531197 := bbase (se 3 (by rfl) ⟨99599, by rfl⟩ : syracuseStep 531197 = 199199) (by norm_num)
theorem B793349 : Blo 350755 793349 := bbase (se 4 (by rfl) ⟨74376, by rfl⟩ : syracuseStep 793349 = 148753) (by norm_num)
theorem B531221 : Blo 350755 531221 := bbase (se 6 (by rfl) ⟨12450, by rfl⟩ : syracuseStep 531221 = 24901) (by norm_num)
theorem B531245 : Blo 350755 531245 := bbase (se 3 (by rfl) ⟨99608, by rfl⟩ : syracuseStep 531245 = 199217) (by norm_num)
theorem B531269 : Blo 350755 531269 := bbase (se 4 (by rfl) ⟨49806, by rfl⟩ : syracuseStep 531269 = 99613) (by norm_num)
theorem B793421 : Blo 350755 793421 := bbase (se 3 (by rfl) ⟨148766, by rfl⟩ : syracuseStep 793421 = 297533) (by norm_num)
theorem B596821 : Blo 350755 596821 := bbase (se 9 (by rfl) ⟨1748, by rfl⟩ : syracuseStep 596821 = 3497) (by norm_num)
theorem B531293 : Blo 350755 531293 := bbase (se 3 (by rfl) ⟨99617, by rfl⟩ : syracuseStep 531293 = 199235) (by norm_num)
theorem B891749 : Blo 350755 891749 := bbase (se 4 (by rfl) ⟨83601, by rfl⟩ : syracuseStep 891749 = 167203) (by norm_num)
theorem B531317 : Blo 350755 531317 := bbase (se 5 (by rfl) ⟨24905, by rfl⟩ : syracuseStep 531317 = 49811) (by norm_num)
theorem B531341 : Blo 350755 531341 := bbase (se 3 (by rfl) ⟨99626, by rfl⟩ : syracuseStep 531341 = 199253) (by norm_num)
theorem B793493 : Blo 350755 793493 := bbase (se 6 (by rfl) ⟨18597, by rfl⟩ : syracuseStep 793493 = 37195) (by norm_num)
theorem B1809317 : Blo 350755 1809317 := bbase (se 4 (by rfl) ⟨169623, by rfl⟩ : syracuseStep 1809317 = 339247) (by norm_num)
theorem B531365 : Blo 350755 531365 := bbase (se 4 (by rfl) ⟨49815, by rfl⟩ : syracuseStep 531365 = 99631) (by norm_num)
theorem B596909 : Blo 350755 596909 := bbase (se 3 (by rfl) ⟨111920, by rfl⟩ : syracuseStep 596909 = 223841) (by norm_num)
theorem B531389 : Blo 350755 531389 := bbase (se 3 (by rfl) ⟨99635, by rfl⟩ : syracuseStep 531389 = 199271) (by norm_num)
theorem B1186757 : Blo 350755 1186757 := bbase (se 4 (by rfl) ⟨111258, by rfl⟩ : syracuseStep 1186757 = 222517) (by norm_num)
theorem B531413 : Blo 350755 531413 := bbase (se 7 (by rfl) ⟨6227, by rfl⟩ : syracuseStep 531413 = 12455) (by norm_num)
theorem B793565 : Blo 350755 793565 := bbase (se 3 (by rfl) ⟨148793, by rfl⟩ : syracuseStep 793565 = 297587) (by norm_num)
theorem B531437 : Blo 350755 531437 := bbase (se 3 (by rfl) ⟨99644, by rfl⟩ : syracuseStep 531437 = 199289) (by norm_num)
theorem B564221 : Blo 350755 564221 := bbase (se 3 (by rfl) ⟨105791, by rfl⟩ : syracuseStep 564221 = 211583) (by norm_num)
theorem B531461 : Blo 350755 531461 := bbase (se 4 (by rfl) ⟨49824, by rfl⟩ : syracuseStep 531461 = 99649) (by norm_num)
theorem B531485 : Blo 350755 531485 := bbase (se 3 (by rfl) ⟨99653, by rfl⟩ : syracuseStep 531485 = 199307) (by norm_num)
theorem B793637 : Blo 350755 793637 := bbase (se 4 (by rfl) ⟨74403, by rfl⟩ : syracuseStep 793637 = 148807) (by norm_num)
theorem B597037 : Blo 350755 597037 := bbase (se 3 (by rfl) ⟨111944, by rfl⟩ : syracuseStep 597037 = 223889) (by norm_num)
theorem B531509 : Blo 350755 531509 := bbase (se 5 (by rfl) ⟨24914, by rfl⟩ : syracuseStep 531509 = 49829) (by norm_num)
theorem B531533 : Blo 350755 531533 := bbase (se 3 (by rfl) ⟨99662, by rfl⟩ : syracuseStep 531533 = 199325) (by norm_num)
theorem B531557 : Blo 350755 531557 := bbase (se 4 (by rfl) ⟨49833, by rfl⟩ : syracuseStep 531557 = 99667) (by norm_num)
theorem B793709 : Blo 350755 793709 := bbase (se 3 (by rfl) ⟨148820, by rfl⟩ : syracuseStep 793709 = 297641) (by norm_num)
theorem B1055861 : Blo 350755 1055861 := bbase (se 5 (by rfl) ⟨49493, by rfl⟩ : syracuseStep 1055861 = 98987) (by norm_num)
theorem B564349 : Blo 350755 564349 := bbase (se 3 (by rfl) ⟨105815, by rfl⟩ : syracuseStep 564349 = 211631) (by norm_num)
theorem B531581 : Blo 350755 531581 := bbase (se 3 (by rfl) ⟨99671, by rfl⟩ : syracuseStep 531581 = 199343) (by norm_num)
theorem B597125 : Blo 350755 597125 := bbase (se 4 (by rfl) ⟨55980, by rfl⟩ : syracuseStep 597125 = 111961) (by norm_num)
theorem B531605 : Blo 350755 531605 := bbase (se 6 (by rfl) ⟨12459, by rfl⟩ : syracuseStep 531605 = 24919) (by norm_num)
theorem B531629 : Blo 350755 531629 := bbase (se 3 (by rfl) ⟨99680, by rfl⟩ : syracuseStep 531629 = 199361) (by norm_num)
theorem B793781 : Blo 350755 793781 := bbase (se 5 (by rfl) ⟨37208, by rfl⟩ : syracuseStep 793781 = 74417) (by norm_num)
theorem B564413 : Blo 350755 564413 := bbase (se 3 (by rfl) ⟨105827, by rfl⟩ : syracuseStep 564413 = 211655) (by norm_num)
theorem B892093 : Blo 350755 892093 := bbase (se 3 (by rfl) ⟨167267, by rfl⟩ : syracuseStep 892093 = 334535) (by norm_num)
theorem B531653 : Blo 350755 531653 := bbase (se 4 (by rfl) ⟨49842, by rfl⟩ : syracuseStep 531653 = 99685) (by norm_num)
theorem B531677 : Blo 350755 531677 := bbase (se 3 (by rfl) ⟨99689, by rfl⟩ : syracuseStep 531677 = 199379) (by norm_num)
theorem B531701 : Blo 350755 531701 := bbase (se 5 (by rfl) ⟨24923, by rfl⟩ : syracuseStep 531701 = 49847) (by norm_num)
theorem B793853 : Blo 350755 793853 := bbase (se 3 (by rfl) ⟨148847, by rfl⟩ : syracuseStep 793853 = 297695) (by norm_num)
theorem B597253 : Blo 350755 597253 := bbase (se 4 (by rfl) ⟨55992, by rfl⟩ : syracuseStep 597253 = 111985) (by norm_num)
theorem B531725 : Blo 350755 531725 := bbase (se 3 (by rfl) ⟨99698, by rfl⟩ : syracuseStep 531725 = 199397) (by norm_num)
theorem B531749 : Blo 350755 531749 := bbase (se 4 (by rfl) ⟨49851, by rfl⟩ : syracuseStep 531749 = 99703) (by norm_num)
theorem B892205 : Blo 350755 892205 := bbase (se 3 (by rfl) ⟨167288, by rfl⟩ : syracuseStep 892205 = 334577) (by norm_num)
theorem B531773 : Blo 350755 531773 := bbase (se 3 (by rfl) ⟨99707, by rfl⟩ : syracuseStep 531773 = 199415) (by norm_num)
theorem B793925 : Blo 350755 793925 := bbase (se 4 (by rfl) ⟨74430, by rfl⟩ : syracuseStep 793925 = 148861) (by norm_num)
theorem B531797 : Blo 350755 531797 := bbase (se 11 (by rfl) ⟨389, by rfl⟩ : syracuseStep 531797 = 779) (by norm_num)
theorem B597341 : Blo 350755 597341 := bbase (se 3 (by rfl) ⟨112001, by rfl⟩ : syracuseStep 597341 = 224003) (by norm_num)
theorem B531821 : Blo 350755 531821 := bbase (se 3 (by rfl) ⟨99716, by rfl⟩ : syracuseStep 531821 = 199433) (by norm_num)
theorem B1187189 : Blo 350755 1187189 := bbase (se 5 (by rfl) ⟨55649, by rfl⟩ : syracuseStep 1187189 = 111299) (by norm_num)
theorem B531845 : Blo 350755 531845 := bbase (se 4 (by rfl) ⟨49860, by rfl⟩ : syracuseStep 531845 = 99721) (by norm_num)
theorem B793997 : Blo 350755 793997 := bbase (se 3 (by rfl) ⟨148874, by rfl⟩ : syracuseStep 793997 = 297749) (by norm_num)
theorem B531869 : Blo 350755 531869 := bbase (se 3 (by rfl) ⟨99725, by rfl⟩ : syracuseStep 531869 = 199451) (by norm_num)
theorem B531893 : Blo 350755 531893 := bbase (se 5 (by rfl) ⟨24932, by rfl⟩ : syracuseStep 531893 = 49865) (by norm_num)
theorem B531917 : Blo 350755 531917 := bbase (se 3 (by rfl) ⟨99734, by rfl⟩ : syracuseStep 531917 = 199469) (by norm_num)
theorem B794069 : Blo 350755 794069 := bbase (se 7 (by rfl) ⟨9305, by rfl⟩ : syracuseStep 794069 = 18611) (by norm_num)
theorem B597469 : Blo 350755 597469 := bbase (se 3 (by rfl) ⟨112025, by rfl⟩ : syracuseStep 597469 = 224051) (by norm_num)
theorem B531941 : Blo 350755 531941 := bbase (se 4 (by rfl) ⟨49869, by rfl⟩ : syracuseStep 531941 = 99739) (by norm_num)
theorem B892397 : Blo 350755 892397 := bbase (se 3 (by rfl) ⟨167324, by rfl⟩ : syracuseStep 892397 = 334649) (by norm_num)
theorem B531965 : Blo 350755 531965 := bbase (se 3 (by rfl) ⟨99743, by rfl⟩ : syracuseStep 531965 = 199487) (by norm_num)
theorem B531989 : Blo 350755 531989 := bbase (se 6 (by rfl) ⟨12468, by rfl⟩ : syracuseStep 531989 = 24937) (by norm_num)
theorem B794141 : Blo 350755 794141 := bbase (se 3 (by rfl) ⟨148901, by rfl⟩ : syracuseStep 794141 = 297803) (by norm_num)
theorem B532013 : Blo 350755 532013 := bbase (se 3 (by rfl) ⟨99752, by rfl⟩ : syracuseStep 532013 = 199505) (by norm_num)
theorem B597557 : Blo 350755 597557 := bbase (se 5 (by rfl) ⟨28010, by rfl⟩ : syracuseStep 597557 = 56021) (by norm_num)
theorem B532037 : Blo 350755 532037 := bbase (se 4 (by rfl) ⟨49878, by rfl⟩ : syracuseStep 532037 = 99757) (by norm_num)
theorem B532061 : Blo 350755 532061 := bbase (se 3 (by rfl) ⟨99761, by rfl⟩ : syracuseStep 532061 = 199523) (by norm_num)
theorem B794213 : Blo 350755 794213 := bbase (se 4 (by rfl) ⟨74457, by rfl⟩ : syracuseStep 794213 = 148915) (by norm_num)
theorem B532085 : Blo 350755 532085 := bbase (se 5 (by rfl) ⟨24941, by rfl⟩ : syracuseStep 532085 = 49883) (by norm_num)
theorem B532109 : Blo 350755 532109 := bbase (se 3 (by rfl) ⟨99770, by rfl⟩ : syracuseStep 532109 = 199541) (by norm_num)
theorem B1777301 : Blo 350755 1777301 := bbase (se 6 (by rfl) ⟨41655, by rfl⟩ : syracuseStep 1777301 = 83311) (by norm_num)
theorem B532133 : Blo 350755 532133 := bbase (se 4 (by rfl) ⟨49887, by rfl⟩ : syracuseStep 532133 = 99775) (by norm_num)
theorem B794285 : Blo 350755 794285 := bbase (se 3 (by rfl) ⟨148928, by rfl⟩ : syracuseStep 794285 = 297857) (by norm_num)
theorem B597685 : Blo 350755 597685 := bbase (se 5 (by rfl) ⟨28016, by rfl⟩ : syracuseStep 597685 = 56033) (by norm_num)
theorem B794357 : Blo 350755 794357 := bbase (se 5 (by rfl) ⟨37235, by rfl⟩ : syracuseStep 794357 = 74471) (by norm_num)
theorem B597773 : Blo 350755 597773 := bbase (se 3 (by rfl) ⟨112082, by rfl⟩ : syracuseStep 597773 = 224165) (by norm_num)
theorem B1187621 : Blo 350755 1187621 := bbase (se 4 (by rfl) ⟨111339, by rfl⟩ : syracuseStep 1187621 = 222679) (by norm_num)
theorem B794429 : Blo 350755 794429 := bbase (se 3 (by rfl) ⟨148955, by rfl⟩ : syracuseStep 794429 = 297911) (by norm_num)
theorem B892741 : Blo 350755 892741 := bbase (se 4 (by rfl) ⟨83694, by rfl⟩ : syracuseStep 892741 = 167389) (by norm_num)
theorem B401257 : Blo 350755 401257 := bbase (se 2 (by rfl) ⟨150471, by rfl⟩ : syracuseStep 401257 = 300943) (by norm_num)
theorem B794501 : Blo 350755 794501 := bbase (se 4 (by rfl) ⟨74484, by rfl⟩ : syracuseStep 794501 = 148969) (by norm_num)
theorem B597901 : Blo 350755 597901 := bbase (se 3 (by rfl) ⟨112106, by rfl⟩ : syracuseStep 597901 = 224213) (by norm_num)
theorem B1089445 : Blo 350755 1089445 := bbase (se 4 (by rfl) ⟨102135, by rfl⟩ : syracuseStep 1089445 = 204271) (by norm_num)
theorem B892853 : Blo 350755 892853 := bbase (se 5 (by rfl) ⟨41852, by rfl⟩ : syracuseStep 892853 = 83705) (by norm_num)
theorem B794573 : Blo 350755 794573 := bbase (se 3 (by rfl) ⟨148982, by rfl⟩ : syracuseStep 794573 = 297965) (by norm_num)
theorem B597989 : Blo 350755 597989 := bbase (se 4 (by rfl) ⟨56061, by rfl⟩ : syracuseStep 597989 = 112123) (by norm_num)
theorem B794645 : Blo 350755 794645 := bbase (se 6 (by rfl) ⟨18624, by rfl⟩ : syracuseStep 794645 = 37249) (by norm_num)
theorem B794717 : Blo 350755 794717 := bbase (se 3 (by rfl) ⟨149009, by rfl⟩ : syracuseStep 794717 = 298019) (by norm_num)
theorem B598117 : Blo 350755 598117 := bbase (se 4 (by rfl) ⟨56073, by rfl⟩ : syracuseStep 598117 = 112147) (by norm_num)
theorem B893045 : Blo 350755 893045 := bbase (se 5 (by rfl) ⟨41861, by rfl⟩ : syracuseStep 893045 = 83723) (by norm_num)
theorem B499861 : Blo 350755 499861 := bbase (se 6 (by rfl) ⟨11715, by rfl⟩ : syracuseStep 499861 = 23431) (by norm_num)
theorem B794789 : Blo 350755 794789 := bbase (se 4 (by rfl) ⟨74511, by rfl⟩ : syracuseStep 794789 = 149023) (by norm_num)
theorem B598205 : Blo 350755 598205 := bbase (se 3 (by rfl) ⟨112163, by rfl⟩ : syracuseStep 598205 = 224327) (by norm_num)
theorem B1188053 : Blo 350755 1188053 := bbase (se 7 (by rfl) ⟨13922, by rfl⟩ : syracuseStep 1188053 = 27845) (by norm_num)
theorem B794861 : Blo 350755 794861 := bbase (se 3 (by rfl) ⟨149036, by rfl⟩ : syracuseStep 794861 = 298073) (by norm_num)
theorem B794933 : Blo 350755 794933 := bbase (se 5 (by rfl) ⟨37262, by rfl⟩ : syracuseStep 794933 = 74525) (by norm_num)
theorem B598333 : Blo 350755 598333 := bbase (se 3 (by rfl) ⟨112187, by rfl⟩ : syracuseStep 598333 = 224375) (by norm_num)
theorem B795005 : Blo 350755 795005 := bbase (se 3 (by rfl) ⟨149063, by rfl⟩ : syracuseStep 795005 = 298127) (by norm_num)
theorem B598421 : Blo 350755 598421 := bbase (se 6 (by rfl) ⟨14025, by rfl⟩ : syracuseStep 598421 = 28051) (by norm_num)
theorem B795077 : Blo 350755 795077 := bbase (se 4 (by rfl) ⟨74538, by rfl⟩ : syracuseStep 795077 = 149077) (by norm_num)
theorem B893389 : Blo 350755 893389 := bbase (se 3 (by rfl) ⟨167510, by rfl⟩ : syracuseStep 893389 = 335021) (by norm_num)
theorem B500197 : Blo 350755 500197 := bbase (se 4 (by rfl) ⟨46893, by rfl⟩ : syracuseStep 500197 = 93787) (by norm_num)
theorem B565733 : Blo 350755 565733 := bbase (se 4 (by rfl) ⟨53037, by rfl⟩ : syracuseStep 565733 = 106075) (by norm_num)
theorem B795149 : Blo 350755 795149 := bbase (se 3 (by rfl) ⟨149090, by rfl⟩ : syracuseStep 795149 = 298181) (by norm_num)
theorem B598549 : Blo 350755 598549 := bbase (se 6 (by rfl) ⟨14028, by rfl⟩ : syracuseStep 598549 = 28057) (by norm_num)
theorem B893501 : Blo 350755 893501 := bbase (se 3 (by rfl) ⟨167531, by rfl⟩ : syracuseStep 893501 = 335063) (by norm_num)
theorem B795221 : Blo 350755 795221 := bbase (se 8 (by rfl) ⟨4659, by rfl⟩ : syracuseStep 795221 = 9319) (by norm_num)
theorem B565861 : Blo 350755 565861 := bbase (se 4 (by rfl) ⟨53049, by rfl⟩ : syracuseStep 565861 = 106099) (by norm_num)
theorem B598637 : Blo 350755 598637 := bbase (se 3 (by rfl) ⟨112244, by rfl⟩ : syracuseStep 598637 = 224489) (by norm_num)
theorem B1188485 : Blo 350755 1188485 := bbase (se 4 (by rfl) ⟨111420, by rfl⟩ : syracuseStep 1188485 = 222841) (by norm_num)
theorem B795293 : Blo 350755 795293 := bbase (se 3 (by rfl) ⟨149117, by rfl⟩ : syracuseStep 795293 = 298235) (by norm_num)
theorem B500413 : Blo 350755 500413 := bbase (se 3 (by rfl) ⟨93827, by rfl⟩ : syracuseStep 500413 = 187655) (by norm_num)
theorem B795365 : Blo 350755 795365 := bbase (se 4 (by rfl) ⟨74565, by rfl⟩ : syracuseStep 795365 = 149131) (by norm_num)
theorem B2138869 : Blo 350755 2138869 := bbase (se 5 (by rfl) ⟨100259, by rfl⟩ : syracuseStep 2138869 = 200519) (by norm_num)
theorem B893693 : Blo 350755 893693 := bbase (se 3 (by rfl) ⟨167567, by rfl⟩ : syracuseStep 893693 = 335135) (by norm_num)
theorem B795437 : Blo 350755 795437 := bbase (se 3 (by rfl) ⟨149144, by rfl⟩ : syracuseStep 795437 = 298289) (by norm_num)
theorem B795509 : Blo 350755 795509 := bbase (se 5 (by rfl) ⟨37289, by rfl⟩ : syracuseStep 795509 = 74579) (by norm_num)
theorem B1778597 : Blo 350755 1778597 := bbase (se 4 (by rfl) ⟨166743, by rfl⟩ : syracuseStep 1778597 = 333487) (by norm_num)
theorem B795581 : Blo 350755 795581 := bbase (se 3 (by rfl) ⟨149171, by rfl⟩ : syracuseStep 795581 = 298343) (by norm_num)
theorem B795653 : Blo 350755 795653 := bbase (se 4 (by rfl) ⟨74592, by rfl⟩ : syracuseStep 795653 = 149185) (by norm_num)
theorem B500789 : Blo 350755 500789 := bbase (se 5 (by rfl) ⟨23474, by rfl⟩ : syracuseStep 500789 = 46949) (by norm_num)
theorem B1188917 : Blo 350755 1188917 := bbase (se 5 (by rfl) ⟨55730, by rfl⟩ : syracuseStep 1188917 = 111461) (by norm_num)
theorem B795725 : Blo 350755 795725 := bbase (se 3 (by rfl) ⟨149198, by rfl⟩ : syracuseStep 795725 = 298397) (by norm_num)
theorem B894037 : Blo 350755 894037 := bbase (se 8 (by rfl) ⟨5238, by rfl⟩ : syracuseStep 894037 = 10477) (by norm_num)
theorem B402553 : Blo 350755 402553 := bbase (se 2 (by rfl) ⟨150957, by rfl⟩ : syracuseStep 402553 = 301915) (by norm_num)
theorem B795797 : Blo 350755 795797 := bbase (se 6 (by rfl) ⟨18651, by rfl⟩ : syracuseStep 795797 = 37303) (by norm_num)
theorem B894149 : Blo 350755 894149 := bbase (se 4 (by rfl) ⟨83826, by rfl⟩ : syracuseStep 894149 = 167653) (by norm_num)
theorem B828613 : Blo 350755 828613 := bbase (se 4 (by rfl) ⟨77682, by rfl⟩ : syracuseStep 828613 = 155365) (by norm_num)
theorem B795869 : Blo 350755 795869 := bbase (se 3 (by rfl) ⟨149225, by rfl⟩ : syracuseStep 795869 = 298451) (by norm_num)
theorem B795941 : Blo 350755 795941 := bbase (se 4 (by rfl) ⟨74619, by rfl⟩ : syracuseStep 795941 = 149239) (by norm_num)
theorem B2663765 : Blo 350755 2663765 := bbase (se 12 (by rfl) ⟨975, by rfl⟩ : syracuseStep 2663765 = 1951) (by norm_num)
theorem B796013 : Blo 350755 796013 := bbase (se 3 (by rfl) ⟨149252, by rfl⟩ : syracuseStep 796013 = 298505) (by norm_num)
theorem B894341 : Blo 350755 894341 := bbase (se 4 (by rfl) ⟨83844, by rfl⟩ : syracuseStep 894341 = 167689) (by norm_num)
theorem B566669 : Blo 350755 566669 := bbase (se 3 (by rfl) ⟨106250, by rfl⟩ : syracuseStep 566669 = 212501) (by norm_num)
theorem B796085 : Blo 350755 796085 := bbase (se 5 (by rfl) ⟨37316, by rfl⟩ : syracuseStep 796085 = 74633) (by norm_num)
theorem B4498901 : Blo 350755 4498901 := bbase (se 7 (by rfl) ⟨52721, by rfl⟩ : syracuseStep 4498901 = 105443) (by norm_num)
theorem B533989 : Blo 350755 533989 := bbase (se 4 (by rfl) ⟨50061, by rfl⟩ : syracuseStep 533989 = 100123) (by norm_num)
theorem B1189349 : Blo 350755 1189349 := bbase (se 4 (by rfl) ⟨111501, by rfl⟩ : syracuseStep 1189349 = 223003) (by norm_num)
theorem B796157 : Blo 350755 796157 := bbase (se 3 (by rfl) ⟨149279, by rfl⟩ : syracuseStep 796157 = 298559) (by norm_num)
theorem B796229 : Blo 350755 796229 := bbase (se 4 (by rfl) ⟨74646, by rfl⟩ : syracuseStep 796229 = 149293) (by norm_num)
theorem B796301 : Blo 350755 796301 := bbase (se 3 (by rfl) ⟨149306, by rfl⟩ : syracuseStep 796301 = 298613) (by norm_num)
theorem B566957 : Blo 350755 566957 := bbase (se 3 (by rfl) ⟨106304, by rfl⟩ : syracuseStep 566957 = 212609) (by norm_num)
theorem B796373 : Blo 350755 796373 := bbase (se 7 (by rfl) ⟨9332, by rfl⟩ : syracuseStep 796373 = 18665) (by norm_num)
theorem B894685 : Blo 350755 894685 := bbase (se 3 (by rfl) ⟨167753, by rfl⟩ : syracuseStep 894685 = 335507) (by norm_num)
theorem B534293 : Blo 350755 534293 := bbase (se 6 (by rfl) ⟨12522, by rfl⟩ : syracuseStep 534293 = 25045) (by norm_num)
theorem B796445 : Blo 350755 796445 := bbase (se 3 (by rfl) ⟨149333, by rfl⟩ : syracuseStep 796445 = 298667) (by norm_num)
theorem B894797 : Blo 350755 894797 := bbase (se 3 (by rfl) ⟨167774, by rfl⟩ : syracuseStep 894797 = 335549) (by norm_num)
theorem B796517 : Blo 350755 796517 := bbase (se 4 (by rfl) ⟨74673, by rfl⟩ : syracuseStep 796517 = 149347) (by norm_num)
theorem B632701 : Blo 350755 632701 := bbase (se 3 (by rfl) ⟨118631, by rfl⟩ : syracuseStep 632701 = 237263) (by norm_num)
theorem B1189781 : Blo 350755 1189781 := bbase (se 6 (by rfl) ⟨27885, by rfl⟩ : syracuseStep 1189781 = 55771) (by norm_num)
theorem B796589 : Blo 350755 796589 := bbase (se 3 (by rfl) ⟨149360, by rfl⟩ : syracuseStep 796589 = 298721) (by norm_num)
theorem B796661 : Blo 350755 796661 := bbase (se 5 (by rfl) ⟨37343, by rfl⟩ : syracuseStep 796661 = 74687) (by norm_num)
theorem B894989 : Blo 350755 894989 := bbase (se 3 (by rfl) ⟨167810, by rfl⟩ : syracuseStep 894989 = 335621) (by norm_num)
theorem B796733 : Blo 350755 796733 := bbase (se 3 (by rfl) ⟨149387, by rfl⟩ : syracuseStep 796733 = 298775) (by norm_num)
theorem B567373 : Blo 350755 567373 := bbase (se 3 (by rfl) ⟨106382, by rfl⟩ : syracuseStep 567373 = 212765) (by norm_num)
theorem B5711957 : Blo 350755 5711957 := bbase (se 8 (by rfl) ⟨33468, by rfl⟩ : syracuseStep 5711957 = 66937) (by norm_num)
theorem B403553 : Blo 350755 403553 := bbase (se 2 (by rfl) ⟨151332, by rfl⟩ : syracuseStep 403553 = 302665) (by norm_num)
theorem B796805 : Blo 350755 796805 := bbase (se 4 (by rfl) ⟨74700, by rfl⟩ : syracuseStep 796805 = 149401) (by norm_num)
theorem B1779893 : Blo 350755 1779893 := bbase (se 5 (by rfl) ⟨83432, by rfl⟩ : syracuseStep 1779893 = 166865) (by norm_num)
theorem B796877 : Blo 350755 796877 := bbase (se 3 (by rfl) ⟨149414, by rfl⟩ : syracuseStep 796877 = 298829) (by norm_num)
theorem B1124597 : Blo 350755 1124597 := bbase (se 5 (by rfl) ⟨52715, by rfl⟩ : syracuseStep 1124597 = 105431) (by norm_num)
theorem B796949 : Blo 350755 796949 := bbase (se 6 (by rfl) ⟨18678, by rfl⟩ : syracuseStep 796949 = 37357) (by norm_num)
theorem B1190213 : Blo 350755 1190213 := bbase (se 4 (by rfl) ⟨111582, by rfl⟩ : syracuseStep 1190213 = 223165) (by norm_num)
theorem B797021 : Blo 350755 797021 := bbase (se 3 (by rfl) ⟨149441, by rfl⟩ : syracuseStep 797021 = 298883) (by norm_num)
theorem B665957 : Blo 350755 665957 := bbase (se 4 (by rfl) ⟨62433, by rfl⟩ : syracuseStep 665957 = 124867) (by norm_num)
theorem B895333 : Blo 350755 895333 := bbase (se 4 (by rfl) ⟨83937, by rfl⟩ : syracuseStep 895333 = 167875) (by norm_num)
theorem B797093 : Blo 350755 797093 := bbase (se 4 (by rfl) ⟨74727, by rfl⟩ : syracuseStep 797093 = 149455) (by norm_num)
theorem B502213 : Blo 350755 502213 := bbase (se 4 (by rfl) ⟨47082, by rfl⟩ : syracuseStep 502213 = 94165) (by norm_num)
theorem B895445 : Blo 350755 895445 := bbase (se 7 (by rfl) ⟨10493, by rfl⟩ : syracuseStep 895445 = 20987) (by norm_num)
theorem B797165 : Blo 350755 797165 := bbase (se 3 (by rfl) ⟨149468, by rfl⟩ : syracuseStep 797165 = 298937) (by norm_num)
theorem B797237 : Blo 350755 797237 := bbase (se 5 (by rfl) ⟨37370, by rfl⟩ : syracuseStep 797237 = 74741) (by norm_num)
theorem B2009717 : Blo 350755 2009717 := bbase (se 5 (by rfl) ⟨94205, by rfl⟩ : syracuseStep 2009717 = 188411) (by norm_num)
theorem B797309 : Blo 350755 797309 := bbase (se 3 (by rfl) ⟨149495, by rfl⟩ : syracuseStep 797309 = 298991) (by norm_num)
theorem B666245 : Blo 350755 666245 := bbase (se 4 (by rfl) ⟨62460, by rfl⟩ : syracuseStep 666245 = 124921) (by norm_num)
theorem B895637 : Blo 350755 895637 := bbase (se 6 (by rfl) ⟨20991, by rfl⟩ : syracuseStep 895637 = 41983) (by norm_num)
theorem B633509 : Blo 350755 633509 := bbase (se 4 (by rfl) ⟨59391, by rfl⟩ : syracuseStep 633509 = 118783) (by norm_num)
theorem B797381 : Blo 350755 797381 := bbase (se 4 (by rfl) ⟨74754, by rfl⟩ : syracuseStep 797381 = 149509) (by norm_num)
theorem B1190645 : Blo 350755 1190645 := bbase (se 5 (by rfl) ⟨55811, by rfl⟩ : syracuseStep 1190645 = 111623) (by norm_num)
theorem B797453 : Blo 350755 797453 := bbase (se 3 (by rfl) ⟨149522, by rfl⟩ : syracuseStep 797453 = 299045) (by norm_num)
theorem B666397 : Blo 350755 666397 := bbase (se 3 (by rfl) ⟨124949, by rfl⟩ : syracuseStep 666397 = 249899) (by norm_num)
theorem B797525 : Blo 350755 797525 := bbase (se 9 (by rfl) ⟨2336, by rfl⟩ : syracuseStep 797525 = 4673) (by norm_num)
theorem B797597 : Blo 350755 797597 := bbase (se 3 (by rfl) ⟨149549, by rfl⟩ : syracuseStep 797597 = 299099) (by norm_num)
theorem B797669 : Blo 350755 797669 := bbase (se 4 (by rfl) ⟨74781, by rfl⟩ : syracuseStep 797669 = 149563) (by norm_num)
theorem B895981 : Blo 350755 895981 := bbase (se 3 (by rfl) ⟨167996, by rfl⟩ : syracuseStep 895981 = 335993) (by norm_num)
theorem B502805 : Blo 350755 502805 := bbase (se 6 (by rfl) ⟨11784, by rfl⟩ : syracuseStep 502805 = 23569) (by norm_num)
theorem B797741 : Blo 350755 797741 := bbase (se 3 (by rfl) ⟨149576, by rfl⟩ : syracuseStep 797741 = 299153) (by norm_num)
theorem B666701 : Blo 350755 666701 := bbase (se 3 (by rfl) ⟨125006, by rfl⟩ : syracuseStep 666701 = 250013) (by norm_num)
theorem B535637 : Blo 350755 535637 := bbase (se 8 (by rfl) ⟨3138, by rfl⟩ : syracuseStep 535637 = 6277) (by norm_num)
theorem B896093 : Blo 350755 896093 := bbase (se 3 (by rfl) ⟨168017, by rfl⟩ : syracuseStep 896093 = 336035) (by norm_num)
theorem B502885 : Blo 350755 502885 := bbase (se 4 (by rfl) ⟨47145, by rfl⟩ : syracuseStep 502885 = 94291) (by norm_num)
theorem B797813 : Blo 350755 797813 := bbase (se 5 (by rfl) ⟨37397, by rfl⟩ : syracuseStep 797813 = 74795) (by norm_num)
theorem B601229 : Blo 350755 601229 := bbase (se 3 (by rfl) ⟨112730, by rfl⟩ : syracuseStep 601229 = 225461) (by norm_num)
theorem B1191077 : Blo 350755 1191077 := bbase (se 4 (by rfl) ⟨111663, by rfl⟩ : syracuseStep 1191077 = 223327) (by norm_num)
theorem B797885 : Blo 350755 797885 := bbase (se 3 (by rfl) ⟨149603, by rfl⟩ : syracuseStep 797885 = 299207) (by norm_num)
theorem B503005 : Blo 350755 503005 := bbase (se 3 (by rfl) ⟨94313, by rfl⟩ : syracuseStep 503005 = 188627) (by norm_num)
theorem B797957 : Blo 350755 797957 := bbase (se 4 (by rfl) ⟨74808, by rfl⟩ : syracuseStep 797957 = 149617) (by norm_num)
theorem B535837 : Blo 350755 535837 := bbase (se 3 (by rfl) ⟨100469, by rfl⟩ : syracuseStep 535837 = 200939) (by norm_num)
theorem B896285 : Blo 350755 896285 := bbase (se 3 (by rfl) ⟨168053, by rfl⟩ : syracuseStep 896285 = 336107) (by norm_num)
theorem B503101 : Blo 350755 503101 := bbase (se 3 (by rfl) ⟨94331, by rfl⟩ : syracuseStep 503101 = 188663) (by norm_num)
theorem B798029 : Blo 350755 798029 := bbase (se 3 (by rfl) ⟨149630, by rfl⟩ : syracuseStep 798029 = 299261) (by norm_num)
theorem B3026261 : Blo 350755 3026261 := bbase (se 11 (by rfl) ⟨2216, by rfl⟩ : syracuseStep 3026261 = 4433) (by norm_num)
theorem B798101 : Blo 350755 798101 := bbase (se 6 (by rfl) ⟨18705, by rfl⟩ : syracuseStep 798101 = 37411) (by norm_num)
theorem B1781189 : Blo 350755 1781189 := bbase (se 4 (by rfl) ⟨166986, by rfl⟩ : syracuseStep 1781189 = 333973) (by norm_num)
theorem B798173 : Blo 350755 798173 := bbase (se 3 (by rfl) ⟨149657, by rfl⟩ : syracuseStep 798173 = 299315) (by norm_num)
theorem B1191509 : Blo 350755 1191509 := bbase (se 8 (by rfl) ⟨6981, by rfl⟩ : syracuseStep 1191509 = 13963) (by norm_num)
theorem B896629 : Blo 350755 896629 := bbase (se 5 (by rfl) ⟨42029, by rfl⟩ : syracuseStep 896629 = 84059) (by norm_num)
theorem B1126021 : Blo 350755 1126021 := bbase (se 4 (by rfl) ⟨105564, by rfl⟩ : syracuseStep 1126021 = 211129) (by norm_num)
theorem B1814197 : Blo 350755 1814197 := bbase (se 5 (by rfl) ⟨85040, by rfl⟩ : syracuseStep 1814197 = 170081) (by norm_num)
theorem B896741 : Blo 350755 896741 := bbase (se 4 (by rfl) ⟨84069, by rfl⟩ : syracuseStep 896741 = 168139) (by norm_num)
theorem B503597 : Blo 350755 503597 := bbase (se 3 (by rfl) ⟨94424, by rfl⟩ : syracuseStep 503597 = 188849) (by norm_num)
theorem B667453 : Blo 350755 667453 := bbase (se 3 (by rfl) ⟨125147, by rfl⟩ : syracuseStep 667453 = 250295) (by norm_num)
theorem B896933 : Blo 350755 896933 := bbase (se 4 (by rfl) ⟨84087, by rfl⟩ : syracuseStep 896933 = 168175) (by norm_num)
theorem B667597 : Blo 350755 667597 := bbase (se 3 (by rfl) ⟨125174, by rfl⟩ : syracuseStep 667597 = 250349) (by norm_num)
theorem B1191941 : Blo 350755 1191941 := bbase (se 4 (by rfl) ⟨111744, by rfl⟩ : syracuseStep 1191941 = 223489) (by norm_num)
theorem B667757 : Blo 350755 667757 := bbase (se 3 (by rfl) ⟨125204, by rfl⟩ : syracuseStep 667757 = 250409) (by norm_num)
theorem B536725 : Blo 350755 536725 := bbase (se 6 (by rfl) ⟨12579, by rfl⟩ : syracuseStep 536725 = 25159) (by norm_num)
theorem B1618165 : Blo 350755 1618165 := bbase (se 5 (by rfl) ⟨75851, by rfl⟩ : syracuseStep 1618165 = 151703) (by norm_num)
theorem B667901 : Blo 350755 667901 := bbase (se 3 (by rfl) ⟨125231, by rfl⟩ : syracuseStep 667901 = 250463) (by norm_num)
theorem B897277 : Blo 350755 897277 := bbase (se 3 (by rfl) ⟨168239, by rfl⟩ : syracuseStep 897277 = 336479) (by norm_num)
theorem B13873493 : Blo 350755 13873493 := bbase (se 10 (by rfl) ⟨20322, by rfl⟩ : syracuseStep 13873493 = 40645) (by norm_num)
theorem B504149 : Blo 350755 504149 := bbase (se 10 (by rfl) ⟨738, by rfl⟩ : syracuseStep 504149 = 1477) (by norm_num)
theorem B897389 : Blo 350755 897389 := bbase (se 3 (by rfl) ⟨168260, by rfl⟩ : syracuseStep 897389 = 336521) (by norm_num)
theorem B1192373 : Blo 350755 1192373 := bbase (se 5 (by rfl) ⟨55892, by rfl⟩ : syracuseStep 1192373 = 111785) (by norm_num)
theorem B1290725 : Blo 350755 1290725 := bbase (se 4 (by rfl) ⟨121005, by rfl⟩ : syracuseStep 1290725 = 242011) (by norm_num)
theorem B668189 : Blo 350755 668189 := bbase (se 3 (by rfl) ⟨125285, by rfl⟩ : syracuseStep 668189 = 250571) (by norm_num)
theorem B897581 : Blo 350755 897581 := bbase (se 3 (by rfl) ⟨168296, by rfl⟩ : syracuseStep 897581 = 336593) (by norm_num)
theorem B668341 : Blo 350755 668341 := bbase (se 5 (by rfl) ⟨31328, by rfl⟩ : syracuseStep 668341 = 62657) (by norm_num)
theorem B1782485 : Blo 350755 1782485 := bbase (se 7 (by rfl) ⟨20888, by rfl⟩ : syracuseStep 1782485 = 41777) (by norm_num)
theorem B1192805 : Blo 350755 1192805 := bbase (se 4 (by rfl) ⟨111825, by rfl⟩ : syracuseStep 1192805 = 223651) (by norm_num)
theorem B897925 : Blo 350755 897925 := bbase (se 4 (by rfl) ⟨84180, by rfl⟩ : syracuseStep 897925 = 168361) (by norm_num)
theorem B1029077 : Blo 350755 1029077 := bbase (se 7 (by rfl) ⟨12059, by rfl⟩ : syracuseStep 1029077 = 24119) (by norm_num)
theorem B668645 : Blo 350755 668645 := bbase (se 4 (by rfl) ⟨62685, by rfl⟩ : syracuseStep 668645 = 125371) (by norm_num)
theorem B504901 : Blo 350755 504901 := bbase (se 4 (by rfl) ⟨47334, by rfl⟩ : syracuseStep 504901 = 94669) (by norm_num)
theorem B1127621 : Blo 350755 1127621 := bbase (se 4 (by rfl) ⟨105714, by rfl⟩ : syracuseStep 1127621 = 211429) (by norm_num)
theorem B1193237 : Blo 350755 1193237 := bbase (se 6 (by rfl) ⟨27966, by rfl⟩ : syracuseStep 1193237 = 55933) (by norm_num)
theorem B636277 : Blo 350755 636277 := bbase (se 5 (by rfl) ⟨29825, by rfl⟩ : syracuseStep 636277 = 59651) (by norm_num)
theorem B1193669 : Blo 350755 1193669 := bbase (se 4 (by rfl) ⟨111906, by rfl⟩ : syracuseStep 1193669 = 223813) (by norm_num)
theorem B669397 : Blo 350755 669397 := bbase (se 7 (by rfl) ⟨7844, by rfl⟩ : syracuseStep 669397 = 15689) (by norm_num)
theorem B669541 : Blo 350755 669541 := bbase (se 4 (by rfl) ⟨62769, by rfl⟩ : syracuseStep 669541 = 125539) (by norm_num)
theorem B636853 : Blo 350755 636853 := bbase (se 5 (by rfl) ⟨29852, by rfl⟩ : syracuseStep 636853 = 59705) (by norm_num)
theorem B1783781 : Blo 350755 1783781 := bbase (se 4 (by rfl) ⟨167229, by rfl⟩ : syracuseStep 1783781 = 334459) (by norm_num)
theorem B669701 : Blo 350755 669701 := bbase (se 4 (by rfl) ⟨62784, by rfl⟩ : syracuseStep 669701 = 125569) (by norm_num)
theorem B1194101 : Blo 350755 1194101 := bbase (se 5 (by rfl) ⟨55973, by rfl⟩ : syracuseStep 1194101 = 111947) (by norm_num)
theorem B374917 : Blo 350755 374917 := bbase (se 4 (by rfl) ⟨35148, by rfl⟩ : syracuseStep 374917 = 70297) (by norm_num)
theorem B669845 : Blo 350755 669845 := bbase (se 6 (by rfl) ⟨15699, by rfl⟩ : syracuseStep 669845 = 31399) (by norm_num)
theorem B374977 : Blo 350755 374977 := bbase (se 2 (by rfl) ⟨140616, by rfl⟩ : syracuseStep 374977 = 281233) (by norm_num)
theorem B3029237 : Blo 350755 3029237 := bbase (se 5 (by rfl) ⟨141995, by rfl⟩ : syracuseStep 3029237 = 283991) (by norm_num)
theorem B1128725 : Blo 350755 1128725 := bbase (se 6 (by rfl) ⟨26454, by rfl⟩ : syracuseStep 1128725 = 52909) (by norm_num)
theorem B670133 : Blo 350755 670133 := bbase (se 5 (by rfl) ⟨31412, by rfl⟩ : syracuseStep 670133 = 62825) (by norm_num)
theorem B506341 : Blo 350755 506341 := bbase (se 4 (by rfl) ⟨47469, by rfl⟩ : syracuseStep 506341 = 94939) (by norm_num)
theorem B375293 : Blo 350755 375293 := bbase (se 3 (by rfl) ⟨70367, by rfl⟩ : syracuseStep 375293 = 140735) (by norm_num)
theorem B1194533 : Blo 350755 1194533 := bbase (se 4 (by rfl) ⟨111987, by rfl⟩ : syracuseStep 1194533 = 223975) (by norm_num)
theorem B670285 : Blo 350755 670285 := bbase (se 3 (by rfl) ⟨125678, by rfl⟩ : syracuseStep 670285 = 251357) (by norm_num)
theorem B637517 : Blo 350755 637517 := bbase (se 3 (by rfl) ⟨119534, by rfl⟩ : syracuseStep 637517 = 239069) (by norm_num)
theorem B506525 : Blo 350755 506525 := bbase (se 3 (by rfl) ⟨94973, by rfl⟩ : syracuseStep 506525 = 189947) (by norm_num)
theorem B637733 : Blo 350755 637733 := bbase (se 4 (by rfl) ⟨59787, by rfl⟩ : syracuseStep 637733 = 119575) (by norm_num)
theorem B1424213 : Blo 350755 1424213 := bbase (se 9 (by rfl) ⟨4172, by rfl⟩ : syracuseStep 1424213 = 8345) (by norm_num)
theorem B670589 : Blo 350755 670589 := bbase (se 3 (by rfl) ⟨125735, by rfl⟩ : syracuseStep 670589 = 251471) (by norm_num)
theorem B375737 : Blo 350755 375737 := bbase (se 2 (by rfl) ⟨140901, by rfl⟩ : syracuseStep 375737 = 281803) (by norm_num)
theorem B13581269 : Blo 350755 13581269 := bbase (se 7 (by rfl) ⟨159155, by rfl⟩ : syracuseStep 13581269 = 318311) (by norm_num)
theorem B1194965 : Blo 350755 1194965 := bbase (se 7 (by rfl) ⟨14003, by rfl⟩ : syracuseStep 1194965 = 28007) (by norm_num)
theorem B375797 : Blo 350755 375797 := bbase (se 5 (by rfl) ⟨17615, by rfl⟩ : syracuseStep 375797 = 35231) (by norm_num)
theorem B965621 : Blo 350755 965621 := bbase (se 5 (by rfl) ⟨45263, by rfl⟩ : syracuseStep 965621 = 90527) (by norm_num)
theorem B375925 : Blo 350755 375925 := bbase (se 5 (by rfl) ⟨17621, by rfl⟩ : syracuseStep 375925 = 35243) (by norm_num)
theorem B474349 : Blo 350755 474349 := bbase (se 3 (by rfl) ⟨88940, by rfl⟩ : syracuseStep 474349 = 177881) (by norm_num)
theorem B1785077 : Blo 350755 1785077 := bbase (se 5 (by rfl) ⟨83675, by rfl⟩ : syracuseStep 1785077 = 167351) (by norm_num)
theorem B638237 : Blo 350755 638237 := bbase (se 3 (by rfl) ⟨119669, by rfl⟩ : syracuseStep 638237 = 239339) (by norm_num)
theorem B2997557 : Blo 350755 2997557 := bbase (se 5 (by rfl) ⟨140510, by rfl⟩ : syracuseStep 2997557 = 281021) (by norm_num)
theorem B1195397 : Blo 350755 1195397 := bbase (se 4 (by rfl) ⟨112068, by rfl⟩ : syracuseStep 1195397 = 224137) (by norm_num)
theorem B2145781 : Blo 350755 2145781 := bbase (se 5 (by rfl) ⟨100583, by rfl⟩ : syracuseStep 2145781 = 201167) (by norm_num)
theorem B802333 : Blo 350755 802333 := bbase (se 3 (by rfl) ⟨150437, by rfl⟩ : syracuseStep 802333 = 300875) (by norm_num)
theorem B376369 : Blo 350755 376369 := bbase (se 2 (by rfl) ⟨141138, by rfl⟩ : syracuseStep 376369 = 282277) (by norm_num)
theorem B671341 : Blo 350755 671341 := bbase (se 3 (by rfl) ⟨125876, by rfl⟩ : syracuseStep 671341 = 251753) (by norm_num)
theorem B376489 : Blo 350755 376489 := bbase (se 2 (by rfl) ⟨141183, by rfl⟩ : syracuseStep 376489 = 282367) (by norm_num)
theorem B671485 : Blo 350755 671485 := bbase (se 3 (by rfl) ⟨125903, by rfl⟩ : syracuseStep 671485 = 251807) (by norm_num)
theorem B1195829 : Blo 350755 1195829 := bbase (se 5 (by rfl) ⟨56054, by rfl⟩ : syracuseStep 1195829 = 112109) (by norm_num)
theorem B671645 : Blo 350755 671645 := bbase (se 3 (by rfl) ⟨125933, by rfl⟩ : syracuseStep 671645 = 251867) (by norm_num)
theorem B376741 : Blo 350755 376741 := bbase (se 4 (by rfl) ⟨35319, by rfl⟩ : syracuseStep 376741 = 70639) (by norm_num)
theorem B376745 : Blo 350755 376745 := bbase (se 2 (by rfl) ⟨141279, by rfl⟩ : syracuseStep 376745 = 282559) (by norm_num)
theorem B671789 : Blo 350755 671789 := bbase (se 3 (by rfl) ⟨125960, by rfl⟩ : syracuseStep 671789 = 251921) (by norm_num)
theorem B3293237 : Blo 350755 3293237 := bbase (se 5 (by rfl) ⟨154370, by rfl⟩ : syracuseStep 3293237 = 308741) (by norm_num)
theorem B901181 : Blo 350755 901181 := bbase (se 3 (by rfl) ⟨168971, by rfl⟩ : syracuseStep 901181 = 337943) (by norm_num)
theorem B1425557 : Blo 350755 1425557 := bbase (se 6 (by rfl) ⟨33411, by rfl⟩ : syracuseStep 1425557 = 66823) (by norm_num)
theorem B1130645 : Blo 350755 1130645 := bbase (se 6 (by rfl) ⟨26499, by rfl⟩ : syracuseStep 1130645 = 52999) (by norm_num)
theorem B1196261 : Blo 350755 1196261 := bbase (se 4 (by rfl) ⟨112149, by rfl⟩ : syracuseStep 1196261 = 224299) (by norm_num)
theorem B672077 : Blo 350755 672077 := bbase (se 3 (by rfl) ⟨126014, by rfl⟩ : syracuseStep 672077 = 252029) (by norm_num)
theorem B377309 : Blo 350755 377309 := bbase (se 3 (by rfl) ⟨70745, by rfl⟩ : syracuseStep 377309 = 141491) (by norm_num)
theorem B672229 : Blo 350755 672229 := bbase (se 4 (by rfl) ⟨63021, by rfl⟩ : syracuseStep 672229 = 126043) (by norm_num)
theorem B1786373 : Blo 350755 1786373 := bbase (se 4 (by rfl) ⟨167472, by rfl⟩ : syracuseStep 1786373 = 334945) (by norm_num)
theorem B3195413 : Blo 350755 3195413 := bbase (se 6 (by rfl) ⟨74892, by rfl⟩ : syracuseStep 3195413 = 149785) (by norm_num)
theorem B475733 : Blo 350755 475733 := bbase (se 8 (by rfl) ⟨2787, by rfl⟩ : syracuseStep 475733 = 5575) (by norm_num)
theorem B1196693 : Blo 350755 1196693 := bbase (se 6 (by rfl) ⟨28047, by rfl⟩ : syracuseStep 1196693 = 56095) (by norm_num)
theorem B377497 : Blo 350755 377497 := bbase (se 2 (by rfl) ⟨141561, by rfl⟩ : syracuseStep 377497 = 283123) (by norm_num)
theorem B803501 : Blo 350755 803501 := bbase (se 3 (by rfl) ⟨150656, by rfl⟩ : syracuseStep 803501 = 301313) (by norm_num)
theorem B672533 : Blo 350755 672533 := bbase (se 6 (by rfl) ⟨15762, by rfl⟩ : syracuseStep 672533 = 31525) (by norm_num)
theorem B1688357 : Blo 350755 1688357 := bbase (se 4 (by rfl) ⟨158283, by rfl⟩ : syracuseStep 1688357 = 316567) (by norm_num)
theorem B1000325 : Blo 350755 1000325 := bbase (se 4 (by rfl) ⟨93780, by rfl⟩ : syracuseStep 1000325 = 187561) (by norm_num)
theorem B2671541 : Blo 350755 2671541 := bbase (se 5 (by rfl) ⟨125228, by rfl⟩ : syracuseStep 2671541 = 250457) (by norm_num)
theorem B1197125 : Blo 350755 1197125 := bbase (se 4 (by rfl) ⟨112230, by rfl⟩ : syracuseStep 1197125 = 224461) (by norm_num)
theorem B1688741 : Blo 350755 1688741 := bbase (se 4 (by rfl) ⟨158319, by rfl⟩ : syracuseStep 1688741 = 316639) (by norm_num)
theorem B2802869 : Blo 350755 2802869 := bbase (se 5 (by rfl) ⟨131384, by rfl⟩ : syracuseStep 2802869 = 262769) (by norm_num)
theorem B968053 : Blo 350755 968053 := bbase (se 5 (by rfl) ⟨45377, by rfl⟩ : syracuseStep 968053 = 90755) (by norm_num)
theorem B378317 : Blo 350755 378317 := bbase (se 3 (by rfl) ⟨70934, by rfl⟩ : syracuseStep 378317 = 141869) (by norm_num)
theorem B2803157 : Blo 350755 2803157 := bbase (se 7 (by rfl) ⟨32849, by rfl⟩ : syracuseStep 2803157 = 65699) (by norm_num)
theorem B673285 : Blo 350755 673285 := bbase (se 4 (by rfl) ⟨63120, by rfl⟩ : syracuseStep 673285 = 126241) (by norm_num)
theorem B1132069 : Blo 350755 1132069 := bbase (se 4 (by rfl) ⟨106131, by rfl⟩ : syracuseStep 1132069 = 212263) (by norm_num)
theorem B443981 : Blo 350755 443981 := bbase (se 3 (by rfl) ⟨83246, by rfl⟩ : syracuseStep 443981 = 166493) (by norm_num)
theorem B444037 : Blo 350755 444037 := bbase (se 4 (by rfl) ⟨41628, by rfl⟩ : syracuseStep 444037 = 83257) (by norm_num)
theorem B673429 : Blo 350755 673429 := bbase (se 6 (by rfl) ⟨15783, by rfl⟩ : syracuseStep 673429 = 31567) (by norm_num)
theorem B444133 : Blo 350755 444133 := bbase (se 4 (by rfl) ⟨41637, by rfl⟩ : syracuseStep 444133 = 83275) (by norm_num)
theorem B1787669 : Blo 350755 1787669 := bbase (se 6 (by rfl) ⟨41898, by rfl⟩ : syracuseStep 1787669 = 83797) (by norm_num)
theorem B378761 : Blo 350755 378761 := bbase (se 2 (by rfl) ⟨142035, by rfl⟩ : syracuseStep 378761 = 284071) (by norm_num)
theorem B444305 : Blo 350755 444305 := bbase (se 2 (by rfl) ⟨166614, by rfl⟩ : syracuseStep 444305 = 333229) (by norm_num)
theorem B444361 : Blo 350755 444361 := bbase (se 2 (by rfl) ⟨166635, by rfl⟩ : syracuseStep 444361 = 333271) (by norm_num)
theorem B575453 : Blo 350755 575453 := bbase (se 3 (by rfl) ⟨107897, by rfl⟩ : syracuseStep 575453 = 215795) (by norm_num)
theorem B1132517 : Blo 350755 1132517 := bbase (se 4 (by rfl) ⟨106173, by rfl⟩ : syracuseStep 1132517 = 212347) (by norm_num)
theorem B444457 : Blo 350755 444457 := bbase (se 2 (by rfl) ⟨166671, by rfl⟩ : syracuseStep 444457 = 333343) (by norm_num)
theorem B444629 : Blo 350755 444629 := bbase (se 7 (by rfl) ⟨5210, by rfl⟩ : syracuseStep 444629 = 10421) (by norm_num)
theorem B444685 : Blo 350755 444685 := bbase (se 3 (by rfl) ⟨83378, by rfl⟩ : syracuseStep 444685 = 166757) (by norm_num)
theorem B444781 : Blo 350755 444781 := bbase (se 3 (by rfl) ⟨83396, by rfl⟩ : syracuseStep 444781 = 166793) (by norm_num)
theorem B1427861 : Blo 350755 1427861 := bbase (se 6 (by rfl) ⟨33465, by rfl⟩ : syracuseStep 1427861 = 66931) (by norm_num)
theorem B1001909 : Blo 350755 1001909 := bbase (se 5 (by rfl) ⟨46964, by rfl⟩ : syracuseStep 1001909 = 93929) (by norm_num)
theorem B3230165 : Blo 350755 3230165 := bbase (se 7 (by rfl) ⟨37853, by rfl⟩ : syracuseStep 3230165 = 75707) (by norm_num)
theorem B2017781 : Blo 350755 2017781 := bbase (se 5 (by rfl) ⟨94583, by rfl⟩ : syracuseStep 2017781 = 189167) (by norm_num)
theorem B444953 : Blo 350755 444953 := bbase (se 2 (by rfl) ⟨166857, by rfl⟩ : syracuseStep 444953 = 333715) (by norm_num)
theorem B445009 : Blo 350755 445009 := bbase (se 2 (by rfl) ⟨166878, by rfl⟩ : syracuseStep 445009 = 333757) (by norm_num)
theorem B4016789 : Blo 350755 4016789 := bbase (se 6 (by rfl) ⟨94143, by rfl⟩ : syracuseStep 4016789 = 188287) (by norm_num)
theorem B445105 : Blo 350755 445105 := bbase (se 2 (by rfl) ⟨166914, by rfl⟩ : syracuseStep 445105 = 333829) (by norm_num)
theorem B510797 : Blo 350755 510797 := bbase (se 3 (by rfl) ⟨95774, by rfl⟩ : syracuseStep 510797 = 191549) (by norm_num)
theorem B445277 : Blo 350755 445277 := bbase (se 3 (by rfl) ⟨83489, by rfl⟩ : syracuseStep 445277 = 166979) (by norm_num)
theorem B445333 : Blo 350755 445333 := bbase (se 6 (by rfl) ⟨10437, by rfl⟩ : syracuseStep 445333 = 20875) (by norm_num)
theorem B445429 : Blo 350755 445429 := bbase (se 5 (by rfl) ⟨20879, by rfl⟩ : syracuseStep 445429 = 41759) (by norm_num)
theorem B1788965 : Blo 350755 1788965 := bbase (se 4 (by rfl) ⟨167715, by rfl⟩ : syracuseStep 1788965 = 335431) (by norm_num)
theorem B1035301 : Blo 350755 1035301 := bbase (se 4 (by rfl) ⟨97059, by rfl⟩ : syracuseStep 1035301 = 194119) (by norm_num)
theorem B1002581 : Blo 350755 1002581 := bbase (se 8 (by rfl) ⟨5874, by rfl⟩ : syracuseStep 1002581 = 11749) (by norm_num)
theorem B445601 : Blo 350755 445601 := bbase (se 2 (by rfl) ⟨167100, by rfl⟩ : syracuseStep 445601 = 334201) (by norm_num)
theorem B445657 : Blo 350755 445657 := bbase (se 2 (by rfl) ⟨167121, by rfl⟩ : syracuseStep 445657 = 334243) (by norm_num)
theorem B445753 : Blo 350755 445753 := bbase (se 2 (by rfl) ⟨167157, by rfl⟩ : syracuseStep 445753 = 334315) (by norm_num)
theorem B445925 : Blo 350755 445925 := bbase (se 4 (by rfl) ⟨41805, by rfl⟩ : syracuseStep 445925 = 83611) (by norm_num)
theorem B1003013 : Blo 350755 1003013 := bbase (se 4 (by rfl) ⟨94032, by rfl⟩ : syracuseStep 1003013 = 188065) (by norm_num)
theorem B445981 : Blo 350755 445981 := bbase (se 3 (by rfl) ⟨83621, by rfl⟩ : syracuseStep 445981 = 167243) (by norm_num)
theorem B446077 : Blo 350755 446077 := bbase (se 3 (by rfl) ⟨83639, by rfl⟩ : syracuseStep 446077 = 167279) (by norm_num)
theorem B675461 : Blo 350755 675461 := bbase (se 4 (by rfl) ⟨63324, by rfl⟩ : syracuseStep 675461 = 126649) (by norm_num)
theorem B2018965 : Blo 350755 2018965 := bbase (se 6 (by rfl) ⟨47319, by rfl⟩ : syracuseStep 2018965 = 94639) (by norm_num)
theorem B2248373 : Blo 350755 2248373 := bbase (se 5 (by rfl) ⟨105392, by rfl⟩ : syracuseStep 2248373 = 210785) (by norm_num)
theorem B446249 : Blo 350755 446249 := bbase (se 2 (by rfl) ⟨167343, by rfl⟩ : syracuseStep 446249 = 334687) (by norm_num)
theorem B446305 : Blo 350755 446305 := bbase (se 2 (by rfl) ⟨167364, by rfl⟩ : syracuseStep 446305 = 334729) (by norm_num)
theorem B905069 : Blo 350755 905069 := bbase (se 3 (by rfl) ⟨169700, by rfl⟩ : syracuseStep 905069 = 339401) (by norm_num)
theorem B380857 : Blo 350755 380857 := bbase (se 2 (by rfl) ⟨142821, by rfl⟩ : syracuseStep 380857 = 285643) (by norm_num)
theorem B446401 : Blo 350755 446401 := bbase (se 2 (by rfl) ⟨167400, by rfl⟩ : syracuseStep 446401 = 334801) (by norm_num)
theorem B479197 : Blo 350755 479197 := bbase (se 3 (by rfl) ⟨89849, by rfl⟩ : syracuseStep 479197 = 179699) (by norm_num)
theorem B446573 : Blo 350755 446573 := bbase (se 3 (by rfl) ⟨83732, by rfl⟩ : syracuseStep 446573 = 167465) (by norm_num)
theorem B446629 : Blo 350755 446629 := bbase (se 4 (by rfl) ⟨41871, by rfl⟩ : syracuseStep 446629 = 83743) (by norm_num)
theorem B1134773 : Blo 350755 1134773 := bbase (se 5 (by rfl) ⟨53192, by rfl⟩ : syracuseStep 1134773 = 106385) (by norm_num)
theorem B1003765 : Blo 350755 1003765 := bbase (se 5 (by rfl) ⟨47051, by rfl⟩ : syracuseStep 1003765 = 94103) (by norm_num)
theorem B446725 : Blo 350755 446725 := bbase (se 4 (by rfl) ⟨41880, by rfl⟩ : syracuseStep 446725 = 83761) (by norm_num)
theorem B1790261 : Blo 350755 1790261 := bbase (se 5 (by rfl) ⟨83918, by rfl⟩ : syracuseStep 1790261 = 167837) (by norm_num)
theorem B446897 : Blo 350755 446897 := bbase (se 2 (by rfl) ⟨167586, by rfl⟩ : syracuseStep 446897 = 335173) (by norm_num)
theorem B446953 : Blo 350755 446953 := bbase (se 2 (by rfl) ⟨167607, by rfl⟩ : syracuseStep 446953 = 335215) (by norm_num)
theorem B1364501 : Blo 350755 1364501 := bbase (se 6 (by rfl) ⟨31980, by rfl⟩ : syracuseStep 1364501 = 63961) (by norm_num)
theorem B447049 : Blo 350755 447049 := bbase (se 2 (by rfl) ⟨167643, by rfl⟩ : syracuseStep 447049 = 335287) (by norm_num)
theorem B1430261 : Blo 350755 1430261 := bbase (se 5 (by rfl) ⟨67043, by rfl⟩ : syracuseStep 1430261 = 134087) (by norm_num)
theorem B447221 : Blo 350755 447221 := bbase (se 5 (by rfl) ⟨20963, by rfl⟩ : syracuseStep 447221 = 41927) (by norm_num)
theorem B447277 : Blo 350755 447277 := bbase (se 3 (by rfl) ⟨83864, by rfl⟩ : syracuseStep 447277 = 167729) (by norm_num)
theorem B1037125 : Blo 350755 1037125 := bbase (se 4 (by rfl) ⟨97230, by rfl⟩ : syracuseStep 1037125 = 194461) (by norm_num)
theorem B447373 : Blo 350755 447373 := bbase (se 3 (by rfl) ⟨83882, by rfl⟩ : syracuseStep 447373 = 167765) (by norm_num)
theorem B971669 : Blo 350755 971669 := bbase (se 6 (by rfl) ⟨22773, by rfl⟩ : syracuseStep 971669 = 45547) (by norm_num)
theorem B906277 : Blo 350755 906277 := bbase (se 4 (by rfl) ⟨84963, by rfl⟩ : syracuseStep 906277 = 169927) (by norm_num)
theorem B447545 : Blo 350755 447545 := bbase (se 2 (by rfl) ⟨167829, by rfl⟩ : syracuseStep 447545 = 335659) (by norm_num)
theorem B447601 : Blo 350755 447601 := bbase (se 2 (by rfl) ⟨167850, by rfl⟩ : syracuseStep 447601 = 335701) (by norm_num)
theorem B447697 : Blo 350755 447697 := bbase (se 2 (by rfl) ⟨167886, by rfl⟩ : syracuseStep 447697 = 335773) (by norm_num)
theorem B382241 : Blo 350755 382241 := bbase (se 2 (by rfl) ⟨143340, by rfl⟩ : syracuseStep 382241 = 286681) (by norm_num)
theorem B447869 : Blo 350755 447869 := bbase (se 3 (by rfl) ⟨83975, by rfl⟩ : syracuseStep 447869 = 167951) (by norm_num)
theorem B447925 : Blo 350755 447925 := bbase (se 5 (by rfl) ⟨20996, by rfl⟩ : syracuseStep 447925 = 41993) (by norm_num)
theorem B448021 : Blo 350755 448021 := bbase (se 6 (by rfl) ⟨10500, by rfl⟩ : syracuseStep 448021 = 21001) (by norm_num)
theorem B1791557 : Blo 350755 1791557 := bbase (se 4 (by rfl) ⟨167958, by rfl⟩ : syracuseStep 1791557 = 335917) (by norm_num)
theorem B1070725 : Blo 350755 1070725 := bbase (se 4 (by rfl) ⟨100380, by rfl⟩ : syracuseStep 1070725 = 200761) (by norm_num)
theorem B448193 : Blo 350755 448193 := bbase (se 2 (by rfl) ⟨168072, by rfl⟩ : syracuseStep 448193 = 336145) (by norm_num)
theorem B448249 : Blo 350755 448249 := bbase (se 2 (by rfl) ⟨168093, by rfl⟩ : syracuseStep 448249 = 336187) (by norm_num)
theorem B448345 : Blo 350755 448345 := bbase (se 2 (by rfl) ⟨168129, by rfl⟩ : syracuseStep 448345 = 336259) (by norm_num)
theorem B645013 : Blo 350755 645013 := bbase (se 6 (by rfl) ⟨15117, by rfl⟩ : syracuseStep 645013 = 30235) (by norm_num)
theorem B6805397 : Blo 350755 6805397 := bbase (se 6 (by rfl) ⟨159501, by rfl⟩ : syracuseStep 6805397 = 319003) (by norm_num)
theorem B382925 : Blo 350755 382925 := bbase (se 3 (by rfl) ⟨71798, by rfl⟩ : syracuseStep 382925 = 143597) (by norm_num)
theorem B1333205 : Blo 350755 1333205 := bbase (se 7 (by rfl) ⟨15623, by rfl⟩ : syracuseStep 1333205 = 31247) (by norm_num)
theorem B2414549 : Blo 350755 2414549 := bbase (se 7 (by rfl) ⟨28295, by rfl⟩ : syracuseStep 2414549 = 56591) (by norm_num)
theorem B448517 : Blo 350755 448517 := bbase (se 4 (by rfl) ⟨42048, by rfl⟩ : syracuseStep 448517 = 84097) (by norm_num)
theorem B448573 : Blo 350755 448573 := bbase (se 3 (by rfl) ⟨84107, by rfl⟩ : syracuseStep 448573 = 168215) (by norm_num)
theorem B448669 : Blo 350755 448669 := bbase (se 3 (by rfl) ⟨84125, by rfl⟩ : syracuseStep 448669 = 168251) (by norm_num)
theorem B1333493 : Blo 350755 1333493 := bbase (se 5 (by rfl) ⟨62507, by rfl⟩ : syracuseStep 1333493 = 125015) (by norm_num)
theorem B448841 : Blo 350755 448841 := bbase (se 2 (by rfl) ⟨168315, by rfl⟩ : syracuseStep 448841 = 336631) (by norm_num)
theorem B448897 : Blo 350755 448897 := bbase (se 2 (by rfl) ⟨168336, by rfl⟩ : syracuseStep 448897 = 336673) (by norm_num)
theorem B3627413 : Blo 350755 3627413 := bbase (se 6 (by rfl) ⟨85017, by rfl⟩ : syracuseStep 3627413 = 170035) (by norm_num)
theorem B711109 : Blo 350755 711109 := bbase (se 4 (by rfl) ⟨66666, by rfl⟩ : syracuseStep 711109 = 133333) (by norm_num)
theorem B907757 : Blo 350755 907757 := bbase (se 3 (by rfl) ⟨170204, by rfl⟩ : syracuseStep 907757 = 340409) (by norm_num)
theorem B2546261 : Blo 350755 2546261 := bbase (se 8 (by rfl) ⟨14919, by rfl⟩ : syracuseStep 2546261 = 29839) (by norm_num)
theorem B940709 : Blo 350755 940709 := bbase (se 4 (by rfl) ⟨88191, by rfl⟩ : syracuseStep 940709 = 176383) (by norm_num)
theorem B1792853 : Blo 350755 1792853 := bbase (se 9 (by rfl) ⟨5252, by rfl⟩ : syracuseStep 1792853 = 10505) (by norm_num)
theorem B1006613 : Blo 350755 1006613 := bbase (se 6 (by rfl) ⟨23592, by rfl⟩ : syracuseStep 1006613 = 47185) (by norm_num)
theorem B5692693 : Blo 350755 5692693 := bbase (se 6 (by rfl) ⟨133422, by rfl⟩ : syracuseStep 5692693 = 266845) (by norm_num)
theorem B1072453 : Blo 350755 1072453 := bbase (se 4 (by rfl) ⟨100542, by rfl⟩ : syracuseStep 1072453 = 201085) (by norm_num)
theorem B1334677 : Blo 350755 1334677 := bbase (se 6 (by rfl) ⟨31281, by rfl⟩ : syracuseStep 1334677 = 62563) (by norm_num)
theorem B1072549 : Blo 350755 1072549 := bbase (se 4 (by rfl) ⟨100551, by rfl⟩ : syracuseStep 1072549 = 201103) (by norm_num)
theorem B2252245 : Blo 350755 2252245 := bbase (se 7 (by rfl) ⟨26393, by rfl⟩ : syracuseStep 2252245 = 52787) (by norm_num)
theorem B3399317 : Blo 350755 3399317 := bbase (se 6 (by rfl) ⟨79671, by rfl⟩ : syracuseStep 3399317 = 159343) (by norm_num)
theorem B1334981 : Blo 350755 1334981 := bbase (se 4 (by rfl) ⟨125154, by rfl⟩ : syracuseStep 1334981 = 250309) (by norm_num)
theorem B1794149 : Blo 350755 1794149 := bbase (se 4 (by rfl) ⟨168201, by rfl⟩ : syracuseStep 1794149 = 336403) (by norm_num)
theorem B1007797 : Blo 350755 1007797 := bbase (se 5 (by rfl) ⟨47240, by rfl⟩ : syracuseStep 1007797 = 94481) (by norm_num)
theorem B909605 : Blo 350755 909605 := bbase (se 4 (by rfl) ⟨85275, by rfl⟩ : syracuseStep 909605 = 170551) (by norm_num)
theorem B1007957 : Blo 350755 1007957 := bbase (se 10 (by rfl) ⟨1476, by rfl⟩ : syracuseStep 1007957 = 2953) (by norm_num)
theorem B680293 : Blo 350755 680293 := bbase (se 4 (by rfl) ⟨63777, by rfl⟩ : syracuseStep 680293 = 127555) (by norm_num)
theorem B844285 : Blo 350755 844285 := bbase (se 3 (by rfl) ⟨158303, by rfl⟩ : syracuseStep 844285 = 316607) (by norm_num)
theorem B2679317 : Blo 350755 2679317 := bbase (se 6 (by rfl) ⟨62796, by rfl⟩ : syracuseStep 2679317 = 125593) (by norm_num)
theorem B1008197 : Blo 350755 1008197 := bbase (se 4 (by rfl) ⟨94518, by rfl⟩ : syracuseStep 1008197 = 189037) (by norm_num)
theorem B680525 : Blo 350755 680525 := bbase (se 3 (by rfl) ⟨127598, by rfl⟩ : syracuseStep 680525 = 255197) (by norm_num)
theorem B647765 : Blo 350755 647765 := bbase (se 8 (by rfl) ⟨3795, by rfl⟩ : syracuseStep 647765 = 7591) (by norm_num)
theorem B1532533 : Blo 350755 1532533 := bbase (se 5 (by rfl) ⟨71837, by rfl⟩ : syracuseStep 1532533 = 143675) (by norm_num)
theorem B1008389 : Blo 350755 1008389 := bbase (se 4 (by rfl) ⟨94536, by rfl⟩ : syracuseStep 1008389 = 189073) (by norm_num)
theorem B1696565 : Blo 350755 1696565 := bbase (se 5 (by rfl) ⟨79526, by rfl⟩ : syracuseStep 1696565 = 159053) (by norm_num)
theorem B3793877 : Blo 350755 3793877 := bbase (se 7 (by rfl) ⟨44459, by rfl⟩ : syracuseStep 3793877 = 88919) (by norm_num)
theorem B1369045 : Blo 350755 1369045 := bbase (se 7 (by rfl) ⟨16043, by rfl⟩ : syracuseStep 1369045 = 32087) (by norm_num)
theorem B1270853 : Blo 350755 1270853 := bbase (se 4 (by rfl) ⟨119142, by rfl⟩ : syracuseStep 1270853 = 238285) (by norm_num)
theorem B844901 : Blo 350755 844901 := bbase (se 4 (by rfl) ⟨79209, by rfl⟩ : syracuseStep 844901 = 158419) (by norm_num)
theorem B845101 : Blo 350755 845101 := bbase (se 3 (by rfl) ⟨158456, by rfl⟩ : syracuseStep 845101 = 316913) (by norm_num)
theorem B1795445 : Blo 350755 1795445 := bbase (se 5 (by rfl) ⟨84161, by rfl⟩ : syracuseStep 1795445 = 168323) (by norm_num)
theorem B386537 : Blo 350755 386537 := bbase (se 2 (by rfl) ⟨144951, by rfl⟩ : syracuseStep 386537 = 289903) (by norm_num)
theorem B1271285 : Blo 350755 1271285 := bbase (se 5 (by rfl) ⟨59591, by rfl⟩ : syracuseStep 1271285 = 119183) (by norm_num)
theorem B1500677 : Blo 350755 1500677 := bbase (se 4 (by rfl) ⟨140688, by rfl⟩ : syracuseStep 1500677 = 281377) (by norm_num)
theorem B1009381 : Blo 350755 1009381 := bbase (se 4 (by rfl) ⟨94629, by rfl⟩ : syracuseStep 1009381 = 189259) (by norm_num)
theorem B1337093 : Blo 350755 1337093 := bbase (se 4 (by rfl) ⟨125352, by rfl⟩ : syracuseStep 1337093 = 250705) (by norm_num)
theorem B6022997 : Blo 350755 6022997 := bbase (se 9 (by rfl) ⟨17645, by rfl⟩ : syracuseStep 6022997 = 35291) (by norm_num)
theorem B714701 : Blo 350755 714701 := bbase (se 3 (by rfl) ⟨134006, by rfl⟩ : syracuseStep 714701 = 268013) (by norm_num)
theorem B1337381 : Blo 350755 1337381 := bbase (se 4 (by rfl) ⟨125379, by rfl⟩ : syracuseStep 1337381 = 250759) (by norm_num)
theorem B845909 : Blo 350755 845909 := bbase (se 8 (by rfl) ⟨4956, by rfl⟩ : syracuseStep 845909 = 9913) (by norm_num)
theorem B1075301 : Blo 350755 1075301 := bbase (se 4 (by rfl) ⟨100809, by rfl⟩ : syracuseStep 1075301 = 201619) (by norm_num)
theorem B452893 : Blo 350755 452893 := bbase (se 3 (by rfl) ⟨84917, by rfl⟩ : syracuseStep 452893 = 169835) (by norm_num)
theorem B1501685 : Blo 350755 1501685 := bbase (se 5 (by rfl) ⟨70391, by rfl⟩ : syracuseStep 1501685 = 140783) (by norm_num)
theorem B682597 : Blo 350755 682597 := bbase (se 4 (by rfl) ⟨63993, by rfl⟩ : syracuseStep 682597 = 127987) (by norm_num)
theorem B846677 : Blo 350755 846677 := bbase (se 9 (by rfl) ⟨2480, by rfl⟩ : syracuseStep 846677 = 4961) (by norm_num)
theorem B1338565 : Blo 350755 1338565 := bbase (se 4 (by rfl) ⟨125490, by rfl⟩ : syracuseStep 1338565 = 250981) (by norm_num)
theorem B3042613 : Blo 350755 3042613 := bbase (se 5 (by rfl) ⟨142622, by rfl⟩ : syracuseStep 3042613 = 285245) (by norm_num)
theorem B1338869 : Blo 350755 1338869 := bbase (se 5 (by rfl) ⟨62759, by rfl⟩ : syracuseStep 1338869 = 125519) (by norm_num)
theorem B421465 : Blo 350755 421465 := bbase (se 2 (by rfl) ⟨158049, by rfl⟩ : syracuseStep 421465 = 316099) (by norm_num)
theorem B421493 : Blo 350755 421493 := bbase (se 5 (by rfl) ⟨19757, by rfl⟩ : syracuseStep 421493 = 39515) (by norm_num)
theorem B749245 : Blo 350755 749245 := bbase (se 3 (by rfl) ⟨140483, by rfl⟩ : syracuseStep 749245 = 280967) (by norm_num)
theorem B356333 : Blo 350755 356333 := bbase (se 3 (by rfl) ⟨66812, by rfl⟩ : syracuseStep 356333 = 133625) (by norm_num)
theorem B815093 : Blo 350755 815093 := bbase (se 5 (by rfl) ⟨38207, by rfl⟩ : syracuseStep 815093 = 76415) (by norm_num)
theorem B421993 : Blo 350755 421993 := bbase (se 2 (by rfl) ⟨158247, by rfl⟩ : syracuseStep 421993 = 316495) (by norm_num)
theorem B749749 : Blo 350755 749749 := bbase (se 5 (by rfl) ⟨35144, by rfl⟩ : syracuseStep 749749 = 70289) (by norm_num)
theorem B1503461 : Blo 350755 1503461 := bbase (se 4 (by rfl) ⟨140949, by rfl⟩ : syracuseStep 1503461 = 281899) (by norm_num)
theorem B454997 : Blo 350755 454997 := bbase (se 10 (by rfl) ⟨666, by rfl⟩ : syracuseStep 454997 = 1333) (by norm_num)
theorem B1077637 : Blo 350755 1077637 := bbase (se 4 (by rfl) ⟨101028, by rfl⟩ : syracuseStep 1077637 = 202057) (by norm_num)
theorem B848389 : Blo 350755 848389 := bbase (se 4 (by rfl) ⟨79536, by rfl⟩ : syracuseStep 848389 = 159073) (by norm_num)
theorem B356897 : Blo 350755 356897 := bbase (se 2 (by rfl) ⟨133836, by rfl⟩ : syracuseStep 356897 = 267673) (by norm_num)
theorem B356933 : Blo 350755 356933 := bbase (se 4 (by rfl) ⟨33462, by rfl⟩ : syracuseStep 356933 = 66925) (by norm_num)
theorem B1274629 : Blo 350755 1274629 := bbase (se 4 (by rfl) ⟨119496, by rfl⟩ : syracuseStep 1274629 = 238993) (by norm_num)
theorem B717661 : Blo 350755 717661 := bbase (se 3 (by rfl) ⟨134561, by rfl⟩ : syracuseStep 717661 = 269123) (by norm_num)
theorem B750637 : Blo 350755 750637 := bbase (se 3 (by rfl) ⟨140744, by rfl⟩ : syracuseStep 750637 = 281489) (by norm_num)
theorem B357481 : Blo 350755 357481 := bbase (se 2 (by rfl) ⟨134055, by rfl⟩ : syracuseStep 357481 = 268111) (by norm_num)
theorem B849005 : Blo 350755 849005 := bbase (se 3 (by rfl) ⟨159188, by rfl⟩ : syracuseStep 849005 = 318377) (by norm_num)
theorem B1635509 : Blo 350755 1635509 := bbase (se 5 (by rfl) ⟨76664, by rfl⟩ : syracuseStep 1635509 = 153329) (by norm_num)
theorem B423181 : Blo 350755 423181 := bbase (se 3 (by rfl) ⟨79346, by rfl⟩ : syracuseStep 423181 = 158693) (by norm_num)
theorem B423373 : Blo 350755 423373 := bbase (se 3 (by rfl) ⟨79382, by rfl⟩ : syracuseStep 423373 = 158765) (by norm_num)
theorem B751133 : Blo 350755 751133 := bbase (se 3 (by rfl) ⟨140837, by rfl⟩ : syracuseStep 751133 = 281675) (by norm_num)
theorem B849437 : Blo 350755 849437 := bbase (se 3 (by rfl) ⟨159269, by rfl⟩ : syracuseStep 849437 = 318539) (by norm_num)
theorem B423473 : Blo 350755 423473 := bbase (se 2 (by rfl) ⟨158802, by rfl⟩ : syracuseStep 423473 = 317605) (by norm_num)
theorem B1340981 : Blo 350755 1340981 := bbase (se 5 (by rfl) ⟨62858, by rfl⟩ : syracuseStep 1340981 = 125717) (by norm_num)
theorem B1603205 : Blo 350755 1603205 := bbase (se 4 (by rfl) ⟨150300, by rfl⟩ : syracuseStep 1603205 = 300601) (by norm_num)
theorem B2717333 : Blo 350755 2717333 := bbase (se 6 (by rfl) ⟨63687, by rfl⟩ : syracuseStep 2717333 = 127375) (by norm_num)
theorem B1341269 : Blo 350755 1341269 := bbase (se 9 (by rfl) ⟨3929, by rfl⟩ : syracuseStep 1341269 = 7859) (by norm_num)
theorem B718789 : Blo 350755 718789 := bbase (se 4 (by rfl) ⟨67386, by rfl⟩ : syracuseStep 718789 = 134773) (by norm_num)
theorem B948437 : Blo 350755 948437 := bbase (se 7 (by rfl) ⟨11114, by rfl⟩ : syracuseStep 948437 = 22229) (by norm_num)
theorem B424261 : Blo 350755 424261 := bbase (se 4 (by rfl) ⟨39774, by rfl⟩ : syracuseStep 424261 = 79549) (by norm_num)
theorem B1374581 : Blo 350755 1374581 := bbase (se 5 (by rfl) ⟨64433, by rfl⟩ : syracuseStep 1374581 = 128867) (by norm_num)
theorem B752021 : Blo 350755 752021 := bbase (se 6 (by rfl) ⟨17625, by rfl⟩ : syracuseStep 752021 = 35251) (by norm_num)
theorem B752141 : Blo 350755 752141 := bbase (se 3 (by rfl) ⟨141026, by rfl⟩ : syracuseStep 752141 = 282053) (by norm_num)
theorem B358993 : Blo 350755 358993 := bbase (se 2 (by rfl) ⟨134622, by rfl⟩ : syracuseStep 358993 = 269245) (by norm_num)
theorem B490093 : Blo 350755 490093 := bbase (se 3 (by rfl) ⟨91892, by rfl⟩ : syracuseStep 490093 = 183785) (by norm_num)
theorem B1702565 : Blo 350755 1702565 := bbase (se 4 (by rfl) ⟨159615, by rfl⟩ : syracuseStep 1702565 = 319231) (by norm_num)
theorem B850637 : Blo 350755 850637 := bbase (se 3 (by rfl) ⟨159494, by rfl⟩ : syracuseStep 850637 = 318989) (by norm_num)
theorem B457445 : Blo 350755 457445 := bbase (se 4 (by rfl) ⟨42885, by rfl⟩ : syracuseStep 457445 = 85771) (by norm_num)
theorem B1801061 : Blo 350755 1801061 := bbase (se 4 (by rfl) ⟨168849, by rfl⟩ : syracuseStep 1801061 = 337699) (by norm_num)
theorem B359309 : Blo 350755 359309 := bbase (se 3 (by rfl) ⟨67370, by rfl⟩ : syracuseStep 359309 = 134741) (by norm_num)
theorem B1342453 : Blo 350755 1342453 := bbase (se 5 (by rfl) ⟨62927, by rfl⟩ : syracuseStep 1342453 = 125855) (by norm_num)
theorem B687109 : Blo 350755 687109 := bbase (se 4 (by rfl) ⟨64416, by rfl⟩ : syracuseStep 687109 = 128833) (by norm_num)
theorem B457741 : Blo 350755 457741 := bbase (se 3 (by rfl) ⟨85826, by rfl⟩ : syracuseStep 457741 = 171653) (by norm_num)
theorem B424973 : Blo 350755 424973 := bbase (se 3 (by rfl) ⟨79682, by rfl⟩ : syracuseStep 424973 = 159365) (by norm_num)
theorem B752773 : Blo 350755 752773 := bbase (se 4 (by rfl) ⟨70572, by rfl⟩ : syracuseStep 752773 = 141145) (by norm_num)
theorem B1342757 : Blo 350755 1342757 := bbase (se 4 (by rfl) ⟨125883, by rfl⟩ : syracuseStep 1342757 = 251767) (by norm_num)
theorem B425309 : Blo 350755 425309 := bbase (se 3 (by rfl) ⟨79745, by rfl⟩ : syracuseStep 425309 = 159491) (by norm_num)
theorem B425425 : Blo 350755 425425 := bbase (se 2 (by rfl) ⟨159534, by rfl⟩ : syracuseStep 425425 = 319069) (by norm_num)
theorem B425449 : Blo 350755 425449 := bbase (se 2 (by rfl) ⟨159543, by rfl⟩ : syracuseStep 425449 = 319087) (by norm_num)
theorem B917477 : Blo 350755 917477 := bbase (se 4 (by rfl) ⟨86013, by rfl⟩ : syracuseStep 917477 = 172027) (by norm_num)
theorem B753661 : Blo 350755 753661 := bbase (se 3 (by rfl) ⟨141311, by rfl⟩ : syracuseStep 753661 = 282623) (by norm_num)
theorem B8781965 : Blo 350755 8781965 := bstep (se 3 (by rfl) ⟨1646618, by rfl⟩ : syracuseStep 8781965 = 3293237) B3293237
theorem B1343729 : Blo 350755 1343729 := bstep (se 2 (by rfl) ⟨503898, by rfl⟩ : syracuseStep 1343729 = 1007797) B1007797
theorem B2130275 : Blo 350755 2130275 := bstep (se 1 (by rfl) ⟨1597706, by rfl⟩ : syracuseStep 2130275 = 3195413) B3195413
theorem B3801485 : Blo 350755 3801485 := bstep (se 3 (by rfl) ⟨712778, by rfl⟩ : syracuseStep 3801485 = 1425557) B1425557
theorem B3015053 : Blo 350755 3015053 := bstep (se 3 (by rfl) ⟨565322, by rfl⟩ : syracuseStep 3015053 = 1130645) B1130645
theorem B1868579 : Blo 350755 1868579 := bstep (se 1 (by rfl) ⟨1401434, by rfl⟩ : syracuseStep 1868579 = 2802869) B2802869
theorem B754481 : Blo 350755 754481 := bstep (se 2 (by rfl) ⟨282930, by rfl⟩ : syracuseStep 754481 = 565861) B565861
theorem B1344397 : Blo 350755 1344397 := bstep (se 3 (by rfl) ⟨252074, by rfl⟩ : syracuseStep 1344397 = 504149) B504149
theorem B1213325 : Blo 350755 1213325 := bstep (se 3 (by rfl) ⟨227498, by rfl⟩ : syracuseStep 1213325 = 454997) B454997
theorem B1868771 : Blo 350755 1868771 := bstep (se 1 (by rfl) ⟨1401578, by rfl⟩ : syracuseStep 1868771 = 2803157) B2803157
theorem B1148141 : Blo 350755 1148141 := bstep (se 3 (by rfl) ⟨215276, by rfl⟩ : syracuseStep 1148141 = 430553) B430553
theorem B755011 : Blo 350755 755011 := bstep (se 1 (by rfl) ⟨566258, by rfl⟩ : syracuseStep 755011 = 1132517) B1132517
theorem B394627 : Blo 350755 394627 := bstep (se 1 (by rfl) ⟨295970, by rfl⟩ : syracuseStep 394627 = 591941) B591941
theorem B951725 : Blo 350755 951725 := bstep (se 3 (by rfl) ⟨178448, by rfl⟩ : syracuseStep 951725 = 356897) B356897
theorem B951821 : Blo 350755 951821 := bstep (se 3 (by rfl) ⟨178466, by rfl⟩ : syracuseStep 951821 = 356933) B356933
theorem B394771 : Blo 350755 394771 := bstep (se 1 (by rfl) ⟨296078, by rfl⟩ : syracuseStep 394771 = 592157) B592157
theorem B951907 : Blo 350755 951907 := bstep (se 1 (by rfl) ⟨713930, by rfl⟩ : syracuseStep 951907 = 1427861) B1427861
theorem B394915 : Blo 350755 394915 := bstep (se 1 (by rfl) ⟨296186, by rfl⟩ : syracuseStep 394915 = 592373) B592373
theorem B1345187 : Blo 350755 1345187 := bstep (se 1 (by rfl) ⟨1008890, by rfl⟩ : syracuseStep 1345187 = 2017781) B2017781
theorem B2262725 : Blo 350755 2262725 := bstep (se 4 (by rfl) ⟨212130, by rfl⟩ : syracuseStep 2262725 = 424261) B424261
theorem B395059 : Blo 350755 395059 := bstep (se 1 (by rfl) ⟨296294, by rfl⟩ : syracuseStep 395059 = 592589) B592589
theorem B526145 : Blo 350755 526145 := bstep (se 2 (by rfl) ⟨197304, by rfl⟩ : syracuseStep 526145 = 394609) B394609
theorem B526163 : Blo 350755 526163 := bstep (se 1 (by rfl) ⟨394622, by rfl⟩ : syracuseStep 526163 = 789245) B789245
theorem B526193 : Blo 350755 526193 := bstep (se 2 (by rfl) ⟨197322, by rfl⟩ : syracuseStep 526193 = 394645) B394645
theorem B526211 : Blo 350755 526211 := bstep (se 1 (by rfl) ⟨394658, by rfl⟩ : syracuseStep 526211 = 789317) B789317
theorem B722819 : Blo 350755 722819 := bstep (se 1 (by rfl) ⟨542114, by rfl⟩ : syracuseStep 722819 = 1084229) B1084229
theorem B526241 : Blo 350755 526241 := bstep (se 2 (by rfl) ⟨197340, by rfl⟩ : syracuseStep 526241 = 394681) B394681
theorem B526259 : Blo 350755 526259 := bstep (se 1 (by rfl) ⟨394694, by rfl⟩ : syracuseStep 526259 = 789389) B789389
theorem B395203 : Blo 350755 395203 := bstep (se 1 (by rfl) ⟨296402, by rfl⟩ : syracuseStep 395203 = 592805) B592805
theorem B526289 : Blo 350755 526289 := bstep (se 2 (by rfl) ⟨197358, by rfl⟩ : syracuseStep 526289 = 394717) B394717
theorem B526307 : Blo 350755 526307 := bstep (se 1 (by rfl) ⟨394730, by rfl⟩ : syracuseStep 526307 = 789461) B789461
theorem B526337 : Blo 350755 526337 := bstep (se 2 (by rfl) ⟨197376, by rfl⟩ : syracuseStep 526337 = 394753) B394753
theorem B2689037 : Blo 350755 2689037 := bstep (se 3 (by rfl) ⟨504194, by rfl⟩ : syracuseStep 2689037 = 1008389) B1008389
theorem B526355 : Blo 350755 526355 := bstep (se 1 (by rfl) ⟨394766, by rfl⟩ : syracuseStep 526355 = 789533) B789533
theorem B591907 : Blo 350755 591907 := bstep (se 1 (by rfl) ⟨443930, by rfl⟩ : syracuseStep 591907 = 887861) B887861
theorem B526385 : Blo 350755 526385 := bstep (se 2 (by rfl) ⟨197394, by rfl⟩ : syracuseStep 526385 = 394789) B394789
theorem B1509425 : Blo 350755 1509425 := bstep (se 2 (by rfl) ⟨566034, by rfl⟩ : syracuseStep 1509425 = 1132069) B1132069
theorem B526403 : Blo 350755 526403 := bstep (se 1 (by rfl) ⟨394802, by rfl⟩ : syracuseStep 526403 = 789605) B789605
theorem B395347 : Blo 350755 395347 := bstep (se 1 (by rfl) ⟨296510, by rfl⟩ : syracuseStep 395347 = 593021) B593021
theorem B526433 : Blo 350755 526433 := bstep (se 2 (by rfl) ⟨197412, by rfl⟩ : syracuseStep 526433 = 394825) B394825
theorem B1509475 : Blo 350755 1509475 := bstep (se 1 (by rfl) ⟨1132106, by rfl⟩ : syracuseStep 1509475 = 2264213) B2264213
theorem B526451 : Blo 350755 526451 := bstep (se 1 (by rfl) ⟨394838, by rfl⟩ : syracuseStep 526451 = 789677) B789677
theorem B4524173 : Blo 350755 4524173 := bstep (se 3 (by rfl) ⟨848282, by rfl⟩ : syracuseStep 4524173 = 1696565) B1696565
theorem B526481 : Blo 350755 526481 := bstep (se 2 (by rfl) ⟨197430, by rfl⟩ : syracuseStep 526481 = 394861) B394861
theorem B526499 : Blo 350755 526499 := bstep (se 1 (by rfl) ⟨394874, by rfl⟩ : syracuseStep 526499 = 789749) B789749
theorem B592049 : Blo 350755 592049 := bstep (se 2 (by rfl) ⟨222018, by rfl⟩ : syracuseStep 592049 = 444037) B444037
theorem B526529 : Blo 350755 526529 := bstep (se 2 (by rfl) ⟨197448, by rfl⟩ : syracuseStep 526529 = 394897) B394897
theorem B526547 : Blo 350755 526547 := bstep (se 1 (by rfl) ⟨394910, by rfl⟩ : syracuseStep 526547 = 789821) B789821
theorem B395491 : Blo 350755 395491 := bstep (se 1 (by rfl) ⟨296618, by rfl⟩ : syracuseStep 395491 = 593237) B593237
theorem B526577 : Blo 350755 526577 := bstep (se 2 (by rfl) ⟨197466, by rfl⟩ : syracuseStep 526577 = 394933) B394933
theorem B526595 : Blo 350755 526595 := bstep (se 1 (by rfl) ⟨394946, by rfl⟩ : syracuseStep 526595 = 789893) B789893
theorem B10455317 : Blo 350755 10455317 := bstep (se 6 (by rfl) ⟨245046, by rfl⟩ : syracuseStep 10455317 = 490093) B490093
theorem B526625 : Blo 350755 526625 := bstep (se 2 (by rfl) ⟨197484, by rfl⟩ : syracuseStep 526625 = 394969) B394969
theorem B592177 : Blo 350755 592177 := bstep (se 2 (by rfl) ⟨222066, by rfl⟩ : syracuseStep 592177 = 444133) B444133
theorem B1345841 : Blo 350755 1345841 := bstep (se 2 (by rfl) ⟨504690, by rfl⟩ : syracuseStep 1345841 = 1009381) B1009381
theorem B526643 : Blo 350755 526643 := bstep (se 1 (by rfl) ⟨394982, by rfl⟩ : syracuseStep 526643 = 789965) B789965
theorem B526673 : Blo 350755 526673 := bstep (se 2 (by rfl) ⟨197502, by rfl⟩ : syracuseStep 526673 = 395005) B395005
theorem B592211 : Blo 350755 592211 := bstep (se 1 (by rfl) ⟨444158, by rfl⟩ : syracuseStep 592211 = 888317) B888317
theorem B526691 : Blo 350755 526691 := bstep (se 1 (by rfl) ⟨395018, by rfl⟩ : syracuseStep 526691 = 790037) B790037
theorem B395635 : Blo 350755 395635 := bstep (se 1 (by rfl) ⟨296726, by rfl⟩ : syracuseStep 395635 = 593453) B593453
theorem B526721 : Blo 350755 526721 := bstep (se 2 (by rfl) ⟨197520, by rfl⟩ : syracuseStep 526721 = 395041) B395041
theorem B2591117 : Blo 350755 2591117 := bstep (se 3 (by rfl) ⟨485834, by rfl⟩ : syracuseStep 2591117 = 971669) B971669
theorem B526739 : Blo 350755 526739 := bstep (se 1 (by rfl) ⟨395054, by rfl⟩ : syracuseStep 526739 = 790109) B790109
theorem B526769 : Blo 350755 526769 := bstep (se 2 (by rfl) ⟨197538, by rfl⟩ : syracuseStep 526769 = 395077) B395077
theorem B526787 : Blo 350755 526787 := bstep (se 1 (by rfl) ⟨395090, by rfl⟩ : syracuseStep 526787 = 790181) B790181
theorem B592339 : Blo 350755 592339 := bstep (se 1 (by rfl) ⟨444254, by rfl⟩ : syracuseStep 592339 = 888509) B888509
theorem B526817 : Blo 350755 526817 := bstep (se 2 (by rfl) ⟨197556, by rfl⟩ : syracuseStep 526817 = 395113) B395113
theorem B526835 : Blo 350755 526835 := bstep (se 1 (by rfl) ⟨395126, by rfl⟩ : syracuseStep 526835 = 790253) B790253
theorem B395779 : Blo 350755 395779 := bstep (se 1 (by rfl) ⟨296834, by rfl⟩ : syracuseStep 395779 = 593669) B593669
theorem B526865 : Blo 350755 526865 := bstep (se 2 (by rfl) ⟨197574, by rfl⟩ : syracuseStep 526865 = 395149) B395149
theorem B526883 : Blo 350755 526883 := bstep (se 1 (by rfl) ⟨395162, by rfl⟩ : syracuseStep 526883 = 790325) B790325
theorem B526913 : Blo 350755 526913 := bstep (se 2 (by rfl) ⟨197592, by rfl⟩ : syracuseStep 526913 = 395185) B395185
theorem B526931 : Blo 350755 526931 := bstep (se 1 (by rfl) ⟨395198, by rfl⟩ : syracuseStep 526931 = 790397) B790397
theorem B592481 : Blo 350755 592481 := bstep (se 2 (by rfl) ⟨222180, by rfl⟩ : syracuseStep 592481 = 444361) B444361
theorem B526961 : Blo 350755 526961 := bstep (se 2 (by rfl) ⟨197610, by rfl⟩ : syracuseStep 526961 = 395221) B395221
theorem B526979 : Blo 350755 526979 := bstep (se 1 (by rfl) ⟨395234, by rfl⟩ : syracuseStep 526979 = 790469) B790469
theorem B395923 : Blo 350755 395923 := bstep (se 1 (by rfl) ⟨296942, by rfl⟩ : syracuseStep 395923 = 593885) B593885
theorem B527009 : Blo 350755 527009 := bstep (se 2 (by rfl) ⟨197628, by rfl⟩ : syracuseStep 527009 = 395257) B395257
theorem B527027 : Blo 350755 527027 := bstep (se 1 (by rfl) ⟨395270, by rfl⟩ : syracuseStep 527027 = 790541) B790541
theorem B527057 : Blo 350755 527057 := bstep (se 2 (by rfl) ⟨197646, by rfl⟩ : syracuseStep 527057 = 395293) B395293
theorem B592609 : Blo 350755 592609 := bstep (se 2 (by rfl) ⟨222228, by rfl⟩ : syracuseStep 592609 = 444457) B444457
theorem B527075 : Blo 350755 527075 := bstep (se 1 (by rfl) ⟨395306, by rfl⟩ : syracuseStep 527075 = 790613) B790613
theorem B527105 : Blo 350755 527105 := bstep (se 2 (by rfl) ⟨197664, by rfl⟩ : syracuseStep 527105 = 395329) B395329
theorem B592643 : Blo 350755 592643 := bstep (se 1 (by rfl) ⟨444482, by rfl⟩ : syracuseStep 592643 = 888965) B888965
theorem B756497 : Blo 350755 756497 := bstep (se 2 (by rfl) ⟨283686, by rfl⟩ : syracuseStep 756497 = 567373) B567373
theorem B527123 : Blo 350755 527123 := bstep (se 1 (by rfl) ⟨395342, by rfl⟩ : syracuseStep 527123 = 790685) B790685
theorem B396067 : Blo 350755 396067 := bstep (se 1 (by rfl) ⟨297050, by rfl⟩ : syracuseStep 396067 = 594101) B594101
theorem B756515 : Blo 350755 756515 := bstep (se 1 (by rfl) ⟨567386, by rfl⟩ : syracuseStep 756515 = 1134773) B1134773
theorem B527153 : Blo 350755 527153 := bstep (se 2 (by rfl) ⟨197682, by rfl⟩ : syracuseStep 527153 = 395365) B395365
theorem B527171 : Blo 350755 527171 := bstep (se 1 (by rfl) ⟨395378, by rfl⟩ : syracuseStep 527171 = 790757) B790757
theorem B527201 : Blo 350755 527201 := bstep (se 2 (by rfl) ⟨197700, by rfl⟩ : syracuseStep 527201 = 395401) B395401
theorem B527219 : Blo 350755 527219 := bstep (se 1 (by rfl) ⟨395414, by rfl⟩ : syracuseStep 527219 = 790829) B790829
theorem B592771 : Blo 350755 592771 := bstep (se 1 (by rfl) ⟨444578, by rfl⟩ : syracuseStep 592771 = 889157) B889157
theorem B527249 : Blo 350755 527249 := bstep (se 2 (by rfl) ⟨197718, by rfl⟩ : syracuseStep 527249 = 395437) B395437
theorem B527267 : Blo 350755 527267 := bstep (se 1 (by rfl) ⟨395450, by rfl⟩ : syracuseStep 527267 = 790901) B790901
theorem B789425 : Blo 350755 789425 := bstep (se 2 (by rfl) ⟨296034, by rfl⟩ : syracuseStep 789425 = 592069) B592069
theorem B396211 : Blo 350755 396211 := bstep (se 1 (by rfl) ⟨297158, by rfl⟩ : syracuseStep 396211 = 594317) B594317
theorem B527297 : Blo 350755 527297 := bstep (se 2 (by rfl) ⟨197736, by rfl⟩ : syracuseStep 527297 = 395473) B395473
theorem B789443 : Blo 350755 789443 := bstep (se 1 (by rfl) ⟨592082, by rfl⟩ : syracuseStep 789443 = 1184165) B1184165
theorem B527315 : Blo 350755 527315 := bstep (se 1 (by rfl) ⟨395486, by rfl⟩ : syracuseStep 527315 = 790973) B790973
theorem B527345 : Blo 350755 527345 := bstep (se 2 (by rfl) ⟨197754, by rfl⟩ : syracuseStep 527345 = 395509) B395509
theorem B527363 : Blo 350755 527363 := bstep (se 1 (by rfl) ⟨395522, by rfl⟩ : syracuseStep 527363 = 791045) B791045
theorem B592913 : Blo 350755 592913 := bstep (se 2 (by rfl) ⟨222342, by rfl⟩ : syracuseStep 592913 = 444685) B444685
theorem B527393 : Blo 350755 527393 := bstep (se 2 (by rfl) ⟨197772, by rfl⟩ : syracuseStep 527393 = 395545) B395545
theorem B527411 : Blo 350755 527411 := bstep (se 1 (by rfl) ⟨395558, by rfl⟩ : syracuseStep 527411 = 791117) B791117
theorem B396355 : Blo 350755 396355 := bstep (se 1 (by rfl) ⟨297266, by rfl⟩ : syracuseStep 396355 = 594533) B594533
theorem B527441 : Blo 350755 527441 := bstep (se 2 (by rfl) ⟨197790, by rfl⟩ : syracuseStep 527441 = 395581) B395581
theorem B527459 : Blo 350755 527459 := bstep (se 1 (by rfl) ⟨395594, by rfl⟩ : syracuseStep 527459 = 791189) B791189
theorem B527489 : Blo 350755 527489 := bstep (se 2 (by rfl) ⟨197808, by rfl⟩ : syracuseStep 527489 = 395617) B395617
theorem B4361357 : Blo 350755 4361357 := bstep (se 3 (by rfl) ⟨817754, by rfl⟩ : syracuseStep 4361357 = 1635509) B1635509
theorem B593041 : Blo 350755 593041 := bstep (se 2 (by rfl) ⟨222390, by rfl⟩ : syracuseStep 593041 = 444781) B444781
theorem B527507 : Blo 350755 527507 := bstep (se 1 (by rfl) ⟨395630, by rfl⟩ : syracuseStep 527507 = 791261) B791261
theorem B953507 : Blo 350755 953507 := bstep (se 1 (by rfl) ⟨715130, by rfl⟩ : syracuseStep 953507 = 1430261) B1430261
theorem B527537 : Blo 350755 527537 := bstep (se 2 (by rfl) ⟨197826, by rfl⟩ : syracuseStep 527537 = 395653) B395653
theorem B593075 : Blo 350755 593075 := bstep (se 1 (by rfl) ⟨444806, by rfl⟩ : syracuseStep 593075 = 889613) B889613
theorem B527555 : Blo 350755 527555 := bstep (se 1 (by rfl) ⟨395666, by rfl⟩ : syracuseStep 527555 = 791333) B791333
theorem B789713 : Blo 350755 789713 := bstep (se 2 (by rfl) ⟨296142, by rfl⟩ : syracuseStep 789713 = 592285) B592285
theorem B396499 : Blo 350755 396499 := bstep (se 1 (by rfl) ⟨297374, by rfl⟩ : syracuseStep 396499 = 594749) B594749
theorem B527585 : Blo 350755 527585 := bstep (se 2 (by rfl) ⟨197844, by rfl⟩ : syracuseStep 527585 = 395689) B395689
theorem B789731 : Blo 350755 789731 := bstep (se 1 (by rfl) ⟨592298, by rfl⟩ : syracuseStep 789731 = 1184597) B1184597
theorem B527603 : Blo 350755 527603 := bstep (se 1 (by rfl) ⟨395702, by rfl⟩ : syracuseStep 527603 = 791405) B791405
theorem B527633 : Blo 350755 527633 := bstep (se 2 (by rfl) ⟨197862, by rfl⟩ : syracuseStep 527633 = 395725) B395725
theorem B527651 : Blo 350755 527651 := bstep (se 1 (by rfl) ⟨395738, by rfl⟩ : syracuseStep 527651 = 791477) B791477
theorem B593203 : Blo 350755 593203 := bstep (se 1 (by rfl) ⟨444902, by rfl⟩ : syracuseStep 593203 = 889805) B889805
theorem B527681 : Blo 350755 527681 := bstep (se 2 (by rfl) ⟨197880, by rfl⟩ : syracuseStep 527681 = 395761) B395761
theorem B527699 : Blo 350755 527699 := bstep (se 1 (by rfl) ⟨395774, by rfl⟩ : syracuseStep 527699 = 791549) B791549
theorem B2035043 : Blo 350755 2035043 := bstep (se 1 (by rfl) ⟨1526282, by rfl⟩ : syracuseStep 2035043 = 3052565) B3052565
theorem B396643 : Blo 350755 396643 := bstep (se 1 (by rfl) ⟨297482, by rfl⟩ : syracuseStep 396643 = 594965) B594965
theorem B527729 : Blo 350755 527729 := bstep (se 2 (by rfl) ⟨197898, by rfl⟩ : syracuseStep 527729 = 395797) B395797
theorem B527747 : Blo 350755 527747 := bstep (se 1 (by rfl) ⟨395810, by rfl⟩ : syracuseStep 527747 = 791621) B791621
theorem B527777 : Blo 350755 527777 := bstep (se 2 (by rfl) ⟨197916, by rfl⟩ : syracuseStep 527777 = 395833) B395833
theorem B1019309 : Blo 350755 1019309 := bstep (se 3 (by rfl) ⟨191120, by rfl⟩ : syracuseStep 1019309 = 382241) B382241
theorem B527795 : Blo 350755 527795 := bstep (se 1 (by rfl) ⟨395846, by rfl⟩ : syracuseStep 527795 = 791693) B791693
theorem B593345 : Blo 350755 593345 := bstep (se 2 (by rfl) ⟨222504, by rfl⟩ : syracuseStep 593345 = 445009) B445009
theorem B527825 : Blo 350755 527825 := bstep (se 2 (by rfl) ⟨197934, by rfl⟩ : syracuseStep 527825 = 395869) B395869
theorem B527843 : Blo 350755 527843 := bstep (se 1 (by rfl) ⟨395882, by rfl⟩ : syracuseStep 527843 = 791765) B791765
theorem B790001 : Blo 350755 790001 := bstep (se 2 (by rfl) ⟨296250, by rfl⟩ : syracuseStep 790001 = 592501) B592501
theorem B396787 : Blo 350755 396787 := bstep (se 1 (by rfl) ⟨297590, by rfl⟩ : syracuseStep 396787 = 595181) B595181
theorem B527873 : Blo 350755 527873 := bstep (se 2 (by rfl) ⟨197952, by rfl⟩ : syracuseStep 527873 = 395905) B395905
theorem B790019 : Blo 350755 790019 := bstep (se 1 (by rfl) ⟨592514, by rfl⟩ : syracuseStep 790019 = 1185029) B1185029
theorem B527891 : Blo 350755 527891 := bstep (se 1 (by rfl) ⟨395918, by rfl⟩ : syracuseStep 527891 = 791837) B791837
theorem B527921 : Blo 350755 527921 := bstep (se 2 (by rfl) ⟨197970, by rfl⟩ : syracuseStep 527921 = 395941) B395941
theorem B593473 : Blo 350755 593473 := bstep (se 2 (by rfl) ⟨222552, by rfl⟩ : syracuseStep 593473 = 445105) B445105
theorem B527939 : Blo 350755 527939 := bstep (se 1 (by rfl) ⟨395954, by rfl⟩ : syracuseStep 527939 = 791909) B791909
theorem B527969 : Blo 350755 527969 := bstep (se 2 (by rfl) ⟨197988, by rfl⟩ : syracuseStep 527969 = 395977) B395977
theorem B593507 : Blo 350755 593507 := bstep (se 1 (by rfl) ⟨445130, by rfl⟩ : syracuseStep 593507 = 890261) B890261
theorem B527987 : Blo 350755 527987 := bstep (se 1 (by rfl) ⟨395990, by rfl⟩ : syracuseStep 527987 = 791981) B791981
theorem B396931 : Blo 350755 396931 := bstep (se 1 (by rfl) ⟨297698, by rfl⟩ : syracuseStep 396931 = 595397) B595397
theorem B528017 : Blo 350755 528017 := bstep (se 2 (by rfl) ⟨198006, by rfl⟩ : syracuseStep 528017 = 396013) B396013
theorem B528035 : Blo 350755 528035 := bstep (se 1 (by rfl) ⟨396026, by rfl⟩ : syracuseStep 528035 = 792053) B792053
theorem B528065 : Blo 350755 528065 := bstep (se 2 (by rfl) ⟨198024, by rfl⟩ : syracuseStep 528065 = 396049) B396049
theorem B888529 : Blo 350755 888529 := bstep (se 2 (by rfl) ⟨333198, by rfl⟩ : syracuseStep 888529 = 666397) B666397
theorem B528083 : Blo 350755 528083 := bstep (se 1 (by rfl) ⟨396062, by rfl⟩ : syracuseStep 528083 = 792125) B792125
theorem B593635 : Blo 350755 593635 := bstep (se 1 (by rfl) ⟨445226, by rfl⟩ : syracuseStep 593635 = 890453) B890453
theorem B528113 : Blo 350755 528113 := bstep (se 2 (by rfl) ⟨198042, by rfl⟩ : syracuseStep 528113 = 396085) B396085
theorem B528131 : Blo 350755 528131 := bstep (se 1 (by rfl) ⟨396098, by rfl⟩ : syracuseStep 528131 = 792197) B792197
theorem B790289 : Blo 350755 790289 := bstep (se 2 (by rfl) ⟨296358, by rfl⟩ : syracuseStep 790289 = 592717) B592717
theorem B397075 : Blo 350755 397075 := bstep (se 1 (by rfl) ⟨297806, by rfl⟩ : syracuseStep 397075 = 595613) B595613
theorem B528161 : Blo 350755 528161 := bstep (se 2 (by rfl) ⟨198060, by rfl⟩ : syracuseStep 528161 = 396121) B396121
theorem B790307 : Blo 350755 790307 := bstep (se 1 (by rfl) ⟨592730, by rfl⟩ : syracuseStep 790307 = 1185461) B1185461
theorem B528179 : Blo 350755 528179 := bstep (se 1 (by rfl) ⟨396134, by rfl⟩ : syracuseStep 528179 = 792269) B792269
theorem B528209 : Blo 350755 528209 := bstep (se 2 (by rfl) ⟨198078, by rfl⟩ : syracuseStep 528209 = 396157) B396157
theorem B528227 : Blo 350755 528227 := bstep (se 1 (by rfl) ⟨396170, by rfl⟩ : syracuseStep 528227 = 792341) B792341
theorem B593777 : Blo 350755 593777 := bstep (se 2 (by rfl) ⟨222666, by rfl⟩ : syracuseStep 593777 = 445333) B445333
theorem B528257 : Blo 350755 528257 := bstep (se 2 (by rfl) ⟨198096, by rfl⟩ : syracuseStep 528257 = 396193) B396193
theorem B528275 : Blo 350755 528275 := bstep (se 1 (by rfl) ⟨396206, by rfl⟩ : syracuseStep 528275 = 792413) B792413
theorem B397219 : Blo 350755 397219 := bstep (se 1 (by rfl) ⟨297914, by rfl⟩ : syracuseStep 397219 = 595829) B595829
theorem B528305 : Blo 350755 528305 := bstep (se 2 (by rfl) ⟨198114, by rfl⟩ : syracuseStep 528305 = 396229) B396229
theorem B528323 : Blo 350755 528323 := bstep (se 1 (by rfl) ⟨396242, by rfl⟩ : syracuseStep 528323 = 792485) B792485
theorem B11407301 : Blo 350755 11407301 := bstep (se 4 (by rfl) ⟨1069434, by rfl⟩ : syracuseStep 11407301 = 2138869) B2138869
theorem B528353 : Blo 350755 528353 := bstep (se 2 (by rfl) ⟨198132, by rfl⟩ : syracuseStep 528353 = 396265) B396265
theorem B888803 : Blo 350755 888803 := bstep (se 1 (by rfl) ⟨666602, by rfl⟩ : syracuseStep 888803 = 1333205) B1333205
theorem B1609699 : Blo 350755 1609699 := bstep (se 1 (by rfl) ⟨1207274, by rfl⟩ : syracuseStep 1609699 = 2414549) B2414549
theorem B593905 : Blo 350755 593905 := bstep (se 2 (by rfl) ⟨222714, by rfl⟩ : syracuseStep 593905 = 445429) B445429
theorem B528371 : Blo 350755 528371 := bstep (se 1 (by rfl) ⟨396278, by rfl⟩ : syracuseStep 528371 = 792557) B792557
theorem B528401 : Blo 350755 528401 := bstep (se 2 (by rfl) ⟨198150, by rfl⟩ : syracuseStep 528401 = 396301) B396301
theorem B593939 : Blo 350755 593939 := bstep (se 1 (by rfl) ⟨445454, by rfl⟩ : syracuseStep 593939 = 890909) B890909
theorem B528419 : Blo 350755 528419 := bstep (se 1 (by rfl) ⟨396314, by rfl⟩ : syracuseStep 528419 = 792629) B792629
theorem B790577 : Blo 350755 790577 := bstep (se 2 (by rfl) ⟨296466, by rfl⟩ : syracuseStep 790577 = 592933) B592933
theorem B1380401 : Blo 350755 1380401 := bstep (se 2 (by rfl) ⟨517650, by rfl⟩ : syracuseStep 1380401 = 1035301) B1035301
theorem B397363 : Blo 350755 397363 := bstep (se 1 (by rfl) ⟨298022, by rfl⟩ : syracuseStep 397363 = 596045) B596045
theorem B528449 : Blo 350755 528449 := bstep (se 2 (by rfl) ⟨198168, by rfl⟩ : syracuseStep 528449 = 396337) B396337
theorem B790595 : Blo 350755 790595 := bstep (se 1 (by rfl) ⟨592946, by rfl⟩ : syracuseStep 790595 = 1185893) B1185893
theorem B528467 : Blo 350755 528467 := bstep (se 1 (by rfl) ⟨396350, by rfl⟩ : syracuseStep 528467 = 792701) B792701
theorem B528497 : Blo 350755 528497 := bstep (se 2 (by rfl) ⟨198186, by rfl⟩ : syracuseStep 528497 = 396373) B396373
theorem B528515 : Blo 350755 528515 := bstep (se 1 (by rfl) ⟨396386, by rfl⟩ : syracuseStep 528515 = 792773) B792773
theorem B594067 : Blo 350755 594067 := bstep (se 1 (by rfl) ⟨445550, by rfl⟩ : syracuseStep 594067 = 891101) B891101
theorem B528545 : Blo 350755 528545 := bstep (se 2 (by rfl) ⟨198204, by rfl⟩ : syracuseStep 528545 = 396409) B396409
theorem B888995 : Blo 350755 888995 := bstep (se 1 (by rfl) ⟨666746, by rfl⟩ : syracuseStep 888995 = 1333493) B1333493
theorem B528563 : Blo 350755 528563 := bstep (se 1 (by rfl) ⟨396422, by rfl⟩ : syracuseStep 528563 = 792845) B792845
theorem B397507 : Blo 350755 397507 := bstep (se 1 (by rfl) ⟨298130, by rfl⟩ : syracuseStep 397507 = 596261) B596261
theorem B1183949 : Blo 350755 1183949 := bstep (se 3 (by rfl) ⟨221990, by rfl⟩ : syracuseStep 1183949 = 443981) B443981
theorem B528593 : Blo 350755 528593 := bstep (se 2 (by rfl) ⟨198222, by rfl⟩ : syracuseStep 528593 = 396445) B396445
theorem B528611 : Blo 350755 528611 := bstep (se 1 (by rfl) ⟨396458, by rfl⟩ : syracuseStep 528611 = 792917) B792917
theorem B528641 : Blo 350755 528641 := bstep (se 2 (by rfl) ⟨198240, by rfl⟩ : syracuseStep 528641 = 396481) B396481
theorem B1184003 : Blo 350755 1184003 := bstep (se 1 (by rfl) ⟨888002, by rfl⟩ : syracuseStep 1184003 = 1776005) B1776005
theorem B528659 : Blo 350755 528659 := bstep (se 1 (by rfl) ⟨396494, by rfl⟩ : syracuseStep 528659 = 792989) B792989
theorem B594209 : Blo 350755 594209 := bstep (se 2 (by rfl) ⟨222828, by rfl⟩ : syracuseStep 594209 = 445657) B445657
theorem B528689 : Blo 350755 528689 := bstep (se 2 (by rfl) ⟨198258, by rfl⟩ : syracuseStep 528689 = 396517) B396517
theorem B528707 : Blo 350755 528707 := bstep (se 1 (by rfl) ⟨396530, by rfl⟩ : syracuseStep 528707 = 793061) B793061
theorem B790865 : Blo 350755 790865 := bstep (se 2 (by rfl) ⟨296574, by rfl⟩ : syracuseStep 790865 = 593149) B593149
theorem B397651 : Blo 350755 397651 := bstep (se 1 (by rfl) ⟨298238, by rfl⟩ : syracuseStep 397651 = 596477) B596477
theorem B528737 : Blo 350755 528737 := bstep (se 2 (by rfl) ⟨198276, by rfl⟩ : syracuseStep 528737 = 396553) B396553
theorem B790883 : Blo 350755 790883 := bstep (se 1 (by rfl) ⟨593162, by rfl⟩ : syracuseStep 790883 = 1186325) B1186325
theorem B528755 : Blo 350755 528755 := bstep (se 1 (by rfl) ⟨396566, by rfl⟩ : syracuseStep 528755 = 793133) B793133
theorem B528785 : Blo 350755 528785 := bstep (se 2 (by rfl) ⟨198294, by rfl⟩ : syracuseStep 528785 = 396589) B396589
theorem B594337 : Blo 350755 594337 := bstep (se 2 (by rfl) ⟨222876, by rfl⟩ : syracuseStep 594337 = 445753) B445753
theorem B528803 : Blo 350755 528803 := bstep (se 1 (by rfl) ⟨396602, by rfl⟩ : syracuseStep 528803 = 793205) B793205
theorem B528833 : Blo 350755 528833 := bstep (se 2 (by rfl) ⟨198312, by rfl⟩ : syracuseStep 528833 = 396625) B396625
theorem B627139 : Blo 350755 627139 := bstep (se 1 (by rfl) ⟨470354, by rfl⟩ : syracuseStep 627139 = 940709) B940709
theorem B594371 : Blo 350755 594371 := bstep (se 1 (by rfl) ⟨445778, by rfl⟩ : syracuseStep 594371 = 891557) B891557
theorem B1511885 : Blo 350755 1511885 := bstep (se 3 (by rfl) ⟨283478, by rfl⟩ : syracuseStep 1511885 = 566957) B566957
theorem B528851 : Blo 350755 528851 := bstep (se 1 (by rfl) ⟨396638, by rfl⟩ : syracuseStep 528851 = 793277) B793277
theorem B397795 : Blo 350755 397795 := bstep (se 1 (by rfl) ⟨298346, by rfl⟩ : syracuseStep 397795 = 596693) B596693
theorem B528881 : Blo 350755 528881 := bstep (se 2 (by rfl) ⟨198330, by rfl⟩ : syracuseStep 528881 = 396661) B396661
theorem B922097 : Blo 350755 922097 := bstep (se 2 (by rfl) ⟨345786, by rfl⟩ : syracuseStep 922097 = 691573) B691573
theorem B528899 : Blo 350755 528899 := bstep (se 1 (by rfl) ⟨396674, by rfl⟩ : syracuseStep 528899 = 793349) B793349
theorem B1184273 : Blo 350755 1184273 := bstep (se 2 (by rfl) ⟨444102, by rfl⟩ : syracuseStep 1184273 = 888205) B888205
theorem B528929 : Blo 350755 528929 := bstep (se 2 (by rfl) ⟨198348, by rfl⟩ : syracuseStep 528929 = 396697) B396697
theorem B528947 : Blo 350755 528947 := bstep (se 1 (by rfl) ⟨396710, by rfl⟩ : syracuseStep 528947 = 793421) B793421
theorem B594499 : Blo 350755 594499 := bstep (se 1 (by rfl) ⟨445874, by rfl⟩ : syracuseStep 594499 = 891749) B891749
theorem B528977 : Blo 350755 528977 := bstep (se 2 (by rfl) ⟨198366, by rfl⟩ : syracuseStep 528977 = 396733) B396733
theorem B528995 : Blo 350755 528995 := bstep (se 1 (by rfl) ⟨396746, by rfl⟩ : syracuseStep 528995 = 793493) B793493
theorem B791153 : Blo 350755 791153 := bstep (se 2 (by rfl) ⟨296682, by rfl⟩ : syracuseStep 791153 = 593365) B593365
theorem B397939 : Blo 350755 397939 := bstep (se 1 (by rfl) ⟨298454, by rfl⟩ : syracuseStep 397939 = 596909) B596909
theorem B529025 : Blo 350755 529025 := bstep (se 2 (by rfl) ⟨198384, by rfl⟩ : syracuseStep 529025 = 396769) B396769
theorem B791171 : Blo 350755 791171 := bstep (se 1 (by rfl) ⟨593378, by rfl⟩ : syracuseStep 791171 = 1186757) B1186757
theorem B529043 : Blo 350755 529043 := bstep (se 1 (by rfl) ⟨396782, by rfl⟩ : syracuseStep 529043 = 793565) B793565
theorem B529073 : Blo 350755 529073 := bstep (se 2 (by rfl) ⟨198402, by rfl⟩ : syracuseStep 529073 = 396805) B396805
theorem B529091 : Blo 350755 529091 := bstep (se 1 (by rfl) ⟨396818, by rfl⟩ : syracuseStep 529091 = 793637) B793637
theorem B594641 : Blo 350755 594641 := bstep (se 2 (by rfl) ⟨222990, by rfl⟩ : syracuseStep 594641 = 445981) B445981
theorem B529121 : Blo 350755 529121 := bstep (se 2 (by rfl) ⟨198420, by rfl⟩ : syracuseStep 529121 = 396841) B396841
theorem B529139 : Blo 350755 529139 := bstep (se 1 (by rfl) ⟨396854, by rfl⟩ : syracuseStep 529139 = 793709) B793709
theorem B398083 : Blo 350755 398083 := bstep (se 1 (by rfl) ⟨298562, by rfl⟩ : syracuseStep 398083 = 597125) B597125
theorem B529169 : Blo 350755 529169 := bstep (se 2 (by rfl) ⟨198438, by rfl⟩ : syracuseStep 529169 = 396877) B396877
theorem B561953 : Blo 350755 561953 := bstep (se 2 (by rfl) ⟨210732, by rfl⟩ : syracuseStep 561953 = 421465) B421465
theorem B529187 : Blo 350755 529187 := bstep (se 1 (by rfl) ⟨396890, by rfl⟩ : syracuseStep 529187 = 793781) B793781
theorem B529217 : Blo 350755 529217 := bstep (se 2 (by rfl) ⟨198456, by rfl⟩ : syracuseStep 529217 = 396913) B396913
theorem B594769 : Blo 350755 594769 := bstep (se 2 (by rfl) ⟨223038, by rfl⟩ : syracuseStep 594769 = 446077) B446077
theorem B529235 : Blo 350755 529235 := bstep (se 1 (by rfl) ⟨396926, by rfl⟩ : syracuseStep 529235 = 793853) B793853
theorem B529265 : Blo 350755 529265 := bstep (se 2 (by rfl) ⟨198474, by rfl⟩ : syracuseStep 529265 = 396949) B396949
theorem B2691953 : Blo 350755 2691953 := bstep (se 2 (by rfl) ⟨1009482, by rfl⟩ : syracuseStep 2691953 = 2018965) B2018965
theorem B594803 : Blo 350755 594803 := bstep (se 1 (by rfl) ⟨446102, by rfl⟩ : syracuseStep 594803 = 892205) B892205
theorem B529283 : Blo 350755 529283 := bstep (se 1 (by rfl) ⟨396962, by rfl⟩ : syracuseStep 529283 = 793925) B793925
theorem B791441 : Blo 350755 791441 := bstep (se 2 (by rfl) ⟨296790, by rfl⟩ : syracuseStep 791441 = 593581) B593581
theorem B398227 : Blo 350755 398227 := bstep (se 1 (by rfl) ⟨298670, by rfl⟩ : syracuseStep 398227 = 597341) B597341
theorem B529313 : Blo 350755 529313 := bstep (se 2 (by rfl) ⟨198492, by rfl⟩ : syracuseStep 529313 = 396985) B396985
theorem B791459 : Blo 350755 791459 := bstep (se 1 (by rfl) ⟨593594, by rfl⟩ : syracuseStep 791459 = 1187189) B1187189
theorem B529331 : Blo 350755 529331 := bstep (se 1 (by rfl) ⟨396998, by rfl⟩ : syracuseStep 529331 = 793997) B793997
theorem B529361 : Blo 350755 529361 := bstep (se 2 (by rfl) ⟨198510, by rfl⟩ : syracuseStep 529361 = 397021) B397021
theorem B529379 : Blo 350755 529379 := bstep (se 1 (by rfl) ⟨397034, by rfl⟩ : syracuseStep 529379 = 794069) B794069
theorem B594931 : Blo 350755 594931 := bstep (se 1 (by rfl) ⟨446198, by rfl⟩ : syracuseStep 594931 = 892397) B892397
theorem B529409 : Blo 350755 529409 := bstep (se 2 (by rfl) ⟨198528, by rfl⟩ : syracuseStep 529409 = 397057) B397057
theorem B529427 : Blo 350755 529427 := bstep (se 1 (by rfl) ⟨397070, by rfl⟩ : syracuseStep 529427 = 794141) B794141
theorem B398371 : Blo 350755 398371 := bstep (se 1 (by rfl) ⟨298778, by rfl⟩ : syracuseStep 398371 = 597557) B597557
theorem B1184813 : Blo 350755 1184813 := bstep (se 3 (by rfl) ⟨222152, by rfl⟩ : syracuseStep 1184813 = 444305) B444305
theorem B529457 : Blo 350755 529457 := bstep (se 2 (by rfl) ⟨198546, by rfl⟩ : syracuseStep 529457 = 397093) B397093
theorem B529475 : Blo 350755 529475 := bstep (se 1 (by rfl) ⟨397106, by rfl⟩ : syracuseStep 529475 = 794213) B794213
theorem B889937 : Blo 350755 889937 := bstep (se 2 (by rfl) ⟨333726, by rfl⟩ : syracuseStep 889937 = 667453) B667453
theorem B529505 : Blo 350755 529505 := bstep (se 2 (by rfl) ⟨198564, by rfl⟩ : syracuseStep 529505 = 397129) B397129
theorem B1184867 : Blo 350755 1184867 := bstep (se 1 (by rfl) ⟨888650, by rfl⟩ : syracuseStep 1184867 = 1777301) B1777301
theorem B2266211 : Blo 350755 2266211 := bstep (se 1 (by rfl) ⟨1699658, by rfl⟩ : syracuseStep 2266211 = 3399317) B3399317
theorem B529523 : Blo 350755 529523 := bstep (se 1 (by rfl) ⟨397142, by rfl⟩ : syracuseStep 529523 = 794285) B794285
theorem B595073 : Blo 350755 595073 := bstep (se 2 (by rfl) ⟨223152, by rfl⟩ : syracuseStep 595073 = 446305) B446305
theorem B889987 : Blo 350755 889987 := bstep (se 1 (by rfl) ⟨667490, by rfl⟩ : syracuseStep 889987 = 1334981) B1334981
theorem B529553 : Blo 350755 529553 := bstep (se 2 (by rfl) ⟨198582, by rfl⟩ : syracuseStep 529553 = 397165) B397165
theorem B529571 : Blo 350755 529571 := bstep (se 1 (by rfl) ⟨397178, by rfl⟩ : syracuseStep 529571 = 794357) B794357
theorem B791729 : Blo 350755 791729 := bstep (se 2 (by rfl) ⟨296898, by rfl⟩ : syracuseStep 791729 = 593797) B593797
theorem B398515 : Blo 350755 398515 := bstep (se 1 (by rfl) ⟨298886, by rfl⟩ : syracuseStep 398515 = 597773) B597773
theorem B529601 : Blo 350755 529601 := bstep (se 2 (by rfl) ⟨198600, by rfl⟩ : syracuseStep 529601 = 397201) B397201
theorem B791747 : Blo 350755 791747 := bstep (se 1 (by rfl) ⟨593810, by rfl⟩ : syracuseStep 791747 = 1187621) B1187621
theorem B1905869 : Blo 350755 1905869 := bstep (se 3 (by rfl) ⟨357350, by rfl⟩ : syracuseStep 1905869 = 714701) B714701
theorem B1021133 : Blo 350755 1021133 := bstep (se 3 (by rfl) ⟨191462, by rfl⟩ : syracuseStep 1021133 = 382925) B382925
theorem B529619 : Blo 350755 529619 := bstep (se 1 (by rfl) ⟨397214, by rfl⟩ : syracuseStep 529619 = 794429) B794429
theorem B529649 : Blo 350755 529649 := bstep (se 2 (by rfl) ⟨198618, by rfl⟩ : syracuseStep 529649 = 397237) B397237
theorem B595201 : Blo 350755 595201 := bstep (se 2 (by rfl) ⟨223200, by rfl⟩ : syracuseStep 595201 = 446401) B446401
theorem B529667 : Blo 350755 529667 := bstep (se 1 (by rfl) ⟨397250, by rfl⟩ : syracuseStep 529667 = 794501) B794501
theorem B890129 : Blo 350755 890129 := bstep (se 2 (by rfl) ⟨333798, by rfl⟩ : syracuseStep 890129 = 667597) B667597
theorem B529697 : Blo 350755 529697 := bstep (se 2 (by rfl) ⟨198636, by rfl⟩ : syracuseStep 529697 = 397273) B397273
theorem B595235 : Blo 350755 595235 := bstep (se 1 (by rfl) ⟨446426, by rfl⟩ : syracuseStep 595235 = 892853) B892853
theorem B529715 : Blo 350755 529715 := bstep (se 1 (by rfl) ⟨397286, by rfl⟩ : syracuseStep 529715 = 794573) B794573
theorem B398659 : Blo 350755 398659 := bstep (se 1 (by rfl) ⟨298994, by rfl⟩ : syracuseStep 398659 = 597989) B597989
theorem B529745 : Blo 350755 529745 := bstep (se 2 (by rfl) ⟨198654, by rfl⟩ : syracuseStep 529745 = 397309) B397309
theorem B529763 : Blo 350755 529763 := bstep (se 1 (by rfl) ⟨397322, by rfl⟩ : syracuseStep 529763 = 794645) B794645
theorem B1185137 : Blo 350755 1185137 := bstep (se 2 (by rfl) ⟨444426, by rfl⟩ : syracuseStep 1185137 = 888853) B888853
theorem B529793 : Blo 350755 529793 := bstep (se 2 (by rfl) ⟨198672, by rfl⟩ : syracuseStep 529793 = 397345) B397345
theorem B529811 : Blo 350755 529811 := bstep (se 1 (by rfl) ⟨397358, by rfl⟩ : syracuseStep 529811 = 794717) B794717
theorem B595363 : Blo 350755 595363 := bstep (se 1 (by rfl) ⟨446522, by rfl⟩ : syracuseStep 595363 = 893045) B893045
theorem B529841 : Blo 350755 529841 := bstep (se 2 (by rfl) ⟨198690, by rfl⟩ : syracuseStep 529841 = 397381) B397381
theorem B529859 : Blo 350755 529859 := bstep (se 1 (by rfl) ⟨397394, by rfl⟩ : syracuseStep 529859 = 794789) B794789
theorem B792017 : Blo 350755 792017 := bstep (se 2 (by rfl) ⟨297006, by rfl⟩ : syracuseStep 792017 = 594013) B594013
theorem B398803 : Blo 350755 398803 := bstep (se 1 (by rfl) ⟨299102, by rfl⟩ : syracuseStep 398803 = 598205) B598205
theorem B529889 : Blo 350755 529889 := bstep (se 2 (by rfl) ⟨198708, by rfl⟩ : syracuseStep 529889 = 397417) B397417
theorem B792035 : Blo 350755 792035 := bstep (se 1 (by rfl) ⟨594026, by rfl⟩ : syracuseStep 792035 = 1188053) B1188053
theorem B529907 : Blo 350755 529907 := bstep (se 1 (by rfl) ⟨397430, by rfl⟩ : syracuseStep 529907 = 794861) B794861
theorem B529937 : Blo 350755 529937 := bstep (se 2 (by rfl) ⟨198726, by rfl⟩ : syracuseStep 529937 = 397453) B397453
theorem B529955 : Blo 350755 529955 := bstep (se 1 (by rfl) ⟨397466, by rfl⟩ : syracuseStep 529955 = 794933) B794933
theorem B595505 : Blo 350755 595505 := bstep (se 2 (by rfl) ⟨223314, by rfl⟩ : syracuseStep 595505 = 446629) B446629
theorem B529985 : Blo 350755 529985 := bstep (se 2 (by rfl) ⟨198744, by rfl⟩ : syracuseStep 529985 = 397489) B397489
theorem B530003 : Blo 350755 530003 := bstep (se 1 (by rfl) ⟨397502, by rfl⟩ : syracuseStep 530003 = 795005) B795005
theorem B398947 : Blo 350755 398947 := bstep (se 1 (by rfl) ⟨299210, by rfl⟩ : syracuseStep 398947 = 598421) B598421
theorem B530033 : Blo 350755 530033 := bstep (se 2 (by rfl) ⟨198762, by rfl⟩ : syracuseStep 530033 = 397525) B397525
theorem B530051 : Blo 350755 530051 := bstep (se 1 (by rfl) ⟨397538, by rfl⟩ : syracuseStep 530051 = 795077) B795077
theorem B530081 : Blo 350755 530081 := bstep (se 2 (by rfl) ⟨198780, by rfl⟩ : syracuseStep 530081 = 397561) B397561
theorem B595633 : Blo 350755 595633 := bstep (se 2 (by rfl) ⟨223362, by rfl⟩ : syracuseStep 595633 = 446725) B446725
theorem B530099 : Blo 350755 530099 := bstep (se 1 (by rfl) ⟨397574, by rfl⟩ : syracuseStep 530099 = 795149) B795149
theorem B530129 : Blo 350755 530129 := bstep (se 2 (by rfl) ⟨198798, by rfl⟩ : syracuseStep 530129 = 397597) B397597
theorem B595667 : Blo 350755 595667 := bstep (se 1 (by rfl) ⟨446750, by rfl⟩ : syracuseStep 595667 = 893501) B893501
theorem B530147 : Blo 350755 530147 := bstep (se 1 (by rfl) ⟨397610, by rfl⟩ : syracuseStep 530147 = 795221) B795221
theorem B431843 : Blo 350755 431843 := bstep (se 1 (by rfl) ⟨323882, by rfl⟩ : syracuseStep 431843 = 647765) B647765
theorem B792305 : Blo 350755 792305 := bstep (se 2 (by rfl) ⟨297114, by rfl⟩ : syracuseStep 792305 = 594229) B594229
theorem B399091 : Blo 350755 399091 := bstep (se 1 (by rfl) ⟨299318, by rfl⟩ : syracuseStep 399091 = 598637) B598637
theorem B530177 : Blo 350755 530177 := bstep (se 2 (by rfl) ⟨198816, by rfl⟩ : syracuseStep 530177 = 397633) B397633
theorem B792323 : Blo 350755 792323 := bstep (se 1 (by rfl) ⟨594242, by rfl⟩ : syracuseStep 792323 = 1188485) B1188485
theorem B530195 : Blo 350755 530195 := bstep (se 1 (by rfl) ⟨397646, by rfl⟩ : syracuseStep 530195 = 795293) B795293
theorem B530225 : Blo 350755 530225 := bstep (se 2 (by rfl) ⟨198834, by rfl⟩ : syracuseStep 530225 = 397669) B397669
theorem B530243 : Blo 350755 530243 := bstep (se 1 (by rfl) ⟨397682, by rfl⟩ : syracuseStep 530243 = 795365) B795365
theorem B595795 : Blo 350755 595795 := bstep (se 1 (by rfl) ⟨446846, by rfl⟩ : syracuseStep 595795 = 893693) B893693
theorem B530273 : Blo 350755 530273 := bstep (se 2 (by rfl) ⟨198852, by rfl⟩ : syracuseStep 530273 = 397705) B397705
theorem B530291 : Blo 350755 530291 := bstep (se 1 (by rfl) ⟨397718, by rfl⟩ : syracuseStep 530291 = 795437) B795437
theorem B1185677 : Blo 350755 1185677 := bstep (se 3 (by rfl) ⟨222314, by rfl⟩ : syracuseStep 1185677 = 444629) B444629
theorem B530321 : Blo 350755 530321 := bstep (se 2 (by rfl) ⟨198870, by rfl⟩ : syracuseStep 530321 = 397741) B397741
theorem B530339 : Blo 350755 530339 := bstep (se 1 (by rfl) ⟨397754, by rfl⟩ : syracuseStep 530339 = 795509) B795509
theorem B530369 : Blo 350755 530369 := bstep (se 2 (by rfl) ⟨198888, by rfl⟩ : syracuseStep 530369 = 397777) B397777
theorem B1185731 : Blo 350755 1185731 := bstep (se 1 (by rfl) ⟨889298, by rfl⟩ : syracuseStep 1185731 = 1778597) B1778597
theorem B530387 : Blo 350755 530387 := bstep (se 1 (by rfl) ⟨397790, by rfl⟩ : syracuseStep 530387 = 795581) B795581
theorem B595937 : Blo 350755 595937 := bstep (se 2 (by rfl) ⟨223476, by rfl⟩ : syracuseStep 595937 = 446953) B446953
theorem B2529251 : Blo 350755 2529251 := bstep (se 1 (by rfl) ⟨1896938, by rfl⟩ : syracuseStep 2529251 = 3793877) B3793877
theorem B530417 : Blo 350755 530417 := bstep (se 2 (by rfl) ⟨198906, by rfl⟩ : syracuseStep 530417 = 397813) B397813
theorem B530435 : Blo 350755 530435 := bstep (se 1 (by rfl) ⟨397826, by rfl⟩ : syracuseStep 530435 = 795653) B795653
theorem B792593 : Blo 350755 792593 := bstep (se 2 (by rfl) ⟨297222, by rfl⟩ : syracuseStep 792593 = 594445) B594445
theorem B530465 : Blo 350755 530465 := bstep (se 2 (by rfl) ⟨198924, by rfl⟩ : syracuseStep 530465 = 397849) B397849
theorem B792611 : Blo 350755 792611 := bstep (se 1 (by rfl) ⟨594458, by rfl⟩ : syracuseStep 792611 = 1188917) B1188917
theorem B530483 : Blo 350755 530483 := bstep (se 1 (by rfl) ⟨397862, by rfl⟩ : syracuseStep 530483 = 795725) B795725
theorem B563267 : Blo 350755 563267 := bstep (se 1 (by rfl) ⟨422450, by rfl⟩ : syracuseStep 563267 = 844901) B844901
theorem B530513 : Blo 350755 530513 := bstep (se 2 (by rfl) ⟨198942, by rfl⟩ : syracuseStep 530513 = 397885) B397885
theorem B596065 : Blo 350755 596065 := bstep (se 2 (by rfl) ⟨223524, by rfl⟩ : syracuseStep 596065 = 447049) B447049
theorem B530531 : Blo 350755 530531 := bstep (se 1 (by rfl) ⟨397898, by rfl⟩ : syracuseStep 530531 = 795797) B795797
theorem B530561 : Blo 350755 530561 := bstep (se 2 (by rfl) ⟨198960, by rfl⟩ : syracuseStep 530561 = 397921) B397921
theorem B596099 : Blo 350755 596099 := bstep (se 1 (by rfl) ⟨447074, by rfl⟩ : syracuseStep 596099 = 894149) B894149
theorem B530579 : Blo 350755 530579 := bstep (se 1 (by rfl) ⟨397934, by rfl⟩ : syracuseStep 530579 = 795869) B795869
theorem B530609 : Blo 350755 530609 := bstep (se 2 (by rfl) ⟨198978, by rfl⟩ : syracuseStep 530609 = 397957) B397957
theorem B530627 : Blo 350755 530627 := bstep (se 1 (by rfl) ⟨397970, by rfl⟩ : syracuseStep 530627 = 795941) B795941
theorem B1186001 : Blo 350755 1186001 := bstep (se 2 (by rfl) ⟨444750, by rfl⟩ : syracuseStep 1186001 = 889501) B889501
theorem B530657 : Blo 350755 530657 := bstep (se 2 (by rfl) ⟨198996, by rfl⟩ : syracuseStep 530657 = 397993) B397993
theorem B1775843 : Blo 350755 1775843 := bstep (se 1 (by rfl) ⟨1331882, by rfl⟩ : syracuseStep 1775843 = 2663765) B2663765
theorem B891121 : Blo 350755 891121 := bstep (se 2 (by rfl) ⟨334170, by rfl⟩ : syracuseStep 891121 = 668341) B668341
theorem B530675 : Blo 350755 530675 := bstep (se 1 (by rfl) ⟨398006, by rfl⟩ : syracuseStep 530675 = 796013) B796013
theorem B596227 : Blo 350755 596227 := bstep (se 1 (by rfl) ⟨447170, by rfl⟩ : syracuseStep 596227 = 894341) B894341
theorem B530705 : Blo 350755 530705 := bstep (se 2 (by rfl) ⟨199014, by rfl⟩ : syracuseStep 530705 = 398029) B398029
theorem B530723 : Blo 350755 530723 := bstep (se 1 (by rfl) ⟨398042, by rfl⟩ : syracuseStep 530723 = 796085) B796085
theorem B792881 : Blo 350755 792881 := bstep (se 2 (by rfl) ⟨297330, by rfl⟩ : syracuseStep 792881 = 594661) B594661
theorem B530753 : Blo 350755 530753 := bstep (se 2 (by rfl) ⟨199032, by rfl⟩ : syracuseStep 530753 = 398065) B398065
theorem B792899 : Blo 350755 792899 := bstep (se 1 (by rfl) ⟨594674, by rfl⟩ : syracuseStep 792899 = 1189349) B1189349
theorem B530771 : Blo 350755 530771 := bstep (se 1 (by rfl) ⟨398078, by rfl⟩ : syracuseStep 530771 = 796157) B796157
theorem B530801 : Blo 350755 530801 := bstep (se 2 (by rfl) ⟨199050, by rfl⟩ : syracuseStep 530801 = 398101) B398101
theorem B530819 : Blo 350755 530819 := bstep (se 1 (by rfl) ⟨398114, by rfl⟩ : syracuseStep 530819 = 796229) B796229
theorem B596369 : Blo 350755 596369 := bstep (se 2 (by rfl) ⟨223638, by rfl⟩ : syracuseStep 596369 = 447277) B447277
theorem B530849 : Blo 350755 530849 := bstep (se 2 (by rfl) ⟨199068, by rfl⟩ : syracuseStep 530849 = 398137) B398137
theorem B530867 : Blo 350755 530867 := bstep (se 1 (by rfl) ⟨398150, by rfl⟩ : syracuseStep 530867 = 796301) B796301
theorem B530897 : Blo 350755 530897 := bstep (se 2 (by rfl) ⟨199086, by rfl⟩ : syracuseStep 530897 = 398173) B398173
theorem B956881 : Blo 350755 956881 := bstep (se 2 (by rfl) ⟨358830, by rfl⟩ : syracuseStep 956881 = 717661) B717661
theorem B530915 : Blo 350755 530915 := bstep (se 1 (by rfl) ⟨398186, by rfl⟩ : syracuseStep 530915 = 796373) B796373
theorem B530945 : Blo 350755 530945 := bstep (se 2 (by rfl) ⟨199104, by rfl⟩ : syracuseStep 530945 = 398209) B398209
theorem B891395 : Blo 350755 891395 := bstep (se 1 (by rfl) ⟨668546, by rfl⟩ : syracuseStep 891395 = 1337093) B1337093
theorem B596497 : Blo 350755 596497 := bstep (se 2 (by rfl) ⟨223686, by rfl⟩ : syracuseStep 596497 = 447373) B447373
theorem B530963 : Blo 350755 530963 := bstep (se 1 (by rfl) ⟨398222, by rfl⟩ : syracuseStep 530963 = 796445) B796445
theorem B530993 : Blo 350755 530993 := bstep (se 2 (by rfl) ⟨199122, by rfl⟩ : syracuseStep 530993 = 398245) B398245
theorem B596531 : Blo 350755 596531 := bstep (se 1 (by rfl) ⟨447398, by rfl⟩ : syracuseStep 596531 = 894797) B894797
theorem B4495925 : Blo 350755 4495925 := bstep (se 5 (by rfl) ⟨210746, by rfl⟩ : syracuseStep 4495925 = 421493) B421493
theorem B531011 : Blo 350755 531011 := bstep (se 1 (by rfl) ⟨398258, by rfl⟩ : syracuseStep 531011 = 796517) B796517
theorem B793169 : Blo 350755 793169 := bstep (se 2 (by rfl) ⟨297438, by rfl⟩ : syracuseStep 793169 = 594877) B594877
theorem B531041 : Blo 350755 531041 := bstep (se 2 (by rfl) ⟨199140, by rfl⟩ : syracuseStep 531041 = 398281) B398281
theorem B793187 : Blo 350755 793187 := bstep (se 1 (by rfl) ⟨594890, by rfl⟩ : syracuseStep 793187 = 1189781) B1189781
theorem B531059 : Blo 350755 531059 := bstep (se 1 (by rfl) ⟨398294, by rfl⟩ : syracuseStep 531059 = 796589) B796589
theorem B531089 : Blo 350755 531089 := bstep (se 2 (by rfl) ⟨199158, by rfl⟩ : syracuseStep 531089 = 398317) B398317
theorem B531107 : Blo 350755 531107 := bstep (se 1 (by rfl) ⟨398330, by rfl⟩ : syracuseStep 531107 = 796661) B796661
theorem B596659 : Blo 350755 596659 := bstep (se 1 (by rfl) ⟨447494, by rfl⟩ : syracuseStep 596659 = 894989) B894989
theorem B531137 : Blo 350755 531137 := bstep (se 2 (by rfl) ⟨199176, by rfl⟩ : syracuseStep 531137 = 398353) B398353
theorem B891587 : Blo 350755 891587 := bstep (se 1 (by rfl) ⟨668690, by rfl⟩ : syracuseStep 891587 = 1337381) B1337381
theorem B531155 : Blo 350755 531155 := bstep (se 1 (by rfl) ⟨398366, by rfl⟩ : syracuseStep 531155 = 796733) B796733
theorem B563939 : Blo 350755 563939 := bstep (se 1 (by rfl) ⟨422954, by rfl⟩ : syracuseStep 563939 = 845909) B845909
theorem B3807971 : Blo 350755 3807971 := bstep (se 1 (by rfl) ⟨2855978, by rfl⟩ : syracuseStep 3807971 = 5711957) B5711957
theorem B1186541 : Blo 350755 1186541 := bstep (se 3 (by rfl) ⟨222476, by rfl⟩ : syracuseStep 1186541 = 444953) B444953
theorem B531185 : Blo 350755 531185 := bstep (se 2 (by rfl) ⟨199194, by rfl⟩ : syracuseStep 531185 = 398389) B398389
theorem B531203 : Blo 350755 531203 := bstep (se 1 (by rfl) ⟨398402, by rfl⟩ : syracuseStep 531203 = 796805) B796805
theorem B531233 : Blo 350755 531233 := bstep (se 2 (by rfl) ⟨199212, by rfl⟩ : syracuseStep 531233 = 398425) B398425
theorem B1186595 : Blo 350755 1186595 := bstep (se 1 (by rfl) ⟨889946, by rfl⟩ : syracuseStep 1186595 = 1779893) B1779893
theorem B531251 : Blo 350755 531251 := bstep (se 1 (by rfl) ⟨398438, by rfl⟩ : syracuseStep 531251 = 796877) B796877
theorem B596801 : Blo 350755 596801 := bstep (se 2 (by rfl) ⟨223800, by rfl⟩ : syracuseStep 596801 = 447601) B447601
theorem B531281 : Blo 350755 531281 := bstep (se 2 (by rfl) ⟨199230, by rfl⟩ : syracuseStep 531281 = 398461) B398461
theorem B531299 : Blo 350755 531299 := bstep (se 1 (by rfl) ⟨398474, by rfl⟩ : syracuseStep 531299 = 796949) B796949
theorem B793457 : Blo 350755 793457 := bstep (se 2 (by rfl) ⟨297546, by rfl⟩ : syracuseStep 793457 = 595093) B595093
theorem B531329 : Blo 350755 531329 := bstep (se 2 (by rfl) ⟨199248, by rfl⟩ : syracuseStep 531329 = 398497) B398497
theorem B793475 : Blo 350755 793475 := bstep (se 1 (by rfl) ⟨595106, by rfl⟩ : syracuseStep 793475 = 1190213) B1190213
theorem B531347 : Blo 350755 531347 := bstep (se 1 (by rfl) ⟨398510, by rfl⟩ : syracuseStep 531347 = 797021) B797021
theorem B531377 : Blo 350755 531377 := bstep (se 2 (by rfl) ⟨199266, by rfl⟩ : syracuseStep 531377 = 398533) B398533
theorem B596929 : Blo 350755 596929 := bstep (se 2 (by rfl) ⟨223848, by rfl⟩ : syracuseStep 596929 = 447697) B447697
theorem B531395 : Blo 350755 531395 := bstep (se 1 (by rfl) ⟨398546, by rfl⟩ : syracuseStep 531395 = 797093) B797093
theorem B531425 : Blo 350755 531425 := bstep (se 2 (by rfl) ⟨199284, by rfl⟩ : syracuseStep 531425 = 398569) B398569
theorem B596963 : Blo 350755 596963 := bstep (se 1 (by rfl) ⟨447722, by rfl⟩ : syracuseStep 596963 = 895445) B895445
theorem B531443 : Blo 350755 531443 := bstep (se 1 (by rfl) ⟨398582, by rfl⟩ : syracuseStep 531443 = 797165) B797165
theorem B1776653 : Blo 350755 1776653 := bstep (se 3 (by rfl) ⟨333122, by rfl⟩ : syracuseStep 1776653 = 666245) B666245
theorem B564241 : Blo 350755 564241 := bstep (se 2 (by rfl) ⟨211590, by rfl⟩ : syracuseStep 564241 = 423181) B423181
theorem B531473 : Blo 350755 531473 := bstep (se 2 (by rfl) ⟨199302, by rfl⟩ : syracuseStep 531473 = 398605) B398605
theorem B531491 : Blo 350755 531491 := bstep (se 1 (by rfl) ⟨398618, by rfl⟩ : syracuseStep 531491 = 797237) B797237
theorem B1186865 : Blo 350755 1186865 := bstep (se 2 (by rfl) ⟨445074, by rfl⟩ : syracuseStep 1186865 = 890149) B890149
theorem B531521 : Blo 350755 531521 := bstep (se 2 (by rfl) ⟨199320, by rfl⟩ : syracuseStep 531521 = 398641) B398641
theorem B531539 : Blo 350755 531539 := bstep (se 1 (by rfl) ⟨398654, by rfl⟩ : syracuseStep 531539 = 797309) B797309
theorem B597091 : Blo 350755 597091 := bstep (se 1 (by rfl) ⟨447818, by rfl⟩ : syracuseStep 597091 = 895637) B895637
theorem B531569 : Blo 350755 531569 := bstep (se 2 (by rfl) ⟨199338, by rfl⟩ : syracuseStep 531569 = 398677) B398677
theorem B531587 : Blo 350755 531587 := bstep (se 1 (by rfl) ⟨398690, by rfl⟩ : syracuseStep 531587 = 797381) B797381
theorem B793745 : Blo 350755 793745 := bstep (se 2 (by rfl) ⟨297654, by rfl⟩ : syracuseStep 793745 = 595309) B595309
theorem B531617 : Blo 350755 531617 := bstep (se 2 (by rfl) ⟨199356, by rfl⟩ : syracuseStep 531617 = 398713) B398713
theorem B793763 : Blo 350755 793763 := bstep (se 1 (by rfl) ⟨595322, by rfl⟩ : syracuseStep 793763 = 1190645) B1190645
theorem B531635 : Blo 350755 531635 := bstep (se 1 (by rfl) ⟨398726, by rfl⟩ : syracuseStep 531635 = 797453) B797453
theorem B531665 : Blo 350755 531665 := bstep (se 2 (by rfl) ⟨199374, by rfl⟩ : syracuseStep 531665 = 398749) B398749
theorem B564451 : Blo 350755 564451 := bstep (se 1 (by rfl) ⟨423338, by rfl⟩ : syracuseStep 564451 = 846677) B846677
theorem B531683 : Blo 350755 531683 := bstep (se 1 (by rfl) ⟨398762, by rfl⟩ : syracuseStep 531683 = 797525) B797525
theorem B597233 : Blo 350755 597233 := bstep (se 2 (by rfl) ⟨223962, by rfl⟩ : syracuseStep 597233 = 447925) B447925
theorem B531713 : Blo 350755 531713 := bstep (se 2 (by rfl) ⟨199392, by rfl⟩ : syracuseStep 531713 = 398785) B398785
theorem B1219853 : Blo 350755 1219853 := bstep (se 3 (by rfl) ⟨228722, by rfl⟩ : syracuseStep 1219853 = 457445) B457445
theorem B564497 : Blo 350755 564497 := bstep (se 2 (by rfl) ⟨211686, by rfl⟩ : syracuseStep 564497 = 423373) B423373
theorem B531731 : Blo 350755 531731 := bstep (se 1 (by rfl) ⟨398798, by rfl⟩ : syracuseStep 531731 = 797597) B797597
theorem B531761 : Blo 350755 531761 := bstep (se 2 (by rfl) ⟨199410, by rfl⟩ : syracuseStep 531761 = 398821) B398821
theorem B531779 : Blo 350755 531779 := bstep (se 1 (by rfl) ⟨398834, by rfl⟩ : syracuseStep 531779 = 797669) B797669
theorem B531809 : Blo 350755 531809 := bstep (se 2 (by rfl) ⟨199428, by rfl⟩ : syracuseStep 531809 = 398857) B398857
theorem B597361 : Blo 350755 597361 := bstep (se 2 (by rfl) ⟨224010, by rfl⟩ : syracuseStep 597361 = 448021) B448021
theorem B531827 : Blo 350755 531827 := bstep (se 1 (by rfl) ⟨398870, by rfl⟩ : syracuseStep 531827 = 797741) B797741
theorem B531857 : Blo 350755 531857 := bstep (se 2 (by rfl) ⟨199446, by rfl⟩ : syracuseStep 531857 = 398893) B398893
theorem B597395 : Blo 350755 597395 := bstep (se 1 (by rfl) ⟨448046, by rfl⟩ : syracuseStep 597395 = 896093) B896093
theorem B531875 : Blo 350755 531875 := bstep (se 1 (by rfl) ⟨398906, by rfl⟩ : syracuseStep 531875 = 797813) B797813
theorem B794033 : Blo 350755 794033 := bstep (se 2 (by rfl) ⟨297762, by rfl⟩ : syracuseStep 794033 = 595525) B595525
theorem B400819 : Blo 350755 400819 := bstep (se 1 (by rfl) ⟨300614, by rfl⟩ : syracuseStep 400819 = 601229) B601229
theorem B531905 : Blo 350755 531905 := bstep (se 2 (by rfl) ⟨199464, by rfl⟩ : syracuseStep 531905 = 398929) B398929
theorem B794051 : Blo 350755 794051 := bstep (se 1 (by rfl) ⟨595538, by rfl⟩ : syracuseStep 794051 = 1191077) B1191077
theorem B531923 : Blo 350755 531923 := bstep (se 1 (by rfl) ⟨398942, by rfl⟩ : syracuseStep 531923 = 797885) B797885
theorem B531953 : Blo 350755 531953 := bstep (se 2 (by rfl) ⟨199482, by rfl⟩ : syracuseStep 531953 = 398965) B398965
theorem B531971 : Blo 350755 531971 := bstep (se 1 (by rfl) ⟨398978, by rfl⟩ : syracuseStep 531971 = 797957) B797957
theorem B597523 : Blo 350755 597523 := bstep (se 1 (by rfl) ⟨448142, by rfl⟩ : syracuseStep 597523 = 896285) B896285
theorem B532001 : Blo 350755 532001 := bstep (se 2 (by rfl) ⟨199500, by rfl⟩ : syracuseStep 532001 = 399001) B399001
theorem B532019 : Blo 350755 532019 := bstep (se 1 (by rfl) ⟨399014, by rfl⟩ : syracuseStep 532019 = 798029) B798029
theorem B1187405 : Blo 350755 1187405 := bstep (se 3 (by rfl) ⟨222638, by rfl⟩ : syracuseStep 1187405 = 445277) B445277
theorem B532049 : Blo 350755 532049 := bstep (se 2 (by rfl) ⟨199518, by rfl⟩ : syracuseStep 532049 = 399037) B399037
theorem B532067 : Blo 350755 532067 := bstep (se 1 (by rfl) ⟨399050, by rfl⟩ : syracuseStep 532067 = 798101) B798101
theorem B892529 : Blo 350755 892529 := bstep (se 2 (by rfl) ⟨334698, by rfl⟩ : syracuseStep 892529 = 669397) B669397
theorem B532097 : Blo 350755 532097 := bstep (se 2 (by rfl) ⟨199536, by rfl⟩ : syracuseStep 532097 = 399073) B399073
theorem B1187459 : Blo 350755 1187459 := bstep (se 1 (by rfl) ⟨890594, by rfl⟩ : syracuseStep 1187459 = 1781189) B1781189
theorem B532115 : Blo 350755 532115 := bstep (se 1 (by rfl) ⟨399086, by rfl⟩ : syracuseStep 532115 = 798173) B798173
theorem B597665 : Blo 350755 597665 := bstep (se 2 (by rfl) ⟨224124, by rfl⟩ : syracuseStep 597665 = 448249) B448249
theorem B892579 : Blo 350755 892579 := bstep (se 1 (by rfl) ⟨669434, by rfl⟩ : syracuseStep 892579 = 1338869) B1338869
theorem B958157 : Blo 350755 958157 := bstep (se 3 (by rfl) ⟨179654, by rfl⟩ : syracuseStep 958157 = 359309) B359309
theorem B794321 : Blo 350755 794321 := bstep (se 2 (by rfl) ⟨297870, by rfl⟩ : syracuseStep 794321 = 595741) B595741
theorem B794339 : Blo 350755 794339 := bstep (se 1 (by rfl) ⟨595754, by rfl⟩ : syracuseStep 794339 = 1191509) B1191509
theorem B597793 : Blo 350755 597793 := bstep (se 2 (by rfl) ⟨224172, by rfl⟩ : syracuseStep 597793 = 448345) B448345
theorem B892721 : Blo 350755 892721 := bstep (se 2 (by rfl) ⟨334770, by rfl⟩ : syracuseStep 892721 = 669541) B669541
theorem B597827 : Blo 350755 597827 := bstep (se 1 (by rfl) ⟨448370, by rfl⟩ : syracuseStep 597827 = 896741) B896741
theorem B1187729 : Blo 350755 1187729 := bstep (se 2 (by rfl) ⟨445398, by rfl⟩ : syracuseStep 1187729 = 890797) B890797
theorem B958385 : Blo 350755 958385 := bstep (se 2 (by rfl) ⟨359394, by rfl⟩ : syracuseStep 958385 = 718789) B718789
theorem B597955 : Blo 350755 597955 := bstep (se 1 (by rfl) ⟨448466, by rfl⟩ : syracuseStep 597955 = 896933) B896933
theorem B794609 : Blo 350755 794609 := bstep (se 2 (by rfl) ⟨297978, by rfl⟩ : syracuseStep 794609 = 595957) B595957
theorem B794627 : Blo 350755 794627 := bstep (se 1 (by rfl) ⟨595970, by rfl⟩ : syracuseStep 794627 = 1191941) B1191941
theorem B598097 : Blo 350755 598097 := bstep (se 2 (by rfl) ⟨224286, by rfl⟩ : syracuseStep 598097 = 448573) B448573
theorem B499889 : Blo 350755 499889 := bstep (se 2 (by rfl) ⟨187458, by rfl⟩ : syracuseStep 499889 = 374917) B374917
theorem B598225 : Blo 350755 598225 := bstep (se 2 (by rfl) ⟨224334, by rfl⟩ : syracuseStep 598225 = 448669) B448669
theorem B9248995 : Blo 350755 9248995 := bstep (se 1 (by rfl) ⟨6936746, by rfl⟩ : syracuseStep 9248995 = 13873493) B13873493
theorem B598259 : Blo 350755 598259 := bstep (se 1 (by rfl) ⟨448694, by rfl⟩ : syracuseStep 598259 = 897389) B897389
theorem B499969 : Blo 350755 499969 := bstep (se 2 (by rfl) ⟨187488, by rfl⟩ : syracuseStep 499969 = 374977) B374977
theorem B2007301 : Blo 350755 2007301 := bstep (se 4 (by rfl) ⟨188184, by rfl⟩ : syracuseStep 2007301 = 376369) B376369
theorem B794897 : Blo 350755 794897 := bstep (se 2 (by rfl) ⟨298086, by rfl⟩ : syracuseStep 794897 = 596173) B596173
theorem B794915 : Blo 350755 794915 := bstep (se 1 (by rfl) ⟨596186, by rfl⟩ : syracuseStep 794915 = 1192373) B1192373
theorem B860483 : Blo 350755 860483 := bstep (se 1 (by rfl) ⟨645362, by rfl⟩ : syracuseStep 860483 = 1290725) B1290725
theorem B598387 : Blo 350755 598387 := bstep (se 1 (by rfl) ⟨448790, by rfl⟩ : syracuseStep 598387 = 897581) B897581
theorem B1188269 : Blo 350755 1188269 := bstep (se 3 (by rfl) ⟨222800, by rfl⟩ : syracuseStep 1188269 = 445601) B445601
theorem B1188323 : Blo 350755 1188323 := bstep (se 1 (by rfl) ⟨891242, by rfl⟩ : syracuseStep 1188323 = 1782485) B1782485
theorem B598529 : Blo 350755 598529 := bstep (se 2 (by rfl) ⟨224448, by rfl⟩ : syracuseStep 598529 = 448897) B448897
theorem B795185 : Blo 350755 795185 := bstep (se 2 (by rfl) ⟨298194, by rfl⟩ : syracuseStep 795185 = 596389) B596389
theorem B795203 : Blo 350755 795203 := bstep (se 1 (by rfl) ⟨596402, by rfl⟩ : syracuseStep 795203 = 1192805) B1192805
theorem B1188593 : Blo 350755 1188593 := bstep (se 2 (by rfl) ⟨445722, by rfl⟩ : syracuseStep 1188593 = 891445) B891445
theorem B566003 : Blo 350755 566003 := bstep (se 1 (by rfl) ⟨424502, by rfl⟩ : syracuseStep 566003 = 849005) B849005
theorem B893713 : Blo 350755 893713 := bstep (se 2 (by rfl) ⟨335142, by rfl⟩ : syracuseStep 893713 = 670285) B670285
theorem B795473 : Blo 350755 795473 := bstep (se 2 (by rfl) ⟨298302, by rfl⟩ : syracuseStep 795473 = 596605) B596605
theorem B795491 : Blo 350755 795491 := bstep (se 1 (by rfl) ⟨596618, by rfl⟩ : syracuseStep 795491 = 1193237) B1193237
theorem B500755 : Blo 350755 500755 := bstep (se 1 (by rfl) ⟨375566, by rfl⟩ : syracuseStep 500755 = 751133) B751133
theorem B566291 : Blo 350755 566291 := bstep (se 1 (by rfl) ⟨424718, by rfl⟩ : syracuseStep 566291 = 849437) B849437
theorem B893987 : Blo 350755 893987 := bstep (se 1 (by rfl) ⟨670490, by rfl⟩ : syracuseStep 893987 = 1340981) B1340981
theorem B1811555 : Blo 350755 1811555 := bstep (se 1 (by rfl) ⟨1358666, by rfl⟩ : syracuseStep 1811555 = 2717333) B2717333
theorem B795761 : Blo 350755 795761 := bstep (se 2 (by rfl) ⟨298410, by rfl⟩ : syracuseStep 795761 = 596821) B596821
theorem B795779 : Blo 350755 795779 := bstep (se 1 (by rfl) ⟨596834, by rfl⟩ : syracuseStep 795779 = 1193669) B1193669
theorem B894179 : Blo 350755 894179 := bstep (se 1 (by rfl) ⟨670634, by rfl⟩ : syracuseStep 894179 = 1341269) B1341269
theorem B1189133 : Blo 350755 1189133 := bstep (se 3 (by rfl) ⟨222962, by rfl⟩ : syracuseStep 1189133 = 445925) B445925
theorem B1189187 : Blo 350755 1189187 := bstep (se 1 (by rfl) ⟨891890, by rfl⟩ : syracuseStep 1189187 = 1783781) B1783781
theorem B796049 : Blo 350755 796049 := bstep (se 2 (by rfl) ⟨298518, by rfl⟩ : syracuseStep 796049 = 597037) B597037
theorem B796067 : Blo 350755 796067 := bstep (se 1 (by rfl) ⟨597050, by rfl⟩ : syracuseStep 796067 = 1194101) B1194101
theorem B4040117 : Blo 350755 4040117 := bstep (se 5 (by rfl) ⟨189380, by rfl⟩ : syracuseStep 4040117 = 378761) B378761
theorem B632291 : Blo 350755 632291 := bstep (se 1 (by rfl) ⟨474218, by rfl⟩ : syracuseStep 632291 = 948437) B948437
theorem B501233 : Blo 350755 501233 := bstep (se 2 (by rfl) ⟨187962, by rfl⟩ : syracuseStep 501233 = 375925) B375925
theorem B1189457 : Blo 350755 1189457 := bstep (se 2 (by rfl) ⟨446046, by rfl⟩ : syracuseStep 1189457 = 892093) B892093
theorem B501347 : Blo 350755 501347 := bstep (se 1 (by rfl) ⟨376010, by rfl⟩ : syracuseStep 501347 = 752021) B752021
theorem B632465 : Blo 350755 632465 := bstep (se 2 (by rfl) ⟨237174, by rfl⟩ : syracuseStep 632465 = 474349) B474349
theorem B796337 : Blo 350755 796337 := bstep (se 2 (by rfl) ⟨298626, by rfl⟩ : syracuseStep 796337 = 597253) B597253
theorem B501427 : Blo 350755 501427 := bstep (se 1 (by rfl) ⟨376070, by rfl⟩ : syracuseStep 501427 = 752141) B752141
theorem B796355 : Blo 350755 796355 := bstep (se 1 (by rfl) ⟨597266, by rfl⟩ : syracuseStep 796355 = 1194533) B1194533
theorem B567091 : Blo 350755 567091 := bstep (se 1 (by rfl) ⟨425318, by rfl⟩ : syracuseStep 567091 = 850637) B850637
theorem B1779569 : Blo 350755 1779569 := bstep (se 2 (by rfl) ⟨667338, by rfl⟩ : syracuseStep 1779569 = 1334677) B1334677
theorem B2140037 : Blo 350755 2140037 := bstep (se 4 (by rfl) ⟨200628, by rfl⟩ : syracuseStep 2140037 = 401257) B401257
theorem B567233 : Blo 350755 567233 := bstep (se 2 (by rfl) ⟨212712, by rfl⟩ : syracuseStep 567233 = 425425) B425425
theorem B796625 : Blo 350755 796625 := bstep (se 2 (by rfl) ⟨298734, by rfl⟩ : syracuseStep 796625 = 597469) B597469
theorem B567265 : Blo 350755 567265 := bstep (se 2 (by rfl) ⟨212724, by rfl⟩ : syracuseStep 567265 = 425449) B425449
theorem B9054179 : Blo 350755 9054179 := bstep (se 1 (by rfl) ⟨6790634, by rfl⟩ : syracuseStep 9054179 = 13581269) B13581269
theorem B796643 : Blo 350755 796643 := bstep (se 1 (by rfl) ⟨597482, by rfl⟩ : syracuseStep 796643 = 1194965) B1194965
theorem B2861041 : Blo 350755 2861041 := bstep (se 2 (by rfl) ⟨1072890, by rfl⟩ : syracuseStep 2861041 = 2145781) B2145781
theorem B1189997 : Blo 350755 1189997 := bstep (se 3 (by rfl) ⟨223124, by rfl⟩ : syracuseStep 1189997 = 446249) B446249
theorem B895121 : Blo 350755 895121 := bstep (se 2 (by rfl) ⟨335670, by rfl⟩ : syracuseStep 895121 = 671341) B671341
theorem B1190051 : Blo 350755 1190051 := bstep (se 1 (by rfl) ⟨892538, by rfl⟩ : syracuseStep 1190051 = 1785077) B1785077
theorem B895171 : Blo 350755 895171 := bstep (se 1 (by rfl) ⟨671378, by rfl⟩ : syracuseStep 895171 = 1342757) B1342757
theorem B2009285 : Blo 350755 2009285 := bstep (se 4 (by rfl) ⟨188370, by rfl⟩ : syracuseStep 2009285 = 376741) B376741
theorem B501985 : Blo 350755 501985 := bstep (se 2 (by rfl) ⟨188244, by rfl⟩ : syracuseStep 501985 = 376489) B376489
theorem B796913 : Blo 350755 796913 := bstep (se 2 (by rfl) ⟨298842, by rfl⟩ : syracuseStep 796913 = 597685) B597685
theorem B796931 : Blo 350755 796931 := bstep (se 1 (by rfl) ⟨597698, by rfl⟩ : syracuseStep 796931 = 1195397) B1195397
theorem B3909941 : Blo 350755 3909941 := bstep (se 5 (by rfl) ⟨183278, by rfl⟩ : syracuseStep 3909941 = 366557) B366557
theorem B895313 : Blo 350755 895313 := bstep (se 2 (by rfl) ⟨335742, by rfl⟩ : syracuseStep 895313 = 671485) B671485
theorem B1190321 : Blo 350755 1190321 := bstep (se 2 (by rfl) ⟨446370, by rfl⟩ : syracuseStep 1190321 = 892741) B892741
theorem B797201 : Blo 350755 797201 := bstep (se 2 (by rfl) ⟨298950, by rfl⟩ : syracuseStep 797201 = 597901) B597901
theorem B797219 : Blo 350755 797219 := bstep (se 1 (by rfl) ⟨597914, by rfl⟩ : syracuseStep 797219 = 1195829) B1195829
theorem B1452593 : Blo 350755 1452593 := bstep (se 2 (by rfl) ⟨544722, by rfl⟩ : syracuseStep 1452593 = 1089445) B1089445
theorem B600787 : Blo 350755 600787 := bstep (se 1 (by rfl) ⟨450590, by rfl⟩ : syracuseStep 600787 = 901181) B901181
theorem B797489 : Blo 350755 797489 := bstep (se 2 (by rfl) ⟨299058, by rfl⟩ : syracuseStep 797489 = 598117) B598117
theorem B797507 : Blo 350755 797507 := bstep (se 1 (by rfl) ⟨598130, by rfl⟩ : syracuseStep 797507 = 1196261) B1196261
theorem B666481 : Blo 350755 666481 := bstep (se 2 (by rfl) ⟨249930, by rfl⟩ : syracuseStep 666481 = 499861) B499861
theorem B568193 : Blo 350755 568193 := bstep (se 2 (by rfl) ⟨213072, by rfl⟩ : syracuseStep 568193 = 426145) B426145
theorem B502691 : Blo 350755 502691 := bstep (se 1 (by rfl) ⟨377018, by rfl⟩ : syracuseStep 502691 = 754037) B754037
theorem B1190861 : Blo 350755 1190861 := bstep (se 3 (by rfl) ⟨223286, by rfl⟩ : syracuseStep 1190861 = 446573) B446573
theorem B1190915 : Blo 350755 1190915 := bstep (se 1 (by rfl) ⟨893186, by rfl⟩ : syracuseStep 1190915 = 1786373) B1786373
theorem B797777 : Blo 350755 797777 := bstep (se 2 (by rfl) ⟨299166, by rfl⟩ : syracuseStep 797777 = 598333) B598333
theorem B797795 : Blo 350755 797795 := bstep (se 1 (by rfl) ⟨598346, by rfl⟩ : syracuseStep 797795 = 1196693) B1196693
theorem B535667 : Blo 350755 535667 := bstep (se 1 (by rfl) ⟨401750, by rfl⟩ : syracuseStep 535667 = 803501) B803501
theorem B1125571 : Blo 350755 1125571 := bstep (se 1 (by rfl) ⟨844178, by rfl⟩ : syracuseStep 1125571 = 1688357) B1688357
theorem B666883 : Blo 350755 666883 := bstep (se 1 (by rfl) ⟨500162, by rfl⟩ : syracuseStep 666883 = 1000325) B1000325
theorem B1191185 : Blo 350755 1191185 := bstep (se 2 (by rfl) ⟨446694, by rfl⟩ : syracuseStep 1191185 = 893389) B893389
theorem B1781027 : Blo 350755 1781027 := bstep (se 1 (by rfl) ⟨1335770, by rfl⟩ : syracuseStep 1781027 = 2671541) B2671541
theorem B666929 : Blo 350755 666929 := bstep (se 2 (by rfl) ⟨250098, by rfl⟩ : syracuseStep 666929 = 500197) B500197
theorem B896305 : Blo 350755 896305 := bstep (se 2 (by rfl) ⟨336114, by rfl⟩ : syracuseStep 896305 = 672229) B672229
theorem B1125713 : Blo 350755 1125713 := bstep (se 2 (by rfl) ⟨422142, by rfl⟩ : syracuseStep 1125713 = 844285) B844285
theorem B798065 : Blo 350755 798065 := bstep (se 2 (by rfl) ⟨299274, by rfl⟩ : syracuseStep 798065 = 598549) B598549
theorem B798083 : Blo 350755 798083 := bstep (se 1 (by rfl) ⟨598562, by rfl⟩ : syracuseStep 798083 = 1197125) B1197125
theorem B1125827 : Blo 350755 1125827 := bstep (se 1 (by rfl) ⟨844370, by rfl⟩ : syracuseStep 1125827 = 1688741) B1688741
theorem B2862533 : Blo 350755 2862533 := bstep (se 4 (by rfl) ⟨268362, by rfl⟩ : syracuseStep 2862533 = 536725) B536725
theorem B2043377 : Blo 350755 2043377 := bstep (se 2 (by rfl) ⟨766266, by rfl⟩ : syracuseStep 2043377 = 1532533) B1532533
theorem B503329 : Blo 350755 503329 := bstep (se 2 (by rfl) ⟨188748, by rfl⟩ : syracuseStep 503329 = 377497) B377497
theorem B896579 : Blo 350755 896579 := bstep (se 1 (by rfl) ⟨672434, by rfl⟩ : syracuseStep 896579 = 1344869) B1344869
theorem B667217 : Blo 350755 667217 := bstep (se 2 (by rfl) ⟨250206, by rfl⟩ : syracuseStep 667217 = 500413) B500413
theorem B503443 : Blo 350755 503443 := bstep (se 1 (by rfl) ⟨377582, by rfl⟩ : syracuseStep 503443 = 755165) B755165
theorem B896771 : Blo 350755 896771 := bstep (se 1 (by rfl) ⟨672578, by rfl⟩ : syracuseStep 896771 = 1345157) B1345157
theorem B1191725 : Blo 350755 1191725 := bstep (se 3 (by rfl) ⟨223448, by rfl⟩ : syracuseStep 1191725 = 446897) B446897
theorem B1191779 : Blo 350755 1191779 := bstep (se 1 (by rfl) ⟨893834, by rfl⟩ : syracuseStep 1191779 = 1787669) B1787669
theorem B1781837 : Blo 350755 1781837 := bstep (se 3 (by rfl) ⟨334094, by rfl⟩ : syracuseStep 1781837 = 668189) B668189
theorem B1192049 : Blo 350755 1192049 := bstep (se 2 (by rfl) ⟨447018, by rfl⟩ : syracuseStep 1192049 = 894037) B894037
theorem B536737 : Blo 350755 536737 := bstep (se 2 (by rfl) ⟨201276, by rfl⟩ : syracuseStep 536737 = 402553) B402553
theorem B667939 : Blo 350755 667939 := bstep (se 1 (by rfl) ⟨500954, by rfl⟩ : syracuseStep 667939 = 1001909) B1001909
theorem B1126801 : Blo 350755 1126801 := bstep (se 2 (by rfl) ⟨422550, by rfl⟩ : syracuseStep 1126801 = 845101) B845101
theorem B1290737 : Blo 350755 1290737 := bstep (se 2 (by rfl) ⟨484026, by rfl⟩ : syracuseStep 1290737 = 968053) B968053
theorem B1192589 : Blo 350755 1192589 := bstep (se 3 (by rfl) ⟨223610, by rfl⟩ : syracuseStep 1192589 = 447221) B447221
theorem B897713 : Blo 350755 897713 := bstep (se 2 (by rfl) ⟨336642, by rfl⟩ : syracuseStep 897713 = 673285) B673285
theorem B1192643 : Blo 350755 1192643 := bstep (se 1 (by rfl) ⟨894482, by rfl⟩ : syracuseStep 1192643 = 1788965) B1788965
theorem B668387 : Blo 350755 668387 := bstep (se 1 (by rfl) ⟨501290, by rfl⟩ : syracuseStep 668387 = 1002581) B1002581
theorem B897763 : Blo 350755 897763 := bstep (se 1 (by rfl) ⟨673322, by rfl⟩ : syracuseStep 897763 = 1346645) B1346645
theorem B4633357 : Blo 350755 4633357 := bstep (se 3 (by rfl) ⟨868754, by rfl⟩ : syracuseStep 4633357 = 1737509) B1737509
theorem B897905 : Blo 350755 897905 := bstep (se 2 (by rfl) ⟨336714, by rfl⟩ : syracuseStep 897905 = 673429) B673429
theorem B1192913 : Blo 350755 1192913 := bstep (se 2 (by rfl) ⟨447342, by rfl⟩ : syracuseStep 1192913 = 894685) B894685
theorem B504787 : Blo 350755 504787 := bstep (se 1 (by rfl) ⟨378590, by rfl⟩ : syracuseStep 504787 = 757181) B757181
theorem B668675 : Blo 350755 668675 := bstep (se 1 (by rfl) ⟨501506, by rfl⟩ : syracuseStep 668675 = 1003013) B1003013
theorem B2700485 : Blo 350755 2700485 := bstep (se 4 (by rfl) ⟨253170, by rfl⟩ : syracuseStep 2700485 = 506341) B506341
theorem B603379 : Blo 350755 603379 := bstep (se 1 (by rfl) ⟨452534, by rfl⟩ : syracuseStep 603379 = 905069) B905069
theorem B4502897 : Blo 350755 4502897 := bstep (se 2 (by rfl) ⟨1688586, by rfl⟩ : syracuseStep 4502897 = 3377173) B3377173
theorem B1193453 : Blo 350755 1193453 := bstep (se 3 (by rfl) ⟨223772, by rfl⟩ : syracuseStep 1193453 = 447545) B447545
theorem B1193507 : Blo 350755 1193507 := bstep (se 1 (by rfl) ⟨895130, by rfl⟩ : syracuseStep 1193507 = 1790261) B1790261
theorem B603857 : Blo 350755 603857 := bstep (se 2 (by rfl) ⟨226446, by rfl⟩ : syracuseStep 603857 = 452893) B452893
theorem B27997973 : Blo 350755 27997973 := bstep (se 6 (by rfl) ⟨656202, by rfl⟩ : syracuseStep 27997973 = 1312405) B1312405
theorem B1193777 : Blo 350755 1193777 := bstep (se 2 (by rfl) ⟨447666, by rfl⟩ : syracuseStep 1193777 = 895333) B895333
theorem B669617 : Blo 350755 669617 := bstep (se 2 (by rfl) ⟨251106, by rfl⟩ : syracuseStep 669617 = 502213) B502213
theorem B2013133 : Blo 350755 2013133 := bstep (se 3 (by rfl) ⟨377462, by rfl⟩ : syracuseStep 2013133 = 754925) B754925
theorem B1194317 : Blo 350755 1194317 := bstep (se 3 (by rfl) ⟨223934, by rfl⟩ : syracuseStep 1194317 = 447869) B447869
theorem B375139 : Blo 350755 375139 := bstep (se 1 (by rfl) ⟨281354, by rfl⟩ : syracuseStep 375139 = 562709) B562709
theorem B1194371 : Blo 350755 1194371 := bstep (se 1 (by rfl) ⟨895778, by rfl⟩ : syracuseStep 1194371 = 1791557) B1791557
theorem B4536931 : Blo 350755 4536931 := bstep (se 1 (by rfl) ⟨3402698, by rfl⟩ : syracuseStep 4536931 = 6805397) B6805397
theorem B1030765 : Blo 350755 1030765 := bstep (se 3 (by rfl) ⟨193268, by rfl⟩ : syracuseStep 1030765 = 386537) B386537
theorem B1194641 : Blo 350755 1194641 := bstep (se 2 (by rfl) ⟨447990, by rfl⟩ : syracuseStep 1194641 = 895981) B895981
theorem B506515 : Blo 350755 506515 := bstep (se 1 (by rfl) ⟨379886, by rfl⟩ : syracuseStep 506515 = 759773) B759773
theorem B670513 : Blo 350755 670513 := bstep (se 2 (by rfl) ⟨251442, by rfl⟩ : syracuseStep 670513 = 502885) B502885
theorem B1784753 : Blo 350755 1784753 := bstep (se 2 (by rfl) ⟨669282, by rfl⟩ : syracuseStep 1784753 = 1338565) B1338565
theorem B670673 : Blo 350755 670673 := bstep (se 2 (by rfl) ⟨251502, by rfl⟩ : syracuseStep 670673 = 503005) B503005
theorem B605171 : Blo 350755 605171 := bstep (se 1 (by rfl) ⟨453878, by rfl⟩ : syracuseStep 605171 = 907757) B907757
theorem B965773 : Blo 350755 965773 := bstep (se 3 (by rfl) ⟨181082, by rfl⟩ : syracuseStep 965773 = 362165) B362165
theorem B1195181 : Blo 350755 1195181 := bstep (se 3 (by rfl) ⟨224096, by rfl⟩ : syracuseStep 1195181 = 448193) B448193
theorem B1195235 : Blo 350755 1195235 := bstep (se 1 (by rfl) ⟨896426, by rfl⟩ : syracuseStep 1195235 = 1792853) B1792853
theorem B376147 : Blo 350755 376147 := bstep (se 1 (by rfl) ⟨282110, by rfl⟩ : syracuseStep 376147 = 564221) B564221
theorem B671075 : Blo 350755 671075 := bstep (se 1 (by rfl) ⟨503306, by rfl⟩ : syracuseStep 671075 = 1006613) B1006613
theorem B703907 : Blo 350755 703907 := bstep (se 1 (by rfl) ⟨527930, by rfl⟩ : syracuseStep 703907 = 1055861) B1055861
theorem B1195505 : Blo 350755 1195505 := bstep (se 2 (by rfl) ⟨448314, by rfl⟩ : syracuseStep 1195505 = 896629) B896629
theorem B998993 : Blo 350755 998993 := bstep (se 2 (by rfl) ⟨374622, by rfl⟩ : syracuseStep 998993 = 749245) B749245
theorem B2015117 : Blo 350755 2015117 := bstep (se 3 (by rfl) ⟨377834, by rfl⟩ : syracuseStep 2015117 = 755669) B755669
theorem B507809 : Blo 350755 507809 := bstep (se 2 (by rfl) ⟨190428, by rfl⟩ : syracuseStep 507809 = 380857) B380857
theorem B638929 : Blo 350755 638929 := bstep (se 2 (by rfl) ⟨239598, by rfl⟩ : syracuseStep 638929 = 479197) B479197
theorem B1196045 : Blo 350755 1196045 := bstep (se 3 (by rfl) ⟨224258, by rfl⟩ : syracuseStep 1196045 = 448517) B448517
theorem B1196099 : Blo 350755 1196099 := bstep (se 1 (by rfl) ⟨897074, by rfl⟩ : syracuseStep 1196099 = 1794149) B1794149
theorem B2441285 : Blo 350755 2441285 := bstep (se 4 (by rfl) ⟨228870, by rfl⟩ : syracuseStep 2441285 = 457741) B457741
theorem B606403 : Blo 350755 606403 := bstep (se 1 (by rfl) ⟨454802, by rfl⟩ : syracuseStep 606403 = 909605) B909605
theorem B671971 : Blo 350755 671971 := bstep (se 1 (by rfl) ⟨503978, by rfl⟩ : syracuseStep 671971 = 1007957) B1007957
theorem B999665 : Blo 350755 999665 := bstep (se 2 (by rfl) ⟨374874, by rfl⟩ : syracuseStep 999665 = 749749) B749749
theorem B377155 : Blo 350755 377155 := bstep (se 1 (by rfl) ⟨282866, by rfl⟩ : syracuseStep 377155 = 565733) B565733
theorem B1196369 : Blo 350755 1196369 := bstep (se 2 (by rfl) ⟨448638, by rfl⟩ : syracuseStep 1196369 = 897277) B897277
theorem B1786211 : Blo 350755 1786211 := bstep (se 1 (by rfl) ⟨1339658, by rfl⟩ : syracuseStep 1786211 = 2679317) B2679317
theorem B672131 : Blo 350755 672131 := bstep (se 1 (by rfl) ⟨504098, by rfl⟩ : syracuseStep 672131 = 1008197) B1008197
theorem B1131185 : Blo 350755 1131185 := bstep (se 2 (by rfl) ⟨424194, by rfl⟩ : syracuseStep 1131185 = 848389) B848389
theorem B2016049 : Blo 350755 2016049 := bstep (se 2 (by rfl) ⟨756018, by rfl⟩ : syracuseStep 2016049 = 1512037) B1512037
theorem B1196909 : Blo 350755 1196909 := bstep (se 3 (by rfl) ⟨224420, by rfl⟩ : syracuseStep 1196909 = 448841) B448841
theorem B1196963 : Blo 350755 1196963 := bstep (se 1 (by rfl) ⟨897722, by rfl⟩ : syracuseStep 1196963 = 1795445) B1795445
theorem B377779 : Blo 350755 377779 := bstep (se 1 (by rfl) ⟨283334, by rfl⟩ : syracuseStep 377779 = 566669) B566669
theorem B2999267 : Blo 350755 2999267 := bstep (se 1 (by rfl) ⟨2249450, by rfl⟩ : syracuseStep 2999267 = 4498901) B4498901
theorem B1000451 : Blo 350755 1000451 := bstep (se 1 (by rfl) ⟨750338, by rfl⟩ : syracuseStep 1000451 = 1500677) B1500677
theorem B1787021 : Blo 350755 1787021 := bstep (se 3 (by rfl) ⟨335066, by rfl⟩ : syracuseStep 1787021 = 670133) B670133
theorem B1197233 : Blo 350755 1197233 := bstep (se 2 (by rfl) ⟨448962, by rfl⟩ : syracuseStep 1197233 = 897925) B897925
theorem B4015331 : Blo 350755 4015331 := bstep (se 1 (by rfl) ⟨3011498, by rfl⟩ : syracuseStep 4015331 = 6022997) B6022997
theorem B1000781 : Blo 350755 1000781 := bstep (se 3 (by rfl) ⟨187646, by rfl⟩ : syracuseStep 1000781 = 375293) B375293
theorem B1000849 : Blo 350755 1000849 := bstep (se 2 (by rfl) ⟨375318, by rfl⟩ : syracuseStep 1000849 = 750637) B750637
theorem B673201 : Blo 350755 673201 := bstep (se 2 (by rfl) ⟨252450, by rfl⟩ : syracuseStep 673201 = 504901) B504901
theorem B476641 : Blo 350755 476641 := bstep (se 2 (by rfl) ⟨178740, by rfl⟩ : syracuseStep 476641 = 357481) B357481
theorem B443971 : Blo 350755 443971 := bstep (se 1 (by rfl) ⟨332978, by rfl⟩ : syracuseStep 443971 = 665957) B665957
theorem B1001123 : Blo 350755 1001123 := bstep (se 1 (by rfl) ⟨750842, by rfl⟩ : syracuseStep 1001123 = 1501685) B1501685
theorem B444467 : Blo 350755 444467 := bstep (se 1 (by rfl) ⟨333350, by rfl⟩ : syracuseStep 444467 = 666701) B666701
theorem B1427633 : Blo 350755 1427633 := bstep (se 2 (by rfl) ⟨535362, by rfl⟩ : syracuseStep 1427633 = 1070725) B1070725
theorem B1362125 : Blo 350755 1362125 := bstep (se 3 (by rfl) ⟨255398, by rfl⟩ : syracuseStep 1362125 = 510797) B510797
theorem B2017507 : Blo 350755 2017507 := bstep (se 1 (by rfl) ⟨1513130, by rfl⟩ : syracuseStep 2017507 = 3026261) B3026261
theorem B1001965 : Blo 350755 1001965 := bstep (se 3 (by rfl) ⟨187868, by rfl⟩ : syracuseStep 1001965 = 375737) B375737
theorem B1002125 : Blo 350755 1002125 := bstep (se 3 (by rfl) ⟨187898, by rfl⟩ : syracuseStep 1002125 = 375797) B375797
theorem B2574989 : Blo 350755 2574989 := bstep (se 3 (by rfl) ⟨482810, by rfl⟩ : syracuseStep 2574989 = 965621) B965621
theorem B543395 : Blo 350755 543395 := bstep (se 1 (by rfl) ⟨407546, by rfl⟩ : syracuseStep 543395 = 815093) B815093
theorem B1133261 : Blo 350755 1133261 := bstep (se 3 (by rfl) ⟨212486, by rfl⟩ : syracuseStep 1133261 = 424973) B424973
theorem B2018033 : Blo 350755 2018033 := bstep (se 2 (by rfl) ⟨756762, by rfl⟩ : syracuseStep 2018033 = 1513525) B1513525
theorem B445171 : Blo 350755 445171 := bstep (se 1 (by rfl) ⟨333878, by rfl⟩ : syracuseStep 445171 = 667757) B667757
theorem B1002307 : Blo 350755 1002307 := bstep (se 1 (by rfl) ⟨751730, by rfl⟩ : syracuseStep 1002307 = 1503461) B1503461
theorem B445267 : Blo 350755 445267 := bstep (se 1 (by rfl) ⟨333950, by rfl⟩ : syracuseStep 445267 = 667901) B667901
theorem B445763 : Blo 350755 445763 := bstep (se 1 (by rfl) ⟨334322, by rfl⟩ : syracuseStep 445763 = 668645) B668645
theorem B478657 : Blo 350755 478657 := bstep (se 2 (by rfl) ⟨179496, by rfl⟩ : syracuseStep 478657 = 358993) B358993
theorem B1134157 : Blo 350755 1134157 := bstep (se 3 (by rfl) ⟨212654, by rfl⟩ : syracuseStep 1134157 = 425309) B425309
theorem B1068803 : Blo 350755 1068803 := bstep (se 1 (by rfl) ⟨801602, by rfl⟩ : syracuseStep 1068803 = 1603205) B1603205
theorem B1789937 : Blo 350755 1789937 := bstep (se 2 (by rfl) ⟨671226, by rfl⟩ : syracuseStep 1789937 = 1342453) B1342453
theorem B446467 : Blo 350755 446467 := bstep (se 1 (by rfl) ⟨334850, by rfl⟩ : syracuseStep 446467 = 669701) B669701
theorem B446563 : Blo 350755 446563 := bstep (se 1 (by rfl) ⟨334922, by rfl⟩ : syracuseStep 446563 = 669845) B669845
theorem B2019491 : Blo 350755 2019491 := bstep (se 1 (by rfl) ⟨1514618, by rfl⟩ : syracuseStep 2019491 = 3029237) B3029237
theorem B1003697 : Blo 350755 1003697 := bstep (se 2 (by rfl) ⟨376386, by rfl⟩ : syracuseStep 1003697 = 752773) B752773
theorem B7590257 : Blo 350755 7590257 := bstep (se 2 (by rfl) ⟨2846346, by rfl⟩ : syracuseStep 7590257 = 5692693) B5692693
theorem B1429937 : Blo 350755 1429937 := bstep (se 2 (by rfl) ⟨536226, by rfl⟩ : syracuseStep 1429937 = 1072453) B1072453
theorem B1135043 : Blo 350755 1135043 := bstep (se 1 (by rfl) ⟨851282, by rfl⟩ : syracuseStep 1135043 = 1702565) B1702565
theorem B1430065 : Blo 350755 1430065 := bstep (se 2 (by rfl) ⟨536274, by rfl⟩ : syracuseStep 1430065 = 1072549) B1072549
theorem B1200707 : Blo 350755 1200707 := bstep (se 1 (by rfl) ⟨900530, by rfl⟩ : syracuseStep 1200707 = 1801061) B1801061
theorem B447059 : Blo 350755 447059 := bstep (se 1 (by rfl) ⟨335294, by rfl⟩ : syracuseStep 447059 = 670589) B670589
theorem B3002993 : Blo 350755 3002993 := bstep (se 2 (by rfl) ⟨1126122, by rfl⟩ : syracuseStep 3002993 = 2252245) B2252245
theorem B1069777 : Blo 350755 1069777 := bstep (se 2 (by rfl) ⟨401166, by rfl⟩ : syracuseStep 1069777 = 802333) B802333
theorem B1004653 : Blo 350755 1004653 := bstep (se 3 (by rfl) ⟨188372, by rfl⟩ : syracuseStep 1004653 = 376745) B376745
theorem B447763 : Blo 350755 447763 := bstep (se 1 (by rfl) ⟨335822, by rfl⟩ : syracuseStep 447763 = 671645) B671645
theorem B611651 : Blo 350755 611651 := bstep (se 1 (by rfl) ⟨458738, by rfl⟩ : syracuseStep 611651 = 917477) B917477
theorem B1004881 : Blo 350755 1004881 := bstep (se 2 (by rfl) ⟨376830, by rfl⟩ : syracuseStep 1004881 = 753661) B753661
theorem B447859 : Blo 350755 447859 := bstep (se 1 (by rfl) ⟨335894, by rfl⟩ : syracuseStep 447859 = 671789) B671789
theorem B1791395 : Blo 350755 1791395 := bstep (se 1 (by rfl) ⟨1343546, by rfl⟩ : syracuseStep 1791395 = 2687093) B2687093
theorem B1005041 : Blo 350755 1005041 := bstep (se 2 (by rfl) ⟨376890, by rfl⟩ : syracuseStep 1005041 = 753781) B753781
theorem B1005155 : Blo 350755 1005155 := bstep (se 1 (by rfl) ⟨753866, by rfl⟩ : syracuseStep 1005155 = 1507733) B1507733
theorem B1267363 : Blo 350755 1267363 := bstep (se 1 (by rfl) ⟨950522, by rfl⟩ : syracuseStep 1267363 = 1901045) B1901045
theorem B907057 : Blo 350755 907057 := bstep (se 2 (by rfl) ⟨340146, by rfl⟩ : syracuseStep 907057 = 680293) B680293
theorem B448355 : Blo 350755 448355 := bstep (se 1 (by rfl) ⟨336266, by rfl⟩ : syracuseStep 448355 = 672533) B672533
theorem B2250629 : Blo 350755 2250629 := bstep (se 4 (by rfl) ⟨210996, by rfl⟩ : syracuseStep 2250629 = 421993) B421993
theorem B1333219 : Blo 350755 1333219 := bstep (se 1 (by rfl) ⟨999914, by rfl⟩ : syracuseStep 1333219 = 1999829) B1999829
theorem B1267825 : Blo 350755 1267825 := bstep (se 2 (by rfl) ⟨475434, by rfl⟩ : syracuseStep 1267825 = 950869) B950869
theorem B1792205 : Blo 350755 1792205 := bstep (se 3 (by rfl) ⟨336038, by rfl⟩ : syracuseStep 1792205 = 672077) B672077
theorem B1136941 : Blo 350755 1136941 := bstep (se 3 (by rfl) ⟨213176, by rfl⟩ : syracuseStep 1136941 = 426353) B426353
theorem B350755 : Blo 350755 350755 := bstep (se 1 (by rfl) ⟨263066, by rfl⟩ : syracuseStep 350755 = 526133) B526133
theorem B1268273 : Blo 350755 1268273 := bstep (se 2 (by rfl) ⟨475602, by rfl⟩ : syracuseStep 1268273 = 951205) B951205
theorem B350771 : Blo 350755 350771 := bstep (se 1 (by rfl) ⟨263078, by rfl⟩ : syracuseStep 350771 = 526157) B526157
theorem B350787 : Blo 350755 350787 := bstep (se 1 (by rfl) ⟨263090, by rfl⟩ : syracuseStep 350787 = 526181) B526181
theorem B2447941 : Blo 350755 2447941 := bstep (se 4 (by rfl) ⟨229494, by rfl⟩ : syracuseStep 2447941 = 458989) B458989
theorem B1006157 : Blo 350755 1006157 := bstep (se 3 (by rfl) ⟨188654, by rfl⟩ : syracuseStep 1006157 = 377309) B377309
theorem B350803 : Blo 350755 350803 := bstep (se 1 (by rfl) ⟨263102, by rfl⟩ : syracuseStep 350803 = 526205) B526205
theorem B350819 : Blo 350755 350819 := bstep (se 1 (by rfl) ⟨263114, by rfl⟩ : syracuseStep 350819 = 526229) B526229
theorem B350835 : Blo 350755 350835 := bstep (se 1 (by rfl) ⟨263126, by rfl⟩ : syracuseStep 350835 = 526253) B526253
theorem B350851 : Blo 350755 350851 := bstep (se 1 (by rfl) ⟨263138, by rfl⟩ : syracuseStep 350851 = 526277) B526277
theorem B350867 : Blo 350755 350867 := bstep (se 1 (by rfl) ⟨263150, by rfl⟩ : syracuseStep 350867 = 526301) B526301
theorem B383635 : Blo 350755 383635 := bstep (se 1 (by rfl) ⟨287726, by rfl⟩ : syracuseStep 383635 = 575453) B575453
theorem B350883 : Blo 350755 350883 := bstep (se 1 (by rfl) ⟨263162, by rfl⟩ : syracuseStep 350883 = 526325) B526325
theorem B1268401 : Blo 350755 1268401 := bstep (se 2 (by rfl) ⟨475650, by rfl⟩ : syracuseStep 1268401 = 951301) B951301
theorem B350899 : Blo 350755 350899 := bstep (se 1 (by rfl) ⟨263174, by rfl⟩ : syracuseStep 350899 = 526349) B526349
theorem B350915 : Blo 350755 350915 := bstep (se 1 (by rfl) ⟨263186, by rfl⟩ : syracuseStep 350915 = 526373) B526373
theorem B350931 : Blo 350755 350931 := bstep (se 1 (by rfl) ⟨263198, by rfl⟩ : syracuseStep 350931 = 526397) B526397
theorem B350947 : Blo 350755 350947 := bstep (se 1 (by rfl) ⟨263210, by rfl⟩ : syracuseStep 350947 = 526421) B526421
theorem B350963 : Blo 350755 350963 := bstep (se 1 (by rfl) ⟨263222, by rfl⟩ : syracuseStep 350963 = 526445) B526445
theorem B350979 : Blo 350755 350979 := bstep (se 1 (by rfl) ⟨263234, by rfl⟩ : syracuseStep 350979 = 526469) B526469
theorem B1006339 : Blo 350755 1006339 := bstep (se 1 (by rfl) ⟨754754, by rfl⟩ : syracuseStep 1006339 = 1509509) B1509509
theorem B350995 : Blo 350755 350995 := bstep (se 1 (by rfl) ⟨263246, by rfl⟩ : syracuseStep 350995 = 526493) B526493
theorem B351011 : Blo 350755 351011 := bstep (se 1 (by rfl) ⟨263258, by rfl⟩ : syracuseStep 351011 = 526517) B526517
theorem B351027 : Blo 350755 351027 := bstep (se 1 (by rfl) ⟨263270, by rfl⟩ : syracuseStep 351027 = 526541) B526541
theorem B351043 : Blo 350755 351043 := bstep (se 1 (by rfl) ⟨263282, by rfl⟩ : syracuseStep 351043 = 526565) B526565
theorem B351059 : Blo 350755 351059 := bstep (se 1 (by rfl) ⟨263294, by rfl⟩ : syracuseStep 351059 = 526589) B526589
theorem B351075 : Blo 350755 351075 := bstep (se 1 (by rfl) ⟨263306, by rfl⟩ : syracuseStep 351075 = 526613) B526613
theorem B351091 : Blo 350755 351091 := bstep (se 1 (by rfl) ⟨263318, by rfl⟩ : syracuseStep 351091 = 526637) B526637
theorem B351107 : Blo 350755 351107 := bstep (se 1 (by rfl) ⟨263330, by rfl⟩ : syracuseStep 351107 = 526661) B526661
theorem B1268621 : Blo 350755 1268621 := bstep (se 3 (by rfl) ⟨237866, by rfl⟩ : syracuseStep 1268621 = 475733) B475733
theorem B351123 : Blo 350755 351123 := bstep (se 1 (by rfl) ⟨263342, by rfl⟩ : syracuseStep 351123 = 526685) B526685
theorem B351139 : Blo 350755 351139 := bstep (se 1 (by rfl) ⟨263354, by rfl⟩ : syracuseStep 351139 = 526709) B526709
theorem B1006499 : Blo 350755 1006499 := bstep (se 1 (by rfl) ⟨754874, by rfl⟩ : syracuseStep 1006499 = 1509749) B1509749
theorem B351155 : Blo 350755 351155 := bstep (se 1 (by rfl) ⟨263366, by rfl⟩ : syracuseStep 351155 = 526733) B526733
theorem B351171 : Blo 350755 351171 := bstep (se 1 (by rfl) ⟨263378, by rfl⟩ : syracuseStep 351171 = 526757) B526757
theorem B351187 : Blo 350755 351187 := bstep (se 1 (by rfl) ⟨263390, by rfl⟩ : syracuseStep 351187 = 526781) B526781
theorem B351203 : Blo 350755 351203 := bstep (se 1 (by rfl) ⟨263402, by rfl⟩ : syracuseStep 351203 = 526805) B526805
theorem B351219 : Blo 350755 351219 := bstep (se 1 (by rfl) ⟨263414, by rfl⟩ : syracuseStep 351219 = 526829) B526829
theorem B351235 : Blo 350755 351235 := bstep (se 1 (by rfl) ⟨263426, by rfl⟩ : syracuseStep 351235 = 526853) B526853
theorem B351251 : Blo 350755 351251 := bstep (se 1 (by rfl) ⟨263438, by rfl⟩ : syracuseStep 351251 = 526877) B526877
theorem B351267 : Blo 350755 351267 := bstep (se 1 (by rfl) ⟨263450, by rfl⟩ : syracuseStep 351267 = 526901) B526901
theorem B351283 : Blo 350755 351283 := bstep (se 1 (by rfl) ⟨263462, by rfl⟩ : syracuseStep 351283 = 526925) B526925
theorem B351299 : Blo 350755 351299 := bstep (se 1 (by rfl) ⟨263474, by rfl⟩ : syracuseStep 351299 = 526949) B526949
theorem B351315 : Blo 350755 351315 := bstep (se 1 (by rfl) ⟨263486, by rfl⟩ : syracuseStep 351315 = 526973) B526973
theorem B351331 : Blo 350755 351331 := bstep (se 1 (by rfl) ⟨263498, by rfl⟩ : syracuseStep 351331 = 526997) B526997
theorem B2677859 : Blo 350755 2677859 := bstep (se 1 (by rfl) ⟨2008394, by rfl⟩ : syracuseStep 2677859 = 4016789) B4016789
theorem B351347 : Blo 350755 351347 := bstep (se 1 (by rfl) ⟨263510, by rfl⟩ : syracuseStep 351347 = 527021) B527021
theorem B351363 : Blo 350755 351363 := bstep (se 1 (by rfl) ⟨263522, by rfl⟩ : syracuseStep 351363 = 527045) B527045
theorem B351379 : Blo 350755 351379 := bstep (se 1 (by rfl) ⟨263534, by rfl⟩ : syracuseStep 351379 = 527069) B527069
theorem B351395 : Blo 350755 351395 := bstep (se 1 (by rfl) ⟨263546, by rfl⟩ : syracuseStep 351395 = 527093) B527093
theorem B351411 : Blo 350755 351411 := bstep (se 1 (by rfl) ⟨263558, by rfl⟩ : syracuseStep 351411 = 527117) B527117
theorem B351427 : Blo 350755 351427 := bstep (se 1 (by rfl) ⟨263570, by rfl⟩ : syracuseStep 351427 = 527141) B527141
theorem B351443 : Blo 350755 351443 := bstep (se 1 (by rfl) ⟨263582, by rfl⟩ : syracuseStep 351443 = 527165) B527165
theorem B351459 : Blo 350755 351459 := bstep (se 1 (by rfl) ⟨263594, by rfl⟩ : syracuseStep 351459 = 527189) B527189
theorem B351475 : Blo 350755 351475 := bstep (se 1 (by rfl) ⟨263606, by rfl⟩ : syracuseStep 351475 = 527213) B527213
theorem B351491 : Blo 350755 351491 := bstep (se 1 (by rfl) ⟨263618, by rfl⟩ : syracuseStep 351491 = 527237) B527237
theorem B351507 : Blo 350755 351507 := bstep (se 1 (by rfl) ⟨263630, by rfl⟩ : syracuseStep 351507 = 527261) B527261
theorem B351523 : Blo 350755 351523 := bstep (se 1 (by rfl) ⟨263642, by rfl⟩ : syracuseStep 351523 = 527285) B527285
theorem B711985 : Blo 350755 711985 := bstep (se 2 (by rfl) ⟨266994, by rfl⟩ : syracuseStep 711985 = 533989) B533989
theorem B351539 : Blo 350755 351539 := bstep (se 1 (by rfl) ⟨263654, by rfl⟩ : syracuseStep 351539 = 527309) B527309
theorem B351555 : Blo 350755 351555 := bstep (se 1 (by rfl) ⟨263666, by rfl⟩ : syracuseStep 351555 = 527333) B527333
theorem B351571 : Blo 350755 351571 := bstep (se 1 (by rfl) ⟨263678, by rfl⟩ : syracuseStep 351571 = 527357) B527357
theorem B351587 : Blo 350755 351587 := bstep (se 1 (by rfl) ⟨263690, by rfl⟩ : syracuseStep 351587 = 527381) B527381
theorem B351603 : Blo 350755 351603 := bstep (se 1 (by rfl) ⟨263702, by rfl⟩ : syracuseStep 351603 = 527405) B527405
theorem B351619 : Blo 350755 351619 := bstep (se 1 (by rfl) ⟨263714, by rfl⟩ : syracuseStep 351619 = 527429) B527429
theorem B351635 : Blo 350755 351635 := bstep (se 1 (by rfl) ⟨263726, by rfl⟩ : syracuseStep 351635 = 527453) B527453
theorem B351651 : Blo 350755 351651 := bstep (se 1 (by rfl) ⟨263738, by rfl⟩ : syracuseStep 351651 = 527477) B527477
theorem B351667 : Blo 350755 351667 := bstep (se 1 (by rfl) ⟨263750, by rfl⟩ : syracuseStep 351667 = 527501) B527501
theorem B351683 : Blo 350755 351683 := bstep (se 1 (by rfl) ⟨263762, by rfl⟩ : syracuseStep 351683 = 527525) B527525
theorem B351699 : Blo 350755 351699 := bstep (se 1 (by rfl) ⟨263774, by rfl⟩ : syracuseStep 351699 = 527549) B527549
theorem B351715 : Blo 350755 351715 := bstep (se 1 (by rfl) ⟨263786, by rfl⟩ : syracuseStep 351715 = 527573) B527573
theorem B351731 : Blo 350755 351731 := bstep (se 1 (by rfl) ⟨263798, by rfl⟩ : syracuseStep 351731 = 527597) B527597
theorem B351747 : Blo 350755 351747 := bstep (se 1 (by rfl) ⟨263810, by rfl⟩ : syracuseStep 351747 = 527621) B527621
theorem B351763 : Blo 350755 351763 := bstep (se 1 (by rfl) ⟨263822, by rfl⟩ : syracuseStep 351763 = 527645) B527645
theorem B351779 : Blo 350755 351779 := bstep (se 1 (by rfl) ⟨263834, by rfl⟩ : syracuseStep 351779 = 527669) B527669
theorem B351795 : Blo 350755 351795 := bstep (se 1 (by rfl) ⟨263846, by rfl⟩ : syracuseStep 351795 = 527693) B527693
theorem B351811 : Blo 350755 351811 := bstep (se 1 (by rfl) ⟨263858, by rfl⟩ : syracuseStep 351811 = 527717) B527717
theorem B351827 : Blo 350755 351827 := bstep (se 1 (by rfl) ⟨263870, by rfl⟩ : syracuseStep 351827 = 527741) B527741
theorem B351843 : Blo 350755 351843 := bstep (se 1 (by rfl) ⟨263882, by rfl⟩ : syracuseStep 351843 = 527765) B527765
theorem B351859 : Blo 350755 351859 := bstep (se 1 (by rfl) ⟨263894, by rfl⟩ : syracuseStep 351859 = 527789) B527789
theorem B351875 : Blo 350755 351875 := bstep (se 1 (by rfl) ⟨263906, by rfl⟩ : syracuseStep 351875 = 527813) B527813
theorem B351891 : Blo 350755 351891 := bstep (se 1 (by rfl) ⟨263918, by rfl⟩ : syracuseStep 351891 = 527837) B527837
theorem B351907 : Blo 350755 351907 := bstep (se 1 (by rfl) ⟨263930, by rfl⟩ : syracuseStep 351907 = 527861) B527861
theorem B351923 : Blo 350755 351923 := bstep (se 1 (by rfl) ⟨263942, by rfl⟩ : syracuseStep 351923 = 527885) B527885
theorem B351939 : Blo 350755 351939 := bstep (se 1 (by rfl) ⟨263954, by rfl⟩ : syracuseStep 351939 = 527909) B527909
theorem B351955 : Blo 350755 351955 := bstep (se 1 (by rfl) ⟨263966, by rfl⟩ : syracuseStep 351955 = 527933) B527933
theorem B351971 : Blo 350755 351971 := bstep (se 1 (by rfl) ⟨263978, by rfl⟩ : syracuseStep 351971 = 527957) B527957
theorem B351987 : Blo 350755 351987 := bstep (se 1 (by rfl) ⟨263990, by rfl⟩ : syracuseStep 351987 = 527981) B527981
theorem B450307 : Blo 350755 450307 := bstep (se 1 (by rfl) ⟨337730, by rfl⟩ : syracuseStep 450307 = 675461) B675461
theorem B352003 : Blo 350755 352003 := bstep (se 1 (by rfl) ⟨264002, by rfl⟩ : syracuseStep 352003 = 528005) B528005
theorem B352019 : Blo 350755 352019 := bstep (se 1 (by rfl) ⟨264014, by rfl⟩ : syracuseStep 352019 = 528029) B528029
theorem B1498915 : Blo 350755 1498915 := bstep (se 1 (by rfl) ⟨1124186, by rfl⟩ : syracuseStep 1498915 = 2248373) B2248373
theorem B352035 : Blo 350755 352035 := bstep (se 1 (by rfl) ⟨264026, by rfl⟩ : syracuseStep 352035 = 528053) B528053
theorem B352051 : Blo 350755 352051 := bstep (se 1 (by rfl) ⟨264038, by rfl⟩ : syracuseStep 352051 = 528077) B528077
theorem B352067 : Blo 350755 352067 := bstep (se 1 (by rfl) ⟨264050, by rfl⟩ : syracuseStep 352067 = 528101) B528101
theorem B352083 : Blo 350755 352083 := bstep (se 1 (by rfl) ⟨264062, by rfl⟩ : syracuseStep 352083 = 528125) B528125
theorem B352099 : Blo 350755 352099 := bstep (se 1 (by rfl) ⟨264074, by rfl⟩ : syracuseStep 352099 = 528149) B528149
theorem B352115 : Blo 350755 352115 := bstep (se 1 (by rfl) ⟨264086, by rfl⟩ : syracuseStep 352115 = 528173) B528173
theorem B352131 : Blo 350755 352131 := bstep (se 1 (by rfl) ⟨264098, by rfl⟩ : syracuseStep 352131 = 528197) B528197
theorem B1073027 : Blo 350755 1073027 := bstep (se 1 (by rfl) ⟨804770, by rfl⟩ : syracuseStep 1073027 = 1609541) B1609541
theorem B352147 : Blo 350755 352147 := bstep (se 1 (by rfl) ⟨264110, by rfl⟩ : syracuseStep 352147 = 528221) B528221
theorem B352163 : Blo 350755 352163 := bstep (se 1 (by rfl) ⟨264122, by rfl⟩ : syracuseStep 352163 = 528245) B528245
theorem B352179 : Blo 350755 352179 := bstep (se 1 (by rfl) ⟨264134, by rfl⟩ : syracuseStep 352179 = 528269) B528269
theorem B352195 : Blo 350755 352195 := bstep (se 1 (by rfl) ⟨264146, by rfl⟩ : syracuseStep 352195 = 528293) B528293
theorem B1007569 : Blo 350755 1007569 := bstep (se 2 (by rfl) ⟨377838, by rfl⟩ : syracuseStep 1007569 = 755677) B755677
theorem B352211 : Blo 350755 352211 := bstep (se 1 (by rfl) ⟨264158, by rfl⟩ : syracuseStep 352211 = 528317) B528317
theorem B352227 : Blo 350755 352227 := bstep (se 1 (by rfl) ⟨264170, by rfl⟩ : syracuseStep 352227 = 528341) B528341
theorem B352243 : Blo 350755 352243 := bstep (se 1 (by rfl) ⟨264182, by rfl⟩ : syracuseStep 352243 = 528365) B528365
theorem B352259 : Blo 350755 352259 := bstep (se 1 (by rfl) ⟨264194, by rfl⟩ : syracuseStep 352259 = 528389) B528389
theorem B352275 : Blo 350755 352275 := bstep (se 1 (by rfl) ⟨264206, by rfl⟩ : syracuseStep 352275 = 528413) B528413
theorem B352291 : Blo 350755 352291 := bstep (se 1 (by rfl) ⟨264218, by rfl⟩ : syracuseStep 352291 = 528437) B528437
theorem B352307 : Blo 350755 352307 := bstep (se 1 (by rfl) ⟨264230, by rfl⟩ : syracuseStep 352307 = 528461) B528461
theorem B352323 : Blo 350755 352323 := bstep (se 1 (by rfl) ⟨264242, by rfl⟩ : syracuseStep 352323 = 528485) B528485
theorem B352339 : Blo 350755 352339 := bstep (se 1 (by rfl) ⟨264254, by rfl⟩ : syracuseStep 352339 = 528509) B528509
theorem B352355 : Blo 350755 352355 := bstep (se 1 (by rfl) ⟨264266, by rfl⟩ : syracuseStep 352355 = 528533) B528533
theorem B352371 : Blo 350755 352371 := bstep (se 1 (by rfl) ⟨264278, by rfl⟩ : syracuseStep 352371 = 528557) B528557
theorem B352387 : Blo 350755 352387 := bstep (se 1 (by rfl) ⟨264290, by rfl⟩ : syracuseStep 352387 = 528581) B528581
theorem B1335437 : Blo 350755 1335437 := bstep (se 3 (by rfl) ⟨250394, by rfl⟩ : syracuseStep 1335437 = 500789) B500789
theorem B352403 : Blo 350755 352403 := bstep (se 1 (by rfl) ⟨264302, by rfl⟩ : syracuseStep 352403 = 528605) B528605
theorem B352419 : Blo 350755 352419 := bstep (se 1 (by rfl) ⟨264314, by rfl⟩ : syracuseStep 352419 = 528629) B528629
theorem B352435 : Blo 350755 352435 := bstep (se 1 (by rfl) ⟨264326, by rfl⟩ : syracuseStep 352435 = 528653) B528653
theorem B352451 : Blo 350755 352451 := bstep (se 1 (by rfl) ⟨264338, by rfl⟩ : syracuseStep 352451 = 528677) B528677
theorem B352467 : Blo 350755 352467 := bstep (se 1 (by rfl) ⟨264350, by rfl⟩ : syracuseStep 352467 = 528701) B528701
theorem B352483 : Blo 350755 352483 := bstep (se 1 (by rfl) ⟨264362, by rfl⟩ : syracuseStep 352483 = 528725) B528725
theorem B352499 : Blo 350755 352499 := bstep (se 1 (by rfl) ⟨264374, by rfl⟩ : syracuseStep 352499 = 528749) B528749
theorem B352515 : Blo 350755 352515 := bstep (se 1 (by rfl) ⟨264386, by rfl⟩ : syracuseStep 352515 = 528773) B528773
theorem B352531 : Blo 350755 352531 := bstep (se 1 (by rfl) ⟨264398, by rfl⟩ : syracuseStep 352531 = 528797) B528797
theorem B352547 : Blo 350755 352547 := bstep (se 1 (by rfl) ⟨264410, by rfl⟩ : syracuseStep 352547 = 528821) B528821
theorem B352563 : Blo 350755 352563 := bstep (se 1 (by rfl) ⟨264422, by rfl⟩ : syracuseStep 352563 = 528845) B528845
theorem B352579 : Blo 350755 352579 := bstep (se 1 (by rfl) ⟨264434, by rfl⟩ : syracuseStep 352579 = 528869) B528869
theorem B352595 : Blo 350755 352595 := bstep (se 1 (by rfl) ⟨264446, by rfl⟩ : syracuseStep 352595 = 528893) B528893
theorem B352611 : Blo 350755 352611 := bstep (se 1 (by rfl) ⟨264458, by rfl⟩ : syracuseStep 352611 = 528917) B528917
theorem B909667 : Blo 350755 909667 := bstep (se 1 (by rfl) ⟨682250, by rfl⟩ : syracuseStep 909667 = 1364501) B1364501
theorem B352627 : Blo 350755 352627 := bstep (se 1 (by rfl) ⟨264470, by rfl⟩ : syracuseStep 352627 = 528941) B528941
theorem B352643 : Blo 350755 352643 := bstep (se 1 (by rfl) ⟨264482, by rfl⟩ : syracuseStep 352643 = 528965) B528965
theorem B352659 : Blo 350755 352659 := bstep (se 1 (by rfl) ⟨264494, by rfl⟩ : syracuseStep 352659 = 528989) B528989
theorem B352675 : Blo 350755 352675 := bstep (se 1 (by rfl) ⟨264506, by rfl⟩ : syracuseStep 352675 = 529013) B529013
theorem B352691 : Blo 350755 352691 := bstep (se 1 (by rfl) ⟨264518, by rfl⟩ : syracuseStep 352691 = 529037) B529037
theorem B352707 : Blo 350755 352707 := bstep (se 1 (by rfl) ⟨264530, by rfl⟩ : syracuseStep 352707 = 529061) B529061
theorem B352723 : Blo 350755 352723 := bstep (se 1 (by rfl) ⟨264542, by rfl⟩ : syracuseStep 352723 = 529085) B529085
theorem B352739 : Blo 350755 352739 := bstep (se 1 (by rfl) ⟨264554, by rfl⟩ : syracuseStep 352739 = 529109) B529109
theorem B352755 : Blo 350755 352755 := bstep (se 1 (by rfl) ⟨264566, by rfl⟩ : syracuseStep 352755 = 529133) B529133
theorem B352771 : Blo 350755 352771 := bstep (se 1 (by rfl) ⟨264578, by rfl⟩ : syracuseStep 352771 = 529157) B529157
theorem B3006989 : Blo 350755 3006989 := bstep (se 3 (by rfl) ⟨563810, by rfl⟩ : syracuseStep 3006989 = 1127621) B1127621
theorem B352787 : Blo 350755 352787 := bstep (se 1 (by rfl) ⟨264590, by rfl⟩ : syracuseStep 352787 = 529181) B529181
theorem B352803 : Blo 350755 352803 := bstep (se 1 (by rfl) ⟨264602, by rfl⟩ : syracuseStep 352803 = 529205) B529205
theorem B352819 : Blo 350755 352819 := bstep (se 1 (by rfl) ⟨264614, by rfl⟩ : syracuseStep 352819 = 529229) B529229
theorem B352835 : Blo 350755 352835 := bstep (se 1 (by rfl) ⟨264626, by rfl⟩ : syracuseStep 352835 = 529253) B529253
theorem B352851 : Blo 350755 352851 := bstep (se 1 (by rfl) ⟨264638, by rfl⟩ : syracuseStep 352851 = 529277) B529277
theorem B352867 : Blo 350755 352867 := bstep (se 1 (by rfl) ⟨264650, by rfl⟩ : syracuseStep 352867 = 529301) B529301
theorem B352883 : Blo 350755 352883 := bstep (se 1 (by rfl) ⟨264662, by rfl⟩ : syracuseStep 352883 = 529325) B529325
theorem B352899 : Blo 350755 352899 := bstep (se 1 (by rfl) ⟨264674, by rfl⟩ : syracuseStep 352899 = 529349) B529349
theorem B352915 : Blo 350755 352915 := bstep (se 1 (by rfl) ⟨264686, by rfl⟩ : syracuseStep 352915 = 529373) B529373
theorem B352931 : Blo 350755 352931 := bstep (se 1 (by rfl) ⟨264698, by rfl⟩ : syracuseStep 352931 = 529397) B529397
theorem B352947 : Blo 350755 352947 := bstep (se 1 (by rfl) ⟨264710, by rfl⟩ : syracuseStep 352947 = 529421) B529421
theorem B352963 : Blo 350755 352963 := bstep (se 1 (by rfl) ⟨264722, by rfl⟩ : syracuseStep 352963 = 529445) B529445
theorem B352979 : Blo 350755 352979 := bstep (se 1 (by rfl) ⟨264734, by rfl⟩ : syracuseStep 352979 = 529469) B529469
theorem B352995 : Blo 350755 352995 := bstep (se 1 (by rfl) ⟨264746, by rfl⟩ : syracuseStep 352995 = 529493) B529493
theorem B2712305 : Blo 350755 2712305 := bstep (se 2 (by rfl) ⟨1017114, by rfl⟩ : syracuseStep 2712305 = 2034229) B2034229
theorem B353011 : Blo 350755 353011 := bstep (se 1 (by rfl) ⟨264758, by rfl⟩ : syracuseStep 353011 = 529517) B529517
theorem B353027 : Blo 350755 353027 := bstep (se 1 (by rfl) ⟨264770, by rfl⟩ : syracuseStep 353027 = 529541) B529541
theorem B353043 : Blo 350755 353043 := bstep (se 1 (by rfl) ⟨264782, by rfl⟩ : syracuseStep 353043 = 529565) B529565
theorem B353059 : Blo 350755 353059 := bstep (se 1 (by rfl) ⟨264794, by rfl⟩ : syracuseStep 353059 = 529589) B529589
theorem B910129 : Blo 350755 910129 := bstep (se 2 (by rfl) ⟨341298, by rfl⟩ : syracuseStep 910129 = 682597) B682597
theorem B353075 : Blo 350755 353075 := bstep (se 1 (by rfl) ⟨264806, by rfl⟩ : syracuseStep 353075 = 529613) B529613
theorem B353091 : Blo 350755 353091 := bstep (se 1 (by rfl) ⟨264818, by rfl⟩ : syracuseStep 353091 = 529637) B529637
theorem B353107 : Blo 350755 353107 := bstep (se 1 (by rfl) ⟨264830, by rfl⟩ : syracuseStep 353107 = 529661) B529661
theorem B353123 : Blo 350755 353123 := bstep (se 1 (by rfl) ⟨264842, by rfl⟩ : syracuseStep 353123 = 529685) B529685
theorem B353139 : Blo 350755 353139 := bstep (se 1 (by rfl) ⟨264854, by rfl⟩ : syracuseStep 353139 = 529709) B529709
theorem B353155 : Blo 350755 353155 := bstep (se 1 (by rfl) ⟨264866, by rfl⟩ : syracuseStep 353155 = 529733) B529733
theorem B353171 : Blo 350755 353171 := bstep (se 1 (by rfl) ⟨264878, by rfl⟩ : syracuseStep 353171 = 529757) B529757
theorem B353187 : Blo 350755 353187 := bstep (se 1 (by rfl) ⟨264890, by rfl⟩ : syracuseStep 353187 = 529781) B529781
theorem B353203 : Blo 350755 353203 := bstep (se 1 (by rfl) ⟨264902, by rfl⟩ : syracuseStep 353203 = 529805) B529805
theorem B353219 : Blo 350755 353219 := bstep (se 1 (by rfl) ⟨264914, by rfl⟩ : syracuseStep 353219 = 529829) B529829
theorem B353235 : Blo 350755 353235 := bstep (se 1 (by rfl) ⟨264926, by rfl⟩ : syracuseStep 353235 = 529853) B529853
theorem B353251 : Blo 350755 353251 := bstep (se 1 (by rfl) ⟨264938, by rfl⟩ : syracuseStep 353251 = 529877) B529877
theorem B353267 : Blo 350755 353267 := bstep (se 1 (by rfl) ⟨264950, by rfl⟩ : syracuseStep 353267 = 529901) B529901
theorem B353283 : Blo 350755 353283 := bstep (se 1 (by rfl) ⟨264962, by rfl⟩ : syracuseStep 353283 = 529925) B529925
theorem B353299 : Blo 350755 353299 := bstep (se 1 (by rfl) ⟨264974, by rfl⟩ : syracuseStep 353299 = 529949) B529949
theorem B353315 : Blo 350755 353315 := bstep (se 1 (by rfl) ⟨264986, by rfl⟩ : syracuseStep 353315 = 529973) B529973
theorem B1795121 : Blo 350755 1795121 := bstep (se 2 (by rfl) ⟨673170, by rfl⟩ : syracuseStep 1795121 = 1346341) B1346341
theorem B353331 : Blo 350755 353331 := bstep (se 1 (by rfl) ⟨264998, by rfl⟩ : syracuseStep 353331 = 529997) B529997
theorem B353347 : Blo 350755 353347 := bstep (se 1 (by rfl) ⟨265010, by rfl⟩ : syracuseStep 353347 = 530021) B530021
theorem B353363 : Blo 350755 353363 := bstep (se 1 (by rfl) ⟨265022, by rfl⟩ : syracuseStep 353363 = 530045) B530045
theorem B353379 : Blo 350755 353379 := bstep (se 1 (by rfl) ⟨265034, by rfl⟩ : syracuseStep 353379 = 530069) B530069
theorem B353395 : Blo 350755 353395 := bstep (se 1 (by rfl) ⟨265046, by rfl⟩ : syracuseStep 353395 = 530093) B530093
theorem B353411 : Blo 350755 353411 := bstep (se 1 (by rfl) ⟨265058, by rfl⟩ : syracuseStep 353411 = 530117) B530117
theorem B353427 : Blo 350755 353427 := bstep (se 1 (by rfl) ⟨265070, by rfl⟩ : syracuseStep 353427 = 530141) B530141
theorem B353443 : Blo 350755 353443 := bstep (se 1 (by rfl) ⟨265082, by rfl⟩ : syracuseStep 353443 = 530165) B530165
theorem B353459 : Blo 350755 353459 := bstep (se 1 (by rfl) ⟨265094, by rfl⟩ : syracuseStep 353459 = 530189) B530189
theorem B353475 : Blo 350755 353475 := bstep (se 1 (by rfl) ⟨265106, by rfl⟩ : syracuseStep 353475 = 530213) B530213
theorem B1008845 : Blo 350755 1008845 := bstep (se 3 (by rfl) ⟨189158, by rfl⟩ : syracuseStep 1008845 = 378317) B378317
theorem B353491 : Blo 350755 353491 := bstep (se 1 (by rfl) ⟨265118, by rfl⟩ : syracuseStep 353491 = 530237) B530237
theorem B353507 : Blo 350755 353507 := bstep (se 1 (by rfl) ⟨265130, by rfl⟩ : syracuseStep 353507 = 530261) B530261
theorem B353523 : Blo 350755 353523 := bstep (se 1 (by rfl) ⟨265142, by rfl⟩ : syracuseStep 353523 = 530285) B530285
theorem B353539 : Blo 350755 353539 := bstep (se 1 (by rfl) ⟨265154, by rfl⟩ : syracuseStep 353539 = 530309) B530309
theorem B353555 : Blo 350755 353555 := bstep (se 1 (by rfl) ⟨265166, by rfl⟩ : syracuseStep 353555 = 530333) B530333
theorem B353571 : Blo 350755 353571 := bstep (se 1 (by rfl) ⟨265178, by rfl⟩ : syracuseStep 353571 = 530357) B530357
theorem B353587 : Blo 350755 353587 := bstep (se 1 (by rfl) ⟨265190, by rfl⟩ : syracuseStep 353587 = 530381) B530381
theorem B353603 : Blo 350755 353603 := bstep (se 1 (by rfl) ⟨265202, by rfl⟩ : syracuseStep 353603 = 530405) B530405
theorem B353619 : Blo 350755 353619 := bstep (se 1 (by rfl) ⟨265214, by rfl⟩ : syracuseStep 353619 = 530429) B530429
theorem B353635 : Blo 350755 353635 := bstep (se 1 (by rfl) ⟨265226, by rfl⟩ : syracuseStep 353635 = 530453) B530453
theorem B353651 : Blo 350755 353651 := bstep (se 1 (by rfl) ⟨265238, by rfl⟩ : syracuseStep 353651 = 530477) B530477
theorem B353667 : Blo 350755 353667 := bstep (se 1 (by rfl) ⟨265250, by rfl⟩ : syracuseStep 353667 = 530501) B530501
theorem B1009027 : Blo 350755 1009027 := bstep (se 1 (by rfl) ⟨756770, by rfl⟩ : syracuseStep 1009027 = 1513541) B1513541
theorem B353683 : Blo 350755 353683 := bstep (se 1 (by rfl) ⟨265262, by rfl⟩ : syracuseStep 353683 = 530525) B530525
theorem B353699 : Blo 350755 353699 := bstep (se 1 (by rfl) ⟨265274, by rfl⟩ : syracuseStep 353699 = 530549) B530549
theorem B1009073 : Blo 350755 1009073 := bstep (se 2 (by rfl) ⟨378402, by rfl⟩ : syracuseStep 1009073 = 756805) B756805
theorem B353715 : Blo 350755 353715 := bstep (se 1 (by rfl) ⟨265286, by rfl⟩ : syracuseStep 353715 = 530573) B530573
theorem B353731 : Blo 350755 353731 := bstep (se 1 (by rfl) ⟨265298, by rfl⟩ : syracuseStep 353731 = 530597) B530597
theorem B353747 : Blo 350755 353747 := bstep (se 1 (by rfl) ⟨265310, by rfl⟩ : syracuseStep 353747 = 530621) B530621
theorem B353763 : Blo 350755 353763 := bstep (se 1 (by rfl) ⟨265322, by rfl⟩ : syracuseStep 353763 = 530645) B530645
theorem B353779 : Blo 350755 353779 := bstep (se 1 (by rfl) ⟨265334, by rfl⟩ : syracuseStep 353779 = 530669) B530669
theorem B353795 : Blo 350755 353795 := bstep (se 1 (by rfl) ⟨265346, by rfl⟩ : syracuseStep 353795 = 530693) B530693
theorem B353811 : Blo 350755 353811 := bstep (se 1 (by rfl) ⟨265358, by rfl⟩ : syracuseStep 353811 = 530717) B530717
theorem B353827 : Blo 350755 353827 := bstep (se 1 (by rfl) ⟨265370, by rfl⟩ : syracuseStep 353827 = 530741) B530741
theorem B353843 : Blo 350755 353843 := bstep (se 1 (by rfl) ⟨265382, by rfl⟩ : syracuseStep 353843 = 530765) B530765
theorem B353859 : Blo 350755 353859 := bstep (se 1 (by rfl) ⟨265394, by rfl⟩ : syracuseStep 353859 = 530789) B530789
theorem B353875 : Blo 350755 353875 := bstep (se 1 (by rfl) ⟨265406, by rfl⟩ : syracuseStep 353875 = 530813) B530813
theorem B2418275 : Blo 350755 2418275 := bstep (se 1 (by rfl) ⟨1813706, by rfl⟩ : syracuseStep 2418275 = 3627413) B3627413
theorem B353891 : Blo 350755 353891 := bstep (se 1 (by rfl) ⟨265418, by rfl⟩ : syracuseStep 353891 = 530837) B530837
theorem B353907 : Blo 350755 353907 := bstep (se 1 (by rfl) ⟨265430, by rfl⟩ : syracuseStep 353907 = 530861) B530861
theorem B353923 : Blo 350755 353923 := bstep (se 1 (by rfl) ⟨265442, by rfl⟩ : syracuseStep 353923 = 530885) B530885
theorem B353939 : Blo 350755 353939 := bstep (se 1 (by rfl) ⟨265454, by rfl⟩ : syracuseStep 353939 = 530909) B530909
theorem B353955 : Blo 350755 353955 := bstep (se 1 (by rfl) ⟨265466, by rfl⟩ : syracuseStep 353955 = 530933) B530933
theorem B353971 : Blo 350755 353971 := bstep (se 1 (by rfl) ⟨265478, by rfl⟩ : syracuseStep 353971 = 530957) B530957
theorem B353987 : Blo 350755 353987 := bstep (se 1 (by rfl) ⟨265490, by rfl⟩ : syracuseStep 353987 = 530981) B530981
theorem B5531333 : Blo 350755 5531333 := bstep (se 4 (by rfl) ⟨518562, by rfl⟩ : syracuseStep 5531333 = 1037125) B1037125
theorem B714449 : Blo 350755 714449 := bstep (se 2 (by rfl) ⟨267918, by rfl⟩ : syracuseStep 714449 = 535837) B535837
theorem B354003 : Blo 350755 354003 := bstep (se 1 (by rfl) ⟨265502, by rfl⟩ : syracuseStep 354003 = 531005) B531005
theorem B1697507 : Blo 350755 1697507 := bstep (se 1 (by rfl) ⟨1273130, by rfl⟩ : syracuseStep 1697507 = 2546261) B2546261
theorem B354019 : Blo 350755 354019 := bstep (se 1 (by rfl) ⟨265514, by rfl⟩ : syracuseStep 354019 = 531029) B531029
theorem B4056817 : Blo 350755 4056817 := bstep (se 2 (by rfl) ⟨1521306, by rfl⟩ : syracuseStep 4056817 = 3042613) B3042613
theorem B354035 : Blo 350755 354035 := bstep (se 1 (by rfl) ⟨265526, by rfl⟩ : syracuseStep 354035 = 531053) B531053
theorem B354051 : Blo 350755 354051 := bstep (se 1 (by rfl) ⟨265538, by rfl⟩ : syracuseStep 354051 = 531077) B531077
theorem B354067 : Blo 350755 354067 := bstep (se 1 (by rfl) ⟨265550, by rfl⟩ : syracuseStep 354067 = 531101) B531101
theorem B354083 : Blo 350755 354083 := bstep (se 1 (by rfl) ⟨265562, by rfl⟩ : syracuseStep 354083 = 531125) B531125
theorem B354099 : Blo 350755 354099 := bstep (se 1 (by rfl) ⟨265574, by rfl⟩ : syracuseStep 354099 = 531149) B531149
theorem B354115 : Blo 350755 354115 := bstep (se 1 (by rfl) ⟨265586, by rfl⟩ : syracuseStep 354115 = 531173) B531173
theorem B354131 : Blo 350755 354131 := bstep (se 1 (by rfl) ⟨265598, by rfl⟩ : syracuseStep 354131 = 531197) B531197
theorem B354147 : Blo 350755 354147 := bstep (se 1 (by rfl) ⟨265610, by rfl⟩ : syracuseStep 354147 = 531221) B531221
theorem B354163 : Blo 350755 354163 := bstep (se 1 (by rfl) ⟨265622, by rfl⟩ : syracuseStep 354163 = 531245) B531245
theorem B354179 : Blo 350755 354179 := bstep (se 1 (by rfl) ⟨265634, by rfl⟩ : syracuseStep 354179 = 531269) B531269
theorem B354195 : Blo 350755 354195 := bstep (se 1 (by rfl) ⟨265646, by rfl⟩ : syracuseStep 354195 = 531293) B531293
theorem B354211 : Blo 350755 354211 := bstep (se 1 (by rfl) ⟨265658, by rfl⟩ : syracuseStep 354211 = 531317) B531317
theorem B354227 : Blo 350755 354227 := bstep (se 1 (by rfl) ⟨265670, by rfl⟩ : syracuseStep 354227 = 531341) B531341
theorem B1206211 : Blo 350755 1206211 := bstep (se 1 (by rfl) ⟨904658, by rfl⟩ : syracuseStep 1206211 = 1809317) B1809317
theorem B354243 : Blo 350755 354243 := bstep (se 1 (by rfl) ⟨265682, by rfl⟩ : syracuseStep 354243 = 531365) B531365
theorem B354259 : Blo 350755 354259 := bstep (se 1 (by rfl) ⟨265694, by rfl⟩ : syracuseStep 354259 = 531389) B531389
theorem B354275 : Blo 350755 354275 := bstep (se 1 (by rfl) ⟨265706, by rfl⟩ : syracuseStep 354275 = 531413) B531413
theorem B354291 : Blo 350755 354291 := bstep (se 1 (by rfl) ⟨265718, by rfl⟩ : syracuseStep 354291 = 531437) B531437
theorem B354307 : Blo 350755 354307 := bstep (se 1 (by rfl) ⟨265730, by rfl⟩ : syracuseStep 354307 = 531461) B531461
theorem B354323 : Blo 350755 354323 := bstep (se 1 (by rfl) ⟨265742, by rfl⟩ : syracuseStep 354323 = 531485) B531485
theorem B354339 : Blo 350755 354339 := bstep (se 1 (by rfl) ⟨265754, by rfl⟩ : syracuseStep 354339 = 531509) B531509
theorem B354355 : Blo 350755 354355 := bstep (se 1 (by rfl) ⟨265766, by rfl⟩ : syracuseStep 354355 = 531533) B531533
theorem B354371 : Blo 350755 354371 := bstep (se 1 (by rfl) ⟨265778, by rfl⟩ : syracuseStep 354371 = 531557) B531557
theorem B354387 : Blo 350755 354387 := bstep (se 1 (by rfl) ⟨265790, by rfl⟩ : syracuseStep 354387 = 531581) B531581
theorem B485473 : Blo 350755 485473 := bstep (se 2 (by rfl) ⟨182052, by rfl⟩ : syracuseStep 485473 = 364105) B364105
theorem B354403 : Blo 350755 354403 := bstep (se 1 (by rfl) ⟨265802, by rfl⟩ : syracuseStep 354403 = 531605) B531605
theorem B354419 : Blo 350755 354419 := bstep (se 1 (by rfl) ⟨265814, by rfl⟩ : syracuseStep 354419 = 531629) B531629
theorem B354435 : Blo 350755 354435 := bstep (se 1 (by rfl) ⟨265826, by rfl⟩ : syracuseStep 354435 = 531653) B531653
theorem B354451 : Blo 350755 354451 := bstep (se 1 (by rfl) ⟨265838, by rfl⟩ : syracuseStep 354451 = 531677) B531677
theorem B354467 : Blo 350755 354467 := bstep (se 1 (by rfl) ⟨265850, by rfl⟩ : syracuseStep 354467 = 531701) B531701
theorem B1501361 : Blo 350755 1501361 := bstep (se 2 (by rfl) ⟨563010, by rfl⟩ : syracuseStep 1501361 = 1126021) B1126021
theorem B354483 : Blo 350755 354483 := bstep (se 1 (by rfl) ⟨265862, by rfl⟩ : syracuseStep 354483 = 531725) B531725
theorem B354499 : Blo 350755 354499 := bstep (se 1 (by rfl) ⟨265874, by rfl⟩ : syracuseStep 354499 = 531749) B531749
theorem B354515 : Blo 350755 354515 := bstep (se 1 (by rfl) ⟨265886, by rfl⟩ : syracuseStep 354515 = 531773) B531773
theorem B354531 : Blo 350755 354531 := bstep (se 1 (by rfl) ⟨265898, by rfl⟩ : syracuseStep 354531 = 531797) B531797
theorem B2418929 : Blo 350755 2418929 := bstep (se 2 (by rfl) ⟨907098, by rfl⟩ : syracuseStep 2418929 = 1814197) B1814197
theorem B354547 : Blo 350755 354547 := bstep (se 1 (by rfl) ⟨265910, by rfl⟩ : syracuseStep 354547 = 531821) B531821
theorem B354563 : Blo 350755 354563 := bstep (se 1 (by rfl) ⟨265922, by rfl⟩ : syracuseStep 354563 = 531845) B531845
theorem B354579 : Blo 350755 354579 := bstep (se 1 (by rfl) ⟨265934, by rfl⟩ : syracuseStep 354579 = 531869) B531869
theorem B354595 : Blo 350755 354595 := bstep (se 1 (by rfl) ⟨265946, by rfl⟩ : syracuseStep 354595 = 531893) B531893
theorem B354611 : Blo 350755 354611 := bstep (se 1 (by rfl) ⟨265958, by rfl⟩ : syracuseStep 354611 = 531917) B531917
theorem B354627 : Blo 350755 354627 := bstep (se 1 (by rfl) ⟨265970, by rfl⟩ : syracuseStep 354627 = 531941) B531941
theorem B354643 : Blo 350755 354643 := bstep (se 1 (by rfl) ⟨265982, by rfl⟩ : syracuseStep 354643 = 531965) B531965
theorem B354659 : Blo 350755 354659 := bstep (se 1 (by rfl) ⟨265994, by rfl⟩ : syracuseStep 354659 = 531989) B531989
theorem B354675 : Blo 350755 354675 := bstep (se 1 (by rfl) ⟨266006, by rfl⟩ : syracuseStep 354675 = 532013) B532013
theorem B354691 : Blo 350755 354691 := bstep (se 1 (by rfl) ⟨266018, by rfl⟩ : syracuseStep 354691 = 532037) B532037
theorem B354707 : Blo 350755 354707 := bstep (se 1 (by rfl) ⟨266030, by rfl⟩ : syracuseStep 354707 = 532061) B532061
theorem B354723 : Blo 350755 354723 := bstep (se 1 (by rfl) ⟨266042, by rfl⟩ : syracuseStep 354723 = 532085) B532085
theorem B354739 : Blo 350755 354739 := bstep (se 1 (by rfl) ⟨266054, by rfl⟩ : syracuseStep 354739 = 532109) B532109
theorem B354755 : Blo 350755 354755 := bstep (se 1 (by rfl) ⟨266066, by rfl⟩ : syracuseStep 354755 = 532133) B532133
theorem B7301573 : Blo 350755 7301573 := bstep (se 4 (by rfl) ⟨684522, by rfl⟩ : syracuseStep 7301573 = 1369045) B1369045
theorem B1076141 : Blo 350755 1076141 := bstep (se 3 (by rfl) ⟨201776, by rfl⟩ : syracuseStep 1076141 = 403553) B403553
theorem B1338353 : Blo 350755 1338353 := bstep (se 2 (by rfl) ⟨501882, by rfl⟩ : syracuseStep 1338353 = 1003765) B1003765
theorem B2157553 : Blo 350755 2157553 := bstep (se 2 (by rfl) ⟨809082, by rfl⟩ : syracuseStep 2157553 = 1618165) B1618165
theorem B453683 : Blo 350755 453683 := bstep (se 1 (by rfl) ⟨340262, by rfl⟩ : syracuseStep 453683 = 680525) B680525
theorem B1436849 : Blo 350755 1436849 := bstep (se 2 (by rfl) ⟨538818, by rfl⟩ : syracuseStep 1436849 = 1077637) B1077637
theorem B4517045 : Blo 350755 4517045 := bstep (se 5 (by rfl) ⟨211736, by rfl⟩ : syracuseStep 4517045 = 423473) B423473
theorem B847235 : Blo 350755 847235 := bstep (se 1 (by rfl) ⟨635426, by rfl⟩ : syracuseStep 847235 = 1270853) B1270853
theorem B3665549 : Blo 350755 3665549 := bstep (se 3 (by rfl) ⟨687290, by rfl⟩ : syracuseStep 3665549 = 1374581) B1374581
theorem B847523 : Blo 350755 847523 := bstep (se 1 (by rfl) ⟨635642, by rfl⟩ : syracuseStep 847523 = 1271285) B1271285
theorem B1699505 : Blo 350755 1699505 := bstep (se 2 (by rfl) ⟨637314, by rfl⟩ : syracuseStep 1699505 = 1274629) B1274629
theorem B4419269 : Blo 350755 4419269 := bstep (se 4 (by rfl) ⟨414306, by rfl⟩ : syracuseStep 4419269 = 828613) B828613
theorem B356195 : Blo 350755 356195 := bstep (se 1 (by rfl) ⟨267146, by rfl⟩ : syracuseStep 356195 = 534293) B534293
theorem B8613773 : Blo 350755 8613773 := bstep (se 3 (by rfl) ⟨1615082, by rfl⟩ : syracuseStep 8613773 = 3230165) B3230165
theorem B1208369 : Blo 350755 1208369 := bstep (se 2 (by rfl) ⟨453138, by rfl⟩ : syracuseStep 1208369 = 906277) B906277
theorem B716867 : Blo 350755 716867 := bstep (se 1 (by rfl) ⟨537650, by rfl⟩ : syracuseStep 716867 = 1075301) B1075301
theorem B749731 : Blo 350755 749731 := bstep (se 1 (by rfl) ⟨562298, by rfl⟩ : syracuseStep 749731 = 1124597) B1124597
theorem B5402933 : Blo 350755 5402933 := bstep (se 5 (by rfl) ⟨253262, by rfl⟩ : syracuseStep 5402933 = 506525) B506525
theorem B2683205 : Blo 350755 2683205 := bstep (se 4 (by rfl) ⟨251550, by rfl⟩ : syracuseStep 2683205 = 503101) B503101
theorem B1339811 : Blo 350755 1339811 := bstep (se 1 (by rfl) ⟨1004858, by rfl⟩ : syracuseStep 1339811 = 2009717) B2009717
theorem B422339 : Blo 350755 422339 := bstep (se 1 (by rfl) ⟨316754, by rfl⟩ : syracuseStep 422339 = 633509) B633509
theorem B848369 : Blo 350755 848369 := bstep (se 2 (by rfl) ⟨318138, by rfl⟩ : syracuseStep 848369 = 636277) B636277
theorem B357091 : Blo 350755 357091 := bstep (se 1 (by rfl) ⟨267818, by rfl⟩ : syracuseStep 357091 = 535637) B535637
theorem B1700621 : Blo 350755 1700621 := bstep (se 3 (by rfl) ⟨318866, by rfl⟩ : syracuseStep 1700621 = 637733) B637733
theorem B849137 : Blo 350755 849137 := bstep (se 2 (by rfl) ⟨318426, by rfl⟩ : syracuseStep 849137 = 636853) B636853
theorem B750961 : Blo 350755 750961 := bstep (se 2 (by rfl) ⟨281610, by rfl⟩ : syracuseStep 750961 = 563221) B563221
theorem B1340813 : Blo 350755 1340813 := bstep (se 3 (by rfl) ⟨251402, by rfl⟩ : syracuseStep 1340813 = 502805) B502805
theorem B1505101 : Blo 350755 1505101 := bstep (se 3 (by rfl) ⟨282206, by rfl⟩ : syracuseStep 1505101 = 564413) B564413
theorem B948145 : Blo 350755 948145 := bstep (se 2 (by rfl) ⟨355554, by rfl⟩ : syracuseStep 948145 = 711109) B711109
theorem B686051 : Blo 350755 686051 := bstep (se 1 (by rfl) ⟨514538, by rfl⟩ : syracuseStep 686051 = 1029077) B1029077
theorem B1701965 : Blo 350755 1701965 := bstep (se 3 (by rfl) ⟨319118, by rfl⟩ : syracuseStep 1701965 = 638237) B638237
theorem B916145 : Blo 350755 916145 := bstep (se 2 (by rfl) ⟨343554, by rfl⟩ : syracuseStep 916145 = 687109) B687109
theorem B752465 : Blo 350755 752465 := bstep (se 2 (by rfl) ⟨282174, by rfl⟩ : syracuseStep 752465 = 564349) B564349
theorem B752483 : Blo 350755 752483 := bstep (se 1 (by rfl) ⟨564362, by rfl⟩ : syracuseStep 752483 = 1128725) B1128725
theorem B2194445 : Blo 350755 2194445 := bstep (se 3 (by rfl) ⟨411458, by rfl⟩ : syracuseStep 2194445 = 822917) B822917
theorem B425011 : Blo 350755 425011 := bstep (se 1 (by rfl) ⟨318758, by rfl⟩ : syracuseStep 425011 = 637517) B637517
theorem B949475 : Blo 350755 949475 := bstep (se 1 (by rfl) ⟨712106, by rfl⟩ : syracuseStep 949475 = 1424213) B1424213
theorem B3374405 : Blo 350755 3374405 := bstep (se 4 (by rfl) ⟨316350, by rfl⟩ : syracuseStep 3374405 = 632701) B632701
theorem B3440069 : Blo 350755 3440069 := bstep (se 4 (by rfl) ⟨322506, by rfl⟩ : syracuseStep 3440069 = 645013) B645013
theorem B1342925 : Blo 350755 1342925 := bstep (se 3 (by rfl) ⟨251798, by rfl⟩ : syracuseStep 1342925 = 503597) B503597
theorem B1998371 : Blo 350755 1998371 := bstep (se 1 (by rfl) ⟨1498778, by rfl⟩ : syracuseStep 1998371 = 2997557) B2997557
theorem B950221 : Blo 350755 950221 := bstep (se 3 (by rfl) ⟨178166, by rfl⟩ : syracuseStep 950221 = 356333) B356333
theorem B754123 : Blo 350755 754123 := bstep (se 1 (by rfl) ⟨565592, by rfl⟩ : syracuseStep 754123 = 1131185) B1131185
theorem B1212889 : Blo 350755 1212889 := bstep (se 2 (by rfl) ⟨454833, by rfl⟩ : syracuseStep 1212889 = 909667) B909667
theorem B1245719 : Blo 350755 1245719 := bstep (se 1 (by rfl) ⟨934289, by rfl⟩ : syracuseStep 1245719 = 1868579) B1868579
theorem B1999511 : Blo 350755 1999511 := bstep (se 1 (by rfl) ⟨1499633, by rfl⟩ : syracuseStep 1999511 = 2999267) B2999267
theorem B2688065 : Blo 350755 2688065 := bstep (se 2 (by rfl) ⟨1008024, by rfl⟩ : syracuseStep 2688065 = 2016049) B2016049
theorem B1213505 : Blo 350755 1213505 := bstep (se 2 (by rfl) ⟨455064, by rfl⟩ : syracuseStep 1213505 = 910129) B910129
theorem B1508483 : Blo 350755 1508483 := bstep (se 1 (by rfl) ⟨1131362, by rfl⟩ : syracuseStep 1508483 = 2262725) B2262725
theorem B2458925 : Blo 350755 2458925 := bstep (se 3 (by rfl) ⟨461048, by rfl⟩ : syracuseStep 2458925 = 922097) B922097
theorem B3016115 : Blo 350755 3016115 := bstep (se 1 (by rfl) ⟨2262086, by rfl⟩ : syracuseStep 3016115 = 4524173) B4524173
theorem B394699 : Blo 350755 394699 := bstep (se 1 (by rfl) ⟨296024, by rfl⟩ : syracuseStep 394699 = 592049) B592049
theorem B951755 : Blo 350755 951755 := bstep (se 1 (by rfl) ⟨713816, by rfl⟩ : syracuseStep 951755 = 1427633) B1427633
theorem B394807 : Blo 350755 394807 := bstep (se 1 (by rfl) ⟨296105, by rfl⟩ : syracuseStep 394807 = 592211) B592211
theorem B394987 : Blo 350755 394987 := bstep (se 1 (by rfl) ⟨296240, by rfl⟩ : syracuseStep 394987 = 592481) B592481
theorem B362263 : Blo 350755 362263 := bstep (se 1 (by rfl) ⟨271697, by rfl⟩ : syracuseStep 362263 = 543395) B543395
theorem B755507 : Blo 350755 755507 := bstep (se 1 (by rfl) ⟨566630, by rfl⟩ : syracuseStep 755507 = 1133261) B1133261
theorem B1345355 : Blo 350755 1345355 := bstep (se 1 (by rfl) ⟨1009016, by rfl⟩ : syracuseStep 1345355 = 2018033) B2018033
theorem B395095 : Blo 350755 395095 := bstep (se 1 (by rfl) ⟨296321, by rfl⟩ : syracuseStep 395095 = 592643) B592643
theorem B526169 : Blo 350755 526169 := bstep (se 2 (by rfl) ⟨197313, by rfl⟩ : syracuseStep 526169 = 394627) B394627
theorem B1345369 : Blo 350755 1345369 := bstep (se 2 (by rfl) ⟨504513, by rfl⟩ : syracuseStep 1345369 = 1009027) B1009027
theorem B526283 : Blo 350755 526283 := bstep (se 1 (by rfl) ⟨394712, by rfl⟩ : syracuseStep 526283 = 789425) B789425
theorem B526295 : Blo 350755 526295 := bstep (se 1 (by rfl) ⟨394721, by rfl⟩ : syracuseStep 526295 = 789443) B789443
theorem B395275 : Blo 350755 395275 := bstep (se 1 (by rfl) ⟨296456, by rfl⟩ : syracuseStep 395275 = 592913) B592913
theorem B526361 : Blo 350755 526361 := bstep (se 2 (by rfl) ⟨197385, by rfl⟩ : syracuseStep 526361 = 394771) B394771
theorem B591961 : Blo 350755 591961 := bstep (se 2 (by rfl) ⟨221985, by rfl⟩ : syracuseStep 591961 = 443971) B443971
theorem B395383 : Blo 350755 395383 := bstep (se 1 (by rfl) ⟨296537, by rfl⟩ : syracuseStep 395383 = 593075) B593075
theorem B526475 : Blo 350755 526475 := bstep (se 1 (by rfl) ⟨394856, by rfl⟩ : syracuseStep 526475 = 789713) B789713
theorem B526487 : Blo 350755 526487 := bstep (se 1 (by rfl) ⟨394865, by rfl⟩ : syracuseStep 526487 = 789731) B789731
theorem B526553 : Blo 350755 526553 := bstep (se 2 (by rfl) ⟨197457, by rfl⟩ : syracuseStep 526553 = 394915) B394915
theorem B395563 : Blo 350755 395563 := bstep (se 1 (by rfl) ⟨296672, by rfl⟩ : syracuseStep 395563 = 593345) B593345
theorem B5409089 : Blo 350755 5409089 := bstep (se 2 (by rfl) ⟨2028408, by rfl⟩ : syracuseStep 5409089 = 4056817) B4056817
theorem B526667 : Blo 350755 526667 := bstep (se 1 (by rfl) ⟨395000, by rfl⟩ : syracuseStep 526667 = 790001) B790001
theorem B526679 : Blo 350755 526679 := bstep (se 1 (by rfl) ⟨395009, by rfl⟩ : syracuseStep 526679 = 790019) B790019
theorem B395671 : Blo 350755 395671 := bstep (se 1 (by rfl) ⟨296753, by rfl⟩ : syracuseStep 395671 = 593507) B593507
theorem B526745 : Blo 350755 526745 := bstep (se 2 (by rfl) ⟨197529, by rfl⟩ : syracuseStep 526745 = 395059) B395059
theorem B526859 : Blo 350755 526859 := bstep (se 1 (by rfl) ⟨395144, by rfl⟩ : syracuseStep 526859 = 790289) B790289
theorem B526871 : Blo 350755 526871 := bstep (se 1 (by rfl) ⟨395153, by rfl⟩ : syracuseStep 526871 = 790307) B790307
theorem B395851 : Blo 350755 395851 := bstep (se 1 (by rfl) ⟨296888, by rfl⟩ : syracuseStep 395851 = 593777) B593777
theorem B526937 : Blo 350755 526937 := bstep (se 2 (by rfl) ⟨197601, by rfl⟩ : syracuseStep 526937 = 395203) B395203
theorem B1608281 : Blo 350755 1608281 := bstep (se 2 (by rfl) ⟨603105, by rfl⟩ : syracuseStep 1608281 = 1206211) B1206211
theorem B4983389 : Blo 350755 4983389 := bstep (se 3 (by rfl) ⟨934385, by rfl⟩ : syracuseStep 4983389 = 1868771) B1868771
theorem B756353 : Blo 350755 756353 := bstep (se 2 (by rfl) ⟨283632, by rfl⟩ : syracuseStep 756353 = 567265) B567265
theorem B7604867 : Blo 350755 7604867 := bstep (se 1 (by rfl) ⟨5703650, by rfl⟩ : syracuseStep 7604867 = 11407301) B11407301
theorem B592535 : Blo 350755 592535 := bstep (se 1 (by rfl) ⟨444401, by rfl⟩ : syracuseStep 592535 = 888803) B888803
theorem B395959 : Blo 350755 395959 := bstep (se 1 (by rfl) ⟨296969, by rfl⟩ : syracuseStep 395959 = 593939) B593939
theorem B527051 : Blo 350755 527051 := bstep (se 1 (by rfl) ⟨395288, by rfl⟩ : syracuseStep 527051 = 790577) B790577
theorem B920267 : Blo 350755 920267 := bstep (se 1 (by rfl) ⟨690200, by rfl⟩ : syracuseStep 920267 = 1380401) B1380401
theorem B527063 : Blo 350755 527063 := bstep (se 1 (by rfl) ⟨395297, by rfl⟩ : syracuseStep 527063 = 790595) B790595
theorem B789209 : Blo 350755 789209 := bstep (se 2 (by rfl) ⟨295953, by rfl⟩ : syracuseStep 789209 = 591907) B591907
theorem B1510109 : Blo 350755 1510109 := bstep (se 3 (by rfl) ⟨283145, by rfl⟩ : syracuseStep 1510109 = 566291) B566291
theorem B592663 : Blo 350755 592663 := bstep (se 1 (by rfl) ⟨444497, by rfl⟩ : syracuseStep 592663 = 888995) B888995
theorem B1346327 : Blo 350755 1346327 := bstep (se 1 (by rfl) ⟨1009745, by rfl⟩ : syracuseStep 1346327 = 2019491) B2019491
theorem B527129 : Blo 350755 527129 := bstep (se 2 (by rfl) ⟨197673, by rfl⟩ : syracuseStep 527129 = 395347) B395347
theorem B789299 : Blo 350755 789299 := bstep (se 1 (by rfl) ⟨591974, by rfl⟩ : syracuseStep 789299 = 1183949) B1183949
theorem B789335 : Blo 350755 789335 := bstep (se 1 (by rfl) ⟨592001, by rfl⟩ : syracuseStep 789335 = 1184003) B1184003
theorem B396139 : Blo 350755 396139 := bstep (se 1 (by rfl) ⟨297104, by rfl⟩ : syracuseStep 396139 = 594209) B594209
theorem B527243 : Blo 350755 527243 := bstep (se 1 (by rfl) ⟨395432, by rfl⟩ : syracuseStep 527243 = 790865) B790865
theorem B527255 : Blo 350755 527255 := bstep (se 1 (by rfl) ⟨395441, by rfl⟩ : syracuseStep 527255 = 790883) B790883
theorem B953291 : Blo 350755 953291 := bstep (se 1 (by rfl) ⟨714968, by rfl⟩ : syracuseStep 953291 = 1429937) B1429937
theorem B396247 : Blo 350755 396247 := bstep (se 1 (by rfl) ⟨297185, by rfl⟩ : syracuseStep 396247 = 594371) B594371
theorem B756695 : Blo 350755 756695 := bstep (se 1 (by rfl) ⟨567521, by rfl⟩ : syracuseStep 756695 = 1135043) B1135043
theorem B527321 : Blo 350755 527321 := bstep (se 2 (by rfl) ⟨197745, by rfl⟩ : syracuseStep 527321 = 395491) B395491
theorem B2690009 : Blo 350755 2690009 := bstep (se 2 (by rfl) ⟨1008753, by rfl⟩ : syracuseStep 2690009 = 2017507) B2017507
theorem B789515 : Blo 350755 789515 := bstep (se 1 (by rfl) ⟨592136, by rfl⟩ : syracuseStep 789515 = 1184273) B1184273
theorem B789569 : Blo 350755 789569 := bstep (se 2 (by rfl) ⟨296088, by rfl⟩ : syracuseStep 789569 = 592177) B592177
theorem B2001995 : Blo 350755 2001995 := bstep (se 1 (by rfl) ⟨1501496, by rfl⟩ : syracuseStep 2001995 = 3002993) B3002993
theorem B527435 : Blo 350755 527435 := bstep (se 1 (by rfl) ⟨395576, by rfl⟩ : syracuseStep 527435 = 791153) B791153
theorem B527447 : Blo 350755 527447 := bstep (se 1 (by rfl) ⟨395585, by rfl⟩ : syracuseStep 527447 = 791171) B791171
theorem B396427 : Blo 350755 396427 := bstep (se 1 (by rfl) ⟨297320, by rfl⟩ : syracuseStep 396427 = 594641) B594641
theorem B527513 : Blo 350755 527513 := bstep (se 2 (by rfl) ⟨197817, by rfl⟩ : syracuseStep 527513 = 395635) B395635
theorem B396535 : Blo 350755 396535 := bstep (se 1 (by rfl) ⟨297401, by rfl⟩ : syracuseStep 396535 = 594803) B594803
theorem B527627 : Blo 350755 527627 := bstep (se 1 (by rfl) ⟨395720, by rfl⟩ : syracuseStep 527627 = 791441) B791441
theorem B527639 : Blo 350755 527639 := bstep (se 1 (by rfl) ⟨395729, by rfl⟩ : syracuseStep 527639 = 791459) B791459
theorem B789785 : Blo 350755 789785 := bstep (se 2 (by rfl) ⟨296169, by rfl⟩ : syracuseStep 789785 = 592339) B592339
theorem B2264365 : Blo 350755 2264365 := bstep (se 3 (by rfl) ⟨424568, by rfl⟩ : syracuseStep 2264365 = 849137) B849137
theorem B527705 : Blo 350755 527705 := bstep (se 2 (by rfl) ⟨197889, by rfl⟩ : syracuseStep 527705 = 395779) B395779
theorem B789875 : Blo 350755 789875 := bstep (se 1 (by rfl) ⟨592406, by rfl⟩ : syracuseStep 789875 = 1184813) B1184813
theorem B593291 : Blo 350755 593291 := bstep (se 1 (by rfl) ⟨444968, by rfl⟩ : syracuseStep 593291 = 889937) B889937
theorem B789911 : Blo 350755 789911 := bstep (se 1 (by rfl) ⟨592433, by rfl⟩ : syracuseStep 789911 = 1184867) B1184867
theorem B1510807 : Blo 350755 1510807 := bstep (se 1 (by rfl) ⟨1133105, by rfl⟩ : syracuseStep 1510807 = 2266211) B2266211
theorem B396715 : Blo 350755 396715 := bstep (se 1 (by rfl) ⟨297536, by rfl⟩ : syracuseStep 396715 = 595073) B595073
theorem B527819 : Blo 350755 527819 := bstep (se 1 (by rfl) ⟨395864, by rfl⟩ : syracuseStep 527819 = 791729) B791729
theorem B527831 : Blo 350755 527831 := bstep (se 1 (by rfl) ⟨395873, by rfl⟩ : syracuseStep 527831 = 791747) B791747
theorem B593419 : Blo 350755 593419 := bstep (se 1 (by rfl) ⟨445064, by rfl⟩ : syracuseStep 593419 = 890129) B890129
theorem B396823 : Blo 350755 396823 := bstep (se 1 (by rfl) ⟨297617, by rfl⟩ : syracuseStep 396823 = 595235) B595235
theorem B527897 : Blo 350755 527897 := bstep (se 2 (by rfl) ⟨197961, by rfl⟩ : syracuseStep 527897 = 395923) B395923
theorem B790091 : Blo 350755 790091 := bstep (se 1 (by rfl) ⟨592568, by rfl⟩ : syracuseStep 790091 = 1185137) B1185137
theorem B790145 : Blo 350755 790145 := bstep (se 2 (by rfl) ⟨296304, by rfl⟩ : syracuseStep 790145 = 592609) B592609
theorem B528011 : Blo 350755 528011 := bstep (se 1 (by rfl) ⟨396008, by rfl⟩ : syracuseStep 528011 = 792017) B792017
theorem B528023 : Blo 350755 528023 := bstep (se 1 (by rfl) ⟨396017, by rfl⟩ : syracuseStep 528023 = 792035) B792035
theorem B593561 : Blo 350755 593561 := bstep (se 2 (by rfl) ⟨222585, by rfl⟩ : syracuseStep 593561 = 445171) B445171
theorem B397003 : Blo 350755 397003 := bstep (se 1 (by rfl) ⟨297752, by rfl⟩ : syracuseStep 397003 = 595505) B595505
theorem B528089 : Blo 350755 528089 := bstep (se 2 (by rfl) ⟨198033, by rfl⟩ : syracuseStep 528089 = 396067) B396067
theorem B593689 : Blo 350755 593689 := bstep (se 2 (by rfl) ⟨222633, by rfl⟩ : syracuseStep 593689 = 445267) B445267
theorem B397111 : Blo 350755 397111 := bstep (se 1 (by rfl) ⟨297833, by rfl⟩ : syracuseStep 397111 = 595667) B595667
theorem B888641 : Blo 350755 888641 := bstep (se 2 (by rfl) ⟨333240, by rfl⟩ : syracuseStep 888641 = 666481) B666481
theorem B528203 : Blo 350755 528203 := bstep (se 1 (by rfl) ⟨396152, by rfl⟩ : syracuseStep 528203 = 792305) B792305
theorem B528215 : Blo 350755 528215 := bstep (se 1 (by rfl) ⟨396161, by rfl⟩ : syracuseStep 528215 = 792323) B792323
theorem B790361 : Blo 350755 790361 := bstep (se 2 (by rfl) ⟨296385, by rfl⟩ : syracuseStep 790361 = 592771) B592771
theorem B1904485 : Blo 350755 1904485 := bstep (se 4 (by rfl) ⟨178545, by rfl⟩ : syracuseStep 1904485 = 357091) B357091
theorem B528281 : Blo 350755 528281 := bstep (se 2 (by rfl) ⟨198105, by rfl⟩ : syracuseStep 528281 = 396211) B396211
theorem B790451 : Blo 350755 790451 := bstep (se 1 (by rfl) ⟨592838, by rfl⟩ : syracuseStep 790451 = 1185677) B1185677
theorem B790487 : Blo 350755 790487 := bstep (se 1 (by rfl) ⟨592865, by rfl⟩ : syracuseStep 790487 = 1185731) B1185731
theorem B397291 : Blo 350755 397291 := bstep (se 1 (by rfl) ⟨297968, by rfl⟩ : syracuseStep 397291 = 595937) B595937
theorem B528395 : Blo 350755 528395 := bstep (se 1 (by rfl) ⟨396296, by rfl⟩ : syracuseStep 528395 = 792593) B792593
theorem B528407 : Blo 350755 528407 := bstep (se 1 (by rfl) ⟨396305, by rfl⟩ : syracuseStep 528407 = 792611) B792611
theorem B397399 : Blo 350755 397399 := bstep (se 1 (by rfl) ⟨298049, by rfl⟩ : syracuseStep 397399 = 596099) B596099
theorem B528473 : Blo 350755 528473 := bstep (se 2 (by rfl) ⟨198177, by rfl⟩ : syracuseStep 528473 = 396355) B396355
theorem B790667 : Blo 350755 790667 := bstep (se 1 (by rfl) ⟨593000, by rfl⟩ : syracuseStep 790667 = 1186001) B1186001
theorem B1183895 : Blo 350755 1183895 := bstep (se 1 (by rfl) ⟨887921, by rfl⟩ : syracuseStep 1183895 = 1775843) B1775843
theorem B790721 : Blo 350755 790721 := bstep (se 2 (by rfl) ⟨296520, by rfl⟩ : syracuseStep 790721 = 593041) B593041
theorem B528587 : Blo 350755 528587 := bstep (se 1 (by rfl) ⟨396440, by rfl⟩ : syracuseStep 528587 = 792881) B792881
theorem B528599 : Blo 350755 528599 := bstep (se 1 (by rfl) ⟨396449, by rfl⟩ : syracuseStep 528599 = 792899) B792899
theorem B397579 : Blo 350755 397579 := bstep (se 1 (by rfl) ⟨298184, by rfl⟩ : syracuseStep 397579 = 596369) B596369
theorem B528665 : Blo 350755 528665 := bstep (se 2 (by rfl) ⟨198249, by rfl⟩ : syracuseStep 528665 = 396499) B396499
theorem B594263 : Blo 350755 594263 := bstep (se 1 (by rfl) ⟨445697, by rfl⟩ : syracuseStep 594263 = 891395) B891395
theorem B889177 : Blo 350755 889177 := bstep (se 2 (by rfl) ⟨333441, by rfl⟩ : syracuseStep 889177 = 666883) B666883
theorem B397687 : Blo 350755 397687 := bstep (se 1 (by rfl) ⟨298265, by rfl⟩ : syracuseStep 397687 = 596531) B596531
theorem B528779 : Blo 350755 528779 := bstep (se 1 (by rfl) ⟨396584, by rfl⟩ : syracuseStep 528779 = 793169) B793169
theorem B528791 : Blo 350755 528791 := bstep (se 1 (by rfl) ⟨396593, by rfl⟩ : syracuseStep 528791 = 793187) B793187
theorem B790937 : Blo 350755 790937 := bstep (se 2 (by rfl) ⟨296601, by rfl⟩ : syracuseStep 790937 = 593203) B593203
theorem B594391 : Blo 350755 594391 := bstep (se 1 (by rfl) ⟨445793, by rfl⟩ : syracuseStep 594391 = 891587) B891587
theorem B528857 : Blo 350755 528857 := bstep (se 2 (by rfl) ⟨198321, by rfl⟩ : syracuseStep 528857 = 396643) B396643
theorem B791027 : Blo 350755 791027 := bstep (se 1 (by rfl) ⟨593270, by rfl⟩ : syracuseStep 791027 = 1186541) B1186541
theorem B14750221 : Blo 350755 14750221 := bstep (se 3 (by rfl) ⟨2765666, by rfl⟩ : syracuseStep 14750221 = 5531333) B5531333
theorem B791063 : Blo 350755 791063 := bstep (se 1 (by rfl) ⟨593297, by rfl⟩ : syracuseStep 791063 = 1186595) B1186595
theorem B397867 : Blo 350755 397867 := bstep (se 1 (by rfl) ⟨298400, by rfl⟩ : syracuseStep 397867 = 596801) B596801
theorem B528971 : Blo 350755 528971 := bstep (se 1 (by rfl) ⟨396728, by rfl⟩ : syracuseStep 528971 = 793457) B793457
theorem B528983 : Blo 350755 528983 := bstep (se 1 (by rfl) ⟨396737, by rfl⟩ : syracuseStep 528983 = 793475) B793475
theorem B1151581 : Blo 350755 1151581 := bstep (se 3 (by rfl) ⟨215921, by rfl⟩ : syracuseStep 1151581 = 431843) B431843
theorem B397975 : Blo 350755 397975 := bstep (se 1 (by rfl) ⟨298481, by rfl⟩ : syracuseStep 397975 = 596963) B596963
theorem B529049 : Blo 350755 529049 := bstep (se 2 (by rfl) ⟨198393, by rfl⟩ : syracuseStep 529049 = 396787) B396787
theorem B1184435 : Blo 350755 1184435 := bstep (se 1 (by rfl) ⟨888326, by rfl⟩ : syracuseStep 1184435 = 1776653) B1776653
theorem B791243 : Blo 350755 791243 := bstep (se 1 (by rfl) ⟨593432, by rfl⟩ : syracuseStep 791243 = 1186865) B1186865
theorem B791297 : Blo 350755 791297 := bstep (se 2 (by rfl) ⟨296736, by rfl⟩ : syracuseStep 791297 = 593473) B593473
theorem B529163 : Blo 350755 529163 := bstep (se 1 (by rfl) ⟨396872, by rfl⟩ : syracuseStep 529163 = 793745) B793745
theorem B1512209 : Blo 350755 1512209 := bstep (se 2 (by rfl) ⟨567078, by rfl⟩ : syracuseStep 1512209 = 1134157) B1134157
theorem B529175 : Blo 350755 529175 := bstep (se 1 (by rfl) ⟨396881, by rfl⟩ : syracuseStep 529175 = 793763) B793763
theorem B398155 : Blo 350755 398155 := bstep (se 1 (by rfl) ⟨298616, by rfl⟩ : syracuseStep 398155 = 597233) B597233
theorem B529241 : Blo 350755 529241 := bstep (se 2 (by rfl) ⟨198465, by rfl⟩ : syracuseStep 529241 = 396931) B396931
theorem B398263 : Blo 350755 398263 := bstep (se 1 (by rfl) ⟨298697, by rfl⟩ : syracuseStep 398263 = 597395) B597395
theorem B1184705 : Blo 350755 1184705 := bstep (se 2 (by rfl) ⟨444264, by rfl⟩ : syracuseStep 1184705 = 888529) B888529
theorem B529355 : Blo 350755 529355 := bstep (se 1 (by rfl) ⟨397016, by rfl⟩ : syracuseStep 529355 = 794033) B794033
theorem B529367 : Blo 350755 529367 := bstep (se 1 (by rfl) ⟨397025, by rfl⟩ : syracuseStep 529367 = 794051) B794051
theorem B791513 : Blo 350755 791513 := bstep (se 2 (by rfl) ⟨296817, by rfl⟩ : syracuseStep 791513 = 593635) B593635
theorem B529433 : Blo 350755 529433 := bstep (se 2 (by rfl) ⟨198537, by rfl⟩ : syracuseStep 529433 = 397075) B397075
theorem B791603 : Blo 350755 791603 := bstep (se 1 (by rfl) ⟨593702, by rfl⟩ : syracuseStep 791603 = 1187405) B1187405
theorem B595019 : Blo 350755 595019 := bstep (se 1 (by rfl) ⟨446264, by rfl⟩ : syracuseStep 595019 = 892529) B892529
theorem B791639 : Blo 350755 791639 := bstep (se 1 (by rfl) ⟨593729, by rfl⟩ : syracuseStep 791639 = 1187459) B1187459
theorem B398443 : Blo 350755 398443 := bstep (se 1 (by rfl) ⟨298832, by rfl⟩ : syracuseStep 398443 = 597665) B597665
theorem B529547 : Blo 350755 529547 := bstep (se 1 (by rfl) ⟨397160, by rfl⟩ : syracuseStep 529547 = 794321) B794321
theorem B529559 : Blo 350755 529559 := bstep (se 1 (by rfl) ⟨397169, by rfl⟩ : syracuseStep 529559 = 794339) B794339
theorem B595147 : Blo 350755 595147 := bstep (se 1 (by rfl) ⟨446360, by rfl⟩ : syracuseStep 595147 = 892721) B892721
theorem B398551 : Blo 350755 398551 := bstep (se 1 (by rfl) ⟨298913, by rfl⟩ : syracuseStep 398551 = 597827) B597827
theorem B529625 : Blo 350755 529625 := bstep (se 2 (by rfl) ⟨198609, by rfl⟩ : syracuseStep 529625 = 397219) B397219
theorem B791819 : Blo 350755 791819 := bstep (se 1 (by rfl) ⟨593864, by rfl⟩ : syracuseStep 791819 = 1187729) B1187729
theorem B791873 : Blo 350755 791873 := bstep (se 2 (by rfl) ⟨296952, by rfl⟩ : syracuseStep 791873 = 593905) B593905
theorem B529739 : Blo 350755 529739 := bstep (se 1 (by rfl) ⟨397304, by rfl⟩ : syracuseStep 529739 = 794609) B794609
theorem B529751 : Blo 350755 529751 := bstep (se 1 (by rfl) ⟨397313, by rfl⟩ : syracuseStep 529751 = 794627) B794627
theorem B595289 : Blo 350755 595289 := bstep (se 2 (by rfl) ⟨223233, by rfl⟩ : syracuseStep 595289 = 446467) B446467
theorem B398731 : Blo 350755 398731 := bstep (se 1 (by rfl) ⟨299048, by rfl⟩ : syracuseStep 398731 = 598097) B598097
theorem B529817 : Blo 350755 529817 := bstep (se 2 (by rfl) ⟨198681, by rfl⟩ : syracuseStep 529817 = 397363) B397363
theorem B890291 : Blo 350755 890291 := bstep (se 1 (by rfl) ⟨667718, by rfl⟩ : syracuseStep 890291 = 1335437) B1335437
theorem B595417 : Blo 350755 595417 := bstep (se 2 (by rfl) ⟨223281, by rfl⟩ : syracuseStep 595417 = 446563) B446563
theorem B1185245 : Blo 350755 1185245 := bstep (se 3 (by rfl) ⟨222233, by rfl⟩ : syracuseStep 1185245 = 444467) B444467
theorem B398839 : Blo 350755 398839 := bstep (se 1 (by rfl) ⟨299129, by rfl⟩ : syracuseStep 398839 = 598259) B598259
theorem B529931 : Blo 350755 529931 := bstep (se 1 (by rfl) ⟨397448, by rfl⟩ : syracuseStep 529931 = 794897) B794897
theorem B529943 : Blo 350755 529943 := bstep (se 1 (by rfl) ⟨397457, by rfl⟩ : syracuseStep 529943 = 794915) B794915
theorem B792089 : Blo 350755 792089 := bstep (se 2 (by rfl) ⟨297033, by rfl⟩ : syracuseStep 792089 = 594067) B594067
theorem B530009 : Blo 350755 530009 := bstep (se 2 (by rfl) ⟨198753, by rfl⟩ : syracuseStep 530009 = 397507) B397507
theorem B792179 : Blo 350755 792179 := bstep (se 1 (by rfl) ⟨594134, by rfl⟩ : syracuseStep 792179 = 1188269) B1188269
theorem B792215 : Blo 350755 792215 := bstep (se 1 (by rfl) ⟨594161, by rfl⟩ : syracuseStep 792215 = 1188323) B1188323
theorem B399019 : Blo 350755 399019 := bstep (se 1 (by rfl) ⟨299264, by rfl⟩ : syracuseStep 399019 = 598529) B598529
theorem B2004659 : Blo 350755 2004659 := bstep (se 1 (by rfl) ⟨1503494, by rfl⟩ : syracuseStep 2004659 = 3006989) B3006989
theorem B530123 : Blo 350755 530123 := bstep (se 1 (by rfl) ⟨397592, by rfl⟩ : syracuseStep 530123 = 795185) B795185
theorem B530135 : Blo 350755 530135 := bstep (se 1 (by rfl) ⟨397601, by rfl⟩ : syracuseStep 530135 = 795203) B795203
theorem B890585 : Blo 350755 890585 := bstep (se 2 (by rfl) ⟨333969, by rfl⟩ : syracuseStep 890585 = 667939) B667939
theorem B530201 : Blo 350755 530201 := bstep (se 2 (by rfl) ⟨198825, by rfl⟩ : syracuseStep 530201 = 397651) B397651
theorem B792395 : Blo 350755 792395 := bstep (se 1 (by rfl) ⟨594296, by rfl⟩ : syracuseStep 792395 = 1188593) B1188593
theorem B792449 : Blo 350755 792449 := bstep (se 2 (by rfl) ⟨297168, by rfl⟩ : syracuseStep 792449 = 594337) B594337
theorem B530315 : Blo 350755 530315 := bstep (se 1 (by rfl) ⟨397736, by rfl⟩ : syracuseStep 530315 = 795473) B795473
theorem B530327 : Blo 350755 530327 := bstep (se 1 (by rfl) ⟨397745, by rfl⟩ : syracuseStep 530327 = 795491) B795491
theorem B530393 : Blo 350755 530393 := bstep (se 2 (by rfl) ⟨198897, by rfl⟩ : syracuseStep 530393 = 397795) B397795
theorem B595991 : Blo 350755 595991 := bstep (se 1 (by rfl) ⟨446993, by rfl⟩ : syracuseStep 595991 = 893987) B893987
theorem B1906753 : Blo 350755 1906753 := bstep (se 2 (by rfl) ⟨715032, by rfl⟩ : syracuseStep 1906753 = 1430065) B1430065
theorem B5150789 : Blo 350755 5150789 := bstep (se 4 (by rfl) ⟨482886, by rfl⟩ : syracuseStep 5150789 = 965773) B965773
theorem B530507 : Blo 350755 530507 := bstep (se 1 (by rfl) ⟨397880, by rfl⟩ : syracuseStep 530507 = 795761) B795761
theorem B530519 : Blo 350755 530519 := bstep (se 1 (by rfl) ⟨397889, by rfl⟩ : syracuseStep 530519 = 795779) B795779
theorem B792665 : Blo 350755 792665 := bstep (se 2 (by rfl) ⟨297249, by rfl⟩ : syracuseStep 792665 = 594499) B594499
theorem B596119 : Blo 350755 596119 := bstep (se 1 (by rfl) ⟨447089, by rfl⟩ : syracuseStep 596119 = 894179) B894179
theorem B530585 : Blo 350755 530585 := bstep (se 2 (by rfl) ⟨198969, by rfl⟩ : syracuseStep 530585 = 397939) B397939
theorem B792755 : Blo 350755 792755 := bstep (se 1 (by rfl) ⟨594566, by rfl⟩ : syracuseStep 792755 = 1189133) B1189133
theorem B792791 : Blo 350755 792791 := bstep (se 1 (by rfl) ⟨594593, by rfl⟩ : syracuseStep 792791 = 1189187) B1189187
theorem B530699 : Blo 350755 530699 := bstep (se 1 (by rfl) ⟨398024, by rfl⟩ : syracuseStep 530699 = 796049) B796049
theorem B24254741 : Blo 350755 24254741 := bstep (se 6 (by rfl) ⟨568470, by rfl⟩ : syracuseStep 24254741 = 1136941) B1136941
theorem B530711 : Blo 350755 530711 := bstep (se 1 (by rfl) ⟨398033, by rfl⟩ : syracuseStep 530711 = 796067) B796067
theorem B2693411 : Blo 350755 2693411 := bstep (se 1 (by rfl) ⟨2020058, by rfl⟩ : syracuseStep 2693411 = 4040117) B4040117
theorem B530777 : Blo 350755 530777 := bstep (se 2 (by rfl) ⟨199041, by rfl⟩ : syracuseStep 530777 = 398083) B398083
theorem B792971 : Blo 350755 792971 := bstep (se 1 (by rfl) ⟨594728, by rfl⟩ : syracuseStep 792971 = 1189457) B1189457
theorem B1612183 : Blo 350755 1612183 := bstep (se 1 (by rfl) ⟨1209137, by rfl⟩ : syracuseStep 1612183 = 2418275) B2418275
theorem B793025 : Blo 350755 793025 := bstep (se 2 (by rfl) ⟨297384, by rfl⟩ : syracuseStep 793025 = 594769) B594769
theorem B530891 : Blo 350755 530891 := bstep (se 1 (by rfl) ⟨398168, by rfl⟩ : syracuseStep 530891 = 796337) B796337
theorem B530903 : Blo 350755 530903 := bstep (se 1 (by rfl) ⟨398177, by rfl⟩ : syracuseStep 530903 = 796355) B796355
theorem B530969 : Blo 350755 530969 := bstep (se 2 (by rfl) ⟨199113, by rfl⟩ : syracuseStep 530969 = 398227) B398227
theorem B1186379 : Blo 350755 1186379 := bstep (se 1 (by rfl) ⟨889784, by rfl⟩ : syracuseStep 1186379 = 1779569) B1779569
theorem B531083 : Blo 350755 531083 := bstep (se 1 (by rfl) ⟨398312, by rfl⟩ : syracuseStep 531083 = 796625) B796625
theorem B6036119 : Blo 350755 6036119 := bstep (se 1 (by rfl) ⟨4527089, by rfl⟩ : syracuseStep 6036119 = 9054179) B9054179
theorem B531095 : Blo 350755 531095 := bstep (se 1 (by rfl) ⟨398321, by rfl⟩ : syracuseStep 531095 = 796643) B796643
theorem B793241 : Blo 350755 793241 := bstep (se 2 (by rfl) ⟨297465, by rfl⟩ : syracuseStep 793241 = 594931) B594931
theorem B531161 : Blo 350755 531161 := bstep (se 2 (by rfl) ⟨199185, by rfl⟩ : syracuseStep 531161 = 398371) B398371
theorem B793331 : Blo 350755 793331 := bstep (se 1 (by rfl) ⟨594998, by rfl⟩ : syracuseStep 793331 = 1189997) B1189997
theorem B596747 : Blo 350755 596747 := bstep (se 1 (by rfl) ⟨447560, by rfl⟩ : syracuseStep 596747 = 895121) B895121
theorem B793367 : Blo 350755 793367 := bstep (se 1 (by rfl) ⟨595025, by rfl⟩ : syracuseStep 793367 = 1190051) B1190051
theorem B3873581 : Blo 350755 3873581 := bstep (se 3 (by rfl) ⟨726296, by rfl⟩ : syracuseStep 3873581 = 1452593) B1452593
theorem B1612619 : Blo 350755 1612619 := bstep (se 1 (by rfl) ⟨1209464, by rfl⟩ : syracuseStep 1612619 = 2418929) B2418929
theorem B531275 : Blo 350755 531275 := bstep (se 1 (by rfl) ⟨398456, by rfl⟩ : syracuseStep 531275 = 796913) B796913
theorem B531287 : Blo 350755 531287 := bstep (se 1 (by rfl) ⟨398465, by rfl⟩ : syracuseStep 531287 = 796931) B796931
theorem B1186649 : Blo 350755 1186649 := bstep (se 2 (by rfl) ⟨444993, by rfl⟩ : syracuseStep 1186649 = 889987) B889987
theorem B596875 : Blo 350755 596875 := bstep (se 1 (by rfl) ⟨447656, by rfl⟩ : syracuseStep 596875 = 895313) B895313
theorem B531353 : Blo 350755 531353 := bstep (se 2 (by rfl) ⟨199257, by rfl⟩ : syracuseStep 531353 = 398515) B398515
theorem B793547 : Blo 350755 793547 := bstep (se 1 (by rfl) ⟨595160, by rfl⟩ : syracuseStep 793547 = 1190321) B1190321
theorem B793601 : Blo 350755 793601 := bstep (se 2 (by rfl) ⟨297600, by rfl⟩ : syracuseStep 793601 = 595201) B595201
theorem B531467 : Blo 350755 531467 := bstep (se 1 (by rfl) ⟨398600, by rfl⟩ : syracuseStep 531467 = 797201) B797201
theorem B531479 : Blo 350755 531479 := bstep (se 1 (by rfl) ⟨398609, by rfl⟩ : syracuseStep 531479 = 797219) B797219
theorem B597017 : Blo 350755 597017 := bstep (se 2 (by rfl) ⟨223881, by rfl⟩ : syracuseStep 597017 = 447763) B447763
theorem B531545 : Blo 350755 531545 := bstep (se 2 (by rfl) ⟨199329, by rfl⟩ : syracuseStep 531545 = 398659) B398659
theorem B2006117 : Blo 350755 2006117 := bstep (se 4 (by rfl) ⟨188073, by rfl⟩ : syracuseStep 2006117 = 376147) B376147
theorem B597145 : Blo 350755 597145 := bstep (se 2 (by rfl) ⟨223929, by rfl⟩ : syracuseStep 597145 = 447859) B447859
theorem B531659 : Blo 350755 531659 := bstep (se 1 (by rfl) ⟨398744, by rfl⟩ : syracuseStep 531659 = 797489) B797489
theorem B531671 : Blo 350755 531671 := bstep (se 1 (by rfl) ⟨398753, by rfl⟩ : syracuseStep 531671 = 797507) B797507
theorem B793817 : Blo 350755 793817 := bstep (se 2 (by rfl) ⟨297681, by rfl⟩ : syracuseStep 793817 = 595363) B595363
theorem B4005125 : Blo 350755 4005125 := bstep (se 4 (by rfl) ⟨375480, by rfl⟩ : syracuseStep 4005125 = 750961) B750961
theorem B531737 : Blo 350755 531737 := bstep (se 2 (by rfl) ⟨199401, by rfl⟩ : syracuseStep 531737 = 398803) B398803
theorem B793907 : Blo 350755 793907 := bstep (se 1 (by rfl) ⟨595430, by rfl⟩ : syracuseStep 793907 = 1190861) B1190861
theorem B892235 : Blo 350755 892235 := bstep (se 1 (by rfl) ⟨669176, by rfl⟩ : syracuseStep 892235 = 1338353) B1338353
theorem B793943 : Blo 350755 793943 := bstep (se 1 (by rfl) ⟨595457, by rfl⟩ : syracuseStep 793943 = 1190915) B1190915
theorem B531851 : Blo 350755 531851 := bstep (se 1 (by rfl) ⟨398888, by rfl⟩ : syracuseStep 531851 = 797777) B797777
theorem B531863 : Blo 350755 531863 := bstep (se 1 (by rfl) ⟨398897, by rfl⟩ : syracuseStep 531863 = 797795) B797795
theorem B957899 : Blo 350755 957899 := bstep (se 1 (by rfl) ⟨718424, by rfl⟩ : syracuseStep 957899 = 1436849) B1436849
theorem B531929 : Blo 350755 531929 := bstep (se 2 (by rfl) ⟨199473, by rfl⟩ : syracuseStep 531929 = 398947) B398947
theorem B794123 : Blo 350755 794123 := bstep (se 1 (by rfl) ⟨595592, by rfl⟩ : syracuseStep 794123 = 1191185) B1191185
theorem B1187351 : Blo 350755 1187351 := bstep (se 1 (by rfl) ⟨890513, by rfl⟩ : syracuseStep 1187351 = 1781027) B1781027
theorem B794177 : Blo 350755 794177 := bstep (se 2 (by rfl) ⟨297816, by rfl⟩ : syracuseStep 794177 = 595633) B595633
theorem B532043 : Blo 350755 532043 := bstep (se 1 (by rfl) ⟨399032, by rfl⟩ : syracuseStep 532043 = 798065) B798065
theorem B564823 : Blo 350755 564823 := bstep (se 1 (by rfl) ⟨423617, by rfl⟩ : syracuseStep 564823 = 847235) B847235
theorem B532055 : Blo 350755 532055 := bstep (se 1 (by rfl) ⟨399041, by rfl⟩ : syracuseStep 532055 = 798083) B798083
theorem B1908355 : Blo 350755 1908355 := bstep (se 1 (by rfl) ⟨1431266, by rfl⟩ : syracuseStep 1908355 = 2862533) B2862533
theorem B532121 : Blo 350755 532121 := bstep (se 2 (by rfl) ⟨199545, by rfl⟩ : syracuseStep 532121 = 399091) B399091
theorem B1515181 : Blo 350755 1515181 := bstep (se 3 (by rfl) ⟨284096, by rfl⟩ : syracuseStep 1515181 = 568193) B568193
theorem B597719 : Blo 350755 597719 := bstep (se 1 (by rfl) ⟨448289, by rfl⟩ : syracuseStep 597719 = 896579) B896579
theorem B2006801 : Blo 350755 2006801 := bstep (se 2 (by rfl) ⟨752550, by rfl⟩ : syracuseStep 2006801 = 1505101) B1505101
theorem B794393 : Blo 350755 794393 := bstep (se 2 (by rfl) ⟨297897, by rfl⟩ : syracuseStep 794393 = 595795) B595795
theorem B597847 : Blo 350755 597847 := bstep (se 1 (by rfl) ⟨448385, by rfl⟩ : syracuseStep 597847 = 896771) B896771
theorem B794483 : Blo 350755 794483 := bstep (se 1 (by rfl) ⟨595862, by rfl⟩ : syracuseStep 794483 = 1191725) B1191725
theorem B794519 : Blo 350755 794519 := bstep (se 1 (by rfl) ⟨595889, by rfl⟩ : syracuseStep 794519 = 1191779) B1191779
theorem B5742515 : Blo 350755 5742515 := bstep (se 1 (by rfl) ⟨4306886, by rfl⟩ : syracuseStep 5742515 = 8613773) B8613773
theorem B1777625 : Blo 350755 1777625 := bstep (se 2 (by rfl) ⟨666609, by rfl⟩ : syracuseStep 1777625 = 1333219) B1333219
theorem B1187891 : Blo 350755 1187891 := bstep (se 1 (by rfl) ⟨890918, by rfl⟩ : syracuseStep 1187891 = 1781837) B1781837
theorem B794699 : Blo 350755 794699 := bstep (se 1 (by rfl) ⟨596024, by rfl⟩ : syracuseStep 794699 = 1192049) B1192049
theorem B794753 : Blo 350755 794753 := bstep (se 2 (by rfl) ⟨298032, by rfl⟩ : syracuseStep 794753 = 596065) B596065
theorem B893207 : Blo 350755 893207 := bstep (se 1 (by rfl) ⟨669905, by rfl⟩ : syracuseStep 893207 = 1339811) B1339811
theorem B1188161 : Blo 350755 1188161 := bstep (se 2 (by rfl) ⟨445560, by rfl⟩ : syracuseStep 1188161 = 891121) B891121
theorem B565579 : Blo 350755 565579 := bstep (se 1 (by rfl) ⟨424184, by rfl⟩ : syracuseStep 565579 = 848369) B848369
theorem B860491 : Blo 350755 860491 := bstep (se 1 (by rfl) ⟨645368, by rfl⟩ : syracuseStep 860491 = 1290737) B1290737
theorem B794969 : Blo 350755 794969 := bstep (se 2 (by rfl) ⟨298113, by rfl⟩ : syracuseStep 794969 = 596227) B596227
theorem B795059 : Blo 350755 795059 := bstep (se 1 (by rfl) ⟨596294, by rfl⟩ : syracuseStep 795059 = 1192589) B1192589
theorem B598475 : Blo 350755 598475 := bstep (se 1 (by rfl) ⟨448856, by rfl⟩ : syracuseStep 598475 = 897713) B897713
theorem B795095 : Blo 350755 795095 := bstep (se 1 (by rfl) ⟨596321, by rfl⟩ : syracuseStep 795095 = 1192643) B1192643
theorem B500185 : Blo 350755 500185 := bstep (se 2 (by rfl) ⟨187569, by rfl⟩ : syracuseStep 500185 = 375139) B375139
theorem B598603 : Blo 350755 598603 := bstep (se 1 (by rfl) ⟨448952, by rfl⟩ : syracuseStep 598603 = 897905) B897905
theorem B795275 : Blo 350755 795275 := bstep (se 1 (by rfl) ⟨596456, by rfl⟩ : syracuseStep 795275 = 1192913) B1192913
theorem B795329 : Blo 350755 795329 := bstep (se 2 (by rfl) ⟨298248, by rfl⟩ : syracuseStep 795329 = 596497) B596497
theorem B1188701 : Blo 350755 1188701 := bstep (se 3 (by rfl) ⟨222881, by rfl⟩ : syracuseStep 1188701 = 445763) B445763
theorem B795545 : Blo 350755 795545 := bstep (se 2 (by rfl) ⟨298329, by rfl⟩ : syracuseStep 795545 = 596659) B596659
theorem B893875 : Blo 350755 893875 := bstep (se 1 (by rfl) ⟨670406, by rfl⟩ : syracuseStep 893875 = 1340813) B1340813
theorem B795635 : Blo 350755 795635 := bstep (se 1 (by rfl) ⟨596726, by rfl⟩ : syracuseStep 795635 = 1193453) B1193453
theorem B795671 : Blo 350755 795671 := bstep (se 1 (by rfl) ⟨596753, by rfl⟩ : syracuseStep 795671 = 1193507) B1193507
theorem B894017 : Blo 350755 894017 := bstep (se 2 (by rfl) ⟨335256, by rfl⟩ : syracuseStep 894017 = 670513) B670513
theorem B402571 : Blo 350755 402571 := bstep (se 1 (by rfl) ⟨301928, by rfl⟩ : syracuseStep 402571 = 603857) B603857
theorem B795851 : Blo 350755 795851 := bstep (se 1 (by rfl) ⟨596888, by rfl⟩ : syracuseStep 795851 = 1193777) B1193777
theorem B795905 : Blo 350755 795905 := bstep (se 2 (by rfl) ⟨298464, by rfl⟩ : syracuseStep 795905 = 596929) B596929
theorem B566681 : Blo 350755 566681 := bstep (se 2 (by rfl) ⟨212505, by rfl⟩ : syracuseStep 566681 = 425011) B425011
theorem B796121 : Blo 350755 796121 := bstep (se 2 (by rfl) ⟨298545, by rfl⟩ : syracuseStep 796121 = 597091) B597091
theorem B1779245 : Blo 350755 1779245 := bstep (se 3 (by rfl) ⟨333608, by rfl⟩ : syracuseStep 1779245 = 667217) B667217
theorem B796211 : Blo 350755 796211 := bstep (se 1 (by rfl) ⟨597158, by rfl⟩ : syracuseStep 796211 = 1194317) B1194317
theorem B796247 : Blo 350755 796247 := bstep (se 1 (by rfl) ⟨597185, by rfl⟩ : syracuseStep 796247 = 1194371) B1194371
theorem B3024485 : Blo 350755 3024485 := bstep (se 4 (by rfl) ⟨283545, by rfl⟩ : syracuseStep 3024485 = 567091) B567091
theorem B796427 : Blo 350755 796427 := bstep (se 1 (by rfl) ⟨597320, by rfl⟩ : syracuseStep 796427 = 1194641) B1194641
theorem B796481 : Blo 350755 796481 := bstep (se 2 (by rfl) ⟨298680, by rfl⟩ : syracuseStep 796481 = 597361) B597361
theorem B501643 : Blo 350755 501643 := bstep (se 1 (by rfl) ⟨376232, by rfl⟩ : syracuseStep 501643 = 752465) B752465
theorem B501655 : Blo 350755 501655 := bstep (se 1 (by rfl) ⟨376241, by rfl⟩ : syracuseStep 501655 = 752483) B752483
theorem B1189835 : Blo 350755 1189835 := bstep (se 1 (by rfl) ⟨892376, by rfl⟩ : syracuseStep 1189835 = 1784753) B1784753
theorem B403447 : Blo 350755 403447 := bstep (se 1 (by rfl) ⟨302585, by rfl⟩ : syracuseStep 403447 = 605171) B605171
theorem B796697 : Blo 350755 796697 := bstep (se 2 (by rfl) ⟨298761, by rfl⟩ : syracuseStep 796697 = 597523) B597523
theorem B796787 : Blo 350755 796787 := bstep (se 1 (by rfl) ⟨597590, by rfl⟩ : syracuseStep 796787 = 1195181) B1195181
theorem B632983 : Blo 350755 632983 := bstep (se 1 (by rfl) ⟨474737, by rfl⟩ : syracuseStep 632983 = 949475) B949475
theorem B796823 : Blo 350755 796823 := bstep (se 1 (by rfl) ⟨597617, by rfl⟩ : syracuseStep 796823 = 1195235) B1195235
theorem B1190105 : Blo 350755 1190105 := bstep (se 2 (by rfl) ⟨446289, by rfl⟩ : syracuseStep 1190105 = 892579) B892579
theorem B469271 : Blo 350755 469271 := bstep (se 1 (by rfl) ⟨351953, by rfl⟩ : syracuseStep 469271 = 703907) B703907
theorem B895283 : Blo 350755 895283 := bstep (se 1 (by rfl) ⟨671462, by rfl⟩ : syracuseStep 895283 = 1342925) B1342925
theorem B797003 : Blo 350755 797003 := bstep (se 1 (by rfl) ⟨597752, by rfl⟩ : syracuseStep 797003 = 1195505) B1195505
theorem B600409 : Blo 350755 600409 := bstep (se 2 (by rfl) ⟨225153, by rfl⟩ : syracuseStep 600409 = 450307) B450307
theorem B797057 : Blo 350755 797057 := bstep (se 2 (by rfl) ⟨298896, by rfl⟩ : syracuseStep 797057 = 597793) B597793
theorem B665995 : Blo 350755 665995 := bstep (se 1 (by rfl) ⟨499496, by rfl⟩ : syracuseStep 665995 = 998993) B998993
theorem B1354157 : Blo 350755 1354157 := bstep (se 3 (by rfl) ⟨253904, by rfl⟩ : syracuseStep 1354157 = 507809) B507809
theorem B797273 : Blo 350755 797273 := bstep (se 2 (by rfl) ⟨298977, by rfl⟩ : syracuseStep 797273 = 597955) B597955
theorem B797363 : Blo 350755 797363 := bstep (se 1 (by rfl) ⟨598022, by rfl⟩ : syracuseStep 797363 = 1196045) B1196045
theorem B797399 : Blo 350755 797399 := bstep (se 1 (by rfl) ⟨598049, by rfl⟩ : syracuseStep 797399 = 1196099) B1196099
theorem B3222317 : Blo 350755 3222317 := bstep (se 3 (by rfl) ⟨604184, by rfl⟩ : syracuseStep 3222317 = 1208369) B1208369
theorem B666443 : Blo 350755 666443 := bstep (se 1 (by rfl) ⟨499832, by rfl⟩ : syracuseStep 666443 = 999665) B999665
theorem B895819 : Blo 350755 895819 := bstep (se 1 (by rfl) ⟨671864, by rfl⟩ : syracuseStep 895819 = 1343729) B1343729
theorem B797579 : Blo 350755 797579 := bstep (se 1 (by rfl) ⟨598184, by rfl⟩ : syracuseStep 797579 = 1196369) B1196369
theorem B1190807 : Blo 350755 1190807 := bstep (se 1 (by rfl) ⟨893105, by rfl⟩ : syracuseStep 1190807 = 1786211) B1786211
theorem B1420183 : Blo 350755 1420183 := bstep (se 1 (by rfl) ⟨1065137, by rfl⟩ : syracuseStep 1420183 = 2130275) B2130275
theorem B2534323 : Blo 350755 2534323 := bstep (se 1 (by rfl) ⟨1900742, by rfl⟩ : syracuseStep 2534323 = 3801485) B3801485
theorem B2010035 : Blo 350755 2010035 := bstep (se 1 (by rfl) ⟨1507526, by rfl⟩ : syracuseStep 2010035 = 3015053) B3015053
theorem B797633 : Blo 350755 797633 := bstep (se 2 (by rfl) ⟨299112, by rfl⟩ : syracuseStep 797633 = 598225) B598225
theorem B12331993 : Blo 350755 12331993 := bstep (se 2 (by rfl) ⟨4624497, by rfl⟩ : syracuseStep 12331993 = 9248995) B9248995
theorem B895961 : Blo 350755 895961 := bstep (se 2 (by rfl) ⟨335985, by rfl⟩ : syracuseStep 895961 = 671971) B671971
theorem B666625 : Blo 350755 666625 := bstep (se 2 (by rfl) ⟨249984, by rfl⟩ : syracuseStep 666625 = 499969) B499969
theorem B797849 : Blo 350755 797849 := bstep (se 2 (by rfl) ⟨299193, by rfl⟩ : syracuseStep 797849 = 598387) B598387
theorem B797939 : Blo 350755 797939 := bstep (se 1 (by rfl) ⟨598454, by rfl⟩ : syracuseStep 797939 = 1196909) B1196909
theorem B797975 : Blo 350755 797975 := bstep (se 1 (by rfl) ⟨598481, by rfl⟩ : syracuseStep 797975 = 1196963) B1196963
theorem B666967 : Blo 350755 666967 := bstep (se 1 (by rfl) ⟨500225, by rfl⟩ : syracuseStep 666967 = 1000451) B1000451
theorem B1191347 : Blo 350755 1191347 := bstep (se 1 (by rfl) ⟨893510, by rfl⟩ : syracuseStep 1191347 = 1787021) B1787021
theorem B798155 : Blo 350755 798155 := bstep (se 1 (by rfl) ⟨598616, by rfl⟩ : syracuseStep 798155 = 1197233) B1197233
theorem B667187 : Blo 350755 667187 := bstep (se 1 (by rfl) ⟨500390, by rfl⟩ : syracuseStep 667187 = 1000781) B1000781
theorem B634483 : Blo 350755 634483 := bstep (se 1 (by rfl) ⟨475862, by rfl⟩ : syracuseStep 634483 = 951725) B951725
theorem B634547 : Blo 350755 634547 := bstep (se 1 (by rfl) ⟨475910, by rfl⟩ : syracuseStep 634547 = 951821) B951821
theorem B1191617 : Blo 350755 1191617 := bstep (se 2 (by rfl) ⟨446856, by rfl⟩ : syracuseStep 1191617 = 893713) B893713
theorem B667415 : Blo 350755 667415 := bstep (se 1 (by rfl) ⟨500561, by rfl⟩ : syracuseStep 667415 = 1001123) B1001123
theorem B896791 : Blo 350755 896791 := bstep (se 1 (by rfl) ⟨672593, by rfl⟩ : syracuseStep 896791 = 1345187) B1345187
theorem B1126237 : Blo 350755 1126237 := bstep (se 3 (by rfl) ⟨211169, by rfl⟩ : syracuseStep 1126237 = 422339) B422339
theorem B503705 : Blo 350755 503705 := bstep (se 2 (by rfl) ⟨188889, by rfl⟩ : syracuseStep 503705 = 377779) B377779
theorem B667673 : Blo 350755 667673 := bstep (se 2 (by rfl) ⟨250377, by rfl⟩ : syracuseStep 667673 = 500755) B500755
theorem B897227 : Blo 350755 897227 := bstep (se 1 (by rfl) ⟨672920, by rfl⟩ : syracuseStep 897227 = 1345841) B1345841
theorem B1192157 : Blo 350755 1192157 := bstep (se 3 (by rfl) ⟨223529, by rfl⟩ : syracuseStep 1192157 = 447059) B447059
theorem B2011493 : Blo 350755 2011493 := bstep (se 4 (by rfl) ⟨188577, by rfl⟩ : syracuseStep 2011493 = 377155) B377155
theorem B668083 : Blo 350755 668083 := bstep (se 1 (by rfl) ⟨501062, by rfl⟩ : syracuseStep 668083 = 1002125) B1002125
theorem B1716659 : Blo 350755 1716659 := bstep (se 1 (by rfl) ⟨1287494, by rfl⟩ : syracuseStep 1716659 = 2574989) B2574989
theorem B504343 : Blo 350755 504343 := bstep (se 1 (by rfl) ⟨378257, by rfl⟩ : syracuseStep 504343 = 756515) B756515
theorem B897601 : Blo 350755 897601 := bstep (se 2 (by rfl) ⟨336600, by rfl⟩ : syracuseStep 897601 = 673201) B673201
theorem B635521 : Blo 350755 635521 := bstep (se 2 (by rfl) ⟨238320, by rfl⟩ : syracuseStep 635521 = 476641) B476641
theorem B635671 : Blo 350755 635671 := bstep (se 1 (by rfl) ⟨476753, by rfl⟩ : syracuseStep 635671 = 953507) B953507
theorem B2011949 : Blo 350755 2011949 := bstep (se 3 (by rfl) ⟨377240, by rfl⟩ : syracuseStep 2011949 = 754481) B754481
theorem B1356695 : Blo 350755 1356695 := bstep (se 1 (by rfl) ⟨1017521, by rfl⟩ : syracuseStep 1356695 = 2035043) B2035043
theorem B668569 : Blo 350755 668569 := bstep (se 2 (by rfl) ⟨250713, by rfl⟩ : syracuseStep 668569 = 501427) B501427
theorem B3814721 : Blo 350755 3814721 := bstep (se 2 (by rfl) ⟨1430520, by rfl⟩ : syracuseStep 3814721 = 2861041) B2861041
theorem B1193291 : Blo 350755 1193291 := bstep (se 1 (by rfl) ⟨894968, by rfl⟩ : syracuseStep 1193291 = 1789937) B1789937
theorem B1783133 : Blo 350755 1783133 := bstep (se 3 (by rfl) ⟨334337, by rfl⟩ : syracuseStep 1783133 = 668675) B668675
theorem B669131 : Blo 350755 669131 := bstep (se 1 (by rfl) ⟨501848, by rfl⟩ : syracuseStep 669131 = 1003697) B1003697
theorem B2012633 : Blo 350755 2012633 := bstep (se 2 (by rfl) ⟨754737, by rfl⟩ : syracuseStep 2012633 = 1509475) B1509475
theorem B5060171 : Blo 350755 5060171 := bstep (se 1 (by rfl) ⟨3795128, by rfl⟩ : syracuseStep 5060171 = 7590257) B7590257
theorem B1193561 : Blo 350755 1193561 := bstep (se 2 (by rfl) ⟨447585, by rfl⟩ : syracuseStep 1193561 = 895171) B895171
theorem B669313 : Blo 350755 669313 := bstep (se 2 (by rfl) ⟨250992, by rfl⟩ : syracuseStep 669313 = 501985) B501985
theorem B800471 : Blo 350755 800471 := bstep (se 1 (by rfl) ⟨600353, by rfl⟩ : syracuseStep 800471 = 1200707) B1200707
theorem B374635 : Blo 350755 374635 := bstep (se 1 (by rfl) ⟨280976, by rfl⟩ : syracuseStep 374635 = 561953) B561953
theorem B3061709 : Blo 350755 3061709 := bstep (se 3 (by rfl) ⟨574070, by rfl⟩ : syracuseStep 3061709 = 1148141) B1148141
theorem B2046053 : Blo 350755 2046053 := bstep (se 4 (by rfl) ⟨191817, by rfl⟩ : syracuseStep 2046053 = 383635) B383635
theorem B1194263 : Blo 350755 1194263 := bstep (se 1 (by rfl) ⟨895697, by rfl⟩ : syracuseStep 1194263 = 1791395) B1791395
theorem B670027 : Blo 350755 670027 := bstep (se 1 (by rfl) ⟨502520, by rfl⟩ : syracuseStep 670027 = 1005041) B1005041
theorem B670103 : Blo 350755 670103 := bstep (se 1 (by rfl) ⟨502577, by rfl⟩ : syracuseStep 670103 = 1005155) B1005155
theorem B1686109 : Blo 350755 1686109 := bstep (se 3 (by rfl) ⟨316145, by rfl⟩ : syracuseStep 1686109 = 632291) B632291
theorem B1686167 : Blo 350755 1686167 := bstep (se 1 (by rfl) ⟨1264625, by rfl⟩ : syracuseStep 1686167 = 2529251) B2529251
theorem B375511 : Blo 350755 375511 := bstep (se 1 (by rfl) ⟨281633, by rfl⟩ : syracuseStep 375511 = 563267) B563267
theorem B1194803 : Blo 350755 1194803 := bstep (se 1 (by rfl) ⟨896102, by rfl⟩ : syracuseStep 1194803 = 1792205) B1792205
theorem B2997283 : Blo 350755 2997283 := bstep (se 1 (by rfl) ⟨2247962, by rfl⟩ : syracuseStep 2997283 = 4495925) B4495925
theorem B670771 : Blo 350755 670771 := bstep (se 1 (by rfl) ⟨503078, by rfl⟩ : syracuseStep 670771 = 1006157) B1006157
theorem B1195073 : Blo 350755 1195073 := bstep (se 2 (by rfl) ⟨448152, by rfl⟩ : syracuseStep 1195073 = 896305) B896305
theorem B375959 : Blo 350755 375959 := bstep (se 1 (by rfl) ⟨281969, by rfl⟩ : syracuseStep 375959 = 563939) B563939
theorem B2538647 : Blo 350755 2538647 := bstep (se 1 (by rfl) ⟨1903985, by rfl⟩ : syracuseStep 2538647 = 3807971) B3807971
theorem B638209 : Blo 350755 638209 := bstep (se 2 (by rfl) ⟨239328, by rfl⟩ : syracuseStep 638209 = 478657) B478657
theorem B670999 : Blo 350755 670999 := bstep (se 1 (by rfl) ⟨503249, by rfl⟩ : syracuseStep 670999 = 1006499) B1006499
theorem B671105 : Blo 350755 671105 := bstep (se 2 (by rfl) ⟨251664, by rfl⟩ : syracuseStep 671105 = 503329) B503329
theorem B1785239 : Blo 350755 1785239 := bstep (se 1 (by rfl) ⟨1338929, by rfl⟩ : syracuseStep 1785239 = 2677859) B2677859
theorem B376331 : Blo 350755 376331 := bstep (se 1 (by rfl) ⟨282248, by rfl⟩ : syracuseStep 376331 = 564497) B564497
theorem B671257 : Blo 350755 671257 := bstep (se 2 (by rfl) ⟨251721, by rfl⟩ : syracuseStep 671257 = 503443) B503443
theorem B1195613 : Blo 350755 1195613 := bstep (se 3 (by rfl) ⟨224177, by rfl⟩ : syracuseStep 1195613 = 448355) B448355
theorem B638771 : Blo 350755 638771 := bstep (se 1 (by rfl) ⟨479078, by rfl⟩ : syracuseStep 638771 = 958157) B958157
theorem B638923 : Blo 350755 638923 := bstep (se 1 (by rfl) ⟨479192, by rfl⟩ : syracuseStep 638923 = 958385) B958385
theorem B2146265 : Blo 350755 2146265 := bstep (se 2 (by rfl) ⟨804849, by rfl⟩ : syracuseStep 2146265 = 1609699) B1609699
theorem B573655 : Blo 350755 573655 := bstep (se 1 (by rfl) ⟨430241, by rfl⟩ : syracuseStep 573655 = 860483) B860483
theorem B999641 : Blo 350755 999641 := bstep (se 2 (by rfl) ⟨374865, by rfl⟩ : syracuseStep 999641 = 749731) B749731
theorem B377335 : Blo 350755 377335 := bstep (se 1 (by rfl) ⟨283001, by rfl⟩ : syracuseStep 377335 = 566003) B566003
theorem B836185 : Blo 350755 836185 := bstep (se 2 (by rfl) ⟨313569, by rfl⟩ : syracuseStep 836185 = 627139) B627139
theorem B1196747 : Blo 350755 1196747 := bstep (se 1 (by rfl) ⟨897560, by rfl⟩ : syracuseStep 1196747 = 1795121) B1795121
theorem B672563 : Blo 350755 672563 := bstep (se 1 (by rfl) ⟨504422, by rfl⟩ : syracuseStep 672563 = 1008845) B1008845
theorem B1426369 : Blo 350755 1426369 := bstep (se 2 (by rfl) ⟨534888, by rfl⟩ : syracuseStep 1426369 = 1069777) B1069777
theorem B672715 : Blo 350755 672715 := bstep (se 1 (by rfl) ⟨504536, by rfl⟩ : syracuseStep 672715 = 1009073) B1009073
theorem B1197017 : Blo 350755 1197017 := bstep (se 2 (by rfl) ⟨448881, by rfl⟩ : syracuseStep 1197017 = 897763) B897763
theorem B6177809 : Blo 350755 6177809 := bstep (se 2 (by rfl) ⟨2316678, by rfl⟩ : syracuseStep 6177809 = 4633357) B4633357
theorem B476299 : Blo 350755 476299 := bstep (se 1 (by rfl) ⟨357224, by rfl⟩ : syracuseStep 476299 = 714449) B714449
theorem B1131671 : Blo 350755 1131671 := bstep (se 1 (by rfl) ⟨848753, by rfl⟩ : syracuseStep 1131671 = 1697507) B1697507
theorem B1426691 : Blo 350755 1426691 := bstep (se 1 (by rfl) ⟨1070018, by rfl⟩ : syracuseStep 1426691 = 2140037) B2140037
theorem B673049 : Blo 350755 673049 := bstep (se 2 (by rfl) ⟨252393, by rfl⟩ : syracuseStep 673049 = 504787) B504787
theorem B378155 : Blo 350755 378155 := bstep (se 1 (by rfl) ⟨283616, by rfl⟩ : syracuseStep 378155 = 567233) B567233
theorem B1000907 : Blo 350755 1000907 := bstep (se 1 (by rfl) ⟨750680, by rfl⟩ : syracuseStep 1000907 = 1501361) B1501361
theorem B2606627 : Blo 350755 2606627 := bstep (se 1 (by rfl) ⟨1954970, by rfl⟩ : syracuseStep 2606627 = 3909941) B3909941
theorem B4867715 : Blo 350755 4867715 := bstep (se 1 (by rfl) ⟨3650786, by rfl⟩ : syracuseStep 4867715 = 7301573) B7301573
theorem B804505 : Blo 350755 804505 := bstep (se 2 (by rfl) ⟨301689, by rfl⟩ : syracuseStep 804505 = 603379) B603379
theorem B2017325 : Blo 350755 2017325 := bstep (se 3 (by rfl) ⟨378248, by rfl⟩ : syracuseStep 2017325 = 756497) B756497
theorem B444619 : Blo 350755 444619 := bstep (se 1 (by rfl) ⟨333464, by rfl⟩ : syracuseStep 444619 = 666929) B666929
theorem B1689817 : Blo 350755 1689817 := bstep (se 2 (by rfl) ⟨633681, by rfl⟩ : syracuseStep 1689817 = 1267363) B1267363
theorem B1362251 : Blo 350755 1362251 := bstep (se 1 (by rfl) ⟨1021688, by rfl⟩ : syracuseStep 1362251 = 2043377) B2043377
theorem B2443699 : Blo 350755 2443699 := bstep (se 1 (by rfl) ⟨1832774, by rfl⟩ : syracuseStep 2443699 = 3665549) B3665549
theorem B1133003 : Blo 350755 1133003 := bstep (se 1 (by rfl) ⟨849752, by rfl⟩ : syracuseStep 1133003 = 1699505) B1699505
theorem B1264193 : Blo 350755 1264193 := bstep (se 2 (by rfl) ⟨474072, by rfl⟩ : syracuseStep 1264193 = 948145) B948145
theorem B477911 : Blo 350755 477911 := bstep (se 1 (by rfl) ⟨358433, by rfl⟩ : syracuseStep 477911 = 716867) B716867
theorem B1690433 : Blo 350755 1690433 := bstep (se 2 (by rfl) ⟨633912, by rfl⟩ : syracuseStep 1690433 = 1267825) B1267825
theorem B1788803 : Blo 350755 1788803 := bstep (se 1 (by rfl) ⟨1341602, by rfl⟩ : syracuseStep 1788803 = 2683205) B2683205
theorem B1428445 : Blo 350755 1428445 := bstep (se 3 (by rfl) ⟨267833, by rfl⟩ : syracuseStep 1428445 = 535667) B535667
theorem B445591 : Blo 350755 445591 := bstep (se 1 (by rfl) ⟨334193, by rfl⟩ : syracuseStep 445591 = 668387) B668387
theorem B1133747 : Blo 350755 1133747 := bstep (se 1 (by rfl) ⟨850310, by rfl⟩ : syracuseStep 1133747 = 1700621) B1700621
theorem B3263921 : Blo 350755 3263921 := bstep (se 2 (by rfl) ⟨1223970, by rfl⟩ : syracuseStep 3263921 = 2447941) B2447941
theorem B6049241 : Blo 350755 6049241 := bstep (se 2 (by rfl) ⟨2268465, by rfl⟩ : syracuseStep 6049241 = 4536931) B4536931
theorem B675353 : Blo 350755 675353 := bstep (se 2 (by rfl) ⟨253257, by rfl⟩ : syracuseStep 675353 = 506515) B506515
theorem B1691201 : Blo 350755 1691201 := bstep (se 2 (by rfl) ⟨634200, by rfl⟩ : syracuseStep 1691201 = 1268401) B1268401
theorem B3001931 : Blo 350755 3001931 := bstep (se 1 (by rfl) ⟨2251448, by rfl⟩ : syracuseStep 3001931 = 4502897) B4502897
theorem B18665315 : Blo 350755 18665315 := bstep (se 1 (by rfl) ⟨13998986, by rfl⟩ : syracuseStep 18665315 = 27997973) B27997973
theorem B446411 : Blo 350755 446411 := bstep (se 1 (by rfl) ⟨334808, by rfl⟩ : syracuseStep 446411 = 669617) B669617
theorem B1134643 : Blo 350755 1134643 := bstep (se 1 (by rfl) ⟨850982, by rfl⟩ : syracuseStep 1134643 = 1701965) B1701965
theorem B4837637 : Blo 350755 4837637 := bstep (se 4 (by rfl) ⟨453528, by rfl⟩ : syracuseStep 4837637 = 907057) B907057
theorem B610763 : Blo 350755 610763 := bstep (se 1 (by rfl) ⟨458072, by rfl⟩ : syracuseStep 610763 = 916145) B916145
theorem B447115 : Blo 350755 447115 := bstep (se 1 (by rfl) ⟨335336, by rfl⟩ : syracuseStep 447115 = 670673) B670673
theorem B1462963 : Blo 350755 1462963 := bstep (se 1 (by rfl) ⟨1097222, by rfl⟩ : syracuseStep 1462963 = 2194445) B2194445
theorem B2249603 : Blo 350755 2249603 := bstep (se 1 (by rfl) ⟨1687202, by rfl⟩ : syracuseStep 2249603 = 3374405) B3374405
theorem B447383 : Blo 350755 447383 := bstep (se 1 (by rfl) ⟨335537, by rfl⟩ : syracuseStep 447383 = 671075) B671075
theorem B1332247 : Blo 350755 1332247 := bstep (se 1 (by rfl) ⟨999185, by rfl⟩ : syracuseStep 1332247 = 1998371) B1998371
theorem B1266961 : Blo 350755 1266961 := bstep (se 2 (by rfl) ⟨475110, by rfl⟩ : syracuseStep 1266961 = 950221) B950221
theorem B1627523 : Blo 350755 1627523 := bstep (se 1 (by rfl) ⟨1220642, by rfl⟩ : syracuseStep 1627523 = 2441285) B2441285
theorem B5854643 : Blo 350755 5854643 := bstep (se 1 (by rfl) ⟨4390982, by rfl⟩ : syracuseStep 5854643 = 8781965) B8781965
theorem B448087 : Blo 350755 448087 := bstep (se 1 (by rfl) ⟨336065, by rfl⟩ : syracuseStep 448087 = 672131) B672131
theorem B808537 : Blo 350755 808537 := bstep (se 2 (by rfl) ⟨303201, by rfl⟩ : syracuseStep 808537 = 606403) B606403
theorem B2676401 : Blo 350755 2676401 := bstep (se 2 (by rfl) ⟨1003650, by rfl⟩ : syracuseStep 2676401 = 2007301) B2007301
theorem B1333037 : Blo 350755 1333037 := bstep (se 3 (by rfl) ⟨249944, by rfl⟩ : syracuseStep 1333037 = 499889) B499889
theorem B808883 : Blo 350755 808883 := bstep (se 1 (by rfl) ⟨606662, by rfl⟩ : syracuseStep 808883 = 1213325) B1213325
theorem B2676887 : Blo 350755 2676887 := bstep (se 1 (by rfl) ⟨2007665, by rfl⟩ : syracuseStep 2676887 = 4015331) B4015331
theorem B1792529 : Blo 350755 1792529 := bstep (se 2 (by rfl) ⟨672198, by rfl⟩ : syracuseStep 1792529 = 1344397) B1344397
theorem B350763 : Blo 350755 350763 := bstep (se 1 (by rfl) ⟨263072, by rfl⟩ : syracuseStep 350763 = 526145) B526145
theorem B350775 : Blo 350755 350775 := bstep (se 1 (by rfl) ⟨263081, by rfl⟩ : syracuseStep 350775 = 526163) B526163
theorem B350795 : Blo 350755 350795 := bstep (se 1 (by rfl) ⟨263096, by rfl⟩ : syracuseStep 350795 = 526193) B526193
theorem B350807 : Blo 350755 350807 := bstep (se 1 (by rfl) ⟨263105, by rfl⟩ : syracuseStep 350807 = 526211) B526211
theorem B481879 : Blo 350755 481879 := bstep (se 1 (by rfl) ⟨361409, by rfl⟩ : syracuseStep 481879 = 722819) B722819
theorem B350827 : Blo 350755 350827 := bstep (se 1 (by rfl) ⟨263120, by rfl⟩ : syracuseStep 350827 = 526241) B526241
theorem B350839 : Blo 350755 350839 := bstep (se 1 (by rfl) ⟨263129, by rfl⟩ : syracuseStep 350839 = 526259) B526259
theorem B350859 : Blo 350755 350859 := bstep (se 1 (by rfl) ⟨263144, by rfl⟩ : syracuseStep 350859 = 526289) B526289
theorem B350871 : Blo 350755 350871 := bstep (se 1 (by rfl) ⟨263153, by rfl⟩ : syracuseStep 350871 = 526307) B526307
theorem B350891 : Blo 350755 350891 := bstep (se 1 (by rfl) ⟨263168, by rfl⟩ : syracuseStep 350891 = 526337) B526337
theorem B1792691 : Blo 350755 1792691 := bstep (se 1 (by rfl) ⟨1344518, by rfl⟩ : syracuseStep 1792691 = 2689037) B2689037
theorem B350903 : Blo 350755 350903 := bstep (se 1 (by rfl) ⟨263177, by rfl⟩ : syracuseStep 350903 = 526355) B526355
theorem B350923 : Blo 350755 350923 := bstep (se 1 (by rfl) ⟨263192, by rfl⟩ : syracuseStep 350923 = 526385) B526385
theorem B1006283 : Blo 350755 1006283 := bstep (se 1 (by rfl) ⟨754712, by rfl⟩ : syracuseStep 1006283 = 1509425) B1509425
theorem B350935 : Blo 350755 350935 := bstep (se 1 (by rfl) ⟨263201, by rfl⟩ : syracuseStep 350935 = 526403) B526403
theorem B350955 : Blo 350755 350955 := bstep (se 1 (by rfl) ⟨263216, by rfl⟩ : syracuseStep 350955 = 526433) B526433
theorem B350967 : Blo 350755 350967 := bstep (se 1 (by rfl) ⟨263225, by rfl⟩ : syracuseStep 350967 = 526451) B526451
theorem B350987 : Blo 350755 350987 := bstep (se 1 (by rfl) ⟨263240, by rfl⟩ : syracuseStep 350987 = 526481) B526481
theorem B350999 : Blo 350755 350999 := bstep (se 1 (by rfl) ⟨263249, by rfl⟩ : syracuseStep 350999 = 526499) B526499
theorem B351019 : Blo 350755 351019 := bstep (se 1 (by rfl) ⟨263264, by rfl⟩ : syracuseStep 351019 = 526529) B526529
theorem B908083 : Blo 350755 908083 := bstep (se 1 (by rfl) ⟨681062, by rfl⟩ : syracuseStep 908083 = 1362125) B1362125
theorem B351031 : Blo 350755 351031 := bstep (se 1 (by rfl) ⟨263273, by rfl⟩ : syracuseStep 351031 = 526547) B526547
theorem B351051 : Blo 350755 351051 := bstep (se 1 (by rfl) ⟨263288, by rfl⟩ : syracuseStep 351051 = 526577) B526577
theorem B351063 : Blo 350755 351063 := bstep (se 1 (by rfl) ⟨263297, by rfl⟩ : syracuseStep 351063 = 526595) B526595
theorem B6970211 : Blo 350755 6970211 := bstep (se 1 (by rfl) ⟨5227658, by rfl⟩ : syracuseStep 6970211 = 10455317) B10455317
theorem B351083 : Blo 350755 351083 := bstep (se 1 (by rfl) ⟨263312, by rfl⟩ : syracuseStep 351083 = 526625) B526625
theorem B351095 : Blo 350755 351095 := bstep (se 1 (by rfl) ⟨263321, by rfl⟩ : syracuseStep 351095 = 526643) B526643
theorem B351115 : Blo 350755 351115 := bstep (se 1 (by rfl) ⟨263336, by rfl⟩ : syracuseStep 351115 = 526673) B526673
theorem B351127 : Blo 350755 351127 := bstep (se 1 (by rfl) ⟨263345, by rfl⟩ : syracuseStep 351127 = 526691) B526691
theorem B351147 : Blo 350755 351147 := bstep (se 1 (by rfl) ⟨263360, by rfl⟩ : syracuseStep 351147 = 526721) B526721
theorem B1727411 : Blo 350755 1727411 := bstep (se 1 (by rfl) ⟨1295558, by rfl⟩ : syracuseStep 1727411 = 2591117) B2591117
theorem B351159 : Blo 350755 351159 := bstep (se 1 (by rfl) ⟨263369, by rfl⟩ : syracuseStep 351159 = 526739) B526739
theorem B351179 : Blo 350755 351179 := bstep (se 1 (by rfl) ⟨263384, by rfl⟩ : syracuseStep 351179 = 526769) B526769
theorem B351191 : Blo 350755 351191 := bstep (se 1 (by rfl) ⟨263393, by rfl⟩ : syracuseStep 351191 = 526787) B526787
theorem B351211 : Blo 350755 351211 := bstep (se 1 (by rfl) ⟨263408, by rfl⟩ : syracuseStep 351211 = 526817) B526817
theorem B351223 : Blo 350755 351223 := bstep (se 1 (by rfl) ⟨263417, by rfl⟩ : syracuseStep 351223 = 526835) B526835
theorem B351243 : Blo 350755 351243 := bstep (se 1 (by rfl) ⟨263432, by rfl⟩ : syracuseStep 351243 = 526865) B526865
theorem B351255 : Blo 350755 351255 := bstep (se 1 (by rfl) ⟨263441, by rfl⟩ : syracuseStep 351255 = 526883) B526883
theorem B351275 : Blo 350755 351275 := bstep (se 1 (by rfl) ⟨263456, by rfl⟩ : syracuseStep 351275 = 526913) B526913
theorem B351287 : Blo 350755 351287 := bstep (se 1 (by rfl) ⟨263465, by rfl⟩ : syracuseStep 351287 = 526931) B526931
theorem B351307 : Blo 350755 351307 := bstep (se 1 (by rfl) ⟨263480, by rfl⟩ : syracuseStep 351307 = 526961) B526961
theorem B351319 : Blo 350755 351319 := bstep (se 1 (by rfl) ⟨263489, by rfl⟩ : syracuseStep 351319 = 526979) B526979
theorem B1006681 : Blo 350755 1006681 := bstep (se 2 (by rfl) ⟨377505, by rfl⟩ : syracuseStep 1006681 = 755011) B755011
theorem B351339 : Blo 350755 351339 := bstep (se 1 (by rfl) ⟨263504, by rfl⟩ : syracuseStep 351339 = 527009) B527009
theorem B351351 : Blo 350755 351351 := bstep (se 1 (by rfl) ⟨263513, by rfl⟩ : syracuseStep 351351 = 527027) B527027
theorem B351371 : Blo 350755 351371 := bstep (se 1 (by rfl) ⟨263528, by rfl⟩ : syracuseStep 351371 = 527057) B527057
theorem B351383 : Blo 350755 351383 := bstep (se 1 (by rfl) ⟨263537, by rfl⟩ : syracuseStep 351383 = 527075) B527075
theorem B351403 : Blo 350755 351403 := bstep (se 1 (by rfl) ⟨263552, by rfl⟩ : syracuseStep 351403 = 527105) B527105
theorem B351415 : Blo 350755 351415 := bstep (se 1 (by rfl) ⟨263561, by rfl⟩ : syracuseStep 351415 = 527123) B527123
theorem B1334465 : Blo 350755 1334465 := bstep (se 2 (by rfl) ⟨500424, by rfl⟩ : syracuseStep 1334465 = 1000849) B1000849
theorem B351435 : Blo 350755 351435 := bstep (se 1 (by rfl) ⟨263576, by rfl⟩ : syracuseStep 351435 = 527153) B527153
theorem B351447 : Blo 350755 351447 := bstep (se 1 (by rfl) ⟨263585, by rfl⟩ : syracuseStep 351447 = 527171) B527171
theorem B351467 : Blo 350755 351467 := bstep (se 1 (by rfl) ⟨263600, by rfl⟩ : syracuseStep 351467 = 527201) B527201
theorem B351479 : Blo 350755 351479 := bstep (se 1 (by rfl) ⟨263609, by rfl⟩ : syracuseStep 351479 = 527219) B527219
theorem B351499 : Blo 350755 351499 := bstep (se 1 (by rfl) ⟨263624, by rfl⟩ : syracuseStep 351499 = 527249) B527249
theorem B351511 : Blo 350755 351511 := bstep (se 1 (by rfl) ⟨263633, by rfl⟩ : syracuseStep 351511 = 527267) B527267
theorem B351531 : Blo 350755 351531 := bstep (se 1 (by rfl) ⟨263648, by rfl⟩ : syracuseStep 351531 = 527297) B527297
theorem B7232813 : Blo 350755 7232813 := bstep (se 3 (by rfl) ⟨1356152, by rfl⟩ : syracuseStep 7232813 = 2712305) B2712305
theorem B351543 : Blo 350755 351543 := bstep (se 1 (by rfl) ⟨263657, by rfl⟩ : syracuseStep 351543 = 527315) B527315
theorem B351563 : Blo 350755 351563 := bstep (se 1 (by rfl) ⟨263672, by rfl⟩ : syracuseStep 351563 = 527345) B527345
theorem B351575 : Blo 350755 351575 := bstep (se 1 (by rfl) ⟨263681, by rfl⟩ : syracuseStep 351575 = 527363) B527363
theorem B351595 : Blo 350755 351595 := bstep (se 1 (by rfl) ⟨263696, by rfl⟩ : syracuseStep 351595 = 527393) B527393
theorem B351607 : Blo 350755 351607 := bstep (se 1 (by rfl) ⟨263705, by rfl⟩ : syracuseStep 351607 = 527411) B527411
theorem B351627 : Blo 350755 351627 := bstep (se 1 (by rfl) ⟨263720, by rfl⟩ : syracuseStep 351627 = 527441) B527441
theorem B351639 : Blo 350755 351639 := bstep (se 1 (by rfl) ⟨263729, by rfl⟩ : syracuseStep 351639 = 527459) B527459
theorem B351659 : Blo 350755 351659 := bstep (se 1 (by rfl) ⟨263744, by rfl⟩ : syracuseStep 351659 = 527489) B527489
theorem B2907571 : Blo 350755 2907571 := bstep (se 1 (by rfl) ⟨2180678, by rfl⟩ : syracuseStep 2907571 = 4361357) B4361357
theorem B351671 : Blo 350755 351671 := bstep (se 1 (by rfl) ⟨263753, by rfl⟩ : syracuseStep 351671 = 527507) B527507
theorem B351691 : Blo 350755 351691 := bstep (se 1 (by rfl) ⟨263768, by rfl⟩ : syracuseStep 351691 = 527537) B527537
theorem B351703 : Blo 350755 351703 := bstep (se 1 (by rfl) ⟨263777, by rfl⟩ : syracuseStep 351703 = 527555) B527555
theorem B1269209 : Blo 350755 1269209 := bstep (se 2 (by rfl) ⟨475953, by rfl⟩ : syracuseStep 1269209 = 951907) B951907
theorem B351723 : Blo 350755 351723 := bstep (se 1 (by rfl) ⟨263792, by rfl⟩ : syracuseStep 351723 = 527585) B527585
theorem B351735 : Blo 350755 351735 := bstep (se 1 (by rfl) ⟨263801, by rfl⟩ : syracuseStep 351735 = 527603) B527603
theorem B351755 : Blo 350755 351755 := bstep (se 1 (by rfl) ⟨263816, by rfl⟩ : syracuseStep 351755 = 527633) B527633
theorem B351767 : Blo 350755 351767 := bstep (se 1 (by rfl) ⟨263825, by rfl⟩ : syracuseStep 351767 = 527651) B527651
theorem B351787 : Blo 350755 351787 := bstep (se 1 (by rfl) ⟨263840, by rfl⟩ : syracuseStep 351787 = 527681) B527681
theorem B351799 : Blo 350755 351799 := bstep (se 1 (by rfl) ⟨263849, by rfl⟩ : syracuseStep 351799 = 527699) B527699
theorem B351819 : Blo 350755 351819 := bstep (se 1 (by rfl) ⟨263864, by rfl⟩ : syracuseStep 351819 = 527729) B527729
theorem B351831 : Blo 350755 351831 := bstep (se 1 (by rfl) ⟨263873, by rfl⟩ : syracuseStep 351831 = 527747) B527747
theorem B351851 : Blo 350755 351851 := bstep (se 1 (by rfl) ⟨263888, by rfl⟩ : syracuseStep 351851 = 527777) B527777
theorem B351863 : Blo 350755 351863 := bstep (se 1 (by rfl) ⟨263897, by rfl⟩ : syracuseStep 351863 = 527795) B527795
theorem B351883 : Blo 350755 351883 := bstep (se 1 (by rfl) ⟨263912, by rfl⟩ : syracuseStep 351883 = 527825) B527825
theorem B351895 : Blo 350755 351895 := bstep (se 1 (by rfl) ⟨263921, by rfl⟩ : syracuseStep 351895 = 527843) B527843
theorem B351915 : Blo 350755 351915 := bstep (se 1 (by rfl) ⟨263936, by rfl⟩ : syracuseStep 351915 = 527873) B527873
theorem B351927 : Blo 350755 351927 := bstep (se 1 (by rfl) ⟨263945, by rfl⟩ : syracuseStep 351927 = 527891) B527891
theorem B351947 : Blo 350755 351947 := bstep (se 1 (by rfl) ⟨263960, by rfl⟩ : syracuseStep 351947 = 527921) B527921
theorem B351959 : Blo 350755 351959 := bstep (se 1 (by rfl) ⟨263969, by rfl⟩ : syracuseStep 351959 = 527939) B527939
theorem B351979 : Blo 350755 351979 := bstep (se 1 (by rfl) ⟨263984, by rfl⟩ : syracuseStep 351979 = 527969) B527969
theorem B351991 : Blo 350755 351991 := bstep (se 1 (by rfl) ⟨263993, by rfl⟩ : syracuseStep 351991 = 527987) B527987
theorem B352011 : Blo 350755 352011 := bstep (se 1 (by rfl) ⟨264008, by rfl⟩ : syracuseStep 352011 = 528017) B528017
theorem B352023 : Blo 350755 352023 := bstep (se 1 (by rfl) ⟨264017, by rfl⟩ : syracuseStep 352023 = 528035) B528035
theorem B352043 : Blo 350755 352043 := bstep (se 1 (by rfl) ⟨264032, by rfl⟩ : syracuseStep 352043 = 528065) B528065
theorem B352055 : Blo 350755 352055 := bstep (se 1 (by rfl) ⟨264041, by rfl⟩ : syracuseStep 352055 = 528083) B528083
theorem B352075 : Blo 350755 352075 := bstep (se 1 (by rfl) ⟨264056, by rfl⟩ : syracuseStep 352075 = 528113) B528113
theorem B712535 : Blo 350755 712535 := bstep (se 1 (by rfl) ⟨534401, by rfl⟩ : syracuseStep 712535 = 1068803) B1068803
theorem B352087 : Blo 350755 352087 := bstep (se 1 (by rfl) ⟨264065, by rfl⟩ : syracuseStep 352087 = 528131) B528131
theorem B352107 : Blo 350755 352107 := bstep (se 1 (by rfl) ⟨264080, by rfl⟩ : syracuseStep 352107 = 528161) B528161
theorem B352119 : Blo 350755 352119 := bstep (se 1 (by rfl) ⟨264089, by rfl⟩ : syracuseStep 352119 = 528179) B528179
theorem B352139 : Blo 350755 352139 := bstep (se 1 (by rfl) ⟨264104, by rfl⟩ : syracuseStep 352139 = 528209) B528209
theorem B352151 : Blo 350755 352151 := bstep (se 1 (by rfl) ⟨264113, by rfl⟩ : syracuseStep 352151 = 528227) B528227
theorem B352171 : Blo 350755 352171 := bstep (se 1 (by rfl) ⟨264128, by rfl⟩ : syracuseStep 352171 = 528257) B528257
theorem B352183 : Blo 350755 352183 := bstep (se 1 (by rfl) ⟨264137, by rfl⟩ : syracuseStep 352183 = 528275) B528275
theorem B352203 : Blo 350755 352203 := bstep (se 1 (by rfl) ⟨264152, by rfl⟩ : syracuseStep 352203 = 528305) B528305
theorem B352215 : Blo 350755 352215 := bstep (se 1 (by rfl) ⟨264161, by rfl⟩ : syracuseStep 352215 = 528323) B528323
theorem B352235 : Blo 350755 352235 := bstep (se 1 (by rfl) ⟨264176, by rfl⟩ : syracuseStep 352235 = 528353) B528353
theorem B352247 : Blo 350755 352247 := bstep (se 1 (by rfl) ⟨264185, by rfl⟩ : syracuseStep 352247 = 528371) B528371
theorem B352267 : Blo 350755 352267 := bstep (se 1 (by rfl) ⟨264200, by rfl⟩ : syracuseStep 352267 = 528401) B528401
theorem B352279 : Blo 350755 352279 := bstep (se 1 (by rfl) ⟨264209, by rfl⟩ : syracuseStep 352279 = 528419) B528419
theorem B352299 : Blo 350755 352299 := bstep (se 1 (by rfl) ⟨264224, by rfl⟩ : syracuseStep 352299 = 528449) B528449
theorem B352311 : Blo 350755 352311 := bstep (se 1 (by rfl) ⟨264233, by rfl⟩ : syracuseStep 352311 = 528467) B528467
theorem B352331 : Blo 350755 352331 := bstep (se 1 (by rfl) ⟨264248, by rfl⟩ : syracuseStep 352331 = 528497) B528497
theorem B352343 : Blo 350755 352343 := bstep (se 1 (by rfl) ⟨264257, by rfl⟩ : syracuseStep 352343 = 528515) B528515
theorem B352363 : Blo 350755 352363 := bstep (se 1 (by rfl) ⟨264272, by rfl⟩ : syracuseStep 352363 = 528545) B528545
theorem B352375 : Blo 350755 352375 := bstep (se 1 (by rfl) ⟨264281, by rfl⟩ : syracuseStep 352375 = 528563) B528563
theorem B647297 : Blo 350755 647297 := bstep (se 2 (by rfl) ⟨242736, by rfl⟩ : syracuseStep 647297 = 485473) B485473
theorem B352395 : Blo 350755 352395 := bstep (se 1 (by rfl) ⟨264296, by rfl⟩ : syracuseStep 352395 = 528593) B528593
theorem B352407 : Blo 350755 352407 := bstep (se 1 (by rfl) ⟨264305, by rfl⟩ : syracuseStep 352407 = 528611) B528611
theorem B352427 : Blo 350755 352427 := bstep (se 1 (by rfl) ⟨264320, by rfl⟩ : syracuseStep 352427 = 528641) B528641
theorem B352439 : Blo 350755 352439 := bstep (se 1 (by rfl) ⟨264329, by rfl⟩ : syracuseStep 352439 = 528659) B528659
theorem B352459 : Blo 350755 352459 := bstep (se 1 (by rfl) ⟨264344, by rfl⟩ : syracuseStep 352459 = 528689) B528689
theorem B352471 : Blo 350755 352471 := bstep (se 1 (by rfl) ⟨264353, by rfl⟩ : syracuseStep 352471 = 528707) B528707
theorem B352491 : Blo 350755 352491 := bstep (se 1 (by rfl) ⟨264368, by rfl⟩ : syracuseStep 352491 = 528737) B528737
theorem B352503 : Blo 350755 352503 := bstep (se 1 (by rfl) ⟨264377, by rfl⟩ : syracuseStep 352503 = 528755) B528755
theorem B352523 : Blo 350755 352523 := bstep (se 1 (by rfl) ⟨264392, by rfl⟩ : syracuseStep 352523 = 528785) B528785
theorem B352535 : Blo 350755 352535 := bstep (se 1 (by rfl) ⟨264401, by rfl⟩ : syracuseStep 352535 = 528803) B528803
theorem B352555 : Blo 350755 352555 := bstep (se 1 (by rfl) ⟨264416, by rfl⟩ : syracuseStep 352555 = 528833) B528833
theorem B1007923 : Blo 350755 1007923 := bstep (se 1 (by rfl) ⟨755942, by rfl⟩ : syracuseStep 1007923 = 1511885) B1511885
theorem B352567 : Blo 350755 352567 := bstep (se 1 (by rfl) ⟨264425, by rfl⟩ : syracuseStep 352567 = 528851) B528851
theorem B352587 : Blo 350755 352587 := bstep (se 1 (by rfl) ⟨264440, by rfl⟩ : syracuseStep 352587 = 528881) B528881
theorem B352599 : Blo 350755 352599 := bstep (se 1 (by rfl) ⟨264449, by rfl⟩ : syracuseStep 352599 = 528899) B528899
theorem B352619 : Blo 350755 352619 := bstep (se 1 (by rfl) ⟨264464, by rfl⟩ : syracuseStep 352619 = 528929) B528929
theorem B352631 : Blo 350755 352631 := bstep (se 1 (by rfl) ⟨264473, by rfl⟩ : syracuseStep 352631 = 528947) B528947
theorem B352651 : Blo 350755 352651 := bstep (se 1 (by rfl) ⟨264488, by rfl⟩ : syracuseStep 352651 = 528977) B528977
theorem B352663 : Blo 350755 352663 := bstep (se 1 (by rfl) ⟨264497, by rfl⟩ : syracuseStep 352663 = 528995) B528995
theorem B352683 : Blo 350755 352683 := bstep (se 1 (by rfl) ⟨264512, by rfl⟩ : syracuseStep 352683 = 529025) B529025
theorem B352695 : Blo 350755 352695 := bstep (se 1 (by rfl) ⟨264521, by rfl⟩ : syracuseStep 352695 = 529043) B529043
theorem B352715 : Blo 350755 352715 := bstep (se 1 (by rfl) ⟨264536, by rfl⟩ : syracuseStep 352715 = 529073) B529073
theorem B352727 : Blo 350755 352727 := bstep (se 1 (by rfl) ⟨264545, by rfl⟩ : syracuseStep 352727 = 529091) B529091
theorem B352747 : Blo 350755 352747 := bstep (se 1 (by rfl) ⟨264560, by rfl⟩ : syracuseStep 352747 = 529121) B529121
theorem B352759 : Blo 350755 352759 := bstep (se 1 (by rfl) ⟨264569, by rfl⟩ : syracuseStep 352759 = 529139) B529139
theorem B352779 : Blo 350755 352779 := bstep (se 1 (by rfl) ⟨264584, by rfl⟩ : syracuseStep 352779 = 529169) B529169
theorem B352791 : Blo 350755 352791 := bstep (se 1 (by rfl) ⟨264593, by rfl⟩ : syracuseStep 352791 = 529187) B529187
theorem B352811 : Blo 350755 352811 := bstep (se 1 (by rfl) ⟨264608, by rfl⟩ : syracuseStep 352811 = 529217) B529217
theorem B352823 : Blo 350755 352823 := bstep (se 1 (by rfl) ⟨264617, by rfl⟩ : syracuseStep 352823 = 529235) B529235
theorem B352843 : Blo 350755 352843 := bstep (se 1 (by rfl) ⟨264632, by rfl⟩ : syracuseStep 352843 = 529265) B529265
theorem B1794635 : Blo 350755 1794635 := bstep (se 1 (by rfl) ⟨1345976, by rfl⟩ : syracuseStep 1794635 = 2691953) B2691953
theorem B352855 : Blo 350755 352855 := bstep (se 1 (by rfl) ⟨264641, by rfl⟩ : syracuseStep 352855 = 529283) B529283
theorem B352875 : Blo 350755 352875 := bstep (se 1 (by rfl) ⟨264656, by rfl⟩ : syracuseStep 352875 = 529313) B529313
theorem B352887 : Blo 350755 352887 := bstep (se 1 (by rfl) ⟨264665, by rfl⟩ : syracuseStep 352887 = 529331) B529331
theorem B352907 : Blo 350755 352907 := bstep (se 1 (by rfl) ⟨264680, by rfl⟩ : syracuseStep 352907 = 529361) B529361
theorem B1335953 : Blo 350755 1335953 := bstep (se 2 (by rfl) ⟨500982, by rfl⟩ : syracuseStep 1335953 = 1001965) B1001965
theorem B352919 : Blo 350755 352919 := bstep (se 1 (by rfl) ⟨264689, by rfl⟩ : syracuseStep 352919 = 529379) B529379
theorem B352939 : Blo 350755 352939 := bstep (se 1 (by rfl) ⟨264704, by rfl⟩ : syracuseStep 352939 = 529409) B529409
theorem B352951 : Blo 350755 352951 := bstep (se 1 (by rfl) ⟨264713, by rfl⟩ : syracuseStep 352951 = 529427) B529427
theorem B352971 : Blo 350755 352971 := bstep (se 1 (by rfl) ⟨264728, by rfl⟩ : syracuseStep 352971 = 529457) B529457
theorem B352983 : Blo 350755 352983 := bstep (se 1 (by rfl) ⟨264737, by rfl⟩ : syracuseStep 352983 = 529475) B529475
theorem B353003 : Blo 350755 353003 := bstep (se 1 (by rfl) ⟨264752, by rfl⟩ : syracuseStep 353003 = 529505) B529505
theorem B353015 : Blo 350755 353015 := bstep (se 1 (by rfl) ⟨264761, by rfl⟩ : syracuseStep 353015 = 529523) B529523
theorem B353035 : Blo 350755 353035 := bstep (se 1 (by rfl) ⟨264776, by rfl⟩ : syracuseStep 353035 = 529553) B529553
theorem B353047 : Blo 350755 353047 := bstep (se 1 (by rfl) ⟨264785, by rfl⟩ : syracuseStep 353047 = 529571) B529571
theorem B353067 : Blo 350755 353067 := bstep (se 1 (by rfl) ⟨264800, by rfl⟩ : syracuseStep 353067 = 529601) B529601
theorem B1270579 : Blo 350755 1270579 := bstep (se 1 (by rfl) ⟨952934, by rfl⟩ : syracuseStep 1270579 = 1905869) B1905869
theorem B680755 : Blo 350755 680755 := bstep (se 1 (by rfl) ⟨510566, by rfl⟩ : syracuseStep 680755 = 1021133) B1021133
theorem B353079 : Blo 350755 353079 := bstep (se 1 (by rfl) ⟨264809, by rfl⟩ : syracuseStep 353079 = 529619) B529619
theorem B353099 : Blo 350755 353099 := bstep (se 1 (by rfl) ⟨264824, by rfl⟩ : syracuseStep 353099 = 529649) B529649
theorem B353111 : Blo 350755 353111 := bstep (se 1 (by rfl) ⟨264833, by rfl⟩ : syracuseStep 353111 = 529667) B529667
theorem B1631069 : Blo 350755 1631069 := bstep (se 3 (by rfl) ⟨305825, by rfl⟩ : syracuseStep 1631069 = 611651) B611651
theorem B353131 : Blo 350755 353131 := bstep (se 1 (by rfl) ⟨264848, by rfl⟩ : syracuseStep 353131 = 529697) B529697
theorem B353143 : Blo 350755 353143 := bstep (se 1 (by rfl) ⟨264857, by rfl⟩ : syracuseStep 353143 = 529715) B529715
theorem B353163 : Blo 350755 353163 := bstep (se 1 (by rfl) ⟨264872, by rfl⟩ : syracuseStep 353163 = 529745) B529745
theorem B353175 : Blo 350755 353175 := bstep (se 1 (by rfl) ⟨264881, by rfl⟩ : syracuseStep 353175 = 529763) B529763
theorem B353195 : Blo 350755 353195 := bstep (se 1 (by rfl) ⟨264896, by rfl⟩ : syracuseStep 353195 = 529793) B529793
theorem B353207 : Blo 350755 353207 := bstep (se 1 (by rfl) ⟨264905, by rfl⟩ : syracuseStep 353207 = 529811) B529811
theorem B353227 : Blo 350755 353227 := bstep (se 1 (by rfl) ⟨264920, by rfl⟩ : syracuseStep 353227 = 529841) B529841
theorem B353239 : Blo 350755 353239 := bstep (se 1 (by rfl) ⟨264929, by rfl⟩ : syracuseStep 353239 = 529859) B529859
theorem B353259 : Blo 350755 353259 := bstep (se 1 (by rfl) ⟨264944, by rfl⟩ : syracuseStep 353259 = 529889) B529889
theorem B353271 : Blo 350755 353271 := bstep (se 1 (by rfl) ⟨264953, by rfl⟩ : syracuseStep 353271 = 529907) B529907
theorem B353291 : Blo 350755 353291 := bstep (se 1 (by rfl) ⟨264968, by rfl⟩ : syracuseStep 353291 = 529937) B529937
theorem B353303 : Blo 350755 353303 := bstep (se 1 (by rfl) ⟨264977, by rfl⟩ : syracuseStep 353303 = 529955) B529955
theorem B353323 : Blo 350755 353323 := bstep (se 1 (by rfl) ⟨264992, by rfl⟩ : syracuseStep 353323 = 529985) B529985
theorem B353335 : Blo 350755 353335 := bstep (se 1 (by rfl) ⟨265001, by rfl⟩ : syracuseStep 353335 = 530003) B530003
theorem B353355 : Blo 350755 353355 := bstep (se 1 (by rfl) ⟨265016, by rfl⟩ : syracuseStep 353355 = 530033) B530033
theorem B353367 : Blo 350755 353367 := bstep (se 1 (by rfl) ⟨265025, by rfl⟩ : syracuseStep 353367 = 530051) B530051
theorem B1336409 : Blo 350755 1336409 := bstep (se 2 (by rfl) ⟨501153, by rfl⟩ : syracuseStep 1336409 = 1002307) B1002307
theorem B3204197 : Blo 350755 3204197 := bstep (se 4 (by rfl) ⟨300393, by rfl⟩ : syracuseStep 3204197 = 600787) B600787
theorem B353387 : Blo 350755 353387 := bstep (se 1 (by rfl) ⟨265040, by rfl⟩ : syracuseStep 353387 = 530081) B530081
theorem B353399 : Blo 350755 353399 := bstep (se 1 (by rfl) ⟨265049, by rfl⟩ : syracuseStep 353399 = 530099) B530099
theorem B353419 : Blo 350755 353419 := bstep (se 1 (by rfl) ⟨265064, by rfl⟩ : syracuseStep 353419 = 530129) B530129
theorem B353431 : Blo 350755 353431 := bstep (se 1 (by rfl) ⟨265073, by rfl⟩ : syracuseStep 353431 = 530147) B530147
theorem B353451 : Blo 350755 353451 := bstep (se 1 (by rfl) ⟨265088, by rfl⟩ : syracuseStep 353451 = 530177) B530177
theorem B353463 : Blo 350755 353463 := bstep (se 1 (by rfl) ⟨265097, by rfl⟩ : syracuseStep 353463 = 530195) B530195
theorem B353483 : Blo 350755 353483 := bstep (se 1 (by rfl) ⟨265112, by rfl⟩ : syracuseStep 353483 = 530225) B530225
theorem B353495 : Blo 350755 353495 := bstep (se 1 (by rfl) ⟨265121, by rfl⟩ : syracuseStep 353495 = 530243) B530243
theorem B353515 : Blo 350755 353515 := bstep (se 1 (by rfl) ⟨265136, by rfl⟩ : syracuseStep 353515 = 530273) B530273
theorem B353527 : Blo 350755 353527 := bstep (se 1 (by rfl) ⟨265145, by rfl⟩ : syracuseStep 353527 = 530291) B530291
theorem B1500419 : Blo 350755 1500419 := bstep (se 1 (by rfl) ⟨1125314, by rfl⟩ : syracuseStep 1500419 = 2250629) B2250629
theorem B353547 : Blo 350755 353547 := bstep (se 1 (by rfl) ⟨265160, by rfl⟩ : syracuseStep 353547 = 530321) B530321
theorem B353559 : Blo 350755 353559 := bstep (se 1 (by rfl) ⟨265169, by rfl⟩ : syracuseStep 353559 = 530339) B530339
theorem B353579 : Blo 350755 353579 := bstep (se 1 (by rfl) ⟨265184, by rfl⟩ : syracuseStep 353579 = 530369) B530369
theorem B1336621 : Blo 350755 1336621 := bstep (se 3 (by rfl) ⟨250616, by rfl⟩ : syracuseStep 1336621 = 501233) B501233
theorem B353591 : Blo 350755 353591 := bstep (se 1 (by rfl) ⟨265193, by rfl⟩ : syracuseStep 353591 = 530387) B530387
theorem B2876737 : Blo 350755 2876737 := bstep (se 2 (by rfl) ⟨1078776, by rfl⟩ : syracuseStep 2876737 = 2157553) B2157553
theorem B353611 : Blo 350755 353611 := bstep (se 1 (by rfl) ⟨265208, by rfl⟩ : syracuseStep 353611 = 530417) B530417
theorem B353623 : Blo 350755 353623 := bstep (se 1 (by rfl) ⟨265217, by rfl⟩ : syracuseStep 353623 = 530435) B530435
theorem B353643 : Blo 350755 353643 := bstep (se 1 (by rfl) ⟨265232, by rfl⟩ : syracuseStep 353643 = 530465) B530465
theorem B353655 : Blo 350755 353655 := bstep (se 1 (by rfl) ⟨265241, by rfl⟩ : syracuseStep 353655 = 530483) B530483
theorem B353675 : Blo 350755 353675 := bstep (se 1 (by rfl) ⟨265256, by rfl⟩ : syracuseStep 353675 = 530513) B530513
theorem B353687 : Blo 350755 353687 := bstep (se 1 (by rfl) ⟨265265, by rfl⟩ : syracuseStep 353687 = 530531) B530531
theorem B353707 : Blo 350755 353707 := bstep (se 1 (by rfl) ⟨265280, by rfl⟩ : syracuseStep 353707 = 530561) B530561
theorem B353719 : Blo 350755 353719 := bstep (se 1 (by rfl) ⟨265289, by rfl⟩ : syracuseStep 353719 = 530579) B530579
theorem B353739 : Blo 350755 353739 := bstep (se 1 (by rfl) ⟨265304, by rfl⟩ : syracuseStep 353739 = 530609) B530609
theorem B353751 : Blo 350755 353751 := bstep (se 1 (by rfl) ⟨265313, by rfl⟩ : syracuseStep 353751 = 530627) B530627
theorem B353771 : Blo 350755 353771 := bstep (se 1 (by rfl) ⟨265328, by rfl⟩ : syracuseStep 353771 = 530657) B530657
theorem B353783 : Blo 350755 353783 := bstep (se 1 (by rfl) ⟨265337, by rfl⟩ : syracuseStep 353783 = 530675) B530675
theorem B353803 : Blo 350755 353803 := bstep (se 1 (by rfl) ⟨265352, by rfl⟩ : syracuseStep 353803 = 530705) B530705
theorem B353815 : Blo 350755 353815 := bstep (se 1 (by rfl) ⟨265361, by rfl⟩ : syracuseStep 353815 = 530723) B530723
theorem B353835 : Blo 350755 353835 := bstep (se 1 (by rfl) ⟨265376, by rfl⟩ : syracuseStep 353835 = 530753) B530753
theorem B353847 : Blo 350755 353847 := bstep (se 1 (by rfl) ⟨265385, by rfl⟩ : syracuseStep 353847 = 530771) B530771
theorem B353867 : Blo 350755 353867 := bstep (se 1 (by rfl) ⟨265400, by rfl⟩ : syracuseStep 353867 = 530801) B530801
theorem B353879 : Blo 350755 353879 := bstep (se 1 (by rfl) ⟨265409, by rfl⟩ : syracuseStep 353879 = 530819) B530819
theorem B1500761 : Blo 350755 1500761 := bstep (se 2 (by rfl) ⟨562785, by rfl⟩ : syracuseStep 1500761 = 1125571) B1125571
theorem B1336925 : Blo 350755 1336925 := bstep (se 3 (by rfl) ⟨250673, by rfl⟩ : syracuseStep 1336925 = 501347) B501347
theorem B353899 : Blo 350755 353899 := bstep (se 1 (by rfl) ⟨265424, by rfl⟩ : syracuseStep 353899 = 530849) B530849
theorem B353911 : Blo 350755 353911 := bstep (se 1 (by rfl) ⟨265433, by rfl⟩ : syracuseStep 353911 = 530867) B530867
theorem B353931 : Blo 350755 353931 := bstep (se 1 (by rfl) ⟨265448, by rfl⟩ : syracuseStep 353931 = 530897) B530897
theorem B353943 : Blo 350755 353943 := bstep (se 1 (by rfl) ⟨265457, by rfl⟩ : syracuseStep 353943 = 530915) B530915
theorem B353963 : Blo 350755 353963 := bstep (se 1 (by rfl) ⟨265472, by rfl⟩ : syracuseStep 353963 = 530945) B530945
theorem B353975 : Blo 350755 353975 := bstep (se 1 (by rfl) ⟨265481, by rfl⟩ : syracuseStep 353975 = 530963) B530963
theorem B845515 : Blo 350755 845515 := bstep (se 1 (by rfl) ⟨634136, by rfl⟩ : syracuseStep 845515 = 1268273) B1268273
theorem B353995 : Blo 350755 353995 := bstep (se 1 (by rfl) ⟨265496, by rfl⟩ : syracuseStep 353995 = 530993) B530993
theorem B354007 : Blo 350755 354007 := bstep (se 1 (by rfl) ⟨265505, by rfl⟩ : syracuseStep 354007 = 531011) B531011
theorem B354027 : Blo 350755 354027 := bstep (se 1 (by rfl) ⟨265520, by rfl⟩ : syracuseStep 354027 = 531041) B531041
theorem B354039 : Blo 350755 354039 := bstep (se 1 (by rfl) ⟨265529, by rfl⟩ : syracuseStep 354039 = 531059) B531059
theorem B354059 : Blo 350755 354059 := bstep (se 1 (by rfl) ⟨265544, by rfl⟩ : syracuseStep 354059 = 531089) B531089
theorem B354071 : Blo 350755 354071 := bstep (se 1 (by rfl) ⟨265553, by rfl⟩ : syracuseStep 354071 = 531107) B531107
theorem B354091 : Blo 350755 354091 := bstep (se 1 (by rfl) ⟨265568, by rfl⟩ : syracuseStep 354091 = 531137) B531137
theorem B354103 : Blo 350755 354103 := bstep (se 1 (by rfl) ⟨265577, by rfl⟩ : syracuseStep 354103 = 531155) B531155
theorem B354123 : Blo 350755 354123 := bstep (se 1 (by rfl) ⟨265592, by rfl⟩ : syracuseStep 354123 = 531185) B531185
theorem B354135 : Blo 350755 354135 := bstep (se 1 (by rfl) ⟨265601, by rfl⟩ : syracuseStep 354135 = 531203) B531203
theorem B354155 : Blo 350755 354155 := bstep (se 1 (by rfl) ⟨265616, by rfl⟩ : syracuseStep 354155 = 531233) B531233
theorem B354167 : Blo 350755 354167 := bstep (se 1 (by rfl) ⟨265625, by rfl⟩ : syracuseStep 354167 = 531251) B531251
theorem B354187 : Blo 350755 354187 := bstep (se 1 (by rfl) ⟨265640, by rfl⟩ : syracuseStep 354187 = 531281) B531281
theorem B354199 : Blo 350755 354199 := bstep (se 1 (by rfl) ⟨265649, by rfl⟩ : syracuseStep 354199 = 531299) B531299
theorem B354219 : Blo 350755 354219 := bstep (se 1 (by rfl) ⟨265664, by rfl⟩ : syracuseStep 354219 = 531329) B531329
theorem B845747 : Blo 350755 845747 := bstep (se 1 (by rfl) ⟨634310, by rfl⟩ : syracuseStep 845747 = 1268621) B1268621
theorem B354231 : Blo 350755 354231 := bstep (se 1 (by rfl) ⟨265673, by rfl⟩ : syracuseStep 354231 = 531347) B531347
theorem B354251 : Blo 350755 354251 := bstep (se 1 (by rfl) ⟨265688, by rfl⟩ : syracuseStep 354251 = 531377) B531377
theorem B354263 : Blo 350755 354263 := bstep (se 1 (by rfl) ⟨265697, by rfl⟩ : syracuseStep 354263 = 531395) B531395
theorem B354283 : Blo 350755 354283 := bstep (se 1 (by rfl) ⟨265712, by rfl⟩ : syracuseStep 354283 = 531425) B531425
theorem B354295 : Blo 350755 354295 := bstep (se 1 (by rfl) ⟨265721, by rfl⟩ : syracuseStep 354295 = 531443) B531443
theorem B354315 : Blo 350755 354315 := bstep (se 1 (by rfl) ⟨265736, by rfl⟩ : syracuseStep 354315 = 531473) B531473
theorem B354327 : Blo 350755 354327 := bstep (se 1 (by rfl) ⟨265745, by rfl⟩ : syracuseStep 354327 = 531491) B531491
theorem B354347 : Blo 350755 354347 := bstep (se 1 (by rfl) ⟨265760, by rfl⟩ : syracuseStep 354347 = 531521) B531521
theorem B354359 : Blo 350755 354359 := bstep (se 1 (by rfl) ⟨265769, by rfl⟩ : syracuseStep 354359 = 531539) B531539
theorem B354379 : Blo 350755 354379 := bstep (se 1 (by rfl) ⟨265784, by rfl⟩ : syracuseStep 354379 = 531569) B531569
theorem B354391 : Blo 350755 354391 := bstep (se 1 (by rfl) ⟨265793, by rfl⟩ : syracuseStep 354391 = 531587) B531587
theorem B354411 : Blo 350755 354411 := bstep (se 1 (by rfl) ⟨265808, by rfl⟩ : syracuseStep 354411 = 531617) B531617
theorem B354423 : Blo 350755 354423 := bstep (se 1 (by rfl) ⟨265817, by rfl⟩ : syracuseStep 354423 = 531635) B531635
theorem B354443 : Blo 350755 354443 := bstep (se 1 (by rfl) ⟨265832, by rfl⟩ : syracuseStep 354443 = 531665) B531665
theorem B354455 : Blo 350755 354455 := bstep (se 1 (by rfl) ⟨265841, by rfl⟩ : syracuseStep 354455 = 531683) B531683
theorem B354475 : Blo 350755 354475 := bstep (se 1 (by rfl) ⟨265856, by rfl⟩ : syracuseStep 354475 = 531713) B531713
theorem B813235 : Blo 350755 813235 := bstep (se 1 (by rfl) ⟨609926, by rfl⟩ : syracuseStep 813235 = 1219853) B1219853
theorem B354487 : Blo 350755 354487 := bstep (se 1 (by rfl) ⟨265865, by rfl⟩ : syracuseStep 354487 = 531731) B531731
theorem B354507 : Blo 350755 354507 := bstep (se 1 (by rfl) ⟨265880, by rfl⟩ : syracuseStep 354507 = 531761) B531761
theorem B354519 : Blo 350755 354519 := bstep (se 1 (by rfl) ⟨265889, by rfl⟩ : syracuseStep 354519 = 531779) B531779
theorem B354539 : Blo 350755 354539 := bstep (se 1 (by rfl) ⟨265904, by rfl⟩ : syracuseStep 354539 = 531809) B531809
theorem B354551 : Blo 350755 354551 := bstep (se 1 (by rfl) ⟨265913, by rfl⟩ : syracuseStep 354551 = 531827) B531827
theorem B354571 : Blo 350755 354571 := bstep (se 1 (by rfl) ⟨265928, by rfl⟩ : syracuseStep 354571 = 531857) B531857
theorem B354583 : Blo 350755 354583 := bstep (se 1 (by rfl) ⟨265937, by rfl⟩ : syracuseStep 354583 = 531875) B531875
theorem B354603 : Blo 350755 354603 := bstep (se 1 (by rfl) ⟨265952, by rfl⟩ : syracuseStep 354603 = 531905) B531905
theorem B354615 : Blo 350755 354615 := bstep (se 1 (by rfl) ⟨265961, by rfl⟩ : syracuseStep 354615 = 531923) B531923
theorem B354635 : Blo 350755 354635 := bstep (se 1 (by rfl) ⟨265976, by rfl⟩ : syracuseStep 354635 = 531953) B531953
theorem B354647 : Blo 350755 354647 := bstep (se 1 (by rfl) ⟨265985, by rfl⟩ : syracuseStep 354647 = 531971) B531971
theorem B354667 : Blo 350755 354667 := bstep (se 1 (by rfl) ⟨266000, by rfl⟩ : syracuseStep 354667 = 532001) B532001
theorem B354679 : Blo 350755 354679 := bstep (se 1 (by rfl) ⟨266009, by rfl⟩ : syracuseStep 354679 = 532019) B532019
theorem B354699 : Blo 350755 354699 := bstep (se 1 (by rfl) ⟨266024, by rfl⟩ : syracuseStep 354699 = 532049) B532049
theorem B354711 : Blo 350755 354711 := bstep (se 1 (by rfl) ⟨266033, by rfl⟩ : syracuseStep 354711 = 532067) B532067
theorem B354731 : Blo 350755 354731 := bstep (se 1 (by rfl) ⟨266048, by rfl⟩ : syracuseStep 354731 = 532097) B532097
theorem B354743 : Blo 350755 354743 := bstep (se 1 (by rfl) ⟨266057, by rfl⟩ : syracuseStep 354743 = 532115) B532115
theorem B715351 : Blo 350755 715351 := bstep (se 1 (by rfl) ⟨536513, by rfl⟩ : syracuseStep 715351 = 1073027) B1073027
theorem B715649 : Blo 350755 715649 := bstep (se 2 (by rfl) ⟨268368, by rfl⟩ : syracuseStep 715649 = 536737) B536737
theorem B1502401 : Blo 350755 1502401 := bstep (se 2 (by rfl) ⟨563400, by rfl⟩ : syracuseStep 1502401 = 1126801) B1126801
theorem B1207703 : Blo 350755 1207703 := bstep (se 1 (by rfl) ⟨905777, by rfl⟩ : syracuseStep 1207703 = 1811555) B1811555
theorem B421643 : Blo 350755 421643 := bstep (se 1 (by rfl) ⟨316232, by rfl⟩ : syracuseStep 421643 = 632465) B632465
theorem B3010405 : Blo 350755 3010405 := bstep (se 4 (by rfl) ⟨282225, by rfl⟩ : syracuseStep 3010405 = 564451) B564451
theorem B1339523 : Blo 350755 1339523 := bstep (se 1 (by rfl) ⟨1004642, by rfl⟩ : syracuseStep 1339523 = 2009285) B2009285
theorem B1339537 : Blo 350755 1339537 := bstep (se 2 (by rfl) ⟨502326, by rfl⟩ : syracuseStep 1339537 = 1004653) B1004653
theorem B1339841 : Blo 350755 1339841 := bstep (se 2 (by rfl) ⟨502440, by rfl⟩ : syracuseStep 1339841 = 1004881) B1004881
theorem B717427 : Blo 350755 717427 := bstep (se 1 (by rfl) ⟨538070, by rfl⟩ : syracuseStep 717427 = 1076141) B1076141
theorem B3011363 : Blo 350755 3011363 := bstep (se 1 (by rfl) ⟨2258522, by rfl⟩ : syracuseStep 3011363 = 4517045) B4517045
theorem B750475 : Blo 350755 750475 := bstep (se 1 (by rfl) ⟨562856, by rfl⟩ : syracuseStep 750475 = 1125713) B1125713
theorem B750551 : Blo 350755 750551 := bstep (se 1 (by rfl) ⟨562913, by rfl⟩ : syracuseStep 750551 = 1125827) B1125827
theorem B1340509 : Blo 350755 1340509 := bstep (se 3 (by rfl) ⟨251345, by rfl⟩ : syracuseStep 1340509 = 502691) B502691
theorem B2946179 : Blo 350755 2946179 := bstep (se 1 (by rfl) ⟨2209634, by rfl⟩ : syracuseStep 2946179 = 4419269) B4419269
theorem B2684177 : Blo 350755 2684177 := bstep (se 2 (by rfl) ⟨1006566, by rfl⟩ : syracuseStep 2684177 = 2013133) B2013133
theorem B1209821 : Blo 350755 1209821 := bstep (se 3 (by rfl) ⟨226841, by rfl⟩ : syracuseStep 1209821 = 453683) B453683
theorem B3601955 : Blo 350755 3601955 := bstep (se 1 (by rfl) ⟨2701466, by rfl⟩ : syracuseStep 3601955 = 5402933) B5402933
theorem B1275841 : Blo 350755 1275841 := bstep (se 2 (by rfl) ⟨478440, by rfl⟩ : syracuseStep 1275841 = 956881) B956881
theorem B1800323 : Blo 350755 1800323 := bstep (se 1 (by rfl) ⟨1350242, by rfl⟩ : syracuseStep 1800323 = 2700485) B2700485
theorem B1374353 : Blo 350755 1374353 := bstep (se 2 (by rfl) ⟨515382, by rfl⟩ : syracuseStep 1374353 = 1030765) B1030765
theorem B1341785 : Blo 350755 1341785 := bstep (se 2 (by rfl) ⟨503169, by rfl⟩ : syracuseStep 1341785 = 1006339) B1006339
theorem B8550805 : Blo 350755 8550805 := bstep (se 6 (by rfl) ⟨200409, by rfl⟩ : syracuseStep 8550805 = 400819) B400819
theorem B2718157 : Blo 350755 2718157 := bstep (se 3 (by rfl) ⟨509654, by rfl⟩ : syracuseStep 2718157 = 1019309) B1019309
theorem B457367 : Blo 350755 457367 := bstep (se 1 (by rfl) ⟨343025, by rfl⟩ : syracuseStep 457367 = 686051) B686051
theorem B752321 : Blo 350755 752321 := bstep (se 2 (by rfl) ⟨282120, by rfl⟩ : syracuseStep 752321 = 564241) B564241
theorem B949313 : Blo 350755 949313 := bstep (se 2 (by rfl) ⟨355992, by rfl⟩ : syracuseStep 949313 = 711985) B711985
theorem B2260061 : Blo 350755 2260061 := bstep (se 3 (by rfl) ⟨423761, by rfl⟩ : syracuseStep 2260061 = 847523) B847523
theorem B949853 : Blo 350755 949853 := bstep (se 3 (by rfl) ⟨178097, by rfl⟩ : syracuseStep 949853 = 356195) B356195
theorem B2293379 : Blo 350755 2293379 := bstep (se 1 (by rfl) ⟨1720034, by rfl⟩ : syracuseStep 2293379 = 3440069) B3440069
theorem B1998553 : Blo 350755 1998553 := bstep (se 2 (by rfl) ⟨749457, by rfl⟩ : syracuseStep 1998553 = 1498915) B1498915
theorem B1343411 : Blo 350755 1343411 := bstep (se 1 (by rfl) ⟨1007558, by rfl⟩ : syracuseStep 1343411 = 2015117) B2015117
theorem B1343425 : Blo 350755 1343425 := bstep (se 2 (by rfl) ⟨503784, by rfl⟩ : syracuseStep 1343425 = 1007569) B1007569
theorem B851905 : Blo 350755 851905 := bstep (se 2 (by rfl) ⟨319464, by rfl⟩ : syracuseStep 851905 = 638929) B638929
theorem B1343897 : Blo 350755 1343897 := bstep (se 2 (by rfl) ⟨503961, by rfl⟩ : syracuseStep 1343897 = 1007923) B1007923
theorem B754105 : Blo 350755 754105 := bstep (se 2 (by rfl) ⟨282789, by rfl⟩ : syracuseStep 754105 = 565579) B565579
theorem B1147321 : Blo 350755 1147321 := bstep (se 2 (by rfl) ⟨430245, by rfl⟩ : syracuseStep 1147321 = 860491) B860491
theorem B754447 : Blo 350755 754447 := bstep (se 1 (by rfl) ⟨565835, by rfl⟩ : syracuseStep 754447 = 1131671) B1131671
theorem B1114913 : Blo 350755 1114913 := bstep (se 2 (by rfl) ⟨418092, by rfl⟩ : syracuseStep 1114913 = 836185) B836185
theorem B1639283 : Blo 350755 1639283 := bstep (se 1 (by rfl) ⟨1229462, by rfl⟩ : syracuseStep 1639283 = 2458925) B2458925
theorem B3245143 : Blo 350755 3245143 := bstep (se 1 (by rfl) ⟨2433857, by rfl⟩ : syracuseStep 3245143 = 4867715) B4867715
theorem B1901825 : Blo 350755 1901825 := bstep (se 2 (by rfl) ⟨713184, by rfl⟩ : syracuseStep 1901825 = 1426369) B1426369
theorem B1344883 : Blo 350755 1344883 := bstep (se 1 (by rfl) ⟨1008662, by rfl⟩ : syracuseStep 1344883 = 2017325) B2017325
theorem B3606059 : Blo 350755 3606059 := bstep (se 1 (by rfl) ⟨2704544, by rfl⟩ : syracuseStep 3606059 = 5409089) B5409089
theorem B755335 : Blo 350755 755335 := bstep (se 1 (by rfl) ⟨566501, by rfl⟩ : syracuseStep 755335 = 1133003) B1133003
theorem B3835649 : Blo 350755 3835649 := bstep (se 2 (by rfl) ⟨1438368, by rfl⟩ : syracuseStep 3835649 = 2876737) B2876737
theorem B395023 : Blo 350755 395023 := bstep (se 1 (by rfl) ⟨296267, by rfl⟩ : syracuseStep 395023 = 592535) B592535
theorem B526139 : Blo 350755 526139 := bstep (se 1 (by rfl) ⟨394604, by rfl⟩ : syracuseStep 526139 = 789209) B789209
theorem B526199 : Blo 350755 526199 := bstep (se 1 (by rfl) ⟨394649, by rfl⟩ : syracuseStep 526199 = 789299) B789299
theorem B526223 : Blo 350755 526223 := bstep (se 1 (by rfl) ⟨394667, by rfl⟩ : syracuseStep 526223 = 789335) B789335
theorem B526265 : Blo 350755 526265 := bstep (se 2 (by rfl) ⟨197349, by rfl⟩ : syracuseStep 526265 = 394699) B394699
theorem B526343 : Blo 350755 526343 := bstep (se 1 (by rfl) ⟨394757, by rfl⟩ : syracuseStep 526343 = 789515) B789515
theorem B526379 : Blo 350755 526379 := bstep (se 1 (by rfl) ⟨394784, by rfl⟩ : syracuseStep 526379 = 789569) B789569
theorem B526409 : Blo 350755 526409 := bstep (se 2 (by rfl) ⟨197403, by rfl⟩ : syracuseStep 526409 = 394807) B394807
theorem B755831 : Blo 350755 755831 := bstep (se 1 (by rfl) ⟨566873, by rfl⟩ : syracuseStep 755831 = 1133747) B1133747
theorem B526523 : Blo 350755 526523 := bstep (se 1 (by rfl) ⟨394892, by rfl⟩ : syracuseStep 526523 = 789785) B789785
theorem B526583 : Blo 350755 526583 := bstep (se 1 (by rfl) ⟨394937, by rfl⟩ : syracuseStep 526583 = 789875) B789875
theorem B395527 : Blo 350755 395527 := bstep (se 1 (by rfl) ⟨296645, by rfl⟩ : syracuseStep 395527 = 593291) B593291
theorem B526607 : Blo 350755 526607 := bstep (se 1 (by rfl) ⟨394955, by rfl⟩ : syracuseStep 526607 = 789911) B789911
theorem B526649 : Blo 350755 526649 := bstep (se 2 (by rfl) ⟨197493, by rfl⟩ : syracuseStep 526649 = 394987) B394987
theorem B4032827 : Blo 350755 4032827 := bstep (se 1 (by rfl) ⟨3024620, by rfl⟩ : syracuseStep 4032827 = 6049241) B6049241
theorem B526727 : Blo 350755 526727 := bstep (se 1 (by rfl) ⟨395045, by rfl⟩ : syracuseStep 526727 = 790091) B790091
theorem B2001287 : Blo 350755 2001287 := bstep (se 1 (by rfl) ⟨1500965, by rfl⟩ : syracuseStep 2001287 = 3001931) B3001931
theorem B526763 : Blo 350755 526763 := bstep (se 1 (by rfl) ⟨395072, by rfl⟩ : syracuseStep 526763 = 790145) B790145
theorem B395707 : Blo 350755 395707 := bstep (se 1 (by rfl) ⟨296780, by rfl⟩ : syracuseStep 395707 = 593561) B593561
theorem B526793 : Blo 350755 526793 := bstep (se 2 (by rfl) ⟨197547, by rfl⟩ : syracuseStep 526793 = 395095) B395095
theorem B592427 : Blo 350755 592427 := bstep (se 1 (by rfl) ⟨444320, by rfl⟩ : syracuseStep 592427 = 888641) B888641
theorem B526907 : Blo 350755 526907 := bstep (se 1 (by rfl) ⟨395180, by rfl⟩ : syracuseStep 526907 = 790361) B790361
theorem B2001469 : Blo 350755 2001469 := bstep (se 3 (by rfl) ⟨375275, by rfl⟩ : syracuseStep 2001469 = 750551) B750551
theorem B526967 : Blo 350755 526967 := bstep (se 1 (by rfl) ⟨395225, by rfl⟩ : syracuseStep 526967 = 790451) B790451
theorem B526991 : Blo 350755 526991 := bstep (se 1 (by rfl) ⟨395243, by rfl⟩ : syracuseStep 526991 = 790487) B790487
theorem B527033 : Blo 350755 527033 := bstep (se 2 (by rfl) ⟨197637, by rfl⟩ : syracuseStep 527033 = 395275) B395275
theorem B527111 : Blo 350755 527111 := bstep (se 1 (by rfl) ⟨395333, by rfl⟩ : syracuseStep 527111 = 790667) B790667
theorem B789263 : Blo 350755 789263 := bstep (se 1 (by rfl) ⟨591947, by rfl⟩ : syracuseStep 789263 = 1183895) B1183895
theorem B789281 : Blo 350755 789281 := bstep (se 2 (by rfl) ⟨295980, by rfl⟩ : syracuseStep 789281 = 591961) B591961
theorem B527147 : Blo 350755 527147 := bstep (se 1 (by rfl) ⟨395360, by rfl⟩ : syracuseStep 527147 = 790721) B790721
theorem B527177 : Blo 350755 527177 := bstep (se 2 (by rfl) ⟨197691, by rfl⟩ : syracuseStep 527177 = 395383) B395383
theorem B396175 : Blo 350755 396175 := bstep (se 1 (by rfl) ⟨297131, by rfl⟩ : syracuseStep 396175 = 594263) B594263
theorem B1084313 : Blo 350755 1084313 := bstep (se 2 (by rfl) ⟨406617, by rfl⟩ : syracuseStep 1084313 = 813235) B813235
theorem B592825 : Blo 350755 592825 := bstep (se 2 (by rfl) ⟨222309, by rfl⟩ : syracuseStep 592825 = 444619) B444619
theorem B527291 : Blo 350755 527291 := bstep (se 1 (by rfl) ⟨395468, by rfl⟩ : syracuseStep 527291 = 790937) B790937
theorem B527351 : Blo 350755 527351 := bstep (se 1 (by rfl) ⟨395513, by rfl⟩ : syracuseStep 527351 = 791027) B791027
theorem B527375 : Blo 350755 527375 := bstep (se 1 (by rfl) ⟨395531, by rfl⟩ : syracuseStep 527375 = 791063) B791063
theorem B527417 : Blo 350755 527417 := bstep (se 2 (by rfl) ⟨197781, by rfl⟩ : syracuseStep 527417 = 395563) B395563
theorem B789623 : Blo 350755 789623 := bstep (se 1 (by rfl) ⟨592217, by rfl⟩ : syracuseStep 789623 = 1184435) B1184435
theorem B527495 : Blo 350755 527495 := bstep (se 1 (by rfl) ⟨395621, by rfl⟩ : syracuseStep 527495 = 791243) B791243
theorem B527531 : Blo 350755 527531 := bstep (se 1 (by rfl) ⟨395648, by rfl⟩ : syracuseStep 527531 = 791297) B791297
theorem B887993 : Blo 350755 887993 := bstep (se 2 (by rfl) ⟨332997, by rfl⟩ : syracuseStep 887993 = 665995) B665995
theorem B527561 : Blo 350755 527561 := bstep (se 2 (by rfl) ⟨197835, by rfl⟩ : syracuseStep 527561 = 395671) B395671
theorem B789803 : Blo 350755 789803 := bstep (se 1 (by rfl) ⟨592352, by rfl⟩ : syracuseStep 789803 = 1184705) B1184705
theorem B527675 : Blo 350755 527675 := bstep (se 1 (by rfl) ⟨395756, by rfl⟩ : syracuseStep 527675 = 791513) B791513
theorem B3804509 : Blo 350755 3804509 := bstep (se 3 (by rfl) ⟨713345, by rfl⟩ : syracuseStep 3804509 = 1426691) B1426691
theorem B527735 : Blo 350755 527735 := bstep (se 1 (by rfl) ⟨395801, by rfl⟩ : syracuseStep 527735 = 791603) B791603
theorem B396679 : Blo 350755 396679 := bstep (se 1 (by rfl) ⟨297509, by rfl⟩ : syracuseStep 396679 = 595019) B595019
theorem B527759 : Blo 350755 527759 := bstep (se 1 (by rfl) ⟨395819, by rfl⟩ : syracuseStep 527759 = 791639) B791639
theorem B527801 : Blo 350755 527801 := bstep (se 2 (by rfl) ⟨197925, by rfl⟩ : syracuseStep 527801 = 395851) B395851
theorem B953801 : Blo 350755 953801 := bstep (se 2 (by rfl) ⟨357675, by rfl⟩ : syracuseStep 953801 = 715351) B715351
theorem B527879 : Blo 350755 527879 := bstep (se 1 (by rfl) ⟨395909, by rfl⟩ : syracuseStep 527879 = 791819) B791819
theorem B527915 : Blo 350755 527915 := bstep (se 1 (by rfl) ⟨395936, by rfl⟩ : syracuseStep 527915 = 791873) B791873
theorem B396859 : Blo 350755 396859 := bstep (se 1 (by rfl) ⟨297644, by rfl⟩ : syracuseStep 396859 = 595289) B595289
theorem B527945 : Blo 350755 527945 := bstep (se 2 (by rfl) ⟨197979, by rfl⟩ : syracuseStep 527945 = 395959) B395959
theorem B1085015 : Blo 350755 1085015 := bstep (se 1 (by rfl) ⟨813761, by rfl⟩ : syracuseStep 1085015 = 1627523) B1627523
theorem B3903095 : Blo 350755 3903095 := bstep (se 1 (by rfl) ⟨2927321, by rfl⟩ : syracuseStep 3903095 = 5854643) B5854643
theorem B593527 : Blo 350755 593527 := bstep (se 1 (by rfl) ⟨445145, by rfl⟩ : syracuseStep 593527 = 890291) B890291
theorem B790163 : Blo 350755 790163 := bstep (se 1 (by rfl) ⟨592622, by rfl⟩ : syracuseStep 790163 = 1185245) B1185245
theorem B528059 : Blo 350755 528059 := bstep (se 1 (by rfl) ⟨396044, by rfl⟩ : syracuseStep 528059 = 792089) B792089
theorem B790217 : Blo 350755 790217 := bstep (se 2 (by rfl) ⟨296331, by rfl⟩ : syracuseStep 790217 = 592663) B592663
theorem B1511149 : Blo 350755 1511149 := bstep (se 3 (by rfl) ⟨283340, by rfl⟩ : syracuseStep 1511149 = 566681) B566681
theorem B528119 : Blo 350755 528119 := bstep (se 1 (by rfl) ⟨396089, by rfl⟩ : syracuseStep 528119 = 792179) B792179
theorem B528143 : Blo 350755 528143 := bstep (se 1 (by rfl) ⟨396107, by rfl⟩ : syracuseStep 528143 = 792215) B792215
theorem B528185 : Blo 350755 528185 := bstep (se 2 (by rfl) ⟨198069, by rfl⟩ : syracuseStep 528185 = 396139) B396139
theorem B593723 : Blo 350755 593723 := bstep (se 1 (by rfl) ⟨445292, by rfl⟩ : syracuseStep 593723 = 890585) B890585
theorem B888691 : Blo 350755 888691 := bstep (se 1 (by rfl) ⟨666518, by rfl⟩ : syracuseStep 888691 = 1333037) B1333037
theorem B528263 : Blo 350755 528263 := bstep (se 1 (by rfl) ⟨396197, by rfl⟩ : syracuseStep 528263 = 792395) B792395
theorem B3379097 : Blo 350755 3379097 := bstep (se 2 (by rfl) ⟨1267161, by rfl⟩ : syracuseStep 3379097 = 2534323) B2534323
theorem B528299 : Blo 350755 528299 := bstep (se 1 (by rfl) ⟨396224, by rfl⟩ : syracuseStep 528299 = 792449) B792449
theorem B528329 : Blo 350755 528329 := bstep (se 2 (by rfl) ⟨198123, by rfl⟩ : syracuseStep 528329 = 396247) B396247
theorem B1904593 : Blo 350755 1904593 := bstep (se 2 (by rfl) ⟨714222, by rfl⟩ : syracuseStep 1904593 = 1428445) B1428445
theorem B888833 : Blo 350755 888833 := bstep (se 2 (by rfl) ⟨333312, by rfl⟩ : syracuseStep 888833 = 666625) B666625
theorem B397327 : Blo 350755 397327 := bstep (se 1 (by rfl) ⟨297995, by rfl⟩ : syracuseStep 397327 = 595991) B595991
theorem B528443 : Blo 350755 528443 := bstep (se 1 (by rfl) ⟨396332, by rfl⟩ : syracuseStep 528443 = 792665) B792665
theorem B9605213 : Blo 350755 9605213 := bstep (se 3 (by rfl) ⟨1800977, by rfl⟩ : syracuseStep 9605213 = 3601955) B3601955
theorem B6951005 : Blo 350755 6951005 := bstep (se 3 (by rfl) ⟨1303313, by rfl⟩ : syracuseStep 6951005 = 2606627) B2606627
theorem B528503 : Blo 350755 528503 := bstep (se 1 (by rfl) ⟨396377, by rfl⟩ : syracuseStep 528503 = 792755) B792755
theorem B528527 : Blo 350755 528527 := bstep (se 1 (by rfl) ⟨396395, by rfl⟩ : syracuseStep 528527 = 792791) B792791
theorem B528569 : Blo 350755 528569 := bstep (se 2 (by rfl) ⟨198213, by rfl⟩ : syracuseStep 528569 = 396427) B396427
theorem B594121 : Blo 350755 594121 := bstep (se 2 (by rfl) ⟨222795, by rfl⟩ : syracuseStep 594121 = 445591) B445591
theorem B2003201 : Blo 350755 2003201 := bstep (se 2 (by rfl) ⟨751200, by rfl⟩ : syracuseStep 2003201 = 1502401) B1502401
theorem B528647 : Blo 350755 528647 := bstep (se 1 (by rfl) ⟨396485, by rfl⟩ : syracuseStep 528647 = 792971) B792971
theorem B528683 : Blo 350755 528683 := bstep (se 1 (by rfl) ⟨396512, by rfl⟩ : syracuseStep 528683 = 793025) B793025
theorem B528713 : Blo 350755 528713 := bstep (se 2 (by rfl) ⟨198267, by rfl⟩ : syracuseStep 528713 = 396535) B396535
theorem B790919 : Blo 350755 790919 := bstep (se 1 (by rfl) ⟨593189, by rfl⟩ : syracuseStep 790919 = 1186379) B1186379
theorem B3019153 : Blo 350755 3019153 := bstep (se 2 (by rfl) ⟨1132182, by rfl⟩ : syracuseStep 3019153 = 2264365) B2264365
theorem B528827 : Blo 350755 528827 := bstep (se 1 (by rfl) ⟨396620, by rfl⟩ : syracuseStep 528827 = 793241) B793241
theorem B889289 : Blo 350755 889289 := bstep (se 2 (by rfl) ⟨333483, by rfl⟩ : syracuseStep 889289 = 666967) B666967
theorem B528887 : Blo 350755 528887 := bstep (se 1 (by rfl) ⟨396665, by rfl⟩ : syracuseStep 528887 = 793331) B793331
theorem B397831 : Blo 350755 397831 := bstep (se 1 (by rfl) ⟨298373, by rfl⟩ : syracuseStep 397831 = 596747) B596747
theorem B528911 : Blo 350755 528911 := bstep (se 1 (by rfl) ⟨396683, by rfl⟩ : syracuseStep 528911 = 793367) B793367
theorem B528953 : Blo 350755 528953 := bstep (se 2 (by rfl) ⟨198357, by rfl⟩ : syracuseStep 528953 = 396715) B396715
theorem B791099 : Blo 350755 791099 := bstep (se 1 (by rfl) ⟨593324, by rfl⟩ : syracuseStep 791099 = 1186649) B1186649
theorem B529031 : Blo 350755 529031 := bstep (se 1 (by rfl) ⟨396773, by rfl⟩ : syracuseStep 529031 = 793547) B793547
theorem B529067 : Blo 350755 529067 := bstep (se 1 (by rfl) ⟨396800, by rfl⟩ : syracuseStep 529067 = 793601) B793601
theorem B791225 : Blo 350755 791225 := bstep (se 2 (by rfl) ⟨296709, by rfl⟩ : syracuseStep 791225 = 593419) B593419
theorem B398011 : Blo 350755 398011 := bstep (se 1 (by rfl) ⟨298508, by rfl⟩ : syracuseStep 398011 = 597017) B597017
theorem B529097 : Blo 350755 529097 := bstep (se 2 (by rfl) ⟨198411, by rfl⟩ : syracuseStep 529097 = 396823) B396823
theorem B7574309 : Blo 350755 7574309 := bstep (se 4 (by rfl) ⟨710091, by rfl⟩ : syracuseStep 7574309 = 1420183) B1420183
theorem B889643 : Blo 350755 889643 := bstep (se 1 (by rfl) ⟨667232, by rfl⟩ : syracuseStep 889643 = 1334465) B1334465
theorem B529211 : Blo 350755 529211 := bstep (se 1 (by rfl) ⟨396908, by rfl⟩ : syracuseStep 529211 = 793817) B793817
theorem B4821875 : Blo 350755 4821875 := bstep (se 1 (by rfl) ⟨3616406, by rfl⟩ : syracuseStep 4821875 = 7232813) B7232813
theorem B529271 : Blo 350755 529271 := bstep (se 1 (by rfl) ⟨396953, by rfl⟩ : syracuseStep 529271 = 793907) B793907
theorem B594823 : Blo 350755 594823 := bstep (se 1 (by rfl) ⟨446117, by rfl⟩ : syracuseStep 594823 = 892235) B892235
theorem B529295 : Blo 350755 529295 := bstep (se 1 (by rfl) ⟨396971, by rfl⟩ : syracuseStep 529295 = 793943) B793943
theorem B529337 : Blo 350755 529337 := bstep (se 2 (by rfl) ⟨198501, by rfl⟩ : syracuseStep 529337 = 397003) B397003
theorem B529415 : Blo 350755 529415 := bstep (se 1 (by rfl) ⟨397061, by rfl⟩ : syracuseStep 529415 = 794123) B794123
theorem B791567 : Blo 350755 791567 := bstep (se 1 (by rfl) ⟨593675, by rfl⟩ : syracuseStep 791567 = 1187351) B1187351
theorem B791585 : Blo 350755 791585 := bstep (se 2 (by rfl) ⟨296844, by rfl⟩ : syracuseStep 791585 = 593689) B593689
theorem B529451 : Blo 350755 529451 := bstep (se 1 (by rfl) ⟨397088, by rfl⟩ : syracuseStep 529451 = 794177) B794177
theorem B529481 : Blo 350755 529481 := bstep (se 2 (by rfl) ⟨198555, by rfl⟩ : syracuseStep 529481 = 397111) B397111
theorem B398479 : Blo 350755 398479 := bstep (se 1 (by rfl) ⟨298859, by rfl⟩ : syracuseStep 398479 = 597719) B597719
theorem B529595 : Blo 350755 529595 := bstep (se 1 (by rfl) ⟨397196, by rfl⟩ : syracuseStep 529595 = 794393) B794393
theorem B529655 : Blo 350755 529655 := bstep (se 1 (by rfl) ⟨397241, by rfl⟩ : syracuseStep 529655 = 794483) B794483
theorem B529679 : Blo 350755 529679 := bstep (se 1 (by rfl) ⟨397259, by rfl⟩ : syracuseStep 529679 = 794519) B794519
theorem B529721 : Blo 350755 529721 := bstep (se 2 (by rfl) ⟨198645, by rfl⟩ : syracuseStep 529721 = 397291) B397291
theorem B1185083 : Blo 350755 1185083 := bstep (se 1 (by rfl) ⟨888812, by rfl⟩ : syracuseStep 1185083 = 1777625) B1777625
theorem B791927 : Blo 350755 791927 := bstep (se 1 (by rfl) ⟨593945, by rfl⟩ : syracuseStep 791927 = 1187891) B1187891
theorem B529799 : Blo 350755 529799 := bstep (se 1 (by rfl) ⟨397349, by rfl⟩ : syracuseStep 529799 = 794699) B794699
theorem B1512857 : Blo 350755 1512857 := bstep (se 2 (by rfl) ⟨567321, by rfl⟩ : syracuseStep 1512857 = 1134643) B1134643
theorem B529835 : Blo 350755 529835 := bstep (se 1 (by rfl) ⟨397376, by rfl⟩ : syracuseStep 529835 = 794753) B794753
theorem B431531 : Blo 350755 431531 := bstep (se 1 (by rfl) ⟨323648, by rfl⟩ : syracuseStep 431531 = 647297) B647297
theorem B529865 : Blo 350755 529865 := bstep (se 2 (by rfl) ⟨198699, by rfl⟩ : syracuseStep 529865 = 397399) B397399
theorem B595471 : Blo 350755 595471 := bstep (se 1 (by rfl) ⟨446603, by rfl⟩ : syracuseStep 595471 = 893207) B893207
theorem B792107 : Blo 350755 792107 := bstep (se 1 (by rfl) ⟨594080, by rfl⟩ : syracuseStep 792107 = 1188161) B1188161
theorem B529979 : Blo 350755 529979 := bstep (se 1 (by rfl) ⟨397484, by rfl⟩ : syracuseStep 529979 = 794969) B794969
theorem B530039 : Blo 350755 530039 := bstep (se 1 (by rfl) ⟨397529, by rfl⟩ : syracuseStep 530039 = 795059) B795059
theorem B398983 : Blo 350755 398983 := bstep (se 1 (by rfl) ⟨299237, by rfl⟩ : syracuseStep 398983 = 598475) B598475
theorem B530063 : Blo 350755 530063 := bstep (se 1 (by rfl) ⟨397547, by rfl⟩ : syracuseStep 530063 = 795095) B795095
theorem B530105 : Blo 350755 530105 := bstep (se 2 (by rfl) ⟨198789, by rfl⟩ : syracuseStep 530105 = 397579) B397579
theorem B530183 : Blo 350755 530183 := bstep (se 1 (by rfl) ⟨397637, by rfl⟩ : syracuseStep 530183 = 795275) B795275
theorem B890635 : Blo 350755 890635 := bstep (se 1 (by rfl) ⟨667976, by rfl⟩ : syracuseStep 890635 = 1335953) B1335953
theorem B1185569 : Blo 350755 1185569 := bstep (se 2 (by rfl) ⟨444588, by rfl⟩ : syracuseStep 1185569 = 889177) B889177
theorem B530219 : Blo 350755 530219 := bstep (se 1 (by rfl) ⟨397664, by rfl⟩ : syracuseStep 530219 = 795329) B795329
theorem B530249 : Blo 350755 530249 := bstep (se 2 (by rfl) ⟨198843, by rfl⟩ : syracuseStep 530249 = 397687) B397687
theorem B792467 : Blo 350755 792467 := bstep (se 1 (by rfl) ⟨594350, by rfl⟩ : syracuseStep 792467 = 1188701) B1188701
theorem B1087379 : Blo 350755 1087379 := bstep (se 1 (by rfl) ⟨815534, by rfl⟩ : syracuseStep 1087379 = 1631069) B1631069
theorem B890777 : Blo 350755 890777 := bstep (se 2 (by rfl) ⟨334041, by rfl⟩ : syracuseStep 890777 = 668083) B668083
theorem B530363 : Blo 350755 530363 := bstep (se 1 (by rfl) ⟨397772, by rfl⟩ : syracuseStep 530363 = 795545) B795545
theorem B792521 : Blo 350755 792521 := bstep (se 2 (by rfl) ⟨297195, by rfl⟩ : syracuseStep 792521 = 594391) B594391
theorem B530423 : Blo 350755 530423 := bstep (se 1 (by rfl) ⟨397817, by rfl⟩ : syracuseStep 530423 = 795635) B795635
theorem B530447 : Blo 350755 530447 := bstep (se 1 (by rfl) ⟨397835, by rfl⟩ : syracuseStep 530447 = 795671) B795671
theorem B19666961 : Blo 350755 19666961 := bstep (se 2 (by rfl) ⟨7375110, by rfl⟩ : syracuseStep 19666961 = 14750221) B14750221
theorem B596011 : Blo 350755 596011 := bstep (se 1 (by rfl) ⟨447008, by rfl⟩ : syracuseStep 596011 = 894017) B894017
theorem B530489 : Blo 350755 530489 := bstep (se 2 (by rfl) ⟨198933, by rfl⟩ : syracuseStep 530489 = 397867) B397867
theorem B890939 : Blo 350755 890939 := bstep (se 1 (by rfl) ⟨668204, by rfl⟩ : syracuseStep 890939 = 1336409) B1336409
theorem B1251389 : Blo 350755 1251389 := bstep (se 3 (by rfl) ⟨234635, by rfl⟩ : syracuseStep 1251389 = 469271) B469271
theorem B2136131 : Blo 350755 2136131 := bstep (se 1 (by rfl) ⟨1602098, by rfl⟩ : syracuseStep 2136131 = 3204197) B3204197
theorem B530567 : Blo 350755 530567 := bstep (se 1 (by rfl) ⟨397925, by rfl⟩ : syracuseStep 530567 = 795851) B795851
theorem B956569 : Blo 350755 956569 := bstep (se 2 (by rfl) ⟨358713, by rfl⟩ : syracuseStep 956569 = 717427) B717427
theorem B530603 : Blo 350755 530603 := bstep (se 1 (by rfl) ⟨397952, by rfl⟩ : syracuseStep 530603 = 795905) B795905
theorem B596153 : Blo 350755 596153 := bstep (se 2 (by rfl) ⟨223557, by rfl⟩ : syracuseStep 596153 = 447115) B447115
theorem B530633 : Blo 350755 530633 := bstep (se 2 (by rfl) ⟨198987, by rfl⟩ : syracuseStep 530633 = 397975) B397975
theorem B530747 : Blo 350755 530747 := bstep (se 1 (by rfl) ⟨398060, by rfl⟩ : syracuseStep 530747 = 796121) B796121
theorem B1186163 : Blo 350755 1186163 := bstep (se 1 (by rfl) ⟨889622, by rfl⟩ : syracuseStep 1186163 = 1779245) B1779245
theorem B530807 : Blo 350755 530807 := bstep (se 1 (by rfl) ⟨398105, by rfl⟩ : syracuseStep 530807 = 796211) B796211
theorem B530831 : Blo 350755 530831 := bstep (se 1 (by rfl) ⟨398123, by rfl⟩ : syracuseStep 530831 = 796247) B796247
theorem B891283 : Blo 350755 891283 := bstep (se 1 (by rfl) ⟨668462, by rfl⟩ : syracuseStep 891283 = 1336925) B1336925
theorem B14522773 : Blo 350755 14522773 := bstep (se 6 (by rfl) ⟨340377, by rfl⟩ : syracuseStep 14522773 = 680755) B680755
theorem B530873 : Blo 350755 530873 := bstep (se 2 (by rfl) ⟨199077, by rfl⟩ : syracuseStep 530873 = 398155) B398155
theorem B530951 : Blo 350755 530951 := bstep (se 1 (by rfl) ⟨398213, by rfl⟩ : syracuseStep 530951 = 796427) B796427
theorem B891425 : Blo 350755 891425 := bstep (se 2 (by rfl) ⟨334284, by rfl⟩ : syracuseStep 891425 = 668569) B668569
theorem B530987 : Blo 350755 530987 := bstep (se 1 (by rfl) ⟨398240, by rfl⟩ : syracuseStep 530987 = 796481) B796481
theorem B531017 : Blo 350755 531017 := bstep (se 2 (by rfl) ⟨199131, by rfl⟩ : syracuseStep 531017 = 398263) B398263
theorem B563831 : Blo 350755 563831 := bstep (se 1 (by rfl) ⟨422873, by rfl⟩ : syracuseStep 563831 = 845747) B845747
theorem B793223 : Blo 350755 793223 := bstep (se 1 (by rfl) ⟨594917, by rfl⟩ : syracuseStep 793223 = 1189835) B1189835
theorem B531131 : Blo 350755 531131 := bstep (se 1 (by rfl) ⟨398348, by rfl⟩ : syracuseStep 531131 = 796697) B796697
theorem B1776329 : Blo 350755 1776329 := bstep (se 2 (by rfl) ⟨666123, by rfl⟩ : syracuseStep 1776329 = 1332247) B1332247
theorem B531191 : Blo 350755 531191 := bstep (se 1 (by rfl) ⟨398393, by rfl⟩ : syracuseStep 531191 = 796787) B796787
theorem B531215 : Blo 350755 531215 := bstep (se 1 (by rfl) ⟨398411, by rfl⟩ : syracuseStep 531215 = 796823) B796823
theorem B531257 : Blo 350755 531257 := bstep (se 2 (by rfl) ⟨199221, by rfl⟩ : syracuseStep 531257 = 398443) B398443
theorem B793403 : Blo 350755 793403 := bstep (se 1 (by rfl) ⟨595052, by rfl⟩ : syracuseStep 793403 = 1190105) B1190105
theorem B596855 : Blo 350755 596855 := bstep (se 1 (by rfl) ⟨447641, by rfl⟩ : syracuseStep 596855 = 895283) B895283
theorem B531335 : Blo 350755 531335 := bstep (se 1 (by rfl) ⟨398501, by rfl⟩ : syracuseStep 531335 = 797003) B797003
theorem B531371 : Blo 350755 531371 := bstep (se 1 (by rfl) ⟨398528, by rfl⟩ : syracuseStep 531371 = 797057) B797057
theorem B793529 : Blo 350755 793529 := bstep (se 2 (by rfl) ⟨297573, by rfl⟩ : syracuseStep 793529 = 595147) B595147
theorem B531401 : Blo 350755 531401 := bstep (se 2 (by rfl) ⟨199275, by rfl⟩ : syracuseStep 531401 = 398551) B398551
theorem B531515 : Blo 350755 531515 := bstep (se 1 (by rfl) ⟨398636, by rfl⟩ : syracuseStep 531515 = 797273) B797273
theorem B1219645 : Blo 350755 1219645 := bstep (se 3 (by rfl) ⟨228683, by rfl⟩ : syracuseStep 1219645 = 457367) B457367
theorem B531575 : Blo 350755 531575 := bstep (se 1 (by rfl) ⟨398681, by rfl⟩ : syracuseStep 531575 = 797363) B797363
theorem B531599 : Blo 350755 531599 := bstep (se 1 (by rfl) ⟨398699, by rfl⟩ : syracuseStep 531599 = 797399) B797399
theorem B531641 : Blo 350755 531641 := bstep (se 2 (by rfl) ⟨199365, by rfl⟩ : syracuseStep 531641 = 398731) B398731
theorem B531719 : Blo 350755 531719 := bstep (se 1 (by rfl) ⟨398789, by rfl⟩ : syracuseStep 531719 = 797579) B797579
theorem B793871 : Blo 350755 793871 := bstep (se 1 (by rfl) ⟨595403, by rfl⟩ : syracuseStep 793871 = 1190807) B1190807
theorem B793889 : Blo 350755 793889 := bstep (se 2 (by rfl) ⟨297708, by rfl⟩ : syracuseStep 793889 = 595417) B595417
theorem B531755 : Blo 350755 531755 := bstep (se 1 (by rfl) ⟨398816, by rfl⟩ : syracuseStep 531755 = 797633) B797633
theorem B597307 : Blo 350755 597307 := bstep (se 1 (by rfl) ⟨447980, by rfl⟩ : syracuseStep 597307 = 895961) B895961
theorem B531785 : Blo 350755 531785 := bstep (se 2 (by rfl) ⟨199419, by rfl⟩ : syracuseStep 531785 = 398839) B398839
theorem B531899 : Blo 350755 531899 := bstep (se 1 (by rfl) ⟨398924, by rfl⟩ : syracuseStep 531899 = 797849) B797849
theorem B597449 : Blo 350755 597449 := bstep (se 2 (by rfl) ⟨224043, by rfl⟩ : syracuseStep 597449 = 448087) B448087
theorem B531959 : Blo 350755 531959 := bstep (se 1 (by rfl) ⟨398969, by rfl⟩ : syracuseStep 531959 = 797939) B797939
theorem B892417 : Blo 350755 892417 := bstep (se 2 (by rfl) ⟨334656, by rfl⟩ : syracuseStep 892417 = 669313) B669313
theorem B531983 : Blo 350755 531983 := bstep (se 1 (by rfl) ⟨398987, by rfl⟩ : syracuseStep 531983 = 797975) B797975
theorem B532025 : Blo 350755 532025 := bstep (se 2 (by rfl) ⟨199509, by rfl⟩ : syracuseStep 532025 = 399019) B399019
theorem B794231 : Blo 350755 794231 := bstep (se 1 (by rfl) ⟨595673, by rfl⟩ : syracuseStep 794231 = 1191347) B1191347
theorem B532103 : Blo 350755 532103 := bstep (se 1 (by rfl) ⟨399077, by rfl⟩ : syracuseStep 532103 = 798155) B798155
theorem B1908397 : Blo 350755 1908397 := bstep (se 3 (by rfl) ⟨357824, by rfl⟩ : syracuseStep 1908397 = 715649) B715649
theorem B794411 : Blo 350755 794411 := bstep (se 1 (by rfl) ⟨595808, by rfl⟩ : syracuseStep 794411 = 1191617) B1191617
theorem B893015 : Blo 350755 893015 := bstep (se 1 (by rfl) ⟨669761, by rfl⟩ : syracuseStep 893015 = 1339523) B1339523
theorem B598151 : Blo 350755 598151 := bstep (se 1 (by rfl) ⟨448613, by rfl⟩ : syracuseStep 598151 = 897227) B897227
theorem B794771 : Blo 350755 794771 := bstep (se 1 (by rfl) ⟨596078, by rfl⟩ : syracuseStep 794771 = 1192157) B1192157
theorem B794825 : Blo 350755 794825 := bstep (se 2 (by rfl) ⟨298059, by rfl⟩ : syracuseStep 794825 = 596119) B596119
theorem B893227 : Blo 350755 893227 := bstep (se 1 (by rfl) ⟨669920, by rfl⟩ : syracuseStep 893227 = 1339841) B1339841
theorem B893369 : Blo 350755 893369 := bstep (se 2 (by rfl) ⟨335013, by rfl⟩ : syracuseStep 893369 = 670027) B670027
theorem B2007575 : Blo 350755 2007575 := bstep (se 1 (by rfl) ⟨1505681, by rfl⟩ : syracuseStep 2007575 = 3011363) B3011363
theorem B795527 : Blo 350755 795527 := bstep (se 1 (by rfl) ⟨596645, by rfl⟩ : syracuseStep 795527 = 1193291) B1193291
theorem B1188755 : Blo 350755 1188755 := bstep (se 1 (by rfl) ⟨891566, by rfl⟩ : syracuseStep 1188755 = 1783133) B1783133
theorem B500681 : Blo 350755 500681 := bstep (se 2 (by rfl) ⟨187755, by rfl⟩ : syracuseStep 500681 = 375511) B375511
theorem B795707 : Blo 350755 795707 := bstep (se 1 (by rfl) ⟨596780, by rfl⟩ : syracuseStep 795707 = 1193561) B1193561
theorem B533647 : Blo 350755 533647 := bstep (se 1 (by rfl) ⟨400235, by rfl⟩ : syracuseStep 533647 = 800471) B800471
theorem B795833 : Blo 350755 795833 := bstep (se 2 (by rfl) ⟨298437, by rfl⟩ : syracuseStep 795833 = 596875) B596875
theorem B2041139 : Blo 350755 2041139 := bstep (se 1 (by rfl) ⟨1530854, by rfl⟩ : syracuseStep 2041139 = 3061709) B3061709
theorem B894361 : Blo 350755 894361 := bstep (se 2 (by rfl) ⟨335385, by rfl⟩ : syracuseStep 894361 = 670771) B670771
theorem B796175 : Blo 350755 796175 := bstep (se 1 (by rfl) ⟨597131, by rfl⟩ : syracuseStep 796175 = 1194263) B1194263
theorem B796193 : Blo 350755 796193 := bstep (se 2 (by rfl) ⟨298572, by rfl⟩ : syracuseStep 796193 = 597145) B597145
theorem B894523 : Blo 350755 894523 := bstep (se 1 (by rfl) ⟨670892, by rfl⟩ : syracuseStep 894523 = 1341785) B1341785
theorem B2532941 : Blo 350755 2532941 := bstep (se 3 (by rfl) ⟨474926, by rfl⟩ : syracuseStep 2532941 = 949853) B949853
theorem B894665 : Blo 350755 894665 := bstep (se 2 (by rfl) ⟨335499, by rfl⟩ : syracuseStep 894665 = 670999) B670999
theorem B1124111 : Blo 350755 1124111 := bstep (se 1 (by rfl) ⟨843083, by rfl⟩ : syracuseStep 1124111 = 1686167) B1686167
theorem B501547 : Blo 350755 501547 := bstep (se 1 (by rfl) ⟨376160, by rfl⟩ : syracuseStep 501547 = 752321) B752321
theorem B18425717 : Blo 350755 18425717 := bstep (se 5 (by rfl) ⟨863705, by rfl⟩ : syracuseStep 18425717 = 1727411) B1727411
theorem B796535 : Blo 350755 796535 := bstep (se 1 (by rfl) ⟨597401, by rfl⟩ : syracuseStep 796535 = 1194803) B1194803
theorem B3876761 : Blo 350755 3876761 := bstep (se 2 (by rfl) ⟨1453785, by rfl⟩ : syracuseStep 3876761 = 2907571) B2907571
theorem B1124381 : Blo 350755 1124381 := bstep (se 3 (by rfl) ⟨210821, by rfl⟩ : syracuseStep 1124381 = 421643) B421643
theorem B895009 : Blo 350755 895009 := bstep (se 2 (by rfl) ⟨335628, by rfl⟩ : syracuseStep 895009 = 671257) B671257
theorem B632875 : Blo 350755 632875 := bstep (se 1 (by rfl) ⟨474656, by rfl⟩ : syracuseStep 632875 = 949313) B949313
theorem B796715 : Blo 350755 796715 := bstep (se 1 (by rfl) ⟨597536, by rfl⟩ : syracuseStep 796715 = 1195073) B1195073
theorem B1190159 : Blo 350755 1190159 := bstep (se 1 (by rfl) ⟨892619, by rfl⟩ : syracuseStep 1190159 = 1785239) B1785239
theorem B2664737 : Blo 350755 2664737 := bstep (se 2 (by rfl) ⟨999276, by rfl⟩ : syracuseStep 2664737 = 1998553) B1998553
theorem B797075 : Blo 350755 797075 := bstep (se 1 (by rfl) ⟨597806, by rfl⟩ : syracuseStep 797075 = 1195613) B1195613
theorem B797129 : Blo 350755 797129 := bstep (se 2 (by rfl) ⟨298923, by rfl⟩ : syracuseStep 797129 = 597847) B597847
theorem B15313373 : Blo 350755 15313373 := bstep (se 3 (by rfl) ⟨2871257, by rfl⟩ : syracuseStep 15313373 = 5742515) B5742515
theorem B1190429 : Blo 350755 1190429 := bstep (se 3 (by rfl) ⟨223205, by rfl⟩ : syracuseStep 1190429 = 446411) B446411
theorem B895607 : Blo 350755 895607 := bstep (se 1 (by rfl) ⟨671705, by rfl⟩ : syracuseStep 895607 = 1343411) B1343411
theorem B764873 : Blo 350755 764873 := bstep (se 2 (by rfl) ⟨286827, by rfl⟩ : syracuseStep 764873 = 573655) B573655
theorem B797831 : Blo 350755 797831 := bstep (se 1 (by rfl) ⟨598373, by rfl⟩ : syracuseStep 797831 = 1196747) B1196747
theorem B2665709 : Blo 350755 2665709 := bstep (se 3 (by rfl) ⟨499820, by rfl⟩ : syracuseStep 2665709 = 999641) B999641
theorem B1617185 : Blo 350755 1617185 := bstep (se 2 (by rfl) ⟨606444, by rfl⟩ : syracuseStep 1617185 = 1212889) B1212889
theorem B798011 : Blo 350755 798011 := bstep (se 1 (by rfl) ⟨598508, by rfl⟩ : syracuseStep 798011 = 1197017) B1197017
theorem B503113 : Blo 350755 503113 := bstep (se 2 (by rfl) ⟨188667, by rfl⟩ : syracuseStep 503113 = 377335) B377335
theorem B798137 : Blo 350755 798137 := bstep (se 2 (by rfl) ⟨299301, by rfl⟩ : syracuseStep 798137 = 598603) B598603
theorem B2010743 : Blo 350755 2010743 := bstep (se 1 (by rfl) ⟨1508057, by rfl⟩ : syracuseStep 2010743 = 3016115) B3016115
theorem B667271 : Blo 350755 667271 := bstep (se 1 (by rfl) ⟨500453, by rfl⟩ : syracuseStep 667271 = 1000907) B1000907
theorem B503671 : Blo 350755 503671 := bstep (se 1 (by rfl) ⟨377753, by rfl⟩ : syracuseStep 503671 = 755507) B755507
theorem B896903 : Blo 350755 896903 := bstep (se 1 (by rfl) ⟨672677, by rfl⟩ : syracuseStep 896903 = 1345355) B1345355
theorem B1191833 : Blo 350755 1191833 := bstep (se 2 (by rfl) ⟨446937, by rfl⟩ : syracuseStep 1191833 = 893875) B893875
theorem B896953 : Blo 350755 896953 := bstep (se 2 (by rfl) ⟨336357, by rfl⟩ : syracuseStep 896953 = 672715) B672715
theorem B3321917 : Blo 350755 3321917 := bstep (se 3 (by rfl) ⟨622859, by rfl⟩ : syracuseStep 3321917 = 1245719) B1245719
theorem B536761 : Blo 350755 536761 := bstep (se 2 (by rfl) ⟨201285, by rfl⟩ : syracuseStep 536761 = 402571) B402571
theorem B1782161 : Blo 350755 1782161 := bstep (se 2 (by rfl) ⟨668310, by rfl⟩ : syracuseStep 1782161 = 1336621) B1336621
theorem B3322259 : Blo 350755 3322259 := bstep (se 1 (by rfl) ⟨2491694, by rfl⟩ : syracuseStep 3322259 = 4983389) B4983389
theorem B504235 : Blo 350755 504235 := bstep (se 1 (by rfl) ⟨378176, by rfl⟩ : syracuseStep 504235 = 756353) B756353
theorem B897551 : Blo 350755 897551 := bstep (se 1 (by rfl) ⟨673163, by rfl⟩ : syracuseStep 897551 = 1346327) B1346327
theorem B1126955 : Blo 350755 1126955 := bstep (se 1 (by rfl) ⟨845216, by rfl⟩ : syracuseStep 1126955 = 1690433) B1690433
theorem B1192535 : Blo 350755 1192535 := bstep (se 1 (by rfl) ⟨894401, by rfl⟩ : syracuseStep 1192535 = 1788803) B1788803
theorem B635527 : Blo 350755 635527 := bstep (se 1 (by rfl) ⟨476645, by rfl⟩ : syracuseStep 635527 = 953291) B953291
theorem B504463 : Blo 350755 504463 := bstep (se 1 (by rfl) ⟨378347, by rfl⟩ : syracuseStep 504463 = 756695) B756695
theorem B1127353 : Blo 350755 1127353 := bstep (se 2 (by rfl) ⟨422757, by rfl⟩ : syracuseStep 1127353 = 845515) B845515
theorem B2175947 : Blo 350755 2175947 := bstep (se 1 (by rfl) ⟨1631960, by rfl⟩ : syracuseStep 2175947 = 3263921) B3263921
theorem B1127467 : Blo 350755 1127467 := bstep (se 1 (by rfl) ⟨845600, by rfl⟩ : syracuseStep 1127467 = 1691201) B1691201
theorem B1193021 : Blo 350755 1193021 := bstep (se 3 (by rfl) ⟨223691, by rfl⟩ : syracuseStep 1193021 = 447383) B447383
theorem B2667653 : Blo 350755 2667653 := bstep (se 4 (by rfl) ⟨250092, by rfl⟩ : syracuseStep 2667653 = 500185) B500185
theorem B668873 : Blo 350755 668873 := bstep (se 2 (by rfl) ⟨250827, by rfl⟩ : syracuseStep 668873 = 501655) B501655
theorem B537929 : Blo 350755 537929 := bstep (se 2 (by rfl) ⟨201723, by rfl⟩ : syracuseStep 537929 = 403447) B403447
theorem B3225091 : Blo 350755 3225091 := bstep (se 1 (by rfl) ⟨2418818, by rfl⟩ : syracuseStep 3225091 = 4837637) B4837637
theorem B800545 : Blo 350755 800545 := bstep (se 2 (by rfl) ⟨300204, by rfl⟩ : syracuseStep 800545 = 600409) B600409
theorem B3258265 : Blo 350755 3258265 := bstep (se 2 (by rfl) ⟨1221849, by rfl⟩ : syracuseStep 3258265 = 2443699) B2443699
theorem B1194425 : Blo 350755 1194425 := bstep (se 2 (by rfl) ⟨447909, by rfl⟩ : syracuseStep 1194425 = 895819) B895819
theorem B1784267 : Blo 350755 1784267 := bstep (se 1 (by rfl) ⟨1338200, by rfl⟩ : syracuseStep 1784267 = 2676401) B2676401
theorem B3226189 : Blo 350755 3226189 := bstep (se 3 (by rfl) ⟨604910, by rfl⟩ : syracuseStep 3226189 = 1209821) B1209821
theorem B539255 : Blo 350755 539255 := bstep (se 1 (by rfl) ⟨404441, by rfl⟩ : syracuseStep 539255 = 808883) B808883
theorem B1784591 : Blo 350755 1784591 := bstep (se 1 (by rfl) ⟨1338443, by rfl⟩ : syracuseStep 1784591 = 2676887) B2676887
theorem B3390245 : Blo 350755 3390245 := bstep (se 4 (by rfl) ⟨317835, by rfl⟩ : syracuseStep 3390245 = 635671) B635671
theorem B16169827 : Blo 350755 16169827 := bstep (se 1 (by rfl) ⟨12127370, by rfl⟩ : syracuseStep 16169827 = 24254741) B24254741
theorem B1195019 : Blo 350755 1195019 := bstep (se 1 (by rfl) ⟨896264, by rfl⟩ : syracuseStep 1195019 = 1792529) B1792529
theorem B1195127 : Blo 350755 1195127 := bstep (se 1 (by rfl) ⟨896345, by rfl⟩ : syracuseStep 1195127 = 1792691) B1792691
theorem B670855 : Blo 350755 670855 := bstep (se 1 (by rfl) ⟨503141, by rfl⟩ : syracuseStep 670855 = 1006283) B1006283
theorem B2014409 : Blo 350755 2014409 := bstep (se 2 (by rfl) ⟨755403, by rfl⟩ : syracuseStep 2014409 = 1510807) B1510807
theorem B2670083 : Blo 350755 2670083 := bstep (se 1 (by rfl) ⟨2002562, by rfl⟩ : syracuseStep 2670083 = 4005125) B4005125
theorem B638599 : Blo 350755 638599 := bstep (se 1 (by rfl) ⟨478949, by rfl⟩ : syracuseStep 638599 = 957899) B957899
theorem B1195721 : Blo 350755 1195721 := bstep (se 2 (by rfl) ⟨448395, by rfl⟩ : syracuseStep 1195721 = 896791) B896791
theorem B2539313 : Blo 350755 2539313 := bstep (se 2 (by rfl) ⟨952242, by rfl⟩ : syracuseStep 2539313 = 1904485) B1904485
theorem B4013873 : Blo 350755 4013873 := bstep (se 2 (by rfl) ⟨1505202, by rfl⟩ : syracuseStep 4013873 = 3010405) B3010405
theorem B1786049 : Blo 350755 1786049 := bstep (se 2 (by rfl) ⟨669768, by rfl⟩ : syracuseStep 1786049 = 1339537) B1339537
theorem B1196423 : Blo 350755 1196423 := bstep (se 1 (by rfl) ⟨897317, by rfl⟩ : syracuseStep 1196423 = 1794635) B1794635
theorem B672457 : Blo 350755 672457 := bstep (se 2 (by rfl) ⟨252171, by rfl⟩ : syracuseStep 672457 = 504343) B504343
theorem B2540261 : Blo 350755 2540261 := bstep (se 4 (by rfl) ⟨238149, by rfl⟩ : syracuseStep 2540261 = 476299) B476299
theorem B1196801 : Blo 350755 1196801 := bstep (se 2 (by rfl) ⟨448800, by rfl⟩ : syracuseStep 1196801 = 897601) B897601
theorem B1000279 : Blo 350755 1000279 := bstep (se 1 (by rfl) ⟨750209, by rfl⟩ : syracuseStep 1000279 = 1500419) B1500419
theorem B1950617 : Blo 350755 1950617 := bstep (se 2 (by rfl) ⟨731481, by rfl⟩ : syracuseStep 1950617 = 1462963) B1462963
theorem B1000507 : Blo 350755 1000507 := bstep (se 1 (by rfl) ⟨750380, by rfl⟩ : syracuseStep 1000507 = 1500761) B1500761
theorem B2016323 : Blo 350755 2016323 := bstep (se 1 (by rfl) ⟨1512242, by rfl⟩ : syracuseStep 2016323 = 3024485) B3024485
theorem B1000633 : Blo 350755 1000633 := bstep (se 2 (by rfl) ⟨375237, by rfl⟩ : syracuseStep 1000633 = 750475) B750475
theorem B1787345 : Blo 350755 1787345 := bstep (se 2 (by rfl) ⟨670254, by rfl⟩ : syracuseStep 1787345 = 1340509) B1340509
theorem B902771 : Blo 350755 902771 := bstep (se 1 (by rfl) ⟨677078, by rfl⟩ : syracuseStep 902771 = 1354157) B1354157
theorem B1689281 : Blo 350755 1689281 := bstep (se 2 (by rfl) ⟨633480, by rfl⟩ : syracuseStep 1689281 = 1266961) B1266961
theorem B2148211 : Blo 350755 2148211 := bstep (se 1 (by rfl) ⟨1611158, by rfl⟩ : syracuseStep 2148211 = 3222317) B3222317
theorem B444295 : Blo 350755 444295 := bstep (se 1 (by rfl) ⟨333221, by rfl⟩ : syracuseStep 444295 = 666443) B666443
theorem B805135 : Blo 350755 805135 := bstep (se 1 (by rfl) ⟨603851, by rfl⟩ : syracuseStep 805135 = 1207703) B1207703
theorem B444791 : Blo 350755 444791 := bstep (se 1 (by rfl) ⟨333593, by rfl⟩ : syracuseStep 444791 = 667187) B667187
theorem B444943 : Blo 350755 444943 := bstep (se 1 (by rfl) ⟨333707, by rfl⟩ : syracuseStep 444943 = 667415) B667415
theorem B445115 : Blo 350755 445115 := bstep (se 1 (by rfl) ⟨333836, by rfl⟩ : syracuseStep 445115 = 667673) B667673
theorem B2542337 : Blo 350755 2542337 := bstep (se 2 (by rfl) ⟨953376, by rfl⟩ : syracuseStep 2542337 = 1906753) B1906753
theorem B1002557 : Blo 350755 1002557 := bstep (se 3 (by rfl) ⟨187979, by rfl⟩ : syracuseStep 1002557 = 375959) B375959
theorem B2149577 : Blo 350755 2149577 := bstep (se 2 (by rfl) ⟨806091, by rfl⟩ : syracuseStep 2149577 = 1612183) B1612183
theorem B904463 : Blo 350755 904463 := bstep (se 1 (by rfl) ⟨678347, by rfl⟩ : syracuseStep 904463 = 1356695) B1356695
theorem B3624209 : Blo 350755 3624209 := bstep (se 2 (by rfl) ⟨1359078, by rfl⟩ : syracuseStep 3624209 = 2718157) B2718157
theorem B642505 : Blo 350755 642505 := bstep (se 2 (by rfl) ⟨240939, by rfl⟩ : syracuseStep 642505 = 481879) B481879
theorem B2248145 : Blo 350755 2248145 := bstep (se 2 (by rfl) ⟨843054, by rfl⟩ : syracuseStep 2248145 = 1686109) B1686109
theorem B1789451 : Blo 350755 1789451 := bstep (se 1 (by rfl) ⟨1342088, by rfl⟩ : syracuseStep 1789451 = 2684177) B2684177
theorem B2543147 : Blo 350755 2543147 := bstep (se 1 (by rfl) ⟨1907360, by rfl⟩ : syracuseStep 2543147 = 3814721) B3814721
theorem B446087 : Blo 350755 446087 := bstep (se 1 (by rfl) ⟨334565, by rfl⟩ : syracuseStep 446087 = 669131) B669131
theorem B1789613 : Blo 350755 1789613 := bstep (se 3 (by rfl) ⟨335552, by rfl⟩ : syracuseStep 1789613 = 671105) B671105
theorem B1003549 : Blo 350755 1003549 := bstep (se 3 (by rfl) ⟨188165, by rfl⟩ : syracuseStep 1003549 = 376331) B376331
theorem B1364035 : Blo 350755 1364035 := bstep (se 1 (by rfl) ⟨1023026, by rfl⟩ : syracuseStep 1364035 = 2046053) B2046053
theorem B1200215 : Blo 350755 1200215 := bstep (se 1 (by rfl) ⟨900161, by rfl⟩ : syracuseStep 1200215 = 1800323) B1800323
theorem B446735 : Blo 350755 446735 := bstep (se 1 (by rfl) ⟨335051, by rfl⟩ : syracuseStep 446735 = 670103) B670103
theorem B2675429 : Blo 350755 2675429 := bstep (se 4 (by rfl) ⟨250821, by rfl⟩ : syracuseStep 2675429 = 501643) B501643
theorem B1692431 : Blo 350755 1692431 := bstep (se 1 (by rfl) ⟨1269323, by rfl⟩ : syracuseStep 1692431 = 2538647) B2538647
theorem B2544473 : Blo 350755 2544473 := bstep (se 2 (by rfl) ⟨954177, by rfl⟩ : syracuseStep 2544473 = 1908355) B1908355
theorem B2020241 : Blo 350755 2020241 := bstep (se 2 (by rfl) ⟨757590, by rfl⟩ : syracuseStep 2020241 = 1515181) B1515181
theorem B1528919 : Blo 350755 1528919 := bstep (se 1 (by rfl) ⟨1146689, by rfl⟩ : syracuseStep 1528919 = 2293379) B2293379
theorem B1791233 : Blo 350755 1791233 := bstep (se 2 (by rfl) ⟨671712, by rfl⟩ : syracuseStep 1791233 = 1343425) B1343425
theorem B1135873 : Blo 350755 1135873 := bstep (se 2 (by rfl) ⟨425952, by rfl⟩ : syracuseStep 1135873 = 851905) B851905
theorem B1430843 : Blo 350755 1430843 := bstep (se 1 (by rfl) ⟨1073132, by rfl⟩ : syracuseStep 1430843 = 2146265) B2146265
theorem B1333007 : Blo 350755 1333007 := bstep (se 1 (by rfl) ⟨999755, by rfl⟩ : syracuseStep 1333007 = 1999511) B1999511
theorem B1005497 : Blo 350755 1005497 := bstep (se 2 (by rfl) ⟨377061, by rfl⟩ : syracuseStep 1005497 = 754123) B754123
theorem B4118539 : Blo 350755 4118539 := bstep (se 1 (by rfl) ⟨3088904, by rfl⟩ : syracuseStep 4118539 = 6177809) B6177809
theorem B1792043 : Blo 350755 1792043 := bstep (se 1 (by rfl) ⟨1344032, by rfl⟩ : syracuseStep 1792043 = 2688065) B2688065
theorem B809003 : Blo 350755 809003 := bstep (se 1 (by rfl) ⟨606752, by rfl⟩ : syracuseStep 809003 = 1213505) B1213505
theorem B1694105 : Blo 350755 1694105 := bstep (se 2 (by rfl) ⟨635289, by rfl⟩ : syracuseStep 1694105 = 1270579) B1270579
theorem B350779 : Blo 350755 350779 := bstep (se 1 (by rfl) ⟨263084, by rfl⟩ : syracuseStep 350779 = 526169) B526169
theorem B350855 : Blo 350755 350855 := bstep (se 1 (by rfl) ⟨263141, by rfl⟩ : syracuseStep 350855 = 526283) B526283
theorem B350863 : Blo 350755 350863 := bstep (se 1 (by rfl) ⟨263147, by rfl⟩ : syracuseStep 350863 = 526295) B526295
theorem B350907 : Blo 350755 350907 := bstep (se 1 (by rfl) ⟨263180, by rfl⟩ : syracuseStep 350907 = 526361) B526361
theorem B350983 : Blo 350755 350983 := bstep (se 1 (by rfl) ⟨263237, by rfl⟩ : syracuseStep 350983 = 526475) B526475
theorem B350991 : Blo 350755 350991 := bstep (se 1 (by rfl) ⟨263243, by rfl⟩ : syracuseStep 350991 = 526487) B526487
theorem B351035 : Blo 350755 351035 := bstep (se 1 (by rfl) ⟨263276, by rfl⟩ : syracuseStep 351035 = 526553) B526553
theorem B351111 : Blo 350755 351111 := bstep (se 1 (by rfl) ⟨263333, by rfl⟩ : syracuseStep 351111 = 526667) B526667
theorem B908167 : Blo 350755 908167 := bstep (se 1 (by rfl) ⟨681125, by rfl⟩ : syracuseStep 908167 = 1362251) B1362251
theorem B351119 : Blo 350755 351119 := bstep (se 1 (by rfl) ⟨263339, by rfl⟩ : syracuseStep 351119 = 526679) B526679
theorem B351163 : Blo 350755 351163 := bstep (se 1 (by rfl) ⟨263372, by rfl⟩ : syracuseStep 351163 = 526745) B526745
theorem B351239 : Blo 350755 351239 := bstep (se 1 (by rfl) ⟨263429, by rfl⟩ : syracuseStep 351239 = 526859) B526859
theorem B351247 : Blo 350755 351247 := bstep (se 1 (by rfl) ⟨263435, by rfl⟩ : syracuseStep 351247 = 526871) B526871
theorem B842795 : Blo 350755 842795 := bstep (se 1 (by rfl) ⟨632096, by rfl⟩ : syracuseStep 842795 = 1264193) B1264193
theorem B351291 : Blo 350755 351291 := bstep (se 1 (by rfl) ⟨263468, by rfl⟩ : syracuseStep 351291 = 526937) B526937
theorem B1072187 : Blo 350755 1072187 := bstep (se 1 (by rfl) ⟨804140, by rfl⟩ : syracuseStep 1072187 = 1608281) B1608281
theorem B5069911 : Blo 350755 5069911 := bstep (se 1 (by rfl) ⟨3802433, by rfl⟩ : syracuseStep 5069911 = 7604867) B7604867
theorem B351367 : Blo 350755 351367 := bstep (se 1 (by rfl) ⟨263525, by rfl⟩ : syracuseStep 351367 = 527051) B527051
theorem B613511 : Blo 350755 613511 := bstep (se 1 (by rfl) ⟨460133, by rfl⟩ : syracuseStep 613511 = 920267) B920267
theorem B351375 : Blo 350755 351375 := bstep (se 1 (by rfl) ⟨263531, by rfl⟩ : syracuseStep 351375 = 527063) B527063
theorem B1006739 : Blo 350755 1006739 := bstep (se 1 (by rfl) ⟨755054, by rfl⟩ : syracuseStep 1006739 = 1510109) B1510109
theorem B351419 : Blo 350755 351419 := bstep (se 1 (by rfl) ⟨263564, by rfl⟩ : syracuseStep 351419 = 527129) B527129
theorem B351495 : Blo 350755 351495 := bstep (se 1 (by rfl) ⟨263621, by rfl⟩ : syracuseStep 351495 = 527243) B527243
theorem B351503 : Blo 350755 351503 := bstep (se 1 (by rfl) ⟨263627, by rfl⟩ : syracuseStep 351503 = 527255) B527255
theorem B351547 : Blo 350755 351547 := bstep (se 1 (by rfl) ⟨263660, by rfl⟩ : syracuseStep 351547 = 527321) B527321
theorem B1793339 : Blo 350755 1793339 := bstep (se 1 (by rfl) ⟨1345004, by rfl⟩ : syracuseStep 1793339 = 2690009) B2690009
theorem B1334663 : Blo 350755 1334663 := bstep (se 1 (by rfl) ⟨1000997, by rfl⟩ : syracuseStep 1334663 = 2001995) B2001995
theorem B351623 : Blo 350755 351623 := bstep (se 1 (by rfl) ⟨263717, by rfl⟩ : syracuseStep 351623 = 527435) B527435
theorem B351631 : Blo 350755 351631 := bstep (se 1 (by rfl) ⟨263723, by rfl⟩ : syracuseStep 351631 = 527447) B527447
theorem B351675 : Blo 350755 351675 := bstep (se 1 (by rfl) ⟨263756, by rfl⟩ : syracuseStep 351675 = 527513) B527513
theorem B1793501 : Blo 350755 1793501 := bstep (se 3 (by rfl) ⟨336281, by rfl⟩ : syracuseStep 1793501 = 672563) B672563
theorem B351751 : Blo 350755 351751 := bstep (se 1 (by rfl) ⟨263813, by rfl⟩ : syracuseStep 351751 = 527627) B527627
theorem B351759 : Blo 350755 351759 := bstep (se 1 (by rfl) ⟨263819, by rfl⟩ : syracuseStep 351759 = 527639) B527639
theorem B1072673 : Blo 350755 1072673 := bstep (se 2 (by rfl) ⟨402252, by rfl⟩ : syracuseStep 1072673 = 804505) B804505
theorem B351803 : Blo 350755 351803 := bstep (se 1 (by rfl) ⟨263852, by rfl⟩ : syracuseStep 351803 = 527705) B527705
theorem B351879 : Blo 350755 351879 := bstep (se 1 (by rfl) ⟨263909, by rfl⟩ : syracuseStep 351879 = 527819) B527819
theorem B351887 : Blo 350755 351887 := bstep (se 1 (by rfl) ⟨263915, by rfl⟩ : syracuseStep 351887 = 527831) B527831
theorem B450235 : Blo 350755 450235 := bstep (se 1 (by rfl) ⟨337676, by rfl⟩ : syracuseStep 450235 = 675353) B675353
theorem B351931 : Blo 350755 351931 := bstep (se 1 (by rfl) ⟨263948, by rfl⟩ : syracuseStep 351931 = 527897) B527897
theorem B483017 : Blo 350755 483017 := bstep (se 2 (by rfl) ⟨181131, by rfl⟩ : syracuseStep 483017 = 362263) B362263
theorem B352007 : Blo 350755 352007 := bstep (se 1 (by rfl) ⟨264005, by rfl⟩ : syracuseStep 352007 = 528011) B528011
theorem B352015 : Blo 350755 352015 := bstep (se 1 (by rfl) ⟨264011, by rfl⟩ : syracuseStep 352015 = 528023) B528023
theorem B1793825 : Blo 350755 1793825 := bstep (se 2 (by rfl) ⟨672684, by rfl⟩ : syracuseStep 1793825 = 1345369) B1345369
theorem B352059 : Blo 350755 352059 := bstep (se 1 (by rfl) ⟨264044, by rfl⟩ : syracuseStep 352059 = 528089) B528089
theorem B352135 : Blo 350755 352135 := bstep (se 1 (by rfl) ⟨264101, by rfl⟩ : syracuseStep 352135 = 528203) B528203
theorem B352143 : Blo 350755 352143 := bstep (se 1 (by rfl) ⟨264107, by rfl⟩ : syracuseStep 352143 = 528215) B528215
theorem B12443543 : Blo 350755 12443543 := bstep (se 1 (by rfl) ⟨9332657, by rfl⟩ : syracuseStep 12443543 = 18665315) B18665315
theorem B352187 : Blo 350755 352187 := bstep (se 1 (by rfl) ⟨264140, by rfl⟩ : syracuseStep 352187 = 528281) B528281
theorem B352263 : Blo 350755 352263 := bstep (se 1 (by rfl) ⟨264197, by rfl⟩ : syracuseStep 352263 = 528395) B528395
theorem B352271 : Blo 350755 352271 := bstep (se 1 (by rfl) ⟨264203, by rfl⟩ : syracuseStep 352271 = 528407) B528407
theorem B352315 : Blo 350755 352315 := bstep (se 1 (by rfl) ⟨264236, by rfl⟩ : syracuseStep 352315 = 528473) B528473
theorem B352391 : Blo 350755 352391 := bstep (se 1 (by rfl) ⟨264293, by rfl⟩ : syracuseStep 352391 = 528587) B528587
theorem B352399 : Blo 350755 352399 := bstep (se 1 (by rfl) ⟨264299, by rfl⟩ : syracuseStep 352399 = 528599) B528599
theorem B352443 : Blo 350755 352443 := bstep (se 1 (by rfl) ⟨264332, by rfl⟩ : syracuseStep 352443 = 528665) B528665
theorem B843977 : Blo 350755 843977 := bstep (se 2 (by rfl) ⟨316491, by rfl⟩ : syracuseStep 843977 = 632983) B632983
theorem B352519 : Blo 350755 352519 := bstep (se 1 (by rfl) ⟨264389, by rfl⟩ : syracuseStep 352519 = 528779) B528779
theorem B352527 : Blo 350755 352527 := bstep (se 1 (by rfl) ⟨264395, by rfl⟩ : syracuseStep 352527 = 528791) B528791
theorem B2253089 : Blo 350755 2253089 := bstep (se 2 (by rfl) ⟨844908, by rfl⟩ : syracuseStep 2253089 = 1689817) B1689817
theorem B352571 : Blo 350755 352571 := bstep (se 1 (by rfl) ⟨264428, by rfl⟩ : syracuseStep 352571 = 528857) B528857
theorem B4022621 : Blo 350755 4022621 := bstep (se 3 (by rfl) ⟨754241, by rfl⟩ : syracuseStep 4022621 = 1508483) B1508483
theorem B352647 : Blo 350755 352647 := bstep (se 1 (by rfl) ⟨264485, by rfl⟩ : syracuseStep 352647 = 528971) B528971
theorem B352655 : Blo 350755 352655 := bstep (se 1 (by rfl) ⟨264491, by rfl⟩ : syracuseStep 352655 = 528983) B528983
theorem B352699 : Blo 350755 352699 := bstep (se 1 (by rfl) ⟨264524, by rfl⟩ : syracuseStep 352699 = 529049) B529049
theorem B352775 : Blo 350755 352775 := bstep (se 1 (by rfl) ⟨264581, by rfl⟩ : syracuseStep 352775 = 529163) B529163
theorem B1008139 : Blo 350755 1008139 := bstep (se 1 (by rfl) ⟨756104, by rfl⟩ : syracuseStep 1008139 = 1512209) B1512209
theorem B352783 : Blo 350755 352783 := bstep (se 1 (by rfl) ⟨264587, by rfl⟩ : syracuseStep 352783 = 529175) B529175
theorem B352827 : Blo 350755 352827 := bstep (se 1 (by rfl) ⟨264620, by rfl⟩ : syracuseStep 352827 = 529241) B529241
theorem B1499735 : Blo 350755 1499735 := bstep (se 1 (by rfl) ⟨1124801, by rfl⟩ : syracuseStep 1499735 = 2249603) B2249603
theorem B352903 : Blo 350755 352903 := bstep (se 1 (by rfl) ⟨264677, by rfl⟩ : syracuseStep 352903 = 529355) B529355
theorem B352911 : Blo 350755 352911 := bstep (se 1 (by rfl) ⟨264683, by rfl⟩ : syracuseStep 352911 = 529367) B529367
theorem B352955 : Blo 350755 352955 := bstep (se 1 (by rfl) ⟨264716, by rfl⟩ : syracuseStep 352955 = 529433) B529433
theorem B1794797 : Blo 350755 1794797 := bstep (se 3 (by rfl) ⟨336524, by rfl⟩ : syracuseStep 1794797 = 673049) B673049
theorem B353031 : Blo 350755 353031 := bstep (se 1 (by rfl) ⟨264773, by rfl⟩ : syracuseStep 353031 = 529547) B529547
theorem B353039 : Blo 350755 353039 := bstep (se 1 (by rfl) ⟨264779, by rfl⟩ : syracuseStep 353039 = 529559) B529559
theorem B1008413 : Blo 350755 1008413 := bstep (se 3 (by rfl) ⟨189077, by rfl⟩ : syracuseStep 1008413 = 378155) B378155
theorem B353083 : Blo 350755 353083 := bstep (se 1 (by rfl) ⟨264812, by rfl⟩ : syracuseStep 353083 = 529625) B529625
theorem B353159 : Blo 350755 353159 := bstep (se 1 (by rfl) ⟨264869, by rfl⟩ : syracuseStep 353159 = 529739) B529739
theorem B353167 : Blo 350755 353167 := bstep (se 1 (by rfl) ⟨264875, by rfl⟩ : syracuseStep 353167 = 529751) B529751
theorem B353211 : Blo 350755 353211 := bstep (se 1 (by rfl) ⟨264908, by rfl⟩ : syracuseStep 353211 = 529817) B529817
theorem B353287 : Blo 350755 353287 := bstep (se 1 (by rfl) ⟨264965, by rfl⟩ : syracuseStep 353287 = 529931) B529931
theorem B353295 : Blo 350755 353295 := bstep (se 1 (by rfl) ⟨264971, by rfl⟩ : syracuseStep 353295 = 529943) B529943
theorem B353339 : Blo 350755 353339 := bstep (se 1 (by rfl) ⟨265004, by rfl⟩ : syracuseStep 353339 = 530009) B530009
theorem B1336439 : Blo 350755 1336439 := bstep (se 1 (by rfl) ⟨1002329, by rfl⟩ : syracuseStep 1336439 = 2004659) B2004659
theorem B353415 : Blo 350755 353415 := bstep (se 1 (by rfl) ⟨265061, by rfl⟩ : syracuseStep 353415 = 530123) B530123
theorem B353423 : Blo 350755 353423 := bstep (se 1 (by rfl) ⟨265067, by rfl⟩ : syracuseStep 353423 = 530135) B530135
theorem B353467 : Blo 350755 353467 := bstep (se 1 (by rfl) ⟨265100, by rfl⟩ : syracuseStep 353467 = 530201) B530201
theorem B353543 : Blo 350755 353543 := bstep (se 1 (by rfl) ⟨265157, by rfl⟩ : syracuseStep 353543 = 530315) B530315
theorem B353551 : Blo 350755 353551 := bstep (se 1 (by rfl) ⟨265163, by rfl⟩ : syracuseStep 353551 = 530327) B530327
theorem B16442657 : Blo 350755 16442657 := bstep (se 2 (by rfl) ⟨6165996, by rfl⟩ : syracuseStep 16442657 = 12331993) B12331993
theorem B353595 : Blo 350755 353595 := bstep (se 1 (by rfl) ⟨265196, by rfl⟩ : syracuseStep 353595 = 530393) B530393
theorem B3433859 : Blo 350755 3433859 := bstep (se 1 (by rfl) ⟨2575394, by rfl⟩ : syracuseStep 3433859 = 5150789) B5150789
theorem B353671 : Blo 350755 353671 := bstep (se 1 (by rfl) ⟨265253, by rfl⟩ : syracuseStep 353671 = 530507) B530507
theorem B353679 : Blo 350755 353679 := bstep (se 1 (by rfl) ⟨265259, by rfl⟩ : syracuseStep 353679 = 530519) B530519
theorem B353723 : Blo 350755 353723 := bstep (se 1 (by rfl) ⟨265292, by rfl⟩ : syracuseStep 353723 = 530585) B530585
theorem B353799 : Blo 350755 353799 := bstep (se 1 (by rfl) ⟨265349, by rfl⟩ : syracuseStep 353799 = 530699) B530699
theorem B353807 : Blo 350755 353807 := bstep (se 1 (by rfl) ⟨265355, by rfl⟩ : syracuseStep 353807 = 530711) B530711
theorem B1795607 : Blo 350755 1795607 := bstep (se 1 (by rfl) ⟨1346705, by rfl⟩ : syracuseStep 1795607 = 2693411) B2693411
theorem B353851 : Blo 350755 353851 := bstep (se 1 (by rfl) ⟨265388, by rfl⟩ : syracuseStep 353851 = 530777) B530777
theorem B353927 : Blo 350755 353927 := bstep (se 1 (by rfl) ⟨265445, by rfl⟩ : syracuseStep 353927 = 530891) B530891
theorem B353935 : Blo 350755 353935 := bstep (se 1 (by rfl) ⟨265451, by rfl⟩ : syracuseStep 353935 = 530903) B530903
theorem B353979 : Blo 350755 353979 := bstep (se 1 (by rfl) ⟨265484, by rfl⟩ : syracuseStep 353979 = 530969) B530969
theorem B354055 : Blo 350755 354055 := bstep (se 1 (by rfl) ⟨265541, by rfl⟩ : syracuseStep 354055 = 531083) B531083
theorem B4024079 : Blo 350755 4024079 := bstep (se 1 (by rfl) ⟨3018059, by rfl⟩ : syracuseStep 4024079 = 6036119) B6036119
theorem B354063 : Blo 350755 354063 := bstep (se 1 (by rfl) ⟨265547, by rfl⟩ : syracuseStep 354063 = 531095) B531095
theorem B354107 : Blo 350755 354107 := bstep (se 1 (by rfl) ⟨265580, by rfl⟩ : syracuseStep 354107 = 531161) B531161
theorem B2582387 : Blo 350755 2582387 := bstep (se 1 (by rfl) ⟨1936790, by rfl⟩ : syracuseStep 2582387 = 3873581) B3873581
theorem B1075079 : Blo 350755 1075079 := bstep (se 1 (by rfl) ⟨806309, by rfl⟩ : syracuseStep 1075079 = 1612619) B1612619
theorem B354183 : Blo 350755 354183 := bstep (se 1 (by rfl) ⟨265637, by rfl⟩ : syracuseStep 354183 = 531275) B531275
theorem B354191 : Blo 350755 354191 := bstep (se 1 (by rfl) ⟨265643, by rfl⟩ : syracuseStep 354191 = 531287) B531287
theorem B4646807 : Blo 350755 4646807 := bstep (se 1 (by rfl) ⟨3485105, by rfl⟩ : syracuseStep 4646807 = 6970211) B6970211
theorem B354235 : Blo 350755 354235 := bstep (se 1 (by rfl) ⟨265676, by rfl⟩ : syracuseStep 354235 = 531353) B531353
theorem B354311 : Blo 350755 354311 := bstep (se 1 (by rfl) ⟨265733, by rfl⟩ : syracuseStep 354311 = 531467) B531467
theorem B354319 : Blo 350755 354319 := bstep (se 1 (by rfl) ⟨265739, by rfl⟩ : syracuseStep 354319 = 531479) B531479
theorem B354363 : Blo 350755 354363 := bstep (se 1 (by rfl) ⟨265772, by rfl⟩ : syracuseStep 354363 = 531545) B531545
theorem B1337411 : Blo 350755 1337411 := bstep (se 1 (by rfl) ⟨1003058, by rfl⟩ : syracuseStep 1337411 = 2006117) B2006117
theorem B10152053 : Blo 350755 10152053 := bstep (se 5 (by rfl) ⟨475877, by rfl⟩ : syracuseStep 10152053 = 951755) B951755
theorem B6514805 : Blo 350755 6514805 := bstep (se 5 (by rfl) ⟨305381, by rfl⟩ : syracuseStep 6514805 = 610763) B610763
theorem B354439 : Blo 350755 354439 := bstep (se 1 (by rfl) ⟨265829, by rfl⟩ : syracuseStep 354439 = 531659) B531659
theorem B354447 : Blo 350755 354447 := bstep (se 1 (by rfl) ⟨265835, by rfl⟩ : syracuseStep 354447 = 531671) B531671
theorem B845977 : Blo 350755 845977 := bstep (se 2 (by rfl) ⟨317241, by rfl⟩ : syracuseStep 845977 = 634483) B634483
theorem B354491 : Blo 350755 354491 := bstep (se 1 (by rfl) ⟨265868, by rfl⟩ : syracuseStep 354491 = 531737) B531737
theorem B354567 : Blo 350755 354567 := bstep (se 1 (by rfl) ⟨265925, by rfl⟩ : syracuseStep 354567 = 531851) B531851
theorem B354575 : Blo 350755 354575 := bstep (se 1 (by rfl) ⟨265931, by rfl⟩ : syracuseStep 354575 = 531863) B531863
theorem B846139 : Blo 350755 846139 := bstep (se 1 (by rfl) ⟨634604, by rfl⟩ : syracuseStep 846139 = 1269209) B1269209
theorem B354619 : Blo 350755 354619 := bstep (se 1 (by rfl) ⟨265964, by rfl⟩ : syracuseStep 354619 = 531929) B531929
theorem B354695 : Blo 350755 354695 := bstep (se 1 (by rfl) ⟨266021, by rfl⟩ : syracuseStep 354695 = 532043) B532043
theorem B354703 : Blo 350755 354703 := bstep (se 1 (by rfl) ⟨266027, by rfl⟩ : syracuseStep 354703 = 532055) B532055
theorem B354747 : Blo 350755 354747 := bstep (se 1 (by rfl) ⟨266060, by rfl⟩ : syracuseStep 354747 = 532121) B532121
theorem B1501649 : Blo 350755 1501649 := bstep (se 2 (by rfl) ⟨563118, by rfl⟩ : syracuseStep 1501649 = 1126237) B1126237
theorem B1337867 : Blo 350755 1337867 := bstep (se 1 (by rfl) ⟨1003400, by rfl⟩ : syracuseStep 1337867 = 2006801) B2006801
theorem B1535441 : Blo 350755 1535441 := bstep (se 2 (by rfl) ⟨575790, by rfl⟩ : syracuseStep 1535441 = 1151581) B1151581
theorem B847361 : Blo 350755 847361 := bstep (se 2 (by rfl) ⟨317760, by rfl⟩ : syracuseStep 847361 = 635521) B635521
theorem B1274429 : Blo 350755 1274429 := bstep (se 3 (by rfl) ⟨238955, by rfl⟩ : syracuseStep 1274429 = 477911) B477911
theorem B1340023 : Blo 350755 1340023 := bstep (se 1 (by rfl) ⟨1005017, by rfl⟩ : syracuseStep 1340023 = 2010035) B2010035
theorem B1078049 : Blo 350755 1078049 := bstep (se 2 (by rfl) ⟨404268, by rfl⟩ : syracuseStep 1078049 = 808537) B808537
theorem B423031 : Blo 350755 423031 := bstep (se 1 (by rfl) ⟨317273, by rfl⟩ : syracuseStep 423031 = 634547) B634547
theorem B1701121 : Blo 350755 1701121 := bstep (se 2 (by rfl) ⟨637920, by rfl⟩ : syracuseStep 1701121 = 1275841) B1275841
theorem B1340995 : Blo 350755 1340995 := bstep (se 1 (by rfl) ⟨1005746, by rfl⟩ : syracuseStep 1340995 = 2011493) B2011493
theorem B1144439 : Blo 350755 1144439 := bstep (se 1 (by rfl) ⟨858329, by rfl⟩ : syracuseStep 1144439 = 1716659) B1716659
theorem B3012389 : Blo 350755 3012389 := bstep (se 4 (by rfl) ⟨282411, by rfl⟩ : syracuseStep 3012389 = 564823) B564823
theorem B11401073 : Blo 350755 11401073 := bstep (se 2 (by rfl) ⟨4275402, by rfl⟩ : syracuseStep 11401073 = 8550805) B8550805
theorem B1341299 : Blo 350755 1341299 := bstep (se 1 (by rfl) ⟨1005974, by rfl⟩ : syracuseStep 1341299 = 2011949) B2011949
theorem B1964119 : Blo 350755 1964119 := bstep (se 1 (by rfl) ⟨1473089, by rfl⟩ : syracuseStep 1964119 = 2946179) B2946179
theorem B1341755 : Blo 350755 1341755 := bstep (se 1 (by rfl) ⟨1006316, by rfl⟩ : syracuseStep 1341755 = 2012633) B2012633
theorem B3373447 : Blo 350755 3373447 := bstep (se 1 (by rfl) ⟨2530085, by rfl⟩ : syracuseStep 3373447 = 5060171) B5060171
theorem B1210777 : Blo 350755 1210777 := bstep (se 2 (by rfl) ⟨454041, by rfl⟩ : syracuseStep 1210777 = 908083) B908083
theorem B3996377 : Blo 350755 3996377 := bstep (se 2 (by rfl) ⟨1498641, by rfl⟩ : syracuseStep 3996377 = 2997283) B2997283
theorem B916235 : Blo 350755 916235 := bstep (se 1 (by rfl) ⟨687176, by rfl⟩ : syracuseStep 916235 = 1374353) B1374353
theorem B1342241 : Blo 350755 1342241 := bstep (se 2 (by rfl) ⟨503340, by rfl⟩ : syracuseStep 1342241 = 1006681) B1006681
theorem B850945 : Blo 350755 850945 := bstep (se 2 (by rfl) ⟨319104, by rfl⟩ : syracuseStep 850945 = 638209) B638209
theorem B1998053 : Blo 350755 1998053 := bstep (se 4 (by rfl) ⟨187317, by rfl⟩ : syracuseStep 1998053 = 374635) B374635
theorem B1506707 : Blo 350755 1506707 := bstep (se 1 (by rfl) ⟨1130030, by rfl⟩ : syracuseStep 1506707 = 2260061) B2260061
theorem B1703389 : Blo 350755 1703389 := bstep (se 3 (by rfl) ⟨319385, by rfl⟩ : syracuseStep 1703389 = 638771) B638771
theorem B1900093 : Blo 350755 1900093 := bstep (se 3 (by rfl) ⟨356267, by rfl⟩ : syracuseStep 1900093 = 712535) B712535
theorem B1343213 : Blo 350755 1343213 := bstep (se 3 (by rfl) ⟨251852, by rfl⟩ : syracuseStep 1343213 = 503705) B503705
theorem B851897 : Blo 350755 851897 := bstep (se 2 (by rfl) ⟨319461, by rfl⟩ : syracuseStep 851897 = 638923) B638923
theorem B1344185 : Blo 350755 1344185 := bstep (se 2 (by rfl) ⟨504069, by rfl⟩ : syracuseStep 1344185 = 1008139) B1008139
theorem B1344215 : Blo 350755 1344215 := bstep (se 1 (by rfl) ⟨1008161, by rfl⟩ : syracuseStep 1344215 = 2016323) B2016323
theorem B2557099 : Blo 350755 2557099 := bstep (se 1 (by rfl) ⟨1917824, by rfl⟩ : syracuseStep 2557099 = 3835649) B3835649
theorem B4326857 : Blo 350755 4326857 := bstep (se 2 (by rfl) ⟨1622571, by rfl⟩ : syracuseStep 4326857 = 3245143) B3245143
theorem B2688551 : Blo 350755 2688551 := bstep (se 1 (by rfl) ⟨2016413, by rfl⟩ : syracuseStep 2688551 = 4032827) B4032827
theorem B3999293 : Blo 350755 3999293 := bstep (se 3 (by rfl) ⟨749867, by rfl⟩ : syracuseStep 3999293 = 1499735) B1499735
theorem B394951 : Blo 350755 394951 := bstep (se 1 (by rfl) ⟨296213, by rfl⟩ : syracuseStep 394951 = 592427) B592427
theorem B526175 : Blo 350755 526175 := bstep (se 1 (by rfl) ⟨394631, by rfl⟩ : syracuseStep 526175 = 789263) B789263
theorem B526187 : Blo 350755 526187 := bstep (se 1 (by rfl) ⟨394640, by rfl⟩ : syracuseStep 526187 = 789281) B789281
theorem B722875 : Blo 350755 722875 := bstep (se 1 (by rfl) ⟨542156, by rfl⟩ : syracuseStep 722875 = 1084313) B1084313
theorem B526415 : Blo 350755 526415 := bstep (se 1 (by rfl) ⟨394811, by rfl⟩ : syracuseStep 526415 = 789623) B789623
theorem B591995 : Blo 350755 591995 := bstep (se 1 (by rfl) ⟨443996, by rfl⟩ : syracuseStep 591995 = 887993) B887993
theorem B6457477 : Blo 350755 6457477 := bstep (se 4 (by rfl) ⟨605388, by rfl⟩ : syracuseStep 6457477 = 1210777) B1210777
theorem B526535 : Blo 350755 526535 := bstep (se 1 (by rfl) ⟨394901, by rfl⟩ : syracuseStep 526535 = 789803) B789803
theorem B526697 : Blo 350755 526697 := bstep (se 2 (by rfl) ⟨197511, by rfl⟩ : syracuseStep 526697 = 395023) B395023
theorem B723343 : Blo 350755 723343 := bstep (se 1 (by rfl) ⟨542507, by rfl⟩ : syracuseStep 723343 = 1085015) B1085015
theorem B526775 : Blo 350755 526775 := bstep (se 1 (by rfl) ⟨395081, by rfl⟩ : syracuseStep 526775 = 790163) B790163
theorem B526811 : Blo 350755 526811 := bstep (se 1 (by rfl) ⟨395108, by rfl⟩ : syracuseStep 526811 = 790217) B790217
theorem B592393 : Blo 350755 592393 := bstep (se 2 (by rfl) ⟨222147, by rfl⟩ : syracuseStep 592393 = 444295) B444295
theorem B395815 : Blo 350755 395815 := bstep (se 1 (by rfl) ⟨296861, by rfl⟩ : syracuseStep 395815 = 593723) B593723
theorem B592555 : Blo 350755 592555 := bstep (se 1 (by rfl) ⟨444416, by rfl⟩ : syracuseStep 592555 = 888833) B888833
theorem B527279 : Blo 350755 527279 := bstep (se 1 (by rfl) ⟨395459, by rfl⟩ : syracuseStep 527279 = 790919) B790919
theorem B592859 : Blo 350755 592859 := bstep (se 1 (by rfl) ⟨444644, by rfl⟩ : syracuseStep 592859 = 889289) B889289
theorem B527369 : Blo 350755 527369 := bstep (se 2 (by rfl) ⟨197763, by rfl⟩ : syracuseStep 527369 = 395527) B395527
theorem B527399 : Blo 350755 527399 := bstep (se 1 (by rfl) ⟨395549, by rfl⟩ : syracuseStep 527399 = 791099) B791099
theorem B527483 : Blo 350755 527483 := bstep (se 1 (by rfl) ⟨395612, by rfl⟩ : syracuseStep 527483 = 791225) B791225
theorem B5049539 : Blo 350755 5049539 := bstep (se 1 (by rfl) ⟨3787154, by rfl⟩ : syracuseStep 5049539 = 7574309) B7574309
theorem B593095 : Blo 350755 593095 := bstep (se 1 (by rfl) ⟨444821, by rfl⟩ : syracuseStep 593095 = 889643) B889643
theorem B3214583 : Blo 350755 3214583 := bstep (se 1 (by rfl) ⟨2410937, by rfl⟩ : syracuseStep 3214583 = 4821875) B4821875
theorem B527609 : Blo 350755 527609 := bstep (se 2 (by rfl) ⟨197853, by rfl⟩ : syracuseStep 527609 = 395707) B395707
theorem B1346827 : Blo 350755 1346827 := bstep (se 1 (by rfl) ⟨1010120, by rfl⟩ : syracuseStep 1346827 = 2020241) B2020241
theorem B527711 : Blo 350755 527711 := bstep (se 1 (by rfl) ⟨395783, by rfl⟩ : syracuseStep 527711 = 791567) B791567
theorem B593257 : Blo 350755 593257 := bstep (se 2 (by rfl) ⟨222471, by rfl⟩ : syracuseStep 593257 = 444943) B444943
theorem B527723 : Blo 350755 527723 := bstep (se 1 (by rfl) ⟨395792, by rfl⟩ : syracuseStep 527723 = 791585) B791585
theorem B1019279 : Blo 350755 1019279 := bstep (se 1 (by rfl) ⟨764459, by rfl⟩ : syracuseStep 1019279 = 1528919) B1528919
theorem B790055 : Blo 350755 790055 := bstep (se 1 (by rfl) ⟨592541, by rfl⟩ : syracuseStep 790055 = 1185083) B1185083
theorem B527951 : Blo 350755 527951 := bstep (se 1 (by rfl) ⟨395963, by rfl⟩ : syracuseStep 527951 = 791927) B791927
theorem B528071 : Blo 350755 528071 := bstep (se 1 (by rfl) ⟨396053, by rfl⟩ : syracuseStep 528071 = 792107) B792107
theorem B4034285 : Blo 350755 4034285 := bstep (se 3 (by rfl) ⟨756428, by rfl⟩ : syracuseStep 4034285 = 1512857) B1512857
theorem B888671 : Blo 350755 888671 := bstep (se 1 (by rfl) ⟨666503, by rfl⟩ : syracuseStep 888671 = 1333007) B1333007
theorem B528233 : Blo 350755 528233 := bstep (se 2 (by rfl) ⟨198087, by rfl⟩ : syracuseStep 528233 = 396175) B396175
theorem B790379 : Blo 350755 790379 := bstep (se 1 (by rfl) ⟨592784, by rfl⟩ : syracuseStep 790379 = 1185569) B1185569
theorem B790433 : Blo 350755 790433 := bstep (se 2 (by rfl) ⟨296412, by rfl⟩ : syracuseStep 790433 = 592825) B592825
theorem B528311 : Blo 350755 528311 := bstep (se 1 (by rfl) ⟨396233, by rfl⟩ : syracuseStep 528311 = 792467) B792467
theorem B593851 : Blo 350755 593851 := bstep (se 1 (by rfl) ⟨445388, by rfl⟩ : syracuseStep 593851 = 890777) B890777
theorem B528347 : Blo 350755 528347 := bstep (se 1 (by rfl) ⟨396260, by rfl⟩ : syracuseStep 528347 = 792521) B792521
theorem B13111307 : Blo 350755 13111307 := bstep (se 1 (by rfl) ⟨9833480, by rfl⟩ : syracuseStep 13111307 = 19666961) B19666961
theorem B593959 : Blo 350755 593959 := bstep (se 1 (by rfl) ⟨445469, by rfl⟩ : syracuseStep 593959 = 890939) B890939
theorem B397435 : Blo 350755 397435 := bstep (se 1 (by rfl) ⟨298076, by rfl⟩ : syracuseStep 397435 = 596153) B596153
theorem B790775 : Blo 350755 790775 := bstep (se 1 (by rfl) ⟨593081, by rfl⟩ : syracuseStep 790775 = 1186163) B1186163
theorem B594283 : Blo 350755 594283 := bstep (se 1 (by rfl) ⟨445712, by rfl⟩ : syracuseStep 594283 = 891425) B891425
theorem B528815 : Blo 350755 528815 := bstep (se 1 (by rfl) ⟨396611, by rfl⟩ : syracuseStep 528815 = 793223) B793223
theorem B1184219 : Blo 350755 1184219 := bstep (se 1 (by rfl) ⟨888164, by rfl⟩ : syracuseStep 1184219 = 1776329) B1776329
theorem B528905 : Blo 350755 528905 := bstep (se 2 (by rfl) ⟨198339, by rfl⟩ : syracuseStep 528905 = 396679) B396679
theorem B528935 : Blo 350755 528935 := bstep (se 1 (by rfl) ⟨396701, by rfl⟩ : syracuseStep 528935 = 793403) B793403
theorem B397903 : Blo 350755 397903 := bstep (se 1 (by rfl) ⟨298427, by rfl⟩ : syracuseStep 397903 = 596855) B596855
theorem B856673 : Blo 350755 856673 := bstep (se 2 (by rfl) ⟨321252, by rfl⟩ : syracuseStep 856673 = 642505) B642505
theorem B529019 : Blo 350755 529019 := bstep (se 1 (by rfl) ⟨396764, by rfl⟩ : syracuseStep 529019 = 793529) B793529
theorem B561863 : Blo 350755 561863 := bstep (se 1 (by rfl) ⟨421397, by rfl⟩ : syracuseStep 561863 = 842795) B842795
theorem B529145 : Blo 350755 529145 := bstep (se 2 (by rfl) ⟨198429, by rfl⟩ : syracuseStep 529145 = 396859) B396859
theorem B791369 : Blo 350755 791369 := bstep (se 2 (by rfl) ⟨296763, by rfl⟩ : syracuseStep 791369 = 593527) B593527
theorem B529247 : Blo 350755 529247 := bstep (se 1 (by rfl) ⟨396935, by rfl⟩ : syracuseStep 529247 = 793871) B793871
theorem B529259 : Blo 350755 529259 := bstep (se 1 (by rfl) ⟨396944, by rfl⟩ : syracuseStep 529259 = 793889) B793889
theorem B889775 : Blo 350755 889775 := bstep (se 1 (by rfl) ⟨667331, by rfl⟩ : syracuseStep 889775 = 1334663) B1334663
theorem B398299 : Blo 350755 398299 := bstep (se 1 (by rfl) ⟨298724, by rfl⟩ : syracuseStep 398299 = 597449) B597449
theorem B529487 : Blo 350755 529487 := bstep (se 1 (by rfl) ⟨397115, by rfl⟩ : syracuseStep 529487 = 794231) B794231
theorem B1184921 : Blo 350755 1184921 := bstep (se 2 (by rfl) ⟨444345, by rfl⟩ : syracuseStep 1184921 = 888691) B888691
theorem B529607 : Blo 350755 529607 := bstep (se 1 (by rfl) ⟨397205, by rfl⟩ : syracuseStep 529607 = 794411) B794411
theorem B8295695 : Blo 350755 8295695 := bstep (se 1 (by rfl) ⟨6221771, by rfl⟩ : syracuseStep 8295695 = 12443543) B12443543
theorem B529769 : Blo 350755 529769 := bstep (se 2 (by rfl) ⟨198663, by rfl⟩ : syracuseStep 529769 = 397327) B397327
theorem B595343 : Blo 350755 595343 := bstep (se 1 (by rfl) ⟨446507, by rfl⟩ : syracuseStep 595343 = 893015) B893015
theorem B398767 : Blo 350755 398767 := bstep (se 1 (by rfl) ⟨299075, by rfl⟩ : syracuseStep 398767 = 598151) B598151
theorem B529847 : Blo 350755 529847 := bstep (se 1 (by rfl) ⟨397385, by rfl⟩ : syracuseStep 529847 = 794771) B794771
theorem B529883 : Blo 350755 529883 := bstep (se 1 (by rfl) ⟨397412, by rfl⟩ : syracuseStep 529883 = 794825) B794825
theorem B792161 : Blo 350755 792161 := bstep (se 2 (by rfl) ⟨297060, by rfl⟩ : syracuseStep 792161 = 594121) B594121
theorem B595579 : Blo 350755 595579 := bstep (se 1 (by rfl) ⟨446684, by rfl⟩ : syracuseStep 595579 = 893369) B893369
theorem B530351 : Blo 350755 530351 := bstep (se 1 (by rfl) ⟨397763, by rfl⟩ : syracuseStep 530351 = 795527) B795527
theorem B792503 : Blo 350755 792503 := bstep (se 1 (by rfl) ⟨594377, by rfl⟩ : syracuseStep 792503 = 1188755) B1188755
theorem B530441 : Blo 350755 530441 := bstep (se 2 (by rfl) ⟨198915, by rfl⟩ : syracuseStep 530441 = 397831) B397831
theorem B530471 : Blo 350755 530471 := bstep (se 1 (by rfl) ⟨397853, by rfl⟩ : syracuseStep 530471 = 795707) B795707
theorem B890959 : Blo 350755 890959 := bstep (se 1 (by rfl) ⟨668219, by rfl⟩ : syracuseStep 890959 = 1336439) B1336439
theorem B530555 : Blo 350755 530555 := bstep (se 1 (by rfl) ⟨397916, by rfl⟩ : syracuseStep 530555 = 795833) B795833
theorem B530681 : Blo 350755 530681 := bstep (se 2 (by rfl) ⟨199005, by rfl⟩ : syracuseStep 530681 = 398011) B398011
theorem B1186109 : Blo 350755 1186109 := bstep (se 3 (by rfl) ⟨222395, by rfl⟩ : syracuseStep 1186109 = 444791) B444791
theorem B530783 : Blo 350755 530783 := bstep (se 1 (by rfl) ⟨398087, by rfl⟩ : syracuseStep 530783 = 796175) B796175
theorem B530795 : Blo 350755 530795 := bstep (se 1 (by rfl) ⟨398096, by rfl⟩ : syracuseStep 530795 = 796193) B796193
theorem B596443 : Blo 350755 596443 := bstep (se 1 (by rfl) ⟨447332, by rfl⟩ : syracuseStep 596443 = 894665) B894665
theorem B793097 : Blo 350755 793097 := bstep (se 2 (by rfl) ⟨297411, by rfl⟩ : syracuseStep 793097 = 594823) B594823
theorem B531023 : Blo 350755 531023 := bstep (se 1 (by rfl) ⟨398267, by rfl⟩ : syracuseStep 531023 = 796535) B796535
theorem B531143 : Blo 350755 531143 := bstep (se 1 (by rfl) ⟨398357, by rfl⟩ : syracuseStep 531143 = 796715) B796715
theorem B891607 : Blo 350755 891607 := bstep (se 1 (by rfl) ⟨668705, by rfl⟩ : syracuseStep 891607 = 1337411) B1337411
theorem B564041 : Blo 350755 564041 := bstep (se 2 (by rfl) ⟨211515, by rfl⟩ : syracuseStep 564041 = 423031) B423031
theorem B793439 : Blo 350755 793439 := bstep (se 1 (by rfl) ⟨595079, by rfl⟩ : syracuseStep 793439 = 1190159) B1190159
theorem B531305 : Blo 350755 531305 := bstep (se 2 (by rfl) ⟨199239, by rfl⟩ : syracuseStep 531305 = 398479) B398479
theorem B1776491 : Blo 350755 1776491 := bstep (se 1 (by rfl) ⟨1332368, by rfl⟩ : syracuseStep 1776491 = 2664737) B2664737
theorem B531383 : Blo 350755 531383 := bstep (se 1 (by rfl) ⟨398537, by rfl⟩ : syracuseStep 531383 = 797075) B797075
theorem B531419 : Blo 350755 531419 := bstep (se 1 (by rfl) ⟨398564, by rfl⟩ : syracuseStep 531419 = 797129) B797129
theorem B2268161 : Blo 350755 2268161 := bstep (se 2 (by rfl) ⟨850560, by rfl⟩ : syracuseStep 2268161 = 1701121) B1701121
theorem B891911 : Blo 350755 891911 := bstep (se 1 (by rfl) ⟨668933, by rfl⟩ : syracuseStep 891911 = 1337867) B1337867
theorem B793619 : Blo 350755 793619 := bstep (se 1 (by rfl) ⟨595214, by rfl⟩ : syracuseStep 793619 = 1190429) B1190429
theorem B597071 : Blo 350755 597071 := bstep (se 1 (by rfl) ⟨447803, by rfl⟩ : syracuseStep 597071 = 895607) B895607
theorem B1186973 : Blo 350755 1186973 := bstep (se 3 (by rfl) ⟨222557, by rfl⟩ : syracuseStep 1186973 = 445115) B445115
theorem B4300121 : Blo 350755 4300121 := bstep (se 2 (by rfl) ⟨1612545, by rfl⟩ : syracuseStep 4300121 = 3225091) B3225091
theorem B793961 : Blo 350755 793961 := bstep (se 2 (by rfl) ⟨297735, by rfl⟩ : syracuseStep 793961 = 595471) B595471
theorem B531887 : Blo 350755 531887 := bstep (se 1 (by rfl) ⟨398915, by rfl⟩ : syracuseStep 531887 = 797831) B797831
theorem B1777139 : Blo 350755 1777139 := bstep (se 1 (by rfl) ⟨1332854, by rfl⟩ : syracuseStep 1777139 = 2665709) B2665709
theorem B531977 : Blo 350755 531977 := bstep (se 2 (by rfl) ⟨199491, by rfl⟩ : syracuseStep 531977 = 398983) B398983
theorem B532007 : Blo 350755 532007 := bstep (se 1 (by rfl) ⟨399005, by rfl⟩ : syracuseStep 532007 = 798011) B798011
theorem B532091 : Blo 350755 532091 := bstep (se 1 (by rfl) ⟨399068, by rfl⟩ : syracuseStep 532091 = 798137) B798137
theorem B564907 : Blo 350755 564907 := bstep (se 1 (by rfl) ⟨423680, by rfl⟩ : syracuseStep 564907 = 847361) B847361
theorem B1187513 : Blo 350755 1187513 := bstep (se 2 (by rfl) ⟨445317, by rfl⟩ : syracuseStep 1187513 = 890635) B890635
theorem B597935 : Blo 350755 597935 := bstep (se 1 (by rfl) ⟨448451, by rfl⟩ : syracuseStep 597935 = 896903) B896903
theorem B794555 : Blo 350755 794555 := bstep (se 1 (by rfl) ⟨595916, by rfl⟩ : syracuseStep 794555 = 1191833) B1191833
theorem B794681 : Blo 350755 794681 := bstep (se 2 (by rfl) ⟨298005, by rfl⟩ : syracuseStep 794681 = 596011) B596011
theorem B1188107 : Blo 350755 1188107 := bstep (se 1 (by rfl) ⟨891080, by rfl⟩ : syracuseStep 1188107 = 1782161) B1782161
theorem B598367 : Blo 350755 598367 := bstep (se 1 (by rfl) ⟨448775, by rfl⟩ : syracuseStep 598367 = 897551) B897551
theorem B795023 : Blo 350755 795023 := bstep (se 1 (by rfl) ⟨596267, by rfl⟩ : syracuseStep 795023 = 1192535) B1192535
theorem B4497929 : Blo 350755 4497929 := bstep (se 2 (by rfl) ⟨1686723, by rfl⟩ : syracuseStep 4497929 = 3373447) B3373447
theorem B1188377 : Blo 350755 1188377 := bstep (se 2 (by rfl) ⟨445641, by rfl⟩ : syracuseStep 1188377 = 891283) B891283
theorem B1450631 : Blo 350755 1450631 := bstep (se 1 (by rfl) ⟨1087973, by rfl⟩ : syracuseStep 1450631 = 2175947) B2175947
theorem B795347 : Blo 350755 795347 := bstep (se 1 (by rfl) ⟨596510, by rfl⟩ : syracuseStep 795347 = 1193021) B1193021
theorem B1778435 : Blo 350755 1778435 := bstep (se 1 (by rfl) ⟨1333826, by rfl⟩ : syracuseStep 1778435 = 2667653) B2667653
theorem B4301585 : Blo 350755 4301585 := bstep (se 2 (by rfl) ⟨1613094, by rfl⟩ : syracuseStep 4301585 = 3226189) B3226189
theorem B762959 : Blo 350755 762959 := bstep (se 1 (by rfl) ⟨572219, by rfl⟩ : syracuseStep 762959 = 1144439) B1144439
theorem B2008259 : Blo 350755 2008259 := bstep (se 1 (by rfl) ⟨1506194, by rfl⟩ : syracuseStep 2008259 = 3012389) B3012389
theorem B894199 : Blo 350755 894199 := bstep (se 1 (by rfl) ⟨670649, by rfl⟩ : syracuseStep 894199 = 1341299) B1341299
theorem B6759881 : Blo 350755 6759881 := bstep (se 2 (by rfl) ⟨2534955, by rfl⟩ : syracuseStep 6759881 = 5069911) B5069911
theorem B894473 : Blo 350755 894473 := bstep (se 2 (by rfl) ⟨335427, by rfl⟩ : syracuseStep 894473 = 670855) B670855
theorem B894503 : Blo 350755 894503 := bstep (se 1 (by rfl) ⟨670877, by rfl⟩ : syracuseStep 894503 = 1341755) B1341755
theorem B796283 : Blo 350755 796283 := bstep (se 1 (by rfl) ⟨597212, by rfl⟩ : syracuseStep 796283 = 1194425) B1194425
theorem B1189511 : Blo 350755 1189511 := bstep (se 1 (by rfl) ⟨892133, by rfl⟩ : syracuseStep 1189511 = 1784267) B1784267
theorem B1189565 : Blo 350755 1189565 := bstep (se 3 (by rfl) ⟨223043, by rfl⟩ : syracuseStep 1189565 = 446087) B446087
theorem B796409 : Blo 350755 796409 := bstep (se 2 (by rfl) ⟨298653, by rfl⟩ : syracuseStep 796409 = 597307) B597307
theorem B2664251 : Blo 350755 2664251 := bstep (se 1 (by rfl) ⟨1998188, by rfl⟩ : syracuseStep 2664251 = 3996377) B3996377
theorem B1189727 : Blo 350755 1189727 := bstep (se 1 (by rfl) ⟨892295, by rfl⟩ : syracuseStep 1189727 = 1784591) B1784591
theorem B894827 : Blo 350755 894827 := bstep (se 1 (by rfl) ⟨671120, by rfl⟩ : syracuseStep 894827 = 1342241) B1342241
theorem B1288045 : Blo 350755 1288045 := bstep (se 3 (by rfl) ⟨241508, by rfl⟩ : syracuseStep 1288045 = 483017) B483017
theorem B2271185 : Blo 350755 2271185 := bstep (se 2 (by rfl) ⟨851694, by rfl⟩ : syracuseStep 2271185 = 1703389) B1703389
theorem B1189889 : Blo 350755 1189889 := bstep (se 2 (by rfl) ⟨446208, by rfl⟩ : syracuseStep 1189889 = 892417) B892417
theorem B796679 : Blo 350755 796679 := bstep (se 1 (by rfl) ⟨597509, by rfl⟩ : syracuseStep 796679 = 1195019) B1195019
theorem B796751 : Blo 350755 796751 := bstep (se 1 (by rfl) ⟨597563, by rfl⟩ : syracuseStep 796751 = 1195127) B1195127
theorem B2533457 : Blo 350755 2533457 := bstep (se 2 (by rfl) ⟨950046, by rfl⟩ : syracuseStep 2533457 = 1900093) B1900093
theorem B600313 : Blo 350755 600313 := bstep (se 2 (by rfl) ⟨225117, by rfl⟩ : syracuseStep 600313 = 450235) B450235
theorem B1780055 : Blo 350755 1780055 := bstep (se 1 (by rfl) ⟨1335041, by rfl⟩ : syracuseStep 1780055 = 2670083) B2670083
theorem B797147 : Blo 350755 797147 := bstep (se 1 (by rfl) ⟨597860, by rfl⟩ : syracuseStep 797147 = 1195721) B1195721
theorem B2271725 : Blo 350755 2271725 := bstep (se 3 (by rfl) ⟨425948, by rfl⟩ : syracuseStep 2271725 = 851897) B851897
theorem B895475 : Blo 350755 895475 := bstep (se 1 (by rfl) ⟨671606, by rfl⟩ : syracuseStep 895475 = 1343213) B1343213
theorem B1190699 : Blo 350755 1190699 := bstep (se 1 (by rfl) ⟨893024, by rfl⟩ : syracuseStep 1190699 = 1786049) B1786049
theorem B797615 : Blo 350755 797615 := bstep (se 1 (by rfl) ⟨598211, by rfl⟩ : syracuseStep 797615 = 1196423) B1196423
theorem B895931 : Blo 350755 895931 := bstep (se 1 (by rfl) ⟨671948, by rfl⟩ : syracuseStep 895931 = 1343897) B1343897
theorem B1190969 : Blo 350755 1190969 := bstep (se 2 (by rfl) ⟨446613, by rfl⟩ : syracuseStep 1190969 = 893227) B893227
theorem B797867 : Blo 350755 797867 := bstep (se 1 (by rfl) ⟨598400, by rfl⟩ : syracuseStep 797867 = 1196801) B1196801
theorem B1191293 : Blo 350755 1191293 := bstep (se 3 (by rfl) ⟨223367, by rfl⟩ : syracuseStep 1191293 = 446735) B446735
theorem B896609 : Blo 350755 896609 := bstep (se 2 (by rfl) ⟨336228, by rfl⟩ : syracuseStep 896609 = 672457) B672457
theorem B1191563 : Blo 350755 1191563 := bstep (se 1 (by rfl) ⟨893672, by rfl⟩ : syracuseStep 1191563 = 1787345) B1787345
theorem B601847 : Blo 350755 601847 := bstep (se 1 (by rfl) ⟨451385, by rfl⟩ : syracuseStep 601847 = 902771) B902771
theorem B1126187 : Blo 350755 1126187 := bstep (se 1 (by rfl) ⟨844640, by rfl⟩ : syracuseStep 1126187 = 1689281) B1689281
theorem B1192481 : Blo 350755 1192481 := bstep (se 2 (by rfl) ⟨447180, by rfl⟩ : syracuseStep 1192481 = 894361) B894361
theorem B1192697 : Blo 350755 1192697 := bstep (se 2 (by rfl) ⟨447261, by rfl⟩ : syracuseStep 1192697 = 894523) B894523
theorem B602975 : Blo 350755 602975 := bstep (se 1 (by rfl) ⟨452231, by rfl⟩ : syracuseStep 602975 = 904463) B904463
theorem B635867 : Blo 350755 635867 := bstep (se 1 (by rfl) ⟨476900, by rfl⟩ : syracuseStep 635867 = 953801) B953801
theorem B4371421 : Blo 350755 4371421 := bstep (se 3 (by rfl) ⟨819641, by rfl⟩ : syracuseStep 4371421 = 1639283) B1639283
theorem B1192967 : Blo 350755 1192967 := bstep (se 1 (by rfl) ⟨894725, by rfl⟩ : syracuseStep 1192967 = 1789451) B1789451
theorem B668729 : Blo 350755 668729 := bstep (se 2 (by rfl) ⟨250773, by rfl⟩ : syracuseStep 668729 = 501547) B501547
theorem B2602063 : Blo 350755 2602063 := bstep (se 1 (by rfl) ⟨1951547, by rfl⟩ : syracuseStep 2602063 = 3903095) B3903095
theorem B1193075 : Blo 350755 1193075 := bstep (se 1 (by rfl) ⟨894806, by rfl⟩ : syracuseStep 1193075 = 1789613) B1789613
theorem B1193345 : Blo 350755 1193345 := bstep (se 2 (by rfl) ⟨447504, by rfl⟩ : syracuseStep 1193345 = 895009) B895009
theorem B6403475 : Blo 350755 6403475 := bstep (se 1 (by rfl) ⟨4802606, by rfl⟩ : syracuseStep 6403475 = 9605213) B9605213
theorem B4634003 : Blo 350755 4634003 := bstep (se 1 (by rfl) ⟨3475502, by rfl⟩ : syracuseStep 4634003 = 6951005) B6951005
theorem B1127969 : Blo 350755 1127969 := bstep (se 2 (by rfl) ⟨422988, by rfl⟩ : syracuseStep 1127969 = 845977) B845977
theorem B1128185 : Blo 350755 1128185 := bstep (se 2 (by rfl) ⟨423069, by rfl⟩ : syracuseStep 1128185 = 846139) B846139
theorem B1783619 : Blo 350755 1783619 := bstep (se 1 (by rfl) ⟨1337714, by rfl⟩ : syracuseStep 1783619 = 2675429) B2675429
theorem B1128287 : Blo 350755 1128287 := bstep (se 1 (by rfl) ⟨846215, by rfl⟩ : syracuseStep 1128287 = 1692431) B1692431
theorem B2668625 : Blo 350755 2668625 := bstep (se 2 (by rfl) ⟨1000734, by rfl⟩ : syracuseStep 2668625 = 2001469) B2001469
theorem B3815581 : Blo 350755 3815581 := bstep (se 3 (by rfl) ⟨715421, by rfl⟩ : syracuseStep 3815581 = 1430843) B1430843
theorem B1194155 : Blo 350755 1194155 := bstep (se 1 (by rfl) ⟨895616, by rfl⟩ : syracuseStep 1194155 = 1791233) B1791233
theorem B670331 : Blo 350755 670331 := bstep (se 1 (by rfl) ⟨502748, by rfl⟩ : syracuseStep 670331 = 1005497) B1005497
theorem B1194695 : Blo 350755 1194695 := bstep (se 1 (by rfl) ⟨896021, by rfl⟩ : syracuseStep 1194695 = 1792043) B1792043
theorem B539335 : Blo 350755 539335 := bstep (se 1 (by rfl) ⟨404501, by rfl⟩ : syracuseStep 539335 = 809003) B809003
theorem B1424087 : Blo 350755 1424087 := bstep (se 1 (by rfl) ⟨1068065, by rfl⟩ : syracuseStep 1424087 = 2136131) B2136131
theorem B9616157 : Blo 350755 9616157 := bstep (se 3 (by rfl) ⟨1803029, by rfl⟩ : syracuseStep 9616157 = 3606059) B3606059
theorem B1129403 : Blo 350755 1129403 := bstep (se 1 (by rfl) ⟨847052, by rfl⟩ : syracuseStep 1129403 = 1694105) B1694105
theorem B375887 : Blo 350755 375887 := bstep (se 1 (by rfl) ⟨281915, by rfl⟩ : syracuseStep 375887 = 563831) B563831
theorem B670817 : Blo 350755 670817 := bstep (se 2 (by rfl) ⟨251556, by rfl⟩ : syracuseStep 670817 = 503113) B503113
theorem B4602997 : Blo 350755 4602997 := bstep (se 5 (by rfl) ⟨215765, by rfl⟩ : syracuseStep 4602997 = 431531) B431531
theorem B409007 : Blo 350755 409007 := bstep (se 1 (by rfl) ⟨306755, by rfl⟩ : syracuseStep 409007 = 613511) B613511
theorem B671159 : Blo 350755 671159 := bstep (se 1 (by rfl) ⟨503369, by rfl⟩ : syracuseStep 671159 = 1006739) B1006739
theorem B1195559 : Blo 350755 1195559 := bstep (se 1 (by rfl) ⟨896669, by rfl⟩ : syracuseStep 1195559 = 1793339) B1793339
theorem B2014865 : Blo 350755 2014865 := bstep (se 2 (by rfl) ⟨755574, by rfl⟩ : syracuseStep 2014865 = 1511149) B1511149
theorem B1195667 : Blo 350755 1195667 := bstep (se 1 (by rfl) ⟨896750, by rfl⟩ : syracuseStep 1195667 = 1793501) B1793501
theorem B2866877 : Blo 350755 2866877 := bstep (se 3 (by rfl) ⟨537539, by rfl⟩ : syracuseStep 2866877 = 1075079) B1075079
theorem B671561 : Blo 350755 671561 := bstep (se 2 (by rfl) ⟨251835, by rfl⟩ : syracuseStep 671561 = 503671) B503671
theorem B1195883 : Blo 350755 1195883 := bstep (se 1 (by rfl) ⟨896912, by rfl⟩ : syracuseStep 1195883 = 1793825) B1793825
theorem B1195937 : Blo 350755 1195937 := bstep (se 2 (by rfl) ⟨448476, by rfl⟩ : syracuseStep 1195937 = 896953) B896953
theorem B2539457 : Blo 350755 2539457 := bstep (se 2 (by rfl) ⟨952296, by rfl⟩ : syracuseStep 2539457 = 1904593) B1904593
theorem B1818713 : Blo 350755 1818713 := bstep (se 2 (by rfl) ⟨682017, by rfl⟩ : syracuseStep 1818713 = 1364035) B1364035
theorem B2015549 : Blo 350755 2015549 := bstep (se 3 (by rfl) ⟨377915, by rfl⟩ : syracuseStep 2015549 = 755831) B755831
theorem B1196531 : Blo 350755 1196531 := bstep (se 1 (by rfl) ⟨897398, by rfl⟩ : syracuseStep 1196531 = 1794797) B1794797
theorem B672275 : Blo 350755 672275 := bstep (se 1 (by rfl) ⟨504206, by rfl⟩ : syracuseStep 672275 = 1008413) B1008413
theorem B672313 : Blo 350755 672313 := bstep (se 2 (by rfl) ⟨252117, by rfl⟩ : syracuseStep 672313 = 504235) B504235
theorem B1786697 : Blo 350755 1786697 := bstep (se 2 (by rfl) ⟨670011, by rfl⟩ : syracuseStep 1786697 = 1340023) B1340023
theorem B672617 : Blo 350755 672617 := bstep (se 2 (by rfl) ⟨252231, by rfl⟩ : syracuseStep 672617 = 504463) B504463
theorem B10961771 : Blo 350755 10961771 := bstep (se 1 (by rfl) ⟨8221328, by rfl⟩ : syracuseStep 10961771 = 16442657) B16442657
theorem B1360759 : Blo 350755 1360759 := bstep (se 1 (by rfl) ⟨1020569, by rfl⟩ : syracuseStep 1360759 = 2041139) B2041139
theorem B1197071 : Blo 350755 1197071 := bstep (se 1 (by rfl) ⟨897803, by rfl⟩ : syracuseStep 1197071 = 1795607) B1795607
theorem B1688627 : Blo 350755 1688627 := bstep (se 1 (by rfl) ⟨1266470, by rfl⟩ : syracuseStep 1688627 = 2532941) B2532941
theorem B1721591 : Blo 350755 1721591 := bstep (se 1 (by rfl) ⟨1291193, by rfl⟩ : syracuseStep 1721591 = 2582387) B2582387
theorem B3097871 : Blo 350755 3097871 := bstep (se 1 (by rfl) ⟨2323403, by rfl⟩ : syracuseStep 3097871 = 4646807) B4646807
theorem B6768035 : Blo 350755 6768035 := bstep (se 1 (by rfl) ⟨5076026, by rfl⟩ : syracuseStep 6768035 = 10152053) B10152053
theorem B4343203 : Blo 350755 4343203 := bstep (se 1 (by rfl) ⟨3257402, by rfl⟩ : syracuseStep 4343203 = 6514805) B6514805
theorem B1001099 : Blo 350755 1001099 := bstep (se 1 (by rfl) ⟨750824, by rfl⟩ : syracuseStep 1001099 = 1501649) B1501649
theorem B10208915 : Blo 350755 10208915 := bstep (se 1 (by rfl) ⟨7656686, by rfl⟩ : syracuseStep 10208915 = 15313373) B15313373
theorem B509915 : Blo 350755 509915 := bstep (se 1 (by rfl) ⟨382436, by rfl⟩ : syracuseStep 509915 = 764873) B764873
theorem B1787993 : Blo 350755 1787993 := bstep (se 2 (by rfl) ⟨670497, by rfl⟩ : syracuseStep 1787993 = 1340995) B1340995
theorem B1067393 : Blo 350755 1067393 := bstep (se 2 (by rfl) ⟨400272, by rfl⟩ : syracuseStep 1067393 = 800545) B800545
theorem B444847 : Blo 350755 444847 := bstep (se 1 (by rfl) ⟨333635, by rfl⟩ : syracuseStep 444847 = 667271) B667271
theorem B4344353 : Blo 350755 4344353 := bstep (se 2 (by rfl) ⟨1629132, by rfl⟩ : syracuseStep 4344353 = 3258265) B3258265
theorem B5491385 : Blo 350755 5491385 := bstep (se 2 (by rfl) ⟨2059269, by rfl⟩ : syracuseStep 5491385 = 4118539) B4118539
theorem B2214611 : Blo 350755 2214611 := bstep (se 1 (by rfl) ⟨1660958, by rfl⟩ : syracuseStep 2214611 = 3321917) B3321917
theorem B2673485 : Blo 350755 2673485 := bstep (se 3 (by rfl) ⟨501278, by rfl⟩ : syracuseStep 2673485 = 1002557) B1002557
theorem B2214839 : Blo 350755 2214839 := bstep (se 1 (by rfl) ⟨1661129, by rfl⟩ : syracuseStep 2214839 = 3322259) B3322259
theorem B445915 : Blo 350755 445915 := bstep (se 1 (by rfl) ⟨334436, by rfl⟩ : syracuseStep 445915 = 668873) B668873
theorem B10145357 : Blo 350755 10145357 := bstep (se 3 (by rfl) ⟨1902254, by rfl⟩ : syracuseStep 10145357 = 3804509) B3804509
theorem B1134593 : Blo 350755 1134593 := bstep (se 2 (by rfl) ⟨425472, by rfl⟩ : syracuseStep 1134593 = 850945) B850945
theorem B1626193 : Blo 350755 1626193 := bstep (se 2 (by rfl) ⟨609822, by rfl⟩ : syracuseStep 1626193 = 1219645) B1219645
theorem B610823 : Blo 350755 610823 := bstep (se 1 (by rfl) ⟨458117, by rfl⟩ : syracuseStep 610823 = 916235) B916235
theorem B11457125 : Blo 350755 11457125 := bstep (se 4 (by rfl) ⟨1074105, by rfl⟩ : syracuseStep 11457125 = 2148211) B2148211
theorem B1332035 : Blo 350755 1332035 := bstep (se 1 (by rfl) ⟨999026, by rfl⟩ : syracuseStep 1332035 = 1998053) B1998053
theorem B2544529 : Blo 350755 2544529 := bstep (se 2 (by rfl) ⟨954198, by rfl⟩ : syracuseStep 2544529 = 1908397) B1908397
theorem B1004471 : Blo 350755 1004471 := bstep (se 1 (by rfl) ⟨753353, by rfl⟩ : syracuseStep 1004471 = 1506707) B1506707
theorem B1692875 : Blo 350755 1692875 := bstep (se 1 (by rfl) ⟨1269656, by rfl⟩ : syracuseStep 1692875 = 2539313) B2539313
theorem B2675915 : Blo 350755 2675915 := bstep (se 1 (by rfl) ⟨2006936, by rfl⟩ : syracuseStep 2675915 = 4013873) B4013873
theorem B3200573 : Blo 350755 3200573 := bstep (se 3 (by rfl) ⟨600107, by rfl⟩ : syracuseStep 3200573 = 1200215) B1200215
theorem B743275 : Blo 350755 743275 := bstep (se 1 (by rfl) ⟨557456, by rfl⟩ : syracuseStep 743275 = 1114913) B1114913
theorem B2250605 : Blo 350755 2250605 := bstep (se 3 (by rfl) ⟨421988, by rfl⟩ : syracuseStep 2250605 = 843977) B843977
theorem B1005473 : Blo 350755 1005473 := bstep (se 2 (by rfl) ⟨377052, by rfl⟩ : syracuseStep 1005473 = 754105) B754105
theorem B1529761 : Blo 350755 1529761 := bstep (se 2 (by rfl) ⟨573660, by rfl⟩ : syracuseStep 1529761 = 1147321) B1147321
theorem B1300411 : Blo 350755 1300411 := bstep (se 1 (by rfl) ⟨975308, by rfl⟩ : syracuseStep 1300411 = 1950617) B1950617
theorem B1267883 : Blo 350755 1267883 := bstep (se 1 (by rfl) ⟨950912, by rfl⟩ : syracuseStep 1267883 = 1901825) B1901825
theorem B1005929 : Blo 350755 1005929 := bstep (se 2 (by rfl) ⟨377223, by rfl⟩ : syracuseStep 1005929 = 754447) B754447
theorem B1333705 : Blo 350755 1333705 := bstep (se 2 (by rfl) ⟨500139, by rfl⟩ : syracuseStep 1333705 = 1000279) B1000279
theorem B350759 : Blo 350755 350759 := bstep (se 1 (by rfl) ⟨263069, by rfl⟩ : syracuseStep 350759 = 526139) B526139
theorem B350799 : Blo 350755 350799 := bstep (se 1 (by rfl) ⟨263099, by rfl⟩ : syracuseStep 350799 = 526199) B526199
theorem B350815 : Blo 350755 350815 := bstep (se 1 (by rfl) ⟨263111, by rfl⟩ : syracuseStep 350815 = 526223) B526223
theorem B350843 : Blo 350755 350843 := bstep (se 1 (by rfl) ⟨263132, by rfl⟩ : syracuseStep 350843 = 526265) B526265
theorem B350895 : Blo 350755 350895 := bstep (se 1 (by rfl) ⟨263171, by rfl⟩ : syracuseStep 350895 = 526343) B526343
theorem B350919 : Blo 350755 350919 := bstep (se 1 (by rfl) ⟨263189, by rfl⟩ : syracuseStep 350919 = 526379) B526379
theorem B350939 : Blo 350755 350939 := bstep (se 1 (by rfl) ⟨263204, by rfl⟩ : syracuseStep 350939 = 526409) B526409
theorem B1334009 : Blo 350755 1334009 := bstep (se 2 (by rfl) ⟨500253, by rfl⟩ : syracuseStep 1334009 = 1000507) B1000507
theorem B351015 : Blo 350755 351015 := bstep (se 1 (by rfl) ⟨263261, by rfl⟩ : syracuseStep 351015 = 526523) B526523
theorem B351055 : Blo 350755 351055 := bstep (se 1 (by rfl) ⟨263291, by rfl⟩ : syracuseStep 351055 = 526583) B526583
theorem B351071 : Blo 350755 351071 := bstep (se 1 (by rfl) ⟨263303, by rfl⟩ : syracuseStep 351071 = 526607) B526607
theorem B351099 : Blo 350755 351099 := bstep (se 1 (by rfl) ⟨263324, by rfl⟩ : syracuseStep 351099 = 526649) B526649
theorem B1334177 : Blo 350755 1334177 := bstep (se 2 (by rfl) ⟨500316, by rfl⟩ : syracuseStep 1334177 = 1000633) B1000633
theorem B351151 : Blo 350755 351151 := bstep (se 1 (by rfl) ⟨263363, by rfl⟩ : syracuseStep 351151 = 526727) B526727
theorem B1334191 : Blo 350755 1334191 := bstep (se 1 (by rfl) ⟨1000643, by rfl⟩ : syracuseStep 1334191 = 2001287) B2001287
theorem B351175 : Blo 350755 351175 := bstep (se 1 (by rfl) ⟨263381, by rfl⟩ : syracuseStep 351175 = 526763) B526763
theorem B351195 : Blo 350755 351195 := bstep (se 1 (by rfl) ⟨263396, by rfl⟩ : syracuseStep 351195 = 526793) B526793
theorem B351271 : Blo 350755 351271 := bstep (se 1 (by rfl) ⟨263453, by rfl⟩ : syracuseStep 351271 = 526907) B526907
theorem B351311 : Blo 350755 351311 := bstep (se 1 (by rfl) ⟨263483, by rfl⟩ : syracuseStep 351311 = 526967) B526967
theorem B351327 : Blo 350755 351327 := bstep (se 1 (by rfl) ⟨263495, by rfl⟩ : syracuseStep 351327 = 526991) B526991
theorem B351355 : Blo 350755 351355 := bstep (se 1 (by rfl) ⟨263516, by rfl⟩ : syracuseStep 351355 = 527033) B527033
theorem B1793177 : Blo 350755 1793177 := bstep (se 2 (by rfl) ⟨672441, by rfl⟩ : syracuseStep 1793177 = 1344883) B1344883
theorem B1694891 : Blo 350755 1694891 := bstep (se 1 (by rfl) ⟨1271168, by rfl⟩ : syracuseStep 1694891 = 2542337) B2542337
theorem B351407 : Blo 350755 351407 := bstep (se 1 (by rfl) ⟨263555, by rfl⟩ : syracuseStep 351407 = 527111) B527111
theorem B351431 : Blo 350755 351431 := bstep (se 1 (by rfl) ⟨263573, by rfl⟩ : syracuseStep 351431 = 527147) B527147
theorem B351451 : Blo 350755 351451 := bstep (se 1 (by rfl) ⟨263588, by rfl⟩ : syracuseStep 351451 = 527177) B527177
theorem B6774029 : Blo 350755 6774029 := bstep (se 3 (by rfl) ⟨1270130, by rfl⟩ : syracuseStep 6774029 = 2540261) B2540261
theorem B351527 : Blo 350755 351527 := bstep (se 1 (by rfl) ⟨263645, by rfl⟩ : syracuseStep 351527 = 527291) B527291
theorem B351567 : Blo 350755 351567 := bstep (se 1 (by rfl) ⟨263675, by rfl⟩ : syracuseStep 351567 = 527351) B527351
theorem B351583 : Blo 350755 351583 := bstep (se 1 (by rfl) ⟨263687, by rfl⟩ : syracuseStep 351583 = 527375) B527375
theorem B351611 : Blo 350755 351611 := bstep (se 1 (by rfl) ⟨263708, by rfl⟩ : syracuseStep 351611 = 527417) B527417
theorem B2874797 : Blo 350755 2874797 := bstep (se 3 (by rfl) ⟨539024, by rfl⟩ : syracuseStep 2874797 = 1078049) B1078049
theorem B351663 : Blo 350755 351663 := bstep (se 1 (by rfl) ⟨263747, by rfl⟩ : syracuseStep 351663 = 527495) B527495
theorem B351687 : Blo 350755 351687 := bstep (se 1 (by rfl) ⟨263765, by rfl⟩ : syracuseStep 351687 = 527531) B527531
theorem B351707 : Blo 350755 351707 := bstep (se 1 (by rfl) ⟨263780, by rfl⟩ : syracuseStep 351707 = 527561) B527561
theorem B1433051 : Blo 350755 1433051 := bstep (se 1 (by rfl) ⟨1074788, by rfl⟩ : syracuseStep 1433051 = 2149577) B2149577
theorem B2416139 : Blo 350755 2416139 := bstep (se 1 (by rfl) ⟨1812104, by rfl⟩ : syracuseStep 2416139 = 3624209) B3624209
theorem B351783 : Blo 350755 351783 := bstep (se 1 (by rfl) ⟨263837, by rfl⟩ : syracuseStep 351783 = 527675) B527675
theorem B351823 : Blo 350755 351823 := bstep (se 1 (by rfl) ⟨263867, by rfl⟩ : syracuseStep 351823 = 527735) B527735
theorem B351839 : Blo 350755 351839 := bstep (se 1 (by rfl) ⟨263879, by rfl⟩ : syracuseStep 351839 = 527759) B527759
theorem B351867 : Blo 350755 351867 := bstep (se 1 (by rfl) ⟨263900, by rfl⟩ : syracuseStep 351867 = 527801) B527801
theorem B1498763 : Blo 350755 1498763 := bstep (se 1 (by rfl) ⟨1124072, by rfl⟩ : syracuseStep 1498763 = 2248145) B2248145
theorem B351919 : Blo 350755 351919 := bstep (se 1 (by rfl) ⟨263939, by rfl⟩ : syracuseStep 351919 = 527879) B527879
theorem B351943 : Blo 350755 351943 := bstep (se 1 (by rfl) ⟨263957, by rfl⟩ : syracuseStep 351943 = 527915) B527915
theorem B1695431 : Blo 350755 1695431 := bstep (se 1 (by rfl) ⟨1271573, by rfl⟩ : syracuseStep 1695431 = 2543147) B2543147
theorem B351963 : Blo 350755 351963 := bstep (se 1 (by rfl) ⟨263972, by rfl⟩ : syracuseStep 351963 = 527945) B527945
theorem B352039 : Blo 350755 352039 := bstep (se 1 (by rfl) ⟨264029, by rfl⟩ : syracuseStep 352039 = 528059) B528059
theorem B352079 : Blo 350755 352079 := bstep (se 1 (by rfl) ⟨264059, by rfl⟩ : syracuseStep 352079 = 528119) B528119
theorem B352095 : Blo 350755 352095 := bstep (se 1 (by rfl) ⟨264071, by rfl⟩ : syracuseStep 352095 = 528143) B528143
theorem B1335149 : Blo 350755 1335149 := bstep (se 3 (by rfl) ⟨250340, by rfl⟩ : syracuseStep 1335149 = 500681) B500681
theorem B352123 : Blo 350755 352123 := bstep (se 1 (by rfl) ⟨264092, by rfl⟩ : syracuseStep 352123 = 528185) B528185
theorem B352175 : Blo 350755 352175 := bstep (se 1 (by rfl) ⟨264131, by rfl⟩ : syracuseStep 352175 = 528263) B528263
theorem B2252731 : Blo 350755 2252731 := bstep (se 1 (by rfl) ⟨1689548, by rfl⟩ : syracuseStep 2252731 = 3379097) B3379097
theorem B352199 : Blo 350755 352199 := bstep (se 1 (by rfl) ⟨264149, by rfl⟩ : syracuseStep 352199 = 528299) B528299
theorem B352219 : Blo 350755 352219 := bstep (se 1 (by rfl) ⟨264164, by rfl⟩ : syracuseStep 352219 = 528329) B528329
theorem B352295 : Blo 350755 352295 := bstep (se 1 (by rfl) ⟨264221, by rfl⟩ : syracuseStep 352295 = 528443) B528443
theorem B843833 : Blo 350755 843833 := bstep (se 2 (by rfl) ⟨316437, by rfl⟩ : syracuseStep 843833 = 632875) B632875
theorem B352335 : Blo 350755 352335 := bstep (se 1 (by rfl) ⟨264251, by rfl⟩ : syracuseStep 352335 = 528503) B528503
theorem B352351 : Blo 350755 352351 := bstep (se 1 (by rfl) ⟨264263, by rfl⟩ : syracuseStep 352351 = 528527) B528527
theorem B352379 : Blo 350755 352379 := bstep (se 1 (by rfl) ⟨264284, by rfl⟩ : syracuseStep 352379 = 528569) B528569
theorem B1335467 : Blo 350755 1335467 := bstep (se 1 (by rfl) ⟨1001600, by rfl⟩ : syracuseStep 1335467 = 2003201) B2003201
theorem B352431 : Blo 350755 352431 := bstep (se 1 (by rfl) ⟨264323, by rfl⟩ : syracuseStep 352431 = 528647) B528647
theorem B352455 : Blo 350755 352455 := bstep (se 1 (by rfl) ⟨264341, by rfl⟩ : syracuseStep 352455 = 528683) B528683
theorem B352475 : Blo 350755 352475 := bstep (se 1 (by rfl) ⟨264356, by rfl⟩ : syracuseStep 352475 = 528713) B528713
theorem B352551 : Blo 350755 352551 := bstep (se 1 (by rfl) ⟨264413, by rfl⟩ : syracuseStep 352551 = 528827) B528827
theorem B352591 : Blo 350755 352591 := bstep (se 1 (by rfl) ⟨264443, by rfl⟩ : syracuseStep 352591 = 528887) B528887
theorem B352607 : Blo 350755 352607 := bstep (se 1 (by rfl) ⟨264455, by rfl⟩ : syracuseStep 352607 = 528911) B528911
theorem B1073513 : Blo 350755 1073513 := bstep (se 2 (by rfl) ⟨402567, by rfl⟩ : syracuseStep 1073513 = 805135) B805135
theorem B352635 : Blo 350755 352635 := bstep (se 1 (by rfl) ⟨264476, by rfl⟩ : syracuseStep 352635 = 528953) B528953
theorem B352687 : Blo 350755 352687 := bstep (se 1 (by rfl) ⟨264515, by rfl⟩ : syracuseStep 352687 = 529031) B529031
theorem B352711 : Blo 350755 352711 := bstep (se 1 (by rfl) ⟨264533, by rfl⟩ : syracuseStep 352711 = 529067) B529067
theorem B352731 : Blo 350755 352731 := bstep (se 1 (by rfl) ⟨264548, by rfl⟩ : syracuseStep 352731 = 529097) B529097
theorem B352807 : Blo 350755 352807 := bstep (se 1 (by rfl) ⟨264605, by rfl⟩ : syracuseStep 352807 = 529211) B529211
theorem B1696315 : Blo 350755 1696315 := bstep (se 1 (by rfl) ⟨1272236, by rfl⟩ : syracuseStep 1696315 = 2544473) B2544473
theorem B352847 : Blo 350755 352847 := bstep (se 1 (by rfl) ⟨264635, by rfl⟩ : syracuseStep 352847 = 529271) B529271
theorem B352863 : Blo 350755 352863 := bstep (se 1 (by rfl) ⟨264647, by rfl⟩ : syracuseStep 352863 = 529295) B529295
theorem B352891 : Blo 350755 352891 := bstep (se 1 (by rfl) ⟨264668, by rfl⟩ : syracuseStep 352891 = 529337) B529337
theorem B352943 : Blo 350755 352943 := bstep (se 1 (by rfl) ⟨264707, by rfl⟩ : syracuseStep 352943 = 529415) B529415
theorem B352967 : Blo 350755 352967 := bstep (se 1 (by rfl) ⟨264725, by rfl⟩ : syracuseStep 352967 = 529451) B529451
theorem B352987 : Blo 350755 352987 := bstep (se 1 (by rfl) ⟨264740, by rfl⟩ : syracuseStep 352987 = 529481) B529481
theorem B353063 : Blo 350755 353063 := bstep (se 1 (by rfl) ⟨264797, by rfl⟩ : syracuseStep 353063 = 529595) B529595
theorem B353103 : Blo 350755 353103 := bstep (se 1 (by rfl) ⟨264827, by rfl⟩ : syracuseStep 353103 = 529655) B529655
theorem B353119 : Blo 350755 353119 := bstep (se 1 (by rfl) ⟨264839, by rfl⟩ : syracuseStep 353119 = 529679) B529679
theorem B353147 : Blo 350755 353147 := bstep (se 1 (by rfl) ⟨264860, by rfl⟩ : syracuseStep 353147 = 529721) B529721
theorem B353199 : Blo 350755 353199 := bstep (se 1 (by rfl) ⟨264899, by rfl⟩ : syracuseStep 353199 = 529799) B529799
theorem B353223 : Blo 350755 353223 := bstep (se 1 (by rfl) ⟨264917, by rfl⟩ : syracuseStep 353223 = 529835) B529835
theorem B353243 : Blo 350755 353243 := bstep (se 1 (by rfl) ⟨264932, by rfl⟩ : syracuseStep 353243 = 529865) B529865
theorem B353319 : Blo 350755 353319 := bstep (se 1 (by rfl) ⟨264989, by rfl⟩ : syracuseStep 353319 = 529979) B529979
theorem B353359 : Blo 350755 353359 := bstep (se 1 (by rfl) ⟨265019, by rfl⟩ : syracuseStep 353359 = 530039) B530039
theorem B353375 : Blo 350755 353375 := bstep (se 1 (by rfl) ⟨265031, by rfl⟩ : syracuseStep 353375 = 530063) B530063
theorem B353403 : Blo 350755 353403 := bstep (se 1 (by rfl) ⟨265052, by rfl⟩ : syracuseStep 353403 = 530105) B530105
theorem B353455 : Blo 350755 353455 := bstep (se 1 (by rfl) ⟨265091, by rfl⟩ : syracuseStep 353455 = 530183) B530183
theorem B353479 : Blo 350755 353479 := bstep (se 1 (by rfl) ⟨265109, by rfl⟩ : syracuseStep 353479 = 530219) B530219
theorem B353499 : Blo 350755 353499 := bstep (se 1 (by rfl) ⟨265124, by rfl⟩ : syracuseStep 353499 = 530249) B530249
theorem B353575 : Blo 350755 353575 := bstep (se 1 (by rfl) ⟨265181, by rfl⟩ : syracuseStep 353575 = 530363) B530363
theorem B353615 : Blo 350755 353615 := bstep (se 1 (by rfl) ⟨265211, by rfl⟩ : syracuseStep 353615 = 530423) B530423
theorem B353631 : Blo 350755 353631 := bstep (se 1 (by rfl) ⟨265223, by rfl⟩ : syracuseStep 353631 = 530447) B530447
theorem B353659 : Blo 350755 353659 := bstep (se 1 (by rfl) ⟨265244, by rfl⟩ : syracuseStep 353659 = 530489) B530489
theorem B353711 : Blo 350755 353711 := bstep (se 1 (by rfl) ⟨265283, by rfl⟩ : syracuseStep 353711 = 530567) B530567
theorem B353735 : Blo 350755 353735 := bstep (se 1 (by rfl) ⟨265301, by rfl⟩ : syracuseStep 353735 = 530603) B530603
theorem B353755 : Blo 350755 353755 := bstep (se 1 (by rfl) ⟨265316, by rfl⟩ : syracuseStep 353755 = 530633) B530633
theorem B353831 : Blo 350755 353831 := bstep (se 1 (by rfl) ⟨265373, by rfl⟩ : syracuseStep 353831 = 530747) B530747
theorem B353871 : Blo 350755 353871 := bstep (se 1 (by rfl) ⟨265403, by rfl⟩ : syracuseStep 353871 = 530807) B530807
theorem B353887 : Blo 350755 353887 := bstep (se 1 (by rfl) ⟨265415, by rfl⟩ : syracuseStep 353887 = 530831) B530831
theorem B353915 : Blo 350755 353915 := bstep (se 1 (by rfl) ⟨265436, by rfl⟩ : syracuseStep 353915 = 530873) B530873
theorem B353967 : Blo 350755 353967 := bstep (se 1 (by rfl) ⟨265475, by rfl⟩ : syracuseStep 353967 = 530951) B530951
theorem B353991 : Blo 350755 353991 := bstep (se 1 (by rfl) ⟨265493, by rfl⟩ : syracuseStep 353991 = 530987) B530987
theorem B354011 : Blo 350755 354011 := bstep (se 1 (by rfl) ⟨265508, by rfl⟩ : syracuseStep 354011 = 531017) B531017
theorem B354087 : Blo 350755 354087 := bstep (se 1 (by rfl) ⟨265565, by rfl⟩ : syracuseStep 354087 = 531131) B531131
theorem B354127 : Blo 350755 354127 := bstep (se 1 (by rfl) ⟨265595, by rfl⟩ : syracuseStep 354127 = 531191) B531191
theorem B354143 : Blo 350755 354143 := bstep (se 1 (by rfl) ⟨265607, by rfl⟩ : syracuseStep 354143 = 531215) B531215
theorem B354171 : Blo 350755 354171 := bstep (se 1 (by rfl) ⟨265628, by rfl⟩ : syracuseStep 354171 = 531257) B531257
theorem B354223 : Blo 350755 354223 := bstep (se 1 (by rfl) ⟨265667, by rfl⟩ : syracuseStep 354223 = 531335) B531335
theorem B354247 : Blo 350755 354247 := bstep (se 1 (by rfl) ⟨265685, by rfl⟩ : syracuseStep 354247 = 531371) B531371
theorem B354267 : Blo 350755 354267 := bstep (se 1 (by rfl) ⟨265700, by rfl⟩ : syracuseStep 354267 = 531401) B531401
theorem B714791 : Blo 350755 714791 := bstep (se 1 (by rfl) ⟨536093, by rfl⟩ : syracuseStep 714791 = 1072187) B1072187
theorem B354343 : Blo 350755 354343 := bstep (se 1 (by rfl) ⟨265757, by rfl⟩ : syracuseStep 354343 = 531515) B531515
theorem B354383 : Blo 350755 354383 := bstep (se 1 (by rfl) ⟨265787, by rfl⟩ : syracuseStep 354383 = 531575) B531575
theorem B354399 : Blo 350755 354399 := bstep (se 1 (by rfl) ⟨265799, by rfl⟩ : syracuseStep 354399 = 531599) B531599
theorem B354427 : Blo 350755 354427 := bstep (se 1 (by rfl) ⟨265820, by rfl⟩ : syracuseStep 354427 = 531641) B531641
theorem B354479 : Blo 350755 354479 := bstep (se 1 (by rfl) ⟨265859, by rfl⟩ : syracuseStep 354479 = 531719) B531719
theorem B354503 : Blo 350755 354503 := bstep (se 1 (by rfl) ⟨265877, by rfl⟩ : syracuseStep 354503 = 531755) B531755
theorem B354523 : Blo 350755 354523 := bstep (se 1 (by rfl) ⟨265892, by rfl⟩ : syracuseStep 354523 = 531785) B531785
theorem B354599 : Blo 350755 354599 := bstep (se 1 (by rfl) ⟨265949, by rfl⟩ : syracuseStep 354599 = 531899) B531899
theorem B354639 : Blo 350755 354639 := bstep (se 1 (by rfl) ⟨265979, by rfl⟩ : syracuseStep 354639 = 531959) B531959
theorem B354655 : Blo 350755 354655 := bstep (se 1 (by rfl) ⟨265991, by rfl⟩ : syracuseStep 354655 = 531983) B531983
theorem B715115 : Blo 350755 715115 := bstep (se 1 (by rfl) ⟨536336, by rfl⟩ : syracuseStep 715115 = 1072673) B1072673
theorem B354683 : Blo 350755 354683 := bstep (se 1 (by rfl) ⟨266012, by rfl⟩ : syracuseStep 354683 = 532025) B532025
theorem B354735 : Blo 350755 354735 := bstep (se 1 (by rfl) ⟨266051, by rfl⟩ : syracuseStep 354735 = 532103) B532103
theorem B1338065 : Blo 350755 1338065 := bstep (se 2 (by rfl) ⟨501774, by rfl⟩ : syracuseStep 1338065 = 1003549) B1003549
theorem B3337037 : Blo 350755 3337037 := bstep (se 3 (by rfl) ⟨625694, by rfl⟩ : syracuseStep 3337037 = 1251389) B1251389
theorem B1502059 : Blo 350755 1502059 := bstep (se 1 (by rfl) ⟨1126544, by rfl⟩ : syracuseStep 1502059 = 2253089) B2253089
theorem B2681747 : Blo 350755 2681747 := bstep (se 1 (by rfl) ⟨2011310, by rfl⟩ : syracuseStep 2681747 = 4022621) B4022621
theorem B715681 : Blo 350755 715681 := bstep (se 2 (by rfl) ⟨268380, by rfl⟩ : syracuseStep 715681 = 536761) B536761
theorem B1338383 : Blo 350755 1338383 := bstep (se 1 (by rfl) ⟨1003787, by rfl⟩ : syracuseStep 1338383 = 2007575) B2007575
theorem B4025537 : Blo 350755 4025537 := bstep (se 2 (by rfl) ⟨1509576, by rfl⟩ : syracuseStep 4025537 = 3019153) B3019153
theorem B2846117 : Blo 350755 2846117 := bstep (se 4 (by rfl) ⟨266823, by rfl⟩ : syracuseStep 2846117 = 533647) B533647
theorem B847369 : Blo 350755 847369 := bstep (se 2 (by rfl) ⟨317763, by rfl⟩ : syracuseStep 847369 = 635527) B635527
theorem B2289239 : Blo 350755 2289239 := bstep (se 1 (by rfl) ⟨1716929, by rfl⟩ : syracuseStep 2289239 = 3433859) B3433859
theorem B749407 : Blo 350755 749407 := bstep (se 1 (by rfl) ⟨562055, by rfl⟩ : syracuseStep 749407 = 1124111) B1124111
theorem B2682719 : Blo 350755 2682719 := bstep (se 1 (by rfl) ⟨2012039, by rfl⟩ : syracuseStep 2682719 = 4024079) B4024079
theorem B1503137 : Blo 350755 1503137 := bstep (se 2 (by rfl) ⟨563676, by rfl⟩ : syracuseStep 1503137 = 1127353) B1127353
theorem B12283811 : Blo 350755 12283811 := bstep (se 1 (by rfl) ⟨9212858, by rfl⟩ : syracuseStep 12283811 = 18425717) B18425717
theorem B2584507 : Blo 350755 2584507 := bstep (se 1 (by rfl) ⟨1938380, by rfl⟩ : syracuseStep 2584507 = 3876761) B3876761
theorem B6057989 : Blo 350755 6057989 := bstep (se 4 (by rfl) ⟨567936, by rfl⟩ : syracuseStep 6057989 = 1135873) B1135873
theorem B749587 : Blo 350755 749587 := bstep (se 1 (by rfl) ⟨562190, by rfl⟩ : syracuseStep 749587 = 1124381) B1124381
theorem B1503289 : Blo 350755 1503289 := bstep (se 2 (by rfl) ⟨563733, by rfl⟩ : syracuseStep 1503289 = 1127467) B1127467
theorem B1438013 : Blo 350755 1438013 := bstep (se 3 (by rfl) ⟨269627, by rfl⟩ : syracuseStep 1438013 = 539255) B539255
theorem B1078123 : Blo 350755 1078123 := bstep (se 1 (by rfl) ⟨808592, by rfl⟩ : syracuseStep 1078123 = 1617185) B1617185
theorem B1340495 : Blo 350755 1340495 := bstep (se 1 (by rfl) ⟨1005371, by rfl⟩ : syracuseStep 1340495 = 2010743) B2010743
theorem B2618825 : Blo 350755 2618825 := bstep (se 2 (by rfl) ⟨982059, by rfl⟩ : syracuseStep 2618825 = 1964119) B1964119
theorem B1275425 : Blo 350755 1275425 := bstep (se 2 (by rfl) ⟨478284, by rfl⟩ : syracuseStep 1275425 = 956569) B956569
theorem B751303 : Blo 350755 751303 := bstep (se 1 (by rfl) ⟨563477, by rfl⟩ : syracuseStep 751303 = 1126955) B1126955
theorem B849619 : Blo 350755 849619 := bstep (se 1 (by rfl) ⟨637214, by rfl⟩ : syracuseStep 849619 = 1274429) B1274429
theorem B19363697 : Blo 350755 19363697 := bstep (se 2 (by rfl) ⟨7261386, by rfl⟩ : syracuseStep 19363697 = 14522773) B14522773
theorem B4028453 : Blo 350755 4028453 := bstep (se 4 (by rfl) ⟨377667, by rfl⟩ : syracuseStep 4028453 = 755335) B755335
theorem B358619 : Blo 350755 358619 := bstep (se 1 (by rfl) ⟨268964, by rfl⟩ : syracuseStep 358619 = 537929) B537929
theorem B21559769 : Blo 350755 21559769 := bstep (se 2 (by rfl) ⟨8084913, by rfl⟩ : syracuseStep 21559769 = 16169827) B16169827
theorem B1210889 : Blo 350755 1210889 := bstep (se 2 (by rfl) ⟨454083, by rfl⟩ : syracuseStep 1210889 = 908167) B908167
theorem B4094509 : Blo 350755 4094509 := bstep (se 3 (by rfl) ⟨767720, by rfl⟩ : syracuseStep 4094509 = 1535441) B1535441
theorem B7600715 : Blo 350755 7600715 := bstep (se 1 (by rfl) ⟨5700536, by rfl⟩ : syracuseStep 7600715 = 11401073) B11401073
theorem B11598709 : Blo 350755 11598709 := bstep (se 5 (by rfl) ⟨543689, by rfl⟩ : syracuseStep 11598709 = 1087379) B1087379
theorem B2260163 : Blo 350755 2260163 := bstep (se 1 (by rfl) ⟨1695122, by rfl⟩ : syracuseStep 2260163 = 3390245) B3390245
theorem B1342939 : Blo 350755 1342939 := bstep (se 1 (by rfl) ⟨1007204, by rfl⟩ : syracuseStep 1342939 = 2014409) B2014409
theorem B851465 : Blo 350755 851465 := bstep (se 2 (by rfl) ⟨319299, by rfl⟩ : syracuseStep 851465 = 638599) B638599
theorem B1343699 : Blo 350755 1343699 := bstep (se 1 (by rfl) ⟨1007774, by rfl⟩ : syracuseStep 1343699 = 2015549) B2015549
theorem B4849901 : Blo 350755 4849901 := bstep (se 3 (by rfl) ⟨909356, by rfl⟩ : syracuseStep 4849901 = 1818713) B1818713
theorem B2261753 : Blo 350755 2261753 := bstep (se 2 (by rfl) ⟨848157, by rfl⟩ : syracuseStep 2261753 = 1696315) B1696315
theorem B3834701 : Blo 350755 3834701 := bstep (se 3 (by rfl) ⟨719006, by rfl⟩ : syracuseStep 3834701 = 1438013) B1438013
theorem B1147727 : Blo 350755 1147727 := bstep (se 1 (by rfl) ⟨860795, by rfl⟩ : syracuseStep 1147727 = 1721591) B1721591
theorem B2065247 : Blo 350755 2065247 := bstep (se 1 (by rfl) ⟨1548935, by rfl⟩ : syracuseStep 2065247 = 3097871) B3097871
theorem B2884571 : Blo 350755 2884571 := bstep (se 1 (by rfl) ⟨2163428, by rfl⟩ : syracuseStep 2884571 = 4326857) B4326857
theorem B394663 : Blo 350755 394663 := bstep (se 1 (by rfl) ⟨295997, by rfl⟩ : syracuseStep 394663 = 591995) B591995
theorem B3409465 : Blo 350755 3409465 := bstep (se 2 (by rfl) ⟨1278549, by rfl⟩ : syracuseStep 3409465 = 2557099) B2557099
theorem B1476407 : Blo 350755 1476407 := bstep (se 1 (by rfl) ⟨1107305, by rfl⟩ : syracuseStep 1476407 = 2214611) B2214611
theorem B1476559 : Blo 350755 1476559 := bstep (se 1 (by rfl) ⟨1107419, by rfl⟩ : syracuseStep 1476559 = 2214839) B2214839
theorem B395239 : Blo 350755 395239 := bstep (se 1 (by rfl) ⟨296429, by rfl⟩ : syracuseStep 395239 = 592859) B592859
theorem B1607933 : Blo 350755 1607933 := bstep (se 3 (by rfl) ⟨301487, by rfl⟩ : syracuseStep 1607933 = 602975) B602975
theorem B526601 : Blo 350755 526601 := bstep (se 2 (by rfl) ⟨197475, by rfl⟩ : syracuseStep 526601 = 394951) B394951
theorem B29231389 : Blo 350755 29231389 := bstep (se 3 (by rfl) ⟨5480885, by rfl⟩ : syracuseStep 29231389 = 10961771) B10961771
theorem B526703 : Blo 350755 526703 := bstep (se 1 (by rfl) ⟨395027, by rfl⟩ : syracuseStep 526703 = 790055) B790055
theorem B2689523 : Blo 350755 2689523 := bstep (se 1 (by rfl) ⟨2017142, by rfl⟩ : syracuseStep 2689523 = 4034285) B4034285
theorem B592447 : Blo 350755 592447 := bstep (se 1 (by rfl) ⟨444335, by rfl⟩ : syracuseStep 592447 = 888671) B888671
theorem B526919 : Blo 350755 526919 := bstep (se 1 (by rfl) ⟨395189, by rfl⟩ : syracuseStep 526919 = 790379) B790379
theorem B526955 : Blo 350755 526955 := bstep (se 1 (by rfl) ⟨395216, by rfl⟩ : syracuseStep 526955 = 790433) B790433
theorem B756395 : Blo 350755 756395 := bstep (se 1 (by rfl) ⟨567296, by rfl⟩ : syracuseStep 756395 = 1134593) B1134593
theorem B527183 : Blo 350755 527183 := bstep (se 1 (by rfl) ⟨395387, by rfl⟩ : syracuseStep 527183 = 790775) B790775
theorem B2034557 : Blo 350755 2034557 := bstep (se 3 (by rfl) ⟨381479, by rfl⟩ : syracuseStep 2034557 = 762959) B762959
theorem B789479 : Blo 350755 789479 := bstep (se 1 (by rfl) ⟨592109, by rfl⟩ : syracuseStep 789479 = 1184219) B1184219
theorem B7638083 : Blo 350755 7638083 := bstep (se 1 (by rfl) ⟨5728562, by rfl⟩ : syracuseStep 7638083 = 11457125) B11457125
theorem B888023 : Blo 350755 888023 := bstep (se 1 (by rfl) ⟨666017, by rfl⟩ : syracuseStep 888023 = 1332035) B1332035
theorem B527579 : Blo 350755 527579 := bstep (se 1 (by rfl) ⟨395684, by rfl⟩ : syracuseStep 527579 = 791369) B791369
theorem B593129 : Blo 350755 593129 := bstep (se 2 (by rfl) ⟨222423, by rfl⟩ : syracuseStep 593129 = 444847) B444847
theorem B593183 : Blo 350755 593183 := bstep (se 1 (by rfl) ⟨444887, by rfl⟩ : syracuseStep 593183 = 889775) B889775
theorem B789857 : Blo 350755 789857 := bstep (se 2 (by rfl) ⟨296196, by rfl⟩ : syracuseStep 789857 = 592393) B592393
theorem B527753 : Blo 350755 527753 := bstep (se 2 (by rfl) ⟨197907, by rfl⟩ : syracuseStep 527753 = 395815) B395815
theorem B789947 : Blo 350755 789947 := bstep (se 1 (by rfl) ⟨592460, by rfl⟩ : syracuseStep 789947 = 1184921) B1184921
theorem B790073 : Blo 350755 790073 := bstep (se 2 (by rfl) ⟨296277, by rfl⟩ : syracuseStep 790073 = 592555) B592555
theorem B396895 : Blo 350755 396895 := bstep (se 1 (by rfl) ⟨297671, by rfl⟩ : syracuseStep 396895 = 595343) B595343
theorem B2133715 : Blo 350755 2133715 := bstep (se 1 (by rfl) ⟨1600286, by rfl⟩ : syracuseStep 2133715 = 3200573) B3200573
theorem B528107 : Blo 350755 528107 := bstep (se 1 (by rfl) ⟨396080, by rfl⟩ : syracuseStep 528107 = 792161) B792161
theorem B2002745 : Blo 350755 2002745 := bstep (se 2 (by rfl) ⟨751029, by rfl⟩ : syracuseStep 2002745 = 1502059) B1502059
theorem B6983533 : Blo 350755 6983533 := bstep (se 3 (by rfl) ⟨1309412, by rfl⟩ : syracuseStep 6983533 = 2618825) B2618825
theorem B528335 : Blo 350755 528335 := bstep (se 1 (by rfl) ⟨396251, by rfl⟩ : syracuseStep 528335 = 792503) B792503
theorem B790739 : Blo 350755 790739 := bstep (se 1 (by rfl) ⟨593054, by rfl⟩ : syracuseStep 790739 = 1186109) B1186109
theorem B790793 : Blo 350755 790793 := bstep (se 2 (by rfl) ⟨296547, by rfl⟩ : syracuseStep 790793 = 593095) B593095
theorem B528731 : Blo 350755 528731 := bstep (se 1 (by rfl) ⟨396548, by rfl⟩ : syracuseStep 528731 = 793097) B793097
theorem B791009 : Blo 350755 791009 := bstep (se 2 (by rfl) ⟨296628, by rfl⟩ : syracuseStep 791009 = 593257) B593257
theorem B889339 : Blo 350755 889339 := bstep (se 1 (by rfl) ⟨667004, by rfl⟩ : syracuseStep 889339 = 1334009) B1334009
theorem B528959 : Blo 350755 528959 := bstep (se 1 (by rfl) ⟨396719, by rfl⟩ : syracuseStep 528959 = 793439) B793439
theorem B1184327 : Blo 350755 1184327 := bstep (se 1 (by rfl) ⟨888245, by rfl⟩ : syracuseStep 1184327 = 1776491) B1776491
theorem B889451 : Blo 350755 889451 := bstep (se 1 (by rfl) ⟨667088, by rfl⟩ : syracuseStep 889451 = 1334177) B1334177
theorem B594553 : Blo 350755 594553 := bstep (se 2 (by rfl) ⟨222957, by rfl⟩ : syracuseStep 594553 = 445915) B445915
theorem B1512107 : Blo 350755 1512107 := bstep (se 1 (by rfl) ⟨1134080, by rfl⟩ : syracuseStep 1512107 = 2268161) B2268161
theorem B594607 : Blo 350755 594607 := bstep (se 1 (by rfl) ⟨445955, by rfl⟩ : syracuseStep 594607 = 891911) B891911
theorem B529079 : Blo 350755 529079 := bstep (se 1 (by rfl) ⟨396809, by rfl⟩ : syracuseStep 529079 = 793619) B793619
theorem B398047 : Blo 350755 398047 := bstep (se 1 (by rfl) ⟨298535, by rfl⟩ : syracuseStep 398047 = 597071) B597071
theorem B791315 : Blo 350755 791315 := bstep (se 1 (by rfl) ⟨593486, by rfl⟩ : syracuseStep 791315 = 1186973) B1186973
theorem B529307 : Blo 350755 529307 := bstep (se 1 (by rfl) ⟨396980, by rfl⟩ : syracuseStep 529307 = 793961) B793961
theorem B955367 : Blo 350755 955367 := bstep (se 1 (by rfl) ⟨716525, by rfl⟩ : syracuseStep 955367 = 1433051) B1433051
theorem B1184759 : Blo 350755 1184759 := bstep (se 1 (by rfl) ⟨888569, by rfl⟩ : syracuseStep 1184759 = 1777139) B1777139
theorem B1610759 : Blo 350755 1610759 := bstep (se 1 (by rfl) ⟨1208069, by rfl⟩ : syracuseStep 1610759 = 2416139) B2416139
theorem B791675 : Blo 350755 791675 := bstep (se 1 (by rfl) ⟨593756, by rfl⟩ : syracuseStep 791675 = 1187513) B1187513
theorem B890099 : Blo 350755 890099 := bstep (se 1 (by rfl) ⟨667574, by rfl⟩ : syracuseStep 890099 = 1335149) B1335149
theorem B791801 : Blo 350755 791801 := bstep (se 2 (by rfl) ⟨296925, by rfl⟩ : syracuseStep 791801 = 593851) B593851
theorem B3446009 : Blo 350755 3446009 := bstep (se 2 (by rfl) ⟨1292253, by rfl⟩ : syracuseStep 3446009 = 2584507) B2584507
theorem B398623 : Blo 350755 398623 := bstep (se 1 (by rfl) ⟨298967, by rfl⟩ : syracuseStep 398623 = 597935) B597935
theorem B529703 : Blo 350755 529703 := bstep (se 1 (by rfl) ⟨397277, by rfl⟩ : syracuseStep 529703 = 794555) B794555
theorem B562555 : Blo 350755 562555 := bstep (se 1 (by rfl) ⟨421916, by rfl⟩ : syracuseStep 562555 = 843833) B843833
theorem B529787 : Blo 350755 529787 := bstep (se 1 (by rfl) ⟨397340, by rfl⟩ : syracuseStep 529787 = 794681) B794681
theorem B791945 : Blo 350755 791945 := bstep (se 2 (by rfl) ⟨296979, by rfl⟩ : syracuseStep 791945 = 593959) B593959
theorem B2004385 : Blo 350755 2004385 := bstep (se 2 (by rfl) ⟨751644, by rfl⟩ : syracuseStep 2004385 = 1503289) B1503289
theorem B2168257 : Blo 350755 2168257 := bstep (se 2 (by rfl) ⟨813096, by rfl⟩ : syracuseStep 2168257 = 1626193) B1626193
theorem B890311 : Blo 350755 890311 := bstep (se 1 (by rfl) ⟨667733, by rfl⟩ : syracuseStep 890311 = 1335467) B1335467
theorem B529913 : Blo 350755 529913 := bstep (se 2 (by rfl) ⟨198717, by rfl⟩ : syracuseStep 529913 = 397435) B397435
theorem B792071 : Blo 350755 792071 := bstep (se 1 (by rfl) ⟨594053, by rfl⟩ : syracuseStep 792071 = 1188107) B1188107
theorem B6755885 : Blo 350755 6755885 := bstep (se 3 (by rfl) ⟨1266728, by rfl⟩ : syracuseStep 6755885 = 2533457) B2533457
theorem B398911 : Blo 350755 398911 := bstep (se 1 (by rfl) ⟨299183, by rfl⟩ : syracuseStep 398911 = 598367) B598367
theorem B530015 : Blo 350755 530015 := bstep (se 1 (by rfl) ⟨397511, by rfl⟩ : syracuseStep 530015 = 795023) B795023
theorem B792251 : Blo 350755 792251 := bstep (se 1 (by rfl) ⟨594188, by rfl⟩ : syracuseStep 792251 = 1188377) B1188377
theorem B530231 : Blo 350755 530231 := bstep (se 1 (by rfl) ⟨397673, by rfl⟩ : syracuseStep 530231 = 795347) B795347
theorem B792377 : Blo 350755 792377 := bstep (se 2 (by rfl) ⟨297141, by rfl⟩ : syracuseStep 792377 = 594283) B594283
theorem B1185623 : Blo 350755 1185623 := bstep (se 1 (by rfl) ⟨889217, by rfl⟩ : syracuseStep 1185623 = 1778435) B1778435
theorem B24549317 : Blo 350755 24549317 := bstep (se 4 (by rfl) ⟨2301498, by rfl⟩ : syracuseStep 24549317 = 4602997) B4602997
theorem B530537 : Blo 350755 530537 := bstep (se 2 (by rfl) ⟨198951, by rfl⟩ : syracuseStep 530537 = 397903) B397903
theorem B1906973 : Blo 350755 1906973 := bstep (se 3 (by rfl) ⟨357557, by rfl⟩ : syracuseStep 1906973 = 715115) B715115
theorem B596315 : Blo 350755 596315 := bstep (se 1 (by rfl) ⟨447236, by rfl⟩ : syracuseStep 596315 = 894473) B894473
theorem B596335 : Blo 350755 596335 := bstep (se 1 (by rfl) ⟨447251, by rfl⟩ : syracuseStep 596335 = 894503) B894503
theorem B530855 : Blo 350755 530855 := bstep (se 1 (by rfl) ⟨398141, by rfl⟩ : syracuseStep 530855 = 796283) B796283
theorem B793007 : Blo 350755 793007 := bstep (se 1 (by rfl) ⟨594755, by rfl⟩ : syracuseStep 793007 = 1189511) B1189511
theorem B793043 : Blo 350755 793043 := bstep (se 1 (by rfl) ⟨594782, by rfl⟩ : syracuseStep 793043 = 1189565) B1189565
theorem B530939 : Blo 350755 530939 := bstep (se 1 (by rfl) ⟨398204, by rfl⟩ : syracuseStep 530939 = 796409) B796409
theorem B1776167 : Blo 350755 1776167 := bstep (se 1 (by rfl) ⟨1332125, by rfl⟩ : syracuseStep 1776167 = 2664251) B2664251
theorem B793151 : Blo 350755 793151 := bstep (se 1 (by rfl) ⟨594863, by rfl⟩ : syracuseStep 793151 = 1189727) B1189727
theorem B596551 : Blo 350755 596551 := bstep (se 1 (by rfl) ⟨447413, by rfl⟩ : syracuseStep 596551 = 894827) B894827
theorem B531065 : Blo 350755 531065 := bstep (se 2 (by rfl) ⟨199149, by rfl⟩ : syracuseStep 531065 = 398299) B398299
theorem B1514123 : Blo 350755 1514123 := bstep (se 1 (by rfl) ⟨1135592, by rfl⟩ : syracuseStep 1514123 = 2271185) B2271185
theorem B793259 : Blo 350755 793259 := bstep (se 1 (by rfl) ⟨594944, by rfl⟩ : syracuseStep 793259 = 1189889) B1189889
theorem B531119 : Blo 350755 531119 := bstep (se 1 (by rfl) ⟨398339, by rfl⟩ : syracuseStep 531119 = 796679) B796679
theorem B531167 : Blo 350755 531167 := bstep (se 1 (by rfl) ⟨398375, by rfl⟩ : syracuseStep 531167 = 796751) B796751
theorem B1186703 : Blo 350755 1186703 := bstep (se 1 (by rfl) ⟨890027, by rfl⟩ : syracuseStep 1186703 = 1780055) B1780055
theorem B531431 : Blo 350755 531431 := bstep (se 1 (by rfl) ⟨398573, by rfl⟩ : syracuseStep 531431 = 797147) B797147
theorem B1514483 : Blo 350755 1514483 := bstep (se 1 (by rfl) ⟨1135862, by rfl⟩ : syracuseStep 1514483 = 2271725) B2271725
theorem B596983 : Blo 350755 596983 := bstep (se 1 (by rfl) ⟨447737, by rfl⟩ : syracuseStep 596983 = 895475) B895475
theorem B892043 : Blo 350755 892043 := bstep (se 1 (by rfl) ⟨669032, by rfl⟩ : syracuseStep 892043 = 1338065) B1338065
theorem B793799 : Blo 350755 793799 := bstep (se 1 (by rfl) ⟨595349, by rfl⟩ : syracuseStep 793799 = 1190699) B1190699
theorem B531689 : Blo 350755 531689 := bstep (se 2 (by rfl) ⟨199383, by rfl⟩ : syracuseStep 531689 = 398767) B398767
theorem B531743 : Blo 350755 531743 := bstep (se 1 (by rfl) ⟨398807, by rfl⟩ : syracuseStep 531743 = 797615) B797615
theorem B597287 : Blo 350755 597287 := bstep (se 1 (by rfl) ⟨447965, by rfl⟩ : syracuseStep 597287 = 895931) B895931
theorem B892255 : Blo 350755 892255 := bstep (se 1 (by rfl) ⟨669191, by rfl⟩ : syracuseStep 892255 = 1338383) B1338383
theorem B793979 : Blo 350755 793979 := bstep (se 1 (by rfl) ⟨595484, by rfl⟩ : syracuseStep 793979 = 1190969) B1190969
theorem B531911 : Blo 350755 531911 := bstep (se 1 (by rfl) ⟨398933, by rfl⟩ : syracuseStep 531911 = 797867) B797867
theorem B794105 : Blo 350755 794105 := bstep (se 2 (by rfl) ⟨297789, by rfl⟩ : syracuseStep 794105 = 595579) B595579
theorem B794195 : Blo 350755 794195 := bstep (se 1 (by rfl) ⟨595646, by rfl⟩ : syracuseStep 794195 = 1191293) B1191293
theorem B597739 : Blo 350755 597739 := bstep (se 1 (by rfl) ⟨448304, by rfl⟩ : syracuseStep 597739 = 896609) B896609
theorem B794375 : Blo 350755 794375 := bstep (se 1 (by rfl) ⟨595781, by rfl⟩ : syracuseStep 794375 = 1191563) B1191563
theorem B991033 : Blo 350755 991033 := bstep (se 2 (by rfl) ⟨371637, by rfl⟩ : syracuseStep 991033 = 743275) B743275
theorem B401231 : Blo 350755 401231 := bstep (se 1 (by rfl) ⟨300923, by rfl⟩ : syracuseStep 401231 = 601847) B601847
theorem B2039681 : Blo 350755 2039681 := bstep (se 2 (by rfl) ⟨764880, by rfl⟩ : syracuseStep 2039681 = 1529761) B1529761
theorem B4038659 : Blo 350755 4038659 := bstep (se 1 (by rfl) ⟨3028994, by rfl⟩ : syracuseStep 4038659 = 6057989) B6057989
theorem B1187945 : Blo 350755 1187945 := bstep (se 2 (by rfl) ⟨445479, by rfl⟩ : syracuseStep 1187945 = 890959) B890959
theorem B5087441 : Blo 350755 5087441 := bstep (se 2 (by rfl) ⟨1907790, by rfl⟩ : syracuseStep 5087441 = 3815581) B3815581
theorem B794987 : Blo 350755 794987 := bstep (se 1 (by rfl) ⟨596240, by rfl⟩ : syracuseStep 794987 = 1192481) B1192481
theorem B795131 : Blo 350755 795131 := bstep (se 1 (by rfl) ⟨596348, by rfl⟩ : syracuseStep 795131 = 1192697) B1192697
theorem B1778273 : Blo 350755 1778273 := bstep (se 2 (by rfl) ⟨666852, by rfl⟩ : syracuseStep 1778273 = 1333705) B1333705
theorem B795257 : Blo 350755 795257 := bstep (se 2 (by rfl) ⟨298221, by rfl⟩ : syracuseStep 795257 = 596443) B596443
theorem B795311 : Blo 350755 795311 := bstep (se 1 (by rfl) ⟨596483, by rfl⟩ : syracuseStep 795311 = 1192967) B1192967
theorem B893663 : Blo 350755 893663 := bstep (se 1 (by rfl) ⟨670247, by rfl⟩ : syracuseStep 893663 = 1340495) B1340495
theorem B795383 : Blo 350755 795383 := bstep (se 1 (by rfl) ⟨596537, by rfl⟩ : syracuseStep 795383 = 1193075) B1193075
theorem B795563 : Blo 350755 795563 := bstep (se 1 (by rfl) ⟨596672, by rfl⟩ : syracuseStep 795563 = 1193345) B1193345
theorem B4268983 : Blo 350755 4268983 := bstep (se 1 (by rfl) ⟨3201737, by rfl⟩ : syracuseStep 4268983 = 6403475) B6403475
theorem B3089335 : Blo 350755 3089335 := bstep (se 1 (by rfl) ⟨2317001, by rfl⟩ : syracuseStep 3089335 = 4634003) B4634003
theorem B1188809 : Blo 350755 1188809 := bstep (se 2 (by rfl) ⟨445803, by rfl⟩ : syracuseStep 1188809 = 891607) B891607
theorem B1090685 : Blo 350755 1090685 := bstep (se 3 (by rfl) ⟨204503, by rfl⟩ : syracuseStep 1090685 = 409007) B409007
theorem B1189079 : Blo 350755 1189079 := bstep (se 1 (by rfl) ⟨891809, by rfl⟩ : syracuseStep 1189079 = 1783619) B1783619
theorem B1778921 : Blo 350755 1778921 := bstep (se 2 (by rfl) ⟨667095, by rfl⟩ : syracuseStep 1778921 = 1334191) B1334191
theorem B1779083 : Blo 350755 1779083 := bstep (se 1 (by rfl) ⟨1334312, by rfl⟩ : syracuseStep 1779083 = 2668625) B2668625
theorem B796103 : Blo 350755 796103 := bstep (se 1 (by rfl) ⟨597077, by rfl⟩ : syracuseStep 796103 = 1194155) B1194155
theorem B796463 : Blo 350755 796463 := bstep (se 1 (by rfl) ⟨597347, by rfl⟩ : syracuseStep 796463 = 1194695) B1194695
theorem B567643 : Blo 350755 567643 := bstep (se 1 (by rfl) ⟨425732, by rfl⟩ : syracuseStep 567643 = 851465) B851465
theorem B797039 : Blo 350755 797039 := bstep (se 1 (by rfl) ⟨597779, by rfl⟩ : syracuseStep 797039 = 1195559) B1195559
theorem B797111 : Blo 350755 797111 := bstep (se 1 (by rfl) ⟨597833, by rfl⟩ : syracuseStep 797111 = 1195667) B1195667
theorem B1911251 : Blo 350755 1911251 := bstep (se 1 (by rfl) ⟨1433438, by rfl⟩ : syracuseStep 1911251 = 2866877) B2866877
theorem B797255 : Blo 350755 797255 := bstep (se 1 (by rfl) ⟨597941, by rfl⟩ : syracuseStep 797255 = 1195883) B1195883
theorem B797291 : Blo 350755 797291 := bstep (se 1 (by rfl) ⟨597968, by rfl⟩ : syracuseStep 797291 = 1195937) B1195937
theorem B797687 : Blo 350755 797687 := bstep (se 1 (by rfl) ⟨598265, by rfl⟩ : syracuseStep 797687 = 1196531) B1196531
theorem B896123 : Blo 350755 896123 := bstep (se 1 (by rfl) ⟨672092, by rfl⟩ : syracuseStep 896123 = 1344185) B1344185
theorem B896143 : Blo 350755 896143 := bstep (se 1 (by rfl) ⟨672107, by rfl⟩ : syracuseStep 896143 = 1344215) B1344215
theorem B1191131 : Blo 350755 1191131 := bstep (se 1 (by rfl) ⟨893348, by rfl⟩ : syracuseStep 1191131 = 1786697) B1786697
theorem B798047 : Blo 350755 798047 := bstep (se 1 (by rfl) ⟨598535, by rfl⟩ : syracuseStep 798047 = 1197071) B1197071
theorem B1125751 : Blo 350755 1125751 := bstep (se 1 (by rfl) ⟨844313, by rfl⟩ : syracuseStep 1125751 = 1688627) B1688627
theorem B896417 : Blo 350755 896417 := bstep (se 2 (by rfl) ⟨336156, by rfl⟩ : syracuseStep 896417 = 672313) B672313
theorem B2862701 : Blo 350755 2862701 := bstep (se 3 (by rfl) ⟨536756, by rfl⟩ : syracuseStep 2862701 = 1073513) B1073513
theorem B2666195 : Blo 350755 2666195 := bstep (se 1 (by rfl) ⟨1999646, by rfl⟩ : syracuseStep 2666195 = 3999293) B3999293
theorem B1814345 : Blo 350755 1814345 := bstep (se 2 (by rfl) ⟨680379, by rfl⟩ : syracuseStep 1814345 = 1360759) B1360759
theorem B1191995 : Blo 350755 1191995 := bstep (se 1 (by rfl) ⟨893996, by rfl⟩ : syracuseStep 1191995 = 1787993) B1787993
theorem B1192265 : Blo 350755 1192265 := bstep (se 2 (by rfl) ⟨447099, by rfl⟩ : syracuseStep 1192265 = 894199) B894199
theorem B2896235 : Blo 350755 2896235 := bstep (se 1 (by rfl) ⟨2172176, by rfl⟩ : syracuseStep 2896235 = 4344353) B4344353
theorem B1782323 : Blo 350755 1782323 := bstep (se 1 (by rfl) ⟨1336742, by rfl⟩ : syracuseStep 1782323 = 2673485) B2673485
theorem B2143055 : Blo 350755 2143055 := bstep (se 1 (by rfl) ⟨1607291, by rfl⟩ : syracuseStep 2143055 = 3214583) B3214583
theorem B6763571 : Blo 350755 6763571 := bstep (se 1 (by rfl) ⟨5072678, by rfl⟩ : syracuseStep 6763571 = 10145357) B10145357
theorem B1717393 : Blo 350755 1717393 := bstep (se 2 (by rfl) ⟨644022, by rfl⟩ : syracuseStep 1717393 = 1288045) B1288045
theorem B963833 : Blo 350755 963833 := bstep (se 2 (by rfl) ⟨361437, by rfl⟩ : syracuseStep 963833 = 722875) B722875
theorem B800417 : Blo 350755 800417 := bstep (se 2 (by rfl) ⟨300156, by rfl⟩ : syracuseStep 800417 = 600313) B600313
theorem B407215 : Blo 350755 407215 := bstep (se 1 (by rfl) ⟨305411, by rfl⟩ : syracuseStep 407215 = 610823) B610823
theorem B571115 : Blo 350755 571115 := bstep (se 1 (by rfl) ⟨428336, by rfl⟩ : syracuseStep 571115 = 856673) B856673
theorem B964457 : Blo 350755 964457 := bstep (se 2 (by rfl) ⟨361671, by rfl⟩ : syracuseStep 964457 = 723343) B723343
theorem B669647 : Blo 350755 669647 := bstep (se 1 (by rfl) ⟨502235, by rfl⟩ : syracuseStep 669647 = 1004471) B1004471
theorem B1128583 : Blo 350755 1128583 := bstep (se 1 (by rfl) ⟨846437, by rfl⟩ : syracuseStep 1128583 = 1692875) B1692875
theorem B1783943 : Blo 350755 1783943 := bstep (se 1 (by rfl) ⟨1337957, by rfl⟩ : syracuseStep 1783943 = 2675915) B2675915
theorem B670619 : Blo 350755 670619 := bstep (se 1 (by rfl) ⟨502964, by rfl⟩ : syracuseStep 670619 = 1005929) B1005929
theorem B2669597 : Blo 350755 2669597 := bstep (se 3 (by rfl) ⟨500549, by rfl⟩ : syracuseStep 2669597 = 1001099) B1001099
theorem B1129825 : Blo 350755 1129825 := bstep (se 2 (by rfl) ⟨423684, by rfl⟩ : syracuseStep 1129825 = 847369) B847369
theorem B1195451 : Blo 350755 1195451 := bstep (se 1 (by rfl) ⟨896588, by rfl⟩ : syracuseStep 1195451 = 1793177) B1793177
theorem B3816965 : Blo 350755 3816965 := bstep (se 4 (by rfl) ⟨357840, by rfl⟩ : syracuseStep 3816965 = 715681) B715681
theorem B2866747 : Blo 350755 2866747 := bstep (se 1 (by rfl) ⟨2150060, by rfl⟩ : syracuseStep 2866747 = 4300121) B4300121
theorem B1916531 : Blo 350755 1916531 := bstep (se 1 (by rfl) ⟨1437398, by rfl⟩ : syracuseStep 1916531 = 2874797) B2874797
theorem B999175 : Blo 350755 999175 := bstep (se 1 (by rfl) ⟨749381, by rfl⟩ : syracuseStep 999175 = 1498763) B1498763
theorem B999209 : Blo 350755 999209 := bstep (se 2 (by rfl) ⟨374703, by rfl⟩ : syracuseStep 999209 = 749407) B749407
theorem B1130287 : Blo 350755 1130287 := bstep (se 1 (by rfl) ⟨847715, by rfl⟩ : syracuseStep 1130287 = 1695431) B1695431
theorem B1359773 : Blo 350755 1359773 := bstep (se 3 (by rfl) ⟨254957, by rfl⟩ : syracuseStep 1359773 = 509915) B509915
theorem B999449 : Blo 350755 999449 := bstep (se 2 (by rfl) ⟨374793, by rfl⟩ : syracuseStep 999449 = 749587) B749587
theorem B2998619 : Blo 350755 2998619 := bstep (se 1 (by rfl) ⟨2248964, by rfl⟩ : syracuseStep 2998619 = 4497929) B4497929
theorem B13877669 : Blo 350755 13877669 := bstep (se 4 (by rfl) ⟨1301031, by rfl⟩ : syracuseStep 13877669 = 2602063) B2602063
theorem B967087 : Blo 350755 967087 := bstep (se 1 (by rfl) ⟨725315, by rfl⟩ : syracuseStep 967087 = 1450631) B1450631
theorem B2867723 : Blo 350755 2867723 := bstep (se 1 (by rfl) ⟨2150792, by rfl⟩ : syracuseStep 2867723 = 4301585) B4301585
theorem B4506587 : Blo 350755 4506587 := bstep (se 1 (by rfl) ⟨3379940, by rfl⟩ : syracuseStep 4506587 = 6759881) B6759881
theorem B3392705 : Blo 350755 3392705 := bstep (se 2 (by rfl) ⟨1272264, by rfl⟩ : syracuseStep 3392705 = 2544529) B2544529
theorem B476527 : Blo 350755 476527 := bstep (se 1 (by rfl) ⟨357395, by rfl⟩ : syracuseStep 476527 = 714791) B714791
theorem B1787831 : Blo 350755 1787831 := bstep (se 1 (by rfl) ⟨1340873, by rfl⟩ : syracuseStep 1787831 = 2681747) B2681747
theorem B1001737 : Blo 350755 1001737 := bstep (se 2 (by rfl) ⟨375651, by rfl⟩ : syracuseStep 1001737 = 751303) B751303
theorem B1132825 : Blo 350755 1132825 := bstep (se 2 (by rfl) ⟨424809, by rfl⟩ : syracuseStep 1132825 = 849619) B849619
theorem B1526159 : Blo 350755 1526159 := bstep (se 1 (by rfl) ⟨1144619, by rfl⟩ : syracuseStep 1526159 = 2289239) B2289239
theorem B1788479 : Blo 350755 1788479 := bstep (se 1 (by rfl) ⟨1341359, by rfl⟩ : syracuseStep 1788479 = 2682719) B2682719
theorem B1002091 : Blo 350755 1002091 := bstep (se 1 (by rfl) ⟨751568, by rfl⟩ : syracuseStep 1002091 = 1503137) B1503137
theorem B1002365 : Blo 350755 1002365 := bstep (se 3 (by rfl) ⟨187943, by rfl⟩ : syracuseStep 1002365 = 375887) B375887
theorem B445819 : Blo 350755 445819 := bstep (se 1 (by rfl) ⟨334364, by rfl⟩ : syracuseStep 445819 = 668729) B668729
theorem B5459345 : Blo 350755 5459345 := bstep (se 2 (by rfl) ⟨2047254, by rfl⟩ : syracuseStep 5459345 = 4094509) B4094509
theorem B14373179 : Blo 350755 14373179 := bstep (se 1 (by rfl) ⟨10779884, by rfl⟩ : syracuseStep 14373179 = 21559769) B21559769
theorem B807259 : Blo 350755 807259 := bstep (se 1 (by rfl) ⟨605444, by rfl⟩ : syracuseStep 807259 = 1210889) B1210889
theorem B5067143 : Blo 350755 5067143 := bstep (se 1 (by rfl) ⟨3800357, by rfl⟩ : syracuseStep 5067143 = 7600715) B7600715
theorem B446887 : Blo 350755 446887 := bstep (se 1 (by rfl) ⟨335165, by rfl⟩ : syracuseStep 446887 = 670331) B670331
theorem B6410771 : Blo 350755 6410771 := bstep (se 1 (by rfl) ⟨4808078, by rfl⟩ : syracuseStep 6410771 = 9616157) B9616157
theorem B1790585 : Blo 350755 1790585 := bstep (se 2 (by rfl) ⟨671469, by rfl⟩ : syracuseStep 1790585 = 1342939) B1342939
theorem B447211 : Blo 350755 447211 := bstep (se 1 (by rfl) ⟨335408, by rfl⟩ : syracuseStep 447211 = 670817) B670817
theorem B447439 : Blo 350755 447439 := bstep (se 1 (by rfl) ⟨335579, by rfl⟩ : syracuseStep 447439 = 671159) B671159
theorem B447707 : Blo 350755 447707 := bstep (se 1 (by rfl) ⟨335780, by rfl⟩ : syracuseStep 447707 = 671561) B671561
theorem B3003641 : Blo 350755 3003641 := bstep (se 2 (by rfl) ⟨1126365, by rfl⟩ : syracuseStep 3003641 = 2252731) B2252731
theorem B1692971 : Blo 350755 1692971 := bstep (se 1 (by rfl) ⟨1269728, by rfl⟩ : syracuseStep 1692971 = 2539457) B2539457
theorem B448183 : Blo 350755 448183 := bstep (se 1 (by rfl) ⟨336137, by rfl⟩ : syracuseStep 448183 = 672275) B672275
theorem B448411 : Blo 350755 448411 := bstep (se 1 (by rfl) ⟨336308, by rfl⟩ : syracuseStep 448411 = 672617) B672617
theorem B4512023 : Blo 350755 4512023 := bstep (se 1 (by rfl) ⟨3384017, by rfl⟩ : syracuseStep 4512023 = 6768035) B6768035
theorem B1792367 : Blo 350755 1792367 := bstep (se 1 (by rfl) ⟨1344275, by rfl⟩ : syracuseStep 1792367 = 2688551) B2688551
theorem B6805943 : Blo 350755 6805943 := bstep (se 1 (by rfl) ⟨5104457, by rfl⟩ : syracuseStep 6805943 = 10208915) B10208915
theorem B350783 : Blo 350755 350783 := bstep (se 1 (by rfl) ⟨263087, by rfl⟩ : syracuseStep 350783 = 526175) B526175
theorem B350791 : Blo 350755 350791 := bstep (se 1 (by rfl) ⟨263093, by rfl⟩ : syracuseStep 350791 = 526187) B526187
theorem B350943 : Blo 350755 350943 := bstep (se 1 (by rfl) ⟨263207, by rfl⟩ : syracuseStep 350943 = 526415) B526415
theorem B351023 : Blo 350755 351023 := bstep (se 1 (by rfl) ⟨263267, by rfl⟩ : syracuseStep 351023 = 526535) B526535
theorem B351131 : Blo 350755 351131 := bstep (se 1 (by rfl) ⟨263348, by rfl⟩ : syracuseStep 351131 = 526697) B526697
theorem B711595 : Blo 350755 711595 := bstep (se 1 (by rfl) ⟨533696, by rfl⟩ : syracuseStep 711595 = 1067393) B1067393
theorem B351183 : Blo 350755 351183 := bstep (se 1 (by rfl) ⟨263387, by rfl⟩ : syracuseStep 351183 = 526775) B526775
theorem B351207 : Blo 350755 351207 := bstep (se 1 (by rfl) ⟨263405, by rfl⟩ : syracuseStep 351207 = 526811) B526811
theorem B3660923 : Blo 350755 3660923 := bstep (se 1 (by rfl) ⟨2745692, by rfl⟩ : syracuseStep 3660923 = 5491385) B5491385
theorem B1498301 : Blo 350755 1498301 := bstep (se 3 (by rfl) ⟨280931, by rfl⟩ : syracuseStep 1498301 = 561863) B561863
theorem B5790937 : Blo 350755 5790937 := bstep (se 2 (by rfl) ⟨2171601, by rfl⟩ : syracuseStep 5790937 = 4343203) B4343203
theorem B351519 : Blo 350755 351519 := bstep (se 1 (by rfl) ⟨263639, by rfl⟩ : syracuseStep 351519 = 527279) B527279
theorem B351579 : Blo 350755 351579 := bstep (se 1 (by rfl) ⟨263684, by rfl⟩ : syracuseStep 351579 = 527369) B527369
theorem B351599 : Blo 350755 351599 := bstep (se 1 (by rfl) ⟨263699, by rfl⟩ : syracuseStep 351599 = 527399) B527399
theorem B351655 : Blo 350755 351655 := bstep (se 1 (by rfl) ⟨263741, by rfl⟩ : syracuseStep 351655 = 527483) B527483
theorem B3366359 : Blo 350755 3366359 := bstep (se 1 (by rfl) ⟨2524769, by rfl⟩ : syracuseStep 3366359 = 5049539) B5049539
theorem B351739 : Blo 350755 351739 := bstep (se 1 (by rfl) ⟨263804, by rfl⟩ : syracuseStep 351739 = 527609) B527609
theorem B351807 : Blo 350755 351807 := bstep (se 1 (by rfl) ⟨263855, by rfl⟩ : syracuseStep 351807 = 527711) B527711
theorem B351815 : Blo 350755 351815 := bstep (se 1 (by rfl) ⟨263861, by rfl⟩ : syracuseStep 351815 = 527723) B527723
theorem B679519 : Blo 350755 679519 := bstep (se 1 (by rfl) ⟨509639, by rfl⟩ : syracuseStep 679519 = 1019279) B1019279
theorem B3825269 : Blo 350755 3825269 := bstep (se 5 (by rfl) ⟨179309, by rfl⟩ : syracuseStep 3825269 = 358619) B358619
theorem B351967 : Blo 350755 351967 := bstep (se 1 (by rfl) ⟨263975, by rfl⟩ : syracuseStep 351967 = 527951) B527951
theorem B352047 : Blo 350755 352047 := bstep (se 1 (by rfl) ⟨264035, by rfl⟩ : syracuseStep 352047 = 528071) B528071
theorem B352155 : Blo 350755 352155 := bstep (se 1 (by rfl) ⟨264116, by rfl⟩ : syracuseStep 352155 = 528233) B528233
theorem B352207 : Blo 350755 352207 := bstep (se 1 (by rfl) ⟨264155, by rfl⟩ : syracuseStep 352207 = 528311) B528311
theorem B352231 : Blo 350755 352231 := bstep (se 1 (by rfl) ⟨264173, by rfl⟩ : syracuseStep 352231 = 528347) B528347
theorem B8740871 : Blo 350755 8740871 := bstep (se 1 (by rfl) ⟨6555653, by rfl⟩ : syracuseStep 8740871 = 13111307) B13111307
theorem B8609969 : Blo 350755 8609969 := bstep (se 2 (by rfl) ⟨3228738, by rfl⟩ : syracuseStep 8609969 = 6457477) B6457477
theorem B352543 : Blo 350755 352543 := bstep (se 1 (by rfl) ⟨264407, by rfl⟩ : syracuseStep 352543 = 528815) B528815
theorem B352603 : Blo 350755 352603 := bstep (se 1 (by rfl) ⟨264452, by rfl⟩ : syracuseStep 352603 = 528905) B528905
theorem B352623 : Blo 350755 352623 := bstep (se 1 (by rfl) ⟨264467, by rfl⟩ : syracuseStep 352623 = 528935) B528935
theorem B352679 : Blo 350755 352679 := bstep (se 1 (by rfl) ⟨264509, by rfl⟩ : syracuseStep 352679 = 529019) B529019
theorem B352763 : Blo 350755 352763 := bstep (se 1 (by rfl) ⟨264572, by rfl⟩ : syracuseStep 352763 = 529145) B529145
theorem B352831 : Blo 350755 352831 := bstep (se 1 (by rfl) ⟨264623, by rfl⟩ : syracuseStep 352831 = 529247) B529247
theorem B352839 : Blo 350755 352839 := bstep (se 1 (by rfl) ⟨264629, by rfl⟩ : syracuseStep 352839 = 529259) B529259
theorem B352991 : Blo 350755 352991 := bstep (se 1 (by rfl) ⟨264743, by rfl⟩ : syracuseStep 352991 = 529487) B529487
theorem B353071 : Blo 350755 353071 := bstep (se 1 (by rfl) ⟨264803, by rfl⟩ : syracuseStep 353071 = 529607) B529607
theorem B5530463 : Blo 350755 5530463 := bstep (se 1 (by rfl) ⟨4147847, by rfl⟩ : syracuseStep 5530463 = 8295695) B8295695
theorem B353179 : Blo 350755 353179 := bstep (se 1 (by rfl) ⟨264884, by rfl⟩ : syracuseStep 353179 = 529769) B529769
theorem B353231 : Blo 350755 353231 := bstep (se 1 (by rfl) ⟨264923, by rfl⟩ : syracuseStep 353231 = 529847) B529847
theorem B353255 : Blo 350755 353255 := bstep (se 1 (by rfl) ⟨264941, by rfl⟩ : syracuseStep 353255 = 529883) B529883
theorem B1500403 : Blo 350755 1500403 := bstep (se 1 (by rfl) ⟨1125302, by rfl⟩ : syracuseStep 1500403 = 2250605) B2250605
theorem B353567 : Blo 350755 353567 := bstep (se 1 (by rfl) ⟨265175, by rfl⟩ : syracuseStep 353567 = 530351) B530351
theorem B353627 : Blo 350755 353627 := bstep (se 1 (by rfl) ⟨265220, by rfl⟩ : syracuseStep 353627 = 530441) B530441
theorem B353647 : Blo 350755 353647 := bstep (se 1 (by rfl) ⟨265235, by rfl⟩ : syracuseStep 353647 = 530471) B530471
theorem B353703 : Blo 350755 353703 := bstep (se 1 (by rfl) ⟨265277, by rfl⟩ : syracuseStep 353703 = 530555) B530555
theorem B845255 : Blo 350755 845255 := bstep (se 1 (by rfl) ⟨633941, by rfl⟩ : syracuseStep 845255 = 1267883) B1267883
theorem B353787 : Blo 350755 353787 := bstep (se 1 (by rfl) ⟨265340, by rfl⟩ : syracuseStep 353787 = 530681) B530681
theorem B353855 : Blo 350755 353855 := bstep (se 1 (by rfl) ⟨265391, by rfl⟩ : syracuseStep 353855 = 530783) B530783
theorem B353863 : Blo 350755 353863 := bstep (se 1 (by rfl) ⟨265397, by rfl⟩ : syracuseStep 353863 = 530795) B530795
theorem B1795769 : Blo 350755 1795769 := bstep (se 2 (by rfl) ⟨673413, by rfl⟩ : syracuseStep 1795769 = 1346827) B1346827
theorem B354015 : Blo 350755 354015 := bstep (se 1 (by rfl) ⟨265511, by rfl⟩ : syracuseStep 354015 = 531023) B531023
theorem B354095 : Blo 350755 354095 := bstep (se 1 (by rfl) ⟨265571, by rfl⟩ : syracuseStep 354095 = 531143) B531143
theorem B354203 : Blo 350755 354203 := bstep (se 1 (by rfl) ⟨265652, by rfl⟩ : syracuseStep 354203 = 531305) B531305
theorem B354255 : Blo 350755 354255 := bstep (se 1 (by rfl) ⟨265691, by rfl⟩ : syracuseStep 354255 = 531383) B531383
theorem B354279 : Blo 350755 354279 := bstep (se 1 (by rfl) ⟨265709, by rfl⟩ : syracuseStep 354279 = 531419) B531419
theorem B4516019 : Blo 350755 4516019 := bstep (se 1 (by rfl) ⟨3387014, by rfl⟩ : syracuseStep 4516019 = 6774029) B6774029
theorem B3008765 : Blo 350755 3008765 := bstep (se 3 (by rfl) ⟨564143, by rfl⟩ : syracuseStep 3008765 = 1128287) B1128287
theorem B354591 : Blo 350755 354591 := bstep (se 1 (by rfl) ⟨265943, by rfl⟩ : syracuseStep 354591 = 531887) B531887
theorem B354651 : Blo 350755 354651 := bstep (se 1 (by rfl) ⟨265988, by rfl⟩ : syracuseStep 354651 = 531977) B531977
theorem B354671 : Blo 350755 354671 := bstep (se 1 (by rfl) ⟨266003, by rfl⟩ : syracuseStep 354671 = 532007) B532007
theorem B354727 : Blo 350755 354727 := bstep (se 1 (by rfl) ⟨266045, by rfl⟩ : syracuseStep 354727 = 532091) B532091
theorem B2681261 : Blo 350755 2681261 := bstep (se 3 (by rfl) ⟨502736, by rfl⟩ : syracuseStep 2681261 = 1005473) B1005473
theorem B1338839 : Blo 350755 1338839 := bstep (se 1 (by rfl) ⟨1004129, by rfl⟩ : syracuseStep 1338839 = 2008259) B2008259
theorem B1437497 : Blo 350755 1437497 := bstep (se 2 (by rfl) ⟨539061, by rfl⟩ : syracuseStep 1437497 = 1078123) B1078123
theorem B5828561 : Blo 350755 5828561 := bstep (se 2 (by rfl) ⟨2185710, by rfl⟩ : syracuseStep 5828561 = 4371421) B4371421
theorem B2224691 : Blo 350755 2224691 := bstep (se 1 (by rfl) ⟨1668518, by rfl⟩ : syracuseStep 2224691 = 3337037) B3337037
theorem B2683691 : Blo 350755 2683691 := bstep (se 1 (by rfl) ⟨2012768, by rfl⟩ : syracuseStep 2683691 = 4025537) B4025537
theorem B1504109 : Blo 350755 1504109 := bstep (se 3 (by rfl) ⟨282020, by rfl⟩ : syracuseStep 1504109 = 564041) B564041
theorem B1897411 : Blo 350755 1897411 := bstep (se 1 (by rfl) ⟨1423058, by rfl⟩ : syracuseStep 1897411 = 2846117) B2846117
theorem B3011741 : Blo 350755 3011741 := bstep (se 3 (by rfl) ⟨564701, by rfl⟩ : syracuseStep 3011741 = 1129403) B1129403
theorem B750791 : Blo 350755 750791 := bstep (se 1 (by rfl) ⟨563093, by rfl⟩ : syracuseStep 750791 = 1126187) B1126187
theorem B1733881 : Blo 350755 1733881 := bstep (se 2 (by rfl) ⟨650205, by rfl⟩ : syracuseStep 1733881 = 1300411) B1300411
theorem B8189207 : Blo 350755 8189207 := bstep (se 1 (by rfl) ⟨6141905, by rfl⟩ : syracuseStep 8189207 = 12283811) B12283811
theorem B4519709 : Blo 350755 4519709 := bstep (se 3 (by rfl) ⟨847445, by rfl⟩ : syracuseStep 4519709 = 1694891) B1694891
theorem B423911 : Blo 350755 423911 := bstep (se 1 (by rfl) ⟨317933, by rfl⟩ : syracuseStep 423911 = 635867) B635867
theorem B719113 : Blo 350755 719113 := bstep (se 2 (by rfl) ⟨269667, by rfl⟩ : syracuseStep 719113 = 539335) B539335
theorem B751979 : Blo 350755 751979 := bstep (se 1 (by rfl) ⟨563984, by rfl⟩ : syracuseStep 751979 = 1127969) B1127969
theorem B850283 : Blo 350755 850283 := bstep (se 1 (by rfl) ⟨637712, by rfl⟩ : syracuseStep 850283 = 1275425) B1275425
theorem B15464945 : Blo 350755 15464945 := bstep (se 2 (by rfl) ⟨5799354, by rfl⟩ : syracuseStep 15464945 = 11598709) B11598709
theorem B752123 : Blo 350755 752123 := bstep (se 1 (by rfl) ⟨564092, by rfl⟩ : syracuseStep 752123 = 1128185) B1128185
theorem B12909131 : Blo 350755 12909131 := bstep (se 1 (by rfl) ⟨9681848, by rfl⟩ : syracuseStep 12909131 = 19363697) B19363697
theorem B2685635 : Blo 350755 2685635 := bstep (se 1 (by rfl) ⟨2014226, by rfl⟩ : syracuseStep 2685635 = 4028453) B4028453
theorem B949391 : Blo 350755 949391 := bstep (se 1 (by rfl) ⟨712043, by rfl⟩ : syracuseStep 949391 = 1424087) B1424087
theorem B1506775 : Blo 350755 1506775 := bstep (se 1 (by rfl) ⟨1130081, by rfl⟩ : syracuseStep 1506775 = 2260163) B2260163
theorem B753209 : Blo 350755 753209 := bstep (se 2 (by rfl) ⟨282453, by rfl⟩ : syracuseStep 753209 = 564907) B564907
theorem B1343243 : Blo 350755 1343243 := bstep (se 1 (by rfl) ⟨1007432, by rfl⟩ : syracuseStep 1343243 = 2014865) B2014865
theorem B1999079 : Blo 350755 1999079 := bstep (se 1 (by rfl) ⟨1499309, by rfl⟩ : syracuseStep 1999079 = 2998619) B2998619
theorem B1507835 : Blo 350755 1507835 := bstep (se 1 (by rfl) ⟨1130876, by rfl⟩ : syracuseStep 1507835 = 2261753) B2261753
theorem B2556467 : Blo 350755 2556467 := bstep (se 1 (by rfl) ⟨1917350, by rfl⟩ : syracuseStep 2556467 = 3834701) B3834701
theorem B1376831 : Blo 350755 1376831 := bstep (se 1 (by rfl) ⟨1032623, by rfl⟩ : syracuseStep 1376831 = 2065247) B2065247
theorem B2261803 : Blo 350755 2261803 := bstep (se 1 (by rfl) ⟨1696352, by rfl⟩ : syracuseStep 2261803 = 3392705) B3392705
theorem B2000537 : Blo 350755 2000537 := bstep (se 2 (by rfl) ⟨750201, by rfl⟩ : syracuseStep 2000537 = 1500403) B1500403
theorem B526217 : Blo 350755 526217 := bstep (se 2 (by rfl) ⟨197331, by rfl⟩ : syracuseStep 526217 = 394663) B394663
theorem B526319 : Blo 350755 526319 := bstep (se 1 (by rfl) ⟨394739, by rfl⟩ : syracuseStep 526319 = 789479) B789479
theorem B592015 : Blo 350755 592015 := bstep (se 1 (by rfl) ⟨444011, by rfl⟩ : syracuseStep 592015 = 888023) B888023
theorem B395419 : Blo 350755 395419 := bstep (se 1 (by rfl) ⟨296564, by rfl⟩ : syracuseStep 395419 = 593129) B593129
theorem B395455 : Blo 350755 395455 := bstep (se 1 (by rfl) ⟨296591, by rfl⟩ : syracuseStep 395455 = 593183) B593183
theorem B526571 : Blo 350755 526571 := bstep (se 1 (by rfl) ⟨394928, by rfl⟩ : syracuseStep 526571 = 789857) B789857
theorem B3639563 : Blo 350755 3639563 := bstep (se 1 (by rfl) ⟨2729672, by rfl⟩ : syracuseStep 3639563 = 5459345) B5459345
theorem B526631 : Blo 350755 526631 := bstep (se 1 (by rfl) ⟨394973, by rfl⟩ : syracuseStep 526631 = 789947) B789947
theorem B526715 : Blo 350755 526715 := bstep (se 1 (by rfl) ⟨395036, by rfl⟩ : syracuseStep 526715 = 790073) B790073
theorem B1968745 : Blo 350755 1968745 := bstep (se 2 (by rfl) ⟨738279, by rfl⟩ : syracuseStep 1968745 = 1476559) B1476559
theorem B526985 : Blo 350755 526985 := bstep (se 2 (by rfl) ⟨197619, by rfl⟩ : syracuseStep 526985 = 395239) B395239
theorem B527159 : Blo 350755 527159 := bstep (se 1 (by rfl) ⟨395369, by rfl⟩ : syracuseStep 527159 = 790739) B790739
theorem B527195 : Blo 350755 527195 := bstep (se 1 (by rfl) ⟨395396, by rfl⟩ : syracuseStep 527195 = 790793) B790793
theorem B3378095 : Blo 350755 3378095 := bstep (se 1 (by rfl) ⟨2533571, by rfl⟩ : syracuseStep 3378095 = 5067143) B5067143
theorem B527339 : Blo 350755 527339 := bstep (se 1 (by rfl) ⟨395504, by rfl⟩ : syracuseStep 527339 = 791009) B791009
theorem B36637717 : Blo 350755 36637717 := bstep (se 6 (by rfl) ⟨858696, by rfl⟩ : syracuseStep 36637717 = 1717393) B1717393
theorem B1510433 : Blo 350755 1510433 := bstep (se 2 (by rfl) ⟨566412, by rfl⟩ : syracuseStep 1510433 = 1132825) B1132825
theorem B789551 : Blo 350755 789551 := bstep (se 1 (by rfl) ⟨592163, by rfl⟩ : syracuseStep 789551 = 1184327) B1184327
theorem B592967 : Blo 350755 592967 := bstep (se 1 (by rfl) ⟨444725, by rfl⟩ : syracuseStep 592967 = 889451) B889451
theorem B756857 : Blo 350755 756857 := bstep (se 2 (by rfl) ⟨283821, by rfl⟩ : syracuseStep 756857 = 567643) B567643
theorem B527543 : Blo 350755 527543 := bstep (se 1 (by rfl) ⟨395657, by rfl⟩ : syracuseStep 527543 = 791315) B791315
theorem B789839 : Blo 350755 789839 := bstep (se 1 (by rfl) ⟨592379, by rfl⟩ : syracuseStep 789839 = 1184759) B1184759
theorem B527783 : Blo 350755 527783 := bstep (se 1 (by rfl) ⟨395837, by rfl⟩ : syracuseStep 527783 = 791675) B791675
theorem B789929 : Blo 350755 789929 := bstep (se 2 (by rfl) ⟨296223, by rfl⟩ : syracuseStep 789929 = 592447) B592447
theorem B593399 : Blo 350755 593399 := bstep (se 1 (by rfl) ⟨445049, by rfl⟩ : syracuseStep 593399 = 890099) B890099
theorem B2002427 : Blo 350755 2002427 := bstep (se 1 (by rfl) ⟨1501820, by rfl⟩ : syracuseStep 2002427 = 3003641) B3003641
theorem B527867 : Blo 350755 527867 := bstep (se 1 (by rfl) ⟨395900, by rfl⟩ : syracuseStep 527867 = 791801) B791801
theorem B2297339 : Blo 350755 2297339 := bstep (se 1 (by rfl) ⟨1723004, by rfl⟩ : syracuseStep 2297339 = 3446009) B3446009
theorem B527963 : Blo 350755 527963 := bstep (se 1 (by rfl) ⟨395972, by rfl⟩ : syracuseStep 527963 = 791945) B791945
theorem B528047 : Blo 350755 528047 := bstep (se 1 (by rfl) ⟨396035, by rfl⟩ : syracuseStep 528047 = 792071) B792071
theorem B528167 : Blo 350755 528167 := bstep (se 1 (by rfl) ⟨396125, by rfl⟩ : syracuseStep 528167 = 792251) B792251
theorem B528251 : Blo 350755 528251 := bstep (se 1 (by rfl) ⟨396188, by rfl⟩ : syracuseStep 528251 = 792377) B792377
theorem B790415 : Blo 350755 790415 := bstep (se 1 (by rfl) ⟨592811, by rfl⟩ : syracuseStep 790415 = 1185623) B1185623
theorem B397543 : Blo 350755 397543 := bstep (se 1 (by rfl) ⟨298157, by rfl⟩ : syracuseStep 397543 = 596315) B596315
theorem B528671 : Blo 350755 528671 := bstep (se 1 (by rfl) ⟨396503, by rfl⟩ : syracuseStep 528671 = 793007) B793007
theorem B528695 : Blo 350755 528695 := bstep (se 1 (by rfl) ⟨396521, by rfl⟩ : syracuseStep 528695 = 793043) B793043
theorem B1184111 : Blo 350755 1184111 := bstep (se 1 (by rfl) ⟨888083, by rfl⟩ : syracuseStep 1184111 = 1776167) B1776167
theorem B528767 : Blo 350755 528767 := bstep (se 1 (by rfl) ⟨396575, by rfl⟩ : syracuseStep 528767 = 793151) B793151
theorem B528839 : Blo 350755 528839 := bstep (se 1 (by rfl) ⟨396629, by rfl⟩ : syracuseStep 528839 = 793259) B793259
theorem B594425 : Blo 350755 594425 := bstep (se 2 (by rfl) ⟨222909, by rfl⟩ : syracuseStep 594425 = 445819) B445819
theorem B791135 : Blo 350755 791135 := bstep (se 1 (by rfl) ⟨593351, by rfl⟩ : syracuseStep 791135 = 1186703) B1186703
theorem B594695 : Blo 350755 594695 := bstep (se 1 (by rfl) ⟨446021, by rfl⟩ : syracuseStep 594695 = 892043) B892043
theorem B529193 : Blo 350755 529193 := bstep (se 2 (by rfl) ⟨198447, by rfl⟩ : syracuseStep 529193 = 396895) B396895
theorem B529199 : Blo 350755 529199 := bstep (se 1 (by rfl) ⟨396899, by rfl⟩ : syracuseStep 529199 = 793799) B793799
theorem B3937085 : Blo 350755 3937085 := bstep (se 3 (by rfl) ⟨738203, by rfl⟩ : syracuseStep 3937085 = 1476407) B1476407
theorem B398191 : Blo 350755 398191 := bstep (se 1 (by rfl) ⟨298643, by rfl⟩ : syracuseStep 398191 = 597287) B597287
theorem B529319 : Blo 350755 529319 := bstep (se 1 (by rfl) ⟨396989, by rfl⟩ : syracuseStep 529319 = 793979) B793979
theorem B529403 : Blo 350755 529403 := bstep (se 1 (by rfl) ⟨397052, by rfl⟩ : syracuseStep 529403 = 794105) B794105
theorem B529463 : Blo 350755 529463 := bstep (se 1 (by rfl) ⟨397097, by rfl⟩ : syracuseStep 529463 = 794195) B794195
theorem B9311377 : Blo 350755 9311377 := bstep (se 2 (by rfl) ⟨3491766, by rfl⟩ : syracuseStep 9311377 = 6983533) B6983533
theorem B529583 : Blo 350755 529583 := bstep (se 1 (by rfl) ⟨397187, by rfl⟩ : syracuseStep 529583 = 794375) B794375
theorem B2692439 : Blo 350755 2692439 := bstep (se 1 (by rfl) ⟨2019329, by rfl⟩ : syracuseStep 2692439 = 4038659) B4038659
theorem B791963 : Blo 350755 791963 := bstep (se 1 (by rfl) ⟨593972, by rfl⟩ : syracuseStep 791963 = 1187945) B1187945
theorem B5739979 : Blo 350755 5739979 := bstep (se 1 (by rfl) ⟨4304984, by rfl⟩ : syracuseStep 5739979 = 8609969) B8609969
theorem B529991 : Blo 350755 529991 := bstep (se 1 (by rfl) ⟨397493, by rfl⟩ : syracuseStep 529991 = 794987) B794987
theorem B530087 : Blo 350755 530087 := bstep (se 1 (by rfl) ⟨397565, by rfl⟩ : syracuseStep 530087 = 795131) B795131
theorem B1185515 : Blo 350755 1185515 := bstep (se 1 (by rfl) ⟨889136, by rfl⟩ : syracuseStep 1185515 = 1778273) B1778273
theorem B530171 : Blo 350755 530171 := bstep (se 1 (by rfl) ⟨397628, by rfl⟩ : syracuseStep 530171 = 795257) B795257
theorem B530207 : Blo 350755 530207 := bstep (se 1 (by rfl) ⟨397655, by rfl⟩ : syracuseStep 530207 = 795311) B795311
theorem B595775 : Blo 350755 595775 := bstep (se 1 (by rfl) ⟨446831, by rfl⟩ : syracuseStep 595775 = 893663) B893663
theorem B530255 : Blo 350755 530255 := bstep (se 1 (by rfl) ⟨397691, by rfl⟩ : syracuseStep 530255 = 795383) B795383
theorem B595849 : Blo 350755 595849 := bstep (se 2 (by rfl) ⟨223443, by rfl⟩ : syracuseStep 595849 = 446887) B446887
theorem B530375 : Blo 350755 530375 := bstep (se 1 (by rfl) ⟨397781, by rfl⟩ : syracuseStep 530375 = 795563) B795563
theorem B792539 : Blo 350755 792539 := bstep (se 1 (by rfl) ⟨594404, by rfl⟩ : syracuseStep 792539 = 1188809) B1188809
theorem B1185785 : Blo 350755 1185785 := bstep (se 2 (by rfl) ⟨444669, by rfl⟩ : syracuseStep 1185785 = 889339) B889339
theorem B792719 : Blo 350755 792719 := bstep (se 1 (by rfl) ⟨594539, by rfl⟩ : syracuseStep 792719 = 1189079) B1189079
theorem B1185947 : Blo 350755 1185947 := bstep (se 1 (by rfl) ⟨889460, by rfl⟩ : syracuseStep 1185947 = 1778921) B1778921
theorem B792737 : Blo 350755 792737 := bstep (se 2 (by rfl) ⟨297276, by rfl⟩ : syracuseStep 792737 = 594553) B594553
theorem B792809 : Blo 350755 792809 := bstep (se 2 (by rfl) ⟨297303, by rfl⟩ : syracuseStep 792809 = 594607) B594607
theorem B1186055 : Blo 350755 1186055 := bstep (se 1 (by rfl) ⟨889541, by rfl⟩ : syracuseStep 1186055 = 1779083) B1779083
theorem B530729 : Blo 350755 530729 := bstep (se 2 (by rfl) ⟨199023, by rfl⟩ : syracuseStep 530729 = 398047) B398047
theorem B530735 : Blo 350755 530735 := bstep (se 1 (by rfl) ⟨398051, by rfl⟩ : syracuseStep 530735 = 796103) B796103
theorem B596281 : Blo 350755 596281 := bstep (se 2 (by rfl) ⟨223605, by rfl⟩ : syracuseStep 596281 = 447211) B447211
theorem B4069757 : Blo 350755 4069757 := bstep (se 3 (by rfl) ⟨763079, by rfl⟩ : syracuseStep 4069757 = 1526159) B1526159
theorem B21142037 : Blo 350755 21142037 := bstep (se 6 (by rfl) ⟨495516, by rfl⟩ : syracuseStep 21142037 = 991033) B991033
theorem B530975 : Blo 350755 530975 := bstep (se 1 (by rfl) ⟨398231, by rfl⟩ : syracuseStep 530975 = 796463) B796463
theorem B2529881 : Blo 350755 2529881 := bstep (se 2 (by rfl) ⟨948705, by rfl⟩ : syracuseStep 2529881 = 1897411) B1897411
theorem B596585 : Blo 350755 596585 := bstep (se 2 (by rfl) ⟨223719, by rfl⟩ : syracuseStep 596585 = 447439) B447439
theorem B2005661 : Blo 350755 2005661 := bstep (se 3 (by rfl) ⟨376061, by rfl⟩ : syracuseStep 2005661 = 752123) B752123
theorem B2005843 : Blo 350755 2005843 := bstep (se 1 (by rfl) ⟨1504382, by rfl⟩ : syracuseStep 2005843 = 3008765) B3008765
theorem B531359 : Blo 350755 531359 := bstep (se 1 (by rfl) ⟨398519, by rfl⟩ : syracuseStep 531359 = 797039) B797039
theorem B531407 : Blo 350755 531407 := bstep (se 1 (by rfl) ⟨398555, by rfl⟩ : syracuseStep 531407 = 797111) B797111
theorem B531497 : Blo 350755 531497 := bstep (se 2 (by rfl) ⟨199311, by rfl⟩ : syracuseStep 531497 = 398623) B398623
theorem B531503 : Blo 350755 531503 := bstep (se 1 (by rfl) ⟨398627, by rfl⟩ : syracuseStep 531503 = 797255) B797255
theorem B531527 : Blo 350755 531527 := bstep (se 1 (by rfl) ⟨398645, by rfl⟩ : syracuseStep 531527 = 797291) B797291
theorem B2891009 : Blo 350755 2891009 := bstep (se 2 (by rfl) ⟨1084128, by rfl⟩ : syracuseStep 2891009 = 2168257) B2168257
theorem B1187081 : Blo 350755 1187081 := bstep (se 2 (by rfl) ⟨445155, by rfl⟩ : syracuseStep 1187081 = 890311) B890311
theorem B531791 : Blo 350755 531791 := bstep (se 1 (by rfl) ⟨398843, by rfl⟩ : syracuseStep 531791 = 797687) B797687
theorem B597415 : Blo 350755 597415 := bstep (se 1 (by rfl) ⟨448061, by rfl⟩ : syracuseStep 597415 = 896123) B896123
theorem B531881 : Blo 350755 531881 := bstep (se 2 (by rfl) ⟨199455, by rfl⟩ : syracuseStep 531881 = 398911) B398911
theorem B794087 : Blo 350755 794087 := bstep (se 1 (by rfl) ⟨595565, by rfl⟩ : syracuseStep 794087 = 1191131) B1191131
theorem B532031 : Blo 350755 532031 := bstep (se 1 (by rfl) ⟨399023, by rfl⟩ : syracuseStep 532031 = 798047) B798047
theorem B597577 : Blo 350755 597577 := bstep (se 2 (by rfl) ⟨224091, by rfl⟩ : syracuseStep 597577 = 448183) B448183
theorem B597611 : Blo 350755 597611 := bstep (se 1 (by rfl) ⟨448208, by rfl⟩ : syracuseStep 597611 = 896417) B896417
theorem B892559 : Blo 350755 892559 := bstep (se 1 (by rfl) ⟨669419, by rfl⟩ : syracuseStep 892559 = 1338839) B1338839
theorem B1908467 : Blo 350755 1908467 := bstep (se 1 (by rfl) ⟨1431350, by rfl⟩ : syracuseStep 1908467 = 2862701) B2862701
theorem B1777463 : Blo 350755 1777463 := bstep (se 1 (by rfl) ⟨1333097, by rfl⟩ : syracuseStep 1777463 = 2666195) B2666195
theorem B597881 : Blo 350755 597881 := bstep (se 2 (by rfl) ⟨224205, by rfl⟩ : syracuseStep 597881 = 448411) B448411
theorem B958331 : Blo 350755 958331 := bstep (se 1 (by rfl) ⟨718748, by rfl⟩ : syracuseStep 958331 = 1437497) B1437497
theorem B794663 : Blo 350755 794663 := bstep (se 1 (by rfl) ⟨595997, by rfl⟩ : syracuseStep 794663 = 1191995) B1191995
theorem B794843 : Blo 350755 794843 := bstep (se 1 (by rfl) ⟨596132, by rfl⟩ : syracuseStep 794843 = 1192265) B1192265
theorem B958817 : Blo 350755 958817 := bstep (se 2 (by rfl) ⟨359556, by rfl⟩ : syracuseStep 958817 = 719113) B719113
theorem B1483127 : Blo 350755 1483127 := bstep (se 1 (by rfl) ⟨1112345, by rfl⟩ : syracuseStep 1483127 = 2224691) B2224691
theorem B1188215 : Blo 350755 1188215 := bstep (se 1 (by rfl) ⟨891161, by rfl⟩ : syracuseStep 1188215 = 1782323) B1782323
theorem B795113 : Blo 350755 795113 := bstep (se 2 (by rfl) ⟨298167, by rfl⟩ : syracuseStep 795113 = 596335) B596335
theorem B795401 : Blo 350755 795401 := bstep (se 2 (by rfl) ⟨298275, by rfl⟩ : syracuseStep 795401 = 596551) B596551
theorem B2007827 : Blo 350755 2007827 := bstep (se 1 (by rfl) ⟨1505870, by rfl⟩ : syracuseStep 2007827 = 3011741) B3011741
theorem B500527 : Blo 350755 500527 := bstep (se 1 (by rfl) ⟨375395, by rfl⟩ : syracuseStep 500527 = 750791) B750791
theorem B533611 : Blo 350755 533611 := bstep (se 1 (by rfl) ⟨400208, by rfl⟩ : syracuseStep 533611 = 800417) B800417
theorem B795977 : Blo 350755 795977 := bstep (se 2 (by rfl) ⟨298491, by rfl⟩ : syracuseStep 795977 = 596983) B596983
theorem B1189295 : Blo 350755 1189295 := bstep (se 1 (by rfl) ⟨891971, by rfl⟩ : syracuseStep 1189295 = 1783943) B1783943
theorem B501319 : Blo 350755 501319 := bstep (se 1 (by rfl) ⟨375989, by rfl⟩ : syracuseStep 501319 = 751979) B751979
theorem B566855 : Blo 350755 566855 := bstep (se 1 (by rfl) ⟨425141, by rfl⟩ : syracuseStep 566855 = 850283) B850283
theorem B1189673 : Blo 350755 1189673 := bstep (se 2 (by rfl) ⟨446127, by rfl⟩ : syracuseStep 1189673 = 892255) B892255
theorem B2009033 : Blo 350755 2009033 := bstep (se 2 (by rfl) ⟨753387, by rfl⟩ : syracuseStep 2009033 = 1506775) B1506775
theorem B1779731 : Blo 350755 1779731 := bstep (se 1 (by rfl) ⟨1334798, by rfl⟩ : syracuseStep 1779731 = 2669597) B2669597
theorem B632927 : Blo 350755 632927 := bstep (se 1 (by rfl) ⟨474695, by rfl⟩ : syracuseStep 632927 = 949391) B949391
theorem B796967 : Blo 350755 796967 := bstep (se 1 (by rfl) ⟨597725, by rfl⟩ : syracuseStep 796967 = 1195451) B1195451
theorem B796985 : Blo 350755 796985 := bstep (se 2 (by rfl) ⟨298869, by rfl⟩ : syracuseStep 796985 = 597739) B597739
theorem B502139 : Blo 350755 502139 := bstep (se 1 (by rfl) ⟨376604, by rfl⟩ : syracuseStep 502139 = 753209) B753209
theorem B895495 : Blo 350755 895495 := bstep (se 1 (by rfl) ⟨671621, by rfl⟩ : syracuseStep 895495 = 1343243) B1343243
theorem B666139 : Blo 350755 666139 := bstep (se 1 (by rfl) ⟨499604, by rfl⟩ : syracuseStep 666139 = 999209) B999209
theorem B666299 : Blo 350755 666299 := bstep (se 1 (by rfl) ⟨499724, by rfl⟩ : syracuseStep 666299 = 999449) B999449
theorem B895799 : Blo 350755 895799 := bstep (se 1 (by rfl) ⟨671849, by rfl⟩ : syracuseStep 895799 = 1343699) B1343699
theorem B1911815 : Blo 350755 1911815 := bstep (se 1 (by rfl) ⟨1433861, by rfl⟩ : syracuseStep 1911815 = 2867723) B2867723
theorem B1289449 : Blo 350755 1289449 := bstep (se 2 (by rfl) ⟨483543, by rfl⟩ : syracuseStep 1289449 = 967087) B967087
theorem B37007117 : Blo 350755 37007117 := bstep (se 3 (by rfl) ⟨6938834, by rfl⟩ : syracuseStep 37007117 = 13877669) B13877669
theorem B1191887 : Blo 350755 1191887 := bstep (se 1 (by rfl) ⟨893915, by rfl⟩ : syracuseStep 1191887 = 1787831) B1787831
theorem B1192319 : Blo 350755 1192319 := bstep (se 1 (by rfl) ⟨894239, by rfl⟩ : syracuseStep 1192319 = 1788479) B1788479
theorem B504263 : Blo 350755 504263 := bstep (se 1 (by rfl) ⟨378197, by rfl⟩ : syracuseStep 504263 = 756395) B756395
theorem B635369 : Blo 350755 635369 := bstep (se 2 (by rfl) ⟨238263, by rfl⟩ : syracuseStep 635369 = 476527) B476527
theorem B668243 : Blo 350755 668243 := bstep (se 1 (by rfl) ⟨501182, by rfl⟩ : syracuseStep 668243 = 1002365) B1002365
theorem B1356371 : Blo 350755 1356371 := bstep (se 1 (by rfl) ⟨1017278, by rfl⟩ : syracuseStep 1356371 = 2034557) B2034557
theorem B5092055 : Blo 350755 5092055 := bstep (se 1 (by rfl) ⟨3819041, by rfl⟩ : syracuseStep 5092055 = 7638083) B7638083
theorem B5714813 : Blo 350755 5714813 := bstep (se 3 (by rfl) ⟨1071527, by rfl⟩ : syracuseStep 5714813 = 2143055) B2143055
theorem B3060605 : Blo 350755 3060605 := bstep (se 3 (by rfl) ⟨573863, by rfl⟩ : syracuseStep 3060605 = 1147727) B1147727
theorem B4010957 : Blo 350755 4010957 := bstep (se 3 (by rfl) ⟨752054, by rfl⟩ : syracuseStep 4010957 = 1504109) B1504109
theorem B9582119 : Blo 350755 9582119 := bstep (se 1 (by rfl) ⟨7186589, by rfl⟩ : syracuseStep 9582119 = 14373179) B14373179
theorem B4273847 : Blo 350755 4273847 := bstep (se 1 (by rfl) ⟨3205385, by rfl⟩ : syracuseStep 4273847 = 6410771) B6410771
theorem B38975185 : Blo 350755 38975185 := bstep (se 2 (by rfl) ⟨14615694, by rfl⟩ : syracuseStep 38975185 = 29231389) B29231389
theorem B1193723 : Blo 350755 1193723 := bstep (se 1 (by rfl) ⟨895292, by rfl⟩ : syracuseStep 1193723 = 1790585) B1790585
theorem B1193885 : Blo 350755 1193885 := bstep (se 3 (by rfl) ⟨223853, by rfl⟩ : syracuseStep 1193885 = 447707) B447707
theorem B2570221 : Blo 350755 2570221 := bstep (se 3 (by rfl) ⟨481916, by rfl⟩ : syracuseStep 2570221 = 963833) B963833
theorem B636911 : Blo 350755 636911 := bstep (se 1 (by rfl) ⟨477683, by rfl⟩ : syracuseStep 636911 = 955367) B955367
theorem B1128647 : Blo 350755 1128647 := bstep (se 1 (by rfl) ⟨846485, by rfl⟩ : syracuseStep 1128647 = 1692971) B1692971
theorem B4503923 : Blo 350755 4503923 := bstep (se 1 (by rfl) ⟨3377942, by rfl⟩ : syracuseStep 4503923 = 6755885) B6755885
theorem B16366211 : Blo 350755 16366211 := bstep (se 1 (by rfl) ⟨12274658, by rfl⟩ : syracuseStep 16366211 = 24549317) B24549317
theorem B1194857 : Blo 350755 1194857 := bstep (se 2 (by rfl) ⟨448071, by rfl⟩ : syracuseStep 1194857 = 896143) B896143
theorem B1194911 : Blo 350755 1194911 := bstep (se 1 (by rfl) ⟨896183, by rfl⟩ : syracuseStep 1194911 = 1792367) B1792367
theorem B4537295 : Blo 350755 4537295 := bstep (se 1 (by rfl) ⟨3402971, by rfl⟩ : syracuseStep 4537295 = 6805943) B6805943
theorem B998867 : Blo 350755 998867 := bstep (se 1 (by rfl) ⟨749150, by rfl⟩ : syracuseStep 998867 = 1498301) B1498301
theorem B2244239 : Blo 350755 2244239 := bstep (se 1 (by rfl) ⟨1683179, by rfl⟩ : syracuseStep 2244239 = 3366359) B3366359
theorem B1785725 : Blo 350755 1785725 := bstep (se 3 (by rfl) ⟨334823, by rfl⟩ : syracuseStep 1785725 = 669647) B669647
theorem B1359787 : Blo 350755 1359787 := bstep (se 1 (by rfl) ⟨1019840, by rfl⟩ : syracuseStep 1359787 = 2039681) B2039681
theorem B1130429 : Blo 350755 1130429 := bstep (se 3 (by rfl) ⟨211955, by rfl⟩ : syracuseStep 1130429 = 423911) B423911
theorem B3391627 : Blo 350755 3391627 := bstep (se 1 (by rfl) ⟨2543720, by rfl⟩ : syracuseStep 3391627 = 5087441) B5087441
theorem B3686975 : Blo 350755 3686975 := bstep (se 1 (by rfl) ⟨2765231, by rfl⟩ : syracuseStep 3686975 = 5530463) B5530463
theorem B1197179 : Blo 350755 1197179 := bstep (se 1 (by rfl) ⟨897884, by rfl⟩ : syracuseStep 1197179 = 1795769) B1795769
theorem B1787507 : Blo 350755 1787507 := bstep (se 1 (by rfl) ⟨1340630, by rfl⟩ : syracuseStep 1787507 = 2681261) B2681261
theorem B2311841 : Blo 350755 2311841 := bstep (se 2 (by rfl) ⟨866940, by rfl⟩ : syracuseStep 2311841 = 1733881) B1733881
theorem B2672513 : Blo 350755 2672513 := bstep (se 2 (by rfl) ⟨1002192, by rfl⟩ : syracuseStep 2672513 = 2004385) B2004385
theorem B542953 : Blo 350755 542953 := bstep (se 2 (by rfl) ⟨203607, by rfl⟩ : syracuseStep 542953 = 407215) B407215
theorem B1788317 : Blo 350755 1788317 := bstep (se 3 (by rfl) ⟨335309, by rfl⟩ : syracuseStep 1788317 = 670619) B670619
theorem B3885707 : Blo 350755 3885707 := bstep (se 1 (by rfl) ⟨2914280, by rfl⟩ : syracuseStep 3885707 = 5828561) B5828561
theorem B3624101 : Blo 350755 3624101 := bstep (se 4 (by rfl) ⟨339759, by rfl⟩ : syracuseStep 3624101 = 679519) B679519
theorem B1789127 : Blo 350755 1789127 := bstep (se 1 (by rfl) ⟨1341845, by rfl⟩ : syracuseStep 1789127 = 2683691) B2683691
theorem B4509047 : Blo 350755 4509047 := bstep (se 1 (by rfl) ⟨3381785, by rfl⟩ : syracuseStep 4509047 = 6763571) B6763571
theorem B5459471 : Blo 350755 5459471 := bstep (se 1 (by rfl) ⟨4094603, by rfl⟩ : syracuseStep 5459471 = 8189207) B8189207
theorem B380743 : Blo 350755 380743 := bstep (se 1 (by rfl) ⟨285557, by rfl⟩ : syracuseStep 380743 = 571115) B571115
theorem B642971 : Blo 350755 642971 := bstep (se 1 (by rfl) ⟨482228, by rfl⟩ : syracuseStep 642971 = 964457) B964457
theorem B7721249 : Blo 350755 7721249 := bstep (se 2 (by rfl) ⟨2895468, by rfl⟩ : syracuseStep 7721249 = 5790937) B5790937
theorem B10309963 : Blo 350755 10309963 := bstep (se 1 (by rfl) ⟨7732472, by rfl⟩ : syracuseStep 10309963 = 15464945) B15464945
theorem B8606087 : Blo 350755 8606087 := bstep (se 1 (by rfl) ⟨6454565, by rfl⟩ : syracuseStep 8606087 = 12909131) B12909131
theorem B1790423 : Blo 350755 1790423 := bstep (se 1 (by rfl) ⟨1342817, by rfl⟩ : syracuseStep 1790423 = 2685635) B2685635
theorem B3822329 : Blo 350755 3822329 := bstep (se 2 (by rfl) ⟨1433373, by rfl⟩ : syracuseStep 3822329 = 2866747) B2866747
theorem B1069949 : Blo 350755 1069949 := bstep (se 3 (by rfl) ⟨200615, by rfl⟩ : syracuseStep 1069949 = 401231) B401231
theorem B2544643 : Blo 350755 2544643 := bstep (se 1 (by rfl) ⟨1908482, by rfl⟩ : syracuseStep 2544643 = 3816965) B3816965
theorem B1332233 : Blo 350755 1332233 := bstep (se 2 (by rfl) ⟨499587, by rfl⟩ : syracuseStep 1332233 = 999175) B999175
theorem B906515 : Blo 350755 906515 := bstep (se 1 (by rfl) ⟨679886, by rfl⟩ : syracuseStep 906515 = 1359773) B1359773
theorem B3233267 : Blo 350755 3233267 := bstep (se 1 (by rfl) ⟨2424950, by rfl⟩ : syracuseStep 3233267 = 4849901) B4849901
theorem B1923047 : Blo 350755 1923047 := bstep (se 1 (by rfl) ⟨1442285, by rfl⟩ : syracuseStep 1923047 = 2884571) B2884571
theorem B3004391 : Blo 350755 3004391 := bstep (se 1 (by rfl) ⟨2253293, by rfl⟩ : syracuseStep 3004391 = 4506587) B4506587
theorem B5691977 : Blo 350755 5691977 := bstep (se 2 (by rfl) ⟨2134491, by rfl⟩ : syracuseStep 5691977 = 4268983) B4268983
theorem B4119113 : Blo 350755 4119113 := bstep (se 2 (by rfl) ⟨1544667, by rfl⟩ : syracuseStep 4119113 = 3089335) B3089335
theorem B1071955 : Blo 350755 1071955 := bstep (se 1 (by rfl) ⟨803966, by rfl⟩ : syracuseStep 1071955 = 1607933) B1607933
theorem B351067 : Blo 350755 351067 := bstep (se 1 (by rfl) ⟨263300, by rfl⟩ : syracuseStep 351067 = 526601) B526601
theorem B351135 : Blo 350755 351135 := bstep (se 1 (by rfl) ⟨263351, by rfl⟩ : syracuseStep 351135 = 526703) B526703
theorem B1793015 : Blo 350755 1793015 := bstep (se 1 (by rfl) ⟨1344761, by rfl⟩ : syracuseStep 1793015 = 2689523) B2689523
theorem B351279 : Blo 350755 351279 := bstep (se 1 (by rfl) ⟨263459, by rfl⟩ : syracuseStep 351279 = 526919) B526919
theorem B351303 : Blo 350755 351303 := bstep (se 1 (by rfl) ⟨263477, by rfl⟩ : syracuseStep 351303 = 526955) B526955
theorem B351455 : Blo 350755 351455 := bstep (se 1 (by rfl) ⟨263591, by rfl⟩ : syracuseStep 351455 = 527183) B527183
theorem B4545953 : Blo 350755 4545953 := bstep (se 2 (by rfl) ⟨1704732, by rfl⟩ : syracuseStep 4545953 = 3409465) B3409465
theorem B351719 : Blo 350755 351719 := bstep (se 1 (by rfl) ⟨263789, by rfl⟩ : syracuseStep 351719 = 527579) B527579
theorem B351835 : Blo 350755 351835 := bstep (se 1 (by rfl) ⟨263876, by rfl⟩ : syracuseStep 351835 = 527753) B527753
theorem B352071 : Blo 350755 352071 := bstep (se 1 (by rfl) ⟨264053, by rfl⟩ : syracuseStep 352071 = 528107) B528107
theorem B1335163 : Blo 350755 1335163 := bstep (se 1 (by rfl) ⟨1001372, by rfl⟩ : syracuseStep 1335163 = 2002745) B2002745
theorem B352223 : Blo 350755 352223 := bstep (se 1 (by rfl) ⟨264167, by rfl⟩ : syracuseStep 352223 = 528335) B528335
theorem B352487 : Blo 350755 352487 := bstep (se 1 (by rfl) ⟨264365, by rfl⟩ : syracuseStep 352487 = 528731) B528731
theorem B2908493 : Blo 350755 2908493 := bstep (se 3 (by rfl) ⟨545342, by rfl⟩ : syracuseStep 2908493 = 1090685) B1090685
theorem B1335649 : Blo 350755 1335649 := bstep (se 2 (by rfl) ⟨500868, by rfl⟩ : syracuseStep 1335649 = 1001737) B1001737
theorem B352639 : Blo 350755 352639 := bstep (se 1 (by rfl) ⟨264479, by rfl⟩ : syracuseStep 352639 = 528959) B528959
theorem B1008071 : Blo 350755 1008071 := bstep (se 1 (by rfl) ⟨756053, by rfl⟩ : syracuseStep 1008071 = 1512107) B1512107
theorem B352719 : Blo 350755 352719 := bstep (se 1 (by rfl) ⟨264539, by rfl⟩ : syracuseStep 352719 = 529079) B529079
theorem B352871 : Blo 350755 352871 := bstep (se 1 (by rfl) ⟨264653, by rfl⟩ : syracuseStep 352871 = 529307) B529307
theorem B1073839 : Blo 350755 1073839 := bstep (se 1 (by rfl) ⟨805379, by rfl⟩ : syracuseStep 1073839 = 1610759) B1610759
theorem B1336121 : Blo 350755 1336121 := bstep (se 2 (by rfl) ⟨501045, by rfl⟩ : syracuseStep 1336121 = 1002091) B1002091
theorem B353135 : Blo 350755 353135 := bstep (se 1 (by rfl) ⟨264851, by rfl⟩ : syracuseStep 353135 = 529703) B529703
theorem B353191 : Blo 350755 353191 := bstep (se 1 (by rfl) ⟨264893, by rfl⟩ : syracuseStep 353191 = 529787) B529787
theorem B353275 : Blo 350755 353275 := bstep (se 1 (by rfl) ⟨264956, by rfl⟩ : syracuseStep 353275 = 529913) B529913
theorem B353343 : Blo 350755 353343 := bstep (se 1 (by rfl) ⟨265007, by rfl⟩ : syracuseStep 353343 = 530015) B530015
theorem B2254013 : Blo 350755 2254013 := bstep (se 3 (by rfl) ⟨422627, by rfl⟩ : syracuseStep 2254013 = 845255) B845255
theorem B353487 : Blo 350755 353487 := bstep (se 1 (by rfl) ⟨265115, by rfl⟩ : syracuseStep 353487 = 530231) B530231
theorem B353691 : Blo 350755 353691 := bstep (se 1 (by rfl) ⟨265268, by rfl⟩ : syracuseStep 353691 = 530537) B530537
theorem B3008015 : Blo 350755 3008015 := bstep (se 1 (by rfl) ⟨2256011, by rfl⟩ : syracuseStep 3008015 = 4512023) B4512023
theorem B1271315 : Blo 350755 1271315 := bstep (se 1 (by rfl) ⟨953486, by rfl⟩ : syracuseStep 1271315 = 1906973) B1906973
theorem B353903 : Blo 350755 353903 := bstep (se 1 (by rfl) ⟨265427, by rfl⟩ : syracuseStep 353903 = 530855) B530855
theorem B353959 : Blo 350755 353959 := bstep (se 1 (by rfl) ⟨265469, by rfl⟩ : syracuseStep 353959 = 530939) B530939
theorem B354043 : Blo 350755 354043 := bstep (se 1 (by rfl) ⟨265532, by rfl⟩ : syracuseStep 354043 = 531065) B531065
theorem B1009415 : Blo 350755 1009415 := bstep (se 1 (by rfl) ⟨757061, by rfl⟩ : syracuseStep 1009415 = 1514123) B1514123
theorem B354079 : Blo 350755 354079 := bstep (se 1 (by rfl) ⟨265559, by rfl⟩ : syracuseStep 354079 = 531119) B531119
theorem B354111 : Blo 350755 354111 := bstep (se 1 (by rfl) ⟨265583, by rfl⟩ : syracuseStep 354111 = 531167) B531167
theorem B1501001 : Blo 350755 1501001 := bstep (se 2 (by rfl) ⟨562875, by rfl⟩ : syracuseStep 1501001 = 1125751) B1125751
theorem B354287 : Blo 350755 354287 := bstep (se 1 (by rfl) ⟨265715, by rfl⟩ : syracuseStep 354287 = 531431) B531431
theorem B1009655 : Blo 350755 1009655 := bstep (se 1 (by rfl) ⟨757241, by rfl⟩ : syracuseStep 1009655 = 1514483) B1514483
theorem B354459 : Blo 350755 354459 := bstep (se 1 (by rfl) ⟨265844, by rfl⟩ : syracuseStep 354459 = 531689) B531689
theorem B354495 : Blo 350755 354495 := bstep (se 1 (by rfl) ⟨265871, by rfl⟩ : syracuseStep 354495 = 531743) B531743
theorem B3795173 : Blo 350755 3795173 := bstep (se 4 (by rfl) ⟨355797, by rfl⟩ : syracuseStep 3795173 = 711595) B711595
theorem B2844953 : Blo 350755 2844953 := bstep (se 2 (by rfl) ⟨1066857, by rfl⟩ : syracuseStep 2844953 = 2133715) B2133715
theorem B354607 : Blo 350755 354607 := bstep (se 1 (by rfl) ⟨265955, by rfl⟩ : syracuseStep 354607 = 531911) B531911
theorem B2550179 : Blo 350755 2550179 := bstep (se 1 (by rfl) ⟨1912634, by rfl⟩ : syracuseStep 2550179 = 3825269) B3825269
theorem B5827247 : Blo 350755 5827247 := bstep (se 1 (by rfl) ⟨4370435, by rfl⟩ : syracuseStep 5827247 = 8740871) B8740871
theorem B1076345 : Blo 350755 1076345 := bstep (se 2 (by rfl) ⟨403629, by rfl⟩ : syracuseStep 1076345 = 807259) B807259
theorem B3010679 : Blo 350755 3010679 := bstep (se 1 (by rfl) ⟨2258009, by rfl⟩ : syracuseStep 3010679 = 4516019) B4516019
theorem B1274167 : Blo 350755 1274167 := bstep (se 1 (by rfl) ⟨955625, by rfl⟩ : syracuseStep 1274167 = 1911251) B1911251
theorem B750073 : Blo 350755 750073 := bstep (se 2 (by rfl) ⟨281277, by rfl⟩ : syracuseStep 750073 = 562555) B562555
theorem B1209563 : Blo 350755 1209563 := bstep (se 1 (by rfl) ⟨907172, by rfl⟩ : syracuseStep 1209563 = 1814345) B1814345
theorem B1504777 : Blo 350755 1504777 := bstep (se 2 (by rfl) ⟨564291, by rfl⟩ : syracuseStep 1504777 = 1128583) B1128583
theorem B1930823 : Blo 350755 1930823 := bstep (se 1 (by rfl) ⟨1448117, by rfl⟩ : syracuseStep 1930823 = 2896235) B2896235
theorem B9762461 : Blo 350755 9762461 := bstep (se 3 (by rfl) ⟨1830461, by rfl⟩ : syracuseStep 9762461 = 3660923) B3660923
theorem B3013139 : Blo 350755 3013139 := bstep (se 1 (by rfl) ⟨2259854, by rfl⟩ : syracuseStep 3013139 = 4519709) B4519709
theorem B1506433 : Blo 350755 1506433 := bstep (se 2 (by rfl) ⟨564912, by rfl⟩ : syracuseStep 1506433 = 1129825) B1129825
theorem B1507049 : Blo 350755 1507049 := bstep (se 2 (by rfl) ⟨565143, by rfl⟩ : syracuseStep 1507049 = 1130287) B1130287
theorem B1277687 : Blo 350755 1277687 := bstep (se 1 (by rfl) ⟨958265, by rfl⟩ : syracuseStep 1277687 = 1916531) B1916531
theorem B4522169 : Blo 350755 4522169 := bstep (se 2 (by rfl) ⟨1695813, by rfl⟩ : syracuseStep 4522169 = 3391627) B3391627
theorem B1704311 : Blo 350755 1704311 := bstep (se 1 (by rfl) ⟨1278233, by rfl⟩ : syracuseStep 1704311 = 2556467) B2556467
theorem B917887 : Blo 350755 917887 := bstep (se 1 (by rfl) ⟨688415, by rfl⟩ : syracuseStep 917887 = 1376831) B1376831
theorem B2457983 : Blo 350755 2457983 := bstep (se 1 (by rfl) ⟨1843487, by rfl⟩ : syracuseStep 2457983 = 3686975) B3686975
theorem B2556845 : Blo 350755 2556845 := bstep (se 3 (by rfl) ⟨479408, by rfl⟩ : syracuseStep 2556845 = 958817) B958817
theorem B3015737 : Blo 350755 3015737 := bstep (se 2 (by rfl) ⟨1130901, by rfl⟩ : syracuseStep 3015737 = 2261803) B2261803
theorem B1541227 : Blo 350755 1541227 := bstep (se 1 (by rfl) ⟨1155920, by rfl⟩ : syracuseStep 1541227 = 2311841) B2311841
theorem B1344701 : Blo 350755 1344701 := bstep (se 3 (by rfl) ⟨252131, by rfl⟩ : syracuseStep 1344701 = 504263) B504263
theorem B2426375 : Blo 350755 2426375 := bstep (se 1 (by rfl) ⟨1819781, by rfl⟩ : syracuseStep 2426375 = 3639563) B3639563
theorem B2590471 : Blo 350755 2590471 := bstep (se 1 (by rfl) ⟨1942853, by rfl⟩ : syracuseStep 2590471 = 3885707) B3885707
theorem B10192877 : Blo 350755 10192877 := bstep (se 3 (by rfl) ⟨1911164, by rfl⟩ : syracuseStep 10192877 = 3822329) B3822329
theorem B526367 : Blo 350755 526367 := bstep (se 1 (by rfl) ⟨394775, by rfl⟩ : syracuseStep 526367 = 789551) B789551
theorem B395311 : Blo 350755 395311 := bstep (se 1 (by rfl) ⟨296483, by rfl⟩ : syracuseStep 395311 = 592967) B592967
theorem B526559 : Blo 350755 526559 := bstep (se 1 (by rfl) ⟨394919, by rfl⟩ : syracuseStep 526559 = 789839) B789839
theorem B526619 : Blo 350755 526619 := bstep (se 1 (by rfl) ⟨394964, by rfl⟩ : syracuseStep 526619 = 789929) B789929
theorem B395599 : Blo 350755 395599 := bstep (se 1 (by rfl) ⟨296699, by rfl⟩ : syracuseStep 395599 = 593399) B593399
theorem B3639647 : Blo 350755 3639647 := bstep (se 1 (by rfl) ⟨2729735, by rfl⟩ : syracuseStep 3639647 = 5459471) B5459471
theorem B526943 : Blo 350755 526943 := bstep (se 1 (by rfl) ⟨395207, by rfl⟩ : syracuseStep 526943 = 790415) B790415
theorem B428647 : Blo 350755 428647 := bstep (se 1 (by rfl) ⟨321485, by rfl⟩ : syracuseStep 428647 = 642971) B642971
theorem B789353 : Blo 350755 789353 := bstep (se 2 (by rfl) ⟨296007, by rfl⟩ : syracuseStep 789353 = 592015) B592015
theorem B527225 : Blo 350755 527225 := bstep (se 2 (by rfl) ⟨197709, by rfl⟩ : syracuseStep 527225 = 395419) B395419
theorem B789407 : Blo 350755 789407 := bstep (se 1 (by rfl) ⟨592055, by rfl⟩ : syracuseStep 789407 = 1184111) B1184111
theorem B527273 : Blo 350755 527273 := bstep (se 2 (by rfl) ⟨197727, by rfl⟩ : syracuseStep 527273 = 395455) B395455
theorem B5737391 : Blo 350755 5737391 := bstep (se 1 (by rfl) ⟨4303043, by rfl⟩ : syracuseStep 5737391 = 8606087) B8606087
theorem B396283 : Blo 350755 396283 := bstep (se 1 (by rfl) ⟨297212, by rfl⟩ : syracuseStep 396283 = 594425) B594425
theorem B527423 : Blo 350755 527423 := bstep (se 1 (by rfl) ⟨395567, by rfl⟩ : syracuseStep 527423 = 791135) B791135
theorem B396463 : Blo 350755 396463 := bstep (se 1 (by rfl) ⟨297347, by rfl⟩ : syracuseStep 396463 = 594695) B594695
theorem B2624723 : Blo 350755 2624723 := bstep (se 1 (by rfl) ⟨1968542, by rfl⟩ : syracuseStep 2624723 = 3937085) B3937085
theorem B888155 : Blo 350755 888155 := bstep (se 1 (by rfl) ⟨666116, by rfl⟩ : syracuseStep 888155 = 1332233) B1332233
theorem B888185 : Blo 350755 888185 := bstep (se 2 (by rfl) ⟨333069, by rfl⟩ : syracuseStep 888185 = 666139) B666139
theorem B2624993 : Blo 350755 2624993 := bstep (se 2 (by rfl) ⟨984372, by rfl⟩ : syracuseStep 2624993 = 1968745) B1968745
theorem B527975 : Blo 350755 527975 := bstep (se 1 (by rfl) ⟨395981, by rfl⟩ : syracuseStep 527975 = 791963) B791963
theorem B790343 : Blo 350755 790343 := bstep (se 1 (by rfl) ⟨592757, by rfl⟩ : syracuseStep 790343 = 1185515) B1185515
theorem B397183 : Blo 350755 397183 := bstep (se 1 (by rfl) ⟨297887, by rfl⟩ : syracuseStep 397183 = 595775) B595775
theorem B528359 : Blo 350755 528359 := bstep (se 1 (by rfl) ⟨396269, by rfl⟩ : syracuseStep 528359 = 792539) B792539
theorem B1282031 : Blo 350755 1282031 := bstep (se 1 (by rfl) ⟨961523, by rfl⟩ : syracuseStep 1282031 = 1923047) B1923047
theorem B2002927 : Blo 350755 2002927 := bstep (se 1 (by rfl) ⟨1502195, by rfl⟩ : syracuseStep 2002927 = 3004391) B3004391
theorem B790523 : Blo 350755 790523 := bstep (se 1 (by rfl) ⟨592892, by rfl⟩ : syracuseStep 790523 = 1185785) B1185785
theorem B528479 : Blo 350755 528479 := bstep (se 1 (by rfl) ⟨396359, by rfl⟩ : syracuseStep 528479 = 792719) B792719
theorem B790631 : Blo 350755 790631 := bstep (se 1 (by rfl) ⟨592973, by rfl⟩ : syracuseStep 790631 = 1185947) B1185947
theorem B528491 : Blo 350755 528491 := bstep (se 1 (by rfl) ⟨396368, by rfl⟩ : syracuseStep 528491 = 792737) B792737
theorem B528539 : Blo 350755 528539 := bstep (se 1 (by rfl) ⟨396404, by rfl⟩ : syracuseStep 528539 = 792809) B792809
theorem B790703 : Blo 350755 790703 := bstep (se 1 (by rfl) ⟨593027, by rfl⟩ : syracuseStep 790703 = 1186055) B1186055
theorem B14094691 : Blo 350755 14094691 := bstep (se 1 (by rfl) ⟨10571018, by rfl⟩ : syracuseStep 14094691 = 21142037) B21142037
theorem B397723 : Blo 350755 397723 := bstep (se 1 (by rfl) ⟨298292, by rfl⟩ : syracuseStep 397723 = 596585) B596585
theorem B791387 : Blo 350755 791387 := bstep (se 1 (by rfl) ⟨593540, by rfl⟩ : syracuseStep 791387 = 1187081) B1187081
theorem B529391 : Blo 350755 529391 := bstep (se 1 (by rfl) ⟨397043, by rfl⟩ : syracuseStep 529391 = 794087) B794087
theorem B398407 : Blo 350755 398407 := bstep (se 1 (by rfl) ⟨298805, by rfl⟩ : syracuseStep 398407 = 597611) B597611
theorem B595039 : Blo 350755 595039 := bstep (se 1 (by rfl) ⟨446279, by rfl⟩ : syracuseStep 595039 = 892559) B892559
theorem B1184975 : Blo 350755 1184975 := bstep (se 1 (by rfl) ⟨888731, by rfl⟩ : syracuseStep 1184975 = 1777463) B1777463
theorem B398587 : Blo 350755 398587 := bstep (se 1 (by rfl) ⟨298940, by rfl⟩ : syracuseStep 398587 = 597881) B597881
theorem B529775 : Blo 350755 529775 := bstep (se 1 (by rfl) ⟨397331, by rfl⟩ : syracuseStep 529775 = 794663) B794663
theorem B529895 : Blo 350755 529895 := bstep (se 1 (by rfl) ⟨397421, by rfl⟩ : syracuseStep 529895 = 794843) B794843
theorem B1938995 : Blo 350755 1938995 := bstep (se 1 (by rfl) ⟨1454246, by rfl⟩ : syracuseStep 1938995 = 2908493) B2908493
theorem B988751 : Blo 350755 988751 := bstep (se 1 (by rfl) ⟨741563, by rfl⟩ : syracuseStep 988751 = 1483127) B1483127
theorem B792143 : Blo 350755 792143 := bstep (se 1 (by rfl) ⟨594107, by rfl⟩ : syracuseStep 792143 = 1188215) B1188215
theorem B530057 : Blo 350755 530057 := bstep (se 2 (by rfl) ⟨198771, by rfl⟩ : syracuseStep 530057 = 397543) B397543
theorem B530075 : Blo 350755 530075 := bstep (se 1 (by rfl) ⟨397556, by rfl⟩ : syracuseStep 530075 = 795113) B795113
theorem B530267 : Blo 350755 530267 := bstep (se 1 (by rfl) ⟨397700, by rfl⟩ : syracuseStep 530267 = 795401) B795401
theorem B890747 : Blo 350755 890747 := bstep (se 1 (by rfl) ⟨668060, by rfl⟩ : syracuseStep 890747 = 1336121) B1336121
theorem B530651 : Blo 350755 530651 := bstep (se 1 (by rfl) ⟨397988, by rfl⟩ : syracuseStep 530651 = 795977) B795977
theorem B792863 : Blo 350755 792863 := bstep (se 1 (by rfl) ⟨594647, by rfl⟩ : syracuseStep 792863 = 1189295) B1189295
theorem B2005343 : Blo 350755 2005343 := bstep (se 1 (by rfl) ⟨1504007, by rfl⟩ : syracuseStep 2005343 = 3008015) B3008015
theorem B530921 : Blo 350755 530921 := bstep (se 2 (by rfl) ⟨199095, by rfl⟩ : syracuseStep 530921 = 398191) B398191
theorem B793115 : Blo 350755 793115 := bstep (se 1 (by rfl) ⟨594836, by rfl⟩ : syracuseStep 793115 = 1189673) B1189673
theorem B1186487 : Blo 350755 1186487 := bstep (se 1 (by rfl) ⟨889865, by rfl⟩ : syracuseStep 1186487 = 1779731) B1779731
theorem B2530115 : Blo 350755 2530115 := bstep (se 1 (by rfl) ⟨1897586, by rfl⟩ : syracuseStep 2530115 = 3795173) B3795173
theorem B531311 : Blo 350755 531311 := bstep (se 1 (by rfl) ⟨398483, by rfl⟩ : syracuseStep 531311 = 796967) B796967
theorem B531323 : Blo 350755 531323 := bstep (se 1 (by rfl) ⟨398492, by rfl⟩ : syracuseStep 531323 = 796985) B796985
theorem B597199 : Blo 350755 597199 := bstep (se 1 (by rfl) ⟨447899, by rfl⟩ : syracuseStep 597199 = 895799) B895799
theorem B2006369 : Blo 350755 2006369 := bstep (se 2 (by rfl) ⟨752388, by rfl⟩ : syracuseStep 2006369 = 1504777) B1504777
theorem B794465 : Blo 350755 794465 := bstep (se 2 (by rfl) ⟨297924, by rfl⟩ : syracuseStep 794465 = 595849) B595849
theorem B794591 : Blo 350755 794591 := bstep (se 1 (by rfl) ⟨595943, by rfl⟩ : syracuseStep 794591 = 1191887) B1191887
theorem B2007119 : Blo 350755 2007119 := bstep (se 1 (by rfl) ⟨1505339, by rfl⟩ : syracuseStep 2007119 = 3010679) B3010679
theorem B794879 : Blo 350755 794879 := bstep (se 1 (by rfl) ⟨596159, by rfl⟩ : syracuseStep 794879 = 1192319) B1192319
theorem B795041 : Blo 350755 795041 := bstep (se 2 (by rfl) ⟨298140, by rfl⟩ : syracuseStep 795041 = 596281) B596281
theorem B3809875 : Blo 350755 3809875 := bstep (se 1 (by rfl) ⟨2857406, by rfl⟩ : syracuseStep 3809875 = 5714813) B5714813
theorem B2040403 : Blo 350755 2040403 := bstep (se 1 (by rfl) ⟨1530302, by rfl⟩ : syracuseStep 2040403 = 3060605) B3060605
theorem B7709357 : Blo 350755 7709357 := bstep (se 3 (by rfl) ⟨1445504, by rfl⟩ : syracuseStep 7709357 = 2891009) B2891009
theorem B1287215 : Blo 350755 1287215 := bstep (se 1 (by rfl) ⟨965411, by rfl⟩ : syracuseStep 1287215 = 1930823) B1930823
theorem B795815 : Blo 350755 795815 := bstep (se 1 (by rfl) ⟨596861, by rfl⟩ : syracuseStep 795815 = 1193723) B1193723
theorem B795923 : Blo 350755 795923 := bstep (se 1 (by rfl) ⟨596942, by rfl⟩ : syracuseStep 795923 = 1193885) B1193885
theorem B2008577 : Blo 350755 2008577 := bstep (se 2 (by rfl) ⟨753216, by rfl⟩ : syracuseStep 2008577 = 1506433) B1506433
theorem B2008759 : Blo 350755 2008759 := bstep (se 1 (by rfl) ⟨1506569, by rfl⟩ : syracuseStep 2008759 = 3013139) B3013139
theorem B796553 : Blo 350755 796553 := bstep (se 2 (by rfl) ⟨298707, by rfl⟩ : syracuseStep 796553 = 597415) B597415
theorem B796571 : Blo 350755 796571 := bstep (se 1 (by rfl) ⟨597428, by rfl⟩ : syracuseStep 796571 = 1194857) B1194857
theorem B796607 : Blo 350755 796607 := bstep (se 1 (by rfl) ⟨597455, by rfl⟩ : syracuseStep 796607 = 1194911) B1194911
theorem B3024863 : Blo 350755 3024863 := bstep (se 1 (by rfl) ⟨2268647, by rfl⟩ : syracuseStep 3024863 = 4537295) B4537295
theorem B796769 : Blo 350755 796769 := bstep (se 2 (by rfl) ⟨298788, by rfl⟩ : syracuseStep 796769 = 597577) B597577
theorem B665911 : Blo 350755 665911 := bstep (se 1 (by rfl) ⟨499433, by rfl⟩ : syracuseStep 665911 = 998867) B998867
theorem B1780217 : Blo 350755 1780217 := bstep (se 2 (by rfl) ⟨667581, by rfl⟩ : syracuseStep 1780217 = 1335163) B1335163
theorem B1813049 : Blo 350755 1813049 := bstep (se 2 (by rfl) ⟨679893, by rfl⟩ : syracuseStep 1813049 = 1359787) B1359787
theorem B1190483 : Blo 350755 1190483 := bstep (se 1 (by rfl) ⟨892862, by rfl⟩ : syracuseStep 1190483 = 1785725) B1785725
theorem B1780865 : Blo 350755 1780865 := bstep (se 2 (by rfl) ⟨667824, by rfl⟩ : syracuseStep 1780865 = 1335649) B1335649
theorem B798119 : Blo 350755 798119 := bstep (se 1 (by rfl) ⟨598589, by rfl⟩ : syracuseStep 798119 = 1197179) B1197179
theorem B20589997 : Blo 350755 20589997 := bstep (se 3 (by rfl) ⟨3860624, by rfl⟩ : syracuseStep 20589997 = 7721249) B7721249
theorem B667369 : Blo 350755 667369 := bstep (se 2 (by rfl) ⟨250263, by rfl⟩ : syracuseStep 667369 = 500527) B500527
theorem B1191671 : Blo 350755 1191671 := bstep (se 1 (by rfl) ⟨893753, by rfl⟩ : syracuseStep 1191671 = 1787507) B1787507
theorem B2895749 : Blo 350755 2895749 := bstep (se 4 (by rfl) ⟨271476, by rfl⟩ : syracuseStep 2895749 = 542953) B542953
theorem B1781675 : Blo 350755 1781675 := bstep (se 1 (by rfl) ⟨1336256, by rfl⟩ : syracuseStep 1781675 = 2672513) B2672513
theorem B1192211 : Blo 350755 1192211 := bstep (se 1 (by rfl) ⟨894158, by rfl⟩ : syracuseStep 1192211 = 1788317) B1788317
theorem B504571 : Blo 350755 504571 := bstep (se 1 (by rfl) ⟨378428, by rfl⟩ : syracuseStep 504571 = 756857) B756857
theorem B668425 : Blo 350755 668425 := bstep (se 2 (by rfl) ⟨250659, by rfl⟩ : syracuseStep 668425 = 501319) B501319
theorem B1192751 : Blo 350755 1192751 := bstep (se 1 (by rfl) ⟨894563, by rfl⟩ : syracuseStep 1192751 = 1789127) B1789127
theorem B1193615 : Blo 350755 1193615 := bstep (se 1 (by rfl) ⟨895211, by rfl⟩ : syracuseStep 1193615 = 1790423) B1790423
theorem B1193993 : Blo 350755 1193993 := bstep (se 2 (by rfl) ⟨447747, by rfl⟩ : syracuseStep 1193993 = 895495) B895495
theorem B604343 : Blo 350755 604343 := bstep (se 1 (by rfl) ⟨453257, by rfl⟩ : syracuseStep 604343 = 906515) B906515
theorem B1719265 : Blo 350755 1719265 := bstep (se 2 (by rfl) ⟨644724, by rfl⟩ : syracuseStep 1719265 = 1289449) B1289449
theorem B1686587 : Blo 350755 1686587 := bstep (se 1 (by rfl) ⟨1264940, by rfl⟩ : syracuseStep 1686587 = 2529881) B2529881
theorem B1195343 : Blo 350755 1195343 := bstep (se 1 (by rfl) ⟨896507, by rfl⟩ : syracuseStep 1195343 = 1793015) B1793015
theorem B3030635 : Blo 350755 3030635 := bstep (se 1 (by rfl) ⟨2272976, by rfl⟩ : syracuseStep 3030635 = 4545953) B4545953
theorem B638887 : Blo 350755 638887 := bstep (se 1 (by rfl) ⟨479165, by rfl⟩ : syracuseStep 638887 = 958331) B958331
theorem B672047 : Blo 350755 672047 := bstep (se 1 (by rfl) ⟨504035, by rfl⟩ : syracuseStep 672047 = 1008071) B1008071
theorem B13746617 : Blo 350755 13746617 := bstep (se 2 (by rfl) ⟨5154981, by rfl⟩ : syracuseStep 13746617 = 10309963) B10309963
theorem B1000097 : Blo 350755 1000097 := bstep (se 2 (by rfl) ⟨375036, by rfl⟩ : syracuseStep 1000097 = 750073) B750073
theorem B377903 : Blo 350755 377903 := bstep (se 1 (by rfl) ⟨283427, by rfl⟩ : syracuseStep 377903 = 566855) B566855
theorem B672943 : Blo 350755 672943 := bstep (se 1 (by rfl) ⟨504707, by rfl⟩ : syracuseStep 672943 = 1009415) B1009415
theorem B1000667 : Blo 350755 1000667 := bstep (se 1 (by rfl) ⟨750500, by rfl⟩ : syracuseStep 1000667 = 1501001) B1501001
theorem B673103 : Blo 350755 673103 := bstep (se 1 (by rfl) ⟨504827, by rfl⟩ : syracuseStep 673103 = 1009655) B1009655
theorem B3392857 : Blo 350755 3392857 := bstep (se 2 (by rfl) ⟨1272321, by rfl⟩ : syracuseStep 3392857 = 2544643) B2544643
theorem B3884831 : Blo 350755 3884831 := bstep (se 1 (by rfl) ⟨2913623, by rfl⟩ : syracuseStep 3884831 = 5827247) B5827247
theorem B444199 : Blo 350755 444199 := bstep (se 1 (by rfl) ⟨333149, by rfl⟩ : syracuseStep 444199 = 666299) B666299
theorem B7653305 : Blo 350755 7653305 := bstep (se 2 (by rfl) ⟨2869989, by rfl⟩ : syracuseStep 7653305 = 5739979) B5739979
theorem B3426961 : Blo 350755 3426961 := bstep (se 2 (by rfl) ⟨1285110, by rfl⟩ : syracuseStep 3426961 = 2570221) B2570221
theorem B445495 : Blo 350755 445495 := bstep (se 1 (by rfl) ⟨334121, by rfl⟩ : syracuseStep 445495 = 668243) B668243
theorem B904247 : Blo 350755 904247 := bstep (se 1 (by rfl) ⟨678185, by rfl⟩ : syracuseStep 904247 = 1356371) B1356371
theorem B3394703 : Blo 350755 3394703 := bstep (se 1 (by rfl) ⟨2546027, by rfl⟩ : syracuseStep 3394703 = 5092055) B5092055
theorem B2673971 : Blo 350755 2673971 := bstep (se 1 (by rfl) ⟨2005478, by rfl⟩ : syracuseStep 2673971 = 4010957) B4010957
theorem B806375 : Blo 350755 806375 := bstep (se 1 (by rfl) ⟨604781, by rfl⟩ : syracuseStep 806375 = 1209563) B1209563
theorem B207867653 : Blo 350755 207867653 := bstep (se 4 (by rfl) ⟨19487592, by rfl⟩ : syracuseStep 207867653 = 38975185) B38975185
theorem B6508307 : Blo 350755 6508307 := bstep (se 1 (by rfl) ⟨4881230, by rfl⟩ : syracuseStep 6508307 = 9762461) B9762461
theorem B2674457 : Blo 350755 2674457 := bstep (se 2 (by rfl) ⟨1002921, by rfl⟩ : syracuseStep 2674457 = 2005843) B2005843
theorem B1429273 : Blo 350755 1429273 := bstep (se 2 (by rfl) ⟨535977, by rfl⟩ : syracuseStep 1429273 = 1071955) B1071955
theorem B3002615 : Blo 350755 3002615 := bstep (se 1 (by rfl) ⟨2251961, by rfl⟩ : syracuseStep 3002615 = 4503923) B4503923
theorem B1496159 : Blo 350755 1496159 := bstep (se 1 (by rfl) ⟨1122119, by rfl⟩ : syracuseStep 1496159 = 2244239) B2244239
theorem B1004699 : Blo 350755 1004699 := bstep (se 1 (by rfl) ⟨753524, by rfl⟩ : syracuseStep 1004699 = 1507049) B1507049
theorem B1332719 : Blo 350755 1332719 := bstep (se 1 (by rfl) ⟨999539, by rfl⟩ : syracuseStep 1332719 = 1999079) B1999079
theorem B1005223 : Blo 350755 1005223 := bstep (se 1 (by rfl) ⟨753917, by rfl⟩ : syracuseStep 1005223 = 1507835) B1507835
theorem B1431785 : Blo 350755 1431785 := bstep (se 2 (by rfl) ⟨536919, by rfl⟩ : syracuseStep 1431785 = 1073839) B1073839
theorem B1333691 : Blo 350755 1333691 := bstep (se 1 (by rfl) ⟨1000268, by rfl⟩ : syracuseStep 1333691 = 2000537) B2000537
theorem B350811 : Blo 350755 350811 := bstep (se 1 (by rfl) ⟨263108, by rfl⟩ : syracuseStep 350811 = 526217) B526217
theorem B1694317 : Blo 350755 1694317 := bstep (se 3 (by rfl) ⟨317684, by rfl⟩ : syracuseStep 1694317 = 635369) B635369
theorem B350879 : Blo 350755 350879 := bstep (se 1 (by rfl) ⟨263159, by rfl⟩ : syracuseStep 350879 = 526319) B526319
theorem B351047 : Blo 350755 351047 := bstep (se 1 (by rfl) ⟨263285, by rfl⟩ : syracuseStep 351047 = 526571) B526571
theorem B351087 : Blo 350755 351087 := bstep (se 1 (by rfl) ⟨263315, by rfl⟩ : syracuseStep 351087 = 526631) B526631
theorem B351143 : Blo 350755 351143 := bstep (se 1 (by rfl) ⟨263357, by rfl⟩ : syracuseStep 351143 = 526715) B526715
theorem B351323 : Blo 350755 351323 := bstep (se 1 (by rfl) ⟨263492, by rfl⟩ : syracuseStep 351323 = 526985) B526985
theorem B351439 : Blo 350755 351439 := bstep (se 1 (by rfl) ⟨263579, by rfl⟩ : syracuseStep 351439 = 527159) B527159
theorem B351463 : Blo 350755 351463 := bstep (se 1 (by rfl) ⟨263597, by rfl⟩ : syracuseStep 351463 = 527195) B527195
theorem B2252063 : Blo 350755 2252063 := bstep (se 1 (by rfl) ⟨1689047, by rfl⟩ : syracuseStep 2252063 = 3378095) B3378095
theorem B351559 : Blo 350755 351559 := bstep (se 1 (by rfl) ⟨263669, by rfl⟩ : syracuseStep 351559 = 527339) B527339
theorem B1006955 : Blo 350755 1006955 := bstep (se 1 (by rfl) ⟨755216, by rfl⟩ : syracuseStep 1006955 = 1510433) B1510433
theorem B2416067 : Blo 350755 2416067 := bstep (se 1 (by rfl) ⟨1812050, by rfl⟩ : syracuseStep 2416067 = 3624101) B3624101
theorem B351695 : Blo 350755 351695 := bstep (se 1 (by rfl) ⟨263771, by rfl⟩ : syracuseStep 351695 = 527543) B527543
theorem B3006031 : Blo 350755 3006031 := bstep (se 1 (by rfl) ⟨2254523, by rfl⟩ : syracuseStep 3006031 = 4509047) B4509047
theorem B351855 : Blo 350755 351855 := bstep (se 1 (by rfl) ⟨263891, by rfl⟩ : syracuseStep 351855 = 527783) B527783
theorem B1531559 : Blo 350755 1531559 := bstep (se 1 (by rfl) ⟨1148669, by rfl⟩ : syracuseStep 1531559 = 2297339) B2297339
theorem B1334951 : Blo 350755 1334951 := bstep (se 1 (by rfl) ⟨1001213, by rfl⟩ : syracuseStep 1334951 = 2002427) B2002427
theorem B351911 : Blo 350755 351911 := bstep (se 1 (by rfl) ⟨263933, by rfl⟩ : syracuseStep 351911 = 527867) B527867
theorem B351975 : Blo 350755 351975 := bstep (se 1 (by rfl) ⟨263981, by rfl⟩ : syracuseStep 351975 = 527963) B527963
theorem B352031 : Blo 350755 352031 := bstep (se 1 (by rfl) ⟨264023, by rfl⟩ : syracuseStep 352031 = 528047) B528047
theorem B352111 : Blo 350755 352111 := bstep (se 1 (by rfl) ⟨264083, by rfl⟩ : syracuseStep 352111 = 528167) B528167
theorem B352167 : Blo 350755 352167 := bstep (se 1 (by rfl) ⟨264125, by rfl⟩ : syracuseStep 352167 = 528251) B528251
theorem B352447 : Blo 350755 352447 := bstep (se 1 (by rfl) ⟨264335, by rfl⟩ : syracuseStep 352447 = 528671) B528671
theorem B352463 : Blo 350755 352463 := bstep (se 1 (by rfl) ⟨264347, by rfl⟩ : syracuseStep 352463 = 528695) B528695
theorem B352511 : Blo 350755 352511 := bstep (se 1 (by rfl) ⟨264383, by rfl⟩ : syracuseStep 352511 = 528767) B528767
theorem B352559 : Blo 350755 352559 := bstep (se 1 (by rfl) ⟨264419, by rfl⟩ : syracuseStep 352559 = 528839) B528839
theorem B352795 : Blo 350755 352795 := bstep (se 1 (by rfl) ⟨264596, by rfl⟩ : syracuseStep 352795 = 529193) B529193
theorem B352799 : Blo 350755 352799 := bstep (se 1 (by rfl) ⟨264599, by rfl⟩ : syracuseStep 352799 = 529199) B529199
theorem B713299 : Blo 350755 713299 := bstep (se 1 (by rfl) ⟨534974, by rfl⟩ : syracuseStep 713299 = 1069949) B1069949
theorem B352879 : Blo 350755 352879 := bstep (se 1 (by rfl) ⟨264659, by rfl⟩ : syracuseStep 352879 = 529319) B529319
theorem B352935 : Blo 350755 352935 := bstep (se 1 (by rfl) ⟨264701, by rfl⟩ : syracuseStep 352935 = 529403) B529403
theorem B352975 : Blo 350755 352975 := bstep (se 1 (by rfl) ⟨264731, by rfl⟩ : syracuseStep 352975 = 529463) B529463
theorem B353055 : Blo 350755 353055 := bstep (se 1 (by rfl) ⟨264791, by rfl⟩ : syracuseStep 353055 = 529583) B529583
theorem B1794959 : Blo 350755 1794959 := bstep (se 1 (by rfl) ⟨1346219, by rfl⟩ : syracuseStep 1794959 = 2692439) B2692439
theorem B2155511 : Blo 350755 2155511 := bstep (se 1 (by rfl) ⟨1616633, by rfl⟩ : syracuseStep 2155511 = 3233267) B3233267
theorem B353327 : Blo 350755 353327 := bstep (se 1 (by rfl) ⟨264995, by rfl⟩ : syracuseStep 353327 = 529991) B529991
theorem B353391 : Blo 350755 353391 := bstep (se 1 (by rfl) ⟨265043, by rfl⟩ : syracuseStep 353391 = 530087) B530087
theorem B353447 : Blo 350755 353447 := bstep (se 1 (by rfl) ⟨265085, by rfl⟩ : syracuseStep 353447 = 530171) B530171
theorem B353471 : Blo 350755 353471 := bstep (se 1 (by rfl) ⟨265103, by rfl⟩ : syracuseStep 353471 = 530207) B530207
theorem B353503 : Blo 350755 353503 := bstep (se 1 (by rfl) ⟨265127, by rfl⟩ : syracuseStep 353503 = 530255) B530255
theorem B353583 : Blo 350755 353583 := bstep (se 1 (by rfl) ⟨265187, by rfl⟩ : syracuseStep 353583 = 530375) B530375
theorem B48850289 : Blo 350755 48850289 := bstep (se 2 (by rfl) ⟨18318858, by rfl⟩ : syracuseStep 48850289 = 36637717) B36637717
theorem B353819 : Blo 350755 353819 := bstep (se 1 (by rfl) ⟨265364, by rfl⟩ : syracuseStep 353819 = 530729) B530729
theorem B353823 : Blo 350755 353823 := bstep (se 1 (by rfl) ⟨265367, by rfl⟩ : syracuseStep 353823 = 530735) B530735
theorem B2713171 : Blo 350755 2713171 := bstep (se 1 (by rfl) ⟨2034878, by rfl⟩ : syracuseStep 2713171 = 4069757) B4069757
theorem B353983 : Blo 350755 353983 := bstep (se 1 (by rfl) ⟨265487, by rfl⟩ : syracuseStep 353983 = 530975) B530975
theorem B3794651 : Blo 350755 3794651 := bstep (se 1 (by rfl) ⟨2845988, by rfl⟩ : syracuseStep 3794651 = 5691977) B5691977
theorem B2746075 : Blo 350755 2746075 := bstep (se 1 (by rfl) ⟨2059556, by rfl⟩ : syracuseStep 2746075 = 4119113) B4119113
theorem B1337107 : Blo 350755 1337107 := bstep (se 1 (by rfl) ⟨1002830, by rfl⟩ : syracuseStep 1337107 = 2005661) B2005661
theorem B354239 : Blo 350755 354239 := bstep (se 1 (by rfl) ⟨265679, by rfl⟩ : syracuseStep 354239 = 531359) B531359
theorem B354271 : Blo 350755 354271 := bstep (se 1 (by rfl) ⟨265703, by rfl⟩ : syracuseStep 354271 = 531407) B531407
theorem B354331 : Blo 350755 354331 := bstep (se 1 (by rfl) ⟨265748, by rfl⟩ : syracuseStep 354331 = 531497) B531497
theorem B354335 : Blo 350755 354335 := bstep (se 1 (by rfl) ⟨265751, by rfl⟩ : syracuseStep 354335 = 531503) B531503
theorem B354351 : Blo 350755 354351 := bstep (se 1 (by rfl) ⟨265763, by rfl⟩ : syracuseStep 354351 = 531527) B531527
theorem B354527 : Blo 350755 354527 := bstep (se 1 (by rfl) ⟨265895, by rfl⟩ : syracuseStep 354527 = 531791) B531791
theorem B354587 : Blo 350755 354587 := bstep (se 1 (by rfl) ⟨265940, by rfl⟩ : syracuseStep 354587 = 531881) B531881
theorem B354687 : Blo 350755 354687 := bstep (se 1 (by rfl) ⟨266015, by rfl⟩ : syracuseStep 354687 = 532031) B532031
theorem B1272311 : Blo 350755 1272311 := bstep (se 1 (by rfl) ⟨954233, by rfl⟩ : syracuseStep 1272311 = 1908467) B1908467
theorem B1698889 : Blo 350755 1698889 := bstep (se 2 (by rfl) ⟨637083, by rfl⟩ : syracuseStep 1698889 = 1274167) B1274167
theorem B1338551 : Blo 350755 1338551 := bstep (se 1 (by rfl) ⟨1003913, by rfl⟩ : syracuseStep 1338551 = 2007827) B2007827
theorem B2845925 : Blo 350755 2845925 := bstep (se 4 (by rfl) ⟨266805, by rfl⟩ : syracuseStep 2845925 = 533611) B533611
theorem B1502675 : Blo 350755 1502675 := bstep (se 1 (by rfl) ⟨1127006, by rfl⟩ : syracuseStep 1502675 = 2254013) B2254013
theorem B1339037 : Blo 350755 1339037 := bstep (se 3 (by rfl) ⟨251069, by rfl⟩ : syracuseStep 1339037 = 502139) B502139
theorem B847543 : Blo 350755 847543 := bstep (se 1 (by rfl) ⟨635657, by rfl⟩ : syracuseStep 847543 = 1271315) B1271315
theorem B1339355 : Blo 350755 1339355 := bstep (se 1 (by rfl) ⟨1004516, by rfl⟩ : syracuseStep 1339355 = 2009033) B2009033
theorem B421951 : Blo 350755 421951 := bstep (se 1 (by rfl) ⟨316463, by rfl⟩ : syracuseStep 421951 = 632927) B632927
theorem B1896635 : Blo 350755 1896635 := bstep (se 1 (by rfl) ⟨1422476, by rfl⟩ : syracuseStep 1896635 = 2844953) B2844953
theorem B12415169 : Blo 350755 12415169 := bstep (se 2 (by rfl) ⟨4655688, by rfl⟩ : syracuseStep 12415169 = 9311377) B9311377
theorem B1700119 : Blo 350755 1700119 := bstep (se 1 (by rfl) ⟨1275089, by rfl⟩ : syracuseStep 1700119 = 2550179) B2550179
theorem B1274543 : Blo 350755 1274543 := bstep (se 1 (by rfl) ⟨955907, by rfl⟩ : syracuseStep 1274543 = 1911815) B1911815
theorem B717563 : Blo 350755 717563 := bstep (se 1 (by rfl) ⟨538172, by rfl⟩ : syracuseStep 717563 = 1076345) B1076345
theorem B24671411 : Blo 350755 24671411 := bstep (se 1 (by rfl) ⟨18503558, by rfl⟩ : syracuseStep 24671411 = 37007117) B37007117
theorem B6388079 : Blo 350755 6388079 := bstep (se 1 (by rfl) ⟨4791059, by rfl⟩ : syracuseStep 6388079 = 9582119) B9582119
theorem B2849231 : Blo 350755 2849231 := bstep (se 1 (by rfl) ⟨2136923, by rfl⟩ : syracuseStep 2849231 = 4273847) B4273847
theorem B424607 : Blo 350755 424607 := bstep (se 1 (by rfl) ⟨318455, by rfl⟩ : syracuseStep 424607 = 636911) B636911
theorem B752431 : Blo 350755 752431 := bstep (se 1 (by rfl) ⟨564323, by rfl⟩ : syracuseStep 752431 = 1128647) B1128647
theorem B2030629 : Blo 350755 2030629 := bstep (se 4 (by rfl) ⟨190371, by rfl⟩ : syracuseStep 2030629 = 380743) B380743
theorem B10910807 : Blo 350755 10910807 := bstep (se 1 (by rfl) ⟨8183105, by rfl⟩ : syracuseStep 10910807 = 16366211) B16366211
theorem B851791 : Blo 350755 851791 := bstep (se 1 (by rfl) ⟨638843, by rfl⟩ : syracuseStep 851791 = 1277687) B1277687
theorem B753619 : Blo 350755 753619 := bstep (se 1 (by rfl) ⟨565214, by rfl⟩ : syracuseStep 753619 = 1130429) B1130429
theorem B3014779 : Blo 350755 3014779 := bstep (se 1 (by rfl) ⟨2261084, by rfl⟩ : syracuseStep 3014779 = 4522169) B4522169
theorem B1704563 : Blo 350755 1704563 := bstep (se 1 (by rfl) ⟨1278422, by rfl⟩ : syracuseStep 1704563 = 2556845) B2556845
theorem B951065 : Blo 350755 951065 := bstep (se 2 (by rfl) ⟨356649, by rfl⟩ : syracuseStep 951065 = 713299) B713299
theorem B5079833 : Blo 350755 5079833 := bstep (se 2 (by rfl) ⟨1904937, by rfl⟩ : syracuseStep 5079833 = 3809875) B3809875
theorem B2720537 : Blo 350755 2720537 := bstep (se 2 (by rfl) ⟨1020201, by rfl⟩ : syracuseStep 2720537 = 2040403) B2040403
theorem B6554621 : Blo 350755 6554621 := bstep (se 3 (by rfl) ⟨1228991, by rfl⟩ : syracuseStep 6554621 = 2457983) B2457983
theorem B2589887 : Blo 350755 2589887 := bstep (se 1 (by rfl) ⟨1942415, by rfl⟩ : syracuseStep 2589887 = 3884831) B3884831
theorem B2426431 : Blo 350755 2426431 := bstep (se 1 (by rfl) ⟨1819823, by rfl⟩ : syracuseStep 2426431 = 3639647) B3639647
theorem B4523809 : Blo 350755 4523809 := bstep (se 2 (by rfl) ⟨1696428, by rfl⟩ : syracuseStep 4523809 = 3392857) B3392857
theorem B75171685 : Blo 350755 75171685 := bstep (se 4 (by rfl) ⟨7047345, by rfl⟩ : syracuseStep 75171685 = 14094691) B14094691
theorem B526235 : Blo 350755 526235 := bstep (se 1 (by rfl) ⟨394676, by rfl⟩ : syracuseStep 526235 = 789353) B789353
theorem B526271 : Blo 350755 526271 := bstep (se 1 (by rfl) ⟨394703, by rfl⟩ : syracuseStep 526271 = 789407) B789407
theorem B2263135 : Blo 350755 2263135 := bstep (se 1 (by rfl) ⟨1697351, by rfl⟩ : syracuseStep 2263135 = 3394703) B3394703
theorem B592103 : Blo 350755 592103 := bstep (se 1 (by rfl) ⟨444077, by rfl⟩ : syracuseStep 592103 = 888155) B888155
theorem B592123 : Blo 350755 592123 := bstep (se 1 (by rfl) ⟨444092, by rfl⟩ : syracuseStep 592123 = 888185) B888185
theorem B592265 : Blo 350755 592265 := bstep (se 2 (by rfl) ⟨222099, by rfl⟩ : syracuseStep 592265 = 444199) B444199
theorem B138578435 : Blo 350755 138578435 := bstep (se 1 (by rfl) ⟨103933826, by rfl⟩ : syracuseStep 138578435 = 207867653) B207867653
theorem B526895 : Blo 350755 526895 := bstep (se 1 (by rfl) ⟨395171, by rfl⟩ : syracuseStep 526895 = 790343) B790343
theorem B854687 : Blo 350755 854687 := bstep (se 1 (by rfl) ⟨641015, by rfl⟩ : syracuseStep 854687 = 1282031) B1282031
theorem B527015 : Blo 350755 527015 := bstep (se 1 (by rfl) ⟨395261, by rfl⟩ : syracuseStep 527015 = 790523) B790523
theorem B527081 : Blo 350755 527081 := bstep (se 2 (by rfl) ⟨197655, by rfl⟩ : syracuseStep 527081 = 395311) B395311
theorem B527087 : Blo 350755 527087 := bstep (se 1 (by rfl) ⟨395315, by rfl⟩ : syracuseStep 527087 = 790631) B790631
theorem B527135 : Blo 350755 527135 := bstep (se 1 (by rfl) ⟨395351, by rfl⟩ : syracuseStep 527135 = 790703) B790703
theorem B2001743 : Blo 350755 2001743 := bstep (se 1 (by rfl) ⟨1501307, by rfl⟩ : syracuseStep 2001743 = 3002615) B3002615
theorem B887881 : Blo 350755 887881 := bstep (se 2 (by rfl) ⟨332955, by rfl⟩ : syracuseStep 887881 = 665911) B665911
theorem B527465 : Blo 350755 527465 := bstep (se 2 (by rfl) ⟨197799, by rfl⟩ : syracuseStep 527465 = 395599) B395599
theorem B527591 : Blo 350755 527591 := bstep (se 1 (by rfl) ⟨395693, by rfl⟩ : syracuseStep 527591 = 791387) B791387
theorem B789983 : Blo 350755 789983 := bstep (se 1 (by rfl) ⟨592487, by rfl⟩ : syracuseStep 789983 = 1184975) B1184975
theorem B888479 : Blo 350755 888479 := bstep (se 1 (by rfl) ⟨666359, by rfl⟩ : syracuseStep 888479 = 1332719) B1332719
theorem B659167 : Blo 350755 659167 := bstep (se 1 (by rfl) ⟨494375, by rfl⟩ : syracuseStep 659167 = 988751) B988751
theorem B528095 : Blo 350755 528095 := bstep (se 1 (by rfl) ⟨396071, by rfl⟩ : syracuseStep 528095 = 792143) B792143
theorem B593831 : Blo 350755 593831 := bstep (se 1 (by rfl) ⟨445373, by rfl⟩ : syracuseStep 593831 = 890747) B890747
theorem B528377 : Blo 350755 528377 := bstep (se 2 (by rfl) ⟨198141, by rfl⟩ : syracuseStep 528377 = 396283) B396283
theorem B593993 : Blo 350755 593993 := bstep (se 2 (by rfl) ⟨222747, by rfl⟩ : syracuseStep 593993 = 445495) B445495
theorem B2265185 : Blo 350755 2265185 := bstep (se 2 (by rfl) ⟨849444, by rfl⟩ : syracuseStep 2265185 = 1698889) B1698889
theorem B954523 : Blo 350755 954523 := bstep (se 1 (by rfl) ⟨715892, by rfl⟩ : syracuseStep 954523 = 1431785) B1431785
theorem B528575 : Blo 350755 528575 := bstep (se 1 (by rfl) ⟨396431, by rfl⟩ : syracuseStep 528575 = 792863) B792863
theorem B528617 : Blo 350755 528617 := bstep (se 2 (by rfl) ⟨198231, by rfl⟩ : syracuseStep 528617 = 396463) B396463
theorem B889127 : Blo 350755 889127 := bstep (se 1 (by rfl) ⟨666845, by rfl⟩ : syracuseStep 889127 = 1333691) B1333691
theorem B528743 : Blo 350755 528743 := bstep (se 1 (by rfl) ⟨396557, by rfl⟩ : syracuseStep 528743 = 793115) B793115
theorem B790991 : Blo 350755 790991 := bstep (se 1 (by rfl) ⟨593243, by rfl⟩ : syracuseStep 790991 = 1186487) B1186487
theorem B1610711 : Blo 350755 1610711 := bstep (se 1 (by rfl) ⟨1208033, by rfl⟩ : syracuseStep 1610711 = 2416067) B2416067
theorem B889825 : Blo 350755 889825 := bstep (se 2 (by rfl) ⟨333684, by rfl⟩ : syracuseStep 889825 = 667369) B667369
theorem B1905697 : Blo 350755 1905697 := bstep (se 2 (by rfl) ⟨714636, by rfl⟩ : syracuseStep 1905697 = 1429273) B1429273
theorem B889967 : Blo 350755 889967 := bstep (se 1 (by rfl) ⟨667475, by rfl⟩ : syracuseStep 889967 = 1334951) B1334951
theorem B529577 : Blo 350755 529577 := bstep (se 2 (by rfl) ⟨198591, by rfl⟩ : syracuseStep 529577 = 397183) B397183
theorem B529643 : Blo 350755 529643 := bstep (se 1 (by rfl) ⟨397232, by rfl⟩ : syracuseStep 529643 = 794465) B794465
theorem B529727 : Blo 350755 529727 := bstep (se 1 (by rfl) ⟨397295, by rfl⟩ : syracuseStep 529727 = 794591) B794591
theorem B562601 : Blo 350755 562601 := bstep (se 2 (by rfl) ⟨210975, by rfl⟩ : syracuseStep 562601 = 421951) B421951
theorem B529919 : Blo 350755 529919 := bstep (se 1 (by rfl) ⟨397439, by rfl⟩ : syracuseStep 529919 = 794879) B794879
theorem B530027 : Blo 350755 530027 := bstep (se 1 (by rfl) ⟨397520, by rfl⟩ : syracuseStep 530027 = 795041) B795041
theorem B530297 : Blo 350755 530297 := bstep (se 2 (by rfl) ⟨198861, by rfl⟩ : syracuseStep 530297 = 397723) B397723
theorem B858143 : Blo 350755 858143 := bstep (se 1 (by rfl) ⟨643607, by rfl⟩ : syracuseStep 858143 = 1287215) B1287215
theorem B530543 : Blo 350755 530543 := bstep (se 1 (by rfl) ⟨397907, by rfl⟩ : syracuseStep 530543 = 795815) B795815
theorem B530615 : Blo 350755 530615 := bstep (se 1 (by rfl) ⟨397961, by rfl⟩ : syracuseStep 530615 = 795923) B795923
theorem B891233 : Blo 350755 891233 := bstep (se 2 (by rfl) ⟨334212, by rfl⟩ : syracuseStep 891233 = 668425) B668425
theorem B2529767 : Blo 350755 2529767 := bstep (se 1 (by rfl) ⟨1897325, by rfl⟩ : syracuseStep 2529767 = 3794651) B3794651
theorem B531035 : Blo 350755 531035 := bstep (se 1 (by rfl) ⟨398276, by rfl⟩ : syracuseStep 531035 = 796553) B796553
theorem B531047 : Blo 350755 531047 := bstep (se 1 (by rfl) ⟨398285, by rfl⟩ : syracuseStep 531047 = 796571) B796571
theorem B531071 : Blo 350755 531071 := bstep (se 1 (by rfl) ⟨398303, by rfl⟩ : syracuseStep 531071 = 796607) B796607
theorem B531179 : Blo 350755 531179 := bstep (se 1 (by rfl) ⟨398384, by rfl⟩ : syracuseStep 531179 = 796769) B796769
theorem B531209 : Blo 350755 531209 := bstep (se 2 (by rfl) ⟨199203, by rfl⟩ : syracuseStep 531209 = 398407) B398407
theorem B793385 : Blo 350755 793385 := bstep (se 2 (by rfl) ⟨297519, by rfl⟩ : syracuseStep 793385 = 595039) B595039
theorem B4529141 : Blo 350755 4529141 := bstep (se 5 (by rfl) ⟨212303, by rfl⟩ : syracuseStep 4529141 = 424607) B424607
theorem B531449 : Blo 350755 531449 := bstep (se 2 (by rfl) ⟨199293, by rfl⟩ : syracuseStep 531449 = 398587) B398587
theorem B1186811 : Blo 350755 1186811 := bstep (se 1 (by rfl) ⟨890108, by rfl⟩ : syracuseStep 1186811 = 1780217) B1780217
theorem B793655 : Blo 350755 793655 := bstep (se 1 (by rfl) ⟨595241, by rfl⟩ : syracuseStep 793655 = 1190483) B1190483
theorem B1187243 : Blo 350755 1187243 := bstep (se 1 (by rfl) ⟨890432, by rfl⟩ : syracuseStep 1187243 = 1780865) B1780865
theorem B892367 : Blo 350755 892367 := bstep (se 1 (by rfl) ⟨669275, by rfl⟩ : syracuseStep 892367 = 1338551) B1338551
theorem B532079 : Blo 350755 532079 := bstep (se 1 (by rfl) ⟨399059, by rfl⟩ : syracuseStep 532079 = 798119) B798119
theorem B892691 : Blo 350755 892691 := bstep (se 1 (by rfl) ⟨669518, by rfl⟩ : syracuseStep 892691 = 1339037) B1339037
theorem B794447 : Blo 350755 794447 := bstep (se 1 (by rfl) ⟨595835, by rfl⟩ : syracuseStep 794447 = 1191671) B1191671
theorem B1187783 : Blo 350755 1187783 := bstep (se 1 (by rfl) ⟨890837, by rfl⟩ : syracuseStep 1187783 = 1781675) B1781675
theorem B892903 : Blo 350755 892903 := bstep (se 1 (by rfl) ⟨669677, by rfl⟩ : syracuseStep 892903 = 1339355) B1339355
theorem B4497565 : Blo 350755 4497565 := bstep (se 3 (by rfl) ⟨843293, by rfl⟩ : syracuseStep 4497565 = 1686587) B1686587
theorem B794807 : Blo 350755 794807 := bstep (se 1 (by rfl) ⟨596105, by rfl⟩ : syracuseStep 794807 = 1192211) B1192211
theorem B795167 : Blo 350755 795167 := bstep (se 1 (by rfl) ⟨596375, by rfl⟩ : syracuseStep 795167 = 1192751) B1192751
theorem B6005501 : Blo 350755 6005501 := bstep (se 3 (by rfl) ⟨1126031, by rfl⟩ : syracuseStep 6005501 = 2252063) B2252063
theorem B795743 : Blo 350755 795743 := bstep (se 1 (by rfl) ⟨596807, by rfl⟩ : syracuseStep 795743 = 1193615) B1193615
theorem B795995 : Blo 350755 795995 := bstep (se 1 (by rfl) ⟨596996, by rfl⟩ : syracuseStep 795995 = 1193993) B1193993
theorem B402895 : Blo 350755 402895 := bstep (se 1 (by rfl) ⟨302171, by rfl⟩ : syracuseStep 402895 = 604343) B604343
theorem B796265 : Blo 350755 796265 := bstep (se 2 (by rfl) ⟨298599, by rfl⟩ : syracuseStep 796265 = 597199) B597199
theorem B4008041 : Blo 350755 4008041 := bstep (se 2 (by rfl) ⟨1503015, by rfl⟩ : syracuseStep 4008041 = 3006031) B3006031
theorem B796895 : Blo 350755 796895 := bstep (se 1 (by rfl) ⟨597671, by rfl⟩ : syracuseStep 796895 = 1195343) B1195343
theorem B666731 : Blo 350755 666731 := bstep (se 1 (by rfl) ⟨500048, by rfl⟩ : syracuseStep 666731 = 1000097) B1000097
theorem B1223849 : Blo 350755 1223849 := bstep (se 2 (by rfl) ⟨458943, by rfl⟩ : syracuseStep 1223849 = 917887) B917887
theorem B2010491 : Blo 350755 2010491 := bstep (se 1 (by rfl) ⟨1507868, by rfl⟩ : syracuseStep 2010491 = 3015737) B3015737
theorem B896467 : Blo 350755 896467 := bstep (se 1 (by rfl) ⟨672350, by rfl⟩ : syracuseStep 896467 = 1344701) B1344701
theorem B667111 : Blo 350755 667111 := bstep (se 1 (by rfl) ⟨500333, by rfl⟩ : syracuseStep 667111 = 1000667) B1000667
theorem B1617583 : Blo 350755 1617583 := bstep (se 1 (by rfl) ⟨1213187, by rfl⟩ : syracuseStep 1617583 = 2426375) B2426375
theorem B6795251 : Blo 350755 6795251 := bstep (se 1 (by rfl) ⟨5096438, by rfl⟩ : syracuseStep 6795251 = 10192877) B10192877
theorem B897257 : Blo 350755 897257 := bstep (se 2 (by rfl) ⟨336471, by rfl⟩ : syracuseStep 897257 = 672943) B672943
theorem B602831 : Blo 350755 602831 := bstep (se 1 (by rfl) ⟨452123, by rfl⟩ : syracuseStep 602831 = 904247) B904247
theorem B3617561 : Blo 350755 3617561 := bstep (se 2 (by rfl) ⟨1356585, by rfl⟩ : syracuseStep 3617561 = 2713171) B2713171
theorem B1749815 : Blo 350755 1749815 := bstep (se 1 (by rfl) ⟨1312361, by rfl⟩ : syracuseStep 1749815 = 2624723) B2624723
theorem B1782647 : Blo 350755 1782647 := bstep (se 1 (by rfl) ⟨1336985, by rfl⟩ : syracuseStep 1782647 = 2673971) B2673971
theorem B1749995 : Blo 350755 1749995 := bstep (se 1 (by rfl) ⟨1312496, by rfl⟩ : syracuseStep 1749995 = 2624993) B2624993
theorem B537583 : Blo 350755 537583 := bstep (se 1 (by rfl) ⟨403187, by rfl⟩ : syracuseStep 537583 = 806375) B806375
theorem B3453961 : Blo 350755 3453961 := bstep (se 2 (by rfl) ⟨1295235, by rfl⟩ : syracuseStep 3453961 = 2590471) B2590471
theorem B1782809 : Blo 350755 1782809 := bstep (se 2 (by rfl) ⟨668553, by rfl⟩ : syracuseStep 1782809 = 1337107) B1337107
theorem B1782971 : Blo 350755 1782971 := bstep (se 1 (by rfl) ⟨1337228, by rfl⟩ : syracuseStep 1782971 = 2674457) B2674457
theorem B5748029 : Blo 350755 5748029 := bstep (se 3 (by rfl) ⟨1077755, by rfl⟩ : syracuseStep 5748029 = 2155511) B2155511
theorem B997439 : Blo 350755 997439 := bstep (se 1 (by rfl) ⟨748079, by rfl⟩ : syracuseStep 997439 = 1496159) B1496159
theorem B669799 : Blo 350755 669799 := bstep (se 1 (by rfl) ⟨502349, by rfl⟩ : syracuseStep 669799 = 1004699) B1004699
theorem B571529 : Blo 350755 571529 := bstep (se 2 (by rfl) ⟨214323, by rfl⟩ : syracuseStep 571529 = 428647) B428647
theorem B4569281 : Blo 350755 4569281 := bstep (se 2 (by rfl) ⟨1713480, by rfl⟩ : syracuseStep 4569281 = 3426961) B3426961
theorem B1292663 : Blo 350755 1292663 := bstep (se 1 (by rfl) ⟨969497, by rfl⟩ : syracuseStep 1292663 = 1938995) B1938995
theorem B1686743 : Blo 350755 1686743 := bstep (se 1 (by rfl) ⟨1265057, by rfl⟩ : syracuseStep 1686743 = 2530115) B2530115
theorem B671303 : Blo 350755 671303 := bstep (se 1 (by rfl) ⟨503477, by rfl⟩ : syracuseStep 671303 = 1006955) B1006955
theorem B1130057 : Blo 350755 1130057 := bstep (se 2 (by rfl) ⟨423771, by rfl⟩ : syracuseStep 1130057 = 847543) B847543
theorem B2670569 : Blo 350755 2670569 := bstep (se 2 (by rfl) ⟨1001463, by rfl⟩ : syracuseStep 2670569 = 2002927) B2002927
theorem B1196639 : Blo 350755 1196639 := bstep (se 1 (by rfl) ⟨897479, by rfl⟩ : syracuseStep 1196639 = 1794959) B1794959
theorem B672761 : Blo 350755 672761 := bstep (se 2 (by rfl) ⟨252285, by rfl⟩ : syracuseStep 672761 = 504571) B504571
theorem B2016575 : Blo 350755 2016575 := bstep (se 1 (by rfl) ⟨1512431, by rfl⟩ : syracuseStep 2016575 = 3024863) B3024863
theorem B1001783 : Blo 350755 1001783 := bstep (se 1 (by rfl) ⟨751337, by rfl⟩ : syracuseStep 1001783 = 1502675) B1502675
theorem B1264423 : Blo 350755 1264423 := bstep (se 1 (by rfl) ⟨948317, by rfl⟩ : syracuseStep 1264423 = 1896635) B1896635
theorem B8276779 : Blo 350755 8276779 := bstep (se 1 (by rfl) ⟨6207584, by rfl⟩ : syracuseStep 8276779 = 12415169) B12415169
theorem B478375 : Blo 350755 478375 := bstep (se 1 (by rfl) ⟨358781, by rfl⟩ : syracuseStep 478375 = 717563) B717563
theorem B1003241 : Blo 350755 1003241 := bstep (se 2 (by rfl) ⟨376215, by rfl⟩ : syracuseStep 1003241 = 752431) B752431
theorem B2707505 : Blo 350755 2707505 := bstep (se 2 (by rfl) ⟨1015314, by rfl⟩ : syracuseStep 2707505 = 2030629) B2030629
theorem B4084157 : Blo 350755 4084157 := bstep (se 3 (by rfl) ⟨765779, by rfl⟩ : syracuseStep 4084157 = 1531559) B1531559
theorem B17355485 : Blo 350755 17355485 := bstep (se 3 (by rfl) ⟨3254153, by rfl⟩ : syracuseStep 17355485 = 6508307) B6508307
theorem B2020423 : Blo 350755 2020423 := bstep (se 1 (by rfl) ⟨1515317, by rfl⟩ : syracuseStep 2020423 = 3030635) B3030635
theorem B1135721 : Blo 350755 1135721 := bstep (se 2 (by rfl) ⟨425895, by rfl⟩ : syracuseStep 1135721 = 851791) B851791
theorem B1004825 : Blo 350755 1004825 := bstep (se 2 (by rfl) ⟨376809, by rfl⟩ : syracuseStep 1004825 = 753619) B753619
theorem B448031 : Blo 350755 448031 := bstep (se 1 (by rfl) ⟨336023, by rfl⟩ : syracuseStep 448031 = 672047) B672047
theorem B1136207 : Blo 350755 1136207 := bstep (se 1 (by rfl) ⟨852155, by rfl⟩ : syracuseStep 1136207 = 1704311) B1704311
theorem B9164411 : Blo 350755 9164411 := bstep (se 1 (by rfl) ⟨6873308, by rfl⟩ : syracuseStep 9164411 = 13746617) B13746617
theorem B448735 : Blo 350755 448735 := bstep (se 1 (by rfl) ⟨336551, by rfl⟩ : syracuseStep 448735 = 673103) B673103
theorem B5102203 : Blo 350755 5102203 := bstep (se 1 (by rfl) ⟨3826652, by rfl⟩ : syracuseStep 5102203 = 7653305) B7653305
theorem B350911 : Blo 350755 350911 := bstep (se 1 (by rfl) ⟨263183, by rfl⟩ : syracuseStep 350911 = 526367) B526367
theorem B9067301 : Blo 350755 9067301 := bstep (se 4 (by rfl) ⟨850059, by rfl⟩ : syracuseStep 9067301 = 1700119) B1700119
theorem B2054969 : Blo 350755 2054969 := bstep (se 2 (by rfl) ⟨770613, by rfl⟩ : syracuseStep 2054969 = 1541227) B1541227
theorem B351039 : Blo 350755 351039 := bstep (se 1 (by rfl) ⟨263279, by rfl⟩ : syracuseStep 351039 = 526559) B526559
theorem B351079 : Blo 350755 351079 := bstep (se 1 (by rfl) ⟨263309, by rfl⟩ : syracuseStep 351079 = 526619) B526619
theorem B351295 : Blo 350755 351295 := bstep (se 1 (by rfl) ⟨263471, by rfl⟩ : syracuseStep 351295 = 526943) B526943
theorem B351483 : Blo 350755 351483 := bstep (se 1 (by rfl) ⟨263612, by rfl⟩ : syracuseStep 351483 = 527225) B527225
theorem B351515 : Blo 350755 351515 := bstep (se 1 (by rfl) ⟨263636, by rfl⟩ : syracuseStep 351515 = 527273) B527273
theorem B3824927 : Blo 350755 3824927 := bstep (se 1 (by rfl) ⟨2868695, by rfl⟩ : syracuseStep 3824927 = 5737391) B5737391
theorem B351615 : Blo 350755 351615 := bstep (se 1 (by rfl) ⟨263711, by rfl⟩ : syracuseStep 351615 = 527423) B527423
theorem B2678345 : Blo 350755 2678345 := bstep (se 2 (by rfl) ⟨1004379, by rfl⟩ : syracuseStep 2678345 = 2008759) B2008759
theorem B3661433 : Blo 350755 3661433 := bstep (se 2 (by rfl) ⟨1373037, by rfl⟩ : syracuseStep 3661433 = 2746075) B2746075
theorem B351983 : Blo 350755 351983 := bstep (se 1 (by rfl) ⟨263987, by rfl⟩ : syracuseStep 351983 = 527975) B527975
theorem B352239 : Blo 350755 352239 := bstep (se 1 (by rfl) ⟨264179, by rfl⟩ : syracuseStep 352239 = 528359) B528359
theorem B352319 : Blo 350755 352319 := bstep (se 1 (by rfl) ⟨264239, by rfl⟩ : syracuseStep 352319 = 528479) B528479
theorem B352327 : Blo 350755 352327 := bstep (se 1 (by rfl) ⟨264245, by rfl⟩ : syracuseStep 352327 = 528491) B528491
theorem B352359 : Blo 350755 352359 := bstep (se 1 (by rfl) ⟨264269, by rfl⟩ : syracuseStep 352359 = 528539) B528539
theorem B1007741 : Blo 350755 1007741 := bstep (se 3 (by rfl) ⟨188951, by rfl⟩ : syracuseStep 1007741 = 377903) B377903
theorem B352927 : Blo 350755 352927 := bstep (se 1 (by rfl) ⟨264695, by rfl⟩ : syracuseStep 352927 = 529391) B529391
theorem B353183 : Blo 350755 353183 := bstep (se 1 (by rfl) ⟨264887, by rfl⟩ : syracuseStep 353183 = 529775) B529775
theorem B353263 : Blo 350755 353263 := bstep (se 1 (by rfl) ⟨264947, by rfl⟩ : syracuseStep 353263 = 529895) B529895
theorem B353371 : Blo 350755 353371 := bstep (se 1 (by rfl) ⟨265028, by rfl⟩ : syracuseStep 353371 = 530057) B530057
theorem B353383 : Blo 350755 353383 := bstep (se 1 (by rfl) ⟨265037, by rfl⟩ : syracuseStep 353383 = 530075) B530075
theorem B353511 : Blo 350755 353511 := bstep (se 1 (by rfl) ⟨265133, by rfl⟩ : syracuseStep 353511 = 530267) B530267
theorem B353767 : Blo 350755 353767 := bstep (se 1 (by rfl) ⟨265325, by rfl⟩ : syracuseStep 353767 = 530651) B530651
theorem B1336895 : Blo 350755 1336895 := bstep (se 1 (by rfl) ⟨1002671, by rfl⟩ : syracuseStep 1336895 = 2005343) B2005343
theorem B353947 : Blo 350755 353947 := bstep (se 1 (by rfl) ⟨265460, by rfl⟩ : syracuseStep 353947 = 530921) B530921
theorem B27453329 : Blo 350755 27453329 := bstep (se 2 (by rfl) ⟨10294998, by rfl⟩ : syracuseStep 27453329 = 20589997) B20589997
theorem B354207 : Blo 350755 354207 := bstep (se 1 (by rfl) ⟨265655, by rfl⟩ : syracuseStep 354207 = 531311) B531311
theorem B354215 : Blo 350755 354215 := bstep (se 1 (by rfl) ⟨265661, by rfl⟩ : syracuseStep 354215 = 531323) B531323
theorem B1337579 : Blo 350755 1337579 := bstep (se 1 (by rfl) ⟨1003184, by rfl⟩ : syracuseStep 1337579 = 2006369) B2006369
theorem B1338079 : Blo 350755 1338079 := bstep (se 1 (by rfl) ⟨1003559, by rfl⟩ : syracuseStep 1338079 = 2007119) B2007119
theorem B5139571 : Blo 350755 5139571 := bstep (se 1 (by rfl) ⟨3854678, by rfl⟩ : syracuseStep 5139571 = 7709357) B7709357
theorem B32566859 : Blo 350755 32566859 := bstep (se 1 (by rfl) ⟨24425144, by rfl⟩ : syracuseStep 32566859 = 48850289) B48850289
theorem B17034877 : Blo 350755 17034877 := bstep (se 3 (by rfl) ⟨3194039, by rfl⟩ : syracuseStep 17034877 = 6388079) B6388079
theorem B1339051 : Blo 350755 1339051 := bstep (se 1 (by rfl) ⟨1004288, by rfl⟩ : syracuseStep 1339051 = 2008577) B2008577
theorem B848207 : Blo 350755 848207 := bstep (se 1 (by rfl) ⟨636155, by rfl⟩ : syracuseStep 848207 = 1272311) B1272311
theorem B1208699 : Blo 350755 1208699 := bstep (se 1 (by rfl) ⟨906524, by rfl⟩ : syracuseStep 1208699 = 1813049) B1813049
theorem B1897283 : Blo 350755 1897283 := bstep (se 1 (by rfl) ⟨1422962, by rfl⟩ : syracuseStep 1897283 = 2845925) B2845925
theorem B1340297 : Blo 350755 1340297 := bstep (se 2 (by rfl) ⟨502611, by rfl⟩ : syracuseStep 1340297 = 1005223) B1005223
theorem B1930499 : Blo 350755 1930499 := bstep (se 1 (by rfl) ⟨1447874, by rfl⟩ : syracuseStep 1930499 = 2895749) B2895749
theorem B849695 : Blo 350755 849695 := bstep (se 1 (by rfl) ⟨637271, by rfl⟩ : syracuseStep 849695 = 1274543) B1274543
theorem B16447607 : Blo 350755 16447607 := bstep (se 1 (by rfl) ⟨12335705, by rfl⟩ : syracuseStep 16447607 = 24671411) B24671411
theorem B2259089 : Blo 350755 2259089 := bstep (se 2 (by rfl) ⟨847158, by rfl⟩ : syracuseStep 2259089 = 1694317) B1694317
theorem B2292353 : Blo 350755 2292353 := bstep (se 2 (by rfl) ⟨859632, by rfl⟩ : syracuseStep 2292353 = 1719265) B1719265
theorem B1899487 : Blo 350755 1899487 := bstep (se 1 (by rfl) ⟨1424615, by rfl⟩ : syracuseStep 1899487 = 2849231) B2849231
theorem B7273871 : Blo 350755 7273871 := bstep (se 1 (by rfl) ⟨5455403, by rfl⟩ : syracuseStep 7273871 = 10910807) B10910807
theorem B851849 : Blo 350755 851849 := bstep (se 2 (by rfl) ⟨319443, by rfl⟩ : syracuseStep 851849 = 638887) B638887
theorem B5996753 : Blo 350755 5996753 := bstep (se 2 (by rfl) ⟨2248782, by rfl⟩ : syracuseStep 5996753 = 4497565) B4497565
theorem B1344383 : Blo 350755 1344383 := bstep (se 1 (by rfl) ⟨1008287, by rfl⟩ : syracuseStep 1344383 = 2016575) B2016575
theorem B394735 : Blo 350755 394735 := bstep (se 1 (by rfl) ⟨296051, by rfl⟩ : syracuseStep 394735 = 592103) B592103
theorem B394843 : Blo 350755 394843 := bstep (se 1 (by rfl) ⟨296132, by rfl⟩ : syracuseStep 394843 = 592265) B592265
theorem B526655 : Blo 350755 526655 := bstep (se 1 (by rfl) ⟨394991, by rfl⟩ : syracuseStep 526655 = 789983) B789983
theorem B6031745 : Blo 350755 6031745 := bstep (se 2 (by rfl) ⟨2261904, by rfl⟩ : syracuseStep 6031745 = 4523809) B4523809
theorem B592319 : Blo 350755 592319 := bstep (se 1 (by rfl) ⟨444239, by rfl⟩ : syracuseStep 592319 = 888479) B888479
theorem B395887 : Blo 350755 395887 := bstep (se 1 (by rfl) ⟨296915, by rfl⟩ : syracuseStep 395887 = 593831) B593831
theorem B1805003 : Blo 350755 1805003 := bstep (se 1 (by rfl) ⟨1353752, by rfl⟩ : syracuseStep 1805003 = 2707505) B2707505
theorem B395995 : Blo 350755 395995 := bstep (se 1 (by rfl) ⟨296996, by rfl⟩ : syracuseStep 395995 = 593993) B593993
theorem B3017513 : Blo 350755 3017513 := bstep (se 2 (by rfl) ⟨1131567, by rfl⟩ : syracuseStep 3017513 = 2263135) B2263135
theorem B592751 : Blo 350755 592751 := bstep (se 1 (by rfl) ⟨444563, by rfl⟩ : syracuseStep 592751 = 889127) B889127
theorem B2722771 : Blo 350755 2722771 := bstep (se 1 (by rfl) ⟨2042078, by rfl⟩ : syracuseStep 2722771 = 4084157) B4084157
theorem B527327 : Blo 350755 527327 := bstep (se 1 (by rfl) ⟨395495, by rfl⟩ : syracuseStep 527327 = 790991) B790991
theorem B789497 : Blo 350755 789497 := bstep (se 2 (by rfl) ⟨296061, by rfl⟩ : syracuseStep 789497 = 592123) B592123
theorem B11570323 : Blo 350755 11570323 := bstep (se 1 (by rfl) ⟨8677742, by rfl⟩ : syracuseStep 11570323 = 17355485) B17355485
theorem B757147 : Blo 350755 757147 := bstep (se 1 (by rfl) ⟨567860, by rfl⟩ : syracuseStep 757147 = 1135721) B1135721
theorem B593311 : Blo 350755 593311 := bstep (se 1 (by rfl) ⟨444983, by rfl⟩ : syracuseStep 593311 = 889967) B889967
theorem B1183841 : Blo 350755 1183841 := bstep (se 2 (by rfl) ⟨443940, by rfl⟩ : syracuseStep 1183841 = 887881) B887881
theorem B6852761 : Blo 350755 6852761 := bstep (se 2 (by rfl) ⟨2569785, by rfl⟩ : syracuseStep 6852761 = 5139571) B5139571
theorem B594155 : Blo 350755 594155 := bstep (se 1 (by rfl) ⟨445616, by rfl⟩ : syracuseStep 594155 = 891233) B891233
theorem B528923 : Blo 350755 528923 := bstep (se 1 (by rfl) ⟨396692, by rfl⟩ : syracuseStep 528923 = 793385) B793385
theorem B889481 : Blo 350755 889481 := bstep (se 2 (by rfl) ⟨333555, by rfl⟩ : syracuseStep 889481 = 667111) B667111
theorem B3019427 : Blo 350755 3019427 := bstep (se 1 (by rfl) ⟨2264570, by rfl⟩ : syracuseStep 3019427 = 4529141) B4529141
theorem B791207 : Blo 350755 791207 := bstep (se 1 (by rfl) ⟨593405, by rfl⟩ : syracuseStep 791207 = 1186811) B1186811
theorem B529103 : Blo 350755 529103 := bstep (se 1 (by rfl) ⟨396827, by rfl⟩ : syracuseStep 529103 = 793655) B793655
theorem B2265853 : Blo 350755 2265853 := bstep (se 3 (by rfl) ⟨424847, by rfl⟩ : syracuseStep 2265853 = 849695) B849695
theorem B22713169 : Blo 350755 22713169 := bstep (se 2 (by rfl) ⟨8517438, by rfl⟩ : syracuseStep 22713169 = 17034877) B17034877
theorem B791495 : Blo 350755 791495 := bstep (se 1 (by rfl) ⟨593621, by rfl⟩ : syracuseStep 791495 = 1187243) B1187243
theorem B594911 : Blo 350755 594911 := bstep (se 1 (by rfl) ⟨446183, by rfl⟩ : syracuseStep 594911 = 892367) B892367
theorem B595127 : Blo 350755 595127 := bstep (se 1 (by rfl) ⟨446345, by rfl⟩ : syracuseStep 595127 = 892691) B892691
theorem B529631 : Blo 350755 529631 := bstep (se 1 (by rfl) ⟨397223, by rfl⟩ : syracuseStep 529631 = 794447) B794447
theorem B791855 : Blo 350755 791855 := bstep (se 1 (by rfl) ⟨593891, by rfl⟩ : syracuseStep 791855 = 1187783) B1187783
theorem B529871 : Blo 350755 529871 := bstep (se 1 (by rfl) ⟨397403, by rfl⟩ : syracuseStep 529871 = 794807) B794807
theorem B2659837 : Blo 350755 2659837 := bstep (se 3 (by rfl) ⟨498719, by rfl⟩ : syracuseStep 2659837 = 997439) B997439
theorem B530111 : Blo 350755 530111 := bstep (se 1 (by rfl) ⟨397583, by rfl⟩ : syracuseStep 530111 = 795167) B795167
theorem B4003667 : Blo 350755 4003667 := bstep (se 1 (by rfl) ⟨3002750, by rfl⟩ : syracuseStep 4003667 = 6005501) B6005501
theorem B530495 : Blo 350755 530495 := bstep (se 1 (by rfl) ⟨397871, by rfl⟩ : syracuseStep 530495 = 795743) B795743
theorem B530663 : Blo 350755 530663 := bstep (se 1 (by rfl) ⟨397997, by rfl⟩ : syracuseStep 530663 = 795995) B795995
theorem B3447101 : Blo 350755 3447101 := bstep (se 3 (by rfl) ⟨646331, by rfl⟩ : syracuseStep 3447101 = 1292663) B1292663
theorem B891263 : Blo 350755 891263 := bstep (se 1 (by rfl) ⟨668447, by rfl⟩ : syracuseStep 891263 = 1336895) B1336895
theorem B530843 : Blo 350755 530843 := bstep (se 1 (by rfl) ⟨398132, by rfl⟩ : syracuseStep 530843 = 796265) B796265
theorem B1186433 : Blo 350755 1186433 := bstep (se 2 (by rfl) ⟨444912, by rfl⟩ : syracuseStep 1186433 = 889825) B889825
theorem B2693897 : Blo 350755 2693897 := bstep (se 2 (by rfl) ⟨1010211, by rfl⟩ : syracuseStep 2693897 = 2020423) B2020423
theorem B531263 : Blo 350755 531263 := bstep (se 1 (by rfl) ⟨398447, by rfl⟩ : syracuseStep 531263 = 796895) B796895
theorem B891719 : Blo 350755 891719 := bstep (se 1 (by rfl) ⟨668789, by rfl⟩ : syracuseStep 891719 = 1337579) B1337579
theorem B4530167 : Blo 350755 4530167 := bstep (se 1 (by rfl) ⟨3397625, by rfl⟩ : syracuseStep 4530167 = 6795251) B6795251
theorem B893065 : Blo 350755 893065 := bstep (se 2 (by rfl) ⟨334899, by rfl⟩ : syracuseStep 893065 = 669799) B669799
theorem B598171 : Blo 350755 598171 := bstep (se 1 (by rfl) ⟨448628, by rfl⟩ : syracuseStep 598171 = 897257) B897257
theorem B565471 : Blo 350755 565471 := bstep (se 1 (by rfl) ⟨424103, by rfl⟩ : syracuseStep 565471 = 848207) B848207
theorem B1777949 : Blo 350755 1777949 := bstep (se 3 (by rfl) ⟨333365, by rfl⟩ : syracuseStep 1777949 = 666731) B666731
theorem B598313 : Blo 350755 598313 := bstep (se 2 (by rfl) ⟨224367, by rfl⟩ : syracuseStep 598313 = 448735) B448735
theorem B401887 : Blo 350755 401887 := bstep (se 1 (by rfl) ⟨301415, by rfl⟩ : syracuseStep 401887 = 602831) B602831
theorem B1188431 : Blo 350755 1188431 := bstep (se 1 (by rfl) ⟨891323, by rfl⟩ : syracuseStep 1188431 = 1782647) B1782647
theorem B893531 : Blo 350755 893531 := bstep (se 1 (by rfl) ⟨670148, by rfl⟩ : syracuseStep 893531 = 1340297) B1340297
theorem B1188539 : Blo 350755 1188539 := bstep (se 1 (by rfl) ⟨891404, by rfl⟩ : syracuseStep 1188539 = 1782809) B1782809
theorem B1188647 : Blo 350755 1188647 := bstep (se 1 (by rfl) ⟨891485, by rfl⟩ : syracuseStep 1188647 = 1782971) B1782971
theorem B1286999 : Blo 350755 1286999 := bstep (se 1 (by rfl) ⟨965249, by rfl⟩ : syracuseStep 1286999 = 1930499) B1930499
theorem B3515557 : Blo 350755 3515557 := bstep (se 4 (by rfl) ⟨329583, by rfl⟩ : syracuseStep 3515557 = 659167) B659167
theorem B2532649 : Blo 350755 2532649 := bstep (se 2 (by rfl) ⟨949743, by rfl⟩ : syracuseStep 2532649 = 1899487) B1899487
theorem B1124495 : Blo 350755 1124495 := bstep (se 1 (by rfl) ⟨843371, by rfl⟩ : syracuseStep 1124495 = 1686743) B1686743
theorem B567899 : Blo 350755 567899 := bstep (se 1 (by rfl) ⟨425924, by rfl⟩ : syracuseStep 567899 = 851849) B851849
theorem B1190537 : Blo 350755 1190537 := bstep (se 2 (by rfl) ⟨446451, by rfl⟩ : syracuseStep 1190537 = 892903) B892903
theorem B1780379 : Blo 350755 1780379 := bstep (se 1 (by rfl) ⟨1335284, by rfl⟩ : syracuseStep 1780379 = 2670569) B2670569
theorem B6040493 : Blo 350755 6040493 := bstep (se 3 (by rfl) ⟨1132592, by rfl⟩ : syracuseStep 6040493 = 2265185) B2265185
theorem B797759 : Blo 350755 797759 := bstep (se 1 (by rfl) ⟨598319, by rfl⟩ : syracuseStep 797759 = 1196639) B1196639
theorem B634043 : Blo 350755 634043 := bstep (se 1 (by rfl) ⟨475532, by rfl⟩ : syracuseStep 634043 = 951065) B951065
theorem B3386555 : Blo 350755 3386555 := bstep (se 1 (by rfl) ⟨2539916, by rfl⟩ : syracuseStep 3386555 = 5079833) B5079833
theorem B1813691 : Blo 350755 1813691 := bstep (se 1 (by rfl) ⟨1360268, by rfl⟩ : syracuseStep 1813691 = 2720537) B2720537
theorem B4369747 : Blo 350755 4369747 := bstep (se 1 (by rfl) ⟨3277310, by rfl⟩ : syracuseStep 4369747 = 6554621) B6554621
theorem B5090789 : Blo 350755 5090789 := bstep (se 4 (by rfl) ⟨477261, by rfl⟩ : syracuseStep 5090789 = 954523) B954523
theorem B667855 : Blo 350755 667855 := bstep (se 1 (by rfl) ⟨500891, by rfl⟩ : syracuseStep 667855 = 1001783) B1001783
theorem B92385623 : Blo 350755 92385623 := bstep (se 1 (by rfl) ⟨69289217, by rfl⟩ : syracuseStep 92385623 = 138578435) B138578435
theorem B569791 : Blo 350755 569791 := bstep (se 1 (by rfl) ⟨427343, by rfl⟩ : syracuseStep 569791 = 854687) B854687
theorem B5059421 : Blo 350755 5059421 := bstep (se 3 (by rfl) ⟨948641, by rfl⟩ : syracuseStep 5059421 = 1897283) B1897283
theorem B668827 : Blo 350755 668827 := bstep (se 1 (by rfl) ⟨501620, by rfl⟩ : syracuseStep 668827 = 1003241) B1003241
theorem B669883 : Blo 350755 669883 := bstep (se 1 (by rfl) ⟨502412, by rfl⟩ : syracuseStep 669883 = 1004825) B1004825
theorem B375067 : Blo 350755 375067 := bstep (se 1 (by rfl) ⟨281300, by rfl⟩ : syracuseStep 375067 = 562601) B562601
theorem B1784105 : Blo 350755 1784105 := bstep (se 2 (by rfl) ⟨669039, by rfl⟩ : syracuseStep 1784105 = 1338079) B1338079
theorem B1685897 : Blo 350755 1685897 := bstep (se 2 (by rfl) ⟨632211, by rfl⟩ : syracuseStep 1685897 = 1264423) B1264423
theorem B6109607 : Blo 350755 6109607 := bstep (se 1 (by rfl) ⟨4582205, by rfl⟩ : syracuseStep 6109607 = 9164411) B9164411
theorem B572095 : Blo 350755 572095 := bstep (se 1 (by rfl) ⟨429071, by rfl⟩ : syracuseStep 572095 = 858143) B858143
theorem B1194749 : Blo 350755 1194749 := bstep (se 3 (by rfl) ⟨224015, by rfl⟩ : syracuseStep 1194749 = 448031) B448031
theorem B3029885 : Blo 350755 3029885 := bstep (se 3 (by rfl) ⟨568103, by rfl⟩ : syracuseStep 3029885 = 1136207) B1136207
theorem B1686511 : Blo 350755 1686511 := bstep (se 1 (by rfl) ⟨1264883, by rfl⟩ : syracuseStep 1686511 = 2529767) B2529767
theorem B6044867 : Blo 350755 6044867 := bstep (se 1 (by rfl) ⟨4533650, by rfl⟩ : syracuseStep 6044867 = 9067301) B9067301
theorem B1195289 : Blo 350755 1195289 := bstep (se 2 (by rfl) ⟨448233, by rfl⟩ : syracuseStep 1195289 = 896467) B896467
theorem B1785401 : Blo 350755 1785401 := bstep (se 2 (by rfl) ⟨669525, by rfl⟩ : syracuseStep 1785401 = 1339051) B1339051
theorem B1785563 : Blo 350755 1785563 := bstep (se 1 (by rfl) ⟨1339172, by rfl⟩ : syracuseStep 1785563 = 2678345) B2678345
theorem B2440955 : Blo 350755 2440955 := bstep (se 1 (by rfl) ⟨1830716, by rfl⟩ : syracuseStep 2440955 = 3661433) B3661433
theorem B671827 : Blo 350755 671827 := bstep (se 1 (by rfl) ⟨503870, by rfl⟩ : syracuseStep 671827 = 1007741) B1007741
theorem B1524077 : Blo 350755 1524077 := bstep (se 3 (by rfl) ⟨285764, by rfl⟩ : syracuseStep 1524077 = 571529) B571529
theorem B18302219 : Blo 350755 18302219 := bstep (se 1 (by rfl) ⟨13726664, by rfl⟩ : syracuseStep 18302219 = 27453329) B27453329
theorem B4605281 : Blo 350755 4605281 := bstep (se 2 (by rfl) ⟨1726980, by rfl⟩ : syracuseStep 4605281 = 3453961) B3453961
theorem B2540929 : Blo 350755 2540929 := bstep (se 2 (by rfl) ⟨952848, by rfl⟩ : syracuseStep 2540929 = 1905697) B1905697
theorem B2672027 : Blo 350755 2672027 := bstep (se 1 (by rfl) ⟨2004020, by rfl⟩ : syracuseStep 2672027 = 4008041) B4008041
theorem B21711239 : Blo 350755 21711239 := bstep (se 1 (by rfl) ⟨16283429, by rfl⟩ : syracuseStep 21711239 = 32566859) B32566859
theorem B2148773 : Blo 350755 2148773 := bstep (se 4 (by rfl) ⟨201447, by rfl⟩ : syracuseStep 2148773 = 402895) B402895
theorem B805799 : Blo 350755 805799 := bstep (se 1 (by rfl) ⟨604349, by rfl⟩ : syracuseStep 805799 = 1208699) B1208699
theorem B3263597 : Blo 350755 3263597 := bstep (se 3 (by rfl) ⟨611924, by rfl⟩ : syracuseStep 3263597 = 1223849) B1223849
theorem B2411707 : Blo 350755 2411707 := bstep (se 1 (by rfl) ⟨1808780, by rfl⟩ : syracuseStep 2411707 = 3617561) B3617561
theorem B1166543 : Blo 350755 1166543 := bstep (se 1 (by rfl) ⟨874907, by rfl⟩ : syracuseStep 1166543 = 1749815) B1749815
theorem B1166663 : Blo 350755 1166663 := bstep (se 1 (by rfl) ⟨874997, by rfl⟩ : syracuseStep 1166663 = 1749995) B1749995
theorem B6802937 : Blo 350755 6802937 := bstep (se 2 (by rfl) ⟨2551101, by rfl⟩ : syracuseStep 6802937 = 5102203) B5102203
theorem B10965071 : Blo 350755 10965071 := bstep (se 1 (by rfl) ⟨8223803, by rfl⟩ : syracuseStep 10965071 = 16447607) B16447607
theorem B1528235 : Blo 350755 1528235 := bstep (se 1 (by rfl) ⟨1146176, by rfl⟩ : syracuseStep 1528235 = 2292353) B2292353
theorem B447535 : Blo 350755 447535 := bstep (se 1 (by rfl) ⟨335651, by rfl⟩ : syracuseStep 447535 = 671303) B671303
theorem B4019705 : Blo 350755 4019705 := bstep (se 2 (by rfl) ⟨1507389, by rfl⟩ : syracuseStep 4019705 = 3014779) B3014779
theorem B1136375 : Blo 350755 1136375 := bstep (se 1 (by rfl) ⟨852281, by rfl⟩ : syracuseStep 1136375 = 1704563) B1704563
theorem B448507 : Blo 350755 448507 := bstep (se 1 (by rfl) ⟨336380, by rfl⟩ : syracuseStep 448507 = 672761) B672761
theorem B1726591 : Blo 350755 1726591 := bstep (se 1 (by rfl) ⟨1294943, by rfl⟩ : syracuseStep 1726591 = 2589887) B2589887
theorem B350823 : Blo 350755 350823 := bstep (se 1 (by rfl) ⟨263117, by rfl⟩ : syracuseStep 350823 = 526235) B526235
theorem B350847 : Blo 350755 350847 := bstep (se 1 (by rfl) ⟨263135, by rfl⟩ : syracuseStep 350847 = 526271) B526271
theorem B351263 : Blo 350755 351263 := bstep (se 1 (by rfl) ⟨263447, by rfl⟩ : syracuseStep 351263 = 526895) B526895
theorem B351343 : Blo 350755 351343 := bstep (se 1 (by rfl) ⟨263507, by rfl⟩ : syracuseStep 351343 = 527015) B527015
theorem B351387 : Blo 350755 351387 := bstep (se 1 (by rfl) ⟨263540, by rfl⟩ : syracuseStep 351387 = 527081) B527081
theorem B351391 : Blo 350755 351391 := bstep (se 1 (by rfl) ⟨263543, by rfl⟩ : syracuseStep 351391 = 527087) B527087
theorem B351423 : Blo 350755 351423 := bstep (se 1 (by rfl) ⟨263567, by rfl⟩ : syracuseStep 351423 = 527135) B527135
theorem B1334495 : Blo 350755 1334495 := bstep (se 1 (by rfl) ⟨1000871, by rfl⟩ : syracuseStep 1334495 = 2001743) B2001743
theorem B351643 : Blo 350755 351643 := bstep (se 1 (by rfl) ⟨263732, by rfl⟩ : syracuseStep 351643 = 527465) B527465
theorem B3235241 : Blo 350755 3235241 := bstep (se 2 (by rfl) ⟨1213215, by rfl⟩ : syracuseStep 3235241 = 2426431) B2426431
theorem B351727 : Blo 350755 351727 := bstep (se 1 (by rfl) ⟨263795, by rfl⟩ : syracuseStep 351727 = 527591) B527591
theorem B100228913 : Blo 350755 100228913 := bstep (se 2 (by rfl) ⟨37585842, by rfl⟩ : syracuseStep 100228913 = 75171685) B75171685
theorem B352063 : Blo 350755 352063 := bstep (se 1 (by rfl) ⟨264047, by rfl⟩ : syracuseStep 352063 = 528095) B528095
theorem B352251 : Blo 350755 352251 := bstep (se 1 (by rfl) ⟨264188, by rfl⟩ : syracuseStep 352251 = 528377) B528377
theorem B352383 : Blo 350755 352383 := bstep (se 1 (by rfl) ⟨264287, by rfl⟩ : syracuseStep 352383 = 528575) B528575
theorem B352411 : Blo 350755 352411 := bstep (se 1 (by rfl) ⟨264308, by rfl⟩ : syracuseStep 352411 = 528617) B528617
theorem B352495 : Blo 350755 352495 := bstep (se 1 (by rfl) ⟨264371, by rfl⟩ : syracuseStep 352495 = 528743) B528743
theorem B1073807 : Blo 350755 1073807 := bstep (se 1 (by rfl) ⟨805355, by rfl⟩ : syracuseStep 1073807 = 1610711) B1610711
theorem B353051 : Blo 350755 353051 := bstep (se 1 (by rfl) ⟨264788, by rfl⟩ : syracuseStep 353051 = 529577) B529577
theorem B353095 : Blo 350755 353095 := bstep (se 1 (by rfl) ⟨264821, by rfl⟩ : syracuseStep 353095 = 529643) B529643
theorem B353151 : Blo 350755 353151 := bstep (se 1 (by rfl) ⟨264863, by rfl⟩ : syracuseStep 353151 = 529727) B529727
theorem B353279 : Blo 350755 353279 := bstep (se 1 (by rfl) ⟨264959, by rfl⟩ : syracuseStep 353279 = 529919) B529919
theorem B11035705 : Blo 350755 11035705 := bstep (se 2 (by rfl) ⟨4138389, by rfl⟩ : syracuseStep 11035705 = 8276779) B8276779
theorem B353351 : Blo 350755 353351 := bstep (se 1 (by rfl) ⟨265013, by rfl⟩ : syracuseStep 353351 = 530027) B530027
theorem B353531 : Blo 350755 353531 := bstep (se 1 (by rfl) ⟨265148, by rfl⟩ : syracuseStep 353531 = 530297) B530297
theorem B353695 : Blo 350755 353695 := bstep (se 1 (by rfl) ⟨265271, by rfl⟩ : syracuseStep 353695 = 530543) B530543
theorem B353743 : Blo 350755 353743 := bstep (se 1 (by rfl) ⟨265307, by rfl⟩ : syracuseStep 353743 = 530615) B530615
theorem B354023 : Blo 350755 354023 := bstep (se 1 (by rfl) ⟨265517, by rfl⟩ : syracuseStep 354023 = 531035) B531035
theorem B354031 : Blo 350755 354031 := bstep (se 1 (by rfl) ⟨265523, by rfl⟩ : syracuseStep 354031 = 531047) B531047
theorem B354047 : Blo 350755 354047 := bstep (se 1 (by rfl) ⟨265535, by rfl⟩ : syracuseStep 354047 = 531071) B531071
theorem B354119 : Blo 350755 354119 := bstep (se 1 (by rfl) ⟨265589, by rfl⟩ : syracuseStep 354119 = 531179) B531179
theorem B354139 : Blo 350755 354139 := bstep (se 1 (by rfl) ⟨265604, by rfl⟩ : syracuseStep 354139 = 531209) B531209
theorem B1369979 : Blo 350755 1369979 := bstep (se 1 (by rfl) ⟨1027484, by rfl⟩ : syracuseStep 1369979 = 2054969) B2054969
theorem B354299 : Blo 350755 354299 := bstep (se 1 (by rfl) ⟨265724, by rfl⟩ : syracuseStep 354299 = 531449) B531449
theorem B2549951 : Blo 350755 2549951 := bstep (se 1 (by rfl) ⟨1912463, by rfl⟩ : syracuseStep 2549951 = 3824927) B3824927
theorem B2156777 : Blo 350755 2156777 := bstep (se 2 (by rfl) ⟨808791, by rfl⟩ : syracuseStep 2156777 = 1617583) B1617583
theorem B354719 : Blo 350755 354719 := bstep (se 1 (by rfl) ⟨266039, by rfl⟩ : syracuseStep 354719 = 532079) B532079
theorem B2551333 : Blo 350755 2551333 := bstep (se 4 (by rfl) ⟨239187, by rfl⟩ : syracuseStep 2551333 = 478375) B478375
theorem B716777 : Blo 350755 716777 := bstep (se 2 (by rfl) ⟨268791, by rfl⟩ : syracuseStep 716777 = 537583) B537583
theorem B1340327 : Blo 350755 1340327 := bstep (se 1 (by rfl) ⟨1005245, by rfl⟩ : syracuseStep 1340327 = 2010491) B2010491
theorem B3832019 : Blo 350755 3832019 := bstep (se 1 (by rfl) ⟨2874014, by rfl⟩ : syracuseStep 3832019 = 5748029) B5748029
theorem B1506059 : Blo 350755 1506059 := bstep (se 1 (by rfl) ⟨1129544, by rfl⟩ : syracuseStep 1506059 = 2259089) B2259089
theorem B3046187 : Blo 350755 3046187 := bstep (se 1 (by rfl) ⟨2284640, by rfl⟩ : syracuseStep 3046187 = 4569281) B4569281
theorem B4849247 : Blo 350755 4849247 := bstep (se 1 (by rfl) ⟨3636935, by rfl⟩ : syracuseStep 4849247 = 7273871) B7273871
theorem B753371 : Blo 350755 753371 := bstep (se 1 (by rfl) ⟨565028, by rfl⟩ : syracuseStep 753371 = 1130057) B1130057
theorem B3997835 : Blo 350755 3997835 := bstep (se 1 (by rfl) ⟨2998376, by rfl⟩ : syracuseStep 3997835 = 5996753) B5996753
theorem B1016051 : Blo 350755 1016051 := bstep (se 1 (by rfl) ⟨762038, by rfl⟩ : syracuseStep 1016051 = 1524077) B1524077
theorem B753961 : Blo 350755 753961 := bstep (se 2 (by rfl) ⟨282735, by rfl⟩ : syracuseStep 753961 = 565471) B565471
theorem B14714273 : Blo 350755 14714273 := bstep (se 2 (by rfl) ⟨5517852, by rfl⟩ : syracuseStep 14714273 = 11035705) B11035705
theorem B4687409 : Blo 350755 4687409 := bstep (se 2 (by rfl) ⟨1757778, by rfl⟩ : syracuseStep 4687409 = 3515557) B3515557
theorem B394879 : Blo 350755 394879 := bstep (se 1 (by rfl) ⟨296159, by rfl⟩ : syracuseStep 394879 = 592319) B592319
theorem B3376865 : Blo 350755 3376865 := bstep (se 2 (by rfl) ⟨1266324, by rfl⟩ : syracuseStep 3376865 = 2532649) B2532649
theorem B395167 : Blo 350755 395167 := bstep (se 1 (by rfl) ⟨296375, by rfl⟩ : syracuseStep 395167 = 592751) B592751
theorem B526313 : Blo 350755 526313 := bstep (se 2 (by rfl) ⟨197367, by rfl⟩ : syracuseStep 526313 = 394735) B394735
theorem B526331 : Blo 350755 526331 := bstep (se 1 (by rfl) ⟨394748, by rfl⟩ : syracuseStep 526331 = 789497) B789497
theorem B526457 : Blo 350755 526457 := bstep (se 2 (by rfl) ⟨197421, by rfl⟩ : syracuseStep 526457 = 394843) B394843
theorem B7310047 : Blo 350755 7310047 := bstep (se 1 (by rfl) ⟨5482535, by rfl⟩ : syracuseStep 7310047 = 10965071) B10965071
theorem B789227 : Blo 350755 789227 := bstep (se 1 (by rfl) ⟨591920, by rfl⟩ : syracuseStep 789227 = 1183841) B1183841
theorem B396103 : Blo 350755 396103 := bstep (se 1 (by rfl) ⟨297077, by rfl⟩ : syracuseStep 396103 = 594155) B594155
theorem B1018823 : Blo 350755 1018823 := bstep (se 1 (by rfl) ⟨764117, by rfl⟩ : syracuseStep 1018823 = 1528235) B1528235
theorem B592987 : Blo 350755 592987 := bstep (se 1 (by rfl) ⟨444740, by rfl⟩ : syracuseStep 592987 = 889481) B889481
theorem B527471 : Blo 350755 527471 := bstep (se 1 (by rfl) ⟨395603, by rfl⟩ : syracuseStep 527471 = 791207) B791207
theorem B527663 : Blo 350755 527663 := bstep (se 1 (by rfl) ⟨395747, by rfl⟩ : syracuseStep 527663 = 791495) B791495
theorem B396607 : Blo 350755 396607 := bstep (se 1 (by rfl) ⟨297455, by rfl⟩ : syracuseStep 396607 = 594911) B594911
theorem B396751 : Blo 350755 396751 := bstep (se 1 (by rfl) ⟨297563, by rfl⟩ : syracuseStep 396751 = 595127) B595127
theorem B527849 : Blo 350755 527849 := bstep (se 2 (by rfl) ⟨197943, by rfl⟩ : syracuseStep 527849 = 395887) B395887
theorem B527903 : Blo 350755 527903 := bstep (se 1 (by rfl) ⟨395927, by rfl⟩ : syracuseStep 527903 = 791855) B791855
theorem B527993 : Blo 350755 527993 := bstep (se 2 (by rfl) ⟨197997, by rfl⟩ : syracuseStep 527993 = 395995) B395995
theorem B3051173 : Blo 350755 3051173 := bstep (se 4 (by rfl) ⟨286047, by rfl⟩ : syracuseStep 3051173 = 572095) B572095
theorem B757583 : Blo 350755 757583 := bstep (se 1 (by rfl) ⟨568187, by rfl⟩ : syracuseStep 757583 = 1136375) B1136375
theorem B3215609 : Blo 350755 3215609 := bstep (se 2 (by rfl) ⟨1205853, by rfl⟩ : syracuseStep 3215609 = 2411707) B2411707
theorem B594175 : Blo 350755 594175 := bstep (se 1 (by rfl) ⟨445631, by rfl⟩ : syracuseStep 594175 = 891263) B891263
theorem B790955 : Blo 350755 790955 := bstep (se 1 (by rfl) ⟨593216, by rfl⟩ : syracuseStep 790955 = 1186433) B1186433
theorem B791081 : Blo 350755 791081 := bstep (se 2 (by rfl) ⟨296655, by rfl⟩ : syracuseStep 791081 = 593311) B593311
theorem B594479 : Blo 350755 594479 := bstep (se 1 (by rfl) ⟨445859, by rfl⟩ : syracuseStep 594479 = 891719) B891719
theorem B889663 : Blo 350755 889663 := bstep (se 1 (by rfl) ⟨667247, by rfl⟩ : syracuseStep 889663 = 1334495) B1334495
theorem B66819275 : Blo 350755 66819275 := bstep (se 1 (by rfl) ⟨50114456, by rfl⟩ : syracuseStep 66819275 = 100228913) B100228913
theorem B3020111 : Blo 350755 3020111 := bstep (se 1 (by rfl) ⟨2265083, by rfl⟩ : syracuseStep 3020111 = 4530167) B4530167
theorem B1185299 : Blo 350755 1185299 := bstep (se 1 (by rfl) ⟨888974, by rfl⟩ : syracuseStep 1185299 = 1777949) B1777949
theorem B398875 : Blo 350755 398875 := bstep (se 1 (by rfl) ⟨299156, by rfl⟩ : syracuseStep 398875 = 598313) B598313
theorem B890473 : Blo 350755 890473 := bstep (se 2 (by rfl) ⟨333927, by rfl⟩ : syracuseStep 890473 = 667855) B667855
theorem B792287 : Blo 350755 792287 := bstep (se 1 (by rfl) ⟨594215, by rfl⟩ : syracuseStep 792287 = 1188431) B1188431
theorem B595687 : Blo 350755 595687 := bstep (se 1 (by rfl) ⟨446765, by rfl⟩ : syracuseStep 595687 = 893531) B893531
theorem B792359 : Blo 350755 792359 := bstep (se 1 (by rfl) ⟨594269, by rfl⟩ : syracuseStep 792359 = 1188539) B1188539
theorem B792431 : Blo 350755 792431 := bstep (se 1 (by rfl) ⟨594323, by rfl⟩ : syracuseStep 792431 = 1188647) B1188647
theorem B857999 : Blo 350755 857999 := bstep (se 1 (by rfl) ⟨643499, by rfl⟩ : syracuseStep 857999 = 1286999) B1286999
theorem B759721 : Blo 350755 759721 := bstep (se 2 (by rfl) ⟨284895, by rfl⟩ : syracuseStep 759721 = 569791) B569791
theorem B3021137 : Blo 350755 3021137 := bstep (se 2 (by rfl) ⟨1132926, by rfl⟩ : syracuseStep 3021137 = 2265853) B2265853
theorem B16292285 : Blo 350755 16292285 := bstep (se 3 (by rfl) ⟨3054803, by rfl⟩ : syracuseStep 16292285 = 6109607) B6109607
theorem B30284225 : Blo 350755 30284225 := bstep (se 2 (by rfl) ⟨11356584, by rfl⟩ : syracuseStep 30284225 = 22713169) B22713169
theorem B596713 : Blo 350755 596713 := bstep (se 2 (by rfl) ⟨223767, by rfl⟩ : syracuseStep 596713 = 447535) B447535
theorem B891769 : Blo 350755 891769 := bstep (se 2 (by rfl) ⟨334413, by rfl⟩ : syracuseStep 891769 = 668827) B668827
theorem B793691 : Blo 350755 793691 := bstep (se 1 (by rfl) ⟨595268, by rfl⟩ : syracuseStep 793691 = 1190537) B1190537
theorem B1186919 : Blo 350755 1186919 := bstep (se 1 (by rfl) ⟨890189, by rfl⟩ : syracuseStep 1186919 = 1780379) B1780379
theorem B3546449 : Blo 350755 3546449 := bstep (se 2 (by rfl) ⟨1329918, by rfl⟩ : syracuseStep 3546449 = 2659837) B2659837
theorem B531839 : Blo 350755 531839 := bstep (se 1 (by rfl) ⟨398879, by rfl⟩ : syracuseStep 531839 = 797759) B797759
theorem B598009 : Blo 350755 598009 := bstep (se 2 (by rfl) ⟨224253, by rfl⟩ : syracuseStep 598009 = 448507) B448507
theorem B2302121 : Blo 350755 2302121 := bstep (se 2 (by rfl) ⟨863295, by rfl⟩ : syracuseStep 2302121 = 1726591) B1726591
theorem B893177 : Blo 350755 893177 := bstep (se 2 (by rfl) ⟨334941, by rfl⟩ : syracuseStep 893177 = 669883) B669883
theorem B500089 : Blo 350755 500089 := bstep (se 2 (by rfl) ⟨187533, by rfl⟩ : syracuseStep 500089 = 375067) B375067
theorem B893551 : Blo 350755 893551 := bstep (se 1 (by rfl) ⟨670163, by rfl⟩ : syracuseStep 893551 = 1340327) B1340327
theorem B1189403 : Blo 350755 1189403 := bstep (se 1 (by rfl) ⟨892052, by rfl⟩ : syracuseStep 1189403 = 1784105) B1784105
theorem B1123931 : Blo 350755 1123931 := bstep (se 1 (by rfl) ⟨842948, by rfl⟩ : syracuseStep 1123931 = 1685897) B1685897
theorem B796499 : Blo 350755 796499 := bstep (se 1 (by rfl) ⟨597374, by rfl⟩ : syracuseStep 796499 = 1194749) B1194749
theorem B796859 : Blo 350755 796859 := bstep (se 1 (by rfl) ⟨597644, by rfl⟩ : syracuseStep 796859 = 1195289) B1195289
theorem B1190267 : Blo 350755 1190267 := bstep (se 1 (by rfl) ⟨892700, by rfl⟩ : syracuseStep 1190267 = 1785401) B1785401
theorem B1190375 : Blo 350755 1190375 := bstep (se 1 (by rfl) ⟨892781, by rfl⟩ : syracuseStep 1190375 = 1785563) B1785563
theorem B502247 : Blo 350755 502247 := bstep (se 1 (by rfl) ⟨376685, by rfl⟩ : syracuseStep 502247 = 753371) B753371
theorem B895769 : Blo 350755 895769 := bstep (se 2 (by rfl) ⟨335913, by rfl⟩ : syracuseStep 895769 = 671827) B671827
theorem B1190753 : Blo 350755 1190753 := bstep (se 2 (by rfl) ⟨446532, by rfl⟩ : syracuseStep 1190753 = 893065) B893065
theorem B797561 : Blo 350755 797561 := bstep (se 2 (by rfl) ⟨299085, by rfl⟩ : syracuseStep 797561 = 598171) B598171
theorem B896255 : Blo 350755 896255 := bstep (se 1 (by rfl) ⟨672191, by rfl⟩ : syracuseStep 896255 = 1344383) B1344383
theorem B12201479 : Blo 350755 12201479 := bstep (se 1 (by rfl) ⟨9151109, by rfl⟩ : syracuseStep 12201479 = 18302219) B18302219
theorem B1781351 : Blo 350755 1781351 := bstep (se 1 (by rfl) ⟨1336013, by rfl⟩ : syracuseStep 1781351 = 2672027) B2672027
theorem B3387905 : Blo 350755 3387905 := bstep (se 2 (by rfl) ⟨1270464, by rfl⟩ : syracuseStep 3387905 = 2540929) B2540929
theorem B2011675 : Blo 350755 2011675 := bstep (se 1 (by rfl) ⟨1508756, by rfl⟩ : syracuseStep 2011675 = 3017513) B3017513
theorem B537199 : Blo 350755 537199 := bstep (se 1 (by rfl) ⟨402899, by rfl⟩ : syracuseStep 537199 = 805799) B805799
theorem B2175731 : Blo 350755 2175731 := bstep (se 1 (by rfl) ⟨1631798, by rfl⟩ : syracuseStep 2175731 = 3263597) B3263597
theorem B4535291 : Blo 350755 4535291 := bstep (se 1 (by rfl) ⟨3401468, by rfl⟩ : syracuseStep 4535291 = 6802937) B6802937
theorem B2143397 : Blo 350755 2143397 := bstep (se 4 (by rfl) ⟨200943, by rfl⟩ : syracuseStep 2143397 = 401887) B401887
theorem B4568507 : Blo 350755 4568507 := bstep (se 1 (by rfl) ⟨3426380, by rfl⟩ : syracuseStep 4568507 = 6852761) B6852761
theorem B2012951 : Blo 350755 2012951 := bstep (se 1 (by rfl) ⟨1509713, by rfl⟩ : syracuseStep 2012951 = 3019427) B3019427
theorem B2669111 : Blo 350755 2669111 := bstep (se 1 (by rfl) ⟨2001833, by rfl⟩ : syracuseStep 2669111 = 4003667) B4003667
theorem B9192269 : Blo 350755 9192269 := bstep (se 3 (by rfl) ⟨1723550, by rfl⟩ : syracuseStep 9192269 = 3447101) B3447101
theorem B378599 : Blo 350755 378599 := bstep (se 1 (by rfl) ⟨283949, by rfl⟩ : syracuseStep 378599 = 567899) B567899
theorem B3393859 : Blo 350755 3393859 := bstep (se 1 (by rfl) ⟨2545394, by rfl⟩ : syracuseStep 3393859 = 5090789) B5090789
theorem B477851 : Blo 350755 477851 := bstep (se 1 (by rfl) ⟨358388, by rfl⟩ : syracuseStep 477851 = 716777) B716777
theorem B61590415 : Blo 350755 61590415 := bstep (se 1 (by rfl) ⟨46192811, by rfl⟩ : syracuseStep 61590415 = 92385623) B92385623
theorem B2248681 : Blo 350755 2248681 := bstep (se 2 (by rfl) ⟨843255, by rfl⟩ : syracuseStep 2248681 = 1686511) B1686511
theorem B1004039 : Blo 350755 1004039 := bstep (se 1 (by rfl) ⟨753029, by rfl⟩ : syracuseStep 1004039 = 1506059) B1506059
theorem B2019923 : Blo 350755 2019923 := bstep (se 1 (by rfl) ⟨1514942, by rfl⟩ : syracuseStep 2019923 = 3029885) B3029885
theorem B3232831 : Blo 350755 3232831 := bstep (se 1 (by rfl) ⟨2424623, by rfl⟩ : syracuseStep 3232831 = 4849247) B4849247
theorem B1627303 : Blo 350755 1627303 := bstep (se 1 (by rfl) ⟨1220477, by rfl⟩ : syracuseStep 1627303 = 2440955) B2440955
theorem B3070187 : Blo 350755 3070187 := bstep (se 1 (by rfl) ⟨2302640, by rfl⟩ : syracuseStep 3070187 = 4605281) B4605281
theorem B351103 : Blo 350755 351103 := bstep (se 1 (by rfl) ⟨263327, by rfl⟩ : syracuseStep 351103 = 526655) B526655
theorem B4021163 : Blo 350755 4021163 := bstep (se 1 (by rfl) ⟨3015872, by rfl⟩ : syracuseStep 4021163 = 6031745) B6031745
theorem B14474159 : Blo 350755 14474159 := bstep (se 1 (by rfl) ⟨10855619, by rfl⟩ : syracuseStep 14474159 = 21711239) B21711239
theorem B1203335 : Blo 350755 1203335 := bstep (se 1 (by rfl) ⟨902501, by rfl⟩ : syracuseStep 1203335 = 1805003) B1805003
theorem B351551 : Blo 350755 351551 := bstep (se 1 (by rfl) ⟨263663, by rfl⟩ : syracuseStep 351551 = 527327) B527327
theorem B777695 : Blo 350755 777695 := bstep (se 1 (by rfl) ⟨583271, by rfl⟩ : syracuseStep 777695 = 1166543) B1166543
theorem B777775 : Blo 350755 777775 := bstep (se 1 (by rfl) ⟨583331, by rfl⟩ : syracuseStep 777775 = 1166663) B1166663
theorem B352615 : Blo 350755 352615 := bstep (se 1 (by rfl) ⟨264461, by rfl⟩ : syracuseStep 352615 = 528923) B528923
theorem B352735 : Blo 350755 352735 := bstep (se 1 (by rfl) ⟨264551, by rfl⟩ : syracuseStep 352735 = 529103) B529103
theorem B353087 : Blo 350755 353087 := bstep (se 1 (by rfl) ⟨264815, by rfl⟩ : syracuseStep 353087 = 529631) B529631
theorem B353247 : Blo 350755 353247 := bstep (se 1 (by rfl) ⟨264935, by rfl⟩ : syracuseStep 353247 = 529871) B529871
theorem B2679803 : Blo 350755 2679803 := bstep (se 1 (by rfl) ⟨2009852, by rfl⟩ : syracuseStep 2679803 = 4019705) B4019705
theorem B353407 : Blo 350755 353407 := bstep (se 1 (by rfl) ⟨265055, by rfl⟩ : syracuseStep 353407 = 530111) B530111
theorem B3630361 : Blo 350755 3630361 := bstep (se 2 (by rfl) ⟨1361385, by rfl⟩ : syracuseStep 3630361 = 2722771) B2722771
theorem B353663 : Blo 350755 353663 := bstep (se 1 (by rfl) ⟨265247, by rfl⟩ : syracuseStep 353663 = 530495) B530495
theorem B353775 : Blo 350755 353775 := bstep (se 1 (by rfl) ⟨265331, by rfl⟩ : syracuseStep 353775 = 530663) B530663
theorem B15427097 : Blo 350755 15427097 := bstep (se 2 (by rfl) ⟨5785161, by rfl⟩ : syracuseStep 15427097 = 11570323) B11570323
theorem B353895 : Blo 350755 353895 := bstep (se 1 (by rfl) ⟨265421, by rfl⟩ : syracuseStep 353895 = 530843) B530843
theorem B5826329 : Blo 350755 5826329 := bstep (se 2 (by rfl) ⟨2184873, by rfl⟩ : syracuseStep 5826329 = 4369747) B4369747
theorem B1795931 : Blo 350755 1795931 := bstep (se 1 (by rfl) ⟨1346948, by rfl⟩ : syracuseStep 1795931 = 2693897) B2693897
theorem B1009529 : Blo 350755 1009529 := bstep (se 2 (by rfl) ⟨378573, by rfl⟩ : syracuseStep 1009529 = 757147) B757147
theorem B354175 : Blo 350755 354175 := bstep (se 1 (by rfl) ⟨265631, by rfl⟩ : syracuseStep 354175 = 531263) B531263
theorem B3401777 : Blo 350755 3401777 := bstep (se 2 (by rfl) ⟨1275666, by rfl⟩ : syracuseStep 3401777 = 2551333) B2551333
theorem B2156827 : Blo 350755 2156827 := bstep (se 1 (by rfl) ⟨1617620, by rfl⟩ : syracuseStep 2156827 = 3235241) B3235241
theorem B715871 : Blo 350755 715871 := bstep (se 1 (by rfl) ⟨536903, by rfl⟩ : syracuseStep 715871 = 1073807) B1073807
theorem B5730061 : Blo 350755 5730061 := bstep (se 3 (by rfl) ⟨1074386, by rfl⟩ : syracuseStep 5730061 = 2148773) B2148773
theorem B913319 : Blo 350755 913319 := bstep (se 1 (by rfl) ⟨684989, by rfl⟩ : syracuseStep 913319 = 1369979) B1369979
theorem B749663 : Blo 350755 749663 := bstep (se 1 (by rfl) ⟨562247, by rfl⟩ : syracuseStep 749663 = 1124495) B1124495
theorem B1699967 : Blo 350755 1699967 := bstep (se 1 (by rfl) ⟨1274975, by rfl⟩ : syracuseStep 1699967 = 2549951) B2549951
theorem B1437851 : Blo 350755 1437851 := bstep (se 1 (by rfl) ⟨1078388, by rfl⟩ : syracuseStep 1437851 = 2156777) B2156777
theorem B4026995 : Blo 350755 4026995 := bstep (se 1 (by rfl) ⟨3020246, by rfl⟩ : syracuseStep 4026995 = 6040493) B6040493
theorem B422695 : Blo 350755 422695 := bstep (se 1 (by rfl) ⟨317021, by rfl⟩ : syracuseStep 422695 = 634043) B634043
theorem B2257703 : Blo 350755 2257703 := bstep (se 1 (by rfl) ⟨1693277, by rfl⟩ : syracuseStep 2257703 = 3386555) B3386555
theorem B1209127 : Blo 350755 1209127 := bstep (se 1 (by rfl) ⟨906845, by rfl⟩ : syracuseStep 1209127 = 1813691) B1813691
theorem B3372947 : Blo 350755 3372947 := bstep (se 1 (by rfl) ⟨2529710, by rfl⟩ : syracuseStep 3372947 = 5059421) B5059421
theorem B2554679 : Blo 350755 2554679 := bstep (se 1 (by rfl) ⟨1916009, by rfl⟩ : syracuseStep 2554679 = 3832019) B3832019
theorem B2030791 : Blo 350755 2030791 := bstep (se 1 (by rfl) ⟨1523093, by rfl⟩ : syracuseStep 2030791 = 3046187) B3046187
theorem B4029911 : Blo 350755 4029911 := bstep (se 1 (by rfl) ⟨3022433, by rfl⟩ : syracuseStep 4029911 = 6044867) B6044867
theorem B6128179 : Blo 350755 6128179 := bstep (se 1 (by rfl) ⟨4596134, by rfl⟩ : syracuseStep 6128179 = 9192269) B9192269
theorem B526151 : Blo 350755 526151 := bstep (se 1 (by rfl) ⟨394613, by rfl⟩ : syracuseStep 526151 = 789227) B789227
theorem B526505 : Blo 350755 526505 := bstep (se 2 (by rfl) ⟨197439, by rfl⟩ : syracuseStep 526505 = 394879) B394879
theorem B2034115 : Blo 350755 2034115 := bstep (se 1 (by rfl) ⟨1525586, by rfl⟩ : syracuseStep 2034115 = 3051173) B3051173
theorem B526889 : Blo 350755 526889 := bstep (se 2 (by rfl) ⟨197583, by rfl⟩ : syracuseStep 526889 = 395167) B395167
theorem B527303 : Blo 350755 527303 := bstep (se 1 (by rfl) ⟨395477, by rfl⟩ : syracuseStep 527303 = 790955) B790955
theorem B527387 : Blo 350755 527387 := bstep (se 1 (by rfl) ⟨395540, by rfl⟩ : syracuseStep 527387 = 791081) B791081
theorem B396319 : Blo 350755 396319 := bstep (se 1 (by rfl) ⟨297239, by rfl⟩ : syracuseStep 396319 = 594479) B594479
theorem B1346615 : Blo 350755 1346615 := bstep (se 1 (by rfl) ⟨1009961, by rfl⟩ : syracuseStep 1346615 = 2019923) B2019923
theorem B4525145 : Blo 350755 4525145 := bstep (se 2 (by rfl) ⟨1696929, by rfl⟩ : syracuseStep 4525145 = 3393859) B3393859
theorem B790199 : Blo 350755 790199 := bstep (se 1 (by rfl) ⟨592649, by rfl⟩ : syracuseStep 790199 = 1185299) B1185299
theorem B528137 : Blo 350755 528137 := bstep (se 2 (by rfl) ⟨198051, by rfl⟩ : syracuseStep 528137 = 396103) B396103
theorem B528191 : Blo 350755 528191 := bstep (se 1 (by rfl) ⟨396143, by rfl⟩ : syracuseStep 528191 = 792287) B792287
theorem B82120553 : Blo 350755 82120553 := bstep (se 2 (by rfl) ⟨30795207, by rfl⟩ : syracuseStep 82120553 = 61590415) B61590415
theorem B528239 : Blo 350755 528239 := bstep (se 1 (by rfl) ⟨396179, by rfl⟩ : syracuseStep 528239 = 792359) B792359
theorem B528287 : Blo 350755 528287 := bstep (se 1 (by rfl) ⟨396215, by rfl⟩ : syracuseStep 528287 = 792431) B792431
theorem B790649 : Blo 350755 790649 := bstep (se 2 (by rfl) ⟨296493, by rfl⟩ : syracuseStep 790649 = 592987) B592987
theorem B20189483 : Blo 350755 20189483 := bstep (se 1 (by rfl) ⟨15142112, by rfl⟩ : syracuseStep 20189483 = 30284225) B30284225
theorem B528809 : Blo 350755 528809 := bstep (se 2 (by rfl) ⟨198303, by rfl⟩ : syracuseStep 528809 = 396607) B396607
theorem B529001 : Blo 350755 529001 := bstep (se 2 (by rfl) ⟨198375, by rfl⟩ : syracuseStep 529001 = 396751) B396751
theorem B529127 : Blo 350755 529127 := bstep (se 1 (by rfl) ⟨396845, by rfl⟩ : syracuseStep 529127 = 793691) B793691
theorem B791279 : Blo 350755 791279 := bstep (se 1 (by rfl) ⟨593459, by rfl⟩ : syracuseStep 791279 = 1186919) B1186919
theorem B2364299 : Blo 350755 2364299 := bstep (se 1 (by rfl) ⟨1773224, by rfl⟩ : syracuseStep 2364299 = 3546449) B3546449
theorem B7640081 : Blo 350755 7640081 := bstep (se 2 (by rfl) ⟨2865030, by rfl⟩ : syracuseStep 7640081 = 5730061) B5730061
theorem B595451 : Blo 350755 595451 := bstep (se 1 (by rfl) ⟨446588, by rfl⟩ : syracuseStep 595451 = 893177) B893177
theorem B792233 : Blo 350755 792233 := bstep (se 2 (by rfl) ⟨297087, by rfl⟩ : syracuseStep 792233 = 594175) B594175
theorem B792935 : Blo 350755 792935 := bstep (se 1 (by rfl) ⟨594701, by rfl⟩ : syracuseStep 792935 = 1189403) B1189403
theorem B563593 : Blo 350755 563593 := bstep (se 2 (by rfl) ⟨211347, by rfl⟩ : syracuseStep 563593 = 422695) B422695
theorem B1612169 : Blo 350755 1612169 := bstep (se 2 (by rfl) ⟨604563, by rfl⟩ : syracuseStep 1612169 = 1209127) B1209127
theorem B1186217 : Blo 350755 1186217 := bstep (se 2 (by rfl) ⟨444831, by rfl⟩ : syracuseStep 1186217 = 889663) B889663
theorem B530999 : Blo 350755 530999 := bstep (se 1 (by rfl) ⟨398249, by rfl⟩ : syracuseStep 530999 = 796499) B796499
theorem B2267851 : Blo 350755 2267851 := bstep (se 1 (by rfl) ⟨1700888, by rfl⟩ : syracuseStep 2267851 = 3401777) B3401777
theorem B531239 : Blo 350755 531239 := bstep (se 1 (by rfl) ⟨398429, by rfl⟩ : syracuseStep 531239 = 796859) B796859
theorem B2169737 : Blo 350755 2169737 := bstep (se 2 (by rfl) ⟨813651, by rfl⟩ : syracuseStep 2169737 = 1627303) B1627303
theorem B793511 : Blo 350755 793511 := bstep (se 1 (by rfl) ⟨595133, by rfl⟩ : syracuseStep 793511 = 1190267) B1190267
theorem B793583 : Blo 350755 793583 := bstep (se 1 (by rfl) ⟨595187, by rfl⟩ : syracuseStep 793583 = 1190375) B1190375
theorem B597179 : Blo 350755 597179 := bstep (se 1 (by rfl) ⟨447884, by rfl⟩ : syracuseStep 597179 = 895769) B895769
theorem B793835 : Blo 350755 793835 := bstep (se 1 (by rfl) ⟨595376, by rfl⟩ : syracuseStep 793835 = 1190753) B1190753
theorem B531707 : Blo 350755 531707 := bstep (se 1 (by rfl) ⟨398780, by rfl⟩ : syracuseStep 531707 = 797561) B797561
theorem B531833 : Blo 350755 531833 := bstep (se 2 (by rfl) ⟨199437, by rfl⟩ : syracuseStep 531833 = 398875) B398875
theorem B1187297 : Blo 350755 1187297 := bstep (se 2 (by rfl) ⟨445236, by rfl⟩ : syracuseStep 1187297 = 890473) B890473
theorem B597503 : Blo 350755 597503 := bstep (se 1 (by rfl) ⟨448127, by rfl⟩ : syracuseStep 597503 = 896255) B896255
theorem B794249 : Blo 350755 794249 := bstep (se 2 (by rfl) ⟨297843, by rfl⟩ : syracuseStep 794249 = 595687) B595687
theorem B8134319 : Blo 350755 8134319 := bstep (se 1 (by rfl) ⟨6100739, by rfl⟩ : syracuseStep 8134319 = 12201479) B12201479
theorem B1187567 : Blo 350755 1187567 := bstep (se 1 (by rfl) ⟨890675, by rfl⟩ : syracuseStep 1187567 = 1781351) B1781351
theorem B499775 : Blo 350755 499775 := bstep (se 1 (by rfl) ⟨374831, by rfl⟩ : syracuseStep 499775 = 749663) B749663
theorem B958567 : Blo 350755 958567 := bstep (se 1 (by rfl) ⟨718925, by rfl⟩ : syracuseStep 958567 = 1437851) B1437851
theorem B1450487 : Blo 350755 1450487 := bstep (se 1 (by rfl) ⟨1087865, by rfl⟩ : syracuseStep 1450487 = 2175731) B2175731
theorem B3023527 : Blo 350755 3023527 := bstep (se 1 (by rfl) ⟨2267645, by rfl⟩ : syracuseStep 3023527 = 4535291) B4535291
theorem B795617 : Blo 350755 795617 := bstep (se 2 (by rfl) ⟨298356, by rfl⟩ : syracuseStep 795617 = 596713) B596713
theorem B1189025 : Blo 350755 1189025 := bstep (se 2 (by rfl) ⟨445884, by rfl⟩ : syracuseStep 1189025 = 891769) B891769
theorem B2073853 : Blo 350755 2073853 := bstep (se 3 (by rfl) ⟨388847, by rfl⟩ : syracuseStep 2073853 = 777695) B777695
theorem B1779407 : Blo 350755 1779407 := bstep (se 1 (by rfl) ⟨1334555, by rfl⟩ : syracuseStep 1779407 = 2669111) B2669111
theorem B797345 : Blo 350755 797345 := bstep (se 2 (by rfl) ⟨299004, by rfl⟩ : syracuseStep 797345 = 598009) B598009
theorem B2665223 : Blo 350755 2665223 := bstep (se 1 (by rfl) ⟨1998917, by rfl⟩ : syracuseStep 2665223 = 3997835) B3997835
theorem B666785 : Blo 350755 666785 := bstep (se 2 (by rfl) ⟨250044, by rfl⟩ : syracuseStep 666785 = 500089) B500089
theorem B1191401 : Blo 350755 1191401 := bstep (se 2 (by rfl) ⟨446775, by rfl⟩ : syracuseStep 1191401 = 893551) B893551
theorem B9809515 : Blo 350755 9809515 := bstep (se 1 (by rfl) ⟨7357136, by rfl⟩ : syracuseStep 9809515 = 14714273) B14714273
theorem B3124939 : Blo 350755 3124939 := bstep (se 1 (by rfl) ⟨2343704, by rfl⟩ : syracuseStep 3124939 = 4687409) B4687409
theorem B505055 : Blo 350755 505055 := bstep (se 1 (by rfl) ⟨378791, by rfl⟩ : syracuseStep 505055 = 757583) B757583
theorem B2143739 : Blo 350755 2143739 := bstep (se 1 (by rfl) ⟨1607804, by rfl⟩ : syracuseStep 2143739 = 3215609) B3215609
theorem B669359 : Blo 350755 669359 := bstep (se 1 (by rfl) ⟨502019, by rfl⟩ : syracuseStep 669359 = 1004039) B1004039
theorem B2865061 : Blo 350755 2865061 := bstep (se 4 (by rfl) ⟨268599, by rfl⟩ : syracuseStep 2865061 = 537199) B537199
theorem B44546183 : Blo 350755 44546183 := bstep (se 1 (by rfl) ⟨33409637, by rfl⟩ : syracuseStep 44546183 = 66819275) B66819275
theorem B2013407 : Blo 350755 2013407 := bstep (se 1 (by rfl) ⟨1510055, by rfl⟩ : syracuseStep 2013407 = 3020111) B3020111
theorem B9746729 : Blo 350755 9746729 := bstep (se 2 (by rfl) ⟨3655023, by rfl⟩ : syracuseStep 9746729 = 7310047) B7310047
theorem B2046791 : Blo 350755 2046791 := bstep (se 1 (by rfl) ⟨1535093, by rfl⟩ : syracuseStep 2046791 = 3070187) B3070187
theorem B2014091 : Blo 350755 2014091 := bstep (se 1 (by rfl) ⟨1510568, by rfl⟩ : syracuseStep 2014091 = 3021137) B3021137
theorem B10861523 : Blo 350755 10861523 := bstep (se 1 (by rfl) ⟨8146142, by rfl⟩ : syracuseStep 10861523 = 16292285) B16292285
theorem B9649439 : Blo 350755 9649439 := bstep (se 1 (by rfl) ⟨7237079, by rfl⟩ : syracuseStep 9649439 = 14474159) B14474159
theorem B802223 : Blo 350755 802223 := bstep (se 1 (by rfl) ⟨601667, by rfl⟩ : syracuseStep 802223 = 1203335) B1203335
theorem B2998241 : Blo 350755 2998241 := bstep (se 2 (by rfl) ⟨1124340, by rfl⟩ : syracuseStep 2998241 = 2248681) B2248681
theorem B1786535 : Blo 350755 1786535 := bstep (se 1 (by rfl) ⟨1339901, by rfl⟩ : syracuseStep 1786535 = 2679803) B2679803
theorem B3884219 : Blo 350755 3884219 := bstep (se 1 (by rfl) ⟨2913164, by rfl⟩ : syracuseStep 3884219 = 5826329) B5826329
theorem B1197287 : Blo 350755 1197287 := bstep (se 1 (by rfl) ⟨897965, by rfl⟩ : syracuseStep 1197287 = 1795931) B1795931
theorem B673019 : Blo 350755 673019 := bstep (se 1 (by rfl) ⟨504764, by rfl⟩ : syracuseStep 673019 = 1009529) B1009529
theorem B4310441 : Blo 350755 4310441 := bstep (se 2 (by rfl) ⟨1616415, by rfl⟩ : syracuseStep 4310441 = 3232831) B3232831
theorem B5097077 : Blo 350755 5097077 := bstep (se 5 (by rfl) ⟨238925, by rfl⟩ : syracuseStep 5097077 = 477851) B477851
theorem B477247 : Blo 350755 477247 := bstep (se 1 (by rfl) ⟨357935, by rfl⟩ : syracuseStep 477247 = 715871) B715871
theorem B608879 : Blo 350755 608879 := bstep (se 1 (by rfl) ⟨456659, by rfl⟩ : syracuseStep 608879 = 913319) B913319
theorem B1133311 : Blo 350755 1133311 := bstep (se 1 (by rfl) ⟨849983, by rfl⟩ : syracuseStep 1133311 = 1699967) B1699967
theorem B1428931 : Blo 350755 1428931 := bstep (se 1 (by rfl) ⟨1071698, by rfl⟩ : syracuseStep 1428931 = 2143397) B2143397
theorem B2248631 : Blo 350755 2248631 := bstep (se 1 (by rfl) ⟨1686473, by rfl⟩ : syracuseStep 2248631 = 3372947) B3372947
theorem B2707721 : Blo 350755 2707721 := bstep (se 2 (by rfl) ⟨1015395, by rfl⟩ : syracuseStep 2707721 = 2030791) B2030791
theorem B1037033 : Blo 350755 1037033 := bstep (se 2 (by rfl) ⟨388887, by rfl⟩ : syracuseStep 1037033 = 777775) B777775
theorem B10867445 : Blo 350755 10867445 := bstep (se 5 (by rfl) ⟨509411, by rfl⟩ : syracuseStep 10867445 = 1018823) B1018823
theorem B1005281 : Blo 350755 1005281 := bstep (se 2 (by rfl) ⟨376980, by rfl⟩ : syracuseStep 1005281 = 753961) B753961
theorem B2709469 : Blo 350755 2709469 := bstep (se 3 (by rfl) ⟨508025, by rfl⟩ : syracuseStep 2709469 = 1016051) B1016051
theorem B2251243 : Blo 350755 2251243 := bstep (se 1 (by rfl) ⟨1688432, by rfl⟩ : syracuseStep 2251243 = 3376865) B3376865
theorem B350875 : Blo 350755 350875 := bstep (se 1 (by rfl) ⟨263156, by rfl⟩ : syracuseStep 350875 = 526313) B526313
theorem B350887 : Blo 350755 350887 := bstep (se 1 (by rfl) ⟨263165, by rfl⟩ : syracuseStep 350887 = 526331) B526331
theorem B350971 : Blo 350755 350971 := bstep (se 1 (by rfl) ⟨263228, by rfl⟩ : syracuseStep 350971 = 526457) B526457
theorem B4840481 : Blo 350755 4840481 := bstep (se 2 (by rfl) ⟨1815180, by rfl⟩ : syracuseStep 4840481 = 3630361) B3630361
theorem B351647 : Blo 350755 351647 := bstep (se 1 (by rfl) ⟨263735, by rfl⟩ : syracuseStep 351647 = 527471) B527471
theorem B351775 : Blo 350755 351775 := bstep (se 1 (by rfl) ⟨263831, by rfl⟩ : syracuseStep 351775 = 527663) B527663
theorem B351899 : Blo 350755 351899 := bstep (se 1 (by rfl) ⟨263924, by rfl⟩ : syracuseStep 351899 = 527849) B527849
theorem B351935 : Blo 350755 351935 := bstep (se 1 (by rfl) ⟨263951, by rfl⟩ : syracuseStep 351935 = 527903) B527903
theorem B351995 : Blo 350755 351995 := bstep (se 1 (by rfl) ⟨263996, by rfl⟩ : syracuseStep 351995 = 527993) B527993
theorem B2875769 : Blo 350755 2875769 := bstep (se 2 (by rfl) ⟨1078413, by rfl⟩ : syracuseStep 2875769 = 2156827) B2156827
theorem B1009597 : Blo 350755 1009597 := bstep (se 3 (by rfl) ⟨189299, by rfl⟩ : syracuseStep 1009597 = 378599) B378599
theorem B2680775 : Blo 350755 2680775 := bstep (se 1 (by rfl) ⟨2010581, by rfl⟩ : syracuseStep 2680775 = 4021163) B4021163
theorem B354559 : Blo 350755 354559 := bstep (se 1 (by rfl) ⟨265919, by rfl⟩ : syracuseStep 354559 = 531839) B531839
theorem B2287997 : Blo 350755 2287997 := bstep (se 3 (by rfl) ⟨428999, by rfl⟩ : syracuseStep 2287997 = 857999) B857999
theorem B1534747 : Blo 350755 1534747 := bstep (se 1 (by rfl) ⟨1151060, by rfl⟩ : syracuseStep 1534747 = 2302121) B2302121
theorem B2682233 : Blo 350755 2682233 := bstep (se 2 (by rfl) ⟨1005837, by rfl⟩ : syracuseStep 2682233 = 2011675) B2011675
theorem B10284731 : Blo 350755 10284731 := bstep (se 1 (by rfl) ⟨7713548, by rfl⟩ : syracuseStep 10284731 = 15427097) B15427097
theorem B749287 : Blo 350755 749287 := bstep (se 1 (by rfl) ⟨561965, by rfl⟩ : syracuseStep 749287 = 1123931) B1123931
theorem B1339325 : Blo 350755 1339325 := bstep (se 3 (by rfl) ⟨251123, by rfl⟩ : syracuseStep 1339325 = 502247) B502247
theorem B1012961 : Blo 350755 1012961 := bstep (se 2 (by rfl) ⟨379860, by rfl⟩ : syracuseStep 1012961 = 759721) B759721
theorem B2258603 : Blo 350755 2258603 := bstep (se 1 (by rfl) ⟨1693952, by rfl⟩ : syracuseStep 2258603 = 3387905) B3387905
theorem B2684663 : Blo 350755 2684663 := bstep (se 1 (by rfl) ⟨2013497, by rfl⟩ : syracuseStep 2684663 = 4026995) B4026995
theorem B1505135 : Blo 350755 1505135 := bstep (se 1 (by rfl) ⟨1128851, by rfl⟩ : syracuseStep 1505135 = 2257703) B2257703
theorem B3045671 : Blo 350755 3045671 := bstep (se 1 (by rfl) ⟨2284253, by rfl⟩ : syracuseStep 3045671 = 4568507) B4568507
theorem B1341967 : Blo 350755 1341967 := bstep (se 1 (by rfl) ⟨1006475, by rfl⟩ : syracuseStep 1341967 = 2012951) B2012951
theorem B1703119 : Blo 350755 1703119 := bstep (se 1 (by rfl) ⟨1277339, by rfl⟩ : syracuseStep 1703119 = 2554679) B2554679
theorem B2686607 : Blo 350755 2686607 := bstep (se 1 (by rfl) ⟨2014955, by rfl⟩ : syracuseStep 2686607 = 4029911) B4029911
theorem B1278089 : Blo 350755 1278089 := bstep (se 2 (by rfl) ⟨479283, by rfl⟩ : syracuseStep 1278089 = 958567) B958567
theorem B2589479 : Blo 350755 2589479 := bstep (se 1 (by rfl) ⟨1942109, by rfl⟩ : syracuseStep 2589479 = 3884219) B3884219
theorem B4031369 : Blo 350755 4031369 := bstep (se 2 (by rfl) ⟨1511763, by rfl⟩ : syracuseStep 4031369 = 3023527) B3023527
theorem B3016763 : Blo 350755 3016763 := bstep (se 1 (by rfl) ⟨2262572, by rfl⟩ : syracuseStep 3016763 = 4525145) B4525145
theorem B526799 : Blo 350755 526799 := bstep (se 1 (by rfl) ⟨395099, by rfl⟩ : syracuseStep 526799 = 790199) B790199
theorem B1346129 : Blo 350755 1346129 := bstep (se 2 (by rfl) ⟨504798, by rfl⟩ : syracuseStep 1346129 = 1009597) B1009597
theorem B527099 : Blo 350755 527099 := bstep (se 1 (by rfl) ⟨395324, by rfl⟩ : syracuseStep 527099 = 790649) B790649
theorem B1805147 : Blo 350755 1805147 := bstep (se 1 (by rfl) ⟨1353860, by rfl⟩ : syracuseStep 1805147 = 2707721) B2707721
theorem B691355 : Blo 350755 691355 := bstep (se 1 (by rfl) ⟨518516, by rfl⟩ : syracuseStep 691355 = 1037033) B1037033
theorem B527519 : Blo 350755 527519 := bstep (se 1 (by rfl) ⟨395639, by rfl⟩ : syracuseStep 527519 = 791279) B791279
theorem B7244963 : Blo 350755 7244963 := bstep (se 1 (by rfl) ⟨5433722, by rfl⟩ : syracuseStep 7244963 = 10867445) B10867445
theorem B1346813 : Blo 350755 1346813 := bstep (se 3 (by rfl) ⟨252527, by rfl⟩ : syracuseStep 1346813 = 505055) B505055
theorem B1576199 : Blo 350755 1576199 := bstep (se 1 (by rfl) ⟨1182149, by rfl⟩ : syracuseStep 1576199 = 2364299) B2364299
theorem B396967 : Blo 350755 396967 := bstep (se 1 (by rfl) ⟨297725, by rfl⟩ : syracuseStep 396967 = 595451) B595451
theorem B1511081 : Blo 350755 1511081 := bstep (se 2 (by rfl) ⟨566655, by rfl⟩ : syracuseStep 1511081 = 1133311) B1133311
theorem B528155 : Blo 350755 528155 := bstep (se 1 (by rfl) ⟨396116, by rfl⟩ : syracuseStep 528155 = 792233) B792233
theorem B528425 : Blo 350755 528425 := bstep (se 2 (by rfl) ⟨198159, by rfl⟩ : syracuseStep 528425 = 396319) B396319
theorem B528623 : Blo 350755 528623 := bstep (se 1 (by rfl) ⟨396467, by rfl⟩ : syracuseStep 528623 = 792935) B792935
theorem B790811 : Blo 350755 790811 := bstep (se 1 (by rfl) ⟨593108, by rfl⟩ : syracuseStep 790811 = 1186217) B1186217
theorem B1446491 : Blo 350755 1446491 := bstep (se 1 (by rfl) ⟨1084868, by rfl⟩ : syracuseStep 1446491 = 2169737) B2169737
theorem B529007 : Blo 350755 529007 := bstep (se 1 (by rfl) ⟨396755, by rfl⟩ : syracuseStep 529007 = 793511) B793511
theorem B529055 : Blo 350755 529055 := bstep (se 1 (by rfl) ⟨396791, by rfl⟩ : syracuseStep 529055 = 793583) B793583
theorem B398119 : Blo 350755 398119 := bstep (se 1 (by rfl) ⟨298589, by rfl⟩ : syracuseStep 398119 = 597179) B597179
theorem B529223 : Blo 350755 529223 := bstep (se 1 (by rfl) ⟨396917, by rfl⟩ : syracuseStep 529223 = 793835) B793835
theorem B4166585 : Blo 350755 4166585 := bstep (se 2 (by rfl) ⟨1562469, by rfl⟩ : syracuseStep 4166585 = 3124939) B3124939
theorem B791531 : Blo 350755 791531 := bstep (se 1 (by rfl) ⟨593648, by rfl⟩ : syracuseStep 791531 = 1187297) B1187297
theorem B398335 : Blo 350755 398335 := bstep (se 1 (by rfl) ⟨298751, by rfl⟩ : syracuseStep 398335 = 597503) B597503
theorem B529499 : Blo 350755 529499 := bstep (se 1 (by rfl) ⟨397124, by rfl⟩ : syracuseStep 529499 = 794249) B794249
theorem B791711 : Blo 350755 791711 := bstep (se 1 (by rfl) ⟨593783, by rfl⟩ : syracuseStep 791711 = 1187567) B1187567
theorem B530411 : Blo 350755 530411 := bstep (se 1 (by rfl) ⟨397808, by rfl⟩ : syracuseStep 530411 = 795617) B795617
theorem B792683 : Blo 350755 792683 := bstep (se 1 (by rfl) ⟨594512, by rfl⟩ : syracuseStep 792683 = 1189025) B1189025
theorem B1186271 : Blo 350755 1186271 := bstep (se 1 (by rfl) ⟨889703, by rfl⟩ : syracuseStep 1186271 = 1779407) B1779407
theorem B531563 : Blo 350755 531563 := bstep (se 1 (by rfl) ⟨398672, by rfl⟩ : syracuseStep 531563 = 797345) B797345
theorem B1776815 : Blo 350755 1776815 := bstep (se 1 (by rfl) ⟨1332611, by rfl⟩ : syracuseStep 1776815 = 2665223) B2665223
theorem B794267 : Blo 350755 794267 := bstep (se 1 (by rfl) ⟨595700, by rfl⟩ : syracuseStep 794267 = 1191401) B1191401
theorem B6856487 : Blo 350755 6856487 := bstep (se 1 (by rfl) ⟨5142365, by rfl⟩ : syracuseStep 6856487 = 10284731) B10284731
theorem B892883 : Blo 350755 892883 := bstep (se 1 (by rfl) ⟨669662, by rfl⟩ : syracuseStep 892883 = 1339325) B1339325
theorem B3023801 : Blo 350755 3023801 := bstep (se 2 (by rfl) ⟨1133925, by rfl⟩ : syracuseStep 3023801 = 2267851) B2267851
theorem B43394453 : Blo 350755 43394453 := bstep (se 6 (by rfl) ⟨1017057, by rfl⟩ : syracuseStep 43394453 = 2034115) B2034115
theorem B29697455 : Blo 350755 29697455 := bstep (se 1 (by rfl) ⟨22273091, by rfl⟩ : syracuseStep 29697455 = 44546183) B44546183
theorem B6497819 : Blo 350755 6497819 := bstep (se 1 (by rfl) ⟨4873364, by rfl⟩ : syracuseStep 6497819 = 9746729) B9746729
theorem B2270825 : Blo 350755 2270825 := bstep (se 2 (by rfl) ⟨851559, by rfl⟩ : syracuseStep 2270825 = 1703119) B1703119
theorem B6432959 : Blo 350755 6432959 := bstep (se 1 (by rfl) ⟨4824719, by rfl⟩ : syracuseStep 6432959 = 9649439) B9649439
theorem B534815 : Blo 350755 534815 := bstep (se 1 (by rfl) ⟨401111, by rfl⟩ : syracuseStep 534815 = 802223) B802223
theorem B1191023 : Blo 350755 1191023 := bstep (se 1 (by rfl) ⟨893267, by rfl⟩ : syracuseStep 1191023 = 1786535) B1786535
theorem B798191 : Blo 350755 798191 := bstep (se 1 (by rfl) ⟨598643, by rfl⟩ : syracuseStep 798191 = 1197287) B1197287
theorem B2765137 : Blo 350755 2765137 := bstep (se 2 (by rfl) ⟨1036926, by rfl⟩ : syracuseStep 2765137 = 2073853) B2073853
theorem B405919 : Blo 350755 405919 := bstep (se 1 (by rfl) ⟨304439, by rfl⟩ : syracuseStep 405919 = 608879) B608879
theorem B897743 : Blo 350755 897743 := bstep (se 1 (by rfl) ⟨673307, by rfl⟩ : syracuseStep 897743 = 1346615) B1346615
theorem B636329 : Blo 350755 636329 := bstep (se 2 (by rfl) ⟨238623, by rfl⟩ : syracuseStep 636329 = 477247) B477247
theorem B5093387 : Blo 350755 5093387 := bstep (se 1 (by rfl) ⟨3820040, by rfl⟩ : syracuseStep 5093387 = 7640081) B7640081
theorem B2046329 : Blo 350755 2046329 := bstep (se 2 (by rfl) ⟨767373, by rfl⟩ : syracuseStep 2046329 = 1534747) B1534747
theorem B670187 : Blo 350755 670187 := bstep (se 1 (by rfl) ⟨502640, by rfl⟩ : syracuseStep 670187 = 1005281) B1005281
theorem B3226987 : Blo 350755 3226987 := bstep (se 1 (by rfl) ⟨2420240, by rfl⟩ : syracuseStep 3226987 = 4840481) B4840481
theorem B999049 : Blo 350755 999049 := bstep (se 2 (by rfl) ⟨374643, by rfl⟩ : syracuseStep 999049 = 749287) B749287
theorem B5422879 : Blo 350755 5422879 := bstep (se 1 (by rfl) ⟨4067159, by rfl⟩ : syracuseStep 5422879 = 8134319) B8134319
theorem B1917179 : Blo 350755 1917179 := bstep (se 1 (by rfl) ⟨1437884, by rfl⟩ : syracuseStep 1917179 = 2875769) B2875769
theorem B966991 : Blo 350755 966991 := bstep (se 1 (by rfl) ⟨725243, by rfl⟩ : syracuseStep 966991 = 1450487) B1450487
theorem B1787183 : Blo 350755 1787183 := bstep (se 1 (by rfl) ⟨1340387, by rfl⟩ : syracuseStep 1787183 = 2680775) B2680775
theorem B1525331 : Blo 350755 1525331 := bstep (se 1 (by rfl) ⟨1143998, by rfl⟩ : syracuseStep 1525331 = 2287997) B2287997
theorem B444523 : Blo 350755 444523 := bstep (se 1 (by rfl) ⟨333392, by rfl⟩ : syracuseStep 444523 = 666785) B666785
theorem B1788155 : Blo 350755 1788155 := bstep (se 1 (by rfl) ⟨1341116, by rfl⟩ : syracuseStep 1788155 = 2682233) B2682233
theorem B7620965 : Blo 350755 7620965 := bstep (se 4 (by rfl) ⟨714465, by rfl⟩ : syracuseStep 7620965 = 1428931) B1428931
theorem B3820081 : Blo 350755 3820081 := bstep (se 2 (by rfl) ⟨1432530, by rfl⟩ : syracuseStep 3820081 = 2865061) B2865061
theorem B52317413 : Blo 350755 52317413 := bstep (se 4 (by rfl) ⟨4904757, by rfl⟩ : syracuseStep 52317413 = 9809515) B9809515
theorem B3001657 : Blo 350755 3001657 := bstep (se 2 (by rfl) ⟨1125621, by rfl⟩ : syracuseStep 3001657 = 2251243) B2251243
theorem B1789289 : Blo 350755 1789289 := bstep (se 2 (by rfl) ⟨670983, by rfl⟩ : syracuseStep 1789289 = 1341967) B1341967
theorem B675307 : Blo 350755 675307 := bstep (se 1 (by rfl) ⟨506480, by rfl⟩ : syracuseStep 675307 = 1012961) B1012961
theorem B1429159 : Blo 350755 1429159 := bstep (se 1 (by rfl) ⟨1071869, by rfl⟩ : syracuseStep 1429159 = 2143739) B2143739
theorem B446239 : Blo 350755 446239 := bstep (se 1 (by rfl) ⟨334679, by rfl⟩ : syracuseStep 446239 = 669359) B669359
theorem B1789775 : Blo 350755 1789775 := bstep (se 1 (by rfl) ⟨1342331, by rfl⟩ : syracuseStep 1789775 = 2684663) B2684663
theorem B1003423 : Blo 350755 1003423 := bstep (se 1 (by rfl) ⟨752567, by rfl⟩ : syracuseStep 1003423 = 1505135) B1505135
theorem B1364527 : Blo 350755 1364527 := bstep (se 1 (by rfl) ⟨1023395, by rfl⟩ : syracuseStep 1364527 = 2046791) B2046791
theorem B1791071 : Blo 350755 1791071 := bstep (se 1 (by rfl) ⟨1343303, by rfl⟩ : syracuseStep 1791071 = 2686607) B2686607
theorem B1332733 : Blo 350755 1332733 := bstep (se 3 (by rfl) ⟨249887, by rfl⟩ : syracuseStep 1332733 = 499775) B499775
theorem B448679 : Blo 350755 448679 := bstep (se 1 (by rfl) ⟨336509, by rfl⟩ : syracuseStep 448679 = 673019) B673019
theorem B2873627 : Blo 350755 2873627 := bstep (se 1 (by rfl) ⟨2155220, by rfl⟩ : syracuseStep 2873627 = 4310441) B4310441
theorem B130734485 : Blo 350755 130734485 := bstep (se 6 (by rfl) ⟨3064089, by rfl⟩ : syracuseStep 130734485 = 6128179) B6128179
theorem B3398051 : Blo 350755 3398051 := bstep (se 1 (by rfl) ⟨2548538, by rfl⟩ : syracuseStep 3398051 = 5097077) B5097077
theorem B350767 : Blo 350755 350767 := bstep (se 1 (by rfl) ⟨263075, by rfl⟩ : syracuseStep 350767 = 526151) B526151
theorem B351003 : Blo 350755 351003 := bstep (se 1 (by rfl) ⟨263252, by rfl⟩ : syracuseStep 351003 = 526505) B526505
theorem B351259 : Blo 350755 351259 := bstep (se 1 (by rfl) ⟨263444, by rfl⟩ : syracuseStep 351259 = 526889) B526889
theorem B351535 : Blo 350755 351535 := bstep (se 1 (by rfl) ⟨263651, by rfl⟩ : syracuseStep 351535 = 527303) B527303
theorem B351591 : Blo 350755 351591 := bstep (se 1 (by rfl) ⟨263693, by rfl⟩ : syracuseStep 351591 = 527387) B527387
theorem B352091 : Blo 350755 352091 := bstep (se 1 (by rfl) ⟨264068, by rfl⟩ : syracuseStep 352091 = 528137) B528137
theorem B352127 : Blo 350755 352127 := bstep (se 1 (by rfl) ⟨264095, by rfl⟩ : syracuseStep 352127 = 528191) B528191
theorem B54747035 : Blo 350755 54747035 := bstep (se 1 (by rfl) ⟨41060276, by rfl⟩ : syracuseStep 54747035 = 82120553) B82120553
theorem B352159 : Blo 350755 352159 := bstep (se 1 (by rfl) ⟨264119, by rfl⟩ : syracuseStep 352159 = 528239) B528239
theorem B352191 : Blo 350755 352191 := bstep (se 1 (by rfl) ⟨264143, by rfl⟩ : syracuseStep 352191 = 528287) B528287
theorem B1499087 : Blo 350755 1499087 := bstep (se 1 (by rfl) ⟨1124315, by rfl⟩ : syracuseStep 1499087 = 2248631) B2248631
theorem B13459655 : Blo 350755 13459655 := bstep (se 1 (by rfl) ⟨10094741, by rfl⟩ : syracuseStep 13459655 = 20189483) B20189483
theorem B352539 : Blo 350755 352539 := bstep (se 1 (by rfl) ⟨264404, by rfl⟩ : syracuseStep 352539 = 528809) B528809
theorem B352667 : Blo 350755 352667 := bstep (se 1 (by rfl) ⟨264500, by rfl⟩ : syracuseStep 352667 = 529001) B529001
theorem B352751 : Blo 350755 352751 := bstep (se 1 (by rfl) ⟨264563, by rfl⟩ : syracuseStep 352751 = 529127) B529127
theorem B1074779 : Blo 350755 1074779 := bstep (se 1 (by rfl) ⟨806084, by rfl⟩ : syracuseStep 1074779 = 1612169) B1612169
theorem B353999 : Blo 350755 353999 := bstep (se 1 (by rfl) ⟨265499, by rfl⟩ : syracuseStep 353999 = 530999) B530999
theorem B354159 : Blo 350755 354159 := bstep (se 1 (by rfl) ⟨265619, by rfl⟩ : syracuseStep 354159 = 531239) B531239
theorem B354471 : Blo 350755 354471 := bstep (se 1 (by rfl) ⟨265853, by rfl⟩ : syracuseStep 354471 = 531707) B531707
theorem B354555 : Blo 350755 354555 := bstep (se 1 (by rfl) ⟨265916, by rfl⟩ : syracuseStep 354555 = 531833) B531833
theorem B751457 : Blo 350755 751457 := bstep (se 2 (by rfl) ⟨281796, by rfl⟩ : syracuseStep 751457 = 563593) B563593
theorem B1505735 : Blo 350755 1505735 := bstep (se 1 (by rfl) ⟨1129301, by rfl⟩ : syracuseStep 1505735 = 2258603) B2258603
theorem B1342271 : Blo 350755 1342271 := bstep (se 1 (by rfl) ⟨1006703, by rfl⟩ : syracuseStep 1342271 = 2013407) B2013407
theorem B2030447 : Blo 350755 2030447 := bstep (se 1 (by rfl) ⟨1522835, by rfl⟩ : syracuseStep 2030447 = 3045671) B3045671
theorem B1342727 : Blo 350755 1342727 := bstep (se 1 (by rfl) ⟨1007045, by rfl⟩ : syracuseStep 1342727 = 2014091) B2014091
theorem B7241015 : Blo 350755 7241015 := bstep (se 1 (by rfl) ⟨5430761, by rfl⟩ : syracuseStep 7241015 = 10861523) B10861523
theorem B14450501 : Blo 350755 14450501 := bstep (se 4 (by rfl) ⟨1354734, by rfl⟩ : syracuseStep 14450501 = 2709469) B2709469
theorem B1998827 : Blo 350755 1998827 := bstep (se 1 (by rfl) ⟨1499120, by rfl⟩ : syracuseStep 1998827 = 2998241) B2998241
theorem B852059 : Blo 350755 852059 := bstep (se 1 (by rfl) ⟨639044, by rfl⟩ : syracuseStep 852059 = 1278089) B1278089
theorem B1278119 : Blo 350755 1278119 := bstep (se 1 (by rfl) ⟨958589, by rfl⟩ : syracuseStep 1278119 = 1917179) B1917179
theorem B2687579 : Blo 350755 2687579 := bstep (se 1 (by rfl) ⟨2015684, by rfl⟩ : syracuseStep 2687579 = 4031369) B4031369
theorem B1016887 : Blo 350755 1016887 := bstep (se 1 (by rfl) ⟨762665, by rfl⟩ : syracuseStep 1016887 = 1525331) B1525331
theorem B5080643 : Blo 350755 5080643 := bstep (se 1 (by rfl) ⟨3810482, by rfl⟩ : syracuseStep 5080643 = 7620965) B7620965
theorem B460903 : Blo 350755 460903 := bstep (se 1 (by rfl) ⟨345677, by rfl⟩ : syracuseStep 460903 = 691355) B691355
theorem B592697 : Blo 350755 592697 := bstep (se 2 (by rfl) ⟨222261, by rfl⟩ : syracuseStep 592697 = 444523) B444523
theorem B527207 : Blo 350755 527207 := bstep (se 1 (by rfl) ⟨395405, by rfl⟩ : syracuseStep 527207 = 790811) B790811
theorem B527687 : Blo 350755 527687 := bstep (se 1 (by rfl) ⟨395765, by rfl⟩ : syracuseStep 527687 = 791531) B791531
theorem B527807 : Blo 350755 527807 := bstep (se 1 (by rfl) ⟨395855, by rfl⟩ : syracuseStep 527807 = 791711) B791711
theorem B528455 : Blo 350755 528455 := bstep (se 1 (by rfl) ⟨396341, by rfl⟩ : syracuseStep 528455 = 792683) B792683
theorem B2265367 : Blo 350755 2265367 := bstep (se 1 (by rfl) ⟨1699025, by rfl⟩ : syracuseStep 2265367 = 3398051) B3398051
theorem B790847 : Blo 350755 790847 := bstep (se 1 (by rfl) ⟨593135, by rfl⟩ : syracuseStep 790847 = 1186271) B1186271
theorem B4002209 : Blo 350755 4002209 := bstep (se 2 (by rfl) ⟨1500828, by rfl⟩ : syracuseStep 4002209 = 3001657) B3001657
theorem B1184543 : Blo 350755 1184543 := bstep (se 1 (by rfl) ⟨888407, by rfl⟩ : syracuseStep 1184543 = 1776815) B1776815
theorem B1905545 : Blo 350755 1905545 := bstep (se 2 (by rfl) ⟨714579, by rfl⟩ : syracuseStep 1905545 = 1429159) B1429159
theorem B529289 : Blo 350755 529289 := bstep (se 2 (by rfl) ⟨198483, by rfl⟩ : syracuseStep 529289 = 396967) B396967
theorem B2003885 : Blo 350755 2003885 := bstep (se 3 (by rfl) ⟨375728, by rfl⟩ : syracuseStep 2003885 = 751457) B751457
theorem B594985 : Blo 350755 594985 := bstep (se 2 (by rfl) ⟨223119, by rfl⟩ : syracuseStep 594985 = 446239) B446239
theorem B529511 : Blo 350755 529511 := bstep (se 1 (by rfl) ⟨397133, by rfl⟩ : syracuseStep 529511 = 794267) B794267
theorem B595255 : Blo 350755 595255 := bstep (se 1 (by rfl) ⟨446441, by rfl⟩ : syracuseStep 595255 = 892883) B892883
theorem B4331879 : Blo 350755 4331879 := bstep (se 1 (by rfl) ⟨3248909, by rfl⟩ : syracuseStep 4331879 = 6497819) B6497819
theorem B530825 : Blo 350755 530825 := bstep (se 2 (by rfl) ⟨199059, by rfl⟩ : syracuseStep 530825 = 398119) B398119
theorem B1513883 : Blo 350755 1513883 := bstep (se 1 (by rfl) ⟨1135412, by rfl⟩ : syracuseStep 1513883 = 2270825) B2270825
theorem B531113 : Blo 350755 531113 := bstep (se 2 (by rfl) ⟨199167, by rfl⟩ : syracuseStep 531113 = 398335) B398335
theorem B1776977 : Blo 350755 1776977 := bstep (se 2 (by rfl) ⟨666366, by rfl⟩ : syracuseStep 1776977 = 1332733) B1332733
theorem B794015 : Blo 350755 794015 := bstep (se 1 (by rfl) ⟨595511, by rfl⟩ : syracuseStep 794015 = 1191023) B1191023
theorem B532127 : Blo 350755 532127 := bstep (se 1 (by rfl) ⟨399095, by rfl⟩ : syracuseStep 532127 = 798191) B798191
theorem B598495 : Blo 350755 598495 := bstep (se 1 (by rfl) ⟨448871, by rfl⟩ : syracuseStep 598495 = 897743) B897743
theorem B4203197 : Blo 350755 4203197 := bstep (se 3 (by rfl) ⟨788099, by rfl⟩ : syracuseStep 4203197 = 1576199) B1576199
theorem B19309373 : Blo 350755 19309373 := bstep (se 3 (by rfl) ⟨3620507, by rfl⟩ : syracuseStep 19309373 = 7241015) B7241015
theorem B4302649 : Blo 350755 4302649 := bstep (se 2 (by rfl) ⟨1613493, by rfl⟩ : syracuseStep 4302649 = 3226987) B3226987
theorem B894847 : Blo 350755 894847 := bstep (se 1 (by rfl) ⟨671135, by rfl⟩ : syracuseStep 894847 = 1342271) B1342271
theorem B1353631 : Blo 350755 1353631 := bstep (se 1 (by rfl) ⟨1015223, by rfl⟩ : syracuseStep 1353631 = 2030447) B2030447
theorem B895151 : Blo 350755 895151 := bstep (se 1 (by rfl) ⟨671363, by rfl⟩ : syracuseStep 895151 = 1342727) B1342727
theorem B1289321 : Blo 350755 1289321 := bstep (se 2 (by rfl) ⟨483495, by rfl⟩ : syracuseStep 1289321 = 966991) B966991
theorem B35892413 : Blo 350755 35892413 := bstep (se 3 (by rfl) ⟨6729827, by rfl⟩ : syracuseStep 35892413 = 13459655) B13459655
theorem B1191455 : Blo 350755 1191455 := bstep (se 1 (by rfl) ⟨893591, by rfl⟩ : syracuseStep 1191455 = 1787183) B1787183
theorem B2011175 : Blo 350755 2011175 := bstep (se 1 (by rfl) ⟨1508381, by rfl⟩ : syracuseStep 2011175 = 3016763) B3016763
theorem B1192103 : Blo 350755 1192103 := bstep (se 1 (by rfl) ⟨894077, by rfl⟩ : syracuseStep 1192103 = 1788155) B1788155
theorem B897419 : Blo 350755 897419 := bstep (se 1 (by rfl) ⟨673064, by rfl⟩ : syracuseStep 897419 = 1346129) B1346129
theorem B4829975 : Blo 350755 4829975 := bstep (se 1 (by rfl) ⟨3622481, by rfl⟩ : syracuseStep 4829975 = 7244963) B7244963
theorem B34878275 : Blo 350755 34878275 := bstep (se 1 (by rfl) ⟨26158706, by rfl⟩ : syracuseStep 34878275 = 52317413) B52317413
theorem B897875 : Blo 350755 897875 := bstep (se 1 (by rfl) ⟨673406, by rfl⟩ : syracuseStep 897875 = 1346813) B1346813
theorem B1192859 : Blo 350755 1192859 := bstep (se 1 (by rfl) ⟨894644, by rfl⟩ : syracuseStep 1192859 = 1789289) B1789289
theorem B1193183 : Blo 350755 1193183 := bstep (se 1 (by rfl) ⟨894887, by rfl⟩ : syracuseStep 1193183 = 1789775) B1789775
theorem B964327 : Blo 350755 964327 := bstep (se 1 (by rfl) ⟨723245, by rfl⟩ : syracuseStep 964327 = 1446491) B1446491
theorem B1194047 : Blo 350755 1194047 := bstep (se 1 (by rfl) ⟨895535, by rfl⟩ : syracuseStep 1194047 = 1791071) B1791071
theorem B5093441 : Blo 350755 5093441 := bstep (se 2 (by rfl) ⟨1910040, by rfl⟩ : syracuseStep 5093441 = 3820081) B3820081
theorem B1915751 : Blo 350755 1915751 := bstep (se 1 (by rfl) ⟨1436813, by rfl⟩ : syracuseStep 1915751 = 2873627) B2873627
theorem B900409 : Blo 350755 900409 := bstep (se 2 (by rfl) ⟨337653, by rfl⟩ : syracuseStep 900409 = 675307) B675307
theorem B4570991 : Blo 350755 4570991 := bstep (se 1 (by rfl) ⟨3428243, by rfl⟩ : syracuseStep 4570991 = 6856487) B6856487
theorem B999391 : Blo 350755 999391 := bstep (se 1 (by rfl) ⟨749543, by rfl⟩ : syracuseStep 999391 = 1499087) B1499087
theorem B1196477 : Blo 350755 1196477 := bstep (se 3 (by rfl) ⟨224339, by rfl⟩ : syracuseStep 1196477 = 448679) B448679
theorem B3686849 : Blo 350755 3686849 := bstep (se 2 (by rfl) ⟨1382568, by rfl⟩ : syracuseStep 3686849 = 2765137) B2765137
theorem B541225 : Blo 350755 541225 := bstep (se 2 (by rfl) ⟨202959, by rfl⟩ : syracuseStep 541225 = 405919) B405919
theorem B2015867 : Blo 350755 2015867 := bstep (se 1 (by rfl) ⟨1511900, by rfl⟩ : syracuseStep 2015867 = 3023801) B3023801
theorem B1819369 : Blo 350755 1819369 := bstep (se 2 (by rfl) ⟨682263, by rfl⟩ : syracuseStep 1819369 = 1364527) B1364527
theorem B3395591 : Blo 350755 3395591 := bstep (se 1 (by rfl) ⟨2546693, by rfl⟩ : syracuseStep 3395591 = 5093387) B5093387
theorem B1364219 : Blo 350755 1364219 := bstep (se 1 (by rfl) ⟨1023164, by rfl⟩ : syracuseStep 1364219 = 2046329) B2046329
theorem B1003823 : Blo 350755 1003823 := bstep (se 1 (by rfl) ⟨752867, by rfl⟩ : syracuseStep 1003823 = 1505735) B1505735
theorem B446791 : Blo 350755 446791 := bstep (se 1 (by rfl) ⟨335093, by rfl⟩ : syracuseStep 446791 = 670187) B670187
theorem B1332065 : Blo 350755 1332065 := bstep (se 2 (by rfl) ⟨499524, by rfl⟩ : syracuseStep 1332065 = 999049) B999049
theorem B7230505 : Blo 350755 7230505 := bstep (se 2 (by rfl) ⟨2711439, by rfl⟩ : syracuseStep 7230505 = 5422879) B5422879
theorem B1332551 : Blo 350755 1332551 := bstep (se 1 (by rfl) ⟨999413, by rfl⟩ : syracuseStep 1332551 = 1998827) B1998827
theorem B1726319 : Blo 350755 1726319 := bstep (se 1 (by rfl) ⟨1294739, by rfl⟩ : syracuseStep 1726319 = 2589479) B2589479
theorem B351199 : Blo 350755 351199 := bstep (se 1 (by rfl) ⟨263399, by rfl⟩ : syracuseStep 351199 = 526799) B526799
theorem B351399 : Blo 350755 351399 := bstep (se 1 (by rfl) ⟨263549, by rfl⟩ : syracuseStep 351399 = 527099) B527099
theorem B1203431 : Blo 350755 1203431 := bstep (se 1 (by rfl) ⟨902573, by rfl⟩ : syracuseStep 1203431 = 1805147) B1805147
theorem B351679 : Blo 350755 351679 := bstep (se 1 (by rfl) ⟨263759, by rfl⟩ : syracuseStep 351679 = 527519) B527519
theorem B1007387 : Blo 350755 1007387 := bstep (se 1 (by rfl) ⟨755540, by rfl⟩ : syracuseStep 1007387 = 1511081) B1511081
theorem B352103 : Blo 350755 352103 := bstep (se 1 (by rfl) ⟨264077, by rfl⟩ : syracuseStep 352103 = 528155) B528155
theorem B352283 : Blo 350755 352283 := bstep (se 1 (by rfl) ⟨264212, by rfl⟩ : syracuseStep 352283 = 528425) B528425
theorem B352415 : Blo 350755 352415 := bstep (se 1 (by rfl) ⟨264311, by rfl⟩ : syracuseStep 352415 = 528623) B528623
theorem B352671 : Blo 350755 352671 := bstep (se 1 (by rfl) ⟨264503, by rfl⟩ : syracuseStep 352671 = 529007) B529007
theorem B352703 : Blo 350755 352703 := bstep (se 1 (by rfl) ⟨264527, by rfl⟩ : syracuseStep 352703 = 529055) B529055
theorem B352815 : Blo 350755 352815 := bstep (se 1 (by rfl) ⟨264611, by rfl⟩ : syracuseStep 352815 = 529223) B529223
theorem B2777723 : Blo 350755 2777723 := bstep (se 1 (by rfl) ⟨2083292, by rfl⟩ : syracuseStep 2777723 = 4166585) B4166585
theorem B352999 : Blo 350755 352999 := bstep (se 1 (by rfl) ⟨264749, by rfl⟩ : syracuseStep 352999 = 529499) B529499
theorem B79193213 : Blo 350755 79193213 := bstep (se 3 (by rfl) ⟨14848727, by rfl⟩ : syracuseStep 79193213 = 29697455) B29697455
theorem B353607 : Blo 350755 353607 := bstep (se 1 (by rfl) ⟨265205, by rfl⟩ : syracuseStep 353607 = 530411) B530411
theorem B87156323 : Blo 350755 87156323 := bstep (se 1 (by rfl) ⟨65367242, by rfl⟩ : syracuseStep 87156323 = 130734485) B130734485
theorem B354375 : Blo 350755 354375 := bstep (se 1 (by rfl) ⟨265781, by rfl⟩ : syracuseStep 354375 = 531563) B531563
theorem B1337897 : Blo 350755 1337897 := bstep (se 2 (by rfl) ⟨501711, by rfl⟩ : syracuseStep 1337897 = 1003423) B1003423
theorem B36498023 : Blo 350755 36498023 := bstep (se 1 (by rfl) ⟨27373517, by rfl⟩ : syracuseStep 36498023 = 54747035) B54747035
theorem B28929635 : Blo 350755 28929635 := bstep (se 1 (by rfl) ⟨21697226, by rfl⟩ : syracuseStep 28929635 = 43394453) B43394453
theorem B716519 : Blo 350755 716519 := bstep (se 1 (by rfl) ⟨537389, by rfl⟩ : syracuseStep 716519 = 1074779) B1074779
theorem B4288639 : Blo 350755 4288639 := bstep (se 1 (by rfl) ⟨3216479, by rfl⟩ : syracuseStep 4288639 = 6432959) B6432959
theorem B356543 : Blo 350755 356543 := bstep (se 1 (by rfl) ⟨267407, by rfl⟩ : syracuseStep 356543 = 534815) B534815
theorem B424219 : Blo 350755 424219 := bstep (se 1 (by rfl) ⟨318164, by rfl⟩ : syracuseStep 424219 = 636329) B636329
theorem B9633667 : Blo 350755 9633667 := bstep (se 1 (by rfl) ⟨7225250, by rfl⟩ : syracuseStep 9633667 = 14450501) B14450501
theorem B2457899 : Blo 350755 2457899 := bstep (se 1 (by rfl) ⟨1843424, by rfl⟩ : syracuseStep 2457899 = 3686849) B3686849
theorem B1343911 : Blo 350755 1343911 := bstep (se 1 (by rfl) ⟨1007933, by rfl⟩ : syracuseStep 1343911 = 2015867) B2015867
theorem B3408317 : Blo 350755 3408317 := bstep (se 3 (by rfl) ⟨639059, by rfl⟩ : syracuseStep 3408317 = 1278119) B1278119
theorem B2425825 : Blo 350755 2425825 := bstep (se 2 (by rfl) ⟨909684, by rfl⟩ : syracuseStep 2425825 = 1819369) B1819369
theorem B395131 : Blo 350755 395131 := bstep (se 1 (by rfl) ⟨296348, by rfl⟩ : syracuseStep 395131 = 592697) B592697
theorem B3803125 : Blo 350755 3803125 := bstep (se 5 (by rfl) ⟨178271, by rfl⟩ : syracuseStep 3803125 = 356543) B356543
theorem B1804841 : Blo 350755 1804841 := bstep (se 2 (by rfl) ⟨676815, by rfl⟩ : syracuseStep 1804841 = 1353631) B1353631
theorem B2263727 : Blo 350755 2263727 := bstep (se 1 (by rfl) ⟨1697795, by rfl⟩ : syracuseStep 2263727 = 3395591) B3395591
theorem B527231 : Blo 350755 527231 := bstep (se 1 (by rfl) ⟨395423, by rfl⟩ : syracuseStep 527231 = 790847) B790847
theorem B2886533 : Blo 350755 2886533 := bstep (se 4 (by rfl) ⟨270612, by rfl⟩ : syracuseStep 2886533 = 541225) B541225
theorem B789695 : Blo 350755 789695 := bstep (se 1 (by rfl) ⟨592271, by rfl⟩ : syracuseStep 789695 = 1184543) B1184543
theorem B888043 : Blo 350755 888043 := bstep (se 1 (by rfl) ⟨666032, by rfl⟩ : syracuseStep 888043 = 1332065) B1332065
theorem B888367 : Blo 350755 888367 := bstep (se 1 (by rfl) ⟨666275, by rfl⟩ : syracuseStep 888367 = 1332551) B1332551
theorem B2887919 : Blo 350755 2887919 := bstep (se 1 (by rfl) ⟨2165939, by rfl⟩ : syracuseStep 2887919 = 4331879) B4331879
theorem B1184651 : Blo 350755 1184651 := bstep (se 1 (by rfl) ⟨888488, by rfl⟩ : syracuseStep 1184651 = 1776977) B1776977
theorem B529343 : Blo 350755 529343 := bstep (se 1 (by rfl) ⟨397007, by rfl⟩ : syracuseStep 529343 = 794015) B794015
theorem B3020489 : Blo 350755 3020489 := bstep (se 2 (by rfl) ⟨1132683, by rfl⟩ : syracuseStep 3020489 = 2265367) B2265367
theorem B595721 : Blo 350755 595721 := bstep (se 2 (by rfl) ⟨223395, by rfl⟩ : syracuseStep 595721 = 446791) B446791
theorem B52795475 : Blo 350755 52795475 := bstep (se 1 (by rfl) ⟨39596606, by rfl⟩ : syracuseStep 52795475 = 79193213) B79193213
theorem B58104215 : Blo 350755 58104215 := bstep (se 1 (by rfl) ⟨43578161, by rfl⟩ : syracuseStep 58104215 = 87156323) B87156323
theorem B9640673 : Blo 350755 9640673 := bstep (se 2 (by rfl) ⟨3615252, by rfl⟩ : syracuseStep 9640673 = 7230505) B7230505
theorem B793313 : Blo 350755 793313 := bstep (se 2 (by rfl) ⟨297492, by rfl⟩ : syracuseStep 793313 = 594985) B594985
theorem B596767 : Blo 350755 596767 := bstep (se 1 (by rfl) ⟨447575, by rfl⟩ : syracuseStep 596767 = 895151) B895151
theorem B891931 : Blo 350755 891931 := bstep (se 1 (by rfl) ⟨668948, by rfl⟩ : syracuseStep 891931 = 1337897) B1337897
theorem B793673 : Blo 350755 793673 := bstep (se 2 (by rfl) ⟨297627, by rfl⟩ : syracuseStep 793673 = 595255) B595255
theorem B859547 : Blo 350755 859547 := bstep (se 1 (by rfl) ⟨644660, by rfl⟩ : syracuseStep 859547 = 1289321) B1289321
theorem B23928275 : Blo 350755 23928275 := bstep (se 1 (by rfl) ⟨17946206, by rfl⟩ : syracuseStep 23928275 = 35892413) B35892413
theorem B1285769 : Blo 350755 1285769 := bstep (se 2 (by rfl) ⟨482163, by rfl⟩ : syracuseStep 1285769 = 964327) B964327
theorem B794303 : Blo 350755 794303 := bstep (se 1 (by rfl) ⟨595727, by rfl⟩ : syracuseStep 794303 = 1191455) B1191455
theorem B794735 : Blo 350755 794735 := bstep (se 1 (by rfl) ⟨596051, by rfl⟩ : syracuseStep 794735 = 1192103) B1192103
theorem B598279 : Blo 350755 598279 := bstep (se 1 (by rfl) ⟨448709, by rfl⟩ : syracuseStep 598279 = 897419) B897419
theorem B565625 : Blo 350755 565625 := bstep (se 2 (by rfl) ⟨212109, by rfl⟩ : syracuseStep 565625 = 424219) B424219
theorem B3219983 : Blo 350755 3219983 := bstep (se 1 (by rfl) ⟨2414987, by rfl⟩ : syracuseStep 3219983 = 4829975) B4829975
theorem B598583 : Blo 350755 598583 := bstep (se 1 (by rfl) ⟨448937, by rfl⟩ : syracuseStep 598583 = 897875) B897875
theorem B795239 : Blo 350755 795239 := bstep (se 1 (by rfl) ⟨596429, by rfl⟩ : syracuseStep 795239 = 1192859) B1192859
theorem B795455 : Blo 350755 795455 := bstep (se 1 (by rfl) ⟨596591, by rfl⟩ : syracuseStep 795455 = 1193183) B1193183
theorem B796031 : Blo 350755 796031 := bstep (se 1 (by rfl) ⟨597023, by rfl⟩ : syracuseStep 796031 = 1194047) B1194047
theorem B22947461 : Blo 350755 22947461 := bstep (se 4 (by rfl) ⟨2151324, by rfl⟩ : syracuseStep 22947461 = 4302649) B4302649
theorem B2272157 : Blo 350755 2272157 := bstep (se 3 (by rfl) ⟨426029, by rfl⟩ : syracuseStep 2272157 = 852059) B852059
theorem B797651 : Blo 350755 797651 := bstep (se 1 (by rfl) ⟨598238, by rfl⟩ : syracuseStep 797651 = 1196477) B1196477
theorem B797993 : Blo 350755 797993 := bstep (se 2 (by rfl) ⟨299247, by rfl⟩ : syracuseStep 797993 = 598495) B598495
theorem B3387095 : Blo 350755 3387095 := bstep (se 1 (by rfl) ⟨2540321, by rfl⟩ : syracuseStep 3387095 = 5080643) B5080643
theorem B1355849 : Blo 350755 1355849 := bstep (se 2 (by rfl) ⟨508443, by rfl⟩ : syracuseStep 1355849 = 1016887) B1016887
theorem B1193129 : Blo 350755 1193129 := bstep (se 2 (by rfl) ⟨447423, by rfl⟩ : syracuseStep 1193129 = 894847) B894847
theorem B669215 : Blo 350755 669215 := bstep (se 1 (by rfl) ⟨501911, by rfl⟩ : syracuseStep 669215 = 1003823) B1003823
theorem B2668139 : Blo 350755 2668139 := bstep (se 1 (by rfl) ⟨2001104, by rfl⟩ : syracuseStep 2668139 = 4002209) B4002209
theorem B4603517 : Blo 350755 4603517 := bstep (se 3 (by rfl) ⟨863159, by rfl⟩ : syracuseStep 4603517 = 1726319) B1726319
theorem B671591 : Blo 350755 671591 := bstep (se 1 (by rfl) ⟨503693, by rfl⟩ : syracuseStep 671591 = 1007387) B1007387
theorem B5718185 : Blo 350755 5718185 := bstep (se 2 (by rfl) ⟨2144319, by rfl⟩ : syracuseStep 5718185 = 4288639) B4288639
theorem B1851815 : Blo 350755 1851815 := bstep (se 1 (by rfl) ⟨1388861, by rfl⟩ : syracuseStep 1851815 = 2777723) B2777723
theorem B2802131 : Blo 350755 2802131 := bstep (se 1 (by rfl) ⟨2101598, by rfl⟩ : syracuseStep 2802131 = 4203197) B4203197
theorem B24332015 : Blo 350755 24332015 := bstep (se 1 (by rfl) ⟨18249011, by rfl⟩ : syracuseStep 24332015 = 36498023) B36498023
theorem B19286423 : Blo 350755 19286423 := bstep (se 1 (by rfl) ⟨14464817, by rfl⟩ : syracuseStep 19286423 = 28929635) B28929635
theorem B477679 : Blo 350755 477679 := bstep (se 1 (by rfl) ⟨358259, by rfl⟩ : syracuseStep 477679 = 716519) B716519
theorem B23252183 : Blo 350755 23252183 := bstep (se 1 (by rfl) ⟨17439137, by rfl⟩ : syracuseStep 23252183 = 34878275) B34878275
theorem B3395627 : Blo 350755 3395627 := bstep (se 1 (by rfl) ⟨2546720, by rfl⟩ : syracuseStep 3395627 = 5093441) B5093441
theorem B1200545 : Blo 350755 1200545 := bstep (se 2 (by rfl) ⟨450204, by rfl⟩ : syracuseStep 1200545 = 900409) B900409
theorem B1332521 : Blo 350755 1332521 := bstep (se 2 (by rfl) ⟨499695, by rfl⟩ : syracuseStep 1332521 = 999391) B999391
theorem B1791719 : Blo 350755 1791719 := bstep (se 1 (by rfl) ⟨1343789, by rfl⟩ : syracuseStep 1791719 = 2687579) B2687579
theorem B351471 : Blo 350755 351471 := bstep (se 1 (by rfl) ⟨263603, by rfl⟩ : syracuseStep 351471 = 527207) B527207
theorem B351791 : Blo 350755 351791 := bstep (se 1 (by rfl) ⟨263843, by rfl⟩ : syracuseStep 351791 = 527687) B527687
theorem B351871 : Blo 350755 351871 := bstep (se 1 (by rfl) ⟨263903, by rfl⟩ : syracuseStep 351871 = 527807) B527807
theorem B352303 : Blo 350755 352303 := bstep (se 1 (by rfl) ⟨264227, by rfl⟩ : syracuseStep 352303 = 528455) B528455
theorem B614537 : Blo 350755 614537 := bstep (se 2 (by rfl) ⟨230451, by rfl⟩ : syracuseStep 614537 = 460903) B460903
theorem B909479 : Blo 350755 909479 := bstep (se 1 (by rfl) ⟨682109, by rfl⟩ : syracuseStep 909479 = 1364219) B1364219
theorem B1270363 : Blo 350755 1270363 := bstep (se 1 (by rfl) ⟨952772, by rfl⟩ : syracuseStep 1270363 = 1905545) B1905545
theorem B352859 : Blo 350755 352859 := bstep (se 1 (by rfl) ⟨264644, by rfl⟩ : syracuseStep 352859 = 529289) B529289
theorem B1335923 : Blo 350755 1335923 := bstep (se 1 (by rfl) ⟨1001942, by rfl⟩ : syracuseStep 1335923 = 2003885) B2003885
theorem B353007 : Blo 350755 353007 := bstep (se 1 (by rfl) ⟨264755, by rfl⟩ : syracuseStep 353007 = 529511) B529511
theorem B353883 : Blo 350755 353883 := bstep (se 1 (by rfl) ⟨265412, by rfl⟩ : syracuseStep 353883 = 530825) B530825
theorem B1009255 : Blo 350755 1009255 := bstep (se 1 (by rfl) ⟨756941, by rfl⟩ : syracuseStep 1009255 = 1513883) B1513883
theorem B354075 : Blo 350755 354075 := bstep (se 1 (by rfl) ⟨265556, by rfl⟩ : syracuseStep 354075 = 531113) B531113
theorem B354751 : Blo 350755 354751 := bstep (se 1 (by rfl) ⟨266063, by rfl⟩ : syracuseStep 354751 = 532127) B532127
theorem B12872915 : Blo 350755 12872915 := bstep (se 1 (by rfl) ⟨9654686, by rfl⟩ : syracuseStep 12872915 = 19309373) B19309373
theorem B1340783 : Blo 350755 1340783 := bstep (se 1 (by rfl) ⟨1005587, by rfl⟩ : syracuseStep 1340783 = 2011175) B2011175
theorem B3209149 : Blo 350755 3209149 := bstep (se 3 (by rfl) ⟨601715, by rfl⟩ : syracuseStep 3209149 = 1203431) B1203431
theorem B1277167 : Blo 350755 1277167 := bstep (se 1 (by rfl) ⟨957875, by rfl⟩ : syracuseStep 1277167 = 1915751) B1915751
theorem B12844889 : Blo 350755 12844889 := bstep (se 2 (by rfl) ⟨4816833, by rfl⟩ : syracuseStep 12844889 = 9633667) B9633667
theorem B3047327 : Blo 350755 3047327 := bstep (se 1 (by rfl) ⟨2285495, by rfl⟩ : syracuseStep 3047327 = 4570991) B4570991
theorem B1638599 : Blo 350755 1638599 := bstep (se 1 (by rfl) ⟨1228949, by rfl⟩ : syracuseStep 1638599 = 2457899) B2457899
theorem B1868087 : Blo 350755 1868087 := bstep (se 1 (by rfl) ⟨1401065, by rfl⟩ : syracuseStep 1868087 = 2802131) B2802131
theorem B2425277 : Blo 350755 2425277 := bstep (se 3 (by rfl) ⟨454739, by rfl⟩ : syracuseStep 2425277 = 909479) B909479
theorem B1509151 : Blo 350755 1509151 := bstep (se 1 (by rfl) ⟨1131863, by rfl⟩ : syracuseStep 1509151 = 2263727) B2263727
theorem B526463 : Blo 350755 526463 := bstep (se 1 (by rfl) ⟨394847, by rfl⟩ : syracuseStep 526463 = 789695) B789695
theorem B1345673 : Blo 350755 1345673 := bstep (se 2 (by rfl) ⟨504627, by rfl⟩ : syracuseStep 1345673 = 1009255) B1009255
theorem B15501455 : Blo 350755 15501455 := bstep (se 1 (by rfl) ⟨11626091, by rfl⟩ : syracuseStep 15501455 = 23252183) B23252183
theorem B526841 : Blo 350755 526841 := bstep (se 2 (by rfl) ⟨197565, by rfl⟩ : syracuseStep 526841 = 395131) B395131
theorem B2263751 : Blo 350755 2263751 := bstep (se 1 (by rfl) ⟨1697813, by rfl⟩ : syracuseStep 2263751 = 3395627) B3395627
theorem B789767 : Blo 350755 789767 := bstep (se 1 (by rfl) ⟨592325, by rfl⟩ : syracuseStep 789767 = 1184651) B1184651
theorem B888347 : Blo 350755 888347 := bstep (se 1 (by rfl) ⟨666260, by rfl⟩ : syracuseStep 888347 = 1332521) B1332521
theorem B397147 : Blo 350755 397147 := bstep (se 1 (by rfl) ⟨297860, by rfl⟩ : syracuseStep 397147 = 595721) B595721
theorem B35196983 : Blo 350755 35196983 := bstep (se 1 (by rfl) ⟨26397737, by rfl⟩ : syracuseStep 35196983 = 52795475) B52795475
theorem B38736143 : Blo 350755 38736143 := bstep (se 1 (by rfl) ⟨29052107, by rfl⟩ : syracuseStep 38736143 = 58104215) B58104215
theorem B1184057 : Blo 350755 1184057 := bstep (se 2 (by rfl) ⟨444021, by rfl⟩ : syracuseStep 1184057 = 888043) B888043
theorem B6427115 : Blo 350755 6427115 := bstep (se 1 (by rfl) ⟨4820336, by rfl⟩ : syracuseStep 6427115 = 9640673) B9640673
theorem B528875 : Blo 350755 528875 := bstep (se 1 (by rfl) ⟨396656, by rfl⟩ : syracuseStep 528875 = 793313) B793313
theorem B64885373 : Blo 350755 64885373 := bstep (se 3 (by rfl) ⟨12166007, by rfl⟩ : syracuseStep 64885373 = 24332015) B24332015
theorem B529115 : Blo 350755 529115 := bstep (se 1 (by rfl) ⟨396836, by rfl⟩ : syracuseStep 529115 = 793673) B793673
theorem B1184489 : Blo 350755 1184489 := bstep (se 2 (by rfl) ⟨444183, by rfl⟩ : syracuseStep 1184489 = 888367) B888367
theorem B857179 : Blo 350755 857179 := bstep (se 1 (by rfl) ⟨642884, by rfl⟩ : syracuseStep 857179 = 1285769) B1285769
theorem B529535 : Blo 350755 529535 := bstep (se 1 (by rfl) ⟨397151, by rfl⟩ : syracuseStep 529535 = 794303) B794303
theorem B529823 : Blo 350755 529823 := bstep (se 1 (by rfl) ⟨397367, by rfl⟩ : syracuseStep 529823 = 794735) B794735
theorem B399055 : Blo 350755 399055 := bstep (se 1 (by rfl) ⟨299291, by rfl⟩ : syracuseStep 399055 = 598583) B598583
theorem B530159 : Blo 350755 530159 := bstep (se 1 (by rfl) ⟨397619, by rfl⟩ : syracuseStep 530159 = 795239) B795239
theorem B890615 : Blo 350755 890615 := bstep (se 1 (by rfl) ⟨667961, by rfl⟩ : syracuseStep 890615 = 1335923) B1335923
theorem B530303 : Blo 350755 530303 := bstep (se 1 (by rfl) ⟨397727, by rfl⟩ : syracuseStep 530303 = 795455) B795455
theorem B530687 : Blo 350755 530687 := bstep (se 1 (by rfl) ⟨398015, by rfl⟩ : syracuseStep 530687 = 796031) B796031
theorem B1514771 : Blo 350755 1514771 := bstep (se 1 (by rfl) ⟨1136078, by rfl⟩ : syracuseStep 1514771 = 2272157) B2272157
theorem B531767 : Blo 350755 531767 := bstep (se 1 (by rfl) ⟨398825, by rfl⟩ : syracuseStep 531767 = 797651) B797651
theorem B531995 : Blo 350755 531995 := bstep (se 1 (by rfl) ⟨398996, by rfl⟩ : syracuseStep 531995 = 797993) B797993
theorem B795419 : Blo 350755 795419 := bstep (se 1 (by rfl) ⟨596564, by rfl⟩ : syracuseStep 795419 = 1193129) B1193129
theorem B893855 : Blo 350755 893855 := bstep (se 1 (by rfl) ⟨670391, by rfl⟩ : syracuseStep 893855 = 1340783) B1340783
theorem B795689 : Blo 350755 795689 := bstep (se 2 (by rfl) ⟨298383, by rfl⟩ : syracuseStep 795689 = 596767) B596767
theorem B1778759 : Blo 350755 1778759 := bstep (se 1 (by rfl) ⟨1334069, by rfl⟩ : syracuseStep 1778759 = 2668139) B2668139
theorem B1189241 : Blo 350755 1189241 := bstep (se 2 (by rfl) ⟨445965, by rfl⟩ : syracuseStep 1189241 = 891931) B891931
theorem B8563259 : Blo 350755 8563259 := bstep (se 1 (by rfl) ⟨6422444, by rfl⟩ : syracuseStep 8563259 = 12844889) B12844889
theorem B3812123 : Blo 350755 3812123 := bstep (se 1 (by rfl) ⟨2859092, by rfl⟩ : syracuseStep 3812123 = 5718185) B5718185
theorem B2272211 : Blo 350755 2272211 := bstep (se 1 (by rfl) ⟨1704158, by rfl⟩ : syracuseStep 2272211 = 3408317) B3408317
theorem B797705 : Blo 350755 797705 := bstep (se 2 (by rfl) ⟨299139, by rfl⟩ : syracuseStep 797705 = 598279) B598279
theorem B12857615 : Blo 350755 12857615 := bstep (se 1 (by rfl) ⟨9643211, by rfl⟩ : syracuseStep 12857615 = 19286423) B19286423
theorem B800363 : Blo 350755 800363 := bstep (se 1 (by rfl) ⟨600272, by rfl⟩ : syracuseStep 800363 = 1200545) B1200545
theorem B636905 : Blo 350755 636905 := bstep (se 2 (by rfl) ⟨238839, by rfl⟩ : syracuseStep 636905 = 477679) B477679
theorem B2013659 : Blo 350755 2013659 := bstep (se 1 (by rfl) ⟨1510244, by rfl⟩ : syracuseStep 2013659 = 3020489) B3020489
theorem B1194479 : Blo 350755 1194479 := bstep (se 1 (by rfl) ⟨895859, by rfl⟩ : syracuseStep 1194479 = 1791719) B1791719
theorem B573031 : Blo 350755 573031 := bstep (se 1 (by rfl) ⟨429773, by rfl⟩ : syracuseStep 573031 = 859547) B859547
theorem B409691 : Blo 350755 409691 := bstep (se 1 (by rfl) ⟨307268, by rfl⟩ : syracuseStep 409691 = 614537) B614537
theorem B377083 : Blo 350755 377083 := bstep (se 1 (by rfl) ⟨282812, by rfl⟩ : syracuseStep 377083 = 565625) B565625
theorem B2146655 : Blo 350755 2146655 := bstep (se 1 (by rfl) ⟨1609991, by rfl⟩ : syracuseStep 2146655 = 3219983) B3219983
theorem B4278865 : Blo 350755 4278865 := bstep (se 2 (by rfl) ⟨1604574, by rfl⟩ : syracuseStep 4278865 = 3209149) B3209149
theorem B903899 : Blo 350755 903899 := bstep (se 1 (by rfl) ⟨677924, by rfl⟩ : syracuseStep 903899 = 1355849) B1355849
theorem B446143 : Blo 350755 446143 := bstep (se 1 (by rfl) ⟨334607, by rfl⟩ : syracuseStep 446143 = 669215) B669215
theorem B1790909 : Blo 350755 1790909 := bstep (se 3 (by rfl) ⟨335795, by rfl⟩ : syracuseStep 1790909 = 671591) B671591
theorem B3069011 : Blo 350755 3069011 := bstep (se 1 (by rfl) ⟨2301758, by rfl⟩ : syracuseStep 3069011 = 4603517) B4603517
theorem B1234543 : Blo 350755 1234543 := bstep (se 1 (by rfl) ⟨925907, by rfl⟩ : syracuseStep 1234543 = 1851815) B1851815
theorem B1791881 : Blo 350755 1791881 := bstep (se 2 (by rfl) ⟨671955, by rfl⟩ : syracuseStep 1791881 = 1343911) B1343911
theorem B1693817 : Blo 350755 1693817 := bstep (se 2 (by rfl) ⟨635181, by rfl⟩ : syracuseStep 1693817 = 1270363) B1270363
theorem B3234433 : Blo 350755 3234433 := bstep (se 2 (by rfl) ⟨1212912, by rfl⟩ : syracuseStep 3234433 = 2425825) B2425825
theorem B1203227 : Blo 350755 1203227 := bstep (se 1 (by rfl) ⟨902420, by rfl⟩ : syracuseStep 1203227 = 1804841) B1804841
theorem B351487 : Blo 350755 351487 := bstep (se 1 (by rfl) ⟨263615, by rfl⟩ : syracuseStep 351487 = 527231) B527231
theorem B1924355 : Blo 350755 1924355 := bstep (se 1 (by rfl) ⟨1443266, by rfl⟩ : syracuseStep 1924355 = 2886533) B2886533
theorem B5070833 : Blo 350755 5070833 := bstep (se 2 (by rfl) ⟨1901562, by rfl⟩ : syracuseStep 5070833 = 3803125) B3803125
theorem B1925279 : Blo 350755 1925279 := bstep (se 1 (by rfl) ⟨1443959, by rfl⟩ : syracuseStep 1925279 = 2887919) B2887919
theorem B352895 : Blo 350755 352895 := bstep (se 1 (by rfl) ⟨264671, by rfl⟩ : syracuseStep 352895 = 529343) B529343
theorem B15952183 : Blo 350755 15952183 := bstep (se 1 (by rfl) ⟨11964137, by rfl⟩ : syracuseStep 15952183 = 23928275) B23928275
theorem B15298307 : Blo 350755 15298307 := bstep (se 1 (by rfl) ⟨11473730, by rfl⟩ : syracuseStep 15298307 = 22947461) B22947461
theorem B8581943 : Blo 350755 8581943 := bstep (se 1 (by rfl) ⟨6436457, by rfl⟩ : syracuseStep 8581943 = 12872915) B12872915
theorem B2258063 : Blo 350755 2258063 := bstep (se 1 (by rfl) ⟨1693547, by rfl⟩ : syracuseStep 2258063 = 3387095) B3387095
theorem B1702889 : Blo 350755 1702889 := bstep (se 2 (by rfl) ⟨638583, by rfl⟩ : syracuseStep 1702889 = 1277167) B1277167
theorem B2031551 : Blo 350755 2031551 := bstep (se 1 (by rfl) ⟨1523663, by rfl⟩ : syracuseStep 2031551 = 3047327) B3047327
theorem B4981565 : Blo 350755 4981565 := bstep (se 3 (by rfl) ⟨934043, by rfl⟩ : syracuseStep 4981565 = 1868087) B1868087
theorem B1509167 : Blo 350755 1509167 := bstep (se 1 (by rfl) ⟨1131875, by rfl⟩ : syracuseStep 1509167 = 2263751) B2263751
theorem B526511 : Blo 350755 526511 := bstep (se 1 (by rfl) ⟨394883, by rfl⟩ : syracuseStep 526511 = 789767) B789767
theorem B592231 : Blo 350755 592231 := bstep (se 1 (by rfl) ⟨444173, by rfl⟩ : syracuseStep 592231 = 888347) B888347
theorem B23464655 : Blo 350755 23464655 := bstep (se 1 (by rfl) ⟨17598491, by rfl⟩ : syracuseStep 23464655 = 35196983) B35196983
theorem B25824095 : Blo 350755 25824095 := bstep (se 1 (by rfl) ⟨19368071, by rfl⟩ : syracuseStep 25824095 = 38736143) B38736143
theorem B789371 : Blo 350755 789371 := bstep (se 1 (by rfl) ⟨592028, by rfl⟩ : syracuseStep 789371 = 1184057) B1184057
theorem B43256915 : Blo 350755 43256915 := bstep (se 1 (by rfl) ⟨32442686, by rfl⟩ : syracuseStep 43256915 = 64885373) B64885373
theorem B789659 : Blo 350755 789659 := bstep (se 1 (by rfl) ⟨592244, by rfl⟩ : syracuseStep 789659 = 1184489) B1184489
theorem B5705153 : Blo 350755 5705153 := bstep (se 2 (by rfl) ⟨2139432, by rfl⟩ : syracuseStep 5705153 = 4278865) B4278865
theorem B593743 : Blo 350755 593743 := bstep (se 1 (by rfl) ⟨445307, by rfl⟩ : syracuseStep 593743 = 890615) B890615
theorem B594857 : Blo 350755 594857 := bstep (se 2 (by rfl) ⟨223071, by rfl⟩ : syracuseStep 594857 = 446143) B446143
theorem B529529 : Blo 350755 529529 := bstep (se 2 (by rfl) ⟨198573, by rfl⟩ : syracuseStep 529529 = 397147) B397147
theorem B3380555 : Blo 350755 3380555 := bstep (se 1 (by rfl) ⟨2535416, by rfl⟩ : syracuseStep 3380555 = 5070833) B5070833
theorem B1283519 : Blo 350755 1283519 := bstep (se 1 (by rfl) ⟨962639, by rfl⟩ : syracuseStep 1283519 = 1925279) B1925279
theorem B530279 : Blo 350755 530279 := bstep (se 1 (by rfl) ⟨397709, by rfl⟩ : syracuseStep 530279 = 795419) B795419
theorem B595903 : Blo 350755 595903 := bstep (se 1 (by rfl) ⟨446927, by rfl⟩ : syracuseStep 595903 = 893855) B893855
theorem B530459 : Blo 350755 530459 := bstep (se 1 (by rfl) ⟨397844, by rfl⟩ : syracuseStep 530459 = 795689) B795689
theorem B1185839 : Blo 350755 1185839 := bstep (se 1 (by rfl) ⟨889379, by rfl⟩ : syracuseStep 1185839 = 1778759) B1778759
theorem B792827 : Blo 350755 792827 := bstep (se 1 (by rfl) ⟨594620, by rfl⟩ : syracuseStep 792827 = 1189241) B1189241
theorem B1514807 : Blo 350755 1514807 := bstep (se 1 (by rfl) ⟨1136105, by rfl⟩ : syracuseStep 1514807 = 2272211) B2272211
theorem B531803 : Blo 350755 531803 := bstep (se 1 (by rfl) ⟨398852, by rfl⟩ : syracuseStep 531803 = 797705) B797705
theorem B1646057 : Blo 350755 1646057 := bstep (se 2 (by rfl) ⟨617271, by rfl⟩ : syracuseStep 1646057 = 1234543) B1234543
theorem B532073 : Blo 350755 532073 := bstep (se 2 (by rfl) ⟨199527, by rfl⟩ : syracuseStep 532073 = 399055) B399055
theorem B10198871 : Blo 350755 10198871 := bstep (se 1 (by rfl) ⟨7649153, by rfl⟩ : syracuseStep 10198871 = 15298307) B15298307
theorem B533575 : Blo 350755 533575 := bstep (se 1 (by rfl) ⟨400181, by rfl⟩ : syracuseStep 533575 = 800363) B800363
theorem B796319 : Blo 350755 796319 := bstep (se 1 (by rfl) ⟨597239, by rfl⟩ : syracuseStep 796319 = 1194479) B1194479
theorem B764041 : Blo 350755 764041 := bstep (se 2 (by rfl) ⟨286515, by rfl⟩ : syracuseStep 764041 = 573031) B573031
theorem B1354367 : Blo 350755 1354367 := bstep (se 1 (by rfl) ⟨1015775, by rfl⟩ : syracuseStep 1354367 = 2031551) B2031551
theorem B1092509 : Blo 350755 1092509 := bstep (se 3 (by rfl) ⟨204845, by rfl⟩ : syracuseStep 1092509 = 409691) B409691
theorem B1616851 : Blo 350755 1616851 := bstep (se 1 (by rfl) ⟨1212638, by rfl⟩ : syracuseStep 1616851 = 2425277) B2425277
theorem B502777 : Blo 350755 502777 := bstep (se 2 (by rfl) ⟨188541, by rfl⟩ : syracuseStep 502777 = 377083) B377083
theorem B897115 : Blo 350755 897115 := bstep (se 1 (by rfl) ⟨672836, by rfl⟩ : syracuseStep 897115 = 1345673) B1345673
theorem B10334303 : Blo 350755 10334303 := bstep (se 1 (by rfl) ⟨7750727, by rfl⟩ : syracuseStep 10334303 = 15501455) B15501455
theorem B85078309 : Blo 350755 85078309 := bstep (se 4 (by rfl) ⟨7976091, by rfl⟩ : syracuseStep 85078309 = 15952183) B15952183
theorem B602599 : Blo 350755 602599 := bstep (se 1 (by rfl) ⟨451949, by rfl⟩ : syracuseStep 602599 = 903899) B903899
theorem B17478389 : Blo 350755 17478389 := bstep (se 5 (by rfl) ⟨819299, by rfl⟩ : syracuseStep 17478389 = 1638599) B1638599
theorem B2012201 : Blo 350755 2012201 := bstep (se 2 (by rfl) ⟨754575, by rfl⟩ : syracuseStep 2012201 = 1509151) B1509151
theorem B1193939 : Blo 350755 1193939 := bstep (se 1 (by rfl) ⟨895454, by rfl⟩ : syracuseStep 1193939 = 1790909) B1790909
theorem B2046007 : Blo 350755 2046007 := bstep (se 1 (by rfl) ⟨1534505, by rfl⟩ : syracuseStep 2046007 = 3069011) B3069011
theorem B1194587 : Blo 350755 1194587 := bstep (se 1 (by rfl) ⟨895940, by rfl⟩ : syracuseStep 1194587 = 1791881) B1791881
theorem B1129211 : Blo 350755 1129211 := bstep (se 1 (by rfl) ⟨846908, by rfl⟩ : syracuseStep 1129211 = 1693817) B1693817
theorem B802151 : Blo 350755 802151 := bstep (se 1 (by rfl) ⟨601613, by rfl⟩ : syracuseStep 802151 = 1203227) B1203227
theorem B2541415 : Blo 350755 2541415 := bstep (se 1 (by rfl) ⟨1906061, by rfl⟩ : syracuseStep 2541415 = 3812123) B3812123
theorem B8571743 : Blo 350755 8571743 := bstep (se 1 (by rfl) ⟨6428807, by rfl⟩ : syracuseStep 8571743 = 12857615) B12857615
theorem B5721295 : Blo 350755 5721295 := bstep (se 1 (by rfl) ⟨4290971, by rfl⟩ : syracuseStep 5721295 = 8581943) B8581943
theorem B5131613 : Blo 350755 5131613 := bstep (se 3 (by rfl) ⟨962177, by rfl⟩ : syracuseStep 5131613 = 1924355) B1924355
theorem B4312577 : Blo 350755 4312577 := bstep (se 2 (by rfl) ⟨1617216, by rfl⟩ : syracuseStep 4312577 = 3234433) B3234433
theorem B1135259 : Blo 350755 1135259 := bstep (se 1 (by rfl) ⟨851444, by rfl⟩ : syracuseStep 1135259 = 1702889) B1702889
theorem B1431103 : Blo 350755 1431103 := bstep (se 1 (by rfl) ⟨1073327, by rfl⟩ : syracuseStep 1431103 = 2146655) B2146655
theorem B350975 : Blo 350755 350975 := bstep (se 1 (by rfl) ⟨263231, by rfl⟩ : syracuseStep 350975 = 526463) B526463
theorem B351227 : Blo 350755 351227 := bstep (se 1 (by rfl) ⟨263420, by rfl⟩ : syracuseStep 351227 = 526841) B526841
theorem B4284743 : Blo 350755 4284743 := bstep (se 1 (by rfl) ⟨3213557, by rfl⟩ : syracuseStep 4284743 = 6427115) B6427115
theorem B352583 : Blo 350755 352583 := bstep (se 1 (by rfl) ⟨264437, by rfl⟩ : syracuseStep 352583 = 528875) B528875
theorem B352743 : Blo 350755 352743 := bstep (se 1 (by rfl) ⟨264557, by rfl⟩ : syracuseStep 352743 = 529115) B529115
theorem B353023 : Blo 350755 353023 := bstep (se 1 (by rfl) ⟨264767, by rfl⟩ : syracuseStep 353023 = 529535) B529535
theorem B353215 : Blo 350755 353215 := bstep (se 1 (by rfl) ⟨264911, by rfl⟩ : syracuseStep 353215 = 529823) B529823
theorem B353439 : Blo 350755 353439 := bstep (se 1 (by rfl) ⟨265079, by rfl⟩ : syracuseStep 353439 = 530159) B530159
theorem B353535 : Blo 350755 353535 := bstep (se 1 (by rfl) ⟨265151, by rfl⟩ : syracuseStep 353535 = 530303) B530303
theorem B353791 : Blo 350755 353791 := bstep (se 1 (by rfl) ⟨265343, by rfl⟩ : syracuseStep 353791 = 530687) B530687
theorem B1009847 : Blo 350755 1009847 := bstep (se 1 (by rfl) ⟨757385, by rfl⟩ : syracuseStep 1009847 = 1514771) B1514771
theorem B354511 : Blo 350755 354511 := bstep (se 1 (by rfl) ⟨265883, by rfl⟩ : syracuseStep 354511 = 531767) B531767
theorem B354663 : Blo 350755 354663 := bstep (se 1 (by rfl) ⟨265997, by rfl⟩ : syracuseStep 354663 = 531995) B531995
theorem B1142905 : Blo 350755 1142905 := bstep (se 2 (by rfl) ⟨428589, by rfl⟩ : syracuseStep 1142905 = 857179) B857179
theorem B22835357 : Blo 350755 22835357 := bstep (se 3 (by rfl) ⟨4281629, by rfl⟩ : syracuseStep 22835357 = 8563259) B8563259
theorem B1505375 : Blo 350755 1505375 := bstep (se 1 (by rfl) ⟨1129031, by rfl⟩ : syracuseStep 1505375 = 2258063) B2258063
theorem B424603 : Blo 350755 424603 := bstep (se 1 (by rfl) ⟨318452, by rfl⟩ : syracuseStep 424603 = 636905) B636905
theorem B1342439 : Blo 350755 1342439 := bstep (se 1 (by rfl) ⟨1006829, by rfl⟩ : syracuseStep 1342439 = 2013659) B2013659
theorem B526247 : Blo 350755 526247 := bstep (se 1 (by rfl) ⟨394685, by rfl⟩ : syracuseStep 526247 = 789371) B789371
theorem B28837943 : Blo 350755 28837943 := bstep (se 1 (by rfl) ⟨21628457, by rfl⟩ : syracuseStep 28837943 = 43256915) B43256915
theorem B526439 : Blo 350755 526439 := bstep (se 1 (by rfl) ⟨394829, by rfl⟩ : syracuseStep 526439 = 789659) B789659
theorem B3803435 : Blo 350755 3803435 := bstep (se 1 (by rfl) ⟨2852576, by rfl⟩ : syracuseStep 3803435 = 5705153) B5705153
theorem B1018721 : Blo 350755 1018721 := bstep (se 2 (by rfl) ⟨382020, by rfl⟩ : syracuseStep 1018721 = 764041) B764041
theorem B756839 : Blo 350755 756839 := bstep (se 1 (by rfl) ⟨567629, by rfl⟩ : syracuseStep 756839 = 1135259) B1135259
theorem B789641 : Blo 350755 789641 := bstep (se 2 (by rfl) ⟨296115, by rfl⟩ : syracuseStep 789641 = 592231) B592231
theorem B396571 : Blo 350755 396571 := bstep (se 1 (by rfl) ⟨297428, by rfl⟩ : syracuseStep 396571 = 594857) B594857
theorem B9014813 : Blo 350755 9014813 := bstep (se 3 (by rfl) ⟨1690277, by rfl⟩ : syracuseStep 9014813 = 3380555) B3380555
theorem B855679 : Blo 350755 855679 := bstep (se 1 (by rfl) ⟨641759, by rfl⟩ : syracuseStep 855679 = 1283519) B1283519
theorem B790559 : Blo 350755 790559 := bstep (se 1 (by rfl) ⟨592919, by rfl⟩ : syracuseStep 790559 = 1185839) B1185839
theorem B528551 : Blo 350755 528551 := bstep (se 1 (by rfl) ⟨396413, by rfl⟩ : syracuseStep 528551 = 792827) B792827
theorem B8623205 : Blo 350755 8623205 := bstep (se 4 (by rfl) ⟨808425, by rfl⟩ : syracuseStep 8623205 = 1616851) B1616851
theorem B791657 : Blo 350755 791657 := bstep (se 2 (by rfl) ⟨296871, by rfl⟩ : syracuseStep 791657 = 593743) B593743
theorem B2692925 : Blo 350755 2692925 := bstep (se 3 (by rfl) ⟨504923, by rfl⟩ : syracuseStep 2692925 = 1009847) B1009847
theorem B530879 : Blo 350755 530879 := bstep (se 1 (by rfl) ⟨398159, by rfl⟩ : syracuseStep 530879 = 796319) B796319
theorem B1908137 : Blo 350755 1908137 := bstep (se 2 (by rfl) ⟨715551, by rfl⟩ : syracuseStep 1908137 = 1431103) B1431103
theorem B794537 : Blo 350755 794537 := bstep (se 2 (by rfl) ⟨297951, by rfl⟩ : syracuseStep 794537 = 595903) B595903
theorem B6889535 : Blo 350755 6889535 := bstep (se 1 (by rfl) ⟨5167151, by rfl⟩ : syracuseStep 6889535 = 10334303) B10334303
theorem B2728009 : Blo 350755 2728009 := bstep (se 2 (by rfl) ⟨1023003, by rfl⟩ : syracuseStep 2728009 = 2046007) B2046007
theorem B566137 : Blo 350755 566137 := bstep (se 2 (by rfl) ⟨212301, by rfl⟩ : syracuseStep 566137 = 424603) B424603
theorem B795959 : Blo 350755 795959 := bstep (se 1 (by rfl) ⟨596969, by rfl⟩ : syracuseStep 795959 = 1193939) B1193939
theorem B796391 : Blo 350755 796391 := bstep (se 1 (by rfl) ⟨597293, by rfl⟩ : syracuseStep 796391 = 1194587) B1194587
theorem B894959 : Blo 350755 894959 := bstep (se 1 (by rfl) ⟨671219, by rfl⟩ : syracuseStep 894959 = 1342439) B1342439
theorem B534767 : Blo 350755 534767 := bstep (se 1 (by rfl) ⟨401075, by rfl⟩ : syracuseStep 534767 = 802151) B802151
theorem B3321043 : Blo 350755 3321043 := bstep (se 1 (by rfl) ⟨2490782, by rfl⟩ : syracuseStep 3321043 = 4981565) B4981565
theorem B15643103 : Blo 350755 15643103 := bstep (se 1 (by rfl) ⟨11732327, by rfl⟩ : syracuseStep 15643103 = 23464655) B23464655
theorem B5714495 : Blo 350755 5714495 := bstep (se 1 (by rfl) ⟨4285871, by rfl⟩ : syracuseStep 5714495 = 8571743) B8571743
theorem B17216063 : Blo 350755 17216063 := bstep (se 1 (by rfl) ⟨12912047, by rfl⟩ : syracuseStep 17216063 = 25824095) B25824095
theorem B46609037 : Blo 350755 46609037 := bstep (se 3 (by rfl) ⟨8739194, by rfl⟩ : syracuseStep 46609037 = 17478389) B17478389
theorem B3388553 : Blo 350755 3388553 := bstep (se 2 (by rfl) ⟨1270707, by rfl⟩ : syracuseStep 3388553 = 2541415) B2541415
theorem B670369 : Blo 350755 670369 := bstep (se 2 (by rfl) ⟨251388, by rfl⟩ : syracuseStep 670369 = 502777) B502777
theorem B1097371 : Blo 350755 1097371 := bstep (se 1 (by rfl) ⟨823028, by rfl⟩ : syracuseStep 1097371 = 1646057) B1646057
theorem B6799247 : Blo 350755 6799247 := bstep (se 1 (by rfl) ⟨5099435, by rfl⟩ : syracuseStep 6799247 = 10198871) B10198871
theorem B1196153 : Blo 350755 1196153 := bstep (se 2 (by rfl) ⟨448557, by rfl⟩ : syracuseStep 1196153 = 897115) B897115
theorem B1523873 : Blo 350755 1523873 := bstep (se 2 (by rfl) ⟨571452, by rfl⟩ : syracuseStep 1523873 = 1142905) B1142905
theorem B803465 : Blo 350755 803465 := bstep (se 2 (by rfl) ⟨301299, by rfl⟩ : syracuseStep 803465 = 602599) B602599
theorem B46613717 : Blo 350755 46613717 := bstep (se 7 (by rfl) ⟨546254, by rfl⟩ : syracuseStep 46613717 = 1092509) B1092509
theorem B902911 : Blo 350755 902911 := bstep (se 1 (by rfl) ⟨677183, by rfl⟩ : syracuseStep 902911 = 1354367) B1354367
theorem B15223571 : Blo 350755 15223571 := bstep (se 1 (by rfl) ⟨11417678, by rfl⟩ : syracuseStep 15223571 = 22835357) B22835357
theorem B13684301 : Blo 350755 13684301 := bstep (se 3 (by rfl) ⟨2565806, by rfl⟩ : syracuseStep 13684301 = 5131613) B5131613
theorem B1003583 : Blo 350755 1003583 := bstep (se 1 (by rfl) ⟨752687, by rfl⟩ : syracuseStep 1003583 = 1505375) B1505375
theorem B1006111 : Blo 350755 1006111 := bstep (se 1 (by rfl) ⟨754583, by rfl⟩ : syracuseStep 1006111 = 1509167) B1509167
theorem B711433 : Blo 350755 711433 := bstep (se 2 (by rfl) ⟨266787, by rfl⟩ : syracuseStep 711433 = 533575) B533575
theorem B351007 : Blo 350755 351007 := bstep (se 1 (by rfl) ⟨263255, by rfl⟩ : syracuseStep 351007 = 526511) B526511
theorem B2875051 : Blo 350755 2875051 := bstep (se 1 (by rfl) ⟨2156288, by rfl⟩ : syracuseStep 2875051 = 4312577) B4312577
theorem B45703925 : Blo 350755 45703925 := bstep (se 5 (by rfl) ⟨2142371, by rfl⟩ : syracuseStep 45703925 = 4284743) B4284743
theorem B353019 : Blo 350755 353019 := bstep (se 1 (by rfl) ⟨264764, by rfl⟩ : syracuseStep 353019 = 529529) B529529
theorem B353519 : Blo 350755 353519 := bstep (se 1 (by rfl) ⟨265139, by rfl⟩ : syracuseStep 353519 = 530279) B530279
theorem B353639 : Blo 350755 353639 := bstep (se 1 (by rfl) ⟨265229, by rfl⟩ : syracuseStep 353639 = 530459) B530459
theorem B7628393 : Blo 350755 7628393 := bstep (se 2 (by rfl) ⟨2860647, by rfl⟩ : syracuseStep 7628393 = 5721295) B5721295
theorem B1009871 : Blo 350755 1009871 := bstep (se 1 (by rfl) ⟨757403, by rfl⟩ : syracuseStep 1009871 = 1514807) B1514807
theorem B354535 : Blo 350755 354535 := bstep (se 1 (by rfl) ⟨265901, by rfl⟩ : syracuseStep 354535 = 531803) B531803
theorem B354715 : Blo 350755 354715 := bstep (se 1 (by rfl) ⟨266036, by rfl⟩ : syracuseStep 354715 = 532073) B532073
theorem B113437745 : Blo 350755 113437745 := bstep (se 2 (by rfl) ⟨42539154, by rfl⟩ : syracuseStep 113437745 = 85078309) B85078309
theorem B1341467 : Blo 350755 1341467 := bstep (se 1 (by rfl) ⟨1006100, by rfl⟩ : syracuseStep 1341467 = 2012201) B2012201
theorem B752807 : Blo 350755 752807 := bstep (se 1 (by rfl) ⟨564605, by rfl⟩ : syracuseStep 752807 = 1129211) B1129211
theorem B1015915 : Blo 350755 1015915 := bstep (se 1 (by rfl) ⟨761936, by rfl⟩ : syracuseStep 1015915 = 1523873) B1523873
theorem B14549381 : Blo 350755 14549381 := bstep (se 4 (by rfl) ⟨1364004, by rfl⟩ : syracuseStep 14549381 = 2728009) B2728009
theorem B754849 : Blo 350755 754849 := bstep (se 2 (by rfl) ⟨283068, by rfl⟩ : syracuseStep 754849 = 566137) B566137
theorem B41714941 : Blo 350755 41714941 := bstep (se 3 (by rfl) ⟨7821551, by rfl⟩ : syracuseStep 41714941 = 15643103) B15643103
theorem B526427 : Blo 350755 526427 := bstep (se 1 (by rfl) ⟨394820, by rfl⟩ : syracuseStep 526427 = 789641) B789641
theorem B527039 : Blo 350755 527039 := bstep (se 1 (by rfl) ⟨395279, by rfl⟩ : syracuseStep 527039 = 790559) B790559
theorem B527771 : Blo 350755 527771 := bstep (se 1 (by rfl) ⟨395828, by rfl⟩ : syracuseStep 527771 = 791657) B791657
theorem B528761 : Blo 350755 528761 := bstep (se 2 (by rfl) ⟨198285, by rfl⟩ : syracuseStep 528761 = 396571) B396571
theorem B529691 : Blo 350755 529691 := bstep (se 1 (by rfl) ⟨397268, by rfl⟩ : syracuseStep 529691 = 794537) B794537
theorem B4593023 : Blo 350755 4593023 := bstep (se 1 (by rfl) ⟨3444767, by rfl⟩ : syracuseStep 4593023 = 6889535) B6889535
theorem B530639 : Blo 350755 530639 := bstep (se 1 (by rfl) ⟨397979, by rfl⟩ : syracuseStep 530639 = 795959) B795959
theorem B5085595 : Blo 350755 5085595 := bstep (se 1 (by rfl) ⟨3814196, by rfl⟩ : syracuseStep 5085595 = 7628393) B7628393
theorem B530927 : Blo 350755 530927 := bstep (se 1 (by rfl) ⟨398195, by rfl⟩ : syracuseStep 530927 = 796391) B796391
theorem B596639 : Blo 350755 596639 := bstep (se 1 (by rfl) ⟨447479, by rfl⟩ : syracuseStep 596639 = 894959) B894959
theorem B3809663 : Blo 350755 3809663 := bstep (se 1 (by rfl) ⟨2857247, by rfl⟩ : syracuseStep 3809663 = 5714495) B5714495
theorem B11477375 : Blo 350755 11477375 := bstep (se 1 (by rfl) ⟨8608031, by rfl⟩ : syracuseStep 11477375 = 17216063) B17216063
theorem B31072691 : Blo 350755 31072691 := bstep (se 1 (by rfl) ⟨23304518, by rfl⟩ : syracuseStep 31072691 = 46609037) B46609037
theorem B893825 : Blo 350755 893825 := bstep (se 2 (by rfl) ⟨335184, by rfl⟩ : syracuseStep 893825 = 670369) B670369
theorem B5088365 : Blo 350755 5088365 := bstep (se 3 (by rfl) ⟨954068, by rfl⟩ : syracuseStep 5088365 = 1908137) B1908137
theorem B894311 : Blo 350755 894311 := bstep (se 1 (by rfl) ⟨670733, by rfl⟩ : syracuseStep 894311 = 1341467) B1341467
theorem B501871 : Blo 350755 501871 := bstep (se 1 (by rfl) ⟨376403, by rfl⟩ : syracuseStep 501871 = 752807) B752807
theorem B4532831 : Blo 350755 4532831 := bstep (se 1 (by rfl) ⟨3399623, by rfl⟩ : syracuseStep 4532831 = 6799247) B6799247
theorem B797435 : Blo 350755 797435 := bstep (se 1 (by rfl) ⟨598076, by rfl⟩ : syracuseStep 797435 = 1196153) B1196153
theorem B535643 : Blo 350755 535643 := bstep (se 1 (by rfl) ⟨401732, by rfl⟩ : syracuseStep 535643 = 803465) B803465
theorem B31075811 : Blo 350755 31075811 := bstep (se 1 (by rfl) ⟨23306858, by rfl⟩ : syracuseStep 31075811 = 46613717) B46613717
theorem B2535623 : Blo 350755 2535623 := bstep (se 1 (by rfl) ⟨1901717, by rfl⟩ : syracuseStep 2535623 = 3803435) B3803435
theorem B504559 : Blo 350755 504559 := bstep (se 1 (by rfl) ⟨378419, by rfl⟩ : syracuseStep 504559 = 756839) B756839
theorem B6009875 : Blo 350755 6009875 := bstep (se 1 (by rfl) ⟨4507406, by rfl⟩ : syracuseStep 6009875 = 9014813) B9014813
theorem B9122867 : Blo 350755 9122867 := bstep (se 1 (by rfl) ⟨6842150, by rfl⟩ : syracuseStep 9122867 = 13684301) B13684301
theorem B669055 : Blo 350755 669055 := bstep (se 1 (by rfl) ⟨501791, by rfl⟩ : syracuseStep 669055 = 1003583) B1003583
theorem B5748803 : Blo 350755 5748803 := bstep (se 1 (by rfl) ⟨4311602, by rfl⟩ : syracuseStep 5748803 = 8623205) B8623205
theorem B1426045 : Blo 350755 1426045 := bstep (se 3 (by rfl) ⟨267383, by rfl⟩ : syracuseStep 1426045 = 534767) B534767
theorem B17712229 : Blo 350755 17712229 := bstep (se 4 (by rfl) ⟨1660521, by rfl⟩ : syracuseStep 17712229 = 3321043) B3321043
theorem B673247 : Blo 350755 673247 := bstep (se 1 (by rfl) ⟨504935, by rfl⟩ : syracuseStep 673247 = 1009871) B1009871
theorem B5852645 : Blo 350755 5852645 := bstep (se 4 (by rfl) ⟨548685, by rfl⟩ : syracuseStep 5852645 = 1097371) B1097371
theorem B350831 : Blo 350755 350831 := bstep (se 1 (by rfl) ⟨263123, by rfl⟩ : syracuseStep 350831 = 526247) B526247
theorem B19225295 : Blo 350755 19225295 := bstep (se 1 (by rfl) ⟨14418971, by rfl⟩ : syracuseStep 19225295 = 28837943) B28837943
theorem B350959 : Blo 350755 350959 := bstep (se 1 (by rfl) ⟨263219, by rfl⟩ : syracuseStep 350959 = 526439) B526439
theorem B10149047 : Blo 350755 10149047 := bstep (se 1 (by rfl) ⟨7611785, by rfl⟩ : syracuseStep 10149047 = 15223571) B15223571
theorem B679147 : Blo 350755 679147 := bstep (se 1 (by rfl) ⟨509360, by rfl⟩ : syracuseStep 679147 = 1018721) B1018721
theorem B1203881 : Blo 350755 1203881 := bstep (se 2 (by rfl) ⟨451455, by rfl⟩ : syracuseStep 1203881 = 902911) B902911
theorem B352367 : Blo 350755 352367 := bstep (se 1 (by rfl) ⟨264275, by rfl⟩ : syracuseStep 352367 = 528551) B528551
theorem B1795283 : Blo 350755 1795283 := bstep (se 1 (by rfl) ⟨1346462, by rfl⟩ : syracuseStep 1795283 = 2692925) B2692925
theorem B3794309 : Blo 350755 3794309 := bstep (se 4 (by rfl) ⟨355716, by rfl⟩ : syracuseStep 3794309 = 711433) B711433
theorem B353919 : Blo 350755 353919 := bstep (se 1 (by rfl) ⟨265439, by rfl⟩ : syracuseStep 353919 = 530879) B530879
theorem B1140905 : Blo 350755 1140905 := bstep (se 2 (by rfl) ⟨427839, by rfl⟩ : syracuseStep 1140905 = 855679) B855679
theorem B30469283 : Blo 350755 30469283 := bstep (se 1 (by rfl) ⟨22851962, by rfl⟩ : syracuseStep 30469283 = 45703925) B45703925
theorem B75625163 : Blo 350755 75625163 := bstep (se 1 (by rfl) ⟨56718872, by rfl⟩ : syracuseStep 75625163 = 113437745) B113437745
theorem B1341481 : Blo 350755 1341481 := bstep (se 2 (by rfl) ⟨503055, by rfl⟩ : syracuseStep 1341481 = 1006111) B1006111
theorem B2259035 : Blo 350755 2259035 := bstep (se 1 (by rfl) ⟨1694276, by rfl⟩ : syracuseStep 2259035 = 3388553) B3388553
theorem B3833401 : Blo 350755 3833401 := bstep (se 2 (by rfl) ⟨1437525, by rfl⟩ : syracuseStep 3833401 = 2875051) B2875051
theorem B9699587 : Blo 350755 9699587 := bstep (se 1 (by rfl) ⟨7274690, by rfl⟩ : syracuseStep 9699587 = 14549381) B14549381
theorem B1901393 : Blo 350755 1901393 := bstep (se 2 (by rfl) ⟨713022, by rfl⟩ : syracuseStep 1901393 = 1426045) B1426045
theorem B3901763 : Blo 350755 3901763 := bstep (se 1 (by rfl) ⟨2926322, by rfl⟩ : syracuseStep 3901763 = 5852645) B5852645
theorem B2690981 : Blo 350755 2690981 := bstep (se 4 (by rfl) ⟨252279, by rfl⟩ : syracuseStep 2690981 = 504559) B504559
theorem B397759 : Blo 350755 397759 := bstep (se 1 (by rfl) ⟨298319, by rfl⟩ : syracuseStep 397759 = 596639) B596639
theorem B12816863 : Blo 350755 12816863 := bstep (se 1 (by rfl) ⟨9612647, by rfl⟩ : syracuseStep 12816863 = 19225295) B19225295
theorem B595883 : Blo 350755 595883 := bstep (se 1 (by rfl) ⟨446912, by rfl⟩ : syracuseStep 595883 = 893825) B893825
theorem B596207 : Blo 350755 596207 := bstep (se 1 (by rfl) ⟨447155, by rfl⟩ : syracuseStep 596207 = 894311) B894311
theorem B2529539 : Blo 350755 2529539 := bstep (se 1 (by rfl) ⟨1897154, by rfl⟩ : syracuseStep 2529539 = 3794309) B3794309
theorem B760603 : Blo 350755 760603 := bstep (se 1 (by rfl) ⟨570452, by rfl⟩ : syracuseStep 760603 = 1140905) B1140905
theorem B3021887 : Blo 350755 3021887 := bstep (se 1 (by rfl) ⟨2266415, by rfl⟩ : syracuseStep 3021887 = 4532831) B4532831
theorem B531623 : Blo 350755 531623 := bstep (se 1 (by rfl) ⟨398717, by rfl⟩ : syracuseStep 531623 = 797435) B797435
theorem B892073 : Blo 350755 892073 := bstep (se 2 (by rfl) ⟨334527, by rfl⟩ : syracuseStep 892073 = 669055) B669055
theorem B20717207 : Blo 350755 20717207 := bstep (se 1 (by rfl) ⟨15537905, by rfl⟩ : syracuseStep 20717207 = 31075811) B31075811
theorem B4006583 : Blo 350755 4006583 := bstep (se 1 (by rfl) ⟨3004937, by rfl⟩ : syracuseStep 4006583 = 6009875) B6009875
theorem B1354553 : Blo 350755 1354553 := bstep (se 2 (by rfl) ⟨507957, by rfl⟩ : syracuseStep 1354553 = 1015915) B1015915
theorem B55619921 : Blo 350755 55619921 := bstep (se 2 (by rfl) ⟨20857470, by rfl⟩ : syracuseStep 55619921 = 41714941) B41714941
theorem B669161 : Blo 350755 669161 := bstep (se 2 (by rfl) ⟨250935, by rfl⟩ : syracuseStep 669161 = 501871) B501871
theorem B3062015 : Blo 350755 3062015 := bstep (se 1 (by rfl) ⟨2296511, by rfl⟩ : syracuseStep 3062015 = 4593023) B4593023
theorem B6766031 : Blo 350755 6766031 := bstep (se 1 (by rfl) ⟨5074523, by rfl⟩ : syracuseStep 6766031 = 10149047) B10149047
theorem B2539775 : Blo 350755 2539775 := bstep (se 1 (by rfl) ⟨1904831, by rfl⟩ : syracuseStep 2539775 = 3809663) B3809663
theorem B7651583 : Blo 350755 7651583 := bstep (se 1 (by rfl) ⟨5738687, by rfl⟩ : syracuseStep 7651583 = 11477375) B11477375
theorem B3392243 : Blo 350755 3392243 := bstep (se 1 (by rfl) ⟨2544182, by rfl⟩ : syracuseStep 3392243 = 5088365) B5088365
theorem B1196855 : Blo 350755 1196855 := bstep (se 1 (by rfl) ⟨897641, by rfl⟩ : syracuseStep 1196855 = 1795283) B1795283
theorem B3622117 : Blo 350755 3622117 := bstep (se 4 (by rfl) ⟨339573, by rfl⟩ : syracuseStep 3622117 = 679147) B679147
theorem B1788641 : Blo 350755 1788641 := bstep (se 2 (by rfl) ⟨670740, by rfl⟩ : syracuseStep 1788641 = 1341481) B1341481
theorem B1690415 : Blo 350755 1690415 := bstep (se 1 (by rfl) ⟨1267811, by rfl⟩ : syracuseStep 1690415 = 2535623) B2535623
theorem B50416775 : Blo 350755 50416775 := bstep (se 1 (by rfl) ⟨37812581, by rfl⟩ : syracuseStep 50416775 = 75625163) B75625163
theorem B6081911 : Blo 350755 6081911 := bstep (se 1 (by rfl) ⟨4561433, by rfl⟩ : syracuseStep 6081911 = 9122867) B9122867
theorem B448831 : Blo 350755 448831 := bstep (se 1 (by rfl) ⟨336623, by rfl⟩ : syracuseStep 448831 = 673247) B673247
theorem B82860509 : Blo 350755 82860509 := bstep (se 3 (by rfl) ⟨15536345, by rfl⟩ : syracuseStep 82860509 = 31072691) B31072691
theorem B350951 : Blo 350755 350951 := bstep (se 1 (by rfl) ⟨263213, by rfl⟩ : syracuseStep 350951 = 526427) B526427
theorem B23616305 : Blo 350755 23616305 := bstep (se 2 (by rfl) ⟨8856114, by rfl⟩ : syracuseStep 23616305 = 17712229) B17712229
theorem B1006465 : Blo 350755 1006465 := bstep (se 2 (by rfl) ⟨377424, by rfl⟩ : syracuseStep 1006465 = 754849) B754849
theorem B351359 : Blo 350755 351359 := bstep (se 1 (by rfl) ⟨263519, by rfl⟩ : syracuseStep 351359 = 527039) B527039
theorem B351847 : Blo 350755 351847 := bstep (se 1 (by rfl) ⟨263885, by rfl⟩ : syracuseStep 351847 = 527771) B527771
theorem B352507 : Blo 350755 352507 := bstep (se 1 (by rfl) ⟨264380, by rfl⟩ : syracuseStep 352507 = 528761) B528761
theorem B353127 : Blo 350755 353127 := bstep (se 1 (by rfl) ⟨264845, by rfl⟩ : syracuseStep 353127 = 529691) B529691
theorem B353759 : Blo 350755 353759 := bstep (se 1 (by rfl) ⟨265319, by rfl⟩ : syracuseStep 353759 = 530639) B530639
theorem B353951 : Blo 350755 353951 := bstep (se 1 (by rfl) ⟨265463, by rfl⟩ : syracuseStep 353951 = 530927) B530927
theorem B357095 : Blo 350755 357095 := bstep (se 1 (by rfl) ⟨267821, by rfl⟩ : syracuseStep 357095 = 535643) B535643
theorem B20312855 : Blo 350755 20312855 := bstep (se 1 (by rfl) ⟨15234641, by rfl⟩ : syracuseStep 20312855 = 30469283) B30469283
theorem B6780793 : Blo 350755 6780793 := bstep (se 2 (by rfl) ⟨2542797, by rfl⟩ : syracuseStep 6780793 = 5085595) B5085595
theorem B3832535 : Blo 350755 3832535 := bstep (se 1 (by rfl) ⟨2874401, by rfl⟩ : syracuseStep 3832535 = 5748803) B5748803
theorem B1506023 : Blo 350755 1506023 := bstep (se 1 (by rfl) ⟨1129517, by rfl⟩ : syracuseStep 1506023 = 2259035) B2259035
theorem B3210349 : Blo 350755 3210349 := bstep (se 3 (by rfl) ⟨601940, by rfl⟩ : syracuseStep 3210349 = 1203881) B1203881
theorem B5111201 : Blo 350755 5111201 := bstep (se 2 (by rfl) ⟨1916700, by rfl⟩ : syracuseStep 5111201 = 3833401) B3833401
theorem B2261495 : Blo 350755 2261495 := bstep (se 1 (by rfl) ⟨1696121, by rfl⟩ : syracuseStep 2261495 = 3392243) B3392243
theorem B952253 : Blo 350755 952253 := bstep (se 3 (by rfl) ⟨178547, by rfl⟩ : syracuseStep 952253 = 357095) B357095
theorem B397255 : Blo 350755 397255 := bstep (se 1 (by rfl) ⟨297941, by rfl⟩ : syracuseStep 397255 = 595883) B595883
theorem B397471 : Blo 350755 397471 := bstep (se 1 (by rfl) ⟨298103, by rfl⟩ : syracuseStep 397471 = 596207) B596207
theorem B594715 : Blo 350755 594715 := bstep (se 1 (by rfl) ⟨446036, by rfl⟩ : syracuseStep 594715 = 892073) B892073
theorem B530345 : Blo 350755 530345 := bstep (se 2 (by rfl) ⟨198879, by rfl⟩ : syracuseStep 530345 = 397759) B397759
theorem B598441 : Blo 350755 598441 := bstep (se 2 (by rfl) ⟨224415, by rfl⟩ : syracuseStep 598441 = 448831) B448831
theorem B13541903 : Blo 350755 13541903 := bstep (se 1 (by rfl) ⟨10156427, by rfl⟩ : syracuseStep 13541903 = 20312855) B20312855
theorem B2041343 : Blo 350755 2041343 := bstep (se 1 (by rfl) ⟨1531007, by rfl⟩ : syracuseStep 2041343 = 3062015) B3062015
theorem B6466391 : Blo 350755 6466391 := bstep (se 1 (by rfl) ⟨4849793, by rfl⟩ : syracuseStep 6466391 = 9699587) B9699587
theorem B797903 : Blo 350755 797903 := bstep (se 1 (by rfl) ⟨598427, by rfl⟩ : syracuseStep 797903 = 1196855) B1196855
theorem B2601175 : Blo 350755 2601175 := bstep (se 1 (by rfl) ⟨1950881, by rfl⟩ : syracuseStep 2601175 = 3901763) B3901763
theorem B4829489 : Blo 350755 4829489 := bstep (se 2 (by rfl) ⟨1811058, by rfl⟩ : syracuseStep 4829489 = 3622117) B3622117
theorem B1192427 : Blo 350755 1192427 := bstep (se 1 (by rfl) ⟨894320, by rfl⟩ : syracuseStep 1192427 = 1788641) B1788641
theorem B1126943 : Blo 350755 1126943 := bstep (se 1 (by rfl) ⟨845207, by rfl⟩ : syracuseStep 1126943 = 1690415) B1690415
theorem B1784429 : Blo 350755 1784429 := bstep (se 3 (by rfl) ⟨334580, by rfl⟩ : syracuseStep 1784429 = 669161) B669161
theorem B1686359 : Blo 350755 1686359 := bstep (se 1 (by rfl) ⟨1264769, by rfl⟩ : syracuseStep 1686359 = 2529539) B2529539
theorem B15744203 : Blo 350755 15744203 := bstep (se 1 (by rfl) ⟨11808152, by rfl⟩ : syracuseStep 15744203 = 23616305) B23616305
theorem B2014591 : Blo 350755 2014591 := bstep (se 1 (by rfl) ⟨1510943, by rfl⟩ : syracuseStep 2014591 = 3021887) B3021887
theorem B13811471 : Blo 350755 13811471 := bstep (se 1 (by rfl) ⟨10358603, by rfl⟩ : syracuseStep 13811471 = 20717207) B20717207
theorem B2671055 : Blo 350755 2671055 := bstep (se 1 (by rfl) ⟨2003291, by rfl⟩ : syracuseStep 2671055 = 4006583) B4006583
theorem B903035 : Blo 350755 903035 := bstep (se 1 (by rfl) ⟨677276, by rfl⟩ : syracuseStep 903035 = 1354553) B1354553
theorem B37079947 : Blo 350755 37079947 := bstep (se 1 (by rfl) ⟨27809960, by rfl⟩ : syracuseStep 37079947 = 55619921) B55619921
theorem B4280465 : Blo 350755 4280465 := bstep (se 2 (by rfl) ⟨1605174, by rfl⟩ : syracuseStep 4280465 = 3210349) B3210349
theorem B1004015 : Blo 350755 1004015 := bstep (se 1 (by rfl) ⟨753011, by rfl⟩ : syracuseStep 1004015 = 1506023) B1506023
theorem B4510687 : Blo 350755 4510687 := bstep (se 1 (by rfl) ⟨3383015, by rfl⟩ : syracuseStep 4510687 = 6766031) B6766031
theorem B1693183 : Blo 350755 1693183 := bstep (se 1 (by rfl) ⟨1269887, by rfl⟩ : syracuseStep 1693183 = 2539775) B2539775
theorem B5101055 : Blo 350755 5101055 := bstep (se 1 (by rfl) ⟨3825791, by rfl⟩ : syracuseStep 5101055 = 7651583) B7651583
theorem B1267595 : Blo 350755 1267595 := bstep (se 1 (by rfl) ⟨950696, by rfl⟩ : syracuseStep 1267595 = 1901393) B1901393
theorem B33611183 : Blo 350755 33611183 := bstep (se 1 (by rfl) ⟨25208387, by rfl⟩ : syracuseStep 33611183 = 50416775) B50416775
theorem B4054607 : Blo 350755 4054607 := bstep (se 1 (by rfl) ⟨3040955, by rfl⟩ : syracuseStep 4054607 = 6081911) B6081911
theorem B1793987 : Blo 350755 1793987 := bstep (se 1 (by rfl) ⟨1345490, by rfl⟩ : syracuseStep 1793987 = 2690981) B2690981
theorem B8544575 : Blo 350755 8544575 := bstep (se 1 (by rfl) ⟨6408431, by rfl⟩ : syracuseStep 8544575 = 12816863) B12816863
theorem B55240339 : Blo 350755 55240339 := bstep (se 1 (by rfl) ⟨41430254, by rfl⟩ : syracuseStep 55240339 = 82860509) B82860509
theorem B354415 : Blo 350755 354415 := bstep (se 1 (by rfl) ⟨265811, by rfl⟩ : syracuseStep 354415 = 531623) B531623
theorem B10220093 : Blo 350755 10220093 := bstep (se 3 (by rfl) ⟨1916267, by rfl⟩ : syracuseStep 10220093 = 3832535) B3832535
theorem B9041057 : Blo 350755 9041057 := bstep (se 2 (by rfl) ⟨3390396, by rfl⟩ : syracuseStep 9041057 = 6780793) B6780793
theorem B1014137 : Blo 350755 1014137 := bstep (se 2 (by rfl) ⟨380301, by rfl⟩ : syracuseStep 1014137 = 760603) B760603
theorem B1341953 : Blo 350755 1341953 := bstep (se 2 (by rfl) ⟨503232, by rfl⟩ : syracuseStep 1341953 = 1006465) B1006465
theorem B3407467 : Blo 350755 3407467 := bstep (se 1 (by rfl) ⟨2555600, by rfl⟩ : syracuseStep 3407467 = 5111201) B5111201
theorem B1507663 : Blo 350755 1507663 := bstep (se 1 (by rfl) ⟨1130747, by rfl⟩ : syracuseStep 1507663 = 2261495) B2261495
theorem B2853643 : Blo 350755 2853643 := bstep (se 1 (by rfl) ⟨2140232, by rfl⟩ : syracuseStep 2853643 = 4280465) B4280465
theorem B197759717 : Blo 350755 197759717 := bstep (se 4 (by rfl) ⟨18539973, by rfl⟩ : syracuseStep 197759717 = 37079947) B37079947
theorem B529673 : Blo 350755 529673 := bstep (se 2 (by rfl) ⟨198627, by rfl⟩ : syracuseStep 529673 = 397255) B397255
theorem B529961 : Blo 350755 529961 := bstep (se 2 (by rfl) ⟨198735, by rfl⟩ : syracuseStep 529961 = 397471) B397471
theorem B792953 : Blo 350755 792953 := bstep (se 2 (by rfl) ⟨297357, by rfl⟩ : syracuseStep 792953 = 594715) B594715
theorem B531935 : Blo 350755 531935 := bstep (se 1 (by rfl) ⟨398951, by rfl⟩ : syracuseStep 531935 = 797903) B797903
theorem B3219659 : Blo 350755 3219659 := bstep (se 1 (by rfl) ⟨2414744, by rfl⟩ : syracuseStep 3219659 = 4829489) B4829489
theorem B794951 : Blo 350755 794951 := bstep (se 1 (by rfl) ⟨596213, by rfl⟩ : syracuseStep 794951 = 1192427) B1192427
theorem B894635 : Blo 350755 894635 := bstep (se 1 (by rfl) ⟨670976, by rfl⟩ : syracuseStep 894635 = 1341953) B1341953
theorem B1189619 : Blo 350755 1189619 := bstep (se 1 (by rfl) ⟨892214, by rfl⟩ : syracuseStep 1189619 = 1784429) B1784429
theorem B1124239 : Blo 350755 1124239 := bstep (se 1 (by rfl) ⟨843179, by rfl⟩ : syracuseStep 1124239 = 1686359) B1686359
theorem B10496135 : Blo 350755 10496135 := bstep (se 1 (by rfl) ⟨7872101, by rfl⟩ : syracuseStep 10496135 = 15744203) B15744203
theorem B1780703 : Blo 350755 1780703 := bstep (se 1 (by rfl) ⟨1335527, by rfl⟩ : syracuseStep 1780703 = 2671055) B2671055
theorem B797921 : Blo 350755 797921 := bstep (se 2 (by rfl) ⟨299220, by rfl⟩ : syracuseStep 797921 = 598441) B598441
theorem B22785533 : Blo 350755 22785533 := bstep (se 3 (by rfl) ⟨4272287, by rfl⟩ : syracuseStep 22785533 = 8544575) B8544575
theorem B602023 : Blo 350755 602023 := bstep (se 1 (by rfl) ⟨451517, by rfl⟩ : syracuseStep 602023 = 903035) B903035
theorem B634835 : Blo 350755 634835 := bstep (se 1 (by rfl) ⟨476126, by rfl⟩ : syracuseStep 634835 = 952253) B952253
theorem B2703071 : Blo 350755 2703071 := bstep (se 1 (by rfl) ⟨2027303, by rfl⟩ : syracuseStep 2703071 = 4054607) B4054607
theorem B1195991 : Blo 350755 1195991 := bstep (se 1 (by rfl) ⟨896993, by rfl⟩ : syracuseStep 1195991 = 1793987) B1793987
theorem B9027935 : Blo 350755 9027935 := bstep (se 1 (by rfl) ⟨6770951, by rfl⟩ : syracuseStep 9027935 = 13541903) B13541903
theorem B1360895 : Blo 350755 1360895 := bstep (se 1 (by rfl) ⟨1020671, by rfl⟩ : syracuseStep 1360895 = 2041343) B2041343
theorem B6014249 : Blo 350755 6014249 := bstep (se 2 (by rfl) ⟨2255343, by rfl⟩ : syracuseStep 6014249 = 4510687) B4510687
theorem B4310927 : Blo 350755 4310927 := bstep (se 1 (by rfl) ⟨3233195, by rfl⟩ : syracuseStep 4310927 = 6466391) B6466391
theorem B676091 : Blo 350755 676091 := bstep (se 1 (by rfl) ⟨507068, by rfl⟩ : syracuseStep 676091 = 1014137) B1014137
theorem B4543289 : Blo 350755 4543289 := bstep (se 2 (by rfl) ⟨1703733, by rfl⟩ : syracuseStep 4543289 = 3407467) B3407467
theorem B2677373 : Blo 350755 2677373 := bstep (se 3 (by rfl) ⟨502007, by rfl⟩ : syracuseStep 2677373 = 1004015) B1004015
theorem B73653785 : Blo 350755 73653785 := bstep (se 2 (by rfl) ⟨27620169, by rfl⟩ : syracuseStep 73653785 = 55240339) B55240339
theorem B3400703 : Blo 350755 3400703 := bstep (se 1 (by rfl) ⟨2550527, by rfl⟩ : syracuseStep 3400703 = 5101055) B5101055
theorem B845063 : Blo 350755 845063 := bstep (se 1 (by rfl) ⟨633797, by rfl⟩ : syracuseStep 845063 = 1267595) B1267595
theorem B353563 : Blo 350755 353563 := bstep (se 1 (by rfl) ⟨265172, by rfl⟩ : syracuseStep 353563 = 530345) B530345
theorem B22407455 : Blo 350755 22407455 := bstep (se 1 (by rfl) ⟨16805591, by rfl⟩ : syracuseStep 22407455 = 33611183) B33611183
theorem B3468233 : Blo 350755 3468233 := bstep (se 2 (by rfl) ⟨1300587, by rfl⟩ : syracuseStep 3468233 = 2601175) B2601175
theorem B2257577 : Blo 350755 2257577 := bstep (se 2 (by rfl) ⟨846591, by rfl⟩ : syracuseStep 2257577 = 1693183) B1693183
theorem B751295 : Blo 350755 751295 := bstep (se 1 (by rfl) ⟨563471, by rfl⟩ : syracuseStep 751295 = 1126943) B1126943
theorem B6813395 : Blo 350755 6813395 := bstep (se 1 (by rfl) ⟨5110046, by rfl⟩ : syracuseStep 6813395 = 10220093) B10220093
theorem B6027371 : Blo 350755 6027371 := bstep (se 1 (by rfl) ⟨4520528, by rfl⟩ : syracuseStep 6027371 = 9041057) B9041057
theorem B2686121 : Blo 350755 2686121 := bstep (se 2 (by rfl) ⟨1007295, by rfl⟩ : syracuseStep 2686121 = 2014591) B2014591
theorem B9207647 : Blo 350755 9207647 := bstep (se 1 (by rfl) ⟨6905735, by rfl⟩ : syracuseStep 9207647 = 13811471) B13811471
theorem B3804857 : Blo 350755 3804857 := bstep (se 2 (by rfl) ⟨1426821, by rfl⟩ : syracuseStep 3804857 = 2853643) B2853643
theorem B528635 : Blo 350755 528635 := bstep (se 1 (by rfl) ⟨396476, by rfl⟩ : syracuseStep 528635 = 792953) B792953
theorem B2003453 : Blo 350755 2003453 := bstep (se 3 (by rfl) ⟨375647, by rfl⟩ : syracuseStep 2003453 = 751295) B751295
theorem B529967 : Blo 350755 529967 := bstep (se 1 (by rfl) ⟨397475, by rfl⟩ : syracuseStep 529967 = 794951) B794951
theorem B2267135 : Blo 350755 2267135 := bstep (se 1 (by rfl) ⟨1700351, by rfl⟩ : syracuseStep 2267135 = 3400703) B3400703
theorem B563375 : Blo 350755 563375 := bstep (se 1 (by rfl) ⟨422531, by rfl⟩ : syracuseStep 563375 = 845063) B845063
theorem B596423 : Blo 350755 596423 := bstep (se 1 (by rfl) ⟨447317, by rfl⟩ : syracuseStep 596423 = 894635) B894635
theorem B793079 : Blo 350755 793079 := bstep (se 1 (by rfl) ⟨594809, by rfl⟩ : syracuseStep 793079 = 1189619) B1189619
theorem B1187135 : Blo 350755 1187135 := bstep (se 1 (by rfl) ⟨890351, by rfl⟩ : syracuseStep 1187135 = 1780703) B1780703
theorem B531947 : Blo 350755 531947 := bstep (se 1 (by rfl) ⟨398960, by rfl⟩ : syracuseStep 531947 = 797921) B797921
theorem B6138431 : Blo 350755 6138431 := bstep (se 1 (by rfl) ⟨4603823, by rfl⟩ : syracuseStep 6138431 = 9207647) B9207647
theorem B797327 : Blo 350755 797327 := bstep (se 1 (by rfl) ⟨597995, by rfl⟩ : syracuseStep 797327 = 1195991) B1195991
theorem B2010217 : Blo 350755 2010217 := bstep (se 2 (by rfl) ⟨753831, by rfl⟩ : syracuseStep 2010217 = 1507663) B1507663
theorem B4009499 : Blo 350755 4009499 := bstep (se 1 (by rfl) ⟨3007124, by rfl⟩ : syracuseStep 4009499 = 6014249) B6014249
theorem B131839811 : Blo 350755 131839811 := bstep (se 1 (by rfl) ⟨98879858, by rfl⟩ : syracuseStep 131839811 = 197759717) B197759717
theorem B3028859 : Blo 350755 3028859 := bstep (se 1 (by rfl) ⟨2271644, by rfl⟩ : syracuseStep 3028859 = 4543289) B4543289
theorem B1784915 : Blo 350755 1784915 := bstep (se 1 (by rfl) ⟨1338686, by rfl⟩ : syracuseStep 1784915 = 2677373) B2677373
theorem B49102523 : Blo 350755 49102523 := bstep (se 1 (by rfl) ⟨36826892, by rfl⟩ : syracuseStep 49102523 = 73653785) B73653785
theorem B2146439 : Blo 350755 2146439 := bstep (se 1 (by rfl) ⟨1609829, by rfl⟩ : syracuseStep 2146439 = 3219659) B3219659
theorem B59753213 : Blo 350755 59753213 := bstep (se 3 (by rfl) ⟨11203727, by rfl⟩ : syracuseStep 59753213 = 22407455) B22407455
theorem B6997423 : Blo 350755 6997423 := bstep (se 1 (by rfl) ⟨5248067, by rfl⟩ : syracuseStep 6997423 = 10496135) B10496135
theorem B2312155 : Blo 350755 2312155 := bstep (se 1 (by rfl) ⟨1734116, by rfl⟩ : syracuseStep 2312155 = 3468233) B3468233
theorem B15190355 : Blo 350755 15190355 := bstep (se 1 (by rfl) ⟨11392766, by rfl⟩ : syracuseStep 15190355 = 22785533) B22785533
theorem B4542263 : Blo 350755 4542263 := bstep (se 1 (by rfl) ⟨3406697, by rfl⟩ : syracuseStep 4542263 = 6813395) B6813395
theorem B4018247 : Blo 350755 4018247 := bstep (se 1 (by rfl) ⟨3013685, by rfl⟩ : syracuseStep 4018247 = 6027371) B6027371
theorem B1790747 : Blo 350755 1790747 := bstep (se 1 (by rfl) ⟨1343060, by rfl⟩ : syracuseStep 1790747 = 2686121) B2686121
theorem B1692893 : Blo 350755 1692893 := bstep (se 3 (by rfl) ⟨317417, by rfl⟩ : syracuseStep 1692893 = 634835) B634835
theorem B6018623 : Blo 350755 6018623 := bstep (se 1 (by rfl) ⟨4513967, by rfl⟩ : syracuseStep 6018623 = 9027935) B9027935
theorem B2873951 : Blo 350755 2873951 := bstep (se 1 (by rfl) ⟨2155463, by rfl⟩ : syracuseStep 2873951 = 4310927) B4310927
theorem B1498985 : Blo 350755 1498985 := bstep (se 2 (by rfl) ⟨562119, by rfl⟩ : syracuseStep 1498985 = 1124239) B1124239
theorem B3629053 : Blo 350755 3629053 := bstep (se 3 (by rfl) ⟨680447, by rfl⟩ : syracuseStep 3629053 = 1360895) B1360895
theorem B450727 : Blo 350755 450727 := bstep (se 1 (by rfl) ⟨338045, by rfl⟩ : syracuseStep 450727 = 676091) B676091
theorem B353115 : Blo 350755 353115 := bstep (se 1 (by rfl) ⟨264836, by rfl⟩ : syracuseStep 353115 = 529673) B529673
theorem B353307 : Blo 350755 353307 := bstep (se 1 (by rfl) ⟨264980, by rfl⟩ : syracuseStep 353307 = 529961) B529961
theorem B354623 : Blo 350755 354623 := bstep (se 1 (by rfl) ⟨265967, by rfl⟩ : syracuseStep 354623 = 531935) B531935
theorem B1505051 : Blo 350755 1505051 := bstep (se 1 (by rfl) ⟨1128788, by rfl⟩ : syracuseStep 1505051 = 2257577) B2257577
theorem B12843157 : Blo 350755 12843157 := bstep (se 6 (by rfl) ⟨301011, by rfl⟩ : syracuseStep 12843157 = 602023) B602023
theorem B1802047 : Blo 350755 1802047 := bstep (se 1 (by rfl) ⟨1351535, by rfl⟩ : syracuseStep 1802047 = 2703071) B2703071
theorem B10126903 : Blo 350755 10126903 := bstep (se 1 (by rfl) ⟨7595177, by rfl⟩ : syracuseStep 10126903 = 15190355) B15190355
theorem B3082873 : Blo 350755 3082873 := bstep (se 2 (by rfl) ⟨1156077, by rfl⟩ : syracuseStep 3082873 = 2312155) B2312155
theorem B1511423 : Blo 350755 1511423 := bstep (se 1 (by rfl) ⟨1133567, by rfl⟩ : syracuseStep 1511423 = 2267135) B2267135
theorem B397615 : Blo 350755 397615 := bstep (se 1 (by rfl) ⟨298211, by rfl⟩ : syracuseStep 397615 = 596423) B596423
theorem B528719 : Blo 350755 528719 := bstep (se 1 (by rfl) ⟨396539, by rfl⟩ : syracuseStep 528719 = 793079) B793079
theorem B791423 : Blo 350755 791423 := bstep (se 1 (by rfl) ⟨593567, by rfl⟩ : syracuseStep 791423 = 1187135) B1187135
theorem B531551 : Blo 350755 531551 := bstep (se 1 (by rfl) ⟨398663, by rfl⟩ : syracuseStep 531551 = 797327) B797327
theorem B87893207 : Blo 350755 87893207 := bstep (se 1 (by rfl) ⟨65919905, by rfl⟩ : syracuseStep 87893207 = 131839811) B131839811
theorem B1189943 : Blo 350755 1189943 := bstep (se 1 (by rfl) ⟨892457, by rfl⟩ : syracuseStep 1189943 = 1784915) B1784915
theorem B2402729 : Blo 350755 2402729 := bstep (se 2 (by rfl) ⟨901023, by rfl⟩ : syracuseStep 2402729 = 1802047) B1802047
theorem B2536571 : Blo 350755 2536571 := bstep (se 1 (by rfl) ⟨1902428, by rfl⟩ : syracuseStep 2536571 = 3804857) B3804857
theorem B3028175 : Blo 350755 3028175 := bstep (se 1 (by rfl) ⟨2271131, by rfl⟩ : syracuseStep 3028175 = 4542263) B4542263
theorem B1193831 : Blo 350755 1193831 := bstep (se 1 (by rfl) ⟨895373, by rfl⟩ : syracuseStep 1193831 = 1790747) B1790747
theorem B1128595 : Blo 350755 1128595 := bstep (se 1 (by rfl) ⟨846446, by rfl⟩ : syracuseStep 1128595 = 1692893) B1692893
theorem B9615509 : Blo 350755 9615509 := bstep (se 6 (by rfl) ⟨225363, by rfl⟩ : syracuseStep 9615509 = 450727) B450727
theorem B4012415 : Blo 350755 4012415 := bstep (se 1 (by rfl) ⟨3009311, by rfl⟩ : syracuseStep 4012415 = 6018623) B6018623
theorem B1915967 : Blo 350755 1915967 := bstep (se 1 (by rfl) ⟨1436975, by rfl⟩ : syracuseStep 1915967 = 2873951) B2873951
theorem B999323 : Blo 350755 999323 := bstep (se 1 (by rfl) ⟨749492, by rfl⟩ : syracuseStep 999323 = 1498985) B1498985
theorem B2672999 : Blo 350755 2672999 := bstep (se 1 (by rfl) ⟨2004749, by rfl⟩ : syracuseStep 2672999 = 4009499) B4009499
theorem B17124209 : Blo 350755 17124209 := bstep (se 2 (by rfl) ⟨6421578, by rfl⟩ : syracuseStep 17124209 = 12843157) B12843157
theorem B1003367 : Blo 350755 1003367 := bstep (se 1 (by rfl) ⟨752525, by rfl⟩ : syracuseStep 1003367 = 1505051) B1505051
theorem B2019239 : Blo 350755 2019239 := bstep (se 1 (by rfl) ⟨1514429, by rfl⟩ : syracuseStep 2019239 = 3028859) B3028859
theorem B4838737 : Blo 350755 4838737 := bstep (se 2 (by rfl) ⟨1814526, by rfl⟩ : syracuseStep 4838737 = 3629053) B3629053
theorem B1430959 : Blo 350755 1430959 := bstep (se 1 (by rfl) ⟨1073219, by rfl⟩ : syracuseStep 1430959 = 2146439) B2146439
theorem B39835475 : Blo 350755 39835475 := bstep (se 1 (by rfl) ⟨29876606, by rfl⟩ : syracuseStep 39835475 = 59753213) B59753213
theorem B9329897 : Blo 350755 9329897 := bstep (se 2 (by rfl) ⟨3498711, by rfl⟩ : syracuseStep 9329897 = 6997423) B6997423
theorem B2678831 : Blo 350755 2678831 := bstep (se 1 (by rfl) ⟨2009123, by rfl⟩ : syracuseStep 2678831 = 4018247) B4018247
theorem B352423 : Blo 350755 352423 := bstep (se 1 (by rfl) ⟨264317, by rfl⟩ : syracuseStep 352423 = 528635) B528635
theorem B1335635 : Blo 350755 1335635 := bstep (se 1 (by rfl) ⟨1001726, by rfl⟩ : syracuseStep 1335635 = 2003453) B2003453
theorem B353311 : Blo 350755 353311 := bstep (se 1 (by rfl) ⟨264983, by rfl⟩ : syracuseStep 353311 = 529967) B529967
theorem B2680289 : Blo 350755 2680289 := bstep (se 2 (by rfl) ⟨1005108, by rfl⟩ : syracuseStep 2680289 = 2010217) B2010217
theorem B354631 : Blo 350755 354631 := bstep (se 1 (by rfl) ⟨265973, by rfl⟩ : syracuseStep 354631 = 531947) B531947
theorem B1502333 : Blo 350755 1502333 := bstep (se 3 (by rfl) ⟨281687, by rfl⟩ : syracuseStep 1502333 = 563375) B563375
theorem B4092287 : Blo 350755 4092287 := bstep (se 1 (by rfl) ⟨3069215, by rfl⟩ : syracuseStep 4092287 = 6138431) B6138431
theorem B32735015 : Blo 350755 32735015 := bstep (se 1 (by rfl) ⟨24551261, by rfl⟩ : syracuseStep 32735015 = 49102523) B49102523
theorem B10912765 : Blo 350755 10912765 := bstep (se 3 (by rfl) ⟨2046143, by rfl⟩ : syracuseStep 10912765 = 4092287) B4092287
theorem B13502537 : Blo 350755 13502537 := bstep (se 2 (by rfl) ⟨5063451, by rfl⟩ : syracuseStep 13502537 = 10126903) B10126903
theorem B1346159 : Blo 350755 1346159 := bstep (se 1 (by rfl) ⟨1009619, by rfl⟩ : syracuseStep 1346159 = 2019239) B2019239
theorem B527615 : Blo 350755 527615 := bstep (se 1 (by rfl) ⟨395711, by rfl⟩ : syracuseStep 527615 = 791423) B791423
theorem B890423 : Blo 350755 890423 := bstep (se 1 (by rfl) ⟨667817, by rfl⟩ : syracuseStep 890423 = 1335635) B1335635
theorem B530153 : Blo 350755 530153 := bstep (se 2 (by rfl) ⟨198807, by rfl⟩ : syracuseStep 530153 = 397615) B397615
theorem B58595471 : Blo 350755 58595471 := bstep (se 1 (by rfl) ⟨43946603, by rfl⟩ : syracuseStep 58595471 = 87893207) B87893207
theorem B793295 : Blo 350755 793295 := bstep (se 1 (by rfl) ⟨594971, by rfl⟩ : syracuseStep 793295 = 1189943) B1189943
theorem B1907945 : Blo 350755 1907945 := bstep (se 2 (by rfl) ⟨715479, by rfl⟩ : syracuseStep 1907945 = 1430959) B1430959
theorem B795887 : Blo 350755 795887 := bstep (se 1 (by rfl) ⟨596915, by rfl⟩ : syracuseStep 795887 = 1193831) B1193831
theorem B666215 : Blo 350755 666215 := bstep (se 1 (by rfl) ⟨499661, by rfl⟩ : syracuseStep 666215 = 999323) B999323
theorem B1781999 : Blo 350755 1781999 := bstep (se 1 (by rfl) ⟨1336499, by rfl⟩ : syracuseStep 1781999 = 2672999) B2672999
theorem B11416139 : Blo 350755 11416139 := bstep (se 1 (by rfl) ⟨8562104, by rfl⟩ : syracuseStep 11416139 = 17124209) B17124209
theorem B668911 : Blo 350755 668911 := bstep (se 1 (by rfl) ⟨501683, by rfl⟩ : syracuseStep 668911 = 1003367) B1003367
theorem B4110497 : Blo 350755 4110497 := bstep (se 2 (by rfl) ⟨1541436, by rfl⟩ : syracuseStep 4110497 = 3082873) B3082873
theorem B26556983 : Blo 350755 26556983 := bstep (se 1 (by rfl) ⟨19917737, by rfl⟩ : syracuseStep 26556983 = 39835475) B39835475
theorem B1785887 : Blo 350755 1785887 := bstep (se 1 (by rfl) ⟨1339415, by rfl⟩ : syracuseStep 1785887 = 2678831) B2678831
theorem B1786859 : Blo 350755 1786859 := bstep (se 1 (by rfl) ⟨1340144, by rfl⟩ : syracuseStep 1786859 = 2680289) B2680289
theorem B1001555 : Blo 350755 1001555 := bstep (se 1 (by rfl) ⟨751166, by rfl⟩ : syracuseStep 1001555 = 1502333) B1502333
theorem B1691047 : Blo 350755 1691047 := bstep (se 1 (by rfl) ⟨1268285, by rfl⟩ : syracuseStep 1691047 = 2536571) B2536571
theorem B2018783 : Blo 350755 2018783 := bstep (se 1 (by rfl) ⟨1514087, by rfl⟩ : syracuseStep 2018783 = 3028175) B3028175
theorem B6410339 : Blo 350755 6410339 := bstep (se 1 (by rfl) ⟨4807754, by rfl⟩ : syracuseStep 6410339 = 9615509) B9615509
theorem B2674943 : Blo 350755 2674943 := bstep (se 1 (by rfl) ⟨2006207, by rfl⟩ : syracuseStep 2674943 = 4012415) B4012415
theorem B1007615 : Blo 350755 1007615 := bstep (se 1 (by rfl) ⟨755711, by rfl⟩ : syracuseStep 1007615 = 1511423) B1511423
theorem B352479 : Blo 350755 352479 := bstep (se 1 (by rfl) ⟨264359, by rfl⟩ : syracuseStep 352479 = 528719) B528719
theorem B354367 : Blo 350755 354367 := bstep (se 1 (by rfl) ⟨265775, by rfl⟩ : syracuseStep 354367 = 531551) B531551
theorem B6219931 : Blo 350755 6219931 := bstep (se 1 (by rfl) ⟨4664948, by rfl⟩ : syracuseStep 6219931 = 9329897) B9329897
theorem B1601819 : Blo 350755 1601819 := bstep (se 1 (by rfl) ⟨1201364, by rfl⟩ : syracuseStep 1601819 = 2402729) B2402729
theorem B6451649 : Blo 350755 6451649 := bstep (se 2 (by rfl) ⟨2419368, by rfl⟩ : syracuseStep 6451649 = 4838737) B4838737
theorem B1504793 : Blo 350755 1504793 := bstep (se 2 (by rfl) ⟨564297, by rfl⟩ : syracuseStep 1504793 = 1128595) B1128595
theorem B1277311 : Blo 350755 1277311 := bstep (se 1 (by rfl) ⟨957983, by rfl⟩ : syracuseStep 1277311 = 1915967) B1915967
theorem B21823343 : Blo 350755 21823343 := bstep (se 1 (by rfl) ⟨16367507, by rfl⟩ : syracuseStep 21823343 = 32735015) B32735015
theorem B14550353 : Blo 350755 14550353 := bstep (se 2 (by rfl) ⟨5456382, by rfl⟩ : syracuseStep 14550353 = 10912765) B10912765
theorem B1345855 : Blo 350755 1345855 := bstep (se 1 (by rfl) ⟨1009391, by rfl⟩ : syracuseStep 1345855 = 2018783) B2018783
theorem B8293241 : Blo 350755 8293241 := bstep (se 2 (by rfl) ⟨3109965, by rfl⟩ : syracuseStep 8293241 = 6219931) B6219931
theorem B593615 : Blo 350755 593615 := bstep (se 1 (by rfl) ⟨445211, by rfl⟩ : syracuseStep 593615 = 890423) B890423
theorem B39063647 : Blo 350755 39063647 := bstep (se 1 (by rfl) ⟨29297735, by rfl⟩ : syracuseStep 39063647 = 58595471) B58595471
theorem B528863 : Blo 350755 528863 := bstep (se 1 (by rfl) ⟨396647, by rfl⟩ : syracuseStep 528863 = 793295) B793295
theorem B530591 : Blo 350755 530591 := bstep (se 1 (by rfl) ⟨397943, by rfl⟩ : syracuseStep 530591 = 795887) B795887
theorem B891881 : Blo 350755 891881 := bstep (se 2 (by rfl) ⟨334455, by rfl⟩ : syracuseStep 891881 = 668911) B668911
theorem B1187999 : Blo 350755 1187999 := bstep (se 1 (by rfl) ⟨890999, by rfl⟩ : syracuseStep 1187999 = 1781999) B1781999
theorem B4301099 : Blo 350755 4301099 := bstep (se 1 (by rfl) ⟨3225824, by rfl⟩ : syracuseStep 4301099 = 6451649) B6451649
theorem B7610759 : Blo 350755 7610759 := bstep (se 1 (by rfl) ⟨5708069, by rfl⟩ : syracuseStep 7610759 = 11416139) B11416139
theorem B17704655 : Blo 350755 17704655 := bstep (se 1 (by rfl) ⟨13278491, by rfl⟩ : syracuseStep 17704655 = 26556983) B26556983
theorem B1190591 : Blo 350755 1190591 := bstep (se 1 (by rfl) ⟨892943, by rfl⟩ : syracuseStep 1190591 = 1785887) B1785887
theorem B1191239 : Blo 350755 1191239 := bstep (se 1 (by rfl) ⟨893429, by rfl⟩ : syracuseStep 1191239 = 1786859) B1786859
theorem B667703 : Blo 350755 667703 := bstep (se 1 (by rfl) ⟨500777, by rfl⟩ : syracuseStep 667703 = 1001555) B1001555
theorem B897439 : Blo 350755 897439 := bstep (se 1 (by rfl) ⟨673079, by rfl⟩ : syracuseStep 897439 = 1346159) B1346159
theorem B4273559 : Blo 350755 4273559 := bstep (se 1 (by rfl) ⟨3205169, by rfl⟩ : syracuseStep 4273559 = 6410339) B6410339
theorem B1783295 : Blo 350755 1783295 := bstep (se 1 (by rfl) ⟨1337471, by rfl⟩ : syracuseStep 1783295 = 2674943) B2674943
theorem B671743 : Blo 350755 671743 := bstep (se 1 (by rfl) ⟨503807, by rfl⟩ : syracuseStep 671743 = 1007615) B1007615
theorem B444143 : Blo 350755 444143 := bstep (se 1 (by rfl) ⟨333107, by rfl⟩ : syracuseStep 444143 = 666215) B666215
theorem B1067879 : Blo 350755 1067879 := bstep (se 1 (by rfl) ⟨800909, by rfl⟩ : syracuseStep 1067879 = 1601819) B1601819
theorem B1003195 : Blo 350755 1003195 := bstep (se 1 (by rfl) ⟨752396, by rfl⟩ : syracuseStep 1003195 = 1504793) B1504793
theorem B2740331 : Blo 350755 2740331 := bstep (se 1 (by rfl) ⟨2055248, by rfl⟩ : syracuseStep 2740331 = 4110497) B4110497
theorem B9001691 : Blo 350755 9001691 := bstep (se 1 (by rfl) ⟨6751268, by rfl⟩ : syracuseStep 9001691 = 13502537) B13502537
theorem B351743 : Blo 350755 351743 := bstep (se 1 (by rfl) ⟨263807, by rfl⟩ : syracuseStep 351743 = 527615) B527615
theorem B353435 : Blo 350755 353435 := bstep (se 1 (by rfl) ⟨265076, by rfl⟩ : syracuseStep 353435 = 530153) B530153
theorem B2254729 : Blo 350755 2254729 := bstep (se 2 (by rfl) ⟨845523, by rfl⟩ : syracuseStep 2254729 = 1691047) B1691047
theorem B1271963 : Blo 350755 1271963 := bstep (se 1 (by rfl) ⟨953972, by rfl⟩ : syracuseStep 1271963 = 1907945) B1907945
theorem B1703081 : Blo 350755 1703081 := bstep (se 2 (by rfl) ⟨638655, by rfl⟩ : syracuseStep 1703081 = 1277311) B1277311
theorem B14548895 : Blo 350755 14548895 := bstep (se 1 (by rfl) ⟨10911671, by rfl⟩ : syracuseStep 14548895 = 21823343) B21823343
theorem B9700235 : Blo 350755 9700235 := bstep (se 1 (by rfl) ⟨7275176, by rfl⟩ : syracuseStep 9700235 = 14550353) B14550353
theorem B395743 : Blo 350755 395743 := bstep (se 1 (by rfl) ⟨296807, by rfl⟩ : syracuseStep 395743 = 593615) B593615
theorem B6001127 : Blo 350755 6001127 := bstep (se 1 (by rfl) ⟨4500845, by rfl⟩ : syracuseStep 6001127 = 9001691) B9001691
theorem B1184381 : Blo 350755 1184381 := bstep (se 3 (by rfl) ⟨222071, by rfl⟩ : syracuseStep 1184381 = 444143) B444143
theorem B594587 : Blo 350755 594587 := bstep (se 1 (by rfl) ⟨445940, by rfl⟩ : syracuseStep 594587 = 891881) B891881
theorem B791999 : Blo 350755 791999 := bstep (se 1 (by rfl) ⟨593999, by rfl⟩ : syracuseStep 791999 = 1187999) B1187999
theorem B11803103 : Blo 350755 11803103 := bstep (se 1 (by rfl) ⟨8852327, by rfl⟩ : syracuseStep 11803103 = 17704655) B17704655
theorem B793727 : Blo 350755 793727 := bstep (se 1 (by rfl) ⟨595295, by rfl⟩ : syracuseStep 793727 = 1190591) B1190591
theorem B794159 : Blo 350755 794159 := bstep (se 1 (by rfl) ⟨595619, by rfl⟩ : syracuseStep 794159 = 1191239) B1191239
theorem B1188863 : Blo 350755 1188863 := bstep (se 1 (by rfl) ⟨891647, by rfl⟩ : syracuseStep 1188863 = 1783295) B1783295
theorem B895657 : Blo 350755 895657 := bstep (se 2 (by rfl) ⟨335871, by rfl⟩ : syracuseStep 895657 = 671743) B671743
theorem B1780541 : Blo 350755 1780541 := bstep (se 3 (by rfl) ⟨333851, by rfl⟩ : syracuseStep 1780541 = 667703) B667703
theorem B2867399 : Blo 350755 2867399 := bstep (se 1 (by rfl) ⟨2150549, by rfl⟩ : syracuseStep 2867399 = 4301099) B4301099
theorem B3391901 : Blo 350755 3391901 := bstep (se 3 (by rfl) ⟨635981, by rfl⟩ : syracuseStep 3391901 = 1271963) B1271963
theorem B1196585 : Blo 350755 1196585 := bstep (se 2 (by rfl) ⟨448719, by rfl⟩ : syracuseStep 1196585 = 897439) B897439
theorem B1135387 : Blo 350755 1135387 := bstep (se 1 (by rfl) ⟨851540, by rfl⟩ : syracuseStep 1135387 = 1703081) B1703081
theorem B711919 : Blo 350755 711919 := bstep (se 1 (by rfl) ⟨533939, by rfl⟩ : syracuseStep 711919 = 1067879) B1067879
theorem B5528827 : Blo 350755 5528827 := bstep (se 1 (by rfl) ⟨4146620, by rfl⟩ : syracuseStep 5528827 = 8293241) B8293241
theorem B3006305 : Blo 350755 3006305 := bstep (se 2 (by rfl) ⟨1127364, by rfl⟩ : syracuseStep 3006305 = 2254729) B2254729
theorem B26042431 : Blo 350755 26042431 := bstep (se 1 (by rfl) ⟨19531823, by rfl⟩ : syracuseStep 26042431 = 39063647) B39063647
theorem B1826887 : Blo 350755 1826887 := bstep (se 1 (by rfl) ⟨1370165, by rfl⟩ : syracuseStep 1826887 = 2740331) B2740331
theorem B352575 : Blo 350755 352575 := bstep (se 1 (by rfl) ⟨264431, by rfl⟩ : syracuseStep 352575 = 528863) B528863
theorem B1794473 : Blo 350755 1794473 := bstep (se 2 (by rfl) ⟨672927, by rfl⟩ : syracuseStep 1794473 = 1345855) B1345855
theorem B353727 : Blo 350755 353727 := bstep (se 1 (by rfl) ⟨265295, by rfl⟩ : syracuseStep 353727 = 530591) B530591
theorem B1337593 : Blo 350755 1337593 := bstep (se 2 (by rfl) ⟨501597, by rfl⟩ : syracuseStep 1337593 = 1003195) B1003195
theorem B5073839 : Blo 350755 5073839 := bstep (se 1 (by rfl) ⟨3805379, by rfl⟩ : syracuseStep 5073839 = 7610759) B7610759
theorem B2849039 : Blo 350755 2849039 := bstep (se 1 (by rfl) ⟨2136779, by rfl⟩ : syracuseStep 2849039 = 4273559) B4273559
theorem B9699263 : Blo 350755 9699263 := bstep (se 1 (by rfl) ⟨7274447, by rfl⟩ : syracuseStep 9699263 = 14548895) B14548895
theorem B2261267 : Blo 350755 2261267 := bstep (se 1 (by rfl) ⟨1695950, by rfl⟩ : syracuseStep 2261267 = 3391901) B3391901
theorem B4000751 : Blo 350755 4000751 := bstep (se 1 (by rfl) ⟨3000563, by rfl⟩ : syracuseStep 4000751 = 6001127) B6001127
theorem B789587 : Blo 350755 789587 := bstep (se 1 (by rfl) ⟨592190, by rfl⟩ : syracuseStep 789587 = 1184381) B1184381
theorem B396391 : Blo 350755 396391 := bstep (se 1 (by rfl) ⟨297293, by rfl⟩ : syracuseStep 396391 = 594587) B594587
theorem B527657 : Blo 350755 527657 := bstep (se 2 (by rfl) ⟨197871, by rfl⟩ : syracuseStep 527657 = 395743) B395743
theorem B527999 : Blo 350755 527999 := bstep (se 1 (by rfl) ⟨395999, by rfl⟩ : syracuseStep 527999 = 791999) B791999
theorem B7868735 : Blo 350755 7868735 := bstep (se 1 (by rfl) ⟨5901551, by rfl⟩ : syracuseStep 7868735 = 11803103) B11803103
theorem B529151 : Blo 350755 529151 := bstep (se 1 (by rfl) ⟨396863, by rfl⟩ : syracuseStep 529151 = 793727) B793727
theorem B529439 : Blo 350755 529439 := bstep (se 1 (by rfl) ⟨397079, by rfl⟩ : syracuseStep 529439 = 794159) B794159
theorem B2004203 : Blo 350755 2004203 := bstep (se 1 (by rfl) ⟨1503152, by rfl⟩ : syracuseStep 2004203 = 3006305) B3006305
theorem B792575 : Blo 350755 792575 := bstep (se 1 (by rfl) ⟨594431, by rfl⟩ : syracuseStep 792575 = 1188863) B1188863
theorem B1513849 : Blo 350755 1513849 := bstep (se 2 (by rfl) ⟨567693, by rfl⟩ : syracuseStep 1513849 = 1135387) B1135387
theorem B1187027 : Blo 350755 1187027 := bstep (se 1 (by rfl) ⟨890270, by rfl⟩ : syracuseStep 1187027 = 1780541) B1780541
theorem B3382559 : Blo 350755 3382559 := bstep (se 1 (by rfl) ⟨2536919, by rfl⟩ : syracuseStep 3382559 = 5073839) B5073839
theorem B6466175 : Blo 350755 6466175 := bstep (se 1 (by rfl) ⟨4849631, by rfl⟩ : syracuseStep 6466175 = 9699263) B9699263
theorem B2435849 : Blo 350755 2435849 := bstep (se 2 (by rfl) ⟨913443, by rfl⟩ : syracuseStep 2435849 = 1826887) B1826887
theorem B1911599 : Blo 350755 1911599 := bstep (se 1 (by rfl) ⟨1433699, by rfl⟩ : syracuseStep 1911599 = 2867399) B2867399
theorem B797723 : Blo 350755 797723 := bstep (se 1 (by rfl) ⟨598292, by rfl⟩ : syracuseStep 797723 = 1196585) B1196585
theorem B6466823 : Blo 350755 6466823 := bstep (se 1 (by rfl) ⟨4850117, by rfl⟩ : syracuseStep 6466823 = 9700235) B9700235
theorem B1783457 : Blo 350755 1783457 := bstep (se 2 (by rfl) ⟨668796, by rfl⟩ : syracuseStep 1783457 = 1337593) B1337593
theorem B1194209 : Blo 350755 1194209 := bstep (se 2 (by rfl) ⟨447828, by rfl⟩ : syracuseStep 1194209 = 895657) B895657
theorem B1196315 : Blo 350755 1196315 := bstep (se 1 (by rfl) ⟨897236, by rfl⟩ : syracuseStep 1196315 = 1794473) B1794473
theorem B34723241 : Blo 350755 34723241 := bstep (se 2 (by rfl) ⟨13021215, by rfl⟩ : syracuseStep 34723241 = 26042431) B26042431
theorem B1899359 : Blo 350755 1899359 := bstep (se 1 (by rfl) ⟨1424519, by rfl⟩ : syracuseStep 1899359 = 2849039) B2849039
theorem B949225 : Blo 350755 949225 := bstep (se 2 (by rfl) ⟨355959, by rfl⟩ : syracuseStep 949225 = 711919) B711919
theorem B7371769 : Blo 350755 7371769 := bstep (se 2 (by rfl) ⟨2764413, by rfl⟩ : syracuseStep 7371769 = 5528827) B5528827
theorem B1507511 : Blo 350755 1507511 := bstep (se 1 (by rfl) ⟨1130633, by rfl⟩ : syracuseStep 1507511 = 2261267) B2261267
theorem B526391 : Blo 350755 526391 := bstep (se 1 (by rfl) ⟨394793, by rfl⟩ : syracuseStep 526391 = 789587) B789587
theorem B5245823 : Blo 350755 5245823 := bstep (se 1 (by rfl) ⟨3934367, by rfl⟩ : syracuseStep 5245823 = 7868735) B7868735
theorem B528383 : Blo 350755 528383 := bstep (se 1 (by rfl) ⟨396287, by rfl⟩ : syracuseStep 528383 = 792575) B792575
theorem B528521 : Blo 350755 528521 := bstep (se 2 (by rfl) ⟨198195, by rfl⟩ : syracuseStep 528521 = 396391) B396391
theorem B791351 : Blo 350755 791351 := bstep (se 1 (by rfl) ⟨593513, by rfl⟩ : syracuseStep 791351 = 1187027) B1187027
theorem B531815 : Blo 350755 531815 := bstep (se 1 (by rfl) ⟨398861, by rfl⟩ : syracuseStep 531815 = 797723) B797723
theorem B1188971 : Blo 350755 1188971 := bstep (se 1 (by rfl) ⟨891728, by rfl⟩ : syracuseStep 1188971 = 1783457) B1783457
theorem B796139 : Blo 350755 796139 := bstep (se 1 (by rfl) ⟨597104, by rfl⟩ : syracuseStep 796139 = 1194209) B1194209
theorem B797543 : Blo 350755 797543 := bstep (se 1 (by rfl) ⟨598157, by rfl⟩ : syracuseStep 797543 = 1196315) B1196315
theorem B2667167 : Blo 350755 2667167 := bstep (se 1 (by rfl) ⟨2000375, by rfl⟩ : syracuseStep 2667167 = 4000751) B4000751
theorem B23148827 : Blo 350755 23148827 := bstep (se 1 (by rfl) ⟨17361620, by rfl⟩ : syracuseStep 23148827 = 34723241) B34723241
theorem B4310783 : Blo 350755 4310783 := bstep (se 1 (by rfl) ⟨3233087, by rfl⟩ : syracuseStep 4310783 = 6466175) B6466175
theorem B1623899 : Blo 350755 1623899 := bstep (se 1 (by rfl) ⟨1217924, by rfl⟩ : syracuseStep 1623899 = 2435849) B2435849
theorem B4311215 : Blo 350755 4311215 := bstep (se 1 (by rfl) ⟨3233411, by rfl⟩ : syracuseStep 4311215 = 6466823) B6466823
theorem B2018465 : Blo 350755 2018465 := bstep (se 2 (by rfl) ⟨756924, by rfl⟩ : syracuseStep 2018465 = 1513849) B1513849
theorem B1265633 : Blo 350755 1265633 := bstep (se 2 (by rfl) ⟨474612, by rfl⟩ : syracuseStep 1265633 = 949225) B949225
theorem B1266239 : Blo 350755 1266239 := bstep (se 1 (by rfl) ⟨949679, by rfl⟩ : syracuseStep 1266239 = 1899359) B1899359
theorem B351771 : Blo 350755 351771 := bstep (se 1 (by rfl) ⟨263828, by rfl⟩ : syracuseStep 351771 = 527657) B527657
theorem B351999 : Blo 350755 351999 := bstep (se 1 (by rfl) ⟨263999, by rfl⟩ : syracuseStep 351999 = 527999) B527999
theorem B352767 : Blo 350755 352767 := bstep (se 1 (by rfl) ⟨264575, by rfl⟩ : syracuseStep 352767 = 529151) B529151
theorem B352959 : Blo 350755 352959 := bstep (se 1 (by rfl) ⟨264719, by rfl⟩ : syracuseStep 352959 = 529439) B529439
theorem B1336135 : Blo 350755 1336135 := bstep (se 1 (by rfl) ⟨1002101, by rfl⟩ : syracuseStep 1336135 = 2004203) B2004203
theorem B2255039 : Blo 350755 2255039 := bstep (se 1 (by rfl) ⟨1691279, by rfl⟩ : syracuseStep 2255039 = 3382559) B3382559
theorem B1274399 : Blo 350755 1274399 := bstep (se 1 (by rfl) ⟨955799, by rfl⟩ : syracuseStep 1274399 = 1911599) B1911599
theorem B9829025 : Blo 350755 9829025 := bstep (se 2 (by rfl) ⟨3685884, by rfl⟩ : syracuseStep 9829025 = 7371769) B7371769
theorem B3376637 : Blo 350755 3376637 := bstep (se 3 (by rfl) ⟨633119, by rfl⟩ : syracuseStep 3376637 = 1266239) B1266239
theorem B1345643 : Blo 350755 1345643 := bstep (se 1 (by rfl) ⟨1009232, by rfl⟩ : syracuseStep 1345643 = 2018465) B2018465
theorem B527567 : Blo 350755 527567 := bstep (se 1 (by rfl) ⟨395675, by rfl⟩ : syracuseStep 527567 = 791351) B791351
theorem B4330397 : Blo 350755 4330397 := bstep (se 3 (by rfl) ⟨811949, by rfl⟩ : syracuseStep 4330397 = 1623899) B1623899
theorem B792647 : Blo 350755 792647 := bstep (se 1 (by rfl) ⟨594485, by rfl⟩ : syracuseStep 792647 = 1188971) B1188971
theorem B530759 : Blo 350755 530759 := bstep (se 1 (by rfl) ⟨398069, by rfl⟩ : syracuseStep 530759 = 796139) B796139
theorem B531695 : Blo 350755 531695 := bstep (se 1 (by rfl) ⟨398771, by rfl⟩ : syracuseStep 531695 = 797543) B797543
theorem B1778111 : Blo 350755 1778111 := bstep (se 1 (by rfl) ⟨1333583, by rfl⟩ : syracuseStep 1778111 = 2667167) B2667167
theorem B1781513 : Blo 350755 1781513 := bstep (se 2 (by rfl) ⟨668067, by rfl⟩ : syracuseStep 1781513 = 1336135) B1336135
theorem B1005007 : Blo 350755 1005007 := bstep (se 1 (by rfl) ⟨753755, by rfl⟩ : syracuseStep 1005007 = 1507511) B1507511
theorem B2873855 : Blo 350755 2873855 := bstep (se 1 (by rfl) ⟨2155391, by rfl⟩ : syracuseStep 2873855 = 4310783) B4310783
theorem B350927 : Blo 350755 350927 := bstep (se 1 (by rfl) ⟨263195, by rfl⟩ : syracuseStep 350927 = 526391) B526391
theorem B2874143 : Blo 350755 2874143 := bstep (se 1 (by rfl) ⟨2155607, by rfl⟩ : syracuseStep 2874143 = 4311215) B4311215
theorem B3497215 : Blo 350755 3497215 := bstep (se 1 (by rfl) ⟨2622911, by rfl⟩ : syracuseStep 3497215 = 5245823) B5245823
theorem B843755 : Blo 350755 843755 := bstep (se 1 (by rfl) ⟨632816, by rfl⟩ : syracuseStep 843755 = 1265633) B1265633
theorem B352255 : Blo 350755 352255 := bstep (se 1 (by rfl) ⟨264191, by rfl⟩ : syracuseStep 352255 = 528383) B528383
theorem B352347 : Blo 350755 352347 := bstep (se 1 (by rfl) ⟨264260, by rfl⟩ : syracuseStep 352347 = 528521) B528521
theorem B354543 : Blo 350755 354543 := bstep (se 1 (by rfl) ⟨265907, by rfl⟩ : syracuseStep 354543 = 531815) B531815
theorem B1503359 : Blo 350755 1503359 := bstep (se 1 (by rfl) ⟨1127519, by rfl⟩ : syracuseStep 1503359 = 2255039) B2255039
theorem B849599 : Blo 350755 849599 := bstep (se 1 (by rfl) ⟨637199, by rfl⟩ : syracuseStep 849599 = 1274399) B1274399
theorem B15432551 : Blo 350755 15432551 := bstep (se 1 (by rfl) ⟨11574413, by rfl⟩ : syracuseStep 15432551 = 23148827) B23148827
theorem B6552683 : Blo 350755 6552683 := bstep (se 1 (by rfl) ⟨4914512, by rfl⟩ : syracuseStep 6552683 = 9829025) B9829025
theorem B2886931 : Blo 350755 2886931 := bstep (se 1 (by rfl) ⟨2165198, by rfl⟩ : syracuseStep 2886931 = 4330397) B4330397
theorem B528431 : Blo 350755 528431 := bstep (se 1 (by rfl) ⟨396323, by rfl⟩ : syracuseStep 528431 = 792647) B792647
theorem B1185407 : Blo 350755 1185407 := bstep (se 1 (by rfl) ⟨889055, by rfl⟩ : syracuseStep 1185407 = 1778111) B1778111
theorem B1187675 : Blo 350755 1187675 := bstep (se 1 (by rfl) ⟨890756, by rfl⟩ : syracuseStep 1187675 = 1781513) B1781513
theorem B566399 : Blo 350755 566399 := bstep (se 1 (by rfl) ⟨424799, by rfl⟩ : syracuseStep 566399 = 849599) B849599
theorem B4662953 : Blo 350755 4662953 := bstep (se 2 (by rfl) ⟨1748607, by rfl⟩ : syracuseStep 4662953 = 3497215) B3497215
theorem B4368455 : Blo 350755 4368455 := bstep (se 1 (by rfl) ⟨3276341, by rfl⟩ : syracuseStep 4368455 = 6552683) B6552683
theorem B897095 : Blo 350755 897095 := bstep (se 1 (by rfl) ⟨672821, by rfl⟩ : syracuseStep 897095 = 1345643) B1345643
theorem B1915903 : Blo 350755 1915903 := bstep (se 1 (by rfl) ⟨1436927, by rfl⟩ : syracuseStep 1915903 = 2873855) B2873855
theorem B1916095 : Blo 350755 1916095 := bstep (se 1 (by rfl) ⟨1437071, by rfl⟩ : syracuseStep 1916095 = 2874143) B2874143
theorem B1002239 : Blo 350755 1002239 := bstep (se 1 (by rfl) ⟨751679, by rfl⟩ : syracuseStep 1002239 = 1503359) B1503359
theorem B2250013 : Blo 350755 2250013 := bstep (se 3 (by rfl) ⟨421877, by rfl⟩ : syracuseStep 2250013 = 843755) B843755
theorem B2251091 : Blo 350755 2251091 := bstep (se 1 (by rfl) ⟨1688318, by rfl⟩ : syracuseStep 2251091 = 3376637) B3376637
theorem B351711 : Blo 350755 351711 := bstep (se 1 (by rfl) ⟨263783, by rfl⟩ : syracuseStep 351711 = 527567) B527567
theorem B353839 : Blo 350755 353839 := bstep (se 1 (by rfl) ⟨265379, by rfl⟩ : syracuseStep 353839 = 530759) B530759
theorem B354463 : Blo 350755 354463 := bstep (se 1 (by rfl) ⟨265847, by rfl⟩ : syracuseStep 354463 = 531695) B531695
theorem B1340009 : Blo 350755 1340009 := bstep (se 2 (by rfl) ⟨502503, by rfl⟩ : syracuseStep 1340009 = 1005007) B1005007
theorem B10288367 : Blo 350755 10288367 := bstep (se 1 (by rfl) ⟨7716275, by rfl⟩ : syracuseStep 10288367 = 15432551) B15432551
theorem B1510397 : Blo 350755 1510397 := bstep (se 3 (by rfl) ⟨283199, by rfl⟩ : syracuseStep 1510397 = 566399) B566399
theorem B790271 : Blo 350755 790271 := bstep (se 1 (by rfl) ⟨592703, by rfl⟩ : syracuseStep 790271 = 1185407) B1185407
theorem B791783 : Blo 350755 791783 := bstep (se 1 (by rfl) ⟨593837, by rfl⟩ : syracuseStep 791783 = 1187675) B1187675
theorem B598063 : Blo 350755 598063 := bstep (se 1 (by rfl) ⟨448547, by rfl⟩ : syracuseStep 598063 = 897095) B897095
theorem B893339 : Blo 350755 893339 := bstep (se 1 (by rfl) ⟨670004, by rfl⟩ : syracuseStep 893339 = 1340009) B1340009
theorem B6858911 : Blo 350755 6858911 := bstep (se 1 (by rfl) ⟨5144183, by rfl⟩ : syracuseStep 6858911 = 10288367) B10288367
theorem B668159 : Blo 350755 668159 := bstep (se 1 (by rfl) ⟨501119, by rfl⟩ : syracuseStep 668159 = 1002239) B1002239
theorem B3849241 : Blo 350755 3849241 := bstep (se 2 (by rfl) ⟨1443465, by rfl⟩ : syracuseStep 3849241 = 2886931) B2886931
theorem B3000017 : Blo 350755 3000017 := bstep (se 2 (by rfl) ⟨1125006, by rfl⟩ : syracuseStep 3000017 = 2250013) B2250013
theorem B352287 : Blo 350755 352287 := bstep (se 1 (by rfl) ⟨264215, by rfl⟩ : syracuseStep 352287 = 528431) B528431
theorem B1500727 : Blo 350755 1500727 := bstep (se 1 (by rfl) ⟨1125545, by rfl⟩ : syracuseStep 1500727 = 2251091) B2251091
theorem B3108635 : Blo 350755 3108635 := bstep (se 1 (by rfl) ⟨2331476, by rfl⟩ : syracuseStep 3108635 = 4662953) B4662953
theorem B2912303 : Blo 350755 2912303 := bstep (se 1 (by rfl) ⟨2184227, by rfl⟩ : syracuseStep 2912303 = 4368455) B4368455
theorem B2554537 : Blo 350755 2554537 := bstep (se 2 (by rfl) ⟨957951, by rfl⟩ : syracuseStep 2554537 = 1915903) B1915903
theorem B2554793 : Blo 350755 2554793 := bstep (se 2 (by rfl) ⟨958047, by rfl⟩ : syracuseStep 2554793 = 1916095) B1916095
theorem B2000011 : Blo 350755 2000011 := bstep (se 1 (by rfl) ⟨1500008, by rfl⟩ : syracuseStep 2000011 = 3000017) B3000017
theorem B2000969 : Blo 350755 2000969 := bstep (se 2 (by rfl) ⟨750363, by rfl⟩ : syracuseStep 2000969 = 1500727) B1500727
theorem B526847 : Blo 350755 526847 := bstep (se 1 (by rfl) ⟨395135, by rfl⟩ : syracuseStep 526847 = 790271) B790271
theorem B527855 : Blo 350755 527855 := bstep (se 1 (by rfl) ⟨395891, by rfl⟩ : syracuseStep 527855 = 791783) B791783
theorem B595559 : Blo 350755 595559 := bstep (se 1 (by rfl) ⟨446669, by rfl⟩ : syracuseStep 595559 = 893339) B893339
theorem B2072423 : Blo 350755 2072423 := bstep (se 1 (by rfl) ⟨1554317, by rfl⟩ : syracuseStep 2072423 = 3108635) B3108635
theorem B1941535 : Blo 350755 1941535 := bstep (se 1 (by rfl) ⟨1456151, by rfl⟩ : syracuseStep 1941535 = 2912303) B2912303
theorem B797417 : Blo 350755 797417 := bstep (se 2 (by rfl) ⟨299031, by rfl⟩ : syracuseStep 797417 = 598063) B598063
theorem B4572607 : Blo 350755 4572607 := bstep (se 1 (by rfl) ⟨3429455, by rfl⟩ : syracuseStep 4572607 = 6858911) B6858911
theorem B445439 : Blo 350755 445439 := bstep (se 1 (by rfl) ⟨334079, by rfl⟩ : syracuseStep 445439 = 668159) B668159
theorem B5132321 : Blo 350755 5132321 := bstep (se 2 (by rfl) ⟨1924620, by rfl⟩ : syracuseStep 5132321 = 3849241) B3849241
theorem B1006931 : Blo 350755 1006931 := bstep (se 1 (by rfl) ⟨755198, by rfl⟩ : syracuseStep 1006931 = 1510397) B1510397
theorem B3406049 : Blo 350755 3406049 := bstep (se 2 (by rfl) ⟨1277268, by rfl⟩ : syracuseStep 3406049 = 2554537) B2554537
theorem B1703195 : Blo 350755 1703195 := bstep (se 1 (by rfl) ⟨1277396, by rfl⟩ : syracuseStep 1703195 = 2554793) B2554793
theorem B10354853 : Blo 350755 10354853 := bstep (se 4 (by rfl) ⟨970767, by rfl⟩ : syracuseStep 10354853 = 1941535) B1941535
theorem B6096809 : Blo 350755 6096809 := bstep (se 2 (by rfl) ⟨2286303, by rfl⟩ : syracuseStep 6096809 = 4572607) B4572607
theorem B397039 : Blo 350755 397039 := bstep (se 1 (by rfl) ⟨297779, by rfl⟩ : syracuseStep 397039 = 595559) B595559
theorem B531611 : Blo 350755 531611 := bstep (se 1 (by rfl) ⟨398708, by rfl⟩ : syracuseStep 531611 = 797417) B797417
theorem B1187837 : Blo 350755 1187837 := bstep (se 3 (by rfl) ⟨222719, by rfl⟩ : syracuseStep 1187837 = 445439) B445439
theorem B2270699 : Blo 350755 2270699 := bstep (se 1 (by rfl) ⟨1703024, by rfl⟩ : syracuseStep 2270699 = 3406049) B3406049
theorem B2666681 : Blo 350755 2666681 := bstep (se 2 (by rfl) ⟨1000005, by rfl⟩ : syracuseStep 2666681 = 2000011) B2000011
theorem B3421547 : Blo 350755 3421547 := bstep (se 1 (by rfl) ⟨2566160, by rfl⟩ : syracuseStep 3421547 = 5132321) B5132321
theorem B1135463 : Blo 350755 1135463 := bstep (se 1 (by rfl) ⟨851597, by rfl⟩ : syracuseStep 1135463 = 1703195) B1703195
theorem B5526461 : Blo 350755 5526461 := bstep (se 3 (by rfl) ⟨1036211, by rfl⟩ : syracuseStep 5526461 = 2072423) B2072423
theorem B1333979 : Blo 350755 1333979 := bstep (se 1 (by rfl) ⟨1000484, by rfl⟩ : syracuseStep 1333979 = 2000969) B2000969
theorem B351231 : Blo 350755 351231 := bstep (se 1 (by rfl) ⟨263423, by rfl⟩ : syracuseStep 351231 = 526847) B526847
theorem B351903 : Blo 350755 351903 := bstep (se 1 (by rfl) ⟨263927, by rfl⟩ : syracuseStep 351903 = 527855) B527855
theorem B2685149 : Blo 350755 2685149 := bstep (se 3 (by rfl) ⟨503465, by rfl⟩ : syracuseStep 2685149 = 1006931) B1006931
theorem B4064539 : Blo 350755 4064539 := bstep (se 1 (by rfl) ⟨3048404, by rfl⟩ : syracuseStep 4064539 = 6096809) B6096809
theorem B889319 : Blo 350755 889319 := bstep (se 1 (by rfl) ⟨666989, by rfl⟩ : syracuseStep 889319 = 1333979) B1333979
theorem B529385 : Blo 350755 529385 := bstep (se 2 (by rfl) ⟨198519, by rfl⟩ : syracuseStep 529385 = 397039) B397039
theorem B791891 : Blo 350755 791891 := bstep (se 1 (by rfl) ⟨593918, by rfl⟩ : syracuseStep 791891 = 1187837) B1187837
theorem B1513799 : Blo 350755 1513799 := bstep (se 1 (by rfl) ⟨1135349, by rfl⟩ : syracuseStep 1513799 = 2270699) B2270699
theorem B1777787 : Blo 350755 1777787 := bstep (se 1 (by rfl) ⟨1333340, by rfl⟩ : syracuseStep 1777787 = 2666681) B2666681
theorem B3027901 : Blo 350755 3027901 := bstep (se 3 (by rfl) ⟨567731, by rfl⟩ : syracuseStep 3027901 = 1135463) B1135463
theorem B3684307 : Blo 350755 3684307 := bstep (se 1 (by rfl) ⟨2763230, by rfl⟩ : syracuseStep 3684307 = 5526461) B5526461
theorem B2281031 : Blo 350755 2281031 := bstep (se 1 (by rfl) ⟨1710773, by rfl⟩ : syracuseStep 2281031 = 3421547) B3421547
theorem B1790099 : Blo 350755 1790099 := bstep (se 1 (by rfl) ⟨1342574, by rfl⟩ : syracuseStep 1790099 = 2685149) B2685149
theorem B6903235 : Blo 350755 6903235 := bstep (se 1 (by rfl) ⟨5177426, by rfl⟩ : syracuseStep 6903235 = 10354853) B10354853
theorem B354407 : Blo 350755 354407 := bstep (se 1 (by rfl) ⟨265805, by rfl⟩ : syracuseStep 354407 = 531611) B531611
theorem B592879 : Blo 350755 592879 := bstep (se 1 (by rfl) ⟨444659, by rfl⟩ : syracuseStep 592879 = 889319) B889319
theorem B527927 : Blo 350755 527927 := bstep (se 1 (by rfl) ⟨395945, by rfl⟩ : syracuseStep 527927 = 791891) B791891
theorem B1185191 : Blo 350755 1185191 := bstep (se 1 (by rfl) ⟨888893, by rfl⟩ : syracuseStep 1185191 = 1777787) B1777787
theorem B4037201 : Blo 350755 4037201 := bstep (se 2 (by rfl) ⟨1513950, by rfl⟩ : syracuseStep 4037201 = 3027901) B3027901
theorem B5419385 : Blo 350755 5419385 := bstep (se 2 (by rfl) ⟨2032269, by rfl⟩ : syracuseStep 5419385 = 4064539) B4064539
theorem B1520687 : Blo 350755 1520687 := bstep (se 1 (by rfl) ⟨1140515, by rfl⟩ : syracuseStep 1520687 = 2281031) B2281031
theorem B1193399 : Blo 350755 1193399 := bstep (se 1 (by rfl) ⟨895049, by rfl⟩ : syracuseStep 1193399 = 1790099) B1790099
theorem B352923 : Blo 350755 352923 := bstep (se 1 (by rfl) ⟨264692, by rfl⟩ : syracuseStep 352923 = 529385) B529385
theorem B1009199 : Blo 350755 1009199 := bstep (se 1 (by rfl) ⟨756899, by rfl⟩ : syracuseStep 1009199 = 1513799) B1513799
theorem B9204313 : Blo 350755 9204313 := bstep (se 2 (by rfl) ⟨3451617, by rfl⟩ : syracuseStep 9204313 = 6903235) B6903235
theorem B4912409 : Blo 350755 4912409 := bstep (se 2 (by rfl) ⟨1842153, by rfl⟩ : syracuseStep 4912409 = 3684307) B3684307
theorem B790127 : Blo 350755 790127 := bstep (se 1 (by rfl) ⟨592595, by rfl⟩ : syracuseStep 790127 = 1185191) B1185191
theorem B790505 : Blo 350755 790505 := bstep (se 2 (by rfl) ⟨296439, by rfl⟩ : syracuseStep 790505 = 592879) B592879
theorem B2691467 : Blo 350755 2691467 := bstep (se 1 (by rfl) ⟨2018600, by rfl⟩ : syracuseStep 2691467 = 4037201) B4037201
theorem B3612923 : Blo 350755 3612923 := bstep (se 1 (by rfl) ⟨2709692, by rfl⟩ : syracuseStep 3612923 = 5419385) B5419385
theorem B795599 : Blo 350755 795599 := bstep (se 1 (by rfl) ⟨596699, by rfl⟩ : syracuseStep 795599 = 1193399) B1193399
theorem B12272417 : Blo 350755 12272417 := bstep (se 2 (by rfl) ⟨4602156, by rfl⟩ : syracuseStep 12272417 = 9204313) B9204313
theorem B672799 : Blo 350755 672799 := bstep (se 1 (by rfl) ⟨504599, by rfl⟩ : syracuseStep 672799 = 1009199) B1009199
theorem B351951 : Blo 350755 351951 := bstep (se 1 (by rfl) ⟨263963, by rfl⟩ : syracuseStep 351951 = 527927) B527927
theorem B1013791 : Blo 350755 1013791 := bstep (se 1 (by rfl) ⟨760343, by rfl⟩ : syracuseStep 1013791 = 1520687) B1520687
theorem B3274939 : Blo 350755 3274939 := bstep (se 1 (by rfl) ⟨2456204, by rfl⟩ : syracuseStep 3274939 = 4912409) B4912409
theorem B526751 : Blo 350755 526751 := bstep (se 1 (by rfl) ⟨395063, by rfl⟩ : syracuseStep 526751 = 790127) B790127
theorem B527003 : Blo 350755 527003 := bstep (se 1 (by rfl) ⟨395252, by rfl⟩ : syracuseStep 527003 = 790505) B790505
theorem B530399 : Blo 350755 530399 := bstep (se 1 (by rfl) ⟨397799, by rfl⟩ : syracuseStep 530399 = 795599) B795599
theorem B1351721 : Blo 350755 1351721 := bstep (se 2 (by rfl) ⟨506895, by rfl⟩ : syracuseStep 1351721 = 1013791) B1013791
theorem B4366585 : Blo 350755 4366585 := bstep (se 2 (by rfl) ⟨1637469, by rfl⟩ : syracuseStep 4366585 = 3274939) B3274939
theorem B897065 : Blo 350755 897065 := bstep (se 2 (by rfl) ⟨336399, by rfl⟩ : syracuseStep 897065 = 672799) B672799
theorem B2408615 : Blo 350755 2408615 := bstep (se 1 (by rfl) ⟨1806461, by rfl⟩ : syracuseStep 2408615 = 3612923) B3612923
theorem B8181611 : Blo 350755 8181611 := bstep (se 1 (by rfl) ⟨6136208, by rfl⟩ : syracuseStep 8181611 = 12272417) B12272417
theorem B1794311 : Blo 350755 1794311 := bstep (se 1 (by rfl) ⟨1345733, by rfl⟩ : syracuseStep 1794311 = 2691467) B2691467
theorem B1605743 : Blo 350755 1605743 := bstep (se 1 (by rfl) ⟨1204307, by rfl⟩ : syracuseStep 1605743 = 2408615) B2408615
theorem B598043 : Blo 350755 598043 := bstep (se 1 (by rfl) ⟨448532, by rfl⟩ : syracuseStep 598043 = 897065) B897065
theorem B5454407 : Blo 350755 5454407 := bstep (se 1 (by rfl) ⟨4090805, by rfl⟩ : syracuseStep 5454407 = 8181611) B8181611
theorem B901147 : Blo 350755 901147 := bstep (se 1 (by rfl) ⟨675860, by rfl⟩ : syracuseStep 901147 = 1351721) B1351721
theorem B1196207 : Blo 350755 1196207 := bstep (se 1 (by rfl) ⟨897155, by rfl⟩ : syracuseStep 1196207 = 1794311) B1794311
theorem B5822113 : Blo 350755 5822113 := bstep (se 2 (by rfl) ⟨2183292, by rfl⟩ : syracuseStep 5822113 = 4366585) B4366585
theorem B351167 : Blo 350755 351167 := bstep (se 1 (by rfl) ⟨263375, by rfl⟩ : syracuseStep 351167 = 526751) B526751
theorem B351335 : Blo 350755 351335 := bstep (se 1 (by rfl) ⟨263501, by rfl⟩ : syracuseStep 351335 = 527003) B527003
theorem B353599 : Blo 350755 353599 := bstep (se 1 (by rfl) ⟨265199, by rfl⟩ : syracuseStep 353599 = 530399) B530399
theorem B398695 : Blo 350755 398695 := bstep (se 1 (by rfl) ⟨299021, by rfl⟩ : syracuseStep 398695 = 598043) B598043
theorem B797471 : Blo 350755 797471 := bstep (se 1 (by rfl) ⟨598103, by rfl⟩ : syracuseStep 797471 = 1196207) B1196207
theorem B1201529 : Blo 350755 1201529 := bstep (se 2 (by rfl) ⟨450573, by rfl⟩ : syracuseStep 1201529 = 901147) B901147
theorem B1070495 : Blo 350755 1070495 := bstep (se 1 (by rfl) ⟨802871, by rfl⟩ : syracuseStep 1070495 = 1605743) B1605743
theorem B7762817 : Blo 350755 7762817 := bstep (se 2 (by rfl) ⟨2911056, by rfl⟩ : syracuseStep 7762817 = 5822113) B5822113
theorem B3636271 : Blo 350755 3636271 := bstep (se 1 (by rfl) ⟨2727203, by rfl⟩ : syracuseStep 3636271 = 5454407) B5454407
theorem B531593 : Blo 350755 531593 := bstep (se 2 (by rfl) ⟨199347, by rfl⟩ : syracuseStep 531593 = 398695) B398695
theorem B531647 : Blo 350755 531647 := bstep (se 1 (by rfl) ⟨398735, by rfl⟩ : syracuseStep 531647 = 797471) B797471
theorem B801019 : Blo 350755 801019 := bstep (se 1 (by rfl) ⟨600764, by rfl⟩ : syracuseStep 801019 = 1201529) B1201529
theorem B20700845 : Blo 350755 20700845 := bstep (se 3 (by rfl) ⟨3881408, by rfl⟩ : syracuseStep 20700845 = 7762817) B7762817
theorem B713663 : Blo 350755 713663 := bstep (se 1 (by rfl) ⟨535247, by rfl⟩ : syracuseStep 713663 = 1070495) B1070495
theorem B19393445 : Blo 350755 19393445 := bstep (se 4 (by rfl) ⟨1818135, by rfl⟩ : syracuseStep 19393445 = 3636271) B3636271
theorem B13800563 : Blo 350755 13800563 := bstep (se 1 (by rfl) ⟨10350422, by rfl⟩ : syracuseStep 13800563 = 20700845) B20700845
theorem B51715853 : Blo 350755 51715853 := bstep (se 3 (by rfl) ⟨9696722, by rfl⟩ : syracuseStep 51715853 = 19393445) B19393445
theorem B4272101 : Blo 350755 4272101 := bstep (se 4 (by rfl) ⟨400509, by rfl⟩ : syracuseStep 4272101 = 801019) B801019
theorem B475775 : Blo 350755 475775 := bstep (se 1 (by rfl) ⟨356831, by rfl⟩ : syracuseStep 475775 = 713663) B713663
theorem B354395 : Blo 350755 354395 := bstep (se 1 (by rfl) ⟨265796, by rfl⟩ : syracuseStep 354395 = 531593) B531593
theorem B354431 : Blo 350755 354431 := bstep (se 1 (by rfl) ⟨265823, by rfl⟩ : syracuseStep 354431 = 531647) B531647
theorem B34477235 : Blo 350755 34477235 := bstep (se 1 (by rfl) ⟨25857926, by rfl⟩ : syracuseStep 34477235 = 51715853) B51715853
theorem B9200375 : Blo 350755 9200375 := bstep (se 1 (by rfl) ⟨6900281, by rfl⟩ : syracuseStep 9200375 = 13800563) B13800563
theorem B5074933 : Blo 350755 5074933 := bstep (se 5 (by rfl) ⟨237887, by rfl⟩ : syracuseStep 5074933 = 475775) B475775
theorem B2848067 : Blo 350755 2848067 := bstep (se 1 (by rfl) ⟨2136050, by rfl⟩ : syracuseStep 2848067 = 4272101) B4272101
theorem B6133583 : Blo 350755 6133583 := bstep (se 1 (by rfl) ⟨4600187, by rfl⟩ : syracuseStep 6133583 = 9200375) B9200375
theorem B22984823 : Blo 350755 22984823 := bstep (se 1 (by rfl) ⟨17238617, by rfl⟩ : syracuseStep 22984823 = 34477235) B34477235
theorem B6766577 : Blo 350755 6766577 := bstep (se 2 (by rfl) ⟨2537466, by rfl⟩ : syracuseStep 6766577 = 5074933) B5074933
theorem B1898711 : Blo 350755 1898711 := bstep (se 1 (by rfl) ⟨1424033, by rfl⟩ : syracuseStep 1898711 = 2848067) B2848067
theorem B15323215 : Blo 350755 15323215 := bstep (se 1 (by rfl) ⟨11492411, by rfl⟩ : syracuseStep 15323215 = 22984823) B22984823
theorem B1265807 : Blo 350755 1265807 := bstep (se 1 (by rfl) ⟨949355, by rfl⟩ : syracuseStep 1265807 = 1898711) B1898711
theorem B4511051 : Blo 350755 4511051 := bstep (se 1 (by rfl) ⟨3383288, by rfl⟩ : syracuseStep 4511051 = 6766577) B6766577
theorem B4089055 : Blo 350755 4089055 := bstep (se 1 (by rfl) ⟨3066791, by rfl⟩ : syracuseStep 4089055 = 6133583) B6133583
theorem B5452073 : Blo 350755 5452073 := bstep (se 2 (by rfl) ⟨2044527, by rfl⟩ : syracuseStep 5452073 = 4089055) B4089055
theorem B20430953 : Blo 350755 20430953 := bstep (se 2 (by rfl) ⟨7661607, by rfl⟩ : syracuseStep 20430953 = 15323215) B15323215
theorem B843871 : Blo 350755 843871 := bstep (se 1 (by rfl) ⟨632903, by rfl⟩ : syracuseStep 843871 = 1265807) B1265807
theorem B3007367 : Blo 350755 3007367 := bstep (se 1 (by rfl) ⟨2255525, by rfl⟩ : syracuseStep 3007367 = 4511051) B4511051
theorem B2004911 : Blo 350755 2004911 := bstep (se 1 (by rfl) ⟨1503683, by rfl⟩ : syracuseStep 2004911 = 3007367) B3007367
theorem B1125161 : Blo 350755 1125161 := bstep (se 2 (by rfl) ⟨421935, by rfl⟩ : syracuseStep 1125161 = 843871) B843871
theorem B13620635 : Blo 350755 13620635 := bstep (se 1 (by rfl) ⟨10215476, by rfl⟩ : syracuseStep 13620635 = 20430953) B20430953
theorem B3634715 : Blo 350755 3634715 := bstep (se 1 (by rfl) ⟨2726036, by rfl⟩ : syracuseStep 3634715 = 5452073) B5452073
theorem B9080423 : Blo 350755 9080423 := bstep (se 1 (by rfl) ⟨6810317, by rfl⟩ : syracuseStep 9080423 = 13620635) B13620635
theorem B1336607 : Blo 350755 1336607 := bstep (se 1 (by rfl) ⟨1002455, by rfl⟩ : syracuseStep 1336607 = 2004911) B2004911
theorem B750107 : Blo 350755 750107 := bstep (se 1 (by rfl) ⟨562580, by rfl⟩ : syracuseStep 750107 = 1125161) B1125161
theorem B2423143 : Blo 350755 2423143 := bstep (se 1 (by rfl) ⟨1817357, by rfl⟩ : syracuseStep 2423143 = 3634715) B3634715
theorem B2000285 : Blo 350755 2000285 := bstep (se 3 (by rfl) ⟨375053, by rfl⟩ : syracuseStep 2000285 = 750107) B750107
theorem B891071 : Blo 350755 891071 := bstep (se 1 (by rfl) ⟨668303, by rfl⟩ : syracuseStep 891071 = 1336607) B1336607
theorem B3230857 : Blo 350755 3230857 := bstep (se 2 (by rfl) ⟨1211571, by rfl⟩ : syracuseStep 3230857 = 2423143) B2423143
theorem B6053615 : Blo 350755 6053615 := bstep (se 1 (by rfl) ⟨4540211, by rfl⟩ : syracuseStep 6053615 = 9080423) B9080423
theorem B594047 : Blo 350755 594047 := bstep (se 1 (by rfl) ⟨445535, by rfl⟩ : syracuseStep 594047 = 891071) B891071
theorem B4035743 : Blo 350755 4035743 := bstep (se 1 (by rfl) ⟨3026807, by rfl⟩ : syracuseStep 4035743 = 6053615) B6053615
theorem B1333523 : Blo 350755 1333523 := bstep (se 1 (by rfl) ⟨1000142, by rfl⟩ : syracuseStep 1333523 = 2000285) B2000285
theorem B17231237 : Blo 350755 17231237 := bstep (se 4 (by rfl) ⟨1615428, by rfl⟩ : syracuseStep 17231237 = 3230857) B3230857
theorem B396031 : Blo 350755 396031 := bstep (se 1 (by rfl) ⟨297023, by rfl⟩ : syracuseStep 396031 = 594047) B594047
theorem B2690495 : Blo 350755 2690495 := bstep (se 1 (by rfl) ⟨2017871, by rfl⟩ : syracuseStep 2690495 = 4035743) B4035743
theorem B889015 : Blo 350755 889015 := bstep (se 1 (by rfl) ⟨666761, by rfl⟩ : syracuseStep 889015 = 1333523) B1333523
theorem B11487491 : Blo 350755 11487491 := bstep (se 1 (by rfl) ⟨8615618, by rfl⟩ : syracuseStep 11487491 = 17231237) B17231237
theorem B528041 : Blo 350755 528041 := bstep (se 2 (by rfl) ⟨198015, by rfl⟩ : syracuseStep 528041 = 396031) B396031
theorem B1185353 : Blo 350755 1185353 := bstep (se 2 (by rfl) ⟨444507, by rfl⟩ : syracuseStep 1185353 = 889015) B889015
theorem B7658327 : Blo 350755 7658327 := bstep (se 1 (by rfl) ⟨5743745, by rfl⟩ : syracuseStep 7658327 = 11487491) B11487491
theorem B1793663 : Blo 350755 1793663 := bstep (se 1 (by rfl) ⟨1345247, by rfl⟩ : syracuseStep 1793663 = 2690495) B2690495
theorem B790235 : Blo 350755 790235 := bstep (se 1 (by rfl) ⟨592676, by rfl⟩ : syracuseStep 790235 = 1185353) B1185353
theorem B1195775 : Blo 350755 1195775 := bstep (se 1 (by rfl) ⟨896831, by rfl⟩ : syracuseStep 1195775 = 1793663) B1793663
theorem B352027 : Blo 350755 352027 := bstep (se 1 (by rfl) ⟨264020, by rfl⟩ : syracuseStep 352027 = 528041) B528041
theorem B5105551 : Blo 350755 5105551 := bstep (se 1 (by rfl) ⟨3829163, by rfl⟩ : syracuseStep 5105551 = 7658327) B7658327
theorem B526823 : Blo 350755 526823 := bstep (se 1 (by rfl) ⟨395117, by rfl⟩ : syracuseStep 526823 = 790235) B790235
theorem B797183 : Blo 350755 797183 := bstep (se 1 (by rfl) ⟨597887, by rfl⟩ : syracuseStep 797183 = 1195775) B1195775
theorem B6807401 : Blo 350755 6807401 := bstep (se 2 (by rfl) ⟨2552775, by rfl⟩ : syracuseStep 6807401 = 5105551) B5105551
theorem B531455 : Blo 350755 531455 := bstep (se 1 (by rfl) ⟨398591, by rfl⟩ : syracuseStep 531455 = 797183) B797183
theorem B4538267 : Blo 350755 4538267 := bstep (se 1 (by rfl) ⟨3403700, by rfl⟩ : syracuseStep 4538267 = 6807401) B6807401
theorem B351215 : Blo 350755 351215 := bstep (se 1 (by rfl) ⟨263411, by rfl⟩ : syracuseStep 351215 = 526823) B526823
theorem B3025511 : Blo 350755 3025511 := bstep (se 1 (by rfl) ⟨2269133, by rfl⟩ : syracuseStep 3025511 = 4538267) B4538267
theorem B354303 : Blo 350755 354303 := bstep (se 1 (by rfl) ⟨265727, by rfl⟩ : syracuseStep 354303 = 531455) B531455
theorem B2017007 : Blo 350755 2017007 := bstep (se 1 (by rfl) ⟨1512755, by rfl⟩ : syracuseStep 2017007 = 3025511) B3025511
theorem B1344671 : Blo 350755 1344671 := bstep (se 1 (by rfl) ⟨1008503, by rfl⟩ : syracuseStep 1344671 = 2017007) B2017007
theorem B896447 : Blo 350755 896447 := bstep (se 1 (by rfl) ⟨672335, by rfl⟩ : syracuseStep 896447 = 1344671) B1344671
theorem B597631 : Blo 350755 597631 := bstep (se 1 (by rfl) ⟨448223, by rfl⟩ : syracuseStep 597631 = 896447) B896447
theorem B796841 : Blo 350755 796841 := bstep (se 2 (by rfl) ⟨298815, by rfl⟩ : syracuseStep 796841 = 597631) B597631
theorem B531227 : Blo 350755 531227 := bstep (se 1 (by rfl) ⟨398420, by rfl⟩ : syracuseStep 531227 = 796841) B796841
theorem B354151 : Blo 350755 354151 := bstep (se 1 (by rfl) ⟨265613, by rfl⟩ : syracuseStep 354151 = 531227) B531227

theorem C0 (j : ℕ) (h1 : 87688 ≤ j) (h2 : j ≤ 88387) : Blo 350755 (4 * j + 3) := by
  interval_cases j
  · exact B350755
  · exact B350759
  · exact B350763
  · exact B350767
  · exact B350771
  · exact B350775
  · exact B350779
  · exact B350783
  · exact B350787
  · exact B350791
  · exact B350795
  · exact B350799
  · exact B350803
  · exact B350807
  · exact B350811
  · exact B350815
  · exact B350819
  · exact B350823
  · exact B350827
  · exact B350831
  · exact B350835
  · exact B350839
  · exact B350843
  · exact B350847
  · exact B350851
  · exact B350855
  · exact B350859
  · exact B350863
  · exact B350867
  · exact B350871
  · exact B350875
  · exact B350879
  · exact B350883
  · exact B350887
  · exact B350891
  · exact B350895
  · exact B350899
  · exact B350903
  · exact B350907
  · exact B350911
  · exact B350915
  · exact B350919
  · exact B350923
  · exact B350927
  · exact B350931
  · exact B350935
  · exact B350939
  · exact B350943
  · exact B350947
  · exact B350951
  · exact B350955
  · exact B350959
  · exact B350963
  · exact B350967
  · exact B350971
  · exact B350975
  · exact B350979
  · exact B350983
  · exact B350987
  · exact B350991
  · exact B350995
  · exact B350999
  · exact B351003
  · exact B351007
  · exact B351011
  · exact B351015
  · exact B351019
  · exact B351023
  · exact B351027
  · exact B351031
  · exact B351035
  · exact B351039
  · exact B351043
  · exact B351047
  · exact B351051
  · exact B351055
  · exact B351059
  · exact B351063
  · exact B351067
  · exact B351071
  · exact B351075
  · exact B351079
  · exact B351083
  · exact B351087
  · exact B351091
  · exact B351095
  · exact B351099
  · exact B351103
  · exact B351107
  · exact B351111
  · exact B351115
  · exact B351119
  · exact B351123
  · exact B351127
  · exact B351131
  · exact B351135
  · exact B351139
  · exact B351143
  · exact B351147
  · exact B351151
  · exact B351155
  · exact B351159
  · exact B351163
  · exact B351167
  · exact B351171
  · exact B351175
  · exact B351179
  · exact B351183
  · exact B351187
  · exact B351191
  · exact B351195
  · exact B351199
  · exact B351203
  · exact B351207
  · exact B351211
  · exact B351215
  · exact B351219
  · exact B351223
  · exact B351227
  · exact B351231
  · exact B351235
  · exact B351239
  · exact B351243
  · exact B351247
  · exact B351251
  · exact B351255
  · exact B351259
  · exact B351263
  · exact B351267
  · exact B351271
  · exact B351275
  · exact B351279
  · exact B351283
  · exact B351287
  · exact B351291
  · exact B351295
  · exact B351299
  · exact B351303
  · exact B351307
  · exact B351311
  · exact B351315
  · exact B351319
  · exact B351323
  · exact B351327
  · exact B351331
  · exact B351335
  · exact B351339
  · exact B351343
  · exact B351347
  · exact B351351
  · exact B351355
  · exact B351359
  · exact B351363
  · exact B351367
  · exact B351371
  · exact B351375
  · exact B351379
  · exact B351383
  · exact B351387
  · exact B351391
  · exact B351395
  · exact B351399
  · exact B351403
  · exact B351407
  · exact B351411
  · exact B351415
  · exact B351419
  · exact B351423
  · exact B351427
  · exact B351431
  · exact B351435
  · exact B351439
  · exact B351443
  · exact B351447
  · exact B351451
  · exact B351455
  · exact B351459
  · exact B351463
  · exact B351467
  · exact B351471
  · exact B351475
  · exact B351479
  · exact B351483
  · exact B351487
  · exact B351491
  · exact B351495
  · exact B351499
  · exact B351503
  · exact B351507
  · exact B351511
  · exact B351515
  · exact B351519
  · exact B351523
  · exact B351527
  · exact B351531
  · exact B351535
  · exact B351539
  · exact B351543
  · exact B351547
  · exact B351551
  · exact B351555
  · exact B351559
  · exact B351563
  · exact B351567
  · exact B351571
  · exact B351575
  · exact B351579
  · exact B351583
  · exact B351587
  · exact B351591
  · exact B351595
  · exact B351599
  · exact B351603
  · exact B351607
  · exact B351611
  · exact B351615
  · exact B351619
  · exact B351623
  · exact B351627
  · exact B351631
  · exact B351635
  · exact B351639
  · exact B351643
  · exact B351647
  · exact B351651
  · exact B351655
  · exact B351659
  · exact B351663
  · exact B351667
  · exact B351671
  · exact B351675
  · exact B351679
  · exact B351683
  · exact B351687
  · exact B351691
  · exact B351695
  · exact B351699
  · exact B351703
  · exact B351707
  · exact B351711
  · exact B351715
  · exact B351719
  · exact B351723
  · exact B351727
  · exact B351731
  · exact B351735
  · exact B351739
  · exact B351743
  · exact B351747
  · exact B351751
  · exact B351755
  · exact B351759
  · exact B351763
  · exact B351767
  · exact B351771
  · exact B351775
  · exact B351779
  · exact B351783
  · exact B351787
  · exact B351791
  · exact B351795
  · exact B351799
  · exact B351803
  · exact B351807
  · exact B351811
  · exact B351815
  · exact B351819
  · exact B351823
  · exact B351827
  · exact B351831
  · exact B351835
  · exact B351839
  · exact B351843
  · exact B351847
  · exact B351851
  · exact B351855
  · exact B351859
  · exact B351863
  · exact B351867
  · exact B351871
  · exact B351875
  · exact B351879
  · exact B351883
  · exact B351887
  · exact B351891
  · exact B351895
  · exact B351899
  · exact B351903
  · exact B351907
  · exact B351911
  · exact B351915
  · exact B351919
  · exact B351923
  · exact B351927
  · exact B351931
  · exact B351935
  · exact B351939
  · exact B351943
  · exact B351947
  · exact B351951
  · exact B351955
  · exact B351959
  · exact B351963
  · exact B351967
  · exact B351971
  · exact B351975
  · exact B351979
  · exact B351983
  · exact B351987
  · exact B351991
  · exact B351995
  · exact B351999
  · exact B352003
  · exact B352007
  · exact B352011
  · exact B352015
  · exact B352019
  · exact B352023
  · exact B352027
  · exact B352031
  · exact B352035
  · exact B352039
  · exact B352043
  · exact B352047
  · exact B352051
  · exact B352055
  · exact B352059
  · exact B352063
  · exact B352067
  · exact B352071
  · exact B352075
  · exact B352079
  · exact B352083
  · exact B352087
  · exact B352091
  · exact B352095
  · exact B352099
  · exact B352103
  · exact B352107
  · exact B352111
  · exact B352115
  · exact B352119
  · exact B352123
  · exact B352127
  · exact B352131
  · exact B352135
  · exact B352139
  · exact B352143
  · exact B352147
  · exact B352151
  · exact B352155
  · exact B352159
  · exact B352163
  · exact B352167
  · exact B352171
  · exact B352175
  · exact B352179
  · exact B352183
  · exact B352187
  · exact B352191
  · exact B352195
  · exact B352199
  · exact B352203
  · exact B352207
  · exact B352211
  · exact B352215
  · exact B352219
  · exact B352223
  · exact B352227
  · exact B352231
  · exact B352235
  · exact B352239
  · exact B352243
  · exact B352247
  · exact B352251
  · exact B352255
  · exact B352259
  · exact B352263
  · exact B352267
  · exact B352271
  · exact B352275
  · exact B352279
  · exact B352283
  · exact B352287
  · exact B352291
  · exact B352295
  · exact B352299
  · exact B352303
  · exact B352307
  · exact B352311
  · exact B352315
  · exact B352319
  · exact B352323
  · exact B352327
  · exact B352331
  · exact B352335
  · exact B352339
  · exact B352343
  · exact B352347
  · exact B352351
  · exact B352355
  · exact B352359
  · exact B352363
  · exact B352367
  · exact B352371
  · exact B352375
  · exact B352379
  · exact B352383
  · exact B352387
  · exact B352391
  · exact B352395
  · exact B352399
  · exact B352403
  · exact B352407
  · exact B352411
  · exact B352415
  · exact B352419
  · exact B352423
  · exact B352427
  · exact B352431
  · exact B352435
  · exact B352439
  · exact B352443
  · exact B352447
  · exact B352451
  · exact B352455
  · exact B352459
  · exact B352463
  · exact B352467
  · exact B352471
  · exact B352475
  · exact B352479
  · exact B352483
  · exact B352487
  · exact B352491
  · exact B352495
  · exact B352499
  · exact B352503
  · exact B352507
  · exact B352511
  · exact B352515
  · exact B352519
  · exact B352523
  · exact B352527
  · exact B352531
  · exact B352535
  · exact B352539
  · exact B352543
  · exact B352547
  · exact B352551
  · exact B352555
  · exact B352559
  · exact B352563
  · exact B352567
  · exact B352571
  · exact B352575
  · exact B352579
  · exact B352583
  · exact B352587
  · exact B352591
  · exact B352595
  · exact B352599
  · exact B352603
  · exact B352607
  · exact B352611
  · exact B352615
  · exact B352619
  · exact B352623
  · exact B352627
  · exact B352631
  · exact B352635
  · exact B352639
  · exact B352643
  · exact B352647
  · exact B352651
  · exact B352655
  · exact B352659
  · exact B352663
  · exact B352667
  · exact B352671
  · exact B352675
  · exact B352679
  · exact B352683
  · exact B352687
  · exact B352691
  · exact B352695
  · exact B352699
  · exact B352703
  · exact B352707
  · exact B352711
  · exact B352715
  · exact B352719
  · exact B352723
  · exact B352727
  · exact B352731
  · exact B352735
  · exact B352739
  · exact B352743
  · exact B352747
  · exact B352751
  · exact B352755
  · exact B352759
  · exact B352763
  · exact B352767
  · exact B352771
  · exact B352775
  · exact B352779
  · exact B352783
  · exact B352787
  · exact B352791
  · exact B352795
  · exact B352799
  · exact B352803
  · exact B352807
  · exact B352811
  · exact B352815
  · exact B352819
  · exact B352823
  · exact B352827
  · exact B352831
  · exact B352835
  · exact B352839
  · exact B352843
  · exact B352847
  · exact B352851
  · exact B352855
  · exact B352859
  · exact B352863
  · exact B352867
  · exact B352871
  · exact B352875
  · exact B352879
  · exact B352883
  · exact B352887
  · exact B352891
  · exact B352895
  · exact B352899
  · exact B352903
  · exact B352907
  · exact B352911
  · exact B352915
  · exact B352919
  · exact B352923
  · exact B352927
  · exact B352931
  · exact B352935
  · exact B352939
  · exact B352943
  · exact B352947
  · exact B352951
  · exact B352955
  · exact B352959
  · exact B352963
  · exact B352967
  · exact B352971
  · exact B352975
  · exact B352979
  · exact B352983
  · exact B352987
  · exact B352991
  · exact B352995
  · exact B352999
  · exact B353003
  · exact B353007
  · exact B353011
  · exact B353015
  · exact B353019
  · exact B353023
  · exact B353027
  · exact B353031
  · exact B353035
  · exact B353039
  · exact B353043
  · exact B353047
  · exact B353051
  · exact B353055
  · exact B353059
  · exact B353063
  · exact B353067
  · exact B353071
  · exact B353075
  · exact B353079
  · exact B353083
  · exact B353087
  · exact B353091
  · exact B353095
  · exact B353099
  · exact B353103
  · exact B353107
  · exact B353111
  · exact B353115
  · exact B353119
  · exact B353123
  · exact B353127
  · exact B353131
  · exact B353135
  · exact B353139
  · exact B353143
  · exact B353147
  · exact B353151
  · exact B353155
  · exact B353159
  · exact B353163
  · exact B353167
  · exact B353171
  · exact B353175
  · exact B353179
  · exact B353183
  · exact B353187
  · exact B353191
  · exact B353195
  · exact B353199
  · exact B353203
  · exact B353207
  · exact B353211
  · exact B353215
  · exact B353219
  · exact B353223
  · exact B353227
  · exact B353231
  · exact B353235
  · exact B353239
  · exact B353243
  · exact B353247
  · exact B353251
  · exact B353255
  · exact B353259
  · exact B353263
  · exact B353267
  · exact B353271
  · exact B353275
  · exact B353279
  · exact B353283
  · exact B353287
  · exact B353291
  · exact B353295
  · exact B353299
  · exact B353303
  · exact B353307
  · exact B353311
  · exact B353315
  · exact B353319
  · exact B353323
  · exact B353327
  · exact B353331
  · exact B353335
  · exact B353339
  · exact B353343
  · exact B353347
  · exact B353351
  · exact B353355
  · exact B353359
  · exact B353363
  · exact B353367
  · exact B353371
  · exact B353375
  · exact B353379
  · exact B353383
  · exact B353387
  · exact B353391
  · exact B353395
  · exact B353399
  · exact B353403
  · exact B353407
  · exact B353411
  · exact B353415
  · exact B353419
  · exact B353423
  · exact B353427
  · exact B353431
  · exact B353435
  · exact B353439
  · exact B353443
  · exact B353447
  · exact B353451
  · exact B353455
  · exact B353459
  · exact B353463
  · exact B353467
  · exact B353471
  · exact B353475
  · exact B353479
  · exact B353483
  · exact B353487
  · exact B353491
  · exact B353495
  · exact B353499
  · exact B353503
  · exact B353507
  · exact B353511
  · exact B353515
  · exact B353519
  · exact B353523
  · exact B353527
  · exact B353531
  · exact B353535
  · exact B353539
  · exact B353543
  · exact B353547
  · exact B353551

theorem C1 (j : ℕ) (h1 : 88388 ≤ j) (h2 : j ≤ 88688) : Blo 350755 (4 * j + 3) := by
  interval_cases j
  · exact B353555
  · exact B353559
  · exact B353563
  · exact B353567
  · exact B353571
  · exact B353575
  · exact B353579
  · exact B353583
  · exact B353587
  · exact B353591
  · exact B353595
  · exact B353599
  · exact B353603
  · exact B353607
  · exact B353611
  · exact B353615
  · exact B353619
  · exact B353623
  · exact B353627
  · exact B353631
  · exact B353635
  · exact B353639
  · exact B353643
  · exact B353647
  · exact B353651
  · exact B353655
  · exact B353659
  · exact B353663
  · exact B353667
  · exact B353671
  · exact B353675
  · exact B353679
  · exact B353683
  · exact B353687
  · exact B353691
  · exact B353695
  · exact B353699
  · exact B353703
  · exact B353707
  · exact B353711
  · exact B353715
  · exact B353719
  · exact B353723
  · exact B353727
  · exact B353731
  · exact B353735
  · exact B353739
  · exact B353743
  · exact B353747
  · exact B353751
  · exact B353755
  · exact B353759
  · exact B353763
  · exact B353767
  · exact B353771
  · exact B353775
  · exact B353779
  · exact B353783
  · exact B353787
  · exact B353791
  · exact B353795
  · exact B353799
  · exact B353803
  · exact B353807
  · exact B353811
  · exact B353815
  · exact B353819
  · exact B353823
  · exact B353827
  · exact B353831
  · exact B353835
  · exact B353839
  · exact B353843
  · exact B353847
  · exact B353851
  · exact B353855
  · exact B353859
  · exact B353863
  · exact B353867
  · exact B353871
  · exact B353875
  · exact B353879
  · exact B353883
  · exact B353887
  · exact B353891
  · exact B353895
  · exact B353899
  · exact B353903
  · exact B353907
  · exact B353911
  · exact B353915
  · exact B353919
  · exact B353923
  · exact B353927
  · exact B353931
  · exact B353935
  · exact B353939
  · exact B353943
  · exact B353947
  · exact B353951
  · exact B353955
  · exact B353959
  · exact B353963
  · exact B353967
  · exact B353971
  · exact B353975
  · exact B353979
  · exact B353983
  · exact B353987
  · exact B353991
  · exact B353995
  · exact B353999
  · exact B354003
  · exact B354007
  · exact B354011
  · exact B354015
  · exact B354019
  · exact B354023
  · exact B354027
  · exact B354031
  · exact B354035
  · exact B354039
  · exact B354043
  · exact B354047
  · exact B354051
  · exact B354055
  · exact B354059
  · exact B354063
  · exact B354067
  · exact B354071
  · exact B354075
  · exact B354079
  · exact B354083
  · exact B354087
  · exact B354091
  · exact B354095
  · exact B354099
  · exact B354103
  · exact B354107
  · exact B354111
  · exact B354115
  · exact B354119
  · exact B354123
  · exact B354127
  · exact B354131
  · exact B354135
  · exact B354139
  · exact B354143
  · exact B354147
  · exact B354151
  · exact B354155
  · exact B354159
  · exact B354163
  · exact B354167
  · exact B354171
  · exact B354175
  · exact B354179
  · exact B354183
  · exact B354187
  · exact B354191
  · exact B354195
  · exact B354199
  · exact B354203
  · exact B354207
  · exact B354211
  · exact B354215
  · exact B354219
  · exact B354223
  · exact B354227
  · exact B354231
  · exact B354235
  · exact B354239
  · exact B354243
  · exact B354247
  · exact B354251
  · exact B354255
  · exact B354259
  · exact B354263
  · exact B354267
  · exact B354271
  · exact B354275
  · exact B354279
  · exact B354283
  · exact B354287
  · exact B354291
  · exact B354295
  · exact B354299
  · exact B354303
  · exact B354307
  · exact B354311
  · exact B354315
  · exact B354319
  · exact B354323
  · exact B354327
  · exact B354331
  · exact B354335
  · exact B354339
  · exact B354343
  · exact B354347
  · exact B354351
  · exact B354355
  · exact B354359
  · exact B354363
  · exact B354367
  · exact B354371
  · exact B354375
  · exact B354379
  · exact B354383
  · exact B354387
  · exact B354391
  · exact B354395
  · exact B354399
  · exact B354403
  · exact B354407
  · exact B354411
  · exact B354415
  · exact B354419
  · exact B354423
  · exact B354427
  · exact B354431
  · exact B354435
  · exact B354439
  · exact B354443
  · exact B354447
  · exact B354451
  · exact B354455
  · exact B354459
  · exact B354463
  · exact B354467
  · exact B354471
  · exact B354475
  · exact B354479
  · exact B354483
  · exact B354487
  · exact B354491
  · exact B354495
  · exact B354499
  · exact B354503
  · exact B354507
  · exact B354511
  · exact B354515
  · exact B354519
  · exact B354523
  · exact B354527
  · exact B354531
  · exact B354535
  · exact B354539
  · exact B354543
  · exact B354547
  · exact B354551
  · exact B354555
  · exact B354559
  · exact B354563
  · exact B354567
  · exact B354571
  · exact B354575
  · exact B354579
  · exact B354583
  · exact B354587
  · exact B354591
  · exact B354595
  · exact B354599
  · exact B354603
  · exact B354607
  · exact B354611
  · exact B354615
  · exact B354619
  · exact B354623
  · exact B354627
  · exact B354631
  · exact B354635
  · exact B354639
  · exact B354643
  · exact B354647
  · exact B354651
  · exact B354655
  · exact B354659
  · exact B354663
  · exact B354667
  · exact B354671
  · exact B354675
  · exact B354679
  · exact B354683
  · exact B354687
  · exact B354691
  · exact B354695
  · exact B354699
  · exact B354703
  · exact B354707
  · exact B354711
  · exact B354715
  · exact B354719
  · exact B354723
  · exact B354727
  · exact B354731
  · exact B354735
  · exact B354739
  · exact B354743
  · exact B354747
  · exact B354751
  · exact B354755

theorem solution (m : ℕ) (hlo : 350755 ≤ m) (hhi : m ≤ 354755) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 87688 ≤ j := by omega
    have hj2 : j ≤ 88688 := by omega
    have hb : Blo 350755 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 88388 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
