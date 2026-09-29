-- Prove2me | solution 1 for syracuse_descends_range_1758080_1760080
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:38:32.998985+00:00
-- url     : https://prove2.me/submissions/f09d7367-2860-4436-93f6-35254aa5c131

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


theorem B3956741 : Blo 1758080 3956741 := bbase (se 4 (by rfl) ⟨370944, by rfl⟩ : syracuseStep 3956741 = 741889) (by norm_num)
theorem B2637845 : Blo 1758080 2637845 := bbase (se 6 (by rfl) ⟨61824, by rfl⟩ : syracuseStep 2637845 = 123649) (by norm_num)
theorem B2637869 : Blo 1758080 2637869 := bbase (se 3 (by rfl) ⟨494600, by rfl⟩ : syracuseStep 2637869 = 989201) (by norm_num)
theorem B2113597 : Blo 1758080 2113597 := bbase (se 3 (by rfl) ⟨396299, by rfl⟩ : syracuseStep 2113597 = 792599) (by norm_num)
theorem B2637893 : Blo 1758080 2637893 := bbase (se 4 (by rfl) ⟨247302, by rfl⟩ : syracuseStep 2637893 = 494605) (by norm_num)
theorem B3956813 : Blo 1758080 3956813 := bbase (se 3 (by rfl) ⟨741902, by rfl⟩ : syracuseStep 3956813 = 1483805) (by norm_num)
theorem B4120669 : Blo 1758080 4120669 := bbase (se 3 (by rfl) ⟨772625, by rfl⟩ : syracuseStep 4120669 = 1545251) (by norm_num)
theorem B2637917 : Blo 1758080 2637917 := bbase (se 3 (by rfl) ⟨494609, by rfl⟩ : syracuseStep 2637917 = 989219) (by norm_num)
theorem B2637941 : Blo 1758080 2637941 := bbase (se 5 (by rfl) ⟨123653, by rfl⟩ : syracuseStep 2637941 = 247307) (by norm_num)
theorem B5349509 : Blo 1758080 5349509 := bbase (se 4 (by rfl) ⟨501516, by rfl⟩ : syracuseStep 5349509 = 1003033) (by norm_num)
theorem B2637965 : Blo 1758080 2637965 := bbase (se 3 (by rfl) ⟨494618, by rfl⟩ : syracuseStep 2637965 = 989237) (by norm_num)
theorem B3956885 : Blo 1758080 3956885 := bbase (se 6 (by rfl) ⟨92739, by rfl⟩ : syracuseStep 3956885 = 185479) (by norm_num)
theorem B2637989 : Blo 1758080 2637989 := bbase (se 4 (by rfl) ⟨247311, by rfl⟩ : syracuseStep 2637989 = 494623) (by norm_num)
theorem B2638013 : Blo 1758080 2638013 := bbase (se 3 (by rfl) ⟨494627, by rfl⟩ : syracuseStep 2638013 = 989255) (by norm_num)
theorem B2638037 : Blo 1758080 2638037 := bbase (se 7 (by rfl) ⟨30914, by rfl⟩ : syracuseStep 2638037 = 61829) (by norm_num)
theorem B7512277 : Blo 1758080 7512277 := bbase (se 7 (by rfl) ⟨88034, by rfl⟩ : syracuseStep 7512277 = 176069) (by norm_num)
theorem B5636309 : Blo 1758080 5636309 := bbase (se 7 (by rfl) ⟨66050, by rfl⟩ : syracuseStep 5636309 = 132101) (by norm_num)
theorem B3956957 : Blo 1758080 3956957 := bbase (se 3 (by rfl) ⟨741929, by rfl⟩ : syracuseStep 3956957 = 1483859) (by norm_num)
theorem B2638061 : Blo 1758080 2638061 := bbase (se 3 (by rfl) ⟨494636, by rfl⟩ : syracuseStep 2638061 = 989273) (by norm_num)
theorem B2638085 : Blo 1758080 2638085 := bbase (se 4 (by rfl) ⟨247320, by rfl⟩ : syracuseStep 2638085 = 494641) (by norm_num)
theorem B2818309 : Blo 1758080 2818309 := bbase (se 4 (by rfl) ⟨264216, by rfl⟩ : syracuseStep 2818309 = 528433) (by norm_num)
theorem B2638109 : Blo 1758080 2638109 := bbase (se 3 (by rfl) ⟨494645, by rfl⟩ : syracuseStep 2638109 = 989291) (by norm_num)
theorem B3957029 : Blo 1758080 3957029 := bbase (se 4 (by rfl) ⟨370971, by rfl⟩ : syracuseStep 3957029 = 741943) (by norm_num)
theorem B6676789 : Blo 1758080 6676789 := bbase (se 5 (by rfl) ⟨312974, by rfl⟩ : syracuseStep 6676789 = 625949) (by norm_num)
theorem B2638133 : Blo 1758080 2638133 := bbase (se 5 (by rfl) ⟨123662, by rfl⟩ : syracuseStep 2638133 = 247325) (by norm_num)
theorem B2638157 : Blo 1758080 2638157 := bbase (se 3 (by rfl) ⟨494654, by rfl⟩ : syracuseStep 2638157 = 989309) (by norm_num)
theorem B2638181 : Blo 1758080 2638181 := bbase (se 4 (by rfl) ⟨247329, by rfl⟩ : syracuseStep 2638181 = 494659) (by norm_num)
theorem B2818405 : Blo 1758080 2818405 := bbase (se 4 (by rfl) ⟨264225, by rfl⟩ : syracuseStep 2818405 = 528451) (by norm_num)
theorem B3957101 : Blo 1758080 3957101 := bbase (se 3 (by rfl) ⟨741956, by rfl⟩ : syracuseStep 3957101 = 1483913) (by norm_num)
theorem B12034421 : Blo 1758080 12034421 := bbase (se 5 (by rfl) ⟨564113, by rfl⟩ : syracuseStep 12034421 = 1128227) (by norm_num)
theorem B2638205 : Blo 1758080 2638205 := bbase (se 3 (by rfl) ⟨494663, by rfl⟩ : syracuseStep 2638205 = 989327) (by norm_num)
theorem B2638229 : Blo 1758080 2638229 := bbase (se 6 (by rfl) ⟨61833, by rfl⟩ : syracuseStep 2638229 = 123667) (by norm_num)
theorem B4284821 : Blo 1758080 4284821 := bbase (se 6 (by rfl) ⟨100425, by rfl⟩ : syracuseStep 4284821 = 200851) (by norm_num)
theorem B5939621 : Blo 1758080 5939621 := bbase (se 4 (by rfl) ⟨556839, by rfl⟩ : syracuseStep 5939621 = 1113679) (by norm_num)
theorem B2638253 : Blo 1758080 2638253 := bbase (se 3 (by rfl) ⟨494672, by rfl⟩ : syracuseStep 2638253 = 989345) (by norm_num)
theorem B3957173 : Blo 1758080 3957173 := bbase (se 5 (by rfl) ⟨185492, by rfl⟩ : syracuseStep 3957173 = 370985) (by norm_num)
theorem B13541813 : Blo 1758080 13541813 := bbase (se 5 (by rfl) ⟨634772, by rfl⟩ : syracuseStep 13541813 = 1269545) (by norm_num)
theorem B2638277 : Blo 1758080 2638277 := bbase (se 4 (by rfl) ⟨247338, by rfl⟩ : syracuseStep 2638277 = 494677) (by norm_num)
theorem B10019285 : Blo 1758080 10019285 := bbase (se 7 (by rfl) ⟨117413, by rfl⟩ : syracuseStep 10019285 = 234827) (by norm_num)
theorem B2638301 : Blo 1758080 2638301 := bbase (se 3 (by rfl) ⟨494681, by rfl⟩ : syracuseStep 2638301 = 989363) (by norm_num)
theorem B2638325 : Blo 1758080 2638325 := bbase (se 5 (by rfl) ⟨123671, by rfl⟩ : syracuseStep 2638325 = 247343) (by norm_num)
theorem B3957245 : Blo 1758080 3957245 := bbase (se 3 (by rfl) ⟨741983, by rfl⟩ : syracuseStep 3957245 = 1483967) (by norm_num)
theorem B2818565 : Blo 1758080 2818565 := bbase (se 4 (by rfl) ⟨264240, by rfl⟩ : syracuseStep 2818565 = 528481) (by norm_num)
theorem B2638349 : Blo 1758080 2638349 := bbase (se 3 (by rfl) ⟨494690, by rfl⟩ : syracuseStep 2638349 = 989381) (by norm_num)
theorem B2638373 : Blo 1758080 2638373 := bbase (se 4 (by rfl) ⟨247347, by rfl⟩ : syracuseStep 2638373 = 494695) (by norm_num)
theorem B2638397 : Blo 1758080 2638397 := bbase (se 3 (by rfl) ⟨494699, by rfl⟩ : syracuseStep 2638397 = 989399) (by norm_num)
theorem B3957317 : Blo 1758080 3957317 := bbase (se 4 (by rfl) ⟨370998, by rfl⟩ : syracuseStep 3957317 = 741997) (by norm_num)
theorem B2638421 : Blo 1758080 2638421 := bbase (se 8 (by rfl) ⟨15459, by rfl⟩ : syracuseStep 2638421 = 30919) (by norm_num)
theorem B8905301 : Blo 1758080 8905301 := bbase (se 8 (by rfl) ⟨52179, by rfl⟩ : syracuseStep 8905301 = 104359) (by norm_num)
theorem B6677093 : Blo 1758080 6677093 := bbase (se 4 (by rfl) ⟨625977, by rfl⟩ : syracuseStep 6677093 = 1251955) (by norm_num)
theorem B2638445 : Blo 1758080 2638445 := bbase (se 3 (by rfl) ⟨494708, by rfl⟩ : syracuseStep 2638445 = 989417) (by norm_num)
theorem B8020613 : Blo 1758080 8020613 := bbase (se 4 (by rfl) ⟨751932, by rfl⟩ : syracuseStep 8020613 = 1503865) (by norm_num)
theorem B2638469 : Blo 1758080 2638469 := bbase (se 4 (by rfl) ⟨247356, by rfl⟩ : syracuseStep 2638469 = 494713) (by norm_num)
theorem B2171525 : Blo 1758080 2171525 := bbase (se 4 (by rfl) ⟨203580, by rfl⟩ : syracuseStep 2171525 = 407161) (by norm_num)
theorem B3957389 : Blo 1758080 3957389 := bbase (se 3 (by rfl) ⟨742010, by rfl⟩ : syracuseStep 3957389 = 1484021) (by norm_num)
theorem B2638493 : Blo 1758080 2638493 := bbase (se 3 (by rfl) ⟨494717, by rfl⟩ : syracuseStep 2638493 = 989435) (by norm_num)
theorem B2638517 : Blo 1758080 2638517 := bbase (se 5 (by rfl) ⟨123680, by rfl⟩ : syracuseStep 2638517 = 247361) (by norm_num)
theorem B2638541 : Blo 1758080 2638541 := bbase (se 3 (by rfl) ⟨494726, by rfl⟩ : syracuseStep 2638541 = 989453) (by norm_num)
theorem B3957461 : Blo 1758080 3957461 := bbase (se 7 (by rfl) ⟨46376, by rfl⟩ : syracuseStep 3957461 = 92753) (by norm_num)
theorem B2638565 : Blo 1758080 2638565 := bbase (se 4 (by rfl) ⟨247365, by rfl⟩ : syracuseStep 2638565 = 494731) (by norm_num)
theorem B2638589 : Blo 1758080 2638589 := bbase (se 3 (by rfl) ⟨494735, by rfl⟩ : syracuseStep 2638589 = 989471) (by norm_num)
theorem B3212045 : Blo 1758080 3212045 := bbase (se 3 (by rfl) ⟨602258, by rfl⟩ : syracuseStep 3212045 = 1204517) (by norm_num)
theorem B2638613 : Blo 1758080 2638613 := bbase (se 6 (by rfl) ⟨61842, by rfl⟩ : syracuseStep 2638613 = 123685) (by norm_num)
theorem B3957533 : Blo 1758080 3957533 := bbase (se 3 (by rfl) ⟨742037, by rfl⟩ : syracuseStep 3957533 = 1484075) (by norm_num)
theorem B2638637 : Blo 1758080 2638637 := bbase (se 3 (by rfl) ⟨494744, by rfl⟩ : syracuseStep 2638637 = 989489) (by norm_num)
theorem B2638661 : Blo 1758080 2638661 := bbase (se 4 (by rfl) ⟨247374, by rfl⟩ : syracuseStep 2638661 = 494749) (by norm_num)
theorem B2114381 : Blo 1758080 2114381 := bbase (se 3 (by rfl) ⟨396446, by rfl⟩ : syracuseStep 2114381 = 792893) (by norm_num)
theorem B5940053 : Blo 1758080 5940053 := bbase (se 9 (by rfl) ⟨17402, by rfl⟩ : syracuseStep 5940053 = 34805) (by norm_num)
theorem B2638685 : Blo 1758080 2638685 := bbase (se 3 (by rfl) ⟨494753, by rfl⟩ : syracuseStep 2638685 = 989507) (by norm_num)
theorem B3957605 : Blo 1758080 3957605 := bbase (se 4 (by rfl) ⟨371025, by rfl⟩ : syracuseStep 3957605 = 742051) (by norm_num)
theorem B2638709 : Blo 1758080 2638709 := bbase (se 5 (by rfl) ⟨123689, by rfl⟩ : syracuseStep 2638709 = 247379) (by norm_num)
theorem B2638733 : Blo 1758080 2638733 := bbase (se 3 (by rfl) ⟨494762, by rfl⟩ : syracuseStep 2638733 = 989525) (by norm_num)
theorem B2638757 : Blo 1758080 2638757 := bbase (se 4 (by rfl) ⟨247383, by rfl⟩ : syracuseStep 2638757 = 494767) (by norm_num)
theorem B3957677 : Blo 1758080 3957677 := bbase (se 3 (by rfl) ⟨742064, by rfl⟩ : syracuseStep 3957677 = 1484129) (by norm_num)
theorem B7513013 : Blo 1758080 7513013 := bbase (se 5 (by rfl) ⟨352172, by rfl⟩ : syracuseStep 7513013 = 704345) (by norm_num)
theorem B2638781 : Blo 1758080 2638781 := bbase (se 3 (by rfl) ⟨494771, by rfl⟩ : syracuseStep 2638781 = 989543) (by norm_num)
theorem B2638805 : Blo 1758080 2638805 := bbase (se 7 (by rfl) ⟨30923, by rfl⟩ : syracuseStep 2638805 = 61847) (by norm_num)
theorem B2638829 : Blo 1758080 2638829 := bbase (se 3 (by rfl) ⟨494780, by rfl⟩ : syracuseStep 2638829 = 989561) (by norm_num)
theorem B3957749 : Blo 1758080 3957749 := bbase (se 5 (by rfl) ⟨185519, by rfl⟩ : syracuseStep 3957749 = 371039) (by norm_num)
theorem B2638853 : Blo 1758080 2638853 := bbase (se 4 (by rfl) ⟨247392, by rfl⟩ : syracuseStep 2638853 = 494785) (by norm_num)
theorem B2638877 : Blo 1758080 2638877 := bbase (se 3 (by rfl) ⟨494789, by rfl⟩ : syracuseStep 2638877 = 989579) (by norm_num)
theorem B2638901 : Blo 1758080 2638901 := bbase (se 5 (by rfl) ⟨123698, by rfl⟩ : syracuseStep 2638901 = 247397) (by norm_num)
theorem B3957821 : Blo 1758080 3957821 := bbase (se 3 (by rfl) ⟨742091, by rfl⟩ : syracuseStep 3957821 = 1484183) (by norm_num)
theorem B2638925 : Blo 1758080 2638925 := bbase (se 3 (by rfl) ⟨494798, by rfl⟩ : syracuseStep 2638925 = 989597) (by norm_num)
theorem B2638949 : Blo 1758080 2638949 := bbase (se 4 (by rfl) ⟨247401, by rfl⟩ : syracuseStep 2638949 = 494803) (by norm_num)
theorem B5637221 : Blo 1758080 5637221 := bbase (se 4 (by rfl) ⟨528489, by rfl⟩ : syracuseStep 5637221 = 1056979) (by norm_num)
theorem B2638973 : Blo 1758080 2638973 := bbase (se 3 (by rfl) ⟨494807, by rfl⟩ : syracuseStep 2638973 = 989615) (by norm_num)
theorem B3957893 : Blo 1758080 3957893 := bbase (se 4 (by rfl) ⟨371052, by rfl⟩ : syracuseStep 3957893 = 742105) (by norm_num)
theorem B2638997 : Blo 1758080 2638997 := bbase (se 6 (by rfl) ⟨61851, by rfl⟩ : syracuseStep 2638997 = 123703) (by norm_num)
theorem B2639021 : Blo 1758080 2639021 := bbase (se 3 (by rfl) ⟨494816, by rfl⟩ : syracuseStep 2639021 = 989633) (by norm_num)
theorem B2639045 : Blo 1758080 2639045 := bbase (se 4 (by rfl) ⟨247410, by rfl⟩ : syracuseStep 2639045 = 494821) (by norm_num)
theorem B3957965 : Blo 1758080 3957965 := bbase (se 3 (by rfl) ⟨742118, by rfl⟩ : syracuseStep 3957965 = 1484237) (by norm_num)
theorem B2639069 : Blo 1758080 2639069 := bbase (se 3 (by rfl) ⟨494825, by rfl⟩ : syracuseStep 2639069 = 989651) (by norm_num)
theorem B2966773 : Blo 1758080 2966773 := bbase (se 5 (by rfl) ⟨139067, by rfl⟩ : syracuseStep 2966773 = 278135) (by norm_num)
theorem B2639093 : Blo 1758080 2639093 := bbase (se 5 (by rfl) ⟨123707, by rfl⟩ : syracuseStep 2639093 = 247415) (by norm_num)
theorem B2639117 : Blo 1758080 2639117 := bbase (se 3 (by rfl) ⟨494834, by rfl⟩ : syracuseStep 2639117 = 989669) (by norm_num)
theorem B3958037 : Blo 1758080 3958037 := bbase (se 6 (by rfl) ⟨92766, by rfl⟩ : syracuseStep 3958037 = 185533) (by norm_num)
theorem B2639141 : Blo 1758080 2639141 := bbase (se 4 (by rfl) ⟨247419, by rfl⟩ : syracuseStep 2639141 = 494839) (by norm_num)
theorem B2639165 : Blo 1758080 2639165 := bbase (se 3 (by rfl) ⟨494843, by rfl⟩ : syracuseStep 2639165 = 989687) (by norm_num)
theorem B2966861 : Blo 1758080 2966861 := bbase (se 3 (by rfl) ⟨556286, by rfl⟩ : syracuseStep 2966861 = 1112573) (by norm_num)
theorem B2639189 : Blo 1758080 2639189 := bbase (se 12 (by rfl) ⟨966, by rfl⟩ : syracuseStep 2639189 = 1933) (by norm_num)
theorem B3958109 : Blo 1758080 3958109 := bbase (se 3 (by rfl) ⟨742145, by rfl⟩ : syracuseStep 3958109 = 1484291) (by norm_num)
theorem B2639213 : Blo 1758080 2639213 := bbase (se 3 (by rfl) ⟨494852, by rfl⟩ : syracuseStep 2639213 = 989705) (by norm_num)
theorem B4752773 : Blo 1758080 4752773 := bbase (se 4 (by rfl) ⟨445572, by rfl⟩ : syracuseStep 4752773 = 891145) (by norm_num)
theorem B2639237 : Blo 1758080 2639237 := bbase (se 4 (by rfl) ⟨247428, by rfl⟩ : syracuseStep 2639237 = 494857) (by norm_num)
theorem B2639261 : Blo 1758080 2639261 := bbase (se 3 (by rfl) ⟨494861, by rfl⟩ : syracuseStep 2639261 = 989723) (by norm_num)
theorem B3958181 : Blo 1758080 3958181 := bbase (se 4 (by rfl) ⟨371079, by rfl⟩ : syracuseStep 3958181 = 742159) (by norm_num)
theorem B2639285 : Blo 1758080 2639285 := bbase (se 5 (by rfl) ⟨123716, by rfl⟩ : syracuseStep 2639285 = 247433) (by norm_num)
theorem B1877437 : Blo 1758080 1877437 := bbase (se 3 (by rfl) ⟨352019, by rfl⟩ : syracuseStep 1877437 = 704039) (by norm_num)
theorem B2966989 : Blo 1758080 2966989 := bbase (se 3 (by rfl) ⟨556310, by rfl⟩ : syracuseStep 2966989 = 1112621) (by norm_num)
theorem B2639309 : Blo 1758080 2639309 := bbase (se 3 (by rfl) ⟨494870, by rfl⟩ : syracuseStep 2639309 = 989741) (by norm_num)
theorem B2639333 : Blo 1758080 2639333 := bbase (se 4 (by rfl) ⟨247437, by rfl⟩ : syracuseStep 2639333 = 494875) (by norm_num)
theorem B3958253 : Blo 1758080 3958253 := bbase (se 3 (by rfl) ⟨742172, by rfl⟩ : syracuseStep 3958253 = 1484345) (by norm_num)
theorem B2639357 : Blo 1758080 2639357 := bbase (se 3 (by rfl) ⟨494879, by rfl⟩ : syracuseStep 2639357 = 989759) (by norm_num)
theorem B2639381 : Blo 1758080 2639381 := bbase (se 6 (by rfl) ⟨61860, by rfl⟩ : syracuseStep 2639381 = 123721) (by norm_num)
theorem B2967077 : Blo 1758080 2967077 := bbase (se 4 (by rfl) ⟨278163, by rfl⟩ : syracuseStep 2967077 = 556327) (by norm_num)
theorem B2639405 : Blo 1758080 2639405 := bbase (se 3 (by rfl) ⟨494888, by rfl⟩ : syracuseStep 2639405 = 989777) (by norm_num)
theorem B3958325 : Blo 1758080 3958325 := bbase (se 5 (by rfl) ⟨185546, by rfl⟩ : syracuseStep 3958325 = 371093) (by norm_num)
theorem B2639429 : Blo 1758080 2639429 := bbase (se 4 (by rfl) ⟨247446, by rfl⟩ : syracuseStep 2639429 = 494893) (by norm_num)
theorem B2639453 : Blo 1758080 2639453 := bbase (se 3 (by rfl) ⟨494897, by rfl⟩ : syracuseStep 2639453 = 989795) (by norm_num)
theorem B1877617 : Blo 1758080 1877617 := bbase (se 2 (by rfl) ⟨704106, by rfl⟩ : syracuseStep 1877617 = 1408213) (by norm_num)
theorem B10020469 : Blo 1758080 10020469 := bbase (se 5 (by rfl) ⟨469709, by rfl⟩ : syracuseStep 10020469 = 939419) (by norm_num)
theorem B2639477 : Blo 1758080 2639477 := bbase (se 5 (by rfl) ⟨123725, by rfl⟩ : syracuseStep 2639477 = 247451) (by norm_num)
theorem B3958397 : Blo 1758080 3958397 := bbase (se 3 (by rfl) ⟨742199, by rfl⟩ : syracuseStep 3958397 = 1484399) (by norm_num)
theorem B2639501 : Blo 1758080 2639501 := bbase (se 3 (by rfl) ⟨494906, by rfl⟩ : syracuseStep 2639501 = 989813) (by norm_num)
theorem B2967205 : Blo 1758080 2967205 := bbase (se 4 (by rfl) ⟨278175, by rfl⟩ : syracuseStep 2967205 = 556351) (by norm_num)
theorem B2639525 : Blo 1758080 2639525 := bbase (se 4 (by rfl) ⟨247455, by rfl⟩ : syracuseStep 2639525 = 494911) (by norm_num)
theorem B2033333 : Blo 1758080 2033333 := bbase (se 5 (by rfl) ⟨95312, by rfl⟩ : syracuseStep 2033333 = 190625) (by norm_num)
theorem B16910005 : Blo 1758080 16910005 := bbase (se 5 (by rfl) ⟨792656, by rfl⟩ : syracuseStep 16910005 = 1585313) (by norm_num)
theorem B2639549 : Blo 1758080 2639549 := bbase (se 3 (by rfl) ⟨494915, by rfl⟩ : syracuseStep 2639549 = 989831) (by norm_num)
theorem B3958469 : Blo 1758080 3958469 := bbase (se 4 (by rfl) ⟨371106, by rfl⟩ : syracuseStep 3958469 = 742213) (by norm_num)
theorem B2639573 : Blo 1758080 2639573 := bbase (se 7 (by rfl) ⟨30932, by rfl⟩ : syracuseStep 2639573 = 61865) (by norm_num)
theorem B4515557 : Blo 1758080 4515557 := bbase (se 4 (by rfl) ⟨423333, by rfl⟩ : syracuseStep 4515557 = 846667) (by norm_num)
theorem B2639597 : Blo 1758080 2639597 := bbase (se 3 (by rfl) ⟨494924, by rfl⟩ : syracuseStep 2639597 = 989849) (by norm_num)
theorem B2967293 : Blo 1758080 2967293 := bbase (se 3 (by rfl) ⟨556367, by rfl⟩ : syracuseStep 2967293 = 1112735) (by norm_num)
theorem B2639621 : Blo 1758080 2639621 := bbase (se 4 (by rfl) ⟨247464, by rfl⟩ : syracuseStep 2639621 = 494929) (by norm_num)
theorem B3958541 : Blo 1758080 3958541 := bbase (se 3 (by rfl) ⟨742226, by rfl⟩ : syracuseStep 3958541 = 1484453) (by norm_num)
theorem B2639645 : Blo 1758080 2639645 := bbase (se 3 (by rfl) ⟨494933, by rfl⟩ : syracuseStep 2639645 = 989867) (by norm_num)
theorem B2639669 : Blo 1758080 2639669 := bbase (se 5 (by rfl) ⟨123734, by rfl⟩ : syracuseStep 2639669 = 247469) (by norm_num)
theorem B3008333 : Blo 1758080 3008333 := bbase (se 3 (by rfl) ⟨564062, by rfl⟩ : syracuseStep 3008333 = 1128125) (by norm_num)
theorem B2639693 : Blo 1758080 2639693 := bbase (se 3 (by rfl) ⟨494942, by rfl⟩ : syracuseStep 2639693 = 989885) (by norm_num)
theorem B3958613 : Blo 1758080 3958613 := bbase (se 9 (by rfl) ⟨11597, by rfl⟩ : syracuseStep 3958613 = 23195) (by norm_num)
theorem B8906597 : Blo 1758080 8906597 := bbase (se 4 (by rfl) ⟨834993, by rfl⟩ : syracuseStep 8906597 = 1669987) (by norm_num)
theorem B2639717 : Blo 1758080 2639717 := bbase (se 4 (by rfl) ⟨247473, by rfl⟩ : syracuseStep 2639717 = 494947) (by norm_num)
theorem B2967421 : Blo 1758080 2967421 := bbase (se 3 (by rfl) ⟨556391, by rfl⟩ : syracuseStep 2967421 = 1112783) (by norm_num)
theorem B2639741 : Blo 1758080 2639741 := bbase (se 3 (by rfl) ⟨494951, by rfl⟩ : syracuseStep 2639741 = 989903) (by norm_num)
theorem B2639765 : Blo 1758080 2639765 := bbase (se 6 (by rfl) ⟨61869, by rfl⟩ : syracuseStep 2639765 = 123739) (by norm_num)
theorem B3958685 : Blo 1758080 3958685 := bbase (se 3 (by rfl) ⟨742253, by rfl⟩ : syracuseStep 3958685 = 1484507) (by norm_num)
theorem B2639789 : Blo 1758080 2639789 := bbase (se 3 (by rfl) ⟨494960, by rfl⟩ : syracuseStep 2639789 = 989921) (by norm_num)
theorem B2639813 : Blo 1758080 2639813 := bbase (se 4 (by rfl) ⟨247482, by rfl⟩ : syracuseStep 2639813 = 494965) (by norm_num)
theorem B4450261 : Blo 1758080 4450261 := bbase (se 7 (by rfl) ⟨52151, by rfl⟩ : syracuseStep 4450261 = 104303) (by norm_num)
theorem B2967509 : Blo 1758080 2967509 := bbase (se 7 (by rfl) ⟨34775, by rfl⟩ : syracuseStep 2967509 = 69551) (by norm_num)
theorem B2639837 : Blo 1758080 2639837 := bbase (se 3 (by rfl) ⟨494969, by rfl⟩ : syracuseStep 2639837 = 989939) (by norm_num)
theorem B3958757 : Blo 1758080 3958757 := bbase (se 4 (by rfl) ⟨371133, by rfl⟩ : syracuseStep 3958757 = 742267) (by norm_num)
theorem B2639861 : Blo 1758080 2639861 := bbase (se 5 (by rfl) ⟨123743, by rfl⟩ : syracuseStep 2639861 = 247487) (by norm_num)
theorem B5007365 : Blo 1758080 5007365 := bbase (se 4 (by rfl) ⟨469440, by rfl⟩ : syracuseStep 5007365 = 938881) (by norm_num)
theorem B2639885 : Blo 1758080 2639885 := bbase (se 3 (by rfl) ⟨494978, by rfl⟩ : syracuseStep 2639885 = 989957) (by norm_num)
theorem B19023893 : Blo 1758080 19023893 := bbase (se 6 (by rfl) ⟨445872, by rfl⟩ : syracuseStep 19023893 = 891745) (by norm_num)
theorem B2639909 : Blo 1758080 2639909 := bbase (se 4 (by rfl) ⟨247491, by rfl⟩ : syracuseStep 2639909 = 494983) (by norm_num)
theorem B1878061 : Blo 1758080 1878061 := bbase (se 3 (by rfl) ⟨352136, by rfl⟩ : syracuseStep 1878061 = 704273) (by norm_num)
theorem B3958829 : Blo 1758080 3958829 := bbase (se 3 (by rfl) ⟨742280, by rfl⟩ : syracuseStep 3958829 = 1484561) (by norm_num)
theorem B2639933 : Blo 1758080 2639933 := bbase (se 3 (by rfl) ⟨494987, by rfl⟩ : syracuseStep 2639933 = 989975) (by norm_num)
theorem B4450373 : Blo 1758080 4450373 := bbase (se 4 (by rfl) ⟨417222, by rfl⟩ : syracuseStep 4450373 = 834445) (by norm_num)
theorem B2967637 : Blo 1758080 2967637 := bbase (se 8 (by rfl) ⟨17388, by rfl⟩ : syracuseStep 2967637 = 34777) (by norm_num)
theorem B2639957 : Blo 1758080 2639957 := bbase (se 8 (by rfl) ⟨15468, by rfl⟩ : syracuseStep 2639957 = 30937) (by norm_num)
theorem B2639981 : Blo 1758080 2639981 := bbase (se 3 (by rfl) ⟨494996, by rfl⟩ : syracuseStep 2639981 = 989993) (by norm_num)
theorem B3958901 : Blo 1758080 3958901 := bbase (se 5 (by rfl) ⟨185573, by rfl⟩ : syracuseStep 3958901 = 371147) (by norm_num)
theorem B2640005 : Blo 1758080 2640005 := bbase (se 4 (by rfl) ⟨247500, by rfl⟩ : syracuseStep 2640005 = 495001) (by norm_num)
theorem B2640029 : Blo 1758080 2640029 := bbase (se 3 (by rfl) ⟨495005, by rfl⟩ : syracuseStep 2640029 = 990011) (by norm_num)
theorem B1878185 : Blo 1758080 1878185 := bbase (se 2 (by rfl) ⟨704319, by rfl⟩ : syracuseStep 1878185 = 1408639) (by norm_num)
theorem B2967725 : Blo 1758080 2967725 := bbase (se 3 (by rfl) ⟨556448, by rfl⟩ : syracuseStep 2967725 = 1112897) (by norm_num)
theorem B2640053 : Blo 1758080 2640053 := bbase (se 5 (by rfl) ⟨123752, by rfl⟩ : syracuseStep 2640053 = 247505) (by norm_num)
theorem B3958973 : Blo 1758080 3958973 := bbase (se 3 (by rfl) ⟨742307, by rfl⟩ : syracuseStep 3958973 = 1484615) (by norm_num)
theorem B2640077 : Blo 1758080 2640077 := bbase (se 3 (by rfl) ⟨495014, by rfl⟩ : syracuseStep 2640077 = 990029) (by norm_num)
theorem B2640101 : Blo 1758080 2640101 := bbase (se 4 (by rfl) ⟨247509, by rfl⟩ : syracuseStep 2640101 = 495019) (by norm_num)
theorem B4450565 : Blo 1758080 4450565 := bbase (se 4 (by rfl) ⟨417240, by rfl⟩ : syracuseStep 4450565 = 834481) (by norm_num)
theorem B3959045 : Blo 1758080 3959045 := bbase (se 4 (by rfl) ⟨371160, by rfl⟩ : syracuseStep 3959045 = 742321) (by norm_num)
theorem B3565853 : Blo 1758080 3565853 := bbase (se 3 (by rfl) ⟨668597, by rfl⟩ : syracuseStep 3565853 = 1337195) (by norm_num)
theorem B2967853 : Blo 1758080 2967853 := bbase (se 3 (by rfl) ⟨556472, by rfl⟩ : syracuseStep 2967853 = 1112945) (by norm_num)
theorem B4753733 : Blo 1758080 4753733 := bbase (se 4 (by rfl) ⟨445662, by rfl⟩ : syracuseStep 4753733 = 891325) (by norm_num)
theorem B3213637 : Blo 1758080 3213637 := bbase (se 4 (by rfl) ⟨301278, by rfl⟩ : syracuseStep 3213637 = 602557) (by norm_num)
theorem B3565901 : Blo 1758080 3565901 := bbase (se 3 (by rfl) ⟨668606, by rfl⟩ : syracuseStep 3565901 = 1337213) (by norm_num)
theorem B3959117 : Blo 1758080 3959117 := bbase (se 3 (by rfl) ⟨742334, by rfl⟩ : syracuseStep 3959117 = 1484669) (by norm_num)
theorem B13363541 : Blo 1758080 13363541 := bbase (se 10 (by rfl) ⟨19575, by rfl⟩ : syracuseStep 13363541 = 39151) (by norm_num)
theorem B2967941 : Blo 1758080 2967941 := bbase (se 4 (by rfl) ⟨278244, by rfl⟩ : syracuseStep 2967941 = 556489) (by norm_num)
theorem B3959189 : Blo 1758080 3959189 := bbase (se 6 (by rfl) ⟨92793, by rfl⟩ : syracuseStep 3959189 = 185587) (by norm_num)
theorem B1878437 : Blo 1758080 1878437 := bbase (se 4 (by rfl) ⟨176103, by rfl⟩ : syracuseStep 1878437 = 352207) (by norm_num)
theorem B5638565 : Blo 1758080 5638565 := bbase (se 4 (by rfl) ⟨528615, by rfl⟩ : syracuseStep 5638565 = 1057231) (by norm_num)
theorem B15034805 : Blo 1758080 15034805 := bbase (se 5 (by rfl) ⟨704756, by rfl⟩ : syracuseStep 15034805 = 1409513) (by norm_num)
theorem B3959261 : Blo 1758080 3959261 := bbase (se 3 (by rfl) ⟨742361, by rfl⟩ : syracuseStep 3959261 = 1484723) (by norm_num)
theorem B5933573 : Blo 1758080 5933573 := bbase (se 4 (by rfl) ⟨556272, by rfl⟩ : syracuseStep 5933573 = 1112545) (by norm_num)
theorem B2968069 : Blo 1758080 2968069 := bbase (se 4 (by rfl) ⟨278256, by rfl⟩ : syracuseStep 2968069 = 556513) (by norm_num)
theorem B3959333 : Blo 1758080 3959333 := bbase (se 4 (by rfl) ⟨371187, by rfl⟩ : syracuseStep 3959333 = 742375) (by norm_num)
theorem B2673197 : Blo 1758080 2673197 := bbase (se 3 (by rfl) ⟨501224, by rfl⟩ : syracuseStep 2673197 = 1002449) (by norm_num)
theorem B15026741 : Blo 1758080 15026741 := bbase (se 5 (by rfl) ⟨704378, by rfl⟩ : syracuseStep 15026741 = 1408757) (by norm_num)
theorem B5351989 : Blo 1758080 5351989 := bbase (se 5 (by rfl) ⟨250874, by rfl⟩ : syracuseStep 5351989 = 501749) (by norm_num)
theorem B4450909 : Blo 1758080 4450909 := bbase (se 3 (by rfl) ⟨834545, by rfl⟩ : syracuseStep 4450909 = 1669091) (by norm_num)
theorem B2968157 : Blo 1758080 2968157 := bbase (se 3 (by rfl) ⟨556529, by rfl⟩ : syracuseStep 2968157 = 1113059) (by norm_num)
theorem B3959405 : Blo 1758080 3959405 := bbase (se 3 (by rfl) ⟨742388, by rfl⟩ : syracuseStep 3959405 = 1484777) (by norm_num)
theorem B6679205 : Blo 1758080 6679205 := bbase (se 4 (by rfl) ⟨626175, by rfl⟩ : syracuseStep 6679205 = 1252351) (by norm_num)
theorem B3959477 : Blo 1758080 3959477 := bbase (se 5 (by rfl) ⟨185600, by rfl⟩ : syracuseStep 3959477 = 371201) (by norm_num)
theorem B3386053 : Blo 1758080 3386053 := bbase (se 4 (by rfl) ⟨317442, by rfl⟩ : syracuseStep 3386053 = 634885) (by norm_num)
theorem B4451021 : Blo 1758080 4451021 := bbase (se 3 (by rfl) ⟨834566, by rfl⟩ : syracuseStep 4451021 = 1669133) (by norm_num)
theorem B2968285 : Blo 1758080 2968285 := bbase (se 3 (by rfl) ⟨556553, by rfl⟩ : syracuseStep 2968285 = 1113107) (by norm_num)
theorem B13355765 : Blo 1758080 13355765 := bbase (se 5 (by rfl) ⟨626051, by rfl⟩ : syracuseStep 13355765 = 1252103) (by norm_num)
theorem B3959549 : Blo 1758080 3959549 := bbase (se 3 (by rfl) ⟨742415, by rfl⟩ : syracuseStep 3959549 = 1484831) (by norm_num)
theorem B2255629 : Blo 1758080 2255629 := bbase (se 3 (by rfl) ⟨422930, by rfl⟩ : syracuseStep 2255629 = 845861) (by norm_num)
theorem B2968373 : Blo 1758080 2968373 := bbase (se 5 (by rfl) ⟨139142, by rfl⟩ : syracuseStep 2968373 = 278285) (by norm_num)
theorem B3566405 : Blo 1758080 3566405 := bbase (se 4 (by rfl) ⟨334350, by rfl⟩ : syracuseStep 3566405 = 668701) (by norm_num)
theorem B3959621 : Blo 1758080 3959621 := bbase (se 4 (by rfl) ⟨371214, by rfl⟩ : syracuseStep 3959621 = 742429) (by norm_num)
theorem B1878881 : Blo 1758080 1878881 := bbase (se 2 (by rfl) ⟨704580, by rfl⟩ : syracuseStep 1878881 = 1409161) (by norm_num)
theorem B8457061 : Blo 1758080 8457061 := bbase (se 4 (by rfl) ⟨792849, by rfl⟩ : syracuseStep 8457061 = 1585699) (by norm_num)
theorem B2255737 : Blo 1758080 2255737 := bbase (se 2 (by rfl) ⟨845901, by rfl⟩ : syracuseStep 2255737 = 1691803) (by norm_num)
theorem B4451213 : Blo 1758080 4451213 := bbase (se 3 (by rfl) ⟨834602, by rfl⟩ : syracuseStep 4451213 = 1669205) (by norm_num)
theorem B3959693 : Blo 1758080 3959693 := bbase (se 3 (by rfl) ⟨742442, by rfl⟩ : syracuseStep 3959693 = 1484885) (by norm_num)
theorem B12675989 : Blo 1758080 12675989 := bbase (se 6 (by rfl) ⟨297093, by rfl⟩ : syracuseStep 12675989 = 594187) (by norm_num)
theorem B5934005 : Blo 1758080 5934005 := bbase (se 5 (by rfl) ⟨278156, by rfl⟩ : syracuseStep 5934005 = 556313) (by norm_num)
theorem B2968501 : Blo 1758080 2968501 := bbase (se 5 (by rfl) ⟨139148, by rfl⟩ : syracuseStep 2968501 = 278297) (by norm_num)
theorem B6679493 : Blo 1758080 6679493 := bbase (se 4 (by rfl) ⟨626202, by rfl⟩ : syracuseStep 6679493 = 1252405) (by norm_num)
theorem B3959765 : Blo 1758080 3959765 := bbase (se 7 (by rfl) ⟨46403, by rfl⟩ : syracuseStep 3959765 = 92807) (by norm_num)
theorem B2968589 : Blo 1758080 2968589 := bbase (se 3 (by rfl) ⟨556610, by rfl⟩ : syracuseStep 2968589 = 1113221) (by norm_num)
theorem B3009565 : Blo 1758080 3009565 := bbase (se 3 (by rfl) ⟨564293, by rfl⟩ : syracuseStep 3009565 = 1128587) (by norm_num)
theorem B3959837 : Blo 1758080 3959837 := bbase (se 3 (by rfl) ⟨742469, by rfl⟩ : syracuseStep 3959837 = 1484939) (by norm_num)
theorem B3755045 : Blo 1758080 3755045 := bbase (se 4 (by rfl) ⟨352035, by rfl⟩ : syracuseStep 3755045 = 704071) (by norm_num)
theorem B1879129 : Blo 1758080 1879129 := bbase (se 2 (by rfl) ⟨704673, by rfl⟩ : syracuseStep 1879129 = 1409347) (by norm_num)
theorem B3959909 : Blo 1758080 3959909 := bbase (se 4 (by rfl) ⟨371241, by rfl⟩ : syracuseStep 3959909 = 742483) (by norm_num)
theorem B8907893 : Blo 1758080 8907893 := bbase (se 5 (by rfl) ⟨417557, by rfl⟩ : syracuseStep 8907893 = 835115) (by norm_num)
theorem B2968717 : Blo 1758080 2968717 := bbase (se 3 (by rfl) ⟨556634, by rfl⟩ : syracuseStep 2968717 = 1113269) (by norm_num)
theorem B5008549 : Blo 1758080 5008549 := bbase (se 4 (by rfl) ⟨469551, by rfl⟩ : syracuseStep 5008549 = 939103) (by norm_num)
theorem B3959981 : Blo 1758080 3959981 := bbase (se 3 (by rfl) ⟨742496, by rfl⟩ : syracuseStep 3959981 = 1484993) (by norm_num)
theorem B4451557 : Blo 1758080 4451557 := bbase (se 4 (by rfl) ⟨417333, by rfl⟩ : syracuseStep 4451557 = 834667) (by norm_num)
theorem B2968805 : Blo 1758080 2968805 := bbase (se 4 (by rfl) ⟨278325, by rfl⟩ : syracuseStep 2968805 = 556651) (by norm_num)
theorem B4582637 : Blo 1758080 4582637 := bbase (se 3 (by rfl) ⟨859244, by rfl⟩ : syracuseStep 4582637 = 1718489) (by norm_num)
theorem B3960053 : Blo 1758080 3960053 := bbase (se 5 (by rfl) ⟨185627, by rfl⟩ : syracuseStep 3960053 = 371255) (by norm_num)
theorem B3960125 : Blo 1758080 3960125 := bbase (se 3 (by rfl) ⟨742523, by rfl⟩ : syracuseStep 3960125 = 1485047) (by norm_num)
theorem B5008709 : Blo 1758080 5008709 := bbase (se 4 (by rfl) ⟨469566, by rfl⟩ : syracuseStep 5008709 = 939133) (by norm_num)
theorem B4451669 : Blo 1758080 4451669 := bbase (se 11 (by rfl) ⟨3260, by rfl⟩ : syracuseStep 4451669 = 6521) (by norm_num)
theorem B5934437 : Blo 1758080 5934437 := bbase (se 4 (by rfl) ⟨556353, by rfl⟩ : syracuseStep 5934437 = 1112707) (by norm_num)
theorem B2968933 : Blo 1758080 2968933 := bbase (se 4 (by rfl) ⟨278337, by rfl⟩ : syracuseStep 2968933 = 556675) (by norm_num)
theorem B8449429 : Blo 1758080 8449429 := bbase (se 6 (by rfl) ⟨198033, by rfl⟩ : syracuseStep 8449429 = 396067) (by norm_num)
theorem B3755413 : Blo 1758080 3755413 := bbase (se 6 (by rfl) ⟨88017, by rfl⟩ : syracuseStep 3755413 = 176035) (by norm_num)
theorem B18050485 : Blo 1758080 18050485 := bbase (se 5 (by rfl) ⟨846116, by rfl⟩ : syracuseStep 18050485 = 1692233) (by norm_num)
theorem B2969021 : Blo 1758080 2969021 := bbase (se 3 (by rfl) ⟨556691, by rfl⟩ : syracuseStep 2969021 = 1113383) (by norm_num)
theorem B1977853 : Blo 1758080 1977853 := bbase (se 3 (by rfl) ⟨370847, by rfl⟩ : syracuseStep 1977853 = 741695) (by norm_num)
theorem B3526141 : Blo 1758080 3526141 := bbase (se 3 (by rfl) ⟨661151, by rfl⟩ : syracuseStep 3526141 = 1322303) (by norm_num)
theorem B4451861 : Blo 1758080 4451861 := bbase (se 6 (by rfl) ⟨104340, by rfl⟩ : syracuseStep 4451861 = 208681) (by norm_num)
theorem B3337757 : Blo 1758080 3337757 := bbase (se 3 (by rfl) ⟨625829, by rfl⟩ : syracuseStep 3337757 = 1251659) (by norm_num)
theorem B1977889 : Blo 1758080 1977889 := bbase (se 2 (by rfl) ⟨741708, by rfl⟩ : syracuseStep 1977889 = 1483417) (by norm_num)
theorem B5008949 : Blo 1758080 5008949 := bbase (se 5 (by rfl) ⟨234794, by rfl⟩ : syracuseStep 5008949 = 469589) (by norm_num)
theorem B10022453 : Blo 1758080 10022453 := bbase (se 5 (by rfl) ⟨469802, by rfl⟩ : syracuseStep 10022453 = 939605) (by norm_num)
theorem B2969149 : Blo 1758080 2969149 := bbase (se 3 (by rfl) ⟨556715, by rfl⟩ : syracuseStep 2969149 = 1113431) (by norm_num)
theorem B1977925 : Blo 1758080 1977925 := bbase (se 4 (by rfl) ⟨185430, by rfl⟩ : syracuseStep 1977925 = 370861) (by norm_num)
theorem B1977961 : Blo 1758080 1977961 := bbase (se 2 (by rfl) ⟨741735, by rfl⟩ : syracuseStep 1977961 = 1483471) (by norm_num)
theorem B1977997 : Blo 1758080 1977997 := bbase (se 3 (by rfl) ⟨370874, by rfl⟩ : syracuseStep 1977997 = 741749) (by norm_num)
theorem B3616397 : Blo 1758080 3616397 := bbase (se 3 (by rfl) ⟨678074, by rfl⟩ : syracuseStep 3616397 = 1356149) (by norm_num)
theorem B2969237 : Blo 1758080 2969237 := bbase (se 6 (by rfl) ⟨69591, by rfl⟩ : syracuseStep 2969237 = 139183) (by norm_num)
theorem B1978033 : Blo 1758080 1978033 := bbase (se 2 (by rfl) ⟨741762, by rfl⟩ : syracuseStep 1978033 = 1483525) (by norm_num)
theorem B1978069 : Blo 1758080 1978069 := bbase (se 7 (by rfl) ⟨23180, by rfl⟩ : syracuseStep 1978069 = 46361) (by norm_num)
theorem B3010277 : Blo 1758080 3010277 := bbase (se 4 (by rfl) ⟨282213, by rfl⟩ : syracuseStep 3010277 = 564427) (by norm_num)
theorem B5009141 : Blo 1758080 5009141 := bbase (se 5 (by rfl) ⟨234803, by rfl⟩ : syracuseStep 5009141 = 469607) (by norm_num)
theorem B1978105 : Blo 1758080 1978105 := bbase (se 2 (by rfl) ⟨741789, by rfl⟩ : syracuseStep 1978105 = 1483579) (by norm_num)
theorem B5934869 : Blo 1758080 5934869 := bbase (se 6 (by rfl) ⟨139098, by rfl⟩ : syracuseStep 5934869 = 278197) (by norm_num)
theorem B2969365 : Blo 1758080 2969365 := bbase (se 6 (by rfl) ⟨69594, by rfl⟩ : syracuseStep 2969365 = 139189) (by norm_num)
theorem B9031445 : Blo 1758080 9031445 := bbase (se 6 (by rfl) ⟨211674, by rfl⟩ : syracuseStep 9031445 = 423349) (by norm_num)
theorem B1978141 : Blo 1758080 1978141 := bbase (se 3 (by rfl) ⟨370901, by rfl⟩ : syracuseStep 1978141 = 741803) (by norm_num)
theorem B1978177 : Blo 1758080 1978177 := bbase (se 2 (by rfl) ⟨741816, by rfl⟩ : syracuseStep 1978177 = 1483633) (by norm_num)
theorem B1978213 : Blo 1758080 1978213 := bbase (se 4 (by rfl) ⟨185457, by rfl⟩ : syracuseStep 1978213 = 370915) (by norm_num)
theorem B4452205 : Blo 1758080 4452205 := bbase (se 3 (by rfl) ⟨834788, by rfl⟩ : syracuseStep 4452205 = 1669577) (by norm_num)
theorem B2969453 : Blo 1758080 2969453 := bbase (se 3 (by rfl) ⟨556772, by rfl⟩ : syracuseStep 2969453 = 1113545) (by norm_num)
theorem B1978249 : Blo 1758080 1978249 := bbase (se 2 (by rfl) ⟨741843, by rfl⟩ : syracuseStep 1978249 = 1483687) (by norm_num)
theorem B1978285 : Blo 1758080 1978285 := bbase (se 3 (by rfl) ⟨370928, by rfl⟩ : syracuseStep 1978285 = 741857) (by norm_num)
theorem B5713861 : Blo 1758080 5713861 := bbase (se 4 (by rfl) ⟨535674, by rfl⟩ : syracuseStep 5713861 = 1071349) (by norm_num)
theorem B1978321 : Blo 1758080 1978321 := bbase (se 2 (by rfl) ⟨741870, by rfl⟩ : syracuseStep 1978321 = 1483741) (by norm_num)
theorem B4452317 : Blo 1758080 4452317 := bbase (se 3 (by rfl) ⟨834809, by rfl⟩ : syracuseStep 4452317 = 1669619) (by norm_num)
theorem B2969581 : Blo 1758080 2969581 := bbase (se 3 (by rfl) ⟨556796, by rfl⟩ : syracuseStep 2969581 = 1113593) (by norm_num)
theorem B1978357 : Blo 1758080 1978357 := bbase (se 5 (by rfl) ⟨92735, by rfl⟩ : syracuseStep 1978357 = 185471) (by norm_num)
theorem B11276309 : Blo 1758080 11276309 := bbase (se 6 (by rfl) ⟨264288, by rfl⟩ : syracuseStep 11276309 = 528577) (by norm_num)
theorem B1978393 : Blo 1758080 1978393 := bbase (se 2 (by rfl) ⟨741897, by rfl⟩ : syracuseStep 1978393 = 1483795) (by norm_num)
theorem B1978429 : Blo 1758080 1978429 := bbase (se 3 (by rfl) ⟨370955, by rfl⟩ : syracuseStep 1978429 = 741911) (by norm_num)
theorem B2969669 : Blo 1758080 2969669 := bbase (se 4 (by rfl) ⟨278406, by rfl⟩ : syracuseStep 2969669 = 556813) (by norm_num)
theorem B1978465 : Blo 1758080 1978465 := bbase (se 2 (by rfl) ⟨741924, by rfl⟩ : syracuseStep 1978465 = 1483849) (by norm_num)
theorem B6680677 : Blo 1758080 6680677 := bbase (se 4 (by rfl) ⟨626313, by rfl⟩ : syracuseStep 6680677 = 1252627) (by norm_num)
theorem B1978501 : Blo 1758080 1978501 := bbase (se 4 (by rfl) ⟨185484, by rfl⟩ : syracuseStep 1978501 = 370969) (by norm_num)
theorem B7516309 : Blo 1758080 7516309 := bbase (se 6 (by rfl) ⟨176163, by rfl⟩ : syracuseStep 7516309 = 352327) (by norm_num)
theorem B4452509 : Blo 1758080 4452509 := bbase (se 3 (by rfl) ⟨834845, by rfl⟩ : syracuseStep 4452509 = 1669691) (by norm_num)
theorem B1929377 : Blo 1758080 1929377 := bbase (se 2 (by rfl) ⟨723516, by rfl⟩ : syracuseStep 1929377 = 1447033) (by norm_num)
theorem B1978537 : Blo 1758080 1978537 := bbase (se 2 (by rfl) ⟨741951, by rfl⟩ : syracuseStep 1978537 = 1483903) (by norm_num)
theorem B12857525 : Blo 1758080 12857525 := bbase (se 5 (by rfl) ⟨602696, by rfl⟩ : syracuseStep 12857525 = 1205393) (by norm_num)
theorem B5935301 : Blo 1758080 5935301 := bbase (se 4 (by rfl) ⟨556434, by rfl⟩ : syracuseStep 5935301 = 1112869) (by norm_num)
theorem B2969797 : Blo 1758080 2969797 := bbase (se 4 (by rfl) ⟨278418, by rfl⟩ : syracuseStep 2969797 = 556837) (by norm_num)
theorem B1978573 : Blo 1758080 1978573 := bbase (se 3 (by rfl) ⟨370982, by rfl⟩ : syracuseStep 1978573 = 741965) (by norm_num)
theorem B1978609 : Blo 1758080 1978609 := bbase (se 2 (by rfl) ⟨741978, by rfl⟩ : syracuseStep 1978609 = 1483957) (by norm_num)
theorem B2674949 : Blo 1758080 2674949 := bbase (se 4 (by rfl) ⟨250776, by rfl⟩ : syracuseStep 2674949 = 501553) (by norm_num)
theorem B3338509 : Blo 1758080 3338509 := bbase (se 3 (by rfl) ⟨625970, by rfl⟩ : syracuseStep 3338509 = 1251941) (by norm_num)
theorem B1978645 : Blo 1758080 1978645 := bbase (se 6 (by rfl) ⟨46374, by rfl⟩ : syracuseStep 1978645 = 92749) (by norm_num)
theorem B2855197 : Blo 1758080 2855197 := bbase (se 3 (by rfl) ⟨535349, by rfl⟩ : syracuseStep 2855197 = 1070699) (by norm_num)
theorem B2969885 : Blo 1758080 2969885 := bbase (se 3 (by rfl) ⟨556853, by rfl⟩ : syracuseStep 2969885 = 1113707) (by norm_num)
theorem B1978681 : Blo 1758080 1978681 := bbase (se 2 (by rfl) ⟨742005, by rfl⟩ : syracuseStep 1978681 = 1484011) (by norm_num)
theorem B1978717 : Blo 1758080 1978717 := bbase (se 3 (by rfl) ⟨371009, by rfl⟩ : syracuseStep 1978717 = 742019) (by norm_num)
theorem B1978753 : Blo 1758080 1978753 := bbase (se 2 (by rfl) ⟨742032, by rfl⟩ : syracuseStep 1978753 = 1484065) (by norm_num)
theorem B8909189 : Blo 1758080 8909189 := bbase (se 4 (by rfl) ⟨835236, by rfl⟩ : syracuseStep 8909189 = 1670473) (by norm_num)
theorem B4010381 : Blo 1758080 4010381 := bbase (se 3 (by rfl) ⟨751946, by rfl⟩ : syracuseStep 4010381 = 1503893) (by norm_num)
theorem B6680981 : Blo 1758080 6680981 := bbase (se 6 (by rfl) ⟨156585, by rfl⟩ : syracuseStep 6680981 = 313171) (by norm_num)
theorem B3338653 : Blo 1758080 3338653 := bbase (se 3 (by rfl) ⟨625997, by rfl⟩ : syracuseStep 3338653 = 1251995) (by norm_num)
theorem B2970013 : Blo 1758080 2970013 := bbase (se 3 (by rfl) ⟨556877, by rfl⟩ : syracuseStep 2970013 = 1113755) (by norm_num)
theorem B1978789 : Blo 1758080 1978789 := bbase (se 4 (by rfl) ⟨185511, by rfl⟩ : syracuseStep 1978789 = 371023) (by norm_num)
theorem B12038581 : Blo 1758080 12038581 := bbase (se 5 (by rfl) ⟨564308, by rfl⟩ : syracuseStep 12038581 = 1128617) (by norm_num)
theorem B1978825 : Blo 1758080 1978825 := bbase (se 2 (by rfl) ⟨742059, by rfl⟩ : syracuseStep 1978825 = 1484119) (by norm_num)
theorem B5714405 : Blo 1758080 5714405 := bbase (se 4 (by rfl) ⟨535725, by rfl⟩ : syracuseStep 5714405 = 1071451) (by norm_num)
theorem B1978861 : Blo 1758080 1978861 := bbase (se 3 (by rfl) ⟨371036, by rfl⟩ : syracuseStep 1978861 = 742073) (by norm_num)
theorem B4452853 : Blo 1758080 4452853 := bbase (se 5 (by rfl) ⟨208727, by rfl⟩ : syracuseStep 4452853 = 417455) (by norm_num)
theorem B2970101 : Blo 1758080 2970101 := bbase (se 5 (by rfl) ⟨139223, by rfl⟩ : syracuseStep 2970101 = 278447) (by norm_num)
theorem B5632517 : Blo 1758080 5632517 := bbase (se 4 (by rfl) ⟨528048, by rfl⟩ : syracuseStep 5632517 = 1056097) (by norm_num)
theorem B1978897 : Blo 1758080 1978897 := bbase (se 2 (by rfl) ⟨742086, by rfl⟩ : syracuseStep 1978897 = 1484173) (by norm_num)
theorem B1978933 : Blo 1758080 1978933 := bbase (se 5 (by rfl) ⟨92762, by rfl⟩ : syracuseStep 1978933 = 185525) (by norm_num)
theorem B3338813 : Blo 1758080 3338813 := bbase (se 3 (by rfl) ⟨626027, by rfl⟩ : syracuseStep 3338813 = 1252055) (by norm_num)
theorem B1978969 : Blo 1758080 1978969 := bbase (se 2 (by rfl) ⟨742113, by rfl⟩ : syracuseStep 1978969 = 1484227) (by norm_num)
theorem B2503261 : Blo 1758080 2503261 := bbase (se 3 (by rfl) ⟨469361, by rfl⟩ : syracuseStep 2503261 = 938723) (by norm_num)
theorem B4452965 : Blo 1758080 4452965 := bbase (se 4 (by rfl) ⟨417465, by rfl⟩ : syracuseStep 4452965 = 834931) (by norm_num)
theorem B5935733 : Blo 1758080 5935733 := bbase (se 5 (by rfl) ⟨278237, by rfl⟩ : syracuseStep 5935733 = 556475) (by norm_num)
theorem B1979005 : Blo 1758080 1979005 := bbase (se 3 (by rfl) ⟨371063, by rfl⟩ : syracuseStep 1979005 = 742127) (by norm_num)
theorem B1979041 : Blo 1758080 1979041 := bbase (se 2 (by rfl) ⟨742140, by rfl⟩ : syracuseStep 1979041 = 1484281) (by norm_num)
theorem B13718197 : Blo 1758080 13718197 := bbase (se 5 (by rfl) ⟨643040, by rfl⟩ : syracuseStep 13718197 = 1286081) (by norm_num)
theorem B1979077 : Blo 1758080 1979077 := bbase (se 4 (by rfl) ⟨185538, by rfl⟩ : syracuseStep 1979077 = 371077) (by norm_num)
theorem B3338957 : Blo 1758080 3338957 := bbase (se 3 (by rfl) ⟨626054, by rfl⟩ : syracuseStep 3338957 = 1252109) (by norm_num)
theorem B2503381 : Blo 1758080 2503381 := bbase (se 7 (by rfl) ⟨29336, by rfl⟩ : syracuseStep 2503381 = 58673) (by norm_num)
theorem B5010133 : Blo 1758080 5010133 := bbase (se 7 (by rfl) ⟨58712, by rfl⟩ : syracuseStep 5010133 = 117425) (by norm_num)
theorem B2257625 : Blo 1758080 2257625 := bbase (se 2 (by rfl) ⟨846609, by rfl⟩ : syracuseStep 2257625 = 1693219) (by norm_num)
theorem B1979113 : Blo 1758080 1979113 := bbase (se 2 (by rfl) ⟨742167, by rfl⟩ : syracuseStep 1979113 = 1484335) (by norm_num)
theorem B1782529 : Blo 1758080 1782529 := bbase (se 2 (by rfl) ⟨668448, by rfl⟩ : syracuseStep 1782529 = 1336897) (by norm_num)
theorem B1979149 : Blo 1758080 1979149 := bbase (se 3 (by rfl) ⟨371090, by rfl⟩ : syracuseStep 1979149 = 742181) (by norm_num)
theorem B8901413 : Blo 1758080 8901413 := bbase (se 4 (by rfl) ⟨834507, by rfl⟩ : syracuseStep 8901413 = 1669015) (by norm_num)
theorem B4453157 : Blo 1758080 4453157 := bbase (se 4 (by rfl) ⟨417483, by rfl⟩ : syracuseStep 4453157 = 834967) (by norm_num)
theorem B1979185 : Blo 1758080 1979185 := bbase (se 2 (by rfl) ⟨742194, by rfl⟩ : syracuseStep 1979185 = 1484389) (by norm_num)
theorem B2503477 : Blo 1758080 2503477 := bbase (se 5 (by rfl) ⟨117350, by rfl⟩ : syracuseStep 2503477 = 234701) (by norm_num)
theorem B1979221 : Blo 1758080 1979221 := bbase (se 9 (by rfl) ⟨5798, by rfl⟩ : syracuseStep 1979221 = 11597) (by norm_num)
theorem B12678005 : Blo 1758080 12678005 := bbase (se 5 (by rfl) ⟨594281, by rfl⟩ : syracuseStep 12678005 = 1188563) (by norm_num)
theorem B3756917 : Blo 1758080 3756917 := bbase (se 5 (by rfl) ⟨176105, by rfl⟩ : syracuseStep 3756917 = 352211) (by norm_num)
theorem B1979257 : Blo 1758080 1979257 := bbase (se 2 (by rfl) ⟨742221, by rfl⟩ : syracuseStep 1979257 = 1484443) (by norm_num)
theorem B2675581 : Blo 1758080 2675581 := bbase (se 3 (by rfl) ⟨501671, by rfl⟩ : syracuseStep 2675581 = 1003343) (by norm_num)
theorem B1979293 : Blo 1758080 1979293 := bbase (se 3 (by rfl) ⟨371117, by rfl⟩ : syracuseStep 1979293 = 742235) (by norm_num)
theorem B1979329 : Blo 1758080 1979329 := bbase (se 2 (by rfl) ⟨742248, by rfl⟩ : syracuseStep 1979329 = 1484497) (by norm_num)
theorem B1979365 : Blo 1758080 1979365 := bbase (se 4 (by rfl) ⟨185565, by rfl⟩ : syracuseStep 1979365 = 371131) (by norm_num)
theorem B3339245 : Blo 1758080 3339245 := bbase (se 3 (by rfl) ⟨626108, by rfl⟩ : syracuseStep 3339245 = 1252217) (by norm_num)
theorem B3757061 : Blo 1758080 3757061 := bbase (se 4 (by rfl) ⟨352224, by rfl⟩ : syracuseStep 3757061 = 704449) (by norm_num)
theorem B2225161 : Blo 1758080 2225161 := bbase (se 2 (by rfl) ⟨834435, by rfl⟩ : syracuseStep 2225161 = 1668871) (by norm_num)
theorem B1979401 : Blo 1758080 1979401 := bbase (se 2 (by rfl) ⟨742275, by rfl⟩ : syracuseStep 1979401 = 1484551) (by norm_num)
theorem B9638933 : Blo 1758080 9638933 := bbase (se 6 (by rfl) ⟨225912, by rfl⟩ : syracuseStep 9638933 = 451825) (by norm_num)
theorem B4756501 : Blo 1758080 4756501 := bbase (se 6 (by rfl) ⟨111480, by rfl⟩ : syracuseStep 4756501 = 222961) (by norm_num)
theorem B1782821 : Blo 1758080 1782821 := bbase (se 4 (by rfl) ⟨167139, by rfl⟩ : syracuseStep 1782821 = 334279) (by norm_num)
theorem B5936165 : Blo 1758080 5936165 := bbase (se 4 (by rfl) ⟨556515, by rfl⟩ : syracuseStep 5936165 = 1113031) (by norm_num)
theorem B1979437 : Blo 1758080 1979437 := bbase (se 3 (by rfl) ⟨371144, by rfl⟩ : syracuseStep 1979437 = 742289) (by norm_num)
theorem B1979473 : Blo 1758080 1979473 := bbase (se 2 (by rfl) ⟨742302, by rfl⟩ : syracuseStep 1979473 = 1484605) (by norm_num)
theorem B1979509 : Blo 1758080 1979509 := bbase (se 5 (by rfl) ⟨92789, by rfl⟩ : syracuseStep 1979509 = 185579) (by norm_num)
theorem B4453501 : Blo 1758080 4453501 := bbase (se 3 (by rfl) ⟨835031, by rfl⟩ : syracuseStep 4453501 = 1670063) (by norm_num)
theorem B3339397 : Blo 1758080 3339397 := bbase (se 4 (by rfl) ⟨313068, by rfl⟩ : syracuseStep 3339397 = 626137) (by norm_num)
theorem B1979545 : Blo 1758080 1979545 := bbase (se 2 (by rfl) ⟨742329, by rfl⟩ : syracuseStep 1979545 = 1484659) (by norm_num)
theorem B2225333 : Blo 1758080 2225333 := bbase (se 5 (by rfl) ⟨104312, by rfl⟩ : syracuseStep 2225333 = 208625) (by norm_num)
theorem B1979581 : Blo 1758080 1979581 := bbase (se 3 (by rfl) ⟨371171, by rfl⟩ : syracuseStep 1979581 = 742343) (by norm_num)
theorem B1979617 : Blo 1758080 1979617 := bbase (se 2 (by rfl) ⟨742356, by rfl⟩ : syracuseStep 1979617 = 1484713) (by norm_num)
theorem B2225389 : Blo 1758080 2225389 := bbase (se 3 (by rfl) ⟨417260, by rfl⟩ : syracuseStep 2225389 = 834521) (by norm_num)
theorem B4453613 : Blo 1758080 4453613 := bbase (se 3 (by rfl) ⟨835052, by rfl⟩ : syracuseStep 4453613 = 1670105) (by norm_num)
theorem B1979653 : Blo 1758080 1979653 := bbase (se 4 (by rfl) ⟨185592, by rfl⟩ : syracuseStep 1979653 = 371185) (by norm_num)
theorem B2503973 : Blo 1758080 2503973 := bbase (se 4 (by rfl) ⟨234747, by rfl⟩ : syracuseStep 2503973 = 469495) (by norm_num)
theorem B1979689 : Blo 1758080 1979689 := bbase (se 2 (by rfl) ⟨742383, by rfl⟩ : syracuseStep 1979689 = 1484767) (by norm_num)
theorem B2225485 : Blo 1758080 2225485 := bbase (se 3 (by rfl) ⟨417278, by rfl⟩ : syracuseStep 2225485 = 834557) (by norm_num)
theorem B1979725 : Blo 1758080 1979725 := bbase (se 3 (by rfl) ⟨371198, by rfl⟩ : syracuseStep 1979725 = 742397) (by norm_num)
theorem B3757421 : Blo 1758080 3757421 := bbase (se 3 (by rfl) ⟨704516, by rfl⟩ : syracuseStep 3757421 = 1409033) (by norm_num)
theorem B1979761 : Blo 1758080 1979761 := bbase (se 2 (by rfl) ⟨742410, by rfl⟩ : syracuseStep 1979761 = 1484821) (by norm_num)
theorem B1979797 : Blo 1758080 1979797 := bbase (se 6 (by rfl) ⟨46401, by rfl⟩ : syracuseStep 1979797 = 92803) (by norm_num)
theorem B4453805 : Blo 1758080 4453805 := bbase (se 3 (by rfl) ⟨835088, by rfl⟩ : syracuseStep 4453805 = 1670177) (by norm_num)
theorem B3339701 : Blo 1758080 3339701 := bbase (se 5 (by rfl) ⟨156548, by rfl⟩ : syracuseStep 3339701 = 313097) (by norm_num)
theorem B1979833 : Blo 1758080 1979833 := bbase (se 2 (by rfl) ⟨742437, by rfl⟩ : syracuseStep 1979833 = 1484875) (by norm_num)
theorem B8566229 : Blo 1758080 8566229 := bbase (se 7 (by rfl) ⟨100385, by rfl⟩ : syracuseStep 8566229 = 200771) (by norm_num)
theorem B5936597 : Blo 1758080 5936597 := bbase (se 7 (by rfl) ⟨69569, by rfl⟩ : syracuseStep 5936597 = 139139) (by norm_num)
theorem B1979869 : Blo 1758080 1979869 := bbase (se 3 (by rfl) ⟨371225, by rfl⟩ : syracuseStep 1979869 = 742451) (by norm_num)
theorem B2225657 : Blo 1758080 2225657 := bbase (se 2 (by rfl) ⟨834621, by rfl⟩ : syracuseStep 2225657 = 1669243) (by norm_num)
theorem B1979905 : Blo 1758080 1979905 := bbase (se 2 (by rfl) ⟨742464, by rfl⟩ : syracuseStep 1979905 = 1484929) (by norm_num)
theorem B1979941 : Blo 1758080 1979941 := bbase (se 4 (by rfl) ⟨185619, by rfl⟩ : syracuseStep 1979941 = 371239) (by norm_num)
theorem B2225713 : Blo 1758080 2225713 := bbase (se 2 (by rfl) ⟨834642, by rfl⟩ : syracuseStep 2225713 = 1669285) (by norm_num)
theorem B4224581 : Blo 1758080 4224581 := bbase (se 4 (by rfl) ⟨396054, by rfl⟩ : syracuseStep 4224581 = 792109) (by norm_num)
theorem B1979977 : Blo 1758080 1979977 := bbase (se 2 (by rfl) ⟨742491, by rfl⟩ : syracuseStep 1979977 = 1484983) (by norm_num)
theorem B1783405 : Blo 1758080 1783405 := bbase (se 3 (by rfl) ⟨334388, by rfl⟩ : syracuseStep 1783405 = 668777) (by norm_num)
theorem B1980013 : Blo 1758080 1980013 := bbase (se 3 (by rfl) ⟨371252, by rfl⟩ : syracuseStep 1980013 = 742505) (by norm_num)
theorem B2225809 : Blo 1758080 2225809 := bbase (se 2 (by rfl) ⟨834678, by rfl⟩ : syracuseStep 2225809 = 1669357) (by norm_num)
theorem B1980049 : Blo 1758080 1980049 := bbase (se 2 (by rfl) ⟨742518, by rfl⟩ : syracuseStep 1980049 = 1485037) (by norm_num)
theorem B1980085 : Blo 1758080 1980085 := bbase (se 5 (by rfl) ⟨92816, by rfl⟩ : syracuseStep 1980085 = 185633) (by norm_num)
theorem B4454149 : Blo 1758080 4454149 := bbase (se 4 (by rfl) ⟨417576, by rfl⟩ : syracuseStep 4454149 = 835153) (by norm_num)
theorem B5011237 : Blo 1758080 5011237 := bbase (se 4 (by rfl) ⟨469803, by rfl⟩ : syracuseStep 5011237 = 939607) (by norm_num)
theorem B2225981 : Blo 1758080 2225981 := bbase (se 3 (by rfl) ⟨417371, by rfl⟩ : syracuseStep 2225981 = 834743) (by norm_num)
theorem B2504525 : Blo 1758080 2504525 := bbase (se 3 (by rfl) ⟨469598, by rfl⟩ : syracuseStep 2504525 = 939197) (by norm_num)
theorem B4224869 : Blo 1758080 4224869 := bbase (se 4 (by rfl) ⟨396081, by rfl⟩ : syracuseStep 4224869 = 792163) (by norm_num)
theorem B2226037 : Blo 1758080 2226037 := bbase (se 5 (by rfl) ⟨104345, by rfl⟩ : syracuseStep 2226037 = 208691) (by norm_num)
theorem B4454261 : Blo 1758080 4454261 := bbase (se 5 (by rfl) ⟨208793, by rfl⟩ : syracuseStep 4454261 = 417587) (by norm_num)
theorem B5937029 : Blo 1758080 5937029 := bbase (se 4 (by rfl) ⟨556596, by rfl⟩ : syracuseStep 5937029 = 1113193) (by norm_num)
theorem B4011949 : Blo 1758080 4011949 := bbase (se 3 (by rfl) ⟨752240, by rfl⟩ : syracuseStep 4011949 = 1504481) (by norm_num)
theorem B2226133 : Blo 1758080 2226133 := bbase (se 7 (by rfl) ⟨26087, by rfl⟩ : syracuseStep 2226133 = 52175) (by norm_num)
theorem B2856917 : Blo 1758080 2856917 := bbase (se 7 (by rfl) ⟨33479, by rfl⟩ : syracuseStep 2856917 = 66959) (by norm_num)
theorem B8902709 : Blo 1758080 8902709 := bbase (se 5 (by rfl) ⟨417314, by rfl⟩ : syracuseStep 8902709 = 834629) (by norm_num)
theorem B4454453 : Blo 1758080 4454453 := bbase (se 5 (by rfl) ⟨208802, by rfl⟩ : syracuseStep 4454453 = 417605) (by norm_num)
theorem B6338645 : Blo 1758080 6338645 := bbase (se 8 (by rfl) ⟨37140, by rfl⟩ : syracuseStep 6338645 = 74281) (by norm_num)
theorem B16898165 : Blo 1758080 16898165 := bbase (se 5 (by rfl) ⟨792101, by rfl⟩ : syracuseStep 16898165 = 1584203) (by norm_num)
theorem B2226305 : Blo 1758080 2226305 := bbase (se 2 (by rfl) ⟨834864, by rfl⟩ : syracuseStep 2226305 = 1669729) (by norm_num)
theorem B3340453 : Blo 1758080 3340453 := bbase (se 4 (by rfl) ⟨313167, by rfl⟩ : syracuseStep 3340453 = 626335) (by norm_num)
theorem B2226361 : Blo 1758080 2226361 := bbase (se 2 (by rfl) ⟨834885, by rfl⟩ : syracuseStep 2226361 = 1669771) (by norm_num)
theorem B3758309 : Blo 1758080 3758309 := bbase (se 4 (by rfl) ⟨352341, by rfl⟩ : syracuseStep 3758309 = 704683) (by norm_num)
theorem B1784041 : Blo 1758080 1784041 := bbase (se 2 (by rfl) ⟨669015, by rfl⟩ : syracuseStep 1784041 = 1338031) (by norm_num)
theorem B2226457 : Blo 1758080 2226457 := bbase (se 2 (by rfl) ⟨834921, by rfl⟩ : syracuseStep 2226457 = 1669843) (by norm_num)
theorem B5937461 : Blo 1758080 5937461 := bbase (se 5 (by rfl) ⟨278318, by rfl⟩ : syracuseStep 5937461 = 556637) (by norm_num)
theorem B3340597 : Blo 1758080 3340597 := bbase (se 5 (by rfl) ⟨156590, by rfl⟩ : syracuseStep 3340597 = 313181) (by norm_num)
theorem B4454797 : Blo 1758080 4454797 := bbase (se 3 (by rfl) ⟨835274, by rfl⟩ : syracuseStep 4454797 = 1670549) (by norm_num)
theorem B2005409 : Blo 1758080 2005409 := bbase (se 2 (by rfl) ⟨752028, by rfl⟩ : syracuseStep 2005409 = 1504057) (by norm_num)
theorem B2226629 : Blo 1758080 2226629 := bbase (se 4 (by rfl) ⟨208746, by rfl⟩ : syracuseStep 2226629 = 417493) (by norm_num)
theorem B3340757 : Blo 1758080 3340757 := bbase (se 7 (by rfl) ⟨39149, by rfl⟩ : syracuseStep 3340757 = 78299) (by norm_num)
theorem B3758557 : Blo 1758080 3758557 := bbase (se 3 (by rfl) ⟨704729, by rfl⟩ : syracuseStep 3758557 = 1409459) (by norm_num)
theorem B2005501 : Blo 1758080 2005501 := bbase (se 3 (by rfl) ⟨376031, by rfl⟩ : syracuseStep 2005501 = 752063) (by norm_num)
theorem B2226685 : Blo 1758080 2226685 := bbase (se 3 (by rfl) ⟨417503, by rfl⟩ : syracuseStep 2226685 = 835007) (by norm_num)
theorem B4454909 : Blo 1758080 4454909 := bbase (se 3 (by rfl) ⟨835295, by rfl⟩ : syracuseStep 4454909 = 1670591) (by norm_num)
theorem B2505277 : Blo 1758080 2505277 := bbase (se 3 (by rfl) ⟨469739, by rfl⟩ : syracuseStep 2505277 = 939479) (by norm_num)
theorem B2226781 : Blo 1758080 2226781 := bbase (se 3 (by rfl) ⟨417521, by rfl⟩ : syracuseStep 2226781 = 835043) (by norm_num)
theorem B3340901 : Blo 1758080 3340901 := bbase (se 4 (by rfl) ⟨313209, by rfl⟩ : syracuseStep 3340901 = 626419) (by norm_num)
theorem B2816669 : Blo 1758080 2816669 := bbase (se 3 (by rfl) ⟨528125, by rfl⟩ : syracuseStep 2816669 = 1056251) (by norm_num)
theorem B4455101 : Blo 1758080 4455101 := bbase (se 3 (by rfl) ⟨835331, by rfl⟩ : syracuseStep 4455101 = 1670663) (by norm_num)
theorem B5937893 : Blo 1758080 5937893 := bbase (se 4 (by rfl) ⟨556677, by rfl⟩ : syracuseStep 5937893 = 1113355) (by norm_num)
theorem B2226953 : Blo 1758080 2226953 := bbase (se 2 (by rfl) ⟨835107, by rfl⟩ : syracuseStep 2226953 = 1670215) (by norm_num)
theorem B2816797 : Blo 1758080 2816797 := bbase (se 3 (by rfl) ⟨528149, by rfl⟩ : syracuseStep 2816797 = 1056299) (by norm_num)
theorem B2227009 : Blo 1758080 2227009 := bbase (se 2 (by rfl) ⟨835128, by rfl⟩ : syracuseStep 2227009 = 1670257) (by norm_num)
theorem B6675317 : Blo 1758080 6675317 := bbase (se 5 (by rfl) ⟨312905, by rfl⟩ : syracuseStep 6675317 = 625811) (by norm_num)
theorem B3341189 : Blo 1758080 3341189 := bbase (se 4 (by rfl) ⟨313236, by rfl⟩ : syracuseStep 3341189 = 626473) (by norm_num)
theorem B2227105 : Blo 1758080 2227105 := bbase (se 2 (by rfl) ⟨835164, by rfl⟩ : syracuseStep 2227105 = 1670329) (by norm_num)
theorem B3759061 : Blo 1758080 3759061 := bbase (se 7 (by rfl) ⟨44051, by rfl⟩ : syracuseStep 3759061 = 88103) (by norm_num)
theorem B2005993 : Blo 1758080 2005993 := bbase (se 2 (by rfl) ⟨752247, by rfl⟩ : syracuseStep 2005993 = 1504495) (by norm_num)
theorem B3955733 : Blo 1758080 3955733 := bbase (se 6 (by rfl) ⟨92712, by rfl⟩ : syracuseStep 3955733 = 185425) (by norm_num)
theorem B3341341 : Blo 1758080 3341341 := bbase (se 3 (by rfl) ⟨626501, by rfl⟩ : syracuseStep 3341341 = 1253003) (by norm_num)
theorem B6773797 : Blo 1758080 6773797 := bbase (se 4 (by rfl) ⟨635043, by rfl⟩ : syracuseStep 6773797 = 1270087) (by norm_num)
theorem B2227277 : Blo 1758080 2227277 := bbase (se 3 (by rfl) ⟨417614, by rfl⟩ : syracuseStep 2227277 = 835229) (by norm_num)
theorem B3955805 : Blo 1758080 3955805 := bbase (se 3 (by rfl) ⟨741713, by rfl⟩ : syracuseStep 3955805 = 1483427) (by norm_num)
theorem B2227333 : Blo 1758080 2227333 := bbase (se 4 (by rfl) ⟨208812, by rfl⟩ : syracuseStep 2227333 = 417625) (by norm_num)
theorem B6675605 : Blo 1758080 6675605 := bbase (se 6 (by rfl) ⟨156459, by rfl⟩ : syracuseStep 6675605 = 312919) (by norm_num)
theorem B5938325 : Blo 1758080 5938325 := bbase (se 6 (by rfl) ⟨139179, by rfl⟩ : syracuseStep 5938325 = 278359) (by norm_num)
theorem B2817181 : Blo 1758080 2817181 := bbase (se 3 (by rfl) ⟨528221, by rfl⟩ : syracuseStep 2817181 = 1056443) (by norm_num)
theorem B3955877 : Blo 1758080 3955877 := bbase (se 4 (by rfl) ⟨370863, by rfl⟩ : syracuseStep 3955877 = 741727) (by norm_num)
theorem B7511237 : Blo 1758080 7511237 := bbase (se 4 (by rfl) ⟨704178, by rfl⟩ : syracuseStep 7511237 = 1408357) (by norm_num)
theorem B2227429 : Blo 1758080 2227429 := bbase (se 4 (by rfl) ⟨208821, by rfl⟩ : syracuseStep 2227429 = 417643) (by norm_num)
theorem B3955949 : Blo 1758080 3955949 := bbase (se 3 (by rfl) ⟨741740, by rfl⟩ : syracuseStep 3955949 = 1483481) (by norm_num)
theorem B5160197 : Blo 1758080 5160197 := bbase (se 4 (by rfl) ⟨483768, by rfl⟩ : syracuseStep 5160197 = 967537) (by norm_num)
theorem B2112809 : Blo 1758080 2112809 := bbase (se 2 (by rfl) ⟨792303, by rfl⟩ : syracuseStep 2112809 = 1584607) (by norm_num)
theorem B3956021 : Blo 1758080 3956021 := bbase (se 5 (by rfl) ⟨185438, by rfl⟩ : syracuseStep 3956021 = 370877) (by norm_num)
theorem B8453429 : Blo 1758080 8453429 := bbase (se 5 (by rfl) ⟨396254, by rfl⟩ : syracuseStep 8453429 = 792509) (by norm_num)
theorem B2637125 : Blo 1758080 2637125 := bbase (se 4 (by rfl) ⟨247230, by rfl⟩ : syracuseStep 2637125 = 494461) (by norm_num)
theorem B8904005 : Blo 1758080 8904005 := bbase (se 4 (by rfl) ⟨834750, by rfl⟩ : syracuseStep 8904005 = 1669501) (by norm_num)
theorem B2637149 : Blo 1758080 2637149 := bbase (se 3 (by rfl) ⟨494465, by rfl⟩ : syracuseStep 2637149 = 988931) (by norm_num)
theorem B2637173 : Blo 1758080 2637173 := bbase (se 5 (by rfl) ⟨123617, by rfl⟩ : syracuseStep 2637173 = 247235) (by norm_num)
theorem B3956093 : Blo 1758080 3956093 := bbase (se 3 (by rfl) ⟨741767, by rfl⟩ : syracuseStep 3956093 = 1483535) (by norm_num)
theorem B2637197 : Blo 1758080 2637197 := bbase (se 3 (by rfl) ⟨494474, by rfl⟩ : syracuseStep 2637197 = 988949) (by norm_num)
theorem B2227601 : Blo 1758080 2227601 := bbase (se 2 (by rfl) ⟨835350, by rfl⟩ : syracuseStep 2227601 = 1670701) (by norm_num)
theorem B2817437 : Blo 1758080 2817437 := bbase (se 3 (by rfl) ⟨528269, by rfl⟩ : syracuseStep 2817437 = 1056539) (by norm_num)
theorem B2637221 : Blo 1758080 2637221 := bbase (se 4 (by rfl) ⟨247239, by rfl⟩ : syracuseStep 2637221 = 494479) (by norm_num)
theorem B2637245 : Blo 1758080 2637245 := bbase (se 3 (by rfl) ⟨494483, by rfl⟩ : syracuseStep 2637245 = 988967) (by norm_num)
theorem B3956165 : Blo 1758080 3956165 := bbase (se 4 (by rfl) ⟨370890, by rfl⟩ : syracuseStep 3956165 = 741781) (by norm_num)
theorem B4513229 : Blo 1758080 4513229 := bbase (se 3 (by rfl) ⟨846230, by rfl⟩ : syracuseStep 4513229 = 1692461) (by norm_num)
theorem B2637269 : Blo 1758080 2637269 := bbase (se 7 (by rfl) ⟨30905, by rfl⟩ : syracuseStep 2637269 = 61811) (by norm_num)
theorem B7511525 : Blo 1758080 7511525 := bbase (se 4 (by rfl) ⟨704205, by rfl⟩ : syracuseStep 7511525 = 1408411) (by norm_num)
theorem B2637293 : Blo 1758080 2637293 := bbase (se 3 (by rfl) ⟨494492, by rfl⟩ : syracuseStep 2637293 = 988985) (by norm_num)
theorem B2637317 : Blo 1758080 2637317 := bbase (se 4 (by rfl) ⟨247248, by rfl⟩ : syracuseStep 2637317 = 494497) (by norm_num)
theorem B3956237 : Blo 1758080 3956237 := bbase (se 3 (by rfl) ⟨741794, by rfl⟩ : syracuseStep 3956237 = 1483589) (by norm_num)
theorem B2637341 : Blo 1758080 2637341 := bbase (se 3 (by rfl) ⟨494501, by rfl⟩ : syracuseStep 2637341 = 989003) (by norm_num)
theorem B2637365 : Blo 1758080 2637365 := bbase (se 5 (by rfl) ⟨123626, by rfl⟩ : syracuseStep 2637365 = 247253) (by norm_num)
theorem B5938757 : Blo 1758080 5938757 := bbase (se 4 (by rfl) ⟨556758, by rfl⟩ : syracuseStep 5938757 = 1113517) (by norm_num)
theorem B2637389 : Blo 1758080 2637389 := bbase (se 3 (by rfl) ⟨494510, by rfl⟩ : syracuseStep 2637389 = 989021) (by norm_num)
theorem B3956309 : Blo 1758080 3956309 := bbase (se 8 (by rfl) ⟨23181, by rfl⟩ : syracuseStep 3956309 = 46363) (by norm_num)
theorem B2637413 : Blo 1758080 2637413 := bbase (se 4 (by rfl) ⟨247257, by rfl⟩ : syracuseStep 2637413 = 494515) (by norm_num)
theorem B2637437 : Blo 1758080 2637437 := bbase (se 3 (by rfl) ⟨494519, by rfl⟩ : syracuseStep 2637437 = 989039) (by norm_num)
theorem B2637461 : Blo 1758080 2637461 := bbase (se 6 (by rfl) ⟨61815, by rfl⟩ : syracuseStep 2637461 = 123631) (by norm_num)
theorem B3956381 : Blo 1758080 3956381 := bbase (se 3 (by rfl) ⟨741821, by rfl⟩ : syracuseStep 3956381 = 1483643) (by norm_num)
theorem B2637485 : Blo 1758080 2637485 := bbase (se 3 (by rfl) ⟨494528, by rfl⟩ : syracuseStep 2637485 = 989057) (by norm_num)
theorem B2637509 : Blo 1758080 2637509 := bbase (se 4 (by rfl) ⟨247266, by rfl⟩ : syracuseStep 2637509 = 494533) (by norm_num)
theorem B2637533 : Blo 1758080 2637533 := bbase (se 3 (by rfl) ⟨494537, by rfl⟩ : syracuseStep 2637533 = 989075) (by norm_num)
theorem B3956453 : Blo 1758080 3956453 := bbase (se 4 (by rfl) ⟨370917, by rfl⟩ : syracuseStep 3956453 = 741835) (by norm_num)
theorem B2637557 : Blo 1758080 2637557 := bbase (se 5 (by rfl) ⟨123635, by rfl⟩ : syracuseStep 2637557 = 247271) (by norm_num)
theorem B2637581 : Blo 1758080 2637581 := bbase (se 3 (by rfl) ⟨494546, by rfl⟩ : syracuseStep 2637581 = 989093) (by norm_num)
theorem B2637605 : Blo 1758080 2637605 := bbase (se 4 (by rfl) ⟨247275, by rfl⟩ : syracuseStep 2637605 = 494551) (by norm_num)
theorem B3956525 : Blo 1758080 3956525 := bbase (se 3 (by rfl) ⟨741848, by rfl⟩ : syracuseStep 3956525 = 1483697) (by norm_num)
theorem B2637629 : Blo 1758080 2637629 := bbase (se 3 (by rfl) ⟨494555, by rfl⟩ : syracuseStep 2637629 = 989111) (by norm_num)
theorem B2637653 : Blo 1758080 2637653 := bbase (se 9 (by rfl) ⟨7727, by rfl⟩ : syracuseStep 2637653 = 15455) (by norm_num)
theorem B2006869 : Blo 1758080 2006869 := bbase (se 9 (by rfl) ⟨5879, by rfl⟩ : syracuseStep 2006869 = 11759) (by norm_num)
theorem B4226917 : Blo 1758080 4226917 := bbase (se 4 (by rfl) ⟨396273, by rfl⟩ : syracuseStep 4226917 = 792547) (by norm_num)
theorem B2637677 : Blo 1758080 2637677 := bbase (se 3 (by rfl) ⟨494564, by rfl⟩ : syracuseStep 2637677 = 989129) (by norm_num)
theorem B3956597 : Blo 1758080 3956597 := bbase (se 5 (by rfl) ⟨185465, by rfl⟩ : syracuseStep 3956597 = 370931) (by norm_num)
theorem B2637701 : Blo 1758080 2637701 := bbase (se 4 (by rfl) ⟨247284, by rfl⟩ : syracuseStep 2637701 = 494569) (by norm_num)
theorem B2637725 : Blo 1758080 2637725 := bbase (se 3 (by rfl) ⟨494573, by rfl⟩ : syracuseStep 2637725 = 989147) (by norm_num)
theorem B2637749 : Blo 1758080 2637749 := bbase (se 5 (by rfl) ⟨123644, by rfl⟩ : syracuseStep 2637749 = 247289) (by norm_num)
theorem B3956669 : Blo 1758080 3956669 := bbase (se 3 (by rfl) ⟨741875, by rfl⟩ : syracuseStep 3956669 = 1483751) (by norm_num)
theorem B3170245 : Blo 1758080 3170245 := bbase (se 4 (by rfl) ⟨297210, by rfl⟩ : syracuseStep 3170245 = 594421) (by norm_num)
theorem B2637773 : Blo 1758080 2637773 := bbase (se 3 (by rfl) ⟨494582, by rfl⟩ : syracuseStep 2637773 = 989165) (by norm_num)
theorem B4014029 : Blo 1758080 4014029 := bbase (se 3 (by rfl) ⟨752630, by rfl⟩ : syracuseStep 4014029 = 1505261) (by norm_num)
theorem B2113501 : Blo 1758080 2113501 := bbase (se 3 (by rfl) ⟨396281, by rfl⟩ : syracuseStep 2113501 = 792563) (by norm_num)
theorem B2637797 : Blo 1758080 2637797 := bbase (se 4 (by rfl) ⟨247293, by rfl⟩ : syracuseStep 2637797 = 494587) (by norm_num)
theorem B5939189 : Blo 1758080 5939189 := bbase (se 5 (by rfl) ⟨278399, by rfl⟩ : syracuseStep 5939189 = 556799) (by norm_num)
theorem B2637821 : Blo 1758080 2637821 := bbase (se 3 (by rfl) ⟨494591, by rfl⟩ : syracuseStep 2637821 = 989183) (by norm_num)
theorem B2637827 : Blo 1758080 2637827 := bstep (se 1 (by rfl) ⟨1978370, by rfl⟩ : syracuseStep 2637827 = 3956741) B3956741
theorem B10018829 : Blo 1758080 10018829 := bstep (se 3 (by rfl) ⟨1878530, by rfl⟩ : syracuseStep 10018829 = 3757061) B3757061
theorem B2637857 : Blo 1758080 2637857 := bstep (se 2 (by rfl) ⟨989196, by rfl⟩ : syracuseStep 2637857 = 1978393) B1978393
theorem B2637875 : Blo 1758080 2637875 := bstep (se 1 (by rfl) ⟨1978406, by rfl⟩ : syracuseStep 2637875 = 3956813) B3956813
theorem B2637905 : Blo 1758080 2637905 := bstep (se 2 (by rfl) ⟨989214, by rfl⟩ : syracuseStep 2637905 = 1978429) B1978429
theorem B2637923 : Blo 1758080 2637923 := bstep (se 1 (by rfl) ⟨1978442, by rfl⟩ : syracuseStep 2637923 = 3956885) B3956885
theorem B3956849 : Blo 1758080 3956849 := bstep (se 2 (by rfl) ⟨1483818, by rfl⟩ : syracuseStep 3956849 = 2967637) B2967637
theorem B2637953 : Blo 1758080 2637953 := bstep (se 2 (by rfl) ⟨989232, by rfl⟩ : syracuseStep 2637953 = 1978465) B1978465
theorem B3956867 : Blo 1758080 3956867 := bstep (se 1 (by rfl) ⟨2967650, by rfl⟩ : syracuseStep 3956867 = 5935301) B5935301
theorem B2637971 : Blo 1758080 2637971 := bstep (se 1 (by rfl) ⟨1978478, by rfl⟩ : syracuseStep 2637971 = 3956957) B3956957
theorem B2638001 : Blo 1758080 2638001 := bstep (se 2 (by rfl) ⟨989250, by rfl⟩ : syracuseStep 2638001 = 1978501) B1978501
theorem B2638019 : Blo 1758080 2638019 := bstep (se 1 (by rfl) ⟨1978514, by rfl⟩ : syracuseStep 2638019 = 3957029) B3957029
theorem B36126917 : Blo 1758080 36126917 := bstep (se 4 (by rfl) ⟨3386898, by rfl⟩ : syracuseStep 36126917 = 6773797) B6773797
theorem B5939405 : Blo 1758080 5939405 := bstep (se 3 (by rfl) ⟨1113638, by rfl⟩ : syracuseStep 5939405 = 2227277) B2227277
theorem B2638049 : Blo 1758080 2638049 := bstep (se 2 (by rfl) ⟨989268, by rfl⟩ : syracuseStep 2638049 = 1978537) B1978537
theorem B2638067 : Blo 1758080 2638067 := bstep (se 1 (by rfl) ⟨1978550, by rfl⟩ : syracuseStep 2638067 = 3957101) B3957101
theorem B5939459 : Blo 1758080 5939459 := bstep (se 1 (by rfl) ⟨4454594, by rfl⟩ : syracuseStep 5939459 = 8909189) B8909189
theorem B2638097 : Blo 1758080 2638097 := bstep (se 2 (by rfl) ⟨989286, by rfl⟩ : syracuseStep 2638097 = 1978573) B1978573
theorem B2638115 : Blo 1758080 2638115 := bstep (se 1 (by rfl) ⟨1978586, by rfl⟩ : syracuseStep 2638115 = 3957173) B3957173
theorem B9027875 : Blo 1758080 9027875 := bstep (se 1 (by rfl) ⟨6770906, by rfl⟩ : syracuseStep 9027875 = 13541813) B13541813
theorem B2638145 : Blo 1758080 2638145 := bstep (se 2 (by rfl) ⟨989304, by rfl⟩ : syracuseStep 2638145 = 1978609) B1978609
theorem B3809603 : Blo 1758080 3809603 := bstep (se 1 (by rfl) ⟨2857202, by rfl⟩ : syracuseStep 3809603 = 5714405) B5714405
theorem B11272517 : Blo 1758080 11272517 := bstep (se 4 (by rfl) ⟨1056798, by rfl⟩ : syracuseStep 11272517 = 2113597) B2113597
theorem B2638163 : Blo 1758080 2638163 := bstep (se 1 (by rfl) ⟨1978622, by rfl⟩ : syracuseStep 2638163 = 3957245) B3957245
theorem B2638193 : Blo 1758080 2638193 := bstep (se 2 (by rfl) ⟨989322, by rfl⟩ : syracuseStep 2638193 = 1978645) B1978645
theorem B2638211 : Blo 1758080 2638211 := bstep (se 1 (by rfl) ⟨1978658, by rfl⟩ : syracuseStep 2638211 = 3957317) B3957317
theorem B3957137 : Blo 1758080 3957137 := bstep (se 2 (by rfl) ⟨1483926, by rfl⟩ : syracuseStep 3957137 = 2967853) B2967853
theorem B2638241 : Blo 1758080 2638241 := bstep (se 2 (by rfl) ⟨989340, by rfl⟩ : syracuseStep 2638241 = 1978681) B1978681
theorem B3957155 : Blo 1758080 3957155 := bstep (se 1 (by rfl) ⟨2967866, by rfl⟩ : syracuseStep 3957155 = 5935733) B5935733
theorem B5145005 : Blo 1758080 5145005 := bstep (se 3 (by rfl) ⟨964688, by rfl⟩ : syracuseStep 5145005 = 1929377) B1929377
theorem B2638259 : Blo 1758080 2638259 := bstep (se 1 (by rfl) ⟨1978694, by rfl⟩ : syracuseStep 2638259 = 3957389) B3957389
theorem B2638289 : Blo 1758080 2638289 := bstep (se 2 (by rfl) ⟨989358, by rfl⟩ : syracuseStep 2638289 = 1978717) B1978717
theorem B2638307 : Blo 1758080 2638307 := bstep (se 1 (by rfl) ⟨1978730, by rfl⟩ : syracuseStep 2638307 = 3957461) B3957461
theorem B2638337 : Blo 1758080 2638337 := bstep (se 2 (by rfl) ⟨989376, by rfl⟩ : syracuseStep 2638337 = 1978753) B1978753
theorem B5939729 : Blo 1758080 5939729 := bstep (se 2 (by rfl) ⟨2227398, by rfl⟩ : syracuseStep 5939729 = 4454797) B4454797
theorem B2638355 : Blo 1758080 2638355 := bstep (se 1 (by rfl) ⟨1978766, by rfl⟩ : syracuseStep 2638355 = 3957533) B3957533
theorem B2638385 : Blo 1758080 2638385 := bstep (se 2 (by rfl) ⟨989394, by rfl⟩ : syracuseStep 2638385 = 1978789) B1978789
theorem B2638403 : Blo 1758080 2638403 := bstep (se 1 (by rfl) ⟨1978802, by rfl⟩ : syracuseStep 2638403 = 3957605) B3957605
theorem B2638433 : Blo 1758080 2638433 := bstep (se 2 (by rfl) ⟨989412, by rfl⟩ : syracuseStep 2638433 = 1978825) B1978825
theorem B2638451 : Blo 1758080 2638451 := bstep (se 1 (by rfl) ⟨1978838, by rfl⟩ : syracuseStep 2638451 = 3957677) B3957677
theorem B2638481 : Blo 1758080 2638481 := bstep (se 2 (by rfl) ⟨989430, by rfl⟩ : syracuseStep 2638481 = 1978861) B1978861
theorem B2638499 : Blo 1758080 2638499 := bstep (se 1 (by rfl) ⟨1978874, by rfl⟩ : syracuseStep 2638499 = 3957749) B3957749
theorem B3957425 : Blo 1758080 3957425 := bstep (se 2 (by rfl) ⟨1484034, by rfl⟩ : syracuseStep 3957425 = 2968069) B2968069
theorem B2638529 : Blo 1758080 2638529 := bstep (se 2 (by rfl) ⟨989448, by rfl⟩ : syracuseStep 2638529 = 1978897) B1978897
theorem B3957443 : Blo 1758080 3957443 := bstep (se 1 (by rfl) ⟨2968082, by rfl⟩ : syracuseStep 3957443 = 5936165) B5936165
theorem B2638547 : Blo 1758080 2638547 := bstep (se 1 (by rfl) ⟨1978910, by rfl⟩ : syracuseStep 2638547 = 3957821) B3957821
theorem B2638577 : Blo 1758080 2638577 := bstep (se 2 (by rfl) ⟨989466, by rfl⟩ : syracuseStep 2638577 = 1978933) B1978933
theorem B7135985 : Blo 1758080 7135985 := bstep (se 2 (by rfl) ⟨2675994, by rfl⟩ : syracuseStep 7135985 = 5351989) B5351989
theorem B2638595 : Blo 1758080 2638595 := bstep (se 1 (by rfl) ⟨1978946, by rfl⟩ : syracuseStep 2638595 = 3957893) B3957893
theorem B6677261 : Blo 1758080 6677261 := bstep (se 3 (by rfl) ⟨1251986, by rfl⟩ : syracuseStep 6677261 = 2503973) B2503973
theorem B2638625 : Blo 1758080 2638625 := bstep (se 2 (by rfl) ⟨989484, by rfl⟩ : syracuseStep 2638625 = 1978969) B1978969
theorem B2638643 : Blo 1758080 2638643 := bstep (se 1 (by rfl) ⟨1978982, by rfl⟩ : syracuseStep 2638643 = 3957965) B3957965
theorem B2638673 : Blo 1758080 2638673 := bstep (se 2 (by rfl) ⟨989502, by rfl⟩ : syracuseStep 2638673 = 1979005) B1979005
theorem B2638691 : Blo 1758080 2638691 := bstep (se 1 (by rfl) ⟨1979018, by rfl⟩ : syracuseStep 2638691 = 3958037) B3958037
theorem B2638721 : Blo 1758080 2638721 := bstep (se 2 (by rfl) ⟨989520, by rfl⟩ : syracuseStep 2638721 = 1979041) B1979041
theorem B2638739 : Blo 1758080 2638739 := bstep (se 1 (by rfl) ⟨1979054, by rfl⟩ : syracuseStep 2638739 = 3958109) B3958109
theorem B2638769 : Blo 1758080 2638769 := bstep (se 2 (by rfl) ⟨989538, by rfl⟩ : syracuseStep 2638769 = 1979077) B1979077
theorem B2638787 : Blo 1758080 2638787 := bstep (se 1 (by rfl) ⟨1979090, by rfl⟩ : syracuseStep 2638787 = 3958181) B3958181
theorem B3957713 : Blo 1758080 3957713 := bstep (se 2 (by rfl) ⟨1484142, by rfl⟩ : syracuseStep 3957713 = 2968285) B2968285
theorem B2638817 : Blo 1758080 2638817 := bstep (se 2 (by rfl) ⟨989556, by rfl⟩ : syracuseStep 2638817 = 1979113) B1979113
theorem B5710819 : Blo 1758080 5710819 := bstep (se 1 (by rfl) ⟨4283114, by rfl⟩ : syracuseStep 5710819 = 8566229) B8566229
theorem B3957731 : Blo 1758080 3957731 := bstep (se 1 (by rfl) ⟨2968298, by rfl⟩ : syracuseStep 3957731 = 5936597) B5936597
theorem B2638835 : Blo 1758080 2638835 := bstep (se 1 (by rfl) ⟨1979126, by rfl⟩ : syracuseStep 2638835 = 3958253) B3958253
theorem B3007505 : Blo 1758080 3007505 := bstep (se 2 (by rfl) ⟨1127814, by rfl⟩ : syracuseStep 3007505 = 2255629) B2255629
theorem B2638865 : Blo 1758080 2638865 := bstep (se 2 (by rfl) ⟨989574, by rfl⟩ : syracuseStep 2638865 = 1979149) B1979149
theorem B2638883 : Blo 1758080 2638883 := bstep (se 1 (by rfl) ⟨1979162, by rfl⟩ : syracuseStep 2638883 = 3958325) B3958325
theorem B5940269 : Blo 1758080 5940269 := bstep (se 3 (by rfl) ⟨1113800, by rfl⟩ : syracuseStep 5940269 = 2227601) B2227601
theorem B2638913 : Blo 1758080 2638913 := bstep (se 2 (by rfl) ⟨989592, by rfl⟩ : syracuseStep 2638913 = 1979185) B1979185
theorem B7513165 : Blo 1758080 7513165 := bstep (se 3 (by rfl) ⟨1408718, by rfl⟩ : syracuseStep 7513165 = 2817437) B2817437
theorem B2638931 : Blo 1758080 2638931 := bstep (se 1 (by rfl) ⟨1979198, by rfl⟩ : syracuseStep 2638931 = 3958397) B3958397
theorem B2638961 : Blo 1758080 2638961 := bstep (se 2 (by rfl) ⟨989610, by rfl⟩ : syracuseStep 2638961 = 1979221) B1979221
theorem B2638979 : Blo 1758080 2638979 := bstep (se 1 (by rfl) ⟨1979234, by rfl⟩ : syracuseStep 2638979 = 3958469) B3958469
theorem B3007649 : Blo 1758080 3007649 := bstep (se 2 (by rfl) ⟨1127868, by rfl⟩ : syracuseStep 3007649 = 2255737) B2255737
theorem B2639009 : Blo 1758080 2639009 := bstep (se 2 (by rfl) ⟨989628, by rfl⟩ : syracuseStep 2639009 = 1979257) B1979257
theorem B2639027 : Blo 1758080 2639027 := bstep (se 1 (by rfl) ⟨1979270, by rfl⟩ : syracuseStep 2639027 = 3958541) B3958541
theorem B2639057 : Blo 1758080 2639057 := bstep (se 2 (by rfl) ⟨989646, by rfl⟩ : syracuseStep 2639057 = 1979293) B1979293
theorem B2639075 : Blo 1758080 2639075 := bstep (se 1 (by rfl) ⟨1979306, by rfl⟩ : syracuseStep 2639075 = 3958613) B3958613
theorem B3958001 : Blo 1758080 3958001 := bstep (se 2 (by rfl) ⟨1484250, by rfl⟩ : syracuseStep 3958001 = 2968501) B2968501
theorem B3958019 : Blo 1758080 3958019 := bstep (se 1 (by rfl) ⟨2968514, by rfl⟩ : syracuseStep 3958019 = 5937029) B5937029
theorem B2639105 : Blo 1758080 2639105 := bstep (se 2 (by rfl) ⟨989664, by rfl⟩ : syracuseStep 2639105 = 1979329) B1979329
theorem B2639123 : Blo 1758080 2639123 := bstep (se 1 (by rfl) ⟨1979342, by rfl⟩ : syracuseStep 2639123 = 3958685) B3958685
theorem B2639153 : Blo 1758080 2639153 := bstep (se 2 (by rfl) ⟨989682, by rfl⟩ : syracuseStep 2639153 = 1979365) B1979365
theorem B2639171 : Blo 1758080 2639171 := bstep (se 1 (by rfl) ⟨1979378, by rfl⟩ : syracuseStep 2639171 = 3958757) B3958757
theorem B2966881 : Blo 1758080 2966881 := bstep (se 2 (by rfl) ⟨1112580, by rfl⟩ : syracuseStep 2966881 = 2225161) B2225161
theorem B2639201 : Blo 1758080 2639201 := bstep (se 2 (by rfl) ⟨989700, by rfl⟩ : syracuseStep 2639201 = 1979401) B1979401
theorem B12682595 : Blo 1758080 12682595 := bstep (se 1 (by rfl) ⟨9511946, by rfl⟩ : syracuseStep 12682595 = 19023893) B19023893
theorem B2639219 : Blo 1758080 2639219 := bstep (se 1 (by rfl) ⟨1979414, by rfl⟩ : syracuseStep 2639219 = 3958829) B3958829
theorem B2966915 : Blo 1758080 2966915 := bstep (se 1 (by rfl) ⟨2225186, by rfl⟩ : syracuseStep 2966915 = 4450373) B4450373
theorem B2639249 : Blo 1758080 2639249 := bstep (se 2 (by rfl) ⟨989718, by rfl⟩ : syracuseStep 2639249 = 1979437) B1979437
theorem B11265443 : Blo 1758080 11265443 := bstep (se 1 (by rfl) ⟨8449082, by rfl⟩ : syracuseStep 11265443 = 16898165) B16898165
theorem B2639267 : Blo 1758080 2639267 := bstep (se 1 (by rfl) ⟨1979450, by rfl⟩ : syracuseStep 2639267 = 3958901) B3958901
theorem B2639297 : Blo 1758080 2639297 := bstep (se 2 (by rfl) ⟨989736, by rfl⟩ : syracuseStep 2639297 = 1979473) B1979473
theorem B2639315 : Blo 1758080 2639315 := bstep (se 1 (by rfl) ⟨1979486, by rfl⟩ : syracuseStep 2639315 = 3958973) B3958973
theorem B2639345 : Blo 1758080 2639345 := bstep (se 2 (by rfl) ⟨989754, by rfl⟩ : syracuseStep 2639345 = 1979509) B1979509
theorem B2967043 : Blo 1758080 2967043 := bstep (se 1 (by rfl) ⟨2225282, by rfl⟩ : syracuseStep 2967043 = 4450565) B4450565
theorem B2639363 : Blo 1758080 2639363 := bstep (se 1 (by rfl) ⟨1979522, by rfl⟩ : syracuseStep 2639363 = 3959045) B3959045
theorem B3958289 : Blo 1758080 3958289 := bstep (se 2 (by rfl) ⟨1484358, by rfl⟩ : syracuseStep 3958289 = 2968717) B2968717
theorem B2377235 : Blo 1758080 2377235 := bstep (se 1 (by rfl) ⟨1782926, by rfl⟩ : syracuseStep 2377235 = 3565853) B3565853
theorem B2639393 : Blo 1758080 2639393 := bstep (se 2 (by rfl) ⟨989772, by rfl⟩ : syracuseStep 2639393 = 1979545) B1979545
theorem B3958307 : Blo 1758080 3958307 := bstep (se 1 (by rfl) ⟨2968730, by rfl⟩ : syracuseStep 3958307 = 5937461) B5937461
theorem B6678065 : Blo 1758080 6678065 := bstep (se 2 (by rfl) ⟨2504274, by rfl⟩ : syracuseStep 6678065 = 5008549) B5008549
theorem B2639411 : Blo 1758080 2639411 := bstep (se 1 (by rfl) ⟨1979558, by rfl⟩ : syracuseStep 2639411 = 3959117) B3959117
theorem B2639441 : Blo 1758080 2639441 := bstep (se 2 (by rfl) ⟨989790, by rfl⟩ : syracuseStep 2639441 = 1979581) B1979581
theorem B2639459 : Blo 1758080 2639459 := bstep (se 1 (by rfl) ⟨1979594, by rfl⟩ : syracuseStep 2639459 = 3959189) B3959189
theorem B2639489 : Blo 1758080 2639489 := bstep (se 2 (by rfl) ⟨989808, by rfl⟩ : syracuseStep 2639489 = 1979617) B1979617
theorem B2967185 : Blo 1758080 2967185 := bstep (se 2 (by rfl) ⟨1112694, by rfl⟩ : syracuseStep 2967185 = 2225389) B2225389
theorem B2639507 : Blo 1758080 2639507 := bstep (se 1 (by rfl) ⟨1979630, by rfl⟩ : syracuseStep 2639507 = 3959261) B3959261
theorem B2639537 : Blo 1758080 2639537 := bstep (se 2 (by rfl) ⟨989826, by rfl⟩ : syracuseStep 2639537 = 1979653) B1979653
theorem B2639555 : Blo 1758080 2639555 := bstep (se 1 (by rfl) ⟨1979666, by rfl⟩ : syracuseStep 2639555 = 3959333) B3959333
theorem B17139397 : Blo 1758080 17139397 := bstep (se 4 (by rfl) ⟨1606818, by rfl⟩ : syracuseStep 17139397 = 3213637) B3213637
theorem B2639585 : Blo 1758080 2639585 := bstep (se 2 (by rfl) ⟨989844, by rfl⟩ : syracuseStep 2639585 = 1979689) B1979689
theorem B2639603 : Blo 1758080 2639603 := bstep (se 1 (by rfl) ⟨1979702, by rfl⟩ : syracuseStep 2639603 = 3959405) B3959405
theorem B2967313 : Blo 1758080 2967313 := bstep (se 2 (by rfl) ⟨1112742, by rfl⟩ : syracuseStep 2967313 = 2225485) B2225485
theorem B2639633 : Blo 1758080 2639633 := bstep (se 2 (by rfl) ⟨989862, by rfl⟩ : syracuseStep 2639633 = 1979725) B1979725
theorem B1877779 : Blo 1758080 1877779 := bstep (se 1 (by rfl) ⟨1408334, by rfl⟩ : syracuseStep 1877779 = 2816669) B2816669
theorem B2639651 : Blo 1758080 2639651 := bstep (se 1 (by rfl) ⟨1979738, by rfl⟩ : syracuseStep 2639651 = 3959477) B3959477
theorem B3958577 : Blo 1758080 3958577 := bstep (se 2 (by rfl) ⟨1484466, by rfl⟩ : syracuseStep 3958577 = 2968933) B2968933
theorem B2967347 : Blo 1758080 2967347 := bstep (se 1 (by rfl) ⟨2225510, by rfl⟩ : syracuseStep 2967347 = 4451021) B4451021
theorem B2639681 : Blo 1758080 2639681 := bstep (se 2 (by rfl) ⟨989880, by rfl⟩ : syracuseStep 2639681 = 1979761) B1979761
theorem B3958595 : Blo 1758080 3958595 := bstep (se 1 (by rfl) ⟨2968946, by rfl⟩ : syracuseStep 3958595 = 5937893) B5937893
theorem B2639699 : Blo 1758080 2639699 := bstep (se 1 (by rfl) ⟨1979774, by rfl⟩ : syracuseStep 2639699 = 3959549) B3959549
theorem B11265905 : Blo 1758080 11265905 := bstep (se 2 (by rfl) ⟨4224714, by rfl⟩ : syracuseStep 11265905 = 8449429) B8449429
theorem B5007217 : Blo 1758080 5007217 := bstep (se 2 (by rfl) ⟨1877706, by rfl⟩ : syracuseStep 5007217 = 3755413) B3755413
theorem B2639729 : Blo 1758080 2639729 := bstep (se 2 (by rfl) ⟨989898, by rfl⟩ : syracuseStep 2639729 = 1979797) B1979797
theorem B2377603 : Blo 1758080 2377603 := bstep (se 1 (by rfl) ⟨1783202, by rfl⟩ : syracuseStep 2377603 = 3566405) B3566405
theorem B2639747 : Blo 1758080 2639747 := bstep (se 1 (by rfl) ⟨1979810, by rfl⟩ : syracuseStep 2639747 = 3959621) B3959621
theorem B2639777 : Blo 1758080 2639777 := bstep (se 2 (by rfl) ⟨989916, by rfl⟩ : syracuseStep 2639777 = 1979833) B1979833
theorem B4450211 : Blo 1758080 4450211 := bstep (se 1 (by rfl) ⟨3337658, by rfl⟩ : syracuseStep 4450211 = 6675317) B6675317
theorem B2967475 : Blo 1758080 2967475 := bstep (se 1 (by rfl) ⟨2225606, by rfl⟩ : syracuseStep 2967475 = 4451213) B4451213
theorem B2639795 : Blo 1758080 2639795 := bstep (se 1 (by rfl) ⟨1979846, by rfl⟩ : syracuseStep 2639795 = 3959693) B3959693
theorem B2639825 : Blo 1758080 2639825 := bstep (se 2 (by rfl) ⟨989934, by rfl⟩ : syracuseStep 2639825 = 1979869) B1979869
theorem B2639843 : Blo 1758080 2639843 := bstep (se 1 (by rfl) ⟨1979882, by rfl⟩ : syracuseStep 2639843 = 3959765) B3959765
theorem B2639873 : Blo 1758080 2639873 := bstep (se 2 (by rfl) ⟨989952, by rfl⟩ : syracuseStep 2639873 = 1979905) B1979905
theorem B2639891 : Blo 1758080 2639891 := bstep (se 1 (by rfl) ⟨1979918, by rfl⟩ : syracuseStep 2639891 = 3959837) B3959837
theorem B2639921 : Blo 1758080 2639921 := bstep (se 2 (by rfl) ⟨989970, by rfl⟩ : syracuseStep 2639921 = 1979941) B1979941
theorem B2967617 : Blo 1758080 2967617 := bstep (se 2 (by rfl) ⟨1112856, by rfl⟩ : syracuseStep 2967617 = 2225713) B2225713
theorem B2639939 : Blo 1758080 2639939 := bstep (se 1 (by rfl) ⟨1979954, by rfl⟩ : syracuseStep 2639939 = 3959909) B3959909
theorem B3958865 : Blo 1758080 3958865 := bstep (se 2 (by rfl) ⟨1484574, by rfl⟩ : syracuseStep 3958865 = 2969149) B2969149
theorem B2639969 : Blo 1758080 2639969 := bstep (se 2 (by rfl) ⟨989988, by rfl⟩ : syracuseStep 2639969 = 1979977) B1979977
theorem B4450403 : Blo 1758080 4450403 := bstep (se 1 (by rfl) ⟨3337802, by rfl⟩ : syracuseStep 4450403 = 6675605) B6675605
theorem B3958883 : Blo 1758080 3958883 := bstep (se 1 (by rfl) ⟨2969162, by rfl⟩ : syracuseStep 3958883 = 5938325) B5938325
theorem B2639987 : Blo 1758080 2639987 := bstep (se 1 (by rfl) ⟨1979990, by rfl⟩ : syracuseStep 2639987 = 3959981) B3959981
theorem B5007491 : Blo 1758080 5007491 := bstep (se 1 (by rfl) ⟨3755618, by rfl⟩ : syracuseStep 5007491 = 7511237) B7511237
theorem B2377873 : Blo 1758080 2377873 := bstep (se 2 (by rfl) ⟨891702, by rfl⟩ : syracuseStep 2377873 = 1783405) B1783405
theorem B2640017 : Blo 1758080 2640017 := bstep (se 2 (by rfl) ⟨990006, by rfl⟩ : syracuseStep 2640017 = 1980013) B1980013
theorem B2640035 : Blo 1758080 2640035 := bstep (se 1 (by rfl) ⟨1980026, by rfl⟩ : syracuseStep 2640035 = 3960053) B3960053
theorem B2967745 : Blo 1758080 2967745 := bstep (se 2 (by rfl) ⟨1112904, by rfl⟩ : syracuseStep 2967745 = 2225809) B2225809
theorem B2640065 : Blo 1758080 2640065 := bstep (se 2 (by rfl) ⟨990024, by rfl⟩ : syracuseStep 2640065 = 1980049) B1980049
theorem B6678733 : Blo 1758080 6678733 := bstep (se 3 (by rfl) ⟨1252262, by rfl⟩ : syracuseStep 6678733 = 2504525) B2504525
theorem B5638349 : Blo 1758080 5638349 := bstep (se 3 (by rfl) ⟨1057190, by rfl⟩ : syracuseStep 5638349 = 2114381) B2114381
theorem B2640083 : Blo 1758080 2640083 := bstep (se 1 (by rfl) ⟨1980062, by rfl⟩ : syracuseStep 2640083 = 3960125) B3960125
theorem B2967779 : Blo 1758080 2967779 := bstep (se 1 (by rfl) ⟨2225834, by rfl⟩ : syracuseStep 2967779 = 4451669) B4451669
theorem B22546673 : Blo 1758080 22546673 := bstep (se 2 (by rfl) ⟨8455002, by rfl⟩ : syracuseStep 22546673 = 16910005) B16910005
theorem B2640113 : Blo 1758080 2640113 := bstep (se 2 (by rfl) ⟨990042, by rfl⟩ : syracuseStep 2640113 = 1980085) B1980085
theorem B3008819 : Blo 1758080 3008819 := bstep (se 1 (by rfl) ⟨2256614, by rfl⟩ : syracuseStep 3008819 = 4513229) B4513229
theorem B5007683 : Blo 1758080 5007683 := bstep (se 1 (by rfl) ⟨3755762, by rfl⟩ : syracuseStep 5007683 = 7511525) B7511525
theorem B10012997 : Blo 1758080 10012997 := bstep (se 4 (by rfl) ⟨938718, by rfl⟩ : syracuseStep 10012997 = 1877437) B1877437
theorem B2967907 : Blo 1758080 2967907 := bstep (se 1 (by rfl) ⟨2225930, by rfl⟩ : syracuseStep 2967907 = 4451861) B4451861
theorem B3959153 : Blo 1758080 3959153 := bstep (se 2 (by rfl) ⟨1484682, by rfl⟩ : syracuseStep 3959153 = 2969365) B2969365
theorem B3959171 : Blo 1758080 3959171 := bstep (se 1 (by rfl) ⟨2969378, by rfl⟩ : syracuseStep 3959171 = 5938757) B5938757
theorem B2410931 : Blo 1758080 2410931 := bstep (se 1 (by rfl) ⟨1808198, by rfl⟩ : syracuseStep 2410931 = 3616397) B3616397
theorem B2968049 : Blo 1758080 2968049 := bstep (se 2 (by rfl) ⟨1113018, by rfl⟩ : syracuseStep 2968049 = 2226037) B2226037
theorem B5933681 : Blo 1758080 5933681 := bstep (se 2 (by rfl) ⟨2225130, by rfl⟩ : syracuseStep 5933681 = 4450261) B4450261
theorem B2968177 : Blo 1758080 2968177 := bstep (se 2 (by rfl) ⟨1113066, by rfl⟩ : syracuseStep 2968177 = 2226133) B2226133
theorem B3959441 : Blo 1758080 3959441 := bstep (se 2 (by rfl) ⟨1484790, by rfl⟩ : syracuseStep 3959441 = 2969581) B2969581
theorem B2968211 : Blo 1758080 2968211 := bstep (se 1 (by rfl) ⟨2226158, by rfl⟩ : syracuseStep 2968211 = 4452317) B4452317
theorem B3959459 : Blo 1758080 3959459 := bstep (se 1 (by rfl) ⟨2969594, by rfl⟩ : syracuseStep 3959459 = 5939189) B5939189
theorem B3566339 : Blo 1758080 3566339 := bstep (se 1 (by rfl) ⟨2674754, by rfl⟩ : syracuseStep 3566339 = 5349509) B5349509
theorem B10013453 : Blo 1758080 10013453 := bstep (se 3 (by rfl) ⟨1877522, by rfl⟩ : syracuseStep 10013453 = 3755045) B3755045
theorem B4754189 : Blo 1758080 4754189 := bstep (se 3 (by rfl) ⟨891410, by rfl⟩ : syracuseStep 4754189 = 1782821) B1782821
theorem B2968339 : Blo 1758080 2968339 := bstep (se 1 (by rfl) ⟨2226254, by rfl⟩ : syracuseStep 2968339 = 4452509) B4452509
theorem B8571683 : Blo 1758080 8571683 := bstep (se 1 (by rfl) ⟨6428762, by rfl⟩ : syracuseStep 8571683 = 12857525) B12857525
theorem B8907569 : Blo 1758080 8907569 := bstep (se 2 (by rfl) ⟨3340338, by rfl⟩ : syracuseStep 8907569 = 6680677) B6680677
theorem B10021745 : Blo 1758080 10021745 := bstep (se 2 (by rfl) ⟨3758154, by rfl⟩ : syracuseStep 10021745 = 7516309) B7516309
theorem B2968481 : Blo 1758080 2968481 := bstep (se 2 (by rfl) ⟨1113180, by rfl⟩ : syracuseStep 2968481 = 2226361) B2226361
theorem B8022947 : Blo 1758080 8022947 := bstep (se 1 (by rfl) ⟨6017210, by rfl⟩ : syracuseStep 8022947 = 12034421) B12034421
theorem B3959729 : Blo 1758080 3959729 := bstep (se 2 (by rfl) ⟨1484898, by rfl⟩ : syracuseStep 3959729 = 2969797) B2969797
theorem B2673587 : Blo 1758080 2673587 := bstep (se 1 (by rfl) ⟨2005190, by rfl⟩ : syracuseStep 2673587 = 4010381) B4010381
theorem B3959747 : Blo 1758080 3959747 := bstep (se 1 (by rfl) ⟨2969810, by rfl⟩ : syracuseStep 3959747 = 5939621) B5939621
theorem B6679523 : Blo 1758080 6679523 := bstep (se 1 (by rfl) ⟨5009642, by rfl⟩ : syracuseStep 6679523 = 10019285) B10019285
theorem B3755011 : Blo 1758080 3755011 := bstep (se 1 (by rfl) ⟨2816258, by rfl⟩ : syracuseStep 3755011 = 5632517) B5632517
theorem B1879043 : Blo 1758080 1879043 := bstep (se 1 (by rfl) ⟨1409282, by rfl⟩ : syracuseStep 1879043 = 2818565) B2818565
theorem B4451345 : Blo 1758080 4451345 := bstep (se 2 (by rfl) ⟨1669254, by rfl⟩ : syracuseStep 4451345 = 3338509) B3338509
theorem B2968609 : Blo 1758080 2968609 := bstep (se 2 (by rfl) ⟨1113228, by rfl⟩ : syracuseStep 2968609 = 2226457) B2226457
theorem B4451395 : Blo 1758080 4451395 := bstep (se 1 (by rfl) ⟨3338546, by rfl⟩ : syracuseStep 4451395 = 6677093) B6677093
theorem B2968643 : Blo 1758080 2968643 := bstep (se 1 (by rfl) ⟨2226482, by rfl⟩ : syracuseStep 2968643 = 4452965) B4452965
theorem B5008493 : Blo 1758080 5008493 := bstep (se 3 (by rfl) ⟨939092, by rfl⟩ : syracuseStep 5008493 = 1878185) B1878185
theorem B5934221 : Blo 1758080 5934221 := bstep (se 3 (by rfl) ⟨1112666, by rfl⟩ : syracuseStep 5934221 = 2225333) B2225333
theorem B2141363 : Blo 1758080 2141363 := bstep (se 1 (by rfl) ⟨1606022, by rfl⟩ : syracuseStep 2141363 = 3212045) B3212045
theorem B5934275 : Blo 1758080 5934275 := bstep (se 1 (by rfl) ⟨4450706, by rfl⟩ : syracuseStep 5934275 = 8901413) B8901413
theorem B2968771 : Blo 1758080 2968771 := bstep (se 1 (by rfl) ⟨2226578, by rfl⟩ : syracuseStep 2968771 = 4453157) B4453157
theorem B4451537 : Blo 1758080 4451537 := bstep (se 2 (by rfl) ⟨1669326, by rfl⟩ : syracuseStep 4451537 = 3338653) B3338653
theorem B3960017 : Blo 1758080 3960017 := bstep (se 2 (by rfl) ⟨1485006, by rfl⟩ : syracuseStep 3960017 = 2970013) B2970013
theorem B3960035 : Blo 1758080 3960035 := bstep (se 1 (by rfl) ⟨2970026, by rfl⟩ : syracuseStep 3960035 = 5940053) B5940053
theorem B16051441 : Blo 1758080 16051441 := bstep (se 2 (by rfl) ⟨6019290, by rfl⟩ : syracuseStep 16051441 = 12038581) B12038581
theorem B5008675 : Blo 1758080 5008675 := bstep (se 1 (by rfl) ⟨3756506, by rfl⟩ : syracuseStep 5008675 = 7513013) B7513013
theorem B2674001 : Blo 1758080 2674001 := bstep (se 2 (by rfl) ⟨1002750, by rfl⟩ : syracuseStep 2674001 = 2005501) B2005501
theorem B2968913 : Blo 1758080 2968913 := bstep (se 2 (by rfl) ⟨1113342, by rfl⟩ : syracuseStep 2968913 = 2226685) B2226685
theorem B3337681 : Blo 1758080 3337681 := bstep (se 2 (by rfl) ⟨1251630, by rfl⟩ : syracuseStep 3337681 = 2503261) B2503261
theorem B5934545 : Blo 1758080 5934545 := bstep (se 2 (by rfl) ⟨2225454, by rfl⟩ : syracuseStep 5934545 = 4450909) B4450909
theorem B2969041 : Blo 1758080 2969041 := bstep (se 2 (by rfl) ⟨1113390, by rfl⟩ : syracuseStep 2969041 = 2226781) B2226781
theorem B2969075 : Blo 1758080 2969075 := bstep (se 1 (by rfl) ⟨2226806, by rfl⟩ : syracuseStep 2969075 = 4453613) B4453613
theorem B1977907 : Blo 1758080 1977907 := bstep (se 1 (by rfl) ⟨1483430, by rfl⟩ : syracuseStep 1977907 = 2966861) B2966861
theorem B3337841 : Blo 1758080 3337841 := bstep (se 2 (by rfl) ⟨1251690, by rfl⟩ : syracuseStep 3337841 = 2503381) B2503381
theorem B6680177 : Blo 1758080 6680177 := bstep (se 2 (by rfl) ⟨2505066, by rfl⟩ : syracuseStep 6680177 = 5010133) B5010133
theorem B2969203 : Blo 1758080 2969203 := bstep (se 1 (by rfl) ⟨2226902, by rfl⟩ : syracuseStep 2969203 = 4453805) B4453805
theorem B1978051 : Blo 1758080 1978051 := bstep (se 1 (by rfl) ⟨1483538, by rfl⟩ : syracuseStep 1978051 = 2967077) B2967077
theorem B18058949 : Blo 1758080 18058949 := bstep (se 4 (by rfl) ⟨1693026, by rfl⟩ : syracuseStep 18058949 = 3386053) B3386053
theorem B3755729 : Blo 1758080 3755729 := bstep (se 2 (by rfl) ⟨1408398, by rfl⟩ : syracuseStep 3755729 = 2816797) B2816797
theorem B2969345 : Blo 1758080 2969345 := bstep (se 2 (by rfl) ⟨1113504, by rfl⟩ : syracuseStep 2969345 = 2227009) B2227009
theorem B5009165 : Blo 1758080 5009165 := bstep (se 3 (by rfl) ⟨939218, by rfl⟩ : syracuseStep 5009165 = 1878437) B1878437
theorem B11276081 : Blo 1758080 11276081 := bstep (se 2 (by rfl) ⟨4228530, by rfl⟩ : syracuseStep 11276081 = 8457061) B8457061
theorem B1978195 : Blo 1758080 1978195 := bstep (se 1 (by rfl) ⟨1483646, by rfl⟩ : syracuseStep 1978195 = 2967293) B2967293
theorem B2969473 : Blo 1758080 2969473 := bstep (se 2 (by rfl) ⟨1113552, by rfl⟩ : syracuseStep 2969473 = 2227105) B2227105
theorem B2969507 : Blo 1758080 2969507 := bstep (se 1 (by rfl) ⟨2227130, by rfl⟩ : syracuseStep 2969507 = 4454261) B4454261
theorem B2674657 : Blo 1758080 2674657 := bstep (se 2 (by rfl) ⟨1002996, by rfl⟩ : syracuseStep 2674657 = 2005993) B2005993
theorem B1978339 : Blo 1758080 1978339 := bstep (se 1 (by rfl) ⟨1483754, by rfl⟩ : syracuseStep 1978339 = 2967509) B2967509
theorem B5935085 : Blo 1758080 5935085 := bstep (se 3 (by rfl) ⟨1112828, by rfl⟩ : syracuseStep 5935085 = 2225657) B2225657
theorem B3338243 : Blo 1758080 3338243 := bstep (se 1 (by rfl) ⟨2503682, by rfl⟩ : syracuseStep 3338243 = 5007365) B5007365
theorem B9506821 : Blo 1758080 9506821 := bstep (se 4 (by rfl) ⟨891264, by rfl⟩ : syracuseStep 9506821 = 1782529) B1782529
theorem B5935139 : Blo 1758080 5935139 := bstep (se 1 (by rfl) ⟨4451354, by rfl⟩ : syracuseStep 5935139 = 8902709) B8902709
theorem B2969635 : Blo 1758080 2969635 := bstep (se 1 (by rfl) ⟨2227226, by rfl⟩ : syracuseStep 2969635 = 4454453) B4454453
theorem B1978483 : Blo 1758080 1978483 := bstep (se 1 (by rfl) ⟨1483862, by rfl⟩ : syracuseStep 1978483 = 2967725) B2967725
theorem B4452529 : Blo 1758080 4452529 := bstep (se 2 (by rfl) ⟨1669698, by rfl⟩ : syracuseStep 4452529 = 3339397) B3339397
theorem B2969777 : Blo 1758080 2969777 := bstep (se 2 (by rfl) ⟨1113666, by rfl⟩ : syracuseStep 2969777 = 2227333) B2227333
theorem B3756241 : Blo 1758080 3756241 := bstep (se 2 (by rfl) ⟨1408590, by rfl⟩ : syracuseStep 3756241 = 2817181) B2817181
theorem B8909027 : Blo 1758080 8909027 := bstep (se 1 (by rfl) ⟨6681770, by rfl⟩ : syracuseStep 8909027 = 13363541) B13363541
theorem B1978627 : Blo 1758080 1978627 := bstep (se 1 (by rfl) ⟨1483970, by rfl⟩ : syracuseStep 1978627 = 2967941) B2967941
theorem B10023203 : Blo 1758080 10023203 := bstep (se 1 (by rfl) ⟨7517402, by rfl⟩ : syracuseStep 10023203 = 15034805) B15034805
theorem B5935409 : Blo 1758080 5935409 := bstep (se 2 (by rfl) ⟨2225778, by rfl⟩ : syracuseStep 5935409 = 4451557) B4451557
theorem B2969905 : Blo 1758080 2969905 := bstep (se 2 (by rfl) ⟨1113714, by rfl⟩ : syracuseStep 2969905 = 2227429) B2227429
theorem B2969939 : Blo 1758080 2969939 := bstep (se 1 (by rfl) ⟨2227454, by rfl⟩ : syracuseStep 2969939 = 4454909) B4454909
theorem B1782131 : Blo 1758080 1782131 := bstep (se 1 (by rfl) ⟨1336598, by rfl⟩ : syracuseStep 1782131 = 2673197) B2673197
theorem B1978771 : Blo 1758080 1978771 := bstep (se 1 (by rfl) ⟨1484078, by rfl⟩ : syracuseStep 1978771 = 2968157) B2968157
theorem B4452803 : Blo 1758080 4452803 := bstep (se 1 (by rfl) ⟨3339602, by rfl⟩ : syracuseStep 4452803 = 6679205) B6679205
theorem B2970067 : Blo 1758080 2970067 := bstep (se 1 (by rfl) ⟨2227550, by rfl⟩ : syracuseStep 2970067 = 4455101) B4455101
theorem B1978915 : Blo 1758080 1978915 := bstep (se 1 (by rfl) ⟨1484186, by rfl⟩ : syracuseStep 1978915 = 2968373) B2968373
theorem B21688885 : Blo 1758080 21688885 := bstep (se 5 (by rfl) ⟨1016666, by rfl⟩ : syracuseStep 21688885 = 2033333) B2033333
theorem B8450659 : Blo 1758080 8450659 := bstep (se 1 (by rfl) ⟨6337994, by rfl⟩ : syracuseStep 8450659 = 12675989) B12675989
theorem B4452995 : Blo 1758080 4452995 := bstep (se 1 (by rfl) ⟨3339746, by rfl⟩ : syracuseStep 4452995 = 6679493) B6679493
theorem B13357709 : Blo 1758080 13357709 := bstep (se 3 (by rfl) ⟨2504570, by rfl⟩ : syracuseStep 13357709 = 5009141) B5009141
theorem B1979059 : Blo 1758080 1979059 := bstep (se 1 (by rfl) ⟨1484294, by rfl⟩ : syracuseStep 1979059 = 2968589) B2968589
theorem B2503489 : Blo 1758080 2503489 := bstep (se 2 (by rfl) ⟨938808, by rfl⟩ : syracuseStep 2503489 = 1877617) B1877617
theorem B1979203 : Blo 1758080 1979203 := bstep (se 1 (by rfl) ⟨1484402, by rfl⟩ : syracuseStep 1979203 = 2968805) B2968805
theorem B5935949 : Blo 1758080 5935949 := bstep (se 3 (by rfl) ⟨1112990, by rfl⟩ : syracuseStep 5935949 = 2225981) B2225981
theorem B1758083 : Blo 1758080 1758083 := bstep (se 1 (by rfl) ⟨1318562, by rfl⟩ : syracuseStep 1758083 = 2637125) B2637125
theorem B5936003 : Blo 1758080 5936003 := bstep (se 1 (by rfl) ⟨4452002, by rfl⟩ : syracuseStep 5936003 = 8904005) B8904005
theorem B3339139 : Blo 1758080 3339139 := bstep (se 1 (by rfl) ⟨2504354, by rfl⟩ : syracuseStep 3339139 = 5008709) B5008709
theorem B1758099 : Blo 1758080 1758099 := bstep (se 1 (by rfl) ⟨1318574, by rfl⟩ : syracuseStep 1758099 = 2637149) B2637149
theorem B1758115 : Blo 1758080 1758115 := bstep (se 1 (by rfl) ⟨1318586, by rfl⟩ : syracuseStep 1758115 = 2637173) B2637173
theorem B5010349 : Blo 1758080 5010349 := bstep (se 3 (by rfl) ⟨939440, by rfl⟩ : syracuseStep 5010349 = 1878881) B1878881
theorem B1758131 : Blo 1758080 1758131 := bstep (se 1 (by rfl) ⟨1318598, by rfl⟩ : syracuseStep 1758131 = 2637197) B2637197
theorem B1758147 : Blo 1758080 1758147 := bstep (se 1 (by rfl) ⟨1318610, by rfl⟩ : syracuseStep 1758147 = 2637221) B2637221
theorem B1758163 : Blo 1758080 1758163 := bstep (se 1 (by rfl) ⟨1318622, by rfl⟩ : syracuseStep 1758163 = 2637245) B2637245
theorem B1979347 : Blo 1758080 1979347 := bstep (se 1 (by rfl) ⟨1484510, by rfl⟩ : syracuseStep 1979347 = 2969021) B2969021
theorem B1758179 : Blo 1758080 1758179 := bstep (se 1 (by rfl) ⟨1318634, by rfl⟩ : syracuseStep 1758179 = 2637269) B2637269
theorem B1758195 : Blo 1758080 1758195 := bstep (se 1 (by rfl) ⟨1318646, by rfl⟩ : syracuseStep 1758195 = 2637293) B2637293
theorem B1758211 : Blo 1758080 1758211 := bstep (se 1 (by rfl) ⟨1318658, by rfl⟩ : syracuseStep 1758211 = 2637317) B2637317
theorem B8909837 : Blo 1758080 8909837 := bstep (se 3 (by rfl) ⟨1670594, by rfl⟩ : syracuseStep 8909837 = 3341189) B3341189
theorem B2225171 : Blo 1758080 2225171 := bstep (se 1 (by rfl) ⟨1668878, by rfl⟩ : syracuseStep 2225171 = 3337757) B3337757
theorem B1758227 : Blo 1758080 1758227 := bstep (se 1 (by rfl) ⟨1318670, by rfl⟩ : syracuseStep 1758227 = 2637341) B2637341
theorem B1758243 : Blo 1758080 1758243 := bstep (se 1 (by rfl) ⟨1318682, by rfl⟩ : syracuseStep 1758243 = 2637365) B2637365
theorem B3339299 : Blo 1758080 3339299 := bstep (se 1 (by rfl) ⟨2504474, by rfl⟩ : syracuseStep 3339299 = 5008949) B5008949
theorem B6681635 : Blo 1758080 6681635 := bstep (se 1 (by rfl) ⟨5011226, by rfl⟩ : syracuseStep 6681635 = 10022453) B10022453
theorem B6681649 : Blo 1758080 6681649 := bstep (se 2 (by rfl) ⟨2505618, by rfl⟩ : syracuseStep 6681649 = 5011237) B5011237
theorem B1758259 : Blo 1758080 1758259 := bstep (se 1 (by rfl) ⟨1318694, by rfl⟩ : syracuseStep 1758259 = 2637389) B2637389
theorem B48165941 : Blo 1758080 48165941 := bstep (se 5 (by rfl) ⟨2257778, by rfl⟩ : syracuseStep 48165941 = 4515557) B4515557
theorem B1758275 : Blo 1758080 1758275 := bstep (se 1 (by rfl) ⟨1318706, by rfl⟩ : syracuseStep 1758275 = 2637413) B2637413
theorem B1758291 : Blo 1758080 1758291 := bstep (se 1 (by rfl) ⟨1318718, by rfl⟩ : syracuseStep 1758291 = 2637437) B2637437
theorem B1758307 : Blo 1758080 1758307 := bstep (se 1 (by rfl) ⟨1318730, by rfl⟩ : syracuseStep 1758307 = 2637461) B2637461
theorem B1979491 : Blo 1758080 1979491 := bstep (se 1 (by rfl) ⟨1484618, by rfl⟩ : syracuseStep 1979491 = 2969237) B2969237
theorem B2675825 : Blo 1758080 2675825 := bstep (se 2 (by rfl) ⟨1003434, by rfl⟩ : syracuseStep 2675825 = 2006869) B2006869
theorem B1758323 : Blo 1758080 1758323 := bstep (se 1 (by rfl) ⟨1318742, by rfl⟩ : syracuseStep 1758323 = 2637485) B2637485
theorem B1758339 : Blo 1758080 1758339 := bstep (se 1 (by rfl) ⟨1318754, by rfl⟩ : syracuseStep 1758339 = 2637509) B2637509
theorem B5936273 : Blo 1758080 5936273 := bstep (se 2 (by rfl) ⟨2226102, by rfl⟩ : syracuseStep 5936273 = 4452205) B4452205
theorem B1758355 : Blo 1758080 1758355 := bstep (se 1 (by rfl) ⟨1318766, by rfl⟩ : syracuseStep 1758355 = 2637533) B2637533
theorem B1758371 : Blo 1758080 1758371 := bstep (se 1 (by rfl) ⟨1318778, by rfl⟩ : syracuseStep 1758371 = 2637557) B2637557
theorem B1758387 : Blo 1758080 1758387 := bstep (se 1 (by rfl) ⟨1318790, by rfl⟩ : syracuseStep 1758387 = 2637581) B2637581
theorem B1758403 : Blo 1758080 1758403 := bstep (se 1 (by rfl) ⟨1318802, by rfl⟩ : syracuseStep 1758403 = 2637605) B2637605
theorem B1758419 : Blo 1758080 1758419 := bstep (se 1 (by rfl) ⟨1318814, by rfl⟩ : syracuseStep 1758419 = 2637629) B2637629
theorem B1758435 : Blo 1758080 1758435 := bstep (se 1 (by rfl) ⟨1318826, by rfl⟩ : syracuseStep 1758435 = 2637653) B2637653
theorem B1758451 : Blo 1758080 1758451 := bstep (se 1 (by rfl) ⟨1318838, by rfl⟩ : syracuseStep 1758451 = 2637677) B2637677
theorem B1979635 : Blo 1758080 1979635 := bstep (se 1 (by rfl) ⟨1484726, by rfl⟩ : syracuseStep 1979635 = 2969453) B2969453
theorem B1758467 : Blo 1758080 1758467 := bstep (se 1 (by rfl) ⟨1318850, by rfl⟩ : syracuseStep 1758467 = 2637701) B2637701
theorem B1758483 : Blo 1758080 1758483 := bstep (se 1 (by rfl) ⟨1318862, by rfl⟩ : syracuseStep 1758483 = 2637725) B2637725
theorem B1758499 : Blo 1758080 1758499 := bstep (se 1 (by rfl) ⟨1318874, by rfl⟩ : syracuseStep 1758499 = 2637749) B2637749
theorem B1758515 : Blo 1758080 1758515 := bstep (se 1 (by rfl) ⟨1318886, by rfl⟩ : syracuseStep 1758515 = 2637773) B2637773
theorem B2676019 : Blo 1758080 2676019 := bstep (se 1 (by rfl) ⟨2007014, by rfl⟩ : syracuseStep 2676019 = 4014029) B4014029
theorem B1758531 : Blo 1758080 1758531 := bstep (se 1 (by rfl) ⟨1318898, by rfl⟩ : syracuseStep 1758531 = 2637797) B2637797
theorem B1758547 : Blo 1758080 1758547 := bstep (se 1 (by rfl) ⟨1318910, by rfl⟩ : syracuseStep 1758547 = 2637821) B2637821
theorem B1758563 : Blo 1758080 1758563 := bstep (se 1 (by rfl) ⟨1318922, by rfl⟩ : syracuseStep 1758563 = 2637845) B2637845
theorem B7517539 : Blo 1758080 7517539 := bstep (se 1 (by rfl) ⟨5638154, by rfl⟩ : syracuseStep 7517539 = 11276309) B11276309
theorem B1758579 : Blo 1758080 1758579 := bstep (se 1 (by rfl) ⟨1318934, by rfl⟩ : syracuseStep 1758579 = 2637869) B2637869
theorem B1758595 : Blo 1758080 1758595 := bstep (se 1 (by rfl) ⟨1318946, by rfl⟩ : syracuseStep 1758595 = 2637893) B2637893
theorem B1979779 : Blo 1758080 1979779 := bstep (se 1 (by rfl) ⟨1484834, by rfl⟩ : syracuseStep 1979779 = 2969669) B2969669
theorem B25703821 : Blo 1758080 25703821 := bstep (se 3 (by rfl) ⟨4819466, by rfl⟩ : syracuseStep 25703821 = 9638933) B9638933
theorem B2504081 : Blo 1758080 2504081 := bstep (se 2 (by rfl) ⟨939030, by rfl⟩ : syracuseStep 2504081 = 1878061) B1878061
theorem B1758611 : Blo 1758080 1758611 := bstep (se 1 (by rfl) ⟨1318958, by rfl⟩ : syracuseStep 1758611 = 2637917) B2637917
theorem B1758627 : Blo 1758080 1758627 := bstep (se 1 (by rfl) ⟨1318970, by rfl⟩ : syracuseStep 1758627 = 2637941) B2637941
theorem B1758643 : Blo 1758080 1758643 := bstep (se 1 (by rfl) ⟨1318982, by rfl⟩ : syracuseStep 1758643 = 2637965) B2637965
theorem B1758659 : Blo 1758080 1758659 := bstep (se 1 (by rfl) ⟨1318994, by rfl⟩ : syracuseStep 1758659 = 2637989) B2637989
theorem B25368005 : Blo 1758080 25368005 := bstep (se 4 (by rfl) ⟨2378250, by rfl⟩ : syracuseStep 25368005 = 4756501) B4756501
theorem B5494225 : Blo 1758080 5494225 := bstep (se 2 (by rfl) ⟨2060334, by rfl⟩ : syracuseStep 5494225 = 4120669) B4120669
theorem B1758675 : Blo 1758080 1758675 := bstep (se 1 (by rfl) ⟨1319006, by rfl⟩ : syracuseStep 1758675 = 2638013) B2638013
theorem B1758691 : Blo 1758080 1758691 := bstep (se 1 (by rfl) ⟨1319018, by rfl⟩ : syracuseStep 1758691 = 2638037) B2638037
theorem B1758707 : Blo 1758080 1758707 := bstep (se 1 (by rfl) ⟨1319030, by rfl⟩ : syracuseStep 1758707 = 2638061) B2638061
theorem B1758723 : Blo 1758080 1758723 := bstep (se 1 (by rfl) ⟨1319042, by rfl⟩ : syracuseStep 1758723 = 2638085) B2638085
theorem B1758739 : Blo 1758080 1758739 := bstep (se 1 (by rfl) ⟨1319054, by rfl⟩ : syracuseStep 1758739 = 2638109) B2638109
theorem B1979923 : Blo 1758080 1979923 := bstep (se 1 (by rfl) ⟨1484942, by rfl⟩ : syracuseStep 1979923 = 2969885) B2969885
theorem B1758755 : Blo 1758080 1758755 := bstep (se 1 (by rfl) ⟨1319066, by rfl⟩ : syracuseStep 1758755 = 2638133) B2638133
theorem B4453937 : Blo 1758080 4453937 := bstep (se 2 (by rfl) ⟨1670226, by rfl⟩ : syracuseStep 4453937 = 3340453) B3340453
theorem B1758771 : Blo 1758080 1758771 := bstep (se 1 (by rfl) ⟨1319078, by rfl⟩ : syracuseStep 1758771 = 2638157) B2638157
theorem B1758787 : Blo 1758080 1758787 := bstep (se 1 (by rfl) ⟨1319090, by rfl⟩ : syracuseStep 1758787 = 2638181) B2638181
theorem B1758803 : Blo 1758080 1758803 := bstep (se 1 (by rfl) ⟨1319102, by rfl⟩ : syracuseStep 1758803 = 2638205) B2638205
theorem B1758819 : Blo 1758080 1758819 := bstep (se 1 (by rfl) ⟨1319114, by rfl⟩ : syracuseStep 1758819 = 2638229) B2638229
theorem B2856547 : Blo 1758080 2856547 := bstep (se 1 (by rfl) ⟨2142410, by rfl⟩ : syracuseStep 2856547 = 4284821) B4284821
theorem B4453987 : Blo 1758080 4453987 := bstep (se 1 (by rfl) ⟨3340490, by rfl⟩ : syracuseStep 4453987 = 6680981) B6680981
theorem B10016369 : Blo 1758080 10016369 := bstep (se 2 (by rfl) ⟨3756138, by rfl⟩ : syracuseStep 10016369 = 7512277) B7512277
theorem B1758835 : Blo 1758080 1758835 := bstep (se 1 (by rfl) ⟨1319126, by rfl⟩ : syracuseStep 1758835 = 2638253) B2638253
theorem B1758851 : Blo 1758080 1758851 := bstep (se 1 (by rfl) ⟨1319138, by rfl⟩ : syracuseStep 1758851 = 2638277) B2638277
theorem B1758867 : Blo 1758080 1758867 := bstep (se 1 (by rfl) ⟨1319150, by rfl⟩ : syracuseStep 1758867 = 2638301) B2638301
theorem B1758883 : Blo 1758080 1758883 := bstep (se 1 (by rfl) ⟨1319162, by rfl⟩ : syracuseStep 1758883 = 2638325) B2638325
theorem B1980067 : Blo 1758080 1980067 := bstep (se 1 (by rfl) ⟨1485050, by rfl⟩ : syracuseStep 1980067 = 2970101) B2970101
theorem B5936813 : Blo 1758080 5936813 := bstep (se 3 (by rfl) ⟨1113152, by rfl⟩ : syracuseStep 5936813 = 2226305) B2226305
theorem B3757745 : Blo 1758080 3757745 := bstep (se 2 (by rfl) ⟨1409154, by rfl⟩ : syracuseStep 3757745 = 2818309) B2818309
theorem B1758899 : Blo 1758080 1758899 := bstep (se 1 (by rfl) ⟨1319174, by rfl⟩ : syracuseStep 1758899 = 2638349) B2638349
theorem B1758915 : Blo 1758080 1758915 := bstep (se 1 (by rfl) ⟨1319186, by rfl⟩ : syracuseStep 1758915 = 2638373) B2638373
theorem B3806929 : Blo 1758080 3806929 := bstep (se 2 (by rfl) ⟨1427598, by rfl⟩ : syracuseStep 3806929 = 2855197) B2855197
theorem B2225875 : Blo 1758080 2225875 := bstep (se 1 (by rfl) ⟨1669406, by rfl⟩ : syracuseStep 2225875 = 3338813) B3338813
theorem B1758931 : Blo 1758080 1758931 := bstep (se 1 (by rfl) ⟨1319198, by rfl⟩ : syracuseStep 1758931 = 2638397) B2638397
theorem B1758947 : Blo 1758080 1758947 := bstep (se 1 (by rfl) ⟨1319210, by rfl⟩ : syracuseStep 1758947 = 2638421) B2638421
theorem B5936867 : Blo 1758080 5936867 := bstep (se 1 (by rfl) ⟨4452650, by rfl⟩ : syracuseStep 5936867 = 8905301) B8905301
theorem B8902385 : Blo 1758080 8902385 := bstep (se 2 (by rfl) ⟨3338394, by rfl⟩ : syracuseStep 8902385 = 6676789) B6676789
theorem B4454129 : Blo 1758080 4454129 := bstep (se 2 (by rfl) ⟨1670298, by rfl⟩ : syracuseStep 4454129 = 3340597) B3340597
theorem B1758963 : Blo 1758080 1758963 := bstep (se 1 (by rfl) ⟨1319222, by rfl⟩ : syracuseStep 1758963 = 2638445) B2638445
theorem B5347075 : Blo 1758080 5347075 := bstep (se 1 (by rfl) ⟨4010306, by rfl⟩ : syracuseStep 5347075 = 8020613) B8020613
theorem B1758979 : Blo 1758080 1758979 := bstep (se 1 (by rfl) ⟨1319234, by rfl⟩ : syracuseStep 1758979 = 2638469) B2638469
theorem B1758995 : Blo 1758080 1758995 := bstep (se 1 (by rfl) ⟨1319246, by rfl⟩ : syracuseStep 1758995 = 2638493) B2638493
theorem B1759011 : Blo 1758080 1759011 := bstep (se 1 (by rfl) ⟨1319258, by rfl⟩ : syracuseStep 1759011 = 2638517) B2638517
theorem B2225971 : Blo 1758080 2225971 := bstep (se 1 (by rfl) ⟨1669478, by rfl⟩ : syracuseStep 2225971 = 3338957) B3338957
theorem B1759027 : Blo 1758080 1759027 := bstep (se 1 (by rfl) ⟨1319270, by rfl⟩ : syracuseStep 1759027 = 2638541) B2638541
theorem B1759043 : Blo 1758080 1759043 := bstep (se 1 (by rfl) ⟨1319282, by rfl⟩ : syracuseStep 1759043 = 2638565) B2638565
theorem B1759059 : Blo 1758080 1759059 := bstep (se 1 (by rfl) ⟨1319294, by rfl⟩ : syracuseStep 1759059 = 2638589) B2638589
theorem B1759075 : Blo 1758080 1759075 := bstep (se 1 (by rfl) ⟨1319306, by rfl⟩ : syracuseStep 1759075 = 2638613) B2638613
theorem B1759091 : Blo 1758080 1759091 := bstep (se 1 (by rfl) ⟨1319318, by rfl⟩ : syracuseStep 1759091 = 2638637) B2638637
theorem B1759107 : Blo 1758080 1759107 := bstep (se 1 (by rfl) ⟨1319330, by rfl⟩ : syracuseStep 1759107 = 2638661) B2638661
theorem B15030157 : Blo 1758080 15030157 := bstep (se 3 (by rfl) ⟨2818154, by rfl⟩ : syracuseStep 15030157 = 5636309) B5636309
theorem B1759123 : Blo 1758080 1759123 := bstep (se 1 (by rfl) ⟨1319342, by rfl⟩ : syracuseStep 1759123 = 2638685) B2638685
theorem B2504611 : Blo 1758080 2504611 := bstep (se 1 (by rfl) ⟨1878458, by rfl⟩ : syracuseStep 2504611 = 3756917) B3756917
theorem B1759139 : Blo 1758080 1759139 := bstep (se 1 (by rfl) ⟨1319354, by rfl⟩ : syracuseStep 1759139 = 2638709) B2638709
theorem B1759155 : Blo 1758080 1759155 := bstep (se 1 (by rfl) ⟨1319366, by rfl⟩ : syracuseStep 1759155 = 2638733) B2638733
theorem B1759171 : Blo 1758080 1759171 := bstep (se 1 (by rfl) ⟨1319378, by rfl⟩ : syracuseStep 1759171 = 2638757) B2638757
theorem B5011409 : Blo 1758080 5011409 := bstep (se 2 (by rfl) ⟨1879278, by rfl⟩ : syracuseStep 5011409 = 3758557) B3758557
theorem B1759187 : Blo 1758080 1759187 := bstep (se 1 (by rfl) ⟨1319390, by rfl⟩ : syracuseStep 1759187 = 2638781) B2638781
theorem B1759203 : Blo 1758080 1759203 := bstep (se 1 (by rfl) ⟨1319402, by rfl⟩ : syracuseStep 1759203 = 2638805) B2638805
theorem B5937137 : Blo 1758080 5937137 := bstep (se 2 (by rfl) ⟨2226426, by rfl⟩ : syracuseStep 5937137 = 4452853) B4452853
theorem B1759219 : Blo 1758080 1759219 := bstep (se 1 (by rfl) ⟨1319414, by rfl⟩ : syracuseStep 1759219 = 2638829) B2638829
theorem B1759235 : Blo 1758080 1759235 := bstep (se 1 (by rfl) ⟨1319426, by rfl⟩ : syracuseStep 1759235 = 2638853) B2638853
theorem B7133197 : Blo 1758080 7133197 := bstep (se 3 (by rfl) ⟨1337474, by rfl⟩ : syracuseStep 7133197 = 2674949) B2674949
theorem B13760525 : Blo 1758080 13760525 := bstep (se 3 (by rfl) ⟨2580098, by rfl⟩ : syracuseStep 13760525 = 5160197) B5160197
theorem B1759251 : Blo 1758080 1759251 := bstep (se 1 (by rfl) ⟨1319438, by rfl⟩ : syracuseStep 1759251 = 2638877) B2638877
theorem B1759267 : Blo 1758080 1759267 := bstep (se 1 (by rfl) ⟨1319450, by rfl⟩ : syracuseStep 1759267 = 2638901) B2638901
theorem B1759283 : Blo 1758080 1759283 := bstep (se 1 (by rfl) ⟨1319462, by rfl⟩ : syracuseStep 1759283 = 2638925) B2638925
theorem B50706485 : Blo 1758080 50706485 := bstep (se 5 (by rfl) ⟨2376866, by rfl⟩ : syracuseStep 50706485 = 4753733) B4753733
theorem B1759299 : Blo 1758080 1759299 := bstep (se 1 (by rfl) ⟨1319474, by rfl⟩ : syracuseStep 1759299 = 2638949) B2638949
theorem B3758147 : Blo 1758080 3758147 := bstep (se 1 (by rfl) ⟨2818610, by rfl⟩ : syracuseStep 3758147 = 5637221) B5637221
theorem B3340369 : Blo 1758080 3340369 := bstep (se 2 (by rfl) ⟨1252638, by rfl⟩ : syracuseStep 3340369 = 2505277) B2505277
theorem B1759315 : Blo 1758080 1759315 := bstep (se 1 (by rfl) ⟨1319486, by rfl⟩ : syracuseStep 1759315 = 2638973) B2638973
theorem B1759331 : Blo 1758080 1759331 := bstep (se 1 (by rfl) ⟨1319498, by rfl⟩ : syracuseStep 1759331 = 2638997) B2638997
theorem B5634157 : Blo 1758080 5634157 := bstep (se 3 (by rfl) ⟨1056404, by rfl⟩ : syracuseStep 5634157 = 2112809) B2112809
theorem B1759347 : Blo 1758080 1759347 := bstep (se 1 (by rfl) ⟨1319510, by rfl⟩ : syracuseStep 1759347 = 2639021) B2639021
theorem B1759363 : Blo 1758080 1759363 := bstep (se 1 (by rfl) ⟨1319522, by rfl⟩ : syracuseStep 1759363 = 2639045) B2639045
theorem B1759379 : Blo 1758080 1759379 := bstep (se 1 (by rfl) ⟨1319534, by rfl⟩ : syracuseStep 1759379 = 2639069) B2639069
theorem B1759395 : Blo 1758080 1759395 := bstep (se 1 (by rfl) ⟨1319546, by rfl⟩ : syracuseStep 1759395 = 2639093) B2639093
theorem B1759411 : Blo 1758080 1759411 := bstep (se 1 (by rfl) ⟨1319558, by rfl⟩ : syracuseStep 1759411 = 2639117) B2639117
theorem B1759427 : Blo 1758080 1759427 := bstep (se 1 (by rfl) ⟨1319570, by rfl⟩ : syracuseStep 1759427 = 2639141) B2639141
theorem B9509069 : Blo 1758080 9509069 := bstep (se 3 (by rfl) ⟨1782950, by rfl⟩ : syracuseStep 9509069 = 3565901) B3565901
theorem B1759443 : Blo 1758080 1759443 := bstep (se 1 (by rfl) ⟨1319582, by rfl⟩ : syracuseStep 1759443 = 2639165) B2639165
theorem B1759459 : Blo 1758080 1759459 := bstep (se 1 (by rfl) ⟨1319594, by rfl⟩ : syracuseStep 1759459 = 2639189) B2639189
theorem B18290929 : Blo 1758080 18290929 := bstep (se 2 (by rfl) ⟨6859098, by rfl⟩ : syracuseStep 18290929 = 13718197) B13718197
theorem B2504947 : Blo 1758080 2504947 := bstep (se 1 (by rfl) ⟨1878710, by rfl⟩ : syracuseStep 2504947 = 3757421) B3757421
theorem B1759475 : Blo 1758080 1759475 := bstep (se 1 (by rfl) ⟨1319606, by rfl⟩ : syracuseStep 1759475 = 2639213) B2639213
theorem B3168515 : Blo 1758080 3168515 := bstep (se 1 (by rfl) ⟨2376386, by rfl⟩ : syracuseStep 3168515 = 4752773) B4752773
theorem B1759491 : Blo 1758080 1759491 := bstep (se 1 (by rfl) ⟨1319618, by rfl⟩ : syracuseStep 1759491 = 2639237) B2639237
theorem B1759507 : Blo 1758080 1759507 := bstep (se 1 (by rfl) ⟨1319630, by rfl⟩ : syracuseStep 1759507 = 2639261) B2639261
theorem B2226467 : Blo 1758080 2226467 := bstep (se 1 (by rfl) ⟨1669850, by rfl⟩ : syracuseStep 2226467 = 3339701) B3339701
theorem B1759523 : Blo 1758080 1759523 := bstep (se 1 (by rfl) ⟨1319642, by rfl⟩ : syracuseStep 1759523 = 2639285) B2639285
theorem B1759539 : Blo 1758080 1759539 := bstep (se 1 (by rfl) ⟨1319654, by rfl⟩ : syracuseStep 1759539 = 2639309) B2639309
theorem B1759555 : Blo 1758080 1759555 := bstep (se 1 (by rfl) ⟨1319666, by rfl⟩ : syracuseStep 1759555 = 2639333) B2639333
theorem B1759571 : Blo 1758080 1759571 := bstep (se 1 (by rfl) ⟨1319678, by rfl⟩ : syracuseStep 1759571 = 2639357) B2639357
theorem B1759587 : Blo 1758080 1759587 := bstep (se 1 (by rfl) ⟨1319690, by rfl⟩ : syracuseStep 1759587 = 2639381) B2639381
theorem B1759603 : Blo 1758080 1759603 := bstep (se 1 (by rfl) ⟨1319702, by rfl⟩ : syracuseStep 1759603 = 2639405) B2639405
theorem B2816387 : Blo 1758080 2816387 := bstep (se 1 (by rfl) ⟨2112290, by rfl⟩ : syracuseStep 2816387 = 4224581) B4224581
theorem B1759619 : Blo 1758080 1759619 := bstep (se 1 (by rfl) ⟨1319714, by rfl⟩ : syracuseStep 1759619 = 2639429) B2639429
theorem B1759635 : Blo 1758080 1759635 := bstep (se 1 (by rfl) ⟨1319726, by rfl⟩ : syracuseStep 1759635 = 2639453) B2639453
theorem B1759651 : Blo 1758080 1759651 := bstep (se 1 (by rfl) ⟨1319738, by rfl⟩ : syracuseStep 1759651 = 2639477) B2639477
theorem B5347757 : Blo 1758080 5347757 := bstep (se 3 (by rfl) ⟨1002704, by rfl⟩ : syracuseStep 5347757 = 2005409) B2005409
theorem B1759667 : Blo 1758080 1759667 := bstep (se 1 (by rfl) ⟨1319750, by rfl⟩ : syracuseStep 1759667 = 2639501) B2639501
theorem B1759683 : Blo 1758080 1759683 := bstep (se 1 (by rfl) ⟨1319762, by rfl⟩ : syracuseStep 1759683 = 2639525) B2639525
theorem B1759699 : Blo 1758080 1759699 := bstep (se 1 (by rfl) ⟨1319774, by rfl⟩ : syracuseStep 1759699 = 2639549) B2639549
theorem B1759715 : Blo 1758080 1759715 := bstep (se 1 (by rfl) ⟨1319786, by rfl⟩ : syracuseStep 1759715 = 2639573) B2639573
theorem B1759731 : Blo 1758080 1759731 := bstep (se 1 (by rfl) ⟨1319798, by rfl⟩ : syracuseStep 1759731 = 2639597) B2639597
theorem B1759747 : Blo 1758080 1759747 := bstep (se 1 (by rfl) ⟨1319810, by rfl⟩ : syracuseStep 1759747 = 2639621) B2639621
theorem B5937677 : Blo 1758080 5937677 := bstep (se 3 (by rfl) ⟨1113314, by rfl⟩ : syracuseStep 5937677 = 2226629) B2226629
theorem B1759763 : Blo 1758080 1759763 := bstep (se 1 (by rfl) ⟨1319822, by rfl⟩ : syracuseStep 1759763 = 2639645) B2639645
theorem B1759779 : Blo 1758080 1759779 := bstep (se 1 (by rfl) ⟨1319834, by rfl⟩ : syracuseStep 1759779 = 2639669) B2639669
theorem B2005555 : Blo 1758080 2005555 := bstep (se 1 (by rfl) ⟨1504166, by rfl⟩ : syracuseStep 2005555 = 3008333) B3008333
theorem B1759795 : Blo 1758080 1759795 := bstep (se 1 (by rfl) ⟨1319846, by rfl⟩ : syracuseStep 1759795 = 2639693) B2639693
theorem B2816579 : Blo 1758080 2816579 := bstep (se 1 (by rfl) ⟨2112434, by rfl⟩ : syracuseStep 2816579 = 4224869) B4224869
theorem B5937731 : Blo 1758080 5937731 := bstep (se 1 (by rfl) ⟨4453298, by rfl⟩ : syracuseStep 5937731 = 8906597) B8906597
theorem B1759811 : Blo 1758080 1759811 := bstep (se 1 (by rfl) ⟨1319858, by rfl⟩ : syracuseStep 1759811 = 2639717) B2639717
theorem B1759827 : Blo 1758080 1759827 := bstep (se 1 (by rfl) ⟨1319870, by rfl⟩ : syracuseStep 1759827 = 2639741) B2639741
theorem B1759843 : Blo 1758080 1759843 := bstep (se 1 (by rfl) ⟨1319882, by rfl⟩ : syracuseStep 1759843 = 2639765) B2639765
theorem B5012081 : Blo 1758080 5012081 := bstep (se 2 (by rfl) ⟨1879530, by rfl⟩ : syracuseStep 5012081 = 3759061) B3759061
theorem B1759859 : Blo 1758080 1759859 := bstep (se 1 (by rfl) ⟨1319894, by rfl⟩ : syracuseStep 1759859 = 2639789) B2639789
theorem B1759875 : Blo 1758080 1759875 := bstep (se 1 (by rfl) ⟨1319906, by rfl⟩ : syracuseStep 1759875 = 2639813) B2639813
theorem B1759891 : Blo 1758080 1759891 := bstep (se 1 (by rfl) ⟨1319918, by rfl⟩ : syracuseStep 1759891 = 2639837) B2639837
theorem B1759907 : Blo 1758080 1759907 := bstep (se 1 (by rfl) ⟨1319930, by rfl⟩ : syracuseStep 1759907 = 2639861) B2639861
theorem B1759923 : Blo 1758080 1759923 := bstep (se 1 (by rfl) ⟨1319942, by rfl⟩ : syracuseStep 1759923 = 2639885) B2639885
theorem B1759939 : Blo 1758080 1759939 := bstep (se 1 (by rfl) ⟨1319954, by rfl⟩ : syracuseStep 1759939 = 2639909) B2639909
theorem B4012753 : Blo 1758080 4012753 := bstep (se 2 (by rfl) ⟨1504782, by rfl⟩ : syracuseStep 4012753 = 3009565) B3009565
theorem B1759955 : Blo 1758080 1759955 := bstep (se 1 (by rfl) ⟨1319966, by rfl⟩ : syracuseStep 1759955 = 2639933) B2639933
theorem B4455121 : Blo 1758080 4455121 := bstep (se 2 (by rfl) ⟨1670670, by rfl⟩ : syracuseStep 4455121 = 3341341) B3341341
theorem B4225763 : Blo 1758080 4225763 := bstep (se 1 (by rfl) ⟨3169322, by rfl⟩ : syracuseStep 4225763 = 6338645) B6338645
theorem B1759971 : Blo 1758080 1759971 := bstep (se 1 (by rfl) ⟨1319978, by rfl⟩ : syracuseStep 1759971 = 2639957) B2639957
theorem B1759987 : Blo 1758080 1759987 := bstep (se 1 (by rfl) ⟨1319990, by rfl⟩ : syracuseStep 1759987 = 2639981) B2639981
theorem B1760003 : Blo 1758080 1760003 := bstep (se 1 (by rfl) ⟨1320002, by rfl⟩ : syracuseStep 1760003 = 2640005) B2640005
theorem B1760019 : Blo 1758080 1760019 := bstep (se 1 (by rfl) ⟨1320014, by rfl⟩ : syracuseStep 1760019 = 2640029) B2640029
theorem B2505505 : Blo 1758080 2505505 := bstep (se 2 (by rfl) ⟨939564, by rfl⟩ : syracuseStep 2505505 = 1879129) B1879129
theorem B1760035 : Blo 1758080 1760035 := bstep (se 1 (by rfl) ⟨1320026, by rfl⟩ : syracuseStep 1760035 = 2640053) B2640053
theorem B1760051 : Blo 1758080 1760051 := bstep (se 1 (by rfl) ⟨1320038, by rfl⟩ : syracuseStep 1760051 = 2640077) B2640077
theorem B2505539 : Blo 1758080 2505539 := bstep (se 1 (by rfl) ⟨1879154, by rfl⟩ : syracuseStep 2505539 = 3758309) B3758309
theorem B1760067 : Blo 1758080 1760067 := bstep (se 1 (by rfl) ⟨1320050, by rfl⟩ : syracuseStep 1760067 = 2640101) B2640101
theorem B5938001 : Blo 1758080 5938001 := bstep (se 2 (by rfl) ⟨2226750, by rfl⟩ : syracuseStep 5938001 = 4453501) B4453501
theorem B3759043 : Blo 1758080 3759043 := bstep (se 1 (by rfl) ⟨2819282, by rfl⟩ : syracuseStep 3759043 = 5638565) B5638565
theorem B13351877 : Blo 1758080 13351877 := bstep (se 4 (by rfl) ⟨1251738, by rfl⟩ : syracuseStep 13351877 = 2503477) B2503477
theorem B2227171 : Blo 1758080 2227171 := bstep (se 1 (by rfl) ⟨1670378, by rfl⟩ : syracuseStep 2227171 = 3340757) B3340757
theorem B3955697 : Blo 1758080 3955697 := bstep (se 2 (by rfl) ⟨1483386, by rfl⟩ : syracuseStep 3955697 = 2966773) B2966773
theorem B3955715 : Blo 1758080 3955715 := bstep (se 1 (by rfl) ⟨2966786, by rfl⟩ : syracuseStep 3955715 = 5933573) B5933573
theorem B5790733 : Blo 1758080 5790733 := bstep (se 3 (by rfl) ⟨1085762, by rfl⟩ : syracuseStep 5790733 = 2171525) B2171525
theorem B10017827 : Blo 1758080 10017827 := bstep (se 1 (by rfl) ⟨7513370, by rfl⟩ : syracuseStep 10017827 = 15026741) B15026741
theorem B2227267 : Blo 1758080 2227267 := bstep (se 1 (by rfl) ⟨1670450, by rfl⟩ : syracuseStep 2227267 = 3340901) B3340901
theorem B8903843 : Blo 1758080 8903843 := bstep (se 1 (by rfl) ⟨6677882, by rfl⟩ : syracuseStep 8903843 = 13355765) B13355765
theorem B15031493 : Blo 1758080 15031493 := bstep (se 4 (by rfl) ⟨1409202, by rfl⟩ : syracuseStep 15031493 = 2818405) B2818405
theorem B6020333 : Blo 1758080 6020333 := bstep (se 3 (by rfl) ⟨1128812, by rfl⟩ : syracuseStep 6020333 = 2257625) B2257625
theorem B24067313 : Blo 1758080 24067313 := bstep (se 2 (by rfl) ⟨9025242, by rfl⟩ : syracuseStep 24067313 = 18050485) B18050485
theorem B3955985 : Blo 1758080 3955985 := bstep (se 2 (by rfl) ⟨1483494, by rfl⟩ : syracuseStep 3955985 = 2966989) B2966989
theorem B3956003 : Blo 1758080 3956003 := bstep (se 1 (by rfl) ⟨2967002, by rfl⟩ : syracuseStep 3956003 = 5934005) B5934005
theorem B14269765 : Blo 1758080 14269765 := bstep (se 4 (by rfl) ⟨1337790, by rfl⟩ : syracuseStep 14269765 = 2675581) B2675581
theorem B2637137 : Blo 1758080 2637137 := bstep (se 2 (by rfl) ⟨988926, by rfl⟩ : syracuseStep 2637137 = 1977853) B1977853
theorem B4701521 : Blo 1758080 4701521 := bstep (se 2 (by rfl) ⟨1763070, by rfl⟩ : syracuseStep 4701521 = 3526141) B3526141
theorem B2637155 : Blo 1758080 2637155 := bstep (se 1 (by rfl) ⟨1977866, by rfl⟩ : syracuseStep 2637155 = 3955733) B3955733
theorem B5938541 : Blo 1758080 5938541 := bstep (se 3 (by rfl) ⟨1113476, by rfl⟩ : syracuseStep 5938541 = 2226953) B2226953
theorem B2637185 : Blo 1758080 2637185 := bstep (se 2 (by rfl) ⟨988944, by rfl⟩ : syracuseStep 2637185 = 1977889) B1977889
theorem B2637203 : Blo 1758080 2637203 := bstep (se 1 (by rfl) ⟨1977902, by rfl⟩ : syracuseStep 2637203 = 3955805) B3955805
theorem B5938595 : Blo 1758080 5938595 := bstep (se 1 (by rfl) ⟨4453946, by rfl⟩ : syracuseStep 5938595 = 8907893) B8907893
theorem B2637233 : Blo 1758080 2637233 := bstep (se 2 (by rfl) ⟨988962, by rfl⟩ : syracuseStep 2637233 = 1977925) B1977925
theorem B2637251 : Blo 1758080 2637251 := bstep (se 1 (by rfl) ⟨1977938, by rfl⟩ : syracuseStep 2637251 = 3955877) B3955877
theorem B2637281 : Blo 1758080 2637281 := bstep (se 2 (by rfl) ⟨988980, by rfl⟩ : syracuseStep 2637281 = 1977961) B1977961
theorem B13360625 : Blo 1758080 13360625 := bstep (se 2 (by rfl) ⟨5010234, by rfl⟩ : syracuseStep 13360625 = 10020469) B10020469
theorem B2637299 : Blo 1758080 2637299 := bstep (se 1 (by rfl) ⟨1977974, by rfl⟩ : syracuseStep 2637299 = 3955949) B3955949
theorem B3055091 : Blo 1758080 3055091 := bstep (se 1 (by rfl) ⟨2291318, by rfl⟩ : syracuseStep 3055091 = 4582637) B4582637
theorem B2637329 : Blo 1758080 2637329 := bstep (se 2 (by rfl) ⟨988998, by rfl⟩ : syracuseStep 2637329 = 1977997) B1977997
theorem B38059541 : Blo 1758080 38059541 := bstep (se 6 (by rfl) ⟨892020, by rfl⟩ : syracuseStep 38059541 = 1784041) B1784041
theorem B2637347 : Blo 1758080 2637347 := bstep (se 1 (by rfl) ⟨1978010, by rfl⟩ : syracuseStep 2637347 = 3956021) B3956021
theorem B5635619 : Blo 1758080 5635619 := bstep (se 1 (by rfl) ⟨4226714, by rfl⟩ : syracuseStep 5635619 = 8453429) B8453429
theorem B3956273 : Blo 1758080 3956273 := bstep (se 2 (by rfl) ⟨1483602, by rfl⟩ : syracuseStep 3956273 = 2967205) B2967205
theorem B2637377 : Blo 1758080 2637377 := bstep (se 2 (by rfl) ⟨989016, by rfl⟩ : syracuseStep 2637377 = 1978033) B1978033
theorem B3956291 : Blo 1758080 3956291 := bstep (se 1 (by rfl) ⟨2967218, by rfl⟩ : syracuseStep 3956291 = 5934437) B5934437
theorem B21397061 : Blo 1758080 21397061 := bstep (se 4 (by rfl) ⟨2005974, by rfl⟩ : syracuseStep 21397061 = 4011949) B4011949
theorem B2637395 : Blo 1758080 2637395 := bstep (se 1 (by rfl) ⟨1978046, by rfl⟩ : syracuseStep 2637395 = 3956093) B3956093
theorem B2637425 : Blo 1758080 2637425 := bstep (se 2 (by rfl) ⟨989034, by rfl⟩ : syracuseStep 2637425 = 1978069) B1978069
theorem B2637443 : Blo 1758080 2637443 := bstep (se 1 (by rfl) ⟨1978082, by rfl⟩ : syracuseStep 2637443 = 3956165) B3956165
theorem B33808013 : Blo 1758080 33808013 := bstep (se 3 (by rfl) ⟨6339002, by rfl⟩ : syracuseStep 33808013 = 12678005) B12678005
theorem B2637473 : Blo 1758080 2637473 := bstep (se 2 (by rfl) ⟨989052, by rfl⟩ : syracuseStep 2637473 = 1978105) B1978105
theorem B5938865 : Blo 1758080 5938865 := bstep (se 2 (by rfl) ⟨2227074, by rfl⟩ : syracuseStep 5938865 = 4454149) B4454149
theorem B2637491 : Blo 1758080 2637491 := bstep (se 1 (by rfl) ⟨1978118, by rfl⟩ : syracuseStep 2637491 = 3956237) B3956237
theorem B2637521 : Blo 1758080 2637521 := bstep (se 2 (by rfl) ⟨989070, by rfl⟩ : syracuseStep 2637521 = 1978141) B1978141
theorem B2637539 : Blo 1758080 2637539 := bstep (se 1 (by rfl) ⟨1978154, by rfl⟩ : syracuseStep 2637539 = 3956309) B3956309
theorem B2637569 : Blo 1758080 2637569 := bstep (se 2 (by rfl) ⟨989088, by rfl⟩ : syracuseStep 2637569 = 1978177) B1978177
theorem B2637587 : Blo 1758080 2637587 := bstep (se 1 (by rfl) ⟨1978190, by rfl⟩ : syracuseStep 2637587 = 3956381) B3956381
theorem B2637617 : Blo 1758080 2637617 := bstep (se 2 (by rfl) ⟨989106, by rfl⟩ : syracuseStep 2637617 = 1978213) B1978213
theorem B5635889 : Blo 1758080 5635889 := bstep (se 2 (by rfl) ⟨2113458, by rfl⟩ : syracuseStep 5635889 = 4226917) B4226917
theorem B2637635 : Blo 1758080 2637635 := bstep (se 1 (by rfl) ⟨1978226, by rfl⟩ : syracuseStep 2637635 = 3956453) B3956453
theorem B2006851 : Blo 1758080 2006851 := bstep (se 1 (by rfl) ⟨1505138, by rfl⟩ : syracuseStep 2006851 = 3010277) B3010277
theorem B3956561 : Blo 1758080 3956561 := bstep (se 2 (by rfl) ⟨1483710, by rfl⟩ : syracuseStep 3956561 = 2967421) B2967421
theorem B2637665 : Blo 1758080 2637665 := bstep (se 2 (by rfl) ⟨989124, by rfl⟩ : syracuseStep 2637665 = 1978249) B1978249
theorem B3956579 : Blo 1758080 3956579 := bstep (se 1 (by rfl) ⟨2967434, by rfl⟩ : syracuseStep 3956579 = 5934869) B5934869
theorem B6020963 : Blo 1758080 6020963 := bstep (se 1 (by rfl) ⟨4515722, by rfl⟩ : syracuseStep 6020963 = 9031445) B9031445
theorem B2637683 : Blo 1758080 2637683 := bstep (se 1 (by rfl) ⟨1978262, by rfl⟩ : syracuseStep 2637683 = 3956525) B3956525
theorem B7618445 : Blo 1758080 7618445 := bstep (se 3 (by rfl) ⟨1428458, by rfl⟩ : syracuseStep 7618445 = 2856917) B2856917
theorem B2637713 : Blo 1758080 2637713 := bstep (se 2 (by rfl) ⟨989142, by rfl⟩ : syracuseStep 2637713 = 1978285) B1978285
theorem B2637731 : Blo 1758080 2637731 := bstep (se 1 (by rfl) ⟨1978298, by rfl⟩ : syracuseStep 2637731 = 3956597) B3956597
theorem B4226993 : Blo 1758080 4226993 := bstep (se 2 (by rfl) ⟨1585122, by rfl⟩ : syracuseStep 4226993 = 3170245) B3170245
theorem B7618481 : Blo 1758080 7618481 := bstep (se 2 (by rfl) ⟨2856930, by rfl⟩ : syracuseStep 7618481 = 5713861) B5713861
theorem B2637761 : Blo 1758080 2637761 := bstep (se 2 (by rfl) ⟨989160, by rfl⟩ : syracuseStep 2637761 = 1978321) B1978321
theorem B8904653 : Blo 1758080 8904653 := bstep (se 3 (by rfl) ⟨1669622, by rfl⟩ : syracuseStep 8904653 = 3339245) B3339245
theorem B2818001 : Blo 1758080 2818001 := bstep (se 2 (by rfl) ⟨1056750, by rfl⟩ : syracuseStep 2818001 = 2113501) B2113501
theorem B2637779 : Blo 1758080 2637779 := bstep (se 1 (by rfl) ⟨1978334, by rfl⟩ : syracuseStep 2637779 = 3956669) B3956669
theorem B2637809 : Blo 1758080 2637809 := bstep (se 2 (by rfl) ⟨989178, by rfl⟩ : syracuseStep 2637809 = 1978357) B1978357
theorem B9510929 : Blo 1758080 9510929 := bstep (se 2 (by rfl) ⟨3566598, by rfl⟩ : syracuseStep 9510929 = 7133197) B7133197
theorem B3956759 : Blo 1758080 3956759 := bstep (se 1 (by rfl) ⟨2967569, by rfl⟩ : syracuseStep 3956759 = 5935139) B5935139
theorem B30883909 : Blo 1758080 30883909 := bstep (se 4 (by rfl) ⟨2895366, by rfl⟩ : syracuseStep 30883909 = 5790733) B5790733
theorem B2637899 : Blo 1758080 2637899 := bstep (se 1 (by rfl) ⟨1978424, by rfl⟩ : syracuseStep 2637899 = 3956849) B3956849
theorem B2637911 : Blo 1758080 2637911 := bstep (se 1 (by rfl) ⟨1978433, by rfl⟩ : syracuseStep 2637911 = 3956867) B3956867
theorem B24084611 : Blo 1758080 24084611 := bstep (se 1 (by rfl) ⟨18063458, by rfl⟩ : syracuseStep 24084611 = 36126917) B36126917
theorem B7512209 : Blo 1758080 7512209 := bstep (se 2 (by rfl) ⟨2817078, by rfl⟩ : syracuseStep 7512209 = 5634157) B5634157
theorem B5939351 : Blo 1758080 5939351 := bstep (se 1 (by rfl) ⟨4454513, by rfl⟩ : syracuseStep 5939351 = 8909027) B8909027
theorem B2637977 : Blo 1758080 2637977 := bstep (se 2 (by rfl) ⟨989241, by rfl⟩ : syracuseStep 2637977 = 1978483) B1978483
theorem B3170497 : Blo 1758080 3170497 := bstep (se 2 (by rfl) ⟨1188936, by rfl⟩ : syracuseStep 3170497 = 2377873) B2377873
theorem B3956939 : Blo 1758080 3956939 := bstep (se 1 (by rfl) ⟨2967704, by rfl⟩ : syracuseStep 3956939 = 5935409) B5935409
theorem B2539735 : Blo 1758080 2539735 := bstep (se 1 (by rfl) ⟨1904801, by rfl⟩ : syracuseStep 2539735 = 3809603) B3809603
theorem B3956993 : Blo 1758080 3956993 := bstep (se 2 (by rfl) ⟨1483872, by rfl⟩ : syracuseStep 3956993 = 2967745) B2967745
theorem B2638091 : Blo 1758080 2638091 := bstep (se 1 (by rfl) ⟨1978568, by rfl⟩ : syracuseStep 2638091 = 3957137) B3957137
theorem B8904977 : Blo 1758080 8904977 := bstep (se 2 (by rfl) ⟨3339366, by rfl⟩ : syracuseStep 8904977 = 6678733) B6678733
theorem B2638103 : Blo 1758080 2638103 := bstep (se 1 (by rfl) ⟨1978577, by rfl⟩ : syracuseStep 2638103 = 3957155) B3957155
theorem B24387905 : Blo 1758080 24387905 := bstep (se 2 (by rfl) ⟨9145464, by rfl⟩ : syracuseStep 24387905 = 18290929) B18290929
theorem B2638169 : Blo 1758080 2638169 := bstep (se 2 (by rfl) ⟨989313, by rfl⟩ : syracuseStep 2638169 = 1978627) B1978627
theorem B8020397 : Blo 1758080 8020397 := bstep (se 3 (by rfl) ⟨1503824, by rfl⟩ : syracuseStep 8020397 = 3007649) B3007649
theorem B8905139 : Blo 1758080 8905139 := bstep (se 1 (by rfl) ⟨6678854, by rfl⟩ : syracuseStep 8905139 = 13357709) B13357709
theorem B2638283 : Blo 1758080 2638283 := bstep (se 1 (by rfl) ⟨1978712, by rfl⟩ : syracuseStep 2638283 = 3957425) B3957425
theorem B2638295 : Blo 1758080 2638295 := bstep (se 1 (by rfl) ⟨1978721, by rfl⟩ : syracuseStep 2638295 = 3957443) B3957443
theorem B3957209 : Blo 1758080 3957209 := bstep (se 2 (by rfl) ⟨1483953, by rfl⟩ : syracuseStep 3957209 = 2967907) B2967907
theorem B5710301 : Blo 1758080 5710301 := bstep (se 3 (by rfl) ⟨1070681, by rfl⟩ : syracuseStep 5710301 = 2141363) B2141363
theorem B2638361 : Blo 1758080 2638361 := bstep (se 2 (by rfl) ⟨989385, by rfl⟩ : syracuseStep 2638361 = 1978771) B1978771
theorem B3957299 : Blo 1758080 3957299 := bstep (se 1 (by rfl) ⟨2967974, by rfl⟩ : syracuseStep 3957299 = 5935949) B5935949
theorem B3957335 : Blo 1758080 3957335 := bstep (se 1 (by rfl) ⟨2968001, by rfl⟩ : syracuseStep 3957335 = 5936003) B5936003
theorem B2638475 : Blo 1758080 2638475 := bstep (se 1 (by rfl) ⟨1978856, by rfl⟩ : syracuseStep 2638475 = 3957713) B3957713
theorem B2638487 : Blo 1758080 2638487 := bstep (se 1 (by rfl) ⟨1978865, by rfl⟩ : syracuseStep 2638487 = 3957731) B3957731
theorem B5939891 : Blo 1758080 5939891 := bstep (se 1 (by rfl) ⟨4454918, by rfl⟩ : syracuseStep 5939891 = 8909837) B8909837
theorem B2638553 : Blo 1758080 2638553 := bstep (se 2 (by rfl) ⟨989457, by rfl⟩ : syracuseStep 2638553 = 1978915) B1978915
theorem B28918513 : Blo 1758080 28918513 := bstep (se 2 (by rfl) ⟨10844442, by rfl⟩ : syracuseStep 28918513 = 21688885) B21688885
theorem B3957515 : Blo 1758080 3957515 := bstep (se 1 (by rfl) ⟨2968136, by rfl⟩ : syracuseStep 3957515 = 5936273) B5936273
theorem B3957569 : Blo 1758080 3957569 := bstep (se 2 (by rfl) ⟨1484088, by rfl⟩ : syracuseStep 3957569 = 2968177) B2968177
theorem B2638667 : Blo 1758080 2638667 := bstep (se 1 (by rfl) ⟨1979000, by rfl⟩ : syracuseStep 2638667 = 3958001) B3958001
theorem B2638679 : Blo 1758080 2638679 := bstep (se 1 (by rfl) ⟨1979009, by rfl⟩ : syracuseStep 2638679 = 3958019) B3958019
theorem B13353821 : Blo 1758080 13353821 := bstep (se 3 (by rfl) ⟨2503841, by rfl⟩ : syracuseStep 13353821 = 5007683) B5007683
theorem B8455063 : Blo 1758080 8455063 := bstep (se 1 (by rfl) ⟨6341297, by rfl⟩ : syracuseStep 8455063 = 12682595) B12682595
theorem B2638745 : Blo 1758080 2638745 := bstep (se 2 (by rfl) ⟨989529, by rfl⟩ : syracuseStep 2638745 = 1979059) B1979059
theorem B5350337 : Blo 1758080 5350337 := bstep (se 2 (by rfl) ⟨2006376, by rfl⟩ : syracuseStep 5350337 = 4012753) B4012753
theorem B5940161 : Blo 1758080 5940161 := bstep (se 2 (by rfl) ⟨2227560, by rfl⟩ : syracuseStep 5940161 = 4455121) B4455121
theorem B2638859 : Blo 1758080 2638859 := bstep (se 1 (by rfl) ⟨1979144, by rfl⟩ : syracuseStep 2638859 = 3958289) B3958289
theorem B2638871 : Blo 1758080 2638871 := bstep (se 1 (by rfl) ⟨1979153, by rfl⟩ : syracuseStep 2638871 = 3958307) B3958307
theorem B3957785 : Blo 1758080 3957785 := bstep (se 2 (by rfl) ⟨1484169, by rfl⟩ : syracuseStep 3957785 = 2968339) B2968339
theorem B6677549 : Blo 1758080 6677549 := bstep (se 3 (by rfl) ⟨1252040, by rfl⟩ : syracuseStep 6677549 = 2504081) B2504081
theorem B6677579 : Blo 1758080 6677579 := bstep (se 1 (by rfl) ⟨5008184, by rfl⟩ : syracuseStep 6677579 = 10016369) B10016369
theorem B2638937 : Blo 1758080 2638937 := bstep (se 2 (by rfl) ⟨989601, by rfl⟩ : syracuseStep 2638937 = 1979203) B1979203
theorem B3957875 : Blo 1758080 3957875 := bstep (se 1 (by rfl) ⟨2968406, by rfl⟩ : syracuseStep 3957875 = 5936813) B5936813
theorem B3957911 : Blo 1758080 3957911 := bstep (se 1 (by rfl) ⟨2968433, by rfl⟩ : syracuseStep 3957911 = 5936867) B5936867
theorem B2639051 : Blo 1758080 2639051 := bstep (se 1 (by rfl) ⟨1979288, by rfl⟩ : syracuseStep 2639051 = 3958577) B3958577
theorem B2639063 : Blo 1758080 2639063 := bstep (se 1 (by rfl) ⟨1979297, by rfl⟩ : syracuseStep 2639063 = 3958595) B3958595
theorem B2966807 : Blo 1758080 2966807 := bstep (se 1 (by rfl) ⟨2225105, by rfl⟩ : syracuseStep 2966807 = 4450211) B4450211
theorem B2639129 : Blo 1758080 2639129 := bstep (se 2 (by rfl) ⟨989673, by rfl⟩ : syracuseStep 2639129 = 1979347) B1979347
theorem B3958091 : Blo 1758080 3958091 := bstep (se 1 (by rfl) ⟨2968568, by rfl⟩ : syracuseStep 3958091 = 5937137) B5937137
theorem B5006681 : Blo 1758080 5006681 := bstep (se 2 (by rfl) ⟨1877505, by rfl⟩ : syracuseStep 5006681 = 3755011) B3755011
theorem B3958145 : Blo 1758080 3958145 := bstep (se 2 (by rfl) ⟨1484304, by rfl⟩ : syracuseStep 3958145 = 2968609) B2968609
theorem B2639243 : Blo 1758080 2639243 := bstep (se 1 (by rfl) ⟨1979432, by rfl⟩ : syracuseStep 2639243 = 3958865) B3958865
theorem B2966935 : Blo 1758080 2966935 := bstep (se 1 (by rfl) ⟨2225201, by rfl⟩ : syracuseStep 2966935 = 4450403) B4450403
theorem B2639255 : Blo 1758080 2639255 := bstep (se 1 (by rfl) ⟨1979441, by rfl⟩ : syracuseStep 2639255 = 3958883) B3958883
theorem B2639321 : Blo 1758080 2639321 := bstep (se 2 (by rfl) ⟨989745, by rfl⟩ : syracuseStep 2639321 = 1979491) B1979491
theorem B2639435 : Blo 1758080 2639435 := bstep (se 1 (by rfl) ⟨1979576, by rfl⟩ : syracuseStep 2639435 = 3959153) B3959153
theorem B1877591 : Blo 1758080 1877591 := bstep (se 1 (by rfl) ⟨1408193, by rfl⟩ : syracuseStep 1877591 = 2816387) B2816387
theorem B2639447 : Blo 1758080 2639447 := bstep (se 1 (by rfl) ⟨1979585, by rfl⟩ : syracuseStep 2639447 = 3959171) B3959171
theorem B3958361 : Blo 1758080 3958361 := bstep (se 2 (by rfl) ⟨1484385, by rfl⟩ : syracuseStep 3958361 = 2968771) B2968771
theorem B3565171 : Blo 1758080 3565171 := bstep (se 1 (by rfl) ⟨2673878, by rfl⟩ : syracuseStep 3565171 = 5347757) B5347757
theorem B2639513 : Blo 1758080 2639513 := bstep (se 2 (by rfl) ⟨989817, by rfl⟩ : syracuseStep 2639513 = 1979635) B1979635
theorem B3958451 : Blo 1758080 3958451 := bstep (se 1 (by rfl) ⟨2968838, by rfl⟩ : syracuseStep 3958451 = 5937677) B5937677
theorem B3958487 : Blo 1758080 3958487 := bstep (se 1 (by rfl) ⟨2968865, by rfl⟩ : syracuseStep 3958487 = 5937731) B5937731
theorem B6678233 : Blo 1758080 6678233 := bstep (se 2 (by rfl) ⟨2504337, by rfl⟩ : syracuseStep 6678233 = 5008675) B5008675
theorem B2639627 : Blo 1758080 2639627 := bstep (se 1 (by rfl) ⟨1979720, by rfl⟩ : syracuseStep 2639627 = 3959441) B3959441
theorem B2639639 : Blo 1758080 2639639 := bstep (se 1 (by rfl) ⟨1979729, by rfl⟩ : syracuseStep 2639639 = 3959459) B3959459
theorem B2377559 : Blo 1758080 2377559 := bstep (se 1 (by rfl) ⟨1783169, by rfl⟩ : syracuseStep 2377559 = 3566339) B3566339
theorem B2639705 : Blo 1758080 2639705 := bstep (se 2 (by rfl) ⟨989889, by rfl⟩ : syracuseStep 2639705 = 1979779) B1979779
theorem B3958667 : Blo 1758080 3958667 := bstep (se 1 (by rfl) ⟨2969000, by rfl⟩ : syracuseStep 3958667 = 5938001) B5938001
theorem B4450241 : Blo 1758080 4450241 := bstep (se 2 (by rfl) ⟨1668840, by rfl⟩ : syracuseStep 4450241 = 3337681) B3337681
theorem B7325633 : Blo 1758080 7325633 := bstep (se 2 (by rfl) ⟨2747112, by rfl⟩ : syracuseStep 7325633 = 5494225) B5494225
theorem B3958721 : Blo 1758080 3958721 := bstep (se 2 (by rfl) ⟨1484520, by rfl⟩ : syracuseStep 3958721 = 2969041) B2969041
theorem B2639819 : Blo 1758080 2639819 := bstep (se 1 (by rfl) ⟨1979864, by rfl⟩ : syracuseStep 2639819 = 3959729) B3959729
theorem B2639831 : Blo 1758080 2639831 := bstep (se 1 (by rfl) ⟨1979873, by rfl⟩ : syracuseStep 2639831 = 3959747) B3959747
theorem B2967563 : Blo 1758080 2967563 := bstep (se 1 (by rfl) ⟨2225672, by rfl⟩ : syracuseStep 2967563 = 4451345) B4451345
theorem B6678551 : Blo 1758080 6678551 := bstep (se 1 (by rfl) ⟨5008913, by rfl⟩ : syracuseStep 6678551 = 10017827) B10017827
theorem B2639897 : Blo 1758080 2639897 := bstep (se 2 (by rfl) ⟨989961, by rfl⟩ : syracuseStep 2639897 = 1979923) B1979923
theorem B10020995 : Blo 1758080 10020995 := bstep (se 1 (by rfl) ⟨7515746, by rfl⟩ : syracuseStep 10020995 = 15031493) B15031493
theorem B2967691 : Blo 1758080 2967691 := bstep (se 1 (by rfl) ⟨2225768, by rfl⟩ : syracuseStep 2967691 = 4451537) B4451537
theorem B2640011 : Blo 1758080 2640011 := bstep (se 1 (by rfl) ⟨1980008, by rfl⟩ : syracuseStep 2640011 = 3960017) B3960017
theorem B2640023 : Blo 1758080 2640023 := bstep (se 1 (by rfl) ⟨1980017, by rfl⟩ : syracuseStep 2640023 = 3960035) B3960035
theorem B3958937 : Blo 1758080 3958937 := bstep (se 2 (by rfl) ⟨1484601, by rfl⟩ : syracuseStep 3958937 = 2969203) B2969203
theorem B2640089 : Blo 1758080 2640089 := bstep (se 2 (by rfl) ⟨990033, by rfl⟩ : syracuseStep 2640089 = 1980067) B1980067
theorem B3959027 : Blo 1758080 3959027 := bstep (se 1 (by rfl) ⟨2969270, by rfl⟩ : syracuseStep 3959027 = 5938541) B5938541
theorem B3959063 : Blo 1758080 3959063 := bstep (se 1 (by rfl) ⟨2969297, by rfl⟩ : syracuseStep 3959063 = 5938595) B5938595
theorem B2967833 : Blo 1758080 2967833 := bstep (se 2 (by rfl) ⟨1112937, by rfl⟩ : syracuseStep 2967833 = 2225875) B2225875
theorem B8907083 : Blo 1758080 8907083 := bstep (se 1 (by rfl) ⟨6680312, by rfl⟩ : syracuseStep 8907083 = 13360625) B13360625
theorem B7129433 : Blo 1758080 7129433 := bstep (se 2 (by rfl) ⟨2673537, by rfl⟩ : syracuseStep 7129433 = 5347075) B5347075
theorem B25373027 : Blo 1758080 25373027 := bstep (se 1 (by rfl) ⟨19029770, by rfl⟩ : syracuseStep 25373027 = 38059541) B38059541
theorem B14264707 : Blo 1758080 14264707 := bstep (se 1 (by rfl) ⟨10698530, by rfl⟩ : syracuseStep 14264707 = 21397061) B21397061
theorem B2967961 : Blo 1758080 2967961 := bstep (se 2 (by rfl) ⟨1112985, by rfl⟩ : syracuseStep 2967961 = 2225971) B2225971
theorem B22538675 : Blo 1758080 22538675 := bstep (se 1 (by rfl) ⟨16904006, by rfl⟩ : syracuseStep 22538675 = 33808013) B33808013
theorem B3959243 : Blo 1758080 3959243 := bstep (se 1 (by rfl) ⟨2969432, by rfl⟩ : syracuseStep 3959243 = 5938865) B5938865
theorem B7129565 : Blo 1758080 7129565 := bstep (se 3 (by rfl) ⟨1336793, by rfl⟩ : syracuseStep 7129565 = 2673587) B2673587
theorem B3959297 : Blo 1758080 3959297 := bstep (se 2 (by rfl) ⟨1484736, by rfl⟩ : syracuseStep 3959297 = 2969473) B2969473
theorem B20040209 : Blo 1758080 20040209 := bstep (se 2 (by rfl) ⟨7515078, by rfl⟩ : syracuseStep 20040209 = 15030157) B15030157
theorem B7514669 : Blo 1758080 7514669 := bstep (se 3 (by rfl) ⟨1409000, by rfl⟩ : syracuseStep 7514669 = 2818001) B2818001
theorem B3566209 : Blo 1758080 3566209 := bstep (se 2 (by rfl) ⟨1337328, by rfl⟩ : syracuseStep 3566209 = 2674657) B2674657
theorem B12675761 : Blo 1758080 12675761 := bstep (se 2 (by rfl) ⟨4753410, by rfl⟩ : syracuseStep 12675761 = 9506821) B9506821
theorem B6679219 : Blo 1758080 6679219 := bstep (se 1 (by rfl) ⟨5009414, by rfl⟩ : syracuseStep 6679219 = 10018829) B10018829
theorem B3959513 : Blo 1758080 3959513 := bstep (se 2 (by rfl) ⟨1484817, by rfl⟩ : syracuseStep 3959513 = 2969635) B2969635
theorem B5933789 : Blo 1758080 5933789 := bstep (se 3 (by rfl) ⟨1112585, by rfl⟩ : syracuseStep 5933789 = 2225171) B2225171
theorem B3959603 : Blo 1758080 3959603 := bstep (se 1 (by rfl) ⟨2969702, by rfl⟩ : syracuseStep 3959603 = 5939405) B5939405
theorem B3959639 : Blo 1758080 3959639 := bstep (se 1 (by rfl) ⟨2969729, by rfl⟩ : syracuseStep 3959639 = 5939459) B5939459
theorem B7515011 : Blo 1758080 7515011 := bstep (se 1 (by rfl) ⟨5636258, by rfl⟩ : syracuseStep 7515011 = 11272517) B11272517
theorem B5008321 : Blo 1758080 5008321 := bstep (se 2 (by rfl) ⟨1878120, by rfl⟩ : syracuseStep 5008321 = 3756241) B3756241
theorem B2968535 : Blo 1758080 2968535 := bstep (se 1 (by rfl) ⟨2226401, by rfl⟩ : syracuseStep 2968535 = 4452803) B4452803
theorem B3959819 : Blo 1758080 3959819 := bstep (se 1 (by rfl) ⟨2969864, by rfl⟩ : syracuseStep 3959819 = 5939729) B5939729
theorem B3959873 : Blo 1758080 3959873 := bstep (se 2 (by rfl) ⟨1484952, by rfl⟩ : syracuseStep 3959873 = 2969905) B2969905
theorem B2968663 : Blo 1758080 2968663 := bstep (se 1 (by rfl) ⟨2226497, by rfl⟩ : syracuseStep 2968663 = 4452995) B4452995
theorem B4451507 : Blo 1758080 4451507 := bstep (se 1 (by rfl) ⟨3338630, by rfl⟩ : syracuseStep 4451507 = 6677261) B6677261
theorem B3960089 : Blo 1758080 3960089 := bstep (se 2 (by rfl) ⟨1485033, by rfl⟩ : syracuseStep 3960089 = 2970067) B2970067
theorem B8449373 : Blo 1758080 8449373 := bstep (se 3 (by rfl) ⟨1584257, by rfl⟩ : syracuseStep 8449373 = 3168515) B3168515
theorem B3960179 : Blo 1758080 3960179 := bstep (se 1 (by rfl) ⟨2970134, by rfl⟩ : syracuseStep 3960179 = 5940269) B5940269
theorem B2674073 : Blo 1758080 2674073 := bstep (se 2 (by rfl) ⟨1002777, by rfl⟩ : syracuseStep 2674073 = 2005555) B2005555
theorem B11267545 : Blo 1758080 11267545 := bstep (se 2 (by rfl) ⟨4225329, by rfl⟩ : syracuseStep 11267545 = 8450659) B8450659
theorem B12537389 : Blo 1758080 12537389 := bstep (se 3 (by rfl) ⟨2350760, by rfl⟩ : syracuseStep 12537389 = 4701521) B4701521
theorem B1977943 : Blo 1758080 1977943 := bstep (se 1 (by rfl) ⟨1483457, by rfl⟩ : syracuseStep 1977943 = 2966915) B2966915
theorem B16912003 : Blo 1758080 16912003 := bstep (se 1 (by rfl) ⟨12684002, by rfl⟩ : syracuseStep 16912003 = 25368005) B25368005
theorem B4452043 : Blo 1758080 4452043 := bstep (se 1 (by rfl) ⟨3339032, by rfl⟩ : syracuseStep 4452043 = 6678065) B6678065
theorem B2969291 : Blo 1758080 2969291 := bstep (se 1 (by rfl) ⟨2226968, by rfl⟩ : syracuseStep 2969291 = 4453937) B4453937
theorem B3337985 : Blo 1758080 3337985 := bstep (se 2 (by rfl) ⟨1251744, by rfl⟩ : syracuseStep 3337985 = 2503489) B2503489
theorem B1978123 : Blo 1758080 1978123 := bstep (se 1 (by rfl) ⟨1483592, by rfl⟩ : syracuseStep 1978123 = 2967185) B2967185
theorem B5934923 : Blo 1758080 5934923 := bstep (se 1 (by rfl) ⟨4451192, by rfl⟩ : syracuseStep 5934923 = 8902385) B8902385
theorem B2969419 : Blo 1758080 2969419 := bstep (se 1 (by rfl) ⟨2227064, by rfl⟩ : syracuseStep 2969419 = 4454129) B4454129
theorem B4452185 : Blo 1758080 4452185 := bstep (se 2 (by rfl) ⟨1669569, by rfl⟩ : syracuseStep 4452185 = 3339139) B3339139
theorem B19009397 : Blo 1758080 19009397 := bstep (se 5 (by rfl) ⟨891065, by rfl⟩ : syracuseStep 19009397 = 1782131) B1782131
theorem B1978231 : Blo 1758080 1978231 := bstep (se 1 (by rfl) ⟨1483673, by rfl⟩ : syracuseStep 1978231 = 2967347) B2967347
theorem B6680465 : Blo 1758080 6680465 := bstep (se 2 (by rfl) ⟨2505174, by rfl⟩ : syracuseStep 6680465 = 5010349) B5010349
theorem B7614425 : Blo 1758080 7614425 := bstep (se 2 (by rfl) ⟨2855409, by rfl⟩ : syracuseStep 7614425 = 5710819) B5710819
theorem B2969561 : Blo 1758080 2969561 := bstep (se 2 (by rfl) ⟨1113585, by rfl⟩ : syracuseStep 2969561 = 2227171) B2227171
theorem B8146909 : Blo 1758080 8146909 := bstep (se 3 (by rfl) ⟨1527545, by rfl⟩ : syracuseStep 8146909 = 3055091) B3055091
theorem B33804323 : Blo 1758080 33804323 := bstep (se 1 (by rfl) ⟨25353242, by rfl⟩ : syracuseStep 33804323 = 50706485) B50706485
theorem B1978411 : Blo 1758080 1978411 := bstep (se 1 (by rfl) ⟨1483808, by rfl⟩ : syracuseStep 1978411 = 2967617) B2967617
theorem B8908865 : Blo 1758080 8908865 := bstep (se 2 (by rfl) ⟨3340824, by rfl⟩ : syracuseStep 8908865 = 6681649) B6681649
theorem B3338327 : Blo 1758080 3338327 := bstep (se 1 (by rfl) ⟨2503745, by rfl⟩ : syracuseStep 3338327 = 5007491) B5007491
theorem B5935193 : Blo 1758080 5935193 := bstep (se 2 (by rfl) ⟨2225697, by rfl⟩ : syracuseStep 5935193 = 4451395) B4451395
theorem B2969689 : Blo 1758080 2969689 := bstep (se 2 (by rfl) ⟨1113633, by rfl⟩ : syracuseStep 2969689 = 2227267) B2227267
theorem B1978519 : Blo 1758080 1978519 := bstep (se 1 (by rfl) ⟨1483889, by rfl⟩ : syracuseStep 1978519 = 2967779) B2967779
theorem B21401921 : Blo 1758080 21401921 := bstep (se 2 (by rfl) ⟨8025720, by rfl⟩ : syracuseStep 21401921 = 16051441) B16051441
theorem B1978699 : Blo 1758080 1978699 := bstep (se 1 (by rfl) ⟨1484024, by rfl⟩ : syracuseStep 1978699 = 2968049) B2968049
theorem B3568025 : Blo 1758080 3568025 := bstep (se 2 (by rfl) ⟨1338009, by rfl⟩ : syracuseStep 3568025 = 2676019) B2676019
theorem B19026353 : Blo 1758080 19026353 := bstep (se 2 (by rfl) ⟨7134882, by rfl⟩ : syracuseStep 19026353 = 14269765) B14269765
theorem B1978807 : Blo 1758080 1978807 := bstep (se 1 (by rfl) ⟨1484105, by rfl⟩ : syracuseStep 1978807 = 2968211) B2968211
theorem B10023385 : Blo 1758080 10023385 := bstep (se 2 (by rfl) ⟨3758769, by rfl⟩ : syracuseStep 10023385 = 7517539) B7517539
theorem B34271761 : Blo 1758080 34271761 := bstep (se 2 (by rfl) ⟨12851910, by rfl⟩ : syracuseStep 34271761 = 25703821) B25703821
theorem B5714455 : Blo 1758080 5714455 := bstep (se 1 (by rfl) ⟨4285841, by rfl⟩ : syracuseStep 5714455 = 8571683) B8571683
theorem B6681163 : Blo 1758080 6681163 := bstep (se 1 (by rfl) ⟨5010872, by rfl⟩ : syracuseStep 6681163 = 10021745) B10021745
theorem B1978987 : Blo 1758080 1978987 := bstep (se 1 (by rfl) ⟨1484240, by rfl⟩ : syracuseStep 1978987 = 2968481) B2968481
theorem B8901251 : Blo 1758080 8901251 := bstep (se 1 (by rfl) ⟨6675938, by rfl⟩ : syracuseStep 8901251 = 13351877) B13351877
theorem B4453015 : Blo 1758080 4453015 := bstep (se 1 (by rfl) ⟨3339761, by rfl⟩ : syracuseStep 4453015 = 6679523) B6679523
theorem B1979095 : Blo 1758080 1979095 := bstep (se 1 (by rfl) ⟨1484321, by rfl⟩ : syracuseStep 1979095 = 2968643) B2968643
theorem B3338995 : Blo 1758080 3338995 := bstep (se 1 (by rfl) ⟨2504246, by rfl⟩ : syracuseStep 3338995 = 5008493) B5008493
theorem B5935895 : Blo 1758080 5935895 := bstep (se 1 (by rfl) ⟨4451921, by rfl⟩ : syracuseStep 5935895 = 8903843) B8903843
theorem B16044875 : Blo 1758080 16044875 := bstep (se 1 (by rfl) ⟨12033656, by rfl⟩ : syracuseStep 16044875 = 24067313) B24067313
theorem B6681437 : Blo 1758080 6681437 := bstep (se 3 (by rfl) ⟨1252769, by rfl⟩ : syracuseStep 6681437 = 2505539) B2505539
theorem B1758091 : Blo 1758080 1758091 := bstep (se 1 (by rfl) ⟨1318568, by rfl⟩ : syracuseStep 1758091 = 2637137) B2637137
theorem B1782667 : Blo 1758080 1782667 := bstep (se 1 (by rfl) ⟨1337000, by rfl⟩ : syracuseStep 1782667 = 2674001) B2674001
theorem B1979275 : Blo 1758080 1979275 := bstep (se 1 (by rfl) ⟨1484456, by rfl⟩ : syracuseStep 1979275 = 2968913) B2968913
theorem B1758103 : Blo 1758080 1758103 := bstep (se 1 (by rfl) ⟨1318577, by rfl⟩ : syracuseStep 1758103 = 2637155) B2637155
theorem B1758123 : Blo 1758080 1758123 := bstep (se 1 (by rfl) ⟨1318592, by rfl⟩ : syracuseStep 1758123 = 2637185) B2637185
theorem B22852529 : Blo 1758080 22852529 := bstep (se 2 (by rfl) ⟨8569698, by rfl⟩ : syracuseStep 22852529 = 17139397) B17139397
theorem B1758135 : Blo 1758080 1758135 := bstep (se 1 (by rfl) ⟨1318601, by rfl⟩ : syracuseStep 1758135 = 2637203) B2637203
theorem B5075905 : Blo 1758080 5075905 := bstep (se 2 (by rfl) ⟨1903464, by rfl⟩ : syracuseStep 5075905 = 3806929) B3806929
theorem B1758155 : Blo 1758080 1758155 := bstep (se 1 (by rfl) ⟨1318616, by rfl⟩ : syracuseStep 1758155 = 2637233) B2637233
theorem B1758167 : Blo 1758080 1758167 := bstep (se 1 (by rfl) ⟨1318625, by rfl⟩ : syracuseStep 1758167 = 2637251) B2637251
theorem B1758187 : Blo 1758080 1758187 := bstep (se 1 (by rfl) ⟨1318640, by rfl⟩ : syracuseStep 1758187 = 2637281) B2637281
theorem B1758199 : Blo 1758080 1758199 := bstep (se 1 (by rfl) ⟨1318649, by rfl⟩ : syracuseStep 1758199 = 2637299) B2637299
theorem B1979383 : Blo 1758080 1979383 := bstep (se 1 (by rfl) ⟨1484537, by rfl⟩ : syracuseStep 1979383 = 2969075) B2969075
theorem B1758219 : Blo 1758080 1758219 := bstep (se 1 (by rfl) ⟨1318664, by rfl⟩ : syracuseStep 1758219 = 2637329) B2637329
theorem B1758231 : Blo 1758080 1758231 := bstep (se 1 (by rfl) ⟨1318673, by rfl⟩ : syracuseStep 1758231 = 2637347) B2637347
theorem B3757079 : Blo 1758080 3757079 := bstep (se 1 (by rfl) ⟨2817809, by rfl⟩ : syracuseStep 3757079 = 5635619) B5635619
theorem B2503705 : Blo 1758080 2503705 := bstep (se 2 (by rfl) ⟨938889, by rfl⟩ : syracuseStep 2503705 = 1877779) B1877779
theorem B1758251 : Blo 1758080 1758251 := bstep (se 1 (by rfl) ⟨1318688, by rfl⟩ : syracuseStep 1758251 = 2637377) B2637377
theorem B1758263 : Blo 1758080 1758263 := bstep (se 1 (by rfl) ⟨1318697, by rfl⟩ : syracuseStep 1758263 = 2637395) B2637395
theorem B2225227 : Blo 1758080 2225227 := bstep (se 1 (by rfl) ⟨1668920, by rfl⟩ : syracuseStep 2225227 = 3337841) B3337841
theorem B1758283 : Blo 1758080 1758283 := bstep (se 1 (by rfl) ⟨1318712, by rfl⟩ : syracuseStep 1758283 = 2637425) B2637425
theorem B4453451 : Blo 1758080 4453451 := bstep (se 1 (by rfl) ⟨3340088, by rfl⟩ : syracuseStep 4453451 = 6680177) B6680177
theorem B1758295 : Blo 1758080 1758295 := bstep (se 1 (by rfl) ⟨1318721, by rfl⟩ : syracuseStep 1758295 = 2637443) B2637443
theorem B2675801 : Blo 1758080 2675801 := bstep (se 2 (by rfl) ⟨1003425, by rfl⟩ : syracuseStep 2675801 = 2006851) B2006851
theorem B21394525 : Blo 1758080 21394525 := bstep (se 3 (by rfl) ⟨4011473, by rfl⟩ : syracuseStep 21394525 = 8022947) B8022947
theorem B1758315 : Blo 1758080 1758315 := bstep (se 1 (by rfl) ⟨1318736, by rfl⟩ : syracuseStep 1758315 = 2637473) B2637473
theorem B1758327 : Blo 1758080 1758327 := bstep (se 1 (by rfl) ⟨1318745, by rfl⟩ : syracuseStep 1758327 = 2637491) B2637491
theorem B12039299 : Blo 1758080 12039299 := bstep (se 1 (by rfl) ⟨9029474, by rfl⟩ : syracuseStep 12039299 = 18058949) B18058949
theorem B1758347 : Blo 1758080 1758347 := bstep (se 1 (by rfl) ⟨1318760, by rfl⟩ : syracuseStep 1758347 = 2637521) B2637521
theorem B2503819 : Blo 1758080 2503819 := bstep (se 1 (by rfl) ⟨1877864, by rfl⟩ : syracuseStep 2503819 = 3755729) B3755729
theorem B1758359 : Blo 1758080 1758359 := bstep (se 1 (by rfl) ⟨1318769, by rfl⟩ : syracuseStep 1758359 = 2637539) B2637539
theorem B1758379 : Blo 1758080 1758379 := bstep (se 1 (by rfl) ⟨1318784, by rfl⟩ : syracuseStep 1758379 = 2637569) B2637569
theorem B1979563 : Blo 1758080 1979563 := bstep (se 1 (by rfl) ⟨1484672, by rfl⟩ : syracuseStep 1979563 = 2969345) B2969345
theorem B3339443 : Blo 1758080 3339443 := bstep (se 1 (by rfl) ⟨2504582, by rfl⟩ : syracuseStep 3339443 = 5009165) B5009165
theorem B1758391 : Blo 1758080 1758391 := bstep (se 1 (by rfl) ⟨1318793, by rfl⟩ : syracuseStep 1758391 = 2637587) B2637587
theorem B1758411 : Blo 1758080 1758411 := bstep (se 1 (by rfl) ⟨1318808, by rfl⟩ : syracuseStep 1758411 = 2637617) B2637617
theorem B3757259 : Blo 1758080 3757259 := bstep (se 1 (by rfl) ⟨2817944, by rfl⟩ : syracuseStep 3757259 = 5635889) B5635889
theorem B7517387 : Blo 1758080 7517387 := bstep (se 1 (by rfl) ⟨5638040, by rfl⟩ : syracuseStep 7517387 = 11276081) B11276081
theorem B1758423 : Blo 1758080 1758423 := bstep (se 1 (by rfl) ⟨1318817, by rfl⟩ : syracuseStep 1758423 = 2637635) B2637635
theorem B3339481 : Blo 1758080 3339481 := bstep (se 2 (by rfl) ⟨1252305, by rfl⟩ : syracuseStep 3339481 = 2504611) B2504611
theorem B1758443 : Blo 1758080 1758443 := bstep (se 1 (by rfl) ⟨1318832, by rfl⟩ : syracuseStep 1758443 = 2637665) B2637665
theorem B1758455 : Blo 1758080 1758455 := bstep (se 1 (by rfl) ⟨1318841, by rfl⟩ : syracuseStep 1758455 = 2637683) B2637683
theorem B1758475 : Blo 1758080 1758475 := bstep (se 1 (by rfl) ⟨1318856, by rfl⟩ : syracuseStep 1758475 = 2637713) B2637713
theorem B1758487 : Blo 1758080 1758487 := bstep (se 1 (by rfl) ⟨1318865, by rfl⟩ : syracuseStep 1758487 = 2637731) B2637731
theorem B1979671 : Blo 1758080 1979671 := bstep (se 1 (by rfl) ⟨1484753, by rfl⟩ : syracuseStep 1979671 = 2969507) B2969507
theorem B1758507 : Blo 1758080 1758507 := bstep (se 1 (by rfl) ⟨1318880, by rfl⟩ : syracuseStep 1758507 = 2637761) B2637761
theorem B5936435 : Blo 1758080 5936435 := bstep (se 1 (by rfl) ⟨4452326, by rfl⟩ : syracuseStep 5936435 = 8904653) B8904653
theorem B1758519 : Blo 1758080 1758519 := bstep (se 1 (by rfl) ⟨1318889, by rfl⟩ : syracuseStep 1758519 = 2637779) B2637779
theorem B1758539 : Blo 1758080 1758539 := bstep (se 1 (by rfl) ⟨1318904, by rfl⟩ : syracuseStep 1758539 = 2637809) B2637809
theorem B2225495 : Blo 1758080 2225495 := bstep (se 1 (by rfl) ⟨1669121, by rfl⟩ : syracuseStep 2225495 = 3338243) B3338243
theorem B1758551 : Blo 1758080 1758551 := bstep (se 1 (by rfl) ⟨1318913, by rfl⟩ : syracuseStep 1758551 = 2637827) B2637827
theorem B1758571 : Blo 1758080 1758571 := bstep (se 1 (by rfl) ⟨1318928, by rfl⟩ : syracuseStep 1758571 = 2637857) B2637857
theorem B20043125 : Blo 1758080 20043125 := bstep (se 5 (by rfl) ⟨939521, by rfl⟩ : syracuseStep 20043125 = 1879043) B1879043
theorem B1758583 : Blo 1758080 1758583 := bstep (se 1 (by rfl) ⟨1318937, by rfl⟩ : syracuseStep 1758583 = 2637875) B2637875
theorem B1758603 : Blo 1758080 1758603 := bstep (se 1 (by rfl) ⟨1318952, by rfl⟩ : syracuseStep 1758603 = 2637905) B2637905
theorem B1758615 : Blo 1758080 1758615 := bstep (se 1 (by rfl) ⟨1318961, by rfl⟩ : syracuseStep 1758615 = 2637923) B2637923
theorem B1758635 : Blo 1758080 1758635 := bstep (se 1 (by rfl) ⟨1318976, by rfl⟩ : syracuseStep 1758635 = 2637953) B2637953
theorem B1758647 : Blo 1758080 1758647 := bstep (se 1 (by rfl) ⟨1318985, by rfl⟩ : syracuseStep 1758647 = 2637971) B2637971
theorem B4453825 : Blo 1758080 4453825 := bstep (se 2 (by rfl) ⟨1670184, by rfl⟩ : syracuseStep 4453825 = 3340369) B3340369
theorem B1758667 : Blo 1758080 1758667 := bstep (se 1 (by rfl) ⟨1319000, by rfl⟩ : syracuseStep 1758667 = 2638001) B2638001
theorem B1979851 : Blo 1758080 1979851 := bstep (se 1 (by rfl) ⟨1484888, by rfl⟩ : syracuseStep 1979851 = 2969777) B2969777
theorem B1758679 : Blo 1758080 1758679 := bstep (se 1 (by rfl) ⟨1319009, by rfl⟩ : syracuseStep 1758679 = 2638019) B2638019
theorem B1758699 : Blo 1758080 1758699 := bstep (se 1 (by rfl) ⟨1319024, by rfl⟩ : syracuseStep 1758699 = 2638049) B2638049
theorem B1758711 : Blo 1758080 1758711 := bstep (se 1 (by rfl) ⟨1319033, by rfl⟩ : syracuseStep 1758711 = 2638067) B2638067
theorem B1758731 : Blo 1758080 1758731 := bstep (se 1 (by rfl) ⟨1319048, by rfl⟩ : syracuseStep 1758731 = 2638097) B2638097
theorem B1758743 : Blo 1758080 1758743 := bstep (se 1 (by rfl) ⟨1319057, by rfl⟩ : syracuseStep 1758743 = 2638115) B2638115
theorem B6018583 : Blo 1758080 6018583 := bstep (se 1 (by rfl) ⟨4513937, by rfl⟩ : syracuseStep 6018583 = 9027875) B9027875
theorem B6682135 : Blo 1758080 6682135 := bstep (se 1 (by rfl) ⟨5011601, by rfl⟩ : syracuseStep 6682135 = 10023203) B10023203
theorem B1758763 : Blo 1758080 1758763 := bstep (se 1 (by rfl) ⟨1319072, by rfl⟩ : syracuseStep 1758763 = 2638145) B2638145
theorem B1758775 : Blo 1758080 1758775 := bstep (se 1 (by rfl) ⟨1319081, by rfl⟩ : syracuseStep 1758775 = 2638163) B2638163
theorem B1979959 : Blo 1758080 1979959 := bstep (se 1 (by rfl) ⟨1484969, by rfl⟩ : syracuseStep 1979959 = 2969939) B2969939
theorem B5936705 : Blo 1758080 5936705 := bstep (se 2 (by rfl) ⟨2226264, by rfl⟩ : syracuseStep 5936705 = 4452529) B4452529
theorem B1758795 : Blo 1758080 1758795 := bstep (se 1 (by rfl) ⟨1319096, by rfl⟩ : syracuseStep 1758795 = 2638193) B2638193
theorem B1758807 : Blo 1758080 1758807 := bstep (se 1 (by rfl) ⟨1319105, by rfl⟩ : syracuseStep 1758807 = 2638211) B2638211
theorem B1758827 : Blo 1758080 1758827 := bstep (se 1 (by rfl) ⟨1319120, by rfl⟩ : syracuseStep 1758827 = 2638241) B2638241
theorem B1758839 : Blo 1758080 1758839 := bstep (se 1 (by rfl) ⟨1319129, by rfl⟩ : syracuseStep 1758839 = 2638259) B2638259
theorem B1758859 : Blo 1758080 1758859 := bstep (se 1 (by rfl) ⟨1319144, by rfl⟩ : syracuseStep 1758859 = 2638289) B2638289
theorem B1758871 : Blo 1758080 1758871 := bstep (se 1 (by rfl) ⟨1319153, by rfl⟩ : syracuseStep 1758871 = 2638307) B2638307
theorem B3339929 : Blo 1758080 3339929 := bstep (se 2 (by rfl) ⟨1252473, by rfl⟩ : syracuseStep 3339929 = 2504947) B2504947
theorem B1758891 : Blo 1758080 1758891 := bstep (se 1 (by rfl) ⟨1319168, by rfl⟩ : syracuseStep 1758891 = 2638337) B2638337
theorem B1758903 : Blo 1758080 1758903 := bstep (se 1 (by rfl) ⟨1319177, by rfl⟩ : syracuseStep 1758903 = 2638355) B2638355
theorem B1758923 : Blo 1758080 1758923 := bstep (se 1 (by rfl) ⟨1319192, by rfl⟩ : syracuseStep 1758923 = 2638385) B2638385
theorem B1758935 : Blo 1758080 1758935 := bstep (se 1 (by rfl) ⟨1319201, by rfl⟩ : syracuseStep 1758935 = 2638403) B2638403
theorem B1758955 : Blo 1758080 1758955 := bstep (se 1 (by rfl) ⟨1319216, by rfl⟩ : syracuseStep 1758955 = 2638433) B2638433
theorem B1758967 : Blo 1758080 1758967 := bstep (se 1 (by rfl) ⟨1319225, by rfl⟩ : syracuseStep 1758967 = 2638451) B2638451
theorem B1758987 : Blo 1758080 1758987 := bstep (se 1 (by rfl) ⟨1319240, by rfl⟩ : syracuseStep 1758987 = 2638481) B2638481
theorem B1758999 : Blo 1758080 1758999 := bstep (se 1 (by rfl) ⟨1319249, by rfl⟩ : syracuseStep 1758999 = 2638499) B2638499
theorem B1759019 : Blo 1758080 1759019 := bstep (se 1 (by rfl) ⟨1319264, by rfl⟩ : syracuseStep 1759019 = 2638529) B2638529
theorem B1759031 : Blo 1758080 1759031 := bstep (se 1 (by rfl) ⟨1319273, by rfl⟩ : syracuseStep 1759031 = 2638547) B2638547
theorem B1759051 : Blo 1758080 1759051 := bstep (se 1 (by rfl) ⟨1319288, by rfl⟩ : syracuseStep 1759051 = 2638577) B2638577
theorem B1759063 : Blo 1758080 1759063 := bstep (se 1 (by rfl) ⟨1319297, by rfl⟩ : syracuseStep 1759063 = 2638595) B2638595
theorem B1759083 : Blo 1758080 1759083 := bstep (se 1 (by rfl) ⟨1319312, by rfl⟩ : syracuseStep 1759083 = 2638625) B2638625
theorem B1759095 : Blo 1758080 1759095 := bstep (se 1 (by rfl) ⟨1319321, by rfl⟩ : syracuseStep 1759095 = 2638643) B2638643
theorem B1759115 : Blo 1758080 1759115 := bstep (se 1 (by rfl) ⟨1319336, by rfl⟩ : syracuseStep 1759115 = 2638673) B2638673
theorem B1759127 : Blo 1758080 1759127 := bstep (se 1 (by rfl) ⟨1319345, by rfl⟩ : syracuseStep 1759127 = 2638691) B2638691
theorem B1759147 : Blo 1758080 1759147 := bstep (se 1 (by rfl) ⟨1319360, by rfl⟩ : syracuseStep 1759147 = 2638721) B2638721
theorem B1759159 : Blo 1758080 1759159 := bstep (se 1 (by rfl) ⟨1319369, by rfl⟩ : syracuseStep 1759159 = 2638739) B2638739
theorem B1759179 : Blo 1758080 1759179 := bstep (se 1 (by rfl) ⟨1319384, by rfl⟩ : syracuseStep 1759179 = 2638769) B2638769
theorem B1759191 : Blo 1758080 1759191 := bstep (se 1 (by rfl) ⟨1319393, by rfl⟩ : syracuseStep 1759191 = 2638787) B2638787
theorem B1759211 : Blo 1758080 1759211 := bstep (se 1 (by rfl) ⟨1319408, by rfl⟩ : syracuseStep 1759211 = 2638817) B2638817
theorem B1759223 : Blo 1758080 1759223 := bstep (se 1 (by rfl) ⟨1319417, by rfl⟩ : syracuseStep 1759223 = 2638835) B2638835
theorem B2005003 : Blo 1758080 2005003 := bstep (se 1 (by rfl) ⟨1503752, by rfl⟩ : syracuseStep 2005003 = 3007505) B3007505
theorem B1759243 : Blo 1758080 1759243 := bstep (se 1 (by rfl) ⟨1319432, by rfl⟩ : syracuseStep 1759243 = 2638865) B2638865
theorem B2226199 : Blo 1758080 2226199 := bstep (se 1 (by rfl) ⟨1669649, by rfl⟩ : syracuseStep 2226199 = 3339299) B3339299
theorem B1759255 : Blo 1758080 1759255 := bstep (se 1 (by rfl) ⟨1319441, by rfl⟩ : syracuseStep 1759255 = 2638883) B2638883
theorem B4454423 : Blo 1758080 4454423 := bstep (se 1 (by rfl) ⟨3340817, by rfl⟩ : syracuseStep 4454423 = 6681635) B6681635
theorem B32110627 : Blo 1758080 32110627 := bstep (se 1 (by rfl) ⟨24082970, by rfl⟩ : syracuseStep 32110627 = 48165941) B48165941
theorem B1759275 : Blo 1758080 1759275 := bstep (se 1 (by rfl) ⟨1319456, by rfl⟩ : syracuseStep 1759275 = 2638913) B2638913
theorem B1759287 : Blo 1758080 1759287 := bstep (se 1 (by rfl) ⟨1319465, by rfl⟩ : syracuseStep 1759287 = 2638931) B2638931
theorem B1759307 : Blo 1758080 1759307 := bstep (se 1 (by rfl) ⟨1319480, by rfl⟩ : syracuseStep 1759307 = 2638961) B2638961
theorem B1783883 : Blo 1758080 1783883 := bstep (se 1 (by rfl) ⟨1337912, by rfl⟩ : syracuseStep 1783883 = 2675825) B2675825
theorem B1759319 : Blo 1758080 1759319 := bstep (se 1 (by rfl) ⟨1319489, by rfl⟩ : syracuseStep 1759319 = 2638979) B2638979
theorem B5937245 : Blo 1758080 5937245 := bstep (se 3 (by rfl) ⟨1113233, by rfl⟩ : syracuseStep 5937245 = 2226467) B2226467
theorem B1759339 : Blo 1758080 1759339 := bstep (se 1 (by rfl) ⟨1319504, by rfl⟩ : syracuseStep 1759339 = 2639009) B2639009
theorem B1759351 : Blo 1758080 1759351 := bstep (se 1 (by rfl) ⟨1319513, by rfl⟩ : syracuseStep 1759351 = 2639027) B2639027
theorem B1759371 : Blo 1758080 1759371 := bstep (se 1 (by rfl) ⟨1319528, by rfl⟩ : syracuseStep 1759371 = 2639057) B2639057
theorem B1759383 : Blo 1758080 1759383 := bstep (se 1 (by rfl) ⟨1319537, by rfl⟩ : syracuseStep 1759383 = 2639075) B2639075
theorem B1759403 : Blo 1758080 1759403 := bstep (se 1 (by rfl) ⟨1319552, by rfl⟩ : syracuseStep 1759403 = 2639105) B2639105
theorem B1759415 : Blo 1758080 1759415 := bstep (se 1 (by rfl) ⟨1319561, by rfl⟩ : syracuseStep 1759415 = 2639123) B2639123
theorem B1759435 : Blo 1758080 1759435 := bstep (se 1 (by rfl) ⟨1319576, by rfl⟩ : syracuseStep 1759435 = 2639153) B2639153
theorem B1759447 : Blo 1758080 1759447 := bstep (se 1 (by rfl) ⟨1319585, by rfl⟩ : syracuseStep 1759447 = 2639171) B2639171
theorem B1759467 : Blo 1758080 1759467 := bstep (se 1 (by rfl) ⟨1319600, by rfl⟩ : syracuseStep 1759467 = 2639201) B2639201
theorem B1759479 : Blo 1758080 1759479 := bstep (se 1 (by rfl) ⟨1319609, by rfl⟩ : syracuseStep 1759479 = 2639219) B2639219
theorem B1759499 : Blo 1758080 1759499 := bstep (se 1 (by rfl) ⟨1319624, by rfl⟩ : syracuseStep 1759499 = 2639249) B2639249
theorem B7510295 : Blo 1758080 7510295 := bstep (se 1 (by rfl) ⟨5632721, by rfl⟩ : syracuseStep 7510295 = 11265443) B11265443
theorem B1759511 : Blo 1758080 1759511 := bstep (se 1 (by rfl) ⟨1319633, by rfl⟩ : syracuseStep 1759511 = 2639267) B2639267
theorem B1759531 : Blo 1758080 1759531 := bstep (se 1 (by rfl) ⟨1319648, by rfl⟩ : syracuseStep 1759531 = 2639297) B2639297
theorem B1759543 : Blo 1758080 1759543 := bstep (se 1 (by rfl) ⟨1319657, by rfl⟩ : syracuseStep 1759543 = 2639315) B2639315
theorem B1759563 : Blo 1758080 1759563 := bstep (se 1 (by rfl) ⟨1319672, by rfl⟩ : syracuseStep 1759563 = 2639345) B2639345
theorem B1759575 : Blo 1758080 1759575 := bstep (se 1 (by rfl) ⟨1319681, by rfl⟩ : syracuseStep 1759575 = 2639363) B2639363
theorem B1759595 : Blo 1758080 1759595 := bstep (se 1 (by rfl) ⟨1319696, by rfl⟩ : syracuseStep 1759595 = 2639393) B2639393
theorem B1759607 : Blo 1758080 1759607 := bstep (se 1 (by rfl) ⟨1319705, by rfl⟩ : syracuseStep 1759607 = 2639411) B2639411
theorem B3340673 : Blo 1758080 3340673 := bstep (se 2 (by rfl) ⟨1252752, by rfl⟩ : syracuseStep 3340673 = 2505505) B2505505
theorem B1759627 : Blo 1758080 1759627 := bstep (se 1 (by rfl) ⟨1319720, by rfl⟩ : syracuseStep 1759627 = 2639441) B2639441
theorem B1759639 : Blo 1758080 1759639 := bstep (se 1 (by rfl) ⟨1319729, by rfl⟩ : syracuseStep 1759639 = 2639459) B2639459
theorem B1759659 : Blo 1758080 1759659 := bstep (se 1 (by rfl) ⟨1319744, by rfl⟩ : syracuseStep 1759659 = 2639489) B2639489
theorem B1759671 : Blo 1758080 1759671 := bstep (se 1 (by rfl) ⟨1319753, by rfl⟩ : syracuseStep 1759671 = 2639507) B2639507
theorem B2505163 : Blo 1758080 2505163 := bstep (se 1 (by rfl) ⟨1878872, by rfl⟩ : syracuseStep 2505163 = 3757745) B3757745
theorem B1759691 : Blo 1758080 1759691 := bstep (se 1 (by rfl) ⟨1319768, by rfl⟩ : syracuseStep 1759691 = 2639537) B2639537
theorem B13720013 : Blo 1758080 13720013 := bstep (se 3 (by rfl) ⟨2572502, by rfl⟩ : syracuseStep 13720013 = 5145005) B5145005
theorem B1759703 : Blo 1758080 1759703 := bstep (se 1 (by rfl) ⟨1319777, by rfl⟩ : syracuseStep 1759703 = 2639555) B2639555
theorem B6429149 : Blo 1758080 6429149 := bstep (se 3 (by rfl) ⟨1205465, by rfl⟩ : syracuseStep 6429149 = 2410931) B2410931
theorem B1759723 : Blo 1758080 1759723 := bstep (se 1 (by rfl) ⟨1319792, by rfl⟩ : syracuseStep 1759723 = 2639585) B2639585
theorem B1759735 : Blo 1758080 1759735 := bstep (se 1 (by rfl) ⟨1319801, by rfl⟩ : syracuseStep 1759735 = 2639603) B2639603
theorem B1759755 : Blo 1758080 1759755 := bstep (se 1 (by rfl) ⟨1319816, by rfl⟩ : syracuseStep 1759755 = 2639633) B2639633
theorem B1759767 : Blo 1758080 1759767 := bstep (se 1 (by rfl) ⟨1319825, by rfl⟩ : syracuseStep 1759767 = 2639651) B2639651
theorem B1759787 : Blo 1758080 1759787 := bstep (se 1 (by rfl) ⟨1319840, by rfl⟩ : syracuseStep 1759787 = 2639681) B2639681
theorem B1759799 : Blo 1758080 1759799 := bstep (se 1 (by rfl) ⟨1319849, by rfl⟩ : syracuseStep 1759799 = 2639699) B2639699
theorem B7510603 : Blo 1758080 7510603 := bstep (se 1 (by rfl) ⟨5632952, by rfl⟩ : syracuseStep 7510603 = 11265905) B11265905
theorem B1759819 : Blo 1758080 1759819 := bstep (se 1 (by rfl) ⟨1319864, by rfl⟩ : syracuseStep 1759819 = 2639729) B2639729
theorem B1759831 : Blo 1758080 1759831 := bstep (se 1 (by rfl) ⟨1319873, by rfl⟩ : syracuseStep 1759831 = 2639747) B2639747
theorem B5012057 : Blo 1758080 5012057 := bstep (se 2 (by rfl) ⟨1879521, by rfl⟩ : syracuseStep 5012057 = 3759043) B3759043
theorem B1759851 : Blo 1758080 1759851 := bstep (se 1 (by rfl) ⟨1319888, by rfl⟩ : syracuseStep 1759851 = 2639777) B2639777
theorem B1759863 : Blo 1758080 1759863 := bstep (se 1 (by rfl) ⟨1319897, by rfl⟩ : syracuseStep 1759863 = 2639795) B2639795
theorem B3340939 : Blo 1758080 3340939 := bstep (se 1 (by rfl) ⟨2505704, by rfl⟩ : syracuseStep 3340939 = 5011409) B5011409
theorem B1759883 : Blo 1758080 1759883 := bstep (se 1 (by rfl) ⟨1319912, by rfl⟩ : syracuseStep 1759883 = 2639825) B2639825
theorem B1759895 : Blo 1758080 1759895 := bstep (se 1 (by rfl) ⟨1319921, by rfl⟩ : syracuseStep 1759895 = 2639843) B2639843
theorem B1759915 : Blo 1758080 1759915 := bstep (se 1 (by rfl) ⟨1319936, by rfl⟩ : syracuseStep 1759915 = 2639873) B2639873
theorem B9173683 : Blo 1758080 9173683 := bstep (se 1 (by rfl) ⟨6880262, by rfl⟩ : syracuseStep 9173683 = 13760525) B13760525
theorem B1759927 : Blo 1758080 1759927 := bstep (se 1 (by rfl) ⟨1319945, by rfl⟩ : syracuseStep 1759927 = 2639891) B2639891
theorem B1759947 : Blo 1758080 1759947 := bstep (se 1 (by rfl) ⟨1319960, by rfl⟩ : syracuseStep 1759947 = 2639921) B2639921
theorem B2505431 : Blo 1758080 2505431 := bstep (se 1 (by rfl) ⟨1879073, by rfl⟩ : syracuseStep 2505431 = 3758147) B3758147
theorem B1759959 : Blo 1758080 1759959 := bstep (se 1 (by rfl) ⟨1319969, by rfl⟩ : syracuseStep 1759959 = 2639939) B2639939
theorem B6339293 : Blo 1758080 6339293 := bstep (se 3 (by rfl) ⟨1188617, by rfl⟩ : syracuseStep 6339293 = 2377235) B2377235
theorem B1759979 : Blo 1758080 1759979 := bstep (se 1 (by rfl) ⟨1319984, by rfl⟩ : syracuseStep 1759979 = 2639969) B2639969
theorem B1759991 : Blo 1758080 1759991 := bstep (se 1 (by rfl) ⟨1319993, by rfl⟩ : syracuseStep 1759991 = 2639987) B2639987
theorem B1760011 : Blo 1758080 1760011 := bstep (se 1 (by rfl) ⟨1320008, by rfl⟩ : syracuseStep 1760011 = 2640017) B2640017
theorem B10017553 : Blo 1758080 10017553 := bstep (se 2 (by rfl) ⟨3756582, by rfl⟩ : syracuseStep 10017553 = 7513165) B7513165
theorem B1760023 : Blo 1758080 1760023 := bstep (se 1 (by rfl) ⟨1320017, by rfl⟩ : syracuseStep 1760023 = 2640035) B2640035
theorem B1760043 : Blo 1758080 1760043 := bstep (se 1 (by rfl) ⟨1320032, by rfl⟩ : syracuseStep 1760043 = 2640065) B2640065
theorem B6339379 : Blo 1758080 6339379 := bstep (se 1 (by rfl) ⟨4754534, by rfl⟩ : syracuseStep 6339379 = 9509069) B9509069
theorem B3758899 : Blo 1758080 3758899 := bstep (se 1 (by rfl) ⟨2819174, by rfl⟩ : syracuseStep 3758899 = 5638349) B5638349
theorem B1760055 : Blo 1758080 1760055 := bstep (se 1 (by rfl) ⟨1320041, by rfl⟩ : syracuseStep 1760055 = 2640083) B2640083
theorem B15031115 : Blo 1758080 15031115 := bstep (se 1 (by rfl) ⟨11273336, by rfl⟩ : syracuseStep 15031115 = 22546673) B22546673
theorem B1760075 : Blo 1758080 1760075 := bstep (se 1 (by rfl) ⟨1320056, by rfl⟩ : syracuseStep 1760075 = 2640113) B2640113
theorem B7510877 : Blo 1758080 7510877 := bstep (se 3 (by rfl) ⟨1408289, by rfl⟩ : syracuseStep 7510877 = 2816579) B2816579
theorem B2005879 : Blo 1758080 2005879 := bstep (se 1 (by rfl) ⟨1504409, by rfl⟩ : syracuseStep 2005879 = 3008819) B3008819
theorem B6675331 : Blo 1758080 6675331 := bstep (se 1 (by rfl) ⟨5006498, by rfl⟩ : syracuseStep 6675331 = 10012997) B10012997
theorem B3955787 : Blo 1758080 3955787 := bstep (se 1 (by rfl) ⟨2966840, by rfl⟩ : syracuseStep 3955787 = 5933681) B5933681
theorem B3341387 : Blo 1758080 3341387 := bstep (se 1 (by rfl) ⟨2506040, by rfl⟩ : syracuseStep 3341387 = 5012081) B5012081
theorem B3955841 : Blo 1758080 3955841 := bstep (se 2 (by rfl) ⟨1483440, by rfl⟩ : syracuseStep 3955841 = 2966881) B2966881
theorem B2817175 : Blo 1758080 2817175 := bstep (se 1 (by rfl) ⟨2112881, by rfl⟩ : syracuseStep 2817175 = 4225763) B4225763
theorem B3169459 : Blo 1758080 3169459 := bstep (se 1 (by rfl) ⟨2377094, by rfl⟩ : syracuseStep 3169459 = 4754189) B4754189
theorem B6675635 : Blo 1758080 6675635 := bstep (se 1 (by rfl) ⟨5006726, by rfl⟩ : syracuseStep 6675635 = 10013453) B10013453
theorem B5938379 : Blo 1758080 5938379 := bstep (se 1 (by rfl) ⟨4453784, by rfl⟩ : syracuseStep 5938379 = 8907569) B8907569
theorem B19029293 : Blo 1758080 19029293 := bstep (se 3 (by rfl) ⟨3567992, by rfl⟩ : syracuseStep 19029293 = 7135985) B7135985
theorem B2637131 : Blo 1758080 2637131 := bstep (se 1 (by rfl) ⟨1977848, by rfl⟩ : syracuseStep 2637131 = 3955697) B3955697
theorem B2637143 : Blo 1758080 2637143 := bstep (se 1 (by rfl) ⟨1977857, by rfl⟩ : syracuseStep 2637143 = 3955715) B3955715
theorem B3956057 : Blo 1758080 3956057 := bstep (se 2 (by rfl) ⟨1483521, by rfl⟩ : syracuseStep 3956057 = 2967043) B2967043
theorem B2637209 : Blo 1758080 2637209 := bstep (se 2 (by rfl) ⟨988953, by rfl⟩ : syracuseStep 2637209 = 1977907) B1977907
theorem B3956147 : Blo 1758080 3956147 := bstep (se 1 (by rfl) ⟨2967110, by rfl⟩ : syracuseStep 3956147 = 5934221) B5934221
theorem B3956183 : Blo 1758080 3956183 := bstep (se 1 (by rfl) ⟨2967137, by rfl⟩ : syracuseStep 3956183 = 5934275) B5934275
theorem B3808729 : Blo 1758080 3808729 := bstep (se 2 (by rfl) ⟨1428273, by rfl⟩ : syracuseStep 3808729 = 2856547) B2856547
theorem B5938649 : Blo 1758080 5938649 := bstep (se 2 (by rfl) ⟨2226993, by rfl⟩ : syracuseStep 5938649 = 4453987) B4453987
theorem B4013555 : Blo 1758080 4013555 := bstep (se 1 (by rfl) ⟨3010166, by rfl⟩ : syracuseStep 4013555 = 6020333) B6020333
theorem B2637323 : Blo 1758080 2637323 := bstep (se 1 (by rfl) ⟨1977992, by rfl⟩ : syracuseStep 2637323 = 3955985) B3955985
theorem B2637335 : Blo 1758080 2637335 := bstep (se 1 (by rfl) ⟨1978001, by rfl⟩ : syracuseStep 2637335 = 3956003) B3956003
theorem B2637401 : Blo 1758080 2637401 := bstep (se 2 (by rfl) ⟨989025, by rfl⟩ : syracuseStep 2637401 = 1978051) B1978051
theorem B3956363 : Blo 1758080 3956363 := bstep (se 1 (by rfl) ⟨2967272, by rfl⟩ : syracuseStep 3956363 = 5934545) B5934545
theorem B3956417 : Blo 1758080 3956417 := bstep (se 2 (by rfl) ⟨1483656, by rfl⟩ : syracuseStep 3956417 = 2967313) B2967313
theorem B2637515 : Blo 1758080 2637515 := bstep (se 1 (by rfl) ⟨1978136, by rfl⟩ : syracuseStep 2637515 = 3956273) B3956273
theorem B2637527 : Blo 1758080 2637527 := bstep (se 1 (by rfl) ⟨1978145, by rfl⟩ : syracuseStep 2637527 = 3956291) B3956291
theorem B2637593 : Blo 1758080 2637593 := bstep (se 2 (by rfl) ⟨989097, by rfl⟩ : syracuseStep 2637593 = 1978195) B1978195
theorem B6676289 : Blo 1758080 6676289 := bstep (se 2 (by rfl) ⟨2503608, by rfl⟩ : syracuseStep 6676289 = 5007217) B5007217
theorem B3170137 : Blo 1758080 3170137 := bstep (se 2 (by rfl) ⟨1188801, by rfl⟩ : syracuseStep 3170137 = 2377603) B2377603
theorem B2637707 : Blo 1758080 2637707 := bstep (se 1 (by rfl) ⟨1978280, by rfl⟩ : syracuseStep 2637707 = 3956561) B3956561
theorem B2637719 : Blo 1758080 2637719 := bstep (se 1 (by rfl) ⟨1978289, by rfl⟩ : syracuseStep 2637719 = 3956579) B3956579
theorem B4013975 : Blo 1758080 4013975 := bstep (se 1 (by rfl) ⟨3010481, by rfl⟩ : syracuseStep 4013975 = 6020963) B6020963
theorem B3956633 : Blo 1758080 3956633 := bstep (se 2 (by rfl) ⟨1483737, by rfl⟩ : syracuseStep 3956633 = 2967475) B2967475
theorem B5078963 : Blo 1758080 5078963 := bstep (se 1 (by rfl) ⟨3809222, by rfl⟩ : syracuseStep 5078963 = 7618445) B7618445
theorem B2817995 : Blo 1758080 2817995 := bstep (se 1 (by rfl) ⟨2113496, by rfl⟩ : syracuseStep 2817995 = 4226993) B4226993
theorem B5078987 : Blo 1758080 5078987 := bstep (se 1 (by rfl) ⟨3809240, by rfl⟩ : syracuseStep 5078987 = 7618481) B7618481
theorem B2637785 : Blo 1758080 2637785 := bstep (se 2 (by rfl) ⟨989169, by rfl⟩ : syracuseStep 2637785 = 1978339) B1978339
theorem B3956723 : Blo 1758080 3956723 := bstep (se 1 (by rfl) ⟨2967542, by rfl⟩ : syracuseStep 3956723 = 5935085) B5935085
theorem B6340619 : Blo 1758080 6340619 := bstep (se 1 (by rfl) ⟨4755464, by rfl⟩ : syracuseStep 6340619 = 9510929) B9510929
theorem B2637839 : Blo 1758080 2637839 := bstep (se 1 (by rfl) ⟨1978379, by rfl⟩ : syracuseStep 2637839 = 3956759) B3956759
theorem B22536215 : Blo 1758080 22536215 := bstep (se 1 (by rfl) ⟨16902161, by rfl⟩ : syracuseStep 22536215 = 33804323) B33804323
theorem B5939243 : Blo 1758080 5939243 := bstep (se 1 (by rfl) ⟨4454432, by rfl⟩ : syracuseStep 5939243 = 8908865) B8908865
theorem B2637881 : Blo 1758080 2637881 := bstep (se 2 (by rfl) ⟨989205, by rfl⟩ : syracuseStep 2637881 = 1978411) B1978411
theorem B3956795 : Blo 1758080 3956795 := bstep (se 1 (by rfl) ⟨2967596, by rfl⟩ : syracuseStep 3956795 = 5935193) B5935193
theorem B16056407 : Blo 1758080 16056407 := bstep (se 1 (by rfl) ⟨12042305, by rfl⟩ : syracuseStep 16056407 = 24084611) B24084611
theorem B2637959 : Blo 1758080 2637959 := bstep (se 1 (by rfl) ⟨1978469, by rfl⟩ : syracuseStep 2637959 = 3956939) B3956939
theorem B2637995 : Blo 1758080 2637995 := bstep (se 1 (by rfl) ⟨1978496, by rfl⟩ : syracuseStep 2637995 = 3956993) B3956993
theorem B3956921 : Blo 1758080 3956921 := bstep (se 2 (by rfl) ⟨1483845, by rfl⟩ : syracuseStep 3956921 = 2967691) B2967691
theorem B2638025 : Blo 1758080 2638025 := bstep (se 2 (by rfl) ⟨989259, by rfl⟩ : syracuseStep 2638025 = 1978519) B1978519
theorem B4227329 : Blo 1758080 4227329 := bstep (se 2 (by rfl) ⟨1585248, by rfl⟩ : syracuseStep 4227329 = 3170497) B3170497
theorem B2638139 : Blo 1758080 2638139 := bstep (se 1 (by rfl) ⟨1978604, by rfl⟩ : syracuseStep 2638139 = 3957209) B3957209
theorem B2638199 : Blo 1758080 2638199 := bstep (se 1 (by rfl) ⟨1978649, by rfl⟩ : syracuseStep 2638199 = 3957299) B3957299
theorem B2638223 : Blo 1758080 2638223 := bstep (se 1 (by rfl) ⟨1978667, by rfl⟩ : syracuseStep 2638223 = 3957335) B3957335
theorem B2638265 : Blo 1758080 2638265 := bstep (se 2 (by rfl) ⟨989349, by rfl⟩ : syracuseStep 2638265 = 1978699) B1978699
theorem B2638343 : Blo 1758080 2638343 := bstep (se 1 (by rfl) ⟨1978757, by rfl⟩ : syracuseStep 2638343 = 3957515) B3957515
theorem B3957263 : Blo 1758080 3957263 := bstep (se 1 (by rfl) ⟨2967947, by rfl⟩ : syracuseStep 3957263 = 5935895) B5935895
theorem B3957281 : Blo 1758080 3957281 := bstep (se 2 (by rfl) ⟨1483980, by rfl⟩ : syracuseStep 3957281 = 2967961) B2967961
theorem B2638379 : Blo 1758080 2638379 := bstep (se 1 (by rfl) ⟨1978784, by rfl⟩ : syracuseStep 2638379 = 3957569) B3957569
theorem B2638409 : Blo 1758080 2638409 := bstep (se 2 (by rfl) ⟨989403, by rfl⟩ : syracuseStep 2638409 = 1978807) B1978807
theorem B2638523 : Blo 1758080 2638523 := bstep (se 1 (by rfl) ⟨1978892, by rfl⟩ : syracuseStep 2638523 = 3957785) B3957785
theorem B45695681 : Blo 1758080 45695681 := bstep (se 2 (by rfl) ⟨17135880, by rfl⟩ : syracuseStep 45695681 = 34271761) B34271761
theorem B7619273 : Blo 1758080 7619273 := bstep (se 2 (by rfl) ⟨2857227, by rfl⟩ : syracuseStep 7619273 = 5714455) B5714455
theorem B2638583 : Blo 1758080 2638583 := bstep (se 1 (by rfl) ⟨1978937, by rfl⟩ : syracuseStep 2638583 = 3957875) B3957875
theorem B2638607 : Blo 1758080 2638607 := bstep (se 1 (by rfl) ⟨1978955, by rfl⟩ : syracuseStep 2638607 = 3957911) B3957911
theorem B2638649 : Blo 1758080 2638649 := bstep (se 2 (by rfl) ⟨989493, by rfl⟩ : syracuseStep 2638649 = 1978987) B1978987
theorem B3957623 : Blo 1758080 3957623 := bstep (se 1 (by rfl) ⟨2968217, by rfl⟩ : syracuseStep 3957623 = 5936435) B5936435
theorem B2638727 : Blo 1758080 2638727 := bstep (se 1 (by rfl) ⟨1979045, by rfl⟩ : syracuseStep 2638727 = 3958091) B3958091
theorem B8905625 : Blo 1758080 8905625 := bstep (se 2 (by rfl) ⟨3339609, by rfl⟩ : syracuseStep 8905625 = 6679219) B6679219
theorem B12231577 : Blo 1758080 12231577 := bstep (se 2 (by rfl) ⟨4586841, by rfl⟩ : syracuseStep 12231577 = 9173683) B9173683
theorem B13362083 : Blo 1758080 13362083 := bstep (se 1 (by rfl) ⟨10021562, by rfl⟩ : syracuseStep 13362083 = 20043125) B20043125
theorem B2638763 : Blo 1758080 2638763 := bstep (se 1 (by rfl) ⟨1979072, by rfl⟩ : syracuseStep 2638763 = 3958145) B3958145
theorem B2638793 : Blo 1758080 2638793 := bstep (se 2 (by rfl) ⟨989547, by rfl⟩ : syracuseStep 2638793 = 1979095) B1979095
theorem B3957803 : Blo 1758080 3957803 := bstep (se 1 (by rfl) ⟨2968352, by rfl⟩ : syracuseStep 3957803 = 5936705) B5936705
theorem B2638907 : Blo 1758080 2638907 := bstep (se 1 (by rfl) ⟨1979180, by rfl⟩ : syracuseStep 2638907 = 3958361) B3958361
theorem B2638967 : Blo 1758080 2638967 := bstep (se 1 (by rfl) ⟨1979225, by rfl⟩ : syracuseStep 2638967 = 3958451) B3958451
theorem B2638991 : Blo 1758080 2638991 := bstep (se 1 (by rfl) ⟨1979243, by rfl⟩ : syracuseStep 2638991 = 3958487) B3958487
theorem B2639033 : Blo 1758080 2639033 := bstep (se 2 (by rfl) ⟨989637, by rfl⟩ : syracuseStep 2639033 = 1979275) B1979275
theorem B11273417 : Blo 1758080 11273417 := bstep (se 2 (by rfl) ⟨4227531, by rfl⟩ : syracuseStep 11273417 = 8455063) B8455063
theorem B6767873 : Blo 1758080 6767873 := bstep (se 2 (by rfl) ⟨2537952, by rfl⟩ : syracuseStep 6767873 = 5075905) B5075905
theorem B6677761 : Blo 1758080 6677761 := bstep (se 2 (by rfl) ⟨2504160, by rfl⟩ : syracuseStep 6677761 = 5008321) B5008321
theorem B2639111 : Blo 1758080 2639111 := bstep (se 1 (by rfl) ⟨1979333, by rfl⟩ : syracuseStep 2639111 = 3958667) B3958667
theorem B2966827 : Blo 1758080 2966827 := bstep (se 1 (by rfl) ⟨2225120, by rfl⟩ : syracuseStep 2966827 = 4450241) B4450241
theorem B4883755 : Blo 1758080 4883755 := bstep (se 1 (by rfl) ⟨3662816, by rfl⟩ : syracuseStep 4883755 = 7325633) B7325633
theorem B2639147 : Blo 1758080 2639147 := bstep (se 1 (by rfl) ⟨1979360, by rfl⟩ : syracuseStep 2639147 = 3958721) B3958721
theorem B2639177 : Blo 1758080 2639177 := bstep (se 2 (by rfl) ⟨989691, by rfl⟩ : syracuseStep 2639177 = 1979383) B1979383
theorem B3958163 : Blo 1758080 3958163 := bstep (se 1 (by rfl) ⟨2968622, by rfl⟩ : syracuseStep 3958163 = 5937245) B5937245
theorem B2966969 : Blo 1758080 2966969 := bstep (se 2 (by rfl) ⟨1112613, by rfl⟩ : syracuseStep 2966969 = 2225227) B2225227
theorem B2639291 : Blo 1758080 2639291 := bstep (se 1 (by rfl) ⟨1979468, by rfl⟩ : syracuseStep 2639291 = 3958937) B3958937
theorem B3958217 : Blo 1758080 3958217 := bstep (se 2 (by rfl) ⟨1484331, by rfl⟩ : syracuseStep 3958217 = 2968663) B2968663
theorem B33433037 : Blo 1758080 33433037 := bstep (se 3 (by rfl) ⟨6268694, by rfl⟩ : syracuseStep 33433037 = 12537389) B12537389
theorem B28526033 : Blo 1758080 28526033 := bstep (se 2 (by rfl) ⟨10697262, by rfl⟩ : syracuseStep 28526033 = 21394525) B21394525
theorem B2639351 : Blo 1758080 2639351 := bstep (se 1 (by rfl) ⟨1979513, by rfl⟩ : syracuseStep 2639351 = 3959027) B3959027
theorem B5006863 : Blo 1758080 5006863 := bstep (se 1 (by rfl) ⟨3755147, by rfl⟩ : syracuseStep 5006863 = 7510295) B7510295
theorem B2639375 : Blo 1758080 2639375 := bstep (se 1 (by rfl) ⟨1979531, by rfl⟩ : syracuseStep 2639375 = 3959063) B3959063
theorem B2639417 : Blo 1758080 2639417 := bstep (se 2 (by rfl) ⟨989781, by rfl⟩ : syracuseStep 2639417 = 1979563) B1979563
theorem B4752955 : Blo 1758080 4752955 := bstep (se 1 (by rfl) ⟨3564716, by rfl⟩ : syracuseStep 4752955 = 7129433) B7129433
theorem B5006909 : Blo 1758080 5006909 := bstep (se 3 (by rfl) ⟨938795, by rfl⟩ : syracuseStep 5006909 = 1877591) B1877591
theorem B15025783 : Blo 1758080 15025783 := bstep (se 1 (by rfl) ⟨11269337, by rfl⟩ : syracuseStep 15025783 = 22538675) B22538675
theorem B2639495 : Blo 1758080 2639495 := bstep (se 1 (by rfl) ⟨1979621, by rfl⟩ : syracuseStep 2639495 = 3959243) B3959243
theorem B4753043 : Blo 1758080 4753043 := bstep (se 1 (by rfl) ⟨3564782, by rfl⟩ : syracuseStep 4753043 = 7129565) B7129565
theorem B4286099 : Blo 1758080 4286099 := bstep (se 1 (by rfl) ⟨3214574, by rfl⟩ : syracuseStep 4286099 = 6429149) B6429149
theorem B2639531 : Blo 1758080 2639531 := bstep (se 1 (by rfl) ⟨1979648, by rfl⟩ : syracuseStep 2639531 = 3959297) B3959297
theorem B2639561 : Blo 1758080 2639561 := bstep (se 2 (by rfl) ⟨989835, by rfl⟩ : syracuseStep 2639561 = 1979671) B1979671
theorem B2639675 : Blo 1758080 2639675 := bstep (se 1 (by rfl) ⟨1979756, by rfl⟩ : syracuseStep 2639675 = 3959513) B3959513
theorem B2639735 : Blo 1758080 2639735 := bstep (se 1 (by rfl) ⟨1979801, by rfl⟩ : syracuseStep 2639735 = 3959603) B3959603
theorem B10020743 : Blo 1758080 10020743 := bstep (se 1 (by rfl) ⟨7515557, by rfl⟩ : syracuseStep 10020743 = 15031115) B15031115
theorem B2639759 : Blo 1758080 2639759 := bstep (se 1 (by rfl) ⟨1979819, by rfl⟩ : syracuseStep 2639759 = 3959639) B3959639
theorem B5007251 : Blo 1758080 5007251 := bstep (se 1 (by rfl) ⟨3755438, by rfl⟩ : syracuseStep 5007251 = 7510877) B7510877
theorem B2639801 : Blo 1758080 2639801 := bstep (se 2 (by rfl) ⟨989925, by rfl⟩ : syracuseStep 2639801 = 1979851) B1979851
theorem B2639879 : Blo 1758080 2639879 := bstep (se 1 (by rfl) ⟨1979909, by rfl⟩ : syracuseStep 2639879 = 3959819) B3959819
theorem B2639915 : Blo 1758080 2639915 := bstep (se 1 (by rfl) ⟨1979936, by rfl⟩ : syracuseStep 2639915 = 3959873) B3959873
theorem B2639945 : Blo 1758080 2639945 := bstep (se 2 (by rfl) ⟨989979, by rfl⟩ : syracuseStep 2639945 = 1979959) B1979959
theorem B4450423 : Blo 1758080 4450423 := bstep (se 1 (by rfl) ⟨3337817, by rfl⟩ : syracuseStep 4450423 = 6675635) B6675635
theorem B2967671 : Blo 1758080 2967671 := bstep (se 1 (by rfl) ⟨2225753, by rfl⟩ : syracuseStep 2967671 = 4451507) B4451507
theorem B3958919 : Blo 1758080 3958919 := bstep (se 1 (by rfl) ⟨2969189, by rfl⟩ : syracuseStep 3958919 = 5938379) B5938379
theorem B4753561 : Blo 1758080 4753561 := bstep (se 2 (by rfl) ⟨1782585, by rfl⟩ : syracuseStep 4753561 = 3565171) B3565171
theorem B2640059 : Blo 1758080 2640059 := bstep (se 1 (by rfl) ⟨1980044, by rfl⟩ : syracuseStep 2640059 = 3960089) B3960089
theorem B2640119 : Blo 1758080 2640119 := bstep (se 1 (by rfl) ⟨1980089, by rfl⟩ : syracuseStep 2640119 = 3960179) B3960179
theorem B3959099 : Blo 1758080 3959099 := bstep (se 1 (by rfl) ⟨2969324, by rfl⟩ : syracuseStep 3959099 = 5938649) B5938649
theorem B3959225 : Blo 1758080 3959225 := bstep (se 2 (by rfl) ⟨1484709, by rfl⟩ : syracuseStep 3959225 = 2969419) B2969419
theorem B7514653 : Blo 1758080 7514653 := bstep (se 3 (by rfl) ⟨1408997, by rfl⟩ : syracuseStep 7514653 = 2817995) B2817995
theorem B4450859 : Blo 1758080 4450859 := bstep (se 1 (by rfl) ⟨3338144, by rfl⟩ : syracuseStep 4450859 = 6676289) B6676289
theorem B2968123 : Blo 1758080 2968123 := bstep (se 1 (by rfl) ⟨2226092, by rfl⟩ : syracuseStep 2968123 = 4452185) B4452185
theorem B3385975 : Blo 1758080 3385975 := bstep (se 1 (by rfl) ⟨2539481, by rfl⟩ : syracuseStep 3385975 = 5078963) B5078963
theorem B3385991 : Blo 1758080 3385991 := bstep (se 1 (by rfl) ⟨2539493, by rfl⟩ : syracuseStep 3385991 = 5078987) B5078987
theorem B2968265 : Blo 1758080 2968265 := bstep (se 2 (by rfl) ⟨1113099, by rfl⟩ : syracuseStep 2968265 = 2226199) B2226199
theorem B42814169 : Blo 1758080 42814169 := bstep (se 2 (by rfl) ⟨16055313, by rfl⟩ : syracuseStep 42814169 = 32110627) B32110627
theorem B10693349 : Blo 1758080 10693349 := bstep (se 4 (by rfl) ⟨1002501, by rfl⟩ : syracuseStep 10693349 = 2005003) B2005003
theorem B5008139 : Blo 1758080 5008139 := bstep (se 1 (by rfl) ⟨3756104, by rfl⟩ : syracuseStep 5008139 = 7512209) B7512209
theorem B3959567 : Blo 1758080 3959567 := bstep (se 1 (by rfl) ⟨2969675, by rfl⟩ : syracuseStep 3959567 = 5939351) B5939351
theorem B3959585 : Blo 1758080 3959585 := bstep (se 2 (by rfl) ⟨1484844, by rfl⟩ : syracuseStep 3959585 = 2969689) B2969689
theorem B2378683 : Blo 1758080 2378683 := bstep (se 1 (by rfl) ⟨1784012, by rfl⟩ : syracuseStep 2378683 = 3568025) B3568025
theorem B12684235 : Blo 1758080 12684235 := bstep (se 1 (by rfl) ⟨9513176, by rfl⟩ : syracuseStep 12684235 = 19026353) B19026353
theorem B5934167 : Blo 1758080 5934167 := bstep (se 1 (by rfl) ⟨4450625, by rfl⟩ : syracuseStep 5934167 = 8901251) B8901251
theorem B3959927 : Blo 1758080 3959927 := bstep (se 1 (by rfl) ⟨2969945, by rfl⟩ : syracuseStep 3959927 = 5939891) B5939891
theorem B13364513 : Blo 1758080 13364513 := bstep (se 2 (by rfl) ⟨5011692, by rfl⟩ : syracuseStep 13364513 = 10023385) B10023385
theorem B3566891 : Blo 1758080 3566891 := bstep (se 1 (by rfl) ⟨2675168, by rfl⟩ : syracuseStep 3566891 = 5350337) B5350337
theorem B3960107 : Blo 1758080 3960107 := bstep (se 1 (by rfl) ⟨2970080, by rfl⟩ : syracuseStep 3960107 = 5940161) B5940161
theorem B4451699 : Blo 1758080 4451699 := bstep (se 1 (by rfl) ⟨3338774, by rfl⟩ : syracuseStep 4451699 = 6677549) B6677549
theorem B4451719 : Blo 1758080 4451719 := bstep (se 1 (by rfl) ⟨3338789, by rfl⟩ : syracuseStep 4451719 = 6677579) B6677579
theorem B2968967 : Blo 1758080 2968967 := bstep (se 1 (by rfl) ⟨2226725, by rfl⟩ : syracuseStep 2968967 = 4453451) B4453451
theorem B10014137 : Blo 1758080 10014137 := bstep (se 2 (by rfl) ⟨3755301, by rfl⟩ : syracuseStep 10014137 = 7510603) B7510603
theorem B8908217 : Blo 1758080 8908217 := bstep (se 2 (by rfl) ⟨3340581, by rfl⟩ : syracuseStep 8908217 = 6681163) B6681163
theorem B4754945 : Blo 1758080 4754945 := bstep (se 2 (by rfl) ⟨1783104, by rfl⟩ : syracuseStep 4754945 = 3566209) B3566209
theorem B1977871 : Blo 1758080 1977871 := bstep (se 1 (by rfl) ⟨1483403, by rfl⟩ : syracuseStep 1977871 = 2966807) B2966807
theorem B3337787 : Blo 1758080 3337787 := bstep (se 1 (by rfl) ⟨2503340, by rfl⟩ : syracuseStep 3337787 = 5006681) B5006681
theorem B5934653 : Blo 1758080 5934653 := bstep (se 3 (by rfl) ⟨1112747, by rfl⟩ : syracuseStep 5934653 = 2225495) B2225495
theorem B4451993 : Blo 1758080 4451993 := bstep (se 2 (by rfl) ⟨1669497, by rfl⟩ : syracuseStep 4451993 = 3338995) B3338995
theorem B13356737 : Blo 1758080 13356737 := bstep (se 2 (by rfl) ⟨5008776, by rfl⟩ : syracuseStep 13356737 = 10017553) B10017553
theorem B7130861 : Blo 1758080 7130861 := bstep (se 3 (by rfl) ⟨1337036, by rfl⟩ : syracuseStep 7130861 = 2674073) B2674073
theorem B13545253 : Blo 1758080 13545253 := bstep (se 4 (by rfl) ⟨1269867, by rfl⟩ : syracuseStep 13545253 = 2539735) B2539735
theorem B4452155 : Blo 1758080 4452155 := bstep (se 1 (by rfl) ⟨3339116, by rfl⟩ : syracuseStep 4452155 = 6678233) B6678233
theorem B2674505 : Blo 1758080 2674505 := bstep (se 2 (by rfl) ⟨1002939, by rfl⟩ : syracuseStep 2674505 = 2005879) B2005879
theorem B8900441 : Blo 1758080 8900441 := bstep (se 2 (by rfl) ⟨3337665, by rfl⟩ : syracuseStep 8900441 = 6675331) B6675331
theorem B10702813 : Blo 1758080 10702813 := bstep (se 3 (by rfl) ⟨2006777, by rfl⟩ : syracuseStep 10702813 = 4013555) B4013555
theorem B1978375 : Blo 1758080 1978375 := bstep (se 1 (by rfl) ⟨1483781, by rfl⟩ : syracuseStep 1978375 = 2967563) B2967563
theorem B4452367 : Blo 1758080 4452367 := bstep (se 1 (by rfl) ⟨3339275, by rfl⟩ : syracuseStep 4452367 = 6678551) B6678551
theorem B2969615 : Blo 1758080 2969615 := bstep (se 1 (by rfl) ⟨2227211, by rfl⟩ : syracuseStep 2969615 = 4454423) B4454423
theorem B3338273 : Blo 1758080 3338273 := bstep (se 2 (by rfl) ⟨1251852, by rfl⟩ : syracuseStep 3338273 = 2503705) B2503705
theorem B6680663 : Blo 1758080 6680663 := bstep (se 1 (by rfl) ⟨5010497, by rfl⟩ : syracuseStep 6680663 = 10020995) B10020995
theorem B3338425 : Blo 1758080 3338425 := bstep (se 2 (by rfl) ⟨1251909, by rfl⟩ : syracuseStep 3338425 = 2503819) B2503819
theorem B1978555 : Blo 1758080 1978555 := bstep (se 1 (by rfl) ⟨1483916, by rfl⟩ : syracuseStep 1978555 = 2967833) B2967833
theorem B3756233 : Blo 1758080 3756233 := bstep (se 2 (by rfl) ⟨1408587, by rfl⟩ : syracuseStep 3756233 = 2817175) B2817175
theorem B13365485 : Blo 1758080 13365485 := bstep (se 3 (by rfl) ⟨2506028, by rfl⟩ : syracuseStep 13365485 = 5012057) B5012057
theorem B4452641 : Blo 1758080 4452641 := bstep (se 2 (by rfl) ⟨1669740, by rfl⟩ : syracuseStep 4452641 = 3339481) B3339481
theorem B9146675 : Blo 1758080 9146675 := bstep (se 1 (by rfl) ⟨6860006, by rfl⟩ : syracuseStep 9146675 = 13720013) B13720013
theorem B5009779 : Blo 1758080 5009779 := bstep (se 1 (by rfl) ⟨3757334, by rfl⟩ : syracuseStep 5009779 = 7514669) B7514669
theorem B8450507 : Blo 1758080 8450507 := bstep (se 1 (by rfl) ⟨6337880, by rfl⟩ : syracuseStep 8450507 = 12675761) B12675761
theorem B6681149 : Blo 1758080 6681149 := bstep (se 3 (by rfl) ⟨1252715, by rfl⟩ : syracuseStep 6681149 = 2505431) B2505431
theorem B5010007 : Blo 1758080 5010007 := bstep (se 1 (by rfl) ⟨3757505, by rfl⟩ : syracuseStep 5010007 = 7515011) B7515011
theorem B1979023 : Blo 1758080 1979023 := bstep (se 1 (by rfl) ⟨1484267, by rfl⟩ : syracuseStep 1979023 = 2968535) B2968535
theorem B8024777 : Blo 1758080 8024777 := bstep (se 2 (by rfl) ⟨3009291, by rfl⟩ : syracuseStep 8024777 = 6018583) B6018583
theorem B8909513 : Blo 1758080 8909513 := bstep (se 2 (by rfl) ⟨3341067, by rfl⟩ : syracuseStep 8909513 = 6682135) B6682135
theorem B9507557 : Blo 1758080 9507557 := bstep (se 4 (by rfl) ⟨891333, by rfl⟩ : syracuseStep 9507557 = 1782667) B1782667
theorem B22549337 : Blo 1758080 22549337 := bstep (se 2 (by rfl) ⟨8456001, by rfl⟩ : syracuseStep 22549337 = 16912003) B16912003
theorem B12686195 : Blo 1758080 12686195 := bstep (se 1 (by rfl) ⟨9514646, by rfl⟩ : syracuseStep 12686195 = 19029293) B19029293
theorem B1758087 : Blo 1758080 1758087 := bstep (se 1 (by rfl) ⟨1318565, by rfl⟩ : syracuseStep 1758087 = 2637131) B2637131
theorem B1758095 : Blo 1758080 1758095 := bstep (se 1 (by rfl) ⟨1318571, by rfl⟩ : syracuseStep 1758095 = 2637143) B2637143
theorem B5632915 : Blo 1758080 5632915 := bstep (se 1 (by rfl) ⟨4224686, by rfl⟩ : syracuseStep 5632915 = 8449373) B8449373
theorem B5936057 : Blo 1758080 5936057 := bstep (se 2 (by rfl) ⟨2226021, by rfl⟩ : syracuseStep 5936057 = 4452043) B4452043
theorem B1758139 : Blo 1758080 1758139 := bstep (se 1 (by rfl) ⟨1318604, by rfl⟩ : syracuseStep 1758139 = 2637209) B2637209
theorem B1758215 : Blo 1758080 1758215 := bstep (se 1 (by rfl) ⟨1318661, by rfl⟩ : syracuseStep 1758215 = 2637323) B2637323
theorem B1758223 : Blo 1758080 1758223 := bstep (se 1 (by rfl) ⟨1318667, by rfl⟩ : syracuseStep 1758223 = 2637335) B2637335
theorem B1758267 : Blo 1758080 1758267 := bstep (se 1 (by rfl) ⟨1318700, by rfl⟩ : syracuseStep 1758267 = 2637401) B2637401
theorem B1758343 : Blo 1758080 1758343 := bstep (se 1 (by rfl) ⟨1318757, by rfl⟩ : syracuseStep 1758343 = 2637515) B2637515
theorem B1979527 : Blo 1758080 1979527 := bstep (se 1 (by rfl) ⟨1484645, by rfl⟩ : syracuseStep 1979527 = 2969291) B2969291
theorem B1758351 : Blo 1758080 1758351 := bstep (se 1 (by rfl) ⟨1318763, by rfl⟩ : syracuseStep 1758351 = 2637527) B2637527
theorem B2225323 : Blo 1758080 2225323 := bstep (se 1 (by rfl) ⟨1668992, by rfl⟩ : syracuseStep 2225323 = 3337985) B3337985
theorem B1758395 : Blo 1758080 1758395 := bstep (se 1 (by rfl) ⟨1318796, by rfl⟩ : syracuseStep 1758395 = 2637593) B2637593
theorem B1758471 : Blo 1758080 1758471 := bstep (se 1 (by rfl) ⟨1318853, by rfl⟩ : syracuseStep 1758471 = 2637707) B2637707
theorem B4453643 : Blo 1758080 4453643 := bstep (se 1 (by rfl) ⟨3340232, by rfl⟩ : syracuseStep 4453643 = 6680465) B6680465
theorem B1758479 : Blo 1758080 1758479 := bstep (se 1 (by rfl) ⟨1318859, by rfl⟩ : syracuseStep 1758479 = 2637719) B2637719
theorem B2675983 : Blo 1758080 2675983 := bstep (se 1 (by rfl) ⟨2006987, by rfl⟩ : syracuseStep 2675983 = 4013975) B4013975
theorem B1758523 : Blo 1758080 1758523 := bstep (se 1 (by rfl) ⟨1318892, by rfl⟩ : syracuseStep 1758523 = 2637785) B2637785
theorem B5076283 : Blo 1758080 5076283 := bstep (se 1 (by rfl) ⟨3807212, by rfl⟩ : syracuseStep 5076283 = 7614425) B7614425
theorem B1979707 : Blo 1758080 1979707 := bstep (se 1 (by rfl) ⟨1484780, by rfl⟩ : syracuseStep 1979707 = 2969561) B2969561
theorem B1758599 : Blo 1758080 1758599 := bstep (se 1 (by rfl) ⟨1318949, by rfl⟩ : syracuseStep 1758599 = 2637899) B2637899
theorem B2225551 : Blo 1758080 2225551 := bstep (se 1 (by rfl) ⟨1669163, by rfl⟩ : syracuseStep 2225551 = 3338327) B3338327
theorem B1758607 : Blo 1758080 1758607 := bstep (se 1 (by rfl) ⟨1318955, by rfl⟩ : syracuseStep 1758607 = 2637911) B2637911
theorem B41178545 : Blo 1758080 41178545 := bstep (se 2 (by rfl) ⟨15441954, by rfl⟩ : syracuseStep 41178545 = 30883909) B30883909
theorem B1758651 : Blo 1758080 1758651 := bstep (se 1 (by rfl) ⟨1318988, by rfl⟩ : syracuseStep 1758651 = 2637977) B2637977
theorem B1758727 : Blo 1758080 1758727 := bstep (se 1 (by rfl) ⟨1319045, by rfl⟩ : syracuseStep 1758727 = 2638091) B2638091
theorem B5936651 : Blo 1758080 5936651 := bstep (se 1 (by rfl) ⟨4452488, by rfl⟩ : syracuseStep 5936651 = 8904977) B8904977
theorem B1758735 : Blo 1758080 1758735 := bstep (se 1 (by rfl) ⟨1319051, by rfl⟩ : syracuseStep 1758735 = 2638103) B2638103
theorem B4757021 : Blo 1758080 4757021 := bstep (se 3 (by rfl) ⟨891941, by rfl⟩ : syracuseStep 4757021 = 1783883) B1783883
theorem B16258603 : Blo 1758080 16258603 := bstep (se 1 (by rfl) ⟨12193952, by rfl⟩ : syracuseStep 16258603 = 24387905) B24387905
theorem B14267947 : Blo 1758080 14267947 := bstep (se 1 (by rfl) ⟨10700960, by rfl⟩ : syracuseStep 14267947 = 21401921) B21401921
theorem B1758779 : Blo 1758080 1758779 := bstep (se 1 (by rfl) ⟨1319084, by rfl⟩ : syracuseStep 1758779 = 2638169) B2638169
theorem B5346931 : Blo 1758080 5346931 := bstep (se 1 (by rfl) ⟨4010198, by rfl⟩ : syracuseStep 5346931 = 8020397) B8020397
theorem B5936759 : Blo 1758080 5936759 := bstep (se 1 (by rfl) ⟨4452569, by rfl⟩ : syracuseStep 5936759 = 8905139) B8905139
theorem B1758855 : Blo 1758080 1758855 := bstep (se 1 (by rfl) ⟨1319141, by rfl⟩ : syracuseStep 1758855 = 2638283) B2638283
theorem B1758863 : Blo 1758080 1758863 := bstep (se 1 (by rfl) ⟨1319147, by rfl⟩ : syracuseStep 1758863 = 2638295) B2638295
theorem B3806867 : Blo 1758080 3806867 := bstep (se 1 (by rfl) ⟨2855150, by rfl⟩ : syracuseStep 3806867 = 5710301) B5710301
theorem B1758907 : Blo 1758080 1758907 := bstep (se 1 (by rfl) ⟨1319180, by rfl⟩ : syracuseStep 1758907 = 2638361) B2638361
theorem B1758983 : Blo 1758080 1758983 := bstep (se 1 (by rfl) ⟨1319237, by rfl⟩ : syracuseStep 1758983 = 2638475) B2638475
theorem B1758991 : Blo 1758080 1758991 := bstep (se 1 (by rfl) ⟨1319243, by rfl⟩ : syracuseStep 1758991 = 2638487) B2638487
theorem B1759035 : Blo 1758080 1759035 := bstep (se 1 (by rfl) ⟨1319276, by rfl⟩ : syracuseStep 1759035 = 2638553) B2638553
theorem B19019609 : Blo 1758080 19019609 := bstep (se 2 (by rfl) ⟨7132353, by rfl⟩ : syracuseStep 19019609 = 14264707) B14264707
theorem B10696583 : Blo 1758080 10696583 := bstep (se 1 (by rfl) ⟨8022437, by rfl⟩ : syracuseStep 10696583 = 16044875) B16044875
theorem B1759111 : Blo 1758080 1759111 := bstep (se 1 (by rfl) ⟨1319333, by rfl⟩ : syracuseStep 1759111 = 2638667) B2638667
theorem B1759119 : Blo 1758080 1759119 := bstep (se 1 (by rfl) ⟨1319339, by rfl⟩ : syracuseStep 1759119 = 2638679) B2638679
theorem B8902547 : Blo 1758080 8902547 := bstep (se 1 (by rfl) ⟨6676910, by rfl⟩ : syracuseStep 8902547 = 13353821) B13353821
theorem B4454291 : Blo 1758080 4454291 := bstep (se 1 (by rfl) ⟨3340718, by rfl⟩ : syracuseStep 4454291 = 6681437) B6681437
theorem B3340217 : Blo 1758080 3340217 := bstep (se 2 (by rfl) ⟨1252581, by rfl⟩ : syracuseStep 3340217 = 2505163) B2505163
theorem B1759163 : Blo 1758080 1759163 := bstep (se 1 (by rfl) ⟨1319372, by rfl⟩ : syracuseStep 1759163 = 2638745) B2638745
theorem B15235019 : Blo 1758080 15235019 := bstep (se 1 (by rfl) ⟨11426264, by rfl⟩ : syracuseStep 15235019 = 22852529) B22852529
theorem B1759239 : Blo 1758080 1759239 := bstep (se 1 (by rfl) ⟨1319429, by rfl⟩ : syracuseStep 1759239 = 2638859) B2638859
theorem B2504719 : Blo 1758080 2504719 := bstep (se 1 (by rfl) ⟨1878539, by rfl⟩ : syracuseStep 2504719 = 3757079) B3757079
theorem B1759247 : Blo 1758080 1759247 := bstep (se 1 (by rfl) ⟨1319435, by rfl⟩ : syracuseStep 1759247 = 2638871) B2638871
theorem B1759291 : Blo 1758080 1759291 := bstep (se 1 (by rfl) ⟨1319468, by rfl⟩ : syracuseStep 1759291 = 2638937) B2638937
theorem B1783867 : Blo 1758080 1783867 := bstep (se 1 (by rfl) ⟨1337900, by rfl⟩ : syracuseStep 1783867 = 2675801) B2675801
theorem B8026199 : Blo 1758080 8026199 := bstep (se 1 (by rfl) ⟨6019649, by rfl⟩ : syracuseStep 8026199 = 12039299) B12039299
theorem B2226295 : Blo 1758080 2226295 := bstep (se 1 (by rfl) ⟨1669721, by rfl⟩ : syracuseStep 2226295 = 3339443) B3339443
theorem B2504839 : Blo 1758080 2504839 := bstep (se 1 (by rfl) ⟨1878629, by rfl⟩ : syracuseStep 2504839 = 3757259) B3757259
theorem B1759367 : Blo 1758080 1759367 := bstep (se 1 (by rfl) ⟨1319525, by rfl⟩ : syracuseStep 1759367 = 2639051) B2639051
theorem B5011591 : Blo 1758080 5011591 := bstep (se 1 (by rfl) ⟨3758693, by rfl⟩ : syracuseStep 5011591 = 7517387) B7517387
theorem B1759375 : Blo 1758080 1759375 := bstep (se 1 (by rfl) ⟨1319531, by rfl⟩ : syracuseStep 1759375 = 2639063) B2639063
theorem B4454585 : Blo 1758080 4454585 := bstep (se 2 (by rfl) ⟨1670469, by rfl⟩ : syracuseStep 4454585 = 3340939) B3340939
theorem B1759419 : Blo 1758080 1759419 := bstep (se 1 (by rfl) ⟨1319564, by rfl⟩ : syracuseStep 1759419 = 2639129) B2639129
theorem B5937353 : Blo 1758080 5937353 := bstep (se 2 (by rfl) ⟨2226507, by rfl⟩ : syracuseStep 5937353 = 4453015) B4453015
theorem B1759495 : Blo 1758080 1759495 := bstep (se 1 (by rfl) ⟨1319621, by rfl⟩ : syracuseStep 1759495 = 2639243) B2639243
theorem B1759503 : Blo 1758080 1759503 := bstep (se 1 (by rfl) ⟨1319627, by rfl⟩ : syracuseStep 1759503 = 2639255) B2639255
theorem B1759547 : Blo 1758080 1759547 := bstep (se 1 (by rfl) ⟨1319660, by rfl⟩ : syracuseStep 1759547 = 2639321) B2639321
theorem B38558017 : Blo 1758080 38558017 := bstep (se 2 (by rfl) ⟨14459256, by rfl⟩ : syracuseStep 38558017 = 28918513) B28918513
theorem B1759623 : Blo 1758080 1759623 := bstep (se 1 (by rfl) ⟨1319717, by rfl⟩ : syracuseStep 1759623 = 2639435) B2639435
theorem B1759631 : Blo 1758080 1759631 := bstep (se 1 (by rfl) ⟨1319723, by rfl⟩ : syracuseStep 1759631 = 2639447) B2639447
theorem B8452505 : Blo 1758080 8452505 := bstep (se 2 (by rfl) ⟨3169689, by rfl⟩ : syracuseStep 8452505 = 6339379) B6339379
theorem B5011865 : Blo 1758080 5011865 := bstep (se 2 (by rfl) ⟨1879449, by rfl⟩ : syracuseStep 5011865 = 3758899) B3758899
theorem B2226619 : Blo 1758080 2226619 := bstep (se 1 (by rfl) ⟨1669964, by rfl⟩ : syracuseStep 2226619 = 3339929) B3339929
theorem B1759675 : Blo 1758080 1759675 := bstep (se 1 (by rfl) ⟨1319756, by rfl⟩ : syracuseStep 1759675 = 2639513) B2639513
theorem B1759751 : Blo 1758080 1759751 := bstep (se 1 (by rfl) ⟨1319813, by rfl⟩ : syracuseStep 1759751 = 2639627) B2639627
theorem B1759759 : Blo 1758080 1759759 := bstep (se 1 (by rfl) ⟨1319819, by rfl⟩ : syracuseStep 1759759 = 2639639) B2639639
theorem B1759803 : Blo 1758080 1759803 := bstep (se 1 (by rfl) ⟨1319852, by rfl⟩ : syracuseStep 1759803 = 2639705) B2639705
theorem B1759879 : Blo 1758080 1759879 := bstep (se 1 (by rfl) ⟨1319909, by rfl⟩ : syracuseStep 1759879 = 2639819) B2639819
theorem B1759887 : Blo 1758080 1759887 := bstep (se 1 (by rfl) ⟨1319915, by rfl⟩ : syracuseStep 1759887 = 2639831) B2639831
theorem B1759931 : Blo 1758080 1759931 := bstep (se 1 (by rfl) ⟨1319948, by rfl⟩ : syracuseStep 1759931 = 2639897) B2639897
theorem B1760007 : Blo 1758080 1760007 := bstep (se 1 (by rfl) ⟨1320005, by rfl⟩ : syracuseStep 1760007 = 2640011) B2640011
theorem B1760015 : Blo 1758080 1760015 := bstep (se 1 (by rfl) ⟨1320011, by rfl⟩ : syracuseStep 1760015 = 2640023) B2640023
theorem B1760059 : Blo 1758080 1760059 := bstep (se 1 (by rfl) ⟨1320044, by rfl⟩ : syracuseStep 1760059 = 2640089) B2640089
theorem B5938055 : Blo 1758080 5938055 := bstep (se 1 (by rfl) ⟨4453541, by rfl⟩ : syracuseStep 5938055 = 8907083) B8907083
theorem B16915351 : Blo 1758080 16915351 := bstep (se 1 (by rfl) ⟨12686513, by rfl⟩ : syracuseStep 16915351 = 25373027) B25373027
theorem B4225945 : Blo 1758080 4225945 := bstep (se 2 (by rfl) ⟨1584729, by rfl⟩ : syracuseStep 4225945 = 3169459) B3169459
theorem B2227115 : Blo 1758080 2227115 := bstep (se 1 (by rfl) ⟨1670336, by rfl⟩ : syracuseStep 2227115 = 3340673) B3340673
theorem B13360139 : Blo 1758080 13360139 := bstep (se 1 (by rfl) ⟨10020104, by rfl⟩ : syracuseStep 13360139 = 20040209) B20040209
theorem B3955859 : Blo 1758080 3955859 := bstep (se 1 (by rfl) ⟨2966894, by rfl⟩ : syracuseStep 3955859 = 5933789) B5933789
theorem B4226195 : Blo 1758080 4226195 := bstep (se 1 (by rfl) ⟨3169646, by rfl⟩ : syracuseStep 4226195 = 6339293) B6339293
theorem B3955913 : Blo 1758080 3955913 := bstep (se 2 (by rfl) ⟨1483467, by rfl⟩ : syracuseStep 3955913 = 2966935) B2966935
theorem B5938433 : Blo 1758080 5938433 := bstep (se 2 (by rfl) ⟨2226912, by rfl⟩ : syracuseStep 5938433 = 4453825) B4453825
theorem B15023393 : Blo 1758080 15023393 := bstep (se 2 (by rfl) ⟨5633772, by rfl⟩ : syracuseStep 15023393 = 11267545) B11267545
theorem B5078305 : Blo 1758080 5078305 := bstep (se 2 (by rfl) ⟨1904364, by rfl⟩ : syracuseStep 5078305 = 3808729) B3808729
theorem B2637191 : Blo 1758080 2637191 := bstep (se 1 (by rfl) ⟨1977893, by rfl⟩ : syracuseStep 2637191 = 3955787) B3955787
theorem B2227591 : Blo 1758080 2227591 := bstep (se 1 (by rfl) ⟨1670693, by rfl⟩ : syracuseStep 2227591 = 3341387) B3341387
theorem B2637227 : Blo 1758080 2637227 := bstep (se 1 (by rfl) ⟨1977920, by rfl⟩ : syracuseStep 2637227 = 3955841) B3955841
theorem B2637257 : Blo 1758080 2637257 := bstep (se 2 (by rfl) ⟨988971, by rfl⟩ : syracuseStep 2637257 = 1977943) B1977943
theorem B2637371 : Blo 1758080 2637371 := bstep (se 1 (by rfl) ⟨1978028, by rfl⟩ : syracuseStep 2637371 = 3956057) B3956057
theorem B6340157 : Blo 1758080 6340157 := bstep (se 3 (by rfl) ⟨1188779, by rfl⟩ : syracuseStep 6340157 = 2377559) B2377559
theorem B2637431 : Blo 1758080 2637431 := bstep (se 1 (by rfl) ⟨1978073, by rfl⟩ : syracuseStep 2637431 = 3956147) B3956147
theorem B2637455 : Blo 1758080 2637455 := bstep (se 1 (by rfl) ⟨1978091, by rfl⟩ : syracuseStep 2637455 = 3956183) B3956183
theorem B2637497 : Blo 1758080 2637497 := bstep (se 2 (by rfl) ⟨989061, by rfl⟩ : syracuseStep 2637497 = 1978123) B1978123
theorem B2637575 : Blo 1758080 2637575 := bstep (se 1 (by rfl) ⟨1978181, by rfl⟩ : syracuseStep 2637575 = 3956363) B3956363
theorem B4226849 : Blo 1758080 4226849 := bstep (se 2 (by rfl) ⟨1585068, by rfl⟩ : syracuseStep 4226849 = 3170137) B3170137
theorem B2637611 : Blo 1758080 2637611 := bstep (se 1 (by rfl) ⟨1978208, by rfl⟩ : syracuseStep 2637611 = 3956417) B3956417
theorem B2637641 : Blo 1758080 2637641 := bstep (se 2 (by rfl) ⟨989115, by rfl⟩ : syracuseStep 2637641 = 1978231) B1978231
theorem B3956615 : Blo 1758080 3956615 := bstep (se 1 (by rfl) ⟨2967461, by rfl⟩ : syracuseStep 3956615 = 5934923) B5934923
theorem B12672931 : Blo 1758080 12672931 := bstep (se 1 (by rfl) ⟨9504698, by rfl⟩ : syracuseStep 12672931 = 19009397) B19009397
theorem B2637755 : Blo 1758080 2637755 := bstep (se 1 (by rfl) ⟨1978316, by rfl⟩ : syracuseStep 2637755 = 3956633) B3956633
theorem B10862545 : Blo 1758080 10862545 := bstep (se 2 (by rfl) ⟨4073454, by rfl⟩ : syracuseStep 10862545 = 8146909) B8146909
theorem B2637815 : Blo 1758080 2637815 := bstep (se 1 (by rfl) ⟨1978361, by rfl⟩ : syracuseStep 2637815 = 3956723) B3956723
theorem B4227079 : Blo 1758080 4227079 := bstep (se 1 (by rfl) ⟨3170309, by rfl⟩ : syracuseStep 4227079 = 6340619) B6340619
theorem B2637833 : Blo 1758080 2637833 := bstep (se 2 (by rfl) ⟨989187, by rfl⟩ : syracuseStep 2637833 = 1978375) B1978375
theorem B15024143 : Blo 1758080 15024143 := bstep (se 1 (by rfl) ⟨11268107, by rfl⟩ : syracuseStep 15024143 = 22536215) B22536215
theorem B2637863 : Blo 1758080 2637863 := bstep (se 1 (by rfl) ⟨1978397, by rfl⟩ : syracuseStep 2637863 = 3956795) B3956795
theorem B2637947 : Blo 1758080 2637947 := bstep (se 1 (by rfl) ⟨1978460, by rfl⟩ : syracuseStep 2637947 = 3956921) B3956921
theorem B2638073 : Blo 1758080 2638073 := bstep (se 2 (by rfl) ⟨989277, by rfl⟩ : syracuseStep 2638073 = 1978555) B1978555
theorem B2638175 : Blo 1758080 2638175 := bstep (se 1 (by rfl) ⟨1978631, by rfl⟩ : syracuseStep 2638175 = 3957263) B3957263
theorem B2638187 : Blo 1758080 2638187 := bstep (se 1 (by rfl) ⟨1978640, by rfl⟩ : syracuseStep 2638187 = 3957281) B3957281
theorem B5349851 : Blo 1758080 5349851 := bstep (se 1 (by rfl) ⟨4012388, by rfl⟩ : syracuseStep 5349851 = 8024777) B8024777
theorem B5079515 : Blo 1758080 5079515 := bstep (se 1 (by rfl) ⟨3809636, by rfl⟩ : syracuseStep 5079515 = 7619273) B7619273
theorem B5939675 : Blo 1758080 5939675 := bstep (se 1 (by rfl) ⟨4454756, by rfl⟩ : syracuseStep 5939675 = 8909513) B8909513
theorem B15032891 : Blo 1758080 15032891 := bstep (se 1 (by rfl) ⟨11274668, by rfl⟩ : syracuseStep 15032891 = 22549337) B22549337
theorem B2638415 : Blo 1758080 2638415 := bstep (se 1 (by rfl) ⟨1978811, by rfl⟩ : syracuseStep 2638415 = 3957623) B3957623
theorem B3957371 : Blo 1758080 3957371 := bstep (se 1 (by rfl) ⟨2968028, by rfl⟩ : syracuseStep 3957371 = 5936057) B5936057
theorem B11272877 : Blo 1758080 11272877 := bstep (se 3 (by rfl) ⟨2113664, by rfl⟩ : syracuseStep 11272877 = 4227329) B4227329
theorem B2638535 : Blo 1758080 2638535 := bstep (se 1 (by rfl) ⟨1978901, by rfl⟩ : syracuseStep 2638535 = 3957803) B3957803
theorem B10019537 : Blo 1758080 10019537 := bstep (se 2 (by rfl) ⟨3757326, by rfl⟩ : syracuseStep 10019537 = 7514653) B7514653
theorem B3957497 : Blo 1758080 3957497 := bstep (se 2 (by rfl) ⟨1484061, by rfl⟩ : syracuseStep 3957497 = 2968123) B2968123
theorem B4514633 : Blo 1758080 4514633 := bstep (se 2 (by rfl) ⟨1692987, by rfl⟩ : syracuseStep 4514633 = 3385975) B3385975
theorem B2638697 : Blo 1758080 2638697 := bstep (se 2 (by rfl) ⟨989511, by rfl⟩ : syracuseStep 2638697 = 1979023) B1979023
theorem B2638775 : Blo 1758080 2638775 := bstep (se 1 (by rfl) ⟨1979081, by rfl⟩ : syracuseStep 2638775 = 3958163) B3958163
theorem B27452363 : Blo 1758080 27452363 := bstep (se 1 (by rfl) ⟨20589272, by rfl⟩ : syracuseStep 27452363 = 41178545) B41178545
theorem B2638811 : Blo 1758080 2638811 := bstep (se 1 (by rfl) ⟨1979108, by rfl⟩ : syracuseStep 2638811 = 3958217) B3958217
theorem B3957767 : Blo 1758080 3957767 := bstep (se 1 (by rfl) ⟨2968325, by rfl⟩ : syracuseStep 3957767 = 5936651) B5936651
theorem B3171347 : Blo 1758080 3171347 := bstep (se 1 (by rfl) ⟨2378510, by rfl⟩ : syracuseStep 3171347 = 4757021) B4757021
theorem B3957839 : Blo 1758080 3957839 := bstep (se 1 (by rfl) ⟨2968379, by rfl⟩ : syracuseStep 3957839 = 5936759) B5936759
theorem B22553801 : Blo 1758080 22553801 := bstep (se 2 (by rfl) ⟨8457675, by rfl⟩ : syracuseStep 22553801 = 16915351) B16915351
theorem B5350799 : Blo 1758080 5350799 := bstep (se 1 (by rfl) ⟨4013099, by rfl⟩ : syracuseStep 5350799 = 8026199) B8026199
theorem B2639279 : Blo 1758080 2639279 := bstep (se 1 (by rfl) ⟨1979459, by rfl⟩ : syracuseStep 2639279 = 3958919) B3958919
theorem B3958235 : Blo 1758080 3958235 := bstep (se 1 (by rfl) ⟨2968676, by rfl⟩ : syracuseStep 3958235 = 5937353) B5937353
theorem B27084293 : Blo 1758080 27084293 := bstep (se 4 (by rfl) ⟨2539152, by rfl⟩ : syracuseStep 27084293 = 5078305) B5078305
theorem B2639369 : Blo 1758080 2639369 := bstep (se 2 (by rfl) ⟨989763, by rfl⟩ : syracuseStep 2639369 = 1979527) B1979527
theorem B2639399 : Blo 1758080 2639399 := bstep (se 1 (by rfl) ⟨1979549, by rfl⟩ : syracuseStep 2639399 = 3959099) B3959099
theorem B2967097 : Blo 1758080 2967097 := bstep (se 2 (by rfl) ⟨1112661, by rfl⟩ : syracuseStep 2967097 = 2225323) B2225323
theorem B2639483 : Blo 1758080 2639483 := bstep (se 1 (by rfl) ⟨1979612, by rfl⟩ : syracuseStep 2639483 = 3959225) B3959225
theorem B2967239 : Blo 1758080 2967239 := bstep (se 1 (by rfl) ⟨2225429, by rfl⟩ : syracuseStep 2967239 = 4450859) B4450859
theorem B6768377 : Blo 1758080 6768377 := bstep (se 2 (by rfl) ⟨2538141, by rfl⟩ : syracuseStep 6768377 = 5076283) B5076283
theorem B2639609 : Blo 1758080 2639609 := bstep (se 2 (by rfl) ⟨989853, by rfl⟩ : syracuseStep 2639609 = 1979707) B1979707
theorem B28542779 : Blo 1758080 28542779 := bstep (se 1 (by rfl) ⟨21407084, by rfl⟩ : syracuseStep 28542779 = 42814169) B42814169
theorem B7128899 : Blo 1758080 7128899 := bstep (se 1 (by rfl) ⟨5346674, by rfl⟩ : syracuseStep 7128899 = 10693349) B10693349
theorem B2639711 : Blo 1758080 2639711 := bstep (se 1 (by rfl) ⟨1979783, by rfl⟩ : syracuseStep 2639711 = 3959567) B3959567
theorem B2967401 : Blo 1758080 2967401 := bstep (se 2 (by rfl) ⟨1112775, by rfl⟩ : syracuseStep 2967401 = 2225551) B2225551
theorem B2639723 : Blo 1758080 2639723 := bstep (se 1 (by rfl) ⟨1979792, by rfl⟩ : syracuseStep 2639723 = 3959585) B3959585
theorem B3958703 : Blo 1758080 3958703 := bstep (se 1 (by rfl) ⟨2969027, by rfl⟩ : syracuseStep 3958703 = 5938055) B5938055
theorem B8906759 : Blo 1758080 8906759 := bstep (se 1 (by rfl) ⟨6680069, by rfl⟩ : syracuseStep 8906759 = 13360139) B13360139
theorem B21678137 : Blo 1758080 21678137 := bstep (se 2 (by rfl) ⟨8129301, by rfl⟩ : syracuseStep 21678137 = 16258603) B16258603
theorem B19023929 : Blo 1758080 19023929 := bstep (se 2 (by rfl) ⟨7133973, by rfl⟩ : syracuseStep 19023929 = 14267947) B14267947
theorem B2639951 : Blo 1758080 2639951 := bstep (se 1 (by rfl) ⟨1979963, by rfl⟩ : syracuseStep 2639951 = 3959927) B3959927
theorem B7129241 : Blo 1758080 7129241 := bstep (se 2 (by rfl) ⟨2673465, by rfl⟩ : syracuseStep 7129241 = 5346931) B5346931
theorem B3958955 : Blo 1758080 3958955 := bstep (se 1 (by rfl) ⟨2969216, by rfl⟩ : syracuseStep 3958955 = 5938433) B5938433
theorem B2377927 : Blo 1758080 2377927 := bstep (se 1 (by rfl) ⟨1783445, by rfl⟩ : syracuseStep 2377927 = 3566891) B3566891
theorem B2640071 : Blo 1758080 2640071 := bstep (se 1 (by rfl) ⟨1980053, by rfl⟩ : syracuseStep 2640071 = 3960107) B3960107
theorem B2967799 : Blo 1758080 2967799 := bstep (se 1 (by rfl) ⟨2225849, by rfl⟩ : syracuseStep 2967799 = 4451699) B4451699
theorem B2967995 : Blo 1758080 2967995 := bstep (se 1 (by rfl) ⟨2225996, by rfl⟩ : syracuseStep 2967995 = 4451993) B4451993
theorem B8907245 : Blo 1758080 8907245 := bstep (se 3 (by rfl) ⟨1670108, by rfl⟩ : syracuseStep 8907245 = 3340217) B3340217
theorem B4753907 : Blo 1758080 4753907 := bstep (se 1 (by rfl) ⟨3565430, by rfl⟩ : syracuseStep 4753907 = 7130861) B7130861
theorem B2968103 : Blo 1758080 2968103 := bstep (se 1 (by rfl) ⟨2226077, by rfl⟩ : syracuseStep 2968103 = 4452155) B4452155
theorem B5933627 : Blo 1758080 5933627 := bstep (se 1 (by rfl) ⟨4450220, by rfl⟩ : syracuseStep 5933627 = 8900441) B8900441
theorem B3959495 : Blo 1758080 3959495 := bstep (se 1 (by rfl) ⟨2969621, by rfl⟩ : syracuseStep 3959495 = 5939243) B5939243
theorem B2378489 : Blo 1758080 2378489 := bstep (se 2 (by rfl) ⟨891933, by rfl⟩ : syracuseStep 2378489 = 1783867) B1783867
theorem B5933897 : Blo 1758080 5933897 := bstep (se 2 (by rfl) ⟨2225211, by rfl⟩ : syracuseStep 5933897 = 4450423) B4450423
theorem B2968393 : Blo 1758080 2968393 := bstep (se 2 (by rfl) ⟨1113147, by rfl⟩ : syracuseStep 2968393 = 2226295) B2226295
theorem B2968427 : Blo 1758080 2968427 := bstep (se 1 (by rfl) ⟨2226320, by rfl⟩ : syracuseStep 2968427 = 4452641) B4452641
theorem B6097783 : Blo 1758080 6097783 := bstep (se 1 (by rfl) ⟨4573337, by rfl⟩ : syracuseStep 6097783 = 9146675) B9146675
theorem B4451233 : Blo 1758080 4451233 := bstep (se 2 (by rfl) ⟨1669212, by rfl⟩ : syracuseStep 4451233 = 3338425) B3338425
theorem B6679705 : Blo 1758080 6679705 := bstep (se 2 (by rfl) ⟨2504889, by rfl⟩ : syracuseStep 6679705 = 5009779) B5009779
theorem B8457463 : Blo 1758080 8457463 := bstep (se 1 (by rfl) ⟨6343097, by rfl⟩ : syracuseStep 8457463 = 12686195) B12686195
theorem B2968825 : Blo 1758080 2968825 := bstep (se 2 (by rfl) ⟨1113309, by rfl⟩ : syracuseStep 2968825 = 2226619) B2226619
theorem B8908055 : Blo 1758080 8908055 := bstep (se 1 (by rfl) ⟨6681041, by rfl⟩ : syracuseStep 8908055 = 13362083) B13362083
theorem B6680009 : Blo 1758080 6680009 := bstep (se 2 (by rfl) ⟨2505003, by rfl⟩ : syracuseStep 6680009 = 5010007) B5010007
theorem B7515611 : Blo 1758080 7515611 := bstep (se 1 (by rfl) ⟨5636708, by rfl⟩ : syracuseStep 7515611 = 11273417) B11273417
theorem B2969095 : Blo 1758080 2969095 := bstep (se 1 (by rfl) ⟨2226821, by rfl⟩ : syracuseStep 2969095 = 4453643) B4453643
theorem B1977979 : Blo 1758080 1977979 := bstep (se 1 (by rfl) ⟨1483484, by rfl⟩ : syracuseStep 1977979 = 2966969) B2966969
theorem B19017355 : Blo 1758080 19017355 := bstep (se 1 (by rfl) ⟨14263016, by rfl⟩ : syracuseStep 19017355 = 28526033) B28526033
theorem B3337939 : Blo 1758080 3337939 := bstep (se 1 (by rfl) ⟨2503454, by rfl⟩ : syracuseStep 3337939 = 5006909) B5006909
theorem B6680495 : Blo 1758080 6680495 := bstep (se 1 (by rfl) ⟨5010371, by rfl⟩ : syracuseStep 6680495 = 10020743) B10020743
theorem B3338167 : Blo 1758080 3338167 := bstep (se 1 (by rfl) ⟨2503625, by rfl⟩ : syracuseStep 3338167 = 5007251) B5007251
theorem B5935031 : Blo 1758080 5935031 := bstep (se 1 (by rfl) ⟨4451273, by rfl⟩ : syracuseStep 5935031 = 8902547) B8902547
theorem B16912313 : Blo 1758080 16912313 := bstep (se 2 (by rfl) ⟨6342117, by rfl⟩ : syracuseStep 16912313 = 12684235) B12684235
theorem B2969527 : Blo 1758080 2969527 := bstep (se 1 (by rfl) ⟨2227145, by rfl⟩ : syracuseStep 2969527 = 4454291) B4454291
theorem B1978447 : Blo 1758080 1978447 := bstep (se 1 (by rfl) ⟨1483835, by rfl⟩ : syracuseStep 1978447 = 2967671) B2967671
theorem B2969723 : Blo 1758080 2969723 := bstep (se 1 (by rfl) ⟨2227292, by rfl⟩ : syracuseStep 2969723 = 4454585) B4454585
theorem B8900765 : Blo 1758080 8900765 := bstep (se 3 (by rfl) ⟨1668893, by rfl⟩ : syracuseStep 8900765 = 3337787) B3337787
theorem B3567977 : Blo 1758080 3567977 := bstep (se 2 (by rfl) ⟨1337991, by rfl⟩ : syracuseStep 3567977 = 2675983) B2675983
theorem B2257327 : Blo 1758080 2257327 := bstep (se 1 (by rfl) ⟨1692995, by rfl⟩ : syracuseStep 2257327 = 3385991) B3385991
theorem B1978843 : Blo 1758080 1978843 := bstep (se 1 (by rfl) ⟨1484132, by rfl⟩ : syracuseStep 1978843 = 2968265) B2968265
theorem B3338759 : Blo 1758080 3338759 := bstep (se 1 (by rfl) ⟨2504069, by rfl⟩ : syracuseStep 3338759 = 5008139) B5008139
theorem B5935625 : Blo 1758080 5935625 := bstep (se 2 (by rfl) ⟨2225859, by rfl⟩ : syracuseStep 5935625 = 4451719) B4451719
theorem B2970121 : Blo 1758080 2970121 := bstep (se 2 (by rfl) ⟨1113795, by rfl⟩ : syracuseStep 2970121 = 2227591) B2227591
theorem B6337273 : Blo 1758080 6337273 := bstep (se 2 (by rfl) ⟨2376477, by rfl⟩ : syracuseStep 6337273 = 4752955) B4752955
theorem B20034377 : Blo 1758080 20034377 := bstep (se 2 (by rfl) ⟨7512891, by rfl⟩ : syracuseStep 20034377 = 15025783) B15025783
theorem B10015595 : Blo 1758080 10015595 := bstep (se 1 (by rfl) ⟨7511696, by rfl⟩ : syracuseStep 10015595 = 15023393) B15023393
theorem B8909675 : Blo 1758080 8909675 := bstep (se 1 (by rfl) ⟨6682256, by rfl⟩ : syracuseStep 8909675 = 13364513) B13364513
theorem B1758127 : Blo 1758080 1758127 := bstep (se 1 (by rfl) ⟨1318595, by rfl⟩ : syracuseStep 1758127 = 2637191) B2637191
theorem B1979311 : Blo 1758080 1979311 := bstep (se 1 (by rfl) ⟨1484483, by rfl⟩ : syracuseStep 1979311 = 2968967) B2968967
theorem B1758151 : Blo 1758080 1758151 := bstep (se 1 (by rfl) ⟨1318613, by rfl⟩ : syracuseStep 1758151 = 2637227) B2637227
theorem B1758171 : Blo 1758080 1758171 := bstep (se 1 (by rfl) ⟨1318628, by rfl⟩ : syracuseStep 1758171 = 2637257) B2637257
theorem B12686309 : Blo 1758080 12686309 := bstep (se 4 (by rfl) ⟨1189341, by rfl⟩ : syracuseStep 12686309 = 2378683) B2378683
theorem B1758247 : Blo 1758080 1758247 := bstep (se 1 (by rfl) ⟨1318685, by rfl⟩ : syracuseStep 1758247 = 2637371) B2637371
theorem B18060337 : Blo 1758080 18060337 := bstep (se 2 (by rfl) ⟨6772626, by rfl⟩ : syracuseStep 18060337 = 13545253) B13545253
theorem B1758287 : Blo 1758080 1758287 := bstep (se 1 (by rfl) ⟨1318715, by rfl⟩ : syracuseStep 1758287 = 2637431) B2637431
theorem B1758303 : Blo 1758080 1758303 := bstep (se 1 (by rfl) ⟨1318727, by rfl⟩ : syracuseStep 1758303 = 2637455) B2637455
theorem B1758331 : Blo 1758080 1758331 := bstep (se 1 (by rfl) ⟨1318748, by rfl⟩ : syracuseStep 1758331 = 2637497) B2637497
theorem B1758383 : Blo 1758080 1758383 := bstep (se 1 (by rfl) ⟨1318787, by rfl⟩ : syracuseStep 1758383 = 2637575) B2637575
theorem B1758407 : Blo 1758080 1758407 := bstep (se 1 (by rfl) ⟨1318805, by rfl⟩ : syracuseStep 1758407 = 2637611) B2637611
theorem B16897241 : Blo 1758080 16897241 := bstep (se 2 (by rfl) ⟨6336465, by rfl⟩ : syracuseStep 16897241 = 12672931) B12672931
theorem B1758427 : Blo 1758080 1758427 := bstep (se 1 (by rfl) ⟨1318820, by rfl⟩ : syracuseStep 1758427 = 2637641) B2637641
theorem B1783003 : Blo 1758080 1783003 := bstep (se 1 (by rfl) ⟨1337252, by rfl⟩ : syracuseStep 1783003 = 2674505) B2674505
theorem B1758503 : Blo 1758080 1758503 := bstep (se 1 (by rfl) ⟨1318877, by rfl⟩ : syracuseStep 1758503 = 2637755) B2637755
theorem B1758543 : Blo 1758080 1758543 := bstep (se 1 (by rfl) ⟨1318907, by rfl⟩ : syracuseStep 1758543 = 2637815) B2637815
theorem B1758559 : Blo 1758080 1758559 := bstep (se 1 (by rfl) ⟨1318919, by rfl⟩ : syracuseStep 1758559 = 2637839) B2637839
theorem B1979743 : Blo 1758080 1979743 := bstep (se 1 (by rfl) ⟨1484807, by rfl⟩ : syracuseStep 1979743 = 2969615) B2969615
theorem B5936489 : Blo 1758080 5936489 := bstep (se 2 (by rfl) ⟨2226183, by rfl⟩ : syracuseStep 5936489 = 4452367) B4452367
theorem B3339625 : Blo 1758080 3339625 := bstep (se 2 (by rfl) ⟨1252359, by rfl⟩ : syracuseStep 3339625 = 2504719) B2504719
theorem B1758587 : Blo 1758080 1758587 := bstep (se 1 (by rfl) ⟨1318940, by rfl⟩ : syracuseStep 1758587 = 2637881) B2637881
theorem B4453775 : Blo 1758080 4453775 := bstep (se 1 (by rfl) ⟨3340331, by rfl⟩ : syracuseStep 4453775 = 6680663) B6680663
theorem B8902061 : Blo 1758080 8902061 := bstep (se 3 (by rfl) ⟨1669136, by rfl⟩ : syracuseStep 8902061 = 3338273) B3338273
theorem B1758639 : Blo 1758080 1758639 := bstep (se 1 (by rfl) ⟨1318979, by rfl⟩ : syracuseStep 1758639 = 2637959) B2637959
theorem B1758663 : Blo 1758080 1758663 := bstep (se 1 (by rfl) ⟨1318997, by rfl⟩ : syracuseStep 1758663 = 2637995) B2637995
theorem B1758683 : Blo 1758080 1758683 := bstep (se 1 (by rfl) ⟨1319012, by rfl⟩ : syracuseStep 1758683 = 2638025) B2638025
theorem B8910323 : Blo 1758080 8910323 := bstep (se 1 (by rfl) ⟨6682742, by rfl⟩ : syracuseStep 8910323 = 13365485) B13365485
theorem B3339785 : Blo 1758080 3339785 := bstep (se 2 (by rfl) ⟨1252419, by rfl⟩ : syracuseStep 3339785 = 2504839) B2504839
theorem B6682121 : Blo 1758080 6682121 := bstep (se 2 (by rfl) ⟨2505795, by rfl⟩ : syracuseStep 6682121 = 5011591) B5011591
theorem B6338081 : Blo 1758080 6338081 := bstep (se 2 (by rfl) ⟨2376780, by rfl⟩ : syracuseStep 6338081 = 4753561) B4753561
theorem B1758759 : Blo 1758080 1758759 := bstep (se 1 (by rfl) ⟨1319069, by rfl⟩ : syracuseStep 1758759 = 2638139) B2638139
theorem B42817085 : Blo 1758080 42817085 := bstep (se 3 (by rfl) ⟨8028203, by rfl⟩ : syracuseStep 42817085 = 16056407) B16056407
theorem B1758799 : Blo 1758080 1758799 := bstep (se 1 (by rfl) ⟨1319099, by rfl⟩ : syracuseStep 1758799 = 2638199) B2638199
theorem B1758815 : Blo 1758080 1758815 := bstep (se 1 (by rfl) ⟨1319111, by rfl⟩ : syracuseStep 1758815 = 2638223) B2638223
theorem B1758843 : Blo 1758080 1758843 := bstep (se 1 (by rfl) ⟨1319132, by rfl⟩ : syracuseStep 1758843 = 2638265) B2638265
theorem B5633671 : Blo 1758080 5633671 := bstep (se 1 (by rfl) ⟨4225253, by rfl⟩ : syracuseStep 5633671 = 8450507) B8450507
theorem B1758895 : Blo 1758080 1758895 := bstep (se 1 (by rfl) ⟨1319171, by rfl⟩ : syracuseStep 1758895 = 2638343) B2638343
theorem B1758919 : Blo 1758080 1758919 := bstep (se 1 (by rfl) ⟨1319189, by rfl⟩ : syracuseStep 1758919 = 2638379) B2638379
theorem B4454099 : Blo 1758080 4454099 := bstep (se 1 (by rfl) ⟨3340574, by rfl⟩ : syracuseStep 4454099 = 6681149) B6681149
theorem B1758939 : Blo 1758080 1758939 := bstep (se 1 (by rfl) ⟨1319204, by rfl⟩ : syracuseStep 1758939 = 2638409) B2638409
theorem B11269853 : Blo 1758080 11269853 := bstep (se 3 (by rfl) ⟨2113097, by rfl⟩ : syracuseStep 11269853 = 4226195) B4226195
theorem B51410689 : Blo 1758080 51410689 := bstep (se 2 (by rfl) ⟨19279008, by rfl⟩ : syracuseStep 51410689 = 38558017) B38558017
theorem B1759015 : Blo 1758080 1759015 := bstep (se 1 (by rfl) ⟨1319261, by rfl⟩ : syracuseStep 1759015 = 2638523) B2638523
theorem B30463787 : Blo 1758080 30463787 := bstep (se 1 (by rfl) ⟨22847840, by rfl⟩ : syracuseStep 30463787 = 45695681) B45695681
theorem B6338371 : Blo 1758080 6338371 := bstep (se 1 (by rfl) ⟨4753778, by rfl⟩ : syracuseStep 6338371 = 9507557) B9507557
theorem B1759055 : Blo 1758080 1759055 := bstep (se 1 (by rfl) ⟨1319291, by rfl⟩ : syracuseStep 1759055 = 2638583) B2638583
theorem B1759071 : Blo 1758080 1759071 := bstep (se 1 (by rfl) ⟨1319303, by rfl⟩ : syracuseStep 1759071 = 2638607) B2638607
theorem B10016621 : Blo 1758080 10016621 := bstep (se 3 (by rfl) ⟨1878116, by rfl⟩ : syracuseStep 10016621 = 3756233) B3756233
theorem B1759099 : Blo 1758080 1759099 := bstep (se 1 (by rfl) ⟨1319324, by rfl⟩ : syracuseStep 1759099 = 2638649) B2638649
theorem B1759151 : Blo 1758080 1759151 := bstep (se 1 (by rfl) ⟨1319363, by rfl⟩ : syracuseStep 1759151 = 2638727) B2638727
theorem B5937083 : Blo 1758080 5937083 := bstep (se 1 (by rfl) ⟨4452812, by rfl⟩ : syracuseStep 5937083 = 8905625) B8905625
theorem B1759175 : Blo 1758080 1759175 := bstep (se 1 (by rfl) ⟨1319381, by rfl⟩ : syracuseStep 1759175 = 2638763) B2638763
theorem B1759195 : Blo 1758080 1759195 := bstep (se 1 (by rfl) ⟨1319396, by rfl⟩ : syracuseStep 1759195 = 2638793) B2638793
theorem B1759271 : Blo 1758080 1759271 := bstep (se 1 (by rfl) ⟨1319453, by rfl⟩ : syracuseStep 1759271 = 2638907) B2638907
theorem B1759311 : Blo 1758080 1759311 := bstep (se 1 (by rfl) ⟨1319483, by rfl⟩ : syracuseStep 1759311 = 2638967) B2638967
theorem B1759327 : Blo 1758080 1759327 := bstep (se 1 (by rfl) ⟨1319495, by rfl⟩ : syracuseStep 1759327 = 2638991) B2638991
theorem B1759355 : Blo 1758080 1759355 := bstep (se 1 (by rfl) ⟨1319516, by rfl⟩ : syracuseStep 1759355 = 2639033) B2639033
theorem B4511915 : Blo 1758080 4511915 := bstep (se 1 (by rfl) ⟨3383936, by rfl⟩ : syracuseStep 4511915 = 6767873) B6767873
theorem B1759407 : Blo 1758080 1759407 := bstep (se 1 (by rfl) ⟨1319555, by rfl⟩ : syracuseStep 1759407 = 2639111) B2639111
theorem B1759431 : Blo 1758080 1759431 := bstep (se 1 (by rfl) ⟨1319573, by rfl⟩ : syracuseStep 1759431 = 2639147) B2639147
theorem B1759451 : Blo 1758080 1759451 := bstep (se 1 (by rfl) ⟨1319588, by rfl⟩ : syracuseStep 1759451 = 2639177) B2639177
theorem B1759527 : Blo 1758080 1759527 := bstep (se 1 (by rfl) ⟨1319645, by rfl⟩ : syracuseStep 1759527 = 2639291) B2639291
theorem B22288691 : Blo 1758080 22288691 := bstep (se 1 (by rfl) ⟨16716518, by rfl⟩ : syracuseStep 22288691 = 33433037) B33433037
theorem B1759567 : Blo 1758080 1759567 := bstep (se 1 (by rfl) ⟨1319675, by rfl⟩ : syracuseStep 1759567 = 2639351) B2639351
theorem B1759583 : Blo 1758080 1759583 := bstep (se 1 (by rfl) ⟨1319687, by rfl⟩ : syracuseStep 1759583 = 2639375) B2639375
theorem B1759611 : Blo 1758080 1759611 := bstep (se 1 (by rfl) ⟨1319708, by rfl⟩ : syracuseStep 1759611 = 2639417) B2639417
theorem B1759663 : Blo 1758080 1759663 := bstep (se 1 (by rfl) ⟨1319747, by rfl⟩ : syracuseStep 1759663 = 2639495) B2639495
theorem B3168695 : Blo 1758080 3168695 := bstep (se 1 (by rfl) ⟨2376521, by rfl⟩ : syracuseStep 3168695 = 4753043) B4753043
theorem B2537911 : Blo 1758080 2537911 := bstep (se 1 (by rfl) ⟨1903433, by rfl⟩ : syracuseStep 2537911 = 3806867) B3806867
theorem B2857399 : Blo 1758080 2857399 := bstep (se 1 (by rfl) ⟨2143049, by rfl⟩ : syracuseStep 2857399 = 4286099) B4286099
theorem B1759687 : Blo 1758080 1759687 := bstep (se 1 (by rfl) ⟨1319765, by rfl⟩ : syracuseStep 1759687 = 2639531) B2639531
theorem B1759707 : Blo 1758080 1759707 := bstep (se 1 (by rfl) ⟨1319780, by rfl⟩ : syracuseStep 1759707 = 2639561) B2639561
theorem B7510553 : Blo 1758080 7510553 := bstep (se 2 (by rfl) ⟨2816457, by rfl⟩ : syracuseStep 7510553 = 5632915) B5632915
theorem B5634593 : Blo 1758080 5634593 := bstep (se 2 (by rfl) ⟨2112972, by rfl⟩ : syracuseStep 5634593 = 4225945) B4225945
theorem B16308769 : Blo 1758080 16308769 := bstep (se 2 (by rfl) ⟨6115788, by rfl⟩ : syracuseStep 16308769 = 12231577) B12231577
theorem B1759783 : Blo 1758080 1759783 := bstep (se 1 (by rfl) ⟨1319837, by rfl⟩ : syracuseStep 1759783 = 2639675) B2639675
theorem B12679739 : Blo 1758080 12679739 := bstep (se 1 (by rfl) ⟨9509804, by rfl⟩ : syracuseStep 12679739 = 19019609) B19019609
theorem B1759823 : Blo 1758080 1759823 := bstep (se 1 (by rfl) ⟨1319867, by rfl⟩ : syracuseStep 1759823 = 2639735) B2639735
theorem B1759839 : Blo 1758080 1759839 := bstep (se 1 (by rfl) ⟨1319879, by rfl⟩ : syracuseStep 1759839 = 2639759) B2639759
theorem B1759867 : Blo 1758080 1759867 := bstep (se 1 (by rfl) ⟨1319900, by rfl⟩ : syracuseStep 1759867 = 2639801) B2639801
theorem B10156679 : Blo 1758080 10156679 := bstep (se 1 (by rfl) ⟨7617509, by rfl⟩ : syracuseStep 10156679 = 15235019) B15235019
theorem B1759919 : Blo 1758080 1759919 := bstep (se 1 (by rfl) ⟨1319939, by rfl⟩ : syracuseStep 1759919 = 2639879) B2639879
theorem B1759943 : Blo 1758080 1759943 := bstep (se 1 (by rfl) ⟨1319957, by rfl⟩ : syracuseStep 1759943 = 2639915) B2639915
theorem B1759963 : Blo 1758080 1759963 := bstep (se 1 (by rfl) ⟨1319972, by rfl⟩ : syracuseStep 1759963 = 2639945) B2639945
theorem B1760039 : Blo 1758080 1760039 := bstep (se 1 (by rfl) ⟨1320029, by rfl⟩ : syracuseStep 1760039 = 2640059) B2640059
theorem B1760079 : Blo 1758080 1760079 := bstep (se 1 (by rfl) ⟨1320059, by rfl⟩ : syracuseStep 1760079 = 2640119) B2640119
theorem B5635003 : Blo 1758080 5635003 := bstep (se 1 (by rfl) ⟨4226252, by rfl⟩ : syracuseStep 5635003 = 8452505) B8452505
theorem B3341243 : Blo 1758080 3341243 := bstep (se 1 (by rfl) ⟨2505932, by rfl⟩ : syracuseStep 3341243 = 5011865) B5011865
theorem B8903681 : Blo 1758080 8903681 := bstep (se 2 (by rfl) ⟨3338880, by rfl⟩ : syracuseStep 8903681 = 6677761) B6677761
theorem B3955769 : Blo 1758080 3955769 := bstep (se 2 (by rfl) ⟨1483413, by rfl⟩ : syracuseStep 3955769 = 2966827) B2966827
theorem B6511673 : Blo 1758080 6511673 := bstep (se 2 (by rfl) ⟨2441877, by rfl⟩ : syracuseStep 6511673 = 4883755) B4883755
theorem B2637161 : Blo 1758080 2637161 := bstep (se 2 (by rfl) ⟨988935, by rfl⟩ : syracuseStep 2637161 = 1977871) B1977871
theorem B6675817 : Blo 1758080 6675817 := bstep (se 2 (by rfl) ⟨2503431, by rfl⟩ : syracuseStep 6675817 = 5006863) B5006863
theorem B3956111 : Blo 1758080 3956111 := bstep (se 1 (by rfl) ⟨2967083, by rfl⟩ : syracuseStep 3956111 = 5934167) B5934167
theorem B2637239 : Blo 1758080 2637239 := bstep (se 1 (by rfl) ⟨1977929, by rfl⟩ : syracuseStep 2637239 = 3955859) B3955859
theorem B2637275 : Blo 1758080 2637275 := bstep (se 1 (by rfl) ⟨1977956, by rfl⟩ : syracuseStep 2637275 = 3955913) B3955913
theorem B6676091 : Blo 1758080 6676091 := bstep (se 1 (by rfl) ⟨5007068, by rfl⟩ : syracuseStep 6676091 = 10014137) B10014137
theorem B5938811 : Blo 1758080 5938811 := bstep (se 1 (by rfl) ⟨4454108, by rfl⟩ : syracuseStep 5938811 = 8908217) B8908217
theorem B3169963 : Blo 1758080 3169963 := bstep (se 1 (by rfl) ⟨2377472, by rfl⟩ : syracuseStep 3169963 = 4754945) B4754945
theorem B28524221 : Blo 1758080 28524221 := bstep (se 3 (by rfl) ⟨5348291, by rfl⟩ : syracuseStep 28524221 = 10696583) B10696583
theorem B3956435 : Blo 1758080 3956435 := bstep (se 1 (by rfl) ⟨2967326, by rfl⟩ : syracuseStep 3956435 = 5934653) B5934653
theorem B4226771 : Blo 1758080 4226771 := bstep (se 1 (by rfl) ⟨3170078, by rfl⟩ : syracuseStep 4226771 = 6340157) B6340157
theorem B5938973 : Blo 1758080 5938973 := bstep (se 3 (by rfl) ⟨1113557, by rfl⟩ : syracuseStep 5938973 = 2227115) B2227115
theorem B8904491 : Blo 1758080 8904491 := bstep (se 1 (by rfl) ⟨6678368, by rfl⟩ : syracuseStep 8904491 = 13356737) B13356737
theorem B2817899 : Blo 1758080 2817899 := bstep (se 1 (by rfl) ⟨2113424, by rfl⟩ : syracuseStep 2817899 = 4226849) B4226849
theorem B2637743 : Blo 1758080 2637743 := bstep (se 1 (by rfl) ⟨1978307, by rfl⟩ : syracuseStep 2637743 = 3956615) B3956615
theorem B14483393 : Blo 1758080 14483393 := bstep (se 2 (by rfl) ⟨5431272, by rfl⟩ : syracuseStep 14483393 = 10862545) B10862545
theorem B14270417 : Blo 1758080 14270417 := bstep (se 2 (by rfl) ⟨5351406, by rfl⟩ : syracuseStep 14270417 = 10702813) B10702813
theorem B5636105 : Blo 1758080 5636105 := bstep (se 2 (by rfl) ⟨2113539, by rfl⟩ : syracuseStep 5636105 = 4227079) B4227079
theorem B2637929 : Blo 1758080 2637929 := bstep (se 2 (by rfl) ⟨989223, by rfl⟩ : syracuseStep 2637929 = 1978447) B1978447
theorem B3957065 : Blo 1758080 3957065 := bstep (se 2 (by rfl) ⟨1483899, by rfl⟩ : syracuseStep 3957065 = 2967799) B2967799
theorem B3957083 : Blo 1758080 3957083 := bstep (se 1 (by rfl) ⟨2967812, by rfl⟩ : syracuseStep 3957083 = 5935625) B5935625
theorem B2638247 : Blo 1758080 2638247 := bstep (se 1 (by rfl) ⟨1978685, by rfl⟩ : syracuseStep 2638247 = 3957371) B3957371
theorem B2638331 : Blo 1758080 2638331 := bstep (se 1 (by rfl) ⟨1978748, by rfl⟩ : syracuseStep 2638331 = 3957497) B3957497
theorem B6677063 : Blo 1758080 6677063 := bstep (se 1 (by rfl) ⟨5007797, by rfl⟩ : syracuseStep 6677063 = 10015595) B10015595
theorem B5939783 : Blo 1758080 5939783 := bstep (se 1 (by rfl) ⟨4454837, by rfl⟩ : syracuseStep 5939783 = 8909675) B8909675
theorem B2638457 : Blo 1758080 2638457 := bstep (se 2 (by rfl) ⟨989421, by rfl⟩ : syracuseStep 2638457 = 1978843) B1978843
theorem B2638511 : Blo 1758080 2638511 := bstep (se 1 (by rfl) ⟨1978883, by rfl⟩ : syracuseStep 2638511 = 3957767) B3957767
theorem B2114231 : Blo 1758080 2114231 := bstep (se 1 (by rfl) ⟨1585673, by rfl⟩ : syracuseStep 2114231 = 3171347) B3171347
theorem B2638559 : Blo 1758080 2638559 := bstep (se 1 (by rfl) ⟨1978919, by rfl⟩ : syracuseStep 2638559 = 3957839) B3957839
theorem B11264827 : Blo 1758080 11264827 := bstep (se 1 (by rfl) ⟨8448620, by rfl⟩ : syracuseStep 11264827 = 16897241) B16897241
theorem B3957659 : Blo 1758080 3957659 := bstep (se 1 (by rfl) ⟨2968244, by rfl⟩ : syracuseStep 3957659 = 5936489) B5936489
theorem B2638823 : Blo 1758080 2638823 := bstep (se 1 (by rfl) ⟨1979117, by rfl⟩ : syracuseStep 2638823 = 3958235) B3958235
theorem B5940215 : Blo 1758080 5940215 := bstep (se 1 (by rfl) ⟨4455161, by rfl⟩ : syracuseStep 5940215 = 8910323) B8910323
theorem B18056195 : Blo 1758080 18056195 := bstep (se 1 (by rfl) ⟨13542146, by rfl⟩ : syracuseStep 18056195 = 27084293) B27084293
theorem B12682277 : Blo 1758080 12682277 := bstep (se 4 (by rfl) ⟨1188963, by rfl⟩ : syracuseStep 12682277 = 2377927) B2377927
theorem B3957857 : Blo 1758080 3957857 := bstep (se 2 (by rfl) ⟨1484196, by rfl⟩ : syracuseStep 3957857 = 2968393) B2968393
theorem B7513235 : Blo 1758080 7513235 := bstep (se 1 (by rfl) ⟨5634926, by rfl⟩ : syracuseStep 7513235 = 11269853) B11269853
theorem B4752599 : Blo 1758080 4752599 := bstep (se 1 (by rfl) ⟨3564449, by rfl⟩ : syracuseStep 4752599 = 7128899) B7128899
theorem B2639081 : Blo 1758080 2639081 := bstep (se 2 (by rfl) ⟨989655, by rfl⟩ : syracuseStep 2639081 = 1979311) B1979311
theorem B6677747 : Blo 1758080 6677747 := bstep (se 1 (by rfl) ⟨5008310, by rfl⟩ : syracuseStep 6677747 = 10016621) B10016621
theorem B7513337 : Blo 1758080 7513337 := bstep (se 2 (by rfl) ⟨2817501, by rfl⟩ : syracuseStep 7513337 = 5635003) B5635003
theorem B2639135 : Blo 1758080 2639135 := bstep (se 1 (by rfl) ⟨1979351, by rfl⟩ : syracuseStep 2639135 = 3958703) B3958703
theorem B3958055 : Blo 1758080 3958055 := bstep (se 1 (by rfl) ⟨2968541, by rfl⟩ : syracuseStep 3958055 = 5937083) B5937083
theorem B14452091 : Blo 1758080 14452091 := bstep (se 1 (by rfl) ⟨10839068, by rfl⟩ : syracuseStep 14452091 = 21678137) B21678137
theorem B12682619 : Blo 1758080 12682619 := bstep (se 1 (by rfl) ⟨9511964, by rfl⟩ : syracuseStep 12682619 = 19023929) B19023929
theorem B4752827 : Blo 1758080 4752827 := bstep (se 1 (by rfl) ⟨3564620, by rfl⟩ : syracuseStep 4752827 = 7129241) B7129241
theorem B3007943 : Blo 1758080 3007943 := bstep (se 1 (by rfl) ⟨2255957, by rfl⟩ : syracuseStep 3007943 = 4511915) B4511915
theorem B2639303 : Blo 1758080 2639303 := bstep (se 1 (by rfl) ⟨1979477, by rfl⟩ : syracuseStep 2639303 = 3958955) B3958955
theorem B8906273 : Blo 1758080 8906273 := bstep (se 2 (by rfl) ⟨3339852, by rfl⟩ : syracuseStep 8906273 = 6679705) B6679705
theorem B3958433 : Blo 1758080 3958433 := bstep (se 2 (by rfl) ⟨1484412, by rfl⟩ : syracuseStep 3958433 = 2968825) B2968825
theorem B5007035 : Blo 1758080 5007035 := bstep (se 1 (by rfl) ⟨3755276, by rfl⟩ : syracuseStep 5007035 = 7510553) B7510553
theorem B2639657 : Blo 1758080 2639657 := bstep (se 2 (by rfl) ⟨989871, by rfl⟩ : syracuseStep 2639657 = 1979743) B1979743
theorem B2639663 : Blo 1758080 2639663 := bstep (se 1 (by rfl) ⟨1979747, by rfl⟩ : syracuseStep 2639663 = 3959495) B3959495
theorem B38037397 : Blo 1758080 38037397 := bstep (se 6 (by rfl) ⟨891501, by rfl⟩ : syracuseStep 38037397 = 1783003) B1783003
theorem B6342637 : Blo 1758080 6342637 := bstep (se 3 (by rfl) ⟨1189244, by rfl⟩ : syracuseStep 6342637 = 2378489) B2378489
theorem B3958793 : Blo 1758080 3958793 := bstep (se 2 (by rfl) ⟨1484547, by rfl⟩ : syracuseStep 3958793 = 2969095) B2969095
theorem B25356473 : Blo 1758080 25356473 := bstep (se 2 (by rfl) ⟨9508677, by rfl⟩ : syracuseStep 25356473 = 19017355) B19017355
theorem B4450585 : Blo 1758080 4450585 := bstep (se 2 (by rfl) ⟨1668969, by rfl⟩ : syracuseStep 4450585 = 3337939) B3337939
theorem B13535525 : Blo 1758080 13535525 := bstep (se 4 (by rfl) ⟨1268955, by rfl⟩ : syracuseStep 13535525 = 2537911) B2537911
theorem B15239461 : Blo 1758080 15239461 := bstep (se 4 (by rfl) ⟨1428699, by rfl⟩ : syracuseStep 15239461 = 2857399) B2857399
theorem B4450727 : Blo 1758080 4450727 := bstep (se 1 (by rfl) ⟨3338045, by rfl⟩ : syracuseStep 4450727 = 6676091) B6676091
theorem B3959207 : Blo 1758080 3959207 := bstep (se 1 (by rfl) ⟨2969405, by rfl⟩ : syracuseStep 3959207 = 5938811) B5938811
theorem B19016147 : Blo 1758080 19016147 := bstep (se 1 (by rfl) ⟨14262110, by rfl⟩ : syracuseStep 19016147 = 28524221) B28524221
theorem B3959315 : Blo 1758080 3959315 := bstep (se 1 (by rfl) ⟨2969486, by rfl⟩ : syracuseStep 3959315 = 5938973) B5938973
theorem B73206301 : Blo 1758080 73206301 := bstep (se 3 (by rfl) ⟨13726181, by rfl⟩ : syracuseStep 73206301 = 27452363) B27452363
theorem B1878599 : Blo 1758080 1878599 := bstep (se 1 (by rfl) ⟨1408949, by rfl⟩ : syracuseStep 1878599 = 2817899) B2817899
theorem B4450889 : Blo 1758080 4450889 := bstep (se 2 (by rfl) ⟨1669083, by rfl⟩ : syracuseStep 4450889 = 3338167) B3338167
theorem B3959369 : Blo 1758080 3959369 := bstep (se 2 (by rfl) ⟨1484763, by rfl⟩ : syracuseStep 3959369 = 2969527) B2969527
theorem B11274875 : Blo 1758080 11274875 := bstep (se 1 (by rfl) ⟨8456156, by rfl⟩ : syracuseStep 11274875 = 16912313) B16912313
theorem B9513611 : Blo 1758080 9513611 := bstep (se 1 (by rfl) ⟨7135208, by rfl⟩ : syracuseStep 9513611 = 14270417) B14270417
theorem B5933843 : Blo 1758080 5933843 := bstep (se 1 (by rfl) ⟨4450382, by rfl⟩ : syracuseStep 5933843 = 8900765) B8900765
theorem B2378651 : Blo 1758080 2378651 := bstep (se 1 (by rfl) ⟨1783988, by rfl⟩ : syracuseStep 2378651 = 3567977) B3567977
theorem B3566567 : Blo 1758080 3566567 := bstep (se 1 (by rfl) ⟨2674925, by rfl⟩ : syracuseStep 3566567 = 5349851) B5349851
theorem B3959783 : Blo 1758080 3959783 := bstep (se 1 (by rfl) ⟨2969837, by rfl⟩ : syracuseStep 3959783 = 5939675) B5939675
theorem B10021927 : Blo 1758080 10021927 := bstep (se 1 (by rfl) ⟨7516445, by rfl⟩ : syracuseStep 10021927 = 15032891) B15032891
theorem B7515251 : Blo 1758080 7515251 := bstep (se 1 (by rfl) ⟨5636438, by rfl⟩ : syracuseStep 7515251 = 11272877) B11272877
theorem B6679691 : Blo 1758080 6679691 := bstep (se 1 (by rfl) ⟨5009768, by rfl⟩ : syracuseStep 6679691 = 10019537) B10019537
theorem B13356251 : Blo 1758080 13356251 := bstep (se 1 (by rfl) ⟨10017188, by rfl⟩ : syracuseStep 13356251 = 20034377) B20034377
theorem B3009755 : Blo 1758080 3009755 := bstep (se 1 (by rfl) ⟨2257316, by rfl⟩ : syracuseStep 3009755 = 4514633) B4514633
theorem B8457539 : Blo 1758080 8457539 := bstep (se 1 (by rfl) ⟨6343154, by rfl⟩ : syracuseStep 8457539 = 12686309) B12686309
theorem B3960161 : Blo 1758080 3960161 := bstep (se 2 (by rfl) ⟨1485060, by rfl⟩ : syracuseStep 3960161 = 2970121) B2970121
theorem B21745025 : Blo 1758080 21745025 := bstep (se 2 (by rfl) ⟨8154384, by rfl⟩ : syracuseStep 21745025 = 16308769) B16308769
theorem B15035867 : Blo 1758080 15035867 := bstep (se 1 (by rfl) ⟨11276900, by rfl⟩ : syracuseStep 15035867 = 22553801) B22553801
theorem B59436509 : Blo 1758080 59436509 := bstep (se 3 (by rfl) ⟨11144345, by rfl⟩ : syracuseStep 59436509 = 22288691) B22288691
theorem B2969183 : Blo 1758080 2969183 := bstep (se 1 (by rfl) ⟨2226887, by rfl⟩ : syracuseStep 2969183 = 4453775) B4453775
theorem B3567199 : Blo 1758080 3567199 := bstep (se 1 (by rfl) ⟨2675399, by rfl⟩ : syracuseStep 3567199 = 5350799) B5350799
theorem B5934707 : Blo 1758080 5934707 := bstep (se 1 (by rfl) ⟨4451030, by rfl⟩ : syracuseStep 5934707 = 8902061) B8902061
theorem B8449697 : Blo 1758080 8449697 := bstep (se 2 (by rfl) ⟨3168636, by rfl⟩ : syracuseStep 8449697 = 6337273) B6337273
theorem B28544723 : Blo 1758080 28544723 := bstep (se 1 (by rfl) ⟨21408542, by rfl⟩ : syracuseStep 28544723 = 42817085) B42817085
theorem B1978159 : Blo 1758080 1978159 := bstep (se 1 (by rfl) ⟨1483619, by rfl⟩ : syracuseStep 1978159 = 2967239) B2967239
theorem B2969399 : Blo 1758080 2969399 := bstep (se 1 (by rfl) ⟨2227049, by rfl⟩ : syracuseStep 2969399 = 4454099) B4454099
theorem B8130377 : Blo 1758080 8130377 := bstep (se 2 (by rfl) ⟨3048891, by rfl⟩ : syracuseStep 8130377 = 6097783) B6097783
theorem B5934977 : Blo 1758080 5934977 := bstep (se 2 (by rfl) ⟨2225616, by rfl⟩ : syracuseStep 5934977 = 4451233) B4451233
theorem B1978267 : Blo 1758080 1978267 := bstep (se 1 (by rfl) ⟨1483700, by rfl⟩ : syracuseStep 1978267 = 2967401) B2967401
theorem B13545373 : Blo 1758080 13545373 := bstep (se 3 (by rfl) ⟨2539757, by rfl⟩ : syracuseStep 13545373 = 5079515) B5079515
theorem B274190341 : Blo 1758080 274190341 := bstep (se 4 (by rfl) ⟨25705344, by rfl⟩ : syracuseStep 274190341 = 51410689) B51410689
theorem B24080449 : Blo 1758080 24080449 := bstep (se 2 (by rfl) ⟨9030168, by rfl⟩ : syracuseStep 24080449 = 18060337) B18060337
theorem B1978663 : Blo 1758080 1978663 := bstep (se 1 (by rfl) ⟨1483997, by rfl⟩ : syracuseStep 1978663 = 2967995) B2967995
theorem B11276617 : Blo 1758080 11276617 := bstep (se 2 (by rfl) ⟨4228731, by rfl⟩ : syracuseStep 11276617 = 8457463) B8457463
theorem B3756395 : Blo 1758080 3756395 := bstep (se 1 (by rfl) ⟨2817296, by rfl⟩ : syracuseStep 3756395 = 5634593) B5634593
theorem B1978735 : Blo 1758080 1978735 := bstep (se 1 (by rfl) ⟨1484051, by rfl⟩ : syracuseStep 1978735 = 2968103) B2968103
theorem B6771119 : Blo 1758080 6771119 := bstep (se 1 (by rfl) ⟨5078339, by rfl⟩ : syracuseStep 6771119 = 10156679) B10156679
theorem B8901089 : Blo 1758080 8901089 := bstep (se 2 (by rfl) ⟨3337908, by rfl⟩ : syracuseStep 8901089 = 6675817) B6675817
theorem B4452833 : Blo 1758080 4452833 := bstep (se 2 (by rfl) ⟨1669812, by rfl⟩ : syracuseStep 4452833 = 3339625) B3339625
theorem B1978951 : Blo 1758080 1978951 := bstep (se 1 (by rfl) ⟨1484213, by rfl⟩ : syracuseStep 1978951 = 2968427) B2968427
theorem B5935787 : Blo 1758080 5935787 := bstep (se 1 (by rfl) ⟨4451840, by rfl⟩ : syracuseStep 5935787 = 8903681) B8903681
theorem B81236765 : Blo 1758080 81236765 := bstep (se 3 (by rfl) ⟨15231893, by rfl⟩ : syracuseStep 81236765 = 30463787) B30463787
theorem B1758107 : Blo 1758080 1758107 := bstep (se 1 (by rfl) ⟨1318580, by rfl⟩ : syracuseStep 1758107 = 2637161) B2637161
theorem B12039077 : Blo 1758080 12039077 := bstep (se 4 (by rfl) ⟨1128663, by rfl⟩ : syracuseStep 12039077 = 2257327) B2257327
theorem B1758159 : Blo 1758080 1758159 := bstep (se 1 (by rfl) ⟨1318619, by rfl⟩ : syracuseStep 1758159 = 2637239) B2637239
theorem B4453339 : Blo 1758080 4453339 := bstep (se 1 (by rfl) ⟨3340004, by rfl⟩ : syracuseStep 4453339 = 6680009) B6680009
theorem B1758183 : Blo 1758080 1758183 := bstep (se 1 (by rfl) ⟨1318637, by rfl⟩ : syracuseStep 1758183 = 2637275) B2637275
theorem B5010407 : Blo 1758080 5010407 := bstep (se 1 (by rfl) ⟨3757805, by rfl⟩ : syracuseStep 5010407 = 7515611) B7515611
theorem B8451161 : Blo 1758080 8451161 := bstep (se 2 (by rfl) ⟨3169185, by rfl⟩ : syracuseStep 8451161 = 6338371) B6338371
theorem B5936327 : Blo 1758080 5936327 := bstep (se 1 (by rfl) ⟨4452245, by rfl⟩ : syracuseStep 5936327 = 8904491) B8904491
theorem B1758495 : Blo 1758080 1758495 := bstep (se 1 (by rfl) ⟨1318871, by rfl⟩ : syracuseStep 1758495 = 2637743) B2637743
theorem B4453663 : Blo 1758080 4453663 := bstep (se 1 (by rfl) ⟨3340247, by rfl⟩ : syracuseStep 4453663 = 6680495) B6680495
theorem B9655595 : Blo 1758080 9655595 := bstep (se 1 (by rfl) ⟨7241696, by rfl⟩ : syracuseStep 9655595 = 14483393) B14483393
theorem B1758555 : Blo 1758080 1758555 := bstep (se 1 (by rfl) ⟨1318916, by rfl⟩ : syracuseStep 1758555 = 2637833) B2637833
theorem B10016095 : Blo 1758080 10016095 := bstep (se 1 (by rfl) ⟨7512071, by rfl⟩ : syracuseStep 10016095 = 15024143) B15024143
theorem B1758575 : Blo 1758080 1758575 := bstep (se 1 (by rfl) ⟨1318931, by rfl⟩ : syracuseStep 1758575 = 2637863) B2637863
theorem B1758631 : Blo 1758080 1758631 := bstep (se 1 (by rfl) ⟨1318973, by rfl⟩ : syracuseStep 1758631 = 2637947) B2637947
theorem B1979815 : Blo 1758080 1979815 := bstep (se 1 (by rfl) ⟨1484861, by rfl⟩ : syracuseStep 1979815 = 2969723) B2969723
theorem B17364461 : Blo 1758080 17364461 := bstep (se 3 (by rfl) ⟨3255836, by rfl⟩ : syracuseStep 17364461 = 6511673) B6511673
theorem B1758715 : Blo 1758080 1758715 := bstep (se 1 (by rfl) ⟨1319036, by rfl⟩ : syracuseStep 1758715 = 2638073) B2638073
theorem B1758783 : Blo 1758080 1758783 := bstep (se 1 (by rfl) ⟨1319087, by rfl⟩ : syracuseStep 1758783 = 2638175) B2638175
theorem B1758791 : Blo 1758080 1758791 := bstep (se 1 (by rfl) ⟨1319093, by rfl⟩ : syracuseStep 1758791 = 2638187) B2638187
theorem B1758943 : Blo 1758080 1758943 := bstep (se 1 (by rfl) ⟨1319207, by rfl⟩ : syracuseStep 1758943 = 2638415) B2638415
theorem B1759023 : Blo 1758080 1759023 := bstep (se 1 (by rfl) ⟨1319267, by rfl⟩ : syracuseStep 1759023 = 2638535) B2638535
theorem B1759131 : Blo 1758080 1759131 := bstep (se 1 (by rfl) ⟨1319348, by rfl⟩ : syracuseStep 1759131 = 2638697) B2638697
theorem B1759183 : Blo 1758080 1759183 := bstep (se 1 (by rfl) ⟨1319387, by rfl⟩ : syracuseStep 1759183 = 2638775) B2638775
theorem B1759207 : Blo 1758080 1759207 := bstep (se 1 (by rfl) ⟨1319405, by rfl⟩ : syracuseStep 1759207 = 2638811) B2638811
theorem B1759519 : Blo 1758080 1759519 := bstep (se 1 (by rfl) ⟨1319639, by rfl⟩ : syracuseStep 1759519 = 2639279) B2639279
theorem B2226523 : Blo 1758080 2226523 := bstep (se 1 (by rfl) ⟨1669892, by rfl⟩ : syracuseStep 2226523 = 3339785) B3339785
theorem B1759579 : Blo 1758080 1759579 := bstep (se 1 (by rfl) ⟨1319684, by rfl⟩ : syracuseStep 1759579 = 2639369) B2639369
theorem B4454747 : Blo 1758080 4454747 := bstep (se 1 (by rfl) ⟨3341060, by rfl⟩ : syracuseStep 4454747 = 6682121) B6682121
theorem B4225387 : Blo 1758080 4225387 := bstep (se 1 (by rfl) ⟨3169040, by rfl⟩ : syracuseStep 4225387 = 6338081) B6338081
theorem B1759599 : Blo 1758080 1759599 := bstep (se 1 (by rfl) ⟨1319699, by rfl⟩ : syracuseStep 1759599 = 2639399) B2639399
theorem B1759655 : Blo 1758080 1759655 := bstep (se 1 (by rfl) ⟨1319741, by rfl⟩ : syracuseStep 1759655 = 2639483) B2639483
theorem B4512251 : Blo 1758080 4512251 := bstep (se 1 (by rfl) ⟨3384188, by rfl⟩ : syracuseStep 4512251 = 6768377) B6768377
theorem B1759739 : Blo 1758080 1759739 := bstep (se 1 (by rfl) ⟨1319804, by rfl⟩ : syracuseStep 1759739 = 2639609) B2639609
theorem B19028519 : Blo 1758080 19028519 := bstep (se 1 (by rfl) ⟨14271389, by rfl⟩ : syracuseStep 19028519 = 28542779) B28542779
theorem B1759807 : Blo 1758080 1759807 := bstep (se 1 (by rfl) ⟨1319855, by rfl⟩ : syracuseStep 1759807 = 2639711) B2639711
theorem B1759815 : Blo 1758080 1759815 := bstep (se 1 (by rfl) ⟨1319861, by rfl⟩ : syracuseStep 1759815 = 2639723) B2639723
theorem B5937839 : Blo 1758080 5937839 := bstep (se 1 (by rfl) ⟨4453379, by rfl⟩ : syracuseStep 5937839 = 8906759) B8906759
theorem B8903357 : Blo 1758080 8903357 := bstep (se 3 (by rfl) ⟨1669379, by rfl⟩ : syracuseStep 8903357 = 3338759) B3338759
theorem B1759967 : Blo 1758080 1759967 := bstep (se 1 (by rfl) ⟨1319975, by rfl⟩ : syracuseStep 1759967 = 2639951) B2639951
theorem B1760047 : Blo 1758080 1760047 := bstep (se 1 (by rfl) ⟨1320035, by rfl⟩ : syracuseStep 1760047 = 2640071) B2640071
theorem B2112463 : Blo 1758080 2112463 := bstep (se 1 (by rfl) ⟨1584347, by rfl⟩ : syracuseStep 2112463 = 3168695) B3168695
theorem B5938163 : Blo 1758080 5938163 := bstep (se 1 (by rfl) ⟨4453622, by rfl⟩ : syracuseStep 5938163 = 8907245) B8907245
theorem B3169271 : Blo 1758080 3169271 := bstep (se 1 (by rfl) ⟨2376953, by rfl⟩ : syracuseStep 3169271 = 4753907) B4753907
theorem B3955751 : Blo 1758080 3955751 := bstep (se 1 (by rfl) ⟨2966813, by rfl⟩ : syracuseStep 3955751 = 5933627) B5933627
theorem B8453159 : Blo 1758080 8453159 := bstep (se 1 (by rfl) ⟨6339869, by rfl⟩ : syracuseStep 8453159 = 12679739) B12679739
theorem B3955931 : Blo 1758080 3955931 := bstep (se 1 (by rfl) ⟨2966948, by rfl⟩ : syracuseStep 3955931 = 5933897) B5933897
theorem B2227495 : Blo 1758080 2227495 := bstep (se 1 (by rfl) ⟨1670621, by rfl⟩ : syracuseStep 2227495 = 3341243) B3341243
theorem B2637179 : Blo 1758080 2637179 := bstep (se 1 (by rfl) ⟨1977884, by rfl⟩ : syracuseStep 2637179 = 3955769) B3955769
theorem B3956129 : Blo 1758080 3956129 := bstep (se 2 (by rfl) ⟨1483548, by rfl⟩ : syracuseStep 3956129 = 2967097) B2967097
theorem B2637305 : Blo 1758080 2637305 := bstep (se 2 (by rfl) ⟨988989, by rfl⟩ : syracuseStep 2637305 = 1977979) B1977979
theorem B7511561 : Blo 1758080 7511561 := bstep (se 2 (by rfl) ⟨2816835, by rfl⟩ : syracuseStep 7511561 = 5633671) B5633671
theorem B5938703 : Blo 1758080 5938703 := bstep (se 1 (by rfl) ⟨4454027, by rfl⟩ : syracuseStep 5938703 = 8908055) B8908055
theorem B4226617 : Blo 1758080 4226617 := bstep (se 2 (by rfl) ⟨1584981, by rfl⟩ : syracuseStep 4226617 = 3169963) B3169963
theorem B2637407 : Blo 1758080 2637407 := bstep (se 1 (by rfl) ⟨1978055, by rfl⟩ : syracuseStep 2637407 = 3956111) B3956111
theorem B2637623 : Blo 1758080 2637623 := bstep (se 1 (by rfl) ⟨1978217, by rfl⟩ : syracuseStep 2637623 = 3956435) B3956435
theorem B2817847 : Blo 1758080 2817847 := bstep (se 1 (by rfl) ⟨2113385, by rfl⟩ : syracuseStep 2817847 = 4226771) B4226771
theorem B3956687 : Blo 1758080 3956687 := bstep (se 1 (by rfl) ⟨2967515, by rfl⟩ : syracuseStep 3956687 = 5935031) B5935031
theorem B2638043 : Blo 1758080 2638043 := bstep (se 1 (by rfl) ⟨1978532, by rfl⟩ : syracuseStep 2638043 = 3957065) B3957065
theorem B2638055 : Blo 1758080 2638055 := bstep (se 1 (by rfl) ⟨1978541, by rfl⟩ : syracuseStep 2638055 = 3957083) B3957083
theorem B2638217 : Blo 1758080 2638217 := bstep (se 2 (by rfl) ⟨989331, by rfl⟩ : syracuseStep 2638217 = 1978663) B1978663
theorem B3957191 : Blo 1758080 3957191 := bstep (se 1 (by rfl) ⟨2967893, by rfl⟩ : syracuseStep 3957191 = 5935787) B5935787
theorem B2638313 : Blo 1758080 2638313 := bstep (se 2 (by rfl) ⟨989367, by rfl⟩ : syracuseStep 2638313 = 1978735) B1978735
theorem B54157843 : Blo 1758080 54157843 := bstep (se 1 (by rfl) ⟨40618382, by rfl⟩ : syracuseStep 54157843 = 81236765) B81236765
theorem B12673597 : Blo 1758080 12673597 := bstep (se 3 (by rfl) ⟨2376299, by rfl⟩ : syracuseStep 12673597 = 4752599) B4752599
theorem B2638439 : Blo 1758080 2638439 := bstep (se 1 (by rfl) ⟨1978829, by rfl⟩ : syracuseStep 2638439 = 3957659) B3957659
theorem B8454851 : Blo 1758080 8454851 := bstep (se 1 (by rfl) ⟨6341138, by rfl⟩ : syracuseStep 8454851 = 12682277) B12682277
theorem B97608401 : Blo 1758080 97608401 := bstep (se 2 (by rfl) ⟨36603150, by rfl⟩ : syracuseStep 97608401 = 73206301) B73206301
theorem B2638571 : Blo 1758080 2638571 := bstep (se 1 (by rfl) ⟨1978928, by rfl⟩ : syracuseStep 2638571 = 3957857) B3957857
theorem B2638601 : Blo 1758080 2638601 := bstep (se 2 (by rfl) ⟨989475, by rfl⟩ : syracuseStep 2638601 = 1978951) B1978951
theorem B3957551 : Blo 1758080 3957551 := bstep (se 1 (by rfl) ⟨2968163, by rfl⟩ : syracuseStep 3957551 = 5936327) B5936327
theorem B22553437 : Blo 1758080 22553437 := bstep (se 3 (by rfl) ⟨4228769, by rfl⟩ : syracuseStep 22553437 = 8457539) B8457539
theorem B2638703 : Blo 1758080 2638703 := bstep (se 1 (by rfl) ⟨1979027, by rfl⟩ : syracuseStep 2638703 = 3958055) B3958055
theorem B9634727 : Blo 1758080 9634727 := bstep (se 1 (by rfl) ⟨7226045, by rfl⟩ : syracuseStep 9634727 = 14452091) B14452091
theorem B8455079 : Blo 1758080 8455079 := bstep (se 1 (by rfl) ⟨6341309, by rfl⟩ : syracuseStep 8455079 = 12682619) B12682619
theorem B2638955 : Blo 1758080 2638955 := bstep (se 1 (by rfl) ⟨1979216, by rfl⟩ : syracuseStep 2638955 = 3958433) B3958433
theorem B18056317 : Blo 1758080 18056317 := bstep (se 3 (by rfl) ⟨3385559, by rfl⟩ : syracuseStep 18056317 = 6771119) B6771119
theorem B2639195 : Blo 1758080 2639195 := bstep (se 1 (by rfl) ⟨1979396, by rfl⟩ : syracuseStep 2639195 = 3958793) B3958793
theorem B13362569 : Blo 1758080 13362569 := bstep (se 2 (by rfl) ⟨5010963, by rfl⟩ : syracuseStep 13362569 = 10021927) B10021927
theorem B2967151 : Blo 1758080 2967151 := bstep (se 1 (by rfl) ⟨2225363, by rfl⟩ : syracuseStep 2967151 = 4450727) B4450727
theorem B2639471 : Blo 1758080 2639471 := bstep (se 1 (by rfl) ⟨1979603, by rfl⟩ : syracuseStep 2639471 = 3959207) B3959207
theorem B25372277 : Blo 1758080 25372277 := bstep (se 5 (by rfl) ⟨1189325, by rfl⟩ : syracuseStep 25372277 = 2378651) B2378651
theorem B2639543 : Blo 1758080 2639543 := bstep (se 1 (by rfl) ⟨1979657, by rfl⟩ : syracuseStep 2639543 = 3959315) B3959315
theorem B2967259 : Blo 1758080 2967259 := bstep (se 1 (by rfl) ⟨2225444, by rfl⟩ : syracuseStep 2967259 = 4450889) B4450889
theorem B2639579 : Blo 1758080 2639579 := bstep (se 1 (by rfl) ⟨1979684, by rfl⟩ : syracuseStep 2639579 = 3959369) B3959369
theorem B6342407 : Blo 1758080 6342407 := bstep (se 1 (by rfl) ⟨4756805, by rfl⟩ : syracuseStep 6342407 = 9513611) B9513611
theorem B3958559 : Blo 1758080 3958559 := bstep (se 1 (by rfl) ⟨2968919, by rfl⟩ : syracuseStep 3958559 = 5937839) B5937839
theorem B13354793 : Blo 1758080 13354793 := bstep (se 2 (by rfl) ⟨5008047, by rfl⟩ : syracuseStep 13354793 = 10016095) B10016095
theorem B2639753 : Blo 1758080 2639753 := bstep (se 2 (by rfl) ⟨989907, by rfl⟩ : syracuseStep 2639753 = 1979815) B1979815
theorem B2377711 : Blo 1758080 2377711 := bstep (se 1 (by rfl) ⟨1783283, by rfl⟩ : syracuseStep 2377711 = 3566567) B3566567
theorem B2639855 : Blo 1758080 2639855 := bstep (se 1 (by rfl) ⟨1979891, by rfl⟩ : syracuseStep 2639855 = 3959783) B3959783
theorem B3958775 : Blo 1758080 3958775 := bstep (se 1 (by rfl) ⟨2969081, by rfl⟩ : syracuseStep 3958775 = 5938163) B5938163
theorem B2640107 : Blo 1758080 2640107 := bstep (se 1 (by rfl) ⟨1980080, by rfl⟩ : syracuseStep 2640107 = 3960161) B3960161
theorem B5007707 : Blo 1758080 5007707 := bstep (se 1 (by rfl) ⟨3755780, by rfl⟩ : syracuseStep 5007707 = 7511561) B7511561
theorem B3959135 : Blo 1758080 3959135 := bstep (se 1 (by rfl) ⟨2969351, by rfl⟩ : syracuseStep 3959135 = 5938703) B5938703
theorem B8456849 : Blo 1758080 8456849 := bstep (se 2 (by rfl) ⟨3171318, by rfl⟩ : syracuseStep 8456849 = 6342637) B6342637
theorem B365587121 : Blo 1758080 365587121 := bstep (se 2 (by rfl) ⟨137095170, by rfl⟩ : syracuseStep 365587121 = 274190341) B274190341
theorem B32107265 : Blo 1758080 32107265 := bstep (se 2 (by rfl) ⟨12040224, by rfl⟩ : syracuseStep 32107265 = 24080449) B24080449
theorem B5934059 : Blo 1758080 5934059 := bstep (se 1 (by rfl) ⟨4450544, by rfl⟩ : syracuseStep 5934059 = 8901089) B8901089
theorem B2968555 : Blo 1758080 2968555 := bstep (se 1 (by rfl) ⟨2226416, by rfl⟩ : syracuseStep 2968555 = 4452833) B4452833
theorem B5934113 : Blo 1758080 5934113 := bstep (se 2 (by rfl) ⟨2225292, by rfl⟩ : syracuseStep 5934113 = 4450585) B4450585
theorem B4451375 : Blo 1758080 4451375 := bstep (se 1 (by rfl) ⟨3338531, by rfl⟩ : syracuseStep 4451375 = 6677063) B6677063
theorem B3959855 : Blo 1758080 3959855 := bstep (se 1 (by rfl) ⟨2969891, by rfl⟩ : syracuseStep 3959855 = 5939783) B5939783
theorem B20319281 : Blo 1758080 20319281 := bstep (se 2 (by rfl) ⟨7619730, by rfl⟩ : syracuseStep 20319281 = 15239461) B15239461
theorem B15035489 : Blo 1758080 15035489 := bstep (se 2 (by rfl) ⟨5638308, by rfl⟩ : syracuseStep 15035489 = 11276617) B11276617
theorem B2968697 : Blo 1758080 2968697 := bstep (se 2 (by rfl) ⟨1113261, by rfl⟩ : syracuseStep 2968697 = 2226523) B2226523
theorem B3960143 : Blo 1758080 3960143 := bstep (se 1 (by rfl) ⟨2970107, by rfl⟩ : syracuseStep 3960143 = 5940215) B5940215
theorem B12037463 : Blo 1758080 12037463 := bstep (se 1 (by rfl) ⟨9028097, by rfl⟩ : syracuseStep 12037463 = 18056195) B18056195
theorem B5008823 : Blo 1758080 5008823 := bstep (se 1 (by rfl) ⟨3756617, by rfl⟩ : syracuseStep 5008823 = 7513235) B7513235
theorem B4451831 : Blo 1758080 4451831 := bstep (se 1 (by rfl) ⟨3338873, by rfl⟩ : syracuseStep 4451831 = 6677747) B6677747
theorem B5008891 : Blo 1758080 5008891 := bstep (se 1 (by rfl) ⟨3756668, by rfl⟩ : syracuseStep 5008891 = 7513337) B7513337
theorem B15019769 : Blo 1758080 15019769 := bstep (se 2 (by rfl) ⟨5632413, by rfl⟩ : syracuseStep 15019769 = 11264827) B11264827
theorem B3338023 : Blo 1758080 3338023 := bstep (se 1 (by rfl) ⟨2503517, by rfl⟩ : syracuseStep 3338023 = 5007035) B5007035
theorem B16904315 : Blo 1758080 16904315 := bstep (se 1 (by rfl) ⟨12678236, by rfl⟩ : syracuseStep 16904315 = 25356473) B25356473
theorem B5009597 : Blo 1758080 5009597 := bstep (se 3 (by rfl) ⟨939299, by rfl⟩ : syracuseStep 5009597 = 1878599) B1878599
theorem B9023683 : Blo 1758080 9023683 := bstep (se 1 (by rfl) ⟨6767762, by rfl⟩ : syracuseStep 9023683 = 13535525) B13535525
theorem B2969831 : Blo 1758080 2969831 := bstep (se 1 (by rfl) ⟨2227373, by rfl⟩ : syracuseStep 2969831 = 4454747) B4454747
theorem B15028517 : Blo 1758080 15028517 := bstep (se 4 (by rfl) ⟨1408923, by rfl⟩ : syracuseStep 15028517 = 2817847) B2817847
theorem B12677431 : Blo 1758080 12677431 := bstep (se 1 (by rfl) ⟨9508073, by rfl⟩ : syracuseStep 12677431 = 19016147) B19016147
theorem B12685679 : Blo 1758080 12685679 := bstep (se 1 (by rfl) ⟨9514259, by rfl⟩ : syracuseStep 12685679 = 19028519) B19028519
theorem B2969993 : Blo 1758080 2969993 := bstep (se 2 (by rfl) ⟨1113747, by rfl⟩ : syracuseStep 2969993 = 2227495) B2227495
theorem B7516583 : Blo 1758080 7516583 := bstep (se 1 (by rfl) ⟨5637437, by rfl⟩ : syracuseStep 7516583 = 11274875) B11274875
theorem B22532525 : Blo 1758080 22532525 := bstep (se 3 (by rfl) ⟨4224848, by rfl⟩ : syracuseStep 22532525 = 8449697) B8449697
theorem B5935571 : Blo 1758080 5935571 := bstep (se 1 (by rfl) ⟨4451678, by rfl⟩ : syracuseStep 5935571 = 8903357) B8903357
theorem B5010167 : Blo 1758080 5010167 := bstep (se 1 (by rfl) ⟨3757625, by rfl⟩ : syracuseStep 5010167 = 7515251) B7515251
theorem B4453127 : Blo 1758080 4453127 := bstep (se 1 (by rfl) ⟨3339845, by rfl⟩ : syracuseStep 4453127 = 6679691) B6679691
theorem B4756265 : Blo 1758080 4756265 := bstep (se 2 (by rfl) ⟨1783599, by rfl⟩ : syracuseStep 4756265 = 3567199) B3567199
theorem B1758119 : Blo 1758080 1758119 := bstep (se 1 (by rfl) ⟨1318589, by rfl⟩ : syracuseStep 1758119 = 2637179) B2637179
theorem B14496683 : Blo 1758080 14496683 := bstep (se 1 (by rfl) ⟨10872512, by rfl⟩ : syracuseStep 14496683 = 21745025) B21745025
theorem B10023911 : Blo 1758080 10023911 := bstep (se 1 (by rfl) ⟨7517933, by rfl⟩ : syracuseStep 10023911 = 15035867) B15035867
theorem B1758203 : Blo 1758080 1758203 := bstep (se 1 (by rfl) ⟨1318652, by rfl⟩ : syracuseStep 1758203 = 2637305) B2637305
theorem B1758271 : Blo 1758080 1758271 := bstep (se 1 (by rfl) ⟨1318703, by rfl⟩ : syracuseStep 1758271 = 2637407) B2637407
theorem B1979455 : Blo 1758080 1979455 := bstep (se 1 (by rfl) ⟨1484591, by rfl⟩ : syracuseStep 1979455 = 2969183) B2969183
theorem B1758415 : Blo 1758080 1758415 := bstep (se 1 (by rfl) ⟨1318811, by rfl⟩ : syracuseStep 1758415 = 2637623) B2637623
theorem B1979599 : Blo 1758080 1979599 := bstep (se 1 (by rfl) ⟨1484699, by rfl⟩ : syracuseStep 1979599 = 2969399) B2969399
theorem B18060497 : Blo 1758080 18060497 := bstep (se 2 (by rfl) ⟨6772686, by rfl⟩ : syracuseStep 18060497 = 13545373) B13545373
theorem B5420251 : Blo 1758080 5420251 := bstep (se 1 (by rfl) ⟨4065188, by rfl⟩ : syracuseStep 5420251 = 8130377) B8130377
theorem B3757403 : Blo 1758080 3757403 := bstep (se 1 (by rfl) ⟨2818052, by rfl⟩ : syracuseStep 3757403 = 5636105) B5636105
theorem B1758619 : Blo 1758080 1758619 := bstep (se 1 (by rfl) ⟨1318964, by rfl⟩ : syracuseStep 1758619 = 2637929) B2637929
theorem B1758831 : Blo 1758080 1758831 := bstep (se 1 (by rfl) ⟨1319123, by rfl⟩ : syracuseStep 1758831 = 2638247) B2638247
theorem B1758887 : Blo 1758080 1758887 := bstep (se 1 (by rfl) ⟨1319165, by rfl⟩ : syracuseStep 1758887 = 2638331) B2638331
theorem B1758971 : Blo 1758080 1758971 := bstep (se 1 (by rfl) ⟨1319228, by rfl⟩ : syracuseStep 1758971 = 2638457) B2638457
theorem B1759007 : Blo 1758080 1759007 := bstep (se 1 (by rfl) ⟨1319255, by rfl⟩ : syracuseStep 1759007 = 2638511) B2638511
theorem B5633849 : Blo 1758080 5633849 := bstep (se 2 (by rfl) ⟨2112693, by rfl⟩ : syracuseStep 5633849 = 4225387) B4225387
theorem B1759039 : Blo 1758080 1759039 := bstep (se 1 (by rfl) ⟨1319279, by rfl⟩ : syracuseStep 1759039 = 2638559) B2638559
theorem B8026013 : Blo 1758080 8026013 := bstep (se 3 (by rfl) ⟨1504877, by rfl⟩ : syracuseStep 8026013 = 3009755) B3009755
theorem B8026051 : Blo 1758080 8026051 := bstep (se 1 (by rfl) ⟨6019538, by rfl⟩ : syracuseStep 8026051 = 12039077) B12039077
theorem B1759215 : Blo 1758080 1759215 := bstep (se 1 (by rfl) ⟨1319411, by rfl⟩ : syracuseStep 1759215 = 2638823) B2638823
theorem B3340271 : Blo 1758080 3340271 := bstep (se 1 (by rfl) ⟨2505203, by rfl⟩ : syracuseStep 3340271 = 5010407) B5010407
theorem B5634107 : Blo 1758080 5634107 := bstep (se 1 (by rfl) ⟨4225580, by rfl⟩ : syracuseStep 5634107 = 8451161) B8451161
theorem B1759387 : Blo 1758080 1759387 := bstep (se 1 (by rfl) ⟨1319540, by rfl⟩ : syracuseStep 1759387 = 2639081) B2639081
theorem B1759423 : Blo 1758080 1759423 := bstep (se 1 (by rfl) ⟨1319567, by rfl⟩ : syracuseStep 1759423 = 2639135) B2639135
theorem B6437063 : Blo 1758080 6437063 := bstep (se 1 (by rfl) ⟨4827797, by rfl⟩ : syracuseStep 6437063 = 9655595) B9655595
theorem B10017053 : Blo 1758080 10017053 := bstep (se 3 (by rfl) ⟨1878197, by rfl⟩ : syracuseStep 10017053 = 3756395) B3756395
theorem B3168551 : Blo 1758080 3168551 := bstep (se 1 (by rfl) ⟨2376413, by rfl⟩ : syracuseStep 3168551 = 4752827) B4752827
theorem B2005295 : Blo 1758080 2005295 := bstep (se 1 (by rfl) ⟨1503971, by rfl⟩ : syracuseStep 2005295 = 3007943) B3007943
theorem B1759535 : Blo 1758080 1759535 := bstep (se 1 (by rfl) ⟨1319651, by rfl⟩ : syracuseStep 1759535 = 2639303) B2639303
theorem B5937515 : Blo 1758080 5937515 := bstep (se 1 (by rfl) ⟨4453136, by rfl⟩ : syracuseStep 5937515 = 8906273) B8906273
theorem B1759771 : Blo 1758080 1759771 := bstep (se 1 (by rfl) ⟨1319828, by rfl⟩ : syracuseStep 1759771 = 2639657) B2639657
theorem B1759775 : Blo 1758080 1759775 := bstep (se 1 (by rfl) ⟨1319831, by rfl⟩ : syracuseStep 1759775 = 2639663) B2639663
theorem B158497357 : Blo 1758080 158497357 := bstep (se 3 (by rfl) ⟨29718254, by rfl⟩ : syracuseStep 158497357 = 59436509) B59436509
theorem B2816617 : Blo 1758080 2816617 := bstep (se 2 (by rfl) ⟨1056231, by rfl⟩ : syracuseStep 2816617 = 2112463) B2112463
theorem B5937785 : Blo 1758080 5937785 := bstep (se 2 (by rfl) ⟨2226669, by rfl⟩ : syracuseStep 5937785 = 4453339) B4453339
theorem B12032669 : Blo 1758080 12032669 := bstep (se 3 (by rfl) ⟨2256125, by rfl⟩ : syracuseStep 12032669 = 4512251) B4512251
theorem B5938217 : Blo 1758080 5938217 := bstep (se 2 (by rfl) ⟨2226831, by rfl⟩ : syracuseStep 5938217 = 4453663) B4453663
theorem B3955895 : Blo 1758080 3955895 := bstep (se 1 (by rfl) ⟨2966921, by rfl⟩ : syracuseStep 3955895 = 5933843) B5933843
theorem B22551797 : Blo 1758080 22551797 := bstep (se 5 (by rfl) ⟨1057115, by rfl⟩ : syracuseStep 22551797 = 2114231) B2114231
theorem B2112847 : Blo 1758080 2112847 := bstep (se 1 (by rfl) ⟨1584635, by rfl⟩ : syracuseStep 2112847 = 3169271) B3169271
theorem B2637167 : Blo 1758080 2637167 := bstep (se 1 (by rfl) ⟨1977875, by rfl⟩ : syracuseStep 2637167 = 3955751) B3955751
theorem B5635439 : Blo 1758080 5635439 := bstep (se 1 (by rfl) ⟨4226579, by rfl⟩ : syracuseStep 5635439 = 8453159) B8453159
theorem B5635489 : Blo 1758080 5635489 := bstep (se 2 (by rfl) ⟨2113308, by rfl⟩ : syracuseStep 5635489 = 4226617) B4226617
theorem B8904167 : Blo 1758080 8904167 := bstep (se 1 (by rfl) ⟨6678125, by rfl⟩ : syracuseStep 8904167 = 13356251) B13356251
theorem B2637287 : Blo 1758080 2637287 := bstep (se 1 (by rfl) ⟨1977965, by rfl⟩ : syracuseStep 2637287 = 3955931) B3955931
theorem B2637419 : Blo 1758080 2637419 := bstep (se 1 (by rfl) ⟨1978064, by rfl⟩ : syracuseStep 2637419 = 3956129) B3956129
theorem B2637545 : Blo 1758080 2637545 := bstep (se 2 (by rfl) ⟨989079, by rfl⟩ : syracuseStep 2637545 = 1978159) B1978159
theorem B3956471 : Blo 1758080 3956471 := bstep (se 1 (by rfl) ⟨2967353, by rfl⟩ : syracuseStep 3956471 = 5934707) B5934707
theorem B185220917 : Blo 1758080 185220917 := bstep (se 5 (by rfl) ⟨8682230, by rfl⟩ : syracuseStep 185220917 = 17364461) B17364461
theorem B19029815 : Blo 1758080 19029815 := bstep (se 1 (by rfl) ⟨14272361, by rfl⟩ : syracuseStep 19029815 = 28544723) B28544723
theorem B50716529 : Blo 1758080 50716529 := bstep (se 2 (by rfl) ⟨19018698, by rfl⟩ : syracuseStep 50716529 = 38037397) B38037397
theorem B2637689 : Blo 1758080 2637689 := bstep (se 2 (by rfl) ⟨989133, by rfl⟩ : syracuseStep 2637689 = 1978267) B1978267
theorem B3956651 : Blo 1758080 3956651 := bstep (se 1 (by rfl) ⟨2967488, by rfl⟩ : syracuseStep 3956651 = 5934977) B5934977
theorem B2637791 : Blo 1758080 2637791 := bstep (se 1 (by rfl) ⟨1978343, by rfl⟩ : syracuseStep 2637791 = 3956687) B3956687
theorem B10019011 : Blo 1758080 10019011 := bstep (se 1 (by rfl) ⟨7514258, by rfl⟩ : syracuseStep 10019011 = 15028517) B15028517
theorem B2638127 : Blo 1758080 2638127 := bstep (se 1 (by rfl) ⟨1978595, by rfl⟩ : syracuseStep 2638127 = 3957191) B3957191
theorem B3957047 : Blo 1758080 3957047 := bstep (se 1 (by rfl) ⟨2967785, by rfl⟩ : syracuseStep 3957047 = 5935571) B5935571
theorem B5636567 : Blo 1758080 5636567 := bstep (se 1 (by rfl) ⟨4227425, by rfl⟩ : syracuseStep 5636567 = 8454851) B8454851
theorem B3170843 : Blo 1758080 3170843 := bstep (se 1 (by rfl) ⟨2378132, by rfl⟩ : syracuseStep 3170843 = 4756265) B4756265
theorem B2638367 : Blo 1758080 2638367 := bstep (se 1 (by rfl) ⟨1978775, by rfl⟩ : syracuseStep 2638367 = 3957551) B3957551
theorem B6423151 : Blo 1758080 6423151 := bstep (se 1 (by rfl) ⟨4817363, by rfl⟩ : syracuseStep 6423151 = 9634727) B9634727
theorem B5636719 : Blo 1758080 5636719 := bstep (se 1 (by rfl) ⟨4227539, by rfl⟩ : syracuseStep 5636719 = 8455079) B8455079
theorem B211329809 : Blo 1758080 211329809 := bstep (se 2 (by rfl) ⟨79248678, by rfl⟩ : syracuseStep 211329809 = 158497357) B158497357
theorem B4228271 : Blo 1758080 4228271 := bstep (se 1 (by rfl) ⟨3171203, by rfl⟩ : syracuseStep 4228271 = 6342407) B6342407
theorem B2639039 : Blo 1758080 2639039 := bstep (se 1 (by rfl) ⟨1979279, by rfl⟩ : syracuseStep 2639039 = 3958559) B3958559
theorem B3958073 : Blo 1758080 3958073 := bstep (se 2 (by rfl) ⟨1484277, by rfl⟩ : syracuseStep 3958073 = 2968555) B2968555
theorem B2639183 : Blo 1758080 2639183 := bstep (se 1 (by rfl) ⟨1979387, by rfl⟩ : syracuseStep 2639183 = 3958775) B3958775
theorem B2639273 : Blo 1758080 2639273 := bstep (se 2 (by rfl) ⟨989727, by rfl⟩ : syracuseStep 2639273 = 1979455) B1979455
theorem B6678035 : Blo 1758080 6678035 := bstep (se 1 (by rfl) ⟨5008526, by rfl⟩ : syracuseStep 6678035 = 10017053) B10017053
theorem B2639423 : Blo 1758080 2639423 := bstep (se 1 (by rfl) ⟨1979567, by rfl⟩ : syracuseStep 2639423 = 3959135) B3959135
theorem B3958343 : Blo 1758080 3958343 := bstep (se 1 (by rfl) ⟨2968757, by rfl⟩ : syracuseStep 3958343 = 5937515) B5937515
theorem B2639465 : Blo 1758080 2639465 := bstep (se 2 (by rfl) ⟨989799, by rfl⟩ : syracuseStep 2639465 = 1979599) B1979599
theorem B7227001 : Blo 1758080 7227001 := bstep (se 2 (by rfl) ⟨2710125, by rfl⟩ : syracuseStep 7227001 = 5420251) B5420251
theorem B45074069 : Blo 1758080 45074069 := bstep (se 6 (by rfl) ⟨1056423, by rfl⟩ : syracuseStep 45074069 = 2112847) B2112847
theorem B3958523 : Blo 1758080 3958523 := bstep (se 1 (by rfl) ⟨2968892, by rfl⟩ : syracuseStep 3958523 = 5937785) B5937785
theorem B5637899 : Blo 1758080 5637899 := bstep (se 1 (by rfl) ⟨4228424, by rfl⟩ : syracuseStep 5637899 = 8456849) B8456849
theorem B7513985 : Blo 1758080 7513985 := bstep (se 2 (by rfl) ⟨2817744, by rfl⟩ : syracuseStep 7513985 = 5635489) B5635489
theorem B6678521 : Blo 1758080 6678521 := bstep (se 2 (by rfl) ⟨2504445, by rfl⟩ : syracuseStep 6678521 = 5008891) B5008891
theorem B3958811 : Blo 1758080 3958811 := bstep (se 1 (by rfl) ⟨2969108, by rfl⟩ : syracuseStep 3958811 = 5938217) B5938217
theorem B2967583 : Blo 1758080 2967583 := bstep (se 1 (by rfl) ⟨2225687, by rfl⟩ : syracuseStep 2967583 = 4451375) B4451375
theorem B2639903 : Blo 1758080 2639903 := bstep (se 1 (by rfl) ⟨1979927, by rfl⟩ : syracuseStep 2639903 = 3959855) B3959855
theorem B15034531 : Blo 1758080 15034531 := bstep (se 1 (by rfl) ⟨11275898, by rfl⟩ : syracuseStep 15034531 = 22551797) B22551797
theorem B2640095 : Blo 1758080 2640095 := bstep (se 1 (by rfl) ⟨1980071, by rfl⟩ : syracuseStep 2640095 = 3960143) B3960143
theorem B2967887 : Blo 1758080 2967887 := bstep (se 1 (by rfl) ⟨2225915, by rfl⟩ : syracuseStep 2967887 = 4451831) B4451831
theorem B4450697 : Blo 1758080 4450697 := bstep (se 2 (by rfl) ⟨1669011, by rfl⟩ : syracuseStep 4450697 = 3338023) B3338023
theorem B10013179 : Blo 1758080 10013179 := bstep (se 1 (by rfl) ⟨7509884, by rfl⟩ : syracuseStep 10013179 = 15019769) B15019769
theorem B123480611 : Blo 1758080 123480611 := bstep (se 1 (by rfl) ⟨92610458, by rfl⟩ : syracuseStep 123480611 = 185220917) B185220917
theorem B33811019 : Blo 1758080 33811019 := bstep (se 1 (by rfl) ⟨25358264, by rfl⟩ : syracuseStep 33811019 = 50716529) B50716529
theorem B10701401 : Blo 1758080 10701401 := bstep (se 2 (by rfl) ⟨4013025, by rfl⟩ : syracuseStep 10701401 = 8026051) B8026051
theorem B8457119 : Blo 1758080 8457119 := bstep (se 1 (by rfl) ⟨6342839, by rfl⟩ : syracuseStep 8457119 = 12685679) B12685679
theorem B16903241 : Blo 1758080 16903241 := bstep (se 2 (by rfl) ⟨6338715, by rfl⟩ : syracuseStep 16903241 = 12677431) B12677431
theorem B65072267 : Blo 1758080 65072267 := bstep (se 1 (by rfl) ⟨48804200, by rfl⟩ : syracuseStep 65072267 = 97608401) B97608401
theorem B2968751 : Blo 1758080 2968751 := bstep (se 1 (by rfl) ⟨2226563, by rfl⟩ : syracuseStep 2968751 = 4453127) B4453127
theorem B3755489 : Blo 1758080 3755489 := bstep (se 2 (by rfl) ⟨1408308, by rfl⟩ : syracuseStep 3755489 = 2816617) B2816617
theorem B8908379 : Blo 1758080 8908379 := bstep (se 1 (by rfl) ⟨6681284, by rfl⟩ : syracuseStep 8908379 = 13362569) B13362569
theorem B3755899 : Blo 1758080 3755899 := bstep (se 1 (by rfl) ⟨2816924, by rfl⟩ : syracuseStep 3755899 = 5633849) B5633849
theorem B3756071 : Blo 1758080 3756071 := bstep (se 1 (by rfl) ⟨2817053, by rfl⟩ : syracuseStep 3756071 = 5634107) B5634107
theorem B3338471 : Blo 1758080 3338471 := bstep (se 1 (by rfl) ⟨2503853, by rfl⟩ : syracuseStep 3338471 = 5007707) B5007707
theorem B243724747 : Blo 1758080 243724747 := bstep (se 1 (by rfl) ⟨182793560, by rfl⟩ : syracuseStep 243724747 = 365587121) B365587121
theorem B13546187 : Blo 1758080 13546187 := bstep (se 1 (by rfl) ⟨10159640, by rfl⟩ : syracuseStep 13546187 = 20319281) B20319281
theorem B10023659 : Blo 1758080 10023659 := bstep (se 1 (by rfl) ⟨7517744, by rfl⟩ : syracuseStep 10023659 = 15035489) B15035489
theorem B1979131 : Blo 1758080 1979131 := bstep (se 1 (by rfl) ⟨1484348, by rfl⟩ : syracuseStep 1979131 = 2968697) B2968697
theorem B8024975 : Blo 1758080 8024975 := bstep (se 1 (by rfl) ⟨6018731, by rfl⟩ : syracuseStep 8024975 = 12037463) B12037463
theorem B1758111 : Blo 1758080 1758111 := bstep (se 1 (by rfl) ⟨1318583, by rfl⟩ : syracuseStep 1758111 = 2637167) B2637167
theorem B3756959 : Blo 1758080 3756959 := bstep (se 1 (by rfl) ⟨2817719, by rfl⟩ : syracuseStep 3756959 = 5635439) B5635439
theorem B3339215 : Blo 1758080 3339215 := bstep (se 1 (by rfl) ⟨2504411, by rfl⟩ : syracuseStep 3339215 = 5008823) B5008823
theorem B1758191 : Blo 1758080 1758191 := bstep (se 1 (by rfl) ⟨1318643, by rfl⟩ : syracuseStep 1758191 = 2637287) B2637287
theorem B5936111 : Blo 1758080 5936111 := bstep (se 1 (by rfl) ⟨4452083, by rfl⟩ : syracuseStep 5936111 = 8904167) B8904167
theorem B1758279 : Blo 1758080 1758279 := bstep (se 1 (by rfl) ⟨1318709, by rfl⟩ : syracuseStep 1758279 = 2637419) B2637419
theorem B21402701 : Blo 1758080 21402701 := bstep (se 3 (by rfl) ⟨4013006, by rfl⟩ : syracuseStep 21402701 = 8026013) B8026013
theorem B1758363 : Blo 1758080 1758363 := bstep (se 1 (by rfl) ⟨1318772, by rfl⟩ : syracuseStep 1758363 = 2637545) B2637545
theorem B12686543 : Blo 1758080 12686543 := bstep (se 1 (by rfl) ⟨9514907, by rfl⟩ : syracuseStep 12686543 = 19029815) B19029815
theorem B1758459 : Blo 1758080 1758459 := bstep (se 1 (by rfl) ⟨1318844, by rfl⟩ : syracuseStep 1758459 = 2637689) B2637689
theorem B1758527 : Blo 1758080 1758527 := bstep (se 1 (by rfl) ⟨1318895, by rfl⟩ : syracuseStep 1758527 = 2637791) B2637791
theorem B11269543 : Blo 1758080 11269543 := bstep (se 1 (by rfl) ⟨8452157, by rfl⟩ : syracuseStep 11269543 = 16904315) B16904315
theorem B3339731 : Blo 1758080 3339731 := bstep (se 1 (by rfl) ⟨2504798, by rfl⟩ : syracuseStep 3339731 = 5009597) B5009597
theorem B1758695 : Blo 1758080 1758695 := bstep (se 1 (by rfl) ⟨1319021, by rfl⟩ : syracuseStep 1758695 = 2638043) B2638043
theorem B1758703 : Blo 1758080 1758703 := bstep (se 1 (by rfl) ⟨1319027, by rfl⟩ : syracuseStep 1758703 = 2638055) B2638055
theorem B1979887 : Blo 1758080 1979887 := bstep (se 1 (by rfl) ⟨1484915, by rfl⟩ : syracuseStep 1979887 = 2969831) B2969831
theorem B12031577 : Blo 1758080 12031577 := bstep (se 2 (by rfl) ⟨4511841, by rfl⟩ : syracuseStep 12031577 = 9023683) B9023683
theorem B1758811 : Blo 1758080 1758811 := bstep (se 1 (by rfl) ⟨1319108, by rfl⟩ : syracuseStep 1758811 = 2638217) B2638217
theorem B1979995 : Blo 1758080 1979995 := bstep (se 1 (by rfl) ⟨1484996, by rfl⟩ : syracuseStep 1979995 = 2969993) B2969993
theorem B5011055 : Blo 1758080 5011055 := bstep (se 1 (by rfl) ⟨3758291, by rfl⟩ : syracuseStep 5011055 = 7516583) B7516583
theorem B15021683 : Blo 1758080 15021683 := bstep (se 1 (by rfl) ⟨11266262, by rfl⟩ : syracuseStep 15021683 = 22532525) B22532525
theorem B1758875 : Blo 1758080 1758875 := bstep (se 1 (by rfl) ⟨1319156, by rfl⟩ : syracuseStep 1758875 = 2638313) B2638313
theorem B1758959 : Blo 1758080 1758959 := bstep (se 1 (by rfl) ⟨1319219, by rfl⟩ : syracuseStep 1758959 = 2638439) B2638439
theorem B1759047 : Blo 1758080 1759047 := bstep (se 1 (by rfl) ⟨1319285, by rfl⟩ : syracuseStep 1759047 = 2638571) B2638571
theorem B3340111 : Blo 1758080 3340111 := bstep (se 1 (by rfl) ⟨2505083, by rfl⟩ : syracuseStep 3340111 = 5010167) B5010167
theorem B1759067 : Blo 1758080 1759067 := bstep (se 1 (by rfl) ⟨1319300, by rfl⟩ : syracuseStep 1759067 = 2638601) B2638601
theorem B1759135 : Blo 1758080 1759135 := bstep (se 1 (by rfl) ⟨1319351, by rfl⟩ : syracuseStep 1759135 = 2638703) B2638703
theorem B6682607 : Blo 1758080 6682607 := bstep (se 1 (by rfl) ⟨5011955, by rfl⟩ : syracuseStep 6682607 = 10023911) B10023911
theorem B72210457 : Blo 1758080 72210457 := bstep (se 2 (by rfl) ⟨27078921, by rfl⟩ : syracuseStep 72210457 = 54157843) B54157843
theorem B1759303 : Blo 1758080 1759303 := bstep (se 1 (by rfl) ⟨1319477, by rfl⟩ : syracuseStep 1759303 = 2638955) B2638955
theorem B16898129 : Blo 1758080 16898129 := bstep (se 2 (by rfl) ⟨6336798, by rfl⟩ : syracuseStep 16898129 = 12673597) B12673597
theorem B5347453 : Blo 1758080 5347453 := bstep (se 3 (by rfl) ⟨1002647, by rfl⟩ : syracuseStep 5347453 = 2005295) B2005295
theorem B12040331 : Blo 1758080 12040331 := bstep (se 1 (by rfl) ⟨9030248, by rfl⟩ : syracuseStep 12040331 = 18060497) B18060497
theorem B2504935 : Blo 1758080 2504935 := bstep (se 1 (by rfl) ⟨1878701, by rfl⟩ : syracuseStep 2504935 = 3757403) B3757403
theorem B1759463 : Blo 1758080 1759463 := bstep (se 1 (by rfl) ⟨1319597, by rfl⟩ : syracuseStep 1759463 = 2639195) B2639195
theorem B1759647 : Blo 1758080 1759647 := bstep (se 1 (by rfl) ⟨1319735, by rfl⟩ : syracuseStep 1759647 = 2639471) B2639471
theorem B16914851 : Blo 1758080 16914851 := bstep (se 1 (by rfl) ⟨12686138, by rfl⟩ : syracuseStep 16914851 = 25372277) B25372277
theorem B1759695 : Blo 1758080 1759695 := bstep (se 1 (by rfl) ⟨1319771, by rfl⟩ : syracuseStep 1759695 = 2639543) B2639543
theorem B30071249 : Blo 1758080 30071249 := bstep (se 2 (by rfl) ⟨11276718, by rfl⟩ : syracuseStep 30071249 = 22553437) B22553437
theorem B1759719 : Blo 1758080 1759719 := bstep (se 1 (by rfl) ⟨1319789, by rfl⟩ : syracuseStep 1759719 = 2639579) B2639579
theorem B8903195 : Blo 1758080 8903195 := bstep (se 1 (by rfl) ⟨6677396, by rfl⟩ : syracuseStep 8903195 = 13354793) B13354793
theorem B1759835 : Blo 1758080 1759835 := bstep (se 1 (by rfl) ⟨1319876, by rfl⟩ : syracuseStep 1759835 = 2639753) B2639753
theorem B2226847 : Blo 1758080 2226847 := bstep (se 1 (by rfl) ⟨1670135, by rfl⟩ : syracuseStep 2226847 = 3340271) B3340271
theorem B1759903 : Blo 1758080 1759903 := bstep (se 1 (by rfl) ⟨1319927, by rfl⟩ : syracuseStep 1759903 = 2639855) B2639855
theorem B4291375 : Blo 1758080 4291375 := bstep (se 1 (by rfl) ⟨3218531, by rfl⟩ : syracuseStep 4291375 = 6437063) B6437063
theorem B1760071 : Blo 1758080 1760071 := bstep (se 1 (by rfl) ⟨1320053, by rfl⟩ : syracuseStep 1760071 = 2640107) B2640107
theorem B24075089 : Blo 1758080 24075089 := bstep (se 2 (by rfl) ⟨9028158, by rfl⟩ : syracuseStep 24075089 = 18056317) B18056317
theorem B2112367 : Blo 1758080 2112367 := bstep (se 1 (by rfl) ⟨1584275, by rfl⟩ : syracuseStep 2112367 = 3168551) B3168551
theorem B32087117 : Blo 1758080 32087117 := bstep (se 3 (by rfl) ⟨6016334, by rfl⟩ : syracuseStep 32087117 = 12032669) B12032669
theorem B21404843 : Blo 1758080 21404843 := bstep (se 1 (by rfl) ⟨16053632, by rfl⟩ : syracuseStep 21404843 = 32107265) B32107265
theorem B3956039 : Blo 1758080 3956039 := bstep (se 1 (by rfl) ⟨2967029, by rfl⟩ : syracuseStep 3956039 = 5934059) B5934059
theorem B3956075 : Blo 1758080 3956075 := bstep (se 1 (by rfl) ⟨2967056, by rfl⟩ : syracuseStep 3956075 = 5934113) B5934113
theorem B2637263 : Blo 1758080 2637263 := bstep (se 1 (by rfl) ⟨1977947, by rfl⟩ : syracuseStep 2637263 = 3955895) B3955895
theorem B3956201 : Blo 1758080 3956201 := bstep (se 2 (by rfl) ⟨1483575, by rfl⟩ : syracuseStep 3956201 = 2967151) B2967151
theorem B3956345 : Blo 1758080 3956345 := bstep (se 2 (by rfl) ⟨1483629, by rfl⟩ : syracuseStep 3956345 = 2967259) B2967259
theorem B38657821 : Blo 1758080 38657821 := bstep (se 3 (by rfl) ⟨7248341, by rfl⟩ : syracuseStep 38657821 = 14496683) B14496683
theorem B2637647 : Blo 1758080 2637647 := bstep (se 1 (by rfl) ⟨1978235, by rfl⟩ : syracuseStep 2637647 = 3956471) B3956471
theorem B2637767 : Blo 1758080 2637767 := bstep (se 1 (by rfl) ⟨1978325, by rfl⟩ : syracuseStep 2637767 = 3956651) B3956651
theorem B3170281 : Blo 1758080 3170281 := bstep (se 2 (by rfl) ⟨1188855, by rfl⟩ : syracuseStep 3170281 = 2377711) B2377711
theorem B96280609 : Blo 1758080 96280609 := bstep (se 2 (by rfl) ⟨36105228, by rfl⟩ : syracuseStep 96280609 = 72210457) B72210457
theorem B3956777 : Blo 1758080 3956777 := bstep (se 2 (by rfl) ⟨1483791, by rfl⟩ : syracuseStep 3956777 = 2967583) B2967583
theorem B85565645 : Blo 1758080 85565645 := bstep (se 3 (by rfl) ⟨16043558, by rfl⟩ : syracuseStep 85565645 = 32087117) B32087117
theorem B2638031 : Blo 1758080 2638031 := bstep (se 1 (by rfl) ⟨1978523, by rfl⟩ : syracuseStep 2638031 = 3957047) B3957047
theorem B20046041 : Blo 1758080 20046041 := bstep (se 2 (by rfl) ⟨7517265, by rfl⟩ : syracuseStep 20046041 = 15034531) B15034531
theorem B2113895 : Blo 1758080 2113895 := bstep (se 1 (by rfl) ⟨1585421, by rfl⟩ : syracuseStep 2113895 = 3170843) B3170843
theorem B140886539 : Blo 1758080 140886539 := bstep (se 1 (by rfl) ⟨105664904, by rfl⟩ : syracuseStep 140886539 = 211329809) B211329809
theorem B5349983 : Blo 1758080 5349983 := bstep (se 1 (by rfl) ⟨4012487, by rfl⟩ : syracuseStep 5349983 = 8024975) B8024975
theorem B38544005 : Blo 1758080 38544005 := bstep (se 4 (by rfl) ⟨3613500, by rfl⟩ : syracuseStep 38544005 = 7227001) B7227001
theorem B3957407 : Blo 1758080 3957407 := bstep (se 1 (by rfl) ⟨2968055, by rfl⟩ : syracuseStep 3957407 = 5936111) B5936111
theorem B2818847 : Blo 1758080 2818847 := bstep (se 1 (by rfl) ⟨2114135, by rfl⟩ : syracuseStep 2818847 = 4228271) B4228271
theorem B2638715 : Blo 1758080 2638715 := bstep (se 1 (by rfl) ⟨1979036, by rfl⟩ : syracuseStep 2638715 = 3958073) B3958073
theorem B2638841 : Blo 1758080 2638841 := bstep (se 2 (by rfl) ⟨989565, by rfl⟩ : syracuseStep 2638841 = 1979131) B1979131
theorem B2638895 : Blo 1758080 2638895 := bstep (se 1 (by rfl) ⟨1979171, by rfl⟩ : syracuseStep 2638895 = 3958343) B3958343
theorem B8021051 : Blo 1758080 8021051 := bstep (se 1 (by rfl) ⟨6015788, by rfl⟩ : syracuseStep 8021051 = 12031577) B12031577
theorem B30049379 : Blo 1758080 30049379 := bstep (se 1 (by rfl) ⟨22537034, by rfl⟩ : syracuseStep 30049379 = 45074069) B45074069
theorem B2639015 : Blo 1758080 2639015 := bstep (se 1 (by rfl) ⟨1979261, by rfl⟩ : syracuseStep 2639015 = 3958523) B3958523
theorem B8905949 : Blo 1758080 8905949 := bstep (se 3 (by rfl) ⟨1669865, by rfl⟩ : syracuseStep 8905949 = 3339731) B3339731
theorem B2639207 : Blo 1758080 2639207 := bstep (se 1 (by rfl) ⟨1979405, by rfl⟩ : syracuseStep 2639207 = 3958811) B3958811
theorem B11265419 : Blo 1758080 11265419 := bstep (se 1 (by rfl) ⟨8449064, by rfl⟩ : syracuseStep 11265419 = 16898129) B16898129
theorem B2967131 : Blo 1758080 2967131 := bstep (se 1 (by rfl) ⟨2225348, by rfl⟩ : syracuseStep 2967131 = 4450697) B4450697
theorem B20047499 : Blo 1758080 20047499 := bstep (se 1 (by rfl) ⟨15035624, by rfl⟩ : syracuseStep 20047499 = 30071249) B30071249
theorem B15026057 : Blo 1758080 15026057 := bstep (se 2 (by rfl) ⟨5634771, by rfl⟩ : syracuseStep 15026057 = 11269543) B11269543
theorem B16050059 : Blo 1758080 16050059 := bstep (se 1 (by rfl) ⟨12037544, by rfl⟩ : syracuseStep 16050059 = 24075089) B24075089
theorem B5638079 : Blo 1758080 5638079 := bstep (se 1 (by rfl) ⟨4228559, by rfl⟩ : syracuseStep 5638079 = 8457119) B8457119
theorem B20031461 : Blo 1758080 20031461 := bstep (se 4 (by rfl) ⟨1877949, by rfl⟩ : syracuseStep 20031461 = 3755899) B3755899
theorem B2639849 : Blo 1758080 2639849 := bstep (se 2 (by rfl) ⟨989943, by rfl⟩ : syracuseStep 2639849 = 1979887) B1979887
theorem B2639993 : Blo 1758080 2639993 := bstep (se 2 (by rfl) ⟨989997, by rfl⟩ : syracuseStep 2639993 = 1979995) B1979995
theorem B7129937 : Blo 1758080 7129937 := bstep (se 2 (by rfl) ⟨2673726, by rfl⟩ : syracuseStep 7129937 = 5347453) B5347453
theorem B32107549 : Blo 1758080 32107549 := bstep (se 3 (by rfl) ⟨6020165, by rfl⟩ : syracuseStep 32107549 = 12040331) B12040331
theorem B9030791 : Blo 1758080 9030791 := bstep (se 1 (by rfl) ⟨6773093, by rfl⟩ : syracuseStep 9030791 = 13546187) B13546187
theorem B8457695 : Blo 1758080 8457695 := bstep (se 1 (by rfl) ⟨6343271, by rfl⟩ : syracuseStep 8457695 = 12686543) B12686543
theorem B8564201 : Blo 1758080 8564201 := bstep (se 2 (by rfl) ⟨3211575, by rfl⟩ : syracuseStep 8564201 = 6423151) B6423151
theorem B2969129 : Blo 1758080 2969129 := bstep (se 2 (by rfl) ⟨1113423, by rfl⟩ : syracuseStep 2969129 = 2226847) B2226847
theorem B4452023 : Blo 1758080 4452023 := bstep (se 1 (by rfl) ⟨3339017, by rfl⟩ : syracuseStep 4452023 = 6678035) B6678035
theorem B5721833 : Blo 1758080 5721833 := bstep (se 2 (by rfl) ⟨2145687, by rfl⟩ : syracuseStep 5721833 = 4291375) B4291375
theorem B10014455 : Blo 1758080 10014455 := bstep (se 1 (by rfl) ⟨7510841, by rfl⟩ : syracuseStep 10014455 = 15021683) B15021683
theorem B10014637 : Blo 1758080 10014637 := bstep (se 3 (by rfl) ⟨1877744, by rfl⟩ : syracuseStep 10014637 = 3755489) B3755489
theorem B4452347 : Blo 1758080 4452347 := bstep (se 1 (by rfl) ⟨3339260, by rfl⟩ : syracuseStep 4452347 = 6678521) B6678521
theorem B1978591 : Blo 1758080 1978591 := bstep (se 1 (by rfl) ⟨1483943, by rfl⟩ : syracuseStep 1978591 = 2967887) B2967887
theorem B28537069 : Blo 1758080 28537069 := bstep (se 3 (by rfl) ⟨5350700, by rfl⟩ : syracuseStep 28537069 = 10701401) B10701401
theorem B11276567 : Blo 1758080 11276567 := bstep (se 1 (by rfl) ⟨8457425, by rfl⟩ : syracuseStep 11276567 = 16914851) B16914851
theorem B5935463 : Blo 1758080 5935463 := bstep (se 1 (by rfl) ⟨4451597, by rfl⟩ : syracuseStep 5935463 = 8903195) B8903195
theorem B22540679 : Blo 1758080 22540679 := bstep (se 1 (by rfl) ⟨16905509, by rfl⟩ : syracuseStep 22540679 = 33811019) B33811019
theorem B11268827 : Blo 1758080 11268827 := bstep (se 1 (by rfl) ⟨8451620, by rfl⟩ : syracuseStep 11268827 = 16903241) B16903241
theorem B43381511 : Blo 1758080 43381511 := bstep (se 1 (by rfl) ⟨32536133, by rfl⟩ : syracuseStep 43381511 = 65072267) B65072267
theorem B1979167 : Blo 1758080 1979167 := bstep (se 1 (by rfl) ⟨1484375, by rfl⟩ : syracuseStep 1979167 = 2968751) B2968751
theorem B1758175 : Blo 1758080 1758175 := bstep (se 1 (by rfl) ⟨1318631, by rfl⟩ : syracuseStep 1758175 = 2637263) B2637263
theorem B4453481 : Blo 1758080 4453481 := bstep (se 2 (by rfl) ⟨1670055, by rfl⟩ : syracuseStep 4453481 = 3340111) B3340111
theorem B1758431 : Blo 1758080 1758431 := bstep (se 1 (by rfl) ⟨1318823, by rfl⟩ : syracuseStep 1758431 = 2637647) B2637647
theorem B1758511 : Blo 1758080 1758511 := bstep (se 1 (by rfl) ⟨1318883, by rfl⟩ : syracuseStep 1758511 = 2637767) B2637767
theorem B2504047 : Blo 1758080 2504047 := bstep (se 1 (by rfl) ⟨1878035, by rfl⟩ : syracuseStep 2504047 = 3756071) B3756071
theorem B2225647 : Blo 1758080 2225647 := bstep (se 1 (by rfl) ⟨1669235, by rfl⟩ : syracuseStep 2225647 = 3338471) B3338471
theorem B1758751 : Blo 1758080 1758751 := bstep (se 1 (by rfl) ⟨1319063, by rfl⟩ : syracuseStep 1758751 = 2638127) B2638127
theorem B13358681 : Blo 1758080 13358681 := bstep (se 2 (by rfl) ⟨5009505, by rfl⟩ : syracuseStep 13358681 = 10019011) B10019011
theorem B3757711 : Blo 1758080 3757711 := bstep (se 1 (by rfl) ⟨2818283, by rfl⟩ : syracuseStep 3757711 = 5636567) B5636567
theorem B1758911 : Blo 1758080 1758911 := bstep (se 1 (by rfl) ⟨1319183, by rfl⟩ : syracuseStep 1758911 = 2638367) B2638367
theorem B6682439 : Blo 1758080 6682439 := bstep (se 1 (by rfl) ⟨5011829, by rfl⟩ : syracuseStep 6682439 = 10023659) B10023659
theorem B30062501 : Blo 1758080 30062501 := bstep (se 4 (by rfl) ⟨2818359, by rfl⟩ : syracuseStep 30062501 = 5636719) B5636719
theorem B324966329 : Blo 1758080 324966329 := bstep (se 2 (by rfl) ⟨121862373, by rfl⟩ : syracuseStep 324966329 = 243724747) B243724747
theorem B2504639 : Blo 1758080 2504639 := bstep (se 1 (by rfl) ⟨1878479, by rfl⟩ : syracuseStep 2504639 = 3756959) B3756959
theorem B2226143 : Blo 1758080 2226143 := bstep (se 1 (by rfl) ⟨1669607, by rfl⟩ : syracuseStep 2226143 = 3339215) B3339215
theorem B13350905 : Blo 1758080 13350905 := bstep (se 2 (by rfl) ⟨5006589, by rfl⟩ : syracuseStep 13350905 = 10013179) B10013179
theorem B14268467 : Blo 1758080 14268467 := bstep (se 1 (by rfl) ⟨10701350, by rfl⟩ : syracuseStep 14268467 = 21402701) B21402701
theorem B1759359 : Blo 1758080 1759359 := bstep (se 1 (by rfl) ⟨1319519, by rfl⟩ : syracuseStep 1759359 = 2639039) B2639039
theorem B1759455 : Blo 1758080 1759455 := bstep (se 1 (by rfl) ⟨1319591, by rfl⟩ : syracuseStep 1759455 = 2639183) B2639183
theorem B1759515 : Blo 1758080 1759515 := bstep (se 1 (by rfl) ⟨1319636, by rfl⟩ : syracuseStep 1759515 = 2639273) B2639273
theorem B1759615 : Blo 1758080 1759615 := bstep (se 1 (by rfl) ⟨1319711, by rfl⟩ : syracuseStep 1759615 = 2639423) B2639423
theorem B1759643 : Blo 1758080 1759643 := bstep (se 1 (by rfl) ⟨1319732, by rfl⟩ : syracuseStep 1759643 = 2639465) B2639465
theorem B3340703 : Blo 1758080 3340703 := bstep (se 1 (by rfl) ⟨2505527, by rfl⟩ : syracuseStep 3340703 = 5011055) B5011055
theorem B2816489 : Blo 1758080 2816489 := bstep (se 2 (by rfl) ⟨1056183, by rfl⟩ : syracuseStep 2816489 = 2112367) B2112367
theorem B3758599 : Blo 1758080 3758599 := bstep (se 1 (by rfl) ⟨2818949, by rfl⟩ : syracuseStep 3758599 = 5637899) B5637899
theorem B13359653 : Blo 1758080 13359653 := bstep (se 4 (by rfl) ⟨1252467, by rfl⟩ : syracuseStep 13359653 = 2504935) B2504935
theorem B4455071 : Blo 1758080 4455071 := bstep (se 1 (by rfl) ⟨3341303, by rfl⟩ : syracuseStep 4455071 = 6682607) B6682607
theorem B1759935 : Blo 1758080 1759935 := bstep (se 1 (by rfl) ⟨1319951, by rfl⟩ : syracuseStep 1759935 = 2639903) B2639903
theorem B1760063 : Blo 1758080 1760063 := bstep (se 1 (by rfl) ⟨1320047, by rfl⟩ : syracuseStep 1760063 = 2640095) B2640095
theorem B82320407 : Blo 1758080 82320407 := bstep (se 1 (by rfl) ⟨61740305, by rfl⟩ : syracuseStep 82320407 = 123480611) B123480611
theorem B14269895 : Blo 1758080 14269895 := bstep (se 1 (by rfl) ⟨10702421, by rfl⟩ : syracuseStep 14269895 = 21404843) B21404843
theorem B2637359 : Blo 1758080 2637359 := bstep (se 1 (by rfl) ⟨1978019, by rfl⟩ : syracuseStep 2637359 = 3956039) B3956039
theorem B2637383 : Blo 1758080 2637383 := bstep (se 1 (by rfl) ⟨1978037, by rfl⟩ : syracuseStep 2637383 = 3956075) B3956075
theorem B2637467 : Blo 1758080 2637467 := bstep (se 1 (by rfl) ⟨1978100, by rfl⟩ : syracuseStep 2637467 = 3956201) B3956201
theorem B20037293 : Blo 1758080 20037293 := bstep (se 3 (by rfl) ⟨3756992, by rfl⟩ : syracuseStep 20037293 = 7513985) B7513985
theorem B51543761 : Blo 1758080 51543761 := bstep (se 2 (by rfl) ⟨19328910, by rfl⟩ : syracuseStep 51543761 = 38657821) B38657821
theorem B5938919 : Blo 1758080 5938919 := bstep (se 1 (by rfl) ⟨4454189, by rfl⟩ : syracuseStep 5938919 = 8908379) B8908379
theorem B2637563 : Blo 1758080 2637563 := bstep (se 1 (by rfl) ⟨1978172, by rfl⟩ : syracuseStep 2637563 = 3956345) B3956345
theorem B4227041 : Blo 1758080 4227041 := bstep (se 2 (by rfl) ⟨1585140, by rfl⟩ : syracuseStep 4227041 = 3170281) B3170281
theorem B2637851 : Blo 1758080 2637851 := bstep (se 1 (by rfl) ⟨1978388, by rfl⟩ : syracuseStep 2637851 = 3956777) B3956777
theorem B3956975 : Blo 1758080 3956975 := bstep (se 1 (by rfl) ⟨2967731, by rfl⟩ : syracuseStep 3956975 = 5935463) B5935463
theorem B2638121 : Blo 1758080 2638121 := bstep (se 2 (by rfl) ⟨989295, by rfl⟩ : syracuseStep 2638121 = 1978591) B1978591
theorem B2638271 : Blo 1758080 2638271 := bstep (se 1 (by rfl) ⟨1978703, by rfl⟩ : syracuseStep 2638271 = 3957407) B3957407
theorem B7512551 : Blo 1758080 7512551 := bstep (se 1 (by rfl) ⟨5634413, by rfl⟩ : syracuseStep 7512551 = 11268827) B11268827
theorem B5637053 : Blo 1758080 5637053 := bstep (se 3 (by rfl) ⟨1056947, by rfl⟩ : syracuseStep 5637053 = 2113895) B2113895
theorem B2638889 : Blo 1758080 2638889 := bstep (se 2 (by rfl) ⟨989583, by rfl⟩ : syracuseStep 2638889 = 1979167) B1979167
theorem B8905787 : Blo 1758080 8905787 := bstep (se 1 (by rfl) ⟨6679340, by rfl⟩ : syracuseStep 8905787 = 13358681) B13358681
theorem B10700039 : Blo 1758080 10700039 := bstep (se 1 (by rfl) ⟨8025029, by rfl⟩ : syracuseStep 10700039 = 16050059) B16050059
theorem B13354307 : Blo 1758080 13354307 := bstep (se 1 (by rfl) ⟨10015730, by rfl⟩ : syracuseStep 13354307 = 20031461) B20031461
theorem B9512311 : Blo 1758080 9512311 := bstep (se 1 (by rfl) ⟨7134233, by rfl⟩ : syracuseStep 9512311 = 14268467) B14268467
theorem B8906435 : Blo 1758080 8906435 := bstep (se 1 (by rfl) ⟨6679826, by rfl⟩ : syracuseStep 8906435 = 13359653) B13359653
theorem B4753291 : Blo 1758080 4753291 := bstep (se 1 (by rfl) ⟨3564968, by rfl⟩ : syracuseStep 4753291 = 7129937) B7129937
theorem B2967529 : Blo 1758080 2967529 := bstep (se 2 (by rfl) ⟨1112823, by rfl⟩ : syracuseStep 2967529 = 2225647) B2225647
theorem B54880271 : Blo 1758080 54880271 := bstep (se 1 (by rfl) ⟨41160203, by rfl⟩ : syracuseStep 54880271 = 82320407) B82320407
theorem B9513263 : Blo 1758080 9513263 := bstep (se 1 (by rfl) ⟨7134947, by rfl⟩ : syracuseStep 9513263 = 14269895) B14269895
theorem B5638463 : Blo 1758080 5638463 := bstep (se 1 (by rfl) ⟨4228847, by rfl⟩ : syracuseStep 5638463 = 8457695) B8457695
theorem B2968015 : Blo 1758080 2968015 := bstep (se 1 (by rfl) ⟨2226011, by rfl⟩ : syracuseStep 2968015 = 4452023) B4452023
theorem B3959279 : Blo 1758080 3959279 := bstep (se 1 (by rfl) ⟨2969459, by rfl⟩ : syracuseStep 3959279 = 5938919) B5938919
theorem B6679037 : Blo 1758080 6679037 := bstep (se 3 (by rfl) ⟨1252319, by rfl⟩ : syracuseStep 6679037 = 2504639) B2504639
theorem B2968231 : Blo 1758080 2968231 := bstep (se 1 (by rfl) ⟨2226173, by rfl⟩ : syracuseStep 2968231 = 4452347) B4452347
theorem B57043763 : Blo 1758080 57043763 := bstep (se 1 (by rfl) ⟨42782822, by rfl⟩ : syracuseStep 57043763 = 85565645) B85565645
theorem B13364027 : Blo 1758080 13364027 := bstep (se 1 (by rfl) ⟨10023020, by rfl⟩ : syracuseStep 13364027 = 20046041) B20046041
theorem B15027119 : Blo 1758080 15027119 := bstep (se 1 (by rfl) ⟨11270339, by rfl⟩ : syracuseStep 15027119 = 22540679) B22540679
theorem B93924359 : Blo 1758080 93924359 := bstep (se 1 (by rfl) ⟨70443269, by rfl⟩ : syracuseStep 93924359 = 140886539) B140886539
theorem B28921007 : Blo 1758080 28921007 := bstep (se 1 (by rfl) ⟨21690755, by rfl⟩ : syracuseStep 28921007 = 43381511) B43381511
theorem B20032919 : Blo 1758080 20032919 := bstep (se 1 (by rfl) ⟨15024689, by rfl⟩ : syracuseStep 20032919 = 30049379) B30049379
theorem B2968987 : Blo 1758080 2968987 := bstep (se 1 (by rfl) ⟨2226740, by rfl⟩ : syracuseStep 2968987 = 4453481) B4453481
theorem B1978087 : Blo 1758080 1978087 := bstep (se 1 (by rfl) ⟨1483565, by rfl⟩ : syracuseStep 1978087 = 2967131) B2967131
theorem B8908541 : Blo 1758080 8908541 := bstep (se 3 (by rfl) ⟨1670351, by rfl⟩ : syracuseStep 8908541 = 3340703) B3340703
theorem B13364999 : Blo 1758080 13364999 := bstep (se 1 (by rfl) ⟨10023749, by rfl⟩ : syracuseStep 13364999 = 20047499) B20047499
theorem B20041667 : Blo 1758080 20041667 := bstep (se 1 (by rfl) ⟨15031250, by rfl⟩ : syracuseStep 20041667 = 30062501) B30062501
theorem B8900603 : Blo 1758080 8900603 := bstep (se 1 (by rfl) ⟨6675452, by rfl⟩ : syracuseStep 8900603 = 13350905) B13350905
theorem B14266621 : Blo 1758080 14266621 := bstep (se 3 (by rfl) ⟨2674991, by rfl⟩ : syracuseStep 14266621 = 5349983) B5349983
theorem B2970047 : Blo 1758080 2970047 := bstep (se 1 (by rfl) ⟨2227535, by rfl⟩ : syracuseStep 2970047 = 4455071) B4455071
theorem B3338729 : Blo 1758080 3338729 := bstep (se 2 (by rfl) ⟨1252023, by rfl⟩ : syracuseStep 3338729 = 2504047) B2504047
theorem B137450029 : Blo 1758080 137450029 := bstep (se 3 (by rfl) ⟨25771880, by rfl⟩ : syracuseStep 137450029 = 51543761) B51543761
theorem B7516925 : Blo 1758080 7516925 := bstep (se 3 (by rfl) ⟨1409423, by rfl⟩ : syracuseStep 7516925 = 2818847) B2818847
theorem B5010281 : Blo 1758080 5010281 := bstep (se 2 (by rfl) ⟨1878855, by rfl⟩ : syracuseStep 5010281 = 3757711) B3757711
theorem B1979419 : Blo 1758080 1979419 := bstep (se 1 (by rfl) ⟨1484564, by rfl⟩ : syracuseStep 1979419 = 2969129) B2969129
theorem B1758239 : Blo 1758080 1758239 := bstep (se 1 (by rfl) ⟨1318679, by rfl⟩ : syracuseStep 1758239 = 2637359) B2637359
theorem B1758255 : Blo 1758080 1758255 := bstep (se 1 (by rfl) ⟨1318691, by rfl⟩ : syracuseStep 1758255 = 2637383) B2637383
theorem B1758311 : Blo 1758080 1758311 := bstep (se 1 (by rfl) ⟨1318733, by rfl⟩ : syracuseStep 1758311 = 2637467) B2637467
theorem B13358195 : Blo 1758080 13358195 := bstep (se 1 (by rfl) ⟨10018646, by rfl⟩ : syracuseStep 13358195 = 20037293) B20037293
theorem B3814555 : Blo 1758080 3814555 := bstep (se 1 (by rfl) ⟨2860916, by rfl⟩ : syracuseStep 3814555 = 5721833) B5721833
theorem B1758375 : Blo 1758080 1758375 := bstep (se 1 (by rfl) ⟨1318781, by rfl⟩ : syracuseStep 1758375 = 2637563) B2637563
theorem B5936381 : Blo 1758080 5936381 := bstep (se 3 (by rfl) ⟨1113071, by rfl⟩ : syracuseStep 5936381 = 2226143) B2226143
theorem B128374145 : Blo 1758080 128374145 := bstep (se 2 (by rfl) ⟨48140304, by rfl⟩ : syracuseStep 128374145 = 96280609) B96280609
theorem B1758687 : Blo 1758080 1758687 := bstep (se 1 (by rfl) ⟨1319015, by rfl⟩ : syracuseStep 1758687 = 2638031) B2638031
theorem B7517711 : Blo 1758080 7517711 := bstep (se 1 (by rfl) ⟨5638283, by rfl⟩ : syracuseStep 7517711 = 11276567) B11276567
theorem B38049425 : Blo 1758080 38049425 := bstep (se 2 (by rfl) ⟨14268534, by rfl⟩ : syracuseStep 38049425 = 28537069) B28537069
theorem B25696003 : Blo 1758080 25696003 := bstep (se 1 (by rfl) ⟨19272002, by rfl⟩ : syracuseStep 25696003 = 38544005) B38544005
theorem B1759143 : Blo 1758080 1759143 := bstep (se 1 (by rfl) ⟨1319357, by rfl⟩ : syracuseStep 1759143 = 2638715) B2638715
theorem B1759227 : Blo 1758080 1759227 := bstep (se 1 (by rfl) ⟨1319420, by rfl⟩ : syracuseStep 1759227 = 2638841) B2638841
theorem B5011465 : Blo 1758080 5011465 := bstep (se 2 (by rfl) ⟨1879299, by rfl⟩ : syracuseStep 5011465 = 3758599) B3758599
theorem B1759263 : Blo 1758080 1759263 := bstep (se 1 (by rfl) ⟨1319447, by rfl⟩ : syracuseStep 1759263 = 2638895) B2638895
theorem B5347367 : Blo 1758080 5347367 := bstep (se 1 (by rfl) ⟨4010525, by rfl⟩ : syracuseStep 5347367 = 8021051) B8021051
theorem B1759343 : Blo 1758080 1759343 := bstep (se 1 (by rfl) ⟨1319507, by rfl⟩ : syracuseStep 1759343 = 2639015) B2639015
theorem B5937299 : Blo 1758080 5937299 := bstep (se 1 (by rfl) ⟨4452974, by rfl⟩ : syracuseStep 5937299 = 8905949) B8905949
theorem B1759471 : Blo 1758080 1759471 := bstep (se 1 (by rfl) ⟨1319603, by rfl⟩ : syracuseStep 1759471 = 2639207) B2639207
theorem B7510279 : Blo 1758080 7510279 := bstep (se 1 (by rfl) ⟨5632709, by rfl⟩ : syracuseStep 7510279 = 11265419) B11265419
theorem B4454959 : Blo 1758080 4454959 := bstep (se 1 (by rfl) ⟨3341219, by rfl⟩ : syracuseStep 4454959 = 6682439) B6682439
theorem B10017371 : Blo 1758080 10017371 := bstep (se 1 (by rfl) ⟨7513028, by rfl⟩ : syracuseStep 10017371 = 15026057) B15026057
theorem B7510637 : Blo 1758080 7510637 := bstep (se 3 (by rfl) ⟨1408244, by rfl⟩ : syracuseStep 7510637 = 2816489) B2816489
theorem B216644219 : Blo 1758080 216644219 := bstep (se 1 (by rfl) ⟨162483164, by rfl⟩ : syracuseStep 216644219 = 324966329) B324966329
theorem B3758719 : Blo 1758080 3758719 := bstep (se 1 (by rfl) ⟨2819039, by rfl⟩ : syracuseStep 3758719 = 5638079) B5638079
theorem B1759899 : Blo 1758080 1759899 := bstep (se 1 (by rfl) ⟨1319924, by rfl⟩ : syracuseStep 1759899 = 2639849) B2639849
theorem B42810065 : Blo 1758080 42810065 := bstep (se 2 (by rfl) ⟨16053774, by rfl⟩ : syracuseStep 42810065 = 32107549) B32107549
theorem B1759995 : Blo 1758080 1759995 := bstep (se 1 (by rfl) ⟨1319996, by rfl⟩ : syracuseStep 1759995 = 2639993) B2639993
theorem B6020527 : Blo 1758080 6020527 := bstep (se 1 (by rfl) ⟨4515395, by rfl⟩ : syracuseStep 6020527 = 9030791) B9030791
theorem B5709467 : Blo 1758080 5709467 := bstep (se 1 (by rfl) ⟨4282100, by rfl⟩ : syracuseStep 5709467 = 8564201) B8564201
theorem B6676303 : Blo 1758080 6676303 := bstep (se 1 (by rfl) ⟨5007227, by rfl⟩ : syracuseStep 6676303 = 10014455) B10014455
theorem B13352849 : Blo 1758080 13352849 := bstep (se 2 (by rfl) ⟨5007318, by rfl⟩ : syracuseStep 13352849 = 10014637) B10014637
theorem B2818027 : Blo 1758080 2818027 := bstep (se 1 (by rfl) ⟨2113520, by rfl⟩ : syracuseStep 2818027 = 4227041) B4227041
theorem B2637983 : Blo 1758080 2637983 := bstep (se 1 (by rfl) ⟨1978487, by rfl⟩ : syracuseStep 2637983 = 3956975) B3956975
theorem B19022161 : Blo 1758080 19022161 := bstep (se 2 (by rfl) ⟨7133310, by rfl⟩ : syracuseStep 19022161 = 14266621) B14266621
theorem B3957353 : Blo 1758080 3957353 := bstep (se 2 (by rfl) ⟨1484007, by rfl⟩ : syracuseStep 3957353 = 2968015) B2968015
theorem B5939945 : Blo 1758080 5939945 := bstep (se 2 (by rfl) ⟨2227479, by rfl⟩ : syracuseStep 5939945 = 4454959) B4454959
theorem B8905463 : Blo 1758080 8905463 := bstep (se 1 (by rfl) ⟨6679097, by rfl⟩ : syracuseStep 8905463 = 13358195) B13358195
theorem B3957587 : Blo 1758080 3957587 := bstep (se 1 (by rfl) ⟨2968190, by rfl⟩ : syracuseStep 3957587 = 5936381) B5936381
theorem B3957641 : Blo 1758080 3957641 := bstep (se 2 (by rfl) ⟨1484115, by rfl⟩ : syracuseStep 3957641 = 2968231) B2968231
theorem B85582763 : Blo 1758080 85582763 := bstep (se 1 (by rfl) ⟨64187072, by rfl⟩ : syracuseStep 85582763 = 128374145) B128374145
theorem B36586847 : Blo 1758080 36586847 := bstep (se 1 (by rfl) ⟨27440135, by rfl⟩ : syracuseStep 36586847 = 54880271) B54880271
theorem B3564911 : Blo 1758080 3564911 := bstep (se 1 (by rfl) ⟨2673683, by rfl⟩ : syracuseStep 3564911 = 5347367) B5347367
theorem B2639225 : Blo 1758080 2639225 := bstep (se 2 (by rfl) ⟨989709, by rfl⟩ : syracuseStep 2639225 = 1979419) B1979419
theorem B3958199 : Blo 1758080 3958199 := bstep (se 1 (by rfl) ⟨2968649, by rfl⟩ : syracuseStep 3958199 = 5937299) B5937299
theorem B6342175 : Blo 1758080 6342175 := bstep (se 1 (by rfl) ⟨4756631, by rfl⟩ : syracuseStep 6342175 = 9513263) B9513263
theorem B2639519 : Blo 1758080 2639519 := bstep (se 1 (by rfl) ⟨1979639, by rfl⟩ : syracuseStep 2639519 = 3959279) B3959279
theorem B6678247 : Blo 1758080 6678247 := bstep (se 1 (by rfl) ⟨5008685, by rfl⟩ : syracuseStep 6678247 = 10017371) B10017371
theorem B5007091 : Blo 1758080 5007091 := bstep (se 1 (by rfl) ⟨3755318, by rfl⟩ : syracuseStep 5007091 = 7510637) B7510637
theorem B12683081 : Blo 1758080 12683081 := bstep (se 2 (by rfl) ⟨4756155, by rfl⟩ : syracuseStep 12683081 = 9512311) B9512311
theorem B38029175 : Blo 1758080 38029175 := bstep (se 1 (by rfl) ⟨28521881, by rfl⟩ : syracuseStep 38029175 = 57043763) B57043763
theorem B3958649 : Blo 1758080 3958649 := bstep (se 2 (by rfl) ⟨1484493, by rfl⟩ : syracuseStep 3958649 = 2968987) B2968987
theorem B13355279 : Blo 1758080 13355279 := bstep (se 1 (by rfl) ⟨10016459, by rfl⟩ : syracuseStep 13355279 = 20032919) B20032919
theorem B34261337 : Blo 1758080 34261337 := bstep (se 2 (by rfl) ⟨12848001, by rfl⟩ : syracuseStep 34261337 = 25696003) B25696003
theorem B5933735 : Blo 1758080 5933735 := bstep (se 1 (by rfl) ⟨4450301, by rfl⟩ : syracuseStep 5933735 = 8900603) B8900603
theorem B5008367 : Blo 1758080 5008367 := bstep (se 1 (by rfl) ⟨3756275, by rfl⟩ : syracuseStep 5008367 = 7512551) B7512551
theorem B10013705 : Blo 1758080 10013705 := bstep (se 2 (by rfl) ⟨3755139, by rfl⟩ : syracuseStep 10013705 = 7510279) B7510279
theorem B77122685 : Blo 1758080 77122685 := bstep (se 3 (by rfl) ⟨14460503, by rfl⟩ : syracuseStep 77122685 = 28921007) B28921007
theorem B183266705 : Blo 1758080 183266705 := bstep (se 2 (by rfl) ⟨68725014, by rfl⟩ : syracuseStep 183266705 = 137450029) B137450029
theorem B25366283 : Blo 1758080 25366283 := bstep (se 1 (by rfl) ⟨19024712, by rfl⟩ : syracuseStep 25366283 = 38049425) B38049425
theorem B4452691 : Blo 1758080 4452691 := bstep (se 1 (by rfl) ⟨3339518, by rfl⟩ : syracuseStep 4452691 = 6679037) B6679037
theorem B15225245 : Blo 1758080 15225245 := bstep (se 3 (by rfl) ⟨2854733, by rfl⟩ : syracuseStep 15225245 = 5709467) B5709467
theorem B144429479 : Blo 1758080 144429479 := bstep (se 1 (by rfl) ⟨108322109, by rfl⟩ : syracuseStep 144429479 = 216644219) B216644219
theorem B8909351 : Blo 1758080 8909351 := bstep (se 1 (by rfl) ⟨6682013, by rfl⟩ : syracuseStep 8909351 = 13364027) B13364027
theorem B62616239 : Blo 1758080 62616239 := bstep (se 1 (by rfl) ⟨46962179, by rfl⟩ : syracuseStep 62616239 = 93924359) B93924359
theorem B8901737 : Blo 1758080 8901737 := bstep (se 2 (by rfl) ⟨3338151, by rfl⟩ : syracuseStep 8901737 = 6676303) B6676303
theorem B8909999 : Blo 1758080 8909999 := bstep (se 1 (by rfl) ⟨6682499, by rfl⟩ : syracuseStep 8909999 = 13364999) B13364999
theorem B6337721 : Blo 1758080 6337721 := bstep (se 2 (by rfl) ⟨2376645, by rfl⟩ : syracuseStep 6337721 = 4753291) B4753291
theorem B8901899 : Blo 1758080 8901899 := bstep (se 1 (by rfl) ⟨6676424, by rfl⟩ : syracuseStep 8901899 = 13352849) B13352849
theorem B3757369 : Blo 1758080 3757369 := bstep (se 2 (by rfl) ⟨1409013, by rfl⟩ : syracuseStep 3757369 = 2818027) B2818027
theorem B6681953 : Blo 1758080 6681953 := bstep (se 2 (by rfl) ⟨2505732, by rfl⟩ : syracuseStep 6681953 = 5011465) B5011465
theorem B1758567 : Blo 1758080 1758567 := bstep (se 1 (by rfl) ⟨1318925, by rfl⟩ : syracuseStep 1758567 = 2637851) B2637851
theorem B1758747 : Blo 1758080 1758747 := bstep (se 1 (by rfl) ⟨1319060, by rfl⟩ : syracuseStep 1758747 = 2638121) B2638121
theorem B1758847 : Blo 1758080 1758847 := bstep (se 1 (by rfl) ⟨1319135, by rfl⟩ : syracuseStep 1758847 = 2638271) B2638271
theorem B1980031 : Blo 1758080 1980031 := bstep (se 1 (by rfl) ⟨1485023, by rfl⟩ : syracuseStep 1980031 = 2970047) B2970047
theorem B2225819 : Blo 1758080 2225819 := bstep (se 1 (by rfl) ⟨1669364, by rfl⟩ : syracuseStep 2225819 = 3338729) B3338729
theorem B5011283 : Blo 1758080 5011283 := bstep (se 1 (by rfl) ⟨3758462, by rfl⟩ : syracuseStep 5011283 = 7516925) B7516925
theorem B3340187 : Blo 1758080 3340187 := bstep (se 1 (by rfl) ⟨2505140, by rfl⟩ : syracuseStep 3340187 = 5010281) B5010281
theorem B1759259 : Blo 1758080 1759259 := bstep (se 1 (by rfl) ⟨1319444, by rfl⟩ : syracuseStep 1759259 = 2638889) B2638889
theorem B5937191 : Blo 1758080 5937191 := bstep (se 1 (by rfl) ⟨4452893, by rfl⟩ : syracuseStep 5937191 = 8905787) B8905787
theorem B5011625 : Blo 1758080 5011625 := bstep (se 2 (by rfl) ⟨1879359, by rfl⟩ : syracuseStep 5011625 = 3758719) B3758719
theorem B7133359 : Blo 1758080 7133359 := bstep (se 1 (by rfl) ⟨5350019, by rfl⟩ : syracuseStep 7133359 = 10700039) B10700039
theorem B8902871 : Blo 1758080 8902871 := bstep (se 1 (by rfl) ⟨6677153, by rfl⟩ : syracuseStep 8902871 = 13354307) B13354307
theorem B5011807 : Blo 1758080 5011807 := bstep (se 1 (by rfl) ⟨3758855, by rfl⟩ : syracuseStep 5011807 = 7517711) B7517711
theorem B5937623 : Blo 1758080 5937623 := bstep (se 1 (by rfl) ⟨4453217, by rfl⟩ : syracuseStep 5937623 = 8906435) B8906435
theorem B5086073 : Blo 1758080 5086073 := bstep (se 2 (by rfl) ⟨1907277, by rfl⟩ : syracuseStep 5086073 = 3814555) B3814555
theorem B3758975 : Blo 1758080 3758975 := bstep (se 1 (by rfl) ⟨2819231, by rfl⟩ : syracuseStep 3758975 = 5638463) B5638463
theorem B28540043 : Blo 1758080 28540043 := bstep (se 1 (by rfl) ⟨21405032, by rfl⟩ : syracuseStep 28540043 = 42810065) B42810065
theorem B8027369 : Blo 1758080 8027369 := bstep (se 2 (by rfl) ⟨3010263, by rfl⟩ : syracuseStep 8027369 = 6020527) B6020527
theorem B10018079 : Blo 1758080 10018079 := bstep (se 1 (by rfl) ⟨7513559, by rfl⟩ : syracuseStep 10018079 = 15027119) B15027119
theorem B2637449 : Blo 1758080 2637449 := bstep (se 2 (by rfl) ⟨989043, by rfl⟩ : syracuseStep 2637449 = 1978087) B1978087
theorem B15032141 : Blo 1758080 15032141 := bstep (se 3 (by rfl) ⟨2818526, by rfl⟩ : syracuseStep 15032141 = 5637053) B5637053
theorem B5939027 : Blo 1758080 5939027 := bstep (se 1 (by rfl) ⟨4454270, by rfl⟩ : syracuseStep 5939027 = 8908541) B8908541
theorem B13361111 : Blo 1758080 13361111 := bstep (se 1 (by rfl) ⟨10020833, by rfl⟩ : syracuseStep 13361111 = 20041667) B20041667
theorem B3956705 : Blo 1758080 3956705 := bstep (se 2 (by rfl) ⟨1483764, by rfl⟩ : syracuseStep 3956705 = 2967529) B2967529
theorem B9511145 : Blo 1758080 9511145 := bstep (se 2 (by rfl) ⟨3566679, by rfl⟩ : syracuseStep 9511145 = 7133359) B7133359
theorem B10150163 : Blo 1758080 10150163 := bstep (se 1 (by rfl) ⟨7612622, by rfl⟩ : syracuseStep 10150163 = 15225245) B15225245
theorem B5939567 : Blo 1758080 5939567 := bstep (se 1 (by rfl) ⟨4454675, by rfl⟩ : syracuseStep 5939567 = 8909351) B8909351
theorem B2638235 : Blo 1758080 2638235 := bstep (se 1 (by rfl) ⟨1978676, by rfl⟩ : syracuseStep 2638235 = 3957353) B3957353
theorem B25362881 : Blo 1758080 25362881 := bstep (se 2 (by rfl) ⟨9511080, by rfl⟩ : syracuseStep 25362881 = 19022161) B19022161
theorem B16900589 : Blo 1758080 16900589 := bstep (se 3 (by rfl) ⟨3168860, by rfl⟩ : syracuseStep 16900589 = 6337721) B6337721
theorem B2638391 : Blo 1758080 2638391 := bstep (se 1 (by rfl) ⟨1978793, by rfl⟩ : syracuseStep 2638391 = 3957587) B3957587
theorem B2638427 : Blo 1758080 2638427 := bstep (se 1 (by rfl) ⟨1978820, by rfl⟩ : syracuseStep 2638427 = 3957641) B3957641
theorem B5939999 : Blo 1758080 5939999 := bstep (se 1 (by rfl) ⟨4454999, by rfl⟩ : syracuseStep 5939999 = 8909999) B8909999
theorem B2638799 : Blo 1758080 2638799 := bstep (se 1 (by rfl) ⟨1979099, by rfl⟩ : syracuseStep 2638799 = 3958199) B3958199
theorem B8455387 : Blo 1758080 8455387 := bstep (se 1 (by rfl) ⟨6341540, by rfl⟩ : syracuseStep 8455387 = 12683081) B12683081
theorem B2639099 : Blo 1758080 2639099 := bstep (se 1 (by rfl) ⟨1979324, by rfl⟩ : syracuseStep 2639099 = 3958649) B3958649
theorem B3958127 : Blo 1758080 3958127 := bstep (se 1 (by rfl) ⟨2968595, by rfl⟩ : syracuseStep 3958127 = 5937191) B5937191
theorem B3958415 : Blo 1758080 3958415 := bstep (se 1 (by rfl) ⟨2968811, by rfl⟩ : syracuseStep 3958415 = 5937623) B5937623
theorem B8456233 : Blo 1758080 8456233 := bstep (se 2 (by rfl) ⟨3171087, by rfl⟩ : syracuseStep 8456233 = 6342175) B6342175
theorem B51415123 : Blo 1758080 51415123 := bstep (se 1 (by rfl) ⟨38561342, by rfl⟩ : syracuseStep 51415123 = 77122685) B77122685
theorem B5351579 : Blo 1758080 5351579 := bstep (se 1 (by rfl) ⟨4013684, by rfl⟩ : syracuseStep 5351579 = 8027369) B8027369
theorem B2640041 : Blo 1758080 2640041 := bstep (se 2 (by rfl) ⟨990015, by rfl⟩ : syracuseStep 2640041 = 1980031) B1980031
theorem B6678719 : Blo 1758080 6678719 := bstep (se 1 (by rfl) ⟨5009039, by rfl⟩ : syracuseStep 6678719 = 10018079) B10018079
theorem B122177803 : Blo 1758080 122177803 := bstep (se 1 (by rfl) ⟨91633352, by rfl⟩ : syracuseStep 122177803 = 183266705) B183266705
theorem B16910855 : Blo 1758080 16910855 := bstep (se 1 (by rfl) ⟨12683141, by rfl⟩ : syracuseStep 16910855 = 25366283) B25366283
theorem B10021427 : Blo 1758080 10021427 := bstep (se 1 (by rfl) ⟨7516070, by rfl⟩ : syracuseStep 10021427 = 15032141) B15032141
theorem B3959351 : Blo 1758080 3959351 := bstep (se 1 (by rfl) ⟨2969513, by rfl⟩ : syracuseStep 3959351 = 5939027) B5939027
theorem B8907407 : Blo 1758080 8907407 := bstep (se 1 (by rfl) ⟨6680555, by rfl⟩ : syracuseStep 8907407 = 13361111) B13361111
theorem B3959963 : Blo 1758080 3959963 := bstep (se 1 (by rfl) ⟨2969972, by rfl⟩ : syracuseStep 3959963 = 5939945) B5939945
theorem B5934491 : Blo 1758080 5934491 := bstep (se 1 (by rfl) ⟨4450868, by rfl⟩ : syracuseStep 5934491 = 8901737) B8901737
theorem B5934599 : Blo 1758080 5934599 := bstep (se 1 (by rfl) ⟨4450949, by rfl⟩ : syracuseStep 5934599 = 8901899) B8901899
theorem B9506429 : Blo 1758080 9506429 := bstep (se 3 (by rfl) ⟨1782455, by rfl⟩ : syracuseStep 9506429 = 3564911) B3564911
theorem B5935247 : Blo 1758080 5935247 := bstep (se 1 (by rfl) ⟨4451435, by rfl⟩ : syracuseStep 5935247 = 8902871) B8902871
theorem B5935517 : Blo 1758080 5935517 := bstep (se 3 (by rfl) ⟨1112909, by rfl⟩ : syracuseStep 5935517 = 2225819) B2225819
theorem B5009825 : Blo 1758080 5009825 := bstep (se 2 (by rfl) ⟨1878684, by rfl⟩ : syracuseStep 5009825 = 3757369) B3757369
theorem B3338911 : Blo 1758080 3338911 := bstep (se 1 (by rfl) ⟨2504183, by rfl⟩ : syracuseStep 3338911 = 5008367) B5008367
theorem B19026695 : Blo 1758080 19026695 := bstep (se 1 (by rfl) ⟨14270021, by rfl⟩ : syracuseStep 19026695 = 28540043) B28540043
theorem B13562861 : Blo 1758080 13562861 := bstep (se 3 (by rfl) ⟨2543036, by rfl⟩ : syracuseStep 13562861 = 5086073) B5086073
theorem B1758299 : Blo 1758080 1758299 := bstep (se 1 (by rfl) ⟨1318724, by rfl⟩ : syracuseStep 1758299 = 2637449) B2637449
theorem B1758655 : Blo 1758080 1758655 := bstep (se 1 (by rfl) ⟨1318991, by rfl⟩ : syracuseStep 1758655 = 2637983) B2637983
theorem B96286319 : Blo 1758080 96286319 := bstep (se 1 (by rfl) ⟨72214739, by rfl⟩ : syracuseStep 96286319 = 144429479) B144429479
theorem B5936921 : Blo 1758080 5936921 := bstep (se 2 (by rfl) ⟨2226345, by rfl⟩ : syracuseStep 5936921 = 4452691) B4452691
theorem B41744159 : Blo 1758080 41744159 := bstep (se 1 (by rfl) ⟨31308119, by rfl⟩ : syracuseStep 41744159 = 62616239) B62616239
theorem B6682409 : Blo 1758080 6682409 := bstep (se 2 (by rfl) ⟨2505903, by rfl⟩ : syracuseStep 6682409 = 5011807) B5011807
theorem B5936975 : Blo 1758080 5936975 := bstep (se 1 (by rfl) ⟨4452731, by rfl⟩ : syracuseStep 5936975 = 8905463) B8905463
theorem B57055175 : Blo 1758080 57055175 := bstep (se 1 (by rfl) ⟨42791381, by rfl⟩ : syracuseStep 57055175 = 85582763) B85582763
theorem B91363565 : Blo 1758080 91363565 := bstep (se 3 (by rfl) ⟨17130668, by rfl⟩ : syracuseStep 91363565 = 34261337) B34261337
theorem B4454635 : Blo 1758080 4454635 := bstep (se 1 (by rfl) ⟨3340976, by rfl⟩ : syracuseStep 4454635 = 6681953) B6681953
theorem B1759483 : Blo 1758080 1759483 := bstep (se 1 (by rfl) ⟨1319612, by rfl⟩ : syracuseStep 1759483 = 2639225) B2639225
theorem B97564925 : Blo 1758080 97564925 := bstep (se 3 (by rfl) ⟨18293423, by rfl⟩ : syracuseStep 97564925 = 36586847) B36586847
theorem B1759679 : Blo 1758080 1759679 := bstep (se 1 (by rfl) ⟨1319759, by rfl⟩ : syracuseStep 1759679 = 2639519) B2639519
theorem B3340855 : Blo 1758080 3340855 := bstep (se 1 (by rfl) ⟨2505641, by rfl⟩ : syracuseStep 3340855 = 5011283) B5011283
theorem B25352783 : Blo 1758080 25352783 := bstep (se 1 (by rfl) ⟨19014587, by rfl⟩ : syracuseStep 25352783 = 38029175) B38029175
theorem B2226791 : Blo 1758080 2226791 := bstep (se 1 (by rfl) ⟨1670093, by rfl⟩ : syracuseStep 2226791 = 3340187) B3340187
theorem B3341083 : Blo 1758080 3341083 := bstep (se 1 (by rfl) ⟨2505812, by rfl⟩ : syracuseStep 3341083 = 5011625) B5011625
theorem B8903519 : Blo 1758080 8903519 := bstep (se 1 (by rfl) ⟨6677639, by rfl⟩ : syracuseStep 8903519 = 13355279) B13355279
theorem B3955823 : Blo 1758080 3955823 := bstep (se 1 (by rfl) ⟨2966867, by rfl⟩ : syracuseStep 3955823 = 5933735) B5933735
theorem B2505983 : Blo 1758080 2505983 := bstep (se 1 (by rfl) ⟨1879487, by rfl⟩ : syracuseStep 2505983 = 3758975) B3758975
theorem B6675803 : Blo 1758080 6675803 := bstep (se 1 (by rfl) ⟨5006852, by rfl⟩ : syracuseStep 6675803 = 10013705) B10013705
theorem B8904329 : Blo 1758080 8904329 := bstep (se 2 (by rfl) ⟨3339123, by rfl⟩ : syracuseStep 8904329 = 6678247) B6678247
theorem B6676121 : Blo 1758080 6676121 := bstep (se 2 (by rfl) ⟨2503545, by rfl⟩ : syracuseStep 6676121 = 5007091) B5007091
theorem B2637803 : Blo 1758080 2637803 := bstep (se 1 (by rfl) ⟨1978352, by rfl⟩ : syracuseStep 2637803 = 3956705) B3956705
theorem B3956831 : Blo 1758080 3956831 := bstep (se 1 (by rfl) ⟨2967623, by rfl⟩ : syracuseStep 3956831 = 5935247) B5935247
theorem B6340763 : Blo 1758080 6340763 := bstep (se 1 (by rfl) ⟨4755572, by rfl⟩ : syracuseStep 6340763 = 9511145) B9511145
theorem B6766775 : Blo 1758080 6766775 := bstep (se 1 (by rfl) ⟨5075081, by rfl⟩ : syracuseStep 6766775 = 10150163) B10150163
theorem B3957011 : Blo 1758080 3957011 := bstep (se 1 (by rfl) ⟨2967758, by rfl⟩ : syracuseStep 3957011 = 5935517) B5935517
theorem B16908587 : Blo 1758080 16908587 := bstep (se 1 (by rfl) ⟨12681440, by rfl⟩ : syracuseStep 16908587 = 25362881) B25362881
theorem B5939513 : Blo 1758080 5939513 := bstep (se 2 (by rfl) ⟨2227317, by rfl⟩ : syracuseStep 5939513 = 4454635) B4454635
theorem B2638751 : Blo 1758080 2638751 := bstep (se 1 (by rfl) ⟨1979063, by rfl⟩ : syracuseStep 2638751 = 3958127) B3958127
theorem B2638943 : Blo 1758080 2638943 := bstep (se 1 (by rfl) ⟨1979207, by rfl⟩ : syracuseStep 2638943 = 3958415) B3958415
theorem B3957947 : Blo 1758080 3957947 := bstep (se 1 (by rfl) ⟨2968460, by rfl⟩ : syracuseStep 3957947 = 5936921) B5936921
theorem B27829439 : Blo 1758080 27829439 := bstep (se 1 (by rfl) ⟨20872079, by rfl⟩ : syracuseStep 27829439 = 41744159) B41744159
theorem B3957983 : Blo 1758080 3957983 := bstep (se 1 (by rfl) ⟨2968487, by rfl⟩ : syracuseStep 3957983 = 5936975) B5936975
theorem B38036783 : Blo 1758080 38036783 := bstep (se 1 (by rfl) ⟨28527587, by rfl⟩ : syracuseStep 38036783 = 57055175) B57055175
theorem B60909043 : Blo 1758080 60909043 := bstep (se 1 (by rfl) ⟨45681782, by rfl⟩ : syracuseStep 60909043 = 91363565) B91363565
theorem B11273849 : Blo 1758080 11273849 := bstep (se 2 (by rfl) ⟨4227693, by rfl⟩ : syracuseStep 11273849 = 8455387) B8455387
theorem B11273903 : Blo 1758080 11273903 := bstep (se 1 (by rfl) ⟨8455427, by rfl⟩ : syracuseStep 11273903 = 16910855) B16910855
theorem B2639567 : Blo 1758080 2639567 := bstep (se 1 (by rfl) ⟨1979675, by rfl⟩ : syracuseStep 2639567 = 3959351) B3959351
theorem B16901855 : Blo 1758080 16901855 := bstep (se 1 (by rfl) ⟨12676391, by rfl⟩ : syracuseStep 16901855 = 25352783) B25352783
theorem B2639975 : Blo 1758080 2639975 := bstep (se 1 (by rfl) ⟨1979981, by rfl⟩ : syracuseStep 2639975 = 3959963) B3959963
theorem B4450535 : Blo 1758080 4450535 := bstep (se 1 (by rfl) ⟨3337901, by rfl⟩ : syracuseStep 4450535 = 6675803) B6675803
theorem B4450747 : Blo 1758080 4450747 := bstep (se 1 (by rfl) ⟨3338060, by rfl⟩ : syracuseStep 4450747 = 6676121) B6676121
theorem B11274977 : Blo 1758080 11274977 := bstep (se 2 (by rfl) ⟨4228116, by rfl⟩ : syracuseStep 11274977 = 8456233) B8456233
theorem B68553497 : Blo 1758080 68553497 := bstep (se 2 (by rfl) ⟨25707561, by rfl⟩ : syracuseStep 68553497 = 51415123) B51415123
theorem B3959711 : Blo 1758080 3959711 := bstep (se 1 (by rfl) ⟨2969783, by rfl⟩ : syracuseStep 3959711 = 5939567) B5939567
theorem B11267059 : Blo 1758080 11267059 := bstep (se 1 (by rfl) ⟨8450294, by rfl⟩ : syracuseStep 11267059 = 16900589) B16900589
theorem B3959999 : Blo 1758080 3959999 := bstep (se 1 (by rfl) ⟨2969999, by rfl⟩ : syracuseStep 3959999 = 5939999) B5939999
theorem B4451881 : Blo 1758080 4451881 := bstep (se 2 (by rfl) ⟨1669455, by rfl⟩ : syracuseStep 4451881 = 3338911) B3338911
theorem B3567719 : Blo 1758080 3567719 := bstep (se 1 (by rfl) ⟨2675789, by rfl⟩ : syracuseStep 3567719 = 5351579) B5351579
theorem B4452479 : Blo 1758080 4452479 := bstep (se 1 (by rfl) ⟨3339359, by rfl⟩ : syracuseStep 4452479 = 6678719) B6678719
theorem B6680951 : Blo 1758080 6680951 := bstep (se 1 (by rfl) ⟨5010713, by rfl⟩ : syracuseStep 6680951 = 10021427) B10021427
theorem B5935679 : Blo 1758080 5935679 := bstep (se 1 (by rfl) ⟨4451759, by rfl⟩ : syracuseStep 5935679 = 8903519) B8903519
theorem B50737853 : Blo 1758080 50737853 := bstep (se 3 (by rfl) ⟨9513347, by rfl⟩ : syracuseStep 50737853 = 19026695) B19026695
theorem B6337619 : Blo 1758080 6337619 := bstep (se 1 (by rfl) ⟨4753214, by rfl⟩ : syracuseStep 6337619 = 9506429) B9506429
theorem B5936219 : Blo 1758080 5936219 := bstep (se 1 (by rfl) ⟨4452164, by rfl⟩ : syracuseStep 5936219 = 8904329) B8904329
theorem B1758535 : Blo 1758080 1758535 := bstep (se 1 (by rfl) ⟨1318901, by rfl⟩ : syracuseStep 1758535 = 2637803) B2637803
theorem B1758823 : Blo 1758080 1758823 := bstep (se 1 (by rfl) ⟨1319117, by rfl⟩ : syracuseStep 1758823 = 2638235) B2638235
theorem B3339883 : Blo 1758080 3339883 := bstep (se 1 (by rfl) ⟨2504912, by rfl⟩ : syracuseStep 3339883 = 5009825) B5009825
theorem B162903737 : Blo 1758080 162903737 := bstep (se 2 (by rfl) ⟨61088901, by rfl⟩ : syracuseStep 162903737 = 122177803) B122177803
theorem B1758927 : Blo 1758080 1758927 := bstep (se 1 (by rfl) ⟨1319195, by rfl⟩ : syracuseStep 1758927 = 2638391) B2638391
theorem B1758951 : Blo 1758080 1758951 := bstep (se 1 (by rfl) ⟨1319213, by rfl⟩ : syracuseStep 1758951 = 2638427) B2638427
theorem B1759199 : Blo 1758080 1759199 := bstep (se 1 (by rfl) ⟨1319399, by rfl⟩ : syracuseStep 1759199 = 2638799) B2638799
theorem B6682621 : Blo 1758080 6682621 := bstep (se 3 (by rfl) ⟨1252991, by rfl⟩ : syracuseStep 6682621 = 2505983) B2505983
theorem B4454473 : Blo 1758080 4454473 := bstep (se 2 (by rfl) ⟨1670427, by rfl⟩ : syracuseStep 4454473 = 3340855) B3340855
theorem B1759399 : Blo 1758080 1759399 := bstep (se 1 (by rfl) ⟨1319549, by rfl⟩ : syracuseStep 1759399 = 2639099) B2639099
theorem B4454777 : Blo 1758080 4454777 := bstep (se 2 (by rfl) ⟨1670541, by rfl⟩ : syracuseStep 4454777 = 3341083) B3341083
theorem B64190879 : Blo 1758080 64190879 := bstep (se 1 (by rfl) ⟨48143159, by rfl⟩ : syracuseStep 64190879 = 96286319) B96286319
theorem B4454939 : Blo 1758080 4454939 := bstep (se 1 (by rfl) ⟨3341204, by rfl⟩ : syracuseStep 4454939 = 6682409) B6682409
theorem B1760027 : Blo 1758080 1760027 := bstep (se 1 (by rfl) ⟨1320020, by rfl⟩ : syracuseStep 1760027 = 2640041) B2640041
theorem B65043283 : Blo 1758080 65043283 := bstep (se 1 (by rfl) ⟨48782462, by rfl⟩ : syracuseStep 65043283 = 97564925) B97564925
theorem B5938109 : Blo 1758080 5938109 := bstep (se 3 (by rfl) ⟨1113395, by rfl⟩ : syracuseStep 5938109 = 2226791) B2226791
theorem B5938271 : Blo 1758080 5938271 := bstep (se 1 (by rfl) ⟨4453703, by rfl⟩ : syracuseStep 5938271 = 8907407) B8907407
theorem B2637215 : Blo 1758080 2637215 := bstep (se 1 (by rfl) ⟨1977911, by rfl⟩ : syracuseStep 2637215 = 3955823) B3955823
theorem B3956327 : Blo 1758080 3956327 := bstep (se 1 (by rfl) ⟨2967245, by rfl⟩ : syracuseStep 3956327 = 5934491) B5934491
theorem B3956399 : Blo 1758080 3956399 := bstep (se 1 (by rfl) ⟨2967299, by rfl⟩ : syracuseStep 3956399 = 5934599) B5934599
theorem B36167629 : Blo 1758080 36167629 := bstep (se 3 (by rfl) ⟨6781430, by rfl⟩ : syracuseStep 36167629 = 13562861) B13562861
theorem B2637887 : Blo 1758080 2637887 := bstep (se 1 (by rfl) ⟨1978415, by rfl⟩ : syracuseStep 2637887 = 3956831) B3956831
theorem B5939297 : Blo 1758080 5939297 := bstep (se 2 (by rfl) ⟨2227236, by rfl⟩ : syracuseStep 5939297 = 4454473) B4454473
theorem B4227175 : Blo 1758080 4227175 := bstep (se 1 (by rfl) ⟨3170381, by rfl⟩ : syracuseStep 4227175 = 6340763) B6340763
theorem B2638007 : Blo 1758080 2638007 := bstep (se 1 (by rfl) ⟨1978505, by rfl⟩ : syracuseStep 2638007 = 3957011) B3957011
theorem B11272391 : Blo 1758080 11272391 := bstep (se 1 (by rfl) ⟨8454293, by rfl⟩ : syracuseStep 11272391 = 16908587) B16908587
theorem B3957119 : Blo 1758080 3957119 := bstep (se 1 (by rfl) ⟨2967839, by rfl⟩ : syracuseStep 3957119 = 5935679) B5935679
theorem B33825235 : Blo 1758080 33825235 := bstep (se 1 (by rfl) ⟨25368926, by rfl⟩ : syracuseStep 33825235 = 50737853) B50737853
theorem B3957479 : Blo 1758080 3957479 := bstep (se 1 (by rfl) ⟨2968109, by rfl⟩ : syracuseStep 3957479 = 5936219) B5936219
theorem B2638631 : Blo 1758080 2638631 := bstep (se 1 (by rfl) ⟨1978973, by rfl⟩ : syracuseStep 2638631 = 3957947) B3957947
theorem B2638655 : Blo 1758080 2638655 := bstep (se 1 (by rfl) ⟨1978991, by rfl⟩ : syracuseStep 2638655 = 3957983) B3957983
theorem B108602491 : Blo 1758080 108602491 := bstep (se 1 (by rfl) ⟨81451868, by rfl⟩ : syracuseStep 108602491 = 162903737) B162903737
theorem B2967023 : Blo 1758080 2967023 := bstep (se 1 (by rfl) ⟨2225267, by rfl⟩ : syracuseStep 2967023 = 4450535) B4450535
theorem B2639807 : Blo 1758080 2639807 := bstep (se 1 (by rfl) ⟨1979855, by rfl⟩ : syracuseStep 2639807 = 3959711) B3959711
theorem B3958739 : Blo 1758080 3958739 := bstep (se 1 (by rfl) ⟨2969054, by rfl⟩ : syracuseStep 3958739 = 5938109) B5938109
theorem B3958847 : Blo 1758080 3958847 := bstep (se 1 (by rfl) ⟨2969135, by rfl⟩ : syracuseStep 3958847 = 5938271) B5938271
theorem B2639999 : Blo 1758080 2639999 := bstep (se 1 (by rfl) ⟨1979999, by rfl⟩ : syracuseStep 2639999 = 3959999) B3959999
theorem B2378479 : Blo 1758080 2378479 := bstep (se 1 (by rfl) ⟨1783859, by rfl⟩ : syracuseStep 2378479 = 3567719) B3567719
theorem B2968319 : Blo 1758080 2968319 := bstep (se 1 (by rfl) ⟨2226239, by rfl⟩ : syracuseStep 2968319 = 4452479) B4452479
theorem B3959675 : Blo 1758080 3959675 := bstep (se 1 (by rfl) ⟨2969756, by rfl⟩ : syracuseStep 3959675 = 5939513) B5939513
theorem B5934329 : Blo 1758080 5934329 := bstep (se 2 (by rfl) ⟨2225373, by rfl⟩ : syracuseStep 5934329 = 4450747) B4450747
theorem B25357855 : Blo 1758080 25357855 := bstep (se 1 (by rfl) ⟨19018391, by rfl⟩ : syracuseStep 25357855 = 38036783) B38036783
theorem B7515899 : Blo 1758080 7515899 := bstep (se 1 (by rfl) ⟨5636924, by rfl⟩ : syracuseStep 7515899 = 11273849) B11273849
theorem B86724377 : Blo 1758080 86724377 := bstep (se 2 (by rfl) ⟨32521641, by rfl⟩ : syracuseStep 86724377 = 65043283) B65043283
theorem B7515935 : Blo 1758080 7515935 := bstep (se 1 (by rfl) ⟨5636951, by rfl⟩ : syracuseStep 7515935 = 11273903) B11273903
theorem B11267903 : Blo 1758080 11267903 := bstep (se 1 (by rfl) ⟨8450927, by rfl⟩ : syracuseStep 11267903 = 16901855) B16901855
theorem B2969851 : Blo 1758080 2969851 := bstep (se 1 (by rfl) ⟨2227388, by rfl⟩ : syracuseStep 2969851 = 4454777) B4454777
theorem B2969959 : Blo 1758080 2969959 := bstep (se 1 (by rfl) ⟨2227469, by rfl⟩ : syracuseStep 2969959 = 4454939) B4454939
theorem B7516651 : Blo 1758080 7516651 := bstep (se 1 (by rfl) ⟨5637488, by rfl⟩ : syracuseStep 7516651 = 11274977) B11274977
theorem B81212057 : Blo 1758080 81212057 := bstep (se 2 (by rfl) ⟨30454521, by rfl⟩ : syracuseStep 81212057 = 60909043) B60909043
theorem B5935841 : Blo 1758080 5935841 := bstep (se 2 (by rfl) ⟨2225940, by rfl⟩ : syracuseStep 5935841 = 4451881) B4451881
theorem B182809325 : Blo 1758080 182809325 := bstep (se 3 (by rfl) ⟨34276748, by rfl⟩ : syracuseStep 182809325 = 68553497) B68553497
theorem B4453177 : Blo 1758080 4453177 := bstep (se 2 (by rfl) ⟨1669941, by rfl⟩ : syracuseStep 4453177 = 3339883) B3339883
theorem B1758143 : Blo 1758080 1758143 := bstep (se 1 (by rfl) ⟨1318607, by rfl⟩ : syracuseStep 1758143 = 2637215) B2637215
theorem B48223505 : Blo 1758080 48223505 := bstep (se 2 (by rfl) ⟨18083814, by rfl⟩ : syracuseStep 48223505 = 36167629) B36167629
theorem B8910161 : Blo 1758080 8910161 := bstep (se 2 (by rfl) ⟨3341310, by rfl⟩ : syracuseStep 8910161 = 6682621) B6682621
theorem B4511183 : Blo 1758080 4511183 := bstep (se 1 (by rfl) ⟨3383387, by rfl⟩ : syracuseStep 4511183 = 6766775) B6766775
theorem B4453967 : Blo 1758080 4453967 := bstep (se 1 (by rfl) ⟨3340475, by rfl⟩ : syracuseStep 4453967 = 6680951) B6680951
theorem B1759167 : Blo 1758080 1759167 := bstep (se 1 (by rfl) ⟨1319375, by rfl⟩ : syracuseStep 1759167 = 2638751) B2638751
theorem B4225079 : Blo 1758080 4225079 := bstep (se 1 (by rfl) ⟨3168809, by rfl⟩ : syracuseStep 4225079 = 6337619) B6337619
theorem B1759295 : Blo 1758080 1759295 := bstep (se 1 (by rfl) ⟨1319471, by rfl⟩ : syracuseStep 1759295 = 2638943) B2638943
theorem B18552959 : Blo 1758080 18552959 := bstep (se 1 (by rfl) ⟨13914719, by rfl⟩ : syracuseStep 18552959 = 27829439) B27829439
theorem B1759711 : Blo 1758080 1759711 := bstep (se 1 (by rfl) ⟨1319783, by rfl⟩ : syracuseStep 1759711 = 2639567) B2639567
theorem B15022745 : Blo 1758080 15022745 := bstep (se 2 (by rfl) ⟨5633529, by rfl⟩ : syracuseStep 15022745 = 11267059) B11267059
theorem B1759983 : Blo 1758080 1759983 := bstep (se 1 (by rfl) ⟨1319987, by rfl⟩ : syracuseStep 1759983 = 2639975) B2639975
theorem B42793919 : Blo 1758080 42793919 := bstep (se 1 (by rfl) ⟨32095439, by rfl⟩ : syracuseStep 42793919 = 64190879) B64190879
theorem B2637551 : Blo 1758080 2637551 := bstep (se 1 (by rfl) ⟨1978163, by rfl⟩ : syracuseStep 2637551 = 3956327) B3956327
theorem B2637599 : Blo 1758080 2637599 := bstep (se 1 (by rfl) ⟨1978199, by rfl⟩ : syracuseStep 2637599 = 3956399) B3956399
theorem B5636233 : Blo 1758080 5636233 := bstep (se 2 (by rfl) ⟨2113587, by rfl⟩ : syracuseStep 5636233 = 4227175) B4227175
theorem B2638079 : Blo 1758080 2638079 := bstep (se 1 (by rfl) ⟨1978559, by rfl⟩ : syracuseStep 2638079 = 3957119) B3957119
theorem B54141371 : Blo 1758080 54141371 := bstep (se 1 (by rfl) ⟨40606028, by rfl⟩ : syracuseStep 54141371 = 81212057) B81212057
theorem B3957227 : Blo 1758080 3957227 := bstep (se 1 (by rfl) ⟨2967920, by rfl⟩ : syracuseStep 3957227 = 5935841) B5935841
theorem B2638319 : Blo 1758080 2638319 := bstep (se 1 (by rfl) ⟨1978739, by rfl⟩ : syracuseStep 2638319 = 3957479) B3957479
theorem B121872883 : Blo 1758080 121872883 := bstep (se 1 (by rfl) ⟨91404662, by rfl⟩ : syracuseStep 121872883 = 182809325) B182809325
theorem B5940107 : Blo 1758080 5940107 := bstep (se 1 (by rfl) ⟨4455080, by rfl⟩ : syracuseStep 5940107 = 8910161) B8910161
theorem B3171305 : Blo 1758080 3171305 := bstep (se 2 (by rfl) ⟨1189239, by rfl⟩ : syracuseStep 3171305 = 2378479) B2378479
theorem B2639159 : Blo 1758080 2639159 := bstep (se 1 (by rfl) ⟨1979369, by rfl⟩ : syracuseStep 2639159 = 3958739) B3958739
theorem B2639231 : Blo 1758080 2639231 := bstep (se 1 (by rfl) ⟨1979423, by rfl⟩ : syracuseStep 2639231 = 3958847) B3958847
theorem B144803321 : Blo 1758080 144803321 := bstep (se 2 (by rfl) ⟨54301245, by rfl⟩ : syracuseStep 144803321 = 108602491) B108602491
theorem B2639783 : Blo 1758080 2639783 := bstep (se 1 (by rfl) ⟨1979837, by rfl⟩ : syracuseStep 2639783 = 3959675) B3959675
theorem B33810473 : Blo 1758080 33810473 := bstep (se 2 (by rfl) ⟨12678927, by rfl⟩ : syracuseStep 33810473 = 25357855) B25357855
theorem B3959531 : Blo 1758080 3959531 := bstep (se 1 (by rfl) ⟨2969648, by rfl⟩ : syracuseStep 3959531 = 5939297) B5939297
theorem B7514927 : Blo 1758080 7514927 := bstep (se 1 (by rfl) ⟨5636195, by rfl⟩ : syracuseStep 7514927 = 11272391) B11272391
theorem B11266877 : Blo 1758080 11266877 := bstep (se 3 (by rfl) ⟨2112539, by rfl⟩ : syracuseStep 11266877 = 4225079) B4225079
theorem B3959801 : Blo 1758080 3959801 := bstep (se 2 (by rfl) ⟨1484925, by rfl⟩ : syracuseStep 3959801 = 2969851) B2969851
theorem B3959945 : Blo 1758080 3959945 := bstep (se 2 (by rfl) ⟨1484979, by rfl⟩ : syracuseStep 3959945 = 2969959) B2969959
theorem B45100313 : Blo 1758080 45100313 := bstep (se 2 (by rfl) ⟨16912617, by rfl⟩ : syracuseStep 45100313 = 33825235) B33825235
theorem B10022201 : Blo 1758080 10022201 := bstep (se 2 (by rfl) ⟨3758325, by rfl⟩ : syracuseStep 10022201 = 7516651) B7516651
theorem B32149003 : Blo 1758080 32149003 := bstep (se 1 (by rfl) ⟨24111752, by rfl⟩ : syracuseStep 32149003 = 48223505) B48223505
theorem B1978015 : Blo 1758080 1978015 := bstep (se 1 (by rfl) ⟨1483511, by rfl⟩ : syracuseStep 1978015 = 2967023) B2967023
theorem B2969311 : Blo 1758080 2969311 := bstep (se 1 (by rfl) ⟨2226983, by rfl⟩ : syracuseStep 2969311 = 4453967) B4453967
theorem B10015163 : Blo 1758080 10015163 := bstep (se 1 (by rfl) ⟨7511372, by rfl⟩ : syracuseStep 10015163 = 15022745) B15022745
theorem B1978879 : Blo 1758080 1978879 := bstep (se 1 (by rfl) ⟨1484159, by rfl⟩ : syracuseStep 1978879 = 2968319) B2968319
theorem B28529279 : Blo 1758080 28529279 := bstep (se 1 (by rfl) ⟨21396959, by rfl⟩ : syracuseStep 28529279 = 42793919) B42793919
theorem B1758367 : Blo 1758080 1758367 := bstep (se 1 (by rfl) ⟨1318775, by rfl⟩ : syracuseStep 1758367 = 2637551) B2637551
theorem B5010599 : Blo 1758080 5010599 := bstep (se 1 (by rfl) ⟨3757949, by rfl⟩ : syracuseStep 5010599 = 7515899) B7515899
theorem B57816251 : Blo 1758080 57816251 := bstep (se 1 (by rfl) ⟨43362188, by rfl⟩ : syracuseStep 57816251 = 86724377) B86724377
theorem B1758399 : Blo 1758080 1758399 := bstep (se 1 (by rfl) ⟨1318799, by rfl⟩ : syracuseStep 1758399 = 2637599) B2637599
theorem B5010623 : Blo 1758080 5010623 := bstep (se 1 (by rfl) ⟨3757967, by rfl⟩ : syracuseStep 5010623 = 7515935) B7515935
theorem B1758591 : Blo 1758080 1758591 := bstep (se 1 (by rfl) ⟨1318943, by rfl⟩ : syracuseStep 1758591 = 2637887) B2637887
theorem B1758671 : Blo 1758080 1758671 := bstep (se 1 (by rfl) ⟨1319003, by rfl⟩ : syracuseStep 1758671 = 2638007) B2638007
theorem B1759087 : Blo 1758080 1759087 := bstep (se 1 (by rfl) ⟨1319315, by rfl⟩ : syracuseStep 1759087 = 2638631) B2638631
theorem B1759103 : Blo 1758080 1759103 := bstep (se 1 (by rfl) ⟨1319327, by rfl⟩ : syracuseStep 1759103 = 2638655) B2638655
theorem B5937569 : Blo 1758080 5937569 := bstep (se 2 (by rfl) ⟨2226588, by rfl⟩ : syracuseStep 5937569 = 4453177) B4453177
theorem B1759871 : Blo 1758080 1759871 := bstep (se 1 (by rfl) ⟨1319903, by rfl⟩ : syracuseStep 1759871 = 2639807) B2639807
theorem B12368639 : Blo 1758080 12368639 := bstep (se 1 (by rfl) ⟨9276479, by rfl⟩ : syracuseStep 12368639 = 18552959) B18552959
theorem B1759999 : Blo 1758080 1759999 := bstep (se 1 (by rfl) ⟨1319999, by rfl⟩ : syracuseStep 1759999 = 2639999) B2639999
theorem B48119285 : Blo 1758080 48119285 := bstep (se 5 (by rfl) ⟨2255591, by rfl⟩ : syracuseStep 48119285 = 4511183) B4511183
theorem B3956219 : Blo 1758080 3956219 := bstep (se 1 (by rfl) ⟨2967164, by rfl⟩ : syracuseStep 3956219 = 5934329) B5934329
theorem B7511935 : Blo 1758080 7511935 := bstep (se 1 (by rfl) ⟨5633951, by rfl⟩ : syracuseStep 7511935 = 11267903) B11267903
theorem B36094247 : Blo 1758080 36094247 := bstep (se 1 (by rfl) ⟨27070685, by rfl⟩ : syracuseStep 36094247 = 54141371) B54141371
theorem B6676775 : Blo 1758080 6676775 := bstep (se 1 (by rfl) ⟨5007581, by rfl⟩ : syracuseStep 6676775 = 10015163) B10015163
theorem B2638151 : Blo 1758080 2638151 := bstep (se 1 (by rfl) ⟨1978613, by rfl⟩ : syracuseStep 2638151 = 3957227) B3957227
theorem B13361597 : Blo 1758080 13361597 := bstep (se 3 (by rfl) ⟨2505299, by rfl⟩ : syracuseStep 13361597 = 5010599) B5010599
theorem B162497177 : Blo 1758080 162497177 := bstep (se 2 (by rfl) ⟨60936441, by rfl⟩ : syracuseStep 162497177 = 121872883) B121872883
theorem B2114203 : Blo 1758080 2114203 := bstep (se 1 (by rfl) ⟨1585652, by rfl⟩ : syracuseStep 2114203 = 3171305) B3171305
theorem B2638505 : Blo 1758080 2638505 := bstep (se 2 (by rfl) ⟨989439, by rfl⟩ : syracuseStep 2638505 = 1978879) B1978879
theorem B38544167 : Blo 1758080 38544167 := bstep (se 1 (by rfl) ⟨28908125, by rfl⟩ : syracuseStep 38544167 = 57816251) B57816251
theorem B96535547 : Blo 1758080 96535547 := bstep (se 1 (by rfl) ⟨72401660, by rfl⟩ : syracuseStep 96535547 = 144803321) B144803321
theorem B3958379 : Blo 1758080 3958379 := bstep (se 1 (by rfl) ⟨2968784, by rfl⟩ : syracuseStep 3958379 = 5937569) B5937569
theorem B2639687 : Blo 1758080 2639687 := bstep (se 1 (by rfl) ⟨1979765, by rfl⟩ : syracuseStep 2639687 = 3959531) B3959531
theorem B2639867 : Blo 1758080 2639867 := bstep (se 1 (by rfl) ⟨1979900, by rfl⟩ : syracuseStep 2639867 = 3959801) B3959801
theorem B32983037 : Blo 1758080 32983037 := bstep (se 3 (by rfl) ⟨6184319, by rfl⟩ : syracuseStep 32983037 = 12368639) B12368639
theorem B2639963 : Blo 1758080 2639963 := bstep (se 1 (by rfl) ⟨1979972, by rfl⟩ : syracuseStep 2639963 = 3959945) B3959945
theorem B30066875 : Blo 1758080 30066875 := bstep (se 1 (by rfl) ⟨22550156, by rfl⟩ : syracuseStep 30066875 = 45100313) B45100313
theorem B3959081 : Blo 1758080 3959081 := bstep (se 2 (by rfl) ⟨1484655, by rfl⟩ : syracuseStep 3959081 = 2969311) B2969311
theorem B7514977 : Blo 1758080 7514977 := bstep (se 2 (by rfl) ⟨2818116, by rfl⟩ : syracuseStep 7514977 = 5636233) B5636233
theorem B3960071 : Blo 1758080 3960071 := bstep (se 1 (by rfl) ⟨2970053, by rfl⟩ : syracuseStep 3960071 = 5940107) B5940107
theorem B22540315 : Blo 1758080 22540315 := bstep (se 1 (by rfl) ⟨16905236, by rfl⟩ : syracuseStep 22540315 = 33810473) B33810473
theorem B5009951 : Blo 1758080 5009951 := bstep (se 1 (by rfl) ⟨3757463, by rfl⟩ : syracuseStep 5009951 = 7514927) B7514927
theorem B42865337 : Blo 1758080 42865337 := bstep (se 2 (by rfl) ⟨16074501, by rfl⟩ : syracuseStep 42865337 = 32149003) B32149003
theorem B30045005 : Blo 1758080 30045005 := bstep (se 3 (by rfl) ⟨5633438, by rfl⟩ : syracuseStep 30045005 = 11266877) B11266877
theorem B6681467 : Blo 1758080 6681467 := bstep (se 1 (by rfl) ⟨5011100, by rfl⟩ : syracuseStep 6681467 = 10022201) B10022201
theorem B10015913 : Blo 1758080 10015913 := bstep (se 2 (by rfl) ⟨3755967, by rfl⟩ : syracuseStep 10015913 = 7511935) B7511935
theorem B1758719 : Blo 1758080 1758719 := bstep (se 1 (by rfl) ⟨1319039, by rfl⟩ : syracuseStep 1758719 = 2638079) B2638079
theorem B1758879 : Blo 1758080 1758879 := bstep (se 1 (by rfl) ⟨1319159, by rfl⟩ : syracuseStep 1758879 = 2638319) B2638319
theorem B19019519 : Blo 1758080 19019519 := bstep (se 1 (by rfl) ⟨14264639, by rfl⟩ : syracuseStep 19019519 = 28529279) B28529279
theorem B3340415 : Blo 1758080 3340415 := bstep (se 1 (by rfl) ⟨2505311, by rfl⟩ : syracuseStep 3340415 = 5010623) B5010623
theorem B1759439 : Blo 1758080 1759439 := bstep (se 1 (by rfl) ⟨1319579, by rfl⟩ : syracuseStep 1759439 = 2639159) B2639159
theorem B1759487 : Blo 1758080 1759487 := bstep (se 1 (by rfl) ⟨1319615, by rfl⟩ : syracuseStep 1759487 = 2639231) B2639231
theorem B1759855 : Blo 1758080 1759855 := bstep (se 1 (by rfl) ⟨1319891, by rfl⟩ : syracuseStep 1759855 = 2639783) B2639783
theorem B128318093 : Blo 1758080 128318093 := bstep (se 3 (by rfl) ⟨24059642, by rfl⟩ : syracuseStep 128318093 = 48119285) B48119285
theorem B2637353 : Blo 1758080 2637353 := bstep (se 2 (by rfl) ⟨989007, by rfl⟩ : syracuseStep 2637353 = 1978015) B1978015
theorem B2637479 : Blo 1758080 2637479 := bstep (se 1 (by rfl) ⟨1978109, by rfl⟩ : syracuseStep 2637479 = 3956219) B3956219
theorem B108331451 : Blo 1758080 108331451 := bstep (se 1 (by rfl) ⟨81248588, by rfl⟩ : syracuseStep 108331451 = 162497177) B162497177
theorem B20030003 : Blo 1758080 20030003 := bstep (se 1 (by rfl) ⟨15022502, by rfl⟩ : syracuseStep 20030003 = 30045005) B30045005
theorem B64357031 : Blo 1758080 64357031 := bstep (se 1 (by rfl) ⟨48267773, by rfl⟩ : syracuseStep 64357031 = 96535547) B96535547
theorem B6677275 : Blo 1758080 6677275 := bstep (se 1 (by rfl) ⟨5007956, by rfl⟩ : syracuseStep 6677275 = 10015913) B10015913
theorem B2818937 : Blo 1758080 2818937 := bstep (se 2 (by rfl) ⟨1057101, by rfl⟩ : syracuseStep 2818937 = 2114203) B2114203
theorem B2638919 : Blo 1758080 2638919 := bstep (se 1 (by rfl) ⟨1979189, by rfl⟩ : syracuseStep 2638919 = 3958379) B3958379
theorem B10019969 : Blo 1758080 10019969 := bstep (se 2 (by rfl) ⟨3757488, by rfl⟩ : syracuseStep 10019969 = 7514977) B7514977
theorem B21988691 : Blo 1758080 21988691 := bstep (se 1 (by rfl) ⟨16491518, by rfl⟩ : syracuseStep 21988691 = 32983037) B32983037
theorem B2639387 : Blo 1758080 2639387 := bstep (se 1 (by rfl) ⟨1979540, by rfl⟩ : syracuseStep 2639387 = 3959081) B3959081
theorem B2640047 : Blo 1758080 2640047 := bstep (se 1 (by rfl) ⟨1980035, by rfl⟩ : syracuseStep 2640047 = 3960071) B3960071
theorem B24062831 : Blo 1758080 24062831 := bstep (se 1 (by rfl) ⟨18047123, by rfl⟩ : syracuseStep 24062831 = 36094247) B36094247
theorem B4451183 : Blo 1758080 4451183 := bstep (se 1 (by rfl) ⟨3338387, by rfl⟩ : syracuseStep 4451183 = 6676775) B6676775
theorem B8907731 : Blo 1758080 8907731 := bstep (se 1 (by rfl) ⟨6680798, by rfl⟩ : syracuseStep 8907731 = 13361597) B13361597
theorem B28576891 : Blo 1758080 28576891 := bstep (se 1 (by rfl) ⟨21432668, by rfl⟩ : syracuseStep 28576891 = 42865337) B42865337
theorem B85545395 : Blo 1758080 85545395 := bstep (se 1 (by rfl) ⟨64159046, by rfl⟩ : syracuseStep 85545395 = 128318093) B128318093
theorem B1758235 : Blo 1758080 1758235 := bstep (se 1 (by rfl) ⟨1318676, by rfl⟩ : syracuseStep 1758235 = 2637353) B2637353
theorem B1758319 : Blo 1758080 1758319 := bstep (se 1 (by rfl) ⟨1318739, by rfl⟩ : syracuseStep 1758319 = 2637479) B2637479
theorem B30053753 : Blo 1758080 30053753 := bstep (se 2 (by rfl) ⟨11270157, by rfl⟩ : syracuseStep 30053753 = 22540315) B22540315
theorem B1758767 : Blo 1758080 1758767 := bstep (se 1 (by rfl) ⟨1319075, by rfl⟩ : syracuseStep 1758767 = 2638151) B2638151
theorem B3339967 : Blo 1758080 3339967 := bstep (se 1 (by rfl) ⟨2504975, by rfl⟩ : syracuseStep 3339967 = 5009951) B5009951
theorem B1759003 : Blo 1758080 1759003 := bstep (se 1 (by rfl) ⟨1319252, by rfl⟩ : syracuseStep 1759003 = 2638505) B2638505
theorem B25696111 : Blo 1758080 25696111 := bstep (se 1 (by rfl) ⟨19272083, by rfl⟩ : syracuseStep 25696111 = 38544167) B38544167
theorem B4454311 : Blo 1758080 4454311 := bstep (se 1 (by rfl) ⟨3340733, by rfl⟩ : syracuseStep 4454311 = 6681467) B6681467
theorem B12679679 : Blo 1758080 12679679 := bstep (se 1 (by rfl) ⟨9509759, by rfl⟩ : syracuseStep 12679679 = 19019519) B19019519
theorem B1759791 : Blo 1758080 1759791 := bstep (se 1 (by rfl) ⟨1319843, by rfl⟩ : syracuseStep 1759791 = 2639687) B2639687
theorem B1759911 : Blo 1758080 1759911 := bstep (se 1 (by rfl) ⟨1319933, by rfl⟩ : syracuseStep 1759911 = 2639867) B2639867
theorem B1759975 : Blo 1758080 1759975 := bstep (se 1 (by rfl) ⟨1319981, by rfl⟩ : syracuseStep 1759975 = 2639963) B2639963
theorem B2226943 : Blo 1758080 2226943 := bstep (se 1 (by rfl) ⟨1670207, by rfl⟩ : syracuseStep 2226943 = 3340415) B3340415
theorem B20044583 : Blo 1758080 20044583 := bstep (se 1 (by rfl) ⟨15033437, by rfl⟩ : syracuseStep 20044583 = 30066875) B30066875
theorem B72220967 : Blo 1758080 72220967 := bstep (se 1 (by rfl) ⟨54165725, by rfl⟩ : syracuseStep 72220967 = 108331451) B108331451
theorem B13353335 : Blo 1758080 13353335 := bstep (se 1 (by rfl) ⟨10015001, by rfl⟩ : syracuseStep 13353335 = 20030003) B20030003
theorem B13363055 : Blo 1758080 13363055 := bstep (se 1 (by rfl) ⟨10022291, by rfl⟩ : syracuseStep 13363055 = 20044583) B20044583
theorem B16041887 : Blo 1758080 16041887 := bstep (se 1 (by rfl) ⟨12031415, by rfl⟩ : syracuseStep 16041887 = 24062831) B24062831
theorem B2967455 : Blo 1758080 2967455 := bstep (se 1 (by rfl) ⟨2225591, by rfl⟩ : syracuseStep 2967455 = 4451183) B4451183
theorem B34261481 : Blo 1758080 34261481 := bstep (se 2 (by rfl) ⟨12848055, by rfl⟩ : syracuseStep 34261481 = 25696111) B25696111
theorem B42904687 : Blo 1758080 42904687 := bstep (se 1 (by rfl) ⟨32178515, by rfl⟩ : syracuseStep 42904687 = 64357031) B64357031
theorem B1879291 : Blo 1758080 1879291 := bstep (se 1 (by rfl) ⟨1409468, by rfl⟩ : syracuseStep 1879291 = 2818937) B2818937
theorem B6679979 : Blo 1758080 6679979 := bstep (se 1 (by rfl) ⟨5009984, by rfl⟩ : syracuseStep 6679979 = 10019969) B10019969
theorem B14659127 : Blo 1758080 14659127 := bstep (se 1 (by rfl) ⟨10994345, by rfl⟩ : syracuseStep 14659127 = 21988691) B21988691
theorem B2969257 : Blo 1758080 2969257 := bstep (se 2 (by rfl) ⟨1113471, by rfl⟩ : syracuseStep 2969257 = 2226943) B2226943
theorem B33812477 : Blo 1758080 33812477 := bstep (se 3 (by rfl) ⟨6339839, by rfl⟩ : syracuseStep 33812477 = 12679679) B12679679
theorem B4453289 : Blo 1758080 4453289 := bstep (se 2 (by rfl) ⟨1669983, by rfl⟩ : syracuseStep 4453289 = 3339967) B3339967
theorem B57030263 : Blo 1758080 57030263 := bstep (se 1 (by rfl) ⟨42772697, by rfl⟩ : syracuseStep 57030263 = 85545395) B85545395
theorem B152410085 : Blo 1758080 152410085 := bstep (se 4 (by rfl) ⟨14288445, by rfl⟩ : syracuseStep 152410085 = 28576891) B28576891
theorem B1759279 : Blo 1758080 1759279 := bstep (se 1 (by rfl) ⟨1319459, by rfl⟩ : syracuseStep 1759279 = 2638919) B2638919
theorem B20035835 : Blo 1758080 20035835 := bstep (se 1 (by rfl) ⟨15026876, by rfl⟩ : syracuseStep 20035835 = 30053753) B30053753
theorem B1759591 : Blo 1758080 1759591 := bstep (se 1 (by rfl) ⟨1319693, by rfl⟩ : syracuseStep 1759591 = 2639387) B2639387
theorem B8903033 : Blo 1758080 8903033 := bstep (se 2 (by rfl) ⟨3338637, by rfl⟩ : syracuseStep 8903033 = 6677275) B6677275
theorem B1760031 : Blo 1758080 1760031 := bstep (se 1 (by rfl) ⟨1320023, by rfl⟩ : syracuseStep 1760031 = 2640047) B2640047
theorem B5938487 : Blo 1758080 5938487 := bstep (se 1 (by rfl) ⟨4453865, by rfl⟩ : syracuseStep 5938487 = 8907731) B8907731
theorem B5939081 : Blo 1758080 5939081 := bstep (se 2 (by rfl) ⟨2227155, by rfl⟩ : syracuseStep 5939081 = 4454311) B4454311
theorem B38020175 : Blo 1758080 38020175 := bstep (se 1 (by rfl) ⟨28515131, by rfl⟩ : syracuseStep 38020175 = 57030263) B57030263
theorem B101606723 : Blo 1758080 101606723 := bstep (se 1 (by rfl) ⟨76205042, by rfl⟩ : syracuseStep 101606723 = 152410085) B152410085
theorem B57206249 : Blo 1758080 57206249 := bstep (se 2 (by rfl) ⟨21452343, by rfl⟩ : syracuseStep 57206249 = 42904687) B42904687
theorem B22840987 : Blo 1758080 22840987 := bstep (se 1 (by rfl) ⟨17130740, by rfl⟩ : syracuseStep 22840987 = 34261481) B34261481
theorem B3958991 : Blo 1758080 3958991 := bstep (se 1 (by rfl) ⟨2969243, by rfl⟩ : syracuseStep 3958991 = 5938487) B5938487
theorem B3959009 : Blo 1758080 3959009 := bstep (se 2 (by rfl) ⟨1484628, by rfl⟩ : syracuseStep 3959009 = 2969257) B2969257
theorem B3959387 : Blo 1758080 3959387 := bstep (se 1 (by rfl) ⟨2969540, by rfl⟩ : syracuseStep 3959387 = 5939081) B5939081
theorem B48147311 : Blo 1758080 48147311 := bstep (se 1 (by rfl) ⟨36110483, by rfl⟩ : syracuseStep 48147311 = 72220967) B72220967
theorem B2968859 : Blo 1758080 2968859 := bstep (se 1 (by rfl) ⟨2226644, by rfl⟩ : syracuseStep 2968859 = 4453289) B4453289
theorem B8908703 : Blo 1758080 8908703 := bstep (se 1 (by rfl) ⟨6681527, by rfl⟩ : syracuseStep 8908703 = 13363055) B13363055
theorem B10694591 : Blo 1758080 10694591 := bstep (se 1 (by rfl) ⟨8020943, by rfl⟩ : syracuseStep 10694591 = 16041887) B16041887
theorem B1978303 : Blo 1758080 1978303 := bstep (se 1 (by rfl) ⟨1483727, by rfl⟩ : syracuseStep 1978303 = 2967455) B2967455
theorem B10022885 : Blo 1758080 10022885 := bstep (se 4 (by rfl) ⟨939645, by rfl⟩ : syracuseStep 10022885 = 1879291) B1879291
theorem B13357223 : Blo 1758080 13357223 := bstep (se 1 (by rfl) ⟨10017917, by rfl⟩ : syracuseStep 13357223 = 20035835) B20035835
theorem B5935355 : Blo 1758080 5935355 := bstep (se 1 (by rfl) ⟨4451516, by rfl⟩ : syracuseStep 5935355 = 8903033) B8903033
theorem B4453319 : Blo 1758080 4453319 := bstep (se 1 (by rfl) ⟨3339989, by rfl⟩ : syracuseStep 4453319 = 6679979) B6679979
theorem B22541651 : Blo 1758080 22541651 := bstep (se 1 (by rfl) ⟨16906238, by rfl⟩ : syracuseStep 22541651 = 33812477) B33812477
theorem B8902223 : Blo 1758080 8902223 := bstep (se 1 (by rfl) ⟨6676667, by rfl⟩ : syracuseStep 8902223 = 13353335) B13353335
theorem B9772751 : Blo 1758080 9772751 := bstep (se 1 (by rfl) ⟨7329563, by rfl⟩ : syracuseStep 9772751 = 14659127) B14659127
theorem B8904815 : Blo 1758080 8904815 := bstep (se 1 (by rfl) ⟨6678611, by rfl⟩ : syracuseStep 8904815 = 13357223) B13357223
theorem B3956903 : Blo 1758080 3956903 := bstep (se 1 (by rfl) ⟨2967677, by rfl⟩ : syracuseStep 3956903 = 5935355) B5935355
theorem B25346783 : Blo 1758080 25346783 := bstep (se 1 (by rfl) ⟨19010087, by rfl⟩ : syracuseStep 25346783 = 38020175) B38020175
theorem B2639327 : Blo 1758080 2639327 := bstep (se 1 (by rfl) ⟨1979495, by rfl⟩ : syracuseStep 2639327 = 3958991) B3958991
theorem B2639339 : Blo 1758080 2639339 := bstep (se 1 (by rfl) ⟨1979504, by rfl⟩ : syracuseStep 2639339 = 3959009) B3959009
theorem B2639591 : Blo 1758080 2639591 := bstep (se 1 (by rfl) ⟨1979693, by rfl⟩ : syracuseStep 2639591 = 3959387) B3959387
theorem B26060669 : Blo 1758080 26060669 := bstep (se 3 (by rfl) ⟨4886375, by rfl⟩ : syracuseStep 26060669 = 9772751) B9772751
theorem B32098207 : Blo 1758080 32098207 := bstep (se 1 (by rfl) ⟨24073655, by rfl⟩ : syracuseStep 32098207 = 48147311) B48147311
theorem B7129727 : Blo 1758080 7129727 := bstep (se 1 (by rfl) ⟨5347295, by rfl⟩ : syracuseStep 7129727 = 10694591) B10694591
theorem B2968879 : Blo 1758080 2968879 := bstep (se 1 (by rfl) ⟨2226659, by rfl⟩ : syracuseStep 2968879 = 4453319) B4453319
theorem B15027767 : Blo 1758080 15027767 := bstep (se 1 (by rfl) ⟨11270825, by rfl⟩ : syracuseStep 15027767 = 22541651) B22541651
theorem B38137499 : Blo 1758080 38137499 := bstep (se 1 (by rfl) ⟨28603124, by rfl⟩ : syracuseStep 38137499 = 57206249) B57206249
theorem B5934815 : Blo 1758080 5934815 := bstep (se 1 (by rfl) ⟨4451111, by rfl⟩ : syracuseStep 5934815 = 8902223) B8902223
theorem B1979239 : Blo 1758080 1979239 := bstep (se 1 (by rfl) ⟨1484429, by rfl⟩ : syracuseStep 1979239 = 2968859) B2968859
theorem B30454649 : Blo 1758080 30454649 := bstep (se 2 (by rfl) ⟨11420493, by rfl⟩ : syracuseStep 30454649 = 22840987) B22840987
theorem B6681923 : Blo 1758080 6681923 := bstep (se 1 (by rfl) ⟨5011442, by rfl⟩ : syracuseStep 6681923 = 10022885) B10022885
theorem B67737815 : Blo 1758080 67737815 := bstep (se 1 (by rfl) ⟨50803361, by rfl⟩ : syracuseStep 67737815 = 101606723) B101606723
theorem B2637737 : Blo 1758080 2637737 := bstep (se 2 (by rfl) ⟨989151, by rfl⟩ : syracuseStep 2637737 = 1978303) B1978303
theorem B5939135 : Blo 1758080 5939135 := bstep (se 1 (by rfl) ⟨4454351, by rfl⟩ : syracuseStep 5939135 = 8908703) B8908703
theorem B2637935 : Blo 1758080 2637935 := bstep (se 1 (by rfl) ⟨1978451, by rfl⟩ : syracuseStep 2637935 = 3956903) B3956903
theorem B2638985 : Blo 1758080 2638985 := bstep (se 2 (by rfl) ⟨989619, by rfl⟩ : syracuseStep 2638985 = 1979239) B1979239
theorem B3958505 : Blo 1758080 3958505 := bstep (se 2 (by rfl) ⟨1484439, by rfl⟩ : syracuseStep 3958505 = 2968879) B2968879
theorem B4753151 : Blo 1758080 4753151 := bstep (se 1 (by rfl) ⟨3564863, by rfl⟩ : syracuseStep 4753151 = 7129727) B7129727
theorem B42797609 : Blo 1758080 42797609 := bstep (se 2 (by rfl) ⟨16049103, by rfl⟩ : syracuseStep 42797609 = 32098207) B32098207
theorem B3959423 : Blo 1758080 3959423 := bstep (se 1 (by rfl) ⟨2969567, by rfl⟩ : syracuseStep 3959423 = 5939135) B5939135
theorem B20303099 : Blo 1758080 20303099 := bstep (se 1 (by rfl) ⟨15227324, by rfl⟩ : syracuseStep 20303099 = 30454649) B30454649
theorem B45158543 : Blo 1758080 45158543 := bstep (se 1 (by rfl) ⟨33868907, by rfl⟩ : syracuseStep 45158543 = 67737815) B67737815
theorem B25424999 : Blo 1758080 25424999 := bstep (se 1 (by rfl) ⟨19068749, by rfl⟩ : syracuseStep 25424999 = 38137499) B38137499
theorem B1758491 : Blo 1758080 1758491 := bstep (se 1 (by rfl) ⟨1318868, by rfl⟩ : syracuseStep 1758491 = 2637737) B2637737
theorem B5936543 : Blo 1758080 5936543 := bstep (se 1 (by rfl) ⟨4452407, by rfl⟩ : syracuseStep 5936543 = 8904815) B8904815
theorem B4454615 : Blo 1758080 4454615 := bstep (se 1 (by rfl) ⟨3340961, by rfl⟩ : syracuseStep 4454615 = 6681923) B6681923
theorem B1759551 : Blo 1758080 1759551 := bstep (se 1 (by rfl) ⟨1319663, by rfl⟩ : syracuseStep 1759551 = 2639327) B2639327
theorem B1759559 : Blo 1758080 1759559 := bstep (se 1 (by rfl) ⟨1319669, by rfl⟩ : syracuseStep 1759559 = 2639339) B2639339
theorem B1759727 : Blo 1758080 1759727 := bstep (se 1 (by rfl) ⟨1319795, by rfl⟩ : syracuseStep 1759727 = 2639591) B2639591
theorem B17373779 : Blo 1758080 17373779 := bstep (se 1 (by rfl) ⟨13030334, by rfl⟩ : syracuseStep 17373779 = 26060669) B26060669
theorem B67591421 : Blo 1758080 67591421 := bstep (se 3 (by rfl) ⟨12673391, by rfl⟩ : syracuseStep 67591421 = 25346783) B25346783
theorem B10018511 : Blo 1758080 10018511 := bstep (se 1 (by rfl) ⟨7513883, by rfl⟩ : syracuseStep 10018511 = 15027767) B15027767
theorem B3956543 : Blo 1758080 3956543 := bstep (se 1 (by rfl) ⟨2967407, by rfl⟩ : syracuseStep 3956543 = 5934815) B5934815
theorem B30105695 : Blo 1758080 30105695 := bstep (se 1 (by rfl) ⟨22579271, by rfl⟩ : syracuseStep 30105695 = 45158543) B45158543
theorem B16949999 : Blo 1758080 16949999 := bstep (se 1 (by rfl) ⟨12712499, by rfl⟩ : syracuseStep 16949999 = 25424999) B25424999
theorem B3957695 : Blo 1758080 3957695 := bstep (se 1 (by rfl) ⟨2968271, by rfl⟩ : syracuseStep 3957695 = 5936543) B5936543
theorem B2639003 : Blo 1758080 2639003 := bstep (se 1 (by rfl) ⟨1979252, by rfl⟩ : syracuseStep 2639003 = 3958505) B3958505
theorem B2639615 : Blo 1758080 2639615 := bstep (se 1 (by rfl) ⟨1979711, by rfl⟩ : syracuseStep 2639615 = 3959423) B3959423
theorem B13535399 : Blo 1758080 13535399 := bstep (se 1 (by rfl) ⟨10151549, by rfl⟩ : syracuseStep 13535399 = 20303099) B20303099
theorem B6679007 : Blo 1758080 6679007 := bstep (se 1 (by rfl) ⟨5009255, by rfl⟩ : syracuseStep 6679007 = 10018511) B10018511
theorem B2969743 : Blo 1758080 2969743 := bstep (se 1 (by rfl) ⟨2227307, by rfl⟩ : syracuseStep 2969743 = 4454615) B4454615
theorem B45060947 : Blo 1758080 45060947 := bstep (se 1 (by rfl) ⟨33795710, by rfl⟩ : syracuseStep 45060947 = 67591421) B67591421
theorem B1758623 : Blo 1758080 1758623 := bstep (se 1 (by rfl) ⟨1318967, by rfl⟩ : syracuseStep 1758623 = 2637935) B2637935
theorem B1759323 : Blo 1758080 1759323 := bstep (se 1 (by rfl) ⟨1319492, by rfl⟩ : syracuseStep 1759323 = 2638985) B2638985
theorem B3168767 : Blo 1758080 3168767 := bstep (se 1 (by rfl) ⟨2376575, by rfl⟩ : syracuseStep 3168767 = 4753151) B4753151
theorem B28531739 : Blo 1758080 28531739 := bstep (se 1 (by rfl) ⟨21398804, by rfl⟩ : syracuseStep 28531739 = 42797609) B42797609
theorem B11582519 : Blo 1758080 11582519 := bstep (se 1 (by rfl) ⟨8686889, by rfl⟩ : syracuseStep 11582519 = 17373779) B17373779
theorem B2637695 : Blo 1758080 2637695 := bstep (se 1 (by rfl) ⟨1978271, by rfl⟩ : syracuseStep 2637695 = 3956543) B3956543
theorem B80281853 : Blo 1758080 80281853 := bstep (se 3 (by rfl) ⟨15052847, by rfl⟩ : syracuseStep 80281853 = 30105695) B30105695
theorem B30040631 : Blo 1758080 30040631 := bstep (se 1 (by rfl) ⟨22530473, by rfl⟩ : syracuseStep 30040631 = 45060947) B45060947
theorem B2638463 : Blo 1758080 2638463 := bstep (se 1 (by rfl) ⟨1978847, by rfl⟩ : syracuseStep 2638463 = 3957695) B3957695
theorem B3959657 : Blo 1758080 3959657 := bstep (se 2 (by rfl) ⟨1484871, by rfl⟩ : syracuseStep 3959657 = 2969743) B2969743
theorem B11299999 : Blo 1758080 11299999 := bstep (se 1 (by rfl) ⟨8474999, by rfl⟩ : syracuseStep 11299999 = 16949999) B16949999
theorem B123546869 : Blo 1758080 123546869 := bstep (se 5 (by rfl) ⟨5791259, by rfl⟩ : syracuseStep 123546869 = 11582519) B11582519
theorem B8450045 : Blo 1758080 8450045 := bstep (se 3 (by rfl) ⟨1584383, by rfl⟩ : syracuseStep 8450045 = 3168767) B3168767
theorem B9023599 : Blo 1758080 9023599 := bstep (se 1 (by rfl) ⟨6767699, by rfl⟩ : syracuseStep 9023599 = 13535399) B13535399
theorem B4452671 : Blo 1758080 4452671 := bstep (se 1 (by rfl) ⟨3339503, by rfl⟩ : syracuseStep 4452671 = 6679007) B6679007
theorem B1758463 : Blo 1758080 1758463 := bstep (se 1 (by rfl) ⟨1318847, by rfl⟩ : syracuseStep 1758463 = 2637695) B2637695
theorem B1759335 : Blo 1758080 1759335 := bstep (se 1 (by rfl) ⟨1319501, by rfl⟩ : syracuseStep 1759335 = 2639003) B2639003
theorem B1759743 : Blo 1758080 1759743 := bstep (se 1 (by rfl) ⟨1319807, by rfl⟩ : syracuseStep 1759743 = 2639615) B2639615
theorem B19021159 : Blo 1758080 19021159 := bstep (se 1 (by rfl) ⟨14265869, by rfl⟩ : syracuseStep 19021159 = 28531739) B28531739
theorem B15066665 : Blo 1758080 15066665 := bstep (se 2 (by rfl) ⟨5649999, by rfl⟩ : syracuseStep 15066665 = 11299999) B11299999
theorem B2639771 : Blo 1758080 2639771 := bstep (se 1 (by rfl) ⟨1979828, by rfl⟩ : syracuseStep 2639771 = 3959657) B3959657
theorem B82364579 : Blo 1758080 82364579 := bstep (se 1 (by rfl) ⟨61773434, by rfl⟩ : syracuseStep 82364579 = 123546869) B123546869
theorem B53521235 : Blo 1758080 53521235 := bstep (se 1 (by rfl) ⟨40140926, by rfl⟩ : syracuseStep 53521235 = 80281853) B80281853
theorem B2968447 : Blo 1758080 2968447 := bstep (se 1 (by rfl) ⟨2226335, by rfl⟩ : syracuseStep 2968447 = 4452671) B4452671
theorem B101446181 : Blo 1758080 101446181 := bstep (se 4 (by rfl) ⟨9510579, by rfl⟩ : syracuseStep 101446181 = 19021159) B19021159
theorem B5633363 : Blo 1758080 5633363 := bstep (se 1 (by rfl) ⟨4225022, by rfl⟩ : syracuseStep 5633363 = 8450045) B8450045
theorem B12031465 : Blo 1758080 12031465 := bstep (se 2 (by rfl) ⟨4511799, by rfl⟩ : syracuseStep 12031465 = 9023599) B9023599
theorem B20027087 : Blo 1758080 20027087 := bstep (se 1 (by rfl) ⟨15020315, by rfl⟩ : syracuseStep 20027087 = 30040631) B30040631
theorem B1758975 : Blo 1758080 1758975 := bstep (se 1 (by rfl) ⟨1319231, by rfl⟩ : syracuseStep 1758975 = 2638463) B2638463
theorem B10044443 : Blo 1758080 10044443 := bstep (se 1 (by rfl) ⟨7533332, by rfl⟩ : syracuseStep 10044443 = 15066665) B15066665
theorem B3957929 : Blo 1758080 3957929 := bstep (se 2 (by rfl) ⟨1484223, by rfl⟩ : syracuseStep 3957929 = 2968447) B2968447
theorem B16041953 : Blo 1758080 16041953 := bstep (se 2 (by rfl) ⟨6015732, by rfl⟩ : syracuseStep 16041953 = 12031465) B12031465
theorem B3755575 : Blo 1758080 3755575 := bstep (se 1 (by rfl) ⟨2816681, by rfl⟩ : syracuseStep 3755575 = 5633363) B5633363
theorem B35680823 : Blo 1758080 35680823 := bstep (se 1 (by rfl) ⟨26760617, by rfl⟩ : syracuseStep 35680823 = 53521235) B53521235
theorem B67630787 : Blo 1758080 67630787 := bstep (se 1 (by rfl) ⟨50723090, by rfl⟩ : syracuseStep 67630787 = 101446181) B101446181
theorem B13351391 : Blo 1758080 13351391 := bstep (se 1 (by rfl) ⟨10013543, by rfl⟩ : syracuseStep 13351391 = 20027087) B20027087
theorem B1759847 : Blo 1758080 1759847 := bstep (se 1 (by rfl) ⟨1319885, by rfl⟩ : syracuseStep 1759847 = 2639771) B2639771
theorem B54909719 : Blo 1758080 54909719 := bstep (se 1 (by rfl) ⟨41182289, by rfl⟩ : syracuseStep 54909719 = 82364579) B82364579
theorem B2638619 : Blo 1758080 2638619 := bstep (se 1 (by rfl) ⟨1978964, by rfl⟩ : syracuseStep 2638619 = 3957929) B3957929
theorem B5007433 : Blo 1758080 5007433 := bstep (se 2 (by rfl) ⟨1877787, by rfl⟩ : syracuseStep 5007433 = 3755575) B3755575
theorem B10694635 : Blo 1758080 10694635 := bstep (se 1 (by rfl) ⟨8020976, by rfl⟩ : syracuseStep 10694635 = 16041953) B16041953
theorem B8900927 : Blo 1758080 8900927 := bstep (se 1 (by rfl) ⟨6675695, by rfl⟩ : syracuseStep 8900927 = 13351391) B13351391
theorem B36606479 : Blo 1758080 36606479 := bstep (se 1 (by rfl) ⟨27454859, by rfl⟩ : syracuseStep 36606479 = 54909719) B54909719
theorem B26785181 : Blo 1758080 26785181 := bstep (se 3 (by rfl) ⟨5022221, by rfl⟩ : syracuseStep 26785181 = 10044443) B10044443
theorem B23787215 : Blo 1758080 23787215 := bstep (se 1 (by rfl) ⟨17840411, by rfl⟩ : syracuseStep 23787215 = 35680823) B35680823
theorem B45087191 : Blo 1758080 45087191 := bstep (se 1 (by rfl) ⟨33815393, by rfl⟩ : syracuseStep 45087191 = 67630787) B67630787
theorem B6676577 : Blo 1758080 6676577 := bstep (se 2 (by rfl) ⟨2503716, by rfl⟩ : syracuseStep 6676577 = 5007433) B5007433
theorem B97617277 : Blo 1758080 97617277 := bstep (se 3 (by rfl) ⟨18303239, by rfl⟩ : syracuseStep 97617277 = 36606479) B36606479
theorem B30058127 : Blo 1758080 30058127 := bstep (se 1 (by rfl) ⟨22543595, by rfl⟩ : syracuseStep 30058127 = 45087191) B45087191
theorem B5933951 : Blo 1758080 5933951 := bstep (se 1 (by rfl) ⟨4450463, by rfl⟩ : syracuseStep 5933951 = 8900927) B8900927
theorem B57038053 : Blo 1758080 57038053 := bstep (se 4 (by rfl) ⟨5347317, by rfl⟩ : syracuseStep 57038053 = 10694635) B10694635
theorem B1759079 : Blo 1758080 1759079 := bstep (se 1 (by rfl) ⟨1319309, by rfl⟩ : syracuseStep 1759079 = 2638619) B2638619
theorem B17856787 : Blo 1758080 17856787 := bstep (se 1 (by rfl) ⟨13392590, by rfl⟩ : syracuseStep 17856787 = 26785181) B26785181
theorem B15858143 : Blo 1758080 15858143 := bstep (se 1 (by rfl) ⟨11893607, by rfl⟩ : syracuseStep 15858143 = 23787215) B23787215
theorem B20038751 : Blo 1758080 20038751 := bstep (se 1 (by rfl) ⟨15029063, by rfl⟩ : syracuseStep 20038751 = 30058127) B30058127
theorem B4451051 : Blo 1758080 4451051 := bstep (se 1 (by rfl) ⟨3338288, by rfl⟩ : syracuseStep 4451051 = 6676577) B6676577
theorem B23809049 : Blo 1758080 23809049 := bstep (se 2 (by rfl) ⟨8928393, by rfl⟩ : syracuseStep 23809049 = 17856787) B17856787
theorem B76050737 : Blo 1758080 76050737 := bstep (se 2 (by rfl) ⟨28519026, by rfl⟩ : syracuseStep 76050737 = 57038053) B57038053
theorem B10572095 : Blo 1758080 10572095 := bstep (se 1 (by rfl) ⟨7929071, by rfl⟩ : syracuseStep 10572095 = 15858143) B15858143
theorem B3955967 : Blo 1758080 3955967 := bstep (se 1 (by rfl) ⟨2966975, by rfl⟩ : syracuseStep 3955967 = 5933951) B5933951
theorem B520625477 : Blo 1758080 520625477 := bstep (se 4 (by rfl) ⟨48808638, by rfl⟩ : syracuseStep 520625477 = 97617277) B97617277
theorem B50700491 : Blo 1758080 50700491 := bstep (se 1 (by rfl) ⟨38025368, by rfl⟩ : syracuseStep 50700491 = 76050737) B76050737
theorem B2967367 : Blo 1758080 2967367 := bstep (se 1 (by rfl) ⟨2225525, by rfl⟩ : syracuseStep 2967367 = 4451051) B4451051
theorem B7048063 : Blo 1758080 7048063 := bstep (se 1 (by rfl) ⟨5286047, by rfl⟩ : syracuseStep 7048063 = 10572095) B10572095
theorem B15872699 : Blo 1758080 15872699 := bstep (se 1 (by rfl) ⟨11904524, by rfl⟩ : syracuseStep 15872699 = 23809049) B23809049
theorem B347083651 : Blo 1758080 347083651 := bstep (se 1 (by rfl) ⟨260312738, by rfl⟩ : syracuseStep 347083651 = 520625477) B520625477
theorem B13359167 : Blo 1758080 13359167 := bstep (se 1 (by rfl) ⟨10019375, by rfl⟩ : syracuseStep 13359167 = 20038751) B20038751
theorem B2637311 : Blo 1758080 2637311 := bstep (se 1 (by rfl) ⟨1977983, by rfl⟩ : syracuseStep 2637311 = 3955967) B3955967
theorem B33800327 : Blo 1758080 33800327 := bstep (se 1 (by rfl) ⟨25350245, by rfl⟩ : syracuseStep 33800327 = 50700491) B50700491
theorem B9397417 : Blo 1758080 9397417 := bstep (se 2 (by rfl) ⟨3524031, by rfl⟩ : syracuseStep 9397417 = 7048063) B7048063
theorem B8906111 : Blo 1758080 8906111 := bstep (se 1 (by rfl) ⟨6679583, by rfl⟩ : syracuseStep 8906111 = 13359167) B13359167
theorem B462778201 : Blo 1758080 462778201 := bstep (se 2 (by rfl) ⟨173541825, by rfl⟩ : syracuseStep 462778201 = 347083651) B347083651
theorem B1758207 : Blo 1758080 1758207 := bstep (se 1 (by rfl) ⟨1318655, by rfl⟩ : syracuseStep 1758207 = 2637311) B2637311
theorem B42327197 : Blo 1758080 42327197 := bstep (se 3 (by rfl) ⟨7936349, by rfl⟩ : syracuseStep 42327197 = 15872699) B15872699
theorem B3956489 : Blo 1758080 3956489 := bstep (se 2 (by rfl) ⟨1483683, by rfl⟩ : syracuseStep 3956489 = 2967367) B2967367
theorem B12529889 : Blo 1758080 12529889 := bstep (se 2 (by rfl) ⟨4698708, by rfl⟩ : syracuseStep 12529889 = 9397417) B9397417
theorem B28218131 : Blo 1758080 28218131 := bstep (se 1 (by rfl) ⟨21163598, by rfl⟩ : syracuseStep 28218131 = 42327197) B42327197
theorem B22533551 : Blo 1758080 22533551 := bstep (se 1 (by rfl) ⟨16900163, by rfl⟩ : syracuseStep 22533551 = 33800327) B33800327
theorem B5937407 : Blo 1758080 5937407 := bstep (se 1 (by rfl) ⟨4453055, by rfl⟩ : syracuseStep 5937407 = 8906111) B8906111
theorem B617037601 : Blo 1758080 617037601 := bstep (se 2 (by rfl) ⟨231389100, by rfl⟩ : syracuseStep 617037601 = 462778201) B462778201
theorem B2637659 : Blo 1758080 2637659 := bstep (se 1 (by rfl) ⟨1978244, by rfl⟩ : syracuseStep 2637659 = 3956489) B3956489
theorem B3958271 : Blo 1758080 3958271 := bstep (se 1 (by rfl) ⟨2968703, by rfl⟩ : syracuseStep 3958271 = 5937407) B5937407
theorem B822716801 : Blo 1758080 822716801 := bstep (se 2 (by rfl) ⟨308518800, by rfl⟩ : syracuseStep 822716801 = 617037601) B617037601
theorem B18812087 : Blo 1758080 18812087 := bstep (se 1 (by rfl) ⟨14109065, by rfl⟩ : syracuseStep 18812087 = 28218131) B28218131
theorem B1758439 : Blo 1758080 1758439 := bstep (se 1 (by rfl) ⟨1318829, by rfl⟩ : syracuseStep 1758439 = 2637659) B2637659
theorem B8353259 : Blo 1758080 8353259 := bstep (se 1 (by rfl) ⟨6264944, by rfl⟩ : syracuseStep 8353259 = 12529889) B12529889
theorem B15022367 : Blo 1758080 15022367 := bstep (se 1 (by rfl) ⟨11266775, by rfl⟩ : syracuseStep 15022367 = 22533551) B22533551
theorem B2638847 : Blo 1758080 2638847 := bstep (se 1 (by rfl) ⟨1979135, by rfl⟩ : syracuseStep 2638847 = 3958271) B3958271
theorem B10014911 : Blo 1758080 10014911 := bstep (se 1 (by rfl) ⟨7511183, by rfl⟩ : syracuseStep 10014911 = 15022367) B15022367
theorem B5568839 : Blo 1758080 5568839 := bstep (se 1 (by rfl) ⟨4176629, by rfl⟩ : syracuseStep 5568839 = 8353259) B8353259
theorem B548477867 : Blo 1758080 548477867 := bstep (se 1 (by rfl) ⟨411358400, by rfl⟩ : syracuseStep 548477867 = 822716801) B822716801
theorem B12541391 : Blo 1758080 12541391 := bstep (se 1 (by rfl) ⟨9406043, by rfl⟩ : syracuseStep 12541391 = 18812087) B18812087
theorem B6676607 : Blo 1758080 6676607 := bstep (se 1 (by rfl) ⟨5007455, by rfl⟩ : syracuseStep 6676607 = 10014911) B10014911
theorem B3712559 : Blo 1758080 3712559 := bstep (se 1 (by rfl) ⟨2784419, by rfl⟩ : syracuseStep 3712559 = 5568839) B5568839
theorem B365651911 : Blo 1758080 365651911 := bstep (se 1 (by rfl) ⟨274238933, by rfl⟩ : syracuseStep 365651911 = 548477867) B548477867
theorem B8360927 : Blo 1758080 8360927 := bstep (se 1 (by rfl) ⟨6270695, by rfl⟩ : syracuseStep 8360927 = 12541391) B12541391
theorem B1759231 : Blo 1758080 1759231 := bstep (se 1 (by rfl) ⟨1319423, by rfl⟩ : syracuseStep 1759231 = 2638847) B2638847
theorem B4451071 : Blo 1758080 4451071 := bstep (se 1 (by rfl) ⟨3338303, by rfl⟩ : syracuseStep 4451071 = 6676607) B6676607
theorem B5573951 : Blo 1758080 5573951 := bstep (se 1 (by rfl) ⟨4180463, by rfl⟩ : syracuseStep 5573951 = 8360927) B8360927
theorem B9900157 : Blo 1758080 9900157 := bstep (se 3 (by rfl) ⟨1856279, by rfl⟩ : syracuseStep 9900157 = 3712559) B3712559
theorem B487535881 : Blo 1758080 487535881 := bstep (se 2 (by rfl) ⟨182825955, by rfl⟩ : syracuseStep 487535881 = 365651911) B365651911
theorem B13200209 : Blo 1758080 13200209 := bstep (se 2 (by rfl) ⟨4950078, by rfl⟩ : syracuseStep 13200209 = 9900157) B9900157
theorem B5934761 : Blo 1758080 5934761 := bstep (se 2 (by rfl) ⟨2225535, by rfl⟩ : syracuseStep 5934761 = 4451071) B4451071
theorem B650047841 : Blo 1758080 650047841 := bstep (se 2 (by rfl) ⟨243767940, by rfl⟩ : syracuseStep 650047841 = 487535881) B487535881
theorem B3715967 : Blo 1758080 3715967 := bstep (se 1 (by rfl) ⟨2786975, by rfl⟩ : syracuseStep 3715967 = 5573951) B5573951
theorem B433365227 : Blo 1758080 433365227 := bstep (se 1 (by rfl) ⟨325023920, by rfl⟩ : syracuseStep 433365227 = 650047841) B650047841
theorem B8800139 : Blo 1758080 8800139 := bstep (se 1 (by rfl) ⟨6600104, by rfl⟩ : syracuseStep 8800139 = 13200209) B13200209
theorem B2477311 : Blo 1758080 2477311 := bstep (se 1 (by rfl) ⟨1857983, by rfl⟩ : syracuseStep 2477311 = 3715967) B3715967
theorem B3956507 : Blo 1758080 3956507 := bstep (se 1 (by rfl) ⟨2967380, by rfl⟩ : syracuseStep 3956507 = 5934761) B5934761
theorem B5866759 : Blo 1758080 5866759 := bstep (se 1 (by rfl) ⟨4400069, by rfl⟩ : syracuseStep 5866759 = 8800139) B8800139
theorem B288910151 : Blo 1758080 288910151 := bstep (se 1 (by rfl) ⟨216682613, by rfl⟩ : syracuseStep 288910151 = 433365227) B433365227
theorem B13212325 : Blo 1758080 13212325 := bstep (se 4 (by rfl) ⟨1238655, by rfl⟩ : syracuseStep 13212325 = 2477311) B2477311
theorem B2637671 : Blo 1758080 2637671 := bstep (se 1 (by rfl) ⟨1978253, by rfl⟩ : syracuseStep 2637671 = 3956507) B3956507
theorem B192606767 : Blo 1758080 192606767 := bstep (se 1 (by rfl) ⟨144455075, by rfl⟩ : syracuseStep 192606767 = 288910151) B288910151
theorem B1758447 : Blo 1758080 1758447 := bstep (se 1 (by rfl) ⟨1318835, by rfl⟩ : syracuseStep 1758447 = 2637671) B2637671
theorem B70465733 : Blo 1758080 70465733 := bstep (se 4 (by rfl) ⟨6606162, by rfl⟩ : syracuseStep 70465733 = 13212325) B13212325
theorem B7822345 : Blo 1758080 7822345 := bstep (se 2 (by rfl) ⟨2933379, by rfl⟩ : syracuseStep 7822345 = 5866759) B5866759
theorem B10429793 : Blo 1758080 10429793 := bstep (se 2 (by rfl) ⟨3911172, by rfl⟩ : syracuseStep 10429793 = 7822345) B7822345
theorem B128404511 : Blo 1758080 128404511 := bstep (se 1 (by rfl) ⟨96303383, by rfl⟩ : syracuseStep 128404511 = 192606767) B192606767
theorem B46977155 : Blo 1758080 46977155 := bstep (se 1 (by rfl) ⟨35232866, by rfl⟩ : syracuseStep 46977155 = 70465733) B70465733
theorem B31318103 : Blo 1758080 31318103 := bstep (se 1 (by rfl) ⟨23488577, by rfl⟩ : syracuseStep 31318103 = 46977155) B46977155
theorem B85603007 : Blo 1758080 85603007 := bstep (se 1 (by rfl) ⟨64202255, by rfl⟩ : syracuseStep 85603007 = 128404511) B128404511
theorem B6953195 : Blo 1758080 6953195 := bstep (se 1 (by rfl) ⟨5214896, by rfl⟩ : syracuseStep 6953195 = 10429793) B10429793
theorem B57068671 : Blo 1758080 57068671 := bstep (se 1 (by rfl) ⟨42801503, by rfl⟩ : syracuseStep 57068671 = 85603007) B85603007
theorem B20878735 : Blo 1758080 20878735 := bstep (se 1 (by rfl) ⟨15659051, by rfl⟩ : syracuseStep 20878735 = 31318103) B31318103
theorem B4635463 : Blo 1758080 4635463 := bstep (se 1 (by rfl) ⟨3476597, by rfl⟩ : syracuseStep 4635463 = 6953195) B6953195
theorem B27838313 : Blo 1758080 27838313 := bstep (se 2 (by rfl) ⟨10439367, by rfl⟩ : syracuseStep 27838313 = 20878735) B20878735
theorem B6180617 : Blo 1758080 6180617 := bstep (se 2 (by rfl) ⟨2317731, by rfl⟩ : syracuseStep 6180617 = 4635463) B4635463
theorem B76091561 : Blo 1758080 76091561 := bstep (se 2 (by rfl) ⟨28534335, by rfl⟩ : syracuseStep 76091561 = 57068671) B57068671
theorem B50727707 : Blo 1758080 50727707 := bstep (se 1 (by rfl) ⟨38045780, by rfl⟩ : syracuseStep 50727707 = 76091561) B76091561
theorem B18558875 : Blo 1758080 18558875 := bstep (se 1 (by rfl) ⟨13919156, by rfl⟩ : syracuseStep 18558875 = 27838313) B27838313
theorem B4120411 : Blo 1758080 4120411 := bstep (se 1 (by rfl) ⟨3090308, by rfl⟩ : syracuseStep 4120411 = 6180617) B6180617
theorem B33818471 : Blo 1758080 33818471 := bstep (se 1 (by rfl) ⟨25363853, by rfl⟩ : syracuseStep 33818471 = 50727707) B50727707
theorem B12372583 : Blo 1758080 12372583 := bstep (se 1 (by rfl) ⟨9279437, by rfl⟩ : syracuseStep 12372583 = 18558875) B18558875
theorem B5493881 : Blo 1758080 5493881 := bstep (se 2 (by rfl) ⟨2060205, by rfl⟩ : syracuseStep 5493881 = 4120411) B4120411
theorem B3662587 : Blo 1758080 3662587 := bstep (se 1 (by rfl) ⟨2746940, by rfl⟩ : syracuseStep 3662587 = 5493881) B5493881
theorem B22545647 : Blo 1758080 22545647 := bstep (se 1 (by rfl) ⟨16909235, by rfl⟩ : syracuseStep 22545647 = 33818471) B33818471
theorem B16496777 : Blo 1758080 16496777 := bstep (se 2 (by rfl) ⟨6186291, by rfl⟩ : syracuseStep 16496777 = 12372583) B12372583
theorem B19533797 : Blo 1758080 19533797 := bstep (se 4 (by rfl) ⟨1831293, by rfl⟩ : syracuseStep 19533797 = 3662587) B3662587
theorem B10997851 : Blo 1758080 10997851 := bstep (se 1 (by rfl) ⟨8248388, by rfl⟩ : syracuseStep 10997851 = 16496777) B16496777
theorem B15030431 : Blo 1758080 15030431 := bstep (se 1 (by rfl) ⟨11272823, by rfl⟩ : syracuseStep 15030431 = 22545647) B22545647
theorem B14663801 : Blo 1758080 14663801 := bstep (se 2 (by rfl) ⟨5498925, by rfl⟩ : syracuseStep 14663801 = 10997851) B10997851
theorem B10020287 : Blo 1758080 10020287 := bstep (se 1 (by rfl) ⟨7515215, by rfl⟩ : syracuseStep 10020287 = 15030431) B15030431
theorem B13022531 : Blo 1758080 13022531 := bstep (se 1 (by rfl) ⟨9766898, by rfl⟩ : syracuseStep 13022531 = 19533797) B19533797
theorem B39103469 : Blo 1758080 39103469 := bstep (se 3 (by rfl) ⟨7331900, by rfl⟩ : syracuseStep 39103469 = 14663801) B14663801
theorem B6680191 : Blo 1758080 6680191 := bstep (se 1 (by rfl) ⟨5010143, by rfl⟩ : syracuseStep 6680191 = 10020287) B10020287
theorem B8681687 : Blo 1758080 8681687 := bstep (se 1 (by rfl) ⟨6511265, by rfl⟩ : syracuseStep 8681687 = 13022531) B13022531
theorem B26068979 : Blo 1758080 26068979 := bstep (se 1 (by rfl) ⟨19551734, by rfl⟩ : syracuseStep 26068979 = 39103469) B39103469
theorem B8906921 : Blo 1758080 8906921 := bstep (se 2 (by rfl) ⟨3340095, by rfl⟩ : syracuseStep 8906921 = 6680191) B6680191
theorem B5787791 : Blo 1758080 5787791 := bstep (se 1 (by rfl) ⟨4340843, by rfl⟩ : syracuseStep 5787791 = 8681687) B8681687
theorem B3858527 : Blo 1758080 3858527 := bstep (se 1 (by rfl) ⟨2893895, by rfl⟩ : syracuseStep 3858527 = 5787791) B5787791
theorem B17379319 : Blo 1758080 17379319 := bstep (se 1 (by rfl) ⟨13034489, by rfl⟩ : syracuseStep 17379319 = 26068979) B26068979
theorem B5937947 : Blo 1758080 5937947 := bstep (se 1 (by rfl) ⟨4453460, by rfl⟩ : syracuseStep 5937947 = 8906921) B8906921
theorem B10289405 : Blo 1758080 10289405 := bstep (se 3 (by rfl) ⟨1929263, by rfl⟩ : syracuseStep 10289405 = 3858527) B3858527
theorem B3958631 : Blo 1758080 3958631 := bstep (se 1 (by rfl) ⟨2968973, by rfl⟩ : syracuseStep 3958631 = 5937947) B5937947
theorem B23172425 : Blo 1758080 23172425 := bstep (se 2 (by rfl) ⟨8689659, by rfl⟩ : syracuseStep 23172425 = 17379319) B17379319
theorem B2639087 : Blo 1758080 2639087 := bstep (se 1 (by rfl) ⟨1979315, by rfl⟩ : syracuseStep 2639087 = 3958631) B3958631
theorem B6859603 : Blo 1758080 6859603 := bstep (se 1 (by rfl) ⟨5144702, by rfl⟩ : syracuseStep 6859603 = 10289405) B10289405
theorem B15448283 : Blo 1758080 15448283 := bstep (se 1 (by rfl) ⟨11586212, by rfl⟩ : syracuseStep 15448283 = 23172425) B23172425
theorem B10298855 : Blo 1758080 10298855 := bstep (se 1 (by rfl) ⟨7724141, by rfl⟩ : syracuseStep 10298855 = 15448283) B15448283
theorem B9146137 : Blo 1758080 9146137 := bstep (se 2 (by rfl) ⟨3429801, by rfl⟩ : syracuseStep 9146137 = 6859603) B6859603
theorem B1759391 : Blo 1758080 1759391 := bstep (se 1 (by rfl) ⟨1319543, by rfl⟩ : syracuseStep 1759391 = 2639087) B2639087
theorem B6865903 : Blo 1758080 6865903 := bstep (se 1 (by rfl) ⟨5149427, by rfl⟩ : syracuseStep 6865903 = 10298855) B10298855
theorem B12194849 : Blo 1758080 12194849 := bstep (se 2 (by rfl) ⟨4573068, by rfl⟩ : syracuseStep 12194849 = 9146137) B9146137
theorem B8129899 : Blo 1758080 8129899 := bstep (se 1 (by rfl) ⟨6097424, by rfl⟩ : syracuseStep 8129899 = 12194849) B12194849
theorem B36618149 : Blo 1758080 36618149 := bstep (se 4 (by rfl) ⟨3432951, by rfl⟩ : syracuseStep 36618149 = 6865903) B6865903
theorem B10839865 : Blo 1758080 10839865 := bstep (se 2 (by rfl) ⟨4064949, by rfl⟩ : syracuseStep 10839865 = 8129899) B8129899
theorem B24412099 : Blo 1758080 24412099 := bstep (se 1 (by rfl) ⟨18309074, by rfl⟩ : syracuseStep 24412099 = 36618149) B36618149
theorem B14453153 : Blo 1758080 14453153 := bstep (se 2 (by rfl) ⟨5419932, by rfl⟩ : syracuseStep 14453153 = 10839865) B10839865
theorem B32549465 : Blo 1758080 32549465 := bstep (se 2 (by rfl) ⟨12206049, by rfl⟩ : syracuseStep 32549465 = 24412099) B24412099
theorem B9635435 : Blo 1758080 9635435 := bstep (se 1 (by rfl) ⟨7226576, by rfl⟩ : syracuseStep 9635435 = 14453153) B14453153
theorem B86798573 : Blo 1758080 86798573 := bstep (se 3 (by rfl) ⟨16274732, by rfl⟩ : syracuseStep 86798573 = 32549465) B32549465
theorem B6423623 : Blo 1758080 6423623 := bstep (se 1 (by rfl) ⟨4817717, by rfl⟩ : syracuseStep 6423623 = 9635435) B9635435
theorem B57865715 : Blo 1758080 57865715 := bstep (se 1 (by rfl) ⟨43399286, by rfl⟩ : syracuseStep 57865715 = 86798573) B86798573
theorem B38577143 : Blo 1758080 38577143 := bstep (se 1 (by rfl) ⟨28932857, by rfl⟩ : syracuseStep 38577143 = 57865715) B57865715
theorem B4282415 : Blo 1758080 4282415 := bstep (se 1 (by rfl) ⟨3211811, by rfl⟩ : syracuseStep 4282415 = 6423623) B6423623
theorem B25718095 : Blo 1758080 25718095 := bstep (se 1 (by rfl) ⟨19288571, by rfl⟩ : syracuseStep 25718095 = 38577143) B38577143
theorem B2854943 : Blo 1758080 2854943 := bstep (se 1 (by rfl) ⟨2141207, by rfl⟩ : syracuseStep 2854943 = 4282415) B4282415
theorem B1903295 : Blo 1758080 1903295 := bstep (se 1 (by rfl) ⟨1427471, by rfl⟩ : syracuseStep 1903295 = 2854943) B2854943
theorem B34290793 : Blo 1758080 34290793 := bstep (se 2 (by rfl) ⟨12859047, by rfl⟩ : syracuseStep 34290793 = 25718095) B25718095
theorem B45721057 : Blo 1758080 45721057 := bstep (se 2 (by rfl) ⟨17145396, by rfl⟩ : syracuseStep 45721057 = 34290793) B34290793
theorem B5075453 : Blo 1758080 5075453 := bstep (se 3 (by rfl) ⟨951647, by rfl⟩ : syracuseStep 5075453 = 1903295) B1903295
theorem B3383635 : Blo 1758080 3383635 := bstep (se 1 (by rfl) ⟨2537726, by rfl⟩ : syracuseStep 3383635 = 5075453) B5075453
theorem B60961409 : Blo 1758080 60961409 := bstep (se 2 (by rfl) ⟨22860528, by rfl⟩ : syracuseStep 60961409 = 45721057) B45721057
theorem B40640939 : Blo 1758080 40640939 := bstep (se 1 (by rfl) ⟨30480704, by rfl⟩ : syracuseStep 40640939 = 60961409) B60961409
theorem B4511513 : Blo 1758080 4511513 := bstep (se 2 (by rfl) ⟨1691817, by rfl⟩ : syracuseStep 4511513 = 3383635) B3383635
theorem B3007675 : Blo 1758080 3007675 := bstep (se 1 (by rfl) ⟨2255756, by rfl⟩ : syracuseStep 3007675 = 4511513) B4511513
theorem B27093959 : Blo 1758080 27093959 := bstep (se 1 (by rfl) ⟨20320469, by rfl⟩ : syracuseStep 27093959 = 40640939) B40640939
theorem B4010233 : Blo 1758080 4010233 := bstep (se 2 (by rfl) ⟨1503837, by rfl⟩ : syracuseStep 4010233 = 3007675) B3007675
theorem B18062639 : Blo 1758080 18062639 := bstep (se 1 (by rfl) ⟨13546979, by rfl⟩ : syracuseStep 18062639 = 27093959) B27093959
theorem B5346977 : Blo 1758080 5346977 := bstep (se 2 (by rfl) ⟨2005116, by rfl⟩ : syracuseStep 5346977 = 4010233) B4010233
theorem B12041759 : Blo 1758080 12041759 := bstep (se 1 (by rfl) ⟨9031319, by rfl⟩ : syracuseStep 12041759 = 18062639) B18062639
theorem B14258605 : Blo 1758080 14258605 := bstep (se 3 (by rfl) ⟨2673488, by rfl⟩ : syracuseStep 14258605 = 5346977) B5346977
theorem B8027839 : Blo 1758080 8027839 := bstep (se 1 (by rfl) ⟨6020879, by rfl⟩ : syracuseStep 8027839 = 12041759) B12041759
theorem B42815141 : Blo 1758080 42815141 := bstep (se 4 (by rfl) ⟨4013919, by rfl⟩ : syracuseStep 42815141 = 8027839) B8027839
theorem B19011473 : Blo 1758080 19011473 := bstep (se 2 (by rfl) ⟨7129302, by rfl⟩ : syracuseStep 19011473 = 14258605) B14258605
theorem B12674315 : Blo 1758080 12674315 := bstep (se 1 (by rfl) ⟨9505736, by rfl⟩ : syracuseStep 12674315 = 19011473) B19011473
theorem B28543427 : Blo 1758080 28543427 := bstep (se 1 (by rfl) ⟨21407570, by rfl⟩ : syracuseStep 28543427 = 42815141) B42815141
theorem B8449543 : Blo 1758080 8449543 := bstep (se 1 (by rfl) ⟨6337157, by rfl⟩ : syracuseStep 8449543 = 12674315) B12674315
theorem B19028951 : Blo 1758080 19028951 := bstep (se 1 (by rfl) ⟨14271713, by rfl⟩ : syracuseStep 19028951 = 28543427) B28543427
theorem B11266057 : Blo 1758080 11266057 := bstep (se 2 (by rfl) ⟨4224771, by rfl⟩ : syracuseStep 11266057 = 8449543) B8449543
theorem B12685967 : Blo 1758080 12685967 := bstep (se 1 (by rfl) ⟨9514475, by rfl⟩ : syracuseStep 12685967 = 19028951) B19028951
theorem B8457311 : Blo 1758080 8457311 := bstep (se 1 (by rfl) ⟨6342983, by rfl⟩ : syracuseStep 8457311 = 12685967) B12685967
theorem B15021409 : Blo 1758080 15021409 := bstep (se 2 (by rfl) ⟨5633028, by rfl⟩ : syracuseStep 15021409 = 11266057) B11266057
theorem B5638207 : Blo 1758080 5638207 := bstep (se 1 (by rfl) ⟨4228655, by rfl⟩ : syracuseStep 5638207 = 8457311) B8457311
theorem B20028545 : Blo 1758080 20028545 := bstep (se 2 (by rfl) ⟨7510704, by rfl⟩ : syracuseStep 20028545 = 15021409) B15021409
theorem B7517609 : Blo 1758080 7517609 := bstep (se 2 (by rfl) ⟨2819103, by rfl⟩ : syracuseStep 7517609 = 5638207) B5638207
theorem B13352363 : Blo 1758080 13352363 := bstep (se 1 (by rfl) ⟨10014272, by rfl⟩ : syracuseStep 13352363 = 20028545) B20028545
theorem B8901575 : Blo 1758080 8901575 := bstep (se 1 (by rfl) ⟨6676181, by rfl⟩ : syracuseStep 8901575 = 13352363) B13352363
theorem B5011739 : Blo 1758080 5011739 := bstep (se 1 (by rfl) ⟨3758804, by rfl⟩ : syracuseStep 5011739 = 7517609) B7517609
theorem B5934383 : Blo 1758080 5934383 := bstep (se 1 (by rfl) ⟨4450787, by rfl⟩ : syracuseStep 5934383 = 8901575) B8901575
theorem B3341159 : Blo 1758080 3341159 := bstep (se 1 (by rfl) ⟨2505869, by rfl⟩ : syracuseStep 3341159 = 5011739) B5011739
theorem B2227439 : Blo 1758080 2227439 := bstep (se 1 (by rfl) ⟨1670579, by rfl⟩ : syracuseStep 2227439 = 3341159) B3341159
theorem B3956255 : Blo 1758080 3956255 := bstep (se 1 (by rfl) ⟨2967191, by rfl⟩ : syracuseStep 3956255 = 5934383) B5934383
theorem B5939837 : Blo 1758080 5939837 := bstep (se 3 (by rfl) ⟨1113719, by rfl⟩ : syracuseStep 5939837 = 2227439) B2227439
theorem B2637503 : Blo 1758080 2637503 := bstep (se 1 (by rfl) ⟨1978127, by rfl⟩ : syracuseStep 2637503 = 3956255) B3956255
theorem B3959891 : Blo 1758080 3959891 := bstep (se 1 (by rfl) ⟨2969918, by rfl⟩ : syracuseStep 3959891 = 5939837) B5939837
theorem B1758335 : Blo 1758080 1758335 := bstep (se 1 (by rfl) ⟨1318751, by rfl⟩ : syracuseStep 1758335 = 2637503) B2637503
theorem B2639927 : Blo 1758080 2639927 := bstep (se 1 (by rfl) ⟨1979945, by rfl⟩ : syracuseStep 2639927 = 3959891) B3959891
theorem B1759951 : Blo 1758080 1759951 := bstep (se 1 (by rfl) ⟨1319963, by rfl⟩ : syracuseStep 1759951 = 2639927) B2639927

theorem C0 (j : ℕ) (h1 : 439520 ≤ j) (h2 : j ≤ 440019) : Blo 1758080 (4 * j + 3) := by
  interval_cases j
  · exact B1758083
  · exact B1758087
  · exact B1758091
  · exact B1758095
  · exact B1758099
  · exact B1758103
  · exact B1758107
  · exact B1758111
  · exact B1758115
  · exact B1758119
  · exact B1758123
  · exact B1758127
  · exact B1758131
  · exact B1758135
  · exact B1758139
  · exact B1758143
  · exact B1758147
  · exact B1758151
  · exact B1758155
  · exact B1758159
  · exact B1758163
  · exact B1758167
  · exact B1758171
  · exact B1758175
  · exact B1758179
  · exact B1758183
  · exact B1758187
  · exact B1758191
  · exact B1758195
  · exact B1758199
  · exact B1758203
  · exact B1758207
  · exact B1758211
  · exact B1758215
  · exact B1758219
  · exact B1758223
  · exact B1758227
  · exact B1758231
  · exact B1758235
  · exact B1758239
  · exact B1758243
  · exact B1758247
  · exact B1758251
  · exact B1758255
  · exact B1758259
  · exact B1758263
  · exact B1758267
  · exact B1758271
  · exact B1758275
  · exact B1758279
  · exact B1758283
  · exact B1758287
  · exact B1758291
  · exact B1758295
  · exact B1758299
  · exact B1758303
  · exact B1758307
  · exact B1758311
  · exact B1758315
  · exact B1758319
  · exact B1758323
  · exact B1758327
  · exact B1758331
  · exact B1758335
  · exact B1758339
  · exact B1758343
  · exact B1758347
  · exact B1758351
  · exact B1758355
  · exact B1758359
  · exact B1758363
  · exact B1758367
  · exact B1758371
  · exact B1758375
  · exact B1758379
  · exact B1758383
  · exact B1758387
  · exact B1758391
  · exact B1758395
  · exact B1758399
  · exact B1758403
  · exact B1758407
  · exact B1758411
  · exact B1758415
  · exact B1758419
  · exact B1758423
  · exact B1758427
  · exact B1758431
  · exact B1758435
  · exact B1758439
  · exact B1758443
  · exact B1758447
  · exact B1758451
  · exact B1758455
  · exact B1758459
  · exact B1758463
  · exact B1758467
  · exact B1758471
  · exact B1758475
  · exact B1758479
  · exact B1758483
  · exact B1758487
  · exact B1758491
  · exact B1758495
  · exact B1758499
  · exact B1758503
  · exact B1758507
  · exact B1758511
  · exact B1758515
  · exact B1758519
  · exact B1758523
  · exact B1758527
  · exact B1758531
  · exact B1758535
  · exact B1758539
  · exact B1758543
  · exact B1758547
  · exact B1758551
  · exact B1758555
  · exact B1758559
  · exact B1758563
  · exact B1758567
  · exact B1758571
  · exact B1758575
  · exact B1758579
  · exact B1758583
  · exact B1758587
  · exact B1758591
  · exact B1758595
  · exact B1758599
  · exact B1758603
  · exact B1758607
  · exact B1758611
  · exact B1758615
  · exact B1758619
  · exact B1758623
  · exact B1758627
  · exact B1758631
  · exact B1758635
  · exact B1758639
  · exact B1758643
  · exact B1758647
  · exact B1758651
  · exact B1758655
  · exact B1758659
  · exact B1758663
  · exact B1758667
  · exact B1758671
  · exact B1758675
  · exact B1758679
  · exact B1758683
  · exact B1758687
  · exact B1758691
  · exact B1758695
  · exact B1758699
  · exact B1758703
  · exact B1758707
  · exact B1758711
  · exact B1758715
  · exact B1758719
  · exact B1758723
  · exact B1758727
  · exact B1758731
  · exact B1758735
  · exact B1758739
  · exact B1758743
  · exact B1758747
  · exact B1758751
  · exact B1758755
  · exact B1758759
  · exact B1758763
  · exact B1758767
  · exact B1758771
  · exact B1758775
  · exact B1758779
  · exact B1758783
  · exact B1758787
  · exact B1758791
  · exact B1758795
  · exact B1758799
  · exact B1758803
  · exact B1758807
  · exact B1758811
  · exact B1758815
  · exact B1758819
  · exact B1758823
  · exact B1758827
  · exact B1758831
  · exact B1758835
  · exact B1758839
  · exact B1758843
  · exact B1758847
  · exact B1758851
  · exact B1758855
  · exact B1758859
  · exact B1758863
  · exact B1758867
  · exact B1758871
  · exact B1758875
  · exact B1758879
  · exact B1758883
  · exact B1758887
  · exact B1758891
  · exact B1758895
  · exact B1758899
  · exact B1758903
  · exact B1758907
  · exact B1758911
  · exact B1758915
  · exact B1758919
  · exact B1758923
  · exact B1758927
  · exact B1758931
  · exact B1758935
  · exact B1758939
  · exact B1758943
  · exact B1758947
  · exact B1758951
  · exact B1758955
  · exact B1758959
  · exact B1758963
  · exact B1758967
  · exact B1758971
  · exact B1758975
  · exact B1758979
  · exact B1758983
  · exact B1758987
  · exact B1758991
  · exact B1758995
  · exact B1758999
  · exact B1759003
  · exact B1759007
  · exact B1759011
  · exact B1759015
  · exact B1759019
  · exact B1759023
  · exact B1759027
  · exact B1759031
  · exact B1759035
  · exact B1759039
  · exact B1759043
  · exact B1759047
  · exact B1759051
  · exact B1759055
  · exact B1759059
  · exact B1759063
  · exact B1759067
  · exact B1759071
  · exact B1759075
  · exact B1759079
  · exact B1759083
  · exact B1759087
  · exact B1759091
  · exact B1759095
  · exact B1759099
  · exact B1759103
  · exact B1759107
  · exact B1759111
  · exact B1759115
  · exact B1759119
  · exact B1759123
  · exact B1759127
  · exact B1759131
  · exact B1759135
  · exact B1759139
  · exact B1759143
  · exact B1759147
  · exact B1759151
  · exact B1759155
  · exact B1759159
  · exact B1759163
  · exact B1759167
  · exact B1759171
  · exact B1759175
  · exact B1759179
  · exact B1759183
  · exact B1759187
  · exact B1759191
  · exact B1759195
  · exact B1759199
  · exact B1759203
  · exact B1759207
  · exact B1759211
  · exact B1759215
  · exact B1759219
  · exact B1759223
  · exact B1759227
  · exact B1759231
  · exact B1759235
  · exact B1759239
  · exact B1759243
  · exact B1759247
  · exact B1759251
  · exact B1759255
  · exact B1759259
  · exact B1759263
  · exact B1759267
  · exact B1759271
  · exact B1759275
  · exact B1759279
  · exact B1759283
  · exact B1759287
  · exact B1759291
  · exact B1759295
  · exact B1759299
  · exact B1759303
  · exact B1759307
  · exact B1759311
  · exact B1759315
  · exact B1759319
  · exact B1759323
  · exact B1759327
  · exact B1759331
  · exact B1759335
  · exact B1759339
  · exact B1759343
  · exact B1759347
  · exact B1759351
  · exact B1759355
  · exact B1759359
  · exact B1759363
  · exact B1759367
  · exact B1759371
  · exact B1759375
  · exact B1759379
  · exact B1759383
  · exact B1759387
  · exact B1759391
  · exact B1759395
  · exact B1759399
  · exact B1759403
  · exact B1759407
  · exact B1759411
  · exact B1759415
  · exact B1759419
  · exact B1759423
  · exact B1759427
  · exact B1759431
  · exact B1759435
  · exact B1759439
  · exact B1759443
  · exact B1759447
  · exact B1759451
  · exact B1759455
  · exact B1759459
  · exact B1759463
  · exact B1759467
  · exact B1759471
  · exact B1759475
  · exact B1759479
  · exact B1759483
  · exact B1759487
  · exact B1759491
  · exact B1759495
  · exact B1759499
  · exact B1759503
  · exact B1759507
  · exact B1759511
  · exact B1759515
  · exact B1759519
  · exact B1759523
  · exact B1759527
  · exact B1759531
  · exact B1759535
  · exact B1759539
  · exact B1759543
  · exact B1759547
  · exact B1759551
  · exact B1759555
  · exact B1759559
  · exact B1759563
  · exact B1759567
  · exact B1759571
  · exact B1759575
  · exact B1759579
  · exact B1759583
  · exact B1759587
  · exact B1759591
  · exact B1759595
  · exact B1759599
  · exact B1759603
  · exact B1759607
  · exact B1759611
  · exact B1759615
  · exact B1759619
  · exact B1759623
  · exact B1759627
  · exact B1759631
  · exact B1759635
  · exact B1759639
  · exact B1759643
  · exact B1759647
  · exact B1759651
  · exact B1759655
  · exact B1759659
  · exact B1759663
  · exact B1759667
  · exact B1759671
  · exact B1759675
  · exact B1759679
  · exact B1759683
  · exact B1759687
  · exact B1759691
  · exact B1759695
  · exact B1759699
  · exact B1759703
  · exact B1759707
  · exact B1759711
  · exact B1759715
  · exact B1759719
  · exact B1759723
  · exact B1759727
  · exact B1759731
  · exact B1759735
  · exact B1759739
  · exact B1759743
  · exact B1759747
  · exact B1759751
  · exact B1759755
  · exact B1759759
  · exact B1759763
  · exact B1759767
  · exact B1759771
  · exact B1759775
  · exact B1759779
  · exact B1759783
  · exact B1759787
  · exact B1759791
  · exact B1759795
  · exact B1759799
  · exact B1759803
  · exact B1759807
  · exact B1759811
  · exact B1759815
  · exact B1759819
  · exact B1759823
  · exact B1759827
  · exact B1759831
  · exact B1759835
  · exact B1759839
  · exact B1759843
  · exact B1759847
  · exact B1759851
  · exact B1759855
  · exact B1759859
  · exact B1759863
  · exact B1759867
  · exact B1759871
  · exact B1759875
  · exact B1759879
  · exact B1759883
  · exact B1759887
  · exact B1759891
  · exact B1759895
  · exact B1759899
  · exact B1759903
  · exact B1759907
  · exact B1759911
  · exact B1759915
  · exact B1759919
  · exact B1759923
  · exact B1759927
  · exact B1759931
  · exact B1759935
  · exact B1759939
  · exact B1759943
  · exact B1759947
  · exact B1759951
  · exact B1759955
  · exact B1759959
  · exact B1759963
  · exact B1759967
  · exact B1759971
  · exact B1759975
  · exact B1759979
  · exact B1759983
  · exact B1759987
  · exact B1759991
  · exact B1759995
  · exact B1759999
  · exact B1760003
  · exact B1760007
  · exact B1760011
  · exact B1760015
  · exact B1760019
  · exact B1760023
  · exact B1760027
  · exact B1760031
  · exact B1760035
  · exact B1760039
  · exact B1760043
  · exact B1760047
  · exact B1760051
  · exact B1760055
  · exact B1760059
  · exact B1760063
  · exact B1760067
  · exact B1760071
  · exact B1760075
  · exact B1760079

theorem solution (m : ℕ) (hlo : 1758080 ≤ m) (hhi : m ≤ 1760080) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 439520 ≤ j := by omega
    have hj2 : j ≤ 440019 := by omega
    have hb : Blo 1758080 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
