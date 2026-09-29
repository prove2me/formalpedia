-- Prove2me | solution 1 for syracuse_descends_range_195805_199805
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:51.461502+00:00
-- url     : https://prove2.me/submissions/20eb7887-e14c-4262-9f6a-4c2e93615305

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


theorem B294917 : Blo 195805 294917 := bbase (se 4 (by rfl) ⟨27648, by rfl⟩ : syracuseStep 294917 = 55297) (by norm_num)
theorem B294941 : Blo 195805 294941 := bbase (se 3 (by rfl) ⟨55301, by rfl⟩ : syracuseStep 294941 = 110603) (by norm_num)
theorem B294965 : Blo 195805 294965 := bbase (se 5 (by rfl) ⟨13826, by rfl⟩ : syracuseStep 294965 = 27653) (by norm_num)
theorem B294989 : Blo 195805 294989 := bbase (se 3 (by rfl) ⟨55310, by rfl⟩ : syracuseStep 294989 = 110621) (by norm_num)
theorem B295013 : Blo 195805 295013 := bbase (se 4 (by rfl) ⟨27657, by rfl⟩ : syracuseStep 295013 = 55315) (by norm_num)
theorem B295037 : Blo 195805 295037 := bbase (se 3 (by rfl) ⟨55319, by rfl⟩ : syracuseStep 295037 = 110639) (by norm_num)
theorem B295061 : Blo 195805 295061 := bbase (se 6 (by rfl) ⟨6915, by rfl⟩ : syracuseStep 295061 = 13831) (by norm_num)
theorem B295085 : Blo 195805 295085 := bbase (se 3 (by rfl) ⟨55328, by rfl⟩ : syracuseStep 295085 = 110657) (by norm_num)
theorem B295109 : Blo 195805 295109 := bbase (se 4 (by rfl) ⟨27666, by rfl⟩ : syracuseStep 295109 = 55333) (by norm_num)
theorem B295133 : Blo 195805 295133 := bbase (se 3 (by rfl) ⟨55337, by rfl⟩ : syracuseStep 295133 = 110675) (by norm_num)
theorem B753893 : Blo 195805 753893 := bbase (se 4 (by rfl) ⟨70677, by rfl⟩ : syracuseStep 753893 = 141355) (by norm_num)
theorem B295157 : Blo 195805 295157 := bbase (se 5 (by rfl) ⟨13835, by rfl⟩ : syracuseStep 295157 = 27671) (by norm_num)
theorem B295181 : Blo 195805 295181 := bbase (se 3 (by rfl) ⟨55346, by rfl⟩ : syracuseStep 295181 = 110693) (by norm_num)
theorem B295205 : Blo 195805 295205 := bbase (se 4 (by rfl) ⟨27675, by rfl⟩ : syracuseStep 295205 = 55351) (by norm_num)
theorem B295229 : Blo 195805 295229 := bbase (se 3 (by rfl) ⟨55355, by rfl⟩ : syracuseStep 295229 = 110711) (by norm_num)
theorem B295253 : Blo 195805 295253 := bbase (se 10 (by rfl) ⟨432, by rfl⟩ : syracuseStep 295253 = 865) (by norm_num)
theorem B295277 : Blo 195805 295277 := bbase (se 3 (by rfl) ⟨55364, by rfl⟩ : syracuseStep 295277 = 110729) (by norm_num)
theorem B295301 : Blo 195805 295301 := bbase (se 4 (by rfl) ⟨27684, by rfl⟩ : syracuseStep 295301 = 55369) (by norm_num)
theorem B295325 : Blo 195805 295325 := bbase (se 3 (by rfl) ⟨55373, by rfl⟩ : syracuseStep 295325 = 110747) (by norm_num)
theorem B426397 : Blo 195805 426397 := bbase (se 3 (by rfl) ⟨79949, by rfl⟩ : syracuseStep 426397 = 159899) (by norm_num)
theorem B295349 : Blo 195805 295349 := bbase (se 5 (by rfl) ⟨13844, by rfl⟩ : syracuseStep 295349 = 27689) (by norm_num)
theorem B295373 : Blo 195805 295373 := bbase (se 3 (by rfl) ⟨55382, by rfl⟩ : syracuseStep 295373 = 110765) (by norm_num)
theorem B295397 : Blo 195805 295397 := bbase (se 4 (by rfl) ⟨27693, by rfl⟩ : syracuseStep 295397 = 55387) (by norm_num)
theorem B295421 : Blo 195805 295421 := bbase (se 3 (by rfl) ⟨55391, by rfl⟩ : syracuseStep 295421 = 110783) (by norm_num)
theorem B754181 : Blo 195805 754181 := bbase (se 4 (by rfl) ⟨70704, by rfl⟩ : syracuseStep 754181 = 141409) (by norm_num)
theorem B295445 : Blo 195805 295445 := bbase (se 6 (by rfl) ⟨6924, by rfl⟩ : syracuseStep 295445 = 13849) (by norm_num)
theorem B295469 : Blo 195805 295469 := bbase (se 3 (by rfl) ⟨55400, by rfl⟩ : syracuseStep 295469 = 110801) (by norm_num)
theorem B295493 : Blo 195805 295493 := bbase (se 4 (by rfl) ⟨27702, by rfl⟩ : syracuseStep 295493 = 55405) (by norm_num)
theorem B295517 : Blo 195805 295517 := bbase (se 3 (by rfl) ⟨55409, by rfl⟩ : syracuseStep 295517 = 110819) (by norm_num)
theorem B295541 : Blo 195805 295541 := bbase (se 5 (by rfl) ⟨13853, by rfl⟩ : syracuseStep 295541 = 27707) (by norm_num)
theorem B295565 : Blo 195805 295565 := bbase (se 3 (by rfl) ⟨55418, by rfl⟩ : syracuseStep 295565 = 110837) (by norm_num)
theorem B295589 : Blo 195805 295589 := bbase (se 4 (by rfl) ⟨27711, by rfl⟩ : syracuseStep 295589 = 55423) (by norm_num)
theorem B295613 : Blo 195805 295613 := bbase (se 3 (by rfl) ⟨55427, by rfl⟩ : syracuseStep 295613 = 110855) (by norm_num)
theorem B295637 : Blo 195805 295637 := bbase (se 7 (by rfl) ⟨3464, by rfl⟩ : syracuseStep 295637 = 6929) (by norm_num)
theorem B295661 : Blo 195805 295661 := bbase (se 3 (by rfl) ⟨55436, by rfl⟩ : syracuseStep 295661 = 110873) (by norm_num)
theorem B295685 : Blo 195805 295685 := bbase (se 4 (by rfl) ⟨27720, by rfl⟩ : syracuseStep 295685 = 55441) (by norm_num)
theorem B295709 : Blo 195805 295709 := bbase (se 3 (by rfl) ⟨55445, by rfl⟩ : syracuseStep 295709 = 110891) (by norm_num)
theorem B295733 : Blo 195805 295733 := bbase (se 5 (by rfl) ⟨13862, by rfl⟩ : syracuseStep 295733 = 27725) (by norm_num)
theorem B295757 : Blo 195805 295757 := bbase (se 3 (by rfl) ⟨55454, by rfl⟩ : syracuseStep 295757 = 110909) (by norm_num)
theorem B295781 : Blo 195805 295781 := bbase (se 4 (by rfl) ⟨27729, by rfl⟩ : syracuseStep 295781 = 55459) (by norm_num)
theorem B295805 : Blo 195805 295805 := bbase (se 3 (by rfl) ⟨55463, by rfl⟩ : syracuseStep 295805 = 110927) (by norm_num)
theorem B295829 : Blo 195805 295829 := bbase (se 6 (by rfl) ⟨6933, by rfl⟩ : syracuseStep 295829 = 13867) (by norm_num)
theorem B295853 : Blo 195805 295853 := bbase (se 3 (by rfl) ⟨55472, by rfl⟩ : syracuseStep 295853 = 110945) (by norm_num)
theorem B295877 : Blo 195805 295877 := bbase (se 4 (by rfl) ⟨27738, by rfl⟩ : syracuseStep 295877 = 55477) (by norm_num)
theorem B295901 : Blo 195805 295901 := bbase (se 3 (by rfl) ⟨55481, by rfl⟩ : syracuseStep 295901 = 110963) (by norm_num)
theorem B295925 : Blo 195805 295925 := bbase (se 5 (by rfl) ⟨13871, by rfl⟩ : syracuseStep 295925 = 27743) (by norm_num)
theorem B295949 : Blo 195805 295949 := bbase (se 3 (by rfl) ⟨55490, by rfl⟩ : syracuseStep 295949 = 110981) (by norm_num)
theorem B295973 : Blo 195805 295973 := bbase (se 4 (by rfl) ⟨27747, by rfl⟩ : syracuseStep 295973 = 55495) (by norm_num)
theorem B295997 : Blo 195805 295997 := bbase (se 3 (by rfl) ⟨55499, by rfl⟩ : syracuseStep 295997 = 110999) (by norm_num)
theorem B296021 : Blo 195805 296021 := bbase (se 8 (by rfl) ⟨1734, by rfl⟩ : syracuseStep 296021 = 3469) (by norm_num)
theorem B296045 : Blo 195805 296045 := bbase (se 3 (by rfl) ⟨55508, by rfl⟩ : syracuseStep 296045 = 111017) (by norm_num)
theorem B296069 : Blo 195805 296069 := bbase (se 4 (by rfl) ⟨27756, by rfl⟩ : syracuseStep 296069 = 55513) (by norm_num)
theorem B296093 : Blo 195805 296093 := bbase (se 3 (by rfl) ⟨55517, by rfl⟩ : syracuseStep 296093 = 111035) (by norm_num)
theorem B296117 : Blo 195805 296117 := bbase (se 5 (by rfl) ⟨13880, by rfl⟩ : syracuseStep 296117 = 27761) (by norm_num)
theorem B722117 : Blo 195805 722117 := bbase (se 4 (by rfl) ⟨67698, by rfl⟩ : syracuseStep 722117 = 135397) (by norm_num)
theorem B296141 : Blo 195805 296141 := bbase (se 3 (by rfl) ⟨55526, by rfl⟩ : syracuseStep 296141 = 111053) (by norm_num)
theorem B296165 : Blo 195805 296165 := bbase (se 4 (by rfl) ⟨27765, by rfl⟩ : syracuseStep 296165 = 55531) (by norm_num)
theorem B296189 : Blo 195805 296189 := bbase (se 3 (by rfl) ⟨55535, by rfl⟩ : syracuseStep 296189 = 111071) (by norm_num)
theorem B296213 : Blo 195805 296213 := bbase (se 6 (by rfl) ⟨6942, by rfl⟩ : syracuseStep 296213 = 13885) (by norm_num)
theorem B296237 : Blo 195805 296237 := bbase (se 3 (by rfl) ⟨55544, by rfl⟩ : syracuseStep 296237 = 111089) (by norm_num)
theorem B296261 : Blo 195805 296261 := bbase (se 4 (by rfl) ⟨27774, by rfl⟩ : syracuseStep 296261 = 55549) (by norm_num)
theorem B296285 : Blo 195805 296285 := bbase (se 3 (by rfl) ⟨55553, by rfl⟩ : syracuseStep 296285 = 111107) (by norm_num)
theorem B296309 : Blo 195805 296309 := bbase (se 5 (by rfl) ⟨13889, by rfl⟩ : syracuseStep 296309 = 27779) (by norm_num)
theorem B296333 : Blo 195805 296333 := bbase (se 3 (by rfl) ⟨55562, by rfl⟩ : syracuseStep 296333 = 111125) (by norm_num)
theorem B296357 : Blo 195805 296357 := bbase (se 4 (by rfl) ⟨27783, by rfl⟩ : syracuseStep 296357 = 55567) (by norm_num)
theorem B296381 : Blo 195805 296381 := bbase (se 3 (by rfl) ⟨55571, by rfl⟩ : syracuseStep 296381 = 111143) (by norm_num)
theorem B296405 : Blo 195805 296405 := bbase (se 7 (by rfl) ⟨3473, by rfl⟩ : syracuseStep 296405 = 6947) (by norm_num)
theorem B296429 : Blo 195805 296429 := bbase (se 3 (by rfl) ⟨55580, by rfl⟩ : syracuseStep 296429 = 111161) (by norm_num)
theorem B296453 : Blo 195805 296453 := bbase (se 4 (by rfl) ⟨27792, by rfl⟩ : syracuseStep 296453 = 55585) (by norm_num)
theorem B296477 : Blo 195805 296477 := bbase (se 3 (by rfl) ⟨55589, by rfl⟩ : syracuseStep 296477 = 111179) (by norm_num)
theorem B296501 : Blo 195805 296501 := bbase (se 5 (by rfl) ⟨13898, by rfl⟩ : syracuseStep 296501 = 27797) (by norm_num)
theorem B296525 : Blo 195805 296525 := bbase (se 3 (by rfl) ⟨55598, by rfl⟩ : syracuseStep 296525 = 111197) (by norm_num)
theorem B558677 : Blo 195805 558677 := bbase (se 8 (by rfl) ⟨3273, by rfl⟩ : syracuseStep 558677 = 6547) (by norm_num)
theorem B296549 : Blo 195805 296549 := bbase (se 4 (by rfl) ⟨27801, by rfl⟩ : syracuseStep 296549 = 55603) (by norm_num)
theorem B296573 : Blo 195805 296573 := bbase (se 3 (by rfl) ⟨55607, by rfl⟩ : syracuseStep 296573 = 111215) (by norm_num)
theorem B296597 : Blo 195805 296597 := bbase (se 6 (by rfl) ⟨6951, by rfl⟩ : syracuseStep 296597 = 13903) (by norm_num)
theorem B755365 : Blo 195805 755365 := bbase (se 4 (by rfl) ⟨70815, by rfl⟩ : syracuseStep 755365 = 141631) (by norm_num)
theorem B296621 : Blo 195805 296621 := bbase (se 3 (by rfl) ⟨55616, by rfl⟩ : syracuseStep 296621 = 111233) (by norm_num)
theorem B296645 : Blo 195805 296645 := bbase (se 4 (by rfl) ⟨27810, by rfl⟩ : syracuseStep 296645 = 55621) (by norm_num)
theorem B296669 : Blo 195805 296669 := bbase (se 3 (by rfl) ⟨55625, by rfl⟩ : syracuseStep 296669 = 111251) (by norm_num)
theorem B296693 : Blo 195805 296693 := bbase (se 5 (by rfl) ⟨13907, by rfl⟩ : syracuseStep 296693 = 27815) (by norm_num)
theorem B296717 : Blo 195805 296717 := bbase (se 3 (by rfl) ⟨55634, by rfl⟩ : syracuseStep 296717 = 111269) (by norm_num)
theorem B296741 : Blo 195805 296741 := bbase (se 4 (by rfl) ⟨27819, by rfl⟩ : syracuseStep 296741 = 55639) (by norm_num)
theorem B296765 : Blo 195805 296765 := bbase (se 3 (by rfl) ⟨55643, by rfl⟩ : syracuseStep 296765 = 111287) (by norm_num)
theorem B296789 : Blo 195805 296789 := bbase (se 9 (by rfl) ⟨869, by rfl⟩ : syracuseStep 296789 = 1739) (by norm_num)
theorem B952165 : Blo 195805 952165 := bbase (se 4 (by rfl) ⟨89265, by rfl⟩ : syracuseStep 952165 = 178531) (by norm_num)
theorem B198509 : Blo 195805 198509 := bbase (se 3 (by rfl) ⟨37220, by rfl⟩ : syracuseStep 198509 = 74441) (by norm_num)
theorem B296813 : Blo 195805 296813 := bbase (se 3 (by rfl) ⟨55652, by rfl⟩ : syracuseStep 296813 = 111305) (by norm_num)
theorem B296837 : Blo 195805 296837 := bbase (se 4 (by rfl) ⟨27828, by rfl⟩ : syracuseStep 296837 = 55657) (by norm_num)
theorem B198541 : Blo 195805 198541 := bbase (se 3 (by rfl) ⟨37226, by rfl⟩ : syracuseStep 198541 = 74453) (by norm_num)
theorem B296861 : Blo 195805 296861 := bbase (se 3 (by rfl) ⟨55661, by rfl⟩ : syracuseStep 296861 = 111323) (by norm_num)
theorem B296885 : Blo 195805 296885 := bbase (se 5 (by rfl) ⟨13916, by rfl⟩ : syracuseStep 296885 = 27833) (by norm_num)
theorem B296909 : Blo 195805 296909 := bbase (se 3 (by rfl) ⟨55670, by rfl⟩ : syracuseStep 296909 = 111341) (by norm_num)
theorem B755669 : Blo 195805 755669 := bbase (se 7 (by rfl) ⟨8855, by rfl⟩ : syracuseStep 755669 = 17711) (by norm_num)
theorem B296933 : Blo 195805 296933 := bbase (se 4 (by rfl) ⟨27837, by rfl⟩ : syracuseStep 296933 = 55675) (by norm_num)
theorem B296957 : Blo 195805 296957 := bbase (se 3 (by rfl) ⟨55679, by rfl⟩ : syracuseStep 296957 = 111359) (by norm_num)
theorem B296981 : Blo 195805 296981 := bbase (se 6 (by rfl) ⟨6960, by rfl⟩ : syracuseStep 296981 = 13921) (by norm_num)
theorem B297005 : Blo 195805 297005 := bbase (se 3 (by rfl) ⟨55688, by rfl⟩ : syracuseStep 297005 = 111377) (by norm_num)
theorem B297029 : Blo 195805 297029 := bbase (se 4 (by rfl) ⟨27846, by rfl⟩ : syracuseStep 297029 = 55693) (by norm_num)
theorem B297053 : Blo 195805 297053 := bbase (se 3 (by rfl) ⟨55697, by rfl⟩ : syracuseStep 297053 = 111395) (by norm_num)
theorem B297077 : Blo 195805 297077 := bbase (se 5 (by rfl) ⟨13925, by rfl⟩ : syracuseStep 297077 = 27851) (by norm_num)
theorem B297101 : Blo 195805 297101 := bbase (se 3 (by rfl) ⟨55706, by rfl⟩ : syracuseStep 297101 = 111413) (by norm_num)
theorem B198821 : Blo 195805 198821 := bbase (se 4 (by rfl) ⟨18639, by rfl⟩ : syracuseStep 198821 = 37279) (by norm_num)
theorem B297125 : Blo 195805 297125 := bbase (se 4 (by rfl) ⟨27855, by rfl⟩ : syracuseStep 297125 = 55711) (by norm_num)
theorem B297149 : Blo 195805 297149 := bbase (se 3 (by rfl) ⟨55715, by rfl⟩ : syracuseStep 297149 = 111431) (by norm_num)
theorem B297173 : Blo 195805 297173 := bbase (se 7 (by rfl) ⟨3482, by rfl⟩ : syracuseStep 297173 = 6965) (by norm_num)
theorem B297197 : Blo 195805 297197 := bbase (se 3 (by rfl) ⟨55724, by rfl⟩ : syracuseStep 297197 = 111449) (by norm_num)
theorem B559349 : Blo 195805 559349 := bbase (se 5 (by rfl) ⟨26219, by rfl⟩ : syracuseStep 559349 = 52439) (by norm_num)
theorem B297221 : Blo 195805 297221 := bbase (se 4 (by rfl) ⟨27864, by rfl⟩ : syracuseStep 297221 = 55729) (by norm_num)
theorem B297245 : Blo 195805 297245 := bbase (se 3 (by rfl) ⟨55733, by rfl⟩ : syracuseStep 297245 = 111467) (by norm_num)
theorem B297269 : Blo 195805 297269 := bbase (se 5 (by rfl) ⟨13934, by rfl⟩ : syracuseStep 297269 = 27869) (by norm_num)
theorem B297293 : Blo 195805 297293 := bbase (se 3 (by rfl) ⟨55742, by rfl⟩ : syracuseStep 297293 = 111485) (by norm_num)
theorem B297317 : Blo 195805 297317 := bbase (se 4 (by rfl) ⟨27873, by rfl⟩ : syracuseStep 297317 = 55747) (by norm_num)
theorem B297341 : Blo 195805 297341 := bbase (se 3 (by rfl) ⟨55751, by rfl⟩ : syracuseStep 297341 = 111503) (by norm_num)
theorem B297365 : Blo 195805 297365 := bbase (se 6 (by rfl) ⟨6969, by rfl⟩ : syracuseStep 297365 = 13939) (by norm_num)
theorem B297389 : Blo 195805 297389 := bbase (se 3 (by rfl) ⟨55760, by rfl⟩ : syracuseStep 297389 = 111521) (by norm_num)
theorem B297413 : Blo 195805 297413 := bbase (se 4 (by rfl) ⟨27882, by rfl⟩ : syracuseStep 297413 = 55765) (by norm_num)
theorem B297437 : Blo 195805 297437 := bbase (se 3 (by rfl) ⟨55769, by rfl⟩ : syracuseStep 297437 = 111539) (by norm_num)
theorem B297461 : Blo 195805 297461 := bbase (se 5 (by rfl) ⟨13943, by rfl⟩ : syracuseStep 297461 = 27887) (by norm_num)
theorem B297485 : Blo 195805 297485 := bbase (se 3 (by rfl) ⟨55778, by rfl⟩ : syracuseStep 297485 = 111557) (by norm_num)
theorem B297509 : Blo 195805 297509 := bbase (se 4 (by rfl) ⟨27891, by rfl⟩ : syracuseStep 297509 = 55783) (by norm_num)
theorem B297533 : Blo 195805 297533 := bbase (se 3 (by rfl) ⟨55787, by rfl⟩ : syracuseStep 297533 = 111575) (by norm_num)
theorem B297557 : Blo 195805 297557 := bbase (se 8 (by rfl) ⟨1743, by rfl⟩ : syracuseStep 297557 = 3487) (by norm_num)
theorem B297581 : Blo 195805 297581 := bbase (se 3 (by rfl) ⟨55796, by rfl⟩ : syracuseStep 297581 = 111593) (by norm_num)
theorem B297605 : Blo 195805 297605 := bbase (se 4 (by rfl) ⟨27900, by rfl⟩ : syracuseStep 297605 = 55801) (by norm_num)
theorem B297629 : Blo 195805 297629 := bbase (se 3 (by rfl) ⟨55805, by rfl⟩ : syracuseStep 297629 = 111611) (by norm_num)
theorem B559781 : Blo 195805 559781 := bbase (se 4 (by rfl) ⟨52479, by rfl⟩ : syracuseStep 559781 = 104959) (by norm_num)
theorem B297653 : Blo 195805 297653 := bbase (se 5 (by rfl) ⟨13952, by rfl⟩ : syracuseStep 297653 = 27905) (by norm_num)
theorem B297677 : Blo 195805 297677 := bbase (se 3 (by rfl) ⟨55814, by rfl⟩ : syracuseStep 297677 = 111629) (by norm_num)
theorem B297701 : Blo 195805 297701 := bbase (se 4 (by rfl) ⟨27909, by rfl⟩ : syracuseStep 297701 = 55819) (by norm_num)
theorem B330493 : Blo 195805 330493 := bbase (se 3 (by rfl) ⟨61967, by rfl⟩ : syracuseStep 330493 = 123935) (by norm_num)
theorem B297725 : Blo 195805 297725 := bbase (se 3 (by rfl) ⟨55823, by rfl⟩ : syracuseStep 297725 = 111647) (by norm_num)
theorem B297749 : Blo 195805 297749 := bbase (se 6 (by rfl) ⟨6978, by rfl⟩ : syracuseStep 297749 = 13957) (by norm_num)
theorem B199453 : Blo 195805 199453 := bbase (se 3 (by rfl) ⟨37397, by rfl⟩ : syracuseStep 199453 = 74795) (by norm_num)
theorem B297773 : Blo 195805 297773 := bbase (se 3 (by rfl) ⟨55832, by rfl⟩ : syracuseStep 297773 = 111665) (by norm_num)
theorem B363317 : Blo 195805 363317 := bbase (se 5 (by rfl) ⟨17030, by rfl⟩ : syracuseStep 363317 = 34061) (by norm_num)
theorem B297797 : Blo 195805 297797 := bbase (se 4 (by rfl) ⟨27918, by rfl⟩ : syracuseStep 297797 = 55837) (by norm_num)
theorem B330581 : Blo 195805 330581 := bbase (se 9 (by rfl) ⟨968, by rfl⟩ : syracuseStep 330581 = 1937) (by norm_num)
theorem B297821 : Blo 195805 297821 := bbase (se 3 (by rfl) ⟨55841, by rfl⟩ : syracuseStep 297821 = 111683) (by norm_num)
theorem B297845 : Blo 195805 297845 := bbase (se 5 (by rfl) ⟨13961, by rfl⟩ : syracuseStep 297845 = 27923) (by norm_num)
theorem B297869 : Blo 195805 297869 := bbase (se 3 (by rfl) ⟨55850, by rfl⟩ : syracuseStep 297869 = 111701) (by norm_num)
theorem B297893 : Blo 195805 297893 := bbase (se 4 (by rfl) ⟨27927, by rfl⟩ : syracuseStep 297893 = 55855) (by norm_num)
theorem B297917 : Blo 195805 297917 := bbase (se 3 (by rfl) ⟨55859, by rfl⟩ : syracuseStep 297917 = 111719) (by norm_num)
theorem B330709 : Blo 195805 330709 := bbase (se 7 (by rfl) ⟨3875, by rfl⟩ : syracuseStep 330709 = 7751) (by norm_num)
theorem B297941 : Blo 195805 297941 := bbase (se 7 (by rfl) ⟨3491, by rfl⟩ : syracuseStep 297941 = 6983) (by norm_num)
theorem B297965 : Blo 195805 297965 := bbase (se 3 (by rfl) ⟨55868, by rfl⟩ : syracuseStep 297965 = 111737) (by norm_num)
theorem B297989 : Blo 195805 297989 := bbase (se 4 (by rfl) ⟨27936, by rfl⟩ : syracuseStep 297989 = 55873) (by norm_num)
theorem B298013 : Blo 195805 298013 := bbase (se 3 (by rfl) ⟨55877, by rfl⟩ : syracuseStep 298013 = 111755) (by norm_num)
theorem B330797 : Blo 195805 330797 := bbase (se 3 (by rfl) ⟨62024, by rfl⟩ : syracuseStep 330797 = 124049) (by norm_num)
theorem B298037 : Blo 195805 298037 := bbase (se 5 (by rfl) ⟨13970, by rfl⟩ : syracuseStep 298037 = 27941) (by norm_num)
theorem B298061 : Blo 195805 298061 := bbase (se 3 (by rfl) ⟨55886, by rfl⟩ : syracuseStep 298061 = 111773) (by norm_num)
theorem B298085 : Blo 195805 298085 := bbase (se 4 (by rfl) ⟨27945, by rfl⟩ : syracuseStep 298085 = 55891) (by norm_num)
theorem B298109 : Blo 195805 298109 := bbase (se 3 (by rfl) ⟨55895, by rfl⟩ : syracuseStep 298109 = 111791) (by norm_num)
theorem B756869 : Blo 195805 756869 := bbase (se 4 (by rfl) ⟨70956, by rfl⟩ : syracuseStep 756869 = 141913) (by norm_num)
theorem B298133 : Blo 195805 298133 := bbase (se 6 (by rfl) ⟨6987, by rfl⟩ : syracuseStep 298133 = 13975) (by norm_num)
theorem B330925 : Blo 195805 330925 := bbase (se 3 (by rfl) ⟨62048, by rfl⟩ : syracuseStep 330925 = 124097) (by norm_num)
theorem B298157 : Blo 195805 298157 := bbase (se 3 (by rfl) ⟨55904, by rfl⟩ : syracuseStep 298157 = 111809) (by norm_num)
theorem B298181 : Blo 195805 298181 := bbase (se 4 (by rfl) ⟨27954, by rfl⟩ : syracuseStep 298181 = 55909) (by norm_num)
theorem B298205 : Blo 195805 298205 := bbase (se 3 (by rfl) ⟨55913, by rfl⟩ : syracuseStep 298205 = 111827) (by norm_num)
theorem B756965 : Blo 195805 756965 := bbase (se 4 (by rfl) ⟨70965, by rfl⟩ : syracuseStep 756965 = 141931) (by norm_num)
theorem B298229 : Blo 195805 298229 := bbase (se 5 (by rfl) ⟨13979, by rfl⟩ : syracuseStep 298229 = 27959) (by norm_num)
theorem B331013 : Blo 195805 331013 := bbase (se 4 (by rfl) ⟨31032, by rfl⟩ : syracuseStep 331013 = 62065) (by norm_num)
theorem B298253 : Blo 195805 298253 := bbase (se 3 (by rfl) ⟨55922, by rfl⟩ : syracuseStep 298253 = 111845) (by norm_num)
theorem B298277 : Blo 195805 298277 := bbase (se 4 (by rfl) ⟨27963, by rfl⟩ : syracuseStep 298277 = 55927) (by norm_num)
theorem B298301 : Blo 195805 298301 := bbase (se 3 (by rfl) ⟨55931, by rfl⟩ : syracuseStep 298301 = 111863) (by norm_num)
theorem B298325 : Blo 195805 298325 := bbase (se 11 (by rfl) ⟨218, by rfl⟩ : syracuseStep 298325 = 437) (by norm_num)
theorem B298349 : Blo 195805 298349 := bbase (se 3 (by rfl) ⟨55940, by rfl⟩ : syracuseStep 298349 = 111881) (by norm_num)
theorem B200053 : Blo 195805 200053 := bbase (se 5 (by rfl) ⟨9377, by rfl⟩ : syracuseStep 200053 = 18755) (by norm_num)
theorem B331141 : Blo 195805 331141 := bbase (se 4 (by rfl) ⟨31044, by rfl⟩ : syracuseStep 331141 = 62089) (by norm_num)
theorem B298373 : Blo 195805 298373 := bbase (se 4 (by rfl) ⟨27972, by rfl⟩ : syracuseStep 298373 = 55945) (by norm_num)
theorem B560533 : Blo 195805 560533 := bbase (se 6 (by rfl) ⟨13137, by rfl⟩ : syracuseStep 560533 = 26275) (by norm_num)
theorem B298397 : Blo 195805 298397 := bbase (se 3 (by rfl) ⟨55949, by rfl⟩ : syracuseStep 298397 = 111899) (by norm_num)
theorem B298421 : Blo 195805 298421 := bbase (se 5 (by rfl) ⟨13988, by rfl⟩ : syracuseStep 298421 = 27977) (by norm_num)
theorem B298445 : Blo 195805 298445 := bbase (se 3 (by rfl) ⟨55958, by rfl⟩ : syracuseStep 298445 = 111917) (by norm_num)
theorem B331229 : Blo 195805 331229 := bbase (se 3 (by rfl) ⟨62105, by rfl⟩ : syracuseStep 331229 = 124211) (by norm_num)
theorem B298469 : Blo 195805 298469 := bbase (se 4 (by rfl) ⟨27981, by rfl⟩ : syracuseStep 298469 = 55963) (by norm_num)
theorem B265717 : Blo 195805 265717 := bbase (se 5 (by rfl) ⟨12455, by rfl⟩ : syracuseStep 265717 = 24911) (by norm_num)
theorem B298493 : Blo 195805 298493 := bbase (se 3 (by rfl) ⟨55967, by rfl⟩ : syracuseStep 298493 = 111935) (by norm_num)
theorem B298517 : Blo 195805 298517 := bbase (se 6 (by rfl) ⟨6996, by rfl⟩ : syracuseStep 298517 = 13993) (by norm_num)
theorem B298541 : Blo 195805 298541 := bbase (se 3 (by rfl) ⟨55976, by rfl⟩ : syracuseStep 298541 = 111953) (by norm_num)
theorem B298565 : Blo 195805 298565 := bbase (se 4 (by rfl) ⟨27990, by rfl⟩ : syracuseStep 298565 = 55981) (by norm_num)
theorem B331357 : Blo 195805 331357 := bbase (se 3 (by rfl) ⟨62129, by rfl⟩ : syracuseStep 331357 = 124259) (by norm_num)
theorem B298589 : Blo 195805 298589 := bbase (se 3 (by rfl) ⟨55985, by rfl⟩ : syracuseStep 298589 = 111971) (by norm_num)
theorem B298613 : Blo 195805 298613 := bbase (se 5 (by rfl) ⟨13997, by rfl⟩ : syracuseStep 298613 = 27995) (by norm_num)
theorem B298637 : Blo 195805 298637 := bbase (se 3 (by rfl) ⟨55994, by rfl⟩ : syracuseStep 298637 = 111989) (by norm_num)
theorem B298661 : Blo 195805 298661 := bbase (se 4 (by rfl) ⟨27999, by rfl⟩ : syracuseStep 298661 = 55999) (by norm_num)
theorem B331445 : Blo 195805 331445 := bbase (se 5 (by rfl) ⟨15536, by rfl⟩ : syracuseStep 331445 = 31073) (by norm_num)
theorem B298685 : Blo 195805 298685 := bbase (se 3 (by rfl) ⟨56003, by rfl⟩ : syracuseStep 298685 = 112007) (by norm_num)
theorem B265933 : Blo 195805 265933 := bbase (se 3 (by rfl) ⟨49862, by rfl⟩ : syracuseStep 265933 = 99725) (by norm_num)
theorem B298709 : Blo 195805 298709 := bbase (se 7 (by rfl) ⟨3500, by rfl⟩ : syracuseStep 298709 = 7001) (by norm_num)
theorem B298733 : Blo 195805 298733 := bbase (se 3 (by rfl) ⟨56012, by rfl⟩ : syracuseStep 298733 = 112025) (by norm_num)
theorem B298757 : Blo 195805 298757 := bbase (se 4 (by rfl) ⟨28008, by rfl⟩ : syracuseStep 298757 = 56017) (by norm_num)
theorem B298781 : Blo 195805 298781 := bbase (se 3 (by rfl) ⟨56021, by rfl⟩ : syracuseStep 298781 = 112043) (by norm_num)
theorem B331573 : Blo 195805 331573 := bbase (se 5 (by rfl) ⟨15542, by rfl⟩ : syracuseStep 331573 = 31085) (by norm_num)
theorem B298805 : Blo 195805 298805 := bbase (se 5 (by rfl) ⟨14006, by rfl⟩ : syracuseStep 298805 = 28013) (by norm_num)
theorem B298829 : Blo 195805 298829 := bbase (se 3 (by rfl) ⟨56030, by rfl⟩ : syracuseStep 298829 = 112061) (by norm_num)
theorem B298853 : Blo 195805 298853 := bbase (se 4 (by rfl) ⟨28017, by rfl⟩ : syracuseStep 298853 = 56035) (by norm_num)
theorem B298877 : Blo 195805 298877 := bbase (se 3 (by rfl) ⟨56039, by rfl⟩ : syracuseStep 298877 = 112079) (by norm_num)
theorem B331661 : Blo 195805 331661 := bbase (se 3 (by rfl) ⟨62186, by rfl⟩ : syracuseStep 331661 = 124373) (by norm_num)
theorem B298901 : Blo 195805 298901 := bbase (se 6 (by rfl) ⟨7005, by rfl⟩ : syracuseStep 298901 = 14011) (by norm_num)
theorem B298925 : Blo 195805 298925 := bbase (se 3 (by rfl) ⟨56048, by rfl⟩ : syracuseStep 298925 = 112097) (by norm_num)
theorem B298949 : Blo 195805 298949 := bbase (se 4 (by rfl) ⟨28026, by rfl⟩ : syracuseStep 298949 = 56053) (by norm_num)
theorem B298973 : Blo 195805 298973 := bbase (se 3 (by rfl) ⟨56057, by rfl⟩ : syracuseStep 298973 = 112115) (by norm_num)
theorem B298997 : Blo 195805 298997 := bbase (se 5 (by rfl) ⟨14015, by rfl⟩ : syracuseStep 298997 = 28031) (by norm_num)
theorem B331789 : Blo 195805 331789 := bbase (se 3 (by rfl) ⟨62210, by rfl⟩ : syracuseStep 331789 = 124421) (by norm_num)
theorem B299021 : Blo 195805 299021 := bbase (se 3 (by rfl) ⟨56066, by rfl⟩ : syracuseStep 299021 = 112133) (by norm_num)
theorem B757781 : Blo 195805 757781 := bbase (se 6 (by rfl) ⟨17760, by rfl⟩ : syracuseStep 757781 = 35521) (by norm_num)
theorem B299045 : Blo 195805 299045 := bbase (se 4 (by rfl) ⟨28035, by rfl⟩ : syracuseStep 299045 = 56071) (by norm_num)
theorem B299069 : Blo 195805 299069 := bbase (se 3 (by rfl) ⟨56075, by rfl⟩ : syracuseStep 299069 = 112151) (by norm_num)
theorem B299093 : Blo 195805 299093 := bbase (se 8 (by rfl) ⟨1752, by rfl⟩ : syracuseStep 299093 = 3505) (by norm_num)
theorem B331877 : Blo 195805 331877 := bbase (se 4 (by rfl) ⟨31113, by rfl⟩ : syracuseStep 331877 = 62227) (by norm_num)
theorem B299117 : Blo 195805 299117 := bbase (se 3 (by rfl) ⟨56084, by rfl⟩ : syracuseStep 299117 = 112169) (by norm_num)
theorem B299141 : Blo 195805 299141 := bbase (se 4 (by rfl) ⟨28044, by rfl⟩ : syracuseStep 299141 = 56089) (by norm_num)
theorem B299165 : Blo 195805 299165 := bbase (se 3 (by rfl) ⟨56093, by rfl⟩ : syracuseStep 299165 = 112187) (by norm_num)
theorem B299189 : Blo 195805 299189 := bbase (se 5 (by rfl) ⟨14024, by rfl⟩ : syracuseStep 299189 = 28049) (by norm_num)
theorem B495821 : Blo 195805 495821 := bbase (se 3 (by rfl) ⟨92966, by rfl⟩ : syracuseStep 495821 = 185933) (by norm_num)
theorem B299213 : Blo 195805 299213 := bbase (se 3 (by rfl) ⟨56102, by rfl⟩ : syracuseStep 299213 = 112205) (by norm_num)
theorem B332005 : Blo 195805 332005 := bbase (se 4 (by rfl) ⟨31125, by rfl⟩ : syracuseStep 332005 = 62251) (by norm_num)
theorem B299237 : Blo 195805 299237 := bbase (se 4 (by rfl) ⟨28053, by rfl⟩ : syracuseStep 299237 = 56107) (by norm_num)
theorem B299261 : Blo 195805 299261 := bbase (se 3 (by rfl) ⟨56111, by rfl⟩ : syracuseStep 299261 = 112223) (by norm_num)
theorem B299285 : Blo 195805 299285 := bbase (se 6 (by rfl) ⟨7014, by rfl⟩ : syracuseStep 299285 = 14029) (by norm_num)
theorem B299309 : Blo 195805 299309 := bbase (se 3 (by rfl) ⟨56120, by rfl⟩ : syracuseStep 299309 = 112241) (by norm_num)
theorem B758069 : Blo 195805 758069 := bbase (se 5 (by rfl) ⟨35534, by rfl⟩ : syracuseStep 758069 = 71069) (by norm_num)
theorem B332093 : Blo 195805 332093 := bbase (se 3 (by rfl) ⟨62267, by rfl⟩ : syracuseStep 332093 = 124535) (by norm_num)
theorem B299333 : Blo 195805 299333 := bbase (se 4 (by rfl) ⟨28062, by rfl⟩ : syracuseStep 299333 = 56125) (by norm_num)
theorem B299357 : Blo 195805 299357 := bbase (se 3 (by rfl) ⟨56129, by rfl⟩ : syracuseStep 299357 = 112259) (by norm_num)
theorem B299381 : Blo 195805 299381 := bbase (se 5 (by rfl) ⟨14033, by rfl⟩ : syracuseStep 299381 = 28067) (by norm_num)
theorem B299405 : Blo 195805 299405 := bbase (se 3 (by rfl) ⟨56138, by rfl⟩ : syracuseStep 299405 = 112277) (by norm_num)
theorem B299429 : Blo 195805 299429 := bbase (se 4 (by rfl) ⟨28071, by rfl⟩ : syracuseStep 299429 = 56143) (by norm_num)
theorem B332221 : Blo 195805 332221 := bbase (se 3 (by rfl) ⟨62291, by rfl⟩ : syracuseStep 332221 = 124583) (by norm_num)
theorem B299453 : Blo 195805 299453 := bbase (se 3 (by rfl) ⟨56147, by rfl⟩ : syracuseStep 299453 = 112295) (by norm_num)
theorem B299477 : Blo 195805 299477 := bbase (se 7 (by rfl) ⟨3509, by rfl⟩ : syracuseStep 299477 = 7019) (by norm_num)
theorem B299501 : Blo 195805 299501 := bbase (se 3 (by rfl) ⟨56156, by rfl⟩ : syracuseStep 299501 = 112313) (by norm_num)
theorem B299525 : Blo 195805 299525 := bbase (se 4 (by rfl) ⟨28080, by rfl⟩ : syracuseStep 299525 = 56161) (by norm_num)
theorem B332309 : Blo 195805 332309 := bbase (se 6 (by rfl) ⟨7788, by rfl⟩ : syracuseStep 332309 = 15577) (by norm_num)
theorem B299549 : Blo 195805 299549 := bbase (se 3 (by rfl) ⟨56165, by rfl⟩ : syracuseStep 299549 = 112331) (by norm_num)
theorem B496165 : Blo 195805 496165 := bbase (se 4 (by rfl) ⟨46515, by rfl⟩ : syracuseStep 496165 = 93031) (by norm_num)
theorem B266797 : Blo 195805 266797 := bbase (se 3 (by rfl) ⟨50024, by rfl⟩ : syracuseStep 266797 = 100049) (by norm_num)
theorem B299573 : Blo 195805 299573 := bbase (se 5 (by rfl) ⟨14042, by rfl⟩ : syracuseStep 299573 = 28085) (by norm_num)
theorem B299597 : Blo 195805 299597 := bbase (se 3 (by rfl) ⟨56174, by rfl⟩ : syracuseStep 299597 = 112349) (by norm_num)
theorem B299621 : Blo 195805 299621 := bbase (se 4 (by rfl) ⟨28089, by rfl⟩ : syracuseStep 299621 = 56179) (by norm_num)
theorem B299645 : Blo 195805 299645 := bbase (se 3 (by rfl) ⟨56183, by rfl⟩ : syracuseStep 299645 = 112367) (by norm_num)
theorem B496277 : Blo 195805 496277 := bbase (se 6 (by rfl) ⟨11631, by rfl⟩ : syracuseStep 496277 = 23263) (by norm_num)
theorem B332437 : Blo 195805 332437 := bbase (se 6 (by rfl) ⟨7791, by rfl⟩ : syracuseStep 332437 = 15583) (by norm_num)
theorem B299669 : Blo 195805 299669 := bbase (se 6 (by rfl) ⟨7023, by rfl⟩ : syracuseStep 299669 = 14047) (by norm_num)
theorem B299693 : Blo 195805 299693 := bbase (se 3 (by rfl) ⟨56192, by rfl⟩ : syracuseStep 299693 = 112385) (by norm_num)
theorem B332525 : Blo 195805 332525 := bbase (se 3 (by rfl) ⟨62348, by rfl⟩ : syracuseStep 332525 = 124697) (by norm_num)
theorem B496469 : Blo 195805 496469 := bbase (se 9 (by rfl) ⟨1454, by rfl⟩ : syracuseStep 496469 = 2909) (by norm_num)
theorem B332653 : Blo 195805 332653 := bbase (se 3 (by rfl) ⟨62372, by rfl⟩ : syracuseStep 332653 = 124745) (by norm_num)
theorem B332741 : Blo 195805 332741 := bbase (se 4 (by rfl) ⟨31194, by rfl⟩ : syracuseStep 332741 = 62389) (by norm_num)
theorem B201785 : Blo 195805 201785 := bbase (se 2 (by rfl) ⟨75669, by rfl⟩ : syracuseStep 201785 = 151339) (by norm_num)
theorem B332869 : Blo 195805 332869 := bbase (se 4 (by rfl) ⟨31206, by rfl⟩ : syracuseStep 332869 = 62413) (by norm_num)
theorem B332957 : Blo 195805 332957 := bbase (se 3 (by rfl) ⟨62429, by rfl⟩ : syracuseStep 332957 = 124859) (by norm_num)
theorem B496813 : Blo 195805 496813 := bbase (se 3 (by rfl) ⟨93152, by rfl⟩ : syracuseStep 496813 = 186305) (by norm_num)
theorem B496925 : Blo 195805 496925 := bbase (se 3 (by rfl) ⟨93173, by rfl⟩ : syracuseStep 496925 = 186347) (by norm_num)
theorem B333085 : Blo 195805 333085 := bbase (se 3 (by rfl) ⟨62453, by rfl⟩ : syracuseStep 333085 = 124907) (by norm_num)
theorem B333173 : Blo 195805 333173 := bbase (se 5 (by rfl) ⟨15617, by rfl⟩ : syracuseStep 333173 = 31235) (by norm_num)
theorem B628165 : Blo 195805 628165 := bbase (se 4 (by rfl) ⟨58890, by rfl⟩ : syracuseStep 628165 = 117781) (by norm_num)
theorem B300493 : Blo 195805 300493 := bbase (se 3 (by rfl) ⟨56342, by rfl⟩ : syracuseStep 300493 = 112685) (by norm_num)
theorem B267733 : Blo 195805 267733 := bbase (se 7 (by rfl) ⟨3137, by rfl⟩ : syracuseStep 267733 = 6275) (by norm_num)
theorem B1512917 : Blo 195805 1512917 := bbase (se 7 (by rfl) ⟨17729, by rfl⟩ : syracuseStep 1512917 = 35459) (by norm_num)
theorem B497117 : Blo 195805 497117 := bbase (se 3 (by rfl) ⟨93209, by rfl⟩ : syracuseStep 497117 = 186419) (by norm_num)
theorem B333301 : Blo 195805 333301 := bbase (se 5 (by rfl) ⟨15623, by rfl⟩ : syracuseStep 333301 = 31247) (by norm_num)
theorem B661013 : Blo 195805 661013 := bbase (se 6 (by rfl) ⟨15492, by rfl⟩ : syracuseStep 661013 = 30985) (by norm_num)
theorem B529973 : Blo 195805 529973 := bbase (se 5 (by rfl) ⟨24842, by rfl⟩ : syracuseStep 529973 = 49685) (by norm_num)
theorem B333389 : Blo 195805 333389 := bbase (se 3 (by rfl) ⟨62510, by rfl⟩ : syracuseStep 333389 = 125021) (by norm_num)
theorem B333517 : Blo 195805 333517 := bbase (se 3 (by rfl) ⟨62534, by rfl⟩ : syracuseStep 333517 = 125069) (by norm_num)
theorem B268013 : Blo 195805 268013 := bbase (se 3 (by rfl) ⟨50252, by rfl⟩ : syracuseStep 268013 = 100505) (by norm_num)
theorem B333605 : Blo 195805 333605 := bbase (se 4 (by rfl) ⟨31275, by rfl⟩ : syracuseStep 333605 = 62551) (by norm_num)
theorem B497461 : Blo 195805 497461 := bbase (se 5 (by rfl) ⟨23318, by rfl⟩ : syracuseStep 497461 = 46637) (by norm_num)
theorem B497573 : Blo 195805 497573 := bbase (se 4 (by rfl) ⟨46647, by rfl⟩ : syracuseStep 497573 = 93295) (by norm_num)
theorem B333733 : Blo 195805 333733 := bbase (se 4 (by rfl) ⟨31287, by rfl⟩ : syracuseStep 333733 = 62575) (by norm_num)
theorem B661445 : Blo 195805 661445 := bbase (se 4 (by rfl) ⟨62010, by rfl⟩ : syracuseStep 661445 = 124021) (by norm_num)
theorem B956357 : Blo 195805 956357 := bbase (se 4 (by rfl) ⟨89658, by rfl⟩ : syracuseStep 956357 = 179317) (by norm_num)
theorem B333821 : Blo 195805 333821 := bbase (se 3 (by rfl) ⟨62591, by rfl⟩ : syracuseStep 333821 = 125183) (by norm_num)
theorem B497765 : Blo 195805 497765 := bbase (se 4 (by rfl) ⟨46665, by rfl⟩ : syracuseStep 497765 = 93331) (by norm_num)
theorem B333949 : Blo 195805 333949 := bbase (se 3 (by rfl) ⟨62615, by rfl⟩ : syracuseStep 333949 = 125231) (by norm_num)
theorem B563381 : Blo 195805 563381 := bbase (se 5 (by rfl) ⟨26408, by rfl⟩ : syracuseStep 563381 = 52817) (by norm_num)
theorem B5445845 : Blo 195805 5445845 := bbase (se 7 (by rfl) ⟨63818, by rfl⟩ : syracuseStep 5445845 = 127637) (by norm_num)
theorem B334037 : Blo 195805 334037 := bbase (se 7 (by rfl) ⟨3914, by rfl⟩ : syracuseStep 334037 = 7829) (by norm_num)
theorem B235769 : Blo 195805 235769 := bbase (se 2 (by rfl) ⟨88413, by rfl⟩ : syracuseStep 235769 = 176827) (by norm_num)
theorem B334165 : Blo 195805 334165 := bbase (se 10 (by rfl) ⟨489, by rfl⟩ : syracuseStep 334165 = 979) (by norm_num)
theorem B235885 : Blo 195805 235885 := bbase (se 3 (by rfl) ⟨44228, by rfl⟩ : syracuseStep 235885 = 88457) (by norm_num)
theorem B661877 : Blo 195805 661877 := bbase (se 5 (by rfl) ⟨31025, by rfl⟩ : syracuseStep 661877 = 62051) (by norm_num)
theorem B334253 : Blo 195805 334253 := bbase (se 3 (by rfl) ⟨62672, by rfl⟩ : syracuseStep 334253 = 125345) (by norm_num)
theorem B498109 : Blo 195805 498109 := bbase (se 3 (by rfl) ⟨93395, by rfl⟩ : syracuseStep 498109 = 186791) (by norm_num)
theorem B498221 : Blo 195805 498221 := bbase (se 3 (by rfl) ⟨93416, by rfl⟩ : syracuseStep 498221 = 186833) (by norm_num)
theorem B334381 : Blo 195805 334381 := bbase (se 3 (by rfl) ⟨62696, by rfl⟩ : syracuseStep 334381 = 125393) (by norm_num)
theorem B236081 : Blo 195805 236081 := bbase (se 2 (by rfl) ⟨88530, by rfl⟩ : syracuseStep 236081 = 177061) (by norm_num)
theorem B629333 : Blo 195805 629333 := bbase (se 8 (by rfl) ⟨3687, by rfl⟩ : syracuseStep 629333 = 7375) (by norm_num)
theorem B301661 : Blo 195805 301661 := bbase (se 3 (by rfl) ⟨56561, by rfl⟩ : syracuseStep 301661 = 113123) (by norm_num)
theorem B334469 : Blo 195805 334469 := bbase (se 4 (by rfl) ⟨31356, by rfl⟩ : syracuseStep 334469 = 62713) (by norm_num)
theorem B498413 : Blo 195805 498413 := bbase (se 3 (by rfl) ⟨93452, by rfl⟩ : syracuseStep 498413 = 186905) (by norm_num)
theorem B400133 : Blo 195805 400133 := bbase (se 4 (by rfl) ⟨37512, by rfl⟩ : syracuseStep 400133 = 75025) (by norm_num)
theorem B334597 : Blo 195805 334597 := bbase (se 4 (by rfl) ⟨31368, by rfl⟩ : syracuseStep 334597 = 62737) (by norm_num)
theorem B662309 : Blo 195805 662309 := bbase (se 4 (by rfl) ⟨62091, by rfl⟩ : syracuseStep 662309 = 124183) (by norm_num)
theorem B531269 : Blo 195805 531269 := bbase (se 4 (by rfl) ⟨49806, by rfl⟩ : syracuseStep 531269 = 99613) (by norm_num)
theorem B334685 : Blo 195805 334685 := bbase (se 3 (by rfl) ⟨62753, by rfl⟩ : syracuseStep 334685 = 125507) (by norm_num)
theorem B334813 : Blo 195805 334813 := bbase (se 3 (by rfl) ⟨62777, by rfl⟩ : syracuseStep 334813 = 125555) (by norm_num)
theorem B334901 : Blo 195805 334901 := bbase (se 5 (by rfl) ⟨15698, by rfl⟩ : syracuseStep 334901 = 31397) (by norm_num)
theorem B498757 : Blo 195805 498757 := bbase (se 4 (by rfl) ⟨46758, by rfl⟩ : syracuseStep 498757 = 93517) (by norm_num)
theorem B236629 : Blo 195805 236629 := bbase (se 8 (by rfl) ⟨1386, by rfl⟩ : syracuseStep 236629 = 2773) (by norm_num)
theorem B302221 : Blo 195805 302221 := bbase (se 3 (by rfl) ⟨56666, by rfl⟩ : syracuseStep 302221 = 113333) (by norm_num)
theorem B498869 : Blo 195805 498869 := bbase (se 5 (by rfl) ⟨23384, by rfl⟩ : syracuseStep 498869 = 46769) (by norm_num)
theorem B335029 : Blo 195805 335029 := bbase (se 5 (by rfl) ⟨15704, by rfl⟩ : syracuseStep 335029 = 31409) (by norm_num)
theorem B662741 : Blo 195805 662741 := bbase (se 7 (by rfl) ⟨7766, by rfl⟩ : syracuseStep 662741 = 15533) (by norm_num)
theorem B302293 : Blo 195805 302293 := bbase (se 7 (by rfl) ⟨3542, by rfl⟩ : syracuseStep 302293 = 7085) (by norm_num)
theorem B236773 : Blo 195805 236773 := bbase (se 4 (by rfl) ⟨22197, by rfl⟩ : syracuseStep 236773 = 44395) (by norm_num)
theorem B957701 : Blo 195805 957701 := bbase (se 4 (by rfl) ⟨89784, by rfl⟩ : syracuseStep 957701 = 179569) (by norm_num)
theorem B335117 : Blo 195805 335117 := bbase (se 3 (by rfl) ⟨62834, by rfl⟩ : syracuseStep 335117 = 125669) (by norm_num)
theorem B564565 : Blo 195805 564565 := bbase (se 11 (by rfl) ⟨413, by rfl⟩ : syracuseStep 564565 = 827) (by norm_num)
theorem B499061 : Blo 195805 499061 := bbase (se 5 (by rfl) ⟨23393, by rfl⟩ : syracuseStep 499061 = 46787) (by norm_num)
theorem B269693 : Blo 195805 269693 := bbase (se 3 (by rfl) ⟨50567, by rfl⟩ : syracuseStep 269693 = 101135) (by norm_num)
theorem B335245 : Blo 195805 335245 := bbase (se 3 (by rfl) ⟨62858, by rfl⟩ : syracuseStep 335245 = 125717) (by norm_num)
theorem B335333 : Blo 195805 335333 := bbase (se 4 (by rfl) ⟨31437, by rfl⟩ : syracuseStep 335333 = 62875) (by norm_num)
theorem B564725 : Blo 195805 564725 := bbase (se 5 (by rfl) ⟨26471, by rfl⟩ : syracuseStep 564725 = 52943) (by norm_num)
theorem B335461 : Blo 195805 335461 := bbase (se 4 (by rfl) ⟨31449, by rfl⟩ : syracuseStep 335461 = 62899) (by norm_num)
theorem B335477 : Blo 195805 335477 := bbase (se 5 (by rfl) ⟨15725, by rfl⟩ : syracuseStep 335477 = 31451) (by norm_num)
theorem B663173 : Blo 195805 663173 := bbase (se 4 (by rfl) ⟨62172, by rfl⟩ : syracuseStep 663173 = 124345) (by norm_num)
theorem B335549 : Blo 195805 335549 := bbase (se 3 (by rfl) ⟨62915, by rfl⟩ : syracuseStep 335549 = 125831) (by norm_num)
theorem B499405 : Blo 195805 499405 := bbase (se 3 (by rfl) ⟨93638, by rfl⟩ : syracuseStep 499405 = 187277) (by norm_num)
theorem B564965 : Blo 195805 564965 := bbase (se 4 (by rfl) ⟨52965, by rfl⟩ : syracuseStep 564965 = 105931) (by norm_num)
theorem B499517 : Blo 195805 499517 := bbase (se 3 (by rfl) ⟨93659, by rfl⟩ : syracuseStep 499517 = 187319) (by norm_num)
theorem B335677 : Blo 195805 335677 := bbase (se 3 (by rfl) ⟨62939, by rfl⟩ : syracuseStep 335677 = 125879) (by norm_num)
theorem B761717 : Blo 195805 761717 := bbase (se 5 (by rfl) ⟨35705, by rfl⟩ : syracuseStep 761717 = 71411) (by norm_num)
theorem B335765 : Blo 195805 335765 := bbase (se 6 (by rfl) ⟨7869, by rfl⟩ : syracuseStep 335765 = 15739) (by norm_num)
theorem B565157 : Blo 195805 565157 := bbase (se 4 (by rfl) ⟨52983, by rfl⟩ : syracuseStep 565157 = 105967) (by norm_num)
theorem B499709 : Blo 195805 499709 := bbase (se 3 (by rfl) ⟨93695, by rfl⟩ : syracuseStep 499709 = 187391) (by norm_num)
theorem B335893 : Blo 195805 335893 := bbase (se 6 (by rfl) ⟨7872, by rfl⟩ : syracuseStep 335893 = 15745) (by norm_num)
theorem B663605 : Blo 195805 663605 := bbase (se 5 (by rfl) ⟨31106, by rfl⟩ : syracuseStep 663605 = 62213) (by norm_num)
theorem B401501 : Blo 195805 401501 := bbase (se 3 (by rfl) ⟨75281, by rfl⟩ : syracuseStep 401501 = 150563) (by norm_num)
theorem B335981 : Blo 195805 335981 := bbase (se 3 (by rfl) ⟨62996, by rfl⟩ : syracuseStep 335981 = 125993) (by norm_num)
theorem B598213 : Blo 195805 598213 := bbase (se 4 (by rfl) ⟨56082, by rfl⟩ : syracuseStep 598213 = 112165) (by norm_num)
theorem B4923605 : Blo 195805 4923605 := bbase (se 7 (by rfl) ⟨57698, by rfl⟩ : syracuseStep 4923605 = 115397) (by norm_num)
theorem B336109 : Blo 195805 336109 := bbase (se 3 (by rfl) ⟨63020, by rfl⟩ : syracuseStep 336109 = 126041) (by norm_num)
theorem B237821 : Blo 195805 237821 := bbase (se 3 (by rfl) ⟨44591, by rfl⟩ : syracuseStep 237821 = 89183) (by norm_num)
theorem B336197 : Blo 195805 336197 := bbase (se 4 (by rfl) ⟨31518, by rfl⟩ : syracuseStep 336197 = 63037) (by norm_num)
theorem B500053 : Blo 195805 500053 := bbase (se 10 (by rfl) ⟨732, by rfl⟩ : syracuseStep 500053 = 1465) (by norm_num)
theorem B631189 : Blo 195805 631189 := bbase (se 6 (by rfl) ⟨14793, by rfl⟩ : syracuseStep 631189 = 29587) (by norm_num)
theorem B500165 : Blo 195805 500165 := bbase (se 4 (by rfl) ⟨46890, by rfl⟩ : syracuseStep 500165 = 93781) (by norm_num)
theorem B336325 : Blo 195805 336325 := bbase (se 4 (by rfl) ⟨31530, by rfl⟩ : syracuseStep 336325 = 63061) (by norm_num)
theorem B664037 : Blo 195805 664037 := bbase (se 4 (by rfl) ⟨62253, by rfl⟩ : syracuseStep 664037 = 124507) (by norm_num)
theorem B336413 : Blo 195805 336413 := bbase (se 3 (by rfl) ⟨63077, by rfl⟩ : syracuseStep 336413 = 126155) (by norm_num)
theorem B238153 : Blo 195805 238153 := bbase (se 2 (by rfl) ⟨89307, by rfl⟩ : syracuseStep 238153 = 178615) (by norm_num)
theorem B402013 : Blo 195805 402013 := bbase (se 3 (by rfl) ⟨75377, by rfl⟩ : syracuseStep 402013 = 150755) (by norm_num)
theorem B500357 : Blo 195805 500357 := bbase (se 4 (by rfl) ⟨46908, by rfl⟩ : syracuseStep 500357 = 93817) (by norm_num)
theorem B336541 : Blo 195805 336541 := bbase (se 3 (by rfl) ⟨63101, by rfl⟩ : syracuseStep 336541 = 126203) (by norm_num)
theorem B991925 : Blo 195805 991925 := bbase (se 5 (by rfl) ⟨46496, by rfl⟩ : syracuseStep 991925 = 92993) (by norm_num)
theorem B336629 : Blo 195805 336629 := bbase (se 5 (by rfl) ⟨15779, by rfl⟩ : syracuseStep 336629 = 31559) (by norm_num)
theorem B336757 : Blo 195805 336757 := bbase (se 5 (by rfl) ⟨15785, by rfl⟩ : syracuseStep 336757 = 31571) (by norm_num)
theorem B566149 : Blo 195805 566149 := bbase (se 4 (by rfl) ⟨53076, by rfl⟩ : syracuseStep 566149 = 106153) (by norm_num)
theorem B664469 : Blo 195805 664469 := bbase (se 6 (by rfl) ⟨15573, by rfl⟩ : syracuseStep 664469 = 31147) (by norm_num)
theorem B1123253 : Blo 195805 1123253 := bbase (se 5 (by rfl) ⟨52652, by rfl⟩ : syracuseStep 1123253 = 105305) (by norm_num)
theorem B336845 : Blo 195805 336845 := bbase (se 3 (by rfl) ⟨63158, by rfl⟩ : syracuseStep 336845 = 126317) (by norm_num)
theorem B500701 : Blo 195805 500701 := bbase (se 3 (by rfl) ⟨93881, by rfl⟩ : syracuseStep 500701 = 187763) (by norm_num)
theorem B500813 : Blo 195805 500813 := bbase (se 3 (by rfl) ⟨93902, by rfl⟩ : syracuseStep 500813 = 187805) (by norm_num)
theorem B336973 : Blo 195805 336973 := bbase (se 3 (by rfl) ⟨63182, by rfl⟩ : syracuseStep 336973 = 126365) (by norm_num)
theorem B271517 : Blo 195805 271517 := bbase (se 3 (by rfl) ⟨50909, by rfl⟩ : syracuseStep 271517 = 101819) (by norm_num)
theorem B337061 : Blo 195805 337061 := bbase (se 4 (by rfl) ⟨31599, by rfl⟩ : syracuseStep 337061 = 63199) (by norm_num)
theorem B959701 : Blo 195805 959701 := bbase (se 7 (by rfl) ⟨11246, by rfl⟩ : syracuseStep 959701 = 22493) (by norm_num)
theorem B501005 : Blo 195805 501005 := bbase (se 3 (by rfl) ⟨93938, by rfl⟩ : syracuseStep 501005 = 187877) (by norm_num)
theorem B664901 : Blo 195805 664901 := bbase (se 4 (by rfl) ⟨62334, by rfl⟩ : syracuseStep 664901 = 124669) (by norm_num)
theorem B599381 : Blo 195805 599381 := bbase (se 12 (by rfl) ⟨219, by rfl⟩ : syracuseStep 599381 = 439) (by norm_num)
theorem B599429 : Blo 195805 599429 := bbase (se 4 (by rfl) ⟨56196, by rfl⟩ : syracuseStep 599429 = 112393) (by norm_num)
theorem B239041 : Blo 195805 239041 := bbase (se 2 (by rfl) ⟨89640, by rfl⟩ : syracuseStep 239041 = 179281) (by norm_num)
theorem B2139605 : Blo 195805 2139605 := bbase (se 7 (by rfl) ⟨25073, by rfl⟩ : syracuseStep 2139605 = 50147) (by norm_num)
theorem B2041301 : Blo 195805 2041301 := bbase (se 7 (by rfl) ⟨23921, by rfl⟩ : syracuseStep 2041301 = 47843) (by norm_num)
theorem B763397 : Blo 195805 763397 := bbase (se 4 (by rfl) ⟨71568, by rfl⟩ : syracuseStep 763397 = 143137) (by norm_num)
theorem B501349 : Blo 195805 501349 := bbase (se 4 (by rfl) ⟨47001, by rfl⟩ : syracuseStep 501349 = 94003) (by norm_num)
theorem B501461 : Blo 195805 501461 := bbase (se 7 (by rfl) ⟨5876, by rfl⟩ : syracuseStep 501461 = 11753) (by norm_num)
theorem B403157 : Blo 195805 403157 := bbase (se 7 (by rfl) ⟨4724, by rfl⟩ : syracuseStep 403157 = 9449) (by norm_num)
theorem B632549 : Blo 195805 632549 := bbase (se 4 (by rfl) ⟨59301, by rfl⟩ : syracuseStep 632549 = 118603) (by norm_num)
theorem B665333 : Blo 195805 665333 := bbase (se 5 (by rfl) ⟨31187, by rfl⟩ : syracuseStep 665333 = 62375) (by norm_num)
theorem B861941 : Blo 195805 861941 := bbase (se 5 (by rfl) ⟨40403, by rfl⟩ : syracuseStep 861941 = 80807) (by norm_num)
theorem B1058645 : Blo 195805 1058645 := bbase (se 9 (by rfl) ⟨3101, by rfl⟩ : syracuseStep 1058645 = 6203) (by norm_num)
theorem B501653 : Blo 195805 501653 := bbase (se 6 (by rfl) ⟨11757, by rfl⟩ : syracuseStep 501653 = 23515) (by norm_num)
theorem B993221 : Blo 195805 993221 := bbase (se 4 (by rfl) ⟨93114, by rfl⟩ : syracuseStep 993221 = 186229) (by norm_num)
theorem B567253 : Blo 195805 567253 := bbase (se 7 (by rfl) ⟨6647, by rfl⟩ : syracuseStep 567253 = 13295) (by norm_num)
theorem B665765 : Blo 195805 665765 := bbase (se 4 (by rfl) ⟨62415, by rfl⟩ : syracuseStep 665765 = 124831) (by norm_num)
theorem B501997 : Blo 195805 501997 := bbase (se 3 (by rfl) ⟨94124, by rfl⟩ : syracuseStep 501997 = 188249) (by norm_num)
theorem B502109 : Blo 195805 502109 := bbase (se 3 (by rfl) ⟨94145, by rfl⟩ : syracuseStep 502109 = 188291) (by norm_num)
theorem B895349 : Blo 195805 895349 := bbase (se 5 (by rfl) ⟨41969, by rfl⟩ : syracuseStep 895349 = 83939) (by norm_num)
theorem B502301 : Blo 195805 502301 := bbase (se 3 (by rfl) ⟨94181, by rfl⟩ : syracuseStep 502301 = 188363) (by norm_num)
theorem B666197 : Blo 195805 666197 := bbase (se 8 (by rfl) ⟨3903, by rfl⟩ : syracuseStep 666197 = 7807) (by norm_num)
theorem B2730709 : Blo 195805 2730709 := bbase (se 7 (by rfl) ⟨32000, by rfl⟩ : syracuseStep 2730709 = 64001) (by norm_num)
theorem B240481 : Blo 195805 240481 := bbase (se 2 (by rfl) ⟨90180, by rfl⟩ : syracuseStep 240481 = 180361) (by norm_num)
theorem B502645 : Blo 195805 502645 := bbase (se 5 (by rfl) ⟨23561, by rfl⟩ : syracuseStep 502645 = 47123) (by norm_num)
theorem B502757 : Blo 195805 502757 := bbase (se 4 (by rfl) ⟨47133, by rfl⟩ : syracuseStep 502757 = 94267) (by norm_num)
theorem B666629 : Blo 195805 666629 := bbase (se 4 (by rfl) ⟨62496, by rfl⟩ : syracuseStep 666629 = 124993) (by norm_num)
theorem B797845 : Blo 195805 797845 := bbase (se 6 (by rfl) ⟨18699, by rfl⟩ : syracuseStep 797845 = 37399) (by norm_num)
theorem B339109 : Blo 195805 339109 := bbase (se 4 (by rfl) ⟨31791, by rfl⟩ : syracuseStep 339109 = 63583) (by norm_num)
theorem B502949 : Blo 195805 502949 := bbase (se 4 (by rfl) ⟨47151, by rfl⟩ : syracuseStep 502949 = 94303) (by norm_num)
theorem B994517 : Blo 195805 994517 := bbase (se 7 (by rfl) ⟨11654, by rfl⟩ : syracuseStep 994517 = 23309) (by norm_num)
theorem B371965 : Blo 195805 371965 := bbase (se 3 (by rfl) ⟨69743, by rfl⟩ : syracuseStep 371965 = 139487) (by norm_num)
theorem B372109 : Blo 195805 372109 := bbase (se 3 (by rfl) ⟨69770, by rfl⟩ : syracuseStep 372109 = 139541) (by norm_num)
theorem B667061 : Blo 195805 667061 := bbase (se 5 (by rfl) ⟨31268, by rfl⟩ : syracuseStep 667061 = 62537) (by norm_num)
theorem B568757 : Blo 195805 568757 := bbase (se 5 (by rfl) ⟨26660, by rfl⟩ : syracuseStep 568757 = 53321) (by norm_num)
theorem B503293 : Blo 195805 503293 := bbase (se 3 (by rfl) ⟨94367, by rfl⟩ : syracuseStep 503293 = 188735) (by norm_num)
theorem B372269 : Blo 195805 372269 := bbase (se 3 (by rfl) ⟨69800, by rfl⟩ : syracuseStep 372269 = 139601) (by norm_num)
theorem B405037 : Blo 195805 405037 := bbase (se 3 (by rfl) ⟨75944, by rfl⟩ : syracuseStep 405037 = 151889) (by norm_num)
theorem B503405 : Blo 195805 503405 := bbase (se 3 (by rfl) ⟨94388, by rfl⟩ : syracuseStep 503405 = 188777) (by norm_num)
theorem B470701 : Blo 195805 470701 := bbase (se 3 (by rfl) ⟨88256, by rfl⟩ : syracuseStep 470701 = 176513) (by norm_num)
theorem B372413 : Blo 195805 372413 := bbase (se 3 (by rfl) ⟨69827, by rfl⟩ : syracuseStep 372413 = 139655) (by norm_num)
theorem B503597 : Blo 195805 503597 := bbase (se 3 (by rfl) ⟨94424, by rfl⟩ : syracuseStep 503597 = 188849) (by norm_num)
theorem B667493 : Blo 195805 667493 := bbase (se 4 (by rfl) ⟨62577, by rfl⟩ : syracuseStep 667493 = 125155) (by norm_num)
theorem B372701 : Blo 195805 372701 := bbase (se 3 (by rfl) ⟨69881, by rfl⟩ : syracuseStep 372701 = 139763) (by norm_num)
theorem B339965 : Blo 195805 339965 := bbase (se 3 (by rfl) ⟨63743, by rfl⟩ : syracuseStep 339965 = 127487) (by norm_num)
theorem B372853 : Blo 195805 372853 := bbase (se 5 (by rfl) ⟨17477, by rfl⟩ : syracuseStep 372853 = 34955) (by norm_num)
theorem B503941 : Blo 195805 503941 := bbase (se 4 (by rfl) ⟨47244, by rfl⟩ : syracuseStep 503941 = 94489) (by norm_num)
theorem B504053 : Blo 195805 504053 := bbase (se 5 (by rfl) ⟨23627, by rfl⟩ : syracuseStep 504053 = 47255) (by norm_num)
theorem B667925 : Blo 195805 667925 := bbase (se 6 (by rfl) ⟨15654, by rfl⟩ : syracuseStep 667925 = 31309) (by norm_num)
theorem B471413 : Blo 195805 471413 := bbase (se 5 (by rfl) ⟨22097, by rfl⟩ : syracuseStep 471413 = 44195) (by norm_num)
theorem B373157 : Blo 195805 373157 := bbase (se 4 (by rfl) ⟨34983, by rfl⟩ : syracuseStep 373157 = 69967) (by norm_num)
theorem B504245 : Blo 195805 504245 := bbase (se 5 (by rfl) ⟨23636, by rfl⟩ : syracuseStep 504245 = 47273) (by norm_num)
theorem B995813 : Blo 195805 995813 := bbase (se 4 (by rfl) ⟨93357, by rfl⟩ : syracuseStep 995813 = 186715) (by norm_num)
theorem B209525 : Blo 195805 209525 := bbase (se 5 (by rfl) ⟨9821, by rfl⟩ : syracuseStep 209525 = 19643) (by norm_num)
theorem B209585 : Blo 195805 209585 := bbase (se 2 (by rfl) ⟨78594, by rfl⟩ : syracuseStep 209585 = 157189) (by norm_num)
theorem B668357 : Blo 195805 668357 := bbase (se 4 (by rfl) ⟨62658, by rfl⟩ : syracuseStep 668357 = 125317) (by norm_num)
theorem B1913557 : Blo 195805 1913557 := bbase (se 7 (by rfl) ⟨22424, by rfl⟩ : syracuseStep 1913557 = 44849) (by norm_num)
theorem B504589 : Blo 195805 504589 := bbase (se 3 (by rfl) ⟨94610, by rfl⟩ : syracuseStep 504589 = 189221) (by norm_num)
theorem B209713 : Blo 195805 209713 := bbase (se 2 (by rfl) ⟨78642, by rfl⟩ : syracuseStep 209713 = 157285) (by norm_num)
theorem B504701 : Blo 195805 504701 := bbase (se 3 (by rfl) ⟨94631, by rfl⟩ : syracuseStep 504701 = 189263) (by norm_num)
theorem B472085 : Blo 195805 472085 := bbase (se 6 (by rfl) ⟨11064, by rfl⟩ : syracuseStep 472085 = 22129) (by norm_num)
theorem B635957 : Blo 195805 635957 := bbase (se 5 (by rfl) ⟨29810, by rfl⟩ : syracuseStep 635957 = 59621) (by norm_num)
theorem B504893 : Blo 195805 504893 := bbase (se 3 (by rfl) ⟨94667, by rfl⟩ : syracuseStep 504893 = 189335) (by norm_num)
theorem B668789 : Blo 195805 668789 := bbase (se 5 (by rfl) ⟨31349, by rfl⟩ : syracuseStep 668789 = 62699) (by norm_num)
theorem B373909 : Blo 195805 373909 := bbase (se 6 (by rfl) ⟨8763, by rfl⟩ : syracuseStep 373909 = 17527) (by norm_num)
theorem B210157 : Blo 195805 210157 := bbase (se 3 (by rfl) ⟨39404, by rfl⟩ : syracuseStep 210157 = 78809) (by norm_num)
theorem B374053 : Blo 195805 374053 := bbase (se 4 (by rfl) ⟨35067, by rfl⟩ : syracuseStep 374053 = 70135) (by norm_num)
theorem B210277 : Blo 195805 210277 := bbase (se 4 (by rfl) ⟨19713, by rfl⟩ : syracuseStep 210277 = 39427) (by norm_num)
theorem B505237 : Blo 195805 505237 := bbase (se 6 (by rfl) ⟨11841, by rfl⟩ : syracuseStep 505237 = 23683) (by norm_num)
theorem B374213 : Blo 195805 374213 := bbase (se 4 (by rfl) ⟨35082, by rfl⟩ : syracuseStep 374213 = 70165) (by norm_num)
theorem B603605 : Blo 195805 603605 := bbase (se 7 (by rfl) ⟨7073, by rfl⟩ : syracuseStep 603605 = 14147) (by norm_num)
theorem B505349 : Blo 195805 505349 := bbase (se 4 (by rfl) ⟨47376, by rfl⟩ : syracuseStep 505349 = 94753) (by norm_num)
theorem B669221 : Blo 195805 669221 := bbase (se 4 (by rfl) ⟨62739, by rfl⟩ : syracuseStep 669221 = 125479) (by norm_num)
theorem B374357 : Blo 195805 374357 := bbase (se 8 (by rfl) ⟨2193, by rfl⟩ : syracuseStep 374357 = 4387) (by norm_num)
theorem B210529 : Blo 195805 210529 := bbase (se 2 (by rfl) ⟨78948, by rfl⟩ : syracuseStep 210529 = 157897) (by norm_num)
theorem B210533 : Blo 195805 210533 := bbase (se 4 (by rfl) ⟨19737, by rfl⟩ : syracuseStep 210533 = 39475) (by norm_num)
theorem B505541 : Blo 195805 505541 := bbase (se 4 (by rfl) ⟨47394, by rfl⟩ : syracuseStep 505541 = 94789) (by norm_num)
theorem B341741 : Blo 195805 341741 := bbase (se 3 (by rfl) ⟨64076, by rfl⟩ : syracuseStep 341741 = 128153) (by norm_num)
theorem B997109 : Blo 195805 997109 := bbase (se 5 (by rfl) ⟨46739, by rfl⟩ : syracuseStep 997109 = 93479) (by norm_num)
theorem B571141 : Blo 195805 571141 := bbase (se 4 (by rfl) ⟨53544, by rfl⟩ : syracuseStep 571141 = 107089) (by norm_num)
theorem B374645 : Blo 195805 374645 := bbase (se 5 (by rfl) ⟨17561, by rfl⟩ : syracuseStep 374645 = 35123) (by norm_num)
theorem B669653 : Blo 195805 669653 := bbase (se 7 (by rfl) ⟨7847, by rfl⟩ : syracuseStep 669653 = 15695) (by norm_num)
theorem B538613 : Blo 195805 538613 := bbase (se 5 (by rfl) ⟨25247, by rfl⟩ : syracuseStep 538613 = 50495) (by norm_num)
theorem B374797 : Blo 195805 374797 := bbase (se 3 (by rfl) ⟨70274, by rfl⟩ : syracuseStep 374797 = 140549) (by norm_num)
theorem B211097 : Blo 195805 211097 := bbase (se 2 (by rfl) ⟨79161, by rfl⟩ : syracuseStep 211097 = 158323) (by norm_num)
theorem B440621 : Blo 195805 440621 := bbase (se 3 (by rfl) ⟨82616, by rfl⟩ : syracuseStep 440621 = 165233) (by norm_num)
theorem B637237 : Blo 195805 637237 := bbase (se 5 (by rfl) ⟨29870, by rfl⟩ : syracuseStep 637237 = 59741) (by norm_num)
theorem B375101 : Blo 195805 375101 := bbase (se 3 (by rfl) ⟨70331, by rfl⟩ : syracuseStep 375101 = 140663) (by norm_num)
theorem B211285 : Blo 195805 211285 := bbase (se 10 (by rfl) ⟨309, by rfl⟩ : syracuseStep 211285 = 619) (by norm_num)
theorem B440693 : Blo 195805 440693 := bbase (se 5 (by rfl) ⟨20657, by rfl⟩ : syracuseStep 440693 = 41315) (by norm_num)
theorem B670085 : Blo 195805 670085 := bbase (se 4 (by rfl) ⟨62820, by rfl⟩ : syracuseStep 670085 = 125641) (by norm_num)
theorem B506261 : Blo 195805 506261 := bbase (se 6 (by rfl) ⟨11865, by rfl⟩ : syracuseStep 506261 = 23731) (by norm_num)
theorem B539045 : Blo 195805 539045 := bbase (se 4 (by rfl) ⟨50535, by rfl⟩ : syracuseStep 539045 = 101071) (by norm_num)
theorem B440765 : Blo 195805 440765 := bbase (se 3 (by rfl) ⟨82643, by rfl⟩ : syracuseStep 440765 = 165287) (by norm_num)
theorem B440837 : Blo 195805 440837 := bbase (se 4 (by rfl) ⟨41328, by rfl⟩ : syracuseStep 440837 = 82657) (by norm_num)
theorem B440909 : Blo 195805 440909 := bbase (se 3 (by rfl) ⟨82670, by rfl⟩ : syracuseStep 440909 = 165341) (by norm_num)
theorem B440981 : Blo 195805 440981 := bbase (se 6 (by rfl) ⟨10335, by rfl⟩ : syracuseStep 440981 = 20671) (by norm_num)
theorem B1489589 : Blo 195805 1489589 := bbase (se 5 (by rfl) ⟨69824, by rfl⟩ : syracuseStep 1489589 = 139649) (by norm_num)
theorem B408269 : Blo 195805 408269 := bbase (se 3 (by rfl) ⟨76550, by rfl⟩ : syracuseStep 408269 = 153101) (by norm_num)
theorem B441053 : Blo 195805 441053 := bbase (se 3 (by rfl) ⟨82697, by rfl⟩ : syracuseStep 441053 = 165395) (by norm_num)
theorem B473845 : Blo 195805 473845 := bbase (se 5 (by rfl) ⟨22211, by rfl⟩ : syracuseStep 473845 = 44423) (by norm_num)
theorem B441125 : Blo 195805 441125 := bbase (se 4 (by rfl) ⟨41355, by rfl⟩ : syracuseStep 441125 = 82711) (by norm_num)
theorem B670517 : Blo 195805 670517 := bbase (se 5 (by rfl) ⟨31430, by rfl⟩ : syracuseStep 670517 = 62861) (by norm_num)
theorem B441197 : Blo 195805 441197 := bbase (se 3 (by rfl) ⟨82724, by rfl⟩ : syracuseStep 441197 = 165449) (by norm_num)
theorem B441269 : Blo 195805 441269 := bbase (se 5 (by rfl) ⟨20684, by rfl⟩ : syracuseStep 441269 = 41369) (by norm_num)
theorem B441341 : Blo 195805 441341 := bbase (se 3 (by rfl) ⟨82751, by rfl⟩ : syracuseStep 441341 = 165503) (by norm_num)
theorem B998405 : Blo 195805 998405 := bbase (se 4 (by rfl) ⟨93600, by rfl⟩ : syracuseStep 998405 = 187201) (by norm_num)
theorem B375853 : Blo 195805 375853 := bbase (se 3 (by rfl) ⟨70472, by rfl⟩ : syracuseStep 375853 = 140945) (by norm_num)
theorem B1883189 : Blo 195805 1883189 := bbase (se 5 (by rfl) ⟨88274, by rfl⟩ : syracuseStep 1883189 = 176549) (by norm_num)
theorem B441413 : Blo 195805 441413 := bbase (se 4 (by rfl) ⟨41382, by rfl⟩ : syracuseStep 441413 = 82765) (by norm_num)
theorem B212105 : Blo 195805 212105 := bbase (se 2 (by rfl) ⟨79539, by rfl⟩ : syracuseStep 212105 = 159079) (by norm_num)
theorem B441485 : Blo 195805 441485 := bbase (se 3 (by rfl) ⟨82778, by rfl⟩ : syracuseStep 441485 = 165557) (by norm_num)
theorem B375997 : Blo 195805 375997 := bbase (se 3 (by rfl) ⟨70499, by rfl⟩ : syracuseStep 375997 = 140999) (by norm_num)
theorem B441557 : Blo 195805 441557 := bbase (se 7 (by rfl) ⟨5174, by rfl⟩ : syracuseStep 441557 = 10349) (by norm_num)
theorem B670949 : Blo 195805 670949 := bbase (se 4 (by rfl) ⟨62901, by rfl⟩ : syracuseStep 670949 = 125803) (by norm_num)
theorem B2243861 : Blo 195805 2243861 := bbase (se 6 (by rfl) ⟨52590, by rfl⟩ : syracuseStep 2243861 = 105181) (by norm_num)
theorem B441629 : Blo 195805 441629 := bbase (se 3 (by rfl) ⟨82805, by rfl⟩ : syracuseStep 441629 = 165611) (by norm_num)
theorem B474461 : Blo 195805 474461 := bbase (se 3 (by rfl) ⟨88961, by rfl⟩ : syracuseStep 474461 = 177923) (by norm_num)
theorem B376157 : Blo 195805 376157 := bbase (se 3 (by rfl) ⟨70529, by rfl⟩ : syracuseStep 376157 = 141059) (by norm_num)
theorem B441701 : Blo 195805 441701 := bbase (se 4 (by rfl) ⟨41409, by rfl⟩ : syracuseStep 441701 = 82819) (by norm_num)
theorem B4078997 : Blo 195805 4078997 := bbase (se 6 (by rfl) ⟨95601, by rfl⟩ : syracuseStep 4078997 = 191203) (by norm_num)
theorem B441773 : Blo 195805 441773 := bbase (se 3 (by rfl) ⟨82832, by rfl⟩ : syracuseStep 441773 = 165665) (by norm_num)
theorem B376301 : Blo 195805 376301 := bbase (se 3 (by rfl) ⟨70556, by rfl⟩ : syracuseStep 376301 = 141113) (by norm_num)
theorem B441845 : Blo 195805 441845 := bbase (se 5 (by rfl) ⟨20711, by rfl⟩ : syracuseStep 441845 = 41423) (by norm_num)
theorem B1916405 : Blo 195805 1916405 := bbase (se 5 (by rfl) ⟨89831, by rfl⟩ : syracuseStep 1916405 = 179663) (by norm_num)
theorem B441917 : Blo 195805 441917 := bbase (se 3 (by rfl) ⟨82859, by rfl⟩ : syracuseStep 441917 = 165719) (by norm_num)
theorem B212549 : Blo 195805 212549 := bbase (se 4 (by rfl) ⟨19926, by rfl⟩ : syracuseStep 212549 = 39853) (by norm_num)
theorem B441989 : Blo 195805 441989 := bbase (se 4 (by rfl) ⟨41436, by rfl⟩ : syracuseStep 441989 = 82873) (by norm_num)
theorem B638597 : Blo 195805 638597 := bbase (se 4 (by rfl) ⟨59868, by rfl⟩ : syracuseStep 638597 = 119737) (by norm_num)
theorem B671381 : Blo 195805 671381 := bbase (se 6 (by rfl) ⟨15735, by rfl⟩ : syracuseStep 671381 = 31471) (by norm_num)
theorem B442061 : Blo 195805 442061 := bbase (se 3 (by rfl) ⟨82886, by rfl⟩ : syracuseStep 442061 = 165773) (by norm_num)
theorem B638725 : Blo 195805 638725 := bbase (se 4 (by rfl) ⟨59880, by rfl⟩ : syracuseStep 638725 = 119761) (by norm_num)
theorem B376589 : Blo 195805 376589 := bbase (se 3 (by rfl) ⟨70610, by rfl⟩ : syracuseStep 376589 = 141221) (by norm_num)
theorem B442133 : Blo 195805 442133 := bbase (se 6 (by rfl) ⟨10362, by rfl⟩ : syracuseStep 442133 = 20725) (by norm_num)
theorem B212797 : Blo 195805 212797 := bbase (se 3 (by rfl) ⟨39899, by rfl⟩ : syracuseStep 212797 = 79799) (by norm_num)
theorem B442205 : Blo 195805 442205 := bbase (se 3 (by rfl) ⟨82913, by rfl⟩ : syracuseStep 442205 = 165827) (by norm_num)
theorem B442277 : Blo 195805 442277 := bbase (se 4 (by rfl) ⟨41463, by rfl⟩ : syracuseStep 442277 = 82927) (by norm_num)
theorem B376741 : Blo 195805 376741 := bbase (se 4 (by rfl) ⟨35319, by rfl⟩ : syracuseStep 376741 = 70639) (by norm_num)
theorem B606133 : Blo 195805 606133 := bbase (se 5 (by rfl) ⟨28412, by rfl⟩ : syracuseStep 606133 = 56825) (by norm_num)
theorem B2015189 : Blo 195805 2015189 := bbase (se 7 (by rfl) ⟨23615, by rfl⟩ : syracuseStep 2015189 = 47231) (by norm_num)
theorem B442349 : Blo 195805 442349 := bbase (se 3 (by rfl) ⟨82940, by rfl⟩ : syracuseStep 442349 = 165881) (by norm_num)
theorem B638981 : Blo 195805 638981 := bbase (se 4 (by rfl) ⟨59904, by rfl⟩ : syracuseStep 638981 = 119809) (by norm_num)
theorem B442421 : Blo 195805 442421 := bbase (se 5 (by rfl) ⟨20738, by rfl⟩ : syracuseStep 442421 = 41477) (by norm_num)
theorem B671813 : Blo 195805 671813 := bbase (se 4 (by rfl) ⟨62982, by rfl⟩ : syracuseStep 671813 = 125965) (by norm_num)
theorem B475229 : Blo 195805 475229 := bbase (se 3 (by rfl) ⟨89105, by rfl⟩ : syracuseStep 475229 = 178211) (by norm_num)
theorem B475237 : Blo 195805 475237 := bbase (se 4 (by rfl) ⟨44553, by rfl⟩ : syracuseStep 475237 = 89107) (by norm_num)
theorem B442493 : Blo 195805 442493 := bbase (se 3 (by rfl) ⟨82967, by rfl⟩ : syracuseStep 442493 = 165935) (by norm_num)
theorem B213125 : Blo 195805 213125 := bbase (se 4 (by rfl) ⟨19980, by rfl⟩ : syracuseStep 213125 = 39961) (by norm_num)
theorem B442565 : Blo 195805 442565 := bbase (se 4 (by rfl) ⟨41490, by rfl⟩ : syracuseStep 442565 = 82981) (by norm_num)
theorem B377045 : Blo 195805 377045 := bbase (se 7 (by rfl) ⟨4418, by rfl⟩ : syracuseStep 377045 = 8837) (by norm_num)
theorem B606437 : Blo 195805 606437 := bbase (se 4 (by rfl) ⟨56853, by rfl⟩ : syracuseStep 606437 = 113707) (by norm_num)
theorem B213229 : Blo 195805 213229 := bbase (se 3 (by rfl) ⟨39980, by rfl⟩ : syracuseStep 213229 = 79961) (by norm_num)
theorem B278797 : Blo 195805 278797 := bbase (se 3 (by rfl) ⟨52274, by rfl⟩ : syracuseStep 278797 = 104549) (by norm_num)
theorem B442637 : Blo 195805 442637 := bbase (se 3 (by rfl) ⟨82994, by rfl⟩ : syracuseStep 442637 = 165989) (by norm_num)
theorem B999701 : Blo 195805 999701 := bbase (se 6 (by rfl) ⟨23430, by rfl⟩ : syracuseStep 999701 = 46861) (by norm_num)
theorem B213301 : Blo 195805 213301 := bbase (se 5 (by rfl) ⟨9998, by rfl⟩ : syracuseStep 213301 = 19997) (by norm_num)
theorem B442709 : Blo 195805 442709 := bbase (se 10 (by rfl) ⟨648, by rfl⟩ : syracuseStep 442709 = 1297) (by norm_num)
theorem B1589653 : Blo 195805 1589653 := bbase (se 6 (by rfl) ⟨37257, by rfl⟩ : syracuseStep 1589653 = 74515) (by norm_num)
theorem B442781 : Blo 195805 442781 := bbase (se 3 (by rfl) ⟨83021, by rfl⟩ : syracuseStep 442781 = 166043) (by norm_num)
theorem B442853 : Blo 195805 442853 := bbase (se 4 (by rfl) ⟨41517, by rfl⟩ : syracuseStep 442853 = 83035) (by norm_num)
theorem B672245 : Blo 195805 672245 := bbase (se 5 (by rfl) ⟨31511, by rfl⟩ : syracuseStep 672245 = 63023) (by norm_num)
theorem B442925 : Blo 195805 442925 := bbase (se 3 (by rfl) ⟨83048, by rfl⟩ : syracuseStep 442925 = 166097) (by norm_num)
theorem B770629 : Blo 195805 770629 := bbase (se 4 (by rfl) ⟨72246, by rfl⟩ : syracuseStep 770629 = 144493) (by norm_num)
theorem B442997 : Blo 195805 442997 := bbase (se 5 (by rfl) ⟨20765, by rfl⟩ : syracuseStep 442997 = 41531) (by norm_num)
theorem B279173 : Blo 195805 279173 := bbase (se 4 (by rfl) ⟨26172, by rfl⟩ : syracuseStep 279173 = 52345) (by norm_num)
theorem B443069 : Blo 195805 443069 := bbase (se 3 (by rfl) ⟨83075, by rfl⟩ : syracuseStep 443069 = 166151) (by norm_num)
theorem B443141 : Blo 195805 443141 := bbase (se 4 (by rfl) ⟨41544, by rfl⟩ : syracuseStep 443141 = 83089) (by norm_num)
theorem B1131317 : Blo 195805 1131317 := bbase (se 5 (by rfl) ⟨53030, by rfl⟩ : syracuseStep 1131317 = 106061) (by norm_num)
theorem B443213 : Blo 195805 443213 := bbase (se 3 (by rfl) ⟨83102, by rfl⟩ : syracuseStep 443213 = 166205) (by norm_num)
theorem B476045 : Blo 195805 476045 := bbase (se 3 (by rfl) ⟨89258, by rfl⟩ : syracuseStep 476045 = 178517) (by norm_num)
theorem B443285 : Blo 195805 443285 := bbase (se 6 (by rfl) ⟨10389, by rfl⟩ : syracuseStep 443285 = 20779) (by norm_num)
theorem B574373 : Blo 195805 574373 := bbase (se 4 (by rfl) ⟨53847, by rfl⟩ : syracuseStep 574373 = 107695) (by norm_num)
theorem B672677 : Blo 195805 672677 := bbase (se 4 (by rfl) ⟨63063, by rfl⟩ : syracuseStep 672677 = 126127) (by norm_num)
theorem B377797 : Blo 195805 377797 := bbase (se 4 (by rfl) ⟨35418, by rfl⟩ : syracuseStep 377797 = 70837) (by norm_num)
theorem B443357 : Blo 195805 443357 := bbase (se 3 (by rfl) ⟨83129, by rfl⟩ : syracuseStep 443357 = 166259) (by norm_num)
theorem B443429 : Blo 195805 443429 := bbase (se 4 (by rfl) ⟨41571, by rfl⟩ : syracuseStep 443429 = 83143) (by norm_num)
theorem B1197109 : Blo 195805 1197109 := bbase (se 5 (by rfl) ⟨56114, by rfl⟩ : syracuseStep 1197109 = 112229) (by norm_num)
theorem B803909 : Blo 195805 803909 := bbase (se 4 (by rfl) ⟨75366, by rfl⟩ : syracuseStep 803909 = 150733) (by norm_num)
theorem B607301 : Blo 195805 607301 := bbase (se 4 (by rfl) ⟨56934, by rfl⟩ : syracuseStep 607301 = 113869) (by norm_num)
theorem B377941 : Blo 195805 377941 := bbase (se 8 (by rfl) ⟨2214, by rfl⟩ : syracuseStep 377941 = 4429) (by norm_num)
theorem B443501 : Blo 195805 443501 := bbase (se 3 (by rfl) ⟨83156, by rfl⟩ : syracuseStep 443501 = 166313) (by norm_num)
theorem B443573 : Blo 195805 443573 := bbase (se 5 (by rfl) ⟨20792, by rfl⟩ : syracuseStep 443573 = 41585) (by norm_num)
theorem B836837 : Blo 195805 836837 := bbase (se 4 (by rfl) ⟨78453, by rfl⟩ : syracuseStep 836837 = 156907) (by norm_num)
theorem B378101 : Blo 195805 378101 := bbase (se 5 (by rfl) ⟨17723, by rfl⟩ : syracuseStep 378101 = 35447) (by norm_num)
theorem B443645 : Blo 195805 443645 := bbase (se 3 (by rfl) ⟨83183, by rfl⟩ : syracuseStep 443645 = 166367) (by norm_num)
theorem B1525013 : Blo 195805 1525013 := bbase (se 6 (by rfl) ⟨35742, by rfl⟩ : syracuseStep 1525013 = 71485) (by norm_num)
theorem B443717 : Blo 195805 443717 := bbase (se 4 (by rfl) ⟨41598, by rfl⟩ : syracuseStep 443717 = 83197) (by norm_num)
theorem B673109 : Blo 195805 673109 := bbase (se 12 (by rfl) ⟨246, by rfl⟩ : syracuseStep 673109 = 493) (by norm_num)
theorem B378245 : Blo 195805 378245 := bbase (se 4 (by rfl) ⟨35460, by rfl⟩ : syracuseStep 378245 = 70921) (by norm_num)
theorem B443789 : Blo 195805 443789 := bbase (se 3 (by rfl) ⟨83210, by rfl⟩ : syracuseStep 443789 = 166421) (by norm_num)
theorem B443861 : Blo 195805 443861 := bbase (se 7 (by rfl) ⟨5201, by rfl⟩ : syracuseStep 443861 = 10403) (by norm_num)
theorem B1066517 : Blo 195805 1066517 := bbase (se 6 (by rfl) ⟨24996, by rfl⟩ : syracuseStep 1066517 = 49993) (by norm_num)
theorem B443933 : Blo 195805 443933 := bbase (se 3 (by rfl) ⟨83237, by rfl⟩ : syracuseStep 443933 = 166475) (by norm_num)
theorem B1000997 : Blo 195805 1000997 := bbase (se 4 (by rfl) ⟨93843, by rfl⟩ : syracuseStep 1000997 = 187687) (by norm_num)
theorem B444005 : Blo 195805 444005 := bbase (se 4 (by rfl) ⟨41625, by rfl⟩ : syracuseStep 444005 = 83251) (by norm_num)
theorem B673429 : Blo 195805 673429 := bbase (se 6 (by rfl) ⟨15783, by rfl⟩ : syracuseStep 673429 = 31567) (by norm_num)
theorem B378533 : Blo 195805 378533 := bbase (se 4 (by rfl) ⟨35487, by rfl⟩ : syracuseStep 378533 = 70975) (by norm_num)
theorem B444077 : Blo 195805 444077 := bbase (se 3 (by rfl) ⟨83264, by rfl⟩ : syracuseStep 444077 = 166529) (by norm_num)
theorem B444149 : Blo 195805 444149 := bbase (se 5 (by rfl) ⟨20819, by rfl⟩ : syracuseStep 444149 = 41639) (by norm_num)
theorem B673541 : Blo 195805 673541 := bbase (se 4 (by rfl) ⟨63144, by rfl⟩ : syracuseStep 673541 = 126289) (by norm_num)
theorem B444221 : Blo 195805 444221 := bbase (se 3 (by rfl) ⟨83291, by rfl⟩ : syracuseStep 444221 = 166583) (by norm_num)
theorem B378685 : Blo 195805 378685 := bbase (se 3 (by rfl) ⟨71003, by rfl⟩ : syracuseStep 378685 = 142007) (by norm_num)
theorem B804725 : Blo 195805 804725 := bbase (se 5 (by rfl) ⟨37721, by rfl⟩ : syracuseStep 804725 = 75443) (by norm_num)
theorem B444293 : Blo 195805 444293 := bbase (se 4 (by rfl) ⟨41652, by rfl⟩ : syracuseStep 444293 = 83305) (by norm_num)
theorem B444365 : Blo 195805 444365 := bbase (se 3 (by rfl) ⟨83318, by rfl⟩ : syracuseStep 444365 = 166637) (by norm_num)
theorem B1132501 : Blo 195805 1132501 := bbase (se 7 (by rfl) ⟨13271, by rfl⟩ : syracuseStep 1132501 = 26543) (by norm_num)
theorem B280597 : Blo 195805 280597 := bbase (se 6 (by rfl) ⟨6576, by rfl⟩ : syracuseStep 280597 = 13153) (by norm_num)
theorem B444437 : Blo 195805 444437 := bbase (se 6 (by rfl) ⟨10416, by rfl⟩ : syracuseStep 444437 = 20833) (by norm_num)
theorem B444509 : Blo 195805 444509 := bbase (se 3 (by rfl) ⟨83345, by rfl⟩ : syracuseStep 444509 = 166691) (by norm_num)
theorem B378989 : Blo 195805 378989 := bbase (se 3 (by rfl) ⟨71060, by rfl⟩ : syracuseStep 378989 = 142121) (by norm_num)
theorem B215173 : Blo 195805 215173 := bbase (se 4 (by rfl) ⟨20172, by rfl⟩ : syracuseStep 215173 = 40345) (by norm_num)
theorem B247961 : Blo 195805 247961 := bbase (se 2 (by rfl) ⟨92985, by rfl⟩ : syracuseStep 247961 = 185971) (by norm_num)
theorem B444581 : Blo 195805 444581 := bbase (se 4 (by rfl) ⟨41679, by rfl⟩ : syracuseStep 444581 = 83359) (by norm_num)
theorem B673973 : Blo 195805 673973 := bbase (se 5 (by rfl) ⟨31592, by rfl⟩ : syracuseStep 673973 = 63185) (by norm_num)
theorem B248017 : Blo 195805 248017 := bbase (se 2 (by rfl) ⟨93006, by rfl⟩ : syracuseStep 248017 = 186013) (by norm_num)
theorem B444653 : Blo 195805 444653 := bbase (se 3 (by rfl) ⟨83372, by rfl⟩ : syracuseStep 444653 = 166745) (by norm_num)
theorem B248113 : Blo 195805 248113 := bbase (se 2 (by rfl) ⟨93042, by rfl⟩ : syracuseStep 248113 = 186085) (by norm_num)
theorem B444725 : Blo 195805 444725 := bbase (se 5 (by rfl) ⟨20846, by rfl⟩ : syracuseStep 444725 = 41693) (by norm_num)
theorem B444797 : Blo 195805 444797 := bbase (se 3 (by rfl) ⟨83399, by rfl⟩ : syracuseStep 444797 = 166799) (by norm_num)
theorem B444869 : Blo 195805 444869 := bbase (se 4 (by rfl) ⟨41706, by rfl⟩ : syracuseStep 444869 = 83413) (by norm_num)
theorem B3230165 : Blo 195805 3230165 := bbase (se 7 (by rfl) ⟨37853, by rfl⟩ : syracuseStep 3230165 = 75707) (by norm_num)
theorem B248285 : Blo 195805 248285 := bbase (se 3 (by rfl) ⟨46553, by rfl⟩ : syracuseStep 248285 = 93107) (by norm_num)
theorem B444941 : Blo 195805 444941 := bbase (se 3 (by rfl) ⟨83426, by rfl⟩ : syracuseStep 444941 = 166853) (by norm_num)
theorem B248341 : Blo 195805 248341 := bbase (se 6 (by rfl) ⟨5820, by rfl⟩ : syracuseStep 248341 = 11641) (by norm_num)
theorem B445013 : Blo 195805 445013 := bbase (se 8 (by rfl) ⟨2607, by rfl⟩ : syracuseStep 445013 = 5215) (by norm_num)
theorem B313949 : Blo 195805 313949 := bbase (se 3 (by rfl) ⟨58865, by rfl⟩ : syracuseStep 313949 = 117731) (by norm_num)
theorem B281189 : Blo 195805 281189 := bbase (se 4 (by rfl) ⟨26361, by rfl⟩ : syracuseStep 281189 = 52723) (by norm_num)
theorem B248437 : Blo 195805 248437 := bbase (se 5 (by rfl) ⟨11645, by rfl⟩ : syracuseStep 248437 = 23291) (by norm_num)
theorem B445085 : Blo 195805 445085 := bbase (se 3 (by rfl) ⟨83453, by rfl⟩ : syracuseStep 445085 = 166907) (by norm_num)
theorem B281269 : Blo 195805 281269 := bbase (se 5 (by rfl) ⟨13184, by rfl⟩ : syracuseStep 281269 = 26369) (by norm_num)
theorem B7785173 : Blo 195805 7785173 := bbase (se 7 (by rfl) ⟨91232, by rfl⟩ : syracuseStep 7785173 = 182465) (by norm_num)
theorem B445157 : Blo 195805 445157 := bbase (se 4 (by rfl) ⟨41733, by rfl⟩ : syracuseStep 445157 = 83467) (by norm_num)
theorem B510749 : Blo 195805 510749 := bbase (se 3 (by rfl) ⟨95765, by rfl⟩ : syracuseStep 510749 = 191531) (by norm_num)
theorem B248609 : Blo 195805 248609 := bbase (se 2 (by rfl) ⟨93228, by rfl⟩ : syracuseStep 248609 = 186457) (by norm_num)
theorem B281389 : Blo 195805 281389 := bbase (se 3 (by rfl) ⟨52760, by rfl⟩ : syracuseStep 281389 = 105521) (by norm_num)
theorem B445229 : Blo 195805 445229 := bbase (se 3 (by rfl) ⟨83480, by rfl⟩ : syracuseStep 445229 = 166961) (by norm_num)
theorem B1002293 : Blo 195805 1002293 := bbase (se 5 (by rfl) ⟨46982, by rfl⟩ : syracuseStep 1002293 = 93965) (by norm_num)
theorem B248665 : Blo 195805 248665 := bbase (se 2 (by rfl) ⟨93249, by rfl⟩ : syracuseStep 248665 = 186499) (by norm_num)
theorem B445301 : Blo 195805 445301 := bbase (se 5 (by rfl) ⟨20873, by rfl⟩ : syracuseStep 445301 = 41747) (by norm_num)
theorem B281485 : Blo 195805 281485 := bbase (se 3 (by rfl) ⟨52778, by rfl⟩ : syracuseStep 281485 = 105557) (by norm_num)
theorem B248761 : Blo 195805 248761 := bbase (se 2 (by rfl) ⟨93285, by rfl⟩ : syracuseStep 248761 = 186571) (by norm_num)
theorem B445373 : Blo 195805 445373 := bbase (se 3 (by rfl) ⟨83507, by rfl⟩ : syracuseStep 445373 = 167015) (by norm_num)
theorem B838613 : Blo 195805 838613 := bbase (se 7 (by rfl) ⟨9827, by rfl⟩ : syracuseStep 838613 = 19655) (by norm_num)
theorem B445445 : Blo 195805 445445 := bbase (se 4 (by rfl) ⟨41760, by rfl⟩ : syracuseStep 445445 = 83521) (by norm_num)
theorem B445517 : Blo 195805 445517 := bbase (se 3 (by rfl) ⟨83534, by rfl⟩ : syracuseStep 445517 = 167069) (by norm_num)
theorem B248933 : Blo 195805 248933 := bbase (se 4 (by rfl) ⟨23337, by rfl⟩ : syracuseStep 248933 = 46675) (by norm_num)
theorem B445589 : Blo 195805 445589 := bbase (se 6 (by rfl) ⟨10443, by rfl⟩ : syracuseStep 445589 = 20887) (by norm_num)
theorem B248989 : Blo 195805 248989 := bbase (se 3 (by rfl) ⟨46685, by rfl⟩ : syracuseStep 248989 = 93371) (by norm_num)
theorem B445661 : Blo 195805 445661 := bbase (se 3 (by rfl) ⟨83561, by rfl⟩ : syracuseStep 445661 = 167123) (by norm_num)
theorem B314621 : Blo 195805 314621 := bbase (se 3 (by rfl) ⟨58991, by rfl⟩ : syracuseStep 314621 = 117983) (by norm_num)
theorem B249085 : Blo 195805 249085 := bbase (se 3 (by rfl) ⟨46703, by rfl⟩ : syracuseStep 249085 = 93407) (by norm_num)
theorem B478469 : Blo 195805 478469 := bbase (se 4 (by rfl) ⟨44856, by rfl⟩ : syracuseStep 478469 = 89713) (by norm_num)
theorem B806149 : Blo 195805 806149 := bbase (se 4 (by rfl) ⟨75576, by rfl⟩ : syracuseStep 806149 = 151153) (by norm_num)
theorem B380189 : Blo 195805 380189 := bbase (se 3 (by rfl) ⟨71285, by rfl⟩ : syracuseStep 380189 = 142571) (by norm_num)
theorem B445733 : Blo 195805 445733 := bbase (se 4 (by rfl) ⟨41787, by rfl⟩ : syracuseStep 445733 = 83575) (by norm_num)
theorem B445805 : Blo 195805 445805 := bbase (se 3 (by rfl) ⟨83588, by rfl⟩ : syracuseStep 445805 = 167177) (by norm_num)
theorem B281981 : Blo 195805 281981 := bbase (se 3 (by rfl) ⟨52871, by rfl⟩ : syracuseStep 281981 = 105743) (by norm_num)
theorem B249257 : Blo 195805 249257 := bbase (se 2 (by rfl) ⟨93471, by rfl⟩ : syracuseStep 249257 = 186943) (by norm_num)
theorem B445877 : Blo 195805 445877 := bbase (se 5 (by rfl) ⟨20900, by rfl⟩ : syracuseStep 445877 = 41801) (by norm_num)
theorem B249313 : Blo 195805 249313 := bbase (se 2 (by rfl) ⟨93492, by rfl⟩ : syracuseStep 249313 = 186985) (by norm_num)
theorem B445949 : Blo 195805 445949 := bbase (se 3 (by rfl) ⟨83615, by rfl⟩ : syracuseStep 445949 = 167231) (by norm_num)
theorem B511517 : Blo 195805 511517 := bbase (se 3 (by rfl) ⟨95909, by rfl⟩ : syracuseStep 511517 = 191819) (by norm_num)
theorem B249409 : Blo 195805 249409 := bbase (se 2 (by rfl) ⟨93528, by rfl⟩ : syracuseStep 249409 = 187057) (by norm_num)
theorem B446021 : Blo 195805 446021 := bbase (se 4 (by rfl) ⟨41814, by rfl⟩ : syracuseStep 446021 = 83629) (by norm_num)
theorem B478813 : Blo 195805 478813 := bbase (se 3 (by rfl) ⟨89777, by rfl⟩ : syracuseStep 478813 = 179555) (by norm_num)
theorem B446093 : Blo 195805 446093 := bbase (se 3 (by rfl) ⟨83642, by rfl⟩ : syracuseStep 446093 = 167285) (by norm_num)
theorem B478909 : Blo 195805 478909 := bbase (se 3 (by rfl) ⟨89795, by rfl⟩ : syracuseStep 478909 = 179591) (by norm_num)
theorem B446165 : Blo 195805 446165 := bbase (se 7 (by rfl) ⟨5228, by rfl⟩ : syracuseStep 446165 = 10457) (by norm_num)
theorem B249581 : Blo 195805 249581 := bbase (se 3 (by rfl) ⟨46796, by rfl⟩ : syracuseStep 249581 = 93593) (by norm_num)
theorem B315133 : Blo 195805 315133 := bbase (se 3 (by rfl) ⟨59087, by rfl⟩ : syracuseStep 315133 = 118175) (by norm_num)
theorem B446237 : Blo 195805 446237 := bbase (se 3 (by rfl) ⟨83669, by rfl⟩ : syracuseStep 446237 = 167339) (by norm_num)
theorem B249637 : Blo 195805 249637 := bbase (se 4 (by rfl) ⟨23403, by rfl⟩ : syracuseStep 249637 = 46807) (by norm_num)
theorem B2117461 : Blo 195805 2117461 := bbase (se 9 (by rfl) ⟨6203, by rfl⟩ : syracuseStep 2117461 = 12407) (by norm_num)
theorem B446309 : Blo 195805 446309 := bbase (se 4 (by rfl) ⟨41841, by rfl⟩ : syracuseStep 446309 = 83683) (by norm_num)
theorem B249733 : Blo 195805 249733 := bbase (se 4 (by rfl) ⟨23412, by rfl⟩ : syracuseStep 249733 = 46825) (by norm_num)
theorem B1134485 : Blo 195805 1134485 := bbase (se 6 (by rfl) ⟨26589, by rfl⟩ : syracuseStep 1134485 = 53179) (by norm_num)
theorem B282533 : Blo 195805 282533 := bbase (se 4 (by rfl) ⟨26487, by rfl⟩ : syracuseStep 282533 = 52975) (by norm_num)
theorem B446381 : Blo 195805 446381 := bbase (se 3 (by rfl) ⟨83696, by rfl⟩ : syracuseStep 446381 = 167393) (by norm_num)
theorem B708533 : Blo 195805 708533 := bbase (se 5 (by rfl) ⟨33212, by rfl⟩ : syracuseStep 708533 = 66425) (by norm_num)
theorem B446453 : Blo 195805 446453 := bbase (se 5 (by rfl) ⟨20927, by rfl⟩ : syracuseStep 446453 = 41855) (by norm_num)
theorem B249905 : Blo 195805 249905 := bbase (se 2 (by rfl) ⟨93714, by rfl⟩ : syracuseStep 249905 = 187429) (by norm_num)
theorem B446525 : Blo 195805 446525 := bbase (se 3 (by rfl) ⟨83723, by rfl⟩ : syracuseStep 446525 = 167447) (by norm_num)
theorem B1003589 : Blo 195805 1003589 := bbase (se 4 (by rfl) ⟨94086, by rfl⟩ : syracuseStep 1003589 = 188173) (by norm_num)
theorem B1527893 : Blo 195805 1527893 := bbase (se 8 (by rfl) ⟨8952, by rfl⟩ : syracuseStep 1527893 = 17905) (by norm_num)
theorem B479333 : Blo 195805 479333 := bbase (se 4 (by rfl) ⟨44937, by rfl⟩ : syracuseStep 479333 = 89875) (by norm_num)
theorem B249961 : Blo 195805 249961 := bbase (se 2 (by rfl) ⟨93735, by rfl⟩ : syracuseStep 249961 = 187471) (by norm_num)
theorem B446597 : Blo 195805 446597 := bbase (se 4 (by rfl) ⟨41868, by rfl⟩ : syracuseStep 446597 = 83737) (by norm_num)
theorem B512173 : Blo 195805 512173 := bbase (se 3 (by rfl) ⟨96032, by rfl⟩ : syracuseStep 512173 = 192065) (by norm_num)
theorem B315589 : Blo 195805 315589 := bbase (se 4 (by rfl) ⟨29586, by rfl⟩ : syracuseStep 315589 = 59173) (by norm_num)
theorem B479429 : Blo 195805 479429 := bbase (se 4 (by rfl) ⟨44946, by rfl⟩ : syracuseStep 479429 = 89893) (by norm_num)
theorem B250057 : Blo 195805 250057 := bbase (se 2 (by rfl) ⟨93771, by rfl⟩ : syracuseStep 250057 = 187543) (by norm_num)
theorem B446669 : Blo 195805 446669 := bbase (se 3 (by rfl) ⟨83750, by rfl⟩ : syracuseStep 446669 = 167501) (by norm_num)
theorem B708821 : Blo 195805 708821 := bbase (se 7 (by rfl) ⟨8306, by rfl⟩ : syracuseStep 708821 = 16613) (by norm_num)
theorem B446741 : Blo 195805 446741 := bbase (se 6 (by rfl) ⟨10470, by rfl⟩ : syracuseStep 446741 = 20941) (by norm_num)
theorem B446813 : Blo 195805 446813 := bbase (se 3 (by rfl) ⟨83777, by rfl⟩ : syracuseStep 446813 = 167555) (by norm_num)
theorem B708965 : Blo 195805 708965 := bbase (se 4 (by rfl) ⟨66465, by rfl⟩ : syracuseStep 708965 = 132931) (by norm_num)
theorem B250229 : Blo 195805 250229 := bbase (se 5 (by rfl) ⟨11729, by rfl⟩ : syracuseStep 250229 = 23459) (by norm_num)
theorem B446885 : Blo 195805 446885 := bbase (se 4 (by rfl) ⟨41895, by rfl⟩ : syracuseStep 446885 = 83791) (by norm_num)
theorem B250285 : Blo 195805 250285 := bbase (se 3 (by rfl) ⟨46928, by rfl⟩ : syracuseStep 250285 = 93857) (by norm_num)
theorem B446957 : Blo 195805 446957 := bbase (se 3 (by rfl) ⟨83804, by rfl⟩ : syracuseStep 446957 = 167609) (by norm_num)
theorem B807413 : Blo 195805 807413 := bbase (se 5 (by rfl) ⟨37847, by rfl⟩ : syracuseStep 807413 = 75695) (by norm_num)
theorem B250381 : Blo 195805 250381 := bbase (se 3 (by rfl) ⟨46946, by rfl⟩ : syracuseStep 250381 = 93893) (by norm_num)
theorem B1921589 : Blo 195805 1921589 := bbase (se 5 (by rfl) ⟨90074, by rfl⟩ : syracuseStep 1921589 = 180149) (by norm_num)
theorem B447029 : Blo 195805 447029 := bbase (se 5 (by rfl) ⟨20954, by rfl⟩ : syracuseStep 447029 = 41909) (by norm_num)
theorem B447101 : Blo 195805 447101 := bbase (se 3 (by rfl) ⟨83831, by rfl⟩ : syracuseStep 447101 = 167663) (by norm_num)
theorem B283285 : Blo 195805 283285 := bbase (se 6 (by rfl) ⟨6639, by rfl⟩ : syracuseStep 283285 = 13279) (by norm_num)
theorem B250553 : Blo 195805 250553 := bbase (se 2 (by rfl) ⟨93957, by rfl⟩ : syracuseStep 250553 = 187915) (by norm_num)
theorem B447173 : Blo 195805 447173 := bbase (se 4 (by rfl) ⟨41922, by rfl⟩ : syracuseStep 447173 = 83845) (by norm_num)
theorem B250609 : Blo 195805 250609 := bbase (se 2 (by rfl) ⟨93978, by rfl⟩ : syracuseStep 250609 = 187957) (by norm_num)
theorem B447245 : Blo 195805 447245 := bbase (se 3 (by rfl) ⟨83858, by rfl⟩ : syracuseStep 447245 = 167717) (by norm_num)
theorem B3363605 : Blo 195805 3363605 := bbase (se 6 (by rfl) ⟨78834, by rfl⟩ : syracuseStep 3363605 = 157669) (by norm_num)
theorem B250705 : Blo 195805 250705 := bbase (se 2 (by rfl) ⟨94014, by rfl⟩ : syracuseStep 250705 = 188029) (by norm_num)
theorem B447317 : Blo 195805 447317 := bbase (se 9 (by rfl) ⟨1310, by rfl⟩ : syracuseStep 447317 = 2621) (by norm_num)
theorem B316261 : Blo 195805 316261 := bbase (se 4 (by rfl) ⟨29649, by rfl⟩ : syracuseStep 316261 = 59299) (by norm_num)
theorem B447389 : Blo 195805 447389 := bbase (se 3 (by rfl) ⟨83885, by rfl⟩ : syracuseStep 447389 = 167771) (by norm_num)
theorem B906149 : Blo 195805 906149 := bbase (se 4 (by rfl) ⟨84951, by rfl⟩ : syracuseStep 906149 = 169903) (by norm_num)
theorem B447461 : Blo 195805 447461 := bbase (se 4 (by rfl) ⟨41949, by rfl⟩ : syracuseStep 447461 = 83899) (by norm_num)
theorem B250877 : Blo 195805 250877 := bbase (se 3 (by rfl) ⟨47039, by rfl⟩ : syracuseStep 250877 = 94079) (by norm_num)
theorem B447533 : Blo 195805 447533 := bbase (se 3 (by rfl) ⟨83912, by rfl⟩ : syracuseStep 447533 = 167825) (by norm_num)
theorem B250933 : Blo 195805 250933 := bbase (se 5 (by rfl) ⟨11762, by rfl⟩ : syracuseStep 250933 = 23525) (by norm_num)
theorem B447605 : Blo 195805 447605 := bbase (se 5 (by rfl) ⟨20981, by rfl⟩ : syracuseStep 447605 = 41963) (by norm_num)
theorem B251029 : Blo 195805 251029 := bbase (se 6 (by rfl) ⟨5883, by rfl⟩ : syracuseStep 251029 = 11767) (by norm_num)
theorem B447677 : Blo 195805 447677 := bbase (se 3 (by rfl) ⟨83939, by rfl⟩ : syracuseStep 447677 = 167879) (by norm_num)
theorem B447749 : Blo 195805 447749 := bbase (se 4 (by rfl) ⟨41976, by rfl⟩ : syracuseStep 447749 = 83953) (by norm_num)
theorem B316685 : Blo 195805 316685 := bbase (se 3 (by rfl) ⟨59378, by rfl⟩ : syracuseStep 316685 = 118757) (by norm_num)
theorem B251201 : Blo 195805 251201 := bbase (se 2 (by rfl) ⟨94200, by rfl⟩ : syracuseStep 251201 = 188401) (by norm_num)
theorem B382277 : Blo 195805 382277 := bbase (se 4 (by rfl) ⟨35838, by rfl⟩ : syracuseStep 382277 = 71677) (by norm_num)
theorem B447821 : Blo 195805 447821 := bbase (se 3 (by rfl) ⟨83966, by rfl⟩ : syracuseStep 447821 = 167933) (by norm_num)
theorem B1004885 : Blo 195805 1004885 := bbase (se 17 (by rfl) ⟨11, by rfl⟩ : syracuseStep 1004885 = 23) (by norm_num)
theorem B251257 : Blo 195805 251257 := bbase (se 2 (by rfl) ⟨94221, by rfl⟩ : syracuseStep 251257 = 188443) (by norm_num)
theorem B1267093 : Blo 195805 1267093 := bbase (se 6 (by rfl) ⟨29697, by rfl⟩ : syracuseStep 1267093 = 59395) (by norm_num)
theorem B447893 : Blo 195805 447893 := bbase (se 6 (by rfl) ⟨10497, by rfl⟩ : syracuseStep 447893 = 20995) (by norm_num)
theorem B284077 : Blo 195805 284077 := bbase (se 3 (by rfl) ⟨53264, by rfl⟩ : syracuseStep 284077 = 106529) (by norm_num)
theorem B251353 : Blo 195805 251353 := bbase (se 2 (by rfl) ⟨94257, by rfl⟩ : syracuseStep 251353 = 188515) (by norm_num)
theorem B447965 : Blo 195805 447965 := bbase (se 3 (by rfl) ⟨83993, by rfl⟩ : syracuseStep 447965 = 167987) (by norm_num)
theorem B448037 : Blo 195805 448037 := bbase (se 4 (by rfl) ⟨42003, by rfl⟩ : syracuseStep 448037 = 84007) (by norm_num)
theorem B316973 : Blo 195805 316973 := bbase (se 3 (by rfl) ⟨59432, by rfl⟩ : syracuseStep 316973 = 118865) (by norm_num)
theorem B448109 : Blo 195805 448109 := bbase (se 3 (by rfl) ⟨84020, by rfl⟩ : syracuseStep 448109 = 168041) (by norm_num)
theorem B251525 : Blo 195805 251525 := bbase (se 4 (by rfl) ⟨23580, by rfl⟩ : syracuseStep 251525 = 47161) (by norm_num)
theorem B448181 : Blo 195805 448181 := bbase (se 5 (by rfl) ⟨21008, by rfl⟩ : syracuseStep 448181 = 42017) (by norm_num)
theorem B251581 : Blo 195805 251581 := bbase (se 3 (by rfl) ⟨47171, by rfl⟩ : syracuseStep 251581 = 94343) (by norm_num)
theorem B448253 : Blo 195805 448253 := bbase (se 3 (by rfl) ⟨84047, by rfl⟩ : syracuseStep 448253 = 168095) (by norm_num)
theorem B284413 : Blo 195805 284413 := bbase (se 3 (by rfl) ⟨53327, by rfl⟩ : syracuseStep 284413 = 106655) (by norm_num)
theorem B251677 : Blo 195805 251677 := bbase (se 3 (by rfl) ⟨47189, by rfl⟩ : syracuseStep 251677 = 94379) (by norm_num)
theorem B448325 : Blo 195805 448325 := bbase (se 4 (by rfl) ⟨42030, by rfl⟩ : syracuseStep 448325 = 84061) (by norm_num)
theorem B448397 : Blo 195805 448397 := bbase (se 3 (by rfl) ⟨84074, by rfl⟩ : syracuseStep 448397 = 168149) (by norm_num)
theorem B251849 : Blo 195805 251849 := bbase (se 2 (by rfl) ⟨94443, by rfl⟩ : syracuseStep 251849 = 188887) (by norm_num)
theorem B448469 : Blo 195805 448469 := bbase (se 7 (by rfl) ⟨5255, by rfl⟩ : syracuseStep 448469 = 10511) (by norm_num)
theorem B251905 : Blo 195805 251905 := bbase (se 2 (by rfl) ⟨94464, by rfl⟩ : syracuseStep 251905 = 188929) (by norm_num)
theorem B448541 : Blo 195805 448541 := bbase (se 3 (by rfl) ⟨84101, by rfl⟩ : syracuseStep 448541 = 168203) (by norm_num)
theorem B1136693 : Blo 195805 1136693 := bbase (se 5 (by rfl) ⟨53282, by rfl⟩ : syracuseStep 1136693 = 106565) (by norm_num)
theorem B252001 : Blo 195805 252001 := bbase (se 2 (by rfl) ⟨94500, by rfl⟩ : syracuseStep 252001 = 189001) (by norm_num)
theorem B448613 : Blo 195805 448613 := bbase (se 4 (by rfl) ⟨42057, by rfl⟩ : syracuseStep 448613 = 84115) (by norm_num)
theorem B448685 : Blo 195805 448685 := bbase (se 3 (by rfl) ⟨84128, by rfl⟩ : syracuseStep 448685 = 168257) (by norm_num)
theorem B448757 : Blo 195805 448757 := bbase (se 5 (by rfl) ⟨21035, by rfl⟩ : syracuseStep 448757 = 42071) (by norm_num)
theorem B252173 : Blo 195805 252173 := bbase (se 3 (by rfl) ⟨47282, by rfl⟩ : syracuseStep 252173 = 94565) (by norm_num)
theorem B743701 : Blo 195805 743701 := bbase (se 6 (by rfl) ⟨17430, by rfl⟩ : syracuseStep 743701 = 34861) (by norm_num)
theorem B1497365 : Blo 195805 1497365 := bbase (se 6 (by rfl) ⟨35094, by rfl⟩ : syracuseStep 1497365 = 70189) (by norm_num)
theorem B481589 : Blo 195805 481589 := bbase (se 5 (by rfl) ⟨22574, by rfl⟩ : syracuseStep 481589 = 45149) (by norm_num)
theorem B448829 : Blo 195805 448829 := bbase (se 3 (by rfl) ⟨84155, by rfl⟩ : syracuseStep 448829 = 168311) (by norm_num)
theorem B252229 : Blo 195805 252229 := bbase (se 4 (by rfl) ⟨23646, by rfl⟩ : syracuseStep 252229 = 47293) (by norm_num)
theorem B317773 : Blo 195805 317773 := bbase (se 3 (by rfl) ⟨59582, by rfl⟩ : syracuseStep 317773 = 119165) (by norm_num)
theorem B448901 : Blo 195805 448901 := bbase (se 4 (by rfl) ⟨42084, by rfl⟩ : syracuseStep 448901 = 84169) (by norm_num)
theorem B252325 : Blo 195805 252325 := bbase (se 4 (by rfl) ⟨23655, by rfl⟩ : syracuseStep 252325 = 47311) (by norm_num)
theorem B448973 : Blo 195805 448973 := bbase (se 3 (by rfl) ⟨84182, by rfl⟩ : syracuseStep 448973 = 168365) (by norm_num)
theorem B449045 : Blo 195805 449045 := bbase (se 6 (by rfl) ⟨10524, by rfl⟩ : syracuseStep 449045 = 21049) (by norm_num)
theorem B744005 : Blo 195805 744005 := bbase (se 4 (by rfl) ⟨69750, by rfl⟩ : syracuseStep 744005 = 139501) (by norm_num)
theorem B252497 : Blo 195805 252497 := bbase (se 2 (by rfl) ⟨94686, by rfl⟩ : syracuseStep 252497 = 189373) (by norm_num)
theorem B449117 : Blo 195805 449117 := bbase (se 3 (by rfl) ⟨84209, by rfl⟩ : syracuseStep 449117 = 168419) (by norm_num)
theorem B1006181 : Blo 195805 1006181 := bbase (se 4 (by rfl) ⟨94329, by rfl⟩ : syracuseStep 1006181 = 188659) (by norm_num)
theorem B252553 : Blo 195805 252553 := bbase (se 2 (by rfl) ⟨94707, by rfl⟩ : syracuseStep 252553 = 189415) (by norm_num)
theorem B940709 : Blo 195805 940709 := bbase (se 4 (by rfl) ⟨88191, by rfl⟩ : syracuseStep 940709 = 176383) (by norm_num)
theorem B449189 : Blo 195805 449189 := bbase (se 4 (by rfl) ⟨42111, by rfl⟩ : syracuseStep 449189 = 84223) (by norm_num)
theorem B252649 : Blo 195805 252649 := bbase (se 2 (by rfl) ⟨94743, by rfl⟩ : syracuseStep 252649 = 189487) (by norm_num)
theorem B449261 : Blo 195805 449261 := bbase (se 3 (by rfl) ⟨84236, by rfl⟩ : syracuseStep 449261 = 168473) (by norm_num)
theorem B449333 : Blo 195805 449333 := bbase (se 5 (by rfl) ⟨21062, by rfl⟩ : syracuseStep 449333 = 42125) (by norm_num)
theorem B318325 : Blo 195805 318325 := bbase (se 5 (by rfl) ⟨14921, by rfl⟩ : syracuseStep 318325 = 29843) (by norm_num)
theorem B449405 : Blo 195805 449405 := bbase (se 3 (by rfl) ⟨84263, by rfl⟩ : syracuseStep 449405 = 168527) (by norm_num)
theorem B252821 : Blo 195805 252821 := bbase (se 6 (by rfl) ⟨5925, by rfl⟩ : syracuseStep 252821 = 11851) (by norm_num)
theorem B449477 : Blo 195805 449477 := bbase (se 4 (by rfl) ⟨42138, by rfl⟩ : syracuseStep 449477 = 84277) (by norm_num)
theorem B252877 : Blo 195805 252877 := bbase (se 3 (by rfl) ⟨47414, by rfl⟩ : syracuseStep 252877 = 94829) (by norm_num)
theorem B449549 : Blo 195805 449549 := bbase (se 3 (by rfl) ⟨84290, by rfl⟩ : syracuseStep 449549 = 168581) (by norm_num)
theorem B318581 : Blo 195805 318581 := bbase (se 5 (by rfl) ⟨14933, by rfl⟩ : syracuseStep 318581 = 29867) (by norm_num)
theorem B842885 : Blo 195805 842885 := bbase (se 4 (by rfl) ⟨79020, by rfl⟩ : syracuseStep 842885 = 158041) (by norm_num)
theorem B220297 : Blo 195805 220297 := bbase (se 2 (by rfl) ⟨82611, by rfl⟩ : syracuseStep 220297 = 165223) (by norm_num)
theorem B253085 : Blo 195805 253085 := bbase (se 3 (by rfl) ⟨47453, by rfl⟩ : syracuseStep 253085 = 94907) (by norm_num)
theorem B220333 : Blo 195805 220333 := bbase (se 3 (by rfl) ⟨41312, by rfl⟩ : syracuseStep 220333 = 82625) (by norm_num)
theorem B220369 : Blo 195805 220369 := bbase (se 2 (by rfl) ⟨82638, by rfl⟩ : syracuseStep 220369 = 165277) (by norm_num)
theorem B220405 : Blo 195805 220405 := bbase (se 5 (by rfl) ⟨10331, by rfl⟩ : syracuseStep 220405 = 20663) (by norm_num)
theorem B220441 : Blo 195805 220441 := bbase (se 2 (by rfl) ⟨82665, by rfl⟩ : syracuseStep 220441 = 165331) (by norm_num)
theorem B220477 : Blo 195805 220477 := bbase (se 3 (by rfl) ⟨41339, by rfl⟩ : syracuseStep 220477 = 82679) (by norm_num)
theorem B220513 : Blo 195805 220513 := bbase (se 2 (by rfl) ⟨82692, by rfl⟩ : syracuseStep 220513 = 165385) (by norm_num)
theorem B220549 : Blo 195805 220549 := bbase (se 4 (by rfl) ⟨20676, by rfl⟩ : syracuseStep 220549 = 41353) (by norm_num)
theorem B220585 : Blo 195805 220585 := bbase (se 2 (by rfl) ⟨82719, by rfl⟩ : syracuseStep 220585 = 165439) (by norm_num)
theorem B220621 : Blo 195805 220621 := bbase (se 3 (by rfl) ⟨41366, by rfl⟩ : syracuseStep 220621 = 82733) (by norm_num)
theorem B712165 : Blo 195805 712165 := bbase (se 4 (by rfl) ⟨66765, by rfl⟩ : syracuseStep 712165 = 133531) (by norm_num)
theorem B220657 : Blo 195805 220657 := bbase (se 2 (by rfl) ⟨82746, by rfl⟩ : syracuseStep 220657 = 165493) (by norm_num)
theorem B220693 : Blo 195805 220693 := bbase (se 6 (by rfl) ⟨5172, by rfl⟩ : syracuseStep 220693 = 10345) (by norm_num)
theorem B220729 : Blo 195805 220729 := bbase (se 2 (by rfl) ⟨82773, by rfl⟩ : syracuseStep 220729 = 165547) (by norm_num)
theorem B220765 : Blo 195805 220765 := bbase (se 3 (by rfl) ⟨41393, by rfl⟩ : syracuseStep 220765 = 82787) (by norm_num)
theorem B220801 : Blo 195805 220801 := bbase (se 2 (by rfl) ⟨82800, by rfl⟩ : syracuseStep 220801 = 165601) (by norm_num)
theorem B220837 : Blo 195805 220837 := bbase (se 4 (by rfl) ⟨20703, by rfl⟩ : syracuseStep 220837 = 41407) (by norm_num)
theorem B220873 : Blo 195805 220873 := bbase (se 2 (by rfl) ⟨82827, by rfl⟩ : syracuseStep 220873 = 165655) (by norm_num)
theorem B220909 : Blo 195805 220909 := bbase (se 3 (by rfl) ⟨41420, by rfl⟩ : syracuseStep 220909 = 82841) (by norm_num)
theorem B220945 : Blo 195805 220945 := bbase (se 2 (by rfl) ⟨82854, by rfl⟩ : syracuseStep 220945 = 165709) (by norm_num)
theorem B220981 : Blo 195805 220981 := bbase (se 5 (by rfl) ⟨10358, by rfl⟩ : syracuseStep 220981 = 20717) (by norm_num)
theorem B319285 : Blo 195805 319285 := bbase (se 5 (by rfl) ⟨14966, by rfl⟩ : syracuseStep 319285 = 29933) (by norm_num)
theorem B221017 : Blo 195805 221017 := bbase (se 2 (by rfl) ⟨82881, by rfl⟩ : syracuseStep 221017 = 165763) (by norm_num)
theorem B1007477 : Blo 195805 1007477 := bbase (se 5 (by rfl) ⟨47225, by rfl⟩ : syracuseStep 1007477 = 94451) (by norm_num)
theorem B221053 : Blo 195805 221053 := bbase (se 3 (by rfl) ⟨41447, by rfl⟩ : syracuseStep 221053 = 82895) (by norm_num)
theorem B221089 : Blo 195805 221089 := bbase (se 2 (by rfl) ⟨82908, by rfl⟩ : syracuseStep 221089 = 165817) (by norm_num)
theorem B712613 : Blo 195805 712613 := bbase (se 4 (by rfl) ⟨66807, by rfl⟩ : syracuseStep 712613 = 133615) (by norm_num)
theorem B221125 : Blo 195805 221125 := bbase (se 4 (by rfl) ⟨20730, by rfl⟩ : syracuseStep 221125 = 41461) (by norm_num)
theorem B221161 : Blo 195805 221161 := bbase (se 2 (by rfl) ⟨82935, by rfl⟩ : syracuseStep 221161 = 165871) (by norm_num)
theorem B221197 : Blo 195805 221197 := bbase (se 3 (by rfl) ⟨41474, by rfl⟩ : syracuseStep 221197 = 82949) (by norm_num)
theorem B221233 : Blo 195805 221233 := bbase (se 2 (by rfl) ⟨82962, by rfl⟩ : syracuseStep 221233 = 165925) (by norm_num)
theorem B221269 : Blo 195805 221269 := bbase (se 8 (by rfl) ⟨1296, by rfl⟩ : syracuseStep 221269 = 2593) (by norm_num)
theorem B221305 : Blo 195805 221305 := bbase (se 2 (by rfl) ⟨82989, by rfl⟩ : syracuseStep 221305 = 165979) (by norm_num)
theorem B221341 : Blo 195805 221341 := bbase (se 3 (by rfl) ⟨41501, by rfl⟩ : syracuseStep 221341 = 83003) (by norm_num)
theorem B221377 : Blo 195805 221377 := bbase (se 2 (by rfl) ⟨83016, by rfl⟩ : syracuseStep 221377 = 166033) (by norm_num)
theorem B319709 : Blo 195805 319709 := bbase (se 3 (by rfl) ⟨59945, by rfl⟩ : syracuseStep 319709 = 119891) (by norm_num)
theorem B221413 : Blo 195805 221413 := bbase (se 4 (by rfl) ⟨20757, by rfl⟩ : syracuseStep 221413 = 41515) (by norm_num)
theorem B450805 : Blo 195805 450805 := bbase (se 5 (by rfl) ⟨21131, by rfl⟩ : syracuseStep 450805 = 42263) (by norm_num)
theorem B221449 : Blo 195805 221449 := bbase (se 2 (by rfl) ⟨83043, by rfl⟩ : syracuseStep 221449 = 166087) (by norm_num)
theorem B221485 : Blo 195805 221485 := bbase (se 3 (by rfl) ⟨41528, by rfl⟩ : syracuseStep 221485 = 83057) (by norm_num)
theorem B221521 : Blo 195805 221521 := bbase (se 2 (by rfl) ⟨83070, by rfl⟩ : syracuseStep 221521 = 166141) (by norm_num)
theorem B221557 : Blo 195805 221557 := bbase (se 5 (by rfl) ⟨10385, by rfl⟩ : syracuseStep 221557 = 20771) (by norm_num)
theorem B221593 : Blo 195805 221593 := bbase (se 2 (by rfl) ⟨83097, by rfl⟩ : syracuseStep 221593 = 166195) (by norm_num)
theorem B418213 : Blo 195805 418213 := bbase (se 4 (by rfl) ⟨39207, by rfl⟩ : syracuseStep 418213 = 78415) (by norm_num)
theorem B221629 : Blo 195805 221629 := bbase (se 3 (by rfl) ⟨41555, by rfl⟩ : syracuseStep 221629 = 83111) (by norm_num)
theorem B221665 : Blo 195805 221665 := bbase (se 2 (by rfl) ⟨83124, by rfl⟩ : syracuseStep 221665 = 166249) (by norm_num)
theorem B319997 : Blo 195805 319997 := bbase (se 3 (by rfl) ⟨59999, by rfl⟩ : syracuseStep 319997 = 119999) (by norm_num)
theorem B221701 : Blo 195805 221701 := bbase (se 4 (by rfl) ⟨20784, by rfl⟩ : syracuseStep 221701 = 41569) (by norm_num)
theorem B254497 : Blo 195805 254497 := bbase (se 2 (by rfl) ⟨95436, by rfl⟩ : syracuseStep 254497 = 190873) (by norm_num)
theorem B221737 : Blo 195805 221737 := bbase (se 2 (by rfl) ⟨83151, by rfl⟩ : syracuseStep 221737 = 166303) (by norm_num)
theorem B221773 : Blo 195805 221773 := bbase (se 3 (by rfl) ⟨41582, by rfl⟩ : syracuseStep 221773 = 83165) (by norm_num)
theorem B221809 : Blo 195805 221809 := bbase (se 2 (by rfl) ⟨83178, by rfl⟩ : syracuseStep 221809 = 166357) (by norm_num)
theorem B746117 : Blo 195805 746117 := bbase (se 4 (by rfl) ⟨69948, by rfl⟩ : syracuseStep 746117 = 139897) (by norm_num)
theorem B221845 : Blo 195805 221845 := bbase (se 6 (by rfl) ⟨5199, by rfl⟩ : syracuseStep 221845 = 10399) (by norm_num)
theorem B221869 : Blo 195805 221869 := bbase (se 3 (by rfl) ⟨41600, by rfl⟩ : syracuseStep 221869 = 83201) (by norm_num)
theorem B221881 : Blo 195805 221881 := bbase (se 2 (by rfl) ⟨83205, by rfl⟩ : syracuseStep 221881 = 166411) (by norm_num)
theorem B221917 : Blo 195805 221917 := bbase (se 3 (by rfl) ⟨41609, by rfl⟩ : syracuseStep 221917 = 83219) (by norm_num)
theorem B221953 : Blo 195805 221953 := bbase (se 2 (by rfl) ⟨83232, by rfl⟩ : syracuseStep 221953 = 166465) (by norm_num)
theorem B221989 : Blo 195805 221989 := bbase (se 4 (by rfl) ⟨20811, by rfl⟩ : syracuseStep 221989 = 41623) (by norm_num)
theorem B1696565 : Blo 195805 1696565 := bbase (se 5 (by rfl) ⟨79526, by rfl⟩ : syracuseStep 1696565 = 159053) (by norm_num)
theorem B222025 : Blo 195805 222025 := bbase (se 2 (by rfl) ⟨83259, by rfl⟩ : syracuseStep 222025 = 166519) (by norm_num)
theorem B222061 : Blo 195805 222061 := bbase (se 3 (by rfl) ⟨41636, by rfl⟩ : syracuseStep 222061 = 83273) (by norm_num)
theorem B844661 : Blo 195805 844661 := bbase (se 5 (by rfl) ⟨39593, by rfl⟩ : syracuseStep 844661 = 79187) (by norm_num)
theorem B222097 : Blo 195805 222097 := bbase (se 2 (by rfl) ⟨83286, by rfl⟩ : syracuseStep 222097 = 166573) (by norm_num)
theorem B418709 : Blo 195805 418709 := bbase (se 6 (by rfl) ⟨9813, by rfl⟩ : syracuseStep 418709 = 19627) (by norm_num)
theorem B746405 : Blo 195805 746405 := bbase (se 4 (by rfl) ⟨69975, by rfl⟩ : syracuseStep 746405 = 139951) (by norm_num)
theorem B222133 : Blo 195805 222133 := bbase (se 5 (by rfl) ⟨10412, by rfl⟩ : syracuseStep 222133 = 20825) (by norm_num)
theorem B222169 : Blo 195805 222169 := bbase (se 2 (by rfl) ⟨83313, by rfl⟩ : syracuseStep 222169 = 166627) (by norm_num)
theorem B943093 : Blo 195805 943093 := bbase (se 5 (by rfl) ⟨44207, by rfl⟩ : syracuseStep 943093 = 88415) (by norm_num)
theorem B222205 : Blo 195805 222205 := bbase (se 3 (by rfl) ⟨41663, by rfl⟩ : syracuseStep 222205 = 83327) (by norm_num)
theorem B254989 : Blo 195805 254989 := bbase (se 3 (by rfl) ⟨47810, by rfl⟩ : syracuseStep 254989 = 95621) (by norm_num)
theorem B222241 : Blo 195805 222241 := bbase (se 2 (by rfl) ⟨83340, by rfl⟩ : syracuseStep 222241 = 166681) (by norm_num)
theorem B222277 : Blo 195805 222277 := bbase (se 4 (by rfl) ⟨20838, by rfl⟩ : syracuseStep 222277 = 41677) (by norm_num)
theorem B844901 : Blo 195805 844901 := bbase (se 4 (by rfl) ⟨79209, by rfl⟩ : syracuseStep 844901 = 158419) (by norm_num)
theorem B222313 : Blo 195805 222313 := bbase (se 2 (by rfl) ⟨83367, by rfl⟩ : syracuseStep 222313 = 166735) (by norm_num)
theorem B1008773 : Blo 195805 1008773 := bbase (se 4 (by rfl) ⟨94572, by rfl⟩ : syracuseStep 1008773 = 189145) (by norm_num)
theorem B222349 : Blo 195805 222349 := bbase (se 3 (by rfl) ⟨41690, by rfl⟩ : syracuseStep 222349 = 83381) (by norm_num)
theorem B222385 : Blo 195805 222385 := bbase (se 2 (by rfl) ⟨83394, by rfl⟩ : syracuseStep 222385 = 166789) (by norm_num)
theorem B222421 : Blo 195805 222421 := bbase (se 7 (by rfl) ⟨2606, by rfl⟩ : syracuseStep 222421 = 5213) (by norm_num)
theorem B681205 : Blo 195805 681205 := bbase (se 5 (by rfl) ⟨31931, by rfl⟩ : syracuseStep 681205 = 63863) (by norm_num)
theorem B222457 : Blo 195805 222457 := bbase (se 2 (by rfl) ⟨83421, by rfl⟩ : syracuseStep 222457 = 166843) (by norm_num)
theorem B222493 : Blo 195805 222493 := bbase (se 3 (by rfl) ⟨41717, by rfl⟩ : syracuseStep 222493 = 83435) (by norm_num)
theorem B222529 : Blo 195805 222529 := bbase (se 2 (by rfl) ⟨83448, by rfl⟩ : syracuseStep 222529 = 166897) (by norm_num)
theorem B222565 : Blo 195805 222565 := bbase (se 4 (by rfl) ⟨20865, by rfl⟩ : syracuseStep 222565 = 41731) (by norm_num)
theorem B222601 : Blo 195805 222601 := bbase (se 2 (by rfl) ⟨83475, by rfl⟩ : syracuseStep 222601 = 166951) (by norm_num)
theorem B222637 : Blo 195805 222637 := bbase (se 3 (by rfl) ⟨41744, by rfl⟩ : syracuseStep 222637 = 83489) (by norm_num)
theorem B222673 : Blo 195805 222673 := bbase (se 2 (by rfl) ⟨83502, by rfl⟩ : syracuseStep 222673 = 167005) (by norm_num)
theorem B222709 : Blo 195805 222709 := bbase (se 5 (by rfl) ⟨10439, by rfl⟩ : syracuseStep 222709 = 20879) (by norm_num)
theorem B222745 : Blo 195805 222745 := bbase (se 2 (by rfl) ⟨83529, by rfl⟩ : syracuseStep 222745 = 167059) (by norm_num)
theorem B222781 : Blo 195805 222781 := bbase (se 3 (by rfl) ⟨41771, by rfl⟩ : syracuseStep 222781 = 83543) (by norm_num)
theorem B222817 : Blo 195805 222817 := bbase (se 2 (by rfl) ⟨83556, by rfl⟩ : syracuseStep 222817 = 167113) (by norm_num)
theorem B222853 : Blo 195805 222853 := bbase (se 4 (by rfl) ⟨20892, by rfl⟩ : syracuseStep 222853 = 41785) (by norm_num)
theorem B222889 : Blo 195805 222889 := bbase (se 2 (by rfl) ⟨83583, by rfl⟩ : syracuseStep 222889 = 167167) (by norm_num)
theorem B222925 : Blo 195805 222925 := bbase (se 3 (by rfl) ⟨41798, by rfl⟩ : syracuseStep 222925 = 83597) (by norm_num)
theorem B222961 : Blo 195805 222961 := bbase (se 2 (by rfl) ⟨83610, by rfl⟩ : syracuseStep 222961 = 167221) (by norm_num)
theorem B419597 : Blo 195805 419597 := bbase (se 3 (by rfl) ⟨78674, by rfl⟩ : syracuseStep 419597 = 157349) (by norm_num)
theorem B222997 : Blo 195805 222997 := bbase (se 6 (by rfl) ⟨5226, by rfl⟩ : syracuseStep 222997 = 10453) (by norm_num)
theorem B223033 : Blo 195805 223033 := bbase (se 2 (by rfl) ⟨83637, by rfl⟩ : syracuseStep 223033 = 167275) (by norm_num)
theorem B223069 : Blo 195805 223069 := bbase (se 3 (by rfl) ⟨41825, by rfl⟩ : syracuseStep 223069 = 83651) (by norm_num)
theorem B223105 : Blo 195805 223105 := bbase (se 2 (by rfl) ⟨83664, by rfl⟩ : syracuseStep 223105 = 167329) (by norm_num)
theorem B419717 : Blo 195805 419717 := bbase (se 4 (by rfl) ⟨39348, by rfl⟩ : syracuseStep 419717 = 78697) (by norm_num)
theorem B223141 : Blo 195805 223141 := bbase (se 4 (by rfl) ⟨20919, by rfl⟩ : syracuseStep 223141 = 41839) (by norm_num)
theorem B223177 : Blo 195805 223177 := bbase (se 2 (by rfl) ⟨83691, by rfl⟩ : syracuseStep 223177 = 167383) (by norm_num)
theorem B223213 : Blo 195805 223213 := bbase (se 3 (by rfl) ⟨41852, by rfl⟩ : syracuseStep 223213 = 83705) (by norm_num)
theorem B223249 : Blo 195805 223249 := bbase (se 2 (by rfl) ⟨83718, by rfl⟩ : syracuseStep 223249 = 167437) (by norm_num)
theorem B223285 : Blo 195805 223285 := bbase (se 5 (by rfl) ⟨10466, by rfl⟩ : syracuseStep 223285 = 20933) (by norm_num)
theorem B747589 : Blo 195805 747589 := bbase (se 4 (by rfl) ⟨70086, by rfl⟩ : syracuseStep 747589 = 140173) (by norm_num)
theorem B223321 : Blo 195805 223321 := bbase (se 2 (by rfl) ⟨83745, by rfl⟩ : syracuseStep 223321 = 167491) (by norm_num)
theorem B223357 : Blo 195805 223357 := bbase (se 3 (by rfl) ⟨41879, by rfl⟩ : syracuseStep 223357 = 83759) (by norm_num)
theorem B354461 : Blo 195805 354461 := bbase (se 3 (by rfl) ⟨66461, by rfl⟩ : syracuseStep 354461 = 132923) (by norm_num)
theorem B223393 : Blo 195805 223393 := bbase (se 2 (by rfl) ⟨83772, by rfl⟩ : syracuseStep 223393 = 167545) (by norm_num)
theorem B223429 : Blo 195805 223429 := bbase (se 4 (by rfl) ⟨20946, by rfl⟩ : syracuseStep 223429 = 41893) (by norm_num)
theorem B223465 : Blo 195805 223465 := bbase (se 2 (by rfl) ⟨83799, by rfl⟩ : syracuseStep 223465 = 167599) (by norm_num)
theorem B223501 : Blo 195805 223501 := bbase (se 3 (by rfl) ⟨41906, by rfl⟩ : syracuseStep 223501 = 83813) (by norm_num)
theorem B223537 : Blo 195805 223537 := bbase (se 2 (by rfl) ⟨83826, by rfl⟩ : syracuseStep 223537 = 167653) (by norm_num)
theorem B223573 : Blo 195805 223573 := bbase (se 10 (by rfl) ⟨327, by rfl⟩ : syracuseStep 223573 = 655) (by norm_num)
theorem B747893 : Blo 195805 747893 := bbase (se 5 (by rfl) ⟨35057, by rfl⟩ : syracuseStep 747893 = 70115) (by norm_num)
theorem B223609 : Blo 195805 223609 := bbase (se 2 (by rfl) ⟨83853, by rfl⟩ : syracuseStep 223609 = 167707) (by norm_num)
theorem B1010069 : Blo 195805 1010069 := bbase (se 6 (by rfl) ⟨23673, by rfl⟩ : syracuseStep 1010069 = 47347) (by norm_num)
theorem B223645 : Blo 195805 223645 := bbase (se 3 (by rfl) ⟨41933, by rfl⟩ : syracuseStep 223645 = 83867) (by norm_num)
theorem B223681 : Blo 195805 223681 := bbase (se 2 (by rfl) ⟨83880, by rfl⟩ : syracuseStep 223681 = 167761) (by norm_num)
theorem B223717 : Blo 195805 223717 := bbase (se 4 (by rfl) ⟨20973, by rfl⟩ : syracuseStep 223717 = 41947) (by norm_num)
theorem B420349 : Blo 195805 420349 := bbase (se 3 (by rfl) ⟨78815, by rfl⟩ : syracuseStep 420349 = 157631) (by norm_num)
theorem B223753 : Blo 195805 223753 := bbase (se 2 (by rfl) ⟨83907, by rfl⟩ : syracuseStep 223753 = 167815) (by norm_num)
theorem B223789 : Blo 195805 223789 := bbase (se 3 (by rfl) ⟨41960, by rfl⟩ : syracuseStep 223789 = 83921) (by norm_num)
theorem B223825 : Blo 195805 223825 := bbase (se 2 (by rfl) ⟨83934, by rfl⟩ : syracuseStep 223825 = 167869) (by norm_num)
theorem B682597 : Blo 195805 682597 := bbase (se 4 (by rfl) ⟨63993, by rfl⟩ : syracuseStep 682597 = 127987) (by norm_num)
theorem B223861 : Blo 195805 223861 := bbase (se 5 (by rfl) ⟨10493, by rfl⟩ : syracuseStep 223861 = 20987) (by norm_num)
theorem B223897 : Blo 195805 223897 := bbase (se 2 (by rfl) ⟨83961, by rfl⟩ : syracuseStep 223897 = 167923) (by norm_num)
theorem B223933 : Blo 195805 223933 := bbase (se 3 (by rfl) ⟨41987, by rfl⟩ : syracuseStep 223933 = 83975) (by norm_num)
theorem B223969 : Blo 195805 223969 := bbase (se 2 (by rfl) ⟨83988, by rfl⟩ : syracuseStep 223969 = 167977) (by norm_num)
theorem B224005 : Blo 195805 224005 := bbase (se 4 (by rfl) ⟨21000, by rfl⟩ : syracuseStep 224005 = 42001) (by norm_num)
theorem B224041 : Blo 195805 224041 := bbase (se 2 (by rfl) ⟨84015, by rfl⟩ : syracuseStep 224041 = 168031) (by norm_num)
theorem B224077 : Blo 195805 224077 := bbase (se 3 (by rfl) ⟨42014, by rfl⟩ : syracuseStep 224077 = 84029) (by norm_num)
theorem B322397 : Blo 195805 322397 := bbase (se 3 (by rfl) ⟨60449, by rfl⟩ : syracuseStep 322397 = 120899) (by norm_num)
theorem B224113 : Blo 195805 224113 := bbase (se 2 (by rfl) ⟨84042, by rfl⟩ : syracuseStep 224113 = 168085) (by norm_num)
theorem B224149 : Blo 195805 224149 := bbase (se 6 (by rfl) ⟨5253, by rfl⟩ : syracuseStep 224149 = 10507) (by norm_num)
theorem B224185 : Blo 195805 224185 := bbase (se 2 (by rfl) ⟨84069, by rfl⟩ : syracuseStep 224185 = 168139) (by norm_num)
theorem B256981 : Blo 195805 256981 := bbase (se 7 (by rfl) ⟨3011, by rfl⟩ : syracuseStep 256981 = 6023) (by norm_num)
theorem B224221 : Blo 195805 224221 := bbase (se 3 (by rfl) ⟨42041, by rfl⟩ : syracuseStep 224221 = 84083) (by norm_num)
theorem B224257 : Blo 195805 224257 := bbase (se 2 (by rfl) ⟨84096, by rfl⟩ : syracuseStep 224257 = 168193) (by norm_num)
theorem B224293 : Blo 195805 224293 := bbase (se 4 (by rfl) ⟨21027, by rfl⟩ : syracuseStep 224293 = 42055) (by norm_num)
theorem B224329 : Blo 195805 224329 := bbase (se 2 (by rfl) ⟨84123, by rfl⟩ : syracuseStep 224329 = 168247) (by norm_num)
theorem B224365 : Blo 195805 224365 := bbase (se 3 (by rfl) ⟨42068, by rfl⟩ : syracuseStep 224365 = 84137) (by norm_num)
theorem B224401 : Blo 195805 224401 := bbase (se 2 (by rfl) ⟨84150, by rfl⟩ : syracuseStep 224401 = 168301) (by norm_num)
theorem B224437 : Blo 195805 224437 := bbase (se 5 (by rfl) ⟨10520, by rfl⟩ : syracuseStep 224437 = 21041) (by norm_num)
theorem B224473 : Blo 195805 224473 := bbase (se 2 (by rfl) ⟨84177, by rfl⟩ : syracuseStep 224473 = 168355) (by norm_num)
theorem B224509 : Blo 195805 224509 := bbase (se 3 (by rfl) ⟨42095, by rfl⟩ : syracuseStep 224509 = 84191) (by norm_num)
theorem B224545 : Blo 195805 224545 := bbase (se 2 (by rfl) ⟨84204, by rfl⟩ : syracuseStep 224545 = 168409) (by norm_num)
theorem B224581 : Blo 195805 224581 := bbase (se 4 (by rfl) ⟨21054, by rfl⟩ : syracuseStep 224581 = 42109) (by norm_num)
theorem B847189 : Blo 195805 847189 := bbase (se 11 (by rfl) ⟨620, by rfl⟩ : syracuseStep 847189 = 1241) (by norm_num)
theorem B224617 : Blo 195805 224617 := bbase (se 2 (by rfl) ⟨84231, by rfl⟩ : syracuseStep 224617 = 168463) (by norm_num)
theorem B421237 : Blo 195805 421237 := bbase (se 5 (by rfl) ⟨19745, by rfl⟩ : syracuseStep 421237 = 39491) (by norm_num)
theorem B1207669 : Blo 195805 1207669 := bbase (se 5 (by rfl) ⟨56609, by rfl⟩ : syracuseStep 1207669 = 113219) (by norm_num)
theorem B1076597 : Blo 195805 1076597 := bbase (se 5 (by rfl) ⟨50465, by rfl⟩ : syracuseStep 1076597 = 100931) (by norm_num)
theorem B224653 : Blo 195805 224653 := bbase (se 3 (by rfl) ⟨42122, by rfl⟩ : syracuseStep 224653 = 84245) (by norm_num)
theorem B224689 : Blo 195805 224689 := bbase (se 2 (by rfl) ⟨84258, by rfl⟩ : syracuseStep 224689 = 168517) (by norm_num)
theorem B224713 : Blo 195805 224713 := bbase (se 2 (by rfl) ⟨84267, by rfl⟩ : syracuseStep 224713 = 168535) (by norm_num)
theorem B224725 : Blo 195805 224725 := bbase (se 7 (by rfl) ⟨2633, by rfl⟩ : syracuseStep 224725 = 5267) (by norm_num)
theorem B421357 : Blo 195805 421357 := bbase (se 3 (by rfl) ⟨79004, by rfl⟩ : syracuseStep 421357 = 158009) (by norm_num)
theorem B224761 : Blo 195805 224761 := bbase (se 2 (by rfl) ⟨84285, by rfl⟩ : syracuseStep 224761 = 168571) (by norm_num)
theorem B355909 : Blo 195805 355909 := bbase (se 4 (by rfl) ⟨33366, by rfl⟩ : syracuseStep 355909 = 66733) (by norm_num)
theorem B1011365 : Blo 195805 1011365 := bbase (se 4 (by rfl) ⟨94815, by rfl⟩ : syracuseStep 1011365 = 189631) (by norm_num)
theorem B1699541 : Blo 195805 1699541 := bbase (se 7 (by rfl) ⟨19916, by rfl⟩ : syracuseStep 1699541 = 39833) (by norm_num)
theorem B421613 : Blo 195805 421613 := bbase (se 3 (by rfl) ⟨79052, by rfl⟩ : syracuseStep 421613 = 158105) (by norm_num)
theorem B323357 : Blo 195805 323357 := bbase (se 3 (by rfl) ⟨60629, by rfl⟩ : syracuseStep 323357 = 121259) (by norm_num)
theorem B389053 : Blo 195805 389053 := bbase (se 3 (by rfl) ⟨72947, by rfl⟩ : syracuseStep 389053 = 145895) (by norm_num)
theorem B356717 : Blo 195805 356717 := bbase (se 3 (by rfl) ⟨66884, by rfl⟩ : syracuseStep 356717 = 133769) (by norm_num)
theorem B750005 : Blo 195805 750005 := bbase (se 5 (by rfl) ⟨35156, by rfl⟩ : syracuseStep 750005 = 70313) (by norm_num)
theorem B356789 : Blo 195805 356789 := bbase (se 5 (by rfl) ⟨16724, by rfl⟩ : syracuseStep 356789 = 33449) (by norm_num)
theorem B1896949 : Blo 195805 1896949 := bbase (se 5 (by rfl) ⟨88919, by rfl⟩ : syracuseStep 1896949 = 177839) (by norm_num)
theorem B1274453 : Blo 195805 1274453 := bbase (se 8 (by rfl) ⟨7467, by rfl⟩ : syracuseStep 1274453 = 14935) (by norm_num)
theorem B422501 : Blo 195805 422501 := bbase (se 4 (by rfl) ⟨39609, by rfl⟩ : syracuseStep 422501 = 79219) (by norm_num)
theorem B848501 : Blo 195805 848501 := bbase (se 5 (by rfl) ⟨39773, by rfl⟩ : syracuseStep 848501 = 79547) (by norm_num)
theorem B357005 : Blo 195805 357005 := bbase (se 3 (by rfl) ⟨66938, by rfl⟩ : syracuseStep 357005 = 133877) (by norm_num)
theorem B750293 : Blo 195805 750293 := bbase (se 7 (by rfl) ⟨8792, by rfl⟩ : syracuseStep 750293 = 17585) (by norm_num)
theorem B848677 : Blo 195805 848677 := bbase (se 4 (by rfl) ⟨79563, by rfl⟩ : syracuseStep 848677 = 159127) (by norm_num)
theorem B848693 : Blo 195805 848693 := bbase (se 5 (by rfl) ⟨39782, by rfl⟩ : syracuseStep 848693 = 79565) (by norm_num)
theorem B422741 : Blo 195805 422741 := bbase (se 9 (by rfl) ⟨1238, by rfl⟩ : syracuseStep 422741 = 2477) (by norm_num)
theorem B947477 : Blo 195805 947477 := bbase (se 6 (by rfl) ⟨22206, by rfl⟩ : syracuseStep 947477 = 44413) (by norm_num)
theorem B423245 : Blo 195805 423245 := bbase (se 3 (by rfl) ⟨79358, by rfl⟩ : syracuseStep 423245 = 158717) (by norm_num)
theorem B423253 : Blo 195805 423253 := bbase (se 13 (by rfl) ⟨77, by rfl⟩ : syracuseStep 423253 = 155) (by norm_num)
theorem B3437909 : Blo 195805 3437909 := bbase (se 13 (by rfl) ⟨629, by rfl⟩ : syracuseStep 3437909 = 1259) (by norm_num)
theorem B456245 : Blo 195805 456245 := bbase (se 5 (by rfl) ⟨21386, by rfl⟩ : syracuseStep 456245 = 42773) (by norm_num)
theorem B751477 : Blo 195805 751477 := bbase (se 5 (by rfl) ⟨35225, by rfl⟩ : syracuseStep 751477 = 70451) (by norm_num)
theorem B1505141 : Blo 195805 1505141 := bbase (se 5 (by rfl) ⟨70553, by rfl⟩ : syracuseStep 1505141 = 141107) (by norm_num)
theorem B751781 : Blo 195805 751781 := bbase (se 4 (by rfl) ⟨70479, by rfl⟩ : syracuseStep 751781 = 140959) (by norm_num)
theorem B227705 : Blo 195805 227705 := bbase (se 2 (by rfl) ⟨85389, by rfl⟩ : syracuseStep 227705 = 170779) (by norm_num)
theorem B424381 : Blo 195805 424381 := bbase (se 3 (by rfl) ⟨79571, by rfl⟩ : syracuseStep 424381 = 159143) (by norm_num)
theorem B3176981 : Blo 195805 3176981 := bbase (se 6 (by rfl) ⟨74460, by rfl⟩ : syracuseStep 3176981 = 148921) (by norm_num)
theorem B424525 : Blo 195805 424525 := bbase (se 3 (by rfl) ⟨79598, by rfl⟩ : syracuseStep 424525 = 159197) (by norm_num)
theorem B424597 : Blo 195805 424597 := bbase (se 6 (by rfl) ⟨9951, by rfl⟩ : syracuseStep 424597 = 19903) (by norm_num)
theorem B457445 : Blo 195805 457445 := bbase (se 4 (by rfl) ⟨42885, by rfl⟩ : syracuseStep 457445 = 85771) (by norm_num)
theorem B424757 : Blo 195805 424757 := bbase (se 5 (by rfl) ⟨19910, by rfl⟩ : syracuseStep 424757 = 39821) (by norm_num)
theorem B293717 : Blo 195805 293717 := bbase (se 9 (by rfl) ⟨860, by rfl⟩ : syracuseStep 293717 = 1721) (by norm_num)
theorem B293741 : Blo 195805 293741 := bbase (se 3 (by rfl) ⟨55076, by rfl⟩ : syracuseStep 293741 = 110153) (by norm_num)
theorem B293765 : Blo 195805 293765 := bbase (se 4 (by rfl) ⟨27540, by rfl⟩ : syracuseStep 293765 = 55081) (by norm_num)
theorem B293789 : Blo 195805 293789 := bbase (se 3 (by rfl) ⟨55085, by rfl⟩ : syracuseStep 293789 = 110171) (by norm_num)
theorem B293813 : Blo 195805 293813 := bbase (se 5 (by rfl) ⟨13772, by rfl⟩ : syracuseStep 293813 = 27545) (by norm_num)
theorem B293837 : Blo 195805 293837 := bbase (se 3 (by rfl) ⟨55094, by rfl⟩ : syracuseStep 293837 = 110189) (by norm_num)
theorem B293861 : Blo 195805 293861 := bbase (se 4 (by rfl) ⟨27549, by rfl⟩ : syracuseStep 293861 = 55099) (by norm_num)
theorem B293885 : Blo 195805 293885 := bbase (se 3 (by rfl) ⟨55103, by rfl⟩ : syracuseStep 293885 = 110207) (by norm_num)
theorem B850949 : Blo 195805 850949 := bbase (se 4 (by rfl) ⟨79776, by rfl⟩ : syracuseStep 850949 = 159553) (by norm_num)
theorem B293909 : Blo 195805 293909 := bbase (se 6 (by rfl) ⟨6888, by rfl⟩ : syracuseStep 293909 = 13777) (by norm_num)
theorem B293933 : Blo 195805 293933 := bbase (se 3 (by rfl) ⟨55112, by rfl⟩ : syracuseStep 293933 = 110225) (by norm_num)
theorem B293957 : Blo 195805 293957 := bbase (se 4 (by rfl) ⟨27558, by rfl⟩ : syracuseStep 293957 = 55117) (by norm_num)
theorem B326741 : Blo 195805 326741 := bbase (se 8 (by rfl) ⟨1914, by rfl⟩ : syracuseStep 326741 = 3829) (by norm_num)
theorem B293981 : Blo 195805 293981 := bbase (se 3 (by rfl) ⟨55121, by rfl⟩ : syracuseStep 293981 = 110243) (by norm_num)
theorem B294005 : Blo 195805 294005 := bbase (se 5 (by rfl) ⟨13781, by rfl⟩ : syracuseStep 294005 = 27563) (by norm_num)
theorem B294029 : Blo 195805 294029 := bbase (se 3 (by rfl) ⟨55130, by rfl⟩ : syracuseStep 294029 = 110261) (by norm_num)
theorem B294053 : Blo 195805 294053 := bbase (se 4 (by rfl) ⟨27567, by rfl⟩ : syracuseStep 294053 = 55135) (by norm_num)
theorem B294077 : Blo 195805 294077 := bbase (se 3 (by rfl) ⟨55139, by rfl⟩ : syracuseStep 294077 = 110279) (by norm_num)
theorem B294101 : Blo 195805 294101 := bbase (se 7 (by rfl) ⟨3446, by rfl⟩ : syracuseStep 294101 = 6893) (by norm_num)
theorem B294125 : Blo 195805 294125 := bbase (se 3 (by rfl) ⟨55148, by rfl⟩ : syracuseStep 294125 = 110297) (by norm_num)
theorem B294149 : Blo 195805 294149 := bbase (se 4 (by rfl) ⟨27576, by rfl⟩ : syracuseStep 294149 = 55153) (by norm_num)
theorem B294173 : Blo 195805 294173 := bbase (se 3 (by rfl) ⟨55157, by rfl⟩ : syracuseStep 294173 = 110315) (by norm_num)
theorem B294197 : Blo 195805 294197 := bbase (se 5 (by rfl) ⟨13790, by rfl⟩ : syracuseStep 294197 = 27581) (by norm_num)
theorem B294221 : Blo 195805 294221 := bbase (se 3 (by rfl) ⟨55166, by rfl⟩ : syracuseStep 294221 = 110333) (by norm_num)
theorem B294245 : Blo 195805 294245 := bbase (se 4 (by rfl) ⟨27585, by rfl⟩ : syracuseStep 294245 = 55171) (by norm_num)
theorem B294269 : Blo 195805 294269 := bbase (se 3 (by rfl) ⟨55175, by rfl⟩ : syracuseStep 294269 = 110351) (by norm_num)
theorem B294293 : Blo 195805 294293 := bbase (se 6 (by rfl) ⟨6897, by rfl⟩ : syracuseStep 294293 = 13795) (by norm_num)
theorem B294317 : Blo 195805 294317 := bbase (se 3 (by rfl) ⟨55184, by rfl⟩ : syracuseStep 294317 = 110369) (by norm_num)
theorem B294341 : Blo 195805 294341 := bbase (se 4 (by rfl) ⟨27594, by rfl⟩ : syracuseStep 294341 = 55189) (by norm_num)
theorem B294365 : Blo 195805 294365 := bbase (se 3 (by rfl) ⟨55193, by rfl⟩ : syracuseStep 294365 = 110387) (by norm_num)
theorem B294389 : Blo 195805 294389 := bbase (se 5 (by rfl) ⟨13799, by rfl⟩ : syracuseStep 294389 = 27599) (by norm_num)
theorem B294413 : Blo 195805 294413 := bbase (se 3 (by rfl) ⟨55202, by rfl⟩ : syracuseStep 294413 = 110405) (by norm_num)
theorem B294437 : Blo 195805 294437 := bbase (se 4 (by rfl) ⟨27603, by rfl⟩ : syracuseStep 294437 = 55207) (by norm_num)
theorem B294461 : Blo 195805 294461 := bbase (se 3 (by rfl) ⟨55211, by rfl⟩ : syracuseStep 294461 = 110423) (by norm_num)
theorem B294485 : Blo 195805 294485 := bbase (se 8 (by rfl) ⟨1725, by rfl⟩ : syracuseStep 294485 = 3451) (by norm_num)
theorem B294509 : Blo 195805 294509 := bbase (se 3 (by rfl) ⟨55220, by rfl⟩ : syracuseStep 294509 = 110441) (by norm_num)
theorem B294533 : Blo 195805 294533 := bbase (se 4 (by rfl) ⟨27612, by rfl⟩ : syracuseStep 294533 = 55225) (by norm_num)
theorem B294557 : Blo 195805 294557 := bbase (se 3 (by rfl) ⟨55229, by rfl⟩ : syracuseStep 294557 = 110459) (by norm_num)
theorem B294581 : Blo 195805 294581 := bbase (se 5 (by rfl) ⟨13808, by rfl⟩ : syracuseStep 294581 = 27617) (by norm_num)
theorem B294605 : Blo 195805 294605 := bbase (se 3 (by rfl) ⟨55238, by rfl⟩ : syracuseStep 294605 = 110477) (by norm_num)
theorem B1277653 : Blo 195805 1277653 := bbase (se 7 (by rfl) ⟨14972, by rfl⟩ : syracuseStep 1277653 = 29945) (by norm_num)
theorem B294629 : Blo 195805 294629 := bbase (se 4 (by rfl) ⟨27621, by rfl⟩ : syracuseStep 294629 = 55243) (by norm_num)
theorem B294653 : Blo 195805 294653 := bbase (se 3 (by rfl) ⟨55247, by rfl⟩ : syracuseStep 294653 = 110495) (by norm_num)
theorem B294677 : Blo 195805 294677 := bbase (se 6 (by rfl) ⟨6906, by rfl⟩ : syracuseStep 294677 = 13813) (by norm_num)
theorem B294701 : Blo 195805 294701 := bbase (se 3 (by rfl) ⟨55256, by rfl⟩ : syracuseStep 294701 = 110513) (by norm_num)
theorem B294725 : Blo 195805 294725 := bbase (se 4 (by rfl) ⟨27630, by rfl⟩ : syracuseStep 294725 = 55261) (by norm_num)
theorem B294749 : Blo 195805 294749 := bbase (se 3 (by rfl) ⟨55265, by rfl⟩ : syracuseStep 294749 = 110531) (by norm_num)
theorem B294773 : Blo 195805 294773 := bbase (se 5 (by rfl) ⟨13817, by rfl⟩ : syracuseStep 294773 = 27635) (by norm_num)
theorem B294797 : Blo 195805 294797 := bbase (se 3 (by rfl) ⟨55274, by rfl⟩ : syracuseStep 294797 = 110549) (by norm_num)
theorem B294821 : Blo 195805 294821 := bbase (se 4 (by rfl) ⟨27639, by rfl⟩ : syracuseStep 294821 = 55279) (by norm_num)
theorem B294845 : Blo 195805 294845 := bbase (se 3 (by rfl) ⟨55283, by rfl⟩ : syracuseStep 294845 = 110567) (by norm_num)
theorem B294869 : Blo 195805 294869 := bbase (se 7 (by rfl) ⟨3455, by rfl⟩ : syracuseStep 294869 = 6911) (by norm_num)
theorem B294893 : Blo 195805 294893 := bbase (se 3 (by rfl) ⟨55292, by rfl⟩ : syracuseStep 294893 = 110585) (by norm_num)
theorem B196611 : Blo 195805 196611 := bstep (se 1 (by rfl) ⟨147458, by rfl⟩ : syracuseStep 196611 = 294917) B294917
theorem B425987 : Blo 195805 425987 := bstep (se 1 (by rfl) ⟨319490, by rfl⟩ : syracuseStep 425987 = 638981) B638981
theorem B294929 : Blo 195805 294929 := bstep (se 2 (by rfl) ⟨110598, by rfl⟩ : syracuseStep 294929 = 221197) B221197
theorem B196627 : Blo 195805 196627 := bstep (se 1 (by rfl) ⟨147470, by rfl⟩ : syracuseStep 196627 = 294941) B294941
theorem B294947 : Blo 195805 294947 := bstep (se 1 (by rfl) ⟨221210, by rfl⟩ : syracuseStep 294947 = 442421) B442421
theorem B196643 : Blo 195805 196643 := bstep (se 1 (by rfl) ⟨147482, by rfl⟩ : syracuseStep 196643 = 294965) B294965
theorem B196659 : Blo 195805 196659 := bstep (se 1 (by rfl) ⟨147494, by rfl⟩ : syracuseStep 196659 = 294989) B294989
theorem B294977 : Blo 195805 294977 := bstep (se 2 (by rfl) ⟨110616, by rfl⟩ : syracuseStep 294977 = 221233) B221233
theorem B196675 : Blo 195805 196675 := bstep (se 1 (by rfl) ⟨147506, by rfl⟩ : syracuseStep 196675 = 295013) B295013
theorem B294995 : Blo 195805 294995 := bstep (se 1 (by rfl) ⟨221246, by rfl⟩ : syracuseStep 294995 = 442493) B442493
theorem B196691 : Blo 195805 196691 := bstep (se 1 (by rfl) ⟨147518, by rfl⟩ : syracuseStep 196691 = 295037) B295037
theorem B196707 : Blo 195805 196707 := bstep (se 1 (by rfl) ⟨147530, by rfl⟩ : syracuseStep 196707 = 295061) B295061
theorem B295025 : Blo 195805 295025 := bstep (se 2 (by rfl) ⟨110634, by rfl⟩ : syracuseStep 295025 = 221269) B221269
theorem B196723 : Blo 195805 196723 := bstep (se 1 (by rfl) ⟨147542, by rfl⟩ : syracuseStep 196723 = 295085) B295085
theorem B295043 : Blo 195805 295043 := bstep (se 1 (by rfl) ⟨221282, by rfl⟩ : syracuseStep 295043 = 442565) B442565
theorem B196739 : Blo 195805 196739 := bstep (se 1 (by rfl) ⟨147554, by rfl⟩ : syracuseStep 196739 = 295109) B295109
theorem B196755 : Blo 195805 196755 := bstep (se 1 (by rfl) ⟨147566, by rfl⟩ : syracuseStep 196755 = 295133) B295133
theorem B295073 : Blo 195805 295073 := bstep (se 2 (by rfl) ⟨110652, by rfl⟩ : syracuseStep 295073 = 221305) B221305
theorem B196771 : Blo 195805 196771 := bstep (se 1 (by rfl) ⟨147578, by rfl⟩ : syracuseStep 196771 = 295157) B295157
theorem B295091 : Blo 195805 295091 := bstep (se 1 (by rfl) ⟨221318, by rfl⟩ : syracuseStep 295091 = 442637) B442637
theorem B196787 : Blo 195805 196787 := bstep (se 1 (by rfl) ⟨147590, by rfl⟩ : syracuseStep 196787 = 295181) B295181
theorem B196803 : Blo 195805 196803 := bstep (se 1 (by rfl) ⟨147602, by rfl⟩ : syracuseStep 196803 = 295205) B295205
theorem B295121 : Blo 195805 295121 := bstep (se 2 (by rfl) ⟨110670, by rfl⟩ : syracuseStep 295121 = 221341) B221341
theorem B196819 : Blo 195805 196819 := bstep (se 1 (by rfl) ⟨147614, by rfl⟩ : syracuseStep 196819 = 295229) B295229
theorem B295139 : Blo 195805 295139 := bstep (se 1 (by rfl) ⟨221354, by rfl⟩ : syracuseStep 295139 = 442709) B442709
theorem B196835 : Blo 195805 196835 := bstep (se 1 (by rfl) ⟨147626, by rfl⟩ : syracuseStep 196835 = 295253) B295253
theorem B196851 : Blo 195805 196851 := bstep (se 1 (by rfl) ⟨147638, by rfl⟩ : syracuseStep 196851 = 295277) B295277
theorem B295169 : Blo 195805 295169 := bstep (se 2 (by rfl) ⟨110688, by rfl⟩ : syracuseStep 295169 = 221377) B221377
theorem B196867 : Blo 195805 196867 := bstep (se 1 (by rfl) ⟨147650, by rfl⟩ : syracuseStep 196867 = 295301) B295301
theorem B295187 : Blo 195805 295187 := bstep (se 1 (by rfl) ⟨221390, by rfl⟩ : syracuseStep 295187 = 442781) B442781
theorem B196883 : Blo 195805 196883 := bstep (se 1 (by rfl) ⟨147662, by rfl⟩ : syracuseStep 196883 = 295325) B295325
theorem B196899 : Blo 195805 196899 := bstep (se 1 (by rfl) ⟨147674, by rfl⟩ : syracuseStep 196899 = 295349) B295349
theorem B295217 : Blo 195805 295217 := bstep (se 2 (by rfl) ⟨110706, by rfl⟩ : syracuseStep 295217 = 221413) B221413
theorem B196915 : Blo 195805 196915 := bstep (se 1 (by rfl) ⟨147686, by rfl⟩ : syracuseStep 196915 = 295373) B295373
theorem B295235 : Blo 195805 295235 := bstep (se 1 (by rfl) ⟨221426, by rfl⟩ : syracuseStep 295235 = 442853) B442853
theorem B196931 : Blo 195805 196931 := bstep (se 1 (by rfl) ⟨147698, by rfl⟩ : syracuseStep 196931 = 295397) B295397
theorem B196947 : Blo 195805 196947 := bstep (se 1 (by rfl) ⟨147710, by rfl⟩ : syracuseStep 196947 = 295421) B295421
theorem B295265 : Blo 195805 295265 := bstep (se 2 (by rfl) ⟨110724, by rfl⟩ : syracuseStep 295265 = 221449) B221449
theorem B196963 : Blo 195805 196963 := bstep (se 1 (by rfl) ⟨147722, by rfl⟩ : syracuseStep 196963 = 295445) B295445
theorem B295283 : Blo 195805 295283 := bstep (se 1 (by rfl) ⟨221462, by rfl⟩ : syracuseStep 295283 = 442925) B442925
theorem B196979 : Blo 195805 196979 := bstep (se 1 (by rfl) ⟨147734, by rfl⟩ : syracuseStep 196979 = 295469) B295469
theorem B196995 : Blo 195805 196995 := bstep (se 1 (by rfl) ⟨147746, by rfl⟩ : syracuseStep 196995 = 295493) B295493
theorem B295313 : Blo 195805 295313 := bstep (se 2 (by rfl) ⟨110742, by rfl⟩ : syracuseStep 295313 = 221485) B221485
theorem B197011 : Blo 195805 197011 := bstep (se 1 (by rfl) ⟨147758, by rfl⟩ : syracuseStep 197011 = 295517) B295517
theorem B295331 : Blo 195805 295331 := bstep (se 1 (by rfl) ⟨221498, by rfl⟩ : syracuseStep 295331 = 442997) B442997
theorem B197027 : Blo 195805 197027 := bstep (se 1 (by rfl) ⟨147770, by rfl⟩ : syracuseStep 197027 = 295541) B295541
theorem B197043 : Blo 195805 197043 := bstep (se 1 (by rfl) ⟨147782, by rfl⟩ : syracuseStep 197043 = 295565) B295565
theorem B295361 : Blo 195805 295361 := bstep (se 2 (by rfl) ⟨110760, by rfl⟩ : syracuseStep 295361 = 221521) B221521
theorem B197059 : Blo 195805 197059 := bstep (se 1 (by rfl) ⟨147794, by rfl⟩ : syracuseStep 197059 = 295589) B295589
theorem B295379 : Blo 195805 295379 := bstep (se 1 (by rfl) ⟨221534, by rfl⟩ : syracuseStep 295379 = 443069) B443069
theorem B197075 : Blo 195805 197075 := bstep (se 1 (by rfl) ⟨147806, by rfl⟩ : syracuseStep 197075 = 295613) B295613
theorem B197091 : Blo 195805 197091 := bstep (se 1 (by rfl) ⟨147818, by rfl⟩ : syracuseStep 197091 = 295637) B295637
theorem B295409 : Blo 195805 295409 := bstep (se 2 (by rfl) ⟨110778, by rfl⟩ : syracuseStep 295409 = 221557) B221557
theorem B197107 : Blo 195805 197107 := bstep (se 1 (by rfl) ⟨147830, by rfl⟩ : syracuseStep 197107 = 295661) B295661
theorem B295427 : Blo 195805 295427 := bstep (se 1 (by rfl) ⟨221570, by rfl⟩ : syracuseStep 295427 = 443141) B443141
theorem B197123 : Blo 195805 197123 := bstep (se 1 (by rfl) ⟨147842, by rfl⟩ : syracuseStep 197123 = 295685) B295685
theorem B197139 : Blo 195805 197139 := bstep (se 1 (by rfl) ⟨147854, by rfl⟩ : syracuseStep 197139 = 295709) B295709
theorem B295457 : Blo 195805 295457 := bstep (se 2 (by rfl) ⟨110796, by rfl⟩ : syracuseStep 295457 = 221593) B221593
theorem B197155 : Blo 195805 197155 := bstep (se 1 (by rfl) ⟨147866, by rfl⟩ : syracuseStep 197155 = 295733) B295733
theorem B754211 : Blo 195805 754211 := bstep (se 1 (by rfl) ⟨565658, by rfl⟩ : syracuseStep 754211 = 1131317) B1131317
theorem B557617 : Blo 195805 557617 := bstep (se 2 (by rfl) ⟨209106, by rfl⟩ : syracuseStep 557617 = 418213) B418213
theorem B295475 : Blo 195805 295475 := bstep (se 1 (by rfl) ⟨221606, by rfl⟩ : syracuseStep 295475 = 443213) B443213
theorem B197171 : Blo 195805 197171 := bstep (se 1 (by rfl) ⟨147878, by rfl⟩ : syracuseStep 197171 = 295757) B295757
theorem B197187 : Blo 195805 197187 := bstep (se 1 (by rfl) ⟨147890, by rfl⟩ : syracuseStep 197187 = 295781) B295781
theorem B295505 : Blo 195805 295505 := bstep (se 2 (by rfl) ⟨110814, by rfl⟩ : syracuseStep 295505 = 221629) B221629
theorem B197203 : Blo 195805 197203 := bstep (se 1 (by rfl) ⟨147902, by rfl⟩ : syracuseStep 197203 = 295805) B295805
theorem B295523 : Blo 195805 295523 := bstep (se 1 (by rfl) ⟨221642, by rfl⟩ : syracuseStep 295523 = 443285) B443285
theorem B197219 : Blo 195805 197219 := bstep (se 1 (by rfl) ⟨147914, by rfl⟩ : syracuseStep 197219 = 295829) B295829
theorem B197235 : Blo 195805 197235 := bstep (se 1 (by rfl) ⟨147926, by rfl⟩ : syracuseStep 197235 = 295853) B295853
theorem B295553 : Blo 195805 295553 := bstep (se 2 (by rfl) ⟨110832, by rfl⟩ : syracuseStep 295553 = 221665) B221665
theorem B197251 : Blo 195805 197251 := bstep (se 1 (by rfl) ⟨147938, by rfl⟩ : syracuseStep 197251 = 295877) B295877
theorem B295571 : Blo 195805 295571 := bstep (se 1 (by rfl) ⟨221678, by rfl⟩ : syracuseStep 295571 = 443357) B443357
theorem B197267 : Blo 195805 197267 := bstep (se 1 (by rfl) ⟨147950, by rfl⟩ : syracuseStep 197267 = 295901) B295901
theorem B197283 : Blo 195805 197283 := bstep (se 1 (by rfl) ⟨147962, by rfl⟩ : syracuseStep 197283 = 295925) B295925
theorem B295601 : Blo 195805 295601 := bstep (se 2 (by rfl) ⟨110850, by rfl⟩ : syracuseStep 295601 = 221701) B221701
theorem B197299 : Blo 195805 197299 := bstep (se 1 (by rfl) ⟨147974, by rfl⟩ : syracuseStep 197299 = 295949) B295949
theorem B295619 : Blo 195805 295619 := bstep (se 1 (by rfl) ⟨221714, by rfl⟩ : syracuseStep 295619 = 443429) B443429
theorem B197315 : Blo 195805 197315 := bstep (se 1 (by rfl) ⟨147986, by rfl⟩ : syracuseStep 197315 = 295973) B295973
theorem B197331 : Blo 195805 197331 := bstep (se 1 (by rfl) ⟨147998, by rfl⟩ : syracuseStep 197331 = 295997) B295997
theorem B295649 : Blo 195805 295649 := bstep (se 2 (by rfl) ⟨110868, by rfl⟩ : syracuseStep 295649 = 221737) B221737
theorem B197347 : Blo 195805 197347 := bstep (se 1 (by rfl) ⟨148010, by rfl⟩ : syracuseStep 197347 = 296021) B296021
theorem B295667 : Blo 195805 295667 := bstep (se 1 (by rfl) ⟨221750, by rfl⟩ : syracuseStep 295667 = 443501) B443501
theorem B197363 : Blo 195805 197363 := bstep (se 1 (by rfl) ⟨148022, by rfl⟩ : syracuseStep 197363 = 296045) B296045
theorem B197379 : Blo 195805 197379 := bstep (se 1 (by rfl) ⟨148034, by rfl⟩ : syracuseStep 197379 = 296069) B296069
theorem B295697 : Blo 195805 295697 := bstep (se 2 (by rfl) ⟨110886, by rfl⟩ : syracuseStep 295697 = 221773) B221773
theorem B197395 : Blo 195805 197395 := bstep (se 1 (by rfl) ⟨148046, by rfl⟩ : syracuseStep 197395 = 296093) B296093
theorem B295715 : Blo 195805 295715 := bstep (se 1 (by rfl) ⟨221786, by rfl⟩ : syracuseStep 295715 = 443573) B443573
theorem B197411 : Blo 195805 197411 := bstep (se 1 (by rfl) ⟨148058, by rfl⟩ : syracuseStep 197411 = 296117) B296117
theorem B197427 : Blo 195805 197427 := bstep (se 1 (by rfl) ⟨148070, by rfl⟩ : syracuseStep 197427 = 296141) B296141
theorem B295745 : Blo 195805 295745 := bstep (se 2 (by rfl) ⟨110904, by rfl⟩ : syracuseStep 295745 = 221809) B221809
theorem B557891 : Blo 195805 557891 := bstep (se 1 (by rfl) ⟨418418, by rfl⟩ : syracuseStep 557891 = 836837) B836837
theorem B197443 : Blo 195805 197443 := bstep (se 1 (by rfl) ⟨148082, by rfl⟩ : syracuseStep 197443 = 296165) B296165
theorem B295763 : Blo 195805 295763 := bstep (se 1 (by rfl) ⟨221822, by rfl⟩ : syracuseStep 295763 = 443645) B443645
theorem B197459 : Blo 195805 197459 := bstep (se 1 (by rfl) ⟨148094, by rfl⟩ : syracuseStep 197459 = 296189) B296189
theorem B197475 : Blo 195805 197475 := bstep (se 1 (by rfl) ⟨148106, by rfl⟩ : syracuseStep 197475 = 296213) B296213
theorem B1016675 : Blo 195805 1016675 := bstep (se 1 (by rfl) ⟨762506, by rfl⟩ : syracuseStep 1016675 = 1525013) B1525013
theorem B295793 : Blo 195805 295793 := bstep (se 2 (by rfl) ⟨110922, by rfl⟩ : syracuseStep 295793 = 221845) B221845
theorem B197491 : Blo 195805 197491 := bstep (se 1 (by rfl) ⟨148118, by rfl⟩ : syracuseStep 197491 = 296237) B296237
theorem B295811 : Blo 195805 295811 := bstep (se 1 (by rfl) ⟨221858, by rfl⟩ : syracuseStep 295811 = 443717) B443717
theorem B197507 : Blo 195805 197507 := bstep (se 1 (by rfl) ⟨148130, by rfl⟩ : syracuseStep 197507 = 296261) B296261
theorem B295825 : Blo 195805 295825 := bstep (se 2 (by rfl) ⟨110934, by rfl⟩ : syracuseStep 295825 = 221869) B221869
theorem B197523 : Blo 195805 197523 := bstep (se 1 (by rfl) ⟨148142, by rfl⟩ : syracuseStep 197523 = 296285) B296285
theorem B295841 : Blo 195805 295841 := bstep (se 2 (by rfl) ⟨110940, by rfl⟩ : syracuseStep 295841 = 221881) B221881
theorem B197539 : Blo 195805 197539 := bstep (se 1 (by rfl) ⟨148154, by rfl⟩ : syracuseStep 197539 = 296309) B296309
theorem B295859 : Blo 195805 295859 := bstep (se 1 (by rfl) ⟨221894, by rfl⟩ : syracuseStep 295859 = 443789) B443789
theorem B197555 : Blo 195805 197555 := bstep (se 1 (by rfl) ⟨148166, by rfl⟩ : syracuseStep 197555 = 296333) B296333
theorem B197571 : Blo 195805 197571 := bstep (se 1 (by rfl) ⟨148178, by rfl⟩ : syracuseStep 197571 = 296357) B296357
theorem B295889 : Blo 195805 295889 := bstep (se 2 (by rfl) ⟨110958, by rfl⟩ : syracuseStep 295889 = 221917) B221917
theorem B197587 : Blo 195805 197587 := bstep (se 1 (by rfl) ⟨148190, by rfl⟩ : syracuseStep 197587 = 296381) B296381
theorem B295907 : Blo 195805 295907 := bstep (se 1 (by rfl) ⟨221930, by rfl⟩ : syracuseStep 295907 = 443861) B443861
theorem B197603 : Blo 195805 197603 := bstep (se 1 (by rfl) ⟨148202, by rfl⟩ : syracuseStep 197603 = 296405) B296405
theorem B197619 : Blo 195805 197619 := bstep (se 1 (by rfl) ⟨148214, by rfl⟩ : syracuseStep 197619 = 296429) B296429
theorem B295937 : Blo 195805 295937 := bstep (se 2 (by rfl) ⟨110976, by rfl⟩ : syracuseStep 295937 = 221953) B221953
theorem B197635 : Blo 195805 197635 := bstep (se 1 (by rfl) ⟨148226, by rfl⟩ : syracuseStep 197635 = 296453) B296453
theorem B295955 : Blo 195805 295955 := bstep (se 1 (by rfl) ⟨221966, by rfl⟩ : syracuseStep 295955 = 443933) B443933
theorem B197651 : Blo 195805 197651 := bstep (se 1 (by rfl) ⟨148238, by rfl⟩ : syracuseStep 197651 = 296477) B296477
theorem B197667 : Blo 195805 197667 := bstep (se 1 (by rfl) ⟨148250, by rfl⟩ : syracuseStep 197667 = 296501) B296501
theorem B295985 : Blo 195805 295985 := bstep (se 2 (by rfl) ⟨110994, by rfl⟩ : syracuseStep 295985 = 221989) B221989
theorem B197683 : Blo 195805 197683 := bstep (se 1 (by rfl) ⟨148262, by rfl⟩ : syracuseStep 197683 = 296525) B296525
theorem B296003 : Blo 195805 296003 := bstep (se 1 (by rfl) ⟨222002, by rfl⟩ : syracuseStep 296003 = 444005) B444005
theorem B197699 : Blo 195805 197699 := bstep (se 1 (by rfl) ⟨148274, by rfl⟩ : syracuseStep 197699 = 296549) B296549
theorem B197715 : Blo 195805 197715 := bstep (se 1 (by rfl) ⟨148286, by rfl⟩ : syracuseStep 197715 = 296573) B296573
theorem B296033 : Blo 195805 296033 := bstep (se 2 (by rfl) ⟨111012, by rfl⟩ : syracuseStep 296033 = 222025) B222025
theorem B197731 : Blo 195805 197731 := bstep (se 1 (by rfl) ⟨148298, by rfl⟩ : syracuseStep 197731 = 296597) B296597
theorem B296051 : Blo 195805 296051 := bstep (se 1 (by rfl) ⟨222038, by rfl⟩ : syracuseStep 296051 = 444077) B444077
theorem B197747 : Blo 195805 197747 := bstep (se 1 (by rfl) ⟨148310, by rfl⟩ : syracuseStep 197747 = 296621) B296621
theorem B197763 : Blo 195805 197763 := bstep (se 1 (by rfl) ⟨148322, by rfl⟩ : syracuseStep 197763 = 296645) B296645
theorem B296081 : Blo 195805 296081 := bstep (se 2 (by rfl) ⟨111030, by rfl⟩ : syracuseStep 296081 = 222061) B222061
theorem B197779 : Blo 195805 197779 := bstep (se 1 (by rfl) ⟨148334, by rfl⟩ : syracuseStep 197779 = 296669) B296669
theorem B296099 : Blo 195805 296099 := bstep (se 1 (by rfl) ⟨222074, by rfl⟩ : syracuseStep 296099 = 444149) B444149
theorem B197795 : Blo 195805 197795 := bstep (se 1 (by rfl) ⟨148346, by rfl⟩ : syracuseStep 197795 = 296693) B296693
theorem B754865 : Blo 195805 754865 := bstep (se 2 (by rfl) ⟨283074, by rfl⟩ : syracuseStep 754865 = 566149) B566149
theorem B197811 : Blo 195805 197811 := bstep (se 1 (by rfl) ⟨148358, by rfl⟩ : syracuseStep 197811 = 296717) B296717
theorem B296129 : Blo 195805 296129 := bstep (se 2 (by rfl) ⟨111048, by rfl⟩ : syracuseStep 296129 = 222097) B222097
theorem B197827 : Blo 195805 197827 := bstep (se 1 (by rfl) ⟨148370, by rfl⟩ : syracuseStep 197827 = 296741) B296741
theorem B296147 : Blo 195805 296147 := bstep (se 1 (by rfl) ⟨222110, by rfl⟩ : syracuseStep 296147 = 444221) B444221
theorem B197843 : Blo 195805 197843 := bstep (se 1 (by rfl) ⟨148382, by rfl⟩ : syracuseStep 197843 = 296765) B296765
theorem B197859 : Blo 195805 197859 := bstep (se 1 (by rfl) ⟨148394, by rfl⟩ : syracuseStep 197859 = 296789) B296789
theorem B296177 : Blo 195805 296177 := bstep (se 2 (by rfl) ⟨111066, by rfl⟩ : syracuseStep 296177 = 222133) B222133
theorem B197875 : Blo 195805 197875 := bstep (se 1 (by rfl) ⟨148406, by rfl⟩ : syracuseStep 197875 = 296813) B296813
theorem B296195 : Blo 195805 296195 := bstep (se 1 (by rfl) ⟨222146, by rfl⟩ : syracuseStep 296195 = 444293) B444293
theorem B197891 : Blo 195805 197891 := bstep (se 1 (by rfl) ⟨148418, by rfl⟩ : syracuseStep 197891 = 296837) B296837
theorem B197907 : Blo 195805 197907 := bstep (se 1 (by rfl) ⟨148430, by rfl⟩ : syracuseStep 197907 = 296861) B296861
theorem B296225 : Blo 195805 296225 := bstep (se 2 (by rfl) ⟨111084, by rfl⟩ : syracuseStep 296225 = 222169) B222169
theorem B197923 : Blo 195805 197923 := bstep (se 1 (by rfl) ⟨148442, by rfl⟩ : syracuseStep 197923 = 296885) B296885
theorem B296243 : Blo 195805 296243 := bstep (se 1 (by rfl) ⟨222182, by rfl⟩ : syracuseStep 296243 = 444365) B444365
theorem B197939 : Blo 195805 197939 := bstep (se 1 (by rfl) ⟨148454, by rfl⟩ : syracuseStep 197939 = 296909) B296909
theorem B197955 : Blo 195805 197955 := bstep (se 1 (by rfl) ⟨148466, by rfl⟩ : syracuseStep 197955 = 296933) B296933
theorem B853325 : Blo 195805 853325 := bstep (se 3 (by rfl) ⟨159998, by rfl⟩ : syracuseStep 853325 = 319997) B319997
theorem B296273 : Blo 195805 296273 := bstep (se 2 (by rfl) ⟨111102, by rfl⟩ : syracuseStep 296273 = 222205) B222205
theorem B197971 : Blo 195805 197971 := bstep (se 1 (by rfl) ⟨148478, by rfl⟩ : syracuseStep 197971 = 296957) B296957
theorem B296291 : Blo 195805 296291 := bstep (se 1 (by rfl) ⟨222218, by rfl⟩ : syracuseStep 296291 = 444437) B444437
theorem B197987 : Blo 195805 197987 := bstep (se 1 (by rfl) ⟨148490, by rfl⟩ : syracuseStep 197987 = 296981) B296981
theorem B198003 : Blo 195805 198003 := bstep (se 1 (by rfl) ⟨148502, by rfl⟩ : syracuseStep 198003 = 297005) B297005
theorem B296321 : Blo 195805 296321 := bstep (se 2 (by rfl) ⟨111120, by rfl⟩ : syracuseStep 296321 = 222241) B222241
theorem B198019 : Blo 195805 198019 := bstep (se 1 (by rfl) ⟨148514, by rfl⟩ : syracuseStep 198019 = 297029) B297029
theorem B296339 : Blo 195805 296339 := bstep (se 1 (by rfl) ⟨222254, by rfl⟩ : syracuseStep 296339 = 444509) B444509
theorem B198035 : Blo 195805 198035 := bstep (se 1 (by rfl) ⟨148526, by rfl⟩ : syracuseStep 198035 = 297053) B297053
theorem B198051 : Blo 195805 198051 := bstep (se 1 (by rfl) ⟨148538, by rfl⟩ : syracuseStep 198051 = 297077) B297077
theorem B296369 : Blo 195805 296369 := bstep (se 2 (by rfl) ⟨111138, by rfl⟩ : syracuseStep 296369 = 222277) B222277
theorem B198067 : Blo 195805 198067 := bstep (se 1 (by rfl) ⟨148550, by rfl⟩ : syracuseStep 198067 = 297101) B297101
theorem B296387 : Blo 195805 296387 := bstep (se 1 (by rfl) ⟨222290, by rfl⟩ : syracuseStep 296387 = 444581) B444581
theorem B198083 : Blo 195805 198083 := bstep (se 1 (by rfl) ⟨148562, by rfl⟩ : syracuseStep 198083 = 297125) B297125
theorem B198099 : Blo 195805 198099 := bstep (se 1 (by rfl) ⟨148574, by rfl⟩ : syracuseStep 198099 = 297149) B297149
theorem B296417 : Blo 195805 296417 := bstep (se 2 (by rfl) ⟨111156, by rfl⟩ : syracuseStep 296417 = 222313) B222313
theorem B198115 : Blo 195805 198115 := bstep (se 1 (by rfl) ⟨148586, by rfl⟩ : syracuseStep 198115 = 297173) B297173
theorem B296435 : Blo 195805 296435 := bstep (se 1 (by rfl) ⟨222326, by rfl⟩ : syracuseStep 296435 = 444653) B444653
theorem B198131 : Blo 195805 198131 := bstep (se 1 (by rfl) ⟨148598, by rfl⟩ : syracuseStep 198131 = 297197) B297197
theorem B198147 : Blo 195805 198147 := bstep (se 1 (by rfl) ⟨148610, by rfl⟩ : syracuseStep 198147 = 297221) B297221
theorem B296465 : Blo 195805 296465 := bstep (se 2 (by rfl) ⟨111174, by rfl⟩ : syracuseStep 296465 = 222349) B222349
theorem B198163 : Blo 195805 198163 := bstep (se 1 (by rfl) ⟨148622, by rfl⟩ : syracuseStep 198163 = 297245) B297245
theorem B296483 : Blo 195805 296483 := bstep (se 1 (by rfl) ⟨222362, by rfl⟩ : syracuseStep 296483 = 444725) B444725
theorem B198179 : Blo 195805 198179 := bstep (se 1 (by rfl) ⟨148634, by rfl⟩ : syracuseStep 198179 = 297269) B297269
theorem B198195 : Blo 195805 198195 := bstep (se 1 (by rfl) ⟨148646, by rfl⟩ : syracuseStep 198195 = 297293) B297293
theorem B296513 : Blo 195805 296513 := bstep (se 2 (by rfl) ⟨111192, by rfl⟩ : syracuseStep 296513 = 222385) B222385
theorem B198211 : Blo 195805 198211 := bstep (se 1 (by rfl) ⟨148658, by rfl⟩ : syracuseStep 198211 = 297317) B297317
theorem B296531 : Blo 195805 296531 := bstep (se 1 (by rfl) ⟨222398, by rfl⟩ : syracuseStep 296531 = 444797) B444797
theorem B198227 : Blo 195805 198227 := bstep (se 1 (by rfl) ⟨148670, by rfl⟩ : syracuseStep 198227 = 297341) B297341
theorem B198243 : Blo 195805 198243 := bstep (se 1 (by rfl) ⟨148682, by rfl⟩ : syracuseStep 198243 = 297365) B297365
theorem B296561 : Blo 195805 296561 := bstep (se 2 (by rfl) ⟨111210, by rfl⟩ : syracuseStep 296561 = 222421) B222421
theorem B1279601 : Blo 195805 1279601 := bstep (se 2 (by rfl) ⟨479850, by rfl⟩ : syracuseStep 1279601 = 959701) B959701
theorem B198259 : Blo 195805 198259 := bstep (se 1 (by rfl) ⟨148694, by rfl⟩ : syracuseStep 198259 = 297389) B297389
theorem B296579 : Blo 195805 296579 := bstep (se 1 (by rfl) ⟨222434, by rfl⟩ : syracuseStep 296579 = 444869) B444869
theorem B198275 : Blo 195805 198275 := bstep (se 1 (by rfl) ⟨148706, by rfl⟩ : syracuseStep 198275 = 297413) B297413
theorem B558733 : Blo 195805 558733 := bstep (se 3 (by rfl) ⟨104762, by rfl⟩ : syracuseStep 558733 = 209525) B209525
theorem B198291 : Blo 195805 198291 := bstep (se 1 (by rfl) ⟨148718, by rfl⟩ : syracuseStep 198291 = 297437) B297437
theorem B296609 : Blo 195805 296609 := bstep (se 2 (by rfl) ⟨111228, by rfl⟩ : syracuseStep 296609 = 222457) B222457
theorem B198307 : Blo 195805 198307 := bstep (se 1 (by rfl) ⟨148730, by rfl⟩ : syracuseStep 198307 = 297461) B297461
theorem B296627 : Blo 195805 296627 := bstep (se 1 (by rfl) ⟨222470, by rfl⟩ : syracuseStep 296627 = 444941) B444941
theorem B198323 : Blo 195805 198323 := bstep (se 1 (by rfl) ⟨148742, by rfl⟩ : syracuseStep 198323 = 297485) B297485
theorem B198339 : Blo 195805 198339 := bstep (se 1 (by rfl) ⟨148754, by rfl⟩ : syracuseStep 198339 = 297509) B297509
theorem B952013 : Blo 195805 952013 := bstep (se 3 (by rfl) ⟨178502, by rfl⟩ : syracuseStep 952013 = 357005) B357005
theorem B296657 : Blo 195805 296657 := bstep (se 2 (by rfl) ⟨111246, by rfl⟩ : syracuseStep 296657 = 222493) B222493
theorem B198355 : Blo 195805 198355 := bstep (se 1 (by rfl) ⟨148766, by rfl⟩ : syracuseStep 198355 = 297533) B297533
theorem B296675 : Blo 195805 296675 := bstep (se 1 (by rfl) ⟨222506, by rfl⟩ : syracuseStep 296675 = 445013) B445013
theorem B198371 : Blo 195805 198371 := bstep (se 1 (by rfl) ⟨148778, by rfl⟩ : syracuseStep 198371 = 297557) B297557
theorem B198387 : Blo 195805 198387 := bstep (se 1 (by rfl) ⟨148790, by rfl⟩ : syracuseStep 198387 = 297581) B297581
theorem B296705 : Blo 195805 296705 := bstep (se 2 (by rfl) ⟨111264, by rfl⟩ : syracuseStep 296705 = 222529) B222529
theorem B198403 : Blo 195805 198403 := bstep (se 1 (by rfl) ⟨148802, by rfl⟩ : syracuseStep 198403 = 297605) B297605
theorem B296723 : Blo 195805 296723 := bstep (se 1 (by rfl) ⟨222542, by rfl⟩ : syracuseStep 296723 = 445085) B445085
theorem B198419 : Blo 195805 198419 := bstep (se 1 (by rfl) ⟨148814, by rfl⟩ : syracuseStep 198419 = 297629) B297629
theorem B198435 : Blo 195805 198435 := bstep (se 1 (by rfl) ⟨148826, by rfl⟩ : syracuseStep 198435 = 297653) B297653
theorem B558893 : Blo 195805 558893 := bstep (se 3 (by rfl) ⟨104792, by rfl⟩ : syracuseStep 558893 = 209585) B209585
theorem B296753 : Blo 195805 296753 := bstep (se 2 (by rfl) ⟨111282, by rfl⟩ : syracuseStep 296753 = 222565) B222565
theorem B198451 : Blo 195805 198451 := bstep (se 1 (by rfl) ⟨148838, by rfl⟩ : syracuseStep 198451 = 297677) B297677
theorem B296771 : Blo 195805 296771 := bstep (se 1 (by rfl) ⟨222578, by rfl⟩ : syracuseStep 296771 = 445157) B445157
theorem B198467 : Blo 195805 198467 := bstep (se 1 (by rfl) ⟨148850, by rfl⟩ : syracuseStep 198467 = 297701) B297701
theorem B198483 : Blo 195805 198483 := bstep (se 1 (by rfl) ⟨148862, by rfl⟩ : syracuseStep 198483 = 297725) B297725
theorem B296801 : Blo 195805 296801 := bstep (se 2 (by rfl) ⟨111300, by rfl⟩ : syracuseStep 296801 = 222601) B222601
theorem B198499 : Blo 195805 198499 := bstep (se 1 (by rfl) ⟨148874, by rfl⟩ : syracuseStep 198499 = 297749) B297749
theorem B296819 : Blo 195805 296819 := bstep (se 1 (by rfl) ⟨222614, by rfl⟩ : syracuseStep 296819 = 445229) B445229
theorem B198515 : Blo 195805 198515 := bstep (se 1 (by rfl) ⟨148886, by rfl⟩ : syracuseStep 198515 = 297773) B297773
theorem B198531 : Blo 195805 198531 := bstep (se 1 (by rfl) ⟨148898, by rfl⟩ : syracuseStep 198531 = 297797) B297797
theorem B296849 : Blo 195805 296849 := bstep (se 2 (by rfl) ⟨111318, by rfl⟩ : syracuseStep 296849 = 222637) B222637
theorem B198547 : Blo 195805 198547 := bstep (se 1 (by rfl) ⟨148910, by rfl⟩ : syracuseStep 198547 = 297821) B297821
theorem B296867 : Blo 195805 296867 := bstep (se 1 (by rfl) ⟨222650, by rfl⟩ : syracuseStep 296867 = 445301) B445301
theorem B198563 : Blo 195805 198563 := bstep (se 1 (by rfl) ⟨148922, by rfl⟩ : syracuseStep 198563 = 297845) B297845
theorem B198579 : Blo 195805 198579 := bstep (se 1 (by rfl) ⟨148934, by rfl⟩ : syracuseStep 198579 = 297869) B297869
theorem B296897 : Blo 195805 296897 := bstep (se 2 (by rfl) ⟨111336, by rfl⟩ : syracuseStep 296897 = 222673) B222673
theorem B198595 : Blo 195805 198595 := bstep (se 1 (by rfl) ⟨148946, by rfl⟩ : syracuseStep 198595 = 297893) B297893
theorem B296915 : Blo 195805 296915 := bstep (se 1 (by rfl) ⟨222686, by rfl⟩ : syracuseStep 296915 = 445373) B445373
theorem B198611 : Blo 195805 198611 := bstep (se 1 (by rfl) ⟨148958, by rfl⟩ : syracuseStep 198611 = 297917) B297917
theorem B559075 : Blo 195805 559075 := bstep (se 1 (by rfl) ⟨419306, by rfl⟩ : syracuseStep 559075 = 838613) B838613
theorem B198627 : Blo 195805 198627 := bstep (se 1 (by rfl) ⟨148970, by rfl⟩ : syracuseStep 198627 = 297941) B297941
theorem B296945 : Blo 195805 296945 := bstep (se 2 (by rfl) ⟨111354, by rfl⟩ : syracuseStep 296945 = 222709) B222709
theorem B198643 : Blo 195805 198643 := bstep (se 1 (by rfl) ⟨148982, by rfl⟩ : syracuseStep 198643 = 297965) B297965
theorem B296963 : Blo 195805 296963 := bstep (se 1 (by rfl) ⟨222722, by rfl⟩ : syracuseStep 296963 = 445445) B445445
theorem B198659 : Blo 195805 198659 := bstep (se 1 (by rfl) ⟨148994, by rfl⟩ : syracuseStep 198659 = 297989) B297989
theorem B198675 : Blo 195805 198675 := bstep (se 1 (by rfl) ⟨149006, by rfl⟩ : syracuseStep 198675 = 298013) B298013
theorem B296993 : Blo 195805 296993 := bstep (se 2 (by rfl) ⟨111372, by rfl⟩ : syracuseStep 296993 = 222745) B222745
theorem B198691 : Blo 195805 198691 := bstep (se 1 (by rfl) ⟨149018, by rfl⟩ : syracuseStep 198691 = 298037) B298037
theorem B297011 : Blo 195805 297011 := bstep (se 1 (by rfl) ⟨222758, by rfl⟩ : syracuseStep 297011 = 445517) B445517
theorem B198707 : Blo 195805 198707 := bstep (se 1 (by rfl) ⟨149030, by rfl⟩ : syracuseStep 198707 = 298061) B298061
theorem B198723 : Blo 195805 198723 := bstep (se 1 (by rfl) ⟨149042, by rfl⟩ : syracuseStep 198723 = 298085) B298085
theorem B297041 : Blo 195805 297041 := bstep (se 2 (by rfl) ⟨111390, by rfl⟩ : syracuseStep 297041 = 222781) B222781
theorem B198739 : Blo 195805 198739 := bstep (se 1 (by rfl) ⟨149054, by rfl⟩ : syracuseStep 198739 = 298109) B298109
theorem B297059 : Blo 195805 297059 := bstep (se 1 (by rfl) ⟨222794, by rfl⟩ : syracuseStep 297059 = 445589) B445589
theorem B198755 : Blo 195805 198755 := bstep (se 1 (by rfl) ⟨149066, by rfl⟩ : syracuseStep 198755 = 298133) B298133
theorem B198771 : Blo 195805 198771 := bstep (se 1 (by rfl) ⟨149078, by rfl⟩ : syracuseStep 198771 = 298157) B298157
theorem B297089 : Blo 195805 297089 := bstep (se 2 (by rfl) ⟨111408, by rfl⟩ : syracuseStep 297089 = 222817) B222817
theorem B198787 : Blo 195805 198787 := bstep (se 1 (by rfl) ⟨149090, by rfl⟩ : syracuseStep 198787 = 298181) B298181
theorem B297107 : Blo 195805 297107 := bstep (se 1 (by rfl) ⟨222830, by rfl⟩ : syracuseStep 297107 = 445661) B445661
theorem B198803 : Blo 195805 198803 := bstep (se 1 (by rfl) ⟨149102, by rfl⟩ : syracuseStep 198803 = 298205) B298205
theorem B198819 : Blo 195805 198819 := bstep (se 1 (by rfl) ⟨149114, by rfl⟩ : syracuseStep 198819 = 298229) B298229
theorem B297137 : Blo 195805 297137 := bstep (se 2 (by rfl) ⟨111426, by rfl⟩ : syracuseStep 297137 = 222853) B222853
theorem B198835 : Blo 195805 198835 := bstep (se 1 (by rfl) ⟨149126, by rfl⟩ : syracuseStep 198835 = 298253) B298253
theorem B297155 : Blo 195805 297155 := bstep (se 1 (by rfl) ⟨222866, by rfl⟩ : syracuseStep 297155 = 445733) B445733
theorem B198851 : Blo 195805 198851 := bstep (se 1 (by rfl) ⟨149138, by rfl⟩ : syracuseStep 198851 = 298277) B298277
theorem B198867 : Blo 195805 198867 := bstep (se 1 (by rfl) ⟨149150, by rfl⟩ : syracuseStep 198867 = 298301) B298301
theorem B297185 : Blo 195805 297185 := bstep (se 2 (by rfl) ⟨111444, by rfl⟩ : syracuseStep 297185 = 222889) B222889
theorem B198883 : Blo 195805 198883 := bstep (se 1 (by rfl) ⟨149162, by rfl⟩ : syracuseStep 198883 = 298325) B298325
theorem B297203 : Blo 195805 297203 := bstep (se 1 (by rfl) ⟨222902, by rfl⟩ : syracuseStep 297203 = 445805) B445805
theorem B198899 : Blo 195805 198899 := bstep (se 1 (by rfl) ⟨149174, by rfl⟩ : syracuseStep 198899 = 298349) B298349
theorem B198915 : Blo 195805 198915 := bstep (se 1 (by rfl) ⟨149186, by rfl⟩ : syracuseStep 198915 = 298373) B298373
theorem B297233 : Blo 195805 297233 := bstep (se 2 (by rfl) ⟨111462, by rfl⟩ : syracuseStep 297233 = 222925) B222925
theorem B198931 : Blo 195805 198931 := bstep (se 1 (by rfl) ⟨149198, by rfl⟩ : syracuseStep 198931 = 298397) B298397
theorem B297251 : Blo 195805 297251 := bstep (se 1 (by rfl) ⟨222938, by rfl⟩ : syracuseStep 297251 = 445877) B445877
theorem B198947 : Blo 195805 198947 := bstep (se 1 (by rfl) ⟨149210, by rfl⟩ : syracuseStep 198947 = 298421) B298421
theorem B198963 : Blo 195805 198963 := bstep (se 1 (by rfl) ⟨149222, by rfl⟩ : syracuseStep 198963 = 298445) B298445
theorem B297281 : Blo 195805 297281 := bstep (se 2 (by rfl) ⟨111480, by rfl⟩ : syracuseStep 297281 = 222961) B222961
theorem B198979 : Blo 195805 198979 := bstep (se 1 (by rfl) ⟨149234, by rfl⟩ : syracuseStep 198979 = 298469) B298469
theorem B297299 : Blo 195805 297299 := bstep (se 1 (by rfl) ⟨222974, by rfl⟩ : syracuseStep 297299 = 445949) B445949
theorem B198995 : Blo 195805 198995 := bstep (se 1 (by rfl) ⟨149246, by rfl⟩ : syracuseStep 198995 = 298493) B298493
theorem B199011 : Blo 195805 199011 := bstep (se 1 (by rfl) ⟨149258, by rfl⟩ : syracuseStep 199011 = 298517) B298517
theorem B297329 : Blo 195805 297329 := bstep (se 2 (by rfl) ⟨111498, by rfl⟩ : syracuseStep 297329 = 222997) B222997
theorem B199027 : Blo 195805 199027 := bstep (se 1 (by rfl) ⟨149270, by rfl⟩ : syracuseStep 199027 = 298541) B298541
theorem B297347 : Blo 195805 297347 := bstep (se 1 (by rfl) ⟨223010, by rfl⟩ : syracuseStep 297347 = 446021) B446021
theorem B199043 : Blo 195805 199043 := bstep (se 1 (by rfl) ⟨149282, by rfl⟩ : syracuseStep 199043 = 298565) B298565
theorem B199059 : Blo 195805 199059 := bstep (se 1 (by rfl) ⟨149294, by rfl⟩ : syracuseStep 199059 = 298589) B298589
theorem B297377 : Blo 195805 297377 := bstep (se 2 (by rfl) ⟨111516, by rfl⟩ : syracuseStep 297377 = 223033) B223033
theorem B199075 : Blo 195805 199075 := bstep (se 1 (by rfl) ⟨149306, by rfl⟩ : syracuseStep 199075 = 298613) B298613
theorem B297395 : Blo 195805 297395 := bstep (se 1 (by rfl) ⟨223046, by rfl⟩ : syracuseStep 297395 = 446093) B446093
theorem B199091 : Blo 195805 199091 := bstep (se 1 (by rfl) ⟨149318, by rfl⟩ : syracuseStep 199091 = 298637) B298637
theorem B199107 : Blo 195805 199107 := bstep (se 1 (by rfl) ⟨149330, by rfl⟩ : syracuseStep 199107 = 298661) B298661
theorem B297425 : Blo 195805 297425 := bstep (se 2 (by rfl) ⟨111534, by rfl⟩ : syracuseStep 297425 = 223069) B223069
theorem B199123 : Blo 195805 199123 := bstep (se 1 (by rfl) ⟨149342, by rfl⟩ : syracuseStep 199123 = 298685) B298685
theorem B297443 : Blo 195805 297443 := bstep (se 1 (by rfl) ⟨223082, by rfl⟩ : syracuseStep 297443 = 446165) B446165
theorem B199139 : Blo 195805 199139 := bstep (se 1 (by rfl) ⟨149354, by rfl⟩ : syracuseStep 199139 = 298709) B298709
theorem B199155 : Blo 195805 199155 := bstep (se 1 (by rfl) ⟨149366, by rfl⟩ : syracuseStep 199155 = 298733) B298733
theorem B297473 : Blo 195805 297473 := bstep (se 2 (by rfl) ⟨111552, by rfl⟩ : syracuseStep 297473 = 223105) B223105
theorem B199171 : Blo 195805 199171 := bstep (se 1 (by rfl) ⟨149378, by rfl⟩ : syracuseStep 199171 = 298757) B298757
theorem B297491 : Blo 195805 297491 := bstep (se 1 (by rfl) ⟨223118, by rfl⟩ : syracuseStep 297491 = 446237) B446237
theorem B199187 : Blo 195805 199187 := bstep (se 1 (by rfl) ⟨149390, by rfl⟩ : syracuseStep 199187 = 298781) B298781
theorem B199203 : Blo 195805 199203 := bstep (se 1 (by rfl) ⟨149402, by rfl⟩ : syracuseStep 199203 = 298805) B298805
theorem B297521 : Blo 195805 297521 := bstep (se 2 (by rfl) ⟨111570, by rfl⟩ : syracuseStep 297521 = 223141) B223141
theorem B199219 : Blo 195805 199219 := bstep (se 1 (by rfl) ⟨149414, by rfl⟩ : syracuseStep 199219 = 298829) B298829
theorem B297539 : Blo 195805 297539 := bstep (se 1 (by rfl) ⟨223154, by rfl⟩ : syracuseStep 297539 = 446309) B446309
theorem B199235 : Blo 195805 199235 := bstep (se 1 (by rfl) ⟨149426, by rfl⟩ : syracuseStep 199235 = 298853) B298853
theorem B199251 : Blo 195805 199251 := bstep (se 1 (by rfl) ⟨149438, by rfl⟩ : syracuseStep 199251 = 298877) B298877
theorem B297569 : Blo 195805 297569 := bstep (se 2 (by rfl) ⟨111588, by rfl⟩ : syracuseStep 297569 = 223177) B223177
theorem B756323 : Blo 195805 756323 := bstep (se 1 (by rfl) ⟨567242, by rfl⟩ : syracuseStep 756323 = 1134485) B1134485
theorem B199267 : Blo 195805 199267 := bstep (se 1 (by rfl) ⟨149450, by rfl⟩ : syracuseStep 199267 = 298901) B298901
theorem B1510001 : Blo 195805 1510001 := bstep (se 2 (by rfl) ⟨566250, by rfl⟩ : syracuseStep 1510001 = 1132501) B1132501
theorem B756337 : Blo 195805 756337 := bstep (se 2 (by rfl) ⟨283626, by rfl⟩ : syracuseStep 756337 = 567253) B567253
theorem B297587 : Blo 195805 297587 := bstep (se 1 (by rfl) ⟨223190, by rfl⟩ : syracuseStep 297587 = 446381) B446381
theorem B199283 : Blo 195805 199283 := bstep (se 1 (by rfl) ⟨149462, by rfl⟩ : syracuseStep 199283 = 298925) B298925
theorem B199299 : Blo 195805 199299 := bstep (se 1 (by rfl) ⟨149474, by rfl⟩ : syracuseStep 199299 = 298949) B298949
theorem B297617 : Blo 195805 297617 := bstep (se 2 (by rfl) ⟨111606, by rfl⟩ : syracuseStep 297617 = 223213) B223213
theorem B199315 : Blo 195805 199315 := bstep (se 1 (by rfl) ⟨149486, by rfl⟩ : syracuseStep 199315 = 298973) B298973
theorem B297635 : Blo 195805 297635 := bstep (se 1 (by rfl) ⟨223226, by rfl⟩ : syracuseStep 297635 = 446453) B446453
theorem B199331 : Blo 195805 199331 := bstep (se 1 (by rfl) ⟨149498, by rfl⟩ : syracuseStep 199331 = 298997) B298997
theorem B199347 : Blo 195805 199347 := bstep (se 1 (by rfl) ⟨149510, by rfl⟩ : syracuseStep 199347 = 299021) B299021
theorem B297665 : Blo 195805 297665 := bstep (se 2 (by rfl) ⟨111624, by rfl⟩ : syracuseStep 297665 = 223249) B223249
theorem B199363 : Blo 195805 199363 := bstep (se 1 (by rfl) ⟨149522, by rfl⟩ : syracuseStep 199363 = 299045) B299045
theorem B297683 : Blo 195805 297683 := bstep (se 1 (by rfl) ⟨223262, by rfl⟩ : syracuseStep 297683 = 446525) B446525
theorem B199379 : Blo 195805 199379 := bstep (se 1 (by rfl) ⟨149534, by rfl⟩ : syracuseStep 199379 = 299069) B299069
theorem B1018595 : Blo 195805 1018595 := bstep (se 1 (by rfl) ⟨763946, by rfl⟩ : syracuseStep 1018595 = 1527893) B1527893
theorem B199395 : Blo 195805 199395 := bstep (se 1 (by rfl) ⟨149546, by rfl⟩ : syracuseStep 199395 = 299093) B299093
theorem B297713 : Blo 195805 297713 := bstep (se 2 (by rfl) ⟨111642, by rfl⟩ : syracuseStep 297713 = 223285) B223285
theorem B199411 : Blo 195805 199411 := bstep (se 1 (by rfl) ⟨149558, by rfl⟩ : syracuseStep 199411 = 299117) B299117
theorem B297731 : Blo 195805 297731 := bstep (se 1 (by rfl) ⟨223298, by rfl⟩ : syracuseStep 297731 = 446597) B446597
theorem B199427 : Blo 195805 199427 := bstep (se 1 (by rfl) ⟨149570, by rfl⟩ : syracuseStep 199427 = 299141) B299141
theorem B199443 : Blo 195805 199443 := bstep (se 1 (by rfl) ⟨149582, by rfl⟩ : syracuseStep 199443 = 299165) B299165
theorem B297761 : Blo 195805 297761 := bstep (se 2 (by rfl) ⟨111660, by rfl⟩ : syracuseStep 297761 = 223321) B223321
theorem B199459 : Blo 195805 199459 := bstep (se 1 (by rfl) ⟨149594, by rfl⟩ : syracuseStep 199459 = 299189) B299189
theorem B330547 : Blo 195805 330547 := bstep (se 1 (by rfl) ⟨247910, by rfl⟩ : syracuseStep 330547 = 495821) B495821
theorem B297779 : Blo 195805 297779 := bstep (se 1 (by rfl) ⟨223334, by rfl⟩ : syracuseStep 297779 = 446669) B446669
theorem B199475 : Blo 195805 199475 := bstep (se 1 (by rfl) ⟨149606, by rfl⟩ : syracuseStep 199475 = 299213) B299213
theorem B199491 : Blo 195805 199491 := bstep (se 1 (by rfl) ⟨149618, by rfl⟩ : syracuseStep 199491 = 299237) B299237
theorem B297809 : Blo 195805 297809 := bstep (se 2 (by rfl) ⟨111678, by rfl⟩ : syracuseStep 297809 = 223357) B223357
theorem B199507 : Blo 195805 199507 := bstep (se 1 (by rfl) ⟨149630, by rfl⟩ : syracuseStep 199507 = 299261) B299261
theorem B297827 : Blo 195805 297827 := bstep (se 1 (by rfl) ⟨223370, by rfl⟩ : syracuseStep 297827 = 446741) B446741
theorem B199523 : Blo 195805 199523 := bstep (se 1 (by rfl) ⟨149642, by rfl⟩ : syracuseStep 199523 = 299285) B299285
theorem B199539 : Blo 195805 199539 := bstep (se 1 (by rfl) ⟨149654, by rfl⟩ : syracuseStep 199539 = 299309) B299309
theorem B297857 : Blo 195805 297857 := bstep (se 2 (by rfl) ⟨111696, by rfl⟩ : syracuseStep 297857 = 223393) B223393
theorem B199555 : Blo 195805 199555 := bstep (se 1 (by rfl) ⟨149666, by rfl⟩ : syracuseStep 199555 = 299333) B299333
theorem B297875 : Blo 195805 297875 := bstep (se 1 (by rfl) ⟨223406, by rfl⟩ : syracuseStep 297875 = 446813) B446813
theorem B199571 : Blo 195805 199571 := bstep (se 1 (by rfl) ⟨149678, by rfl⟩ : syracuseStep 199571 = 299357) B299357
theorem B199587 : Blo 195805 199587 := bstep (se 1 (by rfl) ⟨149690, by rfl⟩ : syracuseStep 199587 = 299381) B299381
theorem B297905 : Blo 195805 297905 := bstep (se 2 (by rfl) ⟨111714, by rfl⟩ : syracuseStep 297905 = 223429) B223429
theorem B199603 : Blo 195805 199603 := bstep (se 1 (by rfl) ⟨149702, by rfl⟩ : syracuseStep 199603 = 299405) B299405
theorem B330689 : Blo 195805 330689 := bstep (se 2 (by rfl) ⟨124008, by rfl⟩ : syracuseStep 330689 = 248017) B248017
theorem B297923 : Blo 195805 297923 := bstep (se 1 (by rfl) ⟨223442, by rfl⟩ : syracuseStep 297923 = 446885) B446885
theorem B199619 : Blo 195805 199619 := bstep (se 1 (by rfl) ⟨149714, by rfl⟩ : syracuseStep 199619 = 299429) B299429
theorem B199635 : Blo 195805 199635 := bstep (se 1 (by rfl) ⟨149726, by rfl⟩ : syracuseStep 199635 = 299453) B299453
theorem B297953 : Blo 195805 297953 := bstep (se 2 (by rfl) ⟨111732, by rfl⟩ : syracuseStep 297953 = 223465) B223465
theorem B199651 : Blo 195805 199651 := bstep (se 1 (by rfl) ⟨149738, by rfl⟩ : syracuseStep 199651 = 299477) B299477
theorem B297971 : Blo 195805 297971 := bstep (se 1 (by rfl) ⟨223478, by rfl⟩ : syracuseStep 297971 = 446957) B446957
theorem B199667 : Blo 195805 199667 := bstep (se 1 (by rfl) ⟨149750, by rfl⟩ : syracuseStep 199667 = 299501) B299501
theorem B199683 : Blo 195805 199683 := bstep (se 1 (by rfl) ⟨149762, by rfl⟩ : syracuseStep 199683 = 299525) B299525
theorem B298001 : Blo 195805 298001 := bstep (se 2 (by rfl) ⟨111750, by rfl⟩ : syracuseStep 298001 = 223501) B223501
theorem B199699 : Blo 195805 199699 := bstep (se 1 (by rfl) ⟨149774, by rfl⟩ : syracuseStep 199699 = 299549) B299549
theorem B1281059 : Blo 195805 1281059 := bstep (se 1 (by rfl) ⟨960794, by rfl⟩ : syracuseStep 1281059 = 1921589) B1921589
theorem B298019 : Blo 195805 298019 := bstep (se 1 (by rfl) ⟨223514, by rfl⟩ : syracuseStep 298019 = 447029) B447029
theorem B199715 : Blo 195805 199715 := bstep (se 1 (by rfl) ⟨149786, by rfl⟩ : syracuseStep 199715 = 299573) B299573
theorem B199731 : Blo 195805 199731 := bstep (se 1 (by rfl) ⟨149798, by rfl⟩ : syracuseStep 199731 = 299597) B299597
theorem B330817 : Blo 195805 330817 := bstep (se 2 (by rfl) ⟨124056, by rfl⟩ : syracuseStep 330817 = 248113) B248113
theorem B298049 : Blo 195805 298049 := bstep (se 2 (by rfl) ⟨111768, by rfl⟩ : syracuseStep 298049 = 223537) B223537
theorem B199747 : Blo 195805 199747 := bstep (se 1 (by rfl) ⟨149810, by rfl⟩ : syracuseStep 199747 = 299621) B299621
theorem B298067 : Blo 195805 298067 := bstep (se 1 (by rfl) ⟨223550, by rfl⟩ : syracuseStep 298067 = 447101) B447101
theorem B199763 : Blo 195805 199763 := bstep (se 1 (by rfl) ⟨149822, by rfl⟩ : syracuseStep 199763 = 299645) B299645
theorem B330851 : Blo 195805 330851 := bstep (se 1 (by rfl) ⟨248138, by rfl⟩ : syracuseStep 330851 = 496277) B496277
theorem B199779 : Blo 195805 199779 := bstep (se 1 (by rfl) ⟨149834, by rfl⟩ : syracuseStep 199779 = 299669) B299669
theorem B298097 : Blo 195805 298097 := bstep (se 2 (by rfl) ⟨111786, by rfl⟩ : syracuseStep 298097 = 223573) B223573
theorem B199795 : Blo 195805 199795 := bstep (se 1 (by rfl) ⟨149846, by rfl⟩ : syracuseStep 199795 = 299693) B299693
theorem B298115 : Blo 195805 298115 := bstep (se 1 (by rfl) ⟨223586, by rfl⟩ : syracuseStep 298115 = 447173) B447173
theorem B298145 : Blo 195805 298145 := bstep (se 2 (by rfl) ⟨111804, by rfl⟩ : syracuseStep 298145 = 223609) B223609
theorem B298163 : Blo 195805 298163 := bstep (se 1 (by rfl) ⟨223622, by rfl⟩ : syracuseStep 298163 = 447245) B447245
theorem B298193 : Blo 195805 298193 := bstep (se 2 (by rfl) ⟨111822, by rfl⟩ : syracuseStep 298193 = 223645) B223645
theorem B330979 : Blo 195805 330979 := bstep (se 1 (by rfl) ⟨248234, by rfl⟩ : syracuseStep 330979 = 496469) B496469
theorem B298211 : Blo 195805 298211 := bstep (se 1 (by rfl) ⟨223658, by rfl⟩ : syracuseStep 298211 = 447317) B447317
theorem B298241 : Blo 195805 298241 := bstep (se 2 (by rfl) ⟨111840, by rfl⟩ : syracuseStep 298241 = 223681) B223681
theorem B298259 : Blo 195805 298259 := bstep (se 1 (by rfl) ⟨223694, by rfl⟩ : syracuseStep 298259 = 447389) B447389
theorem B298289 : Blo 195805 298289 := bstep (se 2 (by rfl) ⟨111858, by rfl⟩ : syracuseStep 298289 = 223717) B223717
theorem B298307 : Blo 195805 298307 := bstep (se 1 (by rfl) ⟨223730, by rfl⟩ : syracuseStep 298307 = 447461) B447461
theorem B560465 : Blo 195805 560465 := bstep (se 2 (by rfl) ⟨210174, by rfl⟩ : syracuseStep 560465 = 420349) B420349
theorem B298337 : Blo 195805 298337 := bstep (se 2 (by rfl) ⟨111876, by rfl⟩ : syracuseStep 298337 = 223753) B223753
theorem B331121 : Blo 195805 331121 := bstep (se 2 (by rfl) ⟨124170, by rfl⟩ : syracuseStep 331121 = 248341) B248341
theorem B298355 : Blo 195805 298355 := bstep (se 1 (by rfl) ⟨223766, by rfl⟩ : syracuseStep 298355 = 447533) B447533
theorem B298385 : Blo 195805 298385 := bstep (se 2 (by rfl) ⟨111894, by rfl⟩ : syracuseStep 298385 = 223789) B223789
theorem B298403 : Blo 195805 298403 := bstep (se 1 (by rfl) ⟨223802, by rfl⟩ : syracuseStep 298403 = 447605) B447605
theorem B298433 : Blo 195805 298433 := bstep (se 2 (by rfl) ⟨111912, by rfl⟩ : syracuseStep 298433 = 223825) B223825
theorem B298451 : Blo 195805 298451 := bstep (se 1 (by rfl) ⟨223838, by rfl⟩ : syracuseStep 298451 = 447677) B447677
theorem B331249 : Blo 195805 331249 := bstep (se 2 (by rfl) ⟨124218, by rfl⟩ : syracuseStep 331249 = 248437) B248437
theorem B298481 : Blo 195805 298481 := bstep (se 2 (by rfl) ⟨111930, by rfl⟩ : syracuseStep 298481 = 223861) B223861
theorem B298499 : Blo 195805 298499 := bstep (se 1 (by rfl) ⟨223874, by rfl⟩ : syracuseStep 298499 = 447749) B447749
theorem B1019405 : Blo 195805 1019405 := bstep (se 3 (by rfl) ⟨191138, by rfl⟩ : syracuseStep 1019405 = 382277) B382277
theorem B331283 : Blo 195805 331283 := bstep (se 1 (by rfl) ⟨248462, by rfl⟩ : syracuseStep 331283 = 496925) B496925
theorem B298529 : Blo 195805 298529 := bstep (se 2 (by rfl) ⟨111948, by rfl⟩ : syracuseStep 298529 = 223897) B223897
theorem B298547 : Blo 195805 298547 := bstep (se 1 (by rfl) ⟨223910, by rfl⟩ : syracuseStep 298547 = 447821) B447821
theorem B298577 : Blo 195805 298577 := bstep (se 2 (by rfl) ⟨111966, by rfl⟩ : syracuseStep 298577 = 223933) B223933
theorem B298595 : Blo 195805 298595 := bstep (se 1 (by rfl) ⟨223946, by rfl⟩ : syracuseStep 298595 = 447893) B447893
theorem B3640945 : Blo 195805 3640945 := bstep (se 2 (by rfl) ⟨1365354, by rfl⟩ : syracuseStep 3640945 = 2730709) B2730709
theorem B298625 : Blo 195805 298625 := bstep (se 2 (by rfl) ⟨111984, by rfl⟩ : syracuseStep 298625 = 223969) B223969
theorem B331411 : Blo 195805 331411 := bstep (se 1 (by rfl) ⟨248558, by rfl⟩ : syracuseStep 331411 = 497117) B497117
theorem B298643 : Blo 195805 298643 := bstep (se 1 (by rfl) ⟨223982, by rfl⟩ : syracuseStep 298643 = 447965) B447965
theorem B298673 : Blo 195805 298673 := bstep (se 2 (by rfl) ⟨112002, by rfl⟩ : syracuseStep 298673 = 224005) B224005
theorem B298691 : Blo 195805 298691 := bstep (se 1 (by rfl) ⟨224018, by rfl⟩ : syracuseStep 298691 = 448037) B448037
theorem B265937 : Blo 195805 265937 := bstep (se 2 (by rfl) ⟨99726, by rfl⟩ : syracuseStep 265937 = 199453) B199453
theorem B298721 : Blo 195805 298721 := bstep (se 2 (by rfl) ⟨112020, by rfl⟩ : syracuseStep 298721 = 224041) B224041
theorem B298739 : Blo 195805 298739 := bstep (se 1 (by rfl) ⟨224054, by rfl⟩ : syracuseStep 298739 = 448109) B448109
theorem B298769 : Blo 195805 298769 := bstep (se 2 (by rfl) ⟨112038, by rfl⟩ : syracuseStep 298769 = 224077) B224077
theorem B331553 : Blo 195805 331553 := bstep (se 2 (by rfl) ⟨124332, by rfl⟩ : syracuseStep 331553 = 248665) B248665
theorem B298787 : Blo 195805 298787 := bstep (se 1 (by rfl) ⟨224090, by rfl⟩ : syracuseStep 298787 = 448181) B448181
theorem B298817 : Blo 195805 298817 := bstep (se 2 (by rfl) ⟨112056, by rfl⟩ : syracuseStep 298817 = 224113) B224113
theorem B298835 : Blo 195805 298835 := bstep (se 1 (by rfl) ⟨224126, by rfl⟩ : syracuseStep 298835 = 448253) B448253
theorem B298865 : Blo 195805 298865 := bstep (se 2 (by rfl) ⟨112074, by rfl⟩ : syracuseStep 298865 = 224149) B224149
theorem B298883 : Blo 195805 298883 := bstep (se 1 (by rfl) ⟨224162, by rfl⟩ : syracuseStep 298883 = 448325) B448325
theorem B1347461 : Blo 195805 1347461 := bstep (se 4 (by rfl) ⟨126324, by rfl⟩ : syracuseStep 1347461 = 252649) B252649
theorem B331681 : Blo 195805 331681 := bstep (se 2 (by rfl) ⟨124380, by rfl⟩ : syracuseStep 331681 = 248761) B248761
theorem B298913 : Blo 195805 298913 := bstep (se 2 (by rfl) ⟨112092, by rfl⟩ : syracuseStep 298913 = 224185) B224185
theorem B298931 : Blo 195805 298931 := bstep (se 1 (by rfl) ⟨224198, by rfl⟩ : syracuseStep 298931 = 448397) B448397
theorem B331715 : Blo 195805 331715 := bstep (se 1 (by rfl) ⟨248786, by rfl⟩ : syracuseStep 331715 = 497573) B497573
theorem B298961 : Blo 195805 298961 := bstep (se 2 (by rfl) ⟨112110, by rfl⟩ : syracuseStep 298961 = 224221) B224221
theorem B298979 : Blo 195805 298979 := bstep (se 1 (by rfl) ⟨224234, by rfl⟩ : syracuseStep 298979 = 448469) B448469
theorem B299009 : Blo 195805 299009 := bstep (se 2 (by rfl) ⟨112128, by rfl⟩ : syracuseStep 299009 = 224257) B224257
theorem B299027 : Blo 195805 299027 := bstep (se 1 (by rfl) ⟨224270, by rfl⟩ : syracuseStep 299027 = 448541) B448541
theorem B757795 : Blo 195805 757795 := bstep (se 1 (by rfl) ⟨568346, by rfl⟩ : syracuseStep 757795 = 1136693) B1136693
theorem B299057 : Blo 195805 299057 := bstep (se 2 (by rfl) ⟨112146, by rfl⟩ : syracuseStep 299057 = 224293) B224293
theorem B331843 : Blo 195805 331843 := bstep (se 1 (by rfl) ⟨248882, by rfl⟩ : syracuseStep 331843 = 497765) B497765
theorem B299075 : Blo 195805 299075 := bstep (se 1 (by rfl) ⟨224306, by rfl⟩ : syracuseStep 299075 = 448613) B448613
theorem B299105 : Blo 195805 299105 := bstep (se 2 (by rfl) ⟨112164, by rfl⟩ : syracuseStep 299105 = 224329) B224329
theorem B299123 : Blo 195805 299123 := bstep (se 1 (by rfl) ⟨224342, by rfl⟩ : syracuseStep 299123 = 448685) B448685
theorem B299153 : Blo 195805 299153 := bstep (se 2 (by rfl) ⟨112182, by rfl⟩ : syracuseStep 299153 = 224365) B224365
theorem B299171 : Blo 195805 299171 := bstep (se 1 (by rfl) ⟨224378, by rfl⟩ : syracuseStep 299171 = 448757) B448757
theorem B299201 : Blo 195805 299201 := bstep (se 2 (by rfl) ⟨112200, by rfl⟩ : syracuseStep 299201 = 224401) B224401
theorem B331985 : Blo 195805 331985 := bstep (se 2 (by rfl) ⟨124494, by rfl⟩ : syracuseStep 331985 = 248989) B248989
theorem B299219 : Blo 195805 299219 := bstep (se 1 (by rfl) ⟨224414, by rfl⟩ : syracuseStep 299219 = 448829) B448829
theorem B299249 : Blo 195805 299249 := bstep (se 2 (by rfl) ⟨112218, by rfl⟩ : syracuseStep 299249 = 224437) B224437
theorem B299267 : Blo 195805 299267 := bstep (se 1 (by rfl) ⟨224450, by rfl⟩ : syracuseStep 299267 = 448901) B448901
theorem B561421 : Blo 195805 561421 := bstep (se 3 (by rfl) ⟨105266, by rfl⟩ : syracuseStep 561421 = 210533) B210533
theorem B299297 : Blo 195805 299297 := bstep (se 2 (by rfl) ⟨112236, by rfl⟩ : syracuseStep 299297 = 224473) B224473
theorem B299315 : Blo 195805 299315 := bstep (se 1 (by rfl) ⟨224486, by rfl⟩ : syracuseStep 299315 = 448973) B448973
theorem B495953 : Blo 195805 495953 := bstep (se 2 (by rfl) ⟨185982, by rfl⟩ : syracuseStep 495953 = 371965) B371965
theorem B332113 : Blo 195805 332113 := bstep (se 2 (by rfl) ⟨124542, by rfl⟩ : syracuseStep 332113 = 249085) B249085
theorem B299345 : Blo 195805 299345 := bstep (se 2 (by rfl) ⟨112254, by rfl⟩ : syracuseStep 299345 = 224509) B224509
theorem B299363 : Blo 195805 299363 := bstep (se 1 (by rfl) ⟨224522, by rfl⟩ : syracuseStep 299363 = 449045) B449045
theorem B332147 : Blo 195805 332147 := bstep (se 1 (by rfl) ⟨249110, by rfl⟩ : syracuseStep 332147 = 498221) B498221
theorem B299393 : Blo 195805 299393 := bstep (se 2 (by rfl) ⟨112272, by rfl⟩ : syracuseStep 299393 = 224545) B224545
theorem B496003 : Blo 195805 496003 := bstep (se 1 (by rfl) ⟨372002, by rfl⟩ : syracuseStep 496003 = 744005) B744005
theorem B201107 : Blo 195805 201107 := bstep (se 1 (by rfl) ⟨150830, by rfl⟩ : syracuseStep 201107 = 301661) B301661
theorem B299411 : Blo 195805 299411 := bstep (se 1 (by rfl) ⟨224558, by rfl⟩ : syracuseStep 299411 = 449117) B449117
theorem B299441 : Blo 195805 299441 := bstep (se 2 (by rfl) ⟨112290, by rfl⟩ : syracuseStep 299441 = 224581) B224581
theorem B627139 : Blo 195805 627139 := bstep (se 1 (by rfl) ⟨470354, by rfl⟩ : syracuseStep 627139 = 940709) B940709
theorem B299459 : Blo 195805 299459 := bstep (se 1 (by rfl) ⟨224594, by rfl⟩ : syracuseStep 299459 = 449189) B449189
theorem B299489 : Blo 195805 299489 := bstep (se 2 (by rfl) ⟨112308, by rfl⟩ : syracuseStep 299489 = 224617) B224617
theorem B561649 : Blo 195805 561649 := bstep (se 2 (by rfl) ⟨210618, by rfl⟩ : syracuseStep 561649 = 421237) B421237
theorem B1610225 : Blo 195805 1610225 := bstep (se 2 (by rfl) ⟨603834, by rfl⟩ : syracuseStep 1610225 = 1207669) B1207669
theorem B332275 : Blo 195805 332275 := bstep (se 1 (by rfl) ⟨249206, by rfl⟩ : syracuseStep 332275 = 498413) B498413
theorem B299507 : Blo 195805 299507 := bstep (se 1 (by rfl) ⟨224630, by rfl⟩ : syracuseStep 299507 = 449261) B449261
theorem B266755 : Blo 195805 266755 := bstep (se 1 (by rfl) ⟨200066, by rfl⟩ : syracuseStep 266755 = 400133) B400133
theorem B1282565 : Blo 195805 1282565 := bstep (se 4 (by rfl) ⟨120240, by rfl⟩ : syracuseStep 1282565 = 240481) B240481
theorem B496145 : Blo 195805 496145 := bstep (se 2 (by rfl) ⟨186054, by rfl⟩ : syracuseStep 496145 = 372109) B372109
theorem B299537 : Blo 195805 299537 := bstep (se 2 (by rfl) ⟨112326, by rfl⟩ : syracuseStep 299537 = 224653) B224653
theorem B299555 : Blo 195805 299555 := bstep (se 1 (by rfl) ⟨224666, by rfl⟩ : syracuseStep 299555 = 449333) B449333
theorem B299585 : Blo 195805 299585 := bstep (se 2 (by rfl) ⟨112344, by rfl⟩ : syracuseStep 299585 = 224689) B224689
theorem B299603 : Blo 195805 299603 := bstep (se 1 (by rfl) ⟨224702, by rfl⟩ : syracuseStep 299603 = 449405) B449405
theorem B299633 : Blo 195805 299633 := bstep (se 2 (by rfl) ⟨112362, by rfl⟩ : syracuseStep 299633 = 224725) B224725
theorem B332417 : Blo 195805 332417 := bstep (se 2 (by rfl) ⟨124656, by rfl⟩ : syracuseStep 332417 = 249313) B249313
theorem B299651 : Blo 195805 299651 := bstep (se 1 (by rfl) ⟨224738, by rfl⟩ : syracuseStep 299651 = 449477) B449477
theorem B561809 : Blo 195805 561809 := bstep (se 2 (by rfl) ⟨210678, by rfl⟩ : syracuseStep 561809 = 421357) B421357
theorem B299681 : Blo 195805 299681 := bstep (se 2 (by rfl) ⟨112380, by rfl⟩ : syracuseStep 299681 = 224761) B224761
theorem B299699 : Blo 195805 299699 := bstep (se 1 (by rfl) ⟨224774, by rfl⟩ : syracuseStep 299699 = 449549) B449549
theorem B332545 : Blo 195805 332545 := bstep (se 2 (by rfl) ⟨124704, by rfl⟩ : syracuseStep 332545 = 249409) B249409
theorem B561923 : Blo 195805 561923 := bstep (se 1 (by rfl) ⟨421442, by rfl⟩ : syracuseStep 561923 = 842885) B842885
theorem B332579 : Blo 195805 332579 := bstep (se 1 (by rfl) ⟨249434, by rfl⟩ : syracuseStep 332579 = 498869) B498869
theorem B627601 : Blo 195805 627601 := bstep (se 2 (by rfl) ⟨235350, by rfl⟩ : syracuseStep 627601 = 470701) B470701
theorem B332707 : Blo 195805 332707 := bstep (se 1 (by rfl) ⟨249530, by rfl⟩ : syracuseStep 332707 = 499061) B499061
theorem B529357 : Blo 195805 529357 := bstep (se 3 (by rfl) ⟨99254, by rfl⟩ : syracuseStep 529357 = 198509) B198509
theorem B332849 : Blo 195805 332849 := bstep (se 2 (by rfl) ⟨124818, by rfl⟩ : syracuseStep 332849 = 249637) B249637
theorem B2823281 : Blo 195805 2823281 := bstep (se 2 (by rfl) ⟨1058730, by rfl⟩ : syracuseStep 2823281 = 2117461) B2117461
theorem B332977 : Blo 195805 332977 := bstep (se 2 (by rfl) ⟨124866, by rfl⟩ : syracuseStep 332977 = 249733) B249733
theorem B333011 : Blo 195805 333011 := bstep (se 1 (by rfl) ⟨249758, by rfl⟩ : syracuseStep 333011 = 499517) B499517
theorem B333139 : Blo 195805 333139 := bstep (se 1 (by rfl) ⟨249854, by rfl⟩ : syracuseStep 333139 = 499709) B499709
theorem B267667 : Blo 195805 267667 := bstep (se 1 (by rfl) ⟨200750, by rfl⟩ : syracuseStep 267667 = 401501) B401501
theorem B333281 : Blo 195805 333281 := bstep (se 2 (by rfl) ⟨124980, by rfl⟩ : syracuseStep 333281 = 249961) B249961
theorem B3282403 : Blo 195805 3282403 := bstep (se 1 (by rfl) ⟨2461802, by rfl⟩ : syracuseStep 3282403 = 4923605) B4923605
theorem B497137 : Blo 195805 497137 := bstep (se 2 (by rfl) ⟨186426, by rfl⟩ : syracuseStep 497137 = 372853) B372853
theorem B333409 : Blo 195805 333409 := bstep (se 2 (by rfl) ⟨125028, by rfl⟩ : syracuseStep 333409 = 250057) B250057
theorem B333443 : Blo 195805 333443 := bstep (se 1 (by rfl) ⟨250082, by rfl⟩ : syracuseStep 333443 = 500165) B500165
theorem B661229 : Blo 195805 661229 := bstep (se 3 (by rfl) ⟨123980, by rfl⟩ : syracuseStep 661229 = 247961) B247961
theorem B562925 : Blo 195805 562925 := bstep (se 3 (by rfl) ⟨105548, by rfl⟩ : syracuseStep 562925 = 211097) B211097
theorem B497411 : Blo 195805 497411 := bstep (se 1 (by rfl) ⟨373058, by rfl⟩ : syracuseStep 497411 = 746117) B746117
theorem B333571 : Blo 195805 333571 := bstep (se 1 (by rfl) ⟨250178, by rfl⟩ : syracuseStep 333571 = 500357) B500357
theorem B530189 : Blo 195805 530189 := bstep (se 3 (by rfl) ⟨99410, by rfl⟩ : syracuseStep 530189 = 198821) B198821
theorem B661283 : Blo 195805 661283 := bstep (se 1 (by rfl) ⟨495962, by rfl⟩ : syracuseStep 661283 = 991925) B991925
theorem B333713 : Blo 195805 333713 := bstep (se 2 (by rfl) ⟨125142, by rfl⟩ : syracuseStep 333713 = 250285) B250285
theorem B563107 : Blo 195805 563107 := bstep (se 1 (by rfl) ⟨422330, by rfl⟩ : syracuseStep 563107 = 844661) B844661
theorem B497603 : Blo 195805 497603 := bstep (se 1 (by rfl) ⟨373202, by rfl⟩ : syracuseStep 497603 = 746405) B746405
theorem B628717 : Blo 195805 628717 := bstep (se 3 (by rfl) ⟨117884, by rfl⟩ : syracuseStep 628717 = 235769) B235769
theorem B2529265 : Blo 195805 2529265 := bstep (se 2 (by rfl) ⟨948474, by rfl⟩ : syracuseStep 2529265 = 1896949) B1896949
theorem B333841 : Blo 195805 333841 := bstep (se 2 (by rfl) ⟨125190, by rfl⟩ : syracuseStep 333841 = 250381) B250381
theorem B661553 : Blo 195805 661553 := bstep (se 2 (by rfl) ⟨248082, by rfl⟩ : syracuseStep 661553 = 496165) B496165
theorem B333875 : Blo 195805 333875 := bstep (se 1 (by rfl) ⟨250406, by rfl⟩ : syracuseStep 333875 = 500813) B500813
theorem B2267189 : Blo 195805 2267189 := bstep (se 5 (by rfl) ⟨106274, by rfl⟩ : syracuseStep 2267189 = 212549) B212549
theorem B563267 : Blo 195805 563267 := bstep (se 1 (by rfl) ⟨422450, by rfl⟩ : syracuseStep 563267 = 844901) B844901
theorem B334003 : Blo 195805 334003 := bstep (se 1 (by rfl) ⟨250502, by rfl⟩ : syracuseStep 334003 = 501005) B501005
theorem B1808581 : Blo 195805 1808581 := bstep (se 4 (by rfl) ⟨169554, by rfl⟩ : syracuseStep 1808581 = 339109) B339109
theorem B399587 : Blo 195805 399587 := bstep (se 1 (by rfl) ⟨299690, by rfl⟩ : syracuseStep 399587 = 599381) B599381
theorem B399619 : Blo 195805 399619 := bstep (se 1 (by rfl) ⟨299714, by rfl⟩ : syracuseStep 399619 = 599429) B599429
theorem B334145 : Blo 195805 334145 := bstep (se 2 (by rfl) ⟨125304, by rfl⟩ : syracuseStep 334145 = 250609) B250609
theorem B1350029 : Blo 195805 1350029 := bstep (se 3 (by rfl) ⟨253130, by rfl⟩ : syracuseStep 1350029 = 506261) B506261
theorem B334273 : Blo 195805 334273 := bstep (se 2 (by rfl) ⟨125352, by rfl⟩ : syracuseStep 334273 = 250705) B250705
theorem B1612229 : Blo 195805 1612229 := bstep (se 4 (by rfl) ⟨151146, by rfl⟩ : syracuseStep 1612229 = 302293) B302293
theorem B334307 : Blo 195805 334307 := bstep (se 1 (by rfl) ⟨250730, by rfl⟩ : syracuseStep 334307 = 501461) B501461
theorem B268771 : Blo 195805 268771 := bstep (se 1 (by rfl) ⟨201578, by rfl⟩ : syracuseStep 268771 = 403157) B403157
theorem B1120837 : Blo 195805 1120837 := bstep (se 4 (by rfl) ⟨105078, by rfl⟩ : syracuseStep 1120837 = 210157) B210157
theorem B662093 : Blo 195805 662093 := bstep (se 3 (by rfl) ⟨124142, by rfl⟩ : syracuseStep 662093 = 248285) B248285
theorem B334435 : Blo 195805 334435 := bstep (se 1 (by rfl) ⟨250826, by rfl⟩ : syracuseStep 334435 = 501653) B501653
theorem B662147 : Blo 195805 662147 := bstep (se 1 (by rfl) ⟨496610, by rfl⟩ : syracuseStep 662147 = 993221) B993221
theorem B334577 : Blo 195805 334577 := bstep (se 2 (by rfl) ⟨125466, by rfl⟩ : syracuseStep 334577 = 250933) B250933
theorem B629549 : Blo 195805 629549 := bstep (se 3 (by rfl) ⟨118040, by rfl⟩ : syracuseStep 629549 = 236081) B236081
theorem B498545 : Blo 195805 498545 := bstep (se 2 (by rfl) ⟨186954, by rfl⟩ : syracuseStep 498545 = 373909) B373909
theorem B334705 : Blo 195805 334705 := bstep (se 2 (by rfl) ⟨125514, by rfl⟩ : syracuseStep 334705 = 251029) B251029
theorem B662417 : Blo 195805 662417 := bstep (se 2 (by rfl) ⟨248406, by rfl⟩ : syracuseStep 662417 = 496813) B496813
theorem B334739 : Blo 195805 334739 := bstep (se 1 (by rfl) ⟨251054, by rfl⟩ : syracuseStep 334739 = 502109) B502109
theorem B596899 : Blo 195805 596899 := bstep (se 1 (by rfl) ⟨447674, by rfl⟩ : syracuseStep 596899 = 895349) B895349
theorem B498595 : Blo 195805 498595 := bstep (se 1 (by rfl) ⟨373946, by rfl⟩ : syracuseStep 498595 = 747893) B747893
theorem B334867 : Blo 195805 334867 := bstep (se 1 (by rfl) ⟨251150, by rfl⟩ : syracuseStep 334867 = 502301) B502301
theorem B498737 : Blo 195805 498737 := bstep (se 2 (by rfl) ⟨187026, by rfl⟩ : syracuseStep 498737 = 374053) B374053
theorem B564337 : Blo 195805 564337 := bstep (se 2 (by rfl) ⟨211626, by rfl⟩ : syracuseStep 564337 = 423253) B423253
theorem B335009 : Blo 195805 335009 := bstep (se 2 (by rfl) ⟨125628, by rfl⟩ : syracuseStep 335009 = 251257) B251257
theorem B1219853 : Blo 195805 1219853 := bstep (se 3 (by rfl) ⟨228722, by rfl⟩ : syracuseStep 1219853 = 457445) B457445
theorem B400657 : Blo 195805 400657 := bstep (se 2 (by rfl) ⟨150246, by rfl⟩ : syracuseStep 400657 = 300493) B300493
theorem B335137 : Blo 195805 335137 := bstep (se 2 (by rfl) ⟨125676, by rfl⟩ : syracuseStep 335137 = 251353) B251353
theorem B335171 : Blo 195805 335171 := bstep (se 1 (by rfl) ⟨251378, by rfl⟩ : syracuseStep 335171 = 502757) B502757
theorem B662957 : Blo 195805 662957 := bstep (se 3 (by rfl) ⟨124304, by rfl⟩ : syracuseStep 662957 = 248609) B248609
theorem B335299 : Blo 195805 335299 := bstep (se 1 (by rfl) ⟨251474, by rfl⟩ : syracuseStep 335299 = 502949) B502949
theorem B663011 : Blo 195805 663011 := bstep (se 1 (by rfl) ⟨497258, by rfl⟩ : syracuseStep 663011 = 994517) B994517
theorem B335441 : Blo 195805 335441 := bstep (se 2 (by rfl) ⟨125790, by rfl⟩ : syracuseStep 335441 = 251581) B251581
theorem B761521 : Blo 195805 761521 := bstep (se 2 (by rfl) ⟨285570, by rfl⟩ : syracuseStep 761521 = 571141) B571141
theorem B335569 : Blo 195805 335569 := bstep (se 2 (by rfl) ⟨125838, by rfl⟩ : syracuseStep 335569 = 251677) B251677
theorem B663281 : Blo 195805 663281 := bstep (se 2 (by rfl) ⟨248730, by rfl⟩ : syracuseStep 663281 = 497461) B497461
theorem B335603 : Blo 195805 335603 := bstep (se 1 (by rfl) ⟨251702, by rfl⟩ : syracuseStep 335603 = 503405) B503405
theorem B335731 : Blo 195805 335731 := bstep (se 1 (by rfl) ⟨251798, by rfl⟩ : syracuseStep 335731 = 503597) B503597
theorem B335873 : Blo 195805 335873 := bstep (se 2 (by rfl) ⟨125952, by rfl⟩ : syracuseStep 335873 = 251905) B251905
theorem B499729 : Blo 195805 499729 := bstep (se 2 (by rfl) ⟨187398, by rfl⟩ : syracuseStep 499729 = 374797) B374797
theorem B336001 : Blo 195805 336001 := bstep (se 2 (by rfl) ⟨126000, by rfl⟩ : syracuseStep 336001 = 252001) B252001
theorem B336035 : Blo 195805 336035 := bstep (se 1 (by rfl) ⟨252026, by rfl⟩ : syracuseStep 336035 = 504053) B504053
theorem B237811 : Blo 195805 237811 := bstep (se 1 (by rfl) ⟨178358, by rfl⟩ : syracuseStep 237811 = 356717) B356717
theorem B663821 : Blo 195805 663821 := bstep (se 3 (by rfl) ⟨124466, by rfl⟩ : syracuseStep 663821 = 248933) B248933
theorem B500003 : Blo 195805 500003 := bstep (se 1 (by rfl) ⟨375002, by rfl⟩ : syracuseStep 500003 = 750005) B750005
theorem B237859 : Blo 195805 237859 := bstep (se 1 (by rfl) ⟨178394, by rfl⟩ : syracuseStep 237859 = 356789) B356789
theorem B336163 : Blo 195805 336163 := bstep (se 1 (by rfl) ⟨252122, by rfl⟩ : syracuseStep 336163 = 504245) B504245
theorem B3449141 : Blo 195805 3449141 := bstep (se 5 (by rfl) ⟨161678, by rfl⟩ : syracuseStep 3449141 = 323357) B323357
theorem B663875 : Blo 195805 663875 := bstep (se 1 (by rfl) ⟨497906, by rfl⟩ : syracuseStep 663875 = 995813) B995813
theorem B565613 : Blo 195805 565613 := bstep (se 3 (by rfl) ⟨106052, by rfl⟩ : syracuseStep 565613 = 212105) B212105
theorem B991601 : Blo 195805 991601 := bstep (se 2 (by rfl) ⟨371850, by rfl⟩ : syracuseStep 991601 = 743701) B743701
theorem B565667 : Blo 195805 565667 := bstep (se 1 (by rfl) ⟨424250, by rfl⟩ : syracuseStep 565667 = 848501) B848501
theorem B336305 : Blo 195805 336305 := bstep (se 2 (by rfl) ⟨126114, by rfl⟩ : syracuseStep 336305 = 252229) B252229
theorem B500195 : Blo 195805 500195 := bstep (se 1 (by rfl) ⟨375146, by rfl⟩ : syracuseStep 500195 = 750293) B750293
theorem B1122821 : Blo 195805 1122821 := bstep (se 4 (by rfl) ⟨105264, by rfl⟩ : syracuseStep 1122821 = 210529) B210529
theorem B565795 : Blo 195805 565795 := bstep (se 1 (by rfl) ⟨424346, by rfl⟩ : syracuseStep 565795 = 848693) B848693
theorem B336433 : Blo 195805 336433 := bstep (se 2 (by rfl) ⟨126162, by rfl⟩ : syracuseStep 336433 = 252325) B252325
theorem B3875381 : Blo 195805 3875381 := bstep (se 5 (by rfl) ⟨181658, by rfl⟩ : syracuseStep 3875381 = 363317) B363317
theorem B664145 : Blo 195805 664145 := bstep (se 2 (by rfl) ⟨249054, by rfl⟩ : syracuseStep 664145 = 498109) B498109
theorem B565841 : Blo 195805 565841 := bstep (se 2 (by rfl) ⟨212190, by rfl⟩ : syracuseStep 565841 = 424381) B424381
theorem B336467 : Blo 195805 336467 := bstep (se 1 (by rfl) ⟨252350, by rfl⟩ : syracuseStep 336467 = 504701) B504701
theorem B336595 : Blo 195805 336595 := bstep (se 1 (by rfl) ⟨252446, by rfl⟩ : syracuseStep 336595 = 504893) B504893
theorem B566033 : Blo 195805 566033 := bstep (se 2 (by rfl) ⟨212262, by rfl⟩ : syracuseStep 566033 = 424525) B424525
theorem B336737 : Blo 195805 336737 := bstep (se 2 (by rfl) ⟨126276, by rfl⟩ : syracuseStep 336737 = 252553) B252553
theorem B631651 : Blo 195805 631651 := bstep (se 1 (by rfl) ⟨473738, by rfl⟩ : syracuseStep 631651 = 947477) B947477
theorem B566129 : Blo 195805 566129 := bstep (se 2 (by rfl) ⟨212298, by rfl⟩ : syracuseStep 566129 = 424597) B424597
theorem B336865 : Blo 195805 336865 := bstep (se 2 (by rfl) ⟨126324, by rfl⟩ : syracuseStep 336865 = 252649) B252649
theorem B402403 : Blo 195805 402403 := bstep (se 1 (by rfl) ⟨301802, by rfl⟩ : syracuseStep 402403 = 603605) B603605
theorem B631793 : Blo 195805 631793 := bstep (se 2 (by rfl) ⟨236922, by rfl⟩ : syracuseStep 631793 = 473845) B473845
theorem B336899 : Blo 195805 336899 := bstep (se 1 (by rfl) ⟨252674, by rfl⟩ : syracuseStep 336899 = 505349) B505349
theorem B304163 : Blo 195805 304163 := bstep (se 1 (by rfl) ⟨228122, by rfl⟩ : syracuseStep 304163 = 456245) B456245
theorem B664685 : Blo 195805 664685 := bstep (se 3 (by rfl) ⟨124628, by rfl⟩ : syracuseStep 664685 = 249257) B249257
theorem B337027 : Blo 195805 337027 := bstep (se 1 (by rfl) ⟨252770, by rfl⟩ : syracuseStep 337027 = 505541) B505541
theorem B664739 : Blo 195805 664739 := bstep (se 1 (by rfl) ⟨498554, by rfl⟩ : syracuseStep 664739 = 997109) B997109
theorem B337169 : Blo 195805 337169 := bstep (se 2 (by rfl) ⟨126438, by rfl⟩ : syracuseStep 337169 = 252877) B252877
theorem B1680709 : Blo 195805 1680709 := bstep (se 4 (by rfl) ⟨157566, by rfl⟩ : syracuseStep 1680709 = 315133) B315133
theorem B501137 : Blo 195805 501137 := bstep (se 2 (by rfl) ⟨187926, by rfl⟩ : syracuseStep 501137 = 375853) B375853
theorem B665009 : Blo 195805 665009 := bstep (se 2 (by rfl) ⟨249378, by rfl⟩ : syracuseStep 665009 = 498757) B498757
theorem B501187 : Blo 195805 501187 := bstep (se 1 (by rfl) ⟨375890, by rfl⟩ : syracuseStep 501187 = 751781) B751781
theorem B402961 : Blo 195805 402961 := bstep (se 2 (by rfl) ⟨151110, by rfl⟩ : syracuseStep 402961 = 302221) B302221
theorem B501329 : Blo 195805 501329 := bstep (se 2 (by rfl) ⟨187998, by rfl⟩ : syracuseStep 501329 = 375997) B375997
theorem B993059 : Blo 195805 993059 := bstep (se 1 (by rfl) ⟨744794, by rfl⟩ : syracuseStep 993059 = 1489589) B1489589
theorem B272179 : Blo 195805 272179 := bstep (se 1 (by rfl) ⟨204134, by rfl⟩ : syracuseStep 272179 = 408269) B408269
theorem B894797 : Blo 195805 894797 := bstep (se 3 (by rfl) ⟨167774, by rfl⟩ : syracuseStep 894797 = 335549) B335549
theorem B665549 : Blo 195805 665549 := bstep (se 3 (by rfl) ⟨124790, by rfl⟩ : syracuseStep 665549 = 249581) B249581
theorem B665603 : Blo 195805 665603 := bstep (se 1 (by rfl) ⟨499202, by rfl⟩ : syracuseStep 665603 = 998405) B998405
theorem B567299 : Blo 195805 567299 := bstep (se 1 (by rfl) ⟨425474, by rfl⟩ : syracuseStep 567299 = 850949) B850949
theorem B1255459 : Blo 195805 1255459 := bstep (se 1 (by rfl) ⟨941594, by rfl⟩ : syracuseStep 1255459 = 1883189) B1883189
theorem B1058885 : Blo 195805 1058885 := bstep (se 4 (by rfl) ⟨99270, by rfl⟩ : syracuseStep 1058885 = 198541) B198541
theorem B665873 : Blo 195805 665873 := bstep (se 2 (by rfl) ⟨249702, by rfl⟩ : syracuseStep 665873 = 499405) B499405
theorem B502321 : Blo 195805 502321 := bstep (se 2 (by rfl) ⟨188370, by rfl⟩ : syracuseStep 502321 = 376741) B376741
theorem B993869 : Blo 195805 993869 := bstep (se 3 (by rfl) ⟨186350, by rfl⟩ : syracuseStep 993869 = 372701) B372701
theorem B666413 : Blo 195805 666413 := bstep (se 3 (by rfl) ⟨124952, by rfl⟩ : syracuseStep 666413 = 249905) B249905
theorem B502595 : Blo 195805 502595 := bstep (se 1 (by rfl) ⟨376946, by rfl⟩ : syracuseStep 502595 = 753893) B753893
theorem B404291 : Blo 195805 404291 := bstep (se 1 (by rfl) ⟨303218, by rfl⟩ : syracuseStep 404291 = 606437) B606437
theorem B666467 : Blo 195805 666467 := bstep (se 1 (by rfl) ⟨499850, by rfl⟩ : syracuseStep 666467 = 999701) B999701
theorem B797617 : Blo 195805 797617 := bstep (se 2 (by rfl) ⟨299106, by rfl⟩ : syracuseStep 797617 = 598213) B598213
theorem B601073 : Blo 195805 601073 := bstep (se 2 (by rfl) ⟨225402, by rfl⟩ : syracuseStep 601073 = 450805) B450805
theorem B502787 : Blo 195805 502787 := bstep (se 1 (by rfl) ⟨377090, by rfl⟩ : syracuseStep 502787 = 754181) B754181
theorem B568333 : Blo 195805 568333 := bstep (se 3 (by rfl) ⟨106562, by rfl⟩ : syracuseStep 568333 = 213125) B213125
theorem B371729 : Blo 195805 371729 := bstep (se 2 (by rfl) ⟨139398, by rfl⟩ : syracuseStep 371729 = 278797) B278797
theorem B666737 : Blo 195805 666737 := bstep (se 2 (by rfl) ⟨250026, by rfl⟩ : syracuseStep 666737 = 500053) B500053
theorem B2534597 : Blo 195805 2534597 := bstep (se 4 (by rfl) ⟨237618, by rfl⟩ : syracuseStep 2534597 = 475237) B475237
theorem B568529 : Blo 195805 568529 := bstep (se 2 (by rfl) ⟨213198, by rfl⟩ : syracuseStep 568529 = 426397) B426397
theorem B634189 : Blo 195805 634189 := bstep (se 3 (by rfl) ⟨118910, by rfl⟩ : syracuseStep 634189 = 237821) B237821
theorem B339329 : Blo 195805 339329 := bstep (se 2 (by rfl) ⟨127248, by rfl⟩ : syracuseStep 339329 = 254497) B254497
theorem B535939 : Blo 195805 535939 := bstep (se 1 (by rfl) ⟨401954, by rfl⟩ : syracuseStep 535939 = 803909) B803909
theorem B404867 : Blo 195805 404867 := bstep (se 1 (by rfl) ⟨303650, by rfl⟩ : syracuseStep 404867 = 607301) B607301
theorem B1027505 : Blo 195805 1027505 := bstep (se 2 (by rfl) ⟨385314, by rfl⟩ : syracuseStep 1027505 = 770629) B770629
theorem B536017 : Blo 195805 536017 := bstep (se 2 (by rfl) ⟨201006, by rfl⟩ : syracuseStep 536017 = 402013) B402013
theorem B667277 : Blo 195805 667277 := bstep (se 3 (by rfl) ⟨125114, by rfl⟩ : syracuseStep 667277 = 250229) B250229
theorem B667331 : Blo 195805 667331 := bstep (se 1 (by rfl) ⟨500498, by rfl⟩ : syracuseStep 667331 = 1000997) B1000997
theorem B372451 : Blo 195805 372451 := bstep (se 1 (by rfl) ⟨279338, by rfl⟩ : syracuseStep 372451 = 558677) B558677
theorem B536483 : Blo 195805 536483 := bstep (se 1 (by rfl) ⟨402362, by rfl⟩ : syracuseStep 536483 = 804725) B804725
theorem B503729 : Blo 195805 503729 := bstep (se 2 (by rfl) ⟨188898, by rfl⟩ : syracuseStep 503729 = 377797) B377797
theorem B667601 : Blo 195805 667601 := bstep (se 2 (by rfl) ⟨250350, by rfl⟩ : syracuseStep 667601 = 500701) B500701
theorem B503779 : Blo 195805 503779 := bstep (se 1 (by rfl) ⟨377834, by rfl⟩ : syracuseStep 503779 = 755669) B755669
theorem B1257457 : Blo 195805 1257457 := bstep (se 2 (by rfl) ⟨471546, by rfl⟩ : syracuseStep 1257457 = 943093) B943093
theorem B339985 : Blo 195805 339985 := bstep (se 2 (by rfl) ⟨127494, by rfl⟩ : syracuseStep 339985 = 254989) B254989
theorem B503921 : Blo 195805 503921 := bstep (se 2 (by rfl) ⟨188970, by rfl⟩ : syracuseStep 503921 = 377941) B377941
theorem B372899 : Blo 195805 372899 := bstep (se 1 (by rfl) ⟨279674, by rfl⟩ : syracuseStep 372899 = 559349) B559349
theorem B1126669 : Blo 195805 1126669 := bstep (se 3 (by rfl) ⟨211250, by rfl⟩ : syracuseStep 1126669 = 422501) B422501
theorem B2896181 : Blo 195805 2896181 := bstep (se 5 (by rfl) ⟨135758, by rfl⟩ : syracuseStep 2896181 = 271517) B271517
theorem B209299 : Blo 195805 209299 := bstep (se 1 (by rfl) ⟨156974, by rfl⟩ : syracuseStep 209299 = 313949) B313949
theorem B373187 : Blo 195805 373187 := bstep (se 1 (by rfl) ⟨279890, by rfl⟩ : syracuseStep 373187 = 559781) B559781
theorem B668141 : Blo 195805 668141 := bstep (se 3 (by rfl) ⟨125276, by rfl⟩ : syracuseStep 668141 = 250553) B250553
theorem B340499 : Blo 195805 340499 := bstep (se 1 (by rfl) ⟨255374, by rfl⟩ : syracuseStep 340499 = 510749) B510749
theorem B668195 : Blo 195805 668195 := bstep (se 1 (by rfl) ⟨501146, by rfl⟩ : syracuseStep 668195 = 1002293) B1002293
theorem B668465 : Blo 195805 668465 := bstep (se 2 (by rfl) ⟨250674, by rfl⟩ : syracuseStep 668465 = 501349) B501349
theorem B504643 : Blo 195805 504643 := bstep (se 1 (by rfl) ⟨378482, by rfl⟩ : syracuseStep 504643 = 756965) B756965
theorem B209747 : Blo 195805 209747 := bstep (se 1 (by rfl) ⟨157310, by rfl⟩ : syracuseStep 209747 = 314621) B314621
theorem B897905 : Blo 195805 897905 := bstep (se 2 (by rfl) ⟨336714, by rfl⟩ : syracuseStep 897905 = 673429) B673429
theorem B341011 : Blo 195805 341011 := bstep (se 1 (by rfl) ⟨255758, by rfl⟩ : syracuseStep 341011 = 511517) B511517
theorem B504913 : Blo 195805 504913 := bstep (se 2 (by rfl) ⟨189342, by rfl⟩ : syracuseStep 504913 = 378685) B378685
theorem B472355 : Blo 195805 472355 := bstep (se 1 (by rfl) ⟨354266, by rfl⟩ : syracuseStep 472355 = 708533) B708533
theorem B669005 : Blo 195805 669005 := bstep (se 3 (by rfl) ⟨125438, by rfl⟩ : syracuseStep 669005 = 250877) B250877
theorem B505187 : Blo 195805 505187 := bstep (se 1 (by rfl) ⟨378890, by rfl⟩ : syracuseStep 505187 = 757781) B757781
theorem B374129 : Blo 195805 374129 := bstep (se 2 (by rfl) ⟨140298, by rfl⟩ : syracuseStep 374129 = 280597) B280597
theorem B669059 : Blo 195805 669059 := bstep (se 1 (by rfl) ⟨501794, by rfl⟩ : syracuseStep 669059 = 1003589) B1003589
theorem B996785 : Blo 195805 996785 := bstep (se 2 (by rfl) ⟨373794, by rfl⟩ : syracuseStep 996785 = 747589) B747589
theorem B472547 : Blo 195805 472547 := bstep (se 1 (by rfl) ⟨354410, by rfl⟩ : syracuseStep 472547 = 708821) B708821
theorem B538093 : Blo 195805 538093 := bstep (se 3 (by rfl) ⟨100892, by rfl⟩ : syracuseStep 538093 = 201785) B201785
theorem B505379 : Blo 195805 505379 := bstep (se 1 (by rfl) ⟨379034, by rfl⟩ : syracuseStep 505379 = 758069) B758069
theorem B472643 : Blo 195805 472643 := bstep (se 1 (by rfl) ⟨354482, by rfl⟩ : syracuseStep 472643 = 708965) B708965
theorem B1422917 : Blo 195805 1422917 := bstep (se 4 (by rfl) ⟨133398, by rfl⟩ : syracuseStep 1422917 = 266797) B266797
theorem B669329 : Blo 195805 669329 := bstep (se 2 (by rfl) ⟨250998, by rfl⟩ : syracuseStep 669329 = 501997) B501997
theorem B2242403 : Blo 195805 2242403 := bstep (se 1 (by rfl) ⟨1681802, by rfl⟩ : syracuseStep 2242403 = 3363605) B3363605
theorem B604099 : Blo 195805 604099 := bstep (se 1 (by rfl) ⟨453074, by rfl⟩ : syracuseStep 604099 = 906149) B906149
theorem B669869 : Blo 195805 669869 := bstep (se 3 (by rfl) ⟨125600, by rfl⟩ : syracuseStep 669869 = 251201) B251201
theorem B211123 : Blo 195805 211123 := bstep (se 1 (by rfl) ⟨158342, by rfl⟩ : syracuseStep 211123 = 316685) B316685
theorem B1128653 : Blo 195805 1128653 := bstep (se 3 (by rfl) ⟨211622, by rfl⟩ : syracuseStep 1128653 = 423245) B423245
theorem B669923 : Blo 195805 669923 := bstep (se 1 (by rfl) ⟨502442, by rfl⟩ : syracuseStep 669923 = 1004885) B1004885
theorem B375025 : Blo 195805 375025 := bstep (se 2 (by rfl) ⟨140634, by rfl⟩ : syracuseStep 375025 = 281269) B281269
theorem B440657 : Blo 195805 440657 := bstep (se 2 (by rfl) ⟨165246, by rfl⟩ : syracuseStep 440657 = 330493) B330493
theorem B440675 : Blo 195805 440675 := bstep (se 1 (by rfl) ⟨330506, by rfl⟩ : syracuseStep 440675 = 661013) B661013
theorem B375185 : Blo 195805 375185 := bstep (se 2 (by rfl) ⟨140694, by rfl⟩ : syracuseStep 375185 = 281389) B281389
theorem B670193 : Blo 195805 670193 := bstep (se 2 (by rfl) ⟨251322, by rfl⟩ : syracuseStep 670193 = 502645) B502645
theorem B440945 : Blo 195805 440945 := bstep (se 2 (by rfl) ⟨165354, by rfl⟩ : syracuseStep 440945 = 330709) B330709
theorem B342641 : Blo 195805 342641 := bstep (se 2 (by rfl) ⟨128490, by rfl⟩ : syracuseStep 342641 = 256981) B256981
theorem B440963 : Blo 195805 440963 := bstep (se 1 (by rfl) ⟨330722, by rfl⟩ : syracuseStep 440963 = 661445) B661445
theorem B637571 : Blo 195805 637571 := bstep (se 1 (by rfl) ⟨478178, by rfl⟩ : syracuseStep 637571 = 956357) B956357
theorem B375587 : Blo 195805 375587 := bstep (se 1 (by rfl) ⟨281690, by rfl⟩ : syracuseStep 375587 = 563381) B563381
theorem B998243 : Blo 195805 998243 := bstep (se 1 (by rfl) ⟨748682, by rfl⟩ : syracuseStep 998243 = 1497365) B1497365
theorem B1063793 : Blo 195805 1063793 := bstep (se 2 (by rfl) ⟨398922, by rfl⟩ : syracuseStep 1063793 = 797845) B797845
theorem B441233 : Blo 195805 441233 := bstep (se 2 (by rfl) ⟨165462, by rfl⟩ : syracuseStep 441233 = 330925) B330925
theorem B441251 : Blo 195805 441251 := bstep (se 1 (by rfl) ⟨330938, by rfl⟩ : syracuseStep 441251 = 661877) B661877
theorem B670733 : Blo 195805 670733 := bstep (se 3 (by rfl) ⟨125762, by rfl⟩ : syracuseStep 670733 = 251525) B251525
theorem B670787 : Blo 195805 670787 := bstep (se 1 (by rfl) ⟨503090, by rfl⟩ : syracuseStep 670787 = 1006181) B1006181
theorem B1129585 : Blo 195805 1129585 := bstep (se 2 (by rfl) ⟨423594, by rfl⟩ : syracuseStep 1129585 = 847189) B847189
theorem B441521 : Blo 195805 441521 := bstep (se 2 (by rfl) ⟨165570, by rfl⟩ : syracuseStep 441521 = 331141) B331141
theorem B441539 : Blo 195805 441539 := bstep (se 1 (by rfl) ⟨331154, by rfl⟩ : syracuseStep 441539 = 662309) B662309
theorem B671057 : Blo 195805 671057 := bstep (se 2 (by rfl) ⟨251646, by rfl⟩ : syracuseStep 671057 = 503293) B503293
theorem B540049 : Blo 195805 540049 := bstep (se 2 (by rfl) ⟨202518, by rfl⟩ : syracuseStep 540049 = 405037) B405037
theorem B212387 : Blo 195805 212387 := bstep (se 1 (by rfl) ⟨159290, by rfl⟩ : syracuseStep 212387 = 318581) B318581
theorem B474545 : Blo 195805 474545 := bstep (se 2 (by rfl) ⟨177954, by rfl⟩ : syracuseStep 474545 = 355909) B355909
theorem B441809 : Blo 195805 441809 := bstep (se 2 (by rfl) ⟨165678, by rfl⟩ : syracuseStep 441809 = 331357) B331357
theorem B638417 : Blo 195805 638417 := bstep (se 2 (by rfl) ⟨239406, by rfl⟩ : syracuseStep 638417 = 478813) B478813
theorem B441827 : Blo 195805 441827 := bstep (se 1 (by rfl) ⟨331370, by rfl⟩ : syracuseStep 441827 = 662741) B662741
theorem B638545 : Blo 195805 638545 := bstep (se 2 (by rfl) ⟨239454, by rfl⟩ : syracuseStep 638545 = 478909) B478909
theorem B999053 : Blo 195805 999053 := bstep (se 3 (by rfl) ⟨187322, by rfl⟩ : syracuseStep 999053 = 374645) B374645
theorem B376483 : Blo 195805 376483 := bstep (se 1 (by rfl) ⟨282362, by rfl⟩ : syracuseStep 376483 = 564725) B564725
theorem B442097 : Blo 195805 442097 := bstep (se 2 (by rfl) ⟨165786, by rfl⟩ : syracuseStep 442097 = 331573) B331573
theorem B442115 : Blo 195805 442115 := bstep (se 1 (by rfl) ⟨331586, by rfl⟩ : syracuseStep 442115 = 663173) B663173
theorem B376643 : Blo 195805 376643 := bstep (se 1 (by rfl) ⟨282482, by rfl⟩ : syracuseStep 376643 = 564965) B564965
theorem B671597 : Blo 195805 671597 := bstep (se 3 (by rfl) ⟨125924, by rfl⟩ : syracuseStep 671597 = 251849) B251849
theorem B671651 : Blo 195805 671651 := bstep (se 1 (by rfl) ⟨503738, by rfl⟩ : syracuseStep 671651 = 1007477) B1007477
theorem B475075 : Blo 195805 475075 := bstep (se 1 (by rfl) ⟨356306, by rfl⟩ : syracuseStep 475075 = 712613) B712613
theorem B442385 : Blo 195805 442385 := bstep (se 2 (by rfl) ⟨165894, by rfl⟩ : syracuseStep 442385 = 331789) B331789
theorem B442403 : Blo 195805 442403 := bstep (se 1 (by rfl) ⟨331802, by rfl⟩ : syracuseStep 442403 = 663605) B663605
theorem B213139 : Blo 195805 213139 := bstep (se 1 (by rfl) ⟨159854, by rfl⟩ : syracuseStep 213139 = 319709) B319709
theorem B671921 : Blo 195805 671921 := bstep (se 2 (by rfl) ⟨251970, by rfl⟩ : syracuseStep 671921 = 503941) B503941
theorem B442673 : Blo 195805 442673 := bstep (se 2 (by rfl) ⟨166002, by rfl⟩ : syracuseStep 442673 = 332005) B332005
theorem B442691 : Blo 195805 442691 := bstep (se 1 (by rfl) ⟨332018, by rfl⟩ : syracuseStep 442691 = 664037) B664037
theorem B1131043 : Blo 195805 1131043 := bstep (se 1 (by rfl) ⟨848282, by rfl⟩ : syracuseStep 1131043 = 1696565) B1696565
theorem B442961 : Blo 195805 442961 := bstep (se 2 (by rfl) ⟨166110, by rfl⟩ : syracuseStep 442961 = 332221) B332221
theorem B279139 : Blo 195805 279139 := bstep (se 1 (by rfl) ⟨209354, by rfl⟩ : syracuseStep 279139 = 418709) B418709
theorem B442979 : Blo 195805 442979 := bstep (se 1 (by rfl) ⟨332234, by rfl⟩ : syracuseStep 442979 = 664469) B664469
theorem B672461 : Blo 195805 672461 := bstep (se 3 (by rfl) ⟨126086, by rfl⟩ : syracuseStep 672461 = 252173) B252173
theorem B672515 : Blo 195805 672515 := bstep (se 1 (by rfl) ⟨504386, by rfl⟩ : syracuseStep 672515 = 1008773) B1008773
theorem B443249 : Blo 195805 443249 := bstep (se 2 (by rfl) ⟨166218, by rfl⟩ : syracuseStep 443249 = 332437) B332437
theorem B377713 : Blo 195805 377713 := bstep (se 2 (by rfl) ⟨141642, by rfl⟩ : syracuseStep 377713 = 283285) B283285
theorem B443267 : Blo 195805 443267 := bstep (se 1 (by rfl) ⟨332450, by rfl⟩ : syracuseStep 443267 = 664901) B664901
theorem B1426403 : Blo 195805 1426403 := bstep (se 1 (by rfl) ⟨1069802, by rfl⟩ : syracuseStep 1426403 = 2139605) B2139605
theorem B1360867 : Blo 195805 1360867 := bstep (se 1 (by rfl) ⟨1020650, by rfl⟩ : syracuseStep 1360867 = 2041301) B2041301
theorem B607213 : Blo 195805 607213 := bstep (se 3 (by rfl) ⟨113852, by rfl⟩ : syracuseStep 607213 = 227705) B227705
theorem B508931 : Blo 195805 508931 := bstep (se 1 (by rfl) ⟨381698, by rfl⟩ : syracuseStep 508931 = 763397) B763397
theorem B672785 : Blo 195805 672785 := bstep (se 2 (by rfl) ⟨252294, by rfl⟩ : syracuseStep 672785 = 504589) B504589
theorem B1131569 : Blo 195805 1131569 := bstep (se 2 (by rfl) ⟨424338, by rfl⟩ : syracuseStep 1131569 = 848677) B848677
theorem B279617 : Blo 195805 279617 := bstep (se 2 (by rfl) ⟨104856, by rfl⟩ : syracuseStep 279617 = 209713) B209713
theorem B443537 : Blo 195805 443537 := bstep (se 2 (by rfl) ⟨166326, by rfl⟩ : syracuseStep 443537 = 332653) B332653
theorem B443555 : Blo 195805 443555 := bstep (se 1 (by rfl) ⟨332666, by rfl⟩ : syracuseStep 443555 = 665333) B665333
theorem B574627 : Blo 195805 574627 := bstep (se 1 (by rfl) ⟨430970, by rfl⟩ : syracuseStep 574627 = 861941) B861941
theorem B279731 : Blo 195805 279731 := bstep (se 1 (by rfl) ⟨209798, by rfl⟩ : syracuseStep 279731 = 419597) B419597
theorem B1262789 : Blo 195805 1262789 := bstep (se 4 (by rfl) ⟨118386, by rfl⟩ : syracuseStep 1262789 = 236773) B236773
theorem B705763 : Blo 195805 705763 := bstep (se 1 (by rfl) ⟨529322, by rfl⟩ : syracuseStep 705763 = 1058645) B1058645
theorem B279811 : Blo 195805 279811 := bstep (se 1 (by rfl) ⟨209858, by rfl⟩ : syracuseStep 279811 = 419717) B419717
theorem B443825 : Blo 195805 443825 := bstep (se 2 (by rfl) ⟨166434, by rfl⟩ : syracuseStep 443825 = 332869) B332869
theorem B443843 : Blo 195805 443843 := bstep (se 1 (by rfl) ⟨332882, by rfl⟩ : syracuseStep 443843 = 665765) B665765
theorem B673325 : Blo 195805 673325 := bstep (se 3 (by rfl) ⟨126248, by rfl⟩ : syracuseStep 673325 = 252497) B252497
theorem B673379 : Blo 195805 673379 := bstep (se 1 (by rfl) ⟨505034, by rfl⟩ : syracuseStep 673379 = 1010069) B1010069
theorem B444113 : Blo 195805 444113 := bstep (se 2 (by rfl) ⟨166542, by rfl⟩ : syracuseStep 444113 = 333085) B333085
theorem B444131 : Blo 195805 444131 := bstep (se 1 (by rfl) ⟨333098, by rfl⟩ : syracuseStep 444131 = 666197) B666197
theorem B280369 : Blo 195805 280369 := bstep (se 2 (by rfl) ⟨105138, by rfl⟩ : syracuseStep 280369 = 210277) B210277
theorem B1689457 : Blo 195805 1689457 := bstep (se 2 (by rfl) ⟨633546, by rfl⟩ : syracuseStep 1689457 = 1267093) B1267093
theorem B673649 : Blo 195805 673649 := bstep (se 2 (by rfl) ⟨252618, by rfl⟩ : syracuseStep 673649 = 505237) B505237
theorem B20760461 : Blo 195805 20760461 := bstep (se 3 (by rfl) ⟨3892586, by rfl⟩ : syracuseStep 20760461 = 7785173) B7785173
theorem B378769 : Blo 195805 378769 := bstep (se 2 (by rfl) ⟨142038, by rfl⟩ : syracuseStep 378769 = 284077) B284077
theorem B214931 : Blo 195805 214931 := bstep (se 1 (by rfl) ⟨161198, by rfl⟩ : syracuseStep 214931 = 322397) B322397
theorem B837553 : Blo 195805 837553 := bstep (se 2 (by rfl) ⟨314082, by rfl⟩ : syracuseStep 837553 = 628165) B628165
theorem B1066949 : Blo 195805 1066949 := bstep (se 4 (by rfl) ⟨100026, by rfl⟩ : syracuseStep 1066949 = 200053) B200053
theorem B444401 : Blo 195805 444401 := bstep (se 2 (by rfl) ⟨166650, by rfl⟩ : syracuseStep 444401 = 333301) B333301
theorem B444419 : Blo 195805 444419 := bstep (se 1 (by rfl) ⟨333314, by rfl⟩ : syracuseStep 444419 = 666629) B666629
theorem B444689 : Blo 195805 444689 := bstep (se 2 (by rfl) ⟨166758, by rfl⟩ : syracuseStep 444689 = 333517) B333517
theorem B444707 : Blo 195805 444707 := bstep (se 1 (by rfl) ⟨333530, by rfl⟩ : syracuseStep 444707 = 667061) B667061
theorem B379171 : Blo 195805 379171 := bstep (se 1 (by rfl) ⟨284378, by rfl⟩ : syracuseStep 379171 = 568757) B568757
theorem B379217 : Blo 195805 379217 := bstep (se 2 (by rfl) ⟨142206, by rfl⟩ : syracuseStep 379217 = 284413) B284413
theorem B248179 : Blo 195805 248179 := bstep (se 1 (by rfl) ⟨186134, by rfl⟩ : syracuseStep 248179 = 372269) B372269
theorem B1198469 : Blo 195805 1198469 := bstep (se 4 (by rfl) ⟨112356, by rfl⟩ : syracuseStep 1198469 = 224713) B224713
theorem B674189 : Blo 195805 674189 := bstep (se 3 (by rfl) ⟨126410, by rfl⟩ : syracuseStep 674189 = 252821) B252821
theorem B674243 : Blo 195805 674243 := bstep (se 1 (by rfl) ⟨505682, by rfl⟩ : syracuseStep 674243 = 1011365) B1011365
theorem B248275 : Blo 195805 248275 := bstep (se 1 (by rfl) ⟨186206, by rfl⟩ : syracuseStep 248275 = 372413) B372413
theorem B1133027 : Blo 195805 1133027 := bstep (se 1 (by rfl) ⟨849770, by rfl⟩ : syracuseStep 1133027 = 1699541) B1699541
theorem B1001969 : Blo 195805 1001969 := bstep (se 2 (by rfl) ⟨375738, by rfl⟩ : syracuseStep 1001969 = 751477) B751477
theorem B281075 : Blo 195805 281075 := bstep (se 1 (by rfl) ⟨210806, by rfl⟩ : syracuseStep 281075 = 421613) B421613
theorem B444977 : Blo 195805 444977 := bstep (se 2 (by rfl) ⟨166866, by rfl⟩ : syracuseStep 444977 = 333733) B333733
theorem B444995 : Blo 195805 444995 := bstep (se 1 (by rfl) ⟨333746, by rfl⟩ : syracuseStep 444995 = 667493) B667493
theorem B445265 : Blo 195805 445265 := bstep (se 2 (by rfl) ⟨166974, by rfl⟩ : syracuseStep 445265 = 333949) B333949
theorem B445283 : Blo 195805 445283 := bstep (se 1 (by rfl) ⟨333962, by rfl⟩ : syracuseStep 445283 = 667925) B667925
theorem B871309 : Blo 195805 871309 := bstep (se 3 (by rfl) ⟨163370, by rfl⟩ : syracuseStep 871309 = 326741) B326741
theorem B314275 : Blo 195805 314275 := bstep (se 1 (by rfl) ⟨235706, by rfl⟩ : syracuseStep 314275 = 471413) B471413
theorem B248771 : Blo 195805 248771 := bstep (se 1 (by rfl) ⟨186578, by rfl⟩ : syracuseStep 248771 = 373157) B373157
theorem B2018317 : Blo 195805 2018317 := bstep (se 3 (by rfl) ⟨378434, by rfl⟩ : syracuseStep 2018317 = 756869) B756869
theorem B674893 : Blo 195805 674893 := bstep (se 3 (by rfl) ⟨126542, by rfl⟩ : syracuseStep 674893 = 253085) B253085
theorem B281713 : Blo 195805 281713 := bstep (se 2 (by rfl) ⟨105642, by rfl⟩ : syracuseStep 281713 = 211285) B211285
theorem B445553 : Blo 195805 445553 := bstep (se 2 (by rfl) ⟨167082, by rfl⟩ : syracuseStep 445553 = 334165) B334165
theorem B445571 : Blo 195805 445571 := bstep (se 1 (by rfl) ⟨334178, by rfl⟩ : syracuseStep 445571 = 668357) B668357
theorem B314513 : Blo 195805 314513 := bstep (se 2 (by rfl) ⟨117942, by rfl⟩ : syracuseStep 314513 = 235885) B235885
theorem B281827 : Blo 195805 281827 := bstep (se 1 (by rfl) ⟨211370, by rfl⟩ : syracuseStep 281827 = 422741) B422741
theorem B314723 : Blo 195805 314723 := bstep (se 1 (by rfl) ⟨236042, by rfl⟩ : syracuseStep 314723 = 472085) B472085
theorem B445841 : Blo 195805 445841 := bstep (se 2 (by rfl) ⟨167190, by rfl⟩ : syracuseStep 445841 = 334381) B334381
theorem B445859 : Blo 195805 445859 := bstep (se 1 (by rfl) ⟨334394, by rfl⟩ : syracuseStep 445859 = 668789) B668789
theorem B249475 : Blo 195805 249475 := bstep (se 1 (by rfl) ⟨187106, by rfl⟩ : syracuseStep 249475 = 374213) B374213
theorem B446129 : Blo 195805 446129 := bstep (se 2 (by rfl) ⟨167298, by rfl⟩ : syracuseStep 446129 = 334597) B334597
theorem B446147 : Blo 195805 446147 := bstep (se 1 (by rfl) ⟨334610, by rfl⟩ : syracuseStep 446147 = 669221) B669221
theorem B249571 : Blo 195805 249571 := bstep (se 1 (by rfl) ⟨187178, by rfl⟩ : syracuseStep 249571 = 374357) B374357
theorem B1003427 : Blo 195805 1003427 := bstep (se 1 (by rfl) ⟨752570, by rfl⟩ : syracuseStep 1003427 = 1505141) B1505141
theorem B446417 : Blo 195805 446417 := bstep (se 2 (by rfl) ⟨167406, by rfl⟩ : syracuseStep 446417 = 334813) B334813
theorem B446435 : Blo 195805 446435 := bstep (se 1 (by rfl) ⟨334826, by rfl⟩ : syracuseStep 446435 = 669653) B669653
theorem B315505 : Blo 195805 315505 := bstep (se 2 (by rfl) ⟨118314, by rfl⟩ : syracuseStep 315505 = 236629) B236629
theorem B250067 : Blo 195805 250067 := bstep (se 1 (by rfl) ⟨187550, by rfl⟩ : syracuseStep 250067 = 375101) B375101
theorem B446705 : Blo 195805 446705 := bstep (se 2 (by rfl) ⟨167514, by rfl⟩ : syracuseStep 446705 = 335029) B335029
theorem B446723 : Blo 195805 446723 := bstep (se 1 (by rfl) ⟨335042, by rfl⟩ : syracuseStep 446723 = 670085) B670085
theorem B1134917 : Blo 195805 1134917 := bstep (se 4 (by rfl) ⟨106398, by rfl⟩ : syracuseStep 1134917 = 212797) B212797
theorem B2117987 : Blo 195805 2117987 := bstep (se 1 (by rfl) ⟨1588490, by rfl⟩ : syracuseStep 2117987 = 3176981) B3176981
theorem B446993 : Blo 195805 446993 := bstep (se 2 (by rfl) ⟨167622, by rfl⟩ : syracuseStep 446993 = 335245) B335245
theorem B447011 : Blo 195805 447011 := bstep (se 1 (by rfl) ⟨335258, by rfl⟩ : syracuseStep 447011 = 670517) B670517
theorem B283171 : Blo 195805 283171 := bstep (se 1 (by rfl) ⟨212378, by rfl⟩ : syracuseStep 283171 = 424757) B424757
theorem B1004237 : Blo 195805 1004237 := bstep (se 3 (by rfl) ⟨188294, by rfl⟩ : syracuseStep 1004237 = 376589) B376589
theorem B447281 : Blo 195805 447281 := bstep (se 2 (by rfl) ⟨167730, by rfl⟩ : syracuseStep 447281 = 335461) B335461
theorem B447299 : Blo 195805 447299 := bstep (se 1 (by rfl) ⟨335474, by rfl⟩ : syracuseStep 447299 = 670949) B670949
theorem B1495907 : Blo 195805 1495907 := bstep (se 1 (by rfl) ⟨1121930, by rfl⟩ : syracuseStep 1495907 = 2243861) B2243861
theorem B316307 : Blo 195805 316307 := bstep (se 1 (by rfl) ⟨237230, by rfl⟩ : syracuseStep 316307 = 474461) B474461
theorem B250771 : Blo 195805 250771 := bstep (se 1 (by rfl) ⟨188078, by rfl⟩ : syracuseStep 250771 = 376157) B376157
theorem B250867 : Blo 195805 250867 := bstep (se 1 (by rfl) ⟨188150, by rfl⟩ : syracuseStep 250867 = 376301) B376301
theorem B447569 : Blo 195805 447569 := bstep (se 2 (by rfl) ⟨167838, by rfl⟩ : syracuseStep 447569 = 335677) B335677
theorem B447587 : Blo 195805 447587 := bstep (se 1 (by rfl) ⟨335690, by rfl⟩ : syracuseStep 447587 = 671381) B671381
theorem B808177 : Blo 195805 808177 := bstep (se 2 (by rfl) ⟨303066, by rfl⟩ : syracuseStep 808177 = 606133) B606133
theorem B447857 : Blo 195805 447857 := bstep (se 2 (by rfl) ⟨167946, by rfl⟩ : syracuseStep 447857 = 335893) B335893
theorem B447875 : Blo 195805 447875 := bstep (se 1 (by rfl) ⟨335906, by rfl⟩ : syracuseStep 447875 = 671813) B671813
theorem B316819 : Blo 195805 316819 := bstep (se 1 (by rfl) ⟨237614, by rfl⟩ : syracuseStep 316819 = 475229) B475229
theorem B251363 : Blo 195805 251363 := bstep (se 1 (by rfl) ⟨188522, by rfl⟩ : syracuseStep 251363 = 377045) B377045
theorem B448145 : Blo 195805 448145 := bstep (se 2 (by rfl) ⟨168054, by rfl⟩ : syracuseStep 448145 = 336109) B336109
theorem B284305 : Blo 195805 284305 := bstep (se 2 (by rfl) ⟨106614, by rfl⟩ : syracuseStep 284305 = 213229) B213229
theorem B448163 : Blo 195805 448163 := bstep (se 1 (by rfl) ⟨336122, by rfl⟩ : syracuseStep 448163 = 672245) B672245
theorem B284401 : Blo 195805 284401 := bstep (se 2 (by rfl) ⟨106650, by rfl⟩ : syracuseStep 284401 = 213301) B213301
theorem B2119537 : Blo 195805 2119537 := bstep (se 2 (by rfl) ⟨794826, by rfl⟩ : syracuseStep 2119537 = 1589653) B1589653
theorem B841585 : Blo 195805 841585 := bstep (se 2 (by rfl) ⟨315594, by rfl⟩ : syracuseStep 841585 = 631189) B631189
theorem B448433 : Blo 195805 448433 := bstep (se 2 (by rfl) ⟨168162, by rfl⟩ : syracuseStep 448433 = 336325) B336325
theorem B317363 : Blo 195805 317363 := bstep (se 1 (by rfl) ⟨238022, by rfl⟩ : syracuseStep 317363 = 476045) B476045
theorem B382915 : Blo 195805 382915 := bstep (se 1 (by rfl) ⟨287186, by rfl⟩ : syracuseStep 382915 = 574373) B574373
theorem B448451 : Blo 195805 448451 := bstep (se 1 (by rfl) ⟨336338, by rfl⟩ : syracuseStep 448451 = 672677) B672677
theorem B317537 : Blo 195805 317537 := bstep (se 2 (by rfl) ⟨119076, by rfl⟩ : syracuseStep 317537 = 238153) B238153
theorem B481411 : Blo 195805 481411 := bstep (se 1 (by rfl) ⟨361058, by rfl⟩ : syracuseStep 481411 = 722117) B722117
theorem B252067 : Blo 195805 252067 := bstep (se 1 (by rfl) ⟨189050, by rfl⟩ : syracuseStep 252067 = 378101) B378101
theorem B448721 : Blo 195805 448721 := bstep (se 2 (by rfl) ⟨168270, by rfl⟩ : syracuseStep 448721 = 336541) B336541
theorem B448739 : Blo 195805 448739 := bstep (se 1 (by rfl) ⟨336554, by rfl⟩ : syracuseStep 448739 = 673109) B673109
theorem B252163 : Blo 195805 252163 := bstep (se 1 (by rfl) ⟨189122, by rfl⟩ : syracuseStep 252163 = 378245) B378245
theorem B711011 : Blo 195805 711011 := bstep (se 1 (by rfl) ⟨533258, by rfl⟩ : syracuseStep 711011 = 1066517) B1066517
theorem B449009 : Blo 195805 449009 := bstep (se 2 (by rfl) ⟨168378, by rfl⟩ : syracuseStep 449009 = 336757) B336757
theorem B449027 : Blo 195805 449027 := bstep (se 1 (by rfl) ⟨336770, by rfl⟩ : syracuseStep 449027 = 673541) B673541
theorem B2153101 : Blo 195805 2153101 := bstep (se 3 (by rfl) ⟨403706, by rfl⟩ : syracuseStep 2153101 = 807413) B807413
theorem B1596145 : Blo 195805 1596145 := bstep (se 2 (by rfl) ⟨598554, by rfl⟩ : syracuseStep 1596145 = 1197109) B1197109
theorem B252659 : Blo 195805 252659 := bstep (se 1 (by rfl) ⟨189494, by rfl⟩ : syracuseStep 252659 = 378989) B378989
theorem B449297 : Blo 195805 449297 := bstep (se 2 (by rfl) ⟨168486, by rfl⟩ : syracuseStep 449297 = 336973) B336973
theorem B449315 : Blo 195805 449315 := bstep (se 1 (by rfl) ⟨336986, by rfl⟩ : syracuseStep 449315 = 673973) B673973
theorem B3398597 : Blo 195805 3398597 := bstep (se 4 (by rfl) ⟨318618, by rfl⟩ : syracuseStep 3398597 = 637237) B637237
theorem B908273 : Blo 195805 908273 := bstep (se 2 (by rfl) ⟨340602, by rfl⟩ : syracuseStep 908273 = 681205) B681205
theorem B744461 : Blo 195805 744461 := bstep (se 3 (by rfl) ⟨139586, by rfl⟩ : syracuseStep 744461 = 279173) B279173
theorem B1694789 : Blo 195805 1694789 := bstep (se 4 (by rfl) ⟨158886, by rfl⟩ : syracuseStep 1694789 = 317773) B317773
theorem B220387 : Blo 195805 220387 := bstep (se 1 (by rfl) ⟨165290, by rfl⟩ : syracuseStep 220387 = 330581) B330581
theorem B220531 : Blo 195805 220531 := bstep (se 1 (by rfl) ⟨165398, by rfl⟩ : syracuseStep 220531 = 330797) B330797
theorem B220675 : Blo 195805 220675 := bstep (se 1 (by rfl) ⟨165506, by rfl⟩ : syracuseStep 220675 = 331013) B331013
theorem B318979 : Blo 195805 318979 := bstep (se 1 (by rfl) ⟨239234, by rfl⟩ : syracuseStep 318979 = 478469) B478469
theorem B253459 : Blo 195805 253459 := bstep (se 1 (by rfl) ⟨190094, by rfl⟩ : syracuseStep 253459 = 380189) B380189
theorem B1007153 : Blo 195805 1007153 := bstep (se 2 (by rfl) ⟨377682, by rfl⟩ : syracuseStep 1007153 = 755365) B755365
theorem B220819 : Blo 195805 220819 := bstep (se 1 (by rfl) ⟨165614, by rfl⟩ : syracuseStep 220819 = 331229) B331229
theorem B220963 : Blo 195805 220963 := bstep (se 1 (by rfl) ⟨165722, by rfl⟩ : syracuseStep 220963 = 331445) B331445
theorem B221107 : Blo 195805 221107 := bstep (se 1 (by rfl) ⟨165830, by rfl⟩ : syracuseStep 221107 = 331661) B331661
theorem B221251 : Blo 195805 221251 := bstep (se 1 (by rfl) ⟨165938, by rfl⟩ : syracuseStep 221251 = 331877) B331877
theorem B319555 : Blo 195805 319555 := bstep (se 1 (by rfl) ⟨239666, by rfl⟩ : syracuseStep 319555 = 479333) B479333
theorem B319619 : Blo 195805 319619 := bstep (se 1 (by rfl) ⟨239714, by rfl⟩ : syracuseStep 319619 = 479429) B479429
theorem B286897 : Blo 195805 286897 := bstep (se 2 (by rfl) ⟨107586, by rfl⟩ : syracuseStep 286897 = 215173) B215173
theorem B221395 : Blo 195805 221395 := bstep (se 1 (by rfl) ⟨166046, by rfl⟩ : syracuseStep 221395 = 332093) B332093
theorem B221539 : Blo 195805 221539 := bstep (se 1 (by rfl) ⟨166154, by rfl⟩ : syracuseStep 221539 = 332309) B332309
theorem B221683 : Blo 195805 221683 := bstep (se 1 (by rfl) ⟨166262, by rfl⟩ : syracuseStep 221683 = 332525) B332525
theorem B221827 : Blo 195805 221827 := bstep (se 1 (by rfl) ⟨166370, by rfl⟩ : syracuseStep 221827 = 332741) B332741
theorem B221971 : Blo 195805 221971 := bstep (se 1 (by rfl) ⟨166478, by rfl⟩ : syracuseStep 221971 = 332957) B332957
theorem B910129 : Blo 195805 910129 := bstep (se 2 (by rfl) ⟨341298, by rfl⟩ : syracuseStep 910129 = 682597) B682597
theorem B222115 : Blo 195805 222115 := bstep (se 1 (by rfl) ⟨166586, by rfl⟩ : syracuseStep 222115 = 333173) B333173
theorem B1008611 : Blo 195805 1008611 := bstep (se 1 (by rfl) ⟨756458, by rfl⟩ : syracuseStep 1008611 = 1512917) B1512917
theorem B353315 : Blo 195805 353315 := bstep (se 1 (by rfl) ⟨264986, by rfl⟩ : syracuseStep 353315 = 529973) B529973
theorem B222259 : Blo 195805 222259 := bstep (se 1 (by rfl) ⟨166694, by rfl⟩ : syracuseStep 222259 = 333389) B333389
theorem B222403 : Blo 195805 222403 := bstep (se 1 (by rfl) ⟨166802, by rfl⟩ : syracuseStep 222403 = 333605) B333605
theorem B2876725 : Blo 195805 2876725 := bstep (se 5 (by rfl) ⟨134846, by rfl⟩ : syracuseStep 2876725 = 269693) B269693
theorem B222547 : Blo 195805 222547 := bstep (se 1 (by rfl) ⟨166910, by rfl⟩ : syracuseStep 222547 = 333821) B333821
theorem B845261 : Blo 195805 845261 := bstep (se 3 (by rfl) ⟨158486, by rfl⟩ : syracuseStep 845261 = 316973) B316973
theorem B3630563 : Blo 195805 3630563 := bstep (se 1 (by rfl) ⟨2722922, by rfl⟩ : syracuseStep 3630563 = 5445845) B5445845
theorem B222691 : Blo 195805 222691 := bstep (se 1 (by rfl) ⟨167018, by rfl⟩ : syracuseStep 222691 = 334037) B334037
theorem B321059 : Blo 195805 321059 := bstep (se 1 (by rfl) ⟨240794, by rfl⟩ : syracuseStep 321059 = 481589) B481589
theorem B222835 : Blo 195805 222835 := bstep (se 1 (by rfl) ⟨167126, by rfl⟩ : syracuseStep 222835 = 334253) B334253
theorem B1074865 : Blo 195805 1074865 := bstep (se 2 (by rfl) ⟨403074, by rfl⟩ : syracuseStep 1074865 = 806149) B806149
theorem B419555 : Blo 195805 419555 := bstep (se 1 (by rfl) ⟨314666, by rfl⟩ : syracuseStep 419555 = 629333) B629333
theorem B222979 : Blo 195805 222979 := bstep (se 1 (by rfl) ⟨167234, by rfl⟩ : syracuseStep 222979 = 334469) B334469
theorem B1009421 : Blo 195805 1009421 := bstep (se 3 (by rfl) ⟨189266, by rfl⟩ : syracuseStep 1009421 = 378533) B378533
theorem B747377 : Blo 195805 747377 := bstep (se 2 (by rfl) ⟨280266, by rfl⟩ : syracuseStep 747377 = 560533) B560533
theorem B354179 : Blo 195805 354179 := bstep (se 1 (by rfl) ⟨265634, by rfl⟩ : syracuseStep 354179 = 531269) B531269
theorem B223123 : Blo 195805 223123 := bstep (se 1 (by rfl) ⟨167342, by rfl⟩ : syracuseStep 223123 = 334685) B334685
theorem B714701 : Blo 195805 714701 := bstep (se 3 (by rfl) ⟨134006, by rfl⟩ : syracuseStep 714701 = 268013) B268013
theorem B354289 : Blo 195805 354289 := bstep (se 2 (by rfl) ⟨132858, by rfl⟩ : syracuseStep 354289 = 265717) B265717
theorem B223267 : Blo 195805 223267 := bstep (se 1 (by rfl) ⟨167450, by rfl⟩ : syracuseStep 223267 = 334901) B334901
theorem B1501253 : Blo 195805 1501253 := bstep (se 4 (by rfl) ⟨140742, by rfl⟩ : syracuseStep 1501253 = 281485) B281485
theorem B223411 : Blo 195805 223411 := bstep (se 1 (by rfl) ⟨167558, by rfl⟩ : syracuseStep 223411 = 335117) B335117
theorem B354577 : Blo 195805 354577 := bstep (se 2 (by rfl) ⟨132966, by rfl⟩ : syracuseStep 354577 = 265933) B265933
theorem B223555 : Blo 195805 223555 := bstep (se 1 (by rfl) ⟨167666, by rfl⟩ : syracuseStep 223555 = 335333) B335333
theorem B223651 : Blo 195805 223651 := bstep (se 1 (by rfl) ⟨167738, by rfl⟩ : syracuseStep 223651 = 335477) B335477
theorem B223699 : Blo 195805 223699 := bstep (se 1 (by rfl) ⟨167774, by rfl⟩ : syracuseStep 223699 = 335549) B335549
theorem B518737 : Blo 195805 518737 := bstep (se 2 (by rfl) ⟨194526, by rfl⟩ : syracuseStep 518737 = 389053) B389053
theorem B223843 : Blo 195805 223843 := bstep (se 1 (by rfl) ⟨167882, by rfl⟩ : syracuseStep 223843 = 335765) B335765
theorem B223987 : Blo 195805 223987 := bstep (se 1 (by rfl) ⟨167990, by rfl⟩ : syracuseStep 223987 = 335981) B335981
theorem B224131 : Blo 195805 224131 := bstep (se 1 (by rfl) ⟨168098, by rfl⟩ : syracuseStep 224131 = 336197) B336197
theorem B682897 : Blo 195805 682897 := bstep (se 2 (by rfl) ⟨256086, by rfl⟩ : syracuseStep 682897 = 512173) B512173
theorem B420785 : Blo 195805 420785 := bstep (se 2 (by rfl) ⟨157794, by rfl⟩ : syracuseStep 420785 = 315589) B315589
theorem B224275 : Blo 195805 224275 := bstep (se 1 (by rfl) ⟨168206, by rfl⟩ : syracuseStep 224275 = 336413) B336413
theorem B945229 : Blo 195805 945229 := bstep (se 3 (by rfl) ⟨177230, by rfl⟩ : syracuseStep 945229 = 354461) B354461
theorem B224419 : Blo 195805 224419 := bstep (se 1 (by rfl) ⟨168314, by rfl⟩ : syracuseStep 224419 = 336629) B336629
theorem B748835 : Blo 195805 748835 := bstep (se 1 (by rfl) ⟨561626, by rfl⟩ : syracuseStep 748835 = 1123253) B1123253
theorem B224563 : Blo 195805 224563 := bstep (se 1 (by rfl) ⟨168422, by rfl⟩ : syracuseStep 224563 = 336845) B336845
theorem B224707 : Blo 195805 224707 := bstep (se 1 (by rfl) ⟨168530, by rfl⟩ : syracuseStep 224707 = 337061) B337061
theorem B2551409 : Blo 195805 2551409 := bstep (se 2 (by rfl) ⟨956778, by rfl⟩ : syracuseStep 2551409 = 1913557) B1913557
theorem B421681 : Blo 195805 421681 := bstep (se 2 (by rfl) ⟨158130, by rfl⟩ : syracuseStep 421681 = 316261) B316261
theorem B421699 : Blo 195805 421699 := bstep (se 1 (by rfl) ⟨316274, by rfl⟩ : syracuseStep 421699 = 632549) B632549
theorem B8613773 : Blo 195805 8613773 := bstep (se 3 (by rfl) ⟨1615082, by rfl⟩ : syracuseStep 8613773 = 3230165) B3230165
theorem B749837 : Blo 195805 749837 := bstep (se 3 (by rfl) ⟨140594, by rfl⟩ : syracuseStep 749837 = 281189) B281189
theorem B356977 : Blo 195805 356977 := bstep (se 2 (by rfl) ⟨133866, by rfl⟩ : syracuseStep 356977 = 267733) B267733
theorem B717731 : Blo 195805 717731 := bstep (se 1 (by rfl) ⟨538298, by rfl⟩ : syracuseStep 717731 = 1076597) B1076597
theorem B1274885 : Blo 195805 1274885 := bstep (se 4 (by rfl) ⟨119520, by rfl⟩ : syracuseStep 1274885 = 239041) B239041
theorem B226643 : Blo 195805 226643 := bstep (se 1 (by rfl) ⟨169982, by rfl⟩ : syracuseStep 226643 = 339965) B339965
theorem B849635 : Blo 195805 849635 := bstep (se 1 (by rfl) ⟨637226, by rfl⟩ : syracuseStep 849635 = 1274453) B1274453
theorem B2553869 : Blo 195805 2553869 := bstep (se 3 (by rfl) ⟨478850, by rfl⟩ : syracuseStep 2553869 = 957701) B957701
theorem B423971 : Blo 195805 423971 := bstep (se 1 (by rfl) ⟨317978, by rfl⟩ : syracuseStep 423971 = 635957) B635957
theorem B2291939 : Blo 195805 2291939 := bstep (se 1 (by rfl) ⟨1718954, by rfl⟩ : syracuseStep 2291939 = 3437909) B3437909
theorem B751949 : Blo 195805 751949 := bstep (se 3 (by rfl) ⟨140990, by rfl⟩ : syracuseStep 751949 = 281981) B281981
theorem B424433 : Blo 195805 424433 := bstep (se 2 (by rfl) ⟨159162, by rfl⟩ : syracuseStep 424433 = 318325) B318325
theorem B227827 : Blo 195805 227827 := bstep (se 1 (by rfl) ⟨170870, by rfl⟩ : syracuseStep 227827 = 341741) B341741
theorem B359075 : Blo 195805 359075 := bstep (se 1 (by rfl) ⟨269306, by rfl⟩ : syracuseStep 359075 = 538613) B538613
theorem B293729 : Blo 195805 293729 := bstep (se 2 (by rfl) ⟨110148, by rfl⟩ : syracuseStep 293729 = 220297) B220297
theorem B293747 : Blo 195805 293747 := bstep (se 1 (by rfl) ⟨220310, by rfl⟩ : syracuseStep 293747 = 440621) B440621
theorem B293777 : Blo 195805 293777 := bstep (se 2 (by rfl) ⟨110166, by rfl⟩ : syracuseStep 293777 = 220333) B220333
theorem B293795 : Blo 195805 293795 := bstep (se 1 (by rfl) ⟨220346, by rfl⟩ : syracuseStep 293795 = 440693) B440693
theorem B293825 : Blo 195805 293825 := bstep (se 2 (by rfl) ⟨110184, by rfl⟩ : syracuseStep 293825 = 220369) B220369
theorem B359363 : Blo 195805 359363 := bstep (se 1 (by rfl) ⟨269522, by rfl⟩ : syracuseStep 359363 = 539045) B539045
theorem B1702853 : Blo 195805 1702853 := bstep (se 4 (by rfl) ⟨159642, by rfl⟩ : syracuseStep 1702853 = 319285) B319285
theorem B293843 : Blo 195805 293843 := bstep (se 1 (by rfl) ⟨220382, by rfl⟩ : syracuseStep 293843 = 440765) B440765
theorem B293873 : Blo 195805 293873 := bstep (se 2 (by rfl) ⟨110202, by rfl⟩ : syracuseStep 293873 = 220405) B220405
theorem B293891 : Blo 195805 293891 := bstep (se 1 (by rfl) ⟨220418, by rfl⟩ : syracuseStep 293891 = 440837) B440837
theorem B293921 : Blo 195805 293921 := bstep (se 2 (by rfl) ⟨110220, by rfl⟩ : syracuseStep 293921 = 220441) B220441
theorem B293939 : Blo 195805 293939 := bstep (se 1 (by rfl) ⟨220454, by rfl⟩ : syracuseStep 293939 = 440909) B440909
theorem B293969 : Blo 195805 293969 := bstep (se 2 (by rfl) ⟨110238, by rfl⟩ : syracuseStep 293969 = 220477) B220477
theorem B293987 : Blo 195805 293987 := bstep (se 1 (by rfl) ⟨220490, by rfl⟩ : syracuseStep 293987 = 440981) B440981
theorem B752753 : Blo 195805 752753 := bstep (se 2 (by rfl) ⟨282282, by rfl⟩ : syracuseStep 752753 = 564565) B564565
theorem B294017 : Blo 195805 294017 := bstep (se 2 (by rfl) ⟨110256, by rfl⟩ : syracuseStep 294017 = 220513) B220513
theorem B294035 : Blo 195805 294035 := bstep (se 1 (by rfl) ⟨220526, by rfl⟩ : syracuseStep 294035 = 441053) B441053
theorem B294065 : Blo 195805 294065 := bstep (se 2 (by rfl) ⟨110274, by rfl⟩ : syracuseStep 294065 = 220549) B220549
theorem B294083 : Blo 195805 294083 := bstep (se 1 (by rfl) ⟨220562, by rfl⟩ : syracuseStep 294083 = 441125) B441125
theorem B5078213 : Blo 195805 5078213 := bstep (se 4 (by rfl) ⟨476082, by rfl⟩ : syracuseStep 5078213 = 952165) B952165
theorem B294113 : Blo 195805 294113 := bstep (se 2 (by rfl) ⟨110292, by rfl⟩ : syracuseStep 294113 = 220585) B220585
theorem B195811 : Blo 195805 195811 := bstep (se 1 (by rfl) ⟨146858, by rfl⟩ : syracuseStep 195811 = 293717) B293717
theorem B195827 : Blo 195805 195827 := bstep (se 1 (by rfl) ⟨146870, by rfl⟩ : syracuseStep 195827 = 293741) B293741
theorem B294131 : Blo 195805 294131 := bstep (se 1 (by rfl) ⟨220598, by rfl⟩ : syracuseStep 294131 = 441197) B441197
theorem B195843 : Blo 195805 195843 := bstep (se 1 (by rfl) ⟨146882, by rfl⟩ : syracuseStep 195843 = 293765) B293765
theorem B294161 : Blo 195805 294161 := bstep (se 2 (by rfl) ⟨110310, by rfl⟩ : syracuseStep 294161 = 220621) B220621
theorem B195859 : Blo 195805 195859 := bstep (se 1 (by rfl) ⟨146894, by rfl⟩ : syracuseStep 195859 = 293789) B293789
theorem B195875 : Blo 195805 195875 := bstep (se 1 (by rfl) ⟨146906, by rfl⟩ : syracuseStep 195875 = 293813) B293813
theorem B294179 : Blo 195805 294179 := bstep (se 1 (by rfl) ⟨220634, by rfl⟩ : syracuseStep 294179 = 441269) B441269
theorem B949553 : Blo 195805 949553 := bstep (se 2 (by rfl) ⟨356082, by rfl⟩ : syracuseStep 949553 = 712165) B712165
theorem B195891 : Blo 195805 195891 := bstep (se 1 (by rfl) ⟨146918, by rfl⟩ : syracuseStep 195891 = 293837) B293837
theorem B294209 : Blo 195805 294209 := bstep (se 2 (by rfl) ⟨110328, by rfl⟩ : syracuseStep 294209 = 220657) B220657
theorem B195907 : Blo 195805 195907 := bstep (se 1 (by rfl) ⟨146930, by rfl⟩ : syracuseStep 195907 = 293861) B293861
theorem B195923 : Blo 195805 195923 := bstep (se 1 (by rfl) ⟨146942, by rfl⟩ : syracuseStep 195923 = 293885) B293885
theorem B294227 : Blo 195805 294227 := bstep (se 1 (by rfl) ⟨220670, by rfl⟩ : syracuseStep 294227 = 441341) B441341
theorem B195939 : Blo 195805 195939 := bstep (se 1 (by rfl) ⟨146954, by rfl⟩ : syracuseStep 195939 = 293909) B293909
theorem B294257 : Blo 195805 294257 := bstep (se 2 (by rfl) ⟨110346, by rfl⟩ : syracuseStep 294257 = 220693) B220693
theorem B195955 : Blo 195805 195955 := bstep (se 1 (by rfl) ⟨146966, by rfl⟩ : syracuseStep 195955 = 293933) B293933
theorem B195971 : Blo 195805 195971 := bstep (se 1 (by rfl) ⟨146978, by rfl⟩ : syracuseStep 195971 = 293957) B293957
theorem B294275 : Blo 195805 294275 := bstep (se 1 (by rfl) ⟨220706, by rfl⟩ : syracuseStep 294275 = 441413) B441413
theorem B195987 : Blo 195805 195987 := bstep (se 1 (by rfl) ⟨146990, by rfl⟩ : syracuseStep 195987 = 293981) B293981
theorem B294305 : Blo 195805 294305 := bstep (se 2 (by rfl) ⟨110364, by rfl⟩ : syracuseStep 294305 = 220729) B220729
theorem B196003 : Blo 195805 196003 := bstep (se 1 (by rfl) ⟨147002, by rfl⟩ : syracuseStep 196003 = 294005) B294005
theorem B196019 : Blo 195805 196019 := bstep (se 1 (by rfl) ⟨147014, by rfl⟩ : syracuseStep 196019 = 294029) B294029
theorem B294323 : Blo 195805 294323 := bstep (se 1 (by rfl) ⟨220742, by rfl⟩ : syracuseStep 294323 = 441485) B441485
theorem B196035 : Blo 195805 196035 := bstep (se 1 (by rfl) ⟨147026, by rfl⟩ : syracuseStep 196035 = 294053) B294053
theorem B294353 : Blo 195805 294353 := bstep (se 2 (by rfl) ⟨110382, by rfl⟩ : syracuseStep 294353 = 220765) B220765
theorem B196051 : Blo 195805 196051 := bstep (se 1 (by rfl) ⟨147038, by rfl⟩ : syracuseStep 196051 = 294077) B294077
theorem B196067 : Blo 195805 196067 := bstep (se 1 (by rfl) ⟨147050, by rfl⟩ : syracuseStep 196067 = 294101) B294101
theorem B294371 : Blo 195805 294371 := bstep (se 1 (by rfl) ⟨220778, by rfl⟩ : syracuseStep 294371 = 441557) B441557
theorem B196083 : Blo 195805 196083 := bstep (se 1 (by rfl) ⟨147062, by rfl⟩ : syracuseStep 196083 = 294125) B294125
theorem B294401 : Blo 195805 294401 := bstep (se 2 (by rfl) ⟨110400, by rfl⟩ : syracuseStep 294401 = 220801) B220801
theorem B196099 : Blo 195805 196099 := bstep (se 1 (by rfl) ⟨147074, by rfl⟩ : syracuseStep 196099 = 294149) B294149
theorem B196115 : Blo 195805 196115 := bstep (se 1 (by rfl) ⟨147086, by rfl⟩ : syracuseStep 196115 = 294173) B294173
theorem B294419 : Blo 195805 294419 := bstep (se 1 (by rfl) ⟨220814, by rfl⟩ : syracuseStep 294419 = 441629) B441629
theorem B196131 : Blo 195805 196131 := bstep (se 1 (by rfl) ⟨147098, by rfl⟩ : syracuseStep 196131 = 294197) B294197
theorem B294449 : Blo 195805 294449 := bstep (se 2 (by rfl) ⟨110418, by rfl⟩ : syracuseStep 294449 = 220837) B220837
theorem B196147 : Blo 195805 196147 := bstep (se 1 (by rfl) ⟨147110, by rfl⟩ : syracuseStep 196147 = 294221) B294221
theorem B196163 : Blo 195805 196163 := bstep (se 1 (by rfl) ⟨147122, by rfl⟩ : syracuseStep 196163 = 294245) B294245
theorem B294467 : Blo 195805 294467 := bstep (se 1 (by rfl) ⟨220850, by rfl⟩ : syracuseStep 294467 = 441701) B441701
theorem B196179 : Blo 195805 196179 := bstep (se 1 (by rfl) ⟨147134, by rfl⟩ : syracuseStep 196179 = 294269) B294269
theorem B294497 : Blo 195805 294497 := bstep (se 2 (by rfl) ⟨110436, by rfl⟩ : syracuseStep 294497 = 220873) B220873
theorem B196195 : Blo 195805 196195 := bstep (se 1 (by rfl) ⟨147146, by rfl⟩ : syracuseStep 196195 = 294293) B294293
theorem B2719331 : Blo 195805 2719331 := bstep (se 1 (by rfl) ⟨2039498, by rfl⟩ : syracuseStep 2719331 = 4078997) B4078997
theorem B1703537 : Blo 195805 1703537 := bstep (se 2 (by rfl) ⟨638826, by rfl⟩ : syracuseStep 1703537 = 1277653) B1277653
theorem B196211 : Blo 195805 196211 := bstep (se 1 (by rfl) ⟨147158, by rfl⟩ : syracuseStep 196211 = 294317) B294317
theorem B294515 : Blo 195805 294515 := bstep (se 1 (by rfl) ⟨220886, by rfl⟩ : syracuseStep 294515 = 441773) B441773
theorem B196227 : Blo 195805 196227 := bstep (se 1 (by rfl) ⟨147170, by rfl⟩ : syracuseStep 196227 = 294341) B294341
theorem B2031245 : Blo 195805 2031245 := bstep (se 3 (by rfl) ⟨380858, by rfl⟩ : syracuseStep 2031245 = 761717) B761717
theorem B294545 : Blo 195805 294545 := bstep (se 2 (by rfl) ⟨110454, by rfl⟩ : syracuseStep 294545 = 220909) B220909
theorem B196243 : Blo 195805 196243 := bstep (se 1 (by rfl) ⟨147182, by rfl⟩ : syracuseStep 196243 = 294365) B294365
theorem B196259 : Blo 195805 196259 := bstep (se 1 (by rfl) ⟨147194, by rfl⟩ : syracuseStep 196259 = 294389) B294389
theorem B294563 : Blo 195805 294563 := bstep (se 1 (by rfl) ⟨220922, by rfl⟩ : syracuseStep 294563 = 441845) B441845
theorem B1277603 : Blo 195805 1277603 := bstep (se 1 (by rfl) ⟨958202, by rfl⟩ : syracuseStep 1277603 = 1916405) B1916405
theorem B851633 : Blo 195805 851633 := bstep (se 2 (by rfl) ⟨319362, by rfl⟩ : syracuseStep 851633 = 638725) B638725
theorem B196275 : Blo 195805 196275 := bstep (se 1 (by rfl) ⟨147206, by rfl⟩ : syracuseStep 196275 = 294413) B294413
theorem B294593 : Blo 195805 294593 := bstep (se 2 (by rfl) ⟨110472, by rfl⟩ : syracuseStep 294593 = 220945) B220945
theorem B196291 : Blo 195805 196291 := bstep (se 1 (by rfl) ⟨147218, by rfl⟩ : syracuseStep 196291 = 294437) B294437
theorem B196307 : Blo 195805 196307 := bstep (se 1 (by rfl) ⟨147230, by rfl⟩ : syracuseStep 196307 = 294461) B294461
theorem B294611 : Blo 195805 294611 := bstep (se 1 (by rfl) ⟨220958, by rfl⟩ : syracuseStep 294611 = 441917) B441917
theorem B196323 : Blo 195805 196323 := bstep (se 1 (by rfl) ⟨147242, by rfl⟩ : syracuseStep 196323 = 294485) B294485
theorem B294641 : Blo 195805 294641 := bstep (se 2 (by rfl) ⟨110490, by rfl⟩ : syracuseStep 294641 = 220981) B220981
theorem B196339 : Blo 195805 196339 := bstep (se 1 (by rfl) ⟨147254, by rfl⟩ : syracuseStep 196339 = 294509) B294509
theorem B196355 : Blo 195805 196355 := bstep (se 1 (by rfl) ⟨147266, by rfl⟩ : syracuseStep 196355 = 294533) B294533
theorem B294659 : Blo 195805 294659 := bstep (se 1 (by rfl) ⟨220994, by rfl⟩ : syracuseStep 294659 = 441989) B441989
theorem B425731 : Blo 195805 425731 := bstep (se 1 (by rfl) ⟨319298, by rfl⟩ : syracuseStep 425731 = 638597) B638597
theorem B753421 : Blo 195805 753421 := bstep (se 3 (by rfl) ⟨141266, by rfl⟩ : syracuseStep 753421 = 282533) B282533
theorem B1507085 : Blo 195805 1507085 := bstep (se 3 (by rfl) ⟨282578, by rfl⟩ : syracuseStep 1507085 = 565157) B565157
theorem B196371 : Blo 195805 196371 := bstep (se 1 (by rfl) ⟨147278, by rfl⟩ : syracuseStep 196371 = 294557) B294557
theorem B294689 : Blo 195805 294689 := bstep (se 2 (by rfl) ⟨110508, by rfl⟩ : syracuseStep 294689 = 221017) B221017
theorem B196387 : Blo 195805 196387 := bstep (se 1 (by rfl) ⟨147290, by rfl⟩ : syracuseStep 196387 = 294581) B294581
theorem B196403 : Blo 195805 196403 := bstep (se 1 (by rfl) ⟨147302, by rfl⟩ : syracuseStep 196403 = 294605) B294605
theorem B294707 : Blo 195805 294707 := bstep (se 1 (by rfl) ⟨221030, by rfl⟩ : syracuseStep 294707 = 442061) B442061
theorem B196419 : Blo 195805 196419 := bstep (se 1 (by rfl) ⟨147314, by rfl⟩ : syracuseStep 196419 = 294629) B294629
theorem B294737 : Blo 195805 294737 := bstep (se 2 (by rfl) ⟨110526, by rfl⟩ : syracuseStep 294737 = 221053) B221053
theorem B196435 : Blo 195805 196435 := bstep (se 1 (by rfl) ⟨147326, by rfl⟩ : syracuseStep 196435 = 294653) B294653
theorem B196451 : Blo 195805 196451 := bstep (se 1 (by rfl) ⟨147338, by rfl⟩ : syracuseStep 196451 = 294677) B294677
theorem B294755 : Blo 195805 294755 := bstep (se 1 (by rfl) ⟨221066, by rfl⟩ : syracuseStep 294755 = 442133) B442133
theorem B196467 : Blo 195805 196467 := bstep (se 1 (by rfl) ⟨147350, by rfl⟩ : syracuseStep 196467 = 294701) B294701
theorem B294785 : Blo 195805 294785 := bstep (se 2 (by rfl) ⟨110544, by rfl⟩ : syracuseStep 294785 = 221089) B221089
theorem B196483 : Blo 195805 196483 := bstep (se 1 (by rfl) ⟨147362, by rfl⟩ : syracuseStep 196483 = 294725) B294725
theorem B196499 : Blo 195805 196499 := bstep (se 1 (by rfl) ⟨147374, by rfl⟩ : syracuseStep 196499 = 294749) B294749
theorem B294803 : Blo 195805 294803 := bstep (se 1 (by rfl) ⟨221102, by rfl⟩ : syracuseStep 294803 = 442205) B442205
theorem B196515 : Blo 195805 196515 := bstep (se 1 (by rfl) ⟨147386, by rfl⟩ : syracuseStep 196515 = 294773) B294773
theorem B294833 : Blo 195805 294833 := bstep (se 2 (by rfl) ⟨110562, by rfl⟩ : syracuseStep 294833 = 221125) B221125
theorem B196531 : Blo 195805 196531 := bstep (se 1 (by rfl) ⟨147398, by rfl⟩ : syracuseStep 196531 = 294797) B294797
theorem B196547 : Blo 195805 196547 := bstep (se 1 (by rfl) ⟨147410, by rfl⟩ : syracuseStep 196547 = 294821) B294821
theorem B294851 : Blo 195805 294851 := bstep (se 1 (by rfl) ⟨221138, by rfl⟩ : syracuseStep 294851 = 442277) B442277
theorem B196563 : Blo 195805 196563 := bstep (se 1 (by rfl) ⟨147422, by rfl⟩ : syracuseStep 196563 = 294845) B294845
theorem B294881 : Blo 195805 294881 := bstep (se 2 (by rfl) ⟨110580, by rfl⟩ : syracuseStep 294881 = 221161) B221161
theorem B1343459 : Blo 195805 1343459 := bstep (se 1 (by rfl) ⟨1007594, by rfl⟩ : syracuseStep 1343459 = 2015189) B2015189
theorem B196579 : Blo 195805 196579 := bstep (se 1 (by rfl) ⟨147434, by rfl⟩ : syracuseStep 196579 = 294869) B294869
theorem B196595 : Blo 195805 196595 := bstep (se 1 (by rfl) ⟨147446, by rfl⟩ : syracuseStep 196595 = 294893) B294893
theorem B294899 : Blo 195805 294899 := bstep (se 1 (by rfl) ⟨221174, by rfl⟩ : syracuseStep 294899 = 442349) B442349
theorem B294923 : Blo 195805 294923 := bstep (se 1 (by rfl) ⟨221192, by rfl⟩ : syracuseStep 294923 = 442385) B442385
theorem B196619 : Blo 195805 196619 := bstep (se 1 (by rfl) ⟨147464, by rfl⟩ : syracuseStep 196619 = 294929) B294929
theorem B294935 : Blo 195805 294935 := bstep (se 1 (by rfl) ⟨221201, by rfl⟩ : syracuseStep 294935 = 442403) B442403
theorem B196631 : Blo 195805 196631 := bstep (se 1 (by rfl) ⟨147473, by rfl⟩ : syracuseStep 196631 = 294947) B294947
theorem B196651 : Blo 195805 196651 := bstep (se 1 (by rfl) ⟨147488, by rfl⟩ : syracuseStep 196651 = 294977) B294977
theorem B196663 : Blo 195805 196663 := bstep (se 1 (by rfl) ⟨147497, by rfl⟩ : syracuseStep 196663 = 294995) B294995
theorem B196683 : Blo 195805 196683 := bstep (se 1 (by rfl) ⟨147512, by rfl⟩ : syracuseStep 196683 = 295025) B295025
theorem B196695 : Blo 195805 196695 := bstep (se 1 (by rfl) ⟨147521, by rfl⟩ : syracuseStep 196695 = 295043) B295043
theorem B295001 : Blo 195805 295001 := bstep (se 2 (by rfl) ⟨110625, by rfl⟩ : syracuseStep 295001 = 221251) B221251
theorem B426073 : Blo 195805 426073 := bstep (se 2 (by rfl) ⟨159777, by rfl⟩ : syracuseStep 426073 = 319555) B319555
theorem B196715 : Blo 195805 196715 := bstep (se 1 (by rfl) ⟨147536, by rfl⟩ : syracuseStep 196715 = 295073) B295073
theorem B196727 : Blo 195805 196727 := bstep (se 1 (by rfl) ⟨147545, by rfl⟩ : syracuseStep 196727 = 295091) B295091
theorem B196747 : Blo 195805 196747 := bstep (se 1 (by rfl) ⟨147560, by rfl⟩ : syracuseStep 196747 = 295121) B295121
theorem B196759 : Blo 195805 196759 := bstep (se 1 (by rfl) ⟨147569, by rfl⟩ : syracuseStep 196759 = 295139) B295139
theorem B196779 : Blo 195805 196779 := bstep (se 1 (by rfl) ⟨147584, by rfl⟩ : syracuseStep 196779 = 295169) B295169
theorem B196791 : Blo 195805 196791 := bstep (se 1 (by rfl) ⟨147593, by rfl⟩ : syracuseStep 196791 = 295187) B295187
theorem B295115 : Blo 195805 295115 := bstep (se 1 (by rfl) ⟨221336, by rfl⟩ : syracuseStep 295115 = 442673) B442673
theorem B196811 : Blo 195805 196811 := bstep (se 1 (by rfl) ⟨147608, by rfl⟩ : syracuseStep 196811 = 295217) B295217
theorem B295127 : Blo 195805 295127 := bstep (se 1 (by rfl) ⟨221345, by rfl⟩ : syracuseStep 295127 = 442691) B442691
theorem B196823 : Blo 195805 196823 := bstep (se 1 (by rfl) ⟨147617, by rfl⟩ : syracuseStep 196823 = 295235) B295235
theorem B196843 : Blo 195805 196843 := bstep (se 1 (by rfl) ⟨147632, by rfl⟩ : syracuseStep 196843 = 295265) B295265
theorem B196855 : Blo 195805 196855 := bstep (se 1 (by rfl) ⟨147641, by rfl⟩ : syracuseStep 196855 = 295283) B295283
theorem B196875 : Blo 195805 196875 := bstep (se 1 (by rfl) ⟨147656, by rfl⟩ : syracuseStep 196875 = 295313) B295313
theorem B196887 : Blo 195805 196887 := bstep (se 1 (by rfl) ⟨147665, by rfl⟩ : syracuseStep 196887 = 295331) B295331
theorem B295193 : Blo 195805 295193 := bstep (se 2 (by rfl) ⟨110697, by rfl⟩ : syracuseStep 295193 = 221395) B221395
theorem B196907 : Blo 195805 196907 := bstep (se 1 (by rfl) ⟨147680, by rfl⟩ : syracuseStep 196907 = 295361) B295361
theorem B196919 : Blo 195805 196919 := bstep (se 1 (by rfl) ⟨147689, by rfl⟩ : syracuseStep 196919 = 295379) B295379
theorem B196939 : Blo 195805 196939 := bstep (se 1 (by rfl) ⟨147704, by rfl⟩ : syracuseStep 196939 = 295409) B295409
theorem B196951 : Blo 195805 196951 := bstep (se 1 (by rfl) ⟨147713, by rfl⟩ : syracuseStep 196951 = 295427) B295427
theorem B196971 : Blo 195805 196971 := bstep (se 1 (by rfl) ⟨147728, by rfl⟩ : syracuseStep 196971 = 295457) B295457
theorem B196983 : Blo 195805 196983 := bstep (se 1 (by rfl) ⟨147737, by rfl⟩ : syracuseStep 196983 = 295475) B295475
theorem B295307 : Blo 195805 295307 := bstep (se 1 (by rfl) ⟨221480, by rfl⟩ : syracuseStep 295307 = 442961) B442961
theorem B197003 : Blo 195805 197003 := bstep (se 1 (by rfl) ⟨147752, by rfl⟩ : syracuseStep 197003 = 295505) B295505
theorem B295319 : Blo 195805 295319 := bstep (se 1 (by rfl) ⟨221489, by rfl⟩ : syracuseStep 295319 = 442979) B442979
theorem B197015 : Blo 195805 197015 := bstep (se 1 (by rfl) ⟨147761, by rfl⟩ : syracuseStep 197015 = 295523) B295523
theorem B197035 : Blo 195805 197035 := bstep (se 1 (by rfl) ⟨147776, by rfl⟩ : syracuseStep 197035 = 295553) B295553
theorem B197047 : Blo 195805 197047 := bstep (se 1 (by rfl) ⟨147785, by rfl⟩ : syracuseStep 197047 = 295571) B295571
theorem B197067 : Blo 195805 197067 := bstep (se 1 (by rfl) ⟨147800, by rfl⟩ : syracuseStep 197067 = 295601) B295601
theorem B197079 : Blo 195805 197079 := bstep (se 1 (by rfl) ⟨147809, by rfl⟩ : syracuseStep 197079 = 295619) B295619
theorem B295385 : Blo 195805 295385 := bstep (se 2 (by rfl) ⟨110769, by rfl⟩ : syracuseStep 295385 = 221539) B221539
theorem B197099 : Blo 195805 197099 := bstep (se 1 (by rfl) ⟨147824, by rfl⟩ : syracuseStep 197099 = 295649) B295649
theorem B197111 : Blo 195805 197111 := bstep (se 1 (by rfl) ⟨147833, by rfl⟩ : syracuseStep 197111 = 295667) B295667
theorem B197131 : Blo 195805 197131 := bstep (se 1 (by rfl) ⟨147848, by rfl⟩ : syracuseStep 197131 = 295697) B295697
theorem B197143 : Blo 195805 197143 := bstep (se 1 (by rfl) ⟨147857, by rfl⟩ : syracuseStep 197143 = 295715) B295715
theorem B197163 : Blo 195805 197163 := bstep (se 1 (by rfl) ⟨147872, by rfl⟩ : syracuseStep 197163 = 295745) B295745
theorem B197175 : Blo 195805 197175 := bstep (se 1 (by rfl) ⟨147881, by rfl⟩ : syracuseStep 197175 = 295763) B295763
theorem B295499 : Blo 195805 295499 := bstep (se 1 (by rfl) ⟨221624, by rfl⟩ : syracuseStep 295499 = 443249) B443249
theorem B197195 : Blo 195805 197195 := bstep (se 1 (by rfl) ⟨147896, by rfl⟩ : syracuseStep 197195 = 295793) B295793
theorem B295511 : Blo 195805 295511 := bstep (se 1 (by rfl) ⟨221633, by rfl⟩ : syracuseStep 295511 = 443267) B443267
theorem B197207 : Blo 195805 197207 := bstep (se 1 (by rfl) ⟨147905, by rfl⟩ : syracuseStep 197207 = 295811) B295811
theorem B197227 : Blo 195805 197227 := bstep (se 1 (by rfl) ⟨147920, by rfl⟩ : syracuseStep 197227 = 295841) B295841
theorem B197239 : Blo 195805 197239 := bstep (se 1 (by rfl) ⟨147929, by rfl⟩ : syracuseStep 197239 = 295859) B295859
theorem B197259 : Blo 195805 197259 := bstep (se 1 (by rfl) ⟨147944, by rfl⟩ : syracuseStep 197259 = 295889) B295889
theorem B197271 : Blo 195805 197271 := bstep (se 1 (by rfl) ⟨147953, by rfl⟩ : syracuseStep 197271 = 295907) B295907
theorem B950935 : Blo 195805 950935 := bstep (se 1 (by rfl) ⟨713201, by rfl⟩ : syracuseStep 950935 = 1426403) B1426403
theorem B295577 : Blo 195805 295577 := bstep (se 2 (by rfl) ⟨110841, by rfl⟩ : syracuseStep 295577 = 221683) B221683
theorem B197291 : Blo 195805 197291 := bstep (se 1 (by rfl) ⟨147968, by rfl⟩ : syracuseStep 197291 = 295937) B295937
theorem B197303 : Blo 195805 197303 := bstep (se 1 (by rfl) ⟨147977, by rfl⟩ : syracuseStep 197303 = 295955) B295955
theorem B197323 : Blo 195805 197323 := bstep (se 1 (by rfl) ⟨147992, by rfl⟩ : syracuseStep 197323 = 295985) B295985
theorem B754379 : Blo 195805 754379 := bstep (se 1 (by rfl) ⟨565784, by rfl⟩ : syracuseStep 754379 = 1131569) B1131569
theorem B197335 : Blo 195805 197335 := bstep (se 1 (by rfl) ⟨148001, by rfl⟩ : syracuseStep 197335 = 296003) B296003
theorem B1508057 : Blo 195805 1508057 := bstep (se 2 (by rfl) ⟨565521, by rfl⟩ : syracuseStep 1508057 = 1131043) B1131043
theorem B754393 : Blo 195805 754393 := bstep (se 2 (by rfl) ⟨282897, by rfl⟩ : syracuseStep 754393 = 565795) B565795
theorem B197355 : Blo 195805 197355 := bstep (se 1 (by rfl) ⟨148016, by rfl⟩ : syracuseStep 197355 = 296033) B296033
theorem B197367 : Blo 195805 197367 := bstep (se 1 (by rfl) ⟨148025, by rfl⟩ : syracuseStep 197367 = 296051) B296051
theorem B295691 : Blo 195805 295691 := bstep (se 1 (by rfl) ⟨221768, by rfl⟩ : syracuseStep 295691 = 443537) B443537
theorem B197387 : Blo 195805 197387 := bstep (se 1 (by rfl) ⟨148040, by rfl⟩ : syracuseStep 197387 = 296081) B296081
theorem B295703 : Blo 195805 295703 := bstep (se 1 (by rfl) ⟨221777, by rfl⟩ : syracuseStep 295703 = 443555) B443555
theorem B197399 : Blo 195805 197399 := bstep (se 1 (by rfl) ⟨148049, by rfl⟩ : syracuseStep 197399 = 296099) B296099
theorem B197419 : Blo 195805 197419 := bstep (se 1 (by rfl) ⟨148064, by rfl⟩ : syracuseStep 197419 = 296129) B296129
theorem B197431 : Blo 195805 197431 := bstep (se 1 (by rfl) ⟨148073, by rfl⟩ : syracuseStep 197431 = 296147) B296147
theorem B197451 : Blo 195805 197451 := bstep (se 1 (by rfl) ⟨148088, by rfl⟩ : syracuseStep 197451 = 296177) B296177
theorem B197463 : Blo 195805 197463 := bstep (se 1 (by rfl) ⟨148097, by rfl⟩ : syracuseStep 197463 = 296195) B296195
theorem B295769 : Blo 195805 295769 := bstep (se 2 (by rfl) ⟨110913, by rfl⟩ : syracuseStep 295769 = 221827) B221827
theorem B197483 : Blo 195805 197483 := bstep (se 1 (by rfl) ⟨148112, by rfl⟩ : syracuseStep 197483 = 296225) B296225
theorem B197495 : Blo 195805 197495 := bstep (se 1 (by rfl) ⟨148121, by rfl⟩ : syracuseStep 197495 = 296243) B296243
theorem B197515 : Blo 195805 197515 := bstep (se 1 (by rfl) ⟨148136, by rfl⟩ : syracuseStep 197515 = 296273) B296273
theorem B197527 : Blo 195805 197527 := bstep (se 1 (by rfl) ⟨148145, by rfl⟩ : syracuseStep 197527 = 296291) B296291
theorem B197547 : Blo 195805 197547 := bstep (se 1 (by rfl) ⟨148160, by rfl⟩ : syracuseStep 197547 = 296321) B296321
theorem B197559 : Blo 195805 197559 := bstep (se 1 (by rfl) ⟨148169, by rfl⟩ : syracuseStep 197559 = 296339) B296339
theorem B295883 : Blo 195805 295883 := bstep (se 1 (by rfl) ⟨221912, by rfl⟩ : syracuseStep 295883 = 443825) B443825
theorem B197579 : Blo 195805 197579 := bstep (se 1 (by rfl) ⟨148184, by rfl⟩ : syracuseStep 197579 = 296369) B296369
theorem B295895 : Blo 195805 295895 := bstep (se 1 (by rfl) ⟨221921, by rfl⟩ : syracuseStep 295895 = 443843) B443843
theorem B197591 : Blo 195805 197591 := bstep (se 1 (by rfl) ⟨148193, by rfl⟩ : syracuseStep 197591 = 296387) B296387
theorem B197611 : Blo 195805 197611 := bstep (se 1 (by rfl) ⟨148208, by rfl⟩ : syracuseStep 197611 = 296417) B296417
theorem B197623 : Blo 195805 197623 := bstep (se 1 (by rfl) ⟨148217, by rfl⟩ : syracuseStep 197623 = 296435) B296435
theorem B197643 : Blo 195805 197643 := bstep (se 1 (by rfl) ⟨148232, by rfl⟩ : syracuseStep 197643 = 296465) B296465
theorem B197655 : Blo 195805 197655 := bstep (se 1 (by rfl) ⟨148241, by rfl⟩ : syracuseStep 197655 = 296483) B296483
theorem B295961 : Blo 195805 295961 := bstep (se 2 (by rfl) ⟨110985, by rfl⟩ : syracuseStep 295961 = 221971) B221971
theorem B197675 : Blo 195805 197675 := bstep (se 1 (by rfl) ⟨148256, by rfl⟩ : syracuseStep 197675 = 296513) B296513
theorem B197687 : Blo 195805 197687 := bstep (se 1 (by rfl) ⟨148265, by rfl⟩ : syracuseStep 197687 = 296531) B296531
theorem B1213505 : Blo 195805 1213505 := bstep (se 2 (by rfl) ⟨455064, by rfl⟩ : syracuseStep 1213505 = 910129) B910129
theorem B197707 : Blo 195805 197707 := bstep (se 1 (by rfl) ⟨148280, by rfl⟩ : syracuseStep 197707 = 296561) B296561
theorem B853067 : Blo 195805 853067 := bstep (se 1 (by rfl) ⟨639800, by rfl⟩ : syracuseStep 853067 = 1279601) B1279601
theorem B197719 : Blo 195805 197719 := bstep (se 1 (by rfl) ⟨148289, by rfl⟩ : syracuseStep 197719 = 296579) B296579
theorem B197739 : Blo 195805 197739 := bstep (se 1 (by rfl) ⟨148304, by rfl⟩ : syracuseStep 197739 = 296609) B296609
theorem B197751 : Blo 195805 197751 := bstep (se 1 (by rfl) ⟨148313, by rfl⟩ : syracuseStep 197751 = 296627) B296627
theorem B296075 : Blo 195805 296075 := bstep (se 1 (by rfl) ⟨222056, by rfl⟩ : syracuseStep 296075 = 444113) B444113
theorem B197771 : Blo 195805 197771 := bstep (se 1 (by rfl) ⟨148328, by rfl⟩ : syracuseStep 197771 = 296657) B296657
theorem B296087 : Blo 195805 296087 := bstep (se 1 (by rfl) ⟨222065, by rfl⟩ : syracuseStep 296087 = 444131) B444131
theorem B197783 : Blo 195805 197783 := bstep (se 1 (by rfl) ⟨148337, by rfl⟩ : syracuseStep 197783 = 296675) B296675
theorem B197803 : Blo 195805 197803 := bstep (se 1 (by rfl) ⟨148352, by rfl⟩ : syracuseStep 197803 = 296705) B296705
theorem B197815 : Blo 195805 197815 := bstep (se 1 (by rfl) ⟨148361, by rfl⟩ : syracuseStep 197815 = 296723) B296723
theorem B394433 : Blo 195805 394433 := bstep (se 2 (by rfl) ⟨147912, by rfl⟩ : syracuseStep 394433 = 295825) B295825
theorem B197835 : Blo 195805 197835 := bstep (se 1 (by rfl) ⟨148376, by rfl⟩ : syracuseStep 197835 = 296753) B296753
theorem B197847 : Blo 195805 197847 := bstep (se 1 (by rfl) ⟨148385, by rfl⟩ : syracuseStep 197847 = 296771) B296771
theorem B296153 : Blo 195805 296153 := bstep (se 2 (by rfl) ⟨111057, by rfl⟩ : syracuseStep 296153 = 222115) B222115
theorem B197867 : Blo 195805 197867 := bstep (se 1 (by rfl) ⟨148400, by rfl⟩ : syracuseStep 197867 = 296801) B296801
theorem B197879 : Blo 195805 197879 := bstep (se 1 (by rfl) ⟨148409, by rfl⟩ : syracuseStep 197879 = 296819) B296819
theorem B197899 : Blo 195805 197899 := bstep (se 1 (by rfl) ⟨148424, by rfl⟩ : syracuseStep 197899 = 296849) B296849
theorem B197911 : Blo 195805 197911 := bstep (se 1 (by rfl) ⟨148433, by rfl⟩ : syracuseStep 197911 = 296867) B296867
theorem B197931 : Blo 195805 197931 := bstep (se 1 (by rfl) ⟨148448, by rfl⟩ : syracuseStep 197931 = 296897) B296897
theorem B197943 : Blo 195805 197943 := bstep (se 1 (by rfl) ⟨148457, by rfl⟩ : syracuseStep 197943 = 296915) B296915
theorem B296267 : Blo 195805 296267 := bstep (se 1 (by rfl) ⟨222200, by rfl⟩ : syracuseStep 296267 = 444401) B444401
theorem B197963 : Blo 195805 197963 := bstep (se 1 (by rfl) ⟨148472, by rfl⟩ : syracuseStep 197963 = 296945) B296945
theorem B296279 : Blo 195805 296279 := bstep (se 1 (by rfl) ⟨222209, by rfl⟩ : syracuseStep 296279 = 444419) B444419
theorem B197975 : Blo 195805 197975 := bstep (se 1 (by rfl) ⟨148481, by rfl⟩ : syracuseStep 197975 = 296963) B296963
theorem B197995 : Blo 195805 197995 := bstep (se 1 (by rfl) ⟨148496, by rfl⟩ : syracuseStep 197995 = 296993) B296993
theorem B198007 : Blo 195805 198007 := bstep (se 1 (by rfl) ⟨148505, by rfl⟩ : syracuseStep 198007 = 297011) B297011
theorem B198027 : Blo 195805 198027 := bstep (se 1 (by rfl) ⟨148520, by rfl⟩ : syracuseStep 198027 = 297041) B297041
theorem B198039 : Blo 195805 198039 := bstep (se 1 (by rfl) ⟨148529, by rfl⟩ : syracuseStep 198039 = 297059) B297059
theorem B296345 : Blo 195805 296345 := bstep (se 2 (by rfl) ⟨111129, by rfl⟩ : syracuseStep 296345 = 222259) B222259
theorem B198059 : Blo 195805 198059 := bstep (se 1 (by rfl) ⟨148544, by rfl⟩ : syracuseStep 198059 = 297089) B297089
theorem B198071 : Blo 195805 198071 := bstep (se 1 (by rfl) ⟨148553, by rfl⟩ : syracuseStep 198071 = 297107) B297107
theorem B198091 : Blo 195805 198091 := bstep (se 1 (by rfl) ⟨148568, by rfl⟩ : syracuseStep 198091 = 297137) B297137
theorem B198103 : Blo 195805 198103 := bstep (se 1 (by rfl) ⟨148577, by rfl⟩ : syracuseStep 198103 = 297155) B297155
theorem B198123 : Blo 195805 198123 := bstep (se 1 (by rfl) ⟨148592, by rfl⟩ : syracuseStep 198123 = 297185) B297185
theorem B198135 : Blo 195805 198135 := bstep (se 1 (by rfl) ⟨148601, by rfl⟩ : syracuseStep 198135 = 297203) B297203
theorem B296459 : Blo 195805 296459 := bstep (se 1 (by rfl) ⟨222344, by rfl⟩ : syracuseStep 296459 = 444689) B444689
theorem B198155 : Blo 195805 198155 := bstep (se 1 (by rfl) ⟨148616, by rfl⟩ : syracuseStep 198155 = 297233) B297233
theorem B296471 : Blo 195805 296471 := bstep (se 1 (by rfl) ⟨222353, by rfl⟩ : syracuseStep 296471 = 444707) B444707
theorem B198167 : Blo 195805 198167 := bstep (se 1 (by rfl) ⟨148625, by rfl⟩ : syracuseStep 198167 = 297251) B297251
theorem B198187 : Blo 195805 198187 := bstep (se 1 (by rfl) ⟨148640, by rfl⟩ : syracuseStep 198187 = 297281) B297281
theorem B198199 : Blo 195805 198199 := bstep (se 1 (by rfl) ⟨148649, by rfl⟩ : syracuseStep 198199 = 297299) B297299
theorem B198219 : Blo 195805 198219 := bstep (se 1 (by rfl) ⟨148664, by rfl⟩ : syracuseStep 198219 = 297329) B297329
theorem B198231 : Blo 195805 198231 := bstep (se 1 (by rfl) ⟨148673, by rfl⟩ : syracuseStep 198231 = 297347) B297347
theorem B296537 : Blo 195805 296537 := bstep (se 2 (by rfl) ⟨111201, by rfl⟩ : syracuseStep 296537 = 222403) B222403
theorem B198251 : Blo 195805 198251 := bstep (se 1 (by rfl) ⟨148688, by rfl⟩ : syracuseStep 198251 = 297377) B297377
theorem B198263 : Blo 195805 198263 := bstep (se 1 (by rfl) ⟨148697, by rfl⟩ : syracuseStep 198263 = 297395) B297395
theorem B198283 : Blo 195805 198283 := bstep (se 1 (by rfl) ⟨148712, by rfl⟩ : syracuseStep 198283 = 297425) B297425
theorem B198295 : Blo 195805 198295 := bstep (se 1 (by rfl) ⟨148721, by rfl⟩ : syracuseStep 198295 = 297443) B297443
theorem B755351 : Blo 195805 755351 := bstep (se 1 (by rfl) ⟨566513, by rfl⟩ : syracuseStep 755351 = 1133027) B1133027
theorem B198315 : Blo 195805 198315 := bstep (se 1 (by rfl) ⟨148736, by rfl⟩ : syracuseStep 198315 = 297473) B297473
theorem B198327 : Blo 195805 198327 := bstep (se 1 (by rfl) ⟨148745, by rfl⟩ : syracuseStep 198327 = 297491) B297491
theorem B296651 : Blo 195805 296651 := bstep (se 1 (by rfl) ⟨222488, by rfl⟩ : syracuseStep 296651 = 444977) B444977
theorem B198347 : Blo 195805 198347 := bstep (se 1 (by rfl) ⟨148760, by rfl⟩ : syracuseStep 198347 = 297521) B297521
theorem B296663 : Blo 195805 296663 := bstep (se 1 (by rfl) ⟨222497, by rfl⟩ : syracuseStep 296663 = 444995) B444995
theorem B198359 : Blo 195805 198359 := bstep (se 1 (by rfl) ⟨148769, by rfl⟩ : syracuseStep 198359 = 297539) B297539
theorem B198379 : Blo 195805 198379 := bstep (se 1 (by rfl) ⟨148784, by rfl⟩ : syracuseStep 198379 = 297569) B297569
theorem B3835633 : Blo 195805 3835633 := bstep (se 2 (by rfl) ⟨1438362, by rfl⟩ : syracuseStep 3835633 = 2876725) B2876725
theorem B198391 : Blo 195805 198391 := bstep (se 1 (by rfl) ⟨148793, by rfl⟩ : syracuseStep 198391 = 297587) B297587
theorem B198411 : Blo 195805 198411 := bstep (se 1 (by rfl) ⟨148808, by rfl⟩ : syracuseStep 198411 = 297617) B297617
theorem B198423 : Blo 195805 198423 := bstep (se 1 (by rfl) ⟨148817, by rfl⟩ : syracuseStep 198423 = 297635) B297635
theorem B296729 : Blo 195805 296729 := bstep (se 2 (by rfl) ⟨111273, by rfl⟩ : syracuseStep 296729 = 222547) B222547
theorem B198443 : Blo 195805 198443 := bstep (se 1 (by rfl) ⟨148832, by rfl⟩ : syracuseStep 198443 = 297665) B297665
theorem B198455 : Blo 195805 198455 := bstep (se 1 (by rfl) ⟨148841, by rfl⟩ : syracuseStep 198455 = 297683) B297683
theorem B198475 : Blo 195805 198475 := bstep (se 1 (by rfl) ⟨148856, by rfl⟩ : syracuseStep 198475 = 297713) B297713
theorem B198487 : Blo 195805 198487 := bstep (se 1 (by rfl) ⟨148865, by rfl⟩ : syracuseStep 198487 = 297731) B297731
theorem B198507 : Blo 195805 198507 := bstep (se 1 (by rfl) ⟨148880, by rfl⟩ : syracuseStep 198507 = 297761) B297761
theorem B198519 : Blo 195805 198519 := bstep (se 1 (by rfl) ⟨148889, by rfl⟩ : syracuseStep 198519 = 297779) B297779
theorem B296843 : Blo 195805 296843 := bstep (se 1 (by rfl) ⟨222632, by rfl⟩ : syracuseStep 296843 = 445265) B445265
theorem B198539 : Blo 195805 198539 := bstep (se 1 (by rfl) ⟨148904, by rfl⟩ : syracuseStep 198539 = 297809) B297809
theorem B296855 : Blo 195805 296855 := bstep (se 1 (by rfl) ⟨222641, by rfl⟩ : syracuseStep 296855 = 445283) B445283
theorem B198551 : Blo 195805 198551 := bstep (se 1 (by rfl) ⟨148913, by rfl⟩ : syracuseStep 198551 = 297827) B297827
theorem B198571 : Blo 195805 198571 := bstep (se 1 (by rfl) ⟨148928, by rfl⟩ : syracuseStep 198571 = 297857) B297857
theorem B198583 : Blo 195805 198583 := bstep (se 1 (by rfl) ⟨148937, by rfl⟩ : syracuseStep 198583 = 297875) B297875
theorem B198603 : Blo 195805 198603 := bstep (se 1 (by rfl) ⟨148952, by rfl⟩ : syracuseStep 198603 = 297905) B297905
theorem B198615 : Blo 195805 198615 := bstep (se 1 (by rfl) ⟨148961, by rfl⟩ : syracuseStep 198615 = 297923) B297923
theorem B296921 : Blo 195805 296921 := bstep (se 2 (by rfl) ⟨111345, by rfl⟩ : syracuseStep 296921 = 222691) B222691
theorem B198635 : Blo 195805 198635 := bstep (se 1 (by rfl) ⟨148976, by rfl⟩ : syracuseStep 198635 = 297953) B297953
theorem B198647 : Blo 195805 198647 := bstep (se 1 (by rfl) ⟨148985, by rfl⟩ : syracuseStep 198647 = 297971) B297971
theorem B198667 : Blo 195805 198667 := bstep (se 1 (by rfl) ⟨149000, by rfl⟩ : syracuseStep 198667 = 298001) B298001
theorem B854039 : Blo 195805 854039 := bstep (se 1 (by rfl) ⟨640529, by rfl⟩ : syracuseStep 854039 = 1281059) B1281059
theorem B198679 : Blo 195805 198679 := bstep (se 1 (by rfl) ⟨149009, by rfl⟩ : syracuseStep 198679 = 298019) B298019
theorem B198699 : Blo 195805 198699 := bstep (se 1 (by rfl) ⟨149024, by rfl⟩ : syracuseStep 198699 = 298049) B298049
theorem B198711 : Blo 195805 198711 := bstep (se 1 (by rfl) ⟨149033, by rfl⟩ : syracuseStep 198711 = 298067) B298067
theorem B297035 : Blo 195805 297035 := bstep (se 1 (by rfl) ⟨222776, by rfl⟩ : syracuseStep 297035 = 445553) B445553
theorem B198731 : Blo 195805 198731 := bstep (se 1 (by rfl) ⟨149048, by rfl⟩ : syracuseStep 198731 = 298097) B298097
theorem B297047 : Blo 195805 297047 := bstep (se 1 (by rfl) ⟨222785, by rfl⟩ : syracuseStep 297047 = 445571) B445571
theorem B198743 : Blo 195805 198743 := bstep (se 1 (by rfl) ⟨149057, by rfl⟩ : syracuseStep 198743 = 298115) B298115
theorem B198763 : Blo 195805 198763 := bstep (se 1 (by rfl) ⟨149072, by rfl⟩ : syracuseStep 198763 = 298145) B298145
theorem B198775 : Blo 195805 198775 := bstep (se 1 (by rfl) ⟨149081, by rfl⟩ : syracuseStep 198775 = 298163) B298163
theorem B198795 : Blo 195805 198795 := bstep (se 1 (by rfl) ⟨149096, by rfl⟩ : syracuseStep 198795 = 298193) B298193
theorem B198807 : Blo 195805 198807 := bstep (se 1 (by rfl) ⟨149105, by rfl⟩ : syracuseStep 198807 = 298211) B298211
theorem B297113 : Blo 195805 297113 := bstep (se 2 (by rfl) ⟨111417, by rfl⟩ : syracuseStep 297113 = 222835) B222835
theorem B198827 : Blo 195805 198827 := bstep (se 1 (by rfl) ⟨149120, by rfl⟩ : syracuseStep 198827 = 298241) B298241
theorem B198839 : Blo 195805 198839 := bstep (se 1 (by rfl) ⟨149129, by rfl⟩ : syracuseStep 198839 = 298259) B298259
theorem B198859 : Blo 195805 198859 := bstep (se 1 (by rfl) ⟨149144, by rfl⟩ : syracuseStep 198859 = 298289) B298289
theorem B198871 : Blo 195805 198871 := bstep (se 1 (by rfl) ⟨149153, by rfl⟩ : syracuseStep 198871 = 298307) B298307
theorem B559325 : Blo 195805 559325 := bstep (se 3 (by rfl) ⟨104873, by rfl⟩ : syracuseStep 559325 = 209747) B209747
theorem B198891 : Blo 195805 198891 := bstep (se 1 (by rfl) ⟨149168, by rfl⟩ : syracuseStep 198891 = 298337) B298337
theorem B198903 : Blo 195805 198903 := bstep (se 1 (by rfl) ⟨149177, by rfl⟩ : syracuseStep 198903 = 298355) B298355
theorem B297227 : Blo 195805 297227 := bstep (se 1 (by rfl) ⟨222920, by rfl⟩ : syracuseStep 297227 = 445841) B445841
theorem B198923 : Blo 195805 198923 := bstep (se 1 (by rfl) ⟨149192, by rfl⟩ : syracuseStep 198923 = 298385) B298385
theorem B297239 : Blo 195805 297239 := bstep (se 1 (by rfl) ⟨222929, by rfl⟩ : syracuseStep 297239 = 445859) B445859
theorem B198935 : Blo 195805 198935 := bstep (se 1 (by rfl) ⟨149201, by rfl⟩ : syracuseStep 198935 = 298403) B298403
theorem B198955 : Blo 195805 198955 := bstep (se 1 (by rfl) ⟨149216, by rfl⟩ : syracuseStep 198955 = 298433) B298433
theorem B198967 : Blo 195805 198967 := bstep (se 1 (by rfl) ⟨149225, by rfl⟩ : syracuseStep 198967 = 298451) B298451
theorem B198987 : Blo 195805 198987 := bstep (se 1 (by rfl) ⟨149240, by rfl⟩ : syracuseStep 198987 = 298481) B298481
theorem B198999 : Blo 195805 198999 := bstep (se 1 (by rfl) ⟨149249, by rfl⟩ : syracuseStep 198999 = 298499) B298499
theorem B297305 : Blo 195805 297305 := bstep (se 2 (by rfl) ⟨111489, by rfl⟩ : syracuseStep 297305 = 222979) B222979
theorem B199019 : Blo 195805 199019 := bstep (se 1 (by rfl) ⟨149264, by rfl⟩ : syracuseStep 199019 = 298529) B298529
theorem B199031 : Blo 195805 199031 := bstep (se 1 (by rfl) ⟨149273, by rfl⟩ : syracuseStep 199031 = 298547) B298547
theorem B199051 : Blo 195805 199051 := bstep (se 1 (by rfl) ⟨149288, by rfl⟩ : syracuseStep 199051 = 298577) B298577
theorem B199063 : Blo 195805 199063 := bstep (se 1 (by rfl) ⟨149297, by rfl⟩ : syracuseStep 199063 = 298595) B298595
theorem B199083 : Blo 195805 199083 := bstep (se 1 (by rfl) ⟨149312, by rfl⟩ : syracuseStep 199083 = 298625) B298625
theorem B199095 : Blo 195805 199095 := bstep (se 1 (by rfl) ⟨149321, by rfl⟩ : syracuseStep 199095 = 298643) B298643
theorem B297419 : Blo 195805 297419 := bstep (se 1 (by rfl) ⟨223064, by rfl⟩ : syracuseStep 297419 = 446129) B446129
theorem B199115 : Blo 195805 199115 := bstep (se 1 (by rfl) ⟨149336, by rfl⟩ : syracuseStep 199115 = 298673) B298673
theorem B297431 : Blo 195805 297431 := bstep (se 1 (by rfl) ⟨223073, by rfl⟩ : syracuseStep 297431 = 446147) B446147
theorem B199127 : Blo 195805 199127 := bstep (se 1 (by rfl) ⟨149345, by rfl⟩ : syracuseStep 199127 = 298691) B298691
theorem B199147 : Blo 195805 199147 := bstep (se 1 (by rfl) ⟨149360, by rfl⟩ : syracuseStep 199147 = 298721) B298721
theorem B199159 : Blo 195805 199159 := bstep (se 1 (by rfl) ⟨149369, by rfl⟩ : syracuseStep 199159 = 298739) B298739
theorem B199179 : Blo 195805 199179 := bstep (se 1 (by rfl) ⟨149384, by rfl⟩ : syracuseStep 199179 = 298769) B298769
theorem B199191 : Blo 195805 199191 := bstep (se 1 (by rfl) ⟨149393, by rfl⟩ : syracuseStep 199191 = 298787) B298787
theorem B297497 : Blo 195805 297497 := bstep (se 2 (by rfl) ⟨111561, by rfl⟩ : syracuseStep 297497 = 223123) B223123
theorem B199211 : Blo 195805 199211 := bstep (se 1 (by rfl) ⟨149408, by rfl⟩ : syracuseStep 199211 = 298817) B298817
theorem B199223 : Blo 195805 199223 := bstep (se 1 (by rfl) ⟨149417, by rfl⟩ : syracuseStep 199223 = 298835) B298835
theorem B1116737 : Blo 195805 1116737 := bstep (se 2 (by rfl) ⟨418776, by rfl⟩ : syracuseStep 1116737 = 837553) B837553
theorem B199243 : Blo 195805 199243 := bstep (se 1 (by rfl) ⟨149432, by rfl⟩ : syracuseStep 199243 = 298865) B298865
theorem B199255 : Blo 195805 199255 := bstep (se 1 (by rfl) ⟨149441, by rfl⟩ : syracuseStep 199255 = 298883) B298883
theorem B199275 : Blo 195805 199275 := bstep (se 1 (by rfl) ⟨149456, by rfl⟩ : syracuseStep 199275 = 298913) B298913
theorem B199287 : Blo 195805 199287 := bstep (se 1 (by rfl) ⟨149465, by rfl⟩ : syracuseStep 199287 = 298931) B298931
theorem B297611 : Blo 195805 297611 := bstep (se 1 (by rfl) ⟨223208, by rfl⟩ : syracuseStep 297611 = 446417) B446417
theorem B199307 : Blo 195805 199307 := bstep (se 1 (by rfl) ⟨149480, by rfl⟩ : syracuseStep 199307 = 298961) B298961
theorem B297623 : Blo 195805 297623 := bstep (se 1 (by rfl) ⟨223217, by rfl⟩ : syracuseStep 297623 = 446435) B446435
theorem B199319 : Blo 195805 199319 := bstep (se 1 (by rfl) ⟨149489, by rfl⟩ : syracuseStep 199319 = 298979) B298979
theorem B199339 : Blo 195805 199339 := bstep (se 1 (by rfl) ⟨149504, by rfl⟩ : syracuseStep 199339 = 299009) B299009
theorem B199351 : Blo 195805 199351 := bstep (se 1 (by rfl) ⟨149513, by rfl⟩ : syracuseStep 199351 = 299027) B299027
theorem B199371 : Blo 195805 199371 := bstep (se 1 (by rfl) ⟨149528, by rfl⟩ : syracuseStep 199371 = 299057) B299057
theorem B199383 : Blo 195805 199383 := bstep (se 1 (by rfl) ⟨149537, by rfl⟩ : syracuseStep 199383 = 299075) B299075
theorem B1673945 : Blo 195805 1673945 := bstep (se 2 (by rfl) ⟨627729, by rfl⟩ : syracuseStep 1673945 = 1255459) B1255459
theorem B297689 : Blo 195805 297689 := bstep (se 2 (by rfl) ⟨111633, by rfl⟩ : syracuseStep 297689 = 223267) B223267
theorem B199403 : Blo 195805 199403 := bstep (se 1 (by rfl) ⟨149552, by rfl⟩ : syracuseStep 199403 = 299105) B299105
theorem B199415 : Blo 195805 199415 := bstep (se 1 (by rfl) ⟨149561, by rfl⟩ : syracuseStep 199415 = 299123) B299123
theorem B199435 : Blo 195805 199435 := bstep (se 1 (by rfl) ⟨149576, by rfl⟩ : syracuseStep 199435 = 299153) B299153
theorem B199447 : Blo 195805 199447 := bstep (se 1 (by rfl) ⟨149585, by rfl⟩ : syracuseStep 199447 = 299171) B299171
theorem B199467 : Blo 195805 199467 := bstep (se 1 (by rfl) ⟨149600, by rfl⟩ : syracuseStep 199467 = 299201) B299201
theorem B199479 : Blo 195805 199479 := bstep (se 1 (by rfl) ⟨149609, by rfl⟩ : syracuseStep 199479 = 299219) B299219
theorem B297803 : Blo 195805 297803 := bstep (se 1 (by rfl) ⟨223352, by rfl⟩ : syracuseStep 297803 = 446705) B446705
theorem B199499 : Blo 195805 199499 := bstep (se 1 (by rfl) ⟨149624, by rfl⟩ : syracuseStep 199499 = 299249) B299249
theorem B297815 : Blo 195805 297815 := bstep (se 1 (by rfl) ⟨223361, by rfl⟩ : syracuseStep 297815 = 446723) B446723
theorem B199511 : Blo 195805 199511 := bstep (se 1 (by rfl) ⟨149633, by rfl⟩ : syracuseStep 199511 = 299267) B299267
theorem B199531 : Blo 195805 199531 := bstep (se 1 (by rfl) ⟨149648, by rfl⟩ : syracuseStep 199531 = 299297) B299297
theorem B199543 : Blo 195805 199543 := bstep (se 1 (by rfl) ⟨149657, by rfl⟩ : syracuseStep 199543 = 299315) B299315
theorem B756611 : Blo 195805 756611 := bstep (se 1 (by rfl) ⟨567458, by rfl⟩ : syracuseStep 756611 = 1134917) B1134917
theorem B330635 : Blo 195805 330635 := bstep (se 1 (by rfl) ⟨247976, by rfl⟩ : syracuseStep 330635 = 495953) B495953
theorem B199563 : Blo 195805 199563 := bstep (se 1 (by rfl) ⟨149672, by rfl⟩ : syracuseStep 199563 = 299345) B299345
theorem B1411991 : Blo 195805 1411991 := bstep (se 1 (by rfl) ⟨1058993, by rfl⟩ : syracuseStep 1411991 = 2117987) B2117987
theorem B199575 : Blo 195805 199575 := bstep (se 1 (by rfl) ⟨149681, by rfl⟩ : syracuseStep 199575 = 299363) B299363
theorem B297881 : Blo 195805 297881 := bstep (se 2 (by rfl) ⟨111705, by rfl⟩ : syracuseStep 297881 = 223411) B223411
theorem B199595 : Blo 195805 199595 := bstep (se 1 (by rfl) ⟨149696, by rfl⟩ : syracuseStep 199595 = 299393) B299393
theorem B199607 : Blo 195805 199607 := bstep (se 1 (by rfl) ⟨149705, by rfl⟩ : syracuseStep 199607 = 299411) B299411
theorem B199627 : Blo 195805 199627 := bstep (se 1 (by rfl) ⟨149720, by rfl⟩ : syracuseStep 199627 = 299441) B299441
theorem B199639 : Blo 195805 199639 := bstep (se 1 (by rfl) ⟨149729, by rfl⟩ : syracuseStep 199639 = 299459) B299459
theorem B199659 : Blo 195805 199659 := bstep (se 1 (by rfl) ⟨149744, by rfl⟩ : syracuseStep 199659 = 299489) B299489
theorem B199671 : Blo 195805 199671 := bstep (se 1 (by rfl) ⟨149753, by rfl⟩ : syracuseStep 199671 = 299507) B299507
theorem B855043 : Blo 195805 855043 := bstep (se 1 (by rfl) ⟨641282, by rfl⟩ : syracuseStep 855043 = 1282565) B1282565
theorem B330763 : Blo 195805 330763 := bstep (se 1 (by rfl) ⟨248072, by rfl⟩ : syracuseStep 330763 = 496145) B496145
theorem B297995 : Blo 195805 297995 := bstep (se 1 (by rfl) ⟨223496, by rfl⟩ : syracuseStep 297995 = 446993) B446993
theorem B199691 : Blo 195805 199691 := bstep (se 1 (by rfl) ⟨149768, by rfl⟩ : syracuseStep 199691 = 299537) B299537
theorem B298007 : Blo 195805 298007 := bstep (se 1 (by rfl) ⟨223505, by rfl⟩ : syracuseStep 298007 = 447011) B447011
theorem B199703 : Blo 195805 199703 := bstep (se 1 (by rfl) ⟨149777, by rfl⟩ : syracuseStep 199703 = 299555) B299555
theorem B199723 : Blo 195805 199723 := bstep (se 1 (by rfl) ⟨149792, by rfl⟩ : syracuseStep 199723 = 299585) B299585
theorem B199735 : Blo 195805 199735 := bstep (se 1 (by rfl) ⟨149801, by rfl⟩ : syracuseStep 199735 = 299603) B299603
theorem B199755 : Blo 195805 199755 := bstep (se 1 (by rfl) ⟨149816, by rfl⟩ : syracuseStep 199755 = 299633) B299633
theorem B298073 : Blo 195805 298073 := bstep (se 2 (by rfl) ⟨111777, by rfl⟩ : syracuseStep 298073 = 223555) B223555
theorem B199767 : Blo 195805 199767 := bstep (se 1 (by rfl) ⟨149825, by rfl⟩ : syracuseStep 199767 = 299651) B299651
theorem B199787 : Blo 195805 199787 := bstep (se 1 (by rfl) ⟨149840, by rfl⟩ : syracuseStep 199787 = 299681) B299681
theorem B199799 : Blo 195805 199799 := bstep (se 1 (by rfl) ⟨149849, by rfl⟩ : syracuseStep 199799 = 299699) B299699
theorem B330905 : Blo 195805 330905 := bstep (se 2 (by rfl) ⟨124089, by rfl⟩ : syracuseStep 330905 = 248179) B248179
theorem B298187 : Blo 195805 298187 := bstep (se 1 (by rfl) ⟨223640, by rfl⟩ : syracuseStep 298187 = 447281) B447281
theorem B298199 : Blo 195805 298199 := bstep (se 1 (by rfl) ⟨223649, by rfl⟩ : syracuseStep 298199 = 447299) B447299
theorem B331033 : Blo 195805 331033 := bstep (se 2 (by rfl) ⟨124137, by rfl⟩ : syracuseStep 331033 = 248275) B248275
theorem B298265 : Blo 195805 298265 := bstep (se 2 (by rfl) ⟨111849, by rfl⟩ : syracuseStep 298265 = 223699) B223699
theorem B298379 : Blo 195805 298379 := bstep (se 1 (by rfl) ⟨223784, by rfl⟩ : syracuseStep 298379 = 447569) B447569
theorem B298391 : Blo 195805 298391 := bstep (se 1 (by rfl) ⟨223793, by rfl⟩ : syracuseStep 298391 = 447587) B447587
theorem B691649 : Blo 195805 691649 := bstep (se 2 (by rfl) ⟨259368, by rfl⟩ : syracuseStep 691649 = 518737) B518737
theorem B298457 : Blo 195805 298457 := bstep (se 2 (by rfl) ⟨111921, by rfl⟩ : syracuseStep 298457 = 223843) B223843
theorem B298571 : Blo 195805 298571 := bstep (se 1 (by rfl) ⟨223928, by rfl⟩ : syracuseStep 298571 = 447857) B447857
theorem B298583 : Blo 195805 298583 := bstep (se 1 (by rfl) ⟨223937, by rfl⟩ : syracuseStep 298583 = 447875) B447875
theorem B298649 : Blo 195805 298649 := bstep (se 2 (by rfl) ⟨111993, by rfl⟩ : syracuseStep 298649 = 223987) B223987
theorem B298763 : Blo 195805 298763 := bstep (se 1 (by rfl) ⟨224072, by rfl⟩ : syracuseStep 298763 = 448145) B448145
theorem B298775 : Blo 195805 298775 := bstep (se 1 (by rfl) ⟨224081, by rfl⟩ : syracuseStep 298775 = 448163) B448163
theorem B331607 : Blo 195805 331607 := bstep (se 1 (by rfl) ⟨248705, by rfl⟩ : syracuseStep 331607 = 497411) B497411
theorem B298841 : Blo 195805 298841 := bstep (se 2 (by rfl) ⟨112065, by rfl⟩ : syracuseStep 298841 = 224131) B224131
theorem B298955 : Blo 195805 298955 := bstep (se 1 (by rfl) ⟨224216, by rfl⟩ : syracuseStep 298955 = 448433) B448433
theorem B331735 : Blo 195805 331735 := bstep (se 1 (by rfl) ⟨248801, by rfl⟩ : syracuseStep 331735 = 497603) B497603
theorem B298967 : Blo 195805 298967 := bstep (se 1 (by rfl) ⟨224225, by rfl⟩ : syracuseStep 298967 = 448451) B448451
theorem B2691089 : Blo 195805 2691089 := bstep (se 2 (by rfl) ⟨1009158, by rfl⟩ : syracuseStep 2691089 = 2018317) B2018317
theorem B757777 : Blo 195805 757777 := bstep (se 2 (by rfl) ⟨284166, by rfl⟩ : syracuseStep 757777 = 568333) B568333
theorem B299033 : Blo 195805 299033 := bstep (se 2 (by rfl) ⟨112137, by rfl⟩ : syracuseStep 299033 = 224275) B224275
theorem B1511459 : Blo 195805 1511459 := bstep (se 1 (by rfl) ⟨1133594, by rfl⟩ : syracuseStep 1511459 = 2267189) B2267189
theorem B299147 : Blo 195805 299147 := bstep (se 1 (by rfl) ⟨224360, by rfl⟩ : syracuseStep 299147 = 448721) B448721
theorem B299159 : Blo 195805 299159 := bstep (se 1 (by rfl) ⟨224369, by rfl⟩ : syracuseStep 299159 = 448739) B448739
theorem B299225 : Blo 195805 299225 := bstep (se 2 (by rfl) ⟨112209, by rfl⟩ : syracuseStep 299225 = 224419) B224419
theorem B299339 : Blo 195805 299339 := bstep (se 1 (by rfl) ⟨224504, by rfl⟩ : syracuseStep 299339 = 449009) B449009
theorem B299351 : Blo 195805 299351 := bstep (se 1 (by rfl) ⟨224513, by rfl⟩ : syracuseStep 299351 = 449027) B449027
theorem B299417 : Blo 195805 299417 := bstep (se 2 (by rfl) ⟨112281, by rfl⟩ : syracuseStep 299417 = 224563) B224563
theorem B299531 : Blo 195805 299531 := bstep (se 1 (by rfl) ⟨224648, by rfl⟩ : syracuseStep 299531 = 449297) B449297
theorem B299543 : Blo 195805 299543 := bstep (se 1 (by rfl) ⟨224657, by rfl⟩ : syracuseStep 299543 = 449315) B449315
theorem B332363 : Blo 195805 332363 := bstep (se 1 (by rfl) ⟨249272, by rfl⟩ : syracuseStep 332363 = 498545) B498545
theorem B299609 : Blo 195805 299609 := bstep (se 2 (by rfl) ⟨112353, by rfl⟩ : syracuseStep 299609 = 224707) B224707
theorem B2265731 : Blo 195805 2265731 := bstep (se 1 (by rfl) ⟨1699298, by rfl⟩ : syracuseStep 2265731 = 3398597) B3398597
theorem B496307 : Blo 195805 496307 := bstep (se 1 (by rfl) ⟨372230, by rfl⟩ : syracuseStep 496307 = 744461) B744461
theorem B332491 : Blo 195805 332491 := bstep (se 1 (by rfl) ⟨249368, by rfl⟩ : syracuseStep 332491 = 498737) B498737
theorem B4854593 : Blo 195805 4854593 := bstep (se 2 (by rfl) ⟨1820472, by rfl⟩ : syracuseStep 4854593 = 3640945) B3640945
theorem B332633 : Blo 195805 332633 := bstep (se 2 (by rfl) ⟨124737, by rfl⟩ : syracuseStep 332633 = 249475) B249475
theorem B3183461 : Blo 195805 3183461 := bstep (se 4 (by rfl) ⟨298449, by rfl⟩ : syracuseStep 3183461 = 596899) B596899
theorem B496601 : Blo 195805 496601 := bstep (se 2 (by rfl) ⟨186225, by rfl⟩ : syracuseStep 496601 = 372451) B372451
theorem B332761 : Blo 195805 332761 := bstep (se 2 (by rfl) ⟨124785, by rfl⟩ : syracuseStep 332761 = 249571) B249571
theorem B562241 : Blo 195805 562241 := bstep (se 2 (by rfl) ⟨210840, by rfl⟩ : syracuseStep 562241 = 421681) B421681
theorem B562265 : Blo 195805 562265 := bstep (se 2 (by rfl) ⟨210849, by rfl⟩ : syracuseStep 562265 = 421699) B421699
theorem B1905869 : Blo 195805 1905869 := bstep (se 3 (by rfl) ⟨357350, by rfl⟩ : syracuseStep 1905869 = 714701) B714701
theorem B1676609 : Blo 195805 1676609 := bstep (se 2 (by rfl) ⟨628728, by rfl⟩ : syracuseStep 1676609 = 1257457) B1257457
theorem B333335 : Blo 195805 333335 := bstep (se 1 (by rfl) ⟨250001, by rfl⟩ : syracuseStep 333335 = 500003) B500003
theorem B2299427 : Blo 195805 2299427 := bstep (se 1 (by rfl) ⟨1724570, by rfl⟩ : syracuseStep 2299427 = 3449141) B3449141
theorem B661067 : Blo 195805 661067 := bstep (se 1 (by rfl) ⟨495800, by rfl⟩ : syracuseStep 661067 = 991601) B991601
theorem B333463 : Blo 195805 333463 := bstep (se 1 (by rfl) ⟨250097, by rfl⟩ : syracuseStep 333463 = 500195) B500195
theorem B661337 : Blo 195805 661337 := bstep (se 2 (by rfl) ⟨248001, by rfl⟩ : syracuseStep 661337 = 496003) B496003
theorem B235543 : Blo 195805 235543 := bstep (se 1 (by rfl) ⟨176657, by rfl⟩ : syracuseStep 235543 = 353315) B353315
theorem B202775 : Blo 195805 202775 := bstep (se 1 (by rfl) ⟨152081, by rfl⟩ : syracuseStep 202775 = 304163) B304163
theorem B334091 : Blo 195805 334091 := bstep (se 1 (by rfl) ⟨250568, by rfl⟩ : syracuseStep 334091 = 501137) B501137
theorem B563507 : Blo 195805 563507 := bstep (se 1 (by rfl) ⟨422630, by rfl⟩ : syracuseStep 563507 = 845261) B845261
theorem B334219 : Blo 195805 334219 := bstep (se 1 (by rfl) ⟨250664, by rfl⟩ : syracuseStep 334219 = 501329) B501329
theorem B4299277 : Blo 195805 4299277 := bstep (se 3 (by rfl) ⟨806114, by rfl⟩ : syracuseStep 4299277 = 1612229) B1612229
theorem B662039 : Blo 195805 662039 := bstep (se 1 (by rfl) ⟨496529, by rfl⟩ : syracuseStep 662039 = 993059) B993059
theorem B334361 : Blo 195805 334361 := bstep (se 2 (by rfl) ⟨125385, by rfl⟩ : syracuseStep 334361 = 250771) B250771
theorem B596531 : Blo 195805 596531 := bstep (se 1 (by rfl) ⟨447398, by rfl⟩ : syracuseStep 596531 = 894797) B894797
theorem B498251 : Blo 195805 498251 := bstep (se 1 (by rfl) ⟨373688, by rfl⟩ : syracuseStep 498251 = 747377) B747377
theorem B334489 : Blo 195805 334489 := bstep (se 2 (by rfl) ⟨125433, by rfl⟩ : syracuseStep 334489 = 250867) B250867
theorem B662579 : Blo 195805 662579 := bstep (se 1 (by rfl) ⟨496934, by rfl⟩ : syracuseStep 662579 = 993869) B993869
theorem B335063 : Blo 195805 335063 := bstep (se 1 (by rfl) ⟨251297, by rfl⟩ : syracuseStep 335063 = 502595) B502595
theorem B269527 : Blo 195805 269527 := bstep (se 1 (by rfl) ⟨202145, by rfl⟩ : syracuseStep 269527 = 404291) B404291
theorem B662849 : Blo 195805 662849 := bstep (se 2 (by rfl) ⟨248568, by rfl⟩ : syracuseStep 662849 = 497137) B497137
theorem B400715 : Blo 195805 400715 := bstep (se 1 (by rfl) ⟨300536, by rfl⟩ : syracuseStep 400715 = 601073) B601073
theorem B335191 : Blo 195805 335191 := bstep (se 1 (by rfl) ⟨251393, by rfl⟩ : syracuseStep 335191 = 502787) B502787
theorem B2858341 : Blo 195805 2858341 := bstep (se 4 (by rfl) ⟨267969, by rfl⟩ : syracuseStep 2858341 = 535939) B535939
theorem B499223 : Blo 195805 499223 := bstep (se 1 (by rfl) ⟨374417, by rfl⟩ : syracuseStep 499223 = 748835) B748835
theorem B269911 : Blo 195805 269911 := bstep (se 1 (by rfl) ⟨202433, by rfl⟩ : syracuseStep 269911 = 404867) B404867
theorem B2826049 : Blo 195805 2826049 := bstep (se 2 (by rfl) ⟨1059768, by rfl⟩ : syracuseStep 2826049 = 2119537) B2119537
theorem B1122113 : Blo 195805 1122113 := bstep (se 2 (by rfl) ⟨420792, by rfl⟩ : syracuseStep 1122113 = 841585) B841585
theorem B663389 : Blo 195805 663389 := bstep (se 3 (by rfl) ⟨124385, by rfl⟩ : syracuseStep 663389 = 248771) B248771
theorem B958301 : Blo 195805 958301 := bstep (se 3 (by rfl) ⟨179681, by rfl⟩ : syracuseStep 958301 = 359363) B359363
theorem B5742515 : Blo 195805 5742515 := bstep (se 1 (by rfl) ⟨4306886, by rfl⟩ : syracuseStep 5742515 = 8613773) B8613773
theorem B335819 : Blo 195805 335819 := bstep (se 1 (by rfl) ⟨251864, by rfl⟩ : syracuseStep 335819 = 503729) B503729
theorem B991277 : Blo 195805 991277 := bstep (se 3 (by rfl) ⟨185864, by rfl⟩ : syracuseStep 991277 = 371729) B371729
theorem B335947 : Blo 195805 335947 := bstep (se 1 (by rfl) ⟨251960, by rfl⟩ : syracuseStep 335947 = 503921) B503921
theorem B1351781 : Blo 195805 1351781 := bstep (se 4 (by rfl) ⟨126729, by rfl⟩ : syracuseStep 1351781 = 253459) B253459
theorem B499891 : Blo 195805 499891 := bstep (se 1 (by rfl) ⟨374918, by rfl⟩ : syracuseStep 499891 = 749837) B749837
theorem B6037685 : Blo 195805 6037685 := bstep (se 5 (by rfl) ⟨283016, by rfl⟩ : syracuseStep 6037685 = 566033) B566033
theorem B336089 : Blo 195805 336089 := bstep (se 2 (by rfl) ⟨126033, by rfl⟩ : syracuseStep 336089 = 252067) B252067
theorem B500033 : Blo 195805 500033 := bstep (se 2 (by rfl) ⟨187512, by rfl⟩ : syracuseStep 500033 = 375025) B375025
theorem B532825 : Blo 195805 532825 := bstep (se 2 (by rfl) ⟨199809, by rfl⟩ : syracuseStep 532825 = 399619) B399619
theorem B336217 : Blo 195805 336217 := bstep (se 2 (by rfl) ⟨126081, by rfl⟩ : syracuseStep 336217 = 252163) B252163
theorem B598603 : Blo 195805 598603 := bstep (se 1 (by rfl) ⟨448952, by rfl⟩ : syracuseStep 598603 = 897905) B897905
theorem B303769 : Blo 195805 303769 := bstep (se 2 (by rfl) ⟨113913, by rfl⟩ : syracuseStep 303769 = 227827) B227827
theorem B336791 : Blo 195805 336791 := bstep (se 1 (by rfl) ⟨252593, by rfl⟩ : syracuseStep 336791 = 505187) B505187
theorem B664523 : Blo 195805 664523 := bstep (se 1 (by rfl) ⟨498392, by rfl⟩ : syracuseStep 664523 = 996785) B996785
theorem B336919 : Blo 195805 336919 := bstep (se 1 (by rfl) ⟨252689, by rfl⟩ : syracuseStep 336919 = 505379) B505379
theorem B566365 : Blo 195805 566365 := bstep (se 3 (by rfl) ⟨106193, by rfl⟩ : syracuseStep 566365 = 212387) B212387
theorem B566423 : Blo 195805 566423 := bstep (se 1 (by rfl) ⟨424817, by rfl⟩ : syracuseStep 566423 = 849635) B849635
theorem B664793 : Blo 195805 664793 := bstep (se 2 (by rfl) ⟨249297, by rfl⟩ : syracuseStep 664793 = 498595) B498595
theorem B1516805 : Blo 195805 1516805 := bstep (se 4 (by rfl) ⟨142200, by rfl⟩ : syracuseStep 1516805 = 284401) B284401
theorem B501299 : Blo 195805 501299 := bstep (se 1 (by rfl) ⟨375974, by rfl⟩ : syracuseStep 501299 = 751949) B751949
theorem B1451621 : Blo 195805 1451621 := bstep (se 4 (by rfl) ⟨136089, by rfl⟩ : syracuseStep 1451621 = 272179) B272179
theorem B534209 : Blo 195805 534209 := bstep (se 2 (by rfl) ⟨200328, by rfl⟩ : syracuseStep 534209 = 400657) B400657
theorem B239383 : Blo 195805 239383 := bstep (se 1 (by rfl) ⟨179537, by rfl⟩ : syracuseStep 239383 = 359075) B359075
theorem B665495 : Blo 195805 665495 := bstep (se 1 (by rfl) ⟨499121, by rfl⟩ : syracuseStep 665495 = 998243) B998243
theorem B501835 : Blo 195805 501835 := bstep (se 1 (by rfl) ⟨376376, by rfl⟩ : syracuseStep 501835 = 752753) B752753
theorem B3385475 : Blo 195805 3385475 := bstep (se 1 (by rfl) ⟨2539106, by rfl⟩ : syracuseStep 3385475 = 5078213) B5078213
theorem B633035 : Blo 195805 633035 := bstep (se 1 (by rfl) ⟨474776, by rfl⟩ : syracuseStep 633035 = 949553) B949553
theorem B501977 : Blo 195805 501977 := bstep (se 2 (by rfl) ⟨188241, by rfl⟩ : syracuseStep 501977 = 376483) B376483
theorem B567641 : Blo 195805 567641 := bstep (se 2 (by rfl) ⟨212865, by rfl⟩ : syracuseStep 567641 = 425731) B425731
theorem B3221861 : Blo 195805 3221861 := bstep (se 4 (by rfl) ⟨302049, by rfl⟩ : syracuseStep 3221861 = 604099) B604099
theorem B1812887 : Blo 195805 1812887 := bstep (se 1 (by rfl) ⟨1359665, by rfl⟩ : syracuseStep 1812887 = 2719331) B2719331
theorem B666035 : Blo 195805 666035 := bstep (se 1 (by rfl) ⟨499526, by rfl⟩ : syracuseStep 666035 = 999053) B999053
theorem B1354163 : Blo 195805 1354163 := bstep (se 1 (by rfl) ⟨1015622, by rfl⟩ : syracuseStep 1354163 = 2031245) B2031245
theorem B567755 : Blo 195805 567755 := bstep (se 1 (by rfl) ⟨425816, by rfl⟩ : syracuseStep 567755 = 851633) B851633
theorem B633433 : Blo 195805 633433 := bstep (se 2 (by rfl) ⟨237537, by rfl⟩ : syracuseStep 633433 = 475075) B475075
theorem B3582557 : Blo 195805 3582557 := bstep (se 3 (by rfl) ⟨671729, by rfl⟩ : syracuseStep 3582557 = 1343459) B1343459
theorem B666305 : Blo 195805 666305 := bstep (se 2 (by rfl) ⟨249864, by rfl⟩ : syracuseStep 666305 = 499729) B499729
theorem B502807 : Blo 195805 502807 := bstep (se 1 (by rfl) ⟨377105, by rfl⟩ : syracuseStep 502807 = 754211) B754211
theorem B371927 : Blo 195805 371927 := bstep (se 1 (by rfl) ⟨278945, by rfl⟩ : syracuseStep 371927 = 557891) B557891
theorem B666845 : Blo 195805 666845 := bstep (se 3 (by rfl) ⟨125033, by rfl⟩ : syracuseStep 666845 = 250067) B250067
theorem B1682693 : Blo 195805 1682693 := bstep (se 4 (by rfl) ⟨157752, by rfl⟩ : syracuseStep 1682693 = 315505) B315505
theorem B339287 : Blo 195805 339287 := bstep (se 1 (by rfl) ⟨254465, by rfl⟩ : syracuseStep 339287 = 508931) B508931
theorem B503243 : Blo 195805 503243 := bstep (se 1 (by rfl) ⟨377432, by rfl⟩ : syracuseStep 503243 = 754865) B754865
theorem B372185 : Blo 195805 372185 := bstep (se 2 (by rfl) ⟨139569, by rfl⟩ : syracuseStep 372185 = 279139) B279139
theorem B568883 : Blo 195805 568883 := bstep (se 1 (by rfl) ⟨426662, by rfl⟩ : syracuseStep 568883 = 853325) B853325
theorem B536285 : Blo 195805 536285 := bstep (se 3 (by rfl) ⟨100553, by rfl⟩ : syracuseStep 536285 = 201107) B201107
theorem B634675 : Blo 195805 634675 := bstep (se 1 (by rfl) ⟨476006, by rfl⟩ : syracuseStep 634675 = 952013) B952013
theorem B503617 : Blo 195805 503617 := bstep (se 2 (by rfl) ⟨188856, by rfl⟩ : syracuseStep 503617 = 377713) B377713
theorem B995165 : Blo 195805 995165 := bstep (se 3 (by rfl) ⟨186593, by rfl⟩ : syracuseStep 995165 = 373187) B373187
theorem B372595 : Blo 195805 372595 := bstep (se 1 (by rfl) ⟨279446, by rfl⟩ : syracuseStep 372595 = 558893) B558893
theorem B13840307 : Blo 195805 13840307 := bstep (se 1 (by rfl) ⟨10380230, by rfl⟩ : syracuseStep 13840307 = 20760461) B20760461
theorem B536537 : Blo 195805 536537 := bstep (se 2 (by rfl) ⟨201201, by rfl⟩ : syracuseStep 536537 = 402403) B402403
theorem B1814489 : Blo 195805 1814489 := bstep (se 2 (by rfl) ⟨680433, by rfl⟩ : syracuseStep 1814489 = 1360867) B1360867
theorem B766169 : Blo 195805 766169 := bstep (se 2 (by rfl) ⟨287313, by rfl⟩ : syracuseStep 766169 = 574627) B574627
theorem B798979 : Blo 195805 798979 := bstep (se 1 (by rfl) ⟨599234, by rfl⟩ : syracuseStep 798979 = 1198469) B1198469
theorem B667979 : Blo 195805 667979 := bstep (se 1 (by rfl) ⟨500984, by rfl⟩ : syracuseStep 667979 = 1001969) B1001969
theorem B373081 : Blo 195805 373081 := bstep (se 2 (by rfl) ⟨139905, by rfl⟩ : syracuseStep 373081 = 279811) B279811
theorem B504215 : Blo 195805 504215 := bstep (se 1 (by rfl) ⟨378161, by rfl⟩ : syracuseStep 504215 = 756323) B756323
theorem B2240945 : Blo 195805 2240945 := bstep (se 2 (by rfl) ⟨840354, by rfl⟩ : syracuseStep 2240945 = 1680709) B1680709
theorem B668249 : Blo 195805 668249 := bstep (se 2 (by rfl) ⟨250593, by rfl⟩ : syracuseStep 668249 = 501187) B501187
theorem B537281 : Blo 195805 537281 := bstep (se 2 (by rfl) ⟨201480, by rfl⟩ : syracuseStep 537281 = 402961) B402961
theorem B209675 : Blo 195805 209675 := bstep (se 1 (by rfl) ⟨157256, by rfl⟩ : syracuseStep 209675 = 314513) B314513
theorem B1192805 : Blo 195805 1192805 := bstep (se 4 (by rfl) ⟨111825, by rfl⟩ : syracuseStep 1192805 = 223651) B223651
theorem B373643 : Blo 195805 373643 := bstep (se 1 (by rfl) ⟨280232, by rfl⟩ : syracuseStep 373643 = 560465) B560465
theorem B373825 : Blo 195805 373825 := bstep (se 2 (by rfl) ⟨140184, by rfl⟩ : syracuseStep 373825 = 280369) B280369
theorem B505025 : Blo 195805 505025 := bstep (se 2 (by rfl) ⟨189384, by rfl⟩ : syracuseStep 505025 = 378769) B378769
theorem B898307 : Blo 195805 898307 := bstep (se 1 (by rfl) ⟨673730, by rfl⟩ : syracuseStep 898307 = 1347461) B1347461
theorem B668951 : Blo 195805 668951 := bstep (se 1 (by rfl) ⟨501713, by rfl⟩ : syracuseStep 668951 = 1003427) B1003427
theorem B472385 : Blo 195805 472385 := bstep (se 2 (by rfl) ⟨177144, by rfl⟩ : syracuseStep 472385 = 354289) B354289
theorem B472769 : Blo 195805 472769 := bstep (se 2 (by rfl) ⟨177288, by rfl⟩ : syracuseStep 472769 = 354577) B354577
theorem B505561 : Blo 195805 505561 := bstep (se 2 (by rfl) ⟨189585, by rfl⟩ : syracuseStep 505561 = 379171) B379171
theorem B374539 : Blo 195805 374539 := bstep (se 1 (by rfl) ⟨280904, by rfl⟩ : syracuseStep 374539 = 561809) B561809
theorem B669491 : Blo 195805 669491 := bstep (se 1 (by rfl) ⟨502118, by rfl⟩ : syracuseStep 669491 = 1004237) B1004237
theorem B374615 : Blo 195805 374615 := bstep (se 1 (by rfl) ⟨280961, by rfl⟩ : syracuseStep 374615 = 561923) B561923
theorem B997271 : Blo 195805 997271 := bstep (se 1 (by rfl) ⟨747953, by rfl⟩ : syracuseStep 997271 = 1495907) B1495907
theorem B210871 : Blo 195805 210871 := bstep (se 1 (by rfl) ⟨158153, by rfl⟩ : syracuseStep 210871 = 316307) B316307
theorem B669761 : Blo 195805 669761 := bstep (se 2 (by rfl) ⟨251160, by rfl⟩ : syracuseStep 669761 = 502321) B502321
theorem B1882187 : Blo 195805 1882187 := bstep (se 1 (by rfl) ⟨1411640, by rfl⟩ : syracuseStep 1882187 = 2823281) B2823281
theorem B440729 : Blo 195805 440729 := bstep (se 2 (by rfl) ⟨165273, by rfl⟩ : syracuseStep 440729 = 330547) B330547
theorem B440819 : Blo 195805 440819 := bstep (se 1 (by rfl) ⟨330614, by rfl⟩ : syracuseStep 440819 = 661229) B661229
theorem B375283 : Blo 195805 375283 := bstep (se 1 (by rfl) ⟨281462, by rfl⟩ : syracuseStep 375283 = 562925) B562925
theorem B1161745 : Blo 195805 1161745 := bstep (se 2 (by rfl) ⟨435654, by rfl⟩ : syracuseStep 1161745 = 871309) B871309
theorem B440855 : Blo 195805 440855 := bstep (se 1 (by rfl) ⟨330641, by rfl⟩ : syracuseStep 440855 = 661283) B661283
theorem B670301 : Blo 195805 670301 := bstep (se 3 (by rfl) ⟨125681, by rfl⟩ : syracuseStep 670301 = 251363) B251363
theorem B441035 : Blo 195805 441035 := bstep (se 1 (by rfl) ⟨330776, by rfl⟩ : syracuseStep 441035 = 661553) B661553
theorem B375511 : Blo 195805 375511 := bstep (se 1 (by rfl) ⟨281633, by rfl⟩ : syracuseStep 375511 = 563267) B563267
theorem B211691 : Blo 195805 211691 := bstep (se 1 (by rfl) ⟨158768, by rfl⟩ : syracuseStep 211691 = 317537) B317537
theorem B441089 : Blo 195805 441089 := bstep (se 2 (by rfl) ⟨165408, by rfl⟩ : syracuseStep 441089 = 330817) B330817
theorem B1260305 : Blo 195805 1260305 := bstep (se 2 (by rfl) ⟨472614, by rfl⟩ : syracuseStep 1260305 = 945229) B945229
theorem B899857 : Blo 195805 899857 := bstep (se 2 (by rfl) ⟨337446, by rfl⟩ : syracuseStep 899857 = 674893) B674893
theorem B375617 : Blo 195805 375617 := bstep (se 2 (by rfl) ⟨140856, by rfl⟩ : syracuseStep 375617 = 281713) B281713
theorem B474007 : Blo 195805 474007 := bstep (se 1 (by rfl) ⟨355505, by rfl⟩ : syracuseStep 474007 = 711011) B711011
theorem B900019 : Blo 195805 900019 := bstep (se 1 (by rfl) ⟨675014, by rfl⟩ : syracuseStep 900019 = 1350029) B1350029
theorem B441305 : Blo 195805 441305 := bstep (se 2 (by rfl) ⟨165489, by rfl⟩ : syracuseStep 441305 = 330979) B330979
theorem B375769 : Blo 195805 375769 := bstep (se 2 (by rfl) ⟨140913, by rfl⟩ : syracuseStep 375769 = 281827) B281827
theorem B441395 : Blo 195805 441395 := bstep (se 1 (by rfl) ⟨331046, by rfl⟩ : syracuseStep 441395 = 662093) B662093
theorem B441431 : Blo 195805 441431 := bstep (se 1 (by rfl) ⟨331073, by rfl⟩ : syracuseStep 441431 = 662147) B662147
theorem B441611 : Blo 195805 441611 := bstep (se 1 (by rfl) ⟨331208, by rfl⟩ : syracuseStep 441611 = 662417) B662417
theorem B441665 : Blo 195805 441665 := bstep (se 2 (by rfl) ⟨165624, by rfl⟩ : syracuseStep 441665 = 331249) B331249
theorem B605515 : Blo 195805 605515 := bstep (se 1 (by rfl) ⟨454136, by rfl⟩ : syracuseStep 605515 = 908273) B908273
theorem B1129859 : Blo 195805 1129859 := bstep (se 1 (by rfl) ⟨847394, by rfl⟩ : syracuseStep 1129859 = 1694789) B1694789
theorem B441881 : Blo 195805 441881 := bstep (se 2 (by rfl) ⟨165705, by rfl⟩ : syracuseStep 441881 = 331411) B331411
theorem B441971 : Blo 195805 441971 := bstep (se 1 (by rfl) ⟨331478, by rfl⟩ : syracuseStep 441971 = 662957) B662957
theorem B442007 : Blo 195805 442007 := bstep (se 1 (by rfl) ⟨331505, by rfl⟩ : syracuseStep 442007 = 663011) B663011
theorem B671435 : Blo 195805 671435 := bstep (se 1 (by rfl) ⟨503576, by rfl⟩ : syracuseStep 671435 = 1007153) B1007153
theorem B573149 : Blo 195805 573149 := bstep (se 3 (by rfl) ⟨107465, by rfl⟩ : syracuseStep 573149 = 214931) B214931
theorem B442187 : Blo 195805 442187 := bstep (se 1 (by rfl) ⟨331640, by rfl⟩ : syracuseStep 442187 = 663281) B663281
theorem B442241 : Blo 195805 442241 := bstep (se 2 (by rfl) ⟨165840, by rfl⟩ : syracuseStep 442241 = 331681) B331681
theorem B671705 : Blo 195805 671705 := bstep (se 2 (by rfl) ⟨251889, by rfl⟩ : syracuseStep 671705 = 503779) B503779
theorem B213079 : Blo 195805 213079 := bstep (se 1 (by rfl) ⟨159809, by rfl⟩ : syracuseStep 213079 = 319619) B319619
theorem B442457 : Blo 195805 442457 := bstep (se 2 (by rfl) ⟨165921, by rfl⟩ : syracuseStep 442457 = 331843) B331843
theorem B442547 : Blo 195805 442547 := bstep (se 1 (by rfl) ⟨331910, by rfl⟩ : syracuseStep 442547 = 663821) B663821
theorem B442583 : Blo 195805 442583 := bstep (se 1 (by rfl) ⟨331937, by rfl⟩ : syracuseStep 442583 = 663875) B663875
theorem B377075 : Blo 195805 377075 := bstep (se 1 (by rfl) ⟨282806, by rfl⟩ : syracuseStep 377075 = 565613) B565613
theorem B377111 : Blo 195805 377111 := bstep (se 1 (by rfl) ⟨282833, by rfl⟩ : syracuseStep 377111 = 565667) B565667
theorem B442763 : Blo 195805 442763 := bstep (se 1 (by rfl) ⟨332072, by rfl⟩ : syracuseStep 442763 = 664145) B664145
theorem B377227 : Blo 195805 377227 := bstep (se 1 (by rfl) ⟨282920, by rfl⟩ : syracuseStep 377227 = 565841) B565841
theorem B442817 : Blo 195805 442817 := bstep (se 2 (by rfl) ⟨166056, by rfl⟩ : syracuseStep 442817 = 332113) B332113
theorem B279065 : Blo 195805 279065 := bstep (se 2 (by rfl) ⟨104649, by rfl⟩ : syracuseStep 279065 = 209299) B209299
theorem B377419 : Blo 195805 377419 := bstep (se 1 (by rfl) ⟨283064, by rfl⟩ : syracuseStep 377419 = 566129) B566129
theorem B836185 : Blo 195805 836185 := bstep (se 2 (by rfl) ⟨313569, by rfl⟩ : syracuseStep 836185 = 627139) B627139
theorem B1065565 : Blo 195805 1065565 := bstep (se 3 (by rfl) ⟨199793, by rfl⟩ : syracuseStep 1065565 = 399587) B399587
theorem B672407 : Blo 195805 672407 := bstep (se 1 (by rfl) ⟨504305, by rfl⟩ : syracuseStep 672407 = 1008611) B1008611
theorem B443033 : Blo 195805 443033 := bstep (se 2 (by rfl) ⟨166137, by rfl⟩ : syracuseStep 443033 = 332275) B332275
theorem B377561 : Blo 195805 377561 := bstep (se 2 (by rfl) ⟨141585, by rfl⟩ : syracuseStep 377561 = 283171) B283171
theorem B443123 : Blo 195805 443123 := bstep (se 1 (by rfl) ⟨332342, by rfl⟩ : syracuseStep 443123 = 664685) B664685
theorem B443159 : Blo 195805 443159 := bstep (se 1 (by rfl) ⟨332369, by rfl⟩ : syracuseStep 443159 = 664739) B664739
theorem B475969 : Blo 195805 475969 := bstep (se 2 (by rfl) ⟨178488, by rfl⟩ : syracuseStep 475969 = 356977) B356977
theorem B443339 : Blo 195805 443339 := bstep (se 1 (by rfl) ⟨332504, by rfl⟩ : syracuseStep 443339 = 665009) B665009
theorem B443393 : Blo 195805 443393 := bstep (se 2 (by rfl) ⟨166272, by rfl⟩ : syracuseStep 443393 = 332545) B332545
theorem B214039 : Blo 195805 214039 := bstep (se 1 (by rfl) ⟨160529, by rfl⟩ : syracuseStep 214039 = 321059) B321059
theorem B672857 : Blo 195805 672857 := bstep (se 2 (by rfl) ⟨252321, by rfl⟩ : syracuseStep 672857 = 504643) B504643
theorem B279703 : Blo 195805 279703 := bstep (se 1 (by rfl) ⟨209777, by rfl⟩ : syracuseStep 279703 = 419555) B419555
theorem B672947 : Blo 195805 672947 := bstep (se 1 (by rfl) ⟨504710, by rfl⟩ : syracuseStep 672947 = 1009421) B1009421
theorem B836801 : Blo 195805 836801 := bstep (se 2 (by rfl) ⟨313800, by rfl⟩ : syracuseStep 836801 = 627601) B627601
theorem B443609 : Blo 195805 443609 := bstep (se 2 (by rfl) ⟨166353, by rfl⟩ : syracuseStep 443609 = 332707) B332707
theorem B705809 : Blo 195805 705809 := bstep (se 2 (by rfl) ⟨264678, by rfl⟩ : syracuseStep 705809 = 529357) B529357
theorem B443699 : Blo 195805 443699 := bstep (se 1 (by rfl) ⟨332774, by rfl⟩ : syracuseStep 443699 = 665549) B665549
theorem B443735 : Blo 195805 443735 := bstep (se 1 (by rfl) ⟨332801, by rfl⟩ : syracuseStep 443735 = 665603) B665603
theorem B378199 : Blo 195805 378199 := bstep (se 1 (by rfl) ⟨283649, by rfl⟩ : syracuseStep 378199 = 567299) B567299
theorem B705923 : Blo 195805 705923 := bstep (se 1 (by rfl) ⟨529442, by rfl⟩ : syracuseStep 705923 = 1058885) B1058885
theorem B1000835 : Blo 195805 1000835 := bstep (se 1 (by rfl) ⟨750626, by rfl⟩ : syracuseStep 1000835 = 1501253) B1501253
theorem B673217 : Blo 195805 673217 := bstep (se 2 (by rfl) ⟨252456, by rfl⟩ : syracuseStep 673217 = 504913) B504913
theorem B443915 : Blo 195805 443915 := bstep (se 1 (by rfl) ⟨332936, by rfl⟩ : syracuseStep 443915 = 665873) B665873
theorem B443969 : Blo 195805 443969 := bstep (se 2 (by rfl) ⟨166488, by rfl⟩ : syracuseStep 443969 = 332977) B332977
theorem B444185 : Blo 195805 444185 := bstep (se 2 (by rfl) ⟨166569, by rfl⟩ : syracuseStep 444185 = 333139) B333139
theorem B444275 : Blo 195805 444275 := bstep (se 1 (by rfl) ⟨333206, by rfl⟩ : syracuseStep 444275 = 666413) B666413
theorem B444311 : Blo 195805 444311 := bstep (se 1 (by rfl) ⟨333233, by rfl⟩ : syracuseStep 444311 = 666467) B666467
theorem B280523 : Blo 195805 280523 := bstep (se 1 (by rfl) ⟨210392, by rfl⟩ : syracuseStep 280523 = 420785) B420785
theorem B4376537 : Blo 195805 4376537 := bstep (se 2 (by rfl) ⟨1641201, by rfl⟩ : syracuseStep 4376537 = 3282403) B3282403
theorem B673757 : Blo 195805 673757 := bstep (se 3 (by rfl) ⟨126329, by rfl⟩ : syracuseStep 673757 = 252659) B252659
theorem B444491 : Blo 195805 444491 := bstep (se 1 (by rfl) ⟨333368, by rfl⟩ : syracuseStep 444491 = 666737) B666737
theorem B1427557 : Blo 195805 1427557 := bstep (se 4 (by rfl) ⟨133833, by rfl⟩ : syracuseStep 1427557 = 267667) B267667
theorem B444545 : Blo 195805 444545 := bstep (se 2 (by rfl) ⟨166704, by rfl⟩ : syracuseStep 444545 = 333409) B333409
theorem B1689731 : Blo 195805 1689731 := bstep (se 1 (by rfl) ⟨1267298, by rfl⟩ : syracuseStep 1689731 = 2534597) B2534597
theorem B379019 : Blo 195805 379019 := bstep (se 1 (by rfl) ⟨284264, by rfl⟩ : syracuseStep 379019 = 568529) B568529
theorem B379073 : Blo 195805 379073 := bstep (se 2 (by rfl) ⟨142152, by rfl⟩ : syracuseStep 379073 = 284305) B284305
theorem B2836781 : Blo 195805 2836781 := bstep (se 3 (by rfl) ⟨531896, by rfl⟩ : syracuseStep 2836781 = 1063793) B1063793
theorem B444761 : Blo 195805 444761 := bstep (se 2 (by rfl) ⟨166785, by rfl⟩ : syracuseStep 444761 = 333571) B333571
theorem B444851 : Blo 195805 444851 := bstep (se 1 (by rfl) ⟨333638, by rfl⟩ : syracuseStep 444851 = 667277) B667277
theorem B444887 : Blo 195805 444887 := bstep (se 1 (by rfl) ⟨333665, by rfl⟩ : syracuseStep 444887 = 667331) B667331
theorem B510553 : Blo 195805 510553 := bstep (se 2 (by rfl) ⟨191457, by rfl⟩ : syracuseStep 510553 = 382915) B382915
theorem B445067 : Blo 195805 445067 := bstep (se 1 (by rfl) ⟨333800, by rfl⟩ : syracuseStep 445067 = 667601) B667601
theorem B838289 : Blo 195805 838289 := bstep (se 2 (by rfl) ⟨314358, by rfl⟩ : syracuseStep 838289 = 628717) B628717
theorem B445121 : Blo 195805 445121 := bstep (se 2 (by rfl) ⟨166920, by rfl⟩ : syracuseStep 445121 = 333841) B333841
theorem B248599 : Blo 195805 248599 := bstep (se 1 (by rfl) ⟨186449, by rfl⟩ : syracuseStep 248599 = 372899) B372899
theorem B641881 : Blo 195805 641881 := bstep (se 2 (by rfl) ⟨240705, by rfl⟩ : syracuseStep 641881 = 481411) B481411
theorem B281497 : Blo 195805 281497 := bstep (se 2 (by rfl) ⟨105561, by rfl⟩ : syracuseStep 281497 = 211123) B211123
theorem B445337 : Blo 195805 445337 := bstep (se 2 (by rfl) ⟨167001, by rfl⟩ : syracuseStep 445337 = 334003) B334003
theorem B2411441 : Blo 195805 2411441 := bstep (se 2 (by rfl) ⟨904290, by rfl⟩ : syracuseStep 2411441 = 1808581) B1808581
theorem B445427 : Blo 195805 445427 := bstep (se 1 (by rfl) ⟨334070, by rfl⟩ : syracuseStep 445427 = 668141) B668141
theorem B445463 : Blo 195805 445463 := bstep (se 1 (by rfl) ⟨334097, by rfl⟩ : syracuseStep 445463 = 668195) B668195
theorem B445643 : Blo 195805 445643 := bstep (se 1 (by rfl) ⟨334232, by rfl⟩ : syracuseStep 445643 = 668465) B668465
theorem B445697 : Blo 195805 445697 := bstep (se 2 (by rfl) ⟨167136, by rfl⟩ : syracuseStep 445697 = 334273) B334273
theorem B478487 : Blo 195805 478487 := bstep (se 1 (by rfl) ⟨358865, by rfl⟩ : syracuseStep 478487 = 717731) B717731
theorem B1494449 : Blo 195805 1494449 := bstep (se 2 (by rfl) ⟨560418, by rfl⟩ : syracuseStep 1494449 = 1120837) B1120837
theorem B445913 : Blo 195805 445913 := bstep (se 2 (by rfl) ⟨167217, by rfl⟩ : syracuseStep 445913 = 334435) B334435
theorem B2870801 : Blo 195805 2870801 := bstep (se 2 (by rfl) ⟨1076550, by rfl⟩ : syracuseStep 2870801 = 2153101) B2153101
theorem B314903 : Blo 195805 314903 := bstep (se 1 (by rfl) ⟨236177, by rfl⟩ : syracuseStep 314903 = 472355) B472355
theorem B446003 : Blo 195805 446003 := bstep (se 1 (by rfl) ⟨334502, by rfl⟩ : syracuseStep 446003 = 669005) B669005
theorem B249419 : Blo 195805 249419 := bstep (se 1 (by rfl) ⟨187064, by rfl⟩ : syracuseStep 249419 = 374129) B374129
theorem B446039 : Blo 195805 446039 := bstep (se 1 (by rfl) ⟨334529, by rfl⟩ : syracuseStep 446039 = 669059) B669059
theorem B839261 : Blo 195805 839261 := bstep (se 3 (by rfl) ⟨157361, by rfl⟩ : syracuseStep 839261 = 314723) B314723
theorem B315031 : Blo 195805 315031 := bstep (se 1 (by rfl) ⟨236273, by rfl⟩ : syracuseStep 315031 = 472547) B472547
theorem B904877 : Blo 195805 904877 := bstep (se 3 (by rfl) ⟨169664, by rfl⟩ : syracuseStep 904877 = 339329) B339329
theorem B315095 : Blo 195805 315095 := bstep (se 1 (by rfl) ⟨236321, by rfl⟩ : syracuseStep 315095 = 472643) B472643
theorem B446219 : Blo 195805 446219 := bstep (se 1 (by rfl) ⟨334664, by rfl⟩ : syracuseStep 446219 = 669329) B669329
theorem B1265453 : Blo 195805 1265453 := bstep (se 3 (by rfl) ⟨237272, by rfl⟩ : syracuseStep 1265453 = 474545) B474545
theorem B446273 : Blo 195805 446273 := bstep (se 2 (by rfl) ⟨167352, by rfl⟩ : syracuseStep 446273 = 334705) B334705
theorem B1494935 : Blo 195805 1494935 := bstep (se 1 (by rfl) ⟨1121201, by rfl⟩ : syracuseStep 1494935 = 2242403) B2242403
theorem B282647 : Blo 195805 282647 := bstep (se 1 (by rfl) ⟨211985, by rfl⟩ : syracuseStep 282647 = 423971) B423971
theorem B446489 : Blo 195805 446489 := bstep (se 2 (by rfl) ⟨167433, by rfl⟩ : syracuseStep 446489 = 334867) B334867
theorem B446579 : Blo 195805 446579 := bstep (se 1 (by rfl) ⟨334934, by rfl⟩ : syracuseStep 446579 = 669869) B669869
theorem B446615 : Blo 195805 446615 := bstep (se 1 (by rfl) ⟨334961, by rfl⟩ : syracuseStep 446615 = 669923) B669923
theorem B1527959 : Blo 195805 1527959 := bstep (se 1 (by rfl) ⟨1145969, by rfl⟩ : syracuseStep 1527959 = 2291939) B2291939
theorem B250123 : Blo 195805 250123 := bstep (se 1 (by rfl) ⟨187592, by rfl⟩ : syracuseStep 250123 = 375185) B375185
theorem B446795 : Blo 195805 446795 := bstep (se 1 (by rfl) ⟨335096, by rfl⟩ : syracuseStep 446795 = 670193) B670193
theorem B282955 : Blo 195805 282955 := bstep (se 1 (by rfl) ⟨212216, by rfl⟩ : syracuseStep 282955 = 424433) B424433
theorem B446849 : Blo 195805 446849 := bstep (se 2 (by rfl) ⟨167568, by rfl⟩ : syracuseStep 446849 = 335137) B335137
theorem B250391 : Blo 195805 250391 := bstep (se 1 (by rfl) ⟨187793, by rfl⟩ : syracuseStep 250391 = 375587) B375587
theorem B709165 : Blo 195805 709165 := bstep (se 3 (by rfl) ⟨132968, by rfl⟩ : syracuseStep 709165 = 265937) B265937
theorem B447065 : Blo 195805 447065 := bstep (se 2 (by rfl) ⟨167649, by rfl⟩ : syracuseStep 447065 = 335299) B335299
theorem B1135235 : Blo 195805 1135235 := bstep (se 1 (by rfl) ⟨851426, by rfl⟩ : syracuseStep 1135235 = 1702853) B1702853
theorem B447155 : Blo 195805 447155 := bstep (se 1 (by rfl) ⟨335366, by rfl⟩ : syracuseStep 447155 = 670733) B670733
theorem B447191 : Blo 195805 447191 := bstep (se 1 (by rfl) ⟨335393, by rfl⟩ : syracuseStep 447191 = 670787) B670787
theorem B447371 : Blo 195805 447371 := bstep (se 1 (by rfl) ⟨335528, by rfl⟩ : syracuseStep 447371 = 671057) B671057
theorem B447425 : Blo 195805 447425 := bstep (se 2 (by rfl) ⟨167784, by rfl⟩ : syracuseStep 447425 = 335569) B335569
theorem B1004561 : Blo 195805 1004561 := bstep (se 2 (by rfl) ⟨376710, by rfl⟩ : syracuseStep 1004561 = 753421) B753421
theorem B1135691 : Blo 195805 1135691 := bstep (se 1 (by rfl) ⟨851768, by rfl⟩ : syracuseStep 1135691 = 1703537) B1703537
theorem B447641 : Blo 195805 447641 := bstep (se 2 (by rfl) ⟨167865, by rfl⟩ : syracuseStep 447641 = 335731) B335731
theorem B1004723 : Blo 195805 1004723 := bstep (se 1 (by rfl) ⟨753542, by rfl⟩ : syracuseStep 1004723 = 1507085) B1507085
theorem B251095 : Blo 195805 251095 := bstep (se 1 (by rfl) ⟨188321, by rfl⟩ : syracuseStep 251095 = 376643) B376643
theorem B447731 : Blo 195805 447731 := bstep (se 1 (by rfl) ⟨335798, by rfl⟩ : syracuseStep 447731 = 671597) B671597
theorem B447767 : Blo 195805 447767 := bstep (se 1 (by rfl) ⟨335825, by rfl⟩ : syracuseStep 447767 = 671651) B671651
theorem B283991 : Blo 195805 283991 := bstep (se 1 (by rfl) ⟨212993, by rfl⟩ : syracuseStep 283991 = 425987) B425987
theorem B447947 : Blo 195805 447947 := bstep (se 1 (by rfl) ⟨335960, by rfl⟩ : syracuseStep 447947 = 671921) B671921
theorem B448001 : Blo 195805 448001 := bstep (se 2 (by rfl) ⟨168000, by rfl⟩ : syracuseStep 448001 = 336001) B336001
theorem B284185 : Blo 195805 284185 := bstep (se 2 (by rfl) ⟨106569, by rfl⟩ : syracuseStep 284185 = 213139) B213139
theorem B382529 : Blo 195805 382529 := bstep (se 2 (by rfl) ⟨143448, by rfl⟩ : syracuseStep 382529 = 286897) B286897
theorem B317081 : Blo 195805 317081 := bstep (se 2 (by rfl) ⟨118905, by rfl⟩ : syracuseStep 317081 = 237811) B237811
theorem B448217 : Blo 195805 448217 := bstep (se 2 (by rfl) ⟨168081, by rfl⟩ : syracuseStep 448217 = 336163) B336163
theorem B448307 : Blo 195805 448307 := bstep (se 1 (by rfl) ⟨336230, by rfl⟩ : syracuseStep 448307 = 672461) B672461
theorem B448343 : Blo 195805 448343 := bstep (se 1 (by rfl) ⟨336257, by rfl⟩ : syracuseStep 448343 = 672515) B672515
theorem B677783 : Blo 195805 677783 := bstep (se 1 (by rfl) ⟨508337, by rfl⟩ : syracuseStep 677783 = 1016675) B1016675
theorem B448523 : Blo 195805 448523 := bstep (se 1 (by rfl) ⟨336392, by rfl⟩ : syracuseStep 448523 = 672785) B672785
theorem B743489 : Blo 195805 743489 := bstep (se 2 (by rfl) ⟨278808, by rfl⟩ : syracuseStep 743489 = 557617) B557617
theorem B448577 : Blo 195805 448577 := bstep (se 2 (by rfl) ⟨168216, by rfl⟩ : syracuseStep 448577 = 336433) B336433
theorem B841859 : Blo 195805 841859 := bstep (se 1 (by rfl) ⟨631394, by rfl⟩ : syracuseStep 841859 = 1262789) B1262789
theorem B448793 : Blo 195805 448793 := bstep (se 2 (by rfl) ⟨168297, by rfl⟩ : syracuseStep 448793 = 336595) B336595
theorem B448883 : Blo 195805 448883 := bstep (se 1 (by rfl) ⟨336662, by rfl⟩ : syracuseStep 448883 = 673325) B673325
theorem B448919 : Blo 195805 448919 := bstep (se 1 (by rfl) ⟨336689, by rfl⟩ : syracuseStep 448919 = 673379) B673379
theorem B842201 : Blo 195805 842201 := bstep (se 2 (by rfl) ⟨315825, by rfl⟩ : syracuseStep 842201 = 631651) B631651
theorem B449099 : Blo 195805 449099 := bstep (se 1 (by rfl) ⟨336824, by rfl⟩ : syracuseStep 449099 = 673649) B673649
theorem B449153 : Blo 195805 449153 := bstep (se 2 (by rfl) ⟨168432, by rfl⟩ : syracuseStep 449153 = 336865) B336865
theorem B711299 : Blo 195805 711299 := bstep (se 1 (by rfl) ⟨533474, by rfl⟩ : syracuseStep 711299 = 1066949) B1066949
theorem B449369 : Blo 195805 449369 := bstep (se 2 (by rfl) ⟨168513, by rfl⟩ : syracuseStep 449369 = 337027) B337027
theorem B1268581 : Blo 195805 1268581 := bstep (se 4 (by rfl) ⟨118929, by rfl⟩ : syracuseStep 1268581 = 237859) B237859
theorem B252811 : Blo 195805 252811 := bstep (se 1 (by rfl) ⟨189608, by rfl⟩ : syracuseStep 252811 = 379217) B379217
theorem B449459 : Blo 195805 449459 := bstep (se 1 (by rfl) ⟨337094, by rfl⟩ : syracuseStep 449459 = 674189) B674189
theorem B449495 : Blo 195805 449495 := bstep (se 1 (by rfl) ⟨337121, by rfl⟩ : syracuseStep 449495 = 674243) B674243
theorem B1006667 : Blo 195805 1006667 := bstep (se 1 (by rfl) ⟨755000, by rfl⟩ : syracuseStep 1006667 = 1510001) B1510001
theorem B220459 : Blo 195805 220459 := bstep (se 1 (by rfl) ⟨165344, by rfl⟩ : syracuseStep 220459 = 330689) B330689
theorem B220567 : Blo 195805 220567 := bstep (se 1 (by rfl) ⟨165425, by rfl⟩ : syracuseStep 220567 = 330851) B330851
theorem B744977 : Blo 195805 744977 := bstep (se 2 (by rfl) ⟨279366, by rfl⟩ : syracuseStep 744977 = 558733) B558733
theorem B1433153 : Blo 195805 1433153 := bstep (se 2 (by rfl) ⟨537432, by rfl⟩ : syracuseStep 1433153 = 1074865) B1074865
theorem B220747 : Blo 195805 220747 := bstep (se 1 (by rfl) ⟨165560, by rfl⟩ : syracuseStep 220747 = 331121) B331121
theorem B679603 : Blo 195805 679603 := bstep (se 1 (by rfl) ⟨509702, by rfl⟩ : syracuseStep 679603 = 1019405) B1019405
theorem B220855 : Blo 195805 220855 := bstep (se 1 (by rfl) ⟨165641, by rfl⟩ : syracuseStep 220855 = 331283) B331283
theorem B2252609 : Blo 195805 2252609 := bstep (se 2 (by rfl) ⟨844728, by rfl⟩ : syracuseStep 2252609 = 1689457) B1689457
theorem B221035 : Blo 195805 221035 := bstep (se 1 (by rfl) ⟨165776, by rfl⟩ : syracuseStep 221035 = 331553) B331553
theorem B221143 : Blo 195805 221143 := bstep (se 1 (by rfl) ⟨165857, by rfl⟩ : syracuseStep 221143 = 331715) B331715
theorem B745433 : Blo 195805 745433 := bstep (se 2 (by rfl) ⟨279537, by rfl⟩ : syracuseStep 745433 = 559075) B559075
theorem B221323 : Blo 195805 221323 := bstep (se 1 (by rfl) ⟨165992, by rfl⟩ : syracuseStep 221323 = 331985) B331985
theorem B745645 : Blo 195805 745645 := bstep (se 3 (by rfl) ⟨139808, by rfl⟩ : syracuseStep 745645 = 279617) B279617
theorem B221431 : Blo 195805 221431 := bstep (se 1 (by rfl) ⟨166073, by rfl⟩ : syracuseStep 221431 = 332147) B332147
theorem B1073483 : Blo 195805 1073483 := bstep (se 1 (by rfl) ⟨805112, by rfl⟩ : syracuseStep 1073483 = 1610225) B1610225
theorem B221611 : Blo 195805 221611 := bstep (se 1 (by rfl) ⟨166208, by rfl⟩ : syracuseStep 221611 = 332417) B332417
theorem B745949 : Blo 195805 745949 := bstep (se 3 (by rfl) ⟨139865, by rfl⟩ : syracuseStep 745949 = 279731) B279731
theorem B221719 : Blo 195805 221719 := bstep (se 1 (by rfl) ⟨166289, by rfl⟩ : syracuseStep 221719 = 332579) B332579
theorem B221899 : Blo 195805 221899 := bstep (se 1 (by rfl) ⟨166424, by rfl⟩ : syracuseStep 221899 = 332849) B332849
theorem B222007 : Blo 195805 222007 := bstep (se 1 (by rfl) ⟨166505, by rfl⟩ : syracuseStep 222007 = 333011) B333011
theorem B1008449 : Blo 195805 1008449 := bstep (se 2 (by rfl) ⟨378168, by rfl⟩ : syracuseStep 1008449 = 756337) B756337
theorem B2417525 : Blo 195805 2417525 := bstep (se 5 (by rfl) ⟨113321, by rfl⟩ : syracuseStep 2417525 = 226643) B226643
theorem B222187 : Blo 195805 222187 := bstep (se 1 (by rfl) ⟨166640, by rfl⟩ : syracuseStep 222187 = 333281) B333281
theorem B222295 : Blo 195805 222295 := bstep (se 1 (by rfl) ⟨166721, by rfl⟩ : syracuseStep 222295 = 333443) B333443
theorem B353459 : Blo 195805 353459 := bstep (se 1 (by rfl) ⟨265094, by rfl⟩ : syracuseStep 353459 = 530189) B530189
theorem B910529 : Blo 195805 910529 := bstep (se 2 (by rfl) ⟨341448, by rfl⟩ : syracuseStep 910529 = 682897) B682897
theorem B419033 : Blo 195805 419033 := bstep (se 2 (by rfl) ⟨157137, by rfl⟩ : syracuseStep 419033 = 314275) B314275
theorem B222475 : Blo 195805 222475 := bstep (se 1 (by rfl) ⟨166856, by rfl⟩ : syracuseStep 222475 = 333713) B333713
theorem B222583 : Blo 195805 222583 := bstep (se 1 (by rfl) ⟨166937, by rfl⟩ : syracuseStep 222583 = 333875) B333875
theorem B222763 : Blo 195805 222763 := bstep (se 1 (by rfl) ⟨167072, by rfl⟩ : syracuseStep 222763 = 334145) B334145
theorem B222871 : Blo 195805 222871 := bstep (se 1 (by rfl) ⟨167153, by rfl⟩ : syracuseStep 222871 = 334307) B334307
theorem B845585 : Blo 195805 845585 := bstep (se 2 (by rfl) ⟨317094, by rfl⟩ : syracuseStep 845585 = 634189) B634189
theorem B223051 : Blo 195805 223051 := bstep (se 1 (by rfl) ⟨167288, by rfl⟩ : syracuseStep 223051 = 334577) B334577
theorem B419699 : Blo 195805 419699 := bstep (se 1 (by rfl) ⟨314774, by rfl⟩ : syracuseStep 419699 = 629549) B629549
theorem B223159 : Blo 195805 223159 := bstep (se 1 (by rfl) ⟨167369, by rfl⟩ : syracuseStep 223159 = 334739) B334739
theorem B714689 : Blo 195805 714689 := bstep (se 2 (by rfl) ⟨268008, by rfl⟩ : syracuseStep 714689 = 536017) B536017
theorem B223339 : Blo 195805 223339 := bstep (se 1 (by rfl) ⟨167504, by rfl⟩ : syracuseStep 223339 = 335009) B335009
theorem B813235 : Blo 195805 813235 := bstep (se 1 (by rfl) ⟨609926, by rfl⟩ : syracuseStep 813235 = 1219853) B1219853
theorem B223447 : Blo 195805 223447 := bstep (se 1 (by rfl) ⟨167585, by rfl⟩ : syracuseStep 223447 = 335171) B335171
theorem B4253957 : Blo 195805 4253957 := bstep (se 4 (by rfl) ⟨398808, by rfl⟩ : syracuseStep 4253957 = 797617) B797617
theorem B944477 : Blo 195805 944477 := bstep (se 3 (by rfl) ⟨177089, by rfl⟩ : syracuseStep 944477 = 354179) B354179
theorem B223627 : Blo 195805 223627 := bstep (se 1 (by rfl) ⟨167720, by rfl⟩ : syracuseStep 223627 = 335441) B335441
theorem B846301 : Blo 195805 846301 := bstep (se 3 (by rfl) ⟨158681, by rfl⟩ : syracuseStep 846301 = 317363) B317363
theorem B223735 : Blo 195805 223735 := bstep (se 1 (by rfl) ⟨167801, by rfl⟩ : syracuseStep 223735 = 335603) B335603
theorem B3238469 : Blo 195805 3238469 := bstep (se 4 (by rfl) ⟨303606, by rfl⟩ : syracuseStep 3238469 = 607213) B607213
theorem B223915 : Blo 195805 223915 := bstep (se 1 (by rfl) ⟨167936, by rfl⟩ : syracuseStep 223915 = 335873) B335873
theorem B453313 : Blo 195805 453313 := bstep (se 2 (by rfl) ⟨169992, by rfl⟩ : syracuseStep 453313 = 339985) B339985
theorem B1010393 : Blo 195805 1010393 := bstep (se 2 (by rfl) ⟨378897, by rfl⟩ : syracuseStep 1010393 = 757795) B757795
theorem B224023 : Blo 195805 224023 := bstep (se 1 (by rfl) ⟨168017, by rfl⟩ : syracuseStep 224023 = 336035) B336035
theorem B224203 : Blo 195805 224203 := bstep (se 1 (by rfl) ⟨168152, by rfl⟩ : syracuseStep 224203 = 336305) B336305
theorem B748547 : Blo 195805 748547 := bstep (se 1 (by rfl) ⟨561410, by rfl⟩ : syracuseStep 748547 = 1122821) B1122821
theorem B748561 : Blo 195805 748561 := bstep (se 2 (by rfl) ⟨280710, by rfl⟩ : syracuseStep 748561 = 561421) B561421
theorem B1502225 : Blo 195805 1502225 := bstep (se 2 (by rfl) ⟨563334, by rfl⟩ : syracuseStep 1502225 = 1126669) B1126669
theorem B2583587 : Blo 195805 2583587 := bstep (se 1 (by rfl) ⟨1937690, by rfl⟩ : syracuseStep 2583587 = 3875381) B3875381
theorem B224311 : Blo 195805 224311 := bstep (se 1 (by rfl) ⟨168233, by rfl⟩ : syracuseStep 224311 = 336467) B336467
theorem B224491 : Blo 195805 224491 := bstep (se 1 (by rfl) ⟨168368, by rfl⟩ : syracuseStep 224491 = 336737) B336737
theorem B748865 : Blo 195805 748865 := bstep (se 2 (by rfl) ⟨280824, by rfl⟩ : syracuseStep 748865 = 561649) B561649
theorem B421195 : Blo 195805 421195 := bstep (se 1 (by rfl) ⟨315896, by rfl⟩ : syracuseStep 421195 = 631793) B631793
theorem B224599 : Blo 195805 224599 := bstep (se 1 (by rfl) ⟨168449, by rfl⟩ : syracuseStep 224599 = 336899) B336899
theorem B355673 : Blo 195805 355673 := bstep (se 2 (by rfl) ⟨133377, by rfl⟩ : syracuseStep 355673 = 266755) B266755
theorem B224779 : Blo 195805 224779 := bstep (se 1 (by rfl) ⟨168584, by rfl⟩ : syracuseStep 224779 = 337169) B337169
theorem B2420375 : Blo 195805 2420375 := bstep (se 1 (by rfl) ⟨1815281, by rfl⟩ : syracuseStep 2420375 = 3630563) B3630563
theorem B3764069 : Blo 195805 3764069 := bstep (se 4 (by rfl) ⟨352881, by rfl⟩ : syracuseStep 3764069 = 705763) B705763
theorem B749533 : Blo 195805 749533 := bstep (se 3 (by rfl) ⟨140537, by rfl⟩ : syracuseStep 749533 = 281075) B281075
theorem B454681 : Blo 195805 454681 := bstep (se 2 (by rfl) ⟨170505, by rfl⟩ : syracuseStep 454681 = 341011) B341011
theorem B1077569 : Blo 195805 1077569 := bstep (se 2 (by rfl) ⟨404088, by rfl⟩ : syracuseStep 1077569 = 808177) B808177
theorem B1700189 : Blo 195805 1700189 := bstep (se 3 (by rfl) ⟨318785, by rfl⟩ : syracuseStep 1700189 = 637571) B637571
theorem B422425 : Blo 195805 422425 := bstep (se 2 (by rfl) ⟨158409, by rfl⟩ : syracuseStep 422425 = 316819) B316819
theorem B2716253 : Blo 195805 2716253 := bstep (se 3 (by rfl) ⟨509297, by rfl⟩ : syracuseStep 2716253 = 1018595) B1018595
theorem B717457 : Blo 195805 717457 := bstep (se 2 (by rfl) ⟨269046, by rfl⟩ : syracuseStep 717457 = 538093) B538093
theorem B685003 : Blo 195805 685003 := bstep (se 1 (by rfl) ⟨513752, by rfl⟩ : syracuseStep 685003 = 1027505) B1027505
theorem B1700939 : Blo 195805 1700939 := bstep (se 1 (by rfl) ⟨1275704, by rfl⟩ : syracuseStep 1700939 = 2551409) B2551409
theorem B750809 : Blo 195805 750809 := bstep (se 2 (by rfl) ⟨281553, by rfl⟩ : syracuseStep 750809 = 563107) B563107
theorem B357655 : Blo 195805 357655 := bstep (se 1 (by rfl) ⟨268241, by rfl⟩ : syracuseStep 357655 = 536483) B536483
theorem B3372353 : Blo 195805 3372353 := bstep (se 2 (by rfl) ⟨1264632, by rfl⟩ : syracuseStep 3372353 = 2529265) B2529265
theorem B1930787 : Blo 195805 1930787 := bstep (se 1 (by rfl) ⟨1448090, by rfl⟩ : syracuseStep 1930787 = 2896181) B2896181
theorem B226999 : Blo 195805 226999 := bstep (se 1 (by rfl) ⟨170249, by rfl⟩ : syracuseStep 226999 = 340499) B340499
theorem B358361 : Blo 195805 358361 := bstep (se 2 (by rfl) ⟨134385, by rfl⟩ : syracuseStep 358361 = 268771) B268771
theorem B849923 : Blo 195805 849923 := bstep (se 1 (by rfl) ⟨637442, by rfl⟩ : syracuseStep 849923 = 1274885) B1274885
theorem B2128193 : Blo 195805 2128193 := bstep (se 2 (by rfl) ⟨798072, by rfl⟩ : syracuseStep 2128193 = 1596145) B1596145
theorem B948611 : Blo 195805 948611 := bstep (se 1 (by rfl) ⟨711458, by rfl⟩ : syracuseStep 948611 = 1422917) B1422917
theorem B1702579 : Blo 195805 1702579 := bstep (se 1 (by rfl) ⟨1276934, by rfl⟩ : syracuseStep 1702579 = 2553869) B2553869
theorem B752435 : Blo 195805 752435 := bstep (se 1 (by rfl) ⟨564326, by rfl⟩ : syracuseStep 752435 = 1128653) B1128653
theorem B752449 : Blo 195805 752449 := bstep (se 2 (by rfl) ⟨282168, by rfl⟩ : syracuseStep 752449 = 564337) B564337
theorem B1506113 : Blo 195805 1506113 := bstep (se 2 (by rfl) ⟨564792, by rfl⟩ : syracuseStep 1506113 = 1129585) B1129585
theorem B293771 : Blo 195805 293771 := bstep (se 1 (by rfl) ⟨220328, by rfl⟩ : syracuseStep 293771 = 440657) B440657
theorem B293783 : Blo 195805 293783 := bstep (se 1 (by rfl) ⟨220337, by rfl⟩ : syracuseStep 293783 = 440675) B440675
theorem B293849 : Blo 195805 293849 := bstep (se 2 (by rfl) ⟨110193, by rfl⟩ : syracuseStep 293849 = 220387) B220387
theorem B293963 : Blo 195805 293963 := bstep (se 1 (by rfl) ⟨220472, by rfl⟩ : syracuseStep 293963 = 440945) B440945
theorem B228427 : Blo 195805 228427 := bstep (se 1 (by rfl) ⟨171320, by rfl⟩ : syracuseStep 228427 = 342641) B342641
theorem B293975 : Blo 195805 293975 := bstep (se 1 (by rfl) ⟨220481, by rfl⟩ : syracuseStep 293975 = 440963) B440963
theorem B294041 : Blo 195805 294041 := bstep (se 2 (by rfl) ⟨110265, by rfl⟩ : syracuseStep 294041 = 220531) B220531
theorem B720065 : Blo 195805 720065 := bstep (se 2 (by rfl) ⟨270024, by rfl⟩ : syracuseStep 720065 = 540049) B540049
theorem B195819 : Blo 195805 195819 := bstep (se 1 (by rfl) ⟨146864, by rfl⟩ : syracuseStep 195819 = 293729) B293729
theorem B195831 : Blo 195805 195831 := bstep (se 1 (by rfl) ⟨146873, by rfl⟩ : syracuseStep 195831 = 293747) B293747
theorem B195851 : Blo 195805 195851 := bstep (se 1 (by rfl) ⟨146888, by rfl⟩ : syracuseStep 195851 = 293777) B293777
theorem B294155 : Blo 195805 294155 := bstep (se 1 (by rfl) ⟨220616, by rfl⟩ : syracuseStep 294155 = 441233) B441233
theorem B195863 : Blo 195805 195863 := bstep (se 1 (by rfl) ⟨146897, by rfl⟩ : syracuseStep 195863 = 293795) B293795
theorem B294167 : Blo 195805 294167 := bstep (se 1 (by rfl) ⟨220625, by rfl⟩ : syracuseStep 294167 = 441251) B441251
theorem B195883 : Blo 195805 195883 := bstep (se 1 (by rfl) ⟨146912, by rfl⟩ : syracuseStep 195883 = 293825) B293825
theorem B195895 : Blo 195805 195895 := bstep (se 1 (by rfl) ⟨146921, by rfl⟩ : syracuseStep 195895 = 293843) B293843
theorem B195915 : Blo 195805 195915 := bstep (se 1 (by rfl) ⟨146936, by rfl⟩ : syracuseStep 195915 = 293873) B293873
theorem B195927 : Blo 195805 195927 := bstep (se 1 (by rfl) ⟨146945, by rfl⟩ : syracuseStep 195927 = 293891) B293891
theorem B294233 : Blo 195805 294233 := bstep (se 2 (by rfl) ⟨110337, by rfl⟩ : syracuseStep 294233 = 220675) B220675
theorem B425305 : Blo 195805 425305 := bstep (se 2 (by rfl) ⟨159489, by rfl⟩ : syracuseStep 425305 = 318979) B318979
theorem B195947 : Blo 195805 195947 := bstep (se 1 (by rfl) ⟨146960, by rfl⟩ : syracuseStep 195947 = 293921) B293921
theorem B195959 : Blo 195805 195959 := bstep (se 1 (by rfl) ⟨146969, by rfl⟩ : syracuseStep 195959 = 293939) B293939
theorem B195979 : Blo 195805 195979 := bstep (se 1 (by rfl) ⟨146984, by rfl⟩ : syracuseStep 195979 = 293969) B293969
theorem B195991 : Blo 195805 195991 := bstep (se 1 (by rfl) ⟨146993, by rfl⟩ : syracuseStep 195991 = 293987) B293987
theorem B196011 : Blo 195805 196011 := bstep (se 1 (by rfl) ⟨147008, by rfl⟩ : syracuseStep 196011 = 294017) B294017
theorem B196023 : Blo 195805 196023 := bstep (se 1 (by rfl) ⟨147017, by rfl⟩ : syracuseStep 196023 = 294035) B294035
theorem B851393 : Blo 195805 851393 := bstep (se 2 (by rfl) ⟨319272, by rfl⟩ : syracuseStep 851393 = 638545) B638545
theorem B196043 : Blo 195805 196043 := bstep (se 1 (by rfl) ⟨147032, by rfl⟩ : syracuseStep 196043 = 294065) B294065
theorem B294347 : Blo 195805 294347 := bstep (se 1 (by rfl) ⟨220760, by rfl⟩ : syracuseStep 294347 = 441521) B441521
theorem B196055 : Blo 195805 196055 := bstep (se 1 (by rfl) ⟨147041, by rfl⟩ : syracuseStep 196055 = 294083) B294083
theorem B294359 : Blo 195805 294359 := bstep (se 1 (by rfl) ⟨220769, by rfl⟩ : syracuseStep 294359 = 441539) B441539
theorem B196075 : Blo 195805 196075 := bstep (se 1 (by rfl) ⟨147056, by rfl⟩ : syracuseStep 196075 = 294113) B294113
theorem B196087 : Blo 195805 196087 := bstep (se 1 (by rfl) ⟨147065, by rfl⟩ : syracuseStep 196087 = 294131) B294131
theorem B196107 : Blo 195805 196107 := bstep (se 1 (by rfl) ⟨147080, by rfl⟩ : syracuseStep 196107 = 294161) B294161
theorem B196119 : Blo 195805 196119 := bstep (se 1 (by rfl) ⟨147089, by rfl⟩ : syracuseStep 196119 = 294179) B294179
theorem B294425 : Blo 195805 294425 := bstep (se 2 (by rfl) ⟨110409, by rfl⟩ : syracuseStep 294425 = 220819) B220819
theorem B196139 : Blo 195805 196139 := bstep (se 1 (by rfl) ⟨147104, by rfl⟩ : syracuseStep 196139 = 294209) B294209
theorem B196151 : Blo 195805 196151 := bstep (se 1 (by rfl) ⟨147113, by rfl⟩ : syracuseStep 196151 = 294227) B294227
theorem B1015361 : Blo 195805 1015361 := bstep (se 2 (by rfl) ⟨380760, by rfl⟩ : syracuseStep 1015361 = 761521) B761521
theorem B196171 : Blo 195805 196171 := bstep (se 1 (by rfl) ⟨147128, by rfl⟩ : syracuseStep 196171 = 294257) B294257
theorem B196183 : Blo 195805 196183 := bstep (se 1 (by rfl) ⟨147137, by rfl⟩ : syracuseStep 196183 = 294275) B294275
theorem B196203 : Blo 195805 196203 := bstep (se 1 (by rfl) ⟨147152, by rfl⟩ : syracuseStep 196203 = 294305) B294305
theorem B196215 : Blo 195805 196215 := bstep (se 1 (by rfl) ⟨147161, by rfl⟩ : syracuseStep 196215 = 294323) B294323
theorem B196235 : Blo 195805 196235 := bstep (se 1 (by rfl) ⟨147176, by rfl⟩ : syracuseStep 196235 = 294353) B294353
theorem B294539 : Blo 195805 294539 := bstep (se 1 (by rfl) ⟨220904, by rfl⟩ : syracuseStep 294539 = 441809) B441809
theorem B425611 : Blo 195805 425611 := bstep (se 1 (by rfl) ⟨319208, by rfl⟩ : syracuseStep 425611 = 638417) B638417
theorem B196247 : Blo 195805 196247 := bstep (se 1 (by rfl) ⟨147185, by rfl⟩ : syracuseStep 196247 = 294371) B294371
theorem B294551 : Blo 195805 294551 := bstep (se 1 (by rfl) ⟨220913, by rfl⟩ : syracuseStep 294551 = 441827) B441827
theorem B196267 : Blo 195805 196267 := bstep (se 1 (by rfl) ⟨147200, by rfl⟩ : syracuseStep 196267 = 294401) B294401
theorem B196279 : Blo 195805 196279 := bstep (se 1 (by rfl) ⟨147209, by rfl⟩ : syracuseStep 196279 = 294419) B294419
theorem B196299 : Blo 195805 196299 := bstep (se 1 (by rfl) ⟨147224, by rfl⟩ : syracuseStep 196299 = 294449) B294449
theorem B196311 : Blo 195805 196311 := bstep (se 1 (by rfl) ⟨147233, by rfl⟩ : syracuseStep 196311 = 294467) B294467
theorem B294617 : Blo 195805 294617 := bstep (se 2 (by rfl) ⟨110481, by rfl⟩ : syracuseStep 294617 = 220963) B220963
theorem B196331 : Blo 195805 196331 := bstep (se 1 (by rfl) ⟨147248, by rfl⟩ : syracuseStep 196331 = 294497) B294497
theorem B196343 : Blo 195805 196343 := bstep (se 1 (by rfl) ⟨147257, by rfl⟩ : syracuseStep 196343 = 294515) B294515
theorem B196363 : Blo 195805 196363 := bstep (se 1 (by rfl) ⟨147272, by rfl⟩ : syracuseStep 196363 = 294545) B294545
theorem B196375 : Blo 195805 196375 := bstep (se 1 (by rfl) ⟨147281, by rfl⟩ : syracuseStep 196375 = 294563) B294563
theorem B851735 : Blo 195805 851735 := bstep (se 1 (by rfl) ⟨638801, by rfl⟩ : syracuseStep 851735 = 1277603) B1277603
theorem B196395 : Blo 195805 196395 := bstep (se 1 (by rfl) ⟨147296, by rfl⟩ : syracuseStep 196395 = 294593) B294593
theorem B196407 : Blo 195805 196407 := bstep (se 1 (by rfl) ⟨147305, by rfl⟩ : syracuseStep 196407 = 294611) B294611
theorem B196427 : Blo 195805 196427 := bstep (se 1 (by rfl) ⟨147320, by rfl⟩ : syracuseStep 196427 = 294641) B294641
theorem B294731 : Blo 195805 294731 := bstep (se 1 (by rfl) ⟨221048, by rfl⟩ : syracuseStep 294731 = 442097) B442097
theorem B196439 : Blo 195805 196439 := bstep (se 1 (by rfl) ⟨147329, by rfl⟩ : syracuseStep 196439 = 294659) B294659
theorem B294743 : Blo 195805 294743 := bstep (se 1 (by rfl) ⟨221057, by rfl⟩ : syracuseStep 294743 = 442115) B442115
theorem B196459 : Blo 195805 196459 := bstep (se 1 (by rfl) ⟨147344, by rfl⟩ : syracuseStep 196459 = 294689) B294689
theorem B196471 : Blo 195805 196471 := bstep (se 1 (by rfl) ⟨147353, by rfl⟩ : syracuseStep 196471 = 294707) B294707
theorem B196491 : Blo 195805 196491 := bstep (se 1 (by rfl) ⟨147368, by rfl⟩ : syracuseStep 196491 = 294737) B294737
theorem B196503 : Blo 195805 196503 := bstep (se 1 (by rfl) ⟨147377, by rfl⟩ : syracuseStep 196503 = 294755) B294755
theorem B294809 : Blo 195805 294809 := bstep (se 2 (by rfl) ⟨110553, by rfl⟩ : syracuseStep 294809 = 221107) B221107
theorem B196523 : Blo 195805 196523 := bstep (se 1 (by rfl) ⟨147392, by rfl⟩ : syracuseStep 196523 = 294785) B294785
theorem B196535 : Blo 195805 196535 := bstep (se 1 (by rfl) ⟨147401, by rfl⟩ : syracuseStep 196535 = 294803) B294803
theorem B196555 : Blo 195805 196555 := bstep (se 1 (by rfl) ⟨147416, by rfl⟩ : syracuseStep 196555 = 294833) B294833
theorem B196567 : Blo 195805 196567 := bstep (se 1 (by rfl) ⟨147425, by rfl⟩ : syracuseStep 196567 = 294851) B294851
theorem B196587 : Blo 195805 196587 := bstep (se 1 (by rfl) ⟨147440, by rfl⟩ : syracuseStep 196587 = 294881) B294881
theorem B196599 : Blo 195805 196599 := bstep (se 1 (by rfl) ⟨147449, by rfl⟩ : syracuseStep 196599 = 294899) B294899
theorem B196615 : Blo 195805 196615 := bstep (se 1 (by rfl) ⟨147461, by rfl⟩ : syracuseStep 196615 = 294923) B294923
theorem B196623 : Blo 195805 196623 := bstep (se 1 (by rfl) ⟨147467, by rfl⟩ : syracuseStep 196623 = 294935) B294935
theorem B294971 : Blo 195805 294971 := bstep (se 1 (by rfl) ⟨221228, by rfl⟩ : syracuseStep 294971 = 442457) B442457
theorem B196667 : Blo 195805 196667 := bstep (se 1 (by rfl) ⟨147500, by rfl⟩ : syracuseStep 196667 = 295001) B295001
theorem B753725 : Blo 195805 753725 := bstep (se 3 (by rfl) ⟨141323, by rfl⟩ : syracuseStep 753725 = 282647) B282647
theorem B295031 : Blo 195805 295031 := bstep (se 1 (by rfl) ⟨221273, by rfl⟩ : syracuseStep 295031 = 442547) B442547
theorem B196743 : Blo 195805 196743 := bstep (se 1 (by rfl) ⟨147557, by rfl⟩ : syracuseStep 196743 = 295115) B295115
theorem B295055 : Blo 195805 295055 := bstep (se 1 (by rfl) ⟨221291, by rfl⟩ : syracuseStep 295055 = 442583) B442583
theorem B196751 : Blo 195805 196751 := bstep (se 1 (by rfl) ⟨147563, by rfl⟩ : syracuseStep 196751 = 295127) B295127
theorem B295097 : Blo 195805 295097 := bstep (se 2 (by rfl) ⟨110661, by rfl⟩ : syracuseStep 295097 = 221323) B221323
theorem B196795 : Blo 195805 196795 := bstep (se 1 (by rfl) ⟨147596, by rfl⟩ : syracuseStep 196795 = 295193) B295193
theorem B2162933 : Blo 195805 2162933 := bstep (se 5 (by rfl) ⟨101387, by rfl⟩ : syracuseStep 2162933 = 202775) B202775
theorem B295175 : Blo 195805 295175 := bstep (se 1 (by rfl) ⟨221381, by rfl⟩ : syracuseStep 295175 = 442763) B442763
theorem B196871 : Blo 195805 196871 := bstep (se 1 (by rfl) ⟨147653, by rfl⟩ : syracuseStep 196871 = 295307) B295307
theorem B196879 : Blo 195805 196879 := bstep (se 1 (by rfl) ⟨147659, by rfl⟩ : syracuseStep 196879 = 295319) B295319
theorem B295211 : Blo 195805 295211 := bstep (se 1 (by rfl) ⟨221408, by rfl⟩ : syracuseStep 295211 = 442817) B442817
theorem B196923 : Blo 195805 196923 := bstep (se 1 (by rfl) ⟨147692, by rfl⟩ : syracuseStep 196923 = 295385) B295385
theorem B295241 : Blo 195805 295241 := bstep (se 2 (by rfl) ⟨110715, by rfl⟩ : syracuseStep 295241 = 221431) B221431
theorem B196999 : Blo 195805 196999 := bstep (se 1 (by rfl) ⟨147749, by rfl⟩ : syracuseStep 196999 = 295499) B295499
theorem B197007 : Blo 195805 197007 := bstep (se 1 (by rfl) ⟨147755, by rfl⟩ : syracuseStep 197007 = 295511) B295511
theorem B295355 : Blo 195805 295355 := bstep (se 1 (by rfl) ⟨221516, by rfl⟩ : syracuseStep 295355 = 443033) B443033
theorem B197051 : Blo 195805 197051 := bstep (se 1 (by rfl) ⟨147788, by rfl⟩ : syracuseStep 197051 = 295577) B295577
theorem B295415 : Blo 195805 295415 := bstep (se 1 (by rfl) ⟨221561, by rfl⟩ : syracuseStep 295415 = 443123) B443123
theorem B197127 : Blo 195805 197127 := bstep (se 1 (by rfl) ⟨147845, by rfl⟩ : syracuseStep 197127 = 295691) B295691
theorem B295439 : Blo 195805 295439 := bstep (se 1 (by rfl) ⟨221579, by rfl⟩ : syracuseStep 295439 = 443159) B443159
theorem B197135 : Blo 195805 197135 := bstep (se 1 (by rfl) ⟨147851, by rfl⟩ : syracuseStep 197135 = 295703) B295703
theorem B295481 : Blo 195805 295481 := bstep (se 2 (by rfl) ⟨110805, by rfl⟩ : syracuseStep 295481 = 221611) B221611
theorem B197179 : Blo 195805 197179 := bstep (se 1 (by rfl) ⟨147884, by rfl⟩ : syracuseStep 197179 = 295769) B295769
theorem B295559 : Blo 195805 295559 := bstep (se 1 (by rfl) ⟨221669, by rfl⟩ : syracuseStep 295559 = 443339) B443339
theorem B197255 : Blo 195805 197255 := bstep (se 1 (by rfl) ⟨147941, by rfl⟩ : syracuseStep 197255 = 295883) B295883
theorem B197263 : Blo 195805 197263 := bstep (se 1 (by rfl) ⟨147947, by rfl⟩ : syracuseStep 197263 = 295895) B295895
theorem B295595 : Blo 195805 295595 := bstep (se 1 (by rfl) ⟨221696, by rfl⟩ : syracuseStep 295595 = 443393) B443393
theorem B197307 : Blo 195805 197307 := bstep (se 1 (by rfl) ⟨147980, by rfl⟩ : syracuseStep 197307 = 295961) B295961
theorem B295625 : Blo 195805 295625 := bstep (se 2 (by rfl) ⟨110859, by rfl⟩ : syracuseStep 295625 = 221719) B221719
theorem B197383 : Blo 195805 197383 := bstep (se 1 (by rfl) ⟨148037, by rfl⟩ : syracuseStep 197383 = 296075) B296075
theorem B197391 : Blo 195805 197391 := bstep (se 1 (by rfl) ⟨148043, by rfl⟩ : syracuseStep 197391 = 296087) B296087
theorem B1114913 : Blo 195805 1114913 := bstep (se 2 (by rfl) ⟨418092, by rfl⟩ : syracuseStep 1114913 = 836185) B836185
theorem B557867 : Blo 195805 557867 := bstep (se 1 (by rfl) ⟨418400, by rfl⟩ : syracuseStep 557867 = 836801) B836801
theorem B295739 : Blo 195805 295739 := bstep (se 1 (by rfl) ⟨221804, by rfl⟩ : syracuseStep 295739 = 443609) B443609
theorem B197435 : Blo 195805 197435 := bstep (se 1 (by rfl) ⟨148076, by rfl⟩ : syracuseStep 197435 = 296153) B296153
theorem B295799 : Blo 195805 295799 := bstep (se 1 (by rfl) ⟨221849, by rfl⟩ : syracuseStep 295799 = 443699) B443699
theorem B197511 : Blo 195805 197511 := bstep (se 1 (by rfl) ⟨148133, by rfl⟩ : syracuseStep 197511 = 296267) B296267
theorem B295823 : Blo 195805 295823 := bstep (se 1 (by rfl) ⟨221867, by rfl⟩ : syracuseStep 295823 = 443735) B443735
theorem B197519 : Blo 195805 197519 := bstep (se 1 (by rfl) ⟨148139, by rfl⟩ : syracuseStep 197519 = 296279) B296279
theorem B295865 : Blo 195805 295865 := bstep (se 2 (by rfl) ⟨110949, by rfl⟩ : syracuseStep 295865 = 221899) B221899
theorem B197563 : Blo 195805 197563 := bstep (se 1 (by rfl) ⟨148172, by rfl⟩ : syracuseStep 197563 = 296345) B296345
theorem B295943 : Blo 195805 295943 := bstep (se 1 (by rfl) ⟨221957, by rfl⟩ : syracuseStep 295943 = 443915) B443915
theorem B197639 : Blo 195805 197639 := bstep (se 1 (by rfl) ⟨148229, by rfl⟩ : syracuseStep 197639 = 296459) B296459
theorem B197647 : Blo 195805 197647 := bstep (se 1 (by rfl) ⟨148235, by rfl⟩ : syracuseStep 197647 = 296471) B296471
theorem B295979 : Blo 195805 295979 := bstep (se 1 (by rfl) ⟨221984, by rfl⟩ : syracuseStep 295979 = 443969) B443969
theorem B197691 : Blo 195805 197691 := bstep (se 1 (by rfl) ⟨148268, by rfl⟩ : syracuseStep 197691 = 296537) B296537
theorem B296009 : Blo 195805 296009 := bstep (se 2 (by rfl) ⟨111003, by rfl⟩ : syracuseStep 296009 = 222007) B222007
theorem B197767 : Blo 195805 197767 := bstep (se 1 (by rfl) ⟨148325, by rfl⟩ : syracuseStep 197767 = 296651) B296651
theorem B197775 : Blo 195805 197775 := bstep (se 1 (by rfl) ⟨148331, by rfl⟩ : syracuseStep 197775 = 296663) B296663
theorem B296123 : Blo 195805 296123 := bstep (se 1 (by rfl) ⟨222092, by rfl⟩ : syracuseStep 296123 = 444185) B444185
theorem B197819 : Blo 195805 197819 := bstep (se 1 (by rfl) ⟨148364, by rfl⟩ : syracuseStep 197819 = 296729) B296729
theorem B296183 : Blo 195805 296183 := bstep (se 1 (by rfl) ⟨222137, by rfl⟩ : syracuseStep 296183 = 444275) B444275
theorem B197895 : Blo 195805 197895 := bstep (se 1 (by rfl) ⟨148421, by rfl⟩ : syracuseStep 197895 = 296843) B296843
theorem B296207 : Blo 195805 296207 := bstep (se 1 (by rfl) ⟨222155, by rfl⟩ : syracuseStep 296207 = 444311) B444311
theorem B197903 : Blo 195805 197903 := bstep (se 1 (by rfl) ⟨148427, by rfl⟩ : syracuseStep 197903 = 296855) B296855
theorem B296249 : Blo 195805 296249 := bstep (se 2 (by rfl) ⟨111093, by rfl⟩ : syracuseStep 296249 = 222187) B222187
theorem B197947 : Blo 195805 197947 := bstep (se 1 (by rfl) ⟨148460, by rfl⟩ : syracuseStep 197947 = 296921) B296921
theorem B2917691 : Blo 195805 2917691 := bstep (se 1 (by rfl) ⟨2188268, by rfl⟩ : syracuseStep 2917691 = 4376537) B4376537
theorem B296327 : Blo 195805 296327 := bstep (se 1 (by rfl) ⟨222245, by rfl⟩ : syracuseStep 296327 = 444491) B444491
theorem B198023 : Blo 195805 198023 := bstep (se 1 (by rfl) ⟨148517, by rfl⟩ : syracuseStep 198023 = 297035) B297035
theorem B198031 : Blo 195805 198031 := bstep (se 1 (by rfl) ⟨148523, by rfl⟩ : syracuseStep 198031 = 297047) B297047
theorem B296363 : Blo 195805 296363 := bstep (se 1 (by rfl) ⟨222272, by rfl⟩ : syracuseStep 296363 = 444545) B444545
theorem B198075 : Blo 195805 198075 := bstep (se 1 (by rfl) ⟨148556, by rfl⟩ : syracuseStep 198075 = 297113) B297113
theorem B296393 : Blo 195805 296393 := bstep (se 2 (by rfl) ⟨111147, by rfl⟩ : syracuseStep 296393 = 222295) B222295
theorem B755153 : Blo 195805 755153 := bstep (se 2 (by rfl) ⟨283182, by rfl⟩ : syracuseStep 755153 = 566365) B566365
theorem B198151 : Blo 195805 198151 := bstep (se 1 (by rfl) ⟨148613, by rfl⟩ : syracuseStep 198151 = 297227) B297227
theorem B198159 : Blo 195805 198159 := bstep (se 1 (by rfl) ⟨148619, by rfl⟩ : syracuseStep 198159 = 297239) B297239
theorem B296507 : Blo 195805 296507 := bstep (se 1 (by rfl) ⟨222380, by rfl⟩ : syracuseStep 296507 = 444761) B444761
theorem B198203 : Blo 195805 198203 := bstep (se 1 (by rfl) ⟨148652, by rfl⟩ : syracuseStep 198203 = 297305) B297305
theorem B296567 : Blo 195805 296567 := bstep (se 1 (by rfl) ⟨222425, by rfl⟩ : syracuseStep 296567 = 444851) B444851
theorem B198279 : Blo 195805 198279 := bstep (se 1 (by rfl) ⟨148709, by rfl⟩ : syracuseStep 198279 = 297419) B297419
theorem B296591 : Blo 195805 296591 := bstep (se 1 (by rfl) ⟨222443, by rfl⟩ : syracuseStep 296591 = 444887) B444887
theorem B198287 : Blo 195805 198287 := bstep (se 1 (by rfl) ⟨148715, by rfl⟩ : syracuseStep 198287 = 297431) B297431
theorem B296633 : Blo 195805 296633 := bstep (se 2 (by rfl) ⟨111237, by rfl⟩ : syracuseStep 296633 = 222475) B222475
theorem B198331 : Blo 195805 198331 := bstep (se 1 (by rfl) ⟨148748, by rfl⟩ : syracuseStep 198331 = 297497) B297497
theorem B296711 : Blo 195805 296711 := bstep (se 1 (by rfl) ⟨222533, by rfl⟩ : syracuseStep 296711 = 445067) B445067
theorem B198407 : Blo 195805 198407 := bstep (se 1 (by rfl) ⟨148805, by rfl⟩ : syracuseStep 198407 = 297611) B297611
theorem B558859 : Blo 195805 558859 := bstep (se 1 (by rfl) ⟨419144, by rfl⟩ : syracuseStep 558859 = 838289) B838289
theorem B198415 : Blo 195805 198415 := bstep (se 1 (by rfl) ⟨148811, by rfl⟩ : syracuseStep 198415 = 297623) B297623
theorem B296747 : Blo 195805 296747 := bstep (se 1 (by rfl) ⟨222560, by rfl⟩ : syracuseStep 296747 = 445121) B445121
theorem B1115963 : Blo 195805 1115963 := bstep (se 1 (by rfl) ⟨836972, by rfl⟩ : syracuseStep 1115963 = 1673945) B1673945
theorem B198459 : Blo 195805 198459 := bstep (se 1 (by rfl) ⟨148844, by rfl⟩ : syracuseStep 198459 = 297689) B297689
theorem B296777 : Blo 195805 296777 := bstep (se 2 (by rfl) ⟨111291, by rfl⟩ : syracuseStep 296777 = 222583) B222583
theorem B198535 : Blo 195805 198535 := bstep (se 1 (by rfl) ⟨148901, by rfl⟩ : syracuseStep 198535 = 297803) B297803
theorem B198543 : Blo 195805 198543 := bstep (se 1 (by rfl) ⟨148907, by rfl⟩ : syracuseStep 198543 = 297815) B297815
theorem B296891 : Blo 195805 296891 := bstep (se 1 (by rfl) ⟨222668, by rfl⟩ : syracuseStep 296891 = 445337) B445337
theorem B198587 : Blo 195805 198587 := bstep (se 1 (by rfl) ⟨148940, by rfl⟩ : syracuseStep 198587 = 297881) B297881
theorem B1607627 : Blo 195805 1607627 := bstep (se 1 (by rfl) ⟨1205720, by rfl⟩ : syracuseStep 1607627 = 2411441) B2411441
theorem B296951 : Blo 195805 296951 := bstep (se 1 (by rfl) ⟨222713, by rfl⟩ : syracuseStep 296951 = 445427) B445427
theorem B198663 : Blo 195805 198663 := bstep (se 1 (by rfl) ⟨148997, by rfl⟩ : syracuseStep 198663 = 297995) B297995
theorem B296975 : Blo 195805 296975 := bstep (se 1 (by rfl) ⟨222731, by rfl⟩ : syracuseStep 296975 = 445463) B445463
theorem B198671 : Blo 195805 198671 := bstep (se 1 (by rfl) ⟨149003, by rfl⟩ : syracuseStep 198671 = 298007) B298007
theorem B559133 : Blo 195805 559133 := bstep (se 3 (by rfl) ⟨104837, by rfl⟩ : syracuseStep 559133 = 209675) B209675
theorem B297017 : Blo 195805 297017 := bstep (se 2 (by rfl) ⟨111381, by rfl⟩ : syracuseStep 297017 = 222763) B222763
theorem B198715 : Blo 195805 198715 := bstep (se 1 (by rfl) ⟨149036, by rfl⟩ : syracuseStep 198715 = 298073) B298073
theorem B297095 : Blo 195805 297095 := bstep (se 1 (by rfl) ⟨222821, by rfl⟩ : syracuseStep 297095 = 445643) B445643
theorem B198791 : Blo 195805 198791 := bstep (se 1 (by rfl) ⟨149093, by rfl⟩ : syracuseStep 198791 = 298187) B298187
theorem B198799 : Blo 195805 198799 := bstep (se 1 (by rfl) ⟨149099, by rfl⟩ : syracuseStep 198799 = 298199) B298199
theorem B297131 : Blo 195805 297131 := bstep (se 1 (by rfl) ⟨222848, by rfl⟩ : syracuseStep 297131 = 445697) B445697
theorem B198843 : Blo 195805 198843 := bstep (se 1 (by rfl) ⟨149132, by rfl⟩ : syracuseStep 198843 = 298265) B298265
theorem B297161 : Blo 195805 297161 := bstep (se 2 (by rfl) ⟨111435, by rfl⟩ : syracuseStep 297161 = 222871) B222871
theorem B198919 : Blo 195805 198919 := bstep (se 1 (by rfl) ⟨149189, by rfl⟩ : syracuseStep 198919 = 298379) B298379
theorem B198927 : Blo 195805 198927 := bstep (se 1 (by rfl) ⟨149195, by rfl⟩ : syracuseStep 198927 = 298391) B298391
theorem B461099 : Blo 195805 461099 := bstep (se 1 (by rfl) ⟨345824, by rfl⟩ : syracuseStep 461099 = 691649) B691649
theorem B297275 : Blo 195805 297275 := bstep (se 1 (by rfl) ⟨222956, by rfl⟩ : syracuseStep 297275 = 445913) B445913
theorem B198971 : Blo 195805 198971 := bstep (se 1 (by rfl) ⟨149228, by rfl⟩ : syracuseStep 198971 = 298457) B298457
theorem B5114177 : Blo 195805 5114177 := bstep (se 2 (by rfl) ⟨1917816, by rfl⟩ : syracuseStep 5114177 = 3835633) B3835633
theorem B297335 : Blo 195805 297335 := bstep (se 1 (by rfl) ⟨223001, by rfl⟩ : syracuseStep 297335 = 446003) B446003
theorem B199047 : Blo 195805 199047 := bstep (se 1 (by rfl) ⟨149285, by rfl⟩ : syracuseStep 199047 = 298571) B298571
theorem B297359 : Blo 195805 297359 := bstep (se 1 (by rfl) ⟨223019, by rfl⟩ : syracuseStep 297359 = 446039) B446039
theorem B199055 : Blo 195805 199055 := bstep (se 1 (by rfl) ⟨149291, by rfl⟩ : syracuseStep 199055 = 298583) B298583
theorem B297401 : Blo 195805 297401 := bstep (se 2 (by rfl) ⟨111525, by rfl⟩ : syracuseStep 297401 = 223051) B223051
theorem B199099 : Blo 195805 199099 := bstep (se 1 (by rfl) ⟨149324, by rfl⟩ : syracuseStep 199099 = 298649) B298649
theorem B297479 : Blo 195805 297479 := bstep (se 1 (by rfl) ⟨223109, by rfl⟩ : syracuseStep 297479 = 446219) B446219
theorem B199175 : Blo 195805 199175 := bstep (se 1 (by rfl) ⟨149381, by rfl⟩ : syracuseStep 199175 = 298763) B298763
theorem B199183 : Blo 195805 199183 := bstep (se 1 (by rfl) ⟨149387, by rfl⟩ : syracuseStep 199183 = 298775) B298775
theorem B297515 : Blo 195805 297515 := bstep (se 1 (by rfl) ⟨223136, by rfl⟩ : syracuseStep 297515 = 446273) B446273
theorem B199227 : Blo 195805 199227 := bstep (se 1 (by rfl) ⟨149420, by rfl⟩ : syracuseStep 199227 = 298841) B298841
theorem B297545 : Blo 195805 297545 := bstep (se 2 (by rfl) ⟨111579, by rfl⟩ : syracuseStep 297545 = 223159) B223159
theorem B199303 : Blo 195805 199303 := bstep (se 1 (by rfl) ⟨149477, by rfl⟩ : syracuseStep 199303 = 298955) B298955
theorem B199311 : Blo 195805 199311 := bstep (se 1 (by rfl) ⟨149483, by rfl⟩ : syracuseStep 199311 = 298967) B298967
theorem B297659 : Blo 195805 297659 := bstep (se 1 (by rfl) ⟨223244, by rfl⟩ : syracuseStep 297659 = 446489) B446489
theorem B199355 : Blo 195805 199355 := bstep (se 1 (by rfl) ⟨149516, by rfl⟩ : syracuseStep 199355 = 299033) B299033
theorem B297719 : Blo 195805 297719 := bstep (se 1 (by rfl) ⟨223289, by rfl⟩ : syracuseStep 297719 = 446579) B446579
theorem B6195973 : Blo 195805 6195973 := bstep (se 4 (by rfl) ⟨580872, by rfl⟩ : syracuseStep 6195973 = 1161745) B1161745
theorem B199431 : Blo 195805 199431 := bstep (se 1 (by rfl) ⟨149573, by rfl⟩ : syracuseStep 199431 = 299147) B299147
theorem B297743 : Blo 195805 297743 := bstep (se 1 (by rfl) ⟨223307, by rfl⟩ : syracuseStep 297743 = 446615) B446615
theorem B1018639 : Blo 195805 1018639 := bstep (se 1 (by rfl) ⟨763979, by rfl⟩ : syracuseStep 1018639 = 1527959) B1527959
theorem B199439 : Blo 195805 199439 := bstep (se 1 (by rfl) ⟨149579, by rfl⟩ : syracuseStep 199439 = 299159) B299159
theorem B1903409 : Blo 195805 1903409 := bstep (se 2 (by rfl) ⟨713778, by rfl⟩ : syracuseStep 1903409 = 1427557) B1427557
theorem B297785 : Blo 195805 297785 := bstep (se 2 (by rfl) ⟨111669, by rfl⟩ : syracuseStep 297785 = 223339) B223339
theorem B199483 : Blo 195805 199483 := bstep (se 1 (by rfl) ⟨149612, by rfl⟩ : syracuseStep 199483 = 299225) B299225
theorem B297863 : Blo 195805 297863 := bstep (se 1 (by rfl) ⟨223397, by rfl⟩ : syracuseStep 297863 = 446795) B446795
theorem B199559 : Blo 195805 199559 := bstep (se 1 (by rfl) ⟨149669, by rfl⟩ : syracuseStep 199559 = 299339) B299339
theorem B199567 : Blo 195805 199567 := bstep (se 1 (by rfl) ⟨149675, by rfl⟩ : syracuseStep 199567 = 299351) B299351
theorem B1084313 : Blo 195805 1084313 := bstep (se 2 (by rfl) ⟨406617, by rfl⟩ : syracuseStep 1084313 = 813235) B813235
theorem B297899 : Blo 195805 297899 := bstep (se 1 (by rfl) ⟨223424, by rfl⟩ : syracuseStep 297899 = 446849) B446849
theorem B199611 : Blo 195805 199611 := bstep (se 1 (by rfl) ⟨149708, by rfl⟩ : syracuseStep 199611 = 299417) B299417
theorem B297929 : Blo 195805 297929 := bstep (se 2 (by rfl) ⟨111723, by rfl⟩ : syracuseStep 297929 = 223447) B223447
theorem B199687 : Blo 195805 199687 := bstep (se 1 (by rfl) ⟨149765, by rfl⟩ : syracuseStep 199687 = 299531) B299531
theorem B199695 : Blo 195805 199695 := bstep (se 1 (by rfl) ⟨149771, by rfl⟩ : syracuseStep 199695 = 299543) B299543
theorem B298043 : Blo 195805 298043 := bstep (se 1 (by rfl) ⟨223532, by rfl⟩ : syracuseStep 298043 = 447065) B447065
theorem B199739 : Blo 195805 199739 := bstep (se 1 (by rfl) ⟨149804, by rfl⟩ : syracuseStep 199739 = 299609) B299609
theorem B1510487 : Blo 195805 1510487 := bstep (se 1 (by rfl) ⟨1132865, by rfl⟩ : syracuseStep 1510487 = 2265731) B2265731
theorem B756823 : Blo 195805 756823 := bstep (se 1 (by rfl) ⟨567617, by rfl⟩ : syracuseStep 756823 = 1135235) B1135235
theorem B330871 : Blo 195805 330871 := bstep (se 1 (by rfl) ⟨248153, by rfl⟩ : syracuseStep 330871 = 496307) B496307
theorem B298103 : Blo 195805 298103 := bstep (se 1 (by rfl) ⟨223577, by rfl⟩ : syracuseStep 298103 = 447155) B447155
theorem B298127 : Blo 195805 298127 := bstep (se 1 (by rfl) ⟨223595, by rfl⟩ : syracuseStep 298127 = 447191) B447191
theorem B298169 : Blo 195805 298169 := bstep (se 2 (by rfl) ⟨111813, by rfl⟩ : syracuseStep 298169 = 223627) B223627
theorem B1117421 : Blo 195805 1117421 := bstep (se 3 (by rfl) ⟨209516, by rfl⟩ : syracuseStep 1117421 = 419033) B419033
theorem B298247 : Blo 195805 298247 := bstep (se 1 (by rfl) ⟨223685, by rfl⟩ : syracuseStep 298247 = 447371) B447371
theorem B298283 : Blo 195805 298283 := bstep (se 1 (by rfl) ⟨223712, by rfl⟩ : syracuseStep 298283 = 447425) B447425
theorem B331067 : Blo 195805 331067 := bstep (se 1 (by rfl) ⟨248300, by rfl⟩ : syracuseStep 331067 = 496601) B496601
theorem B298313 : Blo 195805 298313 := bstep (se 2 (by rfl) ⟨111867, by rfl⟩ : syracuseStep 298313 = 223735) B223735
theorem B757127 : Blo 195805 757127 := bstep (se 1 (by rfl) ⟨567845, by rfl⟩ : syracuseStep 757127 = 1135691) B1135691
theorem B298427 : Blo 195805 298427 := bstep (se 1 (by rfl) ⟨223820, by rfl⟩ : syracuseStep 298427 = 447641) B447641
theorem B298487 : Blo 195805 298487 := bstep (se 1 (by rfl) ⟨223865, by rfl⟩ : syracuseStep 298487 = 447731) B447731
theorem B298511 : Blo 195805 298511 := bstep (se 1 (by rfl) ⟨223883, by rfl⟩ : syracuseStep 298511 = 447767) B447767
theorem B1117739 : Blo 195805 1117739 := bstep (se 1 (by rfl) ⟨838304, by rfl⟩ : syracuseStep 1117739 = 1676609) B1676609
theorem B298553 : Blo 195805 298553 := bstep (se 2 (by rfl) ⟨111957, by rfl⟩ : syracuseStep 298553 = 223915) B223915
theorem B757309 : Blo 195805 757309 := bstep (se 3 (by rfl) ⟨141995, by rfl⟩ : syracuseStep 757309 = 283991) B283991
theorem B298631 : Blo 195805 298631 := bstep (se 1 (by rfl) ⟨223973, by rfl⟩ : syracuseStep 298631 = 447947) B447947
theorem B298667 : Blo 195805 298667 := bstep (se 1 (by rfl) ⟨224000, by rfl⟩ : syracuseStep 298667 = 448001) B448001
theorem B331465 : Blo 195805 331465 := bstep (se 2 (by rfl) ⟨124299, by rfl⟩ : syracuseStep 331465 = 248599) B248599
theorem B298697 : Blo 195805 298697 := bstep (se 2 (by rfl) ⟨112011, by rfl⟩ : syracuseStep 298697 = 224023) B224023
theorem B855841 : Blo 195805 855841 := bstep (se 2 (by rfl) ⟨320940, by rfl⟩ : syracuseStep 855841 = 641881) B641881
theorem B298811 : Blo 195805 298811 := bstep (se 1 (by rfl) ⟨224108, by rfl⟩ : syracuseStep 298811 = 448217) B448217
theorem B298871 : Blo 195805 298871 := bstep (se 1 (by rfl) ⟨224153, by rfl⟩ : syracuseStep 298871 = 448307) B448307
theorem B298895 : Blo 195805 298895 := bstep (se 1 (by rfl) ⟨224171, by rfl⟩ : syracuseStep 298895 = 448343) B448343
theorem B298937 : Blo 195805 298937 := bstep (se 2 (by rfl) ⟨112101, by rfl⟩ : syracuseStep 298937 = 224203) B224203
theorem B299015 : Blo 195805 299015 := bstep (se 1 (by rfl) ⟨224261, by rfl⟩ : syracuseStep 299015 = 448523) B448523
theorem B495659 : Blo 195805 495659 := bstep (se 1 (by rfl) ⟨371744, by rfl⟩ : syracuseStep 495659 = 743489) B743489
theorem B299051 : Blo 195805 299051 := bstep (se 1 (by rfl) ⟨224288, by rfl⟩ : syracuseStep 299051 = 448577) B448577
theorem B299081 : Blo 195805 299081 := bstep (se 2 (by rfl) ⟨112155, by rfl⟩ : syracuseStep 299081 = 224311) B224311
theorem B561239 : Blo 195805 561239 := bstep (se 1 (by rfl) ⟨420929, by rfl⟩ : syracuseStep 561239 = 841859) B841859
theorem B1020077 : Blo 195805 1020077 := bstep (se 3 (by rfl) ⟨191264, by rfl⟩ : syracuseStep 1020077 = 382529) B382529
theorem B299195 : Blo 195805 299195 := bstep (se 1 (by rfl) ⟨224396, by rfl⟩ : syracuseStep 299195 = 448793) B448793
theorem B299255 : Blo 195805 299255 := bstep (se 1 (by rfl) ⟨224441, by rfl⟩ : syracuseStep 299255 = 448883) B448883
theorem B3870989 : Blo 195805 3870989 := bstep (se 3 (by rfl) ⟨725810, by rfl⟩ : syracuseStep 3870989 = 1451621) B1451621
theorem B299279 : Blo 195805 299279 := bstep (se 1 (by rfl) ⟨224459, by rfl⟩ : syracuseStep 299279 = 448919) B448919
theorem B299321 : Blo 195805 299321 := bstep (se 2 (by rfl) ⟨112245, by rfl⟩ : syracuseStep 299321 = 224491) B224491
theorem B561467 : Blo 195805 561467 := bstep (se 1 (by rfl) ⟨421100, by rfl⟩ : syracuseStep 561467 = 842201) B842201
theorem B332167 : Blo 195805 332167 := bstep (se 1 (by rfl) ⟨249125, by rfl⟩ : syracuseStep 332167 = 498251) B498251
theorem B299399 : Blo 195805 299399 := bstep (se 1 (by rfl) ⟨224549, by rfl⟩ : syracuseStep 299399 = 449099) B449099
theorem B299435 : Blo 195805 299435 := bstep (se 1 (by rfl) ⟨224576, by rfl⟩ : syracuseStep 299435 = 449153) B449153
theorem B561593 : Blo 195805 561593 := bstep (se 2 (by rfl) ⟨210597, by rfl⟩ : syracuseStep 561593 = 421195) B421195
theorem B299465 : Blo 195805 299465 := bstep (se 2 (by rfl) ⟨112299, by rfl⟩ : syracuseStep 299465 = 224599) B224599
theorem B299579 : Blo 195805 299579 := bstep (se 1 (by rfl) ⟨224684, by rfl⟩ : syracuseStep 299579 = 449369) B449369
theorem B299639 : Blo 195805 299639 := bstep (se 1 (by rfl) ⟨224729, by rfl⟩ : syracuseStep 299639 = 449459) B449459
theorem B299663 : Blo 195805 299663 := bstep (se 1 (by rfl) ⟨224747, by rfl⟩ : syracuseStep 299663 = 449495) B449495
theorem B299705 : Blo 195805 299705 := bstep (se 2 (by rfl) ⟨112389, by rfl⟩ : syracuseStep 299705 = 224779) B224779
theorem B267143 : Blo 195805 267143 := bstep (se 1 (by rfl) ⟨200357, by rfl⟩ : syracuseStep 267143 = 400715) B400715
theorem B1119197 : Blo 195805 1119197 := bstep (se 3 (by rfl) ⟨209849, by rfl⟩ : syracuseStep 1119197 = 419699) B419699
theorem B496651 : Blo 195805 496651 := bstep (se 1 (by rfl) ⟨372488, by rfl⟩ : syracuseStep 496651 = 744977) B744977
theorem B332815 : Blo 195805 332815 := bstep (se 1 (by rfl) ⟨249611, by rfl⟩ : syracuseStep 332815 = 499223) B499223
theorem B955435 : Blo 195805 955435 := bstep (se 1 (by rfl) ⟨716576, by rfl⟩ : syracuseStep 955435 = 1433153) B1433153
theorem B496793 : Blo 195805 496793 := bstep (se 2 (by rfl) ⟨186297, by rfl⟩ : syracuseStep 496793 = 372595) B372595
theorem B496955 : Blo 195805 496955 := bstep (se 1 (by rfl) ⟨372716, by rfl⟩ : syracuseStep 496955 = 745433) B745433
theorem B4560229 : Blo 195805 4560229 := bstep (se 4 (by rfl) ⟨427521, by rfl⟩ : syracuseStep 4560229 = 855043) B855043
theorem B660851 : Blo 195805 660851 := bstep (se 1 (by rfl) ⟨495638, by rfl⟩ : syracuseStep 660851 = 991277) B991277
theorem B333355 : Blo 195805 333355 := bstep (se 1 (by rfl) ⟨250016, by rfl⟩ : syracuseStep 333355 = 500033) B500033
theorem B497299 : Blo 195805 497299 := bstep (se 1 (by rfl) ⟨372974, by rfl⟩ : syracuseStep 497299 = 745949) B745949
theorem B333497 : Blo 195805 333497 := bstep (se 2 (by rfl) ⟨125061, by rfl⟩ : syracuseStep 333497 = 250123) B250123
theorem B1218277 : Blo 195805 1218277 := bstep (se 4 (by rfl) ⟨114213, by rfl⟩ : syracuseStep 1218277 = 228427) B228427
theorem B497441 : Blo 195805 497441 := bstep (se 2 (by rfl) ⟨186540, by rfl⟩ : syracuseStep 497441 = 373081) B373081
theorem B1611683 : Blo 195805 1611683 := bstep (se 1 (by rfl) ⟨1208762, by rfl⟩ : syracuseStep 1611683 = 2417525) B2417525
theorem B563233 : Blo 195805 563233 := bstep (se 2 (by rfl) ⟨211212, by rfl⟩ : syracuseStep 563233 = 422425) B422425
theorem B235639 : Blo 195805 235639 := bstep (se 1 (by rfl) ⟨176729, by rfl⟩ : syracuseStep 235639 = 353459) B353459
theorem B956609 : Blo 195805 956609 := bstep (se 2 (by rfl) ⟨358728, by rfl⟩ : syracuseStep 956609 = 717457) B717457
theorem B8591629 : Blo 195805 8591629 := bstep (se 3 (by rfl) ⟨1610930, by rfl⟩ : syracuseStep 8591629 = 3221861) B3221861
theorem B2529629 : Blo 195805 2529629 := bstep (se 3 (by rfl) ⟨474305, by rfl⟩ : syracuseStep 2529629 = 948611) B948611
theorem B334199 : Blo 195805 334199 := bstep (se 1 (by rfl) ⟨250649, by rfl⟩ : syracuseStep 334199 = 501299) B501299
theorem B563723 : Blo 195805 563723 := bstep (se 1 (by rfl) ⟨422792, by rfl⟩ : syracuseStep 563723 = 845585) B845585
theorem B498433 : Blo 195805 498433 := bstep (se 2 (by rfl) ⟨186912, by rfl⟩ : syracuseStep 498433 = 373825) B373825
theorem B334651 : Blo 195805 334651 := bstep (se 1 (by rfl) ⟨250988, by rfl⟩ : syracuseStep 334651 = 501977) B501977
theorem B629651 : Blo 195805 629651 := bstep (se 1 (by rfl) ⟨472238, by rfl⟩ : syracuseStep 629651 = 944477) B944477
theorem B334793 : Blo 195805 334793 := bstep (se 2 (by rfl) ⟨125547, by rfl⟩ : syracuseStep 334793 = 251095) B251095
theorem B564509 : Blo 195805 564509 := bstep (se 3 (by rfl) ⟨105845, by rfl⟩ : syracuseStep 564509 = 211691) B211691
theorem B499031 : Blo 195805 499031 := bstep (se 1 (by rfl) ⟨374273, by rfl⟩ : syracuseStep 499031 = 748547) B748547
theorem B1121795 : Blo 195805 1121795 := bstep (se 1 (by rfl) ⟨841346, by rfl⟩ : syracuseStep 1121795 = 1682693) B1682693
theorem B499243 : Blo 195805 499243 := bstep (se 1 (by rfl) ⟨374432, by rfl⟩ : syracuseStep 499243 = 748865) B748865
theorem B237115 : Blo 195805 237115 := bstep (se 1 (by rfl) ⟨177836, by rfl⟩ : syracuseStep 237115 = 355673) B355673
theorem B302665 : Blo 195805 302665 := bstep (se 2 (by rfl) ⟨113499, by rfl⟩ : syracuseStep 302665 = 226999) B226999
theorem B335495 : Blo 195805 335495 := bstep (se 1 (by rfl) ⟨251621, by rfl⟩ : syracuseStep 335495 = 503243) B503243
theorem B499385 : Blo 195805 499385 := bstep (se 2 (by rfl) ⟨187269, by rfl⟩ : syracuseStep 499385 = 374539) B374539
theorem B663443 : Blo 195805 663443 := bstep (se 1 (by rfl) ⟨497582, by rfl⟩ : syracuseStep 663443 = 995165) B995165
theorem B336143 : Blo 195805 336143 := bstep (se 1 (by rfl) ⟨252107, by rfl⟩ : syracuseStep 336143 = 504215) B504215
theorem B1810835 : Blo 195805 1810835 := bstep (se 1 (by rfl) ⟨1358126, by rfl⟩ : syracuseStep 1810835 = 2716253) B2716253
theorem B795203 : Blo 195805 795203 := bstep (se 1 (by rfl) ⟨596402, by rfl⟩ : syracuseStep 795203 = 1192805) B1192805
theorem B500377 : Blo 195805 500377 := bstep (se 2 (by rfl) ⟨187641, by rfl⟩ : syracuseStep 500377 = 375283) B375283
theorem B336683 : Blo 195805 336683 := bstep (se 1 (by rfl) ⟨252512, by rfl⟩ : syracuseStep 336683 = 505025) B505025
theorem B500539 : Blo 195805 500539 := bstep (se 1 (by rfl) ⟨375404, by rfl⟩ : syracuseStep 500539 = 750809) B750809
theorem B598871 : Blo 195805 598871 := bstep (se 1 (by rfl) ⟨449153, by rfl⟩ : syracuseStep 598871 = 898307) B898307
theorem B2270105 : Blo 195805 2270105 := bstep (se 2 (by rfl) ⟨851289, by rfl⟩ : syracuseStep 2270105 = 1702579) B1702579
theorem B500681 : Blo 195805 500681 := bstep (se 2 (by rfl) ⟨187755, by rfl⟩ : syracuseStep 500681 = 375511) B375511
theorem B1287191 : Blo 195805 1287191 := bstep (se 1 (by rfl) ⟨965393, by rfl⟩ : syracuseStep 1287191 = 1930787) B1930787
theorem B337081 : Blo 195805 337081 := bstep (se 2 (by rfl) ⟨126405, by rfl⟩ : syracuseStep 337081 = 252811) B252811
theorem B632009 : Blo 195805 632009 := bstep (se 2 (by rfl) ⟨237003, by rfl⟩ : syracuseStep 632009 = 474007) B474007
theorem B664847 : Blo 195805 664847 := bstep (se 1 (by rfl) ⟨498635, by rfl⟩ : syracuseStep 664847 = 997271) B997271
theorem B501025 : Blo 195805 501025 := bstep (se 2 (by rfl) ⟨187884, by rfl⟩ : syracuseStep 501025 = 375769) B375769
theorem B238907 : Blo 195805 238907 := bstep (se 1 (by rfl) ⟨179180, by rfl⟩ : syracuseStep 238907 = 358361) B358361
theorem B566615 : Blo 195805 566615 := bstep (se 1 (by rfl) ⟨424961, by rfl⟩ : syracuseStep 566615 = 849923) B849923
theorem B1254791 : Blo 195805 1254791 := bstep (se 1 (by rfl) ⟨941093, by rfl⟩ : syracuseStep 1254791 = 1882187) B1882187
theorem B665117 : Blo 195805 665117 := bstep (se 3 (by rfl) ⟨124709, by rfl⟩ : syracuseStep 665117 = 249419) B249419
theorem B1418795 : Blo 195805 1418795 := bstep (se 1 (by rfl) ⟨1064096, by rfl⟩ : syracuseStep 1418795 = 2128193) B2128193
theorem B2238029 : Blo 195805 2238029 := bstep (se 3 (by rfl) ⟨419630, by rfl⟩ : syracuseStep 2238029 = 839261) B839261
theorem B567073 : Blo 195805 567073 := bstep (se 2 (by rfl) ⟨212652, by rfl⟩ : syracuseStep 567073 = 425305) B425305
theorem B3811121 : Blo 195805 3811121 := bstep (se 2 (by rfl) ⟨1429170, by rfl⟩ : syracuseStep 3811121 = 2858341) B2858341
theorem B501623 : Blo 195805 501623 := bstep (se 1 (by rfl) ⟨376217, by rfl⟩ : syracuseStep 501623 = 752435) B752435
theorem B567481 : Blo 195805 567481 := bstep (se 2 (by rfl) ⟨212805, by rfl⟩ : syracuseStep 567481 = 425611) B425611
theorem B567595 : Blo 195805 567595 := bstep (se 1 (by rfl) ⟨425696, by rfl⟩ : syracuseStep 567595 = 851393) B851393
theorem B567823 : Blo 195805 567823 := bstep (se 1 (by rfl) ⟨425867, by rfl⟩ : syracuseStep 567823 = 851735) B851735
theorem B568097 : Blo 195805 568097 := bstep (se 2 (by rfl) ⟨213036, by rfl⟩ : syracuseStep 568097 = 426073) B426073
theorem B994193 : Blo 195805 994193 := bstep (se 2 (by rfl) ⟨372822, by rfl⟩ : syracuseStep 994193 = 745645) B745645
theorem B666521 : Blo 195805 666521 := bstep (se 2 (by rfl) ⟨249945, by rfl⟩ : syracuseStep 666521 = 499891) B499891
theorem B502919 : Blo 195805 502919 := bstep (se 1 (by rfl) ⟨377189, by rfl⟩ : syracuseStep 502919 = 754379) B754379
theorem B502969 : Blo 195805 502969 := bstep (se 2 (by rfl) ⟨188613, by rfl⟩ : syracuseStep 502969 = 377227) B377227
theorem B568711 : Blo 195805 568711 := bstep (se 1 (by rfl) ⟨426533, by rfl⟩ : syracuseStep 568711 = 853067) B853067
theorem B503225 : Blo 195805 503225 := bstep (se 2 (by rfl) ⟨188709, by rfl⟩ : syracuseStep 503225 = 377419) B377419
theorem B798137 : Blo 195805 798137 := bstep (se 2 (by rfl) ⟨299301, by rfl⟩ : syracuseStep 798137 = 598603) B598603
theorem B1420753 : Blo 195805 1420753 := bstep (se 2 (by rfl) ⟨532782, by rfl⟩ : syracuseStep 1420753 = 1065565) B1065565
theorem B470539 : Blo 195805 470539 := bstep (se 1 (by rfl) ⟨352904, by rfl⟩ : syracuseStep 470539 = 705809) B705809
theorem B470615 : Blo 195805 470615 := bstep (se 1 (by rfl) ⟨352961, by rfl⟩ : syracuseStep 470615 = 705923) B705923
theorem B667223 : Blo 195805 667223 := bstep (se 1 (by rfl) ⟨500417, by rfl⟩ : syracuseStep 667223 = 1000835) B1000835
theorem B634625 : Blo 195805 634625 := bstep (se 2 (by rfl) ⟨237984, by rfl⟩ : syracuseStep 634625 = 475969) B475969
theorem B503567 : Blo 195805 503567 := bstep (se 1 (by rfl) ⟨377675, by rfl⟩ : syracuseStep 503567 = 755351) B755351
theorem B569359 : Blo 195805 569359 := bstep (se 1 (by rfl) ⟨427019, by rfl⟩ : syracuseStep 569359 = 854039) B854039
theorem B667709 : Blo 195805 667709 := bstep (se 3 (by rfl) ⟨125195, by rfl⟩ : syracuseStep 667709 = 250391) B250391
theorem B1126487 : Blo 195805 1126487 := bstep (se 1 (by rfl) ⟨844865, by rfl⟩ : syracuseStep 1126487 = 1689731) B1689731
theorem B372937 : Blo 195805 372937 := bstep (se 2 (by rfl) ⟨139851, by rfl⟩ : syracuseStep 372937 = 279703) B279703
theorem B504265 : Blo 195805 504265 := bstep (se 2 (by rfl) ⟨189099, by rfl⟩ : syracuseStep 504265 = 378199) B378199
theorem B504407 : Blo 195805 504407 := bstep (se 1 (by rfl) ⟨378305, by rfl⟩ : syracuseStep 504407 = 756611) B756611
theorem B4207285 : Blo 195805 4207285 := bstep (se 5 (by rfl) ⟨197216, by rfl⟩ : syracuseStep 4207285 = 394433) B394433
theorem B996299 : Blo 195805 996299 := bstep (se 1 (by rfl) ⟨747224, by rfl⟩ : syracuseStep 996299 = 1494449) B1494449
theorem B1913867 : Blo 195805 1913867 := bstep (se 1 (by rfl) ⟨1435400, by rfl⟩ : syracuseStep 1913867 = 2870801) B2870801
theorem B209935 : Blo 195805 209935 := bstep (se 1 (by rfl) ⟨157451, by rfl⟩ : syracuseStep 209935 = 314903) B314903
theorem B603251 : Blo 195805 603251 := bstep (se 1 (by rfl) ⟨452438, by rfl⟩ : syracuseStep 603251 = 904877) B904877
theorem B996623 : Blo 195805 996623 := bstep (se 1 (by rfl) ⟨747467, by rfl⟩ : syracuseStep 996623 = 1494935) B1494935
theorem B669113 : Blo 195805 669113 := bstep (se 2 (by rfl) ⟨250917, by rfl⟩ : syracuseStep 669113 = 501835) B501835
theorem B3782213 : Blo 195805 3782213 := bstep (se 4 (by rfl) ⟨354582, by rfl⟩ : syracuseStep 3782213 = 709165) B709165
theorem B1128401 : Blo 195805 1128401 := bstep (se 2 (by rfl) ⟨423150, by rfl⟩ : syracuseStep 1128401 = 846301) B846301
theorem B669707 : Blo 195805 669707 := bstep (se 1 (by rfl) ⟨502280, by rfl⟩ : syracuseStep 669707 = 1004561) B1004561
theorem B374843 : Blo 195805 374843 := bstep (se 1 (by rfl) ⟨281132, by rfl⟩ : syracuseStep 374843 = 562265) B562265
theorem B669815 : Blo 195805 669815 := bstep (se 1 (by rfl) ⟨502361, by rfl⟩ : syracuseStep 669815 = 1004723) B1004723
theorem B1620101 : Blo 195805 1620101 := bstep (se 4 (by rfl) ⟨151884, by rfl⟩ : syracuseStep 1620101 = 303769) B303769
theorem B604417 : Blo 195805 604417 := bstep (se 2 (by rfl) ⟨226656, by rfl⟩ : syracuseStep 604417 = 453313) B453313
theorem B440711 : Blo 195805 440711 := bstep (se 1 (by rfl) ⟨330533, by rfl⟩ : syracuseStep 440711 = 661067) B661067
theorem B375329 : Blo 195805 375329 := bstep (se 2 (by rfl) ⟨140748, by rfl⟩ : syracuseStep 375329 = 281497) B281497
theorem B440891 : Blo 195805 440891 := bstep (se 1 (by rfl) ⟨330668, by rfl⟩ : syracuseStep 440891 = 661337) B661337
theorem B441017 : Blo 195805 441017 := bstep (se 2 (by rfl) ⟨165381, by rfl⟩ : syracuseStep 441017 = 330763) B330763
theorem B998081 : Blo 195805 998081 := bstep (se 2 (by rfl) ⟨374280, by rfl⟩ : syracuseStep 998081 = 748561) B748561
theorem B670409 : Blo 195805 670409 := bstep (se 2 (by rfl) ⟨251403, by rfl⟩ : syracuseStep 670409 = 502807) B502807
theorem B375671 : Blo 195805 375671 := bstep (se 1 (by rfl) ⟨281753, by rfl⟩ : syracuseStep 375671 = 563507) B563507
theorem B441359 : Blo 195805 441359 := bstep (se 1 (by rfl) ⟨331019, by rfl⟩ : syracuseStep 441359 = 662039) B662039
theorem B441377 : Blo 195805 441377 := bstep (se 2 (by rfl) ⟨165516, by rfl⟩ : syracuseStep 441377 = 331033) B331033
theorem B1424557 : Blo 195805 1424557 := bstep (se 3 (by rfl) ⟨267104, by rfl⟩ : syracuseStep 1424557 = 534209) B534209
theorem B441719 : Blo 195805 441719 := bstep (se 1 (by rfl) ⟨331289, by rfl⟩ : syracuseStep 441719 = 662579) B662579
theorem B671111 : Blo 195805 671111 := bstep (se 1 (by rfl) ⟨503333, by rfl⟩ : syracuseStep 671111 = 1006667) B1006667
theorem B441899 : Blo 195805 441899 := bstep (se 1 (by rfl) ⟨331424, by rfl⟩ : syracuseStep 441899 = 662849) B662849
theorem B671489 : Blo 195805 671489 := bstep (se 2 (by rfl) ⟨251808, by rfl⟩ : syracuseStep 671489 = 503617) B503617
theorem B442259 : Blo 195805 442259 := bstep (se 1 (by rfl) ⟨331694, by rfl⟩ : syracuseStep 442259 = 663389) B663389
theorem B638867 : Blo 195805 638867 := bstep (se 1 (by rfl) ⟨479150, by rfl⟩ : syracuseStep 638867 = 958301) B958301
theorem B442313 : Blo 195805 442313 := bstep (se 2 (by rfl) ⟨165867, by rfl⟩ : syracuseStep 442313 = 331735) B331735
theorem B999377 : Blo 195805 999377 := bstep (se 2 (by rfl) ⟨374766, by rfl⟩ : syracuseStep 999377 = 749533) B749533
theorem B606241 : Blo 195805 606241 := bstep (se 2 (by rfl) ⟨227340, by rfl⟩ : syracuseStep 606241 = 454681) B454681
theorem B901187 : Blo 195805 901187 := bstep (se 1 (by rfl) ⟨675890, by rfl⟩ : syracuseStep 901187 = 1351781) B1351781
theorem B1065305 : Blo 195805 1065305 := bstep (se 2 (by rfl) ⟨399489, by rfl⟩ : syracuseStep 1065305 = 798979) B798979
theorem B377273 : Blo 195805 377273 := bstep (se 2 (by rfl) ⟨141477, by rfl⟩ : syracuseStep 377273 = 282955) B282955
theorem B672299 : Blo 195805 672299 := bstep (se 1 (by rfl) ⟨504224, by rfl⟩ : syracuseStep 672299 = 1008449) B1008449
theorem B1491533 : Blo 195805 1491533 := bstep (se 3 (by rfl) ⟨279662, by rfl⟩ : syracuseStep 1491533 = 559325) B559325
theorem B443015 : Blo 195805 443015 := bstep (se 1 (by rfl) ⟨332261, by rfl⟩ : syracuseStep 443015 = 664523) B664523
theorem B377615 : Blo 195805 377615 := bstep (se 1 (by rfl) ⟨283211, by rfl⟩ : syracuseStep 377615 = 566423) B566423
theorem B607019 : Blo 195805 607019 := bstep (se 1 (by rfl) ⟨455264, by rfl⟩ : syracuseStep 607019 = 910529) B910529
theorem B443195 : Blo 195805 443195 := bstep (se 1 (by rfl) ⟨332396, by rfl⟩ : syracuseStep 443195 = 664793) B664793
theorem B443321 : Blo 195805 443321 := bstep (se 2 (by rfl) ⟨166245, by rfl⟩ : syracuseStep 443321 = 332491) B332491
theorem B443663 : Blo 195805 443663 := bstep (se 1 (by rfl) ⟨332747, by rfl⟩ : syracuseStep 443663 = 665495) B665495
theorem B443681 : Blo 195805 443681 := bstep (se 2 (by rfl) ⟨166380, by rfl⟩ : syracuseStep 443681 = 332761) B332761
theorem B476459 : Blo 195805 476459 := bstep (se 1 (by rfl) ⟨357344, by rfl⟩ : syracuseStep 476459 = 714689) B714689
theorem B1590749 : Blo 195805 1590749 := bstep (se 3 (by rfl) ⟨298265, by rfl⟩ : syracuseStep 1590749 = 596531) B596531
theorem B2835971 : Blo 195805 2835971 := bstep (se 1 (by rfl) ⟨2126978, by rfl⟩ : syracuseStep 2835971 = 4253957) B4253957
theorem B378427 : Blo 195805 378427 := bstep (se 1 (by rfl) ⟨283820, by rfl⟩ : syracuseStep 378427 = 567641) B567641
theorem B444023 : Blo 195805 444023 := bstep (se 1 (by rfl) ⟨333017, by rfl⟩ : syracuseStep 444023 = 666035) B666035
theorem B378503 : Blo 195805 378503 := bstep (se 1 (by rfl) ⟨283877, by rfl⟩ : syracuseStep 378503 = 567755) B567755
theorem B476873 : Blo 195805 476873 := bstep (se 2 (by rfl) ⟨178827, by rfl⟩ : syracuseStep 476873 = 357655) B357655
theorem B444203 : Blo 195805 444203 := bstep (se 1 (by rfl) ⟨333152, by rfl⟩ : syracuseStep 444203 = 666305) B666305
theorem B673595 : Blo 195805 673595 := bstep (se 1 (by rfl) ⟨505196, by rfl⟩ : syracuseStep 673595 = 1010393) B1010393
theorem B1001483 : Blo 195805 1001483 := bstep (se 1 (by rfl) ⟨751112, by rfl⟩ : syracuseStep 1001483 = 1502225) B1502225
theorem B1722391 : Blo 195805 1722391 := bstep (se 1 (by rfl) ⟨1291793, by rfl⟩ : syracuseStep 1722391 = 2583587) B2583587
theorem B378913 : Blo 195805 378913 := bstep (se 2 (by rfl) ⟨142092, by rfl⟩ : syracuseStep 378913 = 284185) B284185
theorem B247951 : Blo 195805 247951 := bstep (se 1 (by rfl) ⟨185963, by rfl⟩ : syracuseStep 247951 = 371927) B371927
theorem B444563 : Blo 195805 444563 := bstep (se 1 (by rfl) ⟨333422, by rfl⟩ : syracuseStep 444563 = 666845) B666845
theorem B1001645 : Blo 195805 1001645 := bstep (se 3 (by rfl) ⟨187808, by rfl⟩ : syracuseStep 1001645 = 375617) B375617
theorem B444617 : Blo 195805 444617 := bstep (se 2 (by rfl) ⟨166731, by rfl⟩ : syracuseStep 444617 = 333463) B333463
theorem B674081 : Blo 195805 674081 := bstep (se 2 (by rfl) ⟨252780, by rfl⟩ : syracuseStep 674081 = 505561) B505561
theorem B248123 : Blo 195805 248123 := bstep (se 1 (by rfl) ⟨186092, by rfl⟩ : syracuseStep 248123 = 372185) B372185
theorem B379255 : Blo 195805 379255 := bstep (se 1 (by rfl) ⟨284441, by rfl⟩ : syracuseStep 379255 = 568883) B568883
theorem B2509379 : Blo 195805 2509379 := bstep (se 1 (by rfl) ⟨1882034, by rfl⟩ : syracuseStep 2509379 = 3764069) B3764069
theorem B281161 : Blo 195805 281161 := bstep (se 2 (by rfl) ⟨105435, by rfl⟩ : syracuseStep 281161 = 210871) B210871
theorem B9226871 : Blo 195805 9226871 := bstep (se 1 (by rfl) ⟨6920153, by rfl⟩ : syracuseStep 9226871 = 13840307) B13840307
theorem B314057 : Blo 195805 314057 := bstep (se 2 (by rfl) ⟨117771, by rfl⟩ : syracuseStep 314057 = 235543) B235543
theorem B510779 : Blo 195805 510779 := bstep (se 1 (by rfl) ⟨383084, by rfl⟩ : syracuseStep 510779 = 766169) B766169
theorem B445319 : Blo 195805 445319 := bstep (se 1 (by rfl) ⟨333989, by rfl⟩ : syracuseStep 445319 = 667979) B667979
theorem B1133459 : Blo 195805 1133459 := bstep (se 1 (by rfl) ⟨850094, by rfl⟩ : syracuseStep 1133459 = 1700189) B1700189
theorem B1493963 : Blo 195805 1493963 := bstep (se 1 (by rfl) ⟨1120472, by rfl⟩ : syracuseStep 1493963 = 2240945) B2240945
theorem B445499 : Blo 195805 445499 := bstep (se 1 (by rfl) ⟨334124, by rfl⟩ : syracuseStep 445499 = 668249) B668249
theorem B445625 : Blo 195805 445625 := bstep (se 2 (by rfl) ⟨167109, by rfl⟩ : syracuseStep 445625 = 334219) B334219
theorem B249095 : Blo 195805 249095 := bstep (se 1 (by rfl) ⟨186821, by rfl⟩ : syracuseStep 249095 = 373643) B373643
theorem B1133959 : Blo 195805 1133959 := bstep (se 1 (by rfl) ⟨850469, by rfl⟩ : syracuseStep 1133959 = 1700939) B1700939
theorem B445967 : Blo 195805 445967 := bstep (se 1 (by rfl) ⟨334475, by rfl⟩ : syracuseStep 445967 = 668951) B668951
theorem B445985 : Blo 195805 445985 := bstep (se 2 (by rfl) ⟨167244, by rfl⟩ : syracuseStep 445985 = 334489) B334489
theorem B314923 : Blo 195805 314923 := bstep (se 1 (by rfl) ⟨236192, by rfl⟩ : syracuseStep 314923 = 472385) B472385
theorem B2248235 : Blo 195805 2248235 := bstep (se 1 (by rfl) ⟨1686176, by rfl⟩ : syracuseStep 2248235 = 3372353) B3372353
theorem B904765 : Blo 195805 904765 := bstep (se 3 (by rfl) ⟨169643, by rfl⟩ : syracuseStep 904765 = 339287) B339287
theorem B1199809 : Blo 195805 1199809 := bstep (se 2 (by rfl) ⟨449928, by rfl⟩ : syracuseStep 1199809 = 899857) B899857
theorem B1003265 : Blo 195805 1003265 := bstep (se 2 (by rfl) ⟨376224, by rfl⟩ : syracuseStep 1003265 = 752449) B752449
theorem B315179 : Blo 195805 315179 := bstep (se 1 (by rfl) ⟨236384, by rfl⟩ : syracuseStep 315179 = 472769) B472769
theorem B1691441 : Blo 195805 1691441 := bstep (se 2 (by rfl) ⟨634290, by rfl⟩ : syracuseStep 1691441 = 1268581) B1268581
theorem B446327 : Blo 195805 446327 := bstep (se 1 (by rfl) ⟨334745, by rfl⟩ : syracuseStep 446327 = 669491) B669491
theorem B249743 : Blo 195805 249743 := bstep (se 1 (by rfl) ⟨187307, by rfl⟩ : syracuseStep 249743 = 374615) B374615
theorem B1200025 : Blo 195805 1200025 := bstep (se 2 (by rfl) ⟨450009, by rfl⟩ : syracuseStep 1200025 = 900019) B900019
theorem B446507 : Blo 195805 446507 := bstep (se 1 (by rfl) ⟨334880, by rfl⟩ : syracuseStep 446507 = 669761) B669761
theorem B446867 : Blo 195805 446867 := bstep (se 1 (by rfl) ⟨335150, by rfl⟩ : syracuseStep 446867 = 670301) B670301
theorem B807353 : Blo 195805 807353 := bstep (se 2 (by rfl) ⟨302757, by rfl⟩ : syracuseStep 807353 = 605515) B605515
theorem B446921 : Blo 195805 446921 := bstep (se 2 (by rfl) ⟨167595, by rfl⟩ : syracuseStep 446921 = 335191) B335191
theorem B840203 : Blo 195805 840203 := bstep (se 1 (by rfl) ⟨630152, by rfl⟩ : syracuseStep 840203 = 1260305) B1260305
theorem B1004075 : Blo 195805 1004075 := bstep (se 1 (by rfl) ⟨753056, by rfl⟩ : syracuseStep 1004075 = 1506113) B1506113
theorem B840253 : Blo 195805 840253 := bstep (se 3 (by rfl) ⟨157547, by rfl⟩ : syracuseStep 840253 = 315095) B315095
theorem B1430093 : Blo 195805 1430093 := bstep (se 3 (by rfl) ⟨268142, by rfl⟩ : syracuseStep 1430093 = 536285) B536285
theorem B480043 : Blo 195805 480043 := bstep (se 1 (by rfl) ⟨360032, by rfl⟩ : syracuseStep 480043 = 720065) B720065
theorem B906137 : Blo 195805 906137 := bstep (se 2 (by rfl) ⟨339801, by rfl⟩ : syracuseStep 906137 = 679603) B679603
theorem B676907 : Blo 195805 676907 := bstep (se 1 (by rfl) ⟨507680, by rfl⟩ : syracuseStep 676907 = 1015361) B1015361
theorem B447623 : Blo 195805 447623 := bstep (se 1 (by rfl) ⟨335717, by rfl⟩ : syracuseStep 447623 = 671435) B671435
theorem B382099 : Blo 195805 382099 := bstep (se 1 (by rfl) ⟨286574, by rfl⟩ : syracuseStep 382099 = 573149) B573149
theorem B447803 : Blo 195805 447803 := bstep (se 1 (by rfl) ⟨335852, by rfl⟩ : syracuseStep 447803 = 671705) B671705
theorem B447929 : Blo 195805 447929 := bstep (se 2 (by rfl) ⟨167973, by rfl⟩ : syracuseStep 447929 = 335947) B335947
theorem B284105 : Blo 195805 284105 := bstep (se 2 (by rfl) ⟨106539, by rfl⟩ : syracuseStep 284105 = 213079) B213079
theorem B251407 : Blo 195805 251407 := bstep (se 1 (by rfl) ⟨188555, by rfl⟩ : syracuseStep 251407 = 377111) B377111
theorem B448271 : Blo 195805 448271 := bstep (se 1 (by rfl) ⟨336203, by rfl⟩ : syracuseStep 448271 = 672407) B672407
theorem B448289 : Blo 195805 448289 := bstep (se 2 (by rfl) ⟨168108, by rfl⟩ : syracuseStep 448289 = 336217) B336217
theorem B1005371 : Blo 195805 1005371 := bstep (se 1 (by rfl) ⟨754028, by rfl⟩ : syracuseStep 1005371 = 1508057) B1508057
theorem B1005533 : Blo 195805 1005533 := bstep (se 3 (by rfl) ⟨188537, by rfl⟩ : syracuseStep 1005533 = 377075) B377075
theorem B809003 : Blo 195805 809003 := bstep (se 1 (by rfl) ⟨606752, by rfl⟩ : syracuseStep 809003 = 1213505) B1213505
theorem B448571 : Blo 195805 448571 := bstep (se 1 (by rfl) ⟨336428, by rfl⟩ : syracuseStep 448571 = 672857) B672857
theorem B448631 : Blo 195805 448631 := bstep (se 1 (by rfl) ⟨336473, by rfl⟩ : syracuseStep 448631 = 672947) B672947
theorem B1267913 : Blo 195805 1267913 := bstep (se 2 (by rfl) ⟨475467, by rfl⟩ : syracuseStep 1267913 = 950935) B950935
theorem B1005857 : Blo 195805 1005857 := bstep (se 2 (by rfl) ⟨377196, by rfl⟩ : syracuseStep 1005857 = 754393) B754393
theorem B448811 : Blo 195805 448811 := bstep (se 1 (by rfl) ⟨336608, by rfl⟩ : syracuseStep 448811 = 673217) B673217
theorem B449171 : Blo 195805 449171 := bstep (se 1 (by rfl) ⟨336878, by rfl⟩ : syracuseStep 449171 = 673757) B673757
theorem B285385 : Blo 195805 285385 := bstep (se 2 (by rfl) ⟨107019, by rfl⟩ : syracuseStep 285385 = 214039) B214039
theorem B449225 : Blo 195805 449225 := bstep (se 2 (by rfl) ⟨168459, by rfl⟩ : syracuseStep 449225 = 336919) B336919
theorem B744173 : Blo 195805 744173 := bstep (se 3 (by rfl) ⟨139532, by rfl⟩ : syracuseStep 744173 = 279065) B279065
theorem B252715 : Blo 195805 252715 := bstep (se 1 (by rfl) ⟨189536, by rfl⟩ : syracuseStep 252715 = 379073) B379073
theorem B1891187 : Blo 195805 1891187 := bstep (se 1 (by rfl) ⟨1418390, by rfl⟩ : syracuseStep 1891187 = 2836781) B2836781
theorem B744491 : Blo 195805 744491 := bstep (se 1 (by rfl) ⟨558368, by rfl⟩ : syracuseStep 744491 = 1116737) B1116737
theorem B2841733 : Blo 195805 2841733 := bstep (se 4 (by rfl) ⟨266412, by rfl⟩ : syracuseStep 2841733 = 532825) B532825
theorem B1006829 : Blo 195805 1006829 := bstep (se 3 (by rfl) ⟨188780, by rfl⟩ : syracuseStep 1006829 = 377561) B377561
theorem B220423 : Blo 195805 220423 := bstep (se 1 (by rfl) ⟨165317, by rfl⟩ : syracuseStep 220423 = 330635) B330635
theorem B941327 : Blo 195805 941327 := bstep (se 1 (by rfl) ⟨705995, by rfl⟩ : syracuseStep 941327 = 1411991) B1411991
theorem B220603 : Blo 195805 220603 := bstep (se 1 (by rfl) ⟨165452, by rfl⟩ : syracuseStep 220603 = 330905) B330905
theorem B318991 : Blo 195805 318991 := bstep (se 1 (by rfl) ⟨239243, by rfl⟩ : syracuseStep 318991 = 478487) B478487
theorem B319177 : Blo 195805 319177 := bstep (se 2 (by rfl) ⟨119691, by rfl⟩ : syracuseStep 319177 = 239383) B239383
theorem B843635 : Blo 195805 843635 := bstep (se 1 (by rfl) ⟨632726, by rfl⟩ : syracuseStep 843635 = 1265453) B1265453
theorem B221071 : Blo 195805 221071 := bstep (se 1 (by rfl) ⟨165803, by rfl⟩ : syracuseStep 221071 = 331607) B331607
theorem B1794059 : Blo 195805 1794059 := bstep (se 1 (by rfl) ⟨1345544, by rfl⟩ : syracuseStep 1794059 = 2691089) B2691089
theorem B1007639 : Blo 195805 1007639 := bstep (se 1 (by rfl) ⟨755729, by rfl⟩ : syracuseStep 1007639 = 1511459) B1511459
theorem B1499309 : Blo 195805 1499309 := bstep (se 3 (by rfl) ⟨281120, by rfl⟩ : syracuseStep 1499309 = 562241) B562241
theorem B221575 : Blo 195805 221575 := bstep (se 1 (by rfl) ⟨166181, by rfl⟩ : syracuseStep 221575 = 332363) B332363
theorem B3236395 : Blo 195805 3236395 := bstep (se 1 (by rfl) ⟨2427296, by rfl⟩ : syracuseStep 3236395 = 4854593) B4854593
theorem B221755 : Blo 195805 221755 := bstep (se 1 (by rfl) ⟨166316, by rfl⟩ : syracuseStep 221755 = 332633) B332633
theorem B2122307 : Blo 195805 2122307 := bstep (se 1 (by rfl) ⟨1591730, by rfl⟩ : syracuseStep 2122307 = 3183461) B3183461
theorem B844577 : Blo 195805 844577 := bstep (se 2 (by rfl) ⟨316716, by rfl⟩ : syracuseStep 844577 = 633433) B633433
theorem B680737 : Blo 195805 680737 := bstep (se 2 (by rfl) ⟨255276, by rfl⟩ : syracuseStep 680737 = 510553) B510553
theorem B1270579 : Blo 195805 1270579 := bstep (se 1 (by rfl) ⟨952934, by rfl⟩ : syracuseStep 1270579 = 1905869) B1905869
theorem B222223 : Blo 195805 222223 := bstep (se 1 (by rfl) ⟨166667, by rfl⟩ : syracuseStep 222223 = 333335) B333335
theorem B1532951 : Blo 195805 1532951 := bstep (se 1 (by rfl) ⟨1149713, by rfl⟩ : syracuseStep 1532951 = 2299427) B2299427
theorem B451855 : Blo 195805 451855 := bstep (se 1 (by rfl) ⟨338891, by rfl⟩ : syracuseStep 451855 = 677783) B677783
theorem B222727 : Blo 195805 222727 := bstep (se 1 (by rfl) ⟨167045, by rfl⟩ : syracuseStep 222727 = 334091) B334091
theorem B222907 : Blo 195805 222907 := bstep (se 1 (by rfl) ⟨167180, by rfl⟩ : syracuseStep 222907 = 334361) B334361
theorem B845549 : Blo 195805 845549 := bstep (se 3 (by rfl) ⟨158540, by rfl⟩ : syracuseStep 845549 = 317081) B317081
theorem B14444405 : Blo 195805 14444405 := bstep (se 5 (by rfl) ⟨677081, by rfl⟩ : syracuseStep 14444405 = 1354163) B1354163
theorem B223375 : Blo 195805 223375 := bstep (se 1 (by rfl) ⟨167531, by rfl⟩ : syracuseStep 223375 = 335063) B335063
theorem B420041 : Blo 195805 420041 := bstep (se 2 (by rfl) ⟨157515, by rfl⟩ : syracuseStep 420041 = 315031) B315031
theorem B846233 : Blo 195805 846233 := bstep (se 2 (by rfl) ⟨317337, by rfl⟩ : syracuseStep 846233 = 634675) B634675
theorem B748061 : Blo 195805 748061 := bstep (se 3 (by rfl) ⟨140261, by rfl⟩ : syracuseStep 748061 = 280523) B280523
theorem B748075 : Blo 195805 748075 := bstep (se 1 (by rfl) ⟨561056, by rfl⟩ : syracuseStep 748075 = 1122113) B1122113
theorem B1501739 : Blo 195805 1501739 := bstep (se 1 (by rfl) ⟨1126304, by rfl⟩ : syracuseStep 1501739 = 2252609) B2252609
theorem B3828343 : Blo 195805 3828343 := bstep (se 1 (by rfl) ⟨2871257, by rfl⟩ : syracuseStep 3828343 = 5742515) B5742515
theorem B223879 : Blo 195805 223879 := bstep (se 1 (by rfl) ⟨167909, by rfl⟩ : syracuseStep 223879 = 335819) B335819
theorem B1010369 : Blo 195805 1010369 := bstep (se 2 (by rfl) ⟨378888, by rfl⟩ : syracuseStep 1010369 = 757777) B757777
theorem B4025123 : Blo 195805 4025123 := bstep (se 1 (by rfl) ⟨3018842, by rfl⟩ : syracuseStep 4025123 = 6037685) B6037685
theorem B224059 : Blo 195805 224059 := bstep (se 1 (by rfl) ⟨168044, by rfl⟩ : syracuseStep 224059 = 336089) B336089
theorem B715655 : Blo 195805 715655 := bstep (se 1 (by rfl) ⟨536741, by rfl⟩ : syracuseStep 715655 = 1073483) B1073483
theorem B1010717 : Blo 195805 1010717 := bstep (se 3 (by rfl) ⟨189509, by rfl⟩ : syracuseStep 1010717 = 379019) B379019
theorem B224527 : Blo 195805 224527 := bstep (se 1 (by rfl) ⟨168395, by rfl⟩ : syracuseStep 224527 = 336791) B336791
theorem B1011203 : Blo 195805 1011203 := bstep (se 1 (by rfl) ⟨758402, by rfl⟩ : syracuseStep 1011203 = 1516805) B1516805
theorem B58453589 : Blo 195805 58453589 := bstep (se 8 (by rfl) ⟨342501, by rfl⟩ : syracuseStep 58453589 = 685003) B685003
theorem B2256983 : Blo 195805 2256983 := bstep (se 1 (by rfl) ⟨1692737, by rfl⟩ : syracuseStep 2256983 = 3385475) B3385475
theorem B422023 : Blo 195805 422023 := bstep (se 1 (by rfl) ⟨316517, by rfl⟩ : syracuseStep 422023 = 633035) B633035
theorem B1208591 : Blo 195805 1208591 := bstep (se 1 (by rfl) ⟨906443, by rfl⟩ : syracuseStep 1208591 = 1812887) B1812887
theorem B1896797 : Blo 195805 1896797 := bstep (se 3 (by rfl) ⟨355649, by rfl⟩ : syracuseStep 1896797 = 711299) B711299
theorem B2158979 : Blo 195805 2158979 := bstep (se 1 (by rfl) ⟨1619234, by rfl⟩ : syracuseStep 2158979 = 3238469) B3238469
theorem B2388371 : Blo 195805 2388371 := bstep (se 1 (by rfl) ⟨1791278, by rfl⟩ : syracuseStep 2388371 = 3582557) B3582557
theorem B357691 : Blo 195805 357691 := bstep (se 1 (by rfl) ⟨268268, by rfl⟩ : syracuseStep 357691 = 536537) B536537
theorem B1209659 : Blo 195805 1209659 := bstep (se 1 (by rfl) ⟨907244, by rfl⟩ : syracuseStep 1209659 = 1814489) B1814489
theorem B718379 : Blo 195805 718379 := bstep (se 1 (by rfl) ⟨538784, by rfl⟩ : syracuseStep 718379 = 1077569) B1077569
theorem B1439525 : Blo 195805 1439525 := bstep (se 4 (by rfl) ⟨134955, by rfl⟩ : syracuseStep 1439525 = 269911) B269911
theorem B358187 : Blo 195805 358187 := bstep (se 1 (by rfl) ⟨268640, by rfl⟩ : syracuseStep 358187 = 537281) B537281
theorem B5732369 : Blo 195805 5732369 := bstep (se 2 (by rfl) ⟨2149638, by rfl⟩ : syracuseStep 5732369 = 4299277) B4299277
theorem B293819 : Blo 195805 293819 := bstep (se 1 (by rfl) ⟨220364, by rfl⟩ : syracuseStep 293819 = 440729) B440729
theorem B359369 : Blo 195805 359369 := bstep (se 2 (by rfl) ⟨134763, by rfl⟩ : syracuseStep 359369 = 269527) B269527
theorem B293879 : Blo 195805 293879 := bstep (se 1 (by rfl) ⟨220409, by rfl⟩ : syracuseStep 293879 = 440819) B440819
theorem B293903 : Blo 195805 293903 := bstep (se 1 (by rfl) ⟨220427, by rfl⟩ : syracuseStep 293903 = 440855) B440855
theorem B293945 : Blo 195805 293945 := bstep (se 2 (by rfl) ⟨110229, by rfl⟩ : syracuseStep 293945 = 220459) B220459
theorem B6454333 : Blo 195805 6454333 := bstep (se 3 (by rfl) ⟨1210187, by rfl⟩ : syracuseStep 6454333 = 2420375) B2420375
theorem B294023 : Blo 195805 294023 := bstep (se 1 (by rfl) ⟨220517, by rfl⟩ : syracuseStep 294023 = 441035) B441035
theorem B294059 : Blo 195805 294059 := bstep (se 1 (by rfl) ⟨220544, by rfl⟩ : syracuseStep 294059 = 441089) B441089
theorem B294089 : Blo 195805 294089 := bstep (se 2 (by rfl) ⟨110283, by rfl⟩ : syracuseStep 294089 = 220567) B220567
theorem B195847 : Blo 195805 195847 := bstep (se 1 (by rfl) ⟨146885, by rfl⟩ : syracuseStep 195847 = 293771) B293771
theorem B195855 : Blo 195805 195855 := bstep (se 1 (by rfl) ⟨146891, by rfl⟩ : syracuseStep 195855 = 293783) B293783
theorem B195899 : Blo 195805 195899 := bstep (se 1 (by rfl) ⟨146924, by rfl⟩ : syracuseStep 195899 = 293849) B293849
theorem B294203 : Blo 195805 294203 := bstep (se 1 (by rfl) ⟨220652, by rfl⟩ : syracuseStep 294203 = 441305) B441305
theorem B294263 : Blo 195805 294263 := bstep (se 1 (by rfl) ⟨220697, by rfl⟩ : syracuseStep 294263 = 441395) B441395
theorem B195975 : Blo 195805 195975 := bstep (se 1 (by rfl) ⟨146981, by rfl⟩ : syracuseStep 195975 = 293963) B293963
theorem B195983 : Blo 195805 195983 := bstep (se 1 (by rfl) ⟨146987, by rfl⟩ : syracuseStep 195983 = 293975) B293975
theorem B294287 : Blo 195805 294287 := bstep (se 1 (by rfl) ⟨220715, by rfl⟩ : syracuseStep 294287 = 441431) B441431
theorem B294329 : Blo 195805 294329 := bstep (se 2 (by rfl) ⟨110373, by rfl⟩ : syracuseStep 294329 = 220747) B220747
theorem B196027 : Blo 195805 196027 := bstep (se 1 (by rfl) ⟨147020, by rfl⟩ : syracuseStep 196027 = 294041) B294041
theorem B196103 : Blo 195805 196103 := bstep (se 1 (by rfl) ⟨147077, by rfl⟩ : syracuseStep 196103 = 294155) B294155
theorem B294407 : Blo 195805 294407 := bstep (se 1 (by rfl) ⟨220805, by rfl⟩ : syracuseStep 294407 = 441611) B441611
theorem B196111 : Blo 195805 196111 := bstep (se 1 (by rfl) ⟨147083, by rfl⟩ : syracuseStep 196111 = 294167) B294167
theorem B294443 : Blo 195805 294443 := bstep (se 1 (by rfl) ⟨220832, by rfl⟩ : syracuseStep 294443 = 441665) B441665
theorem B196155 : Blo 195805 196155 := bstep (se 1 (by rfl) ⟨147116, by rfl⟩ : syracuseStep 196155 = 294233) B294233
theorem B294473 : Blo 195805 294473 := bstep (se 2 (by rfl) ⟨110427, by rfl⟩ : syracuseStep 294473 = 220855) B220855
theorem B753239 : Blo 195805 753239 := bstep (se 1 (by rfl) ⟨564929, by rfl⟩ : syracuseStep 753239 = 1129859) B1129859
theorem B196231 : Blo 195805 196231 := bstep (se 1 (by rfl) ⟨147173, by rfl⟩ : syracuseStep 196231 = 294347) B294347
theorem B196239 : Blo 195805 196239 := bstep (se 1 (by rfl) ⟨147179, by rfl⟩ : syracuseStep 196239 = 294359) B294359
theorem B196283 : Blo 195805 196283 := bstep (se 1 (by rfl) ⟨147212, by rfl⟩ : syracuseStep 196283 = 294425) B294425
theorem B294587 : Blo 195805 294587 := bstep (se 1 (by rfl) ⟨220940, by rfl⟩ : syracuseStep 294587 = 441881) B441881
theorem B294647 : Blo 195805 294647 := bstep (se 1 (by rfl) ⟨220985, by rfl⟩ : syracuseStep 294647 = 441971) B441971
theorem B3768065 : Blo 195805 3768065 := bstep (se 2 (by rfl) ⟨1413024, by rfl⟩ : syracuseStep 3768065 = 2826049) B2826049
theorem B196359 : Blo 195805 196359 := bstep (se 1 (by rfl) ⟨147269, by rfl⟩ : syracuseStep 196359 = 294539) B294539
theorem B196367 : Blo 195805 196367 := bstep (se 1 (by rfl) ⟨147275, by rfl⟩ : syracuseStep 196367 = 294551) B294551
theorem B294671 : Blo 195805 294671 := bstep (se 1 (by rfl) ⟨221003, by rfl⟩ : syracuseStep 294671 = 442007) B442007
theorem B294713 : Blo 195805 294713 := bstep (se 2 (by rfl) ⟨110517, by rfl⟩ : syracuseStep 294713 = 221035) B221035
theorem B196411 : Blo 195805 196411 := bstep (se 1 (by rfl) ⟨147308, by rfl⟩ : syracuseStep 196411 = 294617) B294617
theorem B196487 : Blo 195805 196487 := bstep (se 1 (by rfl) ⟨147365, by rfl⟩ : syracuseStep 196487 = 294731) B294731
theorem B294791 : Blo 195805 294791 := bstep (se 1 (by rfl) ⟨221093, by rfl⟩ : syracuseStep 294791 = 442187) B442187
theorem B196495 : Blo 195805 196495 := bstep (se 1 (by rfl) ⟨147371, by rfl⟩ : syracuseStep 196495 = 294743) B294743
theorem B294827 : Blo 195805 294827 := bstep (se 1 (by rfl) ⟨221120, by rfl⟩ : syracuseStep 294827 = 442241) B442241
theorem B196539 : Blo 195805 196539 := bstep (se 1 (by rfl) ⟨147404, by rfl⟩ : syracuseStep 196539 = 294809) B294809
theorem B294857 : Blo 195805 294857 := bstep (se 2 (by rfl) ⟨110571, by rfl⟩ : syracuseStep 294857 = 221143) B221143
theorem B196647 : Blo 195805 196647 := bstep (se 1 (by rfl) ⟨147485, by rfl⟩ : syracuseStep 196647 = 294971) B294971
theorem B196687 : Blo 195805 196687 := bstep (se 1 (by rfl) ⟨147515, by rfl⟩ : syracuseStep 196687 = 295031) B295031
theorem B196703 : Blo 195805 196703 := bstep (se 1 (by rfl) ⟨147527, by rfl⟩ : syracuseStep 196703 = 295055) B295055
theorem B196731 : Blo 195805 196731 := bstep (se 1 (by rfl) ⟨147548, by rfl⟩ : syracuseStep 196731 = 295097) B295097
theorem B1441955 : Blo 195805 1441955 := bstep (se 1 (by rfl) ⟨1081466, by rfl⟩ : syracuseStep 1441955 = 2162933) B2162933
theorem B196783 : Blo 195805 196783 := bstep (se 1 (by rfl) ⟨147587, by rfl⟩ : syracuseStep 196783 = 295175) B295175
theorem B196807 : Blo 195805 196807 := bstep (se 1 (by rfl) ⟨147605, by rfl⟩ : syracuseStep 196807 = 295211) B295211
theorem B196827 : Blo 195805 196827 := bstep (se 1 (by rfl) ⟨147620, by rfl⟩ : syracuseStep 196827 = 295241) B295241
theorem B196903 : Blo 195805 196903 := bstep (se 1 (by rfl) ⟨147677, by rfl⟩ : syracuseStep 196903 = 295355) B295355
theorem B196943 : Blo 195805 196943 := bstep (se 1 (by rfl) ⟨147707, by rfl⟩ : syracuseStep 196943 = 295415) B295415
theorem B196959 : Blo 195805 196959 := bstep (se 1 (by rfl) ⟨147719, by rfl⟩ : syracuseStep 196959 = 295439) B295439
theorem B196987 : Blo 195805 196987 := bstep (se 1 (by rfl) ⟨147740, by rfl⟩ : syracuseStep 196987 = 295481) B295481
theorem B295343 : Blo 195805 295343 := bstep (se 1 (by rfl) ⟨221507, by rfl⟩ : syracuseStep 295343 = 443015) B443015
theorem B197039 : Blo 195805 197039 := bstep (se 1 (by rfl) ⟨147779, by rfl⟩ : syracuseStep 197039 = 295559) B295559
theorem B197063 : Blo 195805 197063 := bstep (se 1 (by rfl) ⟨147797, by rfl⟩ : syracuseStep 197063 = 295595) B295595
theorem B197083 : Blo 195805 197083 := bstep (se 1 (by rfl) ⟨147812, by rfl⟩ : syracuseStep 197083 = 295625) B295625
theorem B295433 : Blo 195805 295433 := bstep (se 2 (by rfl) ⟨110787, by rfl⟩ : syracuseStep 295433 = 221575) B221575
theorem B295463 : Blo 195805 295463 := bstep (se 1 (by rfl) ⟨221597, by rfl⟩ : syracuseStep 295463 = 443195) B443195
theorem B197159 : Blo 195805 197159 := bstep (se 1 (by rfl) ⟨147869, by rfl⟩ : syracuseStep 197159 = 295739) B295739
theorem B197199 : Blo 195805 197199 := bstep (se 1 (by rfl) ⟨147899, by rfl⟩ : syracuseStep 197199 = 295799) B295799
theorem B197215 : Blo 195805 197215 := bstep (se 1 (by rfl) ⟨147911, by rfl⟩ : syracuseStep 197215 = 295823) B295823
theorem B295547 : Blo 195805 295547 := bstep (se 1 (by rfl) ⟨221660, by rfl⟩ : syracuseStep 295547 = 443321) B443321
theorem B197243 : Blo 195805 197243 := bstep (se 1 (by rfl) ⟨147932, by rfl⟩ : syracuseStep 197243 = 295865) B295865
theorem B197295 : Blo 195805 197295 := bstep (se 1 (by rfl) ⟨147971, by rfl⟩ : syracuseStep 197295 = 295943) B295943
theorem B197319 : Blo 195805 197319 := bstep (se 1 (by rfl) ⟨147989, by rfl⟩ : syracuseStep 197319 = 295979) B295979
theorem B197339 : Blo 195805 197339 := bstep (se 1 (by rfl) ⟨148004, by rfl⟩ : syracuseStep 197339 = 296009) B296009
theorem B295673 : Blo 195805 295673 := bstep (se 2 (by rfl) ⟨110877, by rfl⟩ : syracuseStep 295673 = 221755) B221755
theorem B197415 : Blo 195805 197415 := bstep (se 1 (by rfl) ⟨148061, by rfl⟩ : syracuseStep 197415 = 296123) B296123
theorem B197455 : Blo 195805 197455 := bstep (se 1 (by rfl) ⟨148091, by rfl⟩ : syracuseStep 197455 = 296183) B296183
theorem B295775 : Blo 195805 295775 := bstep (se 1 (by rfl) ⟨221831, by rfl⟩ : syracuseStep 295775 = 443663) B443663
theorem B197471 : Blo 195805 197471 := bstep (se 1 (by rfl) ⟨148103, by rfl⟩ : syracuseStep 197471 = 296207) B296207
theorem B295787 : Blo 195805 295787 := bstep (se 1 (by rfl) ⟨221840, by rfl⟩ : syracuseStep 295787 = 443681) B443681
theorem B197499 : Blo 195805 197499 := bstep (se 1 (by rfl) ⟨148124, by rfl⟩ : syracuseStep 197499 = 296249) B296249
theorem B197551 : Blo 195805 197551 := bstep (se 1 (by rfl) ⟨148163, by rfl⟩ : syracuseStep 197551 = 296327) B296327
theorem B197575 : Blo 195805 197575 := bstep (se 1 (by rfl) ⟨148181, by rfl⟩ : syracuseStep 197575 = 296363) B296363
theorem B197595 : Blo 195805 197595 := bstep (se 1 (by rfl) ⟨148196, by rfl⟩ : syracuseStep 197595 = 296393) B296393
theorem B197671 : Blo 195805 197671 := bstep (se 1 (by rfl) ⟨148253, by rfl⟩ : syracuseStep 197671 = 296507) B296507
theorem B296015 : Blo 195805 296015 := bstep (se 1 (by rfl) ⟨222011, by rfl⟩ : syracuseStep 296015 = 444023) B444023
theorem B197711 : Blo 195805 197711 := bstep (se 1 (by rfl) ⟨148283, by rfl⟩ : syracuseStep 197711 = 296567) B296567
theorem B197727 : Blo 195805 197727 := bstep (se 1 (by rfl) ⟨148295, by rfl⟩ : syracuseStep 197727 = 296591) B296591
theorem B197755 : Blo 195805 197755 := bstep (se 1 (by rfl) ⟨148316, by rfl⟩ : syracuseStep 197755 = 296633) B296633
theorem B197807 : Blo 195805 197807 := bstep (se 1 (by rfl) ⟨148355, by rfl⟩ : syracuseStep 197807 = 296711) B296711
theorem B296135 : Blo 195805 296135 := bstep (se 1 (by rfl) ⟨222101, by rfl⟩ : syracuseStep 296135 = 444203) B444203
theorem B197831 : Blo 195805 197831 := bstep (se 1 (by rfl) ⟨148373, by rfl⟩ : syracuseStep 197831 = 296747) B296747
theorem B197851 : Blo 195805 197851 := bstep (se 1 (by rfl) ⟨148388, by rfl⟩ : syracuseStep 197851 = 296777) B296777
theorem B197927 : Blo 195805 197927 := bstep (se 1 (by rfl) ⟨148445, by rfl⟩ : syracuseStep 197927 = 296891) B296891
theorem B197967 : Blo 195805 197967 := bstep (se 1 (by rfl) ⟨148475, by rfl⟩ : syracuseStep 197967 = 296951) B296951
theorem B197983 : Blo 195805 197983 := bstep (se 1 (by rfl) ⟨148487, by rfl⟩ : syracuseStep 197983 = 296975) B296975
theorem B296297 : Blo 195805 296297 := bstep (se 2 (by rfl) ⟨111111, by rfl⟩ : syracuseStep 296297 = 222223) B222223
theorem B198011 : Blo 195805 198011 := bstep (se 1 (by rfl) ⟨148508, by rfl⟩ : syracuseStep 198011 = 297017) B297017
theorem B198063 : Blo 195805 198063 := bstep (se 1 (by rfl) ⟨148547, by rfl⟩ : syracuseStep 198063 = 297095) B297095
theorem B296375 : Blo 195805 296375 := bstep (se 1 (by rfl) ⟨222281, by rfl⟩ : syracuseStep 296375 = 444563) B444563
theorem B198087 : Blo 195805 198087 := bstep (se 1 (by rfl) ⟨148565, by rfl⟩ : syracuseStep 198087 = 297131) B297131
theorem B296411 : Blo 195805 296411 := bstep (se 1 (by rfl) ⟨222308, by rfl⟩ : syracuseStep 296411 = 444617) B444617
theorem B198107 : Blo 195805 198107 := bstep (se 1 (by rfl) ⟨148580, by rfl⟩ : syracuseStep 198107 = 297161) B297161
theorem B198183 : Blo 195805 198183 := bstep (se 1 (by rfl) ⟨148637, by rfl⟩ : syracuseStep 198183 = 297275) B297275
theorem B3409451 : Blo 195805 3409451 := bstep (se 1 (by rfl) ⟨2557088, by rfl⟩ : syracuseStep 3409451 = 5114177) B5114177
theorem B198223 : Blo 195805 198223 := bstep (se 1 (by rfl) ⟨148667, by rfl⟩ : syracuseStep 198223 = 297335) B297335
theorem B198239 : Blo 195805 198239 := bstep (se 1 (by rfl) ⟨148679, by rfl⟩ : syracuseStep 198239 = 297359) B297359
theorem B198267 : Blo 195805 198267 := bstep (se 1 (by rfl) ⟨148700, by rfl⟩ : syracuseStep 198267 = 297401) B297401
theorem B198319 : Blo 195805 198319 := bstep (se 1 (by rfl) ⟨148739, by rfl⟩ : syracuseStep 198319 = 297479) B297479
theorem B198343 : Blo 195805 198343 := bstep (se 1 (by rfl) ⟨148757, by rfl⟩ : syracuseStep 198343 = 297515) B297515
theorem B1672919 : Blo 195805 1672919 := bstep (se 1 (by rfl) ⟨1254689, by rfl⟩ : syracuseStep 1672919 = 2509379) B2509379
theorem B198363 : Blo 195805 198363 := bstep (se 1 (by rfl) ⟨148772, by rfl⟩ : syracuseStep 198363 = 297545) B297545
theorem B198439 : Blo 195805 198439 := bstep (se 1 (by rfl) ⟨148829, by rfl⟩ : syracuseStep 198439 = 297659) B297659
theorem B198479 : Blo 195805 198479 := bstep (se 1 (by rfl) ⟨148859, by rfl⟩ : syracuseStep 198479 = 297719) B297719
theorem B198495 : Blo 195805 198495 := bstep (se 1 (by rfl) ⟨148871, by rfl⟩ : syracuseStep 198495 = 297743) B297743
theorem B198523 : Blo 195805 198523 := bstep (se 1 (by rfl) ⟨148892, by rfl⟩ : syracuseStep 198523 = 297785) B297785
theorem B296879 : Blo 195805 296879 := bstep (se 1 (by rfl) ⟨222659, by rfl⟩ : syracuseStep 296879 = 445319) B445319
theorem B198575 : Blo 195805 198575 := bstep (se 1 (by rfl) ⟨148931, by rfl⟩ : syracuseStep 198575 = 297863) B297863
theorem B755639 : Blo 195805 755639 := bstep (se 1 (by rfl) ⟨566729, by rfl⟩ : syracuseStep 755639 = 1133459) B1133459
theorem B722875 : Blo 195805 722875 := bstep (se 1 (by rfl) ⟨542156, by rfl⟩ : syracuseStep 722875 = 1084313) B1084313
theorem B198599 : Blo 195805 198599 := bstep (se 1 (by rfl) ⟨148949, by rfl⟩ : syracuseStep 198599 = 297899) B297899
theorem B198619 : Blo 195805 198619 := bstep (se 1 (by rfl) ⟨148964, by rfl⟩ : syracuseStep 198619 = 297929) B297929
theorem B296969 : Blo 195805 296969 := bstep (se 2 (by rfl) ⟨111363, by rfl⟩ : syracuseStep 296969 = 222727) B222727
theorem B296999 : Blo 195805 296999 := bstep (se 1 (by rfl) ⟨222749, by rfl⟩ : syracuseStep 296999 = 445499) B445499
theorem B198695 : Blo 195805 198695 := bstep (se 1 (by rfl) ⟨149021, by rfl⟩ : syracuseStep 198695 = 298043) B298043
theorem B198735 : Blo 195805 198735 := bstep (se 1 (by rfl) ⟨149051, by rfl⟩ : syracuseStep 198735 = 298103) B298103
theorem B198751 : Blo 195805 198751 := bstep (se 1 (by rfl) ⟨149063, by rfl⟩ : syracuseStep 198751 = 298127) B298127
theorem B297083 : Blo 195805 297083 := bstep (se 1 (by rfl) ⟨222812, by rfl⟩ : syracuseStep 297083 = 445625) B445625
theorem B198779 : Blo 195805 198779 := bstep (se 1 (by rfl) ⟨149084, by rfl⟩ : syracuseStep 198779 = 298169) B298169
theorem B198831 : Blo 195805 198831 := bstep (se 1 (by rfl) ⟨149123, by rfl⟩ : syracuseStep 198831 = 298247) B298247
theorem B198855 : Blo 195805 198855 := bstep (se 1 (by rfl) ⟨149141, by rfl⟩ : syracuseStep 198855 = 298283) B298283
theorem B198875 : Blo 195805 198875 := bstep (se 1 (by rfl) ⟨149156, by rfl⟩ : syracuseStep 198875 = 298313) B298313
theorem B297209 : Blo 195805 297209 := bstep (se 2 (by rfl) ⟨111453, by rfl⟩ : syracuseStep 297209 = 222907) B222907
theorem B198951 : Blo 195805 198951 := bstep (se 1 (by rfl) ⟨149213, by rfl⟩ : syracuseStep 198951 = 298427) B298427
theorem B198991 : Blo 195805 198991 := bstep (se 1 (by rfl) ⟨149243, by rfl⟩ : syracuseStep 198991 = 298487) B298487
theorem B297311 : Blo 195805 297311 := bstep (se 1 (by rfl) ⟨222983, by rfl⟩ : syracuseStep 297311 = 445967) B445967
theorem B199007 : Blo 195805 199007 := bstep (se 1 (by rfl) ⟨149255, by rfl⟩ : syracuseStep 199007 = 298511) B298511
theorem B297323 : Blo 195805 297323 := bstep (se 1 (by rfl) ⟨222992, by rfl⟩ : syracuseStep 297323 = 445985) B445985
theorem B199035 : Blo 195805 199035 := bstep (se 1 (by rfl) ⟨149276, by rfl⟩ : syracuseStep 199035 = 298553) B298553
theorem B756097 : Blo 195805 756097 := bstep (se 2 (by rfl) ⟨283536, by rfl⟩ : syracuseStep 756097 = 567073) B567073
theorem B199087 : Blo 195805 199087 := bstep (se 1 (by rfl) ⟨149315, by rfl⟩ : syracuseStep 199087 = 298631) B298631
theorem B199111 : Blo 195805 199111 := bstep (se 1 (by rfl) ⟨149333, by rfl⟩ : syracuseStep 199111 = 298667) B298667
theorem B199131 : Blo 195805 199131 := bstep (se 1 (by rfl) ⟨149348, by rfl⟩ : syracuseStep 199131 = 298697) B298697
theorem B199207 : Blo 195805 199207 := bstep (se 1 (by rfl) ⟨149405, by rfl⟩ : syracuseStep 199207 = 298811) B298811
theorem B297551 : Blo 195805 297551 := bstep (se 1 (by rfl) ⟨223163, by rfl⟩ : syracuseStep 297551 = 446327) B446327
theorem B199247 : Blo 195805 199247 := bstep (se 1 (by rfl) ⟨149435, by rfl⟩ : syracuseStep 199247 = 298871) B298871
theorem B199263 : Blo 195805 199263 := bstep (se 1 (by rfl) ⟨149447, by rfl⟩ : syracuseStep 199263 = 298895) B298895
theorem B199291 : Blo 195805 199291 := bstep (se 1 (by rfl) ⟨149468, by rfl⟩ : syracuseStep 199291 = 298937) B298937
theorem B199343 : Blo 195805 199343 := bstep (se 1 (by rfl) ⟨149507, by rfl⟩ : syracuseStep 199343 = 299015) B299015
theorem B330439 : Blo 195805 330439 := bstep (se 1 (by rfl) ⟨247829, by rfl⟩ : syracuseStep 330439 = 495659) B495659
theorem B297671 : Blo 195805 297671 := bstep (se 1 (by rfl) ⟨223253, by rfl⟩ : syracuseStep 297671 = 446507) B446507
theorem B199367 : Blo 195805 199367 := bstep (se 1 (by rfl) ⟨149525, by rfl⟩ : syracuseStep 199367 = 299051) B299051
theorem B199387 : Blo 195805 199387 := bstep (se 1 (by rfl) ⟨149540, by rfl⟩ : syracuseStep 199387 = 299081) B299081
theorem B199463 : Blo 195805 199463 := bstep (se 1 (by rfl) ⟨149597, by rfl⟩ : syracuseStep 199463 = 299195) B299195
theorem B199503 : Blo 195805 199503 := bstep (se 1 (by rfl) ⟨149627, by rfl⟩ : syracuseStep 199503 = 299255) B299255
theorem B199519 : Blo 195805 199519 := bstep (se 1 (by rfl) ⟨149639, by rfl⟩ : syracuseStep 199519 = 299279) B299279
theorem B330601 : Blo 195805 330601 := bstep (se 2 (by rfl) ⟨123975, by rfl⟩ : syracuseStep 330601 = 247951) B247951
theorem B297833 : Blo 195805 297833 := bstep (se 2 (by rfl) ⟨111687, by rfl⟩ : syracuseStep 297833 = 223375) B223375
theorem B199547 : Blo 195805 199547 := bstep (se 1 (by rfl) ⟨149660, by rfl⟩ : syracuseStep 199547 = 299321) B299321
theorem B756641 : Blo 195805 756641 := bstep (se 2 (by rfl) ⟨283740, by rfl⟩ : syracuseStep 756641 = 567481) B567481
theorem B199599 : Blo 195805 199599 := bstep (se 1 (by rfl) ⟨149699, by rfl⟩ : syracuseStep 199599 = 299399) B299399
theorem B297911 : Blo 195805 297911 := bstep (se 1 (by rfl) ⟨223433, by rfl⟩ : syracuseStep 297911 = 446867) B446867
theorem B199623 : Blo 195805 199623 := bstep (se 1 (by rfl) ⟨149717, by rfl⟩ : syracuseStep 199623 = 299435) B299435
theorem B297947 : Blo 195805 297947 := bstep (se 1 (by rfl) ⟨223460, by rfl⟩ : syracuseStep 297947 = 446921) B446921
theorem B199643 : Blo 195805 199643 := bstep (se 1 (by rfl) ⟨149732, by rfl⟩ : syracuseStep 199643 = 299465) B299465
theorem B560135 : Blo 195805 560135 := bstep (se 1 (by rfl) ⟨420101, by rfl⟩ : syracuseStep 560135 = 840203) B840203
theorem B199719 : Blo 195805 199719 := bstep (se 1 (by rfl) ⟨149789, by rfl⟩ : syracuseStep 199719 = 299579) B299579
theorem B756793 : Blo 195805 756793 := bstep (se 2 (by rfl) ⟨283797, by rfl⟩ : syracuseStep 756793 = 567595) B567595
theorem B199759 : Blo 195805 199759 := bstep (se 1 (by rfl) ⟨149819, by rfl⟩ : syracuseStep 199759 = 299639) B299639
theorem B199775 : Blo 195805 199775 := bstep (se 1 (by rfl) ⟨149831, by rfl⟩ : syracuseStep 199775 = 299663) B299663
theorem B199803 : Blo 195805 199803 := bstep (se 1 (by rfl) ⟨149852, by rfl⟩ : syracuseStep 199803 = 299705) B299705
theorem B757097 : Blo 195805 757097 := bstep (se 2 (by rfl) ⟨283911, by rfl⟩ : syracuseStep 757097 = 567823) B567823
theorem B298415 : Blo 195805 298415 := bstep (se 1 (by rfl) ⟨223811, by rfl⟩ : syracuseStep 298415 = 447623) B447623
theorem B331195 : Blo 195805 331195 := bstep (se 1 (by rfl) ⟨248396, by rfl⟩ : syracuseStep 331195 = 496793) B496793
theorem B298505 : Blo 195805 298505 := bstep (se 2 (by rfl) ⟨111939, by rfl⟩ : syracuseStep 298505 = 223879) B223879
theorem B331303 : Blo 195805 331303 := bstep (se 1 (by rfl) ⟨248477, by rfl⟩ : syracuseStep 331303 = 496955) B496955
theorem B298535 : Blo 195805 298535 := bstep (se 1 (by rfl) ⟨223901, by rfl⟩ : syracuseStep 298535 = 447803) B447803
theorem B1510973 : Blo 195805 1510973 := bstep (se 3 (by rfl) ⟨283307, by rfl⟩ : syracuseStep 1510973 = 566615) B566615
theorem B298619 : Blo 195805 298619 := bstep (se 1 (by rfl) ⟨223964, by rfl⟩ : syracuseStep 298619 = 447929) B447929
theorem B8261297 : Blo 195805 8261297 := bstep (se 2 (by rfl) ⟨3097986, by rfl⟩ : syracuseStep 8261297 = 6195973) B6195973
theorem B3346109 : Blo 195805 3346109 := bstep (se 3 (by rfl) ⟨627395, by rfl⟩ : syracuseStep 3346109 = 1254791) B1254791
theorem B298745 : Blo 195805 298745 := bstep (se 2 (by rfl) ⟨112029, by rfl⟩ : syracuseStep 298745 = 224059) B224059
theorem B298847 : Blo 195805 298847 := bstep (se 1 (by rfl) ⟨224135, by rfl⟩ : syracuseStep 298847 = 448271) B448271
theorem B331627 : Blo 195805 331627 := bstep (se 1 (by rfl) ⟨248720, by rfl⟩ : syracuseStep 331627 = 497441) B497441
theorem B298859 : Blo 195805 298859 := bstep (se 1 (by rfl) ⟨224144, by rfl⟩ : syracuseStep 298859 = 448289) B448289
theorem B757613 : Blo 195805 757613 := bstep (se 3 (by rfl) ⟨142052, by rfl⟩ : syracuseStep 757613 = 284105) B284105
theorem B299047 : Blo 195805 299047 := bstep (se 1 (by rfl) ⟨224285, by rfl⟩ : syracuseStep 299047 = 448571) B448571
theorem B299087 : Blo 195805 299087 := bstep (se 1 (by rfl) ⟨224315, by rfl⟩ : syracuseStep 299087 = 448631) B448631
theorem B299207 : Blo 195805 299207 := bstep (se 1 (by rfl) ⟨224405, by rfl⟩ : syracuseStep 299207 = 448811) B448811
theorem B299369 : Blo 195805 299369 := bstep (se 2 (by rfl) ⟨112263, by rfl⟩ : syracuseStep 299369 = 224527) B224527
theorem B299447 : Blo 195805 299447 := bstep (se 1 (by rfl) ⟨224585, by rfl⟩ : syracuseStep 299447 = 449171) B449171
theorem B299483 : Blo 195805 299483 := bstep (se 1 (by rfl) ⟨224612, by rfl⟩ : syracuseStep 299483 = 449225) B449225
theorem B496115 : Blo 195805 496115 := bstep (se 1 (by rfl) ⟨372086, by rfl⟩ : syracuseStep 496115 = 744173) B744173
theorem B1511945 : Blo 195805 1511945 := bstep (se 2 (by rfl) ⟨566979, by rfl⟩ : syracuseStep 1511945 = 1133959) B1133959
theorem B758281 : Blo 195805 758281 := bstep (se 2 (by rfl) ⟨284355, by rfl⟩ : syracuseStep 758281 = 568711) B568711
theorem B627385 : Blo 195805 627385 := bstep (se 2 (by rfl) ⟨235269, by rfl⟩ : syracuseStep 627385 = 470539) B470539
theorem B496327 : Blo 195805 496327 := bstep (se 1 (by rfl) ⟨372245, by rfl⟩ : syracuseStep 496327 = 744491) B744491
theorem B955165 : Blo 195805 955165 := bstep (se 3 (by rfl) ⟨179093, by rfl⟩ : syracuseStep 955165 = 358187) B358187
theorem B627551 : Blo 195805 627551 := bstep (se 1 (by rfl) ⟨470663, by rfl⟩ : syracuseStep 627551 = 941327) B941327
theorem B332687 : Blo 195805 332687 := bstep (se 1 (by rfl) ⟨249515, by rfl⟩ : syracuseStep 332687 = 499031) B499031
theorem B332923 : Blo 195805 332923 := bstep (se 1 (by rfl) ⟨249692, by rfl⟩ : syracuseStep 332923 = 499385) B499385
theorem B759145 : Blo 195805 759145 := bstep (se 2 (by rfl) ⟨284679, by rfl⟩ : syracuseStep 759145 = 569359) B569359
theorem B1119653 : Blo 195805 1119653 := bstep (se 4 (by rfl) ⟨104967, by rfl⟩ : syracuseStep 1119653 = 209935) B209935
theorem B562697 : Blo 195805 562697 := bstep (se 2 (by rfl) ⟨211011, by rfl⟩ : syracuseStep 562697 = 422023) B422023
theorem B497249 : Blo 195805 497249 := bstep (se 2 (by rfl) ⟨186468, by rfl⟩ : syracuseStep 497249 = 372937) B372937
theorem B530135 : Blo 195805 530135 := bstep (se 1 (by rfl) ⟨397601, by rfl⟩ : syracuseStep 530135 = 795203) B795203
theorem B1414871 : Blo 195805 1414871 := bstep (se 1 (by rfl) ⟨1061153, by rfl⟩ : syracuseStep 1414871 = 2122307) B2122307
theorem B563051 : Blo 195805 563051 := bstep (se 1 (by rfl) ⟨422288, by rfl⟩ : syracuseStep 563051 = 844577) B844577
theorem B3381101 : Blo 195805 3381101 := bstep (se 3 (by rfl) ⟨633956, by rfl⟩ : syracuseStep 3381101 = 1267913) B1267913
theorem B1513403 : Blo 195805 1513403 := bstep (se 1 (by rfl) ⟨1135052, by rfl⟩ : syracuseStep 1513403 = 2270105) B2270105
theorem B333787 : Blo 195805 333787 := bstep (se 1 (by rfl) ⟨250340, by rfl⟩ : syracuseStep 333787 = 500681) B500681
theorem B858127 : Blo 195805 858127 := bstep (se 1 (by rfl) ⟨643595, by rfl⟩ : syracuseStep 858127 = 1287191) B1287191
theorem B1021967 : Blo 195805 1021967 := bstep (se 1 (by rfl) ⟨766475, by rfl⟩ : syracuseStep 1021967 = 1532951) B1532951
theorem B1120337 : Blo 195805 1120337 := bstep (se 2 (by rfl) ⟨420126, by rfl⟩ : syracuseStep 1120337 = 840253) B840253
theorem B661661 : Blo 195805 661661 := bstep (se 3 (by rfl) ⟨124061, by rfl⟩ : syracuseStep 661661 = 248123) B248123
theorem B563699 : Blo 195805 563699 := bstep (se 1 (by rfl) ⟨422774, by rfl⟩ : syracuseStep 563699 = 845549) B845549
theorem B334415 : Blo 195805 334415 := bstep (se 1 (by rfl) ⟨250811, by rfl⟩ : syracuseStep 334415 = 501623) B501623
theorem B662201 : Blo 195805 662201 := bstep (se 2 (by rfl) ⟨248325, by rfl⟩ : syracuseStep 662201 = 496651) B496651
theorem B564155 : Blo 195805 564155 := bstep (se 1 (by rfl) ⟨423116, by rfl⟩ : syracuseStep 564155 = 846233) B846233
theorem B498707 : Blo 195805 498707 := bstep (se 1 (by rfl) ⟨374030, by rfl⟩ : syracuseStep 498707 = 748061) B748061
theorem B662795 : Blo 195805 662795 := bstep (se 1 (by rfl) ⟨497096, by rfl⟩ : syracuseStep 662795 = 994193) B994193
theorem B335279 : Blo 195805 335279 := bstep (se 1 (by rfl) ⟨251459, by rfl⟩ : syracuseStep 335279 = 502919) B502919
theorem B663065 : Blo 195805 663065 := bstep (se 2 (by rfl) ⟨248649, by rfl⟩ : syracuseStep 663065 = 497299) B497299
theorem B335483 : Blo 195805 335483 := bstep (se 1 (by rfl) ⟨251612, by rfl⟩ : syracuseStep 335483 = 503225) B503225
theorem B532091 : Blo 195805 532091 := bstep (se 1 (by rfl) ⟨399068, by rfl⟩ : syracuseStep 532091 = 798137) B798137
theorem B1679069 : Blo 195805 1679069 := bstep (se 3 (by rfl) ⟨314825, by rfl⟩ : syracuseStep 1679069 = 629651) B629651
theorem B38969059 : Blo 195805 38969059 := bstep (se 1 (by rfl) ⟨29226794, by rfl⟩ : syracuseStep 38969059 = 58453589) B58453589
theorem B335711 : Blo 195805 335711 := bstep (se 1 (by rfl) ⟨251783, by rfl⟩ : syracuseStep 335711 = 503567) B503567
theorem B336271 : Blo 195805 336271 := bstep (se 1 (by rfl) ⟨252203, by rfl⟩ : syracuseStep 336271 = 504407) B504407
theorem B664199 : Blo 195805 664199 := bstep (se 1 (by rfl) ⟨498149, by rfl⟩ : syracuseStep 664199 = 996299) B996299
theorem B664253 : Blo 195805 664253 := bstep (se 3 (by rfl) ⟨124547, by rfl⟩ : syracuseStep 664253 = 249095) B249095
theorem B402167 : Blo 195805 402167 := bstep (se 1 (by rfl) ⟨301625, by rfl⟩ : syracuseStep 402167 = 603251) B603251
theorem B664415 : Blo 195805 664415 := bstep (se 1 (by rfl) ⟨498311, by rfl⟩ : syracuseStep 664415 = 996623) B996623
theorem B664577 : Blo 195805 664577 := bstep (se 2 (by rfl) ⟨249216, by rfl⟩ : syracuseStep 664577 = 498433) B498433
theorem B336953 : Blo 195805 336953 := bstep (se 2 (by rfl) ⟨126357, by rfl⟩ : syracuseStep 336953 = 252715) B252715
theorem B959683 : Blo 195805 959683 := bstep (se 1 (by rfl) ⟨719762, by rfl⟩ : syracuseStep 959683 = 1439525) B1439525
theorem B1254973 : Blo 195805 1254973 := bstep (se 3 (by rfl) ⟨235307, by rfl⟩ : syracuseStep 1254973 = 470615) B470615
theorem B665387 : Blo 195805 665387 := bstep (se 1 (by rfl) ⟨499040, by rfl⟩ : syracuseStep 665387 = 998081) B998081
theorem B239579 : Blo 195805 239579 := bstep (se 1 (by rfl) ⟨179684, by rfl⟩ : syracuseStep 239579 = 359369) B359369
theorem B665657 : Blo 195805 665657 := bstep (se 2 (by rfl) ⟨249621, by rfl⟩ : syracuseStep 665657 = 499243) B499243
theorem B403553 : Blo 195805 403553 := bstep (se 2 (by rfl) ⟨151332, by rfl⟩ : syracuseStep 403553 = 302665) B302665
theorem B6400133 : Blo 195805 6400133 := bstep (se 4 (by rfl) ⟨600012, by rfl⟩ : syracuseStep 6400133 = 1200025) B1200025
theorem B665981 : Blo 195805 665981 := bstep (se 3 (by rfl) ⟨124871, by rfl⟩ : syracuseStep 665981 = 249743) B249743
theorem B502159 : Blo 195805 502159 := bstep (se 1 (by rfl) ⟨376619, by rfl⟩ : syracuseStep 502159 = 753239) B753239
theorem B666251 : Blo 195805 666251 := bstep (se 1 (by rfl) ⟨499688, by rfl⟩ : syracuseStep 666251 = 999377) B999377
theorem B502483 : Blo 195805 502483 := bstep (se 1 (by rfl) ⟨376862, by rfl⟩ : syracuseStep 502483 = 753725) B753725
theorem B600791 : Blo 195805 600791 := bstep (se 1 (by rfl) ⟨450593, by rfl⟩ : syracuseStep 600791 = 901187) B901187
theorem B9186085 : Blo 195805 9186085 := bstep (se 4 (by rfl) ⟨861195, by rfl⟩ : syracuseStep 9186085 = 1722391) B1722391
theorem B994355 : Blo 195805 994355 := bstep (se 1 (by rfl) ⟨745766, by rfl⟩ : syracuseStep 994355 = 1491533) B1491533
theorem B1256741 : Blo 195805 1256741 := bstep (se 4 (by rfl) ⟨117819, by rfl⟩ : syracuseStep 1256741 = 235639) B235639
theorem B667169 : Blo 195805 667169 := bstep (se 2 (by rfl) ⟨250188, by rfl⟩ : syracuseStep 667169 = 500377) B500377
theorem B1945127 : Blo 195805 1945127 := bstep (se 1 (by rfl) ⟨1458845, by rfl⟩ : syracuseStep 1945127 = 2917691) B2917691
theorem B503435 : Blo 195805 503435 := bstep (se 1 (by rfl) ⟨377576, by rfl⟩ : syracuseStep 503435 = 755153) B755153
theorem B1060499 : Blo 195805 1060499 := bstep (se 1 (by rfl) ⟨795374, by rfl⟩ : syracuseStep 1060499 = 1590749) B1590749
theorem B6368989 : Blo 195805 6368989 := bstep (se 3 (by rfl) ⟨1194185, by rfl⟩ : syracuseStep 6368989 = 2388371) B2388371
theorem B667385 : Blo 195805 667385 := bstep (se 2 (by rfl) ⟨250269, by rfl⟩ : syracuseStep 667385 = 500539) B500539
theorem B667655 : Blo 195805 667655 := bstep (se 1 (by rfl) ⟨500741, by rfl⟩ : syracuseStep 667655 = 1001483) B1001483
theorem B372755 : Blo 195805 372755 := bstep (se 1 (by rfl) ⟨279566, by rfl⟩ : syracuseStep 372755 = 559133) B559133
theorem B667763 : Blo 195805 667763 := bstep (se 1 (by rfl) ⟨500822, by rfl⟩ : syracuseStep 667763 = 1001645) B1001645
theorem B307399 : Blo 195805 307399 := bstep (se 1 (by rfl) ⟨230549, by rfl⟩ : syracuseStep 307399 = 461099) B461099
theorem B3813581 : Blo 195805 3813581 := bstep (se 3 (by rfl) ⟨715046, by rfl⟩ : syracuseStep 3813581 = 1430093) B1430093
theorem B602473 : Blo 195805 602473 := bstep (se 2 (by rfl) ⟨225927, by rfl⟩ : syracuseStep 602473 = 451855) B451855
theorem B668033 : Blo 195805 668033 := bstep (se 2 (by rfl) ⟨250512, by rfl⟩ : syracuseStep 668033 = 501025) B501025
theorem B340519 : Blo 195805 340519 := bstep (se 1 (by rfl) ⟨255389, by rfl⟩ : syracuseStep 340519 = 510779) B510779
theorem B995975 : Blo 195805 995975 := bstep (se 1 (by rfl) ⟨746981, by rfl⟩ : syracuseStep 995975 = 1493963) B1493963
theorem B504569 : Blo 195805 504569 := bstep (se 2 (by rfl) ⟨189213, by rfl⟩ : syracuseStep 504569 = 378427) B378427
theorem B1487645 : Blo 195805 1487645 := bstep (se 3 (by rfl) ⟨278933, by rfl⟩ : syracuseStep 1487645 = 557867) B557867
theorem B1618717 : Blo 195805 1618717 := bstep (se 3 (by rfl) ⟨303509, by rfl⟩ : syracuseStep 1618717 = 607019) B607019
theorem B504751 : Blo 195805 504751 := bstep (se 1 (by rfl) ⟨378563, by rfl⟩ : syracuseStep 504751 = 757127) B757127
theorem B668843 : Blo 195805 668843 := bstep (se 1 (by rfl) ⟨501632, by rfl⟩ : syracuseStep 668843 = 1003265) B1003265
theorem B210119 : Blo 195805 210119 := bstep (se 1 (by rfl) ⟨157589, by rfl⟩ : syracuseStep 210119 = 315179) B315179
theorem B1127627 : Blo 195805 1127627 := bstep (se 1 (by rfl) ⟨845720, by rfl⟩ : syracuseStep 1127627 = 1691441) B1691441
theorem B505217 : Blo 195805 505217 := bstep (se 2 (by rfl) ⟨189456, by rfl⟩ : syracuseStep 505217 = 378913) B378913
theorem B374159 : Blo 195805 374159 := bstep (se 1 (by rfl) ⟨280619, by rfl⟩ : syracuseStep 374159 = 561239) B561239
theorem B374311 : Blo 195805 374311 := bstep (se 1 (by rfl) ⟨280733, by rfl⟩ : syracuseStep 374311 = 561467) B561467
theorem B374395 : Blo 195805 374395 := bstep (se 1 (by rfl) ⟨280796, by rfl⟩ : syracuseStep 374395 = 561593) B561593
theorem B538235 : Blo 195805 538235 := bstep (se 1 (by rfl) ⟨403676, by rfl⟩ : syracuseStep 538235 = 807353) B807353
theorem B669383 : Blo 195805 669383 := bstep (se 1 (by rfl) ⟨502037, by rfl⟩ : syracuseStep 669383 = 1004075) B1004075
theorem B505673 : Blo 195805 505673 := bstep (se 2 (by rfl) ⟨189627, by rfl⟩ : syracuseStep 505673 = 379255) B379255
theorem B1685357 : Blo 195805 1685357 := bstep (se 3 (by rfl) ⟨316004, by rfl⟩ : syracuseStep 1685357 = 632009) B632009
theorem B604091 : Blo 195805 604091 := bstep (se 1 (by rfl) ⟨453068, by rfl⟩ : syracuseStep 604091 = 906137) B906137
theorem B997433 : Blo 195805 997433 := bstep (se 2 (by rfl) ⟨374037, by rfl⟩ : syracuseStep 997433 = 748075) B748075
theorem B374881 : Blo 195805 374881 := bstep (se 2 (by rfl) ⟨140580, by rfl⟩ : syracuseStep 374881 = 281161) B281161
theorem B637085 : Blo 195805 637085 := bstep (se 3 (by rfl) ⟨119453, by rfl⟩ : syracuseStep 637085 = 238907) B238907
theorem B3225757 : Blo 195805 3225757 := bstep (se 3 (by rfl) ⟨604829, by rfl⟩ : syracuseStep 3225757 = 1209659) B1209659
theorem B440567 : Blo 195805 440567 := bstep (se 1 (by rfl) ⟨330425, by rfl⟩ : syracuseStep 440567 = 660851) B660851
theorem B670247 : Blo 195805 670247 := bstep (se 1 (by rfl) ⟨502685, by rfl⟩ : syracuseStep 670247 = 1005371) B1005371
theorem B670355 : Blo 195805 670355 := bstep (se 1 (by rfl) ⟨502766, by rfl⟩ : syracuseStep 670355 = 1005533) B1005533
theorem B539335 : Blo 195805 539335 := bstep (se 1 (by rfl) ⟨404501, by rfl⟩ : syracuseStep 539335 = 809003) B809003
theorem B637739 : Blo 195805 637739 := bstep (se 1 (by rfl) ⟨478304, by rfl⟩ : syracuseStep 637739 = 956609) B956609
theorem B441161 : Blo 195805 441161 := bstep (se 2 (by rfl) ⟨165435, by rfl⟩ : syracuseStep 441161 = 330871) B330871
theorem B670571 : Blo 195805 670571 := bstep (se 1 (by rfl) ⟨502928, by rfl⟩ : syracuseStep 670571 = 1005857) B1005857
theorem B1686419 : Blo 195805 1686419 := bstep (se 1 (by rfl) ⟨1264814, by rfl⟩ : syracuseStep 1686419 = 2529629) B2529629
theorem B670625 : Blo 195805 670625 := bstep (se 2 (by rfl) ⟨251484, by rfl⟩ : syracuseStep 670625 = 502969) B502969
theorem B375815 : Blo 195805 375815 := bstep (se 1 (by rfl) ⟨281861, by rfl⟩ : syracuseStep 375815 = 563723) B563723
theorem B1260791 : Blo 195805 1260791 := bstep (se 1 (by rfl) ⟨945593, by rfl⟩ : syracuseStep 1260791 = 1891187) B1891187
theorem B671219 : Blo 195805 671219 := bstep (se 1 (by rfl) ⟨503414, by rfl⟩ : syracuseStep 671219 = 1006829) B1006829
theorem B376339 : Blo 195805 376339 := bstep (se 1 (by rfl) ⟨282254, by rfl⟩ : syracuseStep 376339 = 564509) B564509
theorem B441953 : Blo 195805 441953 := bstep (se 2 (by rfl) ⟨165732, by rfl⟩ : syracuseStep 441953 = 331465) B331465
theorem B442295 : Blo 195805 442295 := bstep (se 1 (by rfl) ⟨331721, by rfl⟩ : syracuseStep 442295 = 663443) B663443
theorem B1196039 : Blo 195805 1196039 := bstep (se 1 (by rfl) ⟨897029, by rfl⟩ : syracuseStep 1196039 = 1794059) B1794059
theorem B671759 : Blo 195805 671759 := bstep (se 1 (by rfl) ⟨503819, by rfl⟩ : syracuseStep 671759 = 1007639) B1007639
theorem B999539 : Blo 195805 999539 := bstep (se 1 (by rfl) ⟨749654, by rfl⟩ : syracuseStep 999539 = 1499309) B1499309
theorem B442889 : Blo 195805 442889 := bstep (se 2 (by rfl) ⟨166083, by rfl⟩ : syracuseStep 442889 = 332167) B332167
theorem B672353 : Blo 195805 672353 := bstep (se 2 (by rfl) ⟨252132, by rfl⟩ : syracuseStep 672353 = 504265) B504265
theorem B443231 : Blo 195805 443231 := bstep (se 1 (by rfl) ⟨332423, by rfl⟩ : syracuseStep 443231 = 664847) B664847
theorem B443411 : Blo 195805 443411 := bstep (se 1 (by rfl) ⟨332558, by rfl⟩ : syracuseStep 443411 = 665117) B665117
theorem B1492019 : Blo 195805 1492019 := bstep (se 1 (by rfl) ⟨1119014, by rfl⟩ : syracuseStep 1492019 = 2238029) B2238029
theorem B640057 : Blo 195805 640057 := bstep (se 2 (by rfl) ⟨240021, by rfl⟩ : syracuseStep 640057 = 480043) B480043
theorem B2540747 : Blo 195805 2540747 := bstep (se 1 (by rfl) ⟨1905560, by rfl⟩ : syracuseStep 2540747 = 3811121) B3811121
theorem B443753 : Blo 195805 443753 := bstep (se 2 (by rfl) ⟨166407, by rfl⟩ : syracuseStep 443753 = 332815) B332815
theorem B280027 : Blo 195805 280027 := bstep (se 1 (by rfl) ⟨210020, by rfl⟩ : syracuseStep 280027 = 420041) B420041
theorem B509465 : Blo 195805 509465 := bstep (se 2 (by rfl) ⟨191049, by rfl⟩ : syracuseStep 509465 = 382099) B382099
theorem B1001159 : Blo 195805 1001159 := bstep (se 1 (by rfl) ⟨750869, by rfl⟩ : syracuseStep 1001159 = 1501739) B1501739
theorem B476921 : Blo 195805 476921 := bstep (se 2 (by rfl) ⟨178845, by rfl⟩ : syracuseStep 476921 = 357691) B357691
theorem B673579 : Blo 195805 673579 := bstep (se 1 (by rfl) ⟨505184, by rfl⟩ : syracuseStep 673579 = 1010369) B1010369
theorem B6080305 : Blo 195805 6080305 := bstep (se 2 (by rfl) ⟨2280114, by rfl⟩ : syracuseStep 6080305 = 4560229) B4560229
theorem B378731 : Blo 195805 378731 := bstep (se 1 (by rfl) ⟨284048, by rfl⟩ : syracuseStep 378731 = 568097) B568097
theorem B837485 : Blo 195805 837485 := bstep (se 3 (by rfl) ⟨157028, by rfl⟩ : syracuseStep 837485 = 314057) B314057
theorem B477103 : Blo 195805 477103 := bstep (se 1 (by rfl) ⟨357827, by rfl⟩ : syracuseStep 477103 = 715655) B715655
theorem B444347 : Blo 195805 444347 := bstep (se 1 (by rfl) ⟨333260, by rfl⟩ : syracuseStep 444347 = 666521) B666521
theorem B673811 : Blo 195805 673811 := bstep (se 1 (by rfl) ⟨505358, by rfl⟩ : syracuseStep 673811 = 1010717) B1010717
theorem B444473 : Blo 195805 444473 := bstep (se 2 (by rfl) ⟨166677, by rfl⟩ : syracuseStep 444473 = 333355) B333355
theorem B1624369 : Blo 195805 1624369 := bstep (se 2 (by rfl) ⟨609138, by rfl⟩ : syracuseStep 1624369 = 1218277) B1218277
theorem B674135 : Blo 195805 674135 := bstep (se 1 (by rfl) ⟨505601, by rfl⟩ : syracuseStep 674135 = 1011203) B1011203
theorem B444815 : Blo 195805 444815 := bstep (se 1 (by rfl) ⟨333611, by rfl⟩ : syracuseStep 444815 = 667223) B667223
theorem B445139 : Blo 195805 445139 := bstep (se 1 (by rfl) ⟨333854, by rfl⟩ : syracuseStep 445139 = 667709) B667709
theorem B805727 : Blo 195805 805727 := bstep (se 1 (by rfl) ⟨604295, by rfl⟩ : syracuseStep 805727 = 1208591) B1208591
theorem B1264531 : Blo 195805 1264531 := bstep (se 1 (by rfl) ⟨948398, by rfl⟩ : syracuseStep 1264531 = 1896797) B1896797
theorem B805889 : Blo 195805 805889 := bstep (se 2 (by rfl) ⟨302208, by rfl⟩ : syracuseStep 805889 = 604417) B604417
theorem B11455505 : Blo 195805 11455505 := bstep (se 2 (by rfl) ⟨4295814, by rfl⟩ : syracuseStep 11455505 = 8591629) B8591629
theorem B380513 : Blo 195805 380513 := bstep (se 2 (by rfl) ⟨142692, by rfl⟩ : syracuseStep 380513 = 285385) B285385
theorem B446075 : Blo 195805 446075 := bstep (se 1 (by rfl) ⟨334556, by rfl⟩ : syracuseStep 446075 = 669113) B669113
theorem B478919 : Blo 195805 478919 := bstep (se 1 (by rfl) ⟨359189, by rfl⟩ : syracuseStep 478919 = 718379) B718379
theorem B446201 : Blo 195805 446201 := bstep (se 2 (by rfl) ⟨167325, by rfl⟩ : syracuseStep 446201 = 334651) B334651
theorem B446471 : Blo 195805 446471 := bstep (se 1 (by rfl) ⟨334853, by rfl⟩ : syracuseStep 446471 = 669707) B669707
theorem B3821579 : Blo 195805 3821579 := bstep (se 1 (by rfl) ⟨2866184, by rfl⟩ : syracuseStep 3821579 = 5732369) B5732369
theorem B249895 : Blo 195805 249895 := bstep (se 1 (by rfl) ⟨187421, by rfl⟩ : syracuseStep 249895 = 374843) B374843
theorem B446543 : Blo 195805 446543 := bstep (se 1 (by rfl) ⟨334907, by rfl⟩ : syracuseStep 446543 = 669815) B669815
theorem B8605777 : Blo 195805 8605777 := bstep (se 2 (by rfl) ⟨3227166, by rfl⟩ : syracuseStep 8605777 = 6454333) B6454333
theorem B3788977 : Blo 195805 3788977 := bstep (se 2 (by rfl) ⟨1420866, by rfl⟩ : syracuseStep 3788977 = 2841733) B2841733
theorem B250219 : Blo 195805 250219 := bstep (se 1 (by rfl) ⟨187664, by rfl⟩ : syracuseStep 250219 = 375329) B375329
theorem B446939 : Blo 195805 446939 := bstep (se 1 (by rfl) ⟨335204, by rfl⟩ : syracuseStep 446939 = 670409) B670409
theorem B250447 : Blo 195805 250447 := bstep (se 1 (by rfl) ⟨187835, by rfl⟩ : syracuseStep 250447 = 375671) B375671
theorem B316153 : Blo 195805 316153 := bstep (se 2 (by rfl) ⟨118557, by rfl⟩ : syracuseStep 316153 = 237115) B237115
theorem B447407 : Blo 195805 447407 := bstep (se 1 (by rfl) ⟨335555, by rfl⟩ : syracuseStep 447407 = 671111) B671111
theorem B2249693 : Blo 195805 2249693 := bstep (se 3 (by rfl) ⟨421817, by rfl⟩ : syracuseStep 2249693 = 843635) B843635
theorem B2512043 : Blo 195805 2512043 := bstep (se 1 (by rfl) ⟨1884032, by rfl⟩ : syracuseStep 2512043 = 3768065) B3768065
theorem B447659 : Blo 195805 447659 := bstep (se 1 (by rfl) ⟨335744, by rfl⟩ : syracuseStep 447659 = 671489) B671489
theorem B808321 : Blo 195805 808321 := bstep (se 2 (by rfl) ⟨303120, by rfl⟩ : syracuseStep 808321 = 606241) B606241
theorem B710203 : Blo 195805 710203 := bstep (se 1 (by rfl) ⟨532652, by rfl⟩ : syracuseStep 710203 = 1065305) B1065305
theorem B251515 : Blo 195805 251515 := bstep (se 1 (by rfl) ⟨188636, by rfl⟩ : syracuseStep 251515 = 377273) B377273
theorem B448199 : Blo 195805 448199 := bstep (se 1 (by rfl) ⟨336149, by rfl⟩ : syracuseStep 448199 = 672299) B672299
theorem B251743 : Blo 195805 251743 := bstep (se 1 (by rfl) ⟨188807, by rfl⟩ : syracuseStep 251743 = 377615) B377615
theorem B743275 : Blo 195805 743275 := bstep (se 1 (by rfl) ⟨557456, by rfl⟩ : syracuseStep 743275 = 1114913) B1114913
theorem B4315193 : Blo 195805 4315193 := bstep (se 2 (by rfl) ⟨1618197, by rfl⟩ : syracuseStep 4315193 = 3236395) B3236395
theorem B317639 : Blo 195805 317639 := bstep (se 1 (by rfl) ⟨238229, by rfl⟩ : syracuseStep 317639 = 476459) B476459
theorem B1890647 : Blo 195805 1890647 := bstep (se 1 (by rfl) ⟨1417985, by rfl⟩ : syracuseStep 1890647 = 2835971) B2835971
theorem B5757277 : Blo 195805 5757277 := bstep (se 3 (by rfl) ⟨1079489, by rfl⟩ : syracuseStep 5757277 = 2158979) B2158979
theorem B907649 : Blo 195805 907649 := bstep (se 2 (by rfl) ⟨340368, by rfl⟩ : syracuseStep 907649 = 680737) B680737
theorem B1694105 : Blo 195805 1694105 := bstep (se 2 (by rfl) ⟨635289, by rfl⟩ : syracuseStep 1694105 = 1270579) B1270579
theorem B252335 : Blo 195805 252335 := bstep (se 1 (by rfl) ⟨189251, by rfl⟩ : syracuseStep 252335 = 378503) B378503
theorem B317915 : Blo 195805 317915 := bstep (se 1 (by rfl) ⟨238436, by rfl⟩ : syracuseStep 317915 = 476873) B476873
theorem B743975 : Blo 195805 743975 := bstep (se 1 (by rfl) ⟨557981, by rfl⟩ : syracuseStep 743975 = 1115963) B1115963
theorem B449063 : Blo 195805 449063 := bstep (se 1 (by rfl) ⟨336797, by rfl⟩ : syracuseStep 449063 = 673595) B673595
theorem B1071751 : Blo 195805 1071751 := bstep (se 1 (by rfl) ⟨803813, by rfl⟩ : syracuseStep 1071751 = 1607627) B1607627
theorem B449387 : Blo 195805 449387 := bstep (se 1 (by rfl) ⟨337040, by rfl⟩ : syracuseStep 449387 = 674081) B674081
theorem B449441 : Blo 195805 449441 := bstep (se 2 (by rfl) ⟨168540, by rfl⟩ : syracuseStep 449441 = 337081) B337081
theorem B6151247 : Blo 195805 6151247 := bstep (se 1 (by rfl) ⟨4613435, by rfl⟩ : syracuseStep 6151247 = 9226871) B9226871
theorem B1268939 : Blo 195805 1268939 := bstep (se 1 (by rfl) ⟨951704, by rfl⟩ : syracuseStep 1268939 = 1903409) B1903409
theorem B1006991 : Blo 195805 1006991 := bstep (se 1 (by rfl) ⟨755243, by rfl⟩ : syracuseStep 1006991 = 1510487) B1510487
theorem B744947 : Blo 195805 744947 := bstep (se 1 (by rfl) ⟨558710, by rfl⟩ : syracuseStep 744947 = 1117421) B1117421
theorem B220711 : Blo 195805 220711 := bstep (se 1 (by rfl) ⟨165533, by rfl⟩ : syracuseStep 220711 = 331067) B331067
theorem B1596989 : Blo 195805 1596989 := bstep (se 3 (by rfl) ⟨299435, by rfl⟩ : syracuseStep 1596989 = 598871) B598871
theorem B745145 : Blo 195805 745145 := bstep (se 2 (by rfl) ⟨279429, by rfl⟩ : syracuseStep 745145 = 558859) B558859
theorem B745159 : Blo 195805 745159 := bstep (se 1 (by rfl) ⟨558869, by rfl⟩ : syracuseStep 745159 = 1117739) B1117739
theorem B1498823 : Blo 195805 1498823 := bstep (se 1 (by rfl) ⟨1124117, by rfl⟩ : syracuseStep 1498823 = 2248235) B2248235
theorem B680051 : Blo 195805 680051 := bstep (se 1 (by rfl) ⟨510038, by rfl⟩ : syracuseStep 680051 = 1020077) B1020077
theorem B2580659 : Blo 195805 2580659 := bstep (se 1 (by rfl) ⟨1935494, by rfl⟩ : syracuseStep 2580659 = 3870989) B3870989
theorem B746131 : Blo 195805 746131 := bstep (se 1 (by rfl) ⟨559598, by rfl⟩ : syracuseStep 746131 = 1119197) B1119197
theorem B451271 : Blo 195805 451271 := bstep (se 1 (by rfl) ⟨338453, by rfl⟩ : syracuseStep 451271 = 676907) B676907
theorem B5104457 : Blo 195805 5104457 := bstep (se 2 (by rfl) ⟨1914171, by rfl⟩ : syracuseStep 5104457 = 3828343) B3828343
theorem B22438853 : Blo 195805 22438853 := bstep (se 4 (by rfl) ⟨2103642, by rfl⟩ : syracuseStep 22438853 = 4207285) B4207285
theorem B222331 : Blo 195805 222331 := bstep (se 1 (by rfl) ⟨166748, by rfl⟩ : syracuseStep 222331 = 333497) B333497
theorem B1074455 : Blo 195805 1074455 := bstep (se 1 (by rfl) ⟨805841, by rfl⟩ : syracuseStep 1074455 = 1611683) B1611683
theorem B5432741 : Blo 195805 5432741 := bstep (se 4 (by rfl) ⟨509319, by rfl⟩ : syracuseStep 5432741 = 1018639) B1018639
theorem B1009097 : Blo 195805 1009097 := bstep (se 2 (by rfl) ⟨378411, by rfl⟩ : syracuseStep 1009097 = 756823) B756823
theorem B222799 : Blo 195805 222799 := bstep (se 1 (by rfl) ⟨167099, by rfl⟩ : syracuseStep 222799 = 334199) B334199
theorem B1894337 : Blo 195805 1894337 := bstep (se 2 (by rfl) ⟨710376, by rfl⟩ : syracuseStep 1894337 = 1420753) B1420753
theorem B223195 : Blo 195805 223195 := bstep (se 1 (by rfl) ⟨167396, by rfl⟩ : syracuseStep 223195 = 334793) B334793
theorem B419897 : Blo 195805 419897 := bstep (se 2 (by rfl) ⟨157461, by rfl⟩ : syracuseStep 419897 = 314923) B314923
theorem B1206353 : Blo 195805 1206353 := bstep (se 2 (by rfl) ⟨452382, by rfl⟩ : syracuseStep 1206353 = 904765) B904765
theorem B1009745 : Blo 195805 1009745 := bstep (se 2 (by rfl) ⟨378654, by rfl⟩ : syracuseStep 1009745 = 757309) B757309
theorem B1599745 : Blo 195805 1599745 := bstep (se 2 (by rfl) ⟨599904, by rfl⟩ : syracuseStep 1599745 = 1199809) B1199809
theorem B747863 : Blo 195805 747863 := bstep (se 1 (by rfl) ⟨560897, by rfl⟩ : syracuseStep 747863 = 1121795) B1121795
theorem B1141121 : Blo 195805 1141121 := bstep (se 2 (by rfl) ⟨427920, by rfl⟩ : syracuseStep 1141121 = 855841) B855841
theorem B223663 : Blo 195805 223663 := bstep (se 1 (by rfl) ⟨167747, by rfl⟩ : syracuseStep 223663 = 335495) B335495
theorem B224095 : Blo 195805 224095 := bstep (se 1 (by rfl) ⟨168071, by rfl⟩ : syracuseStep 224095 = 336143) B336143
theorem B1207223 : Blo 195805 1207223 := bstep (se 1 (by rfl) ⟨905417, by rfl⟩ : syracuseStep 1207223 = 1810835) B1810835
theorem B224455 : Blo 195805 224455 := bstep (se 1 (by rfl) ⟨168341, by rfl⟩ : syracuseStep 224455 = 336683) B336683
theorem B7597637 : Blo 195805 7597637 := bstep (se 4 (by rfl) ⟨712278, by rfl⟩ : syracuseStep 7597637 = 1424557) B1424557
theorem B945863 : Blo 195805 945863 := bstep (se 1 (by rfl) ⟨709397, by rfl⟩ : syracuseStep 945863 = 1418795) B1418795
theorem B9629603 : Blo 195805 9629603 := bstep (se 1 (by rfl) ⟨7222202, by rfl⟩ : syracuseStep 9629603 = 14444405) B14444405
theorem B1273913 : Blo 195805 1273913 := bstep (se 2 (by rfl) ⟨477717, by rfl⟩ : syracuseStep 1273913 = 955435) B955435
theorem B2683415 : Blo 195805 2683415 := bstep (se 1 (by rfl) ⟨2012561, by rfl⟩ : syracuseStep 2683415 = 4025123) B4025123
theorem B423083 : Blo 195805 423083 := bstep (se 1 (by rfl) ⟨317312, by rfl⟩ : syracuseStep 423083 = 634625) B634625
theorem B750977 : Blo 195805 750977 := bstep (se 2 (by rfl) ⟨281616, by rfl⟩ : syracuseStep 750977 = 563233) B563233
theorem B750991 : Blo 195805 750991 := bstep (se 1 (by rfl) ⟨563243, by rfl⟩ : syracuseStep 750991 = 1126487) B1126487
theorem B1504655 : Blo 195805 1504655 := bstep (se 1 (by rfl) ⟨1128491, by rfl⟩ : syracuseStep 1504655 = 2256983) B2256983
theorem B1340837 : Blo 195805 1340837 := bstep (se 4 (by rfl) ⟨125703, by rfl⟩ : syracuseStep 1340837 = 251407) B251407
theorem B1275911 : Blo 195805 1275911 := bstep (se 1 (by rfl) ⟨956933, by rfl⟩ : syracuseStep 1275911 = 1913867) B1913867
theorem B2521475 : Blo 195805 2521475 := bstep (se 1 (by rfl) ⟨1891106, by rfl⟩ : syracuseStep 2521475 = 3782213) B3782213
theorem B752267 : Blo 195805 752267 := bstep (se 1 (by rfl) ⟨564200, by rfl⟩ : syracuseStep 752267 = 1128401) B1128401
theorem B2849525 : Blo 195805 2849525 := bstep (se 5 (by rfl) ⟨133571, by rfl⟩ : syracuseStep 2849525 = 267143) B267143
theorem B1080067 : Blo 195805 1080067 := bstep (se 1 (by rfl) ⟨810050, by rfl⟩ : syracuseStep 1080067 = 1620101) B1620101
theorem B293807 : Blo 195805 293807 := bstep (se 1 (by rfl) ⟨220355, by rfl⟩ : syracuseStep 293807 = 440711) B440711
theorem B293897 : Blo 195805 293897 := bstep (se 2 (by rfl) ⟨110211, by rfl⟩ : syracuseStep 293897 = 220423) B220423
theorem B293927 : Blo 195805 293927 := bstep (se 1 (by rfl) ⟨220445, by rfl⟩ : syracuseStep 293927 = 440891) B440891
theorem B294011 : Blo 195805 294011 := bstep (se 1 (by rfl) ⟨220508, by rfl⟩ : syracuseStep 294011 = 441017) B441017
theorem B294137 : Blo 195805 294137 := bstep (se 2 (by rfl) ⟨110301, by rfl⟩ : syracuseStep 294137 = 220603) B220603
theorem B195879 : Blo 195805 195879 := bstep (se 1 (by rfl) ⟨146909, by rfl⟩ : syracuseStep 195879 = 293819) B293819
theorem B195919 : Blo 195805 195919 := bstep (se 1 (by rfl) ⟨146939, by rfl⟩ : syracuseStep 195919 = 293879) B293879
theorem B195935 : Blo 195805 195935 := bstep (se 1 (by rfl) ⟨146951, by rfl⟩ : syracuseStep 195935 = 293903) B293903
theorem B294239 : Blo 195805 294239 := bstep (se 1 (by rfl) ⟨220679, by rfl⟩ : syracuseStep 294239 = 441359) B441359
theorem B425321 : Blo 195805 425321 := bstep (se 2 (by rfl) ⟨159495, by rfl⟩ : syracuseStep 425321 = 318991) B318991
theorem B294251 : Blo 195805 294251 := bstep (se 1 (by rfl) ⟨220688, by rfl⟩ : syracuseStep 294251 = 441377) B441377
theorem B195963 : Blo 195805 195963 := bstep (se 1 (by rfl) ⟨146972, by rfl⟩ : syracuseStep 195963 = 293945) B293945
theorem B196015 : Blo 195805 196015 := bstep (se 1 (by rfl) ⟨147011, by rfl⟩ : syracuseStep 196015 = 294023) B294023
theorem B196039 : Blo 195805 196039 := bstep (se 1 (by rfl) ⟨147029, by rfl⟩ : syracuseStep 196039 = 294059) B294059
theorem B196059 : Blo 195805 196059 := bstep (se 1 (by rfl) ⟨147044, by rfl⟩ : syracuseStep 196059 = 294089) B294089
theorem B196135 : Blo 195805 196135 := bstep (se 1 (by rfl) ⟨147101, by rfl⟩ : syracuseStep 196135 = 294203) B294203
theorem B196175 : Blo 195805 196175 := bstep (se 1 (by rfl) ⟨147131, by rfl⟩ : syracuseStep 196175 = 294263) B294263
theorem B294479 : Blo 195805 294479 := bstep (se 1 (by rfl) ⟨220859, by rfl⟩ : syracuseStep 294479 = 441719) B441719
theorem B196191 : Blo 195805 196191 := bstep (se 1 (by rfl) ⟨147143, by rfl⟩ : syracuseStep 196191 = 294287) B294287
theorem B425569 : Blo 195805 425569 := bstep (se 2 (by rfl) ⟨159588, by rfl⟩ : syracuseStep 425569 = 319177) B319177
theorem B196219 : Blo 195805 196219 := bstep (se 1 (by rfl) ⟨147164, by rfl⟩ : syracuseStep 196219 = 294329) B294329
theorem B196271 : Blo 195805 196271 := bstep (se 1 (by rfl) ⟨147203, by rfl⟩ : syracuseStep 196271 = 294407) B294407
theorem B196295 : Blo 195805 196295 := bstep (se 1 (by rfl) ⟨147221, by rfl⟩ : syracuseStep 196295 = 294443) B294443
theorem B294599 : Blo 195805 294599 := bstep (se 1 (by rfl) ⟨220949, by rfl⟩ : syracuseStep 294599 = 441899) B441899
theorem B196315 : Blo 195805 196315 := bstep (se 1 (by rfl) ⟨147236, by rfl⟩ : syracuseStep 196315 = 294473) B294473
theorem B196391 : Blo 195805 196391 := bstep (se 1 (by rfl) ⟨147293, by rfl⟩ : syracuseStep 196391 = 294587) B294587
theorem B196431 : Blo 195805 196431 := bstep (se 1 (by rfl) ⟨147323, by rfl⟩ : syracuseStep 196431 = 294647) B294647
theorem B196447 : Blo 195805 196447 := bstep (se 1 (by rfl) ⟨147335, by rfl⟩ : syracuseStep 196447 = 294671) B294671
theorem B294761 : Blo 195805 294761 := bstep (se 2 (by rfl) ⟨110535, by rfl⟩ : syracuseStep 294761 = 221071) B221071
theorem B196475 : Blo 195805 196475 := bstep (se 1 (by rfl) ⟨147356, by rfl⟩ : syracuseStep 196475 = 294713) B294713
theorem B196527 : Blo 195805 196527 := bstep (se 1 (by rfl) ⟨147395, by rfl⟩ : syracuseStep 196527 = 294791) B294791
theorem B294839 : Blo 195805 294839 := bstep (se 1 (by rfl) ⟨221129, by rfl⟩ : syracuseStep 294839 = 442259) B442259
theorem B425911 : Blo 195805 425911 := bstep (se 1 (by rfl) ⟨319433, by rfl⟩ : syracuseStep 425911 = 638867) B638867
theorem B196551 : Blo 195805 196551 := bstep (se 1 (by rfl) ⟨147413, by rfl⟩ : syracuseStep 196551 = 294827) B294827
theorem B196571 : Blo 195805 196571 := bstep (se 1 (by rfl) ⟨147428, by rfl⟩ : syracuseStep 196571 = 294857) B294857
theorem B294875 : Blo 195805 294875 := bstep (se 1 (by rfl) ⟨221156, by rfl⟩ : syracuseStep 294875 = 442313) B442313
theorem B196895 : Blo 195805 196895 := bstep (se 1 (by rfl) ⟨147671, by rfl⟩ : syracuseStep 196895 = 295343) B295343
theorem B295259 : Blo 195805 295259 := bstep (se 1 (by rfl) ⟨221444, by rfl⟩ : syracuseStep 295259 = 442889) B442889
theorem B196955 : Blo 195805 196955 := bstep (se 1 (by rfl) ⟨147716, by rfl⟩ : syracuseStep 196955 = 295433) B295433
theorem B196975 : Blo 195805 196975 := bstep (se 1 (by rfl) ⟨147731, by rfl⟩ : syracuseStep 196975 = 295463) B295463
theorem B197031 : Blo 195805 197031 := bstep (se 1 (by rfl) ⟨147773, by rfl⟩ : syracuseStep 197031 = 295547) B295547
theorem B197115 : Blo 195805 197115 := bstep (se 1 (by rfl) ⟨147836, by rfl⟩ : syracuseStep 197115 = 295673) B295673
theorem B295487 : Blo 195805 295487 := bstep (se 1 (by rfl) ⟨221615, by rfl⟩ : syracuseStep 295487 = 443231) B443231
theorem B197183 : Blo 195805 197183 := bstep (se 1 (by rfl) ⟨147887, by rfl⟩ : syracuseStep 197183 = 295775) B295775
theorem B197191 : Blo 195805 197191 := bstep (se 1 (by rfl) ⟨147893, by rfl⟩ : syracuseStep 197191 = 295787) B295787
theorem B295607 : Blo 195805 295607 := bstep (se 1 (by rfl) ⟨221705, by rfl⟩ : syracuseStep 295607 = 443411) B443411
theorem B197343 : Blo 195805 197343 := bstep (se 1 (by rfl) ⟨148007, by rfl⟩ : syracuseStep 197343 = 296015) B296015
theorem B197423 : Blo 195805 197423 := bstep (se 1 (by rfl) ⟨148067, by rfl⟩ : syracuseStep 197423 = 296135) B296135
theorem B295835 : Blo 195805 295835 := bstep (se 1 (by rfl) ⟨221876, by rfl⟩ : syracuseStep 295835 = 443753) B443753
theorem B197531 : Blo 195805 197531 := bstep (se 1 (by rfl) ⟨148148, by rfl⟩ : syracuseStep 197531 = 296297) B296297
theorem B197583 : Blo 195805 197583 := bstep (se 1 (by rfl) ⟨148187, by rfl⟩ : syracuseStep 197583 = 296375) B296375
theorem B197607 : Blo 195805 197607 := bstep (se 1 (by rfl) ⟨148205, by rfl⟩ : syracuseStep 197607 = 296411) B296411
theorem B1115279 : Blo 195805 1115279 := bstep (se 1 (by rfl) ⟨836459, by rfl⟩ : syracuseStep 1115279 = 1672919) B1672919
theorem B558323 : Blo 195805 558323 := bstep (se 1 (by rfl) ⟨418742, by rfl⟩ : syracuseStep 558323 = 837485) B837485
theorem B197919 : Blo 195805 197919 := bstep (se 1 (by rfl) ⟨148439, by rfl⟩ : syracuseStep 197919 = 296879) B296879
theorem B296231 : Blo 195805 296231 := bstep (se 1 (by rfl) ⟨222173, by rfl⟩ : syracuseStep 296231 = 444347) B444347
theorem B197979 : Blo 195805 197979 := bstep (se 1 (by rfl) ⟨148484, by rfl⟩ : syracuseStep 197979 = 296969) B296969
theorem B197999 : Blo 195805 197999 := bstep (se 1 (by rfl) ⟨148499, by rfl⟩ : syracuseStep 197999 = 296999) B296999
theorem B296315 : Blo 195805 296315 := bstep (se 1 (by rfl) ⟨222236, by rfl⟩ : syracuseStep 296315 = 444473) B444473
theorem B853409 : Blo 195805 853409 := bstep (se 2 (by rfl) ⟨320028, by rfl⟩ : syracuseStep 853409 = 640057) B640057
theorem B198055 : Blo 195805 198055 := bstep (se 1 (by rfl) ⟨148541, by rfl⟩ : syracuseStep 198055 = 297083) B297083
theorem B296441 : Blo 195805 296441 := bstep (se 2 (by rfl) ⟨111165, by rfl⟩ : syracuseStep 296441 = 222331) B222331
theorem B198139 : Blo 195805 198139 := bstep (se 1 (by rfl) ⟨148604, by rfl⟩ : syracuseStep 198139 = 297209) B297209
theorem B198207 : Blo 195805 198207 := bstep (se 1 (by rfl) ⟨148655, by rfl⟩ : syracuseStep 198207 = 297311) B297311
theorem B198215 : Blo 195805 198215 := bstep (se 1 (by rfl) ⟨148661, by rfl⟩ : syracuseStep 198215 = 297323) B297323
theorem B1279577 : Blo 195805 1279577 := bstep (se 2 (by rfl) ⟨479841, by rfl⟩ : syracuseStep 1279577 = 959683) B959683
theorem B296543 : Blo 195805 296543 := bstep (se 1 (by rfl) ⟨222407, by rfl⟩ : syracuseStep 296543 = 444815) B444815
theorem B198367 : Blo 195805 198367 := bstep (se 1 (by rfl) ⟨148775, by rfl⟩ : syracuseStep 198367 = 297551) B297551
theorem B198447 : Blo 195805 198447 := bstep (se 1 (by rfl) ⟨148835, by rfl⟩ : syracuseStep 198447 = 297671) B297671
theorem B296759 : Blo 195805 296759 := bstep (se 1 (by rfl) ⟨222569, by rfl⟩ : syracuseStep 296759 = 445139) B445139
theorem B198555 : Blo 195805 198555 := bstep (se 1 (by rfl) ⟨148916, by rfl⟩ : syracuseStep 198555 = 297833) B297833
theorem B198607 : Blo 195805 198607 := bstep (se 1 (by rfl) ⟨148955, by rfl⟩ : syracuseStep 198607 = 297911) B297911
theorem B198631 : Blo 195805 198631 := bstep (se 1 (by rfl) ⟨148973, by rfl⟩ : syracuseStep 198631 = 297947) B297947
theorem B4032517 : Blo 195805 4032517 := bstep (se 4 (by rfl) ⟨378048, by rfl⟩ : syracuseStep 4032517 = 756097) B756097
theorem B7637003 : Blo 195805 7637003 := bstep (se 1 (by rfl) ⟨5727752, by rfl⟩ : syracuseStep 7637003 = 11455505) B11455505
theorem B1673297 : Blo 195805 1673297 := bstep (se 2 (by rfl) ⟨627486, by rfl⟩ : syracuseStep 1673297 = 1254973) B1254973
theorem B297065 : Blo 195805 297065 := bstep (se 2 (by rfl) ⟨111399, by rfl⟩ : syracuseStep 297065 = 222799) B222799
theorem B198943 : Blo 195805 198943 := bstep (se 1 (by rfl) ⟨149207, by rfl⟩ : syracuseStep 198943 = 298415) B298415
theorem B199003 : Blo 195805 199003 := bstep (se 1 (by rfl) ⟨149252, by rfl⟩ : syracuseStep 199003 = 298505) B298505
theorem B199023 : Blo 195805 199023 := bstep (se 1 (by rfl) ⟨149267, by rfl⟩ : syracuseStep 199023 = 298535) B298535
theorem B297383 : Blo 195805 297383 := bstep (se 1 (by rfl) ⟨223037, by rfl⟩ : syracuseStep 297383 = 446075) B446075
theorem B199079 : Blo 195805 199079 := bstep (se 1 (by rfl) ⟨149309, by rfl⟩ : syracuseStep 199079 = 298619) B298619
theorem B5507531 : Blo 195805 5507531 := bstep (se 1 (by rfl) ⟨4130648, by rfl⟩ : syracuseStep 5507531 = 8261297) B8261297
theorem B2230739 : Blo 195805 2230739 := bstep (se 1 (by rfl) ⟨1673054, by rfl⟩ : syracuseStep 2230739 = 3346109) B3346109
theorem B297467 : Blo 195805 297467 := bstep (se 1 (by rfl) ⟨223100, by rfl⟩ : syracuseStep 297467 = 446201) B446201
theorem B199163 : Blo 195805 199163 := bstep (se 1 (by rfl) ⟨149372, by rfl⟩ : syracuseStep 199163 = 298745) B298745
theorem B199231 : Blo 195805 199231 := bstep (se 1 (by rfl) ⟨149423, by rfl⟩ : syracuseStep 199231 = 298847) B298847
theorem B199239 : Blo 195805 199239 := bstep (se 1 (by rfl) ⟨149429, by rfl⟩ : syracuseStep 199239 = 298859) B298859
theorem B297593 : Blo 195805 297593 := bstep (se 2 (by rfl) ⟨111597, by rfl⟩ : syracuseStep 297593 = 223195) B223195
theorem B297647 : Blo 195805 297647 := bstep (se 1 (by rfl) ⟨223235, by rfl⟩ : syracuseStep 297647 = 446471) B446471
theorem B297695 : Blo 195805 297695 := bstep (se 1 (by rfl) ⟨223271, by rfl⟩ : syracuseStep 297695 = 446543) B446543
theorem B199391 : Blo 195805 199391 := bstep (se 1 (by rfl) ⟨149543, by rfl⟩ : syracuseStep 199391 = 299087) B299087
theorem B199471 : Blo 195805 199471 := bstep (se 1 (by rfl) ⟨149603, by rfl⟩ : syracuseStep 199471 = 299207) B299207
theorem B199579 : Blo 195805 199579 := bstep (se 1 (by rfl) ⟨149684, by rfl⟩ : syracuseStep 199579 = 299369) B299369
theorem B199631 : Blo 195805 199631 := bstep (se 1 (by rfl) ⟨149723, by rfl⟩ : syracuseStep 199631 = 299447) B299447
theorem B297959 : Blo 195805 297959 := bstep (se 1 (by rfl) ⟨223469, by rfl⟩ : syracuseStep 297959 = 446939) B446939
theorem B199655 : Blo 195805 199655 := bstep (se 1 (by rfl) ⟨149741, by rfl⟩ : syracuseStep 199655 = 299483) B299483
theorem B330743 : Blo 195805 330743 := bstep (se 1 (by rfl) ⟨248057, by rfl⟩ : syracuseStep 330743 = 496115) B496115
theorem B2132993 : Blo 195805 2132993 := bstep (se 2 (by rfl) ⟨799872, by rfl⟩ : syracuseStep 2132993 = 1599745) B1599745
theorem B2165825 : Blo 195805 2165825 := bstep (se 2 (by rfl) ⟨812184, by rfl⟩ : syracuseStep 2165825 = 1624369) B1624369
theorem B560317 : Blo 195805 560317 := bstep (se 3 (by rfl) ⟨105059, by rfl⟩ : syracuseStep 560317 = 210119) B210119
theorem B298217 : Blo 195805 298217 := bstep (se 2 (by rfl) ⟨111831, by rfl⟩ : syracuseStep 298217 = 223663) B223663
theorem B298271 : Blo 195805 298271 := bstep (se 1 (by rfl) ⟨223703, by rfl⟩ : syracuseStep 298271 = 447407) B447407
theorem B1674695 : Blo 195805 1674695 := bstep (se 1 (by rfl) ⟨1256021, by rfl⟩ : syracuseStep 1674695 = 2512043) B2512043
theorem B298439 : Blo 195805 298439 := bstep (se 1 (by rfl) ⟨223829, by rfl⟩ : syracuseStep 298439 = 447659) B447659
theorem B331499 : Blo 195805 331499 := bstep (se 1 (by rfl) ⟨248624, by rfl⟩ : syracuseStep 331499 = 497249) B497249
theorem B298793 : Blo 195805 298793 := bstep (se 2 (by rfl) ⟨112047, by rfl⟩ : syracuseStep 298793 = 224095) B224095
theorem B298799 : Blo 195805 298799 := bstep (se 1 (by rfl) ⟨224099, by rfl⟩ : syracuseStep 298799 = 448199) B448199
theorem B299273 : Blo 195805 299273 := bstep (se 2 (by rfl) ⟨112227, by rfl⟩ : syracuseStep 299273 = 224455) B224455
theorem B495983 : Blo 195805 495983 := bstep (se 1 (by rfl) ⟨371987, by rfl⟩ : syracuseStep 495983 = 743975) B743975
theorem B299375 : Blo 195805 299375 := bstep (se 1 (by rfl) ⟨224531, by rfl⟩ : syracuseStep 299375 = 449063) B449063
theorem B299591 : Blo 195805 299591 := bstep (se 1 (by rfl) ⟨224693, by rfl⟩ : syracuseStep 299591 = 449387) B449387
theorem B299627 : Blo 195805 299627 := bstep (se 1 (by rfl) ⟨224720, by rfl⟩ : syracuseStep 299627 = 449441) B449441
theorem B332471 : Blo 195805 332471 := bstep (se 1 (by rfl) ⟨249353, by rfl⟩ : syracuseStep 332471 = 498707) B498707
theorem B4100831 : Blo 195805 4100831 := bstep (se 1 (by rfl) ⟨3075623, by rfl⟩ : syracuseStep 4100831 = 6151247) B6151247
theorem B8491985 : Blo 195805 8491985 := bstep (se 2 (by rfl) ⟨3184494, by rfl⟩ : syracuseStep 8491985 = 6368989) B6368989
theorem B496631 : Blo 195805 496631 := bstep (se 1 (by rfl) ⟨372473, by rfl⟩ : syracuseStep 496631 = 744947) B744947
theorem B496763 : Blo 195805 496763 := bstep (se 1 (by rfl) ⟨372572, by rfl⟩ : syracuseStep 496763 = 745145) B745145
theorem B1119379 : Blo 195805 1119379 := bstep (se 1 (by rfl) ⟨839534, by rfl⟩ : syracuseStep 1119379 = 1679069) B1679069
theorem B398729 : Blo 195805 398729 := bstep (se 2 (by rfl) ⟨149523, by rfl⟩ : syracuseStep 398729 = 299047) B299047
theorem B333193 : Blo 195805 333193 := bstep (se 2 (by rfl) ⟨124947, by rfl⟩ : syracuseStep 333193 = 249895) B249895
theorem B11474369 : Blo 195805 11474369 := bstep (se 2 (by rfl) ⟨4302888, by rfl⟩ : syracuseStep 11474369 = 8605777) B8605777
theorem B3216941 : Blo 195805 3216941 := bstep (se 3 (by rfl) ⟨603176, by rfl⟩ : syracuseStep 3216941 = 1206353) B1206353
theorem B5051969 : Blo 195805 5051969 := bstep (se 2 (by rfl) ⟨1894488, by rfl⟩ : syracuseStep 5051969 = 3788977) B3788977
theorem B300847 : Blo 195805 300847 := bstep (se 1 (by rfl) ⟨225635, by rfl⟩ : syracuseStep 300847 = 451271) B451271
theorem B333625 : Blo 195805 333625 := bstep (se 2 (by rfl) ⟨125109, by rfl⟩ : syracuseStep 333625 = 250219) B250219
theorem B268111 : Blo 195805 268111 := bstep (se 1 (by rfl) ⟨201083, by rfl⟩ : syracuseStep 268111 = 402167) B402167
theorem B333929 : Blo 195805 333929 := bstep (se 2 (by rfl) ⟨125223, by rfl⟩ : syracuseStep 333929 = 250447) B250447
theorem B661769 : Blo 195805 661769 := bstep (se 2 (by rfl) ⟨248163, by rfl⟩ : syracuseStep 661769 = 496327) B496327
theorem B4266755 : Blo 195805 4266755 := bstep (se 1 (by rfl) ⟨3200066, by rfl⟩ : syracuseStep 4266755 = 6400133) B6400133
theorem B498575 : Blo 195805 498575 := bstep (se 1 (by rfl) ⟨373931, by rfl⟩ : syracuseStep 498575 = 747863) B747863
theorem B760747 : Blo 195805 760747 := bstep (se 1 (by rfl) ⟨570560, by rfl⟩ : syracuseStep 760747 = 1141121) B1141121
theorem B662903 : Blo 195805 662903 := bstep (se 1 (by rfl) ⟨497177, by rfl⟩ : syracuseStep 662903 = 994355) B994355
theorem B499081 : Blo 195805 499081 := bstep (se 2 (by rfl) ⟨187155, by rfl⟩ : syracuseStep 499081 = 374311) B374311
theorem B499193 : Blo 195805 499193 := bstep (se 2 (by rfl) ⟨187197, by rfl⟩ : syracuseStep 499193 = 374395) B374395
theorem B335353 : Blo 195805 335353 := bstep (se 2 (by rfl) ⟨125757, by rfl⟩ : syracuseStep 335353 = 251515) B251515
theorem B335623 : Blo 195805 335623 := bstep (se 1 (by rfl) ⟨251717, by rfl⟩ : syracuseStep 335623 = 503435) B503435
theorem B335657 : Blo 195805 335657 := bstep (se 2 (by rfl) ⟨125871, by rfl⟩ : syracuseStep 335657 = 251743) B251743
theorem B630575 : Blo 195805 630575 := bstep (se 1 (by rfl) ⟨472931, by rfl⟩ : syracuseStep 630575 = 945863) B945863
theorem B991033 : Blo 195805 991033 := bstep (se 2 (by rfl) ⟨371637, by rfl⟩ : syracuseStep 991033 = 743275) B743275
theorem B499841 : Blo 195805 499841 := bstep (se 2 (by rfl) ⟨187440, by rfl⟩ : syracuseStep 499841 = 374881) B374881
theorem B4301009 : Blo 195805 4301009 := bstep (se 2 (by rfl) ⟨1612878, by rfl⟩ : syracuseStep 4301009 = 3225757) B3225757
theorem B663983 : Blo 195805 663983 := bstep (se 1 (by rfl) ⟨497987, by rfl⟩ : syracuseStep 663983 = 995975) B995975
theorem B7676369 : Blo 195805 7676369 := bstep (se 2 (by rfl) ⟨2878638, by rfl⟩ : syracuseStep 7676369 = 5757277) B5757277
theorem B336379 : Blo 195805 336379 := bstep (se 1 (by rfl) ⟨252284, by rfl⟩ : syracuseStep 336379 = 504569) B504569
theorem B991763 : Blo 195805 991763 := bstep (se 1 (by rfl) ⟨743822, by rfl⟩ : syracuseStep 991763 = 1487645) B1487645
theorem B500651 : Blo 195805 500651 := bstep (se 1 (by rfl) ⟨375488, by rfl⟩ : syracuseStep 500651 = 750977) B750977
theorem B336811 : Blo 195805 336811 := bstep (se 1 (by rfl) ⟨252608, by rfl⟩ : syracuseStep 336811 = 505217) B505217
theorem B893891 : Blo 195805 893891 := bstep (se 1 (by rfl) ⟨670418, by rfl⟩ : syracuseStep 893891 = 1340837) B1340837
theorem B337115 : Blo 195805 337115 := bstep (se 1 (by rfl) ⟨252836, by rfl⟩ : syracuseStep 337115 = 505673) B505673
theorem B1123571 : Blo 195805 1123571 := bstep (se 1 (by rfl) ⟨842678, by rfl⟩ : syracuseStep 1123571 = 1685357) B1685357
theorem B402727 : Blo 195805 402727 := bstep (se 1 (by rfl) ⟨302045, by rfl⟩ : syracuseStep 402727 = 604091) B604091
theorem B664955 : Blo 195805 664955 := bstep (se 1 (by rfl) ⟨498716, by rfl⟩ : syracuseStep 664955 = 997433) B997433
theorem B1680983 : Blo 195805 1680983 := bstep (se 1 (by rfl) ⟨1260737, by rfl⟩ : syracuseStep 1680983 = 2521475) B2521475
theorem B2827997 : Blo 195805 2827997 := bstep (se 3 (by rfl) ⟨530249, by rfl⟩ : syracuseStep 2827997 = 1060499) B1060499
theorem B501511 : Blo 195805 501511 := bstep (se 1 (by rfl) ⟨376133, by rfl⟩ : syracuseStep 501511 = 752267) B752267
theorem B1124279 : Blo 195805 1124279 := bstep (se 1 (by rfl) ⟨843209, by rfl⟩ : syracuseStep 1124279 = 1686419) B1686419
theorem B501785 : Blo 195805 501785 := bstep (se 2 (by rfl) ⟨188169, by rfl⟩ : syracuseStep 501785 = 376339) B376339
theorem B567425 : Blo 195805 567425 := bstep (se 2 (by rfl) ⟨212784, by rfl⟩ : syracuseStep 567425 = 425569) B425569
theorem B993545 : Blo 195805 993545 := bstep (se 2 (by rfl) ⟨372579, by rfl⟩ : syracuseStep 993545 = 745159) B745159
theorem B567881 : Blo 195805 567881 := bstep (se 2 (by rfl) ⟨212955, by rfl⟩ : syracuseStep 567881 = 425911) B425911
theorem B797359 : Blo 195805 797359 := bstep (se 1 (by rfl) ⟨598019, by rfl⟩ : syracuseStep 797359 = 1196039) B1196039
theorem B666359 : Blo 195805 666359 := bstep (se 1 (by rfl) ⟨499769, by rfl⟩ : syracuseStep 666359 = 999539) B999539
theorem B961303 : Blo 195805 961303 := bstep (se 1 (by rfl) ⟨720977, by rfl⟩ : syracuseStep 961303 = 1441955) B1441955
theorem B994679 : Blo 195805 994679 := bstep (se 1 (by rfl) ⟨746009, by rfl⟩ : syracuseStep 994679 = 1492019) B1492019
theorem B994841 : Blo 195805 994841 := bstep (se 2 (by rfl) ⟨373065, by rfl⟩ : syracuseStep 994841 = 746131) B746131
theorem B339643 : Blo 195805 339643 := bstep (se 1 (by rfl) ⟨254732, by rfl⟩ : syracuseStep 339643 = 509465) B509465
theorem B2272967 : Blo 195805 2272967 := bstep (se 1 (by rfl) ⟨1704725, by rfl⟩ : syracuseStep 2272967 = 3409451) B3409451
theorem B667439 : Blo 195805 667439 := bstep (se 1 (by rfl) ⟨500579, by rfl⟩ : syracuseStep 667439 = 1001159) B1001159
theorem B503759 : Blo 195805 503759 := bstep (se 1 (by rfl) ⟨377819, by rfl⟩ : syracuseStep 503759 = 755639) B755639
theorem B7155773 : Blo 195805 7155773 := bstep (se 3 (by rfl) ⟨1341707, by rfl⟩ : syracuseStep 7155773 = 2683415) B2683415
theorem B504427 : Blo 195805 504427 := bstep (se 1 (by rfl) ⟨378320, by rfl⟩ : syracuseStep 504427 = 756641) B756641
theorem B373423 : Blo 195805 373423 := bstep (se 1 (by rfl) ⟨280067, by rfl⟩ : syracuseStep 373423 = 560135) B560135
theorem B504731 : Blo 195805 504731 := bstep (se 1 (by rfl) ⟨378548, by rfl⟩ : syracuseStep 504731 = 757097) B757097
theorem B8107073 : Blo 195805 8107073 := bstep (se 2 (by rfl) ⟨3040152, by rfl⟩ : syracuseStep 8107073 = 6080305) B6080305
theorem B636137 : Blo 195805 636137 := bstep (se 2 (by rfl) ⟨238551, by rfl⟩ : syracuseStep 636137 = 477103) B477103
theorem B505075 : Blo 195805 505075 := bstep (se 1 (by rfl) ⟨378806, by rfl⟩ : syracuseStep 505075 = 757613) B757613
theorem B963833 : Blo 195805 963833 := bstep (se 2 (by rfl) ⟨361437, by rfl⟩ : syracuseStep 963833 = 722875) B722875
theorem B669545 : Blo 195805 669545 := bstep (se 2 (by rfl) ⟨251079, by rfl⟩ : syracuseStep 669545 = 502159) B502159
theorem B440585 : Blo 195805 440585 := bstep (se 2 (by rfl) ⟨165219, by rfl⟩ : syracuseStep 440585 = 330439) B330439
theorem B669977 : Blo 195805 669977 := bstep (se 2 (by rfl) ⟨251241, by rfl⟩ : syracuseStep 669977 = 502483) B502483
theorem B375131 : Blo 195805 375131 := bstep (se 1 (by rfl) ⟨281348, by rfl⟩ : syracuseStep 375131 = 562697) B562697
theorem B997757 : Blo 195805 997757 := bstep (se 3 (by rfl) ⟨187079, by rfl⟩ : syracuseStep 997757 = 374159) B374159
theorem B440801 : Blo 195805 440801 := bstep (se 2 (by rfl) ⟨165300, by rfl⟩ : syracuseStep 440801 = 330601) B330601
theorem B1686041 : Blo 195805 1686041 := bstep (se 2 (by rfl) ⟨632265, by rfl⟩ : syracuseStep 1686041 = 1264531) B1264531
theorem B375367 : Blo 195805 375367 := bstep (se 1 (by rfl) ⟨281525, by rfl⟩ : syracuseStep 375367 = 563051) B563051
theorem B441107 : Blo 195805 441107 := bstep (se 1 (by rfl) ⟨330830, by rfl⟩ : syracuseStep 441107 = 661661) B661661
theorem B1260431 : Blo 195805 1260431 := bstep (se 1 (by rfl) ⟨945323, by rfl⟩ : syracuseStep 1260431 = 1890647) B1890647
theorem B605099 : Blo 195805 605099 := bstep (se 1 (by rfl) ⟨453824, by rfl⟩ : syracuseStep 605099 = 907649) B907649
theorem B1129403 : Blo 195805 1129403 := bstep (se 1 (by rfl) ⟨847052, by rfl⟩ : syracuseStep 1129403 = 1694105) B1694105
theorem B211943 : Blo 195805 211943 := bstep (se 1 (by rfl) ⟨158957, by rfl⟩ : syracuseStep 211943 = 317915) B317915
theorem B441467 : Blo 195805 441467 := bstep (se 1 (by rfl) ⟨331100, by rfl⟩ : syracuseStep 441467 = 662201) B662201
theorem B441593 : Blo 195805 441593 := bstep (se 2 (by rfl) ⟨165597, by rfl⟩ : syracuseStep 441593 = 331195) B331195
theorem B376103 : Blo 195805 376103 := bstep (se 1 (by rfl) ⟨282077, by rfl⟩ : syracuseStep 376103 = 564155) B564155
theorem B441737 : Blo 195805 441737 := bstep (se 2 (by rfl) ⟨165651, by rfl⟩ : syracuseStep 441737 = 331303) B331303
theorem B441863 : Blo 195805 441863 := bstep (se 1 (by rfl) ⟨331397, by rfl⟩ : syracuseStep 441863 = 662795) B662795
theorem B671327 : Blo 195805 671327 := bstep (se 1 (by rfl) ⟨503495, by rfl⟩ : syracuseStep 671327 = 1006991) B1006991
theorem B442043 : Blo 195805 442043 := bstep (se 1 (by rfl) ⟨331532, by rfl⟩ : syracuseStep 442043 = 663065) B663065
theorem B1064659 : Blo 195805 1064659 := bstep (se 1 (by rfl) ⟨798494, by rfl⟩ : syracuseStep 1064659 = 1596989) B1596989
theorem B999215 : Blo 195805 999215 := bstep (se 1 (by rfl) ⟨749411, by rfl⟩ : syracuseStep 999215 = 1498823) B1498823
theorem B442169 : Blo 195805 442169 := bstep (se 2 (by rfl) ⟨165813, by rfl⟩ : syracuseStep 442169 = 331627) B331627
theorem B1720439 : Blo 195805 1720439 := bstep (se 1 (by rfl) ⟨1290329, by rfl⟩ : syracuseStep 1720439 = 2580659) B2580659
theorem B409865 : Blo 195805 409865 := bstep (se 2 (by rfl) ⟨153699, by rfl⟩ : syracuseStep 409865 = 307399) B307399
theorem B442799 : Blo 195805 442799 := bstep (se 1 (by rfl) ⟨332099, by rfl⟩ : syracuseStep 442799 = 664199) B664199
theorem B442835 : Blo 195805 442835 := bstep (se 1 (by rfl) ⟨332126, by rfl⟩ : syracuseStep 442835 = 664253) B664253
theorem B803297 : Blo 195805 803297 := bstep (se 2 (by rfl) ⟨301236, by rfl⟩ : syracuseStep 803297 = 602473) B602473
theorem B442943 : Blo 195805 442943 := bstep (se 1 (by rfl) ⟨332207, by rfl⟩ : syracuseStep 442943 = 664415) B664415
theorem B14959235 : Blo 195805 14959235 := bstep (se 1 (by rfl) ⟨11219426, by rfl⟩ : syracuseStep 14959235 = 22438853) B22438853
theorem B443051 : Blo 195805 443051 := bstep (se 1 (by rfl) ⟨332288, by rfl⟩ : syracuseStep 443051 = 664577) B664577
theorem B836513 : Blo 195805 836513 := bstep (se 2 (by rfl) ⟨313692, by rfl⟩ : syracuseStep 836513 = 627385) B627385
theorem B3621827 : Blo 195805 3621827 := bstep (se 1 (by rfl) ⟨2716370, by rfl⟩ : syracuseStep 3621827 = 5432741) B5432741
theorem B672731 : Blo 195805 672731 := bstep (se 1 (by rfl) ⟨504548, by rfl⟩ : syracuseStep 672731 = 1009097) B1009097
theorem B672893 : Blo 195805 672893 := bstep (se 3 (by rfl) ⟨126167, by rfl⟩ : syracuseStep 672893 = 252335) B252335
theorem B443591 : Blo 195805 443591 := bstep (se 1 (by rfl) ⟨332693, by rfl⟩ : syracuseStep 443591 = 665387) B665387
theorem B673001 : Blo 195805 673001 := bstep (se 2 (by rfl) ⟨252375, by rfl⟩ : syracuseStep 673001 = 504751) B504751
theorem B1262891 : Blo 195805 1262891 := bstep (se 1 (by rfl) ⟨947168, by rfl⟩ : syracuseStep 1262891 = 1894337) B1894337
theorem B279931 : Blo 195805 279931 := bstep (se 1 (by rfl) ⟨209948, by rfl⟩ : syracuseStep 279931 = 419897) B419897
theorem B443771 : Blo 195805 443771 := bstep (se 1 (by rfl) ⟨332828, by rfl⟩ : syracuseStep 443771 = 665657) B665657
theorem B673163 : Blo 195805 673163 := bstep (se 1 (by rfl) ⟨504872, by rfl⟩ : syracuseStep 673163 = 1009745) B1009745
theorem B443897 : Blo 195805 443897 := bstep (se 2 (by rfl) ⟨166461, by rfl⟩ : syracuseStep 443897 = 332923) B332923
theorem B443987 : Blo 195805 443987 := bstep (se 1 (by rfl) ⟨332990, by rfl⟩ : syracuseStep 443987 = 665981) B665981
theorem B444167 : Blo 195805 444167 := bstep (se 1 (by rfl) ⟨333125, by rfl⟩ : syracuseStep 444167 = 666251) B666251
theorem B1001321 : Blo 195805 1001321 := bstep (se 2 (by rfl) ⟨375495, by rfl⟩ : syracuseStep 1001321 = 750991) B750991
theorem B804815 : Blo 195805 804815 := bstep (se 1 (by rfl) ⟨603611, by rfl⟩ : syracuseStep 804815 = 1207223) B1207223
theorem B837827 : Blo 195805 837827 := bstep (se 1 (by rfl) ⟨628370, by rfl⟩ : syracuseStep 837827 = 1256741) B1256741
theorem B2148605 : Blo 195805 2148605 := bstep (se 3 (by rfl) ⟨402863, by rfl⟩ : syracuseStep 2148605 = 805727) B805727
theorem B444779 : Blo 195805 444779 := bstep (se 1 (by rfl) ⟨333584, by rfl⟩ : syracuseStep 444779 = 667169) B667169
theorem B1296751 : Blo 195805 1296751 := bstep (se 1 (by rfl) ⟨972563, by rfl⟩ : syracuseStep 1296751 = 1945127) B1945127
theorem B5065091 : Blo 195805 5065091 := bstep (se 1 (by rfl) ⟨3798818, by rfl⟩ : syracuseStep 5065091 = 7597637) B7597637
theorem B1493477 : Blo 195805 1493477 := bstep (se 4 (by rfl) ⟨140013, by rfl⟩ : syracuseStep 1493477 = 280027) B280027
theorem B444923 : Blo 195805 444923 := bstep (se 1 (by rfl) ⟨333692, by rfl⟩ : syracuseStep 444923 = 667385) B667385
theorem B445049 : Blo 195805 445049 := bstep (se 2 (by rfl) ⟨166893, by rfl⟩ : syracuseStep 445049 = 333787) B333787
theorem B2149037 : Blo 195805 2149037 := bstep (se 3 (by rfl) ⟨402944, by rfl⟩ : syracuseStep 2149037 = 805889) B805889
theorem B445103 : Blo 195805 445103 := bstep (se 1 (by rfl) ⟨333827, by rfl⟩ : syracuseStep 445103 = 667655) B667655
theorem B248503 : Blo 195805 248503 := bstep (se 1 (by rfl) ⟨186377, by rfl⟩ : syracuseStep 248503 = 372755) B372755
theorem B445175 : Blo 195805 445175 := bstep (se 1 (by rfl) ⟨333881, by rfl⟩ : syracuseStep 445175 = 667763) B667763
theorem B2542387 : Blo 195805 2542387 := bstep (se 1 (by rfl) ⟨1906790, by rfl⟩ : syracuseStep 2542387 = 3813581) B3813581
theorem B445355 : Blo 195805 445355 := bstep (se 1 (by rfl) ⟨334016, by rfl⟩ : syracuseStep 445355 = 668033) B668033
theorem B282055 : Blo 195805 282055 := bstep (se 1 (by rfl) ⟨211541, by rfl⟩ : syracuseStep 282055 = 423083) B423083
theorem B445895 : Blo 195805 445895 := bstep (se 1 (by rfl) ⟨334421, by rfl⟩ : syracuseStep 445895 = 668843) B668843
theorem B1429001 : Blo 195805 1429001 := bstep (se 2 (by rfl) ⟨535875, by rfl⟩ : syracuseStep 1429001 = 1071751) B1071751
theorem B1003103 : Blo 195805 1003103 := bstep (se 1 (by rfl) ⟨752327, by rfl⟩ : syracuseStep 1003103 = 1504655) B1504655
theorem B446255 : Blo 195805 446255 := bstep (se 1 (by rfl) ⟨334691, by rfl⟩ : syracuseStep 446255 = 669383) B669383
theorem B3592421 : Blo 195805 3592421 := bstep (se 4 (by rfl) ⟨336789, by rfl⟩ : syracuseStep 3592421 = 673579) B673579
theorem B446831 : Blo 195805 446831 := bstep (se 1 (by rfl) ⟨335123, by rfl⟩ : syracuseStep 446831 = 670247) B670247
theorem B446903 : Blo 195805 446903 := bstep (se 1 (by rfl) ⟨335177, by rfl⟩ : syracuseStep 446903 = 670355) B670355
theorem B447047 : Blo 195805 447047 := bstep (se 1 (by rfl) ⟨335285, by rfl⟩ : syracuseStep 447047 = 670571) B670571
theorem B447083 : Blo 195805 447083 := bstep (se 1 (by rfl) ⟨335312, by rfl⟩ : syracuseStep 447083 = 670625) B670625
theorem B250543 : Blo 195805 250543 := bstep (se 1 (by rfl) ⟨187907, by rfl⟩ : syracuseStep 250543 = 375815) B375815
theorem B840527 : Blo 195805 840527 := bstep (se 1 (by rfl) ⟨630395, by rfl⟩ : syracuseStep 840527 = 1260791) B1260791
theorem B283547 : Blo 195805 283547 := bstep (se 1 (by rfl) ⟨212660, by rfl⟩ : syracuseStep 283547 = 425321) B425321
theorem B51958745 : Blo 195805 51958745 := bstep (se 2 (by rfl) ⟨19484529, by rfl⟩ : syracuseStep 51958745 = 38969059) B38969059
theorem B447479 : Blo 195805 447479 := bstep (se 1 (by rfl) ⟨335609, by rfl⟩ : syracuseStep 447479 = 671219) B671219
theorem B447839 : Blo 195805 447839 := bstep (se 1 (by rfl) ⟨335879, by rfl⟩ : syracuseStep 447839 = 671759) B671759
theorem B448235 : Blo 195805 448235 := bstep (se 1 (by rfl) ⟨336176, by rfl⟩ : syracuseStep 448235 = 672353) B672353
theorem B448361 : Blo 195805 448361 := bstep (se 2 (by rfl) ⟨168135, by rfl⟩ : syracuseStep 448361 = 336271) B336271
theorem B1693831 : Blo 195805 1693831 := bstep (se 1 (by rfl) ⟨1270373, by rfl⟩ : syracuseStep 1693831 = 2540747) B2540747
theorem B317947 : Blo 195805 317947 := bstep (se 1 (by rfl) ⟨238460, by rfl⟩ : syracuseStep 317947 = 476921) B476921
theorem B252487 : Blo 195805 252487 := bstep (se 1 (by rfl) ⟨189365, by rfl⟩ : syracuseStep 252487 = 378731) B378731
theorem B449207 : Blo 195805 449207 := bstep (se 1 (by rfl) ⟨336905, by rfl⟩ : syracuseStep 449207 = 673811) B673811
theorem B449423 : Blo 195805 449423 := bstep (se 1 (by rfl) ⟨337067, by rfl⟩ : syracuseStep 449423 = 674135) B674135
theorem B1007315 : Blo 195805 1007315 := bstep (se 1 (by rfl) ⟨755486, by rfl⟩ : syracuseStep 1007315 = 1510973) B1510973
theorem B253675 : Blo 195805 253675 := bstep (se 1 (by rfl) ⟨190256, by rfl⟩ : syracuseStep 253675 = 380513) B380513
theorem B2547719 : Blo 195805 2547719 := bstep (se 1 (by rfl) ⟨1910789, by rfl⟩ : syracuseStep 2547719 = 3821579) B3821579
theorem B1007963 : Blo 195805 1007963 := bstep (se 1 (by rfl) ⟨755972, by rfl⟩ : syracuseStep 1007963 = 1511945) B1511945
theorem B418367 : Blo 195805 418367 := bstep (se 1 (by rfl) ⟨313775, by rfl⟩ : syracuseStep 418367 = 627551) B627551
theorem B221791 : Blo 195805 221791 := bstep (se 1 (by rfl) ⟨166343, by rfl⟩ : syracuseStep 221791 = 332687) B332687
theorem B1499795 : Blo 195805 1499795 := bstep (se 1 (by rfl) ⟨1124846, by rfl⟩ : syracuseStep 1499795 = 2249693) B2249693
theorem B746435 : Blo 195805 746435 := bstep (se 1 (by rfl) ⟨559826, by rfl⟩ : syracuseStep 746435 = 1119653) B1119653
theorem B12248113 : Blo 195805 12248113 := bstep (se 2 (by rfl) ⟨4593042, by rfl⟩ : syracuseStep 12248113 = 9186085) B9186085
theorem B353423 : Blo 195805 353423 := bstep (se 1 (by rfl) ⟨265067, by rfl⟩ : syracuseStep 353423 = 530135) B530135
theorem B943247 : Blo 195805 943247 := bstep (se 1 (by rfl) ⟨707435, by rfl⟩ : syracuseStep 943247 = 1414871) B1414871
theorem B2254067 : Blo 195805 2254067 := bstep (se 1 (by rfl) ⟨1690550, by rfl⟩ : syracuseStep 2254067 = 3381101) B3381101
theorem B1008935 : Blo 195805 1008935 := bstep (se 1 (by rfl) ⟨756701, by rfl⟩ : syracuseStep 1008935 = 1513403) B1513403
theorem B681311 : Blo 195805 681311 := bstep (se 1 (by rfl) ⟨510983, by rfl⟩ : syracuseStep 681311 = 1021967) B1021967
theorem B2876795 : Blo 195805 2876795 := bstep (se 1 (by rfl) ⟨2157596, by rfl⟩ : syracuseStep 2876795 = 4315193) B4315193
theorem B746891 : Blo 195805 746891 := bstep (se 1 (by rfl) ⟨560168, by rfl⟩ : syracuseStep 746891 = 1120337) B1120337
theorem B1009057 : Blo 195805 1009057 := bstep (se 2 (by rfl) ⟨378396, by rfl⟩ : syracuseStep 1009057 = 756793) B756793
theorem B222943 : Blo 195805 222943 := bstep (se 1 (by rfl) ⟨167207, by rfl⟩ : syracuseStep 222943 = 334415) B334415
theorem B845959 : Blo 195805 845959 := bstep (se 1 (by rfl) ⟨634469, by rfl⟩ : syracuseStep 845959 = 1268939) B1268939
theorem B223519 : Blo 195805 223519 := bstep (se 1 (by rfl) ⟨167639, by rfl⟩ : syracuseStep 223519 = 335279) B335279
theorem B223655 : Blo 195805 223655 := bstep (se 1 (by rfl) ⟨167741, by rfl⟩ : syracuseStep 223655 = 335483) B335483
theorem B354727 : Blo 195805 354727 := bstep (se 1 (by rfl) ⟨266045, by rfl⟩ : syracuseStep 354727 = 532091) B532091
theorem B223807 : Blo 195805 223807 := bstep (se 1 (by rfl) ⟨167855, by rfl⟩ : syracuseStep 223807 = 335711) B335711
theorem B453367 : Blo 195805 453367 := bstep (se 1 (by rfl) ⟨340025, by rfl⟩ : syracuseStep 453367 = 680051) B680051
theorem B1076141 : Blo 195805 1076141 := bstep (se 3 (by rfl) ⟨201776, by rfl⟩ : syracuseStep 1076141 = 403553) B403553
theorem B847037 : Blo 195805 847037 := bstep (se 3 (by rfl) ⟨158819, by rfl⟩ : syracuseStep 847037 = 317639) B317639
theorem B3402971 : Blo 195805 3402971 := bstep (se 1 (by rfl) ⟨2552228, by rfl⟩ : syracuseStep 3402971 = 5104457) B5104457
theorem B1011041 : Blo 195805 1011041 := bstep (se 2 (by rfl) ⟨379140, by rfl⟩ : syracuseStep 1011041 = 758281) B758281
theorem B224635 : Blo 195805 224635 := bstep (se 1 (by rfl) ⟨168476, by rfl⟩ : syracuseStep 224635 = 336953) B336953
theorem B454025 : Blo 195805 454025 := bstep (se 2 (by rfl) ⟨170259, by rfl⟩ : syracuseStep 454025 = 340519) B340519
theorem B716303 : Blo 195805 716303 := bstep (se 1 (by rfl) ⟨537227, by rfl⟩ : syracuseStep 716303 = 1074455) B1074455
theorem B421537 : Blo 195805 421537 := bstep (se 2 (by rfl) ⟨158076, by rfl⟩ : syracuseStep 421537 = 316153) B316153
theorem B2158289 : Blo 195805 2158289 := bstep (se 2 (by rfl) ⟨809358, by rfl⟩ : syracuseStep 2158289 = 1618717) B1618717
theorem B1273553 : Blo 195805 1273553 := bstep (se 2 (by rfl) ⟨477582, by rfl⟩ : syracuseStep 1273553 = 955165) B955165
theorem B1503197 : Blo 195805 1503197 := bstep (se 3 (by rfl) ⟨281849, by rfl⟩ : syracuseStep 1503197 = 563699) B563699
theorem B1012193 : Blo 195805 1012193 := bstep (se 2 (by rfl) ⟨379572, by rfl⟩ : syracuseStep 1012193 = 759145) B759145
theorem B1077761 : Blo 195805 1077761 := bstep (se 2 (by rfl) ⟨404160, by rfl⟩ : syracuseStep 1077761 = 808321) B808321
theorem B1602109 : Blo 195805 1602109 := bstep (se 3 (by rfl) ⟨300395, by rfl⟩ : syracuseStep 1602109 = 600791) B600791
theorem B946937 : Blo 195805 946937 := bstep (se 2 (by rfl) ⟨355101, by rfl⟩ : syracuseStep 946937 = 710203) B710203
theorem B6419735 : Blo 195805 6419735 := bstep (se 1 (by rfl) ⟨4814801, by rfl⟩ : syracuseStep 6419735 = 9629603) B9629603
theorem B1144169 : Blo 195805 1144169 := bstep (se 2 (by rfl) ⟨429063, by rfl⟩ : syracuseStep 1144169 = 858127) B858127
theorem B849275 : Blo 195805 849275 := bstep (se 1 (by rfl) ⟨636956, by rfl⟩ : syracuseStep 849275 = 1273913) B1273913
theorem B751751 : Blo 195805 751751 := bstep (se 1 (by rfl) ⟨563813, by rfl⟩ : syracuseStep 751751 = 1127627) B1127627
theorem B719113 : Blo 195805 719113 := bstep (se 2 (by rfl) ⟨269667, by rfl⟩ : syracuseStep 719113 = 539335) B539335
theorem B1440089 : Blo 195805 1440089 := bstep (se 2 (by rfl) ⟨540033, by rfl⟩ : syracuseStep 1440089 = 1080067) B1080067
theorem B358823 : Blo 195805 358823 := bstep (se 1 (by rfl) ⟨269117, by rfl⟩ : syracuseStep 358823 = 538235) B538235
theorem B850607 : Blo 195805 850607 := bstep (se 1 (by rfl) ⟨637955, by rfl⟩ : syracuseStep 850607 = 1275911) B1275911
theorem B424723 : Blo 195805 424723 := bstep (se 1 (by rfl) ⟨318542, by rfl⟩ : syracuseStep 424723 = 637085) B637085
theorem B293711 : Blo 195805 293711 := bstep (se 1 (by rfl) ⟨220283, by rfl⟩ : syracuseStep 293711 = 440567) B440567
theorem B1899683 : Blo 195805 1899683 := bstep (se 1 (by rfl) ⟨1424762, by rfl⟩ : syracuseStep 1899683 = 2849525) B2849525
theorem B1277117 : Blo 195805 1277117 := bstep (se 3 (by rfl) ⟨239459, by rfl⟩ : syracuseStep 1277117 = 478919) B478919
theorem B425159 : Blo 195805 425159 := bstep (se 1 (by rfl) ⟨318869, by rfl⟩ : syracuseStep 425159 = 637739) B637739
theorem B294107 : Blo 195805 294107 := bstep (se 1 (by rfl) ⟨220580, by rfl⟩ : syracuseStep 294107 = 441161) B441161
theorem B195871 : Blo 195805 195871 := bstep (se 1 (by rfl) ⟨146903, by rfl⟩ : syracuseStep 195871 = 293807) B293807
theorem B195931 : Blo 195805 195931 := bstep (se 1 (by rfl) ⟨146948, by rfl⟩ : syracuseStep 195931 = 293897) B293897
theorem B195951 : Blo 195805 195951 := bstep (se 1 (by rfl) ⟨146963, by rfl⟩ : syracuseStep 195951 = 293927) B293927
theorem B294281 : Blo 195805 294281 := bstep (se 2 (by rfl) ⟨110355, by rfl⟩ : syracuseStep 294281 = 220711) B220711
theorem B196007 : Blo 195805 196007 := bstep (se 1 (by rfl) ⟨147005, by rfl⟩ : syracuseStep 196007 = 294011) B294011
theorem B196091 : Blo 195805 196091 := bstep (se 1 (by rfl) ⟨147068, by rfl⟩ : syracuseStep 196091 = 294137) B294137
theorem B196159 : Blo 195805 196159 := bstep (se 1 (by rfl) ⟨147119, by rfl⟩ : syracuseStep 196159 = 294239) B294239
theorem B196167 : Blo 195805 196167 := bstep (se 1 (by rfl) ⟨147125, by rfl⟩ : syracuseStep 196167 = 294251) B294251
theorem B2555509 : Blo 195805 2555509 := bstep (se 5 (by rfl) ⟨119789, by rfl⟩ : syracuseStep 2555509 = 239579) B239579
theorem B196319 : Blo 195805 196319 := bstep (se 1 (by rfl) ⟨147239, by rfl⟩ : syracuseStep 196319 = 294479) B294479
theorem B294635 : Blo 195805 294635 := bstep (se 1 (by rfl) ⟨220976, by rfl⟩ : syracuseStep 294635 = 441953) B441953
theorem B196399 : Blo 195805 196399 := bstep (se 1 (by rfl) ⟨147299, by rfl⟩ : syracuseStep 196399 = 294599) B294599
theorem B196507 : Blo 195805 196507 := bstep (se 1 (by rfl) ⟨147380, by rfl⟩ : syracuseStep 196507 = 294761) B294761
theorem B196559 : Blo 195805 196559 := bstep (se 1 (by rfl) ⟨147419, by rfl⟩ : syracuseStep 196559 = 294839) B294839
theorem B294863 : Blo 195805 294863 := bstep (se 1 (by rfl) ⟨221147, by rfl⟩ : syracuseStep 294863 = 442295) B442295
theorem B196583 : Blo 195805 196583 := bstep (se 1 (by rfl) ⟨147437, by rfl⟩ : syracuseStep 196583 = 294875) B294875
theorem B1146959 : Blo 195805 1146959 := bstep (se 1 (by rfl) ⟨860219, by rfl⟩ : syracuseStep 1146959 = 1720439) B1720439
theorem B196839 : Blo 195805 196839 := bstep (se 1 (by rfl) ⟨147629, by rfl⟩ : syracuseStep 196839 = 295259) B295259
theorem B295199 : Blo 195805 295199 := bstep (se 1 (by rfl) ⟨221399, by rfl⟩ : syracuseStep 295199 = 442799) B442799
theorem B295223 : Blo 195805 295223 := bstep (se 1 (by rfl) ⟨221417, by rfl⟩ : syracuseStep 295223 = 442835) B442835
theorem B295295 : Blo 195805 295295 := bstep (se 1 (by rfl) ⟨221471, by rfl⟩ : syracuseStep 295295 = 442943) B442943
theorem B196991 : Blo 195805 196991 := bstep (se 1 (by rfl) ⟨147743, by rfl⟩ : syracuseStep 196991 = 295487) B295487
theorem B295367 : Blo 195805 295367 := bstep (se 1 (by rfl) ⟨221525, by rfl⟩ : syracuseStep 295367 = 443051) B443051
theorem B197071 : Blo 195805 197071 := bstep (se 1 (by rfl) ⟨147803, by rfl⟩ : syracuseStep 197071 = 295607) B295607
theorem B197223 : Blo 195805 197223 := bstep (se 1 (by rfl) ⟨147917, by rfl⟩ : syracuseStep 197223 = 295835) B295835
theorem B557675 : Blo 195805 557675 := bstep (se 1 (by rfl) ⟨418256, by rfl⟩ : syracuseStep 557675 = 836513) B836513
theorem B295721 : Blo 195805 295721 := bstep (se 2 (by rfl) ⟨110895, by rfl⟩ : syracuseStep 295721 = 221791) B221791
theorem B295727 : Blo 195805 295727 := bstep (se 1 (by rfl) ⟨221795, by rfl⟩ : syracuseStep 295727 = 443591) B443591
theorem B197487 : Blo 195805 197487 := bstep (se 1 (by rfl) ⟨148115, by rfl⟩ : syracuseStep 197487 = 296231) B296231
theorem B295847 : Blo 195805 295847 := bstep (se 1 (by rfl) ⟨221885, by rfl⟩ : syracuseStep 295847 = 443771) B443771
theorem B197543 : Blo 195805 197543 := bstep (se 1 (by rfl) ⟨148157, by rfl⟩ : syracuseStep 197543 = 296315) B296315
theorem B295931 : Blo 195805 295931 := bstep (se 1 (by rfl) ⟨221948, by rfl⟩ : syracuseStep 295931 = 443897) B443897
theorem B197627 : Blo 195805 197627 := bstep (se 1 (by rfl) ⟨148220, by rfl⟩ : syracuseStep 197627 = 296441) B296441
theorem B295991 : Blo 195805 295991 := bstep (se 1 (by rfl) ⟨221993, by rfl⟩ : syracuseStep 295991 = 443987) B443987
theorem B853051 : Blo 195805 853051 := bstep (se 1 (by rfl) ⟨639788, by rfl⟩ : syracuseStep 853051 = 1279577) B1279577
theorem B197695 : Blo 195805 197695 := bstep (se 1 (by rfl) ⟨148271, by rfl⟩ : syracuseStep 197695 = 296543) B296543
theorem B296111 : Blo 195805 296111 := bstep (se 1 (by rfl) ⟨222083, by rfl⟩ : syracuseStep 296111 = 444167) B444167
theorem B197839 : Blo 195805 197839 := bstep (se 1 (by rfl) ⟨148379, by rfl⟩ : syracuseStep 197839 = 296759) B296759
theorem B1115531 : Blo 195805 1115531 := bstep (se 1 (by rfl) ⟨836648, by rfl⟩ : syracuseStep 1115531 = 1673297) B1673297
theorem B198043 : Blo 195805 198043 := bstep (se 1 (by rfl) ⟨148532, by rfl⟩ : syracuseStep 198043 = 297065) B297065
theorem B558551 : Blo 195805 558551 := bstep (se 1 (by rfl) ⟨418913, by rfl⟩ : syracuseStep 558551 = 837827) B837827
theorem B296519 : Blo 195805 296519 := bstep (se 1 (by rfl) ⟨222389, by rfl⟩ : syracuseStep 296519 = 444779) B444779
theorem B3376727 : Blo 195805 3376727 := bstep (se 1 (by rfl) ⟨2532545, by rfl⟩ : syracuseStep 3376727 = 5065091) B5065091
theorem B198255 : Blo 195805 198255 := bstep (se 1 (by rfl) ⟨148691, by rfl⟩ : syracuseStep 198255 = 297383) B297383
theorem B3671687 : Blo 195805 3671687 := bstep (se 1 (by rfl) ⟨2753765, by rfl⟩ : syracuseStep 3671687 = 5507531) B5507531
theorem B296615 : Blo 195805 296615 := bstep (se 1 (by rfl) ⟨222461, by rfl⟩ : syracuseStep 296615 = 444923) B444923
theorem B198311 : Blo 195805 198311 := bstep (se 1 (by rfl) ⟨148733, by rfl⟩ : syracuseStep 198311 = 297467) B297467
theorem B296699 : Blo 195805 296699 := bstep (se 1 (by rfl) ⟨222524, by rfl⟩ : syracuseStep 296699 = 445049) B445049
theorem B198395 : Blo 195805 198395 := bstep (se 1 (by rfl) ⟨148796, by rfl⟩ : syracuseStep 198395 = 297593) B297593
theorem B296735 : Blo 195805 296735 := bstep (se 1 (by rfl) ⟨222551, by rfl⟩ : syracuseStep 296735 = 445103) B445103
theorem B198431 : Blo 195805 198431 := bstep (se 1 (by rfl) ⟨148823, by rfl⟩ : syracuseStep 198431 = 297647) B297647
theorem B198463 : Blo 195805 198463 := bstep (se 1 (by rfl) ⟨148847, by rfl⟩ : syracuseStep 198463 = 297695) B297695
theorem B296783 : Blo 195805 296783 := bstep (se 1 (by rfl) ⟨222587, by rfl⟩ : syracuseStep 296783 = 445175) B445175
theorem B1345409 : Blo 195805 1345409 := bstep (se 2 (by rfl) ⟨504528, by rfl⟩ : syracuseStep 1345409 = 1009057) B1009057
theorem B296903 : Blo 195805 296903 := bstep (se 1 (by rfl) ⟨222677, by rfl⟩ : syracuseStep 296903 = 445355) B445355
theorem B2525165 : Blo 195805 2525165 := bstep (se 3 (by rfl) ⟨473468, by rfl⟩ : syracuseStep 2525165 = 946937) B946937
theorem B198639 : Blo 195805 198639 := bstep (se 1 (by rfl) ⟨148979, by rfl⟩ : syracuseStep 198639 = 297959) B297959
theorem B198811 : Blo 195805 198811 := bstep (se 1 (by rfl) ⟨149108, by rfl⟩ : syracuseStep 198811 = 298217) B298217
theorem B198847 : Blo 195805 198847 := bstep (se 1 (by rfl) ⟨149135, by rfl⟩ : syracuseStep 198847 = 298271) B298271
theorem B297257 : Blo 195805 297257 := bstep (se 2 (by rfl) ⟨111471, by rfl⟩ : syracuseStep 297257 = 222943) B222943
theorem B1116463 : Blo 195805 1116463 := bstep (se 1 (by rfl) ⟨837347, by rfl⟩ : syracuseStep 1116463 = 1674695) B1674695
theorem B297263 : Blo 195805 297263 := bstep (se 1 (by rfl) ⟨222947, by rfl⟩ : syracuseStep 297263 = 445895) B445895
theorem B198959 : Blo 195805 198959 := bstep (se 1 (by rfl) ⟨149219, by rfl⟩ : syracuseStep 198959 = 298439) B298439
theorem B952667 : Blo 195805 952667 := bstep (se 1 (by rfl) ⟨714500, by rfl⟩ : syracuseStep 952667 = 1429001) B1429001
theorem B756125 : Blo 195805 756125 := bstep (se 3 (by rfl) ⟨141773, by rfl⟩ : syracuseStep 756125 = 283547) B283547
theorem B199195 : Blo 195805 199195 := bstep (se 1 (by rfl) ⟨149396, by rfl⟩ : syracuseStep 199195 = 298793) B298793
theorem B297503 : Blo 195805 297503 := bstep (se 1 (by rfl) ⟨223127, by rfl⟩ : syracuseStep 297503 = 446255) B446255
theorem B199199 : Blo 195805 199199 := bstep (se 1 (by rfl) ⟨149399, by rfl⟩ : syracuseStep 199199 = 298799) B298799
theorem B5376689 : Blo 195805 5376689 := bstep (se 2 (by rfl) ⟨2016258, by rfl⟩ : syracuseStep 5376689 = 4032517) B4032517
theorem B2394947 : Blo 195805 2394947 := bstep (se 1 (by rfl) ⟨1796210, by rfl⟩ : syracuseStep 2394947 = 3592421) B3592421
theorem B199515 : Blo 195805 199515 := bstep (se 1 (by rfl) ⟨149636, by rfl⟩ : syracuseStep 199515 = 299273) B299273
theorem B330655 : Blo 195805 330655 := bstep (se 1 (by rfl) ⟨247991, by rfl⟩ : syracuseStep 330655 = 495983) B495983
theorem B297887 : Blo 195805 297887 := bstep (se 1 (by rfl) ⟨223415, by rfl⟩ : syracuseStep 297887 = 446831) B446831
theorem B199583 : Blo 195805 199583 := bstep (se 1 (by rfl) ⟨149687, by rfl⟩ : syracuseStep 199583 = 299375) B299375
theorem B297935 : Blo 195805 297935 := bstep (se 1 (by rfl) ⟨223451, by rfl⟩ : syracuseStep 297935 = 446903) B446903
theorem B298025 : Blo 195805 298025 := bstep (se 2 (by rfl) ⟨111759, by rfl⟩ : syracuseStep 298025 = 223519) B223519
theorem B298031 : Blo 195805 298031 := bstep (se 1 (by rfl) ⟨223523, by rfl⟩ : syracuseStep 298031 = 447047) B447047
theorem B199727 : Blo 195805 199727 := bstep (se 1 (by rfl) ⟨149795, by rfl⟩ : syracuseStep 199727 = 299591) B299591
theorem B298055 : Blo 195805 298055 := bstep (se 1 (by rfl) ⟨223541, by rfl⟩ : syracuseStep 298055 = 447083) B447083
theorem B199751 : Blo 195805 199751 := bstep (se 1 (by rfl) ⟨149813, by rfl⟩ : syracuseStep 199751 = 299627) B299627
theorem B560351 : Blo 195805 560351 := bstep (se 1 (by rfl) ⟨420263, by rfl⟩ : syracuseStep 560351 = 840527) B840527
theorem B34639163 : Blo 195805 34639163 := bstep (se 1 (by rfl) ⟨25979372, by rfl⟩ : syracuseStep 34639163 = 51958745) B51958745
theorem B331087 : Blo 195805 331087 := bstep (se 1 (by rfl) ⟨248315, by rfl⟩ : syracuseStep 331087 = 496631) B496631
theorem B298319 : Blo 195805 298319 := bstep (se 1 (by rfl) ⟨223739, by rfl⟩ : syracuseStep 298319 = 447479) B447479
theorem B331175 : Blo 195805 331175 := bstep (se 1 (by rfl) ⟨248381, by rfl⟩ : syracuseStep 331175 = 496763) B496763
theorem B298409 : Blo 195805 298409 := bstep (se 2 (by rfl) ⟨111903, by rfl⟩ : syracuseStep 298409 = 223807) B223807
theorem B298559 : Blo 195805 298559 := bstep (se 1 (by rfl) ⟨223919, by rfl⟩ : syracuseStep 298559 = 447839) B447839
theorem B331337 : Blo 195805 331337 := bstep (se 2 (by rfl) ⟨124251, by rfl⟩ : syracuseStep 331337 = 248503) B248503
theorem B1281737 : Blo 195805 1281737 := bstep (se 2 (by rfl) ⟨480651, by rfl⟩ : syracuseStep 1281737 = 961303) B961303
theorem B298823 : Blo 195805 298823 := bstep (se 1 (by rfl) ⟨224117, by rfl⟩ : syracuseStep 298823 = 448235) B448235
theorem B298907 : Blo 195805 298907 := bstep (se 1 (by rfl) ⟨224180, by rfl⟩ : syracuseStep 298907 = 448361) B448361
theorem B299471 : Blo 195805 299471 := bstep (se 1 (by rfl) ⟨224603, by rfl⟩ : syracuseStep 299471 = 449207) B449207
theorem B299513 : Blo 195805 299513 := bstep (se 2 (by rfl) ⟨112317, by rfl⟩ : syracuseStep 299513 = 224635) B224635
theorem B332383 : Blo 195805 332383 := bstep (se 1 (by rfl) ⟨249287, by rfl⟩ : syracuseStep 332383 = 498575) B498575
theorem B299615 : Blo 195805 299615 := bstep (se 1 (by rfl) ⟨224711, by rfl⟩ : syracuseStep 299615 = 449423) B449423
theorem B562049 : Blo 195805 562049 := bstep (se 2 (by rfl) ⟨210768, by rfl⟩ : syracuseStep 562049 = 421537) B421537
theorem B332795 : Blo 195805 332795 := bstep (se 1 (by rfl) ⟨249596, by rfl⟩ : syracuseStep 332795 = 499193) B499193
theorem B333227 : Blo 195805 333227 := bstep (se 1 (by rfl) ⟨249920, by rfl⟩ : syracuseStep 333227 = 499841) B499841
theorem B5117579 : Blo 195805 5117579 := bstep (se 1 (by rfl) ⟨3838184, by rfl⟩ : syracuseStep 5117579 = 7676369) B7676369
theorem B661175 : Blo 195805 661175 := bstep (se 1 (by rfl) ⟨495881, by rfl⟩ : syracuseStep 661175 = 991763) B991763
theorem B333767 : Blo 195805 333767 := bstep (se 1 (by rfl) ⟨250325, by rfl⟩ : syracuseStep 333767 = 500651) B500651
theorem B497623 : Blo 195805 497623 := bstep (se 1 (by rfl) ⟨373217, by rfl⟩ : syracuseStep 497623 = 746435) B746435
theorem B595927 : Blo 195805 595927 := bstep (se 1 (by rfl) ⟨446945, by rfl⟩ : syracuseStep 595927 = 893891) B893891
theorem B2136145 : Blo 195805 2136145 := bstep (se 2 (by rfl) ⟨801054, by rfl⟩ : syracuseStep 2136145 = 1602109) B1602109
theorem B628831 : Blo 195805 628831 := bstep (se 1 (by rfl) ⟨471623, by rfl⟩ : syracuseStep 628831 = 943247) B943247
theorem B497897 : Blo 195805 497897 := bstep (se 2 (by rfl) ⟨186711, by rfl⟩ : syracuseStep 497897 = 373423) B373423
theorem B334057 : Blo 195805 334057 := bstep (se 2 (by rfl) ⟨125271, by rfl⟩ : syracuseStep 334057 = 250543) B250543
theorem B497927 : Blo 195805 497927 := bstep (se 1 (by rfl) ⟨373445, by rfl⟩ : syracuseStep 497927 = 746891) B746891
theorem B1120655 : Blo 195805 1120655 := bstep (se 1 (by rfl) ⟨840491, by rfl⟩ : syracuseStep 1120655 = 1680983) B1680983
theorem B596413 : Blo 195805 596413 := bstep (se 3 (by rfl) ⟨111827, by rfl⟩ : syracuseStep 596413 = 223655) B223655
theorem B21142037 : Blo 195805 21142037 := bstep (se 6 (by rfl) ⟨495516, by rfl⟩ : syracuseStep 21142037 = 991033) B991033
theorem B334523 : Blo 195805 334523 := bstep (se 1 (by rfl) ⟨250892, by rfl⟩ : syracuseStep 334523 = 501785) B501785
theorem B662363 : Blo 195805 662363 := bstep (se 1 (by rfl) ⟨496772, by rfl⟩ : syracuseStep 662363 = 993545) B993545
theorem B564691 : Blo 195805 564691 := bstep (se 1 (by rfl) ⟨423518, by rfl⟩ : syracuseStep 564691 = 847037) B847037
theorem B2268647 : Blo 195805 2268647 := bstep (se 1 (by rfl) ⟨1701485, by rfl⟩ : syracuseStep 2268647 = 3402971) B3402971
theorem B663119 : Blo 195805 663119 := bstep (se 1 (by rfl) ⟨497339, by rfl⟩ : syracuseStep 663119 = 994679) B994679
theorem B663227 : Blo 195805 663227 := bstep (se 1 (by rfl) ⟨497420, by rfl⟩ : syracuseStep 663227 = 994841) B994841
theorem B401129 : Blo 195805 401129 := bstep (se 2 (by rfl) ⟨150423, by rfl⟩ : syracuseStep 401129 = 300847) B300847
theorem B1515311 : Blo 195805 1515311 := bstep (se 1 (by rfl) ⟨1136483, by rfl⟩ : syracuseStep 1515311 = 2272967) B2272967
theorem B565181 : Blo 195805 565181 := bstep (se 3 (by rfl) ⟨105971, by rfl⟩ : syracuseStep 565181 = 211943) B211943
theorem B335839 : Blo 195805 335839 := bstep (se 1 (by rfl) ⟨251879, by rfl⟩ : syracuseStep 335839 = 503759) B503759
theorem B5775533 : Blo 195805 5775533 := bstep (se 3 (by rfl) ⟨1082912, by rfl⟩ : syracuseStep 5775533 = 2165825) B2165825
theorem B958817 : Blo 195805 958817 := bstep (se 2 (by rfl) ⟨359556, by rfl⟩ : syracuseStep 958817 = 719113) B719113
theorem B336487 : Blo 195805 336487 := bstep (se 1 (by rfl) ⟨252365, by rfl⟩ : syracuseStep 336487 = 504731) B504731
theorem B500489 : Blo 195805 500489 := bstep (se 2 (by rfl) ⟨187683, by rfl⟩ : syracuseStep 500489 = 375367) B375367
theorem B336649 : Blo 195805 336649 := bstep (se 2 (by rfl) ⟨126243, by rfl⟩ : syracuseStep 336649 = 252487) B252487
theorem B762779 : Blo 195805 762779 := bstep (se 1 (by rfl) ⟨572084, by rfl⟩ : syracuseStep 762779 = 1144169) B1144169
theorem B566183 : Blo 195805 566183 := bstep (se 1 (by rfl) ⟨424637, by rfl⟩ : syracuseStep 566183 = 849275) B849275
theorem B1811429 : Blo 195805 1811429 := bstep (se 4 (by rfl) ⟨169821, by rfl⟩ : syracuseStep 1811429 = 339643) B339643
theorem B566297 : Blo 195805 566297 := bstep (se 2 (by rfl) ⟨212361, by rfl⟩ : syracuseStep 566297 = 424723) B424723
theorem B1352933 : Blo 195805 1352933 := bstep (se 4 (by rfl) ⟨126837, by rfl⟩ : syracuseStep 1352933 = 253675) B253675
theorem B1910141 : Blo 195805 1910141 := bstep (se 3 (by rfl) ⟨358151, by rfl⟩ : syracuseStep 1910141 = 716303) B716303
theorem B501167 : Blo 195805 501167 := bstep (se 1 (by rfl) ⟨375875, by rfl⟩ : syracuseStep 501167 = 751751) B751751
theorem B960059 : Blo 195805 960059 := bstep (se 1 (by rfl) ⟨720044, by rfl⟩ : syracuseStep 960059 = 1440089) B1440089
theorem B665171 : Blo 195805 665171 := bstep (se 1 (by rfl) ⟨498878, by rfl⟩ : syracuseStep 665171 = 997757) B997757
theorem B239215 : Blo 195805 239215 := bstep (se 1 (by rfl) ⟨179411, by rfl⟩ : syracuseStep 239215 = 358823) B358823
theorem B1124027 : Blo 195805 1124027 := bstep (se 1 (by rfl) ⟨843020, by rfl⟩ : syracuseStep 1124027 = 1686041) B1686041
theorem B567071 : Blo 195805 567071 := bstep (se 1 (by rfl) ⟨425303, by rfl⟩ : syracuseStep 567071 = 850607) B850607
theorem B665441 : Blo 195805 665441 := bstep (se 2 (by rfl) ⟨249540, by rfl⟩ : syracuseStep 665441 = 499081) B499081
theorem B403399 : Blo 195805 403399 := bstep (se 1 (by rfl) ⟨302549, by rfl⟩ : syracuseStep 403399 = 605099) B605099
theorem B1419545 : Blo 195805 1419545 := bstep (se 2 (by rfl) ⟨532329, by rfl⟩ : syracuseStep 1419545 = 1064659) B1064659
theorem B666143 : Blo 195805 666143 := bstep (se 1 (by rfl) ⟨499607, by rfl⟩ : syracuseStep 666143 = 999215) B999215
theorem B535531 : Blo 195805 535531 := bstep (se 1 (by rfl) ⟨401648, by rfl⟩ : syracuseStep 535531 = 803297) B803297
theorem B9972823 : Blo 195805 9972823 := bstep (se 1 (by rfl) ⟨7479617, by rfl⟩ : syracuseStep 9972823 = 14959235) B14959235
theorem B1092973 : Blo 195805 1092973 := bstep (se 3 (by rfl) ⟨204932, by rfl⟩ : syracuseStep 1092973 = 409865) B409865
theorem B372215 : Blo 195805 372215 := bstep (se 1 (by rfl) ⟨279161, by rfl⟩ : syracuseStep 372215 = 558323) B558323
theorem B568939 : Blo 195805 568939 := bstep (se 1 (by rfl) ⟨426704, by rfl⟩ : syracuseStep 568939 = 853409) B853409
theorem B667547 : Blo 195805 667547 := bstep (se 1 (by rfl) ⟨500660, by rfl⟩ : syracuseStep 667547 = 1001321) B1001321
theorem B536543 : Blo 195805 536543 := bstep (se 1 (by rfl) ⟨402407, by rfl⟩ : syracuseStep 536543 = 804815) B804815
theorem B5091335 : Blo 195805 5091335 := bstep (se 1 (by rfl) ⟨3818501, by rfl⟩ : syracuseStep 5091335 = 7637003) B7637003
theorem B16330817 : Blo 195805 16330817 := bstep (se 2 (by rfl) ⟨6124056, by rfl⟩ : syracuseStep 16330817 = 12248113) B12248113
theorem B1487159 : Blo 195805 1487159 := bstep (se 1 (by rfl) ⟨1115369, by rfl⟩ : syracuseStep 1487159 = 2230739) B2230739
theorem B995651 : Blo 195805 995651 := bstep (se 1 (by rfl) ⟨746738, by rfl⟩ : syracuseStep 995651 = 1493477) B1493477
theorem B536969 : Blo 195805 536969 := bstep (se 2 (by rfl) ⟨201363, by rfl⟩ : syracuseStep 536969 = 402727) B402727
theorem B373241 : Blo 195805 373241 := bstep (se 2 (by rfl) ⟨139965, by rfl⟩ : syracuseStep 373241 = 279931) B279931
theorem B1421995 : Blo 195805 1421995 := bstep (se 1 (by rfl) ⟨1066496, by rfl⟩ : syracuseStep 1421995 = 2132993) B2132993
theorem B668681 : Blo 195805 668681 := bstep (se 2 (by rfl) ⟨250755, by rfl⟩ : syracuseStep 668681 = 501511) B501511
theorem B668735 : Blo 195805 668735 := bstep (se 1 (by rfl) ⟨501551, by rfl⟩ : syracuseStep 668735 = 1003103) B1003103
theorem B1127945 : Blo 195805 1127945 := bstep (se 2 (by rfl) ⟨422979, by rfl⟩ : syracuseStep 1127945 = 845959) B845959
theorem B2733887 : Blo 195805 2733887 := bstep (se 1 (by rfl) ⟨2050415, by rfl⟩ : syracuseStep 2733887 = 4100831) B4100831
theorem B472969 : Blo 195805 472969 := bstep (se 2 (by rfl) ⟨177363, by rfl⟩ : syracuseStep 472969 = 354727) B354727
theorem B2570221 : Blo 195805 2570221 := bstep (se 3 (by rfl) ⟨481916, by rfl⟩ : syracuseStep 2570221 = 963833) B963833
theorem B1063145 : Blo 195805 1063145 := bstep (se 2 (by rfl) ⟨398679, by rfl⟩ : syracuseStep 1063145 = 797359) B797359
theorem B1816829 : Blo 195805 1816829 := bstep (se 3 (by rfl) ⟨340655, by rfl⟩ : syracuseStep 1816829 = 681311) B681311
theorem B7649579 : Blo 195805 7649579 := bstep (se 1 (by rfl) ⟨5737184, by rfl⟩ : syracuseStep 7649579 = 11474369) B11474369
theorem B1063277 : Blo 195805 1063277 := bstep (se 3 (by rfl) ⟨199364, by rfl⟩ : syracuseStep 1063277 = 398729) B398729
theorem B2144627 : Blo 195805 2144627 := bstep (se 1 (by rfl) ⟨1608470, by rfl⟩ : syracuseStep 2144627 = 3216941) B3216941
theorem B3389849 : Blo 195805 3389849 := bstep (se 2 (by rfl) ⟨1271193, by rfl⟩ : syracuseStep 3389849 = 2542387) B2542387
theorem B441179 : Blo 195805 441179 := bstep (se 1 (by rfl) ⟨330884, by rfl⟩ : syracuseStep 441179 = 661769) B661769
theorem B376073 : Blo 195805 376073 := bstep (se 2 (by rfl) ⟨141027, by rfl⟩ : syracuseStep 376073 = 282055) B282055
theorem B441935 : Blo 195805 441935 := bstep (se 1 (by rfl) ⟨331451, by rfl⟩ : syracuseStep 441935 = 662903) B662903
theorem B671543 : Blo 195805 671543 := bstep (se 1 (by rfl) ⟨503657, by rfl⟩ : syracuseStep 671543 = 1007315) B1007315
theorem B2867339 : Blo 195805 2867339 := bstep (se 1 (by rfl) ⟨2150504, by rfl⟩ : syracuseStep 2867339 = 4301009) B4301009
theorem B671975 : Blo 195805 671975 := bstep (se 1 (by rfl) ⟨503981, by rfl⟩ : syracuseStep 671975 = 1007963) B1007963
theorem B442655 : Blo 195805 442655 := bstep (se 1 (by rfl) ⟨331991, by rfl⟩ : syracuseStep 442655 = 663983) B663983
theorem B278911 : Blo 195805 278911 := bstep (se 1 (by rfl) ⟨209183, by rfl⟩ : syracuseStep 278911 = 418367) B418367
theorem B999863 : Blo 195805 999863 := bstep (se 1 (by rfl) ⟨749897, by rfl⟩ : syracuseStep 999863 = 1499795) B1499795
theorem B672569 : Blo 195805 672569 := bstep (se 2 (by rfl) ⟨252213, by rfl⟩ : syracuseStep 672569 = 504427) B504427
theorem B672623 : Blo 195805 672623 := bstep (se 1 (by rfl) ⟨504467, by rfl⟩ : syracuseStep 672623 = 1008935) B1008935
theorem B1000349 : Blo 195805 1000349 := bstep (se 3 (by rfl) ⟨187565, by rfl⟩ : syracuseStep 1000349 = 375131) B375131
theorem B443303 : Blo 195805 443303 := bstep (se 1 (by rfl) ⟨332477, by rfl⟩ : syracuseStep 443303 = 664955) B664955
theorem B1917863 : Blo 195805 1917863 := bstep (se 1 (by rfl) ⟨1438397, by rfl⟩ : syracuseStep 1917863 = 2876795) B2876795
theorem B1885331 : Blo 195805 1885331 := bstep (se 1 (by rfl) ⟨1413998, by rfl⟩ : syracuseStep 1885331 = 2827997) B2827997
theorem B378283 : Blo 195805 378283 := bstep (se 1 (by rfl) ⟨283712, by rfl⟩ : syracuseStep 378283 = 567425) B567425
theorem B1492505 : Blo 195805 1492505 := bstep (se 2 (by rfl) ⟨559689, by rfl⟩ : syracuseStep 1492505 = 1119379) B1119379
theorem B673433 : Blo 195805 673433 := bstep (se 2 (by rfl) ⟨252537, by rfl⟩ : syracuseStep 673433 = 505075) B505075
theorem B378587 : Blo 195805 378587 := bstep (se 1 (by rfl) ⟨283940, by rfl⟩ : syracuseStep 378587 = 567881) B567881
theorem B444239 : Blo 195805 444239 := bstep (se 1 (by rfl) ⟨333179, by rfl⟩ : syracuseStep 444239 = 666359) B666359
theorem B444257 : Blo 195805 444257 := bstep (se 2 (by rfl) ⟨166596, by rfl⟩ : syracuseStep 444257 = 333193) B333193
theorem B674027 : Blo 195805 674027 := bstep (se 1 (by rfl) ⟨505520, by rfl⟩ : syracuseStep 674027 = 1011041) B1011041
theorem B444833 : Blo 195805 444833 := bstep (se 2 (by rfl) ⟨166812, by rfl⟩ : syracuseStep 444833 = 333625) B333625
theorem B444959 : Blo 195805 444959 := bstep (se 1 (by rfl) ⟨333719, by rfl⟩ : syracuseStep 444959 = 667439) B667439
theorem B1002131 : Blo 195805 1002131 := bstep (se 1 (by rfl) ⟨751598, by rfl⟩ : syracuseStep 1002131 = 1503197) B1503197
theorem B4770515 : Blo 195805 4770515 := bstep (se 1 (by rfl) ⟨3577886, by rfl⟩ : syracuseStep 4770515 = 7155773) B7155773
theorem B674795 : Blo 195805 674795 := bstep (se 1 (by rfl) ⟨506096, by rfl⟩ : syracuseStep 674795 = 1012193) B1012193
theorem B1002941 : Blo 195805 1002941 := bstep (se 3 (by rfl) ⟨188051, by rfl⟩ : syracuseStep 1002941 = 376103) B376103
theorem B4279823 : Blo 195805 4279823 := bstep (se 1 (by rfl) ⟨3209867, by rfl⟩ : syracuseStep 4279823 = 6419735) B6419735
theorem B446363 : Blo 195805 446363 := bstep (se 1 (by rfl) ⟨334772, by rfl⟩ : syracuseStep 446363 = 669545) B669545
theorem B446651 : Blo 195805 446651 := bstep (se 1 (by rfl) ⟨334988, by rfl⟩ : syracuseStep 446651 = 669977) B669977
theorem B840287 : Blo 195805 840287 := bstep (se 1 (by rfl) ⟨630215, by rfl⟩ : syracuseStep 840287 = 1260431) B1260431
theorem B447137 : Blo 195805 447137 := bstep (se 2 (by rfl) ⟨167676, by rfl⟩ : syracuseStep 447137 = 335353) B335353
theorem B1266455 : Blo 195805 1266455 := bstep (se 1 (by rfl) ⟨949841, by rfl⟩ : syracuseStep 1266455 = 1899683) B1899683
theorem B283439 : Blo 195805 283439 := bstep (se 1 (by rfl) ⟨212579, by rfl⟩ : syracuseStep 283439 = 425159) B425159
theorem B447497 : Blo 195805 447497 := bstep (se 2 (by rfl) ⟨167811, by rfl⟩ : syracuseStep 447497 = 335623) B335623
theorem B447551 : Blo 195805 447551 := bstep (se 1 (by rfl) ⟨335663, by rfl⟩ : syracuseStep 447551 = 671327) B671327
theorem B2414551 : Blo 195805 2414551 := bstep (se 1 (by rfl) ⟨1810913, by rfl⟩ : syracuseStep 2414551 = 3621827) B3621827
theorem B448487 : Blo 195805 448487 := bstep (se 1 (by rfl) ⟨336365, by rfl⟩ : syracuseStep 448487 = 672731) B672731
theorem B448505 : Blo 195805 448505 := bstep (se 2 (by rfl) ⟨168189, by rfl⟩ : syracuseStep 448505 = 336379) B336379
theorem B448595 : Blo 195805 448595 := bstep (se 1 (by rfl) ⟨336446, by rfl⟩ : syracuseStep 448595 = 672893) B672893
theorem B743519 : Blo 195805 743519 := bstep (se 1 (by rfl) ⟨557639, by rfl⟩ : syracuseStep 743519 = 1115279) B1115279
theorem B448667 : Blo 195805 448667 := bstep (se 1 (by rfl) ⟨336500, by rfl⟩ : syracuseStep 448667 = 673001) B673001
theorem B841927 : Blo 195805 841927 := bstep (se 1 (by rfl) ⟨631445, by rfl⟩ : syracuseStep 841927 = 1262891) B1262891
theorem B448775 : Blo 195805 448775 := bstep (se 1 (by rfl) ⟨336581, by rfl⟩ : syracuseStep 448775 = 673163) B673163
theorem B449081 : Blo 195805 449081 := bstep (se 2 (by rfl) ⟨168405, by rfl⟩ : syracuseStep 449081 = 336811) B336811
theorem B1432403 : Blo 195805 1432403 := bstep (se 1 (by rfl) ⟨1074302, by rfl⟩ : syracuseStep 1432403 = 2148605) B2148605
theorem B1432691 : Blo 195805 1432691 := bstep (se 1 (by rfl) ⟨1074518, by rfl⟩ : syracuseStep 1432691 = 2149037) B2149037
theorem B220495 : Blo 195805 220495 := bstep (se 1 (by rfl) ⟨165371, by rfl⟩ : syracuseStep 220495 = 330743) B330743
theorem B220999 : Blo 195805 220999 := bstep (se 1 (by rfl) ⟨165749, by rfl⟩ : syracuseStep 220999 = 331499) B331499
theorem B942461 : Blo 195805 942461 := bstep (se 3 (by rfl) ⟨176711, by rfl⟩ : syracuseStep 942461 = 353423) B353423
theorem B221647 : Blo 195805 221647 := bstep (se 1 (by rfl) ⟨166235, by rfl⟩ : syracuseStep 221647 = 332471) B332471
theorem B1729001 : Blo 195805 1729001 := bstep (se 2 (by rfl) ⟨648375, by rfl⟩ : syracuseStep 1729001 = 1296751) B1296751
theorem B5661323 : Blo 195805 5661323 := bstep (se 1 (by rfl) ⟨4245992, by rfl⟩ : syracuseStep 5661323 = 8491985) B8491985
theorem B3367979 : Blo 195805 3367979 := bstep (se 1 (by rfl) ⟨2525984, by rfl⟩ : syracuseStep 3367979 = 5051969) B5051969
theorem B2417957 : Blo 195805 2417957 := bstep (se 4 (by rfl) ⟨226683, by rfl⟩ : syracuseStep 2417957 = 453367) B453367
theorem B222619 : Blo 195805 222619 := bstep (se 1 (by rfl) ⟨166964, by rfl⟩ : syracuseStep 222619 = 333929) B333929
theorem B747089 : Blo 195805 747089 := bstep (se 2 (by rfl) ⟨280158, by rfl⟩ : syracuseStep 747089 = 560317) B560317
theorem B2844503 : Blo 195805 2844503 := bstep (se 1 (by rfl) ⟨2133377, by rfl⟩ : syracuseStep 2844503 = 4266755) B4266755
theorem B223771 : Blo 195805 223771 := bstep (se 1 (by rfl) ⟨167828, by rfl⟩ : syracuseStep 223771 = 335657) B335657
theorem B420383 : Blo 195805 420383 := bstep (se 1 (by rfl) ⟨315287, by rfl⟩ : syracuseStep 420383 = 630575) B630575
theorem B1698479 : Blo 195805 1698479 := bstep (se 1 (by rfl) ⟨1273859, by rfl⟩ : syracuseStep 1698479 = 2547719) B2547719
theorem B224743 : Blo 195805 224743 := bstep (se 1 (by rfl) ⟨168557, by rfl⟩ : syracuseStep 224743 = 337115) B337115
theorem B749047 : Blo 195805 749047 := bstep (se 1 (by rfl) ⟨561785, by rfl⟩ : syracuseStep 749047 = 1123571) B1123571
theorem B1502711 : Blo 195805 1502711 := bstep (se 1 (by rfl) ⟨1127033, by rfl⟩ : syracuseStep 1502711 = 2254067) B2254067
theorem B749519 : Blo 195805 749519 := bstep (se 1 (by rfl) ⟨562139, by rfl⟩ : syracuseStep 749519 = 1124279) B1124279
theorem B717427 : Blo 195805 717427 := bstep (se 1 (by rfl) ⟨538070, by rfl⟩ : syracuseStep 717427 = 1076141) B1076141
theorem B357481 : Blo 195805 357481 := bstep (se 2 (by rfl) ⟨134055, by rfl⟩ : syracuseStep 357481 = 268111) B268111
theorem B1438859 : Blo 195805 1438859 := bstep (se 1 (by rfl) ⟨1079144, by rfl⟩ : syracuseStep 1438859 = 2158289) B2158289
theorem B849035 : Blo 195805 849035 := bstep (se 1 (by rfl) ⟨636776, by rfl⟩ : syracuseStep 849035 = 1273553) B1273553
theorem B2258441 : Blo 195805 2258441 := bstep (se 2 (by rfl) ⟨846915, by rfl⟩ : syracuseStep 2258441 = 1693831) B1693831
theorem B718507 : Blo 195805 718507 := bstep (se 1 (by rfl) ⟨538880, by rfl⟩ : syracuseStep 718507 = 1077761) B1077761
theorem B423929 : Blo 195805 423929 := bstep (se 2 (by rfl) ⟨158973, by rfl⟩ : syracuseStep 423929 = 317947) B317947
theorem B5404715 : Blo 195805 5404715 := bstep (se 1 (by rfl) ⟨4053536, by rfl⟩ : syracuseStep 5404715 = 8107073) B8107073
theorem B424091 : Blo 195805 424091 := bstep (se 1 (by rfl) ⟨318068, by rfl⟩ : syracuseStep 424091 = 636137) B636137
theorem B1210733 : Blo 195805 1210733 := bstep (se 3 (by rfl) ⟨227012, by rfl⟩ : syracuseStep 1210733 = 454025) B454025
theorem B1014329 : Blo 195805 1014329 := bstep (se 2 (by rfl) ⟨380373, by rfl⟩ : syracuseStep 1014329 = 760747) B760747
theorem B293723 : Blo 195805 293723 := bstep (se 1 (by rfl) ⟨220292, by rfl⟩ : syracuseStep 293723 = 440585) B440585
theorem B293867 : Blo 195805 293867 := bstep (se 1 (by rfl) ⟨220400, by rfl⟩ : syracuseStep 293867 = 440801) B440801
theorem B294071 : Blo 195805 294071 := bstep (se 1 (by rfl) ⟨220553, by rfl⟩ : syracuseStep 294071 = 441107) B441107
theorem B195807 : Blo 195805 195807 := bstep (se 1 (by rfl) ⟨146855, by rfl⟩ : syracuseStep 195807 = 293711) B293711
theorem B752935 : Blo 195805 752935 := bstep (se 1 (by rfl) ⟨564701, by rfl⟩ : syracuseStep 752935 = 1129403) B1129403
theorem B294311 : Blo 195805 294311 := bstep (se 1 (by rfl) ⟨220733, by rfl⟩ : syracuseStep 294311 = 441467) B441467
theorem B851411 : Blo 195805 851411 := bstep (se 1 (by rfl) ⟨638558, by rfl⟩ : syracuseStep 851411 = 1277117) B1277117
theorem B196071 : Blo 195805 196071 := bstep (se 1 (by rfl) ⟨147053, by rfl⟩ : syracuseStep 196071 = 294107) B294107
theorem B3407345 : Blo 195805 3407345 := bstep (se 2 (by rfl) ⟨1277754, by rfl⟩ : syracuseStep 3407345 = 2555509) B2555509
theorem B294395 : Blo 195805 294395 := bstep (se 1 (by rfl) ⟨220796, by rfl⟩ : syracuseStep 294395 = 441593) B441593
theorem B196187 : Blo 195805 196187 := bstep (se 1 (by rfl) ⟨147140, by rfl⟩ : syracuseStep 196187 = 294281) B294281
theorem B294491 : Blo 195805 294491 := bstep (se 1 (by rfl) ⟨220868, by rfl⟩ : syracuseStep 294491 = 441737) B441737
theorem B294575 : Blo 195805 294575 := bstep (se 1 (by rfl) ⟨220931, by rfl⟩ : syracuseStep 294575 = 441863) B441863
theorem B294695 : Blo 195805 294695 := bstep (se 1 (by rfl) ⟨221021, by rfl⟩ : syracuseStep 294695 = 442043) B442043
theorem B196423 : Blo 195805 196423 := bstep (se 1 (by rfl) ⟨147317, by rfl⟩ : syracuseStep 196423 = 294635) B294635
theorem B294779 : Blo 195805 294779 := bstep (se 1 (by rfl) ⟨221084, by rfl⟩ : syracuseStep 294779 = 442169) B442169
theorem B196575 : Blo 195805 196575 := bstep (se 1 (by rfl) ⟨147431, by rfl⟩ : syracuseStep 196575 = 294863) B294863
theorem B295103 : Blo 195805 295103 := bstep (se 1 (by rfl) ⟨221327, by rfl⟩ : syracuseStep 295103 = 442655) B442655
theorem B196799 : Blo 195805 196799 := bstep (se 1 (by rfl) ⟨147599, by rfl⟩ : syracuseStep 196799 = 295199) B295199
theorem B196815 : Blo 195805 196815 := bstep (se 1 (by rfl) ⟨147611, by rfl⟩ : syracuseStep 196815 = 295223) B295223
theorem B196863 : Blo 195805 196863 := bstep (se 1 (by rfl) ⟨147647, by rfl⟩ : syracuseStep 196863 = 295295) B295295
theorem B196911 : Blo 195805 196911 := bstep (se 1 (by rfl) ⟨147683, by rfl⟩ : syracuseStep 196911 = 295367) B295367
theorem B197147 : Blo 195805 197147 := bstep (se 1 (by rfl) ⟨147860, by rfl⟩ : syracuseStep 197147 = 295721) B295721
theorem B197151 : Blo 195805 197151 := bstep (se 1 (by rfl) ⟨147863, by rfl⟩ : syracuseStep 197151 = 295727) B295727
theorem B295529 : Blo 195805 295529 := bstep (se 2 (by rfl) ⟨110823, by rfl⟩ : syracuseStep 295529 = 221647) B221647
theorem B295535 : Blo 195805 295535 := bstep (se 1 (by rfl) ⟨221651, by rfl⟩ : syracuseStep 295535 = 443303) B443303
theorem B197231 : Blo 195805 197231 := bstep (se 1 (by rfl) ⟨147923, by rfl⟩ : syracuseStep 197231 = 295847) B295847
theorem B1278575 : Blo 195805 1278575 := bstep (se 1 (by rfl) ⟨958931, by rfl⟩ : syracuseStep 1278575 = 1917863) B1917863
theorem B197287 : Blo 195805 197287 := bstep (se 1 (by rfl) ⟨147965, by rfl⟩ : syracuseStep 197287 = 295931) B295931
theorem B197327 : Blo 195805 197327 := bstep (se 1 (by rfl) ⟨147995, by rfl⟩ : syracuseStep 197327 = 295991) B295991
theorem B197407 : Blo 195805 197407 := bstep (se 1 (by rfl) ⟨148055, by rfl⟩ : syracuseStep 197407 = 296111) B296111
theorem B2556845 : Blo 195805 2556845 := bstep (se 3 (by rfl) ⟨479408, by rfl⟩ : syracuseStep 2556845 = 958817) B958817
theorem B197679 : Blo 195805 197679 := bstep (se 1 (by rfl) ⟨148259, by rfl⟩ : syracuseStep 197679 = 296519) B296519
theorem B197743 : Blo 195805 197743 := bstep (se 1 (by rfl) ⟨148307, by rfl⟩ : syracuseStep 197743 = 296615) B296615
theorem B197799 : Blo 195805 197799 := bstep (se 1 (by rfl) ⟨148349, by rfl⟩ : syracuseStep 197799 = 296699) B296699
theorem B197823 : Blo 195805 197823 := bstep (se 1 (by rfl) ⟨148367, by rfl⟩ : syracuseStep 197823 = 296735) B296735
theorem B296159 : Blo 195805 296159 := bstep (se 1 (by rfl) ⟨222119, by rfl⟩ : syracuseStep 296159 = 444239) B444239
theorem B197855 : Blo 195805 197855 := bstep (se 1 (by rfl) ⟨148391, by rfl⟩ : syracuseStep 197855 = 296783) B296783
theorem B296171 : Blo 195805 296171 := bstep (se 1 (by rfl) ⟨222128, by rfl⟩ : syracuseStep 296171 = 444257) B444257
theorem B197935 : Blo 195805 197935 := bstep (se 1 (by rfl) ⟨148451, by rfl⟩ : syracuseStep 197935 = 296903) B296903
theorem B198171 : Blo 195805 198171 := bstep (se 1 (by rfl) ⟨148628, by rfl⟩ : syracuseStep 198171 = 297257) B297257
theorem B198175 : Blo 195805 198175 := bstep (se 1 (by rfl) ⟨148631, by rfl⟩ : syracuseStep 198175 = 297263) B297263
theorem B296555 : Blo 195805 296555 := bstep (se 1 (by rfl) ⟨222416, by rfl⟩ : syracuseStep 296555 = 444833) B444833
theorem B296639 : Blo 195805 296639 := bstep (se 1 (by rfl) ⟨222479, by rfl⟩ : syracuseStep 296639 = 444959) B444959
theorem B198335 : Blo 195805 198335 := bstep (se 1 (by rfl) ⟨148751, by rfl⟩ : syracuseStep 198335 = 297503) B297503
theorem B3180343 : Blo 195805 3180343 := bstep (se 1 (by rfl) ⟨2385257, by rfl⟩ : syracuseStep 3180343 = 4770515) B4770515
theorem B296825 : Blo 195805 296825 := bstep (se 2 (by rfl) ⟨111309, by rfl⟩ : syracuseStep 296825 = 222619) B222619
theorem B198591 : Blo 195805 198591 := bstep (se 1 (by rfl) ⟨148943, by rfl⟩ : syracuseStep 198591 = 297887) B297887
theorem B198623 : Blo 195805 198623 := bstep (se 1 (by rfl) ⟨148967, by rfl⟩ : syracuseStep 198623 = 297935) B297935
theorem B198683 : Blo 195805 198683 := bstep (se 1 (by rfl) ⟨149012, by rfl⟩ : syracuseStep 198683 = 298025) B298025
theorem B198687 : Blo 195805 198687 := bstep (se 1 (by rfl) ⟨149015, by rfl⟩ : syracuseStep 198687 = 298031) B298031
theorem B198703 : Blo 195805 198703 := bstep (se 1 (by rfl) ⟨149027, by rfl⟩ : syracuseStep 198703 = 298055) B298055
theorem B755837 : Blo 195805 755837 := bstep (se 3 (by rfl) ⟨141719, by rfl⟩ : syracuseStep 755837 = 283439) B283439
theorem B198879 : Blo 195805 198879 := bstep (se 1 (by rfl) ⟨149159, by rfl⟩ : syracuseStep 198879 = 298319) B298319
theorem B198939 : Blo 195805 198939 := bstep (se 1 (by rfl) ⟨149204, by rfl⟩ : syracuseStep 198939 = 298409) B298409
theorem B3180869 : Blo 195805 3180869 := bstep (se 4 (by rfl) ⟨298206, by rfl⟩ : syracuseStep 3180869 = 596413) B596413
theorem B2853215 : Blo 195805 2853215 := bstep (se 1 (by rfl) ⟨2139911, by rfl⟩ : syracuseStep 2853215 = 4279823) B4279823
theorem B199039 : Blo 195805 199039 := bstep (se 1 (by rfl) ⟨149279, by rfl⟩ : syracuseStep 199039 = 298559) B298559
theorem B2034077 : Blo 195805 2034077 := bstep (se 3 (by rfl) ⟨381389, by rfl⟩ : syracuseStep 2034077 = 762779) B762779
theorem B854491 : Blo 195805 854491 := bstep (se 1 (by rfl) ⟨640868, by rfl⟩ : syracuseStep 854491 = 1281737) B1281737
theorem B199215 : Blo 195805 199215 := bstep (se 1 (by rfl) ⟨149411, by rfl⟩ : syracuseStep 199215 = 298823) B298823
theorem B297575 : Blo 195805 297575 := bstep (se 1 (by rfl) ⟨223181, by rfl⟩ : syracuseStep 297575 = 446363) B446363
theorem B199271 : Blo 195805 199271 := bstep (se 1 (by rfl) ⟨149453, by rfl⟩ : syracuseStep 199271 = 298907) B298907
theorem B297767 : Blo 195805 297767 := bstep (se 1 (by rfl) ⟨223325, by rfl⟩ : syracuseStep 297767 = 446651) B446651
theorem B199647 : Blo 195805 199647 := bstep (se 1 (by rfl) ⟨149735, by rfl⟩ : syracuseStep 199647 = 299471) B299471
theorem B199675 : Blo 195805 199675 := bstep (se 1 (by rfl) ⟨149756, by rfl⟩ : syracuseStep 199675 = 299513) B299513
theorem B560191 : Blo 195805 560191 := bstep (se 1 (by rfl) ⟨420143, by rfl⟩ : syracuseStep 560191 = 840287) B840287
theorem B199743 : Blo 195805 199743 := bstep (se 1 (by rfl) ⟨149807, by rfl⟩ : syracuseStep 199743 = 299615) B299615
theorem B298091 : Blo 195805 298091 := bstep (se 1 (by rfl) ⟨223568, by rfl⟩ : syracuseStep 298091 = 447137) B447137
theorem B298331 : Blo 195805 298331 := bstep (se 1 (by rfl) ⟨223748, by rfl⟩ : syracuseStep 298331 = 447497) B447497
theorem B298361 : Blo 195805 298361 := bstep (se 2 (by rfl) ⟨111885, by rfl⟩ : syracuseStep 298361 = 223771) B223771
theorem B298367 : Blo 195805 298367 := bstep (se 1 (by rfl) ⟨223775, by rfl⟩ : syracuseStep 298367 = 447551) B447551
theorem B3411719 : Blo 195805 3411719 := bstep (se 1 (by rfl) ⟨2558789, by rfl⟩ : syracuseStep 3411719 = 5117579) B5117579
theorem B298991 : Blo 195805 298991 := bstep (se 1 (by rfl) ⟨224243, by rfl⟩ : syracuseStep 298991 = 448487) B448487
theorem B299003 : Blo 195805 299003 := bstep (se 1 (by rfl) ⟨224252, by rfl⟩ : syracuseStep 299003 = 448505) B448505
theorem B299063 : Blo 195805 299063 := bstep (se 1 (by rfl) ⟨224297, by rfl⟩ : syracuseStep 299063 = 448595) B448595
theorem B495679 : Blo 195805 495679 := bstep (se 1 (by rfl) ⟨371759, by rfl⟩ : syracuseStep 495679 = 743519) B743519
theorem B299111 : Blo 195805 299111 := bstep (se 1 (by rfl) ⟨224333, by rfl⟩ : syracuseStep 299111 = 448667) B448667
theorem B331931 : Blo 195805 331931 := bstep (se 1 (by rfl) ⟨248948, by rfl⟩ : syracuseStep 331931 = 497897) B497897
theorem B2560157 : Blo 195805 2560157 := bstep (se 3 (by rfl) ⟨480029, by rfl⟩ : syracuseStep 2560157 = 960059) B960059
theorem B331951 : Blo 195805 331951 := bstep (se 1 (by rfl) ⟨248963, by rfl⟩ : syracuseStep 331951 = 497927) B497927
theorem B299183 : Blo 195805 299183 := bstep (se 1 (by rfl) ⟨224387, by rfl⟩ : syracuseStep 299183 = 448775) B448775
theorem B14094691 : Blo 195805 14094691 := bstep (se 1 (by rfl) ⟨10571018, by rfl⟩ : syracuseStep 14094691 = 21142037) B21142037
theorem B299387 : Blo 195805 299387 := bstep (se 1 (by rfl) ⟨224540, by rfl⟩ : syracuseStep 299387 = 449081) B449081
theorem B954935 : Blo 195805 954935 := bstep (se 1 (by rfl) ⟨716201, by rfl⟩ : syracuseStep 954935 = 1432403) B1432403
theorem B299657 : Blo 195805 299657 := bstep (se 2 (by rfl) ⟨112371, by rfl⟩ : syracuseStep 299657 = 224743) B224743
theorem B955127 : Blo 195805 955127 := bstep (se 1 (by rfl) ⟨716345, by rfl⟩ : syracuseStep 955127 = 1432691) B1432691
theorem B758585 : Blo 195805 758585 := bstep (se 2 (by rfl) ⟨284469, by rfl⟩ : syracuseStep 758585 = 568939) B568939
theorem B1512431 : Blo 195805 1512431 := bstep (se 1 (by rfl) ⟨1134323, by rfl⟩ : syracuseStep 1512431 = 2268647) B2268647
theorem B267419 : Blo 195805 267419 := bstep (se 1 (by rfl) ⟨200564, by rfl⟩ : syracuseStep 267419 = 401129) B401129
theorem B628307 : Blo 195805 628307 := bstep (se 1 (by rfl) ⟨471230, by rfl⟩ : syracuseStep 628307 = 942461) B942461
theorem B1152667 : Blo 195805 1152667 := bstep (se 1 (by rfl) ⟨864500, by rfl⟩ : syracuseStep 1152667 = 1729001) B1729001
theorem B3774215 : Blo 195805 3774215 := bstep (se 1 (by rfl) ⟨2830661, by rfl⟩ : syracuseStep 3774215 = 5661323) B5661323
theorem B333659 : Blo 195805 333659 := bstep (se 1 (by rfl) ⟨250244, by rfl⟩ : syracuseStep 333659 = 500489) B500489
theorem B956569 : Blo 195805 956569 := bstep (se 2 (by rfl) ⟨358713, by rfl⟩ : syracuseStep 956569 = 717427) B717427
theorem B1611971 : Blo 195805 1611971 := bstep (se 1 (by rfl) ⟨1208978, by rfl⟩ : syracuseStep 1611971 = 2417957) B2417957
theorem B334111 : Blo 195805 334111 := bstep (se 1 (by rfl) ⟨250583, by rfl⟩ : syracuseStep 334111 = 501167) B501167
theorem B498059 : Blo 195805 498059 := bstep (se 1 (by rfl) ⟨373544, by rfl⟩ : syracuseStep 498059 = 747089) B747089
theorem B958009 : Blo 195805 958009 := bstep (se 2 (by rfl) ⟨359253, by rfl⟩ : syracuseStep 958009 = 718507) B718507
theorem B3219401 : Blo 195805 3219401 := bstep (se 2 (by rfl) ⟨1207275, by rfl⟩ : syracuseStep 3219401 = 2414551) B2414551
theorem B794569 : Blo 195805 794569 := bstep (se 2 (by rfl) ⟨297963, by rfl⟩ : syracuseStep 794569 = 595927) B595927
theorem B663497 : Blo 195805 663497 := bstep (se 2 (by rfl) ⟨248811, by rfl⟩ : syracuseStep 663497 = 497623) B497623
theorem B499679 : Blo 195805 499679 := bstep (se 1 (by rfl) ⟨374759, by rfl⟩ : syracuseStep 499679 = 749519) B749519
theorem B10887211 : Blo 195805 10887211 := bstep (se 1 (by rfl) ⟨8165408, by rfl⟩ : syracuseStep 10887211 = 16330817) B16330817
theorem B991439 : Blo 195805 991439 := bstep (se 1 (by rfl) ⟨743579, by rfl⟩ : syracuseStep 991439 = 1487159) B1487159
theorem B663767 : Blo 195805 663767 := bstep (se 1 (by rfl) ⟨497825, by rfl⟩ : syracuseStep 663767 = 995651) B995651
theorem B1122569 : Blo 195805 1122569 := bstep (se 2 (by rfl) ⟨420963, by rfl⟩ : syracuseStep 1122569 = 841927) B841927
theorem B959239 : Blo 195805 959239 := bstep (se 1 (by rfl) ⟨719429, by rfl⟩ : syracuseStep 959239 = 1438859) B1438859
theorem B566023 : Blo 195805 566023 := bstep (se 1 (by rfl) ⟨424517, by rfl⟩ : syracuseStep 566023 = 849035) B849035
theorem B992573 : Blo 195805 992573 := bstep (se 3 (by rfl) ⟨186107, by rfl⟩ : syracuseStep 992573 = 372215) B372215
theorem B567607 : Blo 195805 567607 := bstep (se 1 (by rfl) ⟨425705, by rfl⟩ : syracuseStep 567607 = 851411) B851411
theorem B2271563 : Blo 195805 2271563 := bstep (se 1 (by rfl) ⟨1703672, by rfl⟩ : syracuseStep 2271563 = 3407345) B3407345
theorem B764639 : Blo 195805 764639 := bstep (se 1 (by rfl) ⟨573479, by rfl⟩ : syracuseStep 764639 = 1146959) B1146959
theorem B1911559 : Blo 195805 1911559 := bstep (se 1 (by rfl) ⟨1433669, by rfl⟩ : syracuseStep 1911559 = 2867339) B2867339
theorem B666575 : Blo 195805 666575 := bstep (se 1 (by rfl) ⟨499931, by rfl⟩ : syracuseStep 666575 = 999863) B999863
theorem B371783 : Blo 195805 371783 := bstep (se 1 (by rfl) ⟨278837, by rfl⟩ : syracuseStep 371783 = 557675) B557675
theorem B371881 : Blo 195805 371881 := bstep (se 2 (by rfl) ⟨139455, by rfl⟩ : syracuseStep 371881 = 278911) B278911
theorem B666899 : Blo 195805 666899 := bstep (se 1 (by rfl) ⟨500174, by rfl⟩ : syracuseStep 666899 = 1000349) B1000349
theorem B1256887 : Blo 195805 1256887 := bstep (se 1 (by rfl) ⟨942665, by rfl⟩ : syracuseStep 1256887 = 1885331) B1885331
theorem B372367 : Blo 195805 372367 := bstep (se 1 (by rfl) ⟨279275, by rfl⟩ : syracuseStep 372367 = 558551) B558551
theorem B995003 : Blo 195805 995003 := bstep (se 1 (by rfl) ⟨746252, by rfl⟩ : syracuseStep 995003 = 1492505) B1492505
theorem B896939 : Blo 195805 896939 := bstep (se 1 (by rfl) ⟨672704, by rfl⟩ : syracuseStep 896939 = 1345409) B1345409
theorem B1683443 : Blo 195805 1683443 := bstep (se 1 (by rfl) ⟨1262582, by rfl⟩ : syracuseStep 1683443 = 2525165) B2525165
theorem B635111 : Blo 195805 635111 := bstep (se 1 (by rfl) ⟨476333, by rfl⟩ : syracuseStep 635111 = 952667) B952667
theorem B504083 : Blo 195805 504083 := bstep (se 1 (by rfl) ⟨378062, by rfl⟩ : syracuseStep 504083 = 756125) B756125
theorem B668087 : Blo 195805 668087 := bstep (se 1 (by rfl) ⟨501065, by rfl⟩ : syracuseStep 668087 = 1002131) B1002131
theorem B3584459 : Blo 195805 3584459 := bstep (se 1 (by rfl) ⟨2688344, by rfl⟩ : syracuseStep 3584459 = 5376689) B5376689
theorem B504377 : Blo 195805 504377 := bstep (se 2 (by rfl) ⟨189141, by rfl⟩ : syracuseStep 504377 = 378283) B378283
theorem B373567 : Blo 195805 373567 := bstep (se 1 (by rfl) ⟨280175, by rfl⟩ : syracuseStep 373567 = 560351) B560351
theorem B668627 : Blo 195805 668627 := bstep (se 1 (by rfl) ⟨501470, by rfl⟩ : syracuseStep 668627 = 1002941) B1002941
theorem B1488617 : Blo 195805 1488617 := bstep (se 2 (by rfl) ⟨558231, by rfl⟩ : syracuseStep 1488617 = 1116463) B1116463
theorem B374699 : Blo 195805 374699 := bstep (se 1 (by rfl) ⟨281024, by rfl⟩ : syracuseStep 374699 = 562049) B562049
theorem B440783 : Blo 195805 440783 := bstep (se 1 (by rfl) ⟨330587, by rfl⟩ : syracuseStep 440783 = 661175) B661175
theorem B440873 : Blo 195805 440873 := bstep (se 2 (by rfl) ⟨165327, by rfl⟩ : syracuseStep 440873 = 330655) B330655
theorem B441449 : Blo 195805 441449 := bstep (se 2 (by rfl) ⟨165543, by rfl⟩ : syracuseStep 441449 = 331087) B331087
theorem B1457297 : Blo 195805 1457297 := bstep (se 2 (by rfl) ⟨546486, by rfl⟩ : syracuseStep 1457297 = 1092973) B1092973
theorem B441575 : Blo 195805 441575 := bstep (se 1 (by rfl) ⟨331181, by rfl⟩ : syracuseStep 441575 = 662363) B662363
theorem B998729 : Blo 195805 998729 := bstep (se 2 (by rfl) ⟨374523, by rfl⟩ : syracuseStep 998729 = 749047) B749047
theorem B442079 : Blo 195805 442079 := bstep (se 1 (by rfl) ⟨331559, by rfl⟩ : syracuseStep 442079 = 663119) B663119
theorem B442151 : Blo 195805 442151 := bstep (se 1 (by rfl) ⟨331613, by rfl⟩ : syracuseStep 442151 = 663227) B663227
theorem B376787 : Blo 195805 376787 := bstep (se 1 (by rfl) ⟨282590, by rfl⟩ : syracuseStep 376787 = 565181) B565181
theorem B3850355 : Blo 195805 3850355 := bstep (se 1 (by rfl) ⟨2887766, by rfl⟩ : syracuseStep 3850355 = 5775533) B5775533
theorem B377455 : Blo 195805 377455 := bstep (se 1 (by rfl) ⟨283091, by rfl⟩ : syracuseStep 377455 = 566183) B566183
theorem B377531 : Blo 195805 377531 := bstep (se 1 (by rfl) ⟨283148, by rfl⟩ : syracuseStep 377531 = 566297) B566297
theorem B2245319 : Blo 195805 2245319 := bstep (se 1 (by rfl) ⟨1683989, by rfl⟩ : syracuseStep 2245319 = 3367979) B3367979
theorem B443177 : Blo 195805 443177 := bstep (se 2 (by rfl) ⟨166191, by rfl⟩ : syracuseStep 443177 = 332383) B332383
theorem B901955 : Blo 195805 901955 := bstep (se 1 (by rfl) ⟨676466, by rfl⟩ : syracuseStep 901955 = 1352933) B1352933
theorem B443447 : Blo 195805 443447 := bstep (se 1 (by rfl) ⟨332585, by rfl⟩ : syracuseStep 443447 = 665171) B665171
theorem B378047 : Blo 195805 378047 := bstep (se 1 (by rfl) ⟨283535, by rfl⟩ : syracuseStep 378047 = 567071) B567071
theorem B443627 : Blo 195805 443627 := bstep (se 1 (by rfl) ⟨332720, by rfl⟩ : syracuseStep 443627 = 665441) B665441
theorem B476641 : Blo 195805 476641 := bstep (se 2 (by rfl) ⟨178740, by rfl⟩ : syracuseStep 476641 = 357481) B357481
theorem B280255 : Blo 195805 280255 := bstep (se 1 (by rfl) ⟨210191, by rfl⟩ : syracuseStep 280255 = 420383) B420383
theorem B444095 : Blo 195805 444095 := bstep (se 1 (by rfl) ⟨333071, by rfl⟩ : syracuseStep 444095 = 666143) B666143
theorem B1132319 : Blo 195805 1132319 := bstep (se 1 (by rfl) ⟨849239, by rfl⟩ : syracuseStep 1132319 = 1698479) B1698479
theorem B1001807 : Blo 195805 1001807 := bstep (se 1 (by rfl) ⟨751355, by rfl⟩ : syracuseStep 1001807 = 1502711) B1502711
theorem B445031 : Blo 195805 445031 := bstep (se 1 (by rfl) ⟨333773, by rfl⟩ : syracuseStep 445031 = 667547) B667547
theorem B3426961 : Blo 195805 3426961 := bstep (se 2 (by rfl) ⟨1285110, by rfl⟩ : syracuseStep 3426961 = 2570221) B2570221
theorem B3394223 : Blo 195805 3394223 := bstep (se 1 (by rfl) ⟨2545667, by rfl⟩ : syracuseStep 3394223 = 5091335) B5091335
theorem B838441 : Blo 195805 838441 := bstep (se 2 (by rfl) ⟨314415, by rfl⟩ : syracuseStep 838441 = 628831) B628831
theorem B445409 : Blo 195805 445409 := bstep (se 2 (by rfl) ⟨167028, by rfl⟩ : syracuseStep 445409 = 334057) B334057
theorem B248827 : Blo 195805 248827 := bstep (se 1 (by rfl) ⟨186620, by rfl⟩ : syracuseStep 248827 = 373241) B373241
theorem B445787 : Blo 195805 445787 := bstep (se 1 (by rfl) ⟨334340, by rfl⟩ : syracuseStep 445787 = 668681) B668681
theorem B445823 : Blo 195805 445823 := bstep (se 1 (by rfl) ⟨334367, by rfl⟩ : syracuseStep 445823 = 668735) B668735
theorem B1822591 : Blo 195805 1822591 := bstep (se 1 (by rfl) ⟨1366943, by rfl⟩ : syracuseStep 1822591 = 2733887) B2733887
theorem B282619 : Blo 195805 282619 := bstep (se 1 (by rfl) ⟨211964, by rfl⟩ : syracuseStep 282619 = 423929) B423929
theorem B282727 : Blo 195805 282727 := bstep (se 1 (by rfl) ⟨212045, by rfl⟩ : syracuseStep 282727 = 424091) B424091
theorem B708763 : Blo 195805 708763 := bstep (se 1 (by rfl) ⟨531572, by rfl⟩ : syracuseStep 708763 = 1063145) B1063145
theorem B5099719 : Blo 195805 5099719 := bstep (se 1 (by rfl) ⟨3824789, by rfl⟩ : syracuseStep 5099719 = 7649579) B7649579
theorem B708851 : Blo 195805 708851 := bstep (se 1 (by rfl) ⟨531638, by rfl⟩ : syracuseStep 708851 = 1063277) B1063277
theorem B807155 : Blo 195805 807155 := bstep (se 1 (by rfl) ⟨605366, by rfl⟩ : syracuseStep 807155 = 1210733) B1210733
theorem B1429751 : Blo 195805 1429751 := bstep (se 1 (by rfl) ⟨1072313, by rfl⟩ : syracuseStep 1429751 = 2144627) B2144627
theorem B676219 : Blo 195805 676219 := bstep (se 1 (by rfl) ⟨507164, by rfl⟩ : syracuseStep 676219 = 1014329) B1014329
theorem B1003913 : Blo 195805 1003913 := bstep (se 2 (by rfl) ⟨376467, by rfl⟩ : syracuseStep 1003913 = 752935) B752935
theorem B250715 : Blo 195805 250715 := bstep (se 1 (by rfl) ⟨188036, by rfl⟩ : syracuseStep 250715 = 376073) B376073
theorem B2151461 : Blo 195805 2151461 := bstep (se 4 (by rfl) ⟨201699, by rfl⟩ : syracuseStep 2151461 = 403399) B403399
theorem B447695 : Blo 195805 447695 := bstep (se 1 (by rfl) ⟨335771, by rfl⟩ : syracuseStep 447695 = 671543) B671543
theorem B447785 : Blo 195805 447785 := bstep (se 2 (by rfl) ⟨167919, by rfl⟩ : syracuseStep 447785 = 335839) B335839
theorem B447983 : Blo 195805 447983 := bstep (se 1 (by rfl) ⟨335987, by rfl⟩ : syracuseStep 447983 = 671975) B671975
theorem B448379 : Blo 195805 448379 := bstep (se 1 (by rfl) ⟨336284, by rfl⟩ : syracuseStep 448379 = 672569) B672569
theorem B448415 : Blo 195805 448415 := bstep (se 1 (by rfl) ⟨336311, by rfl⟩ : syracuseStep 448415 = 672623) B672623
theorem B448649 : Blo 195805 448649 := bstep (se 2 (by rfl) ⟨168243, by rfl⟩ : syracuseStep 448649 = 336487) B336487
theorem B743687 : Blo 195805 743687 := bstep (se 1 (by rfl) ⟨557765, by rfl⟩ : syracuseStep 743687 = 1115531) B1115531
theorem B448865 : Blo 195805 448865 := bstep (se 2 (by rfl) ⟨168324, by rfl⟩ : syracuseStep 448865 = 336649) B336649
theorem B1431917 : Blo 195805 1431917 := bstep (se 3 (by rfl) ⟨268484, by rfl⟩ : syracuseStep 1431917 = 536969) B536969
theorem B2251151 : Blo 195805 2251151 := bstep (se 1 (by rfl) ⟨1688363, by rfl⟩ : syracuseStep 2251151 = 3376727) B3376727
theorem B448955 : Blo 195805 448955 := bstep (se 1 (by rfl) ⟨336716, by rfl⟩ : syracuseStep 448955 = 673433) B673433
theorem B252391 : Blo 195805 252391 := bstep (se 1 (by rfl) ⟨189293, by rfl⟩ : syracuseStep 252391 = 378587) B378587
theorem B1137401 : Blo 195805 1137401 := bstep (se 2 (by rfl) ⟨426525, by rfl⟩ : syracuseStep 1137401 = 853051) B853051
theorem B449351 : Blo 195805 449351 := bstep (se 1 (by rfl) ⟨337013, by rfl⟩ : syracuseStep 449351 = 674027) B674027
theorem B1596631 : Blo 195805 1596631 := bstep (se 1 (by rfl) ⟨1197473, by rfl⟩ : syracuseStep 1596631 = 2394947) B2394947
theorem B318953 : Blo 195805 318953 := bstep (se 2 (by rfl) ⟨119607, by rfl⟩ : syracuseStep 318953 = 239215) B239215
theorem B23092775 : Blo 195805 23092775 := bstep (se 1 (by rfl) ⟨17319581, by rfl⟩ : syracuseStep 23092775 = 34639163) B34639163
theorem B220783 : Blo 195805 220783 := bstep (se 1 (by rfl) ⟨165587, by rfl⟩ : syracuseStep 220783 = 331175) B331175
theorem B220891 : Blo 195805 220891 := bstep (se 1 (by rfl) ⟨165668, by rfl⟩ : syracuseStep 220891 = 331337) B331337
theorem B844303 : Blo 195805 844303 := bstep (se 1 (by rfl) ⟨633227, by rfl⟩ : syracuseStep 844303 = 1266455) B1266455
theorem B221863 : Blo 195805 221863 := bstep (se 1 (by rfl) ⟨166397, by rfl⟩ : syracuseStep 221863 = 332795) B332795
theorem B222151 : Blo 195805 222151 := bstep (se 1 (by rfl) ⟨166613, by rfl⟩ : syracuseStep 222151 = 333227) B333227
theorem B222511 : Blo 195805 222511 := bstep (se 1 (by rfl) ⟨166883, by rfl⟩ : syracuseStep 222511 = 333767) B333767
theorem B714041 : Blo 195805 714041 := bstep (se 2 (by rfl) ⟨267765, by rfl⟩ : syracuseStep 714041 = 535531) B535531
theorem B13297097 : Blo 195805 13297097 := bstep (se 2 (by rfl) ⟨4986411, by rfl⟩ : syracuseStep 13297097 = 9972823) B9972823
theorem B747103 : Blo 195805 747103 := bstep (se 1 (by rfl) ⟨560327, by rfl⟩ : syracuseStep 747103 = 1120655) B1120655
theorem B9791165 : Blo 195805 9791165 := bstep (se 3 (by rfl) ⟨1835843, by rfl⟩ : syracuseStep 9791165 = 3671687) B3671687
theorem B223015 : Blo 195805 223015 := bstep (se 1 (by rfl) ⟨167261, by rfl⟩ : syracuseStep 223015 = 334523) B334523
theorem B1010207 : Blo 195805 1010207 := bstep (se 1 (by rfl) ⟨757655, by rfl⟩ : syracuseStep 1010207 = 1515311) B1515311
theorem B1207619 : Blo 195805 1207619 := bstep (se 1 (by rfl) ⟨905714, by rfl⟩ : syracuseStep 1207619 = 1811429) B1811429
theorem B1895993 : Blo 195805 1895993 := bstep (se 2 (by rfl) ⟨710997, by rfl⟩ : syracuseStep 1895993 = 1421995) B1421995
theorem B1273427 : Blo 195805 1273427 := bstep (se 1 (by rfl) ⟨955070, by rfl⟩ : syracuseStep 1273427 = 1910141) B1910141
theorem B749351 : Blo 195805 749351 := bstep (se 1 (by rfl) ⟨562013, by rfl⟩ : syracuseStep 749351 = 1124027) B1124027
theorem B1896335 : Blo 195805 1896335 := bstep (se 1 (by rfl) ⟨1422251, by rfl⟩ : syracuseStep 1896335 = 2844503) B2844503
theorem B946363 : Blo 195805 946363 := bstep (se 1 (by rfl) ⟨709772, by rfl⟩ : syracuseStep 946363 = 1419545) B1419545
theorem B1799453 : Blo 195805 1799453 := bstep (se 3 (by rfl) ⟨337397, by rfl⟩ : syracuseStep 1799453 = 674795) B674795
theorem B357695 : Blo 195805 357695 := bstep (se 1 (by rfl) ⟨268271, by rfl⟩ : syracuseStep 357695 = 536543) B536543
theorem B2848193 : Blo 195805 2848193 := bstep (se 2 (by rfl) ⟨1068072, by rfl⟩ : syracuseStep 2848193 = 2136145) B2136145
theorem B751963 : Blo 195805 751963 := bstep (se 1 (by rfl) ⟨563972, by rfl⟩ : syracuseStep 751963 = 1127945) B1127945
theorem B1505627 : Blo 195805 1505627 := bstep (se 1 (by rfl) ⟨1129220, by rfl⟩ : syracuseStep 1505627 = 2258441) B2258441
theorem B3603143 : Blo 195805 3603143 := bstep (se 1 (by rfl) ⟨2702357, by rfl⟩ : syracuseStep 3603143 = 5404715) B5404715
theorem B1211219 : Blo 195805 1211219 := bstep (se 1 (by rfl) ⟨908414, by rfl⟩ : syracuseStep 1211219 = 1816829) B1816829
theorem B2259899 : Blo 195805 2259899 := bstep (se 1 (by rfl) ⟨1694924, by rfl⟩ : syracuseStep 2259899 = 3389849) B3389849
theorem B293993 : Blo 195805 293993 := bstep (se 2 (by rfl) ⟨110247, by rfl⟩ : syracuseStep 293993 = 220495) B220495
theorem B195815 : Blo 195805 195815 := bstep (se 1 (by rfl) ⟨146861, by rfl⟩ : syracuseStep 195815 = 293723) B293723
theorem B294119 : Blo 195805 294119 := bstep (se 1 (by rfl) ⟨220589, by rfl⟩ : syracuseStep 294119 = 441179) B441179
theorem B752921 : Blo 195805 752921 := bstep (se 2 (by rfl) ⟨282345, by rfl⟩ : syracuseStep 752921 = 564691) B564691
theorem B195911 : Blo 195805 195911 := bstep (se 1 (by rfl) ⟨146933, by rfl⟩ : syracuseStep 195911 = 293867) B293867
theorem B2522501 : Blo 195805 2522501 := bstep (se 4 (by rfl) ⟨236484, by rfl⟩ : syracuseStep 2522501 = 472969) B472969
theorem B196047 : Blo 195805 196047 := bstep (se 1 (by rfl) ⟨147035, by rfl⟩ : syracuseStep 196047 = 294071) B294071
theorem B196207 : Blo 195805 196207 := bstep (se 1 (by rfl) ⟨147155, by rfl⟩ : syracuseStep 196207 = 294311) B294311
theorem B196263 : Blo 195805 196263 := bstep (se 1 (by rfl) ⟨147197, by rfl⟩ : syracuseStep 196263 = 294395) B294395
theorem B294623 : Blo 195805 294623 := bstep (se 1 (by rfl) ⟨220967, by rfl⟩ : syracuseStep 294623 = 441935) B441935
theorem B196327 : Blo 195805 196327 := bstep (se 1 (by rfl) ⟨147245, by rfl⟩ : syracuseStep 196327 = 294491) B294491
theorem B294665 : Blo 195805 294665 := bstep (se 2 (by rfl) ⟨110499, by rfl⟩ : syracuseStep 294665 = 220999) B220999
theorem B196383 : Blo 195805 196383 := bstep (se 1 (by rfl) ⟨147287, by rfl⟩ : syracuseStep 196383 = 294575) B294575
theorem B196463 : Blo 195805 196463 := bstep (se 1 (by rfl) ⟨147347, by rfl⟩ : syracuseStep 196463 = 294695) B294695
theorem B196519 : Blo 195805 196519 := bstep (se 1 (by rfl) ⟨147389, by rfl⟩ : syracuseStep 196519 = 294779) B294779
theorem B14516281 : Blo 195805 14516281 := bstep (se 2 (by rfl) ⟨5443605, by rfl⟩ : syracuseStep 14516281 = 10887211) B10887211
theorem B196735 : Blo 195805 196735 := bstep (se 1 (by rfl) ⟨147551, by rfl⟩ : syracuseStep 196735 = 295103) B295103
theorem B197019 : Blo 195805 197019 := bstep (se 1 (by rfl) ⟨147764, by rfl⟩ : syracuseStep 197019 = 295529) B295529
theorem B197023 : Blo 195805 197023 := bstep (se 1 (by rfl) ⟨147767, by rfl⟩ : syracuseStep 197023 = 295535) B295535
theorem B852383 : Blo 195805 852383 := bstep (se 1 (by rfl) ⟨639287, by rfl⟩ : syracuseStep 852383 = 1278575) B1278575
theorem B295451 : Blo 195805 295451 := bstep (se 1 (by rfl) ⟨221588, by rfl⟩ : syracuseStep 295451 = 443177) B443177
theorem B1704563 : Blo 195805 1704563 := bstep (se 1 (by rfl) ⟨1278422, by rfl⟩ : syracuseStep 1704563 = 2556845) B2556845
theorem B295631 : Blo 195805 295631 := bstep (se 1 (by rfl) ⟨221723, by rfl⟩ : syracuseStep 295631 = 443447) B443447
theorem B197439 : Blo 195805 197439 := bstep (se 1 (by rfl) ⟨148079, by rfl⟩ : syracuseStep 197439 = 296159) B296159
theorem B295751 : Blo 195805 295751 := bstep (se 1 (by rfl) ⟨221813, by rfl⟩ : syracuseStep 295751 = 443627) B443627
theorem B197447 : Blo 195805 197447 := bstep (se 1 (by rfl) ⟨148085, by rfl⟩ : syracuseStep 197447 = 296171) B296171
theorem B295817 : Blo 195805 295817 := bstep (se 2 (by rfl) ⟨110931, by rfl⟩ : syracuseStep 295817 = 221863) B221863
theorem B1278985 : Blo 195805 1278985 := bstep (se 2 (by rfl) ⟨479619, by rfl⟩ : syracuseStep 1278985 = 959239) B959239
theorem B754697 : Blo 195805 754697 := bstep (se 2 (by rfl) ⟨283011, by rfl⟩ : syracuseStep 754697 = 566023) B566023
theorem B197703 : Blo 195805 197703 := bstep (se 1 (by rfl) ⟨148277, by rfl⟩ : syracuseStep 197703 = 296555) B296555
theorem B296063 : Blo 195805 296063 := bstep (se 1 (by rfl) ⟨222047, by rfl⟩ : syracuseStep 296063 = 444095) B444095
theorem B197759 : Blo 195805 197759 := bstep (se 1 (by rfl) ⟨148319, by rfl⟩ : syracuseStep 197759 = 296639) B296639
theorem B754879 : Blo 195805 754879 := bstep (se 1 (by rfl) ⟨566159, by rfl⟩ : syracuseStep 754879 = 1132319) B1132319
theorem B197883 : Blo 195805 197883 := bstep (se 1 (by rfl) ⟨148412, by rfl⟩ : syracuseStep 197883 = 296825) B296825
theorem B296201 : Blo 195805 296201 := bstep (se 2 (by rfl) ⟨111075, by rfl⟩ : syracuseStep 296201 = 222151) B222151
theorem B1902143 : Blo 195805 1902143 := bstep (se 1 (by rfl) ⟨1426607, by rfl⟩ : syracuseStep 1902143 = 2853215) B2853215
theorem B788077 : Blo 195805 788077 := bstep (se 3 (by rfl) ⟨147764, by rfl⟩ : syracuseStep 788077 = 295529) B295529
theorem B296681 : Blo 195805 296681 := bstep (se 2 (by rfl) ⟨111255, by rfl⟩ : syracuseStep 296681 = 222511) B222511
theorem B296687 : Blo 195805 296687 := bstep (se 1 (by rfl) ⟨222515, by rfl⟩ : syracuseStep 296687 = 445031) B445031
theorem B198383 : Blo 195805 198383 := bstep (se 1 (by rfl) ⟨148787, by rfl⟩ : syracuseStep 198383 = 297575) B297575
theorem B2262815 : Blo 195805 2262815 := bstep (se 1 (by rfl) ⟨1697111, by rfl⟩ : syracuseStep 2262815 = 3394223) B3394223
theorem B75171685 : Blo 195805 75171685 := bstep (se 4 (by rfl) ⟨7047345, by rfl⟩ : syracuseStep 75171685 = 14094691) B14094691
theorem B198511 : Blo 195805 198511 := bstep (se 1 (by rfl) ⟨148883, by rfl⟩ : syracuseStep 198511 = 297767) B297767
theorem B296939 : Blo 195805 296939 := bstep (se 1 (by rfl) ⟨222704, by rfl⟩ : syracuseStep 296939 = 445409) B445409
theorem B198727 : Blo 195805 198727 := bstep (se 1 (by rfl) ⟨149045, by rfl⟩ : syracuseStep 198727 = 298091) B298091
theorem B297191 : Blo 195805 297191 := bstep (se 1 (by rfl) ⟨222893, by rfl⟩ : syracuseStep 297191 = 445787) B445787
theorem B198887 : Blo 195805 198887 := bstep (se 1 (by rfl) ⟨149165, by rfl⟩ : syracuseStep 198887 = 298331) B298331
theorem B198907 : Blo 195805 198907 := bstep (se 1 (by rfl) ⟨149180, by rfl⟩ : syracuseStep 198907 = 298361) B298361
theorem B297215 : Blo 195805 297215 := bstep (se 1 (by rfl) ⟨222911, by rfl⟩ : syracuseStep 297215 = 445823) B445823
theorem B198911 : Blo 195805 198911 := bstep (se 1 (by rfl) ⟨149183, by rfl⟩ : syracuseStep 198911 = 298367) B298367
theorem B297353 : Blo 195805 297353 := bstep (se 2 (by rfl) ⟨111507, by rfl⟩ : syracuseStep 297353 = 223015) B223015
theorem B199327 : Blo 195805 199327 := bstep (se 1 (by rfl) ⟨149495, by rfl⟩ : syracuseStep 199327 = 298991) B298991
theorem B199335 : Blo 195805 199335 := bstep (se 1 (by rfl) ⟨149501, by rfl⟩ : syracuseStep 199335 = 299003) B299003
theorem B199375 : Blo 195805 199375 := bstep (se 1 (by rfl) ⟨149531, by rfl⟩ : syracuseStep 199375 = 299063) B299063
theorem B199407 : Blo 195805 199407 := bstep (se 1 (by rfl) ⟨149555, by rfl⟩ : syracuseStep 199407 = 299111) B299111
theorem B1706771 : Blo 195805 1706771 := bstep (se 1 (by rfl) ⟨1280078, by rfl⟩ : syracuseStep 1706771 = 2560157) B2560157
theorem B199455 : Blo 195805 199455 := bstep (se 1 (by rfl) ⟨149591, by rfl⟩ : syracuseStep 199455 = 299183) B299183
theorem B953167 : Blo 195805 953167 := bstep (se 1 (by rfl) ⟨714875, by rfl⟩ : syracuseStep 953167 = 1429751) B1429751
theorem B199591 : Blo 195805 199591 := bstep (se 1 (by rfl) ⟨149693, by rfl⟩ : syracuseStep 199591 = 299387) B299387
theorem B756809 : Blo 195805 756809 := bstep (se 2 (by rfl) ⟨283803, by rfl⟩ : syracuseStep 756809 = 567607) B567607
theorem B199771 : Blo 195805 199771 := bstep (se 1 (by rfl) ⟨149828, by rfl⟩ : syracuseStep 199771 = 299657) B299657
theorem B298463 : Blo 195805 298463 := bstep (se 1 (by rfl) ⟨223847, by rfl⟩ : syracuseStep 298463 = 447695) B447695
theorem B298523 : Blo 195805 298523 := bstep (se 1 (by rfl) ⟨223892, by rfl⟩ : syracuseStep 298523 = 447785) B447785
theorem B298655 : Blo 195805 298655 := bstep (se 1 (by rfl) ⟨223991, by rfl⟩ : syracuseStep 298655 = 447983) B447983
theorem B1117921 : Blo 195805 1117921 := bstep (se 2 (by rfl) ⟨419220, by rfl⟩ : syracuseStep 1117921 = 838441) B838441
theorem B298919 : Blo 195805 298919 := bstep (se 1 (by rfl) ⟨224189, by rfl⟩ : syracuseStep 298919 = 448379) B448379
theorem B298943 : Blo 195805 298943 := bstep (se 1 (by rfl) ⟨224207, by rfl⟩ : syracuseStep 298943 = 448415) B448415
theorem B331769 : Blo 195805 331769 := bstep (se 2 (by rfl) ⟨124413, by rfl⟩ : syracuseStep 331769 = 248827) B248827
theorem B299099 : Blo 195805 299099 := bstep (se 1 (by rfl) ⟨224324, by rfl⟩ : syracuseStep 299099 = 448649) B448649
theorem B495791 : Blo 195805 495791 := bstep (se 1 (by rfl) ⟨371843, by rfl⟩ : syracuseStep 495791 = 743687) B743687
theorem B495841 : Blo 195805 495841 := bstep (se 2 (by rfl) ⟨185940, by rfl⟩ : syracuseStep 495841 = 371881) B371881
theorem B299243 : Blo 195805 299243 := bstep (se 1 (by rfl) ⟨224432, by rfl⟩ : syracuseStep 299243 = 448865) B448865
theorem B954611 : Blo 195805 954611 := bstep (se 1 (by rfl) ⟨715958, by rfl⟩ : syracuseStep 954611 = 1431917) B1431917
theorem B332039 : Blo 195805 332039 := bstep (se 1 (by rfl) ⟨249029, by rfl⟩ : syracuseStep 332039 = 498059) B498059
theorem B299303 : Blo 195805 299303 := bstep (se 1 (by rfl) ⟨224477, by rfl⟩ : syracuseStep 299303 = 448955) B448955
theorem B758267 : Blo 195805 758267 := bstep (se 1 (by rfl) ⟨568700, by rfl⟩ : syracuseStep 758267 = 1137401) B1137401
theorem B299567 : Blo 195805 299567 := bstep (se 1 (by rfl) ⟨224675, by rfl⟩ : syracuseStep 299567 = 449351) B449351
theorem B496489 : Blo 195805 496489 := bstep (se 2 (by rfl) ⟨186183, by rfl⟩ : syracuseStep 496489 = 372367) B372367
theorem B333119 : Blo 195805 333119 := bstep (se 1 (by rfl) ⟨249839, by rfl⟩ : syracuseStep 333119 = 499679) B499679
theorem B660905 : Blo 195805 660905 := bstep (se 2 (by rfl) ⟨247839, by rfl⟩ : syracuseStep 660905 = 495679) B495679
theorem B660959 : Blo 195805 660959 := bstep (se 1 (by rfl) ⟨495719, by rfl⟩ : syracuseStep 660959 = 991439) B991439
theorem B661715 : Blo 195805 661715 := bstep (se 1 (by rfl) ⟨496286, by rfl⟩ : syracuseStep 661715 = 992573) B992573
theorem B498089 : Blo 195805 498089 := bstep (se 2 (by rfl) ⟨186783, by rfl⟩ : syracuseStep 498089 = 373567) B373567
theorem B1514375 : Blo 195805 1514375 := bstep (se 1 (by rfl) ⟨1135781, by rfl⟩ : syracuseStep 1514375 = 2271563) B2271563
theorem B9608381 : Blo 195805 9608381 := bstep (se 3 (by rfl) ⟨1801571, by rfl⟩ : syracuseStep 9608381 = 3603143) B3603143
theorem B663335 : Blo 195805 663335 := bstep (se 1 (by rfl) ⟨497501, by rfl⟩ : syracuseStep 663335 = 995003) B995003
theorem B499567 : Blo 195805 499567 := bstep (se 1 (by rfl) ⟨374675, by rfl⟩ : syracuseStep 499567 = 749351) B749351
theorem B597959 : Blo 195805 597959 := bstep (se 1 (by rfl) ⟨448469, by rfl⟩ : syracuseStep 597959 = 896939) B896939
theorem B1122295 : Blo 195805 1122295 := bstep (se 1 (by rfl) ⟨841721, by rfl⟩ : syracuseStep 1122295 = 1683443) B1683443
theorem B336055 : Blo 195805 336055 := bstep (se 1 (by rfl) ⟨252041, by rfl⟩ : syracuseStep 336055 = 504083) B504083
theorem B336251 : Blo 195805 336251 := bstep (se 1 (by rfl) ⟨252188, by rfl⟩ : syracuseStep 336251 = 504377) B504377
theorem B336521 : Blo 195805 336521 := bstep (se 2 (by rfl) ⟨126195, by rfl⟩ : syracuseStep 336521 = 252391) B252391
theorem B238463 : Blo 195805 238463 := bstep (se 1 (by rfl) ⟨178847, by rfl⟩ : syracuseStep 238463 = 357695) B357695
theorem B992411 : Blo 195805 992411 := bstep (se 1 (by rfl) ⟨744308, by rfl⟩ : syracuseStep 992411 = 1488617) B1488617
theorem B501947 : Blo 195805 501947 := bstep (se 1 (by rfl) ⟨376460, by rfl⟩ : syracuseStep 501947 = 752921) B752921
theorem B665819 : Blo 195805 665819 := bstep (se 1 (by rfl) ⟨499364, by rfl⟩ : syracuseStep 665819 = 998729) B998729
theorem B1681667 : Blo 195805 1681667 := bstep (se 1 (by rfl) ⟨1261250, by rfl⟩ : syracuseStep 1681667 = 2522501) B2522501
theorem B1059425 : Blo 195805 1059425 := bstep (se 2 (by rfl) ⟨397284, by rfl⟩ : syracuseStep 1059425 = 794569) B794569
theorem B2566903 : Blo 195805 2566903 := bstep (se 1 (by rfl) ⟨1925177, by rfl⟩ : syracuseStep 2566903 = 3850355) B3850355
theorem B1125737 : Blo 195805 1125737 := bstep (se 2 (by rfl) ⟨422151, by rfl⟩ : syracuseStep 1125737 = 844303) B844303
theorem B503273 : Blo 195805 503273 := bstep (se 2 (by rfl) ⟨188727, by rfl⟩ : syracuseStep 503273 = 377455) B377455
theorem B503891 : Blo 195805 503891 := bstep (se 1 (by rfl) ⟨377918, by rfl⟩ : syracuseStep 503891 = 755837) B755837
theorem B667871 : Blo 195805 667871 := bstep (se 1 (by rfl) ⟨500903, by rfl⟩ : syracuseStep 667871 = 1001807) B1001807
theorem B635521 : Blo 195805 635521 := bstep (se 2 (by rfl) ⟨238320, by rfl⟩ : syracuseStep 635521 = 476641) B476641
theorem B996137 : Blo 195805 996137 := bstep (se 2 (by rfl) ⟨373551, by rfl⟩ : syracuseStep 996137 = 747103) B747103
theorem B2405213 : Blo 195805 2405213 := bstep (se 3 (by rfl) ⟨450977, by rfl⟩ : syracuseStep 2405213 = 901955) B901955
theorem B668573 : Blo 195805 668573 := bstep (se 3 (by rfl) ⟨125357, by rfl⟩ : syracuseStep 668573 = 250715) B250715
theorem B373673 : Blo 195805 373673 := bstep (se 2 (by rfl) ⟨140127, by rfl⟩ : syracuseStep 373673 = 280255) B280255
theorem B4240457 : Blo 195805 4240457 := bstep (se 2 (by rfl) ⟨1590171, by rfl⟩ : syracuseStep 4240457 = 3180343) B3180343
theorem B2274479 : Blo 195805 2274479 := bstep (se 1 (by rfl) ⟨1705859, by rfl⟩ : syracuseStep 2274479 = 3411719) B3411719
theorem B472567 : Blo 195805 472567 := bstep (se 1 (by rfl) ⟨354425, by rfl⟩ : syracuseStep 472567 = 708851) B708851
theorem B538103 : Blo 195805 538103 := bstep (se 1 (by rfl) ⟨403577, by rfl⟩ : syracuseStep 538103 = 807155) B807155
theorem B669275 : Blo 195805 669275 := bstep (se 1 (by rfl) ⟨501956, by rfl⟩ : syracuseStep 669275 = 1003913) B1003913
theorem B636623 : Blo 195805 636623 := bstep (se 1 (by rfl) ⟨477467, by rfl⟩ : syracuseStep 636623 = 954935) B954935
theorem B636751 : Blo 195805 636751 := bstep (se 1 (by rfl) ⟨477563, by rfl⟩ : syracuseStep 636751 = 955127) B955127
theorem B505723 : Blo 195805 505723 := bstep (se 1 (by rfl) ⟨379292, by rfl⟩ : syracuseStep 505723 = 758585) B758585
theorem B4798541 : Blo 195805 4798541 := bstep (se 3 (by rfl) ⟨899726, by rfl⟩ : syracuseStep 4798541 = 1799453) B1799453
theorem B4569281 : Blo 195805 4569281 := bstep (se 2 (by rfl) ⟨1713480, by rfl⟩ : syracuseStep 4569281 = 3426961) B3426961
theorem B212635 : Blo 195805 212635 := bstep (se 1 (by rfl) ⟨159476, by rfl⟩ : syracuseStep 212635 = 318953) B318953
theorem B442331 : Blo 195805 442331 := bstep (se 1 (by rfl) ⟨331748, by rfl⟩ : syracuseStep 442331 = 663497) B663497
theorem B2146267 : Blo 195805 2146267 := bstep (se 1 (by rfl) ⟨1609700, by rfl⟩ : syracuseStep 2146267 = 3219401) B3219401
theorem B376825 : Blo 195805 376825 := bstep (se 2 (by rfl) ⟨141309, by rfl⟩ : syracuseStep 376825 = 282619) B282619
theorem B376969 : Blo 195805 376969 := bstep (se 2 (by rfl) ⟨141363, by rfl⟩ : syracuseStep 376969 = 282727) B282727
theorem B442511 : Blo 195805 442511 := bstep (se 1 (by rfl) ⟨331883, by rfl⟩ : syracuseStep 442511 = 663767) B663767
theorem B442601 : Blo 195805 442601 := bstep (se 2 (by rfl) ⟨165975, by rfl⟩ : syracuseStep 442601 = 331951) B331951
theorem B1261817 : Blo 195805 1261817 := bstep (se 2 (by rfl) ⟨473181, by rfl⟩ : syracuseStep 1261817 = 946363) B946363
theorem B6799625 : Blo 195805 6799625 := bstep (se 2 (by rfl) ⟨2549859, by rfl⟩ : syracuseStep 6799625 = 5099719) B5099719
theorem B901625 : Blo 195805 901625 := bstep (se 2 (by rfl) ⟨338109, by rfl⟩ : syracuseStep 901625 = 676219) B676219
theorem B476027 : Blo 195805 476027 := bstep (se 1 (by rfl) ⟨357020, by rfl⟩ : syracuseStep 476027 = 714041) B714041
theorem B8864731 : Blo 195805 8864731 := bstep (se 1 (by rfl) ⟨6648548, by rfl⟩ : syracuseStep 8864731 = 13297097) B13297097
theorem B5424205 : Blo 195805 5424205 := bstep (se 3 (by rfl) ⟨1017038, by rfl⟩ : syracuseStep 5424205 = 2034077) B2034077
theorem B673471 : Blo 195805 673471 := bstep (se 1 (by rfl) ⟨505103, by rfl⟩ : syracuseStep 673471 = 1010207) B1010207
theorem B509759 : Blo 195805 509759 := bstep (se 1 (by rfl) ⟨382319, by rfl⟩ : syracuseStep 509759 = 764639) B764639
theorem B444383 : Blo 195805 444383 := bstep (se 1 (by rfl) ⟨333287, by rfl⟩ : syracuseStep 444383 = 666575) B666575
theorem B247855 : Blo 195805 247855 := bstep (se 1 (by rfl) ⟨185891, by rfl⟩ : syracuseStep 247855 = 371783) B371783
theorem B444599 : Blo 195805 444599 := bstep (se 1 (by rfl) ⟨333449, by rfl⟩ : syracuseStep 444599 = 666899) B666899
theorem B805079 : Blo 195805 805079 := bstep (se 1 (by rfl) ⟨603809, by rfl⟩ : syracuseStep 805079 = 1207619) B1207619
theorem B6703397 : Blo 195805 6703397 := bstep (se 4 (by rfl) ⟨628443, by rfl⟩ : syracuseStep 6703397 = 1256887) B1256887
theorem B1263995 : Blo 195805 1263995 := bstep (se 1 (by rfl) ⟨947996, by rfl⟩ : syracuseStep 1263995 = 1895993) B1895993
theorem B1264223 : Blo 195805 1264223 := bstep (se 1 (by rfl) ⟨948167, by rfl⟩ : syracuseStep 1264223 = 1896335) B1896335
theorem B445391 : Blo 195805 445391 := bstep (se 1 (by rfl) ⟨334043, by rfl⟩ : syracuseStep 445391 = 668087) B668087
theorem B445481 : Blo 195805 445481 := bstep (se 2 (by rfl) ⟨167055, by rfl⟩ : syracuseStep 445481 = 334111) B334111
theorem B1002617 : Blo 195805 1002617 := bstep (se 2 (by rfl) ⟨375981, by rfl⟩ : syracuseStep 1002617 = 751963) B751963
theorem B445751 : Blo 195805 445751 := bstep (se 1 (by rfl) ⟨334313, by rfl⟩ : syracuseStep 445751 = 668627) B668627
theorem B249799 : Blo 195805 249799 := bstep (se 1 (by rfl) ⟨187349, by rfl⟩ : syracuseStep 249799 = 374699) B374699
theorem B1003751 : Blo 195805 1003751 := bstep (se 1 (by rfl) ⟨752813, by rfl⟩ : syracuseStep 1003751 = 1505627) B1505627
theorem B807479 : Blo 195805 807479 := bstep (se 1 (by rfl) ⟨605609, by rfl⟩ : syracuseStep 807479 = 1211219) B1211219
theorem B9720485 : Blo 195805 9720485 := bstep (se 4 (by rfl) ⟨911295, by rfl⟩ : syracuseStep 9720485 = 1822591) B1822591
theorem B971531 : Blo 195805 971531 := bstep (se 1 (by rfl) ⟨728648, by rfl⟩ : syracuseStep 971531 = 1457297) B1457297
theorem B251191 : Blo 195805 251191 := bstep (se 1 (by rfl) ⟨188393, by rfl⟩ : syracuseStep 251191 = 376787) B376787
theorem B251687 : Blo 195805 251687 := bstep (se 1 (by rfl) ⟨188765, by rfl⟩ : syracuseStep 251687 = 377531) B377531
theorem B1496879 : Blo 195805 1496879 := bstep (se 1 (by rfl) ⟨1122659, by rfl⟩ : syracuseStep 1496879 = 2245319) B2245319
theorem B9558557 : Blo 195805 9558557 := bstep (se 3 (by rfl) ⟨1792229, by rfl⟩ : syracuseStep 9558557 = 3584459) B3584459
theorem B2120579 : Blo 195805 2120579 := bstep (se 1 (by rfl) ⟨1590434, by rfl⟩ : syracuseStep 2120579 = 3180869) B3180869
theorem B221287 : Blo 195805 221287 := bstep (se 1 (by rfl) ⟨165965, by rfl⟩ : syracuseStep 221287 = 331931) B331931
theorem B713117 : Blo 195805 713117 := bstep (se 3 (by rfl) ⟨133709, by rfl⟩ : syracuseStep 713117 = 267419) B267419
theorem B1008125 : Blo 195805 1008125 := bstep (se 3 (by rfl) ⟨189023, by rfl⟩ : syracuseStep 1008125 = 378047) B378047
theorem B1139321 : Blo 195805 1139321 := bstep (se 2 (by rfl) ⟨427245, by rfl⟩ : syracuseStep 1139321 = 854491) B854491
theorem B1008287 : Blo 195805 1008287 := bstep (se 1 (by rfl) ⟨756215, by rfl⟩ : syracuseStep 1008287 = 1512431) B1512431
theorem B1434307 : Blo 195805 1434307 := bstep (se 1 (by rfl) ⟨1075730, by rfl⟩ : syracuseStep 1434307 = 2151461) B2151461
theorem B2548745 : Blo 195805 2548745 := bstep (se 2 (by rfl) ⟨955779, by rfl⟩ : syracuseStep 2548745 = 1911559) B1911559
theorem B418871 : Blo 195805 418871 := bstep (se 1 (by rfl) ⟨314153, by rfl⟩ : syracuseStep 418871 = 628307) B628307
theorem B2516143 : Blo 195805 2516143 := bstep (se 1 (by rfl) ⟨1887107, by rfl⟩ : syracuseStep 2516143 = 3774215) B3774215
theorem B222439 : Blo 195805 222439 := bstep (se 1 (by rfl) ⟨166829, by rfl⟩ : syracuseStep 222439 = 333659) B333659
theorem B746921 : Blo 195805 746921 := bstep (se 2 (by rfl) ⟨280095, by rfl⟩ : syracuseStep 746921 = 560191) B560191
theorem B1074647 : Blo 195805 1074647 := bstep (se 1 (by rfl) ⟨805985, by rfl⟩ : syracuseStep 1074647 = 1611971) B1611971
theorem B1500767 : Blo 195805 1500767 := bstep (se 1 (by rfl) ⟨1125575, by rfl⟩ : syracuseStep 1500767 = 2251151) B2251151
theorem B26109773 : Blo 195805 26109773 := bstep (se 3 (by rfl) ⟨4895582, by rfl⟩ : syracuseStep 26109773 = 9791165) B9791165
theorem B15395183 : Blo 195805 15395183 := bstep (se 1 (by rfl) ⟨11546387, by rfl⟩ : syracuseStep 15395183 = 23092775) B23092775
theorem B748379 : Blo 195805 748379 := bstep (se 1 (by rfl) ⟨561284, by rfl⟩ : syracuseStep 748379 = 1122569) B1122569
theorem B945017 : Blo 195805 945017 := bstep (se 2 (by rfl) ⟨354381, by rfl⟩ : syracuseStep 945017 = 708763) B708763
theorem B1536889 : Blo 195805 1536889 := bstep (se 2 (by rfl) ⟨576333, by rfl⟩ : syracuseStep 1536889 = 1152667) B1152667
theorem B848951 : Blo 195805 848951 := bstep (se 1 (by rfl) ⟨636713, by rfl⟩ : syracuseStep 848951 = 1273427) B1273427
theorem B423407 : Blo 195805 423407 := bstep (se 1 (by rfl) ⟨317555, by rfl⟩ : syracuseStep 423407 = 635111) B635111
theorem B1275425 : Blo 195805 1275425 := bstep (se 2 (by rfl) ⟨478284, by rfl⟩ : syracuseStep 1275425 = 956569) B956569
theorem B1898795 : Blo 195805 1898795 := bstep (se 1 (by rfl) ⟨1424096, by rfl⟩ : syracuseStep 1898795 = 2848193) B2848193
theorem B2128841 : Blo 195805 2128841 := bstep (se 2 (by rfl) ⟨798315, by rfl⟩ : syracuseStep 2128841 = 1596631) B1596631
theorem B293855 : Blo 195805 293855 := bstep (se 1 (by rfl) ⟨220391, by rfl⟩ : syracuseStep 293855 = 440783) B440783
theorem B293915 : Blo 195805 293915 := bstep (se 1 (by rfl) ⟨220436, by rfl⟩ : syracuseStep 293915 = 440873) B440873
theorem B1506599 : Blo 195805 1506599 := bstep (se 1 (by rfl) ⟨1129949, by rfl⟩ : syracuseStep 1506599 = 2259899) B2259899
theorem B195995 : Blo 195805 195995 := bstep (se 1 (by rfl) ⟨146996, by rfl⟩ : syracuseStep 195995 = 293993) B293993
theorem B294299 : Blo 195805 294299 := bstep (se 1 (by rfl) ⟨220724, by rfl⟩ : syracuseStep 294299 = 441449) B441449
theorem B1277345 : Blo 195805 1277345 := bstep (se 2 (by rfl) ⟨479004, by rfl⟩ : syracuseStep 1277345 = 958009) B958009
theorem B294377 : Blo 195805 294377 := bstep (se 2 (by rfl) ⟨110391, by rfl⟩ : syracuseStep 294377 = 220783) B220783
theorem B196079 : Blo 195805 196079 := bstep (se 1 (by rfl) ⟨147059, by rfl⟩ : syracuseStep 196079 = 294119) B294119
theorem B294383 : Blo 195805 294383 := bstep (se 1 (by rfl) ⟨220787, by rfl⟩ : syracuseStep 294383 = 441575) B441575
theorem B294521 : Blo 195805 294521 := bstep (se 2 (by rfl) ⟨110445, by rfl⟩ : syracuseStep 294521 = 220891) B220891
theorem B196415 : Blo 195805 196415 := bstep (se 1 (by rfl) ⟨147311, by rfl⟩ : syracuseStep 196415 = 294623) B294623
theorem B294719 : Blo 195805 294719 := bstep (se 1 (by rfl) ⟨221039, by rfl⟩ : syracuseStep 294719 = 442079) B442079
theorem B196443 : Blo 195805 196443 := bstep (se 1 (by rfl) ⟨147332, by rfl⟩ : syracuseStep 196443 = 294665) B294665
theorem B294767 : Blo 195805 294767 := bstep (se 1 (by rfl) ⟨221075, by rfl⟩ : syracuseStep 294767 = 442151) B442151
theorem B295007 : Blo 195805 295007 := bstep (se 1 (by rfl) ⟨221255, by rfl⟩ : syracuseStep 295007 = 442511) B442511
theorem B295049 : Blo 195805 295049 := bstep (se 2 (by rfl) ⟨110643, by rfl⟩ : syracuseStep 295049 = 221287) B221287
theorem B295067 : Blo 195805 295067 := bstep (se 1 (by rfl) ⟨221300, by rfl⟩ : syracuseStep 295067 = 442601) B442601
theorem B196967 : Blo 195805 196967 := bstep (se 1 (by rfl) ⟨147725, by rfl⟩ : syracuseStep 196967 = 295451) B295451
theorem B197087 : Blo 195805 197087 := bstep (se 1 (by rfl) ⟨147815, by rfl⟩ : syracuseStep 197087 = 295631) B295631
theorem B197167 : Blo 195805 197167 := bstep (se 1 (by rfl) ⟨147875, by rfl⟩ : syracuseStep 197167 = 295751) B295751
theorem B197211 : Blo 195805 197211 := bstep (se 1 (by rfl) ⟨147908, by rfl⟩ : syracuseStep 197211 = 295817) B295817
theorem B197375 : Blo 195805 197375 := bstep (se 1 (by rfl) ⟨148031, by rfl⟩ : syracuseStep 197375 = 296063) B296063
theorem B197467 : Blo 195805 197467 := bstep (se 1 (by rfl) ⟨148100, by rfl⟩ : syracuseStep 197467 = 296201) B296201
theorem B197787 : Blo 195805 197787 := bstep (se 1 (by rfl) ⟨148340, by rfl⟩ : syracuseStep 197787 = 296681) B296681
theorem B197791 : Blo 195805 197791 := bstep (se 1 (by rfl) ⟨148343, by rfl⟩ : syracuseStep 197791 = 296687) B296687
theorem B1508543 : Blo 195805 1508543 := bstep (se 1 (by rfl) ⟨1131407, by rfl⟩ : syracuseStep 1508543 = 2262815) B2262815
theorem B296255 : Blo 195805 296255 := bstep (se 1 (by rfl) ⟨222191, by rfl⟩ : syracuseStep 296255 = 444383) B444383
theorem B197959 : Blo 195805 197959 := bstep (se 1 (by rfl) ⟨148469, by rfl⟩ : syracuseStep 197959 = 296939) B296939
theorem B1705313 : Blo 195805 1705313 := bstep (se 2 (by rfl) ⟨639492, by rfl⟩ : syracuseStep 1705313 = 1278985) B1278985
theorem B296399 : Blo 195805 296399 := bstep (se 1 (by rfl) ⟨222299, by rfl⟩ : syracuseStep 296399 = 444599) B444599
theorem B198127 : Blo 195805 198127 := bstep (se 1 (by rfl) ⟨148595, by rfl⟩ : syracuseStep 198127 = 297191) B297191
theorem B198143 : Blo 195805 198143 := bstep (se 1 (by rfl) ⟨148607, by rfl⟩ : syracuseStep 198143 = 297215) B297215
theorem B198235 : Blo 195805 198235 := bstep (se 1 (by rfl) ⟨148676, by rfl⟩ : syracuseStep 198235 = 297353) B297353
theorem B296585 : Blo 195805 296585 := bstep (se 2 (by rfl) ⟨111219, by rfl⟩ : syracuseStep 296585 = 222439) B222439
theorem B296927 : Blo 195805 296927 := bstep (se 1 (by rfl) ⟨222695, by rfl⟩ : syracuseStep 296927 = 445391) B445391
theorem B296987 : Blo 195805 296987 := bstep (se 1 (by rfl) ⟨222740, by rfl⟩ : syracuseStep 296987 = 445481) B445481
theorem B1050769 : Blo 195805 1050769 := bstep (se 2 (by rfl) ⟨394038, by rfl⟩ : syracuseStep 1050769 = 788077) B788077
theorem B297167 : Blo 195805 297167 := bstep (se 1 (by rfl) ⟨222875, by rfl⟩ : syracuseStep 297167 = 445751) B445751
theorem B198975 : Blo 195805 198975 := bstep (se 1 (by rfl) ⟨149231, by rfl⟩ : syracuseStep 198975 = 298463) B298463
theorem B199015 : Blo 195805 199015 := bstep (se 1 (by rfl) ⟨149261, by rfl⟩ : syracuseStep 199015 = 298523) B298523
theorem B199103 : Blo 195805 199103 := bstep (se 1 (by rfl) ⟨149327, by rfl⟩ : syracuseStep 199103 = 298655) B298655
theorem B199279 : Blo 195805 199279 := bstep (se 1 (by rfl) ⟨149459, by rfl⟩ : syracuseStep 199279 = 298919) B298919
theorem B199295 : Blo 195805 199295 := bstep (se 1 (by rfl) ⟨149471, by rfl⟩ : syracuseStep 199295 = 298943) B298943
theorem B199399 : Blo 195805 199399 := bstep (se 1 (by rfl) ⟨149549, by rfl⟩ : syracuseStep 199399 = 299099) B299099
theorem B330473 : Blo 195805 330473 := bstep (se 2 (by rfl) ⟨123927, by rfl⟩ : syracuseStep 330473 = 247855) B247855
theorem B330527 : Blo 195805 330527 := bstep (se 1 (by rfl) ⟨247895, by rfl⟩ : syracuseStep 330527 = 495791) B495791
theorem B1116989 : Blo 195805 1116989 := bstep (se 3 (by rfl) ⟨209435, by rfl⟩ : syracuseStep 1116989 = 418871) B418871
theorem B199495 : Blo 195805 199495 := bstep (se 1 (by rfl) ⟨149621, by rfl⟩ : syracuseStep 199495 = 299243) B299243
theorem B199535 : Blo 195805 199535 := bstep (se 1 (by rfl) ⟨149651, by rfl⟩ : syracuseStep 199535 = 299303) B299303
theorem B199711 : Blo 195805 199711 := bstep (se 1 (by rfl) ⟨149783, by rfl⟩ : syracuseStep 199711 = 299567) B299567
theorem B332059 : Blo 195805 332059 := bstep (se 1 (by rfl) ⟨249044, by rfl⟩ : syracuseStep 332059 = 498089) B498089
theorem B1413719 : Blo 195805 1413719 := bstep (se 1 (by rfl) ⟨1060289, by rfl⟩ : syracuseStep 1413719 = 2120579) B2120579
theorem B333065 : Blo 195805 333065 := bstep (se 2 (by rfl) ⟨124899, by rfl⟩ : syracuseStep 333065 = 249799) B249799
theorem B398639 : Blo 195805 398639 := bstep (se 1 (by rfl) ⟨298979, by rfl⟩ : syracuseStep 398639 = 597959) B597959
theorem B661121 : Blo 195805 661121 := bstep (se 2 (by rfl) ⟨247920, by rfl⟩ : syracuseStep 661121 = 495841) B495841
theorem B759547 : Blo 195805 759547 := bstep (se 1 (by rfl) ⟨569660, by rfl⟩ : syracuseStep 759547 = 1139321) B1139321
theorem B661607 : Blo 195805 661607 := bstep (se 1 (by rfl) ⟨496205, by rfl⟩ : syracuseStep 661607 = 992411) B992411
theorem B497947 : Blo 195805 497947 := bstep (se 1 (by rfl) ⟨373460, by rfl⟩ : syracuseStep 497947 = 746921) B746921
theorem B661985 : Blo 195805 661985 := bstep (se 2 (by rfl) ⟨248244, by rfl⟩ : syracuseStep 661985 = 496489) B496489
theorem B17406515 : Blo 195805 17406515 := bstep (se 1 (by rfl) ⟨13054886, by rfl⟩ : syracuseStep 17406515 = 26109773) B26109773
theorem B334631 : Blo 195805 334631 := bstep (se 1 (by rfl) ⟨250973, by rfl⟩ : syracuseStep 334631 = 501947) B501947
theorem B1121111 : Blo 195805 1121111 := bstep (se 1 (by rfl) ⟨840833, by rfl⟩ : syracuseStep 1121111 = 1681667) B1681667
theorem B10263455 : Blo 195805 10263455 := bstep (se 1 (by rfl) ⟨7697591, by rfl⟩ : syracuseStep 10263455 = 15395183) B15395183
theorem B334921 : Blo 195805 334921 := bstep (se 2 (by rfl) ⟨125595, by rfl⟩ : syracuseStep 334921 = 251191) B251191
theorem B498919 : Blo 195805 498919 := bstep (se 1 (by rfl) ⟨374189, by rfl⟩ : syracuseStep 498919 = 748379) B748379
theorem B630011 : Blo 195805 630011 := bstep (se 1 (by rfl) ⟨472508, by rfl⟩ : syracuseStep 630011 = 945017) B945017
theorem B630089 : Blo 195805 630089 := bstep (se 2 (by rfl) ⟨236283, by rfl⟩ : syracuseStep 630089 = 472567) B472567
theorem B335515 : Blo 195805 335515 := bstep (se 1 (by rfl) ⟨251636, by rfl⟩ : syracuseStep 335515 = 503273) B503273
theorem B335927 : Blo 195805 335927 := bstep (se 1 (by rfl) ⟨251945, by rfl⟩ : syracuseStep 335927 = 503891) B503891
theorem B664091 : Blo 195805 664091 := bstep (se 1 (by rfl) ⟨498068, by rfl⟩ : syracuseStep 664091 = 996137) B996137
theorem B565967 : Blo 195805 565967 := bstep (se 1 (by rfl) ⟨424475, by rfl⟩ : syracuseStep 565967 = 848951) B848951
theorem B2826971 : Blo 195805 2826971 := bstep (se 1 (by rfl) ⟨2120228, by rfl⟩ : syracuseStep 2826971 = 4240457) B4240457
theorem B1516319 : Blo 195805 1516319 := bstep (se 1 (by rfl) ⟨1137239, by rfl⟩ : syracuseStep 1516319 = 2274479) B2274479
theorem B796061 : Blo 195805 796061 := bstep (se 3 (by rfl) ⟨149261, by rfl⟩ : syracuseStep 796061 = 298523) B298523
theorem B1419227 : Blo 195805 1419227 := bstep (se 1 (by rfl) ⟨1064420, by rfl⟩ : syracuseStep 1419227 = 2128841) B2128841
theorem B666089 : Blo 195805 666089 := bstep (se 2 (by rfl) ⟨249783, by rfl⟩ : syracuseStep 666089 = 499567) B499567
theorem B2861689 : Blo 195805 2861689 := bstep (se 2 (by rfl) ⟨1073133, by rfl⟩ : syracuseStep 2861689 = 2146267) B2146267
theorem B502433 : Blo 195805 502433 := bstep (se 2 (by rfl) ⟨188412, by rfl⟩ : syracuseStep 502433 = 376825) B376825
theorem B4533083 : Blo 195805 4533083 := bstep (se 1 (by rfl) ⟨3399812, by rfl⟩ : syracuseStep 4533083 = 6799625) B6799625
theorem B502625 : Blo 195805 502625 := bstep (se 2 (by rfl) ⟨188484, by rfl⟩ : syracuseStep 502625 = 376969) B376969
theorem B503131 : Blo 195805 503131 := bstep (se 1 (by rfl) ⟨377348, by rfl⟩ : syracuseStep 503131 = 754697) B754697
theorem B1912409 : Blo 195805 1912409 := bstep (se 2 (by rfl) ⟨717153, by rfl⟩ : syracuseStep 1912409 = 1434307) B1434307
theorem B2273021 : Blo 195805 2273021 := bstep (se 3 (by rfl) ⟨426191, by rfl⟩ : syracuseStep 2273021 = 852383) B852383
theorem B339839 : Blo 195805 339839 := bstep (se 1 (by rfl) ⟨254879, by rfl⟩ : syracuseStep 339839 = 509759) B509759
theorem B2404333 : Blo 195805 2404333 := bstep (se 3 (by rfl) ⟨450812, by rfl⟩ : syracuseStep 2404333 = 901625) B901625
theorem B536719 : Blo 195805 536719 := bstep (se 1 (by rfl) ⟨402539, by rfl⟩ : syracuseStep 536719 = 805079) B805079
theorem B4468931 : Blo 195805 4468931 := bstep (se 1 (by rfl) ⟨3351698, by rfl⟩ : syracuseStep 4468931 = 6703397) B6703397
theorem B3354857 : Blo 195805 3354857 := bstep (se 2 (by rfl) ⟨1258071, by rfl⟩ : syracuseStep 3354857 = 2516143) B2516143
theorem B504539 : Blo 195805 504539 := bstep (se 1 (by rfl) ⟨378404, by rfl⟩ : syracuseStep 504539 = 756809) B756809
theorem B668411 : Blo 195805 668411 := bstep (se 1 (by rfl) ⟨501308, by rfl⟩ : syracuseStep 668411 = 1002617) B1002617
theorem B897961 : Blo 195805 897961 := bstep (se 2 (by rfl) ⟨336735, by rfl⟩ : syracuseStep 897961 = 673471) B673471
theorem B996461 : Blo 195805 996461 := bstep (se 3 (by rfl) ⟨186836, by rfl⟩ : syracuseStep 996461 = 373673) B373673
theorem B669167 : Blo 195805 669167 := bstep (se 1 (by rfl) ⟨501875, by rfl⟩ : syracuseStep 669167 = 1003751) B1003751
theorem B636407 : Blo 195805 636407 := bstep (se 1 (by rfl) ⟨477305, by rfl⟩ : syracuseStep 636407 = 954611) B954611
theorem B505511 : Blo 195805 505511 := bstep (se 1 (by rfl) ⟨379133, by rfl⟩ : syracuseStep 505511 = 758267) B758267
theorem B538319 : Blo 195805 538319 := bstep (se 1 (by rfl) ⟨403739, by rfl⟩ : syracuseStep 538319 = 807479) B807479
theorem B440603 : Blo 195805 440603 := bstep (se 1 (by rfl) ⟨330452, by rfl⟩ : syracuseStep 440603 = 660905) B660905
theorem B440639 : Blo 195805 440639 := bstep (se 1 (by rfl) ⟨330479, by rfl⟩ : syracuseStep 440639 = 660959) B660959
theorem B3422537 : Blo 195805 3422537 := bstep (se 2 (by rfl) ⟨1283451, by rfl⟩ : syracuseStep 3422537 = 2566903) B2566903
theorem B997919 : Blo 195805 997919 := bstep (se 1 (by rfl) ⟨748439, by rfl⟩ : syracuseStep 997919 = 1496879) B1496879
theorem B1129085 : Blo 195805 1129085 := bstep (se 3 (by rfl) ⟨211703, by rfl⟩ : syracuseStep 1129085 = 423407) B423407
theorem B441143 : Blo 195805 441143 := bstep (se 1 (by rfl) ⟨330857, by rfl⟩ : syracuseStep 441143 = 661715) B661715
theorem B6372371 : Blo 195805 6372371 := bstep (se 1 (by rfl) ⟨4779278, by rfl⟩ : syracuseStep 6372371 = 9558557) B9558557
theorem B671165 : Blo 195805 671165 := bstep (se 3 (by rfl) ⟨125843, by rfl⟩ : syracuseStep 671165 = 251687) B251687
theorem B6405587 : Blo 195805 6405587 := bstep (se 1 (by rfl) ⟨4804190, by rfl⟩ : syracuseStep 6405587 = 9608381) B9608381
theorem B1490561 : Blo 195805 1490561 := bstep (se 2 (by rfl) ⟨558960, by rfl⟩ : syracuseStep 1490561 = 1117921) B1117921
theorem B442223 : Blo 195805 442223 := bstep (se 1 (by rfl) ⟨331667, by rfl⟩ : syracuseStep 442223 = 663335) B663335
theorem B475411 : Blo 195805 475411 := bstep (se 1 (by rfl) ⟨356558, by rfl⟩ : syracuseStep 475411 = 713117) B713117
theorem B672083 : Blo 195805 672083 := bstep (se 1 (by rfl) ⟨504062, by rfl⟩ : syracuseStep 672083 = 1008125) B1008125
theorem B672191 : Blo 195805 672191 := bstep (se 1 (by rfl) ⟨504143, by rfl⟩ : syracuseStep 672191 = 1008287) B1008287
theorem B1000511 : Blo 195805 1000511 := bstep (se 1 (by rfl) ⟨750383, by rfl⟩ : syracuseStep 1000511 = 1500767) B1500767
theorem B2049185 : Blo 195805 2049185 := bstep (se 2 (by rfl) ⟨768444, by rfl⟩ : syracuseStep 2049185 = 1536889) B1536889
theorem B443879 : Blo 195805 443879 := bstep (se 1 (by rfl) ⟨332909, by rfl⟩ : syracuseStep 443879 = 665819) B665819
theorem B706283 : Blo 195805 706283 := bstep (se 1 (by rfl) ⟨529712, by rfl⟩ : syracuseStep 706283 = 1059425) B1059425
theorem B674297 : Blo 195805 674297 := bstep (se 2 (by rfl) ⟨252861, by rfl⟩ : syracuseStep 674297 = 505723) B505723
theorem B445247 : Blo 195805 445247 := bstep (se 1 (by rfl) ⟨333935, by rfl⟩ : syracuseStep 445247 = 667871) B667871
theorem B445715 : Blo 195805 445715 := bstep (se 1 (by rfl) ⟨334286, by rfl⟩ : syracuseStep 445715 = 668573) B668573
theorem B446183 : Blo 195805 446183 := bstep (se 1 (by rfl) ⟨334637, by rfl⟩ : syracuseStep 446183 = 669275) B669275
theorem B2543605 : Blo 195805 2543605 := bstep (se 5 (by rfl) ⟨119231, by rfl⟩ : syracuseStep 2543605 = 238463) B238463
theorem B3199027 : Blo 195805 3199027 := bstep (se 1 (by rfl) ⟨2399270, by rfl⟩ : syracuseStep 3199027 = 4798541) B4798541
theorem B1265863 : Blo 195805 1265863 := bstep (se 1 (by rfl) ⟨949397, by rfl⟩ : syracuseStep 1265863 = 1898795) B1898795
theorem B1004399 : Blo 195805 1004399 := bstep (se 1 (by rfl) ⟨753299, by rfl⟩ : syracuseStep 1004399 = 1506599) B1506599
theorem B283513 : Blo 195805 283513 := bstep (se 2 (by rfl) ⟨106317, by rfl⟩ : syracuseStep 283513 = 212635) B212635
theorem B1496393 : Blo 195805 1496393 := bstep (se 2 (by rfl) ⟨561147, by rfl⟩ : syracuseStep 1496393 = 1122295) B1122295
theorem B19355041 : Blo 195805 19355041 := bstep (se 2 (by rfl) ⟨7258140, by rfl⟩ : syracuseStep 19355041 = 14516281) B14516281
theorem B841211 : Blo 195805 841211 := bstep (se 1 (by rfl) ⟨630908, by rfl⟩ : syracuseStep 841211 = 1261817) B1261817
theorem B448073 : Blo 195805 448073 := bstep (se 2 (by rfl) ⟨168027, by rfl⟩ : syracuseStep 448073 = 336055) B336055
theorem B1136375 : Blo 195805 1136375 := bstep (se 1 (by rfl) ⟨852281, by rfl⟩ : syracuseStep 1136375 = 1704563) B1704563
theorem B317351 : Blo 195805 317351 := bstep (se 1 (by rfl) ⟨238013, by rfl⟩ : syracuseStep 317351 = 476027) B476027
theorem B1268095 : Blo 195805 1268095 := bstep (se 1 (by rfl) ⟨951071, by rfl⟩ : syracuseStep 1268095 = 1902143) B1902143
theorem B11819641 : Blo 195805 11819641 := bstep (se 2 (by rfl) ⟨4432365, by rfl⟩ : syracuseStep 11819641 = 8864731) B8864731
theorem B7232273 : Blo 195805 7232273 := bstep (se 2 (by rfl) ⟨2712102, by rfl⟩ : syracuseStep 7232273 = 5424205) B5424205
theorem B842663 : Blo 195805 842663 := bstep (se 1 (by rfl) ⟨631997, by rfl⟩ : syracuseStep 842663 = 1263995) B1263995
theorem B1006505 : Blo 195805 1006505 := bstep (se 2 (by rfl) ⟨377439, by rfl⟩ : syracuseStep 1006505 = 754879) B754879
theorem B842815 : Blo 195805 842815 := bstep (se 1 (by rfl) ⟨632111, by rfl⟩ : syracuseStep 842815 = 1264223) B1264223
theorem B100228913 : Blo 195805 100228913 := bstep (se 2 (by rfl) ⟨37585842, by rfl⟩ : syracuseStep 100228913 = 75171685) B75171685
theorem B221179 : Blo 195805 221179 := bstep (se 1 (by rfl) ⟨165884, by rfl⟩ : syracuseStep 221179 = 331769) B331769
theorem B221359 : Blo 195805 221359 := bstep (se 1 (by rfl) ⟨166019, by rfl⟩ : syracuseStep 221359 = 332039) B332039
theorem B6480323 : Blo 195805 6480323 := bstep (se 1 (by rfl) ⟨4860242, by rfl⟩ : syracuseStep 6480323 = 9720485) B9720485
theorem B647687 : Blo 195805 647687 := bstep (se 1 (by rfl) ⟨485765, by rfl⟩ : syracuseStep 647687 = 971531) B971531
theorem B222079 : Blo 195805 222079 := bstep (se 1 (by rfl) ⟨166559, by rfl⟩ : syracuseStep 222079 = 333119) B333119
theorem B1270889 : Blo 195805 1270889 := bstep (se 2 (by rfl) ⟨476583, by rfl⟩ : syracuseStep 1270889 = 953167) B953167
theorem B1009583 : Blo 195805 1009583 := bstep (se 1 (by rfl) ⟨757187, by rfl⟩ : syracuseStep 1009583 = 1514375) B1514375
theorem B224167 : Blo 195805 224167 := bstep (se 1 (by rfl) ⟨168125, by rfl⟩ : syracuseStep 224167 = 336251) B336251
theorem B224347 : Blo 195805 224347 := bstep (se 1 (by rfl) ⟨168260, by rfl⟩ : syracuseStep 224347 = 336521) B336521
theorem B1699163 : Blo 195805 1699163 := bstep (se 1 (by rfl) ⟨1274372, by rfl⟩ : syracuseStep 1699163 = 2548745) B2548745
theorem B847361 : Blo 195805 847361 := bstep (se 2 (by rfl) ⟨317760, by rfl⟩ : syracuseStep 847361 = 635521) B635521
theorem B716431 : Blo 195805 716431 := bstep (se 1 (by rfl) ⟨537323, by rfl⟩ : syracuseStep 716431 = 1074647) B1074647
theorem B4551389 : Blo 195805 4551389 := bstep (se 3 (by rfl) ⟨853385, by rfl⟩ : syracuseStep 4551389 = 1706771) B1706771
theorem B750491 : Blo 195805 750491 := bstep (se 1 (by rfl) ⟨562868, by rfl⟩ : syracuseStep 750491 = 1125737) B1125737
theorem B849001 : Blo 195805 849001 := bstep (se 2 (by rfl) ⟨318375, by rfl⟩ : syracuseStep 849001 = 636751) B636751
theorem B1603475 : Blo 195805 1603475 := bstep (se 1 (by rfl) ⟨1202606, by rfl⟩ : syracuseStep 1603475 = 2405213) B2405213
theorem B358735 : Blo 195805 358735 := bstep (se 1 (by rfl) ⟨269051, by rfl⟩ : syracuseStep 358735 = 538103) B538103
theorem B850283 : Blo 195805 850283 := bstep (se 1 (by rfl) ⟨637712, by rfl⟩ : syracuseStep 850283 = 1275425) B1275425
theorem B424415 : Blo 195805 424415 := bstep (se 1 (by rfl) ⟨318311, by rfl⟩ : syracuseStep 424415 = 636623) B636623
theorem B3046187 : Blo 195805 3046187 := bstep (se 1 (by rfl) ⟨2284640, by rfl⟩ : syracuseStep 3046187 = 4569281) B4569281
theorem B195903 : Blo 195805 195903 := bstep (se 1 (by rfl) ⟨146927, by rfl⟩ : syracuseStep 195903 = 293855) B293855
theorem B195943 : Blo 195805 195943 := bstep (se 1 (by rfl) ⟨146957, by rfl⟩ : syracuseStep 195943 = 293915) B293915
theorem B196199 : Blo 195805 196199 := bstep (se 1 (by rfl) ⟨147149, by rfl⟩ : syracuseStep 196199 = 294299) B294299
theorem B851563 : Blo 195805 851563 := bstep (se 1 (by rfl) ⟨638672, by rfl⟩ : syracuseStep 851563 = 1277345) B1277345
theorem B196251 : Blo 195805 196251 := bstep (se 1 (by rfl) ⟨147188, by rfl⟩ : syracuseStep 196251 = 294377) B294377
theorem B196255 : Blo 195805 196255 := bstep (se 1 (by rfl) ⟨147191, by rfl⟩ : syracuseStep 196255 = 294383) B294383
theorem B196347 : Blo 195805 196347 := bstep (se 1 (by rfl) ⟨147260, by rfl⟩ : syracuseStep 196347 = 294521) B294521
theorem B196479 : Blo 195805 196479 := bstep (se 1 (by rfl) ⟨147359, by rfl⟩ : syracuseStep 196479 = 294719) B294719
theorem B196511 : Blo 195805 196511 := bstep (se 1 (by rfl) ⟨147383, by rfl⟩ : syracuseStep 196511 = 294767) B294767
theorem B294887 : Blo 195805 294887 := bstep (se 1 (by rfl) ⟨221165, by rfl⟩ : syracuseStep 294887 = 442331) B442331
theorem B196671 : Blo 195805 196671 := bstep (se 1 (by rfl) ⟨147503, by rfl⟩ : syracuseStep 196671 = 295007) B295007
theorem B196699 : Blo 195805 196699 := bstep (se 1 (by rfl) ⟨147524, by rfl⟩ : syracuseStep 196699 = 295049) B295049
theorem B196711 : Blo 195805 196711 := bstep (se 1 (by rfl) ⟨147533, by rfl⟩ : syracuseStep 196711 = 295067) B295067
theorem B295145 : Blo 195805 295145 := bstep (se 2 (by rfl) ⟨110679, by rfl⟩ : syracuseStep 295145 = 221359) B221359
theorem B197503 : Blo 195805 197503 := bstep (se 1 (by rfl) ⟨148127, by rfl⟩ : syracuseStep 197503 = 296255) B296255
theorem B197599 : Blo 195805 197599 := bstep (se 1 (by rfl) ⟨148199, by rfl⟩ : syracuseStep 197599 = 296399) B296399
theorem B295919 : Blo 195805 295919 := bstep (se 1 (by rfl) ⟨221939, by rfl⟩ : syracuseStep 295919 = 443879) B443879
theorem B197723 : Blo 195805 197723 := bstep (se 1 (by rfl) ⟨148292, by rfl⟩ : syracuseStep 197723 = 296585) B296585
theorem B296105 : Blo 195805 296105 := bstep (se 2 (by rfl) ⟨111039, by rfl⟩ : syracuseStep 296105 = 222079) B222079
theorem B197951 : Blo 195805 197951 := bstep (se 1 (by rfl) ⟨148463, by rfl⟩ : syracuseStep 197951 = 296927) B296927
theorem B197991 : Blo 195805 197991 := bstep (se 1 (by rfl) ⟨148493, by rfl⟩ : syracuseStep 197991 = 296987) B296987
theorem B198111 : Blo 195805 198111 := bstep (se 1 (by rfl) ⟨148583, by rfl⟩ : syracuseStep 198111 = 297167) B297167
theorem B296831 : Blo 195805 296831 := bstep (se 1 (by rfl) ⟨222623, by rfl⟩ : syracuseStep 296831 = 445247) B445247
theorem B297143 : Blo 195805 297143 := bstep (se 1 (by rfl) ⟨222857, by rfl⟩ : syracuseStep 297143 = 445715) B445715
theorem B297455 : Blo 195805 297455 := bstep (se 1 (by rfl) ⟨223091, by rfl⟩ : syracuseStep 297455 = 446183) B446183
theorem B560807 : Blo 195805 560807 := bstep (se 1 (by rfl) ⟨420605, by rfl⟩ : syracuseStep 560807 = 841211) B841211
theorem B298715 : Blo 195805 298715 := bstep (se 1 (by rfl) ⟨224036, by rfl⟩ : syracuseStep 298715 = 448073) B448073
theorem B757583 : Blo 195805 757583 := bstep (se 1 (by rfl) ⟨568187, by rfl⟩ : syracuseStep 757583 = 1136375) B1136375
theorem B298889 : Blo 195805 298889 := bstep (se 2 (by rfl) ⟨112083, by rfl⟩ : syracuseStep 298889 = 224167) B224167
theorem B299129 : Blo 195805 299129 := bstep (se 2 (by rfl) ⟨112173, by rfl⟩ : syracuseStep 299129 = 224347) B224347
theorem B11604343 : Blo 195805 11604343 := bstep (se 1 (by rfl) ⟨8703257, by rfl⟩ : syracuseStep 11604343 = 17406515) B17406515
theorem B4821515 : Blo 195805 4821515 := bstep (se 1 (by rfl) ⟨3616136, by rfl⟩ : syracuseStep 4821515 = 7232273) B7232273
theorem B561775 : Blo 195805 561775 := bstep (se 1 (by rfl) ⟨421331, by rfl⟩ : syracuseStep 561775 = 842663) B842663
theorem B955241 : Blo 195805 955241 := bstep (se 2 (by rfl) ⟨358215, by rfl⟩ : syracuseStep 955241 = 716431) B716431
theorem B66819275 : Blo 195805 66819275 := bstep (se 1 (by rfl) ⟨50114456, by rfl⟩ : syracuseStep 66819275 = 100228913) B100228913
theorem B4265369 : Blo 195805 4265369 := bstep (se 2 (by rfl) ⟨1599513, by rfl⟩ : syracuseStep 4265369 = 3199027) B3199027
theorem B530707 : Blo 195805 530707 := bstep (se 1 (by rfl) ⟨398030, by rfl⟩ : syracuseStep 530707 = 796061) B796061
theorem B334955 : Blo 195805 334955 := bstep (se 1 (by rfl) ⟨251216, by rfl⟩ : syracuseStep 334955 = 502433) B502433
theorem B3022055 : Blo 195805 3022055 := bstep (se 1 (by rfl) ⟨2266541, by rfl⟩ : syracuseStep 3022055 = 4533083) B4533083
theorem B335083 : Blo 195805 335083 := bstep (se 1 (by rfl) ⟨251312, by rfl⟩ : syracuseStep 335083 = 502625) B502625
theorem B564907 : Blo 195805 564907 := bstep (se 1 (by rfl) ⟨423680, by rfl⟩ : syracuseStep 564907 = 847361) B847361
theorem B1515347 : Blo 195805 1515347 := bstep (se 1 (by rfl) ⟨1136510, by rfl⟩ : syracuseStep 1515347 = 2273021) B2273021
theorem B2236571 : Blo 195805 2236571 := bstep (se 1 (by rfl) ⟨1677428, by rfl⟩ : syracuseStep 2236571 = 3354857) B3354857
theorem B663929 : Blo 195805 663929 := bstep (se 2 (by rfl) ⟨248973, by rfl⟩ : syracuseStep 663929 = 497947) B497947
theorem B336359 : Blo 195805 336359 := bstep (se 1 (by rfl) ⟨252269, by rfl⟩ : syracuseStep 336359 = 504539) B504539
theorem B500327 : Blo 195805 500327 := bstep (se 1 (by rfl) ⟨375245, by rfl⟩ : syracuseStep 500327 = 750491) B750491
theorem B664307 : Blo 195805 664307 := bstep (se 1 (by rfl) ⟨498230, by rfl⟩ : syracuseStep 664307 = 996461) B996461
theorem B337007 : Blo 195805 337007 := bstep (se 1 (by rfl) ⟨252755, by rfl⟩ : syracuseStep 337007 = 505511) B505511
theorem B1123753 : Blo 195805 1123753 := bstep (se 2 (by rfl) ⟨421407, by rfl⟩ : syracuseStep 1123753 = 842815) B842815
theorem B566855 : Blo 195805 566855 := bstep (se 1 (by rfl) ⟨425141, by rfl⟩ : syracuseStep 566855 = 850283) B850283
theorem B665225 : Blo 195805 665225 := bstep (se 2 (by rfl) ⟨249459, by rfl⟩ : syracuseStep 665225 = 498919) B498919
theorem B665279 : Blo 195805 665279 := bstep (se 1 (by rfl) ⟨498959, by rfl⟩ : syracuseStep 665279 = 997919) B997919
theorem B4270391 : Blo 195805 4270391 := bstep (se 1 (by rfl) ⟨3202793, by rfl⟩ : syracuseStep 4270391 = 6405587) B6405587
theorem B993707 : Blo 195805 993707 := bstep (se 1 (by rfl) ⟨745280, by rfl⟩ : syracuseStep 993707 = 1490561) B1490561
theorem B633881 : Blo 195805 633881 := bstep (se 2 (by rfl) ⟨237705, by rfl⟩ : syracuseStep 633881 = 475411) B475411
theorem B667007 : Blo 195805 667007 := bstep (se 1 (by rfl) ⟨500255, by rfl⟩ : syracuseStep 667007 = 1000511) B1000511
theorem B470855 : Blo 195805 470855 := bstep (se 1 (by rfl) ⟨353141, by rfl⟩ : syracuseStep 470855 = 706283) B706283
theorem B669599 : Blo 195805 669599 := bstep (se 1 (by rfl) ⟨502199, by rfl⟩ : syracuseStep 669599 = 1004399) B1004399
theorem B1063037 : Blo 195805 1063037 := bstep (se 3 (by rfl) ⟨199319, by rfl⟩ : syracuseStep 1063037 = 398639) B398639
theorem B3815585 : Blo 195805 3815585 := bstep (se 2 (by rfl) ⟨1430844, by rfl⟩ : syracuseStep 3815585 = 2861689) B2861689
theorem B997595 : Blo 195805 997595 := bstep (se 1 (by rfl) ⟨748196, by rfl⟩ : syracuseStep 997595 = 1496393) B1496393
theorem B440747 : Blo 195805 440747 := bstep (se 1 (by rfl) ⟨330560, by rfl⟩ : syracuseStep 440747 = 661121) B661121
theorem B211567 : Blo 195805 211567 := bstep (se 1 (by rfl) ⟨158675, by rfl⟩ : syracuseStep 211567 = 317351) B317351
theorem B441071 : Blo 195805 441071 := bstep (se 1 (by rfl) ⟨330803, by rfl⟩ : syracuseStep 441071 = 661607) B661607
theorem B441323 : Blo 195805 441323 := bstep (se 1 (by rfl) ⟨330992, by rfl⟩ : syracuseStep 441323 = 661985) B661985
theorem B670841 : Blo 195805 670841 := bstep (se 2 (by rfl) ⟨251565, by rfl⟩ : syracuseStep 670841 = 503131) B503131
theorem B671003 : Blo 195805 671003 := bstep (se 1 (by rfl) ⟨503252, by rfl⟩ : syracuseStep 671003 = 1006505) B1006505
theorem B1687817 : Blo 195805 1687817 := bstep (se 2 (by rfl) ⟨632931, by rfl⟩ : syracuseStep 1687817 = 1265863) B1265863
theorem B442727 : Blo 195805 442727 := bstep (se 1 (by rfl) ⟨332045, by rfl⟩ : syracuseStep 442727 = 664091) B664091
theorem B442745 : Blo 195805 442745 := bstep (se 2 (by rfl) ⟨166029, by rfl⟩ : syracuseStep 442745 = 332059) B332059
theorem B377311 : Blo 195805 377311 := bstep (se 1 (by rfl) ⟨282983, by rfl⟩ : syracuseStep 377311 = 565967) B565967
theorem B1884647 : Blo 195805 1884647 := bstep (se 1 (by rfl) ⟨1413485, by rfl⟩ : syracuseStep 1884647 = 2826971) B2826971
theorem B378017 : Blo 195805 378017 := bstep (se 2 (by rfl) ⟨141756, by rfl⟩ : syracuseStep 378017 = 283513) B283513
theorem B1197281 : Blo 195805 1197281 := bstep (se 2 (by rfl) ⟨448980, by rfl⟩ : syracuseStep 1197281 = 897961) B897961
theorem B673055 : Blo 195805 673055 := bstep (se 1 (by rfl) ⟨504791, by rfl⟩ : syracuseStep 673055 = 1009583) B1009583
theorem B1132001 : Blo 195805 1132001 := bstep (se 2 (by rfl) ⟨424500, by rfl⟩ : syracuseStep 1132001 = 849001) B849001
theorem B444059 : Blo 195805 444059 := bstep (se 1 (by rfl) ⟨333044, by rfl⟩ : syracuseStep 444059 = 666089) B666089
theorem B25806721 : Blo 195805 25806721 := bstep (se 2 (by rfl) ⟨9677520, by rfl⟩ : syracuseStep 25806721 = 19355041) B19355041
theorem B1132775 : Blo 195805 1132775 := bstep (se 1 (by rfl) ⟨849581, by rfl⟩ : syracuseStep 1132775 = 1699163) B1699163
theorem B478313 : Blo 195805 478313 := bstep (se 2 (by rfl) ⟨179367, by rfl⟩ : syracuseStep 478313 = 358735) B358735
theorem B3034259 : Blo 195805 3034259 := bstep (se 1 (by rfl) ⟨2275694, by rfl⟩ : syracuseStep 3034259 = 4551389) B4551389
theorem B445607 : Blo 195805 445607 := bstep (se 1 (by rfl) ⟨334205, by rfl⟩ : syracuseStep 445607 = 668411) B668411
theorem B1690793 : Blo 195805 1690793 := bstep (se 2 (by rfl) ⟨634047, by rfl⟩ : syracuseStep 1690793 = 1268095) B1268095
theorem B446111 : Blo 195805 446111 := bstep (se 1 (by rfl) ⟨334583, by rfl⟩ : syracuseStep 446111 = 669167) B669167
theorem B1068983 : Blo 195805 1068983 := bstep (se 1 (by rfl) ⟨801737, by rfl⟩ : syracuseStep 1068983 = 1603475) B1603475
theorem B4050917 : Blo 195805 4050917 := bstep (se 4 (by rfl) ⟨379773, by rfl⟩ : syracuseStep 4050917 = 759547) B759547
theorem B446561 : Blo 195805 446561 := bstep (se 2 (by rfl) ⟨167460, by rfl⟩ : syracuseStep 446561 = 334921) B334921
theorem B2281691 : Blo 195805 2281691 := bstep (se 1 (by rfl) ⟨1711268, by rfl⟩ : syracuseStep 2281691 = 3422537) B3422537
theorem B282943 : Blo 195805 282943 := bstep (se 1 (by rfl) ⟨212207, by rfl⟩ : syracuseStep 282943 = 424415) B424415
theorem B4248247 : Blo 195805 4248247 := bstep (se 1 (by rfl) ⟨3186185, by rfl⟩ : syracuseStep 4248247 = 6372371) B6372371
theorem B1135417 : Blo 195805 1135417 := bstep (se 2 (by rfl) ⟨425781, by rfl⟩ : syracuseStep 1135417 = 851563) B851563
theorem B447353 : Blo 195805 447353 := bstep (se 2 (by rfl) ⟨167757, by rfl⟩ : syracuseStep 447353 = 335515) B335515
theorem B447443 : Blo 195805 447443 := bstep (se 1 (by rfl) ⟨335582, by rfl⟩ : syracuseStep 447443 = 671165) B671165
theorem B448055 : Blo 195805 448055 := bstep (se 1 (by rfl) ⟨336041, by rfl⟩ : syracuseStep 448055 = 672083) B672083
theorem B448127 : Blo 195805 448127 := bstep (se 1 (by rfl) ⟨336095, by rfl⟩ : syracuseStep 448127 = 672191) B672191
theorem B1005695 : Blo 195805 1005695 := bstep (se 1 (by rfl) ⟨754271, by rfl⟩ : syracuseStep 1005695 = 1508543) B1508543
theorem B1136875 : Blo 195805 1136875 := bstep (se 1 (by rfl) ⟨852656, by rfl⟩ : syracuseStep 1136875 = 1705313) B1705313
theorem B1727165 : Blo 195805 1727165 := bstep (se 3 (by rfl) ⟨323843, by rfl⟩ : syracuseStep 1727165 = 647687) B647687
theorem B449531 : Blo 195805 449531 := bstep (se 1 (by rfl) ⟨337148, by rfl⟩ : syracuseStep 449531 = 674297) B674297
theorem B220315 : Blo 195805 220315 := bstep (se 1 (by rfl) ⟨165236, by rfl⟩ : syracuseStep 220315 = 330473) B330473
theorem B220351 : Blo 195805 220351 := bstep (se 1 (by rfl) ⟨165263, by rfl⟩ : syracuseStep 220351 = 330527) B330527
theorem B744659 : Blo 195805 744659 := bstep (se 1 (by rfl) ⟨558494, by rfl⟩ : syracuseStep 744659 = 1116989) B1116989
theorem B1401025 : Blo 195805 1401025 := bstep (se 2 (by rfl) ⟨525384, by rfl⟩ : syracuseStep 1401025 = 1050769) B1050769
theorem B942479 : Blo 195805 942479 := bstep (se 1 (by rfl) ⟨706859, by rfl⟩ : syracuseStep 942479 = 1413719) B1413719
theorem B5464493 : Blo 195805 5464493 := bstep (se 3 (by rfl) ⟨1024592, by rfl⟩ : syracuseStep 5464493 = 2049185) B2049185
theorem B222043 : Blo 195805 222043 := bstep (se 1 (by rfl) ⟨166532, by rfl⟩ : syracuseStep 222043 = 333065) B333065
theorem B223087 : Blo 195805 223087 := bstep (se 1 (by rfl) ⟨167315, by rfl⟩ : syracuseStep 223087 = 334631) B334631
theorem B747407 : Blo 195805 747407 := bstep (se 1 (by rfl) ⟨560555, by rfl⟩ : syracuseStep 747407 = 1121111) B1121111
theorem B6842303 : Blo 195805 6842303 := bstep (se 1 (by rfl) ⟨5131727, by rfl⟩ : syracuseStep 6842303 = 10263455) B10263455
theorem B420007 : Blo 195805 420007 := bstep (se 1 (by rfl) ⟨315005, by rfl⟩ : syracuseStep 420007 = 630011) B630011
theorem B420059 : Blo 195805 420059 := bstep (se 1 (by rfl) ⟨315044, by rfl⟩ : syracuseStep 420059 = 630089) B630089
theorem B3205777 : Blo 195805 3205777 := bstep (se 2 (by rfl) ⟨1202166, by rfl⟩ : syracuseStep 3205777 = 2404333) B2404333
theorem B223951 : Blo 195805 223951 := bstep (se 1 (by rfl) ⟨167963, by rfl⟩ : syracuseStep 223951 = 335927) B335927
theorem B715625 : Blo 195805 715625 := bstep (se 2 (by rfl) ⟨268359, by rfl⟩ : syracuseStep 715625 = 536719) B536719
theorem B4320215 : Blo 195805 4320215 := bstep (se 1 (by rfl) ⟨3240161, by rfl⟩ : syracuseStep 4320215 = 6480323) B6480323
theorem B1010879 : Blo 195805 1010879 := bstep (se 1 (by rfl) ⟨758159, by rfl⟩ : syracuseStep 1010879 = 1516319) B1516319
theorem B847259 : Blo 195805 847259 := bstep (se 1 (by rfl) ⟨635444, by rfl⟩ : syracuseStep 847259 = 1270889) B1270889
theorem B946151 : Blo 195805 946151 := bstep (se 1 (by rfl) ⟨709613, by rfl⟩ : syracuseStep 946151 = 1419227) B1419227
theorem B1274939 : Blo 195805 1274939 := bstep (se 1 (by rfl) ⟨956204, by rfl⟩ : syracuseStep 1274939 = 1912409) B1912409
theorem B226559 : Blo 195805 226559 := bstep (se 1 (by rfl) ⟨169919, by rfl⟩ : syracuseStep 226559 = 339839) B339839
theorem B2979287 : Blo 195805 2979287 := bstep (se 1 (by rfl) ⟨2234465, by rfl⟩ : syracuseStep 2979287 = 4468931) B4468931
theorem B15759521 : Blo 195805 15759521 := bstep (se 2 (by rfl) ⟨5909820, by rfl⟩ : syracuseStep 15759521 = 11819641) B11819641
theorem B424271 : Blo 195805 424271 := bstep (se 1 (by rfl) ⟨318203, by rfl⟩ : syracuseStep 424271 = 636407) B636407
theorem B358879 : Blo 195805 358879 := bstep (se 1 (by rfl) ⟨269159, by rfl⟩ : syracuseStep 358879 = 538319) B538319
theorem B293735 : Blo 195805 293735 := bstep (se 1 (by rfl) ⟨220301, by rfl⟩ : syracuseStep 293735 = 440603) B440603
theorem B293759 : Blo 195805 293759 := bstep (se 1 (by rfl) ⟨220319, by rfl⟩ : syracuseStep 293759 = 440639) B440639
theorem B752723 : Blo 195805 752723 := bstep (se 1 (by rfl) ⟨564542, by rfl⟩ : syracuseStep 752723 = 1129085) B1129085
theorem B2030791 : Blo 195805 2030791 := bstep (se 1 (by rfl) ⟨1523093, by rfl⟩ : syracuseStep 2030791 = 3046187) B3046187
theorem B294095 : Blo 195805 294095 := bstep (se 1 (by rfl) ⟨220571, by rfl⟩ : syracuseStep 294095 = 441143) B441143
theorem B294815 : Blo 195805 294815 := bstep (se 1 (by rfl) ⟨221111, by rfl⟩ : syracuseStep 294815 = 442223) B442223
theorem B13565893 : Blo 195805 13565893 := bstep (se 4 (by rfl) ⟨1271802, by rfl⟩ : syracuseStep 13565893 = 2543605) B2543605
theorem B196591 : Blo 195805 196591 := bstep (se 1 (by rfl) ⟨147443, by rfl⟩ : syracuseStep 196591 = 294887) B294887
theorem B294905 : Blo 195805 294905 := bstep (se 2 (by rfl) ⟨110589, by rfl⟩ : syracuseStep 294905 = 221179) B221179
theorem B196763 : Blo 195805 196763 := bstep (se 1 (by rfl) ⟨147572, by rfl⟩ : syracuseStep 196763 = 295145) B295145
theorem B295151 : Blo 195805 295151 := bstep (se 1 (by rfl) ⟨221363, by rfl⟩ : syracuseStep 295151 = 442727) B442727
theorem B295163 : Blo 195805 295163 := bstep (se 1 (by rfl) ⟨221372, by rfl⟩ : syracuseStep 295163 = 442745) B442745
theorem B1868033 : Blo 195805 1868033 := bstep (se 2 (by rfl) ⟨700512, by rfl⟩ : syracuseStep 1868033 = 1401025) B1401025
theorem B197279 : Blo 195805 197279 := bstep (se 1 (by rfl) ⟨147959, by rfl⟩ : syracuseStep 197279 = 295919) B295919
theorem B197403 : Blo 195805 197403 := bstep (se 1 (by rfl) ⟨148052, by rfl⟩ : syracuseStep 197403 = 296105) B296105
theorem B754667 : Blo 195805 754667 := bstep (se 1 (by rfl) ⟨566000, by rfl⟩ : syracuseStep 754667 = 1132001) B1132001
theorem B296039 : Blo 195805 296039 := bstep (se 1 (by rfl) ⟨222029, by rfl⟩ : syracuseStep 296039 = 444059) B444059
theorem B296057 : Blo 195805 296057 := bstep (se 2 (by rfl) ⟨111021, by rfl⟩ : syracuseStep 296057 = 222043) B222043
theorem B197887 : Blo 195805 197887 := bstep (se 1 (by rfl) ⟨148415, by rfl⟩ : syracuseStep 197887 = 296831) B296831
theorem B198095 : Blo 195805 198095 := bstep (se 1 (by rfl) ⟨148571, by rfl⟩ : syracuseStep 198095 = 297143) B297143
theorem B755183 : Blo 195805 755183 := bstep (se 1 (by rfl) ⟨566387, by rfl⟩ : syracuseStep 755183 = 1132775) B1132775
theorem B198303 : Blo 195805 198303 := bstep (se 1 (by rfl) ⟨148727, by rfl⟩ : syracuseStep 198303 = 297455) B297455
theorem B1509029 : Blo 195805 1509029 := bstep (se 4 (by rfl) ⟨141471, by rfl⟩ : syracuseStep 1509029 = 282943) B282943
theorem B297071 : Blo 195805 297071 := bstep (se 1 (by rfl) ⟨222803, by rfl⟩ : syracuseStep 297071 = 445607) B445607
theorem B297407 : Blo 195805 297407 := bstep (se 1 (by rfl) ⟨223055, by rfl⟩ : syracuseStep 297407 = 446111) B446111
theorem B199143 : Blo 195805 199143 := bstep (se 1 (by rfl) ⟨149357, by rfl⟩ : syracuseStep 199143 = 298715) B298715
theorem B297449 : Blo 195805 297449 := bstep (se 2 (by rfl) ⟨111543, by rfl⟩ : syracuseStep 297449 = 223087) B223087
theorem B34408961 : Blo 195805 34408961 := bstep (se 2 (by rfl) ⟨12903360, by rfl⟩ : syracuseStep 34408961 = 25806721) B25806721
theorem B199259 : Blo 195805 199259 := bstep (se 1 (by rfl) ⟨149444, by rfl⟩ : syracuseStep 199259 = 298889) B298889
theorem B297707 : Blo 195805 297707 := bstep (se 1 (by rfl) ⟨223280, by rfl⟩ : syracuseStep 297707 = 446561) B446561
theorem B199419 : Blo 195805 199419 := bstep (se 1 (by rfl) ⟨149564, by rfl⟩ : syracuseStep 199419 = 299129) B299129
theorem B560009 : Blo 195805 560009 := bstep (se 2 (by rfl) ⟨210003, by rfl⟩ : syracuseStep 560009 = 420007) B420007
theorem B3214343 : Blo 195805 3214343 := bstep (se 1 (by rfl) ⟨2410757, by rfl⟩ : syracuseStep 3214343 = 4821515) B4821515
theorem B298235 : Blo 195805 298235 := bstep (se 1 (by rfl) ⟨223676, by rfl⟩ : syracuseStep 298235 = 447353) B447353
theorem B298295 : Blo 195805 298295 := bstep (se 1 (by rfl) ⟨223721, by rfl⟩ : syracuseStep 298295 = 447443) B447443
theorem B298601 : Blo 195805 298601 := bstep (se 2 (by rfl) ⟨111975, by rfl⟩ : syracuseStep 298601 = 223951) B223951
theorem B298703 : Blo 195805 298703 := bstep (se 1 (by rfl) ⟨224027, by rfl⟩ : syracuseStep 298703 = 448055) B448055
theorem B298751 : Blo 195805 298751 := bstep (se 1 (by rfl) ⟨224063, by rfl⟩ : syracuseStep 298751 = 448127) B448127
theorem B1151443 : Blo 195805 1151443 := bstep (se 1 (by rfl) ⟨863582, by rfl⟩ : syracuseStep 1151443 = 1727165) B1727165
theorem B299687 : Blo 195805 299687 := bstep (se 1 (by rfl) ⟨224765, by rfl⟩ : syracuseStep 299687 = 449531) B449531
theorem B496439 : Blo 195805 496439 := bstep (se 1 (by rfl) ⟨372329, by rfl⟩ : syracuseStep 496439 = 744659) B744659
theorem B628319 : Blo 195805 628319 := bstep (se 1 (by rfl) ⟨471239, by rfl⟩ : syracuseStep 628319 = 942479) B942479
theorem B3642995 : Blo 195805 3642995 := bstep (se 1 (by rfl) ⟨2732246, by rfl⟩ : syracuseStep 3642995 = 5464493) B5464493
theorem B333551 : Blo 195805 333551 := bstep (se 1 (by rfl) ⟨250163, by rfl⟩ : syracuseStep 333551 = 500327) B500327
theorem B15472457 : Blo 195805 15472457 := bstep (se 2 (by rfl) ⟨5802171, by rfl⟩ : syracuseStep 15472457 = 11604343) B11604343
theorem B1513889 : Blo 195805 1513889 := bstep (se 2 (by rfl) ⟨567708, by rfl⟩ : syracuseStep 1513889 = 1135417) B1135417
theorem B498271 : Blo 195805 498271 := bstep (se 1 (by rfl) ⟨373703, by rfl⟩ : syracuseStep 498271 = 747407) B747407
theorem B4561535 : Blo 195805 4561535 := bstep (se 1 (by rfl) ⟨3421151, by rfl⟩ : syracuseStep 4561535 = 6842303) B6842303
theorem B662471 : Blo 195805 662471 := bstep (se 1 (by rfl) ⟨496853, by rfl⟩ : syracuseStep 662471 = 993707) B993707
theorem B564839 : Blo 195805 564839 := bstep (se 1 (by rfl) ⟨423629, by rfl⟩ : syracuseStep 564839 = 847259) B847259
theorem B630767 : Blo 195805 630767 := bstep (se 1 (by rfl) ⟨473075, by rfl⟩ : syracuseStep 630767 = 946151) B946151
theorem B1515833 : Blo 195805 1515833 := bstep (se 2 (by rfl) ⟨568437, by rfl⟩ : syracuseStep 1515833 = 1136875) B1136875
theorem B665063 : Blo 195805 665063 := bstep (se 1 (by rfl) ⟨498797, by rfl⟩ : syracuseStep 665063 = 997595) B997595
theorem B501815 : Blo 195805 501815 := bstep (se 1 (by rfl) ⟨376361, by rfl⟩ : syracuseStep 501815 = 752723) B752723
theorem B1125211 : Blo 195805 1125211 := bstep (se 1 (by rfl) ⟨843908, by rfl⟩ : syracuseStep 1125211 = 1687817) B1687817
theorem B503081 : Blo 195805 503081 := bstep (se 2 (by rfl) ⟨188655, by rfl⟩ : syracuseStep 503081 = 377311) B377311
theorem B798187 : Blo 195805 798187 := bstep (se 1 (by rfl) ⟨598640, by rfl⟩ : syracuseStep 798187 = 1197281) B1197281
theorem B5025725 : Blo 195805 5025725 := bstep (se 3 (by rfl) ⟨942323, by rfl⟩ : syracuseStep 5025725 = 1884647) B1884647
theorem B1127195 : Blo 195805 1127195 := bstep (se 1 (by rfl) ⟨845396, by rfl⟩ : syracuseStep 1127195 = 1690793) B1690793
theorem B373871 : Blo 195805 373871 := bstep (se 1 (by rfl) ⟨280403, by rfl⟩ : syracuseStep 373871 = 560807) B560807
theorem B505055 : Blo 195805 505055 := bstep (se 1 (by rfl) ⟨378791, by rfl⟩ : syracuseStep 505055 = 757583) B757583
theorem B2700611 : Blo 195805 2700611 := bstep (se 1 (by rfl) ⟨2025458, by rfl⟩ : syracuseStep 2700611 = 4050917) B4050917
theorem B1521127 : Blo 195805 1521127 := bstep (se 1 (by rfl) ⟨1140845, by rfl⟩ : syracuseStep 1521127 = 2281691) B2281691
theorem B636827 : Blo 195805 636827 := bstep (se 1 (by rfl) ⟨477620, by rfl⟩ : syracuseStep 636827 = 955241) B955241
theorem B604157 : Blo 195805 604157 := bstep (se 3 (by rfl) ⟨113279, by rfl⟩ : syracuseStep 604157 = 226559) B226559
theorem B44546183 : Blo 195805 44546183 := bstep (se 1 (by rfl) ⟨33409637, by rfl⟩ : syracuseStep 44546183 = 66819275) B66819275
theorem B4274369 : Blo 195805 4274369 := bstep (se 2 (by rfl) ⟨1602888, by rfl⟩ : syracuseStep 4274369 = 3205777) B3205777
theorem B670463 : Blo 195805 670463 := bstep (se 1 (by rfl) ⟨502847, by rfl⟩ : syracuseStep 670463 = 1005695) B1005695
theorem B2014703 : Blo 195805 2014703 := bstep (se 1 (by rfl) ⟨1511027, by rfl⟩ : syracuseStep 2014703 = 3022055) B3022055
theorem B1491047 : Blo 195805 1491047 := bstep (se 1 (by rfl) ⟨1118285, by rfl⟩ : syracuseStep 1491047 = 2236571) B2236571
theorem B442619 : Blo 195805 442619 := bstep (se 1 (by rfl) ⟨331964, by rfl⟩ : syracuseStep 442619 = 663929) B663929
theorem B442871 : Blo 195805 442871 := bstep (se 1 (by rfl) ⟨332153, by rfl⟩ : syracuseStep 442871 = 664307) B664307
theorem B377903 : Blo 195805 377903 := bstep (se 1 (by rfl) ⟨283427, by rfl⟩ : syracuseStep 377903 = 566855) B566855
theorem B443483 : Blo 195805 443483 := bstep (se 1 (by rfl) ⟨332612, by rfl⟩ : syracuseStep 443483 = 665225) B665225
theorem B443519 : Blo 195805 443519 := bstep (se 1 (by rfl) ⟨332639, by rfl⟩ : syracuseStep 443519 = 665279) B665279
theorem B280039 : Blo 195805 280039 := bstep (se 1 (by rfl) ⟨210029, by rfl⟩ : syracuseStep 280039 = 420059) B420059
theorem B477083 : Blo 195805 477083 := bstep (se 1 (by rfl) ⟨357812, by rfl⟩ : syracuseStep 477083 = 715625) B715625
theorem B673919 : Blo 195805 673919 := bstep (se 1 (by rfl) ⟨505439, by rfl⟩ : syracuseStep 673919 = 1010879) B1010879
theorem B444671 : Blo 195805 444671 := bstep (se 1 (by rfl) ⟨333503, by rfl⟩ : syracuseStep 444671 = 667007) B667007
theorem B313903 : Blo 195805 313903 := bstep (se 1 (by rfl) ⟨235427, by rfl⟩ : syracuseStep 313903 = 470855) B470855
theorem B707609 : Blo 195805 707609 := bstep (se 2 (by rfl) ⟨265353, by rfl⟩ : syracuseStep 707609 = 530707) B530707
theorem B478505 : Blo 195805 478505 := bstep (se 2 (by rfl) ⟨179439, by rfl⟩ : syracuseStep 478505 = 358879) B358879
theorem B282089 : Blo 195805 282089 := bstep (se 2 (by rfl) ⟨105783, by rfl⟩ : syracuseStep 282089 = 211567) B211567
theorem B1986191 : Blo 195805 1986191 := bstep (se 1 (by rfl) ⟨1489643, by rfl⟩ : syracuseStep 1986191 = 2979287) B2979287
theorem B446399 : Blo 195805 446399 := bstep (se 1 (by rfl) ⟨334799, by rfl⟩ : syracuseStep 446399 = 669599) B669599
theorem B708691 : Blo 195805 708691 := bstep (se 1 (by rfl) ⟨531518, by rfl⟩ : syracuseStep 708691 = 1063037) B1063037
theorem B2543723 : Blo 195805 2543723 := bstep (se 1 (by rfl) ⟨1907792, by rfl⟩ : syracuseStep 2543723 = 3815585) B3815585
theorem B10506347 : Blo 195805 10506347 := bstep (se 1 (by rfl) ⟨7879760, by rfl⟩ : syracuseStep 10506347 = 15759521) B15759521
theorem B282847 : Blo 195805 282847 := bstep (se 1 (by rfl) ⟨212135, by rfl⟩ : syracuseStep 282847 = 424271) B424271
theorem B2707721 : Blo 195805 2707721 := bstep (se 2 (by rfl) ⟨1015395, by rfl⟩ : syracuseStep 2707721 = 2030791) B2030791
theorem B446777 : Blo 195805 446777 := bstep (se 2 (by rfl) ⟨167541, by rfl⟩ : syracuseStep 446777 = 335083) B335083
theorem B447227 : Blo 195805 447227 := bstep (se 1 (by rfl) ⟨335420, by rfl⟩ : syracuseStep 447227 = 670841) B670841
theorem B447335 : Blo 195805 447335 := bstep (se 1 (by rfl) ⟨335501, by rfl⟩ : syracuseStep 447335 = 671003) B671003
theorem B252011 : Blo 195805 252011 := bstep (se 1 (by rfl) ⟨189008, by rfl⟩ : syracuseStep 252011 = 378017) B378017
theorem B448703 : Blo 195805 448703 := bstep (se 1 (by rfl) ⟨336527, by rfl⟩ : syracuseStep 448703 = 673055) B673055
theorem B1498337 : Blo 195805 1498337 := bstep (se 2 (by rfl) ⟨561876, by rfl⟩ : syracuseStep 1498337 = 1123753) B1123753
theorem B318875 : Blo 195805 318875 := bstep (se 1 (by rfl) ⟨239156, by rfl⟩ : syracuseStep 318875 = 478313) B478313
theorem B2022839 : Blo 195805 2022839 := bstep (se 1 (by rfl) ⟨1517129, by rfl⟩ : syracuseStep 2022839 = 3034259) B3034259
theorem B712655 : Blo 195805 712655 := bstep (se 1 (by rfl) ⟨534491, by rfl⟩ : syracuseStep 712655 = 1068983) B1068983
theorem B2843579 : Blo 195805 2843579 := bstep (se 1 (by rfl) ⟨2132684, by rfl⟩ : syracuseStep 2843579 = 4265369) B4265369
theorem B223303 : Blo 195805 223303 := bstep (se 1 (by rfl) ⟨167477, by rfl⟩ : syracuseStep 223303 = 334955) B334955
theorem B1010231 : Blo 195805 1010231 := bstep (se 1 (by rfl) ⟨757673, by rfl⟩ : syracuseStep 1010231 = 1515347) B1515347
theorem B224239 : Blo 195805 224239 := bstep (se 1 (by rfl) ⟨168179, by rfl⟩ : syracuseStep 224239 = 336359) B336359
theorem B224671 : Blo 195805 224671 := bstep (se 1 (by rfl) ⟨168503, by rfl⟩ : syracuseStep 224671 = 337007) B337007
theorem B749033 : Blo 195805 749033 := bstep (se 2 (by rfl) ⟨280887, by rfl⟩ : syracuseStep 749033 = 561775) B561775
theorem B5664329 : Blo 195805 5664329 := bstep (se 2 (by rfl) ⟨2124123, by rfl⟩ : syracuseStep 5664329 = 4248247) B4248247
theorem B2846927 : Blo 195805 2846927 := bstep (se 1 (by rfl) ⟨2135195, by rfl⟩ : syracuseStep 2846927 = 4270391) B4270391
theorem B2880143 : Blo 195805 2880143 := bstep (se 1 (by rfl) ⟨2160107, by rfl⟩ : syracuseStep 2880143 = 4320215) B4320215
theorem B422587 : Blo 195805 422587 := bstep (se 1 (by rfl) ⟨316940, by rfl⟩ : syracuseStep 422587 = 633881) B633881
theorem B849959 : Blo 195805 849959 := bstep (se 1 (by rfl) ⟨637469, by rfl⟩ : syracuseStep 849959 = 1274939) B1274939
theorem B293753 : Blo 195805 293753 := bstep (se 2 (by rfl) ⟨110157, by rfl⟩ : syracuseStep 293753 = 220315) B220315
theorem B293801 : Blo 195805 293801 := bstep (se 2 (by rfl) ⟨110175, by rfl⟩ : syracuseStep 293801 = 220351) B220351
theorem B293831 : Blo 195805 293831 := bstep (se 1 (by rfl) ⟨220373, by rfl⟩ : syracuseStep 293831 = 440747) B440747
theorem B294047 : Blo 195805 294047 := bstep (se 1 (by rfl) ⟨220535, by rfl⟩ : syracuseStep 294047 = 441071) B441071
theorem B195823 : Blo 195805 195823 := bstep (se 1 (by rfl) ⟨146867, by rfl⟩ : syracuseStep 195823 = 293735) B293735
theorem B195839 : Blo 195805 195839 := bstep (se 1 (by rfl) ⟨146879, by rfl⟩ : syracuseStep 195839 = 293759) B293759
theorem B294215 : Blo 195805 294215 := bstep (se 1 (by rfl) ⟨220661, by rfl⟩ : syracuseStep 294215 = 441323) B441323
theorem B196063 : Blo 195805 196063 := bstep (se 1 (by rfl) ⟨147047, by rfl⟩ : syracuseStep 196063 = 294095) B294095
theorem B753209 : Blo 195805 753209 := bstep (se 2 (by rfl) ⟨282453, by rfl⟩ : syracuseStep 753209 = 564907) B564907
theorem B18087857 : Blo 195805 18087857 := bstep (se 2 (by rfl) ⟨6782946, by rfl⟩ : syracuseStep 18087857 = 13565893) B13565893
theorem B196543 : Blo 195805 196543 := bstep (se 1 (by rfl) ⟨147407, by rfl⟩ : syracuseStep 196543 = 294815) B294815
theorem B196603 : Blo 195805 196603 := bstep (se 1 (by rfl) ⟨147452, by rfl⟩ : syracuseStep 196603 = 294905) B294905
theorem B196767 : Blo 195805 196767 := bstep (se 1 (by rfl) ⟨147575, by rfl⟩ : syracuseStep 196767 = 295151) B295151
theorem B295079 : Blo 195805 295079 := bstep (se 1 (by rfl) ⟨221309, by rfl⟩ : syracuseStep 295079 = 442619) B442619
theorem B196775 : Blo 195805 196775 := bstep (se 1 (by rfl) ⟨147581, by rfl⟩ : syracuseStep 196775 = 295163) B295163
theorem B295247 : Blo 195805 295247 := bstep (se 1 (by rfl) ⟨221435, by rfl⟩ : syracuseStep 295247 = 442871) B442871
theorem B4981421 : Blo 195805 4981421 := bstep (se 3 (by rfl) ⟨934016, by rfl⟩ : syracuseStep 4981421 = 1868033) B1868033
theorem B295655 : Blo 195805 295655 := bstep (se 1 (by rfl) ⟨221741, by rfl⟩ : syracuseStep 295655 = 443483) B443483
theorem B197359 : Blo 195805 197359 := bstep (se 1 (by rfl) ⟨148019, by rfl⟩ : syracuseStep 197359 = 296039) B296039
theorem B197371 : Blo 195805 197371 := bstep (se 1 (by rfl) ⟨148028, by rfl⟩ : syracuseStep 197371 = 296057) B296057
theorem B295679 : Blo 195805 295679 := bstep (se 1 (by rfl) ⟨221759, by rfl⟩ : syracuseStep 295679 = 443519) B443519
theorem B198047 : Blo 195805 198047 := bstep (se 1 (by rfl) ⟨148535, by rfl⟩ : syracuseStep 198047 = 297071) B297071
theorem B296447 : Blo 195805 296447 := bstep (se 1 (by rfl) ⟨222335, by rfl⟩ : syracuseStep 296447 = 444671) B444671
theorem B198271 : Blo 195805 198271 := bstep (se 1 (by rfl) ⟨148703, by rfl⟩ : syracuseStep 198271 = 297407) B297407
theorem B198299 : Blo 195805 198299 := bstep (se 1 (by rfl) ⟨148724, by rfl⟩ : syracuseStep 198299 = 297449) B297449
theorem B22939307 : Blo 195805 22939307 := bstep (se 1 (by rfl) ⟨17204480, by rfl⟩ : syracuseStep 22939307 = 34408961) B34408961
theorem B198471 : Blo 195805 198471 := bstep (se 1 (by rfl) ⟨148853, by rfl⟩ : syracuseStep 198471 = 297707) B297707
theorem B198823 : Blo 195805 198823 := bstep (se 1 (by rfl) ⟨149117, by rfl⟩ : syracuseStep 198823 = 298235) B298235
theorem B198863 : Blo 195805 198863 := bstep (se 1 (by rfl) ⟨149147, by rfl⟩ : syracuseStep 198863 = 298295) B298295
theorem B199067 : Blo 195805 199067 := bstep (se 1 (by rfl) ⟨149300, by rfl⟩ : syracuseStep 199067 = 298601) B298601
theorem B199135 : Blo 195805 199135 := bstep (se 1 (by rfl) ⟨149351, by rfl⟩ : syracuseStep 199135 = 298703) B298703
theorem B199167 : Blo 195805 199167 := bstep (se 1 (by rfl) ⟨149375, by rfl⟩ : syracuseStep 199167 = 298751) B298751
theorem B297599 : Blo 195805 297599 := bstep (se 1 (by rfl) ⟨223199, by rfl⟩ : syracuseStep 297599 = 446399) B446399
theorem B297737 : Blo 195805 297737 := bstep (se 2 (by rfl) ⟨111651, by rfl⟩ : syracuseStep 297737 = 223303) B223303
theorem B1805147 : Blo 195805 1805147 := bstep (se 1 (by rfl) ⟨1353860, by rfl⟩ : syracuseStep 1805147 = 2707721) B2707721
theorem B297851 : Blo 195805 297851 := bstep (se 1 (by rfl) ⟨223388, by rfl⟩ : syracuseStep 297851 = 446777) B446777
theorem B199791 : Blo 195805 199791 := bstep (se 1 (by rfl) ⟨149843, by rfl⟩ : syracuseStep 199791 = 299687) B299687
theorem B298151 : Blo 195805 298151 := bstep (se 1 (by rfl) ⟨223613, by rfl⟩ : syracuseStep 298151 = 447227) B447227
theorem B330959 : Blo 195805 330959 := bstep (se 1 (by rfl) ⟨248219, by rfl⟩ : syracuseStep 330959 = 496439) B496439
theorem B298223 : Blo 195805 298223 := bstep (se 1 (by rfl) ⟨223667, by rfl⟩ : syracuseStep 298223 = 447335) B447335
theorem B2428663 : Blo 195805 2428663 := bstep (se 1 (by rfl) ⟨1821497, by rfl⟩ : syracuseStep 2428663 = 3642995) B3642995
theorem B298985 : Blo 195805 298985 := bstep (se 2 (by rfl) ⟨112119, by rfl⟩ : syracuseStep 298985 = 224239) B224239
theorem B299135 : Blo 195805 299135 := bstep (se 1 (by rfl) ⟨224351, by rfl⟩ : syracuseStep 299135 = 448703) B448703
theorem B299561 : Blo 195805 299561 := bstep (se 2 (by rfl) ⟨112335, by rfl⟩ : syracuseStep 299561 = 224671) B224671
theorem B1348559 : Blo 195805 1348559 := bstep (se 1 (by rfl) ⟨1011419, by rfl⟩ : syracuseStep 1348559 = 2022839) B2022839
theorem B1611085 : Blo 195805 1611085 := bstep (se 3 (by rfl) ⟨302078, by rfl⟩ : syracuseStep 1611085 = 604157) B604157
theorem B563449 : Blo 195805 563449 := bstep (se 2 (by rfl) ⟨211293, by rfl⟩ : syracuseStep 563449 = 422587) B422587
theorem B334543 : Blo 195805 334543 := bstep (se 1 (by rfl) ⟨250907, by rfl⟩ : syracuseStep 334543 = 501815) B501815
theorem B12164093 : Blo 195805 12164093 := bstep (se 3 (by rfl) ⟨2280767, by rfl⟩ : syracuseStep 12164093 = 4561535) B4561535
theorem B335387 : Blo 195805 335387 := bstep (se 1 (by rfl) ⟨251540, by rfl⟩ : syracuseStep 335387 = 503081) B503081
theorem B499355 : Blo 195805 499355 := bstep (se 1 (by rfl) ⟨374516, by rfl⟩ : syracuseStep 499355 = 749033) B749033
theorem B3776219 : Blo 195805 3776219 := bstep (se 1 (by rfl) ⟨2832164, by rfl⟩ : syracuseStep 3776219 = 5664329) B5664329
theorem B3350483 : Blo 195805 3350483 := bstep (se 1 (by rfl) ⟨2512862, by rfl⟩ : syracuseStep 3350483 = 5025725) B5025725
theorem B664361 : Blo 195805 664361 := bstep (se 2 (by rfl) ⟨249135, by rfl⟩ : syracuseStep 664361 = 498271) B498271
theorem B336703 : Blo 195805 336703 := bstep (se 1 (by rfl) ⟨252527, by rfl⟩ : syracuseStep 336703 = 505055) B505055
theorem B566639 : Blo 195805 566639 := bstep (se 1 (by rfl) ⟨424979, by rfl⟩ : syracuseStep 566639 = 849959) B849959
theorem B29697455 : Blo 195805 29697455 := bstep (se 1 (by rfl) ⟨22273091, by rfl⟩ : syracuseStep 29697455 = 44546183) B44546183
theorem B502139 : Blo 195805 502139 := bstep (se 1 (by rfl) ⟨376604, by rfl⟩ : syracuseStep 502139 = 753209) B753209
theorem B1682045 : Blo 195805 1682045 := bstep (se 3 (by rfl) ⟨315383, by rfl⟩ : syracuseStep 1682045 = 630767) B630767
theorem B994031 : Blo 195805 994031 := bstep (se 1 (by rfl) ⟨745523, by rfl⟩ : syracuseStep 994031 = 1491047) B1491047
theorem B503111 : Blo 195805 503111 := bstep (se 1 (by rfl) ⟨377333, by rfl⟩ : syracuseStep 503111 = 754667) B754667
theorem B503455 : Blo 195805 503455 := bstep (se 1 (by rfl) ⟨377591, by rfl⟩ : syracuseStep 503455 = 755183) B755183
theorem B373339 : Blo 195805 373339 := bstep (se 1 (by rfl) ⟨280004, by rfl⟩ : syracuseStep 373339 = 560009) B560009
theorem B373385 : Blo 195805 373385 := bstep (se 2 (by rfl) ⟨140019, by rfl⟩ : syracuseStep 373385 = 280039) B280039
theorem B2142895 : Blo 195805 2142895 := bstep (se 1 (by rfl) ⟨1607171, by rfl⟩ : syracuseStep 2142895 = 3214343) B3214343
theorem B471739 : Blo 195805 471739 := bstep (se 1 (by rfl) ⟨353804, by rfl⟩ : syracuseStep 471739 = 707609) B707609
theorem B1324127 : Blo 195805 1324127 := bstep (se 1 (by rfl) ⟨993095, by rfl⟩ : syracuseStep 1324127 = 1986191) B1986191
theorem B441647 : Blo 195805 441647 := bstep (se 1 (by rfl) ⟨331235, by rfl⟩ : syracuseStep 441647 = 662471) B662471
theorem B1064249 : Blo 195805 1064249 := bstep (se 2 (by rfl) ⟨399093, by rfl⟩ : syracuseStep 1064249 = 798187) B798187
theorem B998891 : Blo 195805 998891 := bstep (se 1 (by rfl) ⟨749168, by rfl⟩ : syracuseStep 998891 = 1498337) B1498337
theorem B376559 : Blo 195805 376559 := bstep (se 1 (by rfl) ⟨282419, by rfl⟩ : syracuseStep 376559 = 564839) B564839
theorem B475103 : Blo 195805 475103 := bstep (se 1 (by rfl) ⟨356327, by rfl⟩ : syracuseStep 475103 = 712655) B712655
theorem B672029 : Blo 195805 672029 := bstep (se 3 (by rfl) ⟨126005, by rfl⟩ : syracuseStep 672029 = 252011) B252011
theorem B377129 : Blo 195805 377129 := bstep (se 2 (by rfl) ⟨141423, by rfl⟩ : syracuseStep 377129 = 282847) B282847
theorem B443375 : Blo 195805 443375 := bstep (se 1 (by rfl) ⟨332531, by rfl⟩ : syracuseStep 443375 = 665063) B665063
theorem B673487 : Blo 195805 673487 := bstep (se 1 (by rfl) ⟨505115, by rfl⟩ : syracuseStep 673487 = 1010231) B1010231
theorem B1920095 : Blo 195805 1920095 := bstep (se 1 (by rfl) ⟨1440071, by rfl⟩ : syracuseStep 1920095 = 2880143) B2880143
theorem B249247 : Blo 195805 249247 := bstep (se 1 (by rfl) ⟨186935, by rfl⟩ : syracuseStep 249247 = 373871) B373871
theorem B446975 : Blo 195805 446975 := bstep (se 1 (by rfl) ⟨335231, by rfl⟩ : syracuseStep 446975 = 670463) B670463
theorem B251935 : Blo 195805 251935 := bstep (se 1 (by rfl) ⟨188951, by rfl⟩ : syracuseStep 251935 = 377903) B377903
theorem B1006019 : Blo 195805 1006019 := bstep (se 1 (by rfl) ⟨754514, by rfl⟩ : syracuseStep 1006019 = 1509029) B1509029
theorem B318055 : Blo 195805 318055 := bstep (se 1 (by rfl) ⟨238541, by rfl⟩ : syracuseStep 318055 = 477083) B477083
theorem B449279 : Blo 195805 449279 := bstep (se 1 (by rfl) ⟨336959, by rfl⟩ : syracuseStep 449279 = 673919) B673919
theorem B1695815 : Blo 195805 1695815 := bstep (se 1 (by rfl) ⟨1271861, by rfl⟩ : syracuseStep 1695815 = 2543723) B2543723
theorem B7004231 : Blo 195805 7004231 := bstep (se 1 (by rfl) ⟨5253173, by rfl⟩ : syracuseStep 7004231 = 10506347) B10506347
theorem B418537 : Blo 195805 418537 := bstep (se 2 (by rfl) ⟨156951, by rfl⟩ : syracuseStep 418537 = 313903) B313903
theorem B418879 : Blo 195805 418879 := bstep (se 1 (by rfl) ⟨314159, by rfl⟩ : syracuseStep 418879 = 628319) B628319
theorem B1500281 : Blo 195805 1500281 := bstep (se 2 (by rfl) ⟨562605, by rfl⟩ : syracuseStep 1500281 = 1125211) B1125211
theorem B222367 : Blo 195805 222367 := bstep (se 1 (by rfl) ⟨166775, by rfl⟩ : syracuseStep 222367 = 333551) B333551
theorem B10314971 : Blo 195805 10314971 := bstep (se 1 (by rfl) ⟨7736228, by rfl⟩ : syracuseStep 10314971 = 15472457) B15472457
theorem B1009259 : Blo 195805 1009259 := bstep (se 1 (by rfl) ⟨756944, by rfl⟩ : syracuseStep 1009259 = 1513889) B1513889
theorem B1698205 : Blo 195805 1698205 := bstep (se 3 (by rfl) ⟨318413, by rfl⟩ : syracuseStep 1698205 = 636827) B636827
theorem B944921 : Blo 195805 944921 := bstep (se 2 (by rfl) ⟨354345, by rfl⟩ : syracuseStep 944921 = 708691) B708691
theorem B1010555 : Blo 195805 1010555 := bstep (se 1 (by rfl) ⟨757916, by rfl⟩ : syracuseStep 1010555 = 1515833) B1515833
theorem B1535257 : Blo 195805 1535257 := bstep (se 2 (by rfl) ⟨575721, by rfl⟩ : syracuseStep 1535257 = 1151443) B1151443
theorem B1895719 : Blo 195805 1895719 := bstep (se 1 (by rfl) ⟨1421789, by rfl⟩ : syracuseStep 1895719 = 2843579) B2843579
theorem B2028169 : Blo 195805 2028169 := bstep (se 2 (by rfl) ⟨760563, by rfl⟩ : syracuseStep 2028169 = 1521127) B1521127
theorem B1897951 : Blo 195805 1897951 := bstep (se 1 (by rfl) ⟨1423463, by rfl⟩ : syracuseStep 1897951 = 2846927) B2846927
theorem B751463 : Blo 195805 751463 := bstep (se 1 (by rfl) ⟨563597, by rfl⟩ : syracuseStep 751463 = 1127195) B1127195
theorem B1276013 : Blo 195805 1276013 := bstep (se 3 (by rfl) ⟨239252, by rfl⟩ : syracuseStep 1276013 = 478505) B478505
theorem B1800407 : Blo 195805 1800407 := bstep (se 1 (by rfl) ⟨1350305, by rfl⟩ : syracuseStep 1800407 = 2700611) B2700611
theorem B850333 : Blo 195805 850333 := bstep (se 3 (by rfl) ⟨159437, by rfl⟩ : syracuseStep 850333 = 318875) B318875
theorem B752237 : Blo 195805 752237 := bstep (se 3 (by rfl) ⟨141044, by rfl⟩ : syracuseStep 752237 = 282089) B282089
theorem B2849579 : Blo 195805 2849579 := bstep (se 1 (by rfl) ⟨2137184, by rfl⟩ : syracuseStep 2849579 = 4274369) B4274369
theorem B195835 : Blo 195805 195835 := bstep (se 1 (by rfl) ⟨146876, by rfl⟩ : syracuseStep 195835 = 293753) B293753
theorem B195867 : Blo 195805 195867 := bstep (se 1 (by rfl) ⟨146900, by rfl⟩ : syracuseStep 195867 = 293801) B293801
theorem B195887 : Blo 195805 195887 := bstep (se 1 (by rfl) ⟨146915, by rfl⟩ : syracuseStep 195887 = 293831) B293831
theorem B196031 : Blo 195805 196031 := bstep (se 1 (by rfl) ⟨147023, by rfl⟩ : syracuseStep 196031 = 294047) B294047
theorem B196143 : Blo 195805 196143 := bstep (se 1 (by rfl) ⟨147107, by rfl⟩ : syracuseStep 196143 = 294215) B294215
theorem B1343135 : Blo 195805 1343135 := bstep (se 1 (by rfl) ⟨1007351, by rfl⟩ : syracuseStep 1343135 = 2014703) B2014703
theorem B12058571 : Blo 195805 12058571 := bstep (se 1 (by rfl) ⟨9043928, by rfl⟩ : syracuseStep 12058571 = 18087857) B18087857
theorem B196719 : Blo 195805 196719 := bstep (se 1 (by rfl) ⟨147539, by rfl⟩ : syracuseStep 196719 = 295079) B295079
theorem B196831 : Blo 195805 196831 := bstep (se 1 (by rfl) ⟨147623, by rfl⟩ : syracuseStep 196831 = 295247) B295247
theorem B197103 : Blo 195805 197103 := bstep (se 1 (by rfl) ⟨147827, by rfl⟩ : syracuseStep 197103 = 295655) B295655
theorem B197119 : Blo 195805 197119 := bstep (se 1 (by rfl) ⟨147839, by rfl⟩ : syracuseStep 197119 = 295679) B295679
theorem B5374613 : Blo 195805 5374613 := bstep (se 6 (by rfl) ⟨125967, by rfl⟩ : syracuseStep 5374613 = 251935) B251935
theorem B295583 : Blo 195805 295583 := bstep (se 1 (by rfl) ⟨221687, by rfl⟩ : syracuseStep 295583 = 443375) B443375
theorem B197631 : Blo 195805 197631 := bstep (se 1 (by rfl) ⟨148223, by rfl⟩ : syracuseStep 197631 = 296447) B296447
theorem B558505 : Blo 195805 558505 := bstep (se 2 (by rfl) ⟨209439, by rfl⟩ : syracuseStep 558505 = 418879) B418879
theorem B296489 : Blo 195805 296489 := bstep (se 2 (by rfl) ⟨111183, by rfl⟩ : syracuseStep 296489 = 222367) B222367
theorem B198399 : Blo 195805 198399 := bstep (se 1 (by rfl) ⟨148799, by rfl⟩ : syracuseStep 198399 = 297599) B297599
theorem B198491 : Blo 195805 198491 := bstep (se 1 (by rfl) ⟨148868, by rfl⟩ : syracuseStep 198491 = 297737) B297737
theorem B198567 : Blo 195805 198567 := bstep (se 1 (by rfl) ⟨148925, by rfl⟩ : syracuseStep 198567 = 297851) B297851
theorem B1280063 : Blo 195805 1280063 := bstep (se 1 (by rfl) ⟨960047, by rfl⟩ : syracuseStep 1280063 = 1920095) B1920095
theorem B198767 : Blo 195805 198767 := bstep (se 1 (by rfl) ⟨149075, by rfl⟩ : syracuseStep 198767 = 298151) B298151
theorem B198815 : Blo 195805 198815 := bstep (se 1 (by rfl) ⟨149111, by rfl⟩ : syracuseStep 198815 = 298223) B298223
theorem B199323 : Blo 195805 199323 := bstep (se 1 (by rfl) ⟨149492, by rfl⟩ : syracuseStep 199323 = 298985) B298985
theorem B199423 : Blo 195805 199423 := bstep (se 1 (by rfl) ⟨149567, by rfl⟩ : syracuseStep 199423 = 299135) B299135
theorem B297983 : Blo 195805 297983 := bstep (se 1 (by rfl) ⟨223487, by rfl⟩ : syracuseStep 297983 = 446975) B446975
theorem B199707 : Blo 195805 199707 := bstep (se 1 (by rfl) ⟨149780, by rfl⟩ : syracuseStep 199707 = 299561) B299561
theorem B2264273 : Blo 195805 2264273 := bstep (se 2 (by rfl) ⟨849102, by rfl⟩ : syracuseStep 2264273 = 1698205) B1698205
theorem B2232197 : Blo 195805 2232197 := bstep (se 4 (by rfl) ⟨209268, by rfl⟩ : syracuseStep 2232197 = 418537) B418537
theorem B2527625 : Blo 195805 2527625 := bstep (se 2 (by rfl) ⟨947859, by rfl⟩ : syracuseStep 2527625 = 1895719) B1895719
theorem B299519 : Blo 195805 299519 := bstep (se 1 (by rfl) ⟨224639, by rfl⟩ : syracuseStep 299519 = 449279) B449279
theorem B332329 : Blo 195805 332329 := bstep (se 2 (by rfl) ⟨124623, by rfl⟩ : syracuseStep 332329 = 249247) B249247
theorem B332903 : Blo 195805 332903 := bstep (se 1 (by rfl) ⟨249677, by rfl⟩ : syracuseStep 332903 = 499355) B499355
theorem B2233655 : Blo 195805 2233655 := bstep (se 1 (by rfl) ⟨1675241, by rfl⟩ : syracuseStep 2233655 = 3350483) B3350483
theorem B497785 : Blo 195805 497785 := bstep (se 2 (by rfl) ⟨186669, by rfl⟩ : syracuseStep 497785 = 373339) B373339
theorem B2857193 : Blo 195805 2857193 := bstep (se 2 (by rfl) ⟨1071447, by rfl⟩ : syracuseStep 2857193 = 2142895) B2142895
theorem B628985 : Blo 195805 628985 := bstep (se 2 (by rfl) ⟨235869, by rfl⟩ : syracuseStep 628985 = 471739) B471739
theorem B334759 : Blo 195805 334759 := bstep (se 1 (by rfl) ⟨251069, by rfl⟩ : syracuseStep 334759 = 502139) B502139
theorem B1121363 : Blo 195805 1121363 := bstep (se 1 (by rfl) ⟨841022, by rfl⟩ : syracuseStep 1121363 = 1682045) B1682045
theorem B662687 : Blo 195805 662687 := bstep (se 1 (by rfl) ⟨497015, by rfl⟩ : syracuseStep 662687 = 994031) B994031
theorem B629947 : Blo 195805 629947 := bstep (se 1 (by rfl) ⟨472460, by rfl⟩ : syracuseStep 629947 = 944921) B944921
theorem B2530601 : Blo 195805 2530601 := bstep (se 2 (by rfl) ⟨948975, by rfl⟩ : syracuseStep 2530601 = 1897951) B1897951
theorem B335407 : Blo 195805 335407 := bstep (se 1 (by rfl) ⟨251555, by rfl⟩ : syracuseStep 335407 = 503111) B503111
theorem B500975 : Blo 195805 500975 := bstep (se 1 (by rfl) ⟨375731, by rfl⟩ : syracuseStep 500975 = 751463) B751463
theorem B501491 : Blo 195805 501491 := bstep (se 1 (by rfl) ⟨376118, by rfl⟩ : syracuseStep 501491 = 752237) B752237
theorem B665927 : Blo 195805 665927 := bstep (se 1 (by rfl) ⟨499445, by rfl⟩ : syracuseStep 665927 = 998891) B998891
theorem B895423 : Blo 195805 895423 := bstep (se 1 (by rfl) ⟨671567, by rfl⟩ : syracuseStep 895423 = 1343135) B1343135
theorem B32156189 : Blo 195805 32156189 := bstep (se 3 (by rfl) ⟨6029285, by rfl⟩ : syracuseStep 32156189 = 12058571) B12058571
theorem B797293 : Blo 195805 797293 := bstep (se 3 (by rfl) ⟨149492, by rfl⟩ : syracuseStep 797293 = 298985) B298985
theorem B3320947 : Blo 195805 3320947 := bstep (se 1 (by rfl) ⟨2490710, by rfl⟩ : syracuseStep 3320947 = 4981421) B4981421
theorem B899039 : Blo 195805 899039 := bstep (se 1 (by rfl) ⟨674279, by rfl⟩ : syracuseStep 899039 = 1348559) B1348559
theorem B670679 : Blo 195805 670679 := bstep (se 1 (by rfl) ⟨503009, by rfl⟩ : syracuseStep 670679 = 1006019) B1006019
theorem B8109395 : Blo 195805 8109395 := bstep (se 1 (by rfl) ⟨6082046, by rfl⟩ : syracuseStep 8109395 = 12164093) B12164093
theorem B671273 : Blo 195805 671273 := bstep (se 2 (by rfl) ⟨251727, by rfl⟩ : syracuseStep 671273 = 503455) B503455
theorem B1130543 : Blo 195805 1130543 := bstep (se 1 (by rfl) ⟨847907, by rfl⟩ : syracuseStep 1130543 = 1695815) B1695815
theorem B4669487 : Blo 195805 4669487 := bstep (se 1 (by rfl) ⟨3502115, by rfl⟩ : syracuseStep 4669487 = 7004231) B7004231
theorem B442907 : Blo 195805 442907 := bstep (se 1 (by rfl) ⟨332180, by rfl⟩ : syracuseStep 442907 = 664361) B664361
theorem B1000187 : Blo 195805 1000187 := bstep (se 1 (by rfl) ⟨750140, by rfl⟩ : syracuseStep 1000187 = 1500281) B1500281
theorem B2704225 : Blo 195805 2704225 := bstep (se 2 (by rfl) ⟨1014084, by rfl⟩ : syracuseStep 2704225 = 2028169) B2028169
theorem B377759 : Blo 195805 377759 := bstep (se 1 (by rfl) ⟨283319, by rfl⟩ : syracuseStep 377759 = 566639) B566639
theorem B672839 : Blo 195805 672839 := bstep (se 1 (by rfl) ⟨504629, by rfl⟩ : syracuseStep 672839 = 1009259) B1009259
theorem B2148113 : Blo 195805 2148113 := bstep (se 2 (by rfl) ⟨805542, by rfl⟩ : syracuseStep 2148113 = 1611085) B1611085
theorem B673703 : Blo 195805 673703 := bstep (se 1 (by rfl) ⟨505277, by rfl⟩ : syracuseStep 673703 = 1010555) B1010555
theorem B248923 : Blo 195805 248923 := bstep (se 1 (by rfl) ⟨186692, by rfl⟩ : syracuseStep 248923 = 373385) B373385
theorem B1133777 : Blo 195805 1133777 := bstep (se 2 (by rfl) ⟨425166, by rfl⟩ : syracuseStep 1133777 = 850333) B850333
theorem B446057 : Blo 195805 446057 := bstep (se 2 (by rfl) ⟨167271, by rfl⟩ : syracuseStep 446057 = 334543) B334543
theorem B1200271 : Blo 195805 1200271 := bstep (se 1 (by rfl) ⟨900203, by rfl⟩ : syracuseStep 1200271 = 1800407) B1800407
theorem B709499 : Blo 195805 709499 := bstep (se 1 (by rfl) ⟨532124, by rfl⟩ : syracuseStep 709499 = 1064249) B1064249
theorem B251039 : Blo 195805 251039 := bstep (se 1 (by rfl) ⟨188279, by rfl⟩ : syracuseStep 251039 = 376559) B376559
theorem B1266941 : Blo 195805 1266941 := bstep (se 3 (by rfl) ⟨237551, by rfl⟩ : syracuseStep 1266941 = 475103) B475103
theorem B448019 : Blo 195805 448019 := bstep (se 1 (by rfl) ⟨336014, by rfl⟩ : syracuseStep 448019 = 672029) B672029
theorem B251419 : Blo 195805 251419 := bstep (se 1 (by rfl) ⟨188564, by rfl⟩ : syracuseStep 251419 = 377129) B377129
theorem B448937 : Blo 195805 448937 := bstep (se 2 (by rfl) ⟨168351, by rfl⟩ : syracuseStep 448937 = 336703) B336703
theorem B15292871 : Blo 195805 15292871 := bstep (se 1 (by rfl) ⟨11469653, by rfl⟩ : syracuseStep 15292871 = 22939307) B22939307
theorem B448991 : Blo 195805 448991 := bstep (se 1 (by rfl) ⟨336743, by rfl⟩ : syracuseStep 448991 = 673487) B673487
theorem B1203431 : Blo 195805 1203431 := bstep (se 1 (by rfl) ⟨902573, by rfl⟩ : syracuseStep 1203431 = 1805147) B1805147
theorem B220639 : Blo 195805 220639 := bstep (se 1 (by rfl) ⟨165479, by rfl⟩ : syracuseStep 220639 = 330959) B330959
theorem B3531005 : Blo 195805 3531005 := bstep (se 3 (by rfl) ⟨662063, by rfl⟩ : syracuseStep 3531005 = 1324127) B1324127
theorem B79193213 : Blo 195805 79193213 := bstep (se 3 (by rfl) ⟨14848727, by rfl⟩ : syracuseStep 79193213 = 29697455) B29697455
theorem B3238217 : Blo 195805 3238217 := bstep (se 2 (by rfl) ⟨1214331, by rfl⟩ : syracuseStep 3238217 = 2428663) B2428663
theorem B223591 : Blo 195805 223591 := bstep (se 1 (by rfl) ⟨167693, by rfl⟩ : syracuseStep 223591 = 335387) B335387
theorem B2517479 : Blo 195805 2517479 := bstep (se 1 (by rfl) ⟨1888109, by rfl⟩ : syracuseStep 2517479 = 3776219) B3776219
theorem B6876647 : Blo 195805 6876647 := bstep (se 1 (by rfl) ⟨5157485, by rfl⟩ : syracuseStep 6876647 = 10314971) B10314971
theorem B8188037 : Blo 195805 8188037 := bstep (se 4 (by rfl) ⟨767628, by rfl⟩ : syracuseStep 8188037 = 1535257) B1535257
theorem B751265 : Blo 195805 751265 := bstep (se 2 (by rfl) ⟨281724, by rfl⟩ : syracuseStep 751265 = 563449) B563449
theorem B424073 : Blo 195805 424073 := bstep (se 2 (by rfl) ⟨159027, by rfl⟩ : syracuseStep 424073 = 318055) B318055
theorem B850675 : Blo 195805 850675 := bstep (se 1 (by rfl) ⟨638006, by rfl⟩ : syracuseStep 850675 = 1276013) B1276013
theorem B1899719 : Blo 195805 1899719 := bstep (se 1 (by rfl) ⟨1424789, by rfl⟩ : syracuseStep 1899719 = 2849579) B2849579
theorem B294431 : Blo 195805 294431 := bstep (se 1 (by rfl) ⟨220823, by rfl⟩ : syracuseStep 294431 = 441647) B441647
theorem B753695 : Blo 195805 753695 := bstep (se 1 (by rfl) ⟨565271, by rfl⟩ : syracuseStep 753695 = 1130543) B1130543
theorem B3112991 : Blo 195805 3112991 := bstep (se 1 (by rfl) ⟨2334743, by rfl⟩ : syracuseStep 3112991 = 4669487) B4669487
theorem B295271 : Blo 195805 295271 := bstep (se 1 (by rfl) ⟨221453, by rfl⟩ : syracuseStep 295271 = 442907) B442907
theorem B197055 : Blo 195805 197055 := bstep (se 1 (by rfl) ⟨147791, by rfl⟩ : syracuseStep 197055 = 295583) B295583
theorem B197659 : Blo 195805 197659 := bstep (se 1 (by rfl) ⟨148244, by rfl⟩ : syracuseStep 197659 = 296489) B296489
theorem B3605633 : Blo 195805 3605633 := bstep (se 2 (by rfl) ⟨1352112, by rfl⟩ : syracuseStep 3605633 = 2704225) B2704225
theorem B853375 : Blo 195805 853375 := bstep (se 1 (by rfl) ⟨640031, by rfl⟩ : syracuseStep 853375 = 1280063) B1280063
theorem B198655 : Blo 195805 198655 := bstep (se 1 (by rfl) ⟨148991, by rfl⟩ : syracuseStep 198655 = 297983) B297983
theorem B1509515 : Blo 195805 1509515 := bstep (se 1 (by rfl) ⟨1132136, by rfl⟩ : syracuseStep 1509515 = 2264273) B2264273
theorem B755851 : Blo 195805 755851 := bstep (se 1 (by rfl) ⟨566888, by rfl⟩ : syracuseStep 755851 = 1133777) B1133777
theorem B297371 : Blo 195805 297371 := bstep (se 1 (by rfl) ⟨223028, by rfl⟩ : syracuseStep 297371 = 446057) B446057
theorem B199679 : Blo 195805 199679 := bstep (se 1 (by rfl) ⟨149759, by rfl⟩ : syracuseStep 199679 = 299519) B299519
theorem B298121 : Blo 195805 298121 := bstep (se 2 (by rfl) ⟨111795, by rfl⟩ : syracuseStep 298121 = 223591) B223591
theorem B298679 : Blo 195805 298679 := bstep (se 1 (by rfl) ⟨224009, by rfl⟩ : syracuseStep 298679 = 448019) B448019
theorem B331897 : Blo 195805 331897 := bstep (se 2 (by rfl) ⟨124461, by rfl⟩ : syracuseStep 331897 = 248923) B248923
theorem B4427929 : Blo 195805 4427929 := bstep (se 2 (by rfl) ⟨1660473, by rfl⟩ : syracuseStep 4427929 = 3320947) B3320947
theorem B1904795 : Blo 195805 1904795 := bstep (se 1 (by rfl) ⟨1428596, by rfl⟩ : syracuseStep 1904795 = 2857193) B2857193
theorem B299291 : Blo 195805 299291 := bstep (se 1 (by rfl) ⟨224468, by rfl⟩ : syracuseStep 299291 = 448937) B448937
theorem B10195247 : Blo 195805 10195247 := bstep (se 1 (by rfl) ⟨7646435, by rfl⟩ : syracuseStep 10195247 = 15292871) B15292871
theorem B299327 : Blo 195805 299327 := bstep (se 1 (by rfl) ⟨224495, by rfl⟩ : syracuseStep 299327 = 448991) B448991
theorem B1677293 : Blo 195805 1677293 := bstep (se 3 (by rfl) ⟨314492, by rfl⟩ : syracuseStep 1677293 = 628985) B628985
theorem B52795475 : Blo 195805 52795475 := bstep (se 1 (by rfl) ⟨39596606, by rfl⟩ : syracuseStep 52795475 = 79193213) B79193213
theorem B333983 : Blo 195805 333983 := bstep (se 1 (by rfl) ⟨250487, by rfl⟩ : syracuseStep 333983 = 500975) B500975
theorem B334327 : Blo 195805 334327 := bstep (se 1 (by rfl) ⟨250745, by rfl⟩ : syracuseStep 334327 = 501491) B501491
theorem B1678319 : Blo 195805 1678319 := bstep (se 1 (by rfl) ⟨1258739, by rfl⟩ : syracuseStep 1678319 = 2517479) B2517479
theorem B21437459 : Blo 195805 21437459 := bstep (se 1 (by rfl) ⟨16078094, by rfl⟩ : syracuseStep 21437459 = 32156189) B32156189
theorem B335225 : Blo 195805 335225 := bstep (se 2 (by rfl) ⟨125709, by rfl⟩ : syracuseStep 335225 = 251419) B251419
theorem B663713 : Blo 195805 663713 := bstep (se 2 (by rfl) ⟨248892, by rfl⟩ : syracuseStep 663713 = 497785) B497785
theorem B500843 : Blo 195805 500843 := bstep (se 1 (by rfl) ⟨375632, by rfl⟩ : syracuseStep 500843 = 751265) B751265
theorem B599359 : Blo 195805 599359 := bstep (se 1 (by rfl) ⟨449519, by rfl⟩ : syracuseStep 599359 = 899039) B899039
theorem B666791 : Blo 195805 666791 := bstep (se 1 (by rfl) ⟨500093, by rfl⟩ : syracuseStep 666791 = 1000187) B1000187
theorem B14332301 : Blo 195805 14332301 := bstep (se 3 (by rfl) ⟨2687306, by rfl⟩ : syracuseStep 14332301 = 5374613) B5374613
theorem B1488131 : Blo 195805 1488131 := bstep (se 1 (by rfl) ⟨1116098, by rfl⟩ : syracuseStep 1488131 = 2232197) B2232197
theorem B1685083 : Blo 195805 1685083 := bstep (se 1 (by rfl) ⟨1263812, by rfl⟩ : syracuseStep 1685083 = 2527625) B2527625
theorem B669437 : Blo 195805 669437 := bstep (se 3 (by rfl) ⟨125519, by rfl⟩ : syracuseStep 669437 = 251039) B251039
theorem B1193897 : Blo 195805 1193897 := bstep (se 2 (by rfl) ⟨447711, by rfl⟩ : syracuseStep 1193897 = 895423) B895423
theorem B1063057 : Blo 195805 1063057 := bstep (se 2 (by rfl) ⟨398646, by rfl⟩ : syracuseStep 1063057 = 797293) B797293
theorem B1489103 : Blo 195805 1489103 := bstep (se 1 (by rfl) ⟨1116827, by rfl⟩ : syracuseStep 1489103 = 2233655) B2233655
theorem B441791 : Blo 195805 441791 := bstep (se 1 (by rfl) ⟨331343, by rfl⟩ : syracuseStep 441791 = 662687) B662687
theorem B1687067 : Blo 195805 1687067 := bstep (se 1 (by rfl) ⟨1265300, by rfl⟩ : syracuseStep 1687067 = 2530601) B2530601
theorem B1130861 : Blo 195805 1130861 := bstep (se 3 (by rfl) ⟨212036, by rfl⟩ : syracuseStep 1130861 = 424073) B424073
theorem B443105 : Blo 195805 443105 := bstep (se 2 (by rfl) ⟨166164, by rfl⟩ : syracuseStep 443105 = 332329) B332329
theorem B443951 : Blo 195805 443951 := bstep (se 1 (by rfl) ⟨332963, by rfl⟩ : syracuseStep 443951 = 665927) B665927
theorem B5458691 : Blo 195805 5458691 := bstep (se 1 (by rfl) ⟨4094018, by rfl⟩ : syracuseStep 5458691 = 8188037) B8188037
theorem B1134233 : Blo 195805 1134233 := bstep (se 2 (by rfl) ⟨425337, by rfl⟩ : syracuseStep 1134233 = 850675) B850675
theorem B446345 : Blo 195805 446345 := bstep (se 2 (by rfl) ⟨167379, by rfl⟩ : syracuseStep 446345 = 334759) B334759
theorem B839929 : Blo 195805 839929 := bstep (se 2 (by rfl) ⟨314973, by rfl⟩ : syracuseStep 839929 = 629947) B629947
theorem B447119 : Blo 195805 447119 := bstep (se 1 (by rfl) ⟨335339, by rfl⟩ : syracuseStep 447119 = 670679) B670679
theorem B447209 : Blo 195805 447209 := bstep (se 2 (by rfl) ⟨167703, by rfl⟩ : syracuseStep 447209 = 335407) B335407
theorem B1266479 : Blo 195805 1266479 := bstep (se 1 (by rfl) ⟨949859, by rfl⟩ : syracuseStep 1266479 = 1899719) B1899719
theorem B447515 : Blo 195805 447515 := bstep (se 1 (by rfl) ⟨335636, by rfl⟩ : syracuseStep 447515 = 671273) B671273
theorem B251839 : Blo 195805 251839 := bstep (se 1 (by rfl) ⟨188879, by rfl⟩ : syracuseStep 251839 = 377759) B377759
theorem B448559 : Blo 195805 448559 := bstep (se 1 (by rfl) ⟨336419, by rfl⟩ : syracuseStep 448559 = 672839) B672839
theorem B1432075 : Blo 195805 1432075 := bstep (se 1 (by rfl) ⟨1074056, by rfl⟩ : syracuseStep 1432075 = 2148113) B2148113
theorem B449135 : Blo 195805 449135 := bstep (se 1 (by rfl) ⟨336851, by rfl⟩ : syracuseStep 449135 = 673703) B673703
theorem B744673 : Blo 195805 744673 := bstep (se 2 (by rfl) ⟨279252, by rfl⟩ : syracuseStep 744673 = 558505) B558505
theorem B1891997 : Blo 195805 1891997 := bstep (se 3 (by rfl) ⟨354749, by rfl⟩ : syracuseStep 1891997 = 709499) B709499
theorem B221935 : Blo 195805 221935 := bstep (se 1 (by rfl) ⟨166451, by rfl⟩ : syracuseStep 221935 = 332903) B332903
theorem B844627 : Blo 195805 844627 := bstep (se 1 (by rfl) ⟨633470, by rfl⟩ : syracuseStep 844627 = 1266941) B1266941
theorem B747575 : Blo 195805 747575 := bstep (se 1 (by rfl) ⟨560681, by rfl⟩ : syracuseStep 747575 = 1121363) B1121363
theorem B2354003 : Blo 195805 2354003 := bstep (se 1 (by rfl) ⟨1765502, by rfl⟩ : syracuseStep 2354003 = 3531005) B3531005
theorem B1600361 : Blo 195805 1600361 := bstep (se 2 (by rfl) ⟨600135, by rfl⟩ : syracuseStep 1600361 = 1200271) B1200271
theorem B2158811 : Blo 195805 2158811 := bstep (se 1 (by rfl) ⟨1619108, by rfl⟩ : syracuseStep 2158811 = 3238217) B3238217
theorem B4584431 : Blo 195805 4584431 := bstep (se 1 (by rfl) ⟨3438323, by rfl⟩ : syracuseStep 4584431 = 6876647) B6876647
theorem B3209149 : Blo 195805 3209149 := bstep (se 3 (by rfl) ⟨601715, by rfl⟩ : syracuseStep 3209149 = 1203431) B1203431
theorem B294185 : Blo 195805 294185 := bstep (se 2 (by rfl) ⟨110319, by rfl⟩ : syracuseStep 294185 = 220639) B220639
theorem B5406263 : Blo 195805 5406263 := bstep (se 1 (by rfl) ⟨4054697, by rfl⟩ : syracuseStep 5406263 = 8109395) B8109395
theorem B196287 : Blo 195805 196287 := bstep (se 1 (by rfl) ⟨147215, by rfl⟩ : syracuseStep 196287 = 294431) B294431
theorem B196847 : Blo 195805 196847 := bstep (se 1 (by rfl) ⟨147635, by rfl⟩ : syracuseStep 196847 = 295271) B295271
theorem B753907 : Blo 195805 753907 := bstep (se 1 (by rfl) ⟨565430, by rfl⟩ : syracuseStep 753907 = 1130861) B1130861
theorem B295403 : Blo 195805 295403 := bstep (se 1 (by rfl) ⟨221552, by rfl⟩ : syracuseStep 295403 = 443105) B443105
theorem B295913 : Blo 195805 295913 := bstep (se 2 (by rfl) ⟨110967, by rfl⟩ : syracuseStep 295913 = 221935) B221935
theorem B295967 : Blo 195805 295967 := bstep (se 1 (by rfl) ⟨221975, by rfl⟩ : syracuseStep 295967 = 443951) B443951
theorem B198247 : Blo 195805 198247 := bstep (se 1 (by rfl) ⟨148685, by rfl⟩ : syracuseStep 198247 = 297371) B297371
theorem B3639127 : Blo 195805 3639127 := bstep (se 1 (by rfl) ⟨2729345, by rfl⟩ : syracuseStep 3639127 = 5458691) B5458691
theorem B198747 : Blo 195805 198747 := bstep (se 1 (by rfl) ⟨149060, by rfl⟩ : syracuseStep 198747 = 298121) B298121
theorem B756155 : Blo 195805 756155 := bstep (se 1 (by rfl) ⟨567116, by rfl⟩ : syracuseStep 756155 = 1134233) B1134233
theorem B199119 : Blo 195805 199119 := bstep (se 1 (by rfl) ⟨149339, by rfl⟩ : syracuseStep 199119 = 298679) B298679
theorem B297563 : Blo 195805 297563 := bstep (se 1 (by rfl) ⟨223172, by rfl⟩ : syracuseStep 297563 = 446345) B446345
theorem B199527 : Blo 195805 199527 := bstep (se 1 (by rfl) ⟨149645, by rfl⟩ : syracuseStep 199527 = 299291) B299291
theorem B199551 : Blo 195805 199551 := bstep (se 1 (by rfl) ⟨149663, by rfl⟩ : syracuseStep 199551 = 299327) B299327
theorem B298079 : Blo 195805 298079 := bstep (se 1 (by rfl) ⟨223559, by rfl⟩ : syracuseStep 298079 = 447119) B447119
theorem B298139 : Blo 195805 298139 := bstep (se 1 (by rfl) ⟨223604, by rfl⟩ : syracuseStep 298139 = 447209) B447209
theorem B298343 : Blo 195805 298343 := bstep (se 1 (by rfl) ⟨223757, by rfl⟩ : syracuseStep 298343 = 447515) B447515
theorem B1118195 : Blo 195805 1118195 := bstep (se 1 (by rfl) ⟨838646, by rfl⟩ : syracuseStep 1118195 = 1677293) B1677293
theorem B299039 : Blo 195805 299039 := bstep (se 1 (by rfl) ⟨224279, by rfl⟩ : syracuseStep 299039 = 448559) B448559
theorem B35196983 : Blo 195805 35196983 := bstep (se 1 (by rfl) ⟨26397737, by rfl⟩ : syracuseStep 35196983 = 52795475) B52795475
theorem B299423 : Blo 195805 299423 := bstep (se 1 (by rfl) ⟨224567, by rfl⟩ : syracuseStep 299423 = 449135) B449135
theorem B1118879 : Blo 195805 1118879 := bstep (se 1 (by rfl) ⟨839159, by rfl⟩ : syracuseStep 1118879 = 1678319) B1678319
theorem B14291639 : Blo 195805 14291639 := bstep (se 1 (by rfl) ⟨10718729, by rfl⟩ : syracuseStep 14291639 = 21437459) B21437459
theorem B3183725 : Blo 195805 3183725 := bstep (se 3 (by rfl) ⟨596948, by rfl⟩ : syracuseStep 3183725 = 1193897) B1193897
theorem B1119905 : Blo 195805 1119905 := bstep (se 2 (by rfl) ⟨419964, by rfl⟩ : syracuseStep 1119905 = 839929) B839929
theorem B333895 : Blo 195805 333895 := bstep (se 1 (by rfl) ⟨250421, by rfl⟩ : syracuseStep 333895 = 500843) B500843
theorem B498383 : Blo 195805 498383 := bstep (se 1 (by rfl) ⟨373787, by rfl⟩ : syracuseStep 498383 = 747575) B747575
theorem B335785 : Blo 195805 335785 := bstep (se 2 (by rfl) ⟨125919, by rfl⟩ : syracuseStep 335785 = 251839) B251839
theorem B1417409 : Blo 195805 1417409 := bstep (se 2 (by rfl) ⟨531528, by rfl⟩ : syracuseStep 1417409 = 1063057) B1063057
theorem B3056287 : Blo 195805 3056287 := bstep (se 1 (by rfl) ⟨2292215, by rfl⟩ : syracuseStep 3056287 = 4584431) B4584431
theorem B1909433 : Blo 195805 1909433 := bstep (se 2 (by rfl) ⟨716037, by rfl⟩ : syracuseStep 1909433 = 1432075) B1432075
theorem B992087 : Blo 195805 992087 := bstep (se 1 (by rfl) ⟨744065, by rfl⟩ : syracuseStep 992087 = 1488131) B1488131
theorem B25109365 : Blo 195805 25109365 := bstep (se 5 (by rfl) ⟨1177001, by rfl⟩ : syracuseStep 25109365 = 2354003) B2354003
theorem B992735 : Blo 195805 992735 := bstep (se 1 (by rfl) ⟨744551, by rfl⟩ : syracuseStep 992735 = 1489103) B1489103
theorem B992897 : Blo 195805 992897 := bstep (se 2 (by rfl) ⟨372336, by rfl⟩ : syracuseStep 992897 = 744673) B744673
theorem B1124711 : Blo 195805 1124711 := bstep (se 1 (by rfl) ⟨843533, by rfl⟩ : syracuseStep 1124711 = 1687067) B1687067
theorem B502463 : Blo 195805 502463 := bstep (se 1 (by rfl) ⟨376847, by rfl⟩ : syracuseStep 502463 = 753695) B753695
theorem B2075327 : Blo 195805 2075327 := bstep (se 1 (by rfl) ⟨1556495, by rfl⟩ : syracuseStep 2075327 = 3112991) B3112991
theorem B2403755 : Blo 195805 2403755 := bstep (se 1 (by rfl) ⟨1802816, by rfl⟩ : syracuseStep 2403755 = 3605633) B3605633
theorem B1126169 : Blo 195805 1126169 := bstep (se 2 (by rfl) ⟨422313, by rfl⟩ : syracuseStep 1126169 = 844627) B844627
theorem B799145 : Blo 195805 799145 := bstep (se 2 (by rfl) ⟨299679, by rfl⟩ : syracuseStep 799145 = 599359) B599359
theorem B6796831 : Blo 195805 6796831 := bstep (se 1 (by rfl) ⟨5097623, by rfl⟩ : syracuseStep 6796831 = 10195247) B10195247
theorem B1261331 : Blo 195805 1261331 := bstep (se 1 (by rfl) ⟨945998, by rfl⟩ : syracuseStep 1261331 = 1891997) B1891997
theorem B442475 : Blo 195805 442475 := bstep (se 1 (by rfl) ⟨331856, by rfl⟩ : syracuseStep 442475 = 663713) B663713
theorem B442529 : Blo 195805 442529 := bstep (se 2 (by rfl) ⟨165948, by rfl⟩ : syracuseStep 442529 = 331897) B331897
theorem B1066907 : Blo 195805 1066907 := bstep (se 1 (by rfl) ⟨800180, by rfl⟩ : syracuseStep 1066907 = 1600361) B1600361
theorem B444527 : Blo 195805 444527 := bstep (se 1 (by rfl) ⟨333395, by rfl⟩ : syracuseStep 444527 = 666791) B666791
theorem B2246777 : Blo 195805 2246777 := bstep (se 2 (by rfl) ⟨842541, by rfl⟩ : syracuseStep 2246777 = 1685083) B1685083
theorem B4278865 : Blo 195805 4278865 := bstep (se 2 (by rfl) ⟨1604574, by rfl⟩ : syracuseStep 4278865 = 3209149) B3209149
theorem B9554867 : Blo 195805 9554867 := bstep (se 1 (by rfl) ⟨7166150, by rfl⟩ : syracuseStep 9554867 = 14332301) B14332301
theorem B445769 : Blo 195805 445769 := bstep (se 2 (by rfl) ⟨167163, by rfl⟩ : syracuseStep 445769 = 334327) B334327
theorem B446291 : Blo 195805 446291 := bstep (se 1 (by rfl) ⟨334718, by rfl⟩ : syracuseStep 446291 = 669437) B669437
theorem B23615621 : Blo 195805 23615621 := bstep (se 4 (by rfl) ⟨2213964, by rfl⟩ : syracuseStep 23615621 = 4427929) B4427929
theorem B1006343 : Blo 195805 1006343 := bstep (se 1 (by rfl) ⟨754757, by rfl⟩ : syracuseStep 1006343 = 1509515) B1509515
theorem B1137833 : Blo 195805 1137833 := bstep (se 2 (by rfl) ⟨426687, by rfl⟩ : syracuseStep 1137833 = 853375) B853375
theorem B1269863 : Blo 195805 1269863 := bstep (se 1 (by rfl) ⟨952397, by rfl⟩ : syracuseStep 1269863 = 1904795) B1904795
theorem B1007801 : Blo 195805 1007801 := bstep (se 2 (by rfl) ⟨377925, by rfl⟩ : syracuseStep 1007801 = 755851) B755851
theorem B844319 : Blo 195805 844319 := bstep (se 1 (by rfl) ⟨633239, by rfl⟩ : syracuseStep 844319 = 1266479) B1266479
theorem B222655 : Blo 195805 222655 := bstep (se 1 (by rfl) ⟨166991, by rfl⟩ : syracuseStep 222655 = 333983) B333983
theorem B223483 : Blo 195805 223483 := bstep (se 1 (by rfl) ⟨167612, by rfl⟩ : syracuseStep 223483 = 335225) B335225
theorem B1439207 : Blo 195805 1439207 := bstep (se 1 (by rfl) ⟨1079405, by rfl⟩ : syracuseStep 1439207 = 2158811) B2158811
theorem B196123 : Blo 195805 196123 := bstep (se 1 (by rfl) ⟨147092, by rfl⟩ : syracuseStep 196123 = 294185) B294185
theorem B294527 : Blo 195805 294527 := bstep (se 1 (by rfl) ⟨220895, by rfl⟩ : syracuseStep 294527 = 441791) B441791
theorem B3604175 : Blo 195805 3604175 := bstep (se 1 (by rfl) ⟨2703131, by rfl⟩ : syracuseStep 3604175 = 5406263) B5406263
theorem B294983 : Blo 195805 294983 := bstep (se 1 (by rfl) ⟨221237, by rfl⟩ : syracuseStep 294983 = 442475) B442475
theorem B295019 : Blo 195805 295019 := bstep (se 1 (by rfl) ⟨221264, by rfl⟩ : syracuseStep 295019 = 442529) B442529
theorem B196935 : Blo 195805 196935 := bstep (se 1 (by rfl) ⟨147701, by rfl⟩ : syracuseStep 196935 = 295403) B295403
theorem B197275 : Blo 195805 197275 := bstep (se 1 (by rfl) ⟨147956, by rfl⟩ : syracuseStep 197275 = 295913) B295913
theorem B197311 : Blo 195805 197311 := bstep (se 1 (by rfl) ⟨147983, by rfl⟩ : syracuseStep 197311 = 295967) B295967
theorem B296351 : Blo 195805 296351 := bstep (se 1 (by rfl) ⟨222263, by rfl⟩ : syracuseStep 296351 = 444527) B444527
theorem B198375 : Blo 195805 198375 := bstep (se 1 (by rfl) ⟨148781, by rfl⟩ : syracuseStep 198375 = 297563) B297563
theorem B296873 : Blo 195805 296873 := bstep (se 2 (by rfl) ⟨111327, by rfl⟩ : syracuseStep 296873 = 222655) B222655
theorem B198719 : Blo 195805 198719 := bstep (se 1 (by rfl) ⟨149039, by rfl⟩ : syracuseStep 198719 = 298079) B298079
theorem B198759 : Blo 195805 198759 := bstep (se 1 (by rfl) ⟨149069, by rfl⟩ : syracuseStep 198759 = 298139) B298139
theorem B297179 : Blo 195805 297179 := bstep (se 1 (by rfl) ⟨222884, by rfl⟩ : syracuseStep 297179 = 445769) B445769
theorem B198895 : Blo 195805 198895 := bstep (se 1 (by rfl) ⟨149171, by rfl⟩ : syracuseStep 198895 = 298343) B298343
theorem B4852169 : Blo 195805 4852169 := bstep (se 2 (by rfl) ⟨1819563, by rfl⟩ : syracuseStep 4852169 = 3639127) B3639127
theorem B297527 : Blo 195805 297527 := bstep (se 1 (by rfl) ⟨223145, by rfl⟩ : syracuseStep 297527 = 446291) B446291
theorem B199359 : Blo 195805 199359 := bstep (se 1 (by rfl) ⟨149519, by rfl⟩ : syracuseStep 199359 = 299039) B299039
theorem B23464655 : Blo 195805 23464655 := bstep (se 1 (by rfl) ⟨17598491, by rfl⟩ : syracuseStep 23464655 = 35196983) B35196983
theorem B199615 : Blo 195805 199615 := bstep (se 1 (by rfl) ⟨149711, by rfl⟩ : syracuseStep 199615 = 299423) B299423
theorem B297977 : Blo 195805 297977 := bstep (se 2 (by rfl) ⟨111741, by rfl⟩ : syracuseStep 297977 = 223483) B223483
theorem B5705153 : Blo 195805 5705153 := bstep (se 2 (by rfl) ⟨2139432, by rfl⟩ : syracuseStep 5705153 = 4278865) B4278865
theorem B332255 : Blo 195805 332255 := bstep (se 1 (by rfl) ⟨249191, by rfl⟩ : syracuseStep 332255 = 498383) B498383
theorem B758555 : Blo 195805 758555 := bstep (se 1 (by rfl) ⟨568916, by rfl⟩ : syracuseStep 758555 = 1137833) B1137833
theorem B562879 : Blo 195805 562879 := bstep (se 1 (by rfl) ⟨422159, by rfl⟩ : syracuseStep 562879 = 844319) B844319
theorem B661391 : Blo 195805 661391 := bstep (se 1 (by rfl) ⟨496043, by rfl⟩ : syracuseStep 661391 = 992087) B992087
theorem B661823 : Blo 195805 661823 := bstep (se 1 (by rfl) ⟨496367, by rfl⟩ : syracuseStep 661823 = 992735) B992735
theorem B661931 : Blo 195805 661931 := bstep (se 1 (by rfl) ⟨496448, by rfl⟩ : syracuseStep 661931 = 992897) B992897
theorem B334975 : Blo 195805 334975 := bstep (se 1 (by rfl) ⟨251231, by rfl⟩ : syracuseStep 334975 = 502463) B502463
theorem B1383551 : Blo 195805 1383551 := bstep (se 1 (by rfl) ⟨1037663, by rfl⟩ : syracuseStep 1383551 = 2075327) B2075327
theorem B532763 : Blo 195805 532763 := bstep (se 1 (by rfl) ⟨399572, by rfl⟩ : syracuseStep 532763 = 799145) B799145
theorem B959471 : Blo 195805 959471 := bstep (se 1 (by rfl) ⟨719603, by rfl⟩ : syracuseStep 959471 = 1439207) B1439207
theorem B2402783 : Blo 195805 2402783 := bstep (se 1 (by rfl) ⟨1802087, by rfl⟩ : syracuseStep 2402783 = 3604175) B3604175
theorem B4075049 : Blo 195805 4075049 := bstep (se 2 (by rfl) ⟨1528143, by rfl⟩ : syracuseStep 4075049 = 3056287) B3056287
theorem B798461 : Blo 195805 798461 := bstep (se 3 (by rfl) ⟨149711, by rfl⟩ : syracuseStep 798461 = 299423) B299423
theorem B504103 : Blo 195805 504103 := bstep (se 1 (by rfl) ⟨378077, by rfl⟩ : syracuseStep 504103 = 756155) B756155
theorem B6369911 : Blo 195805 6369911 := bstep (se 1 (by rfl) ⟨4777433, by rfl⟩ : syracuseStep 6369911 = 9554867) B9554867
theorem B15743747 : Blo 195805 15743747 := bstep (se 1 (by rfl) ⟨11807810, by rfl⟩ : syracuseStep 15743747 = 23615621) B23615621
theorem B670895 : Blo 195805 670895 := bstep (se 1 (by rfl) ⟨503171, by rfl⟩ : syracuseStep 670895 = 1006343) B1006343
theorem B671867 : Blo 195805 671867 := bstep (se 1 (by rfl) ⟨503900, by rfl⟩ : syracuseStep 671867 = 1007801) B1007801
theorem B9062441 : Blo 195805 9062441 := bstep (se 2 (by rfl) ⟨3398415, by rfl⟩ : syracuseStep 9062441 = 6796831) B6796831
theorem B445193 : Blo 195805 445193 := bstep (se 2 (by rfl) ⟨166947, by rfl⟩ : syracuseStep 445193 = 333895) B333895
theorem B840887 : Blo 195805 840887 := bstep (se 1 (by rfl) ⟨630665, by rfl⟩ : syracuseStep 840887 = 1261331) B1261331
theorem B447713 : Blo 195805 447713 := bstep (se 2 (by rfl) ⟨167892, by rfl⟩ : syracuseStep 447713 = 335785) B335785
theorem B1005209 : Blo 195805 1005209 := bstep (se 2 (by rfl) ⟨376953, by rfl⟩ : syracuseStep 1005209 = 753907) B753907
theorem B33479153 : Blo 195805 33479153 := bstep (se 2 (by rfl) ⟨12554682, by rfl⟩ : syracuseStep 33479153 = 25109365) B25109365
theorem B711271 : Blo 195805 711271 := bstep (se 1 (by rfl) ⟨533453, by rfl⟩ : syracuseStep 711271 = 1066907) B1066907
theorem B1497851 : Blo 195805 1497851 := bstep (se 1 (by rfl) ⟨1123388, by rfl⟩ : syracuseStep 1497851 = 2246777) B2246777
theorem B745463 : Blo 195805 745463 := bstep (se 1 (by rfl) ⟨559097, by rfl⟩ : syracuseStep 745463 = 1118195) B1118195
theorem B745919 : Blo 195805 745919 := bstep (se 1 (by rfl) ⟨559439, by rfl⟩ : syracuseStep 745919 = 1118879) B1118879
theorem B9527759 : Blo 195805 9527759 := bstep (se 1 (by rfl) ⟨7145819, by rfl⟩ : syracuseStep 9527759 = 14291639) B14291639
theorem B2122483 : Blo 195805 2122483 := bstep (se 1 (by rfl) ⟨1591862, by rfl⟩ : syracuseStep 2122483 = 3183725) B3183725
theorem B746603 : Blo 195805 746603 := bstep (se 1 (by rfl) ⟨559952, by rfl⟩ : syracuseStep 746603 = 1119905) B1119905
theorem B846575 : Blo 195805 846575 := bstep (se 1 (by rfl) ⟨634931, by rfl⟩ : syracuseStep 846575 = 1269863) B1269863
theorem B944939 : Blo 195805 944939 := bstep (se 1 (by rfl) ⟨708704, by rfl⟩ : syracuseStep 944939 = 1417409) B1417409
theorem B1272955 : Blo 195805 1272955 := bstep (se 1 (by rfl) ⟨954716, by rfl⟩ : syracuseStep 1272955 = 1909433) B1909433
theorem B749807 : Blo 195805 749807 := bstep (se 1 (by rfl) ⟨562355, by rfl⟩ : syracuseStep 749807 = 1124711) B1124711
theorem B1602503 : Blo 195805 1602503 := bstep (se 1 (by rfl) ⟨1201877, by rfl⟩ : syracuseStep 1602503 = 2403755) B2403755
theorem B750779 : Blo 195805 750779 := bstep (se 1 (by rfl) ⟨563084, by rfl⟩ : syracuseStep 750779 = 1126169) B1126169
theorem B196351 : Blo 195805 196351 := bstep (se 1 (by rfl) ⟨147263, by rfl⟩ : syracuseStep 196351 = 294527) B294527
theorem B196655 : Blo 195805 196655 := bstep (se 1 (by rfl) ⟨147491, by rfl⟩ : syracuseStep 196655 = 294983) B294983
theorem B196679 : Blo 195805 196679 := bstep (se 1 (by rfl) ⟨147509, by rfl⟩ : syracuseStep 196679 = 295019) B295019
theorem B197567 : Blo 195805 197567 := bstep (se 1 (by rfl) ⟨148175, by rfl⟩ : syracuseStep 197567 = 296351) B296351
theorem B197915 : Blo 195805 197915 := bstep (se 1 (by rfl) ⟨148436, by rfl⟩ : syracuseStep 197915 = 296873) B296873
theorem B198119 : Blo 195805 198119 := bstep (se 1 (by rfl) ⟨148589, by rfl⟩ : syracuseStep 198119 = 297179) B297179
theorem B198351 : Blo 195805 198351 := bstep (se 1 (by rfl) ⟨148763, by rfl⟩ : syracuseStep 198351 = 297527) B297527
theorem B296795 : Blo 195805 296795 := bstep (se 1 (by rfl) ⟨222596, by rfl⟩ : syracuseStep 296795 = 445193) B445193
theorem B198651 : Blo 195805 198651 := bstep (se 1 (by rfl) ⟨148988, by rfl⟩ : syracuseStep 198651 = 297977) B297977
theorem B3803435 : Blo 195805 3803435 := bstep (se 1 (by rfl) ⟨2852576, by rfl⟩ : syracuseStep 3803435 = 5705153) B5705153
theorem B560591 : Blo 195805 560591 := bstep (se 1 (by rfl) ⟨420443, by rfl⟩ : syracuseStep 560591 = 840887) B840887
theorem B298475 : Blo 195805 298475 := bstep (se 1 (by rfl) ⟨223856, by rfl⟩ : syracuseStep 298475 = 447713) B447713
theorem B22319435 : Blo 195805 22319435 := bstep (se 1 (by rfl) ⟨16739576, by rfl⟩ : syracuseStep 22319435 = 33479153) B33479153
theorem B922367 : Blo 195805 922367 := bstep (se 1 (by rfl) ⟨691775, by rfl⟩ : syracuseStep 922367 = 1383551) B1383551
theorem B496975 : Blo 195805 496975 := bstep (se 1 (by rfl) ⟨372731, by rfl⟩ : syracuseStep 496975 = 745463) B745463
theorem B497279 : Blo 195805 497279 := bstep (se 1 (by rfl) ⟨372959, by rfl⟩ : syracuseStep 497279 = 745919) B745919
theorem B497735 : Blo 195805 497735 := bstep (se 1 (by rfl) ⟨373301, by rfl⟩ : syracuseStep 497735 = 746603) B746603
theorem B564383 : Blo 195805 564383 := bstep (se 1 (by rfl) ⟨423287, by rfl⟩ : syracuseStep 564383 = 846575) B846575
theorem B629959 : Blo 195805 629959 := bstep (se 1 (by rfl) ⟨472469, by rfl⟩ : syracuseStep 629959 = 944939) B944939
theorem B532307 : Blo 195805 532307 := bstep (se 1 (by rfl) ⟨399230, by rfl⟩ : syracuseStep 532307 = 798461) B798461
theorem B499871 : Blo 195805 499871 := bstep (se 1 (by rfl) ⟨374903, by rfl⟩ : syracuseStep 499871 = 749807) B749807
theorem B500519 : Blo 195805 500519 := bstep (se 1 (by rfl) ⟨375389, by rfl⟩ : syracuseStep 500519 = 750779) B750779
theorem B10495831 : Blo 195805 10495831 := bstep (se 1 (by rfl) ⟨7871873, by rfl⟩ : syracuseStep 10495831 = 15743747) B15743747
theorem B2829977 : Blo 195805 2829977 := bstep (se 2 (by rfl) ⟨1061241, by rfl⟩ : syracuseStep 2829977 = 2122483) B2122483
theorem B6041627 : Blo 195805 6041627 := bstep (se 1 (by rfl) ⟨4531220, by rfl⟩ : syracuseStep 6041627 = 9062441) B9062441
theorem B15643103 : Blo 195805 15643103 := bstep (se 1 (by rfl) ⟨11732327, by rfl⟩ : syracuseStep 15643103 = 23464655) B23464655
theorem B505703 : Blo 195805 505703 := bstep (se 1 (by rfl) ⟨379277, by rfl⟩ : syracuseStep 505703 = 758555) B758555
theorem B670139 : Blo 195805 670139 := bstep (se 1 (by rfl) ⟨502604, by rfl⟩ : syracuseStep 670139 = 1005209) B1005209
theorem B440927 : Blo 195805 440927 := bstep (se 1 (by rfl) ⟨330695, by rfl⟩ : syracuseStep 440927 = 661391) B661391
theorem B441215 : Blo 195805 441215 := bstep (se 1 (by rfl) ⟨330911, by rfl⟩ : syracuseStep 441215 = 661823) B661823
theorem B441287 : Blo 195805 441287 := bstep (se 1 (by rfl) ⟨330965, by rfl⟩ : syracuseStep 441287 = 661931) B661931
theorem B998567 : Blo 195805 998567 := bstep (se 1 (by rfl) ⟨748925, by rfl⟩ : syracuseStep 998567 = 1497851) B1497851
theorem B672137 : Blo 195805 672137 := bstep (se 2 (by rfl) ⟨252051, by rfl⟩ : syracuseStep 672137 = 504103) B504103
theorem B639647 : Blo 195805 639647 := bstep (se 1 (by rfl) ⟨479735, by rfl⟩ : syracuseStep 639647 = 959471) B959471
theorem B4246607 : Blo 195805 4246607 := bstep (se 1 (by rfl) ⟨3184955, by rfl⟩ : syracuseStep 4246607 = 6369911) B6369911
theorem B1068335 : Blo 195805 1068335 := bstep (se 1 (by rfl) ⟨801251, by rfl⟩ : syracuseStep 1068335 = 1602503) B1602503
theorem B446633 : Blo 195805 446633 := bstep (se 2 (by rfl) ⟨167487, by rfl⟩ : syracuseStep 446633 = 334975) B334975
theorem B447263 : Blo 195805 447263 := bstep (se 1 (by rfl) ⟨335447, by rfl⟩ : syracuseStep 447263 = 670895) B670895
theorem B447911 : Blo 195805 447911 := bstep (se 1 (by rfl) ⟨335933, by rfl⟩ : syracuseStep 447911 = 671867) B671867
theorem B3234779 : Blo 195805 3234779 := bstep (se 1 (by rfl) ⟨2426084, by rfl⟩ : syracuseStep 3234779 = 4852169) B4852169
theorem B221503 : Blo 195805 221503 := bstep (se 1 (by rfl) ⟨166127, by rfl⟩ : syracuseStep 221503 = 332255) B332255
theorem B1697273 : Blo 195805 1697273 := bstep (se 2 (by rfl) ⟨636477, by rfl⟩ : syracuseStep 1697273 = 1272955) B1272955
theorem B355175 : Blo 195805 355175 := bstep (se 1 (by rfl) ⟨266381, by rfl⟩ : syracuseStep 355175 = 532763) B532763
theorem B6351839 : Blo 195805 6351839 := bstep (se 1 (by rfl) ⟨4763879, by rfl⟩ : syracuseStep 6351839 = 9527759) B9527759
theorem B1601855 : Blo 195805 1601855 := bstep (se 1 (by rfl) ⟨1201391, by rfl⟩ : syracuseStep 1601855 = 2402783) B2402783
theorem B750505 : Blo 195805 750505 := bstep (se 2 (by rfl) ⟨281439, by rfl⟩ : syracuseStep 750505 = 562879) B562879
theorem B2716699 : Blo 195805 2716699 := bstep (se 1 (by rfl) ⟨2037524, by rfl⟩ : syracuseStep 2716699 = 4075049) B4075049
theorem B948361 : Blo 195805 948361 := bstep (se 2 (by rfl) ⟨355635, by rfl⟩ : syracuseStep 948361 = 711271) B711271
theorem B295337 : Blo 195805 295337 := bstep (se 2 (by rfl) ⟨110751, by rfl⟩ : syracuseStep 295337 = 221503) B221503
theorem B426431 : Blo 195805 426431 := bstep (se 1 (by rfl) ⟨319823, by rfl⟩ : syracuseStep 426431 = 639647) B639647
theorem B197863 : Blo 195805 197863 := bstep (se 1 (by rfl) ⟨148397, by rfl⟩ : syracuseStep 197863 = 296795) B296795
theorem B41714941 : Blo 195805 41714941 := bstep (se 3 (by rfl) ⟨7821551, by rfl⟩ : syracuseStep 41714941 = 15643103) B15643103
theorem B2459645 : Blo 195805 2459645 := bstep (se 3 (by rfl) ⟨461183, by rfl⟩ : syracuseStep 2459645 = 922367) B922367
theorem B198983 : Blo 195805 198983 := bstep (se 1 (by rfl) ⟨149237, by rfl⟩ : syracuseStep 198983 = 298475) B298475
theorem B13994441 : Blo 195805 13994441 := bstep (se 2 (by rfl) ⟨5247915, by rfl⟩ : syracuseStep 13994441 = 10495831) B10495831
theorem B297755 : Blo 195805 297755 := bstep (se 1 (by rfl) ⟨223316, by rfl⟩ : syracuseStep 297755 = 446633) B446633
theorem B14879623 : Blo 195805 14879623 := bstep (se 1 (by rfl) ⟨11159717, by rfl⟩ : syracuseStep 14879623 = 22319435) B22319435
theorem B298175 : Blo 195805 298175 := bstep (se 1 (by rfl) ⟨223631, by rfl⟩ : syracuseStep 298175 = 447263) B447263
theorem B298607 : Blo 195805 298607 := bstep (se 1 (by rfl) ⟨223955, by rfl⟩ : syracuseStep 298607 = 447911) B447911
theorem B331519 : Blo 195805 331519 := bstep (se 1 (by rfl) ⟨248639, by rfl⟩ : syracuseStep 331519 = 497279) B497279
theorem B331823 : Blo 195805 331823 := bstep (se 1 (by rfl) ⟨248867, by rfl⟩ : syracuseStep 331823 = 497735) B497735
theorem B333247 : Blo 195805 333247 := bstep (se 1 (by rfl) ⟨249935, by rfl⟩ : syracuseStep 333247 = 499871) B499871
theorem B333679 : Blo 195805 333679 := bstep (se 1 (by rfl) ⟨250259, by rfl⟩ : syracuseStep 333679 = 500519) B500519
theorem B662633 : Blo 195805 662633 := bstep (se 2 (by rfl) ⟨248487, by rfl⟩ : syracuseStep 662633 = 496975) B496975
theorem B236783 : Blo 195805 236783 := bstep (se 1 (by rfl) ⟨177587, by rfl⟩ : syracuseStep 236783 = 355175) B355175
theorem B4234559 : Blo 195805 4234559 := bstep (se 1 (by rfl) ⟨3175919, by rfl⟩ : syracuseStep 4234559 = 6351839) B6351839
theorem B337135 : Blo 195805 337135 := bstep (se 1 (by rfl) ⟨252851, by rfl⟩ : syracuseStep 337135 = 505703) B505703
theorem B665711 : Blo 195805 665711 := bstep (se 1 (by rfl) ⟨499283, by rfl⟩ : syracuseStep 665711 = 998567) B998567
theorem B2535623 : Blo 195805 2535623 := bstep (se 1 (by rfl) ⟨1901717, by rfl⟩ : syracuseStep 2535623 = 3803435) B3803435
theorem B2831071 : Blo 195805 2831071 := bstep (se 1 (by rfl) ⟨2123303, by rfl⟩ : syracuseStep 2831071 = 4246607) B4246607
theorem B373727 : Blo 195805 373727 := bstep (se 1 (by rfl) ⟨280295, by rfl⟩ : syracuseStep 373727 = 560591) B560591
theorem B376255 : Blo 195805 376255 := bstep (se 1 (by rfl) ⟨282191, by rfl⟩ : syracuseStep 376255 = 564383) B564383
theorem B1131515 : Blo 195805 1131515 := bstep (se 1 (by rfl) ⟨848636, by rfl⟩ : syracuseStep 1131515 = 1697273) B1697273
theorem B1000673 : Blo 195805 1000673 := bstep (se 2 (by rfl) ⟨375252, by rfl⟩ : syracuseStep 1000673 = 750505) B750505
theorem B3622265 : Blo 195805 3622265 := bstep (se 2 (by rfl) ⟨1358349, by rfl⟩ : syracuseStep 3622265 = 2716699) B2716699
theorem B1886651 : Blo 195805 1886651 := bstep (se 1 (by rfl) ⟨1414988, by rfl⟩ : syracuseStep 1886651 = 2829977) B2829977
theorem B1264481 : Blo 195805 1264481 := bstep (se 2 (by rfl) ⟨474180, by rfl⟩ : syracuseStep 1264481 = 948361) B948361
theorem B1067903 : Blo 195805 1067903 := bstep (se 1 (by rfl) ⟨800927, by rfl⟩ : syracuseStep 1067903 = 1601855) B1601855
theorem B839945 : Blo 195805 839945 := bstep (se 2 (by rfl) ⟨314979, by rfl⟩ : syracuseStep 839945 = 629959) B629959
theorem B446759 : Blo 195805 446759 := bstep (se 1 (by rfl) ⟨335069, by rfl⟩ : syracuseStep 446759 = 670139) B670139
theorem B448091 : Blo 195805 448091 := bstep (se 1 (by rfl) ⟨336068, by rfl⟩ : syracuseStep 448091 = 672137) B672137
theorem B712223 : Blo 195805 712223 := bstep (se 1 (by rfl) ⟨534167, by rfl⟩ : syracuseStep 712223 = 1068335) B1068335
theorem B2156519 : Blo 195805 2156519 := bstep (se 1 (by rfl) ⟨1617389, by rfl⟩ : syracuseStep 2156519 = 3234779) B3234779
theorem B354871 : Blo 195805 354871 := bstep (se 1 (by rfl) ⟨266153, by rfl⟩ : syracuseStep 354871 = 532307) B532307
theorem B4027751 : Blo 195805 4027751 := bstep (se 1 (by rfl) ⟨3020813, by rfl⟩ : syracuseStep 4027751 = 6041627) B6041627
theorem B293951 : Blo 195805 293951 := bstep (se 1 (by rfl) ⟨220463, by rfl⟩ : syracuseStep 293951 = 440927) B440927
theorem B294143 : Blo 195805 294143 := bstep (se 1 (by rfl) ⟨220607, by rfl⟩ : syracuseStep 294143 = 441215) B441215
theorem B294191 : Blo 195805 294191 := bstep (se 1 (by rfl) ⟨220643, by rfl⟩ : syracuseStep 294191 = 441287) B441287
theorem B196891 : Blo 195805 196891 := bstep (se 1 (by rfl) ⟨147668, by rfl⟩ : syracuseStep 196891 = 295337) B295337
theorem B754343 : Blo 195805 754343 := bstep (se 1 (by rfl) ⟨565757, by rfl⟩ : syracuseStep 754343 = 1131515) B1131515
theorem B1639763 : Blo 195805 1639763 := bstep (se 1 (by rfl) ⟨1229822, by rfl⟩ : syracuseStep 1639763 = 2459645) B2459645
theorem B198503 : Blo 195805 198503 := bstep (se 1 (by rfl) ⟨148877, by rfl⟩ : syracuseStep 198503 = 297755) B297755
theorem B198783 : Blo 195805 198783 := bstep (se 1 (by rfl) ⟨149087, by rfl⟩ : syracuseStep 198783 = 298175) B298175
theorem B199071 : Blo 195805 199071 := bstep (se 1 (by rfl) ⟨149303, by rfl⟩ : syracuseStep 199071 = 298607) B298607
theorem B559963 : Blo 195805 559963 := bstep (se 1 (by rfl) ⟨419972, by rfl⟩ : syracuseStep 559963 = 839945) B839945
theorem B297839 : Blo 195805 297839 := bstep (se 1 (by rfl) ⟨223379, by rfl⟩ : syracuseStep 297839 = 446759) B446759
theorem B298727 : Blo 195805 298727 := bstep (se 1 (by rfl) ⟨224045, by rfl⟩ : syracuseStep 298727 = 448091) B448091
theorem B3774761 : Blo 195805 3774761 := bstep (se 2 (by rfl) ⟨1415535, by rfl⟩ : syracuseStep 3774761 = 2831071) B2831071
theorem B631421 : Blo 195805 631421 := bstep (se 3 (by rfl) ⟨118391, by rfl⟩ : syracuseStep 631421 = 236783) B236783
theorem B501673 : Blo 195805 501673 := bstep (se 2 (by rfl) ⟨188127, by rfl⟩ : syracuseStep 501673 = 376255) B376255
theorem B667115 : Blo 195805 667115 := bstep (se 1 (by rfl) ⟨500336, by rfl⟩ : syracuseStep 667115 = 1000673) B1000673
theorem B1257767 : Blo 195805 1257767 := bstep (se 1 (by rfl) ⟨943325, by rfl⟩ : syracuseStep 1257767 = 1886651) B1886651
theorem B55619921 : Blo 195805 55619921 := bstep (se 2 (by rfl) ⟨20857470, by rfl⟩ : syracuseStep 55619921 = 41714941) B41714941
theorem B19839497 : Blo 195805 19839497 := bstep (se 2 (by rfl) ⟨7439811, by rfl⟩ : syracuseStep 19839497 = 14879623) B14879623
theorem B441755 : Blo 195805 441755 := bstep (se 1 (by rfl) ⟨331316, by rfl⟩ : syracuseStep 441755 = 662633) B662633
theorem B442025 : Blo 195805 442025 := bstep (se 2 (by rfl) ⟨165759, by rfl⟩ : syracuseStep 442025 = 331519) B331519
theorem B474815 : Blo 195805 474815 := bstep (se 1 (by rfl) ⟨356111, by rfl⟩ : syracuseStep 474815 = 712223) B712223
theorem B443807 : Blo 195805 443807 := bstep (se 1 (by rfl) ⟨332855, by rfl⟩ : syracuseStep 443807 = 665711) B665711
theorem B444329 : Blo 195805 444329 := bstep (se 2 (by rfl) ⟨166623, by rfl⟩ : syracuseStep 444329 = 333247) B333247
theorem B444905 : Blo 195805 444905 := bstep (se 2 (by rfl) ⟨166839, by rfl⟩ : syracuseStep 444905 = 333679) B333679
theorem B1690415 : Blo 195805 1690415 := bstep (se 1 (by rfl) ⟨1267811, by rfl⟩ : syracuseStep 1690415 = 2535623) B2535623
theorem B249151 : Blo 195805 249151 := bstep (se 1 (by rfl) ⟨186863, by rfl⟩ : syracuseStep 249151 = 373727) B373727
theorem B11292157 : Blo 195805 11292157 := bstep (se 3 (by rfl) ⟨2117279, by rfl⟩ : syracuseStep 11292157 = 4234559) B4234559
theorem B2414843 : Blo 195805 2414843 := bstep (se 1 (by rfl) ⟨1811132, by rfl⟩ : syracuseStep 2414843 = 3622265) B3622265
theorem B1137149 : Blo 195805 1137149 := bstep (se 3 (by rfl) ⟨213215, by rfl⟩ : syracuseStep 1137149 = 426431) B426431
theorem B9329627 : Blo 195805 9329627 := bstep (se 1 (by rfl) ⟨6997220, by rfl⟩ : syracuseStep 9329627 = 13994441) B13994441
theorem B449513 : Blo 195805 449513 := bstep (se 2 (by rfl) ⟨168567, by rfl⟩ : syracuseStep 449513 = 337135) B337135
theorem B842987 : Blo 195805 842987 := bstep (se 1 (by rfl) ⟨632240, by rfl⟩ : syracuseStep 842987 = 1264481) B1264481
theorem B711935 : Blo 195805 711935 := bstep (se 1 (by rfl) ⟨533951, by rfl⟩ : syracuseStep 711935 = 1067903) B1067903
theorem B221215 : Blo 195805 221215 := bstep (se 1 (by rfl) ⟨165911, by rfl⟩ : syracuseStep 221215 = 331823) B331823
theorem B1892645 : Blo 195805 1892645 := bstep (se 4 (by rfl) ⟨177435, by rfl⟩ : syracuseStep 1892645 = 354871) B354871
theorem B1437679 : Blo 195805 1437679 := bstep (se 1 (by rfl) ⟨1078259, by rfl⟩ : syracuseStep 1437679 = 2156519) B2156519
theorem B2685167 : Blo 195805 2685167 := bstep (se 1 (by rfl) ⟨2013875, by rfl⟩ : syracuseStep 2685167 = 4027751) B4027751
theorem B195967 : Blo 195805 195967 := bstep (se 1 (by rfl) ⟨146975, by rfl⟩ : syracuseStep 195967 = 293951) B293951
theorem B196095 : Blo 195805 196095 := bstep (se 1 (by rfl) ⟨147071, by rfl⟩ : syracuseStep 196095 = 294143) B294143
theorem B196127 : Blo 195805 196127 := bstep (se 1 (by rfl) ⟨147095, by rfl⟩ : syracuseStep 196127 = 294191) B294191
theorem B294953 : Blo 195805 294953 := bstep (se 2 (by rfl) ⟨110607, by rfl⟩ : syracuseStep 294953 = 221215) B221215
theorem B295871 : Blo 195805 295871 := bstep (se 1 (by rfl) ⟨221903, by rfl⟩ : syracuseStep 295871 = 443807) B443807
theorem B296219 : Blo 195805 296219 := bstep (se 1 (by rfl) ⟨222164, by rfl⟩ : syracuseStep 296219 = 444329) B444329
theorem B296603 : Blo 195805 296603 := bstep (se 1 (by rfl) ⟨222452, by rfl⟩ : syracuseStep 296603 = 444905) B444905
theorem B198559 : Blo 195805 198559 := bstep (se 1 (by rfl) ⟨148919, by rfl⟩ : syracuseStep 198559 = 297839) B297839
theorem B199151 : Blo 195805 199151 := bstep (se 1 (by rfl) ⟨149363, by rfl⟩ : syracuseStep 199151 = 298727) B298727
theorem B1609895 : Blo 195805 1609895 := bstep (se 1 (by rfl) ⟨1207421, by rfl⟩ : syracuseStep 1609895 = 2414843) B2414843
theorem B758099 : Blo 195805 758099 := bstep (se 1 (by rfl) ⟨568574, by rfl⟩ : syracuseStep 758099 = 1137149) B1137149
theorem B332201 : Blo 195805 332201 := bstep (se 2 (by rfl) ⟨124575, by rfl⟩ : syracuseStep 332201 = 249151) B249151
theorem B299675 : Blo 195805 299675 := bstep (se 1 (by rfl) ⟨224756, by rfl⟩ : syracuseStep 299675 = 449513) B449513
theorem B561991 : Blo 195805 561991 := bstep (se 1 (by rfl) ⟨421493, by rfl⟩ : syracuseStep 561991 = 842987) B842987
theorem B24879005 : Blo 195805 24879005 := bstep (se 3 (by rfl) ⟨4664813, by rfl⟩ : syracuseStep 24879005 = 9329627) B9329627
theorem B502895 : Blo 195805 502895 := bstep (se 1 (by rfl) ⟨377171, by rfl⟩ : syracuseStep 502895 = 754343) B754343
theorem B1093175 : Blo 195805 1093175 := bstep (se 1 (by rfl) ⟨819881, by rfl⟩ : syracuseStep 1093175 = 1639763) B1639763
theorem B1126943 : Blo 195805 1126943 := bstep (se 1 (by rfl) ⟨845207, by rfl⟩ : syracuseStep 1126943 = 1690415) B1690415
theorem B668897 : Blo 195805 668897 := bstep (se 2 (by rfl) ⟨250836, by rfl⟩ : syracuseStep 668897 = 501673) B501673
theorem B15056209 : Blo 195805 15056209 := bstep (se 2 (by rfl) ⟨5646078, by rfl⟩ : syracuseStep 15056209 = 11292157) B11292157
theorem B474623 : Blo 195805 474623 := bstep (se 1 (by rfl) ⟨355967, by rfl⟩ : syracuseStep 474623 = 711935) B711935
theorem B1916905 : Blo 195805 1916905 := bstep (se 2 (by rfl) ⟨718839, by rfl⟩ : syracuseStep 1916905 = 1437679) B1437679
theorem B1261763 : Blo 195805 1261763 := bstep (se 1 (by rfl) ⟨946322, by rfl⟩ : syracuseStep 1261763 = 1892645) B1892645
theorem B52905325 : Blo 195805 52905325 := bstep (se 3 (by rfl) ⟨9919748, by rfl⟩ : syracuseStep 52905325 = 19839497) B19839497
theorem B444743 : Blo 195805 444743 := bstep (se 1 (by rfl) ⟨333557, by rfl⟩ : syracuseStep 444743 = 667115) B667115
theorem B838511 : Blo 195805 838511 := bstep (se 1 (by rfl) ⟨628883, by rfl⟩ : syracuseStep 838511 = 1257767) B1257767
theorem B37079947 : Blo 195805 37079947 := bstep (se 1 (by rfl) ⟨27809960, by rfl⟩ : syracuseStep 37079947 = 55619921) B55619921
theorem B1790111 : Blo 195805 1790111 := bstep (se 1 (by rfl) ⟨1342583, by rfl⟩ : syracuseStep 1790111 = 2685167) B2685167
theorem B316543 : Blo 195805 316543 := bstep (se 1 (by rfl) ⟨237407, by rfl⟩ : syracuseStep 316543 = 474815) B474815
theorem B746617 : Blo 195805 746617 := bstep (se 2 (by rfl) ⟨279981, by rfl⟩ : syracuseStep 746617 = 559963) B559963
theorem B2516507 : Blo 195805 2516507 := bstep (se 1 (by rfl) ⟨1887380, by rfl⟩ : syracuseStep 2516507 = 3774761) B3774761
theorem B420947 : Blo 195805 420947 := bstep (se 1 (by rfl) ⟨315710, by rfl⟩ : syracuseStep 420947 = 631421) B631421
theorem B294503 : Blo 195805 294503 := bstep (se 1 (by rfl) ⟨220877, by rfl⟩ : syracuseStep 294503 = 441755) B441755
theorem B294683 : Blo 195805 294683 := bstep (se 1 (by rfl) ⟨221012, by rfl⟩ : syracuseStep 294683 = 442025) B442025
theorem B196635 : Blo 195805 196635 := bstep (se 1 (by rfl) ⟨147476, by rfl⟩ : syracuseStep 196635 = 294953) B294953
theorem B197247 : Blo 195805 197247 := bstep (se 1 (by rfl) ⟨147935, by rfl⟩ : syracuseStep 197247 = 295871) B295871
theorem B197479 : Blo 195805 197479 := bstep (se 1 (by rfl) ⟨148109, by rfl⟩ : syracuseStep 197479 = 296219) B296219
theorem B197735 : Blo 195805 197735 := bstep (se 1 (by rfl) ⟨148301, by rfl⟩ : syracuseStep 197735 = 296603) B296603
theorem B296495 : Blo 195805 296495 := bstep (se 1 (by rfl) ⟨222371, by rfl⟩ : syracuseStep 296495 = 444743) B444743
theorem B559007 : Blo 195805 559007 := bstep (se 1 (by rfl) ⟨419255, by rfl⟩ : syracuseStep 559007 = 838511) B838511
theorem B199783 : Blo 195805 199783 := bstep (se 1 (by rfl) ⟨149837, by rfl⟩ : syracuseStep 199783 = 299675) B299675
theorem B197759717 : Blo 195805 197759717 := bstep (se 4 (by rfl) ⟨18539973, by rfl⟩ : syracuseStep 197759717 = 37079947) B37079947
theorem B16586003 : Blo 195805 16586003 := bstep (se 1 (by rfl) ⟨12439502, by rfl⟩ : syracuseStep 16586003 = 24879005) B24879005
theorem B1677671 : Blo 195805 1677671 := bstep (se 1 (by rfl) ⟨1258253, by rfl⟩ : syracuseStep 1677671 = 2516507) B2516507
theorem B728783 : Blo 195805 728783 := bstep (se 1 (by rfl) ⟨546587, by rfl⟩ : syracuseStep 728783 = 1093175) B1093175
theorem B995489 : Blo 195805 995489 := bstep (se 2 (by rfl) ⟨373308, by rfl⟩ : syracuseStep 995489 = 746617) B746617
theorem B505399 : Blo 195805 505399 := bstep (se 1 (by rfl) ⟨379049, by rfl⟩ : syracuseStep 505399 = 758099) B758099
theorem B80299781 : Blo 195805 80299781 := bstep (se 4 (by rfl) ⟨7528104, by rfl⟩ : syracuseStep 80299781 = 15056209) B15056209
theorem B280631 : Blo 195805 280631 := bstep (se 1 (by rfl) ⟨210473, by rfl⟩ : syracuseStep 280631 = 420947) B420947
theorem B445931 : Blo 195805 445931 := bstep (se 1 (by rfl) ⟨334448, by rfl⟩ : syracuseStep 445931 = 668897) B668897
theorem B316415 : Blo 195805 316415 := bstep (se 1 (by rfl) ⟨237311, by rfl⟩ : syracuseStep 316415 = 474623) B474623
theorem B841175 : Blo 195805 841175 := bstep (se 1 (by rfl) ⟨630881, by rfl⟩ : syracuseStep 841175 = 1261763) B1261763
theorem B4773629 : Blo 195805 4773629 := bstep (se 3 (by rfl) ⟨895055, by rfl⟩ : syracuseStep 4773629 = 1790111) B1790111
theorem B70540433 : Blo 195805 70540433 := bstep (se 2 (by rfl) ⟨26452662, by rfl⟩ : syracuseStep 70540433 = 52905325) B52905325
theorem B1073263 : Blo 195805 1073263 := bstep (se 1 (by rfl) ⟨804947, by rfl⟩ : syracuseStep 1073263 = 1609895) B1609895
theorem B221467 : Blo 195805 221467 := bstep (se 1 (by rfl) ⟨166100, by rfl⟩ : syracuseStep 221467 = 332201) B332201
theorem B749321 : Blo 195805 749321 := bstep (se 2 (by rfl) ⟨280995, by rfl⟩ : syracuseStep 749321 = 561991) B561991
theorem B422057 : Blo 195805 422057 := bstep (se 2 (by rfl) ⟨158271, by rfl⟩ : syracuseStep 422057 = 316543) B316543
theorem B1341053 : Blo 195805 1341053 := bstep (se 3 (by rfl) ⟨251447, by rfl⟩ : syracuseStep 1341053 = 502895) B502895
theorem B751295 : Blo 195805 751295 := bstep (se 1 (by rfl) ⟨563471, by rfl⟩ : syracuseStep 751295 = 1126943) B1126943
theorem B196335 : Blo 195805 196335 := bstep (se 1 (by rfl) ⟨147251, by rfl⟩ : syracuseStep 196335 = 294503) B294503
theorem B196455 : Blo 195805 196455 := bstep (se 1 (by rfl) ⟨147341, by rfl⟩ : syracuseStep 196455 = 294683) B294683
theorem B2555873 : Blo 195805 2555873 := bstep (se 2 (by rfl) ⟨958452, by rfl⟩ : syracuseStep 2555873 = 1916905) B1916905
theorem B295289 : Blo 195805 295289 := bstep (se 2 (by rfl) ⟨110733, by rfl⟩ : syracuseStep 295289 = 221467) B221467
theorem B197663 : Blo 195805 197663 := bstep (se 1 (by rfl) ⟨148247, by rfl⟩ : syracuseStep 197663 = 296495) B296495
theorem B297287 : Blo 195805 297287 := bstep (se 1 (by rfl) ⟨222965, by rfl⟩ : syracuseStep 297287 = 445931) B445931
theorem B560783 : Blo 195805 560783 := bstep (se 1 (by rfl) ⟨420587, by rfl⟩ : syracuseStep 560783 = 841175) B841175
theorem B3182419 : Blo 195805 3182419 := bstep (se 1 (by rfl) ⟨2386814, by rfl⟩ : syracuseStep 3182419 = 4773629) B4773629
theorem B1118447 : Blo 195805 1118447 := bstep (se 1 (by rfl) ⟨838835, by rfl⟩ : syracuseStep 1118447 = 1677671) B1677671
theorem B47026955 : Blo 195805 47026955 := bstep (se 1 (by rfl) ⟨35270216, by rfl⟩ : syracuseStep 47026955 = 70540433) B70540433
theorem B499547 : Blo 195805 499547 := bstep (se 1 (by rfl) ⟨374660, by rfl⟩ : syracuseStep 499547 = 749321) B749321
theorem B663659 : Blo 195805 663659 := bstep (se 1 (by rfl) ⟨497744, by rfl⟩ : syracuseStep 663659 = 995489) B995489
theorem B894035 : Blo 195805 894035 := bstep (se 1 (by rfl) ⟨670526, by rfl⟩ : syracuseStep 894035 = 1341053) B1341053
theorem B500863 : Blo 195805 500863 := bstep (se 1 (by rfl) ⟨375647, by rfl⟩ : syracuseStep 500863 = 751295) B751295
theorem B1125485 : Blo 195805 1125485 := bstep (se 3 (by rfl) ⟨211028, by rfl⟩ : syracuseStep 1125485 = 422057) B422057
theorem B372671 : Blo 195805 372671 := bstep (se 1 (by rfl) ⟨279503, by rfl⟩ : syracuseStep 372671 = 559007) B559007
theorem B131839811 : Blo 195805 131839811 := bstep (se 1 (by rfl) ⟨98879858, by rfl⟩ : syracuseStep 131839811 = 197759717) B197759717
theorem B210943 : Blo 195805 210943 := bstep (se 1 (by rfl) ⟨158207, by rfl⟩ : syracuseStep 210943 = 316415) B316415
theorem B673865 : Blo 195805 673865 := bstep (se 2 (by rfl) ⟨252699, by rfl⟩ : syracuseStep 673865 = 505399) B505399
theorem B1431017 : Blo 195805 1431017 := bstep (se 2 (by rfl) ⟨536631, by rfl⟩ : syracuseStep 1431017 = 1073263) B1073263
theorem B53533187 : Blo 195805 53533187 := bstep (se 1 (by rfl) ⟨40149890, by rfl⟩ : syracuseStep 53533187 = 80299781) B80299781
theorem B44229341 : Blo 195805 44229341 := bstep (se 3 (by rfl) ⟨8293001, by rfl⟩ : syracuseStep 44229341 = 16586003) B16586003
theorem B485855 : Blo 195805 485855 := bstep (se 1 (by rfl) ⟨364391, by rfl⟩ : syracuseStep 485855 = 728783) B728783
theorem B748349 : Blo 195805 748349 := bstep (se 3 (by rfl) ⟨140315, by rfl⟩ : syracuseStep 748349 = 280631) B280631
theorem B1703915 : Blo 195805 1703915 := bstep (se 1 (by rfl) ⟨1277936, by rfl⟩ : syracuseStep 1703915 = 2555873) B2555873
theorem B196859 : Blo 195805 196859 := bstep (se 1 (by rfl) ⟨147644, by rfl⟩ : syracuseStep 196859 = 295289) B295289
theorem B198191 : Blo 195805 198191 := bstep (se 1 (by rfl) ⟨148643, by rfl⟩ : syracuseStep 198191 = 297287) B297287
theorem B954011 : Blo 195805 954011 := bstep (se 1 (by rfl) ⟨715508, by rfl⟩ : syracuseStep 954011 = 1431017) B1431017
theorem B35688791 : Blo 195805 35688791 := bstep (se 1 (by rfl) ⟨26766593, by rfl⟩ : syracuseStep 35688791 = 53533187) B53533187
theorem B333031 : Blo 195805 333031 := bstep (se 1 (by rfl) ⟨249773, by rfl⟩ : syracuseStep 333031 = 499547) B499547
theorem B498899 : Blo 195805 498899 := bstep (se 1 (by rfl) ⟨374174, by rfl⟩ : syracuseStep 498899 = 748349) B748349
theorem B87893207 : Blo 195805 87893207 := bstep (se 1 (by rfl) ⟨65919905, by rfl⟩ : syracuseStep 87893207 = 131839811) B131839811
theorem B1125029 : Blo 195805 1125029 := bstep (se 4 (by rfl) ⟨105471, by rfl⟩ : syracuseStep 1125029 = 210943) B210943
theorem B667817 : Blo 195805 667817 := bstep (se 2 (by rfl) ⟨250431, by rfl⟩ : syracuseStep 667817 = 500863) B500863
theorem B4243225 : Blo 195805 4243225 := bstep (se 2 (by rfl) ⟨1591209, by rfl⟩ : syracuseStep 4243225 = 3182419) B3182419
theorem B442439 : Blo 195805 442439 := bstep (se 1 (by rfl) ⟨331829, by rfl⟩ : syracuseStep 442439 = 663659) B663659
theorem B248447 : Blo 195805 248447 := bstep (se 1 (by rfl) ⟨186335, by rfl⟩ : syracuseStep 248447 = 372671) B372671
theorem B1495421 : Blo 195805 1495421 := bstep (se 3 (by rfl) ⟨280391, by rfl⟩ : syracuseStep 1495421 = 560783) B560783
theorem B1135943 : Blo 195805 1135943 := bstep (se 1 (by rfl) ⟨851957, by rfl⟩ : syracuseStep 1135943 = 1703915) B1703915
theorem B449243 : Blo 195805 449243 := bstep (se 1 (by rfl) ⟨336932, by rfl⟩ : syracuseStep 449243 = 673865) B673865
theorem B745631 : Blo 195805 745631 := bstep (se 1 (by rfl) ⟨559223, by rfl⟩ : syracuseStep 745631 = 1118447) B1118447
theorem B2384093 : Blo 195805 2384093 := bstep (se 3 (by rfl) ⟨447017, by rfl⟩ : syracuseStep 2384093 = 894035) B894035
theorem B31351303 : Blo 195805 31351303 := bstep (se 1 (by rfl) ⟨23513477, by rfl⟩ : syracuseStep 31351303 = 47026955) B47026955
theorem B29486227 : Blo 195805 29486227 := bstep (se 1 (by rfl) ⟨22114670, by rfl⟩ : syracuseStep 29486227 = 44229341) B44229341
theorem B323903 : Blo 195805 323903 := bstep (se 1 (by rfl) ⟨242927, by rfl⟩ : syracuseStep 323903 = 485855) B485855
theorem B750323 : Blo 195805 750323 := bstep (se 1 (by rfl) ⟨562742, by rfl⟩ : syracuseStep 750323 = 1125485) B1125485
theorem B294959 : Blo 195805 294959 := bstep (se 1 (by rfl) ⟨221219, by rfl⟩ : syracuseStep 294959 = 442439) B442439
theorem B23792527 : Blo 195805 23792527 := bstep (se 1 (by rfl) ⟨17844395, by rfl⟩ : syracuseStep 23792527 = 35688791) B35688791
theorem B757295 : Blo 195805 757295 := bstep (se 1 (by rfl) ⟨567971, by rfl⟩ : syracuseStep 757295 = 1135943) B1135943
theorem B299495 : Blo 195805 299495 := bstep (se 1 (by rfl) ⟨224621, by rfl⟩ : syracuseStep 299495 = 449243) B449243
theorem B332599 : Blo 195805 332599 := bstep (se 1 (by rfl) ⟨249449, by rfl⟩ : syracuseStep 332599 = 498899) B498899
theorem B497087 : Blo 195805 497087 := bstep (se 1 (by rfl) ⟨372815, by rfl⟩ : syracuseStep 497087 = 745631) B745631
theorem B58595471 : Blo 195805 58595471 := bstep (se 1 (by rfl) ⟨43946603, by rfl⟩ : syracuseStep 58595471 = 87893207) B87893207
theorem B662525 : Blo 195805 662525 := bstep (se 3 (by rfl) ⟨124223, by rfl⟩ : syracuseStep 662525 = 248447) B248447
theorem B500215 : Blo 195805 500215 := bstep (se 1 (by rfl) ⟨375161, by rfl⟩ : syracuseStep 500215 = 750323) B750323
theorem B636007 : Blo 195805 636007 := bstep (se 1 (by rfl) ⟨477005, by rfl⟩ : syracuseStep 636007 = 954011) B954011
theorem B996947 : Blo 195805 996947 := bstep (se 1 (by rfl) ⟨747710, by rfl⟩ : syracuseStep 996947 = 1495421) B1495421
theorem B1589395 : Blo 195805 1589395 := bstep (se 1 (by rfl) ⟨1192046, by rfl⟩ : syracuseStep 1589395 = 2384093) B2384093
theorem B444041 : Blo 195805 444041 := bstep (se 2 (by rfl) ⟨166515, by rfl⟩ : syracuseStep 444041 = 333031) B333031
theorem B445211 : Blo 195805 445211 := bstep (se 1 (by rfl) ⟨333908, by rfl⟩ : syracuseStep 445211 = 667817) B667817
theorem B215935 : Blo 195805 215935 := bstep (se 1 (by rfl) ⟨161951, by rfl⟩ : syracuseStep 215935 = 323903) B323903
theorem B5657633 : Blo 195805 5657633 := bstep (se 2 (by rfl) ⟨2121612, by rfl⟩ : syracuseStep 5657633 = 4243225) B4243225
theorem B167206949 : Blo 195805 167206949 := bstep (se 4 (by rfl) ⟨15675651, by rfl⟩ : syracuseStep 167206949 = 31351303) B31351303
theorem B39314969 : Blo 195805 39314969 := bstep (se 2 (by rfl) ⟨14743113, by rfl⟩ : syracuseStep 39314969 = 29486227) B29486227
theorem B750019 : Blo 195805 750019 := bstep (se 1 (by rfl) ⟨562514, by rfl⟩ : syracuseStep 750019 = 1125029) B1125029
theorem B196639 : Blo 195805 196639 := bstep (se 1 (by rfl) ⟨147479, by rfl⟩ : syracuseStep 196639 = 294959) B294959
theorem B296027 : Blo 195805 296027 := bstep (se 1 (by rfl) ⟨222020, by rfl⟩ : syracuseStep 296027 = 444041) B444041
theorem B296807 : Blo 195805 296807 := bstep (se 1 (by rfl) ⟨222605, by rfl⟩ : syracuseStep 296807 = 445211) B445211
theorem B199663 : Blo 195805 199663 := bstep (se 1 (by rfl) ⟨149747, by rfl⟩ : syracuseStep 199663 = 299495) B299495
theorem B3771755 : Blo 195805 3771755 := bstep (se 1 (by rfl) ⟨2828816, by rfl⟩ : syracuseStep 3771755 = 5657633) B5657633
theorem B331391 : Blo 195805 331391 := bstep (se 1 (by rfl) ⟨248543, by rfl⟩ : syracuseStep 331391 = 497087) B497087
theorem B31723369 : Blo 195805 31723369 := bstep (se 2 (by rfl) ⟨11896263, by rfl⟩ : syracuseStep 31723369 = 23792527) B23792527
theorem B39063647 : Blo 195805 39063647 := bstep (se 1 (by rfl) ⟨29297735, by rfl⟩ : syracuseStep 39063647 = 58595471) B58595471
theorem B1151653 : Blo 195805 1151653 := bstep (se 4 (by rfl) ⟨107967, by rfl⟩ : syracuseStep 1151653 = 215935) B215935
theorem B664631 : Blo 195805 664631 := bstep (se 1 (by rfl) ⟨498473, by rfl⟩ : syracuseStep 664631 = 996947) B996947
theorem B666953 : Blo 195805 666953 := bstep (se 2 (by rfl) ⟨250107, by rfl⟩ : syracuseStep 666953 = 500215) B500215
theorem B504863 : Blo 195805 504863 := bstep (se 1 (by rfl) ⟨378647, by rfl⟩ : syracuseStep 504863 = 757295) B757295
theorem B441683 : Blo 195805 441683 := bstep (se 1 (by rfl) ⟨331262, by rfl⟩ : syracuseStep 441683 = 662525) B662525
theorem B1000025 : Blo 195805 1000025 := bstep (se 2 (by rfl) ⟨375009, by rfl⟩ : syracuseStep 1000025 = 750019) B750019
theorem B443465 : Blo 195805 443465 := bstep (se 2 (by rfl) ⟨166299, by rfl⟩ : syracuseStep 443465 = 332599) B332599
theorem B2119193 : Blo 195805 2119193 := bstep (se 2 (by rfl) ⟨794697, by rfl⟩ : syracuseStep 2119193 = 1589395) B1589395
theorem B111471299 : Blo 195805 111471299 := bstep (se 1 (by rfl) ⟨83603474, by rfl⟩ : syracuseStep 111471299 = 167206949) B167206949
theorem B26209979 : Blo 195805 26209979 := bstep (se 1 (by rfl) ⟨19657484, by rfl⟩ : syracuseStep 26209979 = 39314969) B39314969
theorem B848009 : Blo 195805 848009 := bstep (se 2 (by rfl) ⟨318003, by rfl⟩ : syracuseStep 848009 = 636007) B636007
theorem B2261357 : Blo 195805 2261357 := bstep (se 3 (by rfl) ⟨424004, by rfl⟩ : syracuseStep 2261357 = 848009) B848009
theorem B295643 : Blo 195805 295643 := bstep (se 1 (by rfl) ⟨221732, by rfl⟩ : syracuseStep 295643 = 443465) B443465
theorem B197351 : Blo 195805 197351 := bstep (se 1 (by rfl) ⟨148013, by rfl⟩ : syracuseStep 197351 = 296027) B296027
theorem B197871 : Blo 195805 197871 := bstep (se 1 (by rfl) ⟨148403, by rfl⟩ : syracuseStep 197871 = 296807) B296807
theorem B1412795 : Blo 195805 1412795 := bstep (se 1 (by rfl) ⟨1059596, by rfl⟩ : syracuseStep 1412795 = 2119193) B2119193
theorem B676765205 : Blo 195805 676765205 := bstep (se 6 (by rfl) ⟨15861684, by rfl⟩ : syracuseStep 676765205 = 31723369) B31723369
theorem B17473319 : Blo 195805 17473319 := bstep (se 1 (by rfl) ⟨13104989, by rfl⟩ : syracuseStep 17473319 = 26209979) B26209979
theorem B336575 : Blo 195805 336575 := bstep (se 1 (by rfl) ⟨252431, by rfl⟩ : syracuseStep 336575 = 504863) B504863
theorem B666683 : Blo 195805 666683 := bstep (se 1 (by rfl) ⟨500012, by rfl⟩ : syracuseStep 666683 = 1000025) B1000025
theorem B443087 : Blo 195805 443087 := bstep (se 1 (by rfl) ⟨332315, by rfl⟩ : syracuseStep 443087 = 664631) B664631
theorem B444635 : Blo 195805 444635 := bstep (se 1 (by rfl) ⟨333476, by rfl⟩ : syracuseStep 444635 = 666953) B666953
theorem B2514503 : Blo 195805 2514503 := bstep (se 1 (by rfl) ⟨1885877, by rfl⟩ : syracuseStep 2514503 = 3771755) B3771755
theorem B220927 : Blo 195805 220927 := bstep (se 1 (by rfl) ⟨165695, by rfl⟩ : syracuseStep 220927 = 331391) B331391
theorem B26042431 : Blo 195805 26042431 := bstep (se 1 (by rfl) ⟨19531823, by rfl⟩ : syracuseStep 26042431 = 39063647) B39063647
theorem B1535537 : Blo 195805 1535537 := bstep (se 2 (by rfl) ⟨575826, by rfl⟩ : syracuseStep 1535537 = 1151653) B1151653
theorem B74314199 : Blo 195805 74314199 := bstep (se 1 (by rfl) ⟨55735649, by rfl⟩ : syracuseStep 74314199 = 111471299) B111471299
theorem B294455 : Blo 195805 294455 := bstep (se 1 (by rfl) ⟨220841, by rfl⟩ : syracuseStep 294455 = 441683) B441683
theorem B1507571 : Blo 195805 1507571 := bstep (se 1 (by rfl) ⟨1130678, by rfl⟩ : syracuseStep 1507571 = 2261357) B2261357
theorem B295391 : Blo 195805 295391 := bstep (se 1 (by rfl) ⟨221543, by rfl⟩ : syracuseStep 295391 = 443087) B443087
theorem B197095 : Blo 195805 197095 := bstep (se 1 (by rfl) ⟨147821, by rfl⟩ : syracuseStep 197095 = 295643) B295643
theorem B296423 : Blo 195805 296423 := bstep (se 1 (by rfl) ⟨222317, by rfl⟩ : syracuseStep 296423 = 444635) B444635
theorem B1676335 : Blo 195805 1676335 := bstep (se 1 (by rfl) ⟨1257251, by rfl⟩ : syracuseStep 1676335 = 2514503) B2514503
theorem B1023691 : Blo 195805 1023691 := bstep (se 1 (by rfl) ⟨767768, by rfl⟩ : syracuseStep 1023691 = 1535537) B1535537
theorem B11648879 : Blo 195805 11648879 := bstep (se 1 (by rfl) ⟨8736659, by rfl⟩ : syracuseStep 11648879 = 17473319) B17473319
theorem B444455 : Blo 195805 444455 := bstep (se 1 (by rfl) ⟨333341, by rfl⟩ : syracuseStep 444455 = 666683) B666683
theorem B34723241 : Blo 195805 34723241 := bstep (se 2 (by rfl) ⟨13021215, by rfl⟩ : syracuseStep 34723241 = 26042431) B26042431
theorem B941863 : Blo 195805 941863 := bstep (se 1 (by rfl) ⟨706397, by rfl⟩ : syracuseStep 941863 = 1412795) B1412795
theorem B451176803 : Blo 195805 451176803 := bstep (se 1 (by rfl) ⟨338382602, by rfl⟩ : syracuseStep 451176803 = 676765205) B676765205
theorem B224383 : Blo 195805 224383 := bstep (se 1 (by rfl) ⟨168287, by rfl⟩ : syracuseStep 224383 = 336575) B336575
theorem B49542799 : Blo 195805 49542799 := bstep (se 1 (by rfl) ⟨37157099, by rfl⟩ : syracuseStep 49542799 = 74314199) B74314199
theorem B294569 : Blo 195805 294569 := bstep (se 2 (by rfl) ⟨110463, by rfl⟩ : syracuseStep 294569 = 220927) B220927
theorem B196303 : Blo 195805 196303 := bstep (se 1 (by rfl) ⟨147227, by rfl⟩ : syracuseStep 196303 = 294455) B294455
theorem B196927 : Blo 195805 196927 := bstep (se 1 (by rfl) ⟨147695, by rfl⟩ : syracuseStep 196927 = 295391) B295391
theorem B197615 : Blo 195805 197615 := bstep (se 1 (by rfl) ⟨148211, by rfl⟩ : syracuseStep 197615 = 296423) B296423
theorem B296303 : Blo 195805 296303 := bstep (se 1 (by rfl) ⟨222227, by rfl⟩ : syracuseStep 296303 = 444455) B444455
theorem B299177 : Blo 195805 299177 := bstep (se 2 (by rfl) ⟨112191, by rfl⟩ : syracuseStep 299177 = 224383) B224383
theorem B2235113 : Blo 195805 2235113 := bstep (se 2 (by rfl) ⟨838167, by rfl⟩ : syracuseStep 2235113 = 1676335) B1676335
theorem B300784535 : Blo 195805 300784535 := bstep (se 1 (by rfl) ⟨225588401, by rfl⟩ : syracuseStep 300784535 = 451176803) B451176803
theorem B1255817 : Blo 195805 1255817 := bstep (se 2 (by rfl) ⟨470931, by rfl⟩ : syracuseStep 1255817 = 941863) B941863
theorem B23148827 : Blo 195805 23148827 := bstep (se 1 (by rfl) ⟨17361620, by rfl⟩ : syracuseStep 23148827 = 34723241) B34723241
theorem B1364921 : Blo 195805 1364921 := bstep (se 2 (by rfl) ⟨511845, by rfl⟩ : syracuseStep 1364921 = 1023691) B1023691
theorem B1005047 : Blo 195805 1005047 := bstep (se 1 (by rfl) ⟨753785, by rfl⟩ : syracuseStep 1005047 = 1507571) B1507571
theorem B66057065 : Blo 195805 66057065 := bstep (se 2 (by rfl) ⟨24771399, by rfl⟩ : syracuseStep 66057065 = 49542799) B49542799
theorem B196379 : Blo 195805 196379 := bstep (se 1 (by rfl) ⟨147284, by rfl⟩ : syracuseStep 196379 = 294569) B294569
theorem B7765919 : Blo 195805 7765919 := bstep (se 1 (by rfl) ⟨5824439, by rfl⟩ : syracuseStep 7765919 = 11648879) B11648879
theorem B197535 : Blo 195805 197535 := bstep (se 1 (by rfl) ⟨148151, by rfl⟩ : syracuseStep 197535 = 296303) B296303
theorem B199451 : Blo 195805 199451 := bstep (se 1 (by rfl) ⟨149588, by rfl⟩ : syracuseStep 199451 = 299177) B299177
theorem B670031 : Blo 195805 670031 := bstep (se 1 (by rfl) ⟨502523, by rfl⟩ : syracuseStep 670031 = 1005047) B1005047
theorem B1490075 : Blo 195805 1490075 := bstep (se 1 (by rfl) ⟨1117556, by rfl⟩ : syracuseStep 1490075 = 2235113) B2235113
theorem B200523023 : Blo 195805 200523023 := bstep (se 1 (by rfl) ⟨150392267, by rfl⟩ : syracuseStep 200523023 = 300784535) B300784535
theorem B837211 : Blo 195805 837211 := bstep (se 1 (by rfl) ⟨627908, by rfl⟩ : syracuseStep 837211 = 1255817) B1255817
theorem B909947 : Blo 195805 909947 := bstep (se 1 (by rfl) ⟨682460, by rfl⟩ : syracuseStep 909947 = 1364921) B1364921
theorem B44038043 : Blo 195805 44038043 := bstep (se 1 (by rfl) ⟨33028532, by rfl⟩ : syracuseStep 44038043 = 66057065) B66057065
theorem B15432551 : Blo 195805 15432551 := bstep (se 1 (by rfl) ⟨11574413, by rfl⟩ : syracuseStep 15432551 = 23148827) B23148827
theorem B5177279 : Blo 195805 5177279 := bstep (se 1 (by rfl) ⟨3882959, by rfl⟩ : syracuseStep 5177279 = 7765919) B7765919
theorem B1116281 : Blo 195805 1116281 := bstep (se 2 (by rfl) ⟨418605, by rfl⟩ : syracuseStep 1116281 = 837211) B837211
theorem B993383 : Blo 195805 993383 := bstep (se 1 (by rfl) ⟨745037, by rfl⟩ : syracuseStep 993383 = 1490075) B1490075
theorem B13806077 : Blo 195805 13806077 := bstep (se 3 (by rfl) ⟨2588639, by rfl⟩ : syracuseStep 13806077 = 5177279) B5177279
theorem B606631 : Blo 195805 606631 := bstep (se 1 (by rfl) ⟨454973, by rfl⟩ : syracuseStep 606631 = 909947) B909947
theorem B446687 : Blo 195805 446687 := bstep (se 1 (by rfl) ⟨335015, by rfl⟩ : syracuseStep 446687 = 670031) B670031
theorem B133682015 : Blo 195805 133682015 := bstep (se 1 (by rfl) ⟨100261511, by rfl⟩ : syracuseStep 133682015 = 200523023) B200523023
theorem B29358695 : Blo 195805 29358695 := bstep (se 1 (by rfl) ⟨22019021, by rfl⟩ : syracuseStep 29358695 = 44038043) B44038043
theorem B10288367 : Blo 195805 10288367 := bstep (se 1 (by rfl) ⟨7716275, by rfl⟩ : syracuseStep 10288367 = 15432551) B15432551
theorem B297791 : Blo 195805 297791 := bstep (se 1 (by rfl) ⟨223343, by rfl⟩ : syracuseStep 297791 = 446687) B446687
theorem B662255 : Blo 195805 662255 := bstep (se 1 (by rfl) ⟨496691, by rfl⟩ : syracuseStep 662255 = 993383) B993383
theorem B19572463 : Blo 195805 19572463 := bstep (se 1 (by rfl) ⟨14679347, by rfl⟩ : syracuseStep 19572463 = 29358695) B29358695
theorem B6858911 : Blo 195805 6858911 := bstep (se 1 (by rfl) ⟨5144183, by rfl⟩ : syracuseStep 6858911 = 10288367) B10288367
theorem B36816205 : Blo 195805 36816205 := bstep (se 3 (by rfl) ⟨6903038, by rfl⟩ : syracuseStep 36816205 = 13806077) B13806077
theorem B808841 : Blo 195805 808841 := bstep (se 2 (by rfl) ⟨303315, by rfl⟩ : syracuseStep 808841 = 606631) B606631
theorem B744187 : Blo 195805 744187 := bstep (se 1 (by rfl) ⟨558140, by rfl⟩ : syracuseStep 744187 = 1116281) B1116281
theorem B89121343 : Blo 195805 89121343 := bstep (se 1 (by rfl) ⟨66841007, by rfl⟩ : syracuseStep 89121343 = 133682015) B133682015
theorem B49088273 : Blo 195805 49088273 := bstep (se 2 (by rfl) ⟨18408102, by rfl⟩ : syracuseStep 49088273 = 36816205) B36816205
theorem B198527 : Blo 195805 198527 := bstep (se 1 (by rfl) ⟨148895, by rfl⟩ : syracuseStep 198527 = 297791) B297791
theorem B992249 : Blo 195805 992249 := bstep (se 2 (by rfl) ⟨372093, by rfl⟩ : syracuseStep 992249 = 744187) B744187
theorem B118828457 : Blo 195805 118828457 := bstep (se 2 (by rfl) ⟨44560671, by rfl⟩ : syracuseStep 118828457 = 89121343) B89121343
theorem B26096617 : Blo 195805 26096617 := bstep (se 2 (by rfl) ⟨9786231, by rfl⟩ : syracuseStep 26096617 = 19572463) B19572463
theorem B539227 : Blo 195805 539227 := bstep (se 1 (by rfl) ⟨404420, by rfl⟩ : syracuseStep 539227 = 808841) B808841
theorem B441503 : Blo 195805 441503 := bstep (se 1 (by rfl) ⟨331127, by rfl⟩ : syracuseStep 441503 = 662255) B662255
theorem B4572607 : Blo 195805 4572607 := bstep (se 1 (by rfl) ⟨3429455, by rfl⟩ : syracuseStep 4572607 = 6858911) B6858911
theorem B6096809 : Blo 195805 6096809 := bstep (se 2 (by rfl) ⟨2286303, by rfl⟩ : syracuseStep 6096809 = 4572607) B4572607
theorem B661499 : Blo 195805 661499 := bstep (se 1 (by rfl) ⟨496124, by rfl⟩ : syracuseStep 661499 = 992249) B992249
theorem B523608245 : Blo 195805 523608245 := bstep (se 5 (by rfl) ⟨24544136, by rfl⟩ : syracuseStep 523608245 = 49088273) B49088273
theorem B79218971 : Blo 195805 79218971 := bstep (se 1 (by rfl) ⟨59414228, by rfl⟩ : syracuseStep 79218971 = 118828457) B118828457
theorem B34795489 : Blo 195805 34795489 := bstep (se 2 (by rfl) ⟨13048308, by rfl⟩ : syracuseStep 34795489 = 26096617) B26096617
theorem B718969 : Blo 195805 718969 := bstep (se 2 (by rfl) ⟨269613, by rfl⟩ : syracuseStep 718969 = 539227) B539227
theorem B294335 : Blo 195805 294335 := bstep (se 1 (by rfl) ⟨220751, by rfl⟩ : syracuseStep 294335 = 441503) B441503
theorem B16258157 : Blo 195805 16258157 := bstep (se 3 (by rfl) ⟨3048404, by rfl⟩ : syracuseStep 16258157 = 6096809) B6096809
theorem B958625 : Blo 195805 958625 := bstep (se 2 (by rfl) ⟨359484, by rfl⟩ : syracuseStep 958625 = 718969) B718969
theorem B440999 : Blo 195805 440999 := bstep (se 1 (by rfl) ⟨330749, by rfl⟩ : syracuseStep 440999 = 661499) B661499
theorem B52812647 : Blo 195805 52812647 := bstep (se 1 (by rfl) ⟨39609485, by rfl⟩ : syracuseStep 52812647 = 79218971) B79218971
theorem B46393985 : Blo 195805 46393985 := bstep (se 2 (by rfl) ⟨17397744, by rfl⟩ : syracuseStep 46393985 = 34795489) B34795489
theorem B349072163 : Blo 195805 349072163 := bstep (se 1 (by rfl) ⟨261804122, by rfl⟩ : syracuseStep 349072163 = 523608245) B523608245
theorem B196223 : Blo 195805 196223 := bstep (se 1 (by rfl) ⟨147167, by rfl⟩ : syracuseStep 196223 = 294335) B294335
theorem B35208431 : Blo 195805 35208431 := bstep (se 1 (by rfl) ⟨26406323, by rfl⟩ : syracuseStep 35208431 = 52812647) B52812647
theorem B639083 : Blo 195805 639083 := bstep (se 1 (by rfl) ⟨479312, by rfl⟩ : syracuseStep 639083 = 958625) B958625
theorem B123717293 : Blo 195805 123717293 := bstep (se 3 (by rfl) ⟨23196992, by rfl⟩ : syracuseStep 123717293 = 46393985) B46393985
theorem B10838771 : Blo 195805 10838771 := bstep (se 1 (by rfl) ⟨8129078, by rfl⟩ : syracuseStep 10838771 = 16258157) B16258157
theorem B232714775 : Blo 195805 232714775 := bstep (se 1 (by rfl) ⟨174536081, by rfl⟩ : syracuseStep 232714775 = 349072163) B349072163
theorem B293999 : Blo 195805 293999 := bstep (se 1 (by rfl) ⟨220499, by rfl⟩ : syracuseStep 293999 = 440999) B440999
theorem B426055 : Blo 195805 426055 := bstep (se 1 (by rfl) ⟨319541, by rfl⟩ : syracuseStep 426055 = 639083) B639083
theorem B82478195 : Blo 195805 82478195 := bstep (se 1 (by rfl) ⟨61858646, by rfl⟩ : syracuseStep 82478195 = 123717293) B123717293
theorem B23472287 : Blo 195805 23472287 := bstep (se 1 (by rfl) ⟨17604215, by rfl⟩ : syracuseStep 23472287 = 35208431) B35208431
theorem B7225847 : Blo 195805 7225847 := bstep (se 1 (by rfl) ⟨5419385, by rfl⟩ : syracuseStep 7225847 = 10838771) B10838771
theorem B155143183 : Blo 195805 155143183 := bstep (se 1 (by rfl) ⟨116357387, by rfl⟩ : syracuseStep 155143183 = 232714775) B232714775
theorem B195999 : Blo 195805 195999 := bstep (se 1 (by rfl) ⟨146999, by rfl⟩ : syracuseStep 195999 = 293999) B293999
theorem B4817231 : Blo 195805 4817231 := bstep (se 1 (by rfl) ⟨3612923, by rfl⟩ : syracuseStep 4817231 = 7225847) B7225847
theorem B54985463 : Blo 195805 54985463 := bstep (se 1 (by rfl) ⟨41239097, by rfl⟩ : syracuseStep 54985463 = 82478195) B82478195
theorem B568073 : Blo 195805 568073 := bstep (se 2 (by rfl) ⟨213027, by rfl⟩ : syracuseStep 568073 = 426055) B426055
theorem B15648191 : Blo 195805 15648191 := bstep (se 1 (by rfl) ⟨11736143, by rfl⟩ : syracuseStep 15648191 = 23472287) B23472287
theorem B206857577 : Blo 195805 206857577 := bstep (se 2 (by rfl) ⟨77571591, by rfl⟩ : syracuseStep 206857577 = 155143183) B155143183
theorem B3211487 : Blo 195805 3211487 := bstep (se 1 (by rfl) ⟨2408615, by rfl⟩ : syracuseStep 3211487 = 4817231) B4817231
theorem B1514861 : Blo 195805 1514861 := bstep (se 3 (by rfl) ⟨284036, by rfl⟩ : syracuseStep 1514861 = 568073) B568073
theorem B10432127 : Blo 195805 10432127 := bstep (se 1 (by rfl) ⟨7824095, by rfl⟩ : syracuseStep 10432127 = 15648191) B15648191
theorem B137905051 : Blo 195805 137905051 := bstep (se 1 (by rfl) ⟨103428788, by rfl⟩ : syracuseStep 137905051 = 206857577) B206857577
theorem B36656975 : Blo 195805 36656975 := bstep (se 1 (by rfl) ⟨27492731, by rfl⟩ : syracuseStep 36656975 = 54985463) B54985463
theorem B6954751 : Blo 195805 6954751 := bstep (se 1 (by rfl) ⟨5216063, by rfl⟩ : syracuseStep 6954751 = 10432127) B10432127
theorem B2140991 : Blo 195805 2140991 := bstep (se 1 (by rfl) ⟨1605743, by rfl⟩ : syracuseStep 2140991 = 3211487) B3211487
theorem B183873401 : Blo 195805 183873401 := bstep (se 2 (by rfl) ⟨68952525, by rfl⟩ : syracuseStep 183873401 = 137905051) B137905051
theorem B24437983 : Blo 195805 24437983 := bstep (se 1 (by rfl) ⟨18328487, by rfl⟩ : syracuseStep 24437983 = 36656975) B36656975
theorem B1009907 : Blo 195805 1009907 := bstep (se 1 (by rfl) ⟨757430, by rfl⟩ : syracuseStep 1009907 = 1514861) B1514861
theorem B32583977 : Blo 195805 32583977 := bstep (se 2 (by rfl) ⟨12218991, by rfl⟩ : syracuseStep 32583977 = 24437983) B24437983
theorem B673271 : Blo 195805 673271 := bstep (se 1 (by rfl) ⟨504953, by rfl⟩ : syracuseStep 673271 = 1009907) B1009907
theorem B1427327 : Blo 195805 1427327 := bstep (se 1 (by rfl) ⟨1070495, by rfl⟩ : syracuseStep 1427327 = 2140991) B2140991
theorem B122582267 : Blo 195805 122582267 := bstep (se 1 (by rfl) ⟨91936700, by rfl⟩ : syracuseStep 122582267 = 183873401) B183873401
theorem B9273001 : Blo 195805 9273001 := bstep (se 2 (by rfl) ⟨3477375, by rfl⟩ : syracuseStep 9273001 = 6954751) B6954751
theorem B951551 : Blo 195805 951551 := bstep (se 1 (by rfl) ⟨713663, by rfl⟩ : syracuseStep 951551 = 1427327) B1427327
theorem B12364001 : Blo 195805 12364001 := bstep (se 2 (by rfl) ⟨4636500, by rfl⟩ : syracuseStep 12364001 = 9273001) B9273001
theorem B448847 : Blo 195805 448847 := bstep (se 1 (by rfl) ⟨336635, by rfl⟩ : syracuseStep 448847 = 673271) B673271
theorem B21722651 : Blo 195805 21722651 := bstep (se 1 (by rfl) ⟨16291988, by rfl⟩ : syracuseStep 21722651 = 32583977) B32583977
theorem B81721511 : Blo 195805 81721511 := bstep (se 1 (by rfl) ⟨61291133, by rfl⟩ : syracuseStep 81721511 = 122582267) B122582267
theorem B299231 : Blo 195805 299231 := bstep (se 1 (by rfl) ⟨224423, by rfl⟩ : syracuseStep 299231 = 448847) B448847
theorem B634367 : Blo 195805 634367 := bstep (se 1 (by rfl) ⟨475775, by rfl⟩ : syracuseStep 634367 = 951551) B951551
theorem B8242667 : Blo 195805 8242667 := bstep (se 1 (by rfl) ⟨6182000, by rfl⟩ : syracuseStep 8242667 = 12364001) B12364001
theorem B54481007 : Blo 195805 54481007 := bstep (se 1 (by rfl) ⟨40860755, by rfl⟩ : syracuseStep 54481007 = 81721511) B81721511
theorem B14481767 : Blo 195805 14481767 := bstep (se 1 (by rfl) ⟨10861325, by rfl⟩ : syracuseStep 14481767 = 21722651) B21722651
theorem B199487 : Blo 195805 199487 := bstep (se 1 (by rfl) ⟨149615, by rfl⟩ : syracuseStep 199487 = 299231) B299231
theorem B36320671 : Blo 195805 36320671 := bstep (se 1 (by rfl) ⟨27240503, by rfl⟩ : syracuseStep 36320671 = 54481007) B54481007
theorem B9654511 : Blo 195805 9654511 := bstep (se 1 (by rfl) ⟨7240883, by rfl⟩ : syracuseStep 9654511 = 14481767) B14481767
theorem B5495111 : Blo 195805 5495111 := bstep (se 1 (by rfl) ⟨4121333, by rfl⟩ : syracuseStep 5495111 = 8242667) B8242667
theorem B422911 : Blo 195805 422911 := bstep (se 1 (by rfl) ⟨317183, by rfl⟩ : syracuseStep 422911 = 634367) B634367
theorem B3663407 : Blo 195805 3663407 := bstep (se 1 (by rfl) ⟨2747555, by rfl⟩ : syracuseStep 3663407 = 5495111) B5495111
theorem B2255525 : Blo 195805 2255525 := bstep (se 4 (by rfl) ⟨211455, by rfl⟩ : syracuseStep 2255525 = 422911) B422911
theorem B12872681 : Blo 195805 12872681 := bstep (se 2 (by rfl) ⟨4827255, by rfl⟩ : syracuseStep 12872681 = 9654511) B9654511
theorem B48427561 : Blo 195805 48427561 := bstep (se 2 (by rfl) ⟨18160335, by rfl⟩ : syracuseStep 48427561 = 36320671) B36320671
theorem B64570081 : Blo 195805 64570081 := bstep (se 2 (by rfl) ⟨24213780, by rfl⟩ : syracuseStep 64570081 = 48427561) B48427561
theorem B2442271 : Blo 195805 2442271 := bstep (se 1 (by rfl) ⟨1831703, by rfl⟩ : syracuseStep 2442271 = 3663407) B3663407
theorem B1503683 : Blo 195805 1503683 := bstep (se 1 (by rfl) ⟨1127762, by rfl⟩ : syracuseStep 1503683 = 2255525) B2255525
theorem B8581787 : Blo 195805 8581787 := bstep (se 1 (by rfl) ⟨6436340, by rfl⟩ : syracuseStep 8581787 = 12872681) B12872681
theorem B86093441 : Blo 195805 86093441 := bstep (se 2 (by rfl) ⟨32285040, by rfl⟩ : syracuseStep 86093441 = 64570081) B64570081
theorem B3256361 : Blo 195805 3256361 := bstep (se 2 (by rfl) ⟨1221135, by rfl⟩ : syracuseStep 3256361 = 2442271) B2442271
theorem B1002455 : Blo 195805 1002455 := bstep (se 1 (by rfl) ⟨751841, by rfl⟩ : syracuseStep 1002455 = 1503683) B1503683
theorem B5721191 : Blo 195805 5721191 := bstep (se 1 (by rfl) ⟨4290893, by rfl⟩ : syracuseStep 5721191 = 8581787) B8581787
theorem B2170907 : Blo 195805 2170907 := bstep (se 1 (by rfl) ⟨1628180, by rfl⟩ : syracuseStep 2170907 = 3256361) B3256361
theorem B668303 : Blo 195805 668303 := bstep (se 1 (by rfl) ⟨501227, by rfl⟩ : syracuseStep 668303 = 1002455) B1002455
theorem B3814127 : Blo 195805 3814127 := bstep (se 1 (by rfl) ⟨2860595, by rfl⟩ : syracuseStep 3814127 = 5721191) B5721191
theorem B57395627 : Blo 195805 57395627 := bstep (se 1 (by rfl) ⟨43046720, by rfl⟩ : syracuseStep 57395627 = 86093441) B86093441
theorem B1447271 : Blo 195805 1447271 := bstep (se 1 (by rfl) ⟨1085453, by rfl⟩ : syracuseStep 1447271 = 2170907) B2170907
theorem B445535 : Blo 195805 445535 := bstep (se 1 (by rfl) ⟨334151, by rfl⟩ : syracuseStep 445535 = 668303) B668303
theorem B2542751 : Blo 195805 2542751 := bstep (se 1 (by rfl) ⟨1907063, by rfl⟩ : syracuseStep 2542751 = 3814127) B3814127
theorem B38263751 : Blo 195805 38263751 := bstep (se 1 (by rfl) ⟨28697813, by rfl⟩ : syracuseStep 38263751 = 57395627) B57395627
theorem B297023 : Blo 195805 297023 := bstep (se 1 (by rfl) ⟨222767, by rfl⟩ : syracuseStep 297023 = 445535) B445535
theorem B964847 : Blo 195805 964847 := bstep (se 1 (by rfl) ⟨723635, by rfl⟩ : syracuseStep 964847 = 1447271) B1447271
theorem B25509167 : Blo 195805 25509167 := bstep (se 1 (by rfl) ⟨19131875, by rfl⟩ : syracuseStep 25509167 = 38263751) B38263751
theorem B1695167 : Blo 195805 1695167 := bstep (se 1 (by rfl) ⟨1271375, by rfl⟩ : syracuseStep 1695167 = 2542751) B2542751
theorem B198015 : Blo 195805 198015 := bstep (se 1 (by rfl) ⟨148511, by rfl⟩ : syracuseStep 198015 = 297023) B297023
theorem B1130111 : Blo 195805 1130111 := bstep (se 1 (by rfl) ⟨847583, by rfl⟩ : syracuseStep 1130111 = 1695167) B1695167
theorem B643231 : Blo 195805 643231 := bstep (se 1 (by rfl) ⟨482423, by rfl⟩ : syracuseStep 643231 = 964847) B964847
theorem B17006111 : Blo 195805 17006111 := bstep (se 1 (by rfl) ⟨12754583, by rfl⟩ : syracuseStep 17006111 = 25509167) B25509167
theorem B857641 : Blo 195805 857641 := bstep (se 2 (by rfl) ⟨321615, by rfl⟩ : syracuseStep 857641 = 643231) B643231
theorem B11337407 : Blo 195805 11337407 := bstep (se 1 (by rfl) ⟨8503055, by rfl⟩ : syracuseStep 11337407 = 17006111) B17006111
theorem B753407 : Blo 195805 753407 := bstep (se 1 (by rfl) ⟨565055, by rfl⟩ : syracuseStep 753407 = 1130111) B1130111
theorem B502271 : Blo 195805 502271 := bstep (se 1 (by rfl) ⟨376703, by rfl⟩ : syracuseStep 502271 = 753407) B753407
theorem B7558271 : Blo 195805 7558271 := bstep (se 1 (by rfl) ⟨5668703, by rfl⟩ : syracuseStep 7558271 = 11337407) B11337407
theorem B1143521 : Blo 195805 1143521 := bstep (se 2 (by rfl) ⟨428820, by rfl⟩ : syracuseStep 1143521 = 857641) B857641
theorem B334847 : Blo 195805 334847 := bstep (se 1 (by rfl) ⟨251135, by rfl⟩ : syracuseStep 334847 = 502271) B502271
theorem B762347 : Blo 195805 762347 := bstep (se 1 (by rfl) ⟨571760, by rfl⟩ : syracuseStep 762347 = 1143521) B1143521
theorem B5038847 : Blo 195805 5038847 := bstep (se 1 (by rfl) ⟨3779135, by rfl⟩ : syracuseStep 5038847 = 7558271) B7558271
theorem B508231 : Blo 195805 508231 := bstep (se 1 (by rfl) ⟨381173, by rfl⟩ : syracuseStep 508231 = 762347) B762347
theorem B3359231 : Blo 195805 3359231 := bstep (se 1 (by rfl) ⟨2519423, by rfl⟩ : syracuseStep 3359231 = 5038847) B5038847
theorem B223231 : Blo 195805 223231 := bstep (se 1 (by rfl) ⟨167423, by rfl⟩ : syracuseStep 223231 = 334847) B334847
theorem B297641 : Blo 195805 297641 := bstep (se 2 (by rfl) ⟨111615, by rfl⟩ : syracuseStep 297641 = 223231) B223231
theorem B2239487 : Blo 195805 2239487 := bstep (se 1 (by rfl) ⟨1679615, by rfl⟩ : syracuseStep 2239487 = 3359231) B3359231
theorem B2710565 : Blo 195805 2710565 := bstep (se 4 (by rfl) ⟨254115, by rfl⟩ : syracuseStep 2710565 = 508231) B508231
theorem B198427 : Blo 195805 198427 := bstep (se 1 (by rfl) ⟨148820, by rfl⟩ : syracuseStep 198427 = 297641) B297641
theorem B1807043 : Blo 195805 1807043 := bstep (se 1 (by rfl) ⟨1355282, by rfl⟩ : syracuseStep 1807043 = 2710565) B2710565
theorem B1492991 : Blo 195805 1492991 := bstep (se 1 (by rfl) ⟨1119743, by rfl⟩ : syracuseStep 1492991 = 2239487) B2239487
theorem B4818781 : Blo 195805 4818781 := bstep (se 3 (by rfl) ⟨903521, by rfl⟩ : syracuseStep 4818781 = 1807043) B1807043
theorem B995327 : Blo 195805 995327 := bstep (se 1 (by rfl) ⟨746495, by rfl⟩ : syracuseStep 995327 = 1492991) B1492991
theorem B6425041 : Blo 195805 6425041 := bstep (se 2 (by rfl) ⟨2409390, by rfl⟩ : syracuseStep 6425041 = 4818781) B4818781
theorem B663551 : Blo 195805 663551 := bstep (se 1 (by rfl) ⟨497663, by rfl⟩ : syracuseStep 663551 = 995327) B995327
theorem B8566721 : Blo 195805 8566721 := bstep (se 2 (by rfl) ⟨3212520, by rfl⟩ : syracuseStep 8566721 = 6425041) B6425041
theorem B442367 : Blo 195805 442367 := bstep (se 1 (by rfl) ⟨331775, by rfl⟩ : syracuseStep 442367 = 663551) B663551
theorem B5711147 : Blo 195805 5711147 := bstep (se 1 (by rfl) ⟨4283360, by rfl⟩ : syracuseStep 5711147 = 8566721) B8566721
theorem B294911 : Blo 195805 294911 := bstep (se 1 (by rfl) ⟨221183, by rfl⟩ : syracuseStep 294911 = 442367) B442367
theorem B196607 : Blo 195805 196607 := bstep (se 1 (by rfl) ⟨147455, by rfl⟩ : syracuseStep 196607 = 294911) B294911
theorem B3807431 : Blo 195805 3807431 := bstep (se 1 (by rfl) ⟨2855573, by rfl⟩ : syracuseStep 3807431 = 5711147) B5711147
theorem B2538287 : Blo 195805 2538287 := bstep (se 1 (by rfl) ⟨1903715, by rfl⟩ : syracuseStep 2538287 = 3807431) B3807431
theorem B1692191 : Blo 195805 1692191 := bstep (se 1 (by rfl) ⟨1269143, by rfl⟩ : syracuseStep 1692191 = 2538287) B2538287
theorem B1128127 : Blo 195805 1128127 := bstep (se 1 (by rfl) ⟨846095, by rfl⟩ : syracuseStep 1128127 = 1692191) B1692191
theorem B1504169 : Blo 195805 1504169 := bstep (se 2 (by rfl) ⟨564063, by rfl⟩ : syracuseStep 1504169 = 1128127) B1128127
theorem B1002779 : Blo 195805 1002779 := bstep (se 1 (by rfl) ⟨752084, by rfl⟩ : syracuseStep 1002779 = 1504169) B1504169
theorem B668519 : Blo 195805 668519 := bstep (se 1 (by rfl) ⟨501389, by rfl⟩ : syracuseStep 668519 = 1002779) B1002779
theorem B445679 : Blo 195805 445679 := bstep (se 1 (by rfl) ⟨334259, by rfl⟩ : syracuseStep 445679 = 668519) B668519
theorem B297119 : Blo 195805 297119 := bstep (se 1 (by rfl) ⟨222839, by rfl⟩ : syracuseStep 297119 = 445679) B445679
theorem B198079 : Blo 195805 198079 := bstep (se 1 (by rfl) ⟨148559, by rfl⟩ : syracuseStep 198079 = 297119) B297119

theorem C0 (j : ℕ) (h1 : 48951 ≤ j) (h2 : j ≤ 49650) : Blo 195805 (4 * j + 3) := by
  interval_cases j
  · exact B195807
  · exact B195811
  · exact B195815
  · exact B195819
  · exact B195823
  · exact B195827
  · exact B195831
  · exact B195835
  · exact B195839
  · exact B195843
  · exact B195847
  · exact B195851
  · exact B195855
  · exact B195859
  · exact B195863
  · exact B195867
  · exact B195871
  · exact B195875
  · exact B195879
  · exact B195883
  · exact B195887
  · exact B195891
  · exact B195895
  · exact B195899
  · exact B195903
  · exact B195907
  · exact B195911
  · exact B195915
  · exact B195919
  · exact B195923
  · exact B195927
  · exact B195931
  · exact B195935
  · exact B195939
  · exact B195943
  · exact B195947
  · exact B195951
  · exact B195955
  · exact B195959
  · exact B195963
  · exact B195967
  · exact B195971
  · exact B195975
  · exact B195979
  · exact B195983
  · exact B195987
  · exact B195991
  · exact B195995
  · exact B195999
  · exact B196003
  · exact B196007
  · exact B196011
  · exact B196015
  · exact B196019
  · exact B196023
  · exact B196027
  · exact B196031
  · exact B196035
  · exact B196039
  · exact B196043
  · exact B196047
  · exact B196051
  · exact B196055
  · exact B196059
  · exact B196063
  · exact B196067
  · exact B196071
  · exact B196075
  · exact B196079
  · exact B196083
  · exact B196087
  · exact B196091
  · exact B196095
  · exact B196099
  · exact B196103
  · exact B196107
  · exact B196111
  · exact B196115
  · exact B196119
  · exact B196123
  · exact B196127
  · exact B196131
  · exact B196135
  · exact B196139
  · exact B196143
  · exact B196147
  · exact B196151
  · exact B196155
  · exact B196159
  · exact B196163
  · exact B196167
  · exact B196171
  · exact B196175
  · exact B196179
  · exact B196183
  · exact B196187
  · exact B196191
  · exact B196195
  · exact B196199
  · exact B196203
  · exact B196207
  · exact B196211
  · exact B196215
  · exact B196219
  · exact B196223
  · exact B196227
  · exact B196231
  · exact B196235
  · exact B196239
  · exact B196243
  · exact B196247
  · exact B196251
  · exact B196255
  · exact B196259
  · exact B196263
  · exact B196267
  · exact B196271
  · exact B196275
  · exact B196279
  · exact B196283
  · exact B196287
  · exact B196291
  · exact B196295
  · exact B196299
  · exact B196303
  · exact B196307
  · exact B196311
  · exact B196315
  · exact B196319
  · exact B196323
  · exact B196327
  · exact B196331
  · exact B196335
  · exact B196339
  · exact B196343
  · exact B196347
  · exact B196351
  · exact B196355
  · exact B196359
  · exact B196363
  · exact B196367
  · exact B196371
  · exact B196375
  · exact B196379
  · exact B196383
  · exact B196387
  · exact B196391
  · exact B196395
  · exact B196399
  · exact B196403
  · exact B196407
  · exact B196411
  · exact B196415
  · exact B196419
  · exact B196423
  · exact B196427
  · exact B196431
  · exact B196435
  · exact B196439
  · exact B196443
  · exact B196447
  · exact B196451
  · exact B196455
  · exact B196459
  · exact B196463
  · exact B196467
  · exact B196471
  · exact B196475
  · exact B196479
  · exact B196483
  · exact B196487
  · exact B196491
  · exact B196495
  · exact B196499
  · exact B196503
  · exact B196507
  · exact B196511
  · exact B196515
  · exact B196519
  · exact B196523
  · exact B196527
  · exact B196531
  · exact B196535
  · exact B196539
  · exact B196543
  · exact B196547
  · exact B196551
  · exact B196555
  · exact B196559
  · exact B196563
  · exact B196567
  · exact B196571
  · exact B196575
  · exact B196579
  · exact B196583
  · exact B196587
  · exact B196591
  · exact B196595
  · exact B196599
  · exact B196603
  · exact B196607
  · exact B196611
  · exact B196615
  · exact B196619
  · exact B196623
  · exact B196627
  · exact B196631
  · exact B196635
  · exact B196639
  · exact B196643
  · exact B196647
  · exact B196651
  · exact B196655
  · exact B196659
  · exact B196663
  · exact B196667
  · exact B196671
  · exact B196675
  · exact B196679
  · exact B196683
  · exact B196687
  · exact B196691
  · exact B196695
  · exact B196699
  · exact B196703
  · exact B196707
  · exact B196711
  · exact B196715
  · exact B196719
  · exact B196723
  · exact B196727
  · exact B196731
  · exact B196735
  · exact B196739
  · exact B196743
  · exact B196747
  · exact B196751
  · exact B196755
  · exact B196759
  · exact B196763
  · exact B196767
  · exact B196771
  · exact B196775
  · exact B196779
  · exact B196783
  · exact B196787
  · exact B196791
  · exact B196795
  · exact B196799
  · exact B196803
  · exact B196807
  · exact B196811
  · exact B196815
  · exact B196819
  · exact B196823
  · exact B196827
  · exact B196831
  · exact B196835
  · exact B196839
  · exact B196843
  · exact B196847
  · exact B196851
  · exact B196855
  · exact B196859
  · exact B196863
  · exact B196867
  · exact B196871
  · exact B196875
  · exact B196879
  · exact B196883
  · exact B196887
  · exact B196891
  · exact B196895
  · exact B196899
  · exact B196903
  · exact B196907
  · exact B196911
  · exact B196915
  · exact B196919
  · exact B196923
  · exact B196927
  · exact B196931
  · exact B196935
  · exact B196939
  · exact B196943
  · exact B196947
  · exact B196951
  · exact B196955
  · exact B196959
  · exact B196963
  · exact B196967
  · exact B196971
  · exact B196975
  · exact B196979
  · exact B196983
  · exact B196987
  · exact B196991
  · exact B196995
  · exact B196999
  · exact B197003
  · exact B197007
  · exact B197011
  · exact B197015
  · exact B197019
  · exact B197023
  · exact B197027
  · exact B197031
  · exact B197035
  · exact B197039
  · exact B197043
  · exact B197047
  · exact B197051
  · exact B197055
  · exact B197059
  · exact B197063
  · exact B197067
  · exact B197071
  · exact B197075
  · exact B197079
  · exact B197083
  · exact B197087
  · exact B197091
  · exact B197095
  · exact B197099
  · exact B197103
  · exact B197107
  · exact B197111
  · exact B197115
  · exact B197119
  · exact B197123
  · exact B197127
  · exact B197131
  · exact B197135
  · exact B197139
  · exact B197143
  · exact B197147
  · exact B197151
  · exact B197155
  · exact B197159
  · exact B197163
  · exact B197167
  · exact B197171
  · exact B197175
  · exact B197179
  · exact B197183
  · exact B197187
  · exact B197191
  · exact B197195
  · exact B197199
  · exact B197203
  · exact B197207
  · exact B197211
  · exact B197215
  · exact B197219
  · exact B197223
  · exact B197227
  · exact B197231
  · exact B197235
  · exact B197239
  · exact B197243
  · exact B197247
  · exact B197251
  · exact B197255
  · exact B197259
  · exact B197263
  · exact B197267
  · exact B197271
  · exact B197275
  · exact B197279
  · exact B197283
  · exact B197287
  · exact B197291
  · exact B197295
  · exact B197299
  · exact B197303
  · exact B197307
  · exact B197311
  · exact B197315
  · exact B197319
  · exact B197323
  · exact B197327
  · exact B197331
  · exact B197335
  · exact B197339
  · exact B197343
  · exact B197347
  · exact B197351
  · exact B197355
  · exact B197359
  · exact B197363
  · exact B197367
  · exact B197371
  · exact B197375
  · exact B197379
  · exact B197383
  · exact B197387
  · exact B197391
  · exact B197395
  · exact B197399
  · exact B197403
  · exact B197407
  · exact B197411
  · exact B197415
  · exact B197419
  · exact B197423
  · exact B197427
  · exact B197431
  · exact B197435
  · exact B197439
  · exact B197443
  · exact B197447
  · exact B197451
  · exact B197455
  · exact B197459
  · exact B197463
  · exact B197467
  · exact B197471
  · exact B197475
  · exact B197479
  · exact B197483
  · exact B197487
  · exact B197491
  · exact B197495
  · exact B197499
  · exact B197503
  · exact B197507
  · exact B197511
  · exact B197515
  · exact B197519
  · exact B197523
  · exact B197527
  · exact B197531
  · exact B197535
  · exact B197539
  · exact B197543
  · exact B197547
  · exact B197551
  · exact B197555
  · exact B197559
  · exact B197563
  · exact B197567
  · exact B197571
  · exact B197575
  · exact B197579
  · exact B197583
  · exact B197587
  · exact B197591
  · exact B197595
  · exact B197599
  · exact B197603
  · exact B197607
  · exact B197611
  · exact B197615
  · exact B197619
  · exact B197623
  · exact B197627
  · exact B197631
  · exact B197635
  · exact B197639
  · exact B197643
  · exact B197647
  · exact B197651
  · exact B197655
  · exact B197659
  · exact B197663
  · exact B197667
  · exact B197671
  · exact B197675
  · exact B197679
  · exact B197683
  · exact B197687
  · exact B197691
  · exact B197695
  · exact B197699
  · exact B197703
  · exact B197707
  · exact B197711
  · exact B197715
  · exact B197719
  · exact B197723
  · exact B197727
  · exact B197731
  · exact B197735
  · exact B197739
  · exact B197743
  · exact B197747
  · exact B197751
  · exact B197755
  · exact B197759
  · exact B197763
  · exact B197767
  · exact B197771
  · exact B197775
  · exact B197779
  · exact B197783
  · exact B197787
  · exact B197791
  · exact B197795
  · exact B197799
  · exact B197803
  · exact B197807
  · exact B197811
  · exact B197815
  · exact B197819
  · exact B197823
  · exact B197827
  · exact B197831
  · exact B197835
  · exact B197839
  · exact B197843
  · exact B197847
  · exact B197851
  · exact B197855
  · exact B197859
  · exact B197863
  · exact B197867
  · exact B197871
  · exact B197875
  · exact B197879
  · exact B197883
  · exact B197887
  · exact B197891
  · exact B197895
  · exact B197899
  · exact B197903
  · exact B197907
  · exact B197911
  · exact B197915
  · exact B197919
  · exact B197923
  · exact B197927
  · exact B197931
  · exact B197935
  · exact B197939
  · exact B197943
  · exact B197947
  · exact B197951
  · exact B197955
  · exact B197959
  · exact B197963
  · exact B197967
  · exact B197971
  · exact B197975
  · exact B197979
  · exact B197983
  · exact B197987
  · exact B197991
  · exact B197995
  · exact B197999
  · exact B198003
  · exact B198007
  · exact B198011
  · exact B198015
  · exact B198019
  · exact B198023
  · exact B198027
  · exact B198031
  · exact B198035
  · exact B198039
  · exact B198043
  · exact B198047
  · exact B198051
  · exact B198055
  · exact B198059
  · exact B198063
  · exact B198067
  · exact B198071
  · exact B198075
  · exact B198079
  · exact B198083
  · exact B198087
  · exact B198091
  · exact B198095
  · exact B198099
  · exact B198103
  · exact B198107
  · exact B198111
  · exact B198115
  · exact B198119
  · exact B198123
  · exact B198127
  · exact B198131
  · exact B198135
  · exact B198139
  · exact B198143
  · exact B198147
  · exact B198151
  · exact B198155
  · exact B198159
  · exact B198163
  · exact B198167
  · exact B198171
  · exact B198175
  · exact B198179
  · exact B198183
  · exact B198187
  · exact B198191
  · exact B198195
  · exact B198199
  · exact B198203
  · exact B198207
  · exact B198211
  · exact B198215
  · exact B198219
  · exact B198223
  · exact B198227
  · exact B198231
  · exact B198235
  · exact B198239
  · exact B198243
  · exact B198247
  · exact B198251
  · exact B198255
  · exact B198259
  · exact B198263
  · exact B198267
  · exact B198271
  · exact B198275
  · exact B198279
  · exact B198283
  · exact B198287
  · exact B198291
  · exact B198295
  · exact B198299
  · exact B198303
  · exact B198307
  · exact B198311
  · exact B198315
  · exact B198319
  · exact B198323
  · exact B198327
  · exact B198331
  · exact B198335
  · exact B198339
  · exact B198343
  · exact B198347
  · exact B198351
  · exact B198355
  · exact B198359
  · exact B198363
  · exact B198367
  · exact B198371
  · exact B198375
  · exact B198379
  · exact B198383
  · exact B198387
  · exact B198391
  · exact B198395
  · exact B198399
  · exact B198403
  · exact B198407
  · exact B198411
  · exact B198415
  · exact B198419
  · exact B198423
  · exact B198427
  · exact B198431
  · exact B198435
  · exact B198439
  · exact B198443
  · exact B198447
  · exact B198451
  · exact B198455
  · exact B198459
  · exact B198463
  · exact B198467
  · exact B198471
  · exact B198475
  · exact B198479
  · exact B198483
  · exact B198487
  · exact B198491
  · exact B198495
  · exact B198499
  · exact B198503
  · exact B198507
  · exact B198511
  · exact B198515
  · exact B198519
  · exact B198523
  · exact B198527
  · exact B198531
  · exact B198535
  · exact B198539
  · exact B198543
  · exact B198547
  · exact B198551
  · exact B198555
  · exact B198559
  · exact B198563
  · exact B198567
  · exact B198571
  · exact B198575
  · exact B198579
  · exact B198583
  · exact B198587
  · exact B198591
  · exact B198595
  · exact B198599
  · exact B198603

theorem C1 (j : ℕ) (h1 : 49651 ≤ j) (h2 : j ≤ 49950) : Blo 195805 (4 * j + 3) := by
  interval_cases j
  · exact B198607
  · exact B198611
  · exact B198615
  · exact B198619
  · exact B198623
  · exact B198627
  · exact B198631
  · exact B198635
  · exact B198639
  · exact B198643
  · exact B198647
  · exact B198651
  · exact B198655
  · exact B198659
  · exact B198663
  · exact B198667
  · exact B198671
  · exact B198675
  · exact B198679
  · exact B198683
  · exact B198687
  · exact B198691
  · exact B198695
  · exact B198699
  · exact B198703
  · exact B198707
  · exact B198711
  · exact B198715
  · exact B198719
  · exact B198723
  · exact B198727
  · exact B198731
  · exact B198735
  · exact B198739
  · exact B198743
  · exact B198747
  · exact B198751
  · exact B198755
  · exact B198759
  · exact B198763
  · exact B198767
  · exact B198771
  · exact B198775
  · exact B198779
  · exact B198783
  · exact B198787
  · exact B198791
  · exact B198795
  · exact B198799
  · exact B198803
  · exact B198807
  · exact B198811
  · exact B198815
  · exact B198819
  · exact B198823
  · exact B198827
  · exact B198831
  · exact B198835
  · exact B198839
  · exact B198843
  · exact B198847
  · exact B198851
  · exact B198855
  · exact B198859
  · exact B198863
  · exact B198867
  · exact B198871
  · exact B198875
  · exact B198879
  · exact B198883
  · exact B198887
  · exact B198891
  · exact B198895
  · exact B198899
  · exact B198903
  · exact B198907
  · exact B198911
  · exact B198915
  · exact B198919
  · exact B198923
  · exact B198927
  · exact B198931
  · exact B198935
  · exact B198939
  · exact B198943
  · exact B198947
  · exact B198951
  · exact B198955
  · exact B198959
  · exact B198963
  · exact B198967
  · exact B198971
  · exact B198975
  · exact B198979
  · exact B198983
  · exact B198987
  · exact B198991
  · exact B198995
  · exact B198999
  · exact B199003
  · exact B199007
  · exact B199011
  · exact B199015
  · exact B199019
  · exact B199023
  · exact B199027
  · exact B199031
  · exact B199035
  · exact B199039
  · exact B199043
  · exact B199047
  · exact B199051
  · exact B199055
  · exact B199059
  · exact B199063
  · exact B199067
  · exact B199071
  · exact B199075
  · exact B199079
  · exact B199083
  · exact B199087
  · exact B199091
  · exact B199095
  · exact B199099
  · exact B199103
  · exact B199107
  · exact B199111
  · exact B199115
  · exact B199119
  · exact B199123
  · exact B199127
  · exact B199131
  · exact B199135
  · exact B199139
  · exact B199143
  · exact B199147
  · exact B199151
  · exact B199155
  · exact B199159
  · exact B199163
  · exact B199167
  · exact B199171
  · exact B199175
  · exact B199179
  · exact B199183
  · exact B199187
  · exact B199191
  · exact B199195
  · exact B199199
  · exact B199203
  · exact B199207
  · exact B199211
  · exact B199215
  · exact B199219
  · exact B199223
  · exact B199227
  · exact B199231
  · exact B199235
  · exact B199239
  · exact B199243
  · exact B199247
  · exact B199251
  · exact B199255
  · exact B199259
  · exact B199263
  · exact B199267
  · exact B199271
  · exact B199275
  · exact B199279
  · exact B199283
  · exact B199287
  · exact B199291
  · exact B199295
  · exact B199299
  · exact B199303
  · exact B199307
  · exact B199311
  · exact B199315
  · exact B199319
  · exact B199323
  · exact B199327
  · exact B199331
  · exact B199335
  · exact B199339
  · exact B199343
  · exact B199347
  · exact B199351
  · exact B199355
  · exact B199359
  · exact B199363
  · exact B199367
  · exact B199371
  · exact B199375
  · exact B199379
  · exact B199383
  · exact B199387
  · exact B199391
  · exact B199395
  · exact B199399
  · exact B199403
  · exact B199407
  · exact B199411
  · exact B199415
  · exact B199419
  · exact B199423
  · exact B199427
  · exact B199431
  · exact B199435
  · exact B199439
  · exact B199443
  · exact B199447
  · exact B199451
  · exact B199455
  · exact B199459
  · exact B199463
  · exact B199467
  · exact B199471
  · exact B199475
  · exact B199479
  · exact B199483
  · exact B199487
  · exact B199491
  · exact B199495
  · exact B199499
  · exact B199503
  · exact B199507
  · exact B199511
  · exact B199515
  · exact B199519
  · exact B199523
  · exact B199527
  · exact B199531
  · exact B199535
  · exact B199539
  · exact B199543
  · exact B199547
  · exact B199551
  · exact B199555
  · exact B199559
  · exact B199563
  · exact B199567
  · exact B199571
  · exact B199575
  · exact B199579
  · exact B199583
  · exact B199587
  · exact B199591
  · exact B199595
  · exact B199599
  · exact B199603
  · exact B199607
  · exact B199611
  · exact B199615
  · exact B199619
  · exact B199623
  · exact B199627
  · exact B199631
  · exact B199635
  · exact B199639
  · exact B199643
  · exact B199647
  · exact B199651
  · exact B199655
  · exact B199659
  · exact B199663
  · exact B199667
  · exact B199671
  · exact B199675
  · exact B199679
  · exact B199683
  · exact B199687
  · exact B199691
  · exact B199695
  · exact B199699
  · exact B199703
  · exact B199707
  · exact B199711
  · exact B199715
  · exact B199719
  · exact B199723
  · exact B199727
  · exact B199731
  · exact B199735
  · exact B199739
  · exact B199743
  · exact B199747
  · exact B199751
  · exact B199755
  · exact B199759
  · exact B199763
  · exact B199767
  · exact B199771
  · exact B199775
  · exact B199779
  · exact B199783
  · exact B199787
  · exact B199791
  · exact B199795
  · exact B199799
  · exact B199803

theorem solution (m : ℕ) (hlo : 195805 ≤ m) (hhi : m ≤ 199805) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 48951 ≤ j := by omega
    have hj2 : j ≤ 49950 := by omega
    have hb : Blo 195805 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 49651 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
