-- Prove2me | solution 1 for syracuse_descends_range_1871637_1873637
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:14:16.425776+00:00
-- url     : https://prove2.me/submissions/deec1812-0825-4461-808d-f23bb63e5c6a

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


theorem B5996549 : Blo 1871637 5996549 := bbase (se 4 (by rfl) ⟨562176, by rfl⟩ : syracuseStep 5996549 = 1124353) (by norm_num)
theorem B2809877 : Blo 1871637 2809877 := bbase (se 6 (by rfl) ⟨65856, by rfl⟩ : syracuseStep 2809877 = 131713) (by norm_num)
theorem B2809901 : Blo 1871637 2809901 := bbase (se 3 (by rfl) ⟨526856, by rfl⟩ : syracuseStep 2809901 = 1053713) (by norm_num)
theorem B1998901 : Blo 1871637 1998901 := bbase (se 5 (by rfl) ⟨93698, by rfl⟩ : syracuseStep 1998901 = 187397) (by norm_num)
theorem B2809925 : Blo 1871637 2809925 := bbase (se 4 (by rfl) ⟨263430, by rfl⟩ : syracuseStep 2809925 = 526861) (by norm_num)
theorem B6406229 : Blo 1871637 6406229 := bbase (se 8 (by rfl) ⟨37536, by rfl⟩ : syracuseStep 6406229 = 75073) (by norm_num)
theorem B48013397 : Blo 1871637 48013397 := bbase (se 8 (by rfl) ⟨281328, by rfl⟩ : syracuseStep 48013397 = 562657) (by norm_num)
theorem B2809949 : Blo 1871637 2809949 := bbase (se 3 (by rfl) ⟨526865, by rfl⟩ : syracuseStep 2809949 = 1053731) (by norm_num)
theorem B7110773 : Blo 1871637 7110773 := bbase (se 5 (by rfl) ⟨333317, by rfl⟩ : syracuseStep 7110773 = 666635) (by norm_num)
theorem B2809973 : Blo 1871637 2809973 := bbase (se 5 (by rfl) ⟨131717, by rfl⟩ : syracuseStep 2809973 = 263435) (by norm_num)
theorem B3997829 : Blo 1871637 3997829 := bbase (se 4 (by rfl) ⟨374796, by rfl⟩ : syracuseStep 3997829 = 749593) (by norm_num)
theorem B2809997 : Blo 1871637 2809997 := bbase (se 3 (by rfl) ⟨526874, by rfl⟩ : syracuseStep 2809997 = 1053749) (by norm_num)
theorem B3555485 : Blo 1871637 3555485 := bbase (se 3 (by rfl) ⟨666653, by rfl⟩ : syracuseStep 3555485 = 1333307) (by norm_num)
theorem B6750373 : Blo 1871637 6750373 := bbase (se 4 (by rfl) ⟨632847, by rfl⟩ : syracuseStep 6750373 = 1265695) (by norm_num)
theorem B2810021 : Blo 1871637 2810021 := bbase (se 4 (by rfl) ⟨263439, by rfl⟩ : syracuseStep 2810021 = 526879) (by norm_num)
theorem B2810045 : Blo 1871637 2810045 := bbase (se 3 (by rfl) ⟨526883, by rfl⟩ : syracuseStep 2810045 = 1053767) (by norm_num)
theorem B72982741 : Blo 1871637 72982741 := bbase (se 7 (by rfl) ⟨855266, by rfl⟩ : syracuseStep 72982741 = 1710533) (by norm_num)
theorem B2810069 : Blo 1871637 2810069 := bbase (se 7 (by rfl) ⟨32930, by rfl⟩ : syracuseStep 2810069 = 65861) (by norm_num)
theorem B1999085 : Blo 1871637 1999085 := bbase (se 3 (by rfl) ⟨374828, by rfl⟩ : syracuseStep 1999085 = 749657) (by norm_num)
theorem B2810093 : Blo 1871637 2810093 := bbase (se 3 (by rfl) ⟨526892, by rfl⟩ : syracuseStep 2810093 = 1053785) (by norm_num)
theorem B2810117 : Blo 1871637 2810117 := bbase (se 4 (by rfl) ⟨263448, by rfl⟩ : syracuseStep 2810117 = 526897) (by norm_num)
theorem B4055309 : Blo 1871637 4055309 := bbase (se 3 (by rfl) ⟨760370, by rfl⟩ : syracuseStep 4055309 = 1520741) (by norm_num)
theorem B2105617 : Blo 1871637 2105617 := bbase (se 2 (by rfl) ⟨789606, by rfl⟩ : syracuseStep 2105617 = 1579213) (by norm_num)
theorem B3997973 : Blo 1871637 3997973 := bbase (se 6 (by rfl) ⟨93702, by rfl⟩ : syracuseStep 3997973 = 187405) (by norm_num)
theorem B2810141 : Blo 1871637 2810141 := bbase (se 3 (by rfl) ⟨526901, by rfl⟩ : syracuseStep 2810141 = 1053803) (by norm_num)
theorem B2105653 : Blo 1871637 2105653 := bbase (se 5 (by rfl) ⟨98702, by rfl⟩ : syracuseStep 2105653 = 197405) (by norm_num)
theorem B2810165 : Blo 1871637 2810165 := bbase (se 5 (by rfl) ⟨131726, by rfl⟩ : syracuseStep 2810165 = 263453) (by norm_num)
theorem B2810189 : Blo 1871637 2810189 := bbase (se 3 (by rfl) ⟨526910, by rfl⟩ : syracuseStep 2810189 = 1053821) (by norm_num)
theorem B12165461 : Blo 1871637 12165461 := bbase (se 10 (by rfl) ⟨17820, by rfl⟩ : syracuseStep 12165461 = 35641) (by norm_num)
theorem B2105689 : Blo 1871637 2105689 := bbase (se 2 (by rfl) ⟨789633, by rfl⟩ : syracuseStep 2105689 = 1579267) (by norm_num)
theorem B2531677 : Blo 1871637 2531677 := bbase (se 3 (by rfl) ⟨474689, by rfl⟩ : syracuseStep 2531677 = 949379) (by norm_num)
theorem B2810213 : Blo 1871637 2810213 := bbase (se 4 (by rfl) ⟨263457, by rfl⟩ : syracuseStep 2810213 = 526915) (by norm_num)
theorem B2105725 : Blo 1871637 2105725 := bbase (se 3 (by rfl) ⟨394823, by rfl⟩ : syracuseStep 2105725 = 789647) (by norm_num)
theorem B2810237 : Blo 1871637 2810237 := bbase (se 3 (by rfl) ⟨526919, by rfl⟩ : syracuseStep 2810237 = 1053839) (by norm_num)
theorem B7111061 : Blo 1871637 7111061 := bbase (se 6 (by rfl) ⟨166665, by rfl⟩ : syracuseStep 7111061 = 333331) (by norm_num)
theorem B2810261 : Blo 1871637 2810261 := bbase (se 6 (by rfl) ⟨65865, by rfl⟩ : syracuseStep 2810261 = 131731) (by norm_num)
theorem B2998685 : Blo 1871637 2998685 := bbase (se 3 (by rfl) ⟨562253, by rfl⟩ : syracuseStep 2998685 = 1124507) (by norm_num)
theorem B2105761 : Blo 1871637 2105761 := bbase (se 2 (by rfl) ⟨789660, by rfl⟩ : syracuseStep 2105761 = 1579321) (by norm_num)
theorem B2810285 : Blo 1871637 2810285 := bbase (se 3 (by rfl) ⟨526928, by rfl⟩ : syracuseStep 2810285 = 1053857) (by norm_num)
theorem B2105797 : Blo 1871637 2105797 := bbase (se 4 (by rfl) ⟨197418, by rfl⟩ : syracuseStep 2105797 = 394837) (by norm_num)
theorem B2810309 : Blo 1871637 2810309 := bbase (se 4 (by rfl) ⟨263466, by rfl⟩ : syracuseStep 2810309 = 526933) (by norm_num)
theorem B2810333 : Blo 1871637 2810333 := bbase (se 3 (by rfl) ⟨526937, by rfl⟩ : syracuseStep 2810333 = 1053875) (by norm_num)
theorem B2105833 : Blo 1871637 2105833 := bbase (se 2 (by rfl) ⟨789687, by rfl⟩ : syracuseStep 2105833 = 1579375) (by norm_num)
theorem B4211189 : Blo 1871637 4211189 := bbase (se 5 (by rfl) ⟨197399, by rfl⟩ : syracuseStep 4211189 = 394799) (by norm_num)
theorem B2810357 : Blo 1871637 2810357 := bbase (se 5 (by rfl) ⟨131735, by rfl⟩ : syracuseStep 2810357 = 263471) (by norm_num)
theorem B1950205 : Blo 1871637 1950205 := bbase (se 3 (by rfl) ⟨365663, by rfl⟩ : syracuseStep 1950205 = 731327) (by norm_num)
theorem B2105869 : Blo 1871637 2105869 := bbase (se 3 (by rfl) ⟨394850, by rfl⟩ : syracuseStep 2105869 = 789701) (by norm_num)
theorem B2810381 : Blo 1871637 2810381 := bbase (se 3 (by rfl) ⟨526946, by rfl⟩ : syracuseStep 2810381 = 1053893) (by norm_num)
theorem B2810405 : Blo 1871637 2810405 := bbase (se 4 (by rfl) ⟨263475, by rfl⟩ : syracuseStep 2810405 = 526951) (by norm_num)
theorem B2105905 : Blo 1871637 2105905 := bbase (se 2 (by rfl) ⟨789714, by rfl⟩ : syracuseStep 2105905 = 1579429) (by norm_num)
theorem B2531893 : Blo 1871637 2531893 := bbase (se 5 (by rfl) ⟨118682, by rfl⟩ : syracuseStep 2531893 = 237365) (by norm_num)
theorem B4211261 : Blo 1871637 4211261 := bbase (se 3 (by rfl) ⟨789611, by rfl⟩ : syracuseStep 4211261 = 1579223) (by norm_num)
theorem B2810429 : Blo 1871637 2810429 := bbase (se 3 (by rfl) ⟨526955, by rfl⟩ : syracuseStep 2810429 = 1053911) (by norm_num)
theorem B2105941 : Blo 1871637 2105941 := bbase (se 8 (by rfl) ⟨12339, by rfl⟩ : syracuseStep 2105941 = 24679) (by norm_num)
theorem B2810453 : Blo 1871637 2810453 := bbase (se 8 (by rfl) ⟨16467, by rfl⟩ : syracuseStep 2810453 = 32935) (by norm_num)
theorem B2105977 : Blo 1871637 2105977 := bbase (se 2 (by rfl) ⟨789741, by rfl⟩ : syracuseStep 2105977 = 1579483) (by norm_num)
theorem B4211333 : Blo 1871637 4211333 := bbase (se 4 (by rfl) ⟨394812, by rfl⟩ : syracuseStep 4211333 = 789625) (by norm_num)
theorem B8544917 : Blo 1871637 8544917 := bbase (se 6 (by rfl) ⟨200271, by rfl⟩ : syracuseStep 8544917 = 400543) (by norm_num)
theorem B2106013 : Blo 1871637 2106013 := bbase (se 3 (by rfl) ⟨394877, by rfl⟩ : syracuseStep 2106013 = 789755) (by norm_num)
theorem B2106049 : Blo 1871637 2106049 := bbase (se 2 (by rfl) ⟨789768, by rfl⟩ : syracuseStep 2106049 = 1579537) (by norm_num)
theorem B4211405 : Blo 1871637 4211405 := bbase (se 3 (by rfl) ⟨789638, by rfl⟩ : syracuseStep 4211405 = 1579277) (by norm_num)
theorem B7996117 : Blo 1871637 7996117 := bbase (se 7 (by rfl) ⟨93704, by rfl⟩ : syracuseStep 7996117 = 187409) (by norm_num)
theorem B2106085 : Blo 1871637 2106085 := bbase (se 4 (by rfl) ⟨197445, by rfl⟩ : syracuseStep 2106085 = 394891) (by norm_num)
theorem B4498181 : Blo 1871637 4498181 := bbase (se 4 (by rfl) ⟨421704, by rfl⟩ : syracuseStep 4498181 = 843409) (by norm_num)
theorem B2106121 : Blo 1871637 2106121 := bbase (se 2 (by rfl) ⟨789795, by rfl⟩ : syracuseStep 2106121 = 1579591) (by norm_num)
theorem B4211477 : Blo 1871637 4211477 := bbase (se 6 (by rfl) ⟨98706, by rfl⟩ : syracuseStep 4211477 = 197413) (by norm_num)
theorem B2106157 : Blo 1871637 2106157 := bbase (se 3 (by rfl) ⟨394904, by rfl⟩ : syracuseStep 2106157 = 789809) (by norm_num)
theorem B17998645 : Blo 1871637 17998645 := bbase (se 5 (by rfl) ⟨843686, by rfl⟩ : syracuseStep 17998645 = 1687373) (by norm_num)
theorem B2532173 : Blo 1871637 2532173 := bbase (se 3 (by rfl) ⟨474782, by rfl⟩ : syracuseStep 2532173 = 949565) (by norm_num)
theorem B2106193 : Blo 1871637 2106193 := bbase (se 2 (by rfl) ⟨789822, by rfl⟩ : syracuseStep 2106193 = 1579645) (by norm_num)
theorem B4211549 : Blo 1871637 4211549 := bbase (se 3 (by rfl) ⟨789665, by rfl⟩ : syracuseStep 4211549 = 1579331) (by norm_num)
theorem B2106229 : Blo 1871637 2106229 := bbase (se 5 (by rfl) ⟨98729, by rfl⟩ : syracuseStep 2106229 = 197459) (by norm_num)
theorem B3556237 : Blo 1871637 3556237 := bbase (se 3 (by rfl) ⟨666794, by rfl⟩ : syracuseStep 3556237 = 1333589) (by norm_num)
theorem B2106265 : Blo 1871637 2106265 := bbase (se 2 (by rfl) ⟨789849, by rfl⟩ : syracuseStep 2106265 = 1579699) (by norm_num)
theorem B4211621 : Blo 1871637 4211621 := bbase (se 4 (by rfl) ⟨394839, by rfl⟩ : syracuseStep 4211621 = 789679) (by norm_num)
theorem B2106301 : Blo 1871637 2106301 := bbase (se 3 (by rfl) ⟨394931, by rfl⟩ : syracuseStep 2106301 = 789863) (by norm_num)
theorem B5333957 : Blo 1871637 5333957 := bbase (se 4 (by rfl) ⟨500058, by rfl⟩ : syracuseStep 5333957 = 1000117) (by norm_num)
theorem B1999837 : Blo 1871637 1999837 := bbase (se 3 (by rfl) ⟨374969, by rfl⟩ : syracuseStep 1999837 = 749939) (by norm_num)
theorem B2106337 : Blo 1871637 2106337 := bbase (se 2 (by rfl) ⟨789876, by rfl⟩ : syracuseStep 2106337 = 1579753) (by norm_num)
theorem B4211693 : Blo 1871637 4211693 := bbase (se 3 (by rfl) ⟨789692, by rfl⟩ : syracuseStep 4211693 = 1579385) (by norm_num)
theorem B11994101 : Blo 1871637 11994101 := bbase (se 5 (by rfl) ⟨562223, by rfl⟩ : syracuseStep 11994101 = 1124447) (by norm_num)
theorem B3998717 : Blo 1871637 3998717 := bbase (se 3 (by rfl) ⟨749759, by rfl⟩ : syracuseStep 3998717 = 1499519) (by norm_num)
theorem B2106373 : Blo 1871637 2106373 := bbase (se 4 (by rfl) ⟨197472, by rfl⟩ : syracuseStep 2106373 = 394945) (by norm_num)
theorem B3556381 : Blo 1871637 3556381 := bbase (se 3 (by rfl) ⟨666821, by rfl⟩ : syracuseStep 3556381 = 1333643) (by norm_num)
theorem B1999909 : Blo 1871637 1999909 := bbase (se 4 (by rfl) ⟨187491, by rfl⟩ : syracuseStep 1999909 = 374983) (by norm_num)
theorem B2106409 : Blo 1871637 2106409 := bbase (se 2 (by rfl) ⟨789903, by rfl⟩ : syracuseStep 2106409 = 1579807) (by norm_num)
theorem B4211765 : Blo 1871637 4211765 := bbase (se 5 (by rfl) ⟨197426, by rfl⟩ : syracuseStep 4211765 = 394853) (by norm_num)
theorem B2106445 : Blo 1871637 2106445 := bbase (se 3 (by rfl) ⟨394958, by rfl⟩ : syracuseStep 2106445 = 789917) (by norm_num)
theorem B2106481 : Blo 1871637 2106481 := bbase (se 2 (by rfl) ⟨789930, by rfl⟩ : syracuseStep 2106481 = 1579861) (by norm_num)
theorem B4211837 : Blo 1871637 4211837 := bbase (se 3 (by rfl) ⟨789719, by rfl⟩ : syracuseStep 4211837 = 1579439) (by norm_num)
theorem B6317189 : Blo 1871637 6317189 := bbase (se 4 (by rfl) ⟨592236, by rfl⟩ : syracuseStep 6317189 = 1184473) (by norm_num)
theorem B2106517 : Blo 1871637 2106517 := bbase (se 6 (by rfl) ⟨49371, by rfl⟩ : syracuseStep 2106517 = 98743) (by norm_num)
theorem B2106553 : Blo 1871637 2106553 := bbase (se 2 (by rfl) ⟨789957, by rfl⟩ : syracuseStep 2106553 = 1579915) (by norm_num)
theorem B3556541 : Blo 1871637 3556541 := bbase (se 3 (by rfl) ⟨666851, by rfl⟩ : syracuseStep 3556541 = 1333703) (by norm_num)
theorem B4211909 : Blo 1871637 4211909 := bbase (se 4 (by rfl) ⟨394866, by rfl⟩ : syracuseStep 4211909 = 789733) (by norm_num)
theorem B2000089 : Blo 1871637 2000089 := bbase (se 2 (by rfl) ⟨750033, by rfl⟩ : syracuseStep 2000089 = 1500067) (by norm_num)
theorem B2106589 : Blo 1871637 2106589 := bbase (se 3 (by rfl) ⟨394985, by rfl⟩ : syracuseStep 2106589 = 789971) (by norm_num)
theorem B2106625 : Blo 1871637 2106625 := bbase (se 2 (by rfl) ⟨789984, by rfl⟩ : syracuseStep 2106625 = 1579969) (by norm_num)
theorem B9479429 : Blo 1871637 9479429 := bbase (se 4 (by rfl) ⟨888696, by rfl⟩ : syracuseStep 9479429 = 1777393) (by norm_num)
theorem B4211981 : Blo 1871637 4211981 := bbase (se 3 (by rfl) ⟨789746, by rfl⟩ : syracuseStep 4211981 = 1579493) (by norm_num)
theorem B4269341 : Blo 1871637 4269341 := bbase (se 3 (by rfl) ⟨800501, by rfl⟩ : syracuseStep 4269341 = 1601003) (by norm_num)
theorem B2106661 : Blo 1871637 2106661 := bbase (se 4 (by rfl) ⟨197499, by rfl⟩ : syracuseStep 2106661 = 394999) (by norm_num)
theorem B2106697 : Blo 1871637 2106697 := bbase (se 2 (by rfl) ⟨790011, by rfl⟩ : syracuseStep 2106697 = 1580023) (by norm_num)
theorem B3556685 : Blo 1871637 3556685 := bbase (se 3 (by rfl) ⟨666878, by rfl⟩ : syracuseStep 3556685 = 1333757) (by norm_num)
theorem B4212053 : Blo 1871637 4212053 := bbase (se 12 (by rfl) ⟨1542, by rfl⟩ : syracuseStep 4212053 = 3085) (by norm_num)
theorem B2368865 : Blo 1871637 2368865 := bbase (se 2 (by rfl) ⟨888324, by rfl⟩ : syracuseStep 2368865 = 1776649) (by norm_num)
theorem B2106733 : Blo 1871637 2106733 := bbase (se 3 (by rfl) ⟨395012, by rfl⟩ : syracuseStep 2106733 = 790025) (by norm_num)
theorem B2106769 : Blo 1871637 2106769 := bbase (se 2 (by rfl) ⟨790038, by rfl⟩ : syracuseStep 2106769 = 1580077) (by norm_num)
theorem B2368921 : Blo 1871637 2368921 := bbase (se 2 (by rfl) ⟨888345, by rfl⟩ : syracuseStep 2368921 = 1776691) (by norm_num)
theorem B4212125 : Blo 1871637 4212125 := bbase (se 3 (by rfl) ⟨789773, by rfl⟩ : syracuseStep 4212125 = 1579547) (by norm_num)
theorem B2106805 : Blo 1871637 2106805 := bbase (se 5 (by rfl) ⟨98756, by rfl⟩ : syracuseStep 2106805 = 197513) (by norm_num)
theorem B2106841 : Blo 1871637 2106841 := bbase (se 2 (by rfl) ⟨790065, by rfl⟩ : syracuseStep 2106841 = 1580131) (by norm_num)
theorem B4212197 : Blo 1871637 4212197 := bbase (se 4 (by rfl) ⟨394893, by rfl⟩ : syracuseStep 4212197 = 789787) (by norm_num)
theorem B2369017 : Blo 1871637 2369017 := bbase (se 2 (by rfl) ⟨888381, by rfl⟩ : syracuseStep 2369017 = 1776763) (by norm_num)
theorem B2106877 : Blo 1871637 2106877 := bbase (se 3 (by rfl) ⟨395039, by rfl⟩ : syracuseStep 2106877 = 790079) (by norm_num)
theorem B2106913 : Blo 1871637 2106913 := bbase (se 2 (by rfl) ⟨790092, by rfl⟩ : syracuseStep 2106913 = 1580185) (by norm_num)
theorem B4212269 : Blo 1871637 4212269 := bbase (se 3 (by rfl) ⟨789800, by rfl⟩ : syracuseStep 4212269 = 1579601) (by norm_num)
theorem B6317621 : Blo 1871637 6317621 := bbase (se 5 (by rfl) ⟨296138, by rfl⟩ : syracuseStep 6317621 = 592277) (by norm_num)
theorem B7112245 : Blo 1871637 7112245 := bbase (se 5 (by rfl) ⟨333386, by rfl⟩ : syracuseStep 7112245 = 666773) (by norm_num)
theorem B2106949 : Blo 1871637 2106949 := bbase (se 4 (by rfl) ⟨197526, by rfl⟩ : syracuseStep 2106949 = 395053) (by norm_num)
theorem B2106985 : Blo 1871637 2106985 := bbase (se 2 (by rfl) ⟨790119, by rfl⟩ : syracuseStep 2106985 = 1580239) (by norm_num)
theorem B3556973 : Blo 1871637 3556973 := bbase (se 3 (by rfl) ⟨666932, by rfl⟩ : syracuseStep 3556973 = 1333865) (by norm_num)
theorem B15992437 : Blo 1871637 15992437 := bbase (se 5 (by rfl) ⟨749645, by rfl⟩ : syracuseStep 15992437 = 1499291) (by norm_num)
theorem B4212341 : Blo 1871637 4212341 := bbase (se 5 (by rfl) ⟨197453, by rfl⟩ : syracuseStep 4212341 = 394907) (by norm_num)
theorem B2107021 : Blo 1871637 2107021 := bbase (se 3 (by rfl) ⟨395066, by rfl⟩ : syracuseStep 2107021 = 790133) (by norm_num)
theorem B2000533 : Blo 1871637 2000533 := bbase (se 6 (by rfl) ⟨46887, by rfl⟩ : syracuseStep 2000533 = 93775) (by norm_num)
theorem B2369189 : Blo 1871637 2369189 := bbase (se 4 (by rfl) ⟨222111, by rfl⟩ : syracuseStep 2369189 = 444223) (by norm_num)
theorem B2107057 : Blo 1871637 2107057 := bbase (se 2 (by rfl) ⟨790146, by rfl⟩ : syracuseStep 2107057 = 1580293) (by norm_num)
theorem B4212413 : Blo 1871637 4212413 := bbase (se 3 (by rfl) ⟨789827, by rfl⟩ : syracuseStep 4212413 = 1579655) (by norm_num)
theorem B30361301 : Blo 1871637 30361301 := bbase (se 7 (by rfl) ⟨355796, by rfl⟩ : syracuseStep 30361301 = 711593) (by norm_num)
theorem B2107093 : Blo 1871637 2107093 := bbase (se 7 (by rfl) ⟨24692, by rfl⟩ : syracuseStep 2107093 = 49385) (by norm_num)
theorem B2369245 : Blo 1871637 2369245 := bbase (se 3 (by rfl) ⟨444233, by rfl⟩ : syracuseStep 2369245 = 888467) (by norm_num)
theorem B3999469 : Blo 1871637 3999469 := bbase (se 3 (by rfl) ⟨749900, by rfl⟩ : syracuseStep 3999469 = 1499801) (by norm_num)
theorem B2107129 : Blo 1871637 2107129 := bbase (se 2 (by rfl) ⟨790173, by rfl⟩ : syracuseStep 2107129 = 1580347) (by norm_num)
theorem B4212485 : Blo 1871637 4212485 := bbase (se 4 (by rfl) ⟨394920, by rfl⟩ : syracuseStep 4212485 = 789841) (by norm_num)
theorem B2000657 : Blo 1871637 2000657 := bbase (se 2 (by rfl) ⟨750246, by rfl⟩ : syracuseStep 2000657 = 1500493) (by norm_num)
theorem B2107165 : Blo 1871637 2107165 := bbase (se 3 (by rfl) ⟨395093, by rfl⟩ : syracuseStep 2107165 = 790187) (by norm_num)
theorem B2369341 : Blo 1871637 2369341 := bbase (se 3 (by rfl) ⟨444251, by rfl⟩ : syracuseStep 2369341 = 888503) (by norm_num)
theorem B2107201 : Blo 1871637 2107201 := bbase (se 2 (by rfl) ⟨790200, by rfl⟩ : syracuseStep 2107201 = 1580401) (by norm_num)
theorem B4212557 : Blo 1871637 4212557 := bbase (se 3 (by rfl) ⟨789854, by rfl⟩ : syracuseStep 4212557 = 1579709) (by norm_num)
theorem B2107237 : Blo 1871637 2107237 := bbase (se 4 (by rfl) ⟨197553, by rfl⟩ : syracuseStep 2107237 = 395107) (by norm_num)
theorem B7112549 : Blo 1871637 7112549 := bbase (se 4 (by rfl) ⟨666801, by rfl⟩ : syracuseStep 7112549 = 1333603) (by norm_num)
theorem B3999613 : Blo 1871637 3999613 := bbase (se 3 (by rfl) ⟨749927, by rfl⟩ : syracuseStep 3999613 = 1499855) (by norm_num)
theorem B3000197 : Blo 1871637 3000197 := bbase (se 4 (by rfl) ⟨281268, by rfl⟩ : syracuseStep 3000197 = 562537) (by norm_num)
theorem B2107273 : Blo 1871637 2107273 := bbase (se 2 (by rfl) ⟨790227, by rfl⟩ : syracuseStep 2107273 = 1580455) (by norm_num)
theorem B4212629 : Blo 1871637 4212629 := bbase (se 6 (by rfl) ⟨98733, by rfl⟩ : syracuseStep 4212629 = 197467) (by norm_num)
theorem B2107309 : Blo 1871637 2107309 := bbase (se 3 (by rfl) ⟨395120, by rfl⟩ : syracuseStep 2107309 = 790241) (by norm_num)
theorem B2107345 : Blo 1871637 2107345 := bbase (se 2 (by rfl) ⟨790254, by rfl⟩ : syracuseStep 2107345 = 1580509) (by norm_num)
theorem B5998549 : Blo 1871637 5998549 := bbase (se 7 (by rfl) ⟨70295, by rfl⟩ : syracuseStep 5998549 = 140591) (by norm_num)
theorem B4212701 : Blo 1871637 4212701 := bbase (se 3 (by rfl) ⟨789881, by rfl⟩ : syracuseStep 4212701 = 1579763) (by norm_num)
theorem B6318053 : Blo 1871637 6318053 := bbase (se 4 (by rfl) ⟨592317, by rfl⟩ : syracuseStep 6318053 = 1184635) (by norm_num)
theorem B2369513 : Blo 1871637 2369513 := bbase (se 2 (by rfl) ⟨888567, by rfl⟩ : syracuseStep 2369513 = 1777135) (by norm_num)
theorem B2107381 : Blo 1871637 2107381 := bbase (se 5 (by rfl) ⟨98783, by rfl⟩ : syracuseStep 2107381 = 197567) (by norm_num)
theorem B3000325 : Blo 1871637 3000325 := bbase (se 4 (by rfl) ⟨281280, by rfl⟩ : syracuseStep 3000325 = 562561) (by norm_num)
theorem B6752261 : Blo 1871637 6752261 := bbase (se 4 (by rfl) ⟨633024, by rfl⟩ : syracuseStep 6752261 = 1266049) (by norm_num)
theorem B2107417 : Blo 1871637 2107417 := bbase (se 2 (by rfl) ⟨790281, by rfl⟩ : syracuseStep 2107417 = 1580563) (by norm_num)
theorem B2369569 : Blo 1871637 2369569 := bbase (se 2 (by rfl) ⟨888588, by rfl⟩ : syracuseStep 2369569 = 1777177) (by norm_num)
theorem B4212773 : Blo 1871637 4212773 := bbase (se 4 (by rfl) ⟨394947, by rfl⟩ : syracuseStep 4212773 = 789895) (by norm_num)
theorem B2107453 : Blo 1871637 2107453 := bbase (se 3 (by rfl) ⟨395147, by rfl⟩ : syracuseStep 2107453 = 790295) (by norm_num)
theorem B2107489 : Blo 1871637 2107489 := bbase (se 2 (by rfl) ⟨790308, by rfl⟩ : syracuseStep 2107489 = 1580617) (by norm_num)
theorem B5335141 : Blo 1871637 5335141 := bbase (se 4 (by rfl) ⟨500169, by rfl⟩ : syracuseStep 5335141 = 1000339) (by norm_num)
theorem B4212845 : Blo 1871637 4212845 := bbase (se 3 (by rfl) ⟨789908, by rfl⟩ : syracuseStep 4212845 = 1579817) (by norm_num)
theorem B2369665 : Blo 1871637 2369665 := bbase (se 2 (by rfl) ⟨888624, by rfl⟩ : syracuseStep 2369665 = 1777249) (by norm_num)
theorem B2107525 : Blo 1871637 2107525 := bbase (se 4 (by rfl) ⟨197580, by rfl⟩ : syracuseStep 2107525 = 395161) (by norm_num)
theorem B2107561 : Blo 1871637 2107561 := bbase (se 2 (by rfl) ⟨790335, by rfl⟩ : syracuseStep 2107561 = 1580671) (by norm_num)
theorem B4212917 : Blo 1871637 4212917 := bbase (se 5 (by rfl) ⟨197480, by rfl⟩ : syracuseStep 4212917 = 394961) (by norm_num)
theorem B2107597 : Blo 1871637 2107597 := bbase (se 3 (by rfl) ⟨395174, by rfl⟩ : syracuseStep 2107597 = 790349) (by norm_num)
theorem B2107633 : Blo 1871637 2107633 := bbase (se 2 (by rfl) ⟨790362, by rfl⟩ : syracuseStep 2107633 = 1580725) (by norm_num)
theorem B3999989 : Blo 1871637 3999989 := bbase (se 5 (by rfl) ⟨187499, by rfl⟩ : syracuseStep 3999989 = 374999) (by norm_num)
theorem B4212989 : Blo 1871637 4212989 := bbase (se 3 (by rfl) ⟨789935, by rfl⟩ : syracuseStep 4212989 = 1579871) (by norm_num)
theorem B5335301 : Blo 1871637 5335301 := bbase (se 4 (by rfl) ⟨500184, by rfl⟩ : syracuseStep 5335301 = 1000369) (by norm_num)
theorem B2107669 : Blo 1871637 2107669 := bbase (se 6 (by rfl) ⟨49398, by rfl⟩ : syracuseStep 2107669 = 98797) (by norm_num)
theorem B3795245 : Blo 1871637 3795245 := bbase (se 3 (by rfl) ⟨711608, by rfl⟩ : syracuseStep 3795245 = 1423217) (by norm_num)
theorem B2369837 : Blo 1871637 2369837 := bbase (se 3 (by rfl) ⟨444344, by rfl⟩ : syracuseStep 2369837 = 888689) (by norm_num)
theorem B2107705 : Blo 1871637 2107705 := bbase (se 2 (by rfl) ⟨790389, by rfl⟩ : syracuseStep 2107705 = 1580779) (by norm_num)
theorem B4213061 : Blo 1871637 4213061 := bbase (se 4 (by rfl) ⟨394974, by rfl⟩ : syracuseStep 4213061 = 789949) (by norm_num)
theorem B3795277 : Blo 1871637 3795277 := bbase (se 3 (by rfl) ⟨711614, by rfl⟩ : syracuseStep 3795277 = 1423229) (by norm_num)
theorem B21326165 : Blo 1871637 21326165 := bbase (se 10 (by rfl) ⟨31239, by rfl⟩ : syracuseStep 21326165 = 62479) (by norm_num)
theorem B2279773 : Blo 1871637 2279773 := bbase (se 3 (by rfl) ⟨427457, by rfl⟩ : syracuseStep 2279773 = 854915) (by norm_num)
theorem B2107741 : Blo 1871637 2107741 := bbase (se 3 (by rfl) ⟨395201, by rfl⟩ : syracuseStep 2107741 = 790403) (by norm_num)
theorem B2369893 : Blo 1871637 2369893 := bbase (se 4 (by rfl) ⟨222177, by rfl⟩ : syracuseStep 2369893 = 444355) (by norm_num)
theorem B7596389 : Blo 1871637 7596389 := bbase (se 4 (by rfl) ⟨712161, by rfl⟩ : syracuseStep 7596389 = 1424323) (by norm_num)
theorem B2107777 : Blo 1871637 2107777 := bbase (se 2 (by rfl) ⟨790416, by rfl⟩ : syracuseStep 2107777 = 1580833) (by norm_num)
theorem B4213133 : Blo 1871637 4213133 := bbase (se 3 (by rfl) ⟨789962, by rfl⟩ : syracuseStep 4213133 = 1579925) (by norm_num)
theorem B6318485 : Blo 1871637 6318485 := bbase (se 6 (by rfl) ⟨148089, by rfl⟩ : syracuseStep 6318485 = 296179) (by norm_num)
theorem B2107813 : Blo 1871637 2107813 := bbase (se 4 (by rfl) ⟨197607, by rfl⟩ : syracuseStep 2107813 = 395215) (by norm_num)
theorem B2369989 : Blo 1871637 2369989 := bbase (se 4 (by rfl) ⟨222186, by rfl⟩ : syracuseStep 2369989 = 444373) (by norm_num)
theorem B4213205 : Blo 1871637 4213205 := bbase (se 7 (by rfl) ⟨49373, by rfl⟩ : syracuseStep 4213205 = 98747) (by norm_num)
theorem B9480725 : Blo 1871637 9480725 := bbase (se 6 (by rfl) ⟨222204, by rfl⟩ : syracuseStep 9480725 = 444409) (by norm_num)
theorem B4213277 : Blo 1871637 4213277 := bbase (se 3 (by rfl) ⟨789989, by rfl⟩ : syracuseStep 4213277 = 1579979) (by norm_num)
theorem B4737629 : Blo 1871637 4737629 := bbase (se 3 (by rfl) ⟨888305, by rfl⟩ : syracuseStep 4737629 = 1776611) (by norm_num)
theorem B4213349 : Blo 1871637 4213349 := bbase (se 4 (by rfl) ⟨395001, by rfl⟩ : syracuseStep 4213349 = 790003) (by norm_num)
theorem B4000357 : Blo 1871637 4000357 := bbase (se 4 (by rfl) ⟨375033, by rfl⟩ : syracuseStep 4000357 = 750067) (by norm_num)
theorem B2370161 : Blo 1871637 2370161 := bbase (se 2 (by rfl) ⟨888810, by rfl⟩ : syracuseStep 2370161 = 1777621) (by norm_num)
theorem B2402941 : Blo 1871637 2402941 := bbase (se 3 (by rfl) ⟨450551, by rfl⟩ : syracuseStep 2402941 = 901103) (by norm_num)
theorem B2370217 : Blo 1871637 2370217 := bbase (se 2 (by rfl) ⟨888831, by rfl⟩ : syracuseStep 2370217 = 1777663) (by norm_num)
theorem B4213421 : Blo 1871637 4213421 := bbase (se 3 (by rfl) ⟨790016, by rfl⟩ : syracuseStep 4213421 = 1580033) (by norm_num)
theorem B4270781 : Blo 1871637 4270781 := bbase (se 3 (by rfl) ⟨800771, by rfl⟩ : syracuseStep 4270781 = 1601543) (by norm_num)
theorem B4213493 : Blo 1871637 4213493 := bbase (se 5 (by rfl) ⟨197507, by rfl⟩ : syracuseStep 4213493 = 395015) (by norm_num)
theorem B2370313 : Blo 1871637 2370313 := bbase (se 2 (by rfl) ⟨888867, by rfl⟩ : syracuseStep 2370313 = 1777735) (by norm_num)
theorem B4213565 : Blo 1871637 4213565 := bbase (se 3 (by rfl) ⟨790043, by rfl⟩ : syracuseStep 4213565 = 1580087) (by norm_num)
theorem B6318917 : Blo 1871637 6318917 := bbase (se 4 (by rfl) ⟨592398, by rfl⟩ : syracuseStep 6318917 = 1184797) (by norm_num)
theorem B4213637 : Blo 1871637 4213637 := bbase (se 4 (by rfl) ⟨395028, by rfl⟩ : syracuseStep 4213637 = 790057) (by norm_num)
theorem B4737973 : Blo 1871637 4737973 := bbase (se 5 (by rfl) ⟨222092, by rfl⟩ : syracuseStep 4737973 = 444185) (by norm_num)
theorem B2370485 : Blo 1871637 2370485 := bbase (se 5 (by rfl) ⟨111116, by rfl⟩ : syracuseStep 2370485 = 222233) (by norm_num)
theorem B4213709 : Blo 1871637 4213709 := bbase (se 3 (by rfl) ⟨790070, by rfl⟩ : syracuseStep 4213709 = 1580141) (by norm_num)
theorem B68324309 : Blo 1871637 68324309 := bbase (se 7 (by rfl) ⟨800675, by rfl⟩ : syracuseStep 68324309 = 1601351) (by norm_num)
theorem B2370541 : Blo 1871637 2370541 := bbase (se 3 (by rfl) ⟨444476, by rfl⟩ : syracuseStep 2370541 = 888953) (by norm_num)
theorem B4271093 : Blo 1871637 4271093 := bbase (se 5 (by rfl) ⟨200207, by rfl⟩ : syracuseStep 4271093 = 400415) (by norm_num)
theorem B4213781 : Blo 1871637 4213781 := bbase (se 6 (by rfl) ⟨98760, by rfl⟩ : syracuseStep 4213781 = 197521) (by norm_num)
theorem B4738085 : Blo 1871637 4738085 := bbase (se 4 (by rfl) ⟨444195, by rfl⟩ : syracuseStep 4738085 = 888391) (by norm_num)
theorem B2370637 : Blo 1871637 2370637 := bbase (se 3 (by rfl) ⟨444494, by rfl⟩ : syracuseStep 2370637 = 888989) (by norm_num)
theorem B4213853 : Blo 1871637 4213853 := bbase (se 3 (by rfl) ⟨790097, by rfl⟩ : syracuseStep 4213853 = 1580195) (by norm_num)
theorem B7588981 : Blo 1871637 7588981 := bbase (se 5 (by rfl) ⟨355733, by rfl⟩ : syracuseStep 7588981 = 711467) (by norm_num)
theorem B8998037 : Blo 1871637 8998037 := bbase (se 6 (by rfl) ⟨210891, by rfl⟩ : syracuseStep 8998037 = 421783) (by norm_num)
theorem B4213925 : Blo 1871637 4213925 := bbase (se 4 (by rfl) ⟨395055, by rfl⟩ : syracuseStep 4213925 = 790111) (by norm_num)
theorem B15191221 : Blo 1871637 15191221 := bbase (se 5 (by rfl) ⟨712088, by rfl⟩ : syracuseStep 15191221 = 1424177) (by norm_num)
theorem B2845885 : Blo 1871637 2845885 := bbase (se 3 (by rfl) ⟨533603, by rfl⟩ : syracuseStep 2845885 = 1067207) (by norm_num)
theorem B4738277 : Blo 1871637 4738277 := bbase (se 4 (by rfl) ⟨444213, by rfl⟩ : syracuseStep 4738277 = 888427) (by norm_num)
theorem B4213997 : Blo 1871637 4213997 := bbase (se 3 (by rfl) ⟨790124, by rfl⟩ : syracuseStep 4213997 = 1580249) (by norm_num)
theorem B6319349 : Blo 1871637 6319349 := bbase (se 5 (by rfl) ⟨296219, by rfl⟩ : syracuseStep 6319349 = 592439) (by norm_num)
theorem B2370809 : Blo 1871637 2370809 := bbase (se 2 (by rfl) ⟨889053, by rfl⟩ : syracuseStep 2370809 = 1778107) (by norm_num)
theorem B2370865 : Blo 1871637 2370865 := bbase (se 2 (by rfl) ⟨889074, by rfl⟩ : syracuseStep 2370865 = 1778149) (by norm_num)
theorem B8539445 : Blo 1871637 8539445 := bbase (se 5 (by rfl) ⟨400286, by rfl⟩ : syracuseStep 8539445 = 800573) (by norm_num)
theorem B4214069 : Blo 1871637 4214069 := bbase (se 5 (by rfl) ⟨197534, by rfl⟩ : syracuseStep 4214069 = 395069) (by norm_num)
theorem B4214141 : Blo 1871637 4214141 := bbase (se 3 (by rfl) ⟨790151, by rfl⟩ : syracuseStep 4214141 = 1580303) (by norm_num)
theorem B2370961 : Blo 1871637 2370961 := bbase (se 2 (by rfl) ⟨889110, by rfl⟩ : syracuseStep 2370961 = 1778221) (by norm_num)
theorem B2665885 : Blo 1871637 2665885 := bbase (se 3 (by rfl) ⟨499853, by rfl⟩ : syracuseStep 2665885 = 999707) (by norm_num)
theorem B4214213 : Blo 1871637 4214213 := bbase (se 4 (by rfl) ⟨395082, by rfl⟩ : syracuseStep 4214213 = 790165) (by norm_num)
theorem B4500949 : Blo 1871637 4500949 := bbase (se 7 (by rfl) ⟨52745, by rfl⟩ : syracuseStep 4500949 = 105491) (by norm_num)
theorem B3796445 : Blo 1871637 3796445 := bbase (se 3 (by rfl) ⟨711833, by rfl⟩ : syracuseStep 3796445 = 1423667) (by norm_num)
theorem B4271621 : Blo 1871637 4271621 := bbase (se 4 (by rfl) ⟨400464, by rfl⟩ : syracuseStep 4271621 = 800929) (by norm_num)
theorem B4214285 : Blo 1871637 4214285 := bbase (se 3 (by rfl) ⟨790178, by rfl⟩ : syracuseStep 4214285 = 1580357) (by norm_num)
theorem B15994421 : Blo 1871637 15994421 := bbase (se 5 (by rfl) ⟨749738, by rfl⟩ : syracuseStep 15994421 = 1499477) (by norm_num)
theorem B4738621 : Blo 1871637 4738621 := bbase (se 3 (by rfl) ⟨888491, by rfl⟩ : syracuseStep 4738621 = 1776983) (by norm_num)
theorem B2371133 : Blo 1871637 2371133 := bbase (se 3 (by rfl) ⟨444587, by rfl⟩ : syracuseStep 2371133 = 889175) (by norm_num)
theorem B4214357 : Blo 1871637 4214357 := bbase (se 8 (by rfl) ⟨24693, by rfl⟩ : syracuseStep 4214357 = 49387) (by norm_num)
theorem B13504117 : Blo 1871637 13504117 := bbase (se 5 (by rfl) ⟨633005, by rfl⟩ : syracuseStep 13504117 = 1266011) (by norm_num)
theorem B2371189 : Blo 1871637 2371189 := bbase (se 5 (by rfl) ⟨111149, by rfl⟩ : syracuseStep 2371189 = 222299) (by norm_num)
theorem B4214429 : Blo 1871637 4214429 := bbase (se 3 (by rfl) ⟨790205, by rfl⟩ : syracuseStep 4214429 = 1580411) (by norm_num)
theorem B6319781 : Blo 1871637 6319781 := bbase (se 4 (by rfl) ⟨592479, by rfl⟩ : syracuseStep 6319781 = 1184959) (by norm_num)
theorem B4738733 : Blo 1871637 4738733 := bbase (se 3 (by rfl) ⟨888512, by rfl⟩ : syracuseStep 4738733 = 1777025) (by norm_num)
theorem B2371285 : Blo 1871637 2371285 := bbase (se 7 (by rfl) ⟨27788, by rfl⟩ : syracuseStep 2371285 = 55577) (by norm_num)
theorem B4214501 : Blo 1871637 4214501 := bbase (se 4 (by rfl) ⟨395109, by rfl⟩ : syracuseStep 4214501 = 790219) (by norm_num)
theorem B9482021 : Blo 1871637 9482021 := bbase (se 4 (by rfl) ⟨888939, by rfl⟩ : syracuseStep 9482021 = 1777879) (by norm_num)
theorem B4214573 : Blo 1871637 4214573 := bbase (se 3 (by rfl) ⟨790232, by rfl⟩ : syracuseStep 4214573 = 1580465) (by norm_num)
theorem B4501325 : Blo 1871637 4501325 := bbase (se 3 (by rfl) ⟨843998, by rfl⟩ : syracuseStep 4501325 = 1687997) (by norm_num)
theorem B2846549 : Blo 1871637 2846549 := bbase (se 9 (by rfl) ⟨8339, by rfl⟩ : syracuseStep 2846549 = 16679) (by norm_num)
theorem B4738925 : Blo 1871637 4738925 := bbase (se 3 (by rfl) ⟨888548, by rfl⟩ : syracuseStep 4738925 = 1777097) (by norm_num)
theorem B4214645 : Blo 1871637 4214645 := bbase (se 5 (by rfl) ⟨197561, by rfl⟩ : syracuseStep 4214645 = 395123) (by norm_num)
theorem B4214717 : Blo 1871637 4214717 := bbase (se 3 (by rfl) ⟨790259, by rfl⟩ : syracuseStep 4214717 = 1580519) (by norm_num)
theorem B2666477 : Blo 1871637 2666477 := bbase (se 3 (by rfl) ⟨499964, by rfl⟩ : syracuseStep 2666477 = 999929) (by norm_num)
theorem B4214789 : Blo 1871637 4214789 := bbase (se 4 (by rfl) ⟨395136, by rfl⟩ : syracuseStep 4214789 = 790273) (by norm_num)
theorem B2846749 : Blo 1871637 2846749 := bbase (se 3 (by rfl) ⟨533765, by rfl⟩ : syracuseStep 2846749 = 1067531) (by norm_num)
theorem B2666557 : Blo 1871637 2666557 := bbase (se 3 (by rfl) ⟨499979, by rfl⟩ : syracuseStep 2666557 = 999959) (by norm_num)
theorem B4214861 : Blo 1871637 4214861 := bbase (se 3 (by rfl) ⟨790286, by rfl⟩ : syracuseStep 4214861 = 1580573) (by norm_num)
theorem B6320213 : Blo 1871637 6320213 := bbase (se 8 (by rfl) ⟨37032, by rfl⟩ : syracuseStep 6320213 = 74065) (by norm_num)
theorem B2248817 : Blo 1871637 2248817 := bbase (se 2 (by rfl) ⟨843306, by rfl⟩ : syracuseStep 2248817 = 1686613) (by norm_num)
theorem B2248841 : Blo 1871637 2248841 := bbase (se 2 (by rfl) ⟨843315, by rfl⟩ : syracuseStep 2248841 = 1686631) (by norm_num)
theorem B4214933 : Blo 1871637 4214933 := bbase (se 6 (by rfl) ⟨98787, by rfl⟩ : syracuseStep 4214933 = 197575) (by norm_num)
theorem B2666677 : Blo 1871637 2666677 := bbase (se 5 (by rfl) ⟨125000, by rfl⟩ : syracuseStep 2666677 = 250001) (by norm_num)
theorem B4739269 : Blo 1871637 4739269 := bbase (se 4 (by rfl) ⟨444306, by rfl⟩ : syracuseStep 4739269 = 888613) (by norm_num)
theorem B4215005 : Blo 1871637 4215005 := bbase (se 3 (by rfl) ⟨790313, by rfl⟩ : syracuseStep 4215005 = 1580627) (by norm_num)
theorem B4501757 : Blo 1871637 4501757 := bbase (se 3 (by rfl) ⟨844079, by rfl⟩ : syracuseStep 4501757 = 1688159) (by norm_num)
theorem B2666773 : Blo 1871637 2666773 := bbase (se 6 (by rfl) ⟨62502, by rfl⟩ : syracuseStep 2666773 = 125005) (by norm_num)
theorem B4215077 : Blo 1871637 4215077 := bbase (se 4 (by rfl) ⟨395163, by rfl⟩ : syracuseStep 4215077 = 790327) (by norm_num)
theorem B4509997 : Blo 1871637 4509997 := bbase (se 3 (by rfl) ⟨845624, by rfl⟩ : syracuseStep 4509997 = 1691249) (by norm_num)
theorem B4739381 : Blo 1871637 4739381 := bbase (se 5 (by rfl) ⟨222158, by rfl⟩ : syracuseStep 4739381 = 444317) (by norm_num)
theorem B7106885 : Blo 1871637 7106885 := bbase (se 4 (by rfl) ⟨666270, by rfl⟩ : syracuseStep 7106885 = 1332541) (by norm_num)
theorem B4215149 : Blo 1871637 4215149 := bbase (se 3 (by rfl) ⟨790340, by rfl⟩ : syracuseStep 4215149 = 1580681) (by norm_num)
theorem B3158453 : Blo 1871637 3158453 := bbase (se 5 (by rfl) ⟨148052, by rfl⟩ : syracuseStep 3158453 = 296105) (by norm_num)
theorem B4215221 : Blo 1871637 4215221 := bbase (se 5 (by rfl) ⟨197588, by rfl⟩ : syracuseStep 4215221 = 395177) (by norm_num)
theorem B2249149 : Blo 1871637 2249149 := bbase (se 3 (by rfl) ⟨421715, by rfl⟩ : syracuseStep 2249149 = 843431) (by norm_num)
theorem B4739573 : Blo 1871637 4739573 := bbase (se 5 (by rfl) ⟨222167, by rfl⟩ : syracuseStep 4739573 = 444335) (by norm_num)
theorem B4215293 : Blo 1871637 4215293 := bbase (se 3 (by rfl) ⟨790367, by rfl⟩ : syracuseStep 4215293 = 1580735) (by norm_num)
theorem B6320645 : Blo 1871637 6320645 := bbase (se 4 (by rfl) ⟨592560, by rfl⟩ : syracuseStep 6320645 = 1185121) (by norm_num)
theorem B5403173 : Blo 1871637 5403173 := bbase (se 4 (by rfl) ⟨506547, by rfl⟩ : syracuseStep 5403173 = 1013095) (by norm_num)
theorem B3158581 : Blo 1871637 3158581 := bbase (se 5 (by rfl) ⟨148058, by rfl⟩ : syracuseStep 3158581 = 296117) (by norm_num)
theorem B4215365 : Blo 1871637 4215365 := bbase (se 4 (by rfl) ⟨395190, by rfl⟩ : syracuseStep 4215365 = 790381) (by norm_num)
theorem B7107173 : Blo 1871637 7107173 := bbase (se 4 (by rfl) ⟨666297, by rfl⟩ : syracuseStep 7107173 = 1332595) (by norm_num)
theorem B2249321 : Blo 1871637 2249321 := bbase (se 2 (by rfl) ⟨843495, by rfl⟩ : syracuseStep 2249321 = 1686991) (by norm_num)
theorem B5403269 : Blo 1871637 5403269 := bbase (se 4 (by rfl) ⟨506556, by rfl⟩ : syracuseStep 5403269 = 1013113) (by norm_num)
theorem B3158669 : Blo 1871637 3158669 := bbase (se 3 (by rfl) ⟨592250, by rfl⟩ : syracuseStep 3158669 = 1184501) (by norm_num)
theorem B4215437 : Blo 1871637 4215437 := bbase (se 3 (by rfl) ⟨790394, by rfl⟩ : syracuseStep 4215437 = 1580789) (by norm_num)
theorem B4215509 : Blo 1871637 4215509 := bbase (se 7 (by rfl) ⟨49400, by rfl⟩ : syracuseStep 4215509 = 98801) (by norm_num)
theorem B2249437 : Blo 1871637 2249437 := bbase (se 3 (by rfl) ⟨421769, by rfl⟩ : syracuseStep 2249437 = 843539) (by norm_num)
theorem B2667269 : Blo 1871637 2667269 := bbase (se 4 (by rfl) ⟨250056, by rfl⟩ : syracuseStep 2667269 = 500113) (by norm_num)
theorem B3158797 : Blo 1871637 3158797 := bbase (se 3 (by rfl) ⟨592274, by rfl⟩ : syracuseStep 3158797 = 1184549) (by norm_num)
theorem B4215581 : Blo 1871637 4215581 := bbase (se 3 (by rfl) ⟨790421, by rfl⟩ : syracuseStep 4215581 = 1580843) (by norm_num)
theorem B16208693 : Blo 1871637 16208693 := bbase (se 5 (by rfl) ⟨759782, by rfl⟩ : syracuseStep 16208693 = 1519565) (by norm_num)
theorem B2249533 : Blo 1871637 2249533 := bbase (se 3 (by rfl) ⟨421787, by rfl⟩ : syracuseStep 2249533 = 843575) (by norm_num)
theorem B4739917 : Blo 1871637 4739917 := bbase (se 3 (by rfl) ⟨888734, by rfl⟩ : syracuseStep 4739917 = 1777469) (by norm_num)
theorem B3158885 : Blo 1871637 3158885 := bbase (se 4 (by rfl) ⟨296145, by rfl⟩ : syracuseStep 3158885 = 592291) (by norm_num)
theorem B4215653 : Blo 1871637 4215653 := bbase (se 4 (by rfl) ⟨395217, by rfl⟩ : syracuseStep 4215653 = 790435) (by norm_num)
theorem B18002837 : Blo 1871637 18002837 := bbase (se 6 (by rfl) ⟨421941, by rfl⟩ : syracuseStep 18002837 = 843883) (by norm_num)
theorem B6001573 : Blo 1871637 6001573 := bbase (se 4 (by rfl) ⟨562647, by rfl⟩ : syracuseStep 6001573 = 1125295) (by norm_num)
theorem B6321077 : Blo 1871637 6321077 := bbase (se 5 (by rfl) ⟨296300, by rfl⟩ : syracuseStep 6321077 = 592601) (by norm_num)
theorem B4740029 : Blo 1871637 4740029 := bbase (se 3 (by rfl) ⟨888755, by rfl⟩ : syracuseStep 4740029 = 1777511) (by norm_num)
theorem B2249677 : Blo 1871637 2249677 := bbase (se 3 (by rfl) ⟨421814, by rfl⟩ : syracuseStep 2249677 = 843629) (by norm_num)
theorem B35976149 : Blo 1871637 35976149 := bbase (se 7 (by rfl) ⟨421595, by rfl⟩ : syracuseStep 35976149 = 843191) (by norm_num)
theorem B3159013 : Blo 1871637 3159013 := bbase (se 4 (by rfl) ⟨296157, by rfl⟩ : syracuseStep 3159013 = 592315) (by norm_num)
theorem B5329925 : Blo 1871637 5329925 := bbase (se 4 (by rfl) ⟨499680, by rfl⟩ : syracuseStep 5329925 = 999361) (by norm_num)
theorem B9483317 : Blo 1871637 9483317 := bbase (se 5 (by rfl) ⟨444530, by rfl⟩ : syracuseStep 9483317 = 889061) (by norm_num)
theorem B3159101 : Blo 1871637 3159101 := bbase (se 3 (by rfl) ⟨592331, by rfl⟩ : syracuseStep 3159101 = 1184663) (by norm_num)
theorem B1897573 : Blo 1871637 1897573 := bbase (se 4 (by rfl) ⟨177897, by rfl⟩ : syracuseStep 1897573 = 355795) (by norm_num)
theorem B2135153 : Blo 1871637 2135153 := bbase (se 2 (by rfl) ⟨800682, by rfl⟩ : syracuseStep 2135153 = 1601365) (by norm_num)
theorem B4871285 : Blo 1871637 4871285 := bbase (se 5 (by rfl) ⟨228341, by rfl⟩ : syracuseStep 4871285 = 456683) (by norm_num)
theorem B4740221 : Blo 1871637 4740221 := bbase (se 3 (by rfl) ⟨888791, by rfl⟩ : syracuseStep 4740221 = 1777583) (by norm_num)
theorem B3159229 : Blo 1871637 3159229 := bbase (se 3 (by rfl) ⟨592355, by rfl⟩ : syracuseStep 3159229 = 1184711) (by norm_num)
theorem B8541397 : Blo 1871637 8541397 := bbase (se 7 (by rfl) ⟨100094, by rfl⟩ : syracuseStep 8541397 = 200189) (by norm_num)
theorem B14226677 : Blo 1871637 14226677 := bbase (se 5 (by rfl) ⟨666875, by rfl⟩ : syracuseStep 14226677 = 1333751) (by norm_num)
theorem B3159317 : Blo 1871637 3159317 := bbase (se 6 (by rfl) ⟨74046, by rfl⟩ : syracuseStep 3159317 = 148093) (by norm_num)
theorem B6321509 : Blo 1871637 6321509 := bbase (se 4 (by rfl) ⟨592641, by rfl⟩ : syracuseStep 6321509 = 1185283) (by norm_num)
theorem B3159445 : Blo 1871637 3159445 := bbase (se 6 (by rfl) ⟨74049, by rfl⟩ : syracuseStep 3159445 = 148099) (by norm_num)
theorem B5330357 : Blo 1871637 5330357 := bbase (se 5 (by rfl) ⟨249860, by rfl⟩ : syracuseStep 5330357 = 499721) (by norm_num)
theorem B9475541 : Blo 1871637 9475541 := bbase (se 7 (by rfl) ⟨111041, by rfl⟩ : syracuseStep 9475541 = 222083) (by norm_num)
theorem B4740565 : Blo 1871637 4740565 := bbase (se 7 (by rfl) ⟨55553, by rfl⟩ : syracuseStep 4740565 = 111107) (by norm_num)
theorem B3159533 : Blo 1871637 3159533 := bbase (se 3 (by rfl) ⟨592412, by rfl⟩ : syracuseStep 3159533 = 1184825) (by norm_num)
theorem B4740677 : Blo 1871637 4740677 := bbase (se 4 (by rfl) ⟨444438, by rfl⟩ : syracuseStep 4740677 = 888877) (by norm_num)
theorem B8001125 : Blo 1871637 8001125 := bbase (se 4 (by rfl) ⟨750105, by rfl⟩ : syracuseStep 8001125 = 1500211) (by norm_num)
theorem B3159661 : Blo 1871637 3159661 := bbase (se 3 (by rfl) ⟨592436, by rfl⟩ : syracuseStep 3159661 = 1184873) (by norm_num)
theorem B1898101 : Blo 1871637 1898101 := bbase (se 5 (by rfl) ⟨88973, by rfl⟩ : syracuseStep 1898101 = 177947) (by norm_num)
theorem B14218901 : Blo 1871637 14218901 := bbase (se 6 (by rfl) ⟨333255, by rfl⟩ : syracuseStep 14218901 = 666511) (by norm_num)
theorem B2807477 : Blo 1871637 2807477 := bbase (se 5 (by rfl) ⟨131600, by rfl⟩ : syracuseStep 2807477 = 263201) (by norm_num)
theorem B1898173 : Blo 1871637 1898173 := bbase (se 3 (by rfl) ⟨355907, by rfl⟩ : syracuseStep 1898173 = 711815) (by norm_num)
theorem B3159749 : Blo 1871637 3159749 := bbase (se 4 (by rfl) ⟨296226, by rfl⟩ : syracuseStep 3159749 = 592453) (by norm_num)
theorem B2807501 : Blo 1871637 2807501 := bbase (se 3 (by rfl) ⟨526406, by rfl⟩ : syracuseStep 2807501 = 1052813) (by norm_num)
theorem B1898189 : Blo 1871637 1898189 := bbase (se 3 (by rfl) ⟨355910, by rfl⟩ : syracuseStep 1898189 = 711821) (by norm_num)
theorem B2807525 : Blo 1871637 2807525 := bbase (se 4 (by rfl) ⟨263205, by rfl⟩ : syracuseStep 2807525 = 526411) (by norm_num)
theorem B4806373 : Blo 1871637 4806373 := bbase (se 4 (by rfl) ⟨450597, by rfl⟩ : syracuseStep 4806373 = 901195) (by norm_num)
theorem B2807549 : Blo 1871637 2807549 := bbase (se 3 (by rfl) ⟨526415, by rfl⟩ : syracuseStep 2807549 = 1052831) (by norm_num)
theorem B7108357 : Blo 1871637 7108357 := bbase (se 4 (by rfl) ⟨666408, by rfl⟩ : syracuseStep 7108357 = 1332817) (by norm_num)
theorem B4740869 : Blo 1871637 4740869 := bbase (se 4 (by rfl) ⟨444456, by rfl⟩ : syracuseStep 4740869 = 888913) (by norm_num)
theorem B2807573 : Blo 1871637 2807573 := bbase (se 6 (by rfl) ⟨65802, by rfl⟩ : syracuseStep 2807573 = 131605) (by norm_num)
theorem B6321941 : Blo 1871637 6321941 := bbase (se 6 (by rfl) ⟨148170, by rfl⟩ : syracuseStep 6321941 = 296341) (by norm_num)
theorem B2807597 : Blo 1871637 2807597 := bbase (se 3 (by rfl) ⟨526424, by rfl⟩ : syracuseStep 2807597 = 1052849) (by norm_num)
theorem B2807621 : Blo 1871637 2807621 := bbase (se 4 (by rfl) ⟨263214, by rfl⟩ : syracuseStep 2807621 = 526429) (by norm_num)
theorem B3159877 : Blo 1871637 3159877 := bbase (se 4 (by rfl) ⟨296238, by rfl⟩ : syracuseStep 3159877 = 592477) (by norm_num)
theorem B2807645 : Blo 1871637 2807645 := bbase (se 3 (by rfl) ⟨526433, by rfl⟩ : syracuseStep 2807645 = 1052867) (by norm_num)
theorem B2807669 : Blo 1871637 2807669 := bbase (se 5 (by rfl) ⟨131609, by rfl⟩ : syracuseStep 2807669 = 263219) (by norm_num)
theorem B9000821 : Blo 1871637 9000821 := bbase (se 5 (by rfl) ⟨421913, by rfl⟩ : syracuseStep 9000821 = 843827) (by norm_num)
theorem B8001413 : Blo 1871637 8001413 := bbase (se 4 (by rfl) ⟨750132, by rfl⟩ : syracuseStep 8001413 = 1500265) (by norm_num)
theorem B2807693 : Blo 1871637 2807693 := bbase (se 3 (by rfl) ⟨526442, by rfl⟩ : syracuseStep 2807693 = 1052885) (by norm_num)
theorem B10123157 : Blo 1871637 10123157 := bbase (se 6 (by rfl) ⟨237261, by rfl⟩ : syracuseStep 10123157 = 474523) (by norm_num)
theorem B3602333 : Blo 1871637 3602333 := bbase (se 3 (by rfl) ⟨675437, by rfl⟩ : syracuseStep 3602333 = 1350875) (by norm_num)
theorem B3159965 : Blo 1871637 3159965 := bbase (se 3 (by rfl) ⟨592493, by rfl⟩ : syracuseStep 3159965 = 1184987) (by norm_num)
theorem B2807717 : Blo 1871637 2807717 := bbase (se 4 (by rfl) ⟨263223, by rfl⟩ : syracuseStep 2807717 = 526447) (by norm_num)
theorem B1898417 : Blo 1871637 1898417 := bbase (se 2 (by rfl) ⟨711906, by rfl⟩ : syracuseStep 1898417 = 1423813) (by norm_num)
theorem B2807741 : Blo 1871637 2807741 := bbase (se 3 (by rfl) ⟨526451, by rfl⟩ : syracuseStep 2807741 = 1052903) (by norm_num)
theorem B3553237 : Blo 1871637 3553237 := bbase (se 7 (by rfl) ⟨41639, by rfl⟩ : syracuseStep 3553237 = 83279) (by norm_num)
theorem B2807765 : Blo 1871637 2807765 := bbase (se 7 (by rfl) ⟨32903, by rfl⟩ : syracuseStep 2807765 = 65807) (by norm_num)
theorem B2807789 : Blo 1871637 2807789 := bbase (se 3 (by rfl) ⟨526460, by rfl⟩ : syracuseStep 2807789 = 1052921) (by norm_num)
theorem B2807813 : Blo 1871637 2807813 := bbase (se 4 (by rfl) ⟨263232, by rfl⟩ : syracuseStep 2807813 = 526465) (by norm_num)
theorem B2807837 : Blo 1871637 2807837 := bbase (se 3 (by rfl) ⟨526469, by rfl⟩ : syracuseStep 2807837 = 1052939) (by norm_num)
theorem B3160093 : Blo 1871637 3160093 := bbase (se 3 (by rfl) ⟨592517, by rfl⟩ : syracuseStep 3160093 = 1185035) (by norm_num)
theorem B2807861 : Blo 1871637 2807861 := bbase (se 5 (by rfl) ⟨131618, by rfl⟩ : syracuseStep 2807861 = 263237) (by norm_num)
theorem B7108661 : Blo 1871637 7108661 := bbase (se 5 (by rfl) ⟨333218, by rfl⟩ : syracuseStep 7108661 = 666437) (by norm_num)
theorem B2807885 : Blo 1871637 2807885 := bbase (se 3 (by rfl) ⟨526478, by rfl⟩ : syracuseStep 2807885 = 1052957) (by norm_num)
theorem B4741213 : Blo 1871637 4741213 := bbase (se 3 (by rfl) ⟨888977, by rfl⟩ : syracuseStep 4741213 = 1777955) (by norm_num)
theorem B2807909 : Blo 1871637 2807909 := bbase (se 4 (by rfl) ⟨263241, by rfl⟩ : syracuseStep 2807909 = 526483) (by norm_num)
theorem B3160181 : Blo 1871637 3160181 := bbase (se 5 (by rfl) ⟨148133, by rfl⟩ : syracuseStep 3160181 = 296267) (by norm_num)
theorem B2807933 : Blo 1871637 2807933 := bbase (se 3 (by rfl) ⟨526487, by rfl⟩ : syracuseStep 2807933 = 1052975) (by norm_num)
theorem B2807957 : Blo 1871637 2807957 := bbase (se 6 (by rfl) ⟨65811, by rfl⟩ : syracuseStep 2807957 = 131623) (by norm_num)
theorem B5331109 : Blo 1871637 5331109 := bbase (se 4 (by rfl) ⟨499791, by rfl⟩ : syracuseStep 5331109 = 999583) (by norm_num)
theorem B2807981 : Blo 1871637 2807981 := bbase (se 3 (by rfl) ⟨526496, by rfl⟩ : syracuseStep 2807981 = 1052993) (by norm_num)
theorem B1898677 : Blo 1871637 1898677 := bbase (se 5 (by rfl) ⟨89000, by rfl⟩ : syracuseStep 1898677 = 178001) (by norm_num)
theorem B2808005 : Blo 1871637 2808005 := bbase (se 4 (by rfl) ⟨263250, by rfl⟩ : syracuseStep 2808005 = 526501) (by norm_num)
theorem B6322373 : Blo 1871637 6322373 := bbase (se 4 (by rfl) ⟨592722, by rfl⟩ : syracuseStep 6322373 = 1185445) (by norm_num)
theorem B4741325 : Blo 1871637 4741325 := bbase (se 3 (by rfl) ⟨888998, by rfl⟩ : syracuseStep 4741325 = 1777997) (by norm_num)
theorem B8222933 : Blo 1871637 8222933 := bbase (se 7 (by rfl) ⟨96362, by rfl⟩ : syracuseStep 8222933 = 192725) (by norm_num)
theorem B2808029 : Blo 1871637 2808029 := bbase (se 3 (by rfl) ⟨526505, by rfl⟩ : syracuseStep 2808029 = 1053011) (by norm_num)
theorem B2808053 : Blo 1871637 2808053 := bbase (se 5 (by rfl) ⟨131627, by rfl⟩ : syracuseStep 2808053 = 263255) (by norm_num)
theorem B3160309 : Blo 1871637 3160309 := bbase (se 5 (by rfl) ⟨148139, by rfl⟩ : syracuseStep 3160309 = 296279) (by norm_num)
theorem B3553541 : Blo 1871637 3553541 := bbase (se 4 (by rfl) ⟨333144, by rfl⟩ : syracuseStep 3553541 = 666289) (by norm_num)
theorem B2808077 : Blo 1871637 2808077 := bbase (se 3 (by rfl) ⟨526514, by rfl⟩ : syracuseStep 2808077 = 1053029) (by norm_num)
theorem B2808101 : Blo 1871637 2808101 := bbase (se 4 (by rfl) ⟨263259, by rfl⟩ : syracuseStep 2808101 = 526519) (by norm_num)
theorem B2808125 : Blo 1871637 2808125 := bbase (se 3 (by rfl) ⟨526523, by rfl⟩ : syracuseStep 2808125 = 1053047) (by norm_num)
theorem B9484613 : Blo 1871637 9484613 := bbase (se 4 (by rfl) ⟨889182, by rfl⟩ : syracuseStep 9484613 = 1778365) (by norm_num)
theorem B3160397 : Blo 1871637 3160397 := bbase (se 3 (by rfl) ⟨592574, by rfl⟩ : syracuseStep 3160397 = 1185149) (by norm_num)
theorem B2808149 : Blo 1871637 2808149 := bbase (se 10 (by rfl) ⟨4113, by rfl⟩ : syracuseStep 2808149 = 8227) (by norm_num)
theorem B2808173 : Blo 1871637 2808173 := bbase (se 3 (by rfl) ⟨526532, by rfl⟩ : syracuseStep 2808173 = 1053065) (by norm_num)
theorem B2808197 : Blo 1871637 2808197 := bbase (se 4 (by rfl) ⟨263268, by rfl⟩ : syracuseStep 2808197 = 526537) (by norm_num)
theorem B4741517 : Blo 1871637 4741517 := bbase (se 3 (by rfl) ⟨889034, by rfl⟩ : syracuseStep 4741517 = 1778069) (by norm_num)
theorem B2808221 : Blo 1871637 2808221 := bbase (se 3 (by rfl) ⟨526541, by rfl⟩ : syracuseStep 2808221 = 1053083) (by norm_num)
theorem B2808245 : Blo 1871637 2808245 := bbase (se 5 (by rfl) ⟨131636, by rfl⟩ : syracuseStep 2808245 = 263273) (by norm_num)
theorem B2808269 : Blo 1871637 2808269 := bbase (se 3 (by rfl) ⟨526550, by rfl⟩ : syracuseStep 2808269 = 1053101) (by norm_num)
theorem B3160525 : Blo 1871637 3160525 := bbase (se 3 (by rfl) ⟨592598, by rfl⟩ : syracuseStep 3160525 = 1185197) (by norm_num)
theorem B10664405 : Blo 1871637 10664405 := bbase (se 7 (by rfl) ⟨124973, by rfl⟩ : syracuseStep 10664405 = 249947) (by norm_num)
theorem B2808293 : Blo 1871637 2808293 := bbase (se 4 (by rfl) ⟨263277, by rfl⟩ : syracuseStep 2808293 = 526555) (by norm_num)
theorem B1899001 : Blo 1871637 1899001 := bbase (se 2 (by rfl) ⟨712125, by rfl⟩ : syracuseStep 1899001 = 1424251) (by norm_num)
theorem B2808317 : Blo 1871637 2808317 := bbase (se 3 (by rfl) ⟨526559, by rfl⟩ : syracuseStep 2808317 = 1053119) (by norm_num)
theorem B2808341 : Blo 1871637 2808341 := bbase (se 6 (by rfl) ⟨65820, by rfl⟩ : syracuseStep 2808341 = 131641) (by norm_num)
theorem B3160613 : Blo 1871637 3160613 := bbase (se 4 (by rfl) ⟨296307, by rfl⟩ : syracuseStep 3160613 = 592615) (by norm_num)
theorem B2808365 : Blo 1871637 2808365 := bbase (se 3 (by rfl) ⟨526568, by rfl⟩ : syracuseStep 2808365 = 1053137) (by norm_num)
theorem B10123829 : Blo 1871637 10123829 := bbase (se 5 (by rfl) ⟨474554, by rfl⟩ : syracuseStep 10123829 = 949109) (by norm_num)
theorem B2808389 : Blo 1871637 2808389 := bbase (se 4 (by rfl) ⟨263286, by rfl⟩ : syracuseStep 2808389 = 526573) (by norm_num)
theorem B2808413 : Blo 1871637 2808413 := bbase (se 3 (by rfl) ⟨526577, by rfl⟩ : syracuseStep 2808413 = 1053155) (by norm_num)
theorem B2808437 : Blo 1871637 2808437 := bbase (se 5 (by rfl) ⟨131645, by rfl⟩ : syracuseStep 2808437 = 263291) (by norm_num)
theorem B8002165 : Blo 1871637 8002165 := bbase (se 5 (by rfl) ⟨375101, by rfl⟩ : syracuseStep 8002165 = 750203) (by norm_num)
theorem B6322805 : Blo 1871637 6322805 := bbase (se 5 (by rfl) ⟨296381, by rfl⟩ : syracuseStep 6322805 = 592763) (by norm_num)
theorem B2808461 : Blo 1871637 2808461 := bbase (se 3 (by rfl) ⟨526586, by rfl⟩ : syracuseStep 2808461 = 1053173) (by norm_num)
theorem B2808485 : Blo 1871637 2808485 := bbase (se 4 (by rfl) ⟨263295, by rfl⟩ : syracuseStep 2808485 = 526591) (by norm_num)
theorem B3160741 : Blo 1871637 3160741 := bbase (se 4 (by rfl) ⟨296319, by rfl⟩ : syracuseStep 3160741 = 592639) (by norm_num)
theorem B2808509 : Blo 1871637 2808509 := bbase (se 3 (by rfl) ⟨526595, by rfl⟩ : syracuseStep 2808509 = 1053191) (by norm_num)
theorem B2808533 : Blo 1871637 2808533 := bbase (se 7 (by rfl) ⟨32912, by rfl⟩ : syracuseStep 2808533 = 65825) (by norm_num)
theorem B9476837 : Blo 1871637 9476837 := bbase (se 4 (by rfl) ⟨888453, by rfl⟩ : syracuseStep 9476837 = 1776907) (by norm_num)
theorem B4741861 : Blo 1871637 4741861 := bbase (se 4 (by rfl) ⟨444549, by rfl⟩ : syracuseStep 4741861 = 889099) (by norm_num)
theorem B2808557 : Blo 1871637 2808557 := bbase (se 3 (by rfl) ⟨526604, by rfl⟩ : syracuseStep 2808557 = 1053209) (by norm_num)
theorem B3160829 : Blo 1871637 3160829 := bbase (se 3 (by rfl) ⟨592655, by rfl⟩ : syracuseStep 3160829 = 1185311) (by norm_num)
theorem B2808581 : Blo 1871637 2808581 := bbase (se 4 (by rfl) ⟨263304, by rfl⟩ : syracuseStep 2808581 = 526609) (by norm_num)
theorem B2808605 : Blo 1871637 2808605 := bbase (se 3 (by rfl) ⟨526613, by rfl⟩ : syracuseStep 2808605 = 1053227) (by norm_num)
theorem B2808629 : Blo 1871637 2808629 := bbase (se 5 (by rfl) ⟨131654, by rfl⟩ : syracuseStep 2808629 = 263309) (by norm_num)
theorem B2808653 : Blo 1871637 2808653 := bbase (se 3 (by rfl) ⟨526622, by rfl⟩ : syracuseStep 2808653 = 1053245) (by norm_num)
theorem B4741973 : Blo 1871637 4741973 := bbase (se 9 (by rfl) ⟨13892, by rfl⟩ : syracuseStep 4741973 = 27785) (by norm_num)
theorem B2808677 : Blo 1871637 2808677 := bbase (se 4 (by rfl) ⟨263313, by rfl⟩ : syracuseStep 2808677 = 526627) (by norm_num)
theorem B2808701 : Blo 1871637 2808701 := bbase (se 3 (by rfl) ⟨526631, by rfl⟩ : syracuseStep 2808701 = 1053263) (by norm_num)
theorem B3160957 : Blo 1871637 3160957 := bbase (se 3 (by rfl) ⟨592679, by rfl⟩ : syracuseStep 3160957 = 1185359) (by norm_num)
theorem B2808725 : Blo 1871637 2808725 := bbase (se 6 (by rfl) ⟨65829, by rfl⟩ : syracuseStep 2808725 = 131659) (by norm_num)
theorem B2808749 : Blo 1871637 2808749 := bbase (se 3 (by rfl) ⟨526640, by rfl⟩ : syracuseStep 2808749 = 1053281) (by norm_num)
theorem B2808773 : Blo 1871637 2808773 := bbase (se 4 (by rfl) ⟨263322, by rfl⟩ : syracuseStep 2808773 = 526645) (by norm_num)
theorem B9608149 : Blo 1871637 9608149 := bbase (se 7 (by rfl) ⟨112595, by rfl⟩ : syracuseStep 9608149 = 225191) (by norm_num)
theorem B3161045 : Blo 1871637 3161045 := bbase (se 7 (by rfl) ⟨37043, by rfl⟩ : syracuseStep 3161045 = 74087) (by norm_num)
theorem B2808797 : Blo 1871637 2808797 := bbase (se 3 (by rfl) ⟨526649, by rfl⟩ : syracuseStep 2808797 = 1053299) (by norm_num)
theorem B3554293 : Blo 1871637 3554293 := bbase (se 5 (by rfl) ⟨166607, by rfl⟩ : syracuseStep 3554293 = 333215) (by norm_num)
theorem B2808821 : Blo 1871637 2808821 := bbase (se 5 (by rfl) ⟨131663, by rfl⟩ : syracuseStep 2808821 = 263327) (by norm_num)
theorem B2808845 : Blo 1871637 2808845 := bbase (se 3 (by rfl) ⟨526658, by rfl⟩ : syracuseStep 2808845 = 1053317) (by norm_num)
theorem B2530325 : Blo 1871637 2530325 := bbase (se 6 (by rfl) ⟨59304, by rfl⟩ : syracuseStep 2530325 = 118609) (by norm_num)
theorem B4742165 : Blo 1871637 4742165 := bbase (se 6 (by rfl) ⟨111144, by rfl⟩ : syracuseStep 4742165 = 222289) (by norm_num)
theorem B2808869 : Blo 1871637 2808869 := bbase (se 4 (by rfl) ⟨263331, by rfl⟩ : syracuseStep 2808869 = 526663) (by norm_num)
theorem B6323237 : Blo 1871637 6323237 := bbase (se 4 (by rfl) ⟨592803, by rfl⟩ : syracuseStep 6323237 = 1185607) (by norm_num)
theorem B2808893 : Blo 1871637 2808893 := bbase (se 3 (by rfl) ⟨526667, by rfl⟩ : syracuseStep 2808893 = 1053335) (by norm_num)
theorem B3374149 : Blo 1871637 3374149 := bbase (se 4 (by rfl) ⟨316326, by rfl⟩ : syracuseStep 3374149 = 632653) (by norm_num)
theorem B22772821 : Blo 1871637 22772821 := bbase (se 8 (by rfl) ⟨133434, by rfl⟩ : syracuseStep 22772821 = 266869) (by norm_num)
theorem B2808917 : Blo 1871637 2808917 := bbase (se 8 (by rfl) ⟨16458, by rfl⟩ : syracuseStep 2808917 = 32917) (by norm_num)
theorem B3161173 : Blo 1871637 3161173 := bbase (se 8 (by rfl) ⟨18522, by rfl⟩ : syracuseStep 3161173 = 37045) (by norm_num)
theorem B2808941 : Blo 1871637 2808941 := bbase (se 3 (by rfl) ⟨526676, by rfl⟩ : syracuseStep 2808941 = 1053353) (by norm_num)
theorem B3554437 : Blo 1871637 3554437 := bbase (se 4 (by rfl) ⟨333228, by rfl⟩ : syracuseStep 3554437 = 666457) (by norm_num)
theorem B2808965 : Blo 1871637 2808965 := bbase (se 4 (by rfl) ⟨263340, by rfl⟩ : syracuseStep 2808965 = 526681) (by norm_num)
theorem B2808989 : Blo 1871637 2808989 := bbase (se 3 (by rfl) ⟨526685, by rfl⟩ : syracuseStep 2808989 = 1053371) (by norm_num)
theorem B3161261 : Blo 1871637 3161261 := bbase (se 3 (by rfl) ⟨592736, by rfl⟩ : syracuseStep 3161261 = 1185473) (by norm_num)
theorem B2809013 : Blo 1871637 2809013 := bbase (se 5 (by rfl) ⟨131672, by rfl⟩ : syracuseStep 2809013 = 263345) (by norm_num)
theorem B1924285 : Blo 1871637 1924285 := bbase (se 3 (by rfl) ⟨360803, by rfl⟩ : syracuseStep 1924285 = 721607) (by norm_num)
theorem B2809037 : Blo 1871637 2809037 := bbase (se 3 (by rfl) ⟨526694, by rfl⟩ : syracuseStep 2809037 = 1053389) (by norm_num)
theorem B2809061 : Blo 1871637 2809061 := bbase (se 4 (by rfl) ⟨263349, by rfl⟩ : syracuseStep 2809061 = 526699) (by norm_num)
theorem B2809085 : Blo 1871637 2809085 := bbase (se 3 (by rfl) ⟨526703, by rfl⟩ : syracuseStep 2809085 = 1053407) (by norm_num)
theorem B2809109 : Blo 1871637 2809109 := bbase (se 6 (by rfl) ⟨65838, by rfl⟩ : syracuseStep 2809109 = 131677) (by norm_num)
theorem B3554597 : Blo 1871637 3554597 := bbase (se 4 (by rfl) ⟨333243, by rfl⟩ : syracuseStep 3554597 = 666487) (by norm_num)
theorem B2809133 : Blo 1871637 2809133 := bbase (se 3 (by rfl) ⟨526712, by rfl⟩ : syracuseStep 2809133 = 1053425) (by norm_num)
theorem B3161389 : Blo 1871637 3161389 := bbase (se 3 (by rfl) ⟨592760, by rfl⟩ : syracuseStep 3161389 = 1185521) (by norm_num)
theorem B2809157 : Blo 1871637 2809157 := bbase (se 4 (by rfl) ⟨263358, by rfl⟩ : syracuseStep 2809157 = 526717) (by norm_num)
theorem B8002901 : Blo 1871637 8002901 := bbase (se 11 (by rfl) ⟨5861, by rfl⟩ : syracuseStep 8002901 = 11723) (by norm_num)
theorem B2809181 : Blo 1871637 2809181 := bbase (se 3 (by rfl) ⟨526721, by rfl⟩ : syracuseStep 2809181 = 1053443) (by norm_num)
theorem B4742509 : Blo 1871637 4742509 := bbase (se 3 (by rfl) ⟨889220, by rfl⟩ : syracuseStep 4742509 = 1778441) (by norm_num)
theorem B2809205 : Blo 1871637 2809205 := bbase (se 5 (by rfl) ⟨131681, by rfl⟩ : syracuseStep 2809205 = 263363) (by norm_num)
theorem B3161477 : Blo 1871637 3161477 := bbase (se 4 (by rfl) ⟨296388, by rfl⟩ : syracuseStep 3161477 = 592777) (by norm_num)
theorem B2809229 : Blo 1871637 2809229 := bbase (se 3 (by rfl) ⟨526730, by rfl⟩ : syracuseStep 2809229 = 1053461) (by norm_num)
theorem B2809253 : Blo 1871637 2809253 := bbase (se 4 (by rfl) ⟨263367, by rfl⟩ : syracuseStep 2809253 = 526735) (by norm_num)
theorem B3554741 : Blo 1871637 3554741 := bbase (se 5 (by rfl) ⟨166628, by rfl⟩ : syracuseStep 3554741 = 333257) (by norm_num)
theorem B2809277 : Blo 1871637 2809277 := bbase (se 3 (by rfl) ⟨526739, by rfl⟩ : syracuseStep 2809277 = 1053479) (by norm_num)
theorem B2809301 : Blo 1871637 2809301 := bbase (se 7 (by rfl) ⟨32921, by rfl⟩ : syracuseStep 2809301 = 65843) (by norm_num)
theorem B4742621 : Blo 1871637 4742621 := bbase (se 3 (by rfl) ⟨889241, by rfl⟩ : syracuseStep 4742621 = 1778483) (by norm_num)
theorem B2809325 : Blo 1871637 2809325 := bbase (se 3 (by rfl) ⟨526748, by rfl⟩ : syracuseStep 2809325 = 1053497) (by norm_num)
theorem B1924597 : Blo 1871637 1924597 := bbase (se 5 (by rfl) ⟨90215, by rfl⟩ : syracuseStep 1924597 = 180431) (by norm_num)
theorem B2809349 : Blo 1871637 2809349 := bbase (se 4 (by rfl) ⟨263376, by rfl⟩ : syracuseStep 2809349 = 526753) (by norm_num)
theorem B3161605 : Blo 1871637 3161605 := bbase (se 4 (by rfl) ⟨296400, by rfl⟩ : syracuseStep 3161605 = 592801) (by norm_num)
theorem B2809373 : Blo 1871637 2809373 := bbase (se 3 (by rfl) ⟨526757, by rfl⟩ : syracuseStep 2809373 = 1053515) (by norm_num)
theorem B2809397 : Blo 1871637 2809397 := bbase (se 5 (by rfl) ⟨131690, by rfl⟩ : syracuseStep 2809397 = 263381) (by norm_num)
theorem B2809421 : Blo 1871637 2809421 := bbase (se 3 (by rfl) ⟨526766, by rfl⟩ : syracuseStep 2809421 = 1053533) (by norm_num)
theorem B3161693 : Blo 1871637 3161693 := bbase (se 3 (by rfl) ⟨592817, by rfl⟩ : syracuseStep 3161693 = 1185635) (by norm_num)
theorem B2809445 : Blo 1871637 2809445 := bbase (se 4 (by rfl) ⟨263385, by rfl⟩ : syracuseStep 2809445 = 526771) (by norm_num)
theorem B2809469 : Blo 1871637 2809469 := bbase (se 3 (by rfl) ⟨526775, by rfl⟩ : syracuseStep 2809469 = 1053551) (by norm_num)
theorem B4497029 : Blo 1871637 4497029 := bbase (se 4 (by rfl) ⟨421596, by rfl⟩ : syracuseStep 4497029 = 843193) (by norm_num)
theorem B2809493 : Blo 1871637 2809493 := bbase (se 6 (by rfl) ⟨65847, by rfl⟩ : syracuseStep 2809493 = 131695) (by norm_num)
theorem B3604141 : Blo 1871637 3604141 := bbase (se 3 (by rfl) ⟨675776, by rfl⟩ : syracuseStep 3604141 = 1351553) (by norm_num)
theorem B2809517 : Blo 1871637 2809517 := bbase (se 3 (by rfl) ⟨526784, by rfl⟩ : syracuseStep 2809517 = 1053569) (by norm_num)
theorem B3202757 : Blo 1871637 3202757 := bbase (se 4 (by rfl) ⟨300258, by rfl⟩ : syracuseStep 3202757 = 600517) (by norm_num)
theorem B3374789 : Blo 1871637 3374789 := bbase (se 4 (by rfl) ⟨316386, by rfl⟩ : syracuseStep 3374789 = 632773) (by norm_num)
theorem B2809541 : Blo 1871637 2809541 := bbase (se 4 (by rfl) ⟨263394, by rfl⟩ : syracuseStep 2809541 = 526789) (by norm_num)
theorem B3555029 : Blo 1871637 3555029 := bbase (se 7 (by rfl) ⟨41660, by rfl⟩ : syracuseStep 3555029 = 83321) (by norm_num)
theorem B2809565 : Blo 1871637 2809565 := bbase (se 3 (by rfl) ⟨526793, by rfl⟩ : syracuseStep 2809565 = 1053587) (by norm_num)
theorem B7995125 : Blo 1871637 7995125 := bbase (se 5 (by rfl) ⟨374771, by rfl⟩ : syracuseStep 7995125 = 749543) (by norm_num)
theorem B2809589 : Blo 1871637 2809589 := bbase (se 5 (by rfl) ⟨131699, by rfl⟩ : syracuseStep 2809589 = 263399) (by norm_num)
theorem B2809613 : Blo 1871637 2809613 := bbase (se 3 (by rfl) ⟨526802, by rfl⟩ : syracuseStep 2809613 = 1053605) (by norm_num)
theorem B2809637 : Blo 1871637 2809637 := bbase (se 4 (by rfl) ⟨263403, by rfl⟩ : syracuseStep 2809637 = 526807) (by norm_num)
theorem B2809661 : Blo 1871637 2809661 := bbase (se 3 (by rfl) ⟨526811, by rfl⟩ : syracuseStep 2809661 = 1053623) (by norm_num)
theorem B4497221 : Blo 1871637 4497221 := bbase (se 4 (by rfl) ⟨421614, by rfl⟩ : syracuseStep 4497221 = 843229) (by norm_num)
theorem B2809685 : Blo 1871637 2809685 := bbase (se 9 (by rfl) ⟨8231, by rfl⟩ : syracuseStep 2809685 = 16463) (by norm_num)
theorem B3555181 : Blo 1871637 3555181 := bbase (se 3 (by rfl) ⟨666596, by rfl⟩ : syracuseStep 3555181 = 1333193) (by norm_num)
theorem B3604333 : Blo 1871637 3604333 := bbase (se 3 (by rfl) ⟨675812, by rfl⟩ : syracuseStep 3604333 = 1351625) (by norm_num)
theorem B2809709 : Blo 1871637 2809709 := bbase (se 3 (by rfl) ⟨526820, by rfl⟩ : syracuseStep 2809709 = 1053641) (by norm_num)
theorem B1998713 : Blo 1871637 1998713 := bbase (se 2 (by rfl) ⟨749517, by rfl⟩ : syracuseStep 1998713 = 1499035) (by norm_num)
theorem B2809733 : Blo 1871637 2809733 := bbase (se 4 (by rfl) ⟨263412, by rfl⟩ : syracuseStep 2809733 = 526825) (by norm_num)
theorem B2809757 : Blo 1871637 2809757 := bbase (se 3 (by rfl) ⟨526829, by rfl⟩ : syracuseStep 2809757 = 1053659) (by norm_num)
theorem B2809781 : Blo 1871637 2809781 := bbase (se 5 (by rfl) ⟨131708, by rfl⟩ : syracuseStep 2809781 = 263417) (by norm_num)
theorem B7593925 : Blo 1871637 7593925 := bbase (se 4 (by rfl) ⟨711930, by rfl⟩ : syracuseStep 7593925 = 1423861) (by norm_num)
theorem B2809805 : Blo 1871637 2809805 := bbase (se 3 (by rfl) ⟨526838, by rfl⟩ : syracuseStep 2809805 = 1053677) (by norm_num)
theorem B2998237 : Blo 1871637 2998237 := bbase (se 3 (by rfl) ⟨562169, by rfl⟩ : syracuseStep 2998237 = 1124339) (by norm_num)
theorem B2809829 : Blo 1871637 2809829 := bbase (se 4 (by rfl) ⟨263421, by rfl⟩ : syracuseStep 2809829 = 526843) (by norm_num)
theorem B9478133 : Blo 1871637 9478133 := bbase (se 5 (by rfl) ⟨444287, by rfl⟩ : syracuseStep 9478133 = 888575) (by norm_num)
theorem B2809853 : Blo 1871637 2809853 := bbase (se 3 (by rfl) ⟨526847, by rfl⟩ : syracuseStep 2809853 = 1053695) (by norm_num)
theorem B2809859 : Blo 1871637 2809859 := bstep (se 1 (by rfl) ⟨2107394, by rfl⟩ : syracuseStep 2809859 = 4214789) B4214789
theorem B15990797 : Blo 1871637 15990797 := bstep (se 3 (by rfl) ⟨2998274, by rfl⟩ : syracuseStep 15990797 = 5996549) B5996549
theorem B2809889 : Blo 1871637 2809889 := bstep (se 2 (by rfl) ⟨1053708, by rfl⟩ : syracuseStep 2809889 = 2107417) B2107417
theorem B2809907 : Blo 1871637 2809907 := bstep (se 1 (by rfl) ⟨2107430, by rfl⟩ : syracuseStep 2809907 = 4214861) B4214861
theorem B3555409 : Blo 1871637 3555409 := bstep (se 2 (by rfl) ⟨1333278, by rfl⟩ : syracuseStep 3555409 = 2666557) B2666557
theorem B2809937 : Blo 1871637 2809937 := bstep (se 2 (by rfl) ⟨1053726, by rfl⟩ : syracuseStep 2809937 = 2107453) B2107453
theorem B2809955 : Blo 1871637 2809955 := bstep (se 1 (by rfl) ⟨2107466, by rfl⟩ : syracuseStep 2809955 = 4214933) B4214933
theorem B2809985 : Blo 1871637 2809985 := bstep (se 2 (by rfl) ⟨1053744, by rfl⟩ : syracuseStep 2809985 = 2107489) B2107489
theorem B2810003 : Blo 1871637 2810003 := bstep (se 1 (by rfl) ⟨2107502, by rfl⟩ : syracuseStep 2810003 = 4215005) B4215005
theorem B2810033 : Blo 1871637 2810033 := bstep (se 2 (by rfl) ⟨1053762, by rfl⟩ : syracuseStep 2810033 = 2107525) B2107525
theorem B2703539 : Blo 1871637 2703539 := bstep (se 1 (by rfl) ⟨2027654, by rfl⟩ : syracuseStep 2703539 = 4055309) B4055309
theorem B2810051 : Blo 1871637 2810051 := bstep (se 1 (by rfl) ⟨2107538, by rfl⟩ : syracuseStep 2810051 = 4215077) B4215077
theorem B10666181 : Blo 1871637 10666181 := bstep (se 4 (by rfl) ⟨999954, by rfl⟩ : syracuseStep 10666181 = 1999909) B1999909
theorem B2810081 : Blo 1871637 2810081 := bstep (se 2 (by rfl) ⟨1053780, by rfl⟩ : syracuseStep 2810081 = 2107561) B2107561
theorem B8110307 : Blo 1871637 8110307 := bstep (se 1 (by rfl) ⟨6082730, by rfl⟩ : syracuseStep 8110307 = 12165461) B12165461
theorem B3555569 : Blo 1871637 3555569 := bstep (se 2 (by rfl) ⟨1333338, by rfl⟩ : syracuseStep 3555569 = 2666677) B2666677
theorem B2531569 : Blo 1871637 2531569 := bstep (se 2 (by rfl) ⟨949338, by rfl⟩ : syracuseStep 2531569 = 1898677) B1898677
theorem B2810099 : Blo 1871637 2810099 := bstep (se 1 (by rfl) ⟨2107574, by rfl⟩ : syracuseStep 2810099 = 4215149) B4215149
theorem B2810129 : Blo 1871637 2810129 := bstep (se 2 (by rfl) ⟨1053798, by rfl⟩ : syracuseStep 2810129 = 2107597) B2107597
theorem B1999123 : Blo 1871637 1999123 := bstep (se 1 (by rfl) ⟨1499342, by rfl⟩ : syracuseStep 1999123 = 2998685) B2998685
theorem B2105635 : Blo 1871637 2105635 := bstep (se 1 (by rfl) ⟨1579226, by rfl⟩ : syracuseStep 2105635 = 3158453) B3158453
theorem B2810147 : Blo 1871637 2810147 := bstep (se 1 (by rfl) ⟨2107610, by rfl⟩ : syracuseStep 2810147 = 4215221) B4215221
theorem B5996845 : Blo 1871637 5996845 := bstep (se 3 (by rfl) ⟨1124408, by rfl⟩ : syracuseStep 5996845 = 2248817) B2248817
theorem B5693741 : Blo 1871637 5693741 := bstep (se 3 (by rfl) ⟨1067576, by rfl⟩ : syracuseStep 5693741 = 2135153) B2135153
theorem B2810177 : Blo 1871637 2810177 := bstep (se 2 (by rfl) ⟨1053816, by rfl⟩ : syracuseStep 2810177 = 2107633) B2107633
theorem B2810195 : Blo 1871637 2810195 := bstep (se 1 (by rfl) ⟨2107646, by rfl⟩ : syracuseStep 2810195 = 4215293) B4215293
theorem B5996909 : Blo 1871637 5996909 := bstep (se 3 (by rfl) ⟨1124420, by rfl⟩ : syracuseStep 5996909 = 2248841) B2248841
theorem B2810225 : Blo 1871637 2810225 := bstep (se 2 (by rfl) ⟨1053834, by rfl⟩ : syracuseStep 2810225 = 2107669) B2107669
theorem B2810243 : Blo 1871637 2810243 := bstep (se 1 (by rfl) ⟨2107682, by rfl⟩ : syracuseStep 2810243 = 4215365) B4215365
theorem B2810273 : Blo 1871637 2810273 := bstep (se 2 (by rfl) ⟨1053852, by rfl⟩ : syracuseStep 2810273 = 2107705) B2107705
theorem B2105779 : Blo 1871637 2105779 := bstep (se 1 (by rfl) ⟨1579334, by rfl⟩ : syracuseStep 2105779 = 3158669) B3158669
theorem B2810291 : Blo 1871637 2810291 := bstep (se 1 (by rfl) ⟨2107718, by rfl⟩ : syracuseStep 2810291 = 4215437) B4215437
theorem B3039697 : Blo 1871637 3039697 := bstep (se 2 (by rfl) ⟨1139886, by rfl⟩ : syracuseStep 3039697 = 2279773) B2279773
theorem B3375569 : Blo 1871637 3375569 := bstep (se 2 (by rfl) ⟨1265838, by rfl⟩ : syracuseStep 3375569 = 2531677) B2531677
theorem B2810321 : Blo 1871637 2810321 := bstep (se 2 (by rfl) ⟨1053870, by rfl⟩ : syracuseStep 2810321 = 2107741) B2107741
theorem B2810339 : Blo 1871637 2810339 := bstep (se 1 (by rfl) ⟨2107754, by rfl⟩ : syracuseStep 2810339 = 4215509) B4215509
theorem B2810369 : Blo 1871637 2810369 := bstep (se 2 (by rfl) ⟨1053888, by rfl⟩ : syracuseStep 2810369 = 2107777) B2107777
theorem B2998787 : Blo 1871637 2998787 := bstep (se 1 (by rfl) ⟨2249090, by rfl⟩ : syracuseStep 2998787 = 4498181) B4498181
theorem B2810387 : Blo 1871637 2810387 := bstep (se 1 (by rfl) ⟨2107790, by rfl⟩ : syracuseStep 2810387 = 4215581) B4215581
theorem B10805795 : Blo 1871637 10805795 := bstep (se 1 (by rfl) ⟨8104346, by rfl⟩ : syracuseStep 10805795 = 16208693) B16208693
theorem B2810417 : Blo 1871637 2810417 := bstep (se 2 (by rfl) ⟨1053906, by rfl⟩ : syracuseStep 2810417 = 2107813) B2107813
theorem B2105923 : Blo 1871637 2105923 := bstep (se 1 (by rfl) ⟨1579442, by rfl⟩ : syracuseStep 2105923 = 3158885) B3158885
theorem B2810435 : Blo 1871637 2810435 := bstep (se 1 (by rfl) ⟨2107826, by rfl⟩ : syracuseStep 2810435 = 4215653) B4215653
theorem B2998865 : Blo 1871637 2998865 := bstep (se 2 (by rfl) ⟨1124574, by rfl⟩ : syracuseStep 2998865 = 2249149) B2249149
theorem B12001891 : Blo 1871637 12001891 := bstep (se 1 (by rfl) ⟨9001418, by rfl⟩ : syracuseStep 12001891 = 18002837) B18002837
theorem B3555971 : Blo 1871637 3555971 := bstep (se 1 (by rfl) ⟨2666978, by rfl⟩ : syracuseStep 3555971 = 5333957) B5333957
theorem B10666637 : Blo 1871637 10666637 := bstep (se 3 (by rfl) ⟨1999994, by rfl⟩ : syracuseStep 10666637 = 3999989) B3999989
theorem B2532001 : Blo 1871637 2532001 := bstep (se 2 (by rfl) ⟨949500, by rfl⟩ : syracuseStep 2532001 = 1899001) B1899001
theorem B7996067 : Blo 1871637 7996067 := bstep (se 1 (by rfl) ⟨5997050, by rfl⟩ : syracuseStep 7996067 = 11994101) B11994101
theorem B2106067 : Blo 1871637 2106067 := bstep (se 1 (by rfl) ⟨1579550, by rfl⟩ : syracuseStep 2106067 = 3159101) B3159101
theorem B4211441 : Blo 1871637 4211441 := bstep (se 2 (by rfl) ⟨1579290, by rfl⟩ : syracuseStep 4211441 = 3158581) B3158581
theorem B3375857 : Blo 1871637 3375857 := bstep (se 2 (by rfl) ⟨1265946, by rfl⟩ : syracuseStep 3375857 = 2531893) B2531893
theorem B4211459 : Blo 1871637 4211459 := bstep (se 1 (by rfl) ⟨3158594, by rfl⟩ : syracuseStep 4211459 = 6317189) B6317189
theorem B5333809 : Blo 1871637 5333809 := bstep (se 2 (by rfl) ⟨2000178, by rfl⟩ : syracuseStep 5333809 = 4000357) B4000357
theorem B27009845 : Blo 1871637 27009845 := bstep (se 5 (by rfl) ⟨1266086, by rfl⟩ : syracuseStep 27009845 = 2532173) B2532173
theorem B3203921 : Blo 1871637 3203921 := bstep (se 2 (by rfl) ⟨1201470, by rfl⟩ : syracuseStep 3203921 = 2402941) B2402941
theorem B2106211 : Blo 1871637 2106211 := bstep (se 1 (by rfl) ⟨1579658, by rfl⟩ : syracuseStep 2106211 = 3159317) B3159317
theorem B6316973 : Blo 1871637 6316973 := bstep (se 3 (by rfl) ⟨1184432, by rfl⟩ : syracuseStep 6316973 = 2368865) B2368865
theorem B2999249 : Blo 1871637 2999249 := bstep (se 2 (by rfl) ⟨1124718, by rfl⟩ : syracuseStep 2999249 = 2249437) B2249437
theorem B6317027 : Blo 1871637 6317027 := bstep (se 1 (by rfl) ⟨4737770, by rfl⟩ : syracuseStep 6317027 = 9475541) B9475541
theorem B2106355 : Blo 1871637 2106355 := bstep (se 1 (by rfl) ⟨1579766, by rfl⟩ : syracuseStep 2106355 = 3159533) B3159533
theorem B4211729 : Blo 1871637 4211729 := bstep (se 2 (by rfl) ⟨1579398, by rfl⟩ : syracuseStep 4211729 = 3158797) B3158797
theorem B4211747 : Blo 1871637 4211747 := bstep (se 1 (by rfl) ⟨3158810, by rfl⟩ : syracuseStep 4211747 = 6317621) B6317621
theorem B5334083 : Blo 1871637 5334083 := bstep (se 1 (by rfl) ⟨4000562, by rfl⟩ : syracuseStep 5334083 = 8001125) B8001125
theorem B2999377 : Blo 1871637 2999377 := bstep (se 2 (by rfl) ⟨1124766, by rfl⟩ : syracuseStep 2999377 = 2249533) B2249533
theorem B9479267 : Blo 1871637 9479267 := bstep (se 1 (by rfl) ⟨7109450, by rfl⟩ : syracuseStep 9479267 = 14218901) B14218901
theorem B2106499 : Blo 1871637 2106499 := bstep (se 1 (by rfl) ⟨1579874, by rfl⟩ : syracuseStep 2106499 = 3159749) B3159749
theorem B6317297 : Blo 1871637 6317297 := bstep (se 2 (by rfl) ⟨2368986, by rfl⟩ : syracuseStep 6317297 = 4737973) B4737973
theorem B5334275 : Blo 1871637 5334275 := bstep (se 1 (by rfl) ⟨4000706, by rfl⟩ : syracuseStep 5334275 = 8001413) B8001413
theorem B2106643 : Blo 1871637 2106643 := bstep (se 1 (by rfl) ⟨1579982, by rfl⟩ : syracuseStep 2106643 = 3159965) B3159965
theorem B60712213 : Blo 1871637 60712213 := bstep (se 6 (by rfl) ⟨1422942, by rfl⟩ : syracuseStep 60712213 = 2845885) B2845885
theorem B4212017 : Blo 1871637 4212017 := bstep (se 2 (by rfl) ⟨1579506, by rfl⟩ : syracuseStep 4212017 = 3159013) B3159013
theorem B4212035 : Blo 1871637 4212035 := bstep (se 1 (by rfl) ⟨3159026, by rfl⟩ : syracuseStep 4212035 = 6318053) B6318053
theorem B2106787 : Blo 1871637 2106787 := bstep (se 1 (by rfl) ⟨1580090, by rfl⟩ : syracuseStep 2106787 = 3160181) B3160181
theorem B4498865 : Blo 1871637 4498865 := bstep (se 2 (by rfl) ⟨1687074, by rfl⟩ : syracuseStep 4498865 = 3374149) B3374149
theorem B14222789 : Blo 1871637 14222789 := bstep (se 4 (by rfl) ⟨1333386, by rfl⟩ : syracuseStep 14222789 = 2666773) B2666773
theorem B5481955 : Blo 1871637 5481955 := bstep (se 1 (by rfl) ⟨4111466, by rfl⟩ : syracuseStep 5481955 = 8222933) B8222933
theorem B10118641 : Blo 1871637 10118641 := bstep (se 2 (by rfl) ⟨3794490, by rfl⟩ : syracuseStep 10118641 = 7588981) B7588981
theorem B2369027 : Blo 1871637 2369027 := bstep (se 1 (by rfl) ⟨1776770, by rfl⟩ : syracuseStep 2369027 = 3553541) B3553541
theorem B3556867 : Blo 1871637 3556867 := bstep (se 1 (by rfl) ⟨2667650, by rfl⟩ : syracuseStep 3556867 = 5335301) B5335301
theorem B2106931 : Blo 1871637 2106931 := bstep (se 1 (by rfl) ⟨1580198, by rfl⟩ : syracuseStep 2106931 = 3160397) B3160397
theorem B24053317 : Blo 1871637 24053317 := bstep (se 4 (by rfl) ⟨2254998, by rfl⟩ : syracuseStep 24053317 = 4509997) B4509997
theorem B4212305 : Blo 1871637 4212305 := bstep (se 2 (by rfl) ⟨1579614, by rfl⟩ : syracuseStep 4212305 = 3159229) B3159229
theorem B2565713 : Blo 1871637 2565713 := bstep (se 2 (by rfl) ⟨962142, by rfl⟩ : syracuseStep 2565713 = 1924285) B1924285
theorem B4212323 : Blo 1871637 4212323 := bstep (se 1 (by rfl) ⟨3159242, by rfl⟩ : syracuseStep 4212323 = 6318485) B6318485
theorem B11388529 : Blo 1871637 11388529 := bstep (se 2 (by rfl) ⟨4270698, by rfl⟩ : syracuseStep 11388529 = 8541397) B8541397
theorem B2107075 : Blo 1871637 2107075 := bstep (se 1 (by rfl) ⟨1580306, by rfl⟩ : syracuseStep 2107075 = 3160613) B3160613
theorem B6317837 : Blo 1871637 6317837 := bstep (se 3 (by rfl) ⟨1184594, by rfl⟩ : syracuseStep 6317837 = 2369189) B2369189
theorem B6317891 : Blo 1871637 6317891 := bstep (se 1 (by rfl) ⟨4738418, by rfl⟩ : syracuseStep 6317891 = 9476837) B9476837
theorem B2107219 : Blo 1871637 2107219 := bstep (se 1 (by rfl) ⟨1580414, by rfl⟩ : syracuseStep 2107219 = 3160829) B3160829
theorem B4212593 : Blo 1871637 4212593 := bstep (se 2 (by rfl) ⟨1579722, by rfl⟩ : syracuseStep 4212593 = 3159445) B3159445
theorem B4212611 : Blo 1871637 4212611 := bstep (se 1 (by rfl) ⟨3159458, by rfl⟩ : syracuseStep 4212611 = 6318917) B6318917
theorem B9480077 : Blo 1871637 9480077 := bstep (se 3 (by rfl) ⟨1777514, by rfl⟩ : syracuseStep 9480077 = 3555029) B3555029
theorem B45549539 : Blo 1871637 45549539 := bstep (se 1 (by rfl) ⟨34162154, by rfl⟩ : syracuseStep 45549539 = 68324309) B68324309
theorem B2107363 : Blo 1871637 2107363 := bstep (se 1 (by rfl) ⟨1580522, by rfl⟩ : syracuseStep 2107363 = 3161045) B3161045
theorem B2566129 : Blo 1871637 2566129 := bstep (se 2 (by rfl) ⟨962298, by rfl⟩ : syracuseStep 2566129 = 1924597) B1924597
theorem B7112717 : Blo 1871637 7112717 := bstep (se 3 (by rfl) ⟨1333634, by rfl⟩ : syracuseStep 7112717 = 2667269) B2667269
theorem B5335085 : Blo 1871637 5335085 := bstep (se 3 (by rfl) ⟨1000328, by rfl⟩ : syracuseStep 5335085 = 2000657) B2000657
theorem B6318161 : Blo 1871637 6318161 := bstep (se 2 (by rfl) ⟨2369310, by rfl⟩ : syracuseStep 6318161 = 4738621) B4738621
theorem B5998691 : Blo 1871637 5998691 := bstep (se 1 (by rfl) ⟨4499018, by rfl⟩ : syracuseStep 5998691 = 8998037) B8998037
theorem B2107507 : Blo 1871637 2107507 := bstep (se 1 (by rfl) ⟨1580630, by rfl⟩ : syracuseStep 2107507 = 3161261) B3161261
theorem B4212881 : Blo 1871637 4212881 := bstep (se 2 (by rfl) ⟨1579830, by rfl⟩ : syracuseStep 4212881 = 3159661) B3159661
theorem B4212899 : Blo 1871637 4212899 := bstep (se 1 (by rfl) ⟨3159674, by rfl⟩ : syracuseStep 4212899 = 6319349) B6319349
theorem B2369731 : Blo 1871637 2369731 := bstep (se 1 (by rfl) ⟨1777298, by rfl⟩ : syracuseStep 2369731 = 3554597) B3554597
theorem B5335267 : Blo 1871637 5335267 := bstep (se 1 (by rfl) ⟨4001450, by rfl⟩ : syracuseStep 5335267 = 8002901) B8002901
theorem B2107651 : Blo 1871637 2107651 := bstep (se 1 (by rfl) ⟨1580738, by rfl⟩ : syracuseStep 2107651 = 3161477) B3161477
theorem B2369827 : Blo 1871637 2369827 := bstep (se 1 (by rfl) ⟨1777370, by rfl⟩ : syracuseStep 2369827 = 3554741) B3554741
theorem B6408497 : Blo 1871637 6408497 := bstep (se 2 (by rfl) ⟨2403186, by rfl⟩ : syracuseStep 6408497 = 4806373) B4806373
theorem B2107795 : Blo 1871637 2107795 := bstep (se 1 (by rfl) ⟨1580846, by rfl⟩ : syracuseStep 2107795 = 3161693) B3161693
theorem B4213169 : Blo 1871637 4213169 := bstep (se 2 (by rfl) ⟨1579938, by rfl⟩ : syracuseStep 4213169 = 3159877) B3159877
theorem B4213187 : Blo 1871637 4213187 := bstep (se 1 (by rfl) ⟨3159890, by rfl⟩ : syracuseStep 4213187 = 6319781) B6319781
theorem B51243461 : Blo 1871637 51243461 := bstep (se 4 (by rfl) ⟨4804074, by rfl⟩ : syracuseStep 51243461 = 9608149) B9608149
theorem B3000883 : Blo 1871637 3000883 := bstep (se 1 (by rfl) ⟨2250662, by rfl⟩ : syracuseStep 3000883 = 4501325) B4501325
theorem B6318701 : Blo 1871637 6318701 := bstep (se 3 (by rfl) ⟨1184756, by rfl⟩ : syracuseStep 6318701 = 2369513) B2369513
theorem B4737649 : Blo 1871637 4737649 := bstep (se 2 (by rfl) ⟨1776618, by rfl⟩ : syracuseStep 4737649 = 3553237) B3553237
theorem B7998065 : Blo 1871637 7998065 := bstep (se 2 (by rfl) ⟨2999274, by rfl⟩ : syracuseStep 7998065 = 5998549) B5998549
theorem B6318755 : Blo 1871637 6318755 := bstep (se 1 (by rfl) ⟨4739066, by rfl⟩ : syracuseStep 6318755 = 9478133) B9478133
theorem B4000433 : Blo 1871637 4000433 := bstep (se 2 (by rfl) ⟨1500162, by rfl⟩ : syracuseStep 4000433 = 3000325) B3000325
theorem B3795665 : Blo 1871637 3795665 := bstep (se 2 (by rfl) ⟨1423374, by rfl⟩ : syracuseStep 3795665 = 2846749) B2846749
theorem B4213457 : Blo 1871637 4213457 := bstep (se 2 (by rfl) ⟨1580046, by rfl⟩ : syracuseStep 4213457 = 3160093) B3160093
theorem B4270819 : Blo 1871637 4270819 := bstep (se 1 (by rfl) ⟨3203114, by rfl⟩ : syracuseStep 4270819 = 6406229) B6406229
theorem B4213475 : Blo 1871637 4213475 := bstep (se 1 (by rfl) ⟨3160106, by rfl⟩ : syracuseStep 4213475 = 6320213) B6320213
theorem B32008931 : Blo 1871637 32008931 := bstep (se 1 (by rfl) ⟨24006698, by rfl⟩ : syracuseStep 32008931 = 48013397) B48013397
theorem B2665219 : Blo 1871637 2665219 := bstep (se 1 (by rfl) ⟨1998914, by rfl⟩ : syracuseStep 2665219 = 3997829) B3997829
theorem B2370323 : Blo 1871637 2370323 := bstep (se 1 (by rfl) ⟨1777742, by rfl⟩ : syracuseStep 2370323 = 3555485) B3555485
theorem B7113521 : Blo 1871637 7113521 := bstep (se 2 (by rfl) ⟨2667570, by rfl⟩ : syracuseStep 7113521 = 5335141) B5335141
theorem B2665315 : Blo 1871637 2665315 := bstep (se 1 (by rfl) ⟨1998986, by rfl⟩ : syracuseStep 2665315 = 3997973) B3997973
theorem B4737923 : Blo 1871637 4737923 := bstep (se 1 (by rfl) ⟨3553442, by rfl⟩ : syracuseStep 4737923 = 7106885) B7106885
theorem B6319025 : Blo 1871637 6319025 := bstep (se 2 (by rfl) ⟨2369634, by rfl⟩ : syracuseStep 6319025 = 4739269) B4739269
theorem B10660805 : Blo 1871637 10660805 := bstep (se 4 (by rfl) ⟨999450, by rfl⟩ : syracuseStep 10660805 = 1998901) B1998901
theorem B4213745 : Blo 1871637 4213745 := bstep (se 2 (by rfl) ⟨1580154, by rfl⟩ : syracuseStep 4213745 = 3160309) B3160309
theorem B4213763 : Blo 1871637 4213763 := bstep (se 1 (by rfl) ⟨3160322, by rfl⟩ : syracuseStep 4213763 = 6320645) B6320645
theorem B4738115 : Blo 1871637 4738115 := bstep (se 1 (by rfl) ⟨3553586, by rfl⟩ : syracuseStep 4738115 = 7107173) B7107173
theorem B5696611 : Blo 1871637 5696611 := bstep (se 1 (by rfl) ⟨4272458, by rfl⟩ : syracuseStep 5696611 = 8544917) B8544917
theorem B4214033 : Blo 1871637 4214033 := bstep (se 2 (by rfl) ⟨1580262, by rfl⟩ : syracuseStep 4214033 = 3160525) B3160525
theorem B4214051 : Blo 1871637 4214051 := bstep (se 1 (by rfl) ⟨3160538, by rfl⟩ : syracuseStep 4214051 = 6321077) B6321077
theorem B12004685 : Blo 1871637 12004685 := bstep (se 3 (by rfl) ⟨2250878, by rfl⟩ : syracuseStep 12004685 = 4501757) B4501757
theorem B2600273 : Blo 1871637 2600273 := bstep (se 2 (by rfl) ⟨975102, by rfl⟩ : syracuseStep 2600273 = 1950205) B1950205
theorem B2665811 : Blo 1871637 2665811 := bstep (se 1 (by rfl) ⟨1999358, by rfl⟩ : syracuseStep 2665811 = 3998717) B3998717
theorem B3247523 : Blo 1871637 3247523 := bstep (se 1 (by rfl) ⟨2435642, by rfl⟩ : syracuseStep 3247523 = 4871285) B4871285
theorem B6319565 : Blo 1871637 6319565 := bstep (se 3 (by rfl) ⟨1184918, by rfl⟩ : syracuseStep 6319565 = 2369837) B2369837
theorem B2371027 : Blo 1871637 2371027 := bstep (se 1 (by rfl) ⟨1778270, by rfl⟩ : syracuseStep 2371027 = 3556541) B3556541
theorem B10669553 : Blo 1871637 10669553 := bstep (se 2 (by rfl) ⟨4001082, by rfl⟩ : syracuseStep 10669553 = 8002165) B8002165
theorem B6319619 : Blo 1871637 6319619 := bstep (se 1 (by rfl) ⟨4739714, by rfl⟩ : syracuseStep 6319619 = 9479429) B9479429
theorem B2846227 : Blo 1871637 2846227 := bstep (se 1 (by rfl) ⟨2134670, by rfl⟩ : syracuseStep 2846227 = 4269341) B4269341
theorem B4214321 : Blo 1871637 4214321 := bstep (se 2 (by rfl) ⟨1580370, by rfl⟩ : syracuseStep 4214321 = 3160741) B3160741
theorem B2371123 : Blo 1871637 2371123 := bstep (se 1 (by rfl) ⟨1778342, by rfl⟩ : syracuseStep 2371123 = 3556685) B3556685
theorem B4214339 : Blo 1871637 4214339 := bstep (se 1 (by rfl) ⟨3160754, by rfl⟩ : syracuseStep 4214339 = 6321509) B6321509
theorem B19222085 : Blo 1871637 19222085 := bstep (se 4 (by rfl) ⟨1802070, by rfl⟩ : syracuseStep 19222085 = 3604141) B3604141
theorem B10661489 : Blo 1871637 10661489 := bstep (se 2 (by rfl) ⟨3998058, by rfl⟩ : syracuseStep 10661489 = 7996117) B7996117
theorem B23998193 : Blo 1871637 23998193 := bstep (se 2 (by rfl) ⟨8999322, by rfl⟩ : syracuseStep 23998193 = 17998645) B17998645
theorem B6319889 : Blo 1871637 6319889 := bstep (se 2 (by rfl) ⟨2369958, by rfl⟩ : syracuseStep 6319889 = 4739917) B4739917
theorem B1871651 : Blo 1871637 1871651 := bstep (se 1 (by rfl) ⟨1403738, by rfl⟩ : syracuseStep 1871651 = 2807477) B2807477
theorem B1871667 : Blo 1871637 1871667 := bstep (se 1 (by rfl) ⟨1403750, by rfl⟩ : syracuseStep 1871667 = 2807501) B2807501
theorem B1871683 : Blo 1871637 1871683 := bstep (se 1 (by rfl) ⟨1403762, by rfl⟩ : syracuseStep 1871683 = 2807525) B2807525
theorem B4214609 : Blo 1871637 4214609 := bstep (se 2 (by rfl) ⟨1580478, by rfl⟩ : syracuseStep 4214609 = 3160957) B3160957
theorem B1871699 : Blo 1871637 1871699 := bstep (se 1 (by rfl) ⟨1403774, by rfl⟩ : syracuseStep 1871699 = 2807549) B2807549
theorem B1871715 : Blo 1871637 1871715 := bstep (se 1 (by rfl) ⟨1403786, by rfl⟩ : syracuseStep 1871715 = 2807573) B2807573
theorem B4214627 : Blo 1871637 4214627 := bstep (se 1 (by rfl) ⟨3160970, by rfl⟩ : syracuseStep 4214627 = 6321941) B6321941
theorem B1871731 : Blo 1871637 1871731 := bstep (se 1 (by rfl) ⟨1403798, by rfl⟩ : syracuseStep 1871731 = 2807597) B2807597
theorem B1871747 : Blo 1871637 1871747 := bstep (se 1 (by rfl) ⟨1403810, by rfl⟩ : syracuseStep 1871747 = 2807621) B2807621
theorem B1871763 : Blo 1871637 1871763 := bstep (se 1 (by rfl) ⟨1403822, by rfl⟩ : syracuseStep 1871763 = 2807645) B2807645
theorem B1871779 : Blo 1871637 1871779 := bstep (se 1 (by rfl) ⟨1403834, by rfl⟩ : syracuseStep 1871779 = 2807669) B2807669
theorem B1871795 : Blo 1871637 1871795 := bstep (se 1 (by rfl) ⟨1403846, by rfl⟩ : syracuseStep 1871795 = 2807693) B2807693
theorem B1871811 : Blo 1871637 1871811 := bstep (se 1 (by rfl) ⟨1403858, by rfl⟩ : syracuseStep 1871811 = 2807717) B2807717
theorem B2666449 : Blo 1871637 2666449 := bstep (se 2 (by rfl) ⟨999918, by rfl⟩ : syracuseStep 2666449 = 1999837) B1999837
theorem B1871827 : Blo 1871637 1871827 := bstep (se 1 (by rfl) ⟨1403870, by rfl⟩ : syracuseStep 1871827 = 2807741) B2807741
theorem B1871843 : Blo 1871637 1871843 := bstep (se 1 (by rfl) ⟨1403882, by rfl⟩ : syracuseStep 1871843 = 2807765) B2807765
theorem B4739057 : Blo 1871637 4739057 := bstep (se 2 (by rfl) ⟨1777146, by rfl⟩ : syracuseStep 4739057 = 3554293) B3554293
theorem B1871859 : Blo 1871637 1871859 := bstep (se 1 (by rfl) ⟨1403894, by rfl⟩ : syracuseStep 1871859 = 2807789) B2807789
theorem B1871875 : Blo 1871637 1871875 := bstep (se 1 (by rfl) ⟨1403906, by rfl⟩ : syracuseStep 1871875 = 2807813) B2807813
theorem B4501507 : Blo 1871637 4501507 := bstep (se 1 (by rfl) ⟨3376130, by rfl⟩ : syracuseStep 4501507 = 6752261) B6752261
theorem B11390989 : Blo 1871637 11390989 := bstep (se 3 (by rfl) ⟨2135810, by rfl⟩ : syracuseStep 11390989 = 4271621) B4271621
theorem B1871891 : Blo 1871637 1871891 := bstep (se 1 (by rfl) ⟨1403918, by rfl⟩ : syracuseStep 1871891 = 2807837) B2807837
theorem B1871907 : Blo 1871637 1871907 := bstep (se 1 (by rfl) ⟨1403930, by rfl⟩ : syracuseStep 1871907 = 2807861) B2807861
theorem B4739107 : Blo 1871637 4739107 := bstep (se 1 (by rfl) ⟨3554330, by rfl⟩ : syracuseStep 4739107 = 7108661) B7108661
theorem B1871923 : Blo 1871637 1871923 := bstep (se 1 (by rfl) ⟨1403942, by rfl⟩ : syracuseStep 1871923 = 2807885) B2807885
theorem B1871939 : Blo 1871637 1871939 := bstep (se 1 (by rfl) ⟨1403954, by rfl⟩ : syracuseStep 1871939 = 2807909) B2807909
theorem B1871955 : Blo 1871637 1871955 := bstep (se 1 (by rfl) ⟨1403966, by rfl⟩ : syracuseStep 1871955 = 2807933) B2807933
theorem B1871971 : Blo 1871637 1871971 := bstep (se 1 (by rfl) ⟨1403978, by rfl⟩ : syracuseStep 1871971 = 2807957) B2807957
theorem B30363761 : Blo 1871637 30363761 := bstep (se 2 (by rfl) ⟨11386410, by rfl⟩ : syracuseStep 30363761 = 22772821) B22772821
theorem B1871987 : Blo 1871637 1871987 := bstep (se 1 (by rfl) ⟨1403990, by rfl⟩ : syracuseStep 1871987 = 2807981) B2807981
theorem B4214897 : Blo 1871637 4214897 := bstep (se 2 (by rfl) ⟨1580586, by rfl⟩ : syracuseStep 4214897 = 3161173) B3161173
theorem B1872003 : Blo 1871637 1872003 := bstep (se 1 (by rfl) ⟨1404002, by rfl⟩ : syracuseStep 1872003 = 2808005) B2808005
theorem B4214915 : Blo 1871637 4214915 := bstep (se 1 (by rfl) ⟨3161186, by rfl⟩ : syracuseStep 4214915 = 6322373) B6322373
theorem B1872019 : Blo 1871637 1872019 := bstep (se 1 (by rfl) ⟨1404014, by rfl⟩ : syracuseStep 1872019 = 2808029) B2808029
theorem B1872035 : Blo 1871637 1872035 := bstep (se 1 (by rfl) ⟨1404026, by rfl⟩ : syracuseStep 1872035 = 2808053) B2808053
theorem B4739249 : Blo 1871637 4739249 := bstep (se 2 (by rfl) ⟨1777218, by rfl⟩ : syracuseStep 4739249 = 3554437) B3554437
theorem B1872051 : Blo 1871637 1872051 := bstep (se 1 (by rfl) ⟨1404038, by rfl⟩ : syracuseStep 1872051 = 2808077) B2808077
theorem B1872067 : Blo 1871637 1872067 := bstep (se 1 (by rfl) ⟨1404050, by rfl⟩ : syracuseStep 1872067 = 2808101) B2808101
theorem B1872083 : Blo 1871637 1872083 := bstep (se 1 (by rfl) ⟨1404062, by rfl⟩ : syracuseStep 1872083 = 2808125) B2808125
theorem B1872099 : Blo 1871637 1872099 := bstep (se 1 (by rfl) ⟨1404074, by rfl⟩ : syracuseStep 1872099 = 2808149) B2808149
theorem B14217443 : Blo 1871637 14217443 := bstep (se 1 (by rfl) ⟨10663082, by rfl⟩ : syracuseStep 14217443 = 21326165) B21326165
theorem B20254961 : Blo 1871637 20254961 := bstep (se 2 (by rfl) ⟨7595610, by rfl⟩ : syracuseStep 20254961 = 15191221) B15191221
theorem B1872115 : Blo 1871637 1872115 := bstep (se 1 (by rfl) ⟨1404086, by rfl⟩ : syracuseStep 1872115 = 2808173) B2808173
theorem B1872131 : Blo 1871637 1872131 := bstep (se 1 (by rfl) ⟨1404098, by rfl⟩ : syracuseStep 1872131 = 2808197) B2808197
theorem B1872147 : Blo 1871637 1872147 := bstep (se 1 (by rfl) ⟨1404110, by rfl⟩ : syracuseStep 1872147 = 2808221) B2808221
theorem B2666785 : Blo 1871637 2666785 := bstep (se 2 (by rfl) ⟨1000044, by rfl⟩ : syracuseStep 2666785 = 2000089) B2000089
theorem B1872163 : Blo 1871637 1872163 := bstep (se 1 (by rfl) ⟨1404122, by rfl⟩ : syracuseStep 1872163 = 2808245) B2808245
theorem B6320429 : Blo 1871637 6320429 := bstep (se 3 (by rfl) ⟨1185080, by rfl⟩ : syracuseStep 6320429 = 2370161) B2370161
theorem B1872179 : Blo 1871637 1872179 := bstep (se 1 (by rfl) ⟨1404134, by rfl⟩ : syracuseStep 1872179 = 2808269) B2808269
theorem B1872195 : Blo 1871637 1872195 := bstep (se 1 (by rfl) ⟨1404146, by rfl⟩ : syracuseStep 1872195 = 2808293) B2808293
theorem B1872211 : Blo 1871637 1872211 := bstep (se 1 (by rfl) ⟨1404158, by rfl⟩ : syracuseStep 1872211 = 2808317) B2808317
theorem B1872227 : Blo 1871637 1872227 := bstep (se 1 (by rfl) ⟨1404170, by rfl⟩ : syracuseStep 1872227 = 2808341) B2808341
theorem B6320483 : Blo 1871637 6320483 := bstep (se 1 (by rfl) ⟨4740362, by rfl⟩ : syracuseStep 6320483 = 9480725) B9480725
theorem B1872243 : Blo 1871637 1872243 := bstep (se 1 (by rfl) ⟨1404182, by rfl⟩ : syracuseStep 1872243 = 2808365) B2808365
theorem B1872259 : Blo 1871637 1872259 := bstep (se 1 (by rfl) ⟨1404194, by rfl⟩ : syracuseStep 1872259 = 2808389) B2808389
theorem B4215185 : Blo 1871637 4215185 := bstep (se 2 (by rfl) ⟨1580694, by rfl⟩ : syracuseStep 4215185 = 3161389) B3161389
theorem B3158419 : Blo 1871637 3158419 := bstep (se 1 (by rfl) ⟨2368814, by rfl⟩ : syracuseStep 3158419 = 4737629) B4737629
theorem B1872275 : Blo 1871637 1872275 := bstep (se 1 (by rfl) ⟨1404206, by rfl⟩ : syracuseStep 1872275 = 2808413) B2808413
theorem B1872291 : Blo 1871637 1872291 := bstep (se 1 (by rfl) ⟨1404218, by rfl⟩ : syracuseStep 1872291 = 2808437) B2808437
theorem B4215203 : Blo 1871637 4215203 := bstep (se 1 (by rfl) ⟨3161402, by rfl⟩ : syracuseStep 4215203 = 6322805) B6322805
theorem B1872307 : Blo 1871637 1872307 := bstep (se 1 (by rfl) ⟨1404230, by rfl⟩ : syracuseStep 1872307 = 2808461) B2808461
theorem B1872323 : Blo 1871637 1872323 := bstep (se 1 (by rfl) ⟨1404242, by rfl⟩ : syracuseStep 1872323 = 2808485) B2808485
theorem B1872339 : Blo 1871637 1872339 := bstep (se 1 (by rfl) ⟨1404254, by rfl⟩ : syracuseStep 1872339 = 2808509) B2808509
theorem B2847187 : Blo 1871637 2847187 := bstep (se 1 (by rfl) ⟨2135390, by rfl⟩ : syracuseStep 2847187 = 4270781) B4270781
theorem B1872355 : Blo 1871637 1872355 := bstep (se 1 (by rfl) ⟨1404266, by rfl⟩ : syracuseStep 1872355 = 2808533) B2808533
theorem B1872371 : Blo 1871637 1872371 := bstep (se 1 (by rfl) ⟨1404278, by rfl⟩ : syracuseStep 1872371 = 2808557) B2808557
theorem B1872387 : Blo 1871637 1872387 := bstep (se 1 (by rfl) ⟨1404290, by rfl⟩ : syracuseStep 1872387 = 2808581) B2808581
theorem B8999437 : Blo 1871637 8999437 := bstep (se 3 (by rfl) ⟨1687394, by rfl⟩ : syracuseStep 8999437 = 3374789) B3374789
theorem B1872403 : Blo 1871637 1872403 := bstep (se 1 (by rfl) ⟨1404302, by rfl⟩ : syracuseStep 1872403 = 2808605) B2808605
theorem B3158561 : Blo 1871637 3158561 := bstep (se 2 (by rfl) ⟨1184460, by rfl⟩ : syracuseStep 3158561 = 2368921) B2368921
theorem B1872419 : Blo 1871637 1872419 := bstep (se 1 (by rfl) ⟨1404314, by rfl⟩ : syracuseStep 1872419 = 2808629) B2808629
theorem B1872435 : Blo 1871637 1872435 := bstep (se 1 (by rfl) ⟨1404326, by rfl⟩ : syracuseStep 1872435 = 2808653) B2808653
theorem B1872451 : Blo 1871637 1872451 := bstep (se 1 (by rfl) ⟨1404338, by rfl⟩ : syracuseStep 1872451 = 2808677) B2808677
theorem B1872467 : Blo 1871637 1872467 := bstep (se 1 (by rfl) ⟨1404350, by rfl⟩ : syracuseStep 1872467 = 2808701) B2808701
theorem B1872483 : Blo 1871637 1872483 := bstep (se 1 (by rfl) ⟨1404362, by rfl⟩ : syracuseStep 1872483 = 2808725) B2808725
theorem B6320753 : Blo 1871637 6320753 := bstep (se 2 (by rfl) ⟨2370282, by rfl⟩ : syracuseStep 6320753 = 4740565) B4740565
theorem B6001265 : Blo 1871637 6001265 := bstep (se 2 (by rfl) ⟨2250474, by rfl⟩ : syracuseStep 6001265 = 4500949) B4500949
theorem B1872499 : Blo 1871637 1872499 := bstep (se 1 (by rfl) ⟨1404374, by rfl⟩ : syracuseStep 1872499 = 2808749) B2808749
theorem B1872515 : Blo 1871637 1872515 := bstep (se 1 (by rfl) ⟨1404386, by rfl⟩ : syracuseStep 1872515 = 2808773) B2808773
theorem B21320333 : Blo 1871637 21320333 := bstep (se 3 (by rfl) ⟨3997562, by rfl⟩ : syracuseStep 21320333 = 7995125) B7995125
theorem B1872531 : Blo 1871637 1872531 := bstep (se 1 (by rfl) ⟨1404398, by rfl⟩ : syracuseStep 1872531 = 2808797) B2808797
theorem B3158689 : Blo 1871637 3158689 := bstep (se 2 (by rfl) ⟨1184508, by rfl⟩ : syracuseStep 3158689 = 2369017) B2369017
theorem B1872547 : Blo 1871637 1872547 := bstep (se 1 (by rfl) ⟨1404410, by rfl⟩ : syracuseStep 1872547 = 2808821) B2808821
theorem B2847395 : Blo 1871637 2847395 := bstep (se 1 (by rfl) ⟨2135546, by rfl⟩ : syracuseStep 2847395 = 4271093) B4271093
theorem B4215473 : Blo 1871637 4215473 := bstep (se 2 (by rfl) ⟨1580802, by rfl⟩ : syracuseStep 4215473 = 3161605) B3161605
theorem B1872563 : Blo 1871637 1872563 := bstep (se 1 (by rfl) ⟨1404422, by rfl⟩ : syracuseStep 1872563 = 2808845) B2808845
theorem B3158723 : Blo 1871637 3158723 := bstep (se 1 (by rfl) ⟨2369042, by rfl⟩ : syracuseStep 3158723 = 4738085) B4738085
theorem B1872579 : Blo 1871637 1872579 := bstep (se 1 (by rfl) ⟨1404434, by rfl⟩ : syracuseStep 1872579 = 2808869) B2808869
theorem B4215491 : Blo 1871637 4215491 := bstep (se 1 (by rfl) ⟨3161618, by rfl⟩ : syracuseStep 4215491 = 6323237) B6323237
theorem B1872595 : Blo 1871637 1872595 := bstep (se 1 (by rfl) ⟨1404446, by rfl⟩ : syracuseStep 1872595 = 2808893) B2808893
theorem B1872611 : Blo 1871637 1872611 := bstep (se 1 (by rfl) ⟨1404458, by rfl⟩ : syracuseStep 1872611 = 2808917) B2808917
theorem B9482993 : Blo 1871637 9482993 := bstep (se 2 (by rfl) ⟨3556122, by rfl⟩ : syracuseStep 9482993 = 7112245) B7112245
theorem B1872627 : Blo 1871637 1872627 := bstep (se 1 (by rfl) ⟨1404470, by rfl⟩ : syracuseStep 1872627 = 2808941) B2808941
theorem B1872643 : Blo 1871637 1872643 := bstep (se 1 (by rfl) ⟨1404482, by rfl⟩ : syracuseStep 1872643 = 2808965) B2808965
theorem B1872659 : Blo 1871637 1872659 := bstep (se 1 (by rfl) ⟨1404494, by rfl⟩ : syracuseStep 1872659 = 2808989) B2808989
theorem B1872675 : Blo 1871637 1872675 := bstep (se 1 (by rfl) ⟨1404506, by rfl⟩ : syracuseStep 1872675 = 2809013) B2809013
theorem B1872691 : Blo 1871637 1872691 := bstep (se 1 (by rfl) ⟨1404518, by rfl⟩ : syracuseStep 1872691 = 2809037) B2809037
theorem B20247349 : Blo 1871637 20247349 := bstep (se 5 (by rfl) ⟨949094, by rfl⟩ : syracuseStep 20247349 = 1898189) B1898189
theorem B3158851 : Blo 1871637 3158851 := bstep (se 1 (by rfl) ⟨2369138, by rfl⟩ : syracuseStep 3158851 = 4738277) B4738277
theorem B1872707 : Blo 1871637 1872707 := bstep (se 1 (by rfl) ⟨1404530, by rfl⟩ : syracuseStep 1872707 = 2809061) B2809061
theorem B1872723 : Blo 1871637 1872723 := bstep (se 1 (by rfl) ⟨1404542, by rfl⟩ : syracuseStep 1872723 = 2809085) B2809085
theorem B1872739 : Blo 1871637 1872739 := bstep (se 1 (by rfl) ⟨1404554, by rfl⟩ : syracuseStep 1872739 = 2809109) B2809109
theorem B2667377 : Blo 1871637 2667377 := bstep (se 2 (by rfl) ⟨1000266, by rfl⟩ : syracuseStep 2667377 = 2000533) B2000533
theorem B1872755 : Blo 1871637 1872755 := bstep (se 1 (by rfl) ⟨1404566, by rfl⟩ : syracuseStep 1872755 = 2809133) B2809133
theorem B1872771 : Blo 1871637 1872771 := bstep (se 1 (by rfl) ⟨1404578, by rfl⟩ : syracuseStep 1872771 = 2809157) B2809157
theorem B7590797 : Blo 1871637 7590797 := bstep (se 3 (by rfl) ⟨1423274, by rfl⟩ : syracuseStep 7590797 = 2846549) B2846549
theorem B1872787 : Blo 1871637 1872787 := bstep (se 1 (by rfl) ⟨1404590, by rfl⟩ : syracuseStep 1872787 = 2809181) B2809181
theorem B1872803 : Blo 1871637 1872803 := bstep (se 1 (by rfl) ⟨1404602, by rfl⟩ : syracuseStep 1872803 = 2809205) B2809205
theorem B1872819 : Blo 1871637 1872819 := bstep (se 1 (by rfl) ⟨1404614, by rfl⟩ : syracuseStep 1872819 = 2809229) B2809229
theorem B1872835 : Blo 1871637 1872835 := bstep (se 1 (by rfl) ⟨1404626, by rfl⟩ : syracuseStep 1872835 = 2809253) B2809253
theorem B3158993 : Blo 1871637 3158993 := bstep (se 2 (by rfl) ⟨1184622, by rfl⟩ : syracuseStep 3158993 = 2369245) B2369245
theorem B1872851 : Blo 1871637 1872851 := bstep (se 1 (by rfl) ⟨1404638, by rfl⟩ : syracuseStep 1872851 = 2809277) B2809277
theorem B1872867 : Blo 1871637 1872867 := bstep (se 1 (by rfl) ⟨1404650, by rfl⟩ : syracuseStep 1872867 = 2809301) B2809301
theorem B5329901 : Blo 1871637 5329901 := bstep (se 3 (by rfl) ⟨999356, by rfl⟩ : syracuseStep 5329901 = 1998713) B1998713
theorem B1872883 : Blo 1871637 1872883 := bstep (se 1 (by rfl) ⟨1404662, by rfl⟩ : syracuseStep 1872883 = 2809325) B2809325
theorem B1872899 : Blo 1871637 1872899 := bstep (se 1 (by rfl) ⟨1404674, by rfl⟩ : syracuseStep 1872899 = 2809349) B2809349
theorem B8000525 : Blo 1871637 8000525 := bstep (se 3 (by rfl) ⟨1500098, by rfl⟩ : syracuseStep 8000525 = 3000197) B3000197
theorem B1872915 : Blo 1871637 1872915 := bstep (se 1 (by rfl) ⟨1404686, by rfl⟩ : syracuseStep 1872915 = 2809373) B2809373
theorem B10662947 : Blo 1871637 10662947 := bstep (se 1 (by rfl) ⟨7997210, by rfl⟩ : syracuseStep 10662947 = 15994421) B15994421
theorem B1872931 : Blo 1871637 1872931 := bstep (se 1 (by rfl) ⟨1404698, by rfl⟩ : syracuseStep 1872931 = 2809397) B2809397
theorem B1872947 : Blo 1871637 1872947 := bstep (se 1 (by rfl) ⟨1404710, by rfl⟩ : syracuseStep 1872947 = 2809421) B2809421
theorem B1872963 : Blo 1871637 1872963 := bstep (se 1 (by rfl) ⟨1404722, by rfl⟩ : syracuseStep 1872963 = 2809445) B2809445
theorem B11998277 : Blo 1871637 11998277 := bstep (se 4 (by rfl) ⟨1124838, by rfl⟩ : syracuseStep 11998277 = 2249677) B2249677
theorem B9606221 : Blo 1871637 9606221 := bstep (se 3 (by rfl) ⟨1801166, by rfl⟩ : syracuseStep 9606221 = 3602333) B3602333
theorem B3159121 : Blo 1871637 3159121 := bstep (se 2 (by rfl) ⟨1184670, by rfl⟩ : syracuseStep 3159121 = 2369341) B2369341
theorem B1872979 : Blo 1871637 1872979 := bstep (se 1 (by rfl) ⟨1404734, by rfl⟩ : syracuseStep 1872979 = 2809469) B2809469
theorem B1872995 : Blo 1871637 1872995 := bstep (se 1 (by rfl) ⟨1404746, by rfl⟩ : syracuseStep 1872995 = 2809493) B2809493
theorem B3159155 : Blo 1871637 3159155 := bstep (se 1 (by rfl) ⟨2369366, by rfl⟩ : syracuseStep 3159155 = 4738733) B4738733
theorem B1873011 : Blo 1871637 1873011 := bstep (se 1 (by rfl) ⟨1404758, by rfl⟩ : syracuseStep 1873011 = 2809517) B2809517
theorem B2135171 : Blo 1871637 2135171 := bstep (se 1 (by rfl) ⟨1601378, by rfl⟩ : syracuseStep 2135171 = 3202757) B3202757
theorem B1873027 : Blo 1871637 1873027 := bstep (se 1 (by rfl) ⟨1404770, by rfl⟩ : syracuseStep 1873027 = 2809541) B2809541
theorem B6321293 : Blo 1871637 6321293 := bstep (se 3 (by rfl) ⟨1185242, by rfl⟩ : syracuseStep 6321293 = 2370485) B2370485
theorem B4740241 : Blo 1871637 4740241 := bstep (se 2 (by rfl) ⟨1777590, by rfl⟩ : syracuseStep 4740241 = 3555181) B3555181
theorem B4805777 : Blo 1871637 4805777 := bstep (se 2 (by rfl) ⟨1802166, by rfl⟩ : syracuseStep 4805777 = 3604333) B3604333
theorem B1873043 : Blo 1871637 1873043 := bstep (se 1 (by rfl) ⟨1404782, by rfl⟩ : syracuseStep 1873043 = 2809565) B2809565
theorem B1873059 : Blo 1871637 1873059 := bstep (se 1 (by rfl) ⟨1404794, by rfl⟩ : syracuseStep 1873059 = 2809589) B2809589
theorem B1873075 : Blo 1871637 1873075 := bstep (se 1 (by rfl) ⟨1404806, by rfl⟩ : syracuseStep 1873075 = 2809613) B2809613
theorem B6321347 : Blo 1871637 6321347 := bstep (se 1 (by rfl) ⟨4741010, by rfl⟩ : syracuseStep 6321347 = 9482021) B9482021
theorem B1873091 : Blo 1871637 1873091 := bstep (se 1 (by rfl) ⟨1404818, by rfl⟩ : syracuseStep 1873091 = 2809637) B2809637
theorem B1873107 : Blo 1871637 1873107 := bstep (se 1 (by rfl) ⟨1404830, by rfl⟩ : syracuseStep 1873107 = 2809661) B2809661
theorem B1873123 : Blo 1871637 1873123 := bstep (se 1 (by rfl) ⟨1404842, by rfl⟩ : syracuseStep 1873123 = 2809685) B2809685
theorem B3159283 : Blo 1871637 3159283 := bstep (se 1 (by rfl) ⟨2369462, by rfl⟩ : syracuseStep 3159283 = 4738925) B4738925
theorem B1873139 : Blo 1871637 1873139 := bstep (se 1 (by rfl) ⟨1404854, by rfl⟩ : syracuseStep 1873139 = 2809709) B2809709
theorem B1873155 : Blo 1871637 1873155 := bstep (se 1 (by rfl) ⟨1404866, by rfl⟩ : syracuseStep 1873155 = 2809733) B2809733
theorem B1873171 : Blo 1871637 1873171 := bstep (se 1 (by rfl) ⟨1404878, by rfl⟩ : syracuseStep 1873171 = 2809757) B2809757
theorem B1873187 : Blo 1871637 1873187 := bstep (se 1 (by rfl) ⟨1404890, by rfl⟩ : syracuseStep 1873187 = 2809781) B2809781
theorem B1873203 : Blo 1871637 1873203 := bstep (se 1 (by rfl) ⟨1404902, by rfl⟩ : syracuseStep 1873203 = 2809805) B2809805
theorem B1873219 : Blo 1871637 1873219 := bstep (se 1 (by rfl) ⟨1404914, by rfl⟩ : syracuseStep 1873219 = 2809829) B2809829
theorem B1873235 : Blo 1871637 1873235 := bstep (se 1 (by rfl) ⟨1404926, by rfl⟩ : syracuseStep 1873235 = 2809853) B2809853
theorem B1873251 : Blo 1871637 1873251 := bstep (se 1 (by rfl) ⟨1404938, by rfl⟩ : syracuseStep 1873251 = 2809877) B2809877
theorem B1873267 : Blo 1871637 1873267 := bstep (se 1 (by rfl) ⟨1404950, by rfl⟩ : syracuseStep 1873267 = 2809901) B2809901
theorem B3159425 : Blo 1871637 3159425 := bstep (se 2 (by rfl) ⟨1184784, by rfl⟩ : syracuseStep 3159425 = 2369569) B2369569
theorem B1873283 : Blo 1871637 1873283 := bstep (se 1 (by rfl) ⟨1404962, by rfl⟩ : syracuseStep 1873283 = 2809925) B2809925
theorem B6747533 : Blo 1871637 6747533 := bstep (se 3 (by rfl) ⟨1265162, by rfl⟩ : syracuseStep 6747533 = 2530325) B2530325
theorem B1873299 : Blo 1871637 1873299 := bstep (se 1 (by rfl) ⟨1404974, by rfl⟩ : syracuseStep 1873299 = 2809949) B2809949
theorem B4740515 : Blo 1871637 4740515 := bstep (se 1 (by rfl) ⟨3555386, by rfl⟩ : syracuseStep 4740515 = 7110773) B7110773
theorem B1873315 : Blo 1871637 1873315 := bstep (se 1 (by rfl) ⟨1404986, by rfl⟩ : syracuseStep 1873315 = 2809973) B2809973
theorem B1873331 : Blo 1871637 1873331 := bstep (se 1 (by rfl) ⟨1404998, by rfl⟩ : syracuseStep 1873331 = 2809997) B2809997
theorem B1873347 : Blo 1871637 1873347 := bstep (se 1 (by rfl) ⟨1405010, by rfl⟩ : syracuseStep 1873347 = 2810021) B2810021
theorem B6321617 : Blo 1871637 6321617 := bstep (se 2 (by rfl) ⟨2370606, by rfl⟩ : syracuseStep 6321617 = 4741213) B4741213
theorem B1873363 : Blo 1871637 1873363 := bstep (se 1 (by rfl) ⟨1405022, by rfl⟩ : syracuseStep 1873363 = 2810045) B2810045
theorem B1873379 : Blo 1871637 1873379 := bstep (se 1 (by rfl) ⟨1405034, by rfl⟩ : syracuseStep 1873379 = 2810069) B2810069
theorem B1873395 : Blo 1871637 1873395 := bstep (se 1 (by rfl) ⟨1405046, by rfl⟩ : syracuseStep 1873395 = 2810093) B2810093
theorem B3159553 : Blo 1871637 3159553 := bstep (se 2 (by rfl) ⟨1184832, by rfl⟩ : syracuseStep 3159553 = 2369665) B2369665
theorem B1873411 : Blo 1871637 1873411 := bstep (se 1 (by rfl) ⟨1405058, by rfl⟩ : syracuseStep 1873411 = 2810117) B2810117
theorem B1873427 : Blo 1871637 1873427 := bstep (se 1 (by rfl) ⟨1405070, by rfl⟩ : syracuseStep 1873427 = 2810141) B2810141
theorem B3159587 : Blo 1871637 3159587 := bstep (se 1 (by rfl) ⟨2369690, by rfl⟩ : syracuseStep 3159587 = 4739381) B4739381
theorem B1873443 : Blo 1871637 1873443 := bstep (se 1 (by rfl) ⟨1405082, by rfl⟩ : syracuseStep 1873443 = 2810165) B2810165
theorem B7108145 : Blo 1871637 7108145 := bstep (se 2 (by rfl) ⟨2665554, by rfl⟩ : syracuseStep 7108145 = 5331109) B5331109
theorem B9000497 : Blo 1871637 9000497 := bstep (se 2 (by rfl) ⟨3375186, by rfl⟩ : syracuseStep 9000497 = 6750373) B6750373
theorem B1873459 : Blo 1871637 1873459 := bstep (se 1 (by rfl) ⟨1405094, by rfl⟩ : syracuseStep 1873459 = 2810189) B2810189
theorem B1873475 : Blo 1871637 1873475 := bstep (se 1 (by rfl) ⟨1405106, by rfl⟩ : syracuseStep 1873475 = 2810213) B2810213
theorem B1873491 : Blo 1871637 1873491 := bstep (se 1 (by rfl) ⟨1405118, by rfl⟩ : syracuseStep 1873491 = 2810237) B2810237
theorem B4740707 : Blo 1871637 4740707 := bstep (se 1 (by rfl) ⟨3555530, by rfl⟩ : syracuseStep 4740707 = 7111061) B7111061
theorem B1873507 : Blo 1871637 1873507 := bstep (se 1 (by rfl) ⟨1405130, by rfl⟩ : syracuseStep 1873507 = 2810261) B2810261
theorem B97310321 : Blo 1871637 97310321 := bstep (se 2 (by rfl) ⟨36491370, by rfl⟩ : syracuseStep 97310321 = 72982741) B72982741
theorem B1873523 : Blo 1871637 1873523 := bstep (se 1 (by rfl) ⟨1405142, by rfl⟩ : syracuseStep 1873523 = 2810285) B2810285
theorem B1873539 : Blo 1871637 1873539 := bstep (se 1 (by rfl) ⟨1405154, by rfl⟩ : syracuseStep 1873539 = 2810309) B2810309
theorem B1873555 : Blo 1871637 1873555 := bstep (se 1 (by rfl) ⟨1405166, by rfl⟩ : syracuseStep 1873555 = 2810333) B2810333
theorem B2807459 : Blo 1871637 2807459 := bstep (se 1 (by rfl) ⟨2105594, by rfl⟩ : syracuseStep 2807459 = 4211189) B4211189
theorem B3159715 : Blo 1871637 3159715 := bstep (se 1 (by rfl) ⟨2369786, by rfl⟩ : syracuseStep 3159715 = 4739573) B4739573
theorem B1873571 : Blo 1871637 1873571 := bstep (se 1 (by rfl) ⟨1405178, by rfl⟩ : syracuseStep 1873571 = 2810357) B2810357
theorem B1873587 : Blo 1871637 1873587 := bstep (se 1 (by rfl) ⟨1405190, by rfl⟩ : syracuseStep 1873587 = 2810381) B2810381
theorem B2807489 : Blo 1871637 2807489 := bstep (se 2 (by rfl) ⟨1052808, by rfl⟩ : syracuseStep 2807489 = 2105617) B2105617
theorem B1873603 : Blo 1871637 1873603 := bstep (se 1 (by rfl) ⟨1405202, by rfl⟩ : syracuseStep 1873603 = 2810405) B2810405
theorem B2807507 : Blo 1871637 2807507 := bstep (se 1 (by rfl) ⟨2105630, by rfl⟩ : syracuseStep 2807507 = 4211261) B4211261
theorem B1873619 : Blo 1871637 1873619 := bstep (se 1 (by rfl) ⟨1405214, by rfl⟩ : syracuseStep 1873619 = 2810429) B2810429
theorem B1873635 : Blo 1871637 1873635 := bstep (se 1 (by rfl) ⟨1405226, by rfl⟩ : syracuseStep 1873635 = 2810453) B2810453
theorem B2807537 : Blo 1871637 2807537 := bstep (se 2 (by rfl) ⟨1052826, by rfl⟩ : syracuseStep 2807537 = 2105653) B2105653
theorem B2807555 : Blo 1871637 2807555 := bstep (se 1 (by rfl) ⟨2105666, by rfl⟩ : syracuseStep 2807555 = 4211333) B4211333
theorem B3602179 : Blo 1871637 3602179 := bstep (se 1 (by rfl) ⟨2701634, by rfl⟩ : syracuseStep 3602179 = 5403269) B5403269
theorem B5060369 : Blo 1871637 5060369 := bstep (se 2 (by rfl) ⟨1897638, by rfl⟩ : syracuseStep 5060369 = 3795277) B3795277
theorem B2807585 : Blo 1871637 2807585 := bstep (se 2 (by rfl) ⟨1052844, by rfl⟩ : syracuseStep 2807585 = 2105689) B2105689
theorem B3159857 : Blo 1871637 3159857 := bstep (se 2 (by rfl) ⟨1184946, by rfl⟩ : syracuseStep 3159857 = 2369893) B2369893
theorem B2807603 : Blo 1871637 2807603 := bstep (se 1 (by rfl) ⟨2105702, by rfl⟩ : syracuseStep 2807603 = 4211405) B4211405
theorem B2807633 : Blo 1871637 2807633 := bstep (se 2 (by rfl) ⟨1052862, by rfl⟩ : syracuseStep 2807633 = 2105725) B2105725
theorem B2807651 : Blo 1871637 2807651 := bstep (se 1 (by rfl) ⟨2105738, by rfl⟩ : syracuseStep 2807651 = 4211477) B4211477
theorem B2807681 : Blo 1871637 2807681 := bstep (se 2 (by rfl) ⟨1052880, by rfl⟩ : syracuseStep 2807681 = 2105761) B2105761
theorem B2807699 : Blo 1871637 2807699 := bstep (se 1 (by rfl) ⟨2105774, by rfl⟩ : syracuseStep 2807699 = 4211549) B4211549
theorem B2807729 : Blo 1871637 2807729 := bstep (se 2 (by rfl) ⟨1052898, by rfl⟩ : syracuseStep 2807729 = 2105797) B2105797
theorem B3159985 : Blo 1871637 3159985 := bstep (se 2 (by rfl) ⟨1184994, by rfl⟩ : syracuseStep 3159985 = 2369989) B2369989
theorem B2807747 : Blo 1871637 2807747 := bstep (se 1 (by rfl) ⟨2105810, by rfl⟩ : syracuseStep 2807747 = 4211621) B4211621
theorem B5330893 : Blo 1871637 5330893 := bstep (se 3 (by rfl) ⟨999542, by rfl⟩ : syracuseStep 5330893 = 1999085) B1999085
theorem B3160019 : Blo 1871637 3160019 := bstep (se 1 (by rfl) ⟨2370014, by rfl⟩ : syracuseStep 3160019 = 4740029) B4740029
theorem B2807777 : Blo 1871637 2807777 := bstep (se 2 (by rfl) ⟨1052916, by rfl⟩ : syracuseStep 2807777 = 2105833) B2105833
theorem B23984099 : Blo 1871637 23984099 := bstep (se 1 (by rfl) ⟨17988074, by rfl⟩ : syracuseStep 23984099 = 35976149) B35976149
theorem B6322157 : Blo 1871637 6322157 := bstep (se 3 (by rfl) ⟨1185404, by rfl⟩ : syracuseStep 6322157 = 2370809) B2370809
theorem B2807795 : Blo 1871637 2807795 := bstep (se 1 (by rfl) ⟨2105846, by rfl⟩ : syracuseStep 2807795 = 4211693) B4211693
theorem B3553283 : Blo 1871637 3553283 := bstep (se 1 (by rfl) ⟨2664962, by rfl⟩ : syracuseStep 3553283 = 5329925) B5329925
theorem B2807825 : Blo 1871637 2807825 := bstep (se 2 (by rfl) ⟨1052934, by rfl⟩ : syracuseStep 2807825 = 2105869) B2105869
theorem B2807843 : Blo 1871637 2807843 := bstep (se 1 (by rfl) ⟨2105882, by rfl⟩ : syracuseStep 2807843 = 4211765) B4211765
theorem B6322211 : Blo 1871637 6322211 := bstep (se 1 (by rfl) ⟨4741658, by rfl⟩ : syracuseStep 6322211 = 9483317) B9483317
theorem B2807873 : Blo 1871637 2807873 := bstep (se 2 (by rfl) ⟨1052952, by rfl⟩ : syracuseStep 2807873 = 2105905) B2105905
theorem B2807891 : Blo 1871637 2807891 := bstep (se 1 (by rfl) ⟨2105918, by rfl⟩ : syracuseStep 2807891 = 4211837) B4211837
theorem B3160147 : Blo 1871637 3160147 := bstep (se 1 (by rfl) ⟨2370110, by rfl⟩ : syracuseStep 3160147 = 4740221) B4740221
theorem B2807921 : Blo 1871637 2807921 := bstep (se 2 (by rfl) ⟨1052970, by rfl⟩ : syracuseStep 2807921 = 2105941) B2105941
theorem B2807939 : Blo 1871637 2807939 := bstep (se 1 (by rfl) ⟨2105954, by rfl⟩ : syracuseStep 2807939 = 4211909) B4211909
theorem B2807969 : Blo 1871637 2807969 := bstep (se 2 (by rfl) ⟨1052988, by rfl⟩ : syracuseStep 2807969 = 2105977) B2105977
theorem B9484451 : Blo 1871637 9484451 := bstep (se 1 (by rfl) ⟨7113338, by rfl⟩ : syracuseStep 9484451 = 14226677) B14226677
theorem B2807987 : Blo 1871637 2807987 := bstep (se 1 (by rfl) ⟨2105990, by rfl⟩ : syracuseStep 2807987 = 4211981) B4211981
theorem B2808017 : Blo 1871637 2808017 := bstep (se 2 (by rfl) ⟨1053006, by rfl⟩ : syracuseStep 2808017 = 2106013) B2106013
theorem B3160289 : Blo 1871637 3160289 := bstep (se 2 (by rfl) ⟨1185108, by rfl⟩ : syracuseStep 3160289 = 2370217) B2370217
theorem B2808035 : Blo 1871637 2808035 := bstep (se 1 (by rfl) ⟨2106026, by rfl⟩ : syracuseStep 2808035 = 4212053) B4212053
theorem B2808065 : Blo 1871637 2808065 := bstep (se 2 (by rfl) ⟨1053024, by rfl⟩ : syracuseStep 2808065 = 2106049) B2106049
theorem B20257037 : Blo 1871637 20257037 := bstep (se 3 (by rfl) ⟨3798194, by rfl⟩ : syracuseStep 20257037 = 7596389) B7596389
theorem B2808083 : Blo 1871637 2808083 := bstep (se 1 (by rfl) ⟨2106062, by rfl⟩ : syracuseStep 2808083 = 4212125) B4212125
theorem B3553571 : Blo 1871637 3553571 := bstep (se 1 (by rfl) ⟨2665178, by rfl⟩ : syracuseStep 3553571 = 5330357) B5330357
theorem B2808113 : Blo 1871637 2808113 := bstep (se 2 (by rfl) ⟨1053042, by rfl⟩ : syracuseStep 2808113 = 2106085) B2106085
theorem B6322481 : Blo 1871637 6322481 := bstep (se 2 (by rfl) ⟨2370930, by rfl⟩ : syracuseStep 6322481 = 4741861) B4741861
theorem B2808131 : Blo 1871637 2808131 := bstep (se 1 (by rfl) ⟨2106098, by rfl⟩ : syracuseStep 2808131 = 4212197) B4212197
theorem B10123589 : Blo 1871637 10123589 := bstep (se 4 (by rfl) ⟨949086, by rfl⟩ : syracuseStep 10123589 = 1898173) B1898173
theorem B2808161 : Blo 1871637 2808161 := bstep (se 2 (by rfl) ⟨1053060, by rfl⟩ : syracuseStep 2808161 = 2106121) B2106121
theorem B3160417 : Blo 1871637 3160417 := bstep (se 2 (by rfl) ⟨1185156, by rfl⟩ : syracuseStep 3160417 = 2370313) B2370313
theorem B2808179 : Blo 1871637 2808179 := bstep (se 1 (by rfl) ⟨2106134, by rfl⟩ : syracuseStep 2808179 = 4212269) B4212269
theorem B3160451 : Blo 1871637 3160451 := bstep (se 1 (by rfl) ⟨2370338, by rfl⟩ : syracuseStep 3160451 = 4740677) B4740677
theorem B2808209 : Blo 1871637 2808209 := bstep (se 2 (by rfl) ⟨1053078, by rfl⟩ : syracuseStep 2808209 = 2106157) B2106157
theorem B2808227 : Blo 1871637 2808227 := bstep (se 1 (by rfl) ⟨2106170, by rfl⟩ : syracuseStep 2808227 = 4212341) B4212341
theorem B23992757 : Blo 1871637 23992757 := bstep (se 5 (by rfl) ⟨1124660, by rfl⟩ : syracuseStep 23992757 = 2249321) B2249321
theorem B2808257 : Blo 1871637 2808257 := bstep (se 2 (by rfl) ⟨1053096, by rfl⟩ : syracuseStep 2808257 = 2106193) B2106193
theorem B2808275 : Blo 1871637 2808275 := bstep (se 1 (by rfl) ⟨2106206, by rfl⟩ : syracuseStep 2808275 = 4212413) B4212413
theorem B20240867 : Blo 1871637 20240867 := bstep (se 1 (by rfl) ⟨15180650, by rfl⟩ : syracuseStep 20240867 = 30361301) B30361301
theorem B2808305 : Blo 1871637 2808305 := bstep (se 2 (by rfl) ⟨1053114, by rfl⟩ : syracuseStep 2808305 = 2106229) B2106229
theorem B2808323 : Blo 1871637 2808323 := bstep (se 1 (by rfl) ⟨2106242, by rfl⟩ : syracuseStep 2808323 = 4212485) B4212485
theorem B3160579 : Blo 1871637 3160579 := bstep (se 1 (by rfl) ⟨2370434, by rfl⟩ : syracuseStep 3160579 = 4740869) B4740869
theorem B4741649 : Blo 1871637 4741649 := bstep (se 2 (by rfl) ⟨1778118, by rfl⟩ : syracuseStep 4741649 = 3556237) B3556237
theorem B2808353 : Blo 1871637 2808353 := bstep (se 2 (by rfl) ⟨1053132, by rfl⟩ : syracuseStep 2808353 = 2106265) B2106265
theorem B8002097 : Blo 1871637 8002097 := bstep (se 2 (by rfl) ⟨3000786, by rfl⟩ : syracuseStep 8002097 = 6001573) B6001573
theorem B2808371 : Blo 1871637 2808371 := bstep (se 1 (by rfl) ⟨2106278, by rfl⟩ : syracuseStep 2808371 = 4212557) B4212557
theorem B4741699 : Blo 1871637 4741699 := bstep (se 1 (by rfl) ⟨3556274, by rfl⟩ : syracuseStep 4741699 = 7112549) B7112549
theorem B2808401 : Blo 1871637 2808401 := bstep (se 2 (by rfl) ⟨1053150, by rfl⟩ : syracuseStep 2808401 = 2106301) B2106301
theorem B2808419 : Blo 1871637 2808419 := bstep (se 1 (by rfl) ⟨2106314, by rfl⟩ : syracuseStep 2808419 = 4212629) B4212629
theorem B6748771 : Blo 1871637 6748771 := bstep (se 1 (by rfl) ⟨5061578, by rfl⟩ : syracuseStep 6748771 = 10123157) B10123157
theorem B2808449 : Blo 1871637 2808449 := bstep (se 2 (by rfl) ⟨1053168, by rfl⟩ : syracuseStep 2808449 = 2106337) B2106337
theorem B3160721 : Blo 1871637 3160721 := bstep (se 2 (by rfl) ⟨1185270, by rfl⟩ : syracuseStep 3160721 = 2370541) B2370541
theorem B2808467 : Blo 1871637 2808467 := bstep (se 1 (by rfl) ⟨2106350, by rfl⟩ : syracuseStep 2808467 = 4212701) B4212701
theorem B2808497 : Blo 1871637 2808497 := bstep (se 2 (by rfl) ⟨1053186, by rfl⟩ : syracuseStep 2808497 = 2106373) B2106373
theorem B2808515 : Blo 1871637 2808515 := bstep (se 1 (by rfl) ⟨2106386, by rfl⟩ : syracuseStep 2808515 = 4212773) B4212773
theorem B4741841 : Blo 1871637 4741841 := bstep (se 2 (by rfl) ⟨1778190, by rfl⟩ : syracuseStep 4741841 = 3556381) B3556381
theorem B2808545 : Blo 1871637 2808545 := bstep (se 2 (by rfl) ⟨1053204, by rfl⟩ : syracuseStep 2808545 = 2106409) B2106409
theorem B2808563 : Blo 1871637 2808563 := bstep (se 1 (by rfl) ⟨2106422, by rfl⟩ : syracuseStep 2808563 = 4212845) B4212845
theorem B14408461 : Blo 1871637 14408461 := bstep (se 3 (by rfl) ⟨2701586, by rfl⟩ : syracuseStep 14408461 = 5403173) B5403173
theorem B2808593 : Blo 1871637 2808593 := bstep (se 2 (by rfl) ⟨1053222, by rfl⟩ : syracuseStep 2808593 = 2106445) B2106445
theorem B3160849 : Blo 1871637 3160849 := bstep (se 2 (by rfl) ⟨1185318, by rfl⟩ : syracuseStep 3160849 = 2370637) B2370637
theorem B2808611 : Blo 1871637 2808611 := bstep (se 1 (by rfl) ⟨2106458, by rfl⟩ : syracuseStep 2808611 = 4212917) B4212917
theorem B2530097 : Blo 1871637 2530097 := bstep (se 2 (by rfl) ⟨948786, by rfl⟩ : syracuseStep 2530097 = 1897573) B1897573
theorem B3160883 : Blo 1871637 3160883 := bstep (se 1 (by rfl) ⟨2370662, by rfl⟩ : syracuseStep 3160883 = 4741325) B4741325
theorem B2808641 : Blo 1871637 2808641 := bstep (se 2 (by rfl) ⟨1053240, by rfl⟩ : syracuseStep 2808641 = 2106481) B2106481
theorem B6323021 : Blo 1871637 6323021 := bstep (se 3 (by rfl) ⟨1185566, by rfl⟩ : syracuseStep 6323021 = 2371133) B2371133
theorem B2808659 : Blo 1871637 2808659 := bstep (se 1 (by rfl) ⟨2106494, by rfl⟩ : syracuseStep 2808659 = 4212989) B4212989
theorem B2808689 : Blo 1871637 2808689 := bstep (se 2 (by rfl) ⟨1053258, by rfl⟩ : syracuseStep 2808689 = 2106517) B2106517
theorem B2530163 : Blo 1871637 2530163 := bstep (se 1 (by rfl) ⟨1897622, by rfl⟩ : syracuseStep 2530163 = 3795245) B3795245
theorem B2808707 : Blo 1871637 2808707 := bstep (se 1 (by rfl) ⟨2106530, by rfl⟩ : syracuseStep 2808707 = 4213061) B4213061
theorem B6323075 : Blo 1871637 6323075 := bstep (se 1 (by rfl) ⟨4742306, by rfl⟩ : syracuseStep 6323075 = 9484613) B9484613
theorem B2808737 : Blo 1871637 2808737 := bstep (se 2 (by rfl) ⟨1053276, by rfl⟩ : syracuseStep 2808737 = 2106553) B2106553
theorem B2808755 : Blo 1871637 2808755 := bstep (se 1 (by rfl) ⟨2106566, by rfl⟩ : syracuseStep 2808755 = 4213133) B4213133
theorem B3161011 : Blo 1871637 3161011 := bstep (se 1 (by rfl) ⟨2370758, by rfl⟩ : syracuseStep 3161011 = 4741517) B4741517
theorem B9485261 : Blo 1871637 9485261 := bstep (se 3 (by rfl) ⟨1778486, by rfl⟩ : syracuseStep 9485261 = 3556973) B3556973
theorem B2808785 : Blo 1871637 2808785 := bstep (se 2 (by rfl) ⟨1053294, by rfl⟩ : syracuseStep 2808785 = 2106589) B2106589
theorem B7109603 : Blo 1871637 7109603 := bstep (se 1 (by rfl) ⟨5332202, by rfl⟩ : syracuseStep 7109603 = 10664405) B10664405
theorem B2808803 : Blo 1871637 2808803 := bstep (se 1 (by rfl) ⟨2106602, by rfl⟩ : syracuseStep 2808803 = 4213205) B4213205
theorem B2808833 : Blo 1871637 2808833 := bstep (se 2 (by rfl) ⟨1053312, by rfl⟩ : syracuseStep 2808833 = 2106625) B2106625
theorem B2808851 : Blo 1871637 2808851 := bstep (se 1 (by rfl) ⟨2106638, by rfl⟩ : syracuseStep 2808851 = 4213277) B4213277
theorem B6749219 : Blo 1871637 6749219 := bstep (se 1 (by rfl) ⟨5061914, by rfl⟩ : syracuseStep 6749219 = 10123829) B10123829
theorem B2808881 : Blo 1871637 2808881 := bstep (se 2 (by rfl) ⟨1053330, by rfl⟩ : syracuseStep 2808881 = 2106661) B2106661
theorem B3161153 : Blo 1871637 3161153 := bstep (se 2 (by rfl) ⟨1185432, by rfl⟩ : syracuseStep 3161153 = 2370865) B2370865
theorem B2808899 : Blo 1871637 2808899 := bstep (se 1 (by rfl) ⟨2106674, by rfl⟩ : syracuseStep 2808899 = 4213349) B4213349
theorem B2808929 : Blo 1871637 2808929 := bstep (se 2 (by rfl) ⟨1053348, by rfl⟩ : syracuseStep 2808929 = 2106697) B2106697
theorem B2808947 : Blo 1871637 2808947 := bstep (se 1 (by rfl) ⟨2106710, by rfl⟩ : syracuseStep 2808947 = 4213421) B4213421
theorem B2808977 : Blo 1871637 2808977 := bstep (se 2 (by rfl) ⟨1053366, by rfl⟩ : syracuseStep 2808977 = 2106733) B2106733
theorem B6323345 : Blo 1871637 6323345 := bstep (se 2 (by rfl) ⟨2371254, by rfl⟩ : syracuseStep 6323345 = 4742509) B4742509
theorem B2808995 : Blo 1871637 2808995 := bstep (se 1 (by rfl) ⟨2106746, by rfl⟩ : syracuseStep 2808995 = 4213493) B4213493
theorem B2809025 : Blo 1871637 2809025 := bstep (se 2 (by rfl) ⟨1053384, by rfl⟩ : syracuseStep 2809025 = 2106769) B2106769
theorem B3161281 : Blo 1871637 3161281 := bstep (se 2 (by rfl) ⟨1185480, by rfl⟩ : syracuseStep 3161281 = 2370961) B2370961
theorem B3554513 : Blo 1871637 3554513 := bstep (se 2 (by rfl) ⟨1332942, by rfl⟩ : syracuseStep 3554513 = 2665885) B2665885
theorem B2809043 : Blo 1871637 2809043 := bstep (se 1 (by rfl) ⟨2106782, by rfl⟩ : syracuseStep 2809043 = 4213565) B4213565
theorem B3161315 : Blo 1871637 3161315 := bstep (se 1 (by rfl) ⟨2370986, by rfl⟩ : syracuseStep 3161315 = 4741973) B4741973
theorem B2809073 : Blo 1871637 2809073 := bstep (se 2 (by rfl) ⟨1053402, by rfl⟩ : syracuseStep 2809073 = 2106805) B2106805
theorem B2809091 : Blo 1871637 2809091 := bstep (se 1 (by rfl) ⟨2106818, by rfl⟩ : syracuseStep 2809091 = 4213637) B4213637
theorem B2809121 : Blo 1871637 2809121 := bstep (se 2 (by rfl) ⟨1053420, by rfl⟩ : syracuseStep 2809121 = 2106841) B2106841
theorem B2809139 : Blo 1871637 2809139 := bstep (se 1 (by rfl) ⟨2106854, by rfl⟩ : syracuseStep 2809139 = 4213709) B4213709
theorem B2809169 : Blo 1871637 2809169 := bstep (se 2 (by rfl) ⟨1053438, by rfl⟩ : syracuseStep 2809169 = 2106877) B2106877
theorem B2809187 : Blo 1871637 2809187 := bstep (se 1 (by rfl) ⟨2106890, by rfl⟩ : syracuseStep 2809187 = 4213781) B4213781
theorem B3161443 : Blo 1871637 3161443 := bstep (se 1 (by rfl) ⟨2371082, by rfl⟩ : syracuseStep 3161443 = 4742165) B4742165
theorem B2809217 : Blo 1871637 2809217 := bstep (se 2 (by rfl) ⟨1053456, by rfl⟩ : syracuseStep 2809217 = 2106913) B2106913
theorem B2809235 : Blo 1871637 2809235 := bstep (se 1 (by rfl) ⟨2106926, by rfl⟩ : syracuseStep 2809235 = 4213853) B4213853
theorem B2809265 : Blo 1871637 2809265 := bstep (se 2 (by rfl) ⟨1053474, by rfl⟩ : syracuseStep 2809265 = 2106949) B2106949
theorem B2809283 : Blo 1871637 2809283 := bstep (se 1 (by rfl) ⟨2106962, by rfl⟩ : syracuseStep 2809283 = 4213925) B4213925
theorem B2809313 : Blo 1871637 2809313 := bstep (se 2 (by rfl) ⟨1053492, by rfl⟩ : syracuseStep 2809313 = 2106985) B2106985
theorem B21323249 : Blo 1871637 21323249 := bstep (se 2 (by rfl) ⟨7996218, by rfl⟩ : syracuseStep 21323249 = 15992437) B15992437
theorem B2530801 : Blo 1871637 2530801 := bstep (se 2 (by rfl) ⟨949050, by rfl⟩ : syracuseStep 2530801 = 1898101) B1898101
theorem B2809331 : Blo 1871637 2809331 := bstep (se 1 (by rfl) ⟨2106998, by rfl⟩ : syracuseStep 2809331 = 4213997) B4213997
theorem B18005489 : Blo 1871637 18005489 := bstep (se 2 (by rfl) ⟨6752058, by rfl⟩ : syracuseStep 18005489 = 13504117) B13504117
theorem B3161585 : Blo 1871637 3161585 := bstep (se 2 (by rfl) ⟨1185594, by rfl⟩ : syracuseStep 3161585 = 2371189) B2371189
theorem B2809361 : Blo 1871637 2809361 := bstep (se 2 (by rfl) ⟨1053510, by rfl⟩ : syracuseStep 2809361 = 2107021) B2107021
theorem B5692963 : Blo 1871637 5692963 := bstep (se 1 (by rfl) ⟨4269722, by rfl⟩ : syracuseStep 5692963 = 8539445) B8539445
theorem B2809379 : Blo 1871637 2809379 := bstep (se 1 (by rfl) ⟨2107034, by rfl⟩ : syracuseStep 2809379 = 4214069) B4214069
theorem B2809409 : Blo 1871637 2809409 := bstep (se 2 (by rfl) ⟨1053528, by rfl⟩ : syracuseStep 2809409 = 2107057) B2107057
theorem B2809427 : Blo 1871637 2809427 := bstep (se 1 (by rfl) ⟨2107070, by rfl⟩ : syracuseStep 2809427 = 4214141) B4214141
theorem B2809457 : Blo 1871637 2809457 := bstep (se 2 (by rfl) ⟨1053546, by rfl⟩ : syracuseStep 2809457 = 2107093) B2107093
theorem B3161713 : Blo 1871637 3161713 := bstep (se 2 (by rfl) ⟨1185642, by rfl⟩ : syracuseStep 3161713 = 2371285) B2371285
theorem B2809475 : Blo 1871637 2809475 := bstep (se 1 (by rfl) ⟨2107106, by rfl⟩ : syracuseStep 2809475 = 4214213) B4214213
theorem B24002189 : Blo 1871637 24002189 := bstep (se 3 (by rfl) ⟨4500410, by rfl⟩ : syracuseStep 24002189 = 9000821) B9000821
theorem B5332625 : Blo 1871637 5332625 := bstep (se 2 (by rfl) ⟨1999734, by rfl⟩ : syracuseStep 5332625 = 3999469) B3999469
theorem B2530963 : Blo 1871637 2530963 := bstep (se 1 (by rfl) ⟨1898222, by rfl⟩ : syracuseStep 2530963 = 3796445) B3796445
theorem B3161747 : Blo 1871637 3161747 := bstep (se 1 (by rfl) ⟨2371310, by rfl⟩ : syracuseStep 3161747 = 4742621) B4742621
theorem B2809505 : Blo 1871637 2809505 := bstep (se 2 (by rfl) ⟨1053564, by rfl⟩ : syracuseStep 2809505 = 2107129) B2107129
theorem B9477809 : Blo 1871637 9477809 := bstep (se 2 (by rfl) ⟨3554178, by rfl⟩ : syracuseStep 9477809 = 7108357) B7108357
theorem B2809523 : Blo 1871637 2809523 := bstep (se 1 (by rfl) ⟨2107142, by rfl⟩ : syracuseStep 2809523 = 4214285) B4214285
theorem B2809553 : Blo 1871637 2809553 := bstep (se 2 (by rfl) ⟨1053582, by rfl⟩ : syracuseStep 2809553 = 2107165) B2107165
theorem B2809571 : Blo 1871637 2809571 := bstep (se 1 (by rfl) ⟨2107178, by rfl⟩ : syracuseStep 2809571 = 4214357) B4214357
theorem B2809601 : Blo 1871637 2809601 := bstep (se 2 (by rfl) ⟨1053600, by rfl⟩ : syracuseStep 2809601 = 2107201) B2107201
theorem B2998019 : Blo 1871637 2998019 := bstep (se 1 (by rfl) ⟨2248514, by rfl⟩ : syracuseStep 2998019 = 4497029) B4497029
theorem B2809619 : Blo 1871637 2809619 := bstep (se 1 (by rfl) ⟨2107214, by rfl⟩ : syracuseStep 2809619 = 4214429) B4214429
theorem B5062445 : Blo 1871637 5062445 := bstep (se 3 (by rfl) ⟨949208, by rfl⟩ : syracuseStep 5062445 = 1898417) B1898417
theorem B2809649 : Blo 1871637 2809649 := bstep (se 2 (by rfl) ⟨1053618, by rfl⟩ : syracuseStep 2809649 = 2107237) B2107237
theorem B2809667 : Blo 1871637 2809667 := bstep (se 1 (by rfl) ⟨2107250, by rfl⟩ : syracuseStep 2809667 = 4214501) B4214501
theorem B5332817 : Blo 1871637 5332817 := bstep (se 2 (by rfl) ⟨1999806, by rfl⟩ : syracuseStep 5332817 = 3999613) B3999613
theorem B2809697 : Blo 1871637 2809697 := bstep (se 2 (by rfl) ⟨1053636, by rfl⟩ : syracuseStep 2809697 = 2107273) B2107273
theorem B2809715 : Blo 1871637 2809715 := bstep (se 1 (by rfl) ⟨2107286, by rfl⟩ : syracuseStep 2809715 = 4214573) B4214573
theorem B2998147 : Blo 1871637 2998147 := bstep (se 1 (by rfl) ⟨2248610, by rfl⟩ : syracuseStep 2998147 = 4497221) B4497221
theorem B2809745 : Blo 1871637 2809745 := bstep (se 2 (by rfl) ⟨1053654, by rfl⟩ : syracuseStep 2809745 = 2107309) B2107309
theorem B2809763 : Blo 1871637 2809763 := bstep (se 1 (by rfl) ⟨2107322, by rfl⟩ : syracuseStep 2809763 = 4214645) B4214645
theorem B10125233 : Blo 1871637 10125233 := bstep (se 2 (by rfl) ⟨3796962, by rfl⟩ : syracuseStep 10125233 = 7593925) B7593925
theorem B2809793 : Blo 1871637 2809793 := bstep (se 2 (by rfl) ⟨1053672, by rfl⟩ : syracuseStep 2809793 = 2107345) B2107345
theorem B7110605 : Blo 1871637 7110605 := bstep (se 3 (by rfl) ⟨1333238, by rfl⟩ : syracuseStep 7110605 = 2666477) B2666477
theorem B3997649 : Blo 1871637 3997649 := bstep (se 2 (by rfl) ⟨1499118, by rfl⟩ : syracuseStep 3997649 = 2998237) B2998237
theorem B2809811 : Blo 1871637 2809811 := bstep (se 1 (by rfl) ⟨2107358, by rfl⟩ : syracuseStep 2809811 = 4214717) B4214717
theorem B2809841 : Blo 1871637 2809841 := bstep (se 2 (by rfl) ⟨1053690, by rfl⟩ : syracuseStep 2809841 = 2107381) B2107381
theorem B15187985 : Blo 1871637 15187985 := bstep (se 2 (by rfl) ⟨5695494, by rfl⟩ : syracuseStep 15187985 = 11390989) B11390989
theorem B20242507 : Blo 1871637 20242507 := bstep (se 1 (by rfl) ⟨15181880, by rfl⟩ : syracuseStep 20242507 = 30363761) B30363761
theorem B2809931 : Blo 1871637 2809931 := bstep (se 1 (by rfl) ⟨2107448, by rfl⟩ : syracuseStep 2809931 = 4214897) B4214897
theorem B2809943 : Blo 1871637 2809943 := bstep (se 1 (by rfl) ⟨2107457, by rfl⟩ : syracuseStep 2809943 = 4214915) B4214915
theorem B7110787 : Blo 1871637 7110787 := bstep (se 1 (by rfl) ⟨5333090, by rfl⟩ : syracuseStep 7110787 = 10666181) B10666181
theorem B9478295 : Blo 1871637 9478295 := bstep (se 1 (by rfl) ⟨7108721, by rfl⟩ : syracuseStep 9478295 = 14217443) B14217443
theorem B2810009 : Blo 1871637 2810009 := bstep (se 2 (by rfl) ⟨1053753, by rfl⟩ : syracuseStep 2810009 = 2107507) B2107507
theorem B3997939 : Blo 1871637 3997939 := bstep (se 1 (by rfl) ⟨2998454, by rfl⟩ : syracuseStep 3997939 = 5996909) B5996909
theorem B2810123 : Blo 1871637 2810123 := bstep (se 1 (by rfl) ⟨2107592, by rfl⟩ : syracuseStep 2810123 = 4215185) B4215185
theorem B2810135 : Blo 1871637 2810135 := bstep (se 1 (by rfl) ⟨2107601, by rfl⟩ : syracuseStep 2810135 = 4215203) B4215203
theorem B3375425 : Blo 1871637 3375425 := bstep (se 2 (by rfl) ⟨1265784, by rfl⟩ : syracuseStep 3375425 = 2531569) B2531569
theorem B2810201 : Blo 1871637 2810201 := bstep (se 2 (by rfl) ⟨1053825, by rfl⟩ : syracuseStep 2810201 = 2107651) B2107651
theorem B5693789 : Blo 1871637 5693789 := bstep (se 3 (by rfl) ⟨1067585, by rfl⟩ : syracuseStep 5693789 = 2135171) B2135171
theorem B2105707 : Blo 1871637 2105707 := bstep (se 1 (by rfl) ⟨1579280, by rfl⟩ : syracuseStep 2105707 = 3158561) B3158561
theorem B3555713 : Blo 1871637 3555713 := bstep (se 2 (by rfl) ⟨1333392, by rfl⟩ : syracuseStep 3555713 = 2666785) B2666785
theorem B1999243 : Blo 1871637 1999243 := bstep (se 1 (by rfl) ⟨1499432, by rfl⟩ : syracuseStep 1999243 = 2998865) B2998865
theorem B7995793 : Blo 1871637 7995793 := bstep (se 2 (by rfl) ⟨2998422, by rfl⟩ : syracuseStep 7995793 = 5996845) B5996845
theorem B14213555 : Blo 1871637 14213555 := bstep (se 1 (by rfl) ⟨10660166, by rfl⟩ : syracuseStep 14213555 = 21320333) B21320333
theorem B7111091 : Blo 1871637 7111091 := bstep (se 1 (by rfl) ⟨5333318, by rfl⟩ : syracuseStep 7111091 = 10666637) B10666637
theorem B2810315 : Blo 1871637 2810315 := bstep (se 1 (by rfl) ⟨2107736, by rfl⟩ : syracuseStep 2810315 = 4215473) B4215473
theorem B2105815 : Blo 1871637 2105815 := bstep (se 1 (by rfl) ⟨1579361, by rfl⟩ : syracuseStep 2105815 = 3158723) B3158723
theorem B2810327 : Blo 1871637 2810327 := bstep (se 1 (by rfl) ⟨2107745, by rfl⟩ : syracuseStep 2810327 = 4215491) B4215491
theorem B7209437 : Blo 1871637 7209437 := bstep (se 3 (by rfl) ⟨1351769, by rfl⟩ : syracuseStep 7209437 = 2703539) B2703539
theorem B4211225 : Blo 1871637 4211225 := bstep (se 2 (by rfl) ⟨1579209, by rfl⟩ : syracuseStep 4211225 = 3158419) B3158419
theorem B2810393 : Blo 1871637 2810393 := bstep (se 2 (by rfl) ⟨1053897, by rfl⟩ : syracuseStep 2810393 = 2107795) B2107795
theorem B18006563 : Blo 1871637 18006563 := bstep (se 1 (by rfl) ⟨13504922, by rfl⟩ : syracuseStep 18006563 = 27009845) B27009845
theorem B21627485 : Blo 1871637 21627485 := bstep (se 3 (by rfl) ⟨4055153, by rfl⟩ : syracuseStep 21627485 = 8110307) B8110307
theorem B4211315 : Blo 1871637 4211315 := bstep (se 1 (by rfl) ⟨3158486, by rfl⟩ : syracuseStep 4211315 = 6316973) B6316973
theorem B2105995 : Blo 1871637 2105995 := bstep (se 1 (by rfl) ⟨1579496, by rfl⟩ : syracuseStep 2105995 = 3158993) B3158993
theorem B1999499 : Blo 1871637 1999499 := bstep (se 1 (by rfl) ⟨1499624, by rfl⟩ : syracuseStep 1999499 = 2999249) B2999249
theorem B4211351 : Blo 1871637 4211351 := bstep (se 1 (by rfl) ⟨3158513, by rfl⟩ : syracuseStep 4211351 = 6317027) B6317027
theorem B5333683 : Blo 1871637 5333683 := bstep (se 1 (by rfl) ⟨4000262, by rfl⟩ : syracuseStep 5333683 = 8000525) B8000525
theorem B3556055 : Blo 1871637 3556055 := bstep (se 1 (by rfl) ⟨2667041, by rfl⟩ : syracuseStep 3556055 = 5334083) B5334083
theorem B2106103 : Blo 1871637 2106103 := bstep (se 1 (by rfl) ⟨1579577, by rfl⟩ : syracuseStep 2106103 = 3159155) B3159155
theorem B17089325 : Blo 1871637 17089325 := bstep (se 3 (by rfl) ⟨3204248, by rfl⟩ : syracuseStep 17089325 = 6408497) B6408497
theorem B6316865 : Blo 1871637 6316865 := bstep (se 2 (by rfl) ⟨2368824, by rfl⟩ : syracuseStep 6316865 = 4737649) B4737649
theorem B4211531 : Blo 1871637 4211531 := bstep (se 1 (by rfl) ⟨3158648, by rfl⟩ : syracuseStep 4211531 = 6317297) B6317297
theorem B4211585 : Blo 1871637 4211585 := bstep (se 2 (by rfl) ⟨1579344, by rfl⟩ : syracuseStep 4211585 = 3158689) B3158689
theorem B3376001 : Blo 1871637 3376001 := bstep (se 2 (by rfl) ⟨1266000, by rfl⟩ : syracuseStep 3376001 = 2532001) B2532001
theorem B2106283 : Blo 1871637 2106283 := bstep (se 1 (by rfl) ⟨1579712, by rfl⟩ : syracuseStep 2106283 = 3159425) B3159425
theorem B4498355 : Blo 1871637 4498355 := bstep (se 1 (by rfl) ⟨3373766, by rfl⟩ : syracuseStep 4498355 = 6747533) B6747533
theorem B2999243 : Blo 1871637 2999243 := bstep (se 1 (by rfl) ⟨2249432, by rfl⟩ : syracuseStep 2999243 = 4498865) B4498865
theorem B5694425 : Blo 1871637 5694425 := bstep (se 2 (by rfl) ⟨2135409, by rfl⟩ : syracuseStep 5694425 = 4270819) B4270819
theorem B2106391 : Blo 1871637 2106391 := bstep (se 1 (by rfl) ⟨1579793, by rfl⟩ : syracuseStep 2106391 = 3159587) B3159587
theorem B7111745 : Blo 1871637 7111745 := bstep (se 2 (by rfl) ⟨2666904, by rfl⟩ : syracuseStep 7111745 = 5333809) B5333809
theorem B64873547 : Blo 1871637 64873547 := bstep (se 1 (by rfl) ⟨48655160, by rfl⟩ : syracuseStep 64873547 = 97310321) B97310321
theorem B4211801 : Blo 1871637 4211801 := bstep (se 2 (by rfl) ⟨1579425, by rfl⟩ : syracuseStep 4211801 = 3158851) B3158851
theorem B4211891 : Blo 1871637 4211891 := bstep (se 1 (by rfl) ⟨3158918, by rfl⟩ : syracuseStep 4211891 = 6317837) B6317837
theorem B2106571 : Blo 1871637 2106571 := bstep (se 1 (by rfl) ⟨1579928, by rfl⟩ : syracuseStep 2106571 = 3159857) B3159857
theorem B4211927 : Blo 1871637 4211927 := bstep (se 1 (by rfl) ⟨3158945, by rfl⟩ : syracuseStep 4211927 = 6317891) B6317891
theorem B2106679 : Blo 1871637 2106679 := bstep (se 1 (by rfl) ⟨1580009, by rfl⟩ : syracuseStep 2106679 = 3160019) B3160019
theorem B2368855 : Blo 1871637 2368855 := bstep (se 1 (by rfl) ⟨1776641, by rfl⟩ : syracuseStep 2368855 = 3553283) B3553283
theorem B6317405 : Blo 1871637 6317405 := bstep (se 3 (by rfl) ⟨1184513, by rfl⟩ : syracuseStep 6317405 = 2369027) B2369027
theorem B3556723 : Blo 1871637 3556723 := bstep (se 1 (by rfl) ⟨2667542, by rfl⟩ : syracuseStep 3556723 = 5335085) B5335085
theorem B4212107 : Blo 1871637 4212107 := bstep (se 1 (by rfl) ⟨3159080, by rfl⟩ : syracuseStep 4212107 = 6318161) B6318161
theorem B3999127 : Blo 1871637 3999127 := bstep (se 1 (by rfl) ⟨2999345, by rfl⟩ : syracuseStep 3999127 = 5998691) B5998691
theorem B4212161 : Blo 1871637 4212161 := bstep (se 2 (by rfl) ⟨1579560, by rfl⟩ : syracuseStep 4212161 = 3159121) B3159121
theorem B3999169 : Blo 1871637 3999169 := bstep (se 2 (by rfl) ⟨1499688, by rfl⟩ : syracuseStep 3999169 = 2999377) B2999377
theorem B2106859 : Blo 1871637 2106859 := bstep (se 1 (by rfl) ⟨1580144, by rfl⟩ : syracuseStep 2106859 = 3160289) B3160289
theorem B6841901 : Blo 1871637 6841901 := bstep (se 3 (by rfl) ⟨1282856, by rfl⟩ : syracuseStep 6841901 = 2565713) B2565713
theorem B2106967 : Blo 1871637 2106967 := bstep (se 1 (by rfl) ⟨1580225, by rfl⟩ : syracuseStep 2106967 = 3160451) B3160451
theorem B34162307 : Blo 1871637 34162307 := bstep (se 1 (by rfl) ⟨25621730, by rfl⟩ : syracuseStep 34162307 = 51243461) B51243461
theorem B13493911 : Blo 1871637 13493911 := bstep (se 1 (by rfl) ⟨10120433, by rfl⟩ : syracuseStep 13493911 = 20240867) B20240867
theorem B4212377 : Blo 1871637 4212377 := bstep (se 2 (by rfl) ⟨1579641, by rfl⟩ : syracuseStep 4212377 = 3159283) B3159283
theorem B5334731 : Blo 1871637 5334731 := bstep (se 1 (by rfl) ⟨4001048, by rfl⟩ : syracuseStep 5334731 = 8002097) B8002097
theorem B4212467 : Blo 1871637 4212467 := bstep (se 1 (by rfl) ⟨3159350, by rfl⟩ : syracuseStep 4212467 = 6318701) B6318701
theorem B2107147 : Blo 1871637 2107147 := bstep (se 1 (by rfl) ⟨1580360, by rfl⟩ : syracuseStep 2107147 = 3160721) B3160721
theorem B4212503 : Blo 1871637 4212503 := bstep (se 1 (by rfl) ⟨3159377, by rfl⟩ : syracuseStep 4212503 = 6318755) B6318755
theorem B10667821 : Blo 1871637 10667821 := bstep (se 3 (by rfl) ⟨2000216, by rfl⟩ : syracuseStep 10667821 = 4000433) B4000433
theorem B14215013 : Blo 1871637 14215013 := bstep (se 4 (by rfl) ⟨1332657, by rfl⟩ : syracuseStep 14215013 = 2665315) B2665315
theorem B2107255 : Blo 1871637 2107255 := bstep (se 1 (by rfl) ⟨1580441, by rfl⟩ : syracuseStep 2107255 = 3160883) B3160883
theorem B4212683 : Blo 1871637 4212683 := bstep (se 1 (by rfl) ⟨3159512, by rfl⟩ : syracuseStep 4212683 = 6319025) B6319025
theorem B7309273 : Blo 1871637 7309273 := bstep (se 2 (by rfl) ⟨2740977, by rfl⟩ : syracuseStep 7309273 = 5481955) B5481955
theorem B4212737 : Blo 1871637 4212737 := bstep (se 2 (by rfl) ⟨1579776, by rfl⟩ : syracuseStep 4212737 = 3159553) B3159553
theorem B4499479 : Blo 1871637 4499479 := bstep (se 1 (by rfl) ⟨3374609, by rfl⟩ : syracuseStep 4499479 = 6749219) B6749219
theorem B3794969 : Blo 1871637 3794969 := bstep (se 2 (by rfl) ⟨1423113, by rfl⟩ : syracuseStep 3794969 = 2846227) B2846227
theorem B2107435 : Blo 1871637 2107435 := bstep (se 1 (by rfl) ⟨1580576, by rfl⟩ : syracuseStep 2107435 = 3161153) B3161153
theorem B2369675 : Blo 1871637 2369675 := bstep (se 1 (by rfl) ⟨1777256, by rfl⟩ : syracuseStep 2369675 = 3554513) B3554513
theorem B2107543 : Blo 1871637 2107543 := bstep (se 1 (by rfl) ⟨1580657, by rfl⟩ : syracuseStep 2107543 = 3161315) B3161315
theorem B4212953 : Blo 1871637 4212953 := bstep (se 2 (by rfl) ⟨1579857, by rfl⟩ : syracuseStep 4212953 = 3159715) B3159715
theorem B2165015 : Blo 1871637 2165015 := bstep (se 1 (by rfl) ⟨1623761, by rfl⟩ : syracuseStep 2165015 = 3247523) B3247523
theorem B7113005 : Blo 1871637 7113005 := bstep (se 3 (by rfl) ⟨1333688, by rfl⟩ : syracuseStep 7113005 = 2667377) B2667377
theorem B4213043 : Blo 1871637 4213043 := bstep (se 1 (by rfl) ⟨3159782, by rfl⟩ : syracuseStep 4213043 = 6319565) B6319565
theorem B14215499 : Blo 1871637 14215499 := bstep (se 1 (by rfl) ⟨10661624, by rfl⟩ : syracuseStep 14215499 = 21323249) B21323249
theorem B7113035 : Blo 1871637 7113035 := bstep (se 1 (by rfl) ⟨5334776, by rfl⟩ : syracuseStep 7113035 = 10669553) B10669553
theorem B12003659 : Blo 1871637 12003659 := bstep (se 1 (by rfl) ⟨9002744, by rfl⟩ : syracuseStep 12003659 = 18005489) B18005489
theorem B2107723 : Blo 1871637 2107723 := bstep (se 1 (by rfl) ⟨1580792, by rfl⟩ : syracuseStep 2107723 = 3161585) B3161585
theorem B4213079 : Blo 1871637 4213079 := bstep (se 1 (by rfl) ⟨3159809, by rfl⟩ : syracuseStep 4213079 = 6319619) B6319619
theorem B4802905 : Blo 1871637 4802905 := bstep (se 2 (by rfl) ⟨1801089, by rfl⟩ : syracuseStep 4802905 = 3602179) B3602179
theorem B12814723 : Blo 1871637 12814723 := bstep (se 1 (by rfl) ⟨9611042, by rfl⟩ : syracuseStep 12814723 = 19222085) B19222085
theorem B16001459 : Blo 1871637 16001459 := bstep (se 1 (by rfl) ⟨12001094, by rfl⟩ : syracuseStep 16001459 = 24002189) B24002189
theorem B2107831 : Blo 1871637 2107831 := bstep (se 1 (by rfl) ⟨1580873, by rfl⟩ : syracuseStep 2107831 = 3161747) B3161747
theorem B6318539 : Blo 1871637 6318539 := bstep (se 1 (by rfl) ⟨4738904, by rfl⟩ : syracuseStep 6318539 = 9477809) B9477809
theorem B4213259 : Blo 1871637 4213259 := bstep (se 1 (by rfl) ⟨3159944, by rfl⟩ : syracuseStep 4213259 = 6319889) B6319889
theorem B4213313 : Blo 1871637 4213313 := bstep (se 2 (by rfl) ⟨1579992, by rfl⟩ : syracuseStep 4213313 = 3159985) B3159985
theorem B2665099 : Blo 1871637 2665099 := bstep (se 1 (by rfl) ⟨1998824, by rfl⟩ : syracuseStep 2665099 = 3997649) B3997649
theorem B10660531 : Blo 1871637 10660531 := bstep (se 1 (by rfl) ⟨7995398, by rfl⟩ : syracuseStep 10660531 = 15990797) B15990797
theorem B6318809 : Blo 1871637 6318809 := bstep (se 2 (by rfl) ⟨2369553, by rfl⟩ : syracuseStep 6318809 = 4739107) B4739107
theorem B4213529 : Blo 1871637 4213529 := bstep (se 2 (by rfl) ⟨1580073, by rfl⟩ : syracuseStep 4213529 = 3160147) B3160147
theorem B2370379 : Blo 1871637 2370379 := bstep (se 1 (by rfl) ⟨1777784, by rfl⟩ : syracuseStep 2370379 = 3555569) B3555569
theorem B3795827 : Blo 1871637 3795827 := bstep (se 1 (by rfl) ⟨2846870, by rfl⟩ : syracuseStep 3795827 = 5693741) B5693741
theorem B4213619 : Blo 1871637 4213619 := bstep (se 1 (by rfl) ⟨3160214, by rfl⟩ : syracuseStep 4213619 = 6320429) B6320429
theorem B4213655 : Blo 1871637 4213655 := bstep (se 1 (by rfl) ⟨3160241, by rfl⟩ : syracuseStep 4213655 = 6320483) B6320483
theorem B7113689 : Blo 1871637 7113689 := bstep (se 2 (by rfl) ⟨2667633, by rfl⟩ : syracuseStep 7113689 = 5335267) B5335267
theorem B7203863 : Blo 1871637 7203863 := bstep (se 1 (by rfl) ⟨5402897, by rfl⟩ : syracuseStep 7203863 = 10805795) B10805795
theorem B12815405 : Blo 1871637 12815405 := bstep (se 3 (by rfl) ⟨2402888, by rfl⟩ : syracuseStep 12815405 = 4805777) B4805777
theorem B4213835 : Blo 1871637 4213835 := bstep (se 1 (by rfl) ⟨3160376, by rfl⟩ : syracuseStep 4213835 = 6320753) B6320753
theorem B4000843 : Blo 1871637 4000843 := bstep (se 1 (by rfl) ⟨3000632, by rfl⟩ : syracuseStep 4000843 = 6001265) B6001265
theorem B2370647 : Blo 1871637 2370647 := bstep (se 1 (by rfl) ⟨1777985, by rfl⟩ : syracuseStep 2370647 = 3555971) B3555971
theorem B4213889 : Blo 1871637 4213889 := bstep (se 2 (by rfl) ⟨1580208, by rfl⟩ : syracuseStep 4213889 = 3160417) B3160417
theorem B26987701 : Blo 1871637 26987701 := bstep (se 5 (by rfl) ⟨1265048, by rfl⟩ : syracuseStep 26987701 = 2530097) B2530097
theorem B60738821 : Blo 1871637 60738821 := bstep (se 4 (by rfl) ⟨5694264, by rfl⟩ : syracuseStep 60738821 = 11388529) B11388529
theorem B3796249 : Blo 1871637 3796249 := bstep (se 2 (by rfl) ⟨1423593, by rfl⟩ : syracuseStep 3796249 = 2847187) B2847187
theorem B54013229 : Blo 1871637 54013229 := bstep (se 3 (by rfl) ⟨10127480, by rfl⟩ : syracuseStep 54013229 = 20254961) B20254961
theorem B4214105 : Blo 1871637 4214105 := bstep (se 2 (by rfl) ⟨1580289, by rfl⟩ : syracuseStep 4214105 = 3160579) B3160579
theorem B14224733 : Blo 1871637 14224733 := bstep (se 3 (by rfl) ⟨2667137, by rfl⟩ : syracuseStep 14224733 = 5334275) B5334275
theorem B7998851 : Blo 1871637 7998851 := bstep (se 1 (by rfl) ⟨5999138, by rfl⟩ : syracuseStep 7998851 = 11998277) B11998277
theorem B6319511 : Blo 1871637 6319511 := bstep (se 1 (by rfl) ⟨4739633, by rfl⟩ : syracuseStep 6319511 = 9479267) B9479267
theorem B4001177 : Blo 1871637 4001177 := bstep (se 2 (by rfl) ⟨1500441, by rfl⟩ : syracuseStep 4001177 = 3000883) B3000883
theorem B4214195 : Blo 1871637 4214195 := bstep (se 1 (by rfl) ⟨3160646, by rfl⟩ : syracuseStep 4214195 = 6321293) B6321293
theorem B4214231 : Blo 1871637 4214231 := bstep (se 1 (by rfl) ⟨3160673, by rfl⟩ : syracuseStep 4214231 = 6321347) B6321347
theorem B8998361 : Blo 1871637 8998361 := bstep (se 2 (by rfl) ⟨3374385, by rfl⟩ : syracuseStep 8998361 = 6748771) B6748771
theorem B16002521 : Blo 1871637 16002521 := bstep (se 2 (by rfl) ⟨6000945, by rfl⟩ : syracuseStep 16002521 = 12001891) B12001891
theorem B26996237 : Blo 1871637 26996237 := bstep (se 3 (by rfl) ⟨5061794, by rfl⟩ : syracuseStep 26996237 = 10123589) B10123589
theorem B6934061 : Blo 1871637 6934061 := bstep (se 3 (by rfl) ⟨1300136, by rfl⟩ : syracuseStep 6934061 = 2600273) B2600273
theorem B9481859 : Blo 1871637 9481859 := bstep (se 1 (by rfl) ⟨7111394, by rfl⟩ : syracuseStep 9481859 = 14222789) B14222789
theorem B4214411 : Blo 1871637 4214411 := bstep (se 1 (by rfl) ⟨3160808, by rfl⟩ : syracuseStep 4214411 = 6321617) B6321617
theorem B4214465 : Blo 1871637 4214465 := bstep (se 2 (by rfl) ⟨1580424, by rfl⟩ : syracuseStep 4214465 = 3160849) B3160849
theorem B4738763 : Blo 1871637 4738763 := bstep (se 1 (by rfl) ⟨3554072, by rfl⟩ : syracuseStep 4738763 = 7108145) B7108145
theorem B6000331 : Blo 1871637 6000331 := bstep (se 1 (by rfl) ⟨4500248, by rfl⟩ : syracuseStep 6000331 = 9000497) B9000497
theorem B26996465 : Blo 1871637 26996465 := bstep (se 2 (by rfl) ⟨10123674, by rfl⟩ : syracuseStep 26996465 = 20247349) B20247349
theorem B1871639 : Blo 1871637 1871639 := bstep (se 1 (by rfl) ⟨1403729, by rfl⟩ : syracuseStep 1871639 = 2807459) B2807459
theorem B1871659 : Blo 1871637 1871659 := bstep (se 1 (by rfl) ⟨1403744, by rfl⟩ : syracuseStep 1871659 = 2807489) B2807489
theorem B1871671 : Blo 1871637 1871671 := bstep (se 1 (by rfl) ⟨1403753, by rfl⟩ : syracuseStep 1871671 = 2807507) B2807507
theorem B1871691 : Blo 1871637 1871691 := bstep (se 1 (by rfl) ⟨1403768, by rfl⟩ : syracuseStep 1871691 = 2807537) B2807537
theorem B1871703 : Blo 1871637 1871703 := bstep (se 1 (by rfl) ⟨1403777, by rfl⟩ : syracuseStep 1871703 = 2807555) B2807555
theorem B1871723 : Blo 1871637 1871723 := bstep (se 1 (by rfl) ⟨1403792, by rfl⟩ : syracuseStep 1871723 = 2807585) B2807585
theorem B1871735 : Blo 1871637 1871735 := bstep (se 1 (by rfl) ⟨1403801, by rfl⟩ : syracuseStep 1871735 = 2807603) B2807603
theorem B1871755 : Blo 1871637 1871755 := bstep (se 1 (by rfl) ⟨1403816, by rfl⟩ : syracuseStep 1871755 = 2807633) B2807633
theorem B1871767 : Blo 1871637 1871767 := bstep (se 1 (by rfl) ⟨1403825, by rfl⟩ : syracuseStep 1871767 = 2807651) B2807651
theorem B4214681 : Blo 1871637 4214681 := bstep (se 2 (by rfl) ⟨1580505, by rfl⟩ : syracuseStep 4214681 = 3161011) B3161011
theorem B1871787 : Blo 1871637 1871787 := bstep (se 1 (by rfl) ⟨1403840, by rfl⟩ : syracuseStep 1871787 = 2807681) B2807681
theorem B6320051 : Blo 1871637 6320051 := bstep (se 1 (by rfl) ⟨4740038, by rfl⟩ : syracuseStep 6320051 = 9480077) B9480077
theorem B1871799 : Blo 1871637 1871799 := bstep (se 1 (by rfl) ⟨1403849, by rfl⟩ : syracuseStep 1871799 = 2807699) B2807699
theorem B1871819 : Blo 1871637 1871819 := bstep (se 1 (by rfl) ⟨1403864, by rfl⟩ : syracuseStep 1871819 = 2807729) B2807729
theorem B1871831 : Blo 1871637 1871831 := bstep (se 1 (by rfl) ⟨1403873, by rfl⟩ : syracuseStep 1871831 = 2807747) B2807747
theorem B1871851 : Blo 1871637 1871851 := bstep (se 1 (by rfl) ⟨1403888, by rfl⟩ : syracuseStep 1871851 = 2807777) B2807777
theorem B4214771 : Blo 1871637 4214771 := bstep (se 1 (by rfl) ⟨3161078, by rfl⟩ : syracuseStep 4214771 = 6322157) B6322157
theorem B1871863 : Blo 1871637 1871863 := bstep (se 1 (by rfl) ⟨1403897, by rfl⟩ : syracuseStep 1871863 = 2807795) B2807795
theorem B1871883 : Blo 1871637 1871883 := bstep (se 1 (by rfl) ⟨1403912, by rfl⟩ : syracuseStep 1871883 = 2807825) B2807825
theorem B1871895 : Blo 1871637 1871895 := bstep (se 1 (by rfl) ⟨1403921, by rfl⟩ : syracuseStep 1871895 = 2807843) B2807843
theorem B4214807 : Blo 1871637 4214807 := bstep (se 1 (by rfl) ⟨3161105, by rfl⟩ : syracuseStep 4214807 = 6322211) B6322211
theorem B1871915 : Blo 1871637 1871915 := bstep (se 1 (by rfl) ⟨1403936, by rfl⟩ : syracuseStep 1871915 = 2807873) B2807873
theorem B1871927 : Blo 1871637 1871927 := bstep (se 1 (by rfl) ⟨1403945, by rfl⟩ : syracuseStep 1871927 = 2807891) B2807891
theorem B76845125 : Blo 1871637 76845125 := bstep (se 4 (by rfl) ⟨7204230, by rfl⟩ : syracuseStep 76845125 = 14408461) B14408461
theorem B1871947 : Blo 1871637 1871947 := bstep (se 1 (by rfl) ⟨1403960, by rfl⟩ : syracuseStep 1871947 = 2807921) B2807921
theorem B1871959 : Blo 1871637 1871959 := bstep (se 1 (by rfl) ⟨1403969, by rfl⟩ : syracuseStep 1871959 = 2807939) B2807939
theorem B10661989 : Blo 1871637 10661989 := bstep (se 4 (by rfl) ⟨999561, by rfl⟩ : syracuseStep 10661989 = 1999123) B1999123
theorem B1871979 : Blo 1871637 1871979 := bstep (se 1 (by rfl) ⟨1403984, by rfl⟩ : syracuseStep 1871979 = 2807969) B2807969
theorem B1871991 : Blo 1871637 1871991 := bstep (se 1 (by rfl) ⟨1403993, by rfl⟩ : syracuseStep 1871991 = 2807987) B2807987
theorem B1872011 : Blo 1871637 1872011 := bstep (se 1 (by rfl) ⟨1404008, by rfl⟩ : syracuseStep 1872011 = 2808017) B2808017
theorem B1872023 : Blo 1871637 1872023 := bstep (se 1 (by rfl) ⟨1404017, by rfl⟩ : syracuseStep 1872023 = 2808035) B2808035
theorem B1872043 : Blo 1871637 1872043 := bstep (se 1 (by rfl) ⟨1404032, by rfl⟩ : syracuseStep 1872043 = 2808065) B2808065
theorem B13504691 : Blo 1871637 13504691 := bstep (se 1 (by rfl) ⟨10128518, by rfl⟩ : syracuseStep 13504691 = 20257037) B20257037
theorem B1872055 : Blo 1871637 1872055 := bstep (se 1 (by rfl) ⟨1404041, by rfl⟩ : syracuseStep 1872055 = 2808083) B2808083
theorem B6320321 : Blo 1871637 6320321 := bstep (se 2 (by rfl) ⟨2370120, by rfl⟩ : syracuseStep 6320321 = 4740241) B4740241
theorem B1872075 : Blo 1871637 1872075 := bstep (se 1 (by rfl) ⟨1404056, by rfl⟩ : syracuseStep 1872075 = 2808113) B2808113
theorem B4214987 : Blo 1871637 4214987 := bstep (se 1 (by rfl) ⟨3161240, by rfl⟩ : syracuseStep 4214987 = 6322481) B6322481
theorem B1872087 : Blo 1871637 1872087 := bstep (se 1 (by rfl) ⟨1404065, by rfl⟩ : syracuseStep 1872087 = 2808131) B2808131
theorem B1872107 : Blo 1871637 1872107 := bstep (se 1 (by rfl) ⟨1404080, by rfl⟩ : syracuseStep 1872107 = 2808161) B2808161
theorem B1872119 : Blo 1871637 1872119 := bstep (se 1 (by rfl) ⟨1404089, by rfl⟩ : syracuseStep 1872119 = 2808179) B2808179
theorem B4215041 : Blo 1871637 4215041 := bstep (se 2 (by rfl) ⟨1580640, by rfl⟩ : syracuseStep 4215041 = 3161281) B3161281
theorem B1872139 : Blo 1871637 1872139 := bstep (se 1 (by rfl) ⟨1404104, by rfl⟩ : syracuseStep 1872139 = 2808209) B2808209
theorem B1872151 : Blo 1871637 1872151 := bstep (se 1 (by rfl) ⟨1404113, by rfl⟩ : syracuseStep 1872151 = 2808227) B2808227
theorem B15995171 : Blo 1871637 15995171 := bstep (se 1 (by rfl) ⟨11996378, by rfl⟩ : syracuseStep 15995171 = 23992757) B23992757
theorem B1872171 : Blo 1871637 1872171 := bstep (se 1 (by rfl) ⟨1404128, by rfl⟩ : syracuseStep 1872171 = 2808257) B2808257
theorem B1872183 : Blo 1871637 1872183 := bstep (se 1 (by rfl) ⟨1404137, by rfl⟩ : syracuseStep 1872183 = 2808275) B2808275
theorem B1872203 : Blo 1871637 1872203 := bstep (se 1 (by rfl) ⟨1404152, by rfl⟩ : syracuseStep 1872203 = 2808305) B2808305
theorem B1872215 : Blo 1871637 1872215 := bstep (se 1 (by rfl) ⟨1404161, by rfl⟩ : syracuseStep 1872215 = 2808323) B2808323
theorem B1872235 : Blo 1871637 1872235 := bstep (se 1 (by rfl) ⟨1404176, by rfl⟩ : syracuseStep 1872235 = 2808353) B2808353
theorem B80949617 : Blo 1871637 80949617 := bstep (se 2 (by rfl) ⟨30356106, by rfl⟩ : syracuseStep 80949617 = 60712213) B60712213
theorem B1872247 : Blo 1871637 1872247 := bstep (se 1 (by rfl) ⟨1404185, by rfl⟩ : syracuseStep 1872247 = 2808371) B2808371
theorem B1872267 : Blo 1871637 1872267 := bstep (se 1 (by rfl) ⟨1404200, by rfl⟩ : syracuseStep 1872267 = 2808401) B2808401
theorem B1872279 : Blo 1871637 1872279 := bstep (se 1 (by rfl) ⟨1404209, by rfl⟩ : syracuseStep 1872279 = 2808419) B2808419
theorem B1872299 : Blo 1871637 1872299 := bstep (se 1 (by rfl) ⟨1404224, by rfl⟩ : syracuseStep 1872299 = 2808449) B2808449
theorem B1872311 : Blo 1871637 1872311 := bstep (se 1 (by rfl) ⟨1404233, by rfl⟩ : syracuseStep 1872311 = 2808467) B2808467
theorem B1872331 : Blo 1871637 1872331 := bstep (se 1 (by rfl) ⟨1404248, by rfl⟩ : syracuseStep 1872331 = 2808497) B2808497
theorem B1872343 : Blo 1871637 1872343 := bstep (se 1 (by rfl) ⟨1404257, by rfl⟩ : syracuseStep 1872343 = 2808515) B2808515
theorem B4215257 : Blo 1871637 4215257 := bstep (se 2 (by rfl) ⟨1580721, by rfl⟩ : syracuseStep 4215257 = 3161443) B3161443
theorem B1872363 : Blo 1871637 1872363 := bstep (se 1 (by rfl) ⟨1404272, by rfl⟩ : syracuseStep 1872363 = 2808545) B2808545
theorem B1872375 : Blo 1871637 1872375 := bstep (se 1 (by rfl) ⟨1404281, by rfl⟩ : syracuseStep 1872375 = 2808563) B2808563
theorem B1872395 : Blo 1871637 1872395 := bstep (se 1 (by rfl) ⟨1404296, by rfl⟩ : syracuseStep 1872395 = 2808593) B2808593
theorem B1872407 : Blo 1871637 1872407 := bstep (se 1 (by rfl) ⟨1404305, by rfl⟩ : syracuseStep 1872407 = 2808611) B2808611
theorem B1872427 : Blo 1871637 1872427 := bstep (se 1 (by rfl) ⟨1404320, by rfl⟩ : syracuseStep 1872427 = 2808641) B2808641
theorem B10121773 : Blo 1871637 10121773 := bstep (se 3 (by rfl) ⟨1897832, by rfl⟩ : syracuseStep 10121773 = 3795665) B3795665
theorem B4215347 : Blo 1871637 4215347 := bstep (se 1 (by rfl) ⟨3161510, by rfl⟩ : syracuseStep 4215347 = 6323021) B6323021
theorem B1872439 : Blo 1871637 1872439 := bstep (se 1 (by rfl) ⟨1404329, by rfl⟩ : syracuseStep 1872439 = 2808659) B2808659
theorem B1872459 : Blo 1871637 1872459 := bstep (se 1 (by rfl) ⟨1404344, by rfl⟩ : syracuseStep 1872459 = 2808689) B2808689
theorem B3158615 : Blo 1871637 3158615 := bstep (se 1 (by rfl) ⟨2368961, by rfl⟩ : syracuseStep 3158615 = 4737923) B4737923
theorem B1872471 : Blo 1871637 1872471 := bstep (se 1 (by rfl) ⟨1404353, by rfl⟩ : syracuseStep 1872471 = 2808707) B2808707
theorem B4215383 : Blo 1871637 4215383 := bstep (se 1 (by rfl) ⟨3161537, by rfl⟩ : syracuseStep 4215383 = 6323075) B6323075
theorem B1872491 : Blo 1871637 1872491 := bstep (se 1 (by rfl) ⟨1404368, by rfl⟩ : syracuseStep 1872491 = 2808737) B2808737
theorem B1872503 : Blo 1871637 1872503 := bstep (se 1 (by rfl) ⟨1404377, by rfl⟩ : syracuseStep 1872503 = 2808755) B2808755
theorem B7107203 : Blo 1871637 7107203 := bstep (se 1 (by rfl) ⟨5330402, by rfl⟩ : syracuseStep 7107203 = 10660805) B10660805
theorem B1872523 : Blo 1871637 1872523 := bstep (se 1 (by rfl) ⟨1404392, by rfl⟩ : syracuseStep 1872523 = 2808785) B2808785
theorem B4739735 : Blo 1871637 4739735 := bstep (se 1 (by rfl) ⟨3554801, by rfl⟩ : syracuseStep 4739735 = 7109603) B7109603
theorem B1872535 : Blo 1871637 1872535 := bstep (se 1 (by rfl) ⟨1404401, by rfl⟩ : syracuseStep 1872535 = 2808803) B2808803
theorem B1872555 : Blo 1871637 1872555 := bstep (se 1 (by rfl) ⟨1404416, by rfl⟩ : syracuseStep 1872555 = 2808833) B2808833
theorem B1872567 : Blo 1871637 1872567 := bstep (se 1 (by rfl) ⟨1404425, by rfl⟩ : syracuseStep 1872567 = 2808851) B2808851
theorem B1872587 : Blo 1871637 1872587 := bstep (se 1 (by rfl) ⟨1404440, by rfl⟩ : syracuseStep 1872587 = 2808881) B2808881
theorem B3158743 : Blo 1871637 3158743 := bstep (se 1 (by rfl) ⟨2369057, by rfl⟩ : syracuseStep 3158743 = 4738115) B4738115
theorem B1872599 : Blo 1871637 1872599 := bstep (se 1 (by rfl) ⟨1404449, by rfl⟩ : syracuseStep 1872599 = 2808899) B2808899
theorem B7590617 : Blo 1871637 7590617 := bstep (se 2 (by rfl) ⟨2846481, by rfl⟩ : syracuseStep 7590617 = 5692963) B5692963
theorem B6320861 : Blo 1871637 6320861 := bstep (se 3 (by rfl) ⟨1185161, by rfl⟩ : syracuseStep 6320861 = 2370323) B2370323
theorem B1872619 : Blo 1871637 1872619 := bstep (se 1 (by rfl) ⟨1404464, by rfl⟩ : syracuseStep 1872619 = 2808929) B2808929
theorem B1872631 : Blo 1871637 1872631 := bstep (se 1 (by rfl) ⟨1404473, by rfl⟩ : syracuseStep 1872631 = 2808947) B2808947
theorem B1872651 : Blo 1871637 1872651 := bstep (se 1 (by rfl) ⟨1404488, by rfl⟩ : syracuseStep 1872651 = 2808977) B2808977
theorem B4215563 : Blo 1871637 4215563 := bstep (se 1 (by rfl) ⟨3161672, by rfl⟩ : syracuseStep 4215563 = 6323345) B6323345
theorem B1872663 : Blo 1871637 1872663 := bstep (se 1 (by rfl) ⟨1404497, by rfl⟩ : syracuseStep 1872663 = 2808995) B2808995
theorem B1872683 : Blo 1871637 1872683 := bstep (se 1 (by rfl) ⟨1404512, by rfl⟩ : syracuseStep 1872683 = 2809025) B2809025
theorem B1872695 : Blo 1871637 1872695 := bstep (se 1 (by rfl) ⟨1404521, by rfl⟩ : syracuseStep 1872695 = 2809043) B2809043
theorem B4215617 : Blo 1871637 4215617 := bstep (se 2 (by rfl) ⟨1580856, by rfl⟩ : syracuseStep 4215617 = 3161713) B3161713
theorem B1872715 : Blo 1871637 1872715 := bstep (se 1 (by rfl) ⟨1404536, by rfl⟩ : syracuseStep 1872715 = 2809073) B2809073
theorem B1872727 : Blo 1871637 1872727 := bstep (se 1 (by rfl) ⟨1404545, by rfl⟩ : syracuseStep 1872727 = 2809091) B2809091
theorem B1872747 : Blo 1871637 1872747 := bstep (se 1 (by rfl) ⟨1404560, by rfl⟩ : syracuseStep 1872747 = 2809121) B2809121
theorem B1872759 : Blo 1871637 1872759 := bstep (se 1 (by rfl) ⟨1404569, by rfl⟩ : syracuseStep 1872759 = 2809139) B2809139
theorem B1872779 : Blo 1871637 1872779 := bstep (se 1 (by rfl) ⟨1404584, by rfl⟩ : syracuseStep 1872779 = 2809169) B2809169
theorem B1872791 : Blo 1871637 1872791 := bstep (se 1 (by rfl) ⟨1404593, by rfl⟩ : syracuseStep 1872791 = 2809187) B2809187
theorem B1872811 : Blo 1871637 1872811 := bstep (se 1 (by rfl) ⟨1404608, by rfl⟩ : syracuseStep 1872811 = 2809217) B2809217
theorem B1872823 : Blo 1871637 1872823 := bstep (se 1 (by rfl) ⟨1404617, by rfl⟩ : syracuseStep 1872823 = 2809235) B2809235
theorem B1872843 : Blo 1871637 1872843 := bstep (se 1 (by rfl) ⟨1404632, by rfl⟩ : syracuseStep 1872843 = 2809265) B2809265
theorem B1872855 : Blo 1871637 1872855 := bstep (se 1 (by rfl) ⟨1404641, by rfl⟩ : syracuseStep 1872855 = 2809283) B2809283
theorem B6747101 : Blo 1871637 6747101 := bstep (se 3 (by rfl) ⟨1265081, by rfl⟩ : syracuseStep 6747101 = 2530163) B2530163
theorem B1872875 : Blo 1871637 1872875 := bstep (se 1 (by rfl) ⟨1404656, by rfl⟩ : syracuseStep 1872875 = 2809313) B2809313
theorem B1872887 : Blo 1871637 1872887 := bstep (se 1 (by rfl) ⟨1404665, by rfl⟩ : syracuseStep 1872887 = 2809331) B2809331
theorem B1872907 : Blo 1871637 1872907 := bstep (se 1 (by rfl) ⟨1404680, by rfl⟩ : syracuseStep 1872907 = 2809361) B2809361
theorem B1872919 : Blo 1871637 1872919 := bstep (se 1 (by rfl) ⟨1404689, by rfl⟩ : syracuseStep 1872919 = 2809379) B2809379
theorem B1872939 : Blo 1871637 1872939 := bstep (se 1 (by rfl) ⟨1404704, by rfl⟩ : syracuseStep 1872939 = 2809409) B2809409
theorem B1872951 : Blo 1871637 1872951 := bstep (se 1 (by rfl) ⟨1404713, by rfl⟩ : syracuseStep 1872951 = 2809427) B2809427
theorem B7107659 : Blo 1871637 7107659 := bstep (se 1 (by rfl) ⟨5330744, by rfl⟩ : syracuseStep 7107659 = 10661489) B10661489
theorem B1872971 : Blo 1871637 1872971 := bstep (se 1 (by rfl) ⟨1404728, by rfl⟩ : syracuseStep 1872971 = 2809457) B2809457
theorem B1872983 : Blo 1871637 1872983 := bstep (se 1 (by rfl) ⟨1404737, by rfl⟩ : syracuseStep 1872983 = 2809475) B2809475
theorem B1873003 : Blo 1871637 1873003 := bstep (se 1 (by rfl) ⟨1404752, by rfl⟩ : syracuseStep 1873003 = 2809505) B2809505
theorem B1873015 : Blo 1871637 1873015 := bstep (se 1 (by rfl) ⟨1404761, by rfl⟩ : syracuseStep 1873015 = 2809523) B2809523
theorem B1873035 : Blo 1871637 1873035 := bstep (se 1 (by rfl) ⟨1404776, by rfl⟩ : syracuseStep 1873035 = 2809553) B2809553
theorem B1873047 : Blo 1871637 1873047 := bstep (se 1 (by rfl) ⟨1404785, by rfl⟩ : syracuseStep 1873047 = 2809571) B2809571
theorem B1873067 : Blo 1871637 1873067 := bstep (se 1 (by rfl) ⟨1404800, by rfl⟩ : syracuseStep 1873067 = 2809601) B2809601
theorem B1873079 : Blo 1871637 1873079 := bstep (se 1 (by rfl) ⟨1404809, by rfl⟩ : syracuseStep 1873079 = 2809619) B2809619
theorem B1873099 : Blo 1871637 1873099 := bstep (se 1 (by rfl) ⟨1404824, by rfl⟩ : syracuseStep 1873099 = 2809649) B2809649
theorem B1873111 : Blo 1871637 1873111 := bstep (se 1 (by rfl) ⟨1404833, by rfl⟩ : syracuseStep 1873111 = 2809667) B2809667
theorem B1873131 : Blo 1871637 1873131 := bstep (se 1 (by rfl) ⟨1404848, by rfl⟩ : syracuseStep 1873131 = 2809697) B2809697
theorem B1873143 : Blo 1871637 1873143 := bstep (se 1 (by rfl) ⟨1404857, by rfl⟩ : syracuseStep 1873143 = 2809715) B2809715
theorem B1873163 : Blo 1871637 1873163 := bstep (se 1 (by rfl) ⟨1404872, by rfl⟩ : syracuseStep 1873163 = 2809745) B2809745
theorem B7107857 : Blo 1871637 7107857 := bstep (se 2 (by rfl) ⟨2665446, by rfl⟩ : syracuseStep 7107857 = 5330893) B5330893
theorem B1873175 : Blo 1871637 1873175 := bstep (se 1 (by rfl) ⟨1404881, by rfl⟩ : syracuseStep 1873175 = 2809763) B2809763
theorem B1873195 : Blo 1871637 1873195 := bstep (se 1 (by rfl) ⟨1404896, by rfl⟩ : syracuseStep 1873195 = 2809793) B2809793
theorem B4740403 : Blo 1871637 4740403 := bstep (se 1 (by rfl) ⟨3555302, by rfl⟩ : syracuseStep 4740403 = 7110605) B7110605
theorem B1873207 : Blo 1871637 1873207 := bstep (se 1 (by rfl) ⟨1404905, by rfl⟩ : syracuseStep 1873207 = 2809811) B2809811
theorem B3421505 : Blo 1871637 3421505 := bstep (se 2 (by rfl) ⟨1283064, by rfl⟩ : syracuseStep 3421505 = 2566129) B2566129
theorem B3159371 : Blo 1871637 3159371 := bstep (se 1 (by rfl) ⟨2369528, by rfl⟩ : syracuseStep 3159371 = 4739057) B4739057
theorem B1873227 : Blo 1871637 1873227 := bstep (se 1 (by rfl) ⟨1404920, by rfl⟩ : syracuseStep 1873227 = 2809841) B2809841
theorem B1873239 : Blo 1871637 1873239 := bstep (se 1 (by rfl) ⟨1404929, by rfl⟩ : syracuseStep 1873239 = 2809859) B2809859
theorem B6002009 : Blo 1871637 6002009 := bstep (se 2 (by rfl) ⟨2250753, by rfl⟩ : syracuseStep 6002009 = 4501507) B4501507
theorem B1873259 : Blo 1871637 1873259 := bstep (se 1 (by rfl) ⟨1404944, by rfl⟩ : syracuseStep 1873259 = 2809889) B2809889
theorem B31987061 : Blo 1871637 31987061 := bstep (se 5 (by rfl) ⟨1499393, by rfl⟩ : syracuseStep 31987061 = 2998787) B2998787
theorem B1873271 : Blo 1871637 1873271 := bstep (se 1 (by rfl) ⟨1404953, by rfl⟩ : syracuseStep 1873271 = 2809907) B2809907
theorem B1873291 : Blo 1871637 1873291 := bstep (se 1 (by rfl) ⟨1404968, by rfl⟩ : syracuseStep 1873291 = 2809937) B2809937
theorem B1873303 : Blo 1871637 1873303 := bstep (se 1 (by rfl) ⟨1404977, by rfl⟩ : syracuseStep 1873303 = 2809955) B2809955
theorem B1873323 : Blo 1871637 1873323 := bstep (se 1 (by rfl) ⟨1404992, by rfl⟩ : syracuseStep 1873323 = 2809985) B2809985
theorem B1873335 : Blo 1871637 1873335 := bstep (se 1 (by rfl) ⟨1405001, by rfl⟩ : syracuseStep 1873335 = 2810003) B2810003
theorem B4740545 : Blo 1871637 4740545 := bstep (se 2 (by rfl) ⟨1777704, by rfl⟩ : syracuseStep 4740545 = 3555409) B3555409
theorem B3159499 : Blo 1871637 3159499 := bstep (se 1 (by rfl) ⟨2369624, by rfl⟩ : syracuseStep 3159499 = 4739249) B4739249
theorem B1873355 : Blo 1871637 1873355 := bstep (se 1 (by rfl) ⟨1405016, by rfl⟩ : syracuseStep 1873355 = 2810033) B2810033
theorem B1873367 : Blo 1871637 1873367 := bstep (se 1 (by rfl) ⟨1405025, by rfl⟩ : syracuseStep 1873367 = 2810051) B2810051
theorem B1873387 : Blo 1871637 1873387 := bstep (se 1 (by rfl) ⟨1405040, by rfl⟩ : syracuseStep 1873387 = 2810081) B2810081
theorem B1873399 : Blo 1871637 1873399 := bstep (se 1 (by rfl) ⟨1405049, by rfl⟩ : syracuseStep 1873399 = 2810099) B2810099
theorem B1873419 : Blo 1871637 1873419 := bstep (se 1 (by rfl) ⟨1405064, by rfl⟩ : syracuseStep 1873419 = 2810129) B2810129
theorem B1873431 : Blo 1871637 1873431 := bstep (se 1 (by rfl) ⟨1405073, by rfl⟩ : syracuseStep 1873431 = 2810147) B2810147
theorem B1873451 : Blo 1871637 1873451 := bstep (se 1 (by rfl) ⟨1405088, by rfl⟩ : syracuseStep 1873451 = 2810177) B2810177
theorem B1873463 : Blo 1871637 1873463 := bstep (se 1 (by rfl) ⟨1405097, by rfl⟩ : syracuseStep 1873463 = 2810195) B2810195
theorem B1873483 : Blo 1871637 1873483 := bstep (se 1 (by rfl) ⟨1405112, by rfl⟩ : syracuseStep 1873483 = 2810225) B2810225
theorem B1873495 : Blo 1871637 1873495 := bstep (se 1 (by rfl) ⟨1405121, by rfl⟩ : syracuseStep 1873495 = 2810243) B2810243
theorem B3159641 : Blo 1871637 3159641 := bstep (se 2 (by rfl) ⟨1184865, by rfl⟩ : syracuseStep 3159641 = 2369731) B2369731
theorem B1873515 : Blo 1871637 1873515 := bstep (se 1 (by rfl) ⟨1405136, by rfl⟩ : syracuseStep 1873515 = 2810273) B2810273
theorem B1873527 : Blo 1871637 1873527 := bstep (se 1 (by rfl) ⟨1405145, by rfl⟩ : syracuseStep 1873527 = 2810291) B2810291
theorem B2250379 : Blo 1871637 2250379 := bstep (se 1 (by rfl) ⟨1687784, by rfl⟩ : syracuseStep 2250379 = 3375569) B3375569
theorem B1873547 : Blo 1871637 1873547 := bstep (se 1 (by rfl) ⟨1405160, by rfl⟩ : syracuseStep 1873547 = 2810321) B2810321
theorem B1873559 : Blo 1871637 1873559 := bstep (se 1 (by rfl) ⟨1405169, by rfl⟩ : syracuseStep 1873559 = 2810339) B2810339
theorem B1873579 : Blo 1871637 1873579 := bstep (se 1 (by rfl) ⟨1405184, by rfl⟩ : syracuseStep 1873579 = 2810369) B2810369
theorem B1873591 : Blo 1871637 1873591 := bstep (se 1 (by rfl) ⟨1405193, by rfl⟩ : syracuseStep 1873591 = 2810387) B2810387
theorem B1873611 : Blo 1871637 1873611 := bstep (se 1 (by rfl) ⟨1405208, by rfl⟩ : syracuseStep 1873611 = 2810417) B2810417
theorem B1873623 : Blo 1871637 1873623 := bstep (se 1 (by rfl) ⟨1405217, by rfl⟩ : syracuseStep 1873623 = 2810435) B2810435
theorem B2807513 : Blo 1871637 2807513 := bstep (se 2 (by rfl) ⟨1052817, by rfl⟩ : syracuseStep 2807513 = 2105635) B2105635
theorem B3159769 : Blo 1871637 3159769 := bstep (se 2 (by rfl) ⟨1184913, by rfl⟩ : syracuseStep 3159769 = 2369827) B2369827
theorem B5330711 : Blo 1871637 5330711 := bstep (se 1 (by rfl) ⟨3998033, by rfl⟩ : syracuseStep 5330711 = 7996067) B7996067
theorem B1898263 : Blo 1871637 1898263 := bstep (se 1 (by rfl) ⟨1423697, by rfl⟩ : syracuseStep 1898263 = 2847395) B2847395
theorem B2807627 : Blo 1871637 2807627 := bstep (se 1 (by rfl) ⟨2105720, by rfl⟩ : syracuseStep 2807627 = 4211441) B4211441
theorem B6321995 : Blo 1871637 6321995 := bstep (se 1 (by rfl) ⟨4741496, by rfl⟩ : syracuseStep 6321995 = 9482993) B9482993
theorem B2807639 : Blo 1871637 2807639 := bstep (se 1 (by rfl) ⟨2105729, by rfl⟩ : syracuseStep 2807639 = 4211459) B4211459
theorem B30381925 : Blo 1871637 30381925 := bstep (se 4 (by rfl) ⟨2848305, by rfl⟩ : syracuseStep 30381925 = 5696611) B5696611
theorem B2807705 : Blo 1871637 2807705 := bstep (se 2 (by rfl) ⟨1052889, by rfl⟩ : syracuseStep 2807705 = 2105779) B2105779
theorem B5060531 : Blo 1871637 5060531 := bstep (se 1 (by rfl) ⟨3795398, by rfl⟩ : syracuseStep 5060531 = 7590797) B7590797
theorem B4052929 : Blo 1871637 4052929 := bstep (se 2 (by rfl) ⟨1519848, by rfl⟩ : syracuseStep 4052929 = 3039697) B3039697
theorem B2807819 : Blo 1871637 2807819 := bstep (se 1 (by rfl) ⟨2105864, by rfl⟩ : syracuseStep 2807819 = 4211729) B4211729
theorem B11999249 : Blo 1871637 11999249 := bstep (se 2 (by rfl) ⟨4499718, by rfl⟩ : syracuseStep 11999249 = 8999437) B8999437
theorem B2807831 : Blo 1871637 2807831 := bstep (se 1 (by rfl) ⟨2105873, by rfl⟩ : syracuseStep 2807831 = 4211747) B4211747
theorem B7108631 : Blo 1871637 7108631 := bstep (se 1 (by rfl) ⟨5331473, by rfl⟩ : syracuseStep 7108631 = 10662947) B10662947
theorem B6404147 : Blo 1871637 6404147 := bstep (se 1 (by rfl) ⟨4803110, by rfl⟩ : syracuseStep 6404147 = 9606221) B9606221
theorem B2807897 : Blo 1871637 2807897 := bstep (se 2 (by rfl) ⟨1052961, by rfl⟩ : syracuseStep 2807897 = 2105923) B2105923
theorem B6322265 : Blo 1871637 6322265 := bstep (se 2 (by rfl) ⟨2370849, by rfl⟩ : syracuseStep 6322265 = 4741699) B4741699
theorem B9476189 : Blo 1871637 9476189 := bstep (se 3 (by rfl) ⟨1776785, by rfl⟩ : syracuseStep 9476189 = 3553571) B3553571
theorem B2808011 : Blo 1871637 2808011 := bstep (se 1 (by rfl) ⟨2106008, by rfl⟩ : syracuseStep 2808011 = 4212017) B4212017
theorem B2808023 : Blo 1871637 2808023 := bstep (se 1 (by rfl) ⟨2106017, by rfl⟩ : syracuseStep 2808023 = 4212035) B4212035
theorem B7108829 : Blo 1871637 7108829 := bstep (se 3 (by rfl) ⟨1332905, by rfl⟩ : syracuseStep 7108829 = 2665811) B2665811
theorem B3160343 : Blo 1871637 3160343 := bstep (se 1 (by rfl) ⟨2370257, by rfl⟩ : syracuseStep 3160343 = 4740515) B4740515
theorem B2808089 : Blo 1871637 2808089 := bstep (se 2 (by rfl) ⟨1053033, by rfl⟩ : syracuseStep 2808089 = 2106067) B2106067
theorem B3553625 : Blo 1871637 3553625 := bstep (se 2 (by rfl) ⟨1332609, by rfl⟩ : syracuseStep 3553625 = 2665219) B2665219
theorem B2808203 : Blo 1871637 2808203 := bstep (se 1 (by rfl) ⟨2106152, by rfl⟩ : syracuseStep 2808203 = 4212305) B4212305
theorem B2808215 : Blo 1871637 2808215 := bstep (se 1 (by rfl) ⟨2106161, by rfl⟩ : syracuseStep 2808215 = 4212323) B4212323
theorem B3160471 : Blo 1871637 3160471 := bstep (se 1 (by rfl) ⟨2370353, by rfl⟩ : syracuseStep 3160471 = 4740707) B4740707
theorem B2808281 : Blo 1871637 2808281 := bstep (se 2 (by rfl) ⟨1053105, by rfl⟩ : syracuseStep 2808281 = 2106211) B2106211
theorem B3373579 : Blo 1871637 3373579 := bstep (se 1 (by rfl) ⟨2530184, by rfl⟩ : syracuseStep 3373579 = 5060369) B5060369
theorem B2808395 : Blo 1871637 2808395 := bstep (se 1 (by rfl) ⟨2106296, by rfl⟩ : syracuseStep 2808395 = 4212593) B4212593
theorem B2808407 : Blo 1871637 2808407 := bstep (se 1 (by rfl) ⟨2106305, by rfl⟩ : syracuseStep 2808407 = 4212611) B4212611
theorem B15989399 : Blo 1871637 15989399 := bstep (se 1 (by rfl) ⟨11992049, by rfl⟩ : syracuseStep 15989399 = 23984099) B23984099
theorem B30366359 : Blo 1871637 30366359 := bstep (se 1 (by rfl) ⟨22774769, by rfl⟩ : syracuseStep 30366359 = 45549539) B45549539
theorem B2808473 : Blo 1871637 2808473 := bstep (se 2 (by rfl) ⟨1053177, by rfl⟩ : syracuseStep 2808473 = 2106355) B2106355
theorem B4741811 : Blo 1871637 4741811 := bstep (se 1 (by rfl) ⟨3556358, by rfl⟩ : syracuseStep 4741811 = 7112717) B7112717
theorem B2808587 : Blo 1871637 2808587 := bstep (se 1 (by rfl) ⟨2106440, by rfl⟩ : syracuseStep 2808587 = 4212881) B4212881
theorem B513137429 : Blo 1871637 513137429 := bstep (se 6 (by rfl) ⟨12026658, by rfl⟩ : syracuseStep 513137429 = 24053317) B24053317
theorem B2808599 : Blo 1871637 2808599 := bstep (se 1 (by rfl) ⟨2106449, by rfl⟩ : syracuseStep 2808599 = 4212899) B4212899
theorem B6322967 : Blo 1871637 6322967 := bstep (se 1 (by rfl) ⟨4742225, by rfl⟩ : syracuseStep 6322967 = 9484451) B9484451
theorem B2808665 : Blo 1871637 2808665 := bstep (se 2 (by rfl) ⟨1053249, by rfl⟩ : syracuseStep 2808665 = 2106499) B2106499
theorem B2808779 : Blo 1871637 2808779 := bstep (se 1 (by rfl) ⟨2106584, by rfl⟩ : syracuseStep 2808779 = 4213169) B4213169
theorem B2808791 : Blo 1871637 2808791 := bstep (se 1 (by rfl) ⟨2106593, by rfl⟩ : syracuseStep 2808791 = 4213187) B4213187
theorem B3161099 : Blo 1871637 3161099 := bstep (se 1 (by rfl) ⟨2370824, by rfl⟩ : syracuseStep 3161099 = 4741649) B4741649
theorem B2808857 : Blo 1871637 2808857 := bstep (se 2 (by rfl) ⟨1053321, by rfl⟩ : syracuseStep 2808857 = 2106643) B2106643
theorem B5332043 : Blo 1871637 5332043 := bstep (se 1 (by rfl) ⟨3999032, by rfl⟩ : syracuseStep 5332043 = 7998065) B7998065
theorem B2808971 : Blo 1871637 2808971 := bstep (se 1 (by rfl) ⟨2106728, by rfl⟩ : syracuseStep 2808971 = 4213457) B4213457
theorem B3161227 : Blo 1871637 3161227 := bstep (se 1 (by rfl) ⟨2370920, by rfl⟩ : syracuseStep 3161227 = 4741841) B4741841
theorem B2808983 : Blo 1871637 2808983 := bstep (se 1 (by rfl) ⟨2106737, by rfl⟩ : syracuseStep 2808983 = 4213475) B4213475
theorem B21339287 : Blo 1871637 21339287 := bstep (se 1 (by rfl) ⟨16004465, by rfl⟩ : syracuseStep 21339287 = 32008931) B32008931
theorem B4742347 : Blo 1871637 4742347 := bstep (se 1 (by rfl) ⟨3556760, by rfl⟩ : syracuseStep 4742347 = 7113521) B7113521
theorem B2809049 : Blo 1871637 2809049 := bstep (se 2 (by rfl) ⟨1053393, by rfl⟩ : syracuseStep 2809049 = 2106787) B2106787
theorem B3161369 : Blo 1871637 3161369 := bstep (se 2 (by rfl) ⟨1185513, by rfl⟩ : syracuseStep 3161369 = 2371027) B2371027
theorem B9002285 : Blo 1871637 9002285 := bstep (se 3 (by rfl) ⟨1687928, by rfl⟩ : syracuseStep 9002285 = 3375857) B3375857
theorem B6323507 : Blo 1871637 6323507 := bstep (se 1 (by rfl) ⟨4742630, by rfl⟩ : syracuseStep 6323507 = 9485261) B9485261
theorem B13491521 : Blo 1871637 13491521 := bstep (se 2 (by rfl) ⟨5059320, by rfl⟩ : syracuseStep 13491521 = 10118641) B10118641
theorem B3374401 : Blo 1871637 3374401 := bstep (se 2 (by rfl) ⟨1265400, by rfl⟩ : syracuseStep 3374401 = 2530801) B2530801
theorem B2809163 : Blo 1871637 2809163 := bstep (se 1 (by rfl) ⟨2106872, by rfl⟩ : syracuseStep 2809163 = 4213745) B4213745
theorem B2809175 : Blo 1871637 2809175 := bstep (se 1 (by rfl) ⟨2106881, by rfl⟩ : syracuseStep 2809175 = 4213763) B4213763
theorem B4742489 : Blo 1871637 4742489 := bstep (se 2 (by rfl) ⟨1778433, by rfl⟩ : syracuseStep 4742489 = 3556867) B3556867
theorem B2809241 : Blo 1871637 2809241 := bstep (se 2 (by rfl) ⟨1053465, by rfl⟩ : syracuseStep 2809241 = 2106931) B2106931
theorem B3161497 : Blo 1871637 3161497 := bstep (se 2 (by rfl) ⟨1185561, by rfl⟩ : syracuseStep 3161497 = 2371123) B2371123
theorem B2809355 : Blo 1871637 2809355 := bstep (se 1 (by rfl) ⟨2107016, by rfl⟩ : syracuseStep 2809355 = 4214033) B4214033
theorem B2809367 : Blo 1871637 2809367 := bstep (se 1 (by rfl) ⟨2107025, by rfl⟩ : syracuseStep 2809367 = 4214051) B4214051
theorem B3374617 : Blo 1871637 3374617 := bstep (se 2 (by rfl) ⟨1265481, by rfl⟩ : syracuseStep 3374617 = 2530963) B2530963
theorem B14220845 : Blo 1871637 14220845 := bstep (se 3 (by rfl) ⟨2666408, by rfl⟩ : syracuseStep 14220845 = 5332817) B5332817
theorem B8543789 : Blo 1871637 8543789 := bstep (se 3 (by rfl) ⟨1601960, by rfl⟩ : syracuseStep 8543789 = 3203921) B3203921
theorem B8003123 : Blo 1871637 8003123 := bstep (se 1 (by rfl) ⟨6002342, by rfl⟩ : syracuseStep 8003123 = 12004685) B12004685
theorem B2809433 : Blo 1871637 2809433 := bstep (se 2 (by rfl) ⟨1053537, by rfl⟩ : syracuseStep 2809433 = 2107075) B2107075
theorem B2809547 : Blo 1871637 2809547 := bstep (se 1 (by rfl) ⟨2107160, by rfl⟩ : syracuseStep 2809547 = 4214321) B4214321
theorem B2809559 : Blo 1871637 2809559 := bstep (se 1 (by rfl) ⟨2107169, by rfl⟩ : syracuseStep 2809559 = 4214339) B4214339
theorem B3555083 : Blo 1871637 3555083 := bstep (se 1 (by rfl) ⟨2666312, by rfl⟩ : syracuseStep 3555083 = 5332625) B5332625
theorem B2809625 : Blo 1871637 2809625 := bstep (se 2 (by rfl) ⟨1053609, by rfl⟩ : syracuseStep 2809625 = 2107219) B2107219
theorem B15998795 : Blo 1871637 15998795 := bstep (se 1 (by rfl) ⟨11999096, by rfl⟩ : syracuseStep 15998795 = 23998193) B23998193
theorem B1998679 : Blo 1871637 1998679 := bstep (se 1 (by rfl) ⟨1499009, by rfl⟩ : syracuseStep 1998679 = 2998019) B2998019
theorem B3997529 : Blo 1871637 3997529 := bstep (se 2 (by rfl) ⟨1499073, by rfl⟩ : syracuseStep 3997529 = 2998147) B2998147
theorem B3374963 : Blo 1871637 3374963 := bstep (se 1 (by rfl) ⟨2531222, by rfl⟩ : syracuseStep 3374963 = 5062445) B5062445
theorem B2809739 : Blo 1871637 2809739 := bstep (se 1 (by rfl) ⟨2107304, by rfl⟩ : syracuseStep 2809739 = 4214609) B4214609
theorem B2809751 : Blo 1871637 2809751 := bstep (se 1 (by rfl) ⟨2107313, by rfl⟩ : syracuseStep 2809751 = 4214627) B4214627
theorem B3555265 : Blo 1871637 3555265 := bstep (se 2 (by rfl) ⟨1333224, by rfl⟩ : syracuseStep 3555265 = 2666449) B2666449
theorem B6750155 : Blo 1871637 6750155 := bstep (se 1 (by rfl) ⟨5062616, by rfl⟩ : syracuseStep 6750155 = 10125233) B10125233
theorem B14213069 : Blo 1871637 14213069 := bstep (se 3 (by rfl) ⟨2664950, by rfl⟩ : syracuseStep 14213069 = 5329901) B5329901
theorem B2809817 : Blo 1871637 2809817 := bstep (se 2 (by rfl) ⟨1053681, by rfl⟩ : syracuseStep 2809817 = 2107363) B2107363
theorem B10125323 : Blo 1871637 10125323 := bstep (se 1 (by rfl) ⟨7593992, by rfl⟩ : syracuseStep 10125323 = 15187985) B15187985
theorem B2809871 : Blo 1871637 2809871 := bstep (se 1 (by rfl) ⟨2107403, by rfl⟩ : syracuseStep 2809871 = 4214807) B4214807
theorem B2809913 : Blo 1871637 2809913 := bstep (se 2 (by rfl) ⟨1053717, by rfl⟩ : syracuseStep 2809913 = 2107435) B2107435
theorem B19210301 : Blo 1871637 19210301 := bstep (se 3 (by rfl) ⟨3601931, by rfl⟩ : syracuseStep 19210301 = 7203863) B7203863
theorem B2809991 : Blo 1871637 2809991 := bstep (se 1 (by rfl) ⟨2107493, by rfl⟩ : syracuseStep 2809991 = 4214987) B4214987
theorem B2810027 : Blo 1871637 2810027 := bstep (se 1 (by rfl) ⟨2107520, by rfl⟩ : syracuseStep 2810027 = 4215041) B4215041
theorem B2810057 : Blo 1871637 2810057 := bstep (se 2 (by rfl) ⟨1053771, by rfl⟩ : syracuseStep 2810057 = 2107543) B2107543
theorem B2810171 : Blo 1871637 2810171 := bstep (se 1 (by rfl) ⟨2107628, by rfl⟩ : syracuseStep 2810171 = 4215257) B4215257
theorem B2810231 : Blo 1871637 2810231 := bstep (se 1 (by rfl) ⟨2107673, by rfl⟩ : syracuseStep 2810231 = 4215347) B4215347
theorem B2105743 : Blo 1871637 2105743 := bstep (se 1 (by rfl) ⟨1579307, by rfl⟩ : syracuseStep 2105743 = 3158615) B3158615
theorem B2810255 : Blo 1871637 2810255 := bstep (se 1 (by rfl) ⟨2107691, by rfl⟩ : syracuseStep 2810255 = 4215383) B4215383
theorem B14418323 : Blo 1871637 14418323 := bstep (se 1 (by rfl) ⟨10813742, by rfl⟩ : syracuseStep 14418323 = 21627485) B21627485
theorem B2810297 : Blo 1871637 2810297 := bstep (se 2 (by rfl) ⟨1053861, by rfl⟩ : syracuseStep 2810297 = 2107723) B2107723
theorem B36012509 : Blo 1871637 36012509 := bstep (se 3 (by rfl) ⟨6752345, by rfl⟩ : syracuseStep 36012509 = 13504691) B13504691
theorem B2810375 : Blo 1871637 2810375 := bstep (se 1 (by rfl) ⟨2107781, by rfl⟩ : syracuseStep 2810375 = 4215563) B4215563
theorem B4211243 : Blo 1871637 4211243 := bstep (se 1 (by rfl) ⟨3158432, by rfl⟩ : syracuseStep 4211243 = 6316865) B6316865
theorem B2810411 : Blo 1871637 2810411 := bstep (se 1 (by rfl) ⟨2107808, by rfl⟩ : syracuseStep 2810411 = 4215617) B4215617
theorem B2810441 : Blo 1871637 2810441 := bstep (se 2 (by rfl) ⟨1053915, by rfl⟩ : syracuseStep 2810441 = 2107831) B2107831
theorem B1999495 : Blo 1871637 1999495 := bstep (se 1 (by rfl) ⟨1499621, by rfl⟩ : syracuseStep 1999495 = 2999243) B2999243
theorem B4498067 : Blo 1871637 4498067 := bstep (se 1 (by rfl) ⟨3373550, by rfl⟩ : syracuseStep 4498067 = 6747101) B6747101
theorem B4498105 : Blo 1871637 4498105 := bstep (se 2 (by rfl) ⟨1686789, by rfl⟩ : syracuseStep 4498105 = 3373579) B3373579
theorem B2106247 : Blo 1871637 2106247 := bstep (se 1 (by rfl) ⟨1579685, by rfl⟩ : syracuseStep 2106247 = 3159371) B3159371
theorem B4211603 : Blo 1871637 4211603 := bstep (se 1 (by rfl) ⟨3158702, by rfl⟩ : syracuseStep 4211603 = 6317405) B6317405
theorem B14214041 : Blo 1871637 14214041 := bstep (se 2 (by rfl) ⟨5330265, by rfl⟩ : syracuseStep 14214041 = 10660531) B10660531
theorem B7111577 : Blo 1871637 7111577 := bstep (se 2 (by rfl) ⟨2666841, by rfl⟩ : syracuseStep 7111577 = 5333683) B5333683
theorem B21324707 : Blo 1871637 21324707 := bstep (se 1 (by rfl) ⟨15993530, by rfl⟩ : syracuseStep 21324707 = 31987061) B31987061
theorem B4211657 : Blo 1871637 4211657 := bstep (se 2 (by rfl) ⟨1579371, by rfl⟩ : syracuseStep 4211657 = 3158743) B3158743
theorem B2106427 : Blo 1871637 2106427 := bstep (se 1 (by rfl) ⟨1579820, by rfl⟩ : syracuseStep 2106427 = 3159641) B3159641
theorem B22774871 : Blo 1871637 22774871 := bstep (se 1 (by rfl) ⟨17081153, by rfl⟩ : syracuseStep 22774871 = 34162307) B34162307
theorem B3556487 : Blo 1871637 3556487 := bstep (se 1 (by rfl) ⟨2667365, by rfl⟩ : syracuseStep 3556487 = 5334731) B5334731
theorem B4269431 : Blo 1871637 4269431 := bstep (se 1 (by rfl) ⟨3202073, by rfl⟩ : syracuseStep 4269431 = 6404147) B6404147
theorem B6317459 : Blo 1871637 6317459 := bstep (se 1 (by rfl) ⟨4738094, by rfl⟩ : syracuseStep 6317459 = 9476189) B9476189
theorem B2106895 : Blo 1871637 2106895 := bstep (se 1 (by rfl) ⟨1580171, by rfl⟩ : syracuseStep 2106895 = 3160343) B3160343
theorem B2369083 : Blo 1871637 2369083 := bstep (se 1 (by rfl) ⟨1776812, by rfl⟩ : syracuseStep 2369083 = 3553625) B3553625
theorem B10667639 : Blo 1871637 10667639 := bstep (se 1 (by rfl) ⟨8000729, by rfl⟩ : syracuseStep 10667639 = 16001459) B16001459
theorem B4212359 : Blo 1871637 4212359 := bstep (se 1 (by rfl) ⟨3159269, by rfl⟩ : syracuseStep 4212359 = 6318539) B6318539
theorem B4499201 : Blo 1871637 4499201 := bstep (se 2 (by rfl) ⟨1687200, by rfl⟩ : syracuseStep 4499201 = 3374401) B3374401
theorem B10659599 : Blo 1871637 10659599 := bstep (se 1 (by rfl) ⟨7994699, by rfl⟩ : syracuseStep 10659599 = 15989399) B15989399
theorem B20244239 : Blo 1871637 20244239 := bstep (se 1 (by rfl) ⟨15183179, by rfl⟩ : syracuseStep 20244239 = 30366359) B30366359
theorem B4212539 : Blo 1871637 4212539 := bstep (se 1 (by rfl) ⟨3159404, by rfl⟩ : syracuseStep 4212539 = 6318809) B6318809
theorem B342091619 : Blo 1871637 342091619 := bstep (se 1 (by rfl) ⟨256568714, by rfl⟩ : syracuseStep 342091619 = 513137429) B513137429
theorem B4212665 : Blo 1871637 4212665 := bstep (se 2 (by rfl) ⟨1579749, by rfl⟩ : syracuseStep 4212665 = 3159499) B3159499
theorem B2107399 : Blo 1871637 2107399 := bstep (se 1 (by rfl) ⟨1580549, by rfl⟩ : syracuseStep 2107399 = 3161099) B3161099
theorem B4499489 : Blo 1871637 4499489 := bstep (se 2 (by rfl) ⟨1687308, by rfl⟩ : syracuseStep 4499489 = 3374617) B3374617
theorem B3000505 : Blo 1871637 3000505 := bstep (se 2 (by rfl) ⟨1125189, by rfl⟩ : syracuseStep 3000505 = 2250379) B2250379
theorem B2107579 : Blo 1871637 2107579 := bstep (se 1 (by rfl) ⟨1580684, by rfl⟩ : syracuseStep 2107579 = 3161369) B3161369
theorem B17991881 : Blo 1871637 17991881 := bstep (se 2 (by rfl) ⟨6746955, by rfl⟩ : syracuseStep 17991881 = 13493911) B13493911
theorem B4213007 : Blo 1871637 4213007 := bstep (se 1 (by rfl) ⟨3159755, by rfl⟩ : syracuseStep 4213007 = 6319511) B6319511
theorem B4213025 : Blo 1871637 4213025 := bstep (se 2 (by rfl) ⟨1579884, by rfl⟩ : syracuseStep 4213025 = 3159769) B3159769
theorem B76900661 : Blo 1871637 76900661 := bstep (se 5 (by rfl) ⟨3604718, by rfl⟩ : syracuseStep 76900661 = 7209437) B7209437
theorem B5998907 : Blo 1871637 5998907 := bstep (se 1 (by rfl) ⟨4499180, by rfl⟩ : syracuseStep 5998907 = 8998361) B8998361
theorem B10668347 : Blo 1871637 10668347 := bstep (se 1 (by rfl) ⟨8001260, by rfl⟩ : syracuseStep 10668347 = 16002521) B16002521
theorem B4622707 : Blo 1871637 4622707 := bstep (se 1 (by rfl) ⟨3467030, by rfl⟩ : syracuseStep 4622707 = 6934061) B6934061
theorem B9480563 : Blo 1871637 9480563 := bstep (se 1 (by rfl) ⟨7110422, by rfl⟩ : syracuseStep 9480563 = 14220845) B14220845
theorem B5695859 : Blo 1871637 5695859 := bstep (se 1 (by rfl) ⟨4271894, by rfl⟩ : syracuseStep 5695859 = 8543789) B8543789
theorem B5335415 : Blo 1871637 5335415 := bstep (se 1 (by rfl) ⟨4001561, by rfl⟩ : syracuseStep 5335415 = 8003123) B8003123
theorem B14223761 : Blo 1871637 14223761 := bstep (se 2 (by rfl) ⟨5333910, by rfl⟩ : syracuseStep 14223761 = 10667821) B10667821
theorem B2664905 : Blo 1871637 2664905 := bstep (se 2 (by rfl) ⟨999339, by rfl⟩ : syracuseStep 2664905 = 1998679) B1998679
theorem B11995613 : Blo 1871637 11995613 := bstep (se 3 (by rfl) ⟨2249177, by rfl⟩ : syracuseStep 11995613 = 4498355) B4498355
theorem B2370055 : Blo 1871637 2370055 := bstep (se 1 (by rfl) ⟨1777541, by rfl⟩ : syracuseStep 2370055 = 3555083) B3555083
theorem B18000413 : Blo 1871637 18000413 := bstep (se 3 (by rfl) ⟨3375077, by rfl⟩ : syracuseStep 18000413 = 6750155) B6750155
theorem B2665019 : Blo 1871637 2665019 := bstep (se 1 (by rfl) ⟨1998764, by rfl⟩ : syracuseStep 2665019 = 3997529) B3997529
theorem B4213367 : Blo 1871637 4213367 := bstep (se 1 (by rfl) ⟨3160025, by rfl⟩ : syracuseStep 4213367 = 6320051) B6320051
theorem B10119917 : Blo 1871637 10119917 := bstep (se 3 (by rfl) ⟨1897484, by rfl⟩ : syracuseStep 10119917 = 3794969) B3794969
theorem B6318863 : Blo 1871637 6318863 := bstep (se 1 (by rfl) ⟨4739147, by rfl⟩ : syracuseStep 6318863 = 9478295) B9478295
theorem B23997221 : Blo 1871637 23997221 := bstep (se 4 (by rfl) ⟨2249739, by rfl⟩ : syracuseStep 23997221 = 4499479) B4499479
theorem B4213547 : Blo 1871637 4213547 := bstep (se 1 (by rfl) ⟨3160160, by rfl⟩ : syracuseStep 4213547 = 6320321) B6320321
theorem B14215985 : Blo 1871637 14215985 := bstep (se 2 (by rfl) ⟨5330994, by rfl⟩ : syracuseStep 14215985 = 10661989) B10661989
theorem B9481049 : Blo 1871637 9481049 := bstep (se 2 (by rfl) ⟨3555393, by rfl⟩ : syracuseStep 9481049 = 7110787) B7110787
theorem B3795859 : Blo 1871637 3795859 := bstep (se 1 (by rfl) ⟨2846894, by rfl⟩ : syracuseStep 3795859 = 5693789) B5693789
theorem B2370475 : Blo 1871637 2370475 := bstep (se 1 (by rfl) ⟨1777856, by rfl⟩ : syracuseStep 2370475 = 3555713) B3555713
theorem B12004375 : Blo 1871637 12004375 := bstep (se 1 (by rfl) ⟨9003281, by rfl⟩ : syracuseStep 12004375 = 18006563) B18006563
theorem B6319133 : Blo 1871637 6319133 := bstep (se 3 (by rfl) ⟨1184837, by rfl⟩ : syracuseStep 6319133 = 2369675) B2369675
theorem B4738135 : Blo 1871637 4738135 := bstep (se 1 (by rfl) ⟨3553601, by rfl⟩ : syracuseStep 4738135 = 7107203) B7107203
theorem B2370703 : Blo 1871637 2370703 := bstep (se 1 (by rfl) ⟨1778027, by rfl⟩ : syracuseStep 2370703 = 3556055) B3556055
theorem B4213907 : Blo 1871637 4213907 := bstep (se 1 (by rfl) ⟨3160430, by rfl⟩ : syracuseStep 4213907 = 6320861) B6320861
theorem B2665657 : Blo 1871637 2665657 := bstep (se 2 (by rfl) ⟨999621, by rfl⟩ : syracuseStep 2665657 = 1999243) B1999243
theorem B10661057 : Blo 1871637 10661057 := bstep (se 2 (by rfl) ⟨3997896, by rfl⟩ : syracuseStep 10661057 = 7995793) B7995793
theorem B4213961 : Blo 1871637 4213961 := bstep (se 2 (by rfl) ⟨1580235, by rfl⟩ : syracuseStep 4213961 = 3160471) B3160471
theorem B3796283 : Blo 1871637 3796283 := bstep (se 1 (by rfl) ⟨2847212, by rfl⟩ : syracuseStep 3796283 = 5694425) B5694425
theorem B4738439 : Blo 1871637 4738439 := bstep (se 1 (by rfl) ⟨3553829, by rfl⟩ : syracuseStep 4738439 = 7107659) B7107659
theorem B43249031 : Blo 1871637 43249031 := bstep (se 1 (by rfl) ⟨32436773, by rfl⟩ : syracuseStep 43249031 = 64873547) B64873547
theorem B13495697 : Blo 1871637 13495697 := bstep (se 2 (by rfl) ⟨5060886, by rfl⟩ : syracuseStep 13495697 = 10121773) B10121773
theorem B4738571 : Blo 1871637 4738571 := bstep (se 1 (by rfl) ⟨3553928, by rfl⟩ : syracuseStep 4738571 = 7107857) B7107857
theorem B4001339 : Blo 1871637 4001339 := bstep (se 1 (by rfl) ⟨3001004, by rfl⟩ : syracuseStep 4001339 = 6002009) B6002009
theorem B10669805 : Blo 1871637 10669805 := bstep (se 3 (by rfl) ⟨2000588, by rfl⟩ : syracuseStep 10669805 = 4001177) B4001177
theorem B1871675 : Blo 1871637 1871675 := bstep (se 1 (by rfl) ⟨1403756, by rfl⟩ : syracuseStep 1871675 = 2807513) B2807513
theorem B40488821 : Blo 1871637 40488821 := bstep (se 5 (by rfl) ⟨1897913, by rfl⟩ : syracuseStep 40488821 = 3795827) B3795827
theorem B1871751 : Blo 1871637 1871751 := bstep (se 1 (by rfl) ⟨1403813, by rfl⟩ : syracuseStep 1871751 = 2807627) B2807627
theorem B4214663 : Blo 1871637 4214663 := bstep (se 1 (by rfl) ⟨3160997, by rfl⟩ : syracuseStep 4214663 = 6321995) B6321995
theorem B1871759 : Blo 1871637 1871759 := bstep (se 1 (by rfl) ⟨1403819, by rfl⟩ : syracuseStep 1871759 = 2807639) B2807639
theorem B1871803 : Blo 1871637 1871803 := bstep (se 1 (by rfl) ⟨1403852, by rfl⟩ : syracuseStep 1871803 = 2807705) B2807705
theorem B1871879 : Blo 1871637 1871879 := bstep (se 1 (by rfl) ⟨1403909, by rfl⟩ : syracuseStep 1871879 = 2807819) B2807819
theorem B7999499 : Blo 1871637 7999499 := bstep (se 1 (by rfl) ⟨5999624, by rfl⟩ : syracuseStep 7999499 = 11999249) B11999249
theorem B1871887 : Blo 1871637 1871887 := bstep (se 1 (by rfl) ⟨1403915, by rfl⟩ : syracuseStep 1871887 = 2807831) B2807831
theorem B4739087 : Blo 1871637 4739087 := bstep (se 1 (by rfl) ⟨3554315, by rfl⟩ : syracuseStep 4739087 = 7108631) B7108631
theorem B1871931 : Blo 1871637 1871931 := bstep (se 1 (by rfl) ⟨1403948, by rfl⟩ : syracuseStep 1871931 = 2807897) B2807897
theorem B4214843 : Blo 1871637 4214843 := bstep (se 1 (by rfl) ⟨3161132, by rfl⟩ : syracuseStep 4214843 = 6322265) B6322265
theorem B1872007 : Blo 1871637 1872007 := bstep (se 1 (by rfl) ⟨1404005, by rfl⟩ : syracuseStep 1872007 = 2808011) B2808011
theorem B1872015 : Blo 1871637 1872015 := bstep (se 1 (by rfl) ⟨1404011, by rfl⟩ : syracuseStep 1872015 = 2808023) B2808023
theorem B4739219 : Blo 1871637 4739219 := bstep (se 1 (by rfl) ⟨3554414, by rfl⟩ : syracuseStep 4739219 = 7108829) B7108829
theorem B4214969 : Blo 1871637 4214969 := bstep (se 2 (by rfl) ⟨1580613, by rfl⟩ : syracuseStep 4214969 = 3161227) B3161227
theorem B1872059 : Blo 1871637 1872059 := bstep (se 1 (by rfl) ⟨1404044, by rfl⟩ : syracuseStep 1872059 = 2808089) B2808089
theorem B35983601 : Blo 1871637 35983601 := bstep (se 2 (by rfl) ⟨13493850, by rfl⟩ : syracuseStep 35983601 = 26987701) B26987701
theorem B1872135 : Blo 1871637 1872135 := bstep (se 1 (by rfl) ⟨1404101, by rfl⟩ : syracuseStep 1872135 = 2808203) B2808203
theorem B1872143 : Blo 1871637 1872143 := bstep (se 1 (by rfl) ⟨1404107, by rfl⟩ : syracuseStep 1872143 = 2808215) B2808215
theorem B1872187 : Blo 1871637 1872187 := bstep (se 1 (by rfl) ⟨1404140, by rfl⟩ : syracuseStep 1872187 = 2808281) B2808281
theorem B1872263 : Blo 1871637 1872263 := bstep (se 1 (by rfl) ⟨1404197, by rfl⟩ : syracuseStep 1872263 = 2808395) B2808395
theorem B1872271 : Blo 1871637 1872271 := bstep (se 1 (by rfl) ⟨1404203, by rfl⟩ : syracuseStep 1872271 = 2808407) B2808407
theorem B6320537 : Blo 1871637 6320537 := bstep (se 2 (by rfl) ⟨2370201, by rfl⟩ : syracuseStep 6320537 = 4740403) B4740403
theorem B1872315 : Blo 1871637 1872315 := bstep (se 1 (by rfl) ⟨1404236, by rfl⟩ : syracuseStep 1872315 = 2808473) B2808473
theorem B3158473 : Blo 1871637 3158473 := bstep (se 2 (by rfl) ⟨1184427, by rfl⟩ : syracuseStep 3158473 = 2368855) B2368855
theorem B1872391 : Blo 1871637 1872391 := bstep (se 1 (by rfl) ⟨1404293, by rfl⟩ : syracuseStep 1872391 = 2808587) B2808587
theorem B1872399 : Blo 1871637 1872399 := bstep (se 1 (by rfl) ⟨1404299, by rfl⟩ : syracuseStep 1872399 = 2808599) B2808599
theorem B4215311 : Blo 1871637 4215311 := bstep (se 1 (by rfl) ⟨3161483, by rfl⟩ : syracuseStep 4215311 = 6322967) B6322967
theorem B4215329 : Blo 1871637 4215329 := bstep (se 2 (by rfl) ⟨1580748, by rfl⟩ : syracuseStep 4215329 = 3161497) B3161497
theorem B1872443 : Blo 1871637 1872443 := bstep (se 1 (by rfl) ⟨1404332, by rfl⟩ : syracuseStep 1872443 = 2808665) B2808665
theorem B1872519 : Blo 1871637 1872519 := bstep (se 1 (by rfl) ⟨1404389, by rfl⟩ : syracuseStep 1872519 = 2808779) B2808779
theorem B1872527 : Blo 1871637 1872527 := bstep (se 1 (by rfl) ⟨1404395, by rfl⟩ : syracuseStep 1872527 = 2808791) B2808791
theorem B1872571 : Blo 1871637 1872571 := bstep (se 1 (by rfl) ⟨1404428, by rfl⟩ : syracuseStep 1872571 = 2808857) B2808857
theorem B1872647 : Blo 1871637 1872647 := bstep (se 1 (by rfl) ⟨1404485, by rfl⟩ : syracuseStep 1872647 = 2808971) B2808971
theorem B1872655 : Blo 1871637 1872655 := bstep (se 1 (by rfl) ⟨1404491, by rfl⟩ : syracuseStep 1872655 = 2808983) B2808983
theorem B14226191 : Blo 1871637 14226191 := bstep (se 1 (by rfl) ⟨10669643, by rfl⟩ : syracuseStep 14226191 = 21339287) B21339287
theorem B1872699 : Blo 1871637 1872699 := bstep (se 1 (by rfl) ⟨1404524, by rfl⟩ : syracuseStep 1872699 = 2809049) B2809049
theorem B36008819 : Blo 1871637 36008819 := bstep (se 1 (by rfl) ⟨27006614, by rfl⟩ : syracuseStep 36008819 = 54013229) B54013229
theorem B6001523 : Blo 1871637 6001523 := bstep (se 1 (by rfl) ⟨4501142, by rfl⟩ : syracuseStep 6001523 = 9002285) B9002285
theorem B4215671 : Blo 1871637 4215671 := bstep (se 1 (by rfl) ⟨3161753, by rfl⟩ : syracuseStep 4215671 = 6323507) B6323507
theorem B1872775 : Blo 1871637 1872775 := bstep (se 1 (by rfl) ⟨1404581, by rfl⟩ : syracuseStep 1872775 = 2809163) B2809163
theorem B1872783 : Blo 1871637 1872783 := bstep (se 1 (by rfl) ⟨1404587, by rfl⟩ : syracuseStep 1872783 = 2809175) B2809175
theorem B9483155 : Blo 1871637 9483155 := bstep (se 1 (by rfl) ⟨7112366, by rfl⟩ : syracuseStep 9483155 = 14224733) B14224733
theorem B8000441 : Blo 1871637 8000441 := bstep (se 2 (by rfl) ⟨3000165, by rfl⟩ : syracuseStep 8000441 = 6000331) B6000331
theorem B1872827 : Blo 1871637 1872827 := bstep (se 1 (by rfl) ⟨1404620, by rfl⟩ : syracuseStep 1872827 = 2809241) B2809241
theorem B1872903 : Blo 1871637 1872903 := bstep (se 1 (by rfl) ⟨1404677, by rfl⟩ : syracuseStep 1872903 = 2809355) B2809355
theorem B1872911 : Blo 1871637 1872911 := bstep (se 1 (by rfl) ⟨1404683, by rfl⟩ : syracuseStep 1872911 = 2809367) B2809367
theorem B1872955 : Blo 1871637 1872955 := bstep (se 1 (by rfl) ⟨1404716, by rfl⟩ : syracuseStep 1872955 = 2809433) B2809433
theorem B6321239 : Blo 1871637 6321239 := bstep (se 1 (by rfl) ⟨4740929, by rfl⟩ : syracuseStep 6321239 = 9481859) B9481859
theorem B3159175 : Blo 1871637 3159175 := bstep (se 1 (by rfl) ⟨2369381, by rfl⟩ : syracuseStep 3159175 = 4738763) B4738763
theorem B1873031 : Blo 1871637 1873031 := bstep (se 1 (by rfl) ⟨1404773, by rfl⟩ : syracuseStep 1873031 = 2809547) B2809547
theorem B1873039 : Blo 1871637 1873039 := bstep (se 1 (by rfl) ⟨1404779, by rfl⟩ : syracuseStep 1873039 = 2809559) B2809559
theorem B1873083 : Blo 1871637 1873083 := bstep (se 1 (by rfl) ⟨1404812, by rfl⟩ : syracuseStep 1873083 = 2809625) B2809625
theorem B2249975 : Blo 1871637 2249975 := bstep (se 1 (by rfl) ⟨1687481, by rfl⟩ : syracuseStep 2249975 = 3374963) B3374963
theorem B5403905 : Blo 1871637 5403905 := bstep (se 2 (by rfl) ⟨2026464, by rfl⟩ : syracuseStep 5403905 = 4052929) B4052929
theorem B4740353 : Blo 1871637 4740353 := bstep (se 2 (by rfl) ⟨1777632, by rfl⟩ : syracuseStep 4740353 = 3555265) B3555265
theorem B1873159 : Blo 1871637 1873159 := bstep (se 1 (by rfl) ⟨1404869, by rfl⟩ : syracuseStep 1873159 = 2809739) B2809739
theorem B1873167 : Blo 1871637 1873167 := bstep (se 1 (by rfl) ⟨1404875, by rfl⟩ : syracuseStep 1873167 = 2809751) B2809751
theorem B9745697 : Blo 1871637 9745697 := bstep (se 2 (by rfl) ⟨3654636, by rfl⟩ : syracuseStep 9745697 = 7309273) B7309273
theorem B9475379 : Blo 1871637 9475379 := bstep (se 1 (by rfl) ⟨7106534, by rfl⟩ : syracuseStep 9475379 = 14213069) B14213069
theorem B1873211 : Blo 1871637 1873211 := bstep (se 1 (by rfl) ⟨1404908, by rfl⟩ : syracuseStep 1873211 = 2809817) B2809817
theorem B51230083 : Blo 1871637 51230083 := bstep (se 1 (by rfl) ⟨38422562, by rfl⟩ : syracuseStep 51230083 = 76845125) B76845125
theorem B1873287 : Blo 1871637 1873287 := bstep (se 1 (by rfl) ⟨1404965, by rfl⟩ : syracuseStep 1873287 = 2809931) B2809931
theorem B1873295 : Blo 1871637 1873295 := bstep (se 1 (by rfl) ⟨1404971, by rfl⟩ : syracuseStep 1873295 = 2809943) B2809943
theorem B26990009 : Blo 1871637 26990009 := bstep (se 2 (by rfl) ⟨10121253, by rfl⟩ : syracuseStep 26990009 = 20242507) B20242507
theorem B1873339 : Blo 1871637 1873339 := bstep (se 1 (by rfl) ⟨1405004, by rfl⟩ : syracuseStep 1873339 = 2810009) B2810009
theorem B1873415 : Blo 1871637 1873415 := bstep (se 1 (by rfl) ⟨1405061, by rfl⟩ : syracuseStep 1873415 = 2810123) B2810123
theorem B1873423 : Blo 1871637 1873423 := bstep (se 1 (by rfl) ⟨1405067, by rfl⟩ : syracuseStep 1873423 = 2810135) B2810135
theorem B10663447 : Blo 1871637 10663447 := bstep (se 1 (by rfl) ⟨7997585, by rfl⟩ : syracuseStep 10663447 = 15995171) B15995171
theorem B2250283 : Blo 1871637 2250283 := bstep (se 1 (by rfl) ⟨1687712, by rfl⟩ : syracuseStep 2250283 = 3375425) B3375425
theorem B1873467 : Blo 1871637 1873467 := bstep (se 1 (by rfl) ⟨1405100, by rfl⟩ : syracuseStep 1873467 = 2810201) B2810201
theorem B6321725 : Blo 1871637 6321725 := bstep (se 3 (by rfl) ⟨1185323, by rfl⟩ : syracuseStep 6321725 = 2370647) B2370647
theorem B53966411 : Blo 1871637 53966411 := bstep (se 1 (by rfl) ⟨40474808, by rfl⟩ : syracuseStep 53966411 = 80949617) B80949617
theorem B9475703 : Blo 1871637 9475703 := bstep (se 1 (by rfl) ⟨7106777, by rfl⟩ : syracuseStep 9475703 = 14213555) B14213555
theorem B4740727 : Blo 1871637 4740727 := bstep (se 1 (by rfl) ⟨3555545, by rfl⟩ : syracuseStep 4740727 = 7111091) B7111091
theorem B1873543 : Blo 1871637 1873543 := bstep (se 1 (by rfl) ⟨1405157, by rfl⟩ : syracuseStep 1873543 = 2810315) B2810315
theorem B1873551 : Blo 1871637 1873551 := bstep (se 1 (by rfl) ⟨1405163, by rfl⟩ : syracuseStep 1873551 = 2810327) B2810327
theorem B5330585 : Blo 1871637 5330585 := bstep (se 2 (by rfl) ⟨1998969, by rfl⟩ : syracuseStep 5330585 = 3997939) B3997939
theorem B2807483 : Blo 1871637 2807483 := bstep (se 1 (by rfl) ⟨2105612, by rfl⟩ : syracuseStep 2807483 = 4211225) B4211225
theorem B1873595 : Blo 1871637 1873595 := bstep (se 1 (by rfl) ⟨1405196, by rfl⟩ : syracuseStep 1873595 = 2810393) B2810393
theorem B21337829 : Blo 1871637 21337829 := bstep (se 4 (by rfl) ⟨2000421, by rfl⟩ : syracuseStep 21337829 = 4000843) B4000843
theorem B2807543 : Blo 1871637 2807543 := bstep (se 1 (by rfl) ⟨2105657, by rfl⟩ : syracuseStep 2807543 = 4211315) B4211315
theorem B2807567 : Blo 1871637 2807567 := bstep (se 1 (by rfl) ⟨2105675, by rfl⟩ : syracuseStep 2807567 = 4211351) B4211351
theorem B3159823 : Blo 1871637 3159823 := bstep (se 1 (by rfl) ⟨2369867, by rfl⟩ : syracuseStep 3159823 = 4739735) B4739735
theorem B6403873 : Blo 1871637 6403873 := bstep (se 2 (by rfl) ⟨2401452, by rfl⟩ : syracuseStep 6403873 = 4802905) B4802905
theorem B2807609 : Blo 1871637 2807609 := bstep (se 2 (by rfl) ⟨1052853, by rfl⟩ : syracuseStep 2807609 = 2105707) B2105707
theorem B5060411 : Blo 1871637 5060411 := bstep (se 1 (by rfl) ⟨3795308, by rfl⟩ : syracuseStep 5060411 = 7590617) B7590617
theorem B17086297 : Blo 1871637 17086297 := bstep (se 2 (by rfl) ⟨6407361, by rfl⟩ : syracuseStep 17086297 = 12814723) B12814723
theorem B11392883 : Blo 1871637 11392883 := bstep (se 1 (by rfl) ⟨8544662, by rfl⟩ : syracuseStep 11392883 = 17089325) B17089325
theorem B2807687 : Blo 1871637 2807687 := bstep (se 1 (by rfl) ⟨2105765, by rfl⟩ : syracuseStep 2807687 = 4211531) B4211531
theorem B2807723 : Blo 1871637 2807723 := bstep (se 1 (by rfl) ⟨2105792, by rfl⟩ : syracuseStep 2807723 = 4211585) B4211585
theorem B2250667 : Blo 1871637 2250667 := bstep (se 1 (by rfl) ⟨1688000, by rfl⟩ : syracuseStep 2250667 = 3376001) B3376001
theorem B2807753 : Blo 1871637 2807753 := bstep (se 2 (by rfl) ⟨1052907, by rfl⟩ : syracuseStep 2807753 = 2105815) B2105815
theorem B4741163 : Blo 1871637 4741163 := bstep (se 1 (by rfl) ⟨3555872, by rfl⟩ : syracuseStep 4741163 = 7111745) B7111745
theorem B2807867 : Blo 1871637 2807867 := bstep (se 1 (by rfl) ⟨2105900, by rfl⟩ : syracuseStep 2807867 = 4211801) B4211801
theorem B5773373 : Blo 1871637 5773373 := bstep (se 3 (by rfl) ⟨1082507, by rfl⟩ : syracuseStep 5773373 = 2165015) B2165015
theorem B2807927 : Blo 1871637 2807927 := bstep (se 1 (by rfl) ⟨2105945, by rfl⟩ : syracuseStep 2807927 = 4211891) B4211891
theorem B2807951 : Blo 1871637 2807951 := bstep (se 1 (by rfl) ⟨2105963, by rfl⟩ : syracuseStep 2807951 = 4211927) B4211927
theorem B9124013 : Blo 1871637 9124013 := bstep (se 3 (by rfl) ⟨1710752, by rfl⟩ : syracuseStep 9124013 = 3421505) B3421505
theorem B3553465 : Blo 1871637 3553465 := bstep (se 2 (by rfl) ⟨1332549, by rfl⟩ : syracuseStep 3553465 = 2665099) B2665099
theorem B2807993 : Blo 1871637 2807993 := bstep (se 2 (by rfl) ⟨1052997, by rfl⟩ : syracuseStep 2807993 = 2105995) B2105995
theorem B2808071 : Blo 1871637 2808071 := bstep (se 1 (by rfl) ⟨2106053, by rfl⟩ : syracuseStep 2808071 = 4212107) B4212107
theorem B2808107 : Blo 1871637 2808107 := bstep (se 1 (by rfl) ⟨2106080, by rfl⟩ : syracuseStep 2808107 = 4212161) B4212161
theorem B3160363 : Blo 1871637 3160363 := bstep (se 1 (by rfl) ⟨2370272, by rfl⟩ : syracuseStep 3160363 = 4740545) B4740545
theorem B2808137 : Blo 1871637 2808137 := bstep (se 2 (by rfl) ⟨1053051, by rfl⟩ : syracuseStep 2808137 = 2106103) B2106103
theorem B4561267 : Blo 1871637 4561267 := bstep (se 1 (by rfl) ⟨3420950, by rfl⟩ : syracuseStep 4561267 = 6841901) B6841901
theorem B3160505 : Blo 1871637 3160505 := bstep (se 2 (by rfl) ⟨1185189, by rfl⟩ : syracuseStep 3160505 = 2370379) B2370379
theorem B2808251 : Blo 1871637 2808251 := bstep (se 1 (by rfl) ⟨2106188, by rfl⟩ : syracuseStep 2808251 = 4212377) B4212377
theorem B2808311 : Blo 1871637 2808311 := bstep (se 1 (by rfl) ⟨2106233, by rfl⟩ : syracuseStep 2808311 = 4212467) B4212467
theorem B3553807 : Blo 1871637 3553807 := bstep (se 1 (by rfl) ⟨2665355, by rfl⟩ : syracuseStep 3553807 = 5330711) B5330711
theorem B2808335 : Blo 1871637 2808335 := bstep (se 1 (by rfl) ⟨2106251, by rfl⟩ : syracuseStep 2808335 = 4212503) B4212503
theorem B2808377 : Blo 1871637 2808377 := bstep (se 2 (by rfl) ⟨1053141, by rfl⟩ : syracuseStep 2808377 = 2106283) B2106283
theorem B9476675 : Blo 1871637 9476675 := bstep (se 1 (by rfl) ⟨7107506, by rfl⟩ : syracuseStep 9476675 = 14215013) B14215013
theorem B3373687 : Blo 1871637 3373687 := bstep (se 1 (by rfl) ⟨2530265, by rfl⟩ : syracuseStep 3373687 = 5060531) B5060531
theorem B2808455 : Blo 1871637 2808455 := bstep (se 1 (by rfl) ⟨2106341, by rfl⟩ : syracuseStep 2808455 = 4212683) B4212683
theorem B2808491 : Blo 1871637 2808491 := bstep (se 1 (by rfl) ⟨2106368, by rfl⟩ : syracuseStep 2808491 = 4212737) B4212737
theorem B2808521 : Blo 1871637 2808521 := bstep (se 2 (by rfl) ⟨1053195, by rfl⟩ : syracuseStep 2808521 = 2106391) B2106391
theorem B2808635 : Blo 1871637 2808635 := bstep (se 1 (by rfl) ⟨2106476, by rfl⟩ : syracuseStep 2808635 = 4212953) B4212953
theorem B4742003 : Blo 1871637 4742003 := bstep (se 1 (by rfl) ⟨3556502, by rfl⟩ : syracuseStep 4742003 = 7113005) B7113005
theorem B2808695 : Blo 1871637 2808695 := bstep (se 1 (by rfl) ⟨2106521, by rfl⟩ : syracuseStep 2808695 = 4213043) B4213043
theorem B9476999 : Blo 1871637 9476999 := bstep (se 1 (by rfl) ⟨7107749, by rfl⟩ : syracuseStep 9476999 = 14215499) B14215499
theorem B4742023 : Blo 1871637 4742023 := bstep (se 1 (by rfl) ⟨3556517, by rfl⟩ : syracuseStep 4742023 = 7113035) B7113035
theorem B8002439 : Blo 1871637 8002439 := bstep (se 1 (by rfl) ⟨6001829, by rfl⟩ : syracuseStep 8002439 = 12003659) B12003659
theorem B2808719 : Blo 1871637 2808719 := bstep (se 1 (by rfl) ⟨2106539, by rfl⟩ : syracuseStep 2808719 = 4213079) B4213079
theorem B2808761 : Blo 1871637 2808761 := bstep (se 2 (by rfl) ⟨1053285, by rfl⟩ : syracuseStep 2808761 = 2106571) B2106571
theorem B6323129 : Blo 1871637 6323129 := bstep (se 2 (by rfl) ⟨2371173, by rfl⟩ : syracuseStep 6323129 = 4742347) B4742347
theorem B2808839 : Blo 1871637 2808839 := bstep (se 1 (by rfl) ⟨2106629, by rfl⟩ : syracuseStep 2808839 = 4213259) B4213259
theorem B5331997 : Blo 1871637 5331997 := bstep (se 3 (by rfl) ⟨999749, by rfl⟩ : syracuseStep 5331997 = 1999499) B1999499
theorem B5061665 : Blo 1871637 5061665 := bstep (se 2 (by rfl) ⟨1898124, by rfl⟩ : syracuseStep 5061665 = 3796249) B3796249
theorem B2808875 : Blo 1871637 2808875 := bstep (se 1 (by rfl) ⟨2106656, by rfl⟩ : syracuseStep 2808875 = 4213313) B4213313
theorem B2808905 : Blo 1871637 2808905 := bstep (se 2 (by rfl) ⟨1053339, by rfl⟩ : syracuseStep 2808905 = 2106679) B2106679
theorem B3161207 : Blo 1871637 3161207 := bstep (se 1 (by rfl) ⟨2370905, by rfl⟩ : syracuseStep 3161207 = 4741811) B4741811
theorem B4742297 : Blo 1871637 4742297 := bstep (se 2 (by rfl) ⟨1778361, by rfl⟩ : syracuseStep 4742297 = 3556723) B3556723
theorem B2809019 : Blo 1871637 2809019 := bstep (se 1 (by rfl) ⟨2106764, by rfl⟩ : syracuseStep 2809019 = 4213529) B4213529
theorem B5332169 : Blo 1871637 5332169 := bstep (se 2 (by rfl) ⟨1999563, by rfl⟩ : syracuseStep 5332169 = 3999127) B3999127
theorem B2809079 : Blo 1871637 2809079 := bstep (se 1 (by rfl) ⟨2106809, by rfl⟩ : syracuseStep 2809079 = 4213619) B4213619
theorem B5332225 : Blo 1871637 5332225 := bstep (se 2 (by rfl) ⟨1999584, by rfl⟩ : syracuseStep 5332225 = 3999169) B3999169
theorem B2809103 : Blo 1871637 2809103 := bstep (se 1 (by rfl) ⟨2106827, by rfl⟩ : syracuseStep 2809103 = 4213655) B4213655
theorem B2809145 : Blo 1871637 2809145 := bstep (se 2 (by rfl) ⟨1053429, by rfl⟩ : syracuseStep 2809145 = 2106859) B2106859
theorem B4742459 : Blo 1871637 4742459 := bstep (se 1 (by rfl) ⟨3556844, by rfl⟩ : syracuseStep 4742459 = 7113689) B7113689
theorem B8543603 : Blo 1871637 8543603 := bstep (se 1 (by rfl) ⟨6407702, by rfl⟩ : syracuseStep 8543603 = 12815405) B12815405
theorem B3554695 : Blo 1871637 3554695 := bstep (se 1 (by rfl) ⟨2666021, by rfl⟩ : syracuseStep 3554695 = 5332043) B5332043
theorem B2809223 : Blo 1871637 2809223 := bstep (se 1 (by rfl) ⟨2106917, by rfl⟩ : syracuseStep 2809223 = 4213835) B4213835
theorem B2809259 : Blo 1871637 2809259 := bstep (se 1 (by rfl) ⟨2106944, by rfl⟩ : syracuseStep 2809259 = 4213889) B4213889
theorem B2809289 : Blo 1871637 2809289 := bstep (se 2 (by rfl) ⟨1053483, by rfl⟩ : syracuseStep 2809289 = 2106967) B2106967
theorem B40492547 : Blo 1871637 40492547 := bstep (se 1 (by rfl) ⟨30369410, by rfl⟩ : syracuseStep 40492547 = 60738821) B60738821
theorem B8994347 : Blo 1871637 8994347 := bstep (se 1 (by rfl) ⟨6745760, by rfl⟩ : syracuseStep 8994347 = 13491521) B13491521
theorem B2809403 : Blo 1871637 2809403 := bstep (se 1 (by rfl) ⟨2107052, by rfl⟩ : syracuseStep 2809403 = 4214105) B4214105
theorem B3161659 : Blo 1871637 3161659 := bstep (se 1 (by rfl) ⟨2371244, by rfl⟩ : syracuseStep 3161659 = 4742489) B4742489
theorem B5332567 : Blo 1871637 5332567 := bstep (se 1 (by rfl) ⟨3999425, by rfl⟩ : syracuseStep 5332567 = 7998851) B7998851
theorem B2809463 : Blo 1871637 2809463 := bstep (se 1 (by rfl) ⟨2107097, by rfl⟩ : syracuseStep 2809463 = 4214195) B4214195
theorem B2809487 : Blo 1871637 2809487 := bstep (se 1 (by rfl) ⟨2107115, by rfl⟩ : syracuseStep 2809487 = 4214231) B4214231
theorem B17997491 : Blo 1871637 17997491 := bstep (se 1 (by rfl) ⟨13498118, by rfl⟩ : syracuseStep 17997491 = 26996237) B26996237
theorem B2809529 : Blo 1871637 2809529 := bstep (se 2 (by rfl) ⟨1053573, by rfl⟩ : syracuseStep 2809529 = 2107147) B2107147
theorem B2531017 : Blo 1871637 2531017 := bstep (se 2 (by rfl) ⟨949131, by rfl⟩ : syracuseStep 2531017 = 1898263) B1898263
theorem B2809607 : Blo 1871637 2809607 := bstep (se 1 (by rfl) ⟨2107205, by rfl⟩ : syracuseStep 2809607 = 4214411) B4214411
theorem B2809643 : Blo 1871637 2809643 := bstep (se 1 (by rfl) ⟨2107232, by rfl⟩ : syracuseStep 2809643 = 4214465) B4214465
theorem B40509233 : Blo 1871637 40509233 := bstep (se 2 (by rfl) ⟨15190962, by rfl⟩ : syracuseStep 40509233 = 30381925) B30381925
theorem B2809673 : Blo 1871637 2809673 := bstep (se 2 (by rfl) ⟨1053627, by rfl⟩ : syracuseStep 2809673 = 2107255) B2107255
theorem B17997643 : Blo 1871637 17997643 := bstep (se 1 (by rfl) ⟨13498232, by rfl⟩ : syracuseStep 17997643 = 26996465) B26996465
theorem B10665863 : Blo 1871637 10665863 := bstep (se 1 (by rfl) ⟨7999397, by rfl⟩ : syracuseStep 10665863 = 15998795) B15998795
theorem B2809787 : Blo 1871637 2809787 := bstep (se 1 (by rfl) ⟨2107340, by rfl⟩ : syracuseStep 2809787 = 4214681) B4214681
theorem B2809847 : Blo 1871637 2809847 := bstep (se 1 (by rfl) ⟨2107385, by rfl⟩ : syracuseStep 2809847 = 4214771) B4214771
theorem B6750215 : Blo 1871637 6750215 := bstep (se 1 (by rfl) ⟨5062661, by rfl⟩ : syracuseStep 6750215 = 10125323) B10125323
theorem B2809865 : Blo 1871637 2809865 := bstep (se 2 (by rfl) ⟨1053699, by rfl⟩ : syracuseStep 2809865 = 2107399) B2107399
theorem B21331997 : Blo 1871637 21331997 := bstep (se 3 (by rfl) ⟨3999749, by rfl⟩ : syracuseStep 21331997 = 7999499) B7999499
theorem B2809895 : Blo 1871637 2809895 := bstep (se 1 (by rfl) ⟨2107421, by rfl⟩ : syracuseStep 2809895 = 4214843) B4214843
theorem B2809979 : Blo 1871637 2809979 := bstep (se 1 (by rfl) ⟨2107484, by rfl⟩ : syracuseStep 2809979 = 4214969) B4214969
theorem B2810105 : Blo 1871637 2810105 := bstep (se 2 (by rfl) ⟨1053789, by rfl⟩ : syracuseStep 2810105 = 2107579) B2107579
theorem B2810207 : Blo 1871637 2810207 := bstep (se 1 (by rfl) ⟨2107655, by rfl⟩ : syracuseStep 2810207 = 4215311) B4215311
theorem B2810219 : Blo 1871637 2810219 := bstep (se 1 (by rfl) ⟨2107664, by rfl⟩ : syracuseStep 2810219 = 4215329) B4215329
theorem B2998711 : Blo 1871637 2998711 := bstep (se 1 (by rfl) ⟨2249033, by rfl⟩ : syracuseStep 2998711 = 4498067) B4498067
theorem B2810447 : Blo 1871637 2810447 := bstep (se 1 (by rfl) ⟨2107835, by rfl⟩ : syracuseStep 2810447 = 4215671) B4215671
theorem B4211297 : Blo 1871637 4211297 := bstep (se 2 (by rfl) ⟨1579236, by rfl⟩ : syracuseStep 4211297 = 3158473) B3158473
theorem B5333627 : Blo 1871637 5333627 := bstep (se 1 (by rfl) ⟨4000220, by rfl⟩ : syracuseStep 5333627 = 8000441) B8000441
theorem B4498249 : Blo 1871637 4498249 := bstep (se 2 (by rfl) ⟨1686843, by rfl⟩ : syracuseStep 4498249 = 3373687) B3373687
theorem B6497131 : Blo 1871637 6497131 := bstep (se 1 (by rfl) ⟨4872848, by rfl⟩ : syracuseStep 6497131 = 9745697) B9745697
theorem B6316919 : Blo 1871637 6316919 := bstep (se 1 (by rfl) ⟨4737689, by rfl⟩ : syracuseStep 6316919 = 9475379) B9475379
theorem B5997473 : Blo 1871637 5997473 := bstep (se 2 (by rfl) ⟨2249052, by rfl⟩ : syracuseStep 5997473 = 4498105) B4498105
theorem B4211639 : Blo 1871637 4211639 := bstep (se 1 (by rfl) ⟨3158729, by rfl⟩ : syracuseStep 4211639 = 6317459) B6317459
theorem B22782941 : Blo 1871637 22782941 := bstep (se 3 (by rfl) ⟨4271801, by rfl⟩ : syracuseStep 22782941 = 8543603) B8543603
theorem B15188957 : Blo 1871637 15188957 := bstep (se 3 (by rfl) ⟨2847929, by rfl⟩ : syracuseStep 15188957 = 5695859) B5695859
theorem B6317135 : Blo 1871637 6317135 := bstep (se 1 (by rfl) ⟨4737851, by rfl⟩ : syracuseStep 6317135 = 9475703) B9475703
theorem B7111759 : Blo 1871637 7111759 := bstep (se 1 (by rfl) ⟨5333819, by rfl⟩ : syracuseStep 7111759 = 10667639) B10667639
theorem B2999467 : Blo 1871637 2999467 := bstep (se 1 (by rfl) ⟨2249600, by rfl⟩ : syracuseStep 2999467 = 4499201) B4499201
theorem B7595255 : Blo 1871637 7595255 := bstep (se 1 (by rfl) ⟨5696441, by rfl⟩ : syracuseStep 7595255 = 11392883) B11392883
theorem B2999659 : Blo 1871637 2999659 := bstep (se 1 (by rfl) ⟨2249744, by rfl⟩ : syracuseStep 2999659 = 4499489) B4499489
theorem B6317513 : Blo 1871637 6317513 := bstep (se 2 (by rfl) ⟨2369067, by rfl⟩ : syracuseStep 6317513 = 4738135) B4738135
theorem B11994587 : Blo 1871637 11994587 := bstep (se 1 (by rfl) ⟨8995940, by rfl⟩ : syracuseStep 11994587 = 17991881) B17991881
theorem B4212233 : Blo 1871637 4212233 := bstep (se 2 (by rfl) ⟨1579587, by rfl⟩ : syracuseStep 4212233 = 3159175) B3159175
theorem B51267107 : Blo 1871637 51267107 := bstep (se 1 (by rfl) ⟨38450330, by rfl⟩ : syracuseStep 51267107 = 76900661) B76900661
theorem B7112231 : Blo 1871637 7112231 := bstep (se 1 (by rfl) ⟨5334173, by rfl⟩ : syracuseStep 7112231 = 10668347) B10668347
theorem B3556943 : Blo 1871637 3556943 := bstep (se 1 (by rfl) ⟨2667707, by rfl⟩ : syracuseStep 3556943 = 5335415) B5335415
theorem B2107003 : Blo 1871637 2107003 := bstep (se 1 (by rfl) ⟨1580252, by rfl⟩ : syracuseStep 2107003 = 3160505) B3160505
theorem B7997075 : Blo 1871637 7997075 := bstep (se 1 (by rfl) ⟨5997806, by rfl⟩ : syracuseStep 7997075 = 11995613) B11995613
theorem B6317783 : Blo 1871637 6317783 := bstep (se 1 (by rfl) ⟨4738337, by rfl⟩ : syracuseStep 6317783 = 9476675) B9476675
theorem B68306777 : Blo 1871637 68306777 := bstep (se 2 (by rfl) ⟨25615041, by rfl⟩ : syracuseStep 68306777 = 51230083) B51230083
theorem B4212575 : Blo 1871637 4212575 := bstep (se 1 (by rfl) ⟨3159431, by rfl⟩ : syracuseStep 4212575 = 6318863) B6318863
theorem B6317999 : Blo 1871637 6317999 := bstep (se 1 (by rfl) ⟨4738499, by rfl⟩ : syracuseStep 6317999 = 9476999) B9476999
theorem B5334959 : Blo 1871637 5334959 := bstep (se 1 (by rfl) ⟨4001219, by rfl⟩ : syracuseStep 5334959 = 8002439) B8002439
theorem B4212755 : Blo 1871637 4212755 := bstep (se 1 (by rfl) ⟨3159566, by rfl⟩ : syracuseStep 4212755 = 6319133) B6319133
theorem B3000377 : Blo 1871637 3000377 := bstep (se 2 (by rfl) ⟨1125141, by rfl⟩ : syracuseStep 3000377 = 2250283) B2250283
theorem B2107471 : Blo 1871637 2107471 := bstep (se 1 (by rfl) ⟨1580603, by rfl⟩ : syracuseStep 2107471 = 3161207) B3161207
theorem B20244581 : Blo 1871637 20244581 := bstep (se 4 (by rfl) ⟨1897929, by rfl⟩ : syracuseStep 20244581 = 3795859) B3795859
theorem B8997131 : Blo 1871637 8997131 := bstep (se 1 (by rfl) ⟨6747848, by rfl⟩ : syracuseStep 8997131 = 13495697) B13495697
theorem B26995031 : Blo 1871637 26995031 := bstep (se 1 (by rfl) ⟨20246273, by rfl⟩ : syracuseStep 26995031 = 40492547) B40492547
theorem B4213097 : Blo 1871637 4213097 := bstep (se 2 (by rfl) ⟨1579911, by rfl⟩ : syracuseStep 4213097 = 3159823) B3159823
theorem B8538497 : Blo 1871637 8538497 := bstep (se 2 (by rfl) ⟨3201936, by rfl⟩ : syracuseStep 8538497 = 6403873) B6403873
theorem B23996857 : Blo 1871637 23996857 := bstep (se 2 (by rfl) ⟨8998821, by rfl⟩ : syracuseStep 23996857 = 17997643) B17997643
theorem B7113203 : Blo 1871637 7113203 := bstep (se 1 (by rfl) ⟨5334902, by rfl⟩ : syracuseStep 7113203 = 10669805) B10669805
theorem B3000889 : Blo 1871637 3000889 := bstep (se 2 (by rfl) ⟨1125333, by rfl⟩ : syracuseStep 3000889 = 2250667) B2250667
theorem B12806867 : Blo 1871637 12806867 := bstep (se 1 (by rfl) ⟨9605150, by rfl⟩ : syracuseStep 12806867 = 19210301) B19210301
theorem B23989067 : Blo 1871637 23989067 := bstep (se 1 (by rfl) ⟨17991800, by rfl⟩ : syracuseStep 23989067 = 35983601) B35983601
theorem B4737953 : Blo 1871637 4737953 := bstep (se 2 (by rfl) ⟨1776732, by rfl⟩ : syracuseStep 4737953 = 3553465) B3553465
theorem B4000673 : Blo 1871637 4000673 := bstep (se 2 (by rfl) ⟨1500252, by rfl⟩ : syracuseStep 4000673 = 3000505) B3000505
theorem B9612215 : Blo 1871637 9612215 := bstep (se 1 (by rfl) ⟨7209161, by rfl⟩ : syracuseStep 9612215 = 14418323) B14418323
theorem B4213691 : Blo 1871637 4213691 := bstep (se 1 (by rfl) ⟨3160268, by rfl⟩ : syracuseStep 4213691 = 6320537) B6320537
theorem B4213817 : Blo 1871637 4213817 := bstep (se 2 (by rfl) ⟨1580181, by rfl⟩ : syracuseStep 4213817 = 3160363) B3160363
theorem B6081689 : Blo 1871637 6081689 := bstep (se 2 (by rfl) ⟨2280633, by rfl⟩ : syracuseStep 6081689 = 4561267) B4561267
theorem B24005879 : Blo 1871637 24005879 := bstep (se 1 (by rfl) ⟨18004409, by rfl⟩ : syracuseStep 24005879 = 36008819) B36008819
theorem B4001015 : Blo 1871637 4001015 := bstep (se 1 (by rfl) ⟨3000761, by rfl⟩ : syracuseStep 4001015 = 6001523) B6001523
theorem B14216471 : Blo 1871637 14216471 := bstep (se 1 (by rfl) ⟨10662353, by rfl⟩ : syracuseStep 14216471 = 21324707) B21324707
theorem B5999933 : Blo 1871637 5999933 := bstep (se 3 (by rfl) ⟨1124987, by rfl⟩ : syracuseStep 5999933 = 2249975) B2249975
theorem B4738409 : Blo 1871637 4738409 := bstep (se 2 (by rfl) ⟨1776903, by rfl⟩ : syracuseStep 4738409 = 3553807) B3553807
theorem B15183247 : Blo 1871637 15183247 := bstep (se 1 (by rfl) ⟨11387435, by rfl⟩ : syracuseStep 15183247 = 22774871) B22774871
theorem B4214159 : Blo 1871637 4214159 := bstep (se 1 (by rfl) ⟨3160619, by rfl⟩ : syracuseStep 4214159 = 6321239) B6321239
theorem B2846287 : Blo 1871637 2846287 := bstep (se 1 (by rfl) ⟨2134715, by rfl⟩ : syracuseStep 2846287 = 4269431) B4269431
theorem B17993339 : Blo 1871637 17993339 := bstep (se 1 (by rfl) ⟨13495004, by rfl⟩ : syracuseStep 17993339 = 26990009) B26990009
theorem B4214483 : Blo 1871637 4214483 := bstep (se 1 (by rfl) ⟨3160862, by rfl⟩ : syracuseStep 4214483 = 6321725) B6321725
theorem B1871655 : Blo 1871637 1871655 := bstep (se 1 (by rfl) ⟨1403741, by rfl⟩ : syracuseStep 1871655 = 2807483) B2807483
theorem B14225219 : Blo 1871637 14225219 := bstep (se 1 (by rfl) ⟨10668914, by rfl⟩ : syracuseStep 14225219 = 21337829) B21337829
theorem B1871695 : Blo 1871637 1871695 := bstep (se 1 (by rfl) ⟨1403771, by rfl⟩ : syracuseStep 1871695 = 2807543) B2807543
theorem B7106399 : Blo 1871637 7106399 := bstep (se 1 (by rfl) ⟨5329799, by rfl⟩ : syracuseStep 7106399 = 10659599) B10659599
theorem B1871711 : Blo 1871637 1871711 := bstep (se 1 (by rfl) ⟨1403783, by rfl⟩ : syracuseStep 1871711 = 2807567) B2807567
theorem B13496159 : Blo 1871637 13496159 := bstep (se 1 (by rfl) ⟨10122119, by rfl⟩ : syracuseStep 13496159 = 20244239) B20244239
theorem B7106413 : Blo 1871637 7106413 := bstep (se 3 (by rfl) ⟨1332452, by rfl⟩ : syracuseStep 7106413 = 2664905) B2664905
theorem B1871739 : Blo 1871637 1871739 := bstep (se 1 (by rfl) ⟨1403804, by rfl⟩ : syracuseStep 1871739 = 2807609) B2807609
theorem B228061079 : Blo 1871637 228061079 := bstep (se 1 (by rfl) ⟨171045809, by rfl⟩ : syracuseStep 228061079 = 342091619) B342091619
theorem B1871791 : Blo 1871637 1871791 := bstep (se 1 (by rfl) ⟨1403843, by rfl⟩ : syracuseStep 1871791 = 2807687) B2807687
theorem B1871815 : Blo 1871637 1871815 := bstep (se 1 (by rfl) ⟨1403861, by rfl⟩ : syracuseStep 1871815 = 2807723) B2807723
theorem B1871835 : Blo 1871637 1871835 := bstep (se 1 (by rfl) ⟨1403876, by rfl⟩ : syracuseStep 1871835 = 2807753) B2807753
theorem B1871911 : Blo 1871637 1871911 := bstep (se 1 (by rfl) ⟨1403933, by rfl⟩ : syracuseStep 1871911 = 2807867) B2807867
theorem B1871951 : Blo 1871637 1871951 := bstep (se 1 (by rfl) ⟨1403963, by rfl⟩ : syracuseStep 1871951 = 2807927) B2807927
theorem B1871967 : Blo 1871637 1871967 := bstep (se 1 (by rfl) ⟨1403975, by rfl⟩ : syracuseStep 1871967 = 2807951) B2807951
theorem B6082675 : Blo 1871637 6082675 := bstep (se 1 (by rfl) ⟨4562006, by rfl⟩ : syracuseStep 6082675 = 9124013) B9124013
theorem B1871995 : Blo 1871637 1871995 := bstep (se 1 (by rfl) ⟨1403996, by rfl⟩ : syracuseStep 1871995 = 2807993) B2807993
theorem B7106717 : Blo 1871637 7106717 := bstep (se 3 (by rfl) ⟨1332509, by rfl⟩ : syracuseStep 7106717 = 2665019) B2665019
theorem B10670237 : Blo 1871637 10670237 := bstep (se 3 (by rfl) ⟨2000669, by rfl⟩ : syracuseStep 10670237 = 4001339) B4001339
theorem B1872047 : Blo 1871637 1872047 := bstep (se 1 (by rfl) ⟨1404035, by rfl⟩ : syracuseStep 1872047 = 2808071) B2808071
theorem B1872071 : Blo 1871637 1872071 := bstep (se 1 (by rfl) ⟨1404053, by rfl⟩ : syracuseStep 1872071 = 2808107) B2808107
theorem B1872091 : Blo 1871637 1872091 := bstep (se 1 (by rfl) ⟨1404068, by rfl⟩ : syracuseStep 1872091 = 2808137) B2808137
theorem B6320375 : Blo 1871637 6320375 := bstep (se 1 (by rfl) ⟨4740281, by rfl⟩ : syracuseStep 6320375 = 9480563) B9480563
theorem B9482507 : Blo 1871637 9482507 := bstep (se 1 (by rfl) ⟨7111880, by rfl⟩ : syracuseStep 9482507 = 14223761) B14223761
theorem B1872167 : Blo 1871637 1872167 := bstep (se 1 (by rfl) ⟨1404125, by rfl⟩ : syracuseStep 1872167 = 2808251) B2808251
theorem B1872207 : Blo 1871637 1872207 := bstep (se 1 (by rfl) ⟨1404155, by rfl⟩ : syracuseStep 1872207 = 2808311) B2808311
theorem B1872223 : Blo 1871637 1872223 := bstep (se 1 (by rfl) ⟨1404167, by rfl⟩ : syracuseStep 1872223 = 2808335) B2808335
theorem B1872251 : Blo 1871637 1872251 := bstep (se 1 (by rfl) ⟨1404188, by rfl⟩ : syracuseStep 1872251 = 2808377) B2808377
theorem B1872303 : Blo 1871637 1872303 := bstep (se 1 (by rfl) ⟨1404227, by rfl⟩ : syracuseStep 1872303 = 2808455) B2808455
theorem B1872327 : Blo 1871637 1872327 := bstep (se 1 (by rfl) ⟨1404245, by rfl⟩ : syracuseStep 1872327 = 2808491) B2808491
theorem B1872347 : Blo 1871637 1872347 := bstep (se 1 (by rfl) ⟨1404260, by rfl⟩ : syracuseStep 1872347 = 2808521) B2808521
theorem B6746611 : Blo 1871637 6746611 := bstep (se 1 (by rfl) ⟨5059958, by rfl⟩ : syracuseStep 6746611 = 10119917) B10119917
theorem B4739593 : Blo 1871637 4739593 := bstep (se 2 (by rfl) ⟨1777347, by rfl⟩ : syracuseStep 4739593 = 3554695) B3554695
theorem B1872423 : Blo 1871637 1872423 := bstep (se 1 (by rfl) ⟨1404317, by rfl⟩ : syracuseStep 1872423 = 2808635) B2808635
theorem B6320699 : Blo 1871637 6320699 := bstep (se 1 (by rfl) ⟨4740524, by rfl⟩ : syracuseStep 6320699 = 9481049) B9481049
theorem B1872463 : Blo 1871637 1872463 := bstep (se 1 (by rfl) ⟨1404347, by rfl⟩ : syracuseStep 1872463 = 2808695) B2808695
theorem B1872479 : Blo 1871637 1872479 := bstep (se 1 (by rfl) ⟨1404359, by rfl⟩ : syracuseStep 1872479 = 2808719) B2808719
theorem B24654437 : Blo 1871637 24654437 := bstep (se 4 (by rfl) ⟨2311353, by rfl⟩ : syracuseStep 24654437 = 4622707) B4622707
theorem B1872507 : Blo 1871637 1872507 := bstep (se 1 (by rfl) ⟨1404380, by rfl⟩ : syracuseStep 1872507 = 2808761) B2808761
theorem B4215419 : Blo 1871637 4215419 := bstep (se 1 (by rfl) ⟨3161564, by rfl⟩ : syracuseStep 4215419 = 6323129) B6323129
theorem B1872559 : Blo 1871637 1872559 := bstep (se 1 (by rfl) ⟨1404419, by rfl⟩ : syracuseStep 1872559 = 2808839) B2808839
theorem B1872583 : Blo 1871637 1872583 := bstep (se 1 (by rfl) ⟨1404437, by rfl⟩ : syracuseStep 1872583 = 2808875) B2808875
theorem B14217929 : Blo 1871637 14217929 := bstep (se 2 (by rfl) ⟨5331723, by rfl⟩ : syracuseStep 14217929 = 10663447) B10663447
theorem B1872603 : Blo 1871637 1872603 := bstep (se 1 (by rfl) ⟨1404452, by rfl⟩ : syracuseStep 1872603 = 2808905) B2808905
theorem B3158777 : Blo 1871637 3158777 := bstep (se 2 (by rfl) ⟨1184541, by rfl⟩ : syracuseStep 3158777 = 2369083) B2369083
theorem B4215545 : Blo 1871637 4215545 := bstep (se 2 (by rfl) ⟨1580829, by rfl⟩ : syracuseStep 4215545 = 3161659) B3161659
theorem B1872679 : Blo 1871637 1872679 := bstep (se 1 (by rfl) ⟨1404509, by rfl⟩ : syracuseStep 1872679 = 2809019) B2809019
theorem B7107371 : Blo 1871637 7107371 := bstep (se 1 (by rfl) ⟨5330528, by rfl⟩ : syracuseStep 7107371 = 10661057) B10661057
theorem B6320969 : Blo 1871637 6320969 := bstep (se 2 (by rfl) ⟨2370363, by rfl⟩ : syracuseStep 6320969 = 4740727) B4740727
theorem B1872719 : Blo 1871637 1872719 := bstep (se 1 (by rfl) ⟨1404539, by rfl⟩ : syracuseStep 1872719 = 2809079) B2809079
theorem B1872735 : Blo 1871637 1872735 := bstep (se 1 (by rfl) ⟨1404551, by rfl⟩ : syracuseStep 1872735 = 2809103) B2809103
theorem B1872763 : Blo 1871637 1872763 := bstep (se 1 (by rfl) ⟨1404572, by rfl⟩ : syracuseStep 1872763 = 2809145) B2809145
theorem B3158959 : Blo 1871637 3158959 := bstep (se 1 (by rfl) ⟨2369219, by rfl⟩ : syracuseStep 3158959 = 4738439) B4738439
theorem B1872815 : Blo 1871637 1872815 := bstep (se 1 (by rfl) ⟨1404611, by rfl⟩ : syracuseStep 1872815 = 2809223) B2809223
theorem B28832687 : Blo 1871637 28832687 := bstep (se 1 (by rfl) ⟨21624515, by rfl⟩ : syracuseStep 28832687 = 43249031) B43249031
theorem B1872839 : Blo 1871637 1872839 := bstep (se 1 (by rfl) ⟨1404629, by rfl⟩ : syracuseStep 1872839 = 2809259) B2809259
theorem B1872859 : Blo 1871637 1872859 := bstep (se 1 (by rfl) ⟨1404644, by rfl⟩ : syracuseStep 1872859 = 2809289) B2809289
theorem B3159047 : Blo 1871637 3159047 := bstep (se 1 (by rfl) ⟨2369285, by rfl⟩ : syracuseStep 3159047 = 4738571) B4738571
theorem B1872935 : Blo 1871637 1872935 := bstep (se 1 (by rfl) ⟨1404701, by rfl⟩ : syracuseStep 1872935 = 2809403) B2809403
theorem B1872975 : Blo 1871637 1872975 := bstep (se 1 (by rfl) ⟨1404731, by rfl⟩ : syracuseStep 1872975 = 2809463) B2809463
theorem B1872991 : Blo 1871637 1872991 := bstep (se 1 (by rfl) ⟨1404743, by rfl⟩ : syracuseStep 1872991 = 2809487) B2809487
theorem B11998327 : Blo 1871637 11998327 := bstep (se 1 (by rfl) ⟨8998745, by rfl⟩ : syracuseStep 11998327 = 17997491) B17997491
theorem B1873019 : Blo 1871637 1873019 := bstep (se 1 (by rfl) ⟨1404764, by rfl⟩ : syracuseStep 1873019 = 2809529) B2809529
theorem B1873071 : Blo 1871637 1873071 := bstep (se 1 (by rfl) ⟨1404803, by rfl⟩ : syracuseStep 1873071 = 2809607) B2809607
theorem B1873095 : Blo 1871637 1873095 := bstep (se 1 (by rfl) ⟨1404821, by rfl⟩ : syracuseStep 1873095 = 2809643) B2809643
theorem B27006155 : Blo 1871637 27006155 := bstep (se 1 (by rfl) ⟨20254616, by rfl⟩ : syracuseStep 27006155 = 40509233) B40509233
theorem B1873115 : Blo 1871637 1873115 := bstep (se 1 (by rfl) ⟨1404836, by rfl⟩ : syracuseStep 1873115 = 2809673) B2809673
theorem B1873191 : Blo 1871637 1873191 := bstep (se 1 (by rfl) ⟨1404893, by rfl⟩ : syracuseStep 1873191 = 2809787) B2809787
theorem B1873231 : Blo 1871637 1873231 := bstep (se 1 (by rfl) ⟨1404923, by rfl⟩ : syracuseStep 1873231 = 2809847) B2809847
theorem B3159391 : Blo 1871637 3159391 := bstep (se 1 (by rfl) ⟨2369543, by rfl⟩ : syracuseStep 3159391 = 4739087) B4739087
theorem B1873247 : Blo 1871637 1873247 := bstep (se 1 (by rfl) ⟨1404935, by rfl⟩ : syracuseStep 1873247 = 2809871) B2809871
theorem B1873275 : Blo 1871637 1873275 := bstep (se 1 (by rfl) ⟨1404956, by rfl⟩ : syracuseStep 1873275 = 2809913) B2809913
theorem B1873327 : Blo 1871637 1873327 := bstep (se 1 (by rfl) ⟨1404995, by rfl⟩ : syracuseStep 1873327 = 2809991) B2809991
theorem B3159479 : Blo 1871637 3159479 := bstep (se 1 (by rfl) ⟨2369609, by rfl⟩ : syracuseStep 3159479 = 4739219) B4739219
theorem B1873351 : Blo 1871637 1873351 := bstep (se 1 (by rfl) ⟨1405013, by rfl⟩ : syracuseStep 1873351 = 2810027) B2810027
theorem B1873371 : Blo 1871637 1873371 := bstep (se 1 (by rfl) ⟨1405028, by rfl⟩ : syracuseStep 1873371 = 2810057) B2810057
theorem B1873447 : Blo 1871637 1873447 := bstep (se 1 (by rfl) ⟨1405085, by rfl⟩ : syracuseStep 1873447 = 2810171) B2810171
theorem B1873487 : Blo 1871637 1873487 := bstep (se 1 (by rfl) ⟨1405115, by rfl⟩ : syracuseStep 1873487 = 2810231) B2810231
theorem B1873503 : Blo 1871637 1873503 := bstep (se 1 (by rfl) ⟨1405127, by rfl⟩ : syracuseStep 1873503 = 2810255) B2810255
theorem B1873531 : Blo 1871637 1873531 := bstep (se 1 (by rfl) ⟨1405148, by rfl⟩ : syracuseStep 1873531 = 2810297) B2810297
theorem B24008339 : Blo 1871637 24008339 := bstep (se 1 (by rfl) ⟨18006254, by rfl⟩ : syracuseStep 24008339 = 36012509) B36012509
theorem B1873583 : Blo 1871637 1873583 := bstep (se 1 (by rfl) ⟨1405187, by rfl⟩ : syracuseStep 1873583 = 2810375) B2810375
theorem B9483965 : Blo 1871637 9483965 := bstep (se 3 (by rfl) ⟨1778243, by rfl⟩ : syracuseStep 9483965 = 3556487) B3556487
theorem B2807495 : Blo 1871637 2807495 := bstep (se 1 (by rfl) ⟨2105621, by rfl⟩ : syracuseStep 2807495 = 4211243) B4211243
theorem B1873607 : Blo 1871637 1873607 := bstep (se 1 (by rfl) ⟨1405205, by rfl⟩ : syracuseStep 1873607 = 2810411) B2810411
theorem B1873627 : Blo 1871637 1873627 := bstep (se 1 (by rfl) ⟨1405220, by rfl⟩ : syracuseStep 1873627 = 2810441) B2810441
theorem B9484127 : Blo 1871637 9484127 := bstep (se 1 (by rfl) ⟨7113095, by rfl⟩ : syracuseStep 9484127 = 14226191) B14226191
theorem B2807657 : Blo 1871637 2807657 := bstep (se 2 (by rfl) ⟨1052871, by rfl⟩ : syracuseStep 2807657 = 2105743) B2105743
theorem B2807735 : Blo 1871637 2807735 := bstep (se 1 (by rfl) ⟨2105801, by rfl⟩ : syracuseStep 2807735 = 4211603) B4211603
theorem B6322103 : Blo 1871637 6322103 := bstep (se 1 (by rfl) ⟨4741577, by rfl⟩ : syracuseStep 6322103 = 9483155) B9483155
theorem B9476027 : Blo 1871637 9476027 := bstep (se 1 (by rfl) ⟨7107020, by rfl⟩ : syracuseStep 9476027 = 14214041) B14214041
theorem B4741051 : Blo 1871637 4741051 := bstep (se 1 (by rfl) ⟨3555788, by rfl⟩ : syracuseStep 4741051 = 7111577) B7111577
theorem B2807771 : Blo 1871637 2807771 := bstep (se 1 (by rfl) ⟨2105828, by rfl⟩ : syracuseStep 2807771 = 4211657) B4211657
theorem B3160073 : Blo 1871637 3160073 := bstep (se 2 (by rfl) ⟨1185027, by rfl⟩ : syracuseStep 3160073 = 2370055) B2370055
theorem B10663973 : Blo 1871637 10663973 := bstep (se 4 (by rfl) ⟨999747, by rfl⟩ : syracuseStep 10663973 = 1999495) B1999495
theorem B15997085 : Blo 1871637 15997085 := bstep (se 3 (by rfl) ⟨2999453, by rfl⟩ : syracuseStep 15997085 = 5998907) B5998907
theorem B3602603 : Blo 1871637 3602603 := bstep (se 1 (by rfl) ⟨2701952, by rfl⟩ : syracuseStep 3602603 = 5403905) B5403905
theorem B3160235 : Blo 1871637 3160235 := bstep (se 1 (by rfl) ⟨2370176, by rfl⟩ : syracuseStep 3160235 = 4740353) B4740353
theorem B13498757 : Blo 1871637 13498757 := bstep (se 4 (by rfl) ⟨1265508, by rfl⟩ : syracuseStep 13498757 = 2531017) B2531017
theorem B35977607 : Blo 1871637 35977607 := bstep (se 1 (by rfl) ⟨26983205, by rfl⟩ : syracuseStep 35977607 = 53966411) B53966411
theorem B2808239 : Blo 1871637 2808239 := bstep (se 1 (by rfl) ⟨2106179, by rfl⟩ : syracuseStep 2808239 = 4212359) B4212359
theorem B3553723 : Blo 1871637 3553723 := bstep (se 1 (by rfl) ⟨2665292, by rfl⟩ : syracuseStep 3553723 = 5330585) B5330585
theorem B2808329 : Blo 1871637 2808329 := bstep (se 2 (by rfl) ⟨1053123, by rfl⟩ : syracuseStep 2808329 = 2106247) B2106247
theorem B6322697 : Blo 1871637 6322697 := bstep (se 2 (by rfl) ⟨2371011, by rfl⟩ : syracuseStep 6322697 = 4742023) B4742023
theorem B3373607 : Blo 1871637 3373607 := bstep (se 1 (by rfl) ⟨2530205, by rfl⟩ : syracuseStep 3373607 = 5060411) B5060411
theorem B2808359 : Blo 1871637 2808359 := bstep (se 1 (by rfl) ⟨2106269, by rfl⟩ : syracuseStep 2808359 = 4212539) B4212539
theorem B3160633 : Blo 1871637 3160633 := bstep (se 2 (by rfl) ⟨1185237, by rfl⟩ : syracuseStep 3160633 = 2370475) B2370475
theorem B2808443 : Blo 1871637 2808443 := bstep (se 1 (by rfl) ⟨2106332, by rfl⟩ : syracuseStep 2808443 = 4212665) B4212665
theorem B3160775 : Blo 1871637 3160775 := bstep (se 1 (by rfl) ⟨2370581, by rfl⟩ : syracuseStep 3160775 = 4741163) B4741163
theorem B16005833 : Blo 1871637 16005833 := bstep (se 2 (by rfl) ⟨6002187, by rfl⟩ : syracuseStep 16005833 = 12004375) B12004375
theorem B7109329 : Blo 1871637 7109329 := bstep (se 2 (by rfl) ⟨2665998, by rfl⟩ : syracuseStep 7109329 = 5331997) B5331997
theorem B3848915 : Blo 1871637 3848915 := bstep (se 1 (by rfl) ⟨2886686, by rfl⟩ : syracuseStep 3848915 = 5773373) B5773373
theorem B2808569 : Blo 1871637 2808569 := bstep (se 2 (by rfl) ⟨1053213, by rfl⟩ : syracuseStep 2808569 = 2106427) B2106427
theorem B2808671 : Blo 1871637 2808671 := bstep (se 1 (by rfl) ⟨2106503, by rfl⟩ : syracuseStep 2808671 = 4213007) B4213007
theorem B3160937 : Blo 1871637 3160937 := bstep (se 2 (by rfl) ⟨1185351, by rfl⟩ : syracuseStep 3160937 = 2370703) B2370703
theorem B2808683 : Blo 1871637 2808683 := bstep (se 1 (by rfl) ⟨2106512, by rfl⟩ : syracuseStep 2808683 = 4213025) B4213025
theorem B3554209 : Blo 1871637 3554209 := bstep (se 2 (by rfl) ⟨1332828, by rfl⟩ : syracuseStep 3554209 = 2665657) B2665657
theorem B7109633 : Blo 1871637 7109633 := bstep (se 2 (by rfl) ⟨2666112, by rfl⟩ : syracuseStep 7109633 = 5332225) B5332225
theorem B12000275 : Blo 1871637 12000275 := bstep (se 1 (by rfl) ⟨9000206, by rfl⟩ : syracuseStep 12000275 = 18000413) B18000413
theorem B2808911 : Blo 1871637 2808911 := bstep (se 1 (by rfl) ⟨2106683, by rfl⟩ : syracuseStep 2808911 = 4213367) B4213367
theorem B15998147 : Blo 1871637 15998147 := bstep (se 1 (by rfl) ⟨11998610, by rfl⟩ : syracuseStep 15998147 = 23997221) B23997221
theorem B2809031 : Blo 1871637 2809031 := bstep (se 1 (by rfl) ⟨2106773, by rfl⟩ : syracuseStep 2809031 = 4213547) B4213547
theorem B9477323 : Blo 1871637 9477323 := bstep (se 1 (by rfl) ⟨7107992, by rfl⟩ : syracuseStep 9477323 = 14215985) B14215985
theorem B3161335 : Blo 1871637 3161335 := bstep (se 1 (by rfl) ⟨2371001, by rfl⟩ : syracuseStep 3161335 = 4742003) B4742003
theorem B2809193 : Blo 1871637 2809193 := bstep (se 2 (by rfl) ⟨1053447, by rfl⟩ : syracuseStep 2809193 = 2106895) B2106895
theorem B3374443 : Blo 1871637 3374443 := bstep (se 1 (by rfl) ⟨2530832, by rfl⟩ : syracuseStep 3374443 = 5061665) B5061665
theorem B2809271 : Blo 1871637 2809271 := bstep (se 1 (by rfl) ⟨2106953, by rfl⟩ : syracuseStep 2809271 = 4213907) B4213907
theorem B3161531 : Blo 1871637 3161531 := bstep (se 1 (by rfl) ⟨2371148, by rfl⟩ : syracuseStep 3161531 = 4742297) B4742297
theorem B7110089 : Blo 1871637 7110089 := bstep (se 2 (by rfl) ⟨2666283, by rfl⟩ : syracuseStep 7110089 = 5332567) B5332567
theorem B3554779 : Blo 1871637 3554779 := bstep (se 1 (by rfl) ⟨2666084, by rfl⟩ : syracuseStep 3554779 = 5332169) B5332169
theorem B2809307 : Blo 1871637 2809307 := bstep (se 1 (by rfl) ⟨2106980, by rfl⟩ : syracuseStep 2809307 = 4213961) B4213961
theorem B2530855 : Blo 1871637 2530855 := bstep (se 1 (by rfl) ⟨1898141, by rfl⟩ : syracuseStep 2530855 = 3796283) B3796283
theorem B3161639 : Blo 1871637 3161639 := bstep (se 1 (by rfl) ⟨2371229, by rfl⟩ : syracuseStep 3161639 = 4742459) B4742459
theorem B5996231 : Blo 1871637 5996231 := bstep (se 1 (by rfl) ⟨4497173, by rfl⟩ : syracuseStep 5996231 = 8994347) B8994347
theorem B22781729 : Blo 1871637 22781729 := bstep (se 2 (by rfl) ⟨8543148, by rfl⟩ : syracuseStep 22781729 = 17086297) B17086297
theorem B26992547 : Blo 1871637 26992547 := bstep (se 1 (by rfl) ⟨20244410, by rfl⟩ : syracuseStep 26992547 = 40488821) B40488821
theorem B7110575 : Blo 1871637 7110575 := bstep (se 1 (by rfl) ⟨5332931, by rfl⟩ : syracuseStep 7110575 = 10665863) B10665863
theorem B2809775 : Blo 1871637 2809775 := bstep (se 1 (by rfl) ⟨2107331, by rfl⟩ : syracuseStep 2809775 = 4214663) B4214663
theorem B14221331 : Blo 1871637 14221331 := bstep (se 1 (by rfl) ⟨10665998, by rfl⟩ : syracuseStep 14221331 = 21331997) B21331997
theorem B2809961 : Blo 1871637 2809961 := bstep (se 2 (by rfl) ⟨1053735, by rfl⟩ : syracuseStep 2809961 = 2107471) B2107471
theorem B3555751 : Blo 1871637 3555751 := bstep (se 1 (by rfl) ⟨2666813, by rfl⟩ : syracuseStep 3555751 = 5333627) B5333627
theorem B2810279 : Blo 1871637 2810279 := bstep (se 1 (by rfl) ⟨2107709, by rfl⟩ : syracuseStep 2810279 = 4215419) B4215419
theorem B9478619 : Blo 1871637 9478619 := bstep (se 1 (by rfl) ⟨7108964, by rfl⟩ : syracuseStep 9478619 = 14217929) B14217929
theorem B2105851 : Blo 1871637 2105851 := bstep (se 1 (by rfl) ⟨1579388, by rfl⟩ : syracuseStep 2105851 = 3158777) B3158777
theorem B2810363 : Blo 1871637 2810363 := bstep (se 1 (by rfl) ⟨2107772, by rfl⟩ : syracuseStep 2810363 = 4215545) B4215545
theorem B3998281 : Blo 1871637 3998281 := bstep (se 2 (by rfl) ⟨1499355, by rfl⟩ : syracuseStep 3998281 = 2998711) B2998711
theorem B4211279 : Blo 1871637 4211279 := bstep (se 1 (by rfl) ⟨3158459, by rfl⟩ : syracuseStep 4211279 = 6316919) B6316919
theorem B32440933 : Blo 1871637 32440933 := bstep (se 4 (by rfl) ⟨3041337, by rfl⟩ : syracuseStep 32440933 = 6082675) B6082675
theorem B3998315 : Blo 1871637 3998315 := bstep (se 1 (by rfl) ⟨2998736, by rfl⟩ : syracuseStep 3998315 = 5997473) B5997473
theorem B15188627 : Blo 1871637 15188627 := bstep (se 1 (by rfl) ⟨11391470, by rfl⟩ : syracuseStep 15188627 = 22782941) B22782941
theorem B10125971 : Blo 1871637 10125971 := bstep (se 1 (by rfl) ⟨7594478, by rfl⟩ : syracuseStep 10125971 = 15188957) B15188957
theorem B8995481 : Blo 1871637 8995481 := bstep (se 2 (by rfl) ⟨3373305, by rfl⟩ : syracuseStep 8995481 = 6746611) B6746611
theorem B2106031 : Blo 1871637 2106031 := bstep (se 1 (by rfl) ⟨1579523, by rfl⟩ : syracuseStep 2106031 = 3159047) B3159047
theorem B4211423 : Blo 1871637 4211423 := bstep (se 1 (by rfl) ⟨3158567, by rfl⟩ : syracuseStep 4211423 = 6317135) B6317135
theorem B9479105 : Blo 1871637 9479105 := bstep (se 2 (by rfl) ⟨3554664, by rfl⟩ : syracuseStep 9479105 = 7109329) B7109329
theorem B2106319 : Blo 1871637 2106319 := bstep (se 1 (by rfl) ⟨1579739, by rfl⟩ : syracuseStep 2106319 = 3159479) B3159479
theorem B4211675 : Blo 1871637 4211675 := bstep (se 1 (by rfl) ⟨3158756, by rfl⟩ : syracuseStep 4211675 = 6317513) B6317513
theorem B7996391 : Blo 1871637 7996391 := bstep (se 1 (by rfl) ⟨5997293, by rfl⟩ : syracuseStep 7996391 = 11994587) B11994587
theorem B34178071 : Blo 1871637 34178071 := bstep (se 1 (by rfl) ⟨25633553, by rfl⟩ : syracuseStep 34178071 = 51267107) B51267107
theorem B5997665 : Blo 1871637 5997665 := bstep (se 2 (by rfl) ⟨2249124, by rfl⟩ : syracuseStep 5997665 = 4498249) B4498249
theorem B4211855 : Blo 1871637 4211855 := bstep (se 1 (by rfl) ⟨3158891, by rfl⟩ : syracuseStep 4211855 = 6317783) B6317783
theorem B4211945 : Blo 1871637 4211945 := bstep (se 2 (by rfl) ⟨1579479, by rfl⟩ : syracuseStep 4211945 = 3158959) B3158959
theorem B4211999 : Blo 1871637 4211999 := bstep (se 1 (by rfl) ⟨3158999, by rfl⟩ : syracuseStep 4211999 = 6317999) B6317999
theorem B3556639 : Blo 1871637 3556639 := bstep (se 1 (by rfl) ⟨2667479, by rfl⟩ : syracuseStep 3556639 = 5334959) B5334959
theorem B6317351 : Blo 1871637 6317351 := bstep (se 1 (by rfl) ⟨4738013, by rfl⟩ : syracuseStep 6317351 = 9476027) B9476027
theorem B2106715 : Blo 1871637 2106715 := bstep (se 1 (by rfl) ⟨1580036, by rfl⟩ : syracuseStep 2106715 = 3160073) B3160073
theorem B2000251 : Blo 1871637 2000251 := bstep (se 1 (by rfl) ⟨1500188, by rfl⟩ : syracuseStep 2000251 = 3000377) B3000377
theorem B8996285 : Blo 1871637 8996285 := bstep (se 3 (by rfl) ⟨1686803, by rfl⟩ : syracuseStep 8996285 = 3373607) B3373607
theorem B2401735 : Blo 1871637 2401735 := bstep (se 1 (by rfl) ⟨1801301, by rfl⟩ : syracuseStep 2401735 = 3602603) B3602603
theorem B2106823 : Blo 1871637 2106823 := bstep (se 1 (by rfl) ⟨1580117, by rfl⟩ : syracuseStep 2106823 = 3160235) B3160235
theorem B5998087 : Blo 1871637 5998087 := bstep (se 1 (by rfl) ⟨4498565, by rfl⟩ : syracuseStep 5998087 = 8997131) B8997131
theorem B3999289 : Blo 1871637 3999289 := bstep (se 2 (by rfl) ⟨1499733, by rfl⟩ : syracuseStep 3999289 = 2999467) B2999467
theorem B4212521 : Blo 1871637 4212521 := bstep (se 2 (by rfl) ⟨1579695, by rfl⟩ : syracuseStep 4212521 = 3159391) B3159391
theorem B2107183 : Blo 1871637 2107183 := bstep (se 1 (by rfl) ⟨1580387, by rfl⟩ : syracuseStep 2107183 = 3160775) B3160775
theorem B3999545 : Blo 1871637 3999545 := bstep (se 2 (by rfl) ⟨1499829, by rfl⟩ : syracuseStep 3999545 = 2999659) B2999659
theorem B20244329 : Blo 1871637 20244329 := bstep (se 2 (by rfl) ⟨7591623, by rfl⟩ : syracuseStep 20244329 = 15183247) B15183247
theorem B15992711 : Blo 1871637 15992711 := bstep (se 1 (by rfl) ⟨11994533, by rfl⟩ : syracuseStep 15992711 = 23989067) B23989067
theorem B2107291 : Blo 1871637 2107291 := bstep (se 1 (by rfl) ⟨1580468, by rfl⟩ : syracuseStep 2107291 = 3160937) B3160937
theorem B6408143 : Blo 1871637 6408143 := bstep (se 1 (by rfl) ⟨4806107, by rfl⟩ : syracuseStep 6408143 = 9612215) B9612215
theorem B3795049 : Blo 1871637 3795049 := bstep (se 2 (by rfl) ⟨1423143, by rfl⟩ : syracuseStep 3795049 = 2846287) B2846287
theorem B6318215 : Blo 1871637 6318215 := bstep (se 1 (by rfl) ⟨4738661, by rfl⟩ : syracuseStep 6318215 = 9477323) B9477323
theorem B3999955 : Blo 1871637 3999955 := bstep (se 1 (by rfl) ⟨2999966, by rfl⟩ : syracuseStep 3999955 = 5999933) B5999933
theorem B2107687 : Blo 1871637 2107687 := bstep (se 1 (by rfl) ⟨1580765, by rfl⟩ : syracuseStep 2107687 = 3161531) B3161531
theorem B2107759 : Blo 1871637 2107759 := bstep (se 1 (by rfl) ⟨1580819, by rfl⟩ : syracuseStep 2107759 = 3161639) B3161639
theorem B11995559 : Blo 1871637 11995559 := bstep (se 1 (by rfl) ⟨8996669, by rfl⟩ : syracuseStep 11995559 = 17993339) B17993339
theorem B4737599 : Blo 1871637 4737599 := bstep (se 1 (by rfl) ⟨3553199, by rfl⟩ : syracuseStep 4737599 = 7106399) B7106399
theorem B8997439 : Blo 1871637 8997439 := bstep (se 1 (by rfl) ⟨6748079, by rfl⟩ : syracuseStep 8997439 = 13496159) B13496159
theorem B4500143 : Blo 1871637 4500143 := bstep (se 1 (by rfl) ⟨3375107, by rfl⟩ : syracuseStep 4500143 = 6750215) B6750215
theorem B4737811 : Blo 1871637 4737811 := bstep (se 1 (by rfl) ⟨3553358, by rfl⟩ : syracuseStep 4737811 = 7106717) B7106717
theorem B7113491 : Blo 1871637 7113491 := bstep (se 1 (by rfl) ⟨5335118, by rfl⟩ : syracuseStep 7113491 = 10670237) B10670237
theorem B4213583 : Blo 1871637 4213583 := bstep (se 1 (by rfl) ⟨3160187, by rfl⟩ : syracuseStep 4213583 = 6320375) B6320375
theorem B4213799 : Blo 1871637 4213799 := bstep (se 1 (by rfl) ⟨3160349, by rfl⟩ : syracuseStep 4213799 = 6320699) B6320699
theorem B16436291 : Blo 1871637 16436291 := bstep (se 1 (by rfl) ⟨12327218, by rfl⟩ : syracuseStep 16436291 = 24654437) B24654437
theorem B4738247 : Blo 1871637 4738247 := bstep (se 1 (by rfl) ⟨3553685, by rfl⟩ : syracuseStep 4738247 = 7107371) B7107371
theorem B4213979 : Blo 1871637 4213979 := bstep (se 1 (by rfl) ⟨3160484, by rfl⟩ : syracuseStep 4213979 = 6320969) B6320969
theorem B4738297 : Blo 1871637 4738297 := bstep (se 2 (by rfl) ⟨1776861, by rfl⟩ : syracuseStep 4738297 = 3553723) B3553723
theorem B19221791 : Blo 1871637 19221791 := bstep (se 1 (by rfl) ⟨14416343, by rfl⟩ : syracuseStep 19221791 = 28832687) B28832687
theorem B20254013 : Blo 1871637 20254013 := bstep (se 3 (by rfl) ⟨3797627, by rfl⟩ : syracuseStep 20254013 = 7595255) B7595255
theorem B6319457 : Blo 1871637 6319457 := bstep (se 2 (by rfl) ⟨2369796, by rfl⟩ : syracuseStep 6319457 = 4739593) B4739593
theorem B4214177 : Blo 1871637 4214177 := bstep (se 2 (by rfl) ⟨1580316, by rfl⟩ : syracuseStep 4214177 = 3160633) B3160633
theorem B4001185 : Blo 1871637 4001185 := bstep (se 2 (by rfl) ⟨1500444, by rfl⟩ : syracuseStep 4001185 = 3000889) B3000889
theorem B2371295 : Blo 1871637 2371295 := bstep (se 1 (by rfl) ⟨1778471, by rfl⟩ : syracuseStep 2371295 = 3556943) B3556943
theorem B1871663 : Blo 1871637 1871663 := bstep (se 1 (by rfl) ⟨1403747, by rfl⟩ : syracuseStep 1871663 = 2807495) B2807495
theorem B8662841 : Blo 1871637 8662841 := bstep (se 2 (by rfl) ⟨3248565, by rfl⟩ : syracuseStep 8662841 = 6497131) B6497131
theorem B4738945 : Blo 1871637 4738945 := bstep (se 2 (by rfl) ⟨1777104, by rfl⟩ : syracuseStep 4738945 = 3554209) B3554209
theorem B1871771 : Blo 1871637 1871771 := bstep (se 1 (by rfl) ⟨1403828, by rfl⟩ : syracuseStep 1871771 = 2807657) B2807657
theorem B1871823 : Blo 1871637 1871823 := bstep (se 1 (by rfl) ⟨1403867, by rfl⟩ : syracuseStep 1871823 = 2807735) B2807735
theorem B4214735 : Blo 1871637 4214735 := bstep (se 1 (by rfl) ⟨3161051, by rfl⟩ : syracuseStep 4214735 = 6322103) B6322103
theorem B1871847 : Blo 1871637 1871847 := bstep (se 1 (by rfl) ⟨1403885, by rfl⟩ : syracuseStep 1871847 = 2807771) B2807771
theorem B13496387 : Blo 1871637 13496387 := bstep (se 1 (by rfl) ⟨10122290, by rfl⟩ : syracuseStep 13496387 = 20244581) B20244581
theorem B9482345 : Blo 1871637 9482345 := bstep (se 2 (by rfl) ⟨3555879, by rfl⟩ : syracuseStep 9482345 = 7111759) B7111759
theorem B8999171 : Blo 1871637 8999171 := bstep (se 1 (by rfl) ⟨6749378, by rfl⟩ : syracuseStep 8999171 = 13498757) B13498757
theorem B1872159 : Blo 1871637 1872159 := bstep (se 1 (by rfl) ⟨1404119, by rfl⟩ : syracuseStep 1872159 = 2808239) B2808239
theorem B4215113 : Blo 1871637 4215113 := bstep (se 2 (by rfl) ⟨1580667, by rfl⟩ : syracuseStep 4215113 = 3161335) B3161335
theorem B1872219 : Blo 1871637 1872219 := bstep (se 1 (by rfl) ⟨1404164, by rfl⟩ : syracuseStep 1872219 = 2808329) B2808329
theorem B4215131 : Blo 1871637 4215131 := bstep (se 1 (by rfl) ⟨3161348, by rfl⟩ : syracuseStep 4215131 = 6322697) B6322697
theorem B1872239 : Blo 1871637 1872239 := bstep (se 1 (by rfl) ⟨1404179, by rfl⟩ : syracuseStep 1872239 = 2808359) B2808359
theorem B1872295 : Blo 1871637 1872295 := bstep (se 1 (by rfl) ⟨1404221, by rfl⟩ : syracuseStep 1872295 = 2808443) B2808443
theorem B10670555 : Blo 1871637 10670555 := bstep (se 1 (by rfl) ⟨8002916, by rfl⟩ : syracuseStep 10670555 = 16005833) B16005833
theorem B1872379 : Blo 1871637 1872379 := bstep (se 1 (by rfl) ⟨1404284, by rfl⟩ : syracuseStep 1872379 = 2808569) B2808569
theorem B1872447 : Blo 1871637 1872447 := bstep (se 1 (by rfl) ⟨1404335, by rfl⟩ : syracuseStep 1872447 = 2808671) B2808671
theorem B1872455 : Blo 1871637 1872455 := bstep (se 1 (by rfl) ⟨1404341, by rfl⟩ : syracuseStep 1872455 = 2808683) B2808683
theorem B3158635 : Blo 1871637 3158635 := bstep (se 1 (by rfl) ⟨2368976, by rfl⟩ : syracuseStep 3158635 = 4737953) B4737953
theorem B2667115 : Blo 1871637 2667115 := bstep (se 1 (by rfl) ⟨2000336, by rfl⟩ : syracuseStep 2667115 = 4000673) B4000673
theorem B4739705 : Blo 1871637 4739705 := bstep (se 2 (by rfl) ⟨1777389, by rfl⟩ : syracuseStep 4739705 = 3554779) B3554779
theorem B4739755 : Blo 1871637 4739755 := bstep (se 1 (by rfl) ⟨3554816, by rfl⟩ : syracuseStep 4739755 = 7109633) B7109633
theorem B8000183 : Blo 1871637 8000183 := bstep (se 1 (by rfl) ⟨6000137, by rfl⟩ : syracuseStep 8000183 = 12000275) B12000275
theorem B1872607 : Blo 1871637 1872607 := bstep (se 1 (by rfl) ⟨1404455, by rfl⟩ : syracuseStep 1872607 = 2808911) B2808911
theorem B1872687 : Blo 1871637 1872687 := bstep (se 1 (by rfl) ⟨1404515, by rfl⟩ : syracuseStep 1872687 = 2809031) B2809031
theorem B16003919 : Blo 1871637 16003919 := bstep (se 1 (by rfl) ⟨12002939, by rfl⟩ : syracuseStep 16003919 = 24005879) B24005879
theorem B2667343 : Blo 1871637 2667343 := bstep (se 1 (by rfl) ⟨2000507, by rfl⟩ : syracuseStep 2667343 = 4001015) B4001015
theorem B3158939 : Blo 1871637 3158939 := bstep (se 1 (by rfl) ⟨2369204, by rfl⟩ : syracuseStep 3158939 = 4738409) B4738409
theorem B1872795 : Blo 1871637 1872795 := bstep (se 1 (by rfl) ⟨1404596, by rfl⟩ : syracuseStep 1872795 = 2809193) B2809193
theorem B1872847 : Blo 1871637 1872847 := bstep (se 1 (by rfl) ⟨1404635, by rfl⟩ : syracuseStep 1872847 = 2809271) B2809271
theorem B4740059 : Blo 1871637 4740059 := bstep (se 1 (by rfl) ⟨3555044, by rfl⟩ : syracuseStep 4740059 = 7110089) B7110089
theorem B1872871 : Blo 1871637 1872871 := bstep (se 1 (by rfl) ⟨1404653, by rfl⟩ : syracuseStep 1872871 = 2809307) B2809307
theorem B9475217 : Blo 1871637 9475217 := bstep (se 2 (by rfl) ⟨3553206, by rfl⟩ : syracuseStep 9475217 = 7106413) B7106413
theorem B9483479 : Blo 1871637 9483479 := bstep (se 1 (by rfl) ⟨7112609, by rfl⟩ : syracuseStep 9483479 = 14225219) B14225219
theorem B6321401 : Blo 1871637 6321401 := bstep (se 2 (by rfl) ⟨2370525, by rfl⟩ : syracuseStep 6321401 = 4741051) B4741051
theorem B152040719 : Blo 1871637 152040719 := bstep (se 1 (by rfl) ⟨114030539, by rfl⟩ : syracuseStep 152040719 = 228061079) B228061079
theorem B17995031 : Blo 1871637 17995031 := bstep (se 1 (by rfl) ⟨13496273, by rfl⟩ : syracuseStep 17995031 = 26992547) B26992547
theorem B4740383 : Blo 1871637 4740383 := bstep (se 1 (by rfl) ⟨3555287, by rfl⟩ : syracuseStep 4740383 = 7110575) B7110575
theorem B1873183 : Blo 1871637 1873183 := bstep (se 1 (by rfl) ⟨1404887, by rfl⟩ : syracuseStep 1873183 = 2809775) B2809775
theorem B1873243 : Blo 1871637 1873243 := bstep (se 1 (by rfl) ⟨1404932, by rfl⟩ : syracuseStep 1873243 = 2809865) B2809865
theorem B1873263 : Blo 1871637 1873263 := bstep (se 1 (by rfl) ⟨1404947, by rfl⟩ : syracuseStep 1873263 = 2809895) B2809895
theorem B1873319 : Blo 1871637 1873319 := bstep (se 1 (by rfl) ⟨1404989, by rfl⟩ : syracuseStep 1873319 = 2809979) B2809979
theorem B1873403 : Blo 1871637 1873403 := bstep (se 1 (by rfl) ⟨1405052, by rfl⟩ : syracuseStep 1873403 = 2810105) B2810105
theorem B6321671 : Blo 1871637 6321671 := bstep (se 1 (by rfl) ⟨4741253, by rfl⟩ : syracuseStep 6321671 = 9482507) B9482507
theorem B1873471 : Blo 1871637 1873471 := bstep (se 1 (by rfl) ⟨1405103, by rfl⟩ : syracuseStep 1873471 = 2810207) B2810207
theorem B1873479 : Blo 1871637 1873479 := bstep (se 1 (by rfl) ⟨1405109, by rfl⟩ : syracuseStep 1873479 = 2810219) B2810219
theorem B1873631 : Blo 1871637 1873631 := bstep (se 1 (by rfl) ⟨1405223, by rfl⟩ : syracuseStep 1873631 = 2810447) B2810447
theorem B2807531 : Blo 1871637 2807531 := bstep (se 1 (by rfl) ⟨2105648, by rfl⟩ : syracuseStep 2807531 = 4211297) B4211297
theorem B31995809 : Blo 1871637 31995809 := bstep (se 2 (by rfl) ⟨11998428, by rfl⟩ : syracuseStep 31995809 = 23996857) B23996857
theorem B2807759 : Blo 1871637 2807759 := bstep (se 1 (by rfl) ⟨2105819, by rfl⟩ : syracuseStep 2807759 = 4211639) B4211639
theorem B18004103 : Blo 1871637 18004103 := bstep (se 1 (by rfl) ⟨13503077, by rfl⟩ : syracuseStep 18004103 = 27006155) B27006155
theorem B2808155 : Blo 1871637 2808155 := bstep (se 1 (by rfl) ⟨2106116, by rfl⟩ : syracuseStep 2808155 = 4212233) B4212233
theorem B4741487 : Blo 1871637 4741487 := bstep (se 1 (by rfl) ⟨3556115, by rfl⟩ : syracuseStep 4741487 = 7112231) B7112231
theorem B5331383 : Blo 1871637 5331383 := bstep (se 1 (by rfl) ⟨3998537, by rfl⟩ : syracuseStep 5331383 = 7997075) B7997075
theorem B16005559 : Blo 1871637 16005559 := bstep (se 1 (by rfl) ⟨12004169, by rfl⟩ : syracuseStep 16005559 = 24008339) B24008339
theorem B6322643 : Blo 1871637 6322643 := bstep (se 1 (by rfl) ⟨4741982, by rfl⟩ : syracuseStep 6322643 = 9483965) B9483965
theorem B45537851 : Blo 1871637 45537851 := bstep (se 1 (by rfl) ⟨34153388, by rfl⟩ : syracuseStep 45537851 = 68306777) B68306777
theorem B2808383 : Blo 1871637 2808383 := bstep (se 1 (by rfl) ⟨2106287, by rfl⟩ : syracuseStep 2808383 = 4212575) B4212575
theorem B6322751 : Blo 1871637 6322751 := bstep (se 1 (by rfl) ⟨4742063, by rfl⟩ : syracuseStep 6322751 = 9484127) B9484127
theorem B2808503 : Blo 1871637 2808503 := bstep (se 1 (by rfl) ⟨2106377, by rfl⟩ : syracuseStep 2808503 = 4212755) B4212755
theorem B7109315 : Blo 1871637 7109315 := bstep (se 1 (by rfl) ⟨5331986, by rfl⟩ : syracuseStep 7109315 = 10663973) B10663973
theorem B10664723 : Blo 1871637 10664723 := bstep (se 1 (by rfl) ⟨7998542, by rfl⟩ : syracuseStep 10664723 = 15997085) B15997085
theorem B15997769 : Blo 1871637 15997769 := bstep (se 2 (by rfl) ⟨5999163, by rfl⟩ : syracuseStep 15997769 = 11998327) B11998327
theorem B17996687 : Blo 1871637 17996687 := bstep (se 1 (by rfl) ⟨13497515, by rfl⟩ : syracuseStep 17996687 = 26995031) B26995031
theorem B2808731 : Blo 1871637 2808731 := bstep (se 1 (by rfl) ⟨2106548, by rfl⟩ : syracuseStep 2808731 = 4213097) B4213097
theorem B5692331 : Blo 1871637 5692331 := bstep (se 1 (by rfl) ⟨4269248, by rfl⟩ : syracuseStep 5692331 = 8538497) B8538497
theorem B23985071 : Blo 1871637 23985071 := bstep (se 1 (by rfl) ⟨17988803, by rfl⟩ : syracuseStep 23985071 = 35977607) B35977607
theorem B4742135 : Blo 1871637 4742135 := bstep (se 1 (by rfl) ⟨3556601, by rfl⟩ : syracuseStep 4742135 = 7113203) B7113203
theorem B34151645 : Blo 1871637 34151645 := bstep (se 3 (by rfl) ⟨6403433, by rfl⟩ : syracuseStep 34151645 = 12806867) B12806867
theorem B10263773 : Blo 1871637 10263773 := bstep (se 3 (by rfl) ⟨1924457, by rfl⟩ : syracuseStep 10263773 = 3848915) B3848915
theorem B17997029 : Blo 1871637 17997029 := bstep (se 4 (by rfl) ⟨1687221, by rfl⟩ : syracuseStep 17997029 = 3374443) B3374443
theorem B2809127 : Blo 1871637 2809127 := bstep (se 1 (by rfl) ⟨2106845, by rfl⟩ : syracuseStep 2809127 = 4213691) B4213691
theorem B2809211 : Blo 1871637 2809211 := bstep (se 1 (by rfl) ⟨2106908, by rfl⟩ : syracuseStep 2809211 = 4213817) B4213817
theorem B3374473 : Blo 1871637 3374473 := bstep (se 2 (by rfl) ⟨1265427, by rfl⟩ : syracuseStep 3374473 = 2530855) B2530855
theorem B4054459 : Blo 1871637 4054459 := bstep (se 1 (by rfl) ⟨3040844, by rfl⟩ : syracuseStep 4054459 = 6081689) B6081689
theorem B10665431 : Blo 1871637 10665431 := bstep (se 1 (by rfl) ⟨7999073, by rfl⟩ : syracuseStep 10665431 = 15998147) B15998147
theorem B2809337 : Blo 1871637 2809337 := bstep (se 2 (by rfl) ⟨1053501, by rfl⟩ : syracuseStep 2809337 = 2107003) B2107003
theorem B9477647 : Blo 1871637 9477647 := bstep (se 1 (by rfl) ⟨7108235, by rfl⟩ : syracuseStep 9477647 = 14216471) B14216471
theorem B2809439 : Blo 1871637 2809439 := bstep (se 1 (by rfl) ⟨2107079, by rfl⟩ : syracuseStep 2809439 = 4214159) B4214159
theorem B3997487 : Blo 1871637 3997487 := bstep (se 1 (by rfl) ⟨2998115, by rfl⟩ : syracuseStep 3997487 = 5996231) B5996231
theorem B2809655 : Blo 1871637 2809655 := bstep (se 1 (by rfl) ⟨2107241, by rfl⟩ : syracuseStep 2809655 = 4214483) B4214483
theorem B15187819 : Blo 1871637 15187819 := bstep (se 1 (by rfl) ⟨11390864, by rfl⟩ : syracuseStep 15187819 = 22781729) B22781729
theorem B2810075 : Blo 1871637 2810075 := bstep (se 1 (by rfl) ⟨2107556, by rfl⟩ : syracuseStep 2810075 = 4215113) B4215113
theorem B2810087 : Blo 1871637 2810087 := bstep (se 1 (by rfl) ⟨2107565, by rfl⟩ : syracuseStep 2810087 = 4215131) B4215131
theorem B5333273 : Blo 1871637 5333273 := bstep (se 2 (by rfl) ⟨1999977, by rfl⟩ : syracuseStep 5333273 = 3999955) B3999955
theorem B2810249 : Blo 1871637 2810249 := bstep (se 2 (by rfl) ⟨1053843, by rfl⟩ : syracuseStep 2810249 = 2107687) B2107687
theorem B10125751 : Blo 1871637 10125751 := bstep (se 1 (by rfl) ⟨7594313, by rfl⟩ : syracuseStep 10125751 = 15188627) B15188627
theorem B6750647 : Blo 1871637 6750647 := bstep (se 1 (by rfl) ⟨5062985, by rfl⟩ : syracuseStep 6750647 = 10125971) B10125971
theorem B5996987 : Blo 1871637 5996987 := bstep (se 1 (by rfl) ⟨4497740, by rfl⟩ : syracuseStep 5996987 = 8995481) B8995481
theorem B5333455 : Blo 1871637 5333455 := bstep (se 1 (by rfl) ⟨4000091, by rfl⟩ : syracuseStep 5333455 = 8000183) B8000183
theorem B2810345 : Blo 1871637 2810345 := bstep (se 2 (by rfl) ⟨1053879, by rfl⟩ : syracuseStep 2810345 = 2107759) B2107759
theorem B21340745 : Blo 1871637 21340745 := bstep (se 2 (by rfl) ⟨8002779, by rfl⟩ : syracuseStep 21340745 = 16005559) B16005559
theorem B27370061 : Blo 1871637 27370061 := bstep (se 3 (by rfl) ⟨5131886, by rfl⟩ : syracuseStep 27370061 = 10263773) B10263773
theorem B2105959 : Blo 1871637 2105959 := bstep (se 1 (by rfl) ⟨1579469, by rfl⟩ : syracuseStep 2105959 = 3158939) B3158939
theorem B51258109 : Blo 1871637 51258109 := bstep (se 3 (by rfl) ⟨9610895, by rfl⟩ : syracuseStep 51258109 = 19221791) B19221791
theorem B6316811 : Blo 1871637 6316811 := bstep (se 1 (by rfl) ⟨4737608, by rfl⟩ : syracuseStep 6316811 = 9475217) B9475217
theorem B43254577 : Blo 1871637 43254577 := bstep (se 2 (by rfl) ⟨16220466, by rfl⟩ : syracuseStep 43254577 = 32440933) B32440933
theorem B4211513 : Blo 1871637 4211513 := bstep (se 2 (by rfl) ⟨1579317, by rfl⟩ : syracuseStep 4211513 = 3158635) B3158635
theorem B3556153 : Blo 1871637 3556153 := bstep (se 2 (by rfl) ⟨1333557, by rfl⟩ : syracuseStep 3556153 = 2667115) B2667115
theorem B101360479 : Blo 1871637 101360479 := bstep (se 1 (by rfl) ⟨76020359, by rfl⟩ : syracuseStep 101360479 = 152040719) B152040719
theorem B4211567 : Blo 1871637 4211567 := bstep (se 1 (by rfl) ⟨3158675, by rfl⟩ : syracuseStep 4211567 = 6317351) B6317351
theorem B6317081 : Blo 1871637 6317081 := bstep (se 2 (by rfl) ⟨2368905, by rfl⟩ : syracuseStep 6317081 = 4737811) B4737811
theorem B3556457 : Blo 1871637 3556457 := bstep (se 2 (by rfl) ⟨1333671, by rfl⟩ : syracuseStep 3556457 = 2667343) B2667343
theorem B4212143 : Blo 1871637 4212143 := bstep (se 1 (by rfl) ⟨3159107, by rfl⟩ : syracuseStep 4212143 = 6318215) B6318215
theorem B12002735 : Blo 1871637 12002735 := bstep (se 1 (by rfl) ⟨9002051, by rfl⟩ : syracuseStep 12002735 = 18004103) B18004103
theorem B7997039 : Blo 1871637 7997039 := bstep (se 1 (by rfl) ⟨5997779, by rfl⟩ : syracuseStep 7997039 = 11995559) B11995559
theorem B6317729 : Blo 1871637 6317729 := bstep (se 2 (by rfl) ⟨2369148, by rfl⟩ : syracuseStep 6317729 = 4738297) B4738297
theorem B3000095 : Blo 1871637 3000095 := bstep (se 1 (by rfl) ⟨2250071, by rfl⟩ : syracuseStep 3000095 = 4500143) B4500143
theorem B4499297 : Blo 1871637 4499297 := bstep (se 2 (by rfl) ⟨1687236, by rfl⟩ : syracuseStep 4499297 = 3374473) B3374473
theorem B5334913 : Blo 1871637 5334913 := bstep (se 2 (by rfl) ⟨2000592, by rfl⟩ : syracuseStep 5334913 = 4001185) B4001185
theorem B3794887 : Blo 1871637 3794887 := bstep (se 1 (by rfl) ⟨2846165, by rfl⟩ : syracuseStep 3794887 = 5692331) B5692331
theorem B7997449 : Blo 1871637 7997449 := bstep (se 2 (by rfl) ⟨2999043, by rfl⟩ : syracuseStep 7997449 = 5998087) B5998087
theorem B22767763 : Blo 1871637 22767763 := bstep (se 1 (by rfl) ⟨17075822, by rfl⟩ : syracuseStep 22767763 = 34151645) B34151645
theorem B13502675 : Blo 1871637 13502675 := bstep (se 1 (by rfl) ⟨10127006, by rfl⟩ : syracuseStep 13502675 = 20254013) B20254013
theorem B4212971 : Blo 1871637 4212971 := bstep (se 1 (by rfl) ⟨3159728, by rfl⟩ : syracuseStep 4212971 = 6319457) B6319457
theorem B6318431 : Blo 1871637 6318431 := bstep (se 1 (by rfl) ⟨4738823, by rfl⟩ : syracuseStep 6318431 = 9477647) B9477647
theorem B6318593 : Blo 1871637 6318593 := bstep (se 2 (by rfl) ⟨2369472, by rfl⟩ : syracuseStep 6318593 = 4738945) B4738945
theorem B2664991 : Blo 1871637 2664991 := bstep (se 1 (by rfl) ⟨1998743, by rfl⟩ : syracuseStep 2664991 = 3997487) B3997487
theorem B9480887 : Blo 1871637 9480887 := bstep (se 1 (by rfl) ⟨7110665, by rfl⟩ : syracuseStep 9480887 = 14221331) B14221331
theorem B5999447 : Blo 1871637 5999447 := bstep (se 1 (by rfl) ⟨4499585, by rfl⟩ : syracuseStep 5999447 = 8999171) B8999171
theorem B35990365 : Blo 1871637 35990365 := bstep (se 3 (by rfl) ⟨6748193, by rfl⟩ : syracuseStep 35990365 = 13496387) B13496387
theorem B43830109 : Blo 1871637 43830109 := bstep (se 3 (by rfl) ⟨8218145, by rfl⟩ : syracuseStep 43830109 = 16436291) B16436291
theorem B15993773 : Blo 1871637 15993773 := bstep (se 3 (by rfl) ⟨2998832, by rfl⟩ : syracuseStep 15993773 = 5997665) B5997665
theorem B6319079 : Blo 1871637 6319079 := bstep (se 1 (by rfl) ⟨4739309, by rfl⟩ : syracuseStep 6319079 = 9478619) B9478619
theorem B7113703 : Blo 1871637 7113703 := bstep (se 1 (by rfl) ⟨5335277, by rfl⟩ : syracuseStep 7113703 = 10670555) B10670555
theorem B2665543 : Blo 1871637 2665543 := bstep (se 1 (by rfl) ⟨1999157, by rfl⟩ : syracuseStep 2665543 = 3998315) B3998315
theorem B10669279 : Blo 1871637 10669279 := bstep (se 1 (by rfl) ⟨8001959, by rfl⟩ : syracuseStep 10669279 = 16003919) B16003919
theorem B6319403 : Blo 1871637 6319403 := bstep (se 1 (by rfl) ⟨4739552, by rfl⟩ : syracuseStep 6319403 = 9479105) B9479105
theorem B11996585 : Blo 1871637 11996585 := bstep (se 2 (by rfl) ⟨4498719, by rfl⟩ : syracuseStep 11996585 = 8997439) B8997439
theorem B4214267 : Blo 1871637 4214267 := bstep (se 1 (by rfl) ⟨3160700, by rfl⟩ : syracuseStep 4214267 = 6321401) B6321401
theorem B11996687 : Blo 1871637 11996687 := bstep (se 1 (by rfl) ⟨8997515, by rfl⟩ : syracuseStep 11996687 = 17995031) B17995031
theorem B6319673 : Blo 1871637 6319673 := bstep (se 2 (by rfl) ⟨2369877, by rfl⟩ : syracuseStep 6319673 = 4739755) B4739755
theorem B4214447 : Blo 1871637 4214447 := bstep (se 1 (by rfl) ⟨3160835, by rfl⟩ : syracuseStep 4214447 = 6321671) B6321671
theorem B1871687 : Blo 1871637 1871687 := bstep (se 1 (by rfl) ⟨1403765, by rfl⟩ : syracuseStep 1871687 = 2807531) B2807531
theorem B23990093 : Blo 1871637 23990093 := bstep (se 3 (by rfl) ⟨4498142, by rfl⟩ : syracuseStep 23990093 = 8996285) B8996285
theorem B2666363 : Blo 1871637 2666363 := bstep (se 1 (by rfl) ⟨1999772, by rfl⟩ : syracuseStep 2666363 = 3999545) B3999545
theorem B13496219 : Blo 1871637 13496219 := bstep (se 1 (by rfl) ⟨10122164, by rfl⟩ : syracuseStep 13496219 = 20244329) B20244329
theorem B10661807 : Blo 1871637 10661807 := bstep (se 1 (by rfl) ⟨7996355, by rfl⟩ : syracuseStep 10661807 = 15992711) B15992711
theorem B1871839 : Blo 1871637 1871839 := bstep (se 1 (by rfl) ⟨1403879, by rfl⟩ : syracuseStep 1871839 = 2807759) B2807759
theorem B4272095 : Blo 1871637 4272095 := bstep (se 1 (by rfl) ⟨3204071, by rfl⟩ : syracuseStep 4272095 = 6408143) B6408143
theorem B1872103 : Blo 1871637 1872103 := bstep (se 1 (by rfl) ⟨1404077, by rfl⟩ : syracuseStep 1872103 = 2808155) B2808155
theorem B4215095 : Blo 1871637 4215095 := bstep (se 1 (by rfl) ⟨3161321, by rfl⟩ : syracuseStep 4215095 = 6322643) B6322643
theorem B3158399 : Blo 1871637 3158399 := bstep (se 1 (by rfl) ⟨2368799, by rfl⟩ : syracuseStep 3158399 = 4737599) B4737599
theorem B1872255 : Blo 1871637 1872255 := bstep (se 1 (by rfl) ⟨1404191, by rfl⟩ : syracuseStep 1872255 = 2808383) B2808383
theorem B4215167 : Blo 1871637 4215167 := bstep (se 1 (by rfl) ⟨3161375, by rfl⟩ : syracuseStep 4215167 = 6322751) B6322751
theorem B1872335 : Blo 1871637 1872335 := bstep (se 1 (by rfl) ⟨1404251, by rfl⟩ : syracuseStep 1872335 = 2808503) B2808503
theorem B4739543 : Blo 1871637 4739543 := bstep (se 1 (by rfl) ⟨3554657, by rfl⟩ : syracuseStep 4739543 = 7109315) B7109315
theorem B2667001 : Blo 1871637 2667001 := bstep (se 2 (by rfl) ⟨1000125, by rfl⟩ : syracuseStep 2667001 = 2000251) B2000251
theorem B11997791 : Blo 1871637 11997791 := bstep (se 1 (by rfl) ⟨8998343, by rfl⟩ : syracuseStep 11997791 = 17996687) B17996687
theorem B1872487 : Blo 1871637 1872487 := bstep (se 1 (by rfl) ⟨1404365, by rfl⟩ : syracuseStep 1872487 = 2808731) B2808731
theorem B3158831 : Blo 1871637 3158831 := bstep (se 1 (by rfl) ⟨2369123, by rfl⟩ : syracuseStep 3158831 = 4738247) B4738247
theorem B11998019 : Blo 1871637 11998019 := bstep (se 1 (by rfl) ⟨8998514, by rfl⟩ : syracuseStep 11998019 = 17997029) B17997029
theorem B1872751 : Blo 1871637 1872751 := bstep (se 1 (by rfl) ⟨1404563, by rfl⟩ : syracuseStep 1872751 = 2809127) B2809127
theorem B1872807 : Blo 1871637 1872807 := bstep (se 1 (by rfl) ⟨1404605, by rfl⟩ : syracuseStep 1872807 = 2809211) B2809211
theorem B1872891 : Blo 1871637 1872891 := bstep (se 1 (by rfl) ⟨1404668, by rfl⟩ : syracuseStep 1872891 = 2809337) B2809337
theorem B1872959 : Blo 1871637 1872959 := bstep (se 1 (by rfl) ⟨1404719, by rfl⟩ : syracuseStep 1872959 = 2809439) B2809439
theorem B1873103 : Blo 1871637 1873103 := bstep (se 1 (by rfl) ⟨1404827, by rfl⟩ : syracuseStep 1873103 = 2809655) B2809655
theorem B6321563 : Blo 1871637 6321563 := bstep (se 1 (by rfl) ⟨4741172, by rfl⟩ : syracuseStep 6321563 = 9482345) B9482345
theorem B1873307 : Blo 1871637 1873307 := bstep (se 1 (by rfl) ⟨1404980, by rfl⟩ : syracuseStep 1873307 = 2809961) B2809961
theorem B5060065 : Blo 1871637 5060065 := bstep (se 2 (by rfl) ⟨1897524, by rfl⟩ : syracuseStep 5060065 = 3795049) B3795049
theorem B1873519 : Blo 1871637 1873519 := bstep (se 1 (by rfl) ⟨1405139, by rfl⟩ : syracuseStep 1873519 = 2810279) B2810279
theorem B1873575 : Blo 1871637 1873575 := bstep (se 1 (by rfl) ⟨1405181, by rfl⟩ : syracuseStep 1873575 = 2810363) B2810363
theorem B2807519 : Blo 1871637 2807519 := bstep (se 1 (by rfl) ⟨2105639, by rfl⟩ : syracuseStep 2807519 = 4211279) B4211279
theorem B3159803 : Blo 1871637 3159803 := bstep (se 1 (by rfl) ⟨2369852, by rfl⟩ : syracuseStep 3159803 = 4739705) B4739705
theorem B2807615 : Blo 1871637 2807615 := bstep (se 1 (by rfl) ⟨2105711, by rfl⟩ : syracuseStep 2807615 = 4211423) B4211423
theorem B4741001 : Blo 1871637 4741001 := bstep (se 2 (by rfl) ⟨1777875, by rfl⟩ : syracuseStep 4741001 = 3555751) B3555751
theorem B2807783 : Blo 1871637 2807783 := bstep (se 1 (by rfl) ⟨2105837, by rfl⟩ : syracuseStep 2807783 = 4211675) B4211675
theorem B3160039 : Blo 1871637 3160039 := bstep (se 1 (by rfl) ⟨2370029, by rfl⟩ : syracuseStep 3160039 = 4740059) B4740059
theorem B5330927 : Blo 1871637 5330927 := bstep (se 1 (by rfl) ⟨3998195, by rfl⟩ : syracuseStep 5330927 = 7996391) B7996391
theorem B2807801 : Blo 1871637 2807801 := bstep (se 2 (by rfl) ⟨1052925, by rfl⟩ : syracuseStep 2807801 = 2105851) B2105851
theorem B2807903 : Blo 1871637 2807903 := bstep (se 1 (by rfl) ⟨2105927, by rfl⟩ : syracuseStep 2807903 = 4211855) B4211855
theorem B5331041 : Blo 1871637 5331041 := bstep (se 2 (by rfl) ⟨1999140, by rfl⟩ : syracuseStep 5331041 = 3998281) B3998281
theorem B6322319 : Blo 1871637 6322319 := bstep (se 1 (by rfl) ⟨4741739, by rfl⟩ : syracuseStep 6322319 = 9483479) B9483479
theorem B2807963 : Blo 1871637 2807963 := bstep (se 1 (by rfl) ⟨2105972, by rfl⟩ : syracuseStep 2807963 = 4211945) B4211945
theorem B2807999 : Blo 1871637 2807999 := bstep (se 1 (by rfl) ⟨2105999, by rfl⟩ : syracuseStep 2807999 = 4211999) B4211999
theorem B3160255 : Blo 1871637 3160255 := bstep (se 1 (by rfl) ⟨2370191, by rfl⟩ : syracuseStep 3160255 = 4740383) B4740383
theorem B2808041 : Blo 1871637 2808041 := bstep (se 2 (by rfl) ⟨1053015, by rfl⟩ : syracuseStep 2808041 = 2106031) B2106031
theorem B2808347 : Blo 1871637 2808347 := bstep (se 1 (by rfl) ⟨2106260, by rfl⟩ : syracuseStep 2808347 = 4212521) B4212521
theorem B2808425 : Blo 1871637 2808425 := bstep (se 2 (by rfl) ⟨1053159, by rfl⟩ : syracuseStep 2808425 = 2106319) B2106319
theorem B21330539 : Blo 1871637 21330539 := bstep (se 1 (by rfl) ⟨15997904, by rfl⟩ : syracuseStep 21330539 = 31995809) B31995809
theorem B45570761 : Blo 1871637 45570761 := bstep (se 2 (by rfl) ⟨17089035, by rfl⟩ : syracuseStep 45570761 = 34178071) B34178071
theorem B3160991 : Blo 1871637 3160991 := bstep (se 1 (by rfl) ⟨2370743, by rfl⟩ : syracuseStep 3160991 = 4741487) B4741487
theorem B3554255 : Blo 1871637 3554255 := bstep (se 1 (by rfl) ⟨2665691, by rfl⟩ : syracuseStep 3554255 = 5331383) B5331383
theorem B30358567 : Blo 1871637 30358567 := bstep (se 1 (by rfl) ⟨22768925, by rfl⟩ : syracuseStep 30358567 = 45537851) B45537851
theorem B4742185 : Blo 1871637 4742185 := bstep (se 2 (by rfl) ⟨1778319, by rfl⟩ : syracuseStep 4742185 = 3556639) B3556639
theorem B2808953 : Blo 1871637 2808953 := bstep (se 2 (by rfl) ⟨1053357, by rfl⟩ : syracuseStep 2808953 = 2106715) B2106715
theorem B7109815 : Blo 1871637 7109815 := bstep (se 1 (by rfl) ⟨5332361, by rfl⟩ : syracuseStep 7109815 = 10664723) B10664723
theorem B4742327 : Blo 1871637 4742327 := bstep (se 1 (by rfl) ⟨3556745, by rfl⟩ : syracuseStep 4742327 = 7113491) B7113491
theorem B10665179 : Blo 1871637 10665179 := bstep (se 1 (by rfl) ⟨7998884, by rfl⟩ : syracuseStep 10665179 = 15997769) B15997769
theorem B2809055 : Blo 1871637 2809055 := bstep (se 1 (by rfl) ⟨2106791, by rfl⟩ : syracuseStep 2809055 = 4213583) B4213583
theorem B5405945 : Blo 1871637 5405945 := bstep (se 2 (by rfl) ⟨2027229, by rfl⟩ : syracuseStep 5405945 = 4054459) B4054459
theorem B6323453 : Blo 1871637 6323453 := bstep (se 3 (by rfl) ⟨1185647, by rfl⟩ : syracuseStep 6323453 = 2371295) B2371295
theorem B3202313 : Blo 1871637 3202313 := bstep (se 2 (by rfl) ⟨1200867, by rfl⟩ : syracuseStep 3202313 = 2401735) B2401735
theorem B2809097 : Blo 1871637 2809097 := bstep (se 2 (by rfl) ⟨1053411, by rfl⟩ : syracuseStep 2809097 = 2106823) B2106823
theorem B15990047 : Blo 1871637 15990047 := bstep (se 1 (by rfl) ⟨11992535, by rfl⟩ : syracuseStep 15990047 = 23985071) B23985071
theorem B3161423 : Blo 1871637 3161423 := bstep (se 1 (by rfl) ⟨2371067, by rfl⟩ : syracuseStep 3161423 = 4742135) B4742135
theorem B2809199 : Blo 1871637 2809199 := bstep (se 1 (by rfl) ⟨2106899, by rfl⟩ : syracuseStep 2809199 = 4213799) B4213799
theorem B5332385 : Blo 1871637 5332385 := bstep (se 2 (by rfl) ⟨1999644, by rfl⟩ : syracuseStep 5332385 = 3999289) B3999289
theorem B2809319 : Blo 1871637 2809319 := bstep (se 1 (by rfl) ⟨2106989, by rfl⟩ : syracuseStep 2809319 = 4213979) B4213979
theorem B2809451 : Blo 1871637 2809451 := bstep (se 1 (by rfl) ⟨2107088, by rfl⟩ : syracuseStep 2809451 = 4214177) B4214177
theorem B7110287 : Blo 1871637 7110287 := bstep (se 1 (by rfl) ⟨5332715, by rfl⟩ : syracuseStep 7110287 = 10665431) B10665431
theorem B2809577 : Blo 1871637 2809577 := bstep (se 2 (by rfl) ⟨1053591, by rfl⟩ : syracuseStep 2809577 = 2107183) B2107183
theorem B20250425 : Blo 1871637 20250425 := bstep (se 2 (by rfl) ⟨7593909, by rfl⟩ : syracuseStep 20250425 = 15187819) B15187819
theorem B2809721 : Blo 1871637 2809721 := bstep (se 2 (by rfl) ⟨1053645, by rfl⟩ : syracuseStep 2809721 = 2107291) B2107291
theorem B5775227 : Blo 1871637 5775227 := bstep (se 1 (by rfl) ⟨4331420, by rfl⟩ : syracuseStep 5775227 = 8662841) B8662841
theorem B2809823 : Blo 1871637 2809823 := bstep (se 1 (by rfl) ⟨2107367, by rfl⟩ : syracuseStep 2809823 = 4214735) B4214735
theorem B3555515 : Blo 1871637 3555515 := bstep (se 1 (by rfl) ⟨2666636, by rfl⟩ : syracuseStep 3555515 = 5333273) B5333273
theorem B2810063 : Blo 1871637 2810063 := bstep (se 1 (by rfl) ⟨2107547, by rfl⟩ : syracuseStep 2810063 = 4215095) B4215095
theorem B2105599 : Blo 1871637 2105599 := bstep (se 1 (by rfl) ⟨1579199, by rfl⟩ : syracuseStep 2105599 = 3158399) B3158399
theorem B2810111 : Blo 1871637 2810111 := bstep (se 1 (by rfl) ⟨2107583, by rfl⟩ : syracuseStep 2810111 = 4215167) B4215167
theorem B3997991 : Blo 1871637 3997991 := bstep (se 1 (by rfl) ⟨2998493, by rfl⟩ : syracuseStep 3997991 = 5996987) B5996987
theorem B4211207 : Blo 1871637 4211207 := bstep (se 1 (by rfl) ⟨3158405, by rfl⟩ : syracuseStep 4211207 = 6316811) B6316811
theorem B2105887 : Blo 1871637 2105887 := bstep (se 1 (by rfl) ⟨1579415, by rfl⟩ : syracuseStep 2105887 = 3158831) B3158831
theorem B13501001 : Blo 1871637 13501001 := bstep (se 2 (by rfl) ⟨5062875, by rfl⟩ : syracuseStep 13501001 = 10125751) B10125751
theorem B7111273 : Blo 1871637 7111273 := bstep (se 2 (by rfl) ⟨2666727, by rfl⟩ : syracuseStep 7111273 = 5333455) B5333455
theorem B3556001 : Blo 1871637 3556001 := bstep (se 2 (by rfl) ⟨1333500, by rfl⟩ : syracuseStep 3556001 = 2667001) B2667001
theorem B4211387 : Blo 1871637 4211387 := bstep (se 1 (by rfl) ⟨3158540, by rfl⟩ : syracuseStep 4211387 = 6317081) B6317081
theorem B57672769 : Blo 1871637 57672769 := bstep (se 2 (by rfl) ⟨21627288, by rfl⟩ : syracuseStep 57672769 = 43254577) B43254577
theorem B4211819 : Blo 1871637 4211819 := bstep (se 1 (by rfl) ⟨3158864, by rfl⟩ : syracuseStep 4211819 = 6317729) B6317729
theorem B2106535 : Blo 1871637 2106535 := bstep (se 1 (by rfl) ⟨1579901, by rfl⟩ : syracuseStep 2106535 = 3159803) B3159803
theorem B2000063 : Blo 1871637 2000063 := bstep (se 1 (by rfl) ⟨1500047, by rfl⟩ : syracuseStep 2000063 = 3000095) B3000095
theorem B2999531 : Blo 1871637 2999531 := bstep (se 1 (by rfl) ⟨2249648, by rfl⟩ : syracuseStep 2999531 = 4499297) B4499297
theorem B4212287 : Blo 1871637 4212287 := bstep (se 1 (by rfl) ⟨3159215, by rfl⟩ : syracuseStep 4212287 = 6318431) B6318431
theorem B9479753 : Blo 1871637 9479753 := bstep (se 2 (by rfl) ⟨3554907, by rfl⟩ : syracuseStep 9479753 = 7109815) B7109815
theorem B4212395 : Blo 1871637 4212395 := bstep (se 1 (by rfl) ⟨3159296, by rfl⟩ : syracuseStep 4212395 = 6318593) B6318593
theorem B3999631 : Blo 1871637 3999631 := bstep (se 1 (by rfl) ⟨2999723, by rfl⟩ : syracuseStep 3999631 = 5999447) B5999447
theorem B2107327 : Blo 1871637 2107327 := bstep (se 1 (by rfl) ⟨1580495, by rfl⟩ : syracuseStep 2107327 = 3160991) B3160991
theorem B2369503 : Blo 1871637 2369503 := bstep (se 1 (by rfl) ⟨1777127, by rfl⟩ : syracuseStep 2369503 = 3554255) B3554255
theorem B4212719 : Blo 1871637 4212719 := bstep (se 1 (by rfl) ⟨3159539, by rfl⟩ : syracuseStep 4212719 = 6319079) B6319079
theorem B10660031 : Blo 1871637 10660031 := bstep (se 1 (by rfl) ⟨7995023, by rfl⟩ : syracuseStep 10660031 = 15990047) B15990047
theorem B4212935 : Blo 1871637 4212935 := bstep (se 1 (by rfl) ⟨3159701, by rfl⟩ : syracuseStep 4212935 = 6319403) B6319403
theorem B2107615 : Blo 1871637 2107615 := bstep (se 1 (by rfl) ⟨1580711, by rfl⟩ : syracuseStep 2107615 = 3161423) B3161423
theorem B7997723 : Blo 1871637 7997723 := bstep (se 1 (by rfl) ⟨5998292, by rfl⟩ : syracuseStep 7997723 = 11996585) B11996585
theorem B7997791 : Blo 1871637 7997791 := bstep (se 1 (by rfl) ⟨5998343, by rfl⟩ : syracuseStep 7997791 = 11996687) B11996687
theorem B4213115 : Blo 1871637 4213115 := bstep (se 1 (by rfl) ⟨3159836, by rfl⟩ : syracuseStep 4213115 = 6319673) B6319673
theorem B7113217 : Blo 1871637 7113217 := bstep (se 2 (by rfl) ⟨2667456, by rfl⟩ : syracuseStep 7113217 = 5334913) B5334913
theorem B15993395 : Blo 1871637 15993395 := bstep (se 1 (by rfl) ⟨11995046, by rfl⟩ : syracuseStep 15993395 = 23990093) B23990093
theorem B8997479 : Blo 1871637 8997479 := bstep (se 1 (by rfl) ⟨6748109, by rfl⟩ : syracuseStep 8997479 = 13496219) B13496219
theorem B4213385 : Blo 1871637 4213385 := bstep (se 2 (by rfl) ⟨1580019, by rfl⟩ : syracuseStep 4213385 = 3160039) B3160039
theorem B4213673 : Blo 1871637 4213673 := bstep (se 2 (by rfl) ⟨1580127, by rfl⟩ : syracuseStep 4213673 = 3160255) B3160255
theorem B4500431 : Blo 1871637 4500431 := bstep (se 1 (by rfl) ⟨3375323, by rfl⟩ : syracuseStep 4500431 = 6750647) B6750647
theorem B18246707 : Blo 1871637 18246707 := bstep (se 1 (by rfl) ⟨13685030, by rfl⟩ : syracuseStep 18246707 = 27370061) B27370061
theorem B7998527 : Blo 1871637 7998527 := bstep (se 1 (by rfl) ⟨5998895, by rfl⟩ : syracuseStep 7998527 = 11997791) B11997791
theorem B7998679 : Blo 1871637 7998679 := bstep (se 1 (by rfl) ⟨5999009, by rfl⟩ : syracuseStep 7998679 = 11998019) B11998019
theorem B8539501 : Blo 1871637 8539501 := bstep (se 3 (by rfl) ⟨1601156, by rfl⟩ : syracuseStep 8539501 = 3202313) B3202313
theorem B2370971 : Blo 1871637 2370971 := bstep (se 1 (by rfl) ⟨1778228, by rfl⟩ : syracuseStep 2370971 = 3556457) B3556457
theorem B4214375 : Blo 1871637 4214375 := bstep (se 1 (by rfl) ⟨3160781, by rfl⟩ : syracuseStep 4214375 = 6321563) B6321563
theorem B135147305 : Blo 1871637 135147305 := bstep (se 2 (by rfl) ⟨50680239, by rfl⟩ : syracuseStep 135147305 = 101360479) B101360479
theorem B1871679 : Blo 1871637 1871679 := bstep (se 1 (by rfl) ⟨1403759, by rfl⟩ : syracuseStep 1871679 = 2807519) B2807519
theorem B1871743 : Blo 1871637 1871743 := bstep (se 1 (by rfl) ⟨1403807, by rfl⟩ : syracuseStep 1871743 = 2807615) B2807615
theorem B1871855 : Blo 1871637 1871855 := bstep (se 1 (by rfl) ⟨1403891, by rfl⟩ : syracuseStep 1871855 = 2807783) B2807783
theorem B1871867 : Blo 1871637 1871867 := bstep (se 1 (by rfl) ⟨1403900, by rfl⟩ : syracuseStep 1871867 = 2807801) B2807801
theorem B1871935 : Blo 1871637 1871935 := bstep (se 1 (by rfl) ⟨1403951, by rfl⟩ : syracuseStep 1871935 = 2807903) B2807903
theorem B4214879 : Blo 1871637 4214879 := bstep (se 1 (by rfl) ⟨3161159, by rfl⟩ : syracuseStep 4214879 = 6322319) B6322319
theorem B1871975 : Blo 1871637 1871975 := bstep (se 1 (by rfl) ⟨1403981, by rfl⟩ : syracuseStep 1871975 = 2807963) B2807963
theorem B1871999 : Blo 1871637 1871999 := bstep (se 1 (by rfl) ⟨1403999, by rfl⟩ : syracuseStep 1871999 = 2807999) B2807999
theorem B1872027 : Blo 1871637 1872027 := bstep (se 1 (by rfl) ⟨1404020, by rfl⟩ : syracuseStep 1872027 = 2808041) B2808041
theorem B14225705 : Blo 1871637 14225705 := bstep (se 2 (by rfl) ⟨5334639, by rfl⟩ : syracuseStep 14225705 = 10669279) B10669279
theorem B1872231 : Blo 1871637 1872231 := bstep (se 1 (by rfl) ⟨1404173, by rfl⟩ : syracuseStep 1872231 = 2808347) B2808347
theorem B1872283 : Blo 1871637 1872283 := bstep (se 1 (by rfl) ⟨1404212, by rfl⟩ : syracuseStep 1872283 = 2808425) B2808425
theorem B6320591 : Blo 1871637 6320591 := bstep (se 1 (by rfl) ⟨4740443, by rfl⟩ : syracuseStep 6320591 = 9480887) B9480887
theorem B30380507 : Blo 1871637 30380507 := bstep (se 1 (by rfl) ⟨22785380, by rfl⟩ : syracuseStep 30380507 = 45570761) B45570761
theorem B10662515 : Blo 1871637 10662515 := bstep (se 1 (by rfl) ⟨7996886, by rfl⟩ : syracuseStep 10662515 = 15993773) B15993773
theorem B6746753 : Blo 1871637 6746753 := bstep (se 2 (by rfl) ⟨2530032, by rfl⟩ : syracuseStep 6746753 = 5060065) B5060065
theorem B1872635 : Blo 1871637 1872635 := bstep (se 1 (by rfl) ⟨1404476, by rfl⟩ : syracuseStep 1872635 = 2808953) B2808953
theorem B1872703 : Blo 1871637 1872703 := bstep (se 1 (by rfl) ⟨1404527, by rfl⟩ : syracuseStep 1872703 = 2809055) B2809055
theorem B4215635 : Blo 1871637 4215635 := bstep (se 1 (by rfl) ⟨3161726, by rfl⟩ : syracuseStep 4215635 = 6323453) B6323453
theorem B1872731 : Blo 1871637 1872731 := bstep (se 1 (by rfl) ⟨1404548, by rfl⟩ : syracuseStep 1872731 = 2809097) B2809097
theorem B1872799 : Blo 1871637 1872799 := bstep (se 1 (by rfl) ⟨1404599, by rfl⟩ : syracuseStep 1872799 = 2809199) B2809199
theorem B1872879 : Blo 1871637 1872879 := bstep (se 1 (by rfl) ⟨1404659, by rfl⟩ : syracuseStep 1872879 = 2809319) B2809319
theorem B1872967 : Blo 1871637 1872967 := bstep (se 1 (by rfl) ⟨1404725, by rfl⟩ : syracuseStep 1872967 = 2809451) B2809451
theorem B4740191 : Blo 1871637 4740191 := bstep (se 1 (by rfl) ⟨3555143, by rfl⟩ : syracuseStep 4740191 = 7110287) B7110287
theorem B1873051 : Blo 1871637 1873051 := bstep (se 1 (by rfl) ⟨1404788, by rfl⟩ : syracuseStep 1873051 = 2809577) B2809577
theorem B1873147 : Blo 1871637 1873147 := bstep (se 1 (by rfl) ⟨1404860, by rfl⟩ : syracuseStep 1873147 = 2809721) B2809721
theorem B5059849 : Blo 1871637 5059849 := bstep (se 2 (by rfl) ⟨1897443, by rfl⟩ : syracuseStep 5059849 = 3794887) B3794887
theorem B7107871 : Blo 1871637 7107871 := bstep (se 1 (by rfl) ⟨5330903, by rfl⟩ : syracuseStep 7107871 = 10661807) B10661807
theorem B2848063 : Blo 1871637 2848063 := bstep (se 1 (by rfl) ⟨2136047, by rfl⟩ : syracuseStep 2848063 = 4272095) B4272095
theorem B1873215 : Blo 1871637 1873215 := bstep (se 1 (by rfl) ⟨1404911, by rfl⟩ : syracuseStep 1873215 = 2809823) B2809823
theorem B10663265 : Blo 1871637 10663265 := bstep (se 2 (by rfl) ⟨3998724, by rfl⟩ : syracuseStep 10663265 = 7997449) B7997449
theorem B1873383 : Blo 1871637 1873383 := bstep (se 1 (by rfl) ⟨1405037, by rfl⟩ : syracuseStep 1873383 = 2810075) B2810075
theorem B1873391 : Blo 1871637 1873391 := bstep (se 1 (by rfl) ⟨1405043, by rfl⟩ : syracuseStep 1873391 = 2810087) B2810087
theorem B30357017 : Blo 1871637 30357017 := bstep (se 2 (by rfl) ⟨11383881, by rfl⟩ : syracuseStep 30357017 = 22767763) B22767763
theorem B161912357 : Blo 1871637 161912357 := bstep (se 4 (by rfl) ⟨15179283, by rfl⟩ : syracuseStep 161912357 = 30358567) B30358567
theorem B1873499 : Blo 1871637 1873499 := bstep (se 1 (by rfl) ⟨1405124, by rfl⟩ : syracuseStep 1873499 = 2810249) B2810249
theorem B3159695 : Blo 1871637 3159695 := bstep (se 1 (by rfl) ⟨2369771, by rfl⟩ : syracuseStep 3159695 = 4739543) B4739543
theorem B1873563 : Blo 1871637 1873563 := bstep (se 1 (by rfl) ⟨1405172, by rfl⟩ : syracuseStep 1873563 = 2810345) B2810345
theorem B14227163 : Blo 1871637 14227163 := bstep (se 1 (by rfl) ⟨10670372, by rfl⟩ : syracuseStep 14227163 = 21340745) B21340745
theorem B2807675 : Blo 1871637 2807675 := bstep (se 1 (by rfl) ⟨2105756, by rfl⟩ : syracuseStep 2807675 = 4211513) B4211513
theorem B2807711 : Blo 1871637 2807711 := bstep (se 1 (by rfl) ⟨2105783, by rfl⟩ : syracuseStep 2807711 = 4211567) B4211567
theorem B3553321 : Blo 1871637 3553321 := bstep (se 2 (by rfl) ⟨1332495, by rfl⟩ : syracuseStep 3553321 = 2664991) B2664991
theorem B2807945 : Blo 1871637 2807945 := bstep (se 2 (by rfl) ⟨1052979, by rfl⟩ : syracuseStep 2807945 = 2105959) B2105959
theorem B2808095 : Blo 1871637 2808095 := bstep (se 1 (by rfl) ⟨2106071, by rfl⟩ : syracuseStep 2808095 = 4212143) B4212143
theorem B8001823 : Blo 1871637 8001823 := bstep (se 1 (by rfl) ⟨6001367, by rfl⟩ : syracuseStep 8001823 = 12002735) B12002735
theorem B68344145 : Blo 1871637 68344145 := bstep (se 2 (by rfl) ⟨25629054, by rfl⟩ : syracuseStep 68344145 = 51258109) B51258109
theorem B5331359 : Blo 1871637 5331359 := bstep (se 1 (by rfl) ⟨3998519, by rfl⟩ : syracuseStep 5331359 = 7997039) B7997039
theorem B4741537 : Blo 1871637 4741537 := bstep (se 2 (by rfl) ⟨1778076, by rfl⟩ : syracuseStep 4741537 = 3556153) B3556153
theorem B47987153 : Blo 1871637 47987153 := bstep (se 2 (by rfl) ⟨17995182, by rfl⟩ : syracuseStep 47987153 = 35990365) B35990365
theorem B58440145 : Blo 1871637 58440145 := bstep (se 2 (by rfl) ⟨21915054, by rfl⟩ : syracuseStep 58440145 = 43830109) B43830109
theorem B3160667 : Blo 1871637 3160667 := bstep (se 1 (by rfl) ⟨2370500, by rfl⟩ : syracuseStep 3160667 = 4741001) B4741001
theorem B9484937 : Blo 1871637 9484937 := bstep (se 2 (by rfl) ⟨3556851, by rfl⟩ : syracuseStep 9484937 = 7113703) B7113703
theorem B3553951 : Blo 1871637 3553951 := bstep (se 1 (by rfl) ⟨2665463, by rfl⟩ : syracuseStep 3553951 = 5330927) B5330927
theorem B6322913 : Blo 1871637 6322913 := bstep (se 2 (by rfl) ⟨2371092, by rfl⟩ : syracuseStep 6322913 = 4742185) B4742185
theorem B3554027 : Blo 1871637 3554027 := bstep (se 1 (by rfl) ⟨2665520, by rfl⟩ : syracuseStep 3554027 = 5331041) B5331041
theorem B3554057 : Blo 1871637 3554057 := bstep (se 2 (by rfl) ⟨1332771, by rfl⟩ : syracuseStep 3554057 = 2665543) B2665543
theorem B9001783 : Blo 1871637 9001783 := bstep (se 1 (by rfl) ⟨6751337, by rfl⟩ : syracuseStep 9001783 = 13502675) B13502675
theorem B2808647 : Blo 1871637 2808647 := bstep (se 1 (by rfl) ⟨2106485, by rfl⟩ : syracuseStep 2808647 = 4212971) B4212971
theorem B14220359 : Blo 1871637 14220359 := bstep (se 1 (by rfl) ⟨10665269, by rfl⟩ : syracuseStep 14220359 = 21330539) B21330539
theorem B3161551 : Blo 1871637 3161551 := bstep (se 1 (by rfl) ⟨2371163, by rfl⟩ : syracuseStep 3161551 = 4742327) B4742327
theorem B7110119 : Blo 1871637 7110119 := bstep (se 1 (by rfl) ⟨5332589, by rfl⟩ : syracuseStep 7110119 = 10665179) B10665179
theorem B3554923 : Blo 1871637 3554923 := bstep (se 1 (by rfl) ⟨2666192, by rfl⟩ : syracuseStep 3554923 = 5332385) B5332385
theorem B7110301 : Blo 1871637 7110301 := bstep (se 3 (by rfl) ⟨1333181, by rfl⟩ : syracuseStep 7110301 = 2666363) B2666363
theorem B2809511 : Blo 1871637 2809511 := bstep (se 1 (by rfl) ⟨2107133, by rfl⟩ : syracuseStep 2809511 = 4214267) B4214267
theorem B2809631 : Blo 1871637 2809631 := bstep (se 1 (by rfl) ⟨2107223, by rfl⟩ : syracuseStep 2809631 = 4214447) B4214447
theorem B13500283 : Blo 1871637 13500283 := bstep (se 1 (by rfl) ⟨10125212, by rfl⟩ : syracuseStep 13500283 = 20250425) B20250425
theorem B3850151 : Blo 1871637 3850151 := bstep (se 1 (by rfl) ⟨2887613, by rfl⟩ : syracuseStep 3850151 = 5775227) B5775227
theorem B57663413 : Blo 1871637 57663413 := bstep (se 5 (by rfl) ⟨2702972, by rfl⟩ : syracuseStep 57663413 = 5405945) B5405945
theorem B2809919 : Blo 1871637 2809919 := bstep (se 1 (by rfl) ⟨2107439, by rfl⟩ : syracuseStep 2809919 = 4214879) B4214879
theorem B2810153 : Blo 1871637 2810153 := bstep (se 2 (by rfl) ⟨1053807, by rfl⟩ : syracuseStep 2810153 = 2107615) B2107615
theorem B5333501 : Blo 1871637 5333501 := bstep (se 3 (by rfl) ⟨1000031, by rfl⟩ : syracuseStep 5333501 = 2000063) B2000063
theorem B2810423 : Blo 1871637 2810423 := bstep (se 1 (by rfl) ⟨2107817, by rfl⟩ : syracuseStep 2810423 = 4215635) B4215635
theorem B12002377 : Blo 1871637 12002377 := bstep (se 2 (by rfl) ⟨4500891, by rfl⟩ : syracuseStep 12002377 = 9001783) B9001783
theorem B2106463 : Blo 1871637 2106463 := bstep (se 1 (by rfl) ⟨1579847, by rfl⟩ : syracuseStep 2106463 = 3159695) B3159695
theorem B31991435 : Blo 1871637 31991435 := bstep (se 1 (by rfl) ⟨23993576, by rfl⟩ : syracuseStep 31991435 = 47987153) B47987153
theorem B17991341 : Blo 1871637 17991341 := bstep (se 3 (by rfl) ⟨3373376, by rfl⟩ : syracuseStep 17991341 = 6746753) B6746753
theorem B2107111 : Blo 1871637 2107111 := bstep (se 1 (by rfl) ⟨1580333, by rfl⟩ : syracuseStep 2107111 = 3160667) B3160667
theorem B5998319 : Blo 1871637 5998319 := bstep (se 1 (by rfl) ⟨4498739, by rfl⟩ : syracuseStep 5998319 = 8997479) B8997479
theorem B2369351 : Blo 1871637 2369351 := bstep (se 1 (by rfl) ⟨1777013, by rfl⟩ : syracuseStep 2369351 = 3554027) B3554027
theorem B3000287 : Blo 1871637 3000287 := bstep (se 1 (by rfl) ⟨2250215, by rfl⟩ : syracuseStep 3000287 = 4500431) B4500431
theorem B9480239 : Blo 1871637 9480239 := bstep (se 1 (by rfl) ⟨7110179, by rfl⟩ : syracuseStep 9480239 = 14220359) B14220359
theorem B360392813 : Blo 1871637 360392813 := bstep (se 3 (by rfl) ⟨67573652, by rfl⟩ : syracuseStep 360392813 = 135147305) B135147305
theorem B9480401 : Blo 1871637 9480401 := bstep (se 2 (by rfl) ⟨3555150, by rfl⟩ : syracuseStep 9480401 = 7110301) B7110301
theorem B10267069 : Blo 1871637 10267069 := bstep (se 3 (by rfl) ⟨1925075, by rfl⟩ : syracuseStep 10267069 = 3850151) B3850151
theorem B18000377 : Blo 1871637 18000377 := bstep (se 2 (by rfl) ⟨6750141, by rfl⟩ : syracuseStep 18000377 = 13500283) B13500283
theorem B4737761 : Blo 1871637 4737761 := bstep (se 2 (by rfl) ⟨1776660, by rfl⟩ : syracuseStep 4737761 = 3553321) B3553321
theorem B2665327 : Blo 1871637 2665327 := bstep (se 1 (by rfl) ⟨1998995, by rfl⟩ : syracuseStep 2665327 = 3997991) B3997991
theorem B4213727 : Blo 1871637 4213727 := bstep (se 1 (by rfl) ⟨3160295, by rfl⟩ : syracuseStep 4213727 = 6320591) B6320591
theorem B20253671 : Blo 1871637 20253671 := bstep (se 1 (by rfl) ⟨15190253, by rfl⟩ : syracuseStep 20253671 = 30380507) B30380507
theorem B10669097 : Blo 1871637 10669097 := bstep (se 2 (by rfl) ⟨4000911, by rfl⟩ : syracuseStep 10669097 = 8001823) B8001823
theorem B9481373 : Blo 1871637 9481373 := bstep (se 3 (by rfl) ⟨1777757, by rfl⟩ : syracuseStep 9481373 = 3555515) B3555515
theorem B7998749 : Blo 1871637 7998749 := bstep (se 3 (by rfl) ⟨1499765, by rfl⟩ : syracuseStep 7998749 = 2999531) B2999531
theorem B9481697 : Blo 1871637 9481697 := bstep (se 2 (by rfl) ⟨3555636, by rfl⟩ : syracuseStep 9481697 = 7111273) B7111273
theorem B4738601 : Blo 1871637 4738601 := bstep (se 2 (by rfl) ⟨1776975, by rfl⟩ : syracuseStep 4738601 = 3553951) B3553951
theorem B20238011 : Blo 1871637 20238011 := bstep (se 1 (by rfl) ⟨15178508, by rfl⟩ : syracuseStep 20238011 = 30357017) B30357017
theorem B107941571 : Blo 1871637 107941571 := bstep (se 1 (by rfl) ⟨80956178, by rfl⟩ : syracuseStep 107941571 = 161912357) B161912357
theorem B6319835 : Blo 1871637 6319835 := bstep (se 1 (by rfl) ⟨4739876, by rfl⟩ : syracuseStep 6319835 = 9479753) B9479753
theorem B14216957 : Blo 1871637 14216957 := bstep (se 3 (by rfl) ⟨2665679, by rfl⟩ : syracuseStep 14216957 = 5331359) B5331359
theorem B1871783 : Blo 1871637 1871783 := bstep (se 1 (by rfl) ⟨1403837, by rfl⟩ : syracuseStep 1871783 = 2807675) B2807675
theorem B1871807 : Blo 1871637 1871807 := bstep (se 1 (by rfl) ⟨1403855, by rfl⟩ : syracuseStep 1871807 = 2807711) B2807711
theorem B1871963 : Blo 1871637 1871963 := bstep (se 1 (by rfl) ⟨1403972, by rfl⟩ : syracuseStep 1871963 = 2807945) B2807945
theorem B7106687 : Blo 1871637 7106687 := bstep (se 1 (by rfl) ⟨5330015, by rfl⟩ : syracuseStep 7106687 = 10660031) B10660031
theorem B1872063 : Blo 1871637 1872063 := bstep (se 1 (by rfl) ⟨1404047, by rfl⟩ : syracuseStep 1872063 = 2808095) B2808095
theorem B6746465 : Blo 1871637 6746465 := bstep (se 2 (by rfl) ⟨2529924, by rfl⟩ : syracuseStep 6746465 = 5059849) B5059849
theorem B10662263 : Blo 1871637 10662263 := bstep (se 1 (by rfl) ⟨7996697, by rfl⟩ : syracuseStep 10662263 = 15993395) B15993395
theorem B3797417 : Blo 1871637 3797417 := bstep (se 2 (by rfl) ⟨1424031, by rfl⟩ : syracuseStep 3797417 = 2848063) B2848063
theorem B9482669 : Blo 1871637 9482669 := bstep (se 3 (by rfl) ⟨1778000, by rfl⟩ : syracuseStep 9482669 = 3556001) B3556001
theorem B4215275 : Blo 1871637 4215275 := bstep (se 1 (by rfl) ⟨3161456, by rfl⟩ : syracuseStep 4215275 = 6322913) B6322913
theorem B1872431 : Blo 1871637 1872431 := bstep (se 1 (by rfl) ⟨1404323, by rfl⟩ : syracuseStep 1872431 = 2808647) B2808647
theorem B4215401 : Blo 1871637 4215401 := bstep (se 2 (by rfl) ⟨1580775, by rfl⟩ : syracuseStep 4215401 = 3161551) B3161551
theorem B4739897 : Blo 1871637 4739897 := bstep (se 2 (by rfl) ⟨1777461, by rfl⟩ : syracuseStep 4739897 = 3554923) B3554923
theorem B4740079 : Blo 1871637 4740079 := bstep (se 1 (by rfl) ⟨3555059, by rfl⟩ : syracuseStep 4740079 = 7110119) B7110119
theorem B1873007 : Blo 1871637 1873007 := bstep (se 1 (by rfl) ⟨1404755, by rfl⟩ : syracuseStep 1873007 = 2809511) B2809511
theorem B1873087 : Blo 1871637 1873087 := bstep (se 1 (by rfl) ⟨1404815, by rfl⟩ : syracuseStep 1873087 = 2809631) B2809631
theorem B38442275 : Blo 1871637 38442275 := bstep (se 1 (by rfl) ⟨28831706, by rfl⟩ : syracuseStep 38442275 = 57663413) B57663413
theorem B3159337 : Blo 1871637 3159337 := bstep (se 2 (by rfl) ⟨1184751, by rfl⟩ : syracuseStep 3159337 = 2369503) B2369503
theorem B1873375 : Blo 1871637 1873375 := bstep (se 1 (by rfl) ⟨1405031, by rfl⟩ : syracuseStep 1873375 = 2810063) B2810063
theorem B1873407 : Blo 1871637 1873407 := bstep (se 1 (by rfl) ⟨1405055, by rfl⟩ : syracuseStep 1873407 = 2810111) B2810111
theorem B9483803 : Blo 1871637 9483803 := bstep (se 1 (by rfl) ⟨7112852, by rfl⟩ : syracuseStep 9483803 = 14225705) B14225705
theorem B2807465 : Blo 1871637 2807465 := bstep (se 2 (by rfl) ⟨1052799, by rfl⟩ : syracuseStep 2807465 = 2105599) B2105599
theorem B2807471 : Blo 1871637 2807471 := bstep (se 1 (by rfl) ⟨2105603, by rfl⟩ : syracuseStep 2807471 = 4211207) B4211207
theorem B9000667 : Blo 1871637 9000667 := bstep (se 1 (by rfl) ⟨6750500, by rfl⟩ : syracuseStep 9000667 = 13501001) B13501001
theorem B7108343 : Blo 1871637 7108343 := bstep (se 1 (by rfl) ⟨5331257, by rfl⟩ : syracuseStep 7108343 = 10662515) B10662515
theorem B2807591 : Blo 1871637 2807591 := bstep (se 1 (by rfl) ⟨2105693, by rfl⟩ : syracuseStep 2807591 = 4211387) B4211387
theorem B10663721 : Blo 1871637 10663721 := bstep (se 2 (by rfl) ⟨3998895, by rfl⟩ : syracuseStep 10663721 = 7997791) B7997791
theorem B6322049 : Blo 1871637 6322049 := bstep (se 2 (by rfl) ⟨2370768, by rfl⟩ : syracuseStep 6322049 = 4741537) B4741537
theorem B77920193 : Blo 1871637 77920193 := bstep (se 2 (by rfl) ⟨29220072, by rfl⟩ : syracuseStep 77920193 = 58440145) B58440145
theorem B9484289 : Blo 1871637 9484289 := bstep (se 2 (by rfl) ⟨3556608, by rfl⟩ : syracuseStep 9484289 = 7113217) B7113217
theorem B2807849 : Blo 1871637 2807849 := bstep (se 2 (by rfl) ⟨1052943, by rfl⟩ : syracuseStep 2807849 = 2105887) B2105887
theorem B3160127 : Blo 1871637 3160127 := bstep (se 1 (by rfl) ⟨2370095, by rfl⟩ : syracuseStep 3160127 = 4740191) B4740191
theorem B2807879 : Blo 1871637 2807879 := bstep (se 1 (by rfl) ⟨2105909, by rfl⟩ : syracuseStep 2807879 = 4211819) B4211819
theorem B7108843 : Blo 1871637 7108843 := bstep (se 1 (by rfl) ⟨5331632, by rfl⟩ : syracuseStep 7108843 = 10663265) B10663265
theorem B2808191 : Blo 1871637 2808191 := bstep (se 1 (by rfl) ⟨2106143, by rfl⟩ : syracuseStep 2808191 = 4212287) B4212287
theorem B6322589 : Blo 1871637 6322589 := bstep (se 3 (by rfl) ⟨1185485, by rfl⟩ : syracuseStep 6322589 = 2370971) B2370971
theorem B2808263 : Blo 1871637 2808263 := bstep (se 1 (by rfl) ⟨2106197, by rfl⟩ : syracuseStep 2808263 = 4212395) B4212395
theorem B9484775 : Blo 1871637 9484775 := bstep (se 1 (by rfl) ⟨7113581, by rfl⟩ : syracuseStep 9484775 = 14227163) B14227163
theorem B2808479 : Blo 1871637 2808479 := bstep (se 1 (by rfl) ⟨2106359, by rfl⟩ : syracuseStep 2808479 = 4212719) B4212719
theorem B76897025 : Blo 1871637 76897025 := bstep (se 2 (by rfl) ⟨28836384, by rfl⟩ : syracuseStep 76897025 = 57672769) B57672769
theorem B2808623 : Blo 1871637 2808623 := bstep (se 1 (by rfl) ⟨2106467, by rfl⟩ : syracuseStep 2808623 = 4212935) B4212935
theorem B5331815 : Blo 1871637 5331815 := bstep (se 1 (by rfl) ⟨3998861, by rfl⟩ : syracuseStep 5331815 = 7997723) B7997723
theorem B2808713 : Blo 1871637 2808713 := bstep (se 2 (by rfl) ⟨1053267, by rfl⟩ : syracuseStep 2808713 = 2106535) B2106535
theorem B45562763 : Blo 1871637 45562763 := bstep (se 1 (by rfl) ⟨34172072, by rfl⟩ : syracuseStep 45562763 = 68344145) B68344145
theorem B2808743 : Blo 1871637 2808743 := bstep (se 1 (by rfl) ⟨2106557, by rfl⟩ : syracuseStep 2808743 = 4213115) B4213115
theorem B10664905 : Blo 1871637 10664905 := bstep (se 2 (by rfl) ⟨3999339, by rfl⟩ : syracuseStep 10664905 = 7998679) B7998679
theorem B9477161 : Blo 1871637 9477161 := bstep (se 2 (by rfl) ⟨3553935, by rfl⟩ : syracuseStep 9477161 = 7107871) B7107871
theorem B2808923 : Blo 1871637 2808923 := bstep (se 1 (by rfl) ⟨2106692, by rfl⟩ : syracuseStep 2808923 = 4213385) B4213385
theorem B6323291 : Blo 1871637 6323291 := bstep (se 1 (by rfl) ⟨4742468, by rfl⟩ : syracuseStep 6323291 = 9484937) B9484937
theorem B11386001 : Blo 1871637 11386001 := bstep (se 2 (by rfl) ⟨4269750, by rfl⟩ : syracuseStep 11386001 = 8539501) B8539501
theorem B2809115 : Blo 1871637 2809115 := bstep (se 1 (by rfl) ⟨2106836, by rfl⟩ : syracuseStep 2809115 = 4213673) B4213673
theorem B9477485 : Blo 1871637 9477485 := bstep (se 3 (by rfl) ⟨1777028, by rfl⟩ : syracuseStep 9477485 = 3554057) B3554057
theorem B12164471 : Blo 1871637 12164471 := bstep (se 1 (by rfl) ⟨9123353, by rfl⟩ : syracuseStep 12164471 = 18246707) B18246707
theorem B5332351 : Blo 1871637 5332351 := bstep (se 1 (by rfl) ⟨3999263, by rfl⟩ : syracuseStep 5332351 = 7998527) B7998527
theorem B2809583 : Blo 1871637 2809583 := bstep (se 1 (by rfl) ⟨2107187, by rfl⟩ : syracuseStep 2809583 = 4214375) B4214375
theorem B5332841 : Blo 1871637 5332841 := bstep (se 2 (by rfl) ⟨1999815, by rfl⟩ : syracuseStep 5332841 = 3999631) B3999631
theorem B2809769 : Blo 1871637 2809769 := bstep (se 2 (by rfl) ⟨1053663, by rfl⟩ : syracuseStep 2809769 = 2107327) B2107327
theorem B4497643 : Blo 1871637 4497643 := bstep (se 1 (by rfl) ⟨3373232, by rfl⟩ : syracuseStep 4497643 = 6746465) B6746465
theorem B2531611 : Blo 1871637 2531611 := bstep (se 1 (by rfl) ⟨1898708, by rfl⟩ : syracuseStep 2531611 = 3797417) B3797417
theorem B9478457 : Blo 1871637 9478457 := bstep (se 2 (by rfl) ⟨3554421, by rfl⟩ : syracuseStep 9478457 = 7108843) B7108843
theorem B2810183 : Blo 1871637 2810183 := bstep (se 1 (by rfl) ⟨2107637, by rfl⟩ : syracuseStep 2810183 = 4215275) B4215275
theorem B3555667 : Blo 1871637 3555667 := bstep (se 1 (by rfl) ⟨2666750, by rfl⟩ : syracuseStep 3555667 = 5333501) B5333501
theorem B2810267 : Blo 1871637 2810267 := bstep (se 1 (by rfl) ⟨2107700, by rfl⟩ : syracuseStep 2810267 = 4215401) B4215401
theorem B13689425 : Blo 1871637 13689425 := bstep (se 2 (by rfl) ⟨5133534, by rfl⟩ : syracuseStep 13689425 = 10267069) B10267069
theorem B11994227 : Blo 1871637 11994227 := bstep (se 1 (by rfl) ⟨8995670, by rfl⟩ : syracuseStep 11994227 = 17991341) B17991341
theorem B3998879 : Blo 1871637 3998879 := bstep (se 1 (by rfl) ⟨2999159, by rfl⟩ : syracuseStep 3998879 = 5998319) B5998319
theorem B51946795 : Blo 1871637 51946795 := bstep (se 1 (by rfl) ⟨38960096, by rfl⟩ : syracuseStep 51946795 = 77920193) B77920193
theorem B2106751 : Blo 1871637 2106751 := bstep (se 1 (by rfl) ⟨1580063, by rfl⟩ : syracuseStep 2106751 = 3160127) B3160127
theorem B4212449 : Blo 1871637 4212449 := bstep (se 2 (by rfl) ⟨1579668, by rfl⟩ : syracuseStep 4212449 = 3159337) B3159337
theorem B13502447 : Blo 1871637 13502447 := bstep (se 1 (by rfl) ⟨10126835, by rfl⟩ : syracuseStep 13502447 = 20253671) B20253671
theorem B6318107 : Blo 1871637 6318107 := bstep (se 1 (by rfl) ⟨4738580, by rfl⟩ : syracuseStep 6318107 = 9477161) B9477161
theorem B7112731 : Blo 1871637 7112731 := bstep (se 1 (by rfl) ⟨5334548, by rfl⟩ : syracuseStep 7112731 = 10669097) B10669097
theorem B6318269 : Blo 1871637 6318269 := bstep (se 3 (by rfl) ⟨1184675, by rfl⟩ : syracuseStep 6318269 = 2369351) B2369351
theorem B6318323 : Blo 1871637 6318323 := bstep (se 1 (by rfl) ⟨4738742, by rfl⟩ : syracuseStep 6318323 = 9477485) B9477485
theorem B71961047 : Blo 1871637 71961047 := bstep (se 1 (by rfl) ⟨53970785, by rfl⟩ : syracuseStep 71961047 = 107941571) B107941571
theorem B4213223 : Blo 1871637 4213223 := bstep (se 1 (by rfl) ⟨3159917, by rfl⟩ : syracuseStep 4213223 = 6319835) B6319835
theorem B4737791 : Blo 1871637 4737791 := bstep (se 1 (by rfl) ⟨3553343, by rfl⟩ : syracuseStep 4737791 = 7106687) B7106687
theorem B25628183 : Blo 1871637 25628183 := bstep (se 1 (by rfl) ⟨19221137, by rfl⟩ : syracuseStep 25628183 = 38442275) B38442275
theorem B21327623 : Blo 1871637 21327623 := bstep (se 1 (by rfl) ⟨15995717, by rfl⟩ : syracuseStep 21327623 = 31991435) B31991435
theorem B1871643 : Blo 1871637 1871643 := bstep (se 1 (by rfl) ⟨1403732, by rfl⟩ : syracuseStep 1871643 = 2807465) B2807465
theorem B1871647 : Blo 1871637 1871647 := bstep (se 1 (by rfl) ⟨1403735, by rfl⟩ : syracuseStep 1871647 = 2807471) B2807471
theorem B4738895 : Blo 1871637 4738895 := bstep (se 1 (by rfl) ⟨3554171, by rfl⟩ : syracuseStep 4738895 = 7108343) B7108343
theorem B1871727 : Blo 1871637 1871727 := bstep (se 1 (by rfl) ⟨1403795, by rfl⟩ : syracuseStep 1871727 = 2807591) B2807591
theorem B4214699 : Blo 1871637 4214699 := bstep (se 1 (by rfl) ⟨3161024, by rfl⟩ : syracuseStep 4214699 = 6322049) B6322049
theorem B6320105 : Blo 1871637 6320105 := bstep (se 2 (by rfl) ⟨2370039, by rfl⟩ : syracuseStep 6320105 = 4740079) B4740079
theorem B1871899 : Blo 1871637 1871899 := bstep (se 1 (by rfl) ⟨1403924, by rfl⟩ : syracuseStep 1871899 = 2807849) B2807849
theorem B6320159 : Blo 1871637 6320159 := bstep (se 1 (by rfl) ⟨4740119, by rfl⟩ : syracuseStep 6320159 = 9480239) B9480239
theorem B1871919 : Blo 1871637 1871919 := bstep (se 1 (by rfl) ⟨1403939, by rfl⟩ : syracuseStep 1871919 = 2807879) B2807879
theorem B16003169 : Blo 1871637 16003169 := bstep (se 2 (by rfl) ⟨6001188, by rfl⟩ : syracuseStep 16003169 = 12002377) B12002377
theorem B6320267 : Blo 1871637 6320267 := bstep (se 1 (by rfl) ⟨4740200, by rfl⟩ : syracuseStep 6320267 = 9480401) B9480401
theorem B1872127 : Blo 1871637 1872127 := bstep (se 1 (by rfl) ⟨1404095, by rfl⟩ : syracuseStep 1872127 = 2808191) B2808191
theorem B4215059 : Blo 1871637 4215059 := bstep (se 1 (by rfl) ⟨3161294, by rfl⟩ : syracuseStep 4215059 = 6322589) B6322589
theorem B1872175 : Blo 1871637 1872175 := bstep (se 1 (by rfl) ⟨1404131, by rfl⟩ : syracuseStep 1872175 = 2808263) B2808263
theorem B1872319 : Blo 1871637 1872319 := bstep (se 1 (by rfl) ⟨1404239, by rfl⟩ : syracuseStep 1872319 = 2808479) B2808479
theorem B3158507 : Blo 1871637 3158507 := bstep (se 1 (by rfl) ⟨2368880, by rfl⟩ : syracuseStep 3158507 = 4737761) B4737761
theorem B1872415 : Blo 1871637 1872415 := bstep (se 1 (by rfl) ⟨1404311, by rfl⟩ : syracuseStep 1872415 = 2808623) B2808623
theorem B1872475 : Blo 1871637 1872475 := bstep (se 1 (by rfl) ⟨1404356, by rfl⟩ : syracuseStep 1872475 = 2808713) B2808713
theorem B1872495 : Blo 1871637 1872495 := bstep (se 1 (by rfl) ⟨1404371, by rfl⟩ : syracuseStep 1872495 = 2808743) B2808743
theorem B1872615 : Blo 1871637 1872615 := bstep (se 1 (by rfl) ⟨1404461, by rfl⟩ : syracuseStep 1872615 = 2808923) B2808923
theorem B4215527 : Blo 1871637 4215527 := bstep (se 1 (by rfl) ⟨3161645, by rfl⟩ : syracuseStep 4215527 = 6323291) B6323291
theorem B7590667 : Blo 1871637 7590667 := bstep (se 1 (by rfl) ⟨5693000, by rfl⟩ : syracuseStep 7590667 = 11386001) B11386001
theorem B6320915 : Blo 1871637 6320915 := bstep (se 1 (by rfl) ⟨4740686, by rfl⟩ : syracuseStep 6320915 = 9481373) B9481373
theorem B1872743 : Blo 1871637 1872743 := bstep (se 1 (by rfl) ⟨1404557, by rfl⟩ : syracuseStep 1872743 = 2809115) B2809115
theorem B6321131 : Blo 1871637 6321131 := bstep (se 1 (by rfl) ⟨4740848, by rfl⟩ : syracuseStep 6321131 = 9481697) B9481697
theorem B3159067 : Blo 1871637 3159067 := bstep (se 1 (by rfl) ⟨2369300, by rfl⟩ : syracuseStep 3159067 = 4738601) B4738601
theorem B1873055 : Blo 1871637 1873055 := bstep (se 1 (by rfl) ⟨1404791, by rfl⟩ : syracuseStep 1873055 = 2809583) B2809583
theorem B8000765 : Blo 1871637 8000765 := bstep (se 3 (by rfl) ⟨1500143, by rfl⟩ : syracuseStep 8000765 = 3000287) B3000287
theorem B1873179 : Blo 1871637 1873179 := bstep (se 1 (by rfl) ⟨1404884, by rfl⟩ : syracuseStep 1873179 = 2809769) B2809769
theorem B1873279 : Blo 1871637 1873279 := bstep (se 1 (by rfl) ⟨1404959, by rfl⟩ : syracuseStep 1873279 = 2809919) B2809919
theorem B1873435 : Blo 1871637 1873435 := bstep (se 1 (by rfl) ⟨1405076, by rfl⟩ : syracuseStep 1873435 = 2810153) B2810153
theorem B7108175 : Blo 1871637 7108175 := bstep (se 1 (by rfl) ⟨5331131, by rfl⟩ : syracuseStep 7108175 = 10662263) B10662263
theorem B6321779 : Blo 1871637 6321779 := bstep (se 1 (by rfl) ⟨4741334, by rfl⟩ : syracuseStep 6321779 = 9482669) B9482669
theorem B1873615 : Blo 1871637 1873615 := bstep (se 1 (by rfl) ⟨1405211, by rfl⟩ : syracuseStep 1873615 = 2810423) B2810423
theorem B3159931 : Blo 1871637 3159931 := bstep (se 1 (by rfl) ⟨2369948, by rfl⟩ : syracuseStep 3159931 = 4739897) B4739897
theorem B6322535 : Blo 1871637 6322535 := bstep (se 1 (by rfl) ⟨4741901, by rfl⟩ : syracuseStep 6322535 = 9483803) B9483803
theorem B3553769 : Blo 1871637 3553769 := bstep (se 2 (by rfl) ⟨1332663, by rfl⟩ : syracuseStep 3553769 = 2665327) B2665327
theorem B7109147 : Blo 1871637 7109147 := bstep (se 1 (by rfl) ⟨5331860, by rfl⟩ : syracuseStep 7109147 = 10663721) B10663721
theorem B14219873 : Blo 1871637 14219873 := bstep (se 2 (by rfl) ⟨5332452, by rfl⟩ : syracuseStep 14219873 = 10664905) B10664905
theorem B6322859 : Blo 1871637 6322859 := bstep (se 1 (by rfl) ⟨4742144, by rfl⟩ : syracuseStep 6322859 = 9484289) B9484289
theorem B240261875 : Blo 1871637 240261875 := bstep (se 1 (by rfl) ⟨180196406, by rfl⟩ : syracuseStep 240261875 = 360392813) B360392813
theorem B2808617 : Blo 1871637 2808617 := bstep (se 2 (by rfl) ⟨1053231, by rfl⟩ : syracuseStep 2808617 = 2106463) B2106463
theorem B6323183 : Blo 1871637 6323183 := bstep (se 1 (by rfl) ⟨4742387, by rfl⟩ : syracuseStep 6323183 = 9484775) B9484775
theorem B12000251 : Blo 1871637 12000251 := bstep (se 1 (by rfl) ⟨9000188, by rfl⟩ : syracuseStep 12000251 = 18000377) B18000377
theorem B7109801 : Blo 1871637 7109801 := bstep (se 2 (by rfl) ⟨2666175, by rfl⟩ : syracuseStep 7109801 = 5332351) B5332351
theorem B51264683 : Blo 1871637 51264683 := bstep (se 1 (by rfl) ⟨38448512, by rfl⟩ : syracuseStep 51264683 = 76897025) B76897025
theorem B3554543 : Blo 1871637 3554543 := bstep (se 1 (by rfl) ⟨2665907, by rfl⟩ : syracuseStep 3554543 = 5331815) B5331815
theorem B30375175 : Blo 1871637 30375175 := bstep (se 1 (by rfl) ⟨22781381, by rfl⟩ : syracuseStep 30375175 = 45562763) B45562763
theorem B2809151 : Blo 1871637 2809151 := bstep (se 1 (by rfl) ⟨2106863, by rfl⟩ : syracuseStep 2809151 = 4213727) B4213727
theorem B5332499 : Blo 1871637 5332499 := bstep (se 1 (by rfl) ⟨3999374, by rfl⟩ : syracuseStep 5332499 = 7998749) B7998749
theorem B8109647 : Blo 1871637 8109647 := bstep (se 1 (by rfl) ⟨6082235, by rfl⟩ : syracuseStep 8109647 = 12164471) B12164471
theorem B12000889 : Blo 1871637 12000889 := bstep (se 2 (by rfl) ⟨4500333, by rfl⟩ : syracuseStep 12000889 = 9000667) B9000667
theorem B2809481 : Blo 1871637 2809481 := bstep (se 2 (by rfl) ⟨1053555, by rfl⟩ : syracuseStep 2809481 = 2107111) B2107111
theorem B13492007 : Blo 1871637 13492007 := bstep (se 1 (by rfl) ⟨10119005, by rfl⟩ : syracuseStep 13492007 = 20238011) B20238011
theorem B9477971 : Blo 1871637 9477971 := bstep (se 1 (by rfl) ⟨7108478, by rfl⟩ : syracuseStep 9477971 = 14216957) B14216957
theorem B3555227 : Blo 1871637 3555227 := bstep (se 1 (by rfl) ⟨2666420, by rfl⟩ : syracuseStep 3555227 = 5332841) B5332841
theorem B2810039 : Blo 1871637 2810039 := bstep (se 1 (by rfl) ⟨2107529, by rfl⟩ : syracuseStep 2810039 = 4215059) B4215059
theorem B5996857 : Blo 1871637 5996857 := bstep (se 2 (by rfl) ⟨2248821, by rfl⟩ : syracuseStep 5996857 = 4497643) B4497643
theorem B2105671 : Blo 1871637 2105671 := bstep (se 1 (by rfl) ⟨1579253, by rfl⟩ : syracuseStep 2105671 = 3158507) B3158507
theorem B3375481 : Blo 1871637 3375481 := bstep (se 2 (by rfl) ⟨1265805, by rfl⟩ : syracuseStep 3375481 = 2531611) B2531611
theorem B9126283 : Blo 1871637 9126283 := bstep (se 1 (by rfl) ⟨6844712, by rfl⟩ : syracuseStep 9126283 = 13689425) B13689425
theorem B2810351 : Blo 1871637 2810351 := bstep (se 1 (by rfl) ⟨2107763, by rfl⟩ : syracuseStep 2810351 = 4215527) B4215527
theorem B9478781 : Blo 1871637 9478781 := bstep (se 3 (by rfl) ⟨1777271, by rfl⟩ : syracuseStep 9478781 = 3554543) B3554543
theorem B7996151 : Blo 1871637 7996151 := bstep (se 1 (by rfl) ⟨5997113, by rfl⟩ : syracuseStep 7996151 = 11994227) B11994227
theorem B5333843 : Blo 1871637 5333843 := bstep (se 1 (by rfl) ⟨4000382, by rfl⟩ : syracuseStep 5333843 = 8000765) B8000765
theorem B4212071 : Blo 1871637 4212071 := bstep (se 1 (by rfl) ⟨3159053, by rfl⟩ : syracuseStep 4212071 = 6318107) B6318107
theorem B4212089 : Blo 1871637 4212089 := bstep (se 2 (by rfl) ⟨1579533, by rfl⟩ : syracuseStep 4212089 = 3159067) B3159067
theorem B4212179 : Blo 1871637 4212179 := bstep (se 1 (by rfl) ⟨3159134, by rfl⟩ : syracuseStep 4212179 = 6318269) B6318269
theorem B4212215 : Blo 1871637 4212215 := bstep (se 1 (by rfl) ⟨3159161, by rfl⟩ : syracuseStep 4212215 = 6318323) B6318323
theorem B47974031 : Blo 1871637 47974031 := bstep (se 1 (by rfl) ⟨35980523, by rfl⟩ : syracuseStep 47974031 = 71961047) B71961047
theorem B2369179 : Blo 1871637 2369179 := bstep (se 1 (by rfl) ⟨1776884, by rfl⟩ : syracuseStep 2369179 = 3553769) B3553769
theorem B9479915 : Blo 1871637 9479915 := bstep (se 1 (by rfl) ⟨7109936, by rfl⟩ : syracuseStep 9479915 = 14219873) B14219873
theorem B16001185 : Blo 1871637 16001185 := bstep (se 2 (by rfl) ⟨6000444, by rfl⟩ : syracuseStep 16001185 = 12000889) B12000889
theorem B4213241 : Blo 1871637 4213241 := bstep (se 2 (by rfl) ⟨1579965, by rfl⟩ : syracuseStep 4213241 = 3159931) B3159931
theorem B6318647 : Blo 1871637 6318647 := bstep (se 1 (by rfl) ⟨4738985, by rfl⟩ : syracuseStep 6318647 = 9477971) B9477971
theorem B2370151 : Blo 1871637 2370151 := bstep (se 1 (by rfl) ⟨1777613, by rfl⟩ : syracuseStep 2370151 = 3555227) B3555227
theorem B4213403 : Blo 1871637 4213403 := bstep (se 1 (by rfl) ⟨3160052, by rfl⟩ : syracuseStep 4213403 = 6320105) B6320105
theorem B4213439 : Blo 1871637 4213439 := bstep (se 1 (by rfl) ⟨3160079, by rfl⟩ : syracuseStep 4213439 = 6320159) B6320159
theorem B10668779 : Blo 1871637 10668779 := bstep (se 1 (by rfl) ⟨8001584, by rfl⟩ : syracuseStep 10668779 = 16003169) B16003169
theorem B4213511 : Blo 1871637 4213511 := bstep (se 1 (by rfl) ⟨3160133, by rfl⟩ : syracuseStep 4213511 = 6320267) B6320267
theorem B6318971 : Blo 1871637 6318971 := bstep (se 1 (by rfl) ⟨4739228, by rfl⟩ : syracuseStep 6318971 = 9478457) B9478457
theorem B4213943 : Blo 1871637 4213943 := bstep (se 1 (by rfl) ⟨3160457, by rfl⟩ : syracuseStep 4213943 = 6320915) B6320915
theorem B4214087 : Blo 1871637 4214087 := bstep (se 1 (by rfl) ⟨3160565, by rfl⟩ : syracuseStep 4214087 = 6321131) B6321131
theorem B2665919 : Blo 1871637 2665919 := bstep (se 1 (by rfl) ⟨1999439, by rfl⟩ : syracuseStep 2665919 = 3998879) B3998879
theorem B10120889 : Blo 1871637 10120889 := bstep (se 2 (by rfl) ⟨3795333, by rfl⟩ : syracuseStep 10120889 = 7590667) B7590667
theorem B4738783 : Blo 1871637 4738783 := bstep (se 1 (by rfl) ⟨3554087, by rfl⟩ : syracuseStep 4738783 = 7108175) B7108175
theorem B4214519 : Blo 1871637 4214519 := bstep (se 1 (by rfl) ⟨3160889, by rfl⟩ : syracuseStep 4214519 = 6321779) B6321779
theorem B4215023 : Blo 1871637 4215023 := bstep (se 1 (by rfl) ⟨3161267, by rfl⟩ : syracuseStep 4215023 = 6322535) B6322535
theorem B4739431 : Blo 1871637 4739431 := bstep (se 1 (by rfl) ⟨3554573, by rfl⟩ : syracuseStep 4739431 = 7109147) B7109147
theorem B4215239 : Blo 1871637 4215239 := bstep (se 1 (by rfl) ⟨3161429, by rfl⟩ : syracuseStep 4215239 = 6322859) B6322859
theorem B160174583 : Blo 1871637 160174583 := bstep (se 1 (by rfl) ⟨120130937, by rfl⟩ : syracuseStep 160174583 = 240261875) B240261875
theorem B3158527 : Blo 1871637 3158527 := bstep (se 1 (by rfl) ⟨2368895, by rfl⟩ : syracuseStep 3158527 = 4737791) B4737791
theorem B1872411 : Blo 1871637 1872411 := bstep (se 1 (by rfl) ⟨1404308, by rfl⟩ : syracuseStep 1872411 = 2808617) B2808617
theorem B4215455 : Blo 1871637 4215455 := bstep (se 1 (by rfl) ⟨3161591, by rfl⟩ : syracuseStep 4215455 = 6323183) B6323183
theorem B8000167 : Blo 1871637 8000167 := bstep (se 1 (by rfl) ⟨6000125, by rfl⟩ : syracuseStep 8000167 = 12000251) B12000251
theorem B4739867 : Blo 1871637 4739867 := bstep (se 1 (by rfl) ⟨3554900, by rfl⟩ : syracuseStep 4739867 = 7109801) B7109801
theorem B1872767 : Blo 1871637 1872767 := bstep (se 1 (by rfl) ⟨1404575, by rfl⟩ : syracuseStep 1872767 = 2809151) B2809151
theorem B17085455 : Blo 1871637 17085455 := bstep (se 1 (by rfl) ⟨12814091, by rfl⟩ : syracuseStep 17085455 = 25628183) B25628183
theorem B1872987 : Blo 1871637 1872987 := bstep (se 1 (by rfl) ⟨1404740, by rfl⟩ : syracuseStep 1872987 = 2809481) B2809481
theorem B14218415 : Blo 1871637 14218415 := bstep (se 1 (by rfl) ⟨10663811, by rfl⟩ : syracuseStep 14218415 = 21327623) B21327623
theorem B3159263 : Blo 1871637 3159263 := bstep (se 1 (by rfl) ⟨2369447, by rfl⟩ : syracuseStep 3159263 = 4738895) B4738895
theorem B9483641 : Blo 1871637 9483641 := bstep (se 2 (by rfl) ⟨3556365, by rfl⟩ : syracuseStep 9483641 = 7112731) B7112731
theorem B1873455 : Blo 1871637 1873455 := bstep (se 1 (by rfl) ⟨1405091, by rfl⟩ : syracuseStep 1873455 = 2810183) B2810183
theorem B1873511 : Blo 1871637 1873511 := bstep (se 1 (by rfl) ⟨1405133, by rfl⟩ : syracuseStep 1873511 = 2810267) B2810267
theorem B4740889 : Blo 1871637 4740889 := bstep (se 2 (by rfl) ⟨1777833, by rfl⟩ : syracuseStep 4740889 = 3555667) B3555667
theorem B2808299 : Blo 1871637 2808299 := bstep (se 1 (by rfl) ⟨2106224, by rfl⟩ : syracuseStep 2808299 = 4212449) B4212449
theorem B9001631 : Blo 1871637 9001631 := bstep (se 1 (by rfl) ⟨6751223, by rfl⟩ : syracuseStep 9001631 = 13502447) B13502447
theorem B2808815 : Blo 1871637 2808815 := bstep (se 1 (by rfl) ⟨2106611, by rfl⟩ : syracuseStep 2808815 = 4213223) B4213223
theorem B40500233 : Blo 1871637 40500233 := bstep (se 2 (by rfl) ⟨15187587, by rfl⟩ : syracuseStep 40500233 = 30375175) B30375175
theorem B69262393 : Blo 1871637 69262393 := bstep (se 2 (by rfl) ⟨25973397, by rfl⟩ : syracuseStep 69262393 = 51946795) B51946795
theorem B2809001 : Blo 1871637 2809001 := bstep (se 2 (by rfl) ⟨1053375, by rfl⟩ : syracuseStep 2809001 = 2106751) B2106751
theorem B34176455 : Blo 1871637 34176455 := bstep (se 1 (by rfl) ⟨25632341, by rfl⟩ : syracuseStep 34176455 = 51264683) B51264683
theorem B3554999 : Blo 1871637 3554999 := bstep (se 1 (by rfl) ⟨2666249, by rfl⟩ : syracuseStep 3554999 = 5332499) B5332499
theorem B5406431 : Blo 1871637 5406431 := bstep (se 1 (by rfl) ⟨4054823, by rfl⟩ : syracuseStep 5406431 = 8109647) B8109647
theorem B8994671 : Blo 1871637 8994671 := bstep (se 1 (by rfl) ⟨6746003, by rfl⟩ : syracuseStep 8994671 = 13492007) B13492007
theorem B2809799 : Blo 1871637 2809799 := bstep (se 1 (by rfl) ⟨2107349, by rfl⟩ : syracuseStep 2809799 = 4214699) B4214699
theorem B2810015 : Blo 1871637 2810015 := bstep (se 1 (by rfl) ⟨2107511, by rfl⟩ : syracuseStep 2810015 = 4215023) B4215023
theorem B2810159 : Blo 1871637 2810159 := bstep (se 1 (by rfl) ⟨2107619, by rfl⟩ : syracuseStep 2810159 = 4215239) B4215239
theorem B106783055 : Blo 1871637 106783055 := bstep (se 1 (by rfl) ⟨80087291, by rfl⟩ : syracuseStep 106783055 = 160174583) B160174583
theorem B7995809 : Blo 1871637 7995809 := bstep (se 2 (by rfl) ⟨2998428, by rfl⟩ : syracuseStep 7995809 = 5996857) B5996857
theorem B2810303 : Blo 1871637 2810303 := bstep (se 1 (by rfl) ⟨2107727, by rfl⟩ : syracuseStep 2810303 = 4215455) B4215455
theorem B3555895 : Blo 1871637 3555895 := bstep (se 1 (by rfl) ⟨2666921, by rfl⟩ : syracuseStep 3555895 = 5333843) B5333843
theorem B4211369 : Blo 1871637 4211369 := bstep (se 2 (by rfl) ⟨1579263, by rfl⟩ : syracuseStep 4211369 = 3158527) B3158527
theorem B9478943 : Blo 1871637 9478943 := bstep (se 1 (by rfl) ⟨7109207, by rfl⟩ : syracuseStep 9478943 = 14218415) B14218415
theorem B2106175 : Blo 1871637 2106175 := bstep (se 1 (by rfl) ⟨1579631, by rfl⟩ : syracuseStep 2106175 = 3159263) B3159263
theorem B10666889 : Blo 1871637 10666889 := bstep (se 2 (by rfl) ⟨4000083, by rfl⟩ : syracuseStep 10666889 = 8000167) B8000167
theorem B31982687 : Blo 1871637 31982687 := bstep (se 1 (by rfl) ⟨23987015, by rfl⟩ : syracuseStep 31982687 = 47974031) B47974031
theorem B92349857 : Blo 1871637 92349857 := bstep (se 2 (by rfl) ⟨34631196, by rfl⟩ : syracuseStep 92349857 = 69262393) B69262393
theorem B4212431 : Blo 1871637 4212431 := bstep (se 1 (by rfl) ⟨3159323, by rfl⟩ : syracuseStep 4212431 = 6318647) B6318647
theorem B7112519 : Blo 1871637 7112519 := bstep (se 1 (by rfl) ⟨5334389, by rfl⟩ : syracuseStep 7112519 = 10668779) B10668779
theorem B4212647 : Blo 1871637 4212647 := bstep (se 1 (by rfl) ⟨3159485, by rfl⟩ : syracuseStep 4212647 = 6318971) B6318971
theorem B6318377 : Blo 1871637 6318377 := bstep (se 2 (by rfl) ⟨2369391, by rfl⟩ : syracuseStep 6318377 = 4738783) B4738783
theorem B22784303 : Blo 1871637 22784303 := bstep (se 1 (by rfl) ⟨17088227, by rfl⟩ : syracuseStep 22784303 = 34176455) B34176455
theorem B2369999 : Blo 1871637 2369999 := bstep (se 1 (by rfl) ⟨1777499, by rfl⟩ : syracuseStep 2369999 = 3554999) B3554999
theorem B21334913 : Blo 1871637 21334913 := bstep (se 2 (by rfl) ⟨8000592, by rfl⟩ : syracuseStep 21334913 = 16001185) B16001185
theorem B6319187 : Blo 1871637 6319187 := bstep (se 1 (by rfl) ⟨4739390, by rfl⟩ : syracuseStep 6319187 = 9478781) B9478781
theorem B6319241 : Blo 1871637 6319241 := bstep (se 2 (by rfl) ⟨2369715, by rfl⟩ : syracuseStep 6319241 = 4739431) B4739431
theorem B4500641 : Blo 1871637 4500641 := bstep (se 2 (by rfl) ⟨1687740, by rfl⟩ : syracuseStep 4500641 = 3375481) B3375481
theorem B12168377 : Blo 1871637 12168377 := bstep (se 2 (by rfl) ⟨4563141, by rfl⟩ : syracuseStep 12168377 = 9126283) B9126283
theorem B11390303 : Blo 1871637 11390303 := bstep (se 1 (by rfl) ⟨8542727, by rfl⟩ : syracuseStep 11390303 = 17085455) B17085455
theorem B6319943 : Blo 1871637 6319943 := bstep (se 1 (by rfl) ⟨4739957, by rfl⟩ : syracuseStep 6319943 = 9479915) B9479915
theorem B1872199 : Blo 1871637 1872199 := bstep (se 1 (by rfl) ⟨1404149, by rfl⟩ : syracuseStep 1872199 = 2808299) B2808299
theorem B6001087 : Blo 1871637 6001087 := bstep (se 1 (by rfl) ⟨4500815, by rfl⟩ : syracuseStep 6001087 = 9001631) B9001631
theorem B26989037 : Blo 1871637 26989037 := bstep (se 3 (by rfl) ⟨5060444, by rfl⟩ : syracuseStep 26989037 = 10120889) B10120889
theorem B1872543 : Blo 1871637 1872543 := bstep (se 1 (by rfl) ⟨1404407, by rfl⟩ : syracuseStep 1872543 = 2808815) B2808815
theorem B1872667 : Blo 1871637 1872667 := bstep (se 1 (by rfl) ⟨1404500, by rfl⟩ : syracuseStep 1872667 = 2809001) B2809001
theorem B3158905 : Blo 1871637 3158905 := bstep (se 2 (by rfl) ⟨1184589, by rfl⟩ : syracuseStep 3158905 = 2369179) B2369179
theorem B6321185 : Blo 1871637 6321185 := bstep (se 2 (by rfl) ⟨2370444, by rfl⟩ : syracuseStep 6321185 = 4740889) B4740889
theorem B1873199 : Blo 1871637 1873199 := bstep (se 1 (by rfl) ⟨1404899, by rfl⟩ : syracuseStep 1873199 = 2809799) B2809799
theorem B1873359 : Blo 1871637 1873359 := bstep (se 1 (by rfl) ⟨1405019, by rfl⟩ : syracuseStep 1873359 = 2810039) B2810039
theorem B1873567 : Blo 1871637 1873567 := bstep (se 1 (by rfl) ⟨1405175, by rfl⟩ : syracuseStep 1873567 = 2810351) B2810351
theorem B2807561 : Blo 1871637 2807561 := bstep (se 2 (by rfl) ⟨1052835, by rfl⟩ : syracuseStep 2807561 = 2105671) B2105671
theorem B5330767 : Blo 1871637 5330767 := bstep (se 1 (by rfl) ⟨3998075, by rfl⟩ : syracuseStep 5330767 = 7996151) B7996151
theorem B3159911 : Blo 1871637 3159911 := bstep (se 1 (by rfl) ⟨2369933, by rfl⟩ : syracuseStep 3159911 = 4739867) B4739867
theorem B3160201 : Blo 1871637 3160201 := bstep (se 2 (by rfl) ⟨1185075, by rfl⟩ : syracuseStep 3160201 = 2370151) B2370151
theorem B2808047 : Blo 1871637 2808047 := bstep (se 1 (by rfl) ⟨2106035, by rfl⟩ : syracuseStep 2808047 = 4212071) B4212071
theorem B2808059 : Blo 1871637 2808059 := bstep (se 1 (by rfl) ⟨2106044, by rfl⟩ : syracuseStep 2808059 = 4212089) B4212089
theorem B6322427 : Blo 1871637 6322427 := bstep (se 1 (by rfl) ⟨4741820, by rfl⟩ : syracuseStep 6322427 = 9483641) B9483641
theorem B2808119 : Blo 1871637 2808119 := bstep (se 1 (by rfl) ⟨2106089, by rfl⟩ : syracuseStep 2808119 = 4212179) B4212179
theorem B2808143 : Blo 1871637 2808143 := bstep (se 1 (by rfl) ⟨2106107, by rfl⟩ : syracuseStep 2808143 = 4212215) B4212215
theorem B7109117 : Blo 1871637 7109117 := bstep (se 3 (by rfl) ⟨1332959, by rfl⟩ : syracuseStep 7109117 = 2665919) B2665919
theorem B2808827 : Blo 1871637 2808827 := bstep (se 1 (by rfl) ⟨2106620, by rfl⟩ : syracuseStep 2808827 = 4213241) B4213241
theorem B2808935 : Blo 1871637 2808935 := bstep (se 1 (by rfl) ⟨2106701, by rfl⟩ : syracuseStep 2808935 = 4213403) B4213403
theorem B2808959 : Blo 1871637 2808959 := bstep (se 1 (by rfl) ⟨2106719, by rfl⟩ : syracuseStep 2808959 = 4213439) B4213439
theorem B2809007 : Blo 1871637 2809007 := bstep (se 1 (by rfl) ⟨2106755, by rfl⟩ : syracuseStep 2809007 = 4213511) B4213511
theorem B14417149 : Blo 1871637 14417149 := bstep (se 3 (by rfl) ⟨2703215, by rfl⟩ : syracuseStep 14417149 = 5406431) B5406431
theorem B27000155 : Blo 1871637 27000155 := bstep (se 1 (by rfl) ⟨20250116, by rfl⟩ : syracuseStep 27000155 = 40500233) B40500233
theorem B2809295 : Blo 1871637 2809295 := bstep (se 1 (by rfl) ⟨2106971, by rfl⟩ : syracuseStep 2809295 = 4213943) B4213943
theorem B2809391 : Blo 1871637 2809391 := bstep (se 1 (by rfl) ⟨2107043, by rfl⟩ : syracuseStep 2809391 = 4214087) B4214087
theorem B2809679 : Blo 1871637 2809679 := bstep (se 1 (by rfl) ⟨2107259, by rfl⟩ : syracuseStep 2809679 = 4214519) B4214519
theorem B5996447 : Blo 1871637 5996447 := bstep (se 1 (by rfl) ⟨4497335, by rfl⟩ : syracuseStep 5996447 = 8994671) B8994671
theorem B71188703 : Blo 1871637 71188703 := bstep (se 1 (by rfl) ⟨53391527, by rfl⟩ : syracuseStep 71188703 = 106783055) B106783055
theorem B12001709 : Blo 1871637 12001709 := bstep (se 3 (by rfl) ⟨2250320, by rfl⟩ : syracuseStep 12001709 = 4500641) B4500641
theorem B7111259 : Blo 1871637 7111259 := bstep (se 1 (by rfl) ⟨5333444, by rfl⟩ : syracuseStep 7111259 = 10666889) B10666889
theorem B72000413 : Blo 1871637 72000413 := bstep (se 3 (by rfl) ⟨13500077, by rfl⟩ : syracuseStep 72000413 = 27000155) B27000155
theorem B4211873 : Blo 1871637 4211873 := bstep (se 2 (by rfl) ⟨1579452, by rfl⟩ : syracuseStep 4211873 = 3158905) B3158905
theorem B2106607 : Blo 1871637 2106607 := bstep (se 1 (by rfl) ⟨1579955, by rfl⟩ : syracuseStep 2106607 = 3159911) B3159911
theorem B4212251 : Blo 1871637 4212251 := bstep (se 1 (by rfl) ⟨3159188, by rfl⟩ : syracuseStep 4212251 = 6318377) B6318377
theorem B15189535 : Blo 1871637 15189535 := bstep (se 1 (by rfl) ⟨11392151, by rfl⟩ : syracuseStep 15189535 = 22784303) B22784303
theorem B14223275 : Blo 1871637 14223275 := bstep (se 1 (by rfl) ⟨10667456, by rfl⟩ : syracuseStep 14223275 = 21334913) B21334913
theorem B4212791 : Blo 1871637 4212791 := bstep (se 1 (by rfl) ⟨3159593, by rfl⟩ : syracuseStep 4212791 = 6319187) B6319187
theorem B4212827 : Blo 1871637 4212827 := bstep (se 1 (by rfl) ⟨3159620, by rfl⟩ : syracuseStep 4212827 = 6319241) B6319241
theorem B8112251 : Blo 1871637 8112251 := bstep (se 1 (by rfl) ⟨6084188, by rfl⟩ : syracuseStep 8112251 = 12168377) B12168377
theorem B4213295 : Blo 1871637 4213295 := bstep (se 1 (by rfl) ⟨3159971, by rfl⟩ : syracuseStep 4213295 = 6319943) B6319943
theorem B4213601 : Blo 1871637 4213601 := bstep (se 2 (by rfl) ⟨1580100, by rfl⟩ : syracuseStep 4213601 = 3160201) B3160201
theorem B17992691 : Blo 1871637 17992691 := bstep (se 1 (by rfl) ⟨13494518, by rfl⟩ : syracuseStep 17992691 = 26989037) B26989037
theorem B6319295 : Blo 1871637 6319295 := bstep (se 1 (by rfl) ⟨4739471, by rfl⟩ : syracuseStep 6319295 = 9478943) B9478943
theorem B4214123 : Blo 1871637 4214123 := bstep (se 1 (by rfl) ⟨3160592, by rfl⟩ : syracuseStep 4214123 = 6321185) B6321185
theorem B61566571 : Blo 1871637 61566571 := bstep (se 1 (by rfl) ⟨46174928, by rfl⟩ : syracuseStep 61566571 = 92349857) B92349857
theorem B1871707 : Blo 1871637 1871707 := bstep (se 1 (by rfl) ⟨1403780, by rfl⟩ : syracuseStep 1871707 = 2807561) B2807561
theorem B6319997 : Blo 1871637 6319997 := bstep (se 3 (by rfl) ⟨1184999, by rfl⟩ : syracuseStep 6319997 = 2369999) B2369999
theorem B1872031 : Blo 1871637 1872031 := bstep (se 1 (by rfl) ⟨1404023, by rfl⟩ : syracuseStep 1872031 = 2808047) B2808047
theorem B1872039 : Blo 1871637 1872039 := bstep (se 1 (by rfl) ⟨1404029, by rfl⟩ : syracuseStep 1872039 = 2808059) B2808059
theorem B4214951 : Blo 1871637 4214951 := bstep (se 1 (by rfl) ⟨3161213, by rfl⟩ : syracuseStep 4214951 = 6322427) B6322427
theorem B1872079 : Blo 1871637 1872079 := bstep (se 1 (by rfl) ⟨1404059, by rfl⟩ : syracuseStep 1872079 = 2808119) B2808119
theorem B1872095 : Blo 1871637 1872095 := bstep (se 1 (by rfl) ⟨1404071, by rfl⟩ : syracuseStep 1872095 = 2808143) B2808143
theorem B19222865 : Blo 1871637 19222865 := bstep (se 2 (by rfl) ⟨7208574, by rfl⟩ : syracuseStep 19222865 = 14417149) B14417149
theorem B4739411 : Blo 1871637 4739411 := bstep (se 1 (by rfl) ⟨3554558, by rfl⟩ : syracuseStep 4739411 = 7109117) B7109117
theorem B1872551 : Blo 1871637 1872551 := bstep (se 1 (by rfl) ⟨1404413, by rfl⟩ : syracuseStep 1872551 = 2808827) B2808827
theorem B1872623 : Blo 1871637 1872623 := bstep (se 1 (by rfl) ⟨1404467, by rfl⟩ : syracuseStep 1872623 = 2808935) B2808935
theorem B1872639 : Blo 1871637 1872639 := bstep (se 1 (by rfl) ⟨1404479, by rfl⟩ : syracuseStep 1872639 = 2808959) B2808959
theorem B1872671 : Blo 1871637 1872671 := bstep (se 1 (by rfl) ⟨1404503, by rfl⟩ : syracuseStep 1872671 = 2809007) B2809007
theorem B1872863 : Blo 1871637 1872863 := bstep (se 1 (by rfl) ⟨1404647, by rfl⟩ : syracuseStep 1872863 = 2809295) B2809295
theorem B1872927 : Blo 1871637 1872927 := bstep (se 1 (by rfl) ⟨1404695, by rfl⟩ : syracuseStep 1872927 = 2809391) B2809391
theorem B7107689 : Blo 1871637 7107689 := bstep (se 2 (by rfl) ⟨2665383, by rfl⟩ : syracuseStep 7107689 = 5330767) B5330767
theorem B1873119 : Blo 1871637 1873119 := bstep (se 1 (by rfl) ⟨1404839, by rfl⟩ : syracuseStep 1873119 = 2809679) B2809679
theorem B1873343 : Blo 1871637 1873343 := bstep (se 1 (by rfl) ⟨1405007, by rfl⟩ : syracuseStep 1873343 = 2810015) B2810015
theorem B1873439 : Blo 1871637 1873439 := bstep (se 1 (by rfl) ⟨1405079, by rfl⟩ : syracuseStep 1873439 = 2810159) B2810159
theorem B5330539 : Blo 1871637 5330539 := bstep (se 1 (by rfl) ⟨3997904, by rfl⟩ : syracuseStep 5330539 = 7995809) B7995809
theorem B1873535 : Blo 1871637 1873535 := bstep (se 1 (by rfl) ⟨1405151, by rfl⟩ : syracuseStep 1873535 = 2810303) B2810303
theorem B2807579 : Blo 1871637 2807579 := bstep (se 1 (by rfl) ⟨2105684, by rfl⟩ : syracuseStep 2807579 = 4211369) B4211369
theorem B8001449 : Blo 1871637 8001449 := bstep (se 2 (by rfl) ⟨3000543, by rfl⟩ : syracuseStep 8001449 = 6001087) B6001087
theorem B21321791 : Blo 1871637 21321791 := bstep (se 1 (by rfl) ⟨15991343, by rfl⟩ : syracuseStep 21321791 = 31982687) B31982687
theorem B4741193 : Blo 1871637 4741193 := bstep (se 2 (by rfl) ⟨1777947, by rfl⟩ : syracuseStep 4741193 = 3555895) B3555895
theorem B2808233 : Blo 1871637 2808233 := bstep (se 2 (by rfl) ⟨1053087, by rfl⟩ : syracuseStep 2808233 = 2106175) B2106175
theorem B2808287 : Blo 1871637 2808287 := bstep (se 1 (by rfl) ⟨2106215, by rfl⟩ : syracuseStep 2808287 = 4212431) B4212431
theorem B4741679 : Blo 1871637 4741679 := bstep (se 1 (by rfl) ⟨3556259, by rfl⟩ : syracuseStep 4741679 = 7112519) B7112519
theorem B2808431 : Blo 1871637 2808431 := bstep (se 1 (by rfl) ⟨2106323, by rfl⟩ : syracuseStep 2808431 = 4212647) B4212647
theorem B7593535 : Blo 1871637 7593535 := bstep (se 1 (by rfl) ⟨5695151, by rfl⟩ : syracuseStep 7593535 = 11390303) B11390303
theorem B3997631 : Blo 1871637 3997631 := bstep (se 1 (by rfl) ⟨2998223, by rfl⟩ : syracuseStep 3997631 = 5996447) B5996447
theorem B2809967 : Blo 1871637 2809967 := bstep (se 1 (by rfl) ⟨2107475, by rfl⟩ : syracuseStep 2809967 = 4214951) B4214951
theorem B81010853 : Blo 1871637 81010853 := bstep (se 4 (by rfl) ⟨7594767, by rfl⟩ : syracuseStep 81010853 = 15189535) B15189535
theorem B5334299 : Blo 1871637 5334299 := bstep (se 1 (by rfl) ⟨4000724, by rfl⟩ : syracuseStep 5334299 = 8001449) B8001449
theorem B14214527 : Blo 1871637 14214527 := bstep (se 1 (by rfl) ⟨10660895, by rfl⟩ : syracuseStep 14214527 = 21321791) B21321791
theorem B5408167 : Blo 1871637 5408167 := bstep (se 1 (by rfl) ⟨4056125, by rfl⟩ : syracuseStep 5408167 = 8112251) B8112251
theorem B11995127 : Blo 1871637 11995127 := bstep (se 1 (by rfl) ⟨8996345, by rfl⟩ : syracuseStep 11995127 = 17992691) B17992691
theorem B4212863 : Blo 1871637 4212863 := bstep (se 1 (by rfl) ⟨3159647, by rfl⟩ : syracuseStep 4212863 = 6319295) B6319295
theorem B10660349 : Blo 1871637 10660349 := bstep (se 3 (by rfl) ⟨1998815, by rfl⟩ : syracuseStep 10660349 = 3997631) B3997631
theorem B4213331 : Blo 1871637 4213331 := bstep (se 1 (by rfl) ⟨3159998, by rfl⟩ : syracuseStep 4213331 = 6319997) B6319997
theorem B47459135 : Blo 1871637 47459135 := bstep (se 1 (by rfl) ⟨35594351, by rfl⟩ : syracuseStep 47459135 = 71188703) B71188703
theorem B12815243 : Blo 1871637 12815243 := bstep (se 1 (by rfl) ⟨9611432, by rfl⟩ : syracuseStep 12815243 = 19222865) B19222865
theorem B48000275 : Blo 1871637 48000275 := bstep (se 1 (by rfl) ⟨36000206, by rfl⟩ : syracuseStep 48000275 = 72000413) B72000413
theorem B4738459 : Blo 1871637 4738459 := bstep (se 1 (by rfl) ⟨3553844, by rfl⟩ : syracuseStep 4738459 = 7107689) B7107689
theorem B1871719 : Blo 1871637 1871719 := bstep (se 1 (by rfl) ⟨1403789, by rfl⟩ : syracuseStep 1871719 = 2807579) B2807579
theorem B9482183 : Blo 1871637 9482183 := bstep (se 1 (by rfl) ⟨7111637, by rfl⟩ : syracuseStep 9482183 = 14223275) B14223275
theorem B1872155 : Blo 1871637 1872155 := bstep (se 1 (by rfl) ⟨1404116, by rfl⟩ : syracuseStep 1872155 = 2808233) B2808233
theorem B1872191 : Blo 1871637 1872191 := bstep (se 1 (by rfl) ⟨1404143, by rfl⟩ : syracuseStep 1872191 = 2808287) B2808287
theorem B1872287 : Blo 1871637 1872287 := bstep (se 1 (by rfl) ⟨1404215, by rfl⟩ : syracuseStep 1872287 = 2808431) B2808431
theorem B7107385 : Blo 1871637 7107385 := bstep (se 2 (by rfl) ⟨2665269, by rfl⟩ : syracuseStep 7107385 = 5330539) B5330539
theorem B82088761 : Blo 1871637 82088761 := bstep (se 2 (by rfl) ⟨30783285, by rfl⟩ : syracuseStep 82088761 = 61566571) B61566571
theorem B3159607 : Blo 1871637 3159607 := bstep (se 1 (by rfl) ⟨2369705, by rfl⟩ : syracuseStep 3159607 = 4739411) B4739411
theorem B4740839 : Blo 1871637 4740839 := bstep (se 1 (by rfl) ⟨3555629, by rfl⟩ : syracuseStep 4740839 = 7111259) B7111259
theorem B2807915 : Blo 1871637 2807915 := bstep (se 1 (by rfl) ⟨2105936, by rfl⟩ : syracuseStep 2807915 = 4211873) B4211873
theorem B2808167 : Blo 1871637 2808167 := bstep (se 1 (by rfl) ⟨2106125, by rfl⟩ : syracuseStep 2808167 = 4212251) B4212251
theorem B32004557 : Blo 1871637 32004557 := bstep (se 3 (by rfl) ⟨6000854, by rfl⟩ : syracuseStep 32004557 = 12001709) B12001709
theorem B2808527 : Blo 1871637 2808527 := bstep (se 1 (by rfl) ⟨2106395, by rfl⟩ : syracuseStep 2808527 = 4212791) B4212791
theorem B3160795 : Blo 1871637 3160795 := bstep (se 1 (by rfl) ⟨2370596, by rfl⟩ : syracuseStep 3160795 = 4741193) B4741193
theorem B2808551 : Blo 1871637 2808551 := bstep (se 1 (by rfl) ⟨2106413, by rfl⟩ : syracuseStep 2808551 = 4212827) B4212827
theorem B2808809 : Blo 1871637 2808809 := bstep (se 2 (by rfl) ⟨1053303, by rfl⟩ : syracuseStep 2808809 = 2106607) B2106607
theorem B2808863 : Blo 1871637 2808863 := bstep (se 1 (by rfl) ⟨2106647, by rfl⟩ : syracuseStep 2808863 = 4213295) B4213295
theorem B3161119 : Blo 1871637 3161119 := bstep (se 1 (by rfl) ⟨2370839, by rfl⟩ : syracuseStep 3161119 = 4741679) B4741679
theorem B2809067 : Blo 1871637 2809067 := bstep (se 1 (by rfl) ⟨2106800, by rfl⟩ : syracuseStep 2809067 = 4213601) B4213601
theorem B10124713 : Blo 1871637 10124713 := bstep (se 2 (by rfl) ⟨3796767, by rfl⟩ : syracuseStep 10124713 = 7593535) B7593535
theorem B2809415 : Blo 1871637 2809415 := bstep (se 1 (by rfl) ⟨2107061, by rfl⟩ : syracuseStep 2809415 = 4214123) B4214123
theorem B3556199 : Blo 1871637 3556199 := bstep (se 1 (by rfl) ⟨2667149, by rfl⟩ : syracuseStep 3556199 = 5334299) B5334299
theorem B7996751 : Blo 1871637 7996751 := bstep (se 1 (by rfl) ⟨5997563, by rfl⟩ : syracuseStep 7996751 = 11995127) B11995127
theorem B6317945 : Blo 1871637 6317945 := bstep (se 2 (by rfl) ⟨2369229, by rfl⟩ : syracuseStep 6317945 = 4738459) B4738459
theorem B31639423 : Blo 1871637 31639423 := bstep (se 1 (by rfl) ⟨23729567, by rfl⟩ : syracuseStep 31639423 = 47459135) B47459135
theorem B7210889 : Blo 1871637 7210889 := bstep (se 2 (by rfl) ⟨2704083, by rfl⟩ : syracuseStep 7210889 = 5408167) B5408167
theorem B4212809 : Blo 1871637 4212809 := bstep (se 2 (by rfl) ⟨1579803, by rfl⟩ : syracuseStep 4212809 = 3159607) B3159607
theorem B32000183 : Blo 1871637 32000183 := bstep (se 1 (by rfl) ⟨24000137, by rfl⟩ : syracuseStep 32000183 = 48000275) B48000275
theorem B4214393 : Blo 1871637 4214393 := bstep (se 2 (by rfl) ⟨1580397, by rfl⟩ : syracuseStep 4214393 = 3160795) B3160795
theorem B4214825 : Blo 1871637 4214825 := bstep (se 2 (by rfl) ⟨1580559, by rfl⟩ : syracuseStep 4214825 = 3161119) B3161119
theorem B1871943 : Blo 1871637 1871943 := bstep (se 1 (by rfl) ⟨1403957, by rfl⟩ : syracuseStep 1871943 = 2807915) B2807915
theorem B1872111 : Blo 1871637 1872111 := bstep (se 1 (by rfl) ⟨1404083, by rfl⟩ : syracuseStep 1872111 = 2808167) B2808167
theorem B21336371 : Blo 1871637 21336371 := bstep (se 1 (by rfl) ⟨16002278, by rfl⟩ : syracuseStep 21336371 = 32004557) B32004557
theorem B7106899 : Blo 1871637 7106899 := bstep (se 1 (by rfl) ⟨5330174, by rfl⟩ : syracuseStep 7106899 = 10660349) B10660349
theorem B1872351 : Blo 1871637 1872351 := bstep (se 1 (by rfl) ⟨1404263, by rfl⟩ : syracuseStep 1872351 = 2808527) B2808527
theorem B1872367 : Blo 1871637 1872367 := bstep (se 1 (by rfl) ⟨1404275, by rfl⟩ : syracuseStep 1872367 = 2808551) B2808551
theorem B1872539 : Blo 1871637 1872539 := bstep (se 1 (by rfl) ⟨1404404, by rfl⟩ : syracuseStep 1872539 = 2808809) B2808809
theorem B1872575 : Blo 1871637 1872575 := bstep (se 1 (by rfl) ⟨1404431, by rfl⟩ : syracuseStep 1872575 = 2808863) B2808863
theorem B1872711 : Blo 1871637 1872711 := bstep (se 1 (by rfl) ⟨1404533, by rfl⟩ : syracuseStep 1872711 = 2809067) B2809067
theorem B1872943 : Blo 1871637 1872943 := bstep (se 1 (by rfl) ⟨1404707, by rfl⟩ : syracuseStep 1872943 = 2809415) B2809415
theorem B6321455 : Blo 1871637 6321455 := bstep (se 1 (by rfl) ⟨4741091, by rfl⟩ : syracuseStep 6321455 = 9482183) B9482183
theorem B1873311 : Blo 1871637 1873311 := bstep (se 1 (by rfl) ⟨1404983, by rfl⟩ : syracuseStep 1873311 = 2809967) B2809967
theorem B54007235 : Blo 1871637 54007235 := bstep (se 1 (by rfl) ⟨40505426, by rfl⟩ : syracuseStep 54007235 = 81010853) B81010853
theorem B9476351 : Blo 1871637 9476351 := bstep (se 1 (by rfl) ⟨7107263, by rfl⟩ : syracuseStep 9476351 = 14214527) B14214527
theorem B9476513 : Blo 1871637 9476513 := bstep (se 2 (by rfl) ⟨3553692, by rfl⟩ : syracuseStep 9476513 = 7107385) B7107385
theorem B109451681 : Blo 1871637 109451681 := bstep (se 2 (by rfl) ⟨41044380, by rfl⟩ : syracuseStep 109451681 = 82088761) B82088761
theorem B3160559 : Blo 1871637 3160559 := bstep (se 1 (by rfl) ⟨2370419, by rfl⟩ : syracuseStep 3160559 = 4740839) B4740839
theorem B2808575 : Blo 1871637 2808575 := bstep (se 1 (by rfl) ⟨2106431, by rfl⟩ : syracuseStep 2808575 = 4212863) B4212863
theorem B2808887 : Blo 1871637 2808887 := bstep (se 1 (by rfl) ⟨2106665, by rfl⟩ : syracuseStep 2808887 = 4213331) B4213331
theorem B13499617 : Blo 1871637 13499617 := bstep (se 2 (by rfl) ⟨5062356, by rfl⟩ : syracuseStep 13499617 = 10124713) B10124713
theorem B8543495 : Blo 1871637 8543495 := bstep (se 1 (by rfl) ⟨6407621, by rfl⟩ : syracuseStep 8543495 = 12815243) B12815243
theorem B2809883 : Blo 1871637 2809883 := bstep (se 1 (by rfl) ⟨2107412, by rfl⟩ : syracuseStep 2809883 = 4214825) B4214825
theorem B22782653 : Blo 1871637 22782653 := bstep (se 3 (by rfl) ⟨4271747, by rfl⟩ : syracuseStep 22782653 = 8543495) B8543495
theorem B36004823 : Blo 1871637 36004823 := bstep (se 1 (by rfl) ⟨27003617, by rfl⟩ : syracuseStep 36004823 = 54007235) B54007235
theorem B4211963 : Blo 1871637 4211963 := bstep (se 1 (by rfl) ⟨3158972, by rfl⟩ : syracuseStep 4211963 = 6317945) B6317945
theorem B21333455 : Blo 1871637 21333455 := bstep (se 1 (by rfl) ⟨16000091, by rfl⟩ : syracuseStep 21333455 = 32000183) B32000183
theorem B6317567 : Blo 1871637 6317567 := bstep (se 1 (by rfl) ⟨4738175, by rfl⟩ : syracuseStep 6317567 = 9476351) B9476351
theorem B6317675 : Blo 1871637 6317675 := bstep (se 1 (by rfl) ⟨4738256, by rfl⟩ : syracuseStep 6317675 = 9476513) B9476513
theorem B72967787 : Blo 1871637 72967787 := bstep (se 1 (by rfl) ⟨54725840, by rfl⟩ : syracuseStep 72967787 = 109451681) B109451681
theorem B17999489 : Blo 1871637 17999489 := bstep (se 2 (by rfl) ⟨6749808, by rfl⟩ : syracuseStep 17999489 = 13499617) B13499617
theorem B2107039 : Blo 1871637 2107039 := bstep (se 1 (by rfl) ⟨1580279, by rfl⟩ : syracuseStep 2107039 = 3160559) B3160559
theorem B14224247 : Blo 1871637 14224247 := bstep (se 1 (by rfl) ⟨10668185, by rfl⟩ : syracuseStep 14224247 = 21336371) B21336371
theorem B2370799 : Blo 1871637 2370799 := bstep (se 1 (by rfl) ⟨1778099, by rfl⟩ : syracuseStep 2370799 = 3556199) B3556199
theorem B4214303 : Blo 1871637 4214303 := bstep (se 1 (by rfl) ⟨3160727, by rfl⟩ : syracuseStep 4214303 = 6321455) B6321455
theorem B1872383 : Blo 1871637 1872383 := bstep (se 1 (by rfl) ⟨1404287, by rfl⟩ : syracuseStep 1872383 = 2808575) B2808575
theorem B1872591 : Blo 1871637 1872591 := bstep (se 1 (by rfl) ⟨1404443, by rfl⟩ : syracuseStep 1872591 = 2808887) B2808887
theorem B42185897 : Blo 1871637 42185897 := bstep (se 2 (by rfl) ⟨15819711, by rfl⟩ : syracuseStep 42185897 = 31639423) B31639423
theorem B9475865 : Blo 1871637 9475865 := bstep (se 2 (by rfl) ⟨3553449, by rfl⟩ : syracuseStep 9475865 = 7106899) B7106899
theorem B5331167 : Blo 1871637 5331167 := bstep (se 1 (by rfl) ⟨3998375, by rfl⟩ : syracuseStep 5331167 = 7996751) B7996751
theorem B4807259 : Blo 1871637 4807259 := bstep (se 1 (by rfl) ⟨3605444, by rfl⟩ : syracuseStep 4807259 = 7210889) B7210889
theorem B2808539 : Blo 1871637 2808539 := bstep (se 1 (by rfl) ⟨2106404, by rfl⟩ : syracuseStep 2808539 = 4212809) B4212809
theorem B2809595 : Blo 1871637 2809595 := bstep (se 1 (by rfl) ⟨2107196, by rfl⟩ : syracuseStep 2809595 = 4214393) B4214393
theorem B15188435 : Blo 1871637 15188435 := bstep (se 1 (by rfl) ⟨11391326, by rfl⟩ : syracuseStep 15188435 = 22782653) B22782653
theorem B24003215 : Blo 1871637 24003215 := bstep (se 1 (by rfl) ⟨18002411, by rfl⟩ : syracuseStep 24003215 = 36004823) B36004823
theorem B28123931 : Blo 1871637 28123931 := bstep (se 1 (by rfl) ⟨21092948, by rfl⟩ : syracuseStep 28123931 = 42185897) B42185897
theorem B14222303 : Blo 1871637 14222303 := bstep (se 1 (by rfl) ⟨10666727, by rfl⟩ : syracuseStep 14222303 = 21333455) B21333455
theorem B4211711 : Blo 1871637 4211711 := bstep (se 1 (by rfl) ⟨3158783, by rfl⟩ : syracuseStep 4211711 = 6317567) B6317567
theorem B4211783 : Blo 1871637 4211783 := bstep (se 1 (by rfl) ⟨3158837, by rfl⟩ : syracuseStep 4211783 = 6317675) B6317675
theorem B48645191 : Blo 1871637 48645191 := bstep (se 1 (by rfl) ⟨36483893, by rfl⟩ : syracuseStep 48645191 = 72967787) B72967787
theorem B6317243 : Blo 1871637 6317243 := bstep (se 1 (by rfl) ⟨4737932, by rfl⟩ : syracuseStep 6317243 = 9475865) B9475865
theorem B3204839 : Blo 1871637 3204839 := bstep (se 1 (by rfl) ⟨2403629, by rfl⟩ : syracuseStep 3204839 = 4807259) B4807259
theorem B1872359 : Blo 1871637 1872359 := bstep (se 1 (by rfl) ⟨1404269, by rfl⟩ : syracuseStep 1872359 = 2808539) B2808539
theorem B9482831 : Blo 1871637 9482831 := bstep (se 1 (by rfl) ⟨7112123, by rfl⟩ : syracuseStep 9482831 = 14224247) B14224247
theorem B1873063 : Blo 1871637 1873063 := bstep (se 1 (by rfl) ⟨1404797, by rfl⟩ : syracuseStep 1873063 = 2809595) B2809595
theorem B1873255 : Blo 1871637 1873255 := bstep (se 1 (by rfl) ⟨1404941, by rfl⟩ : syracuseStep 1873255 = 2809883) B2809883
theorem B2807975 : Blo 1871637 2807975 := bstep (se 1 (by rfl) ⟨2105981, by rfl⟩ : syracuseStep 2807975 = 4211963) B4211963
theorem B11999659 : Blo 1871637 11999659 := bstep (se 1 (by rfl) ⟨8999744, by rfl⟩ : syracuseStep 11999659 = 17999489) B17999489
theorem B3554111 : Blo 1871637 3554111 := bstep (se 1 (by rfl) ⟨2665583, by rfl⟩ : syracuseStep 3554111 = 5331167) B5331167
theorem B3161065 : Blo 1871637 3161065 := bstep (se 2 (by rfl) ⟨1185399, by rfl⟩ : syracuseStep 3161065 = 2370799) B2370799
theorem B2809385 : Blo 1871637 2809385 := bstep (se 2 (by rfl) ⟨1053519, by rfl⟩ : syracuseStep 2809385 = 2107039) B2107039
theorem B2809535 : Blo 1871637 2809535 := bstep (se 1 (by rfl) ⟨2107151, by rfl⟩ : syracuseStep 2809535 = 4214303) B4214303
theorem B10125623 : Blo 1871637 10125623 := bstep (se 1 (by rfl) ⟨7594217, by rfl⟩ : syracuseStep 10125623 = 15188435) B15188435
theorem B15999545 : Blo 1871637 15999545 := bstep (se 2 (by rfl) ⟨5999829, by rfl⟩ : syracuseStep 15999545 = 11999659) B11999659
theorem B4211495 : Blo 1871637 4211495 := bstep (se 1 (by rfl) ⟨3158621, by rfl⟩ : syracuseStep 4211495 = 6317243) B6317243
theorem B2369407 : Blo 1871637 2369407 := bstep (se 1 (by rfl) ⟨1777055, by rfl⟩ : syracuseStep 2369407 = 3554111) B3554111
theorem B16002143 : Blo 1871637 16002143 := bstep (se 1 (by rfl) ⟨12001607, by rfl⟩ : syracuseStep 16002143 = 24003215) B24003215
theorem B9481535 : Blo 1871637 9481535 := bstep (se 1 (by rfl) ⟨7111151, by rfl⟩ : syracuseStep 9481535 = 14222303) B14222303
theorem B4214753 : Blo 1871637 4214753 := bstep (se 2 (by rfl) ⟨1580532, by rfl⟩ : syracuseStep 4214753 = 3161065) B3161065
theorem B1871983 : Blo 1871637 1871983 := bstep (se 1 (by rfl) ⟨1403987, by rfl⟩ : syracuseStep 1871983 = 2807975) B2807975
theorem B1872923 : Blo 1871637 1872923 := bstep (se 1 (by rfl) ⟨1404692, by rfl⟩ : syracuseStep 1872923 = 2809385) B2809385
theorem B1873023 : Blo 1871637 1873023 := bstep (se 1 (by rfl) ⟨1404767, by rfl⟩ : syracuseStep 1873023 = 2809535) B2809535
theorem B6321887 : Blo 1871637 6321887 := bstep (se 1 (by rfl) ⟨4741415, by rfl⟩ : syracuseStep 6321887 = 9482831) B9482831
theorem B18749287 : Blo 1871637 18749287 := bstep (se 1 (by rfl) ⟨14061965, by rfl⟩ : syracuseStep 18749287 = 28123931) B28123931
theorem B2807807 : Blo 1871637 2807807 := bstep (se 1 (by rfl) ⟨2105855, by rfl⟩ : syracuseStep 2807807 = 4211711) B4211711
theorem B2807855 : Blo 1871637 2807855 := bstep (se 1 (by rfl) ⟨2105891, by rfl⟩ : syracuseStep 2807855 = 4211783) B4211783
theorem B32430127 : Blo 1871637 32430127 := bstep (se 1 (by rfl) ⟨24322595, by rfl⟩ : syracuseStep 32430127 = 48645191) B48645191
theorem B2136559 : Blo 1871637 2136559 := bstep (se 1 (by rfl) ⟨1602419, by rfl⟩ : syracuseStep 2136559 = 3204839) B3204839
theorem B6750415 : Blo 1871637 6750415 := bstep (se 1 (by rfl) ⟨5062811, by rfl⟩ : syracuseStep 6750415 = 10125623) B10125623
theorem B10666363 : Blo 1871637 10666363 := bstep (se 1 (by rfl) ⟨7999772, by rfl⟩ : syracuseStep 10666363 = 15999545) B15999545
theorem B10668095 : Blo 1871637 10668095 := bstep (se 1 (by rfl) ⟨8001071, by rfl⟩ : syracuseStep 10668095 = 16002143) B16002143
theorem B43240169 : Blo 1871637 43240169 := bstep (se 2 (by rfl) ⟨16215063, by rfl⟩ : syracuseStep 43240169 = 32430127) B32430127
theorem B4214591 : Blo 1871637 4214591 := bstep (se 1 (by rfl) ⟨3160943, by rfl⟩ : syracuseStep 4214591 = 6321887) B6321887
theorem B1871871 : Blo 1871637 1871871 := bstep (se 1 (by rfl) ⟨1403903, by rfl⟩ : syracuseStep 1871871 = 2807807) B2807807
theorem B1871903 : Blo 1871637 1871903 := bstep (se 1 (by rfl) ⟨1403927, by rfl⟩ : syracuseStep 1871903 = 2807855) B2807855
theorem B6321023 : Blo 1871637 6321023 := bstep (se 1 (by rfl) ⟨4740767, by rfl⟩ : syracuseStep 6321023 = 9481535) B9481535
theorem B24999049 : Blo 1871637 24999049 := bstep (se 2 (by rfl) ⟨9374643, by rfl⟩ : syracuseStep 24999049 = 18749287) B18749287
theorem B3159209 : Blo 1871637 3159209 := bstep (se 2 (by rfl) ⟨1184703, by rfl⟩ : syracuseStep 3159209 = 2369407) B2369407
theorem B2807663 : Blo 1871637 2807663 := bstep (se 1 (by rfl) ⟨2105747, by rfl⟩ : syracuseStep 2807663 = 4211495) B4211495
theorem B2848745 : Blo 1871637 2848745 := bstep (se 2 (by rfl) ⟨1068279, by rfl⟩ : syracuseStep 2848745 = 2136559) B2136559
theorem B2809835 : Blo 1871637 2809835 := bstep (se 1 (by rfl) ⟨2107376, by rfl⟩ : syracuseStep 2809835 = 4214753) B4214753
theorem B14221817 : Blo 1871637 14221817 := bstep (se 2 (by rfl) ⟨5333181, by rfl⟩ : syracuseStep 14221817 = 10666363) B10666363
theorem B2106139 : Blo 1871637 2106139 := bstep (se 1 (by rfl) ⟨1579604, by rfl⟩ : syracuseStep 2106139 = 3159209) B3159209
theorem B7112063 : Blo 1871637 7112063 := bstep (se 1 (by rfl) ⟨5334047, by rfl⟩ : syracuseStep 7112063 = 10668095) B10668095
theorem B4214015 : Blo 1871637 4214015 := bstep (se 1 (by rfl) ⟨3160511, by rfl⟩ : syracuseStep 4214015 = 6321023) B6321023
theorem B133328261 : Blo 1871637 133328261 := bstep (se 4 (by rfl) ⟨12499524, by rfl⟩ : syracuseStep 133328261 = 24999049) B24999049
theorem B1871775 : Blo 1871637 1871775 := bstep (se 1 (by rfl) ⟨1403831, by rfl⟩ : syracuseStep 1871775 = 2807663) B2807663
theorem B1873223 : Blo 1871637 1873223 := bstep (se 1 (by rfl) ⟨1404917, by rfl⟩ : syracuseStep 1873223 = 2809835) B2809835
theorem B9000553 : Blo 1871637 9000553 := bstep (se 2 (by rfl) ⟨3375207, by rfl⟩ : syracuseStep 9000553 = 6750415) B6750415
theorem B1899163 : Blo 1871637 1899163 := bstep (se 1 (by rfl) ⟨1424372, by rfl⟩ : syracuseStep 1899163 = 2848745) B2848745
theorem B28826779 : Blo 1871637 28826779 := bstep (se 1 (by rfl) ⟨21620084, by rfl⟩ : syracuseStep 28826779 = 43240169) B43240169
theorem B2809727 : Blo 1871637 2809727 := bstep (se 1 (by rfl) ⟨2107295, by rfl⟩ : syracuseStep 2809727 = 4214591) B4214591
theorem B2532217 : Blo 1871637 2532217 := bstep (se 2 (by rfl) ⟨949581, by rfl⟩ : syracuseStep 2532217 = 1899163) B1899163
theorem B88885507 : Blo 1871637 88885507 := bstep (se 1 (by rfl) ⟨66664130, by rfl⟩ : syracuseStep 88885507 = 133328261) B133328261
theorem B9481211 : Blo 1871637 9481211 := bstep (se 1 (by rfl) ⟨7110908, by rfl⟩ : syracuseStep 9481211 = 14221817) B14221817
theorem B1873151 : Blo 1871637 1873151 := bstep (se 1 (by rfl) ⟨1404863, by rfl⟩ : syracuseStep 1873151 = 2809727) B2809727
theorem B4741375 : Blo 1871637 4741375 := bstep (se 1 (by rfl) ⟨3556031, by rfl⟩ : syracuseStep 4741375 = 7112063) B7112063
theorem B2808185 : Blo 1871637 2808185 := bstep (se 2 (by rfl) ⟨1053069, by rfl⟩ : syracuseStep 2808185 = 2106139) B2106139
theorem B38435705 : Blo 1871637 38435705 := bstep (se 2 (by rfl) ⟨14413389, by rfl⟩ : syracuseStep 38435705 = 28826779) B28826779
theorem B12000737 : Blo 1871637 12000737 := bstep (se 2 (by rfl) ⟨4500276, by rfl⟩ : syracuseStep 12000737 = 9000553) B9000553
theorem B2809343 : Blo 1871637 2809343 := bstep (se 1 (by rfl) ⟨2107007, by rfl⟩ : syracuseStep 2809343 = 4214015) B4214015
theorem B118514009 : Blo 1871637 118514009 := bstep (se 2 (by rfl) ⟨44442753, by rfl⟩ : syracuseStep 118514009 = 88885507) B88885507
theorem B3376289 : Blo 1871637 3376289 := bstep (se 2 (by rfl) ⟨1266108, by rfl⟩ : syracuseStep 3376289 = 2532217) B2532217
theorem B1872123 : Blo 1871637 1872123 := bstep (se 1 (by rfl) ⟨1404092, by rfl⟩ : syracuseStep 1872123 = 2808185) B2808185
theorem B6320807 : Blo 1871637 6320807 := bstep (se 1 (by rfl) ⟨4740605, by rfl⟩ : syracuseStep 6320807 = 9481211) B9481211
theorem B8000491 : Blo 1871637 8000491 := bstep (se 1 (by rfl) ⟨6000368, by rfl⟩ : syracuseStep 8000491 = 12000737) B12000737
theorem B1872895 : Blo 1871637 1872895 := bstep (se 1 (by rfl) ⟨1404671, by rfl⟩ : syracuseStep 1872895 = 2809343) B2809343
theorem B6321833 : Blo 1871637 6321833 := bstep (se 2 (by rfl) ⟨2370687, by rfl⟩ : syracuseStep 6321833 = 4741375) B4741375
theorem B25623803 : Blo 1871637 25623803 := bstep (se 1 (by rfl) ⟨19217852, by rfl⟩ : syracuseStep 25623803 = 38435705) B38435705
theorem B10667321 : Blo 1871637 10667321 := bstep (se 2 (by rfl) ⟨4000245, by rfl⟩ : syracuseStep 10667321 = 8000491) B8000491
theorem B17082535 : Blo 1871637 17082535 := bstep (se 1 (by rfl) ⟨12811901, by rfl⟩ : syracuseStep 17082535 = 25623803) B25623803
theorem B4213871 : Blo 1871637 4213871 := bstep (se 1 (by rfl) ⟨3160403, by rfl⟩ : syracuseStep 4213871 = 6320807) B6320807
theorem B4214555 : Blo 1871637 4214555 := bstep (se 1 (by rfl) ⟨3160916, by rfl⟩ : syracuseStep 4214555 = 6321833) B6321833
theorem B79009339 : Blo 1871637 79009339 := bstep (se 1 (by rfl) ⟨59257004, by rfl⟩ : syracuseStep 79009339 = 118514009) B118514009
theorem B2250859 : Blo 1871637 2250859 := bstep (se 1 (by rfl) ⟨1688144, by rfl⟩ : syracuseStep 2250859 = 3376289) B3376289
theorem B7111547 : Blo 1871637 7111547 := bstep (se 1 (by rfl) ⟨5333660, by rfl⟩ : syracuseStep 7111547 = 10667321) B10667321
theorem B3001145 : Blo 1871637 3001145 := bstep (se 2 (by rfl) ⟨1125429, by rfl⟩ : syracuseStep 3001145 = 2250859) B2250859
theorem B22776713 : Blo 1871637 22776713 := bstep (se 2 (by rfl) ⟨8541267, by rfl⟩ : syracuseStep 22776713 = 17082535) B17082535
theorem B105345785 : Blo 1871637 105345785 := bstep (se 2 (by rfl) ⟨39504669, by rfl⟩ : syracuseStep 105345785 = 79009339) B79009339
theorem B2809247 : Blo 1871637 2809247 := bstep (se 1 (by rfl) ⟨2106935, by rfl⟩ : syracuseStep 2809247 = 4213871) B4213871
theorem B2809703 : Blo 1871637 2809703 := bstep (se 1 (by rfl) ⟨2107277, by rfl⟩ : syracuseStep 2809703 = 4214555) B4214555
theorem B70230523 : Blo 1871637 70230523 := bstep (se 1 (by rfl) ⟨52672892, by rfl⟩ : syracuseStep 70230523 = 105345785) B105345785
theorem B15184475 : Blo 1871637 15184475 := bstep (se 1 (by rfl) ⟨11388356, by rfl⟩ : syracuseStep 15184475 = 22776713) B22776713
theorem B1872831 : Blo 1871637 1872831 := bstep (se 1 (by rfl) ⟨1404623, by rfl⟩ : syracuseStep 1872831 = 2809247) B2809247
theorem B1873135 : Blo 1871637 1873135 := bstep (se 1 (by rfl) ⟨1404851, by rfl⟩ : syracuseStep 1873135 = 2809703) B2809703
theorem B4741031 : Blo 1871637 4741031 := bstep (se 1 (by rfl) ⟨3555773, by rfl⟩ : syracuseStep 4741031 = 7111547) B7111547
theorem B8003053 : Blo 1871637 8003053 := bstep (se 3 (by rfl) ⟨1500572, by rfl⟩ : syracuseStep 8003053 = 3001145) B3001145
theorem B10670737 : Blo 1871637 10670737 := bstep (se 2 (by rfl) ⟨4001526, by rfl⟩ : syracuseStep 10670737 = 8003053) B8003053
theorem B10122983 : Blo 1871637 10122983 := bstep (se 1 (by rfl) ⟨7592237, by rfl⟩ : syracuseStep 10122983 = 15184475) B15184475
theorem B93640697 : Blo 1871637 93640697 := bstep (se 2 (by rfl) ⟨35115261, by rfl⟩ : syracuseStep 93640697 = 70230523) B70230523
theorem B3160687 : Blo 1871637 3160687 := bstep (se 1 (by rfl) ⟨2370515, by rfl⟩ : syracuseStep 3160687 = 4741031) B4741031
theorem B4214249 : Blo 1871637 4214249 := bstep (se 2 (by rfl) ⟨1580343, by rfl⟩ : syracuseStep 4214249 = 3160687) B3160687
theorem B62427131 : Blo 1871637 62427131 := bstep (se 1 (by rfl) ⟨46820348, by rfl⟩ : syracuseStep 62427131 = 93640697) B93640697
theorem B14227649 : Blo 1871637 14227649 := bstep (se 2 (by rfl) ⟨5335368, by rfl⟩ : syracuseStep 14227649 = 10670737) B10670737
theorem B6748655 : Blo 1871637 6748655 := bstep (se 1 (by rfl) ⟨5061491, by rfl⟩ : syracuseStep 6748655 = 10122983) B10122983
theorem B41618087 : Blo 1871637 41618087 := bstep (se 1 (by rfl) ⟨31213565, by rfl⟩ : syracuseStep 41618087 = 62427131) B62427131
theorem B17996413 : Blo 1871637 17996413 := bstep (se 3 (by rfl) ⟨3374327, by rfl⟩ : syracuseStep 17996413 = 6748655) B6748655
theorem B9485099 : Blo 1871637 9485099 := bstep (se 1 (by rfl) ⟨7113824, by rfl⟩ : syracuseStep 9485099 = 14227649) B14227649
theorem B2809499 : Blo 1871637 2809499 := bstep (se 1 (by rfl) ⟨2107124, by rfl⟩ : syracuseStep 2809499 = 4214249) B4214249
theorem B23995217 : Blo 1871637 23995217 := bstep (se 2 (by rfl) ⟨8998206, by rfl⟩ : syracuseStep 23995217 = 17996413) B17996413
theorem B1872999 : Blo 1871637 1872999 := bstep (se 1 (by rfl) ⟨1404749, by rfl⟩ : syracuseStep 1872999 = 2809499) B2809499
theorem B27745391 : Blo 1871637 27745391 := bstep (se 1 (by rfl) ⟨20809043, by rfl⟩ : syracuseStep 27745391 = 41618087) B41618087
theorem B6323399 : Blo 1871637 6323399 := bstep (se 1 (by rfl) ⟨4742549, by rfl⟩ : syracuseStep 6323399 = 9485099) B9485099
theorem B4215599 : Blo 1871637 4215599 := bstep (se 1 (by rfl) ⟨3161699, by rfl⟩ : syracuseStep 4215599 = 6323399) B6323399
theorem B15996811 : Blo 1871637 15996811 := bstep (se 1 (by rfl) ⟨11997608, by rfl⟩ : syracuseStep 15996811 = 23995217) B23995217
theorem B18496927 : Blo 1871637 18496927 := bstep (se 1 (by rfl) ⟨13872695, by rfl⟩ : syracuseStep 18496927 = 27745391) B27745391
theorem B2810399 : Blo 1871637 2810399 := bstep (se 1 (by rfl) ⟨2107799, by rfl⟩ : syracuseStep 2810399 = 4215599) B4215599
theorem B24662569 : Blo 1871637 24662569 := bstep (se 2 (by rfl) ⟨9248463, by rfl⟩ : syracuseStep 24662569 = 18496927) B18496927
theorem B21329081 : Blo 1871637 21329081 := bstep (se 2 (by rfl) ⟨7998405, by rfl⟩ : syracuseStep 21329081 = 15996811) B15996811
theorem B32883425 : Blo 1871637 32883425 := bstep (se 2 (by rfl) ⟨12331284, by rfl⟩ : syracuseStep 32883425 = 24662569) B24662569
theorem B1873599 : Blo 1871637 1873599 := bstep (se 1 (by rfl) ⟨1405199, by rfl⟩ : syracuseStep 1873599 = 2810399) B2810399
theorem B14219387 : Blo 1871637 14219387 := bstep (se 1 (by rfl) ⟨10664540, by rfl⟩ : syracuseStep 14219387 = 21329081) B21329081
theorem B21922283 : Blo 1871637 21922283 := bstep (se 1 (by rfl) ⟨16441712, by rfl⟩ : syracuseStep 21922283 = 32883425) B32883425
theorem B9479591 : Blo 1871637 9479591 := bstep (se 1 (by rfl) ⟨7109693, by rfl⟩ : syracuseStep 9479591 = 14219387) B14219387
theorem B58459421 : Blo 1871637 58459421 := bstep (se 3 (by rfl) ⟨10961141, by rfl⟩ : syracuseStep 58459421 = 21922283) B21922283
theorem B6319727 : Blo 1871637 6319727 := bstep (se 1 (by rfl) ⟨4739795, by rfl⟩ : syracuseStep 6319727 = 9479591) B9479591
theorem B4213151 : Blo 1871637 4213151 := bstep (se 1 (by rfl) ⟨3159863, by rfl⟩ : syracuseStep 4213151 = 6319727) B6319727
theorem B155891789 : Blo 1871637 155891789 := bstep (se 3 (by rfl) ⟨29229710, by rfl⟩ : syracuseStep 155891789 = 58459421) B58459421
theorem B103927859 : Blo 1871637 103927859 := bstep (se 1 (by rfl) ⟨77945894, by rfl⟩ : syracuseStep 103927859 = 155891789) B155891789
theorem B2808767 : Blo 1871637 2808767 := bstep (se 1 (by rfl) ⟨2106575, by rfl⟩ : syracuseStep 2808767 = 4213151) B4213151
theorem B1872511 : Blo 1871637 1872511 := bstep (se 1 (by rfl) ⟨1404383, by rfl⟩ : syracuseStep 1872511 = 2808767) B2808767
theorem B69285239 : Blo 1871637 69285239 := bstep (se 1 (by rfl) ⟨51963929, by rfl⟩ : syracuseStep 69285239 = 103927859) B103927859
theorem B46190159 : Blo 1871637 46190159 := bstep (se 1 (by rfl) ⟨34642619, by rfl⟩ : syracuseStep 46190159 = 69285239) B69285239
theorem B30793439 : Blo 1871637 30793439 := bstep (se 1 (by rfl) ⟨23095079, by rfl⟩ : syracuseStep 30793439 = 46190159) B46190159
theorem B20528959 : Blo 1871637 20528959 := bstep (se 1 (by rfl) ⟨15396719, by rfl⟩ : syracuseStep 20528959 = 30793439) B30793439
theorem B27371945 : Blo 1871637 27371945 := bstep (se 2 (by rfl) ⟨10264479, by rfl⟩ : syracuseStep 27371945 = 20528959) B20528959
theorem B18247963 : Blo 1871637 18247963 := bstep (se 1 (by rfl) ⟨13685972, by rfl⟩ : syracuseStep 18247963 = 27371945) B27371945
theorem B24330617 : Blo 1871637 24330617 := bstep (se 2 (by rfl) ⟨9123981, by rfl⟩ : syracuseStep 24330617 = 18247963) B18247963
theorem B16220411 : Blo 1871637 16220411 := bstep (se 1 (by rfl) ⟨12165308, by rfl⟩ : syracuseStep 16220411 = 24330617) B24330617
theorem B10813607 : Blo 1871637 10813607 := bstep (se 1 (by rfl) ⟨8110205, by rfl⟩ : syracuseStep 10813607 = 16220411) B16220411
theorem B7209071 : Blo 1871637 7209071 := bstep (se 1 (by rfl) ⟨5406803, by rfl⟩ : syracuseStep 7209071 = 10813607) B10813607
theorem B4806047 : Blo 1871637 4806047 := bstep (se 1 (by rfl) ⟨3604535, by rfl⟩ : syracuseStep 4806047 = 7209071) B7209071
theorem B3204031 : Blo 1871637 3204031 := bstep (se 1 (by rfl) ⟨2403023, by rfl⟩ : syracuseStep 3204031 = 4806047) B4806047
theorem B4272041 : Blo 1871637 4272041 := bstep (se 2 (by rfl) ⟨1602015, by rfl⟩ : syracuseStep 4272041 = 3204031) B3204031
theorem B2848027 : Blo 1871637 2848027 := bstep (se 1 (by rfl) ⟨2136020, by rfl⟩ : syracuseStep 2848027 = 4272041) B4272041
theorem B3797369 : Blo 1871637 3797369 := bstep (se 2 (by rfl) ⟨1424013, by rfl⟩ : syracuseStep 3797369 = 2848027) B2848027
theorem B2531579 : Blo 1871637 2531579 := bstep (se 1 (by rfl) ⟨1898684, by rfl⟩ : syracuseStep 2531579 = 3797369) B3797369
theorem B6750877 : Blo 1871637 6750877 := bstep (se 3 (by rfl) ⟨1265789, by rfl⟩ : syracuseStep 6750877 = 2531579) B2531579
theorem B9001169 : Blo 1871637 9001169 := bstep (se 2 (by rfl) ⟨3375438, by rfl⟩ : syracuseStep 9001169 = 6750877) B6750877
theorem B6000779 : Blo 1871637 6000779 := bstep (se 1 (by rfl) ⟨4500584, by rfl⟩ : syracuseStep 6000779 = 9001169) B9001169
theorem B4000519 : Blo 1871637 4000519 := bstep (se 1 (by rfl) ⟨3000389, by rfl⟩ : syracuseStep 4000519 = 6000779) B6000779
theorem B5334025 : Blo 1871637 5334025 := bstep (se 2 (by rfl) ⟨2000259, by rfl⟩ : syracuseStep 5334025 = 4000519) B4000519
theorem B7112033 : Blo 1871637 7112033 := bstep (se 2 (by rfl) ⟨2667012, by rfl⟩ : syracuseStep 7112033 = 5334025) B5334025
theorem B4741355 : Blo 1871637 4741355 := bstep (se 1 (by rfl) ⟨3556016, by rfl⟩ : syracuseStep 4741355 = 7112033) B7112033
theorem B3160903 : Blo 1871637 3160903 := bstep (se 1 (by rfl) ⟨2370677, by rfl⟩ : syracuseStep 3160903 = 4741355) B4741355
theorem B4214537 : Blo 1871637 4214537 := bstep (se 2 (by rfl) ⟨1580451, by rfl⟩ : syracuseStep 4214537 = 3160903) B3160903
theorem B2809691 : Blo 1871637 2809691 := bstep (se 1 (by rfl) ⟨2107268, by rfl⟩ : syracuseStep 2809691 = 4214537) B4214537
theorem B1873127 : Blo 1871637 1873127 := bstep (se 1 (by rfl) ⟨1404845, by rfl⟩ : syracuseStep 1873127 = 2809691) B2809691

theorem C0 (j : ℕ) (h1 : 467909 ≤ j) (h2 : j ≤ 468408) : Blo 1871637 (4 * j + 3) := by
  interval_cases j
  · exact B1871639
  · exact B1871643
  · exact B1871647
  · exact B1871651
  · exact B1871655
  · exact B1871659
  · exact B1871663
  · exact B1871667
  · exact B1871671
  · exact B1871675
  · exact B1871679
  · exact B1871683
  · exact B1871687
  · exact B1871691
  · exact B1871695
  · exact B1871699
  · exact B1871703
  · exact B1871707
  · exact B1871711
  · exact B1871715
  · exact B1871719
  · exact B1871723
  · exact B1871727
  · exact B1871731
  · exact B1871735
  · exact B1871739
  · exact B1871743
  · exact B1871747
  · exact B1871751
  · exact B1871755
  · exact B1871759
  · exact B1871763
  · exact B1871767
  · exact B1871771
  · exact B1871775
  · exact B1871779
  · exact B1871783
  · exact B1871787
  · exact B1871791
  · exact B1871795
  · exact B1871799
  · exact B1871803
  · exact B1871807
  · exact B1871811
  · exact B1871815
  · exact B1871819
  · exact B1871823
  · exact B1871827
  · exact B1871831
  · exact B1871835
  · exact B1871839
  · exact B1871843
  · exact B1871847
  · exact B1871851
  · exact B1871855
  · exact B1871859
  · exact B1871863
  · exact B1871867
  · exact B1871871
  · exact B1871875
  · exact B1871879
  · exact B1871883
  · exact B1871887
  · exact B1871891
  · exact B1871895
  · exact B1871899
  · exact B1871903
  · exact B1871907
  · exact B1871911
  · exact B1871915
  · exact B1871919
  · exact B1871923
  · exact B1871927
  · exact B1871931
  · exact B1871935
  · exact B1871939
  · exact B1871943
  · exact B1871947
  · exact B1871951
  · exact B1871955
  · exact B1871959
  · exact B1871963
  · exact B1871967
  · exact B1871971
  · exact B1871975
  · exact B1871979
  · exact B1871983
  · exact B1871987
  · exact B1871991
  · exact B1871995
  · exact B1871999
  · exact B1872003
  · exact B1872007
  · exact B1872011
  · exact B1872015
  · exact B1872019
  · exact B1872023
  · exact B1872027
  · exact B1872031
  · exact B1872035
  · exact B1872039
  · exact B1872043
  · exact B1872047
  · exact B1872051
  · exact B1872055
  · exact B1872059
  · exact B1872063
  · exact B1872067
  · exact B1872071
  · exact B1872075
  · exact B1872079
  · exact B1872083
  · exact B1872087
  · exact B1872091
  · exact B1872095
  · exact B1872099
  · exact B1872103
  · exact B1872107
  · exact B1872111
  · exact B1872115
  · exact B1872119
  · exact B1872123
  · exact B1872127
  · exact B1872131
  · exact B1872135
  · exact B1872139
  · exact B1872143
  · exact B1872147
  · exact B1872151
  · exact B1872155
  · exact B1872159
  · exact B1872163
  · exact B1872167
  · exact B1872171
  · exact B1872175
  · exact B1872179
  · exact B1872183
  · exact B1872187
  · exact B1872191
  · exact B1872195
  · exact B1872199
  · exact B1872203
  · exact B1872207
  · exact B1872211
  · exact B1872215
  · exact B1872219
  · exact B1872223
  · exact B1872227
  · exact B1872231
  · exact B1872235
  · exact B1872239
  · exact B1872243
  · exact B1872247
  · exact B1872251
  · exact B1872255
  · exact B1872259
  · exact B1872263
  · exact B1872267
  · exact B1872271
  · exact B1872275
  · exact B1872279
  · exact B1872283
  · exact B1872287
  · exact B1872291
  · exact B1872295
  · exact B1872299
  · exact B1872303
  · exact B1872307
  · exact B1872311
  · exact B1872315
  · exact B1872319
  · exact B1872323
  · exact B1872327
  · exact B1872331
  · exact B1872335
  · exact B1872339
  · exact B1872343
  · exact B1872347
  · exact B1872351
  · exact B1872355
  · exact B1872359
  · exact B1872363
  · exact B1872367
  · exact B1872371
  · exact B1872375
  · exact B1872379
  · exact B1872383
  · exact B1872387
  · exact B1872391
  · exact B1872395
  · exact B1872399
  · exact B1872403
  · exact B1872407
  · exact B1872411
  · exact B1872415
  · exact B1872419
  · exact B1872423
  · exact B1872427
  · exact B1872431
  · exact B1872435
  · exact B1872439
  · exact B1872443
  · exact B1872447
  · exact B1872451
  · exact B1872455
  · exact B1872459
  · exact B1872463
  · exact B1872467
  · exact B1872471
  · exact B1872475
  · exact B1872479
  · exact B1872483
  · exact B1872487
  · exact B1872491
  · exact B1872495
  · exact B1872499
  · exact B1872503
  · exact B1872507
  · exact B1872511
  · exact B1872515
  · exact B1872519
  · exact B1872523
  · exact B1872527
  · exact B1872531
  · exact B1872535
  · exact B1872539
  · exact B1872543
  · exact B1872547
  · exact B1872551
  · exact B1872555
  · exact B1872559
  · exact B1872563
  · exact B1872567
  · exact B1872571
  · exact B1872575
  · exact B1872579
  · exact B1872583
  · exact B1872587
  · exact B1872591
  · exact B1872595
  · exact B1872599
  · exact B1872603
  · exact B1872607
  · exact B1872611
  · exact B1872615
  · exact B1872619
  · exact B1872623
  · exact B1872627
  · exact B1872631
  · exact B1872635
  · exact B1872639
  · exact B1872643
  · exact B1872647
  · exact B1872651
  · exact B1872655
  · exact B1872659
  · exact B1872663
  · exact B1872667
  · exact B1872671
  · exact B1872675
  · exact B1872679
  · exact B1872683
  · exact B1872687
  · exact B1872691
  · exact B1872695
  · exact B1872699
  · exact B1872703
  · exact B1872707
  · exact B1872711
  · exact B1872715
  · exact B1872719
  · exact B1872723
  · exact B1872727
  · exact B1872731
  · exact B1872735
  · exact B1872739
  · exact B1872743
  · exact B1872747
  · exact B1872751
  · exact B1872755
  · exact B1872759
  · exact B1872763
  · exact B1872767
  · exact B1872771
  · exact B1872775
  · exact B1872779
  · exact B1872783
  · exact B1872787
  · exact B1872791
  · exact B1872795
  · exact B1872799
  · exact B1872803
  · exact B1872807
  · exact B1872811
  · exact B1872815
  · exact B1872819
  · exact B1872823
  · exact B1872827
  · exact B1872831
  · exact B1872835
  · exact B1872839
  · exact B1872843
  · exact B1872847
  · exact B1872851
  · exact B1872855
  · exact B1872859
  · exact B1872863
  · exact B1872867
  · exact B1872871
  · exact B1872875
  · exact B1872879
  · exact B1872883
  · exact B1872887
  · exact B1872891
  · exact B1872895
  · exact B1872899
  · exact B1872903
  · exact B1872907
  · exact B1872911
  · exact B1872915
  · exact B1872919
  · exact B1872923
  · exact B1872927
  · exact B1872931
  · exact B1872935
  · exact B1872939
  · exact B1872943
  · exact B1872947
  · exact B1872951
  · exact B1872955
  · exact B1872959
  · exact B1872963
  · exact B1872967
  · exact B1872971
  · exact B1872975
  · exact B1872979
  · exact B1872983
  · exact B1872987
  · exact B1872991
  · exact B1872995
  · exact B1872999
  · exact B1873003
  · exact B1873007
  · exact B1873011
  · exact B1873015
  · exact B1873019
  · exact B1873023
  · exact B1873027
  · exact B1873031
  · exact B1873035
  · exact B1873039
  · exact B1873043
  · exact B1873047
  · exact B1873051
  · exact B1873055
  · exact B1873059
  · exact B1873063
  · exact B1873067
  · exact B1873071
  · exact B1873075
  · exact B1873079
  · exact B1873083
  · exact B1873087
  · exact B1873091
  · exact B1873095
  · exact B1873099
  · exact B1873103
  · exact B1873107
  · exact B1873111
  · exact B1873115
  · exact B1873119
  · exact B1873123
  · exact B1873127
  · exact B1873131
  · exact B1873135
  · exact B1873139
  · exact B1873143
  · exact B1873147
  · exact B1873151
  · exact B1873155
  · exact B1873159
  · exact B1873163
  · exact B1873167
  · exact B1873171
  · exact B1873175
  · exact B1873179
  · exact B1873183
  · exact B1873187
  · exact B1873191
  · exact B1873195
  · exact B1873199
  · exact B1873203
  · exact B1873207
  · exact B1873211
  · exact B1873215
  · exact B1873219
  · exact B1873223
  · exact B1873227
  · exact B1873231
  · exact B1873235
  · exact B1873239
  · exact B1873243
  · exact B1873247
  · exact B1873251
  · exact B1873255
  · exact B1873259
  · exact B1873263
  · exact B1873267
  · exact B1873271
  · exact B1873275
  · exact B1873279
  · exact B1873283
  · exact B1873287
  · exact B1873291
  · exact B1873295
  · exact B1873299
  · exact B1873303
  · exact B1873307
  · exact B1873311
  · exact B1873315
  · exact B1873319
  · exact B1873323
  · exact B1873327
  · exact B1873331
  · exact B1873335
  · exact B1873339
  · exact B1873343
  · exact B1873347
  · exact B1873351
  · exact B1873355
  · exact B1873359
  · exact B1873363
  · exact B1873367
  · exact B1873371
  · exact B1873375
  · exact B1873379
  · exact B1873383
  · exact B1873387
  · exact B1873391
  · exact B1873395
  · exact B1873399
  · exact B1873403
  · exact B1873407
  · exact B1873411
  · exact B1873415
  · exact B1873419
  · exact B1873423
  · exact B1873427
  · exact B1873431
  · exact B1873435
  · exact B1873439
  · exact B1873443
  · exact B1873447
  · exact B1873451
  · exact B1873455
  · exact B1873459
  · exact B1873463
  · exact B1873467
  · exact B1873471
  · exact B1873475
  · exact B1873479
  · exact B1873483
  · exact B1873487
  · exact B1873491
  · exact B1873495
  · exact B1873499
  · exact B1873503
  · exact B1873507
  · exact B1873511
  · exact B1873515
  · exact B1873519
  · exact B1873523
  · exact B1873527
  · exact B1873531
  · exact B1873535
  · exact B1873539
  · exact B1873543
  · exact B1873547
  · exact B1873551
  · exact B1873555
  · exact B1873559
  · exact B1873563
  · exact B1873567
  · exact B1873571
  · exact B1873575
  · exact B1873579
  · exact B1873583
  · exact B1873587
  · exact B1873591
  · exact B1873595
  · exact B1873599
  · exact B1873603
  · exact B1873607
  · exact B1873611
  · exact B1873615
  · exact B1873619
  · exact B1873623
  · exact B1873627
  · exact B1873631
  · exact B1873635

theorem solution (m : ℕ) (hlo : 1871637 ≤ m) (hhi : m ≤ 1873637) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 467909 ≤ j := by omega
    have hj2 : j ≤ 468408 := by omega
    have hb : Blo 1871637 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
