-- Prove2me | solution 1 for syracuse_descends_range_1518456_1520456
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:04:23.376028+00:00
-- url     : https://prove2.me/submissions/294693e0-9844-4fce-b8a2-25f7d8886576

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


theorem B2883613 : Blo 1518456 2883613 := bbase (se 3 (by rfl) ⟨540677, by rfl⟩ : syracuseStep 2883613 = 1081355) (by norm_num)
theorem B2564149 : Blo 1518456 2564149 := bbase (se 5 (by rfl) ⟨120194, by rfl⟩ : syracuseStep 2564149 = 240389) (by norm_num)
theorem B1622101 : Blo 1518456 1622101 := bbase (se 8 (by rfl) ⟨9504, by rfl⟩ : syracuseStep 1622101 = 19009) (by norm_num)
theorem B3244141 : Blo 1518456 3244141 := bbase (se 3 (by rfl) ⟨608276, by rfl⟩ : syracuseStep 3244141 = 1216553) (by norm_num)
theorem B5767301 : Blo 1518456 5767301 := bbase (se 4 (by rfl) ⟨540684, by rfl⟩ : syracuseStep 5767301 = 1081369) (by norm_num)
theorem B5128325 : Blo 1518456 5128325 := bbase (se 4 (by rfl) ⟨480780, by rfl⟩ : syracuseStep 5128325 = 961561) (by norm_num)
theorem B2564237 : Blo 1518456 2564237 := bbase (se 3 (by rfl) ⟨480794, by rfl⟩ : syracuseStep 2564237 = 961589) (by norm_num)
theorem B9863317 : Blo 1518456 9863317 := bbase (se 6 (by rfl) ⟨231171, by rfl⟩ : syracuseStep 9863317 = 462343) (by norm_num)
theorem B2883757 : Blo 1518456 2883757 := bbase (se 3 (by rfl) ⟨540704, by rfl⟩ : syracuseStep 2883757 = 1081409) (by norm_num)
theorem B2162909 : Blo 1518456 2162909 := bbase (se 3 (by rfl) ⟨405545, by rfl⟩ : syracuseStep 2162909 = 811091) (by norm_num)
theorem B2564365 : Blo 1518456 2564365 := bbase (se 3 (by rfl) ⟨480818, by rfl⟩ : syracuseStep 2564365 = 961637) (by norm_num)
theorem B2736437 : Blo 1518456 2736437 := bbase (se 5 (by rfl) ⟨128270, by rfl⟩ : syracuseStep 2736437 = 256541) (by norm_num)
theorem B2277701 : Blo 1518456 2277701 := bbase (se 4 (by rfl) ⟨213534, by rfl⟩ : syracuseStep 2277701 = 427069) (by norm_num)
theorem B2883917 : Blo 1518456 2883917 := bbase (se 3 (by rfl) ⟨540734, by rfl⟩ : syracuseStep 2883917 = 1081469) (by norm_num)
theorem B2277725 : Blo 1518456 2277725 := bbase (se 3 (by rfl) ⟨427073, by rfl⟩ : syracuseStep 2277725 = 854147) (by norm_num)
theorem B2564453 : Blo 1518456 2564453 := bbase (se 4 (by rfl) ⟨240417, by rfl⟩ : syracuseStep 2564453 = 480835) (by norm_num)
theorem B2343277 : Blo 1518456 2343277 := bbase (se 3 (by rfl) ⟨439364, by rfl⟩ : syracuseStep 2343277 = 878729) (by norm_num)
theorem B2277749 : Blo 1518456 2277749 := bbase (se 5 (by rfl) ⟨106769, by rfl⟩ : syracuseStep 2277749 = 213539) (by norm_num)
theorem B2277773 : Blo 1518456 2277773 := bbase (se 3 (by rfl) ⟨427082, by rfl⟩ : syracuseStep 2277773 = 854165) (by norm_num)
theorem B2277797 : Blo 1518456 2277797 := bbase (se 4 (by rfl) ⟨213543, by rfl⟩ : syracuseStep 2277797 = 427087) (by norm_num)
theorem B2277821 : Blo 1518456 2277821 := bbase (se 3 (by rfl) ⟨427091, by rfl⟩ : syracuseStep 2277821 = 854183) (by norm_num)
theorem B1622477 : Blo 1518456 1622477 := bbase (se 3 (by rfl) ⟨304214, by rfl⟩ : syracuseStep 1622477 = 608429) (by norm_num)
theorem B2277845 : Blo 1518456 2277845 := bbase (se 7 (by rfl) ⟨26693, by rfl⟩ : syracuseStep 2277845 = 53387) (by norm_num)
theorem B2884061 : Blo 1518456 2884061 := bbase (se 3 (by rfl) ⟨540761, by rfl⟩ : syracuseStep 2884061 = 1081523) (by norm_num)
theorem B2564581 : Blo 1518456 2564581 := bbase (se 4 (by rfl) ⟨240429, by rfl⟩ : syracuseStep 2564581 = 480859) (by norm_num)
theorem B2277869 : Blo 1518456 2277869 := bbase (se 3 (by rfl) ⟨427100, by rfl⟩ : syracuseStep 2277869 = 854201) (by norm_num)
theorem B2277893 : Blo 1518456 2277893 := bbase (se 4 (by rfl) ⟨213552, by rfl⟩ : syracuseStep 2277893 = 427105) (by norm_num)
theorem B3416597 : Blo 1518456 3416597 := bbase (se 6 (by rfl) ⟨80076, by rfl⟩ : syracuseStep 3416597 = 160153) (by norm_num)
theorem B9732629 : Blo 1518456 9732629 := bbase (se 6 (by rfl) ⟨228108, by rfl⟩ : syracuseStep 9732629 = 456217) (by norm_num)
theorem B1622549 : Blo 1518456 1622549 := bbase (se 6 (by rfl) ⟨38028, by rfl⟩ : syracuseStep 1622549 = 76057) (by norm_num)
theorem B2277917 : Blo 1518456 2277917 := bbase (se 3 (by rfl) ⟨427109, by rfl⟩ : syracuseStep 2277917 = 854219) (by norm_num)
theorem B2433581 : Blo 1518456 2433581 := bbase (se 3 (by rfl) ⟨456296, by rfl⟩ : syracuseStep 2433581 = 912593) (by norm_num)
theorem B2277941 : Blo 1518456 2277941 := bbase (se 5 (by rfl) ⟨106778, by rfl⟩ : syracuseStep 2277941 = 213557) (by norm_num)
theorem B5128757 : Blo 1518456 5128757 := bbase (se 5 (by rfl) ⟨240410, by rfl⟩ : syracuseStep 5128757 = 480821) (by norm_num)
theorem B2564669 : Blo 1518456 2564669 := bbase (se 3 (by rfl) ⟨480875, by rfl⟩ : syracuseStep 2564669 = 961751) (by norm_num)
theorem B2277965 : Blo 1518456 2277965 := bbase (se 3 (by rfl) ⟨427118, by rfl⟩ : syracuseStep 2277965 = 854237) (by norm_num)
theorem B3416669 : Blo 1518456 3416669 := bbase (se 3 (by rfl) ⟨640625, by rfl⟩ : syracuseStep 3416669 = 1281251) (by norm_num)
theorem B3244637 : Blo 1518456 3244637 := bbase (se 3 (by rfl) ⟨608369, by rfl⟩ : syracuseStep 3244637 = 1216739) (by norm_num)
theorem B2277989 : Blo 1518456 2277989 := bbase (se 4 (by rfl) ⟨213561, by rfl⟩ : syracuseStep 2277989 = 427123) (by norm_num)
theorem B6488693 : Blo 1518456 6488693 := bbase (se 5 (by rfl) ⟨304157, by rfl⟩ : syracuseStep 6488693 = 608315) (by norm_num)
theorem B1950325 : Blo 1518456 1950325 := bbase (se 5 (by rfl) ⟨91421, by rfl⟩ : syracuseStep 1950325 = 182843) (by norm_num)
theorem B2278013 : Blo 1518456 2278013 := bbase (se 3 (by rfl) ⟨427127, by rfl⟩ : syracuseStep 2278013 = 854255) (by norm_num)
theorem B2925181 : Blo 1518456 2925181 := bbase (se 3 (by rfl) ⟨548471, by rfl⟩ : syracuseStep 2925181 = 1096943) (by norm_num)
theorem B3080845 : Blo 1518456 3080845 := bbase (se 3 (by rfl) ⟨577658, by rfl⟩ : syracuseStep 3080845 = 1155317) (by norm_num)
theorem B2278037 : Blo 1518456 2278037 := bbase (se 6 (by rfl) ⟨53391, by rfl⟩ : syracuseStep 2278037 = 106783) (by norm_num)
theorem B3416741 : Blo 1518456 3416741 := bbase (se 4 (by rfl) ⟨320319, by rfl⟩ : syracuseStep 3416741 = 640639) (by norm_num)
theorem B4866725 : Blo 1518456 4866725 := bbase (se 4 (by rfl) ⟨456255, by rfl⟩ : syracuseStep 4866725 = 912511) (by norm_num)
theorem B2278061 : Blo 1518456 2278061 := bbase (se 3 (by rfl) ⟨427136, by rfl⟩ : syracuseStep 2278061 = 854273) (by norm_num)
theorem B2564797 : Blo 1518456 2564797 := bbase (se 3 (by rfl) ⟨480899, by rfl⟩ : syracuseStep 2564797 = 961799) (by norm_num)
theorem B2278085 : Blo 1518456 2278085 := bbase (se 4 (by rfl) ⟨213570, by rfl⟩ : syracuseStep 2278085 = 427141) (by norm_num)
theorem B1622737 : Blo 1518456 1622737 := bbase (se 2 (by rfl) ⟨608526, by rfl⟩ : syracuseStep 1622737 = 1217053) (by norm_num)
theorem B2278109 : Blo 1518456 2278109 := bbase (se 3 (by rfl) ⟨427145, by rfl⟩ : syracuseStep 2278109 = 854291) (by norm_num)
theorem B3416813 : Blo 1518456 3416813 := bbase (se 3 (by rfl) ⟨640652, by rfl⟩ : syracuseStep 3416813 = 1281305) (by norm_num)
theorem B2433773 : Blo 1518456 2433773 := bbase (se 3 (by rfl) ⟨456332, by rfl⟩ : syracuseStep 2433773 = 912665) (by norm_num)
theorem B2278133 : Blo 1518456 2278133 := bbase (se 5 (by rfl) ⟨106787, by rfl⟩ : syracuseStep 2278133 = 213575) (by norm_num)
theorem B10535669 : Blo 1518456 10535669 := bbase (se 5 (by rfl) ⟨493859, by rfl⟩ : syracuseStep 10535669 = 987719) (by norm_num)
theorem B2884349 : Blo 1518456 2884349 := bbase (se 3 (by rfl) ⟨540815, by rfl⟩ : syracuseStep 2884349 = 1081631) (by norm_num)
theorem B4326149 : Blo 1518456 4326149 := bbase (se 4 (by rfl) ⟨405576, by rfl⟩ : syracuseStep 4326149 = 811153) (by norm_num)
theorem B2278157 : Blo 1518456 2278157 := bbase (se 3 (by rfl) ⟨427154, by rfl⟩ : syracuseStep 2278157 = 854309) (by norm_num)
theorem B2564885 : Blo 1518456 2564885 := bbase (se 6 (by rfl) ⟨60114, by rfl⟩ : syracuseStep 2564885 = 120229) (by norm_num)
theorem B12985109 : Blo 1518456 12985109 := bbase (se 6 (by rfl) ⟨304338, by rfl⟩ : syracuseStep 12985109 = 608677) (by norm_num)
theorem B2278181 : Blo 1518456 2278181 := bbase (se 4 (by rfl) ⟨213579, by rfl⟩ : syracuseStep 2278181 = 427159) (by norm_num)
theorem B1540901 : Blo 1518456 1540901 := bbase (se 4 (by rfl) ⟨144459, by rfl⟩ : syracuseStep 1540901 = 288919) (by norm_num)
theorem B3416885 : Blo 1518456 3416885 := bbase (se 5 (by rfl) ⟨160166, by rfl⟩ : syracuseStep 3416885 = 320333) (by norm_num)
theorem B2278205 : Blo 1518456 2278205 := bbase (se 3 (by rfl) ⟨427163, by rfl⟩ : syracuseStep 2278205 = 854327) (by norm_num)
theorem B1975105 : Blo 1518456 1975105 := bbase (se 2 (by rfl) ⟨740664, by rfl⟩ : syracuseStep 1975105 = 1481329) (by norm_num)
theorem B2278229 : Blo 1518456 2278229 := bbase (se 9 (by rfl) ⟨6674, by rfl⟩ : syracuseStep 2278229 = 13349) (by norm_num)
theorem B2278253 : Blo 1518456 2278253 := bbase (se 3 (by rfl) ⟨427172, by rfl⟩ : syracuseStep 2278253 = 854345) (by norm_num)
theorem B2433901 : Blo 1518456 2433901 := bbase (se 3 (by rfl) ⟨456356, by rfl⟩ : syracuseStep 2433901 = 912713) (by norm_num)
theorem B3416957 : Blo 1518456 3416957 := bbase (se 3 (by rfl) ⟨640679, by rfl⟩ : syracuseStep 3416957 = 1281359) (by norm_num)
theorem B2278277 : Blo 1518456 2278277 := bbase (se 4 (by rfl) ⟨213588, by rfl⟩ : syracuseStep 2278277 = 427177) (by norm_num)
theorem B1622921 : Blo 1518456 1622921 := bbase (se 2 (by rfl) ⟨608595, by rfl⟩ : syracuseStep 1622921 = 1217191) (by norm_num)
theorem B2884501 : Blo 1518456 2884501 := bbase (se 6 (by rfl) ⟨67605, by rfl⟩ : syracuseStep 2884501 = 135211) (by norm_num)
theorem B2565013 : Blo 1518456 2565013 := bbase (se 6 (by rfl) ⟨60117, by rfl⟩ : syracuseStep 2565013 = 120235) (by norm_num)
theorem B2278301 : Blo 1518456 2278301 := bbase (se 3 (by rfl) ⟨427181, by rfl⟩ : syracuseStep 2278301 = 854363) (by norm_num)
theorem B2278325 : Blo 1518456 2278325 := bbase (se 5 (by rfl) ⟨106796, by rfl⟩ : syracuseStep 2278325 = 213593) (by norm_num)
theorem B3417029 : Blo 1518456 3417029 := bbase (se 4 (by rfl) ⟨320346, by rfl⟩ : syracuseStep 3417029 = 640693) (by norm_num)
theorem B2278349 : Blo 1518456 2278349 := bbase (se 3 (by rfl) ⟨427190, by rfl⟩ : syracuseStep 2278349 = 854381) (by norm_num)
theorem B2278373 : Blo 1518456 2278373 := bbase (se 4 (by rfl) ⟨213597, by rfl⟩ : syracuseStep 2278373 = 427195) (by norm_num)
theorem B5129189 : Blo 1518456 5129189 := bbase (se 4 (by rfl) ⟨480861, by rfl⟩ : syracuseStep 5129189 = 961723) (by norm_num)
theorem B2565101 : Blo 1518456 2565101 := bbase (se 3 (by rfl) ⟨480956, by rfl⟩ : syracuseStep 2565101 = 961913) (by norm_num)
theorem B2278397 : Blo 1518456 2278397 := bbase (se 3 (by rfl) ⟨427199, by rfl⟩ : syracuseStep 2278397 = 854399) (by norm_num)
theorem B3417101 : Blo 1518456 3417101 := bbase (se 3 (by rfl) ⟨640706, by rfl⟩ : syracuseStep 3417101 = 1281413) (by norm_num)
theorem B2278421 : Blo 1518456 2278421 := bbase (se 6 (by rfl) ⟨53400, by rfl⟩ : syracuseStep 2278421 = 106801) (by norm_num)
theorem B2278445 : Blo 1518456 2278445 := bbase (se 3 (by rfl) ⟨427208, by rfl⟩ : syracuseStep 2278445 = 854417) (by norm_num)
theorem B2278469 : Blo 1518456 2278469 := bbase (se 4 (by rfl) ⟨213606, by rfl⟩ : syracuseStep 2278469 = 427213) (by norm_num)
theorem B7300165 : Blo 1518456 7300165 := bbase (se 4 (by rfl) ⟨684390, by rfl⟩ : syracuseStep 7300165 = 1368781) (by norm_num)
theorem B1541201 : Blo 1518456 1541201 := bbase (se 2 (by rfl) ⟨577950, by rfl⟩ : syracuseStep 1541201 = 1155901) (by norm_num)
theorem B3417173 : Blo 1518456 3417173 := bbase (se 8 (by rfl) ⟨20022, by rfl⟩ : syracuseStep 3417173 = 40045) (by norm_num)
theorem B2278493 : Blo 1518456 2278493 := bbase (se 3 (by rfl) ⟨427217, by rfl⟩ : syracuseStep 2278493 = 854435) (by norm_num)
theorem B2565229 : Blo 1518456 2565229 := bbase (se 3 (by rfl) ⟨480980, by rfl⟩ : syracuseStep 2565229 = 961961) (by norm_num)
theorem B2278517 : Blo 1518456 2278517 := bbase (se 5 (by rfl) ⟨106805, by rfl⟩ : syracuseStep 2278517 = 213611) (by norm_num)
theorem B4105349 : Blo 1518456 4105349 := bbase (se 4 (by rfl) ⟨384876, by rfl⟩ : syracuseStep 4105349 = 769753) (by norm_num)
theorem B2278541 : Blo 1518456 2278541 := bbase (se 3 (by rfl) ⟨427226, by rfl⟩ : syracuseStep 2278541 = 854453) (by norm_num)
theorem B3417245 : Blo 1518456 3417245 := bbase (se 3 (by rfl) ⟨640733, by rfl⟩ : syracuseStep 3417245 = 1281467) (by norm_num)
theorem B2278565 : Blo 1518456 2278565 := bbase (se 4 (by rfl) ⟨213615, by rfl⟩ : syracuseStep 2278565 = 427231) (by norm_num)
theorem B4867237 : Blo 1518456 4867237 := bbase (se 4 (by rfl) ⟨456303, by rfl⟩ : syracuseStep 4867237 = 912607) (by norm_num)
theorem B12313781 : Blo 1518456 12313781 := bbase (se 5 (by rfl) ⟨577208, by rfl⟩ : syracuseStep 12313781 = 1154417) (by norm_num)
theorem B2278589 : Blo 1518456 2278589 := bbase (se 3 (by rfl) ⟨427235, by rfl⟩ : syracuseStep 2278589 = 854471) (by norm_num)
theorem B2884805 : Blo 1518456 2884805 := bbase (se 4 (by rfl) ⟨270450, by rfl⟩ : syracuseStep 2884805 = 540901) (by norm_num)
theorem B2565317 : Blo 1518456 2565317 := bbase (se 4 (by rfl) ⟨240498, by rfl⟩ : syracuseStep 2565317 = 480997) (by norm_num)
theorem B2278613 : Blo 1518456 2278613 := bbase (se 7 (by rfl) ⟨26702, by rfl⟩ : syracuseStep 2278613 = 53405) (by norm_num)
theorem B3417317 : Blo 1518456 3417317 := bbase (se 4 (by rfl) ⟨320373, by rfl⟩ : syracuseStep 3417317 = 640747) (by norm_num)
theorem B7693541 : Blo 1518456 7693541 := bbase (se 4 (by rfl) ⟨721269, by rfl⟩ : syracuseStep 7693541 = 1442539) (by norm_num)
theorem B2278637 : Blo 1518456 2278637 := bbase (se 3 (by rfl) ⟨427244, by rfl⟩ : syracuseStep 2278637 = 854489) (by norm_num)
theorem B2278661 : Blo 1518456 2278661 := bbase (se 4 (by rfl) ⟨213624, by rfl⟩ : syracuseStep 2278661 = 427249) (by norm_num)
theorem B2278685 : Blo 1518456 2278685 := bbase (se 3 (by rfl) ⟨427253, by rfl⟩ : syracuseStep 2278685 = 854507) (by norm_num)
theorem B3417389 : Blo 1518456 3417389 := bbase (se 3 (by rfl) ⟨640760, by rfl⟩ : syracuseStep 3417389 = 1281521) (by norm_num)
theorem B2278709 : Blo 1518456 2278709 := bbase (se 5 (by rfl) ⟨106814, by rfl⟩ : syracuseStep 2278709 = 213629) (by norm_num)
theorem B2565445 : Blo 1518456 2565445 := bbase (se 4 (by rfl) ⟨240510, by rfl⟩ : syracuseStep 2565445 = 481021) (by norm_num)
theorem B2278733 : Blo 1518456 2278733 := bbase (se 3 (by rfl) ⟨427262, by rfl⟩ : syracuseStep 2278733 = 854525) (by norm_num)
theorem B2278757 : Blo 1518456 2278757 := bbase (se 4 (by rfl) ⟨213633, by rfl⟩ : syracuseStep 2278757 = 427267) (by norm_num)
theorem B3417461 : Blo 1518456 3417461 := bbase (se 5 (by rfl) ⟨160193, by rfl⟩ : syracuseStep 3417461 = 320387) (by norm_num)
theorem B2278781 : Blo 1518456 2278781 := bbase (se 3 (by rfl) ⟨427271, by rfl⟩ : syracuseStep 2278781 = 854543) (by norm_num)
theorem B5473669 : Blo 1518456 5473669 := bbase (se 4 (by rfl) ⟨513156, by rfl⟩ : syracuseStep 5473669 = 1026313) (by norm_num)
theorem B2278805 : Blo 1518456 2278805 := bbase (se 6 (by rfl) ⟨53409, by rfl⟩ : syracuseStep 2278805 = 106819) (by norm_num)
theorem B5129621 : Blo 1518456 5129621 := bbase (se 6 (by rfl) ⟨120225, by rfl⟩ : syracuseStep 5129621 = 240451) (by norm_num)
theorem B11543957 : Blo 1518456 11543957 := bbase (se 6 (by rfl) ⟨270561, by rfl⟩ : syracuseStep 11543957 = 541123) (by norm_num)
theorem B2565533 : Blo 1518456 2565533 := bbase (se 3 (by rfl) ⟨481037, by rfl⟩ : syracuseStep 2565533 = 962075) (by norm_num)
theorem B4326821 : Blo 1518456 4326821 := bbase (se 4 (by rfl) ⟨405639, by rfl⟩ : syracuseStep 4326821 = 811279) (by norm_num)
theorem B2278829 : Blo 1518456 2278829 := bbase (se 3 (by rfl) ⟨427280, by rfl⟩ : syracuseStep 2278829 = 854561) (by norm_num)
theorem B3417533 : Blo 1518456 3417533 := bbase (se 3 (by rfl) ⟨640787, by rfl⟩ : syracuseStep 3417533 = 1281575) (by norm_num)
theorem B3245501 : Blo 1518456 3245501 := bbase (se 3 (by rfl) ⟨608531, by rfl⟩ : syracuseStep 3245501 = 1217063) (by norm_num)
theorem B2278853 : Blo 1518456 2278853 := bbase (se 4 (by rfl) ⟨213642, by rfl⟩ : syracuseStep 2278853 = 427285) (by norm_num)
theorem B2278877 : Blo 1518456 2278877 := bbase (se 3 (by rfl) ⟨427289, by rfl⟩ : syracuseStep 2278877 = 854579) (by norm_num)
theorem B2434541 : Blo 1518456 2434541 := bbase (se 3 (by rfl) ⟨456476, by rfl⟩ : syracuseStep 2434541 = 912953) (by norm_num)
theorem B2278901 : Blo 1518456 2278901 := bbase (se 5 (by rfl) ⟨106823, by rfl⟩ : syracuseStep 2278901 = 213647) (by norm_num)
theorem B3417605 : Blo 1518456 3417605 := bbase (se 4 (by rfl) ⟨320400, by rfl⟩ : syracuseStep 3417605 = 640801) (by norm_num)
theorem B2278925 : Blo 1518456 2278925 := bbase (se 3 (by rfl) ⟨427298, by rfl⟩ : syracuseStep 2278925 = 854597) (by norm_num)
theorem B2565661 : Blo 1518456 2565661 := bbase (se 3 (by rfl) ⟨481061, by rfl⟩ : syracuseStep 2565661 = 962123) (by norm_num)
theorem B2278949 : Blo 1518456 2278949 := bbase (se 4 (by rfl) ⟨213651, by rfl⟩ : syracuseStep 2278949 = 427303) (by norm_num)
theorem B2278973 : Blo 1518456 2278973 := bbase (se 3 (by rfl) ⟨427307, by rfl⟩ : syracuseStep 2278973 = 854615) (by norm_num)
theorem B3417677 : Blo 1518456 3417677 := bbase (se 3 (by rfl) ⟨640814, by rfl⟩ : syracuseStep 3417677 = 1281629) (by norm_num)
theorem B3245645 : Blo 1518456 3245645 := bbase (se 3 (by rfl) ⟨608558, by rfl⟩ : syracuseStep 3245645 = 1217117) (by norm_num)
theorem B2278997 : Blo 1518456 2278997 := bbase (se 8 (by rfl) ⟨13353, by rfl⟩ : syracuseStep 2278997 = 26707) (by norm_num)
theorem B2737757 : Blo 1518456 2737757 := bbase (se 3 (by rfl) ⟨513329, by rfl⟩ : syracuseStep 2737757 = 1026659) (by norm_num)
theorem B2279021 : Blo 1518456 2279021 := bbase (se 3 (by rfl) ⟨427316, by rfl⟩ : syracuseStep 2279021 = 854633) (by norm_num)
theorem B2164333 : Blo 1518456 2164333 := bbase (se 3 (by rfl) ⟨405812, by rfl⟩ : syracuseStep 2164333 = 811625) (by norm_num)
theorem B2565749 : Blo 1518456 2565749 := bbase (se 5 (by rfl) ⟨120269, by rfl⟩ : syracuseStep 2565749 = 240539) (by norm_num)
theorem B2279045 : Blo 1518456 2279045 := bbase (se 4 (by rfl) ⟨213660, by rfl⟩ : syracuseStep 2279045 = 427321) (by norm_num)
theorem B3843733 : Blo 1518456 3843733 := bbase (se 6 (by rfl) ⟨90087, by rfl⟩ : syracuseStep 3843733 = 180175) (by norm_num)
theorem B3417749 : Blo 1518456 3417749 := bbase (se 6 (by rfl) ⟨80103, by rfl⟩ : syracuseStep 3417749 = 160207) (by norm_num)
theorem B2279069 : Blo 1518456 2279069 := bbase (se 3 (by rfl) ⟨427325, by rfl⟩ : syracuseStep 2279069 = 854651) (by norm_num)
theorem B2467493 : Blo 1518456 2467493 := bbase (se 4 (by rfl) ⟨231327, by rfl⟩ : syracuseStep 2467493 = 462655) (by norm_num)
theorem B2279093 : Blo 1518456 2279093 := bbase (se 5 (by rfl) ⟨106832, by rfl⟩ : syracuseStep 2279093 = 213665) (by norm_num)
theorem B2279117 : Blo 1518456 2279117 := bbase (se 3 (by rfl) ⟨427334, by rfl⟩ : syracuseStep 2279117 = 854669) (by norm_num)
theorem B15599317 : Blo 1518456 15599317 := bbase (se 7 (by rfl) ⟨182804, by rfl⟩ : syracuseStep 15599317 = 365609) (by norm_num)
theorem B3417821 : Blo 1518456 3417821 := bbase (se 3 (by rfl) ⟨640841, by rfl⟩ : syracuseStep 3417821 = 1281683) (by norm_num)
theorem B2279141 : Blo 1518456 2279141 := bbase (se 4 (by rfl) ⟨213669, by rfl⟩ : syracuseStep 2279141 = 427339) (by norm_num)
theorem B2279165 : Blo 1518456 2279165 := bbase (se 3 (by rfl) ⟨427343, by rfl⟩ : syracuseStep 2279165 = 854687) (by norm_num)
theorem B3843845 : Blo 1518456 3843845 := bbase (se 4 (by rfl) ⟨360360, by rfl⟩ : syracuseStep 3843845 = 720721) (by norm_num)
theorem B2279189 : Blo 1518456 2279189 := bbase (se 6 (by rfl) ⟨53418, by rfl⟩ : syracuseStep 2279189 = 106837) (by norm_num)
theorem B3417893 : Blo 1518456 3417893 := bbase (se 4 (by rfl) ⟨320427, by rfl⟩ : syracuseStep 3417893 = 640855) (by norm_num)
theorem B2279213 : Blo 1518456 2279213 := bbase (se 3 (by rfl) ⟨427352, by rfl⟩ : syracuseStep 2279213 = 854705) (by norm_num)
theorem B11536181 : Blo 1518456 11536181 := bbase (se 5 (by rfl) ⟨540758, by rfl⟩ : syracuseStep 11536181 = 1081517) (by norm_num)
theorem B2279237 : Blo 1518456 2279237 := bbase (se 4 (by rfl) ⟨213678, by rfl⟩ : syracuseStep 2279237 = 427357) (by norm_num)
theorem B5130053 : Blo 1518456 5130053 := bbase (se 4 (by rfl) ⟨480942, by rfl⟩ : syracuseStep 5130053 = 961885) (by norm_num)
theorem B54077269 : Blo 1518456 54077269 := bbase (se 9 (by rfl) ⟨158429, by rfl⟩ : syracuseStep 54077269 = 316859) (by norm_num)
theorem B4327253 : Blo 1518456 4327253 := bbase (se 9 (by rfl) ⟨12677, by rfl⟩ : syracuseStep 4327253 = 25355) (by norm_num)
theorem B2279261 : Blo 1518456 2279261 := bbase (se 3 (by rfl) ⟨427361, by rfl⟩ : syracuseStep 2279261 = 854723) (by norm_num)
theorem B3417965 : Blo 1518456 3417965 := bbase (se 3 (by rfl) ⟨640868, by rfl⟩ : syracuseStep 3417965 = 1281737) (by norm_num)
theorem B2279285 : Blo 1518456 2279285 := bbase (se 5 (by rfl) ⟨106841, by rfl⟩ : syracuseStep 2279285 = 213683) (by norm_num)
theorem B7604101 : Blo 1518456 7604101 := bbase (se 4 (by rfl) ⟨712884, by rfl⟩ : syracuseStep 7604101 = 1425769) (by norm_num)
theorem B2279309 : Blo 1518456 2279309 := bbase (se 3 (by rfl) ⟨427370, by rfl⟩ : syracuseStep 2279309 = 854741) (by norm_num)
theorem B2279333 : Blo 1518456 2279333 := bbase (se 4 (by rfl) ⟨213687, by rfl⟩ : syracuseStep 2279333 = 427375) (by norm_num)
theorem B3418037 : Blo 1518456 3418037 := bbase (se 5 (by rfl) ⟨160220, by rfl⟩ : syracuseStep 3418037 = 320441) (by norm_num)
theorem B2885557 : Blo 1518456 2885557 := bbase (se 5 (by rfl) ⟨135260, by rfl⟩ : syracuseStep 2885557 = 270521) (by norm_num)
theorem B2434997 : Blo 1518456 2434997 := bbase (se 5 (by rfl) ⟨114140, by rfl⟩ : syracuseStep 2434997 = 228281) (by norm_num)
theorem B2279357 : Blo 1518456 2279357 := bbase (se 3 (by rfl) ⟨427379, by rfl⟩ : syracuseStep 2279357 = 854759) (by norm_num)
theorem B3844037 : Blo 1518456 3844037 := bbase (se 4 (by rfl) ⟨360378, by rfl⟩ : syracuseStep 3844037 = 720757) (by norm_num)
theorem B2279381 : Blo 1518456 2279381 := bbase (se 7 (by rfl) ⟨26711, by rfl⟩ : syracuseStep 2279381 = 53423) (by norm_num)
theorem B2279405 : Blo 1518456 2279405 := bbase (se 3 (by rfl) ⟨427388, by rfl⟩ : syracuseStep 2279405 = 854777) (by norm_num)
theorem B3418109 : Blo 1518456 3418109 := bbase (se 3 (by rfl) ⟨640895, by rfl⟩ : syracuseStep 3418109 = 1281791) (by norm_num)
theorem B2279429 : Blo 1518456 2279429 := bbase (se 4 (by rfl) ⟨213696, by rfl⟩ : syracuseStep 2279429 = 427393) (by norm_num)
theorem B2279453 : Blo 1518456 2279453 := bbase (se 3 (by rfl) ⟨427397, by rfl⟩ : syracuseStep 2279453 = 854795) (by norm_num)
theorem B2279477 : Blo 1518456 2279477 := bbase (se 5 (by rfl) ⟨106850, by rfl⟩ : syracuseStep 2279477 = 213701) (by norm_num)
theorem B3418181 : Blo 1518456 3418181 := bbase (se 4 (by rfl) ⟨320454, by rfl⟩ : syracuseStep 3418181 = 640909) (by norm_num)
theorem B2885701 : Blo 1518456 2885701 := bbase (se 4 (by rfl) ⟨270534, by rfl⟩ : syracuseStep 2885701 = 541069) (by norm_num)
theorem B2279501 : Blo 1518456 2279501 := bbase (se 3 (by rfl) ⟨427406, by rfl⟩ : syracuseStep 2279501 = 854813) (by norm_num)
theorem B2279525 : Blo 1518456 2279525 := bbase (se 4 (by rfl) ⟨213705, by rfl⟩ : syracuseStep 2279525 = 427411) (by norm_num)
theorem B2279549 : Blo 1518456 2279549 := bbase (se 3 (by rfl) ⟨427415, by rfl⟩ : syracuseStep 2279549 = 854831) (by norm_num)
theorem B3418253 : Blo 1518456 3418253 := bbase (se 3 (by rfl) ⟨640922, by rfl⟩ : syracuseStep 3418253 = 1281845) (by norm_num)
theorem B2279573 : Blo 1518456 2279573 := bbase (se 6 (by rfl) ⟨53427, by rfl⟩ : syracuseStep 2279573 = 106855) (by norm_num)
theorem B2435221 : Blo 1518456 2435221 := bbase (se 6 (by rfl) ⟨57075, by rfl⟩ : syracuseStep 2435221 = 114151) (by norm_num)
theorem B2279597 : Blo 1518456 2279597 := bbase (se 3 (by rfl) ⟨427424, by rfl⟩ : syracuseStep 2279597 = 854849) (by norm_num)
theorem B5769413 : Blo 1518456 5769413 := bbase (se 4 (by rfl) ⟨540882, by rfl⟩ : syracuseStep 5769413 = 1081765) (by norm_num)
theorem B2279621 : Blo 1518456 2279621 := bbase (se 4 (by rfl) ⟨213714, by rfl⟩ : syracuseStep 2279621 = 427429) (by norm_num)
theorem B3418325 : Blo 1518456 3418325 := bbase (se 7 (by rfl) ⟨40058, by rfl⟩ : syracuseStep 3418325 = 80117) (by norm_num)
theorem B2435285 : Blo 1518456 2435285 := bbase (se 7 (by rfl) ⟨28538, by rfl⟩ : syracuseStep 2435285 = 57077) (by norm_num)
theorem B2279645 : Blo 1518456 2279645 := bbase (se 3 (by rfl) ⟨427433, by rfl⟩ : syracuseStep 2279645 = 854867) (by norm_num)
theorem B2885861 : Blo 1518456 2885861 := bbase (se 4 (by rfl) ⟨270549, by rfl⟩ : syracuseStep 2885861 = 541099) (by norm_num)
theorem B2279669 : Blo 1518456 2279669 := bbase (se 5 (by rfl) ⟨106859, by rfl⟩ : syracuseStep 2279669 = 213719) (by norm_num)
theorem B5130485 : Blo 1518456 5130485 := bbase (se 5 (by rfl) ⟨240491, by rfl⟩ : syracuseStep 5130485 = 480983) (by norm_num)
theorem B2279693 : Blo 1518456 2279693 := bbase (se 3 (by rfl) ⟨427442, by rfl⟩ : syracuseStep 2279693 = 854885) (by norm_num)
theorem B3844381 : Blo 1518456 3844381 := bbase (se 3 (by rfl) ⟨720821, by rfl⟩ : syracuseStep 3844381 = 1441643) (by norm_num)
theorem B3418397 : Blo 1518456 3418397 := bbase (se 3 (by rfl) ⟨640949, by rfl⟩ : syracuseStep 3418397 = 1281899) (by norm_num)
theorem B2279717 : Blo 1518456 2279717 := bbase (se 4 (by rfl) ⟨213723, by rfl⟩ : syracuseStep 2279717 = 427447) (by norm_num)
theorem B2738485 : Blo 1518456 2738485 := bbase (se 5 (by rfl) ⟨128366, by rfl⟩ : syracuseStep 2738485 = 256733) (by norm_num)
theorem B3246389 : Blo 1518456 3246389 := bbase (se 5 (by rfl) ⟨152174, by rfl⟩ : syracuseStep 3246389 = 304349) (by norm_num)
theorem B2279741 : Blo 1518456 2279741 := bbase (se 3 (by rfl) ⟨427451, by rfl⟩ : syracuseStep 2279741 = 854903) (by norm_num)
theorem B2279765 : Blo 1518456 2279765 := bbase (se 10 (by rfl) ⟨3339, by rfl⟩ : syracuseStep 2279765 = 6679) (by norm_num)
theorem B2435413 : Blo 1518456 2435413 := bbase (se 10 (by rfl) ⟨3567, by rfl⟩ : syracuseStep 2435413 = 7135) (by norm_num)
theorem B3418469 : Blo 1518456 3418469 := bbase (se 4 (by rfl) ⟨320481, by rfl⟩ : syracuseStep 3418469 = 640963) (by norm_num)
theorem B6490469 : Blo 1518456 6490469 := bbase (se 4 (by rfl) ⟨608481, by rfl⟩ : syracuseStep 6490469 = 1216963) (by norm_num)
theorem B2279789 : Blo 1518456 2279789 := bbase (se 3 (by rfl) ⟨427460, by rfl⟩ : syracuseStep 2279789 = 854921) (by norm_num)
theorem B5196149 : Blo 1518456 5196149 := bbase (se 5 (by rfl) ⟨243569, by rfl⟩ : syracuseStep 5196149 = 487139) (by norm_num)
theorem B2886005 : Blo 1518456 2886005 := bbase (se 5 (by rfl) ⟨135281, by rfl⟩ : syracuseStep 2886005 = 270563) (by norm_num)
theorem B2279813 : Blo 1518456 2279813 := bbase (se 4 (by rfl) ⟨213732, by rfl⟩ : syracuseStep 2279813 = 427465) (by norm_num)
theorem B3844493 : Blo 1518456 3844493 := bbase (se 3 (by rfl) ⟨720842, by rfl⟩ : syracuseStep 3844493 = 1441685) (by norm_num)
theorem B2279837 : Blo 1518456 2279837 := bbase (se 3 (by rfl) ⟨427469, by rfl⟩ : syracuseStep 2279837 = 854939) (by norm_num)
theorem B3418541 : Blo 1518456 3418541 := bbase (se 3 (by rfl) ⟨640976, by rfl⟩ : syracuseStep 3418541 = 1281953) (by norm_num)
theorem B6244789 : Blo 1518456 6244789 := bbase (se 5 (by rfl) ⟨292724, by rfl⟩ : syracuseStep 6244789 = 585449) (by norm_num)
theorem B2279861 : Blo 1518456 2279861 := bbase (se 5 (by rfl) ⟨106868, by rfl⟩ : syracuseStep 2279861 = 213737) (by norm_num)
theorem B2279885 : Blo 1518456 2279885 := bbase (se 3 (by rfl) ⟨427478, by rfl⟩ : syracuseStep 2279885 = 854957) (by norm_num)
theorem B5769701 : Blo 1518456 5769701 := bbase (se 4 (by rfl) ⟨540909, by rfl⟩ : syracuseStep 5769701 = 1081819) (by norm_num)
theorem B2279909 : Blo 1518456 2279909 := bbase (se 4 (by rfl) ⟨213741, by rfl⟩ : syracuseStep 2279909 = 427483) (by norm_num)
theorem B3418613 : Blo 1518456 3418613 := bbase (se 5 (by rfl) ⟨160247, by rfl⟩ : syracuseStep 3418613 = 320495) (by norm_num)
theorem B7694837 : Blo 1518456 7694837 := bbase (se 5 (by rfl) ⟨360695, by rfl⟩ : syracuseStep 7694837 = 721391) (by norm_num)
theorem B2279933 : Blo 1518456 2279933 := bbase (se 3 (by rfl) ⟨427487, by rfl⟩ : syracuseStep 2279933 = 854975) (by norm_num)
theorem B2738701 : Blo 1518456 2738701 := bbase (se 3 (by rfl) ⟨513506, by rfl⟩ : syracuseStep 2738701 = 1027013) (by norm_num)
theorem B2279957 : Blo 1518456 2279957 := bbase (se 6 (by rfl) ⟨53436, by rfl⟩ : syracuseStep 2279957 = 106873) (by norm_num)
theorem B2279981 : Blo 1518456 2279981 := bbase (se 3 (by rfl) ⟨427496, by rfl⟩ : syracuseStep 2279981 = 854993) (by norm_num)
theorem B3418685 : Blo 1518456 3418685 := bbase (se 3 (by rfl) ⟨641003, by rfl⟩ : syracuseStep 3418685 = 1282007) (by norm_num)
theorem B4328005 : Blo 1518456 4328005 := bbase (se 4 (by rfl) ⟨405750, by rfl⟩ : syracuseStep 4328005 = 811501) (by norm_num)
theorem B2280005 : Blo 1518456 2280005 := bbase (se 4 (by rfl) ⟨213750, by rfl⟩ : syracuseStep 2280005 = 427501) (by norm_num)
theorem B3844685 : Blo 1518456 3844685 := bbase (se 3 (by rfl) ⟨720878, by rfl⟩ : syracuseStep 3844685 = 1441757) (by norm_num)
theorem B2280029 : Blo 1518456 2280029 := bbase (se 3 (by rfl) ⟨427505, by rfl⟩ : syracuseStep 2280029 = 855011) (by norm_num)
theorem B2280053 : Blo 1518456 2280053 := bbase (se 5 (by rfl) ⟨106877, by rfl⟩ : syracuseStep 2280053 = 213755) (by norm_num)
theorem B3418757 : Blo 1518456 3418757 := bbase (se 4 (by rfl) ⟨320508, by rfl⟩ : syracuseStep 3418757 = 641017) (by norm_num)
theorem B2468485 : Blo 1518456 2468485 := bbase (se 4 (by rfl) ⟨231420, by rfl⟩ : syracuseStep 2468485 = 462841) (by norm_num)
theorem B2280077 : Blo 1518456 2280077 := bbase (se 3 (by rfl) ⟨427514, by rfl⟩ : syracuseStep 2280077 = 855029) (by norm_num)
theorem B2886293 : Blo 1518456 2886293 := bbase (se 6 (by rfl) ⟨67647, by rfl⟩ : syracuseStep 2886293 = 135295) (by norm_num)
theorem B2280101 : Blo 1518456 2280101 := bbase (se 4 (by rfl) ⟨213759, by rfl⟩ : syracuseStep 2280101 = 427519) (by norm_num)
theorem B5130917 : Blo 1518456 5130917 := bbase (se 4 (by rfl) ⟨481023, by rfl⟩ : syracuseStep 5130917 = 962047) (by norm_num)
theorem B2280125 : Blo 1518456 2280125 := bbase (se 3 (by rfl) ⟨427523, by rfl⟩ : syracuseStep 2280125 = 855047) (by norm_num)
theorem B3418829 : Blo 1518456 3418829 := bbase (se 3 (by rfl) ⟨641030, by rfl⟩ : syracuseStep 3418829 = 1282061) (by norm_num)
theorem B2280149 : Blo 1518456 2280149 := bbase (se 7 (by rfl) ⟨26720, by rfl⟩ : syracuseStep 2280149 = 53441) (by norm_num)
theorem B4106981 : Blo 1518456 4106981 := bbase (se 4 (by rfl) ⟨385029, by rfl⟩ : syracuseStep 4106981 = 770059) (by norm_num)
theorem B2280173 : Blo 1518456 2280173 := bbase (se 3 (by rfl) ⟨427532, by rfl⟩ : syracuseStep 2280173 = 855065) (by norm_num)
theorem B2280197 : Blo 1518456 2280197 := bbase (se 4 (by rfl) ⟨213768, by rfl⟩ : syracuseStep 2280197 = 427537) (by norm_num)
theorem B3418901 : Blo 1518456 3418901 := bbase (se 6 (by rfl) ⟨80130, by rfl⟩ : syracuseStep 3418901 = 160261) (by norm_num)
theorem B2280221 : Blo 1518456 2280221 := bbase (se 3 (by rfl) ⟨427541, by rfl⟩ : syracuseStep 2280221 = 855083) (by norm_num)
theorem B2886445 : Blo 1518456 2886445 := bbase (se 3 (by rfl) ⟨541208, by rfl⟩ : syracuseStep 2886445 = 1082417) (by norm_num)
theorem B2280245 : Blo 1518456 2280245 := bbase (se 5 (by rfl) ⟨106886, by rfl⟩ : syracuseStep 2280245 = 213773) (by norm_num)
theorem B2280269 : Blo 1518456 2280269 := bbase (se 3 (by rfl) ⟨427550, by rfl⟩ : syracuseStep 2280269 = 855101) (by norm_num)
theorem B3418973 : Blo 1518456 3418973 := bbase (se 3 (by rfl) ⟨641057, by rfl⟩ : syracuseStep 3418973 = 1282115) (by norm_num)
theorem B2280293 : Blo 1518456 2280293 := bbase (se 4 (by rfl) ⟨213777, by rfl⟩ : syracuseStep 2280293 = 427555) (by norm_num)
theorem B4868981 : Blo 1518456 4868981 := bbase (se 5 (by rfl) ⟨228233, by rfl⟩ : syracuseStep 4868981 = 456467) (by norm_num)
theorem B2280317 : Blo 1518456 2280317 := bbase (se 3 (by rfl) ⟨427559, by rfl⟩ : syracuseStep 2280317 = 855119) (by norm_num)
theorem B2280341 : Blo 1518456 2280341 := bbase (se 6 (by rfl) ⟨53445, by rfl⟩ : syracuseStep 2280341 = 106891) (by norm_num)
theorem B3845029 : Blo 1518456 3845029 := bbase (se 4 (by rfl) ⟨360471, by rfl⟩ : syracuseStep 3845029 = 720943) (by norm_num)
theorem B3419045 : Blo 1518456 3419045 := bbase (se 4 (by rfl) ⟨320535, by rfl⟩ : syracuseStep 3419045 = 641071) (by norm_num)
theorem B2280365 : Blo 1518456 2280365 := bbase (se 3 (by rfl) ⟨427568, by rfl⟩ : syracuseStep 2280365 = 855137) (by norm_num)
theorem B2280389 : Blo 1518456 2280389 := bbase (se 4 (by rfl) ⟨213786, by rfl⟩ : syracuseStep 2280389 = 427573) (by norm_num)
theorem B2280413 : Blo 1518456 2280413 := bbase (se 3 (by rfl) ⟨427577, by rfl⟩ : syracuseStep 2280413 = 855155) (by norm_num)
theorem B3419117 : Blo 1518456 3419117 := bbase (se 3 (by rfl) ⟨641084, by rfl⟩ : syracuseStep 3419117 = 1282169) (by norm_num)
theorem B2280437 : Blo 1518456 2280437 := bbase (se 5 (by rfl) ⟨106895, by rfl⟩ : syracuseStep 2280437 = 213791) (by norm_num)
theorem B2739205 : Blo 1518456 2739205 := bbase (se 4 (by rfl) ⟨256800, by rfl⟩ : syracuseStep 2739205 = 513601) (by norm_num)
theorem B2280461 : Blo 1518456 2280461 := bbase (se 3 (by rfl) ⟨427586, by rfl⟩ : syracuseStep 2280461 = 855173) (by norm_num)
theorem B3845141 : Blo 1518456 3845141 := bbase (se 6 (by rfl) ⟨90120, by rfl⟩ : syracuseStep 3845141 = 180241) (by norm_num)
theorem B2280485 : Blo 1518456 2280485 := bbase (se 4 (by rfl) ⟨213795, by rfl⟩ : syracuseStep 2280485 = 427591) (by norm_num)
theorem B3124261 : Blo 1518456 3124261 := bbase (se 4 (by rfl) ⟨292899, by rfl⟩ : syracuseStep 3124261 = 585799) (by norm_num)
theorem B3247141 : Blo 1518456 3247141 := bbase (se 4 (by rfl) ⟨304419, by rfl⟩ : syracuseStep 3247141 = 608839) (by norm_num)
theorem B3419189 : Blo 1518456 3419189 := bbase (se 5 (by rfl) ⟨160274, by rfl⟩ : syracuseStep 3419189 = 320549) (by norm_num)
theorem B4869173 : Blo 1518456 4869173 := bbase (se 5 (by rfl) ⟨228242, by rfl⟩ : syracuseStep 4869173 = 456485) (by norm_num)
theorem B2280509 : Blo 1518456 2280509 := bbase (se 3 (by rfl) ⟨427595, by rfl⟩ : syracuseStep 2280509 = 855191) (by norm_num)
theorem B2280533 : Blo 1518456 2280533 := bbase (se 8 (by rfl) ⟨13362, by rfl⟩ : syracuseStep 2280533 = 26725) (by norm_num)
theorem B5131349 : Blo 1518456 5131349 := bbase (se 8 (by rfl) ⟨30066, by rfl⟩ : syracuseStep 5131349 = 60133) (by norm_num)
theorem B2280557 : Blo 1518456 2280557 := bbase (se 3 (by rfl) ⟨427604, by rfl⟩ : syracuseStep 2280557 = 855209) (by norm_num)
theorem B3419261 : Blo 1518456 3419261 := bbase (se 3 (by rfl) ⟨641111, by rfl⟩ : syracuseStep 3419261 = 1282223) (by norm_num)
theorem B2280581 : Blo 1518456 2280581 := bbase (se 4 (by rfl) ⟨213804, by rfl⟩ : syracuseStep 2280581 = 427609) (by norm_num)
theorem B2280605 : Blo 1518456 2280605 := bbase (se 3 (by rfl) ⟨427613, by rfl⟩ : syracuseStep 2280605 = 855227) (by norm_num)
theorem B2280629 : Blo 1518456 2280629 := bbase (se 5 (by rfl) ⟨106904, by rfl⟩ : syracuseStep 2280629 = 213809) (by norm_num)
theorem B3247285 : Blo 1518456 3247285 := bbase (se 5 (by rfl) ⟨152216, by rfl⟩ : syracuseStep 3247285 = 304433) (by norm_num)
theorem B3419333 : Blo 1518456 3419333 := bbase (se 4 (by rfl) ⟨320562, by rfl⟩ : syracuseStep 3419333 = 641125) (by norm_num)
theorem B2280653 : Blo 1518456 2280653 := bbase (se 3 (by rfl) ⟨427622, by rfl⟩ : syracuseStep 2280653 = 855245) (by norm_num)
theorem B3845333 : Blo 1518456 3845333 := bbase (se 7 (by rfl) ⟨45062, by rfl⟩ : syracuseStep 3845333 = 90125) (by norm_num)
theorem B2280677 : Blo 1518456 2280677 := bbase (se 4 (by rfl) ⟨213813, by rfl⟩ : syracuseStep 2280677 = 427627) (by norm_num)
theorem B3419405 : Blo 1518456 3419405 := bbase (se 3 (by rfl) ⟨641138, by rfl⟩ : syracuseStep 3419405 = 1282277) (by norm_num)
theorem B6491461 : Blo 1518456 6491461 := bbase (se 4 (by rfl) ⟨608574, by rfl⟩ : syracuseStep 6491461 = 1217149) (by norm_num)
theorem B3419477 : Blo 1518456 3419477 := bbase (se 11 (by rfl) ⟨2504, by rfl⟩ : syracuseStep 3419477 = 5009) (by norm_num)
theorem B5475701 : Blo 1518456 5475701 := bbase (se 5 (by rfl) ⟨256673, by rfl⟩ : syracuseStep 5475701 = 513347) (by norm_num)
theorem B3419549 : Blo 1518456 3419549 := bbase (se 3 (by rfl) ⟨641165, by rfl⟩ : syracuseStep 3419549 = 1282331) (by norm_num)
theorem B3419621 : Blo 1518456 3419621 := bbase (se 4 (by rfl) ⟨320589, by rfl⟩ : syracuseStep 3419621 = 641179) (by norm_num)
theorem B3845677 : Blo 1518456 3845677 := bbase (se 3 (by rfl) ⟨721064, by rfl⟩ : syracuseStep 3845677 = 1442129) (by norm_num)
theorem B3419693 : Blo 1518456 3419693 := bbase (se 3 (by rfl) ⟨641192, by rfl⟩ : syracuseStep 3419693 = 1282385) (by norm_num)
theorem B3649141 : Blo 1518456 3649141 := bbase (se 5 (by rfl) ⟨171053, by rfl⟩ : syracuseStep 3649141 = 342107) (by norm_num)
theorem B3419765 : Blo 1518456 3419765 := bbase (se 5 (by rfl) ⟨160301, by rfl⟩ : syracuseStep 3419765 = 320603) (by norm_num)
theorem B5770885 : Blo 1518456 5770885 := bbase (se 4 (by rfl) ⟨541020, by rfl⟩ : syracuseStep 5770885 = 1082041) (by norm_num)
theorem B3845789 : Blo 1518456 3845789 := bbase (se 3 (by rfl) ⟨721085, by rfl⟩ : syracuseStep 3845789 = 1442171) (by norm_num)
theorem B3419837 : Blo 1518456 3419837 := bbase (se 3 (by rfl) ⟨641219, by rfl⟩ : syracuseStep 3419837 = 1282439) (by norm_num)
theorem B12316373 : Blo 1518456 12316373 := bbase (se 7 (by rfl) ⟨144332, by rfl⟩ : syracuseStep 12316373 = 288665) (by norm_num)
theorem B3419909 : Blo 1518456 3419909 := bbase (se 4 (by rfl) ⟨320616, by rfl⟩ : syracuseStep 3419909 = 641233) (by norm_num)
theorem B7696133 : Blo 1518456 7696133 := bbase (se 4 (by rfl) ⟨721512, by rfl⟩ : syracuseStep 7696133 = 1443025) (by norm_num)
theorem B23383829 : Blo 1518456 23383829 := bbase (se 6 (by rfl) ⟨548058, by rfl⟩ : syracuseStep 23383829 = 1096117) (by norm_num)
theorem B3419981 : Blo 1518456 3419981 := bbase (se 3 (by rfl) ⟨641246, by rfl⟩ : syracuseStep 3419981 = 1282493) (by norm_num)
theorem B4108117 : Blo 1518456 4108117 := bbase (se 9 (by rfl) ⟨12035, by rfl⟩ : syracuseStep 4108117 = 24071) (by norm_num)
theorem B3845981 : Blo 1518456 3845981 := bbase (se 3 (by rfl) ⟨721121, by rfl⟩ : syracuseStep 3845981 = 1442243) (by norm_num)
theorem B1560421 : Blo 1518456 1560421 := bbase (se 4 (by rfl) ⟨146289, by rfl⟩ : syracuseStep 1560421 = 292579) (by norm_num)
theorem B3420053 : Blo 1518456 3420053 := bbase (se 6 (by rfl) ⟨80157, by rfl⟩ : syracuseStep 3420053 = 160315) (by norm_num)
theorem B3698597 : Blo 1518456 3698597 := bbase (se 4 (by rfl) ⟨346743, by rfl⟩ : syracuseStep 3698597 = 693487) (by norm_num)
theorem B5771189 : Blo 1518456 5771189 := bbase (se 5 (by rfl) ⟨270524, by rfl⟩ : syracuseStep 5771189 = 541049) (by norm_num)
theorem B17313749 : Blo 1518456 17313749 := bbase (se 7 (by rfl) ⟨202895, by rfl⟩ : syracuseStep 17313749 = 405791) (by norm_num)
theorem B3420125 : Blo 1518456 3420125 := bbase (se 3 (by rfl) ⟨641273, by rfl⟩ : syracuseStep 3420125 = 1282547) (by norm_num)
theorem B3420197 : Blo 1518456 3420197 := bbase (se 4 (by rfl) ⟨320643, by rfl⟩ : syracuseStep 3420197 = 641287) (by norm_num)
theorem B18493525 : Blo 1518456 18493525 := bbase (se 8 (by rfl) ⟨108360, by rfl⟩ : syracuseStep 18493525 = 216721) (by norm_num)
theorem B3420269 : Blo 1518456 3420269 := bbase (se 3 (by rfl) ⟨641300, by rfl⟩ : syracuseStep 3420269 = 1282601) (by norm_num)
theorem B4108421 : Blo 1518456 4108421 := bbase (se 4 (by rfl) ⟨385164, by rfl⟩ : syracuseStep 4108421 = 770329) (by norm_num)
theorem B7688357 : Blo 1518456 7688357 := bbase (se 4 (by rfl) ⟨720783, by rfl⟩ : syracuseStep 7688357 = 1441567) (by norm_num)
theorem B3846325 : Blo 1518456 3846325 := bbase (se 5 (by rfl) ⟨180296, by rfl⟩ : syracuseStep 3846325 = 360593) (by norm_num)
theorem B3420341 : Blo 1518456 3420341 := bbase (se 5 (by rfl) ⟨160328, by rfl⟩ : syracuseStep 3420341 = 320657) (by norm_num)
theorem B5476565 : Blo 1518456 5476565 := bbase (se 7 (by rfl) ⟨64178, by rfl⟩ : syracuseStep 5476565 = 128357) (by norm_num)
theorem B4681957 : Blo 1518456 4681957 := bbase (se 4 (by rfl) ⟨438933, by rfl⟩ : syracuseStep 4681957 = 877867) (by norm_num)
theorem B1708285 : Blo 1518456 1708285 := bbase (se 3 (by rfl) ⟨320303, by rfl⟩ : syracuseStep 1708285 = 640607) (by norm_num)
theorem B3420413 : Blo 1518456 3420413 := bbase (se 3 (by rfl) ⟨641327, by rfl⟩ : syracuseStep 3420413 = 1282655) (by norm_num)
theorem B1708321 : Blo 1518456 1708321 := bbase (se 2 (by rfl) ⟨640620, by rfl⟩ : syracuseStep 1708321 = 1281241) (by norm_num)
theorem B3846437 : Blo 1518456 3846437 := bbase (se 4 (by rfl) ⟨360603, by rfl⟩ : syracuseStep 3846437 = 721207) (by norm_num)
theorem B3649853 : Blo 1518456 3649853 := bbase (se 3 (by rfl) ⟨684347, by rfl⟩ : syracuseStep 3649853 = 1368695) (by norm_num)
theorem B1708357 : Blo 1518456 1708357 := bbase (se 4 (by rfl) ⟨160158, by rfl⟩ : syracuseStep 1708357 = 320317) (by norm_num)
theorem B3420485 : Blo 1518456 3420485 := bbase (se 4 (by rfl) ⟨320670, by rfl⟩ : syracuseStep 3420485 = 641341) (by norm_num)
theorem B1708393 : Blo 1518456 1708393 := bbase (se 2 (by rfl) ⟨640647, by rfl⟩ : syracuseStep 1708393 = 1281295) (by norm_num)
theorem B5271925 : Blo 1518456 5271925 := bbase (se 5 (by rfl) ⟨247121, by rfl⟩ : syracuseStep 5271925 = 494243) (by norm_num)
theorem B1708429 : Blo 1518456 1708429 := bbase (se 3 (by rfl) ⟨320330, by rfl⟩ : syracuseStep 1708429 = 640661) (by norm_num)
theorem B3420557 : Blo 1518456 3420557 := bbase (se 3 (by rfl) ⟨641354, by rfl⟩ : syracuseStep 3420557 = 1282709) (by norm_num)
theorem B16437653 : Blo 1518456 16437653 := bbase (se 6 (by rfl) ⟨385257, by rfl⟩ : syracuseStep 16437653 = 770515) (by norm_num)
theorem B1708465 : Blo 1518456 1708465 := bbase (se 2 (by rfl) ⟨640674, by rfl⟩ : syracuseStep 1708465 = 1281349) (by norm_num)
theorem B3699133 : Blo 1518456 3699133 := bbase (se 3 (by rfl) ⟨693587, by rfl⟩ : syracuseStep 3699133 = 1387175) (by norm_num)
theorem B1708501 : Blo 1518456 1708501 := bbase (se 7 (by rfl) ⟨20021, by rfl⟩ : syracuseStep 1708501 = 40043) (by norm_num)
theorem B3420629 : Blo 1518456 3420629 := bbase (se 7 (by rfl) ⟨40085, by rfl⟩ : syracuseStep 3420629 = 80171) (by norm_num)
theorem B3846629 : Blo 1518456 3846629 := bbase (se 4 (by rfl) ⟨360621, by rfl⟩ : syracuseStep 3846629 = 721243) (by norm_num)
theorem B1708537 : Blo 1518456 1708537 := bbase (se 2 (by rfl) ⟨640701, by rfl⟩ : syracuseStep 1708537 = 1281403) (by norm_num)
theorem B1708573 : Blo 1518456 1708573 := bbase (se 3 (by rfl) ⟨320357, by rfl⟩ : syracuseStep 1708573 = 640715) (by norm_num)
theorem B3420701 : Blo 1518456 3420701 := bbase (se 3 (by rfl) ⟨641381, by rfl⟩ : syracuseStep 3420701 = 1282763) (by norm_num)
theorem B1708609 : Blo 1518456 1708609 := bbase (se 2 (by rfl) ⟨640728, by rfl⟩ : syracuseStep 1708609 = 1281457) (by norm_num)
theorem B1708645 : Blo 1518456 1708645 := bbase (se 4 (by rfl) ⟨160185, by rfl⟩ : syracuseStep 1708645 = 320371) (by norm_num)
theorem B3420773 : Blo 1518456 3420773 := bbase (se 4 (by rfl) ⟨320697, by rfl⟩ : syracuseStep 3420773 = 641395) (by norm_num)
theorem B1708681 : Blo 1518456 1708681 := bbase (se 2 (by rfl) ⟨640755, by rfl⟩ : syracuseStep 1708681 = 1281511) (by norm_num)
theorem B1708717 : Blo 1518456 1708717 := bbase (se 3 (by rfl) ⟨320384, by rfl⟩ : syracuseStep 1708717 = 640769) (by norm_num)
theorem B3420845 : Blo 1518456 3420845 := bbase (se 3 (by rfl) ⟨641408, by rfl⟩ : syracuseStep 3420845 = 1282817) (by norm_num)
theorem B6927029 : Blo 1518456 6927029 := bbase (se 5 (by rfl) ⟨324704, by rfl⟩ : syracuseStep 6927029 = 649409) (by norm_num)
theorem B3650237 : Blo 1518456 3650237 := bbase (se 3 (by rfl) ⟨684419, by rfl⟩ : syracuseStep 3650237 = 1368839) (by norm_num)
theorem B1708753 : Blo 1518456 1708753 := bbase (se 2 (by rfl) ⟨640782, by rfl⟩ : syracuseStep 1708753 = 1281565) (by norm_num)
theorem B1708789 : Blo 1518456 1708789 := bbase (se 5 (by rfl) ⟨80099, by rfl⟩ : syracuseStep 1708789 = 160199) (by norm_num)
theorem B3420917 : Blo 1518456 3420917 := bbase (se 5 (by rfl) ⟨160355, by rfl⟩ : syracuseStep 3420917 = 320711) (by norm_num)
theorem B5124869 : Blo 1518456 5124869 := bbase (se 4 (by rfl) ⟨480456, by rfl⟩ : syracuseStep 5124869 = 960913) (by norm_num)
theorem B1921801 : Blo 1518456 1921801 := bbase (se 2 (by rfl) ⟨720675, by rfl⟩ : syracuseStep 1921801 = 1441351) (by norm_num)
theorem B1708825 : Blo 1518456 1708825 := bbase (se 2 (by rfl) ⟨640809, by rfl⟩ : syracuseStep 1708825 = 1281619) (by norm_num)
theorem B1708861 : Blo 1518456 1708861 := bbase (se 3 (by rfl) ⟨320411, by rfl⟩ : syracuseStep 1708861 = 640823) (by norm_num)
theorem B3846973 : Blo 1518456 3846973 := bbase (se 3 (by rfl) ⟨721307, by rfl⟩ : syracuseStep 3846973 = 1442615) (by norm_num)
theorem B3420989 : Blo 1518456 3420989 := bbase (se 3 (by rfl) ⟨641435, by rfl⟩ : syracuseStep 3420989 = 1282871) (by norm_num)
theorem B1708897 : Blo 1518456 1708897 := bbase (se 2 (by rfl) ⟨640836, by rfl⟩ : syracuseStep 1708897 = 1281673) (by norm_num)
theorem B1921897 : Blo 1518456 1921897 := bbase (se 2 (by rfl) ⟨720711, by rfl⟩ : syracuseStep 1921897 = 1441423) (by norm_num)
theorem B1708933 : Blo 1518456 1708933 := bbase (se 4 (by rfl) ⟨160212, by rfl⟩ : syracuseStep 1708933 = 320425) (by norm_num)
theorem B1708969 : Blo 1518456 1708969 := bbase (se 2 (by rfl) ⟨640863, by rfl⟩ : syracuseStep 1708969 = 1281727) (by norm_num)
theorem B3847085 : Blo 1518456 3847085 := bbase (se 3 (by rfl) ⟨721328, by rfl⟩ : syracuseStep 3847085 = 1442657) (by norm_num)
theorem B1561529 : Blo 1518456 1561529 := bbase (se 2 (by rfl) ⟨585573, by rfl⟩ : syracuseStep 1561529 = 1171147) (by norm_num)
theorem B1709005 : Blo 1518456 1709005 := bbase (se 3 (by rfl) ⟨320438, by rfl⟩ : syracuseStep 1709005 = 640877) (by norm_num)
theorem B10539989 : Blo 1518456 10539989 := bbase (se 7 (by rfl) ⟨123515, by rfl⟩ : syracuseStep 10539989 = 247031) (by norm_num)
theorem B2053085 : Blo 1518456 2053085 := bbase (se 3 (by rfl) ⟨384953, by rfl⟩ : syracuseStep 2053085 = 769907) (by norm_num)
theorem B3650525 : Blo 1518456 3650525 := bbase (se 3 (by rfl) ⟨684473, by rfl⟩ : syracuseStep 3650525 = 1368947) (by norm_num)
theorem B4109285 : Blo 1518456 4109285 := bbase (se 4 (by rfl) ⟨385245, by rfl⟩ : syracuseStep 4109285 = 770491) (by norm_num)
theorem B1709041 : Blo 1518456 1709041 := bbase (se 2 (by rfl) ⟨640890, by rfl⟩ : syracuseStep 1709041 = 1281781) (by norm_num)
theorem B1922069 : Blo 1518456 1922069 := bbase (se 6 (by rfl) ⟨45048, by rfl⟩ : syracuseStep 1922069 = 90097) (by norm_num)
theorem B1709077 : Blo 1518456 1709077 := bbase (se 6 (by rfl) ⟨40056, by rfl⟩ : syracuseStep 1709077 = 80113) (by norm_num)
theorem B1709113 : Blo 1518456 1709113 := bbase (se 2 (by rfl) ⟨640917, by rfl⟩ : syracuseStep 1709113 = 1281835) (by norm_num)
theorem B1922125 : Blo 1518456 1922125 := bbase (se 3 (by rfl) ⟨360398, by rfl⟩ : syracuseStep 1922125 = 720797) (by norm_num)
theorem B1709149 : Blo 1518456 1709149 := bbase (se 3 (by rfl) ⟨320465, by rfl⟩ : syracuseStep 1709149 = 640931) (by norm_num)
theorem B3847277 : Blo 1518456 3847277 := bbase (se 3 (by rfl) ⟨721364, by rfl⟩ : syracuseStep 3847277 = 1442729) (by norm_num)
theorem B1709185 : Blo 1518456 1709185 := bbase (se 2 (by rfl) ⟨640944, by rfl⟩ : syracuseStep 1709185 = 1281889) (by norm_num)
theorem B1709221 : Blo 1518456 1709221 := bbase (se 4 (by rfl) ⟨160239, by rfl⟩ : syracuseStep 1709221 = 320479) (by norm_num)
theorem B1922221 : Blo 1518456 1922221 := bbase (se 3 (by rfl) ⟨360416, by rfl⟩ : syracuseStep 1922221 = 720833) (by norm_num)
theorem B5125301 : Blo 1518456 5125301 := bbase (se 5 (by rfl) ⟨240248, by rfl⟩ : syracuseStep 5125301 = 480497) (by norm_num)
theorem B3290309 : Blo 1518456 3290309 := bbase (se 4 (by rfl) ⟨308466, by rfl⟩ : syracuseStep 3290309 = 616933) (by norm_num)
theorem B1709257 : Blo 1518456 1709257 := bbase (se 2 (by rfl) ⟨640971, by rfl⟩ : syracuseStep 1709257 = 1281943) (by norm_num)
theorem B1709293 : Blo 1518456 1709293 := bbase (se 3 (by rfl) ⟨320492, by rfl⟩ : syracuseStep 1709293 = 640985) (by norm_num)
theorem B1709329 : Blo 1518456 1709329 := bbase (se 2 (by rfl) ⟨640998, by rfl⟩ : syracuseStep 1709329 = 1281997) (by norm_num)
theorem B12326165 : Blo 1518456 12326165 := bbase (se 6 (by rfl) ⟨288894, by rfl⟩ : syracuseStep 12326165 = 577789) (by norm_num)
theorem B1709365 : Blo 1518456 1709365 := bbase (se 5 (by rfl) ⟨80126, by rfl⟩ : syracuseStep 1709365 = 160253) (by norm_num)
theorem B1922393 : Blo 1518456 1922393 := bbase (se 2 (by rfl) ⟨720897, by rfl⟩ : syracuseStep 1922393 = 1441795) (by norm_num)
theorem B1709401 : Blo 1518456 1709401 := bbase (se 2 (by rfl) ⟨641025, by rfl⟩ : syracuseStep 1709401 = 1282051) (by norm_num)
theorem B1709437 : Blo 1518456 1709437 := bbase (se 3 (by rfl) ⟨320519, by rfl⟩ : syracuseStep 1709437 = 641039) (by norm_num)
theorem B1922449 : Blo 1518456 1922449 := bbase (se 2 (by rfl) ⟨720918, by rfl⟩ : syracuseStep 1922449 = 1441837) (by norm_num)
theorem B1709473 : Blo 1518456 1709473 := bbase (se 2 (by rfl) ⟨641052, by rfl⟩ : syracuseStep 1709473 = 1282105) (by norm_num)
theorem B7689653 : Blo 1518456 7689653 := bbase (se 5 (by rfl) ⟨360452, by rfl⟩ : syracuseStep 7689653 = 720905) (by norm_num)
theorem B1709509 : Blo 1518456 1709509 := bbase (se 4 (by rfl) ⟨160266, by rfl⟩ : syracuseStep 1709509 = 320533) (by norm_num)
theorem B3847621 : Blo 1518456 3847621 := bbase (se 4 (by rfl) ⟨360714, by rfl⟩ : syracuseStep 3847621 = 721429) (by norm_num)
theorem B1709545 : Blo 1518456 1709545 := bbase (se 2 (by rfl) ⟨641079, by rfl⟩ : syracuseStep 1709545 = 1282159) (by norm_num)
theorem B1922545 : Blo 1518456 1922545 := bbase (se 2 (by rfl) ⟨720954, by rfl⟩ : syracuseStep 1922545 = 1441909) (by norm_num)
theorem B1709581 : Blo 1518456 1709581 := bbase (se 3 (by rfl) ⟨320546, by rfl⟩ : syracuseStep 1709581 = 641093) (by norm_num)
theorem B2053669 : Blo 1518456 2053669 := bbase (se 4 (by rfl) ⟨192531, by rfl⟩ : syracuseStep 2053669 = 385063) (by norm_num)
theorem B7304741 : Blo 1518456 7304741 := bbase (se 4 (by rfl) ⟨684819, by rfl⟩ : syracuseStep 7304741 = 1369639) (by norm_num)
theorem B1709617 : Blo 1518456 1709617 := bbase (se 2 (by rfl) ⟨641106, by rfl⟩ : syracuseStep 1709617 = 1282213) (by norm_num)
theorem B3847733 : Blo 1518456 3847733 := bbase (se 5 (by rfl) ⟨180362, by rfl⟩ : syracuseStep 3847733 = 360725) (by norm_num)
theorem B1709653 : Blo 1518456 1709653 := bbase (se 8 (by rfl) ⟨10017, by rfl⟩ : syracuseStep 1709653 = 20035) (by norm_num)
theorem B5125733 : Blo 1518456 5125733 := bbase (se 4 (by rfl) ⟨480537, by rfl⟩ : syracuseStep 5125733 = 961075) (by norm_num)
theorem B8648309 : Blo 1518456 8648309 := bbase (se 5 (by rfl) ⟨405389, by rfl⟩ : syracuseStep 8648309 = 810779) (by norm_num)
theorem B1709689 : Blo 1518456 1709689 := bbase (se 2 (by rfl) ⟨641133, by rfl⟩ : syracuseStep 1709689 = 1282267) (by norm_num)
theorem B1922717 : Blo 1518456 1922717 := bbase (se 3 (by rfl) ⟨360509, by rfl⟩ : syracuseStep 1922717 = 721019) (by norm_num)
theorem B1709725 : Blo 1518456 1709725 := bbase (se 3 (by rfl) ⟨320573, by rfl⟩ : syracuseStep 1709725 = 641147) (by norm_num)
theorem B1709761 : Blo 1518456 1709761 := bbase (se 2 (by rfl) ⟨641160, by rfl⟩ : syracuseStep 1709761 = 1282321) (by norm_num)
theorem B3749573 : Blo 1518456 3749573 := bbase (se 4 (by rfl) ⟨351522, by rfl⟩ : syracuseStep 3749573 = 703045) (by norm_num)
theorem B2053837 : Blo 1518456 2053837 := bbase (se 3 (by rfl) ⟨385094, by rfl⟩ : syracuseStep 2053837 = 770189) (by norm_num)
theorem B1922773 : Blo 1518456 1922773 := bbase (se 7 (by rfl) ⟨22532, by rfl⟩ : syracuseStep 1922773 = 45065) (by norm_num)
theorem B10401493 : Blo 1518456 10401493 := bbase (se 7 (by rfl) ⟨121892, by rfl⟩ : syracuseStep 10401493 = 243785) (by norm_num)
theorem B1709797 : Blo 1518456 1709797 := bbase (se 4 (by rfl) ⟨160293, by rfl⟩ : syracuseStep 1709797 = 320587) (by norm_num)
theorem B3847925 : Blo 1518456 3847925 := bbase (se 5 (by rfl) ⟨180371, by rfl⟩ : syracuseStep 3847925 = 360743) (by norm_num)
theorem B1709833 : Blo 1518456 1709833 := bbase (se 2 (by rfl) ⟨641187, by rfl⟩ : syracuseStep 1709833 = 1282375) (by norm_num)
theorem B1709869 : Blo 1518456 1709869 := bbase (se 3 (by rfl) ⟨320600, by rfl⟩ : syracuseStep 1709869 = 641201) (by norm_num)
theorem B1922869 : Blo 1518456 1922869 := bbase (se 5 (by rfl) ⟨90134, by rfl⟩ : syracuseStep 1922869 = 180269) (by norm_num)
theorem B1709905 : Blo 1518456 1709905 := bbase (se 2 (by rfl) ⟨641214, by rfl⟩ : syracuseStep 1709905 = 1282429) (by norm_num)
theorem B13154165 : Blo 1518456 13154165 := bbase (se 5 (by rfl) ⟨616601, by rfl⟩ : syracuseStep 13154165 = 1233203) (by norm_num)
theorem B1709941 : Blo 1518456 1709941 := bbase (se 5 (by rfl) ⟨80153, by rfl⟩ : syracuseStep 1709941 = 160307) (by norm_num)
theorem B1709977 : Blo 1518456 1709977 := bbase (se 2 (by rfl) ⟨641241, by rfl⟩ : syracuseStep 1709977 = 1282483) (by norm_num)
theorem B1710013 : Blo 1518456 1710013 := bbase (se 3 (by rfl) ⟨320627, by rfl⟩ : syracuseStep 1710013 = 641255) (by norm_num)
theorem B1923041 : Blo 1518456 1923041 := bbase (se 2 (by rfl) ⟨721140, by rfl⟩ : syracuseStep 1923041 = 1442281) (by norm_num)
theorem B1710049 : Blo 1518456 1710049 := bbase (se 2 (by rfl) ⟨641268, by rfl⟩ : syracuseStep 1710049 = 1282537) (by norm_num)
theorem B1710085 : Blo 1518456 1710085 := bbase (se 4 (by rfl) ⟨160320, by rfl⟩ : syracuseStep 1710085 = 320641) (by norm_num)
theorem B5126165 : Blo 1518456 5126165 := bbase (se 6 (by rfl) ⟨120144, by rfl⟩ : syracuseStep 5126165 = 240289) (by norm_num)
theorem B4446229 : Blo 1518456 4446229 := bbase (se 6 (by rfl) ⟨104208, by rfl⟩ : syracuseStep 4446229 = 208417) (by norm_num)
theorem B1923097 : Blo 1518456 1923097 := bbase (se 2 (by rfl) ⟨721161, by rfl⟩ : syracuseStep 1923097 = 1442323) (by norm_num)
theorem B1710121 : Blo 1518456 1710121 := bbase (se 2 (by rfl) ⟨641295, by rfl⟩ : syracuseStep 1710121 = 1282591) (by norm_num)
theorem B1710157 : Blo 1518456 1710157 := bbase (se 3 (by rfl) ⟨320654, by rfl⟩ : syracuseStep 1710157 = 641309) (by norm_num)
theorem B3848269 : Blo 1518456 3848269 := bbase (se 3 (by rfl) ⟨721550, by rfl⟩ : syracuseStep 3848269 = 1443101) (by norm_num)
theorem B1710193 : Blo 1518456 1710193 := bbase (se 2 (by rfl) ⟨641322, by rfl⟩ : syracuseStep 1710193 = 1282645) (by norm_num)
theorem B1923193 : Blo 1518456 1923193 := bbase (se 2 (by rfl) ⟨721197, by rfl⟩ : syracuseStep 1923193 = 1442395) (by norm_num)
theorem B1710229 : Blo 1518456 1710229 := bbase (se 6 (by rfl) ⟨40083, by rfl⟩ : syracuseStep 1710229 = 80167) (by norm_num)
theorem B1710265 : Blo 1518456 1710265 := bbase (se 2 (by rfl) ⟨641349, by rfl⟩ : syracuseStep 1710265 = 1282699) (by norm_num)
theorem B3848381 : Blo 1518456 3848381 := bbase (se 3 (by rfl) ⟨721571, by rfl⟩ : syracuseStep 3848381 = 1443143) (by norm_num)
theorem B1710301 : Blo 1518456 1710301 := bbase (se 3 (by rfl) ⟨320681, by rfl⟩ : syracuseStep 1710301 = 641363) (by norm_num)
theorem B1710337 : Blo 1518456 1710337 := bbase (se 2 (by rfl) ⟨641376, by rfl⟩ : syracuseStep 1710337 = 1282753) (by norm_num)
theorem B1923365 : Blo 1518456 1923365 := bbase (se 4 (by rfl) ⟨180315, by rfl⟩ : syracuseStep 1923365 = 360631) (by norm_num)
theorem B1710373 : Blo 1518456 1710373 := bbase (se 4 (by rfl) ⟨160347, by rfl⟩ : syracuseStep 1710373 = 320695) (by norm_num)
theorem B1710409 : Blo 1518456 1710409 := bbase (se 2 (by rfl) ⟨641403, by rfl⟩ : syracuseStep 1710409 = 1282807) (by norm_num)
theorem B140433749 : Blo 1518456 140433749 := bbase (se 10 (by rfl) ⟨205713, by rfl⟩ : syracuseStep 140433749 = 411427) (by norm_num)
theorem B1923421 : Blo 1518456 1923421 := bbase (se 3 (by rfl) ⟨360641, by rfl⟩ : syracuseStep 1923421 = 721283) (by norm_num)
theorem B1710445 : Blo 1518456 1710445 := bbase (se 3 (by rfl) ⟨320708, by rfl⟩ : syracuseStep 1710445 = 641417) (by norm_num)
theorem B2562421 : Blo 1518456 2562421 := bbase (se 5 (by rfl) ⟨120113, by rfl⟩ : syracuseStep 2562421 = 240227) (by norm_num)
theorem B7297397 : Blo 1518456 7297397 := bbase (se 5 (by rfl) ⟨342065, by rfl⟩ : syracuseStep 7297397 = 684131) (by norm_num)
theorem B3848573 : Blo 1518456 3848573 := bbase (se 3 (by rfl) ⟨721607, by rfl⟩ : syracuseStep 3848573 = 1443215) (by norm_num)
theorem B1710481 : Blo 1518456 1710481 := bbase (se 2 (by rfl) ⟨641430, by rfl⟩ : syracuseStep 1710481 = 1282861) (by norm_num)
theorem B5765525 : Blo 1518456 5765525 := bbase (se 6 (by rfl) ⟨135129, by rfl⟩ : syracuseStep 5765525 = 270259) (by norm_num)
theorem B1923517 : Blo 1518456 1923517 := bbase (se 3 (by rfl) ⟨360659, by rfl⟩ : syracuseStep 1923517 = 721319) (by norm_num)
theorem B5126597 : Blo 1518456 5126597 := bbase (se 4 (by rfl) ⟨480618, by rfl⟩ : syracuseStep 5126597 = 961237) (by norm_num)
theorem B2562509 : Blo 1518456 2562509 := bbase (se 3 (by rfl) ⟨480470, by rfl⟩ : syracuseStep 2562509 = 960941) (by norm_num)
theorem B3463741 : Blo 1518456 3463741 := bbase (se 3 (by rfl) ⟨649451, by rfl⟩ : syracuseStep 3463741 = 1298903) (by norm_num)
theorem B2562637 : Blo 1518456 2562637 := bbase (se 3 (by rfl) ⟨480494, by rfl⟩ : syracuseStep 2562637 = 960989) (by norm_num)
theorem B29219413 : Blo 1518456 29219413 := bbase (se 8 (by rfl) ⟨171207, by rfl⟩ : syracuseStep 29219413 = 342415) (by norm_num)
theorem B1923689 : Blo 1518456 1923689 := bbase (se 2 (by rfl) ⟨721383, by rfl⟩ : syracuseStep 1923689 = 1442767) (by norm_num)
theorem B1923745 : Blo 1518456 1923745 := bbase (se 2 (by rfl) ⟨721404, by rfl⟩ : syracuseStep 1923745 = 1442809) (by norm_num)
theorem B2562725 : Blo 1518456 2562725 := bbase (se 4 (by rfl) ⟨240255, by rfl⟩ : syracuseStep 2562725 = 480511) (by norm_num)
theorem B5765813 : Blo 1518456 5765813 := bbase (se 5 (by rfl) ⟨270272, by rfl⟩ : syracuseStep 5765813 = 540545) (by norm_num)
theorem B7690949 : Blo 1518456 7690949 := bbase (se 4 (by rfl) ⟨721026, by rfl⟩ : syracuseStep 7690949 = 1442053) (by norm_num)
theorem B20798165 : Blo 1518456 20798165 := bbase (se 7 (by rfl) ⟨243728, by rfl⟩ : syracuseStep 20798165 = 487457) (by norm_num)
theorem B1923841 : Blo 1518456 1923841 := bbase (se 2 (by rfl) ⟨721440, by rfl⟩ : syracuseStep 1923841 = 1442881) (by norm_num)
theorem B2562853 : Blo 1518456 2562853 := bbase (se 4 (by rfl) ⟨240267, by rfl⟩ : syracuseStep 2562853 = 480535) (by norm_num)
theorem B12983125 : Blo 1518456 12983125 := bbase (se 9 (by rfl) ⟨38036, by rfl⟩ : syracuseStep 12983125 = 76073) (by norm_num)
theorem B28113749 : Blo 1518456 28113749 := bbase (se 9 (by rfl) ⟨82364, by rfl⟩ : syracuseStep 28113749 = 164729) (by norm_num)
theorem B1825637 : Blo 1518456 1825637 := bbase (se 4 (by rfl) ⟨171153, by rfl⟩ : syracuseStep 1825637 = 342307) (by norm_num)
theorem B5127029 : Blo 1518456 5127029 := bbase (se 5 (by rfl) ⟨240329, by rfl⟩ : syracuseStep 5127029 = 480659) (by norm_num)
theorem B2562941 : Blo 1518456 2562941 := bbase (se 3 (by rfl) ⟨480551, by rfl⟩ : syracuseStep 2562941 = 961103) (by norm_num)
theorem B1924013 : Blo 1518456 1924013 := bbase (se 3 (by rfl) ⟨360752, by rfl⟩ : syracuseStep 1924013 = 721505) (by norm_num)
theorem B1645501 : Blo 1518456 1645501 := bbase (se 3 (by rfl) ⟨308531, by rfl⟩ : syracuseStep 1645501 = 617063) (by norm_num)
theorem B1924069 : Blo 1518456 1924069 := bbase (se 4 (by rfl) ⟨180381, by rfl⟩ : syracuseStep 1924069 = 360763) (by norm_num)
theorem B2563069 : Blo 1518456 2563069 := bbase (se 3 (by rfl) ⟨480575, by rfl⟩ : syracuseStep 2563069 = 961151) (by norm_num)
theorem B1825849 : Blo 1518456 1825849 := bbase (se 2 (by rfl) ⟨684693, by rfl⟩ : syracuseStep 1825849 = 1369387) (by norm_num)
theorem B1924165 : Blo 1518456 1924165 := bbase (se 4 (by rfl) ⟨180390, by rfl⟩ : syracuseStep 1924165 = 360781) (by norm_num)
theorem B2563157 : Blo 1518456 2563157 := bbase (se 8 (by rfl) ⟨15018, by rfl⟩ : syracuseStep 2563157 = 30037) (by norm_num)
theorem B1539181 : Blo 1518456 1539181 := bbase (se 3 (by rfl) ⟨288596, by rfl⟩ : syracuseStep 1539181 = 577193) (by norm_num)
theorem B2309285 : Blo 1518456 2309285 := bbase (se 4 (by rfl) ⟨216495, by rfl⟩ : syracuseStep 2309285 = 432991) (by norm_num)
theorem B1825993 : Blo 1518456 1825993 := bbase (se 2 (by rfl) ⟨684747, by rfl⟩ : syracuseStep 1825993 = 1369495) (by norm_num)
theorem B4324565 : Blo 1518456 4324565 := bbase (se 7 (by rfl) ⟨50678, by rfl⟩ : syracuseStep 4324565 = 101357) (by norm_num)
theorem B2563285 : Blo 1518456 2563285 := bbase (se 7 (by rfl) ⟨30038, by rfl⟩ : syracuseStep 2563285 = 60077) (by norm_num)
theorem B2923733 : Blo 1518456 2923733 := bbase (se 7 (by rfl) ⟨34262, by rfl⟩ : syracuseStep 2923733 = 68525) (by norm_num)
theorem B3243253 : Blo 1518456 3243253 := bbase (se 5 (by rfl) ⟨152027, by rfl⟩ : syracuseStep 3243253 = 304055) (by norm_num)
theorem B8658197 : Blo 1518456 8658197 := bbase (se 6 (by rfl) ⟨202926, by rfl⟩ : syracuseStep 8658197 = 405853) (by norm_num)
theorem B5127461 : Blo 1518456 5127461 := bbase (se 4 (by rfl) ⟨480699, by rfl⟩ : syracuseStep 5127461 = 961399) (by norm_num)
theorem B2882861 : Blo 1518456 2882861 := bbase (se 3 (by rfl) ⟨540536, by rfl⟩ : syracuseStep 2882861 = 1081073) (by norm_num)
theorem B2563373 : Blo 1518456 2563373 := bbase (se 3 (by rfl) ⟨480632, by rfl⟩ : syracuseStep 2563373 = 961265) (by norm_num)
theorem B14794069 : Blo 1518456 14794069 := bbase (se 11 (by rfl) ⟨10835, by rfl⟩ : syracuseStep 14794069 = 21671) (by norm_num)
theorem B1539425 : Blo 1518456 1539425 := bbase (se 2 (by rfl) ⟨577284, by rfl⟩ : syracuseStep 1539425 = 1154569) (by norm_num)
theorem B1949053 : Blo 1518456 1949053 := bbase (se 3 (by rfl) ⟨365447, by rfl⟩ : syracuseStep 1949053 = 730895) (by norm_num)
theorem B1539473 : Blo 1518456 1539473 := bbase (se 2 (by rfl) ⟨577302, by rfl⟩ : syracuseStep 1539473 = 1154605) (by norm_num)
theorem B2563501 : Blo 1518456 2563501 := bbase (se 3 (by rfl) ⟨480656, by rfl⟩ : syracuseStep 2563501 = 961313) (by norm_num)
theorem B2563589 : Blo 1518456 2563589 := bbase (se 4 (by rfl) ⟨240336, by rfl⟩ : syracuseStep 2563589 = 480673) (by norm_num)
theorem B2252405 : Blo 1518456 2252405 := bbase (se 5 (by rfl) ⟨105581, by rfl⟩ : syracuseStep 2252405 = 211163) (by norm_num)
theorem B2563717 : Blo 1518456 2563717 := bbase (se 4 (by rfl) ⟨240348, by rfl⟩ : syracuseStep 2563717 = 480697) (by norm_num)
theorem B2162317 : Blo 1518456 2162317 := bbase (se 3 (by rfl) ⟨405434, by rfl⟩ : syracuseStep 2162317 = 810869) (by norm_num)
theorem B1621657 : Blo 1518456 1621657 := bbase (se 2 (by rfl) ⟨608121, by rfl⟩ : syracuseStep 1621657 = 1216243) (by norm_num)
theorem B2309789 : Blo 1518456 2309789 := bbase (se 3 (by rfl) ⟨433085, by rfl⟩ : syracuseStep 2309789 = 866171) (by norm_num)
theorem B3464909 : Blo 1518456 3464909 := bbase (se 3 (by rfl) ⟨649670, by rfl⟩ : syracuseStep 3464909 = 1299341) (by norm_num)
theorem B1949393 : Blo 1518456 1949393 := bbase (se 2 (by rfl) ⟨731022, by rfl⟩ : syracuseStep 1949393 = 1462045) (by norm_num)
theorem B5127893 : Blo 1518456 5127893 := bbase (se 7 (by rfl) ⟨60092, by rfl⟩ : syracuseStep 5127893 = 120185) (by norm_num)
theorem B2563805 : Blo 1518456 2563805 := bbase (se 3 (by rfl) ⟨480713, by rfl⟩ : syracuseStep 2563805 = 961427) (by norm_num)
theorem B1621729 : Blo 1518456 1621729 := bbase (se 2 (by rfl) ⟨608148, by rfl⟩ : syracuseStep 1621729 = 1216297) (by norm_num)
theorem B5766997 : Blo 1518456 5766997 := bbase (se 9 (by rfl) ⟨16895, by rfl⟩ : syracuseStep 5766997 = 33791) (by norm_num)
theorem B2563933 : Blo 1518456 2563933 := bbase (se 3 (by rfl) ⟨480737, by rfl⟩ : syracuseStep 2563933 = 961475) (by norm_num)
theorem B2162533 : Blo 1518456 2162533 := bbase (se 4 (by rfl) ⟨202737, by rfl⟩ : syracuseStep 2162533 = 405475) (by norm_num)
theorem B4865957 : Blo 1518456 4865957 := bbase (se 4 (by rfl) ⟨456183, by rfl⟩ : syracuseStep 4865957 = 912367) (by norm_num)
theorem B2564021 : Blo 1518456 2564021 := bbase (se 5 (by rfl) ⟨120188, by rfl⟩ : syracuseStep 2564021 = 240377) (by norm_num)
theorem B7692245 : Blo 1518456 7692245 := bbase (se 7 (by rfl) ⟨90143, by rfl⟩ : syracuseStep 7692245 = 180287) (by norm_num)
theorem B2564129 : Blo 1518456 2564129 := bstep (se 2 (by rfl) ⟨961548, by rfl⟩ : syracuseStep 2564129 = 1923097) B1923097
theorem B14606405 : Blo 1518456 14606405 := bstep (se 4 (by rfl) ⟨1369350, by rfl⟩ : syracuseStep 14606405 = 2738701) B2738701
theorem B2162801 : Blo 1518456 2162801 := bstep (se 2 (by rfl) ⟨811050, by rfl⟩ : syracuseStep 2162801 = 1622101) B1622101
theorem B24658033 : Blo 1518456 24658033 := bstep (se 2 (by rfl) ⟨9246762, by rfl⟩ : syracuseStep 24658033 = 18493525) B18493525
theorem B12984461 : Blo 1518456 12984461 := bstep (se 3 (by rfl) ⟨2434586, by rfl⟩ : syracuseStep 12984461 = 4869173) B4869173
theorem B2564257 : Blo 1518456 2564257 := bstep (se 2 (by rfl) ⟨961596, by rfl⟩ : syracuseStep 2564257 = 1923193) B1923193
theorem B2564291 : Blo 1518456 2564291 := bstep (se 1 (by rfl) ⟨1923218, by rfl⟩ : syracuseStep 2564291 = 3846437) B3846437
theorem B2433235 : Blo 1518456 2433235 := bstep (se 1 (by rfl) ⟨1824926, by rfl⟩ : syracuseStep 2433235 = 3649853) B3649853
theorem B5128433 : Blo 1518456 5128433 := bstep (se 2 (by rfl) ⟨1923162, by rfl⟩ : syracuseStep 5128433 = 3846325) B3846325
theorem B6242609 : Blo 1518456 6242609 := bstep (se 2 (by rfl) ⟨2340978, by rfl⟩ : syracuseStep 6242609 = 4681957) B4681957
theorem B2564419 : Blo 1518456 2564419 := bstep (se 1 (by rfl) ⟨1923314, by rfl⟩ : syracuseStep 2564419 = 3846629) B3846629
theorem B18473285 : Blo 1518456 18473285 := bstep (se 4 (by rfl) ⟨1731870, by rfl⟩ : syracuseStep 18473285 = 3463741) B3463741
theorem B2277713 : Blo 1518456 2277713 := bstep (se 2 (by rfl) ⟨854142, by rfl⟩ : syracuseStep 2277713 = 1708285) B1708285
theorem B2277731 : Blo 1518456 2277731 := bstep (se 1 (by rfl) ⟨1708298, by rfl⟩ : syracuseStep 2277731 = 3416597) B3416597
theorem B6488419 : Blo 1518456 6488419 := bstep (se 1 (by rfl) ⟨4866314, by rfl⟩ : syracuseStep 6488419 = 9732629) B9732629
theorem B1622387 : Blo 1518456 1622387 := bstep (se 1 (by rfl) ⟨1216790, by rfl⟩ : syracuseStep 1622387 = 2433581) B2433581
theorem B2277761 : Blo 1518456 2277761 := bstep (se 2 (by rfl) ⟨854160, by rfl⟩ : syracuseStep 2277761 = 1708321) B1708321
theorem B2277779 : Blo 1518456 2277779 := bstep (se 1 (by rfl) ⟨1708334, by rfl⟩ : syracuseStep 2277779 = 3416669) B3416669
theorem B4325795 : Blo 1518456 4325795 := bstep (se 1 (by rfl) ⟨3244346, by rfl⟩ : syracuseStep 4325795 = 6488693) B6488693
theorem B2277809 : Blo 1518456 2277809 := bstep (se 2 (by rfl) ⟨854178, by rfl⟩ : syracuseStep 2277809 = 1708357) B1708357
theorem B2277827 : Blo 1518456 2277827 := bstep (se 1 (by rfl) ⟨1708370, by rfl⟩ : syracuseStep 2277827 = 3416741) B3416741
theorem B3244483 : Blo 1518456 3244483 := bstep (se 1 (by rfl) ⟨2433362, by rfl⟩ : syracuseStep 3244483 = 4866725) B4866725
theorem B2564561 : Blo 1518456 2564561 := bstep (se 2 (by rfl) ⟨961710, by rfl⟩ : syracuseStep 2564561 = 1923421) B1923421
theorem B2433491 : Blo 1518456 2433491 := bstep (se 1 (by rfl) ⟨1825118, by rfl⟩ : syracuseStep 2433491 = 3650237) B3650237
theorem B2277857 : Blo 1518456 2277857 := bstep (se 2 (by rfl) ⟨854196, by rfl⟩ : syracuseStep 2277857 = 1708393) B1708393
theorem B3416561 : Blo 1518456 3416561 := bstep (se 2 (by rfl) ⟨1281210, by rfl⟩ : syracuseStep 3416561 = 2562421) B2562421
theorem B7029233 : Blo 1518456 7029233 := bstep (se 2 (by rfl) ⟨2635962, by rfl⟩ : syracuseStep 7029233 = 5271925) B5271925
theorem B2277875 : Blo 1518456 2277875 := bstep (se 1 (by rfl) ⟨1708406, by rfl⟩ : syracuseStep 2277875 = 3416813) B3416813
theorem B1622515 : Blo 1518456 1622515 := bstep (se 1 (by rfl) ⟨1216886, by rfl⟩ : syracuseStep 1622515 = 2433773) B2433773
theorem B3416579 : Blo 1518456 3416579 := bstep (se 1 (by rfl) ⟨2562434, by rfl⟩ : syracuseStep 3416579 = 5124869) B5124869
theorem B2884099 : Blo 1518456 2884099 := bstep (se 1 (by rfl) ⟨2163074, by rfl⟩ : syracuseStep 2884099 = 4326149) B4326149
theorem B2277905 : Blo 1518456 2277905 := bstep (se 2 (by rfl) ⟨854214, by rfl⟩ : syracuseStep 2277905 = 1708429) B1708429
theorem B2277923 : Blo 1518456 2277923 := bstep (se 1 (by rfl) ⟨1708442, by rfl⟩ : syracuseStep 2277923 = 3416885) B3416885
theorem B2277953 : Blo 1518456 2277953 := bstep (se 2 (by rfl) ⟨854232, by rfl⟩ : syracuseStep 2277953 = 1708465) B1708465
theorem B8208965 : Blo 1518456 8208965 := bstep (se 4 (by rfl) ⟨769590, by rfl⟩ : syracuseStep 8208965 = 1539181) B1539181
theorem B17302085 : Blo 1518456 17302085 := bstep (se 4 (by rfl) ⟨1622070, by rfl⟩ : syracuseStep 17302085 = 3244141) B3244141
theorem B5767757 : Blo 1518456 5767757 := bstep (se 3 (by rfl) ⟨1081454, by rfl⟩ : syracuseStep 5767757 = 2162909) B2162909
theorem B2564689 : Blo 1518456 2564689 := bstep (se 2 (by rfl) ⟨961758, by rfl⟩ : syracuseStep 2564689 = 1923517) B1923517
theorem B2277971 : Blo 1518456 2277971 := bstep (se 1 (by rfl) ⟨1708478, by rfl⟩ : syracuseStep 2277971 = 3416957) B3416957
theorem B2278001 : Blo 1518456 2278001 := bstep (se 2 (by rfl) ⟨854250, by rfl⟩ : syracuseStep 2278001 = 1708501) B1708501
theorem B2564723 : Blo 1518456 2564723 := bstep (se 1 (by rfl) ⟨1923542, by rfl⟩ : syracuseStep 2564723 = 3847085) B3847085
theorem B2278019 : Blo 1518456 2278019 := bstep (se 1 (by rfl) ⟨1708514, by rfl⟩ : syracuseStep 2278019 = 3417029) B3417029
theorem B2433683 : Blo 1518456 2433683 := bstep (se 1 (by rfl) ⟨1825262, by rfl⟩ : syracuseStep 2433683 = 3650525) B3650525
theorem B2278049 : Blo 1518456 2278049 := bstep (se 2 (by rfl) ⟨854268, by rfl⟩ : syracuseStep 2278049 = 1708537) B1708537
theorem B2278067 : Blo 1518456 2278067 := bstep (se 1 (by rfl) ⟨1708550, by rfl⟩ : syracuseStep 2278067 = 3417101) B3417101
theorem B13165253 : Blo 1518456 13165253 := bstep (se 4 (by rfl) ⟨1234242, by rfl⟩ : syracuseStep 13165253 = 2468485) B2468485
theorem B2278097 : Blo 1518456 2278097 := bstep (se 2 (by rfl) ⟨854286, by rfl⟩ : syracuseStep 2278097 = 1708573) B1708573
theorem B2278115 : Blo 1518456 2278115 := bstep (se 1 (by rfl) ⟨1708586, by rfl⟩ : syracuseStep 2278115 = 3417173) B3417173
theorem B2564851 : Blo 1518456 2564851 := bstep (se 1 (by rfl) ⟨1923638, by rfl⟩ : syracuseStep 2564851 = 3847277) B3847277
theorem B2278145 : Blo 1518456 2278145 := bstep (se 2 (by rfl) ⟨854304, by rfl⟩ : syracuseStep 2278145 = 1708609) B1708609
theorem B2736899 : Blo 1518456 2736899 := bstep (se 1 (by rfl) ⟨2052674, by rfl⟩ : syracuseStep 2736899 = 4105349) B4105349
theorem B5128973 : Blo 1518456 5128973 := bstep (se 3 (by rfl) ⟨961682, by rfl⟩ : syracuseStep 5128973 = 1923365) B1923365
theorem B3416849 : Blo 1518456 3416849 := bstep (se 2 (by rfl) ⟨1281318, by rfl⟩ : syracuseStep 3416849 = 2562637) B2562637
theorem B2278163 : Blo 1518456 2278163 := bstep (se 1 (by rfl) ⟨1708622, by rfl⟩ : syracuseStep 2278163 = 3417245) B3417245
theorem B8209187 : Blo 1518456 8209187 := bstep (se 1 (by rfl) ⟨6156890, by rfl⟩ : syracuseStep 8209187 = 12313781) B12313781
theorem B3416867 : Blo 1518456 3416867 := bstep (se 1 (by rfl) ⟨2562650, by rfl⟩ : syracuseStep 3416867 = 5125301) B5125301
theorem B2278193 : Blo 1518456 2278193 := bstep (se 2 (by rfl) ⟨854322, by rfl⟩ : syracuseStep 2278193 = 1708645) B1708645
theorem B2278211 : Blo 1518456 2278211 := bstep (se 1 (by rfl) ⟨1708658, by rfl⟩ : syracuseStep 2278211 = 3417317) B3417317
theorem B5129027 : Blo 1518456 5129027 := bstep (se 1 (by rfl) ⟨3846770, by rfl⟩ : syracuseStep 5129027 = 7693541) B7693541
theorem B3900241 : Blo 1518456 3900241 := bstep (se 2 (by rfl) ⟨1462590, by rfl⟩ : syracuseStep 3900241 = 2925181) B2925181
theorem B2278241 : Blo 1518456 2278241 := bstep (se 2 (by rfl) ⟨854340, by rfl⟩ : syracuseStep 2278241 = 1708681) B1708681
theorem B8217443 : Blo 1518456 8217443 := bstep (se 1 (by rfl) ⟨6163082, by rfl⟩ : syracuseStep 8217443 = 12326165) B12326165
theorem B2278259 : Blo 1518456 2278259 := bstep (se 1 (by rfl) ⟨1708694, by rfl⟩ : syracuseStep 2278259 = 3417389) B3417389
theorem B2564993 : Blo 1518456 2564993 := bstep (se 2 (by rfl) ⟨961872, by rfl⟩ : syracuseStep 2564993 = 1923745) B1923745
theorem B2278289 : Blo 1518456 2278289 := bstep (se 2 (by rfl) ⟨854358, by rfl⟩ : syracuseStep 2278289 = 1708717) B1708717
theorem B2278307 : Blo 1518456 2278307 := bstep (se 1 (by rfl) ⟨1708730, by rfl⟩ : syracuseStep 2278307 = 3417461) B3417461
theorem B4105133 : Blo 1518456 4105133 := bstep (se 3 (by rfl) ⟨769712, by rfl⟩ : syracuseStep 4105133 = 1539425) B1539425
theorem B2278337 : Blo 1518456 2278337 := bstep (se 2 (by rfl) ⟨854376, by rfl⟩ : syracuseStep 2278337 = 1708753) B1708753
theorem B2884547 : Blo 1518456 2884547 := bstep (se 1 (by rfl) ⟨2163410, by rfl⟩ : syracuseStep 2884547 = 4326821) B4326821
theorem B2278355 : Blo 1518456 2278355 := bstep (se 1 (by rfl) ⟨1708766, by rfl⟩ : syracuseStep 2278355 = 3417533) B3417533
theorem B2163667 : Blo 1518456 2163667 := bstep (se 1 (by rfl) ⟨1622750, by rfl⟩ : syracuseStep 2163667 = 3245501) B3245501
theorem B2278385 : Blo 1518456 2278385 := bstep (se 2 (by rfl) ⟨854394, by rfl⟩ : syracuseStep 2278385 = 1708789) B1708789
theorem B2565121 : Blo 1518456 2565121 := bstep (se 2 (by rfl) ⟨961920, by rfl⟩ : syracuseStep 2565121 = 1923841) B1923841
theorem B2278403 : Blo 1518456 2278403 := bstep (se 1 (by rfl) ⟨1708802, by rfl⟩ : syracuseStep 2278403 = 3417605) B3417605
theorem B2278433 : Blo 1518456 2278433 := bstep (se 2 (by rfl) ⟨854412, by rfl⟩ : syracuseStep 2278433 = 1708825) B1708825
theorem B2565155 : Blo 1518456 2565155 := bstep (se 1 (by rfl) ⟨1923866, by rfl⟩ : syracuseStep 2565155 = 3847733) B3847733
theorem B4105261 : Blo 1518456 4105261 := bstep (se 3 (by rfl) ⟨769736, by rfl⟩ : syracuseStep 4105261 = 1539473) B1539473
theorem B3417137 : Blo 1518456 3417137 := bstep (se 2 (by rfl) ⟨1281426, by rfl⟩ : syracuseStep 3417137 = 2562853) B2562853
theorem B2278451 : Blo 1518456 2278451 := bstep (se 1 (by rfl) ⟨1708838, by rfl⟩ : syracuseStep 2278451 = 3417677) B3417677
theorem B2163763 : Blo 1518456 2163763 := bstep (se 1 (by rfl) ⟨1622822, by rfl⟩ : syracuseStep 2163763 = 3245645) B3245645
theorem B3417155 : Blo 1518456 3417155 := bstep (se 1 (by rfl) ⟨2562866, by rfl⟩ : syracuseStep 3417155 = 5125733) B5125733
theorem B2278481 : Blo 1518456 2278481 := bstep (se 2 (by rfl) ⟨854430, by rfl⟩ : syracuseStep 2278481 = 1708861) B1708861
theorem B5129297 : Blo 1518456 5129297 := bstep (se 2 (by rfl) ⟨1923486, by rfl⟩ : syracuseStep 5129297 = 3846973) B3846973
theorem B2278499 : Blo 1518456 2278499 := bstep (se 1 (by rfl) ⟨1708874, by rfl⟩ : syracuseStep 2278499 = 3417749) B3417749
theorem B17310833 : Blo 1518456 17310833 := bstep (se 2 (by rfl) ⟨6491562, by rfl⟩ : syracuseStep 17310833 = 12983125) B12983125
theorem B2278529 : Blo 1518456 2278529 := bstep (se 2 (by rfl) ⟨854448, by rfl⟩ : syracuseStep 2278529 = 1708897) B1708897
theorem B2499715 : Blo 1518456 2499715 := bstep (se 1 (by rfl) ⟨1874786, by rfl⟩ : syracuseStep 2499715 = 3749573) B3749573
theorem B3245201 : Blo 1518456 3245201 := bstep (se 2 (by rfl) ⟨1216950, by rfl⟩ : syracuseStep 3245201 = 2433901) B2433901
theorem B2278547 : Blo 1518456 2278547 := bstep (se 1 (by rfl) ⟨1708910, by rfl⟩ : syracuseStep 2278547 = 3417821) B3417821
theorem B2565283 : Blo 1518456 2565283 := bstep (se 1 (by rfl) ⟨1923962, by rfl⟩ : syracuseStep 2565283 = 3847925) B3847925
theorem B2278577 : Blo 1518456 2278577 := bstep (se 2 (by rfl) ⟨854466, by rfl⟩ : syracuseStep 2278577 = 1708933) B1708933
theorem B2278595 : Blo 1518456 2278595 := bstep (se 1 (by rfl) ⟨1708946, by rfl⟩ : syracuseStep 2278595 = 3417893) B3417893
theorem B4326605 : Blo 1518456 4326605 := bstep (se 3 (by rfl) ⟨811238, by rfl⟩ : syracuseStep 4326605 = 1622477) B1622477
theorem B2278625 : Blo 1518456 2278625 := bstep (se 2 (by rfl) ⟨854484, by rfl⟩ : syracuseStep 2278625 = 1708969) B1708969
theorem B2884835 : Blo 1518456 2884835 := bstep (se 1 (by rfl) ⟨2163626, by rfl⟩ : syracuseStep 2884835 = 4327253) B4327253
theorem B2278643 : Blo 1518456 2278643 := bstep (se 1 (by rfl) ⟨1708982, by rfl⟩ : syracuseStep 2278643 = 3417965) B3417965
theorem B2278673 : Blo 1518456 2278673 := bstep (se 2 (by rfl) ⟨854502, by rfl⟩ : syracuseStep 2278673 = 1709005) B1709005
theorem B78914837 : Blo 1518456 78914837 := bstep (se 6 (by rfl) ⟨1849566, by rfl⟩ : syracuseStep 78914837 = 3699133) B3699133
theorem B2278691 : Blo 1518456 2278691 := bstep (se 1 (by rfl) ⟨1709018, by rfl⟩ : syracuseStep 2278691 = 3418037) B3418037
theorem B1623331 : Blo 1518456 1623331 := bstep (se 1 (by rfl) ⟨1217498, by rfl⟩ : syracuseStep 1623331 = 2434997) B2434997
theorem B2565425 : Blo 1518456 2565425 := bstep (se 2 (by rfl) ⟨962034, by rfl⟩ : syracuseStep 2565425 = 1924069) B1924069
theorem B2278721 : Blo 1518456 2278721 := bstep (se 2 (by rfl) ⟨854520, by rfl⟩ : syracuseStep 2278721 = 1709041) B1709041
theorem B3417425 : Blo 1518456 3417425 := bstep (se 2 (by rfl) ⟨1281534, by rfl⟩ : syracuseStep 3417425 = 2563069) B2563069
theorem B2278739 : Blo 1518456 2278739 := bstep (se 1 (by rfl) ⟨1709054, by rfl⟩ : syracuseStep 2278739 = 3418109) B3418109
theorem B3417443 : Blo 1518456 3417443 := bstep (se 1 (by rfl) ⟨2563082, by rfl⟩ : syracuseStep 3417443 = 5126165) B5126165
theorem B2278769 : Blo 1518456 2278769 := bstep (se 2 (by rfl) ⟨854538, by rfl⟩ : syracuseStep 2278769 = 1709077) B1709077
theorem B2278787 : Blo 1518456 2278787 := bstep (se 1 (by rfl) ⟨1709090, by rfl⟩ : syracuseStep 2278787 = 3418181) B3418181
theorem B4326797 : Blo 1518456 4326797 := bstep (se 3 (by rfl) ⟨811274, by rfl⟩ : syracuseStep 4326797 = 1622549) B1622549
theorem B2278817 : Blo 1518456 2278817 := bstep (se 2 (by rfl) ⟨854556, by rfl⟩ : syracuseStep 2278817 = 1709113) B1709113
theorem B2434465 : Blo 1518456 2434465 := bstep (se 2 (by rfl) ⟨912924, by rfl⟩ : syracuseStep 2434465 = 1825849) B1825849
theorem B9733553 : Blo 1518456 9733553 := bstep (se 2 (by rfl) ⟨3650082, by rfl⟩ : syracuseStep 9733553 = 7300165) B7300165
theorem B2565553 : Blo 1518456 2565553 := bstep (se 2 (by rfl) ⟨962082, by rfl⟩ : syracuseStep 2565553 = 1924165) B1924165
theorem B2278835 : Blo 1518456 2278835 := bstep (se 1 (by rfl) ⟨1709126, by rfl⟩ : syracuseStep 2278835 = 3418253) B3418253
theorem B2278865 : Blo 1518456 2278865 := bstep (se 2 (by rfl) ⟨854574, by rfl⟩ : syracuseStep 2278865 = 1709149) B1709149
theorem B2565587 : Blo 1518456 2565587 := bstep (se 1 (by rfl) ⟨1924190, by rfl⟩ : syracuseStep 2565587 = 3848381) B3848381
theorem B2278883 : Blo 1518456 2278883 := bstep (se 1 (by rfl) ⟨1709162, by rfl⟩ : syracuseStep 2278883 = 3418325) B3418325
theorem B2278913 : Blo 1518456 2278913 := bstep (se 2 (by rfl) ⟨854592, by rfl⟩ : syracuseStep 2278913 = 1709185) B1709185
theorem B2278931 : Blo 1518456 2278931 := bstep (se 1 (by rfl) ⟨1709198, by rfl⟩ : syracuseStep 2278931 = 3418397) B3418397
theorem B2164259 : Blo 1518456 2164259 := bstep (se 1 (by rfl) ⟨1623194, by rfl⟩ : syracuseStep 2164259 = 3246389) B3246389
theorem B6489649 : Blo 1518456 6489649 := bstep (se 2 (by rfl) ⟨2433618, by rfl⟩ : syracuseStep 6489649 = 4867237) B4867237
theorem B2278961 : Blo 1518456 2278961 := bstep (se 2 (by rfl) ⟨854610, by rfl⟩ : syracuseStep 2278961 = 1709221) B1709221
theorem B2278979 : Blo 1518456 2278979 := bstep (se 1 (by rfl) ⟨1709234, by rfl⟩ : syracuseStep 2278979 = 3418469) B3418469
theorem B8652365 : Blo 1518456 8652365 := bstep (se 3 (by rfl) ⟨1622318, by rfl⟩ : syracuseStep 8652365 = 3244637) B3244637
theorem B7300685 : Blo 1518456 7300685 := bstep (se 3 (by rfl) ⟨1368878, by rfl⟩ : syracuseStep 7300685 = 2737757) B2737757
theorem B2565715 : Blo 1518456 2565715 := bstep (se 1 (by rfl) ⟨1924286, by rfl⟩ : syracuseStep 2565715 = 3848573) B3848573
theorem B2279009 : Blo 1518456 2279009 := bstep (se 2 (by rfl) ⟨854628, by rfl⟩ : syracuseStep 2279009 = 1709257) B1709257
theorem B3843683 : Blo 1518456 3843683 := bstep (se 1 (by rfl) ⟨2882762, by rfl⟩ : syracuseStep 3843683 = 5765525) B5765525
theorem B5129837 : Blo 1518456 5129837 := bstep (se 3 (by rfl) ⟨961844, by rfl⟩ : syracuseStep 5129837 = 1923689) B1923689
theorem B3417713 : Blo 1518456 3417713 := bstep (se 2 (by rfl) ⟨1281642, by rfl⟩ : syracuseStep 3417713 = 2563285) B2563285
theorem B2279027 : Blo 1518456 2279027 := bstep (se 1 (by rfl) ⟨1709270, by rfl⟩ : syracuseStep 2279027 = 3418541) B3418541
theorem B3417731 : Blo 1518456 3417731 := bstep (se 1 (by rfl) ⟨2563298, by rfl⟩ : syracuseStep 3417731 = 5126597) B5126597
theorem B6006413 : Blo 1518456 6006413 := bstep (se 3 (by rfl) ⟨1126202, by rfl⟩ : syracuseStep 6006413 = 2252405) B2252405
theorem B2279057 : Blo 1518456 2279057 := bstep (se 2 (by rfl) ⟨854646, by rfl⟩ : syracuseStep 2279057 = 1709293) B1709293
theorem B2279075 : Blo 1518456 2279075 := bstep (se 1 (by rfl) ⟨1709306, by rfl⟩ : syracuseStep 2279075 = 3418613) B3418613
theorem B5129891 : Blo 1518456 5129891 := bstep (se 1 (by rfl) ⟨3847418, by rfl⟩ : syracuseStep 5129891 = 7694837) B7694837
theorem B2279105 : Blo 1518456 2279105 := bstep (se 2 (by rfl) ⟨854664, by rfl⟩ : syracuseStep 2279105 = 1709329) B1709329
theorem B2279123 : Blo 1518456 2279123 := bstep (se 1 (by rfl) ⟨1709342, by rfl⟩ : syracuseStep 2279123 = 3418685) B3418685
theorem B2279153 : Blo 1518456 2279153 := bstep (se 2 (by rfl) ⟨854682, by rfl⟩ : syracuseStep 2279153 = 1709365) B1709365
theorem B2279171 : Blo 1518456 2279171 := bstep (se 1 (by rfl) ⟨1709378, by rfl⟩ : syracuseStep 2279171 = 3418757) B3418757
theorem B2279201 : Blo 1518456 2279201 := bstep (se 2 (by rfl) ⟨854700, by rfl⟩ : syracuseStep 2279201 = 1709401) B1709401
theorem B3843875 : Blo 1518456 3843875 := bstep (se 1 (by rfl) ⟨2882906, by rfl⟩ : syracuseStep 3843875 = 5765813) B5765813
theorem B2279219 : Blo 1518456 2279219 := bstep (se 1 (by rfl) ⟨1709414, by rfl⟩ : syracuseStep 2279219 = 3418829) B3418829
theorem B2598737 : Blo 1518456 2598737 := bstep (se 2 (by rfl) ⟨974526, by rfl⟩ : syracuseStep 2598737 = 1949053) B1949053
theorem B2279249 : Blo 1518456 2279249 := bstep (se 2 (by rfl) ⟨854718, by rfl⟩ : syracuseStep 2279249 = 1709437) B1709437
theorem B2279267 : Blo 1518456 2279267 := bstep (se 1 (by rfl) ⟨1709450, by rfl⟩ : syracuseStep 2279267 = 3418901) B3418901
theorem B2279297 : Blo 1518456 2279297 := bstep (se 2 (by rfl) ⟨854736, by rfl⟩ : syracuseStep 2279297 = 1709473) B1709473
theorem B55461773 : Blo 1518456 55461773 := bstep (se 3 (by rfl) ⟨10399082, by rfl⟩ : syracuseStep 55461773 = 20798165) B20798165
theorem B3418001 : Blo 1518456 3418001 := bstep (se 2 (by rfl) ⟨1281750, by rfl⟩ : syracuseStep 3418001 = 2563501) B2563501
theorem B2279315 : Blo 1518456 2279315 := bstep (se 1 (by rfl) ⟨1709486, by rfl⟩ : syracuseStep 2279315 = 3418973) B3418973
theorem B3418019 : Blo 1518456 3418019 := bstep (se 1 (by rfl) ⟨2563514, by rfl⟩ : syracuseStep 3418019 = 5127029) B5127029
theorem B3245987 : Blo 1518456 3245987 := bstep (se 1 (by rfl) ⟨2434490, by rfl⟩ : syracuseStep 3245987 = 4868981) B4868981
theorem B2279345 : Blo 1518456 2279345 := bstep (se 2 (by rfl) ⟨854754, by rfl⟩ : syracuseStep 2279345 = 1709509) B1709509
theorem B5130161 : Blo 1518456 5130161 := bstep (se 2 (by rfl) ⟨1923810, by rfl⟩ : syracuseStep 5130161 = 3847621) B3847621
theorem B2279363 : Blo 1518456 2279363 := bstep (se 1 (by rfl) ⟨1709522, by rfl⟩ : syracuseStep 2279363 = 3419045) B3419045
theorem B2279393 : Blo 1518456 2279393 := bstep (se 2 (by rfl) ⟨854772, by rfl⟩ : syracuseStep 2279393 = 1709545) B1709545
theorem B2279411 : Blo 1518456 2279411 := bstep (se 1 (by rfl) ⟨1709558, by rfl⟩ : syracuseStep 2279411 = 3419117) B3419117
theorem B2279441 : Blo 1518456 2279441 := bstep (se 2 (by rfl) ⟨854790, by rfl⟩ : syracuseStep 2279441 = 1709581) B1709581
theorem B2279459 : Blo 1518456 2279459 := bstep (se 1 (by rfl) ⟨1709594, by rfl⟩ : syracuseStep 2279459 = 3419189) B3419189
theorem B2738225 : Blo 1518456 2738225 := bstep (se 2 (by rfl) ⟨1026834, by rfl⟩ : syracuseStep 2738225 = 2053669) B2053669
theorem B2279489 : Blo 1518456 2279489 := bstep (se 2 (by rfl) ⟨854808, by rfl⟩ : syracuseStep 2279489 = 1709617) B1709617
theorem B2279507 : Blo 1518456 2279507 := bstep (se 1 (by rfl) ⟨1709630, by rfl⟩ : syracuseStep 2279507 = 3419261) B3419261
theorem B2279537 : Blo 1518456 2279537 := bstep (se 2 (by rfl) ⟨854826, by rfl⟩ : syracuseStep 2279537 = 1709653) B1709653
theorem B2279555 : Blo 1518456 2279555 := bstep (se 1 (by rfl) ⟨1709666, by rfl⟩ : syracuseStep 2279555 = 3419333) B3419333
theorem B2885777 : Blo 1518456 2885777 := bstep (se 2 (by rfl) ⟨1082166, by rfl⟩ : syracuseStep 2885777 = 2164333) B2164333
theorem B2279585 : Blo 1518456 2279585 := bstep (se 2 (by rfl) ⟨854844, by rfl⟩ : syracuseStep 2279585 = 1709689) B1709689
theorem B3418289 : Blo 1518456 3418289 := bstep (se 2 (by rfl) ⟨1281858, by rfl⟩ : syracuseStep 3418289 = 2563717) B2563717
theorem B7694513 : Blo 1518456 7694513 := bstep (se 2 (by rfl) ⟨2885442, by rfl⟩ : syracuseStep 7694513 = 5770885) B5770885
theorem B2279603 : Blo 1518456 2279603 := bstep (se 1 (by rfl) ⟨1709702, by rfl⟩ : syracuseStep 2279603 = 3419405) B3419405
theorem B3418307 : Blo 1518456 3418307 := bstep (se 1 (by rfl) ⟨2563730, by rfl⟩ : syracuseStep 3418307 = 5127461) B5127461
theorem B2279633 : Blo 1518456 2279633 := bstep (se 2 (by rfl) ⟨854862, by rfl⟩ : syracuseStep 2279633 = 1709725) B1709725
theorem B2279651 : Blo 1518456 2279651 := bstep (se 1 (by rfl) ⟨1709738, by rfl⟩ : syracuseStep 2279651 = 3419477) B3419477
theorem B2279681 : Blo 1518456 2279681 := bstep (se 2 (by rfl) ⟨854880, by rfl⟩ : syracuseStep 2279681 = 1709761) B1709761
theorem B4868365 : Blo 1518456 4868365 := bstep (se 3 (by rfl) ⟨912818, by rfl⟩ : syracuseStep 4868365 = 1825637) B1825637
theorem B2738449 : Blo 1518456 2738449 := bstep (se 2 (by rfl) ⟨1026918, by rfl⟩ : syracuseStep 2738449 = 2053837) B2053837
theorem B2279699 : Blo 1518456 2279699 := bstep (se 1 (by rfl) ⟨1709774, by rfl⟩ : syracuseStep 2279699 = 3419549) B3419549
theorem B2279729 : Blo 1518456 2279729 := bstep (se 2 (by rfl) ⟨854898, by rfl⟩ : syracuseStep 2279729 = 1709797) B1709797
theorem B2279747 : Blo 1518456 2279747 := bstep (se 1 (by rfl) ⟨1709810, by rfl⟩ : syracuseStep 2279747 = 3419621) B3419621
theorem B2279777 : Blo 1518456 2279777 := bstep (se 2 (by rfl) ⟨854916, by rfl⟩ : syracuseStep 2279777 = 1709833) B1709833
theorem B4327789 : Blo 1518456 4327789 := bstep (se 3 (by rfl) ⟨811460, by rfl⟩ : syracuseStep 4327789 = 1622921) B1622921
theorem B2279795 : Blo 1518456 2279795 := bstep (se 1 (by rfl) ⟨1709846, by rfl⟩ : syracuseStep 2279795 = 3419693) B3419693
theorem B2279825 : Blo 1518456 2279825 := bstep (se 2 (by rfl) ⟨854934, by rfl⟩ : syracuseStep 2279825 = 1709869) B1709869
theorem B2279843 : Blo 1518456 2279843 := bstep (se 1 (by rfl) ⟨1709882, by rfl⟩ : syracuseStep 2279843 = 3419765) B3419765
theorem B2279873 : Blo 1518456 2279873 := bstep (se 2 (by rfl) ⟨854952, by rfl⟩ : syracuseStep 2279873 = 1709905) B1709905
theorem B5130701 : Blo 1518456 5130701 := bstep (se 3 (by rfl) ⟨962006, by rfl⟩ : syracuseStep 5130701 = 1924013) B1924013
theorem B3418577 : Blo 1518456 3418577 := bstep (se 2 (by rfl) ⟨1281966, by rfl⟩ : syracuseStep 3418577 = 2563933) B2563933
theorem B2279891 : Blo 1518456 2279891 := bstep (se 1 (by rfl) ⟨1709918, by rfl⟩ : syracuseStep 2279891 = 3419837) B3419837
theorem B8210915 : Blo 1518456 8210915 := bstep (se 1 (by rfl) ⟨6158186, by rfl⟩ : syracuseStep 8210915 = 12316373) B12316373
theorem B3418595 : Blo 1518456 3418595 := bstep (se 1 (by rfl) ⟨2563946, by rfl⟩ : syracuseStep 3418595 = 5127893) B5127893
theorem B4164077 : Blo 1518456 4164077 := bstep (se 3 (by rfl) ⟨780764, by rfl⟩ : syracuseStep 4164077 = 1561529) B1561529
theorem B2279921 : Blo 1518456 2279921 := bstep (se 2 (by rfl) ⟨854970, by rfl⟩ : syracuseStep 2279921 = 1709941) B1709941
theorem B2279939 : Blo 1518456 2279939 := bstep (se 1 (by rfl) ⟨1709954, by rfl⟩ : syracuseStep 2279939 = 3419909) B3419909
theorem B5130755 : Blo 1518456 5130755 := bstep (se 1 (by rfl) ⟨3848066, by rfl⟩ : syracuseStep 5130755 = 7696133) B7696133
theorem B2279969 : Blo 1518456 2279969 := bstep (se 2 (by rfl) ⟨854988, by rfl⟩ : syracuseStep 2279969 = 1709977) B1709977
theorem B2279987 : Blo 1518456 2279987 := bstep (se 1 (by rfl) ⟨1709990, by rfl⟩ : syracuseStep 2279987 = 3419981) B3419981
theorem B5474893 : Blo 1518456 5474893 := bstep (se 3 (by rfl) ⟨1026542, by rfl⟩ : syracuseStep 5474893 = 2053085) B2053085
theorem B2280017 : Blo 1518456 2280017 := bstep (se 2 (by rfl) ⟨855006, by rfl⟩ : syracuseStep 2280017 = 1710013) B1710013
theorem B2280035 : Blo 1518456 2280035 := bstep (se 1 (by rfl) ⟨1710026, by rfl⟩ : syracuseStep 2280035 = 3420053) B3420053
theorem B2280065 : Blo 1518456 2280065 := bstep (se 2 (by rfl) ⟨855024, by rfl⟩ : syracuseStep 2280065 = 1710049) B1710049
theorem B2280083 : Blo 1518456 2280083 := bstep (se 1 (by rfl) ⟨1710062, by rfl⟩ : syracuseStep 2280083 = 3420125) B3420125
theorem B2280113 : Blo 1518456 2280113 := bstep (se 2 (by rfl) ⟨855042, by rfl⟩ : syracuseStep 2280113 = 1710085) B1710085
theorem B2280131 : Blo 1518456 2280131 := bstep (se 1 (by rfl) ⟨1710098, by rfl⟩ : syracuseStep 2280131 = 3420197) B3420197
theorem B3844817 : Blo 1518456 3844817 := bstep (se 2 (by rfl) ⟨1441806, by rfl⟩ : syracuseStep 3844817 = 2883613) B2883613
theorem B2280161 : Blo 1518456 2280161 := bstep (se 2 (by rfl) ⟨855060, by rfl⟩ : syracuseStep 2280161 = 1710121) B1710121
theorem B3418865 : Blo 1518456 3418865 := bstep (se 2 (by rfl) ⟨1282074, by rfl⟩ : syracuseStep 3418865 = 2564149) B2564149
theorem B2280179 : Blo 1518456 2280179 := bstep (se 1 (by rfl) ⟨1710134, by rfl⟩ : syracuseStep 2280179 = 3420269) B3420269
theorem B3844867 : Blo 1518456 3844867 := bstep (se 1 (by rfl) ⟨2883650, by rfl⟩ : syracuseStep 3844867 = 5767301) B5767301
theorem B3418883 : Blo 1518456 3418883 := bstep (se 1 (by rfl) ⟨2564162, by rfl⟩ : syracuseStep 3418883 = 5128325) B5128325
theorem B2738947 : Blo 1518456 2738947 := bstep (se 1 (by rfl) ⟨2054210, by rfl⟩ : syracuseStep 2738947 = 4108421) B4108421
theorem B2280209 : Blo 1518456 2280209 := bstep (se 2 (by rfl) ⟨855078, by rfl⟩ : syracuseStep 2280209 = 1710157) B1710157
theorem B5131025 : Blo 1518456 5131025 := bstep (se 2 (by rfl) ⟨1924134, by rfl⟩ : syracuseStep 5131025 = 3848269) B3848269
theorem B2280227 : Blo 1518456 2280227 := bstep (se 1 (by rfl) ⟨1710170, by rfl⟩ : syracuseStep 2280227 = 3420341) B3420341
theorem B2280257 : Blo 1518456 2280257 := bstep (se 2 (by rfl) ⟨855096, by rfl⟩ : syracuseStep 2280257 = 1710193) B1710193
theorem B2280275 : Blo 1518456 2280275 := bstep (se 1 (by rfl) ⟨1710206, by rfl⟩ : syracuseStep 2280275 = 3420413) B3420413
theorem B13151089 : Blo 1518456 13151089 := bstep (se 2 (by rfl) ⟨4931658, by rfl⟩ : syracuseStep 13151089 = 9863317) B9863317
theorem B2280305 : Blo 1518456 2280305 := bstep (se 2 (by rfl) ⟨855114, by rfl⟩ : syracuseStep 2280305 = 1710229) B1710229
theorem B3246961 : Blo 1518456 3246961 := bstep (se 2 (by rfl) ⟨1217610, by rfl⟩ : syracuseStep 3246961 = 2435221) B2435221
theorem B1518467 : Blo 1518456 1518467 := bstep (se 1 (by rfl) ⟨1138850, by rfl⟩ : syracuseStep 1518467 = 2277701) B2277701
theorem B2280323 : Blo 1518456 2280323 := bstep (se 1 (by rfl) ⟨1710242, by rfl⟩ : syracuseStep 2280323 = 3420485) B3420485
theorem B3845009 : Blo 1518456 3845009 := bstep (se 2 (by rfl) ⟨1441878, by rfl⟩ : syracuseStep 3845009 = 2883757) B2883757
theorem B1518483 : Blo 1518456 1518483 := bstep (se 1 (by rfl) ⟨1138862, by rfl⟩ : syracuseStep 1518483 = 2277725) B2277725
theorem B2280353 : Blo 1518456 2280353 := bstep (se 2 (by rfl) ⟨855132, by rfl⟩ : syracuseStep 2280353 = 1710265) B1710265
theorem B1518499 : Blo 1518456 1518499 := bstep (se 1 (by rfl) ⟨1138874, by rfl⟩ : syracuseStep 1518499 = 2277749) B2277749
theorem B1518515 : Blo 1518456 1518515 := bstep (se 1 (by rfl) ⟨1138886, by rfl⟩ : syracuseStep 1518515 = 2277773) B2277773
theorem B2280371 : Blo 1518456 2280371 := bstep (se 1 (by rfl) ⟨1710278, by rfl⟩ : syracuseStep 2280371 = 3420557) B3420557
theorem B1518531 : Blo 1518456 1518531 := bstep (se 1 (by rfl) ⟨1138898, by rfl⟩ : syracuseStep 1518531 = 2277797) B2277797
theorem B2280401 : Blo 1518456 2280401 := bstep (se 2 (by rfl) ⟨855150, by rfl⟩ : syracuseStep 2280401 = 1710301) B1710301
theorem B1518547 : Blo 1518456 1518547 := bstep (se 1 (by rfl) ⟨1138910, by rfl⟩ : syracuseStep 1518547 = 2277821) B2277821
theorem B1518563 : Blo 1518456 1518563 := bstep (se 1 (by rfl) ⟨1138922, by rfl⟩ : syracuseStep 1518563 = 2277845) B2277845
theorem B2280419 : Blo 1518456 2280419 := bstep (se 1 (by rfl) ⟨1710314, by rfl⟩ : syracuseStep 2280419 = 3420629) B3420629
theorem B1518579 : Blo 1518456 1518579 := bstep (se 1 (by rfl) ⟨1138934, by rfl⟩ : syracuseStep 1518579 = 2277869) B2277869
theorem B1518595 : Blo 1518456 1518595 := bstep (se 1 (by rfl) ⟨1138946, by rfl⟩ : syracuseStep 1518595 = 2277893) B2277893
theorem B2280449 : Blo 1518456 2280449 := bstep (se 2 (by rfl) ⟨855168, by rfl⟩ : syracuseStep 2280449 = 1710337) B1710337
theorem B3419153 : Blo 1518456 3419153 := bstep (se 2 (by rfl) ⟨1282182, by rfl⟩ : syracuseStep 3419153 = 2564365) B2564365
theorem B1518611 : Blo 1518456 1518611 := bstep (se 1 (by rfl) ⟨1138958, by rfl⟩ : syracuseStep 1518611 = 2277917) B2277917
theorem B2280467 : Blo 1518456 2280467 := bstep (se 1 (by rfl) ⟨1710350, by rfl⟩ : syracuseStep 2280467 = 3420701) B3420701
theorem B1518627 : Blo 1518456 1518627 := bstep (se 1 (by rfl) ⟨1138970, by rfl⟩ : syracuseStep 1518627 = 2277941) B2277941
theorem B3419171 : Blo 1518456 3419171 := bstep (se 1 (by rfl) ⟨2564378, by rfl⟩ : syracuseStep 3419171 = 5128757) B5128757
theorem B2280497 : Blo 1518456 2280497 := bstep (se 2 (by rfl) ⟨855186, by rfl⟩ : syracuseStep 2280497 = 1710373) B1710373
theorem B1518643 : Blo 1518456 1518643 := bstep (se 1 (by rfl) ⟨1138982, by rfl⟩ : syracuseStep 1518643 = 2277965) B2277965
theorem B1518659 : Blo 1518456 1518659 := bstep (se 1 (by rfl) ⟨1138994, by rfl⟩ : syracuseStep 1518659 = 2277989) B2277989
theorem B2280515 : Blo 1518456 2280515 := bstep (se 1 (by rfl) ⟨1710386, by rfl⟩ : syracuseStep 2280515 = 3420773) B3420773
theorem B1518675 : Blo 1518456 1518675 := bstep (se 1 (by rfl) ⟨1139006, by rfl⟩ : syracuseStep 1518675 = 2278013) B2278013
theorem B2280545 : Blo 1518456 2280545 := bstep (se 2 (by rfl) ⟨855204, by rfl⟩ : syracuseStep 2280545 = 1710409) B1710409
theorem B1518691 : Blo 1518456 1518691 := bstep (se 1 (by rfl) ⟨1139018, by rfl⟩ : syracuseStep 1518691 = 2278037) B2278037
theorem B3247217 : Blo 1518456 3247217 := bstep (se 2 (by rfl) ⟨1217706, by rfl⟩ : syracuseStep 3247217 = 2435413) B2435413
theorem B1518707 : Blo 1518456 1518707 := bstep (se 1 (by rfl) ⟨1139030, by rfl⟩ : syracuseStep 1518707 = 2278061) B2278061
theorem B2280563 : Blo 1518456 2280563 := bstep (se 1 (by rfl) ⟨1710422, by rfl⟩ : syracuseStep 2280563 = 3420845) B3420845
theorem B1518723 : Blo 1518456 1518723 := bstep (se 1 (by rfl) ⟨1139042, by rfl⟩ : syracuseStep 1518723 = 2278085) B2278085
theorem B1518739 : Blo 1518456 1518739 := bstep (se 1 (by rfl) ⟨1139054, by rfl⟩ : syracuseStep 1518739 = 2278109) B2278109
theorem B2280593 : Blo 1518456 2280593 := bstep (se 2 (by rfl) ⟨855222, by rfl⟩ : syracuseStep 2280593 = 1710445) B1710445
theorem B3124369 : Blo 1518456 3124369 := bstep (se 2 (by rfl) ⟨1171638, by rfl⟩ : syracuseStep 3124369 = 2343277) B2343277
theorem B1518755 : Blo 1518456 1518755 := bstep (se 1 (by rfl) ⟨1139066, by rfl⟩ : syracuseStep 1518755 = 2278133) B2278133
theorem B7023779 : Blo 1518456 7023779 := bstep (se 1 (by rfl) ⟨5267834, by rfl⟩ : syracuseStep 7023779 = 10535669) B10535669
theorem B2280611 : Blo 1518456 2280611 := bstep (se 1 (by rfl) ⟨1710458, by rfl⟩ : syracuseStep 2280611 = 3420917) B3420917
theorem B1518771 : Blo 1518456 1518771 := bstep (se 1 (by rfl) ⟨1139078, by rfl⟩ : syracuseStep 1518771 = 2278157) B2278157
theorem B2280641 : Blo 1518456 2280641 := bstep (se 2 (by rfl) ⟨855240, by rfl⟩ : syracuseStep 2280641 = 1710481) B1710481
theorem B1518787 : Blo 1518456 1518787 := bstep (se 1 (by rfl) ⟨1139090, by rfl⟩ : syracuseStep 1518787 = 2278181) B2278181
theorem B1518803 : Blo 1518456 1518803 := bstep (se 1 (by rfl) ⟨1139102, by rfl⟩ : syracuseStep 1518803 = 2278205) B2278205
theorem B2280659 : Blo 1518456 2280659 := bstep (se 1 (by rfl) ⟨1710494, by rfl⟩ : syracuseStep 2280659 = 3420989) B3420989
theorem B1518819 : Blo 1518456 1518819 := bstep (se 1 (by rfl) ⟨1139114, by rfl⟩ : syracuseStep 1518819 = 2278229) B2278229
theorem B8326385 : Blo 1518456 8326385 := bstep (se 2 (by rfl) ⟨3122394, by rfl⟩ : syracuseStep 8326385 = 6244789) B6244789
theorem B1518835 : Blo 1518456 1518835 := bstep (se 1 (by rfl) ⟨1139126, by rfl⟩ : syracuseStep 1518835 = 2278253) B2278253
theorem B1518851 : Blo 1518456 1518851 := bstep (se 1 (by rfl) ⟨1139138, by rfl⟩ : syracuseStep 1518851 = 2278277) B2278277
theorem B1518867 : Blo 1518456 1518867 := bstep (se 1 (by rfl) ⟨1139150, by rfl⟩ : syracuseStep 1518867 = 2278301) B2278301
theorem B1518883 : Blo 1518456 1518883 := bstep (se 1 (by rfl) ⟨1139162, by rfl⟩ : syracuseStep 1518883 = 2278325) B2278325
theorem B3419441 : Blo 1518456 3419441 := bstep (se 2 (by rfl) ⟨1282290, by rfl⟩ : syracuseStep 3419441 = 2564581) B2564581
theorem B1518899 : Blo 1518456 1518899 := bstep (se 1 (by rfl) ⟨1139174, by rfl⟩ : syracuseStep 1518899 = 2278349) B2278349
theorem B1518915 : Blo 1518456 1518915 := bstep (se 1 (by rfl) ⟨1139186, by rfl⟩ : syracuseStep 1518915 = 2278373) B2278373
theorem B3419459 : Blo 1518456 3419459 := bstep (se 1 (by rfl) ⟨2564594, by rfl⟩ : syracuseStep 3419459 = 5129189) B5129189
theorem B2739523 : Blo 1518456 2739523 := bstep (se 1 (by rfl) ⟨2054642, by rfl⟩ : syracuseStep 2739523 = 4109285) B4109285
theorem B1518931 : Blo 1518456 1518931 := bstep (se 1 (by rfl) ⟨1139198, by rfl⟩ : syracuseStep 1518931 = 2278397) B2278397
theorem B1518947 : Blo 1518456 1518947 := bstep (se 1 (by rfl) ⟨1139210, by rfl⟩ : syracuseStep 1518947 = 2278421) B2278421
theorem B1518963 : Blo 1518456 1518963 := bstep (se 1 (by rfl) ⟨1139222, by rfl⟩ : syracuseStep 1518963 = 2278445) B2278445
theorem B1518979 : Blo 1518456 1518979 := bstep (se 1 (by rfl) ⟨1139234, by rfl⟩ : syracuseStep 1518979 = 2278469) B2278469
theorem B1518995 : Blo 1518456 1518995 := bstep (se 1 (by rfl) ⟨1139246, by rfl⟩ : syracuseStep 1518995 = 2278493) B2278493
theorem B1519011 : Blo 1518456 1519011 := bstep (se 1 (by rfl) ⟨1139258, by rfl⟩ : syracuseStep 1519011 = 2278517) B2278517
theorem B5770673 : Blo 1518456 5770673 := bstep (se 2 (by rfl) ⟨2164002, by rfl⟩ : syracuseStep 5770673 = 4328005) B4328005
theorem B1519027 : Blo 1518456 1519027 := bstep (se 1 (by rfl) ⟨1139270, by rfl⟩ : syracuseStep 1519027 = 2278541) B2278541
theorem B1519043 : Blo 1518456 1519043 := bstep (se 1 (by rfl) ⟨1139282, by rfl⟩ : syracuseStep 1519043 = 2278565) B2278565
theorem B1519059 : Blo 1518456 1519059 := bstep (se 1 (by rfl) ⟨1139294, by rfl⟩ : syracuseStep 1519059 = 2278589) B2278589
theorem B1519075 : Blo 1518456 1519075 := bstep (se 1 (by rfl) ⟨1139306, by rfl⟩ : syracuseStep 1519075 = 2278613) B2278613
theorem B1519091 : Blo 1518456 1519091 := bstep (se 1 (by rfl) ⟨1139318, by rfl⟩ : syracuseStep 1519091 = 2278637) B2278637
theorem B1519107 : Blo 1518456 1519107 := bstep (se 1 (by rfl) ⟨1139330, by rfl⟩ : syracuseStep 1519107 = 2278661) B2278661
theorem B1519123 : Blo 1518456 1519123 := bstep (se 1 (by rfl) ⟨1139342, by rfl⟩ : syracuseStep 1519123 = 2278685) B2278685
theorem B1519139 : Blo 1518456 1519139 := bstep (se 1 (by rfl) ⟨1139354, by rfl⟩ : syracuseStep 1519139 = 2278709) B2278709
theorem B1519155 : Blo 1518456 1519155 := bstep (se 1 (by rfl) ⟨1139366, by rfl⟩ : syracuseStep 1519155 = 2278733) B2278733
theorem B1519171 : Blo 1518456 1519171 := bstep (se 1 (by rfl) ⟨1139378, by rfl⟩ : syracuseStep 1519171 = 2278757) B2278757
theorem B3419729 : Blo 1518456 3419729 := bstep (se 2 (by rfl) ⟨1282398, by rfl⟩ : syracuseStep 3419729 = 2564797) B2564797
theorem B1519187 : Blo 1518456 1519187 := bstep (se 1 (by rfl) ⟨1139390, by rfl⟩ : syracuseStep 1519187 = 2278781) B2278781
theorem B1519203 : Blo 1518456 1519203 := bstep (se 1 (by rfl) ⟨1139402, by rfl⟩ : syracuseStep 1519203 = 2278805) B2278805
theorem B3419747 : Blo 1518456 3419747 := bstep (se 1 (by rfl) ⟨2564810, by rfl⟩ : syracuseStep 3419747 = 5129621) B5129621
theorem B7695971 : Blo 1518456 7695971 := bstep (se 1 (by rfl) ⟨5771978, by rfl⟩ : syracuseStep 7695971 = 11543957) B11543957
theorem B1519219 : Blo 1518456 1519219 := bstep (se 1 (by rfl) ⟨1139414, by rfl⟩ : syracuseStep 1519219 = 2278829) B2278829
theorem B1519235 : Blo 1518456 1519235 := bstep (se 1 (by rfl) ⟨1139426, by rfl⟩ : syracuseStep 1519235 = 2278853) B2278853
theorem B14601869 : Blo 1518456 14601869 := bstep (se 3 (by rfl) ⟨2737850, by rfl⟩ : syracuseStep 14601869 = 5475701) B5475701
theorem B1519251 : Blo 1518456 1519251 := bstep (se 1 (by rfl) ⟨1139438, by rfl⟩ : syracuseStep 1519251 = 2278877) B2278877
theorem B1519267 : Blo 1518456 1519267 := bstep (se 1 (by rfl) ⟨1139450, by rfl⟩ : syracuseStep 1519267 = 2278901) B2278901
theorem B1519283 : Blo 1518456 1519283 := bstep (se 1 (by rfl) ⟨1139462, by rfl⟩ : syracuseStep 1519283 = 2278925) B2278925
theorem B1519299 : Blo 1518456 1519299 := bstep (se 1 (by rfl) ⟨1139474, by rfl⟩ : syracuseStep 1519299 = 2278949) B2278949
theorem B4869827 : Blo 1518456 4869827 := bstep (se 1 (by rfl) ⟨3652370, by rfl⟩ : syracuseStep 4869827 = 7304741) B7304741
theorem B1519315 : Blo 1518456 1519315 := bstep (se 1 (by rfl) ⟨1139486, by rfl⟩ : syracuseStep 1519315 = 2278973) B2278973
theorem B1519331 : Blo 1518456 1519331 := bstep (se 1 (by rfl) ⟨1139498, by rfl⟩ : syracuseStep 1519331 = 2278997) B2278997
theorem B1519347 : Blo 1518456 1519347 := bstep (se 1 (by rfl) ⟨1139510, by rfl⟩ : syracuseStep 1519347 = 2279021) B2279021
theorem B2633473 : Blo 1518456 2633473 := bstep (se 2 (by rfl) ⟨987552, by rfl⟩ : syracuseStep 2633473 = 1975105) B1975105
theorem B1519363 : Blo 1518456 1519363 := bstep (se 1 (by rfl) ⟨1139522, by rfl⟩ : syracuseStep 1519363 = 2279045) B2279045
theorem B8654597 : Blo 1518456 8654597 := bstep (se 4 (by rfl) ⟨811368, by rfl⟩ : syracuseStep 8654597 = 1622737) B1622737
theorem B1519379 : Blo 1518456 1519379 := bstep (se 1 (by rfl) ⟨1139534, by rfl⟩ : syracuseStep 1519379 = 2279069) B2279069
theorem B1519395 : Blo 1518456 1519395 := bstep (se 1 (by rfl) ⟨1139546, by rfl⟩ : syracuseStep 1519395 = 2279093) B2279093
theorem B1519411 : Blo 1518456 1519411 := bstep (se 1 (by rfl) ⟨1139558, by rfl⟩ : syracuseStep 1519411 = 2279117) B2279117
theorem B1519427 : Blo 1518456 1519427 := bstep (se 1 (by rfl) ⟨1139570, by rfl⟩ : syracuseStep 1519427 = 2279141) B2279141
theorem B1519443 : Blo 1518456 1519443 := bstep (se 1 (by rfl) ⟨1139582, by rfl⟩ : syracuseStep 1519443 = 2279165) B2279165
theorem B1519459 : Blo 1518456 1519459 := bstep (se 1 (by rfl) ⟨1139594, by rfl⟩ : syracuseStep 1519459 = 2279189) B2279189
theorem B3846001 : Blo 1518456 3846001 := bstep (se 2 (by rfl) ⟨1442250, by rfl⟩ : syracuseStep 3846001 = 2884501) B2884501
theorem B3420017 : Blo 1518456 3420017 := bstep (se 2 (by rfl) ⟨1282506, by rfl⟩ : syracuseStep 3420017 = 2565013) B2565013
theorem B1519475 : Blo 1518456 1519475 := bstep (se 1 (by rfl) ⟨1139606, by rfl⟩ : syracuseStep 1519475 = 2279213) B2279213
theorem B1519491 : Blo 1518456 1519491 := bstep (se 1 (by rfl) ⟨1139618, by rfl⟩ : syracuseStep 1519491 = 2279237) B2279237
theorem B3420035 : Blo 1518456 3420035 := bstep (se 1 (by rfl) ⟨2565026, by rfl⟩ : syracuseStep 3420035 = 5130053) B5130053
theorem B1519507 : Blo 1518456 1519507 := bstep (se 1 (by rfl) ⟨1139630, by rfl⟩ : syracuseStep 1519507 = 2279261) B2279261
theorem B8769443 : Blo 1518456 8769443 := bstep (se 1 (by rfl) ⟨6577082, by rfl⟩ : syracuseStep 8769443 = 13154165) B13154165
theorem B1519523 : Blo 1518456 1519523 := bstep (se 1 (by rfl) ⟨1139642, by rfl⟩ : syracuseStep 1519523 = 2279285) B2279285
theorem B1519539 : Blo 1518456 1519539 := bstep (se 1 (by rfl) ⟨1139654, by rfl⟩ : syracuseStep 1519539 = 2279309) B2279309
theorem B1519555 : Blo 1518456 1519555 := bstep (se 1 (by rfl) ⟨1139666, by rfl⟩ : syracuseStep 1519555 = 2279333) B2279333
theorem B1519571 : Blo 1518456 1519571 := bstep (se 1 (by rfl) ⟨1139678, by rfl⟩ : syracuseStep 1519571 = 2279357) B2279357
theorem B1519587 : Blo 1518456 1519587 := bstep (se 1 (by rfl) ⟨1139690, by rfl⟩ : syracuseStep 1519587 = 2279381) B2279381
theorem B1519603 : Blo 1518456 1519603 := bstep (se 1 (by rfl) ⟨1139702, by rfl⟩ : syracuseStep 1519603 = 2279405) B2279405
theorem B1519619 : Blo 1518456 1519619 := bstep (se 1 (by rfl) ⟨1139714, by rfl⟩ : syracuseStep 1519619 = 2279429) B2279429
theorem B1519635 : Blo 1518456 1519635 := bstep (se 1 (by rfl) ⟨1139726, by rfl⟩ : syracuseStep 1519635 = 2279453) B2279453
theorem B1519651 : Blo 1518456 1519651 := bstep (se 1 (by rfl) ⟨1139738, by rfl⟩ : syracuseStep 1519651 = 2279477) B2279477
theorem B4165681 : Blo 1518456 4165681 := bstep (se 2 (by rfl) ⟨1562130, by rfl⟩ : syracuseStep 4165681 = 3124261) B3124261
theorem B4329521 : Blo 1518456 4329521 := bstep (se 2 (by rfl) ⟨1623570, by rfl⟩ : syracuseStep 4329521 = 3247141) B3247141
theorem B1519667 : Blo 1518456 1519667 := bstep (se 1 (by rfl) ⟨1139750, by rfl⟩ : syracuseStep 1519667 = 2279501) B2279501
theorem B1519683 : Blo 1518456 1519683 := bstep (se 1 (by rfl) ⟨1139762, by rfl⟩ : syracuseStep 1519683 = 2279525) B2279525
theorem B1519699 : Blo 1518456 1519699 := bstep (se 1 (by rfl) ⟨1139774, by rfl⟩ : syracuseStep 1519699 = 2279549) B2279549
theorem B1519715 : Blo 1518456 1519715 := bstep (se 1 (by rfl) ⟨1139786, by rfl⟩ : syracuseStep 1519715 = 2279573) B2279573
theorem B1519731 : Blo 1518456 1519731 := bstep (se 1 (by rfl) ⟨1139798, by rfl⟩ : syracuseStep 1519731 = 2279597) B2279597
theorem B3846275 : Blo 1518456 3846275 := bstep (se 1 (by rfl) ⟨2884706, by rfl⟩ : syracuseStep 3846275 = 5769413) B5769413
theorem B1519747 : Blo 1518456 1519747 := bstep (se 1 (by rfl) ⟨1139810, by rfl⟩ : syracuseStep 1519747 = 2279621) B2279621
theorem B3420305 : Blo 1518456 3420305 := bstep (se 2 (by rfl) ⟨1282614, by rfl⟩ : syracuseStep 3420305 = 2565229) B2565229
theorem B1519763 : Blo 1518456 1519763 := bstep (se 1 (by rfl) ⟨1139822, by rfl⟩ : syracuseStep 1519763 = 2279645) B2279645
theorem B1519779 : Blo 1518456 1519779 := bstep (se 1 (by rfl) ⟨1139834, by rfl⟩ : syracuseStep 1519779 = 2279669) B2279669
theorem B3420323 : Blo 1518456 3420323 := bstep (se 1 (by rfl) ⟨2565242, by rfl⟩ : syracuseStep 3420323 = 5130485) B5130485
theorem B1519795 : Blo 1518456 1519795 := bstep (se 1 (by rfl) ⟨1139846, by rfl⟩ : syracuseStep 1519795 = 2279693) B2279693
theorem B1519811 : Blo 1518456 1519811 := bstep (se 1 (by rfl) ⟨1139858, by rfl⟩ : syracuseStep 1519811 = 2279717) B2279717
theorem B1519827 : Blo 1518456 1519827 := bstep (se 1 (by rfl) ⟨1139870, by rfl⟩ : syracuseStep 1519827 = 2279741) B2279741
theorem B1519843 : Blo 1518456 1519843 := bstep (se 1 (by rfl) ⟨1139882, by rfl⟩ : syracuseStep 1519843 = 2279765) B2279765
theorem B93622499 : Blo 1518456 93622499 := bstep (se 1 (by rfl) ⟨70216874, by rfl⟩ : syracuseStep 93622499 = 140433749) B140433749
theorem B4329713 : Blo 1518456 4329713 := bstep (se 2 (by rfl) ⟨1623642, by rfl⟩ : syracuseStep 4329713 = 3247285) B3247285
theorem B1519859 : Blo 1518456 1519859 := bstep (se 1 (by rfl) ⟨1139894, by rfl⟩ : syracuseStep 1519859 = 2279789) B2279789
theorem B1519875 : Blo 1518456 1519875 := bstep (se 1 (by rfl) ⟨1139906, by rfl⟩ : syracuseStep 1519875 = 2279813) B2279813
theorem B1519891 : Blo 1518456 1519891 := bstep (se 1 (by rfl) ⟨1139918, by rfl⟩ : syracuseStep 1519891 = 2279837) B2279837
theorem B1519907 : Blo 1518456 1519907 := bstep (se 1 (by rfl) ⟨1139930, by rfl⟩ : syracuseStep 1519907 = 2279861) B2279861
theorem B1708339 : Blo 1518456 1708339 := bstep (se 1 (by rfl) ⟨1281254, by rfl⟩ : syracuseStep 1708339 = 2562509) B2562509
theorem B1519923 : Blo 1518456 1519923 := bstep (se 1 (by rfl) ⟨1139942, by rfl⟩ : syracuseStep 1519923 = 2279885) B2279885
theorem B3846467 : Blo 1518456 3846467 := bstep (se 1 (by rfl) ⟨2884850, by rfl⟩ : syracuseStep 3846467 = 5769701) B5769701
theorem B1519939 : Blo 1518456 1519939 := bstep (se 1 (by rfl) ⟨1139954, by rfl⟩ : syracuseStep 1519939 = 2279909) B2279909
theorem B1519955 : Blo 1518456 1519955 := bstep (se 1 (by rfl) ⟨1139966, by rfl⟩ : syracuseStep 1519955 = 2279933) B2279933
theorem B1519971 : Blo 1518456 1519971 := bstep (se 1 (by rfl) ⟨1139978, by rfl⟩ : syracuseStep 1519971 = 2279957) B2279957
theorem B1519987 : Blo 1518456 1519987 := bstep (se 1 (by rfl) ⟨1139990, by rfl⟩ : syracuseStep 1519987 = 2279981) B2279981
theorem B1520003 : Blo 1518456 1520003 := bstep (se 1 (by rfl) ⟨1140002, by rfl⟩ : syracuseStep 1520003 = 2280005) B2280005
theorem B7696781 : Blo 1518456 7696781 := bstep (se 3 (by rfl) ⟨1443146, by rfl⟩ : syracuseStep 7696781 = 2886293) B2886293
theorem B1520019 : Blo 1518456 1520019 := bstep (se 1 (by rfl) ⟨1140014, by rfl⟩ : syracuseStep 1520019 = 2280029) B2280029
theorem B1520035 : Blo 1518456 1520035 := bstep (se 1 (by rfl) ⟨1140026, by rfl⟩ : syracuseStep 1520035 = 2280053) B2280053
theorem B8655281 : Blo 1518456 8655281 := bstep (se 2 (by rfl) ⟨3245730, by rfl⟩ : syracuseStep 8655281 = 6491461) B6491461
theorem B1520051 : Blo 1518456 1520051 := bstep (se 1 (by rfl) ⟨1140038, by rfl⟩ : syracuseStep 1520051 = 2280077) B2280077
theorem B3420593 : Blo 1518456 3420593 := bstep (se 2 (by rfl) ⟨1282722, by rfl⟩ : syracuseStep 3420593 = 2565445) B2565445
theorem B1708483 : Blo 1518456 1708483 := bstep (se 1 (by rfl) ⟨1281362, by rfl⟩ : syracuseStep 1708483 = 2562725) B2562725
theorem B1520067 : Blo 1518456 1520067 := bstep (se 1 (by rfl) ⟨1140050, by rfl⟩ : syracuseStep 1520067 = 2280101) B2280101
theorem B3420611 : Blo 1518456 3420611 := bstep (se 1 (by rfl) ⟨2565458, by rfl⟩ : syracuseStep 3420611 = 5130917) B5130917
theorem B1520083 : Blo 1518456 1520083 := bstep (se 1 (by rfl) ⟨1140062, by rfl⟩ : syracuseStep 1520083 = 2280125) B2280125
theorem B1520099 : Blo 1518456 1520099 := bstep (se 1 (by rfl) ⟨1140074, by rfl⟩ : syracuseStep 1520099 = 2280149) B2280149
theorem B1520115 : Blo 1518456 1520115 := bstep (se 1 (by rfl) ⟨1140086, by rfl⟩ : syracuseStep 1520115 = 2280173) B2280173
theorem B1520131 : Blo 1518456 1520131 := bstep (se 1 (by rfl) ⟨1140098, by rfl⟩ : syracuseStep 1520131 = 2280197) B2280197
theorem B1520147 : Blo 1518456 1520147 := bstep (se 1 (by rfl) ⟨1140110, by rfl⟩ : syracuseStep 1520147 = 2280221) B2280221
theorem B1520163 : Blo 1518456 1520163 := bstep (se 1 (by rfl) ⟨1140122, by rfl⟩ : syracuseStep 1520163 = 2280245) B2280245
theorem B5198381 : Blo 1518456 5198381 := bstep (se 3 (by rfl) ⟨974696, by rfl⟩ : syracuseStep 5198381 = 1949393) B1949393
theorem B1520179 : Blo 1518456 1520179 := bstep (se 1 (by rfl) ⟨1140134, by rfl⟩ : syracuseStep 1520179 = 2280269) B2280269
theorem B1520195 : Blo 1518456 1520195 := bstep (se 1 (by rfl) ⟨1140146, by rfl⟩ : syracuseStep 1520195 = 2280293) B2280293
theorem B1708627 : Blo 1518456 1708627 := bstep (se 1 (by rfl) ⟨1281470, by rfl⟩ : syracuseStep 1708627 = 2562941) B2562941
theorem B1520211 : Blo 1518456 1520211 := bstep (se 1 (by rfl) ⟨1140158, by rfl⟩ : syracuseStep 1520211 = 2280317) B2280317
theorem B1520227 : Blo 1518456 1520227 := bstep (se 1 (by rfl) ⟨1140170, by rfl⟩ : syracuseStep 1520227 = 2280341) B2280341
theorem B1520243 : Blo 1518456 1520243 := bstep (se 1 (by rfl) ⟨1140182, by rfl⟩ : syracuseStep 1520243 = 2280365) B2280365
theorem B1520259 : Blo 1518456 1520259 := bstep (se 1 (by rfl) ⟨1140194, by rfl⟩ : syracuseStep 1520259 = 2280389) B2280389
theorem B1520275 : Blo 1518456 1520275 := bstep (se 1 (by rfl) ⟨1140206, by rfl⟩ : syracuseStep 1520275 = 2280413) B2280413
theorem B1520291 : Blo 1518456 1520291 := bstep (se 1 (by rfl) ⟨1140218, by rfl⟩ : syracuseStep 1520291 = 2280437) B2280437
theorem B1520307 : Blo 1518456 1520307 := bstep (se 1 (by rfl) ⟨1140230, by rfl⟩ : syracuseStep 1520307 = 2280461) B2280461
theorem B1520323 : Blo 1518456 1520323 := bstep (se 1 (by rfl) ⟨1140242, by rfl⟩ : syracuseStep 1520323 = 2280485) B2280485
theorem B40555205 : Blo 1518456 40555205 := bstep (se 4 (by rfl) ⟨3802050, by rfl⟩ : syracuseStep 40555205 = 7604101) B7604101
theorem B1520339 : Blo 1518456 1520339 := bstep (se 1 (by rfl) ⟨1140254, by rfl⟩ : syracuseStep 1520339 = 2280509) B2280509
theorem B3420881 : Blo 1518456 3420881 := bstep (se 2 (by rfl) ⟨1282830, by rfl⟩ : syracuseStep 3420881 = 2565661) B2565661
theorem B1708771 : Blo 1518456 1708771 := bstep (se 1 (by rfl) ⟨1281578, by rfl⟩ : syracuseStep 1708771 = 2563157) B2563157
theorem B1520355 : Blo 1518456 1520355 := bstep (se 1 (by rfl) ⟨1140266, by rfl⟩ : syracuseStep 1520355 = 2280533) B2280533
theorem B3420899 : Blo 1518456 3420899 := bstep (se 1 (by rfl) ⟨2565674, by rfl⟩ : syracuseStep 3420899 = 5131349) B5131349
theorem B1520371 : Blo 1518456 1520371 := bstep (se 1 (by rfl) ⟨1140278, by rfl⟩ : syracuseStep 1520371 = 2280557) B2280557
theorem B1520387 : Blo 1518456 1520387 := bstep (se 1 (by rfl) ⟨1140290, by rfl⟩ : syracuseStep 1520387 = 2280581) B2280581
theorem B4109069 : Blo 1518456 4109069 := bstep (se 3 (by rfl) ⟨770450, by rfl⟩ : syracuseStep 4109069 = 1540901) B1540901
theorem B1520403 : Blo 1518456 1520403 := bstep (se 1 (by rfl) ⟨1140302, by rfl⟩ : syracuseStep 1520403 = 2280605) B2280605
theorem B1520419 : Blo 1518456 1520419 := bstep (se 1 (by rfl) ⟨1140314, by rfl⟩ : syracuseStep 1520419 = 2280629) B2280629
theorem B1520435 : Blo 1518456 1520435 := bstep (se 1 (by rfl) ⟨1140326, by rfl⟩ : syracuseStep 1520435 = 2280653) B2280653
theorem B1520451 : Blo 1518456 1520451 := bstep (se 1 (by rfl) ⟨1140338, by rfl⟩ : syracuseStep 1520451 = 2280677) B2280677
theorem B5772131 : Blo 1518456 5772131 := bstep (se 1 (by rfl) ⟨4329098, by rfl⟩ : syracuseStep 5772131 = 8658197) B8658197
theorem B5124977 : Blo 1518456 5124977 := bstep (se 2 (by rfl) ⟨1921866, by rfl⟩ : syracuseStep 5124977 = 3843733) B3843733
theorem B1921907 : Blo 1518456 1921907 := bstep (se 1 (by rfl) ⟨1441430, by rfl⟩ : syracuseStep 1921907 = 2882861) B2882861
theorem B1708915 : Blo 1518456 1708915 := bstep (se 1 (by rfl) ⟨1281686, by rfl⟩ : syracuseStep 1708915 = 2563373) B2563373
theorem B1709059 : Blo 1518456 1709059 := bstep (se 1 (by rfl) ⟨1281794, by rfl⟩ : syracuseStep 1709059 = 2563589) B2563589
theorem B7689329 : Blo 1518456 7689329 := bstep (se 2 (by rfl) ⟨2883498, by rfl⟩ : syracuseStep 7689329 = 5766997) B5766997
theorem B72103025 : Blo 1518456 72103025 := bstep (se 2 (by rfl) ⟨27038634, by rfl⟩ : syracuseStep 72103025 = 54077269) B54077269
theorem B5477489 : Blo 1518456 5477489 := bstep (se 2 (by rfl) ⟨2054058, by rfl⟩ : syracuseStep 5477489 = 4108117) B4108117
theorem B1709203 : Blo 1518456 1709203 := bstep (se 1 (by rfl) ⟨1281902, by rfl⟩ : syracuseStep 1709203 = 2563805) B2563805
theorem B3847409 : Blo 1518456 3847409 := bstep (se 2 (by rfl) ⟨1442778, by rfl⟩ : syracuseStep 3847409 = 2885557) B2885557
theorem B1709347 : Blo 1518456 1709347 := bstep (se 1 (by rfl) ⟨1282010, by rfl⟩ : syracuseStep 1709347 = 2564021) B2564021
theorem B3847459 : Blo 1518456 3847459 := bstep (se 1 (by rfl) ⟨2885594, by rfl⟩ : syracuseStep 3847459 = 5771189) B5771189
theorem B5928305 : Blo 1518456 5928305 := bstep (se 2 (by rfl) ⟨2223114, by rfl⟩ : syracuseStep 5928305 = 4446229) B4446229
theorem B5125517 : Blo 1518456 5125517 := bstep (se 3 (by rfl) ⟨961034, by rfl⟩ : syracuseStep 5125517 = 1922069) B1922069
theorem B3847601 : Blo 1518456 3847601 := bstep (se 2 (by rfl) ⟨1442850, by rfl⟩ : syracuseStep 3847601 = 2885701) B2885701
theorem B1709491 : Blo 1518456 1709491 := bstep (se 1 (by rfl) ⟨1282118, by rfl⟩ : syracuseStep 1709491 = 2564237) B2564237
theorem B5125571 : Blo 1518456 5125571 := bstep (se 1 (by rfl) ⟨3844178, by rfl⟩ : syracuseStep 5125571 = 7688357) B7688357
theorem B3651043 : Blo 1518456 3651043 := bstep (se 1 (by rfl) ⟨2738282, by rfl⟩ : syracuseStep 3651043 = 5476565) B5476565
theorem B4109869 : Blo 1518456 4109869 := bstep (se 3 (by rfl) ⟨770600, by rfl⟩ : syracuseStep 4109869 = 1541201) B1541201
theorem B1922611 : Blo 1518456 1922611 := bstep (se 1 (by rfl) ⟨1441958, by rfl⟩ : syracuseStep 1922611 = 2883917) B2883917
theorem B1709635 : Blo 1518456 1709635 := bstep (se 1 (by rfl) ⟨1282226, by rfl⟩ : syracuseStep 1709635 = 2564453) B2564453
theorem B10958435 : Blo 1518456 10958435 := bstep (se 1 (by rfl) ⟨8218826, by rfl⟩ : syracuseStep 10958435 = 16437653) B16437653
theorem B1922707 : Blo 1518456 1922707 := bstep (se 1 (by rfl) ⟨1442030, by rfl⟩ : syracuseStep 1922707 = 2884061) B2884061
theorem B5125841 : Blo 1518456 5125841 := bstep (se 2 (by rfl) ⟨1922190, by rfl⟩ : syracuseStep 5125841 = 3844381) B3844381
theorem B1709779 : Blo 1518456 1709779 := bstep (se 1 (by rfl) ⟨1282334, by rfl⟩ : syracuseStep 1709779 = 2564669) B2564669
theorem B3651313 : Blo 1518456 3651313 := bstep (se 2 (by rfl) ⟨1369242, by rfl⟩ : syracuseStep 3651313 = 2738485) B2738485
theorem B4618019 : Blo 1518456 4618019 := bstep (se 1 (by rfl) ⟨3463514, by rfl⟩ : syracuseStep 4618019 = 6927029) B6927029
theorem B1709923 : Blo 1518456 1709923 := bstep (se 1 (by rfl) ⟨1282442, by rfl⟩ : syracuseStep 1709923 = 2564885) B2564885
theorem B8656739 : Blo 1518456 8656739 := bstep (se 1 (by rfl) ⟨6492554, by rfl⟩ : syracuseStep 8656739 = 12985109) B12985109
theorem B7796621 : Blo 1518456 7796621 := bstep (se 3 (by rfl) ⟨1461866, by rfl⟩ : syracuseStep 7796621 = 2923733) B2923733
theorem B6494093 : Blo 1518456 6494093 := bstep (se 3 (by rfl) ⟨1217642, by rfl⟩ : syracuseStep 6494093 = 2435285) B2435285
theorem B10401733 : Blo 1518456 10401733 := bstep (se 4 (by rfl) ⟨975162, by rfl⟩ : syracuseStep 10401733 = 1950325) B1950325
theorem B7026659 : Blo 1518456 7026659 := bstep (se 1 (by rfl) ⟨5269994, by rfl⟩ : syracuseStep 7026659 = 10539989) B10539989
theorem B1710067 : Blo 1518456 1710067 := bstep (se 1 (by rfl) ⟨1282550, by rfl⟩ : syracuseStep 1710067 = 2565101) B2565101
theorem B16431173 : Blo 1518456 16431173 := bstep (se 4 (by rfl) ⟨1540422, by rfl⟩ : syracuseStep 16431173 = 3080845) B3080845
theorem B38959217 : Blo 1518456 38959217 := bstep (se 2 (by rfl) ⟨14609706, by rfl⟩ : syracuseStep 38959217 = 29219413) B29219413
theorem B1923203 : Blo 1518456 1923203 := bstep (se 1 (by rfl) ⟨1442402, by rfl⟩ : syracuseStep 1923203 = 2884805) B2884805
theorem B2193539 : Blo 1518456 2193539 := bstep (se 1 (by rfl) ⟨1645154, by rfl⟩ : syracuseStep 2193539 = 3290309) B3290309
theorem B1710211 : Blo 1518456 1710211 := bstep (se 1 (by rfl) ⟨1282658, by rfl⟩ : syracuseStep 1710211 = 2565317) B2565317
theorem B7297165 : Blo 1518456 7297165 := bstep (se 3 (by rfl) ⟨1368218, by rfl⟩ : syracuseStep 7297165 = 2736437) B2736437
theorem B5126381 : Blo 1518456 5126381 := bstep (se 3 (by rfl) ⟨961196, by rfl⟩ : syracuseStep 5126381 = 1922393) B1922393
theorem B17307917 : Blo 1518456 17307917 := bstep (se 3 (by rfl) ⟨3245234, by rfl⟩ : syracuseStep 17307917 = 6490469) B6490469
theorem B1710355 : Blo 1518456 1710355 := bstep (se 1 (by rfl) ⟨1282766, by rfl⟩ : syracuseStep 1710355 = 2565533) B2565533
theorem B5126435 : Blo 1518456 5126435 := bstep (se 1 (by rfl) ⟨3844826, by rfl⟩ : syracuseStep 5126435 = 7689653) B7689653
theorem B2562401 : Blo 1518456 2562401 := bstep (se 2 (by rfl) ⟨960900, by rfl⟩ : syracuseStep 2562401 = 1921801) B1921801
theorem B9738629 : Blo 1518456 9738629 := bstep (se 4 (by rfl) ⟨912996, by rfl⟩ : syracuseStep 9738629 = 1825993) B1825993
theorem B3848593 : Blo 1518456 3848593 := bstep (se 2 (by rfl) ⟨1443222, by rfl⟩ : syracuseStep 3848593 = 2886445) B2886445
theorem B5765539 : Blo 1518456 5765539 := bstep (se 1 (by rfl) ⟨4324154, by rfl⟩ : syracuseStep 5765539 = 8648309) B8648309
theorem B1710499 : Blo 1518456 1710499 := bstep (se 1 (by rfl) ⟨1282874, by rfl⟩ : syracuseStep 1710499 = 2565749) B2565749
theorem B1644995 : Blo 1518456 1644995 := bstep (se 1 (by rfl) ⟨1233746, by rfl⟩ : syracuseStep 1644995 = 2467493) B2467493
theorem B2562529 : Blo 1518456 2562529 := bstep (se 2 (by rfl) ⟨960948, by rfl⟩ : syracuseStep 2562529 = 1921897) B1921897
theorem B2562563 : Blo 1518456 2562563 := bstep (se 1 (by rfl) ⟨1921922, by rfl⟩ : syracuseStep 2562563 = 3843845) B3843845
theorem B7690787 : Blo 1518456 7690787 := bstep (se 1 (by rfl) ⟨5768090, by rfl⟩ : syracuseStep 7690787 = 11536181) B11536181
theorem B5126705 : Blo 1518456 5126705 := bstep (se 2 (by rfl) ⟨1922514, by rfl⟩ : syracuseStep 5126705 = 3845029) B3845029
theorem B2194001 : Blo 1518456 2194001 := bstep (se 2 (by rfl) ⟨822750, by rfl⟩ : syracuseStep 2194001 = 1645501) B1645501
theorem B2562691 : Blo 1518456 2562691 := bstep (se 1 (by rfl) ⟨1922018, by rfl⟩ : syracuseStep 2562691 = 3844037) B3844037
theorem B3652273 : Blo 1518456 3652273 := bstep (se 2 (by rfl) ⟨1369602, by rfl⟩ : syracuseStep 3652273 = 2739205) B2739205
theorem B2562833 : Blo 1518456 2562833 := bstep (se 2 (by rfl) ⟨961062, by rfl⟩ : syracuseStep 2562833 = 1922125) B1922125
theorem B1923907 : Blo 1518456 1923907 := bstep (se 1 (by rfl) ⟨1442930, by rfl⟩ : syracuseStep 1923907 = 2885861) B2885861
theorem B2562961 : Blo 1518456 2562961 := bstep (se 2 (by rfl) ⟨961110, by rfl⟩ : syracuseStep 2562961 = 1922221) B1922221
theorem B4864931 : Blo 1518456 4864931 := bstep (se 1 (by rfl) ⟨3648698, by rfl⟩ : syracuseStep 4864931 = 7297397) B7297397
theorem B3464099 : Blo 1518456 3464099 := bstep (se 1 (by rfl) ⟨2598074, by rfl⟩ : syracuseStep 3464099 = 5196149) B5196149
theorem B1924003 : Blo 1518456 1924003 := bstep (se 1 (by rfl) ⟨1443002, by rfl⟩ : syracuseStep 1924003 = 2886005) B2886005
theorem B2562995 : Blo 1518456 2562995 := bstep (se 1 (by rfl) ⟨1922246, by rfl⟩ : syracuseStep 2562995 = 3844493) B3844493
theorem B4324337 : Blo 1518456 4324337 := bstep (se 2 (by rfl) ⟨1621626, by rfl⟩ : syracuseStep 4324337 = 3243253) B3243253
theorem B2563123 : Blo 1518456 2563123 := bstep (se 1 (by rfl) ⟨1922342, by rfl⟩ : syracuseStep 2563123 = 3844685) B3844685
theorem B5127245 : Blo 1518456 5127245 := bstep (se 3 (by rfl) ⟨961358, by rfl⟩ : syracuseStep 5127245 = 1922717) B1922717
theorem B19725425 : Blo 1518456 19725425 := bstep (se 2 (by rfl) ⟨7397034, by rfl⟩ : syracuseStep 19725425 = 14794069) B14794069
theorem B5127299 : Blo 1518456 5127299 := bstep (se 1 (by rfl) ⟨3845474, by rfl⟩ : syracuseStep 5127299 = 7690949) B7690949
theorem B7298225 : Blo 1518456 7298225 := bstep (se 2 (by rfl) ⟨2736834, by rfl⟩ : syracuseStep 7298225 = 5473669) B5473669
theorem B2563265 : Blo 1518456 2563265 := bstep (se 2 (by rfl) ⟨961224, by rfl⟩ : syracuseStep 2563265 = 1922449) B1922449
theorem B18742499 : Blo 1518456 18742499 := bstep (se 1 (by rfl) ⟨14056874, by rfl⟩ : syracuseStep 18742499 = 28113749) B28113749
theorem B10951949 : Blo 1518456 10951949 := bstep (se 3 (by rfl) ⟨2053490, by rfl⟩ : syracuseStep 10951949 = 4106981) B4106981
theorem B2563393 : Blo 1518456 2563393 := bstep (se 2 (by rfl) ⟨961272, by rfl⟩ : syracuseStep 2563393 = 1922545) B1922545
theorem B7691597 : Blo 1518456 7691597 := bstep (se 3 (by rfl) ⟨1442174, by rfl⟩ : syracuseStep 7691597 = 2884349) B2884349
theorem B2563427 : Blo 1518456 2563427 := bstep (se 1 (by rfl) ⟨1922570, by rfl⟩ : syracuseStep 2563427 = 3845141) B3845141
theorem B5127569 : Blo 1518456 5127569 := bstep (se 2 (by rfl) ⟨1922838, by rfl⟩ : syracuseStep 5127569 = 3845677) B3845677
theorem B1539523 : Blo 1518456 1539523 := bstep (se 1 (by rfl) ⟨1154642, by rfl⟩ : syracuseStep 1539523 = 2309285) B2309285
theorem B2883043 : Blo 1518456 2883043 := bstep (se 1 (by rfl) ⟨2162282, by rfl⟩ : syracuseStep 2883043 = 4324565) B4324565
theorem B2563555 : Blo 1518456 2563555 := bstep (se 1 (by rfl) ⟨1922666, by rfl⟩ : syracuseStep 2563555 = 3845333) B3845333
theorem B4865521 : Blo 1518456 4865521 := bstep (se 2 (by rfl) ⟨1824570, by rfl⟩ : syracuseStep 4865521 = 3649141) B3649141
theorem B2883089 : Blo 1518456 2883089 := bstep (se 2 (by rfl) ⟨1081158, by rfl⟩ : syracuseStep 2883089 = 2162317) B2162317
theorem B2162209 : Blo 1518456 2162209 := bstep (se 2 (by rfl) ⟨810828, by rfl⟩ : syracuseStep 2162209 = 1621657) B1621657
theorem B2563697 : Blo 1518456 2563697 := bstep (se 2 (by rfl) ⟨961386, by rfl⟩ : syracuseStep 2563697 = 1922773) B1922773
theorem B20799089 : Blo 1518456 20799089 := bstep (se 2 (by rfl) ⟨7799658, by rfl⟩ : syracuseStep 20799089 = 15599317) B15599317
theorem B13868657 : Blo 1518456 13868657 := bstep (se 2 (by rfl) ⟨5200746, by rfl⟩ : syracuseStep 13868657 = 10401493) B10401493
theorem B2162305 : Blo 1518456 2162305 := bstep (se 2 (by rfl) ⟨810864, by rfl⟩ : syracuseStep 2162305 = 1621729) B1621729
theorem B2563825 : Blo 1518456 2563825 := bstep (se 2 (by rfl) ⟨961434, by rfl⟩ : syracuseStep 2563825 = 1922869) B1922869
theorem B1539859 : Blo 1518456 1539859 := bstep (se 1 (by rfl) ⟨1154894, by rfl⟩ : syracuseStep 1539859 = 2309789) B2309789
theorem B2563859 : Blo 1518456 2563859 := bstep (se 1 (by rfl) ⟨1922894, by rfl⟩ : syracuseStep 2563859 = 3845789) B3845789
theorem B2080561 : Blo 1518456 2080561 := bstep (se 2 (by rfl) ⟨780210, by rfl⟩ : syracuseStep 2080561 = 1560421) B1560421
theorem B2883377 : Blo 1518456 2883377 := bstep (se 2 (by rfl) ⟨1081266, by rfl⟩ : syracuseStep 2883377 = 2162533) B2162533
theorem B2309939 : Blo 1518456 2309939 := bstep (se 1 (by rfl) ⟨1732454, by rfl⟩ : syracuseStep 2309939 = 3464909) B3464909
theorem B25968437 : Blo 1518456 25968437 := bstep (se 5 (by rfl) ⟨1217270, by rfl⟩ : syracuseStep 25968437 = 2434541) B2434541
theorem B15589219 : Blo 1518456 15589219 := bstep (se 1 (by rfl) ⟨11691914, by rfl⟩ : syracuseStep 15589219 = 23383829) B23383829
theorem B2563987 : Blo 1518456 2563987 := bstep (se 1 (by rfl) ⟨1922990, by rfl⟩ : syracuseStep 2563987 = 3845981) B3845981
theorem B5128109 : Blo 1518456 5128109 := bstep (se 3 (by rfl) ⟨961520, by rfl⟩ : syracuseStep 5128109 = 1923041) B1923041
theorem B2465731 : Blo 1518456 2465731 := bstep (se 1 (by rfl) ⟨1849298, by rfl⟩ : syracuseStep 2465731 = 3698597) B3698597
theorem B3243971 : Blo 1518456 3243971 := bstep (se 1 (by rfl) ⟨2432978, by rfl⟩ : syracuseStep 3243971 = 4865957) B4865957
theorem B5128163 : Blo 1518456 5128163 := bstep (se 1 (by rfl) ⟨3846122, by rfl⟩ : syracuseStep 5128163 = 7692245) B7692245
theorem B11542499 : Blo 1518456 11542499 := bstep (se 1 (by rfl) ⟨8656874, by rfl⟩ : syracuseStep 11542499 = 17313749) B17313749
theorem B5554241 : Blo 1518456 5554241 := bstep (se 2 (by rfl) ⟨2082840, by rfl⟩ : syracuseStep 5554241 = 4165681) B4165681
theorem B2564183 : Blo 1518456 2564183 := bstep (se 1 (by rfl) ⟨1923137, by rfl⟩ : syracuseStep 2564183 = 3846275) B3846275
theorem B62414999 : Blo 1518456 62414999 := bstep (se 1 (by rfl) ⟨46811249, by rfl⟩ : syracuseStep 62414999 = 93622499) B93622499
theorem B4161739 : Blo 1518456 4161739 := bstep (se 1 (by rfl) ⟨3121304, by rfl⟩ : syracuseStep 4161739 = 6242609) B6242609
theorem B2564311 : Blo 1518456 2564311 := bstep (se 1 (by rfl) ⟨1923233, by rfl⟩ : syracuseStep 2564311 = 3846467) B3846467
theorem B2883863 : Blo 1518456 2883863 := bstep (se 1 (by rfl) ⟨2162897, by rfl⟩ : syracuseStep 2883863 = 4325795) B4325795
theorem B3244313 : Blo 1518456 3244313 := bstep (se 2 (by rfl) ⟨1216617, by rfl⟩ : syracuseStep 3244313 = 2433235) B2433235
theorem B5767469 : Blo 1518456 5767469 := bstep (se 3 (by rfl) ⟨1081400, by rfl⟩ : syracuseStep 5767469 = 2162801) B2162801
theorem B1622327 : Blo 1518456 1622327 := bstep (se 1 (by rfl) ⟨1216745, by rfl⟩ : syracuseStep 1622327 = 2433491) B2433491
theorem B2277707 : Blo 1518456 2277707 := bstep (se 1 (by rfl) ⟨1708280, by rfl⟩ : syracuseStep 2277707 = 3416561) B3416561
theorem B4686155 : Blo 1518456 4686155 := bstep (se 1 (by rfl) ⟨3514616, by rfl⟩ : syracuseStep 4686155 = 7029233) B7029233
theorem B2277719 : Blo 1518456 2277719 := bstep (se 1 (by rfl) ⟨1708289, by rfl⟩ : syracuseStep 2277719 = 3416579) B3416579
theorem B5128541 : Blo 1518456 5128541 := bstep (se 3 (by rfl) ⟨961601, by rfl⟩ : syracuseStep 5128541 = 1923203) B1923203
theorem B5849437 : Blo 1518456 5849437 := bstep (se 3 (by rfl) ⟨1096769, by rfl⟩ : syracuseStep 5849437 = 2193539) B2193539
theorem B3465587 : Blo 1518456 3465587 := bstep (se 1 (by rfl) ⟨2599190, by rfl⟩ : syracuseStep 3465587 = 5198381) B5198381
theorem B11534723 : Blo 1518456 11534723 := bstep (se 1 (by rfl) ⟨8651042, by rfl⟩ : syracuseStep 11534723 = 17302085) B17302085
theorem B2277785 : Blo 1518456 2277785 := bstep (se 2 (by rfl) ⟨854169, by rfl⟩ : syracuseStep 2277785 = 1708339) B1708339
theorem B8651225 : Blo 1518456 8651225 := bstep (se 2 (by rfl) ⟨3244209, by rfl⟩ : syracuseStep 8651225 = 6488419) B6488419
theorem B2277899 : Blo 1518456 2277899 := bstep (se 1 (by rfl) ⟨1708424, by rfl⟩ : syracuseStep 2277899 = 3416849) B3416849
theorem B5472791 : Blo 1518456 5472791 := bstep (se 1 (by rfl) ⟨4104593, by rfl⟩ : syracuseStep 5472791 = 8209187) B8209187
theorem B2277911 : Blo 1518456 2277911 := bstep (se 1 (by rfl) ⟨1708433, by rfl⟩ : syracuseStep 2277911 = 3416867) B3416867
theorem B3416651 : Blo 1518456 3416651 := bstep (se 1 (by rfl) ⟨2562488, by rfl⟩ : syracuseStep 3416651 = 5124977) B5124977
theorem B2277977 : Blo 1518456 2277977 := bstep (se 2 (by rfl) ⟨854241, by rfl⟩ : syracuseStep 2277977 = 1708483) B1708483
theorem B4325977 : Blo 1518456 4325977 := bstep (se 2 (by rfl) ⟨1622241, by rfl⟩ : syracuseStep 4325977 = 3244483) B3244483
theorem B7692893 : Blo 1518456 7692893 := bstep (se 3 (by rfl) ⟨1442417, by rfl⟩ : syracuseStep 7692893 = 2884835) B2884835
theorem B2736755 : Blo 1518456 2736755 := bstep (se 1 (by rfl) ⟨2052566, by rfl⟩ : syracuseStep 2736755 = 4105133) B4105133
theorem B3416705 : Blo 1518456 3416705 := bstep (se 2 (by rfl) ⟨1281264, by rfl⟩ : syracuseStep 3416705 = 2562529) B2562529
theorem B2163353 : Blo 1518456 2163353 := bstep (se 2 (by rfl) ⟨811257, by rfl⟩ : syracuseStep 2163353 = 1622515) B1622515
theorem B2278091 : Blo 1518456 2278091 := bstep (se 1 (by rfl) ⟨1708568, by rfl⟩ : syracuseStep 2278091 = 3417137) B3417137
theorem B29205197 : Blo 1518456 29205197 := bstep (se 3 (by rfl) ⟨5475974, by rfl⟩ : syracuseStep 29205197 = 10951949) B10951949
theorem B2278103 : Blo 1518456 2278103 := bstep (se 1 (by rfl) ⟨1708577, by rfl⟩ : syracuseStep 2278103 = 3417155) B3417155
theorem B2163467 : Blo 1518456 2163467 := bstep (se 1 (by rfl) ⟨1622600, by rfl⟩ : syracuseStep 2163467 = 3245201) B3245201
theorem B7299857 : Blo 1518456 7299857 := bstep (se 2 (by rfl) ⟨2737446, by rfl⟩ : syracuseStep 7299857 = 5474893) B5474893
theorem B2278169 : Blo 1518456 2278169 := bstep (se 2 (by rfl) ⟨854313, by rfl⟩ : syracuseStep 2278169 = 1708627) B1708627
theorem B2884403 : Blo 1518456 2884403 := bstep (se 1 (by rfl) ⟨2163302, by rfl⟩ : syracuseStep 2884403 = 4326605) B4326605
theorem B2564939 : Blo 1518456 2564939 := bstep (se 1 (by rfl) ⟨1923704, by rfl⟩ : syracuseStep 2564939 = 3847409) B3847409
theorem B3416921 : Blo 1518456 3416921 := bstep (se 2 (by rfl) ⟨1281345, by rfl⟩ : syracuseStep 3416921 = 2562691) B2562691
theorem B2278283 : Blo 1518456 2278283 := bstep (se 1 (by rfl) ⟨1708712, by rfl⟩ : syracuseStep 2278283 = 3417425) B3417425
theorem B2278295 : Blo 1518456 2278295 := bstep (se 1 (by rfl) ⟨1708721, by rfl⟩ : syracuseStep 2278295 = 3417443) B3417443
theorem B3417011 : Blo 1518456 3417011 := bstep (se 1 (by rfl) ⟨2562758, by rfl⟩ : syracuseStep 3417011 = 5125517) B5125517
theorem B6489035 : Blo 1518456 6489035 := bstep (se 1 (by rfl) ⟨4866776, by rfl⟩ : syracuseStep 6489035 = 9733553) B9733553
theorem B2565067 : Blo 1518456 2565067 := bstep (se 1 (by rfl) ⟨1923800, by rfl⟩ : syracuseStep 2565067 = 3847601) B3847601
theorem B3417047 : Blo 1518456 3417047 := bstep (se 1 (by rfl) ⟨2562785, by rfl⟩ : syracuseStep 3417047 = 5125571) B5125571
theorem B2278361 : Blo 1518456 2278361 := bstep (se 2 (by rfl) ⟨854385, by rfl⟩ : syracuseStep 2278361 = 1708771) B1708771
theorem B4326365 : Blo 1518456 4326365 := bstep (se 3 (by rfl) ⟨811193, by rfl⟩ : syracuseStep 4326365 = 1622387) B1622387
theorem B5768243 : Blo 1518456 5768243 := bstep (se 1 (by rfl) ⟨4326182, by rfl⟩ : syracuseStep 5768243 = 8652365) B8652365
theorem B4867123 : Blo 1518456 4867123 := bstep (se 1 (by rfl) ⟨3650342, by rfl⟩ : syracuseStep 4867123 = 7300685) B7300685
theorem B2278475 : Blo 1518456 2278475 := bstep (se 1 (by rfl) ⟨1708856, by rfl⟩ : syracuseStep 2278475 = 3417713) B3417713
theorem B2278487 : Blo 1518456 2278487 := bstep (se 1 (by rfl) ⟨1708865, by rfl⟩ : syracuseStep 2278487 = 3417731) B3417731
theorem B2565209 : Blo 1518456 2565209 := bstep (se 2 (by rfl) ⟨961953, by rfl⟩ : syracuseStep 2565209 = 1923907) B1923907
theorem B3417227 : Blo 1518456 3417227 := bstep (se 1 (by rfl) ⟨2562920, by rfl⟩ : syracuseStep 3417227 = 5125841) B5125841
theorem B2278553 : Blo 1518456 2278553 := bstep (se 2 (by rfl) ⟨854457, by rfl⟩ : syracuseStep 2278553 = 1708915) B1708915
theorem B3417281 : Blo 1518456 3417281 := bstep (se 2 (by rfl) ⟨1281480, by rfl⟩ : syracuseStep 3417281 = 2562961) B2562961
theorem B2565337 : Blo 1518456 2565337 := bstep (se 2 (by rfl) ⟨962001, by rfl⟩ : syracuseStep 2565337 = 1924003) B1924003
theorem B2278667 : Blo 1518456 2278667 := bstep (se 1 (by rfl) ⟨1709000, by rfl⟩ : syracuseStep 2278667 = 3418001) B3418001
theorem B2278679 : Blo 1518456 2278679 := bstep (se 1 (by rfl) ⟨1709009, by rfl⟩ : syracuseStep 2278679 = 3418019) B3418019
theorem B2163991 : Blo 1518456 2163991 := bstep (se 1 (by rfl) ⟨1622993, by rfl⟩ : syracuseStep 2163991 = 3245987) B3245987
theorem B2884889 : Blo 1518456 2884889 := bstep (se 2 (by rfl) ⟨1081833, by rfl⟩ : syracuseStep 2884889 = 2163667) B2163667
theorem B2278745 : Blo 1518456 2278745 := bstep (se 2 (by rfl) ⟨854529, by rfl⟩ : syracuseStep 2278745 = 1709059) B1709059
theorem B10954115 : Blo 1518456 10954115 := bstep (se 1 (by rfl) ⟨8215586, by rfl⟩ : syracuseStep 10954115 = 16431173) B16431173
theorem B3417497 : Blo 1518456 3417497 := bstep (se 2 (by rfl) ⟨1281561, by rfl⟩ : syracuseStep 3417497 = 2563123) B2563123
theorem B2278859 : Blo 1518456 2278859 := bstep (se 1 (by rfl) ⟨1709144, by rfl⟩ : syracuseStep 2278859 = 3418289) B3418289
theorem B5129675 : Blo 1518456 5129675 := bstep (se 1 (by rfl) ⟨3847256, by rfl⟩ : syracuseStep 5129675 = 7694513) B7694513
theorem B2278871 : Blo 1518456 2278871 := bstep (se 1 (by rfl) ⟨1709153, by rfl⟩ : syracuseStep 2278871 = 3418307) B3418307
theorem B3417587 : Blo 1518456 3417587 := bstep (se 1 (by rfl) ⟨2563190, by rfl⟩ : syracuseStep 3417587 = 5126381) B5126381
theorem B21890573 : Blo 1518456 21890573 := bstep (se 3 (by rfl) ⟨4104482, by rfl⟩ : syracuseStep 21890573 = 8208965) B8208965
theorem B3417623 : Blo 1518456 3417623 := bstep (se 1 (by rfl) ⟨2563217, by rfl⟩ : syracuseStep 3417623 = 5126435) B5126435
theorem B2278937 : Blo 1518456 2278937 := bstep (se 2 (by rfl) ⟨854601, by rfl⟩ : syracuseStep 2278937 = 1709203) B1709203
theorem B2279051 : Blo 1518456 2279051 := bstep (se 1 (by rfl) ⟨1709288, by rfl⟩ : syracuseStep 2279051 = 3418577) B3418577
theorem B5473943 : Blo 1518456 5473943 := bstep (se 1 (by rfl) ⟨4105457, by rfl⟩ : syracuseStep 5473943 = 8210915) B8210915
theorem B2279063 : Blo 1518456 2279063 := bstep (se 1 (by rfl) ⟨1709297, by rfl⟩ : syracuseStep 2279063 = 3418595) B3418595
theorem B3417803 : Blo 1518456 3417803 := bstep (se 1 (by rfl) ⟨2563352, by rfl⟩ : syracuseStep 3417803 = 5126705) B5126705
theorem B2279129 : Blo 1518456 2279129 := bstep (se 2 (by rfl) ⟨854673, by rfl⟩ : syracuseStep 2279129 = 1709347) B1709347
theorem B5129945 : Blo 1518456 5129945 := bstep (se 2 (by rfl) ⟨1923729, by rfl⟩ : syracuseStep 5129945 = 3847459) B3847459
theorem B6489821 : Blo 1518456 6489821 := bstep (se 3 (by rfl) ⟨1216841, by rfl⟩ : syracuseStep 6489821 = 2433683) B2433683
theorem B3417857 : Blo 1518456 3417857 := bstep (se 2 (by rfl) ⟨1281696, by rfl⟩ : syracuseStep 3417857 = 2563393) B2563393
theorem B20801285 : Blo 1518456 20801285 := bstep (se 4 (by rfl) ⟨1950120, by rfl⟩ : syracuseStep 20801285 = 3900241) B3900241
theorem B2279243 : Blo 1518456 2279243 := bstep (se 1 (by rfl) ⟨1709432, by rfl⟩ : syracuseStep 2279243 = 3418865) B3418865
theorem B2279255 : Blo 1518456 2279255 := bstep (se 1 (by rfl) ⟨1709441, by rfl⟩ : syracuseStep 2279255 = 3418883) B3418883
theorem B3245953 : Blo 1518456 3245953 := bstep (se 2 (by rfl) ⟨1217232, by rfl⟩ : syracuseStep 3245953 = 2434465) B2434465
theorem B2279321 : Blo 1518456 2279321 := bstep (se 2 (by rfl) ⟨854745, by rfl⟩ : syracuseStep 2279321 = 1709491) B1709491
theorem B3844057 : Blo 1518456 3844057 := bstep (se 2 (by rfl) ⟨1441521, by rfl⟩ : syracuseStep 3844057 = 2883043) B2883043
theorem B3418073 : Blo 1518456 3418073 := bstep (se 2 (by rfl) ⟨1281777, by rfl⟩ : syracuseStep 3418073 = 2563555) B2563555
theorem B4868057 : Blo 1518456 4868057 := bstep (se 2 (by rfl) ⟨1825521, by rfl⟩ : syracuseStep 4868057 = 3651043) B3651043
theorem B2279435 : Blo 1518456 2279435 := bstep (se 1 (by rfl) ⟨1709576, by rfl⟩ : syracuseStep 2279435 = 3419153) B3419153
theorem B2279447 : Blo 1518456 2279447 := bstep (se 1 (by rfl) ⟨1709585, by rfl⟩ : syracuseStep 2279447 = 3419171) B3419171
theorem B3418163 : Blo 1518456 3418163 := bstep (se 1 (by rfl) ⟨2563622, by rfl⟩ : syracuseStep 3418163 = 5127245) B5127245
theorem B8652865 : Blo 1518456 8652865 := bstep (se 2 (by rfl) ⟨3244824, by rfl⟩ : syracuseStep 8652865 = 6489649) B6489649
theorem B13150283 : Blo 1518456 13150283 := bstep (se 1 (by rfl) ⟨9862712, by rfl⟩ : syracuseStep 13150283 = 19725425) B19725425
theorem B2164811 : Blo 1518456 2164811 := bstep (se 1 (by rfl) ⟨1623608, by rfl⟩ : syracuseStep 2164811 = 3247217) B3247217
theorem B3418199 : Blo 1518456 3418199 := bstep (se 1 (by rfl) ⟨2563649, by rfl⟩ : syracuseStep 3418199 = 5127299) B5127299
theorem B2279513 : Blo 1518456 2279513 := bstep (se 2 (by rfl) ⟨854817, by rfl⟩ : syracuseStep 2279513 = 1709635) B1709635
theorem B12314717 : Blo 1518456 12314717 := bstep (se 3 (by rfl) ⟨2309009, by rfl⟩ : syracuseStep 12314717 = 4618019) B4618019
theorem B12494999 : Blo 1518456 12494999 := bstep (se 1 (by rfl) ⟨9371249, by rfl⟩ : syracuseStep 12494999 = 18742499) B18742499
theorem B2279627 : Blo 1518456 2279627 := bstep (se 1 (by rfl) ⟨1709720, by rfl⟩ : syracuseStep 2279627 = 3419441) B3419441
theorem B2279639 : Blo 1518456 2279639 := bstep (se 1 (by rfl) ⟨1709729, by rfl⟩ : syracuseStep 2279639 = 3419459) B3419459
theorem B3418379 : Blo 1518456 3418379 := bstep (se 1 (by rfl) ⟨2563784, by rfl⟩ : syracuseStep 3418379 = 5127569) B5127569
theorem B2279705 : Blo 1518456 2279705 := bstep (se 2 (by rfl) ⟨854889, by rfl⟩ : syracuseStep 2279705 = 1709779) B1709779
theorem B3418433 : Blo 1518456 3418433 := bstep (se 2 (by rfl) ⟨1281912, by rfl⟩ : syracuseStep 3418433 = 2563825) B2563825
theorem B4868417 : Blo 1518456 4868417 := bstep (se 2 (by rfl) ⟨1825656, by rfl⟩ : syracuseStep 4868417 = 3651313) B3651313
theorem B13150565 : Blo 1518456 13150565 := bstep (se 4 (by rfl) ⟨1232865, by rfl⟩ : syracuseStep 13150565 = 2465731) B2465731
theorem B2279819 : Blo 1518456 2279819 := bstep (se 1 (by rfl) ⟨1709864, by rfl⟩ : syracuseStep 2279819 = 3419729) B3419729
theorem B2279831 : Blo 1518456 2279831 := bstep (se 1 (by rfl) ⟨1709873, by rfl⟩ : syracuseStep 2279831 = 3419747) B3419747
theorem B5130647 : Blo 1518456 5130647 := bstep (se 1 (by rfl) ⟨3847985, by rfl⟩ : syracuseStep 5130647 = 7695971) B7695971
theorem B9734579 : Blo 1518456 9734579 := bstep (se 1 (by rfl) ⟨7300934, by rfl⟩ : syracuseStep 9734579 = 14601869) B14601869
theorem B3246551 : Blo 1518456 3246551 := bstep (se 1 (by rfl) ⟨2434913, by rfl⟩ : syracuseStep 3246551 = 4869827) B4869827
theorem B20785625 : Blo 1518456 20785625 := bstep (se 2 (by rfl) ⟨7794609, by rfl⟩ : syracuseStep 20785625 = 15589219) B15589219
theorem B2279897 : Blo 1518456 2279897 := bstep (se 2 (by rfl) ⟨854961, by rfl⟩ : syracuseStep 2279897 = 1709923) B1709923
theorem B5769731 : Blo 1518456 5769731 := bstep (se 1 (by rfl) ⟨4327298, by rfl⟩ : syracuseStep 5769731 = 8654597) B8654597
theorem B3418649 : Blo 1518456 3418649 := bstep (se 2 (by rfl) ⟨1281993, by rfl⟩ : syracuseStep 3418649 = 2563987) B2563987
theorem B17312291 : Blo 1518456 17312291 := bstep (se 1 (by rfl) ⟨12984218, by rfl⟩ : syracuseStep 17312291 = 25968437) B25968437
theorem B2280011 : Blo 1518456 2280011 := bstep (se 1 (by rfl) ⟨1710008, by rfl⟩ : syracuseStep 2280011 = 3420017) B3420017
theorem B2280023 : Blo 1518456 2280023 := bstep (se 1 (by rfl) ⟨1710017, by rfl⟩ : syracuseStep 2280023 = 3420035) B3420035
theorem B3418739 : Blo 1518456 3418739 := bstep (se 1 (by rfl) ⟨2564054, by rfl⟩ : syracuseStep 3418739 = 5128109) B5128109
theorem B3418775 : Blo 1518456 3418775 := bstep (se 1 (by rfl) ⟨2564081, by rfl⟩ : syracuseStep 3418775 = 5128163) B5128163
theorem B7694999 : Blo 1518456 7694999 := bstep (se 1 (by rfl) ⟨5771249, by rfl⟩ : syracuseStep 7694999 = 11542499) B11542499
theorem B2280089 : Blo 1518456 2280089 := bstep (se 2 (by rfl) ⟨855033, by rfl⟩ : syracuseStep 2280089 = 1710067) B1710067
theorem B2886347 : Blo 1518456 2886347 := bstep (se 1 (by rfl) ⟨2164760, by rfl⟩ : syracuseStep 2886347 = 4329521) B4329521
theorem B2280203 : Blo 1518456 2280203 := bstep (se 1 (by rfl) ⟨1710152, by rfl⟩ : syracuseStep 2280203 = 3420305) B3420305
theorem B2280215 : Blo 1518456 2280215 := bstep (se 1 (by rfl) ⟨1710161, by rfl⟩ : syracuseStep 2280215 = 3420323) B3420323
theorem B7301933 : Blo 1518456 7301933 := bstep (se 3 (by rfl) ⟨1369112, by rfl⟩ : syracuseStep 7301933 = 2738225) B2738225
theorem B32877377 : Blo 1518456 32877377 := bstep (se 2 (by rfl) ⟨12329016, by rfl⟩ : syracuseStep 32877377 = 24658033) B24658033
theorem B3418955 : Blo 1518456 3418955 := bstep (se 1 (by rfl) ⟨2564216, by rfl⟩ : syracuseStep 3418955 = 5128433) B5128433
theorem B2280281 : Blo 1518456 2280281 := bstep (se 2 (by rfl) ⟨855105, by rfl⟩ : syracuseStep 2280281 = 1710211) B1710211
theorem B3419009 : Blo 1518456 3419009 := bstep (se 2 (by rfl) ⟨1282128, by rfl⟩ : syracuseStep 3419009 = 2564257) B2564257
theorem B1518475 : Blo 1518456 1518475 := bstep (se 1 (by rfl) ⟨1138856, by rfl⟩ : syracuseStep 1518475 = 2277713) B2277713
theorem B1518487 : Blo 1518456 1518487 := bstep (se 1 (by rfl) ⟨1138865, by rfl⟩ : syracuseStep 1518487 = 2277731) B2277731
theorem B1518507 : Blo 1518456 1518507 := bstep (se 1 (by rfl) ⟨1138880, by rfl⟩ : syracuseStep 1518507 = 2277761) B2277761
theorem B5131187 : Blo 1518456 5131187 := bstep (se 1 (by rfl) ⟨3848390, by rfl⟩ : syracuseStep 5131187 = 7696781) B7696781
theorem B1518519 : Blo 1518456 1518519 := bstep (se 1 (by rfl) ⟨1138889, by rfl⟩ : syracuseStep 1518519 = 2277779) B2277779
theorem B1518539 : Blo 1518456 1518539 := bstep (se 1 (by rfl) ⟨1138904, by rfl⟩ : syracuseStep 1518539 = 2277809) B2277809
theorem B5770187 : Blo 1518456 5770187 := bstep (se 1 (by rfl) ⟨4327640, by rfl⟩ : syracuseStep 5770187 = 8655281) B8655281
theorem B2280395 : Blo 1518456 2280395 := bstep (se 1 (by rfl) ⟨1710296, by rfl⟩ : syracuseStep 2280395 = 3420593) B3420593
theorem B1518551 : Blo 1518456 1518551 := bstep (se 1 (by rfl) ⟨1138913, by rfl⟩ : syracuseStep 1518551 = 2277827) B2277827
theorem B2280407 : Blo 1518456 2280407 := bstep (se 1 (by rfl) ⟨1710305, by rfl⟩ : syracuseStep 2280407 = 3420611) B3420611
theorem B1518571 : Blo 1518456 1518571 := bstep (se 1 (by rfl) ⟨1138928, by rfl⟩ : syracuseStep 1518571 = 2277857) B2277857
theorem B1518583 : Blo 1518456 1518583 := bstep (se 1 (by rfl) ⟨1138937, by rfl⟩ : syracuseStep 1518583 = 2277875) B2277875
theorem B1518603 : Blo 1518456 1518603 := bstep (se 1 (by rfl) ⟨1138952, by rfl⟩ : syracuseStep 1518603 = 2277905) B2277905
theorem B6491153 : Blo 1518456 6491153 := bstep (se 2 (by rfl) ⟨2434182, by rfl⟩ : syracuseStep 6491153 = 4868365) B4868365
theorem B1518615 : Blo 1518456 1518615 := bstep (se 1 (by rfl) ⟨1138961, by rfl⟩ : syracuseStep 1518615 = 2277923) B2277923
theorem B2280473 : Blo 1518456 2280473 := bstep (se 2 (by rfl) ⟨855177, by rfl⟩ : syracuseStep 2280473 = 1710355) B1710355
theorem B1518635 : Blo 1518456 1518635 := bstep (se 1 (by rfl) ⟨1138976, by rfl⟩ : syracuseStep 1518635 = 2277953) B2277953
theorem B3845171 : Blo 1518456 3845171 := bstep (se 1 (by rfl) ⟨2883878, by rfl⟩ : syracuseStep 3845171 = 5767757) B5767757
theorem B1518647 : Blo 1518456 1518647 := bstep (se 1 (by rfl) ⟨1138985, by rfl⟩ : syracuseStep 1518647 = 2277971) B2277971
theorem B1518667 : Blo 1518456 1518667 := bstep (se 1 (by rfl) ⟨1139000, by rfl⟩ : syracuseStep 1518667 = 2278001) B2278001
theorem B1518679 : Blo 1518456 1518679 := bstep (se 1 (by rfl) ⟨1139009, by rfl⟩ : syracuseStep 1518679 = 2278019) B2278019
theorem B3419225 : Blo 1518456 3419225 := bstep (se 2 (by rfl) ⟨1282209, by rfl⟩ : syracuseStep 3419225 = 2564419) B2564419
theorem B1518699 : Blo 1518456 1518699 := bstep (se 1 (by rfl) ⟨1139024, by rfl⟩ : syracuseStep 1518699 = 2278049) B2278049
theorem B1518711 : Blo 1518456 1518711 := bstep (se 1 (by rfl) ⟨1139033, by rfl⟩ : syracuseStep 1518711 = 2278067) B2278067
theorem B27036803 : Blo 1518456 27036803 := bstep (se 1 (by rfl) ⟨20277602, by rfl⟩ : syracuseStep 27036803 = 40555205) B40555205
theorem B8776835 : Blo 1518456 8776835 := bstep (se 1 (by rfl) ⟨6582626, by rfl⟩ : syracuseStep 8776835 = 13165253) B13165253
theorem B1518731 : Blo 1518456 1518731 := bstep (se 1 (by rfl) ⟨1139048, by rfl⟩ : syracuseStep 1518731 = 2278097) B2278097
theorem B2280587 : Blo 1518456 2280587 := bstep (se 1 (by rfl) ⟨1710440, by rfl⟩ : syracuseStep 2280587 = 3420881) B3420881
theorem B5770385 : Blo 1518456 5770385 := bstep (se 2 (by rfl) ⟨2163894, by rfl⟩ : syracuseStep 5770385 = 4327789) B4327789
theorem B1518743 : Blo 1518456 1518743 := bstep (se 1 (by rfl) ⟨1139057, by rfl⟩ : syracuseStep 1518743 = 2278115) B2278115
theorem B2280599 : Blo 1518456 2280599 := bstep (se 1 (by rfl) ⟨1710449, by rfl⟩ : syracuseStep 2280599 = 3420899) B3420899
theorem B1518763 : Blo 1518456 1518763 := bstep (se 1 (by rfl) ⟨1139072, by rfl⟩ : syracuseStep 1518763 = 2278145) B2278145
theorem B3419315 : Blo 1518456 3419315 := bstep (se 1 (by rfl) ⟨2564486, by rfl⟩ : syracuseStep 3419315 = 5128973) B5128973
theorem B2739379 : Blo 1518456 2739379 := bstep (se 1 (by rfl) ⟨2054534, by rfl⟩ : syracuseStep 2739379 = 4109069) B4109069
theorem B1518775 : Blo 1518456 1518775 := bstep (se 1 (by rfl) ⟨1139081, by rfl⟩ : syracuseStep 1518775 = 2278163) B2278163
theorem B5131457 : Blo 1518456 5131457 := bstep (se 2 (by rfl) ⟨1924296, by rfl⟩ : syracuseStep 5131457 = 3848593) B3848593
theorem B1518795 : Blo 1518456 1518795 := bstep (se 1 (by rfl) ⟨1139096, by rfl⟩ : syracuseStep 1518795 = 2278193) B2278193
theorem B1518807 : Blo 1518456 1518807 := bstep (se 1 (by rfl) ⟨1139105, by rfl⟩ : syracuseStep 1518807 = 2278211) B2278211
theorem B3419351 : Blo 1518456 3419351 := bstep (se 1 (by rfl) ⟨2564513, by rfl⟩ : syracuseStep 3419351 = 5129027) B5129027
theorem B7687385 : Blo 1518456 7687385 := bstep (se 2 (by rfl) ⟨2882769, by rfl⟩ : syracuseStep 7687385 = 5765539) B5765539
theorem B2280665 : Blo 1518456 2280665 := bstep (se 2 (by rfl) ⟨855249, by rfl⟩ : syracuseStep 2280665 = 1710499) B1710499
theorem B1518827 : Blo 1518456 1518827 := bstep (se 1 (by rfl) ⟨1139120, by rfl⟩ : syracuseStep 1518827 = 2278241) B2278241
theorem B1518839 : Blo 1518456 1518839 := bstep (se 1 (by rfl) ⟨1139129, by rfl⟩ : syracuseStep 1518839 = 2278259) B2278259
theorem B1518859 : Blo 1518456 1518859 := bstep (se 1 (by rfl) ⟨1139144, by rfl⟩ : syracuseStep 1518859 = 2278289) B2278289
theorem B1518871 : Blo 1518456 1518871 := bstep (se 1 (by rfl) ⟨1139153, by rfl⟩ : syracuseStep 1518871 = 2278307) B2278307
theorem B1518891 : Blo 1518456 1518891 := bstep (se 1 (by rfl) ⟨1139168, by rfl⟩ : syracuseStep 1518891 = 2278337) B2278337
theorem B11545901 : Blo 1518456 11545901 := bstep (se 3 (by rfl) ⟨2164856, by rfl⟩ : syracuseStep 11545901 = 4329713) B4329713
theorem B1518903 : Blo 1518456 1518903 := bstep (se 1 (by rfl) ⟨1139177, by rfl⟩ : syracuseStep 1518903 = 2278355) B2278355
theorem B1518923 : Blo 1518456 1518923 := bstep (se 1 (by rfl) ⟨1139192, by rfl⟩ : syracuseStep 1518923 = 2278385) B2278385
theorem B1518935 : Blo 1518456 1518935 := bstep (se 1 (by rfl) ⟨1139201, by rfl⟩ : syracuseStep 1518935 = 2278403) B2278403
theorem B3845465 : Blo 1518456 3845465 := bstep (se 2 (by rfl) ⟨1442049, by rfl⟩ : syracuseStep 3845465 = 2884099) B2884099
theorem B1518955 : Blo 1518456 1518955 := bstep (se 1 (by rfl) ⟨1139216, by rfl⟩ : syracuseStep 1518955 = 2278433) B2278433
theorem B1518967 : Blo 1518456 1518967 := bstep (se 1 (by rfl) ⟨1139225, by rfl⟩ : syracuseStep 1518967 = 2278451) B2278451
theorem B1518987 : Blo 1518456 1518987 := bstep (se 1 (by rfl) ⟨1139240, by rfl⟩ : syracuseStep 1518987 = 2278481) B2278481
theorem B210439565 : Blo 1518456 210439565 := bstep (se 3 (by rfl) ⟨39457418, by rfl⟩ : syracuseStep 210439565 = 78914837) B78914837
theorem B3419531 : Blo 1518456 3419531 := bstep (se 1 (by rfl) ⟨2564648, by rfl⟩ : syracuseStep 3419531 = 5129297) B5129297
theorem B1518999 : Blo 1518456 1518999 := bstep (se 1 (by rfl) ⟨1139249, by rfl⟩ : syracuseStep 1518999 = 2278499) B2278499
theorem B1519019 : Blo 1518456 1519019 := bstep (se 1 (by rfl) ⟨1139264, by rfl⟩ : syracuseStep 1519019 = 2278529) B2278529
theorem B1519031 : Blo 1518456 1519031 := bstep (se 1 (by rfl) ⟨1139273, by rfl⟩ : syracuseStep 1519031 = 2278547) B2278547
theorem B3419585 : Blo 1518456 3419585 := bstep (se 2 (by rfl) ⟨1282344, by rfl⟩ : syracuseStep 3419585 = 2564689) B2564689
theorem B1519051 : Blo 1518456 1519051 := bstep (se 1 (by rfl) ⟨1139288, by rfl⟩ : syracuseStep 1519051 = 2278577) B2278577
theorem B1519063 : Blo 1518456 1519063 := bstep (se 1 (by rfl) ⟨1139297, by rfl⟩ : syracuseStep 1519063 = 2278595) B2278595
theorem B1519083 : Blo 1518456 1519083 := bstep (se 1 (by rfl) ⟨1139312, by rfl⟩ : syracuseStep 1519083 = 2278625) B2278625
theorem B1519095 : Blo 1518456 1519095 := bstep (se 1 (by rfl) ⟨1139321, by rfl⟩ : syracuseStep 1519095 = 2278643) B2278643
theorem B1519115 : Blo 1518456 1519115 := bstep (se 1 (by rfl) ⟨1139336, by rfl⟩ : syracuseStep 1519115 = 2278673) B2278673
theorem B49262093 : Blo 1518456 49262093 := bstep (se 3 (by rfl) ⟨9236642, by rfl⟩ : syracuseStep 49262093 = 18473285) B18473285
theorem B1519127 : Blo 1518456 1519127 := bstep (se 1 (by rfl) ⟨1139345, by rfl⟩ : syracuseStep 1519127 = 2278691) B2278691
theorem B1519147 : Blo 1518456 1519147 := bstep (se 1 (by rfl) ⟨1139360, by rfl⟩ : syracuseStep 1519147 = 2278721) B2278721
theorem B1519159 : Blo 1518456 1519159 := bstep (se 1 (by rfl) ⟨1139369, by rfl⟩ : syracuseStep 1519159 = 2278739) B2278739
theorem B1519179 : Blo 1518456 1519179 := bstep (se 1 (by rfl) ⟨1139384, by rfl⟩ : syracuseStep 1519179 = 2278769) B2278769
theorem B1519191 : Blo 1518456 1519191 := bstep (se 1 (by rfl) ⟨1139393, by rfl⟩ : syracuseStep 1519191 = 2278787) B2278787
theorem B1519211 : Blo 1518456 1519211 := bstep (se 1 (by rfl) ⟨1139408, by rfl⟩ : syracuseStep 1519211 = 2278817) B2278817
theorem B1519223 : Blo 1518456 1519223 := bstep (se 1 (by rfl) ⟨1139417, by rfl⟩ : syracuseStep 1519223 = 2278835) B2278835
theorem B1519243 : Blo 1518456 1519243 := bstep (se 1 (by rfl) ⟨1139432, by rfl⟩ : syracuseStep 1519243 = 2278865) B2278865
theorem B1519255 : Blo 1518456 1519255 := bstep (se 1 (by rfl) ⟨1139441, by rfl⟩ : syracuseStep 1519255 = 2278883) B2278883
theorem B3419801 : Blo 1518456 3419801 := bstep (se 2 (by rfl) ⟨1282425, by rfl⟩ : syracuseStep 3419801 = 2564851) B2564851
theorem B1519275 : Blo 1518456 1519275 := bstep (se 1 (by rfl) ⟨1139456, by rfl⟩ : syracuseStep 1519275 = 2278913) B2278913
theorem B1519287 : Blo 1518456 1519287 := bstep (se 1 (by rfl) ⟨1139465, by rfl⟩ : syracuseStep 1519287 = 2278931) B2278931
theorem B1519307 : Blo 1518456 1519307 := bstep (se 1 (by rfl) ⟨1139480, by rfl⟩ : syracuseStep 1519307 = 2278961) B2278961
theorem B11538125 : Blo 1518456 11538125 := bstep (se 3 (by rfl) ⟨2163398, by rfl⟩ : syracuseStep 11538125 = 4326797) B4326797
theorem B1519319 : Blo 1518456 1519319 := bstep (se 1 (by rfl) ⟨1139489, by rfl⟩ : syracuseStep 1519319 = 2278979) B2278979
theorem B1519339 : Blo 1518456 1519339 := bstep (se 1 (by rfl) ⟨1139504, by rfl⟩ : syracuseStep 1519339 = 2279009) B2279009
theorem B3419891 : Blo 1518456 3419891 := bstep (se 1 (by rfl) ⟨2564918, by rfl⟩ : syracuseStep 3419891 = 5129837) B5129837
theorem B1519351 : Blo 1518456 1519351 := bstep (se 1 (by rfl) ⟨1139513, by rfl⟩ : syracuseStep 1519351 = 2279027) B2279027
theorem B1519371 : Blo 1518456 1519371 := bstep (se 1 (by rfl) ⟨1139528, by rfl⟩ : syracuseStep 1519371 = 2279057) B2279057
theorem B1519383 : Blo 1518456 1519383 := bstep (se 1 (by rfl) ⟨1139537, by rfl⟩ : syracuseStep 1519383 = 2279075) B2279075
theorem B3419927 : Blo 1518456 3419927 := bstep (se 1 (by rfl) ⟨2564945, by rfl⟩ : syracuseStep 3419927 = 5129891) B5129891
theorem B1519403 : Blo 1518456 1519403 := bstep (se 1 (by rfl) ⟨1139552, by rfl⟩ : syracuseStep 1519403 = 2279105) B2279105
theorem B1519415 : Blo 1518456 1519415 := bstep (se 1 (by rfl) ⟨1139561, by rfl⟩ : syracuseStep 1519415 = 2279123) B2279123
theorem B4329281 : Blo 1518456 4329281 := bstep (se 2 (by rfl) ⟨1623480, by rfl⟩ : syracuseStep 4329281 = 3246961) B3246961
theorem B1519435 : Blo 1518456 1519435 := bstep (se 1 (by rfl) ⟨1139576, by rfl⟩ : syracuseStep 1519435 = 2279153) B2279153
theorem B1519447 : Blo 1518456 1519447 := bstep (se 1 (by rfl) ⟨1139585, by rfl⟩ : syracuseStep 1519447 = 2279171) B2279171
theorem B4386653 : Blo 1518456 4386653 := bstep (se 3 (by rfl) ⟨822497, by rfl⟩ : syracuseStep 4386653 = 1644995) B1644995
theorem B1519467 : Blo 1518456 1519467 := bstep (se 1 (by rfl) ⟨1139600, by rfl⟩ : syracuseStep 1519467 = 2279201) B2279201
theorem B1519479 : Blo 1518456 1519479 := bstep (se 1 (by rfl) ⟨1139609, by rfl⟩ : syracuseStep 1519479 = 2279219) B2279219
theorem B1519499 : Blo 1518456 1519499 := bstep (se 1 (by rfl) ⟨1139624, by rfl⟩ : syracuseStep 1519499 = 2279249) B2279249
theorem B1519511 : Blo 1518456 1519511 := bstep (se 1 (by rfl) ⟨1139633, by rfl⟩ : syracuseStep 1519511 = 2279267) B2279267
theorem B5771159 : Blo 1518456 5771159 := bstep (se 1 (by rfl) ⟨4328369, by rfl⟩ : syracuseStep 5771159 = 8656739) B8656739
theorem B1519531 : Blo 1518456 1519531 := bstep (se 1 (by rfl) ⟨1139648, by rfl⟩ : syracuseStep 1519531 = 2279297) B2279297
theorem B36974515 : Blo 1518456 36974515 := bstep (se 1 (by rfl) ⟨27730886, by rfl⟩ : syracuseStep 36974515 = 55461773) B55461773
theorem B4329395 : Blo 1518456 4329395 := bstep (se 1 (by rfl) ⟨3247046, by rfl⟩ : syracuseStep 4329395 = 6494093) B6494093
theorem B1519543 : Blo 1518456 1519543 := bstep (se 1 (by rfl) ⟨1139657, by rfl⟩ : syracuseStep 1519543 = 2279315) B2279315
theorem B1519563 : Blo 1518456 1519563 := bstep (se 1 (by rfl) ⟨1139672, by rfl⟩ : syracuseStep 1519563 = 2279345) B2279345
theorem B3420107 : Blo 1518456 3420107 := bstep (se 1 (by rfl) ⟨2565080, by rfl⟩ : syracuseStep 3420107 = 5130161) B5130161
theorem B1519575 : Blo 1518456 1519575 := bstep (se 1 (by rfl) ⟨1139681, by rfl⟩ : syracuseStep 1519575 = 2279363) B2279363
theorem B1519595 : Blo 1518456 1519595 := bstep (se 1 (by rfl) ⟨1139696, by rfl⟩ : syracuseStep 1519595 = 2279393) B2279393
theorem B1519607 : Blo 1518456 1519607 := bstep (se 1 (by rfl) ⟨1139705, by rfl⟩ : syracuseStep 1519607 = 2279411) B2279411
theorem B3420161 : Blo 1518456 3420161 := bstep (se 2 (by rfl) ⟨1282560, by rfl⟩ : syracuseStep 3420161 = 2565121) B2565121
theorem B1519627 : Blo 1518456 1519627 := bstep (se 1 (by rfl) ⟨1139720, by rfl⟩ : syracuseStep 1519627 = 2279441) B2279441
theorem B1519639 : Blo 1518456 1519639 := bstep (se 1 (by rfl) ⟨1139729, by rfl⟩ : syracuseStep 1519639 = 2279459) B2279459
theorem B1519659 : Blo 1518456 1519659 := bstep (se 1 (by rfl) ⟨1139744, by rfl⟩ : syracuseStep 1519659 = 2279489) B2279489
theorem B1519671 : Blo 1518456 1519671 := bstep (se 1 (by rfl) ⟨1139753, by rfl⟩ : syracuseStep 1519671 = 2279507) B2279507
theorem B1519691 : Blo 1518456 1519691 := bstep (se 1 (by rfl) ⟨1139768, by rfl⟩ : syracuseStep 1519691 = 2279537) B2279537
theorem B25972811 : Blo 1518456 25972811 := bstep (se 1 (by rfl) ⟨19479608, by rfl⟩ : syracuseStep 25972811 = 38959217) B38959217
theorem B1519703 : Blo 1518456 1519703 := bstep (se 1 (by rfl) ⟨1139777, by rfl⟩ : syracuseStep 1519703 = 2279555) B2279555
theorem B5771357 : Blo 1518456 5771357 := bstep (se 3 (by rfl) ⟨1082129, by rfl⟩ : syracuseStep 5771357 = 2164259) B2164259
theorem B1519723 : Blo 1518456 1519723 := bstep (se 1 (by rfl) ⟨1139792, by rfl⟩ : syracuseStep 1519723 = 2279585) B2279585
theorem B1519735 : Blo 1518456 1519735 := bstep (se 1 (by rfl) ⟨1139801, by rfl⟩ : syracuseStep 1519735 = 2279603) B2279603
theorem B1519755 : Blo 1518456 1519755 := bstep (se 1 (by rfl) ⟨1139816, by rfl⟩ : syracuseStep 1519755 = 2279633) B2279633
theorem B1519767 : Blo 1518456 1519767 := bstep (se 1 (by rfl) ⟨1139825, by rfl⟩ : syracuseStep 1519767 = 2279651) B2279651
theorem B1519787 : Blo 1518456 1519787 := bstep (se 1 (by rfl) ⟨1139840, by rfl⟩ : syracuseStep 1519787 = 2279681) B2279681
theorem B11538611 : Blo 1518456 11538611 := bstep (se 1 (by rfl) ⟨8653958, by rfl⟩ : syracuseStep 11538611 = 17307917) B17307917
theorem B1519799 : Blo 1518456 1519799 := bstep (se 1 (by rfl) ⟨1139849, by rfl⟩ : syracuseStep 1519799 = 2279699) B2279699
theorem B4165825 : Blo 1518456 4165825 := bstep (se 2 (by rfl) ⟨1562184, by rfl⟩ : syracuseStep 4165825 = 3124369) B3124369
theorem B1519819 : Blo 1518456 1519819 := bstep (se 1 (by rfl) ⟨1139864, by rfl⟩ : syracuseStep 1519819 = 2279729) B2279729
theorem B1519831 : Blo 1518456 1519831 := bstep (se 1 (by rfl) ⟨1139873, by rfl⟩ : syracuseStep 1519831 = 2279747) B2279747
theorem B3420377 : Blo 1518456 3420377 := bstep (se 2 (by rfl) ⟨1282641, by rfl⟩ : syracuseStep 3420377 = 2565283) B2565283
theorem B1708267 : Blo 1518456 1708267 := bstep (se 1 (by rfl) ⟨1281200, by rfl⟩ : syracuseStep 1708267 = 2562401) B2562401
theorem B1519851 : Blo 1518456 1519851 := bstep (se 1 (by rfl) ⟨1139888, by rfl⟩ : syracuseStep 1519851 = 2279777) B2279777
theorem B1519863 : Blo 1518456 1519863 := bstep (se 1 (by rfl) ⟨1139897, by rfl⟩ : syracuseStep 1519863 = 2279795) B2279795
theorem B6492419 : Blo 1518456 6492419 := bstep (se 1 (by rfl) ⟨4869314, by rfl⟩ : syracuseStep 6492419 = 9738629) B9738629
theorem B1519883 : Blo 1518456 1519883 := bstep (se 1 (by rfl) ⟨1139912, by rfl⟩ : syracuseStep 1519883 = 2279825) B2279825
theorem B1519895 : Blo 1518456 1519895 := bstep (se 1 (by rfl) ⟨1139921, by rfl⟩ : syracuseStep 1519895 = 2279843) B2279843
theorem B1519915 : Blo 1518456 1519915 := bstep (se 1 (by rfl) ⟨1139936, by rfl⟩ : syracuseStep 1519915 = 2279873) B2279873
theorem B3420467 : Blo 1518456 3420467 := bstep (se 1 (by rfl) ⟨2565350, by rfl⟩ : syracuseStep 3420467 = 5130701) B5130701
theorem B1519927 : Blo 1518456 1519927 := bstep (se 1 (by rfl) ⟨1139945, by rfl⟩ : syracuseStep 1519927 = 2279891) B2279891
theorem B1519947 : Blo 1518456 1519947 := bstep (se 1 (by rfl) ⟨1139960, by rfl⟩ : syracuseStep 1519947 = 2279921) B2279921
theorem B1708375 : Blo 1518456 1708375 := bstep (se 1 (by rfl) ⟨1281281, by rfl⟩ : syracuseStep 1708375 = 2562563) B2562563
theorem B1519959 : Blo 1518456 1519959 := bstep (se 1 (by rfl) ⟨1139969, by rfl⟩ : syracuseStep 1519959 = 2279939) B2279939
theorem B3420503 : Blo 1518456 3420503 := bstep (se 1 (by rfl) ⟨2565377, by rfl⟩ : syracuseStep 3420503 = 5130755) B5130755
theorem B1519979 : Blo 1518456 1519979 := bstep (se 1 (by rfl) ⟨1139984, by rfl⟩ : syracuseStep 1519979 = 2279969) B2279969
theorem B1519991 : Blo 1518456 1519991 := bstep (se 1 (by rfl) ⟨1139993, by rfl⟩ : syracuseStep 1519991 = 2279987) B2279987
theorem B1520011 : Blo 1518456 1520011 := bstep (se 1 (by rfl) ⟨1140008, by rfl⟩ : syracuseStep 1520011 = 2280017) B2280017
theorem B1520023 : Blo 1518456 1520023 := bstep (se 1 (by rfl) ⟨1140017, by rfl⟩ : syracuseStep 1520023 = 2280035) B2280035
theorem B1520043 : Blo 1518456 1520043 := bstep (se 1 (by rfl) ⟨1140032, by rfl⟩ : syracuseStep 1520043 = 2280065) B2280065
theorem B1520055 : Blo 1518456 1520055 := bstep (se 1 (by rfl) ⟨1140041, by rfl⟩ : syracuseStep 1520055 = 2280083) B2280083
theorem B1520075 : Blo 1518456 1520075 := bstep (se 1 (by rfl) ⟨1140056, by rfl⟩ : syracuseStep 1520075 = 2280113) B2280113
theorem B1520087 : Blo 1518456 1520087 := bstep (se 1 (by rfl) ⟨1140065, by rfl⟩ : syracuseStep 1520087 = 2280131) B2280131
theorem B1520107 : Blo 1518456 1520107 := bstep (se 1 (by rfl) ⟨1140080, by rfl⟩ : syracuseStep 1520107 = 2280161) B2280161
theorem B1520119 : Blo 1518456 1520119 := bstep (se 1 (by rfl) ⟨1140089, by rfl⟩ : syracuseStep 1520119 = 2280179) B2280179
theorem B1708555 : Blo 1518456 1708555 := bstep (se 1 (by rfl) ⟨1281416, by rfl⟩ : syracuseStep 1708555 = 2562833) B2562833
theorem B1520139 : Blo 1518456 1520139 := bstep (se 1 (by rfl) ⟨1140104, by rfl⟩ : syracuseStep 1520139 = 2280209) B2280209
theorem B3420683 : Blo 1518456 3420683 := bstep (se 1 (by rfl) ⟨2565512, by rfl⟩ : syracuseStep 3420683 = 5131025) B5131025
theorem B1520151 : Blo 1518456 1520151 := bstep (se 1 (by rfl) ⟨1140113, by rfl⟩ : syracuseStep 1520151 = 2280227) B2280227
theorem B1520171 : Blo 1518456 1520171 := bstep (se 1 (by rfl) ⟨1140128, by rfl⟩ : syracuseStep 1520171 = 2280257) B2280257
theorem B1520183 : Blo 1518456 1520183 := bstep (se 1 (by rfl) ⟨1140137, by rfl⟩ : syracuseStep 1520183 = 2280275) B2280275
theorem B3420737 : Blo 1518456 3420737 := bstep (se 2 (by rfl) ⟨1282776, by rfl⟩ : syracuseStep 3420737 = 2565553) B2565553
theorem B1520203 : Blo 1518456 1520203 := bstep (se 1 (by rfl) ⟨1140152, by rfl⟩ : syracuseStep 1520203 = 2280305) B2280305
theorem B1520215 : Blo 1518456 1520215 := bstep (se 1 (by rfl) ⟨1140161, by rfl⟩ : syracuseStep 1520215 = 2280323) B2280323
theorem B2052697 : Blo 1518456 2052697 := bstep (se 2 (by rfl) ⟨769761, by rfl⟩ : syracuseStep 2052697 = 1539523) B1539523
theorem B1520235 : Blo 1518456 1520235 := bstep (se 1 (by rfl) ⟨1140176, by rfl⟩ : syracuseStep 1520235 = 2280353) B2280353
theorem B1708663 : Blo 1518456 1708663 := bstep (se 1 (by rfl) ⟨1281497, by rfl⟩ : syracuseStep 1708663 = 2562995) B2562995
theorem B1520247 : Blo 1518456 1520247 := bstep (se 1 (by rfl) ⟨1140185, by rfl⟩ : syracuseStep 1520247 = 2280371) B2280371
theorem B1520267 : Blo 1518456 1520267 := bstep (se 1 (by rfl) ⟨1140200, by rfl⟩ : syracuseStep 1520267 = 2280401) B2280401
theorem B1520279 : Blo 1518456 1520279 := bstep (se 1 (by rfl) ⟨1140209, by rfl⟩ : syracuseStep 1520279 = 2280419) B2280419
theorem B1520299 : Blo 1518456 1520299 := bstep (se 1 (by rfl) ⟨1140224, by rfl⟩ : syracuseStep 1520299 = 2280449) B2280449
theorem B1520311 : Blo 1518456 1520311 := bstep (se 1 (by rfl) ⟨1140233, by rfl⟩ : syracuseStep 1520311 = 2280467) B2280467
theorem B1520331 : Blo 1518456 1520331 := bstep (se 1 (by rfl) ⟨1140248, by rfl⟩ : syracuseStep 1520331 = 2280497) B2280497
theorem B1520343 : Blo 1518456 1520343 := bstep (se 1 (by rfl) ⟨1140257, by rfl⟩ : syracuseStep 1520343 = 2280515) B2280515
theorem B1520363 : Blo 1518456 1520363 := bstep (se 1 (by rfl) ⟨1140272, by rfl⟩ : syracuseStep 1520363 = 2280545) B2280545
theorem B1520375 : Blo 1518456 1520375 := bstep (se 1 (by rfl) ⟨1140281, by rfl⟩ : syracuseStep 1520375 = 2280563) B2280563
theorem B1520395 : Blo 1518456 1520395 := bstep (se 1 (by rfl) ⟨1140296, by rfl⟩ : syracuseStep 1520395 = 2280593) B2280593
theorem B4682519 : Blo 1518456 4682519 := bstep (se 1 (by rfl) ⟨3511889, by rfl⟩ : syracuseStep 4682519 = 7023779) B7023779
theorem B1520407 : Blo 1518456 1520407 := bstep (se 1 (by rfl) ⟨1140305, by rfl⟩ : syracuseStep 1520407 = 2280611) B2280611
theorem B3420953 : Blo 1518456 3420953 := bstep (se 2 (by rfl) ⟨1282857, by rfl⟩ : syracuseStep 3420953 = 2565715) B2565715
theorem B1708843 : Blo 1518456 1708843 := bstep (se 1 (by rfl) ⟨1281632, by rfl⟩ : syracuseStep 1708843 = 2563265) B2563265
theorem B7689005 : Blo 1518456 7689005 := bstep (se 3 (by rfl) ⟨1441688, by rfl⟩ : syracuseStep 7689005 = 2883377) B2883377
theorem B1520427 : Blo 1518456 1520427 := bstep (se 1 (by rfl) ⟨1140320, by rfl⟩ : syracuseStep 1520427 = 2280641) B2280641
theorem B1520439 : Blo 1518456 1520439 := bstep (se 1 (by rfl) ⟨1140329, by rfl⟩ : syracuseStep 1520439 = 2280659) B2280659
theorem B5550923 : Blo 1518456 5550923 := bstep (se 1 (by rfl) ⟨4163192, by rfl⟩ : syracuseStep 5550923 = 8326385) B8326385
theorem B1708951 : Blo 1518456 1708951 := bstep (se 1 (by rfl) ⟨1281713, by rfl⟩ : syracuseStep 1708951 = 2563427) B2563427
theorem B3847115 : Blo 1518456 3847115 := bstep (se 1 (by rfl) ⟨2885336, by rfl⟩ : syracuseStep 3847115 = 5770673) B5770673
theorem B5125085 : Blo 1518456 5125085 := bstep (se 3 (by rfl) ⟨960953, by rfl⟩ : syracuseStep 5125085 = 1921907) B1921907
theorem B3511297 : Blo 1518456 3511297 := bstep (se 2 (by rfl) ⟨1316736, by rfl⟩ : syracuseStep 3511297 = 2633473) B2633473
theorem B1922059 : Blo 1518456 1922059 := bstep (se 1 (by rfl) ⟨1441544, by rfl⟩ : syracuseStep 1922059 = 2883089) B2883089
theorem B2053145 : Blo 1518456 2053145 := bstep (se 2 (by rfl) ⟨769929, by rfl⟩ : syracuseStep 2053145 = 1539859) B1539859
theorem B2774081 : Blo 1518456 2774081 := bstep (se 2 (by rfl) ⟨1040280, by rfl⟩ : syracuseStep 2774081 = 2080561) B2080561
theorem B1709131 : Blo 1518456 1709131 := bstep (se 1 (by rfl) ⟨1281848, by rfl⟩ : syracuseStep 1709131 = 2563697) B2563697
theorem B13866059 : Blo 1518456 13866059 := bstep (se 1 (by rfl) ⟨10399544, by rfl⟩ : syracuseStep 13866059 = 20799089) B20799089
theorem B9245771 : Blo 1518456 9245771 := bstep (se 1 (by rfl) ⟨6934328, by rfl⟩ : syracuseStep 9245771 = 13868657) B13868657
theorem B23385181 : Blo 1518456 23385181 := bstep (se 3 (by rfl) ⟨4384721, by rfl⟩ : syracuseStep 23385181 = 8769443) B8769443
theorem B1709239 : Blo 1518456 1709239 := bstep (se 1 (by rfl) ⟨1281929, by rfl⟩ : syracuseStep 1709239 = 2563859) B2563859
theorem B1709419 : Blo 1518456 1709419 := bstep (se 1 (by rfl) ⟨1282064, by rfl⟩ : syracuseStep 1709419 = 2564129) B2564129
theorem B9737603 : Blo 1518456 9737603 := bstep (se 1 (by rfl) ⟨7303202, by rfl⟩ : syracuseStep 9737603 = 14606405) B14606405
theorem B8656307 : Blo 1518456 8656307 := bstep (se 1 (by rfl) ⟨6492230, by rfl⟩ : syracuseStep 8656307 = 12984461) B12984461
theorem B1709527 : Blo 1518456 1709527 := bstep (se 1 (by rfl) ⟨1282145, by rfl⟩ : syracuseStep 1709527 = 2564291) B2564291
theorem B9729553 : Blo 1518456 9729553 := bstep (se 2 (by rfl) ⟨3648582, by rfl⟩ : syracuseStep 9729553 = 7297165) B7297165
theorem B21894725 : Blo 1518456 21894725 := bstep (se 4 (by rfl) ⟨2052630, by rfl⟩ : syracuseStep 21894725 = 4105261) B4105261
theorem B11540069 : Blo 1518456 11540069 := bstep (se 4 (by rfl) ⟨1081881, by rfl⟩ : syracuseStep 11540069 = 2163763) B2163763
theorem B1709707 : Blo 1518456 1709707 := bstep (se 1 (by rfl) ⟨1282280, by rfl⟩ : syracuseStep 1709707 = 2564561) B2564561
theorem B3651265 : Blo 1518456 3651265 := bstep (se 2 (by rfl) ⟨1369224, by rfl⟩ : syracuseStep 3651265 = 2738449) B2738449
theorem B1709815 : Blo 1518456 1709815 := bstep (se 1 (by rfl) ⟨1282361, by rfl⟩ : syracuseStep 1709815 = 2564723) B2564723
theorem B1824599 : Blo 1518456 1824599 := bstep (se 1 (by rfl) ⟨1368449, by rfl⟩ : syracuseStep 1824599 = 2736899) B2736899
theorem B5478295 : Blo 1518456 5478295 := bstep (se 1 (by rfl) ⟨4108721, by rfl⟩ : syracuseStep 5478295 = 8217443) B8217443
theorem B3848087 : Blo 1518456 3848087 := bstep (se 1 (by rfl) ⟨2886065, by rfl⟩ : syracuseStep 3848087 = 5772131) B5772131
theorem B1709995 : Blo 1518456 1709995 := bstep (se 1 (by rfl) ⟨1282496, by rfl⟩ : syracuseStep 1709995 = 2564993) B2564993
theorem B1923031 : Blo 1518456 1923031 := bstep (se 1 (by rfl) ⟨1442273, by rfl⟩ : syracuseStep 1923031 = 2884547) B2884547
theorem B11532293 : Blo 1518456 11532293 := bstep (se 4 (by rfl) ⟨1081152, by rfl⟩ : syracuseStep 11532293 = 2162305) B2162305
theorem B1710103 : Blo 1518456 1710103 := bstep (se 1 (by rfl) ⟨1282577, by rfl⟩ : syracuseStep 1710103 = 2565155) B2565155
theorem B5126219 : Blo 1518456 5126219 := bstep (se 1 (by rfl) ⟨3844664, by rfl⟩ : syracuseStep 5126219 = 7689329) B7689329
theorem B48068683 : Blo 1518456 48068683 := bstep (se 1 (by rfl) ⟨36051512, by rfl⟩ : syracuseStep 48068683 = 72103025) B72103025
theorem B11540555 : Blo 1518456 11540555 := bstep (se 1 (by rfl) ⟨8655416, by rfl⟩ : syracuseStep 11540555 = 17310833) B17310833
theorem B3651659 : Blo 1518456 3651659 := bstep (se 1 (by rfl) ⟨2738744, by rfl⟩ : syracuseStep 3651659 = 5477489) B5477489
theorem B23402677 : Blo 1518456 23402677 := bstep (se 5 (by rfl) ⟨1097000, by rfl⟩ : syracuseStep 23402677 = 2194001) B2194001
theorem B1710283 : Blo 1518456 1710283 := bstep (se 1 (by rfl) ⟨1282712, by rfl⟩ : syracuseStep 1710283 = 2565425) B2565425
theorem B19478789 : Blo 1518456 19478789 := bstep (se 4 (by rfl) ⟨1826136, by rfl⟩ : syracuseStep 19478789 = 3652273) B3652273
theorem B15808813 : Blo 1518456 15808813 := bstep (se 3 (by rfl) ⟨2964152, by rfl⟩ : syracuseStep 15808813 = 5928305) B5928305
theorem B1710391 : Blo 1518456 1710391 := bstep (se 1 (by rfl) ⟨1282793, by rfl⟩ : syracuseStep 1710391 = 2565587) B2565587
theorem B5126489 : Blo 1518456 5126489 := bstep (se 2 (by rfl) ⟨1922433, by rfl⟩ : syracuseStep 5126489 = 3844867) B3844867
theorem B3651929 : Blo 1518456 3651929 := bstep (se 2 (by rfl) ⟨1369473, by rfl⟩ : syracuseStep 3651929 = 2738947) B2738947
theorem B2562455 : Blo 1518456 2562455 := bstep (se 1 (by rfl) ⟨1921841, by rfl⟩ : syracuseStep 2562455 = 3843683) B3843683
theorem B7305623 : Blo 1518456 7305623 := bstep (se 1 (by rfl) ⟨5479217, by rfl⟩ : syracuseStep 7305623 = 10958435) B10958435
theorem B4004275 : Blo 1518456 4004275 := bstep (se 1 (by rfl) ⟨3003206, by rfl⟩ : syracuseStep 4004275 = 6006413) B6006413
theorem B2562583 : Blo 1518456 2562583 := bstep (se 1 (by rfl) ⟨1921937, by rfl⟩ : syracuseStep 2562583 = 3843875) B3843875
theorem B4684439 : Blo 1518456 4684439 := bstep (se 1 (by rfl) ⟨3513329, by rfl⟩ : syracuseStep 4684439 = 7026659) B7026659
theorem B1923851 : Blo 1518456 1923851 := bstep (se 1 (by rfl) ⟨1442888, by rfl⟩ : syracuseStep 1923851 = 2885777) B2885777
theorem B3332953 : Blo 1518456 3332953 := bstep (se 2 (by rfl) ⟨1249857, by rfl⟩ : syracuseStep 3332953 = 2499715) B2499715
theorem B8657765 : Blo 1518456 8657765 := bstep (se 4 (by rfl) ⟨811665, by rfl⟩ : syracuseStep 8657765 = 1623331) B1623331
theorem B2776051 : Blo 1518456 2776051 := bstep (se 1 (by rfl) ⟨2082038, by rfl⟩ : syracuseStep 2776051 = 4164077) B4164077
theorem B5127191 : Blo 1518456 5127191 := bstep (se 1 (by rfl) ⟨3845393, by rfl⟩ : syracuseStep 5127191 = 7690787) B7690787
theorem B3652697 : Blo 1518456 3652697 := bstep (se 2 (by rfl) ⟨1369761, by rfl⟩ : syracuseStep 3652697 = 2739523) B2739523
theorem B2563211 : Blo 1518456 2563211 := bstep (se 1 (by rfl) ⟨1922408, by rfl⟩ : syracuseStep 2563211 = 3844817) B3844817
theorem B70139141 : Blo 1518456 70139141 := bstep (se 4 (by rfl) ⟨6575544, by rfl⟩ : syracuseStep 70139141 = 13151089) B13151089
theorem B2563339 : Blo 1518456 2563339 := bstep (se 1 (by rfl) ⟨1922504, by rfl⟩ : syracuseStep 2563339 = 3845009) B3845009
theorem B3243287 : Blo 1518456 3243287 := bstep (se 1 (by rfl) ⟨2432465, by rfl⟩ : syracuseStep 3243287 = 4864931) B4864931
theorem B2309399 : Blo 1518456 2309399 := bstep (se 1 (by rfl) ⟨1732049, by rfl⟩ : syracuseStep 2309399 = 3464099) B3464099
theorem B6487361 : Blo 1518456 6487361 := bstep (se 2 (by rfl) ⟨2432760, by rfl⟩ : syracuseStep 6487361 = 4865521) B4865521
theorem B2882891 : Blo 1518456 2882891 := bstep (se 1 (by rfl) ⟨2162168, by rfl⟩ : syracuseStep 2882891 = 4324337) B4324337
theorem B2882945 : Blo 1518456 2882945 := bstep (se 2 (by rfl) ⟨1081104, by rfl⟩ : syracuseStep 2882945 = 2162209) B2162209
theorem B5479825 : Blo 1518456 5479825 := bstep (se 2 (by rfl) ⟨2054934, by rfl⟩ : syracuseStep 5479825 = 4109869) B4109869
theorem B2563481 : Blo 1518456 2563481 := bstep (se 2 (by rfl) ⟨961305, by rfl⟩ : syracuseStep 2563481 = 1922611) B1922611
theorem B4865483 : Blo 1518456 4865483 := bstep (se 1 (by rfl) ⟨3649112, by rfl⟩ : syracuseStep 4865483 = 7298225) B7298225
theorem B98557397 : Blo 1518456 98557397 := bstep (se 7 (by rfl) ⟨1154969, by rfl⟩ : syracuseStep 98557397 = 2309939) B2309939
theorem B2563609 : Blo 1518456 2563609 := bstep (se 2 (by rfl) ⟨961353, by rfl⟩ : syracuseStep 2563609 = 1922707) B1922707
theorem B6929965 : Blo 1518456 6929965 := bstep (se 3 (by rfl) ⟨1299368, by rfl⟩ : syracuseStep 6929965 = 2598737) B2598737
theorem B5127731 : Blo 1518456 5127731 := bstep (se 1 (by rfl) ⟨3845798, by rfl⟩ : syracuseStep 5127731 = 7691597) B7691597
theorem B20790989 : Blo 1518456 20790989 := bstep (se 3 (by rfl) ⟨3898310, by rfl⟩ : syracuseStep 20790989 = 7796621) B7796621
theorem B5128001 : Blo 1518456 5128001 := bstep (se 2 (by rfl) ⟨1923000, by rfl⟩ : syracuseStep 5128001 = 3846001) B3846001
theorem B13868977 : Blo 1518456 13868977 := bstep (se 2 (by rfl) ⟨5200866, by rfl⟩ : syracuseStep 13868977 = 10401733) B10401733
theorem B2162647 : Blo 1518456 2162647 := bstep (se 1 (by rfl) ⟨1621985, by rfl⟩ : syracuseStep 2162647 = 3243971) B3243971
theorem B3702827 : Blo 1518456 3702827 := bstep (se 1 (by rfl) ⟨2777120, by rfl⟩ : syracuseStep 3702827 = 5554241) B5554241
theorem B7692407 : Blo 1518456 7692407 := bstep (se 1 (by rfl) ⟨5769305, by rfl⟩ : syracuseStep 7692407 = 11538611) B11538611
theorem B2162875 : Blo 1518456 2162875 := bstep (se 1 (by rfl) ⟨1622156, by rfl⟩ : syracuseStep 2162875 = 3244313) B3244313
theorem B31203569 : Blo 1518456 31203569 := bstep (se 2 (by rfl) ⟨11701338, by rfl⟩ : syracuseStep 31203569 = 23402677) B23402677
theorem B2310391 : Blo 1518456 2310391 := bstep (se 1 (by rfl) ⟨1732793, by rfl⟩ : syracuseStep 2310391 = 3465587) B3465587
theorem B5554433 : Blo 1518456 5554433 := bstep (se 2 (by rfl) ⟨2082912, by rfl⟩ : syracuseStep 5554433 = 4165825) B4165825
theorem B2277689 : Blo 1518456 2277689 := bstep (se 2 (by rfl) ⟨854133, by rfl⟩ : syracuseStep 2277689 = 1708267) B1708267
theorem B5767483 : Blo 1518456 5767483 := bstep (se 1 (by rfl) ⟨4325612, by rfl⟩ : syracuseStep 5767483 = 8651225) B8651225
theorem B2277767 : Blo 1518456 2277767 := bstep (se 1 (by rfl) ⟨1708325, by rfl⟩ : syracuseStep 2277767 = 3416651) B3416651
theorem B5128595 : Blo 1518456 5128595 := bstep (se 1 (by rfl) ⟨3846446, by rfl⟩ : syracuseStep 5128595 = 7692893) B7692893
theorem B2277803 : Blo 1518456 2277803 := bstep (se 1 (by rfl) ⟨1708352, by rfl⟩ : syracuseStep 2277803 = 3416705) B3416705
theorem B2277833 : Blo 1518456 2277833 := bstep (se 2 (by rfl) ⟨854187, by rfl⟩ : syracuseStep 2277833 = 1708375) B1708375
theorem B7799249 : Blo 1518456 7799249 := bstep (se 2 (by rfl) ⟨2924718, by rfl⟩ : syracuseStep 7799249 = 5849437) B5849437
theorem B4866571 : Blo 1518456 4866571 := bstep (se 1 (by rfl) ⟨3649928, by rfl⟩ : syracuseStep 4866571 = 7299857) B7299857
theorem B3121679 : Blo 1518456 3121679 := bstep (se 1 (by rfl) ⟨2341259, by rfl⟩ : syracuseStep 3121679 = 4682519) B4682519
theorem B2277947 : Blo 1518456 2277947 := bstep (se 1 (by rfl) ⟨1708460, by rfl⟩ : syracuseStep 2277947 = 3416921) B3416921
theorem B2278007 : Blo 1518456 2278007 := bstep (se 1 (by rfl) ⟨1708505, by rfl⟩ : syracuseStep 2278007 = 3417011) B3417011
theorem B4326023 : Blo 1518456 4326023 := bstep (se 1 (by rfl) ⟨3244517, by rfl⟩ : syracuseStep 4326023 = 6489035) B6489035
theorem B2564743 : Blo 1518456 2564743 := bstep (se 1 (by rfl) ⟨1923557, by rfl⟩ : syracuseStep 2564743 = 3847115) B3847115
theorem B2278031 : Blo 1518456 2278031 := bstep (se 1 (by rfl) ⟨1708523, by rfl⟩ : syracuseStep 2278031 = 3417047) B3417047
theorem B3416723 : Blo 1518456 3416723 := bstep (se 1 (by rfl) ⟨2562542, by rfl⟩ : syracuseStep 3416723 = 5125085) B5125085
theorem B2884243 : Blo 1518456 2884243 := bstep (se 1 (by rfl) ⟨2163182, by rfl⟩ : syracuseStep 2884243 = 4326365) B4326365
theorem B2278073 : Blo 1518456 2278073 := bstep (se 2 (by rfl) ⟨854277, by rfl⟩ : syracuseStep 2278073 = 1708555) B1708555
theorem B3416777 : Blo 1518456 3416777 := bstep (se 2 (by rfl) ⟨1281291, by rfl⟩ : syracuseStep 3416777 = 2562583) B2562583
theorem B2278151 : Blo 1518456 2278151 := bstep (se 1 (by rfl) ⟨1708613, by rfl⟩ : syracuseStep 2278151 = 3417227) B3417227
theorem B2736929 : Blo 1518456 2736929 := bstep (se 2 (by rfl) ⟨1026348, by rfl⟩ : syracuseStep 2736929 = 2052697) B2052697
theorem B5767969 : Blo 1518456 5767969 := bstep (se 2 (by rfl) ⟨2162988, by rfl⟩ : syracuseStep 5767969 = 4325977) B4325977
theorem B2278187 : Blo 1518456 2278187 := bstep (se 1 (by rfl) ⟨1708640, by rfl⟩ : syracuseStep 2278187 = 3417281) B3417281
theorem B4326205 : Blo 1518456 4326205 := bstep (se 3 (by rfl) ⟨811163, by rfl⟩ : syracuseStep 4326205 = 1622327) B1622327
theorem B2278217 : Blo 1518456 2278217 := bstep (se 2 (by rfl) ⟨854331, by rfl⟩ : syracuseStep 2278217 = 1708663) B1708663
theorem B2278331 : Blo 1518456 2278331 := bstep (se 1 (by rfl) ⟨1708748, by rfl⟩ : syracuseStep 2278331 = 3417497) B3417497
theorem B2278391 : Blo 1518456 2278391 := bstep (se 1 (by rfl) ⟨1708793, by rfl⟩ : syracuseStep 2278391 = 3417587) B3417587
theorem B2278415 : Blo 1518456 2278415 := bstep (se 1 (by rfl) ⟨1708811, by rfl⟩ : syracuseStep 2278415 = 3417623) B3417623
theorem B2278457 : Blo 1518456 2278457 := bstep (se 2 (by rfl) ⟨854421, by rfl⟩ : syracuseStep 2278457 = 1708843) B1708843
theorem B7693379 : Blo 1518456 7693379 := bstep (se 1 (by rfl) ⟨5770034, by rfl⟩ : syracuseStep 7693379 = 11540069) B11540069
theorem B2278535 : Blo 1518456 2278535 := bstep (se 1 (by rfl) ⟨1708901, by rfl⟩ : syracuseStep 2278535 = 3417803) B3417803
theorem B4326547 : Blo 1518456 4326547 := bstep (se 1 (by rfl) ⟨3244910, by rfl⟩ : syracuseStep 4326547 = 6489821) B6489821
theorem B2278571 : Blo 1518456 2278571 := bstep (se 1 (by rfl) ⟨1708928, by rfl⟩ : syracuseStep 2278571 = 3417857) B3417857
theorem B2278601 : Blo 1518456 2278601 := bstep (se 2 (by rfl) ⟨854475, by rfl⟩ : syracuseStep 2278601 = 1708951) B1708951
theorem B2565391 : Blo 1518456 2565391 := bstep (se 1 (by rfl) ⟨1924043, by rfl⟩ : syracuseStep 2565391 = 3848087) B3848087
theorem B2278715 : Blo 1518456 2278715 := bstep (se 1 (by rfl) ⟨1709036, by rfl⟩ : syracuseStep 2278715 = 3418073) B3418073
theorem B2278775 : Blo 1518456 2278775 := bstep (se 1 (by rfl) ⟨1709081, by rfl⟩ : syracuseStep 2278775 = 3418163) B3418163
theorem B3417479 : Blo 1518456 3417479 := bstep (se 1 (by rfl) ⟨2563109, by rfl⟩ : syracuseStep 3417479 = 5126219) B5126219
theorem B7693703 : Blo 1518456 7693703 := bstep (se 1 (by rfl) ⟨5770277, by rfl⟩ : syracuseStep 7693703 = 11540555) B11540555
theorem B2434439 : Blo 1518456 2434439 := bstep (se 1 (by rfl) ⟨1825829, by rfl⟩ : syracuseStep 2434439 = 3651659) B3651659
theorem B2278799 : Blo 1518456 2278799 := bstep (se 1 (by rfl) ⟨1709099, by rfl⟩ : syracuseStep 2278799 = 3418199) B3418199
theorem B8209811 : Blo 1518456 8209811 := bstep (se 1 (by rfl) ⟨6157358, by rfl⟩ : syracuseStep 8209811 = 12314717) B12314717
theorem B6489497 : Blo 1518456 6489497 := bstep (se 2 (by rfl) ⟨2433561, by rfl⟩ : syracuseStep 6489497 = 4867123) B4867123
theorem B2278841 : Blo 1518456 2278841 := bstep (se 2 (by rfl) ⟨854565, by rfl⟩ : syracuseStep 2278841 = 1709131) B1709131
theorem B31180241 : Blo 1518456 31180241 := bstep (se 2 (by rfl) ⟨11692590, by rfl⟩ : syracuseStep 31180241 = 23385181) B23385181
theorem B12985859 : Blo 1518456 12985859 := bstep (se 1 (by rfl) ⟨9739394, by rfl⟩ : syracuseStep 12985859 = 19478789) B19478789
theorem B2278919 : Blo 1518456 2278919 := bstep (se 1 (by rfl) ⟨1709189, by rfl⟩ : syracuseStep 2278919 = 3418379) B3418379
theorem B2278955 : Blo 1518456 2278955 := bstep (se 1 (by rfl) ⟨1709216, by rfl⟩ : syracuseStep 2278955 = 3418433) B3418433
theorem B3245611 : Blo 1518456 3245611 := bstep (se 1 (by rfl) ⟨2434208, by rfl⟩ : syracuseStep 3245611 = 4868417) B4868417
theorem B3417659 : Blo 1518456 3417659 := bstep (se 1 (by rfl) ⟨2563244, by rfl⟩ : syracuseStep 3417659 = 5126489) B5126489
theorem B2434619 : Blo 1518456 2434619 := bstep (se 1 (by rfl) ⟨1825964, by rfl⟩ : syracuseStep 2434619 = 3651929) B3651929
theorem B8767043 : Blo 1518456 8767043 := bstep (se 1 (by rfl) ⟨6575282, by rfl⟩ : syracuseStep 8767043 = 13150565) B13150565
theorem B84313669 : Blo 1518456 84313669 := bstep (se 4 (by rfl) ⟨7904406, by rfl⟩ : syracuseStep 84313669 = 15808813) B15808813
theorem B2278985 : Blo 1518456 2278985 := bstep (se 2 (by rfl) ⟨854619, by rfl⟩ : syracuseStep 2278985 = 1709239) B1709239
theorem B6489719 : Blo 1518456 6489719 := bstep (se 1 (by rfl) ⟨4867289, by rfl⟩ : syracuseStep 6489719 = 9734579) B9734579
theorem B2164367 : Blo 1518456 2164367 := bstep (se 1 (by rfl) ⟨1623275, by rfl⟩ : syracuseStep 2164367 = 3246551) B3246551
theorem B3417785 : Blo 1518456 3417785 := bstep (se 2 (by rfl) ⟨1281669, by rfl⟩ : syracuseStep 3417785 = 2563339) B2563339
theorem B2279099 : Blo 1518456 2279099 := bstep (se 1 (by rfl) ⟨1709324, by rfl⟩ : syracuseStep 2279099 = 3418649) B3418649
theorem B2885321 : Blo 1518456 2885321 := bstep (se 2 (by rfl) ⟨1081995, by rfl⟩ : syracuseStep 2885321 = 2163991) B2163991
theorem B5768941 : Blo 1518456 5768941 := bstep (se 3 (by rfl) ⟨1081676, by rfl⟩ : syracuseStep 5768941 = 2163353) B2163353
theorem B2279159 : Blo 1518456 2279159 := bstep (se 1 (by rfl) ⟨1709369, by rfl⟩ : syracuseStep 2279159 = 3418739) B3418739
theorem B2279183 : Blo 1518456 2279183 := bstep (se 1 (by rfl) ⟨1709387, by rfl⟩ : syracuseStep 2279183 = 3418775) B3418775
theorem B5129999 : Blo 1518456 5129999 := bstep (se 1 (by rfl) ⟨3847499, by rfl⟩ : syracuseStep 5129999 = 7694999) B7694999
theorem B2279225 : Blo 1518456 2279225 := bstep (se 2 (by rfl) ⟨854709, by rfl⟩ : syracuseStep 2279225 = 1709419) B1709419
theorem B4867955 : Blo 1518456 4867955 := bstep (se 1 (by rfl) ⟨3650966, by rfl⟩ : syracuseStep 4867955 = 7301933) B7301933
theorem B2279303 : Blo 1518456 2279303 := bstep (se 1 (by rfl) ⟨1709477, by rfl⟩ : syracuseStep 2279303 = 3418955) B3418955
theorem B2279339 : Blo 1518456 2279339 := bstep (se 1 (by rfl) ⟨1709504, by rfl⟩ : syracuseStep 2279339 = 3419009) B3419009
theorem B2279369 : Blo 1518456 2279369 := bstep (se 2 (by rfl) ⟨854763, by rfl⟩ : syracuseStep 2279369 = 1709527) B1709527
theorem B4327435 : Blo 1518456 4327435 := bstep (se 1 (by rfl) ⟨3245576, by rfl⟩ : syracuseStep 4327435 = 6491153) B6491153
theorem B3418127 : Blo 1518456 3418127 := bstep (se 1 (by rfl) ⟨2563595, by rfl⟩ : syracuseStep 3418127 = 5127191) B5127191
theorem B5769245 : Blo 1518456 5769245 := bstep (se 3 (by rfl) ⟨1081733, by rfl⟩ : syracuseStep 5769245 = 2163467) B2163467
theorem B5130269 : Blo 1518456 5130269 := bstep (se 3 (by rfl) ⟨961925, by rfl⟩ : syracuseStep 5130269 = 1923851) B1923851
theorem B3418145 : Blo 1518456 3418145 := bstep (se 2 (by rfl) ⟨1281804, by rfl⟩ : syracuseStep 3418145 = 2563609) B2563609
theorem B2279483 : Blo 1518456 2279483 := bstep (se 1 (by rfl) ⟨1709612, by rfl⟩ : syracuseStep 2279483 = 3419225) B3419225
theorem B2435131 : Blo 1518456 2435131 := bstep (se 1 (by rfl) ⟨1826348, by rfl⟩ : syracuseStep 2435131 = 3652697) B3652697
theorem B18024535 : Blo 1518456 18024535 := bstep (se 1 (by rfl) ⟨13518401, by rfl⟩ : syracuseStep 18024535 = 27036803) B27036803
theorem B5851223 : Blo 1518456 5851223 := bstep (se 1 (by rfl) ⟨4388417, by rfl⟩ : syracuseStep 5851223 = 8776835) B8776835
theorem B2279543 : Blo 1518456 2279543 := bstep (se 1 (by rfl) ⟨1709657, by rfl⟩ : syracuseStep 2279543 = 3419315) B3419315
theorem B2279567 : Blo 1518456 2279567 := bstep (se 1 (by rfl) ⟨1709675, by rfl⟩ : syracuseStep 2279567 = 3419351) B3419351
theorem B2279609 : Blo 1518456 2279609 := bstep (se 2 (by rfl) ⟨854853, by rfl⟩ : syracuseStep 2279609 = 1709707) B1709707
theorem B4868353 : Blo 1518456 4868353 := bstep (se 2 (by rfl) ⟨1825632, by rfl⟩ : syracuseStep 4868353 = 3651265) B3651265
theorem B2279687 : Blo 1518456 2279687 := bstep (se 1 (by rfl) ⟨1709765, by rfl⟩ : syracuseStep 2279687 = 3419531) B3419531
theorem B2279723 : Blo 1518456 2279723 := bstep (se 1 (by rfl) ⟨1709792, by rfl⟩ : syracuseStep 2279723 = 3419585) B3419585
theorem B2279753 : Blo 1518456 2279753 := bstep (se 2 (by rfl) ⟨854907, by rfl⟩ : syracuseStep 2279753 = 1709815) B1709815
theorem B3418487 : Blo 1518456 3418487 := bstep (se 1 (by rfl) ⟨2563865, by rfl⟩ : syracuseStep 3418487 = 5127731) B5127731
theorem B2279867 : Blo 1518456 2279867 := bstep (se 1 (by rfl) ⟨1709900, by rfl⟩ : syracuseStep 2279867 = 3419801) B3419801
theorem B2279927 : Blo 1518456 2279927 := bstep (se 1 (by rfl) ⟨1709945, by rfl⟩ : syracuseStep 2279927 = 3419891) B3419891
theorem B4327937 : Blo 1518456 4327937 := bstep (se 2 (by rfl) ⟨1622976, by rfl⟩ : syracuseStep 4327937 = 3245953) B3245953
theorem B2279951 : Blo 1518456 2279951 := bstep (se 1 (by rfl) ⟨1709963, by rfl⟩ : syracuseStep 2279951 = 3419927) B3419927
theorem B3418667 : Blo 1518456 3418667 := bstep (se 1 (by rfl) ⟨2564000, by rfl⟩ : syracuseStep 3418667 = 5128001) B5128001
theorem B2886187 : Blo 1518456 2886187 := bstep (se 1 (by rfl) ⟨2164640, by rfl⟩ : syracuseStep 2886187 = 4329281) B4329281
theorem B2279993 : Blo 1518456 2279993 := bstep (se 2 (by rfl) ⟨854997, by rfl⟩ : syracuseStep 2279993 = 1709995) B1709995
theorem B18491969 : Blo 1518456 18491969 := bstep (se 2 (by rfl) ⟨6934488, by rfl⟩ : syracuseStep 18491969 = 13868977) B13868977
theorem B14805605 : Blo 1518456 14805605 := bstep (se 4 (by rfl) ⟨1388025, by rfl⟩ : syracuseStep 14805605 = 2776051) B2776051
theorem B2886263 : Blo 1518456 2886263 := bstep (se 1 (by rfl) ⟨2164697, by rfl⟩ : syracuseStep 2886263 = 4329395) B4329395
theorem B2280071 : Blo 1518456 2280071 := bstep (se 1 (by rfl) ⟨1710053, by rfl⟩ : syracuseStep 2280071 = 3420107) B3420107
theorem B2280107 : Blo 1518456 2280107 := bstep (se 1 (by rfl) ⟨1710080, by rfl⟩ : syracuseStep 2280107 = 3420161) B3420161
theorem B2280137 : Blo 1518456 2280137 := bstep (se 2 (by rfl) ⟨855051, by rfl⟩ : syracuseStep 2280137 = 1710103) B1710103
theorem B5475053 : Blo 1518456 5475053 := bstep (se 3 (by rfl) ⟨1026572, by rfl⟩ : syracuseStep 5475053 = 2053145) B2053145
theorem B11537153 : Blo 1518456 11537153 := bstep (se 2 (by rfl) ⟨4326432, by rfl⟩ : syracuseStep 11537153 = 8652865) B8652865
theorem B41609999 : Blo 1518456 41609999 := bstep (se 1 (by rfl) ⟨31207499, by rfl⟩ : syracuseStep 41609999 = 62414999) B62414999
theorem B2280251 : Blo 1518456 2280251 := bstep (se 1 (by rfl) ⟨1710188, by rfl⟩ : syracuseStep 2280251 = 3420377) B3420377
theorem B4328279 : Blo 1518456 4328279 := bstep (se 1 (by rfl) ⟨3246209, by rfl⟩ : syracuseStep 4328279 = 6492419) B6492419
theorem B3844979 : Blo 1518456 3844979 := bstep (se 1 (by rfl) ⟨2883734, by rfl⟩ : syracuseStep 3844979 = 5767469) B5767469
theorem B2280311 : Blo 1518456 2280311 := bstep (se 1 (by rfl) ⟨1710233, by rfl⟩ : syracuseStep 2280311 = 3420467) B3420467
theorem B1518471 : Blo 1518456 1518471 := bstep (se 1 (by rfl) ⟨1138853, by rfl⟩ : syracuseStep 1518471 = 2277707) B2277707
theorem B3124103 : Blo 1518456 3124103 := bstep (se 1 (by rfl) ⟨2343077, by rfl⟩ : syracuseStep 3124103 = 4686155) B4686155
theorem B1518479 : Blo 1518456 1518479 := bstep (se 1 (by rfl) ⟨1138859, by rfl⟩ : syracuseStep 1518479 = 2277719) B2277719
theorem B2280335 : Blo 1518456 2280335 := bstep (se 1 (by rfl) ⟨1710251, by rfl⟩ : syracuseStep 2280335 = 3420503) B3420503
theorem B3419027 : Blo 1518456 3419027 := bstep (se 1 (by rfl) ⟨2564270, by rfl⟩ : syracuseStep 3419027 = 5128541) B5128541
theorem B5548985 : Blo 1518456 5548985 := bstep (se 2 (by rfl) ⟨2080869, by rfl⟩ : syracuseStep 5548985 = 4161739) B4161739
theorem B2280377 : Blo 1518456 2280377 := bstep (se 2 (by rfl) ⟨855141, by rfl⟩ : syracuseStep 2280377 = 1710283) B1710283
theorem B1518523 : Blo 1518456 1518523 := bstep (se 1 (by rfl) ⟨1138892, by rfl⟩ : syracuseStep 1518523 = 2277785) B2277785
theorem B3419081 : Blo 1518456 3419081 := bstep (se 2 (by rfl) ⟨1282155, by rfl⟩ : syracuseStep 3419081 = 2564311) B2564311
theorem B1518599 : Blo 1518456 1518599 := bstep (se 1 (by rfl) ⟨1138949, by rfl⟩ : syracuseStep 1518599 = 2277899) B2277899
theorem B2280455 : Blo 1518456 2280455 := bstep (se 1 (by rfl) ⟨1710341, by rfl⟩ : syracuseStep 2280455 = 3420683) B3420683
theorem B3648527 : Blo 1518456 3648527 := bstep (se 1 (by rfl) ⟨2736395, by rfl⟩ : syracuseStep 3648527 = 5472791) B5472791
theorem B1518607 : Blo 1518456 1518607 := bstep (se 1 (by rfl) ⟨1138955, by rfl⟩ : syracuseStep 1518607 = 2277911) B2277911
theorem B2280491 : Blo 1518456 2280491 := bstep (se 1 (by rfl) ⟨1710368, by rfl⟩ : syracuseStep 2280491 = 3420737) B3420737
theorem B1518651 : Blo 1518456 1518651 := bstep (se 1 (by rfl) ⟨1138988, by rfl⟩ : syracuseStep 1518651 = 2277977) B2277977
theorem B2280521 : Blo 1518456 2280521 := bstep (se 2 (by rfl) ⟨855195, by rfl⟩ : syracuseStep 2280521 = 1710391) B1710391
theorem B1518727 : Blo 1518456 1518727 := bstep (se 1 (by rfl) ⟨1139045, by rfl⟩ : syracuseStep 1518727 = 2278091) B2278091
theorem B1518735 : Blo 1518456 1518735 := bstep (se 1 (by rfl) ⟨1139051, by rfl⟩ : syracuseStep 1518735 = 2278103) B2278103
theorem B1518779 : Blo 1518456 1518779 := bstep (se 1 (by rfl) ⟨1139084, by rfl⟩ : syracuseStep 1518779 = 2278169) B2278169
theorem B2280635 : Blo 1518456 2280635 := bstep (se 1 (by rfl) ⟨1710476, by rfl⟩ : syracuseStep 2280635 = 3420953) B3420953
theorem B1518855 : Blo 1518456 1518855 := bstep (se 1 (by rfl) ⟨1139141, by rfl⟩ : syracuseStep 1518855 = 2278283) B2278283
theorem B1518863 : Blo 1518456 1518863 := bstep (se 1 (by rfl) ⟨1139147, by rfl⟩ : syracuseStep 1518863 = 2278295) B2278295
theorem B1518907 : Blo 1518456 1518907 := bstep (se 1 (by rfl) ⟨1139180, by rfl⟩ : syracuseStep 1518907 = 2278361) B2278361
theorem B3845495 : Blo 1518456 3845495 := bstep (se 1 (by rfl) ⟨2884121, by rfl⟩ : syracuseStep 3845495 = 5768243) B5768243
theorem B1518983 : Blo 1518456 1518983 := bstep (se 1 (by rfl) ⟨1139237, by rfl⟩ : syracuseStep 1518983 = 2278475) B2278475
theorem B9244039 : Blo 1518456 9244039 := bstep (se 1 (by rfl) ⟨6933029, by rfl⟩ : syracuseStep 9244039 = 13866059) B13866059
theorem B6163847 : Blo 1518456 6163847 := bstep (se 1 (by rfl) ⟨4622885, by rfl⟩ : syracuseStep 6163847 = 9245771) B9245771
theorem B1518991 : Blo 1518456 1518991 := bstep (se 1 (by rfl) ⟨1139243, by rfl⟩ : syracuseStep 1518991 = 2278487) B2278487
theorem B1519035 : Blo 1518456 1519035 := bstep (se 1 (by rfl) ⟨1139276, by rfl⟩ : syracuseStep 1519035 = 2278553) B2278553
theorem B1519111 : Blo 1518456 1519111 := bstep (se 1 (by rfl) ⟨1139333, by rfl⟩ : syracuseStep 1519111 = 2278667) B2278667
theorem B1519119 : Blo 1518456 1519119 := bstep (se 1 (by rfl) ⟨1139339, by rfl⟩ : syracuseStep 1519119 = 2278679) B2278679
theorem B7687709 : Blo 1518456 7687709 := bstep (se 3 (by rfl) ⟨1441445, by rfl⟩ : syracuseStep 7687709 = 2882891) B2882891
theorem B1519163 : Blo 1518456 1519163 := bstep (se 1 (by rfl) ⟨1139372, by rfl⟩ : syracuseStep 1519163 = 2278745) B2278745
theorem B7302743 : Blo 1518456 7302743 := bstep (se 1 (by rfl) ⟨5477057, by rfl⟩ : syracuseStep 7302743 = 10954115) B10954115
theorem B6491735 : Blo 1518456 6491735 := bstep (se 1 (by rfl) ⟨4868801, by rfl⟩ : syracuseStep 6491735 = 9737603) B9737603
theorem B5770871 : Blo 1518456 5770871 := bstep (se 1 (by rfl) ⟨4328153, by rfl⟩ : syracuseStep 5770871 = 8656307) B8656307
theorem B1519239 : Blo 1518456 1519239 := bstep (se 1 (by rfl) ⟨1139429, by rfl⟩ : syracuseStep 1519239 = 2278859) B2278859
theorem B3419783 : Blo 1518456 3419783 := bstep (se 1 (by rfl) ⟨2564837, by rfl⟩ : syracuseStep 3419783 = 5129675) B5129675
theorem B1519247 : Blo 1518456 1519247 := bstep (se 1 (by rfl) ⟨1139435, by rfl⟩ : syracuseStep 1519247 = 2278871) B2278871
theorem B14593715 : Blo 1518456 14593715 := bstep (se 1 (by rfl) ⟨10945286, by rfl⟩ : syracuseStep 14593715 = 21890573) B21890573
theorem B1519291 : Blo 1518456 1519291 := bstep (se 1 (by rfl) ⟨1139468, by rfl⟩ : syracuseStep 1519291 = 2278937) B2278937
theorem B1519367 : Blo 1518456 1519367 := bstep (se 1 (by rfl) ⟨1139525, by rfl⟩ : syracuseStep 1519367 = 2279051) B2279051
theorem B3649295 : Blo 1518456 3649295 := bstep (se 1 (by rfl) ⟨2736971, by rfl⟩ : syracuseStep 3649295 = 5473943) B5473943
theorem B1519375 : Blo 1518456 1519375 := bstep (se 1 (by rfl) ⟨1139531, by rfl⟩ : syracuseStep 1519375 = 2279063) B2279063
theorem B1519419 : Blo 1518456 1519419 := bstep (se 1 (by rfl) ⟨1139564, by rfl⟩ : syracuseStep 1519419 = 2279129) B2279129
theorem B3419963 : Blo 1518456 3419963 := bstep (se 1 (by rfl) ⟨2564972, by rfl⟩ : syracuseStep 3419963 = 5129945) B5129945
theorem B1519495 : Blo 1518456 1519495 := bstep (se 1 (by rfl) ⟨1139621, by rfl⟩ : syracuseStep 1519495 = 2279243) B2279243
theorem B1519503 : Blo 1518456 1519503 := bstep (se 1 (by rfl) ⟨1139627, by rfl⟩ : syracuseStep 1519503 = 2279255) B2279255
theorem B3420089 : Blo 1518456 3420089 := bstep (se 2 (by rfl) ⟨1282533, by rfl⟩ : syracuseStep 3420089 = 2565067) B2565067
theorem B1519547 : Blo 1518456 1519547 := bstep (se 1 (by rfl) ⟨1139660, by rfl⟩ : syracuseStep 1519547 = 2279321) B2279321
theorem B4681729 : Blo 1518456 4681729 := bstep (se 2 (by rfl) ⟨1755648, by rfl⟩ : syracuseStep 4681729 = 3511297) B3511297
theorem B7688195 : Blo 1518456 7688195 := bstep (se 1 (by rfl) ⟨5766146, by rfl⟩ : syracuseStep 7688195 = 11532293) B11532293
theorem B1519623 : Blo 1518456 1519623 := bstep (se 1 (by rfl) ⟨1139717, by rfl⟩ : syracuseStep 1519623 = 2279435) B2279435
theorem B1519631 : Blo 1518456 1519631 := bstep (se 1 (by rfl) ⟨1139723, by rfl⟩ : syracuseStep 1519631 = 2279447) B2279447
theorem B1519675 : Blo 1518456 1519675 := bstep (se 1 (by rfl) ⟨1139756, by rfl⟩ : syracuseStep 1519675 = 2279513) B2279513
theorem B1519751 : Blo 1518456 1519751 := bstep (se 1 (by rfl) ⟨1139813, by rfl⟩ : syracuseStep 1519751 = 2279627) B2279627
theorem B1519759 : Blo 1518456 1519759 := bstep (se 1 (by rfl) ⟨1139819, by rfl⟩ : syracuseStep 1519759 = 2279639) B2279639
theorem B1519803 : Blo 1518456 1519803 := bstep (se 1 (by rfl) ⟨1139852, by rfl⟩ : syracuseStep 1519803 = 2279705) B2279705
theorem B1519879 : Blo 1518456 1519879 := bstep (se 1 (by rfl) ⟨1139909, by rfl⟩ : syracuseStep 1519879 = 2279819) B2279819
theorem B1708303 : Blo 1518456 1708303 := bstep (se 1 (by rfl) ⟨1281227, by rfl⟩ : syracuseStep 1708303 = 2562455) B2562455
theorem B1519887 : Blo 1518456 1519887 := bstep (se 1 (by rfl) ⟨1139915, by rfl⟩ : syracuseStep 1519887 = 2279831) B2279831
theorem B3420431 : Blo 1518456 3420431 := bstep (se 1 (by rfl) ⟨2565323, by rfl⟩ : syracuseStep 3420431 = 5130647) B5130647
theorem B4870415 : Blo 1518456 4870415 := bstep (se 1 (by rfl) ⟨3652811, by rfl⟩ : syracuseStep 4870415 = 7305623) B7305623
theorem B3420449 : Blo 1518456 3420449 := bstep (se 2 (by rfl) ⟨1282668, by rfl⟩ : syracuseStep 3420449 = 2565337) B2565337
theorem B13857083 : Blo 1518456 13857083 := bstep (se 1 (by rfl) ⟨10392812, by rfl⟩ : syracuseStep 13857083 = 20785625) B20785625
theorem B1519931 : Blo 1518456 1519931 := bstep (se 1 (by rfl) ⟨1139948, by rfl⟩ : syracuseStep 1519931 = 2279897) B2279897
theorem B3846487 : Blo 1518456 3846487 := bstep (se 1 (by rfl) ⟨2884865, by rfl⟩ : syracuseStep 3846487 = 5769731) B5769731
theorem B1520007 : Blo 1518456 1520007 := bstep (se 1 (by rfl) ⟨1140005, by rfl⟩ : syracuseStep 1520007 = 2280011) B2280011
theorem B1520015 : Blo 1518456 1520015 := bstep (se 1 (by rfl) ⟨1140011, by rfl⟩ : syracuseStep 1520015 = 2280023) B2280023
theorem B1520059 : Blo 1518456 1520059 := bstep (se 1 (by rfl) ⟨1140044, by rfl⟩ : syracuseStep 1520059 = 2280089) B2280089
theorem B1520135 : Blo 1518456 1520135 := bstep (se 1 (by rfl) ⟨1140101, by rfl⟩ : syracuseStep 1520135 = 2280203) B2280203
theorem B1520143 : Blo 1518456 1520143 := bstep (se 1 (by rfl) ⟨1140107, by rfl⟩ : syracuseStep 1520143 = 2280215) B2280215
theorem B21918251 : Blo 1518456 21918251 := bstep (se 1 (by rfl) ⟨16438688, by rfl⟩ : syracuseStep 21918251 = 32877377) B32877377
theorem B1520187 : Blo 1518456 1520187 := bstep (se 1 (by rfl) ⟨1140140, by rfl⟩ : syracuseStep 1520187 = 2280281) B2280281
theorem B5771843 : Blo 1518456 5771843 := bstep (se 1 (by rfl) ⟨4328882, by rfl⟩ : syracuseStep 5771843 = 8657765) B8657765
theorem B3420791 : Blo 1518456 3420791 := bstep (se 1 (by rfl) ⟨2565593, by rfl⟩ : syracuseStep 3420791 = 5131187) B5131187
theorem B3846791 : Blo 1518456 3846791 := bstep (se 1 (by rfl) ⟨2885093, by rfl⟩ : syracuseStep 3846791 = 5770187) B5770187
theorem B1520263 : Blo 1518456 1520263 := bstep (se 1 (by rfl) ⟨1140197, by rfl⟩ : syracuseStep 1520263 = 2280395) B2280395
theorem B1520271 : Blo 1518456 1520271 := bstep (se 1 (by rfl) ⟨1140203, by rfl⟩ : syracuseStep 1520271 = 2280407) B2280407
theorem B1520315 : Blo 1518456 1520315 := bstep (se 1 (by rfl) ⟨1140236, by rfl⟩ : syracuseStep 1520315 = 2280473) B2280473
theorem B12972737 : Blo 1518456 12972737 := bstep (se 2 (by rfl) ⟨4864776, by rfl⟩ : syracuseStep 12972737 = 9729553) B9729553
theorem B1708807 : Blo 1518456 1708807 := bstep (se 1 (by rfl) ⟨1281605, by rfl⟩ : syracuseStep 1708807 = 2563211) B2563211
theorem B1520391 : Blo 1518456 1520391 := bstep (se 1 (by rfl) ⟨1140293, by rfl⟩ : syracuseStep 1520391 = 2280587) B2280587
theorem B3846923 : Blo 1518456 3846923 := bstep (se 1 (by rfl) ⟨2885192, by rfl⟩ : syracuseStep 3846923 = 5770385) B5770385
theorem B1520399 : Blo 1518456 1520399 := bstep (se 1 (by rfl) ⟨1140299, by rfl⟩ : syracuseStep 1520399 = 2280599) B2280599
theorem B3420971 : Blo 1518456 3420971 := bstep (se 1 (by rfl) ⟨2565728, by rfl⟩ : syracuseStep 3420971 = 5131457) B5131457
theorem B5124923 : Blo 1518456 5124923 := bstep (se 1 (by rfl) ⟨3843692, by rfl⟩ : syracuseStep 5124923 = 7687385) B7687385
theorem B1520443 : Blo 1518456 1520443 := bstep (se 1 (by rfl) ⟨1140332, by rfl⟩ : syracuseStep 1520443 = 2280665) B2280665
theorem B7697267 : Blo 1518456 7697267 := bstep (se 1 (by rfl) ⟨5772950, by rfl⟩ : syracuseStep 7697267 = 11545901) B11545901
theorem B1921963 : Blo 1518456 1921963 := bstep (se 1 (by rfl) ⟨1441472, by rfl⟩ : syracuseStep 1921963 = 2882945) B2882945
theorem B140293043 : Blo 1518456 140293043 := bstep (se 1 (by rfl) ⟨105219782, by rfl⟩ : syracuseStep 140293043 = 210439565) B210439565
theorem B1708987 : Blo 1518456 1708987 := bstep (se 1 (by rfl) ⟨1281740, by rfl⟩ : syracuseStep 1708987 = 2563481) B2563481
theorem B65704931 : Blo 1518456 65704931 := bstep (se 1 (by rfl) ⟨49278698, by rfl⟩ : syracuseStep 65704931 = 98557397) B98557397
theorem B7304393 : Blo 1518456 7304393 := bstep (se 2 (by rfl) ⟨2739147, by rfl⟩ : syracuseStep 7304393 = 5478295) B5478295
theorem B12981485 : Blo 1518456 12981485 := bstep (se 3 (by rfl) ⟨2434028, by rfl⟩ : syracuseStep 12981485 = 4868057) B4868057
theorem B3847439 : Blo 1518456 3847439 := bstep (se 1 (by rfl) ⟨2885579, by rfl⟩ : syracuseStep 3847439 = 5771159) B5771159
theorem B5125409 : Blo 1518456 5125409 := bstep (se 2 (by rfl) ⟨1922028, by rfl⟩ : syracuseStep 5125409 = 3844057) B3844057
theorem B17315207 : Blo 1518456 17315207 := bstep (se 1 (by rfl) ⟨12986405, by rfl⟩ : syracuseStep 17315207 = 25972811) B25972811
theorem B1709455 : Blo 1518456 1709455 := bstep (se 1 (by rfl) ⟨1282091, by rfl⟩ : syracuseStep 1709455 = 2564183) B2564183
theorem B3847571 : Blo 1518456 3847571 := bstep (se 1 (by rfl) ⟨2885678, by rfl⟩ : syracuseStep 3847571 = 5771357) B5771357
theorem B35067421 : Blo 1518456 35067421 := bstep (se 3 (by rfl) ⟨6575141, by rfl⟩ : syracuseStep 35067421 = 13150283) B13150283
theorem B5772829 : Blo 1518456 5772829 := bstep (se 3 (by rfl) ⟨1082405, by rfl⟩ : syracuseStep 5772829 = 2164811) B2164811
theorem B7689815 : Blo 1518456 7689815 := bstep (se 1 (by rfl) ⟨5767361, by rfl⟩ : syracuseStep 7689815 = 11534723) B11534723
theorem B256366309 : Blo 1518456 256366309 := bstep (se 4 (by rfl) ⟨24034341, by rfl⟩ : syracuseStep 256366309 = 48068683) B48068683
theorem B1824503 : Blo 1518456 1824503 := bstep (se 1 (by rfl) ⟨1368377, by rfl⟩ : syracuseStep 1824503 = 2736755) B2736755
theorem B19470131 : Blo 1518456 19470131 := bstep (se 1 (by rfl) ⟨14602598, by rfl⟩ : syracuseStep 19470131 = 29205197) B29205197
theorem B5126003 : Blo 1518456 5126003 := bstep (se 1 (by rfl) ⟨3844502, by rfl⟩ : syracuseStep 5126003 = 7689005) B7689005
theorem B1922935 : Blo 1518456 1922935 := bstep (se 1 (by rfl) ⟨1442201, by rfl⟩ : syracuseStep 1922935 = 2884403) B2884403
theorem B3700615 : Blo 1518456 3700615 := bstep (se 1 (by rfl) ⟨2775461, by rfl⟩ : syracuseStep 3700615 = 5550923) B5550923
theorem B1709959 : Blo 1518456 1709959 := bstep (se 1 (by rfl) ⟨1282469, by rfl⟩ : syracuseStep 1709959 = 2564939) B2564939
theorem B5339033 : Blo 1518456 5339033 := bstep (se 2 (by rfl) ⟨2002137, by rfl⟩ : syracuseStep 5339033 = 4004275) B4004275
theorem B1849387 : Blo 1518456 1849387 := bstep (se 1 (by rfl) ⟨1387040, by rfl⟩ : syracuseStep 1849387 = 2774081) B2774081
theorem B1710139 : Blo 1518456 1710139 := bstep (se 1 (by rfl) ⟨1282604, by rfl⟩ : syracuseStep 1710139 = 2565209) B2565209
theorem B8648765 : Blo 1518456 8648765 := bstep (se 3 (by rfl) ⟨1621643, by rfl⟩ : syracuseStep 8648765 = 3243287) B3243287
theorem B7690301 : Blo 1518456 7690301 := bstep (se 3 (by rfl) ⟨1441931, by rfl⟩ : syracuseStep 7690301 = 2883863) B2883863
theorem B1923259 : Blo 1518456 1923259 := bstep (se 1 (by rfl) ⟨1442444, by rfl⟩ : syracuseStep 1923259 = 2884889) B2884889
theorem B14596483 : Blo 1518456 14596483 := bstep (se 1 (by rfl) ⟨10947362, by rfl⟩ : syracuseStep 14596483 = 21894725) B21894725
theorem B13867523 : Blo 1518456 13867523 := bstep (se 1 (by rfl) ⟨10400642, by rfl⟩ : syracuseStep 13867523 = 20801285) B20801285
theorem B2562745 : Blo 1518456 2562745 := bstep (se 2 (by rfl) ⟨961029, by rfl⟩ : syracuseStep 2562745 = 1922059) B1922059
theorem B8329999 : Blo 1518456 8329999 := bstep (se 1 (by rfl) ⟨6247499, by rfl⟩ : syracuseStep 8329999 = 12494999) B12494999
theorem B3652505 : Blo 1518456 3652505 := bstep (se 2 (by rfl) ⟨1369689, by rfl⟩ : syracuseStep 3652505 = 2739379) B2739379
theorem B11541527 : Blo 1518456 11541527 := bstep (se 1 (by rfl) ⟨8656145, by rfl⟩ : syracuseStep 11541527 = 17312291) B17312291
theorem B12491837 : Blo 1518456 12491837 := bstep (se 3 (by rfl) ⟨2342219, by rfl⟩ : syracuseStep 12491837 = 4684439) B4684439
theorem B17775749 : Blo 1518456 17775749 := bstep (se 4 (by rfl) ⟨1666476, by rfl⟩ : syracuseStep 17775749 = 3332953) B3332953
theorem B1924231 : Blo 1518456 1924231 := bstep (se 1 (by rfl) ⟨1443173, by rfl⟩ : syracuseStep 1924231 = 2886347) B2886347
theorem B7306433 : Blo 1518456 7306433 := bstep (se 2 (by rfl) ⟨2739912, by rfl⟩ : syracuseStep 7306433 = 5479825) B5479825
theorem B2563447 : Blo 1518456 2563447 := bstep (se 1 (by rfl) ⟨1922585, by rfl⟩ : syracuseStep 2563447 = 3845171) B3845171
theorem B9239953 : Blo 1518456 9239953 := bstep (se 2 (by rfl) ⟨3464982, by rfl⟩ : syracuseStep 9239953 = 6929965) B6929965
theorem B46759427 : Blo 1518456 46759427 := bstep (se 1 (by rfl) ⟨35069570, by rfl⟩ : syracuseStep 46759427 = 70139141) B70139141
theorem B1539599 : Blo 1518456 1539599 := bstep (se 1 (by rfl) ⟨1154699, by rfl⟩ : syracuseStep 1539599 = 2309399) B2309399
theorem B4324907 : Blo 1518456 4324907 := bstep (se 1 (by rfl) ⟨3243680, by rfl⟩ : syracuseStep 4324907 = 6487361) B6487361
theorem B2563643 : Blo 1518456 2563643 := bstep (se 1 (by rfl) ⟨1922732, by rfl⟩ : syracuseStep 2563643 = 3845465) B3845465
theorem B4865597 : Blo 1518456 4865597 := bstep (se 3 (by rfl) ⟨912299, by rfl⟩ : syracuseStep 4865597 = 1824599) B1824599
theorem B3243655 : Blo 1518456 3243655 := bstep (se 1 (by rfl) ⟨2432741, by rfl⟩ : syracuseStep 3243655 = 4865483) B4865483
theorem B32841395 : Blo 1518456 32841395 := bstep (se 1 (by rfl) ⟨24631046, by rfl⟩ : syracuseStep 32841395 = 49262093) B49262093
theorem B13860659 : Blo 1518456 13860659 := bstep (se 1 (by rfl) ⟨10395494, by rfl⟩ : syracuseStep 13860659 = 20790989) B20790989
theorem B7692083 : Blo 1518456 7692083 := bstep (se 1 (by rfl) ⟨5769062, by rfl⟩ : syracuseStep 7692083 = 11538125) B11538125
theorem B2924435 : Blo 1518456 2924435 := bstep (se 1 (by rfl) ⟨2193326, by rfl⟩ : syracuseStep 2924435 = 4386653) B4386653
theorem B49299353 : Blo 1518456 49299353 := bstep (se 2 (by rfl) ⟨18487257, by rfl⟩ : syracuseStep 49299353 = 36974515) B36974515
theorem B2883529 : Blo 1518456 2883529 := bstep (se 2 (by rfl) ⟨1081323, by rfl⟩ : syracuseStep 2883529 = 2162647) B2162647
theorem B2564041 : Blo 1518456 2564041 := bstep (se 2 (by rfl) ⟨961515, by rfl⟩ : syracuseStep 2564041 = 1923031) B1923031
theorem B24969221 : Blo 1518456 24969221 := bstep (se 4 (by rfl) ⟨2340864, by rfl⟩ : syracuseStep 24969221 = 4681729) B4681729
theorem B2465849 : Blo 1518456 2465849 := bstep (se 2 (by rfl) ⟨924693, by rfl⟩ : syracuseStep 2465849 = 1849387) B1849387
theorem B5128271 : Blo 1518456 5128271 := bstep (se 1 (by rfl) ⟨3846203, by rfl⟩ : syracuseStep 5128271 = 7692407) B7692407
theorem B2883833 : Blo 1518456 2883833 := bstep (se 2 (by rfl) ⟨1081437, by rfl⟩ : syracuseStep 2883833 = 2162875) B2162875
theorem B2564345 : Blo 1518456 2564345 := bstep (se 2 (by rfl) ⟨961629, by rfl⟩ : syracuseStep 2564345 = 1923259) B1923259
theorem B3080521 : Blo 1518456 3080521 := bstep (se 2 (by rfl) ⟨1155195, by rfl⟩ : syracuseStep 3080521 = 2310391) B2310391
theorem B2081119 : Blo 1518456 2081119 := bstep (se 1 (by rfl) ⟨1560839, by rfl⟩ : syracuseStep 2081119 = 3121679) B3121679
theorem B2277737 : Blo 1518456 2277737 := bstep (se 2 (by rfl) ⟨854151, by rfl⟩ : syracuseStep 2277737 = 1708303) B1708303
theorem B2884015 : Blo 1518456 2884015 := bstep (se 1 (by rfl) ⟨2163011, by rfl⟩ : syracuseStep 2884015 = 4326023) B4326023
theorem B2564527 : Blo 1518456 2564527 := bstep (se 1 (by rfl) ⟨1923395, by rfl⟩ : syracuseStep 2564527 = 3846791) B3846791
theorem B2277815 : Blo 1518456 2277815 := bstep (se 1 (by rfl) ⟨1708361, by rfl⟩ : syracuseStep 2277815 = 3416723) B3416723
theorem B5128649 : Blo 1518456 5128649 := bstep (se 2 (by rfl) ⟨1923243, by rfl⟩ : syracuseStep 5128649 = 3846487) B3846487
theorem B2277851 : Blo 1518456 2277851 := bstep (se 1 (by rfl) ⟨1708388, by rfl⟩ : syracuseStep 2277851 = 3416777) B3416777
theorem B2564615 : Blo 1518456 2564615 := bstep (se 1 (by rfl) ⟨1923461, by rfl⟩ : syracuseStep 2564615 = 3846923) B3846923
theorem B3416615 : Blo 1518456 3416615 := bstep (se 1 (by rfl) ⟨2562461, by rfl⟩ : syracuseStep 3416615 = 5124923) B5124923
theorem B93528695 : Blo 1518456 93528695 := bstep (se 1 (by rfl) ⟨70146521, by rfl⟩ : syracuseStep 93528695 = 140293043) B140293043
theorem B43803287 : Blo 1518456 43803287 := bstep (se 1 (by rfl) ⟨32852465, by rfl⟩ : syracuseStep 43803287 = 65704931) B65704931
theorem B14811821 : Blo 1518456 14811821 := bstep (se 3 (by rfl) ⟨2777216, by rfl⟩ : syracuseStep 14811821 = 5554433) B5554433
theorem B6488761 : Blo 1518456 6488761 := bstep (se 2 (by rfl) ⟨2433285, by rfl⟩ : syracuseStep 6488761 = 4866571) B4866571
theorem B5128919 : Blo 1518456 5128919 := bstep (se 1 (by rfl) ⟨3846689, by rfl⟩ : syracuseStep 5128919 = 7693379) B7693379
theorem B2564959 : Blo 1518456 2564959 := bstep (se 1 (by rfl) ⟨1923719, by rfl⟩ : syracuseStep 2564959 = 3847439) B3847439
theorem B3416939 : Blo 1518456 3416939 := bstep (se 1 (by rfl) ⟨2562704, by rfl⟩ : syracuseStep 3416939 = 5125409) B5125409
theorem B3416993 : Blo 1518456 3416993 := bstep (se 2 (by rfl) ⟨1281372, by rfl⟩ : syracuseStep 3416993 = 2562745) B2562745
theorem B2278319 : Blo 1518456 2278319 := bstep (se 1 (by rfl) ⟨1708739, by rfl⟩ : syracuseStep 2278319 = 3417479) B3417479
theorem B5129135 : Blo 1518456 5129135 := bstep (se 1 (by rfl) ⟨3846851, by rfl⟩ : syracuseStep 5129135 = 7693703) B7693703
theorem B1622959 : Blo 1518456 1622959 := bstep (se 1 (by rfl) ⟨1217219, by rfl⟩ : syracuseStep 1622959 = 2434439) B2434439
theorem B11543471 : Blo 1518456 11543471 := bstep (se 1 (by rfl) ⟨8657603, by rfl⟩ : syracuseStep 11543471 = 17315207) B17315207
theorem B5473207 : Blo 1518456 5473207 := bstep (se 1 (by rfl) ⟨4104905, by rfl⟩ : syracuseStep 5473207 = 8209811) B8209811
theorem B2565047 : Blo 1518456 2565047 := bstep (se 1 (by rfl) ⟨1923785, by rfl⟩ : syracuseStep 2565047 = 3847571) B3847571
theorem B4326331 : Blo 1518456 4326331 := bstep (se 1 (by rfl) ⟨3244748, by rfl⟩ : syracuseStep 4326331 = 6489497) B6489497
theorem B2278409 : Blo 1518456 2278409 := bstep (se 2 (by rfl) ⟨854403, by rfl⟩ : syracuseStep 2278409 = 1708807) B1708807
theorem B2278439 : Blo 1518456 2278439 := bstep (se 1 (by rfl) ⟨1708829, by rfl⟩ : syracuseStep 2278439 = 3417659) B3417659
theorem B1623079 : Blo 1518456 1623079 := bstep (se 1 (by rfl) ⟨1217309, by rfl⟩ : syracuseStep 1623079 = 2434619) B2434619
theorem B4326479 : Blo 1518456 4326479 := bstep (se 1 (by rfl) ⟨3244859, by rfl⟩ : syracuseStep 4326479 = 6489719) B6489719
theorem B5768273 : Blo 1518456 5768273 := bstep (se 2 (by rfl) ⟨2163102, by rfl⟩ : syracuseStep 5768273 = 4326205) B4326205
theorem B2278523 : Blo 1518456 2278523 := bstep (se 1 (by rfl) ⟨1708892, by rfl⟩ : syracuseStep 2278523 = 3417785) B3417785
theorem B3417335 : Blo 1518456 3417335 := bstep (se 1 (by rfl) ⟨2563001, by rfl⟩ : syracuseStep 3417335 = 5126003) B5126003
theorem B3245303 : Blo 1518456 3245303 := bstep (se 1 (by rfl) ⟨2433977, by rfl⟩ : syracuseStep 3245303 = 4867955) B4867955
theorem B2278649 : Blo 1518456 2278649 := bstep (se 2 (by rfl) ⟨854493, by rfl⟩ : syracuseStep 2278649 = 1708987) B1708987
theorem B2278751 : Blo 1518456 2278751 := bstep (se 1 (by rfl) ⟨1709063, by rfl⟩ : syracuseStep 2278751 = 3418127) B3418127
theorem B2278763 : Blo 1518456 2278763 := bstep (se 1 (by rfl) ⟨1709072, by rfl⟩ : syracuseStep 2278763 = 3418145) B3418145
theorem B3900815 : Blo 1518456 3900815 := bstep (se 1 (by rfl) ⟨2925611, by rfl⟩ : syracuseStep 3900815 = 5851223) B5851223
theorem B2565641 : Blo 1518456 2565641 := bstep (se 2 (by rfl) ⟨962115, by rfl⟩ : syracuseStep 2565641 = 1924231) B1924231
theorem B5768729 : Blo 1518456 5768729 := bstep (se 2 (by rfl) ⟨2163273, by rfl⟩ : syracuseStep 5768729 = 4326547) B4326547
theorem B2278991 : Blo 1518456 2278991 := bstep (se 1 (by rfl) ⟨1709243, by rfl⟩ : syracuseStep 2278991 = 3418487) B3418487
theorem B2885291 : Blo 1518456 2885291 := bstep (se 1 (by rfl) ⟨2163968, by rfl⟩ : syracuseStep 2885291 = 4327937) B4327937
theorem B2279111 : Blo 1518456 2279111 := bstep (se 1 (by rfl) ⟨1709333, by rfl⟩ : syracuseStep 2279111 = 3418667) B3418667
theorem B3417929 : Blo 1518456 3417929 := bstep (se 2 (by rfl) ⟨1281723, by rfl⟩ : syracuseStep 3417929 = 2563447) B2563447
theorem B27739999 : Blo 1518456 27739999 := bstep (se 1 (by rfl) ⟨20804999, by rfl⟩ : syracuseStep 27739999 = 41609999) B41609999
theorem B2279273 : Blo 1518456 2279273 := bstep (se 2 (by rfl) ⟨854727, by rfl⟩ : syracuseStep 2279273 = 1709455) B1709455
theorem B7694189 : Blo 1518456 7694189 := bstep (se 3 (by rfl) ⟨1442660, by rfl⟩ : syracuseStep 7694189 = 2885321) B2885321
theorem B2885519 : Blo 1518456 2885519 := bstep (se 1 (by rfl) ⟨2164139, by rfl⟩ : syracuseStep 2885519 = 4328279) B4328279
theorem B2279351 : Blo 1518456 2279351 := bstep (se 1 (by rfl) ⟨1709513, by rfl⟩ : syracuseStep 2279351 = 3419027) B3419027
theorem B2435003 : Blo 1518456 2435003 := bstep (se 1 (by rfl) ⟨1826252, by rfl⟩ : syracuseStep 2435003 = 3652505) B3652505
theorem B2279387 : Blo 1518456 2279387 := bstep (se 1 (by rfl) ⟨1709540, by rfl⟩ : syracuseStep 2279387 = 3419081) B3419081
theorem B7694351 : Blo 1518456 7694351 := bstep (se 1 (by rfl) ⟨5770763, by rfl⟩ : syracuseStep 7694351 = 11541527) B11541527
theorem B4327481 : Blo 1518456 4327481 := bstep (se 2 (by rfl) ⟨1622805, by rfl⟩ : syracuseStep 4327481 = 3245611) B3245611
theorem B341821745 : Blo 1518456 341821745 := bstep (se 2 (by rfl) ⟨128183154, by rfl⟩ : syracuseStep 341821745 = 256366309) B256366309
theorem B31172951 : Blo 1518456 31172951 := bstep (se 1 (by rfl) ⟨23379713, by rfl⟩ : syracuseStep 31172951 = 46759427) B46759427
theorem B4868495 : Blo 1518456 4868495 := bstep (se 1 (by rfl) ⟨3651371, by rfl⟩ : syracuseStep 4868495 = 7302743) B7302743
theorem B4327823 : Blo 1518456 4327823 := bstep (se 1 (by rfl) ⟨3245867, by rfl⟩ : syracuseStep 4327823 = 6491735) B6491735
theorem B2279855 : Blo 1518456 2279855 := bstep (se 1 (by rfl) ⟨1709891, by rfl⟩ : syracuseStep 2279855 = 3419783) B3419783
theorem B4934153 : Blo 1518456 4934153 := bstep (se 2 (by rfl) ⟨1850307, by rfl⟩ : syracuseStep 4934153 = 3700615) B3700615
theorem B2279945 : Blo 1518456 2279945 := bstep (se 2 (by rfl) ⟨854979, by rfl⟩ : syracuseStep 2279945 = 1709959) B1709959
theorem B2279975 : Blo 1518456 2279975 := bstep (se 1 (by rfl) ⟨1709981, by rfl⟩ : syracuseStep 2279975 = 3419963) B3419963
theorem B3844705 : Blo 1518456 3844705 := bstep (se 2 (by rfl) ⟨1441764, by rfl⟩ : syracuseStep 3844705 = 2883529) B2883529
theorem B3418721 : Blo 1518456 3418721 := bstep (se 2 (by rfl) ⟨1282020, by rfl⟩ : syracuseStep 3418721 = 2564041) B2564041
theorem B2280059 : Blo 1518456 2280059 := bstep (se 1 (by rfl) ⟨1710044, by rfl⟩ : syracuseStep 2280059 = 3420089) B3420089
theorem B5769913 : Blo 1518456 5769913 := bstep (se 2 (by rfl) ⟨2163717, by rfl⟩ : syracuseStep 5769913 = 4327435) B4327435
theorem B2468551 : Blo 1518456 2468551 := bstep (se 1 (by rfl) ⟨1851413, by rfl⟩ : syracuseStep 2468551 = 3702827) B3702827
theorem B2280185 : Blo 1518456 2280185 := bstep (se 2 (by rfl) ⟨855069, by rfl⟩ : syracuseStep 2280185 = 1710139) B1710139
theorem B3246841 : Blo 1518456 3246841 := bstep (se 2 (by rfl) ⟨1217565, by rfl⟩ : syracuseStep 3246841 = 2435131) B2435131
theorem B20802379 : Blo 1518456 20802379 := bstep (se 1 (by rfl) ⟨15601784, by rfl⟩ : syracuseStep 20802379 = 31203569) B31203569
theorem B2280287 : Blo 1518456 2280287 := bstep (se 1 (by rfl) ⟨1710215, by rfl⟩ : syracuseStep 2280287 = 3420431) B3420431
theorem B2280299 : Blo 1518456 2280299 := bstep (se 1 (by rfl) ⟨1710224, by rfl⟩ : syracuseStep 2280299 = 3420449) B3420449
theorem B1518459 : Blo 1518456 1518459 := bstep (se 1 (by rfl) ⟨1138844, by rfl⟩ : syracuseStep 1518459 = 2277689) B2277689
theorem B1518511 : Blo 1518456 1518511 := bstep (se 1 (by rfl) ⟨1138883, by rfl⟩ : syracuseStep 1518511 = 2277767) B2277767
theorem B3419063 : Blo 1518456 3419063 := bstep (se 1 (by rfl) ⟨2564297, by rfl⟩ : syracuseStep 3419063 = 5128595) B5128595
theorem B1518535 : Blo 1518456 1518535 := bstep (se 1 (by rfl) ⟨1138901, by rfl⟩ : syracuseStep 1518535 = 2277803) B2277803
theorem B1518555 : Blo 1518456 1518555 := bstep (se 1 (by rfl) ⟨1138916, by rfl⟩ : syracuseStep 1518555 = 2277833) B2277833
theorem B6491137 : Blo 1518456 6491137 := bstep (se 2 (by rfl) ⟨2434176, by rfl⟩ : syracuseStep 6491137 = 4868353) B4868353
theorem B1518631 : Blo 1518456 1518631 := bstep (se 1 (by rfl) ⟨1138973, by rfl⟩ : syracuseStep 1518631 = 2277947) B2277947
theorem B1518671 : Blo 1518456 1518671 := bstep (se 1 (by rfl) ⟨1139003, by rfl⟩ : syracuseStep 1518671 = 2278007) B2278007
theorem B2280527 : Blo 1518456 2280527 := bstep (se 1 (by rfl) ⟨1710395, by rfl⟩ : syracuseStep 2280527 = 3420791) B3420791
theorem B1518687 : Blo 1518456 1518687 := bstep (se 1 (by rfl) ⟨1139015, by rfl⟩ : syracuseStep 1518687 = 2278031) B2278031
theorem B1518715 : Blo 1518456 1518715 := bstep (se 1 (by rfl) ⟨1139036, by rfl⟩ : syracuseStep 1518715 = 2278073) B2278073
theorem B1518767 : Blo 1518456 1518767 := bstep (se 1 (by rfl) ⟨1139075, by rfl⟩ : syracuseStep 1518767 = 2278151) B2278151
theorem B1518791 : Blo 1518456 1518791 := bstep (se 1 (by rfl) ⟨1139093, by rfl⟩ : syracuseStep 1518791 = 2278187) B2278187
theorem B2280647 : Blo 1518456 2280647 := bstep (se 1 (by rfl) ⟨1710485, by rfl⟩ : syracuseStep 2280647 = 3420971) B3420971
theorem B1518811 : Blo 1518456 1518811 := bstep (se 1 (by rfl) ⟨1139108, by rfl⟩ : syracuseStep 1518811 = 2278217) B2278217
theorem B5131511 : Blo 1518456 5131511 := bstep (se 1 (by rfl) ⟨3848633, by rfl⟩ : syracuseStep 5131511 = 7697267) B7697267
theorem B1518887 : Blo 1518456 1518887 := bstep (se 1 (by rfl) ⟨1139165, by rfl⟩ : syracuseStep 1518887 = 2278331) B2278331
theorem B1518927 : Blo 1518456 1518927 := bstep (se 1 (by rfl) ⟨1139195, by rfl⟩ : syracuseStep 1518927 = 2278391) B2278391
theorem B1518943 : Blo 1518456 1518943 := bstep (se 1 (by rfl) ⟨1139207, by rfl⟩ : syracuseStep 1518943 = 2278415) B2278415
theorem B1518971 : Blo 1518456 1518971 := bstep (se 1 (by rfl) ⟨1139228, by rfl⟩ : syracuseStep 1518971 = 2278457) B2278457
theorem B12987773 : Blo 1518456 12987773 := bstep (se 3 (by rfl) ⟨2435207, by rfl⟩ : syracuseStep 12987773 = 4870415) B4870415
theorem B1519023 : Blo 1518456 1519023 := bstep (se 1 (by rfl) ⟨1139267, by rfl⟩ : syracuseStep 1519023 = 2278535) B2278535
theorem B1519047 : Blo 1518456 1519047 := bstep (se 1 (by rfl) ⟨1139285, by rfl⟩ : syracuseStep 1519047 = 2278571) B2278571
theorem B1519067 : Blo 1518456 1519067 := bstep (se 1 (by rfl) ⟨1139300, by rfl⟩ : syracuseStep 1519067 = 2278601) B2278601
theorem B4869595 : Blo 1518456 4869595 := bstep (se 1 (by rfl) ⟨3652196, by rfl⟩ : syracuseStep 4869595 = 7304393) B7304393
theorem B8654323 : Blo 1518456 8654323 := bstep (se 1 (by rfl) ⟨6490742, by rfl⟩ : syracuseStep 8654323 = 12981485) B12981485
theorem B3419657 : Blo 1518456 3419657 := bstep (se 2 (by rfl) ⟨1282371, by rfl⟩ : syracuseStep 3419657 = 2564743) B2564743
theorem B3845657 : Blo 1518456 3845657 := bstep (se 2 (by rfl) ⟨1442121, by rfl⟩ : syracuseStep 3845657 = 2884243) B2884243
theorem B1519143 : Blo 1518456 1519143 := bstep (se 1 (by rfl) ⟨1139357, by rfl⟩ : syracuseStep 1519143 = 2278715) B2278715
theorem B1519183 : Blo 1518456 1519183 := bstep (se 1 (by rfl) ⟨1139387, by rfl⟩ : syracuseStep 1519183 = 2278775) B2278775
theorem B1519199 : Blo 1518456 1519199 := bstep (se 1 (by rfl) ⟨1139399, by rfl⟩ : syracuseStep 1519199 = 2278799) B2278799
theorem B1519227 : Blo 1518456 1519227 := bstep (se 1 (by rfl) ⟨1139420, by rfl⟩ : syracuseStep 1519227 = 2278841) B2278841
theorem B20786827 : Blo 1518456 20786827 := bstep (se 1 (by rfl) ⟨15590120, by rfl⟩ : syracuseStep 20786827 = 31180241) B31180241
theorem B1519279 : Blo 1518456 1519279 := bstep (se 1 (by rfl) ⟨1139459, by rfl⟩ : syracuseStep 1519279 = 2278919) B2278919
theorem B1519303 : Blo 1518456 1519303 := bstep (se 1 (by rfl) ⟨1139477, by rfl⟩ : syracuseStep 1519303 = 2278955) B2278955
theorem B5844695 : Blo 1518456 5844695 := bstep (se 1 (by rfl) ⟨4383521, by rfl⟩ : syracuseStep 5844695 = 8767043) B8767043
theorem B1519323 : Blo 1518456 1519323 := bstep (se 1 (by rfl) ⟨1139492, by rfl⟩ : syracuseStep 1519323 = 2278985) B2278985
theorem B1519399 : Blo 1518456 1519399 := bstep (se 1 (by rfl) ⟨1139549, by rfl⟩ : syracuseStep 1519399 = 2279099) B2279099
theorem B1519439 : Blo 1518456 1519439 := bstep (se 1 (by rfl) ⟨1139579, by rfl⟩ : syracuseStep 1519439 = 2279159) B2279159
theorem B1519455 : Blo 1518456 1519455 := bstep (se 1 (by rfl) ⟨1139591, by rfl⟩ : syracuseStep 1519455 = 2279183) B2279183
theorem B3419999 : Blo 1518456 3419999 := bstep (se 1 (by rfl) ⟨2564999, by rfl⟩ : syracuseStep 3419999 = 5129999) B5129999
theorem B12980087 : Blo 1518456 12980087 := bstep (se 1 (by rfl) ⟨9735065, by rfl⟩ : syracuseStep 12980087 = 19470131) B19470131
theorem B1519483 : Blo 1518456 1519483 := bstep (se 1 (by rfl) ⟨1139612, by rfl⟩ : syracuseStep 1519483 = 2279225) B2279225
theorem B1519535 : Blo 1518456 1519535 := bstep (se 1 (by rfl) ⟨1139651, by rfl⟩ : syracuseStep 1519535 = 2279303) B2279303
theorem B3559355 : Blo 1518456 3559355 := bstep (se 1 (by rfl) ⟨2669516, by rfl⟩ : syracuseStep 3559355 = 5339033) B5339033
theorem B1519559 : Blo 1518456 1519559 := bstep (se 1 (by rfl) ⟨1139669, by rfl⟩ : syracuseStep 1519559 = 2279339) B2279339
theorem B1519579 : Blo 1518456 1519579 := bstep (se 1 (by rfl) ⟨1139684, by rfl⟩ : syracuseStep 1519579 = 2279369) B2279369
theorem B3846163 : Blo 1518456 3846163 := bstep (se 1 (by rfl) ⟨2884622, by rfl⟩ : syracuseStep 3846163 = 5769245) B5769245
theorem B3420179 : Blo 1518456 3420179 := bstep (se 1 (by rfl) ⟨2565134, by rfl⟩ : syracuseStep 3420179 = 5130269) B5130269
theorem B1519655 : Blo 1518456 1519655 := bstep (se 1 (by rfl) ⟨1139741, by rfl⟩ : syracuseStep 1519655 = 2279483) B2279483
theorem B1519695 : Blo 1518456 1519695 := bstep (se 1 (by rfl) ⟨1139771, by rfl⟩ : syracuseStep 1519695 = 2279543) B2279543
theorem B1519711 : Blo 1518456 1519711 := bstep (se 1 (by rfl) ⟨1139783, by rfl⟩ : syracuseStep 1519711 = 2279567) B2279567
theorem B1519739 : Blo 1518456 1519739 := bstep (se 1 (by rfl) ⟨1139804, by rfl⟩ : syracuseStep 1519739 = 2279609) B2279609
theorem B1519791 : Blo 1518456 1519791 := bstep (se 1 (by rfl) ⟨1139843, by rfl⟩ : syracuseStep 1519791 = 2279687) B2279687
theorem B1519815 : Blo 1518456 1519815 := bstep (se 1 (by rfl) ⟨1139861, by rfl⟩ : syracuseStep 1519815 = 2279723) B2279723
theorem B1519835 : Blo 1518456 1519835 := bstep (se 1 (by rfl) ⟨1139876, by rfl⟩ : syracuseStep 1519835 = 2279753) B2279753
theorem B1519911 : Blo 1518456 1519911 := bstep (se 1 (by rfl) ⟨1139933, by rfl⟩ : syracuseStep 1519911 = 2279867) B2279867
theorem B1519951 : Blo 1518456 1519951 := bstep (se 1 (by rfl) ⟨1139963, by rfl⟩ : syracuseStep 1519951 = 2279927) B2279927
theorem B9245015 : Blo 1518456 9245015 := bstep (se 1 (by rfl) ⟨6933761, by rfl⟩ : syracuseStep 9245015 = 13867523) B13867523
theorem B1519967 : Blo 1518456 1519967 := bstep (se 1 (by rfl) ⟨1139975, by rfl⟩ : syracuseStep 1519967 = 2279951) B2279951
theorem B3420521 : Blo 1518456 3420521 := bstep (se 2 (by rfl) ⟨1282695, by rfl⟩ : syracuseStep 3420521 = 2565391) B2565391
theorem B1519995 : Blo 1518456 1519995 := bstep (se 1 (by rfl) ⟨1139996, by rfl⟩ : syracuseStep 1519995 = 2279993) B2279993
theorem B5771645 : Blo 1518456 5771645 := bstep (se 3 (by rfl) ⟨1082183, by rfl⟩ : syracuseStep 5771645 = 2164367) B2164367
theorem B1520047 : Blo 1518456 1520047 := bstep (se 1 (by rfl) ⟨1140035, by rfl⟩ : syracuseStep 1520047 = 2280071) B2280071
theorem B1520071 : Blo 1518456 1520071 := bstep (se 1 (by rfl) ⟨1140053, by rfl⟩ : syracuseStep 1520071 = 2280107) B2280107
theorem B1520091 : Blo 1518456 1520091 := bstep (se 1 (by rfl) ⟨1140068, by rfl⟩ : syracuseStep 1520091 = 2280137) B2280137
theorem B3650035 : Blo 1518456 3650035 := bstep (se 1 (by rfl) ⟨2737526, by rfl⟩ : syracuseStep 3650035 = 5475053) B5475053
theorem B12325385 : Blo 1518456 12325385 := bstep (se 2 (by rfl) ⟨4622019, by rfl⟩ : syracuseStep 12325385 = 9244039) B9244039
theorem B1520167 : Blo 1518456 1520167 := bstep (se 1 (by rfl) ⟨1140125, by rfl⟩ : syracuseStep 1520167 = 2280251) B2280251
theorem B1520207 : Blo 1518456 1520207 := bstep (se 1 (by rfl) ⟨1140155, by rfl⟩ : syracuseStep 1520207 = 2280311) B2280311
theorem B1520223 : Blo 1518456 1520223 := bstep (se 1 (by rfl) ⟨1140167, by rfl⟩ : syracuseStep 1520223 = 2280335) B2280335
theorem B3699323 : Blo 1518456 3699323 := bstep (se 1 (by rfl) ⟨2774492, by rfl⟩ : syracuseStep 3699323 = 5548985) B5548985
theorem B1520251 : Blo 1518456 1520251 := bstep (se 1 (by rfl) ⟨1140188, by rfl⟩ : syracuseStep 1520251 = 2280377) B2280377
theorem B1520303 : Blo 1518456 1520303 := bstep (se 1 (by rfl) ⟨1140227, by rfl⟩ : syracuseStep 1520303 = 2280455) B2280455
theorem B1520327 : Blo 1518456 1520327 := bstep (se 1 (by rfl) ⟨1140245, by rfl⟩ : syracuseStep 1520327 = 2280491) B2280491
theorem B46756561 : Blo 1518456 46756561 := bstep (se 2 (by rfl) ⟨17533710, by rfl⟩ : syracuseStep 46756561 = 35067421) B35067421
theorem B8327891 : Blo 1518456 8327891 := bstep (se 1 (by rfl) ⟨6245918, by rfl⟩ : syracuseStep 8327891 = 12491837) B12491837
theorem B7697105 : Blo 1518456 7697105 := bstep (se 2 (by rfl) ⟨2886414, by rfl⟩ : syracuseStep 7697105 = 5772829) B5772829
theorem B1520347 : Blo 1518456 1520347 := bstep (se 1 (by rfl) ⟨1140260, by rfl⟩ : syracuseStep 1520347 = 2280521) B2280521
theorem B11850499 : Blo 1518456 11850499 := bstep (se 1 (by rfl) ⟨8887874, by rfl⟩ : syracuseStep 11850499 = 17775749) B17775749
theorem B1520423 : Blo 1518456 1520423 := bstep (se 1 (by rfl) ⟨1140317, by rfl⟩ : syracuseStep 1520423 = 2280635) B2280635
theorem B4870955 : Blo 1518456 4870955 := bstep (se 1 (by rfl) ⟨3653216, by rfl⟩ : syracuseStep 4870955 = 7306433) B7306433
theorem B4109231 : Blo 1518456 4109231 := bstep (se 1 (by rfl) ⟨3081923, by rfl⟩ : syracuseStep 4109231 = 6163847) B6163847
theorem B5125139 : Blo 1518456 5125139 := bstep (se 1 (by rfl) ⟨3843854, by rfl⟩ : syracuseStep 5125139 = 7687709) B7687709
theorem B1709095 : Blo 1518456 1709095 := bstep (se 1 (by rfl) ⟨1281821, by rfl⟩ : syracuseStep 1709095 = 2563643) B2563643
theorem B3847247 : Blo 1518456 3847247 := bstep (se 1 (by rfl) ⟨2885435, by rfl⟩ : syracuseStep 3847247 = 5770871) B5770871
theorem B9729143 : Blo 1518456 9729143 := bstep (se 1 (by rfl) ⟨7296857, by rfl⟩ : syracuseStep 9729143 = 14593715) B14593715
theorem B21894263 : Blo 1518456 21894263 := bstep (se 1 (by rfl) ⟨16420697, by rfl⟩ : syracuseStep 21894263 = 32841395) B32841395
theorem B5125463 : Blo 1518456 5125463 := bstep (se 1 (by rfl) ⟨3844097, by rfl⟩ : syracuseStep 5125463 = 7688195) B7688195
theorem B24032713 : Blo 1518456 24032713 := bstep (se 2 (by rfl) ⟨9012267, by rfl⟩ : syracuseStep 24032713 = 18024535) B18024535
theorem B16422389 : Blo 1518456 16422389 := bstep (se 5 (by rfl) ⟨769799, by rfl⟩ : syracuseStep 16422389 = 1539599) B1539599
theorem B9238055 : Blo 1518456 9238055 := bstep (se 1 (by rfl) ⟨6928541, by rfl⟩ : syracuseStep 9238055 = 13857083) B13857083
theorem B5199499 : Blo 1518456 5199499 := bstep (se 1 (by rfl) ⟨3899624, by rfl⟩ : syracuseStep 5199499 = 7799249) B7799249
theorem B14612167 : Blo 1518456 14612167 := bstep (se 1 (by rfl) ⟨10959125, by rfl⟩ : syracuseStep 14612167 = 21918251) B21918251
theorem B3847895 : Blo 1518456 3847895 := bstep (se 1 (by rfl) ⟨2885921, by rfl⟩ : syracuseStep 3847895 = 5771843) B5771843
theorem B7689977 : Blo 1518456 7689977 := bstep (se 2 (by rfl) ⟨2883741, by rfl⟩ : syracuseStep 7689977 = 5767483) B5767483
theorem B8648491 : Blo 1518456 8648491 := bstep (se 1 (by rfl) ⟨6486368, by rfl⟩ : syracuseStep 8648491 = 12972737) B12972737
theorem B19461977 : Blo 1518456 19461977 := bstep (se 2 (by rfl) ⟨7298241, by rfl⟩ : syracuseStep 19461977 = 14596483) B14596483
theorem B1824619 : Blo 1518456 1824619 := bstep (se 1 (by rfl) ⟨1368464, by rfl⟩ : syracuseStep 1824619 = 2736929) B2736929
theorem B3848249 : Blo 1518456 3848249 := bstep (se 2 (by rfl) ⟨1443093, by rfl⟩ : syracuseStep 3848249 = 2886187) B2886187
theorem B8657239 : Blo 1518456 8657239 := bstep (se 1 (by rfl) ⟨6492929, by rfl⟩ : syracuseStep 8657239 = 12985859) B12985859
theorem B11106665 : Blo 1518456 11106665 := bstep (se 2 (by rfl) ⟨4164999, by rfl⟩ : syracuseStep 11106665 = 8329999) B8329999
theorem B7690625 : Blo 1518456 7690625 := bstep (se 2 (by rfl) ⟨2883984, by rfl⟩ : syracuseStep 7690625 = 5767969) B5767969
theorem B5126543 : Blo 1518456 5126543 := bstep (se 1 (by rfl) ⟨3844907, by rfl⟩ : syracuseStep 5126543 = 7689815) B7689815
theorem B2562617 : Blo 1518456 2562617 := bstep (se 2 (by rfl) ⟨960981, by rfl⟩ : syracuseStep 2562617 = 1921963) B1921963
theorem B5765843 : Blo 1518456 5765843 := bstep (se 1 (by rfl) ⟨4324382, by rfl⟩ : syracuseStep 5765843 = 8648765) B8648765
theorem B5126867 : Blo 1518456 5126867 := bstep (se 1 (by rfl) ⟨3845150, by rfl⟩ : syracuseStep 5126867 = 7690301) B7690301
theorem B12327979 : Blo 1518456 12327979 := bstep (se 1 (by rfl) ⟨9245984, by rfl⟩ : syracuseStep 12327979 = 18491969) B18491969
theorem B9870403 : Blo 1518456 9870403 := bstep (se 1 (by rfl) ⟨7402802, by rfl⟩ : syracuseStep 9870403 = 14805605) B14805605
theorem B1924175 : Blo 1518456 1924175 := bstep (se 1 (by rfl) ⟨1443131, by rfl⟩ : syracuseStep 1924175 = 2886263) B2886263
theorem B7691435 : Blo 1518456 7691435 := bstep (se 1 (by rfl) ⟨5768576, by rfl⟩ : syracuseStep 7691435 = 11537153) B11537153
theorem B12319937 : Blo 1518456 12319937 := bstep (se 2 (by rfl) ⟨4619976, by rfl⟩ : syracuseStep 12319937 = 9239953) B9239953
theorem B2563319 : Blo 1518456 2563319 := bstep (se 1 (by rfl) ⟨1922489, by rfl⟩ : syracuseStep 2563319 = 3844979) B3844979
theorem B4865341 : Blo 1518456 4865341 := bstep (se 3 (by rfl) ⟨912251, by rfl⟩ : syracuseStep 4865341 = 1824503) B1824503
theorem B2432351 : Blo 1518456 2432351 := bstep (se 1 (by rfl) ⟨1824263, by rfl⟩ : syracuseStep 2432351 = 3648527) B3648527
theorem B112418225 : Blo 1518456 112418225 := bstep (se 2 (by rfl) ⟨42156834, by rfl⟩ : syracuseStep 112418225 = 84313669) B84313669
theorem B36961757 : Blo 1518456 36961757 := bstep (se 3 (by rfl) ⟨6930329, by rfl⟩ : syracuseStep 36961757 = 13860659) B13860659
theorem B4324873 : Blo 1518456 4324873 := bstep (se 2 (by rfl) ⟨1621827, by rfl⟩ : syracuseStep 4324873 = 3243655) B3243655
theorem B2563663 : Blo 1518456 2563663 := bstep (se 1 (by rfl) ⟨1922747, by rfl⟩ : syracuseStep 2563663 = 3845495) B3845495
theorem B7691921 : Blo 1518456 7691921 := bstep (se 2 (by rfl) ⟨2884470, by rfl⟩ : syracuseStep 7691921 = 5768941) B5768941
theorem B8330941 : Blo 1518456 8330941 := bstep (se 3 (by rfl) ⟨1562051, by rfl⟩ : syracuseStep 8330941 = 3124103) B3124103
theorem B2883271 : Blo 1518456 2883271 := bstep (se 1 (by rfl) ⟨2162453, by rfl⟩ : syracuseStep 2883271 = 4324907) B4324907
theorem B3243731 : Blo 1518456 3243731 := bstep (se 1 (by rfl) ⟨2432798, by rfl⟩ : syracuseStep 3243731 = 4865597) B4865597
theorem B7798493 : Blo 1518456 7798493 := bstep (se 3 (by rfl) ⟨1462217, by rfl⟩ : syracuseStep 7798493 = 2924435) B2924435
theorem B2563913 : Blo 1518456 2563913 := bstep (se 2 (by rfl) ⟨961467, by rfl⟩ : syracuseStep 2563913 = 1922935) B1922935
theorem B2432863 : Blo 1518456 2432863 := bstep (se 1 (by rfl) ⟨1824647, by rfl⟩ : syracuseStep 2432863 = 3649295) B3649295
theorem B5128055 : Blo 1518456 5128055 := bstep (se 1 (by rfl) ⟨3846041, by rfl⟩ : syracuseStep 5128055 = 7692083) B7692083
theorem B32866235 : Blo 1518456 32866235 := bstep (se 1 (by rfl) ⟨24649676, by rfl⟩ : syracuseStep 32866235 = 49299353) B49299353
theorem B16646147 : Blo 1518456 16646147 := bstep (se 1 (by rfl) ⟨12484610, by rfl⟩ : syracuseStep 16646147 = 24969221) B24969221
theorem B5128217 : Blo 1518456 5128217 := bstep (se 2 (by rfl) ⟨1923081, by rfl⟩ : syracuseStep 5128217 = 3846163) B3846163
theorem B2277743 : Blo 1518456 2277743 := bstep (se 1 (by rfl) ⟨1708307, by rfl⟩ : syracuseStep 2277743 = 3416615) B3416615
theorem B2466215 : Blo 1518456 2466215 := bstep (se 1 (by rfl) ⟨1849661, by rfl⟩ : syracuseStep 2466215 = 3699323) B3699323
theorem B11542985 : Blo 1518456 11542985 := bstep (se 2 (by rfl) ⟨4328619, by rfl⟩ : syracuseStep 11542985 = 8657239) B8657239
theorem B2277959 : Blo 1518456 2277959 := bstep (se 1 (by rfl) ⟨1708469, by rfl⟩ : syracuseStep 2277959 = 3416939) B3416939
theorem B2277995 : Blo 1518456 2277995 := bstep (se 1 (by rfl) ⟨1708496, by rfl⟩ : syracuseStep 2277995 = 3416993) B3416993
theorem B4866713 : Blo 1518456 4866713 := bstep (se 2 (by rfl) ⟨1825017, by rfl⟩ : syracuseStep 4866713 = 3650035) B3650035
theorem B3416759 : Blo 1518456 3416759 := bstep (se 1 (by rfl) ⟨2562569, by rfl⟩ : syracuseStep 3416759 = 5125139) B5125139
theorem B2884319 : Blo 1518456 2884319 := bstep (se 1 (by rfl) ⟨2163239, by rfl⟩ : syracuseStep 2884319 = 4326479) B4326479
theorem B2564831 : Blo 1518456 2564831 := bstep (se 1 (by rfl) ⟨1923623, by rfl⟩ : syracuseStep 2564831 = 3847247) B3847247
theorem B2278223 : Blo 1518456 2278223 := bstep (se 1 (by rfl) ⟨1708667, by rfl⟩ : syracuseStep 2278223 = 3417335) B3417335
theorem B3416975 : Blo 1518456 3416975 := bstep (se 1 (by rfl) ⟨2562731, by rfl⟩ : syracuseStep 3416975 = 5125463) B5125463
theorem B8651681 : Blo 1518456 8651681 := bstep (se 2 (by rfl) ⟨3244380, by rfl⟩ : syracuseStep 8651681 = 6488761) B6488761
theorem B7693217 : Blo 1518456 7693217 := bstep (se 2 (by rfl) ⟨2884956, by rfl⟩ : syracuseStep 7693217 = 5769913) B5769913
theorem B62342081 : Blo 1518456 62342081 := bstep (se 2 (by rfl) ⟨23378280, by rfl⟩ : syracuseStep 62342081 = 46756561) B46756561
theorem B2565263 : Blo 1518456 2565263 := bstep (se 1 (by rfl) ⟨1923947, by rfl⟩ : syracuseStep 2565263 = 3847895) B3847895
theorem B2278619 : Blo 1518456 2278619 := bstep (se 1 (by rfl) ⟨1708964, by rfl⟩ : syracuseStep 2278619 = 3417929) B3417929
theorem B5129459 : Blo 1518456 5129459 := bstep (se 1 (by rfl) ⟨3847094, by rfl⟩ : syracuseStep 5129459 = 7694189) B7694189
theorem B5768441 : Blo 1518456 5768441 := bstep (se 2 (by rfl) ⟨2163165, by rfl⟩ : syracuseStep 5768441 = 4326331) B4326331
theorem B1623335 : Blo 1518456 1623335 := bstep (se 1 (by rfl) ⟨1217501, by rfl⟩ : syracuseStep 1623335 = 2435003) B2435003
theorem B5129567 : Blo 1518456 5129567 := bstep (se 1 (by rfl) ⟨3847175, by rfl⟩ : syracuseStep 5129567 = 7694351) B7694351
theorem B13157741 : Blo 1518456 13157741 := bstep (se 3 (by rfl) ⟨2467076, by rfl⟩ : syracuseStep 13157741 = 4934153) B4934153
theorem B32867693 : Blo 1518456 32867693 := bstep (se 3 (by rfl) ⟨6162692, by rfl⟩ : syracuseStep 32867693 = 12325385) B12325385
theorem B2884987 : Blo 1518456 2884987 := bstep (se 1 (by rfl) ⟨2163740, by rfl⟩ : syracuseStep 2884987 = 4327481) B4327481
theorem B2565499 : Blo 1518456 2565499 := bstep (se 1 (by rfl) ⟨1924124, by rfl⟩ : syracuseStep 2565499 = 3848249) B3848249
theorem B2278793 : Blo 1518456 2278793 := bstep (se 2 (by rfl) ⟨854547, by rfl⟩ : syracuseStep 2278793 = 1709095) B1709095
theorem B2164105 : Blo 1518456 2164105 := bstep (se 2 (by rfl) ⟨811539, by rfl⟩ : syracuseStep 2164105 = 1623079) B1623079
theorem B24634813 : Blo 1518456 24634813 := bstep (se 3 (by rfl) ⟨4619027, by rfl⟩ : syracuseStep 24634813 = 9238055) B9238055
theorem B3417695 : Blo 1518456 3417695 := bstep (se 1 (by rfl) ⟨2563271, by rfl⟩ : syracuseStep 3417695 = 5126543) B5126543
theorem B3245663 : Blo 1518456 3245663 := bstep (se 1 (by rfl) ⟨2434247, by rfl⟩ : syracuseStep 3245663 = 4868495) B4868495
theorem B2885215 : Blo 1518456 2885215 := bstep (se 1 (by rfl) ⟨2163911, by rfl⟩ : syracuseStep 2885215 = 4327823) B4327823
theorem B2279147 : Blo 1518456 2279147 := bstep (se 1 (by rfl) ⟨1709360, by rfl⟩ : syracuseStep 2279147 = 3418721) B3418721
theorem B3843895 : Blo 1518456 3843895 := bstep (se 1 (by rfl) ⟨2882921, by rfl⟩ : syracuseStep 3843895 = 5765843) B5765843
theorem B3417911 : Blo 1518456 3417911 := bstep (se 1 (by rfl) ⟨2563433, by rfl⟩ : syracuseStep 3417911 = 5126867) B5126867
theorem B2279375 : Blo 1518456 2279375 := bstep (se 1 (by rfl) ⟨1709531, by rfl⟩ : syracuseStep 2279375 = 3419063) B3419063
theorem B3418217 : Blo 1518456 3418217 := bstep (se 2 (by rfl) ⟨1281831, by rfl⟩ : syracuseStep 3418217 = 2563663) B2563663
theorem B27715769 : Blo 1518456 27715769 := bstep (se 2 (by rfl) ⟨10393413, by rfl⟩ : syracuseStep 27715769 = 20786827) B20786827
theorem B6932665 : Blo 1518456 6932665 := bstep (se 2 (by rfl) ⟨2599749, by rfl⟩ : syracuseStep 6932665 = 5199499) B5199499
theorem B3844361 : Blo 1518456 3844361 := bstep (se 2 (by rfl) ⟨1441635, by rfl⟩ : syracuseStep 3844361 = 2883271) B2883271
theorem B19482889 : Blo 1518456 19482889 := bstep (se 2 (by rfl) ⟨7306083, by rfl⟩ : syracuseStep 19482889 = 14612167) B14612167
theorem B2279771 : Blo 1518456 2279771 := bstep (se 1 (by rfl) ⟨1709828, by rfl⟩ : syracuseStep 2279771 = 3419657) B3419657
theorem B2279999 : Blo 1518456 2279999 := bstep (se 1 (by rfl) ⟨1709999, by rfl⟩ : syracuseStep 2279999 = 3419999) B3419999
theorem B8653391 : Blo 1518456 8653391 := bstep (se 1 (by rfl) ⟨6490043, by rfl⟩ : syracuseStep 8653391 = 12980087) B12980087
theorem B3418703 : Blo 1518456 3418703 := bstep (se 1 (by rfl) ⟨2564027, by rfl⟩ : syracuseStep 3418703 = 5128055) B5128055
theorem B2280119 : Blo 1518456 2280119 := bstep (se 1 (by rfl) ⟨1710089, by rfl⟩ : syracuseStep 2280119 = 3420179) B3420179
theorem B3418847 : Blo 1518456 3418847 := bstep (se 1 (by rfl) ⟨2564135, by rfl⟩ : syracuseStep 3418847 = 5128271) B5128271
theorem B5131133 : Blo 1518456 5131133 := bstep (se 3 (by rfl) ⟨962087, by rfl⟩ : syracuseStep 5131133 = 1924175) B1924175
theorem B6163343 : Blo 1518456 6163343 := bstep (se 1 (by rfl) ⟨4622507, by rfl⟩ : syracuseStep 6163343 = 9245015) B9245015
theorem B1518491 : Blo 1518456 1518491 := bstep (se 1 (by rfl) ⟨1138868, by rfl⟩ : syracuseStep 1518491 = 2277737) B2277737
theorem B2280347 : Blo 1518456 2280347 := bstep (se 1 (by rfl) ⟨1710260, by rfl⟩ : syracuseStep 2280347 = 3420521) B3420521
theorem B1518543 : Blo 1518456 1518543 := bstep (se 1 (by rfl) ⟨1138907, by rfl⟩ : syracuseStep 1518543 = 2277815) B2277815
theorem B3419099 : Blo 1518456 3419099 := bstep (se 1 (by rfl) ⟨2564324, by rfl⟩ : syracuseStep 3419099 = 5128649) B5128649
theorem B1518567 : Blo 1518456 1518567 := bstep (se 1 (by rfl) ⟨1138925, by rfl⟩ : syracuseStep 1518567 = 2277851) B2277851
theorem B62352463 : Blo 1518456 62352463 := bstep (se 1 (by rfl) ⟨46764347, by rfl⟩ : syracuseStep 62352463 = 93528695) B93528695
theorem B4107361 : Blo 1518456 4107361 := bstep (se 2 (by rfl) ⟨1540260, by rfl⟩ : syracuseStep 4107361 = 3080521) B3080521
theorem B9874547 : Blo 1518456 9874547 := bstep (se 1 (by rfl) ⟨7405910, by rfl⟩ : syracuseStep 9874547 = 14811821) B14811821
theorem B5131403 : Blo 1518456 5131403 := bstep (se 1 (by rfl) ⟨3848552, by rfl⟩ : syracuseStep 5131403 = 7697105) B7697105
theorem B3419279 : Blo 1518456 3419279 := bstep (se 1 (by rfl) ⟨2564459, by rfl⟩ : syracuseStep 3419279 = 5128919) B5128919
theorem B3247303 : Blo 1518456 3247303 := bstep (se 1 (by rfl) ⟨2435477, by rfl⟩ : syracuseStep 3247303 = 4870955) B4870955
theorem B3845353 : Blo 1518456 3845353 := bstep (se 2 (by rfl) ⟨1442007, by rfl⟩ : syracuseStep 3845353 = 2884015) B2884015
theorem B3419369 : Blo 1518456 3419369 := bstep (se 2 (by rfl) ⟨1282263, by rfl⟩ : syracuseStep 3419369 = 2564527) B2564527
theorem B1518879 : Blo 1518456 1518879 := bstep (se 1 (by rfl) ⟨1139159, by rfl⟩ : syracuseStep 1518879 = 2278319) B2278319
theorem B3419423 : Blo 1518456 3419423 := bstep (se 1 (by rfl) ⟨2564567, by rfl⟩ : syracuseStep 3419423 = 5129135) B5129135
theorem B7695647 : Blo 1518456 7695647 := bstep (se 1 (by rfl) ⟨5771735, by rfl⟩ : syracuseStep 7695647 = 11543471) B11543471
theorem B8654141 : Blo 1518456 8654141 := bstep (se 3 (by rfl) ⟨1622651, by rfl⟩ : syracuseStep 8654141 = 3245303) B3245303
theorem B1518939 : Blo 1518456 1518939 := bstep (se 1 (by rfl) ⟨1139204, by rfl⟩ : syracuseStep 1518939 = 2278409) B2278409
theorem B1518959 : Blo 1518456 1518959 := bstep (se 1 (by rfl) ⟨1139219, by rfl⟩ : syracuseStep 1518959 = 2278439) B2278439
theorem B3845515 : Blo 1518456 3845515 := bstep (se 1 (by rfl) ⟨2884136, by rfl⟩ : syracuseStep 3845515 = 5768273) B5768273
theorem B1519015 : Blo 1518456 1519015 := bstep (se 1 (by rfl) ⟨1139261, by rfl⟩ : syracuseStep 1519015 = 2278523) B2278523
theorem B1519099 : Blo 1518456 1519099 := bstep (se 1 (by rfl) ⟨1139324, by rfl⟩ : syracuseStep 1519099 = 2278649) B2278649
theorem B1519167 : Blo 1518456 1519167 := bstep (se 1 (by rfl) ⟨1139375, by rfl⟩ : syracuseStep 1519167 = 2278751) B2278751
theorem B1519175 : Blo 1518456 1519175 := bstep (se 1 (by rfl) ⟨1139381, by rfl⟩ : syracuseStep 1519175 = 2278763) B2278763
theorem B2600543 : Blo 1518456 2600543 := bstep (se 1 (by rfl) ⟨1950407, by rfl⟩ : syracuseStep 2600543 = 3900815) B3900815
theorem B4329121 : Blo 1518456 4329121 := bstep (se 2 (by rfl) ⟨1623420, by rfl⟩ : syracuseStep 4329121 = 3246841) B3246841
theorem B10948259 : Blo 1518456 10948259 := bstep (se 1 (by rfl) ⟨8211194, by rfl⟩ : syracuseStep 10948259 = 16422389) B16422389
theorem B3845819 : Blo 1518456 3845819 := bstep (se 1 (by rfl) ⟨2884364, by rfl⟩ : syracuseStep 3845819 = 5768729) B5768729
theorem B1519327 : Blo 1518456 1519327 := bstep (se 1 (by rfl) ⟨1139495, by rfl⟩ : syracuseStep 1519327 = 2278991) B2278991
theorem B3419945 : Blo 1518456 3419945 := bstep (se 2 (by rfl) ⟨1282479, by rfl⟩ : syracuseStep 3419945 = 2564959) B2564959
theorem B1519407 : Blo 1518456 1519407 := bstep (se 1 (by rfl) ⟨1139555, by rfl⟩ : syracuseStep 1519407 = 2279111) B2279111
theorem B1519515 : Blo 1518456 1519515 := bstep (se 1 (by rfl) ⟨1139636, by rfl⟩ : syracuseStep 1519515 = 2279273) B2279273
theorem B1519567 : Blo 1518456 1519567 := bstep (se 1 (by rfl) ⟨1139675, by rfl⟩ : syracuseStep 1519567 = 2279351) B2279351
theorem B1519591 : Blo 1518456 1519591 := bstep (se 1 (by rfl) ⟨1139693, by rfl⟩ : syracuseStep 1519591 = 2279387) B2279387
theorem B8654849 : Blo 1518456 8654849 := bstep (se 2 (by rfl) ⟨3245568, by rfl⟩ : syracuseStep 8654849 = 6491137) B6491137
theorem B16437305 : Blo 1518456 16437305 := bstep (se 2 (by rfl) ⟨6163989, by rfl⟩ : syracuseStep 16437305 = 12327979) B12327979
theorem B13160537 : Blo 1518456 13160537 := bstep (se 2 (by rfl) ⟨4935201, by rfl⟩ : syracuseStep 13160537 = 9870403) B9870403
theorem B227881163 : Blo 1518456 227881163 := bstep (se 1 (by rfl) ⟨170910872, by rfl⟩ : syracuseStep 227881163 = 341821745) B341821745
theorem B1519903 : Blo 1518456 1519903 := bstep (se 1 (by rfl) ⟨1139927, by rfl⟩ : syracuseStep 1519903 = 2279855) B2279855
theorem B1519963 : Blo 1518456 1519963 := bstep (se 1 (by rfl) ⟨1139972, by rfl⟩ : syracuseStep 1519963 = 2279945) B2279945
theorem B1519983 : Blo 1518456 1519983 := bstep (se 1 (by rfl) ⟨1139987, by rfl⟩ : syracuseStep 1519983 = 2279975) B2279975
theorem B1708411 : Blo 1518456 1708411 := bstep (se 1 (by rfl) ⟨1281308, by rfl⟩ : syracuseStep 1708411 = 2562617) B2562617
theorem B1520039 : Blo 1518456 1520039 := bstep (se 1 (by rfl) ⟨1140029, by rfl⟩ : syracuseStep 1520039 = 2280059) B2280059
theorem B1520123 : Blo 1518456 1520123 := bstep (se 1 (by rfl) ⟨1140092, by rfl⟩ : syracuseStep 1520123 = 2280185) B2280185
theorem B15585853 : Blo 1518456 15585853 := bstep (se 3 (by rfl) ⟨2922347, by rfl⟩ : syracuseStep 15585853 = 5844695) B5844695
theorem B1520191 : Blo 1518456 1520191 := bstep (se 1 (by rfl) ⟨1140143, by rfl⟩ : syracuseStep 1520191 = 2280287) B2280287
theorem B1520199 : Blo 1518456 1520199 := bstep (se 1 (by rfl) ⟨1140149, by rfl⟩ : syracuseStep 1520199 = 2280299) B2280299
theorem B32043617 : Blo 1518456 32043617 := bstep (se 2 (by rfl) ⟨12016356, by rfl⟩ : syracuseStep 32043617 = 24032713) B24032713
theorem B6492793 : Blo 1518456 6492793 := bstep (se 2 (by rfl) ⟨2434797, by rfl⟩ : syracuseStep 6492793 = 4869595) B4869595
theorem B11539097 : Blo 1518456 11539097 := bstep (se 2 (by rfl) ⟨4327161, by rfl⟩ : syracuseStep 11539097 = 8654323) B8654323
theorem B1520351 : Blo 1518456 1520351 := bstep (se 1 (by rfl) ⟨1140263, by rfl⟩ : syracuseStep 1520351 = 2280527) B2280527
theorem B8213291 : Blo 1518456 8213291 := bstep (se 1 (by rfl) ⟨6159968, by rfl⟩ : syracuseStep 8213291 = 12319937) B12319937
theorem B1520431 : Blo 1518456 1520431 := bstep (se 1 (by rfl) ⟨1140323, by rfl⟩ : syracuseStep 1520431 = 2280647) B2280647
theorem B1708879 : Blo 1518456 1708879 := bstep (se 1 (by rfl) ⟨1281659, by rfl⟩ : syracuseStep 1708879 = 2563319) B2563319
theorem B3421007 : Blo 1518456 3421007 := bstep (se 1 (by rfl) ⟨2565755, by rfl⟩ : syracuseStep 3421007 = 5131511) B5131511
theorem B8655781 : Blo 1518456 8655781 := bstep (se 4 (by rfl) ⟨811479, by rfl⟩ : syracuseStep 8655781 = 1622959) B1622959
theorem B74945483 : Blo 1518456 74945483 := bstep (se 1 (by rfl) ⟨56209112, by rfl⟩ : syracuseStep 74945483 = 112418225) B112418225
theorem B11531321 : Blo 1518456 11531321 := bstep (se 2 (by rfl) ⟨4324245, by rfl⟩ : syracuseStep 11531321 = 8648491) B8648491
theorem B10957949 : Blo 1518456 10957949 := bstep (se 3 (by rfl) ⟨2054615, by rfl⟩ : syracuseStep 10957949 = 4109231) B4109231
theorem B5198995 : Blo 1518456 5198995 := bstep (se 1 (by rfl) ⟨3899246, by rfl⟩ : syracuseStep 5198995 = 7798493) B7798493
theorem B1709275 : Blo 1518456 1709275 := bstep (se 1 (by rfl) ⟨1281956, by rfl⟩ : syracuseStep 1709275 = 2563913) B2563913
theorem B2372903 : Blo 1518456 2372903 := bstep (se 1 (by rfl) ⟨1779677, by rfl⟩ : syracuseStep 2372903 = 3559355) B3559355
theorem B21910823 : Blo 1518456 21910823 := bstep (se 1 (by rfl) ⟨16433117, by rfl⟩ : syracuseStep 21910823 = 32866235) B32866235
theorem B1643899 : Blo 1518456 1643899 := bstep (se 1 (by rfl) ⟨1232924, by rfl⟩ : syracuseStep 1643899 = 2465849) B2465849
theorem B1922555 : Blo 1518456 1922555 := bstep (se 1 (by rfl) ⟨1441916, by rfl⟩ : syracuseStep 1922555 = 2883833) B2883833
theorem B1709563 : Blo 1518456 1709563 := bstep (se 1 (by rfl) ⟨1282172, by rfl⟩ : syracuseStep 1709563 = 2564345) B2564345
theorem B3847763 : Blo 1518456 3847763 := bstep (se 1 (by rfl) ⟨2885822, by rfl⟩ : syracuseStep 3847763 = 5771645) B5771645
theorem B1709743 : Blo 1518456 1709743 := bstep (se 1 (by rfl) ⟨1282307, by rfl⟩ : syracuseStep 1709743 = 2564615) B2564615
theorem B29202191 : Blo 1518456 29202191 := bstep (se 1 (by rfl) ⟨21901643, by rfl⟩ : syracuseStep 29202191 = 43803287) B43803287
theorem B2774825 : Blo 1518456 2774825 := bstep (se 2 (by rfl) ⟨1040559, by rfl⟩ : syracuseStep 2774825 = 2081119) B2081119
theorem B5551927 : Blo 1518456 5551927 := bstep (se 1 (by rfl) ⟨4163945, by rfl⟩ : syracuseStep 5551927 = 8327891) B8327891
theorem B1710031 : Blo 1518456 1710031 := bstep (se 1 (by rfl) ⟨1282523, by rfl⟩ : syracuseStep 1710031 = 2565047) B2565047
theorem B6486095 : Blo 1518456 6486095 := bstep (se 1 (by rfl) ⟨4864571, by rfl⟩ : syracuseStep 6486095 = 9729143) B9729143
theorem B14596175 : Blo 1518456 14596175 := bstep (se 1 (by rfl) ⟨10947131, by rfl⟩ : syracuseStep 14596175 = 21894263) B21894263
theorem B5126273 : Blo 1518456 5126273 := bstep (se 2 (by rfl) ⟨1922352, by rfl⟩ : syracuseStep 5126273 = 3844705) B3844705
theorem B3291401 : Blo 1518456 3291401 := bstep (se 2 (by rfl) ⟨1234275, by rfl⟩ : syracuseStep 3291401 = 2468551) B2468551
theorem B44431685 : Blo 1518456 44431685 := bstep (se 4 (by rfl) ⟨4165470, by rfl⟩ : syracuseStep 44431685 = 8330941) B8330941
theorem B15800665 : Blo 1518456 15800665 := bstep (se 2 (by rfl) ⟨5925249, by rfl⟩ : syracuseStep 15800665 = 11850499) B11850499
theorem B1710427 : Blo 1518456 1710427 := bstep (se 1 (by rfl) ⟨1282820, by rfl⟩ : syracuseStep 1710427 = 2565641) B2565641
theorem B27736505 : Blo 1518456 27736505 := bstep (se 2 (by rfl) ⟨10401189, by rfl⟩ : syracuseStep 27736505 = 20802379) B20802379
theorem B1923527 : Blo 1518456 1923527 := bstep (se 1 (by rfl) ⟨1442645, by rfl⟩ : syracuseStep 1923527 = 2885291) B2885291
theorem B5126651 : Blo 1518456 5126651 := bstep (se 1 (by rfl) ⟨3844988, by rfl⟩ : syracuseStep 5126651 = 7689977) B7689977
theorem B12974651 : Blo 1518456 12974651 := bstep (se 1 (by rfl) ⟨9730988, by rfl⟩ : syracuseStep 12974651 = 19461977) B19461977
theorem B7297609 : Blo 1518456 7297609 := bstep (se 2 (by rfl) ⟨2736603, by rfl⟩ : syracuseStep 7297609 = 5473207) B5473207
theorem B1923679 : Blo 1518456 1923679 := bstep (se 1 (by rfl) ⟨1442759, by rfl⟩ : syracuseStep 1923679 = 2885519) B2885519
theorem B20781967 : Blo 1518456 20781967 := bstep (se 1 (by rfl) ⟨15586475, by rfl⟩ : syracuseStep 20781967 = 31172951) B31172951
theorem B7404443 : Blo 1518456 7404443 := bstep (se 1 (by rfl) ⟨5553332, by rfl⟩ : syracuseStep 7404443 = 11106665) B11106665
theorem B5127083 : Blo 1518456 5127083 := bstep (se 1 (by rfl) ⟨3845312, by rfl⟩ : syracuseStep 5127083 = 7690625) B7690625
theorem B6487121 : Blo 1518456 6487121 := bstep (se 2 (by rfl) ⟨2432670, by rfl⟩ : syracuseStep 6487121 = 4865341) B4865341
theorem B8649949 : Blo 1518456 8649949 := bstep (se 3 (by rfl) ⟨1621865, by rfl⟩ : syracuseStep 8649949 = 3243731) B3243731
theorem B5766497 : Blo 1518456 5766497 := bstep (se 2 (by rfl) ⟨2162436, by rfl⟩ : syracuseStep 5766497 = 4324873) B4324873
theorem B5127623 : Blo 1518456 5127623 := bstep (se 1 (by rfl) ⟨3845717, by rfl⟩ : syracuseStep 5127623 = 7691435) B7691435
theorem B1621567 : Blo 1518456 1621567 := bstep (se 1 (by rfl) ⟨1216175, by rfl⟩ : syracuseStep 1621567 = 2432351) B2432351
theorem B8658515 : Blo 1518456 8658515 := bstep (se 1 (by rfl) ⟨6493886, by rfl⟩ : syracuseStep 8658515 = 12987773) B12987773
theorem B24641171 : Blo 1518456 24641171 := bstep (se 1 (by rfl) ⟨18480878, by rfl⟩ : syracuseStep 24641171 = 36961757) B36961757
theorem B2563771 : Blo 1518456 2563771 := bstep (se 1 (by rfl) ⟨1922828, by rfl⟩ : syracuseStep 2563771 = 3845657) B3845657
theorem B5127947 : Blo 1518456 5127947 := bstep (se 1 (by rfl) ⟨3845960, by rfl⟩ : syracuseStep 5127947 = 7691921) B7691921
theorem B3243817 : Blo 1518456 3243817 := bstep (se 2 (by rfl) ⟨1216431, by rfl⟩ : syracuseStep 3243817 = 2432863) B2432863
theorem B36986665 : Blo 1518456 36986665 := bstep (se 2 (by rfl) ⟨13869999, by rfl⟩ : syracuseStep 36986665 = 27739999) B27739999
theorem B2432825 : Blo 1518456 2432825 := bstep (se 2 (by rfl) ⟨912309, by rfl⟩ : syracuseStep 2432825 = 1824619) B1824619
theorem B8773691 : Blo 1518456 8773691 := bstep (se 1 (by rfl) ⟨6580268, by rfl⟩ : syracuseStep 8773691 = 13160537) B13160537
theorem B151920775 : Blo 1518456 151920775 := bstep (se 1 (by rfl) ⟨113940581, by rfl⟩ : syracuseStep 151920775 = 227881163) B227881163
theorem B25977185 : Blo 1518456 25977185 := bstep (se 2 (by rfl) ⟨9741444, by rfl⟩ : syracuseStep 25977185 = 19482889) B19482889
theorem B3244475 : Blo 1518456 3244475 := bstep (se 1 (by rfl) ⟨2433356, by rfl⟩ : syracuseStep 3244475 = 4866713) B4866713
theorem B7692731 : Blo 1518456 7692731 := bstep (se 1 (by rfl) ⟨5769548, by rfl⟩ : syracuseStep 7692731 = 11539097) B11539097
theorem B2277839 : Blo 1518456 2277839 := bstep (se 1 (by rfl) ⟨1708379, by rfl⟩ : syracuseStep 2277839 = 3416759) B3416759
theorem B2277881 : Blo 1518456 2277881 := bstep (se 2 (by rfl) ⟨854205, by rfl⟩ : syracuseStep 2277881 = 1708411) B1708411
theorem B2277983 : Blo 1518456 2277983 := bstep (se 1 (by rfl) ⟨1708487, by rfl⟩ : syracuseStep 2277983 = 3416975) B3416975
theorem B5767787 : Blo 1518456 5767787 := bstep (se 1 (by rfl) ⟨4325840, by rfl⟩ : syracuseStep 5767787 = 8651681) B8651681
theorem B5128811 : Blo 1518456 5128811 := bstep (se 1 (by rfl) ⟨3846608, by rfl⟩ : syracuseStep 5128811 = 7693217) B7693217
theorem B49963655 : Blo 1518456 49963655 := bstep (se 1 (by rfl) ⟨37472741, by rfl⟩ : syracuseStep 49963655 = 74945483) B74945483
theorem B2564905 : Blo 1518456 2564905 := bstep (se 2 (by rfl) ⟨961839, by rfl⟩ : syracuseStep 2564905 = 1923679) B1923679
theorem B1581935 : Blo 1518456 1581935 := bstep (se 1 (by rfl) ⟨1186451, by rfl⟩ : syracuseStep 1581935 = 2372903) B2372903
theorem B14607215 : Blo 1518456 14607215 := bstep (se 1 (by rfl) ⟨10955411, by rfl⟩ : syracuseStep 14607215 = 21910823) B21910823
theorem B2565175 : Blo 1518456 2565175 := bstep (se 1 (by rfl) ⟨1923881, by rfl⟩ : syracuseStep 2565175 = 3847763) B3847763
theorem B2278463 : Blo 1518456 2278463 := bstep (se 1 (by rfl) ⟨1708847, by rfl⟩ : syracuseStep 2278463 = 3417695) B3417695
theorem B2163775 : Blo 1518456 2163775 := bstep (se 1 (by rfl) ⟨1622831, by rfl⟩ : syracuseStep 2163775 = 3245663) B3245663
theorem B2278505 : Blo 1518456 2278505 := bstep (se 2 (by rfl) ⟨854439, by rfl⟩ : syracuseStep 2278505 = 1708879) B1708879
theorem B118441109 : Blo 1518456 118441109 := bstep (se 6 (by rfl) ⟨2775963, by rfl⟩ : syracuseStep 118441109 = 5551927) B5551927
theorem B5129405 : Blo 1518456 5129405 := bstep (se 3 (by rfl) ⟨961763, by rfl⟩ : syracuseStep 5129405 = 1923527) B1923527
theorem B2278607 : Blo 1518456 2278607 := bstep (se 1 (by rfl) ⟨1708955, by rfl⟩ : syracuseStep 2278607 = 3417911) B3417911
theorem B2278811 : Blo 1518456 2278811 := bstep (se 1 (by rfl) ⟨1709108, by rfl⟩ : syracuseStep 2278811 = 3418217) B3418217
theorem B3417515 : Blo 1518456 3417515 := bstep (se 1 (by rfl) ⟨2563136, by rfl⟩ : syracuseStep 3417515 = 5126273) B5126273
theorem B6931993 : Blo 1518456 6931993 := bstep (se 2 (by rfl) ⟨2599497, by rfl⟩ : syracuseStep 6931993 = 5198995) B5198995
theorem B2279033 : Blo 1518456 2279033 := bstep (se 2 (by rfl) ⟨854637, by rfl⟩ : syracuseStep 2279033 = 1709275) B1709275
theorem B18491003 : Blo 1518456 18491003 := bstep (se 1 (by rfl) ⟨13868252, by rfl⟩ : syracuseStep 18491003 = 27736505) B27736505
theorem B3417767 : Blo 1518456 3417767 := bstep (se 1 (by rfl) ⟨2563325, by rfl⟩ : syracuseStep 3417767 = 5126651) B5126651
theorem B5768927 : Blo 1518456 5768927 := bstep (se 1 (by rfl) ⟨4326695, by rfl⟩ : syracuseStep 5768927 = 8653391) B8653391
theorem B2279135 : Blo 1518456 2279135 := bstep (se 1 (by rfl) ⟨1709351, by rfl⟩ : syracuseStep 2279135 = 3418703) B3418703
theorem B2279231 : Blo 1518456 2279231 := bstep (se 1 (by rfl) ⟨1709423, by rfl⟩ : syracuseStep 2279231 = 3418847) B3418847
theorem B2885473 : Blo 1518456 2885473 := bstep (se 2 (by rfl) ⟨1082052, by rfl⟩ : syracuseStep 2885473 = 2164105) B2164105
theorem B3418055 : Blo 1518456 3418055 := bstep (se 1 (by rfl) ⟨2563541, by rfl⟩ : syracuseStep 3418055 = 5127083) B5127083
theorem B2279399 : Blo 1518456 2279399 := bstep (se 1 (by rfl) ⟨1709549, by rfl⟩ : syracuseStep 2279399 = 3419099) B3419099
theorem B2279417 : Blo 1518456 2279417 := bstep (se 2 (by rfl) ⟨854781, by rfl⟩ : syracuseStep 2279417 = 1709563) B1709563
theorem B2279519 : Blo 1518456 2279519 := bstep (se 1 (by rfl) ⟨1709639, by rfl⟩ : syracuseStep 2279519 = 3419279) B3419279
theorem B2279579 : Blo 1518456 2279579 := bstep (se 1 (by rfl) ⟨1709684, by rfl⟩ : syracuseStep 2279579 = 3419369) B3419369
theorem B2279615 : Blo 1518456 2279615 := bstep (se 1 (by rfl) ⟨1709711, by rfl⟩ : syracuseStep 2279615 = 3419423) B3419423
theorem B5130431 : Blo 1518456 5130431 := bstep (se 1 (by rfl) ⟨3847823, by rfl⟩ : syracuseStep 5130431 = 7695647) B7695647
theorem B5769427 : Blo 1518456 5769427 := bstep (se 1 (by rfl) ⟨4327070, by rfl⟩ : syracuseStep 5769427 = 8654141) B8654141
theorem B2279657 : Blo 1518456 2279657 := bstep (se 2 (by rfl) ⟨854871, by rfl⟩ : syracuseStep 2279657 = 1709743) B1709743
theorem B3844331 : Blo 1518456 3844331 := bstep (se 1 (by rfl) ⟨2883248, by rfl⟩ : syracuseStep 3844331 = 5766497) B5766497
theorem B3418361 : Blo 1518456 3418361 := bstep (se 2 (by rfl) ⟨1281885, by rfl⟩ : syracuseStep 3418361 = 2563771) B2563771
theorem B3418415 : Blo 1518456 3418415 := bstep (se 1 (by rfl) ⟨2563811, by rfl⟩ : syracuseStep 3418415 = 5127623) B5127623
theorem B16427447 : Blo 1518456 16427447 := bstep (se 1 (by rfl) ⟨12320585, by rfl⟩ : syracuseStep 16427447 = 24641171) B24641171
theorem B3418631 : Blo 1518456 3418631 := bstep (se 1 (by rfl) ⟨2563973, by rfl⟩ : syracuseStep 3418631 = 5127947) B5127947
theorem B2279963 : Blo 1518456 2279963 := bstep (se 1 (by rfl) ⟨1709972, by rfl⟩ : syracuseStep 2279963 = 3419945) B3419945
theorem B2280041 : Blo 1518456 2280041 := bstep (se 2 (by rfl) ⟨855015, by rfl⟩ : syracuseStep 2280041 = 1710031) B1710031
theorem B5769899 : Blo 1518456 5769899 := bstep (se 1 (by rfl) ⟨4327424, by rfl⟩ : syracuseStep 5769899 = 8654849) B8654849
theorem B3418811 : Blo 1518456 3418811 := bstep (se 1 (by rfl) ⟨2564108, by rfl⟩ : syracuseStep 3418811 = 5128217) B5128217
theorem B17296253 : Blo 1518456 17296253 := bstep (se 3 (by rfl) ⟨3243047, by rfl⟩ : syracuseStep 17296253 = 6486095) B6486095
theorem B1518495 : Blo 1518456 1518495 := bstep (se 1 (by rfl) ⟨1138871, by rfl⟩ : syracuseStep 1518495 = 2277743) B2277743
theorem B9243553 : Blo 1518456 9243553 := bstep (se 2 (by rfl) ⟨3466332, by rfl⟩ : syracuseStep 9243553 = 6932665) B6932665
theorem B7695323 : Blo 1518456 7695323 := bstep (se 1 (by rfl) ⟨5771492, by rfl⟩ : syracuseStep 7695323 = 11542985) B11542985
theorem B1518639 : Blo 1518456 1518639 := bstep (se 1 (by rfl) ⟨1138979, by rfl⟩ : syracuseStep 1518639 = 2277959) B2277959
theorem B1518663 : Blo 1518456 1518663 := bstep (se 1 (by rfl) ⟨1138997, by rfl⟩ : syracuseStep 1518663 = 2277995) B2277995
theorem B2280569 : Blo 1518456 2280569 := bstep (se 2 (by rfl) ⟨855213, by rfl⟩ : syracuseStep 2280569 = 1710427) B1710427
theorem B5475527 : Blo 1518456 5475527 := bstep (se 1 (by rfl) ⟨4106645, by rfl⟩ : syracuseStep 5475527 = 8213291) B8213291
theorem B1518815 : Blo 1518456 1518815 := bstep (se 1 (by rfl) ⟨1139111, by rfl⟩ : syracuseStep 1518815 = 2278223) B2278223
theorem B2280671 : Blo 1518456 2280671 := bstep (se 1 (by rfl) ⟨1710503, by rfl⟩ : syracuseStep 2280671 = 3421007) B3421007
theorem B41561387 : Blo 1518456 41561387 := bstep (se 1 (by rfl) ⟨31171040, by rfl⟩ : syracuseStep 41561387 = 62342081) B62342081
theorem B8777069 : Blo 1518456 8777069 := bstep (se 3 (by rfl) ⟨1645700, by rfl⟩ : syracuseStep 8777069 = 3291401) B3291401
theorem B7687547 : Blo 1518456 7687547 := bstep (se 1 (by rfl) ⟨5765660, by rfl⟩ : syracuseStep 7687547 = 11531321) B11531321
theorem B4328893 : Blo 1518456 4328893 := bstep (se 3 (by rfl) ⟨811667, by rfl⟩ : syracuseStep 4328893 = 1623335) B1623335
theorem B1519079 : Blo 1518456 1519079 := bstep (se 1 (by rfl) ⟨1139309, by rfl⟩ : syracuseStep 1519079 = 2278619) B2278619
theorem B3419639 : Blo 1518456 3419639 := bstep (se 1 (by rfl) ⟨2564729, by rfl⟩ : syracuseStep 3419639 = 5129459) B5129459
theorem B3845627 : Blo 1518456 3845627 := bstep (se 1 (by rfl) ⟨2884220, by rfl⟩ : syracuseStep 3845627 = 5768441) B5768441
theorem B3419711 : Blo 1518456 3419711 := bstep (se 1 (by rfl) ⟨2564783, by rfl⟩ : syracuseStep 3419711 = 5129567) B5129567
theorem B1519195 : Blo 1518456 1519195 := bstep (se 1 (by rfl) ⟨1139396, by rfl⟩ : syracuseStep 1519195 = 2278793) B2278793
theorem B1519431 : Blo 1518456 1519431 := bstep (se 1 (by rfl) ⟨1139573, by rfl⟩ : syracuseStep 1519431 = 2279147) B2279147
theorem B19468127 : Blo 1518456 19468127 := bstep (se 1 (by rfl) ⟨14601095, by rfl⟩ : syracuseStep 19468127 = 29202191) B29202191
theorem B27709289 : Blo 1518456 27709289 := bstep (se 2 (by rfl) ⟨10390983, by rfl⟩ : syracuseStep 27709289 = 20781967) B20781967
theorem B1519583 : Blo 1518456 1519583 := bstep (se 1 (by rfl) ⟨1139687, by rfl⟩ : syracuseStep 1519583 = 2279375) B2279375
theorem B83136617 : Blo 1518456 83136617 := bstep (se 2 (by rfl) ⟨31176231, by rfl⟩ : syracuseStep 83136617 = 62352463) B62352463
theorem B18477179 : Blo 1518456 18477179 := bstep (se 1 (by rfl) ⟨13857884, by rfl⟩ : syracuseStep 18477179 = 27715769) B27715769
theorem B5476481 : Blo 1518456 5476481 := bstep (se 2 (by rfl) ⟨2053680, by rfl⟩ : syracuseStep 5476481 = 4107361) B4107361
theorem B1519847 : Blo 1518456 1519847 := bstep (se 1 (by rfl) ⟨1139885, by rfl⟩ : syracuseStep 1519847 = 2279771) B2279771
theorem B6934781 : Blo 1518456 6934781 := bstep (se 3 (by rfl) ⟨1300271, by rfl⟩ : syracuseStep 6934781 = 2600543) B2600543
theorem B4329737 : Blo 1518456 4329737 := bstep (se 2 (by rfl) ⟨1623651, by rfl⟩ : syracuseStep 4329737 = 3247303) B3247303
theorem B1519999 : Blo 1518456 1519999 := bstep (se 1 (by rfl) ⟨1139999, by rfl⟩ : syracuseStep 1519999 = 2279999) B2279999
theorem B1520079 : Blo 1518456 1520079 := bstep (se 1 (by rfl) ⟨1140059, by rfl⟩ : syracuseStep 1520079 = 2280119) B2280119
theorem B2191865 : Blo 1518456 2191865 := bstep (se 2 (by rfl) ⟨821949, by rfl⟩ : syracuseStep 2191865 = 1643899) B1643899
theorem B3846649 : Blo 1518456 3846649 := bstep (se 2 (by rfl) ⟨1442493, by rfl⟩ : syracuseStep 3846649 = 2884987) B2884987
theorem B3420665 : Blo 1518456 3420665 := bstep (se 2 (by rfl) ⟨1282749, by rfl⟩ : syracuseStep 3420665 = 2565499) B2565499
theorem B32846417 : Blo 1518456 32846417 := bstep (se 2 (by rfl) ⟨12317406, by rfl⟩ : syracuseStep 32846417 = 24634813) B24634813
theorem B3420755 : Blo 1518456 3420755 := bstep (se 1 (by rfl) ⟨2565566, by rfl⟩ : syracuseStep 3420755 = 5131133) B5131133
theorem B4108895 : Blo 1518456 4108895 := bstep (se 1 (by rfl) ⟨3081671, by rfl⟩ : syracuseStep 4108895 = 6163343) B6163343
theorem B4936295 : Blo 1518456 4936295 := bstep (se 1 (by rfl) ⟨3702221, by rfl⟩ : syracuseStep 4936295 = 7404443) B7404443
theorem B1520231 : Blo 1518456 1520231 := bstep (se 1 (by rfl) ⟨1140173, by rfl⟩ : syracuseStep 1520231 = 2280347) B2280347
theorem B6583031 : Blo 1518456 6583031 := bstep (se 1 (by rfl) ⟨4937273, by rfl⟩ : syracuseStep 6583031 = 9874547) B9874547
theorem B3420935 : Blo 1518456 3420935 := bstep (se 1 (by rfl) ⟨2565701, by rfl⟩ : syracuseStep 3420935 = 5131403) B5131403
theorem B3846953 : Blo 1518456 3846953 := bstep (se 2 (by rfl) ⟨1442607, by rfl⟩ : syracuseStep 3846953 = 2885215) B2885215
theorem B5772161 : Blo 1518456 5772161 := bstep (se 2 (by rfl) ⟨2164560, by rfl⟩ : syracuseStep 5772161 = 4329121) B4329121
theorem B5772343 : Blo 1518456 5772343 := bstep (se 1 (by rfl) ⟨4329257, by rfl⟩ : syracuseStep 5772343 = 8658515) B8658515
theorem B5125193 : Blo 1518456 5125193 := bstep (se 2 (by rfl) ⟨1921947, by rfl⟩ : syracuseStep 5125193 = 3843895) B3843895
theorem B11097431 : Blo 1518456 11097431 := bstep (se 1 (by rfl) ⟨8323073, by rfl⟩ : syracuseStep 11097431 = 16646147) B16646147
theorem B10958203 : Blo 1518456 10958203 := bstep (se 1 (by rfl) ⟨8218652, by rfl⟩ : syracuseStep 10958203 = 16437305) B16437305
theorem B1644143 : Blo 1518456 1644143 := bstep (se 1 (by rfl) ⟨1233107, by rfl⟩ : syracuseStep 1644143 = 2466215) B2466215
theorem B21362411 : Blo 1518456 21362411 := bstep (se 1 (by rfl) ⟨16021808, by rfl⟩ : syracuseStep 21362411 = 32043617) B32043617
theorem B21067553 : Blo 1518456 21067553 := bstep (se 2 (by rfl) ⟨7900332, by rfl⟩ : syracuseStep 21067553 = 15800665) B15800665
theorem B1922879 : Blo 1518456 1922879 := bstep (se 1 (by rfl) ⟨1442159, by rfl⟩ : syracuseStep 1922879 = 2884319) B2884319
theorem B1709887 : Blo 1518456 1709887 := bstep (se 1 (by rfl) ⟨1282415, by rfl⟩ : syracuseStep 1709887 = 2564831) B2564831
theorem B20781137 : Blo 1518456 20781137 := bstep (se 2 (by rfl) ⟨7792926, by rfl⟩ : syracuseStep 20781137 = 15585853) B15585853
theorem B7305299 : Blo 1518456 7305299 := bstep (se 1 (by rfl) ⟨5478974, by rfl⟩ : syracuseStep 7305299 = 10957949) B10957949
theorem B1710175 : Blo 1518456 1710175 := bstep (se 1 (by rfl) ⟨1282631, by rfl⟩ : syracuseStep 1710175 = 2565263) B2565263
theorem B9730145 : Blo 1518456 9730145 := bstep (se 2 (by rfl) ⟨3648804, by rfl⟩ : syracuseStep 9730145 = 7297609) B7297609
theorem B8657057 : Blo 1518456 8657057 := bstep (se 2 (by rfl) ⟨3246396, by rfl⟩ : syracuseStep 8657057 = 6492793) B6492793
theorem B8771827 : Blo 1518456 8771827 := bstep (se 1 (by rfl) ⟨6578870, by rfl⟩ : syracuseStep 8771827 = 13157741) B13157741
theorem B21911795 : Blo 1518456 21911795 := bstep (se 1 (by rfl) ⟨16433846, by rfl⟩ : syracuseStep 21911795 = 32867693) B32867693
theorem B1849883 : Blo 1518456 1849883 := bstep (se 1 (by rfl) ⟨1387412, by rfl⟩ : syracuseStep 1849883 = 2774825) B2774825
theorem B11541041 : Blo 1518456 11541041 := bstep (se 2 (by rfl) ⟨4327890, by rfl⟩ : syracuseStep 11541041 = 8655781) B8655781
theorem B5126813 : Blo 1518456 5126813 := bstep (se 3 (by rfl) ⟨961277, by rfl⟩ : syracuseStep 5126813 = 1922555) B1922555
theorem B9730783 : Blo 1518456 9730783 := bstep (se 1 (by rfl) ⟨7298087, by rfl⟩ : syracuseStep 9730783 = 14596175) B14596175
theorem B2562907 : Blo 1518456 2562907 := bstep (se 1 (by rfl) ⟨1922180, by rfl⟩ : syracuseStep 2562907 = 3844361) B3844361
theorem B29621123 : Blo 1518456 29621123 := bstep (se 1 (by rfl) ⟨22215842, by rfl⟩ : syracuseStep 29621123 = 44431685) B44431685
theorem B11533265 : Blo 1518456 11533265 := bstep (se 2 (by rfl) ⟨4324974, by rfl⟩ : syracuseStep 11533265 = 8649949) B8649949
theorem B5127137 : Blo 1518456 5127137 := bstep (se 2 (by rfl) ⟨1922676, by rfl⟩ : syracuseStep 5127137 = 3845353) B3845353
theorem B8649767 : Blo 1518456 8649767 := bstep (se 1 (by rfl) ⟨6487325, by rfl⟩ : syracuseStep 8649767 = 12974651) B12974651
theorem B5127353 : Blo 1518456 5127353 := bstep (se 2 (by rfl) ⟨1922757, by rfl⟩ : syracuseStep 5127353 = 3845515) B3845515
theorem B4324747 : Blo 1518456 4324747 := bstep (se 1 (by rfl) ⟨3243560, by rfl⟩ : syracuseStep 4324747 = 6487121) B6487121
theorem B2162089 : Blo 1518456 2162089 := bstep (se 2 (by rfl) ⟨810783, by rfl⟩ : syracuseStep 2162089 = 1621567) B1621567
theorem B4325089 : Blo 1518456 4325089 := bstep (se 2 (by rfl) ⟨1621908, by rfl⟩ : syracuseStep 4325089 = 3243817) B3243817
theorem B49315553 : Blo 1518456 49315553 := bstep (se 2 (by rfl) ⟨18493332, by rfl⟩ : syracuseStep 49315553 = 36986665) B36986665
theorem B7298839 : Blo 1518456 7298839 := bstep (se 1 (by rfl) ⟨5474129, by rfl⟩ : syracuseStep 7298839 = 10948259) B10948259
theorem B2563879 : Blo 1518456 2563879 := bstep (se 1 (by rfl) ⟨1922909, by rfl⟩ : syracuseStep 2563879 = 3845819) B3845819
theorem B1621883 : Blo 1518456 1621883 := bstep (se 1 (by rfl) ⟨1216412, by rfl⟩ : syracuseStep 1621883 = 2432825) B2432825
theorem B23396509 : Blo 1518456 23396509 := bstep (se 3 (by rfl) ⟨4386845, by rfl⟩ : syracuseStep 23396509 = 8773691) B8773691
theorem B17318123 : Blo 1518456 17318123 := bstep (se 1 (by rfl) ⟨12988592, by rfl⟩ : syracuseStep 17318123 = 25977185) B25977185
theorem B7692569 : Blo 1518456 7692569 := bstep (se 2 (by rfl) ⟨2884713, by rfl⟩ : syracuseStep 7692569 = 5769427) B5769427
theorem B5128487 : Blo 1518456 5128487 := bstep (se 1 (by rfl) ⟨3846365, by rfl⟩ : syracuseStep 5128487 = 7692731) B7692731
theorem B21897611 : Blo 1518456 21897611 := bstep (se 1 (by rfl) ⟨16423208, by rfl⟩ : syracuseStep 21897611 = 32846417) B32846417
theorem B33309103 : Blo 1518456 33309103 := bstep (se 1 (by rfl) ⟨24981827, by rfl⟩ : syracuseStep 33309103 = 49963655) B49963655
theorem B2564635 : Blo 1518456 2564635 := bstep (se 1 (by rfl) ⟨1923476, by rfl⟩ : syracuseStep 2564635 = 3846953) B3846953
theorem B5128865 : Blo 1518456 5128865 := bstep (se 2 (by rfl) ⟨1923324, by rfl⟩ : syracuseStep 5128865 = 3846649) B3846649
theorem B3416795 : Blo 1518456 3416795 := bstep (se 1 (by rfl) ⟨2562596, by rfl⟩ : syracuseStep 3416795 = 5125193) B5125193
theorem B7398287 : Blo 1518456 7398287 := bstep (se 1 (by rfl) ⟨5548715, by rfl⟩ : syracuseStep 7398287 = 11097431) B11097431
theorem B2278343 : Blo 1518456 2278343 := bstep (se 1 (by rfl) ⟨1708757, by rfl⟩ : syracuseStep 2278343 = 3417515) B3417515
theorem B2278511 : Blo 1518456 2278511 := bstep (se 1 (by rfl) ⟨1708883, by rfl⟩ : syracuseStep 2278511 = 3417767) B3417767
theorem B3417209 : Blo 1518456 3417209 := bstep (se 2 (by rfl) ⟨1281453, by rfl⟩ : syracuseStep 3417209 = 2562907) B2562907
theorem B8651933 : Blo 1518456 8651933 := bstep (se 3 (by rfl) ⟨1622237, by rfl⟩ : syracuseStep 8651933 = 3244475) B3244475
theorem B2278703 : Blo 1518456 2278703 := bstep (se 1 (by rfl) ⟨1709027, by rfl⟩ : syracuseStep 2278703 = 3418055) B3418055
theorem B13854091 : Blo 1518456 13854091 := bstep (se 1 (by rfl) ⟨10390568, by rfl⟩ : syracuseStep 13854091 = 20781137) B20781137
theorem B2885033 : Blo 1518456 2885033 := bstep (se 2 (by rfl) ⟨1081887, by rfl⟩ : syracuseStep 2885033 = 2163775) B2163775
theorem B14607863 : Blo 1518456 14607863 := bstep (se 1 (by rfl) ⟨10955897, by rfl⟩ : syracuseStep 14607863 = 21911795) B21911795
theorem B2278907 : Blo 1518456 2278907 := bstep (se 1 (by rfl) ⟨1709180, by rfl⟩ : syracuseStep 2278907 = 3418361) B3418361
theorem B2278943 : Blo 1518456 2278943 := bstep (se 1 (by rfl) ⟨1709207, by rfl⟩ : syracuseStep 2278943 = 3418415) B3418415
theorem B4384381 : Blo 1518456 4384381 := bstep (se 3 (by rfl) ⟨822071, by rfl⟩ : syracuseStep 4384381 = 1644143) B1644143
theorem B2279087 : Blo 1518456 2279087 := bstep (se 1 (by rfl) ⟨1709315, by rfl⟩ : syracuseStep 2279087 = 3418631) B3418631
theorem B7694027 : Blo 1518456 7694027 := bstep (se 1 (by rfl) ⟨5770520, by rfl⟩ : syracuseStep 7694027 = 11541041) B11541041
theorem B3417875 : Blo 1518456 3417875 := bstep (se 1 (by rfl) ⟨2563406, by rfl⟩ : syracuseStep 3417875 = 5126813) B5126813
theorem B2279207 : Blo 1518456 2279207 := bstep (se 1 (by rfl) ⟨1709405, by rfl⟩ : syracuseStep 2279207 = 3418811) B3418811
theorem B5130215 : Blo 1518456 5130215 := bstep (se 1 (by rfl) ⟨3847661, by rfl⟩ : syracuseStep 5130215 = 7695323) B7695323
theorem B3418091 : Blo 1518456 3418091 := bstep (se 1 (by rfl) ⟨2563568, by rfl⟩ : syracuseStep 3418091 = 5127137) B5127137
theorem B9242657 : Blo 1518456 9242657 := bstep (se 2 (by rfl) ⟨3465996, by rfl⟩ : syracuseStep 9242657 = 6931993) B6931993
theorem B3418235 : Blo 1518456 3418235 := bstep (se 1 (by rfl) ⟨2563676, by rfl⟩ : syracuseStep 3418235 = 5127353) B5127353
theorem B27707591 : Blo 1518456 27707591 := bstep (se 1 (by rfl) ⟨20780693, by rfl⟩ : syracuseStep 27707591 = 41561387) B41561387
theorem B5851379 : Blo 1518456 5851379 := bstep (se 1 (by rfl) ⟨4388534, by rfl⟩ : syracuseStep 5851379 = 8777069) B8777069
theorem B2279759 : Blo 1518456 2279759 := bstep (se 1 (by rfl) ⟨1709819, by rfl⟩ : syracuseStep 2279759 = 3419639) B3419639
theorem B2279807 : Blo 1518456 2279807 := bstep (se 1 (by rfl) ⟨1709855, by rfl⟩ : syracuseStep 2279807 = 3419711) B3419711
theorem B3418505 : Blo 1518456 3418505 := bstep (se 2 (by rfl) ⟨1281939, by rfl⟩ : syracuseStep 3418505 = 2563879) B2563879
theorem B2279849 : Blo 1518456 2279849 := bstep (se 2 (by rfl) ⟨854943, by rfl⟩ : syracuseStep 2279849 = 1709887) B1709887
theorem B32877035 : Blo 1518456 32877035 := bstep (se 1 (by rfl) ⟨24657776, by rfl⟩ : syracuseStep 32877035 = 49315553) B49315553
theorem B12978751 : Blo 1518456 12978751 := bstep (se 1 (by rfl) ⟨9734063, by rfl⟩ : syracuseStep 12978751 = 19468127) B19468127
theorem B2280233 : Blo 1518456 2280233 := bstep (se 2 (by rfl) ⟨855087, by rfl⟩ : syracuseStep 2280233 = 1710175) B1710175
theorem B2886491 : Blo 1518456 2886491 := bstep (se 1 (by rfl) ⟨2164868, by rfl⟩ : syracuseStep 2886491 = 4329737) B4329737
theorem B1518559 : Blo 1518456 1518559 := bstep (se 1 (by rfl) ⟨1138919, by rfl⟩ : syracuseStep 1518559 = 2277839) B2277839
theorem B1518587 : Blo 1518456 1518587 := bstep (se 1 (by rfl) ⟨1138940, by rfl⟩ : syracuseStep 1518587 = 2277881) B2277881
theorem B2280443 : Blo 1518456 2280443 := bstep (se 1 (by rfl) ⟨1710332, by rfl⟩ : syracuseStep 2280443 = 3420665) B3420665
theorem B2280503 : Blo 1518456 2280503 := bstep (se 1 (by rfl) ⟨1710377, by rfl⟩ : syracuseStep 2280503 = 3420755) B3420755
theorem B1518655 : Blo 1518456 1518655 := bstep (se 1 (by rfl) ⟨1138991, by rfl⟩ : syracuseStep 1518655 = 2277983) B2277983
theorem B2739263 : Blo 1518456 2739263 := bstep (se 1 (by rfl) ⟨2054447, by rfl⟩ : syracuseStep 2739263 = 4108895) B4108895
theorem B3845191 : Blo 1518456 3845191 := bstep (se 1 (by rfl) ⟨2883893, by rfl⟩ : syracuseStep 3845191 = 5767787) B5767787
theorem B3419207 : Blo 1518456 3419207 := bstep (se 1 (by rfl) ⟨2564405, by rfl⟩ : syracuseStep 3419207 = 5128811) B5128811
theorem B2280623 : Blo 1518456 2280623 := bstep (se 1 (by rfl) ⟨1710467, by rfl⟩ : syracuseStep 2280623 = 3420935) B3420935
theorem B18492749 : Blo 1518456 18492749 := bstep (se 3 (by rfl) ⟨3467390, by rfl⟩ : syracuseStep 18492749 = 6934781) B6934781
theorem B1518975 : Blo 1518456 1518975 := bstep (se 1 (by rfl) ⟨1139231, by rfl⟩ : syracuseStep 1518975 = 2278463) B2278463
theorem B1519003 : Blo 1518456 1519003 := bstep (se 1 (by rfl) ⟨1139252, by rfl⟩ : syracuseStep 1519003 = 2278505) B2278505
theorem B3419603 : Blo 1518456 3419603 := bstep (se 1 (by rfl) ⟨2564702, by rfl⟩ : syracuseStep 3419603 = 5129405) B5129405
theorem B1519071 : Blo 1518456 1519071 := bstep (se 1 (by rfl) ⟨1139303, by rfl⟩ : syracuseStep 1519071 = 2278607) B2278607
theorem B1519207 : Blo 1518456 1519207 := bstep (se 1 (by rfl) ⟨1139405, by rfl⟩ : syracuseStep 1519207 = 2278811) B2278811
theorem B3419873 : Blo 1518456 3419873 := bstep (se 2 (by rfl) ⟨1282452, by rfl⟩ : syracuseStep 3419873 = 2564905) B2564905
theorem B1519355 : Blo 1518456 1519355 := bstep (se 1 (by rfl) ⟨1139516, by rfl⟩ : syracuseStep 1519355 = 2279033) B2279033
theorem B3845951 : Blo 1518456 3845951 := bstep (se 1 (by rfl) ⟨2884463, by rfl⟩ : syracuseStep 3845951 = 5768927) B5768927
theorem B1519423 : Blo 1518456 1519423 := bstep (se 1 (by rfl) ⟨1139567, by rfl⟩ : syracuseStep 1519423 = 2279135) B2279135
theorem B14045035 : Blo 1518456 14045035 := bstep (se 1 (by rfl) ⟨10533776, by rfl⟩ : syracuseStep 14045035 = 21067553) B21067553
theorem B1519487 : Blo 1518456 1519487 := bstep (se 1 (by rfl) ⟨1139615, by rfl⟩ : syracuseStep 1519487 = 2279231) B2279231
theorem B12324737 : Blo 1518456 12324737 := bstep (se 2 (by rfl) ⟨4621776, by rfl⟩ : syracuseStep 12324737 = 9243553) B9243553
theorem B5844973 : Blo 1518456 5844973 := bstep (se 3 (by rfl) ⟨1095932, by rfl⟩ : syracuseStep 5844973 = 2191865) B2191865
theorem B1519599 : Blo 1518456 1519599 := bstep (se 1 (by rfl) ⟨1139699, by rfl⟩ : syracuseStep 1519599 = 2279399) B2279399
theorem B1519611 : Blo 1518456 1519611 := bstep (se 1 (by rfl) ⟨1139708, by rfl⟩ : syracuseStep 1519611 = 2279417) B2279417
theorem B4870199 : Blo 1518456 4870199 := bstep (se 1 (by rfl) ⟨3652649, by rfl⟩ : syracuseStep 4870199 = 7305299) B7305299
theorem B1519679 : Blo 1518456 1519679 := bstep (se 1 (by rfl) ⟨1139759, by rfl⟩ : syracuseStep 1519679 = 2279519) B2279519
theorem B3420233 : Blo 1518456 3420233 := bstep (se 2 (by rfl) ⟨1282587, by rfl⟩ : syracuseStep 3420233 = 2565175) B2565175
theorem B7696457 : Blo 1518456 7696457 := bstep (se 2 (by rfl) ⟨2886171, by rfl⟩ : syracuseStep 7696457 = 5772343) B5772343
theorem B1519719 : Blo 1518456 1519719 := bstep (se 1 (by rfl) ⟨1139789, by rfl⟩ : syracuseStep 1519719 = 2279579) B2279579
theorem B5771371 : Blo 1518456 5771371 := bstep (se 1 (by rfl) ⟨4328528, by rfl⟩ : syracuseStep 5771371 = 8657057) B8657057
theorem B1519743 : Blo 1518456 1519743 := bstep (se 1 (by rfl) ⟨1139807, by rfl⟩ : syracuseStep 1519743 = 2279615) B2279615
theorem B3420287 : Blo 1518456 3420287 := bstep (se 1 (by rfl) ⟨2565215, by rfl⟩ : syracuseStep 3420287 = 5130431) B5130431
theorem B1519771 : Blo 1518456 1519771 := bstep (se 1 (by rfl) ⟨1139828, by rfl⟩ : syracuseStep 1519771 = 2279657) B2279657
theorem B1519975 : Blo 1518456 1519975 := bstep (se 1 (by rfl) ⟨1139981, by rfl⟩ : syracuseStep 1519975 = 2279963) B2279963
theorem B1520027 : Blo 1518456 1520027 := bstep (se 1 (by rfl) ⟨1140020, by rfl⟩ : syracuseStep 1520027 = 2280041) B2280041
theorem B3846599 : Blo 1518456 3846599 := bstep (se 1 (by rfl) ⟨2884949, by rfl⟩ : syracuseStep 3846599 = 5769899) B5769899
theorem B14610937 : Blo 1518456 14610937 := bstep (se 2 (by rfl) ⟨5479101, by rfl⟩ : syracuseStep 14610937 = 10958203) B10958203
theorem B5771857 : Blo 1518456 5771857 := bstep (se 2 (by rfl) ⟨2164446, by rfl⟩ : syracuseStep 5771857 = 4328893) B4328893
theorem B11530835 : Blo 1518456 11530835 := bstep (se 1 (by rfl) ⟨8648126, by rfl⟩ : syracuseStep 11530835 = 17296253) B17296253
theorem B19747415 : Blo 1518456 19747415 := bstep (se 1 (by rfl) ⟨14810561, by rfl⟩ : syracuseStep 19747415 = 29621123) B29621123
theorem B7688843 : Blo 1518456 7688843 := bstep (se 1 (by rfl) ⟨5766632, by rfl⟩ : syracuseStep 7688843 = 11533265) B11533265
theorem B1520379 : Blo 1518456 1520379 := bstep (se 1 (by rfl) ⟨1140284, by rfl⟩ : syracuseStep 1520379 = 2280569) B2280569
theorem B3650351 : Blo 1518456 3650351 := bstep (se 1 (by rfl) ⟨2737763, by rfl⟩ : syracuseStep 3650351 = 5475527) B5475527
theorem B1520447 : Blo 1518456 1520447 := bstep (se 1 (by rfl) ⟨1140335, by rfl⟩ : syracuseStep 1520447 = 2280671) B2280671
theorem B5125031 : Blo 1518456 5125031 := bstep (se 1 (by rfl) ⟨3843773, by rfl⟩ : syracuseStep 5125031 = 7687547) B7687547
theorem B3847297 : Blo 1518456 3847297 := bstep (se 2 (by rfl) ⟨1442736, by rfl⟩ : syracuseStep 3847297 = 2885473) B2885473
theorem B55424411 : Blo 1518456 55424411 := bstep (se 1 (by rfl) ⟨41568308, by rfl⟩ : syracuseStep 55424411 = 83136617) B83136617
theorem B12318119 : Blo 1518456 12318119 := bstep (se 1 (by rfl) ⟨9238589, by rfl⟩ : syracuseStep 12318119 = 18477179) B18477179
theorem B3650987 : Blo 1518456 3650987 := bstep (se 1 (by rfl) ⟨2738240, by rfl⟩ : syracuseStep 3650987 = 5476481) B5476481
theorem B19732085 : Blo 1518456 19732085 := bstep (se 5 (by rfl) ⟨924941, by rfl⟩ : syracuseStep 19732085 = 1849883) B1849883
theorem B11695769 : Blo 1518456 11695769 := bstep (se 2 (by rfl) ⟨4385913, by rfl⟩ : syracuseStep 11695769 = 8771827) B8771827
theorem B3290863 : Blo 1518456 3290863 := bstep (se 1 (by rfl) ⟨2468147, by rfl⟩ : syracuseStep 3290863 = 4936295) B4936295
theorem B4388687 : Blo 1518456 4388687 := bstep (se 1 (by rfl) ⟨3291515, by rfl⟩ : syracuseStep 4388687 = 6583031) B6583031
theorem B9738143 : Blo 1518456 9738143 := bstep (se 1 (by rfl) ⟨7303607, by rfl⟩ : syracuseStep 9738143 = 14607215) B14607215
theorem B3848107 : Blo 1518456 3848107 := bstep (se 1 (by rfl) ⟨2886080, by rfl⟩ : syracuseStep 3848107 = 5772161) B5772161
theorem B810244133 : Blo 1518456 810244133 := bstep (se 4 (by rfl) ⟨75960387, by rfl⟩ : syracuseStep 810244133 = 151920775) B151920775
theorem B78960739 : Blo 1518456 78960739 := bstep (se 1 (by rfl) ⟨59220554, by rfl⟩ : syracuseStep 78960739 = 118441109) B118441109
theorem B12974377 : Blo 1518456 12974377 := bstep (se 2 (by rfl) ⟨4865391, by rfl⟩ : syracuseStep 12974377 = 9730783) B9730783
theorem B12327335 : Blo 1518456 12327335 := bstep (se 1 (by rfl) ⟨9245501, by rfl⟩ : syracuseStep 12327335 = 18491003) B18491003
theorem B6486763 : Blo 1518456 6486763 := bstep (se 1 (by rfl) ⟨4865072, by rfl⟩ : syracuseStep 6486763 = 9730145) B9730145
theorem B2562887 : Blo 1518456 2562887 := bstep (se 1 (by rfl) ⟨1922165, by rfl⟩ : syracuseStep 2562887 = 3844331) B3844331
theorem B10951631 : Blo 1518456 10951631 := bstep (se 1 (by rfl) ⟨8213723, by rfl⟩ : syracuseStep 10951631 = 16427447) B16427447
theorem B5766329 : Blo 1518456 5766329 := bstep (se 2 (by rfl) ⟨2162373, by rfl⟩ : syracuseStep 5766329 = 4324747) B4324747
theorem B2882785 : Blo 1518456 2882785 := bstep (se 2 (by rfl) ⟨1081044, by rfl⟩ : syracuseStep 2882785 = 2162089) B2162089
theorem B56966429 : Blo 1518456 56966429 := bstep (se 3 (by rfl) ⟨10681205, by rfl⟩ : syracuseStep 56966429 = 21362411) B21362411
theorem B5766511 : Blo 1518456 5766511 := bstep (se 1 (by rfl) ⟨4324883, by rfl⟩ : syracuseStep 5766511 = 8649767) B8649767
theorem B5127677 : Blo 1518456 5127677 := bstep (se 3 (by rfl) ⟨961439, by rfl⟩ : syracuseStep 5127677 = 1922879) B1922879
theorem B4218493 : Blo 1518456 4218493 := bstep (se 3 (by rfl) ⟨790967, by rfl⟩ : syracuseStep 4218493 = 1581935) B1581935
theorem B5766785 : Blo 1518456 5766785 := bstep (se 2 (by rfl) ⟨2162544, by rfl⟩ : syracuseStep 5766785 = 4325089) B4325089
theorem B4325021 : Blo 1518456 4325021 := bstep (se 3 (by rfl) ⟨810941, by rfl⟩ : syracuseStep 4325021 = 1621883) B1621883
theorem B2563751 : Blo 1518456 2563751 := bstep (se 1 (by rfl) ⟨1922813, by rfl⟩ : syracuseStep 2563751 = 3845627) B3845627
theorem B9731785 : Blo 1518456 9731785 := bstep (se 2 (by rfl) ⟨3649419, by rfl⟩ : syracuseStep 9731785 = 7298839) B7298839
theorem B18472859 : Blo 1518456 18472859 := bstep (se 1 (by rfl) ⟨13854644, by rfl⟩ : syracuseStep 18472859 = 27709289) B27709289
theorem B5128379 : Blo 1518456 5128379 := bstep (se 1 (by rfl) ⟨3846284, by rfl⟩ : syracuseStep 5128379 = 7692569) B7692569
theorem B14598407 : Blo 1518456 14598407 := bstep (se 1 (by rfl) ⟨10948805, by rfl⟩ : syracuseStep 14598407 = 21897611) B21897611
theorem B2564399 : Blo 1518456 2564399 := bstep (se 1 (by rfl) ⟨1923299, by rfl⟩ : syracuseStep 2564399 = 3846599) B3846599
theorem B13164943 : Blo 1518456 13164943 := bstep (se 1 (by rfl) ⟨9873707, by rfl⟩ : syracuseStep 13164943 = 19747415) B19747415
theorem B2277863 : Blo 1518456 2277863 := bstep (se 1 (by rfl) ⟨1708397, by rfl⟩ : syracuseStep 2277863 = 3416795) B3416795
theorem B4932191 : Blo 1518456 4932191 := bstep (se 1 (by rfl) ⟨3699143, by rfl⟩ : syracuseStep 4932191 = 7398287) B7398287
theorem B3416687 : Blo 1518456 3416687 := bstep (se 1 (by rfl) ⟨2562515, by rfl⟩ : syracuseStep 3416687 = 5125031) B5125031
theorem B19481249 : Blo 1518456 19481249 := bstep (se 2 (by rfl) ⟨7305468, by rfl⟩ : syracuseStep 19481249 = 14610937) B14610937
theorem B2278139 : Blo 1518456 2278139 := bstep (se 1 (by rfl) ⟨1708604, by rfl⟩ : syracuseStep 2278139 = 3417209) B3417209
theorem B5767955 : Blo 1518456 5767955 := bstep (se 1 (by rfl) ⟨4325966, by rfl⟩ : syracuseStep 5767955 = 8651933) B8651933
theorem B124781381 : Blo 1518456 124781381 := bstep (se 4 (by rfl) ⟨11698254, by rfl⟩ : syracuseStep 124781381 = 23396509) B23396509
theorem B2433991 : Blo 1518456 2433991 := bstep (se 1 (by rfl) ⟨1825493, by rfl⟩ : syracuseStep 2433991 = 3650987) B3650987
theorem B5129351 : Blo 1518456 5129351 := bstep (se 1 (by rfl) ⟨3847013, by rfl⟩ : syracuseStep 5129351 = 7694027) B7694027
theorem B2278583 : Blo 1518456 2278583 := bstep (se 1 (by rfl) ⟨1708937, by rfl⟩ : syracuseStep 2278583 = 3417875) B3417875
theorem B2925791 : Blo 1518456 2925791 := bstep (se 1 (by rfl) ⟨2194343, by rfl⟩ : syracuseStep 2925791 = 4388687) B4388687
theorem B2278727 : Blo 1518456 2278727 := bstep (se 1 (by rfl) ⟨1709045, by rfl⟩ : syracuseStep 2278727 = 3418091) B3418091
theorem B6161771 : Blo 1518456 6161771 := bstep (se 1 (by rfl) ⟨4621328, by rfl⟩ : syracuseStep 6161771 = 9242657) B9242657
theorem B2278823 : Blo 1518456 2278823 := bstep (se 1 (by rfl) ⟨1709117, by rfl⟩ : syracuseStep 2278823 = 3418235) B3418235
theorem B5129729 : Blo 1518456 5129729 := bstep (se 2 (by rfl) ⟨1923648, by rfl⟩ : syracuseStep 5129729 = 3847297) B3847297
theorem B2279003 : Blo 1518456 2279003 := bstep (se 1 (by rfl) ⟨1709252, by rfl⟩ : syracuseStep 2279003 = 3418505) B3418505
theorem B8218223 : Blo 1518456 8218223 := bstep (se 1 (by rfl) ⟨6163667, by rfl⟩ : syracuseStep 8218223 = 12327335) B12327335
theorem B3843713 : Blo 1518456 3843713 := bstep (se 2 (by rfl) ⟨1441392, by rfl⟩ : syracuseStep 3843713 = 2882785) B2882785
theorem B7301087 : Blo 1518456 7301087 := bstep (se 1 (by rfl) ⟨5475815, by rfl⟩ : syracuseStep 7301087 = 10951631) B10951631
theorem B2279471 : Blo 1518456 2279471 := bstep (se 1 (by rfl) ⟨1709603, by rfl⟩ : syracuseStep 2279471 = 3419207) B3419207
theorem B3844219 : Blo 1518456 3844219 := bstep (se 1 (by rfl) ⟨2883164, by rfl⟩ : syracuseStep 3844219 = 5766329) B5766329
theorem B9734269 : Blo 1518456 9734269 := bstep (se 3 (by rfl) ⟨1825175, by rfl⟩ : syracuseStep 9734269 = 3650351) B3650351
theorem B2279735 : Blo 1518456 2279735 := bstep (se 1 (by rfl) ⟨1709801, by rfl⟩ : syracuseStep 2279735 = 3419603) B3419603
theorem B3418451 : Blo 1518456 3418451 := bstep (se 1 (by rfl) ⟨2563838, by rfl⟩ : syracuseStep 3418451 = 5127677) B5127677
theorem B3844523 : Blo 1518456 3844523 := bstep (se 1 (by rfl) ⟨2883392, by rfl⟩ : syracuseStep 3844523 = 5766785) B5766785
theorem B2279915 : Blo 1518456 2279915 := bstep (se 1 (by rfl) ⟨1709936, by rfl⟩ : syracuseStep 2279915 = 3419873) B3419873
theorem B5130809 : Blo 1518456 5130809 := bstep (se 2 (by rfl) ⟨1924053, by rfl⟩ : syracuseStep 5130809 = 3848107) B3848107
theorem B12315239 : Blo 1518456 12315239 := bstep (se 1 (by rfl) ⟨9236429, by rfl⟩ : syracuseStep 12315239 = 18472859) B18472859
theorem B7793297 : Blo 1518456 7793297 := bstep (se 2 (by rfl) ⟨2922486, by rfl⟩ : syracuseStep 7793297 = 5844973) B5844973
theorem B3246799 : Blo 1518456 3246799 := bstep (se 1 (by rfl) ⟨2435099, by rfl⟩ : syracuseStep 3246799 = 4870199) B4870199
theorem B2280155 : Blo 1518456 2280155 := bstep (se 1 (by rfl) ⟨1710116, by rfl⟩ : syracuseStep 2280155 = 3420233) B3420233
theorem B5130971 : Blo 1518456 5130971 := bstep (se 1 (by rfl) ⟨3848228, by rfl⟩ : syracuseStep 5130971 = 7696457) B7696457
theorem B2280191 : Blo 1518456 2280191 := bstep (se 1 (by rfl) ⟨1710143, by rfl⟩ : syracuseStep 2280191 = 3420287) B3420287
theorem B7695161 : Blo 1518456 7695161 := bstep (se 2 (by rfl) ⟨2885685, by rfl⟩ : syracuseStep 7695161 = 5771371) B5771371
theorem B11545415 : Blo 1518456 11545415 := bstep (se 1 (by rfl) ⟨8659061, by rfl⟩ : syracuseStep 11545415 = 17318123) B17318123
theorem B3418991 : Blo 1518456 3418991 := bstep (se 1 (by rfl) ⟨2564243, by rfl⟩ : syracuseStep 3418991 = 5128487) B5128487
theorem B7687223 : Blo 1518456 7687223 := bstep (se 1 (by rfl) ⟨5765417, by rfl⟩ : syracuseStep 7687223 = 11530835) B11530835
theorem B3419243 : Blo 1518456 3419243 := bstep (se 1 (by rfl) ⟨2564432, by rfl⟩ : syracuseStep 3419243 = 5128865) B5128865
theorem B44412137 : Blo 1518456 44412137 := bstep (se 2 (by rfl) ⟨16654551, by rfl⟩ : syracuseStep 44412137 = 33309103) B33309103
theorem B1518895 : Blo 1518456 1518895 := bstep (se 1 (by rfl) ⟨1139171, by rfl⟩ : syracuseStep 1518895 = 2278343) B2278343
theorem B3419513 : Blo 1518456 3419513 := bstep (se 2 (by rfl) ⟨1282317, by rfl⟩ : syracuseStep 3419513 = 2564635) B2564635
theorem B1519007 : Blo 1518456 1519007 := bstep (se 1 (by rfl) ⟨1139255, by rfl⟩ : syracuseStep 1519007 = 2278511) B2278511
theorem B17305001 : Blo 1518456 17305001 := bstep (se 2 (by rfl) ⟨6489375, by rfl⟩ : syracuseStep 17305001 = 12978751) B12978751
theorem B7695809 : Blo 1518456 7695809 := bstep (se 2 (by rfl) ⟨2885928, by rfl⟩ : syracuseStep 7695809 = 5771857) B5771857
theorem B1519135 : Blo 1518456 1519135 := bstep (se 1 (by rfl) ⟨1139351, by rfl⟩ : syracuseStep 1519135 = 2278703) B2278703
theorem B36949607 : Blo 1518456 36949607 := bstep (se 1 (by rfl) ⟨27712205, by rfl⟩ : syracuseStep 36949607 = 55424411) B55424411
theorem B8212079 : Blo 1518456 8212079 := bstep (se 1 (by rfl) ⟨6159059, by rfl⟩ : syracuseStep 8212079 = 12318119) B12318119
theorem B1519271 : Blo 1518456 1519271 := bstep (se 1 (by rfl) ⟨1139453, by rfl⟩ : syracuseStep 1519271 = 2278907) B2278907
theorem B1519295 : Blo 1518456 1519295 := bstep (se 1 (by rfl) ⟨1139471, by rfl⟩ : syracuseStep 1519295 = 2278943) B2278943
theorem B1519391 : Blo 1518456 1519391 := bstep (se 1 (by rfl) ⟨1139543, by rfl⟩ : syracuseStep 1519391 = 2279087) B2279087
theorem B1519471 : Blo 1518456 1519471 := bstep (se 1 (by rfl) ⟨1139603, by rfl⟩ : syracuseStep 1519471 = 2279207) B2279207
theorem B6492095 : Blo 1518456 6492095 := bstep (se 1 (by rfl) ⟨4869071, by rfl⟩ : syracuseStep 6492095 = 9738143) B9738143
theorem B3420143 : Blo 1518456 3420143 := bstep (se 1 (by rfl) ⟨2565107, by rfl⟩ : syracuseStep 3420143 = 5130215) B5130215
theorem B1519839 : Blo 1518456 1519839 := bstep (se 1 (by rfl) ⟨1139879, by rfl⟩ : syracuseStep 1519839 = 2279759) B2279759
theorem B1519871 : Blo 1518456 1519871 := bstep (se 1 (by rfl) ⟨1139903, by rfl⟩ : syracuseStep 1519871 = 2279807) B2279807
theorem B1519899 : Blo 1518456 1519899 := bstep (se 1 (by rfl) ⟨1139924, by rfl⟩ : syracuseStep 1519899 = 2279849) B2279849
theorem B21918023 : Blo 1518456 21918023 := bstep (se 1 (by rfl) ⟨16438517, by rfl⟩ : syracuseStep 21918023 = 32877035) B32877035
theorem B7688681 : Blo 1518456 7688681 := bstep (se 2 (by rfl) ⟨2883255, by rfl⟩ : syracuseStep 7688681 = 5766511) B5766511
theorem B1520155 : Blo 1518456 1520155 := bstep (se 1 (by rfl) ⟨1140116, by rfl⟩ : syracuseStep 1520155 = 2280233) B2280233
theorem B1708591 : Blo 1518456 1708591 := bstep (se 1 (by rfl) ⟨1281443, by rfl⟩ : syracuseStep 1708591 = 2562887) B2562887
theorem B1520295 : Blo 1518456 1520295 := bstep (se 1 (by rfl) ⟨1140221, by rfl⟩ : syracuseStep 1520295 = 2280443) B2280443
theorem B1520335 : Blo 1518456 1520335 := bstep (se 1 (by rfl) ⟨1140251, by rfl⟩ : syracuseStep 1520335 = 2280503) B2280503
theorem B1520415 : Blo 1518456 1520415 := bstep (se 1 (by rfl) ⟨1140311, by rfl⟩ : syracuseStep 1520415 = 2280623) B2280623
theorem B5624657 : Blo 1518456 5624657 := bstep (se 2 (by rfl) ⟨2109246, by rfl⟩ : syracuseStep 5624657 = 4218493) B4218493
theorem B5845841 : Blo 1518456 5845841 := bstep (se 2 (by rfl) ⟨2192190, by rfl⟩ : syracuseStep 5845841 = 4384381) B4384381
theorem B4387817 : Blo 1518456 4387817 := bstep (se 2 (by rfl) ⟨1645431, by rfl⟩ : syracuseStep 4387817 = 3290863) B3290863
theorem B1709167 : Blo 1518456 1709167 := bstep (se 1 (by rfl) ⟨1281875, by rfl⟩ : syracuseStep 1709167 = 2563751) B2563751
theorem B105280985 : Blo 1518456 105280985 := bstep (se 2 (by rfl) ⟨39480369, by rfl⟩ : syracuseStep 105280985 = 78960739) B78960739
theorem B7304701 : Blo 1518456 7304701 := bstep (se 3 (by rfl) ⟨1369631, by rfl⟩ : syracuseStep 7304701 = 2739263) B2739263
theorem B17299169 : Blo 1518456 17299169 := bstep (se 2 (by rfl) ⟨6487188, by rfl⟩ : syracuseStep 17299169 = 12974377) B12974377
theorem B5125895 : Blo 1518456 5125895 := bstep (se 1 (by rfl) ⟨3844421, by rfl⟩ : syracuseStep 5125895 = 7688843) B7688843
theorem B15603677 : Blo 1518456 15603677 := bstep (se 3 (by rfl) ⟨2925689, by rfl⟩ : syracuseStep 15603677 = 5851379) B5851379
theorem B151910477 : Blo 1518456 151910477 := bstep (se 3 (by rfl) ⟨28483214, by rfl⟩ : syracuseStep 151910477 = 56966429) B56966429
theorem B1923355 : Blo 1518456 1923355 := bstep (se 1 (by rfl) ⟨1442516, by rfl⟩ : syracuseStep 1923355 = 2885033) B2885033
theorem B8649017 : Blo 1518456 8649017 := bstep (se 2 (by rfl) ⟨3243381, by rfl⟩ : syracuseStep 8649017 = 6486763) B6486763
theorem B9738575 : Blo 1518456 9738575 := bstep (se 1 (by rfl) ⟨7303931, by rfl⟩ : syracuseStep 9738575 = 14607863) B14607863
theorem B13154723 : Blo 1518456 13154723 := bstep (se 1 (by rfl) ⟨9866042, by rfl⟩ : syracuseStep 13154723 = 19732085) B19732085
theorem B7797179 : Blo 1518456 7797179 := bstep (se 1 (by rfl) ⟨5847884, by rfl⟩ : syracuseStep 7797179 = 11695769) B11695769
theorem B540162755 : Blo 1518456 540162755 := bstep (se 1 (by rfl) ⟨405122066, by rfl⟩ : syracuseStep 540162755 = 810244133) B810244133
theorem B5126921 : Blo 1518456 5126921 := bstep (se 2 (by rfl) ⟨1922595, by rfl⟩ : syracuseStep 5126921 = 3845191) B3845191
theorem B18471727 : Blo 1518456 18471727 := bstep (se 1 (by rfl) ⟨13853795, by rfl⟩ : syracuseStep 18471727 = 27707591) B27707591
theorem B18472121 : Blo 1518456 18472121 := bstep (se 2 (by rfl) ⟨6927045, by rfl⟩ : syracuseStep 18472121 = 13854091) B13854091
theorem B1924327 : Blo 1518456 1924327 := bstep (se 1 (by rfl) ⟨1443245, by rfl⟩ : syracuseStep 1924327 = 2886491) B2886491
theorem B12328499 : Blo 1518456 12328499 := bstep (se 1 (by rfl) ⟨9246374, by rfl⟩ : syracuseStep 12328499 = 18492749) B18492749
theorem B12975713 : Blo 1518456 12975713 := bstep (se 2 (by rfl) ⟨4865892, by rfl⟩ : syracuseStep 12975713 = 9731785) B9731785
theorem B2883347 : Blo 1518456 2883347 := bstep (se 1 (by rfl) ⟨2162510, by rfl⟩ : syracuseStep 2883347 = 4325021) B4325021
theorem B18726713 : Blo 1518456 18726713 := bstep (se 2 (by rfl) ⟨7022517, by rfl⟩ : syracuseStep 18726713 = 14045035) B14045035
theorem B2563967 : Blo 1518456 2563967 := bstep (se 1 (by rfl) ⟨1922975, by rfl⟩ : syracuseStep 2563967 = 3845951) B3845951
theorem B8216491 : Blo 1518456 8216491 := bstep (se 1 (by rfl) ⟨6162368, by rfl⟩ : syracuseStep 8216491 = 12324737) B12324737
theorem B9732271 : Blo 1518456 9732271 := bstep (se 1 (by rfl) ⟨7299203, by rfl⟩ : syracuseStep 9732271 = 14598407) B14598407
theorem B2564473 : Blo 1518456 2564473 := bstep (se 2 (by rfl) ⟨961677, by rfl⟩ : syracuseStep 2564473 = 1923355) B1923355
theorem B2277791 : Blo 1518456 2277791 := bstep (se 1 (by rfl) ⟨1708343, by rfl⟩ : syracuseStep 2277791 = 3416687) B3416687
theorem B2278121 : Blo 1518456 2278121 := bstep (se 2 (by rfl) ⟨854295, by rfl⟩ : syracuseStep 2278121 = 1708591) B1708591
theorem B1950527 : Blo 1518456 1950527 := bstep (se 1 (by rfl) ⟨1462895, by rfl⟩ : syracuseStep 1950527 = 2925791) B2925791
theorem B20792477 : Blo 1518456 20792477 := bstep (se 3 (by rfl) ⟨3898589, by rfl⟩ : syracuseStep 20792477 = 7797179) B7797179
theorem B3417263 : Blo 1518456 3417263 := bstep (se 1 (by rfl) ⟨2562947, by rfl⟩ : syracuseStep 3417263 = 5125895) B5125895
theorem B3245321 : Blo 1518456 3245321 := bstep (se 2 (by rfl) ⟨1216995, by rfl⟩ : syracuseStep 3245321 = 2433991) B2433991
theorem B4867391 : Blo 1518456 4867391 := bstep (se 1 (by rfl) ⟨3650543, by rfl⟩ : syracuseStep 4867391 = 7301087) B7301087
theorem B2278889 : Blo 1518456 2278889 := bstep (se 2 (by rfl) ⟨854583, by rfl⟩ : syracuseStep 2278889 = 1709167) B1709167
theorem B2278967 : Blo 1518456 2278967 := bstep (se 1 (by rfl) ⟨1709225, by rfl⟩ : syracuseStep 2278967 = 3418451) B3418451
theorem B2565769 : Blo 1518456 2565769 := bstep (se 2 (by rfl) ⟨962163, by rfl⟩ : syracuseStep 2565769 = 1924327) B1924327
theorem B8210159 : Blo 1518456 8210159 := bstep (se 1 (by rfl) ⟨6157619, by rfl⟩ : syracuseStep 8210159 = 12315239) B12315239
theorem B5195531 : Blo 1518456 5195531 := bstep (se 1 (by rfl) ⟨3896648, by rfl⟩ : syracuseStep 5195531 = 7793297) B7793297
theorem B3417947 : Blo 1518456 3417947 := bstep (se 1 (by rfl) ⟨2563460, by rfl⟩ : syracuseStep 3417947 = 5126921) B5126921
theorem B5130107 : Blo 1518456 5130107 := bstep (se 1 (by rfl) ⟨3847580, by rfl⟩ : syracuseStep 5130107 = 7695161) B7695161
theorem B2279327 : Blo 1518456 2279327 := bstep (se 1 (by rfl) ⟨1709495, by rfl⟩ : syracuseStep 2279327 = 3418991) B3418991
theorem B2279495 : Blo 1518456 2279495 := bstep (se 1 (by rfl) ⟨1709621, by rfl⟩ : syracuseStep 2279495 = 3419243) B3419243
theorem B12314747 : Blo 1518456 12314747 := bstep (se 1 (by rfl) ⟨9236060, by rfl⟩ : syracuseStep 12314747 = 18472121) B18472121
theorem B29608091 : Blo 1518456 29608091 := bstep (se 1 (by rfl) ⟨22206068, by rfl⟩ : syracuseStep 29608091 = 44412137) B44412137
theorem B2279675 : Blo 1518456 2279675 := bstep (se 1 (by rfl) ⟨1709756, by rfl⟩ : syracuseStep 2279675 = 3419513) B3419513
theorem B11536667 : Blo 1518456 11536667 := bstep (se 1 (by rfl) ⟨8652500, by rfl⟩ : syracuseStep 11536667 = 17305001) B17305001
theorem B5130539 : Blo 1518456 5130539 := bstep (se 1 (by rfl) ⟨3847904, by rfl⟩ : syracuseStep 5130539 = 7695809) B7695809
theorem B8218999 : Blo 1518456 8218999 := bstep (se 1 (by rfl) ⟨6164249, by rfl⟩ : syracuseStep 8218999 = 12328499) B12328499
theorem B5474719 : Blo 1518456 5474719 := bstep (se 1 (by rfl) ⟨4106039, by rfl⟩ : syracuseStep 5474719 = 8212079) B8212079
theorem B10955321 : Blo 1518456 10955321 := bstep (se 2 (by rfl) ⟨4108245, by rfl⟩ : syracuseStep 10955321 = 8216491) B8216491
theorem B11700845 : Blo 1518456 11700845 := bstep (se 3 (by rfl) ⟨2193908, by rfl⟩ : syracuseStep 11700845 = 4387817) B4387817
theorem B4328063 : Blo 1518456 4328063 := bstep (se 1 (by rfl) ⟨3246047, by rfl⟩ : syracuseStep 4328063 = 6492095) B6492095
theorem B2280095 : Blo 1518456 2280095 := bstep (se 1 (by rfl) ⟨1710071, by rfl⟩ : syracuseStep 2280095 = 3420143) B3420143
theorem B3418919 : Blo 1518456 3418919 := bstep (se 1 (by rfl) ⟨2564189, by rfl⟩ : syracuseStep 3418919 = 5128379) B5128379
theorem B12979025 : Blo 1518456 12979025 := bstep (se 2 (by rfl) ⟨4867134, by rfl⟩ : syracuseStep 12979025 = 9734269) B9734269
theorem B1518575 : Blo 1518456 1518575 := bstep (se 1 (by rfl) ⟨1138931, by rfl⟩ : syracuseStep 1518575 = 2277863) B2277863
theorem B3288127 : Blo 1518456 3288127 := bstep (se 1 (by rfl) ⟨2466095, by rfl⟩ : syracuseStep 3288127 = 4932191) B4932191
theorem B12987499 : Blo 1518456 12987499 := bstep (se 1 (by rfl) ⟨9740624, by rfl⟩ : syracuseStep 12987499 = 19481249) B19481249
theorem B1518759 : Blo 1518456 1518759 := bstep (se 1 (by rfl) ⟨1139069, by rfl⟩ : syracuseStep 1518759 = 2278139) B2278139
theorem B3845303 : Blo 1518456 3845303 := bstep (se 1 (by rfl) ⟨2883977, by rfl⟩ : syracuseStep 3845303 = 5767955) B5767955
theorem B3419567 : Blo 1518456 3419567 := bstep (se 1 (by rfl) ⟨2564675, by rfl⟩ : syracuseStep 3419567 = 5129351) B5129351
theorem B1519055 : Blo 1518456 1519055 := bstep (se 1 (by rfl) ⟨1139291, by rfl⟩ : syracuseStep 1519055 = 2278583) B2278583
theorem B1519151 : Blo 1518456 1519151 := bstep (se 1 (by rfl) ⟨1139363, by rfl⟩ : syracuseStep 1519151 = 2278727) B2278727
theorem B4107847 : Blo 1518456 4107847 := bstep (se 1 (by rfl) ⟨3080885, by rfl⟩ : syracuseStep 4107847 = 6161771) B6161771
theorem B4329065 : Blo 1518456 4329065 := bstep (se 2 (by rfl) ⟨1623399, by rfl⟩ : syracuseStep 4329065 = 3246799) B3246799
theorem B1519215 : Blo 1518456 1519215 := bstep (se 1 (by rfl) ⟨1139411, by rfl⟩ : syracuseStep 1519215 = 2278823) B2278823
theorem B3419819 : Blo 1518456 3419819 := bstep (se 1 (by rfl) ⟨2564864, by rfl⟩ : syracuseStep 3419819 = 5129729) B5129729
theorem B1519335 : Blo 1518456 1519335 := bstep (se 1 (by rfl) ⟨1139501, by rfl⟩ : syracuseStep 1519335 = 2279003) B2279003
theorem B24628969 : Blo 1518456 24628969 := bstep (se 2 (by rfl) ⟨9235863, by rfl⟩ : syracuseStep 24628969 = 18471727) B18471727
theorem B1519647 : Blo 1518456 1519647 := bstep (se 1 (by rfl) ⟨1139735, by rfl⟩ : syracuseStep 1519647 = 2279471) B2279471
theorem B101273651 : Blo 1518456 101273651 := bstep (se 1 (by rfl) ⟨75955238, by rfl⟩ : syracuseStep 101273651 = 151910477) B151910477
theorem B1519823 : Blo 1518456 1519823 := bstep (se 1 (by rfl) ⟨1139867, by rfl⟩ : syracuseStep 1519823 = 2279735) B2279735
theorem B6492383 : Blo 1518456 6492383 := bstep (se 1 (by rfl) ⟨4869287, by rfl⟩ : syracuseStep 6492383 = 9738575) B9738575
theorem B8769815 : Blo 1518456 8769815 := bstep (se 1 (by rfl) ⟨6577361, by rfl⟩ : syracuseStep 8769815 = 13154723) B13154723
theorem B1519943 : Blo 1518456 1519943 := bstep (se 1 (by rfl) ⟨1139957, by rfl⟩ : syracuseStep 1519943 = 2279915) B2279915
theorem B3420539 : Blo 1518456 3420539 := bstep (se 1 (by rfl) ⟨2565404, by rfl⟩ : syracuseStep 3420539 = 5130809) B5130809
theorem B360108503 : Blo 1518456 360108503 := bstep (se 1 (by rfl) ⟨270081377, by rfl⟩ : syracuseStep 360108503 = 540162755) B540162755
theorem B1520103 : Blo 1518456 1520103 := bstep (se 1 (by rfl) ⟨1140077, by rfl⟩ : syracuseStep 1520103 = 2280155) B2280155
theorem B3420647 : Blo 1518456 3420647 := bstep (se 1 (by rfl) ⟨2565485, by rfl⟩ : syracuseStep 3420647 = 5130971) B5130971
theorem B1520127 : Blo 1518456 1520127 := bstep (se 1 (by rfl) ⟨1140095, by rfl⟩ : syracuseStep 1520127 = 2280191) B2280191
theorem B7696943 : Blo 1518456 7696943 := bstep (se 1 (by rfl) ⟨5772707, by rfl⟩ : syracuseStep 7696943 = 11545415) B11545415
theorem B5124815 : Blo 1518456 5124815 := bstep (se 1 (by rfl) ⟨3843611, by rfl⟩ : syracuseStep 5124815 = 7687223) B7687223
theorem B1922231 : Blo 1518456 1922231 := bstep (se 1 (by rfl) ⟨1441673, by rfl⟩ : syracuseStep 1922231 = 2883347) B2883347
theorem B1709311 : Blo 1518456 1709311 := bstep (se 1 (by rfl) ⟨1281983, by rfl⟩ : syracuseStep 1709311 = 2563967) B2563967
theorem B5125625 : Blo 1518456 5125625 := bstep (se 2 (by rfl) ⟨1922109, by rfl⟩ : syracuseStep 5125625 = 3844219) B3844219
theorem B1709599 : Blo 1518456 1709599 := bstep (se 1 (by rfl) ⟨1282199, by rfl⟩ : syracuseStep 1709599 = 2564399) B2564399
theorem B14612015 : Blo 1518456 14612015 := bstep (se 1 (by rfl) ⟨10959011, by rfl⟩ : syracuseStep 14612015 = 21918023) B21918023
theorem B5125787 : Blo 1518456 5125787 := bstep (se 1 (by rfl) ⟨3844340, by rfl⟩ : syracuseStep 5125787 = 7688681) B7688681
theorem B17553257 : Blo 1518456 17553257 := bstep (se 2 (by rfl) ⟨6582471, by rfl⟩ : syracuseStep 17553257 = 13164943) B13164943
theorem B83187587 : Blo 1518456 83187587 := bstep (se 1 (by rfl) ⟨62390690, by rfl⟩ : syracuseStep 83187587 = 124781381) B124781381
theorem B3749771 : Blo 1518456 3749771 := bstep (se 1 (by rfl) ⟨2812328, by rfl⟩ : syracuseStep 3749771 = 5624657) B5624657
theorem B3897227 : Blo 1518456 3897227 := bstep (se 1 (by rfl) ⟨2922920, by rfl⟩ : syracuseStep 3897227 = 5845841) B5845841
theorem B70187323 : Blo 1518456 70187323 := bstep (se 1 (by rfl) ⟨52640492, by rfl⟩ : syracuseStep 70187323 = 105280985) B105280985
theorem B5478815 : Blo 1518456 5478815 := bstep (se 1 (by rfl) ⟨4109111, by rfl⟩ : syracuseStep 5478815 = 8218223) B8218223
theorem B2562475 : Blo 1518456 2562475 := bstep (se 1 (by rfl) ⟨1921856, by rfl⟩ : syracuseStep 2562475 = 3843713) B3843713
theorem B11532779 : Blo 1518456 11532779 := bstep (se 1 (by rfl) ⟨8649584, by rfl⟩ : syracuseStep 11532779 = 17299169) B17299169
theorem B10402451 : Blo 1518456 10402451 := bstep (se 1 (by rfl) ⟨7801838, by rfl⟩ : syracuseStep 10402451 = 15603677) B15603677
theorem B5766011 : Blo 1518456 5766011 := bstep (se 1 (by rfl) ⟨4324508, by rfl⟩ : syracuseStep 5766011 = 8649017) B8649017
theorem B2563015 : Blo 1518456 2563015 := bstep (se 1 (by rfl) ⟨1922261, by rfl⟩ : syracuseStep 2563015 = 3844523) B3844523
theorem B9739601 : Blo 1518456 9739601 := bstep (se 2 (by rfl) ⟨3652350, by rfl⟩ : syracuseStep 9739601 = 7304701) B7304701
theorem B8650475 : Blo 1518456 8650475 := bstep (se 1 (by rfl) ⟨6487856, by rfl⟩ : syracuseStep 8650475 = 12975713) B12975713
theorem B24633071 : Blo 1518456 24633071 := bstep (se 1 (by rfl) ⟨18474803, by rfl⟩ : syracuseStep 24633071 = 36949607) B36949607
theorem B12484475 : Blo 1518456 12484475 := bstep (se 1 (by rfl) ⟨9363356, by rfl⟩ : syracuseStep 12484475 = 18726713) B18726713
theorem B12976361 : Blo 1518456 12976361 := bstep (se 2 (by rfl) ⟨4866135, by rfl⟩ : syracuseStep 12976361 = 9732271) B9732271
theorem B3416543 : Blo 1518456 3416543 := bstep (se 1 (by rfl) ⟨2562407, by rfl⟩ : syracuseStep 3416543 = 5124815) B5124815
theorem B3416633 : Blo 1518456 3416633 := bstep (se 2 (by rfl) ⟨1281237, by rfl⟩ : syracuseStep 3416633 = 2562475) B2562475
theorem B13861651 : Blo 1518456 13861651 := bstep (se 1 (by rfl) ⟨10396238, by rfl⟩ : syracuseStep 13861651 = 20792477) B20792477
theorem B2278175 : Blo 1518456 2278175 := bstep (se 1 (by rfl) ⟨1708631, by rfl⟩ : syracuseStep 2278175 = 3417263) B3417263
theorem B2163547 : Blo 1518456 2163547 := bstep (se 1 (by rfl) ⟨1622660, by rfl⟩ : syracuseStep 2163547 = 3245321) B3245321
theorem B3417083 : Blo 1518456 3417083 := bstep (se 1 (by rfl) ⟨2562812, by rfl⟩ : syracuseStep 3417083 = 5125625) B5125625
theorem B9741343 : Blo 1518456 9741343 := bstep (se 1 (by rfl) ⟨7306007, by rfl⟩ : syracuseStep 9741343 = 14612015) B14612015
theorem B3417191 : Blo 1518456 3417191 := bstep (se 1 (by rfl) ⟨2562893, by rfl⟩ : syracuseStep 3417191 = 5125787) B5125787
theorem B5473439 : Blo 1518456 5473439 := bstep (se 1 (by rfl) ⟨4105079, by rfl⟩ : syracuseStep 5473439 = 8210159) B8210159
theorem B2278631 : Blo 1518456 2278631 := bstep (se 1 (by rfl) ⟨1708973, by rfl⟩ : syracuseStep 2278631 = 3417947) B3417947
theorem B2598151 : Blo 1518456 2598151 := bstep (se 1 (by rfl) ⟨1948613, by rfl⟩ : syracuseStep 2598151 = 3897227) B3897227
theorem B3417353 : Blo 1518456 3417353 := bstep (se 2 (by rfl) ⟨1281507, by rfl⟩ : syracuseStep 3417353 = 2563015) B2563015
theorem B8209831 : Blo 1518456 8209831 := bstep (se 1 (by rfl) ⟨6157373, by rfl⟩ : syracuseStep 8209831 = 12314747) B12314747
theorem B4384169 : Blo 1518456 4384169 := bstep (se 2 (by rfl) ⟨1644063, by rfl⟩ : syracuseStep 4384169 = 3288127) B3288127
theorem B2279081 : Blo 1518456 2279081 := bstep (se 2 (by rfl) ⟨854655, by rfl⟩ : syracuseStep 2279081 = 1709311) B1709311
theorem B7800563 : Blo 1518456 7800563 := bstep (se 1 (by rfl) ⟨5850422, by rfl⟩ : syracuseStep 7800563 = 11700845) B11700845
theorem B2885375 : Blo 1518456 2885375 := bstep (se 1 (by rfl) ⟨2164031, by rfl⟩ : syracuseStep 2885375 = 4328063) B4328063
theorem B2279279 : Blo 1518456 2279279 := bstep (se 1 (by rfl) ⟨1709459, by rfl⟩ : syracuseStep 2279279 = 3418919) B3418919
theorem B8652683 : Blo 1518456 8652683 := bstep (se 1 (by rfl) ⟨6489512, by rfl⟩ : syracuseStep 8652683 = 12979025) B12979025
theorem B3844007 : Blo 1518456 3844007 := bstep (se 1 (by rfl) ⟨2883005, by rfl⟩ : syracuseStep 3844007 = 5766011) B5766011
theorem B2279465 : Blo 1518456 2279465 := bstep (se 2 (by rfl) ⟨854799, by rfl⟩ : syracuseStep 2279465 = 1709599) B1709599
theorem B29198501 : Blo 1518456 29198501 := bstep (se 4 (by rfl) ⟨2737359, by rfl⟩ : syracuseStep 29198501 = 5474719) B5474719
theorem B2279711 : Blo 1518456 2279711 := bstep (se 1 (by rfl) ⟨1709783, by rfl⟩ : syracuseStep 2279711 = 3419567) B3419567
theorem B2886043 : Blo 1518456 2886043 := bstep (se 1 (by rfl) ⟨2164532, by rfl⟩ : syracuseStep 2886043 = 4329065) B4329065
theorem B2279879 : Blo 1518456 2279879 := bstep (se 1 (by rfl) ⟨1709909, by rfl⟩ : syracuseStep 2279879 = 3419819) B3419819
theorem B4328255 : Blo 1518456 4328255 := bstep (se 1 (by rfl) ⟨3246191, by rfl⟩ : syracuseStep 4328255 = 6492383) B6492383
theorem B2280359 : Blo 1518456 2280359 := bstep (se 1 (by rfl) ⟨1710269, by rfl⟩ : syracuseStep 2280359 = 3420539) B3420539
theorem B1518527 : Blo 1518456 1518527 := bstep (se 1 (by rfl) ⟨1138895, by rfl⟩ : syracuseStep 1518527 = 2277791) B2277791
theorem B2280431 : Blo 1518456 2280431 := bstep (se 1 (by rfl) ⟨1710323, by rfl⟩ : syracuseStep 2280431 = 3420647) B3420647
theorem B5131295 : Blo 1518456 5131295 := bstep (se 1 (by rfl) ⟨3848471, by rfl⟩ : syracuseStep 5131295 = 7696943) B7696943
theorem B1518747 : Blo 1518456 1518747 := bstep (se 1 (by rfl) ⟨1139060, by rfl⟩ : syracuseStep 1518747 = 2278121) B2278121
theorem B3419297 : Blo 1518456 3419297 := bstep (se 2 (by rfl) ⟨1282236, by rfl⟩ : syracuseStep 3419297 = 2564473) B2564473
theorem B12979709 : Blo 1518456 12979709 := bstep (se 3 (by rfl) ⟨2433695, by rfl⟩ : syracuseStep 12979709 = 4867391) B4867391
theorem B1519259 : Blo 1518456 1519259 := bstep (se 1 (by rfl) ⟨1139444, by rfl⟩ : syracuseStep 1519259 = 2278889) B2278889
theorem B1519311 : Blo 1518456 1519311 := bstep (se 1 (by rfl) ⟨1139483, by rfl⟩ : syracuseStep 1519311 = 2278967) B2278967
theorem B11702171 : Blo 1518456 11702171 := bstep (se 1 (by rfl) ⟨8776628, by rfl⟩ : syracuseStep 11702171 = 17553257) B17553257
theorem B3420071 : Blo 1518456 3420071 := bstep (se 1 (by rfl) ⟨2565053, by rfl⟩ : syracuseStep 3420071 = 5130107) B5130107
theorem B1519551 : Blo 1518456 1519551 := bstep (se 1 (by rfl) ⟨1139663, by rfl⟩ : syracuseStep 1519551 = 2279327) B2279327
theorem B1519663 : Blo 1518456 1519663 := bstep (se 1 (by rfl) ⟨1139747, by rfl⟩ : syracuseStep 1519663 = 2279495) B2279495
theorem B19738727 : Blo 1518456 19738727 := bstep (se 1 (by rfl) ⟨14804045, by rfl⟩ : syracuseStep 19738727 = 29608091) B29608091
theorem B1519783 : Blo 1518456 1519783 := bstep (se 1 (by rfl) ⟨1139837, by rfl⟩ : syracuseStep 1519783 = 2279675) B2279675
theorem B3420359 : Blo 1518456 3420359 := bstep (se 1 (by rfl) ⟨2565269, by rfl⟩ : syracuseStep 3420359 = 5130539) B5130539
theorem B7688519 : Blo 1518456 7688519 := bstep (se 1 (by rfl) ⟨5766389, by rfl⟩ : syracuseStep 7688519 = 11532779) B11532779
theorem B7303547 : Blo 1518456 7303547 := bstep (se 1 (by rfl) ⟨5477660, by rfl⟩ : syracuseStep 7303547 = 10955321) B10955321
theorem B6934967 : Blo 1518456 6934967 := bstep (se 1 (by rfl) ⟨5201225, by rfl⟩ : syracuseStep 6934967 = 10402451) B10402451
theorem B1520063 : Blo 1518456 1520063 := bstep (se 1 (by rfl) ⟨1140047, by rfl⟩ : syracuseStep 1520063 = 2280095) B2280095
theorem B5477129 : Blo 1518456 5477129 := bstep (se 2 (by rfl) ⟨2053923, by rfl⟩ : syracuseStep 5477129 = 4107847) B4107847
theorem B3421025 : Blo 1518456 3421025 := bstep (se 2 (by rfl) ⟨1282884, by rfl⟩ : syracuseStep 3421025 = 2565769) B2565769
theorem B6493067 : Blo 1518456 6493067 := bstep (se 1 (by rfl) ⟨4869800, by rfl⟩ : syracuseStep 6493067 = 9739601) B9739601
theorem B32838625 : Blo 1518456 32838625 := bstep (se 2 (by rfl) ⟨12314484, by rfl⟩ : syracuseStep 32838625 = 24628969) B24628969
theorem B9999389 : Blo 1518456 9999389 := bstep (se 3 (by rfl) ⟨1874885, by rfl⟩ : syracuseStep 9999389 = 3749771) B3749771
theorem B16422047 : Blo 1518456 16422047 := bstep (se 1 (by rfl) ⟨12316535, by rfl⟩ : syracuseStep 16422047 = 24633071) B24633071
theorem B67515767 : Blo 1518456 67515767 := bstep (se 1 (by rfl) ⟨50636825, by rfl⟩ : syracuseStep 67515767 = 101273651) B101273651
theorem B5846543 : Blo 1518456 5846543 := bstep (se 1 (by rfl) ⟨4384907, by rfl⟩ : syracuseStep 5846543 = 8769815) B8769815
theorem B240072335 : Blo 1518456 240072335 := bstep (se 1 (by rfl) ⟨180054251, by rfl⟩ : syracuseStep 240072335 = 360108503) B360108503
theorem B93583097 : Blo 1518456 93583097 := bstep (se 2 (by rfl) ⟨35093661, by rfl⟩ : syracuseStep 93583097 = 70187323) B70187323
theorem B5125949 : Blo 1518456 5125949 := bstep (se 3 (by rfl) ⟨961115, by rfl⟩ : syracuseStep 5125949 = 1922231) B1922231
theorem B10958665 : Blo 1518456 10958665 := bstep (se 2 (by rfl) ⟨4109499, by rfl⟩ : syracuseStep 10958665 = 8218999) B8218999
theorem B3463687 : Blo 1518456 3463687 := bstep (se 1 (by rfl) ⟨2597765, by rfl⟩ : syracuseStep 3463687 = 5195531) B5195531
theorem B55458391 : Blo 1518456 55458391 := bstep (se 1 (by rfl) ⟨41593793, by rfl⟩ : syracuseStep 55458391 = 83187587) B83187587
theorem B17316665 : Blo 1518456 17316665 := bstep (se 2 (by rfl) ⟨6493749, by rfl⟩ : syracuseStep 17316665 = 12987499) B12987499
theorem B7691111 : Blo 1518456 7691111 := bstep (se 1 (by rfl) ⟨5768333, by rfl⟩ : syracuseStep 7691111 = 11536667) B11536667
theorem B3652543 : Blo 1518456 3652543 := bstep (se 1 (by rfl) ⟨2739407, by rfl⟩ : syracuseStep 3652543 = 5478815) B5478815
theorem B2563535 : Blo 1518456 2563535 := bstep (se 1 (by rfl) ⟨1922651, by rfl⟩ : syracuseStep 2563535 = 3845303) B3845303
theorem B5201405 : Blo 1518456 5201405 := bstep (se 3 (by rfl) ⟨975263, by rfl⟩ : syracuseStep 5201405 = 1950527) B1950527
theorem B5766983 : Blo 1518456 5766983 := bstep (se 1 (by rfl) ⟨4325237, by rfl⟩ : syracuseStep 5766983 = 8650475) B8650475
theorem B8322983 : Blo 1518456 8322983 := bstep (se 1 (by rfl) ⟨6242237, by rfl⟩ : syracuseStep 8322983 = 12484475) B12484475
theorem B18472997 : Blo 1518456 18472997 := bstep (se 4 (by rfl) ⟨1731843, by rfl⟩ : syracuseStep 18472997 = 3463687) B3463687
theorem B8650907 : Blo 1518456 8650907 := bstep (se 1 (by rfl) ⟨6488180, by rfl⟩ : syracuseStep 8650907 = 12976361) B12976361
theorem B2277695 : Blo 1518456 2277695 := bstep (se 1 (by rfl) ⟨1708271, by rfl⟩ : syracuseStep 2277695 = 3416543) B3416543
theorem B2277755 : Blo 1518456 2277755 := bstep (se 1 (by rfl) ⟨1708316, by rfl⟩ : syracuseStep 2277755 = 3416633) B3416633
theorem B2278055 : Blo 1518456 2278055 := bstep (se 1 (by rfl) ⟨1708541, by rfl⟩ : syracuseStep 2278055 = 3417083) B3417083
theorem B2278127 : Blo 1518456 2278127 := bstep (se 1 (by rfl) ⟨1708595, by rfl⟩ : syracuseStep 2278127 = 3417191) B3417191
theorem B2278235 : Blo 1518456 2278235 := bstep (se 1 (by rfl) ⟨1708676, by rfl⟩ : syracuseStep 2278235 = 3417353) B3417353
theorem B18482201 : Blo 1518456 18482201 := bstep (se 2 (by rfl) ⟨6930825, by rfl⟩ : syracuseStep 18482201 = 13861651) B13861651
theorem B160048223 : Blo 1518456 160048223 := bstep (se 1 (by rfl) ⟨120036167, by rfl⟩ : syracuseStep 160048223 = 240072335) B240072335
theorem B2884729 : Blo 1518456 2884729 := bstep (se 2 (by rfl) ⟨1081773, by rfl⟩ : syracuseStep 2884729 = 2163547) B2163547
theorem B3417299 : Blo 1518456 3417299 := bstep (se 1 (by rfl) ⟨2562974, by rfl⟩ : syracuseStep 3417299 = 5125949) B5125949
theorem B5768455 : Blo 1518456 5768455 := bstep (se 1 (by rfl) ⟨4326341, by rfl⟩ : syracuseStep 5768455 = 8652683) B8652683
theorem B19465667 : Blo 1518456 19465667 := bstep (se 1 (by rfl) ⟨14599250, by rfl⟩ : syracuseStep 19465667 = 29198501) B29198501
theorem B11544443 : Blo 1518456 11544443 := bstep (se 1 (by rfl) ⟨8658332, by rfl⟩ : syracuseStep 11544443 = 17316665) B17316665
theorem B10946441 : Blo 1518456 10946441 := bstep (se 2 (by rfl) ⟨4104915, by rfl⟩ : syracuseStep 10946441 = 8209831) B8209831
theorem B2279531 : Blo 1518456 2279531 := bstep (se 1 (by rfl) ⟨1709648, by rfl⟩ : syracuseStep 2279531 = 3419297) B3419297
theorem B8653139 : Blo 1518456 8653139 := bstep (se 1 (by rfl) ⟨6489854, by rfl⟩ : syracuseStep 8653139 = 12979709) B12979709
theorem B3467603 : Blo 1518456 3467603 := bstep (se 1 (by rfl) ⟨2600702, by rfl⟩ : syracuseStep 3467603 = 5201405) B5201405
theorem B3844655 : Blo 1518456 3844655 := bstep (se 1 (by rfl) ⟨2883491, by rfl⟩ : syracuseStep 3844655 = 5766983) B5766983
theorem B7801447 : Blo 1518456 7801447 := bstep (se 1 (by rfl) ⟨5851085, by rfl⟩ : syracuseStep 7801447 = 11702171) B11702171
theorem B5548655 : Blo 1518456 5548655 := bstep (se 1 (by rfl) ⟨4161491, by rfl⟩ : syracuseStep 5548655 = 8322983) B8322983
theorem B2280047 : Blo 1518456 2280047 := bstep (se 1 (by rfl) ⟨1710035, by rfl⟩ : syracuseStep 2280047 = 3420071) B3420071
theorem B13159151 : Blo 1518456 13159151 := bstep (se 1 (by rfl) ⟨9869363, by rfl⟩ : syracuseStep 13159151 = 19738727) B19738727
theorem B2280239 : Blo 1518456 2280239 := bstep (se 1 (by rfl) ⟨1710179, by rfl⟩ : syracuseStep 2280239 = 3420359) B3420359
theorem B4623311 : Blo 1518456 4623311 := bstep (se 1 (by rfl) ⟨3467483, by rfl⟩ : syracuseStep 4623311 = 6934967) B6934967
theorem B1518783 : Blo 1518456 1518783 := bstep (se 1 (by rfl) ⟨1139087, by rfl⟩ : syracuseStep 1518783 = 2278175) B2278175
theorem B2280683 : Blo 1518456 2280683 := bstep (se 1 (by rfl) ⟨1710512, by rfl⟩ : syracuseStep 2280683 = 3421025) B3421025
theorem B4328711 : Blo 1518456 4328711 := bstep (se 1 (by rfl) ⟨3246533, by rfl⟩ : syracuseStep 4328711 = 6493067) B6493067
theorem B3648959 : Blo 1518456 3648959 := bstep (se 1 (by rfl) ⟨2736719, by rfl⟩ : syracuseStep 3648959 = 5473439) B5473439
theorem B10948031 : Blo 1518456 10948031 := bstep (se 1 (by rfl) ⟨8211023, by rfl⟩ : syracuseStep 10948031 = 16422047) B16422047
theorem B73944521 : Blo 1518456 73944521 := bstep (se 2 (by rfl) ⟨27729195, by rfl⟩ : syracuseStep 73944521 = 55458391) B55458391
theorem B1519087 : Blo 1518456 1519087 := bstep (se 1 (by rfl) ⟨1139315, by rfl⟩ : syracuseStep 1519087 = 2278631) B2278631
theorem B45010511 : Blo 1518456 45010511 := bstep (se 1 (by rfl) ⟨33757883, by rfl⟩ : syracuseStep 45010511 = 67515767) B67515767
theorem B19476125 : Blo 1518456 19476125 := bstep (se 3 (by rfl) ⟨3651773, by rfl⟩ : syracuseStep 19476125 = 7303547) B7303547
theorem B1519387 : Blo 1518456 1519387 := bstep (se 1 (by rfl) ⟨1139540, by rfl⟩ : syracuseStep 1519387 = 2279081) B2279081
theorem B1519519 : Blo 1518456 1519519 := bstep (se 1 (by rfl) ⟨1139639, by rfl⟩ : syracuseStep 1519519 = 2279279) B2279279
theorem B4870057 : Blo 1518456 4870057 := bstep (se 2 (by rfl) ⟨1826271, by rfl⟩ : syracuseStep 4870057 = 3652543) B3652543
theorem B1519643 : Blo 1518456 1519643 := bstep (se 1 (by rfl) ⟨1139732, by rfl⟩ : syracuseStep 1519643 = 2279465) B2279465
theorem B12988457 : Blo 1518456 12988457 := bstep (se 2 (by rfl) ⟨4870671, by rfl⟩ : syracuseStep 12988457 = 9741343) B9741343
theorem B1519807 : Blo 1518456 1519807 := bstep (se 1 (by rfl) ⟨1139855, by rfl⟩ : syracuseStep 1519807 = 2279711) B2279711
theorem B1519919 : Blo 1518456 1519919 := bstep (se 1 (by rfl) ⟨1139939, by rfl⟩ : syracuseStep 1519919 = 2279879) B2279879
theorem B1520239 : Blo 1518456 1520239 := bstep (se 1 (by rfl) ⟨1140179, by rfl⟩ : syracuseStep 1520239 = 2280359) B2280359
theorem B1520287 : Blo 1518456 1520287 := bstep (se 1 (by rfl) ⟨1140215, by rfl⟩ : syracuseStep 1520287 = 2280431) B2280431
theorem B3420863 : Blo 1518456 3420863 := bstep (se 1 (by rfl) ⟨2565647, by rfl⟩ : syracuseStep 3420863 = 5131295) B5131295
theorem B1709023 : Blo 1518456 1709023 := bstep (se 1 (by rfl) ⟨1281767, by rfl⟩ : syracuseStep 1709023 = 2563535) B2563535
theorem B14611553 : Blo 1518456 14611553 := bstep (se 2 (by rfl) ⟨5479332, by rfl⟩ : syracuseStep 14611553 = 10958665) B10958665
theorem B5125679 : Blo 1518456 5125679 := bstep (se 1 (by rfl) ⟨3844259, by rfl⟩ : syracuseStep 5125679 = 7688519) B7688519
theorem B3651419 : Blo 1518456 3651419 := bstep (se 1 (by rfl) ⟨2738564, by rfl⟩ : syracuseStep 3651419 = 5477129) B5477129
theorem B3848057 : Blo 1518456 3848057 := bstep (se 2 (by rfl) ⟨1443021, by rfl⟩ : syracuseStep 3848057 = 2886043) B2886043
theorem B6666259 : Blo 1518456 6666259 := bstep (se 1 (by rfl) ⟨4999694, by rfl⟩ : syracuseStep 6666259 = 9999389) B9999389
theorem B2922779 : Blo 1518456 2922779 := bstep (se 1 (by rfl) ⟨2192084, by rfl⟩ : syracuseStep 2922779 = 4384169) B4384169
theorem B3897695 : Blo 1518456 3897695 := bstep (se 1 (by rfl) ⟨2923271, by rfl⟩ : syracuseStep 3897695 = 5846543) B5846543
theorem B5200375 : Blo 1518456 5200375 := bstep (se 1 (by rfl) ⟨3900281, by rfl⟩ : syracuseStep 5200375 = 7800563) B7800563
theorem B62388731 : Blo 1518456 62388731 := bstep (se 1 (by rfl) ⟨46791548, by rfl⟩ : syracuseStep 62388731 = 93583097) B93583097
theorem B1923583 : Blo 1518456 1923583 := bstep (se 1 (by rfl) ⟨1442687, by rfl⟩ : syracuseStep 1923583 = 2885375) B2885375
theorem B2562671 : Blo 1518456 2562671 := bstep (se 1 (by rfl) ⟨1922003, by rfl⟩ : syracuseStep 2562671 = 3844007) B3844007
theorem B43784833 : Blo 1518456 43784833 := bstep (se 2 (by rfl) ⟨16419312, by rfl⟩ : syracuseStep 43784833 = 32838625) B32838625
theorem B3464201 : Blo 1518456 3464201 := bstep (se 2 (by rfl) ⟨1299075, by rfl⟩ : syracuseStep 3464201 = 2598151) B2598151
theorem B5127407 : Blo 1518456 5127407 := bstep (se 1 (by rfl) ⟨3845555, by rfl⟩ : syracuseStep 5127407 = 7691111) B7691111
theorem B11542013 : Blo 1518456 11542013 := bstep (se 3 (by rfl) ⟨2164127, by rfl⟩ : syracuseStep 11542013 = 4328255) B4328255
theorem B8888345 : Blo 1518456 8888345 := bstep (se 2 (by rfl) ⟨3333129, by rfl⟩ : syracuseStep 8888345 = 6666259) B6666259
theorem B8658971 : Blo 1518456 8658971 := bstep (se 1 (by rfl) ⟨6494228, by rfl⟩ : syracuseStep 8658971 = 12988457) B12988457
theorem B5767271 : Blo 1518456 5767271 := bstep (se 1 (by rfl) ⟨4325453, by rfl⟩ : syracuseStep 5767271 = 8650907) B8650907
theorem B2564777 : Blo 1518456 2564777 := bstep (se 2 (by rfl) ⟨961791, by rfl⟩ : syracuseStep 2564777 = 1923583) B1923583
theorem B12321467 : Blo 1518456 12321467 := bstep (se 1 (by rfl) ⟨9241100, by rfl⟩ : syracuseStep 12321467 = 18482201) B18482201
theorem B9741035 : Blo 1518456 9741035 := bstep (se 1 (by rfl) ⟨7305776, by rfl⟩ : syracuseStep 9741035 = 14611553) B14611553
theorem B2278199 : Blo 1518456 2278199 := bstep (se 1 (by rfl) ⟨1708649, by rfl⟩ : syracuseStep 2278199 = 3417299) B3417299
theorem B12977111 : Blo 1518456 12977111 := bstep (se 1 (by rfl) ⟨9732833, by rfl⟩ : syracuseStep 12977111 = 19465667) B19465667
theorem B3417119 : Blo 1518456 3417119 := bstep (se 1 (by rfl) ⟨2562839, by rfl⟩ : syracuseStep 3417119 = 5125679) B5125679
theorem B2565371 : Blo 1518456 2565371 := bstep (se 1 (by rfl) ⟨1924028, by rfl⟩ : syracuseStep 2565371 = 3848057) B3848057
theorem B2278697 : Blo 1518456 2278697 := bstep (se 2 (by rfl) ⟨854511, by rfl⟩ : syracuseStep 2278697 = 1709023) B1709023
theorem B5768759 : Blo 1518456 5768759 := bstep (se 1 (by rfl) ⟨4326569, by rfl⟩ : syracuseStep 5768759 = 8653139) B8653139
theorem B2311735 : Blo 1518456 2311735 := bstep (se 1 (by rfl) ⟨1733801, by rfl⟩ : syracuseStep 2311735 = 3467603) B3467603
theorem B2598463 : Blo 1518456 2598463 := bstep (se 1 (by rfl) ⟨1948847, by rfl⟩ : syracuseStep 2598463 = 3897695) B3897695
theorem B41592487 : Blo 1518456 41592487 := bstep (se 1 (by rfl) ⟨31194365, by rfl⟩ : syracuseStep 41592487 = 62388731) B62388731
theorem B3082207 : Blo 1518456 3082207 := bstep (se 1 (by rfl) ⟨2311655, by rfl⟩ : syracuseStep 3082207 = 4623311) B4623311
theorem B3418271 : Blo 1518456 3418271 := bstep (se 1 (by rfl) ⟨2563703, by rfl⟩ : syracuseStep 3418271 = 5127407) B5127407
theorem B2885807 : Blo 1518456 2885807 := bstep (se 1 (by rfl) ⟨2164355, by rfl⟩ : syracuseStep 2885807 = 4328711) B4328711
theorem B7694675 : Blo 1518456 7694675 := bstep (se 1 (by rfl) ⟨5771006, by rfl⟩ : syracuseStep 7694675 = 11542013) B11542013
theorem B12315331 : Blo 1518456 12315331 := bstep (se 1 (by rfl) ⟨9236498, by rfl⟩ : syracuseStep 12315331 = 18472997) B18472997
theorem B1518463 : Blo 1518456 1518463 := bstep (se 1 (by rfl) ⟨1138847, by rfl⟩ : syracuseStep 1518463 = 2277695) B2277695
theorem B1518503 : Blo 1518456 1518503 := bstep (se 1 (by rfl) ⟨1138877, by rfl⟩ : syracuseStep 1518503 = 2277755) B2277755
theorem B1518703 : Blo 1518456 1518703 := bstep (se 1 (by rfl) ⟨1139027, by rfl⟩ : syracuseStep 1518703 = 2278055) B2278055
theorem B2280575 : Blo 1518456 2280575 := bstep (se 1 (by rfl) ⟨1710431, by rfl⟩ : syracuseStep 2280575 = 3420863) B3420863
theorem B1518751 : Blo 1518456 1518751 := bstep (se 1 (by rfl) ⟨1139063, by rfl⟩ : syracuseStep 1518751 = 2278127) B2278127
theorem B1518823 : Blo 1518456 1518823 := bstep (se 1 (by rfl) ⟨1139117, by rfl⟩ : syracuseStep 1518823 = 2278235) B2278235
theorem B6933833 : Blo 1518456 6933833 := bstep (se 2 (by rfl) ⟨2600187, by rfl⟩ : syracuseStep 6933833 = 5200375) B5200375
theorem B58379777 : Blo 1518456 58379777 := bstep (se 2 (by rfl) ⟨21892416, by rfl⟩ : syracuseStep 58379777 = 43784833) B43784833
theorem B7696295 : Blo 1518456 7696295 := bstep (se 1 (by rfl) ⟨5772221, by rfl⟩ : syracuseStep 7696295 = 11544443) B11544443
theorem B1519687 : Blo 1518456 1519687 := bstep (se 1 (by rfl) ⟨1139765, by rfl⟩ : syracuseStep 1519687 = 2279531) B2279531
theorem B3846305 : Blo 1518456 3846305 := bstep (se 2 (by rfl) ⟨1442364, by rfl⟩ : syracuseStep 3846305 = 2884729) B2884729
theorem B1708447 : Blo 1518456 1708447 := bstep (se 1 (by rfl) ⟨1281335, by rfl⟩ : syracuseStep 1708447 = 2562671) B2562671
theorem B3699103 : Blo 1518456 3699103 := bstep (se 1 (by rfl) ⟨2774327, by rfl⟩ : syracuseStep 3699103 = 5548655) B5548655
theorem B1520031 : Blo 1518456 1520031 := bstep (se 1 (by rfl) ⟨1140023, by rfl⟩ : syracuseStep 1520031 = 2280047) B2280047
theorem B1520159 : Blo 1518456 1520159 := bstep (se 1 (by rfl) ⟨1140119, by rfl⟩ : syracuseStep 1520159 = 2280239) B2280239
theorem B1520455 : Blo 1518456 1520455 := bstep (se 1 (by rfl) ⟨1140341, by rfl⟩ : syracuseStep 1520455 = 2280683) B2280683
theorem B9737117 : Blo 1518456 9737117 := bstep (se 3 (by rfl) ⟨1825709, by rfl⟩ : syracuseStep 9737117 = 3651419) B3651419
theorem B49296347 : Blo 1518456 49296347 := bstep (se 1 (by rfl) ⟨36972260, by rfl⟩ : syracuseStep 49296347 = 73944521) B73944521
theorem B6493409 : Blo 1518456 6493409 := bstep (se 2 (by rfl) ⟨2435028, by rfl⟩ : syracuseStep 6493409 = 4870057) B4870057
theorem B106698815 : Blo 1518456 106698815 := bstep (se 1 (by rfl) ⟨80024111, by rfl⟩ : syracuseStep 106698815 = 160048223) B160048223
theorem B10401929 : Blo 1518456 10401929 := bstep (se 2 (by rfl) ⟨3900723, by rfl⟩ : syracuseStep 10401929 = 7801447) B7801447
theorem B7297627 : Blo 1518456 7297627 := bstep (se 1 (by rfl) ⟨5473220, by rfl⟩ : syracuseStep 7297627 = 10946441) B10946441
theorem B1948519 : Blo 1518456 1948519 := bstep (se 1 (by rfl) ⟨1461389, by rfl⟩ : syracuseStep 1948519 = 2922779) B2922779
theorem B7691273 : Blo 1518456 7691273 := bstep (se 2 (by rfl) ⟨2884227, by rfl⟩ : syracuseStep 7691273 = 5768455) B5768455
theorem B2563103 : Blo 1518456 2563103 := bstep (se 1 (by rfl) ⟨1922327, by rfl⟩ : syracuseStep 2563103 = 3844655) B3844655
theorem B8772767 : Blo 1518456 8772767 := bstep (se 1 (by rfl) ⟨6579575, by rfl⟩ : syracuseStep 8772767 = 13159151) B13159151
theorem B2309467 : Blo 1518456 2309467 := bstep (se 1 (by rfl) ⟨1732100, by rfl⟩ : syracuseStep 2309467 = 3464201) B3464201
theorem B2432639 : Blo 1518456 2432639 := bstep (se 1 (by rfl) ⟨1824479, by rfl⟩ : syracuseStep 2432639 = 3648959) B3648959
theorem B7298687 : Blo 1518456 7298687 := bstep (se 1 (by rfl) ⟨5474015, by rfl⟩ : syracuseStep 7298687 = 10948031) B10948031
theorem B30007007 : Blo 1518456 30007007 := bstep (se 1 (by rfl) ⟨22505255, by rfl⟩ : syracuseStep 30007007 = 45010511) B45010511
theorem B12984083 : Blo 1518456 12984083 := bstep (se 1 (by rfl) ⟨9738062, by rfl⟩ : syracuseStep 12984083 = 19476125) B19476125
theorem B2564203 : Blo 1518456 2564203 := bstep (se 1 (by rfl) ⟨1923152, by rfl⟩ : syracuseStep 2564203 = 3846305) B3846305
theorem B2277929 : Blo 1518456 2277929 := bstep (se 2 (by rfl) ⟨854223, by rfl⟩ : syracuseStep 2277929 = 1708447) B1708447
theorem B4932137 : Blo 1518456 4932137 := bstep (se 2 (by rfl) ⟨1849551, by rfl⟩ : syracuseStep 4932137 = 3699103) B3699103
theorem B8651407 : Blo 1518456 8651407 := bstep (se 1 (by rfl) ⟨6488555, by rfl⟩ : syracuseStep 8651407 = 12977111) B12977111
theorem B2278079 : Blo 1518456 2278079 := bstep (se 1 (by rfl) ⟨1708559, by rfl⟩ : syracuseStep 2278079 = 3417119) B3417119
theorem B71132543 : Blo 1518456 71132543 := bstep (se 1 (by rfl) ⟨53349407, by rfl⟩ : syracuseStep 71132543 = 106698815) B106698815
theorem B2278847 : Blo 1518456 2278847 := bstep (se 1 (by rfl) ⟨1709135, by rfl⟩ : syracuseStep 2278847 = 3418271) B3418271
theorem B5129783 : Blo 1518456 5129783 := bstep (se 1 (by rfl) ⟨3847337, by rfl⟩ : syracuseStep 5129783 = 7694675) B7694675
theorem B3082313 : Blo 1518456 3082313 := bstep (se 2 (by rfl) ⟨1155867, by rfl⟩ : syracuseStep 3082313 = 2311735) B2311735
theorem B4622555 : Blo 1518456 4622555 := bstep (se 1 (by rfl) ⟨3466916, by rfl⟩ : syracuseStep 4622555 = 6933833) B6933833
theorem B5130863 : Blo 1518456 5130863 := bstep (se 1 (by rfl) ⟨3848147, by rfl⟩ : syracuseStep 5130863 = 7696295) B7696295
theorem B5925563 : Blo 1518456 5925563 := bstep (se 1 (by rfl) ⟨4444172, by rfl⟩ : syracuseStep 5925563 = 8888345) B8888345
theorem B3844847 : Blo 1518456 3844847 := bstep (se 1 (by rfl) ⟨2883635, by rfl⟩ : syracuseStep 3844847 = 5767271) B5767271
theorem B7695485 : Blo 1518456 7695485 := bstep (se 3 (by rfl) ⟨1442903, by rfl⟩ : syracuseStep 7695485 = 2885807) B2885807
theorem B1518799 : Blo 1518456 1518799 := bstep (se 1 (by rfl) ⟨1139099, by rfl⟩ : syracuseStep 1518799 = 2278199) B2278199
theorem B6491411 : Blo 1518456 6491411 := bstep (se 1 (by rfl) ⟨4868558, by rfl⟩ : syracuseStep 6491411 = 9737117) B9737117
theorem B4328939 : Blo 1518456 4328939 := bstep (se 1 (by rfl) ⟨3246704, by rfl⟩ : syracuseStep 4328939 = 6493409) B6493409
theorem B1519131 : Blo 1518456 1519131 := bstep (se 1 (by rfl) ⟨1139348, by rfl⟩ : syracuseStep 1519131 = 2278697) B2278697
theorem B16420441 : Blo 1518456 16420441 := bstep (se 2 (by rfl) ⟨6157665, by rfl⟩ : syracuseStep 16420441 = 12315331) B12315331
theorem B3845839 : Blo 1518456 3845839 := bstep (se 1 (by rfl) ⟨2884379, by rfl⟩ : syracuseStep 3845839 = 5768759) B5768759
theorem B6934619 : Blo 1518456 6934619 := bstep (se 1 (by rfl) ⟨5200964, by rfl⟩ : syracuseStep 6934619 = 10401929) B10401929
theorem B10392101 : Blo 1518456 10392101 := bstep (se 4 (by rfl) ⟨974259, by rfl⟩ : syracuseStep 10392101 = 1948519) B1948519
theorem B1708735 : Blo 1518456 1708735 := bstep (se 1 (by rfl) ⟨1281551, by rfl⟩ : syracuseStep 1708735 = 2563103) B2563103
theorem B1520383 : Blo 1518456 1520383 := bstep (se 1 (by rfl) ⟨1140287, by rfl⟩ : syracuseStep 1520383 = 2280575) B2280575
theorem B55456649 : Blo 1518456 55456649 := bstep (se 2 (by rfl) ⟨20796243, by rfl⟩ : syracuseStep 55456649 = 41592487) B41592487
theorem B8656055 : Blo 1518456 8656055 := bstep (se 1 (by rfl) ⟨6492041, by rfl⟩ : syracuseStep 8656055 = 12984083) B12984083
theorem B4109609 : Blo 1518456 4109609 := bstep (se 2 (by rfl) ⟨1541103, by rfl⟩ : syracuseStep 4109609 = 3082207) B3082207
theorem B5772647 : Blo 1518456 5772647 := bstep (se 1 (by rfl) ⟨4329485, by rfl⟩ : syracuseStep 5772647 = 8658971) B8658971
theorem B1709851 : Blo 1518456 1709851 := bstep (se 1 (by rfl) ⟨1282388, by rfl⟩ : syracuseStep 1709851 = 2564777) B2564777
theorem B8214311 : Blo 1518456 8214311 := bstep (se 1 (by rfl) ⟨6160733, by rfl⟩ : syracuseStep 8214311 = 12321467) B12321467
theorem B6494023 : Blo 1518456 6494023 := bstep (se 1 (by rfl) ⟨4870517, by rfl⟩ : syracuseStep 6494023 = 9741035) B9741035
theorem B32864231 : Blo 1518456 32864231 := bstep (se 1 (by rfl) ⟨24648173, by rfl⟩ : syracuseStep 32864231 = 49296347) B49296347
theorem B9730169 : Blo 1518456 9730169 := bstep (se 2 (by rfl) ⟨3648813, by rfl⟩ : syracuseStep 9730169 = 7297627) B7297627
theorem B1710247 : Blo 1518456 1710247 := bstep (se 1 (by rfl) ⟨1282685, by rfl⟩ : syracuseStep 1710247 = 2565371) B2565371
theorem B6487037 : Blo 1518456 6487037 := bstep (se 3 (by rfl) ⟨1216319, by rfl⟩ : syracuseStep 6487037 = 2432639) B2432639
theorem B3079289 : Blo 1518456 3079289 := bstep (se 2 (by rfl) ⟨1154733, by rfl⟩ : syracuseStep 3079289 = 2309467) B2309467
theorem B5127515 : Blo 1518456 5127515 := bstep (se 1 (by rfl) ⟨3845636, by rfl⟩ : syracuseStep 5127515 = 7691273) B7691273
theorem B3464617 : Blo 1518456 3464617 := bstep (se 2 (by rfl) ⟨1299231, by rfl⟩ : syracuseStep 3464617 = 2598463) B2598463
theorem B5848511 : Blo 1518456 5848511 := bstep (se 1 (by rfl) ⟨4386383, by rfl⟩ : syracuseStep 5848511 = 8772767) B8772767
theorem B38919851 : Blo 1518456 38919851 := bstep (se 1 (by rfl) ⟨29189888, by rfl⟩ : syracuseStep 38919851 = 58379777) B58379777
theorem B4865791 : Blo 1518456 4865791 := bstep (se 1 (by rfl) ⟨3649343, by rfl⟩ : syracuseStep 4865791 = 7298687) B7298687
theorem B20004671 : Blo 1518456 20004671 := bstep (se 1 (by rfl) ⟨15003503, by rfl⟩ : syracuseStep 20004671 = 30007007) B30007007
theorem B36971099 : Blo 1518456 36971099 := bstep (se 1 (by rfl) ⟨27728324, by rfl⟩ : syracuseStep 36971099 = 55456649) B55456649
theorem B11535209 : Blo 1518456 11535209 := bstep (se 2 (by rfl) ⟨4325703, by rfl⟩ : syracuseStep 11535209 = 8651407) B8651407
theorem B2278313 : Blo 1518456 2278313 := bstep (se 2 (by rfl) ⟨854367, by rfl⟩ : syracuseStep 2278313 = 1708735) B1708735
theorem B3950375 : Blo 1518456 3950375 := bstep (se 1 (by rfl) ⟨2962781, by rfl⟩ : syracuseStep 3950375 = 5925563) B5925563
theorem B5130323 : Blo 1518456 5130323 := bstep (se 1 (by rfl) ⟨3847742, by rfl⟩ : syracuseStep 5130323 = 7695485) B7695485
theorem B4327607 : Blo 1518456 4327607 := bstep (se 1 (by rfl) ⟨3245705, by rfl⟩ : syracuseStep 4327607 = 6491411) B6491411
theorem B3418343 : Blo 1518456 3418343 := bstep (se 1 (by rfl) ⟨2563757, by rfl⟩ : syracuseStep 3418343 = 5127515) B5127515
theorem B2885959 : Blo 1518456 2885959 := bstep (se 1 (by rfl) ⟨2164469, by rfl⟩ : syracuseStep 2885959 = 4328939) B4328939
theorem B2279801 : Blo 1518456 2279801 := bstep (se 2 (by rfl) ⟨854925, by rfl⟩ : syracuseStep 2279801 = 1709851) B1709851
theorem B25946567 : Blo 1518456 25946567 := bstep (se 1 (by rfl) ⟨19459925, by rfl⟩ : syracuseStep 25946567 = 38919851) B38919851
theorem B4623079 : Blo 1518456 4623079 := bstep (se 1 (by rfl) ⟨3467309, by rfl⟩ : syracuseStep 4623079 = 6934619) B6934619
theorem B3418937 : Blo 1518456 3418937 := bstep (se 2 (by rfl) ⟨1282101, by rfl⟩ : syracuseStep 3418937 = 2564203) B2564203
theorem B2280329 : Blo 1518456 2280329 := bstep (se 2 (by rfl) ⟨855123, by rfl⟩ : syracuseStep 2280329 = 1710247) B1710247
theorem B1518619 : Blo 1518456 1518619 := bstep (se 1 (by rfl) ⟨1138964, by rfl⟩ : syracuseStep 1518619 = 2277929) B2277929
theorem B1518719 : Blo 1518456 1518719 := bstep (se 1 (by rfl) ⟨1139039, by rfl⟩ : syracuseStep 1518719 = 2278079) B2278079
theorem B5770703 : Blo 1518456 5770703 := bstep (se 1 (by rfl) ⟨4328027, by rfl⟩ : syracuseStep 5770703 = 8656055) B8656055
theorem B2739739 : Blo 1518456 2739739 := bstep (se 1 (by rfl) ⟨2054804, by rfl⟩ : syracuseStep 2739739 = 4109609) B4109609
theorem B1519231 : Blo 1518456 1519231 := bstep (se 1 (by rfl) ⟨1139423, by rfl⟩ : syracuseStep 1519231 = 2278847) B2278847
theorem B3419855 : Blo 1518456 3419855 := bstep (se 1 (by rfl) ⟨2564891, by rfl⟩ : syracuseStep 3419855 = 5129783) B5129783
theorem B5476207 : Blo 1518456 5476207 := bstep (se 1 (by rfl) ⟨4107155, by rfl⟩ : syracuseStep 5476207 = 8214311) B8214311
theorem B21909487 : Blo 1518456 21909487 := bstep (se 1 (by rfl) ⟨16432115, by rfl⟩ : syracuseStep 21909487 = 32864231) B32864231
theorem B13152365 : Blo 1518456 13152365 := bstep (se 3 (by rfl) ⟨2466068, by rfl⟩ : syracuseStep 13152365 = 4932137) B4932137
theorem B3420575 : Blo 1518456 3420575 := bstep (se 1 (by rfl) ⟨2565431, by rfl⟩ : syracuseStep 3420575 = 5130863) B5130863
theorem B2052859 : Blo 1518456 2052859 := bstep (se 1 (by rfl) ⟨1539644, by rfl⟩ : syracuseStep 2052859 = 3079289) B3079289
theorem B21893921 : Blo 1518456 21893921 := bstep (se 2 (by rfl) ⟨8210220, by rfl⟩ : syracuseStep 21893921 = 16420441) B16420441
theorem B6928067 : Blo 1518456 6928067 := bstep (se 1 (by rfl) ⟨5196050, by rfl⟩ : syracuseStep 6928067 = 10392101) B10392101
theorem B12326813 : Blo 1518456 12326813 := bstep (se 3 (by rfl) ⟨2311277, by rfl⟩ : syracuseStep 12326813 = 4622555) B4622555
theorem B3848431 : Blo 1518456 3848431 := bstep (se 1 (by rfl) ⟨2886323, by rfl⟩ : syracuseStep 3848431 = 5772647) B5772647
theorem B47421695 : Blo 1518456 47421695 := bstep (se 1 (by rfl) ⟨35566271, by rfl⟩ : syracuseStep 47421695 = 71132543) B71132543
theorem B15596029 : Blo 1518456 15596029 := bstep (se 3 (by rfl) ⟨2924255, by rfl⟩ : syracuseStep 15596029 = 5848511) B5848511
theorem B2054875 : Blo 1518456 2054875 := bstep (se 1 (by rfl) ⟨1541156, by rfl⟩ : syracuseStep 2054875 = 3082313) B3082313
theorem B6486779 : Blo 1518456 6486779 := bstep (se 1 (by rfl) ⟨4865084, by rfl⟩ : syracuseStep 6486779 = 9730169) B9730169
theorem B2563231 : Blo 1518456 2563231 := bstep (se 1 (by rfl) ⟨1922423, by rfl⟩ : syracuseStep 2563231 = 3844847) B3844847
theorem B4619489 : Blo 1518456 4619489 := bstep (se 2 (by rfl) ⟨1732308, by rfl⟩ : syracuseStep 4619489 = 3464617) B3464617
theorem B4324691 : Blo 1518456 4324691 := bstep (se 1 (by rfl) ⟨3243518, by rfl⟩ : syracuseStep 4324691 = 6487037) B6487037
theorem B5127785 : Blo 1518456 5127785 := bstep (se 2 (by rfl) ⟨1922919, by rfl⟩ : syracuseStep 5127785 = 3845839) B3845839
theorem B6487721 : Blo 1518456 6487721 := bstep (se 2 (by rfl) ⟨2432895, by rfl⟩ : syracuseStep 6487721 = 4865791) B4865791
theorem B8658697 : Blo 1518456 8658697 := bstep (se 2 (by rfl) ⟨3247011, by rfl⟩ : syracuseStep 8658697 = 6494023) B6494023
theorem B13336447 : Blo 1518456 13336447 := bstep (se 1 (by rfl) ⟨10002335, by rfl⟩ : syracuseStep 13336447 = 20004671) B20004671
theorem B2737145 : Blo 1518456 2737145 := bstep (se 2 (by rfl) ⟨1026429, by rfl⟩ : syracuseStep 2737145 = 2052859) B2052859
theorem B8217875 : Blo 1518456 8217875 := bstep (se 1 (by rfl) ⟨6163406, by rfl⟩ : syracuseStep 8217875 = 12326813) B12326813
theorem B2885071 : Blo 1518456 2885071 := bstep (se 1 (by rfl) ⟨2163803, by rfl⟩ : syracuseStep 2885071 = 4327607) B4327607
theorem B2278895 : Blo 1518456 2278895 := bstep (se 1 (by rfl) ⟨1709171, by rfl⟩ : syracuseStep 2278895 = 3418343) B3418343
theorem B3417641 : Blo 1518456 3417641 := bstep (se 2 (by rfl) ⟨1281615, by rfl⟩ : syracuseStep 3417641 = 2563231) B2563231
theorem B2279291 : Blo 1518456 2279291 := bstep (se 1 (by rfl) ⟨1709468, by rfl⟩ : syracuseStep 2279291 = 3418937) B3418937
theorem B11544929 : Blo 1518456 11544929 := bstep (se 2 (by rfl) ⟨4329348, by rfl⟩ : syracuseStep 11544929 = 8658697) B8658697
theorem B3418523 : Blo 1518456 3418523 := bstep (se 1 (by rfl) ⟨2563892, by rfl⟩ : syracuseStep 3418523 = 5127785) B5127785
theorem B2279903 : Blo 1518456 2279903 := bstep (se 1 (by rfl) ⟨1709927, by rfl⟩ : syracuseStep 2279903 = 3419855) B3419855
theorem B7301609 : Blo 1518456 7301609 := bstep (se 2 (by rfl) ⟨2738103, by rfl⟩ : syracuseStep 7301609 = 5476207) B5476207
theorem B8768243 : Blo 1518456 8768243 := bstep (se 1 (by rfl) ⟨6576182, by rfl⟩ : syracuseStep 8768243 = 13152365) B13152365
theorem B2280383 : Blo 1518456 2280383 := bstep (se 1 (by rfl) ⟨1710287, by rfl⟩ : syracuseStep 2280383 = 3420575) B3420575
theorem B5131241 : Blo 1518456 5131241 := bstep (se 2 (by rfl) ⟨1924215, by rfl⟩ : syracuseStep 5131241 = 3848431) B3848431
theorem B1518875 : Blo 1518456 1518875 := bstep (se 1 (by rfl) ⟨1139156, by rfl⟩ : syracuseStep 1518875 = 2278313) B2278313
theorem B2739833 : Blo 1518456 2739833 := bstep (se 2 (by rfl) ⟨1027437, by rfl⟩ : syracuseStep 2739833 = 2054875) B2054875
theorem B6164105 : Blo 1518456 6164105 := bstep (se 2 (by rfl) ⟨2311539, by rfl⟩ : syracuseStep 6164105 = 4623079) B4623079
theorem B3420215 : Blo 1518456 3420215 := bstep (se 1 (by rfl) ⟨2565161, by rfl⟩ : syracuseStep 3420215 = 5130323) B5130323
theorem B1519867 : Blo 1518456 1519867 := bstep (se 1 (by rfl) ⟨1139900, by rfl⟩ : syracuseStep 1519867 = 2279801) B2279801
theorem B17297711 : Blo 1518456 17297711 := bstep (se 1 (by rfl) ⟨12973283, by rfl⟩ : syracuseStep 17297711 = 25946567) B25946567
theorem B1520219 : Blo 1518456 1520219 := bstep (se 1 (by rfl) ⟨1140164, by rfl⟩ : syracuseStep 1520219 = 2280329) B2280329
theorem B3847135 : Blo 1518456 3847135 := bstep (se 1 (by rfl) ⟨2885351, by rfl⟩ : syracuseStep 3847135 = 5770703) B5770703
theorem B17781929 : Blo 1518456 17781929 := bstep (se 2 (by rfl) ⟨6668223, by rfl⟩ : syracuseStep 17781929 = 13336447) B13336447
theorem B83178821 : Blo 1518456 83178821 := bstep (se 4 (by rfl) ⟨7798014, by rfl⟩ : syracuseStep 83178821 = 15596029) B15596029
theorem B24647399 : Blo 1518456 24647399 := bstep (se 1 (by rfl) ⟨18485549, by rfl⟩ : syracuseStep 24647399 = 36971099) B36971099
theorem B42137333 : Blo 1518456 42137333 := bstep (se 5 (by rfl) ⟨1975187, by rfl⟩ : syracuseStep 42137333 = 3950375) B3950375
theorem B3847945 : Blo 1518456 3847945 := bstep (se 2 (by rfl) ⟨1442979, by rfl⟩ : syracuseStep 3847945 = 2885959) B2885959
theorem B14595947 : Blo 1518456 14595947 := bstep (se 1 (by rfl) ⟨10946960, by rfl⟩ : syracuseStep 14595947 = 21893921) B21893921
theorem B7690139 : Blo 1518456 7690139 := bstep (se 1 (by rfl) ⟨5767604, by rfl⟩ : syracuseStep 7690139 = 11535209) B11535209
theorem B12318637 : Blo 1518456 12318637 := bstep (se 3 (by rfl) ⟨2309744, by rfl⟩ : syracuseStep 12318637 = 4619489) B4619489
theorem B126457853 : Blo 1518456 126457853 := bstep (se 3 (by rfl) ⟨23710847, by rfl⟩ : syracuseStep 126457853 = 47421695) B47421695
theorem B4618711 : Blo 1518456 4618711 := bstep (se 1 (by rfl) ⟨3464033, by rfl⟩ : syracuseStep 4618711 = 6928067) B6928067
theorem B4324519 : Blo 1518456 4324519 := bstep (se 1 (by rfl) ⟨3243389, by rfl⟩ : syracuseStep 4324519 = 6486779) B6486779
theorem B3652985 : Blo 1518456 3652985 := bstep (se 2 (by rfl) ⟨1369869, by rfl⟩ : syracuseStep 3652985 = 2739739) B2739739
theorem B2883127 : Blo 1518456 2883127 := bstep (se 1 (by rfl) ⟨2162345, by rfl⟩ : syracuseStep 2883127 = 4324691) B4324691
theorem B4325147 : Blo 1518456 4325147 := bstep (se 1 (by rfl) ⟨3243860, by rfl⟩ : syracuseStep 4325147 = 6487721) B6487721
theorem B29212649 : Blo 1518456 29212649 := bstep (se 2 (by rfl) ⟨10954743, by rfl⟩ : syracuseStep 29212649 = 21909487) B21909487
theorem B21914333 : Blo 1518456 21914333 := bstep (se 3 (by rfl) ⟨4108937, by rfl⟩ : syracuseStep 21914333 = 8217875) B8217875
theorem B11854619 : Blo 1518456 11854619 := bstep (se 1 (by rfl) ⟨8890964, by rfl⟩ : syracuseStep 11854619 = 17781929) B17781929
theorem B55452547 : Blo 1518456 55452547 := bstep (se 1 (by rfl) ⟨41589410, by rfl⟩ : syracuseStep 55452547 = 83178821) B83178821
theorem B9741293 : Blo 1518456 9741293 := bstep (se 3 (by rfl) ⟨1826492, by rfl⟩ : syracuseStep 9741293 = 3652985) B3652985
theorem B2278427 : Blo 1518456 2278427 := bstep (se 1 (by rfl) ⟨1708820, by rfl⟩ : syracuseStep 2278427 = 3417641) B3417641
theorem B28091555 : Blo 1518456 28091555 := bstep (se 1 (by rfl) ⟨21068666, by rfl⟩ : syracuseStep 28091555 = 42137333) B42137333
theorem B5129513 : Blo 1518456 5129513 := bstep (se 2 (by rfl) ⟨1923567, by rfl⟩ : syracuseStep 5129513 = 3847135) B3847135
theorem B2279015 : Blo 1518456 2279015 := bstep (se 1 (by rfl) ⟨1709261, by rfl⟩ : syracuseStep 2279015 = 3418523) B3418523
theorem B4867739 : Blo 1518456 4867739 := bstep (se 1 (by rfl) ⟨3650804, by rfl⟩ : syracuseStep 4867739 = 7301609) B7301609
theorem B3844169 : Blo 1518456 3844169 := bstep (se 2 (by rfl) ⟨1441563, by rfl⟩ : syracuseStep 3844169 = 2883127) B2883127
theorem B5130593 : Blo 1518456 5130593 := bstep (se 2 (by rfl) ⟨1923972, by rfl⟩ : syracuseStep 5130593 = 3847945) B3847945
theorem B19475099 : Blo 1518456 19475099 := bstep (se 1 (by rfl) ⟨14606324, by rfl⟩ : syracuseStep 19475099 = 29212649) B29212649
theorem B2280143 : Blo 1518456 2280143 := bstep (se 1 (by rfl) ⟨1710107, by rfl⟩ : syracuseStep 2280143 = 3420215) B3420215
theorem B1519263 : Blo 1518456 1519263 := bstep (se 1 (by rfl) ⟨1139447, by rfl⟩ : syracuseStep 1519263 = 2278895) B2278895
theorem B1519527 : Blo 1518456 1519527 := bstep (se 1 (by rfl) ⟨1139645, by rfl⟩ : syracuseStep 1519527 = 2279291) B2279291
theorem B7696619 : Blo 1518456 7696619 := bstep (se 1 (by rfl) ⟨5772464, by rfl⟩ : syracuseStep 7696619 = 11544929) B11544929
theorem B1519935 : Blo 1518456 1519935 := bstep (se 1 (by rfl) ⟨1139951, by rfl⟩ : syracuseStep 1519935 = 2279903) B2279903
theorem B16437613 : Blo 1518456 16437613 := bstep (se 3 (by rfl) ⟨3082052, by rfl⟩ : syracuseStep 16437613 = 6164105) B6164105
theorem B5845495 : Blo 1518456 5845495 := bstep (se 1 (by rfl) ⟨4384121, by rfl⟩ : syracuseStep 5845495 = 8768243) B8768243
theorem B3846761 : Blo 1518456 3846761 := bstep (se 2 (by rfl) ⟨1442535, by rfl⟩ : syracuseStep 3846761 = 2885071) B2885071
theorem B1520255 : Blo 1518456 1520255 := bstep (se 1 (by rfl) ⟨1140191, by rfl⟩ : syracuseStep 1520255 = 2280383) B2280383
theorem B3420827 : Blo 1518456 3420827 := bstep (se 1 (by rfl) ⟨2565620, by rfl⟩ : syracuseStep 3420827 = 5131241) B5131241
theorem B337220941 : Blo 1518456 337220941 := bstep (se 3 (by rfl) ⟨63228926, by rfl⟩ : syracuseStep 337220941 = 126457853) B126457853
theorem B11531807 : Blo 1518456 11531807 := bstep (se 1 (by rfl) ⟨8648855, by rfl⟩ : syracuseStep 11531807 = 17297711) B17297711
theorem B6158281 : Blo 1518456 6158281 := bstep (se 2 (by rfl) ⟨2309355, by rfl⟩ : syracuseStep 6158281 = 4618711) B4618711
theorem B1824763 : Blo 1518456 1824763 := bstep (se 1 (by rfl) ⟨1368572, by rfl⟩ : syracuseStep 1824763 = 2737145) B2737145
theorem B16431599 : Blo 1518456 16431599 := bstep (se 1 (by rfl) ⟨12323699, by rfl⟩ : syracuseStep 16431599 = 24647399) B24647399
theorem B9730631 : Blo 1518456 9730631 := bstep (se 1 (by rfl) ⟨7297973, by rfl⟩ : syracuseStep 9730631 = 14595947) B14595947
theorem B5126759 : Blo 1518456 5126759 := bstep (se 1 (by rfl) ⟨3845069, by rfl⟩ : syracuseStep 5126759 = 7690139) B7690139
theorem B5766025 : Blo 1518456 5766025 := bstep (se 2 (by rfl) ⟨2162259, by rfl⟩ : syracuseStep 5766025 = 4324519) B4324519
theorem B1826555 : Blo 1518456 1826555 := bstep (se 1 (by rfl) ⟨1369916, by rfl⟩ : syracuseStep 1826555 = 2739833) B2739833
theorem B2883431 : Blo 1518456 2883431 := bstep (se 1 (by rfl) ⟨2162573, by rfl⟩ : syracuseStep 2883431 = 4325147) B4325147
theorem B16424849 : Blo 1518456 16424849 := bstep (se 2 (by rfl) ⟨6159318, by rfl⟩ : syracuseStep 16424849 = 12318637) B12318637
theorem B2564507 : Blo 1518456 2564507 := bstep (se 1 (by rfl) ⟨1923380, by rfl⟩ : syracuseStep 2564507 = 3846761) B3846761
theorem B18727703 : Blo 1518456 18727703 := bstep (se 1 (by rfl) ⟨14045777, by rfl⟩ : syracuseStep 18727703 = 28091555) B28091555
theorem B3245159 : Blo 1518456 3245159 := bstep (se 1 (by rfl) ⟨2433869, by rfl⟩ : syracuseStep 3245159 = 4867739) B4867739
theorem B10954399 : Blo 1518456 10954399 := bstep (se 1 (by rfl) ⟨8215799, by rfl⟩ : syracuseStep 10954399 = 16431599) B16431599
theorem B3417839 : Blo 1518456 3417839 := bstep (se 1 (by rfl) ⟨2563379, by rfl⟩ : syracuseStep 3417839 = 5126759) B5126759
theorem B449627921 : Blo 1518456 449627921 := bstep (se 2 (by rfl) ⟨168610470, by rfl⟩ : syracuseStep 449627921 = 337220941) B337220941
theorem B8211041 : Blo 1518456 8211041 := bstep (se 2 (by rfl) ⟨3079140, by rfl⟩ : syracuseStep 8211041 = 6158281) B6158281
theorem B19483253 : Blo 1518456 19483253 := bstep (se 5 (by rfl) ⟨913277, by rfl⟩ : syracuseStep 19483253 = 1826555) B1826555
theorem B5131079 : Blo 1518456 5131079 := bstep (se 1 (by rfl) ⟨3848309, by rfl⟩ : syracuseStep 5131079 = 7696619) B7696619
theorem B2280551 : Blo 1518456 2280551 := bstep (se 1 (by rfl) ⟨1710413, by rfl⟩ : syracuseStep 2280551 = 3420827) B3420827
theorem B21916817 : Blo 1518456 21916817 := bstep (se 2 (by rfl) ⟨8218806, by rfl⟩ : syracuseStep 21916817 = 16437613) B16437613
theorem B14609555 : Blo 1518456 14609555 := bstep (se 1 (by rfl) ⟨10957166, by rfl⟩ : syracuseStep 14609555 = 21914333) B21914333
theorem B7793993 : Blo 1518456 7793993 := bstep (se 2 (by rfl) ⟨2922747, by rfl⟩ : syracuseStep 7793993 = 5845495) B5845495
theorem B1518951 : Blo 1518456 1518951 := bstep (se 1 (by rfl) ⟨1139213, by rfl⟩ : syracuseStep 1518951 = 2278427) B2278427
theorem B3419675 : Blo 1518456 3419675 := bstep (se 1 (by rfl) ⟨2564756, by rfl⟩ : syracuseStep 3419675 = 5129513) B5129513
theorem B7687871 : Blo 1518456 7687871 := bstep (se 1 (by rfl) ⟨5765903, by rfl⟩ : syracuseStep 7687871 = 11531807) B11531807
theorem B1519343 : Blo 1518456 1519343 := bstep (se 1 (by rfl) ⟨1139507, by rfl⟩ : syracuseStep 1519343 = 2279015) B2279015
theorem B73936729 : Blo 1518456 73936729 := bstep (se 2 (by rfl) ⟨27726273, by rfl⟩ : syracuseStep 73936729 = 55452547) B55452547
theorem B7688033 : Blo 1518456 7688033 := bstep (se 2 (by rfl) ⟨2883012, by rfl⟩ : syracuseStep 7688033 = 5766025) B5766025
theorem B3420395 : Blo 1518456 3420395 := bstep (se 1 (by rfl) ⟨2565296, by rfl⟩ : syracuseStep 3420395 = 5130593) B5130593
theorem B1520095 : Blo 1518456 1520095 := bstep (se 1 (by rfl) ⟨1140071, by rfl⟩ : syracuseStep 1520095 = 2280143) B2280143
theorem B1922287 : Blo 1518456 1922287 := bstep (se 1 (by rfl) ⟨1441715, by rfl⟩ : syracuseStep 1922287 = 2883431) B2883431
theorem B10949899 : Blo 1518456 10949899 := bstep (se 1 (by rfl) ⟨8212424, by rfl⟩ : syracuseStep 10949899 = 16424849) B16424849
theorem B7903079 : Blo 1518456 7903079 := bstep (se 1 (by rfl) ⟨5927309, by rfl⟩ : syracuseStep 7903079 = 11854619) B11854619
theorem B6494195 : Blo 1518456 6494195 := bstep (se 1 (by rfl) ⟨4870646, by rfl⟩ : syracuseStep 6494195 = 9741293) B9741293
theorem B2562779 : Blo 1518456 2562779 := bstep (se 1 (by rfl) ⟨1922084, by rfl⟩ : syracuseStep 2562779 = 3844169) B3844169
theorem B6487087 : Blo 1518456 6487087 := bstep (se 1 (by rfl) ⟨4865315, by rfl⟩ : syracuseStep 6487087 = 9730631) B9730631
theorem B12983399 : Blo 1518456 12983399 := bstep (se 1 (by rfl) ⟨9737549, by rfl⟩ : syracuseStep 12983399 = 19475099) B19475099
theorem B2433017 : Blo 1518456 2433017 := bstep (se 2 (by rfl) ⟨912381, by rfl⟩ : syracuseStep 2433017 = 1824763) B1824763
theorem B12485135 : Blo 1518456 12485135 := bstep (se 1 (by rfl) ⟨9363851, by rfl⟩ : syracuseStep 12485135 = 18727703) B18727703
theorem B2163439 : Blo 1518456 2163439 := bstep (se 1 (by rfl) ⟨1622579, by rfl⟩ : syracuseStep 2163439 = 3245159) B3245159
theorem B2278559 : Blo 1518456 2278559 := bstep (se 1 (by rfl) ⟨1708919, by rfl⟩ : syracuseStep 2278559 = 3417839) B3417839
theorem B5268719 : Blo 1518456 5268719 := bstep (se 1 (by rfl) ⟨3951539, by rfl⟩ : syracuseStep 5268719 = 7903079) B7903079
theorem B14599865 : Blo 1518456 14599865 := bstep (se 2 (by rfl) ⟨5474949, by rfl⟩ : syracuseStep 14599865 = 10949899) B10949899
theorem B5474027 : Blo 1518456 5474027 := bstep (se 1 (by rfl) ⟨4105520, by rfl⟩ : syracuseStep 5474027 = 8211041) B8211041
theorem B5195995 : Blo 1518456 5195995 := bstep (se 1 (by rfl) ⟨3896996, by rfl⟩ : syracuseStep 5195995 = 7793993) B7793993
theorem B2279783 : Blo 1518456 2279783 := bstep (se 1 (by rfl) ⟨1709837, by rfl⟩ : syracuseStep 2279783 = 3419675) B3419675
theorem B2280263 : Blo 1518456 2280263 := bstep (se 1 (by rfl) ⟨1710197, by rfl⟩ : syracuseStep 2280263 = 3420395) B3420395
theorem B4329463 : Blo 1518456 4329463 := bstep (se 1 (by rfl) ⟨3247097, by rfl⟩ : syracuseStep 4329463 = 6494195) B6494195
theorem B12988835 : Blo 1518456 12988835 := bstep (se 1 (by rfl) ⟨9741626, by rfl⟩ : syracuseStep 12988835 = 19483253) B19483253
theorem B1708519 : Blo 1518456 1708519 := bstep (se 1 (by rfl) ⟨1281389, by rfl⟩ : syracuseStep 1708519 = 2562779) B2562779
theorem B3420719 : Blo 1518456 3420719 := bstep (se 1 (by rfl) ⟨2565539, by rfl⟩ : syracuseStep 3420719 = 5131079) B5131079
theorem B8655599 : Blo 1518456 8655599 := bstep (se 1 (by rfl) ⟨6491699, by rfl⟩ : syracuseStep 8655599 = 12983399) B12983399
theorem B1520367 : Blo 1518456 1520367 := bstep (se 1 (by rfl) ⟨1140275, by rfl⟩ : syracuseStep 1520367 = 2280551) B2280551
theorem B14611211 : Blo 1518456 14611211 := bstep (se 1 (by rfl) ⟨10958408, by rfl⟩ : syracuseStep 14611211 = 21916817) B21916817
theorem B5125247 : Blo 1518456 5125247 := bstep (se 1 (by rfl) ⟨3843935, by rfl⟩ : syracuseStep 5125247 = 7687871) B7687871
theorem B5125355 : Blo 1518456 5125355 := bstep (se 1 (by rfl) ⟨3844016, by rfl⟩ : syracuseStep 5125355 = 7688033) B7688033
theorem B1709671 : Blo 1518456 1709671 := bstep (se 1 (by rfl) ⟨1282253, by rfl⟩ : syracuseStep 1709671 = 2564507) B2564507
theorem B299751947 : Blo 1518456 299751947 := bstep (se 1 (by rfl) ⟨224813960, by rfl⟩ : syracuseStep 299751947 = 449627921) B449627921
theorem B8649449 : Blo 1518456 8649449 := bstep (se 2 (by rfl) ⟨3243543, by rfl⟩ : syracuseStep 8649449 = 6487087) B6487087
theorem B2563049 : Blo 1518456 2563049 := bstep (se 2 (by rfl) ⟨961143, by rfl⟩ : syracuseStep 2563049 = 1922287) B1922287
theorem B9739703 : Blo 1518456 9739703 := bstep (se 1 (by rfl) ⟨7304777, by rfl⟩ : syracuseStep 9739703 = 14609555) B14609555
theorem B14605865 : Blo 1518456 14605865 := bstep (se 2 (by rfl) ⟨5477199, by rfl⟩ : syracuseStep 14605865 = 10954399) B10954399
theorem B98582305 : Blo 1518456 98582305 := bstep (se 2 (by rfl) ⟨36968364, by rfl⟩ : syracuseStep 98582305 = 73936729) B73936729
theorem B6488045 : Blo 1518456 6488045 := bstep (se 3 (by rfl) ⟨1216508, by rfl⟩ : syracuseStep 6488045 = 2433017) B2433017
theorem B8659223 : Blo 1518456 8659223 := bstep (se 1 (by rfl) ⟨6494417, by rfl⟩ : syracuseStep 8659223 = 12988835) B12988835
theorem B9740807 : Blo 1518456 9740807 := bstep (se 1 (by rfl) ⟨7305605, by rfl⟩ : syracuseStep 9740807 = 14611211) B14611211
theorem B2278025 : Blo 1518456 2278025 := bstep (se 2 (by rfl) ⟨854259, by rfl⟩ : syracuseStep 2278025 = 1708519) B1708519
theorem B3416831 : Blo 1518456 3416831 := bstep (se 1 (by rfl) ⟨2562623, by rfl⟩ : syracuseStep 3416831 = 5125247) B5125247
theorem B3416903 : Blo 1518456 3416903 := bstep (se 1 (by rfl) ⟨2562677, by rfl⟩ : syracuseStep 3416903 = 5125355) B5125355
theorem B2884585 : Blo 1518456 2884585 := bstep (se 2 (by rfl) ⟨1081719, by rfl⟩ : syracuseStep 2884585 = 2163439) B2163439
theorem B33293693 : Blo 1518456 33293693 := bstep (se 3 (by rfl) ⟨6242567, by rfl⟩ : syracuseStep 33293693 = 12485135) B12485135
theorem B2279561 : Blo 1518456 2279561 := bstep (se 2 (by rfl) ⟨854835, by rfl⟩ : syracuseStep 2279561 = 1709671) B1709671
theorem B131443073 : Blo 1518456 131443073 := bstep (se 2 (by rfl) ⟨49291152, by rfl⟩ : syracuseStep 131443073 = 98582305) B98582305
theorem B2280479 : Blo 1518456 2280479 := bstep (se 1 (by rfl) ⟨1710359, by rfl⟩ : syracuseStep 2280479 = 3420719) B3420719
theorem B5770399 : Blo 1518456 5770399 := bstep (se 1 (by rfl) ⟨4327799, by rfl⟩ : syracuseStep 5770399 = 8655599) B8655599
theorem B1519039 : Blo 1518456 1519039 := bstep (se 1 (by rfl) ⟨1139279, by rfl⟩ : syracuseStep 1519039 = 2278559) B2278559
theorem B1519855 : Blo 1518456 1519855 := bstep (se 1 (by rfl) ⟨1139891, by rfl⟩ : syracuseStep 1519855 = 2279783) B2279783
theorem B38932973 : Blo 1518456 38932973 := bstep (se 3 (by rfl) ⟨7299932, by rfl⟩ : syracuseStep 38932973 = 14599865) B14599865
theorem B1520175 : Blo 1518456 1520175 := bstep (se 1 (by rfl) ⟨1140131, by rfl⟩ : syracuseStep 1520175 = 2280263) B2280263
theorem B1708699 : Blo 1518456 1708699 := bstep (se 1 (by rfl) ⟨1281524, by rfl⟩ : syracuseStep 1708699 = 2563049) B2563049
theorem B6493135 : Blo 1518456 6493135 := bstep (se 1 (by rfl) ⟨4869851, by rfl⟩ : syracuseStep 6493135 = 9739703) B9739703
theorem B9737243 : Blo 1518456 9737243 := bstep (se 1 (by rfl) ⟨7302932, by rfl⟩ : syracuseStep 9737243 = 14605865) B14605865
theorem B5772617 : Blo 1518456 5772617 := bstep (se 2 (by rfl) ⟨2164731, by rfl⟩ : syracuseStep 5772617 = 4329463) B4329463
theorem B3512479 : Blo 1518456 3512479 := bstep (se 1 (by rfl) ⟨2634359, by rfl⟩ : syracuseStep 3512479 = 5268719) B5268719
theorem B27711973 : Blo 1518456 27711973 := bstep (se 4 (by rfl) ⟨2597997, by rfl⟩ : syracuseStep 27711973 = 5195995) B5195995
theorem B199834631 : Blo 1518456 199834631 := bstep (se 1 (by rfl) ⟨149875973, by rfl⟩ : syracuseStep 199834631 = 299751947) B299751947
theorem B5766299 : Blo 1518456 5766299 := bstep (se 1 (by rfl) ⟨4324724, by rfl⟩ : syracuseStep 5766299 = 8649449) B8649449
theorem B14597405 : Blo 1518456 14597405 := bstep (se 3 (by rfl) ⟨2737013, by rfl⟩ : syracuseStep 14597405 = 5474027) B5474027
theorem B4325363 : Blo 1518456 4325363 := bstep (se 1 (by rfl) ⟨3244022, by rfl⟩ : syracuseStep 4325363 = 6488045) B6488045
theorem B2277887 : Blo 1518456 2277887 := bstep (se 1 (by rfl) ⟨1708415, by rfl⟩ : syracuseStep 2277887 = 3416831) B3416831
theorem B2277935 : Blo 1518456 2277935 := bstep (se 1 (by rfl) ⟨1708451, by rfl⟩ : syracuseStep 2277935 = 3416903) B3416903
theorem B2278265 : Blo 1518456 2278265 := bstep (se 2 (by rfl) ⟨854349, by rfl⟩ : syracuseStep 2278265 = 1708699) B1708699
theorem B7693865 : Blo 1518456 7693865 := bstep (se 2 (by rfl) ⟨2885199, by rfl⟩ : syracuseStep 7693865 = 5770399) B5770399
theorem B3844199 : Blo 1518456 3844199 := bstep (se 1 (by rfl) ⟨2883149, by rfl⟩ : syracuseStep 3844199 = 5766299) B5766299
theorem B25955315 : Blo 1518456 25955315 := bstep (se 1 (by rfl) ⟨19466486, by rfl⟩ : syracuseStep 25955315 = 38932973) B38932973
theorem B1518683 : Blo 1518456 1518683 := bstep (se 1 (by rfl) ⟨1139012, by rfl⟩ : syracuseStep 1518683 = 2278025) B2278025
theorem B36949297 : Blo 1518456 36949297 := bstep (se 2 (by rfl) ⟨13855986, by rfl⟩ : syracuseStep 36949297 = 27711973) B27711973
theorem B6491495 : Blo 1518456 6491495 := bstep (se 1 (by rfl) ⟨4868621, by rfl⟩ : syracuseStep 6491495 = 9737243) B9737243
theorem B22195795 : Blo 1518456 22195795 := bstep (se 1 (by rfl) ⟨16646846, by rfl⟩ : syracuseStep 22195795 = 33293693) B33293693
theorem B3846113 : Blo 1518456 3846113 := bstep (se 2 (by rfl) ⟨1442292, by rfl⟩ : syracuseStep 3846113 = 2884585) B2884585
theorem B1519707 : Blo 1518456 1519707 := bstep (se 1 (by rfl) ⟨1139780, by rfl⟩ : syracuseStep 1519707 = 2279561) B2279561
theorem B133223087 : Blo 1518456 133223087 := bstep (se 1 (by rfl) ⟨99917315, by rfl⟩ : syracuseStep 133223087 = 199834631) B199834631
theorem B1520319 : Blo 1518456 1520319 := bstep (se 1 (by rfl) ⟨1140239, by rfl⟩ : syracuseStep 1520319 = 2280479) B2280479
theorem B5772815 : Blo 1518456 5772815 := bstep (se 1 (by rfl) ⟨4329611, by rfl⟩ : syracuseStep 5772815 = 8659223) B8659223
theorem B4683305 : Blo 1518456 4683305 := bstep (se 2 (by rfl) ⟨1756239, by rfl⟩ : syracuseStep 4683305 = 3512479) B3512479
theorem B6493871 : Blo 1518456 6493871 := bstep (se 1 (by rfl) ⟨4870403, by rfl⟩ : syracuseStep 6493871 = 9740807) B9740807
theorem B3848411 : Blo 1518456 3848411 := bstep (se 1 (by rfl) ⟨2886308, by rfl⟩ : syracuseStep 3848411 = 5772617) B5772617
theorem B8657513 : Blo 1518456 8657513 := bstep (se 2 (by rfl) ⟨3246567, by rfl⟩ : syracuseStep 8657513 = 6493135) B6493135
theorem B87628715 : Blo 1518456 87628715 := bstep (se 1 (by rfl) ⟨65721536, by rfl⟩ : syracuseStep 87628715 = 131443073) B131443073
theorem B9731603 : Blo 1518456 9731603 := bstep (se 1 (by rfl) ⟨7298702, by rfl⟩ : syracuseStep 9731603 = 14597405) B14597405
theorem B2883575 : Blo 1518456 2883575 := bstep (se 1 (by rfl) ⟨2162681, by rfl⟩ : syracuseStep 2883575 = 4325363) B4325363
theorem B5129243 : Blo 1518456 5129243 := bstep (se 1 (by rfl) ⟨3846932, by rfl⟩ : syracuseStep 5129243 = 7693865) B7693865
theorem B2565607 : Blo 1518456 2565607 := bstep (se 1 (by rfl) ⟨1924205, by rfl⟩ : syracuseStep 2565607 = 3848411) B3848411
theorem B58419143 : Blo 1518456 58419143 := bstep (se 1 (by rfl) ⟨43814357, by rfl⟩ : syracuseStep 58419143 = 87628715) B87628715
theorem B17303543 : Blo 1518456 17303543 := bstep (se 1 (by rfl) ⟨12977657, by rfl⟩ : syracuseStep 17303543 = 25955315) B25955315
theorem B4327663 : Blo 1518456 4327663 := bstep (se 1 (by rfl) ⟨3245747, by rfl⟩ : syracuseStep 4327663 = 6491495) B6491495
theorem B1518591 : Blo 1518456 1518591 := bstep (se 1 (by rfl) ⟨1138943, by rfl⟩ : syracuseStep 1518591 = 2277887) B2277887
theorem B1518623 : Blo 1518456 1518623 := bstep (se 1 (by rfl) ⟨1138967, by rfl⟩ : syracuseStep 1518623 = 2277935) B2277935
theorem B1518843 : Blo 1518456 1518843 := bstep (se 1 (by rfl) ⟨1139132, by rfl⟩ : syracuseStep 1518843 = 2278265) B2278265
theorem B4329247 : Blo 1518456 4329247 := bstep (se 1 (by rfl) ⟨3246935, by rfl⟩ : syracuseStep 4329247 = 6493871) B6493871
theorem B12488813 : Blo 1518456 12488813 := bstep (se 3 (by rfl) ⟨2341652, by rfl⟩ : syracuseStep 12488813 = 4683305) B4683305
theorem B5771675 : Blo 1518456 5771675 := bstep (se 1 (by rfl) ⟨4328756, by rfl⟩ : syracuseStep 5771675 = 8657513) B8657513
theorem B29594393 : Blo 1518456 29594393 := bstep (se 2 (by rfl) ⟨11097897, by rfl⟩ : syracuseStep 29594393 = 22195795) B22195795
theorem B1922383 : Blo 1518456 1922383 := bstep (se 1 (by rfl) ⟨1441787, by rfl⟩ : syracuseStep 1922383 = 2883575) B2883575
theorem B3848543 : Blo 1518456 3848543 := bstep (se 1 (by rfl) ⟨2886407, by rfl⟩ : syracuseStep 3848543 = 5772815) B5772815
theorem B25950941 : Blo 1518456 25950941 := bstep (se 3 (by rfl) ⟨4865801, by rfl⟩ : syracuseStep 25950941 = 9731603) B9731603
theorem B2562799 : Blo 1518456 2562799 := bstep (se 1 (by rfl) ⟨1922099, by rfl⟩ : syracuseStep 2562799 = 3844199) B3844199
theorem B49265729 : Blo 1518456 49265729 := bstep (se 2 (by rfl) ⟨18474648, by rfl⟩ : syracuseStep 49265729 = 36949297) B36949297
theorem B355261565 : Blo 1518456 355261565 := bstep (se 3 (by rfl) ⟨66611543, by rfl⟩ : syracuseStep 355261565 = 133223087) B133223087
theorem B2564075 : Blo 1518456 2564075 := bstep (se 1 (by rfl) ⟨1923056, by rfl⟩ : syracuseStep 2564075 = 3846113) B3846113
theorem B3417065 : Blo 1518456 3417065 := bstep (se 2 (by rfl) ⟨1281399, by rfl⟩ : syracuseStep 3417065 = 2562799) B2562799
theorem B38946095 : Blo 1518456 38946095 := bstep (se 1 (by rfl) ⟨29209571, by rfl⟩ : syracuseStep 38946095 = 58419143) B58419143
theorem B11535695 : Blo 1518456 11535695 := bstep (se 1 (by rfl) ⟨8651771, by rfl⟩ : syracuseStep 11535695 = 17303543) B17303543
theorem B2565695 : Blo 1518456 2565695 := bstep (se 1 (by rfl) ⟨1924271, by rfl⟩ : syracuseStep 2565695 = 3848543) B3848543
theorem B32843819 : Blo 1518456 32843819 := bstep (se 1 (by rfl) ⟨24632864, by rfl⟩ : syracuseStep 32843819 = 49265729) B49265729
theorem B236841043 : Blo 1518456 236841043 := bstep (se 1 (by rfl) ⟨177630782, by rfl⟩ : syracuseStep 236841043 = 355261565) B355261565
theorem B8325875 : Blo 1518456 8325875 := bstep (se 1 (by rfl) ⟨6244406, by rfl⟩ : syracuseStep 8325875 = 12488813) B12488813
theorem B5770217 : Blo 1518456 5770217 := bstep (se 2 (by rfl) ⟨2163831, by rfl⟩ : syracuseStep 5770217 = 4327663) B4327663
theorem B19729595 : Blo 1518456 19729595 := bstep (se 1 (by rfl) ⟨14797196, by rfl⟩ : syracuseStep 19729595 = 29594393) B29594393
theorem B3419495 : Blo 1518456 3419495 := bstep (se 1 (by rfl) ⟨2564621, by rfl⟩ : syracuseStep 3419495 = 5129243) B5129243
theorem B3420809 : Blo 1518456 3420809 := bstep (se 2 (by rfl) ⟨1282803, by rfl⟩ : syracuseStep 3420809 = 2565607) B2565607
theorem B5772329 : Blo 1518456 5772329 := bstep (se 2 (by rfl) ⟨2164623, by rfl⟩ : syracuseStep 5772329 = 4329247) B4329247
theorem B1709383 : Blo 1518456 1709383 := bstep (se 1 (by rfl) ⟨1282037, by rfl⟩ : syracuseStep 1709383 = 2564075) B2564075
theorem B3847783 : Blo 1518456 3847783 := bstep (se 1 (by rfl) ⟨2885837, by rfl⟩ : syracuseStep 3847783 = 5771675) B5771675
theorem B2563177 : Blo 1518456 2563177 := bstep (se 2 (by rfl) ⟨961191, by rfl⟩ : syracuseStep 2563177 = 1922383) B1922383
theorem B17300627 : Blo 1518456 17300627 := bstep (se 1 (by rfl) ⟨12975470, by rfl⟩ : syracuseStep 17300627 = 25950941) B25950941
theorem B2278043 : Blo 1518456 2278043 := bstep (se 1 (by rfl) ⟨1708532, by rfl⟩ : syracuseStep 2278043 = 3417065) B3417065
theorem B3417569 : Blo 1518456 3417569 := bstep (se 2 (by rfl) ⟨1281588, by rfl⟩ : syracuseStep 3417569 = 2563177) B2563177
theorem B2279177 : Blo 1518456 2279177 := bstep (se 2 (by rfl) ⟨854691, by rfl⟩ : syracuseStep 2279177 = 1709383) B1709383
theorem B22202333 : Blo 1518456 22202333 := bstep (se 3 (by rfl) ⟨4162937, by rfl⟩ : syracuseStep 22202333 = 8325875) B8325875
theorem B5130377 : Blo 1518456 5130377 := bstep (se 2 (by rfl) ⟨1923891, by rfl⟩ : syracuseStep 5130377 = 3847783) B3847783
theorem B2279663 : Blo 1518456 2279663 := bstep (se 1 (by rfl) ⟨1709747, by rfl⟩ : syracuseStep 2279663 = 3419495) B3419495
theorem B315788057 : Blo 1518456 315788057 := bstep (se 2 (by rfl) ⟨118420521, by rfl⟩ : syracuseStep 315788057 = 236841043) B236841043
theorem B2280539 : Blo 1518456 2280539 := bstep (se 1 (by rfl) ⟨1710404, by rfl⟩ : syracuseStep 2280539 = 3420809) B3420809
theorem B25964063 : Blo 1518456 25964063 := bstep (se 1 (by rfl) ⟨19473047, by rfl⟩ : syracuseStep 25964063 = 38946095) B38946095
theorem B3846811 : Blo 1518456 3846811 := bstep (se 1 (by rfl) ⟨2885108, by rfl⟩ : syracuseStep 3846811 = 5770217) B5770217
theorem B13153063 : Blo 1518456 13153063 := bstep (se 1 (by rfl) ⟨9864797, by rfl⟩ : syracuseStep 13153063 = 19729595) B19729595
theorem B3848219 : Blo 1518456 3848219 := bstep (se 1 (by rfl) ⟨2886164, by rfl⟩ : syracuseStep 3848219 = 5772329) B5772329
theorem B7690463 : Blo 1518456 7690463 := bstep (se 1 (by rfl) ⟨5767847, by rfl⟩ : syracuseStep 7690463 = 11535695) B11535695
theorem B1710463 : Blo 1518456 1710463 := bstep (se 1 (by rfl) ⟨1282847, by rfl⟩ : syracuseStep 1710463 = 2565695) B2565695
theorem B21895879 : Blo 1518456 21895879 := bstep (se 1 (by rfl) ⟨16421909, by rfl⟩ : syracuseStep 21895879 = 32843819) B32843819
theorem B11533751 : Blo 1518456 11533751 := bstep (se 1 (by rfl) ⟨8650313, by rfl⟩ : syracuseStep 11533751 = 17300627) B17300627
theorem B5129081 : Blo 1518456 5129081 := bstep (se 2 (by rfl) ⟨1923405, by rfl⟩ : syracuseStep 5129081 = 3846811) B3846811
theorem B2278379 : Blo 1518456 2278379 := bstep (se 1 (by rfl) ⟨1708784, by rfl⟩ : syracuseStep 2278379 = 3417569) B3417569
theorem B2565479 : Blo 1518456 2565479 := bstep (se 1 (by rfl) ⟨1924109, by rfl⟩ : syracuseStep 2565479 = 3848219) B3848219
theorem B1518695 : Blo 1518456 1518695 := bstep (se 1 (by rfl) ⟨1139021, by rfl⟩ : syracuseStep 1518695 = 2278043) B2278043
theorem B2280617 : Blo 1518456 2280617 := bstep (se 2 (by rfl) ⟨855231, by rfl⟩ : syracuseStep 2280617 = 1710463) B1710463
theorem B1519451 : Blo 1518456 1519451 := bstep (se 1 (by rfl) ⟨1139588, by rfl⟩ : syracuseStep 1519451 = 2279177) B2279177
theorem B3420251 : Blo 1518456 3420251 := bstep (se 1 (by rfl) ⟨2565188, by rfl⟩ : syracuseStep 3420251 = 5130377) B5130377
theorem B1519775 : Blo 1518456 1519775 := bstep (se 1 (by rfl) ⟨1139831, by rfl⟩ : syracuseStep 1519775 = 2279663) B2279663
theorem B1520359 : Blo 1518456 1520359 := bstep (se 1 (by rfl) ⟨1140269, by rfl⟩ : syracuseStep 1520359 = 2280539) B2280539
theorem B7689167 : Blo 1518456 7689167 := bstep (se 1 (by rfl) ⟨5766875, by rfl⟩ : syracuseStep 7689167 = 11533751) B11533751
theorem B29194505 : Blo 1518456 29194505 := bstep (se 2 (by rfl) ⟨10947939, by rfl⟩ : syracuseStep 29194505 = 21895879) B21895879
theorem B17537417 : Blo 1518456 17537417 := bstep (se 2 (by rfl) ⟨6576531, by rfl⟩ : syracuseStep 17537417 = 13153063) B13153063
theorem B14801555 : Blo 1518456 14801555 := bstep (se 1 (by rfl) ⟨11101166, by rfl⟩ : syracuseStep 14801555 = 22202333) B22202333
theorem B5126975 : Blo 1518456 5126975 := bstep (se 1 (by rfl) ⟨3845231, by rfl⟩ : syracuseStep 5126975 = 7690463) B7690463
theorem B210525371 : Blo 1518456 210525371 := bstep (se 1 (by rfl) ⟨157894028, by rfl⟩ : syracuseStep 210525371 = 315788057) B315788057
theorem B17309375 : Blo 1518456 17309375 := bstep (se 1 (by rfl) ⟨12982031, by rfl⟩ : syracuseStep 17309375 = 25964063) B25964063
theorem B11691611 : Blo 1518456 11691611 := bstep (se 1 (by rfl) ⟨8768708, by rfl⟩ : syracuseStep 11691611 = 17537417) B17537417
theorem B3417983 : Blo 1518456 3417983 := bstep (se 1 (by rfl) ⟨2563487, by rfl⟩ : syracuseStep 3417983 = 5126975) B5126975
theorem B2280167 : Blo 1518456 2280167 := bstep (se 1 (by rfl) ⟨1710125, by rfl⟩ : syracuseStep 2280167 = 3420251) B3420251
theorem B3419387 : Blo 1518456 3419387 := bstep (se 1 (by rfl) ⟨2564540, by rfl⟩ : syracuseStep 3419387 = 5129081) B5129081
theorem B1518919 : Blo 1518456 1518919 := bstep (se 1 (by rfl) ⟨1139189, by rfl⟩ : syracuseStep 1518919 = 2278379) B2278379
theorem B9867703 : Blo 1518456 9867703 := bstep (se 1 (by rfl) ⟨7400777, by rfl⟩ : syracuseStep 9867703 = 14801555) B14801555
theorem B1520411 : Blo 1518456 1520411 := bstep (se 1 (by rfl) ⟨1140308, by rfl⟩ : syracuseStep 1520411 = 2280617) B2280617
theorem B140350247 : Blo 1518456 140350247 := bstep (se 1 (by rfl) ⟨105262685, by rfl⟩ : syracuseStep 140350247 = 210525371) B210525371
theorem B11539583 : Blo 1518456 11539583 := bstep (se 1 (by rfl) ⟨8654687, by rfl⟩ : syracuseStep 11539583 = 17309375) B17309375
theorem B5126111 : Blo 1518456 5126111 := bstep (se 1 (by rfl) ⟨3844583, by rfl⟩ : syracuseStep 5126111 = 7689167) B7689167
theorem B1710319 : Blo 1518456 1710319 := bstep (se 1 (by rfl) ⟨1282739, by rfl⟩ : syracuseStep 1710319 = 2565479) B2565479
theorem B19463003 : Blo 1518456 19463003 := bstep (se 1 (by rfl) ⟨14597252, by rfl⟩ : syracuseStep 19463003 = 29194505) B29194505
theorem B13156937 : Blo 1518456 13156937 := bstep (se 2 (by rfl) ⟨4933851, by rfl⟩ : syracuseStep 13156937 = 9867703) B9867703
theorem B7693055 : Blo 1518456 7693055 := bstep (se 1 (by rfl) ⟨5769791, by rfl⟩ : syracuseStep 7693055 = 11539583) B11539583
theorem B2278655 : Blo 1518456 2278655 := bstep (se 1 (by rfl) ⟨1708991, by rfl⟩ : syracuseStep 2278655 = 3417983) B3417983
theorem B3417407 : Blo 1518456 3417407 := bstep (se 1 (by rfl) ⟨2563055, by rfl⟩ : syracuseStep 3417407 = 5126111) B5126111
theorem B2279591 : Blo 1518456 2279591 := bstep (se 1 (by rfl) ⟨1709693, by rfl⟩ : syracuseStep 2279591 = 3419387) B3419387
theorem B2280425 : Blo 1518456 2280425 := bstep (se 2 (by rfl) ⟨855159, by rfl⟩ : syracuseStep 2280425 = 1710319) B1710319
theorem B7794407 : Blo 1518456 7794407 := bstep (se 1 (by rfl) ⟨5845805, by rfl⟩ : syracuseStep 7794407 = 11691611) B11691611
theorem B1520111 : Blo 1518456 1520111 := bstep (se 1 (by rfl) ⟨1140083, by rfl⟩ : syracuseStep 1520111 = 2280167) B2280167
theorem B93566831 : Blo 1518456 93566831 := bstep (se 1 (by rfl) ⟨70175123, by rfl⟩ : syracuseStep 93566831 = 140350247) B140350247
theorem B12975335 : Blo 1518456 12975335 := bstep (se 1 (by rfl) ⟨9731501, by rfl⟩ : syracuseStep 12975335 = 19463003) B19463003
theorem B5128703 : Blo 1518456 5128703 := bstep (se 1 (by rfl) ⟨3846527, by rfl⟩ : syracuseStep 5128703 = 7693055) B7693055
theorem B2278271 : Blo 1518456 2278271 := bstep (se 1 (by rfl) ⟨1708703, by rfl⟩ : syracuseStep 2278271 = 3417407) B3417407
theorem B5196271 : Blo 1518456 5196271 := bstep (se 1 (by rfl) ⟨3897203, by rfl⟩ : syracuseStep 5196271 = 7794407) B7794407
theorem B1519103 : Blo 1518456 1519103 := bstep (se 1 (by rfl) ⟨1139327, by rfl⟩ : syracuseStep 1519103 = 2278655) B2278655
theorem B1519727 : Blo 1518456 1519727 := bstep (se 1 (by rfl) ⟨1139795, by rfl⟩ : syracuseStep 1519727 = 2279591) B2279591
theorem B1520283 : Blo 1518456 1520283 := bstep (se 1 (by rfl) ⟨1140212, by rfl⟩ : syracuseStep 1520283 = 2280425) B2280425
theorem B8771291 : Blo 1518456 8771291 := bstep (se 1 (by rfl) ⟨6578468, by rfl⟩ : syracuseStep 8771291 = 13156937) B13156937
theorem B8650223 : Blo 1518456 8650223 := bstep (se 1 (by rfl) ⟨6487667, by rfl⟩ : syracuseStep 8650223 = 12975335) B12975335
theorem B249511549 : Blo 1518456 249511549 := bstep (se 3 (by rfl) ⟨46783415, by rfl⟩ : syracuseStep 249511549 = 93566831) B93566831
theorem B3419135 : Blo 1518456 3419135 := bstep (se 1 (by rfl) ⟨2564351, by rfl⟩ : syracuseStep 3419135 = 5128703) B5128703
theorem B1518847 : Blo 1518456 1518847 := bstep (se 1 (by rfl) ⟨1139135, by rfl⟩ : syracuseStep 1518847 = 2278271) B2278271
theorem B332682065 : Blo 1518456 332682065 := bstep (se 2 (by rfl) ⟨124755774, by rfl⟩ : syracuseStep 332682065 = 249511549) B249511549
theorem B6928361 : Blo 1518456 6928361 := bstep (se 2 (by rfl) ⟨2598135, by rfl⟩ : syracuseStep 6928361 = 5196271) B5196271
theorem B5847527 : Blo 1518456 5847527 := bstep (se 1 (by rfl) ⟨4385645, by rfl⟩ : syracuseStep 5847527 = 8771291) B8771291
theorem B5766815 : Blo 1518456 5766815 := bstep (se 1 (by rfl) ⟨4325111, by rfl⟩ : syracuseStep 5766815 = 8650223) B8650223
theorem B2279423 : Blo 1518456 2279423 := bstep (se 1 (by rfl) ⟨1709567, by rfl⟩ : syracuseStep 2279423 = 3419135) B3419135
theorem B3844543 : Blo 1518456 3844543 := bstep (se 1 (by rfl) ⟨2883407, by rfl⟩ : syracuseStep 3844543 = 5766815) B5766815
theorem B221788043 : Blo 1518456 221788043 := bstep (se 1 (by rfl) ⟨166341032, by rfl⟩ : syracuseStep 221788043 = 332682065) B332682065
theorem B4618907 : Blo 1518456 4618907 := bstep (se 1 (by rfl) ⟨3464180, by rfl⟩ : syracuseStep 4618907 = 6928361) B6928361
theorem B3898351 : Blo 1518456 3898351 := bstep (se 1 (by rfl) ⟨2923763, by rfl⟩ : syracuseStep 3898351 = 5847527) B5847527
theorem B147858695 : Blo 1518456 147858695 := bstep (se 1 (by rfl) ⟨110894021, by rfl⟩ : syracuseStep 147858695 = 221788043) B221788043
theorem B5197801 : Blo 1518456 5197801 := bstep (se 2 (by rfl) ⟨1949175, by rfl⟩ : syracuseStep 5197801 = 3898351) B3898351
theorem B1519615 : Blo 1518456 1519615 := bstep (se 1 (by rfl) ⟨1139711, by rfl⟩ : syracuseStep 1519615 = 2279423) B2279423
theorem B5126057 : Blo 1518456 5126057 := bstep (se 2 (by rfl) ⟨1922271, by rfl⟩ : syracuseStep 5126057 = 3844543) B3844543
theorem B3079271 : Blo 1518456 3079271 := bstep (se 1 (by rfl) ⟨2309453, by rfl⟩ : syracuseStep 3079271 = 4618907) B4618907
theorem B3417371 : Blo 1518456 3417371 := bstep (se 1 (by rfl) ⟨2563028, by rfl⟩ : syracuseStep 3417371 = 5126057) B5126057
theorem B2052847 : Blo 1518456 2052847 := bstep (se 1 (by rfl) ⟨1539635, by rfl⟩ : syracuseStep 2052847 = 3079271) B3079271
theorem B98572463 : Blo 1518456 98572463 := bstep (se 1 (by rfl) ⟨73929347, by rfl⟩ : syracuseStep 98572463 = 147858695) B147858695
theorem B6930401 : Blo 1518456 6930401 := bstep (se 2 (by rfl) ⟨2598900, by rfl⟩ : syracuseStep 6930401 = 5197801) B5197801
theorem B2278247 : Blo 1518456 2278247 := bstep (se 1 (by rfl) ⟨1708685, by rfl⟩ : syracuseStep 2278247 = 3417371) B3417371
theorem B10948517 : Blo 1518456 10948517 := bstep (se 4 (by rfl) ⟨1026423, by rfl⟩ : syracuseStep 10948517 = 2052847) B2052847
theorem B65714975 : Blo 1518456 65714975 := bstep (se 1 (by rfl) ⟨49286231, by rfl⟩ : syracuseStep 65714975 = 98572463) B98572463
theorem B18481069 : Blo 1518456 18481069 := bstep (se 3 (by rfl) ⟨3465200, by rfl⟩ : syracuseStep 18481069 = 6930401) B6930401
theorem B1518831 : Blo 1518456 1518831 := bstep (se 1 (by rfl) ⟨1139123, by rfl⟩ : syracuseStep 1518831 = 2278247) B2278247
theorem B43809983 : Blo 1518456 43809983 := bstep (se 1 (by rfl) ⟨32857487, by rfl⟩ : syracuseStep 43809983 = 65714975) B65714975
theorem B24641425 : Blo 1518456 24641425 := bstep (se 2 (by rfl) ⟨9240534, by rfl⟩ : syracuseStep 24641425 = 18481069) B18481069
theorem B7299011 : Blo 1518456 7299011 := bstep (se 1 (by rfl) ⟨5474258, by rfl⟩ : syracuseStep 7299011 = 10948517) B10948517
theorem B29206655 : Blo 1518456 29206655 := bstep (se 1 (by rfl) ⟨21904991, by rfl⟩ : syracuseStep 29206655 = 43809983) B43809983
theorem B32855233 : Blo 1518456 32855233 := bstep (se 2 (by rfl) ⟨12320712, by rfl⟩ : syracuseStep 32855233 = 24641425) B24641425
theorem B4866007 : Blo 1518456 4866007 := bstep (se 1 (by rfl) ⟨3649505, by rfl⟩ : syracuseStep 4866007 = 7299011) B7299011
theorem B43806977 : Blo 1518456 43806977 := bstep (se 2 (by rfl) ⟨16427616, by rfl⟩ : syracuseStep 43806977 = 32855233) B32855233
theorem B19471103 : Blo 1518456 19471103 := bstep (se 1 (by rfl) ⟨14603327, by rfl⟩ : syracuseStep 19471103 = 29206655) B29206655
theorem B6488009 : Blo 1518456 6488009 := bstep (se 2 (by rfl) ⟨2433003, by rfl⟩ : syracuseStep 6488009 = 4866007) B4866007
theorem B29204651 : Blo 1518456 29204651 := bstep (se 1 (by rfl) ⟨21903488, by rfl⟩ : syracuseStep 29204651 = 43806977) B43806977
theorem B12980735 : Blo 1518456 12980735 := bstep (se 1 (by rfl) ⟨9735551, by rfl⟩ : syracuseStep 12980735 = 19471103) B19471103
theorem B4325339 : Blo 1518456 4325339 := bstep (se 1 (by rfl) ⟨3244004, by rfl⟩ : syracuseStep 4325339 = 6488009) B6488009
theorem B8653823 : Blo 1518456 8653823 := bstep (se 1 (by rfl) ⟨6490367, by rfl⟩ : syracuseStep 8653823 = 12980735) B12980735
theorem B19469767 : Blo 1518456 19469767 := bstep (se 1 (by rfl) ⟨14602325, by rfl⟩ : syracuseStep 19469767 = 29204651) B29204651
theorem B11534237 : Blo 1518456 11534237 := bstep (se 3 (by rfl) ⟨2162669, by rfl⟩ : syracuseStep 11534237 = 4325339) B4325339
theorem B5769215 : Blo 1518456 5769215 := bstep (se 1 (by rfl) ⟨4326911, by rfl⟩ : syracuseStep 5769215 = 8653823) B8653823
theorem B7689491 : Blo 1518456 7689491 := bstep (se 1 (by rfl) ⟨5767118, by rfl⟩ : syracuseStep 7689491 = 11534237) B11534237
theorem B25959689 : Blo 1518456 25959689 := bstep (se 2 (by rfl) ⟨9734883, by rfl⟩ : syracuseStep 25959689 = 19469767) B19469767
theorem B3846143 : Blo 1518456 3846143 := bstep (se 1 (by rfl) ⟨2884607, by rfl⟩ : syracuseStep 3846143 = 5769215) B5769215
theorem B17306459 : Blo 1518456 17306459 := bstep (se 1 (by rfl) ⟨12979844, by rfl⟩ : syracuseStep 17306459 = 25959689) B25959689
theorem B5126327 : Blo 1518456 5126327 := bstep (se 1 (by rfl) ⟨3844745, by rfl⟩ : syracuseStep 5126327 = 7689491) B7689491
theorem B3417551 : Blo 1518456 3417551 := bstep (se 1 (by rfl) ⟨2563163, by rfl⟩ : syracuseStep 3417551 = 5126327) B5126327
theorem B11537639 : Blo 1518456 11537639 := bstep (se 1 (by rfl) ⟨8653229, by rfl⟩ : syracuseStep 11537639 = 17306459) B17306459
theorem B2564095 : Blo 1518456 2564095 := bstep (se 1 (by rfl) ⟨1923071, by rfl⟩ : syracuseStep 2564095 = 3846143) B3846143
theorem B2278367 : Blo 1518456 2278367 := bstep (se 1 (by rfl) ⟨1708775, by rfl⟩ : syracuseStep 2278367 = 3417551) B3417551
theorem B3418793 : Blo 1518456 3418793 := bstep (se 2 (by rfl) ⟨1282047, by rfl⟩ : syracuseStep 3418793 = 2564095) B2564095
theorem B7691759 : Blo 1518456 7691759 := bstep (se 1 (by rfl) ⟨5768819, by rfl⟩ : syracuseStep 7691759 = 11537639) B11537639
theorem B2279195 : Blo 1518456 2279195 := bstep (se 1 (by rfl) ⟨1709396, by rfl⟩ : syracuseStep 2279195 = 3418793) B3418793
theorem B1518911 : Blo 1518456 1518911 := bstep (se 1 (by rfl) ⟨1139183, by rfl⟩ : syracuseStep 1518911 = 2278367) B2278367
theorem B5127839 : Blo 1518456 5127839 := bstep (se 1 (by rfl) ⟨3845879, by rfl⟩ : syracuseStep 5127839 = 7691759) B7691759
theorem B3418559 : Blo 1518456 3418559 := bstep (se 1 (by rfl) ⟨2563919, by rfl⟩ : syracuseStep 3418559 = 5127839) B5127839
theorem B1519463 : Blo 1518456 1519463 := bstep (se 1 (by rfl) ⟨1139597, by rfl⟩ : syracuseStep 1519463 = 2279195) B2279195
theorem B2279039 : Blo 1518456 2279039 := bstep (se 1 (by rfl) ⟨1709279, by rfl⟩ : syracuseStep 2279039 = 3418559) B3418559
theorem B1519359 : Blo 1518456 1519359 := bstep (se 1 (by rfl) ⟨1139519, by rfl⟩ : syracuseStep 1519359 = 2279039) B2279039

theorem C0 (j : ℕ) (h1 : 379614 ≤ j) (h2 : j ≤ 380113) : Blo 1518456 (4 * j + 3) := by
  interval_cases j
  · exact B1518459
  · exact B1518463
  · exact B1518467
  · exact B1518471
  · exact B1518475
  · exact B1518479
  · exact B1518483
  · exact B1518487
  · exact B1518491
  · exact B1518495
  · exact B1518499
  · exact B1518503
  · exact B1518507
  · exact B1518511
  · exact B1518515
  · exact B1518519
  · exact B1518523
  · exact B1518527
  · exact B1518531
  · exact B1518535
  · exact B1518539
  · exact B1518543
  · exact B1518547
  · exact B1518551
  · exact B1518555
  · exact B1518559
  · exact B1518563
  · exact B1518567
  · exact B1518571
  · exact B1518575
  · exact B1518579
  · exact B1518583
  · exact B1518587
  · exact B1518591
  · exact B1518595
  · exact B1518599
  · exact B1518603
  · exact B1518607
  · exact B1518611
  · exact B1518615
  · exact B1518619
  · exact B1518623
  · exact B1518627
  · exact B1518631
  · exact B1518635
  · exact B1518639
  · exact B1518643
  · exact B1518647
  · exact B1518651
  · exact B1518655
  · exact B1518659
  · exact B1518663
  · exact B1518667
  · exact B1518671
  · exact B1518675
  · exact B1518679
  · exact B1518683
  · exact B1518687
  · exact B1518691
  · exact B1518695
  · exact B1518699
  · exact B1518703
  · exact B1518707
  · exact B1518711
  · exact B1518715
  · exact B1518719
  · exact B1518723
  · exact B1518727
  · exact B1518731
  · exact B1518735
  · exact B1518739
  · exact B1518743
  · exact B1518747
  · exact B1518751
  · exact B1518755
  · exact B1518759
  · exact B1518763
  · exact B1518767
  · exact B1518771
  · exact B1518775
  · exact B1518779
  · exact B1518783
  · exact B1518787
  · exact B1518791
  · exact B1518795
  · exact B1518799
  · exact B1518803
  · exact B1518807
  · exact B1518811
  · exact B1518815
  · exact B1518819
  · exact B1518823
  · exact B1518827
  · exact B1518831
  · exact B1518835
  · exact B1518839
  · exact B1518843
  · exact B1518847
  · exact B1518851
  · exact B1518855
  · exact B1518859
  · exact B1518863
  · exact B1518867
  · exact B1518871
  · exact B1518875
  · exact B1518879
  · exact B1518883
  · exact B1518887
  · exact B1518891
  · exact B1518895
  · exact B1518899
  · exact B1518903
  · exact B1518907
  · exact B1518911
  · exact B1518915
  · exact B1518919
  · exact B1518923
  · exact B1518927
  · exact B1518931
  · exact B1518935
  · exact B1518939
  · exact B1518943
  · exact B1518947
  · exact B1518951
  · exact B1518955
  · exact B1518959
  · exact B1518963
  · exact B1518967
  · exact B1518971
  · exact B1518975
  · exact B1518979
  · exact B1518983
  · exact B1518987
  · exact B1518991
  · exact B1518995
  · exact B1518999
  · exact B1519003
  · exact B1519007
  · exact B1519011
  · exact B1519015
  · exact B1519019
  · exact B1519023
  · exact B1519027
  · exact B1519031
  · exact B1519035
  · exact B1519039
  · exact B1519043
  · exact B1519047
  · exact B1519051
  · exact B1519055
  · exact B1519059
  · exact B1519063
  · exact B1519067
  · exact B1519071
  · exact B1519075
  · exact B1519079
  · exact B1519083
  · exact B1519087
  · exact B1519091
  · exact B1519095
  · exact B1519099
  · exact B1519103
  · exact B1519107
  · exact B1519111
  · exact B1519115
  · exact B1519119
  · exact B1519123
  · exact B1519127
  · exact B1519131
  · exact B1519135
  · exact B1519139
  · exact B1519143
  · exact B1519147
  · exact B1519151
  · exact B1519155
  · exact B1519159
  · exact B1519163
  · exact B1519167
  · exact B1519171
  · exact B1519175
  · exact B1519179
  · exact B1519183
  · exact B1519187
  · exact B1519191
  · exact B1519195
  · exact B1519199
  · exact B1519203
  · exact B1519207
  · exact B1519211
  · exact B1519215
  · exact B1519219
  · exact B1519223
  · exact B1519227
  · exact B1519231
  · exact B1519235
  · exact B1519239
  · exact B1519243
  · exact B1519247
  · exact B1519251
  · exact B1519255
  · exact B1519259
  · exact B1519263
  · exact B1519267
  · exact B1519271
  · exact B1519275
  · exact B1519279
  · exact B1519283
  · exact B1519287
  · exact B1519291
  · exact B1519295
  · exact B1519299
  · exact B1519303
  · exact B1519307
  · exact B1519311
  · exact B1519315
  · exact B1519319
  · exact B1519323
  · exact B1519327
  · exact B1519331
  · exact B1519335
  · exact B1519339
  · exact B1519343
  · exact B1519347
  · exact B1519351
  · exact B1519355
  · exact B1519359
  · exact B1519363
  · exact B1519367
  · exact B1519371
  · exact B1519375
  · exact B1519379
  · exact B1519383
  · exact B1519387
  · exact B1519391
  · exact B1519395
  · exact B1519399
  · exact B1519403
  · exact B1519407
  · exact B1519411
  · exact B1519415
  · exact B1519419
  · exact B1519423
  · exact B1519427
  · exact B1519431
  · exact B1519435
  · exact B1519439
  · exact B1519443
  · exact B1519447
  · exact B1519451
  · exact B1519455
  · exact B1519459
  · exact B1519463
  · exact B1519467
  · exact B1519471
  · exact B1519475
  · exact B1519479
  · exact B1519483
  · exact B1519487
  · exact B1519491
  · exact B1519495
  · exact B1519499
  · exact B1519503
  · exact B1519507
  · exact B1519511
  · exact B1519515
  · exact B1519519
  · exact B1519523
  · exact B1519527
  · exact B1519531
  · exact B1519535
  · exact B1519539
  · exact B1519543
  · exact B1519547
  · exact B1519551
  · exact B1519555
  · exact B1519559
  · exact B1519563
  · exact B1519567
  · exact B1519571
  · exact B1519575
  · exact B1519579
  · exact B1519583
  · exact B1519587
  · exact B1519591
  · exact B1519595
  · exact B1519599
  · exact B1519603
  · exact B1519607
  · exact B1519611
  · exact B1519615
  · exact B1519619
  · exact B1519623
  · exact B1519627
  · exact B1519631
  · exact B1519635
  · exact B1519639
  · exact B1519643
  · exact B1519647
  · exact B1519651
  · exact B1519655
  · exact B1519659
  · exact B1519663
  · exact B1519667
  · exact B1519671
  · exact B1519675
  · exact B1519679
  · exact B1519683
  · exact B1519687
  · exact B1519691
  · exact B1519695
  · exact B1519699
  · exact B1519703
  · exact B1519707
  · exact B1519711
  · exact B1519715
  · exact B1519719
  · exact B1519723
  · exact B1519727
  · exact B1519731
  · exact B1519735
  · exact B1519739
  · exact B1519743
  · exact B1519747
  · exact B1519751
  · exact B1519755
  · exact B1519759
  · exact B1519763
  · exact B1519767
  · exact B1519771
  · exact B1519775
  · exact B1519779
  · exact B1519783
  · exact B1519787
  · exact B1519791
  · exact B1519795
  · exact B1519799
  · exact B1519803
  · exact B1519807
  · exact B1519811
  · exact B1519815
  · exact B1519819
  · exact B1519823
  · exact B1519827
  · exact B1519831
  · exact B1519835
  · exact B1519839
  · exact B1519843
  · exact B1519847
  · exact B1519851
  · exact B1519855
  · exact B1519859
  · exact B1519863
  · exact B1519867
  · exact B1519871
  · exact B1519875
  · exact B1519879
  · exact B1519883
  · exact B1519887
  · exact B1519891
  · exact B1519895
  · exact B1519899
  · exact B1519903
  · exact B1519907
  · exact B1519911
  · exact B1519915
  · exact B1519919
  · exact B1519923
  · exact B1519927
  · exact B1519931
  · exact B1519935
  · exact B1519939
  · exact B1519943
  · exact B1519947
  · exact B1519951
  · exact B1519955
  · exact B1519959
  · exact B1519963
  · exact B1519967
  · exact B1519971
  · exact B1519975
  · exact B1519979
  · exact B1519983
  · exact B1519987
  · exact B1519991
  · exact B1519995
  · exact B1519999
  · exact B1520003
  · exact B1520007
  · exact B1520011
  · exact B1520015
  · exact B1520019
  · exact B1520023
  · exact B1520027
  · exact B1520031
  · exact B1520035
  · exact B1520039
  · exact B1520043
  · exact B1520047
  · exact B1520051
  · exact B1520055
  · exact B1520059
  · exact B1520063
  · exact B1520067
  · exact B1520071
  · exact B1520075
  · exact B1520079
  · exact B1520083
  · exact B1520087
  · exact B1520091
  · exact B1520095
  · exact B1520099
  · exact B1520103
  · exact B1520107
  · exact B1520111
  · exact B1520115
  · exact B1520119
  · exact B1520123
  · exact B1520127
  · exact B1520131
  · exact B1520135
  · exact B1520139
  · exact B1520143
  · exact B1520147
  · exact B1520151
  · exact B1520155
  · exact B1520159
  · exact B1520163
  · exact B1520167
  · exact B1520171
  · exact B1520175
  · exact B1520179
  · exact B1520183
  · exact B1520187
  · exact B1520191
  · exact B1520195
  · exact B1520199
  · exact B1520203
  · exact B1520207
  · exact B1520211
  · exact B1520215
  · exact B1520219
  · exact B1520223
  · exact B1520227
  · exact B1520231
  · exact B1520235
  · exact B1520239
  · exact B1520243
  · exact B1520247
  · exact B1520251
  · exact B1520255
  · exact B1520259
  · exact B1520263
  · exact B1520267
  · exact B1520271
  · exact B1520275
  · exact B1520279
  · exact B1520283
  · exact B1520287
  · exact B1520291
  · exact B1520295
  · exact B1520299
  · exact B1520303
  · exact B1520307
  · exact B1520311
  · exact B1520315
  · exact B1520319
  · exact B1520323
  · exact B1520327
  · exact B1520331
  · exact B1520335
  · exact B1520339
  · exact B1520343
  · exact B1520347
  · exact B1520351
  · exact B1520355
  · exact B1520359
  · exact B1520363
  · exact B1520367
  · exact B1520371
  · exact B1520375
  · exact B1520379
  · exact B1520383
  · exact B1520387
  · exact B1520391
  · exact B1520395
  · exact B1520399
  · exact B1520403
  · exact B1520407
  · exact B1520411
  · exact B1520415
  · exact B1520419
  · exact B1520423
  · exact B1520427
  · exact B1520431
  · exact B1520435
  · exact B1520439
  · exact B1520443
  · exact B1520447
  · exact B1520451
  · exact B1520455

theorem solution (m : ℕ) (hlo : 1518456 ≤ m) (hhi : m ≤ 1520456) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 379614 ≤ j := by omega
    have hj2 : j ≤ 380113 := by omega
    have hb : Blo 1518456 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
