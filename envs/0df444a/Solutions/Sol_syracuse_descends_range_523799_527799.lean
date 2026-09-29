-- Prove2me | solution 1 for syracuse_descends_range_523799_527799
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:26.512266+00:00
-- url     : https://prove2.me/submissions/91b1f06b-02d3-44b4-8795-b8b2566878bf

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


theorem B786437 : Blo 523799 786437 := bbase (se 4 (by rfl) ⟨73728, by rfl⟩ : syracuseStep 786437 = 147457) (by norm_num)
theorem B884749 : Blo 523799 884749 := bbase (se 3 (by rfl) ⟨165890, by rfl⟩ : syracuseStep 884749 = 331781) (by norm_num)
theorem B589837 : Blo 523799 589837 := bbase (se 3 (by rfl) ⟨110594, by rfl⟩ : syracuseStep 589837 = 221189) (by norm_num)
theorem B786461 : Blo 523799 786461 := bbase (se 3 (by rfl) ⟨147461, by rfl⟩ : syracuseStep 786461 = 294923) (by norm_num)
theorem B589873 : Blo 523799 589873 := bbase (se 2 (by rfl) ⟨221202, by rfl⟩ : syracuseStep 589873 = 442405) (by norm_num)
theorem B1769525 : Blo 523799 1769525 := bbase (se 5 (by rfl) ⟨82946, by rfl⟩ : syracuseStep 1769525 = 165893) (by norm_num)
theorem B1179701 : Blo 523799 1179701 := bbase (se 5 (by rfl) ⟨55298, by rfl⟩ : syracuseStep 1179701 = 110597) (by norm_num)
theorem B786485 : Blo 523799 786485 := bbase (se 5 (by rfl) ⟨36866, by rfl⟩ : syracuseStep 786485 = 73733) (by norm_num)
theorem B786509 : Blo 523799 786509 := bbase (se 3 (by rfl) ⟨147470, by rfl⟩ : syracuseStep 786509 = 294941) (by norm_num)
theorem B589909 : Blo 523799 589909 := bbase (se 8 (by rfl) ⟨3456, by rfl⟩ : syracuseStep 589909 = 6913) (by norm_num)
theorem B884837 : Blo 523799 884837 := bbase (se 4 (by rfl) ⟨82953, by rfl⟩ : syracuseStep 884837 = 165907) (by norm_num)
theorem B786533 : Blo 523799 786533 := bbase (se 4 (by rfl) ⟨73737, by rfl⟩ : syracuseStep 786533 = 147475) (by norm_num)
theorem B589945 : Blo 523799 589945 := bbase (se 2 (by rfl) ⟨221229, by rfl⟩ : syracuseStep 589945 = 442459) (by norm_num)
theorem B1179773 : Blo 523799 1179773 := bbase (se 3 (by rfl) ⟨221207, by rfl⟩ : syracuseStep 1179773 = 442415) (by norm_num)
theorem B786557 : Blo 523799 786557 := bbase (se 3 (by rfl) ⟨147479, by rfl⟩ : syracuseStep 786557 = 294959) (by norm_num)
theorem B786581 : Blo 523799 786581 := bbase (se 6 (by rfl) ⟨18435, by rfl⟩ : syracuseStep 786581 = 36871) (by norm_num)
theorem B589981 : Blo 523799 589981 := bbase (se 3 (by rfl) ⟨110621, by rfl⟩ : syracuseStep 589981 = 221243) (by norm_num)
theorem B786605 : Blo 523799 786605 := bbase (se 3 (by rfl) ⟨147488, by rfl⟩ : syracuseStep 786605 = 294977) (by norm_num)
theorem B590017 : Blo 523799 590017 := bbase (se 2 (by rfl) ⟨221256, by rfl⟩ : syracuseStep 590017 = 442513) (by norm_num)
theorem B1179845 : Blo 523799 1179845 := bbase (se 4 (by rfl) ⟨110610, by rfl⟩ : syracuseStep 1179845 = 221221) (by norm_num)
theorem B786629 : Blo 523799 786629 := bbase (se 4 (by rfl) ⟨73746, by rfl⟩ : syracuseStep 786629 = 147493) (by norm_num)
theorem B786653 : Blo 523799 786653 := bbase (se 3 (by rfl) ⟨147497, by rfl⟩ : syracuseStep 786653 = 294995) (by norm_num)
theorem B884965 : Blo 523799 884965 := bbase (se 4 (by rfl) ⟨82965, by rfl⟩ : syracuseStep 884965 = 165931) (by norm_num)
theorem B590053 : Blo 523799 590053 := bbase (se 4 (by rfl) ⟨55317, by rfl⟩ : syracuseStep 590053 = 110635) (by norm_num)
theorem B786677 : Blo 523799 786677 := bbase (se 5 (by rfl) ⟨36875, by rfl⟩ : syracuseStep 786677 = 73751) (by norm_num)
theorem B590089 : Blo 523799 590089 := bbase (se 2 (by rfl) ⟨221283, by rfl⟩ : syracuseStep 590089 = 442567) (by norm_num)
theorem B1179917 : Blo 523799 1179917 := bbase (se 3 (by rfl) ⟨221234, by rfl⟩ : syracuseStep 1179917 = 442469) (by norm_num)
theorem B786701 : Blo 523799 786701 := bbase (se 3 (by rfl) ⟨147506, by rfl⟩ : syracuseStep 786701 = 295013) (by norm_num)
theorem B786725 : Blo 523799 786725 := bbase (se 4 (by rfl) ⟨73755, by rfl⟩ : syracuseStep 786725 = 147511) (by norm_num)
theorem B590125 : Blo 523799 590125 := bbase (se 3 (by rfl) ⟨110648, by rfl⟩ : syracuseStep 590125 = 221297) (by norm_num)
theorem B885053 : Blo 523799 885053 := bbase (se 3 (by rfl) ⟨165947, by rfl⟩ : syracuseStep 885053 = 331895) (by norm_num)
theorem B786749 : Blo 523799 786749 := bbase (se 3 (by rfl) ⟨147515, by rfl⟩ : syracuseStep 786749 = 295031) (by norm_num)
theorem B590161 : Blo 523799 590161 := bbase (se 2 (by rfl) ⟨221310, by rfl⟩ : syracuseStep 590161 = 442621) (by norm_num)
theorem B1179989 : Blo 523799 1179989 := bbase (se 10 (by rfl) ⟨1728, by rfl⟩ : syracuseStep 1179989 = 3457) (by norm_num)
theorem B786773 : Blo 523799 786773 := bbase (se 10 (by rfl) ⟨1152, by rfl⟩ : syracuseStep 786773 = 2305) (by norm_num)
theorem B786797 : Blo 523799 786797 := bbase (se 3 (by rfl) ⟨147524, by rfl⟩ : syracuseStep 786797 = 295049) (by norm_num)
theorem B590197 : Blo 523799 590197 := bbase (se 5 (by rfl) ⟨27665, by rfl⟩ : syracuseStep 590197 = 55331) (by norm_num)
theorem B2130293 : Blo 523799 2130293 := bbase (se 5 (by rfl) ⟨99857, by rfl⟩ : syracuseStep 2130293 = 199715) (by norm_num)
theorem B786821 : Blo 523799 786821 := bbase (se 4 (by rfl) ⟨73764, by rfl⟩ : syracuseStep 786821 = 147529) (by norm_num)
theorem B590233 : Blo 523799 590233 := bbase (se 2 (by rfl) ⟨221337, by rfl⟩ : syracuseStep 590233 = 442675) (by norm_num)
theorem B1180061 : Blo 523799 1180061 := bbase (se 3 (by rfl) ⟨221261, by rfl⟩ : syracuseStep 1180061 = 442523) (by norm_num)
theorem B786845 : Blo 523799 786845 := bbase (se 3 (by rfl) ⟨147533, by rfl⟩ : syracuseStep 786845 = 295067) (by norm_num)
theorem B786869 : Blo 523799 786869 := bbase (se 5 (by rfl) ⟨36884, by rfl⟩ : syracuseStep 786869 = 73769) (by norm_num)
theorem B885181 : Blo 523799 885181 := bbase (se 3 (by rfl) ⟨165971, by rfl⟩ : syracuseStep 885181 = 331943) (by norm_num)
theorem B590269 : Blo 523799 590269 := bbase (se 3 (by rfl) ⟨110675, by rfl⟩ : syracuseStep 590269 = 221351) (by norm_num)
theorem B786893 : Blo 523799 786893 := bbase (se 3 (by rfl) ⟨147542, by rfl⟩ : syracuseStep 786893 = 295085) (by norm_num)
theorem B590305 : Blo 523799 590305 := bbase (se 2 (by rfl) ⟨221364, by rfl⟩ : syracuseStep 590305 = 442729) (by norm_num)
theorem B2654693 : Blo 523799 2654693 := bbase (se 4 (by rfl) ⟨248877, by rfl⟩ : syracuseStep 2654693 = 497755) (by norm_num)
theorem B1769957 : Blo 523799 1769957 := bbase (se 4 (by rfl) ⟨165933, by rfl⟩ : syracuseStep 1769957 = 331867) (by norm_num)
theorem B1180133 : Blo 523799 1180133 := bbase (se 4 (by rfl) ⟨110637, by rfl⟩ : syracuseStep 1180133 = 221275) (by norm_num)
theorem B786917 : Blo 523799 786917 := bbase (se 4 (by rfl) ⟨73773, by rfl⟩ : syracuseStep 786917 = 147547) (by norm_num)
theorem B1901045 : Blo 523799 1901045 := bbase (se 5 (by rfl) ⟨89111, by rfl⟩ : syracuseStep 1901045 = 178223) (by norm_num)
theorem B786941 : Blo 523799 786941 := bbase (se 3 (by rfl) ⟨147551, by rfl⟩ : syracuseStep 786941 = 295103) (by norm_num)
theorem B590341 : Blo 523799 590341 := bbase (se 4 (by rfl) ⟨55344, by rfl⟩ : syracuseStep 590341 = 110689) (by norm_num)
theorem B885269 : Blo 523799 885269 := bbase (se 6 (by rfl) ⟨20748, by rfl⟩ : syracuseStep 885269 = 41497) (by norm_num)
theorem B786965 : Blo 523799 786965 := bbase (se 6 (by rfl) ⟨18444, by rfl⟩ : syracuseStep 786965 = 36889) (by norm_num)
theorem B590377 : Blo 523799 590377 := bbase (se 2 (by rfl) ⟨221391, by rfl⟩ : syracuseStep 590377 = 442783) (by norm_num)
theorem B1180205 : Blo 523799 1180205 := bbase (se 3 (by rfl) ⟨221288, by rfl⟩ : syracuseStep 1180205 = 442577) (by norm_num)
theorem B786989 : Blo 523799 786989 := bbase (se 3 (by rfl) ⟨147560, by rfl⟩ : syracuseStep 786989 = 295121) (by norm_num)
theorem B787013 : Blo 523799 787013 := bbase (se 4 (by rfl) ⟨73782, by rfl⟩ : syracuseStep 787013 = 147565) (by norm_num)
theorem B590413 : Blo 523799 590413 := bbase (se 3 (by rfl) ⟨110702, by rfl⟩ : syracuseStep 590413 = 221405) (by norm_num)
theorem B950869 : Blo 523799 950869 := bbase (se 8 (by rfl) ⟨5571, by rfl⟩ : syracuseStep 950869 = 11143) (by norm_num)
theorem B787037 : Blo 523799 787037 := bbase (se 3 (by rfl) ⟨147569, by rfl⟩ : syracuseStep 787037 = 295139) (by norm_num)
theorem B590449 : Blo 523799 590449 := bbase (se 2 (by rfl) ⟨221418, by rfl⟩ : syracuseStep 590449 = 442837) (by norm_num)
theorem B1180277 : Blo 523799 1180277 := bbase (se 5 (by rfl) ⟨55325, by rfl⟩ : syracuseStep 1180277 = 110651) (by norm_num)
theorem B787061 : Blo 523799 787061 := bbase (se 5 (by rfl) ⟨36893, by rfl⟩ : syracuseStep 787061 = 73787) (by norm_num)
theorem B787085 : Blo 523799 787085 := bbase (se 3 (by rfl) ⟨147578, by rfl⟩ : syracuseStep 787085 = 295157) (by norm_num)
theorem B885397 : Blo 523799 885397 := bbase (se 6 (by rfl) ⟨20751, by rfl⟩ : syracuseStep 885397 = 41503) (by norm_num)
theorem B590485 : Blo 523799 590485 := bbase (se 6 (by rfl) ⟨13839, by rfl⟩ : syracuseStep 590485 = 27679) (by norm_num)
theorem B787109 : Blo 523799 787109 := bbase (se 4 (by rfl) ⟨73791, by rfl⟩ : syracuseStep 787109 = 147583) (by norm_num)
theorem B1999525 : Blo 523799 1999525 := bbase (se 4 (by rfl) ⟨187455, by rfl⟩ : syracuseStep 1999525 = 374911) (by norm_num)
theorem B590521 : Blo 523799 590521 := bbase (se 2 (by rfl) ⟨221445, by rfl⟩ : syracuseStep 590521 = 442891) (by norm_num)
theorem B1180349 : Blo 523799 1180349 := bbase (se 3 (by rfl) ⟨221315, by rfl⟩ : syracuseStep 1180349 = 442631) (by norm_num)
theorem B787133 : Blo 523799 787133 := bbase (se 3 (by rfl) ⟨147587, by rfl⟩ : syracuseStep 787133 = 295175) (by norm_num)
theorem B787157 : Blo 523799 787157 := bbase (se 7 (by rfl) ⟨9224, by rfl⟩ : syracuseStep 787157 = 18449) (by norm_num)
theorem B590557 : Blo 523799 590557 := bbase (se 3 (by rfl) ⟨110729, by rfl⟩ : syracuseStep 590557 = 221459) (by norm_num)
theorem B885485 : Blo 523799 885485 := bbase (se 3 (by rfl) ⟨166028, by rfl⟩ : syracuseStep 885485 = 332057) (by norm_num)
theorem B787181 : Blo 523799 787181 := bbase (se 3 (by rfl) ⟨147596, by rfl⟩ : syracuseStep 787181 = 295193) (by norm_num)
theorem B590593 : Blo 523799 590593 := bbase (se 2 (by rfl) ⟨221472, by rfl⟩ : syracuseStep 590593 = 442945) (by norm_num)
theorem B1180421 : Blo 523799 1180421 := bbase (se 4 (by rfl) ⟨110664, by rfl⟩ : syracuseStep 1180421 = 221329) (by norm_num)
theorem B787205 : Blo 523799 787205 := bbase (se 4 (by rfl) ⟨73800, by rfl⟩ : syracuseStep 787205 = 147601) (by norm_num)
theorem B1901333 : Blo 523799 1901333 := bbase (se 6 (by rfl) ⟨44562, by rfl⟩ : syracuseStep 1901333 = 89125) (by norm_num)
theorem B787229 : Blo 523799 787229 := bbase (se 3 (by rfl) ⟨147605, by rfl⟩ : syracuseStep 787229 = 295211) (by norm_num)
theorem B590629 : Blo 523799 590629 := bbase (se 4 (by rfl) ⟨55371, by rfl⟩ : syracuseStep 590629 = 110743) (by norm_num)
theorem B787253 : Blo 523799 787253 := bbase (se 5 (by rfl) ⟨36902, by rfl⟩ : syracuseStep 787253 = 73805) (by norm_num)
theorem B590665 : Blo 523799 590665 := bbase (se 2 (by rfl) ⟨221499, by rfl⟩ : syracuseStep 590665 = 442999) (by norm_num)
theorem B1180493 : Blo 523799 1180493 := bbase (se 3 (by rfl) ⟨221342, by rfl⟩ : syracuseStep 1180493 = 442685) (by norm_num)
theorem B787277 : Blo 523799 787277 := bbase (se 3 (by rfl) ⟨147614, by rfl⟩ : syracuseStep 787277 = 295229) (by norm_num)
theorem B787301 : Blo 523799 787301 := bbase (se 4 (by rfl) ⟨73809, by rfl⟩ : syracuseStep 787301 = 147619) (by norm_num)
theorem B885613 : Blo 523799 885613 := bbase (se 3 (by rfl) ⟨166052, by rfl⟩ : syracuseStep 885613 = 332105) (by norm_num)
theorem B590701 : Blo 523799 590701 := bbase (se 3 (by rfl) ⟨110756, by rfl⟩ : syracuseStep 590701 = 221513) (by norm_num)
theorem B787325 : Blo 523799 787325 := bbase (se 3 (by rfl) ⟨147623, by rfl⟩ : syracuseStep 787325 = 295247) (by norm_num)
theorem B590737 : Blo 523799 590737 := bbase (se 2 (by rfl) ⟨221526, by rfl⟩ : syracuseStep 590737 = 443053) (by norm_num)
theorem B1770389 : Blo 523799 1770389 := bbase (se 6 (by rfl) ⟨41493, by rfl⟩ : syracuseStep 1770389 = 82987) (by norm_num)
theorem B1180565 : Blo 523799 1180565 := bbase (se 6 (by rfl) ⟨27669, by rfl⟩ : syracuseStep 1180565 = 55339) (by norm_num)
theorem B787349 : Blo 523799 787349 := bbase (se 6 (by rfl) ⟨18453, by rfl⟩ : syracuseStep 787349 = 36907) (by norm_num)
theorem B787373 : Blo 523799 787373 := bbase (se 3 (by rfl) ⟨147632, by rfl⟩ : syracuseStep 787373 = 295265) (by norm_num)
theorem B590773 : Blo 523799 590773 := bbase (se 5 (by rfl) ⟨27692, by rfl⟩ : syracuseStep 590773 = 55385) (by norm_num)
theorem B885701 : Blo 523799 885701 := bbase (se 4 (by rfl) ⟨83034, by rfl⟩ : syracuseStep 885701 = 166069) (by norm_num)
theorem B787397 : Blo 523799 787397 := bbase (se 4 (by rfl) ⟨73818, by rfl⟩ : syracuseStep 787397 = 147637) (by norm_num)
theorem B1999829 : Blo 523799 1999829 := bbase (se 7 (by rfl) ⟨23435, by rfl⟩ : syracuseStep 1999829 = 46871) (by norm_num)
theorem B590809 : Blo 523799 590809 := bbase (se 2 (by rfl) ⟨221553, by rfl⟩ : syracuseStep 590809 = 443107) (by norm_num)
theorem B1180637 : Blo 523799 1180637 := bbase (se 3 (by rfl) ⟨221369, by rfl⟩ : syracuseStep 1180637 = 442739) (by norm_num)
theorem B787421 : Blo 523799 787421 := bbase (se 3 (by rfl) ⟨147641, by rfl⟩ : syracuseStep 787421 = 295283) (by norm_num)
theorem B2556917 : Blo 523799 2556917 := bbase (se 5 (by rfl) ⟨119855, by rfl⟩ : syracuseStep 2556917 = 239711) (by norm_num)
theorem B787445 : Blo 523799 787445 := bbase (se 5 (by rfl) ⟨36911, by rfl⟩ : syracuseStep 787445 = 73823) (by norm_num)
theorem B590845 : Blo 523799 590845 := bbase (se 3 (by rfl) ⟨110783, by rfl⟩ : syracuseStep 590845 = 221567) (by norm_num)
theorem B787469 : Blo 523799 787469 := bbase (se 3 (by rfl) ⟨147650, by rfl⟩ : syracuseStep 787469 = 295301) (by norm_num)
theorem B590881 : Blo 523799 590881 := bbase (se 2 (by rfl) ⟨221580, by rfl⟩ : syracuseStep 590881 = 443161) (by norm_num)
theorem B1180709 : Blo 523799 1180709 := bbase (se 4 (by rfl) ⟨110691, by rfl⟩ : syracuseStep 1180709 = 221383) (by norm_num)
theorem B787493 : Blo 523799 787493 := bbase (se 4 (by rfl) ⟨73827, by rfl⟩ : syracuseStep 787493 = 147655) (by norm_num)
theorem B787517 : Blo 523799 787517 := bbase (se 3 (by rfl) ⟨147659, by rfl⟩ : syracuseStep 787517 = 295319) (by norm_num)
theorem B885829 : Blo 523799 885829 := bbase (se 4 (by rfl) ⟨83046, by rfl⟩ : syracuseStep 885829 = 166093) (by norm_num)
theorem B590917 : Blo 523799 590917 := bbase (se 4 (by rfl) ⟨55398, by rfl⟩ : syracuseStep 590917 = 110797) (by norm_num)
theorem B787541 : Blo 523799 787541 := bbase (se 8 (by rfl) ⟨4614, by rfl⟩ : syracuseStep 787541 = 9229) (by norm_num)
theorem B590953 : Blo 523799 590953 := bbase (se 2 (by rfl) ⟨221607, by rfl⟩ : syracuseStep 590953 = 443215) (by norm_num)
theorem B1180781 : Blo 523799 1180781 := bbase (se 3 (by rfl) ⟨221396, by rfl⟩ : syracuseStep 1180781 = 442793) (by norm_num)
theorem B787565 : Blo 523799 787565 := bbase (se 3 (by rfl) ⟨147668, by rfl⟩ : syracuseStep 787565 = 295337) (by norm_num)
theorem B787589 : Blo 523799 787589 := bbase (se 4 (by rfl) ⟨73836, by rfl⟩ : syracuseStep 787589 = 147673) (by norm_num)
theorem B590989 : Blo 523799 590989 := bbase (se 3 (by rfl) ⟨110810, by rfl⟩ : syracuseStep 590989 = 221621) (by norm_num)
theorem B885917 : Blo 523799 885917 := bbase (se 3 (by rfl) ⟨166109, by rfl⟩ : syracuseStep 885917 = 332219) (by norm_num)
theorem B787613 : Blo 523799 787613 := bbase (se 3 (by rfl) ⟨147677, by rfl⟩ : syracuseStep 787613 = 295355) (by norm_num)
theorem B591025 : Blo 523799 591025 := bbase (se 2 (by rfl) ⟨221634, by rfl⟩ : syracuseStep 591025 = 443269) (by norm_num)
theorem B1180853 : Blo 523799 1180853 := bbase (se 5 (by rfl) ⟨55352, by rfl⟩ : syracuseStep 1180853 = 110705) (by norm_num)
theorem B787637 : Blo 523799 787637 := bbase (se 5 (by rfl) ⟨36920, by rfl⟩ : syracuseStep 787637 = 73841) (by norm_num)
theorem B787661 : Blo 523799 787661 := bbase (se 3 (by rfl) ⟨147686, by rfl⟩ : syracuseStep 787661 = 295373) (by norm_num)
theorem B591061 : Blo 523799 591061 := bbase (se 7 (by rfl) ⟨6926, by rfl⟩ : syracuseStep 591061 = 13853) (by norm_num)
theorem B787685 : Blo 523799 787685 := bbase (se 4 (by rfl) ⟨73845, by rfl⟩ : syracuseStep 787685 = 147691) (by norm_num)
theorem B591097 : Blo 523799 591097 := bbase (se 2 (by rfl) ⟨221661, by rfl⟩ : syracuseStep 591097 = 443323) (by norm_num)
theorem B1180925 : Blo 523799 1180925 := bbase (se 3 (by rfl) ⟨221423, by rfl⟩ : syracuseStep 1180925 = 442847) (by norm_num)
theorem B787709 : Blo 523799 787709 := bbase (se 3 (by rfl) ⟨147695, by rfl⟩ : syracuseStep 787709 = 295391) (by norm_num)
theorem B787733 : Blo 523799 787733 := bbase (se 6 (by rfl) ⟨18462, by rfl⟩ : syracuseStep 787733 = 36925) (by norm_num)
theorem B886045 : Blo 523799 886045 := bbase (se 3 (by rfl) ⟨166133, by rfl⟩ : syracuseStep 886045 = 332267) (by norm_num)
theorem B591133 : Blo 523799 591133 := bbase (se 3 (by rfl) ⟨110837, by rfl⟩ : syracuseStep 591133 = 221675) (by norm_num)
theorem B787757 : Blo 523799 787757 := bbase (se 3 (by rfl) ⟨147704, by rfl⟩ : syracuseStep 787757 = 295409) (by norm_num)
theorem B591169 : Blo 523799 591169 := bbase (se 2 (by rfl) ⟨221688, by rfl⟩ : syracuseStep 591169 = 443377) (by norm_num)
theorem B1770821 : Blo 523799 1770821 := bbase (se 4 (by rfl) ⟨166014, by rfl⟩ : syracuseStep 1770821 = 332029) (by norm_num)
theorem B1180997 : Blo 523799 1180997 := bbase (se 4 (by rfl) ⟨110718, by rfl⟩ : syracuseStep 1180997 = 221437) (by norm_num)
theorem B787781 : Blo 523799 787781 := bbase (se 4 (by rfl) ⟨73854, by rfl⟩ : syracuseStep 787781 = 147709) (by norm_num)
theorem B787805 : Blo 523799 787805 := bbase (se 3 (by rfl) ⟨147713, by rfl⟩ : syracuseStep 787805 = 295427) (by norm_num)
theorem B591205 : Blo 523799 591205 := bbase (se 4 (by rfl) ⟨55425, by rfl⟩ : syracuseStep 591205 = 110851) (by norm_num)
theorem B886133 : Blo 523799 886133 := bbase (se 5 (by rfl) ⟨41537, by rfl⟩ : syracuseStep 886133 = 83075) (by norm_num)
theorem B787829 : Blo 523799 787829 := bbase (se 5 (by rfl) ⟨36929, by rfl⟩ : syracuseStep 787829 = 73859) (by norm_num)
theorem B591241 : Blo 523799 591241 := bbase (se 2 (by rfl) ⟨221715, by rfl⟩ : syracuseStep 591241 = 443431) (by norm_num)
theorem B1181069 : Blo 523799 1181069 := bbase (se 3 (by rfl) ⟨221450, by rfl⟩ : syracuseStep 1181069 = 442901) (by norm_num)
theorem B787853 : Blo 523799 787853 := bbase (se 3 (by rfl) ⟨147722, by rfl⟩ : syracuseStep 787853 = 295445) (by norm_num)
theorem B787877 : Blo 523799 787877 := bbase (se 4 (by rfl) ⟨73863, by rfl⟩ : syracuseStep 787877 = 147727) (by norm_num)
theorem B591277 : Blo 523799 591277 := bbase (se 3 (by rfl) ⟨110864, by rfl⟩ : syracuseStep 591277 = 221729) (by norm_num)
theorem B787901 : Blo 523799 787901 := bbase (se 3 (by rfl) ⟨147731, by rfl⟩ : syracuseStep 787901 = 295463) (by norm_num)
theorem B591313 : Blo 523799 591313 := bbase (se 2 (by rfl) ⟨221742, by rfl⟩ : syracuseStep 591313 = 443485) (by norm_num)
theorem B1181141 : Blo 523799 1181141 := bbase (se 7 (by rfl) ⟨13841, by rfl⟩ : syracuseStep 1181141 = 27683) (by norm_num)
theorem B787925 : Blo 523799 787925 := bbase (se 7 (by rfl) ⟨9233, by rfl⟩ : syracuseStep 787925 = 18467) (by norm_num)
theorem B1705445 : Blo 523799 1705445 := bbase (se 4 (by rfl) ⟨159885, by rfl⟩ : syracuseStep 1705445 = 319771) (by norm_num)
theorem B787949 : Blo 523799 787949 := bbase (se 3 (by rfl) ⟨147740, by rfl⟩ : syracuseStep 787949 = 295481) (by norm_num)
theorem B886261 : Blo 523799 886261 := bbase (se 5 (by rfl) ⟨41543, by rfl⟩ : syracuseStep 886261 = 83087) (by norm_num)
theorem B591349 : Blo 523799 591349 := bbase (se 5 (by rfl) ⟨27719, by rfl⟩ : syracuseStep 591349 = 55439) (by norm_num)
theorem B787973 : Blo 523799 787973 := bbase (se 4 (by rfl) ⟨73872, by rfl⟩ : syracuseStep 787973 = 147745) (by norm_num)
theorem B591385 : Blo 523799 591385 := bbase (se 2 (by rfl) ⟨221769, by rfl⟩ : syracuseStep 591385 = 443539) (by norm_num)
theorem B1181213 : Blo 523799 1181213 := bbase (se 3 (by rfl) ⟨221477, by rfl⟩ : syracuseStep 1181213 = 442955) (by norm_num)
theorem B787997 : Blo 523799 787997 := bbase (se 3 (by rfl) ⟨147749, by rfl⟩ : syracuseStep 787997 = 295499) (by norm_num)
theorem B788021 : Blo 523799 788021 := bbase (se 5 (by rfl) ⟨36938, by rfl⟩ : syracuseStep 788021 = 73877) (by norm_num)
theorem B591421 : Blo 523799 591421 := bbase (se 3 (by rfl) ⟨110891, by rfl⟩ : syracuseStep 591421 = 221783) (by norm_num)
theorem B886349 : Blo 523799 886349 := bbase (se 3 (by rfl) ⟨166190, by rfl⟩ : syracuseStep 886349 = 332381) (by norm_num)
theorem B788045 : Blo 523799 788045 := bbase (se 3 (by rfl) ⟨147758, by rfl⟩ : syracuseStep 788045 = 295517) (by norm_num)
theorem B8619605 : Blo 523799 8619605 := bbase (se 8 (by rfl) ⟨50505, by rfl⟩ : syracuseStep 8619605 = 101011) (by norm_num)
theorem B591457 : Blo 523799 591457 := bbase (se 2 (by rfl) ⟨221796, by rfl⟩ : syracuseStep 591457 = 443593) (by norm_num)
theorem B1181285 : Blo 523799 1181285 := bbase (se 4 (by rfl) ⟨110745, by rfl⟩ : syracuseStep 1181285 = 221491) (by norm_num)
theorem B788069 : Blo 523799 788069 := bbase (se 4 (by rfl) ⟨73881, by rfl⟩ : syracuseStep 788069 = 147763) (by norm_num)
theorem B788093 : Blo 523799 788093 := bbase (se 3 (by rfl) ⟨147767, by rfl⟩ : syracuseStep 788093 = 295535) (by norm_num)
theorem B591493 : Blo 523799 591493 := bbase (se 4 (by rfl) ⟨55452, by rfl⟩ : syracuseStep 591493 = 110905) (by norm_num)
theorem B2393749 : Blo 523799 2393749 := bbase (se 6 (by rfl) ⟨56103, by rfl⟩ : syracuseStep 2393749 = 112207) (by norm_num)
theorem B788117 : Blo 523799 788117 := bbase (se 6 (by rfl) ⟨18471, by rfl⟩ : syracuseStep 788117 = 36943) (by norm_num)
theorem B591529 : Blo 523799 591529 := bbase (se 2 (by rfl) ⟨221823, by rfl⟩ : syracuseStep 591529 = 443647) (by norm_num)
theorem B1181357 : Blo 523799 1181357 := bbase (se 3 (by rfl) ⟨221504, by rfl⟩ : syracuseStep 1181357 = 443009) (by norm_num)
theorem B788141 : Blo 523799 788141 := bbase (se 3 (by rfl) ⟨147776, by rfl⟩ : syracuseStep 788141 = 295553) (by norm_num)
theorem B788165 : Blo 523799 788165 := bbase (se 4 (by rfl) ⟨73890, by rfl⟩ : syracuseStep 788165 = 147781) (by norm_num)
theorem B886477 : Blo 523799 886477 := bbase (se 3 (by rfl) ⟨166214, by rfl⟩ : syracuseStep 886477 = 332429) (by norm_num)
theorem B591565 : Blo 523799 591565 := bbase (se 3 (by rfl) ⟨110918, by rfl⟩ : syracuseStep 591565 = 221837) (by norm_num)
theorem B788189 : Blo 523799 788189 := bbase (se 3 (by rfl) ⟨147785, by rfl⟩ : syracuseStep 788189 = 295571) (by norm_num)
theorem B2623205 : Blo 523799 2623205 := bbase (se 4 (by rfl) ⟨245925, by rfl⟩ : syracuseStep 2623205 = 491851) (by norm_num)
theorem B591601 : Blo 523799 591601 := bbase (se 2 (by rfl) ⟨221850, by rfl⟩ : syracuseStep 591601 = 443701) (by norm_num)
theorem B2655989 : Blo 523799 2655989 := bbase (se 5 (by rfl) ⟨124499, by rfl⟩ : syracuseStep 2655989 = 248999) (by norm_num)
theorem B1771253 : Blo 523799 1771253 := bbase (se 5 (by rfl) ⟨83027, by rfl⟩ : syracuseStep 1771253 = 166055) (by norm_num)
theorem B1181429 : Blo 523799 1181429 := bbase (se 5 (by rfl) ⟨55379, by rfl⟩ : syracuseStep 1181429 = 110759) (by norm_num)
theorem B788213 : Blo 523799 788213 := bbase (se 5 (by rfl) ⟨36947, by rfl⟩ : syracuseStep 788213 = 73895) (by norm_num)
theorem B788237 : Blo 523799 788237 := bbase (se 3 (by rfl) ⟨147794, by rfl⟩ : syracuseStep 788237 = 295589) (by norm_num)
theorem B591637 : Blo 523799 591637 := bbase (se 6 (by rfl) ⟨13866, by rfl⟩ : syracuseStep 591637 = 27733) (by norm_num)
theorem B886565 : Blo 523799 886565 := bbase (se 4 (by rfl) ⟨83115, by rfl⟩ : syracuseStep 886565 = 166231) (by norm_num)
theorem B788261 : Blo 523799 788261 := bbase (se 4 (by rfl) ⟨73899, by rfl⟩ : syracuseStep 788261 = 147799) (by norm_num)
theorem B591673 : Blo 523799 591673 := bbase (se 2 (by rfl) ⟨221877, by rfl⟩ : syracuseStep 591673 = 443755) (by norm_num)
theorem B1181501 : Blo 523799 1181501 := bbase (se 3 (by rfl) ⟨221531, by rfl⟩ : syracuseStep 1181501 = 443063) (by norm_num)
theorem B788285 : Blo 523799 788285 := bbase (se 3 (by rfl) ⟨147803, by rfl⟩ : syracuseStep 788285 = 295607) (by norm_num)
theorem B788309 : Blo 523799 788309 := bbase (se 9 (by rfl) ⟨2309, by rfl⟩ : syracuseStep 788309 = 4619) (by norm_num)
theorem B591709 : Blo 523799 591709 := bbase (se 3 (by rfl) ⟨110945, by rfl⟩ : syracuseStep 591709 = 221891) (by norm_num)
theorem B788333 : Blo 523799 788333 := bbase (se 3 (by rfl) ⟨147812, by rfl⟩ : syracuseStep 788333 = 295625) (by norm_num)
theorem B591745 : Blo 523799 591745 := bbase (se 2 (by rfl) ⟨221904, by rfl⟩ : syracuseStep 591745 = 443809) (by norm_num)
theorem B1181573 : Blo 523799 1181573 := bbase (se 4 (by rfl) ⟨110772, by rfl⟩ : syracuseStep 1181573 = 221545) (by norm_num)
theorem B788357 : Blo 523799 788357 := bbase (se 4 (by rfl) ⟨73908, by rfl⟩ : syracuseStep 788357 = 147817) (by norm_num)
theorem B788381 : Blo 523799 788381 := bbase (se 3 (by rfl) ⟨147821, by rfl⟩ : syracuseStep 788381 = 295643) (by norm_num)
theorem B886693 : Blo 523799 886693 := bbase (se 4 (by rfl) ⟨83127, by rfl⟩ : syracuseStep 886693 = 166255) (by norm_num)
theorem B591781 : Blo 523799 591781 := bbase (se 4 (by rfl) ⟨55479, by rfl⟩ : syracuseStep 591781 = 110959) (by norm_num)
theorem B788405 : Blo 523799 788405 := bbase (se 5 (by rfl) ⟨36956, by rfl⟩ : syracuseStep 788405 = 73913) (by norm_num)
theorem B591817 : Blo 523799 591817 := bbase (se 2 (by rfl) ⟨221931, by rfl⟩ : syracuseStep 591817 = 443863) (by norm_num)
theorem B1181645 : Blo 523799 1181645 := bbase (se 3 (by rfl) ⟨221558, by rfl⟩ : syracuseStep 1181645 = 443117) (by norm_num)
theorem B788429 : Blo 523799 788429 := bbase (se 3 (by rfl) ⟨147830, by rfl⟩ : syracuseStep 788429 = 295661) (by norm_num)
theorem B788453 : Blo 523799 788453 := bbase (se 4 (by rfl) ⟨73917, by rfl⟩ : syracuseStep 788453 = 147835) (by norm_num)
theorem B591853 : Blo 523799 591853 := bbase (se 3 (by rfl) ⟨110972, by rfl⟩ : syracuseStep 591853 = 221945) (by norm_num)
theorem B3803125 : Blo 523799 3803125 := bbase (se 5 (by rfl) ⟨178271, by rfl⟩ : syracuseStep 3803125 = 356543) (by norm_num)
theorem B886781 : Blo 523799 886781 := bbase (se 3 (by rfl) ⟨166271, by rfl⟩ : syracuseStep 886781 = 332543) (by norm_num)
theorem B788477 : Blo 523799 788477 := bbase (se 3 (by rfl) ⟨147839, by rfl⟩ : syracuseStep 788477 = 295679) (by norm_num)
theorem B591889 : Blo 523799 591889 := bbase (se 2 (by rfl) ⟨221958, by rfl⟩ : syracuseStep 591889 = 443917) (by norm_num)
theorem B1181717 : Blo 523799 1181717 := bbase (se 6 (by rfl) ⟨27696, by rfl⟩ : syracuseStep 1181717 = 55393) (by norm_num)
theorem B4261909 : Blo 523799 4261909 := bbase (se 6 (by rfl) ⟨99888, by rfl⟩ : syracuseStep 4261909 = 199777) (by norm_num)
theorem B788501 : Blo 523799 788501 := bbase (se 6 (by rfl) ⟨18480, by rfl⟩ : syracuseStep 788501 = 36961) (by norm_num)
theorem B3377173 : Blo 523799 3377173 := bbase (se 6 (by rfl) ⟨79152, by rfl⟩ : syracuseStep 3377173 = 158305) (by norm_num)
theorem B788525 : Blo 523799 788525 := bbase (se 3 (by rfl) ⟨147848, by rfl⟩ : syracuseStep 788525 = 295697) (by norm_num)
theorem B591925 : Blo 523799 591925 := bbase (se 5 (by rfl) ⟨27746, by rfl⟩ : syracuseStep 591925 = 55493) (by norm_num)
theorem B788549 : Blo 523799 788549 := bbase (se 4 (by rfl) ⟨73926, by rfl⟩ : syracuseStep 788549 = 147853) (by norm_num)
theorem B591961 : Blo 523799 591961 := bbase (se 2 (by rfl) ⟨221985, by rfl⟩ : syracuseStep 591961 = 443971) (by norm_num)
theorem B1181789 : Blo 523799 1181789 := bbase (se 3 (by rfl) ⟨221585, by rfl⟩ : syracuseStep 1181789 = 443171) (by norm_num)
theorem B788573 : Blo 523799 788573 := bbase (se 3 (by rfl) ⟨147857, by rfl⟩ : syracuseStep 788573 = 295715) (by norm_num)
theorem B788597 : Blo 523799 788597 := bbase (se 5 (by rfl) ⟨36965, by rfl⟩ : syracuseStep 788597 = 73931) (by norm_num)
theorem B886909 : Blo 523799 886909 := bbase (se 3 (by rfl) ⟨166295, by rfl⟩ : syracuseStep 886909 = 332591) (by norm_num)
theorem B591997 : Blo 523799 591997 := bbase (se 3 (by rfl) ⟨110999, by rfl⟩ : syracuseStep 591997 = 221999) (by norm_num)
theorem B788621 : Blo 523799 788621 := bbase (se 3 (by rfl) ⟨147866, by rfl⟩ : syracuseStep 788621 = 295733) (by norm_num)
theorem B592033 : Blo 523799 592033 := bbase (se 2 (by rfl) ⟨222012, by rfl⟩ : syracuseStep 592033 = 444025) (by norm_num)
theorem B1771685 : Blo 523799 1771685 := bbase (se 4 (by rfl) ⟨166095, by rfl⟩ : syracuseStep 1771685 = 332191) (by norm_num)
theorem B1181861 : Blo 523799 1181861 := bbase (se 4 (by rfl) ⟨110799, by rfl⟩ : syracuseStep 1181861 = 221599) (by norm_num)
theorem B788645 : Blo 523799 788645 := bbase (se 4 (by rfl) ⟨73935, by rfl⟩ : syracuseStep 788645 = 147871) (by norm_num)
theorem B788669 : Blo 523799 788669 := bbase (se 3 (by rfl) ⟨147875, by rfl⟩ : syracuseStep 788669 = 295751) (by norm_num)
theorem B592069 : Blo 523799 592069 := bbase (se 4 (by rfl) ⟨55506, by rfl⟩ : syracuseStep 592069 = 111013) (by norm_num)
theorem B886997 : Blo 523799 886997 := bbase (se 7 (by rfl) ⟨10394, by rfl⟩ : syracuseStep 886997 = 20789) (by norm_num)
theorem B788693 : Blo 523799 788693 := bbase (se 7 (by rfl) ⟨9242, by rfl⟩ : syracuseStep 788693 = 18485) (by norm_num)
theorem B2689253 : Blo 523799 2689253 := bbase (se 4 (by rfl) ⟨252117, by rfl⟩ : syracuseStep 2689253 = 504235) (by norm_num)
theorem B592105 : Blo 523799 592105 := bbase (se 2 (by rfl) ⟨222039, by rfl⟩ : syracuseStep 592105 = 444079) (by norm_num)
theorem B1181933 : Blo 523799 1181933 := bbase (se 3 (by rfl) ⟨221612, by rfl⟩ : syracuseStep 1181933 = 443225) (by norm_num)
theorem B788717 : Blo 523799 788717 := bbase (se 3 (by rfl) ⟨147884, by rfl⟩ : syracuseStep 788717 = 295769) (by norm_num)
theorem B788741 : Blo 523799 788741 := bbase (se 4 (by rfl) ⟨73944, by rfl⟩ : syracuseStep 788741 = 147889) (by norm_num)
theorem B592141 : Blo 523799 592141 := bbase (se 3 (by rfl) ⟨111026, by rfl⟩ : syracuseStep 592141 = 222053) (by norm_num)
theorem B788765 : Blo 523799 788765 := bbase (se 3 (by rfl) ⟨147893, by rfl⟩ : syracuseStep 788765 = 295787) (by norm_num)
theorem B592177 : Blo 523799 592177 := bbase (se 2 (by rfl) ⟨222066, by rfl⟩ : syracuseStep 592177 = 444133) (by norm_num)
theorem B1182005 : Blo 523799 1182005 := bbase (se 5 (by rfl) ⟨55406, by rfl⟩ : syracuseStep 1182005 = 110813) (by norm_num)
theorem B788789 : Blo 523799 788789 := bbase (se 5 (by rfl) ⟨36974, by rfl⟩ : syracuseStep 788789 = 73949) (by norm_num)
theorem B788813 : Blo 523799 788813 := bbase (se 3 (by rfl) ⟨147902, by rfl⟩ : syracuseStep 788813 = 295805) (by norm_num)
theorem B559445 : Blo 523799 559445 := bbase (se 10 (by rfl) ⟨819, by rfl⟩ : syracuseStep 559445 = 1639) (by norm_num)
theorem B887125 : Blo 523799 887125 := bbase (se 10 (by rfl) ⟨1299, by rfl⟩ : syracuseStep 887125 = 2599) (by norm_num)
theorem B592213 : Blo 523799 592213 := bbase (se 10 (by rfl) ⟨867, by rfl⟩ : syracuseStep 592213 = 1735) (by norm_num)
theorem B788837 : Blo 523799 788837 := bbase (se 4 (by rfl) ⟨73953, by rfl⟩ : syracuseStep 788837 = 147907) (by norm_num)
theorem B592249 : Blo 523799 592249 := bbase (se 2 (by rfl) ⟨222093, by rfl⟩ : syracuseStep 592249 = 444187) (by norm_num)
theorem B1182077 : Blo 523799 1182077 := bbase (se 3 (by rfl) ⟨221639, by rfl⟩ : syracuseStep 1182077 = 443279) (by norm_num)
theorem B788861 : Blo 523799 788861 := bbase (se 3 (by rfl) ⟨147911, by rfl⟩ : syracuseStep 788861 = 295823) (by norm_num)
theorem B559505 : Blo 523799 559505 := bbase (se 2 (by rfl) ⟨209814, by rfl⟩ : syracuseStep 559505 = 419629) (by norm_num)
theorem B788885 : Blo 523799 788885 := bbase (se 6 (by rfl) ⟨18489, by rfl⟩ : syracuseStep 788885 = 36979) (by norm_num)
theorem B592285 : Blo 523799 592285 := bbase (se 3 (by rfl) ⟨111053, by rfl⟩ : syracuseStep 592285 = 222107) (by norm_num)
theorem B887213 : Blo 523799 887213 := bbase (se 3 (by rfl) ⟨166352, by rfl⟩ : syracuseStep 887213 = 332705) (by norm_num)
theorem B788909 : Blo 523799 788909 := bbase (se 3 (by rfl) ⟨147920, by rfl⟩ : syracuseStep 788909 = 295841) (by norm_num)
theorem B592321 : Blo 523799 592321 := bbase (se 2 (by rfl) ⟨222120, by rfl⟩ : syracuseStep 592321 = 444241) (by norm_num)
theorem B1182149 : Blo 523799 1182149 := bbase (se 4 (by rfl) ⟨110826, by rfl⟩ : syracuseStep 1182149 = 221653) (by norm_num)
theorem B788933 : Blo 523799 788933 := bbase (se 4 (by rfl) ⟨73962, by rfl⟩ : syracuseStep 788933 = 147925) (by norm_num)
theorem B788957 : Blo 523799 788957 := bbase (se 3 (by rfl) ⟨147929, by rfl⟩ : syracuseStep 788957 = 295859) (by norm_num)
theorem B592357 : Blo 523799 592357 := bbase (se 4 (by rfl) ⟨55533, by rfl⟩ : syracuseStep 592357 = 111067) (by norm_num)
theorem B788981 : Blo 523799 788981 := bbase (se 5 (by rfl) ⟨36983, by rfl⟩ : syracuseStep 788981 = 73967) (by norm_num)
theorem B592393 : Blo 523799 592393 := bbase (se 2 (by rfl) ⟨222147, by rfl⟩ : syracuseStep 592393 = 444295) (by norm_num)
theorem B1182221 : Blo 523799 1182221 := bbase (se 3 (by rfl) ⟨221666, by rfl⟩ : syracuseStep 1182221 = 443333) (by norm_num)
theorem B789005 : Blo 523799 789005 := bbase (se 3 (by rfl) ⟨147938, by rfl⟩ : syracuseStep 789005 = 295877) (by norm_num)
theorem B559633 : Blo 523799 559633 := bbase (se 2 (by rfl) ⟨209862, by rfl⟩ : syracuseStep 559633 = 419725) (by norm_num)
theorem B789029 : Blo 523799 789029 := bbase (se 4 (by rfl) ⟨73971, by rfl⟩ : syracuseStep 789029 = 147943) (by norm_num)
theorem B887341 : Blo 523799 887341 := bbase (se 3 (by rfl) ⟨166376, by rfl⟩ : syracuseStep 887341 = 332753) (by norm_num)
theorem B592429 : Blo 523799 592429 := bbase (se 3 (by rfl) ⟨111080, by rfl⟩ : syracuseStep 592429 = 222161) (by norm_num)
theorem B789053 : Blo 523799 789053 := bbase (se 3 (by rfl) ⟨147947, by rfl⟩ : syracuseStep 789053 = 295895) (by norm_num)
theorem B592465 : Blo 523799 592465 := bbase (se 2 (by rfl) ⟨222174, by rfl⟩ : syracuseStep 592465 = 444349) (by norm_num)
theorem B1772117 : Blo 523799 1772117 := bbase (se 8 (by rfl) ⟨10383, by rfl⟩ : syracuseStep 1772117 = 20767) (by norm_num)
theorem B1182293 : Blo 523799 1182293 := bbase (se 8 (by rfl) ⟨6927, by rfl⟩ : syracuseStep 1182293 = 13855) (by norm_num)
theorem B789077 : Blo 523799 789077 := bbase (se 8 (by rfl) ⟨4623, by rfl⟩ : syracuseStep 789077 = 9247) (by norm_num)
theorem B789101 : Blo 523799 789101 := bbase (se 3 (by rfl) ⟨147956, by rfl⟩ : syracuseStep 789101 = 295913) (by norm_num)
theorem B592501 : Blo 523799 592501 := bbase (se 5 (by rfl) ⟨27773, by rfl⟩ : syracuseStep 592501 = 55547) (by norm_num)
theorem B887429 : Blo 523799 887429 := bbase (se 4 (by rfl) ⟨83196, by rfl⟩ : syracuseStep 887429 = 166393) (by norm_num)
theorem B789125 : Blo 523799 789125 := bbase (se 4 (by rfl) ⟨73980, by rfl⟩ : syracuseStep 789125 = 147961) (by norm_num)
theorem B592537 : Blo 523799 592537 := bbase (se 2 (by rfl) ⟨222201, by rfl⟩ : syracuseStep 592537 = 444403) (by norm_num)
theorem B1182365 : Blo 523799 1182365 := bbase (se 3 (by rfl) ⟨221693, by rfl⟩ : syracuseStep 1182365 = 443387) (by norm_num)
theorem B789149 : Blo 523799 789149 := bbase (se 3 (by rfl) ⟨147965, by rfl⟩ : syracuseStep 789149 = 295931) (by norm_num)
theorem B789173 : Blo 523799 789173 := bbase (se 5 (by rfl) ⟨36992, by rfl⟩ : syracuseStep 789173 = 73985) (by norm_num)
theorem B592573 : Blo 523799 592573 := bbase (se 3 (by rfl) ⟨111107, by rfl⟩ : syracuseStep 592573 = 222215) (by norm_num)
theorem B789197 : Blo 523799 789197 := bbase (se 3 (by rfl) ⟨147974, by rfl⟩ : syracuseStep 789197 = 295949) (by norm_num)
theorem B592609 : Blo 523799 592609 := bbase (se 2 (by rfl) ⟨222228, by rfl⟩ : syracuseStep 592609 = 444457) (by norm_num)
theorem B1182437 : Blo 523799 1182437 := bbase (se 4 (by rfl) ⟨110853, by rfl⟩ : syracuseStep 1182437 = 221707) (by norm_num)
theorem B789221 : Blo 523799 789221 := bbase (se 4 (by rfl) ⟨73989, by rfl⟩ : syracuseStep 789221 = 147979) (by norm_num)
theorem B789245 : Blo 523799 789245 := bbase (se 3 (by rfl) ⟨147983, by rfl⟩ : syracuseStep 789245 = 295967) (by norm_num)
theorem B887557 : Blo 523799 887557 := bbase (se 4 (by rfl) ⟨83208, by rfl⟩ : syracuseStep 887557 = 166417) (by norm_num)
theorem B592645 : Blo 523799 592645 := bbase (se 4 (by rfl) ⟨55560, by rfl⟩ : syracuseStep 592645 = 111121) (by norm_num)
theorem B789269 : Blo 523799 789269 := bbase (se 6 (by rfl) ⟨18498, by rfl⟩ : syracuseStep 789269 = 36997) (by norm_num)
theorem B2394917 : Blo 523799 2394917 := bbase (se 4 (by rfl) ⟨224523, by rfl⟩ : syracuseStep 2394917 = 449047) (by norm_num)
theorem B592681 : Blo 523799 592681 := bbase (se 2 (by rfl) ⟨222255, by rfl⟩ : syracuseStep 592681 = 444511) (by norm_num)
theorem B1182509 : Blo 523799 1182509 := bbase (se 3 (by rfl) ⟨221720, by rfl⟩ : syracuseStep 1182509 = 443441) (by norm_num)
theorem B789293 : Blo 523799 789293 := bbase (se 3 (by rfl) ⟨147992, by rfl⟩ : syracuseStep 789293 = 295985) (by norm_num)
theorem B789317 : Blo 523799 789317 := bbase (se 4 (by rfl) ⟨73998, by rfl⟩ : syracuseStep 789317 = 147997) (by norm_num)
theorem B592717 : Blo 523799 592717 := bbase (se 3 (by rfl) ⟨111134, by rfl⟩ : syracuseStep 592717 = 222269) (by norm_num)
theorem B887645 : Blo 523799 887645 := bbase (se 3 (by rfl) ⟨166433, by rfl⟩ : syracuseStep 887645 = 332867) (by norm_num)
theorem B789341 : Blo 523799 789341 := bbase (se 3 (by rfl) ⟨148001, by rfl⟩ : syracuseStep 789341 = 296003) (by norm_num)
theorem B592753 : Blo 523799 592753 := bbase (se 2 (by rfl) ⟨222282, by rfl⟩ : syracuseStep 592753 = 444565) (by norm_num)
theorem B1182581 : Blo 523799 1182581 := bbase (se 5 (by rfl) ⟨55433, by rfl⟩ : syracuseStep 1182581 = 110867) (by norm_num)
theorem B789365 : Blo 523799 789365 := bbase (se 5 (by rfl) ⟨37001, by rfl⟩ : syracuseStep 789365 = 74003) (by norm_num)
theorem B789389 : Blo 523799 789389 := bbase (se 3 (by rfl) ⟨148010, by rfl⟩ : syracuseStep 789389 = 296021) (by norm_num)
theorem B592789 : Blo 523799 592789 := bbase (se 6 (by rfl) ⟨13893, by rfl⟩ : syracuseStep 592789 = 27787) (by norm_num)
theorem B789413 : Blo 523799 789413 := bbase (se 4 (by rfl) ⟨74007, by rfl⟩ : syracuseStep 789413 = 148015) (by norm_num)
theorem B592825 : Blo 523799 592825 := bbase (se 2 (by rfl) ⟨222309, by rfl⟩ : syracuseStep 592825 = 444619) (by norm_num)
theorem B1182653 : Blo 523799 1182653 := bbase (se 3 (by rfl) ⟨221747, by rfl⟩ : syracuseStep 1182653 = 443495) (by norm_num)
theorem B789437 : Blo 523799 789437 := bbase (se 3 (by rfl) ⟨148019, by rfl⟩ : syracuseStep 789437 = 296039) (by norm_num)
theorem B560077 : Blo 523799 560077 := bbase (se 3 (by rfl) ⟨105014, by rfl⟩ : syracuseStep 560077 = 210029) (by norm_num)
theorem B789461 : Blo 523799 789461 := bbase (se 7 (by rfl) ⟨9251, by rfl⟩ : syracuseStep 789461 = 18503) (by norm_num)
theorem B887773 : Blo 523799 887773 := bbase (se 3 (by rfl) ⟨166457, by rfl⟩ : syracuseStep 887773 = 332915) (by norm_num)
theorem B592861 : Blo 523799 592861 := bbase (se 3 (by rfl) ⟨111161, by rfl⟩ : syracuseStep 592861 = 222323) (by norm_num)
theorem B1215461 : Blo 523799 1215461 := bbase (se 4 (by rfl) ⟨113949, by rfl⟩ : syracuseStep 1215461 = 227899) (by norm_num)
theorem B789485 : Blo 523799 789485 := bbase (se 3 (by rfl) ⟨148028, by rfl⟩ : syracuseStep 789485 = 296057) (by norm_num)
theorem B592897 : Blo 523799 592897 := bbase (se 2 (by rfl) ⟨222336, by rfl⟩ : syracuseStep 592897 = 444673) (by norm_num)
theorem B2657285 : Blo 523799 2657285 := bbase (se 4 (by rfl) ⟨249120, by rfl⟩ : syracuseStep 2657285 = 498241) (by norm_num)
theorem B1772549 : Blo 523799 1772549 := bbase (se 4 (by rfl) ⟨166176, by rfl⟩ : syracuseStep 1772549 = 332353) (by norm_num)
theorem B1182725 : Blo 523799 1182725 := bbase (se 4 (by rfl) ⟨110880, by rfl⟩ : syracuseStep 1182725 = 221761) (by norm_num)
theorem B789509 : Blo 523799 789509 := bbase (se 4 (by rfl) ⟨74016, by rfl⟩ : syracuseStep 789509 = 148033) (by norm_num)
theorem B2001941 : Blo 523799 2001941 := bbase (se 6 (by rfl) ⟨46920, by rfl⟩ : syracuseStep 2001941 = 93841) (by norm_num)
theorem B789533 : Blo 523799 789533 := bbase (se 3 (by rfl) ⟨148037, by rfl⟩ : syracuseStep 789533 = 296075) (by norm_num)
theorem B592933 : Blo 523799 592933 := bbase (se 4 (by rfl) ⟨55587, by rfl⟩ : syracuseStep 592933 = 111175) (by norm_num)
theorem B887861 : Blo 523799 887861 := bbase (se 5 (by rfl) ⟨41618, by rfl⟩ : syracuseStep 887861 = 83237) (by norm_num)
theorem B789557 : Blo 523799 789557 := bbase (se 5 (by rfl) ⟨37010, by rfl⟩ : syracuseStep 789557 = 74021) (by norm_num)
theorem B560197 : Blo 523799 560197 := bbase (se 4 (by rfl) ⟨52518, by rfl⟩ : syracuseStep 560197 = 105037) (by norm_num)
theorem B592969 : Blo 523799 592969 := bbase (se 2 (by rfl) ⟨222363, by rfl⟩ : syracuseStep 592969 = 444727) (by norm_num)
theorem B1182797 : Blo 523799 1182797 := bbase (se 3 (by rfl) ⟨221774, by rfl⟩ : syracuseStep 1182797 = 443549) (by norm_num)
theorem B789581 : Blo 523799 789581 := bbase (se 3 (by rfl) ⟨148046, by rfl⟩ : syracuseStep 789581 = 296093) (by norm_num)
theorem B789605 : Blo 523799 789605 := bbase (se 4 (by rfl) ⟨74025, by rfl⟩ : syracuseStep 789605 = 148051) (by norm_num)
theorem B593005 : Blo 523799 593005 := bbase (se 3 (by rfl) ⟨111188, by rfl⟩ : syracuseStep 593005 = 222377) (by norm_num)
theorem B789629 : Blo 523799 789629 := bbase (se 3 (by rfl) ⟨148055, by rfl⟩ : syracuseStep 789629 = 296111) (by norm_num)
theorem B593041 : Blo 523799 593041 := bbase (se 2 (by rfl) ⟨222390, by rfl⟩ : syracuseStep 593041 = 444781) (by norm_num)
theorem B1182869 : Blo 523799 1182869 := bbase (se 6 (by rfl) ⟨27723, by rfl⟩ : syracuseStep 1182869 = 55447) (by norm_num)
theorem B789653 : Blo 523799 789653 := bbase (se 6 (by rfl) ⟨18507, by rfl⟩ : syracuseStep 789653 = 37015) (by norm_num)
theorem B789677 : Blo 523799 789677 := bbase (se 3 (by rfl) ⟨148064, by rfl⟩ : syracuseStep 789677 = 296129) (by norm_num)
theorem B887989 : Blo 523799 887989 := bbase (se 5 (by rfl) ⟨41624, by rfl⟩ : syracuseStep 887989 = 83249) (by norm_num)
theorem B593077 : Blo 523799 593077 := bbase (se 5 (by rfl) ⟨27800, by rfl⟩ : syracuseStep 593077 = 55601) (by norm_num)
theorem B789701 : Blo 523799 789701 := bbase (se 4 (by rfl) ⟨74034, by rfl⟩ : syracuseStep 789701 = 148069) (by norm_num)
theorem B593113 : Blo 523799 593113 := bbase (se 2 (by rfl) ⟨222417, by rfl⟩ : syracuseStep 593113 = 444835) (by norm_num)
theorem B1182941 : Blo 523799 1182941 := bbase (se 3 (by rfl) ⟨221801, by rfl⟩ : syracuseStep 1182941 = 443603) (by norm_num)
theorem B789725 : Blo 523799 789725 := bbase (se 3 (by rfl) ⟨148073, by rfl⟩ : syracuseStep 789725 = 296147) (by norm_num)
theorem B789749 : Blo 523799 789749 := bbase (se 5 (by rfl) ⟨37019, by rfl⟩ : syracuseStep 789749 = 74039) (by norm_num)
theorem B593149 : Blo 523799 593149 := bbase (se 3 (by rfl) ⟨111215, by rfl⟩ : syracuseStep 593149 = 222431) (by norm_num)
theorem B888077 : Blo 523799 888077 := bbase (se 3 (by rfl) ⟨166514, by rfl⟩ : syracuseStep 888077 = 333029) (by norm_num)
theorem B789773 : Blo 523799 789773 := bbase (se 3 (by rfl) ⟨148082, by rfl⟩ : syracuseStep 789773 = 296165) (by norm_num)
theorem B593185 : Blo 523799 593185 := bbase (se 2 (by rfl) ⟨222444, by rfl⟩ : syracuseStep 593185 = 444889) (by norm_num)
theorem B1183013 : Blo 523799 1183013 := bbase (se 4 (by rfl) ⟨110907, by rfl⟩ : syracuseStep 1183013 = 221815) (by norm_num)
theorem B789797 : Blo 523799 789797 := bbase (se 4 (by rfl) ⟨74043, by rfl⟩ : syracuseStep 789797 = 148087) (by norm_num)
theorem B2002229 : Blo 523799 2002229 := bbase (se 5 (by rfl) ⟨93854, by rfl⟩ : syracuseStep 2002229 = 187709) (by norm_num)
theorem B789821 : Blo 523799 789821 := bbase (se 3 (by rfl) ⟨148091, by rfl⟩ : syracuseStep 789821 = 296183) (by norm_num)
theorem B560449 : Blo 523799 560449 := bbase (se 2 (by rfl) ⟨210168, by rfl⟩ : syracuseStep 560449 = 420337) (by norm_num)
theorem B560453 : Blo 523799 560453 := bbase (se 4 (by rfl) ⟨52542, by rfl⟩ : syracuseStep 560453 = 105085) (by norm_num)
theorem B593221 : Blo 523799 593221 := bbase (se 4 (by rfl) ⟨55614, by rfl⟩ : syracuseStep 593221 = 111229) (by norm_num)
theorem B789845 : Blo 523799 789845 := bbase (se 11 (by rfl) ⟨578, by rfl⟩ : syracuseStep 789845 = 1157) (by norm_num)
theorem B593257 : Blo 523799 593257 := bbase (se 2 (by rfl) ⟨222471, by rfl⟩ : syracuseStep 593257 = 444943) (by norm_num)
theorem B1183085 : Blo 523799 1183085 := bbase (se 3 (by rfl) ⟨221828, by rfl⟩ : syracuseStep 1183085 = 443657) (by norm_num)
theorem B789869 : Blo 523799 789869 := bbase (se 3 (by rfl) ⟨148100, by rfl⟩ : syracuseStep 789869 = 296201) (by norm_num)
theorem B789893 : Blo 523799 789893 := bbase (se 4 (by rfl) ⟨74052, by rfl⟩ : syracuseStep 789893 = 148105) (by norm_num)
theorem B888205 : Blo 523799 888205 := bbase (se 3 (by rfl) ⟨166538, by rfl⟩ : syracuseStep 888205 = 333077) (by norm_num)
theorem B593293 : Blo 523799 593293 := bbase (se 3 (by rfl) ⟨111242, by rfl⟩ : syracuseStep 593293 = 222485) (by norm_num)
theorem B789917 : Blo 523799 789917 := bbase (se 3 (by rfl) ⟨148109, by rfl⟩ : syracuseStep 789917 = 296219) (by norm_num)
theorem B593329 : Blo 523799 593329 := bbase (se 2 (by rfl) ⟨222498, by rfl⟩ : syracuseStep 593329 = 444997) (by norm_num)
theorem B1772981 : Blo 523799 1772981 := bbase (se 5 (by rfl) ⟨83108, by rfl⟩ : syracuseStep 1772981 = 166217) (by norm_num)
theorem B1183157 : Blo 523799 1183157 := bbase (se 5 (by rfl) ⟨55460, by rfl⟩ : syracuseStep 1183157 = 110921) (by norm_num)
theorem B789941 : Blo 523799 789941 := bbase (se 5 (by rfl) ⟨37028, by rfl⟩ : syracuseStep 789941 = 74057) (by norm_num)
theorem B789965 : Blo 523799 789965 := bbase (se 3 (by rfl) ⟨148118, by rfl⟩ : syracuseStep 789965 = 296237) (by norm_num)
theorem B4001237 : Blo 523799 4001237 := bbase (se 7 (by rfl) ⟨46889, by rfl⟩ : syracuseStep 4001237 = 93779) (by norm_num)
theorem B593365 : Blo 523799 593365 := bbase (se 7 (by rfl) ⟨6953, by rfl⟩ : syracuseStep 593365 = 13907) (by norm_num)
theorem B888293 : Blo 523799 888293 := bbase (se 4 (by rfl) ⟨83277, by rfl⟩ : syracuseStep 888293 = 166555) (by norm_num)
theorem B789989 : Blo 523799 789989 := bbase (se 4 (by rfl) ⟨74061, by rfl⟩ : syracuseStep 789989 = 148123) (by norm_num)
theorem B593401 : Blo 523799 593401 := bbase (se 2 (by rfl) ⟨222525, by rfl⟩ : syracuseStep 593401 = 445051) (by norm_num)
theorem B1183229 : Blo 523799 1183229 := bbase (se 3 (by rfl) ⟨221855, by rfl⟩ : syracuseStep 1183229 = 443711) (by norm_num)
theorem B790013 : Blo 523799 790013 := bbase (se 3 (by rfl) ⟨148127, by rfl⟩ : syracuseStep 790013 = 296255) (by norm_num)
theorem B790037 : Blo 523799 790037 := bbase (se 6 (by rfl) ⟨18516, by rfl⟩ : syracuseStep 790037 = 37033) (by norm_num)
theorem B593437 : Blo 523799 593437 := bbase (se 3 (by rfl) ⟨111269, by rfl⟩ : syracuseStep 593437 = 222539) (by norm_num)
theorem B790061 : Blo 523799 790061 := bbase (se 3 (by rfl) ⟨148136, by rfl⟩ : syracuseStep 790061 = 296273) (by norm_num)
theorem B593473 : Blo 523799 593473 := bbase (se 2 (by rfl) ⟨222552, by rfl⟩ : syracuseStep 593473 = 445105) (by norm_num)
theorem B1183301 : Blo 523799 1183301 := bbase (se 4 (by rfl) ⟨110934, by rfl⟩ : syracuseStep 1183301 = 221869) (by norm_num)
theorem B790085 : Blo 523799 790085 := bbase (se 4 (by rfl) ⟨74070, by rfl⟩ : syracuseStep 790085 = 148141) (by norm_num)
theorem B2526805 : Blo 523799 2526805 := bbase (se 8 (by rfl) ⟨14805, by rfl⟩ : syracuseStep 2526805 = 29611) (by norm_num)
theorem B790109 : Blo 523799 790109 := bbase (se 3 (by rfl) ⟨148145, by rfl⟩ : syracuseStep 790109 = 296291) (by norm_num)
theorem B888421 : Blo 523799 888421 := bbase (se 4 (by rfl) ⟨83289, by rfl⟩ : syracuseStep 888421 = 166579) (by norm_num)
theorem B593509 : Blo 523799 593509 := bbase (se 4 (by rfl) ⟨55641, by rfl⟩ : syracuseStep 593509 = 111283) (by norm_num)
theorem B790133 : Blo 523799 790133 := bbase (se 5 (by rfl) ⟨37037, by rfl⟩ : syracuseStep 790133 = 74075) (by norm_num)
theorem B593545 : Blo 523799 593545 := bbase (se 2 (by rfl) ⟨222579, by rfl⟩ : syracuseStep 593545 = 445159) (by norm_num)
theorem B1183373 : Blo 523799 1183373 := bbase (se 3 (by rfl) ⟨221882, by rfl⟩ : syracuseStep 1183373 = 443765) (by norm_num)
theorem B790157 : Blo 523799 790157 := bbase (se 3 (by rfl) ⟨148154, by rfl⟩ : syracuseStep 790157 = 296309) (by norm_num)
theorem B790181 : Blo 523799 790181 := bbase (se 4 (by rfl) ⟨74079, by rfl⟩ : syracuseStep 790181 = 148159) (by norm_num)
theorem B593581 : Blo 523799 593581 := bbase (se 3 (by rfl) ⟨111296, by rfl⟩ : syracuseStep 593581 = 222593) (by norm_num)
theorem B888509 : Blo 523799 888509 := bbase (se 3 (by rfl) ⟨166595, by rfl⟩ : syracuseStep 888509 = 333191) (by norm_num)
theorem B790205 : Blo 523799 790205 := bbase (se 3 (by rfl) ⟨148163, by rfl⟩ : syracuseStep 790205 = 296327) (by norm_num)
theorem B593617 : Blo 523799 593617 := bbase (se 2 (by rfl) ⟨222606, by rfl⟩ : syracuseStep 593617 = 445213) (by norm_num)
theorem B1183445 : Blo 523799 1183445 := bbase (se 7 (by rfl) ⟨13868, by rfl⟩ : syracuseStep 1183445 = 27737) (by norm_num)
theorem B790229 : Blo 523799 790229 := bbase (se 7 (by rfl) ⟨9260, by rfl⟩ : syracuseStep 790229 = 18521) (by norm_num)
theorem B790253 : Blo 523799 790253 := bbase (se 3 (by rfl) ⟨148172, by rfl⟩ : syracuseStep 790253 = 296345) (by norm_num)
theorem B593653 : Blo 523799 593653 := bbase (se 5 (by rfl) ⟨27827, by rfl⟩ : syracuseStep 593653 = 55655) (by norm_num)
theorem B790277 : Blo 523799 790277 := bbase (se 4 (by rfl) ⟨74088, by rfl⟩ : syracuseStep 790277 = 148177) (by norm_num)
theorem B593689 : Blo 523799 593689 := bbase (se 2 (by rfl) ⟨222633, by rfl⟩ : syracuseStep 593689 = 445267) (by norm_num)
theorem B1183517 : Blo 523799 1183517 := bbase (se 3 (by rfl) ⟨221909, by rfl⟩ : syracuseStep 1183517 = 443819) (by norm_num)
theorem B790301 : Blo 523799 790301 := bbase (se 3 (by rfl) ⟨148181, by rfl⟩ : syracuseStep 790301 = 296363) (by norm_num)
theorem B790325 : Blo 523799 790325 := bbase (se 5 (by rfl) ⟨37046, by rfl⟩ : syracuseStep 790325 = 74093) (by norm_num)
theorem B888637 : Blo 523799 888637 := bbase (se 3 (by rfl) ⟨166619, by rfl⟩ : syracuseStep 888637 = 333239) (by norm_num)
theorem B593725 : Blo 523799 593725 := bbase (se 3 (by rfl) ⟨111323, by rfl⟩ : syracuseStep 593725 = 222647) (by norm_num)
theorem B790349 : Blo 523799 790349 := bbase (se 3 (by rfl) ⟨148190, by rfl⟩ : syracuseStep 790349 = 296381) (by norm_num)
theorem B593761 : Blo 523799 593761 := bbase (se 2 (by rfl) ⟨222660, by rfl⟩ : syracuseStep 593761 = 445321) (by norm_num)
theorem B1773413 : Blo 523799 1773413 := bbase (se 4 (by rfl) ⟨166257, by rfl⟩ : syracuseStep 1773413 = 332515) (by norm_num)
theorem B1183589 : Blo 523799 1183589 := bbase (se 4 (by rfl) ⟨110961, by rfl⟩ : syracuseStep 1183589 = 221923) (by norm_num)
theorem B790373 : Blo 523799 790373 := bbase (se 4 (by rfl) ⟨74097, by rfl⟩ : syracuseStep 790373 = 148195) (by norm_num)
theorem B561017 : Blo 523799 561017 := bbase (se 2 (by rfl) ⟨210381, by rfl⟩ : syracuseStep 561017 = 420763) (by norm_num)
theorem B790397 : Blo 523799 790397 := bbase (se 3 (by rfl) ⟨148199, by rfl⟩ : syracuseStep 790397 = 296399) (by norm_num)
theorem B888725 : Blo 523799 888725 := bbase (se 6 (by rfl) ⟨20829, by rfl⟩ : syracuseStep 888725 = 41659) (by norm_num)
theorem B790421 : Blo 523799 790421 := bbase (se 6 (by rfl) ⟨18525, by rfl⟩ : syracuseStep 790421 = 37051) (by norm_num)
theorem B1183661 : Blo 523799 1183661 := bbase (se 3 (by rfl) ⟨221936, by rfl⟩ : syracuseStep 1183661 = 443873) (by norm_num)
theorem B790445 : Blo 523799 790445 := bbase (se 3 (by rfl) ⟨148208, by rfl⟩ : syracuseStep 790445 = 296417) (by norm_num)
theorem B790469 : Blo 523799 790469 := bbase (se 4 (by rfl) ⟨74106, by rfl⟩ : syracuseStep 790469 = 148213) (by norm_num)
theorem B790493 : Blo 523799 790493 := bbase (se 3 (by rfl) ⟨148217, by rfl⟩ : syracuseStep 790493 = 296435) (by norm_num)
theorem B1183733 : Blo 523799 1183733 := bbase (se 5 (by rfl) ⟨55487, by rfl⟩ : syracuseStep 1183733 = 110975) (by norm_num)
theorem B790517 : Blo 523799 790517 := bbase (se 5 (by rfl) ⟨37055, by rfl⟩ : syracuseStep 790517 = 74111) (by norm_num)
theorem B790541 : Blo 523799 790541 := bbase (se 3 (by rfl) ⟨148226, by rfl⟩ : syracuseStep 790541 = 296453) (by norm_num)
theorem B888853 : Blo 523799 888853 := bbase (se 6 (by rfl) ⟨20832, by rfl⟩ : syracuseStep 888853 = 41665) (by norm_num)
theorem B790565 : Blo 523799 790565 := bbase (se 4 (by rfl) ⟨74115, by rfl⟩ : syracuseStep 790565 = 148231) (by norm_num)
theorem B561205 : Blo 523799 561205 := bbase (se 5 (by rfl) ⟨26306, by rfl⟩ : syracuseStep 561205 = 52613) (by norm_num)
theorem B1183805 : Blo 523799 1183805 := bbase (se 3 (by rfl) ⟨221963, by rfl⟩ : syracuseStep 1183805 = 443927) (by norm_num)
theorem B790589 : Blo 523799 790589 := bbase (se 3 (by rfl) ⟨148235, by rfl⟩ : syracuseStep 790589 = 296471) (by norm_num)
theorem B790613 : Blo 523799 790613 := bbase (se 8 (by rfl) ⟨4632, by rfl⟩ : syracuseStep 790613 = 9265) (by norm_num)
theorem B888941 : Blo 523799 888941 := bbase (se 3 (by rfl) ⟨166676, by rfl⟩ : syracuseStep 888941 = 333353) (by norm_num)
theorem B790637 : Blo 523799 790637 := bbase (se 3 (by rfl) ⟨148244, by rfl⟩ : syracuseStep 790637 = 296489) (by norm_num)
theorem B1183877 : Blo 523799 1183877 := bbase (se 4 (by rfl) ⟨110988, by rfl⟩ : syracuseStep 1183877 = 221977) (by norm_num)
theorem B790661 : Blo 523799 790661 := bbase (se 4 (by rfl) ⟨74124, by rfl⟩ : syracuseStep 790661 = 148249) (by norm_num)
theorem B790685 : Blo 523799 790685 := bbase (se 3 (by rfl) ⟨148253, by rfl⟩ : syracuseStep 790685 = 296507) (by norm_num)
theorem B790709 : Blo 523799 790709 := bbase (se 5 (by rfl) ⟨37064, by rfl⟩ : syracuseStep 790709 = 74129) (by norm_num)
theorem B1183949 : Blo 523799 1183949 := bbase (se 3 (by rfl) ⟨221990, by rfl⟩ : syracuseStep 1183949 = 443981) (by norm_num)
theorem B790733 : Blo 523799 790733 := bbase (se 3 (by rfl) ⟨148262, by rfl⟩ : syracuseStep 790733 = 296525) (by norm_num)
theorem B790757 : Blo 523799 790757 := bbase (se 4 (by rfl) ⟨74133, by rfl⟩ : syracuseStep 790757 = 148267) (by norm_num)
theorem B889069 : Blo 523799 889069 := bbase (se 3 (by rfl) ⟨166700, by rfl⟩ : syracuseStep 889069 = 333401) (by norm_num)
theorem B790781 : Blo 523799 790781 := bbase (se 3 (by rfl) ⟨148271, by rfl⟩ : syracuseStep 790781 = 296543) (by norm_num)
theorem B2658581 : Blo 523799 2658581 := bbase (se 6 (by rfl) ⟨62310, by rfl⟩ : syracuseStep 2658581 = 124621) (by norm_num)
theorem B1773845 : Blo 523799 1773845 := bbase (se 6 (by rfl) ⟨41574, by rfl⟩ : syracuseStep 1773845 = 83149) (by norm_num)
theorem B1184021 : Blo 523799 1184021 := bbase (se 6 (by rfl) ⟨27750, by rfl⟩ : syracuseStep 1184021 = 55501) (by norm_num)
theorem B790805 : Blo 523799 790805 := bbase (se 6 (by rfl) ⟨18534, by rfl⟩ : syracuseStep 790805 = 37069) (by norm_num)
theorem B790829 : Blo 523799 790829 := bbase (se 3 (by rfl) ⟨148280, by rfl⟩ : syracuseStep 790829 = 296561) (by norm_num)
theorem B889157 : Blo 523799 889157 := bbase (se 4 (by rfl) ⟨83358, by rfl⟩ : syracuseStep 889157 = 166717) (by norm_num)
theorem B790853 : Blo 523799 790853 := bbase (se 4 (by rfl) ⟨74142, by rfl⟩ : syracuseStep 790853 = 148285) (by norm_num)
theorem B1184093 : Blo 523799 1184093 := bbase (se 3 (by rfl) ⟨222017, by rfl⟩ : syracuseStep 1184093 = 444035) (by norm_num)
theorem B790877 : Blo 523799 790877 := bbase (se 3 (by rfl) ⟨148289, by rfl⟩ : syracuseStep 790877 = 296579) (by norm_num)
theorem B790901 : Blo 523799 790901 := bbase (se 5 (by rfl) ⟨37073, by rfl⟩ : syracuseStep 790901 = 74147) (by norm_num)
theorem B790925 : Blo 523799 790925 := bbase (se 3 (by rfl) ⟨148298, by rfl⟩ : syracuseStep 790925 = 296597) (by norm_num)
theorem B1184165 : Blo 523799 1184165 := bbase (se 4 (by rfl) ⟨111015, by rfl⟩ : syracuseStep 1184165 = 222031) (by norm_num)
theorem B790949 : Blo 523799 790949 := bbase (se 4 (by rfl) ⟨74151, by rfl⟩ : syracuseStep 790949 = 148303) (by norm_num)
theorem B790973 : Blo 523799 790973 := bbase (se 3 (by rfl) ⟨148307, by rfl⟩ : syracuseStep 790973 = 296615) (by norm_num)
theorem B889285 : Blo 523799 889285 := bbase (se 4 (by rfl) ⟨83370, by rfl⟩ : syracuseStep 889285 = 166741) (by norm_num)
theorem B790997 : Blo 523799 790997 := bbase (se 7 (by rfl) ⟨9269, by rfl⟩ : syracuseStep 790997 = 18539) (by norm_num)
theorem B2003413 : Blo 523799 2003413 := bbase (se 7 (by rfl) ⟨23477, by rfl⟩ : syracuseStep 2003413 = 46955) (by norm_num)
theorem B1184237 : Blo 523799 1184237 := bbase (se 3 (by rfl) ⟨222044, by rfl⟩ : syracuseStep 1184237 = 444089) (by norm_num)
theorem B791021 : Blo 523799 791021 := bbase (se 3 (by rfl) ⟨148316, by rfl⟩ : syracuseStep 791021 = 296633) (by norm_num)
theorem B791045 : Blo 523799 791045 := bbase (se 4 (by rfl) ⟨74160, by rfl⟩ : syracuseStep 791045 = 148321) (by norm_num)
theorem B889373 : Blo 523799 889373 := bbase (se 3 (by rfl) ⟨166757, by rfl⟩ : syracuseStep 889373 = 333515) (by norm_num)
theorem B791069 : Blo 523799 791069 := bbase (se 3 (by rfl) ⟨148325, by rfl⟩ : syracuseStep 791069 = 296651) (by norm_num)
theorem B1184309 : Blo 523799 1184309 := bbase (se 5 (by rfl) ⟨55514, by rfl⟩ : syracuseStep 1184309 = 111029) (by norm_num)
theorem B791093 : Blo 523799 791093 := bbase (se 5 (by rfl) ⟨37082, by rfl⟩ : syracuseStep 791093 = 74165) (by norm_num)
theorem B791117 : Blo 523799 791117 := bbase (se 3 (by rfl) ⟨148334, by rfl⟩ : syracuseStep 791117 = 296669) (by norm_num)
theorem B791141 : Blo 523799 791141 := bbase (se 4 (by rfl) ⟨74169, by rfl⟩ : syracuseStep 791141 = 148339) (by norm_num)
theorem B1184381 : Blo 523799 1184381 := bbase (se 3 (by rfl) ⟨222071, by rfl⟩ : syracuseStep 1184381 = 444143) (by norm_num)
theorem B791165 : Blo 523799 791165 := bbase (se 3 (by rfl) ⟨148343, by rfl⟩ : syracuseStep 791165 = 296687) (by norm_num)
theorem B791189 : Blo 523799 791189 := bbase (se 6 (by rfl) ⟨18543, by rfl⟩ : syracuseStep 791189 = 37087) (by norm_num)
theorem B889501 : Blo 523799 889501 := bbase (se 3 (by rfl) ⟨166781, by rfl⟩ : syracuseStep 889501 = 333563) (by norm_num)
theorem B791213 : Blo 523799 791213 := bbase (se 3 (by rfl) ⟨148352, by rfl⟩ : syracuseStep 791213 = 296705) (by norm_num)
theorem B1774277 : Blo 523799 1774277 := bbase (se 4 (by rfl) ⟨166338, by rfl⟩ : syracuseStep 1774277 = 332677) (by norm_num)
theorem B1184453 : Blo 523799 1184453 := bbase (se 4 (by rfl) ⟨111042, by rfl⟩ : syracuseStep 1184453 = 222085) (by norm_num)
theorem B791237 : Blo 523799 791237 := bbase (se 4 (by rfl) ⟨74178, by rfl⟩ : syracuseStep 791237 = 148357) (by norm_num)
theorem B791261 : Blo 523799 791261 := bbase (se 3 (by rfl) ⟨148361, by rfl⟩ : syracuseStep 791261 = 296723) (by norm_num)
theorem B889589 : Blo 523799 889589 := bbase (se 5 (by rfl) ⟨41699, by rfl⟩ : syracuseStep 889589 = 83399) (by norm_num)
theorem B791285 : Blo 523799 791285 := bbase (se 5 (by rfl) ⟨37091, by rfl⟩ : syracuseStep 791285 = 74183) (by norm_num)
theorem B2003717 : Blo 523799 2003717 := bbase (se 4 (by rfl) ⟨187848, by rfl⟩ : syracuseStep 2003717 = 375697) (by norm_num)
theorem B1184525 : Blo 523799 1184525 := bbase (se 3 (by rfl) ⟨222098, by rfl⟩ : syracuseStep 1184525 = 444197) (by norm_num)
theorem B791309 : Blo 523799 791309 := bbase (se 3 (by rfl) ⟨148370, by rfl⟩ : syracuseStep 791309 = 296741) (by norm_num)
theorem B791333 : Blo 523799 791333 := bbase (se 4 (by rfl) ⟨74187, by rfl⟩ : syracuseStep 791333 = 148375) (by norm_num)
theorem B791357 : Blo 523799 791357 := bbase (se 3 (by rfl) ⟨148379, by rfl⟩ : syracuseStep 791357 = 296759) (by norm_num)
theorem B1184597 : Blo 523799 1184597 := bbase (se 9 (by rfl) ⟨3470, by rfl⟩ : syracuseStep 1184597 = 6941) (by norm_num)
theorem B791381 : Blo 523799 791381 := bbase (se 9 (by rfl) ⟨2318, by rfl⟩ : syracuseStep 791381 = 4637) (by norm_num)
theorem B562025 : Blo 523799 562025 := bbase (se 2 (by rfl) ⟨210759, by rfl⟩ : syracuseStep 562025 = 421519) (by norm_num)
theorem B791405 : Blo 523799 791405 := bbase (se 3 (by rfl) ⟨148388, by rfl⟩ : syracuseStep 791405 = 296777) (by norm_num)
theorem B889717 : Blo 523799 889717 := bbase (se 5 (by rfl) ⟨41705, by rfl⟩ : syracuseStep 889717 = 83411) (by norm_num)
theorem B791429 : Blo 523799 791429 := bbase (se 4 (by rfl) ⟨74196, by rfl⟩ : syracuseStep 791429 = 148393) (by norm_num)
theorem B1184669 : Blo 523799 1184669 := bbase (se 3 (by rfl) ⟨222125, by rfl⟩ : syracuseStep 1184669 = 444251) (by norm_num)
theorem B791453 : Blo 523799 791453 := bbase (se 3 (by rfl) ⟨148397, by rfl⟩ : syracuseStep 791453 = 296795) (by norm_num)
theorem B791477 : Blo 523799 791477 := bbase (se 5 (by rfl) ⟨37100, by rfl⟩ : syracuseStep 791477 = 74201) (by norm_num)
theorem B889805 : Blo 523799 889805 := bbase (se 3 (by rfl) ⟨166838, by rfl⟩ : syracuseStep 889805 = 333677) (by norm_num)
theorem B791501 : Blo 523799 791501 := bbase (se 3 (by rfl) ⟨148406, by rfl⟩ : syracuseStep 791501 = 296813) (by norm_num)
theorem B1184741 : Blo 523799 1184741 := bbase (se 4 (by rfl) ⟨111069, by rfl⟩ : syracuseStep 1184741 = 222139) (by norm_num)
theorem B791525 : Blo 523799 791525 := bbase (se 4 (by rfl) ⟨74205, by rfl⟩ : syracuseStep 791525 = 148411) (by norm_num)
theorem B791549 : Blo 523799 791549 := bbase (se 3 (by rfl) ⟨148415, by rfl⟩ : syracuseStep 791549 = 296831) (by norm_num)
theorem B791573 : Blo 523799 791573 := bbase (se 6 (by rfl) ⟨18552, by rfl⟩ : syracuseStep 791573 = 37105) (by norm_num)
theorem B1184813 : Blo 523799 1184813 := bbase (se 3 (by rfl) ⟨222152, by rfl⟩ : syracuseStep 1184813 = 444305) (by norm_num)
theorem B791597 : Blo 523799 791597 := bbase (se 3 (by rfl) ⟨148424, by rfl⟩ : syracuseStep 791597 = 296849) (by norm_num)
theorem B791621 : Blo 523799 791621 := bbase (se 4 (by rfl) ⟨74214, by rfl⟩ : syracuseStep 791621 = 148429) (by norm_num)
theorem B889933 : Blo 523799 889933 := bbase (se 3 (by rfl) ⟨166862, by rfl⟩ : syracuseStep 889933 = 333725) (by norm_num)
theorem B791645 : Blo 523799 791645 := bbase (se 3 (by rfl) ⟨148433, by rfl⟩ : syracuseStep 791645 = 296867) (by norm_num)
theorem B1774709 : Blo 523799 1774709 := bbase (se 5 (by rfl) ⟨83189, by rfl⟩ : syracuseStep 1774709 = 166379) (by norm_num)
theorem B1184885 : Blo 523799 1184885 := bbase (se 5 (by rfl) ⟨55541, by rfl⟩ : syracuseStep 1184885 = 111083) (by norm_num)
theorem B791669 : Blo 523799 791669 := bbase (se 5 (by rfl) ⟨37109, by rfl⟩ : syracuseStep 791669 = 74219) (by norm_num)
theorem B791693 : Blo 523799 791693 := bbase (se 3 (by rfl) ⟨148442, by rfl⟩ : syracuseStep 791693 = 296885) (by norm_num)
theorem B890021 : Blo 523799 890021 := bbase (se 4 (by rfl) ⟨83439, by rfl⟩ : syracuseStep 890021 = 166879) (by norm_num)
theorem B1184957 : Blo 523799 1184957 := bbase (se 3 (by rfl) ⟨222179, by rfl⟩ : syracuseStep 1184957 = 444359) (by norm_num)
theorem B1119437 : Blo 523799 1119437 := bbase (se 3 (by rfl) ⟨209894, by rfl⟩ : syracuseStep 1119437 = 419789) (by norm_num)
theorem B1185029 : Blo 523799 1185029 := bbase (se 4 (by rfl) ⟨111096, by rfl⟩ : syracuseStep 1185029 = 222193) (by norm_num)
theorem B562469 : Blo 523799 562469 := bbase (se 4 (by rfl) ⟨52731, by rfl⟩ : syracuseStep 562469 = 105463) (by norm_num)
theorem B890149 : Blo 523799 890149 := bbase (se 4 (by rfl) ⟨83451, by rfl⟩ : syracuseStep 890149 = 166903) (by norm_num)
theorem B1119557 : Blo 523799 1119557 := bbase (se 4 (by rfl) ⟨104958, by rfl⟩ : syracuseStep 1119557 = 209917) (by norm_num)
theorem B1185101 : Blo 523799 1185101 := bbase (se 3 (by rfl) ⟨222206, by rfl⟩ : syracuseStep 1185101 = 444413) (by norm_num)
theorem B890237 : Blo 523799 890237 := bbase (se 3 (by rfl) ⟨166919, by rfl⟩ : syracuseStep 890237 = 333839) (by norm_num)
theorem B1185173 : Blo 523799 1185173 := bbase (se 6 (by rfl) ⟨27777, by rfl⟩ : syracuseStep 1185173 = 55555) (by norm_num)
theorem B1185245 : Blo 523799 1185245 := bbase (se 3 (by rfl) ⟨222233, by rfl⟩ : syracuseStep 1185245 = 444467) (by norm_num)
theorem B890365 : Blo 523799 890365 := bbase (se 3 (by rfl) ⟨166943, by rfl⟩ : syracuseStep 890365 = 333887) (by norm_num)
theorem B562717 : Blo 523799 562717 := bbase (se 3 (by rfl) ⟨105509, by rfl⟩ : syracuseStep 562717 = 211019) (by norm_num)
theorem B2659877 : Blo 523799 2659877 := bbase (se 4 (by rfl) ⟨249363, by rfl⟩ : syracuseStep 2659877 = 498727) (by norm_num)
theorem B1775141 : Blo 523799 1775141 := bbase (se 4 (by rfl) ⟨166419, by rfl⟩ : syracuseStep 1775141 = 332839) (by norm_num)
theorem B1185317 : Blo 523799 1185317 := bbase (se 4 (by rfl) ⟨111123, by rfl⟩ : syracuseStep 1185317 = 222247) (by norm_num)
theorem B890453 : Blo 523799 890453 := bbase (se 8 (by rfl) ⟨5217, by rfl⟩ : syracuseStep 890453 = 10435) (by norm_num)
theorem B1185389 : Blo 523799 1185389 := bbase (se 3 (by rfl) ⟨222260, by rfl⟩ : syracuseStep 1185389 = 444521) (by norm_num)
theorem B1185461 : Blo 523799 1185461 := bbase (se 5 (by rfl) ⟨55568, by rfl⟩ : syracuseStep 1185461 = 111137) (by norm_num)
theorem B890581 : Blo 523799 890581 := bbase (se 7 (by rfl) ⟨10436, by rfl⟩ : syracuseStep 890581 = 20873) (by norm_num)
theorem B1185533 : Blo 523799 1185533 := bbase (se 3 (by rfl) ⟨222287, by rfl⟩ : syracuseStep 1185533 = 444575) (by norm_num)
theorem B1185605 : Blo 523799 1185605 := bbase (se 4 (by rfl) ⟨111150, by rfl⟩ : syracuseStep 1185605 = 222301) (by norm_num)
theorem B1185677 : Blo 523799 1185677 := bbase (se 3 (by rfl) ⟨222314, by rfl⟩ : syracuseStep 1185677 = 444629) (by norm_num)
theorem B1120189 : Blo 523799 1120189 := bbase (se 3 (by rfl) ⟨210035, by rfl⟩ : syracuseStep 1120189 = 420071) (by norm_num)
theorem B563149 : Blo 523799 563149 := bbase (se 3 (by rfl) ⟨105590, by rfl⟩ : syracuseStep 563149 = 211181) (by norm_num)
theorem B1775573 : Blo 523799 1775573 := bbase (se 7 (by rfl) ⟨20807, by rfl⟩ : syracuseStep 1775573 = 41615) (by norm_num)
theorem B1185749 : Blo 523799 1185749 := bbase (se 7 (by rfl) ⟨13895, by rfl⟩ : syracuseStep 1185749 = 27791) (by norm_num)
theorem B563221 : Blo 523799 563221 := bbase (se 6 (by rfl) ⟨13200, by rfl⟩ : syracuseStep 563221 = 26401) (by norm_num)
theorem B1185821 : Blo 523799 1185821 := bbase (se 3 (by rfl) ⟨222341, by rfl⟩ : syracuseStep 1185821 = 444683) (by norm_num)
theorem B1251389 : Blo 523799 1251389 := bbase (se 3 (by rfl) ⟨234635, by rfl⟩ : syracuseStep 1251389 = 469271) (by norm_num)
theorem B1185893 : Blo 523799 1185893 := bbase (se 4 (by rfl) ⟨111177, by rfl⟩ : syracuseStep 1185893 = 222355) (by norm_num)
theorem B1185965 : Blo 523799 1185965 := bbase (se 3 (by rfl) ⟨222368, by rfl⟩ : syracuseStep 1185965 = 444737) (by norm_num)
theorem B1186037 : Blo 523799 1186037 := bbase (se 5 (by rfl) ⟨55595, by rfl⟩ : syracuseStep 1186037 = 111191) (by norm_num)
theorem B1186109 : Blo 523799 1186109 := bbase (se 3 (by rfl) ⟨222395, by rfl⟩ : syracuseStep 1186109 = 444791) (by norm_num)
theorem B1776005 : Blo 523799 1776005 := bbase (se 4 (by rfl) ⟨166500, by rfl⟩ : syracuseStep 1776005 = 333001) (by norm_num)
theorem B1186181 : Blo 523799 1186181 := bbase (se 4 (by rfl) ⟨111204, by rfl⟩ : syracuseStep 1186181 = 222409) (by norm_num)
theorem B563593 : Blo 523799 563593 := bbase (se 2 (by rfl) ⟨211347, by rfl⟩ : syracuseStep 563593 = 422695) (by norm_num)
theorem B1186253 : Blo 523799 1186253 := bbase (se 3 (by rfl) ⟨222422, by rfl⟩ : syracuseStep 1186253 = 444845) (by norm_num)
theorem B1186325 : Blo 523799 1186325 := bbase (se 6 (by rfl) ⟨27804, by rfl⟩ : syracuseStep 1186325 = 55609) (by norm_num)
theorem B4495925 : Blo 523799 4495925 := bbase (se 5 (by rfl) ⟨210746, by rfl⟩ : syracuseStep 4495925 = 421493) (by norm_num)
theorem B1186397 : Blo 523799 1186397 := bbase (se 3 (by rfl) ⟨222449, by rfl⟩ : syracuseStep 1186397 = 444899) (by norm_num)
theorem B6396565 : Blo 523799 6396565 := bbase (se 6 (by rfl) ⟨149919, by rfl⟩ : syracuseStep 6396565 = 299839) (by norm_num)
theorem B1186469 : Blo 523799 1186469 := bbase (se 4 (by rfl) ⟨111231, by rfl⟩ : syracuseStep 1186469 = 222463) (by norm_num)
theorem B629429 : Blo 523799 629429 := bbase (se 5 (by rfl) ⟨29504, by rfl⟩ : syracuseStep 629429 = 59009) (by norm_num)
theorem B1186541 : Blo 523799 1186541 := bbase (se 3 (by rfl) ⟨222476, by rfl⟩ : syracuseStep 1186541 = 444953) (by norm_num)
theorem B629545 : Blo 523799 629545 := bbase (se 2 (by rfl) ⟨236079, by rfl⟩ : syracuseStep 629545 = 472159) (by norm_num)
theorem B1121077 : Blo 523799 1121077 := bbase (se 5 (by rfl) ⟨52550, by rfl⟩ : syracuseStep 1121077 = 105101) (by norm_num)
theorem B2661173 : Blo 523799 2661173 := bbase (se 5 (by rfl) ⟨124742, by rfl⟩ : syracuseStep 2661173 = 249485) (by norm_num)
theorem B1776437 : Blo 523799 1776437 := bbase (se 5 (by rfl) ⟨83270, by rfl⟩ : syracuseStep 1776437 = 166541) (by norm_num)
theorem B1186613 : Blo 523799 1186613 := bbase (se 5 (by rfl) ⟨55622, by rfl⟩ : syracuseStep 1186613 = 111245) (by norm_num)
theorem B1186685 : Blo 523799 1186685 := bbase (se 3 (by rfl) ⟨222503, by rfl⟩ : syracuseStep 1186685 = 445007) (by norm_num)
theorem B1121197 : Blo 523799 1121197 := bbase (se 3 (by rfl) ⟨210224, by rfl⟩ : syracuseStep 1121197 = 420449) (by norm_num)
theorem B1186757 : Blo 523799 1186757 := bbase (se 4 (by rfl) ⟨111258, by rfl⟩ : syracuseStep 1186757 = 222517) (by norm_num)
theorem B629741 : Blo 523799 629741 := bbase (se 3 (by rfl) ⟨118076, by rfl⟩ : syracuseStep 629741 = 236153) (by norm_num)
theorem B1186829 : Blo 523799 1186829 := bbase (se 3 (by rfl) ⟨222530, by rfl⟩ : syracuseStep 1186829 = 445061) (by norm_num)
theorem B1219645 : Blo 523799 1219645 := bbase (se 3 (by rfl) ⟨228683, by rfl⟩ : syracuseStep 1219645 = 457367) (by norm_num)
theorem B1186901 : Blo 523799 1186901 := bbase (se 8 (by rfl) ⟨6954, by rfl⟩ : syracuseStep 1186901 = 13909) (by norm_num)
theorem B1186973 : Blo 523799 1186973 := bbase (se 3 (by rfl) ⟨222557, by rfl⟩ : syracuseStep 1186973 = 445115) (by norm_num)
theorem B1121453 : Blo 523799 1121453 := bbase (se 3 (by rfl) ⟨210272, by rfl⟩ : syracuseStep 1121453 = 420545) (by norm_num)
theorem B1350877 : Blo 523799 1350877 := bbase (se 3 (by rfl) ⟨253289, by rfl⟩ : syracuseStep 1350877 = 506579) (by norm_num)
theorem B531685 : Blo 523799 531685 := bbase (se 4 (by rfl) ⟨49845, by rfl⟩ : syracuseStep 531685 = 99691) (by norm_num)
theorem B1776869 : Blo 523799 1776869 := bbase (se 4 (by rfl) ⟨166581, by rfl⟩ : syracuseStep 1776869 = 333163) (by norm_num)
theorem B1187045 : Blo 523799 1187045 := bbase (se 4 (by rfl) ⟨111285, by rfl⟩ : syracuseStep 1187045 = 222571) (by norm_num)
theorem B1187117 : Blo 523799 1187117 := bbase (se 3 (by rfl) ⟨222584, by rfl⟩ : syracuseStep 1187117 = 445169) (by norm_num)
theorem B1187189 : Blo 523799 1187189 := bbase (se 5 (by rfl) ⟨55649, by rfl⟩ : syracuseStep 1187189 = 111299) (by norm_num)
theorem B2989493 : Blo 523799 2989493 := bbase (se 5 (by rfl) ⟨140132, by rfl⟩ : syracuseStep 2989493 = 280265) (by norm_num)
theorem B1187261 : Blo 523799 1187261 := bbase (se 3 (by rfl) ⟨222611, by rfl⟩ : syracuseStep 1187261 = 445223) (by norm_num)
theorem B663005 : Blo 523799 663005 := bbase (se 3 (by rfl) ⟨124313, by rfl⟩ : syracuseStep 663005 = 248627) (by norm_num)
theorem B531937 : Blo 523799 531937 := bbase (se 2 (by rfl) ⟨199476, by rfl⟩ : syracuseStep 531937 = 398953) (by norm_num)
theorem B1187333 : Blo 523799 1187333 := bbase (se 4 (by rfl) ⟨111312, by rfl⟩ : syracuseStep 1187333 = 222625) (by norm_num)
theorem B630289 : Blo 523799 630289 := bbase (se 2 (by rfl) ⟨236358, by rfl⟩ : syracuseStep 630289 = 472717) (by norm_num)
theorem B663061 : Blo 523799 663061 := bbase (se 6 (by rfl) ⟨15540, by rfl⟩ : syracuseStep 663061 = 31081) (by norm_num)
theorem B1187405 : Blo 523799 1187405 := bbase (se 3 (by rfl) ⟨222638, by rfl⟩ : syracuseStep 1187405 = 445277) (by norm_num)
theorem B663157 : Blo 523799 663157 := bbase (se 5 (by rfl) ⟨31085, by rfl⟩ : syracuseStep 663157 = 62171) (by norm_num)
theorem B1351309 : Blo 523799 1351309 := bbase (se 3 (by rfl) ⟨253370, by rfl⟩ : syracuseStep 1351309 = 506741) (by norm_num)
theorem B1777301 : Blo 523799 1777301 := bbase (se 6 (by rfl) ⟨41655, by rfl⟩ : syracuseStep 1777301 = 83311) (by norm_num)
theorem B1187477 : Blo 523799 1187477 := bbase (se 6 (by rfl) ⟨27831, by rfl⟩ : syracuseStep 1187477 = 55663) (by norm_num)
theorem B630433 : Blo 523799 630433 := bbase (se 2 (by rfl) ⟨236412, by rfl⟩ : syracuseStep 630433 = 472825) (by norm_num)
theorem B2530997 : Blo 523799 2530997 := bbase (se 5 (by rfl) ⟨118640, by rfl⟩ : syracuseStep 2530997 = 237281) (by norm_num)
theorem B1187549 : Blo 523799 1187549 := bbase (se 3 (by rfl) ⟨222665, by rfl⟩ : syracuseStep 1187549 = 445331) (by norm_num)
theorem B1679093 : Blo 523799 1679093 := bbase (se 5 (by rfl) ⟨78707, by rfl⟩ : syracuseStep 1679093 = 157415) (by norm_num)
theorem B532217 : Blo 523799 532217 := bbase (se 2 (by rfl) ⟨199581, by rfl⟩ : syracuseStep 532217 = 399163) (by norm_num)
theorem B663329 : Blo 523799 663329 := bbase (se 2 (by rfl) ⟨248748, by rfl⟩ : syracuseStep 663329 = 497497) (by norm_num)
theorem B663385 : Blo 523799 663385 := bbase (se 2 (by rfl) ⟨248769, by rfl⟩ : syracuseStep 663385 = 497539) (by norm_num)
theorem B663481 : Blo 523799 663481 := bbase (se 2 (by rfl) ⟨248805, by rfl⟩ : syracuseStep 663481 = 497611) (by norm_num)
theorem B2400245 : Blo 523799 2400245 := bbase (se 5 (by rfl) ⟨112511, by rfl⟩ : syracuseStep 2400245 = 225023) (by norm_num)
theorem B1122341 : Blo 523799 1122341 := bbase (se 4 (by rfl) ⟨105219, by rfl⟩ : syracuseStep 1122341 = 210439) (by norm_num)
theorem B1351741 : Blo 523799 1351741 := bbase (se 3 (by rfl) ⟨253451, by rfl⟩ : syracuseStep 1351741 = 506903) (by norm_num)
theorem B2662469 : Blo 523799 2662469 := bbase (se 4 (by rfl) ⟨249606, by rfl⟩ : syracuseStep 2662469 = 499213) (by norm_num)
theorem B1777733 : Blo 523799 1777733 := bbase (se 4 (by rfl) ⟨166662, by rfl⟩ : syracuseStep 1777733 = 333325) (by norm_num)
theorem B663653 : Blo 523799 663653 := bbase (se 4 (by rfl) ⟨62217, by rfl⟩ : syracuseStep 663653 = 124435) (by norm_num)
theorem B532585 : Blo 523799 532585 := bbase (se 2 (by rfl) ⟨199719, by rfl⟩ : syracuseStep 532585 = 399439) (by norm_num)
theorem B663709 : Blo 523799 663709 := bbase (se 3 (by rfl) ⟨124445, by rfl⟩ : syracuseStep 663709 = 248891) (by norm_num)
theorem B2695349 : Blo 523799 2695349 := bbase (se 5 (by rfl) ⟨126344, by rfl⟩ : syracuseStep 2695349 = 252689) (by norm_num)
theorem B663805 : Blo 523799 663805 := bbase (se 3 (by rfl) ⟨124463, by rfl⟩ : syracuseStep 663805 = 248927) (by norm_num)
theorem B1122581 : Blo 523799 1122581 := bbase (se 6 (by rfl) ⟨26310, by rfl⟩ : syracuseStep 1122581 = 52621) (by norm_num)
theorem B532901 : Blo 523799 532901 := bbase (se 4 (by rfl) ⟨49959, by rfl⟩ : syracuseStep 532901 = 99919) (by norm_num)
theorem B663977 : Blo 523799 663977 := bbase (se 2 (by rfl) ⟨248991, by rfl⟩ : syracuseStep 663977 = 497983) (by norm_num)
theorem B664033 : Blo 523799 664033 := bbase (se 2 (by rfl) ⟨249012, by rfl⟩ : syracuseStep 664033 = 498025) (by norm_num)
theorem B1778165 : Blo 523799 1778165 := bbase (se 5 (by rfl) ⟨83351, by rfl⟩ : syracuseStep 1778165 = 166703) (by norm_num)
theorem B664129 : Blo 523799 664129 := bbase (se 2 (by rfl) ⟨249048, by rfl⟩ : syracuseStep 664129 = 498097) (by norm_num)
theorem B631481 : Blo 523799 631481 := bbase (se 2 (by rfl) ⟨236805, by rfl⟩ : syracuseStep 631481 = 473611) (by norm_num)
theorem B1516229 : Blo 523799 1516229 := bbase (se 4 (by rfl) ⟨142146, by rfl⟩ : syracuseStep 1516229 = 284293) (by norm_num)
theorem B664301 : Blo 523799 664301 := bbase (se 3 (by rfl) ⟨124556, by rfl⟩ : syracuseStep 664301 = 249113) (by norm_num)
theorem B2138869 : Blo 523799 2138869 := bbase (se 5 (by rfl) ⟨100259, by rfl⟩ : syracuseStep 2138869 = 200519) (by norm_num)
theorem B1123085 : Blo 523799 1123085 := bbase (se 3 (by rfl) ⟨210578, by rfl⟩ : syracuseStep 1123085 = 421157) (by norm_num)
theorem B1123093 : Blo 523799 1123093 := bbase (se 6 (by rfl) ⟨26322, by rfl⟩ : syracuseStep 1123093 = 52645) (by norm_num)
theorem B664357 : Blo 523799 664357 := bbase (se 4 (by rfl) ⟨62283, by rfl⟩ : syracuseStep 664357 = 124567) (by norm_num)
theorem B664453 : Blo 523799 664453 := bbase (se 4 (by rfl) ⟨62292, by rfl⟩ : syracuseStep 664453 = 124585) (by norm_num)
theorem B1778597 : Blo 523799 1778597 := bbase (se 4 (by rfl) ⟨166743, by rfl⟩ : syracuseStep 1778597 = 333487) (by norm_num)
theorem B2532341 : Blo 523799 2532341 := bbase (se 5 (by rfl) ⟨118703, by rfl⟩ : syracuseStep 2532341 = 237407) (by norm_num)
theorem B631813 : Blo 523799 631813 := bbase (se 4 (by rfl) ⟨59232, by rfl⟩ : syracuseStep 631813 = 118465) (by norm_num)
theorem B664625 : Blo 523799 664625 := bbase (se 2 (by rfl) ⟨249234, by rfl⟩ : syracuseStep 664625 = 498469) (by norm_num)
theorem B664681 : Blo 523799 664681 := bbase (se 2 (by rfl) ⟨249255, by rfl⟩ : syracuseStep 664681 = 498511) (by norm_num)
theorem B1025141 : Blo 523799 1025141 := bbase (se 5 (by rfl) ⟨48053, by rfl⟩ : syracuseStep 1025141 = 96107) (by norm_num)
theorem B664777 : Blo 523799 664777 := bbase (se 2 (by rfl) ⟨249291, by rfl⟩ : syracuseStep 664777 = 498583) (by norm_num)
theorem B533729 : Blo 523799 533729 := bbase (se 2 (by rfl) ⟨200148, by rfl⟩ : syracuseStep 533729 = 400297) (by norm_num)
theorem B599305 : Blo 523799 599305 := bbase (se 2 (by rfl) ⟨224739, by rfl⟩ : syracuseStep 599305 = 449479) (by norm_num)
theorem B2270501 : Blo 523799 2270501 := bbase (se 4 (by rfl) ⟨212859, by rfl⟩ : syracuseStep 2270501 = 425719) (by norm_num)
theorem B2663765 : Blo 523799 2663765 := bbase (se 12 (by rfl) ⟨975, by rfl⟩ : syracuseStep 2663765 = 1951) (by norm_num)
theorem B1779029 : Blo 523799 1779029 := bbase (se 12 (by rfl) ⟨651, by rfl⟩ : syracuseStep 1779029 = 1303) (by norm_num)
theorem B1353053 : Blo 523799 1353053 := bbase (se 3 (by rfl) ⟨253697, by rfl⟩ : syracuseStep 1353053 = 507395) (by norm_num)
theorem B599405 : Blo 523799 599405 := bbase (se 3 (by rfl) ⟨112388, by rfl⟩ : syracuseStep 599405 = 224777) (by norm_num)
theorem B664949 : Blo 523799 664949 := bbase (se 5 (by rfl) ⟨31169, by rfl⟩ : syracuseStep 664949 = 62339) (by norm_num)
theorem B665005 : Blo 523799 665005 := bbase (se 3 (by rfl) ⟨124688, by rfl⟩ : syracuseStep 665005 = 249377) (by norm_num)
theorem B4498901 : Blo 523799 4498901 := bbase (se 7 (by rfl) ⟨52721, by rfl⟩ : syracuseStep 4498901 = 105443) (by norm_num)
theorem B533989 : Blo 523799 533989 := bbase (se 4 (by rfl) ⟨50061, by rfl⟩ : syracuseStep 533989 = 100123) (by norm_num)
theorem B665101 : Blo 523799 665101 := bbase (se 3 (by rfl) ⟨124706, by rfl⟩ : syracuseStep 665101 = 249413) (by norm_num)
theorem B1680949 : Blo 523799 1680949 := bbase (se 5 (by rfl) ⟨78794, by rfl⟩ : syracuseStep 1680949 = 157589) (by norm_num)
theorem B665273 : Blo 523799 665273 := bbase (se 2 (by rfl) ⟨249477, by rfl⟩ : syracuseStep 665273 = 498955) (by norm_num)
theorem B665329 : Blo 523799 665329 := bbase (se 2 (by rfl) ⟨249498, by rfl⟩ : syracuseStep 665329 = 498997) (by norm_num)
theorem B1779461 : Blo 523799 1779461 := bbase (se 4 (by rfl) ⟨166824, by rfl⟩ : syracuseStep 1779461 = 333649) (by norm_num)
theorem B665425 : Blo 523799 665425 := bbase (se 2 (by rfl) ⟨249534, by rfl⟩ : syracuseStep 665425 = 499069) (by norm_num)
theorem B2238293 : Blo 523799 2238293 := bbase (se 9 (by rfl) ⟨6557, by rfl⟩ : syracuseStep 2238293 = 13115) (by norm_num)
theorem B534361 : Blo 523799 534361 := bbase (se 2 (by rfl) ⟨200385, by rfl⟩ : syracuseStep 534361 = 400771) (by norm_num)
theorem B1124221 : Blo 523799 1124221 := bbase (se 3 (by rfl) ⟨210791, by rfl⟩ : syracuseStep 1124221 = 421583) (by norm_num)
theorem B632701 : Blo 523799 632701 := bbase (se 3 (by rfl) ⟨118631, by rfl⟩ : syracuseStep 632701 = 237263) (by norm_num)
theorem B862093 : Blo 523799 862093 := bbase (se 3 (by rfl) ⟨161642, by rfl⟩ : syracuseStep 862093 = 323285) (by norm_num)
theorem B665597 : Blo 523799 665597 := bbase (se 3 (by rfl) ⟨124799, by rfl⟩ : syracuseStep 665597 = 249599) (by norm_num)
theorem B665653 : Blo 523799 665653 := bbase (se 5 (by rfl) ⟨31202, by rfl⟩ : syracuseStep 665653 = 62405) (by norm_num)
theorem B3188821 : Blo 523799 3188821 := bbase (se 8 (by rfl) ⟨18684, by rfl⟩ : syracuseStep 3188821 = 37369) (by norm_num)
theorem B665749 : Blo 523799 665749 := bbase (se 6 (by rfl) ⟨15603, by rfl⟩ : syracuseStep 665749 = 31207) (by norm_num)
theorem B534685 : Blo 523799 534685 := bbase (se 3 (by rfl) ⟨100253, by rfl⟩ : syracuseStep 534685 = 200507) (by norm_num)
theorem B1779893 : Blo 523799 1779893 := bbase (se 5 (by rfl) ⟨83432, by rfl⟩ : syracuseStep 1779893 = 166865) (by norm_num)
theorem B1124597 : Blo 523799 1124597 := bbase (se 5 (by rfl) ⟨52715, by rfl⟩ : syracuseStep 1124597 = 105431) (by norm_num)
theorem B600313 : Blo 523799 600313 := bbase (se 2 (by rfl) ⟨225117, by rfl⟩ : syracuseStep 600313 = 450235) (by norm_num)
theorem B665921 : Blo 523799 665921 := bbase (se 2 (by rfl) ⟨249720, by rfl⟩ : syracuseStep 665921 = 499441) (by norm_num)
theorem B665977 : Blo 523799 665977 := bbase (se 2 (by rfl) ⟨249741, by rfl⟩ : syracuseStep 665977 = 499483) (by norm_num)
theorem B567685 : Blo 523799 567685 := bbase (se 4 (by rfl) ⟨53220, by rfl⟩ : syracuseStep 567685 = 106441) (by norm_num)
theorem B666073 : Blo 523799 666073 := bbase (se 2 (by rfl) ⟨249777, by rfl⟩ : syracuseStep 666073 = 499555) (by norm_num)
theorem B2665061 : Blo 523799 2665061 := bbase (se 4 (by rfl) ⟨249849, by rfl⟩ : syracuseStep 2665061 = 499699) (by norm_num)
theorem B1780325 : Blo 523799 1780325 := bbase (se 4 (by rfl) ⟨166905, by rfl⟩ : syracuseStep 1780325 = 333811) (by norm_num)
theorem B666245 : Blo 523799 666245 := bbase (se 4 (by rfl) ⟨62460, by rfl⟩ : syracuseStep 666245 = 124921) (by norm_num)
theorem B666301 : Blo 523799 666301 := bbase (se 3 (by rfl) ⟨124931, by rfl⟩ : syracuseStep 666301 = 249863) (by norm_num)
theorem B1420021 : Blo 523799 1420021 := bbase (se 5 (by rfl) ⟨66563, by rfl⟩ : syracuseStep 1420021 = 133127) (by norm_num)
theorem B666397 : Blo 523799 666397 := bbase (se 3 (by rfl) ⟨124949, by rfl⟩ : syracuseStep 666397 = 249899) (by norm_num)
theorem B1682309 : Blo 523799 1682309 := bbase (se 4 (by rfl) ⟨157716, by rfl⟩ : syracuseStep 1682309 = 315433) (by norm_num)
theorem B633749 : Blo 523799 633749 := bbase (se 6 (by rfl) ⟨14853, by rfl⟩ : syracuseStep 633749 = 29707) (by norm_num)
theorem B2534341 : Blo 523799 2534341 := bbase (se 4 (by rfl) ⟨237594, by rfl⟩ : syracuseStep 2534341 = 475189) (by norm_num)
theorem B666569 : Blo 523799 666569 := bbase (se 2 (by rfl) ⟨249963, by rfl⟩ : syracuseStep 666569 = 499927) (by norm_num)
theorem B666625 : Blo 523799 666625 := bbase (se 2 (by rfl) ⟨249984, by rfl⟩ : syracuseStep 666625 = 499969) (by norm_num)
theorem B1780757 : Blo 523799 1780757 := bbase (se 6 (by rfl) ⟨41736, by rfl⟩ : syracuseStep 1780757 = 83473) (by norm_num)
theorem B666721 : Blo 523799 666721 := bbase (se 2 (by rfl) ⟨250020, by rfl⟩ : syracuseStep 666721 = 500041) (by norm_num)
theorem B994493 : Blo 523799 994493 := bbase (se 3 (by rfl) ⟨186467, by rfl⟩ : syracuseStep 994493 = 372935) (by norm_num)
theorem B666893 : Blo 523799 666893 := bbase (se 3 (by rfl) ⟨125042, by rfl⟩ : syracuseStep 666893 = 250085) (by norm_num)
theorem B666949 : Blo 523799 666949 := bbase (se 4 (by rfl) ⟨62526, by rfl⟩ : syracuseStep 666949 = 125053) (by norm_num)
theorem B667045 : Blo 523799 667045 := bbase (se 4 (by rfl) ⟨62535, by rfl⟩ : syracuseStep 667045 = 125071) (by norm_num)
theorem B1781189 : Blo 523799 1781189 := bbase (se 4 (by rfl) ⟨166986, by rfl⟩ : syracuseStep 1781189 = 333973) (by norm_num)
theorem B994781 : Blo 523799 994781 := bbase (se 3 (by rfl) ⟨186521, by rfl⟩ : syracuseStep 994781 = 373043) (by norm_num)
theorem B667217 : Blo 523799 667217 := bbase (se 2 (by rfl) ⟨250206, by rfl⟩ : syracuseStep 667217 = 500413) (by norm_num)
theorem B994933 : Blo 523799 994933 := bbase (se 5 (by rfl) ⟨46637, by rfl⟩ : syracuseStep 994933 = 93275) (by norm_num)
theorem B667273 : Blo 523799 667273 := bbase (se 2 (by rfl) ⟨250227, by rfl⟩ : syracuseStep 667273 = 500455) (by norm_num)
theorem B798373 : Blo 523799 798373 := bbase (se 4 (by rfl) ⟨74847, by rfl⟩ : syracuseStep 798373 = 149695) (by norm_num)
theorem B634601 : Blo 523799 634601 := bbase (se 2 (by rfl) ⟨237975, by rfl⟩ : syracuseStep 634601 = 475951) (by norm_num)
theorem B667369 : Blo 523799 667369 := bbase (se 2 (by rfl) ⟨250263, by rfl⟩ : syracuseStep 667369 = 500527) (by norm_num)
theorem B2273093 : Blo 523799 2273093 := bbase (se 4 (by rfl) ⟨213102, by rfl⟩ : syracuseStep 2273093 = 426205) (by norm_num)
theorem B1126237 : Blo 523799 1126237 := bbase (se 3 (by rfl) ⟨211169, by rfl⟩ : syracuseStep 1126237 = 422339) (by norm_num)
theorem B2666357 : Blo 523799 2666357 := bbase (se 5 (by rfl) ⟨124985, by rfl⟩ : syracuseStep 2666357 = 249971) (by norm_num)
theorem B667541 : Blo 523799 667541 := bbase (se 6 (by rfl) ⟨15645, by rfl⟩ : syracuseStep 667541 = 31291) (by norm_num)
theorem B995237 : Blo 523799 995237 := bbase (se 4 (by rfl) ⟨93303, by rfl⟩ : syracuseStep 995237 = 186607) (by norm_num)
theorem B3583925 : Blo 523799 3583925 := bbase (se 5 (by rfl) ⟨167996, by rfl⟩ : syracuseStep 3583925 = 335993) (by norm_num)
theorem B667597 : Blo 523799 667597 := bbase (se 3 (by rfl) ⟨125174, by rfl⟩ : syracuseStep 667597 = 250349) (by norm_num)
theorem B667693 : Blo 523799 667693 := bbase (se 3 (by rfl) ⟨125192, by rfl⟩ : syracuseStep 667693 = 250385) (by norm_num)
theorem B897077 : Blo 523799 897077 := bbase (se 5 (by rfl) ⟨42050, by rfl⟩ : syracuseStep 897077 = 84101) (by norm_num)
theorem B667865 : Blo 523799 667865 := bbase (se 2 (by rfl) ⟨250449, by rfl⟩ : syracuseStep 667865 = 500899) (by norm_num)
theorem B667921 : Blo 523799 667921 := bbase (se 2 (by rfl) ⟨250470, by rfl⟩ : syracuseStep 667921 = 500941) (by norm_num)
theorem B5976341 : Blo 523799 5976341 := bbase (se 6 (by rfl) ⟨140070, by rfl⟩ : syracuseStep 5976341 = 280141) (by norm_num)
theorem B13873493 : Blo 523799 13873493 := bbase (se 10 (by rfl) ⟨20322, by rfl⟩ : syracuseStep 13873493 = 40645) (by norm_num)
theorem B1421957 : Blo 523799 1421957 := bbase (se 4 (by rfl) ⟨133308, by rfl⟩ : syracuseStep 1421957 = 266617) (by norm_num)
theorem B995989 : Blo 523799 995989 := bbase (se 6 (by rfl) ⟨23343, by rfl⟩ : syracuseStep 995989 = 46687) (by norm_num)
theorem B3977909 : Blo 523799 3977909 := bbase (se 5 (by rfl) ⟨186464, by rfl⟩ : syracuseStep 3977909 = 372929) (by norm_num)
theorem B1127125 : Blo 523799 1127125 := bbase (se 7 (by rfl) ⟨13208, by rfl⟩ : syracuseStep 1127125 = 26417) (by norm_num)
theorem B996133 : Blo 523799 996133 := bbase (se 4 (by rfl) ⟨93387, by rfl⟩ : syracuseStep 996133 = 186775) (by norm_num)
theorem B996293 : Blo 523799 996293 := bbase (se 4 (by rfl) ⟨93402, by rfl⟩ : syracuseStep 996293 = 186805) (by norm_num)
theorem B799741 : Blo 523799 799741 := bbase (se 3 (by rfl) ⟨149951, by rfl⟩ : syracuseStep 799741 = 299903) (by norm_num)
theorem B996437 : Blo 523799 996437 := bbase (se 8 (by rfl) ⟨5838, by rfl⟩ : syracuseStep 996437 = 11677) (by norm_num)
theorem B2667653 : Blo 523799 2667653 := bbase (se 4 (by rfl) ⟨250092, by rfl⟩ : syracuseStep 2667653 = 500185) (by norm_num)
theorem B2700485 : Blo 523799 2700485 := bbase (se 4 (by rfl) ⟨253170, by rfl⟩ : syracuseStep 2700485 = 506341) (by norm_num)
theorem B1258733 : Blo 523799 1258733 := bbase (se 3 (by rfl) ⟨236012, by rfl⟩ : syracuseStep 1258733 = 472025) (by norm_num)
theorem B996725 : Blo 523799 996725 := bbase (se 5 (by rfl) ⟨46721, by rfl⟩ : syracuseStep 996725 = 93443) (by norm_num)
theorem B996877 : Blo 523799 996877 := bbase (se 3 (by rfl) ⟨186914, by rfl⟩ : syracuseStep 996877 = 373829) (by norm_num)
theorem B997181 : Blo 523799 997181 := bbase (se 3 (by rfl) ⟨186971, by rfl⟩ : syracuseStep 997181 = 373943) (by norm_num)
theorem B1259405 : Blo 523799 1259405 := bbase (se 3 (by rfl) ⟨236138, by rfl⟩ : syracuseStep 1259405 = 472277) (by norm_num)
theorem B1062877 : Blo 523799 1062877 := bbase (se 3 (by rfl) ⟨199289, by rfl⟩ : syracuseStep 1062877 = 398579) (by norm_num)
theorem B2242565 : Blo 523799 2242565 := bbase (se 4 (by rfl) ⟨210240, by rfl⟩ : syracuseStep 2242565 = 420481) (by norm_num)
theorem B4110421 : Blo 523799 4110421 := bbase (se 8 (by rfl) ⟨24084, by rfl⟩ : syracuseStep 4110421 = 48169) (by norm_num)
theorem B9615509 : Blo 523799 9615509 := bbase (se 6 (by rfl) ⟨225363, by rfl⟩ : syracuseStep 9615509 = 450727) (by norm_num)
theorem B1816757 : Blo 523799 1816757 := bbase (se 5 (by rfl) ⟨85160, by rfl⟩ : syracuseStep 1816757 = 170321) (by norm_num)
theorem B1685717 : Blo 523799 1685717 := bbase (se 7 (by rfl) ⟨19754, by rfl⟩ : syracuseStep 1685717 = 39509) (by norm_num)
theorem B899381 : Blo 523799 899381 := bbase (se 5 (by rfl) ⟨42158, by rfl⟩ : syracuseStep 899381 = 84317) (by norm_num)
theorem B2668949 : Blo 523799 2668949 := bbase (se 6 (by rfl) ⟨62553, by rfl⟩ : syracuseStep 2668949 = 125107) (by norm_num)
theorem B3127733 : Blo 523799 3127733 := bbase (se 5 (by rfl) ⟨146612, by rfl⟩ : syracuseStep 3127733 = 293225) (by norm_num)
theorem B997933 : Blo 523799 997933 := bbase (se 3 (by rfl) ⟨187112, by rfl⟩ : syracuseStep 997933 = 374225) (by norm_num)
theorem B1522229 : Blo 523799 1522229 := bbase (se 5 (by rfl) ⟨71354, by rfl⟩ : syracuseStep 1522229 = 142709) (by norm_num)
theorem B998077 : Blo 523799 998077 := bbase (se 3 (by rfl) ⟨187139, by rfl⟩ : syracuseStep 998077 = 374279) (by norm_num)
theorem B2407141 : Blo 523799 2407141 := bbase (se 4 (by rfl) ⟨225669, by rfl⟩ : syracuseStep 2407141 = 451339) (by norm_num)
theorem B1325909 : Blo 523799 1325909 := bbase (se 9 (by rfl) ⟨3884, by rfl⟩ : syracuseStep 1325909 = 7769) (by norm_num)
theorem B998237 : Blo 523799 998237 := bbase (se 3 (by rfl) ⟨187169, by rfl⟩ : syracuseStep 998237 = 374339) (by norm_num)
theorem B998381 : Blo 523799 998381 := bbase (se 3 (by rfl) ⟨187196, by rfl⟩ : syracuseStep 998381 = 374393) (by norm_num)
theorem B3587125 : Blo 523799 3587125 := bbase (se 5 (by rfl) ⟨168146, by rfl⟩ : syracuseStep 3587125 = 336293) (by norm_num)
theorem B1326253 : Blo 523799 1326253 := bbase (se 3 (by rfl) ⟨248672, by rfl⟩ : syracuseStep 1326253 = 497345) (by norm_num)
theorem B998669 : Blo 523799 998669 := bbase (se 3 (by rfl) ⟨187250, by rfl⟩ : syracuseStep 998669 = 374501) (by norm_num)
theorem B1326365 : Blo 523799 1326365 := bbase (se 3 (by rfl) ⟨248693, by rfl⟩ : syracuseStep 1326365 = 497387) (by norm_num)
theorem B2997557 : Blo 523799 2997557 := bbase (se 5 (by rfl) ⟨140510, by rfl⟩ : syracuseStep 2997557 = 281021) (by norm_num)
theorem B1424789 : Blo 523799 1424789 := bbase (se 6 (by rfl) ⟨33393, by rfl⟩ : syracuseStep 1424789 = 66787) (by norm_num)
theorem B998821 : Blo 523799 998821 := bbase (se 4 (by rfl) ⟨93639, by rfl⟩ : syracuseStep 998821 = 187279) (by norm_num)
theorem B1686997 : Blo 523799 1686997 := bbase (se 7 (by rfl) ⟨19769, by rfl⟩ : syracuseStep 1686997 = 39539) (by norm_num)
theorem B1326557 : Blo 523799 1326557 := bbase (se 3 (by rfl) ⟨248729, by rfl⟩ : syracuseStep 1326557 = 497459) (by norm_num)
theorem B802333 : Blo 523799 802333 := bbase (se 3 (by rfl) ⟨150437, by rfl⟩ : syracuseStep 802333 = 300875) (by norm_num)
theorem B1261165 : Blo 523799 1261165 := bbase (se 3 (by rfl) ⟨236468, by rfl⟩ : syracuseStep 1261165 = 472937) (by norm_num)
theorem B2670245 : Blo 523799 2670245 := bbase (se 4 (by rfl) ⟨250335, by rfl⟩ : syracuseStep 2670245 = 500671) (by norm_num)
theorem B999125 : Blo 523799 999125 := bbase (se 7 (by rfl) ⟨11708, by rfl⟩ : syracuseStep 999125 = 23417) (by norm_num)
theorem B2244341 : Blo 523799 2244341 := bbase (se 5 (by rfl) ⟨105203, by rfl⟩ : syracuseStep 2244341 = 210407) (by norm_num)
theorem B1326901 : Blo 523799 1326901 := bbase (se 5 (by rfl) ⟨62198, by rfl⟩ : syracuseStep 1326901 = 124397) (by norm_num)
theorem B1064765 : Blo 523799 1064765 := bbase (se 3 (by rfl) ⟨199643, by rfl⟩ : syracuseStep 1064765 = 399287) (by norm_num)
theorem B606085 : Blo 523799 606085 := bbase (se 4 (by rfl) ⟨56820, by rfl⟩ : syracuseStep 606085 = 113641) (by norm_num)
theorem B1327013 : Blo 523799 1327013 := bbase (se 4 (by rfl) ⟨124407, by rfl⟩ : syracuseStep 1327013 = 248815) (by norm_num)
theorem B2244581 : Blo 523799 2244581 := bbase (se 4 (by rfl) ⟨210429, by rfl⟩ : syracuseStep 2244581 = 420859) (by norm_num)
theorem B5128181 : Blo 523799 5128181 := bbase (se 5 (by rfl) ⟨240383, by rfl⟩ : syracuseStep 5128181 = 480767) (by norm_num)
theorem B2768933 : Blo 523799 2768933 := bbase (se 4 (by rfl) ⟨259587, by rfl⟩ : syracuseStep 2768933 = 519175) (by norm_num)
theorem B606289 : Blo 523799 606289 := bbase (se 2 (by rfl) ⟨227358, by rfl⟩ : syracuseStep 606289 = 454717) (by norm_num)
theorem B1327205 : Blo 523799 1327205 := bbase (se 4 (by rfl) ⟨124425, by rfl⟩ : syracuseStep 1327205 = 248851) (by norm_num)
theorem B1425557 : Blo 523799 1425557 := bbase (se 6 (by rfl) ⟨33411, by rfl⟩ : syracuseStep 1425557 = 66823) (by norm_num)
theorem B5062837 : Blo 523799 5062837 := bbase (se 5 (by rfl) ⟨237320, by rfl⟩ : syracuseStep 5062837 = 474641) (by norm_num)
theorem B1261781 : Blo 523799 1261781 := bbase (se 7 (by rfl) ⟨14786, by rfl⟩ : syracuseStep 1261781 = 29573) (by norm_num)
theorem B8962325 : Blo 523799 8962325 := bbase (se 6 (by rfl) ⟨210054, by rfl⟩ : syracuseStep 8962325 = 420109) (by norm_num)
theorem B1327549 : Blo 523799 1327549 := bbase (se 3 (by rfl) ⟨248915, by rfl⟩ : syracuseStep 1327549 = 497831) (by norm_num)
theorem B999877 : Blo 523799 999877 := bbase (se 4 (by rfl) ⟨93738, by rfl⟩ : syracuseStep 999877 = 187477) (by norm_num)
theorem B2998741 : Blo 523799 2998741 := bbase (se 7 (by rfl) ⟨35141, by rfl⟩ : syracuseStep 2998741 = 70283) (by norm_num)
theorem B672277 : Blo 523799 672277 := bbase (se 6 (by rfl) ⟨15756, by rfl⟩ : syracuseStep 672277 = 31513) (by norm_num)
theorem B541225 : Blo 523799 541225 := bbase (se 2 (by rfl) ⟨202959, by rfl⟩ : syracuseStep 541225 = 405919) (by norm_num)
theorem B1327661 : Blo 523799 1327661 := bbase (se 3 (by rfl) ⟨248936, by rfl⟩ : syracuseStep 1327661 = 497873) (by norm_num)
theorem B1000021 : Blo 523799 1000021 := bbase (se 8 (by rfl) ⟨5859, by rfl⟩ : syracuseStep 1000021 = 11719) (by norm_num)
theorem B1327853 : Blo 523799 1327853 := bbase (se 3 (by rfl) ⟨248972, by rfl⟩ : syracuseStep 1327853 = 497945) (by norm_num)
theorem B1000181 : Blo 523799 1000181 := bbase (se 5 (by rfl) ⟨46883, by rfl⟩ : syracuseStep 1000181 = 93767) (by norm_num)
theorem B1688357 : Blo 523799 1688357 := bbase (se 4 (by rfl) ⟨158283, by rfl⟩ : syracuseStep 1688357 = 316567) (by norm_num)
theorem B1491797 : Blo 523799 1491797 := bbase (se 9 (by rfl) ⟨4370, by rfl⟩ : syracuseStep 1491797 = 8741) (by norm_num)
theorem B1000325 : Blo 523799 1000325 := bbase (se 4 (by rfl) ⟨93780, by rfl⟩ : syracuseStep 1000325 = 187561) (by norm_num)
theorem B1688485 : Blo 523799 1688485 := bbase (se 4 (by rfl) ⟨158295, by rfl⟩ : syracuseStep 1688485 = 316591) (by norm_num)
theorem B1065901 : Blo 523799 1065901 := bbase (se 3 (by rfl) ⟨199856, by rfl⟩ : syracuseStep 1065901 = 399713) (by norm_num)
theorem B2671541 : Blo 523799 2671541 := bbase (se 5 (by rfl) ⟨125228, by rfl⟩ : syracuseStep 2671541 = 250457) (by norm_num)
theorem B672725 : Blo 523799 672725 := bbase (se 7 (by rfl) ⟨7883, by rfl⟩ : syracuseStep 672725 = 15767) (by norm_num)
theorem B1262549 : Blo 523799 1262549 := bbase (se 7 (by rfl) ⟨14795, by rfl⟩ : syracuseStep 1262549 = 29591) (by norm_num)
theorem B1262557 : Blo 523799 1262557 := bbase (se 3 (by rfl) ⟨236729, by rfl⟩ : syracuseStep 1262557 = 473459) (by norm_num)
theorem B1328197 : Blo 523799 1328197 := bbase (se 4 (by rfl) ⟨124518, by rfl⟩ : syracuseStep 1328197 = 249037) (by norm_num)
theorem B1000613 : Blo 523799 1000613 := bbase (se 4 (by rfl) ⟨93807, by rfl⟩ : syracuseStep 1000613 = 187615) (by norm_num)
theorem B1688741 : Blo 523799 1688741 := bbase (se 4 (by rfl) ⟨158319, by rfl⟩ : syracuseStep 1688741 = 316639) (by norm_num)
theorem B3884213 : Blo 523799 3884213 := bbase (se 5 (by rfl) ⟨182072, by rfl⟩ : syracuseStep 3884213 = 364145) (by norm_num)
theorem B1328309 : Blo 523799 1328309 := bbase (se 5 (by rfl) ⟨62264, by rfl⟩ : syracuseStep 1328309 = 124529) (by norm_num)
theorem B607541 : Blo 523799 607541 := bbase (se 5 (by rfl) ⟨28478, by rfl⟩ : syracuseStep 607541 = 56957) (by norm_num)
theorem B1000765 : Blo 523799 1000765 := bbase (se 3 (by rfl) ⟨187643, by rfl⟩ : syracuseStep 1000765 = 375287) (by norm_num)
theorem B1328501 : Blo 523799 1328501 := bbase (se 5 (by rfl) ⟨62273, by rfl⟩ : syracuseStep 1328501 = 124547) (by norm_num)
theorem B902549 : Blo 523799 902549 := bbase (se 6 (by rfl) ⟨21153, by rfl⟩ : syracuseStep 902549 = 42307) (by norm_num)
theorem B607657 : Blo 523799 607657 := bbase (se 2 (by rfl) ⟨227871, by rfl⟩ : syracuseStep 607657 = 455743) (by norm_num)
theorem B574921 : Blo 523799 574921 := bbase (se 2 (by rfl) ⟨215595, by rfl⟩ : syracuseStep 574921 = 431191) (by norm_num)
theorem B1492469 : Blo 523799 1492469 := bbase (se 5 (by rfl) ⟨69959, by rfl⟩ : syracuseStep 1492469 = 139919) (by norm_num)
theorem B1001069 : Blo 523799 1001069 := bbase (se 3 (by rfl) ⟨187700, by rfl⟩ : syracuseStep 1001069 = 375401) (by norm_num)
theorem B2737781 : Blo 523799 2737781 := bbase (se 5 (by rfl) ⟨128333, by rfl⟩ : syracuseStep 2737781 = 256667) (by norm_num)
theorem B1328845 : Blo 523799 1328845 := bbase (se 3 (by rfl) ⟨249158, by rfl⟩ : syracuseStep 1328845 = 498317) (by norm_num)
theorem B3032821 : Blo 523799 3032821 := bbase (se 5 (by rfl) ⟨142163, by rfl⟩ : syracuseStep 3032821 = 284327) (by norm_num)
theorem B1263365 : Blo 523799 1263365 := bbase (se 4 (by rfl) ⟨118440, by rfl⟩ : syracuseStep 1263365 = 236881) (by norm_num)
theorem B3786517 : Blo 523799 3786517 := bbase (se 6 (by rfl) ⟨88746, by rfl⟩ : syracuseStep 3786517 = 177493) (by norm_num)
theorem B1328957 : Blo 523799 1328957 := bbase (se 3 (by rfl) ⟨249179, by rfl⟩ : syracuseStep 1328957 = 498359) (by norm_num)
theorem B1492901 : Blo 523799 1492901 := bbase (se 4 (by rfl) ⟨139959, by rfl⟩ : syracuseStep 1492901 = 279919) (by norm_num)
theorem B1329149 : Blo 523799 1329149 := bbase (se 3 (by rfl) ⟨249215, by rfl⟩ : syracuseStep 1329149 = 498431) (by norm_num)
theorem B2246869 : Blo 523799 2246869 := bbase (se 7 (by rfl) ⟨26330, by rfl⟩ : syracuseStep 2246869 = 52661) (by norm_num)
theorem B1329493 : Blo 523799 1329493 := bbase (se 10 (by rfl) ⟨1947, by rfl⟩ : syracuseStep 1329493 = 3895) (by norm_num)
theorem B1001821 : Blo 523799 1001821 := bbase (se 3 (by rfl) ⟨187841, by rfl⟩ : syracuseStep 1001821 = 375683) (by norm_num)
theorem B3000725 : Blo 523799 3000725 := bbase (se 6 (by rfl) ⟨70329, by rfl⟩ : syracuseStep 3000725 = 140659) (by norm_num)
theorem B1329605 : Blo 523799 1329605 := bbase (se 4 (by rfl) ⟨124650, by rfl⟩ : syracuseStep 1329605 = 249301) (by norm_num)
theorem B1001965 : Blo 523799 1001965 := bbase (se 3 (by rfl) ⟨187868, by rfl⟩ : syracuseStep 1001965 = 375737) (by norm_num)
theorem B1329797 : Blo 523799 1329797 := bbase (se 4 (by rfl) ⟨124668, by rfl⟩ : syracuseStep 1329797 = 249337) (by norm_num)
theorem B1493653 : Blo 523799 1493653 := bbase (se 6 (by rfl) ⟨35007, by rfl⟩ : syracuseStep 1493653 = 70015) (by norm_num)
theorem B1198901 : Blo 523799 1198901 := bbase (se 5 (by rfl) ⟨56198, by rfl⟩ : syracuseStep 1198901 = 112397) (by norm_num)
theorem B5065685 : Blo 523799 5065685 := bbase (se 7 (by rfl) ⟨59363, by rfl⟩ : syracuseStep 5065685 = 118727) (by norm_num)
theorem B1330141 : Blo 523799 1330141 := bbase (se 3 (by rfl) ⟨249401, by rfl⟩ : syracuseStep 1330141 = 498803) (by norm_num)
theorem B1330253 : Blo 523799 1330253 := bbase (se 3 (by rfl) ⟨249422, by rfl⟩ : syracuseStep 1330253 = 498845) (by norm_num)
theorem B1330445 : Blo 523799 1330445 := bbase (se 3 (by rfl) ⟨249458, by rfl⟩ : syracuseStep 1330445 = 498917) (by norm_num)
theorem B1330789 : Blo 523799 1330789 := bbase (se 4 (by rfl) ⟨124761, by rfl⟩ : syracuseStep 1330789 = 249523) (by norm_num)
theorem B708221 : Blo 523799 708221 := bbase (se 3 (by rfl) ⟨132791, by rfl⟩ : syracuseStep 708221 = 265583) (by norm_num)
theorem B2248357 : Blo 523799 2248357 := bbase (se 4 (by rfl) ⟨210783, by rfl⟩ : syracuseStep 2248357 = 421567) (by norm_num)
theorem B2248373 : Blo 523799 2248373 := bbase (se 5 (by rfl) ⟨105392, by rfl⟩ : syracuseStep 2248373 = 210785) (by norm_num)
theorem B1330901 : Blo 523799 1330901 := bbase (se 7 (by rfl) ⟨15596, by rfl⟩ : syracuseStep 1330901 = 31193) (by norm_num)
theorem B577253 : Blo 523799 577253 := bbase (se 4 (by rfl) ⟨54117, by rfl⟩ : syracuseStep 577253 = 108235) (by norm_num)
theorem B839501 : Blo 523799 839501 := bbase (se 3 (by rfl) ⟨157406, by rfl⟩ : syracuseStep 839501 = 314813) (by norm_num)
theorem B1331093 : Blo 523799 1331093 := bbase (se 6 (by rfl) ⟨31197, by rfl⟩ : syracuseStep 1331093 = 62395) (by norm_num)
theorem B970741 : Blo 523799 970741 := bbase (se 5 (by rfl) ⟨45503, by rfl⟩ : syracuseStep 970741 = 91007) (by norm_num)
theorem B1200197 : Blo 523799 1200197 := bbase (se 4 (by rfl) ⟨112518, by rfl⟩ : syracuseStep 1200197 = 225037) (by norm_num)
theorem B1462469 : Blo 523799 1462469 := bbase (se 4 (by rfl) ⟨137106, by rfl⟩ : syracuseStep 1462469 = 274213) (by norm_num)
theorem B2019541 : Blo 523799 2019541 := bbase (se 7 (by rfl) ⟨23666, by rfl⟩ : syracuseStep 2019541 = 47333) (by norm_num)
theorem B1626325 : Blo 523799 1626325 := bbase (se 7 (by rfl) ⟨19058, by rfl⟩ : syracuseStep 1626325 = 38117) (by norm_num)
theorem B1331437 : Blo 523799 1331437 := bbase (se 3 (by rfl) ⟨249644, by rfl⟩ : syracuseStep 1331437 = 499289) (by norm_num)
theorem B3985685 : Blo 523799 3985685 := bbase (se 6 (by rfl) ⟨93414, by rfl⟩ : syracuseStep 3985685 = 186829) (by norm_num)
theorem B840013 : Blo 523799 840013 := bbase (se 3 (by rfl) ⟨157502, by rfl⟩ : syracuseStep 840013 = 315005) (by norm_num)
theorem B1331549 : Blo 523799 1331549 := bbase (se 3 (by rfl) ⟨249665, by rfl⟩ : syracuseStep 1331549 = 499331) (by norm_num)
theorem B709021 : Blo 523799 709021 := bbase (se 3 (by rfl) ⟨132941, by rfl⟩ : syracuseStep 709021 = 265883) (by norm_num)
theorem B1266133 : Blo 523799 1266133 := bbase (se 7 (by rfl) ⟨14837, by rfl⟩ : syracuseStep 1266133 = 29675) (by norm_num)
theorem B1331741 : Blo 523799 1331741 := bbase (se 3 (by rfl) ⟨249701, by rfl⟩ : syracuseStep 1331741 = 499403) (by norm_num)
theorem B1069597 : Blo 523799 1069597 := bbase (se 3 (by rfl) ⟨200549, by rfl⟩ : syracuseStep 1069597 = 401099) (by norm_num)
theorem B3002933 : Blo 523799 3002933 := bbase (se 5 (by rfl) ⟨140762, by rfl⟩ : syracuseStep 3002933 = 281525) (by norm_num)
theorem B840469 : Blo 523799 840469 := bbase (se 6 (by rfl) ⟨19698, by rfl⟩ : syracuseStep 840469 = 39397) (by norm_num)
theorem B1332085 : Blo 523799 1332085 := bbase (se 5 (by rfl) ⟨62441, by rfl⟩ : syracuseStep 1332085 = 124883) (by norm_num)
theorem B1266653 : Blo 523799 1266653 := bbase (se 3 (by rfl) ⟨237497, by rfl⟩ : syracuseStep 1266653 = 474995) (by norm_num)
theorem B1332197 : Blo 523799 1332197 := bbase (se 4 (by rfl) ⟨124893, by rfl⟩ : syracuseStep 1332197 = 249787) (by norm_num)
theorem B1266749 : Blo 523799 1266749 := bbase (se 3 (by rfl) ⟨237515, by rfl⟩ : syracuseStep 1266749 = 475031) (by norm_num)
theorem B1332389 : Blo 523799 1332389 := bbase (se 4 (by rfl) ⟨124911, by rfl⟩ : syracuseStep 1332389 = 249823) (by norm_num)
theorem B808213 : Blo 523799 808213 := bbase (se 6 (by rfl) ⟨18942, by rfl⟩ : syracuseStep 808213 = 37885) (by norm_num)
theorem B841141 : Blo 523799 841141 := bbase (se 5 (by rfl) ⟨39428, by rfl⟩ : syracuseStep 841141 = 78857) (by norm_num)
theorem B1496501 : Blo 523799 1496501 := bbase (se 5 (by rfl) ⟨70148, by rfl⟩ : syracuseStep 1496501 = 140297) (by norm_num)
theorem B1332733 : Blo 523799 1332733 := bbase (se 3 (by rfl) ⟨249887, by rfl⟩ : syracuseStep 1332733 = 499775) (by norm_num)
theorem B1332845 : Blo 523799 1332845 := bbase (se 3 (by rfl) ⟨249908, by rfl⟩ : syracuseStep 1332845 = 499817) (by norm_num)
theorem B1333037 : Blo 523799 1333037 := bbase (se 3 (by rfl) ⟨249944, by rfl⟩ : syracuseStep 1333037 = 499889) (by norm_num)
theorem B1595189 : Blo 523799 1595189 := bbase (se 5 (by rfl) ⟨74774, by rfl⟩ : syracuseStep 1595189 = 149549) (by norm_num)
theorem B841565 : Blo 523799 841565 := bbase (se 3 (by rfl) ⟨157793, by rfl⟩ : syracuseStep 841565 = 315587) (by norm_num)
theorem B2250629 : Blo 523799 2250629 := bbase (se 4 (by rfl) ⟨210996, by rfl⟩ : syracuseStep 2250629 = 421993) (by norm_num)
theorem B841853 : Blo 523799 841853 := bbase (se 3 (by rfl) ⟨157847, by rfl⟩ : syracuseStep 841853 = 315695) (by norm_num)
theorem B1333381 : Blo 523799 1333381 := bbase (se 4 (by rfl) ⟨125004, by rfl⟩ : syracuseStep 1333381 = 250009) (by norm_num)
theorem B710837 : Blo 523799 710837 := bbase (se 5 (by rfl) ⟨33320, by rfl⟩ : syracuseStep 710837 = 66641) (by norm_num)
theorem B1333493 : Blo 523799 1333493 := bbase (se 5 (by rfl) ⟨62507, by rfl⟩ : syracuseStep 1333493 = 125015) (by norm_num)
theorem B1268093 : Blo 523799 1268093 := bbase (se 3 (by rfl) ⟨237767, by rfl⟩ : syracuseStep 1268093 = 475535) (by norm_num)
theorem B1333685 : Blo 523799 1333685 := bbase (se 5 (by rfl) ⟨62516, by rfl⟩ : syracuseStep 1333685 = 125033) (by norm_num)
theorem B711109 : Blo 523799 711109 := bbase (se 4 (by rfl) ⟨66666, by rfl⟩ : syracuseStep 711109 = 133333) (by norm_num)
theorem B1497685 : Blo 523799 1497685 := bbase (se 8 (by rfl) ⟨8775, by rfl⟩ : syracuseStep 1497685 = 17551) (by norm_num)
theorem B1497845 : Blo 523799 1497845 := bbase (se 5 (by rfl) ⟨70211, by rfl⟩ : syracuseStep 1497845 = 140423) (by norm_num)
theorem B1334029 : Blo 523799 1334029 := bbase (se 3 (by rfl) ⟨250130, by rfl⟩ : syracuseStep 1334029 = 500261) (by norm_num)
theorem B1334141 : Blo 523799 1334141 := bbase (se 3 (by rfl) ⟨250151, by rfl⟩ : syracuseStep 1334141 = 500303) (by norm_num)
theorem B842653 : Blo 523799 842653 := bbase (se 3 (by rfl) ⟨157997, by rfl⟩ : syracuseStep 842653 = 315995) (by norm_num)
theorem B1498085 : Blo 523799 1498085 := bbase (se 4 (by rfl) ⟨140445, by rfl⟩ : syracuseStep 1498085 = 280891) (by norm_num)
theorem B1334333 : Blo 523799 1334333 := bbase (se 3 (by rfl) ⟨250187, by rfl⟩ : syracuseStep 1334333 = 500375) (by norm_num)
theorem B973973 : Blo 523799 973973 := bbase (se 6 (by rfl) ⟨22827, by rfl⟩ : syracuseStep 973973 = 45655) (by norm_num)
theorem B1498277 : Blo 523799 1498277 := bbase (se 4 (by rfl) ⟨140463, by rfl⟩ : syracuseStep 1498277 = 280927) (by norm_num)
theorem B3792053 : Blo 523799 3792053 := bbase (se 5 (by rfl) ⟨177752, by rfl⟩ : syracuseStep 3792053 = 355505) (by norm_num)
theorem B4545877 : Blo 523799 4545877 := bbase (se 11 (by rfl) ⟨3329, by rfl⟩ : syracuseStep 4545877 = 6659) (by norm_num)
theorem B1334677 : Blo 523799 1334677 := bbase (se 6 (by rfl) ⟨31281, by rfl⟩ : syracuseStep 1334677 = 62563) (by norm_num)
theorem B843205 : Blo 523799 843205 := bbase (se 4 (by rfl) ⟨79050, by rfl⟩ : syracuseStep 843205 = 158101) (by norm_num)
theorem B1334789 : Blo 523799 1334789 := bbase (se 4 (by rfl) ⟨125136, by rfl⟩ : syracuseStep 1334789 = 250273) (by norm_num)
theorem B1990277 : Blo 523799 1990277 := bbase (se 4 (by rfl) ⟨186588, by rfl⟩ : syracuseStep 1990277 = 373177) (by norm_num)
theorem B843461 : Blo 523799 843461 := bbase (se 4 (by rfl) ⟨79074, by rfl⟩ : syracuseStep 843461 = 158149) (by norm_num)
theorem B1334981 : Blo 523799 1334981 := bbase (se 4 (by rfl) ⟨125154, by rfl⟩ : syracuseStep 1334981 = 250309) (by norm_num)
theorem B3366613 : Blo 523799 3366613 := bbase (se 7 (by rfl) ⟨39452, by rfl⟩ : syracuseStep 3366613 = 78905) (by norm_num)
theorem B1990565 : Blo 523799 1990565 := bbase (se 4 (by rfl) ⟨186615, by rfl⟩ : syracuseStep 1990565 = 373231) (by norm_num)
theorem B974845 : Blo 523799 974845 := bbase (se 3 (by rfl) ⟨182783, by rfl⟩ : syracuseStep 974845 = 365567) (by norm_num)
theorem B1335325 : Blo 523799 1335325 := bbase (se 3 (by rfl) ⟨250373, by rfl⟩ : syracuseStep 1335325 = 500747) (by norm_num)
theorem B1499269 : Blo 523799 1499269 := bbase (se 4 (by rfl) ⟨140556, by rfl⟩ : syracuseStep 1499269 = 281113) (by norm_num)
theorem B1335437 : Blo 523799 1335437 := bbase (se 3 (by rfl) ⟨250394, by rfl⟩ : syracuseStep 1335437 = 500789) (by norm_num)
theorem B1335629 : Blo 523799 1335629 := bbase (se 3 (by rfl) ⟨250430, by rfl⟩ : syracuseStep 1335629 = 500861) (by norm_num)
theorem B844165 : Blo 523799 844165 := bbase (se 4 (by rfl) ⟨79140, by rfl⟩ : syracuseStep 844165 = 158281) (by norm_num)
theorem B713173 : Blo 523799 713173 := bbase (se 7 (by rfl) ⟨8357, by rfl⟩ : syracuseStep 713173 = 16715) (by norm_num)
theorem B2843221 : Blo 523799 2843221 := bbase (se 8 (by rfl) ⟨16659, by rfl⟩ : syracuseStep 2843221 = 33319) (by norm_num)
theorem B1335973 : Blo 523799 1335973 := bbase (se 4 (by rfl) ⟨125247, by rfl⟩ : syracuseStep 1335973 = 250495) (by norm_num)
theorem B844589 : Blo 523799 844589 := bbase (se 3 (by rfl) ⟨158360, by rfl⟩ : syracuseStep 844589 = 316721) (by norm_num)
theorem B3793877 : Blo 523799 3793877 := bbase (se 7 (by rfl) ⟨44459, by rfl⟩ : syracuseStep 3793877 = 88919) (by norm_num)
theorem B615481 : Blo 523799 615481 := bbase (se 2 (by rfl) ⟨230805, by rfl⟩ : syracuseStep 615481 = 461611) (by norm_num)
theorem B1991749 : Blo 523799 1991749 := bbase (se 4 (by rfl) ⟨186726, by rfl⟩ : syracuseStep 1991749 = 373453) (by norm_num)
theorem B844877 : Blo 523799 844877 := bbase (se 3 (by rfl) ⟨158414, by rfl⟩ : syracuseStep 844877 = 316829) (by norm_num)
theorem B1533077 : Blo 523799 1533077 := bbase (se 6 (by rfl) ⟨35931, by rfl⟩ : syracuseStep 1533077 = 71863) (by norm_num)
theorem B1500373 : Blo 523799 1500373 := bbase (se 7 (by rfl) ⟨17582, by rfl⟩ : syracuseStep 1500373 = 35165) (by norm_num)
theorem B845101 : Blo 523799 845101 := bbase (se 3 (by rfl) ⟨158456, by rfl⟩ : syracuseStep 845101 = 316913) (by norm_num)
theorem B38495573 : Blo 523799 38495573 := bbase (se 12 (by rfl) ⟨14097, by rfl⟩ : syracuseStep 38495573 = 28195) (by norm_num)
theorem B1992053 : Blo 523799 1992053 := bbase (se 5 (by rfl) ⟨93377, by rfl⟩ : syracuseStep 1992053 = 186755) (by norm_num)
theorem B747157 : Blo 523799 747157 := bbase (se 6 (by rfl) ⟨17511, by rfl⟩ : syracuseStep 747157 = 35023) (by norm_num)
theorem B943949 : Blo 523799 943949 := bbase (se 3 (by rfl) ⟨176990, by rfl⟩ : syracuseStep 943949 = 353981) (by norm_num)
theorem B1009541 : Blo 523799 1009541 := bbase (se 4 (by rfl) ⟨94644, by rfl⟩ : syracuseStep 1009541 = 189289) (by norm_num)
theorem B747749 : Blo 523799 747749 := bbase (se 4 (by rfl) ⟨70101, by rfl⟩ : syracuseStep 747749 = 140203) (by norm_num)
theorem B747829 : Blo 523799 747829 := bbase (se 5 (by rfl) ⟨35054, by rfl⟩ : syracuseStep 747829 = 70109) (by norm_num)
theorem B747949 : Blo 523799 747949 := bbase (se 3 (by rfl) ⟨140240, by rfl⟩ : syracuseStep 747949 = 280481) (by norm_num)
theorem B748045 : Blo 523799 748045 := bbase (se 3 (by rfl) ⟨140258, by rfl⟩ : syracuseStep 748045 = 280517) (by norm_num)
theorem B944669 : Blo 523799 944669 := bbase (se 3 (by rfl) ⟨177125, by rfl⟩ : syracuseStep 944669 = 354251) (by norm_num)
theorem B1010341 : Blo 523799 1010341 := bbase (se 4 (by rfl) ⟨94719, by rfl⟩ : syracuseStep 1010341 = 189439) (by norm_num)
theorem B1501877 : Blo 523799 1501877 := bbase (se 5 (by rfl) ⟨70400, by rfl⟩ : syracuseStep 1501877 = 140801) (by norm_num)
theorem B2517733 : Blo 523799 2517733 := bbase (se 4 (by rfl) ⟨236037, by rfl⟩ : syracuseStep 2517733 = 472075) (by norm_num)
theorem B748541 : Blo 523799 748541 := bbase (se 3 (by rfl) ⟨140351, by rfl⟩ : syracuseStep 748541 = 280703) (by norm_num)
theorem B1895669 : Blo 523799 1895669 := bbase (se 5 (by rfl) ⟨88859, by rfl⟩ : syracuseStep 1895669 = 177719) (by norm_num)
theorem B3042613 : Blo 523799 3042613 := bbase (se 5 (by rfl) ⟨142622, by rfl⟩ : syracuseStep 3042613 = 285245) (by norm_num)
theorem B1994165 : Blo 523799 1994165 := bbase (se 5 (by rfl) ⟨93476, by rfl⟩ : syracuseStep 1994165 = 186953) (by norm_num)
theorem B749093 : Blo 523799 749093 := bbase (se 4 (by rfl) ⟨70227, by rfl⟩ : syracuseStep 749093 = 140455) (by norm_num)
theorem B1994453 : Blo 523799 1994453 := bbase (se 7 (by rfl) ⟨23372, by rfl⟩ : syracuseStep 1994453 = 46745) (by norm_num)
theorem B3993461 : Blo 523799 3993461 := bbase (se 5 (by rfl) ⟨187193, by rfl⟩ : syracuseStep 3993461 = 374387) (by norm_num)
theorem B749845 : Blo 523799 749845 := bbase (se 6 (by rfl) ⟨17574, by rfl⟩ : syracuseStep 749845 = 35149) (by norm_num)
theorem B5402933 : Blo 523799 5402933 := bbase (se 5 (by rfl) ⟨253262, by rfl⟩ : syracuseStep 5402933 = 506525) (by norm_num)
theorem B7565653 : Blo 523799 7565653 := bbase (se 10 (by rfl) ⟨11082, by rfl⟩ : syracuseStep 7565653 = 22165) (by norm_num)
theorem B1995637 : Blo 523799 1995637 := bbase (se 5 (by rfl) ⟨93545, by rfl⟩ : syracuseStep 1995637 = 187091) (by norm_num)
theorem B750637 : Blo 523799 750637 := bbase (se 3 (by rfl) ⟨140744, by rfl⟩ : syracuseStep 750637 = 281489) (by norm_num)
theorem B1995941 : Blo 523799 1995941 := bbase (se 4 (by rfl) ⟨187119, by rfl⟩ : syracuseStep 1995941 = 374239) (by norm_num)
theorem B4256981 : Blo 523799 4256981 := bbase (se 7 (by rfl) ⟨49886, by rfl⟩ : syracuseStep 4256981 = 99773) (by norm_num)
theorem B750973 : Blo 523799 750973 := bbase (se 3 (by rfl) ⟨140807, by rfl⟩ : syracuseStep 750973 = 281615) (by norm_num)
theorem B751189 : Blo 523799 751189 := bbase (se 8 (by rfl) ⟨4401, by rfl⟩ : syracuseStep 751189 = 8803) (by norm_num)
theorem B1603205 : Blo 523799 1603205 := bbase (se 4 (by rfl) ⟨150300, by rfl⟩ : syracuseStep 1603205 = 300601) (by norm_num)
theorem B685981 : Blo 523799 685981 := bbase (se 3 (by rfl) ⟨128621, by rfl⟩ : syracuseStep 685981 = 257243) (by norm_num)
theorem B1800101 : Blo 523799 1800101 := bbase (se 4 (by rfl) ⟨168759, by rfl⟩ : syracuseStep 1800101 = 337519) (by norm_num)
theorem B2652101 : Blo 523799 2652101 := bbase (se 4 (by rfl) ⟨248634, by rfl⟩ : syracuseStep 2652101 = 497269) (by norm_num)
theorem B1898437 : Blo 523799 1898437 := bbase (se 4 (by rfl) ⟨177978, by rfl⟩ : syracuseStep 1898437 = 355957) (by norm_num)
theorem B948181 : Blo 523799 948181 := bbase (se 7 (by rfl) ⟨11111, by rfl⟩ : syracuseStep 948181 = 22223) (by norm_num)
theorem B8550805 : Blo 523799 8550805 := bbase (se 6 (by rfl) ⟨200409, by rfl⟩ : syracuseStep 8550805 = 400819) (by norm_num)
theorem B948677 : Blo 523799 948677 := bbase (se 4 (by rfl) ⟨88938, by rfl⟩ : syracuseStep 948677 = 177877) (by norm_num)
theorem B1768229 : Blo 523799 1768229 := bbase (se 4 (by rfl) ⟨165771, by rfl⟩ : syracuseStep 1768229 = 331543) (by norm_num)
theorem B1801061 : Blo 523799 1801061 := bbase (se 4 (by rfl) ⟨168849, by rfl⟩ : syracuseStep 1801061 = 337699) (by norm_num)
theorem B1440661 : Blo 523799 1440661 := bbase (se 6 (by rfl) ⟨33765, by rfl⟩ : syracuseStep 1440661 = 67531) (by norm_num)
theorem B3373973 : Blo 523799 3373973 := bbase (se 6 (by rfl) ⟨79077, by rfl⟩ : syracuseStep 3373973 = 158155) (by norm_num)
theorem B1178549 : Blo 523799 1178549 := bbase (se 5 (by rfl) ⟨55244, by rfl⟩ : syracuseStep 1178549 = 110489) (by norm_num)
theorem B1178621 : Blo 523799 1178621 := bbase (se 3 (by rfl) ⟨220991, by rfl⟩ : syracuseStep 1178621 = 441983) (by norm_num)
theorem B2522117 : Blo 523799 2522117 := bbase (se 4 (by rfl) ⟨236448, by rfl⟩ : syracuseStep 2522117 = 472897) (by norm_num)
theorem B1178693 : Blo 523799 1178693 := bbase (se 4 (by rfl) ⟨110502, by rfl⟩ : syracuseStep 1178693 = 221005) (by norm_num)
theorem B1178765 : Blo 523799 1178765 := bbase (se 3 (by rfl) ⟨221018, by rfl⟩ : syracuseStep 1178765 = 442037) (by norm_num)
theorem B1178837 : Blo 523799 1178837 := bbase (se 7 (by rfl) ⟨13814, by rfl⟩ : syracuseStep 1178837 = 27629) (by norm_num)
theorem B1768661 : Blo 523799 1768661 := bbase (se 7 (by rfl) ⟨20726, by rfl⟩ : syracuseStep 1768661 = 41453) (by norm_num)
theorem B2653397 : Blo 523799 2653397 := bbase (se 7 (by rfl) ⟨31094, by rfl⟩ : syracuseStep 2653397 = 62189) (by norm_num)
theorem B1998053 : Blo 523799 1998053 := bbase (se 4 (by rfl) ⟨187317, by rfl⟩ : syracuseStep 1998053 = 374635) (by norm_num)
theorem B883973 : Blo 523799 883973 := bbase (se 4 (by rfl) ⟨82872, by rfl⟩ : syracuseStep 883973 = 165745) (by norm_num)
theorem B1178909 : Blo 523799 1178909 := bbase (se 3 (by rfl) ⟨221045, by rfl⟩ : syracuseStep 1178909 = 442091) (by norm_num)
theorem B785717 : Blo 523799 785717 := bbase (se 5 (by rfl) ⟨36830, by rfl⟩ : syracuseStep 785717 = 73661) (by norm_num)
theorem B949565 : Blo 523799 949565 := bbase (se 3 (by rfl) ⟨178043, by rfl⟩ : syracuseStep 949565 = 356087) (by norm_num)
theorem B785741 : Blo 523799 785741 := bbase (se 3 (by rfl) ⟨147326, by rfl⟩ : syracuseStep 785741 = 294653) (by norm_num)
theorem B785765 : Blo 523799 785765 := bbase (se 4 (by rfl) ⟨73665, by rfl⟩ : syracuseStep 785765 = 147331) (by norm_num)
theorem B1178981 : Blo 523799 1178981 := bbase (se 4 (by rfl) ⟨110529, by rfl⟩ : syracuseStep 1178981 = 221059) (by norm_num)
theorem B785789 : Blo 523799 785789 := bbase (se 3 (by rfl) ⟨147335, by rfl⟩ : syracuseStep 785789 = 294671) (by norm_num)
theorem B884101 : Blo 523799 884101 := bbase (se 4 (by rfl) ⟨82884, by rfl⟩ : syracuseStep 884101 = 165769) (by norm_num)
theorem B785813 : Blo 523799 785813 := bbase (se 6 (by rfl) ⟨18417, by rfl⟩ : syracuseStep 785813 = 36835) (by norm_num)
theorem B785837 : Blo 523799 785837 := bbase (se 3 (by rfl) ⟨147344, by rfl⟩ : syracuseStep 785837 = 294689) (by norm_num)
theorem B1179053 : Blo 523799 1179053 := bbase (se 3 (by rfl) ⟨221072, by rfl⟩ : syracuseStep 1179053 = 442145) (by norm_num)
theorem B785861 : Blo 523799 785861 := bbase (se 4 (by rfl) ⟨73674, by rfl⟩ : syracuseStep 785861 = 147349) (by norm_num)
theorem B785885 : Blo 523799 785885 := bbase (se 3 (by rfl) ⟨147353, by rfl⟩ : syracuseStep 785885 = 294707) (by norm_num)
theorem B884189 : Blo 523799 884189 := bbase (se 3 (by rfl) ⟨165785, by rfl⟩ : syracuseStep 884189 = 331571) (by norm_num)
theorem B589297 : Blo 523799 589297 := bbase (se 2 (by rfl) ⟨220986, by rfl⟩ : syracuseStep 589297 = 441973) (by norm_num)
theorem B785909 : Blo 523799 785909 := bbase (se 5 (by rfl) ⟨36839, by rfl⟩ : syracuseStep 785909 = 73679) (by norm_num)
theorem B1179125 : Blo 523799 1179125 := bbase (se 5 (by rfl) ⟨55271, by rfl⟩ : syracuseStep 1179125 = 110543) (by norm_num)
theorem B1998341 : Blo 523799 1998341 := bbase (se 4 (by rfl) ⟨187344, by rfl⟩ : syracuseStep 1998341 = 374689) (by norm_num)
theorem B785933 : Blo 523799 785933 := bbase (se 3 (by rfl) ⟨147362, by rfl⟩ : syracuseStep 785933 = 294725) (by norm_num)
theorem B589333 : Blo 523799 589333 := bbase (se 6 (by rfl) ⟨13812, by rfl⟩ : syracuseStep 589333 = 27625) (by norm_num)
theorem B4783637 : Blo 523799 4783637 := bbase (se 6 (by rfl) ⟨112116, by rfl⟩ : syracuseStep 4783637 = 224233) (by norm_num)
theorem B785957 : Blo 523799 785957 := bbase (se 4 (by rfl) ⟨73683, by rfl⟩ : syracuseStep 785957 = 147367) (by norm_num)
theorem B589369 : Blo 523799 589369 := bbase (se 2 (by rfl) ⟨221013, by rfl⟩ : syracuseStep 589369 = 442027) (by norm_num)
theorem B785981 : Blo 523799 785981 := bbase (se 3 (by rfl) ⟨147371, by rfl⟩ : syracuseStep 785981 = 294743) (by norm_num)
theorem B1179197 : Blo 523799 1179197 := bbase (se 3 (by rfl) ⟨221099, by rfl⟩ : syracuseStep 1179197 = 442199) (by norm_num)
theorem B786005 : Blo 523799 786005 := bbase (se 8 (by rfl) ⟨4605, by rfl⟩ : syracuseStep 786005 = 9211) (by norm_num)
theorem B949853 : Blo 523799 949853 := bbase (se 3 (by rfl) ⟨178097, by rfl⟩ : syracuseStep 949853 = 356195) (by norm_num)
theorem B589405 : Blo 523799 589405 := bbase (se 3 (by rfl) ⟨110513, by rfl⟩ : syracuseStep 589405 = 221027) (by norm_num)
theorem B884317 : Blo 523799 884317 := bbase (se 3 (by rfl) ⟨165809, by rfl⟩ : syracuseStep 884317 = 331619) (by norm_num)
theorem B786029 : Blo 523799 786029 := bbase (se 3 (by rfl) ⟨147380, by rfl⟩ : syracuseStep 786029 = 294761) (by norm_num)
theorem B589441 : Blo 523799 589441 := bbase (se 2 (by rfl) ⟨221040, by rfl⟩ : syracuseStep 589441 = 442081) (by norm_num)
theorem B786053 : Blo 523799 786053 := bbase (se 4 (by rfl) ⟨73692, by rfl⟩ : syracuseStep 786053 = 147385) (by norm_num)
theorem B1179269 : Blo 523799 1179269 := bbase (se 4 (by rfl) ⟨110556, by rfl⟩ : syracuseStep 1179269 = 221113) (by norm_num)
theorem B1769093 : Blo 523799 1769093 := bbase (se 4 (by rfl) ⟨165852, by rfl⟩ : syracuseStep 1769093 = 331705) (by norm_num)
theorem B786077 : Blo 523799 786077 := bbase (se 3 (by rfl) ⟨147389, by rfl⟩ : syracuseStep 786077 = 294779) (by norm_num)
theorem B589477 : Blo 523799 589477 := bbase (se 4 (by rfl) ⟨55263, by rfl⟩ : syracuseStep 589477 = 110527) (by norm_num)
theorem B786101 : Blo 523799 786101 := bbase (se 5 (by rfl) ⟨36848, by rfl⟩ : syracuseStep 786101 = 73697) (by norm_num)
theorem B884405 : Blo 523799 884405 := bbase (se 5 (by rfl) ⟨41456, by rfl⟩ : syracuseStep 884405 = 82913) (by norm_num)
theorem B589513 : Blo 523799 589513 := bbase (se 2 (by rfl) ⟨221067, by rfl⟩ : syracuseStep 589513 = 442135) (by norm_num)
theorem B786125 : Blo 523799 786125 := bbase (se 3 (by rfl) ⟨147398, by rfl⟩ : syracuseStep 786125 = 294797) (by norm_num)
theorem B1179341 : Blo 523799 1179341 := bbase (se 3 (by rfl) ⟨221126, by rfl⟩ : syracuseStep 1179341 = 442253) (by norm_num)
theorem B851677 : Blo 523799 851677 := bbase (se 3 (by rfl) ⟨159689, by rfl⟩ : syracuseStep 851677 = 319379) (by norm_num)
theorem B786149 : Blo 523799 786149 := bbase (se 4 (by rfl) ⟨73701, by rfl⟩ : syracuseStep 786149 = 147403) (by norm_num)
theorem B2391781 : Blo 523799 2391781 := bbase (se 4 (by rfl) ⟨224229, by rfl⟩ : syracuseStep 2391781 = 448459) (by norm_num)
theorem B589549 : Blo 523799 589549 := bbase (se 3 (by rfl) ⟨110540, by rfl⟩ : syracuseStep 589549 = 221081) (by norm_num)
theorem B786173 : Blo 523799 786173 := bbase (se 3 (by rfl) ⟨147407, by rfl⟩ : syracuseStep 786173 = 294815) (by norm_num)
theorem B589585 : Blo 523799 589585 := bbase (se 2 (by rfl) ⟨221094, by rfl⟩ : syracuseStep 589585 = 442189) (by norm_num)
theorem B786197 : Blo 523799 786197 := bbase (se 6 (by rfl) ⟨18426, by rfl⟩ : syracuseStep 786197 = 36853) (by norm_num)
theorem B1179413 : Blo 523799 1179413 := bbase (se 6 (by rfl) ⟨27642, by rfl⟩ : syracuseStep 1179413 = 55285) (by norm_num)
theorem B786221 : Blo 523799 786221 := bbase (se 3 (by rfl) ⟨147416, by rfl⟩ : syracuseStep 786221 = 294833) (by norm_num)
theorem B589621 : Blo 523799 589621 := bbase (se 5 (by rfl) ⟨27638, by rfl⟩ : syracuseStep 589621 = 55277) (by norm_num)
theorem B884533 : Blo 523799 884533 := bbase (se 5 (by rfl) ⟨41462, by rfl⟩ : syracuseStep 884533 = 82925) (by norm_num)
theorem B786245 : Blo 523799 786245 := bbase (se 4 (by rfl) ⟨73710, by rfl⟩ : syracuseStep 786245 = 147421) (by norm_num)
theorem B589657 : Blo 523799 589657 := bbase (se 2 (by rfl) ⟨221121, by rfl⟩ : syracuseStep 589657 = 442243) (by norm_num)
theorem B786269 : Blo 523799 786269 := bbase (se 3 (by rfl) ⟨147425, by rfl⟩ : syracuseStep 786269 = 294851) (by norm_num)
theorem B1179485 : Blo 523799 1179485 := bbase (se 3 (by rfl) ⟨221153, by rfl⟩ : syracuseStep 1179485 = 442307) (by norm_num)
theorem B786293 : Blo 523799 786293 := bbase (se 5 (by rfl) ⟨36857, by rfl⟩ : syracuseStep 786293 = 73715) (by norm_num)
theorem B589693 : Blo 523799 589693 := bbase (se 3 (by rfl) ⟨110567, by rfl⟩ : syracuseStep 589693 = 221135) (by norm_num)
theorem B786317 : Blo 523799 786317 := bbase (se 3 (by rfl) ⟨147434, by rfl⟩ : syracuseStep 786317 = 294869) (by norm_num)
theorem B884621 : Blo 523799 884621 := bbase (se 3 (by rfl) ⟨165866, by rfl⟩ : syracuseStep 884621 = 331733) (by norm_num)
theorem B589729 : Blo 523799 589729 := bbase (se 2 (by rfl) ⟨221148, by rfl⟩ : syracuseStep 589729 = 442297) (by norm_num)
theorem B786341 : Blo 523799 786341 := bbase (se 4 (by rfl) ⟨73719, by rfl⟩ : syracuseStep 786341 = 147439) (by norm_num)
theorem B1179557 : Blo 523799 1179557 := bbase (se 4 (by rfl) ⟨110583, by rfl⟩ : syracuseStep 1179557 = 221167) (by norm_num)
theorem B786365 : Blo 523799 786365 := bbase (se 3 (by rfl) ⟨147443, by rfl⟩ : syracuseStep 786365 = 294887) (by norm_num)
theorem B589765 : Blo 523799 589765 := bbase (se 4 (by rfl) ⟨55290, by rfl⟩ : syracuseStep 589765 = 110581) (by norm_num)
theorem B786389 : Blo 523799 786389 := bbase (se 7 (by rfl) ⟨9215, by rfl⟩ : syracuseStep 786389 = 18431) (by norm_num)
theorem B5046229 : Blo 523799 5046229 := bbase (se 7 (by rfl) ⟨59135, by rfl⟩ : syracuseStep 5046229 = 118271) (by norm_num)
theorem B589801 : Blo 523799 589801 := bbase (se 2 (by rfl) ⟨221175, by rfl⟩ : syracuseStep 589801 = 442351) (by norm_num)
theorem B786413 : Blo 523799 786413 := bbase (se 3 (by rfl) ⟨147452, by rfl⟩ : syracuseStep 786413 = 294905) (by norm_num)
theorem B1179629 : Blo 523799 1179629 := bbase (se 3 (by rfl) ⟨221180, by rfl⟩ : syracuseStep 1179629 = 442361) (by norm_num)
theorem B524291 : Blo 523799 524291 := bstep (se 1 (by rfl) ⟨393218, by rfl⟩ : syracuseStep 524291 = 786437) B786437
theorem B1179665 : Blo 523799 1179665 := bstep (se 2 (by rfl) ⟨442374, by rfl⟩ : syracuseStep 1179665 = 884749) B884749
theorem B786449 : Blo 523799 786449 := bstep (se 2 (by rfl) ⟨294918, by rfl⟩ : syracuseStep 786449 = 589837) B589837
theorem B524307 : Blo 523799 524307 := bstep (se 1 (by rfl) ⟨393230, by rfl⟩ : syracuseStep 524307 = 786461) B786461
theorem B1179683 : Blo 523799 1179683 := bstep (se 1 (by rfl) ⟨884762, by rfl⟩ : syracuseStep 1179683 = 1769525) B1769525
theorem B786467 : Blo 523799 786467 := bstep (se 1 (by rfl) ⟨589850, by rfl⟩ : syracuseStep 786467 = 1179701) B1179701
theorem B524323 : Blo 523799 524323 := bstep (se 1 (by rfl) ⟨393242, by rfl⟩ : syracuseStep 524323 = 786485) B786485
theorem B524339 : Blo 523799 524339 := bstep (se 1 (by rfl) ⟨393254, by rfl⟩ : syracuseStep 524339 = 786509) B786509
theorem B786497 : Blo 523799 786497 := bstep (se 2 (by rfl) ⟨294936, by rfl⟩ : syracuseStep 786497 = 589873) B589873
theorem B884803 : Blo 523799 884803 := bstep (se 1 (by rfl) ⟨663602, by rfl⟩ : syracuseStep 884803 = 1327205) B1327205
theorem B589891 : Blo 523799 589891 := bstep (se 1 (by rfl) ⟨442418, by rfl⟩ : syracuseStep 589891 = 884837) B884837
theorem B524355 : Blo 523799 524355 := bstep (se 1 (by rfl) ⟨393266, by rfl⟩ : syracuseStep 524355 = 786533) B786533
theorem B1802321 : Blo 523799 1802321 := bstep (se 2 (by rfl) ⟨675870, by rfl⟩ : syracuseStep 1802321 = 1351741) B1351741
theorem B786515 : Blo 523799 786515 := bstep (se 1 (by rfl) ⟨589886, by rfl⟩ : syracuseStep 786515 = 1179773) B1179773
theorem B524371 : Blo 523799 524371 := bstep (se 1 (by rfl) ⟨393278, by rfl⟩ : syracuseStep 524371 = 786557) B786557
theorem B524387 : Blo 523799 524387 := bstep (se 1 (by rfl) ⟨393290, by rfl⟩ : syracuseStep 524387 = 786581) B786581
theorem B786545 : Blo 523799 786545 := bstep (se 2 (by rfl) ⟨294954, by rfl⟩ : syracuseStep 786545 = 589909) B589909
theorem B524403 : Blo 523799 524403 := bstep (se 1 (by rfl) ⟨393302, by rfl⟩ : syracuseStep 524403 = 786605) B786605
theorem B786563 : Blo 523799 786563 := bstep (se 1 (by rfl) ⟨589922, by rfl⟩ : syracuseStep 786563 = 1179845) B1179845
theorem B524419 : Blo 523799 524419 := bstep (se 1 (by rfl) ⟨393314, by rfl⟩ : syracuseStep 524419 = 786629) B786629
theorem B524435 : Blo 523799 524435 := bstep (se 1 (by rfl) ⟨393326, by rfl⟩ : syracuseStep 524435 = 786653) B786653
theorem B786593 : Blo 523799 786593 := bstep (se 2 (by rfl) ⟨294972, by rfl⟩ : syracuseStep 786593 = 589945) B589945
theorem B524451 : Blo 523799 524451 := bstep (se 1 (by rfl) ⟨393338, by rfl⟩ : syracuseStep 524451 = 786677) B786677
theorem B1999025 : Blo 523799 1999025 := bstep (se 2 (by rfl) ⟨749634, by rfl⟩ : syracuseStep 1999025 = 1499269) B1499269
theorem B786611 : Blo 523799 786611 := bstep (se 1 (by rfl) ⟨589958, by rfl⟩ : syracuseStep 786611 = 1179917) B1179917
theorem B524467 : Blo 523799 524467 := bstep (se 1 (by rfl) ⟨393350, by rfl⟩ : syracuseStep 524467 = 786701) B786701
theorem B524483 : Blo 523799 524483 := bstep (se 1 (by rfl) ⟨393362, by rfl⟩ : syracuseStep 524483 = 786725) B786725
theorem B884945 : Blo 523799 884945 := bstep (se 2 (by rfl) ⟨331854, by rfl⟩ : syracuseStep 884945 = 663709) B663709
theorem B786641 : Blo 523799 786641 := bstep (se 2 (by rfl) ⟨294990, by rfl⟩ : syracuseStep 786641 = 589981) B589981
theorem B590035 : Blo 523799 590035 := bstep (se 1 (by rfl) ⟨442526, by rfl⟩ : syracuseStep 590035 = 885053) B885053
theorem B524499 : Blo 523799 524499 := bstep (se 1 (by rfl) ⟨393374, by rfl⟩ : syracuseStep 524499 = 786749) B786749
theorem B786659 : Blo 523799 786659 := bstep (se 1 (by rfl) ⟨589994, by rfl⟩ : syracuseStep 786659 = 1179989) B1179989
theorem B524515 : Blo 523799 524515 := bstep (se 1 (by rfl) ⟨393386, by rfl⟩ : syracuseStep 524515 = 786773) B786773
theorem B6750449 : Blo 523799 6750449 := bstep (se 2 (by rfl) ⟨2531418, by rfl⟩ : syracuseStep 6750449 = 5062837) B5062837
theorem B524531 : Blo 523799 524531 := bstep (se 1 (by rfl) ⟨393398, by rfl⟩ : syracuseStep 524531 = 786797) B786797
theorem B786689 : Blo 523799 786689 := bstep (se 2 (by rfl) ⟨295008, by rfl⟩ : syracuseStep 786689 = 590017) B590017
theorem B524547 : Blo 523799 524547 := bstep (se 1 (by rfl) ⟨393410, by rfl⟩ : syracuseStep 524547 = 786821) B786821
theorem B1769741 : Blo 523799 1769741 := bstep (se 3 (by rfl) ⟨331826, by rfl⟩ : syracuseStep 1769741 = 663653) B663653
theorem B786707 : Blo 523799 786707 := bstep (se 1 (by rfl) ⟨590030, by rfl⟩ : syracuseStep 786707 = 1180061) B1180061
theorem B524563 : Blo 523799 524563 := bstep (se 1 (by rfl) ⟨393422, by rfl⟩ : syracuseStep 524563 = 786845) B786845
theorem B524579 : Blo 523799 524579 := bstep (se 1 (by rfl) ⟨393434, by rfl⟩ : syracuseStep 524579 = 786869) B786869
theorem B1179953 : Blo 523799 1179953 := bstep (se 2 (by rfl) ⟨442482, by rfl⟩ : syracuseStep 1179953 = 884965) B884965
theorem B786737 : Blo 523799 786737 := bstep (se 2 (by rfl) ⟨295026, by rfl⟩ : syracuseStep 786737 = 590053) B590053
theorem B524595 : Blo 523799 524595 := bstep (se 1 (by rfl) ⟨393446, by rfl⟩ : syracuseStep 524595 = 786893) B786893
theorem B1769795 : Blo 523799 1769795 := bstep (se 1 (by rfl) ⟨1327346, by rfl⟩ : syracuseStep 1769795 = 2654693) B2654693
theorem B1179971 : Blo 523799 1179971 := bstep (se 1 (by rfl) ⟨884978, by rfl⟩ : syracuseStep 1179971 = 1769957) B1769957
theorem B786755 : Blo 523799 786755 := bstep (se 1 (by rfl) ⟨590066, by rfl⟩ : syracuseStep 786755 = 1180133) B1180133
theorem B524611 : Blo 523799 524611 := bstep (se 1 (by rfl) ⟨393458, by rfl⟩ : syracuseStep 524611 = 786917) B786917
theorem B885073 : Blo 523799 885073 := bstep (se 2 (by rfl) ⟨331902, by rfl⟩ : syracuseStep 885073 = 663805) B663805
theorem B524627 : Blo 523799 524627 := bstep (se 1 (by rfl) ⟨393470, by rfl⟩ : syracuseStep 524627 = 786941) B786941
theorem B786785 : Blo 523799 786785 := bstep (se 2 (by rfl) ⟨295044, by rfl⟩ : syracuseStep 786785 = 590089) B590089
theorem B590179 : Blo 523799 590179 := bstep (se 1 (by rfl) ⟨442634, by rfl⟩ : syracuseStep 590179 = 885269) B885269
theorem B524643 : Blo 523799 524643 := bstep (se 1 (by rfl) ⟨393482, by rfl⟩ : syracuseStep 524643 = 786965) B786965
theorem B885107 : Blo 523799 885107 := bstep (se 1 (by rfl) ⟨663830, by rfl⟩ : syracuseStep 885107 = 1327661) B1327661
theorem B786803 : Blo 523799 786803 := bstep (se 1 (by rfl) ⟨590102, by rfl⟩ : syracuseStep 786803 = 1180205) B1180205
theorem B524659 : Blo 523799 524659 := bstep (se 1 (by rfl) ⟨393494, by rfl⟩ : syracuseStep 524659 = 786989) B786989
theorem B524675 : Blo 523799 524675 := bstep (se 1 (by rfl) ⟨393506, by rfl⟩ : syracuseStep 524675 = 787013) B787013
theorem B3801485 : Blo 523799 3801485 := bstep (se 3 (by rfl) ⟨712778, by rfl⟩ : syracuseStep 3801485 = 1425557) B1425557
theorem B786833 : Blo 523799 786833 := bstep (se 2 (by rfl) ⟨295062, by rfl⟩ : syracuseStep 786833 = 590125) B590125
theorem B524691 : Blo 523799 524691 := bstep (se 1 (by rfl) ⟨393518, by rfl⟩ : syracuseStep 524691 = 787037) B787037
theorem B786851 : Blo 523799 786851 := bstep (se 1 (by rfl) ⟨590138, by rfl⟩ : syracuseStep 786851 = 1180277) B1180277
theorem B524707 : Blo 523799 524707 := bstep (se 1 (by rfl) ⟨393530, by rfl⟩ : syracuseStep 524707 = 787061) B787061
theorem B524723 : Blo 523799 524723 := bstep (se 1 (by rfl) ⟨393542, by rfl⟩ : syracuseStep 524723 = 787085) B787085
theorem B786881 : Blo 523799 786881 := bstep (se 2 (by rfl) ⟨295080, by rfl⟩ : syracuseStep 786881 = 590161) B590161
theorem B524739 : Blo 523799 524739 := bstep (se 1 (by rfl) ⟨393554, by rfl⟩ : syracuseStep 524739 = 787109) B787109
theorem B786899 : Blo 523799 786899 := bstep (se 1 (by rfl) ⟨590174, by rfl⟩ : syracuseStep 786899 = 1180349) B1180349
theorem B524755 : Blo 523799 524755 := bstep (se 1 (by rfl) ⟨393566, by rfl⟩ : syracuseStep 524755 = 787133) B787133
theorem B524771 : Blo 523799 524771 := bstep (se 1 (by rfl) ⟨393578, by rfl⟩ : syracuseStep 524771 = 787157) B787157
theorem B786929 : Blo 523799 786929 := bstep (se 2 (by rfl) ⟨295098, by rfl⟩ : syracuseStep 786929 = 590197) B590197
theorem B885235 : Blo 523799 885235 := bstep (se 1 (by rfl) ⟨663926, by rfl⟩ : syracuseStep 885235 = 1327853) B1327853
theorem B590323 : Blo 523799 590323 := bstep (se 1 (by rfl) ⟨442742, by rfl⟩ : syracuseStep 590323 = 885485) B885485
theorem B524787 : Blo 523799 524787 := bstep (se 1 (by rfl) ⟨393590, by rfl⟩ : syracuseStep 524787 = 787181) B787181
theorem B786947 : Blo 523799 786947 := bstep (se 1 (by rfl) ⟨590210, by rfl⟩ : syracuseStep 786947 = 1180421) B1180421
theorem B524803 : Blo 523799 524803 := bstep (se 1 (by rfl) ⟨393602, by rfl⟩ : syracuseStep 524803 = 787205) B787205
theorem B3899917 : Blo 523799 3899917 := bstep (se 3 (by rfl) ⟨731234, by rfl⟩ : syracuseStep 3899917 = 1462469) B1462469
theorem B524819 : Blo 523799 524819 := bstep (se 1 (by rfl) ⟨393614, by rfl⟩ : syracuseStep 524819 = 787229) B787229
theorem B786977 : Blo 523799 786977 := bstep (se 2 (by rfl) ⟨295116, by rfl⟩ : syracuseStep 786977 = 590233) B590233
theorem B524835 : Blo 523799 524835 := bstep (se 1 (by rfl) ⟨393626, by rfl⟩ : syracuseStep 524835 = 787253) B787253
theorem B786995 : Blo 523799 786995 := bstep (se 1 (by rfl) ⟨590246, by rfl⟩ : syracuseStep 786995 = 1180493) B1180493
theorem B524851 : Blo 523799 524851 := bstep (se 1 (by rfl) ⟨393638, by rfl⟩ : syracuseStep 524851 = 787277) B787277
theorem B524867 : Blo 523799 524867 := bstep (se 1 (by rfl) ⟨393650, by rfl⟩ : syracuseStep 524867 = 787301) B787301
theorem B1770065 : Blo 523799 1770065 := bstep (se 2 (by rfl) ⟨663774, by rfl⟩ : syracuseStep 1770065 = 1327549) B1327549
theorem B1180241 : Blo 523799 1180241 := bstep (se 2 (by rfl) ⟨442590, by rfl⟩ : syracuseStep 1180241 = 885181) B885181
theorem B787025 : Blo 523799 787025 := bstep (se 2 (by rfl) ⟨295134, by rfl⟩ : syracuseStep 787025 = 590269) B590269
theorem B524883 : Blo 523799 524883 := bstep (se 1 (by rfl) ⟨393662, by rfl⟩ : syracuseStep 524883 = 787325) B787325
theorem B1180259 : Blo 523799 1180259 := bstep (se 1 (by rfl) ⟨885194, by rfl⟩ : syracuseStep 1180259 = 1770389) B1770389
theorem B787043 : Blo 523799 787043 := bstep (se 1 (by rfl) ⟨590282, by rfl⟩ : syracuseStep 787043 = 1180565) B1180565
theorem B524899 : Blo 523799 524899 := bstep (se 1 (by rfl) ⟨393674, by rfl⟩ : syracuseStep 524899 = 787349) B787349
theorem B3998321 : Blo 523799 3998321 := bstep (se 2 (by rfl) ⟨1499370, by rfl⟩ : syracuseStep 3998321 = 2998741) B2998741
theorem B524915 : Blo 523799 524915 := bstep (se 1 (by rfl) ⟨393686, by rfl⟩ : syracuseStep 524915 = 787373) B787373
theorem B950897 : Blo 523799 950897 := bstep (se 2 (by rfl) ⟨356586, by rfl⟩ : syracuseStep 950897 = 713173) B713173
theorem B885377 : Blo 523799 885377 := bstep (se 2 (by rfl) ⟨332016, by rfl⟩ : syracuseStep 885377 = 664033) B664033
theorem B787073 : Blo 523799 787073 := bstep (se 2 (by rfl) ⟨295152, by rfl⟩ : syracuseStep 787073 = 590305) B590305
theorem B590467 : Blo 523799 590467 := bstep (se 1 (by rfl) ⟨442850, by rfl⟩ : syracuseStep 590467 = 885701) B885701
theorem B524931 : Blo 523799 524931 := bstep (se 1 (by rfl) ⟨393698, by rfl⟩ : syracuseStep 524931 = 787397) B787397
theorem B787091 : Blo 523799 787091 := bstep (se 1 (by rfl) ⟨590318, by rfl⟩ : syracuseStep 787091 = 1180637) B1180637
theorem B524947 : Blo 523799 524947 := bstep (se 1 (by rfl) ⟨393710, by rfl⟩ : syracuseStep 524947 = 787421) B787421
theorem B1704611 : Blo 523799 1704611 := bstep (se 1 (by rfl) ⟨1278458, by rfl⟩ : syracuseStep 1704611 = 2556917) B2556917
theorem B524963 : Blo 523799 524963 := bstep (se 1 (by rfl) ⟨393722, by rfl⟩ : syracuseStep 524963 = 787445) B787445
theorem B787121 : Blo 523799 787121 := bstep (se 2 (by rfl) ⟨295170, by rfl⟩ : syracuseStep 787121 = 590341) B590341
theorem B524979 : Blo 523799 524979 := bstep (se 1 (by rfl) ⟨393734, by rfl⟩ : syracuseStep 524979 = 787469) B787469
theorem B787139 : Blo 523799 787139 := bstep (se 1 (by rfl) ⟨590354, by rfl⟩ : syracuseStep 787139 = 1180709) B1180709
theorem B524995 : Blo 523799 524995 := bstep (se 1 (by rfl) ⟨393746, by rfl⟩ : syracuseStep 524995 = 787493) B787493
theorem B525011 : Blo 523799 525011 := bstep (se 1 (by rfl) ⟨393758, by rfl⟩ : syracuseStep 525011 = 787517) B787517
theorem B787169 : Blo 523799 787169 := bstep (se 2 (by rfl) ⟨295188, by rfl⟩ : syracuseStep 787169 = 590377) B590377
theorem B525027 : Blo 523799 525027 := bstep (se 1 (by rfl) ⟨393770, by rfl⟩ : syracuseStep 525027 = 787541) B787541
theorem B787187 : Blo 523799 787187 := bstep (se 1 (by rfl) ⟨590390, by rfl⟩ : syracuseStep 787187 = 1180781) B1180781
theorem B525043 : Blo 523799 525043 := bstep (se 1 (by rfl) ⟨393782, by rfl⟩ : syracuseStep 525043 = 787565) B787565
theorem B885505 : Blo 523799 885505 := bstep (se 2 (by rfl) ⟨332064, by rfl⟩ : syracuseStep 885505 = 664129) B664129
theorem B525059 : Blo 523799 525059 := bstep (se 1 (by rfl) ⟨393794, by rfl⟩ : syracuseStep 525059 = 787589) B787589
theorem B787217 : Blo 523799 787217 := bstep (se 2 (by rfl) ⟨295206, by rfl⟩ : syracuseStep 787217 = 590413) B590413
theorem B590611 : Blo 523799 590611 := bstep (se 1 (by rfl) ⟨442958, by rfl⟩ : syracuseStep 590611 = 885917) B885917
theorem B525075 : Blo 523799 525075 := bstep (se 1 (by rfl) ⟨393806, by rfl⟩ : syracuseStep 525075 = 787613) B787613
theorem B2589475 : Blo 523799 2589475 := bstep (se 1 (by rfl) ⟨1942106, by rfl⟩ : syracuseStep 2589475 = 3884213) B3884213
theorem B885539 : Blo 523799 885539 := bstep (se 1 (by rfl) ⟨664154, by rfl⟩ : syracuseStep 885539 = 1328309) B1328309
theorem B787235 : Blo 523799 787235 := bstep (se 1 (by rfl) ⟨590426, by rfl⟩ : syracuseStep 787235 = 1180853) B1180853
theorem B525091 : Blo 523799 525091 := bstep (se 1 (by rfl) ⟨393818, by rfl⟩ : syracuseStep 525091 = 787637) B787637
theorem B525107 : Blo 523799 525107 := bstep (se 1 (by rfl) ⟨393830, by rfl⟩ : syracuseStep 525107 = 787661) B787661
theorem B787265 : Blo 523799 787265 := bstep (se 2 (by rfl) ⟨295224, by rfl⟩ : syracuseStep 787265 = 590449) B590449
theorem B525123 : Blo 523799 525123 := bstep (se 1 (by rfl) ⟨393842, by rfl⟩ : syracuseStep 525123 = 787685) B787685
theorem B787283 : Blo 523799 787283 := bstep (se 1 (by rfl) ⟨590462, by rfl⟩ : syracuseStep 787283 = 1180925) B1180925
theorem B525139 : Blo 523799 525139 := bstep (se 1 (by rfl) ⟨393854, by rfl⟩ : syracuseStep 525139 = 787709) B787709
theorem B525155 : Blo 523799 525155 := bstep (se 1 (by rfl) ⟨393866, by rfl⟩ : syracuseStep 525155 = 787733) B787733
theorem B1180529 : Blo 523799 1180529 := bstep (se 2 (by rfl) ⟨442698, by rfl⟩ : syracuseStep 1180529 = 885397) B885397
theorem B787313 : Blo 523799 787313 := bstep (se 2 (by rfl) ⟨295242, by rfl⟩ : syracuseStep 787313 = 590485) B590485
theorem B525171 : Blo 523799 525171 := bstep (se 1 (by rfl) ⟨393878, by rfl⟩ : syracuseStep 525171 = 787757) B787757
theorem B1180547 : Blo 523799 1180547 := bstep (se 1 (by rfl) ⟨885410, by rfl⟩ : syracuseStep 1180547 = 1770821) B1770821
theorem B787331 : Blo 523799 787331 := bstep (se 1 (by rfl) ⟨590498, by rfl⟩ : syracuseStep 787331 = 1180997) B1180997
theorem B525187 : Blo 523799 525187 := bstep (se 1 (by rfl) ⟨393890, by rfl⟩ : syracuseStep 525187 = 787781) B787781
theorem B525203 : Blo 523799 525203 := bstep (se 1 (by rfl) ⟨393902, by rfl⟩ : syracuseStep 525203 = 787805) B787805
theorem B787361 : Blo 523799 787361 := bstep (se 2 (by rfl) ⟨295260, by rfl⟩ : syracuseStep 787361 = 590521) B590521
theorem B885667 : Blo 523799 885667 := bstep (se 1 (by rfl) ⟨664250, by rfl⟩ : syracuseStep 885667 = 1328501) B1328501
theorem B590755 : Blo 523799 590755 := bstep (se 1 (by rfl) ⟨443066, by rfl⟩ : syracuseStep 590755 = 886133) B886133
theorem B525219 : Blo 523799 525219 := bstep (se 1 (by rfl) ⟨393914, by rfl⟩ : syracuseStep 525219 = 787829) B787829
theorem B787379 : Blo 523799 787379 := bstep (se 1 (by rfl) ⟨590534, by rfl⟩ : syracuseStep 787379 = 1181069) B1181069
theorem B525235 : Blo 523799 525235 := bstep (se 1 (by rfl) ⟨393926, by rfl⟩ : syracuseStep 525235 = 787853) B787853
theorem B525251 : Blo 523799 525251 := bstep (se 1 (by rfl) ⟨393938, by rfl⟩ : syracuseStep 525251 = 787877) B787877
theorem B787409 : Blo 523799 787409 := bstep (se 2 (by rfl) ⟨295278, by rfl⟩ : syracuseStep 787409 = 590557) B590557
theorem B525267 : Blo 523799 525267 := bstep (se 1 (by rfl) ⟨393950, by rfl⟩ : syracuseStep 525267 = 787901) B787901
theorem B787427 : Blo 523799 787427 := bstep (se 1 (by rfl) ⟨590570, by rfl⟩ : syracuseStep 787427 = 1181141) B1181141
theorem B525283 : Blo 523799 525283 := bstep (se 1 (by rfl) ⟨393962, by rfl⟩ : syracuseStep 525283 = 787925) B787925
theorem B525299 : Blo 523799 525299 := bstep (se 1 (by rfl) ⟨393974, by rfl⟩ : syracuseStep 525299 = 787949) B787949
theorem B787457 : Blo 523799 787457 := bstep (se 2 (by rfl) ⟨295296, by rfl⟩ : syracuseStep 787457 = 590593) B590593
theorem B525315 : Blo 523799 525315 := bstep (se 1 (by rfl) ⟨393986, by rfl⟩ : syracuseStep 525315 = 787973) B787973
theorem B787475 : Blo 523799 787475 := bstep (se 1 (by rfl) ⟨590606, by rfl⟩ : syracuseStep 787475 = 1181213) B1181213
theorem B525331 : Blo 523799 525331 := bstep (se 1 (by rfl) ⟨393998, by rfl⟩ : syracuseStep 525331 = 787997) B787997
theorem B525347 : Blo 523799 525347 := bstep (se 1 (by rfl) ⟨394010, by rfl⟩ : syracuseStep 525347 = 788021) B788021
theorem B885809 : Blo 523799 885809 := bstep (se 2 (by rfl) ⟨332178, by rfl⟩ : syracuseStep 885809 = 664357) B664357
theorem B787505 : Blo 523799 787505 := bstep (se 2 (by rfl) ⟨295314, by rfl⟩ : syracuseStep 787505 = 590629) B590629
theorem B590899 : Blo 523799 590899 := bstep (se 1 (by rfl) ⟨443174, by rfl⟩ : syracuseStep 590899 = 886349) B886349
theorem B525363 : Blo 523799 525363 := bstep (se 1 (by rfl) ⟨394022, by rfl⟩ : syracuseStep 525363 = 788045) B788045
theorem B787523 : Blo 523799 787523 := bstep (se 1 (by rfl) ⟨590642, by rfl⟩ : syracuseStep 787523 = 1181285) B1181285
theorem B525379 : Blo 523799 525379 := bstep (se 1 (by rfl) ⟨394034, by rfl⟩ : syracuseStep 525379 = 788069) B788069
theorem B525395 : Blo 523799 525395 := bstep (se 1 (by rfl) ⟨394046, by rfl⟩ : syracuseStep 525395 = 788093) B788093
theorem B787553 : Blo 523799 787553 := bstep (se 2 (by rfl) ⟨295332, by rfl⟩ : syracuseStep 787553 = 590665) B590665
theorem B525411 : Blo 523799 525411 := bstep (se 1 (by rfl) ⟨394058, by rfl⟩ : syracuseStep 525411 = 788117) B788117
theorem B1770605 : Blo 523799 1770605 := bstep (se 3 (by rfl) ⟨331988, by rfl⟩ : syracuseStep 1770605 = 663977) B663977
theorem B787571 : Blo 523799 787571 := bstep (se 1 (by rfl) ⟨590678, by rfl⟩ : syracuseStep 787571 = 1181357) B1181357
theorem B525427 : Blo 523799 525427 := bstep (se 1 (by rfl) ⟨394070, by rfl⟩ : syracuseStep 525427 = 788141) B788141
theorem B525443 : Blo 523799 525443 := bstep (se 1 (by rfl) ⟨394082, by rfl⟩ : syracuseStep 525443 = 788165) B788165
theorem B1180817 : Blo 523799 1180817 := bstep (se 2 (by rfl) ⟨442806, by rfl⟩ : syracuseStep 1180817 = 885613) B885613
theorem B787601 : Blo 523799 787601 := bstep (se 2 (by rfl) ⟨295350, by rfl⟩ : syracuseStep 787601 = 590701) B590701
theorem B525459 : Blo 523799 525459 := bstep (se 1 (by rfl) ⟨394094, by rfl⟩ : syracuseStep 525459 = 788189) B788189
theorem B1770659 : Blo 523799 1770659 := bstep (se 1 (by rfl) ⟨1327994, by rfl⟩ : syracuseStep 1770659 = 2655989) B2655989
theorem B1180835 : Blo 523799 1180835 := bstep (se 1 (by rfl) ⟨885626, by rfl⟩ : syracuseStep 1180835 = 1771253) B1771253
theorem B787619 : Blo 523799 787619 := bstep (se 1 (by rfl) ⟨590714, by rfl⟩ : syracuseStep 787619 = 1181429) B1181429
theorem B525475 : Blo 523799 525475 := bstep (se 1 (by rfl) ⟨394106, by rfl⟩ : syracuseStep 525475 = 788213) B788213
theorem B885937 : Blo 523799 885937 := bstep (se 2 (by rfl) ⟨332226, by rfl⟩ : syracuseStep 885937 = 664453) B664453
theorem B525491 : Blo 523799 525491 := bstep (se 1 (by rfl) ⟨394118, by rfl⟩ : syracuseStep 525491 = 788237) B788237
theorem B787649 : Blo 523799 787649 := bstep (se 2 (by rfl) ⟨295368, by rfl⟩ : syracuseStep 787649 = 590737) B590737
theorem B591043 : Blo 523799 591043 := bstep (se 1 (by rfl) ⟨443282, by rfl⟩ : syracuseStep 591043 = 886565) B886565
theorem B525507 : Blo 523799 525507 := bstep (se 1 (by rfl) ⟨394130, by rfl⟩ : syracuseStep 525507 = 788261) B788261
theorem B885971 : Blo 523799 885971 := bstep (se 1 (by rfl) ⟨664478, by rfl⟩ : syracuseStep 885971 = 1328957) B1328957
theorem B787667 : Blo 523799 787667 := bstep (se 1 (by rfl) ⟨590750, by rfl⟩ : syracuseStep 787667 = 1181501) B1181501
theorem B525523 : Blo 523799 525523 := bstep (se 1 (by rfl) ⟨394142, by rfl⟩ : syracuseStep 525523 = 788285) B788285
theorem B525539 : Blo 523799 525539 := bstep (se 1 (by rfl) ⟨394154, by rfl⟩ : syracuseStep 525539 = 788309) B788309
theorem B787697 : Blo 523799 787697 := bstep (se 2 (by rfl) ⟨295386, by rfl⟩ : syracuseStep 787697 = 590773) B590773
theorem B525555 : Blo 523799 525555 := bstep (se 1 (by rfl) ⟨394166, by rfl⟩ : syracuseStep 525555 = 788333) B788333
theorem B787715 : Blo 523799 787715 := bstep (se 1 (by rfl) ⟨590786, by rfl⟩ : syracuseStep 787715 = 1181573) B1181573
theorem B525571 : Blo 523799 525571 := bstep (se 1 (by rfl) ⟨394178, by rfl⟩ : syracuseStep 525571 = 788357) B788357
theorem B525587 : Blo 523799 525587 := bstep (se 1 (by rfl) ⟨394190, by rfl⟩ : syracuseStep 525587 = 788381) B788381
theorem B787745 : Blo 523799 787745 := bstep (se 2 (by rfl) ⟨295404, by rfl⟩ : syracuseStep 787745 = 590809) B590809
theorem B525603 : Blo 523799 525603 := bstep (se 1 (by rfl) ⟨394202, by rfl⟩ : syracuseStep 525603 = 788405) B788405
theorem B787763 : Blo 523799 787763 := bstep (se 1 (by rfl) ⟨590822, by rfl⟩ : syracuseStep 787763 = 1181645) B1181645
theorem B525619 : Blo 523799 525619 := bstep (se 1 (by rfl) ⟨394214, by rfl⟩ : syracuseStep 525619 = 788429) B788429
theorem B525635 : Blo 523799 525635 := bstep (se 1 (by rfl) ⟨394226, by rfl⟩ : syracuseStep 525635 = 788453) B788453
theorem B787793 : Blo 523799 787793 := bstep (se 2 (by rfl) ⟨295422, by rfl⟩ : syracuseStep 787793 = 590845) B590845
theorem B886099 : Blo 523799 886099 := bstep (se 1 (by rfl) ⟨664574, by rfl⟩ : syracuseStep 886099 = 1329149) B1329149
theorem B591187 : Blo 523799 591187 := bstep (se 1 (by rfl) ⟨443390, by rfl⟩ : syracuseStep 591187 = 886781) B886781
theorem B525651 : Blo 523799 525651 := bstep (se 1 (by rfl) ⟨394238, by rfl⟩ : syracuseStep 525651 = 788477) B788477
theorem B787811 : Blo 523799 787811 := bstep (se 1 (by rfl) ⟨590858, by rfl⟩ : syracuseStep 787811 = 1181717) B1181717
theorem B525667 : Blo 523799 525667 := bstep (se 1 (by rfl) ⟨394250, by rfl⟩ : syracuseStep 525667 = 788501) B788501
theorem B525683 : Blo 523799 525683 := bstep (se 1 (by rfl) ⟨394262, by rfl⟩ : syracuseStep 525683 = 788525) B788525
theorem B787841 : Blo 523799 787841 := bstep (se 2 (by rfl) ⟨295440, by rfl⟩ : syracuseStep 787841 = 590881) B590881
theorem B525699 : Blo 523799 525699 := bstep (se 1 (by rfl) ⟨394274, by rfl⟩ : syracuseStep 525699 = 788549) B788549
theorem B787859 : Blo 523799 787859 := bstep (se 1 (by rfl) ⟨590894, by rfl⟩ : syracuseStep 787859 = 1181789) B1181789
theorem B525715 : Blo 523799 525715 := bstep (se 1 (by rfl) ⟨394286, by rfl⟩ : syracuseStep 525715 = 788573) B788573
theorem B525731 : Blo 523799 525731 := bstep (se 1 (by rfl) ⟨394298, by rfl⟩ : syracuseStep 525731 = 788597) B788597
theorem B2655665 : Blo 523799 2655665 := bstep (se 2 (by rfl) ⟨995874, by rfl⟩ : syracuseStep 2655665 = 1991749) B1991749
theorem B1770929 : Blo 523799 1770929 := bstep (se 2 (by rfl) ⟨664098, by rfl⟩ : syracuseStep 1770929 = 1328197) B1328197
theorem B1181105 : Blo 523799 1181105 := bstep (se 2 (by rfl) ⟨442914, by rfl⟩ : syracuseStep 1181105 = 885829) B885829
theorem B787889 : Blo 523799 787889 := bstep (se 2 (by rfl) ⟨295458, by rfl⟩ : syracuseStep 787889 = 590917) B590917
theorem B525747 : Blo 523799 525747 := bstep (se 1 (by rfl) ⟨394310, by rfl⟩ : syracuseStep 525747 = 788621) B788621
theorem B1181123 : Blo 523799 1181123 := bstep (se 1 (by rfl) ⟨885842, by rfl⟩ : syracuseStep 1181123 = 1771685) B1771685
theorem B787907 : Blo 523799 787907 := bstep (se 1 (by rfl) ⟨590930, by rfl⟩ : syracuseStep 787907 = 1181861) B1181861
theorem B525763 : Blo 523799 525763 := bstep (se 1 (by rfl) ⟨394322, by rfl⟩ : syracuseStep 525763 = 788645) B788645
theorem B525779 : Blo 523799 525779 := bstep (se 1 (by rfl) ⟨394334, by rfl⟩ : syracuseStep 525779 = 788669) B788669
theorem B886241 : Blo 523799 886241 := bstep (se 2 (by rfl) ⟨332340, by rfl⟩ : syracuseStep 886241 = 664681) B664681
theorem B787937 : Blo 523799 787937 := bstep (se 2 (by rfl) ⟨295476, by rfl⟩ : syracuseStep 787937 = 590953) B590953
theorem B591331 : Blo 523799 591331 := bstep (se 1 (by rfl) ⟨443498, by rfl⟩ : syracuseStep 591331 = 886997) B886997
theorem B525795 : Blo 523799 525795 := bstep (se 1 (by rfl) ⟨394346, by rfl⟩ : syracuseStep 525795 = 788693) B788693
theorem B787955 : Blo 523799 787955 := bstep (se 1 (by rfl) ⟨590966, by rfl⟩ : syracuseStep 787955 = 1181933) B1181933
theorem B525811 : Blo 523799 525811 := bstep (se 1 (by rfl) ⟨394358, by rfl⟩ : syracuseStep 525811 = 788717) B788717
theorem B525827 : Blo 523799 525827 := bstep (se 1 (by rfl) ⟨394370, by rfl⟩ : syracuseStep 525827 = 788741) B788741
theorem B787985 : Blo 523799 787985 := bstep (se 2 (by rfl) ⟨295494, by rfl⟩ : syracuseStep 787985 = 590989) B590989
theorem B525843 : Blo 523799 525843 := bstep (se 1 (by rfl) ⟨394382, by rfl⟩ : syracuseStep 525843 = 788765) B788765
theorem B788003 : Blo 523799 788003 := bstep (se 1 (by rfl) ⟨591002, by rfl⟩ : syracuseStep 788003 = 1182005) B1182005
theorem B525859 : Blo 523799 525859 := bstep (se 1 (by rfl) ⟨394394, by rfl⟩ : syracuseStep 525859 = 788789) B788789
theorem B525875 : Blo 523799 525875 := bstep (se 1 (by rfl) ⟨394406, by rfl⟩ : syracuseStep 525875 = 788813) B788813
theorem B788033 : Blo 523799 788033 := bstep (se 2 (by rfl) ⟨295512, by rfl⟩ : syracuseStep 788033 = 591025) B591025
theorem B525891 : Blo 523799 525891 := bstep (se 1 (by rfl) ⟨394418, by rfl⟩ : syracuseStep 525891 = 788837) B788837
theorem B788051 : Blo 523799 788051 := bstep (se 1 (by rfl) ⟨591038, by rfl⟩ : syracuseStep 788051 = 1182077) B1182077
theorem B525907 : Blo 523799 525907 := bstep (se 1 (by rfl) ⟨394430, by rfl⟩ : syracuseStep 525907 = 788861) B788861
theorem B886369 : Blo 523799 886369 := bstep (se 2 (by rfl) ⟨332388, by rfl⟩ : syracuseStep 886369 = 664777) B664777
theorem B525923 : Blo 523799 525923 := bstep (se 1 (by rfl) ⟨394442, by rfl⟩ : syracuseStep 525923 = 788885) B788885
theorem B2000483 : Blo 523799 2000483 := bstep (se 1 (by rfl) ⟨1500362, by rfl⟩ : syracuseStep 2000483 = 3000725) B3000725
theorem B788081 : Blo 523799 788081 := bstep (se 2 (by rfl) ⟨295530, by rfl⟩ : syracuseStep 788081 = 591061) B591061
theorem B2000497 : Blo 523799 2000497 := bstep (se 2 (by rfl) ⟨750186, by rfl⟩ : syracuseStep 2000497 = 1500373) B1500373
theorem B591475 : Blo 523799 591475 := bstep (se 1 (by rfl) ⟨443606, by rfl⟩ : syracuseStep 591475 = 887213) B887213
theorem B525939 : Blo 523799 525939 := bstep (se 1 (by rfl) ⟨394454, by rfl⟩ : syracuseStep 525939 = 788909) B788909
theorem B886403 : Blo 523799 886403 := bstep (se 1 (by rfl) ⟨664802, by rfl⟩ : syracuseStep 886403 = 1329605) B1329605
theorem B788099 : Blo 523799 788099 := bstep (se 1 (by rfl) ⟨591074, by rfl⟩ : syracuseStep 788099 = 1182149) B1182149
theorem B525955 : Blo 523799 525955 := bstep (se 1 (by rfl) ⟨394466, by rfl⟩ : syracuseStep 525955 = 788933) B788933
theorem B525971 : Blo 523799 525971 := bstep (se 1 (by rfl) ⟨394478, by rfl⟩ : syracuseStep 525971 = 788957) B788957
theorem B788129 : Blo 523799 788129 := bstep (se 2 (by rfl) ⟨295548, by rfl⟩ : syracuseStep 788129 = 591097) B591097
theorem B525987 : Blo 523799 525987 := bstep (se 1 (by rfl) ⟨394490, by rfl⟩ : syracuseStep 525987 = 788981) B788981
theorem B788147 : Blo 523799 788147 := bstep (se 1 (by rfl) ⟨591110, by rfl⟩ : syracuseStep 788147 = 1182221) B1182221
theorem B526003 : Blo 523799 526003 := bstep (se 1 (by rfl) ⟨394502, by rfl⟩ : syracuseStep 526003 = 789005) B789005
theorem B526019 : Blo 523799 526019 := bstep (se 1 (by rfl) ⟨394514, by rfl⟩ : syracuseStep 526019 = 789029) B789029
theorem B1181393 : Blo 523799 1181393 := bstep (se 2 (by rfl) ⟨443022, by rfl⟩ : syracuseStep 1181393 = 886045) B886045
theorem B788177 : Blo 523799 788177 := bstep (se 2 (by rfl) ⟨295566, by rfl⟩ : syracuseStep 788177 = 591133) B591133
theorem B526035 : Blo 523799 526035 := bstep (se 1 (by rfl) ⟨394526, by rfl⟩ : syracuseStep 526035 = 789053) B789053
theorem B1181411 : Blo 523799 1181411 := bstep (se 1 (by rfl) ⟨886058, by rfl⟩ : syracuseStep 1181411 = 1772117) B1772117
theorem B788195 : Blo 523799 788195 := bstep (se 1 (by rfl) ⟨591146, by rfl⟩ : syracuseStep 788195 = 1182293) B1182293
theorem B526051 : Blo 523799 526051 := bstep (se 1 (by rfl) ⟨394538, by rfl⟩ : syracuseStep 526051 = 789077) B789077
theorem B526067 : Blo 523799 526067 := bstep (se 1 (by rfl) ⟨394550, by rfl⟩ : syracuseStep 526067 = 789101) B789101
theorem B788225 : Blo 523799 788225 := bstep (se 2 (by rfl) ⟨295584, by rfl⟩ : syracuseStep 788225 = 591169) B591169
theorem B886531 : Blo 523799 886531 := bstep (se 1 (by rfl) ⟨664898, by rfl⟩ : syracuseStep 886531 = 1329797) B1329797
theorem B591619 : Blo 523799 591619 := bstep (se 1 (by rfl) ⟨443714, by rfl⟩ : syracuseStep 591619 = 887429) B887429
theorem B526083 : Blo 523799 526083 := bstep (se 1 (by rfl) ⟨394562, by rfl⟩ : syracuseStep 526083 = 789125) B789125
theorem B788243 : Blo 523799 788243 := bstep (se 1 (by rfl) ⟨591182, by rfl⟩ : syracuseStep 788243 = 1182365) B1182365
theorem B526099 : Blo 523799 526099 := bstep (se 1 (by rfl) ⟨394574, by rfl⟩ : syracuseStep 526099 = 789149) B789149
theorem B526115 : Blo 523799 526115 := bstep (se 1 (by rfl) ⟨394586, by rfl⟩ : syracuseStep 526115 = 789173) B789173
theorem B788273 : Blo 523799 788273 := bstep (se 2 (by rfl) ⟨295602, by rfl⟩ : syracuseStep 788273 = 591205) B591205
theorem B526131 : Blo 523799 526131 := bstep (se 1 (by rfl) ⟨394598, by rfl⟩ : syracuseStep 526131 = 789197) B789197
theorem B788291 : Blo 523799 788291 := bstep (se 1 (by rfl) ⟨591218, by rfl⟩ : syracuseStep 788291 = 1182437) B1182437
theorem B526147 : Blo 523799 526147 := bstep (se 1 (by rfl) ⟨394610, by rfl⟩ : syracuseStep 526147 = 789221) B789221
theorem B526163 : Blo 523799 526163 := bstep (se 1 (by rfl) ⟨394622, by rfl⟩ : syracuseStep 526163 = 789245) B789245
theorem B788321 : Blo 523799 788321 := bstep (se 2 (by rfl) ⟨295620, by rfl⟩ : syracuseStep 788321 = 591241) B591241
theorem B526179 : Blo 523799 526179 := bstep (se 1 (by rfl) ⟨394634, by rfl⟩ : syracuseStep 526179 = 789269) B789269
theorem B788339 : Blo 523799 788339 := bstep (se 1 (by rfl) ⟨591254, by rfl⟩ : syracuseStep 788339 = 1182509) B1182509
theorem B526195 : Blo 523799 526195 := bstep (se 1 (by rfl) ⟨394646, by rfl⟩ : syracuseStep 526195 = 789293) B789293
theorem B526211 : Blo 523799 526211 := bstep (se 1 (by rfl) ⟨394658, by rfl⟩ : syracuseStep 526211 = 789317) B789317
theorem B886673 : Blo 523799 886673 := bstep (se 2 (by rfl) ⟨332502, by rfl⟩ : syracuseStep 886673 = 665005) B665005
theorem B788369 : Blo 523799 788369 := bstep (se 2 (by rfl) ⟨295638, by rfl⟩ : syracuseStep 788369 = 591277) B591277
theorem B526227 : Blo 523799 526227 := bstep (se 1 (by rfl) ⟨394670, by rfl⟩ : syracuseStep 526227 = 789341) B789341
theorem B591763 : Blo 523799 591763 := bstep (se 1 (by rfl) ⟨443822, by rfl⟩ : syracuseStep 591763 = 887645) B887645
theorem B788387 : Blo 523799 788387 := bstep (se 1 (by rfl) ⟨591290, by rfl⟩ : syracuseStep 788387 = 1182581) B1182581
theorem B526243 : Blo 523799 526243 := bstep (se 1 (by rfl) ⟨394682, by rfl⟩ : syracuseStep 526243 = 789365) B789365
theorem B526259 : Blo 523799 526259 := bstep (se 1 (by rfl) ⟨394694, by rfl⟩ : syracuseStep 526259 = 789389) B789389
theorem B788417 : Blo 523799 788417 := bstep (se 2 (by rfl) ⟨295656, by rfl⟩ : syracuseStep 788417 = 591313) B591313
theorem B526275 : Blo 523799 526275 := bstep (se 1 (by rfl) ⟨394706, by rfl⟩ : syracuseStep 526275 = 789413) B789413
theorem B1771469 : Blo 523799 1771469 := bstep (se 3 (by rfl) ⟨332150, by rfl⟩ : syracuseStep 1771469 = 664301) B664301
theorem B788435 : Blo 523799 788435 := bstep (se 1 (by rfl) ⟨591326, by rfl⟩ : syracuseStep 788435 = 1182653) B1182653
theorem B526291 : Blo 523799 526291 := bstep (se 1 (by rfl) ⟨394718, by rfl⟩ : syracuseStep 526291 = 789437) B789437
theorem B3377123 : Blo 523799 3377123 := bstep (se 1 (by rfl) ⟨2532842, by rfl⟩ : syracuseStep 3377123 = 5065685) B5065685
theorem B526307 : Blo 523799 526307 := bstep (se 1 (by rfl) ⟨394730, by rfl⟩ : syracuseStep 526307 = 789461) B789461
theorem B1181681 : Blo 523799 1181681 := bstep (se 2 (by rfl) ⟨443130, by rfl⟩ : syracuseStep 1181681 = 886261) B886261
theorem B788465 : Blo 523799 788465 := bstep (se 2 (by rfl) ⟨295674, by rfl⟩ : syracuseStep 788465 = 591349) B591349
theorem B526323 : Blo 523799 526323 := bstep (se 1 (by rfl) ⟨394742, by rfl⟩ : syracuseStep 526323 = 789485) B789485
theorem B1771523 : Blo 523799 1771523 := bstep (se 1 (by rfl) ⟨1328642, by rfl⟩ : syracuseStep 1771523 = 2657285) B2657285
theorem B1181699 : Blo 523799 1181699 := bstep (se 1 (by rfl) ⟨886274, by rfl⟩ : syracuseStep 1181699 = 1772549) B1772549
theorem B788483 : Blo 523799 788483 := bstep (se 1 (by rfl) ⟨591362, by rfl⟩ : syracuseStep 788483 = 1182725) B1182725
theorem B526339 : Blo 523799 526339 := bstep (se 1 (by rfl) ⟨394754, by rfl⟩ : syracuseStep 526339 = 789509) B789509
theorem B886801 : Blo 523799 886801 := bstep (se 2 (by rfl) ⟨332550, by rfl⟩ : syracuseStep 886801 = 665101) B665101
theorem B526355 : Blo 523799 526355 := bstep (se 1 (by rfl) ⟨394766, by rfl⟩ : syracuseStep 526355 = 789533) B789533
theorem B788513 : Blo 523799 788513 := bstep (se 2 (by rfl) ⟨295692, by rfl⟩ : syracuseStep 788513 = 591385) B591385
theorem B591907 : Blo 523799 591907 := bstep (se 1 (by rfl) ⟨443930, by rfl⟩ : syracuseStep 591907 = 887861) B887861
theorem B526371 : Blo 523799 526371 := bstep (se 1 (by rfl) ⟨394778, by rfl⟩ : syracuseStep 526371 = 789557) B789557
theorem B886835 : Blo 523799 886835 := bstep (se 1 (by rfl) ⟨665126, by rfl⟩ : syracuseStep 886835 = 1330253) B1330253
theorem B788531 : Blo 523799 788531 := bstep (se 1 (by rfl) ⟨591398, by rfl⟩ : syracuseStep 788531 = 1182797) B1182797
theorem B526387 : Blo 523799 526387 := bstep (se 1 (by rfl) ⟨394790, by rfl⟩ : syracuseStep 526387 = 789581) B789581
theorem B526403 : Blo 523799 526403 := bstep (se 1 (by rfl) ⟨394802, by rfl⟩ : syracuseStep 526403 = 789605) B789605
theorem B788561 : Blo 523799 788561 := bstep (se 2 (by rfl) ⟨295710, by rfl⟩ : syracuseStep 788561 = 591421) B591421
theorem B526419 : Blo 523799 526419 := bstep (se 1 (by rfl) ⟨394814, by rfl⟩ : syracuseStep 526419 = 789629) B789629
theorem B788579 : Blo 523799 788579 := bstep (se 1 (by rfl) ⟨591434, by rfl⟩ : syracuseStep 788579 = 1182869) B1182869
theorem B526435 : Blo 523799 526435 := bstep (se 1 (by rfl) ⟨394826, by rfl⟩ : syracuseStep 526435 = 789653) B789653
theorem B526451 : Blo 523799 526451 := bstep (se 1 (by rfl) ⟨394838, by rfl⟩ : syracuseStep 526451 = 789677) B789677
theorem B788609 : Blo 523799 788609 := bstep (se 2 (by rfl) ⟨295728, by rfl⟩ : syracuseStep 788609 = 591457) B591457
theorem B526467 : Blo 523799 526467 := bstep (se 1 (by rfl) ⟨394850, by rfl⟩ : syracuseStep 526467 = 789701) B789701
theorem B788627 : Blo 523799 788627 := bstep (se 1 (by rfl) ⟨591470, by rfl⟩ : syracuseStep 788627 = 1182941) B1182941
theorem B526483 : Blo 523799 526483 := bstep (se 1 (by rfl) ⟨394862, by rfl⟩ : syracuseStep 526483 = 789725) B789725
theorem B526499 : Blo 523799 526499 := bstep (se 1 (by rfl) ⟨394874, by rfl⟩ : syracuseStep 526499 = 789749) B789749
theorem B788657 : Blo 523799 788657 := bstep (se 2 (by rfl) ⟨295746, by rfl⟩ : syracuseStep 788657 = 591493) B591493
theorem B886963 : Blo 523799 886963 := bstep (se 1 (by rfl) ⟨665222, by rfl⟩ : syracuseStep 886963 = 1330445) B1330445
theorem B592051 : Blo 523799 592051 := bstep (se 1 (by rfl) ⟨444038, by rfl⟩ : syracuseStep 592051 = 888077) B888077
theorem B526515 : Blo 523799 526515 := bstep (se 1 (by rfl) ⟨394886, by rfl⟩ : syracuseStep 526515 = 789773) B789773
theorem B788675 : Blo 523799 788675 := bstep (se 1 (by rfl) ⟨591506, by rfl⟩ : syracuseStep 788675 = 1183013) B1183013
theorem B526531 : Blo 523799 526531 := bstep (se 1 (by rfl) ⟨394898, by rfl⟩ : syracuseStep 526531 = 789797) B789797
theorem B526547 : Blo 523799 526547 := bstep (se 1 (by rfl) ⟨394910, by rfl⟩ : syracuseStep 526547 = 789821) B789821
theorem B788705 : Blo 523799 788705 := bstep (se 2 (by rfl) ⟨295764, by rfl⟩ : syracuseStep 788705 = 591529) B591529
theorem B526563 : Blo 523799 526563 := bstep (se 1 (by rfl) ⟨394922, by rfl⟩ : syracuseStep 526563 = 789845) B789845
theorem B788723 : Blo 523799 788723 := bstep (se 1 (by rfl) ⟨591542, by rfl⟩ : syracuseStep 788723 = 1183085) B1183085
theorem B526579 : Blo 523799 526579 := bstep (se 1 (by rfl) ⟨394934, by rfl⟩ : syracuseStep 526579 = 789869) B789869
theorem B526595 : Blo 523799 526595 := bstep (se 1 (by rfl) ⟨394946, by rfl⟩ : syracuseStep 526595 = 789893) B789893
theorem B1771793 : Blo 523799 1771793 := bstep (se 2 (by rfl) ⟨664422, by rfl⟩ : syracuseStep 1771793 = 1328845) B1328845
theorem B1181969 : Blo 523799 1181969 := bstep (se 2 (by rfl) ⟨443238, by rfl⟩ : syracuseStep 1181969 = 886477) B886477
theorem B788753 : Blo 523799 788753 := bstep (se 2 (by rfl) ⟨295782, by rfl⟩ : syracuseStep 788753 = 591565) B591565
theorem B526611 : Blo 523799 526611 := bstep (se 1 (by rfl) ⟨394958, by rfl⟩ : syracuseStep 526611 = 789917) B789917
theorem B1181987 : Blo 523799 1181987 := bstep (se 1 (by rfl) ⟨886490, by rfl⟩ : syracuseStep 1181987 = 1772981) B1772981
theorem B788771 : Blo 523799 788771 := bstep (se 1 (by rfl) ⟨591578, by rfl⟩ : syracuseStep 788771 = 1183157) B1183157
theorem B526627 : Blo 523799 526627 := bstep (se 1 (by rfl) ⟨394970, by rfl⟩ : syracuseStep 526627 = 789941) B789941
theorem B526643 : Blo 523799 526643 := bstep (se 1 (by rfl) ⟨394982, by rfl⟩ : syracuseStep 526643 = 789965) B789965
theorem B887105 : Blo 523799 887105 := bstep (se 2 (by rfl) ⟨332664, by rfl⟩ : syracuseStep 887105 = 665329) B665329
theorem B788801 : Blo 523799 788801 := bstep (se 2 (by rfl) ⟨295800, by rfl⟩ : syracuseStep 788801 = 591601) B591601
theorem B592195 : Blo 523799 592195 := bstep (se 1 (by rfl) ⟨444146, by rfl⟩ : syracuseStep 592195 = 888293) B888293
theorem B526659 : Blo 523799 526659 := bstep (se 1 (by rfl) ⟨394994, by rfl⟩ : syracuseStep 526659 = 789989) B789989
theorem B788819 : Blo 523799 788819 := bstep (se 1 (by rfl) ⟨591614, by rfl⟩ : syracuseStep 788819 = 1183229) B1183229
theorem B526675 : Blo 523799 526675 := bstep (se 1 (by rfl) ⟨395006, by rfl⟩ : syracuseStep 526675 = 790013) B790013
theorem B526691 : Blo 523799 526691 := bstep (se 1 (by rfl) ⟨395018, by rfl⟩ : syracuseStep 526691 = 790037) B790037
theorem B788849 : Blo 523799 788849 := bstep (se 2 (by rfl) ⟨295818, by rfl⟩ : syracuseStep 788849 = 591637) B591637
theorem B526707 : Blo 523799 526707 := bstep (se 1 (by rfl) ⟨395030, by rfl⟩ : syracuseStep 526707 = 790061) B790061
theorem B788867 : Blo 523799 788867 := bstep (se 1 (by rfl) ⟨591650, by rfl⟩ : syracuseStep 788867 = 1183301) B1183301
theorem B526723 : Blo 523799 526723 := bstep (se 1 (by rfl) ⟨395042, by rfl⟩ : syracuseStep 526723 = 790085) B790085
theorem B526739 : Blo 523799 526739 := bstep (se 1 (by rfl) ⟨395054, by rfl⟩ : syracuseStep 526739 = 790109) B790109
theorem B788897 : Blo 523799 788897 := bstep (se 2 (by rfl) ⟨295836, by rfl⟩ : syracuseStep 788897 = 591673) B591673
theorem B526755 : Blo 523799 526755 := bstep (se 1 (by rfl) ⟨395066, by rfl⟩ : syracuseStep 526755 = 790133) B790133
theorem B788915 : Blo 523799 788915 := bstep (se 1 (by rfl) ⟨591686, by rfl⟩ : syracuseStep 788915 = 1183373) B1183373
theorem B526771 : Blo 523799 526771 := bstep (se 1 (by rfl) ⟨395078, by rfl⟩ : syracuseStep 526771 = 790157) B790157
theorem B887233 : Blo 523799 887233 := bstep (se 2 (by rfl) ⟨332712, by rfl⟩ : syracuseStep 887233 = 665425) B665425
theorem B526787 : Blo 523799 526787 := bstep (se 1 (by rfl) ⟨395090, by rfl⟩ : syracuseStep 526787 = 790181) B790181
theorem B788945 : Blo 523799 788945 := bstep (se 2 (by rfl) ⟨295854, by rfl⟩ : syracuseStep 788945 = 591709) B591709
theorem B592339 : Blo 523799 592339 := bstep (se 1 (by rfl) ⟨444254, by rfl⟩ : syracuseStep 592339 = 888509) B888509
theorem B526803 : Blo 523799 526803 := bstep (se 1 (by rfl) ⟨395102, by rfl⟩ : syracuseStep 526803 = 790205) B790205
theorem B887267 : Blo 523799 887267 := bstep (se 1 (by rfl) ⟨665450, by rfl⟩ : syracuseStep 887267 = 1330901) B1330901
theorem B788963 : Blo 523799 788963 := bstep (se 1 (by rfl) ⟨591722, by rfl⟩ : syracuseStep 788963 = 1183445) B1183445
theorem B526819 : Blo 523799 526819 := bstep (se 1 (by rfl) ⟨395114, by rfl⟩ : syracuseStep 526819 = 790229) B790229
theorem B526835 : Blo 523799 526835 := bstep (se 1 (by rfl) ⟨395126, by rfl⟩ : syracuseStep 526835 = 790253) B790253
theorem B788993 : Blo 523799 788993 := bstep (se 2 (by rfl) ⟨295872, by rfl⟩ : syracuseStep 788993 = 591745) B591745
theorem B526851 : Blo 523799 526851 := bstep (se 1 (by rfl) ⟨395138, by rfl⟩ : syracuseStep 526851 = 790277) B790277
theorem B1149457 : Blo 523799 1149457 := bstep (se 2 (by rfl) ⟨431046, by rfl⟩ : syracuseStep 1149457 = 862093) B862093
theorem B789011 : Blo 523799 789011 := bstep (se 1 (by rfl) ⟨591758, by rfl⟩ : syracuseStep 789011 = 1183517) B1183517
theorem B526867 : Blo 523799 526867 := bstep (se 1 (by rfl) ⟨395150, by rfl⟩ : syracuseStep 526867 = 790301) B790301
theorem B526883 : Blo 523799 526883 := bstep (se 1 (by rfl) ⟨395162, by rfl⟩ : syracuseStep 526883 = 790325) B790325
theorem B1182257 : Blo 523799 1182257 := bstep (se 2 (by rfl) ⟨443346, by rfl⟩ : syracuseStep 1182257 = 886693) B886693
theorem B789041 : Blo 523799 789041 := bstep (se 2 (by rfl) ⟨295890, by rfl⟩ : syracuseStep 789041 = 591781) B591781
theorem B559667 : Blo 523799 559667 := bstep (se 1 (by rfl) ⟨419750, by rfl⟩ : syracuseStep 559667 = 839501) B839501
theorem B526899 : Blo 523799 526899 := bstep (se 1 (by rfl) ⟨395174, by rfl⟩ : syracuseStep 526899 = 790349) B790349
theorem B1182275 : Blo 523799 1182275 := bstep (se 1 (by rfl) ⟨886706, by rfl⟩ : syracuseStep 1182275 = 1773413) B1773413
theorem B789059 : Blo 523799 789059 := bstep (se 1 (by rfl) ⟨591794, by rfl⟩ : syracuseStep 789059 = 1183589) B1183589
theorem B526915 : Blo 523799 526915 := bstep (se 1 (by rfl) ⟨395186, by rfl⟩ : syracuseStep 526915 = 790373) B790373
theorem B526931 : Blo 523799 526931 := bstep (se 1 (by rfl) ⟨395198, by rfl⟩ : syracuseStep 526931 = 790397) B790397
theorem B789089 : Blo 523799 789089 := bstep (se 2 (by rfl) ⟨295908, by rfl⟩ : syracuseStep 789089 = 591817) B591817
theorem B887395 : Blo 523799 887395 := bstep (se 1 (by rfl) ⟨665546, by rfl⟩ : syracuseStep 887395 = 1331093) B1331093
theorem B592483 : Blo 523799 592483 := bstep (se 1 (by rfl) ⟨444362, by rfl⟩ : syracuseStep 592483 = 888725) B888725
theorem B526947 : Blo 523799 526947 := bstep (se 1 (by rfl) ⟨395210, by rfl⟩ : syracuseStep 526947 = 790421) B790421
theorem B789107 : Blo 523799 789107 := bstep (se 1 (by rfl) ⟨591830, by rfl⟩ : syracuseStep 789107 = 1183661) B1183661
theorem B526963 : Blo 523799 526963 := bstep (se 1 (by rfl) ⟨395222, by rfl⟩ : syracuseStep 526963 = 790445) B790445
theorem B526979 : Blo 523799 526979 := bstep (se 1 (by rfl) ⟨395234, by rfl⟩ : syracuseStep 526979 = 790469) B790469
theorem B6752909 : Blo 523799 6752909 := bstep (se 3 (by rfl) ⟨1266170, by rfl⟩ : syracuseStep 6752909 = 2532341) B2532341
theorem B789137 : Blo 523799 789137 := bstep (se 2 (by rfl) ⟨295926, by rfl⟩ : syracuseStep 789137 = 591853) B591853
theorem B526995 : Blo 523799 526995 := bstep (se 1 (by rfl) ⟨395246, by rfl⟩ : syracuseStep 526995 = 790493) B790493
theorem B789155 : Blo 523799 789155 := bstep (se 1 (by rfl) ⟨591866, by rfl⟩ : syracuseStep 789155 = 1183733) B1183733
theorem B527011 : Blo 523799 527011 := bstep (se 1 (by rfl) ⟨395258, by rfl⟩ : syracuseStep 527011 = 790517) B790517
theorem B527027 : Blo 523799 527027 := bstep (se 1 (by rfl) ⟨395270, by rfl⟩ : syracuseStep 527027 = 790541) B790541
theorem B789185 : Blo 523799 789185 := bstep (se 2 (by rfl) ⟨295944, by rfl⟩ : syracuseStep 789185 = 591889) B591889
theorem B527043 : Blo 523799 527043 := bstep (se 1 (by rfl) ⟨395282, by rfl⟩ : syracuseStep 527043 = 790565) B790565
theorem B789203 : Blo 523799 789203 := bstep (se 1 (by rfl) ⟨591902, by rfl⟩ : syracuseStep 789203 = 1183805) B1183805
theorem B527059 : Blo 523799 527059 := bstep (se 1 (by rfl) ⟨395294, by rfl⟩ : syracuseStep 527059 = 790589) B790589
theorem B527075 : Blo 523799 527075 := bstep (se 1 (by rfl) ⟨395306, by rfl⟩ : syracuseStep 527075 = 790613) B790613
theorem B887537 : Blo 523799 887537 := bstep (se 2 (by rfl) ⟨332826, by rfl⟩ : syracuseStep 887537 = 665653) B665653
theorem B789233 : Blo 523799 789233 := bstep (se 2 (by rfl) ⟨295962, by rfl⟩ : syracuseStep 789233 = 591925) B591925
theorem B592627 : Blo 523799 592627 := bstep (se 1 (by rfl) ⟨444470, by rfl⟩ : syracuseStep 592627 = 888941) B888941
theorem B527091 : Blo 523799 527091 := bstep (se 1 (by rfl) ⟨395318, by rfl⟩ : syracuseStep 527091 = 790637) B790637
theorem B789251 : Blo 523799 789251 := bstep (se 1 (by rfl) ⟨591938, by rfl⟩ : syracuseStep 789251 = 1183877) B1183877
theorem B527107 : Blo 523799 527107 := bstep (se 1 (by rfl) ⟨395330, by rfl⟩ : syracuseStep 527107 = 790661) B790661
theorem B527123 : Blo 523799 527123 := bstep (se 1 (by rfl) ⟨395342, by rfl⟩ : syracuseStep 527123 = 790685) B790685
theorem B789281 : Blo 523799 789281 := bstep (se 2 (by rfl) ⟨295980, by rfl⟩ : syracuseStep 789281 = 591961) B591961
theorem B527139 : Blo 523799 527139 := bstep (se 1 (by rfl) ⟨395354, by rfl⟩ : syracuseStep 527139 = 790709) B790709
theorem B1772333 : Blo 523799 1772333 := bstep (se 3 (by rfl) ⟨332312, by rfl⟩ : syracuseStep 1772333 = 664625) B664625
theorem B789299 : Blo 523799 789299 := bstep (se 1 (by rfl) ⟨591974, by rfl⟩ : syracuseStep 789299 = 1183949) B1183949
theorem B527155 : Blo 523799 527155 := bstep (se 1 (by rfl) ⟨395366, by rfl⟩ : syracuseStep 527155 = 790733) B790733
theorem B527171 : Blo 523799 527171 := bstep (se 1 (by rfl) ⟨395378, by rfl⟩ : syracuseStep 527171 = 790757) B790757
theorem B1182545 : Blo 523799 1182545 := bstep (se 2 (by rfl) ⟨443454, by rfl⟩ : syracuseStep 1182545 = 886909) B886909
theorem B789329 : Blo 523799 789329 := bstep (se 2 (by rfl) ⟨295998, by rfl⟩ : syracuseStep 789329 = 591997) B591997
theorem B527187 : Blo 523799 527187 := bstep (se 1 (by rfl) ⟨395390, by rfl⟩ : syracuseStep 527187 = 790781) B790781
theorem B2657123 : Blo 523799 2657123 := bstep (se 1 (by rfl) ⟨1992842, by rfl⟩ : syracuseStep 2657123 = 3985685) B3985685
theorem B1772387 : Blo 523799 1772387 := bstep (se 1 (by rfl) ⟨1329290, by rfl⟩ : syracuseStep 1772387 = 2658581) B2658581
theorem B1182563 : Blo 523799 1182563 := bstep (se 1 (by rfl) ⟨886922, by rfl⟩ : syracuseStep 1182563 = 1773845) B1773845
theorem B789347 : Blo 523799 789347 := bstep (se 1 (by rfl) ⟨592010, by rfl⟩ : syracuseStep 789347 = 1184021) B1184021
theorem B527203 : Blo 523799 527203 := bstep (se 1 (by rfl) ⟨395402, by rfl⟩ : syracuseStep 527203 = 790805) B790805
theorem B887665 : Blo 523799 887665 := bstep (se 2 (by rfl) ⟨332874, by rfl⟩ : syracuseStep 887665 = 665749) B665749
theorem B527219 : Blo 523799 527219 := bstep (se 1 (by rfl) ⟨395414, by rfl⟩ : syracuseStep 527219 = 790829) B790829
theorem B789377 : Blo 523799 789377 := bstep (se 2 (by rfl) ⟨296016, by rfl⟩ : syracuseStep 789377 = 592033) B592033
theorem B592771 : Blo 523799 592771 := bstep (se 1 (by rfl) ⟨444578, by rfl⟩ : syracuseStep 592771 = 889157) B889157
theorem B527235 : Blo 523799 527235 := bstep (se 1 (by rfl) ⟨395426, by rfl⟩ : syracuseStep 527235 = 790853) B790853
theorem B2886533 : Blo 523799 2886533 := bstep (se 4 (by rfl) ⟨270612, by rfl⟩ : syracuseStep 2886533 = 541225) B541225
theorem B887699 : Blo 523799 887699 := bstep (se 1 (by rfl) ⟨665774, by rfl⟩ : syracuseStep 887699 = 1331549) B1331549
theorem B789395 : Blo 523799 789395 := bstep (se 1 (by rfl) ⟨592046, by rfl⟩ : syracuseStep 789395 = 1184093) B1184093
theorem B527251 : Blo 523799 527251 := bstep (se 1 (by rfl) ⟨395438, by rfl⟩ : syracuseStep 527251 = 790877) B790877
theorem B527267 : Blo 523799 527267 := bstep (se 1 (by rfl) ⟨395450, by rfl⟩ : syracuseStep 527267 = 790901) B790901
theorem B789425 : Blo 523799 789425 := bstep (se 2 (by rfl) ⟨296034, by rfl⟩ : syracuseStep 789425 = 592069) B592069
theorem B527283 : Blo 523799 527283 := bstep (se 1 (by rfl) ⟨395462, by rfl⟩ : syracuseStep 527283 = 790925) B790925
theorem B789443 : Blo 523799 789443 := bstep (se 1 (by rfl) ⟨592082, by rfl⟩ : syracuseStep 789443 = 1184165) B1184165
theorem B527299 : Blo 523799 527299 := bstep (se 1 (by rfl) ⟨395474, by rfl⟩ : syracuseStep 527299 = 790949) B790949
theorem B527315 : Blo 523799 527315 := bstep (se 1 (by rfl) ⟨395486, by rfl⟩ : syracuseStep 527315 = 790973) B790973
theorem B789473 : Blo 523799 789473 := bstep (se 2 (by rfl) ⟨296052, by rfl⟩ : syracuseStep 789473 = 592105) B592105
theorem B527331 : Blo 523799 527331 := bstep (se 1 (by rfl) ⟨395498, by rfl⟩ : syracuseStep 527331 = 790997) B790997
theorem B789491 : Blo 523799 789491 := bstep (se 1 (by rfl) ⟨592118, by rfl⟩ : syracuseStep 789491 = 1184237) B1184237
theorem B527347 : Blo 523799 527347 := bstep (se 1 (by rfl) ⟨395510, by rfl⟩ : syracuseStep 527347 = 791021) B791021
theorem B527363 : Blo 523799 527363 := bstep (se 1 (by rfl) ⟨395522, by rfl⟩ : syracuseStep 527363 = 791045) B791045
theorem B789521 : Blo 523799 789521 := bstep (se 2 (by rfl) ⟨296070, by rfl⟩ : syracuseStep 789521 = 592141) B592141
theorem B887827 : Blo 523799 887827 := bstep (se 1 (by rfl) ⟨665870, by rfl⟩ : syracuseStep 887827 = 1331741) B1331741
theorem B592915 : Blo 523799 592915 := bstep (se 1 (by rfl) ⟨444686, by rfl⟩ : syracuseStep 592915 = 889373) B889373
theorem B527379 : Blo 523799 527379 := bstep (se 1 (by rfl) ⟨395534, by rfl⟩ : syracuseStep 527379 = 791069) B791069
theorem B789539 : Blo 523799 789539 := bstep (se 1 (by rfl) ⟨592154, by rfl⟩ : syracuseStep 789539 = 1184309) B1184309
theorem B2001955 : Blo 523799 2001955 := bstep (se 1 (by rfl) ⟨1501466, by rfl⟩ : syracuseStep 2001955 = 3002933) B3002933
theorem B527395 : Blo 523799 527395 := bstep (se 1 (by rfl) ⟨395546, by rfl⟩ : syracuseStep 527395 = 791093) B791093
theorem B527411 : Blo 523799 527411 := bstep (se 1 (by rfl) ⟨395558, by rfl⟩ : syracuseStep 527411 = 791117) B791117
theorem B5999669 : Blo 523799 5999669 := bstep (se 5 (by rfl) ⟨281234, by rfl⟩ : syracuseStep 5999669 = 562469) B562469
theorem B789569 : Blo 523799 789569 := bstep (se 2 (by rfl) ⟨296088, by rfl⟩ : syracuseStep 789569 = 592177) B592177
theorem B527427 : Blo 523799 527427 := bstep (se 1 (by rfl) ⟨395570, by rfl⟩ : syracuseStep 527427 = 791141) B791141
theorem B789587 : Blo 523799 789587 := bstep (se 1 (by rfl) ⟨592190, by rfl⟩ : syracuseStep 789587 = 1184381) B1184381
theorem B527443 : Blo 523799 527443 := bstep (se 1 (by rfl) ⟨395582, by rfl⟩ : syracuseStep 527443 = 791165) B791165
theorem B527459 : Blo 523799 527459 := bstep (se 1 (by rfl) ⟨395594, by rfl⟩ : syracuseStep 527459 = 791189) B791189
theorem B1772657 : Blo 523799 1772657 := bstep (se 2 (by rfl) ⟨664746, by rfl⟩ : syracuseStep 1772657 = 1329493) B1329493
theorem B1182833 : Blo 523799 1182833 := bstep (se 2 (by rfl) ⟨443562, by rfl⟩ : syracuseStep 1182833 = 887125) B887125
theorem B789617 : Blo 523799 789617 := bstep (se 2 (by rfl) ⟨296106, by rfl⟩ : syracuseStep 789617 = 592213) B592213
theorem B527475 : Blo 523799 527475 := bstep (se 1 (by rfl) ⟨395606, by rfl⟩ : syracuseStep 527475 = 791213) B791213
theorem B1182851 : Blo 523799 1182851 := bstep (se 1 (by rfl) ⟨887138, by rfl⟩ : syracuseStep 1182851 = 1774277) B1774277
theorem B789635 : Blo 523799 789635 := bstep (se 1 (by rfl) ⟨592226, by rfl⟩ : syracuseStep 789635 = 1184453) B1184453
theorem B527491 : Blo 523799 527491 := bstep (se 1 (by rfl) ⟨395618, by rfl⟩ : syracuseStep 527491 = 791237) B791237
theorem B527507 : Blo 523799 527507 := bstep (se 1 (by rfl) ⟨395630, by rfl⟩ : syracuseStep 527507 = 791261) B791261
theorem B887969 : Blo 523799 887969 := bstep (se 2 (by rfl) ⟨332988, by rfl⟩ : syracuseStep 887969 = 665977) B665977
theorem B789665 : Blo 523799 789665 := bstep (se 2 (by rfl) ⟨296124, by rfl⟩ : syracuseStep 789665 = 592249) B592249
theorem B593059 : Blo 523799 593059 := bstep (se 1 (by rfl) ⟨444794, by rfl⟩ : syracuseStep 593059 = 889589) B889589
theorem B527523 : Blo 523799 527523 := bstep (se 1 (by rfl) ⟨395642, by rfl⟩ : syracuseStep 527523 = 791285) B791285
theorem B756913 : Blo 523799 756913 := bstep (se 2 (by rfl) ⟨283842, by rfl⟩ : syracuseStep 756913 = 567685) B567685
theorem B789683 : Blo 523799 789683 := bstep (se 1 (by rfl) ⟨592262, by rfl⟩ : syracuseStep 789683 = 1184525) B1184525
theorem B527539 : Blo 523799 527539 := bstep (se 1 (by rfl) ⟨395654, by rfl⟩ : syracuseStep 527539 = 791309) B791309
theorem B527555 : Blo 523799 527555 := bstep (se 1 (by rfl) ⟨395666, by rfl⟩ : syracuseStep 527555 = 791333) B791333
theorem B789713 : Blo 523799 789713 := bstep (se 2 (by rfl) ⟨296142, by rfl⟩ : syracuseStep 789713 = 592285) B592285
theorem B527571 : Blo 523799 527571 := bstep (se 1 (by rfl) ⟨395678, by rfl⟩ : syracuseStep 527571 = 791357) B791357
theorem B789731 : Blo 523799 789731 := bstep (se 1 (by rfl) ⟨592298, by rfl⟩ : syracuseStep 789731 = 1184597) B1184597
theorem B527587 : Blo 523799 527587 := bstep (se 1 (by rfl) ⟨395690, by rfl⟩ : syracuseStep 527587 = 791381) B791381
theorem B527603 : Blo 523799 527603 := bstep (se 1 (by rfl) ⟨395702, by rfl⟩ : syracuseStep 527603 = 791405) B791405
theorem B789761 : Blo 523799 789761 := bstep (se 2 (by rfl) ⟨296160, by rfl⟩ : syracuseStep 789761 = 592321) B592321
theorem B527619 : Blo 523799 527619 := bstep (se 1 (by rfl) ⟨395714, by rfl⟩ : syracuseStep 527619 = 791429) B791429
theorem B789779 : Blo 523799 789779 := bstep (se 1 (by rfl) ⟨592334, by rfl⟩ : syracuseStep 789779 = 1184669) B1184669
theorem B527635 : Blo 523799 527635 := bstep (se 1 (by rfl) ⟨395726, by rfl⟩ : syracuseStep 527635 = 791453) B791453
theorem B888097 : Blo 523799 888097 := bstep (se 2 (by rfl) ⟨333036, by rfl⟩ : syracuseStep 888097 = 666073) B666073
theorem B527651 : Blo 523799 527651 := bstep (se 1 (by rfl) ⟨395738, by rfl⟩ : syracuseStep 527651 = 791477) B791477
theorem B789809 : Blo 523799 789809 := bstep (se 2 (by rfl) ⟨296178, by rfl⟩ : syracuseStep 789809 = 592357) B592357
theorem B593203 : Blo 523799 593203 := bstep (se 1 (by rfl) ⟨444902, by rfl⟩ : syracuseStep 593203 = 889805) B889805
theorem B527667 : Blo 523799 527667 := bstep (se 1 (by rfl) ⟨395750, by rfl⟩ : syracuseStep 527667 = 791501) B791501
theorem B888131 : Blo 523799 888131 := bstep (se 1 (by rfl) ⟨666098, by rfl⟩ : syracuseStep 888131 = 1332197) B1332197
theorem B789827 : Blo 523799 789827 := bstep (se 1 (by rfl) ⟨592370, by rfl⟩ : syracuseStep 789827 = 1184741) B1184741
theorem B527683 : Blo 523799 527683 := bstep (se 1 (by rfl) ⟨395762, by rfl⟩ : syracuseStep 527683 = 791525) B791525
theorem B527699 : Blo 523799 527699 := bstep (se 1 (by rfl) ⟨395774, by rfl⟩ : syracuseStep 527699 = 791549) B791549
theorem B789857 : Blo 523799 789857 := bstep (se 2 (by rfl) ⟨296196, by rfl⟩ : syracuseStep 789857 = 592393) B592393
theorem B527715 : Blo 523799 527715 := bstep (se 1 (by rfl) ⟨395786, by rfl⟩ : syracuseStep 527715 = 791573) B791573
theorem B789875 : Blo 523799 789875 := bstep (se 1 (by rfl) ⟨592406, by rfl⟩ : syracuseStep 789875 = 1184813) B1184813
theorem B527731 : Blo 523799 527731 := bstep (se 1 (by rfl) ⟨395798, by rfl⟩ : syracuseStep 527731 = 791597) B791597
theorem B527747 : Blo 523799 527747 := bstep (se 1 (by rfl) ⟨395810, by rfl⟩ : syracuseStep 527747 = 791621) B791621
theorem B1183121 : Blo 523799 1183121 := bstep (se 2 (by rfl) ⟨443670, by rfl⟩ : syracuseStep 1183121 = 887341) B887341
theorem B789905 : Blo 523799 789905 := bstep (se 2 (by rfl) ⟨296214, by rfl⟩ : syracuseStep 789905 = 592429) B592429
theorem B527763 : Blo 523799 527763 := bstep (se 1 (by rfl) ⟨395822, by rfl⟩ : syracuseStep 527763 = 791645) B791645
theorem B1183139 : Blo 523799 1183139 := bstep (se 1 (by rfl) ⟨887354, by rfl⟩ : syracuseStep 1183139 = 1774709) B1774709
theorem B789923 : Blo 523799 789923 := bstep (se 1 (by rfl) ⟨592442, by rfl⟩ : syracuseStep 789923 = 1184885) B1184885
theorem B527779 : Blo 523799 527779 := bstep (se 1 (by rfl) ⟨395834, by rfl⟩ : syracuseStep 527779 = 791669) B791669
theorem B527795 : Blo 523799 527795 := bstep (se 1 (by rfl) ⟨395846, by rfl⟩ : syracuseStep 527795 = 791693) B791693
theorem B789953 : Blo 523799 789953 := bstep (se 2 (by rfl) ⟨296232, by rfl⟩ : syracuseStep 789953 = 592465) B592465
theorem B888259 : Blo 523799 888259 := bstep (se 1 (by rfl) ⟨666194, by rfl⟩ : syracuseStep 888259 = 1332389) B1332389
theorem B593347 : Blo 523799 593347 := bstep (se 1 (by rfl) ⟨445010, by rfl⟩ : syracuseStep 593347 = 890021) B890021
theorem B789971 : Blo 523799 789971 := bstep (se 1 (by rfl) ⟨592478, by rfl⟩ : syracuseStep 789971 = 1184957) B1184957
theorem B790001 : Blo 523799 790001 := bstep (se 2 (by rfl) ⟨296250, by rfl⟩ : syracuseStep 790001 = 592501) B592501
theorem B790019 : Blo 523799 790019 := bstep (se 1 (by rfl) ⟨592514, by rfl⟩ : syracuseStep 790019 = 1185029) B1185029
theorem B790049 : Blo 523799 790049 := bstep (se 2 (by rfl) ⟨296268, by rfl⟩ : syracuseStep 790049 = 592537) B592537
theorem B1347121 : Blo 523799 1347121 := bstep (se 2 (by rfl) ⟨505170, by rfl⟩ : syracuseStep 1347121 = 1010341) B1010341
theorem B790067 : Blo 523799 790067 := bstep (se 1 (by rfl) ⟨592550, by rfl⟩ : syracuseStep 790067 = 1185101) B1185101
theorem B888401 : Blo 523799 888401 := bstep (se 2 (by rfl) ⟨333150, by rfl⟩ : syracuseStep 888401 = 666301) B666301
theorem B790097 : Blo 523799 790097 := bstep (se 2 (by rfl) ⟨296286, by rfl⟩ : syracuseStep 790097 = 592573) B592573
theorem B593491 : Blo 523799 593491 := bstep (se 1 (by rfl) ⟨445118, by rfl⟩ : syracuseStep 593491 = 890237) B890237
theorem B790115 : Blo 523799 790115 := bstep (se 1 (by rfl) ⟨592586, by rfl⟩ : syracuseStep 790115 = 1185173) B1185173
theorem B790145 : Blo 523799 790145 := bstep (se 2 (by rfl) ⟨296304, by rfl⟩ : syracuseStep 790145 = 592609) B592609
theorem B2657933 : Blo 523799 2657933 := bstep (se 3 (by rfl) ⟨498362, by rfl⟩ : syracuseStep 2657933 = 996725) B996725
theorem B1773197 : Blo 523799 1773197 := bstep (se 3 (by rfl) ⟨332474, by rfl⟩ : syracuseStep 1773197 = 664949) B664949
theorem B790163 : Blo 523799 790163 := bstep (se 1 (by rfl) ⟨592622, by rfl⟩ : syracuseStep 790163 = 1185245) B1185245
theorem B1183409 : Blo 523799 1183409 := bstep (se 2 (by rfl) ⟨443778, by rfl⟩ : syracuseStep 1183409 = 887557) B887557
theorem B790193 : Blo 523799 790193 := bstep (se 2 (by rfl) ⟨296322, by rfl⟩ : syracuseStep 790193 = 592645) B592645
theorem B1773251 : Blo 523799 1773251 := bstep (se 1 (by rfl) ⟨1329938, by rfl⟩ : syracuseStep 1773251 = 2659877) B2659877
theorem B1183427 : Blo 523799 1183427 := bstep (se 1 (by rfl) ⟨887570, by rfl⟩ : syracuseStep 1183427 = 1775141) B1775141
theorem B790211 : Blo 523799 790211 := bstep (se 1 (by rfl) ⟨592658, by rfl⟩ : syracuseStep 790211 = 1185317) B1185317
theorem B888529 : Blo 523799 888529 := bstep (se 2 (by rfl) ⟨333198, by rfl⟩ : syracuseStep 888529 = 666397) B666397
theorem B790241 : Blo 523799 790241 := bstep (se 2 (by rfl) ⟨296340, by rfl⟩ : syracuseStep 790241 = 592681) B592681
theorem B593635 : Blo 523799 593635 := bstep (se 1 (by rfl) ⟨445226, by rfl⟩ : syracuseStep 593635 = 890453) B890453
theorem B888563 : Blo 523799 888563 := bstep (se 1 (by rfl) ⟨666422, by rfl⟩ : syracuseStep 888563 = 1332845) B1332845
theorem B790259 : Blo 523799 790259 := bstep (se 1 (by rfl) ⟨592694, by rfl⟩ : syracuseStep 790259 = 1185389) B1185389
theorem B790289 : Blo 523799 790289 := bstep (se 2 (by rfl) ⟨296358, by rfl⟩ : syracuseStep 790289 = 592717) B592717
theorem B790307 : Blo 523799 790307 := bstep (se 1 (by rfl) ⟨592730, by rfl⟩ : syracuseStep 790307 = 1185461) B1185461
theorem B790337 : Blo 523799 790337 := bstep (se 2 (by rfl) ⟨296376, by rfl⟩ : syracuseStep 790337 = 592753) B592753
theorem B790355 : Blo 523799 790355 := bstep (se 1 (by rfl) ⟨592766, by rfl⟩ : syracuseStep 790355 = 1185533) B1185533
theorem B790385 : Blo 523799 790385 := bstep (se 2 (by rfl) ⟨296394, by rfl⟩ : syracuseStep 790385 = 592789) B592789
theorem B888691 : Blo 523799 888691 := bstep (se 1 (by rfl) ⟨666518, by rfl⟩ : syracuseStep 888691 = 1333037) B1333037
theorem B790403 : Blo 523799 790403 := bstep (se 1 (by rfl) ⟨592802, by rfl⟩ : syracuseStep 790403 = 1185605) B1185605
theorem B561043 : Blo 523799 561043 := bstep (se 1 (by rfl) ⟨420782, by rfl⟩ : syracuseStep 561043 = 841565) B841565
theorem B790433 : Blo 523799 790433 := bstep (se 2 (by rfl) ⟨296412, by rfl⟩ : syracuseStep 790433 = 592825) B592825
theorem B3379121 : Blo 523799 3379121 := bstep (se 2 (by rfl) ⟨1267170, by rfl⟩ : syracuseStep 3379121 = 2534341) B2534341
theorem B790451 : Blo 523799 790451 := bstep (se 1 (by rfl) ⟨592838, by rfl⟩ : syracuseStep 790451 = 1185677) B1185677
theorem B7573445 : Blo 523799 7573445 := bstep (se 4 (by rfl) ⟨710010, by rfl⟩ : syracuseStep 7573445 = 1420021) B1420021
theorem B11407301 : Blo 523799 11407301 := bstep (se 4 (by rfl) ⟨1069434, by rfl⟩ : syracuseStep 11407301 = 2138869) B2138869
theorem B1773521 : Blo 523799 1773521 := bstep (se 2 (by rfl) ⟨665070, by rfl⟩ : syracuseStep 1773521 = 1330141) B1330141
theorem B1183697 : Blo 523799 1183697 := bstep (se 2 (by rfl) ⟨443886, by rfl⟩ : syracuseStep 1183697 = 887773) B887773
theorem B790481 : Blo 523799 790481 := bstep (se 2 (by rfl) ⟨296430, by rfl⟩ : syracuseStep 790481 = 592861) B592861
theorem B1183715 : Blo 523799 1183715 := bstep (se 1 (by rfl) ⟨887786, by rfl⟩ : syracuseStep 1183715 = 1775573) B1775573
theorem B790499 : Blo 523799 790499 := bstep (se 1 (by rfl) ⟨592874, by rfl⟩ : syracuseStep 790499 = 1185749) B1185749
theorem B888833 : Blo 523799 888833 := bstep (se 2 (by rfl) ⟨333312, by rfl⟩ : syracuseStep 888833 = 666625) B666625
theorem B790529 : Blo 523799 790529 := bstep (se 2 (by rfl) ⟨296448, by rfl⟩ : syracuseStep 790529 = 592897) B592897
theorem B790547 : Blo 523799 790547 := bstep (se 1 (by rfl) ⟨592910, by rfl⟩ : syracuseStep 790547 = 1185821) B1185821
theorem B790577 : Blo 523799 790577 := bstep (se 2 (by rfl) ⟨296466, by rfl⟩ : syracuseStep 790577 = 592933) B592933
theorem B790595 : Blo 523799 790595 := bstep (se 1 (by rfl) ⟨592946, by rfl⟩ : syracuseStep 790595 = 1185893) B1185893
theorem B790625 : Blo 523799 790625 := bstep (se 2 (by rfl) ⟨296484, by rfl⟩ : syracuseStep 790625 = 592969) B592969
theorem B790643 : Blo 523799 790643 := bstep (se 1 (by rfl) ⟨592982, by rfl⟩ : syracuseStep 790643 = 1185965) B1185965
theorem B888961 : Blo 523799 888961 := bstep (se 2 (by rfl) ⟨333360, by rfl⟩ : syracuseStep 888961 = 666721) B666721
theorem B790673 : Blo 523799 790673 := bstep (se 2 (by rfl) ⟨296502, by rfl⟩ : syracuseStep 790673 = 593005) B593005
theorem B888995 : Blo 523799 888995 := bstep (se 1 (by rfl) ⟨666746, by rfl⟩ : syracuseStep 888995 = 1333493) B1333493
theorem B790691 : Blo 523799 790691 := bstep (se 1 (by rfl) ⟨593018, by rfl⟩ : syracuseStep 790691 = 1186037) B1186037
theorem B790721 : Blo 523799 790721 := bstep (se 2 (by rfl) ⟨296520, by rfl⟩ : syracuseStep 790721 = 593041) B593041
theorem B790739 : Blo 523799 790739 := bstep (se 1 (by rfl) ⟨593054, by rfl⟩ : syracuseStep 790739 = 1186109) B1186109
theorem B1183985 : Blo 523799 1183985 := bstep (se 2 (by rfl) ⟨443994, by rfl⟩ : syracuseStep 1183985 = 887989) B887989
theorem B790769 : Blo 523799 790769 := bstep (se 2 (by rfl) ⟨296538, by rfl⟩ : syracuseStep 790769 = 593077) B593077
theorem B1184003 : Blo 523799 1184003 := bstep (se 1 (by rfl) ⟨888002, by rfl⟩ : syracuseStep 1184003 = 1776005) B1776005
theorem B790787 : Blo 523799 790787 := bstep (se 1 (by rfl) ⟨593090, by rfl⟩ : syracuseStep 790787 = 1186181) B1186181
theorem B790817 : Blo 523799 790817 := bstep (se 2 (by rfl) ⟨296556, by rfl⟩ : syracuseStep 790817 = 593113) B593113
theorem B889123 : Blo 523799 889123 := bstep (se 1 (by rfl) ⟨666842, by rfl⟩ : syracuseStep 889123 = 1333685) B1333685
theorem B790835 : Blo 523799 790835 := bstep (se 1 (by rfl) ⟨593126, by rfl⟩ : syracuseStep 790835 = 1186253) B1186253
theorem B790865 : Blo 523799 790865 := bstep (se 2 (by rfl) ⟨296574, by rfl⟩ : syracuseStep 790865 = 593149) B593149
theorem B790883 : Blo 523799 790883 := bstep (se 1 (by rfl) ⟨593162, by rfl⟩ : syracuseStep 790883 = 1186325) B1186325
theorem B790913 : Blo 523799 790913 := bstep (se 2 (by rfl) ⟨296592, by rfl⟩ : syracuseStep 790913 = 593185) B593185
theorem B790931 : Blo 523799 790931 := bstep (se 1 (by rfl) ⟨593198, by rfl⟩ : syracuseStep 790931 = 1186397) B1186397
theorem B889265 : Blo 523799 889265 := bstep (se 2 (by rfl) ⟨333474, by rfl⟩ : syracuseStep 889265 = 666949) B666949
theorem B790961 : Blo 523799 790961 := bstep (se 2 (by rfl) ⟨296610, by rfl⟩ : syracuseStep 790961 = 593221) B593221
theorem B790979 : Blo 523799 790979 := bstep (se 1 (by rfl) ⟨593234, by rfl⟩ : syracuseStep 790979 = 1186469) B1186469
theorem B791009 : Blo 523799 791009 := bstep (se 2 (by rfl) ⟨296628, by rfl⟩ : syracuseStep 791009 = 593257) B593257
theorem B1774061 : Blo 523799 1774061 := bstep (se 3 (by rfl) ⟨332636, by rfl⟩ : syracuseStep 1774061 = 665273) B665273
theorem B791027 : Blo 523799 791027 := bstep (se 1 (by rfl) ⟨593270, by rfl⟩ : syracuseStep 791027 = 1186541) B1186541
theorem B1184273 : Blo 523799 1184273 := bstep (se 2 (by rfl) ⟨444102, by rfl⟩ : syracuseStep 1184273 = 888205) B888205
theorem B791057 : Blo 523799 791057 := bstep (se 2 (by rfl) ⟨296646, by rfl⟩ : syracuseStep 791057 = 593293) B593293
theorem B1774115 : Blo 523799 1774115 := bstep (se 1 (by rfl) ⟨1330586, by rfl⟩ : syracuseStep 1774115 = 2661173) B2661173
theorem B1184291 : Blo 523799 1184291 := bstep (se 1 (by rfl) ⟨888218, by rfl⟩ : syracuseStep 1184291 = 1776437) B1776437
theorem B791075 : Blo 523799 791075 := bstep (se 1 (by rfl) ⟨593306, by rfl⟩ : syracuseStep 791075 = 1186613) B1186613
theorem B889393 : Blo 523799 889393 := bstep (se 2 (by rfl) ⟨333522, by rfl⟩ : syracuseStep 889393 = 667045) B667045
theorem B791105 : Blo 523799 791105 := bstep (se 2 (by rfl) ⟨296664, by rfl⟩ : syracuseStep 791105 = 593329) B593329
theorem B889427 : Blo 523799 889427 := bstep (se 1 (by rfl) ⟨667070, by rfl⟩ : syracuseStep 889427 = 1334141) B1334141
theorem B791123 : Blo 523799 791123 := bstep (se 1 (by rfl) ⟨593342, by rfl⟩ : syracuseStep 791123 = 1186685) B1186685
theorem B791153 : Blo 523799 791153 := bstep (se 2 (by rfl) ⟨296682, by rfl⟩ : syracuseStep 791153 = 593365) B593365
theorem B791171 : Blo 523799 791171 := bstep (se 1 (by rfl) ⟨593378, by rfl⟩ : syracuseStep 791171 = 1186757) B1186757
theorem B791201 : Blo 523799 791201 := bstep (se 2 (by rfl) ⟨296700, by rfl⟩ : syracuseStep 791201 = 593401) B593401
theorem B791219 : Blo 523799 791219 := bstep (se 1 (by rfl) ⟨593414, by rfl⟩ : syracuseStep 791219 = 1186829) B1186829
theorem B791249 : Blo 523799 791249 := bstep (se 2 (by rfl) ⟨296718, by rfl⟩ : syracuseStep 791249 = 593437) B593437
theorem B889555 : Blo 523799 889555 := bstep (se 1 (by rfl) ⟨667166, by rfl⟩ : syracuseStep 889555 = 1334333) B1334333
theorem B791267 : Blo 523799 791267 := bstep (se 1 (by rfl) ⟨593450, by rfl⟩ : syracuseStep 791267 = 1186901) B1186901
theorem B791297 : Blo 523799 791297 := bstep (se 2 (by rfl) ⟨296736, by rfl⟩ : syracuseStep 791297 = 593473) B593473
theorem B791315 : Blo 523799 791315 := bstep (se 1 (by rfl) ⟨593486, by rfl⟩ : syracuseStep 791315 = 1186973) B1186973
theorem B1774385 : Blo 523799 1774385 := bstep (se 2 (by rfl) ⟨665394, by rfl⟩ : syracuseStep 1774385 = 1330789) B1330789
theorem B1184561 : Blo 523799 1184561 := bstep (se 2 (by rfl) ⟨444210, by rfl⟩ : syracuseStep 1184561 = 888421) B888421
theorem B791345 : Blo 523799 791345 := bstep (se 2 (by rfl) ⟨296754, by rfl⟩ : syracuseStep 791345 = 593509) B593509
theorem B1184579 : Blo 523799 1184579 := bstep (se 1 (by rfl) ⟨888434, by rfl⟩ : syracuseStep 1184579 = 1776869) B1776869
theorem B791363 : Blo 523799 791363 := bstep (se 1 (by rfl) ⟨593522, by rfl⟩ : syracuseStep 791363 = 1187045) B1187045
theorem B4494149 : Blo 523799 4494149 := bstep (se 4 (by rfl) ⟨421326, by rfl⟩ : syracuseStep 4494149 = 842653) B842653
theorem B889697 : Blo 523799 889697 := bstep (se 2 (by rfl) ⟨333636, by rfl⟩ : syracuseStep 889697 = 667273) B667273
theorem B791393 : Blo 523799 791393 := bstep (se 2 (by rfl) ⟨296772, by rfl⟩ : syracuseStep 791393 = 593545) B593545
theorem B791411 : Blo 523799 791411 := bstep (se 1 (by rfl) ⟨593558, by rfl⟩ : syracuseStep 791411 = 1187117) B1187117
theorem B791441 : Blo 523799 791441 := bstep (se 2 (by rfl) ⟨296790, by rfl⟩ : syracuseStep 791441 = 593581) B593581
theorem B791459 : Blo 523799 791459 := bstep (se 1 (by rfl) ⟨593594, by rfl⟩ : syracuseStep 791459 = 1187189) B1187189
theorem B791489 : Blo 523799 791489 := bstep (se 2 (by rfl) ⟨296808, by rfl⟩ : syracuseStep 791489 = 593617) B593617
theorem B791507 : Blo 523799 791507 := bstep (se 1 (by rfl) ⟨593630, by rfl⟩ : syracuseStep 791507 = 1187261) B1187261
theorem B889825 : Blo 523799 889825 := bstep (se 2 (by rfl) ⟨333684, by rfl⟩ : syracuseStep 889825 = 667369) B667369
theorem B791537 : Blo 523799 791537 := bstep (se 2 (by rfl) ⟨296826, by rfl⟩ : syracuseStep 791537 = 593653) B593653
theorem B889859 : Blo 523799 889859 := bstep (se 1 (by rfl) ⟨667394, by rfl⟩ : syracuseStep 889859 = 1334789) B1334789
theorem B791555 : Blo 523799 791555 := bstep (se 1 (by rfl) ⟨593666, by rfl⟩ : syracuseStep 791555 = 1187333) B1187333
theorem B2692109 : Blo 523799 2692109 := bstep (se 3 (by rfl) ⟨504770, by rfl⟩ : syracuseStep 2692109 = 1009541) B1009541
theorem B791585 : Blo 523799 791585 := bstep (se 2 (by rfl) ⟨296844, by rfl⟩ : syracuseStep 791585 = 593689) B593689
theorem B791603 : Blo 523799 791603 := bstep (se 1 (by rfl) ⟨593702, by rfl⟩ : syracuseStep 791603 = 1187405) B1187405
theorem B2987077 : Blo 523799 2987077 := bstep (se 4 (by rfl) ⟨280038, by rfl⟩ : syracuseStep 2987077 = 560077) B560077
theorem B1184849 : Blo 523799 1184849 := bstep (se 2 (by rfl) ⟨444318, by rfl⟩ : syracuseStep 1184849 = 888637) B888637
theorem B791633 : Blo 523799 791633 := bstep (se 2 (by rfl) ⟨296862, by rfl⟩ : syracuseStep 791633 = 593725) B593725
theorem B1184867 : Blo 523799 1184867 := bstep (se 1 (by rfl) ⟨888650, by rfl⟩ : syracuseStep 1184867 = 1777301) B1777301
theorem B791651 : Blo 523799 791651 := bstep (se 1 (by rfl) ⟨593738, by rfl⟩ : syracuseStep 791651 = 1187477) B1187477
theorem B791681 : Blo 523799 791681 := bstep (se 2 (by rfl) ⟨296880, by rfl⟩ : syracuseStep 791681 = 593761) B593761
theorem B562307 : Blo 523799 562307 := bstep (se 1 (by rfl) ⟨421730, by rfl⟩ : syracuseStep 562307 = 843461) B843461
theorem B889987 : Blo 523799 889987 := bstep (se 1 (by rfl) ⟨667490, by rfl⟩ : syracuseStep 889987 = 1334981) B1334981
theorem B791699 : Blo 523799 791699 := bstep (se 1 (by rfl) ⟨593774, by rfl⟩ : syracuseStep 791699 = 1187549) B1187549
theorem B1119395 : Blo 523799 1119395 := bstep (se 1 (by rfl) ⟨839546, by rfl⟩ : syracuseStep 1119395 = 1679093) B1679093
theorem B890129 : Blo 523799 890129 := bstep (se 2 (by rfl) ⟨333798, by rfl⟩ : syracuseStep 890129 = 667597) B667597
theorem B1774925 : Blo 523799 1774925 := bstep (se 3 (by rfl) ⟨332798, by rfl⟩ : syracuseStep 1774925 = 665597) B665597
theorem B1185137 : Blo 523799 1185137 := bstep (se 2 (by rfl) ⟨444426, by rfl⟩ : syracuseStep 1185137 = 888853) B888853
theorem B1774979 : Blo 523799 1774979 := bstep (se 1 (by rfl) ⟨1331234, by rfl⟩ : syracuseStep 1774979 = 2662469) B2662469
theorem B1185155 : Blo 523799 1185155 := bstep (se 1 (by rfl) ⟨888866, by rfl⟩ : syracuseStep 1185155 = 1777733) B1777733
theorem B890257 : Blo 523799 890257 := bstep (se 2 (by rfl) ⟨333846, by rfl⟩ : syracuseStep 890257 = 667693) B667693
theorem B890291 : Blo 523799 890291 := bstep (se 1 (by rfl) ⟨667718, by rfl⟩ : syracuseStep 890291 = 1335437) B1335437
theorem B890419 : Blo 523799 890419 := bstep (se 1 (by rfl) ⟨667814, by rfl⟩ : syracuseStep 890419 = 1335629) B1335629
theorem B2692721 : Blo 523799 2692721 := bstep (se 2 (by rfl) ⟨1009770, by rfl⟩ : syracuseStep 2692721 = 2019541) B2019541
theorem B3282565 : Blo 523799 3282565 := bstep (se 4 (by rfl) ⟨307740, by rfl⟩ : syracuseStep 3282565 = 615481) B615481
theorem B1775249 : Blo 523799 1775249 := bstep (se 2 (by rfl) ⟨665718, by rfl⟩ : syracuseStep 1775249 = 1331437) B1331437
theorem B1185425 : Blo 523799 1185425 := bstep (se 2 (by rfl) ⟨444534, by rfl⟩ : syracuseStep 1185425 = 889069) B889069
theorem B1185443 : Blo 523799 1185443 := bstep (se 1 (by rfl) ⟨889082, by rfl⟩ : syracuseStep 1185443 = 1778165) B1778165
theorem B890561 : Blo 523799 890561 := bstep (se 2 (by rfl) ⟨333960, by rfl⟩ : syracuseStep 890561 = 667921) B667921
theorem B563059 : Blo 523799 563059 := bstep (se 1 (by rfl) ⟨422294, by rfl⟩ : syracuseStep 563059 = 844589) B844589
theorem B1185713 : Blo 523799 1185713 := bstep (se 2 (by rfl) ⟨444642, by rfl⟩ : syracuseStep 1185713 = 889285) B889285
theorem B1185731 : Blo 523799 1185731 := bstep (se 1 (by rfl) ⟨889298, by rfl⟩ : syracuseStep 1185731 = 1778597) B1778597
theorem B2529251 : Blo 523799 2529251 := bstep (se 1 (by rfl) ⟨1896938, by rfl⟩ : syracuseStep 2529251 = 3793877) B3793877
theorem B1022051 : Blo 523799 1022051 := bstep (se 1 (by rfl) ⟨766538, by rfl⟩ : syracuseStep 1022051 = 1533077) B1533077
theorem B2398349 : Blo 523799 2398349 := bstep (se 3 (by rfl) ⟨449690, by rfl⟩ : syracuseStep 2398349 = 899381) B899381
theorem B1775789 : Blo 523799 1775789 := bstep (se 3 (by rfl) ⟨332960, by rfl⟩ : syracuseStep 1775789 = 665921) B665921
theorem B1513667 : Blo 523799 1513667 := bstep (se 1 (by rfl) ⟨1135250, by rfl⟩ : syracuseStep 1513667 = 2270501) B2270501
theorem B1186001 : Blo 523799 1186001 := bstep (se 2 (by rfl) ⟨444750, by rfl⟩ : syracuseStep 1186001 = 889501) B889501
theorem B1775843 : Blo 523799 1775843 := bstep (se 1 (by rfl) ⟨1331882, by rfl⟩ : syracuseStep 1775843 = 2663765) B2663765
theorem B1186019 : Blo 523799 1186019 := bstep (se 1 (by rfl) ⟨889514, by rfl⟩ : syracuseStep 1186019 = 1779029) B1779029
theorem B25663715 : Blo 523799 25663715 := bstep (se 1 (by rfl) ⟨19247786, by rfl⟩ : syracuseStep 25663715 = 38495573) B38495573
theorem B3381581 : Blo 523799 3381581 := bstep (se 3 (by rfl) ⟨634046, by rfl⟩ : syracuseStep 3381581 = 1268093) B1268093
theorem B1120625 : Blo 523799 1120625 := bstep (se 2 (by rfl) ⟨420234, by rfl⟩ : syracuseStep 1120625 = 840469) B840469
theorem B2660849 : Blo 523799 2660849 := bstep (se 2 (by rfl) ⟨997818, by rfl⟩ : syracuseStep 2660849 = 1995637) B1995637
theorem B1776113 : Blo 523799 1776113 := bstep (se 2 (by rfl) ⟨666042, by rfl⟩ : syracuseStep 1776113 = 1332085) B1332085
theorem B1186289 : Blo 523799 1186289 := bstep (se 2 (by rfl) ⟨444858, by rfl⟩ : syracuseStep 1186289 = 889717) B889717
theorem B1186307 : Blo 523799 1186307 := bstep (se 1 (by rfl) ⟨889730, by rfl⟩ : syracuseStep 1186307 = 1779461) B1779461
theorem B2529805 : Blo 523799 2529805 := bstep (se 3 (by rfl) ⟨474338, by rfl⟩ : syracuseStep 2529805 = 948677) B948677
theorem B629299 : Blo 523799 629299 := bstep (se 1 (by rfl) ⟨471974, by rfl⟩ : syracuseStep 629299 = 943949) B943949
theorem B1186577 : Blo 523799 1186577 := bstep (se 2 (by rfl) ⟨444966, by rfl⟩ : syracuseStep 1186577 = 889933) B889933
theorem B1186595 : Blo 523799 1186595 := bstep (se 1 (by rfl) ⟨889946, by rfl⟩ : syracuseStep 1186595 = 1779893) B1779893
theorem B2989061 : Blo 523799 2989061 := bstep (se 4 (by rfl) ⟨280224, by rfl⟩ : syracuseStep 2989061 = 560449) B560449
theorem B1776653 : Blo 523799 1776653 := bstep (se 3 (by rfl) ⟨333122, by rfl⟩ : syracuseStep 1776653 = 666245) B666245
theorem B1186865 : Blo 523799 1186865 := bstep (se 2 (by rfl) ⟨445074, by rfl⟩ : syracuseStep 1186865 = 890149) B890149
theorem B1776707 : Blo 523799 1776707 := bstep (se 1 (by rfl) ⟨1332530, by rfl⟩ : syracuseStep 1776707 = 2665061) B2665061
theorem B1186883 : Blo 523799 1186883 := bstep (se 1 (by rfl) ⟨890162, by rfl⟩ : syracuseStep 1186883 = 1780325) B1780325
theorem B1678477 : Blo 523799 1678477 := bstep (se 3 (by rfl) ⟨314714, by rfl⟩ : syracuseStep 1678477 = 629429) B629429
theorem B1121521 : Blo 523799 1121521 := bstep (se 2 (by rfl) ⟨420570, by rfl⟩ : syracuseStep 1121521 = 841141) B841141
theorem B1121539 : Blo 523799 1121539 := bstep (se 1 (by rfl) ⟨841154, by rfl⟩ : syracuseStep 1121539 = 1682309) B1682309
theorem B1776977 : Blo 523799 1776977 := bstep (se 2 (by rfl) ⟨666366, by rfl⟩ : syracuseStep 1776977 = 1332733) B1332733
theorem B1187153 : Blo 523799 1187153 := bstep (se 2 (by rfl) ⟨445182, by rfl⟩ : syracuseStep 1187153 = 890365) B890365
theorem B1187171 : Blo 523799 1187171 := bstep (se 1 (by rfl) ⟨890378, by rfl⟩ : syracuseStep 1187171 = 1780757) B1780757
theorem B662995 : Blo 523799 662995 := bstep (se 1 (by rfl) ⟨497246, by rfl⟩ : syracuseStep 662995 = 994493) B994493
theorem B1187441 : Blo 523799 1187441 := bstep (se 2 (by rfl) ⟨445290, by rfl⟩ : syracuseStep 1187441 = 890581) B890581
theorem B1187459 : Blo 523799 1187459 := bstep (se 1 (by rfl) ⟨890594, by rfl⟩ : syracuseStep 1187459 = 1781189) B1781189
theorem B1777517 : Blo 523799 1777517 := bstep (se 3 (by rfl) ⟨333284, by rfl⟩ : syracuseStep 1777517 = 666569) B666569
theorem B1515395 : Blo 523799 1515395 := bstep (se 1 (by rfl) ⟨1136546, by rfl⟩ : syracuseStep 1515395 = 2273093) B2273093
theorem B1777571 : Blo 523799 1777571 := bstep (se 1 (by rfl) ⟨1333178, by rfl⟩ : syracuseStep 1777571 = 2666357) B2666357
theorem B2662307 : Blo 523799 2662307 := bstep (se 1 (by rfl) ⟨1996730, by rfl⟩ : syracuseStep 2662307 = 3993461) B3993461
theorem B2531249 : Blo 523799 2531249 := bstep (se 2 (by rfl) ⟨949218, by rfl⟩ : syracuseStep 2531249 = 1898437) B1898437
theorem B663491 : Blo 523799 663491 := bstep (se 1 (by rfl) ⟨497618, by rfl⟩ : syracuseStep 663491 = 995237) B995237
theorem B1679309 : Blo 523799 1679309 := bstep (se 3 (by rfl) ⟨314870, by rfl⟩ : syracuseStep 1679309 = 629741) B629741
theorem B1417169 : Blo 523799 1417169 := bstep (se 2 (by rfl) ⟨531438, by rfl⟩ : syracuseStep 1417169 = 1062877) B1062877
theorem B598051 : Blo 523799 598051 := bstep (se 1 (by rfl) ⟨448538, by rfl⟩ : syracuseStep 598051 = 897077) B897077
theorem B5480561 : Blo 523799 5480561 := bstep (se 2 (by rfl) ⟨2055210, by rfl⟩ : syracuseStep 5480561 = 4110421) B4110421
theorem B1777841 : Blo 523799 1777841 := bstep (se 2 (by rfl) ⟨666690, by rfl⟩ : syracuseStep 1777841 = 1333381) B1333381
theorem B9248995 : Blo 523799 9248995 := bstep (se 1 (by rfl) ⟨6936746, by rfl⟩ : syracuseStep 9248995 = 13873493) B13873493
theorem B13476293 : Blo 523799 13476293 := bstep (se 4 (by rfl) ⟨1263402, by rfl⟩ : syracuseStep 13476293 = 2526805) B2526805
theorem B664195 : Blo 523799 664195 := bstep (se 1 (by rfl) ⟨498146, by rfl⟩ : syracuseStep 664195 = 996293) B996293
theorem B2663117 : Blo 523799 2663117 := bstep (se 3 (by rfl) ⟨499334, by rfl⟩ : syracuseStep 2663117 = 998669) B998669
theorem B1778381 : Blo 523799 1778381 := bstep (se 3 (by rfl) ⟨333446, by rfl⟩ : syracuseStep 1778381 = 666893) B666893
theorem B664291 : Blo 523799 664291 := bstep (se 1 (by rfl) ⟨498218, by rfl⟩ : syracuseStep 664291 = 996437) B996437
theorem B1778435 : Blo 523799 1778435 := bstep (se 1 (by rfl) ⟨1333826, by rfl⟩ : syracuseStep 1778435 = 2667653) B2667653
theorem B8528753 : Blo 523799 8528753 := bstep (se 2 (by rfl) ⟨3198282, by rfl⟩ : syracuseStep 8528753 = 6396565) B6396565
theorem B1778705 : Blo 523799 1778705 := bstep (se 2 (by rfl) ⟨667014, by rfl⟩ : syracuseStep 1778705 = 1334029) B1334029
theorem B664787 : Blo 523799 664787 := bstep (se 1 (by rfl) ⟨498590, by rfl⟩ : syracuseStep 664787 = 997181) B997181
theorem B20194757 : Blo 523799 20194757 := bstep (se 4 (by rfl) ⟨1893258, by rfl⟩ : syracuseStep 20194757 = 3786517) B3786517
theorem B1123811 : Blo 523799 1123811 := bstep (se 1 (by rfl) ⟨842858, by rfl⟩ : syracuseStep 1123811 = 1685717) B1685717
theorem B1779245 : Blo 523799 1779245 := bstep (se 3 (by rfl) ⟨333608, by rfl⟩ : syracuseStep 1779245 = 667217) B667217
theorem B2532941 : Blo 523799 2532941 := bstep (se 3 (by rfl) ⟨474926, by rfl⟩ : syracuseStep 2532941 = 949853) B949853
theorem B1779299 : Blo 523799 1779299 := bstep (se 1 (by rfl) ⟨1334474, by rfl⟩ : syracuseStep 1779299 = 2668949) B2668949
theorem B1779569 : Blo 523799 1779569 := bstep (se 2 (by rfl) ⟨667338, by rfl⟩ : syracuseStep 1779569 = 1334677) B1334677
theorem B665491 : Blo 523799 665491 := bstep (se 1 (by rfl) ⟨499118, by rfl⟩ : syracuseStep 665491 = 998237) B998237
theorem B1124273 : Blo 523799 1124273 := bstep (se 2 (by rfl) ⟨421602, by rfl⟩ : syracuseStep 1124273 = 843205) B843205
theorem B1419245 : Blo 523799 1419245 := bstep (se 3 (by rfl) ⟨266108, by rfl⟩ : syracuseStep 1419245 = 532217) B532217
theorem B665587 : Blo 523799 665587 := bstep (se 1 (by rfl) ⟨499190, by rfl⟩ : syracuseStep 665587 = 998381) B998381
theorem B1681411 : Blo 523799 1681411 := bstep (se 1 (by rfl) ⟨1261058, by rfl⟩ : syracuseStep 1681411 = 2522117) B2522117
theorem B1681553 : Blo 523799 1681553 := bstep (se 2 (by rfl) ⟨630582, by rfl⟩ : syracuseStep 1681553 = 1261165) B1261165
theorem B633043 : Blo 523799 633043 := bstep (se 1 (by rfl) ⟨474782, by rfl⟩ : syracuseStep 633043 = 949565) B949565
theorem B3189041 : Blo 523799 3189041 := bstep (se 2 (by rfl) ⟨1195890, by rfl⟩ : syracuseStep 3189041 = 2391781) B2391781
theorem B3189091 : Blo 523799 3189091 := bstep (se 1 (by rfl) ⟨2391818, by rfl⟩ : syracuseStep 3189091 = 4783637) B4783637
theorem B1780109 : Blo 523799 1780109 := bstep (se 3 (by rfl) ⟨333770, by rfl⟩ : syracuseStep 1780109 = 667541) B667541
theorem B1780163 : Blo 523799 1780163 := bstep (se 1 (by rfl) ⟨1335122, by rfl⟩ : syracuseStep 1780163 = 2670245) B2670245
theorem B666083 : Blo 523799 666083 := bstep (se 1 (by rfl) ⟨499562, by rfl⟩ : syracuseStep 666083 = 999125) B999125
theorem B6728305 : Blo 523799 6728305 := bstep (se 2 (by rfl) ⟨2523114, by rfl⟩ : syracuseStep 6728305 = 5046229) B5046229
theorem B3418787 : Blo 523799 3418787 := bstep (se 1 (by rfl) ⟨2564090, by rfl⟩ : syracuseStep 3418787 = 5128181) B5128181
theorem B1780433 : Blo 523799 1780433 := bstep (se 2 (by rfl) ⟨667662, by rfl⟩ : syracuseStep 1780433 = 1335325) B1335325
theorem B7383821 : Blo 523799 7383821 := bstep (se 3 (by rfl) ⟨1384466, by rfl⟩ : syracuseStep 7383821 = 2768933) B2768933
theorem B2992909 : Blo 523799 2992909 := bstep (se 3 (by rfl) ⟨561170, by rfl⟩ : syracuseStep 2992909 = 1122341) B1122341
theorem B5974883 : Blo 523799 5974883 := bstep (se 1 (by rfl) ⟨4481162, by rfl⟩ : syracuseStep 5974883 = 8962325) B8962325
theorem B1420195 : Blo 523799 1420195 := bstep (se 1 (by rfl) ⟨1065146, by rfl⟩ : syracuseStep 1420195 = 2130293) B2130293
theorem B666787 : Blo 523799 666787 := bstep (se 1 (by rfl) ⟨500090, by rfl⟩ : syracuseStep 666787 = 1000181) B1000181
theorem B1125571 : Blo 523799 1125571 := bstep (se 1 (by rfl) ⟨844178, by rfl⟩ : syracuseStep 1125571 = 1688357) B1688357
theorem B994531 : Blo 523799 994531 := bstep (se 1 (by rfl) ⟨745898, by rfl⟩ : syracuseStep 994531 = 1491797) B1491797
theorem B1780973 : Blo 523799 1780973 := bstep (se 3 (by rfl) ⟨333932, by rfl⟩ : syracuseStep 1780973 = 667865) B667865
theorem B666883 : Blo 523799 666883 := bstep (se 1 (by rfl) ⟨500162, by rfl⟩ : syracuseStep 666883 = 1000325) B1000325
theorem B1781027 : Blo 523799 1781027 := bstep (se 1 (by rfl) ⟨1335770, by rfl⟩ : syracuseStep 1781027 = 2671541) B2671541
theorem B896369 : Blo 523799 896369 := bstep (se 2 (by rfl) ⟨336138, by rfl⟩ : syracuseStep 896369 = 672277) B672277
theorem B1125827 : Blo 523799 1125827 := bstep (se 1 (by rfl) ⟨844370, by rfl⟩ : syracuseStep 1125827 = 1688741) B1688741
theorem B2666033 : Blo 523799 2666033 := bstep (se 2 (by rfl) ⟨999762, by rfl⟩ : syracuseStep 2666033 = 1999525) B1999525
theorem B1781297 : Blo 523799 1781297 := bstep (se 2 (by rfl) ⟨667986, by rfl⟩ : syracuseStep 1781297 = 1335973) B1335973
theorem B994979 : Blo 523799 994979 := bstep (se 1 (by rfl) ⟨746234, by rfl⟩ : syracuseStep 994979 = 1492469) B1492469
theorem B5746403 : Blo 523799 5746403 := bstep (se 1 (by rfl) ⟨4309802, by rfl⟩ : syracuseStep 5746403 = 8619605) B8619605
theorem B667379 : Blo 523799 667379 := bstep (se 1 (by rfl) ⟨500534, by rfl⟩ : syracuseStep 667379 = 1001069) B1001069
theorem B1421069 : Blo 523799 1421069 := bstep (se 3 (by rfl) ⟨266450, by rfl⟩ : syracuseStep 1421069 = 532901) B532901
theorem B1748803 : Blo 523799 1748803 := bstep (se 1 (by rfl) ⟨1311602, by rfl⟩ : syracuseStep 1748803 = 2623205) B2623205
theorem B1421201 : Blo 523799 1421201 := bstep (se 2 (by rfl) ⟨532950, by rfl⟩ : syracuseStep 1421201 = 1065901) B1065901
theorem B995267 : Blo 523799 995267 := bstep (se 1 (by rfl) ⟨746450, by rfl⟩ : syracuseStep 995267 = 1492901) B1492901
theorem B799073 : Blo 523799 799073 := bstep (se 2 (by rfl) ⟨299652, by rfl⟩ : syracuseStep 799073 = 599305) B599305
theorem B1126801 : Blo 523799 1126801 := bstep (se 2 (by rfl) ⟨422550, by rfl⟩ : syracuseStep 1126801 = 845101) B845101
theorem B1683949 : Blo 523799 1683949 := bstep (se 3 (by rfl) ⟨315740, by rfl⟩ : syracuseStep 1683949 = 631481) B631481
theorem B7582261 : Blo 523799 7582261 := bstep (se 5 (by rfl) ⟨355418, by rfl⟩ : syracuseStep 7582261 = 710837) B710837
theorem B766561 : Blo 523799 766561 := bstep (se 2 (by rfl) ⟨287460, by rfl⟩ : syracuseStep 766561 = 574921) B574921
theorem B4502213 : Blo 523799 4502213 := bstep (se 4 (by rfl) ⟨422082, by rfl⟩ : syracuseStep 4502213 = 844165) B844165
theorem B2994893 : Blo 523799 2994893 := bstep (se 3 (by rfl) ⟨561542, by rfl⟩ : syracuseStep 2994893 = 1123085) B1123085
theorem B2241265 : Blo 523799 2241265 := bstep (se 2 (by rfl) ⟨840474, by rfl⟩ : syracuseStep 2241265 = 1680949) B1680949
theorem B996209 : Blo 523799 996209 := bstep (se 2 (by rfl) ⟨373578, by rfl⟩ : syracuseStep 996209 = 747157) B747157
theorem B3191665 : Blo 523799 3191665 := bstep (se 2 (by rfl) ⟨1196874, by rfl⟩ : syracuseStep 3191665 = 2393749) B2393749
theorem B2667491 : Blo 523799 2667491 := bstep (se 1 (by rfl) ⟨2000618, by rfl⟩ : syracuseStep 2667491 = 4001237) B4001237
theorem B5682545 : Blo 523799 5682545 := bstep (se 2 (by rfl) ⟨2130954, by rfl⟩ : syracuseStep 5682545 = 4261909) B4261909
theorem B4502897 : Blo 523799 4502897 := bstep (se 2 (by rfl) ⟨1688586, by rfl⟩ : syracuseStep 4502897 = 3377173) B3377173
theorem B800131 : Blo 523799 800131 := bstep (se 1 (by rfl) ⟨600098, by rfl⟩ : syracuseStep 800131 = 1200197) B1200197
theorem B2995825 : Blo 523799 2995825 := bstep (se 2 (by rfl) ⟨1123434, by rfl⟩ : syracuseStep 2995825 = 2246869) B2246869
theorem B2733709 : Blo 523799 2733709 := bstep (se 3 (by rfl) ⟨512570, by rfl⟩ : syracuseStep 2733709 = 1025141) B1025141
theorem B800417 : Blo 523799 800417 := bstep (se 2 (by rfl) ⟨300156, by rfl⟩ : syracuseStep 800417 = 600313) B600313
theorem B997105 : Blo 523799 997105 := bstep (se 2 (by rfl) ⟨373914, by rfl⟩ : syracuseStep 997105 = 747829) B747829
theorem B2668301 : Blo 523799 2668301 := bstep (se 3 (by rfl) ⟨500306, by rfl⟩ : syracuseStep 2668301 = 1000613) B1000613
theorem B997265 : Blo 523799 997265 := bstep (se 2 (by rfl) ⟨373974, by rfl⟩ : syracuseStep 997265 = 747949) B747949
theorem B1423277 : Blo 523799 1423277 := bstep (se 3 (by rfl) ⟨266864, by rfl⟩ : syracuseStep 1423277 = 533729) B533729
theorem B1620109 : Blo 523799 1620109 := bstep (se 3 (by rfl) ⟨303770, by rfl⟩ : syracuseStep 1620109 = 607541) B607541
theorem B997667 : Blo 523799 997667 := bstep (se 1 (by rfl) ⟨748250, by rfl⟩ : syracuseStep 997667 = 1496501) B1496501
theorem B3356977 : Blo 523799 3356977 := bstep (se 2 (by rfl) ⟨1258866, by rfl⟩ : syracuseStep 3356977 = 2517733) B2517733
theorem B2406797 : Blo 523799 2406797 := bstep (se 3 (by rfl) ⟨451274, by rfl⟩ : syracuseStep 2406797 = 902549) B902549
theorem B6011333 : Blo 523799 6011333 := bstep (se 4 (by rfl) ⟨563562, by rfl⟩ : syracuseStep 6011333 = 1127125) B1127125
theorem B1063459 : Blo 523799 1063459 := bstep (se 1 (by rfl) ⟨797594, by rfl⟩ : syracuseStep 1063459 = 1595189) B1595189
theorem B2997283 : Blo 523799 2997283 := bstep (se 1 (by rfl) ⟨2247962, by rfl⟩ : syracuseStep 2997283 = 4495925) B4495925
theorem B998563 : Blo 523799 998563 := bstep (se 1 (by rfl) ⟨748922, by rfl⟩ : syracuseStep 998563 = 1497845) B1497845
theorem B998723 : Blo 523799 998723 := bstep (se 1 (by rfl) ⟨749042, by rfl⟩ : syracuseStep 998723 = 1498085) B1498085
theorem B1326577 : Blo 523799 1326577 := bstep (se 2 (by rfl) ⟨497466, by rfl⟩ : syracuseStep 1326577 = 994933) B994933
theorem B1064497 : Blo 523799 1064497 := bstep (se 2 (by rfl) ⟨399186, by rfl⟩ : syracuseStep 1064497 = 798373) B798373
theorem B2997809 : Blo 523799 2997809 := bstep (se 2 (by rfl) ⟨1124178, by rfl⟩ : syracuseStep 2997809 = 2248357) B2248357
theorem B1326851 : Blo 523799 1326851 := bstep (se 1 (by rfl) ⟨995138, by rfl⟩ : syracuseStep 1326851 = 1990277) B1990277
theorem B4800269 : Blo 523799 4800269 := bstep (se 3 (by rfl) ⟨900050, by rfl⟩ : syracuseStep 4800269 = 1800101) B1800101
theorem B1687331 : Blo 523799 1687331 := bstep (se 1 (by rfl) ⟨1265498, by rfl⟩ : syracuseStep 1687331 = 2530997) B2530997
theorem B6733637 : Blo 523799 6733637 := bstep (se 4 (by rfl) ⟨631278, by rfl⟩ : syracuseStep 6733637 = 1262557) B1262557
theorem B1327043 : Blo 523799 1327043 := bstep (se 1 (by rfl) ⟨995282, by rfl⟩ : syracuseStep 1327043 = 1990565) B1990565
theorem B1294321 : Blo 523799 1294321 := bstep (se 2 (by rfl) ⟨485370, by rfl⟩ : syracuseStep 1294321 = 970741) B970741
theorem B2244941 : Blo 523799 2244941 := bstep (se 3 (by rfl) ⟨420926, by rfl⟩ : syracuseStep 2244941 = 841853) B841853
theorem B999793 : Blo 523799 999793 := bstep (se 2 (by rfl) ⟨374922, by rfl⟩ : syracuseStep 999793 = 749845) B749845
theorem B1688177 : Blo 523799 1688177 := bstep (se 2 (by rfl) ⟨633066, by rfl⟩ : syracuseStep 1688177 = 1266133) B1266133
theorem B2671217 : Blo 523799 2671217 := bstep (se 2 (by rfl) ⟨1001706, by rfl⟩ : syracuseStep 2671217 = 2003413) B2003413
theorem B1426129 : Blo 523799 1426129 := bstep (se 2 (by rfl) ⟨534798, by rfl⟩ : syracuseStep 1426129 = 1069597) B1069597
theorem B1327985 : Blo 523799 1327985 := bstep (se 2 (by rfl) ⟨497994, by rfl⟩ : syracuseStep 1327985 = 995989) B995989
theorem B1491853 : Blo 523799 1491853 := bstep (se 3 (by rfl) ⟨279722, by rfl⟩ : syracuseStep 1491853 = 559445) B559445
theorem B902035 : Blo 523799 902035 := bstep (se 1 (by rfl) ⟨676526, by rfl⟩ : syracuseStep 902035 = 1353053) B1353053
theorem B1328035 : Blo 523799 1328035 := bstep (se 1 (by rfl) ⟨996026, by rfl⟩ : syracuseStep 1328035 = 1992053) B1992053
theorem B2999267 : Blo 523799 2999267 := bstep (se 1 (by rfl) ⟨2249450, by rfl⟩ : syracuseStep 2999267 = 4498901) B4498901
theorem B1492013 : Blo 523799 1492013 := bstep (se 3 (by rfl) ⟨279752, by rfl⟩ : syracuseStep 1492013 = 559505) B559505
theorem B1328177 : Blo 523799 1328177 := bstep (se 2 (by rfl) ⟨498066, by rfl⟩ : syracuseStep 1328177 = 996133) B996133
theorem B1492195 : Blo 523799 1492195 := bstep (se 1 (by rfl) ⟨1119146, by rfl⟩ : syracuseStep 1492195 = 2238293) B2238293
theorem B1066321 : Blo 523799 1066321 := bstep (se 2 (by rfl) ⟨399870, by rfl⟩ : syracuseStep 1066321 = 799741) B799741
theorem B1000849 : Blo 523799 1000849 := bstep (se 2 (by rfl) ⟨375318, by rfl⟩ : syracuseStep 1000849 = 750637) B750637
theorem B1001251 : Blo 523799 1001251 := bstep (se 1 (by rfl) ⟨750938, by rfl⟩ : syracuseStep 1001251 = 1501877) B1501877
theorem B1001297 : Blo 523799 1001297 := bstep (se 2 (by rfl) ⟨375486, by rfl⟩ : syracuseStep 1001297 = 750973) B750973
theorem B1329169 : Blo 523799 1329169 := bstep (se 2 (by rfl) ⟨498438, by rfl⟩ : syracuseStep 1329169 = 996877) B996877
theorem B1001585 : Blo 523799 1001585 := bstep (se 2 (by rfl) ⟨375594, by rfl⟩ : syracuseStep 1001585 = 751189) B751189
theorem B3197069 : Blo 523799 3197069 := bstep (se 3 (by rfl) ⟨599450, by rfl⟩ : syracuseStep 3197069 = 1198901) B1198901
theorem B1263779 : Blo 523799 1263779 := bstep (se 1 (by rfl) ⟨947834, by rfl⟩ : syracuseStep 1263779 = 1895669) B1895669
theorem B1329443 : Blo 523799 1329443 := bstep (se 1 (by rfl) ⟨997082, by rfl⟩ : syracuseStep 1329443 = 1994165) B1994165
theorem B1689997 : Blo 523799 1689997 := bstep (se 3 (by rfl) ⟨316874, by rfl⟩ : syracuseStep 1689997 = 633749) B633749
theorem B8997317 : Blo 523799 8997317 := bstep (se 4 (by rfl) ⟨843498, by rfl⟩ : syracuseStep 8997317 = 1686997) B1686997
theorem B1329635 : Blo 523799 1329635 := bstep (se 1 (by rfl) ⟨997226, by rfl⟩ : syracuseStep 1329635 = 1994453) B1994453
theorem B1493585 : Blo 523799 1493585 := bstep (se 2 (by rfl) ⟨560094, by rfl⟩ : syracuseStep 1493585 = 1120189) B1120189
theorem B1264241 : Blo 523799 1264241 := bstep (se 2 (by rfl) ⟨474090, by rfl⟩ : syracuseStep 1264241 = 948181) B948181
theorem B3001157 : Blo 523799 3001157 := bstep (se 4 (by rfl) ⟨281358, by rfl⟩ : syracuseStep 3001157 = 562717) B562717
theorem B3984227 : Blo 523799 3984227 := bstep (se 1 (by rfl) ⟨2988170, by rfl⟩ : syracuseStep 3984227 = 5976341) B5976341
theorem B10112141 : Blo 523799 10112141 := bstep (se 3 (by rfl) ⟨1896026, by rfl⟩ : syracuseStep 10112141 = 3792053) B3792053
theorem B1330577 : Blo 523799 1330577 := bstep (se 2 (by rfl) ⟨498966, by rfl⟩ : syracuseStep 1330577 = 997933) B997933
theorem B1330627 : Blo 523799 1330627 := bstep (se 1 (by rfl) ⟨997970, by rfl⟩ : syracuseStep 1330627 = 1995941) B1995941
theorem B2837987 : Blo 523799 2837987 := bstep (se 1 (by rfl) ⟨2128490, by rfl⟩ : syracuseStep 2837987 = 4256981) B4256981
theorem B839155 : Blo 523799 839155 := bstep (se 1 (by rfl) ⟨629366, by rfl⟩ : syracuseStep 839155 = 1258733) B1258733
theorem B3362309 : Blo 523799 3362309 := bstep (se 4 (by rfl) ⟨315216, by rfl⟩ : syracuseStep 3362309 = 630433) B630433
theorem B1494541 : Blo 523799 1494541 := bstep (se 3 (by rfl) ⟨280226, by rfl⟩ : syracuseStep 1494541 = 560453) B560453
theorem B1330769 : Blo 523799 1330769 := bstep (se 2 (by rfl) ⟨499038, by rfl⟩ : syracuseStep 1330769 = 998077) B998077
theorem B839393 : Blo 523799 839393 := bstep (se 2 (by rfl) ⟨314772, by rfl⟩ : syracuseStep 839393 = 629545) B629545
theorem B1494769 : Blo 523799 1494769 := bstep (se 2 (by rfl) ⟨560538, by rfl⟩ : syracuseStep 1494769 = 1121077) B1121077
theorem B1068803 : Blo 523799 1068803 := bstep (se 1 (by rfl) ⟨801602, by rfl⟩ : syracuseStep 1068803 = 1603205) B1603205
theorem B4542277 : Blo 523799 4542277 := bstep (se 4 (by rfl) ⟨425838, by rfl⟩ : syracuseStep 4542277 = 851677) B851677
theorem B1920881 : Blo 523799 1920881 := bstep (se 2 (by rfl) ⟨720330, by rfl⟩ : syracuseStep 1920881 = 1440661) B1440661
theorem B1494929 : Blo 523799 1494929 := bstep (se 2 (by rfl) ⟨560598, by rfl⟩ : syracuseStep 1494929 = 1121197) B1121197
theorem B839603 : Blo 523799 839603 := bstep (se 1 (by rfl) ⟨629702, by rfl⟩ : syracuseStep 839603 = 1259405) B1259405
theorem B16175045 : Blo 523799 16175045 := bstep (se 4 (by rfl) ⟨1516410, by rfl⟩ : syracuseStep 16175045 = 3032821) B3032821
theorem B1495043 : Blo 523799 1495043 := bstep (se 1 (by rfl) ⟨1121282, by rfl⟩ : syracuseStep 1495043 = 2242565) B2242565
theorem B1626193 : Blo 523799 1626193 := bstep (se 2 (by rfl) ⟨609822, by rfl⟩ : syracuseStep 1626193 = 1219645) B1219645
theorem B6410339 : Blo 523799 6410339 := bstep (se 1 (by rfl) ⟨4807754, by rfl⟩ : syracuseStep 6410339 = 9615509) B9615509
theorem B2085155 : Blo 523799 2085155 := bstep (se 1 (by rfl) ⟨1563866, by rfl⟩ : syracuseStep 2085155 = 3127733) B3127733
theorem B708913 : Blo 523799 708913 := bstep (se 2 (by rfl) ⟨265842, by rfl⟩ : syracuseStep 708913 = 531685) B531685
theorem B1888589 : Blo 523799 1888589 := bstep (se 3 (by rfl) ⟨354110, by rfl⟩ : syracuseStep 1888589 = 708221) B708221
theorem B1331761 : Blo 523799 1331761 := bstep (se 2 (by rfl) ⟨499410, by rfl⟩ : syracuseStep 1331761 = 998821) B998821
theorem B1200707 : Blo 523799 1200707 := bstep (se 1 (by rfl) ⟨900530, by rfl⟩ : syracuseStep 1200707 = 1801061) B1801061
theorem B2249315 : Blo 523799 2249315 := bstep (se 1 (by rfl) ⟨1686986, by rfl⟩ : syracuseStep 2249315 = 3373973) B3373973
theorem B1692269 : Blo 523799 1692269 := bstep (se 3 (by rfl) ⟨317300, by rfl⟩ : syracuseStep 1692269 = 634601) B634601
theorem B709249 : Blo 523799 709249 := bstep (se 2 (by rfl) ⟨265968, by rfl⟩ : syracuseStep 709249 = 531937) B531937
theorem B840385 : Blo 523799 840385 := bstep (se 2 (by rfl) ⟨315144, by rfl⟩ : syracuseStep 840385 = 630289) B630289
theorem B3232453 : Blo 523799 3232453 := bstep (se 4 (by rfl) ⟨303042, by rfl⟩ : syracuseStep 3232453 = 606085) B606085
theorem B1069777 : Blo 523799 1069777 := bstep (se 2 (by rfl) ⟨401166, by rfl⟩ : syracuseStep 1069777 = 802333) B802333
theorem B1332035 : Blo 523799 1332035 := bstep (se 1 (by rfl) ⟨999026, by rfl⟩ : syracuseStep 1332035 = 1998053) B1998053
theorem B2839373 : Blo 523799 2839373 := bstep (se 3 (by rfl) ⟨532382, by rfl⟩ : syracuseStep 2839373 = 1064765) B1064765
theorem B1496045 : Blo 523799 1496045 := bstep (se 3 (by rfl) ⟨280508, by rfl⟩ : syracuseStep 1496045 = 561017) B561017
theorem B1332227 : Blo 523799 1332227 := bstep (se 1 (by rfl) ⟨999170, by rfl⟩ : syracuseStep 1332227 = 1998341) B1998341
theorem B1496227 : Blo 523799 1496227 := bstep (se 1 (by rfl) ⟨1122170, by rfl⟩ : syracuseStep 1496227 = 2244341) B2244341
theorem B1496387 : Blo 523799 1496387 := bstep (se 1 (by rfl) ⟨1122290, by rfl⟩ : syracuseStep 1496387 = 2244581) B2244581
theorem B5199173 : Blo 523799 5199173 := bstep (se 4 (by rfl) ⟨487422, by rfl⟩ : syracuseStep 5199173 = 974845) B974845
theorem B808385 : Blo 523799 808385 := bstep (se 2 (by rfl) ⟨303144, by rfl⟩ : syracuseStep 808385 = 606289) B606289
theorem B841187 : Blo 523799 841187 := bstep (se 1 (by rfl) ⟨630890, by rfl⟩ : syracuseStep 841187 = 1261781) B1261781
theorem B1267363 : Blo 523799 1267363 := bstep (se 1 (by rfl) ⟨950522, by rfl⟩ : syracuseStep 1267363 = 1901045) B1901045
theorem B1267555 : Blo 523799 1267555 := bstep (se 1 (by rfl) ⟨950666, by rfl⟩ : syracuseStep 1267555 = 1901333) B1901333
theorem B2840453 : Blo 523799 2840453 := bstep (se 4 (by rfl) ⟨266292, by rfl⟩ : syracuseStep 2840453 = 532585) B532585
theorem B1333169 : Blo 523799 1333169 := bstep (se 2 (by rfl) ⟨499938, by rfl⟩ : syracuseStep 1333169 = 999877) B999877
theorem B841699 : Blo 523799 841699 := bstep (se 1 (by rfl) ⟨631274, by rfl⟩ : syracuseStep 841699 = 1262549) B1262549
theorem B1333219 : Blo 523799 1333219 := bstep (se 1 (by rfl) ⟨999914, by rfl⟩ : syracuseStep 1333219 = 1999829) B1999829
theorem B3790961 : Blo 523799 3790961 := bstep (se 2 (by rfl) ⟨1421610, by rfl⟩ : syracuseStep 3790961 = 2843221) B2843221
theorem B1333361 : Blo 523799 1333361 := bstep (se 2 (by rfl) ⟨500010, by rfl⟩ : syracuseStep 1333361 = 1000021) B1000021
theorem B1267825 : Blo 523799 1267825 := bstep (se 2 (by rfl) ⟨475434, by rfl⟩ : syracuseStep 1267825 = 950869) B950869
theorem B1136963 : Blo 523799 1136963 := bstep (se 1 (by rfl) ⟨852722, by rfl⟩ : syracuseStep 1136963 = 1705445) B1705445
theorem B1497457 : Blo 523799 1497457 := bstep (se 2 (by rfl) ⟨561546, by rfl⟩ : syracuseStep 1497457 = 1123093) B1123093
theorem B1825187 : Blo 523799 1825187 := bstep (se 1 (by rfl) ⟨1368890, by rfl⟩ : syracuseStep 1825187 = 2737781) B2737781
theorem B8673733 : Blo 523799 8673733 := bstep (se 4 (by rfl) ⟨813162, by rfl⟩ : syracuseStep 8673733 = 1626325) B1626325
theorem B842243 : Blo 523799 842243 := bstep (se 1 (by rfl) ⟨631682, by rfl⟩ : syracuseStep 842243 = 1263365) B1263365
theorem B2251313 : Blo 523799 2251313 := bstep (se 2 (by rfl) ⟨844242, by rfl⟩ : syracuseStep 2251313 = 1688485) B1688485
theorem B842417 : Blo 523799 842417 := bstep (se 2 (by rfl) ⟨315906, by rfl⟩ : syracuseStep 842417 = 631813) B631813
theorem B1792835 : Blo 523799 1792835 := bstep (se 1 (by rfl) ⟨1344626, by rfl⟩ : syracuseStep 1792835 = 2689253) B2689253
theorem B4480069 : Blo 523799 4480069 := bstep (se 4 (by rfl) ⟨420006, by rfl⟩ : syracuseStep 4480069 = 840013) B840013
theorem B1334353 : Blo 523799 1334353 := bstep (se 2 (by rfl) ⟨500382, by rfl⟩ : syracuseStep 1334353 = 1000765) B1000765
theorem B1596611 : Blo 523799 1596611 := bstep (se 1 (by rfl) ⟨1197458, by rfl⟩ : syracuseStep 1596611 = 2394917) B2394917
theorem B810209 : Blo 523799 810209 := bstep (se 2 (by rfl) ⟨303828, by rfl⟩ : syracuseStep 810209 = 607657) B607657
theorem B711985 : Blo 523799 711985 := bstep (se 2 (by rfl) ⟨266994, by rfl⟩ : syracuseStep 711985 = 533989) B533989
theorem B810307 : Blo 523799 810307 := bstep (se 1 (by rfl) ⟨607730, by rfl⟩ : syracuseStep 810307 = 1215461) B1215461
theorem B1334627 : Blo 523799 1334627 := bstep (se 1 (by rfl) ⟨1000970, by rfl⟩ : syracuseStep 1334627 = 2001941) B2001941
theorem B1334819 : Blo 523799 1334819 := bstep (se 1 (by rfl) ⟨1001114, by rfl⟩ : syracuseStep 1334819 = 2002229) B2002229
theorem B1498733 : Blo 523799 1498733 := bstep (se 3 (by rfl) ⟨281012, by rfl⟩ : syracuseStep 1498733 = 562025) B562025
theorem B712481 : Blo 523799 712481 := bstep (se 2 (by rfl) ⟨267180, by rfl⟩ : syracuseStep 712481 = 534361) B534361
theorem B1498915 : Blo 523799 1498915 := bstep (se 1 (by rfl) ⟨1124186, by rfl⟩ : syracuseStep 1498915 = 2248373) B2248373
theorem B1498961 : Blo 523799 1498961 := bstep (se 2 (by rfl) ⟨562110, by rfl⟩ : syracuseStep 1498961 = 1124221) B1124221
theorem B1793933 : Blo 523799 1793933 := bstep (se 3 (by rfl) ⟨336362, by rfl⟩ : syracuseStep 1793933 = 672725) B672725
theorem B5070833 : Blo 523799 5070833 := bstep (se 2 (by rfl) ⟨1901562, by rfl⟩ : syracuseStep 5070833 = 3803125) B3803125
theorem B3989573 : Blo 523799 3989573 := bstep (se 4 (by rfl) ⟨374022, by rfl⟩ : syracuseStep 3989573 = 748045) B748045
theorem B4251761 : Blo 523799 4251761 := bstep (se 2 (by rfl) ⟨1594410, by rfl⟩ : syracuseStep 4251761 = 3188821) B3188821
theorem B2253005 : Blo 523799 2253005 := bstep (se 3 (by rfl) ⟨422438, by rfl⟩ : syracuseStep 2253005 = 844877) B844877
theorem B712913 : Blo 523799 712913 := bstep (se 2 (by rfl) ⟨267342, by rfl⟩ : syracuseStep 712913 = 534685) B534685
theorem B1335761 : Blo 523799 1335761 := bstep (se 2 (by rfl) ⟨500910, by rfl⟩ : syracuseStep 1335761 = 1001821) B1001821
theorem B1335811 : Blo 523799 1335811 := bstep (se 1 (by rfl) ⟨1001858, by rfl⟩ : syracuseStep 1335811 = 2003717) B2003717
theorem B1335953 : Blo 523799 1335953 := bstep (se 2 (by rfl) ⟨500982, by rfl⟩ : syracuseStep 1335953 = 1001965) B1001965
theorem B844435 : Blo 523799 844435 := bstep (se 1 (by rfl) ⟨633326, by rfl⟩ : syracuseStep 844435 = 1266653) B1266653
theorem B746177 : Blo 523799 746177 := bstep (se 2 (by rfl) ⟨279816, by rfl⟩ : syracuseStep 746177 = 559633) B559633
theorem B844499 : Blo 523799 844499 := bstep (se 1 (by rfl) ⟨633374, by rfl⟩ : syracuseStep 844499 = 1266749) B1266749
theorem B746291 : Blo 523799 746291 := bstep (se 1 (by rfl) ⟨559718, by rfl⟩ : syracuseStep 746291 = 1119437) B1119437
theorem B1991537 : Blo 523799 1991537 := bstep (se 2 (by rfl) ⟨746826, by rfl⟩ : syracuseStep 1991537 = 1493653) B1493653
theorem B746371 : Blo 523799 746371 := bstep (se 1 (by rfl) ⟨559778, by rfl⟩ : syracuseStep 746371 = 1119557) B1119557
theorem B1598413 : Blo 523799 1598413 := bstep (se 3 (by rfl) ⟨299702, by rfl⟩ : syracuseStep 1598413 = 599405) B599405
theorem B12838085 : Blo 523799 12838085 := bstep (se 4 (by rfl) ⟨1203570, by rfl⟩ : syracuseStep 12838085 = 2407141) B2407141
theorem B1500419 : Blo 523799 1500419 := bstep (se 1 (by rfl) ⟨1125314, by rfl⟩ : syracuseStep 1500419 = 2250629) B2250629
theorem B746929 : Blo 523799 746929 := bstep (se 2 (by rfl) ⟨280098, by rfl⟩ : syracuseStep 746929 = 560197) B560197
theorem B4056817 : Blo 523799 4056817 := bstep (se 2 (by rfl) ⟨1521306, by rfl⟩ : syracuseStep 4056817 = 3042613) B3042613
theorem B649315 : Blo 523799 649315 := bstep (se 1 (by rfl) ⟨486986, by rfl⟩ : syracuseStep 649315 = 973973) B973973
theorem B747635 : Blo 523799 747635 := bstep (se 1 (by rfl) ⟨560726, by rfl⟩ : syracuseStep 747635 = 1121453) B1121453
theorem B1992995 : Blo 523799 1992995 := bstep (se 1 (by rfl) ⟨1494746, by rfl⟩ : syracuseStep 1992995 = 2989493) B2989493
theorem B1501649 : Blo 523799 1501649 := bstep (se 2 (by rfl) ⟨563118, by rfl⟩ : syracuseStep 1501649 = 1126237) B1126237
theorem B1600163 : Blo 523799 1600163 := bstep (se 1 (by rfl) ⟨1200122, by rfl⟩ : syracuseStep 1600163 = 2400245) B2400245
theorem B748273 : Blo 523799 748273 := bstep (se 2 (by rfl) ⟨280602, by rfl⟩ : syracuseStep 748273 = 561205) B561205
theorem B1796899 : Blo 523799 1796899 := bstep (se 1 (by rfl) ⟨1347674, by rfl⟩ : syracuseStep 1796899 = 2695349) B2695349
theorem B3337037 : Blo 523799 3337037 := bstep (se 3 (by rfl) ⟨625694, by rfl⟩ : syracuseStep 3337037 = 1251389) B1251389
theorem B748387 : Blo 523799 748387 := bstep (se 1 (by rfl) ⟨561290, by rfl⟩ : syracuseStep 748387 = 1122581) B1122581
theorem B10087537 : Blo 523799 10087537 := bstep (se 2 (by rfl) ⟨3782826, by rfl⟩ : syracuseStep 10087537 = 7565653) B7565653
theorem B1010819 : Blo 523799 1010819 := bstep (se 1 (by rfl) ⟨758114, by rfl⟩ : syracuseStep 1010819 = 1516229) B1516229
theorem B945361 : Blo 523799 945361 := bstep (se 2 (by rfl) ⟨354510, by rfl⟩ : syracuseStep 945361 = 709021) B709021
theorem B1993997 : Blo 523799 1993997 := bstep (se 3 (by rfl) ⟨373874, by rfl⟩ : syracuseStep 1993997 = 747749) B747749
theorem B2519117 : Blo 523799 2519117 := bstep (se 3 (by rfl) ⟨472334, by rfl⟩ : syracuseStep 2519117 = 944669) B944669
theorem B4059277 : Blo 523799 4059277 := bstep (se 3 (by rfl) ⟨761114, by rfl⟩ : syracuseStep 4059277 = 1522229) B1522229
theorem B749731 : Blo 523799 749731 := bstep (se 1 (by rfl) ⟨562298, by rfl⟩ : syracuseStep 749731 = 1124597) B1124597
theorem B1077617 : Blo 523799 1077617 := bstep (se 2 (by rfl) ⟨404106, by rfl⟩ : syracuseStep 1077617 = 808213) B808213
theorem B914641 : Blo 523799 914641 := bstep (se 2 (by rfl) ⟨342990, by rfl⟩ : syracuseStep 914641 = 685981) B685981
theorem B750865 : Blo 523799 750865 := bstep (se 2 (by rfl) ⟨281574, by rfl⟩ : syracuseStep 750865 = 563149) B563149
theorem B2389283 : Blo 523799 2389283 := bstep (se 1 (by rfl) ⟨1791962, by rfl⟩ : syracuseStep 2389283 = 3583925) B3583925
theorem B1996109 : Blo 523799 1996109 := bstep (se 3 (by rfl) ⟨374270, by rfl⟩ : syracuseStep 1996109 = 748541) B748541
theorem B750961 : Blo 523799 750961 := bstep (se 2 (by rfl) ⟨281610, by rfl⟩ : syracuseStep 750961 = 563221) B563221
theorem B3601955 : Blo 523799 3601955 := bstep (se 1 (by rfl) ⟨2701466, by rfl⟩ : syracuseStep 3601955 = 5402933) B5402933
theorem B947971 : Blo 523799 947971 := bstep (se 1 (by rfl) ⟨710978, by rfl⟩ : syracuseStep 947971 = 1421957) B1421957
theorem B3995405 : Blo 523799 3995405 := bstep (se 3 (by rfl) ⟨749138, by rfl⟩ : syracuseStep 3995405 = 1498277) B1498277
theorem B2651939 : Blo 523799 2651939 := bstep (se 1 (by rfl) ⟨1988954, by rfl⟩ : syracuseStep 2651939 = 3977909) B3977909
theorem B751457 : Blo 523799 751457 := bstep (se 2 (by rfl) ⟨281796, by rfl⟩ : syracuseStep 751457 = 563593) B563593
theorem B11401073 : Blo 523799 11401073 := bstep (se 2 (by rfl) ⟨4275402, by rfl⟩ : syracuseStep 11401073 = 8550805) B8550805
theorem B948145 : Blo 523799 948145 := bstep (se 2 (by rfl) ⟨355554, by rfl⟩ : syracuseStep 948145 = 711109) B711109
theorem B1996913 : Blo 523799 1996913 := bstep (se 2 (by rfl) ⟨748842, by rfl⟩ : syracuseStep 1996913 = 1497685) B1497685
theorem B1800323 : Blo 523799 1800323 := bstep (se 1 (by rfl) ⟨1350242, by rfl⟩ : syracuseStep 1800323 = 2700485) B2700485
theorem B1768013 : Blo 523799 1768013 := bstep (se 3 (by rfl) ⟨331502, by rfl⟩ : syracuseStep 1768013 = 663005) B663005
theorem B2652749 : Blo 523799 2652749 := bstep (se 3 (by rfl) ⟨497390, by rfl⟩ : syracuseStep 2652749 = 994781) B994781
theorem B1768067 : Blo 523799 1768067 := bstep (se 1 (by rfl) ⟨1326050, by rfl⟩ : syracuseStep 1768067 = 2652101) B2652101
theorem B4782833 : Blo 523799 4782833 := bstep (se 2 (by rfl) ⟨1793562, by rfl⟩ : syracuseStep 4782833 = 3587125) B3587125
theorem B1997581 : Blo 523799 1997581 := bstep (se 3 (by rfl) ⟨374546, by rfl⟩ : syracuseStep 1997581 = 749093) B749093
theorem B1211171 : Blo 523799 1211171 := bstep (se 1 (by rfl) ⟨908378, by rfl⟩ : syracuseStep 1211171 = 1816757) B1816757
theorem B1768337 : Blo 523799 1768337 := bstep (se 2 (by rfl) ⟨663126, by rfl⟩ : syracuseStep 1768337 = 1326253) B1326253
theorem B1801169 : Blo 523799 1801169 := bstep (se 2 (by rfl) ⟨675438, by rfl⟩ : syracuseStep 1801169 = 1350877) B1350877
theorem B6061169 : Blo 523799 6061169 := bstep (se 2 (by rfl) ⟨2272938, by rfl⟩ : syracuseStep 6061169 = 4545877) B4545877
theorem B1178801 : Blo 523799 1178801 := bstep (se 2 (by rfl) ⟨442050, by rfl⟩ : syracuseStep 1178801 = 884101) B884101
theorem B1178819 : Blo 523799 1178819 := bstep (se 1 (by rfl) ⟨884114, by rfl⟩ : syracuseStep 1178819 = 1768229) B1768229
theorem B883939 : Blo 523799 883939 := bstep (se 1 (by rfl) ⟨662954, by rfl⟩ : syracuseStep 883939 = 1325909) B1325909
theorem B1539341 : Blo 523799 1539341 := bstep (se 3 (by rfl) ⟨288626, by rfl⟩ : syracuseStep 1539341 = 577253) B577253
theorem B785699 : Blo 523799 785699 := bstep (se 1 (by rfl) ⟨589274, by rfl⟩ : syracuseStep 785699 = 1178549) B1178549
theorem B785729 : Blo 523799 785729 := bstep (se 2 (by rfl) ⟨294648, by rfl⟩ : syracuseStep 785729 = 589297) B589297
theorem B3374405 : Blo 523799 3374405 := bstep (se 4 (by rfl) ⟨316350, by rfl⟩ : syracuseStep 3374405 = 632701) B632701
theorem B785747 : Blo 523799 785747 := bstep (se 1 (by rfl) ⟨589310, by rfl⟩ : syracuseStep 785747 = 1178621) B1178621
theorem B785777 : Blo 523799 785777 := bstep (se 2 (by rfl) ⟨294666, by rfl⟩ : syracuseStep 785777 = 589333) B589333
theorem B884081 : Blo 523799 884081 := bstep (se 2 (by rfl) ⟨331530, by rfl⟩ : syracuseStep 884081 = 663061) B663061
theorem B785795 : Blo 523799 785795 := bstep (se 1 (by rfl) ⟨589346, by rfl⟩ : syracuseStep 785795 = 1178693) B1178693
theorem B785825 : Blo 523799 785825 := bstep (se 2 (by rfl) ⟨294684, by rfl⟩ : syracuseStep 785825 = 589369) B589369
theorem B1768877 : Blo 523799 1768877 := bstep (se 3 (by rfl) ⟨331664, by rfl⟩ : syracuseStep 1768877 = 663329) B663329
theorem B785843 : Blo 523799 785843 := bstep (se 1 (by rfl) ⟨589382, by rfl⟩ : syracuseStep 785843 = 1178765) B1178765
theorem B785873 : Blo 523799 785873 := bstep (se 2 (by rfl) ⟨294702, by rfl⟩ : syracuseStep 785873 = 589405) B589405
theorem B1179089 : Blo 523799 1179089 := bstep (se 2 (by rfl) ⟨442158, by rfl⟩ : syracuseStep 1179089 = 884317) B884317
theorem B785891 : Blo 523799 785891 := bstep (se 1 (by rfl) ⟨589418, by rfl⟩ : syracuseStep 785891 = 1178837) B1178837
theorem B1179107 : Blo 523799 1179107 := bstep (se 1 (by rfl) ⟨884330, by rfl⟩ : syracuseStep 1179107 = 1768661) B1768661
theorem B1768931 : Blo 523799 1768931 := bstep (se 1 (by rfl) ⟨1326698, by rfl⟩ : syracuseStep 1768931 = 2653397) B2653397
theorem B884209 : Blo 523799 884209 := bstep (se 2 (by rfl) ⟨331578, by rfl⟩ : syracuseStep 884209 = 663157) B663157
theorem B785921 : Blo 523799 785921 := bstep (se 2 (by rfl) ⟨294720, by rfl⟩ : syracuseStep 785921 = 589441) B589441
theorem B589315 : Blo 523799 589315 := bstep (se 1 (by rfl) ⟨441986, by rfl⟩ : syracuseStep 589315 = 883973) B883973
theorem B1801745 : Blo 523799 1801745 := bstep (se 2 (by rfl) ⟨675654, by rfl⟩ : syracuseStep 1801745 = 1351309) B1351309
theorem B785939 : Blo 523799 785939 := bstep (se 1 (by rfl) ⟨589454, by rfl⟩ : syracuseStep 785939 = 1178909) B1178909
theorem B884243 : Blo 523799 884243 := bstep (se 1 (by rfl) ⟨663182, by rfl⟩ : syracuseStep 884243 = 1326365) B1326365
theorem B523811 : Blo 523799 523811 := bstep (se 1 (by rfl) ⟨392858, by rfl⟩ : syracuseStep 523811 = 785717) B785717
theorem B1998371 : Blo 523799 1998371 := bstep (se 1 (by rfl) ⟨1498778, by rfl⟩ : syracuseStep 1998371 = 2997557) B2997557
theorem B785969 : Blo 523799 785969 := bstep (se 2 (by rfl) ⟨294738, by rfl⟩ : syracuseStep 785969 = 589477) B589477
theorem B523827 : Blo 523799 523827 := bstep (se 1 (by rfl) ⟨392870, by rfl⟩ : syracuseStep 523827 = 785741) B785741
theorem B523843 : Blo 523799 523843 := bstep (se 1 (by rfl) ⟨392882, by rfl⟩ : syracuseStep 523843 = 785765) B785765
theorem B785987 : Blo 523799 785987 := bstep (se 1 (by rfl) ⟨589490, by rfl⟩ : syracuseStep 785987 = 1178981) B1178981
theorem B523859 : Blo 523799 523859 := bstep (se 1 (by rfl) ⟨392894, by rfl⟩ : syracuseStep 523859 = 785789) B785789
theorem B786017 : Blo 523799 786017 := bstep (se 2 (by rfl) ⟨294756, by rfl⟩ : syracuseStep 786017 = 589513) B589513
theorem B523875 : Blo 523799 523875 := bstep (se 1 (by rfl) ⟨392906, by rfl⟩ : syracuseStep 523875 = 785813) B785813
theorem B949859 : Blo 523799 949859 := bstep (se 1 (by rfl) ⟨712394, by rfl⟩ : syracuseStep 949859 = 1424789) B1424789
theorem B4488817 : Blo 523799 4488817 := bstep (se 2 (by rfl) ⟨1683306, by rfl⟩ : syracuseStep 4488817 = 3366613) B3366613
theorem B523891 : Blo 523799 523891 := bstep (se 1 (by rfl) ⟨392918, by rfl⟩ : syracuseStep 523891 = 785837) B785837
theorem B786035 : Blo 523799 786035 := bstep (se 1 (by rfl) ⟨589526, by rfl⟩ : syracuseStep 786035 = 1179053) B1179053
theorem B523907 : Blo 523799 523907 := bstep (se 1 (by rfl) ⟨392930, by rfl⟩ : syracuseStep 523907 = 785861) B785861
theorem B786065 : Blo 523799 786065 := bstep (se 2 (by rfl) ⟨294774, by rfl⟩ : syracuseStep 786065 = 589549) B589549
theorem B523923 : Blo 523799 523923 := bstep (se 1 (by rfl) ⟨392942, by rfl⟩ : syracuseStep 523923 = 785885) B785885
theorem B589459 : Blo 523799 589459 := bstep (se 1 (by rfl) ⟨442094, by rfl⟩ : syracuseStep 589459 = 884189) B884189
theorem B884371 : Blo 523799 884371 := bstep (se 1 (by rfl) ⟨663278, by rfl⟩ : syracuseStep 884371 = 1326557) B1326557
theorem B523939 : Blo 523799 523939 := bstep (se 1 (by rfl) ⟨392954, by rfl⟩ : syracuseStep 523939 = 785909) B785909
theorem B786083 : Blo 523799 786083 := bstep (se 1 (by rfl) ⟨589562, by rfl⟩ : syracuseStep 786083 = 1179125) B1179125
theorem B523955 : Blo 523799 523955 := bstep (se 1 (by rfl) ⟨392966, by rfl⟩ : syracuseStep 523955 = 785933) B785933
theorem B786113 : Blo 523799 786113 := bstep (se 2 (by rfl) ⟨294792, by rfl⟩ : syracuseStep 786113 = 589585) B589585
theorem B523971 : Blo 523799 523971 := bstep (se 1 (by rfl) ⟨392978, by rfl⟩ : syracuseStep 523971 = 785957) B785957
theorem B523987 : Blo 523799 523987 := bstep (se 1 (by rfl) ⟨392990, by rfl⟩ : syracuseStep 523987 = 785981) B785981
theorem B786131 : Blo 523799 786131 := bstep (se 1 (by rfl) ⟨589598, by rfl⟩ : syracuseStep 786131 = 1179197) B1179197
theorem B524003 : Blo 523799 524003 := bstep (se 1 (by rfl) ⟨393002, by rfl⟩ : syracuseStep 524003 = 786005) B786005
theorem B786161 : Blo 523799 786161 := bstep (se 2 (by rfl) ⟨294810, by rfl⟩ : syracuseStep 786161 = 589621) B589621
theorem B1179377 : Blo 523799 1179377 := bstep (se 2 (by rfl) ⟨442266, by rfl⟩ : syracuseStep 1179377 = 884533) B884533
theorem B524019 : Blo 523799 524019 := bstep (se 1 (by rfl) ⟨393014, by rfl⟩ : syracuseStep 524019 = 786029) B786029
theorem B1769201 : Blo 523799 1769201 := bstep (se 2 (by rfl) ⟨663450, by rfl⟩ : syracuseStep 1769201 = 1326901) B1326901
theorem B524035 : Blo 523799 524035 := bstep (se 1 (by rfl) ⟨393026, by rfl⟩ : syracuseStep 524035 = 786053) B786053
theorem B786179 : Blo 523799 786179 := bstep (se 1 (by rfl) ⟨589634, by rfl⟩ : syracuseStep 786179 = 1179269) B1179269
theorem B1179395 : Blo 523799 1179395 := bstep (se 1 (by rfl) ⟨884546, by rfl⟩ : syracuseStep 1179395 = 1769093) B1769093
theorem B524051 : Blo 523799 524051 := bstep (se 1 (by rfl) ⟨393038, by rfl⟩ : syracuseStep 524051 = 786077) B786077
theorem B884513 : Blo 523799 884513 := bstep (se 2 (by rfl) ⟨331692, by rfl⟩ : syracuseStep 884513 = 663385) B663385
theorem B786209 : Blo 523799 786209 := bstep (se 2 (by rfl) ⟨294828, by rfl⟩ : syracuseStep 786209 = 589657) B589657
theorem B524067 : Blo 523799 524067 := bstep (se 1 (by rfl) ⟨393050, by rfl⟩ : syracuseStep 524067 = 786101) B786101
theorem B589603 : Blo 523799 589603 := bstep (se 1 (by rfl) ⟨442202, by rfl⟩ : syracuseStep 589603 = 884405) B884405
theorem B524083 : Blo 523799 524083 := bstep (se 1 (by rfl) ⟨393062, by rfl⟩ : syracuseStep 524083 = 786125) B786125
theorem B786227 : Blo 523799 786227 := bstep (se 1 (by rfl) ⟨589670, by rfl⟩ : syracuseStep 786227 = 1179341) B1179341
theorem B524099 : Blo 523799 524099 := bstep (se 1 (by rfl) ⟨393074, by rfl⟩ : syracuseStep 524099 = 786149) B786149
theorem B786257 : Blo 523799 786257 := bstep (se 2 (by rfl) ⟨294846, by rfl⟩ : syracuseStep 786257 = 589693) B589693
theorem B524115 : Blo 523799 524115 := bstep (se 1 (by rfl) ⟨393086, by rfl⟩ : syracuseStep 524115 = 786173) B786173
theorem B524131 : Blo 523799 524131 := bstep (se 1 (by rfl) ⟨393098, by rfl⟩ : syracuseStep 524131 = 786197) B786197
theorem B786275 : Blo 523799 786275 := bstep (se 1 (by rfl) ⟨589706, by rfl⟩ : syracuseStep 786275 = 1179413) B1179413
theorem B524147 : Blo 523799 524147 := bstep (se 1 (by rfl) ⟨393110, by rfl⟩ : syracuseStep 524147 = 786221) B786221
theorem B786305 : Blo 523799 786305 := bstep (se 2 (by rfl) ⟨294864, by rfl⟩ : syracuseStep 786305 = 589729) B589729
theorem B524163 : Blo 523799 524163 := bstep (se 1 (by rfl) ⟨393122, by rfl⟩ : syracuseStep 524163 = 786245) B786245
theorem B524179 : Blo 523799 524179 := bstep (se 1 (by rfl) ⟨393134, by rfl⟩ : syracuseStep 524179 = 786269) B786269
theorem B786323 : Blo 523799 786323 := bstep (se 1 (by rfl) ⟨589742, by rfl⟩ : syracuseStep 786323 = 1179485) B1179485
theorem B884641 : Blo 523799 884641 := bstep (se 2 (by rfl) ⟨331740, by rfl⟩ : syracuseStep 884641 = 663481) B663481
theorem B524195 : Blo 523799 524195 := bstep (se 1 (by rfl) ⟨393146, by rfl⟩ : syracuseStep 524195 = 786293) B786293
theorem B786353 : Blo 523799 786353 := bstep (se 2 (by rfl) ⟨294882, by rfl⟩ : syracuseStep 786353 = 589765) B589765
theorem B524211 : Blo 523799 524211 := bstep (se 1 (by rfl) ⟨393158, by rfl⟩ : syracuseStep 524211 = 786317) B786317
theorem B589747 : Blo 523799 589747 := bstep (se 1 (by rfl) ⟨442310, by rfl⟩ : syracuseStep 589747 = 884621) B884621
theorem B524227 : Blo 523799 524227 := bstep (se 1 (by rfl) ⟨393170, by rfl⟩ : syracuseStep 524227 = 786341) B786341
theorem B786371 : Blo 523799 786371 := bstep (se 1 (by rfl) ⟨589778, by rfl⟩ : syracuseStep 786371 = 1179557) B1179557
theorem B884675 : Blo 523799 884675 := bstep (se 1 (by rfl) ⟨663506, by rfl⟩ : syracuseStep 884675 = 1327013) B1327013
theorem B524243 : Blo 523799 524243 := bstep (se 1 (by rfl) ⟨393182, by rfl⟩ : syracuseStep 524243 = 786365) B786365
theorem B786401 : Blo 523799 786401 := bstep (se 2 (by rfl) ⟨294900, by rfl⟩ : syracuseStep 786401 = 589801) B589801
theorem B524259 : Blo 523799 524259 := bstep (se 1 (by rfl) ⟨393194, by rfl⟩ : syracuseStep 524259 = 786389) B786389
theorem B524275 : Blo 523799 524275 := bstep (se 1 (by rfl) ⟨393206, by rfl⟩ : syracuseStep 524275 = 786413) B786413
theorem B786419 : Blo 523799 786419 := bstep (se 1 (by rfl) ⟨589814, by rfl⟩ : syracuseStep 786419 = 1179629) B1179629
theorem B786443 : Blo 523799 786443 := bstep (se 1 (by rfl) ⟨589832, by rfl⟩ : syracuseStep 786443 = 1179665) B1179665
theorem B524299 : Blo 523799 524299 := bstep (se 1 (by rfl) ⟨393224, by rfl⟩ : syracuseStep 524299 = 786449) B786449
theorem B786455 : Blo 523799 786455 := bstep (se 1 (by rfl) ⟨589841, by rfl⟩ : syracuseStep 786455 = 1179683) B1179683
theorem B524311 : Blo 523799 524311 := bstep (se 1 (by rfl) ⟨393233, by rfl⟩ : syracuseStep 524311 = 786467) B786467
theorem B524331 : Blo 523799 524331 := bstep (se 1 (by rfl) ⟨393248, by rfl⟩ : syracuseStep 524331 = 786497) B786497
theorem B524343 : Blo 523799 524343 := bstep (se 1 (by rfl) ⟨393257, by rfl⟩ : syracuseStep 524343 = 786515) B786515
theorem B524363 : Blo 523799 524363 := bstep (se 1 (by rfl) ⟨393272, by rfl⟩ : syracuseStep 524363 = 786545) B786545
theorem B524375 : Blo 523799 524375 := bstep (se 1 (by rfl) ⟨393281, by rfl⟩ : syracuseStep 524375 = 786563) B786563
theorem B1179737 : Blo 523799 1179737 := bstep (se 2 (by rfl) ⟨442401, by rfl⟩ : syracuseStep 1179737 = 884803) B884803
theorem B786521 : Blo 523799 786521 := bstep (se 2 (by rfl) ⟨294945, by rfl⟩ : syracuseStep 786521 = 589891) B589891
theorem B524395 : Blo 523799 524395 := bstep (se 1 (by rfl) ⟨393296, by rfl⟩ : syracuseStep 524395 = 786593) B786593
theorem B524407 : Blo 523799 524407 := bstep (se 1 (by rfl) ⟨393305, by rfl⟩ : syracuseStep 524407 = 786611) B786611
theorem B589963 : Blo 523799 589963 := bstep (se 1 (by rfl) ⟨442472, by rfl⟩ : syracuseStep 589963 = 884945) B884945
theorem B524427 : Blo 523799 524427 := bstep (se 1 (by rfl) ⟨393320, by rfl⟩ : syracuseStep 524427 = 786641) B786641
theorem B524439 : Blo 523799 524439 := bstep (se 1 (by rfl) ⟨393329, by rfl⟩ : syracuseStep 524439 = 786659) B786659
theorem B524459 : Blo 523799 524459 := bstep (se 1 (by rfl) ⟨393344, by rfl⟩ : syracuseStep 524459 = 786689) B786689
theorem B1179827 : Blo 523799 1179827 := bstep (se 1 (by rfl) ⟨884870, by rfl⟩ : syracuseStep 1179827 = 1769741) B1769741
theorem B524471 : Blo 523799 524471 := bstep (se 1 (by rfl) ⟨393353, by rfl⟩ : syracuseStep 524471 = 786707) B786707
theorem B786635 : Blo 523799 786635 := bstep (se 1 (by rfl) ⟨589976, by rfl⟩ : syracuseStep 786635 = 1179953) B1179953
theorem B524491 : Blo 523799 524491 := bstep (se 1 (by rfl) ⟨393368, by rfl⟩ : syracuseStep 524491 = 786737) B786737
theorem B1179863 : Blo 523799 1179863 := bstep (se 1 (by rfl) ⟨884897, by rfl⟩ : syracuseStep 1179863 = 1769795) B1769795
theorem B786647 : Blo 523799 786647 := bstep (se 1 (by rfl) ⟨589985, by rfl⟩ : syracuseStep 786647 = 1179971) B1179971
theorem B524503 : Blo 523799 524503 := bstep (se 1 (by rfl) ⟨393377, by rfl⟩ : syracuseStep 524503 = 786755) B786755
theorem B524523 : Blo 523799 524523 := bstep (se 1 (by rfl) ⟨393392, by rfl⟩ : syracuseStep 524523 = 786785) B786785
theorem B590071 : Blo 523799 590071 := bstep (se 1 (by rfl) ⟨442553, by rfl⟩ : syracuseStep 590071 = 885107) B885107
theorem B524535 : Blo 523799 524535 := bstep (se 1 (by rfl) ⟨393401, by rfl⟩ : syracuseStep 524535 = 786803) B786803
theorem B524555 : Blo 523799 524555 := bstep (se 1 (by rfl) ⟨393416, by rfl⟩ : syracuseStep 524555 = 786833) B786833
theorem B524567 : Blo 523799 524567 := bstep (se 1 (by rfl) ⟨393425, by rfl⟩ : syracuseStep 524567 = 786851) B786851
theorem B786713 : Blo 523799 786713 := bstep (se 2 (by rfl) ⟨295017, by rfl⟩ : syracuseStep 786713 = 590035) B590035
theorem B524587 : Blo 523799 524587 := bstep (se 1 (by rfl) ⟨393440, by rfl⟩ : syracuseStep 524587 = 786881) B786881
theorem B524599 : Blo 523799 524599 := bstep (se 1 (by rfl) ⟨393449, by rfl⟩ : syracuseStep 524599 = 786899) B786899
theorem B524619 : Blo 523799 524619 := bstep (se 1 (by rfl) ⟨393464, by rfl⟩ : syracuseStep 524619 = 786929) B786929
theorem B524631 : Blo 523799 524631 := bstep (se 1 (by rfl) ⟨393473, by rfl⟩ : syracuseStep 524631 = 786947) B786947
theorem B524651 : Blo 523799 524651 := bstep (se 1 (by rfl) ⟨393488, by rfl⟩ : syracuseStep 524651 = 786977) B786977
theorem B524663 : Blo 523799 524663 := bstep (se 1 (by rfl) ⟨393497, by rfl⟩ : syracuseStep 524663 = 786995) B786995
theorem B1180043 : Blo 523799 1180043 := bstep (se 1 (by rfl) ⟨885032, by rfl⟩ : syracuseStep 1180043 = 1770065) B1770065
theorem B786827 : Blo 523799 786827 := bstep (se 1 (by rfl) ⟨590120, by rfl⟩ : syracuseStep 786827 = 1180241) B1180241
theorem B524683 : Blo 523799 524683 := bstep (se 1 (by rfl) ⟨393512, by rfl⟩ : syracuseStep 524683 = 787025) B787025
theorem B786839 : Blo 523799 786839 := bstep (se 1 (by rfl) ⟨590129, by rfl⟩ : syracuseStep 786839 = 1180259) B1180259
theorem B524695 : Blo 523799 524695 := bstep (se 1 (by rfl) ⟨393521, by rfl⟩ : syracuseStep 524695 = 787043) B787043
theorem B590251 : Blo 523799 590251 := bstep (se 1 (by rfl) ⟨442688, by rfl⟩ : syracuseStep 590251 = 885377) B885377
theorem B524715 : Blo 523799 524715 := bstep (se 1 (by rfl) ⟨393536, by rfl⟩ : syracuseStep 524715 = 787073) B787073
theorem B524727 : Blo 523799 524727 := bstep (se 1 (by rfl) ⟨393545, by rfl⟩ : syracuseStep 524727 = 787091) B787091
theorem B1180097 : Blo 523799 1180097 := bstep (se 2 (by rfl) ⟨442536, by rfl⟩ : syracuseStep 1180097 = 885073) B885073
theorem B524747 : Blo 523799 524747 := bstep (se 1 (by rfl) ⟨393560, by rfl⟩ : syracuseStep 524747 = 787121) B787121
theorem B524759 : Blo 523799 524759 := bstep (se 1 (by rfl) ⟨393569, by rfl⟩ : syracuseStep 524759 = 787139) B787139
theorem B786905 : Blo 523799 786905 := bstep (se 2 (by rfl) ⟨295089, by rfl⟩ : syracuseStep 786905 = 590179) B590179
theorem B524779 : Blo 523799 524779 := bstep (se 1 (by rfl) ⟨393584, by rfl⟩ : syracuseStep 524779 = 787169) B787169
theorem B524791 : Blo 523799 524791 := bstep (se 1 (by rfl) ⟨393593, by rfl⟩ : syracuseStep 524791 = 787187) B787187
theorem B524811 : Blo 523799 524811 := bstep (se 1 (by rfl) ⟨393608, by rfl⟩ : syracuseStep 524811 = 787217) B787217
theorem B590359 : Blo 523799 590359 := bstep (se 1 (by rfl) ⟨442769, by rfl⟩ : syracuseStep 590359 = 885539) B885539
theorem B524823 : Blo 523799 524823 := bstep (se 1 (by rfl) ⟨393617, by rfl⟩ : syracuseStep 524823 = 787235) B787235
theorem B524843 : Blo 523799 524843 := bstep (se 1 (by rfl) ⟨393632, by rfl⟩ : syracuseStep 524843 = 787265) B787265
theorem B524855 : Blo 523799 524855 := bstep (se 1 (by rfl) ⟨393641, by rfl⟩ : syracuseStep 524855 = 787283) B787283
theorem B885323 : Blo 523799 885323 := bstep (se 1 (by rfl) ⟨663992, by rfl⟩ : syracuseStep 885323 = 1327985) B1327985
theorem B787019 : Blo 523799 787019 := bstep (se 1 (by rfl) ⟨590264, by rfl⟩ : syracuseStep 787019 = 1180529) B1180529
theorem B524875 : Blo 523799 524875 := bstep (se 1 (by rfl) ⟨393656, by rfl⟩ : syracuseStep 524875 = 787313) B787313
theorem B787031 : Blo 523799 787031 := bstep (se 1 (by rfl) ⟨590273, by rfl⟩ : syracuseStep 787031 = 1180547) B1180547
theorem B524887 : Blo 523799 524887 := bstep (se 1 (by rfl) ⟨393665, by rfl⟩ : syracuseStep 524887 = 787331) B787331
theorem B524907 : Blo 523799 524907 := bstep (se 1 (by rfl) ⟨393680, by rfl⟩ : syracuseStep 524907 = 787361) B787361
theorem B524919 : Blo 523799 524919 := bstep (se 1 (by rfl) ⟨393689, by rfl⟩ : syracuseStep 524919 = 787379) B787379
theorem B524939 : Blo 523799 524939 := bstep (se 1 (by rfl) ⟨393704, by rfl⟩ : syracuseStep 524939 = 787409) B787409
theorem B524951 : Blo 523799 524951 := bstep (se 1 (by rfl) ⟨393713, by rfl⟩ : syracuseStep 524951 = 787427) B787427
theorem B1999511 : Blo 523799 1999511 := bstep (se 1 (by rfl) ⟨1499633, by rfl⟩ : syracuseStep 1999511 = 2999267) B2999267
theorem B1180313 : Blo 523799 1180313 := bstep (se 2 (by rfl) ⟨442617, by rfl⟩ : syracuseStep 1180313 = 885235) B885235
theorem B787097 : Blo 523799 787097 := bstep (se 2 (by rfl) ⟨295161, by rfl⟩ : syracuseStep 787097 = 590323) B590323
theorem B524971 : Blo 523799 524971 := bstep (se 1 (by rfl) ⟨393728, by rfl⟩ : syracuseStep 524971 = 787457) B787457
theorem B524983 : Blo 523799 524983 := bstep (se 1 (by rfl) ⟨393737, by rfl⟩ : syracuseStep 524983 = 787475) B787475
theorem B885451 : Blo 523799 885451 := bstep (se 1 (by rfl) ⟨664088, by rfl⟩ : syracuseStep 885451 = 1328177) B1328177
theorem B590539 : Blo 523799 590539 := bstep (se 1 (by rfl) ⟨442904, by rfl⟩ : syracuseStep 590539 = 885809) B885809
theorem B525003 : Blo 523799 525003 := bstep (se 1 (by rfl) ⟨393752, by rfl⟩ : syracuseStep 525003 = 787505) B787505
theorem B525015 : Blo 523799 525015 := bstep (se 1 (by rfl) ⟨393761, by rfl⟩ : syracuseStep 525015 = 787523) B787523
theorem B525035 : Blo 523799 525035 := bstep (se 1 (by rfl) ⟨393776, by rfl⟩ : syracuseStep 525035 = 787553) B787553
theorem B1180403 : Blo 523799 1180403 := bstep (se 1 (by rfl) ⟨885302, by rfl⟩ : syracuseStep 1180403 = 1770605) B1770605
theorem B525047 : Blo 523799 525047 := bstep (se 1 (by rfl) ⟨393785, by rfl⟩ : syracuseStep 525047 = 787571) B787571
theorem B787211 : Blo 523799 787211 := bstep (se 1 (by rfl) ⟨590408, by rfl⟩ : syracuseStep 787211 = 1180817) B1180817
theorem B525067 : Blo 523799 525067 := bstep (se 1 (by rfl) ⟨393800, by rfl⟩ : syracuseStep 525067 = 787601) B787601
theorem B1180439 : Blo 523799 1180439 := bstep (se 1 (by rfl) ⟨885329, by rfl⟩ : syracuseStep 1180439 = 1770659) B1770659
theorem B787223 : Blo 523799 787223 := bstep (se 1 (by rfl) ⟨590417, by rfl⟩ : syracuseStep 787223 = 1180835) B1180835
theorem B525079 : Blo 523799 525079 := bstep (se 1 (by rfl) ⟨393809, by rfl⟩ : syracuseStep 525079 = 787619) B787619
theorem B525099 : Blo 523799 525099 := bstep (se 1 (by rfl) ⟨393824, by rfl⟩ : syracuseStep 525099 = 787649) B787649
theorem B590647 : Blo 523799 590647 := bstep (se 1 (by rfl) ⟨442985, by rfl⟩ : syracuseStep 590647 = 885971) B885971
theorem B525111 : Blo 523799 525111 := bstep (se 1 (by rfl) ⟨393833, by rfl⟩ : syracuseStep 525111 = 787667) B787667
theorem B525131 : Blo 523799 525131 := bstep (se 1 (by rfl) ⟨393848, by rfl⟩ : syracuseStep 525131 = 787697) B787697
theorem B525143 : Blo 523799 525143 := bstep (se 1 (by rfl) ⟨393857, by rfl⟩ : syracuseStep 525143 = 787715) B787715
theorem B885593 : Blo 523799 885593 := bstep (se 2 (by rfl) ⟨332097, by rfl⟩ : syracuseStep 885593 = 664195) B664195
theorem B787289 : Blo 523799 787289 := bstep (se 2 (by rfl) ⟨295233, by rfl⟩ : syracuseStep 787289 = 590467) B590467
theorem B525163 : Blo 523799 525163 := bstep (se 1 (by rfl) ⟨393872, by rfl⟩ : syracuseStep 525163 = 787745) B787745
theorem B525175 : Blo 523799 525175 := bstep (se 1 (by rfl) ⟨393881, by rfl⟩ : syracuseStep 525175 = 787763) B787763
theorem B525195 : Blo 523799 525195 := bstep (se 1 (by rfl) ⟨393896, by rfl⟩ : syracuseStep 525195 = 787793) B787793
theorem B525207 : Blo 523799 525207 := bstep (se 1 (by rfl) ⟨393905, by rfl⟩ : syracuseStep 525207 = 787811) B787811
theorem B525227 : Blo 523799 525227 := bstep (se 1 (by rfl) ⟨393920, by rfl⟩ : syracuseStep 525227 = 787841) B787841
theorem B525239 : Blo 523799 525239 := bstep (se 1 (by rfl) ⟨393929, by rfl⟩ : syracuseStep 525239 = 787859) B787859
theorem B1770443 : Blo 523799 1770443 := bstep (se 1 (by rfl) ⟨1327832, by rfl⟩ : syracuseStep 1770443 = 2655665) B2655665
theorem B1180619 : Blo 523799 1180619 := bstep (se 1 (by rfl) ⟨885464, by rfl⟩ : syracuseStep 1180619 = 1770929) B1770929
theorem B787403 : Blo 523799 787403 := bstep (se 1 (by rfl) ⟨590552, by rfl⟩ : syracuseStep 787403 = 1181105) B1181105
theorem B525259 : Blo 523799 525259 := bstep (se 1 (by rfl) ⟨393944, by rfl⟩ : syracuseStep 525259 = 787889) B787889
theorem B787415 : Blo 523799 787415 := bstep (se 1 (by rfl) ⟨590561, by rfl⟩ : syracuseStep 787415 = 1181123) B1181123
theorem B525271 : Blo 523799 525271 := bstep (se 1 (by rfl) ⟨393953, by rfl⟩ : syracuseStep 525271 = 787907) B787907
theorem B885721 : Blo 523799 885721 := bstep (se 2 (by rfl) ⟨332145, by rfl⟩ : syracuseStep 885721 = 664291) B664291
theorem B590827 : Blo 523799 590827 := bstep (se 1 (by rfl) ⟨443120, by rfl⟩ : syracuseStep 590827 = 886241) B886241
theorem B525291 : Blo 523799 525291 := bstep (se 1 (by rfl) ⟨393968, by rfl⟩ : syracuseStep 525291 = 787937) B787937
theorem B525303 : Blo 523799 525303 := bstep (se 1 (by rfl) ⟨393977, by rfl⟩ : syracuseStep 525303 = 787955) B787955
theorem B1180673 : Blo 523799 1180673 := bstep (se 2 (by rfl) ⟨442752, by rfl⟩ : syracuseStep 1180673 = 885505) B885505
theorem B525323 : Blo 523799 525323 := bstep (se 1 (by rfl) ⟨393992, by rfl⟩ : syracuseStep 525323 = 787985) B787985
theorem B525335 : Blo 523799 525335 := bstep (se 1 (by rfl) ⟨394001, by rfl⟩ : syracuseStep 525335 = 788003) B788003
theorem B787481 : Blo 523799 787481 := bstep (se 2 (by rfl) ⟨295305, by rfl⟩ : syracuseStep 787481 = 590611) B590611
theorem B525355 : Blo 523799 525355 := bstep (se 1 (by rfl) ⟨394016, by rfl⟩ : syracuseStep 525355 = 788033) B788033
theorem B525367 : Blo 523799 525367 := bstep (se 1 (by rfl) ⟨394025, by rfl⟩ : syracuseStep 525367 = 788051) B788051
theorem B525387 : Blo 523799 525387 := bstep (se 1 (by rfl) ⟨394040, by rfl⟩ : syracuseStep 525387 = 788081) B788081
theorem B590935 : Blo 523799 590935 := bstep (se 1 (by rfl) ⟨443201, by rfl⟩ : syracuseStep 590935 = 886403) B886403
theorem B525399 : Blo 523799 525399 := bstep (se 1 (by rfl) ⟨394049, by rfl⟩ : syracuseStep 525399 = 788099) B788099
theorem B525419 : Blo 523799 525419 := bstep (se 1 (by rfl) ⟨394064, by rfl⟩ : syracuseStep 525419 = 788129) B788129
theorem B525431 : Blo 523799 525431 := bstep (se 1 (by rfl) ⟨394073, by rfl⟩ : syracuseStep 525431 = 788147) B788147
theorem B787595 : Blo 523799 787595 := bstep (se 1 (by rfl) ⟨590696, by rfl⟩ : syracuseStep 787595 = 1181393) B1181393
theorem B525451 : Blo 523799 525451 := bstep (se 1 (by rfl) ⟨394088, by rfl⟩ : syracuseStep 525451 = 788177) B788177
theorem B787607 : Blo 523799 787607 := bstep (se 1 (by rfl) ⟨590705, by rfl⟩ : syracuseStep 787607 = 1181411) B1181411
theorem B525463 : Blo 523799 525463 := bstep (se 1 (by rfl) ⟨394097, by rfl⟩ : syracuseStep 525463 = 788195) B788195
theorem B525483 : Blo 523799 525483 := bstep (se 1 (by rfl) ⟨394112, by rfl⟩ : syracuseStep 525483 = 788225) B788225
theorem B525495 : Blo 523799 525495 := bstep (se 1 (by rfl) ⟨394121, by rfl⟩ : syracuseStep 525495 = 788243) B788243
theorem B525515 : Blo 523799 525515 := bstep (se 1 (by rfl) ⟨394136, by rfl⟩ : syracuseStep 525515 = 788273) B788273
theorem B525527 : Blo 523799 525527 := bstep (se 1 (by rfl) ⟨394145, by rfl⟩ : syracuseStep 525527 = 788291) B788291
theorem B1770713 : Blo 523799 1770713 := bstep (se 2 (by rfl) ⟨664017, by rfl⟩ : syracuseStep 1770713 = 1328035) B1328035
theorem B1180889 : Blo 523799 1180889 := bstep (se 2 (by rfl) ⟨442833, by rfl⟩ : syracuseStep 1180889 = 885667) B885667
theorem B787673 : Blo 523799 787673 := bstep (se 2 (by rfl) ⟨295377, by rfl⟩ : syracuseStep 787673 = 590755) B590755
theorem B525547 : Blo 523799 525547 := bstep (se 1 (by rfl) ⟨394160, by rfl⟩ : syracuseStep 525547 = 788321) B788321
theorem B525559 : Blo 523799 525559 := bstep (se 1 (by rfl) ⟨394169, by rfl⟩ : syracuseStep 525559 = 788339) B788339
theorem B591115 : Blo 523799 591115 := bstep (se 1 (by rfl) ⟨443336, by rfl⟩ : syracuseStep 591115 = 886673) B886673
theorem B525579 : Blo 523799 525579 := bstep (se 1 (by rfl) ⟨394184, by rfl⟩ : syracuseStep 525579 = 788369) B788369
theorem B2131217 : Blo 523799 2131217 := bstep (se 2 (by rfl) ⟨799206, by rfl⟩ : syracuseStep 2131217 = 1598413) B1598413
theorem B525591 : Blo 523799 525591 := bstep (se 1 (by rfl) ⟨394193, by rfl⟩ : syracuseStep 525591 = 788387) B788387
theorem B525611 : Blo 523799 525611 := bstep (se 1 (by rfl) ⟨394208, by rfl⟩ : syracuseStep 525611 = 788417) B788417
theorem B1180979 : Blo 523799 1180979 := bstep (se 1 (by rfl) ⟨885734, by rfl⟩ : syracuseStep 1180979 = 1771469) B1771469
theorem B525623 : Blo 523799 525623 := bstep (se 1 (by rfl) ⟨394217, by rfl⟩ : syracuseStep 525623 = 788435) B788435
theorem B787787 : Blo 523799 787787 := bstep (se 1 (by rfl) ⟨590840, by rfl⟩ : syracuseStep 787787 = 1181681) B1181681
theorem B525643 : Blo 523799 525643 := bstep (se 1 (by rfl) ⟨394232, by rfl⟩ : syracuseStep 525643 = 788465) B788465
theorem B1181015 : Blo 523799 1181015 := bstep (se 1 (by rfl) ⟨885761, by rfl⟩ : syracuseStep 1181015 = 1771523) B1771523
theorem B787799 : Blo 523799 787799 := bstep (se 1 (by rfl) ⟨590849, by rfl⟩ : syracuseStep 787799 = 1181699) B1181699
theorem B525655 : Blo 523799 525655 := bstep (se 1 (by rfl) ⟨394241, by rfl⟩ : syracuseStep 525655 = 788483) B788483
theorem B525675 : Blo 523799 525675 := bstep (se 1 (by rfl) ⟨394256, by rfl⟩ : syracuseStep 525675 = 788513) B788513
theorem B591223 : Blo 523799 591223 := bstep (se 1 (by rfl) ⟨443417, by rfl⟩ : syracuseStep 591223 = 886835) B886835
theorem B525687 : Blo 523799 525687 := bstep (se 1 (by rfl) ⟨394265, by rfl⟩ : syracuseStep 525687 = 788531) B788531
theorem B525707 : Blo 523799 525707 := bstep (se 1 (by rfl) ⟨394280, by rfl⟩ : syracuseStep 525707 = 788561) B788561
theorem B525719 : Blo 523799 525719 := bstep (se 1 (by rfl) ⟨394289, by rfl⟩ : syracuseStep 525719 = 788579) B788579
theorem B787865 : Blo 523799 787865 := bstep (se 2 (by rfl) ⟨295449, by rfl⟩ : syracuseStep 787865 = 590899) B590899
theorem B525739 : Blo 523799 525739 := bstep (se 1 (by rfl) ⟨394304, by rfl⟩ : syracuseStep 525739 = 788609) B788609
theorem B2131379 : Blo 523799 2131379 := bstep (se 1 (by rfl) ⟨1598534, by rfl⟩ : syracuseStep 2131379 = 3197069) B3197069
theorem B525751 : Blo 523799 525751 := bstep (se 1 (by rfl) ⟨394313, by rfl⟩ : syracuseStep 525751 = 788627) B788627
theorem B525771 : Blo 523799 525771 := bstep (se 1 (by rfl) ⟨394328, by rfl⟩ : syracuseStep 525771 = 788657) B788657
theorem B525783 : Blo 523799 525783 := bstep (se 1 (by rfl) ⟨394337, by rfl⟩ : syracuseStep 525783 = 788675) B788675
theorem B525803 : Blo 523799 525803 := bstep (se 1 (by rfl) ⟨394352, by rfl⟩ : syracuseStep 525803 = 788705) B788705
theorem B525815 : Blo 523799 525815 := bstep (se 1 (by rfl) ⟨394361, by rfl⟩ : syracuseStep 525815 = 788723) B788723
theorem B1181195 : Blo 523799 1181195 := bstep (se 1 (by rfl) ⟨885896, by rfl⟩ : syracuseStep 1181195 = 1771793) B1771793
theorem B787979 : Blo 523799 787979 := bstep (se 1 (by rfl) ⟨590984, by rfl⟩ : syracuseStep 787979 = 1181969) B1181969
theorem B525835 : Blo 523799 525835 := bstep (se 1 (by rfl) ⟨394376, by rfl⟩ : syracuseStep 525835 = 788753) B788753
theorem B886295 : Blo 523799 886295 := bstep (se 1 (by rfl) ⟨664721, by rfl⟩ : syracuseStep 886295 = 1329443) B1329443
theorem B787991 : Blo 523799 787991 := bstep (se 1 (by rfl) ⟨590993, by rfl⟩ : syracuseStep 787991 = 1181987) B1181987
theorem B525847 : Blo 523799 525847 := bstep (se 1 (by rfl) ⟨394385, by rfl⟩ : syracuseStep 525847 = 788771) B788771
theorem B591403 : Blo 523799 591403 := bstep (se 1 (by rfl) ⟨443552, by rfl⟩ : syracuseStep 591403 = 887105) B887105
theorem B525867 : Blo 523799 525867 := bstep (se 1 (by rfl) ⟨394400, by rfl⟩ : syracuseStep 525867 = 788801) B788801
theorem B525879 : Blo 523799 525879 := bstep (se 1 (by rfl) ⟨394409, by rfl⟩ : syracuseStep 525879 = 788819) B788819
theorem B1181249 : Blo 523799 1181249 := bstep (se 2 (by rfl) ⟨442968, by rfl⟩ : syracuseStep 1181249 = 885937) B885937
theorem B525899 : Blo 523799 525899 := bstep (se 1 (by rfl) ⟨394424, by rfl⟩ : syracuseStep 525899 = 788849) B788849
theorem B788057 : Blo 523799 788057 := bstep (se 2 (by rfl) ⟨295521, by rfl⟩ : syracuseStep 788057 = 591043) B591043
theorem B525911 : Blo 523799 525911 := bstep (se 1 (by rfl) ⟨394433, by rfl⟩ : syracuseStep 525911 = 788867) B788867
theorem B525931 : Blo 523799 525931 := bstep (se 1 (by rfl) ⟨394448, by rfl⟩ : syracuseStep 525931 = 788897) B788897
theorem B525943 : Blo 523799 525943 := bstep (se 1 (by rfl) ⟨394457, by rfl⟩ : syracuseStep 525943 = 788915) B788915
theorem B5998211 : Blo 523799 5998211 := bstep (se 1 (by rfl) ⟨4498658, by rfl⟩ : syracuseStep 5998211 = 8997317) B8997317
theorem B525963 : Blo 523799 525963 := bstep (se 1 (by rfl) ⟨394472, by rfl⟩ : syracuseStep 525963 = 788945) B788945
theorem B886423 : Blo 523799 886423 := bstep (se 1 (by rfl) ⟨664817, by rfl⟩ : syracuseStep 886423 = 1329635) B1329635
theorem B591511 : Blo 523799 591511 := bstep (se 1 (by rfl) ⟨443633, by rfl⟩ : syracuseStep 591511 = 887267) B887267
theorem B525975 : Blo 523799 525975 := bstep (se 1 (by rfl) ⟨394481, by rfl⟩ : syracuseStep 525975 = 788963) B788963
theorem B525995 : Blo 523799 525995 := bstep (se 1 (by rfl) ⟨394496, by rfl⟩ : syracuseStep 525995 = 788993) B788993
theorem B526007 : Blo 523799 526007 := bstep (se 1 (by rfl) ⟨394505, by rfl⟩ : syracuseStep 526007 = 789011) B789011
theorem B788171 : Blo 523799 788171 := bstep (se 1 (by rfl) ⟨591128, by rfl⟩ : syracuseStep 788171 = 1182257) B1182257
theorem B526027 : Blo 523799 526027 := bstep (se 1 (by rfl) ⟨394520, by rfl⟩ : syracuseStep 526027 = 789041) B789041
theorem B788183 : Blo 523799 788183 := bstep (se 1 (by rfl) ⟨591137, by rfl⟩ : syracuseStep 788183 = 1182275) B1182275
theorem B526039 : Blo 523799 526039 := bstep (se 1 (by rfl) ⟨394529, by rfl⟩ : syracuseStep 526039 = 789059) B789059
theorem B526059 : Blo 523799 526059 := bstep (se 1 (by rfl) ⟨394544, by rfl⟩ : syracuseStep 526059 = 789089) B789089
theorem B526071 : Blo 523799 526071 := bstep (se 1 (by rfl) ⟨394553, by rfl⟩ : syracuseStep 526071 = 789107) B789107
theorem B526091 : Blo 523799 526091 := bstep (se 1 (by rfl) ⟨394568, by rfl⟩ : syracuseStep 526091 = 789137) B789137
theorem B526103 : Blo 523799 526103 := bstep (se 1 (by rfl) ⟨394577, by rfl⟩ : syracuseStep 526103 = 789155) B789155
theorem B1181465 : Blo 523799 1181465 := bstep (se 2 (by rfl) ⟨443049, by rfl⟩ : syracuseStep 1181465 = 886099) B886099
theorem B788249 : Blo 523799 788249 := bstep (se 2 (by rfl) ⟨295593, by rfl⟩ : syracuseStep 788249 = 591187) B591187
theorem B526123 : Blo 523799 526123 := bstep (se 1 (by rfl) ⟨394592, by rfl⟩ : syracuseStep 526123 = 789185) B789185
theorem B526135 : Blo 523799 526135 := bstep (se 1 (by rfl) ⟨394601, by rfl⟩ : syracuseStep 526135 = 789203) B789203
theorem B591691 : Blo 523799 591691 := bstep (se 1 (by rfl) ⟨443768, by rfl⟩ : syracuseStep 591691 = 887537) B887537
theorem B526155 : Blo 523799 526155 := bstep (se 1 (by rfl) ⟨394616, by rfl⟩ : syracuseStep 526155 = 789233) B789233
theorem B526167 : Blo 523799 526167 := bstep (se 1 (by rfl) ⟨394625, by rfl⟩ : syracuseStep 526167 = 789251) B789251
theorem B526187 : Blo 523799 526187 := bstep (se 1 (by rfl) ⟨394640, by rfl⟩ : syracuseStep 526187 = 789281) B789281
theorem B1181555 : Blo 523799 1181555 := bstep (se 1 (by rfl) ⟨886166, by rfl⟩ : syracuseStep 1181555 = 1772333) B1772333
theorem B526199 : Blo 523799 526199 := bstep (se 1 (by rfl) ⟨394649, by rfl⟩ : syracuseStep 526199 = 789299) B789299
theorem B2000771 : Blo 523799 2000771 := bstep (se 1 (by rfl) ⟨1500578, by rfl⟩ : syracuseStep 2000771 = 3001157) B3001157
theorem B788363 : Blo 523799 788363 := bstep (se 1 (by rfl) ⟨591272, by rfl⟩ : syracuseStep 788363 = 1182545) B1182545
theorem B526219 : Blo 523799 526219 := bstep (se 1 (by rfl) ⟨394664, by rfl⟩ : syracuseStep 526219 = 789329) B789329
theorem B526231 : Blo 523799 526231 := bstep (se 1 (by rfl) ⟨394673, by rfl⟩ : syracuseStep 526231 = 789347) B789347
theorem B2656151 : Blo 523799 2656151 := bstep (se 1 (by rfl) ⟨1992113, by rfl⟩ : syracuseStep 2656151 = 3984227) B3984227
theorem B1771415 : Blo 523799 1771415 := bstep (se 1 (by rfl) ⟨1328561, by rfl⟩ : syracuseStep 1771415 = 2657123) B2657123
theorem B1181591 : Blo 523799 1181591 := bstep (se 1 (by rfl) ⟨886193, by rfl⟩ : syracuseStep 1181591 = 1772387) B1772387
theorem B788375 : Blo 523799 788375 := bstep (se 1 (by rfl) ⟨591281, by rfl⟩ : syracuseStep 788375 = 1182563) B1182563
theorem B526251 : Blo 523799 526251 := bstep (se 1 (by rfl) ⟨394688, by rfl⟩ : syracuseStep 526251 = 789377) B789377
theorem B591799 : Blo 523799 591799 := bstep (se 1 (by rfl) ⟨443849, by rfl⟩ : syracuseStep 591799 = 887699) B887699
theorem B526263 : Blo 523799 526263 := bstep (se 1 (by rfl) ⟨394697, by rfl⟩ : syracuseStep 526263 = 789395) B789395
theorem B526283 : Blo 523799 526283 := bstep (se 1 (by rfl) ⟨394712, by rfl⟩ : syracuseStep 526283 = 789425) B789425
theorem B526295 : Blo 523799 526295 := bstep (se 1 (by rfl) ⟨394721, by rfl⟩ : syracuseStep 526295 = 789443) B789443
theorem B788441 : Blo 523799 788441 := bstep (se 2 (by rfl) ⟨295665, by rfl⟩ : syracuseStep 788441 = 591331) B591331
theorem B526315 : Blo 523799 526315 := bstep (se 1 (by rfl) ⟨394736, by rfl⟩ : syracuseStep 526315 = 789473) B789473
theorem B526327 : Blo 523799 526327 := bstep (se 1 (by rfl) ⟨394745, by rfl⟩ : syracuseStep 526327 = 789491) B789491
theorem B526347 : Blo 523799 526347 := bstep (se 1 (by rfl) ⟨394760, by rfl⟩ : syracuseStep 526347 = 789521) B789521
theorem B526359 : Blo 523799 526359 := bstep (se 1 (by rfl) ⟨394769, by rfl⟩ : syracuseStep 526359 = 789539) B789539
theorem B3999779 : Blo 523799 3999779 := bstep (se 1 (by rfl) ⟨2999834, by rfl⟩ : syracuseStep 3999779 = 5999669) B5999669
theorem B526379 : Blo 523799 526379 := bstep (se 1 (by rfl) ⟨394784, by rfl⟩ : syracuseStep 526379 = 789569) B789569
theorem B526391 : Blo 523799 526391 := bstep (se 1 (by rfl) ⟨394793, by rfl⟩ : syracuseStep 526391 = 789587) B789587
theorem B1181771 : Blo 523799 1181771 := bstep (se 1 (by rfl) ⟨886328, by rfl⟩ : syracuseStep 1181771 = 1772657) B1772657
theorem B788555 : Blo 523799 788555 := bstep (se 1 (by rfl) ⟨591416, by rfl⟩ : syracuseStep 788555 = 1182833) B1182833
theorem B526411 : Blo 523799 526411 := bstep (se 1 (by rfl) ⟨394808, by rfl⟩ : syracuseStep 526411 = 789617) B789617
theorem B788567 : Blo 523799 788567 := bstep (se 1 (by rfl) ⟨591425, by rfl⟩ : syracuseStep 788567 = 1182851) B1182851
theorem B526423 : Blo 523799 526423 := bstep (se 1 (by rfl) ⟨394817, by rfl⟩ : syracuseStep 526423 = 789635) B789635
theorem B591979 : Blo 523799 591979 := bstep (se 1 (by rfl) ⟨443984, by rfl⟩ : syracuseStep 591979 = 887969) B887969
theorem B526443 : Blo 523799 526443 := bstep (se 1 (by rfl) ⟨394832, by rfl⟩ : syracuseStep 526443 = 789665) B789665
theorem B526455 : Blo 523799 526455 := bstep (se 1 (by rfl) ⟨394841, by rfl⟩ : syracuseStep 526455 = 789683) B789683
theorem B1181825 : Blo 523799 1181825 := bstep (se 2 (by rfl) ⟨443184, by rfl⟩ : syracuseStep 1181825 = 886369) B886369
theorem B526475 : Blo 523799 526475 := bstep (se 1 (by rfl) ⟨394856, by rfl⟩ : syracuseStep 526475 = 789713) B789713
theorem B526487 : Blo 523799 526487 := bstep (se 1 (by rfl) ⟨394865, by rfl⟩ : syracuseStep 526487 = 789731) B789731
theorem B788633 : Blo 523799 788633 := bstep (se 2 (by rfl) ⟨295737, by rfl⟩ : syracuseStep 788633 = 591475) B591475
theorem B526507 : Blo 523799 526507 := bstep (se 1 (by rfl) ⟨394880, by rfl⟩ : syracuseStep 526507 = 789761) B789761
theorem B7604405 : Blo 523799 7604405 := bstep (se 5 (by rfl) ⟨356456, by rfl⟩ : syracuseStep 7604405 = 712913) B712913
theorem B526519 : Blo 523799 526519 := bstep (se 1 (by rfl) ⟨394889, by rfl⟩ : syracuseStep 526519 = 789779) B789779
theorem B526539 : Blo 523799 526539 := bstep (se 1 (by rfl) ⟨394904, by rfl⟩ : syracuseStep 526539 = 789809) B789809
theorem B592087 : Blo 523799 592087 := bstep (se 1 (by rfl) ⟨444065, by rfl⟩ : syracuseStep 592087 = 888131) B888131
theorem B526551 : Blo 523799 526551 := bstep (se 1 (by rfl) ⟨394913, by rfl⟩ : syracuseStep 526551 = 789827) B789827
theorem B526571 : Blo 523799 526571 := bstep (se 1 (by rfl) ⟨394928, by rfl⟩ : syracuseStep 526571 = 789857) B789857
theorem B526583 : Blo 523799 526583 := bstep (se 1 (by rfl) ⟨394937, by rfl⟩ : syracuseStep 526583 = 789875) B789875
theorem B887051 : Blo 523799 887051 := bstep (se 1 (by rfl) ⟨665288, by rfl⟩ : syracuseStep 887051 = 1330577) B1330577
theorem B788747 : Blo 523799 788747 := bstep (se 1 (by rfl) ⟨591560, by rfl⟩ : syracuseStep 788747 = 1183121) B1183121
theorem B526603 : Blo 523799 526603 := bstep (se 1 (by rfl) ⟨394952, by rfl⟩ : syracuseStep 526603 = 789905) B789905
theorem B788759 : Blo 523799 788759 := bstep (se 1 (by rfl) ⟨591569, by rfl⟩ : syracuseStep 788759 = 1183139) B1183139
theorem B526615 : Blo 523799 526615 := bstep (se 1 (by rfl) ⟨394961, by rfl⟩ : syracuseStep 526615 = 789923) B789923
theorem B526635 : Blo 523799 526635 := bstep (se 1 (by rfl) ⟨394976, by rfl⟩ : syracuseStep 526635 = 789953) B789953
theorem B526647 : Blo 523799 526647 := bstep (se 1 (by rfl) ⟨394985, by rfl⟩ : syracuseStep 526647 = 789971) B789971
theorem B5409089 : Blo 523799 5409089 := bstep (se 2 (by rfl) ⟨2028408, by rfl⟩ : syracuseStep 5409089 = 4056817) B4056817
theorem B526667 : Blo 523799 526667 := bstep (se 1 (by rfl) ⟨395000, by rfl⟩ : syracuseStep 526667 = 790001) B790001
theorem B526679 : Blo 523799 526679 := bstep (se 1 (by rfl) ⟨395009, by rfl⟩ : syracuseStep 526679 = 790019) B790019
theorem B1182041 : Blo 523799 1182041 := bstep (se 2 (by rfl) ⟨443265, by rfl⟩ : syracuseStep 1182041 = 886531) B886531
theorem B788825 : Blo 523799 788825 := bstep (se 2 (by rfl) ⟨295809, by rfl⟩ : syracuseStep 788825 = 591619) B591619
theorem B526699 : Blo 523799 526699 := bstep (se 1 (by rfl) ⟨395024, by rfl⟩ : syracuseStep 526699 = 790049) B790049
theorem B526711 : Blo 523799 526711 := bstep (se 1 (by rfl) ⟨395033, by rfl⟩ : syracuseStep 526711 = 790067) B790067
theorem B887179 : Blo 523799 887179 := bstep (se 1 (by rfl) ⟨665384, by rfl⟩ : syracuseStep 887179 = 1330769) B1330769
theorem B592267 : Blo 523799 592267 := bstep (se 1 (by rfl) ⟨444200, by rfl⟩ : syracuseStep 592267 = 888401) B888401
theorem B526731 : Blo 523799 526731 := bstep (se 1 (by rfl) ⟨395048, by rfl⟩ : syracuseStep 526731 = 790097) B790097
theorem B526743 : Blo 523799 526743 := bstep (se 1 (by rfl) ⟨395057, by rfl⟩ : syracuseStep 526743 = 790115) B790115
theorem B526763 : Blo 523799 526763 := bstep (se 1 (by rfl) ⟨395072, by rfl⟩ : syracuseStep 526763 = 790145) B790145
theorem B1771955 : Blo 523799 1771955 := bstep (se 1 (by rfl) ⟨1328966, by rfl⟩ : syracuseStep 1771955 = 2657933) B2657933
theorem B1182131 : Blo 523799 1182131 := bstep (se 1 (by rfl) ⟨886598, by rfl⟩ : syracuseStep 1182131 = 1773197) B1773197
theorem B526775 : Blo 523799 526775 := bstep (se 1 (by rfl) ⟨395081, by rfl⟩ : syracuseStep 526775 = 790163) B790163
theorem B788939 : Blo 523799 788939 := bstep (se 1 (by rfl) ⟨591704, by rfl⟩ : syracuseStep 788939 = 1183409) B1183409
theorem B526795 : Blo 523799 526795 := bstep (se 1 (by rfl) ⟨395096, by rfl⟩ : syracuseStep 526795 = 790193) B790193
theorem B1182167 : Blo 523799 1182167 := bstep (se 1 (by rfl) ⟨886625, by rfl⟩ : syracuseStep 1182167 = 1773251) B1773251
theorem B788951 : Blo 523799 788951 := bstep (se 1 (by rfl) ⟨591713, by rfl⟩ : syracuseStep 788951 = 1183427) B1183427
theorem B526807 : Blo 523799 526807 := bstep (se 1 (by rfl) ⟨395105, by rfl⟩ : syracuseStep 526807 = 790211) B790211
theorem B559595 : Blo 523799 559595 := bstep (se 1 (by rfl) ⟨419696, by rfl⟩ : syracuseStep 559595 = 839393) B839393
theorem B526827 : Blo 523799 526827 := bstep (se 1 (by rfl) ⟨395120, by rfl⟩ : syracuseStep 526827 = 790241) B790241
theorem B592375 : Blo 523799 592375 := bstep (se 1 (by rfl) ⟨444281, by rfl⟩ : syracuseStep 592375 = 888563) B888563
theorem B526839 : Blo 523799 526839 := bstep (se 1 (by rfl) ⟨395129, by rfl⟩ : syracuseStep 526839 = 790259) B790259
theorem B526859 : Blo 523799 526859 := bstep (se 1 (by rfl) ⟨395144, by rfl⟩ : syracuseStep 526859 = 790289) B790289
theorem B526871 : Blo 523799 526871 := bstep (se 1 (by rfl) ⟨395153, by rfl⟩ : syracuseStep 526871 = 790307) B790307
theorem B887321 : Blo 523799 887321 := bstep (se 2 (by rfl) ⟨332745, by rfl⟩ : syracuseStep 887321 = 665491) B665491
theorem B789017 : Blo 523799 789017 := bstep (se 2 (by rfl) ⟨295881, by rfl⟩ : syracuseStep 789017 = 591763) B591763
theorem B526891 : Blo 523799 526891 := bstep (se 1 (by rfl) ⟨395168, by rfl⟩ : syracuseStep 526891 = 790337) B790337
theorem B526903 : Blo 523799 526903 := bstep (se 1 (by rfl) ⟨395177, by rfl⟩ : syracuseStep 526903 = 790355) B790355
theorem B526923 : Blo 523799 526923 := bstep (se 1 (by rfl) ⟨395192, by rfl⟩ : syracuseStep 526923 = 790385) B790385
theorem B526935 : Blo 523799 526935 := bstep (se 1 (by rfl) ⟨395201, by rfl⟩ : syracuseStep 526935 = 790403) B790403
theorem B526955 : Blo 523799 526955 := bstep (se 1 (by rfl) ⟨395216, by rfl⟩ : syracuseStep 526955 = 790433) B790433
theorem B526967 : Blo 523799 526967 := bstep (se 1 (by rfl) ⟨395225, by rfl⟩ : syracuseStep 526967 = 790451) B790451
theorem B5048963 : Blo 523799 5048963 := bstep (se 1 (by rfl) ⟨3786722, by rfl⟩ : syracuseStep 5048963 = 7573445) B7573445
theorem B10783363 : Blo 523799 10783363 := bstep (se 1 (by rfl) ⟨8087522, by rfl⟩ : syracuseStep 10783363 = 16175045) B16175045
theorem B7604867 : Blo 523799 7604867 := bstep (se 1 (by rfl) ⟨5703650, by rfl⟩ : syracuseStep 7604867 = 11407301) B11407301
theorem B1182347 : Blo 523799 1182347 := bstep (se 1 (by rfl) ⟨886760, by rfl⟩ : syracuseStep 1182347 = 1773521) B1773521
theorem B789131 : Blo 523799 789131 := bstep (se 1 (by rfl) ⟨591848, by rfl⟩ : syracuseStep 789131 = 1183697) B1183697
theorem B526987 : Blo 523799 526987 := bstep (se 1 (by rfl) ⟨395240, by rfl⟩ : syracuseStep 526987 = 790481) B790481
theorem B789143 : Blo 523799 789143 := bstep (se 1 (by rfl) ⟨591857, by rfl⟩ : syracuseStep 789143 = 1183715) B1183715
theorem B526999 : Blo 523799 526999 := bstep (se 1 (by rfl) ⟨395249, by rfl⟩ : syracuseStep 526999 = 790499) B790499
theorem B887449 : Blo 523799 887449 := bstep (se 2 (by rfl) ⟨332793, by rfl⟩ : syracuseStep 887449 = 665587) B665587
theorem B592555 : Blo 523799 592555 := bstep (se 1 (by rfl) ⟨444416, by rfl⟩ : syracuseStep 592555 = 888833) B888833
theorem B527019 : Blo 523799 527019 := bstep (se 1 (by rfl) ⟨395264, by rfl⟩ : syracuseStep 527019 = 790529) B790529
theorem B527031 : Blo 523799 527031 := bstep (se 1 (by rfl) ⟨395273, by rfl⟩ : syracuseStep 527031 = 790547) B790547
theorem B1772225 : Blo 523799 1772225 := bstep (se 2 (by rfl) ⟨664584, by rfl⟩ : syracuseStep 1772225 = 1329169) B1329169
theorem B1182401 : Blo 523799 1182401 := bstep (se 2 (by rfl) ⟨443400, by rfl⟩ : syracuseStep 1182401 = 886801) B886801
theorem B527051 : Blo 523799 527051 := bstep (se 1 (by rfl) ⟨395288, by rfl⟩ : syracuseStep 527051 = 790577) B790577
theorem B527063 : Blo 523799 527063 := bstep (se 1 (by rfl) ⟨395297, by rfl⟩ : syracuseStep 527063 = 790595) B790595
theorem B789209 : Blo 523799 789209 := bstep (se 2 (by rfl) ⟨295953, by rfl⟩ : syracuseStep 789209 = 591907) B591907
theorem B527083 : Blo 523799 527083 := bstep (se 1 (by rfl) ⟨395312, by rfl⟩ : syracuseStep 527083 = 790625) B790625
theorem B527095 : Blo 523799 527095 := bstep (se 1 (by rfl) ⟨395321, by rfl⟩ : syracuseStep 527095 = 790643) B790643
theorem B527115 : Blo 523799 527115 := bstep (se 1 (by rfl) ⟨395336, by rfl⟩ : syracuseStep 527115 = 790673) B790673
theorem B592663 : Blo 523799 592663 := bstep (se 1 (by rfl) ⟨444497, by rfl⟩ : syracuseStep 592663 = 888995) B888995
theorem B527127 : Blo 523799 527127 := bstep (se 1 (by rfl) ⟨395345, by rfl⟩ : syracuseStep 527127 = 790691) B790691
theorem B527147 : Blo 523799 527147 := bstep (se 1 (by rfl) ⟨395360, by rfl⟩ : syracuseStep 527147 = 790721) B790721
theorem B527159 : Blo 523799 527159 := bstep (se 1 (by rfl) ⟨395369, by rfl⟩ : syracuseStep 527159 = 790739) B790739
theorem B789323 : Blo 523799 789323 := bstep (se 1 (by rfl) ⟨591992, by rfl⟩ : syracuseStep 789323 = 1183985) B1183985
theorem B527179 : Blo 523799 527179 := bstep (se 1 (by rfl) ⟨395384, by rfl⟩ : syracuseStep 527179 = 790769) B790769
theorem B789335 : Blo 523799 789335 := bstep (se 1 (by rfl) ⟨592001, by rfl⟩ : syracuseStep 789335 = 1184003) B1184003
theorem B527191 : Blo 523799 527191 := bstep (se 1 (by rfl) ⟨395393, by rfl⟩ : syracuseStep 527191 = 790787) B790787
theorem B5671781 : Blo 523799 5671781 := bstep (se 4 (by rfl) ⟨531729, by rfl⟩ : syracuseStep 5671781 = 1063459) B1063459
theorem B527211 : Blo 523799 527211 := bstep (se 1 (by rfl) ⟨395408, by rfl⟩ : syracuseStep 527211 = 790817) B790817
theorem B527223 : Blo 523799 527223 := bstep (se 1 (by rfl) ⟨395417, by rfl⟩ : syracuseStep 527223 = 790835) B790835
theorem B527243 : Blo 523799 527243 := bstep (se 1 (by rfl) ⟨395432, by rfl⟩ : syracuseStep 527243 = 790865) B790865
theorem B527255 : Blo 523799 527255 := bstep (se 1 (by rfl) ⟨395441, by rfl⟩ : syracuseStep 527255 = 790883) B790883
theorem B1182617 : Blo 523799 1182617 := bstep (se 2 (by rfl) ⟨443481, by rfl⟩ : syracuseStep 1182617 = 886963) B886963
theorem B789401 : Blo 523799 789401 := bstep (se 2 (by rfl) ⟨296025, by rfl⟩ : syracuseStep 789401 = 592051) B592051
theorem B527275 : Blo 523799 527275 := bstep (se 1 (by rfl) ⟨395456, by rfl⟩ : syracuseStep 527275 = 790913) B790913
theorem B527287 : Blo 523799 527287 := bstep (se 1 (by rfl) ⟨395465, by rfl⟩ : syracuseStep 527287 = 790931) B790931
theorem B592843 : Blo 523799 592843 := bstep (se 1 (by rfl) ⟨444632, by rfl⟩ : syracuseStep 592843 = 889265) B889265
theorem B527307 : Blo 523799 527307 := bstep (se 1 (by rfl) ⟨395480, by rfl⟩ : syracuseStep 527307 = 790961) B790961
theorem B527319 : Blo 523799 527319 := bstep (se 1 (by rfl) ⟨395489, by rfl⟩ : syracuseStep 527319 = 790979) B790979
theorem B527339 : Blo 523799 527339 := bstep (se 1 (by rfl) ⟨395504, by rfl⟩ : syracuseStep 527339 = 791009) B791009
theorem B1182707 : Blo 523799 1182707 := bstep (se 1 (by rfl) ⟨887030, by rfl⟩ : syracuseStep 1182707 = 1774061) B1774061
theorem B527351 : Blo 523799 527351 := bstep (se 1 (by rfl) ⟨395513, by rfl⟩ : syracuseStep 527351 = 791027) B791027
theorem B789515 : Blo 523799 789515 := bstep (se 1 (by rfl) ⟨592136, by rfl⟩ : syracuseStep 789515 = 1184273) B1184273
theorem B527371 : Blo 523799 527371 := bstep (se 1 (by rfl) ⟨395528, by rfl⟩ : syracuseStep 527371 = 791057) B791057
theorem B1182743 : Blo 523799 1182743 := bstep (se 1 (by rfl) ⟨887057, by rfl⟩ : syracuseStep 1182743 = 1774115) B1774115
theorem B789527 : Blo 523799 789527 := bstep (se 1 (by rfl) ⟨592145, by rfl⟩ : syracuseStep 789527 = 1184291) B1184291
theorem B527383 : Blo 523799 527383 := bstep (se 1 (by rfl) ⟨395537, by rfl⟩ : syracuseStep 527383 = 791075) B791075
theorem B527403 : Blo 523799 527403 := bstep (se 1 (by rfl) ⟨395552, by rfl⟩ : syracuseStep 527403 = 791105) B791105
theorem B592951 : Blo 523799 592951 := bstep (se 1 (by rfl) ⟨444713, by rfl⟩ : syracuseStep 592951 = 889427) B889427
theorem B527415 : Blo 523799 527415 := bstep (se 1 (by rfl) ⟨395561, by rfl⟩ : syracuseStep 527415 = 791123) B791123
theorem B527435 : Blo 523799 527435 := bstep (se 1 (by rfl) ⟨395576, by rfl⟩ : syracuseStep 527435 = 791153) B791153
theorem B527447 : Blo 523799 527447 := bstep (se 1 (by rfl) ⟨395585, by rfl⟩ : syracuseStep 527447 = 791171) B791171
theorem B789593 : Blo 523799 789593 := bstep (se 2 (by rfl) ⟨296097, by rfl⟩ : syracuseStep 789593 = 592195) B592195
theorem B527467 : Blo 523799 527467 := bstep (se 1 (by rfl) ⟨395600, by rfl⟩ : syracuseStep 527467 = 791201) B791201
theorem B527479 : Blo 523799 527479 := bstep (se 1 (by rfl) ⟨395609, by rfl⟩ : syracuseStep 527479 = 791219) B791219
theorem B527499 : Blo 523799 527499 := bstep (se 1 (by rfl) ⟨395624, by rfl⟩ : syracuseStep 527499 = 791249) B791249
theorem B527511 : Blo 523799 527511 := bstep (se 1 (by rfl) ⟨395633, by rfl⟩ : syracuseStep 527511 = 791267) B791267
theorem B527531 : Blo 523799 527531 := bstep (se 1 (by rfl) ⟨395648, by rfl⟩ : syracuseStep 527531 = 791297) B791297
theorem B527543 : Blo 523799 527543 := bstep (se 1 (by rfl) ⟨395657, by rfl⟩ : syracuseStep 527543 = 791315) B791315
theorem B1182923 : Blo 523799 1182923 := bstep (se 1 (by rfl) ⟨887192, by rfl⟩ : syracuseStep 1182923 = 1774385) B1774385
theorem B789707 : Blo 523799 789707 := bstep (se 1 (by rfl) ⟨592280, by rfl⟩ : syracuseStep 789707 = 1184561) B1184561
theorem B527563 : Blo 523799 527563 := bstep (se 1 (by rfl) ⟨395672, by rfl⟩ : syracuseStep 527563 = 791345) B791345
theorem B888023 : Blo 523799 888023 := bstep (se 1 (by rfl) ⟨666017, by rfl⟩ : syracuseStep 888023 = 1332035) B1332035
theorem B789719 : Blo 523799 789719 := bstep (se 1 (by rfl) ⟨592289, by rfl⟩ : syracuseStep 789719 = 1184579) B1184579
theorem B527575 : Blo 523799 527575 := bstep (se 1 (by rfl) ⟨395681, by rfl⟩ : syracuseStep 527575 = 791363) B791363
theorem B1772765 : Blo 523799 1772765 := bstep (se 3 (by rfl) ⟨332393, by rfl⟩ : syracuseStep 1772765 = 664787) B664787
theorem B593131 : Blo 523799 593131 := bstep (se 1 (by rfl) ⟨444848, by rfl⟩ : syracuseStep 593131 = 889697) B889697
theorem B527595 : Blo 523799 527595 := bstep (se 1 (by rfl) ⟨395696, by rfl⟩ : syracuseStep 527595 = 791393) B791393
theorem B527607 : Blo 523799 527607 := bstep (se 1 (by rfl) ⟨395705, by rfl⟩ : syracuseStep 527607 = 791411) B791411
theorem B1182977 : Blo 523799 1182977 := bstep (se 2 (by rfl) ⟨443616, by rfl⟩ : syracuseStep 1182977 = 887233) B887233
theorem B527627 : Blo 523799 527627 := bstep (se 1 (by rfl) ⟨395720, by rfl⟩ : syracuseStep 527627 = 791441) B791441
theorem B527639 : Blo 523799 527639 := bstep (se 1 (by rfl) ⟨395729, by rfl⟩ : syracuseStep 527639 = 791459) B791459
theorem B789785 : Blo 523799 789785 := bstep (se 2 (by rfl) ⟨296169, by rfl⟩ : syracuseStep 789785 = 592339) B592339
theorem B527659 : Blo 523799 527659 := bstep (se 1 (by rfl) ⟨395744, by rfl⟩ : syracuseStep 527659 = 791489) B791489
theorem B527671 : Blo 523799 527671 := bstep (se 1 (by rfl) ⟨395753, by rfl⟩ : syracuseStep 527671 = 791507) B791507
theorem B527691 : Blo 523799 527691 := bstep (se 1 (by rfl) ⟨395768, by rfl⟩ : syracuseStep 527691 = 791537) B791537
theorem B888151 : Blo 523799 888151 := bstep (se 1 (by rfl) ⟨666113, by rfl⟩ : syracuseStep 888151 = 1332227) B1332227
theorem B593239 : Blo 523799 593239 := bstep (se 1 (by rfl) ⟨444929, by rfl⟩ : syracuseStep 593239 = 889859) B889859
theorem B527703 : Blo 523799 527703 := bstep (se 1 (by rfl) ⟨395777, by rfl⟩ : syracuseStep 527703 = 791555) B791555
theorem B527723 : Blo 523799 527723 := bstep (se 1 (by rfl) ⟨395792, by rfl⟩ : syracuseStep 527723 = 791585) B791585
theorem B527735 : Blo 523799 527735 := bstep (se 1 (by rfl) ⟨395801, by rfl⟩ : syracuseStep 527735 = 791603) B791603
theorem B789899 : Blo 523799 789899 := bstep (se 1 (by rfl) ⟨592424, by rfl⟩ : syracuseStep 789899 = 1184849) B1184849
theorem B527755 : Blo 523799 527755 := bstep (se 1 (by rfl) ⟨395816, by rfl⟩ : syracuseStep 527755 = 791633) B791633
theorem B789911 : Blo 523799 789911 := bstep (se 1 (by rfl) ⟨592433, by rfl⟩ : syracuseStep 789911 = 1184867) B1184867
theorem B527767 : Blo 523799 527767 := bstep (se 1 (by rfl) ⟨395825, by rfl⟩ : syracuseStep 527767 = 791651) B791651
theorem B527787 : Blo 523799 527787 := bstep (se 1 (by rfl) ⟨395840, by rfl⟩ : syracuseStep 527787 = 791681) B791681
theorem B527799 : Blo 523799 527799 := bstep (se 1 (by rfl) ⟨395849, by rfl⟩ : syracuseStep 527799 = 791699) B791699
theorem B1183193 : Blo 523799 1183193 := bstep (se 2 (by rfl) ⟨443697, by rfl⟩ : syracuseStep 1183193 = 887395) B887395
theorem B789977 : Blo 523799 789977 := bstep (se 2 (by rfl) ⟨296241, by rfl⟩ : syracuseStep 789977 = 592483) B592483
theorem B593419 : Blo 523799 593419 := bstep (se 1 (by rfl) ⟨445064, by rfl⟩ : syracuseStep 593419 = 890129) B890129
theorem B1183283 : Blo 523799 1183283 := bstep (se 1 (by rfl) ⟨887462, by rfl⟩ : syracuseStep 1183283 = 1774925) B1774925
theorem B790091 : Blo 523799 790091 := bstep (se 1 (by rfl) ⟨592568, by rfl⟩ : syracuseStep 790091 = 1185137) B1185137
theorem B1183319 : Blo 523799 1183319 := bstep (se 1 (by rfl) ⟨887489, by rfl⟩ : syracuseStep 1183319 = 1774979) B1774979
theorem B790103 : Blo 523799 790103 := bstep (se 1 (by rfl) ⟨592577, by rfl⟩ : syracuseStep 790103 = 1185155) B1185155
theorem B593527 : Blo 523799 593527 := bstep (se 1 (by rfl) ⟨445145, by rfl⟩ : syracuseStep 593527 = 890291) B890291
theorem B560791 : Blo 523799 560791 := bstep (se 1 (by rfl) ⟨420593, by rfl⟩ : syracuseStep 560791 = 841187) B841187
theorem B790169 : Blo 523799 790169 := bstep (se 2 (by rfl) ⟨296313, by rfl⟩ : syracuseStep 790169 = 592627) B592627
theorem B2395865 : Blo 523799 2395865 := bstep (se 2 (by rfl) ⟨898449, by rfl⟩ : syracuseStep 2395865 = 1796899) B1796899
theorem B7606021 : Blo 523799 7606021 := bstep (se 4 (by rfl) ⟨713064, by rfl⟩ : syracuseStep 7606021 = 1426129) B1426129
theorem B1183499 : Blo 523799 1183499 := bstep (se 1 (by rfl) ⟨887624, by rfl⟩ : syracuseStep 1183499 = 1775249) B1775249
theorem B790283 : Blo 523799 790283 := bstep (se 1 (by rfl) ⟨592712, by rfl⟩ : syracuseStep 790283 = 1185425) B1185425
theorem B790295 : Blo 523799 790295 := bstep (se 1 (by rfl) ⟨592721, by rfl⟩ : syracuseStep 790295 = 1185443) B1185443
theorem B593707 : Blo 523799 593707 := bstep (se 1 (by rfl) ⟨445280, by rfl⟩ : syracuseStep 593707 = 890561) B890561
theorem B1183553 : Blo 523799 1183553 := bstep (se 2 (by rfl) ⟨443832, by rfl⟩ : syracuseStep 1183553 = 887665) B887665
theorem B790361 : Blo 523799 790361 := bstep (se 2 (by rfl) ⟨296385, by rfl⟩ : syracuseStep 790361 = 592771) B592771
theorem B888779 : Blo 523799 888779 := bstep (se 1 (by rfl) ⟨666584, by rfl⟩ : syracuseStep 888779 = 1333169) B1333169
theorem B790475 : Blo 523799 790475 := bstep (se 1 (by rfl) ⟨592856, by rfl⟩ : syracuseStep 790475 = 1185713) B1185713
theorem B790487 : Blo 523799 790487 := bstep (se 1 (by rfl) ⟨592865, by rfl⟩ : syracuseStep 790487 = 1185731) B1185731
theorem B1183769 : Blo 523799 1183769 := bstep (se 2 (by rfl) ⟨443913, by rfl⟩ : syracuseStep 1183769 = 887827) B887827
theorem B790553 : Blo 523799 790553 := bstep (se 2 (by rfl) ⟨296457, by rfl⟩ : syracuseStep 790553 = 592915) B592915
theorem B2527307 : Blo 523799 2527307 := bstep (se 1 (by rfl) ⟨1895480, by rfl⟩ : syracuseStep 2527307 = 3790961) B3790961
theorem B888907 : Blo 523799 888907 := bstep (se 1 (by rfl) ⟨666680, by rfl⟩ : syracuseStep 888907 = 1333361) B1333361
theorem B9605213 : Blo 523799 9605213 := bstep (se 3 (by rfl) ⟨1800977, by rfl⟩ : syracuseStep 9605213 = 3601955) B3601955
theorem B1183859 : Blo 523799 1183859 := bstep (se 1 (by rfl) ⟨887894, by rfl⟩ : syracuseStep 1183859 = 1775789) B1775789
theorem B790667 : Blo 523799 790667 := bstep (se 1 (by rfl) ⟨593000, by rfl⟩ : syracuseStep 790667 = 1186001) B1186001
theorem B1183895 : Blo 523799 1183895 := bstep (se 1 (by rfl) ⟨887921, by rfl⟩ : syracuseStep 1183895 = 1775843) B1775843
theorem B790679 : Blo 523799 790679 := bstep (se 1 (by rfl) ⟨593009, by rfl⟩ : syracuseStep 790679 = 1186019) B1186019
theorem B17109143 : Blo 523799 17109143 := bstep (se 1 (by rfl) ⟨12831857, by rfl⟩ : syracuseStep 17109143 = 25663715) B25663715
theorem B889049 : Blo 523799 889049 := bstep (se 2 (by rfl) ⟨333393, by rfl⟩ : syracuseStep 889049 = 666787) B666787
theorem B790745 : Blo 523799 790745 := bstep (se 2 (by rfl) ⟨296529, by rfl⟩ : syracuseStep 790745 = 593059) B593059
theorem B7180589 : Blo 523799 7180589 := bstep (se 3 (by rfl) ⟨1346360, by rfl⟩ : syracuseStep 7180589 = 2692721) B2692721
theorem B1773899 : Blo 523799 1773899 := bstep (se 1 (by rfl) ⟨1330424, by rfl⟩ : syracuseStep 1773899 = 2660849) B2660849
theorem B1184075 : Blo 523799 1184075 := bstep (se 1 (by rfl) ⟨888056, by rfl⟩ : syracuseStep 1184075 = 1776113) B1776113
theorem B790859 : Blo 523799 790859 := bstep (se 1 (by rfl) ⟨593144, by rfl⟩ : syracuseStep 790859 = 1186289) B1186289
theorem B790871 : Blo 523799 790871 := bstep (se 1 (by rfl) ⟨593153, by rfl⟩ : syracuseStep 790871 = 1186307) B1186307
theorem B889177 : Blo 523799 889177 := bstep (se 2 (by rfl) ⟨333441, by rfl⟩ : syracuseStep 889177 = 666883) B666883
theorem B1184129 : Blo 523799 1184129 := bstep (se 2 (by rfl) ⟨444048, by rfl⟩ : syracuseStep 1184129 = 888097) B888097
theorem B790937 : Blo 523799 790937 := bstep (se 2 (by rfl) ⟨296601, by rfl⟩ : syracuseStep 790937 = 593203) B593203
theorem B561611 : Blo 523799 561611 := bstep (se 1 (by rfl) ⟨421208, by rfl⟩ : syracuseStep 561611 = 842417) B842417
theorem B791051 : Blo 523799 791051 := bstep (se 1 (by rfl) ⟨593288, by rfl⟩ : syracuseStep 791051 = 1186577) B1186577
theorem B791063 : Blo 523799 791063 := bstep (se 1 (by rfl) ⟨593297, by rfl⟩ : syracuseStep 791063 = 1186595) B1186595
theorem B1774169 : Blo 523799 1774169 := bstep (se 2 (by rfl) ⟨665313, by rfl⟩ : syracuseStep 1774169 = 1330627) B1330627
theorem B1184345 : Blo 523799 1184345 := bstep (se 2 (by rfl) ⟨444129, by rfl⟩ : syracuseStep 1184345 = 888259) B888259
theorem B791129 : Blo 523799 791129 := bstep (se 2 (by rfl) ⟨296673, by rfl⟩ : syracuseStep 791129 = 593347) B593347
theorem B1118873 : Blo 523799 1118873 := bstep (se 2 (by rfl) ⟨419577, by rfl⟩ : syracuseStep 1118873 = 839155) B839155
theorem B1184435 : Blo 523799 1184435 := bstep (se 1 (by rfl) ⟨888326, by rfl⟩ : syracuseStep 1184435 = 1776653) B1776653
theorem B8622773 : Blo 523799 8622773 := bstep (se 5 (by rfl) ⟨404192, by rfl⟩ : syracuseStep 8622773 = 808385) B808385
theorem B791243 : Blo 523799 791243 := bstep (se 1 (by rfl) ⟨593432, by rfl⟩ : syracuseStep 791243 = 1186865) B1186865
theorem B1184471 : Blo 523799 1184471 := bstep (se 1 (by rfl) ⟨888353, by rfl⟩ : syracuseStep 1184471 = 1776707) B1776707
theorem B791255 : Blo 523799 791255 := bstep (se 1 (by rfl) ⟨593441, by rfl⟩ : syracuseStep 791255 = 1186883) B1186883
theorem B791321 : Blo 523799 791321 := bstep (se 2 (by rfl) ⟨296745, by rfl⟩ : syracuseStep 791321 = 593491) B593491
theorem B1184651 : Blo 523799 1184651 := bstep (se 1 (by rfl) ⟨888488, by rfl⟩ : syracuseStep 1184651 = 1776977) B1776977
theorem B791435 : Blo 523799 791435 := bstep (se 1 (by rfl) ⟨593576, by rfl⟩ : syracuseStep 791435 = 1187153) B1187153
theorem B889751 : Blo 523799 889751 := bstep (se 1 (by rfl) ⟨667313, by rfl⟩ : syracuseStep 889751 = 1334627) B1334627
theorem B791447 : Blo 523799 791447 := bstep (se 1 (by rfl) ⟨593585, by rfl⟩ : syracuseStep 791447 = 1187171) B1187171
theorem B2003885 : Blo 523799 2003885 := bstep (se 3 (by rfl) ⟨375728, by rfl⟩ : syracuseStep 2003885 = 751457) B751457
theorem B1184705 : Blo 523799 1184705 := bstep (se 2 (by rfl) ⟨444264, by rfl⟩ : syracuseStep 1184705 = 888529) B888529
theorem B791513 : Blo 523799 791513 := bstep (se 2 (by rfl) ⟨296817, by rfl⟩ : syracuseStep 791513 = 593635) B593635
theorem B889879 : Blo 523799 889879 := bstep (se 1 (by rfl) ⟨667409, by rfl⟩ : syracuseStep 889879 = 1334819) B1334819
theorem B791627 : Blo 523799 791627 := bstep (se 1 (by rfl) ⟨593720, by rfl⟩ : syracuseStep 791627 = 1187441) B1187441
theorem B791639 : Blo 523799 791639 := bstep (se 1 (by rfl) ⟨593729, by rfl⟩ : syracuseStep 791639 = 1187459) B1187459
theorem B2331737 : Blo 523799 2331737 := bstep (se 2 (by rfl) ⟨874401, by rfl⟩ : syracuseStep 2331737 = 1748803) B1748803
theorem B1184921 : Blo 523799 1184921 := bstep (se 2 (by rfl) ⟨444345, by rfl⟩ : syracuseStep 1184921 = 888691) B888691
theorem B1185011 : Blo 523799 1185011 := bstep (se 1 (by rfl) ⟨888758, by rfl⟩ : syracuseStep 1185011 = 1777517) B1777517
theorem B1774871 : Blo 523799 1774871 := bstep (se 1 (by rfl) ⟨1331153, by rfl⟩ : syracuseStep 1774871 = 2662307) B2662307
theorem B1185047 : Blo 523799 1185047 := bstep (se 1 (by rfl) ⟨888785, by rfl⟩ : syracuseStep 1185047 = 1777571) B1777571
theorem B1119539 : Blo 523799 1119539 := bstep (se 1 (by rfl) ⟨839654, by rfl⟩ : syracuseStep 1119539 = 1679309) B1679309
theorem B3380555 : Blo 523799 3380555 := bstep (se 1 (by rfl) ⟨2535416, by rfl⟩ : syracuseStep 3380555 = 5070833) B5070833
theorem B2659715 : Blo 523799 2659715 := bstep (se 1 (by rfl) ⟨1994786, by rfl⟩ : syracuseStep 2659715 = 3989573) B3989573
theorem B2168257 : Blo 523799 2168257 := bstep (se 2 (by rfl) ⟨813096, by rfl⟩ : syracuseStep 2168257 = 1626193) B1626193
theorem B1185227 : Blo 523799 1185227 := bstep (se 1 (by rfl) ⟨888920, by rfl⟩ : syracuseStep 1185227 = 1777841) B1777841
theorem B1185281 : Blo 523799 1185281 := bstep (se 2 (by rfl) ⟨444480, by rfl⟩ : syracuseStep 1185281 = 888961) B888961
theorem B8984195 : Blo 523799 8984195 := bstep (se 1 (by rfl) ⟨6738146, by rfl⟩ : syracuseStep 8984195 = 13476293) B13476293
theorem B890507 : Blo 523799 890507 := bstep (se 1 (by rfl) ⟨667880, by rfl⟩ : syracuseStep 890507 = 1335761) B1335761
theorem B1185497 : Blo 523799 1185497 := bstep (se 2 (by rfl) ⟨444561, by rfl⟩ : syracuseStep 1185497 = 889123) B889123
theorem B890635 : Blo 523799 890635 := bstep (se 1 (by rfl) ⟨667976, by rfl⟩ : syracuseStep 890635 = 1335953) B1335953
theorem B1775411 : Blo 523799 1775411 := bstep (se 1 (by rfl) ⟨1331558, by rfl⟩ : syracuseStep 1775411 = 2663117) B2663117
theorem B1185587 : Blo 523799 1185587 := bstep (se 1 (by rfl) ⟨889190, by rfl⟩ : syracuseStep 1185587 = 1778381) B1778381
theorem B562999 : Blo 523799 562999 := bstep (se 1 (by rfl) ⟨422249, by rfl⟩ : syracuseStep 562999 = 844499) B844499
theorem B1185623 : Blo 523799 1185623 := bstep (se 1 (by rfl) ⟨889217, by rfl⟩ : syracuseStep 1185623 = 1778435) B1778435
theorem B1185803 : Blo 523799 1185803 := bstep (se 1 (by rfl) ⟨889352, by rfl⟩ : syracuseStep 1185803 = 1778705) B1778705
theorem B1775681 : Blo 523799 1775681 := bstep (se 2 (by rfl) ⟨665880, by rfl⟩ : syracuseStep 1775681 = 1331761) B1331761
theorem B1185857 : Blo 523799 1185857 := bstep (se 2 (by rfl) ⟨444696, by rfl⟩ : syracuseStep 1185857 = 889393) B889393
theorem B1022081 : Blo 523799 1022081 := bstep (se 2 (by rfl) ⟨383280, by rfl⟩ : syracuseStep 1022081 = 766561) B766561
theorem B8558723 : Blo 523799 8558723 := bstep (se 1 (by rfl) ⟨6419042, by rfl⟩ : syracuseStep 8558723 = 12838085) B12838085
theorem B1186073 : Blo 523799 1186073 := bstep (se 2 (by rfl) ⟨444777, by rfl⟩ : syracuseStep 1186073 = 889555) B889555
theorem B2988353 : Blo 523799 2988353 := bstep (se 2 (by rfl) ⟨1120632, by rfl⟩ : syracuseStep 2988353 = 2241265) B2241265
theorem B1186163 : Blo 523799 1186163 := bstep (se 1 (by rfl) ⟨889622, by rfl⟩ : syracuseStep 1186163 = 1779245) B1779245
theorem B1186199 : Blo 523799 1186199 := bstep (se 1 (by rfl) ⟨889649, by rfl⟩ : syracuseStep 1186199 = 1779299) B1779299
theorem B1186379 : Blo 523799 1186379 := bstep (se 1 (by rfl) ⟨889784, by rfl⟩ : syracuseStep 1186379 = 1779569) B1779569
theorem B1776221 : Blo 523799 1776221 := bstep (se 3 (by rfl) ⟨333041, by rfl⟩ : syracuseStep 1776221 = 666083) B666083
theorem B1186433 : Blo 523799 1186433 := bstep (se 2 (by rfl) ⟨444912, by rfl⟩ : syracuseStep 1186433 = 889825) B889825
theorem B1121035 : Blo 523799 1121035 := bstep (se 1 (by rfl) ⟨840776, by rfl⟩ : syracuseStep 1121035 = 1681553) B1681553
theorem B1186649 : Blo 523799 1186649 := bstep (se 2 (by rfl) ⟨444993, by rfl⟩ : syracuseStep 1186649 = 889987) B889987
theorem B1186739 : Blo 523799 1186739 := bstep (se 1 (by rfl) ⟨890054, by rfl⟩ : syracuseStep 1186739 = 1780109) B1780109
theorem B1186775 : Blo 523799 1186775 := bstep (se 1 (by rfl) ⟨890081, by rfl⟩ : syracuseStep 1186775 = 1780163) B1780163
theorem B1186955 : Blo 523799 1186955 := bstep (se 1 (by rfl) ⟨890216, by rfl⟩ : syracuseStep 1186955 = 1780433) B1780433
theorem B1187009 : Blo 523799 1187009 := bstep (se 2 (by rfl) ⟨445128, by rfl⟩ : syracuseStep 1187009 = 890257) B890257
theorem B4005125 : Blo 523799 4005125 := bstep (se 4 (by rfl) ⟨375480, by rfl⟩ : syracuseStep 4005125 = 750961) B750961
theorem B1187225 : Blo 523799 1187225 := bstep (se 2 (by rfl) ⟨445209, by rfl⟩ : syracuseStep 1187225 = 890419) B890419
theorem B1187315 : Blo 523799 1187315 := bstep (se 1 (by rfl) ⟨890486, by rfl⟩ : syracuseStep 1187315 = 1780973) B1780973
theorem B3644945 : Blo 523799 3644945 := bstep (se 2 (by rfl) ⟨1366854, by rfl⟩ : syracuseStep 3644945 = 2733709) B2733709
theorem B1187351 : Blo 523799 1187351 := bstep (se 1 (by rfl) ⟨890513, by rfl⟩ : syracuseStep 1187351 = 1781027) B1781027
theorem B1777355 : Blo 523799 1777355 := bstep (se 1 (by rfl) ⟨1333016, by rfl⟩ : syracuseStep 1777355 = 2666033) B2666033
theorem B1187531 : Blo 523799 1187531 := bstep (se 1 (by rfl) ⟨890648, by rfl⟩ : syracuseStep 1187531 = 1781297) B1781297
theorem B663319 : Blo 523799 663319 := bstep (se 1 (by rfl) ⟨497489, by rfl⟩ : syracuseStep 663319 = 994979) B994979
theorem B1777625 : Blo 523799 1777625 := bstep (se 2 (by rfl) ⟨666609, by rfl⟩ : syracuseStep 1777625 = 1333219) B1333219
theorem B1122265 : Blo 523799 1122265 := bstep (se 2 (by rfl) ⟨420849, by rfl⟩ : syracuseStep 1122265 = 841699) B841699
theorem B1679411 : Blo 523799 1679411 := bstep (se 1 (by rfl) ⟨1259558, by rfl⟩ : syracuseStep 1679411 = 2519117) B2519117
theorem B532715 : Blo 523799 532715 := bstep (se 1 (by rfl) ⟨399536, by rfl⟩ : syracuseStep 532715 = 799073) B799073
theorem B7184645 : Blo 523799 7184645 := bstep (se 4 (by rfl) ⟨673560, by rfl⟩ : syracuseStep 7184645 = 1347121) B1347121
theorem B2695517 : Blo 523799 2695517 := bstep (se 3 (by rfl) ⟨505409, by rfl⟩ : syracuseStep 2695517 = 1010819) B1010819
theorem B664139 : Blo 523799 664139 := bstep (se 1 (by rfl) ⟨498104, by rfl⟩ : syracuseStep 664139 = 996209) B996209
theorem B1778327 : Blo 523799 1778327 := bstep (se 1 (by rfl) ⟨1333745, by rfl⟩ : syracuseStep 1778327 = 2667491) B2667491
theorem B2663441 : Blo 523799 2663441 := bstep (se 2 (by rfl) ⟨998790, by rfl⟩ : syracuseStep 2663441 = 1997581) B1997581
theorem B533611 : Blo 523799 533611 := bstep (se 1 (by rfl) ⟨400208, by rfl⟩ : syracuseStep 533611 = 800417) B800417
theorem B2663603 : Blo 523799 2663603 := bstep (se 1 (by rfl) ⟨1997702, by rfl⟩ : syracuseStep 2663603 = 3995405) B3995405
theorem B1778867 : Blo 523799 1778867 := bstep (se 1 (by rfl) ⟨1334150, by rfl⟩ : syracuseStep 1778867 = 2668301) B2668301
theorem B664843 : Blo 523799 664843 := bstep (se 1 (by rfl) ⟨498632, by rfl⟩ : syracuseStep 664843 = 997265) B997265
theorem B5973425 : Blo 523799 5973425 := bstep (se 2 (by rfl) ⟨2240034, by rfl⟩ : syracuseStep 5973425 = 4480069) B4480069
theorem B1779137 : Blo 523799 1779137 := bstep (se 2 (by rfl) ⟨667176, by rfl⟩ : syracuseStep 1779137 = 1334353) B1334353
theorem B2237969 : Blo 523799 2237969 := bstep (se 2 (by rfl) ⟨839238, by rfl⟩ : syracuseStep 2237969 = 1678477) B1678477
theorem B665111 : Blo 523799 665111 := bstep (se 1 (by rfl) ⟨498833, by rfl⟩ : syracuseStep 665111 = 997667) B997667
theorem B4007555 : Blo 523799 4007555 := bstep (se 1 (by rfl) ⟨3005666, by rfl⟩ : syracuseStep 4007555 = 6011333) B6011333
theorem B3188555 : Blo 523799 3188555 := bstep (se 1 (by rfl) ⟨2391416, by rfl⟩ : syracuseStep 3188555 = 4782833) B4782833
theorem B1779677 : Blo 523799 1779677 := bstep (se 3 (by rfl) ⟨333689, by rfl⟩ : syracuseStep 1779677 = 667379) B667379
theorem B1419329 : Blo 523799 1419329 := bstep (se 2 (by rfl) ⟨532248, by rfl⟩ : syracuseStep 1419329 = 1064497) B1064497
theorem B4040779 : Blo 523799 4040779 := bstep (se 1 (by rfl) ⟨3030584, by rfl⟩ : syracuseStep 4040779 = 6061169) B6061169
theorem B4499549 : Blo 523799 4499549 := bstep (se 3 (by rfl) ⟨843665, by rfl⟩ : syracuseStep 4499549 = 1687331) B1687331
theorem B1026227 : Blo 523799 1026227 := bstep (se 1 (by rfl) ⟨769670, by rfl⟩ : syracuseStep 1026227 = 1539341) B1539341
theorem B665815 : Blo 523799 665815 := bstep (se 1 (by rfl) ⟨499361, by rfl⟩ : syracuseStep 665815 = 998723) B998723
theorem B5122349 : Blo 523799 5122349 := bstep (se 3 (by rfl) ⟨960440, by rfl⟩ : syracuseStep 5122349 = 1920881) B1920881
theorem B633239 : Blo 523799 633239 := bstep (se 1 (by rfl) ⟨474929, by rfl⟩ : syracuseStep 633239 = 949859) B949859
theorem B2238941 : Blo 523799 2238941 := bstep (se 3 (by rfl) ⟨419801, by rfl⟩ : syracuseStep 2238941 = 839603) B839603
theorem B797401 : Blo 523799 797401 := bstep (se 2 (by rfl) ⟨299025, by rfl⟩ : syracuseStep 797401 = 598051) B598051
theorem B4500299 : Blo 523799 4500299 := bstep (se 1 (by rfl) ⟨3375224, by rfl⟩ : syracuseStep 4500299 = 6750449) B6750449
theorem B2534323 : Blo 523799 2534323 := bstep (se 1 (by rfl) ⟨1900742, by rfl⟩ : syracuseStep 2534323 = 3801485) B3801485
theorem B12331993 : Blo 523799 12331993 := bstep (se 2 (by rfl) ⟨4624497, by rfl⟩ : syracuseStep 12331993 = 9248995) B9248995
theorem B2665547 : Blo 523799 2665547 := bstep (se 1 (by rfl) ⟨1999160, by rfl⟩ : syracuseStep 2665547 = 3998321) B3998321
theorem B1125451 : Blo 523799 1125451 := bstep (se 1 (by rfl) ⟨844088, by rfl⟩ : syracuseStep 1125451 = 1688177) B1688177
theorem B1780811 : Blo 523799 1780811 := bstep (se 1 (by rfl) ⟨1335608, by rfl⟩ : syracuseStep 1780811 = 2671217) B2671217
theorem B1781081 : Blo 523799 1781081 := bstep (se 2 (by rfl) ⟨667905, by rfl⟩ : syracuseStep 1781081 = 1335811) B1335811
theorem B994675 : Blo 523799 994675 := bstep (se 1 (by rfl) ⟨746006, by rfl⟩ : syracuseStep 994675 = 1492013) B1492013
theorem B1125913 : Blo 523799 1125913 := bstep (se 2 (by rfl) ⟨422217, by rfl⟩ : syracuseStep 1125913 = 844435) B844435
theorem B3452633 : Blo 523799 3452633 := bstep (se 2 (by rfl) ⟨1294737, by rfl⟩ : syracuseStep 3452633 = 2589475) B2589475
theorem B995161 : Blo 523799 995161 := bstep (se 2 (by rfl) ⟨373185, by rfl⟩ : syracuseStep 995161 = 746371) B746371
theorem B667531 : Blo 523799 667531 := bstep (se 1 (by rfl) ⟨500648, by rfl⟩ : syracuseStep 667531 = 1001297) B1001297
theorem B2535725 : Blo 523799 2535725 := bstep (se 3 (by rfl) ⟨475448, by rfl⟩ : syracuseStep 2535725 = 950897) B950897
theorem B995723 : Blo 523799 995723 := bstep (se 1 (by rfl) ⟨746792, by rfl⟩ : syracuseStep 995723 = 1493585) B1493585
theorem B4501939 : Blo 523799 4501939 := bstep (se 1 (by rfl) ⟨3376454, by rfl⟩ : syracuseStep 4501939 = 6752909) B6752909
theorem B1421761 : Blo 523799 1421761 := bstep (se 2 (by rfl) ⟨533160, by rfl⟩ : syracuseStep 1421761 = 1066321) B1066321
theorem B995905 : Blo 523799 995905 := bstep (se 2 (by rfl) ⟨373464, by rfl⟩ : syracuseStep 995905 = 746929) B746929
theorem B2667329 : Blo 523799 2667329 := bstep (se 2 (by rfl) ⟨1000248, by rfl⟩ : syracuseStep 2667329 = 2000497) B2000497
theorem B2241539 : Blo 523799 2241539 := bstep (se 1 (by rfl) ⟨1681154, by rfl⟩ : syracuseStep 2241539 = 3362309) B3362309
theorem B996619 : Blo 523799 996619 := bstep (se 1 (by rfl) ⟨747464, by rfl⟩ : syracuseStep 996619 = 1494929) B1494929
theorem B996695 : Blo 523799 996695 := bstep (se 1 (by rfl) ⟨747521, by rfl⟩ : syracuseStep 996695 = 1495043) B1495043
theorem B2241881 : Blo 523799 2241881 := bstep (se 2 (by rfl) ⟨840705, by rfl⟩ : syracuseStep 2241881 = 1681411) B1681411
theorem B4273559 : Blo 523799 4273559 := bstep (se 1 (by rfl) ⟨3205169, by rfl⟩ : syracuseStep 4273559 = 6410339) B6410339
theorem B865753 : Blo 523799 865753 := bstep (se 2 (by rfl) ⟨324657, by rfl⟩ : syracuseStep 865753 = 649315) B649315
theorem B1390103 : Blo 523799 1390103 := bstep (se 1 (by rfl) ⟨1042577, by rfl⟩ : syracuseStep 1390103 = 2085155) B2085155
theorem B1259059 : Blo 523799 1259059 := bstep (se 1 (by rfl) ⟨944294, by rfl⟩ : syracuseStep 1259059 = 1888589) B1888589
theorem B3356261 : Blo 523799 3356261 := bstep (se 4 (by rfl) ⟨314649, by rfl⟩ : syracuseStep 3356261 = 629299) B629299
theorem B800471 : Blo 523799 800471 := bstep (se 1 (by rfl) ⟨600353, by rfl⟩ : syracuseStep 800471 = 1200707) B1200707
theorem B1128179 : Blo 523799 1128179 := bstep (se 1 (by rfl) ⟨846134, by rfl⟩ : syracuseStep 1128179 = 1692269) B1692269
theorem B2996099 : Blo 523799 2996099 := bstep (se 1 (by rfl) ⟨2247074, by rfl⟩ : syracuseStep 2996099 = 4494149) B4494149
theorem B997363 : Blo 523799 997363 := bstep (se 1 (by rfl) ⟨748022, by rfl⟩ : syracuseStep 997363 = 1496045) B1496045
theorem B997591 : Blo 523799 997591 := bstep (se 1 (by rfl) ⟨748193, by rfl⟩ : syracuseStep 997591 = 1496387) B1496387
theorem B997697 : Blo 523799 997697 := bstep (se 2 (by rfl) ⟨374136, by rfl⟩ : syracuseStep 997697 = 748273) B748273
theorem B997849 : Blo 523799 997849 := bstep (se 2 (by rfl) ⟨374193, by rfl⟩ : syracuseStep 997849 = 748387) B748387
theorem B1686167 : Blo 523799 1686167 := bstep (se 1 (by rfl) ⟨1264625, by rfl⟩ : syracuseStep 1686167 = 2529251) B2529251
theorem B2669273 : Blo 523799 2669273 := bstep (se 2 (by rfl) ⟨1000977, by rfl⟩ : syracuseStep 2669273 = 2001955) B2001955
theorem B13450049 : Blo 523799 13450049 := bstep (se 2 (by rfl) ⟨5043768, by rfl⟩ : syracuseStep 13450049 = 10087537) B10087537
theorem B1326041 : Blo 523799 1326041 := bstep (se 2 (by rfl) ⟨497265, by rfl⟩ : syracuseStep 1326041 = 994531) B994531
theorem B999155 : Blo 523799 999155 := bstep (se 1 (by rfl) ⟨749366, by rfl⟩ : syracuseStep 999155 = 1498733) B1498733
theorem B999307 : Blo 523799 999307 := bstep (se 1 (by rfl) ⟨749480, by rfl⟩ : syracuseStep 999307 = 1498961) B1498961
theorem B1195955 : Blo 523799 1195955 := bstep (se 1 (by rfl) ⟨896966, by rfl⟩ : syracuseStep 1195955 = 1793933) B1793933
theorem B1687499 : Blo 523799 1687499 := bstep (se 1 (by rfl) ⟨1265624, by rfl⟩ : syracuseStep 1687499 = 2531249) B2531249
theorem B2834507 : Blo 523799 2834507 := bstep (se 1 (by rfl) ⟨2125880, by rfl⟩ : syracuseStep 2834507 = 4251761) B4251761
theorem B3653707 : Blo 523799 3653707 := bstep (se 1 (by rfl) ⟨2740280, by rfl⟩ : syracuseStep 3653707 = 5480561) B5480561
theorem B999641 : Blo 523799 999641 := bstep (se 2 (by rfl) ⟨374865, by rfl⟩ : syracuseStep 999641 = 749731) B749731
theorem B2670893 : Blo 523799 2670893 := bstep (se 3 (by rfl) ⟨500792, by rfl⟩ : syracuseStep 2670893 = 1001585) B1001585
theorem B5685835 : Blo 523799 5685835 := bstep (se 1 (by rfl) ⟨4264376, by rfl⟩ : syracuseStep 5685835 = 8528753) B8528753
theorem B1327691 : Blo 523799 1327691 := bstep (se 1 (by rfl) ⟨995768, by rfl⟩ : syracuseStep 1327691 = 1991537) B1991537
theorem B2245265 : Blo 523799 2245265 := bstep (se 2 (by rfl) ⟨841974, by rfl⟩ : syracuseStep 2245265 = 1683949) B1683949
theorem B10109681 : Blo 523799 10109681 := bstep (se 2 (by rfl) ⟨3791130, by rfl⟩ : syracuseStep 10109681 = 7582261) B7582261
theorem B1000279 : Blo 523799 1000279 := bstep (se 1 (by rfl) ⟨750209, by rfl⟩ : syracuseStep 1000279 = 1500419) B1500419
theorem B3031901 : Blo 523799 3031901 := bstep (se 3 (by rfl) ⟨568481, by rfl⟩ : syracuseStep 3031901 = 1136963) B1136963
theorem B4309937 : Blo 523799 4309937 := bstep (se 2 (by rfl) ⟨1616226, by rfl⟩ : syracuseStep 4309937 = 3232453) B3232453
theorem B1426369 : Blo 523799 1426369 := bstep (se 2 (by rfl) ⟨534888, by rfl⟩ : syracuseStep 1426369 = 1069777) B1069777
theorem B1688627 : Blo 523799 1688627 := bstep (se 1 (by rfl) ⟨1266470, by rfl⟩ : syracuseStep 1688627 = 2532941) B2532941
theorem B4867165 : Blo 523799 4867165 := bstep (se 3 (by rfl) ⟨912593, by rfl⟩ : syracuseStep 4867165 = 1825187) B1825187
theorem B2245981 : Blo 523799 2245981 := bstep (se 3 (by rfl) ⟨421121, by rfl⟩ : syracuseStep 2245981 = 842243) B842243
theorem B3982769 : Blo 523799 3982769 := bstep (se 2 (by rfl) ⟨1493538, by rfl⟩ : syracuseStep 3982769 = 2987077) B2987077
theorem B1492445 : Blo 523799 1492445 := bstep (se 3 (by rfl) ⟨279833, by rfl⟩ : syracuseStep 1492445 = 559667) B559667
theorem B1328663 : Blo 523799 1328663 := bstep (se 1 (by rfl) ⟨996497, by rfl⟩ : syracuseStep 1328663 = 1992995) B1992995
theorem B1001099 : Blo 523799 1001099 := bstep (se 1 (by rfl) ⟨750824, by rfl⟩ : syracuseStep 1001099 = 1501649) B1501649
theorem B1001153 : Blo 523799 1001153 := bstep (se 2 (by rfl) ⟨375432, by rfl⟩ : syracuseStep 1001153 = 750865) B750865
theorem B1066775 : Blo 523799 1066775 := bstep (se 1 (by rfl) ⟨800081, by rfl⟩ : syracuseStep 1066775 = 1600163) B1600163
theorem B2279191 : Blo 523799 2279191 := bstep (se 1 (by rfl) ⟨1709393, by rfl⟩ : syracuseStep 2279191 = 3418787) B3418787
theorem B1066841 : Blo 523799 1066841 := bstep (se 2 (by rfl) ⟨400065, by rfl⟩ : syracuseStep 1066841 = 800131) B800131
theorem B3983255 : Blo 523799 3983255 := bstep (se 1 (by rfl) ⟨2987441, by rfl⟩ : syracuseStep 3983255 = 5974883) B5974883
theorem B3229789 : Blo 523799 3229789 := bstep (se 3 (by rfl) ⟨605585, by rfl⟩ : syracuseStep 3229789 = 1211171) B1211171
theorem B4376753 : Blo 523799 4376753 := bstep (se 2 (by rfl) ⟨1641282, by rfl⟩ : syracuseStep 4376753 = 3282565) B3282565
theorem B1329331 : Blo 523799 1329331 := bstep (se 1 (by rfl) ⟨996998, by rfl⟩ : syracuseStep 1329331 = 1993997) B1993997
theorem B1689817 : Blo 523799 1689817 := bstep (se 2 (by rfl) ⟨633681, by rfl⟩ : syracuseStep 1689817 = 1267363) B1267363
theorem B1329473 : Blo 523799 1329473 := bstep (se 2 (by rfl) ⟨498552, by rfl⟩ : syracuseStep 1329473 = 997105) B997105
theorem B1263961 : Blo 523799 1263961 := bstep (se 2 (by rfl) ⟨473985, by rfl⟩ : syracuseStep 1263961 = 947971) B947971
theorem B1690073 : Blo 523799 1690073 := bstep (se 2 (by rfl) ⟨633777, by rfl⟩ : syracuseStep 1690073 = 1267555) B1267555
theorem B1264193 : Blo 523799 1264193 := bstep (se 2 (by rfl) ⟨474072, by rfl⟩ : syracuseStep 1264193 = 948145) B948145
theorem B1690433 : Blo 523799 1690433 := bstep (se 2 (by rfl) ⟨633912, by rfl⟩ : syracuseStep 1690433 = 1267825) B1267825
theorem B4475969 : Blo 523799 4475969 := bstep (se 2 (by rfl) ⟨1678488, by rfl⟩ : syracuseStep 4475969 = 3356977) B3356977
theorem B3001475 : Blo 523799 3001475 := bstep (se 1 (by rfl) ⟨2251106, by rfl⟩ : syracuseStep 3001475 = 4502213) B4502213
theorem B19123573 : Blo 523799 19123573 := bstep (se 5 (by rfl) ⟨896417, by rfl⟩ : syracuseStep 19123573 = 1792835) B1792835
theorem B1592855 : Blo 523799 1592855 := bstep (se 1 (by rfl) ⟨1194641, by rfl⟩ : syracuseStep 1592855 = 2389283) B2389283
theorem B1330739 : Blo 523799 1330739 := bstep (se 1 (by rfl) ⟨998054, by rfl⟩ : syracuseStep 1330739 = 1996109) B1996109
theorem B3788363 : Blo 523799 3788363 := bstep (se 1 (by rfl) ⟨2841272, by rfl⟩ : syracuseStep 3788363 = 5682545) B5682545
theorem B3001931 : Blo 523799 3001931 := bstep (se 1 (by rfl) ⟨2251448, by rfl⟩ : syracuseStep 3001931 = 4502897) B4502897
theorem B1331275 : Blo 523799 1331275 := bstep (se 1 (by rfl) ⟨998456, by rfl⟩ : syracuseStep 1331275 = 1996913) B1996913
theorem B1200215 : Blo 523799 1200215 := bstep (se 1 (by rfl) ⟨900161, by rfl⟩ : syracuseStep 1200215 = 1800323) B1800323
theorem B1331417 : Blo 523799 1331417 := bstep (se 2 (by rfl) ⟨499281, by rfl⟩ : syracuseStep 1331417 = 998563) B998563
theorem B1495361 : Blo 523799 1495361 := bstep (se 2 (by rfl) ⟨560760, by rfl⟩ : syracuseStep 1495361 = 1121521) B1121521
theorem B1495385 : Blo 523799 1495385 := bstep (se 2 (by rfl) ⟨560769, by rfl⟩ : syracuseStep 1495385 = 1121539) B1121539
theorem B15323741 : Blo 523799 15323741 := bstep (se 3 (by rfl) ⟨2873201, by rfl⟩ : syracuseStep 15323741 = 5746403) B5746403
theorem B1200779 : Blo 523799 1200779 := bstep (se 1 (by rfl) ⟨900584, by rfl⟩ : syracuseStep 1200779 = 1801169) B1801169
theorem B3789517 : Blo 523799 3789517 := bstep (se 3 (by rfl) ⟨710534, by rfl⟩ : syracuseStep 3789517 = 1421069) B1421069
theorem B12800717 : Blo 523799 12800717 := bstep (se 3 (by rfl) ⟨2400134, by rfl⟩ : syracuseStep 12800717 = 4800269) B4800269
theorem B5985089 : Blo 523799 5985089 := bstep (se 2 (by rfl) ⟨2244408, by rfl⟩ : syracuseStep 5985089 = 4488817) B4488817
theorem B2249603 : Blo 523799 2249603 := bstep (se 1 (by rfl) ⟨1687202, by rfl⟩ : syracuseStep 2249603 = 3374405) B3374405
theorem B1201163 : Blo 523799 1201163 := bstep (se 1 (by rfl) ⟨900872, by rfl⟩ : syracuseStep 1201163 = 1801745) B1801745
theorem B1332247 : Blo 523799 1332247 := bstep (se 1 (by rfl) ⟨999185, by rfl⟩ : syracuseStep 1332247 = 1998371) B1998371
theorem B1725761 : Blo 523799 1725761 := bstep (se 2 (by rfl) ⟨647160, by rfl⟩ : syracuseStep 1725761 = 1294321) B1294321
theorem B1201547 : Blo 523799 1201547 := bstep (se 1 (by rfl) ⟨901160, by rfl⟩ : syracuseStep 1201547 = 1802321) B1802321
theorem B1332683 : Blo 523799 1332683 := bstep (se 1 (by rfl) ⟨999512, by rfl⟩ : syracuseStep 1332683 = 1999025) B1999025
theorem B1496627 : Blo 523799 1496627 := bstep (se 1 (by rfl) ⟨1122470, by rfl⟩ : syracuseStep 1496627 = 2244941) B2244941
theorem B1333057 : Blo 523799 1333057 := bstep (se 2 (by rfl) ⟨499896, by rfl⟩ : syracuseStep 1333057 = 999793) B999793
theorem B5199889 : Blo 523799 5199889 := bstep (se 2 (by rfl) ⟨1949958, by rfl⟩ : syracuseStep 5199889 = 3899917) B3899917
theorem B21649477 : Blo 523799 21649477 := bstep (se 4 (by rfl) ⟨2029638, by rfl⟩ : syracuseStep 21649477 = 4059277) B4059277
theorem B1333655 : Blo 523799 1333655 := bstep (se 1 (by rfl) ⟨1000241, by rfl⟩ : syracuseStep 1333655 = 2000483) B2000483
theorem B1989137 : Blo 523799 1989137 := bstep (se 2 (by rfl) ⟨745926, by rfl⟩ : syracuseStep 1989137 = 1491853) B1491853
theorem B2251415 : Blo 523799 2251415 := bstep (se 1 (by rfl) ⟨1688561, by rfl⟩ : syracuseStep 2251415 = 3377123) B3377123
theorem B842519 : Blo 523799 842519 := bstep (se 1 (by rfl) ⟨631889, by rfl⟩ : syracuseStep 842519 = 1263779) B1263779
theorem B1989593 : Blo 523799 1989593 := bstep (se 2 (by rfl) ⟨746097, by rfl⟩ : syracuseStep 1989593 = 1492195) B1492195
theorem B842827 : Blo 523799 842827 := bstep (se 1 (by rfl) ⟨632120, by rfl⟩ : syracuseStep 842827 = 1264241) B1264241
theorem B4545629 : Blo 523799 4545629 := bstep (se 3 (by rfl) ⟨852305, by rfl⟩ : syracuseStep 4545629 = 1704611) B1704611
theorem B1989805 : Blo 523799 1989805 := bstep (se 3 (by rfl) ⟨373088, by rfl⟩ : syracuseStep 1989805 = 746177) B746177
theorem B1334465 : Blo 523799 1334465 := bstep (se 2 (by rfl) ⟨500424, by rfl⟩ : syracuseStep 1334465 = 1000849) B1000849
theorem B1924355 : Blo 523799 1924355 := bstep (se 1 (by rfl) ⟨1443266, by rfl⟩ : syracuseStep 1924355 = 2886533) B2886533
theorem B6741427 : Blo 523799 6741427 := bstep (se 1 (by rfl) ⟨5056070, by rfl⟩ : syracuseStep 6741427 = 10112141) B10112141
theorem B1990109 : Blo 523799 1990109 := bstep (se 3 (by rfl) ⟨373145, by rfl⟩ : syracuseStep 1990109 = 746291) B746291
theorem B1891991 : Blo 523799 1891991 := bstep (se 1 (by rfl) ⟨1418993, by rfl⟩ : syracuseStep 1891991 = 2837987) B2837987
theorem B1335001 : Blo 523799 1335001 := bstep (se 2 (by rfl) ⟨500625, by rfl⟩ : syracuseStep 1335001 = 1001251) B1001251
theorem B712535 : Blo 523799 712535 := bstep (se 1 (by rfl) ⟨534401, by rfl⟩ : syracuseStep 712535 = 1068803) B1068803
theorem B2252747 : Blo 523799 2252747 := bstep (se 1 (by rfl) ⟨1689560, by rfl⟩ : syracuseStep 2252747 = 3379121) B3379121
theorem B844057 : Blo 523799 844057 := bstep (se 2 (by rfl) ⟨316521, by rfl⟩ : syracuseStep 844057 = 633043) B633043
theorem B1499485 : Blo 523799 1499485 := bstep (se 3 (by rfl) ⟨281153, by rfl⟩ : syracuseStep 1499485 = 562307) B562307
theorem B1499543 : Blo 523799 1499543 := bstep (se 1 (by rfl) ⟨1124657, by rfl⟩ : syracuseStep 1499543 = 2249315) B2249315
theorem B4252121 : Blo 523799 4252121 := bstep (se 2 (by rfl) ⟨1594545, by rfl⟩ : syracuseStep 4252121 = 3189091) B3189091
theorem B2253329 : Blo 523799 2253329 := bstep (se 2 (by rfl) ⟨844998, by rfl⟩ : syracuseStep 2253329 = 1689997) B1689997
theorem B1892915 : Blo 523799 1892915 := bstep (se 1 (by rfl) ⟨1419686, by rfl⟩ : syracuseStep 1892915 = 2839373) B2839373
theorem B1794739 : Blo 523799 1794739 := bstep (se 1 (by rfl) ⟨1346054, by rfl⟩ : syracuseStep 1794739 = 2692109) B2692109
theorem B1532609 : Blo 523799 1532609 := bstep (se 2 (by rfl) ⟨574728, by rfl⟩ : syracuseStep 1532609 = 1149457) B1149457
theorem B746263 : Blo 523799 746263 := bstep (se 1 (by rfl) ⟨559697, by rfl⟩ : syracuseStep 746263 = 1119395) B1119395
theorem B8971073 : Blo 523799 8971073 := bstep (se 2 (by rfl) ⟨3364152, by rfl⟩ : syracuseStep 8971073 = 6728305) B6728305
theorem B3466115 : Blo 523799 3466115 := bstep (se 1 (by rfl) ⟨2599586, by rfl⟩ : syracuseStep 3466115 = 5199173) B5199173
theorem B4482053 : Blo 523799 4482053 := bstep (se 4 (by rfl) ⟨420192, by rfl⟩ : syracuseStep 4482053 = 840385) B840385
theorem B3990545 : Blo 523799 3990545 := bstep (se 2 (by rfl) ⟨1496454, by rfl⟩ : syracuseStep 3990545 = 2992909) B2992909
theorem B1893593 : Blo 523799 1893593 := bstep (se 2 (by rfl) ⟨710097, by rfl⟩ : syracuseStep 1893593 = 1420195) B1420195
theorem B1893635 : Blo 523799 1893635 := bstep (se 1 (by rfl) ⟨1420226, by rfl⟩ : syracuseStep 1893635 = 2840453) B2840453
theorem B681367 : Blo 523799 681367 := bstep (se 1 (by rfl) ⟨511025, by rfl⟩ : syracuseStep 681367 = 1022051) B1022051
theorem B1598899 : Blo 523799 1598899 := bstep (se 1 (by rfl) ⟨1199174, by rfl⟩ : syracuseStep 1598899 = 2398349) B2398349
theorem B1009111 : Blo 523799 1009111 := bstep (se 1 (by rfl) ⟨756833, by rfl⟩ : syracuseStep 1009111 = 1513667) B1513667
theorem B2254387 : Blo 523799 2254387 := bstep (se 1 (by rfl) ⟨1690790, by rfl⟩ : syracuseStep 2254387 = 3381581) B3381581
theorem B1009217 : Blo 523799 1009217 := bstep (se 2 (by rfl) ⟨378456, by rfl⟩ : syracuseStep 1009217 = 756913) B756913
theorem B747083 : Blo 523799 747083 := bstep (se 1 (by rfl) ⟨560312, by rfl⟩ : syracuseStep 747083 = 1120625) B1120625
theorem B1500761 : Blo 523799 1500761 := bstep (se 2 (by rfl) ⟨562785, by rfl⟩ : syracuseStep 1500761 = 1125571) B1125571
theorem B1500875 : Blo 523799 1500875 := bstep (se 1 (by rfl) ⟨1125656, by rfl⟩ : syracuseStep 1500875 = 2251313) B2251313
theorem B1992707 : Blo 523799 1992707 := bstep (se 1 (by rfl) ⟨1494530, by rfl⟩ : syracuseStep 1992707 = 2989061) B2989061
theorem B1992721 : Blo 523799 1992721 := bstep (se 2 (by rfl) ⟨747270, by rfl⟩ : syracuseStep 1992721 = 1494541) B1494541
theorem B4810853 : Blo 523799 4810853 := bstep (se 4 (by rfl) ⟨451017, by rfl⟩ : syracuseStep 4810853 = 902035) B902035
theorem B1993025 : Blo 523799 1993025 := bstep (se 2 (by rfl) ⟨747384, by rfl⟩ : syracuseStep 1993025 = 1494769) B1494769
theorem B6056369 : Blo 523799 6056369 := bstep (se 2 (by rfl) ⟨2271138, by rfl⟩ : syracuseStep 6056369 = 4542277) B4542277
theorem B748057 : Blo 523799 748057 := bstep (se 2 (by rfl) ⟨280521, by rfl⟩ : syracuseStep 748057 = 561043) B561043
theorem B1010263 : Blo 523799 1010263 := bstep (se 1 (by rfl) ⟨757697, by rfl⟩ : syracuseStep 1010263 = 1515395) B1515395
theorem B944779 : Blo 523799 944779 := bstep (se 1 (by rfl) ⟨708584, by rfl⟩ : syracuseStep 944779 = 1417169) B1417169
theorem B1502003 : Blo 523799 1502003 := bstep (se 1 (by rfl) ⟨1126502, by rfl⟩ : syracuseStep 1502003 = 2253005) B2253005
theorem B1993693 : Blo 523799 1993693 := bstep (se 3 (by rfl) ⟨373817, by rfl⟩ : syracuseStep 1993693 = 747635) B747635
theorem B945217 : Blo 523799 945217 := bstep (se 2 (by rfl) ⟨354456, by rfl⟩ : syracuseStep 945217 = 708913) B708913
theorem B1502401 : Blo 523799 1502401 := bstep (se 2 (by rfl) ⟨563400, by rfl⟩ : syracuseStep 1502401 = 1126801) B1126801
theorem B945665 : Blo 523799 945665 := bstep (se 2 (by rfl) ⟨354624, by rfl⟩ : syracuseStep 945665 = 709249) B709249
theorem B13463171 : Blo 523799 13463171 := bstep (se 1 (by rfl) ⟨10097378, by rfl⟩ : syracuseStep 13463171 = 20194757) B20194757
theorem B749207 : Blo 523799 749207 := bstep (se 1 (by rfl) ⟨561905, by rfl⟩ : syracuseStep 749207 = 1123811) B1123811
theorem B5041925 : Blo 523799 5041925 := bstep (se 4 (by rfl) ⟨472680, by rfl⟩ : syracuseStep 5041925 = 945361) B945361
theorem B4878085 : Blo 523799 4878085 := bstep (se 4 (by rfl) ⟨457320, by rfl⟩ : syracuseStep 4878085 = 914641) B914641
theorem B4255553 : Blo 523799 4255553 := bstep (se 2 (by rfl) ⟨1595832, by rfl⟩ : syracuseStep 4255553 = 3191665) B3191665
theorem B749515 : Blo 523799 749515 := bstep (se 1 (by rfl) ⟨562136, by rfl⟩ : syracuseStep 749515 = 1124273) B1124273
theorem B946163 : Blo 523799 946163 := bstep (se 1 (by rfl) ⟨709622, by rfl⟩ : syracuseStep 946163 = 1419245) B1419245
theorem B2126027 : Blo 523799 2126027 := bstep (se 1 (by rfl) ⟨1594520, by rfl⟩ : syracuseStep 2126027 = 3189041) B3189041
theorem B1994969 : Blo 523799 1994969 := bstep (se 2 (by rfl) ⟨748113, by rfl⟩ : syracuseStep 1994969 = 1496227) B1496227
theorem B2224691 : Blo 523799 2224691 := bstep (se 1 (by rfl) ⟨1668518, by rfl⟩ : syracuseStep 2224691 = 3337037) B3337037
theorem B19690189 : Blo 523799 19690189 := bstep (se 3 (by rfl) ⟨3691910, by rfl⟩ : syracuseStep 19690189 = 7383821) B7383821
theorem B3994433 : Blo 523799 3994433 := bstep (se 2 (by rfl) ⟨1497912, by rfl⟩ : syracuseStep 3994433 = 2995825) B2995825
theorem B750551 : Blo 523799 750551 := bstep (se 1 (by rfl) ⟨562913, by rfl⟩ : syracuseStep 750551 = 1125827) B1125827
theorem B750745 : Blo 523799 750745 := bstep (se 2 (by rfl) ⟨281529, by rfl⟩ : syracuseStep 750745 = 563059) B563059
theorem B947467 : Blo 523799 947467 := bstep (se 1 (by rfl) ⟨710600, by rfl⟩ : syracuseStep 947467 = 1421201) B1421201
theorem B2160145 : Blo 523799 2160145 := bstep (se 2 (by rfl) ⟨810054, by rfl⟩ : syracuseStep 2160145 = 1620109) B1620109
theorem B718411 : Blo 523799 718411 := bstep (se 1 (by rfl) ⟨538808, by rfl⟩ : syracuseStep 718411 = 1077617) B1077617
theorem B1996595 : Blo 523799 1996595 := bstep (se 1 (by rfl) ⟨1497446, by rfl⟩ : syracuseStep 1996595 = 2994893) B2994893
theorem B1996609 : Blo 523799 1996609 := bstep (se 2 (by rfl) ⟨748728, by rfl⟩ : syracuseStep 1996609 = 1497457) B1497457
theorem B4257629 : Blo 523799 4257629 := bstep (se 3 (by rfl) ⟨798305, by rfl⟩ : syracuseStep 4257629 = 1596611) B1596611
theorem B2160557 : Blo 523799 2160557 := bstep (se 3 (by rfl) ⟨405104, by rfl⟩ : syracuseStep 2160557 = 810209) B810209
theorem B11564977 : Blo 523799 11564977 := bstep (se 2 (by rfl) ⟨4336866, by rfl⟩ : syracuseStep 11564977 = 8673733) B8673733
theorem B3373073 : Blo 523799 3373073 := bstep (se 2 (by rfl) ⟨1264902, by rfl⟩ : syracuseStep 3373073 = 2529805) B2529805
theorem B2390317 : Blo 523799 2390317 := bstep (se 3 (by rfl) ⟨448184, by rfl⟩ : syracuseStep 2390317 = 896369) B896369
theorem B1767959 : Blo 523799 1767959 := bstep (se 1 (by rfl) ⟨1325969, by rfl⟩ : syracuseStep 1767959 = 2651939) B2651939
theorem B7600715 : Blo 523799 7600715 := bstep (se 1 (by rfl) ⟨5700536, by rfl⟩ : syracuseStep 7600715 = 11401073) B11401073
theorem B948851 : Blo 523799 948851 := bstep (se 1 (by rfl) ⟨711638, by rfl⟩ : syracuseStep 948851 = 1423277) B1423277
theorem B3996377 : Blo 523799 3996377 := bstep (se 2 (by rfl) ⟨1498641, by rfl⟩ : syracuseStep 3996377 = 2997283) B2997283
theorem B1604531 : Blo 523799 1604531 := bstep (se 1 (by rfl) ⟨1203398, by rfl⟩ : syracuseStep 1604531 = 2406797) B2406797
theorem B1178585 : Blo 523799 1178585 := bstep (se 2 (by rfl) ⟨441969, by rfl⟩ : syracuseStep 1178585 = 883939) B883939
theorem B1178675 : Blo 523799 1178675 := bstep (se 1 (by rfl) ⟨884006, by rfl⟩ : syracuseStep 1178675 = 1768013) B1768013
theorem B1768499 : Blo 523799 1768499 := bstep (se 1 (by rfl) ⟨1326374, by rfl⟩ : syracuseStep 1768499 = 2652749) B2652749
theorem B949313 : Blo 523799 949313 := bstep (se 2 (by rfl) ⟨355992, by rfl⟩ : syracuseStep 949313 = 711985) B711985
theorem B1178711 : Blo 523799 1178711 := bstep (se 1 (by rfl) ⟨884033, by rfl⟩ : syracuseStep 1178711 = 1768067) B1768067
theorem B1080409 : Blo 523799 1080409 := bstep (se 2 (by rfl) ⟨405153, by rfl⟩ : syracuseStep 1080409 = 810307) B810307
theorem B1178891 : Blo 523799 1178891 := bstep (se 1 (by rfl) ⟨884168, by rfl⟩ : syracuseStep 1178891 = 1768337) B1768337
theorem B883993 : Blo 523799 883993 := bstep (se 2 (by rfl) ⟨331497, by rfl⟩ : syracuseStep 883993 = 662995) B662995
theorem B1178945 : Blo 523799 1178945 := bstep (se 2 (by rfl) ⟨442104, by rfl⟩ : syracuseStep 1178945 = 884209) B884209
theorem B1768769 : Blo 523799 1768769 := bstep (se 2 (by rfl) ⟨663288, by rfl⟩ : syracuseStep 1768769 = 1326577) B1326577
theorem B785753 : Blo 523799 785753 := bstep (se 2 (by rfl) ⟨294657, by rfl⟩ : syracuseStep 785753 = 589315) B589315
theorem B1899949 : Blo 523799 1899949 := bstep (se 3 (by rfl) ⟨356240, by rfl⟩ : syracuseStep 1899949 = 712481) B712481
theorem B785867 : Blo 523799 785867 := bstep (se 1 (by rfl) ⟨589400, by rfl⟩ : syracuseStep 785867 = 1178801) B1178801
theorem B785879 : Blo 523799 785879 := bstep (se 1 (by rfl) ⟨589409, by rfl⟩ : syracuseStep 785879 = 1178819) B1178819
theorem B523799 : Blo 523799 523799 := bstep (se 1 (by rfl) ⟨392849, by rfl⟩ : syracuseStep 523799 = 785699) B785699
theorem B785945 : Blo 523799 785945 := bstep (se 2 (by rfl) ⟨294729, by rfl⟩ : syracuseStep 785945 = 589459) B589459
theorem B1179161 : Blo 523799 1179161 := bstep (se 2 (by rfl) ⟨442185, by rfl⟩ : syracuseStep 1179161 = 884371) B884371
theorem B523819 : Blo 523799 523819 := bstep (se 1 (by rfl) ⟨392864, by rfl⟩ : syracuseStep 523819 = 785729) B785729
theorem B523831 : Blo 523799 523831 := bstep (se 1 (by rfl) ⟨392873, by rfl⟩ : syracuseStep 523831 = 785747) B785747
theorem B523851 : Blo 523799 523851 := bstep (se 1 (by rfl) ⟨392888, by rfl⟩ : syracuseStep 523851 = 785777) B785777
theorem B589387 : Blo 523799 589387 := bstep (se 1 (by rfl) ⟨442040, by rfl⟩ : syracuseStep 589387 = 884081) B884081
theorem B523863 : Blo 523799 523863 := bstep (se 1 (by rfl) ⟨392897, by rfl⟩ : syracuseStep 523863 = 785795) B785795
theorem B523883 : Blo 523799 523883 := bstep (se 1 (by rfl) ⟨392912, by rfl⟩ : syracuseStep 523883 = 785825) B785825
theorem B1179251 : Blo 523799 1179251 := bstep (se 1 (by rfl) ⟨884438, by rfl⟩ : syracuseStep 1179251 = 1768877) B1768877
theorem B523895 : Blo 523799 523895 := bstep (se 1 (by rfl) ⟨392921, by rfl⟩ : syracuseStep 523895 = 785843) B785843
theorem B523915 : Blo 523799 523915 := bstep (se 1 (by rfl) ⟨392936, by rfl⟩ : syracuseStep 523915 = 785873) B785873
theorem B786059 : Blo 523799 786059 := bstep (se 1 (by rfl) ⟨589544, by rfl⟩ : syracuseStep 786059 = 1179089) B1179089
theorem B523927 : Blo 523799 523927 := bstep (se 1 (by rfl) ⟨392945, by rfl⟩ : syracuseStep 523927 = 785891) B785891
theorem B786071 : Blo 523799 786071 := bstep (se 1 (by rfl) ⟨589553, by rfl⟩ : syracuseStep 786071 = 1179107) B1179107
theorem B1179287 : Blo 523799 1179287 := bstep (se 1 (by rfl) ⟨884465, by rfl⟩ : syracuseStep 1179287 = 1768931) B1768931
theorem B523947 : Blo 523799 523947 := bstep (se 1 (by rfl) ⟨392960, by rfl⟩ : syracuseStep 523947 = 785921) B785921
theorem B523959 : Blo 523799 523959 := bstep (se 1 (by rfl) ⟨392969, by rfl⟩ : syracuseStep 523959 = 785939) B785939
theorem B589495 : Blo 523799 589495 := bstep (se 1 (by rfl) ⟨442121, by rfl⟩ : syracuseStep 589495 = 884243) B884243
theorem B523979 : Blo 523799 523979 := bstep (se 1 (by rfl) ⟨392984, by rfl⟩ : syracuseStep 523979 = 785969) B785969
theorem B1998539 : Blo 523799 1998539 := bstep (se 1 (by rfl) ⟨1498904, by rfl⟩ : syracuseStep 1998539 = 2997809) B2997809
theorem B523991 : Blo 523799 523991 := bstep (se 1 (by rfl) ⟨392993, by rfl⟩ : syracuseStep 523991 = 785987) B785987
theorem B786137 : Blo 523799 786137 := bstep (se 2 (by rfl) ⟨294801, by rfl⟩ : syracuseStep 786137 = 589603) B589603
theorem B1998553 : Blo 523799 1998553 := bstep (se 2 (by rfl) ⟨749457, by rfl⟩ : syracuseStep 1998553 = 1498915) B1498915
theorem B524011 : Blo 523799 524011 := bstep (se 1 (by rfl) ⟨393008, by rfl⟩ : syracuseStep 524011 = 786017) B786017
theorem B524023 : Blo 523799 524023 := bstep (se 1 (by rfl) ⟨393017, by rfl⟩ : syracuseStep 524023 = 786035) B786035
theorem B524043 : Blo 523799 524043 := bstep (se 1 (by rfl) ⟨393032, by rfl⟩ : syracuseStep 524043 = 786065) B786065
theorem B524055 : Blo 523799 524055 := bstep (se 1 (by rfl) ⟨393041, by rfl⟩ : syracuseStep 524055 = 786083) B786083
theorem B524075 : Blo 523799 524075 := bstep (se 1 (by rfl) ⟨393056, by rfl⟩ : syracuseStep 524075 = 786113) B786113
theorem B524087 : Blo 523799 524087 := bstep (se 1 (by rfl) ⟨393065, by rfl⟩ : syracuseStep 524087 = 786131) B786131
theorem B524107 : Blo 523799 524107 := bstep (se 1 (by rfl) ⟨393080, by rfl⟩ : syracuseStep 524107 = 786161) B786161
theorem B786251 : Blo 523799 786251 := bstep (se 1 (by rfl) ⟨589688, by rfl⟩ : syracuseStep 786251 = 1179377) B1179377
theorem B1179467 : Blo 523799 1179467 := bstep (se 1 (by rfl) ⟨884600, by rfl⟩ : syracuseStep 1179467 = 1769201) B1769201
theorem B524119 : Blo 523799 524119 := bstep (se 1 (by rfl) ⟨393089, by rfl⟩ : syracuseStep 524119 = 786179) B786179
theorem B786263 : Blo 523799 786263 := bstep (se 1 (by rfl) ⟨589697, by rfl⟩ : syracuseStep 786263 = 1179395) B1179395
theorem B884567 : Blo 523799 884567 := bstep (se 1 (by rfl) ⟨663425, by rfl⟩ : syracuseStep 884567 = 1326851) B1326851
theorem B1769309 : Blo 523799 1769309 := bstep (se 3 (by rfl) ⟨331745, by rfl⟩ : syracuseStep 1769309 = 663491) B663491
theorem B2654045 : Blo 523799 2654045 := bstep (se 3 (by rfl) ⟨497633, by rfl⟩ : syracuseStep 2654045 = 995267) B995267
theorem B524139 : Blo 523799 524139 := bstep (se 1 (by rfl) ⟨393104, by rfl⟩ : syracuseStep 524139 = 786209) B786209
theorem B589675 : Blo 523799 589675 := bstep (se 1 (by rfl) ⟨442256, by rfl⟩ : syracuseStep 589675 = 884513) B884513
theorem B524151 : Blo 523799 524151 := bstep (se 1 (by rfl) ⟨393113, by rfl⟩ : syracuseStep 524151 = 786227) B786227
theorem B1179521 : Blo 523799 1179521 := bstep (se 2 (by rfl) ⟨442320, by rfl⟩ : syracuseStep 1179521 = 884641) B884641
theorem B4489091 : Blo 523799 4489091 := bstep (se 1 (by rfl) ⟨3366818, by rfl⟩ : syracuseStep 4489091 = 6733637) B6733637
theorem B524171 : Blo 523799 524171 := bstep (se 1 (by rfl) ⟨393128, by rfl⟩ : syracuseStep 524171 = 786257) B786257
theorem B524183 : Blo 523799 524183 := bstep (se 1 (by rfl) ⟨393137, by rfl⟩ : syracuseStep 524183 = 786275) B786275
theorem B786329 : Blo 523799 786329 := bstep (se 2 (by rfl) ⟨294873, by rfl⟩ : syracuseStep 786329 = 589747) B589747
theorem B524203 : Blo 523799 524203 := bstep (se 1 (by rfl) ⟨393152, by rfl⟩ : syracuseStep 524203 = 786305) B786305
theorem B524215 : Blo 523799 524215 := bstep (se 1 (by rfl) ⟨393161, by rfl⟩ : syracuseStep 524215 = 786323) B786323
theorem B524235 : Blo 523799 524235 := bstep (se 1 (by rfl) ⟨393176, by rfl⟩ : syracuseStep 524235 = 786353) B786353
theorem B524247 : Blo 523799 524247 := bstep (se 1 (by rfl) ⟨393185, by rfl⟩ : syracuseStep 524247 = 786371) B786371
theorem B589783 : Blo 523799 589783 := bstep (se 1 (by rfl) ⟨442337, by rfl⟩ : syracuseStep 589783 = 884675) B884675
theorem B884695 : Blo 523799 884695 := bstep (se 1 (by rfl) ⟨663521, by rfl⟩ : syracuseStep 884695 = 1327043) B1327043
theorem B524267 : Blo 523799 524267 := bstep (se 1 (by rfl) ⟨393200, by rfl⟩ : syracuseStep 524267 = 786401) B786401
theorem B524279 : Blo 523799 524279 := bstep (se 1 (by rfl) ⟨393209, by rfl⟩ : syracuseStep 524279 = 786419) B786419
theorem B524295 : Blo 523799 524295 := bstep (se 1 (by rfl) ⟨393221, by rfl⟩ : syracuseStep 524295 = 786443) B786443
theorem B524303 : Blo 523799 524303 := bstep (se 1 (by rfl) ⟨393227, by rfl⟩ : syracuseStep 524303 = 786455) B786455
theorem B786491 : Blo 523799 786491 := bstep (se 1 (by rfl) ⟨589868, by rfl⟩ : syracuseStep 786491 = 1179737) B1179737
theorem B524347 : Blo 523799 524347 := bstep (se 1 (by rfl) ⟨393260, by rfl⟩ : syracuseStep 524347 = 786521) B786521
theorem B786551 : Blo 523799 786551 := bstep (se 1 (by rfl) ⟨589913, by rfl⟩ : syracuseStep 786551 = 1179827) B1179827
theorem B524423 : Blo 523799 524423 := bstep (se 1 (by rfl) ⟨393317, by rfl⟩ : syracuseStep 524423 = 786635) B786635
theorem B786575 : Blo 523799 786575 := bstep (se 1 (by rfl) ⟨589931, by rfl⟩ : syracuseStep 786575 = 1179863) B1179863
theorem B524431 : Blo 523799 524431 := bstep (se 1 (by rfl) ⟨393323, by rfl⟩ : syracuseStep 524431 = 786647) B786647
theorem B786617 : Blo 523799 786617 := bstep (se 2 (by rfl) ⟨294981, by rfl⟩ : syracuseStep 786617 = 589963) B589963
theorem B524475 : Blo 523799 524475 := bstep (se 1 (by rfl) ⟨393356, by rfl⟩ : syracuseStep 524475 = 786713) B786713
theorem B786695 : Blo 523799 786695 := bstep (se 1 (by rfl) ⟨590021, by rfl⟩ : syracuseStep 786695 = 1180043) B1180043
theorem B524551 : Blo 523799 524551 := bstep (se 1 (by rfl) ⟨393413, by rfl⟩ : syracuseStep 524551 = 786827) B786827
theorem B524559 : Blo 523799 524559 := bstep (se 1 (by rfl) ⟨393419, by rfl⟩ : syracuseStep 524559 = 786839) B786839
theorem B786731 : Blo 523799 786731 := bstep (se 1 (by rfl) ⟨590048, by rfl⟩ : syracuseStep 786731 = 1180097) B1180097
theorem B524603 : Blo 523799 524603 := bstep (se 1 (by rfl) ⟨393452, by rfl⟩ : syracuseStep 524603 = 786905) B786905
theorem B786761 : Blo 523799 786761 := bstep (se 2 (by rfl) ⟨295035, by rfl⟩ : syracuseStep 786761 = 590071) B590071
theorem B885127 : Blo 523799 885127 := bstep (se 1 (by rfl) ⟨663845, by rfl⟩ : syracuseStep 885127 = 1327691) B1327691
theorem B590215 : Blo 523799 590215 := bstep (se 1 (by rfl) ⟨442661, by rfl⟩ : syracuseStep 590215 = 885323) B885323
theorem B524679 : Blo 523799 524679 := bstep (se 1 (by rfl) ⟨393509, by rfl⟩ : syracuseStep 524679 = 787019) B787019
theorem B524687 : Blo 523799 524687 := bstep (se 1 (by rfl) ⟨393515, by rfl⟩ : syracuseStep 524687 = 787031) B787031
theorem B786875 : Blo 523799 786875 := bstep (se 1 (by rfl) ⟨590156, by rfl⟩ : syracuseStep 786875 = 1180313) B1180313
theorem B524731 : Blo 523799 524731 := bstep (se 1 (by rfl) ⟨393548, by rfl⟩ : syracuseStep 524731 = 787097) B787097
theorem B1999313 : Blo 523799 1999313 := bstep (se 2 (by rfl) ⟨749742, by rfl⟩ : syracuseStep 1999313 = 1499485) B1499485
theorem B786935 : Blo 523799 786935 := bstep (se 1 (by rfl) ⟨590201, by rfl⟩ : syracuseStep 786935 = 1180403) B1180403
theorem B524807 : Blo 523799 524807 := bstep (se 1 (by rfl) ⟨393605, by rfl⟩ : syracuseStep 524807 = 787211) B787211
theorem B786959 : Blo 523799 786959 := bstep (se 1 (by rfl) ⟨590219, by rfl⟩ : syracuseStep 786959 = 1180439) B1180439
theorem B524815 : Blo 523799 524815 := bstep (se 1 (by rfl) ⟨393611, by rfl⟩ : syracuseStep 524815 = 787223) B787223
theorem B787001 : Blo 523799 787001 := bstep (se 2 (by rfl) ⟨295125, by rfl⟩ : syracuseStep 787001 = 590251) B590251
theorem B590395 : Blo 523799 590395 := bstep (se 1 (by rfl) ⟨442796, by rfl⟩ : syracuseStep 590395 = 885593) B885593
theorem B524859 : Blo 523799 524859 := bstep (se 1 (by rfl) ⟨393644, by rfl⟩ : syracuseStep 524859 = 787289) B787289
theorem B1180295 : Blo 523799 1180295 := bstep (se 1 (by rfl) ⟨885221, by rfl⟩ : syracuseStep 1180295 = 1770443) B1770443
theorem B787079 : Blo 523799 787079 := bstep (se 1 (by rfl) ⟨590309, by rfl⟩ : syracuseStep 787079 = 1180619) B1180619
theorem B524935 : Blo 523799 524935 := bstep (se 1 (by rfl) ⟨393701, by rfl⟩ : syracuseStep 524935 = 787403) B787403
theorem B524943 : Blo 523799 524943 := bstep (se 1 (by rfl) ⟨393707, by rfl⟩ : syracuseStep 524943 = 787415) B787415
theorem B787115 : Blo 523799 787115 := bstep (se 1 (by rfl) ⟨590336, by rfl⟩ : syracuseStep 787115 = 1180673) B1180673
theorem B524987 : Blo 523799 524987 := bstep (se 1 (by rfl) ⟨393740, by rfl⟩ : syracuseStep 524987 = 787481) B787481
theorem B787145 : Blo 523799 787145 := bstep (se 2 (by rfl) ⟨295179, by rfl⟩ : syracuseStep 787145 = 590359) B590359
theorem B525063 : Blo 523799 525063 := bstep (se 1 (by rfl) ⟨393797, by rfl⟩ : syracuseStep 525063 = 787595) B787595
theorem B525071 : Blo 523799 525071 := bstep (se 1 (by rfl) ⟨393803, by rfl⟩ : syracuseStep 525071 = 787607) B787607
theorem B1180475 : Blo 523799 1180475 := bstep (se 1 (by rfl) ⟨885356, by rfl⟩ : syracuseStep 1180475 = 1770713) B1770713
theorem B787259 : Blo 523799 787259 := bstep (se 1 (by rfl) ⟨590444, by rfl⟩ : syracuseStep 787259 = 1180889) B1180889
theorem B525115 : Blo 523799 525115 := bstep (se 1 (by rfl) ⟨393836, by rfl⟩ : syracuseStep 525115 = 787673) B787673
theorem B787319 : Blo 523799 787319 := bstep (se 1 (by rfl) ⟨590489, by rfl⟩ : syracuseStep 787319 = 1180979) B1180979
theorem B525191 : Blo 523799 525191 := bstep (se 1 (by rfl) ⟨393893, by rfl⟩ : syracuseStep 525191 = 787787) B787787
theorem B787343 : Blo 523799 787343 := bstep (se 1 (by rfl) ⟨590507, by rfl⟩ : syracuseStep 787343 = 1181015) B1181015
theorem B525199 : Blo 523799 525199 := bstep (se 1 (by rfl) ⟨393899, by rfl⟩ : syracuseStep 525199 = 787799) B787799
theorem B2392985 : Blo 523799 2392985 := bstep (se 2 (by rfl) ⟨897369, by rfl⟩ : syracuseStep 2392985 = 1794739) B1794739
theorem B1180601 : Blo 523799 1180601 := bstep (se 2 (by rfl) ⟨442725, by rfl⟩ : syracuseStep 1180601 = 885451) B885451
theorem B787385 : Blo 523799 787385 := bstep (se 2 (by rfl) ⟨295269, by rfl⟩ : syracuseStep 787385 = 590539) B590539
theorem B525243 : Blo 523799 525243 := bstep (se 1 (by rfl) ⟨393932, by rfl⟩ : syracuseStep 525243 = 787865) B787865
theorem B2655179 : Blo 523799 2655179 := bstep (se 1 (by rfl) ⟨1991384, by rfl⟩ : syracuseStep 2655179 = 3982769) B3982769
theorem B787463 : Blo 523799 787463 := bstep (se 1 (by rfl) ⟨590597, by rfl⟩ : syracuseStep 787463 = 1181195) B1181195
theorem B525319 : Blo 523799 525319 := bstep (se 1 (by rfl) ⟨393989, by rfl⟩ : syracuseStep 525319 = 787979) B787979
theorem B885775 : Blo 523799 885775 := bstep (se 1 (by rfl) ⟨664331, by rfl⟩ : syracuseStep 885775 = 1328663) B1328663
theorem B590863 : Blo 523799 590863 := bstep (se 1 (by rfl) ⟨443147, by rfl⟩ : syracuseStep 590863 = 886295) B886295
theorem B525327 : Blo 523799 525327 := bstep (se 1 (by rfl) ⟨393995, by rfl⟩ : syracuseStep 525327 = 787991) B787991
theorem B787499 : Blo 523799 787499 := bstep (se 1 (by rfl) ⟨590624, by rfl⟩ : syracuseStep 787499 = 1181249) B1181249
theorem B525371 : Blo 523799 525371 := bstep (se 1 (by rfl) ⟨394028, by rfl⟩ : syracuseStep 525371 = 788057) B788057
theorem B787529 : Blo 523799 787529 := bstep (se 2 (by rfl) ⟨295323, by rfl⟩ : syracuseStep 787529 = 590647) B590647
theorem B3998807 : Blo 523799 3998807 := bstep (se 1 (by rfl) ⟨2999105, by rfl⟩ : syracuseStep 3998807 = 5998211) B5998211
theorem B525447 : Blo 523799 525447 := bstep (se 1 (by rfl) ⟨394085, by rfl⟩ : syracuseStep 525447 = 788171) B788171
theorem B525455 : Blo 523799 525455 := bstep (se 1 (by rfl) ⟨394091, by rfl⟩ : syracuseStep 525455 = 788183) B788183
theorem B787643 : Blo 523799 787643 := bstep (se 1 (by rfl) ⟨590732, by rfl⟩ : syracuseStep 787643 = 1181465) B1181465
theorem B525499 : Blo 523799 525499 := bstep (se 1 (by rfl) ⟨394124, by rfl⟩ : syracuseStep 525499 = 788249) B788249
theorem B787703 : Blo 523799 787703 := bstep (se 1 (by rfl) ⟨590777, by rfl⟩ : syracuseStep 787703 = 1181555) B1181555
theorem B1901825 : Blo 523799 1901825 := bstep (se 2 (by rfl) ⟨713184, by rfl⟩ : syracuseStep 1901825 = 1426369) B1426369
theorem B525575 : Blo 523799 525575 := bstep (se 1 (by rfl) ⟨394181, by rfl⟩ : syracuseStep 525575 = 788363) B788363
theorem B2655503 : Blo 523799 2655503 := bstep (se 1 (by rfl) ⟨1991627, by rfl⟩ : syracuseStep 2655503 = 3983255) B3983255
theorem B1770767 : Blo 523799 1770767 := bstep (se 1 (by rfl) ⟨1328075, by rfl⟩ : syracuseStep 1770767 = 2656151) B2656151
theorem B1180943 : Blo 523799 1180943 := bstep (se 1 (by rfl) ⟨885707, by rfl⟩ : syracuseStep 1180943 = 1771415) B1771415
theorem B787727 : Blo 523799 787727 := bstep (se 1 (by rfl) ⟨590795, by rfl⟩ : syracuseStep 787727 = 1181591) B1181591
theorem B525583 : Blo 523799 525583 := bstep (se 1 (by rfl) ⟨394187, by rfl⟩ : syracuseStep 525583 = 788375) B788375
theorem B1180961 : Blo 523799 1180961 := bstep (se 2 (by rfl) ⟨442860, by rfl⟩ : syracuseStep 1180961 = 885721) B885721
theorem B787769 : Blo 523799 787769 := bstep (se 2 (by rfl) ⟨295413, by rfl⟩ : syracuseStep 787769 = 590827) B590827
theorem B525627 : Blo 523799 525627 := bstep (se 1 (by rfl) ⟨394220, by rfl⟩ : syracuseStep 525627 = 788441) B788441
theorem B787847 : Blo 523799 787847 := bstep (se 1 (by rfl) ⟨590885, by rfl⟩ : syracuseStep 787847 = 1181771) B1181771
theorem B525703 : Blo 523799 525703 := bstep (se 1 (by rfl) ⟨394277, by rfl⟩ : syracuseStep 525703 = 788555) B788555
theorem B525711 : Blo 523799 525711 := bstep (se 1 (by rfl) ⟨394283, by rfl⟩ : syracuseStep 525711 = 788567) B788567
theorem B787883 : Blo 523799 787883 := bstep (se 1 (by rfl) ⟨590912, by rfl⟩ : syracuseStep 787883 = 1181825) B1181825
theorem B525755 : Blo 523799 525755 := bstep (se 1 (by rfl) ⟨394316, by rfl⟩ : syracuseStep 525755 = 788633) B788633
theorem B787913 : Blo 523799 787913 := bstep (se 2 (by rfl) ⟨295467, by rfl⟩ : syracuseStep 787913 = 590935) B590935
theorem B2917835 : Blo 523799 2917835 := bstep (se 1 (by rfl) ⟨2188376, by rfl⟩ : syracuseStep 2917835 = 4376753) B4376753
theorem B6489553 : Blo 523799 6489553 := bstep (se 2 (by rfl) ⟨2433582, by rfl⟩ : syracuseStep 6489553 = 4867165) B4867165
theorem B591367 : Blo 523799 591367 := bstep (se 1 (by rfl) ⟨443525, by rfl⟩ : syracuseStep 591367 = 887051) B887051
theorem B525831 : Blo 523799 525831 := bstep (se 1 (by rfl) ⟨394373, by rfl⟩ : syracuseStep 525831 = 788747) B788747
theorem B525839 : Blo 523799 525839 := bstep (se 1 (by rfl) ⟨394379, by rfl⟩ : syracuseStep 525839 = 788759) B788759
theorem B1771037 : Blo 523799 1771037 := bstep (se 3 (by rfl) ⟨332069, by rfl⟩ : syracuseStep 1771037 = 664139) B664139
theorem B886315 : Blo 523799 886315 := bstep (se 1 (by rfl) ⟨664736, by rfl⟩ : syracuseStep 886315 = 1329473) B1329473
theorem B3606059 : Blo 523799 3606059 := bstep (se 1 (by rfl) ⟨2704544, by rfl⟩ : syracuseStep 3606059 = 5409089) B5409089
theorem B788027 : Blo 523799 788027 := bstep (se 1 (by rfl) ⟨591020, by rfl⟩ : syracuseStep 788027 = 1182041) B1182041
theorem B525883 : Blo 523799 525883 := bstep (se 1 (by rfl) ⟨394412, by rfl⟩ : syracuseStep 525883 = 788825) B788825
theorem B12748357 : Blo 523799 12748357 := bstep (se 4 (by rfl) ⟨1195158, by rfl⟩ : syracuseStep 12748357 = 2390317) B2390317
theorem B1181303 : Blo 523799 1181303 := bstep (se 1 (by rfl) ⟨885977, by rfl⟩ : syracuseStep 1181303 = 1771955) B1771955
theorem B788087 : Blo 523799 788087 := bstep (se 1 (by rfl) ⟨591065, by rfl⟩ : syracuseStep 788087 = 1182131) B1182131
theorem B525959 : Blo 523799 525959 := bstep (se 1 (by rfl) ⟨394469, by rfl⟩ : syracuseStep 525959 = 788939) B788939
theorem B788111 : Blo 523799 788111 := bstep (se 1 (by rfl) ⟨591083, by rfl⟩ : syracuseStep 788111 = 1182167) B1182167
theorem B525967 : Blo 523799 525967 := bstep (se 1 (by rfl) ⟨394475, by rfl⟩ : syracuseStep 525967 = 788951) B788951
theorem B886457 : Blo 523799 886457 := bstep (se 2 (by rfl) ⟨332421, by rfl⟩ : syracuseStep 886457 = 664843) B664843
theorem B788153 : Blo 523799 788153 := bstep (se 2 (by rfl) ⟨295557, by rfl⟩ : syracuseStep 788153 = 591115) B591115
theorem B591547 : Blo 523799 591547 := bstep (se 1 (by rfl) ⟨443660, by rfl⟩ : syracuseStep 591547 = 887321) B887321
theorem B526011 : Blo 523799 526011 := bstep (se 1 (by rfl) ⟨394508, by rfl⟩ : syracuseStep 526011 = 789017) B789017
theorem B2983661 : Blo 523799 2983661 := bstep (se 3 (by rfl) ⟨559436, by rfl⟩ : syracuseStep 2983661 = 1118873) B1118873
theorem B788231 : Blo 523799 788231 := bstep (se 1 (by rfl) ⟨591173, by rfl⟩ : syracuseStep 788231 = 1182347) B1182347
theorem B526087 : Blo 523799 526087 := bstep (se 1 (by rfl) ⟨394565, by rfl⟩ : syracuseStep 526087 = 789131) B789131
theorem B526095 : Blo 523799 526095 := bstep (se 1 (by rfl) ⟨394571, by rfl⟩ : syracuseStep 526095 = 789143) B789143
theorem B1181483 : Blo 523799 1181483 := bstep (se 1 (by rfl) ⟨886112, by rfl⟩ : syracuseStep 1181483 = 1772225) B1772225
theorem B788267 : Blo 523799 788267 := bstep (se 1 (by rfl) ⟨591200, by rfl⟩ : syracuseStep 788267 = 1182401) B1182401
theorem B526139 : Blo 523799 526139 := bstep (se 1 (by rfl) ⟨394604, by rfl⟩ : syracuseStep 526139 = 789209) B789209
theorem B788297 : Blo 523799 788297 := bstep (se 2 (by rfl) ⟨295611, by rfl⟩ : syracuseStep 788297 = 591223) B591223
theorem B526215 : Blo 523799 526215 := bstep (se 1 (by rfl) ⟨394661, by rfl⟩ : syracuseStep 526215 = 789323) B789323
theorem B526223 : Blo 523799 526223 := bstep (se 1 (by rfl) ⟨394667, by rfl⟩ : syracuseStep 526223 = 789335) B789335
theorem B2131865 : Blo 523799 2131865 := bstep (se 2 (by rfl) ⟨799449, by rfl⟩ : syracuseStep 2131865 = 1598899) B1598899
theorem B788411 : Blo 523799 788411 := bstep (se 1 (by rfl) ⟨591308, by rfl⟩ : syracuseStep 788411 = 1182617) B1182617
theorem B526267 : Blo 523799 526267 := bstep (se 1 (by rfl) ⟨394700, by rfl⟩ : syracuseStep 526267 = 789401) B789401
theorem B1345481 : Blo 523799 1345481 := bstep (se 2 (by rfl) ⟨504555, by rfl⟩ : syracuseStep 1345481 = 1009111) B1009111
theorem B788471 : Blo 523799 788471 := bstep (se 1 (by rfl) ⟨591353, by rfl⟩ : syracuseStep 788471 = 1182707) B1182707
theorem B526343 : Blo 523799 526343 := bstep (se 1 (by rfl) ⟨394757, by rfl⟩ : syracuseStep 526343 = 789515) B789515
theorem B788495 : Blo 523799 788495 := bstep (se 1 (by rfl) ⟨591371, by rfl⟩ : syracuseStep 788495 = 1182743) B1182743
theorem B526351 : Blo 523799 526351 := bstep (se 1 (by rfl) ⟨394763, by rfl⟩ : syracuseStep 526351 = 789527) B789527
theorem B2983979 : Blo 523799 2983979 := bstep (se 1 (by rfl) ⟨2237984, by rfl⟩ : syracuseStep 2983979 = 4475969) B4475969
theorem B788537 : Blo 523799 788537 := bstep (se 2 (by rfl) ⟨295701, by rfl⟩ : syracuseStep 788537 = 591403) B591403
theorem B526395 : Blo 523799 526395 := bstep (se 1 (by rfl) ⟨394796, by rfl⟩ : syracuseStep 526395 = 789593) B789593
theorem B2000983 : Blo 523799 2000983 := bstep (se 1 (by rfl) ⟨1500737, by rfl⟩ : syracuseStep 2000983 = 3001475) B3001475
theorem B788615 : Blo 523799 788615 := bstep (se 1 (by rfl) ⟨591461, by rfl⟩ : syracuseStep 788615 = 1182923) B1182923
theorem B526471 : Blo 523799 526471 := bstep (se 1 (by rfl) ⟨394853, by rfl⟩ : syracuseStep 526471 = 789707) B789707
theorem B592015 : Blo 523799 592015 := bstep (se 1 (by rfl) ⟨444011, by rfl⟩ : syracuseStep 592015 = 888023) B888023
theorem B526479 : Blo 523799 526479 := bstep (se 1 (by rfl) ⟨394859, by rfl⟩ : syracuseStep 526479 = 789719) B789719
theorem B1181843 : Blo 523799 1181843 := bstep (se 1 (by rfl) ⟨886382, by rfl⟩ : syracuseStep 1181843 = 1772765) B1772765
theorem B788651 : Blo 523799 788651 := bstep (se 1 (by rfl) ⟨591488, by rfl⟩ : syracuseStep 788651 = 1182977) B1182977
theorem B526523 : Blo 523799 526523 := bstep (se 1 (by rfl) ⟨394892, by rfl⟩ : syracuseStep 526523 = 789785) B789785
theorem B1181897 : Blo 523799 1181897 := bstep (se 2 (by rfl) ⟨443211, by rfl⟩ : syracuseStep 1181897 = 886423) B886423
theorem B788681 : Blo 523799 788681 := bstep (se 2 (by rfl) ⟨295755, by rfl⟩ : syracuseStep 788681 = 591511) B591511
theorem B526599 : Blo 523799 526599 := bstep (se 1 (by rfl) ⟨394949, by rfl⟩ : syracuseStep 526599 = 789899) B789899
theorem B526607 : Blo 523799 526607 := bstep (se 1 (by rfl) ⟨394955, by rfl⟩ : syracuseStep 526607 = 789911) B789911
theorem B788795 : Blo 523799 788795 := bstep (se 1 (by rfl) ⟨591596, by rfl⟩ : syracuseStep 788795 = 1183193) B1183193
theorem B526651 : Blo 523799 526651 := bstep (se 1 (by rfl) ⟨394988, by rfl⟩ : syracuseStep 526651 = 789977) B789977
theorem B887159 : Blo 523799 887159 := bstep (se 1 (by rfl) ⟨665369, by rfl⟩ : syracuseStep 887159 = 1330739) B1330739
theorem B788855 : Blo 523799 788855 := bstep (se 1 (by rfl) ⟨591641, by rfl⟩ : syracuseStep 788855 = 1183283) B1183283
theorem B2001287 : Blo 523799 2001287 := bstep (se 1 (by rfl) ⟨1500965, by rfl⟩ : syracuseStep 2001287 = 3001931) B3001931
theorem B2525575 : Blo 523799 2525575 := bstep (se 1 (by rfl) ⟨1894181, by rfl⟩ : syracuseStep 2525575 = 3788363) B3788363
theorem B526727 : Blo 523799 526727 := bstep (se 1 (by rfl) ⟨395045, by rfl⟩ : syracuseStep 526727 = 790091) B790091
theorem B788879 : Blo 523799 788879 := bstep (se 1 (by rfl) ⟨591659, by rfl⟩ : syracuseStep 788879 = 1183319) B1183319
theorem B526735 : Blo 523799 526735 := bstep (se 1 (by rfl) ⟨395051, by rfl⟩ : syracuseStep 526735 = 790103) B790103
theorem B788921 : Blo 523799 788921 := bstep (se 2 (by rfl) ⟨295845, by rfl⟩ : syracuseStep 788921 = 591691) B591691
theorem B526779 : Blo 523799 526779 := bstep (se 1 (by rfl) ⟨395084, by rfl⟩ : syracuseStep 526779 = 790169) B790169
theorem B788999 : Blo 523799 788999 := bstep (se 1 (by rfl) ⟨591749, by rfl⟩ : syracuseStep 788999 = 1183499) B1183499
theorem B526855 : Blo 523799 526855 := bstep (se 1 (by rfl) ⟨395141, by rfl⟩ : syracuseStep 526855 = 790283) B790283
theorem B526863 : Blo 523799 526863 := bstep (se 1 (by rfl) ⟨395147, by rfl⟩ : syracuseStep 526863 = 790295) B790295
theorem B789035 : Blo 523799 789035 := bstep (se 1 (by rfl) ⟨591776, by rfl⟩ : syracuseStep 789035 = 1183553) B1183553
theorem B526907 : Blo 523799 526907 := bstep (se 1 (by rfl) ⟨395180, by rfl⟩ : syracuseStep 526907 = 790361) B790361
theorem B2001469 : Blo 523799 2001469 := bstep (se 3 (by rfl) ⟨375275, by rfl⟩ : syracuseStep 2001469 = 750551) B750551
theorem B789065 : Blo 523799 789065 := bstep (se 2 (by rfl) ⟨295899, by rfl⟩ : syracuseStep 789065 = 591799) B591799
theorem B592519 : Blo 523799 592519 := bstep (se 1 (by rfl) ⟨444389, by rfl⟩ : syracuseStep 592519 = 888779) B888779
theorem B526983 : Blo 523799 526983 := bstep (se 1 (by rfl) ⟨395237, by rfl⟩ : syracuseStep 526983 = 790475) B790475
theorem B526991 : Blo 523799 526991 := bstep (se 1 (by rfl) ⟨395243, by rfl⟩ : syracuseStep 526991 = 790487) B790487
theorem B789179 : Blo 523799 789179 := bstep (se 1 (by rfl) ⟨591884, by rfl⟩ : syracuseStep 789179 = 1183769) B1183769
theorem B527035 : Blo 523799 527035 := bstep (se 1 (by rfl) ⟨395276, by rfl⟩ : syracuseStep 527035 = 790553) B790553
theorem B2656961 : Blo 523799 2656961 := bstep (se 2 (by rfl) ⟨996360, by rfl⟩ : syracuseStep 2656961 = 1992721) B1992721
theorem B789239 : Blo 523799 789239 := bstep (se 1 (by rfl) ⟨591929, by rfl⟩ : syracuseStep 789239 = 1183859) B1183859
theorem B527111 : Blo 523799 527111 := bstep (se 1 (by rfl) ⟨395333, by rfl⟩ : syracuseStep 527111 = 790667) B790667
theorem B789263 : Blo 523799 789263 := bstep (se 1 (by rfl) ⟨591947, by rfl⟩ : syracuseStep 789263 = 1183895) B1183895
theorem B527119 : Blo 523799 527119 := bstep (se 1 (by rfl) ⟨395339, by rfl⟩ : syracuseStep 527119 = 790679) B790679
theorem B11406095 : Blo 523799 11406095 := bstep (se 1 (by rfl) ⟨8554571, by rfl⟩ : syracuseStep 11406095 = 17109143) B17109143
theorem B789305 : Blo 523799 789305 := bstep (se 2 (by rfl) ⟨295989, by rfl⟩ : syracuseStep 789305 = 591979) B591979
theorem B887611 : Blo 523799 887611 := bstep (se 1 (by rfl) ⟨665708, by rfl⟩ : syracuseStep 887611 = 1331417) B1331417
theorem B592699 : Blo 523799 592699 := bstep (se 1 (by rfl) ⟨444524, by rfl⟩ : syracuseStep 592699 = 889049) B889049
theorem B527163 : Blo 523799 527163 := bstep (se 1 (by rfl) ⟨395372, by rfl⟩ : syracuseStep 527163 = 790745) B790745
theorem B4787059 : Blo 523799 4787059 := bstep (se 1 (by rfl) ⟨3590294, by rfl⟩ : syracuseStep 4787059 = 7180589) B7180589
theorem B1182599 : Blo 523799 1182599 := bstep (se 1 (by rfl) ⟨886949, by rfl⟩ : syracuseStep 1182599 = 1773899) B1773899
theorem B789383 : Blo 523799 789383 := bstep (se 1 (by rfl) ⟨592037, by rfl⟩ : syracuseStep 789383 = 1184075) B1184075
theorem B527239 : Blo 523799 527239 := bstep (se 1 (by rfl) ⟨395429, by rfl⟩ : syracuseStep 527239 = 790859) B790859
theorem B527247 : Blo 523799 527247 := bstep (se 1 (by rfl) ⟨395435, by rfl⟩ : syracuseStep 527247 = 790871) B790871
theorem B1772441 : Blo 523799 1772441 := bstep (se 2 (by rfl) ⟨664665, by rfl⟩ : syracuseStep 1772441 = 1329331) B1329331
theorem B789419 : Blo 523799 789419 := bstep (se 1 (by rfl) ⟨592064, by rfl⟩ : syracuseStep 789419 = 1184129) B1184129
theorem B527291 : Blo 523799 527291 := bstep (se 1 (by rfl) ⟨395468, by rfl⟩ : syracuseStep 527291 = 790937) B790937
theorem B887753 : Blo 523799 887753 := bstep (se 2 (by rfl) ⟨332907, by rfl⟩ : syracuseStep 887753 = 665815) B665815
theorem B789449 : Blo 523799 789449 := bstep (se 2 (by rfl) ⟨296043, by rfl⟩ : syracuseStep 789449 = 592087) B592087
theorem B527367 : Blo 523799 527367 := bstep (se 1 (by rfl) ⟨395525, by rfl⟩ : syracuseStep 527367 = 791051) B791051
theorem B527375 : Blo 523799 527375 := bstep (se 1 (by rfl) ⟨395531, by rfl⟩ : syracuseStep 527375 = 791063) B791063
theorem B1182779 : Blo 523799 1182779 := bstep (se 1 (by rfl) ⟨887084, by rfl⟩ : syracuseStep 1182779 = 1774169) B1774169
theorem B789563 : Blo 523799 789563 := bstep (se 1 (by rfl) ⟨592172, by rfl⟩ : syracuseStep 789563 = 1184345) B1184345
theorem B527419 : Blo 523799 527419 := bstep (se 1 (by rfl) ⟨395564, by rfl⟩ : syracuseStep 527419 = 791129) B791129
theorem B789623 : Blo 523799 789623 := bstep (se 1 (by rfl) ⟨592217, by rfl⟩ : syracuseStep 789623 = 1184435) B1184435
theorem B527495 : Blo 523799 527495 := bstep (se 1 (by rfl) ⟨395621, by rfl⟩ : syracuseStep 527495 = 791243) B791243
theorem B789647 : Blo 523799 789647 := bstep (se 1 (by rfl) ⟨592235, by rfl⟩ : syracuseStep 789647 = 1184471) B1184471
theorem B527503 : Blo 523799 527503 := bstep (se 1 (by rfl) ⟨395627, by rfl⟩ : syracuseStep 527503 = 791255) B791255
theorem B1182905 : Blo 523799 1182905 := bstep (se 2 (by rfl) ⟨443589, by rfl⟩ : syracuseStep 1182905 = 887179) B887179
theorem B789689 : Blo 523799 789689 := bstep (se 2 (by rfl) ⟨296133, by rfl⟩ : syracuseStep 789689 = 592267) B592267
theorem B527547 : Blo 523799 527547 := bstep (se 1 (by rfl) ⟨395660, by rfl⟩ : syracuseStep 527547 = 791321) B791321
theorem B789767 : Blo 523799 789767 := bstep (se 1 (by rfl) ⟨592325, by rfl⟩ : syracuseStep 789767 = 1184651) B1184651
theorem B527623 : Blo 523799 527623 := bstep (se 1 (by rfl) ⟨395717, by rfl⟩ : syracuseStep 527623 = 791435) B791435
theorem B593167 : Blo 523799 593167 := bstep (se 1 (by rfl) ⟨444875, by rfl⟩ : syracuseStep 593167 = 889751) B889751
theorem B527631 : Blo 523799 527631 := bstep (se 1 (by rfl) ⟨395723, by rfl⟩ : syracuseStep 527631 = 791447) B791447
theorem B789803 : Blo 523799 789803 := bstep (se 1 (by rfl) ⟨592352, by rfl⟩ : syracuseStep 789803 = 1184705) B1184705
theorem B527675 : Blo 523799 527675 := bstep (se 1 (by rfl) ⟨395756, by rfl⟩ : syracuseStep 527675 = 791513) B791513
theorem B789833 : Blo 523799 789833 := bstep (se 2 (by rfl) ⟨296187, by rfl⟩ : syracuseStep 789833 = 592375) B592375
theorem B527751 : Blo 523799 527751 := bstep (se 1 (by rfl) ⟨395813, by rfl⟩ : syracuseStep 527751 = 791627) B791627
theorem B527759 : Blo 523799 527759 := bstep (se 1 (by rfl) ⟨395819, by rfl⟩ : syracuseStep 527759 = 791639) B791639
theorem B789947 : Blo 523799 789947 := bstep (se 1 (by rfl) ⟨592460, by rfl⟩ : syracuseStep 789947 = 1184921) B1184921
theorem B1347017 : Blo 523799 1347017 := bstep (se 2 (by rfl) ⟨505131, by rfl⟩ : syracuseStep 1347017 = 1010263) B1010263
theorem B2985437 : Blo 523799 2985437 := bstep (se 3 (by rfl) ⟨559769, by rfl⟩ : syracuseStep 2985437 = 1119539) B1119539
theorem B790007 : Blo 523799 790007 := bstep (se 1 (by rfl) ⟨592505, by rfl⟩ : syracuseStep 790007 = 1185011) B1185011
theorem B1183247 : Blo 523799 1183247 := bstep (se 1 (by rfl) ⟨887435, by rfl⟩ : syracuseStep 1183247 = 1774871) B1774871
theorem B790031 : Blo 523799 790031 := bstep (se 1 (by rfl) ⟨592523, by rfl⟩ : syracuseStep 790031 = 1185047) B1185047
theorem B9014813 : Blo 523799 9014813 := bstep (se 3 (by rfl) ⟨1690277, by rfl⟩ : syracuseStep 9014813 = 3380555) B3380555
theorem B1183265 : Blo 523799 1183265 := bstep (se 2 (by rfl) ⟨443724, by rfl⟩ : syracuseStep 1183265 = 887449) B887449
theorem B1150507 : Blo 523799 1150507 := bstep (se 1 (by rfl) ⟨862880, by rfl⟩ : syracuseStep 1150507 = 1725761) B1725761
theorem B790073 : Blo 523799 790073 := bstep (se 2 (by rfl) ⟨296277, by rfl⟩ : syracuseStep 790073 = 592555) B592555
theorem B1773143 : Blo 523799 1773143 := bstep (se 1 (by rfl) ⟨1329857, by rfl⟩ : syracuseStep 1773143 = 2659715) B2659715
theorem B888455 : Blo 523799 888455 := bstep (se 1 (by rfl) ⟨666341, by rfl⟩ : syracuseStep 888455 = 1332683) B1332683
theorem B790151 : Blo 523799 790151 := bstep (se 1 (by rfl) ⟨592613, by rfl⟩ : syracuseStep 790151 = 1185227) B1185227
theorem B790187 : Blo 523799 790187 := bstep (se 1 (by rfl) ⟨592640, by rfl⟩ : syracuseStep 790187 = 1185281) B1185281
theorem B790217 : Blo 523799 790217 := bstep (se 2 (by rfl) ⟨296331, by rfl⟩ : syracuseStep 790217 = 592663) B592663
theorem B593671 : Blo 523799 593671 := bstep (se 1 (by rfl) ⟨445253, by rfl⟩ : syracuseStep 593671 = 890507) B890507
theorem B790331 : Blo 523799 790331 := bstep (se 1 (by rfl) ⟨592748, by rfl⟩ : syracuseStep 790331 = 1185497) B1185497
theorem B1183607 : Blo 523799 1183607 := bstep (se 1 (by rfl) ⟨887705, by rfl⟩ : syracuseStep 1183607 = 1775411) B1775411
theorem B790391 : Blo 523799 790391 := bstep (se 1 (by rfl) ⟨592793, by rfl⟩ : syracuseStep 790391 = 1185587) B1185587
theorem B790415 : Blo 523799 790415 := bstep (se 1 (by rfl) ⟨592811, by rfl⟩ : syracuseStep 790415 = 1185623) B1185623
theorem B3379097 : Blo 523799 3379097 := bstep (se 2 (by rfl) ⟨1267161, by rfl⟩ : syracuseStep 3379097 = 2534323) B2534323
theorem B790457 : Blo 523799 790457 := bstep (se 2 (by rfl) ⟨296421, by rfl⟩ : syracuseStep 790457 = 592843) B592843
theorem B2658257 : Blo 523799 2658257 := bstep (se 2 (by rfl) ⟨996846, by rfl⟩ : syracuseStep 2658257 = 1993693) B1993693
theorem B790535 : Blo 523799 790535 := bstep (se 1 (by rfl) ⟨592901, by rfl⟩ : syracuseStep 790535 = 1185803) B1185803
theorem B1183787 : Blo 523799 1183787 := bstep (se 1 (by rfl) ⟨887840, by rfl⟩ : syracuseStep 1183787 = 1775681) B1775681
theorem B790571 : Blo 523799 790571 := bstep (se 1 (by rfl) ⟨592928, by rfl⟩ : syracuseStep 790571 = 1185857) B1185857
theorem B1773629 : Blo 523799 1773629 := bstep (se 3 (by rfl) ⟨332555, by rfl⟩ : syracuseStep 1773629 = 665111) B665111
theorem B790601 : Blo 523799 790601 := bstep (se 2 (by rfl) ⟨296475, by rfl⟩ : syracuseStep 790601 = 592951) B592951
theorem B5705815 : Blo 523799 5705815 := bstep (se 1 (by rfl) ⟨4279361, by rfl⟩ : syracuseStep 5705815 = 8558723) B8558723
theorem B2691245 : Blo 523799 2691245 := bstep (se 3 (by rfl) ⟨504608, by rfl⟩ : syracuseStep 2691245 = 1009217) B1009217
theorem B790715 : Blo 523799 790715 := bstep (se 1 (by rfl) ⟨593036, by rfl⟩ : syracuseStep 790715 = 1186073) B1186073
theorem B6754549 : Blo 523799 6754549 := bstep (se 5 (by rfl) ⟨316619, by rfl⟩ : syracuseStep 6754549 = 633239) B633239
theorem B790775 : Blo 523799 790775 := bstep (se 1 (by rfl) ⟨593081, by rfl⟩ : syracuseStep 790775 = 1186163) B1186163
theorem B2003201 : Blo 523799 2003201 := bstep (se 2 (by rfl) ⟨751200, by rfl⟩ : syracuseStep 2003201 = 1502401) B1502401
theorem B889103 : Blo 523799 889103 := bstep (se 1 (by rfl) ⟨666827, by rfl⟩ : syracuseStep 889103 = 1333655) B1333655
theorem B790799 : Blo 523799 790799 := bstep (se 1 (by rfl) ⟨593099, by rfl⟩ : syracuseStep 790799 = 1186199) B1186199
theorem B790841 : Blo 523799 790841 := bstep (se 2 (by rfl) ⟨296565, by rfl⟩ : syracuseStep 790841 = 593131) B593131
theorem B790919 : Blo 523799 790919 := bstep (se 1 (by rfl) ⟨593189, by rfl⟩ : syracuseStep 790919 = 1186379) B1186379
theorem B1184147 : Blo 523799 1184147 := bstep (se 1 (by rfl) ⟨888110, by rfl⟩ : syracuseStep 1184147 = 1776221) B1776221
theorem B790955 : Blo 523799 790955 := bstep (se 1 (by rfl) ⟨593216, by rfl⟩ : syracuseStep 790955 = 1186433) B1186433
theorem B1184201 : Blo 523799 1184201 := bstep (se 2 (by rfl) ⟨444075, by rfl⟩ : syracuseStep 1184201 = 888151) B888151
theorem B790985 : Blo 523799 790985 := bstep (se 2 (by rfl) ⟨296619, by rfl⟩ : syracuseStep 790985 = 593239) B593239
theorem B25498097 : Blo 523799 25498097 := bstep (se 2 (by rfl) ⟨9561786, by rfl⟩ : syracuseStep 25498097 = 19123573) B19123573
theorem B791099 : Blo 523799 791099 := bstep (se 1 (by rfl) ⟨593324, by rfl⟩ : syracuseStep 791099 = 1186649) B1186649
theorem B791159 : Blo 523799 791159 := bstep (se 1 (by rfl) ⟨593369, by rfl⟩ : syracuseStep 791159 = 1186739) B1186739
theorem B791183 : Blo 523799 791183 := bstep (se 1 (by rfl) ⟨593387, by rfl⟩ : syracuseStep 791183 = 1186775) B1186775
theorem B791225 : Blo 523799 791225 := bstep (se 2 (by rfl) ⟨296709, by rfl⟩ : syracuseStep 791225 = 593419) B593419
theorem B791303 : Blo 523799 791303 := bstep (se 1 (by rfl) ⟨593477, by rfl⟩ : syracuseStep 791303 = 1186955) B1186955
theorem B889643 : Blo 523799 889643 := bstep (se 1 (by rfl) ⟨667232, by rfl⟩ : syracuseStep 889643 = 1334465) B1334465
theorem B791339 : Blo 523799 791339 := bstep (se 1 (by rfl) ⟨593504, by rfl⟩ : syracuseStep 791339 = 1187009) B1187009
theorem B791369 : Blo 523799 791369 := bstep (se 2 (by rfl) ⟨296763, by rfl⟩ : syracuseStep 791369 = 593527) B593527
theorem B791483 : Blo 523799 791483 := bstep (se 1 (by rfl) ⟨593612, by rfl⟩ : syracuseStep 791483 = 1187225) B1187225
theorem B791543 : Blo 523799 791543 := bstep (se 1 (by rfl) ⟨593657, by rfl⟩ : syracuseStep 791543 = 1187315) B1187315
theorem B2429963 : Blo 523799 2429963 := bstep (se 1 (by rfl) ⟨1822472, by rfl⟩ : syracuseStep 2429963 = 3644945) B3644945
theorem B791567 : Blo 523799 791567 := bstep (se 1 (by rfl) ⟨593675, by rfl⟩ : syracuseStep 791567 = 1187351) B1187351
theorem B791609 : Blo 523799 791609 := bstep (se 2 (by rfl) ⟨296853, by rfl⟩ : syracuseStep 791609 = 593707) B593707
theorem B1184903 : Blo 523799 1184903 := bstep (se 1 (by rfl) ⟨888677, by rfl⟩ : syracuseStep 1184903 = 1777355) B1777355
theorem B791687 : Blo 523799 791687 := bstep (se 1 (by rfl) ⟨593765, by rfl⟩ : syracuseStep 791687 = 1187531) B1187531
theorem B890041 : Blo 523799 890041 := bstep (se 2 (by rfl) ⟨333765, by rfl⟩ : syracuseStep 890041 = 667531) B667531
theorem B1185083 : Blo 523799 1185083 := bstep (se 1 (by rfl) ⟨888812, by rfl⟩ : syracuseStep 1185083 = 1777625) B1777625
theorem B1775033 : Blo 523799 1775033 := bstep (se 2 (by rfl) ⟨665637, by rfl⟩ : syracuseStep 1775033 = 1331275) B1331275
theorem B1185209 : Blo 523799 1185209 := bstep (se 2 (by rfl) ⟨444453, by rfl⟩ : syracuseStep 1185209 = 888907) B888907
theorem B4789763 : Blo 523799 4789763 := bstep (se 1 (by rfl) ⟨3592322, by rfl⟩ : syracuseStep 4789763 = 7184645) B7184645
theorem B1185551 : Blo 523799 1185551 := bstep (se 1 (by rfl) ⟨889163, by rfl⟩ : syracuseStep 1185551 = 1778327) B1778327
theorem B1185569 : Blo 523799 1185569 := bstep (se 2 (by rfl) ⟨444588, by rfl⟩ : syracuseStep 1185569 = 889177) B889177
theorem B1021739 : Blo 523799 1021739 := bstep (se 1 (by rfl) ⟨766304, by rfl⟩ : syracuseStep 1021739 = 1532609) B1532609
theorem B6002585 : Blo 523799 6002585 := bstep (se 2 (by rfl) ⟨2250969, by rfl⟩ : syracuseStep 6002585 = 4501939) B4501939
theorem B2988035 : Blo 523799 2988035 := bstep (se 1 (by rfl) ⟨2241026, by rfl⟩ : syracuseStep 2988035 = 4482053) B4482053
theorem B2660363 : Blo 523799 2660363 := bstep (se 1 (by rfl) ⟨1995272, by rfl⟩ : syracuseStep 2660363 = 3990545) B3990545
theorem B1775627 : Blo 523799 1775627 := bstep (se 1 (by rfl) ⟨1331720, by rfl⟩ : syracuseStep 1775627 = 2663441) B2663441
theorem B1775735 : Blo 523799 1775735 := bstep (se 1 (by rfl) ⟨1331801, by rfl⟩ : syracuseStep 1775735 = 2663603) B2663603
theorem B1185911 : Blo 523799 1185911 := bstep (se 1 (by rfl) ⟨889433, by rfl⟩ : syracuseStep 1185911 = 1778867) B1778867
theorem B2660525 : Blo 523799 2660525 := bstep (se 3 (by rfl) ⟨498848, by rfl⟩ : syracuseStep 2660525 = 997697) B997697
theorem B5052689 : Blo 523799 5052689 := bstep (se 2 (by rfl) ⟨1894758, by rfl⟩ : syracuseStep 5052689 = 3789517) B3789517
theorem B1186091 : Blo 523799 1186091 := bstep (se 1 (by rfl) ⟨889568, by rfl⟩ : syracuseStep 1186091 = 1779137) B1779137
theorem B5970509 : Blo 523799 5970509 := bstep (se 3 (by rfl) ⟨1119470, by rfl⟩ : syracuseStep 5970509 = 2238941) B2238941
theorem B1186451 : Blo 523799 1186451 := bstep (se 1 (by rfl) ⟨889838, by rfl⟩ : syracuseStep 1186451 = 1779677) B1779677
theorem B1776329 : Blo 523799 1776329 := bstep (se 2 (by rfl) ⟨666123, by rfl⟩ : syracuseStep 1776329 = 1332247) B1332247
theorem B1186505 : Blo 523799 1186505 := bstep (se 2 (by rfl) ⟨444939, by rfl⟩ : syracuseStep 1186505 = 889879) B889879
theorem B3414899 : Blo 523799 3414899 := bstep (se 1 (by rfl) ⟨2561174, by rfl⟩ : syracuseStep 3414899 = 5122349) B5122349
theorem B4037579 : Blo 523799 4037579 := bstep (se 1 (by rfl) ⟨3028184, by rfl⟩ : syracuseStep 4037579 = 6056369) B6056369
theorem B2891009 : Blo 523799 2891009 := bstep (se 2 (by rfl) ⟨1084128, by rfl⟩ : syracuseStep 2891009 = 2168257) B2168257
theorem B1777031 : Blo 523799 1777031 := bstep (se 1 (by rfl) ⟨1332773, by rfl⟩ : syracuseStep 1777031 = 2665547) B2665547
theorem B1187207 : Blo 523799 1187207 := bstep (se 1 (by rfl) ⟨890405, by rfl⟩ : syracuseStep 1187207 = 1780811) B1780811
theorem B1678745 : Blo 523799 1678745 := bstep (se 2 (by rfl) ⟨629529, by rfl⟩ : syracuseStep 1678745 = 1259059) B1259059
theorem B957881 : Blo 523799 957881 := bstep (se 2 (by rfl) ⟨359205, by rfl⟩ : syracuseStep 957881 = 718411) B718411
theorem B1187387 : Blo 523799 1187387 := bstep (se 1 (by rfl) ⟨890540, by rfl⟩ : syracuseStep 1187387 = 1781081) B1781081
theorem B630443 : Blo 523799 630443 := bstep (se 1 (by rfl) ⟨472832, by rfl⟩ : syracuseStep 630443 = 945665) B945665
theorem B1187513 : Blo 523799 1187513 := bstep (se 2 (by rfl) ⟨445317, by rfl⟩ : syracuseStep 1187513 = 890635) B890635
theorem B2662145 : Blo 523799 2662145 := bstep (se 2 (by rfl) ⟨998304, by rfl⟩ : syracuseStep 2662145 = 1996609) B1996609
theorem B1777409 : Blo 523799 1777409 := bstep (se 2 (by rfl) ⟨666528, by rfl⟩ : syracuseStep 1777409 = 1333057) B1333057
theorem B2301755 : Blo 523799 2301755 := bstep (se 1 (by rfl) ⟨1726316, by rfl⟩ : syracuseStep 2301755 = 3452633) B3452633
theorem B630775 : Blo 523799 630775 := bstep (se 1 (by rfl) ⟨473081, by rfl⟩ : syracuseStep 630775 = 946163) B946163
theorem B1417351 : Blo 523799 1417351 := bstep (se 1 (by rfl) ⟨1063013, by rfl⟩ : syracuseStep 1417351 = 2126027) B2126027
theorem B663815 : Blo 523799 663815 := bstep (se 1 (by rfl) ⟨497861, by rfl⟩ : syracuseStep 663815 = 995723) B995723
theorem B1483127 : Blo 523799 1483127 := bstep (se 1 (by rfl) ⟨1112345, by rfl⟩ : syracuseStep 1483127 = 2224691) B2224691
theorem B1778219 : Blo 523799 1778219 := bstep (se 1 (by rfl) ⟨1333664, by rfl⟩ : syracuseStep 1778219 = 2667329) B2667329
theorem B2662955 : Blo 523799 2662955 := bstep (se 1 (by rfl) ⟨1997216, by rfl⟩ : syracuseStep 2662955 = 3994433) B3994433
theorem B664463 : Blo 523799 664463 := bstep (se 1 (by rfl) ⟨498347, by rfl⟩ : syracuseStep 664463 = 996695) B996695
theorem B926735 : Blo 523799 926735 := bstep (se 1 (by rfl) ⟨695051, by rfl⟩ : syracuseStep 926735 = 1390103) B1390103
theorem B2237507 : Blo 523799 2237507 := bstep (se 1 (by rfl) ⟨1678130, by rfl⟩ : syracuseStep 2237507 = 3356261) B3356261
theorem B533647 : Blo 523799 533647 := bstep (se 1 (by rfl) ⟨400235, by rfl⟩ : syracuseStep 533647 = 800471) B800471
theorem B1123769 : Blo 523799 1123769 := bstep (se 2 (by rfl) ⟨421413, by rfl⟩ : syracuseStep 1123769 = 842827) B842827
theorem B632567 : Blo 523799 632567 := bstep (se 1 (by rfl) ⟨474425, by rfl⟩ : syracuseStep 632567 = 948851) B948851
theorem B1124111 : Blo 523799 1124111 := bstep (se 1 (by rfl) ⟨843083, by rfl⟩ : syracuseStep 1124111 = 1686167) B1686167
theorem B2664251 : Blo 523799 2664251 := bstep (se 1 (by rfl) ⟨1998188, by rfl⟩ : syracuseStep 2664251 = 3996377) B3996377
theorem B1779515 : Blo 523799 1779515 := bstep (se 1 (by rfl) ⟨1334636, by rfl⟩ : syracuseStep 1779515 = 2669273) B2669273
theorem B2533265 : Blo 523799 2533265 := bstep (se 2 (by rfl) ⟨949974, by rfl⟩ : syracuseStep 2533265 = 1899949) B1899949
theorem B8988569 : Blo 523799 8988569 := bstep (se 2 (by rfl) ⟨3370713, by rfl⟩ : syracuseStep 8988569 = 6741427) B6741427
theorem B2664413 : Blo 523799 2664413 := bstep (se 3 (by rfl) ⟨499577, by rfl⟩ : syracuseStep 2664413 = 999155) B999155
theorem B632875 : Blo 523799 632875 := bstep (se 1 (by rfl) ⟨474656, by rfl⟩ : syracuseStep 632875 = 949313) B949313
theorem B2664737 : Blo 523799 2664737 := bstep (se 2 (by rfl) ⟨999276, by rfl⟩ : syracuseStep 2664737 = 1998553) B1998553
theorem B1780001 : Blo 523799 1780001 := bstep (se 2 (by rfl) ⟨667500, by rfl⟩ : syracuseStep 1780001 = 1335001) B1335001
theorem B2992727 : Blo 523799 2992727 := bstep (se 1 (by rfl) ⟨2244545, by rfl⟩ : syracuseStep 2992727 = 4489091) B4489091
theorem B797303 : Blo 523799 797303 := bstep (se 1 (by rfl) ⟨597977, by rfl⟩ : syracuseStep 797303 = 1195955) B1195955
theorem B1124999 : Blo 523799 1124999 := bstep (se 1 (by rfl) ⟨843749, by rfl⟩ : syracuseStep 1124999 = 1687499) B1687499
theorem B1780595 : Blo 523799 1780595 := bstep (se 1 (by rfl) ⟨1335446, by rfl⟩ : syracuseStep 1780595 = 2670893) B2670893
theorem B1125409 : Blo 523799 1125409 := bstep (se 2 (by rfl) ⟨422028, by rfl⟩ : syracuseStep 1125409 = 844057) B844057
theorem B2665709 : Blo 523799 2665709 := bstep (se 3 (by rfl) ⟨499820, by rfl⟩ : syracuseStep 2665709 = 999641) B999641
theorem B1420573 : Blo 523799 1420573 := bstep (se 3 (by rfl) ⟨266357, by rfl⟩ : syracuseStep 1420573 = 532715) B532715
theorem B1125751 : Blo 523799 1125751 := bstep (se 1 (by rfl) ⟨844313, by rfl⟩ : syracuseStep 1125751 = 1688627) B1688627
theorem B7581113 : Blo 523799 7581113 := bstep (se 2 (by rfl) ⟨2842917, by rfl⟩ : syracuseStep 7581113 = 5685835) B5685835
theorem B1420811 : Blo 523799 1420811 := bstep (se 1 (by rfl) ⟨1065608, by rfl⟩ : syracuseStep 1420811 = 2131217) B2131217
theorem B1420919 : Blo 523799 1420919 := bstep (se 1 (by rfl) ⟨1065689, by rfl⟩ : syracuseStep 1420919 = 2131379) B2131379
theorem B995017 : Blo 523799 995017 := bstep (se 2 (by rfl) ⟨373131, by rfl⟩ : syracuseStep 995017 = 746263) B746263
theorem B667435 : Blo 523799 667435 := bstep (se 1 (by rfl) ⟨500576, by rfl⟩ : syracuseStep 667435 = 1001153) B1001153
theorem B2666519 : Blo 523799 2666519 := bstep (se 1 (by rfl) ⟨1999889, by rfl⟩ : syracuseStep 2666519 = 3999779) B3999779
theorem B1126715 : Blo 523799 1126715 := bstep (se 1 (by rfl) ⟨845036, by rfl⟩ : syracuseStep 1126715 = 1690073) B1690073
theorem B2994641 : Blo 523799 2994641 := bstep (se 2 (by rfl) ⟨1122990, by rfl⟩ : syracuseStep 2994641 = 2245981) B2245981
theorem B1126955 : Blo 523799 1126955 := bstep (se 1 (by rfl) ⟨845216, by rfl⟩ : syracuseStep 1126955 = 1690433) B1690433
theorem B3781187 : Blo 523799 3781187 := bstep (se 1 (by rfl) ⟨2835890, by rfl⟩ : syracuseStep 3781187 = 5671781) B5671781
theorem B1061903 : Blo 523799 1061903 := bstep (se 1 (by rfl) ⟨796427, by rfl⟩ : syracuseStep 1061903 = 1592855) B1592855
theorem B1684871 : Blo 523799 1684871 := bstep (se 1 (by rfl) ⟨1263653, by rfl⟩ : syracuseStep 1684871 = 2527307) B2527307
theorem B6403475 : Blo 523799 6403475 := bstep (se 1 (by rfl) ⟨4802606, by rfl⟩ : syracuseStep 6403475 = 9605213) B9605213
theorem B5387705 : Blo 523799 5387705 := bstep (se 2 (by rfl) ⟨2020389, by rfl⟩ : syracuseStep 5387705 = 4040779) B4040779
theorem B4306385 : Blo 523799 4306385 := bstep (se 2 (by rfl) ⟨1614894, by rfl⟩ : syracuseStep 4306385 = 3229789) B3229789
theorem B996923 : Blo 523799 996923 := bstep (se 1 (by rfl) ⟨747692, by rfl⟩ : syracuseStep 996923 = 1495385) B1495385
theorem B800519 : Blo 523799 800519 := bstep (se 1 (by rfl) ⟨600389, by rfl⟩ : syracuseStep 800519 = 1200779) B1200779
theorem B1685281 : Blo 523799 1685281 := bstep (se 2 (by rfl) ⟨631980, by rfl⟩ : syracuseStep 1685281 = 1263961) B1263961
theorem B5748515 : Blo 523799 5748515 := bstep (se 1 (by rfl) ⟨4311386, by rfl⟩ : syracuseStep 5748515 = 8622773) B8622773
theorem B8533811 : Blo 523799 8533811 := bstep (se 1 (by rfl) ⟨6400358, by rfl⟩ : syracuseStep 8533811 = 12800717) B12800717
theorem B997409 : Blo 523799 997409 := bstep (se 2 (by rfl) ⟨374028, by rfl⟩ : syracuseStep 997409 = 748057) B748057
theorem B1554491 : Blo 523799 1554491 := bstep (se 1 (by rfl) ⟨1165868, by rfl⟩ : syracuseStep 1554491 = 2331737) B2331737
theorem B1259705 : Blo 523799 1259705 := bstep (se 2 (by rfl) ⟨472389, by rfl⟩ : syracuseStep 1259705 = 944779) B944779
theorem B801031 : Blo 523799 801031 := bstep (se 1 (by rfl) ⟨600773, by rfl⟩ : syracuseStep 801031 = 1201547) B1201547
theorem B1063201 : Blo 523799 1063201 := bstep (se 2 (by rfl) ⟨398700, by rfl⟩ : syracuseStep 1063201 = 797401) B797401
theorem B997751 : Blo 523799 997751 := bstep (se 1 (by rfl) ⟨748313, by rfl⟩ : syracuseStep 997751 = 1496627) B1496627
theorem B3979853 : Blo 523799 3979853 := bstep (se 3 (by rfl) ⟨746222, by rfl⟩ : syracuseStep 3979853 = 1492445) B1492445
theorem B1260289 : Blo 523799 1260289 := bstep (se 2 (by rfl) ⟨472608, by rfl⟩ : syracuseStep 1260289 = 945217) B945217
theorem B1326091 : Blo 523799 1326091 := bstep (se 1 (by rfl) ⟨994568, by rfl⟩ : syracuseStep 1326091 = 1989137) B1989137
theorem B2669597 : Blo 523799 2669597 := bstep (se 3 (by rfl) ⟨500549, by rfl⟩ : syracuseStep 2669597 = 1001099) B1001099
theorem B1326233 : Blo 523799 1326233 := bstep (se 2 (by rfl) ⟨497337, by rfl⟩ : syracuseStep 1326233 = 994675) B994675
theorem B1326395 : Blo 523799 1326395 := bstep (se 1 (by rfl) ⟨994796, by rfl⟩ : syracuseStep 1326395 = 1989593) B1989593
theorem B3030419 : Blo 523799 3030419 := bstep (se 1 (by rfl) ⟨2272814, by rfl⟩ : syracuseStep 3030419 = 4545629) B4545629
theorem B2670083 : Blo 523799 2670083 := bstep (se 1 (by rfl) ⟨2002562, by rfl⟩ : syracuseStep 2670083 = 4005125) B4005125
theorem B1326739 : Blo 523799 1326739 := bstep (se 1 (by rfl) ⟨995054, by rfl⟩ : syracuseStep 1326739 = 1990109) B1990109
theorem B6504113 : Blo 523799 6504113 := bstep (se 2 (by rfl) ⟨2439042, by rfl⟩ : syracuseStep 6504113 = 4878085) B4878085
theorem B10141361 : Blo 523799 10141361 := bstep (se 2 (by rfl) ⟨3803010, by rfl⟩ : syracuseStep 10141361 = 7606021) B7606021
theorem B1261327 : Blo 523799 1261327 := bstep (se 1 (by rfl) ⟨945995, by rfl⟩ : syracuseStep 1261327 = 1891991) B1891991
theorem B1326881 : Blo 523799 1326881 := bstep (se 2 (by rfl) ⟨497580, by rfl⟩ : syracuseStep 1326881 = 995161) B995161
theorem B999353 : Blo 523799 999353 := bstep (se 2 (by rfl) ⟨374757, by rfl⟩ : syracuseStep 999353 = 749515) B749515
theorem B3784877 : Blo 523799 3784877 := bstep (se 3 (by rfl) ⟨709664, by rfl⟩ : syracuseStep 3784877 = 1419329) B1419329
theorem B12828941 : Blo 523799 12828941 := bstep (se 3 (by rfl) ⟨2405426, by rfl⟩ : syracuseStep 12828941 = 4810853) B4810853
theorem B999695 : Blo 523799 999695 := bstep (se 1 (by rfl) ⟨749771, by rfl⟩ : syracuseStep 999695 = 1499543) B1499543
theorem B2834747 : Blo 523799 2834747 := bstep (se 1 (by rfl) ⟨2126060, by rfl⟩ : syracuseStep 2834747 = 4252121) B4252121
theorem B1261943 : Blo 523799 1261943 := bstep (se 1 (by rfl) ⟨946457, by rfl⟩ : syracuseStep 1261943 = 1892915) B1892915
theorem B2736605 : Blo 523799 2736605 := bstep (se 3 (by rfl) ⟨513113, by rfl⟩ : syracuseStep 2736605 = 1026227) B1026227
theorem B5980715 : Blo 523799 5980715 := bstep (se 1 (by rfl) ⟨4485536, by rfl⟩ : syracuseStep 5980715 = 8971073) B8971073
theorem B2310743 : Blo 523799 2310743 := bstep (se 1 (by rfl) ⟨1733057, by rfl⟩ : syracuseStep 2310743 = 3466115) B3466115
theorem B1327873 : Blo 523799 1327873 := bstep (se 2 (by rfl) ⟨497952, by rfl⟩ : syracuseStep 1327873 = 995905) B995905
theorem B1262395 : Blo 523799 1262395 := bstep (se 1 (by rfl) ⟨946796, by rfl⟩ : syracuseStep 1262395 = 1893593) B1893593
theorem B1262423 : Blo 523799 1262423 := bstep (se 1 (by rfl) ⟨946817, by rfl⟩ : syracuseStep 1262423 = 1893635) B1893635
theorem B3982283 : Blo 523799 3982283 := bstep (se 1 (by rfl) ⟨2986712, by rfl⟩ : syracuseStep 3982283 = 5973425) B5973425
theorem B1491979 : Blo 523799 1491979 := bstep (se 1 (by rfl) ⟨1118984, by rfl⟩ : syracuseStep 1491979 = 2237969) B2237969
theorem B1000507 : Blo 523799 1000507 := bstep (se 1 (by rfl) ⟨750380, by rfl⟩ : syracuseStep 1000507 = 1500761) B1500761
theorem B2671703 : Blo 523799 2671703 := bstep (se 1 (by rfl) ⟨2003777, by rfl⟩ : syracuseStep 2671703 = 4007555) B4007555
theorem B1000583 : Blo 523799 1000583 := bstep (se 1 (by rfl) ⟨750437, by rfl⟩ : syracuseStep 1000583 = 1500875) B1500875
theorem B1492253 : Blo 523799 1492253 := bstep (se 3 (by rfl) ⟨279797, by rfl⟩ : syracuseStep 1492253 = 559595) B559595
theorem B1328471 : Blo 523799 1328471 := bstep (se 1 (by rfl) ⟨996353, by rfl⟩ : syracuseStep 1328471 = 1992707) B1992707
theorem B2999699 : Blo 523799 2999699 := bstep (se 1 (by rfl) ⟨2249774, by rfl⟩ : syracuseStep 2999699 = 4499549) B4499549
theorem B1000993 : Blo 523799 1000993 := bstep (se 2 (by rfl) ⟨375372, by rfl⟩ : syracuseStep 1000993 = 750745) B750745
theorem B1328683 : Blo 523799 1328683 := bstep (se 1 (by rfl) ⟨996512, by rfl⟩ : syracuseStep 1328683 = 1993025) B1993025
theorem B1328825 : Blo 523799 1328825 := bstep (se 2 (by rfl) ⟨498309, by rfl⟩ : syracuseStep 1328825 = 996619) B996619
theorem B1263289 : Blo 523799 1263289 := bstep (se 2 (by rfl) ⟨473733, by rfl⟩ : syracuseStep 1263289 = 947467) B947467
theorem B1001335 : Blo 523799 1001335 := bstep (se 1 (by rfl) ⟨751001, by rfl⟩ : syracuseStep 1001335 = 1502003) B1502003
theorem B3000199 : Blo 523799 3000199 := bstep (se 1 (by rfl) ⟨2250149, by rfl⟩ : syracuseStep 3000199 = 4500299) B4500299
theorem B2246717 : Blo 523799 2246717 := bstep (se 3 (by rfl) ⟨421259, by rfl⟩ : syracuseStep 2246717 = 842519) B842519
theorem B3361283 : Blo 523799 3361283 := bstep (se 1 (by rfl) ⟨2520962, by rfl⟩ : syracuseStep 3361283 = 5041925) B5041925
theorem B2837035 : Blo 523799 2837035 := bstep (se 1 (by rfl) ⟨2127776, by rfl⟩ : syracuseStep 2837035 = 4255553) B4255553
theorem B15419969 : Blo 523799 15419969 := bstep (se 2 (by rfl) ⟨5782488, by rfl⟩ : syracuseStep 15419969 = 11564977) B11564977
theorem B1329817 : Blo 523799 1329817 := bstep (se 2 (by rfl) ⟨498681, by rfl⟩ : syracuseStep 1329817 = 997363) B997363
theorem B6933185 : Blo 523799 6933185 := bstep (se 2 (by rfl) ⟨2599944, by rfl⟩ : syracuseStep 6933185 = 5199889) B5199889
theorem B1329979 : Blo 523799 1329979 := bstep (se 1 (by rfl) ⟨997484, by rfl⟩ : syracuseStep 1329979 = 1994969) B1994969
theorem B1690483 : Blo 523799 1690483 := bstep (se 1 (by rfl) ⟨1267862, by rfl⟩ : syracuseStep 1690483 = 2535725) B2535725
theorem B1330121 : Blo 523799 1330121 := bstep (se 2 (by rfl) ⟨498795, by rfl⟩ : syracuseStep 1330121 = 997591) B997591
theorem B1330465 : Blo 523799 1330465 := bstep (se 2 (by rfl) ⟨498924, by rfl⟩ : syracuseStep 1330465 = 997849) B997849
theorem B1494359 : Blo 523799 1494359 := bstep (se 1 (by rfl) ⟨1120769, by rfl⟩ : syracuseStep 1494359 = 2241539) B2241539
theorem B5131613 : Blo 523799 5131613 := bstep (se 3 (by rfl) ⟨962177, by rfl⟩ : syracuseStep 5131613 = 1924355) B1924355
theorem B1494587 : Blo 523799 1494587 := bstep (se 1 (by rfl) ⟨1120940, by rfl⟩ : syracuseStep 1494587 = 2241881) B2241881
theorem B1494713 : Blo 523799 1494713 := bstep (se 2 (by rfl) ⟨560517, by rfl⟩ : syracuseStep 1494713 = 1121035) B1121035
theorem B1331063 : Blo 523799 1331063 := bstep (se 1 (by rfl) ⟨998297, by rfl⟩ : syracuseStep 1331063 = 1996595) B1996595
theorem B2838419 : Blo 523799 2838419 := bstep (se 1 (by rfl) ⟨2128814, by rfl⟩ : syracuseStep 2838419 = 4257629) B4257629
theorem B2248715 : Blo 523799 2248715 := bstep (se 1 (by rfl) ⟨1686536, by rfl⟩ : syracuseStep 2248715 = 3373073) B3373073
theorem B5067143 : Blo 523799 5067143 := bstep (se 1 (by rfl) ⟨3800357, by rfl⟩ : syracuseStep 5067143 = 7600715) B7600715
theorem B18469397 : Blo 523799 18469397 := bstep (se 6 (by rfl) ⟨432876, by rfl⟩ : syracuseStep 18469397 = 865753) B865753
theorem B8966699 : Blo 523799 8966699 := bstep (se 1 (by rfl) ⟨6725024, by rfl⟩ : syracuseStep 8966699 = 13450049) B13450049
theorem B1069687 : Blo 523799 1069687 := bstep (se 1 (by rfl) ⟨802265, by rfl⟩ : syracuseStep 1069687 = 1604531) B1604531
theorem B1332359 : Blo 523799 1332359 := bstep (se 1 (by rfl) ⟨999269, by rfl⟩ : syracuseStep 1332359 = 1998539) B1998539
theorem B1332409 : Blo 523799 1332409 := bstep (se 2 (by rfl) ⟨499653, by rfl⟩ : syracuseStep 1332409 = 999307) B999307
theorem B1496353 : Blo 523799 1496353 := bstep (se 2 (by rfl) ⟨561132, by rfl⟩ : syracuseStep 1496353 = 1122265) B1122265
theorem B1889671 : Blo 523799 1889671 := bstep (se 1 (by rfl) ⟨1417253, by rfl⟩ : syracuseStep 1889671 = 2834507) B2834507
theorem B4871609 : Blo 523799 4871609 := bstep (se 2 (by rfl) ⟨1826853, by rfl⟩ : syracuseStep 4871609 = 3653707) B3653707
theorem B4478429 : Blo 523799 4478429 := bstep (se 3 (by rfl) ⟨839705, by rfl⟩ : syracuseStep 4478429 = 1679411) B1679411
theorem B3200573 : Blo 523799 3200573 := bstep (se 3 (by rfl) ⟨600107, by rfl⟩ : syracuseStep 3200573 = 1200215) B1200215
theorem B1496843 : Blo 523799 1496843 := bstep (se 1 (by rfl) ⟨1122632, by rfl⟩ : syracuseStep 1496843 = 2245265) B2245265
theorem B1333007 : Blo 523799 1333007 := bstep (se 1 (by rfl) ⟨999755, by rfl⟩ : syracuseStep 1333007 = 1999511) B1999511
theorem B6739787 : Blo 523799 6739787 := bstep (se 1 (by rfl) ⟨5054840, by rfl⟩ : syracuseStep 6739787 = 10109681) B10109681
theorem B2021267 : Blo 523799 2021267 := bstep (se 1 (by rfl) ⟨1515950, by rfl⟩ : syracuseStep 2021267 = 3031901) B3031901
theorem B2873291 : Blo 523799 2873291 := bstep (se 1 (by rfl) ⟨2154968, by rfl⟩ : syracuseStep 2873291 = 4309937) B4309937
theorem B3987629 : Blo 523799 3987629 := bstep (se 3 (by rfl) ⟨747680, by rfl⟩ : syracuseStep 3987629 = 1495361) B1495361
theorem B1333705 : Blo 523799 1333705 := bstep (se 2 (by rfl) ⟨500139, by rfl⟩ : syracuseStep 1333705 = 1000279) B1000279
theorem B1497629 : Blo 523799 1497629 := bstep (se 3 (by rfl) ⟨280805, by rfl⟩ : syracuseStep 1497629 = 561611) B561611
theorem B711227 : Blo 523799 711227 := bstep (se 1 (by rfl) ⟨533420, by rfl⟩ : syracuseStep 711227 = 1066841) B1066841
theorem B1333847 : Blo 523799 1333847 := bstep (se 1 (by rfl) ⟨1000385, by rfl⟩ : syracuseStep 1333847 = 2000771) B2000771
theorem B10902197 : Blo 523799 10902197 := bstep (se 5 (by rfl) ⟨511040, by rfl⟩ : syracuseStep 10902197 = 1022081) B1022081
theorem B5069603 : Blo 523799 5069603 := bstep (se 1 (by rfl) ⟨3802202, by rfl⟩ : syracuseStep 5069603 = 7604405) B7604405
theorem B842795 : Blo 523799 842795 := bstep (se 1 (by rfl) ⟨632096, by rfl⟩ : syracuseStep 842795 = 1264193) B1264193
theorem B3365975 : Blo 523799 3365975 := bstep (se 1 (by rfl) ⟨2524481, by rfl⟩ : syracuseStep 3365975 = 5048963) B5048963
theorem B5069911 : Blo 523799 5069911 := bstep (se 1 (by rfl) ⟨3802433, by rfl⟩ : syracuseStep 5069911 = 7604867) B7604867
theorem B908489 : Blo 523799 908489 := bstep (se 2 (by rfl) ⟨340683, by rfl⟩ : syracuseStep 908489 = 681367) B681367
theorem B3005849 : Blo 523799 3005849 := bstep (se 2 (by rfl) ⟨1127193, by rfl⟩ : syracuseStep 3005849 = 2254387) B2254387
theorem B3038921 : Blo 523799 3038921 := bstep (se 2 (by rfl) ⟨1139595, by rfl⟩ : syracuseStep 3038921 = 2279191) B2279191
theorem B1597243 : Blo 523799 1597243 := bstep (se 1 (by rfl) ⟨1197932, by rfl⟩ : syracuseStep 1597243 = 2395865) B2395865
theorem B3203101 : Blo 523799 3203101 := bstep (se 3 (by rfl) ⟨600581, by rfl⟩ : syracuseStep 3203101 = 1201163) B1201163
theorem B2253089 : Blo 523799 2253089 := bstep (se 2 (by rfl) ⟨844908, by rfl⟩ : syracuseStep 2253089 = 1689817) B1689817
theorem B10215827 : Blo 523799 10215827 := bstep (se 1 (by rfl) ⟨7661870, by rfl⟩ : syracuseStep 10215827 = 15323741) B15323741
theorem B3990059 : Blo 523799 3990059 := bstep (se 1 (by rfl) ⟨2992544, by rfl⟩ : syracuseStep 3990059 = 5985089) B5985089
theorem B1499735 : Blo 523799 1499735 := bstep (se 1 (by rfl) ⟨1124801, by rfl⟩ : syracuseStep 1499735 = 2249603) B2249603
theorem B1335923 : Blo 523799 1335923 := bstep (se 1 (by rfl) ⟨1001942, by rfl⟩ : syracuseStep 1335923 = 2003885) B2003885
theorem B14377817 : Blo 523799 14377817 := bstep (se 2 (by rfl) ⟨5391681, by rfl⟩ : syracuseStep 14377817 = 10783363) B10783363
theorem B105014341 : Blo 523799 105014341 := bstep (se 4 (by rfl) ⟨9845094, by rfl⟩ : syracuseStep 105014341 = 19690189) B19690189
theorem B5989463 : Blo 523799 5989463 := bstep (se 1 (by rfl) ⟨4492097, by rfl⟩ : syracuseStep 5989463 = 8984195) B8984195
theorem B16442657 : Blo 523799 16442657 := bstep (se 2 (by rfl) ⟨6165996, by rfl⟩ : syracuseStep 16442657 = 12331993) B12331993
theorem B1500601 : Blo 523799 1500601 := bstep (se 2 (by rfl) ⟨562725, by rfl⟩ : syracuseStep 1500601 = 1125451) B1125451
theorem B1992221 : Blo 523799 1992221 := bstep (se 3 (by rfl) ⟨373541, by rfl⟩ : syracuseStep 1992221 = 747083) B747083
theorem B1992235 : Blo 523799 1992235 := bstep (se 1 (by rfl) ⟨1494176, by rfl⟩ : syracuseStep 1992235 = 2988353) B2988353
theorem B1500943 : Blo 523799 1500943 := bstep (se 1 (by rfl) ⟨1125707, by rfl⟩ : syracuseStep 1500943 = 2251415) B2251415
theorem B3008477 : Blo 523799 3008477 := bstep (se 3 (by rfl) ⟨564089, by rfl⟩ : syracuseStep 3008477 = 1128179) B1128179
theorem B1501217 : Blo 523799 1501217 := bstep (se 2 (by rfl) ⟨562956, by rfl⟩ : syracuseStep 1501217 = 1125913) B1125913
theorem B2844733 : Blo 523799 2844733 := bstep (se 3 (by rfl) ⟨533387, by rfl⟩ : syracuseStep 2844733 = 1066775) B1066775
theorem B747721 : Blo 523799 747721 := bstep (se 2 (by rfl) ⟨280395, by rfl⟩ : syracuseStep 747721 = 560791) B560791
theorem B1501831 : Blo 523799 1501831 := bstep (se 1 (by rfl) ⟨1126373, by rfl⟩ : syracuseStep 1501831 = 2252747) B2252747
theorem B1797011 : Blo 523799 1797011 := bstep (se 1 (by rfl) ⟨1347758, by rfl⟩ : syracuseStep 1797011 = 2695517) B2695517
theorem B1502219 : Blo 523799 1502219 := bstep (se 1 (by rfl) ⟨1126664, by rfl⟩ : syracuseStep 1502219 = 2253329) B2253329
theorem B2845925 : Blo 523799 2845925 := bstep (se 4 (by rfl) ⟨266805, by rfl⟩ : syracuseStep 2845925 = 533611) B533611
theorem B1895681 : Blo 523799 1895681 := bstep (se 2 (by rfl) ⟨710880, by rfl⟩ : syracuseStep 1895681 = 1421761) B1421761
theorem B2125703 : Blo 523799 2125703 := bstep (se 1 (by rfl) ⟨1594277, by rfl⟩ : syracuseStep 2125703 = 3188555) B3188555
theorem B2880193 : Blo 523799 2880193 := bstep (se 2 (by rfl) ⟨1080072, by rfl⟩ : syracuseStep 2880193 = 2160145) B2160145
theorem B750665 : Blo 523799 750665 := bstep (se 2 (by rfl) ⟨281499, by rfl⟩ : syracuseStep 750665 = 562999) B562999
theorem B8975447 : Blo 523799 8975447 := bstep (se 1 (by rfl) ⟨6731585, by rfl⟩ : syracuseStep 8975447 = 13463171) B13463171
theorem B28865969 : Blo 523799 28865969 := bstep (se 2 (by rfl) ⟨10824738, by rfl⟩ : syracuseStep 28865969 = 21649477) B21649477
theorem B2849039 : Blo 523799 2849039 := bstep (se 1 (by rfl) ⟨2136779, by rfl⟩ : syracuseStep 2849039 = 4273559) B4273559
theorem B1997399 : Blo 523799 1997399 := bstep (se 1 (by rfl) ⟨1498049, by rfl⟩ : syracuseStep 1997399 = 2996099) B2996099
theorem B1440371 : Blo 523799 1440371 := bstep (se 1 (by rfl) ⟨1080278, by rfl⟩ : syracuseStep 1440371 = 2160557) B2160557
theorem B1440545 : Blo 523799 1440545 := bstep (se 2 (by rfl) ⟨540204, by rfl⟩ : syracuseStep 1440545 = 1080409) B1080409
theorem B2653073 : Blo 523799 2653073 := bstep (se 2 (by rfl) ⟨994902, by rfl⟩ : syracuseStep 2653073 = 1989805) B1989805
theorem B1178639 : Blo 523799 1178639 := bstep (se 1 (by rfl) ⟨883979, by rfl⟩ : syracuseStep 1178639 = 1767959) B1767959
theorem B1178657 : Blo 523799 1178657 := bstep (se 2 (by rfl) ⟨441996, by rfl⟩ : syracuseStep 1178657 = 883993) B883993
theorem B1997885 : Blo 523799 1997885 := bstep (se 3 (by rfl) ⟨374603, by rfl⟩ : syracuseStep 1997885 = 749207) B749207
theorem B785723 : Blo 523799 785723 := bstep (se 1 (by rfl) ⟨589292, by rfl⟩ : syracuseStep 785723 = 1178585) B1178585
theorem B884027 : Blo 523799 884027 := bstep (se 1 (by rfl) ⟨663020, by rfl⟩ : syracuseStep 884027 = 1326041) B1326041
theorem B785783 : Blo 523799 785783 := bstep (se 1 (by rfl) ⟨589337, by rfl⟩ : syracuseStep 785783 = 1178675) B1178675
theorem B1178999 : Blo 523799 1178999 := bstep (se 1 (by rfl) ⟨884249, by rfl⟩ : syracuseStep 1178999 = 1768499) B1768499
theorem B785807 : Blo 523799 785807 := bstep (se 1 (by rfl) ⟨589355, by rfl⟩ : syracuseStep 785807 = 1178711) B1178711
theorem B785849 : Blo 523799 785849 := bstep (se 2 (by rfl) ⟨294693, by rfl⟩ : syracuseStep 785849 = 589387) B589387
theorem B785927 : Blo 523799 785927 := bstep (se 1 (by rfl) ⟨589445, by rfl⟩ : syracuseStep 785927 = 1178891) B1178891
theorem B785963 : Blo 523799 785963 := bstep (se 1 (by rfl) ⟨589472, by rfl⟩ : syracuseStep 785963 = 1178945) B1178945
theorem B1179179 : Blo 523799 1179179 := bstep (se 1 (by rfl) ⟨884384, by rfl⟩ : syracuseStep 1179179 = 1768769) B1768769
theorem B523835 : Blo 523799 523835 := bstep (se 1 (by rfl) ⟨392876, by rfl⟩ : syracuseStep 523835 = 785753) B785753
theorem B1900093 : Blo 523799 1900093 := bstep (se 3 (by rfl) ⟨356267, by rfl⟩ : syracuseStep 1900093 = 712535) B712535
theorem B785993 : Blo 523799 785993 := bstep (se 2 (by rfl) ⟨294747, by rfl⟩ : syracuseStep 785993 = 589495) B589495
theorem B523911 : Blo 523799 523911 := bstep (se 1 (by rfl) ⟨392933, by rfl⟩ : syracuseStep 523911 = 785867) B785867
theorem B523919 : Blo 523799 523919 := bstep (se 1 (by rfl) ⟨392939, by rfl⟩ : syracuseStep 523919 = 785879) B785879
theorem B523963 : Blo 523799 523963 := bstep (se 1 (by rfl) ⟨392972, by rfl⟩ : syracuseStep 523963 = 785945) B785945
theorem B786107 : Blo 523799 786107 := bstep (se 1 (by rfl) ⟨589580, by rfl⟩ : syracuseStep 786107 = 1179161) B1179161
theorem B884425 : Blo 523799 884425 := bstep (se 2 (by rfl) ⟨331659, by rfl⟩ : syracuseStep 884425 = 663319) B663319
theorem B786167 : Blo 523799 786167 := bstep (se 1 (by rfl) ⟨589625, by rfl⟩ : syracuseStep 786167 = 1179251) B1179251
theorem B524039 : Blo 523799 524039 := bstep (se 1 (by rfl) ⟨393029, by rfl⟩ : syracuseStep 524039 = 786059) B786059
theorem B524047 : Blo 523799 524047 := bstep (se 1 (by rfl) ⟨393035, by rfl⟩ : syracuseStep 524047 = 786071) B786071
theorem B786191 : Blo 523799 786191 := bstep (se 1 (by rfl) ⟨589643, by rfl⟩ : syracuseStep 786191 = 1179287) B1179287
theorem B786233 : Blo 523799 786233 := bstep (se 2 (by rfl) ⟨294837, by rfl⟩ : syracuseStep 786233 = 589675) B589675
theorem B524091 : Blo 523799 524091 := bstep (se 1 (by rfl) ⟨393068, by rfl⟩ : syracuseStep 524091 = 786137) B786137
theorem B524167 : Blo 523799 524167 := bstep (se 1 (by rfl) ⟨393125, by rfl⟩ : syracuseStep 524167 = 786251) B786251
theorem B786311 : Blo 523799 786311 := bstep (se 1 (by rfl) ⟨589733, by rfl⟩ : syracuseStep 786311 = 1179467) B1179467
theorem B524175 : Blo 523799 524175 := bstep (se 1 (by rfl) ⟨393131, by rfl⟩ : syracuseStep 524175 = 786263) B786263
theorem B589711 : Blo 523799 589711 := bstep (se 1 (by rfl) ⟨442283, by rfl⟩ : syracuseStep 589711 = 884567) B884567
theorem B1179539 : Blo 523799 1179539 := bstep (se 1 (by rfl) ⟨884654, by rfl⟩ : syracuseStep 1179539 = 1769309) B1769309
theorem B1769363 : Blo 523799 1769363 := bstep (se 1 (by rfl) ⟨1327022, by rfl⟩ : syracuseStep 1769363 = 2654045) B2654045
theorem B786347 : Blo 523799 786347 := bstep (se 1 (by rfl) ⟨589760, by rfl⟩ : syracuseStep 786347 = 1179521) B1179521
theorem B524219 : Blo 523799 524219 := bstep (se 1 (by rfl) ⟨393164, by rfl⟩ : syracuseStep 524219 = 786329) B786329
theorem B786377 : Blo 523799 786377 := bstep (se 2 (by rfl) ⟨294891, by rfl⟩ : syracuseStep 786377 = 589783) B589783
theorem B1179593 : Blo 523799 1179593 := bstep (se 2 (by rfl) ⟨442347, by rfl⟩ : syracuseStep 1179593 = 884695) B884695
theorem B524327 : Blo 523799 524327 := bstep (se 1 (by rfl) ⟨393245, by rfl⟩ : syracuseStep 524327 = 786491) B786491
theorem B524367 : Blo 523799 524367 := bstep (se 1 (by rfl) ⟨393275, by rfl⟩ : syracuseStep 524367 = 786551) B786551
theorem B524383 : Blo 523799 524383 := bstep (se 1 (by rfl) ⟨393287, by rfl⟩ : syracuseStep 524383 = 786575) B786575
theorem B2523251 : Blo 523799 2523251 := bstep (se 1 (by rfl) ⟨1892438, by rfl⟩ : syracuseStep 2523251 = 3784877) B3784877
theorem B524411 : Blo 523799 524411 := bstep (se 1 (by rfl) ⟨393308, by rfl⟩ : syracuseStep 524411 = 786617) B786617
theorem B524463 : Blo 523799 524463 := bstep (se 1 (by rfl) ⟨393347, by rfl⟩ : syracuseStep 524463 = 786695) B786695
theorem B8552627 : Blo 523799 8552627 := bstep (se 1 (by rfl) ⟨6414470, by rfl⟩ : syracuseStep 8552627 = 12828941) B12828941
theorem B524487 : Blo 523799 524487 := bstep (se 1 (by rfl) ⟨393365, by rfl⟩ : syracuseStep 524487 = 786731) B786731
theorem B524507 : Blo 523799 524507 := bstep (se 1 (by rfl) ⟨393380, by rfl⟩ : syracuseStep 524507 = 786761) B786761
theorem B524583 : Blo 523799 524583 := bstep (se 1 (by rfl) ⟨393437, by rfl⟩ : syracuseStep 524583 = 786875) B786875
theorem B524623 : Blo 523799 524623 := bstep (se 1 (by rfl) ⟨393467, by rfl⟩ : syracuseStep 524623 = 786935) B786935
theorem B524639 : Blo 523799 524639 := bstep (se 1 (by rfl) ⟨393479, by rfl⟩ : syracuseStep 524639 = 786959) B786959
theorem B524667 : Blo 523799 524667 := bstep (se 1 (by rfl) ⟨393500, by rfl⟩ : syracuseStep 524667 = 787001) B787001
theorem B1540495 : Blo 523799 1540495 := bstep (se 1 (by rfl) ⟨1155371, by rfl⟩ : syracuseStep 1540495 = 2310743) B2310743
theorem B786863 : Blo 523799 786863 := bstep (se 1 (by rfl) ⟨590147, by rfl⟩ : syracuseStep 786863 = 1180295) B1180295
theorem B524719 : Blo 523799 524719 := bstep (se 1 (by rfl) ⟨393539, by rfl⟩ : syracuseStep 524719 = 787079) B787079
theorem B524743 : Blo 523799 524743 := bstep (se 1 (by rfl) ⟨393557, by rfl⟩ : syracuseStep 524743 = 787115) B787115
theorem B524763 : Blo 523799 524763 := bstep (se 1 (by rfl) ⟨393572, by rfl⟩ : syracuseStep 524763 = 787145) B787145
theorem B1180169 : Blo 523799 1180169 := bstep (se 2 (by rfl) ⟨442563, by rfl⟩ : syracuseStep 1180169 = 885127) B885127
theorem B786953 : Blo 523799 786953 := bstep (se 2 (by rfl) ⟨295107, by rfl⟩ : syracuseStep 786953 = 590215) B590215
theorem B786983 : Blo 523799 786983 := bstep (se 1 (by rfl) ⟨590237, by rfl⟩ : syracuseStep 786983 = 1180475) B1180475
theorem B524839 : Blo 523799 524839 := bstep (se 1 (by rfl) ⟨393629, by rfl⟩ : syracuseStep 524839 = 787259) B787259
theorem B524879 : Blo 523799 524879 := bstep (se 1 (by rfl) ⟨393659, by rfl⟩ : syracuseStep 524879 = 787319) B787319
theorem B524895 : Blo 523799 524895 := bstep (se 1 (by rfl) ⟨393671, by rfl⟩ : syracuseStep 524895 = 787343) B787343
theorem B787067 : Blo 523799 787067 := bstep (se 1 (by rfl) ⟨590300, by rfl⟩ : syracuseStep 787067 = 1180601) B1180601
theorem B524923 : Blo 523799 524923 := bstep (se 1 (by rfl) ⟨393692, by rfl⟩ : syracuseStep 524923 = 787385) B787385
theorem B2654855 : Blo 523799 2654855 := bstep (se 1 (by rfl) ⟨1991141, by rfl⟩ : syracuseStep 2654855 = 3982283) B3982283
theorem B1770119 : Blo 523799 1770119 := bstep (se 1 (by rfl) ⟨1327589, by rfl⟩ : syracuseStep 1770119 = 2655179) B2655179
theorem B524975 : Blo 523799 524975 := bstep (se 1 (by rfl) ⟨393731, by rfl⟩ : syracuseStep 524975 = 787463) B787463
theorem B1770173 : Blo 523799 1770173 := bstep (se 3 (by rfl) ⟨331907, by rfl⟩ : syracuseStep 1770173 = 663815) B663815
theorem B524999 : Blo 523799 524999 := bstep (se 1 (by rfl) ⟨393749, by rfl⟩ : syracuseStep 524999 = 787499) B787499
theorem B525019 : Blo 523799 525019 := bstep (se 1 (by rfl) ⟨393764, by rfl⟩ : syracuseStep 525019 = 787529) B787529
theorem B787193 : Blo 523799 787193 := bstep (se 2 (by rfl) ⟨295197, by rfl⟩ : syracuseStep 787193 = 590395) B590395
theorem B525095 : Blo 523799 525095 := bstep (se 1 (by rfl) ⟨393821, by rfl⟩ : syracuseStep 525095 = 787643) B787643
theorem B525135 : Blo 523799 525135 := bstep (se 1 (by rfl) ⟨393851, by rfl⟩ : syracuseStep 525135 = 787703) B787703
theorem B1770335 : Blo 523799 1770335 := bstep (se 1 (by rfl) ⟨1327751, by rfl⟩ : syracuseStep 1770335 = 2655503) B2655503
theorem B1180511 : Blo 523799 1180511 := bstep (se 1 (by rfl) ⟨885383, by rfl⟩ : syracuseStep 1180511 = 1770767) B1770767
theorem B787295 : Blo 523799 787295 := bstep (se 1 (by rfl) ⟨590471, by rfl⟩ : syracuseStep 787295 = 1180943) B1180943
theorem B525151 : Blo 523799 525151 := bstep (se 1 (by rfl) ⟨393863, by rfl⟩ : syracuseStep 525151 = 787727) B787727
theorem B787307 : Blo 523799 787307 := bstep (se 1 (by rfl) ⟨590480, by rfl⟩ : syracuseStep 787307 = 1180961) B1180961
theorem B525179 : Blo 523799 525179 := bstep (se 1 (by rfl) ⟨393884, by rfl⟩ : syracuseStep 525179 = 787769) B787769
theorem B885647 : Blo 523799 885647 := bstep (se 1 (by rfl) ⟨664235, by rfl⟩ : syracuseStep 885647 = 1328471) B1328471
theorem B525231 : Blo 523799 525231 := bstep (se 1 (by rfl) ⟨393923, by rfl⟩ : syracuseStep 525231 = 787847) B787847
theorem B1999799 : Blo 523799 1999799 := bstep (se 1 (by rfl) ⟨1499849, by rfl⟩ : syracuseStep 1999799 = 2999699) B2999699
theorem B525255 : Blo 523799 525255 := bstep (se 1 (by rfl) ⟨393941, by rfl⟩ : syracuseStep 525255 = 787883) B787883
theorem B525275 : Blo 523799 525275 := bstep (se 1 (by rfl) ⟨393956, by rfl⟩ : syracuseStep 525275 = 787913) B787913
theorem B1770497 : Blo 523799 1770497 := bstep (se 2 (by rfl) ⟨663936, by rfl⟩ : syracuseStep 1770497 = 1327873) B1327873
theorem B1180691 : Blo 523799 1180691 := bstep (se 1 (by rfl) ⟨885518, by rfl⟩ : syracuseStep 1180691 = 1771037) B1771037
theorem B525351 : Blo 523799 525351 := bstep (se 1 (by rfl) ⟨394013, by rfl⟩ : syracuseStep 525351 = 788027) B788027
theorem B787535 : Blo 523799 787535 := bstep (se 1 (by rfl) ⟨590651, by rfl⟩ : syracuseStep 787535 = 1181303) B1181303
theorem B525391 : Blo 523799 525391 := bstep (se 1 (by rfl) ⟨394043, by rfl⟩ : syracuseStep 525391 = 788087) B788087
theorem B525407 : Blo 523799 525407 := bstep (se 1 (by rfl) ⟨394055, by rfl⟩ : syracuseStep 525407 = 788111) B788111
theorem B885883 : Blo 523799 885883 := bstep (se 1 (by rfl) ⟨664412, by rfl⟩ : syracuseStep 885883 = 1328825) B1328825
theorem B590971 : Blo 523799 590971 := bstep (se 1 (by rfl) ⟨443228, by rfl⟩ : syracuseStep 590971 = 886457) B886457
theorem B525435 : Blo 523799 525435 := bstep (se 1 (by rfl) ⟨394076, by rfl⟩ : syracuseStep 525435 = 788153) B788153
theorem B525487 : Blo 523799 525487 := bstep (se 1 (by rfl) ⟨394115, by rfl⟩ : syracuseStep 525487 = 788231) B788231
theorem B787655 : Blo 523799 787655 := bstep (se 1 (by rfl) ⟨590741, by rfl⟩ : syracuseStep 787655 = 1181483) B1181483
theorem B525511 : Blo 523799 525511 := bstep (se 1 (by rfl) ⟨394133, by rfl⟩ : syracuseStep 525511 = 788267) B788267
theorem B525531 : Blo 523799 525531 := bstep (se 1 (by rfl) ⟨394148, by rfl⟩ : syracuseStep 525531 = 788297) B788297
theorem B525607 : Blo 523799 525607 := bstep (se 1 (by rfl) ⟨394205, by rfl⟩ : syracuseStep 525607 = 788411) B788411
theorem B525647 : Blo 523799 525647 := bstep (se 1 (by rfl) ⟨394235, by rfl⟩ : syracuseStep 525647 = 788471) B788471
theorem B525663 : Blo 523799 525663 := bstep (se 1 (by rfl) ⟨394247, by rfl⟩ : syracuseStep 525663 = 788495) B788495
theorem B1181033 : Blo 523799 1181033 := bstep (se 2 (by rfl) ⟨442887, by rfl⟩ : syracuseStep 1181033 = 885775) B885775
theorem B787817 : Blo 523799 787817 := bstep (se 2 (by rfl) ⟨295431, by rfl⟩ : syracuseStep 787817 = 590863) B590863
theorem B525691 : Blo 523799 525691 := bstep (se 1 (by rfl) ⟨394268, by rfl⟩ : syracuseStep 525691 = 788537) B788537
theorem B525743 : Blo 523799 525743 := bstep (se 1 (by rfl) ⟨394307, by rfl⟩ : syracuseStep 525743 = 788615) B788615
theorem B140019121 : Blo 523799 140019121 := bstep (se 2 (by rfl) ⟨52507170, by rfl⟩ : syracuseStep 140019121 = 105014341) B105014341
theorem B787895 : Blo 523799 787895 := bstep (se 1 (by rfl) ⟨590921, by rfl⟩ : syracuseStep 787895 = 1181843) B1181843
theorem B525767 : Blo 523799 525767 := bstep (se 1 (by rfl) ⟨394325, by rfl⟩ : syracuseStep 525767 = 788651) B788651
theorem B787931 : Blo 523799 787931 := bstep (se 1 (by rfl) ⟨590948, by rfl⟩ : syracuseStep 787931 = 1181897) B1181897
theorem B525787 : Blo 523799 525787 := bstep (se 1 (by rfl) ⟨394340, by rfl⟩ : syracuseStep 525787 = 788681) B788681
theorem B525863 : Blo 523799 525863 := bstep (se 1 (by rfl) ⟨394397, by rfl⟩ : syracuseStep 525863 = 788795) B788795
theorem B3999293 : Blo 523799 3999293 := bstep (se 3 (by rfl) ⟨749867, by rfl⟩ : syracuseStep 3999293 = 1499735) B1499735
theorem B591439 : Blo 523799 591439 := bstep (se 1 (by rfl) ⟨443579, by rfl⟩ : syracuseStep 591439 = 887159) B887159
theorem B525903 : Blo 523799 525903 := bstep (se 1 (by rfl) ⟨394427, by rfl⟩ : syracuseStep 525903 = 788855) B788855
theorem B525919 : Blo 523799 525919 := bstep (se 1 (by rfl) ⟨394439, by rfl⟩ : syracuseStep 525919 = 788879) B788879
theorem B525947 : Blo 523799 525947 := bstep (se 1 (by rfl) ⟨394460, by rfl⟩ : syracuseStep 525947 = 788921) B788921
theorem B525999 : Blo 523799 525999 := bstep (se 1 (by rfl) ⟨394499, by rfl⟩ : syracuseStep 525999 = 788999) B788999
theorem B526023 : Blo 523799 526023 := bstep (se 1 (by rfl) ⟨394517, by rfl⟩ : syracuseStep 526023 = 789035) B789035
theorem B526043 : Blo 523799 526043 := bstep (se 1 (by rfl) ⟨394532, by rfl⟩ : syracuseStep 526043 = 789065) B789065
theorem B526119 : Blo 523799 526119 := bstep (se 1 (by rfl) ⟨394589, by rfl⟩ : syracuseStep 526119 = 789179) B789179
theorem B1771307 : Blo 523799 1771307 := bstep (se 1 (by rfl) ⟨1328480, by rfl⟩ : syracuseStep 1771307 = 2656961) B2656961
theorem B4622123 : Blo 523799 4622123 := bstep (se 1 (by rfl) ⟨3466592, by rfl⟩ : syracuseStep 4622123 = 6933185) B6933185
theorem B526159 : Blo 523799 526159 := bstep (se 1 (by rfl) ⟨394619, by rfl⟩ : syracuseStep 526159 = 789239) B789239
theorem B526175 : Blo 523799 526175 := bstep (se 1 (by rfl) ⟨394631, by rfl⟩ : syracuseStep 526175 = 789263) B789263
theorem B7604063 : Blo 523799 7604063 := bstep (se 1 (by rfl) ⟨5703047, by rfl⟩ : syracuseStep 7604063 = 11406095) B11406095
theorem B526203 : Blo 523799 526203 := bstep (se 1 (by rfl) ⟨394652, by rfl⟩ : syracuseStep 526203 = 789305) B789305
theorem B2000801 : Blo 523799 2000801 := bstep (se 2 (by rfl) ⟨750300, by rfl⟩ : syracuseStep 2000801 = 1500601) B1500601
theorem B788399 : Blo 523799 788399 := bstep (se 1 (by rfl) ⟨591299, by rfl⟩ : syracuseStep 788399 = 1182599) B1182599
theorem B526255 : Blo 523799 526255 := bstep (se 1 (by rfl) ⟨394691, by rfl⟩ : syracuseStep 526255 = 789383) B789383
theorem B1181627 : Blo 523799 1181627 := bstep (se 1 (by rfl) ⟨886220, by rfl⟩ : syracuseStep 1181627 = 1772441) B1772441
theorem B8652737 : Blo 523799 8652737 := bstep (se 2 (by rfl) ⟨3244776, by rfl⟩ : syracuseStep 8652737 = 6489553) B6489553
theorem B526279 : Blo 523799 526279 := bstep (se 1 (by rfl) ⟨394709, by rfl⟩ : syracuseStep 526279 = 789419) B789419
theorem B886747 : Blo 523799 886747 := bstep (se 1 (by rfl) ⟨665060, by rfl⟩ : syracuseStep 886747 = 1330121) B1330121
theorem B591835 : Blo 523799 591835 := bstep (se 1 (by rfl) ⟨443876, by rfl⟩ : syracuseStep 591835 = 887753) B887753
theorem B526299 : Blo 523799 526299 := bstep (se 1 (by rfl) ⟨394724, by rfl⟩ : syracuseStep 526299 = 789449) B789449
theorem B788489 : Blo 523799 788489 := bstep (se 2 (by rfl) ⟨295683, by rfl⟩ : syracuseStep 788489 = 591367) B591367
theorem B788519 : Blo 523799 788519 := bstep (se 1 (by rfl) ⟨591389, by rfl⟩ : syracuseStep 788519 = 1182779) B1182779
theorem B526375 : Blo 523799 526375 := bstep (se 1 (by rfl) ⟨394781, by rfl⟩ : syracuseStep 526375 = 789563) B789563
theorem B2656313 : Blo 523799 2656313 := bstep (se 2 (by rfl) ⟨996117, by rfl⟩ : syracuseStep 2656313 = 1992235) B1992235
theorem B1771577 : Blo 523799 1771577 := bstep (se 2 (by rfl) ⟨664341, by rfl⟩ : syracuseStep 1771577 = 1328683) B1328683
theorem B1181753 : Blo 523799 1181753 := bstep (se 2 (by rfl) ⟨443157, by rfl⟩ : syracuseStep 1181753 = 886315) B886315
theorem B526415 : Blo 523799 526415 := bstep (se 1 (by rfl) ⟨394811, by rfl⟩ : syracuseStep 526415 = 789623) B789623
theorem B526431 : Blo 523799 526431 := bstep (se 1 (by rfl) ⟨394823, by rfl⟩ : syracuseStep 526431 = 789647) B789647
theorem B788603 : Blo 523799 788603 := bstep (se 1 (by rfl) ⟨591452, by rfl⟩ : syracuseStep 788603 = 1182905) B1182905
theorem B526459 : Blo 523799 526459 := bstep (se 1 (by rfl) ⟨394844, by rfl⟩ : syracuseStep 526459 = 789689) B789689
theorem B526511 : Blo 523799 526511 := bstep (se 1 (by rfl) ⟨394883, by rfl⟩ : syracuseStep 526511 = 789767) B789767
theorem B526535 : Blo 523799 526535 := bstep (se 1 (by rfl) ⟨394901, by rfl⟩ : syracuseStep 526535 = 789803) B789803
theorem B526555 : Blo 523799 526555 := bstep (se 1 (by rfl) ⟨394916, by rfl⟩ : syracuseStep 526555 = 789833) B789833
theorem B788729 : Blo 523799 788729 := bstep (se 2 (by rfl) ⟨295773, by rfl⟩ : syracuseStep 788729 = 591547) B591547
theorem B526631 : Blo 523799 526631 := bstep (se 1 (by rfl) ⟨394973, by rfl⟩ : syracuseStep 526631 = 789947) B789947
theorem B526671 : Blo 523799 526671 := bstep (se 1 (by rfl) ⟨395003, by rfl⟩ : syracuseStep 526671 = 790007) B790007
theorem B788831 : Blo 523799 788831 := bstep (se 1 (by rfl) ⟨591623, by rfl⟩ : syracuseStep 788831 = 1183247) B1183247
theorem B526687 : Blo 523799 526687 := bstep (se 1 (by rfl) ⟨395015, by rfl⟩ : syracuseStep 526687 = 790031) B790031
theorem B2001257 : Blo 523799 2001257 := bstep (se 2 (by rfl) ⟨750471, by rfl⟩ : syracuseStep 2001257 = 1500943) B1500943
theorem B788843 : Blo 523799 788843 := bstep (se 1 (by rfl) ⟨591632, by rfl⟩ : syracuseStep 788843 = 1183265) B1183265
theorem B526715 : Blo 523799 526715 := bstep (se 1 (by rfl) ⟨395036, by rfl⟩ : syracuseStep 526715 = 790073) B790073
theorem B1771901 : Blo 523799 1771901 := bstep (se 3 (by rfl) ⟨332231, by rfl⟩ : syracuseStep 1771901 = 664463) B664463
theorem B1182095 : Blo 523799 1182095 := bstep (se 1 (by rfl) ⟨886571, by rfl⟩ : syracuseStep 1182095 = 1773143) B1773143
theorem B592303 : Blo 523799 592303 := bstep (se 1 (by rfl) ⟨444227, by rfl⟩ : syracuseStep 592303 = 888455) B888455
theorem B526767 : Blo 523799 526767 := bstep (se 1 (by rfl) ⟨395075, by rfl⟩ : syracuseStep 526767 = 790151) B790151
theorem B526791 : Blo 523799 526791 := bstep (se 1 (by rfl) ⟨395093, by rfl⟩ : syracuseStep 526791 = 790187) B790187
theorem B526811 : Blo 523799 526811 := bstep (se 1 (by rfl) ⟨395108, by rfl⟩ : syracuseStep 526811 = 790217) B790217
theorem B4000265 : Blo 523799 4000265 := bstep (se 2 (by rfl) ⟨1500099, by rfl⟩ : syracuseStep 4000265 = 3000199) B3000199
theorem B526887 : Blo 523799 526887 := bstep (se 1 (by rfl) ⟨395165, by rfl⟩ : syracuseStep 526887 = 790331) B790331
theorem B887375 : Blo 523799 887375 := bstep (se 1 (by rfl) ⟨665531, by rfl⟩ : syracuseStep 887375 = 1331063) B1331063
theorem B789071 : Blo 523799 789071 := bstep (se 1 (by rfl) ⟨591803, by rfl⟩ : syracuseStep 789071 = 1183607) B1183607
theorem B526927 : Blo 523799 526927 := bstep (se 1 (by rfl) ⟨395195, by rfl⟩ : syracuseStep 526927 = 790391) B790391
theorem B526943 : Blo 523799 526943 := bstep (se 1 (by rfl) ⟨395207, by rfl⟩ : syracuseStep 526943 = 790415) B790415
theorem B526971 : Blo 523799 526971 := bstep (se 1 (by rfl) ⟨395228, by rfl⟩ : syracuseStep 526971 = 790457) B790457
theorem B1772171 : Blo 523799 1772171 := bstep (se 1 (by rfl) ⟨1329128, by rfl⟩ : syracuseStep 1772171 = 2658257) B2658257
theorem B527023 : Blo 523799 527023 := bstep (se 1 (by rfl) ⟨395267, by rfl⟩ : syracuseStep 527023 = 790535) B790535
theorem B789191 : Blo 523799 789191 := bstep (se 1 (by rfl) ⟨591893, by rfl⟩ : syracuseStep 789191 = 1183787) B1183787
theorem B527047 : Blo 523799 527047 := bstep (se 1 (by rfl) ⟨395285, by rfl⟩ : syracuseStep 527047 = 790571) B790571
theorem B1182419 : Blo 523799 1182419 := bstep (se 1 (by rfl) ⟨886814, by rfl⟩ : syracuseStep 1182419 = 1773629) B1773629
theorem B527067 : Blo 523799 527067 := bstep (se 1 (by rfl) ⟨395300, by rfl⟩ : syracuseStep 527067 = 790601) B790601
theorem B527143 : Blo 523799 527143 := bstep (se 1 (by rfl) ⟨395357, by rfl⟩ : syracuseStep 527143 = 790715) B790715
theorem B527183 : Blo 523799 527183 := bstep (se 1 (by rfl) ⟨395387, by rfl⟩ : syracuseStep 527183 = 790775) B790775
theorem B592735 : Blo 523799 592735 := bstep (se 1 (by rfl) ⟨444551, by rfl⟩ : syracuseStep 592735 = 889103) B889103
theorem B527199 : Blo 523799 527199 := bstep (se 1 (by rfl) ⟨395399, by rfl⟩ : syracuseStep 527199 = 790799) B790799
theorem B789353 : Blo 523799 789353 := bstep (se 2 (by rfl) ⟨296007, by rfl⟩ : syracuseStep 789353 = 592015) B592015
theorem B2001773 : Blo 523799 2001773 := bstep (se 3 (by rfl) ⟨375332, by rfl⟩ : syracuseStep 2001773 = 750665) B750665
theorem B527227 : Blo 523799 527227 := bstep (se 1 (by rfl) ⟨395420, by rfl⟩ : syracuseStep 527227 = 790841) B790841
theorem B3378095 : Blo 523799 3378095 := bstep (se 1 (by rfl) ⟨2533571, by rfl⟩ : syracuseStep 3378095 = 5067143) B5067143
theorem B527279 : Blo 523799 527279 := bstep (se 1 (by rfl) ⟨395459, by rfl⟩ : syracuseStep 527279 = 790919) B790919
theorem B789431 : Blo 523799 789431 := bstep (se 1 (by rfl) ⟨592073, by rfl⟩ : syracuseStep 789431 = 1184147) B1184147
theorem B527303 : Blo 523799 527303 := bstep (se 1 (by rfl) ⟨395477, by rfl⟩ : syracuseStep 527303 = 790955) B790955
theorem B789467 : Blo 523799 789467 := bstep (se 1 (by rfl) ⟨592100, by rfl⟩ : syracuseStep 789467 = 1184201) B1184201
theorem B527323 : Blo 523799 527323 := bstep (se 1 (by rfl) ⟨395492, by rfl⟩ : syracuseStep 527323 = 790985) B790985
theorem B527399 : Blo 523799 527399 := bstep (se 1 (by rfl) ⟨395549, by rfl⟩ : syracuseStep 527399 = 791099) B791099
theorem B527439 : Blo 523799 527439 := bstep (se 1 (by rfl) ⟨395579, by rfl⟩ : syracuseStep 527439 = 791159) B791159
theorem B527455 : Blo 523799 527455 := bstep (se 1 (by rfl) ⟨395591, by rfl⟩ : syracuseStep 527455 = 791183) B791183
theorem B527483 : Blo 523799 527483 := bstep (se 1 (by rfl) ⟨395612, by rfl⟩ : syracuseStep 527483 = 791225) B791225
theorem B527535 : Blo 523799 527535 := bstep (se 1 (by rfl) ⟨395651, by rfl⟩ : syracuseStep 527535 = 791303) B791303
theorem B593095 : Blo 523799 593095 := bstep (se 1 (by rfl) ⟨444821, by rfl⟩ : syracuseStep 593095 = 889643) B889643
theorem B527559 : Blo 523799 527559 := bstep (se 1 (by rfl) ⟨395669, by rfl⟩ : syracuseStep 527559 = 791339) B791339
theorem B527579 : Blo 523799 527579 := bstep (se 1 (by rfl) ⟨395684, by rfl⟩ : syracuseStep 527579 = 791369) B791369
theorem B527655 : Blo 523799 527655 := bstep (se 1 (by rfl) ⟨395741, by rfl⟩ : syracuseStep 527655 = 791483) B791483
theorem B527695 : Blo 523799 527695 := bstep (se 1 (by rfl) ⟨395771, by rfl⟩ : syracuseStep 527695 = 791543) B791543
theorem B527711 : Blo 523799 527711 := bstep (se 1 (by rfl) ⟨395783, by rfl⟩ : syracuseStep 527711 = 791567) B791567
theorem B527739 : Blo 523799 527739 := bstep (se 1 (by rfl) ⟨395804, by rfl⟩ : syracuseStep 527739 = 791609) B791609
theorem B888239 : Blo 523799 888239 := bstep (se 1 (by rfl) ⟨666179, by rfl⟩ : syracuseStep 888239 = 1332359) B1332359
theorem B789935 : Blo 523799 789935 := bstep (se 1 (by rfl) ⟨592451, by rfl⟩ : syracuseStep 789935 = 1184903) B1184903
theorem B527791 : Blo 523799 527791 := bstep (se 1 (by rfl) ⟨395843, by rfl⟩ : syracuseStep 527791 = 791687) B791687
theorem B790025 : Blo 523799 790025 := bstep (se 2 (by rfl) ⟨296259, by rfl⟩ : syracuseStep 790025 = 592519) B592519
theorem B2002441 : Blo 523799 2002441 := bstep (se 2 (by rfl) ⟨750915, by rfl⟩ : syracuseStep 2002441 = 1501831) B1501831
theorem B1773089 : Blo 523799 1773089 := bstep (se 2 (by rfl) ⟨664908, by rfl⟩ : syracuseStep 1773089 = 1329817) B1329817
theorem B790055 : Blo 523799 790055 := bstep (se 1 (by rfl) ⟨592541, by rfl⟩ : syracuseStep 790055 = 1185083) B1185083
theorem B1183355 : Blo 523799 1183355 := bstep (se 1 (by rfl) ⟨887516, by rfl⟩ : syracuseStep 1183355 = 1775033) B1775033
theorem B790139 : Blo 523799 790139 := bstep (se 1 (by rfl) ⟨592604, by rfl⟩ : syracuseStep 790139 = 1185209) B1185209
theorem B3247739 : Blo 523799 3247739 := bstep (se 1 (by rfl) ⟨2435804, by rfl⟩ : syracuseStep 3247739 = 4871609) B4871609
theorem B2985619 : Blo 523799 2985619 := bstep (se 1 (by rfl) ⟨2239214, by rfl⟩ : syracuseStep 2985619 = 4478429) B4478429
theorem B2133715 : Blo 523799 2133715 := bstep (se 1 (by rfl) ⟨1600286, by rfl⟩ : syracuseStep 2133715 = 3200573) B3200573
theorem B1773305 : Blo 523799 1773305 := bstep (se 2 (by rfl) ⟨664989, by rfl⟩ : syracuseStep 1773305 = 1329979) B1329979
theorem B1183481 : Blo 523799 1183481 := bstep (se 2 (by rfl) ⟨443805, by rfl⟩ : syracuseStep 1183481 = 887611) B887611
theorem B790265 : Blo 523799 790265 := bstep (se 2 (by rfl) ⟨296349, by rfl⟩ : syracuseStep 790265 = 592699) B592699
theorem B888671 : Blo 523799 888671 := bstep (se 1 (by rfl) ⟨666503, by rfl⟩ : syracuseStep 888671 = 1333007) B1333007
theorem B790367 : Blo 523799 790367 := bstep (se 1 (by rfl) ⟨592775, by rfl⟩ : syracuseStep 790367 = 1185551) B1185551
theorem B790379 : Blo 523799 790379 := bstep (se 1 (by rfl) ⟨592784, by rfl⟩ : syracuseStep 790379 = 1185569) B1185569
theorem B4493191 : Blo 523799 4493191 := bstep (se 1 (by rfl) ⟨3369893, by rfl⟩ : syracuseStep 4493191 = 6739787) B6739787
theorem B1347511 : Blo 523799 1347511 := bstep (se 1 (by rfl) ⟨1010633, by rfl⟩ : syracuseStep 1347511 = 2021267) B2021267
theorem B4001723 : Blo 523799 4001723 := bstep (se 1 (by rfl) ⟨3001292, by rfl⟩ : syracuseStep 4001723 = 6002585) B6002585
theorem B6721541 : Blo 523799 6721541 := bstep (se 4 (by rfl) ⟨630144, by rfl⟩ : syracuseStep 6721541 = 1260289) B1260289
theorem B1773575 : Blo 523799 1773575 := bstep (se 1 (by rfl) ⟨1330181, by rfl⟩ : syracuseStep 1773575 = 2660363) B2660363
theorem B1183751 : Blo 523799 1183751 := bstep (se 1 (by rfl) ⟨887813, by rfl⟩ : syracuseStep 1183751 = 1775627) B1775627
theorem B1183823 : Blo 523799 1183823 := bstep (se 1 (by rfl) ⟨887867, by rfl⟩ : syracuseStep 1183823 = 1775735) B1775735
theorem B790607 : Blo 523799 790607 := bstep (se 1 (by rfl) ⟨592955, by rfl⟩ : syracuseStep 790607 = 1185911) B1185911
theorem B2658419 : Blo 523799 2658419 := bstep (se 1 (by rfl) ⟨1993814, by rfl⟩ : syracuseStep 2658419 = 3987629) B3987629
theorem B1773683 : Blo 523799 1773683 := bstep (se 1 (by rfl) ⟨1330262, by rfl⟩ : syracuseStep 1773683 = 2660525) B2660525
theorem B790727 : Blo 523799 790727 := bstep (se 1 (by rfl) ⟨593045, by rfl⟩ : syracuseStep 790727 = 1186091) B1186091
theorem B790889 : Blo 523799 790889 := bstep (se 2 (by rfl) ⟨296583, by rfl⟩ : syracuseStep 790889 = 593167) B593167
theorem B1773953 : Blo 523799 1773953 := bstep (se 2 (by rfl) ⟨665232, by rfl⟩ : syracuseStep 1773953 = 1330465) B1330465
theorem B889231 : Blo 523799 889231 := bstep (se 1 (by rfl) ⟨666923, by rfl⟩ : syracuseStep 889231 = 1333847) B1333847
theorem B790967 : Blo 523799 790967 := bstep (se 1 (by rfl) ⟨593225, by rfl⟩ : syracuseStep 790967 = 1186451) B1186451
theorem B1184219 : Blo 523799 1184219 := bstep (se 1 (by rfl) ⟨888164, by rfl⟩ : syracuseStep 1184219 = 1776329) B1776329
theorem B791003 : Blo 523799 791003 := bstep (se 1 (by rfl) ⟨593252, by rfl⟩ : syracuseStep 791003 = 1186505) B1186505
theorem B3379735 : Blo 523799 3379735 := bstep (se 1 (by rfl) ⟨2534801, by rfl⟩ : syracuseStep 3379735 = 5069603) B5069603
theorem B2691719 : Blo 523799 2691719 := bstep (se 1 (by rfl) ⟨2018789, by rfl⟩ : syracuseStep 2691719 = 4037579) B4037579
theorem B2134717 : Blo 523799 2134717 := bstep (se 3 (by rfl) ⟨400259, by rfl⟩ : syracuseStep 2134717 = 800519) B800519
theorem B561863 : Blo 523799 561863 := bstep (se 1 (by rfl) ⟨421397, by rfl⟩ : syracuseStep 561863 = 842795) B842795
theorem B2724637 : Blo 523799 2724637 := bstep (se 3 (by rfl) ⟨510869, by rfl⟩ : syracuseStep 2724637 = 1021739) B1021739
theorem B1184687 : Blo 523799 1184687 := bstep (se 1 (by rfl) ⟨888515, by rfl⟩ : syracuseStep 1184687 = 1777031) B1777031
theorem B791471 : Blo 523799 791471 := bstep (se 1 (by rfl) ⟨593603, by rfl⟩ : syracuseStep 791471 = 1187207) B1187207
theorem B2003899 : Blo 523799 2003899 := bstep (se 1 (by rfl) ⟨1502924, by rfl⟩ : syracuseStep 2003899 = 3005849) B3005849
theorem B791561 : Blo 523799 791561 := bstep (se 2 (by rfl) ⟨296835, by rfl⟩ : syracuseStep 791561 = 593671) B593671
theorem B791591 : Blo 523799 791591 := bstep (se 1 (by rfl) ⟨593693, by rfl⟩ : syracuseStep 791591 = 1187387) B1187387
theorem B889913 : Blo 523799 889913 := bstep (se 2 (by rfl) ⟨333717, by rfl⟩ : syracuseStep 889913 = 667435) B667435
theorem B791675 : Blo 523799 791675 := bstep (se 1 (by rfl) ⟨593756, by rfl⟩ : syracuseStep 791675 = 1187513) B1187513
theorem B1774763 : Blo 523799 1774763 := bstep (se 1 (by rfl) ⟨1331072, by rfl⟩ : syracuseStep 1774763 = 2662145) B2662145
theorem B1184939 : Blo 523799 1184939 := bstep (se 1 (by rfl) ⟨888704, by rfl⟩ : syracuseStep 1184939 = 1777409) B1777409
theorem B7607753 : Blo 523799 7607753 := bstep (se 2 (by rfl) ⟨2852907, by rfl⟩ : syracuseStep 7607753 = 5705815) B5705815
theorem B988751 : Blo 523799 988751 := bstep (se 1 (by rfl) ⟨741563, by rfl⟩ : syracuseStep 988751 = 1483127) B1483127
theorem B2660039 : Blo 523799 2660039 := bstep (se 1 (by rfl) ⟨1995029, by rfl⟩ : syracuseStep 2660039 = 3990059) B3990059
theorem B1775303 : Blo 523799 1775303 := bstep (se 1 (by rfl) ⟨1331477, by rfl⟩ : syracuseStep 1775303 = 2662955) B2662955
theorem B1185479 : Blo 523799 1185479 := bstep (se 1 (by rfl) ⟨889109, by rfl⟩ : syracuseStep 1185479 = 1778219) B1778219
theorem B890615 : Blo 523799 890615 := bstep (se 1 (by rfl) ⟨667961, by rfl⟩ : syracuseStep 890615 = 1335923) B1335923
theorem B3840257 : Blo 523799 3840257 := bstep (se 2 (by rfl) ⟨1440096, by rfl⟩ : syracuseStep 3840257 = 2880193) B2880193
theorem B1776167 : Blo 523799 1776167 := bstep (se 1 (by rfl) ⟨1332125, by rfl⟩ : syracuseStep 1776167 = 2664251) B2664251
theorem B1186343 : Blo 523799 1186343 := bstep (se 1 (by rfl) ⟨889757, by rfl⟩ : syracuseStep 1186343 = 1779515) B1779515
theorem B1776275 : Blo 523799 1776275 := bstep (se 1 (by rfl) ⟨1332206, by rfl⟩ : syracuseStep 1776275 = 2664413) B2664413
theorem B2005651 : Blo 523799 2005651 := bstep (se 1 (by rfl) ⟨1504238, by rfl⟩ : syracuseStep 2005651 = 3008477) B3008477
theorem B1776491 : Blo 523799 1776491 := bstep (se 1 (by rfl) ⟨1332368, by rfl⟩ : syracuseStep 1776491 = 2664737) B2664737
theorem B1186667 : Blo 523799 1186667 := bstep (se 1 (by rfl) ⟨890000, by rfl⟩ : syracuseStep 1186667 = 1780001) B1780001
theorem B1776545 : Blo 523799 1776545 := bstep (se 2 (by rfl) ⟨666204, by rfl⟩ : syracuseStep 1776545 = 1332409) B1332409
theorem B1186721 : Blo 523799 1186721 := bstep (se 2 (by rfl) ⟨445020, by rfl⟩ : syracuseStep 1186721 = 890041) B890041
theorem B1187063 : Blo 523799 1187063 := bstep (se 1 (by rfl) ⟨890297, by rfl⟩ : syracuseStep 1187063 = 1780595) B1780595
theorem B3841453 : Blo 523799 3841453 := bstep (se 3 (by rfl) ⟨720272, by rfl⟩ : syracuseStep 3841453 = 1440545) B1440545
theorem B1777139 : Blo 523799 1777139 := bstep (se 1 (by rfl) ⟨1332854, by rfl⟩ : syracuseStep 1777139 = 2665709) B2665709
theorem B5054075 : Blo 523799 5054075 := bstep (se 1 (by rfl) ⟨3790556, by rfl⟩ : syracuseStep 5054075 = 7581113) B7581113
theorem B1417135 : Blo 523799 1417135 := bstep (se 1 (by rfl) ⟨1062851, by rfl⟩ : syracuseStep 1417135 = 2125703) B2125703
theorem B1777679 : Blo 523799 1777679 := bstep (se 1 (by rfl) ⟨1333259, by rfl⟩ : syracuseStep 1777679 = 2666519) B2666519
theorem B1417601 : Blo 523799 1417601 := bstep (se 2 (by rfl) ⟨531600, by rfl⟩ : syracuseStep 1417601 = 1063201) B1063201
theorem B1778273 : Blo 523799 1778273 := bstep (se 2 (by rfl) ⟨666852, by rfl⟩ : syracuseStep 1778273 = 1333705) B1333705
theorem B5055149 : Blo 523799 5055149 := bstep (se 3 (by rfl) ⟨947840, by rfl⟩ : syracuseStep 5055149 = 1895681) B1895681
theorem B7709357 : Blo 523799 7709357 := bstep (se 3 (by rfl) ⟨1445504, by rfl⟩ : syracuseStep 7709357 = 2891009) B2891009
theorem B1123247 : Blo 523799 1123247 := bstep (se 1 (by rfl) ⟨842435, by rfl⟩ : syracuseStep 1123247 = 1684871) B1684871
theorem B4268983 : Blo 523799 4268983 := bstep (se 1 (by rfl) ⟨3201737, by rfl⟩ : syracuseStep 4268983 = 6403475) B6403475
theorem B19243979 : Blo 523799 19243979 := bstep (se 1 (by rfl) ⟨14432984, by rfl⟩ : syracuseStep 19243979 = 28865969) B28865969
theorem B664615 : Blo 523799 664615 := bstep (se 1 (by rfl) ⟨498461, by rfl⟩ : syracuseStep 664615 = 996923) B996923
theorem B664939 : Blo 523799 664939 := bstep (se 1 (by rfl) ⟨498704, by rfl⟩ : syracuseStep 664939 = 997409) B997409
theorem B6759881 : Blo 523799 6759881 := bstep (se 2 (by rfl) ⟨2534955, by rfl⟩ : syracuseStep 6759881 = 5069911) B5069911
theorem B665167 : Blo 523799 665167 := bstep (se 1 (by rfl) ⟨498875, by rfl⟩ : syracuseStep 665167 = 997751) B997751
theorem B960247 : Blo 523799 960247 := bstep (se 1 (by rfl) ⟨720185, by rfl⟩ : syracuseStep 960247 = 1440371) B1440371
theorem B1681181 : Blo 523799 1681181 := bstep (se 3 (by rfl) ⟨315221, by rfl⟩ : syracuseStep 1681181 = 630443) B630443
theorem B1779731 : Blo 523799 1779731 := bstep (se 1 (by rfl) ⟨1334798, by rfl⟩ : syracuseStep 1779731 = 2669597) B2669597
theorem B2533457 : Blo 523799 2533457 := bstep (se 2 (by rfl) ⟨950046, by rfl⟩ : syracuseStep 2533457 = 1900093) B1900093
theorem B6138013 : Blo 523799 6138013 := bstep (se 3 (by rfl) ⟨1150877, by rfl⟩ : syracuseStep 6138013 = 2301755) B2301755
theorem B1780055 : Blo 523799 1780055 := bstep (se 1 (by rfl) ⟨1335041, by rfl⟩ : syracuseStep 1780055 = 2670083) B2670083
theorem B1681769 : Blo 523799 1681769 := bstep (se 2 (by rfl) ⟨630663, by rfl⟩ : syracuseStep 1681769 = 1261327) B1261327
theorem B4336075 : Blo 523799 4336075 := bstep (se 1 (by rfl) ⟨3252056, by rfl⟩ : syracuseStep 4336075 = 6504113) B6504113
theorem B6760907 : Blo 523799 6760907 := bstep (se 1 (by rfl) ⟨5070680, by rfl⟩ : syracuseStep 6760907 = 10141361) B10141361
theorem B666235 : Blo 523799 666235 := bstep (se 1 (by rfl) ⟨499676, by rfl⟩ : syracuseStep 666235 = 999353) B999353
theorem B4270801 : Blo 523799 4270801 := bstep (se 2 (by rfl) ⟨1601550, by rfl⟩ : syracuseStep 4270801 = 3203101) B3203101
theorem B666463 : Blo 523799 666463 := bstep (se 1 (by rfl) ⟨499847, by rfl⟩ : syracuseStep 666463 = 999695) B999695
theorem B2665871 : Blo 523799 2665871 := bstep (se 1 (by rfl) ⟨1999403, by rfl⟩ : syracuseStep 2665871 = 3998807) B3998807
theorem B1781135 : Blo 523799 1781135 := bstep (se 1 (by rfl) ⟨1335851, by rfl⟩ : syracuseStep 1781135 = 2671703) B2671703
theorem B667055 : Blo 523799 667055 := bstep (se 1 (by rfl) ⟨500291, by rfl⟩ : syracuseStep 667055 = 1000583) B1000583
theorem B994835 : Blo 523799 994835 := bstep (se 1 (by rfl) ⟨746126, by rfl⟩ : syracuseStep 994835 = 1492253) B1492253
theorem B1945223 : Blo 523799 1945223 := bstep (se 1 (by rfl) ⟨1458917, by rfl⟩ : syracuseStep 1945223 = 2917835) B2917835
theorem B1683193 : Blo 523799 1683193 := bstep (se 2 (by rfl) ⟨631197, by rfl⟩ : syracuseStep 1683193 = 1262395) B1262395
theorem B1421243 : Blo 523799 1421243 := bstep (se 1 (by rfl) ⟨1065932, by rfl⟩ : syracuseStep 1421243 = 2131865) B2131865
theorem B896987 : Blo 523799 896987 := bstep (se 1 (by rfl) ⟨672740, by rfl⟩ : syracuseStep 896987 = 1345481) B1345481
theorem B2240855 : Blo 523799 2240855 := bstep (se 1 (by rfl) ⟨1680641, by rfl⟩ : syracuseStep 2240855 = 3361283) B3361283
theorem B996239 : Blo 523799 996239 := bstep (se 1 (by rfl) ⟨747179, by rfl⟩ : syracuseStep 996239 = 1494359) B1494359
theorem B1684385 : Blo 523799 1684385 := bstep (se 2 (by rfl) ⟨631644, by rfl⟩ : syracuseStep 1684385 = 1263289) B1263289
theorem B6009875 : Blo 523799 6009875 := bstep (se 1 (by rfl) ⟨4507406, by rfl⟩ : syracuseStep 6009875 = 9014813) B9014813
theorem B996391 : Blo 523799 996391 := bstep (se 1 (by rfl) ⟨747293, by rfl⟩ : syracuseStep 996391 = 1494587) B1494587
theorem B996475 : Blo 523799 996475 := bstep (se 1 (by rfl) ⟨747356, by rfl⟩ : syracuseStep 996475 = 1494713) B1494713
theorem B2471293 : Blo 523799 2471293 := bstep (se 3 (by rfl) ⟨463367, by rfl⟩ : syracuseStep 2471293 = 926735) B926735
theorem B2667977 : Blo 523799 2667977 := bstep (se 2 (by rfl) ⟨1000491, by rfl⟩ : syracuseStep 2667977 = 2000983) B2000983
theorem B996961 : Blo 523799 996961 := bstep (se 2 (by rfl) ⟨373860, by rfl⟩ : syracuseStep 996961 = 747721) B747721
theorem B5977799 : Blo 523799 5977799 := bstep (se 1 (by rfl) ⟨4483349, by rfl⟩ : syracuseStep 5977799 = 8966699) B8966699
theorem B1619975 : Blo 523799 1619975 := bstep (se 1 (by rfl) ⟨1214981, by rfl⟩ : syracuseStep 1619975 = 2429963) B2429963
theorem B3782713 : Blo 523799 3782713 := bstep (se 2 (by rfl) ⟨1418517, by rfl⟩ : syracuseStep 3782713 = 2837035) B2837035
theorem B2668625 : Blo 523799 2668625 := bstep (se 2 (by rfl) ⟨1000734, by rfl⟩ : syracuseStep 2668625 = 2001469) B2001469
theorem B3193175 : Blo 523799 3193175 := bstep (se 1 (by rfl) ⟨2394881, by rfl⟩ : syracuseStep 3193175 = 4789763) B4789763
theorem B997895 : Blo 523799 997895 := bstep (se 1 (by rfl) ⟨748421, by rfl⟩ : syracuseStep 997895 = 1496843) B1496843
theorem B9616157 : Blo 523799 9616157 := bstep (se 3 (by rfl) ⟨1803029, by rfl⟩ : syracuseStep 9616157 = 3606059) B3606059
theorem B998419 : Blo 523799 998419 := bstep (se 1 (by rfl) ⟨748814, by rfl⟩ : syracuseStep 998419 = 1497629) B1497629
theorem B3980339 : Blo 523799 3980339 := bstep (se 1 (by rfl) ⟨2985254, by rfl⟩ : syracuseStep 3980339 = 5970509) B5970509
theorem B2276599 : Blo 523799 2276599 := bstep (se 1 (by rfl) ⟨1707449, by rfl⟩ : syracuseStep 2276599 = 3414899) B3414899
theorem B1686845 : Blo 523799 1686845 := bstep (se 3 (by rfl) ⟨316283, by rfl⟩ : syracuseStep 1686845 = 632567) B632567
theorem B2243983 : Blo 523799 2243983 := bstep (se 1 (by rfl) ⟨1682987, by rfl⟩ : syracuseStep 2243983 = 3365975) B3365975
theorem B605659 : Blo 523799 605659 := bstep (se 1 (by rfl) ⟨454244, by rfl⟩ : syracuseStep 605659 = 908489) B908489
theorem B1326689 : Blo 523799 1326689 := bstep (se 2 (by rfl) ⟨497508, by rfl⟩ : syracuseStep 1326689 = 995017) B995017
theorem B638587 : Blo 523799 638587 := bstep (se 1 (by rfl) ⟨478940, by rfl⟩ : syracuseStep 638587 = 957881) B957881
theorem B9585211 : Blo 523799 9585211 := bstep (se 1 (by rfl) ⟨7188908, by rfl⟩ : syracuseStep 9585211 = 14377817) B14377817
theorem B1491671 : Blo 523799 1491671 := bstep (se 1 (by rfl) ⟨1118753, by rfl⟩ : syracuseStep 1491671 = 2237507) B2237507
theorem B1426249 : Blo 523799 1426249 := bstep (se 2 (by rfl) ⟨534843, by rfl⟩ : syracuseStep 1426249 = 1069687) B1069687
theorem B10961771 : Blo 523799 10961771 := bstep (se 1 (by rfl) ⟨8221328, by rfl⟩ : syracuseStep 10961771 = 16442657) B16442657
theorem B1328147 : Blo 523799 1328147 := bstep (se 1 (by rfl) ⟨996110, by rfl⟩ : syracuseStep 1328147 = 1992221) B1992221
theorem B1688843 : Blo 523799 1688843 := bstep (se 1 (by rfl) ⟨1266632, by rfl⟩ : syracuseStep 1688843 = 2533265) B2533265
theorem B1000811 : Blo 523799 1000811 := bstep (se 1 (by rfl) ⟨750608, by rfl⟩ : syracuseStep 1000811 = 1501217) B1501217
theorem B1198007 : Blo 523799 1198007 := bstep (se 1 (by rfl) ⟨898505, by rfl⟩ : syracuseStep 1198007 = 1797011) B1797011
theorem B1001479 : Blo 523799 1001479 := bstep (se 1 (by rfl) ⟨751109, by rfl⟩ : syracuseStep 1001479 = 1502219) B1502219
theorem B2247041 : Blo 523799 2247041 := bstep (se 2 (by rfl) ⟨842640, by rfl⟩ : syracuseStep 2247041 = 1685281) B1685281
theorem B1068041 : Blo 523799 1068041 := bstep (se 2 (by rfl) ⟨400515, by rfl⟩ : syracuseStep 1068041 = 801031) B801031
theorem B707935 : Blo 523799 707935 := bstep (se 1 (by rfl) ⟨530951, by rfl⟩ : syracuseStep 707935 = 1061903) B1061903
theorem B5983631 : Blo 523799 5983631 := bstep (se 1 (by rfl) ⟨4487723, by rfl⟩ : syracuseStep 5983631 = 8975447) B8975447
theorem B13684301 : Blo 523799 13684301 := bstep (se 3 (by rfl) ⟨2565806, by rfl⟩ : syracuseStep 13684301 = 5131613) B5131613
theorem B3591803 : Blo 523799 3591803 := bstep (se 1 (by rfl) ⟨2693852, by rfl⟩ : syracuseStep 3591803 = 5387705) B5387705
theorem B2870923 : Blo 523799 2870923 := bstep (se 1 (by rfl) ⟨2153192, by rfl⟩ : syracuseStep 2870923 = 4306385) B4306385
theorem B8081117 : Blo 523799 8081117 := bstep (se 3 (by rfl) ⟨1515209, by rfl⟩ : syracuseStep 8081117 = 3030419) B3030419
theorem B4476653 : Blo 523799 4476653 := bstep (se 3 (by rfl) ⟨839372, by rfl⟩ : syracuseStep 4476653 = 1678745) B1678745
theorem B3592045 : Blo 523799 3592045 := bstep (se 3 (by rfl) ⟨673508, by rfl⟩ : syracuseStep 3592045 = 1347017) B1347017
theorem B5689207 : Blo 523799 5689207 := bstep (se 1 (by rfl) ⟨4266905, by rfl⟩ : syracuseStep 5689207 = 8533811) B8533811
theorem B1036327 : Blo 523799 1036327 := bstep (se 1 (by rfl) ⟨777245, by rfl⟩ : syracuseStep 1036327 = 1554491) B1554491
theorem B839803 : Blo 523799 839803 := bstep (se 1 (by rfl) ⟨629852, by rfl⟩ : syracuseStep 839803 = 1259705) B1259705
theorem B1331599 : Blo 523799 1331599 := bstep (se 1 (by rfl) ⟨998699, by rfl⟩ : syracuseStep 1331599 = 1997399) B1997399
theorem B1331923 : Blo 523799 1331923 := bstep (se 1 (by rfl) ⟨998942, by rfl⟩ : syracuseStep 1331923 = 1997885) B1997885
theorem B841033 : Blo 523799 841033 := bstep (se 2 (by rfl) ⟨315387, by rfl⟩ : syracuseStep 841033 = 630775) B630775
theorem B1889801 : Blo 523799 1889801 := bstep (se 2 (by rfl) ⟨708675, by rfl⟩ : syracuseStep 1889801 = 1417351) B1417351
theorem B1889831 : Blo 523799 1889831 := bstep (se 1 (by rfl) ⟨1417373, by rfl⟩ : syracuseStep 1889831 = 2834747) B2834747
theorem B841295 : Blo 523799 841295 := bstep (se 1 (by rfl) ⟨630971, by rfl⟩ : syracuseStep 841295 = 1261943) B1261943
theorem B1332875 : Blo 523799 1332875 := bstep (se 1 (by rfl) ⟨999656, by rfl⟩ : syracuseStep 1332875 = 1999313) B1999313
theorem B1824403 : Blo 523799 1824403 := bstep (se 1 (by rfl) ⟨1368302, by rfl⟩ : syracuseStep 1824403 = 2736605) B2736605
theorem B3987143 : Blo 523799 3987143 := bstep (se 1 (by rfl) ⟨2990357, by rfl⟩ : syracuseStep 3987143 = 5980715) B5980715
theorem B1595323 : Blo 523799 1595323 := bstep (se 1 (by rfl) ⟨1196492, by rfl⟩ : syracuseStep 1595323 = 2392985) B2392985
theorem B3004573 : Blo 523799 3004573 := bstep (se 3 (by rfl) ⟨563357, by rfl⟩ : syracuseStep 3004573 = 1126715) B1126715
theorem B1267883 : Blo 523799 1267883 := bstep (se 1 (by rfl) ⟨950912, by rfl⟩ : syracuseStep 1267883 = 1901825) B1901825
theorem B1989107 : Blo 523799 1989107 := bstep (se 1 (by rfl) ⟨1491830, by rfl⟩ : syracuseStep 1989107 = 2983661) B2983661
theorem B1989305 : Blo 523799 1989305 := bstep (se 2 (by rfl) ⟨745989, by rfl⟩ : syracuseStep 1989305 = 1491979) B1491979
theorem B1989319 : Blo 523799 1989319 := bstep (se 1 (by rfl) ⟨1491989, by rfl⟩ : syracuseStep 1989319 = 2983979) B2983979
theorem B1497811 : Blo 523799 1497811 := bstep (se 1 (by rfl) ⟨1123358, by rfl⟩ : syracuseStep 1497811 = 2246717) B2246717
theorem B1334009 : Blo 523799 1334009 := bstep (se 2 (by rfl) ⟨500253, by rfl⟩ : syracuseStep 1334009 = 1000507) B1000507
theorem B1334191 : Blo 523799 1334191 := bstep (se 1 (by rfl) ⟨1000643, by rfl⟩ : syracuseStep 1334191 = 2001287) B2001287
theorem B10279979 : Blo 523799 10279979 := bstep (se 1 (by rfl) ⟨7709984, by rfl⟩ : syracuseStep 10279979 = 15419969) B15419969
theorem B1334657 : Blo 523799 1334657 := bstep (se 2 (by rfl) ⟨500496, by rfl⟩ : syracuseStep 1334657 = 1000993) B1000993
theorem B16997809 : Blo 523799 16997809 := bstep (se 2 (by rfl) ⟨6374178, by rfl⟩ : syracuseStep 16997809 = 12748357) B12748357
theorem B3366461 : Blo 523799 3366461 := bstep (se 3 (by rfl) ⟨631211, by rfl⟩ : syracuseStep 3366461 = 1262423) B1262423
theorem B1990291 : Blo 523799 1990291 := bstep (se 1 (by rfl) ⟨1492718, by rfl⟩ : syracuseStep 1990291 = 2985437) B2985437
theorem B1335113 : Blo 523799 1335113 := bstep (se 2 (by rfl) ⟨500667, by rfl⟩ : syracuseStep 1335113 = 1001335) B1001335
theorem B1892279 : Blo 523799 1892279 := bstep (se 1 (by rfl) ⟨1419209, by rfl⟩ : syracuseStep 1892279 = 2838419) B2838419
theorem B2252731 : Blo 523799 2252731 := bstep (se 1 (by rfl) ⟨1689548, by rfl⟩ : syracuseStep 2252731 = 3379097) B3379097
theorem B1499143 : Blo 523799 1499143 := bstep (se 1 (by rfl) ⟨1124357, by rfl⟩ : syracuseStep 1499143 = 2248715) B2248715
theorem B843833 : Blo 523799 843833 := bstep (se 2 (by rfl) ⟨316437, by rfl⟩ : syracuseStep 843833 = 632875) B632875
theorem B3792977 : Blo 523799 3792977 := bstep (se 2 (by rfl) ⟨1422366, by rfl⟩ : syracuseStep 3792977 = 2844733) B2844733
theorem B1794163 : Blo 523799 1794163 := bstep (se 1 (by rfl) ⟨1345622, by rfl⟩ : syracuseStep 1794163 = 2691245) B2691245
theorem B1335467 : Blo 523799 1335467 := bstep (se 1 (by rfl) ⟨1001600, by rfl⟩ : syracuseStep 1335467 = 2003201) B2003201
theorem B16998731 : Blo 523799 16998731 := bstep (se 1 (by rfl) ⟨12749048, by rfl⟩ : syracuseStep 16998731 = 25498097) B25498097
theorem B12312931 : Blo 523799 12312931 := bstep (se 1 (by rfl) ⟨9234698, by rfl⟩ : syracuseStep 12312931 = 18469397) B18469397
theorem B3367433 : Blo 523799 3367433 := bstep (se 2 (by rfl) ⟨1262787, by rfl⟩ : syracuseStep 3367433 = 2525575) B2525575
theorem B6382745 : Blo 523799 6382745 := bstep (se 2 (by rfl) ⟨2393529, by rfl⟩ : syracuseStep 6382745 = 4787059) B4787059
theorem B2253977 : Blo 523799 2253977 := bstep (se 2 (by rfl) ⟨845241, by rfl⟩ : syracuseStep 2253977 = 1690483) B1690483
theorem B1992023 : Blo 523799 1992023 := bstep (se 1 (by rfl) ⟨1494017, by rfl⟩ : syracuseStep 1992023 = 2988035) B2988035
theorem B1500545 : Blo 523799 1500545 := bstep (se 2 (by rfl) ⟨562704, by rfl⟩ : syracuseStep 1500545 = 1125409) B1125409
theorem B3368459 : Blo 523799 3368459 := bstep (se 1 (by rfl) ⟨2526344, by rfl⟩ : syracuseStep 3368459 = 5052689) B5052689
theorem B1894097 : Blo 523799 1894097 := bstep (se 2 (by rfl) ⟨710286, by rfl⟩ : syracuseStep 1894097 = 1420573) B1420573
theorem B7268131 : Blo 523799 7268131 := bstep (se 1 (by rfl) ⟨5451098, by rfl⟩ : syracuseStep 7268131 = 10902197) B10902197
theorem B1501001 : Blo 523799 1501001 := bstep (se 2 (by rfl) ⟨562875, by rfl⟩ : syracuseStep 1501001 = 1125751) B1125751
theorem B1534009 : Blo 523799 1534009 := bstep (se 2 (by rfl) ⟨575253, by rfl⟩ : syracuseStep 1534009 = 1150507) B1150507
theorem B2025947 : Blo 523799 2025947 := bstep (se 1 (by rfl) ⟨1519460, by rfl⟩ : syracuseStep 2025947 = 3038921) B3038921
theorem B7662109 : Blo 523799 7662109 := bstep (se 3 (by rfl) ⟨1436645, by rfl⟩ : syracuseStep 7662109 = 2873291) B2873291
theorem B1502059 : Blo 523799 1502059 := bstep (se 1 (by rfl) ⟨1126544, by rfl⟩ : syracuseStep 1502059 = 2253089) B2253089
theorem B6810551 : Blo 523799 6810551 := bstep (se 1 (by rfl) ⟨5107913, by rfl⟩ : syracuseStep 6810551 = 10215827) B10215827
theorem B9006065 : Blo 523799 9006065 := bstep (se 2 (by rfl) ⟨3377274, by rfl⟩ : syracuseStep 9006065 = 6754549) B6754549
theorem B3992975 : Blo 523799 3992975 := bstep (se 1 (by rfl) ⟨2994731, by rfl⟩ : syracuseStep 3992975 = 5989463) B5989463
theorem B2846117 : Blo 523799 2846117 := bstep (se 4 (by rfl) ⟨266823, by rfl⟩ : syracuseStep 2846117 = 533647) B533647
theorem B749179 : Blo 523799 749179 := bstep (se 1 (by rfl) ⟨561884, by rfl⟩ : syracuseStep 749179 = 1123769) B1123769
theorem B749407 : Blo 523799 749407 := bstep (se 1 (by rfl) ⟨562055, by rfl⟩ : syracuseStep 749407 = 1124111) B1124111
theorem B5992379 : Blo 523799 5992379 := bstep (se 1 (by rfl) ⟨4494284, by rfl⟩ : syracuseStep 5992379 = 8988569) B8988569
theorem B1896605 : Blo 523799 1896605 := bstep (se 3 (by rfl) ⟨355613, by rfl⟩ : syracuseStep 1896605 = 711227) B711227
theorem B2126141 : Blo 523799 2126141 := bstep (se 3 (by rfl) ⟨398651, by rfl⟩ : syracuseStep 2126141 = 797303) B797303
theorem B1995137 : Blo 523799 1995137 := bstep (se 2 (by rfl) ⟨748176, by rfl⟩ : syracuseStep 1995137 = 1496353) B1496353
theorem B1995151 : Blo 523799 1995151 := bstep (se 1 (by rfl) ⟨1496363, by rfl⟩ : syracuseStep 1995151 = 2992727) B2992727
theorem B749999 : Blo 523799 749999 := bstep (se 1 (by rfl) ⟨562499, by rfl⟩ : syracuseStep 749999 = 1124999) B1124999
theorem B2519561 : Blo 523799 2519561 := bstep (se 2 (by rfl) ⟨944835, by rfl⟩ : syracuseStep 2519561 = 1889671) B1889671
theorem B1897283 : Blo 523799 1897283 := bstep (se 1 (by rfl) ⟨1422962, by rfl⟩ : syracuseStep 1897283 = 2845925) B2845925
theorem B947207 : Blo 523799 947207 := bstep (se 1 (by rfl) ⟨710405, by rfl⟩ : syracuseStep 947207 = 1420811) B1420811
theorem B947279 : Blo 523799 947279 := bstep (se 1 (by rfl) ⟨710459, by rfl⟩ : syracuseStep 947279 = 1420919) B1420919
theorem B1996427 : Blo 523799 1996427 := bstep (se 1 (by rfl) ⟨1497320, by rfl⟩ : syracuseStep 1996427 = 2994641) B2994641
theorem B751303 : Blo 523799 751303 := bstep (se 1 (by rfl) ⟨563477, by rfl⟩ : syracuseStep 751303 = 1126955) B1126955
theorem B2520791 : Blo 523799 2520791 := bstep (se 1 (by rfl) ⟨1890593, by rfl⟩ : syracuseStep 2520791 = 3781187) B3781187
theorem B3832343 : Blo 523799 3832343 := bstep (se 1 (by rfl) ⟨2874257, by rfl⟩ : syracuseStep 3832343 = 5748515) B5748515
theorem B1768121 : Blo 523799 1768121 := bstep (se 2 (by rfl) ⟨663045, by rfl⟩ : syracuseStep 1768121 = 1326091) B1326091
theorem B1899359 : Blo 523799 1899359 := bstep (se 1 (by rfl) ⟨1424519, by rfl⟩ : syracuseStep 1899359 = 2849039) B2849039
theorem B2653235 : Blo 523799 2653235 := bstep (se 1 (by rfl) ⟨1989926, by rfl⟩ : syracuseStep 2653235 = 3979853) B3979853
theorem B1768715 : Blo 523799 1768715 := bstep (se 1 (by rfl) ⟨1326536, by rfl⟩ : syracuseStep 1768715 = 2653073) B2653073
theorem B785759 : Blo 523799 785759 := bstep (se 1 (by rfl) ⟨589319, by rfl⟩ : syracuseStep 785759 = 1178639) B1178639
theorem B785771 : Blo 523799 785771 := bstep (se 1 (by rfl) ⟨589328, by rfl⟩ : syracuseStep 785771 = 1178657) B1178657
theorem B884155 : Blo 523799 884155 := bstep (se 1 (by rfl) ⟨663116, by rfl⟩ : syracuseStep 884155 = 1326233) B1326233
theorem B1768985 : Blo 523799 1768985 := bstep (se 2 (by rfl) ⟨663369, by rfl⟩ : syracuseStep 1768985 = 1326739) B1326739
theorem B523815 : Blo 523799 523815 := bstep (se 1 (by rfl) ⟨392861, by rfl⟩ : syracuseStep 523815 = 785723) B785723
theorem B589351 : Blo 523799 589351 := bstep (se 1 (by rfl) ⟨442013, by rfl⟩ : syracuseStep 589351 = 884027) B884027
theorem B884263 : Blo 523799 884263 := bstep (se 1 (by rfl) ⟨663197, by rfl⟩ : syracuseStep 884263 = 1326395) B1326395
theorem B523855 : Blo 523799 523855 := bstep (se 1 (by rfl) ⟨392891, by rfl⟩ : syracuseStep 523855 = 785783) B785783
theorem B785999 : Blo 523799 785999 := bstep (se 1 (by rfl) ⟨589499, by rfl⟩ : syracuseStep 785999 = 1178999) B1178999
theorem B523871 : Blo 523799 523871 := bstep (se 1 (by rfl) ⟨392903, by rfl⟩ : syracuseStep 523871 = 785807) B785807
theorem B1179233 : Blo 523799 1179233 := bstep (se 2 (by rfl) ⟨442212, by rfl⟩ : syracuseStep 1179233 = 884425) B884425
theorem B523899 : Blo 523799 523899 := bstep (se 1 (by rfl) ⟨392924, by rfl⟩ : syracuseStep 523899 = 785849) B785849
theorem B523951 : Blo 523799 523951 := bstep (se 1 (by rfl) ⟨392963, by rfl⟩ : syracuseStep 523951 = 785927) B785927
theorem B523975 : Blo 523799 523975 := bstep (se 1 (by rfl) ⟨392981, by rfl⟩ : syracuseStep 523975 = 785963) B785963
theorem B786119 : Blo 523799 786119 := bstep (se 1 (by rfl) ⟨589589, by rfl⟩ : syracuseStep 786119 = 1179179) B1179179
theorem B523995 : Blo 523799 523995 := bstep (se 1 (by rfl) ⟨392996, by rfl⟩ : syracuseStep 523995 = 785993) B785993
theorem B2129657 : Blo 523799 2129657 := bstep (se 2 (by rfl) ⟨798621, by rfl⟩ : syracuseStep 2129657 = 1597243) B1597243
theorem B524071 : Blo 523799 524071 := bstep (se 1 (by rfl) ⟨393053, by rfl⟩ : syracuseStep 524071 = 786107) B786107
theorem B524111 : Blo 523799 524111 := bstep (se 1 (by rfl) ⟨393083, by rfl⟩ : syracuseStep 524111 = 786167) B786167
theorem B524127 : Blo 523799 524127 := bstep (se 1 (by rfl) ⟨393095, by rfl⟩ : syracuseStep 524127 = 786191) B786191
theorem B786281 : Blo 523799 786281 := bstep (se 2 (by rfl) ⟨294855, by rfl⟩ : syracuseStep 786281 = 589711) B589711
theorem B884587 : Blo 523799 884587 := bstep (se 1 (by rfl) ⟨663440, by rfl⟩ : syracuseStep 884587 = 1326881) B1326881
theorem B524155 : Blo 523799 524155 := bstep (se 1 (by rfl) ⟨393116, by rfl⟩ : syracuseStep 524155 = 786233) B786233
theorem B524207 : Blo 523799 524207 := bstep (se 1 (by rfl) ⟨393155, by rfl⟩ : syracuseStep 524207 = 786311) B786311
theorem B786359 : Blo 523799 786359 := bstep (se 1 (by rfl) ⟨589769, by rfl⟩ : syracuseStep 786359 = 1179539) B1179539
theorem B1179575 : Blo 523799 1179575 := bstep (se 1 (by rfl) ⟨884681, by rfl⟩ : syracuseStep 1179575 = 1769363) B1769363
theorem B524231 : Blo 523799 524231 := bstep (se 1 (by rfl) ⟨393173, by rfl⟩ : syracuseStep 524231 = 786347) B786347
theorem B524251 : Blo 523799 524251 := bstep (se 1 (by rfl) ⟨393188, by rfl⟩ : syracuseStep 524251 = 786377) B786377
theorem B786395 : Blo 523799 786395 := bstep (se 1 (by rfl) ⟨589796, by rfl⟩ : syracuseStep 786395 = 1179593) B1179593
theorem B1998857 : Blo 523799 1998857 := bstep (se 2 (by rfl) ⟨749571, by rfl⟩ : syracuseStep 1998857 = 1499143) B1499143
theorem B5701751 : Blo 523799 5701751 := bstep (se 1 (by rfl) ⟨4276313, by rfl⟩ : syracuseStep 5701751 = 8552627) B8552627
theorem B2392217 : Blo 523799 2392217 := bstep (se 2 (by rfl) ⟨897081, by rfl⟩ : syracuseStep 2392217 = 1794163) B1794163
theorem B524575 : Blo 523799 524575 := bstep (se 1 (by rfl) ⟨393431, by rfl⟩ : syracuseStep 524575 = 786863) B786863
theorem B786779 : Blo 523799 786779 := bstep (se 1 (by rfl) ⟨590084, by rfl⟩ : syracuseStep 786779 = 1180169) B1180169
theorem B524635 : Blo 523799 524635 := bstep (se 1 (by rfl) ⟨393476, by rfl⟩ : syracuseStep 524635 = 786953) B786953
theorem B524655 : Blo 523799 524655 := bstep (se 1 (by rfl) ⟨393491, by rfl⟩ : syracuseStep 524655 = 786983) B786983
theorem B524711 : Blo 523799 524711 := bstep (se 1 (by rfl) ⟨393533, by rfl⟩ : syracuseStep 524711 = 787067) B787067
theorem B1769903 : Blo 523799 1769903 := bstep (se 1 (by rfl) ⟨1327427, by rfl⟩ : syracuseStep 1769903 = 2654855) B2654855
theorem B1180079 : Blo 523799 1180079 := bstep (se 1 (by rfl) ⟨885059, by rfl⟩ : syracuseStep 1180079 = 1770119) B1770119
theorem B1180115 : Blo 523799 1180115 := bstep (se 1 (by rfl) ⟨885086, by rfl⟩ : syracuseStep 1180115 = 1770173) B1770173
theorem B16417241 : Blo 523799 16417241 := bstep (se 2 (by rfl) ⟨6156465, by rfl⟩ : syracuseStep 16417241 = 12312931) B12312931
theorem B524795 : Blo 523799 524795 := bstep (se 1 (by rfl) ⟨393596, by rfl⟩ : syracuseStep 524795 = 787193) B787193
theorem B1180223 : Blo 523799 1180223 := bstep (se 1 (by rfl) ⟨885167, by rfl⟩ : syracuseStep 1180223 = 1770335) B1770335
theorem B787007 : Blo 523799 787007 := bstep (se 1 (by rfl) ⟨590255, by rfl⟩ : syracuseStep 787007 = 1180511) B1180511
theorem B524863 : Blo 523799 524863 := bstep (se 1 (by rfl) ⟨393647, by rfl⟩ : syracuseStep 524863 = 787295) B787295
theorem B524871 : Blo 523799 524871 := bstep (se 1 (by rfl) ⟨393653, by rfl⟩ : syracuseStep 524871 = 787307) B787307
theorem B590431 : Blo 523799 590431 := bstep (se 1 (by rfl) ⟨442823, by rfl⟩ : syracuseStep 590431 = 885647) B885647
theorem B1180331 : Blo 523799 1180331 := bstep (se 1 (by rfl) ⟨885248, by rfl⟩ : syracuseStep 1180331 = 1770497) B1770497
theorem B885431 : Blo 523799 885431 := bstep (se 1 (by rfl) ⟨664073, by rfl⟩ : syracuseStep 885431 = 1328147) B1328147
theorem B787127 : Blo 523799 787127 := bstep (se 1 (by rfl) ⟨590345, by rfl⟩ : syracuseStep 787127 = 1180691) B1180691
theorem B525023 : Blo 523799 525023 := bstep (se 1 (by rfl) ⟨393767, by rfl⟩ : syracuseStep 525023 = 787535) B787535
theorem B12780281 : Blo 523799 12780281 := bstep (se 2 (by rfl) ⟨4792605, by rfl⟩ : syracuseStep 12780281 = 9585211) B9585211
theorem B525103 : Blo 523799 525103 := bstep (se 1 (by rfl) ⟨393827, by rfl⟩ : syracuseStep 525103 = 787655) B787655
theorem B787355 : Blo 523799 787355 := bstep (se 1 (by rfl) ⟨590516, by rfl⟩ : syracuseStep 787355 = 1181033) B1181033
theorem B525211 : Blo 523799 525211 := bstep (se 1 (by rfl) ⟨393908, by rfl⟩ : syracuseStep 525211 = 787817) B787817
theorem B525263 : Blo 523799 525263 := bstep (se 1 (by rfl) ⟨393947, by rfl⟩ : syracuseStep 525263 = 787895) B787895
theorem B525287 : Blo 523799 525287 := bstep (se 1 (by rfl) ⟨393965, by rfl⟩ : syracuseStep 525287 = 787931) B787931
theorem B1901665 : Blo 523799 1901665 := bstep (se 2 (by rfl) ⟨713124, by rfl⟩ : syracuseStep 1901665 = 1426249) B1426249
theorem B1999997 : Blo 523799 1999997 := bstep (se 3 (by rfl) ⟨374999, by rfl⟩ : syracuseStep 1999997 = 749999) B749999
theorem B1180871 : Blo 523799 1180871 := bstep (se 1 (by rfl) ⟨885653, by rfl⟩ : syracuseStep 1180871 = 1771307) B1771307
theorem B3081415 : Blo 523799 3081415 := bstep (se 1 (by rfl) ⟨2311061, by rfl⟩ : syracuseStep 3081415 = 4622123) B4622123
theorem B525599 : Blo 523799 525599 := bstep (se 1 (by rfl) ⟨394199, by rfl⟩ : syracuseStep 525599 = 788399) B788399
theorem B787751 : Blo 523799 787751 := bstep (se 1 (by rfl) ⟨590813, by rfl⟩ : syracuseStep 787751 = 1181627) B1181627
theorem B5768491 : Blo 523799 5768491 := bstep (se 1 (by rfl) ⟨4326368, by rfl⟩ : syracuseStep 5768491 = 8652737) B8652737
theorem B525659 : Blo 523799 525659 := bstep (se 1 (by rfl) ⟨394244, by rfl⟩ : syracuseStep 525659 = 788489) B788489
theorem B8979821 : Blo 523799 8979821 := bstep (se 3 (by rfl) ⟨1683716, by rfl⟩ : syracuseStep 8979821 = 3367433) B3367433
theorem B525679 : Blo 523799 525679 := bstep (se 1 (by rfl) ⟨394259, by rfl⟩ : syracuseStep 525679 = 788519) B788519
theorem B1770875 : Blo 523799 1770875 := bstep (se 1 (by rfl) ⟨1328156, by rfl⟩ : syracuseStep 1770875 = 2656313) B2656313
theorem B1181051 : Blo 523799 1181051 := bstep (se 1 (by rfl) ⟨885788, by rfl⟩ : syracuseStep 1181051 = 1771577) B1771577
theorem B787835 : Blo 523799 787835 := bstep (se 1 (by rfl) ⟨590876, by rfl⟩ : syracuseStep 787835 = 1181753) B1181753
theorem B886153 : Blo 523799 886153 := bstep (se 2 (by rfl) ⟨332307, by rfl⟩ : syracuseStep 886153 = 664615) B664615
theorem B525735 : Blo 523799 525735 := bstep (se 1 (by rfl) ⟨394301, by rfl⟩ : syracuseStep 525735 = 788603) B788603
theorem B1181177 : Blo 523799 1181177 := bstep (se 2 (by rfl) ⟨442941, by rfl⟩ : syracuseStep 1181177 = 885883) B885883
theorem B787961 : Blo 523799 787961 := bstep (se 2 (by rfl) ⟨295485, by rfl⟩ : syracuseStep 787961 = 590971) B590971
theorem B525819 : Blo 523799 525819 := bstep (se 1 (by rfl) ⟨394364, by rfl⟩ : syracuseStep 525819 = 788729) B788729
theorem B525887 : Blo 523799 525887 := bstep (se 1 (by rfl) ⟨394415, by rfl⟩ : syracuseStep 525887 = 788831) B788831
theorem B525895 : Blo 523799 525895 := bstep (se 1 (by rfl) ⟨394421, by rfl⟩ : syracuseStep 525895 = 788843) B788843
theorem B1181267 : Blo 523799 1181267 := bstep (se 1 (by rfl) ⟨885950, by rfl⟩ : syracuseStep 1181267 = 1771901) B1771901
theorem B788063 : Blo 523799 788063 := bstep (se 1 (by rfl) ⟨591047, by rfl⟩ : syracuseStep 788063 = 1182095) B1182095
theorem B591583 : Blo 523799 591583 := bstep (se 1 (by rfl) ⟨443687, by rfl⟩ : syracuseStep 591583 = 887375) B887375
theorem B526047 : Blo 523799 526047 := bstep (se 1 (by rfl) ⟨394535, by rfl⟩ : syracuseStep 526047 = 789071) B789071
theorem B1181447 : Blo 523799 1181447 := bstep (se 1 (by rfl) ⟨886085, by rfl⟩ : syracuseStep 1181447 = 1772171) B1772171
theorem B526127 : Blo 523799 526127 := bstep (se 1 (by rfl) ⟨394595, by rfl⟩ : syracuseStep 526127 = 789191) B789191
theorem B788279 : Blo 523799 788279 := bstep (se 1 (by rfl) ⟨591209, by rfl⟩ : syracuseStep 788279 = 1182419) B1182419
theorem B886585 : Blo 523799 886585 := bstep (se 2 (by rfl) ⟨332469, by rfl⟩ : syracuseStep 886585 = 664939) B664939
theorem B526235 : Blo 523799 526235 := bstep (se 1 (by rfl) ⟨394676, by rfl⟩ : syracuseStep 526235 = 789353) B789353
theorem B526287 : Blo 523799 526287 := bstep (se 1 (by rfl) ⟨394715, by rfl⟩ : syracuseStep 526287 = 789431) B789431
theorem B526311 : Blo 523799 526311 := bstep (se 1 (by rfl) ⟨394733, by rfl⟩ : syracuseStep 526311 = 789467) B789467
theorem B886889 : Blo 523799 886889 := bstep (se 2 (by rfl) ⟨332583, by rfl⟩ : syracuseStep 886889 = 665167) B665167
theorem B788585 : Blo 523799 788585 := bstep (se 2 (by rfl) ⟨295719, by rfl⟩ : syracuseStep 788585 = 591439) B591439
theorem B29231389 : Blo 523799 29231389 := bstep (se 3 (by rfl) ⟨5480885, by rfl⟩ : syracuseStep 29231389 = 10961771) B10961771
theorem B592159 : Blo 523799 592159 := bstep (se 1 (by rfl) ⟨444119, by rfl⟩ : syracuseStep 592159 = 888239) B888239
theorem B526623 : Blo 523799 526623 := bstep (se 1 (by rfl) ⟨394967, by rfl⟩ : syracuseStep 526623 = 789935) B789935
theorem B1280329 : Blo 523799 1280329 := bstep (se 2 (by rfl) ⟨480123, by rfl⟩ : syracuseStep 1280329 = 960247) B960247
theorem B526683 : Blo 523799 526683 := bstep (se 1 (by rfl) ⟨395012, by rfl⟩ : syracuseStep 526683 = 790025) B790025
theorem B1182059 : Blo 523799 1182059 := bstep (se 1 (by rfl) ⟨886544, by rfl⟩ : syracuseStep 1182059 = 1773089) B1773089
theorem B526703 : Blo 523799 526703 := bstep (se 1 (by rfl) ⟨395027, by rfl⟩ : syracuseStep 526703 = 790055) B790055
theorem B2656637 : Blo 523799 2656637 := bstep (se 3 (by rfl) ⟨498119, by rfl⟩ : syracuseStep 2656637 = 996239) B996239
theorem B2394535 : Blo 523799 2394535 := bstep (se 1 (by rfl) ⟨1795901, by rfl⟩ : syracuseStep 2394535 = 3591803) B3591803
theorem B788903 : Blo 523799 788903 := bstep (se 1 (by rfl) ⟨591677, by rfl⟩ : syracuseStep 788903 = 1183355) B1183355
theorem B526759 : Blo 523799 526759 := bstep (se 1 (by rfl) ⟨395069, by rfl⟩ : syracuseStep 526759 = 790139) B790139
theorem B2165159 : Blo 523799 2165159 := bstep (se 1 (by rfl) ⟨1623869, by rfl⟩ : syracuseStep 2165159 = 3247739) B3247739
theorem B2984435 : Blo 523799 2984435 := bstep (se 1 (by rfl) ⟨2238326, by rfl⟩ : syracuseStep 2984435 = 4476653) B4476653
theorem B1182203 : Blo 523799 1182203 := bstep (se 1 (by rfl) ⟨886652, by rfl⟩ : syracuseStep 1182203 = 1773305) B1773305
theorem B788987 : Blo 523799 788987 := bstep (se 1 (by rfl) ⟨591740, by rfl⟩ : syracuseStep 788987 = 1183481) B1183481
theorem B526843 : Blo 523799 526843 := bstep (se 1 (by rfl) ⟨395132, by rfl⟩ : syracuseStep 526843 = 790265) B790265
theorem B592447 : Blo 523799 592447 := bstep (se 1 (by rfl) ⟨444335, by rfl⟩ : syracuseStep 592447 = 888671) B888671
theorem B526911 : Blo 523799 526911 := bstep (se 1 (by rfl) ⟨395183, by rfl⟩ : syracuseStep 526911 = 790367) B790367
theorem B526919 : Blo 523799 526919 := bstep (se 1 (by rfl) ⟨395189, by rfl⟩ : syracuseStep 526919 = 790379) B790379
theorem B1182329 : Blo 523799 1182329 := bstep (se 2 (by rfl) ⟨443373, by rfl⟩ : syracuseStep 1182329 = 886747) B886747
theorem B789113 : Blo 523799 789113 := bstep (se 2 (by rfl) ⟨295917, by rfl⟩ : syracuseStep 789113 = 591835) B591835
theorem B1182383 : Blo 523799 1182383 := bstep (se 1 (by rfl) ⟨886787, by rfl⟩ : syracuseStep 1182383 = 1773575) B1773575
theorem B789167 : Blo 523799 789167 := bstep (se 1 (by rfl) ⟨591875, by rfl⟩ : syracuseStep 789167 = 1183751) B1183751
theorem B789215 : Blo 523799 789215 := bstep (se 1 (by rfl) ⟨591911, by rfl⟩ : syracuseStep 789215 = 1183823) B1183823
theorem B527071 : Blo 523799 527071 := bstep (se 1 (by rfl) ⟨395303, by rfl⟩ : syracuseStep 527071 = 790607) B790607
theorem B1772279 : Blo 523799 1772279 := bstep (se 1 (by rfl) ⟨1329209, by rfl⟩ : syracuseStep 1772279 = 2658419) B2658419
theorem B1182455 : Blo 523799 1182455 := bstep (se 1 (by rfl) ⟨886841, by rfl⟩ : syracuseStep 1182455 = 1773683) B1773683
theorem B527151 : Blo 523799 527151 := bstep (se 1 (by rfl) ⟨395363, by rfl⟩ : syracuseStep 527151 = 790727) B790727
theorem B527259 : Blo 523799 527259 := bstep (se 1 (by rfl) ⟨395444, by rfl⟩ : syracuseStep 527259 = 790889) B790889
theorem B1182635 : Blo 523799 1182635 := bstep (se 1 (by rfl) ⟨886976, by rfl⟩ : syracuseStep 1182635 = 1773953) B1773953
theorem B527311 : Blo 523799 527311 := bstep (se 1 (by rfl) ⟨395483, by rfl⟩ : syracuseStep 527311 = 790967) B790967
theorem B789479 : Blo 523799 789479 := bstep (se 1 (by rfl) ⟨592109, by rfl⟩ : syracuseStep 789479 = 1184219) B1184219
theorem B527335 : Blo 523799 527335 := bstep (se 1 (by rfl) ⟨395501, by rfl⟩ : syracuseStep 527335 = 791003) B791003
theorem B789737 : Blo 523799 789737 := bstep (se 2 (by rfl) ⟨296151, by rfl⟩ : syracuseStep 789737 = 592303) B592303
theorem B789791 : Blo 523799 789791 := bstep (se 1 (by rfl) ⟨592343, by rfl⟩ : syracuseStep 789791 = 1184687) B1184687
theorem B527647 : Blo 523799 527647 := bstep (se 1 (by rfl) ⟨395735, by rfl⟩ : syracuseStep 527647 = 791471) B791471
theorem B527707 : Blo 523799 527707 := bstep (se 1 (by rfl) ⟨395780, by rfl⟩ : syracuseStep 527707 = 791561) B791561
theorem B527727 : Blo 523799 527727 := bstep (se 1 (by rfl) ⟨395795, by rfl⟩ : syracuseStep 527727 = 791591) B791591
theorem B593275 : Blo 523799 593275 := bstep (se 1 (by rfl) ⟨444956, by rfl⟩ : syracuseStep 593275 = 889913) B889913
theorem B527783 : Blo 523799 527783 := bstep (se 1 (by rfl) ⟨395837, by rfl⟩ : syracuseStep 527783 = 791675) B791675
theorem B1183175 : Blo 523799 1183175 := bstep (se 1 (by rfl) ⟨887381, by rfl⟩ : syracuseStep 1183175 = 1774763) B1774763
theorem B789959 : Blo 523799 789959 := bstep (se 1 (by rfl) ⟨592469, by rfl⟩ : syracuseStep 789959 = 1184939) B1184939
theorem B888313 : Blo 523799 888313 := bstep (se 2 (by rfl) ⟨333117, by rfl⟩ : syracuseStep 888313 = 666235) B666235
theorem B560863 : Blo 523799 560863 := bstep (se 1 (by rfl) ⟨420647, by rfl⟩ : syracuseStep 560863 = 841295) B841295
theorem B659167 : Blo 523799 659167 := bstep (se 1 (by rfl) ⟨494375, by rfl⟩ : syracuseStep 659167 = 988751) B988751
theorem B888583 : Blo 523799 888583 := bstep (se 1 (by rfl) ⟨666437, by rfl⟩ : syracuseStep 888583 = 1332875) B1332875
theorem B888617 : Blo 523799 888617 := bstep (se 2 (by rfl) ⟨333231, by rfl⟩ : syracuseStep 888617 = 666463) B666463
theorem B790313 : Blo 523799 790313 := bstep (se 2 (by rfl) ⟨296367, by rfl⟩ : syracuseStep 790313 = 592735) B592735
theorem B2658095 : Blo 523799 2658095 := bstep (se 1 (by rfl) ⟨1993571, by rfl⟩ : syracuseStep 2658095 = 3987143) B3987143
theorem B1773359 : Blo 523799 1773359 := bstep (se 1 (by rfl) ⟨1330019, by rfl⟩ : syracuseStep 1773359 = 2660039) B2660039
theorem B1183535 : Blo 523799 1183535 := bstep (se 1 (by rfl) ⟨887651, by rfl⟩ : syracuseStep 1183535 = 1775303) B1775303
theorem B790319 : Blo 523799 790319 := bstep (se 1 (by rfl) ⟨592739, by rfl⟩ : syracuseStep 790319 = 1185479) B1185479
theorem B2002745 : Blo 523799 2002745 := bstep (se 2 (by rfl) ⟨751029, by rfl⟩ : syracuseStep 2002745 = 1502059) B1502059
theorem B593743 : Blo 523799 593743 := bstep (se 1 (by rfl) ⟨445307, by rfl⟩ : syracuseStep 593743 = 890615) B890615
theorem B790793 : Blo 523799 790793 := bstep (se 2 (by rfl) ⟨296547, by rfl⟩ : syracuseStep 790793 = 593095) B593095
theorem B1184111 : Blo 523799 1184111 := bstep (se 1 (by rfl) ⟨888083, by rfl⟩ : syracuseStep 1184111 = 1776167) B1776167
theorem B790895 : Blo 523799 790895 := bstep (se 1 (by rfl) ⟨593171, by rfl⟩ : syracuseStep 790895 = 1186343) B1186343
theorem B1184183 : Blo 523799 1184183 := bstep (se 1 (by rfl) ⟨888137, by rfl⟩ : syracuseStep 1184183 = 1776275) B1776275
theorem B889339 : Blo 523799 889339 := bstep (se 1 (by rfl) ⟨667004, by rfl⟩ : syracuseStep 889339 = 1334009) B1334009
theorem B1184327 : Blo 523799 1184327 := bstep (se 1 (by rfl) ⟨888245, by rfl⟩ : syracuseStep 1184327 = 1776491) B1776491
theorem B791111 : Blo 523799 791111 := bstep (se 1 (by rfl) ⟨593333, by rfl⟩ : syracuseStep 791111 = 1186667) B1186667
theorem B1184363 : Blo 523799 1184363 := bstep (se 1 (by rfl) ⟨888272, by rfl⟩ : syracuseStep 1184363 = 1776545) B1776545
theorem B791147 : Blo 523799 791147 := bstep (se 1 (by rfl) ⟨593360, by rfl⟩ : syracuseStep 791147 = 1186721) B1186721
theorem B6853319 : Blo 523799 6853319 := bstep (se 1 (by rfl) ⟨5139989, by rfl⟩ : syracuseStep 6853319 = 10279979) B10279979
theorem B791375 : Blo 523799 791375 := bstep (se 1 (by rfl) ⟨593531, by rfl⟩ : syracuseStep 791375 = 1187063) B1187063
theorem B889771 : Blo 523799 889771 := bstep (se 1 (by rfl) ⟨667328, by rfl⟩ : syracuseStep 889771 = 1334657) B1334657
theorem B1184759 : Blo 523799 1184759 := bstep (se 1 (by rfl) ⟨888569, by rfl⟩ : syracuseStep 1184759 = 1777139) B1777139
theorem B890075 : Blo 523799 890075 := bstep (se 1 (by rfl) ⟨667556, by rfl⟩ : syracuseStep 890075 = 1335113) B1335113
theorem B1185119 : Blo 523799 1185119 := bstep (se 1 (by rfl) ⟨888839, by rfl⟩ : syracuseStep 1185119 = 1777679) B1777679
theorem B562555 : Blo 523799 562555 := bstep (se 1 (by rfl) ⟨421916, by rfl⟩ : syracuseStep 562555 = 843833) B843833
theorem B1381769 : Blo 523799 1381769 := bstep (se 2 (by rfl) ⟨518163, by rfl⟩ : syracuseStep 1381769 = 1036327) B1036327
theorem B2528651 : Blo 523799 2528651 := bstep (se 1 (by rfl) ⟨1896488, by rfl⟩ : syracuseStep 2528651 = 3792977) B3792977
theorem B890311 : Blo 523799 890311 := bstep (se 1 (by rfl) ⟨667733, by rfl⟩ : syracuseStep 890311 = 1335467) B1335467
theorem B1119737 : Blo 523799 1119737 := bstep (se 2 (by rfl) ⟨419901, by rfl⟩ : syracuseStep 1119737 = 839803) B839803
theorem B6755885 : Blo 523799 6755885 := bstep (se 3 (by rfl) ⟨1266728, by rfl⟩ : syracuseStep 6755885 = 2533457) B2533457
theorem B1185515 : Blo 523799 1185515 := bstep (se 1 (by rfl) ⟨889136, by rfl⟩ : syracuseStep 1185515 = 1778273) B1778273
theorem B2660201 : Blo 523799 2660201 := bstep (se 2 (by rfl) ⟨997575, by rfl⟩ : syracuseStep 2660201 = 1995151) B1995151
theorem B1775465 : Blo 523799 1775465 := bstep (se 2 (by rfl) ⟨665799, by rfl⟩ : syracuseStep 1775465 = 1331599) B1331599
theorem B1185641 : Blo 523799 1185641 := bstep (se 2 (by rfl) ⟨444615, by rfl⟩ : syracuseStep 1185641 = 889231) B889231
theorem B1775897 : Blo 523799 1775897 := bstep (se 2 (by rfl) ⟨665961, by rfl⟩ : syracuseStep 1775897 = 1331923) B1331923
theorem B1120787 : Blo 523799 1120787 := bstep (se 1 (by rfl) ⟨840590, by rfl⟩ : syracuseStep 1120787 = 1681181) B1681181
theorem B1186487 : Blo 523799 1186487 := bstep (se 1 (by rfl) ⟨889865, by rfl⟩ : syracuseStep 1186487 = 1779731) B1779731
theorem B1186703 : Blo 523799 1186703 := bstep (se 1 (by rfl) ⟨890027, by rfl⟩ : syracuseStep 1186703 = 1780055) B1780055
theorem B1350631 : Blo 523799 1350631 := bstep (se 1 (by rfl) ⟨1012973, by rfl⟩ : syracuseStep 1350631 = 2025947) B2025947
theorem B1121377 : Blo 523799 1121377 := bstep (se 2 (by rfl) ⟨420516, by rfl⟩ : syracuseStep 1121377 = 841033) B841033
theorem B13180229 : Blo 523799 13180229 := bstep (se 4 (by rfl) ⟨1235646, by rfl⟩ : syracuseStep 13180229 = 2471293) B2471293
theorem B6004043 : Blo 523799 6004043 := bstep (se 1 (by rfl) ⟨4503032, by rfl⟩ : syracuseStep 6004043 = 9006065) B9006065
theorem B2432537 : Blo 523799 2432537 := bstep (se 2 (by rfl) ⟨912201, by rfl⟩ : syracuseStep 2432537 = 1824403) B1824403
theorem B1777247 : Blo 523799 1777247 := bstep (se 1 (by rfl) ⟨1332935, by rfl⟩ : syracuseStep 1777247 = 2665871) B2665871
theorem B2661983 : Blo 523799 2661983 := bstep (se 1 (by rfl) ⟨1996487, by rfl⟩ : syracuseStep 2661983 = 3992975) B3992975
theorem B1187423 : Blo 523799 1187423 := bstep (se 1 (by rfl) ⟨890567, by rfl⟩ : syracuseStep 1187423 = 1781135) B1781135
theorem B663223 : Blo 523799 663223 := bstep (se 1 (by rfl) ⟨497417, by rfl⟩ : syracuseStep 663223 = 994835) B994835
theorem B597991 : Blo 523799 597991 := bstep (se 1 (by rfl) ⟨448493, by rfl⟩ : syracuseStep 597991 = 896987) B896987
theorem B4006097 : Blo 523799 4006097 := bstep (se 2 (by rfl) ⟨1502286, by rfl⟩ : syracuseStep 4006097 = 3004573) B3004573
theorem B1417427 : Blo 523799 1417427 := bstep (se 1 (by rfl) ⟨1063070, by rfl⟩ : syracuseStep 1417427 = 2126141) B2126141
theorem B1679707 : Blo 523799 1679707 := bstep (se 1 (by rfl) ⟨1259780, by rfl⟩ : syracuseStep 1679707 = 2519561) B2519561
theorem B1122923 : Blo 523799 1122923 := bstep (se 1 (by rfl) ⟨842192, by rfl⟩ : syracuseStep 1122923 = 1684385) B1684385
theorem B631471 : Blo 523799 631471 := bstep (se 1 (by rfl) ⟨473603, by rfl⟩ : syracuseStep 631471 = 947207) B947207
theorem B4006583 : Blo 523799 4006583 := bstep (se 1 (by rfl) ⟨3004937, by rfl⟩ : syracuseStep 4006583 = 6009875) B6009875
theorem B631519 : Blo 523799 631519 := bstep (se 1 (by rfl) ⟨473639, by rfl⟩ : syracuseStep 631519 = 947279) B947279
theorem B1778651 : Blo 523799 1778651 := bstep (se 1 (by rfl) ⟨1333988, by rfl⟩ : syracuseStep 1778651 = 2667977) B2667977
theorem B1778813 : Blo 523799 1778813 := bstep (se 3 (by rfl) ⟨333527, by rfl⟩ : syracuseStep 1778813 = 667055) B667055
theorem B1680527 : Blo 523799 1680527 := bstep (se 1 (by rfl) ⟨1260395, by rfl⟩ : syracuseStep 1680527 = 2520791) B2520791
theorem B1778921 : Blo 523799 1778921 := bstep (se 2 (by rfl) ⟨667095, by rfl⟩ : syracuseStep 1778921 = 1334191) B1334191
theorem B1779083 : Blo 523799 1779083 := bstep (se 1 (by rfl) ⟨1334312, by rfl⟩ : syracuseStep 1779083 = 2668625) B2668625
theorem B665263 : Blo 523799 665263 := bstep (se 1 (by rfl) ⟨498947, by rfl⟩ : syracuseStep 665263 = 997895) B997895
theorem B2991977 : Blo 523799 2991977 := bstep (se 2 (by rfl) ⟨1121991, by rfl⟩ : syracuseStep 2991977 = 2243983) B2243983
theorem B5121937 : Blo 523799 5121937 := bstep (se 2 (by rfl) ⟨1920726, by rfl⟩ : syracuseStep 5121937 = 3841453) B3841453
theorem B5679085 : Blo 523799 5679085 := bstep (se 3 (by rfl) ⟨1064828, by rfl⟩ : syracuseStep 5679085 = 2129657) B2129657
theorem B1124563 : Blo 523799 1124563 := bstep (se 1 (by rfl) ⟨843422, by rfl⟩ : syracuseStep 1124563 = 1686845) B1686845
theorem B6728669 : Blo 523799 6728669 := bstep (se 3 (by rfl) ⟨1261625, by rfl⟩ : syracuseStep 6728669 = 2523251) B2523251
theorem B994447 : Blo 523799 994447 := bstep (se 1 (by rfl) ⟨745835, by rfl⟩ : syracuseStep 994447 = 1491671) B1491671
theorem B1125895 : Blo 523799 1125895 := bstep (se 1 (by rfl) ⟨844421, by rfl⟩ : syracuseStep 1125895 = 1688843) B1688843
theorem B667207 : Blo 523799 667207 := bstep (se 1 (by rfl) ⟨500405, by rfl⟩ : syracuseStep 667207 = 1000811) B1000811
theorem B2666195 : Blo 523799 2666195 := bstep (se 1 (by rfl) ⟨1999646, by rfl⟩ : syracuseStep 2666195 = 3999293) B3999293
theorem B798671 : Blo 523799 798671 := bstep (se 1 (by rfl) ⟨599003, by rfl⟩ : syracuseStep 798671 = 1198007) B1198007
theorem B2666843 : Blo 523799 2666843 := bstep (se 1 (by rfl) ⟨2000132, by rfl⟩ : syracuseStep 2666843 = 4000265) B4000265
theorem B5059421 : Blo 523799 5059421 := bstep (se 3 (by rfl) ⟨948641, by rfl⟩ : syracuseStep 5059421 = 1897283) B1897283
theorem B9122867 : Blo 523799 9122867 := bstep (se 1 (by rfl) ⟨6842150, by rfl⟩ : syracuseStep 9122867 = 13684301) B13684301
theorem B2995325 : Blo 523799 2995325 := bstep (se 3 (by rfl) ⟨561623, by rfl⟩ : syracuseStep 2995325 = 1123247) B1123247
theorem B5387411 : Blo 523799 5387411 := bstep (se 1 (by rfl) ⟨4040558, by rfl⟩ : syracuseStep 5387411 = 8081117) B8081117
theorem B2667815 : Blo 523799 2667815 := bstep (se 1 (by rfl) ⟨2000861, by rfl⟩ : syracuseStep 2667815 = 4001723) B4001723
theorem B2045345 : Blo 523799 2045345 := bstep (se 2 (by rfl) ⟨767004, by rfl⟩ : syracuseStep 2045345 = 1534009) B1534009
theorem B11385157 : Blo 523799 11385157 := bstep (se 4 (by rfl) ⟨1067358, by rfl⟩ : syracuseStep 11385157 = 2134717) B2134717
theorem B1259867 : Blo 523799 1259867 := bstep (se 1 (by rfl) ⟨944900, by rfl⟩ : syracuseStep 1259867 = 1889801) B1889801
theorem B1259887 : Blo 523799 1259887 := bstep (se 1 (by rfl) ⟨944915, by rfl⟩ : syracuseStep 1259887 = 1889831) B1889831
theorem B1326071 : Blo 523799 1326071 := bstep (se 1 (by rfl) ⟨994553, by rfl⟩ : syracuseStep 1326071 = 1989107) B1989107
theorem B1326203 : Blo 523799 1326203 := bstep (se 1 (by rfl) ⟨994652, by rfl⟩ : syracuseStep 1326203 = 1989305) B1989305
theorem B2669921 : Blo 523799 2669921 := bstep (se 2 (by rfl) ⟨1001220, by rfl⟩ : syracuseStep 2669921 = 2002441) B2002441
theorem B998905 : Blo 523799 998905 := bstep (se 2 (by rfl) ⟨374589, by rfl⟩ : syracuseStep 998905 = 749179) B749179
theorem B3980825 : Blo 523799 3980825 := bstep (se 2 (by rfl) ⟨1492809, by rfl⟩ : syracuseStep 3980825 = 2985619) B2985619
theorem B2244257 : Blo 523799 2244257 := bstep (se 2 (by rfl) ⟨841596, by rfl⟩ : syracuseStep 2244257 = 1683193) B1683193
theorem B2244307 : Blo 523799 2244307 := bstep (se 1 (by rfl) ⟨1683230, by rfl⟩ : syracuseStep 2244307 = 3366461) B3366461
theorem B999209 : Blo 523799 999209 := bstep (se 2 (by rfl) ⟨374703, by rfl⟩ : syracuseStep 999209 = 749407) B749407
theorem B7585609 : Blo 523799 7585609 := bstep (se 2 (by rfl) ⟨2844603, by rfl⟩ : syracuseStep 7585609 = 5689207) B5689207
theorem B12829319 : Blo 523799 12829319 := bstep (se 1 (by rfl) ⟨9621989, by rfl⟩ : syracuseStep 12829319 = 19243979) B19243979
theorem B10240685 : Blo 523799 10240685 := bstep (se 3 (by rfl) ⟨1920128, by rfl⟩ : syracuseStep 10240685 = 3840257) B3840257
theorem B4506313 : Blo 523799 4506313 := bstep (se 2 (by rfl) ⟨1689867, by rfl⟩ : syracuseStep 4506313 = 3379735) B3379735
theorem B1328015 : Blo 523799 1328015 := bstep (se 1 (by rfl) ⟨996011, by rfl⟩ : syracuseStep 1328015 = 1992023) B1992023
theorem B1000363 : Blo 523799 1000363 := bstep (se 1 (by rfl) ⟨750272, by rfl⟩ : syracuseStep 1000363 = 1500545) B1500545
theorem B4506587 : Blo 523799 4506587 := bstep (se 1 (by rfl) ⟨3379940, by rfl⟩ : syracuseStep 4506587 = 6759881) B6759881
theorem B2245639 : Blo 523799 2245639 := bstep (se 1 (by rfl) ⟨1684229, by rfl⟩ : syracuseStep 2245639 = 3368459) B3368459
theorem B1262731 : Blo 523799 1262731 := bstep (se 1 (by rfl) ⟨947048, by rfl⟩ : syracuseStep 1262731 = 1894097) B1894097
theorem B1000667 : Blo 523799 1000667 := bstep (se 1 (by rfl) ⟨750500, by rfl⟩ : syracuseStep 1000667 = 1501001) B1501001
theorem B2671865 : Blo 523799 2671865 := bstep (se 2 (by rfl) ⟨1001949, by rfl⟩ : syracuseStep 2671865 = 2003899) B2003899
theorem B1328521 : Blo 523799 1328521 := bstep (se 2 (by rfl) ⟨498195, by rfl⟩ : syracuseStep 1328521 = 996391) B996391
theorem B1328633 : Blo 523799 1328633 := bstep (se 2 (by rfl) ⟨498237, by rfl⟩ : syracuseStep 1328633 = 996475) B996475
theorem B4507271 : Blo 523799 4507271 := bstep (se 1 (by rfl) ⟨3380453, by rfl⟩ : syracuseStep 4507271 = 6760907) B6760907
theorem B4540367 : Blo 523799 4540367 := bstep (se 1 (by rfl) ⟨3405275, by rfl⟩ : syracuseStep 4540367 = 6810551) B6810551
theorem B1329281 : Blo 523799 1329281 := bstep (se 2 (by rfl) ⟨498480, by rfl⟩ : syracuseStep 1329281 = 996961) B996961
theorem B746768645 : Blo 523799 746768645 := bstep (se 4 (by rfl) ⟨70009560, by rfl⟩ : syracuseStep 746768645 = 140019121) B140019121
theorem B1001737 : Blo 523799 1001737 := bstep (se 2 (by rfl) ⟨375651, by rfl⟩ : syracuseStep 1001737 = 751303) B751303
theorem B1296815 : Blo 523799 1296815 := bstep (se 1 (by rfl) ⟨972611, by rfl⟩ : syracuseStep 1296815 = 1945223) B1945223
theorem B1264403 : Blo 523799 1264403 := bstep (se 1 (by rfl) ⟨948302, by rfl⟩ : syracuseStep 1264403 = 1896605) B1896605
theorem B1493903 : Blo 523799 1493903 := bstep (se 1 (by rfl) ⟨1120427, by rfl⟩ : syracuseStep 1493903 = 2240855) B2240855
theorem B1330091 : Blo 523799 1330091 := bstep (se 1 (by rfl) ⟨997568, by rfl⟩ : syracuseStep 1330091 = 1995137) B1995137
theorem B2674201 : Blo 523799 2674201 := bstep (se 2 (by rfl) ⟨1002825, by rfl⟩ : syracuseStep 2674201 = 2005651) B2005651
theorem B1330951 : Blo 523799 1330951 := bstep (se 1 (by rfl) ⟨998213, by rfl⟩ : syracuseStep 1330951 = 1996427) B1996427
theorem B3985199 : Blo 523799 3985199 := bstep (se 1 (by rfl) ⟨2988899, by rfl⟩ : syracuseStep 3985199 = 5977799) B5977799
theorem B1331225 : Blo 523799 1331225 := bstep (se 2 (by rfl) ⟨499209, by rfl⟩ : syracuseStep 1331225 = 998419) B998419
theorem B3035465 : Blo 523799 3035465 := bstep (se 2 (by rfl) ⟨1138299, by rfl⟩ : syracuseStep 3035465 = 2276599) B2276599
theorem B6410771 : Blo 523799 6410771 := bstep (se 1 (by rfl) ⟨4808078, by rfl⟩ : syracuseStep 6410771 = 9616157) B9616157
theorem B1266239 : Blo 523799 1266239 := bstep (se 1 (by rfl) ⟨949679, by rfl⟩ : syracuseStep 1266239 = 1899359) B1899359
theorem B22663745 : Blo 523799 22663745 := bstep (se 2 (by rfl) ⟨8498904, by rfl⟩ : syracuseStep 22663745 = 16997809) B16997809
theorem B19157573 : Blo 523799 19157573 := bstep (se 4 (by rfl) ⟨1796022, by rfl⟩ : syracuseStep 19157573 = 3592045) B3592045
theorem B807545 : Blo 523799 807545 := bstep (se 2 (by rfl) ⟨302829, by rfl⟩ : syracuseStep 807545 = 605659) B605659
theorem B1889513 : Blo 523799 1889513 := bstep (se 2 (by rfl) ⟨708567, by rfl⟩ : syracuseStep 1889513 = 1417135) B1417135
theorem B3003641 : Blo 523799 3003641 := bstep (se 2 (by rfl) ⟨1126365, by rfl⟩ : syracuseStep 3003641 = 2252731) B2252731
theorem B2053993 : Blo 523799 2053993 := bstep (se 2 (by rfl) ⟨770247, by rfl⟩ : syracuseStep 2053993 = 1540495) B1540495
theorem B1333199 : Blo 523799 1333199 := bstep (se 1 (by rfl) ⟨999899, by rfl⟩ : syracuseStep 1333199 = 1999799) B1999799
theorem B5069375 : Blo 523799 5069375 := bstep (se 1 (by rfl) ⟨3802031, by rfl⟩ : syracuseStep 5069375 = 7604063) B7604063
theorem B5691977 : Blo 523799 5691977 := bstep (se 2 (by rfl) ⟨2134491, by rfl⟩ : syracuseStep 5691977 = 4268983) B4268983
theorem B1333867 : Blo 523799 1333867 := bstep (se 1 (by rfl) ⟨1000400, by rfl⟩ : syracuseStep 1333867 = 2000801) B2000801
theorem B1334171 : Blo 523799 1334171 := bstep (se 1 (by rfl) ⟨1000628, by rfl⟩ : syracuseStep 1334171 = 2001257) B2001257
theorem B1498027 : Blo 523799 1498027 := bstep (se 1 (by rfl) ⟨1123520, by rfl⟩ : syracuseStep 1498027 = 2247041) B2247041
theorem B1498301 : Blo 523799 1498301 := bstep (se 3 (by rfl) ⟨280931, by rfl⟩ : syracuseStep 1498301 = 561863) B561863
theorem B1334515 : Blo 523799 1334515 := bstep (se 1 (by rfl) ⟨1000886, by rfl⟩ : syracuseStep 1334515 = 2001773) B2001773
theorem B2252063 : Blo 523799 2252063 := bstep (se 1 (by rfl) ⟨1689047, by rfl⟩ : syracuseStep 2252063 = 3378095) B3378095
theorem B712027 : Blo 523799 712027 := bstep (se 1 (by rfl) ⟨534020, by rfl⟩ : syracuseStep 712027 = 1068041) B1068041
theorem B3989087 : Blo 523799 3989087 := bstep (se 1 (by rfl) ⟨2991815, by rfl⟩ : syracuseStep 3989087 = 5983631) B5983631
theorem B9690841 : Blo 523799 9690841 := bstep (se 2 (by rfl) ⟨3634065, by rfl⟩ : syracuseStep 9690841 = 7268131) B7268131
theorem B23125733 : Blo 523799 23125733 := bstep (se 4 (by rfl) ⟨2168037, by rfl⟩ : syracuseStep 23125733 = 4336075) B4336075
theorem B4481027 : Blo 523799 4481027 := bstep (se 1 (by rfl) ⟨3360770, by rfl⟩ : syracuseStep 4481027 = 6721541) B6721541
theorem B1335305 : Blo 523799 1335305 := bstep (se 2 (by rfl) ⟨500739, by rfl⟩ : syracuseStep 1335305 = 1001479) B1001479
theorem B8184017 : Blo 523799 8184017 := bstep (se 2 (by rfl) ⟨3069006, by rfl⟩ : syracuseStep 8184017 = 6138013) B6138013
theorem B1794479 : Blo 523799 1794479 := bstep (se 1 (by rfl) ⟨1345859, by rfl⟩ : syracuseStep 1794479 = 2691719) B2691719
theorem B10216145 : Blo 523799 10216145 := bstep (se 2 (by rfl) ⟨3831054, by rfl⟩ : syracuseStep 10216145 = 7662109) B7662109
theorem B5694401 : Blo 523799 5694401 := bstep (se 2 (by rfl) ⟨2135400, by rfl⟩ : syracuseStep 5694401 = 4270801) B4270801
theorem B5071835 : Blo 523799 5071835 := bstep (se 1 (by rfl) ⟨3803876, by rfl⟩ : syracuseStep 5071835 = 7607753) B7607753
theorem B845255 : Blo 523799 845255 := bstep (se 1 (by rfl) ⟨633941, by rfl⟩ : syracuseStep 845255 = 1267883) B1267883
theorem B943913 : Blo 523799 943913 := bstep (se 2 (by rfl) ⟨353967, by rfl⟩ : syracuseStep 943913 = 707935) B707935
theorem B3827897 : Blo 523799 3827897 := bstep (se 2 (by rfl) ⟨1435461, by rfl⟩ : syracuseStep 3827897 = 2870923) B2870923
theorem B2844953 : Blo 523799 2844953 := bstep (se 2 (by rfl) ⟨1066857, by rfl⟩ : syracuseStep 2844953 = 2133715) B2133715
theorem B3369383 : Blo 523799 3369383 := bstep (se 1 (by rfl) ⟨2527037, by rfl⟩ : syracuseStep 3369383 = 5054075) B5054075
theorem B5990921 : Blo 523799 5990921 := bstep (se 2 (by rfl) ⟨2246595, by rfl⟩ : syracuseStep 5990921 = 4493191) B4493191
theorem B1796681 : Blo 523799 1796681 := bstep (se 2 (by rfl) ⟨673755, by rfl⟩ : syracuseStep 1796681 = 1347511) B1347511
theorem B11332487 : Blo 523799 11332487 := bstep (se 1 (by rfl) ⟨8499365, by rfl⟩ : syracuseStep 11332487 = 16998731) B16998731
theorem B945067 : Blo 523799 945067 := bstep (se 1 (by rfl) ⟨708800, by rfl⟩ : syracuseStep 945067 = 1417601) B1417601
theorem B3370099 : Blo 523799 3370099 := bstep (se 1 (by rfl) ⟨2527574, by rfl⟩ : syracuseStep 3370099 = 5055149) B5055149
theorem B5139571 : Blo 523799 5139571 := bstep (se 1 (by rfl) ⟨3854678, by rfl⟩ : syracuseStep 5139571 = 7709357) B7709357
theorem B4255163 : Blo 523799 4255163 := bstep (se 1 (by rfl) ⟨3191372, by rfl⟩ : syracuseStep 4255163 = 6382745) B6382745
theorem B1502651 : Blo 523799 1502651 := bstep (se 1 (by rfl) ⟨1126988, by rfl⟩ : syracuseStep 1502651 = 2253977) B2253977
theorem B4484717 : Blo 523799 4484717 := bstep (se 3 (by rfl) ⟨840884, by rfl⟩ : syracuseStep 4484717 = 1681769) B1681769
theorem B3632849 : Blo 523799 3632849 := bstep (se 2 (by rfl) ⟨1362318, by rfl⟩ : syracuseStep 3632849 = 2724637) B2724637
theorem B1897411 : Blo 523799 1897411 := bstep (se 1 (by rfl) ⟨1423058, by rfl⟩ : syracuseStep 1897411 = 2846117) B2846117
theorem B2127097 : Blo 523799 2127097 := bstep (se 2 (by rfl) ⟨797661, by rfl⟩ : syracuseStep 2127097 = 1595323) B1595323
theorem B947495 : Blo 523799 947495 := bstep (se 1 (by rfl) ⟨710621, by rfl⟩ : syracuseStep 947495 = 1421243) B1421243
theorem B3994919 : Blo 523799 3994919 := bstep (se 1 (by rfl) ⟨2996189, by rfl⟩ : syracuseStep 3994919 = 5992379) B5992379
theorem B5043617 : Blo 523799 5043617 := bstep (se 2 (by rfl) ⟨1891356, by rfl⟩ : syracuseStep 5043617 = 3782713) B3782713
theorem B3405797 : Blo 523799 3405797 := bstep (se 4 (by rfl) ⟨319293, by rfl⟩ : syracuseStep 3405797 = 638587) B638587
theorem B2652425 : Blo 523799 2652425 := bstep (se 2 (by rfl) ⟨994659, by rfl⟩ : syracuseStep 2652425 = 1989319) B1989319
theorem B1997081 : Blo 523799 1997081 := bstep (se 2 (by rfl) ⟨748905, by rfl⟩ : syracuseStep 1997081 = 1497811) B1497811
theorem B1079983 : Blo 523799 1079983 := bstep (se 1 (by rfl) ⟨809987, by rfl⟩ : syracuseStep 1079983 = 1619975) B1619975
theorem B2128783 : Blo 523799 2128783 := bstep (se 1 (by rfl) ⟨1596587, by rfl⟩ : syracuseStep 2128783 = 3193175) B3193175
theorem B2554895 : Blo 523799 2554895 := bstep (se 1 (by rfl) ⟨1916171, by rfl⟩ : syracuseStep 2554895 = 3832343) B3832343
theorem B1178747 : Blo 523799 1178747 := bstep (se 1 (by rfl) ⟨884060, by rfl⟩ : syracuseStep 1178747 = 1768121) B1768121
theorem B1178873 : Blo 523799 1178873 := bstep (se 2 (by rfl) ⟨442077, by rfl⟩ : syracuseStep 1178873 = 884155) B884155
theorem B1768823 : Blo 523799 1768823 := bstep (se 1 (by rfl) ⟨1326617, by rfl⟩ : syracuseStep 1768823 = 2653235) B2653235
theorem B2653559 : Blo 523799 2653559 := bstep (se 1 (by rfl) ⟨1990169, by rfl⟩ : syracuseStep 2653559 = 3980339) B3980339
theorem B785801 : Blo 523799 785801 := bstep (se 2 (by rfl) ⟨294675, by rfl⟩ : syracuseStep 785801 = 589351) B589351
theorem B1179017 : Blo 523799 1179017 := bstep (se 2 (by rfl) ⟨442131, by rfl⟩ : syracuseStep 1179017 = 884263) B884263
theorem B1179143 : Blo 523799 1179143 := bstep (se 1 (by rfl) ⟨884357, by rfl⟩ : syracuseStep 1179143 = 1768715) B1768715
theorem B2653721 : Blo 523799 2653721 := bstep (se 2 (by rfl) ⟨995145, by rfl⟩ : syracuseStep 2653721 = 1990291) B1990291
theorem B523839 : Blo 523799 523839 := bstep (se 1 (by rfl) ⟨392879, by rfl⟩ : syracuseStep 523839 = 785759) B785759
theorem B523847 : Blo 523799 523847 := bstep (se 1 (by rfl) ⟨392885, by rfl⟩ : syracuseStep 523847 = 785771) B785771
theorem B1179323 : Blo 523799 1179323 := bstep (se 1 (by rfl) ⟨884492, by rfl⟩ : syracuseStep 1179323 = 1768985) B1768985
theorem B523999 : Blo 523799 523999 := bstep (se 1 (by rfl) ⟨392999, by rfl⟩ : syracuseStep 523999 = 785999) B785999
theorem B786155 : Blo 523799 786155 := bstep (se 1 (by rfl) ⟨589616, by rfl⟩ : syracuseStep 786155 = 1179233) B1179233
theorem B884459 : Blo 523799 884459 := bstep (se 1 (by rfl) ⟨663344, by rfl⟩ : syracuseStep 884459 = 1326689) B1326689
theorem B524079 : Blo 523799 524079 := bstep (se 1 (by rfl) ⟨393059, by rfl⟩ : syracuseStep 524079 = 786119) B786119
theorem B1179449 : Blo 523799 1179449 := bstep (se 2 (by rfl) ⟨442293, by rfl⟩ : syracuseStep 1179449 = 884587) B884587
theorem B5046077 : Blo 523799 5046077 := bstep (se 3 (by rfl) ⟨946139, by rfl⟩ : syracuseStep 5046077 = 1892279) B1892279
theorem B524187 : Blo 523799 524187 := bstep (se 1 (by rfl) ⟨393140, by rfl⟩ : syracuseStep 524187 = 786281) B786281
theorem B524239 : Blo 523799 524239 := bstep (se 1 (by rfl) ⟨393179, by rfl⟩ : syracuseStep 524239 = 786359) B786359
theorem B786383 : Blo 523799 786383 := bstep (se 1 (by rfl) ⟨589787, by rfl⟩ : syracuseStep 786383 = 1179575) B1179575
theorem B524263 : Blo 523799 524263 := bstep (se 1 (by rfl) ⟨393197, by rfl⟩ : syracuseStep 524263 = 786395) B786395
theorem B3801167 : Blo 523799 3801167 := bstep (se 1 (by rfl) ⟨2850875, by rfl⟩ : syracuseStep 3801167 = 5701751) B5701751
theorem B524519 : Blo 523799 524519 := bstep (se 1 (by rfl) ⟨393389, by rfl⟩ : syracuseStep 524519 = 786779) B786779
theorem B1179935 : Blo 523799 1179935 := bstep (se 1 (by rfl) ⟨884951, by rfl⟩ : syracuseStep 1179935 = 1769903) B1769903
theorem B786719 : Blo 523799 786719 := bstep (se 1 (by rfl) ⟨590039, by rfl⟩ : syracuseStep 786719 = 1180079) B1180079
theorem B786743 : Blo 523799 786743 := bstep (se 1 (by rfl) ⟨590057, by rfl⟩ : syracuseStep 786743 = 1180115) B1180115
theorem B10944827 : Blo 523799 10944827 := bstep (se 1 (by rfl) ⟨8208620, by rfl⟩ : syracuseStep 10944827 = 16417241) B16417241
theorem B786815 : Blo 523799 786815 := bstep (se 1 (by rfl) ⟨590111, by rfl⟩ : syracuseStep 786815 = 1180223) B1180223
theorem B524671 : Blo 523799 524671 := bstep (se 1 (by rfl) ⟨393503, by rfl⟩ : syracuseStep 524671 = 787007) B787007
theorem B8552879 : Blo 523799 8552879 := bstep (se 1 (by rfl) ⟨6414659, by rfl⟩ : syracuseStep 8552879 = 12829319) B12829319
theorem B786887 : Blo 523799 786887 := bstep (se 1 (by rfl) ⟨590165, by rfl⟩ : syracuseStep 786887 = 1180331) B1180331
theorem B590287 : Blo 523799 590287 := bstep (se 1 (by rfl) ⟨442715, by rfl⟩ : syracuseStep 590287 = 885431) B885431
theorem B524751 : Blo 523799 524751 := bstep (se 1 (by rfl) ⟨393563, by rfl⟩ : syracuseStep 524751 = 787127) B787127
theorem B8520187 : Blo 523799 8520187 := bstep (se 1 (by rfl) ⟨6390140, by rfl⟩ : syracuseStep 8520187 = 12780281) B12780281
theorem B885343 : Blo 523799 885343 := bstep (se 1 (by rfl) ⟨664007, by rfl⟩ : syracuseStep 885343 = 1328015) B1328015
theorem B524903 : Blo 523799 524903 := bstep (se 1 (by rfl) ⟨393677, by rfl⟩ : syracuseStep 524903 = 787355) B787355
theorem B787241 : Blo 523799 787241 := bstep (se 2 (by rfl) ⟨295215, by rfl⟩ : syracuseStep 787241 = 590431) B590431
theorem B787247 : Blo 523799 787247 := bstep (se 1 (by rfl) ⟨590435, by rfl⟩ : syracuseStep 787247 = 1180871) B1180871
theorem B525167 : Blo 523799 525167 := bstep (se 1 (by rfl) ⟨393875, by rfl⟩ : syracuseStep 525167 = 787751) B787751
theorem B1180583 : Blo 523799 1180583 := bstep (se 1 (by rfl) ⟨885437, by rfl⟩ : syracuseStep 1180583 = 1770875) B1770875
theorem B787367 : Blo 523799 787367 := bstep (se 1 (by rfl) ⟨590525, by rfl⟩ : syracuseStep 787367 = 1181051) B1181051
theorem B525223 : Blo 523799 525223 := bstep (se 1 (by rfl) ⟨393917, by rfl⟩ : syracuseStep 525223 = 787835) B787835
theorem B885755 : Blo 523799 885755 := bstep (se 1 (by rfl) ⟨664316, by rfl⟩ : syracuseStep 885755 = 1328633) B1328633
theorem B787451 : Blo 523799 787451 := bstep (se 1 (by rfl) ⟨590588, by rfl⟩ : syracuseStep 787451 = 1181177) B1181177
theorem B525307 : Blo 523799 525307 := bstep (se 1 (by rfl) ⟨393980, by rfl⟩ : syracuseStep 525307 = 787961) B787961
theorem B787511 : Blo 523799 787511 := bstep (se 1 (by rfl) ⟨590633, by rfl⟩ : syracuseStep 787511 = 1181267) B1181267
theorem B525375 : Blo 523799 525375 := bstep (se 1 (by rfl) ⟨394031, by rfl⟩ : syracuseStep 525375 = 788063) B788063
theorem B4785277 : Blo 523799 4785277 := bstep (se 3 (by rfl) ⟨897239, by rfl⟩ : syracuseStep 4785277 = 1794479) B1794479
theorem B787631 : Blo 523799 787631 := bstep (se 1 (by rfl) ⟨590723, by rfl⟩ : syracuseStep 787631 = 1181447) B1181447
theorem B525519 : Blo 523799 525519 := bstep (se 1 (by rfl) ⟨394139, by rfl⟩ : syracuseStep 525519 = 788279) B788279
theorem B591259 : Blo 523799 591259 := bstep (se 1 (by rfl) ⟨443444, by rfl⟩ : syracuseStep 591259 = 886889) B886889
theorem B525723 : Blo 523799 525723 := bstep (se 1 (by rfl) ⟨394292, by rfl⟩ : syracuseStep 525723 = 788585) B788585
theorem B886187 : Blo 523799 886187 := bstep (se 1 (by rfl) ⟨664640, by rfl⟩ : syracuseStep 886187 = 1329281) B1329281
theorem B3376637 : Blo 523799 3376637 := bstep (se 3 (by rfl) ⟨633119, by rfl⟩ : syracuseStep 3376637 = 1266239) B1266239
theorem B497845763 : Blo 523799 497845763 := bstep (se 1 (by rfl) ⟨373384322, by rfl⟩ : syracuseStep 497845763 = 746768645) B746768645
theorem B788039 : Blo 523799 788039 := bstep (se 1 (by rfl) ⟨591029, by rfl⟩ : syracuseStep 788039 = 1182059) B1182059
theorem B1771091 : Blo 523799 1771091 := bstep (se 1 (by rfl) ⟨1328318, by rfl⟩ : syracuseStep 1771091 = 2656637) B2656637
theorem B525935 : Blo 523799 525935 := bstep (se 1 (by rfl) ⟨394451, by rfl⟩ : syracuseStep 525935 = 788903) B788903
theorem B1443439 : Blo 523799 1443439 := bstep (se 1 (by rfl) ⟨1082579, by rfl⟩ : syracuseStep 1443439 = 2165159) B2165159
theorem B788135 : Blo 523799 788135 := bstep (se 1 (by rfl) ⟨591101, by rfl⟩ : syracuseStep 788135 = 1182203) B1182203
theorem B525991 : Blo 523799 525991 := bstep (se 1 (by rfl) ⟨394493, by rfl⟩ : syracuseStep 525991 = 788987) B788987
theorem B788219 : Blo 523799 788219 := bstep (se 1 (by rfl) ⟨591164, by rfl⟩ : syracuseStep 788219 = 1182329) B1182329
theorem B526075 : Blo 523799 526075 := bstep (se 1 (by rfl) ⟨394556, by rfl⟩ : syracuseStep 526075 = 789113) B789113
theorem B788255 : Blo 523799 788255 := bstep (se 1 (by rfl) ⟨591191, by rfl⟩ : syracuseStep 788255 = 1182383) B1182383
theorem B526111 : Blo 523799 526111 := bstep (se 1 (by rfl) ⟨394583, by rfl⟩ : syracuseStep 526111 = 789167) B789167
theorem B526143 : Blo 523799 526143 := bstep (se 1 (by rfl) ⟨394607, by rfl⟩ : syracuseStep 526143 = 789215) B789215
theorem B1181519 : Blo 523799 1181519 := bstep (se 1 (by rfl) ⟨886139, by rfl⟩ : syracuseStep 1181519 = 1772279) B1772279
theorem B788303 : Blo 523799 788303 := bstep (se 1 (by rfl) ⟨591227, by rfl⟩ : syracuseStep 788303 = 1182455) B1182455
theorem B1771361 : Blo 523799 1771361 := bstep (se 2 (by rfl) ⟨664260, by rfl⟩ : syracuseStep 1771361 = 1328521) B1328521
theorem B1181537 : Blo 523799 1181537 := bstep (se 2 (by rfl) ⟨443076, by rfl⟩ : syracuseStep 1181537 = 886153) B886153
theorem B886727 : Blo 523799 886727 := bstep (se 1 (by rfl) ⟨665045, by rfl⟩ : syracuseStep 886727 = 1330091) B1330091
theorem B788423 : Blo 523799 788423 := bstep (se 1 (by rfl) ⟨591317, by rfl⟩ : syracuseStep 788423 = 1182635) B1182635
theorem B526319 : Blo 523799 526319 := bstep (se 1 (by rfl) ⟨394739, by rfl⟩ : syracuseStep 526319 = 789479) B789479
theorem B526491 : Blo 523799 526491 := bstep (se 1 (by rfl) ⟨394868, by rfl⟩ : syracuseStep 526491 = 789737) B789737
theorem B526527 : Blo 523799 526527 := bstep (se 1 (by rfl) ⟨394895, by rfl⟩ : syracuseStep 526527 = 789791) B789791
theorem B887017 : Blo 523799 887017 := bstep (se 2 (by rfl) ⟨332631, by rfl⟩ : syracuseStep 887017 = 665263) B665263
theorem B788777 : Blo 523799 788777 := bstep (se 2 (by rfl) ⟨295791, by rfl⟩ : syracuseStep 788777 = 591583) B591583
theorem B788783 : Blo 523799 788783 := bstep (se 1 (by rfl) ⟨591587, by rfl⟩ : syracuseStep 788783 = 1183175) B1183175
theorem B526639 : Blo 523799 526639 := bstep (se 1 (by rfl) ⟨394979, by rfl⟩ : syracuseStep 526639 = 789959) B789959
theorem B1182113 : Blo 523799 1182113 := bstep (se 2 (by rfl) ⟨443292, by rfl⟩ : syracuseStep 1182113 = 886585) B886585
theorem B592411 : Blo 523799 592411 := bstep (se 1 (by rfl) ⟨444308, by rfl⟩ : syracuseStep 592411 = 888617) B888617
theorem B526875 : Blo 523799 526875 := bstep (se 1 (by rfl) ⟨395156, by rfl⟩ : syracuseStep 526875 = 790313) B790313
theorem B2656799 : Blo 523799 2656799 := bstep (se 1 (by rfl) ⟨1992599, by rfl⟩ : syracuseStep 2656799 = 3985199) B3985199
theorem B1772063 : Blo 523799 1772063 := bstep (se 1 (by rfl) ⟨1329047, by rfl⟩ : syracuseStep 1772063 = 2658095) B2658095
theorem B1182239 : Blo 523799 1182239 := bstep (se 1 (by rfl) ⟨886679, by rfl⟩ : syracuseStep 1182239 = 1773359) B1773359
theorem B789023 : Blo 523799 789023 := bstep (se 1 (by rfl) ⟨591767, by rfl⟩ : syracuseStep 789023 = 1183535) B1183535
theorem B526879 : Blo 523799 526879 := bstep (se 1 (by rfl) ⟨395159, by rfl⟩ : syracuseStep 526879 = 790319) B790319
theorem B7572113 : Blo 523799 7572113 := bstep (se 2 (by rfl) ⟨2839542, by rfl⟩ : syracuseStep 7572113 = 5679085) B5679085
theorem B887483 : Blo 523799 887483 := bstep (se 1 (by rfl) ⟨665612, by rfl⟩ : syracuseStep 887483 = 1331225) B1331225
theorem B527195 : Blo 523799 527195 := bstep (se 1 (by rfl) ⟨395396, by rfl⟩ : syracuseStep 527195 = 790793) B790793
theorem B789407 : Blo 523799 789407 := bstep (se 1 (by rfl) ⟨592055, by rfl⟩ : syracuseStep 789407 = 1184111) B1184111
theorem B527263 : Blo 523799 527263 := bstep (se 1 (by rfl) ⟨395447, by rfl⟩ : syracuseStep 527263 = 790895) B790895
theorem B789455 : Blo 523799 789455 := bstep (se 1 (by rfl) ⟨592091, by rfl⟩ : syracuseStep 789455 = 1184183) B1184183
theorem B789545 : Blo 523799 789545 := bstep (se 2 (by rfl) ⟨296079, by rfl⟩ : syracuseStep 789545 = 592159) B592159
theorem B15109163 : Blo 523799 15109163 := bstep (se 1 (by rfl) ⟨11331872, by rfl⟩ : syracuseStep 15109163 = 22663745) B22663745
theorem B789551 : Blo 523799 789551 := bstep (se 1 (by rfl) ⟨592163, by rfl⟩ : syracuseStep 789551 = 1184327) B1184327
theorem B527407 : Blo 523799 527407 := bstep (se 1 (by rfl) ⟨395555, by rfl⟩ : syracuseStep 527407 = 791111) B791111
theorem B789575 : Blo 523799 789575 := bstep (se 1 (by rfl) ⟨592181, by rfl⟩ : syracuseStep 789575 = 1184363) B1184363
theorem B527431 : Blo 523799 527431 := bstep (se 1 (by rfl) ⟨395573, by rfl⟩ : syracuseStep 527431 = 791147) B791147
theorem B527583 : Blo 523799 527583 := bstep (se 1 (by rfl) ⟨395687, by rfl⟩ : syracuseStep 527583 = 791375) B791375
theorem B789839 : Blo 523799 789839 := bstep (se 1 (by rfl) ⟨592379, by rfl⟩ : syracuseStep 789839 = 1184759) B1184759
theorem B789929 : Blo 523799 789929 := bstep (se 2 (by rfl) ⟨296223, by rfl⟩ : syracuseStep 789929 = 592447) B592447
theorem B2526653 : Blo 523799 2526653 := bstep (se 3 (by rfl) ⟨473747, by rfl⟩ : syracuseStep 2526653 = 947495) B947495
theorem B593383 : Blo 523799 593383 := bstep (se 1 (by rfl) ⟨445037, by rfl⟩ : syracuseStep 593383 = 890075) B890075
theorem B2002427 : Blo 523799 2002427 := bstep (se 1 (by rfl) ⟨1501820, by rfl⟩ : syracuseStep 2002427 = 3003641) B3003641
theorem B790079 : Blo 523799 790079 := bstep (se 1 (by rfl) ⟨592559, by rfl⟩ : syracuseStep 790079 = 1185119) B1185119
theorem B921179 : Blo 523799 921179 := bstep (se 1 (by rfl) ⟨690884, by rfl⟩ : syracuseStep 921179 = 1381769) B1381769
theorem B790343 : Blo 523799 790343 := bstep (se 1 (by rfl) ⟨592757, by rfl⟩ : syracuseStep 790343 = 1185515) B1185515
theorem B1773467 : Blo 523799 1773467 := bstep (se 1 (by rfl) ⟨1330100, by rfl⟩ : syracuseStep 1773467 = 2660201) B2660201
theorem B1183643 : Blo 523799 1183643 := bstep (se 1 (by rfl) ⟨887732, by rfl⟩ : syracuseStep 1183643 = 1775465) B1775465
theorem B790427 : Blo 523799 790427 := bstep (se 1 (by rfl) ⟨592820, by rfl⟩ : syracuseStep 790427 = 1185641) B1185641
theorem B888799 : Blo 523799 888799 := bstep (se 1 (by rfl) ⟨666599, by rfl⟩ : syracuseStep 888799 = 1333199) B1333199
theorem B4493465 : Blo 523799 4493465 := bstep (se 2 (by rfl) ⟨1685049, by rfl⟩ : syracuseStep 4493465 = 3370099) B3370099
theorem B6852761 : Blo 523799 6852761 := bstep (se 2 (by rfl) ⟨2569785, by rfl⟩ : syracuseStep 6852761 = 5139571) B5139571
theorem B1183931 : Blo 523799 1183931 := bstep (se 1 (by rfl) ⟨887948, by rfl⟩ : syracuseStep 1183931 = 1775897) B1775897
theorem B3379583 : Blo 523799 3379583 := bstep (se 1 (by rfl) ⟨2534687, by rfl⟩ : syracuseStep 3379583 = 5069375) B5069375
theorem B790991 : Blo 523799 790991 := bstep (se 1 (by rfl) ⟨593243, by rfl⟩ : syracuseStep 790991 = 1186487) B1186487
theorem B13832693 : Blo 523799 13832693 := bstep (se 5 (by rfl) ⟨648407, by rfl⟩ : syracuseStep 13832693 = 1296815) B1296815
theorem B791033 : Blo 523799 791033 := bstep (se 2 (by rfl) ⟨296637, by rfl⟩ : syracuseStep 791033 = 593275) B593275
theorem B791135 : Blo 523799 791135 := bstep (se 1 (by rfl) ⟨593351, by rfl⟩ : syracuseStep 791135 = 1186703) B1186703
theorem B889447 : Blo 523799 889447 := bstep (se 1 (by rfl) ⟨667085, by rfl⟩ : syracuseStep 889447 = 1334171) B1334171
theorem B1184417 : Blo 523799 1184417 := bstep (se 2 (by rfl) ⟨444156, by rfl⟩ : syracuseStep 1184417 = 888313) B888313
theorem B889609 : Blo 523799 889609 := bstep (se 2 (by rfl) ⟨333603, by rfl⟩ : syracuseStep 889609 = 667207) B667207
theorem B8786819 : Blo 523799 8786819 := bstep (se 1 (by rfl) ⟨6590114, by rfl⟩ : syracuseStep 8786819 = 13180229) B13180229
theorem B4002695 : Blo 523799 4002695 := bstep (se 1 (by rfl) ⟨3002021, by rfl⟩ : syracuseStep 4002695 = 6004043) B6004043
theorem B1774601 : Blo 523799 1774601 := bstep (se 2 (by rfl) ⟨665475, by rfl⟩ : syracuseStep 1774601 = 1330951) B1330951
theorem B1184777 : Blo 523799 1184777 := bstep (se 2 (by rfl) ⟨444291, by rfl⟩ : syracuseStep 1184777 = 888583) B888583
theorem B2659391 : Blo 523799 2659391 := bstep (se 1 (by rfl) ⟨1994543, by rfl⟩ : syracuseStep 2659391 = 3989087) B3989087
theorem B1774655 : Blo 523799 1774655 := bstep (se 1 (by rfl) ⟨1330991, by rfl⟩ : syracuseStep 1774655 = 2661983) B2661983
theorem B1184831 : Blo 523799 1184831 := bstep (se 1 (by rfl) ⟨888623, by rfl⟩ : syracuseStep 1184831 = 1777247) B1777247
theorem B791615 : Blo 523799 791615 := bstep (se 1 (by rfl) ⟨593711, by rfl⟩ : syracuseStep 791615 = 1187423) B1187423
theorem B791657 : Blo 523799 791657 := bstep (se 2 (by rfl) ⟨296871, by rfl⟩ : syracuseStep 791657 = 593743) B593743
theorem B2987351 : Blo 523799 2987351 := bstep (se 1 (by rfl) ⟨2240513, by rfl⟩ : syracuseStep 2987351 = 4481027) B4481027
theorem B890203 : Blo 523799 890203 := bstep (se 1 (by rfl) ⟨667652, by rfl⟩ : syracuseStep 890203 = 1335305) B1335305
theorem B1185767 : Blo 523799 1185767 := bstep (se 1 (by rfl) ⟨889325, by rfl⟩ : syracuseStep 1185767 = 1778651) B1778651
theorem B3381223 : Blo 523799 3381223 := bstep (se 1 (by rfl) ⟨2535917, by rfl⟩ : syracuseStep 3381223 = 5071835) B5071835
theorem B1185785 : Blo 523799 1185785 := bstep (se 2 (by rfl) ⟨444669, by rfl⟩ : syracuseStep 1185785 = 889339) B889339
theorem B1185875 : Blo 523799 1185875 := bstep (se 1 (by rfl) ⟨889406, by rfl⟩ : syracuseStep 1185875 = 1778813) B1778813
theorem B1185947 : Blo 523799 1185947 := bstep (se 1 (by rfl) ⟨889460, by rfl⟩ : syracuseStep 1185947 = 1778921) B1778921
theorem B1186055 : Blo 523799 1186055 := bstep (se 1 (by rfl) ⟨889541, by rfl⟩ : syracuseStep 1186055 = 1779083) B1779083
theorem B1186361 : Blo 523799 1186361 := bstep (se 2 (by rfl) ⟨444885, by rfl⟩ : syracuseStep 1186361 = 889771) B889771
theorem B2529881 : Blo 523799 2529881 := bstep (se 2 (by rfl) ⟨948705, by rfl⟩ : syracuseStep 2529881 = 1897411) B1897411
theorem B4791149 : Blo 523799 4791149 := bstep (se 3 (by rfl) ⟨898340, by rfl⟩ : syracuseStep 4791149 = 1796681) B1796681
theorem B1187081 : Blo 523799 1187081 := bstep (se 2 (by rfl) ⟨445155, by rfl⟩ : syracuseStep 1187081 = 890311) B890311
theorem B2989811 : Blo 523799 2989811 := bstep (se 1 (by rfl) ⟨2242358, by rfl⟩ : syracuseStep 2989811 = 4484717) B4484717
theorem B1777463 : Blo 523799 1777463 := bstep (se 1 (by rfl) ⟨1333097, by rfl⟩ : syracuseStep 1777463 = 2666195) B2666195
theorem B1777895 : Blo 523799 1777895 := bstep (se 1 (by rfl) ⟨1333421, by rfl⟩ : syracuseStep 1777895 = 2666843) B2666843
theorem B15180209 : Blo 523799 15180209 := bstep (se 2 (by rfl) ⟨5692578, by rfl⟩ : syracuseStep 15180209 = 11385157) B11385157
theorem B1679849 : Blo 523799 1679849 := bstep (se 2 (by rfl) ⟨629943, by rfl⟩ : syracuseStep 1679849 = 1259887) B1259887
theorem B6005501 : Blo 523799 6005501 := bstep (se 3 (by rfl) ⟨1126031, by rfl⟩ : syracuseStep 6005501 = 2252063) B2252063
theorem B1778489 : Blo 523799 1778489 := bstep (se 2 (by rfl) ⟨666933, by rfl⟩ : syracuseStep 1778489 = 1333867) B1333867
theorem B2663279 : Blo 523799 2663279 := bstep (se 1 (by rfl) ⟨1997459, by rfl⟩ : syracuseStep 2663279 = 3994919) B3994919
theorem B1778543 : Blo 523799 1778543 := bstep (se 1 (by rfl) ⟨1333907, by rfl⟩ : syracuseStep 1778543 = 2667815) B2667815
theorem B4007069 : Blo 523799 4007069 := bstep (se 3 (by rfl) ⟨751325, by rfl⟩ : syracuseStep 4007069 = 1502651) B1502651
theorem B2991269 : Blo 523799 2991269 := bstep (se 4 (by rfl) ⟨280431, by rfl⟩ : syracuseStep 2991269 = 560863) B560863
theorem B3515557 : Blo 523799 3515557 := bstep (se 4 (by rfl) ⟨329583, by rfl⟩ : syracuseStep 3515557 = 659167) B659167
theorem B2270531 : Blo 523799 2270531 := bstep (se 1 (by rfl) ⟨1702898, by rfl⟩ : syracuseStep 2270531 = 3405797) B3405797
theorem B1779353 : Blo 523799 1779353 := bstep (se 2 (by rfl) ⟨667257, by rfl⟩ : syracuseStep 1779353 = 1334515) B1334515
theorem B1779947 : Blo 523799 1779947 := bstep (se 1 (by rfl) ⟨1334960, by rfl⟩ : syracuseStep 1779947 = 2669921) B2669921
theorem B2992409 : Blo 523799 2992409 := bstep (se 2 (by rfl) ⟨1122153, by rfl⟩ : syracuseStep 2992409 = 2244307) B2244307
theorem B12921121 : Blo 523799 12921121 := bstep (se 2 (by rfl) ⟨4845420, by rfl⟩ : syracuseStep 12921121 = 9690841) B9690841
theorem B666139 : Blo 523799 666139 := bstep (se 1 (by rfl) ⟨499604, by rfl⟩ : syracuseStep 666139 = 999209) B999209
theorem B797321 : Blo 523799 797321 := bstep (se 2 (by rfl) ⟨298995, by rfl⟩ : syracuseStep 797321 = 597991) B597991
theorem B6827123 : Blo 523799 6827123 := bstep (se 1 (by rfl) ⟨5120342, by rfl⟩ : syracuseStep 6827123 = 10240685) B10240685
theorem B2239609 : Blo 523799 2239609 := bstep (se 2 (by rfl) ⟨839853, by rfl⟩ : syracuseStep 2239609 = 1679707) B1679707
theorem B667111 : Blo 523799 667111 := bstep (se 1 (by rfl) ⟨500333, by rfl⟩ : syracuseStep 667111 = 1000667) B1000667
theorem B1781243 : Blo 523799 1781243 := bstep (se 1 (by rfl) ⟨1335932, by rfl⟩ : syracuseStep 1781243 = 2671865) B2671865
theorem B6008417 : Blo 523799 6008417 := bstep (se 2 (by rfl) ⟨2253156, by rfl⟩ : syracuseStep 6008417 = 4506313) B4506313
theorem B3026911 : Blo 523799 3026911 := bstep (se 1 (by rfl) ⟨2270183, by rfl⟩ : syracuseStep 3026911 = 4540367) B4540367
theorem B2994185 : Blo 523799 2994185 := bstep (se 2 (by rfl) ⟨1122819, by rfl⟩ : syracuseStep 2994185 = 2245639) B2245639
theorem B2535553 : Blo 523799 2535553 := bstep (se 2 (by rfl) ⟨950832, by rfl⟩ : syracuseStep 2535553 = 1901665) B1901665
theorem B1683641 : Blo 523799 1683641 := bstep (se 2 (by rfl) ⟨631365, by rfl⟩ : syracuseStep 1683641 = 1262731) B1262731
theorem B4108553 : Blo 523799 4108553 := bstep (se 2 (by rfl) ⟨1540707, by rfl⟩ : syracuseStep 4108553 = 3081415) B3081415
theorem B4273847 : Blo 523799 4273847 := bstep (se 1 (by rfl) ⟨3205385, by rfl⟩ : syracuseStep 4273847 = 6410771) B6410771
theorem B38975185 : Blo 523799 38975185 := bstep (se 2 (by rfl) ⟨14615694, by rfl⟩ : syracuseStep 38975185 = 29231389) B29231389
theorem B4568879 : Blo 523799 4568879 := bstep (se 1 (by rfl) ⟨3426659, by rfl⟩ : syracuseStep 4568879 = 6853319) B6853319
theorem B3192713 : Blo 523799 3192713 := bstep (se 2 (by rfl) ⟨1197267, by rfl⟩ : syracuseStep 3192713 = 2394535) B2394535
theorem B1259675 : Blo 523799 1259675 := bstep (se 1 (by rfl) ⟨944756, by rfl⟩ : syracuseStep 1259675 = 1889513) B1889513
theorem B1685767 : Blo 523799 1685767 := bstep (se 1 (by rfl) ⟨1264325, by rfl⟩ : syracuseStep 1685767 = 2528651) B2528651
theorem B4503923 : Blo 523799 4503923 := bstep (se 1 (by rfl) ⟨3377942, by rfl⟩ : syracuseStep 4503923 = 6755885) B6755885
theorem B5454253 : Blo 523799 5454253 := bstep (se 3 (by rfl) ⟨1022672, by rfl⟩ : syracuseStep 5454253 = 2045345) B2045345
theorem B1260089 : Blo 523799 1260089 := bstep (se 2 (by rfl) ⟨472533, by rfl⟩ : syracuseStep 1260089 = 945067) B945067
theorem B1325929 : Blo 523799 1325929 := bstep (se 2 (by rfl) ⟨497223, by rfl⟩ : syracuseStep 1325929 = 994447) B994447
theorem B998867 : Blo 523799 998867 := bstep (se 1 (by rfl) ⟨749150, by rfl⟩ : syracuseStep 998867 = 1498301) B1498301
theorem B1621691 : Blo 523799 1621691 := bstep (se 1 (by rfl) ⟨1216268, by rfl⟩ : syracuseStep 1621691 = 2432537) B2432537
theorem B15417155 : Blo 523799 15417155 := bstep (se 1 (by rfl) ⟨11562866, by rfl⟩ : syracuseStep 15417155 = 23125733) B23125733
theorem B5456011 : Blo 523799 5456011 := bstep (se 1 (by rfl) ⟨4092008, by rfl⟩ : syracuseStep 5456011 = 8184017) B8184017
theorem B2670731 : Blo 523799 2670731 := bstep (se 1 (by rfl) ⟨2003048, by rfl⟩ : syracuseStep 2670731 = 4006097) B4006097
theorem B2671055 : Blo 523799 2671055 := bstep (se 1 (by rfl) ⟨2003291, by rfl⟩ : syracuseStep 2671055 = 4006583) B4006583
theorem B27313685 : Blo 523799 27313685 := bstep (se 6 (by rfl) ⟨640164, by rfl⟩ : syracuseStep 27313685 = 1280329) B1280329
theorem B2246255 : Blo 523799 2246255 := bstep (se 1 (by rfl) ⟨1684691, by rfl⟩ : syracuseStep 2246255 = 3369383) B3369383
theorem B2836129 : Blo 523799 2836129 := bstep (se 2 (by rfl) ⟨1063548, by rfl⟩ : syracuseStep 2836129 = 2127097) B2127097
theorem B7554991 : Blo 523799 7554991 := bstep (se 1 (by rfl) ⟨5666243, by rfl⟩ : syracuseStep 7554991 = 11332487) B11332487
theorem B2836775 : Blo 523799 2836775 := bstep (se 1 (by rfl) ⟨2127581, by rfl⟩ : syracuseStep 2836775 = 4255163) B4255163
theorem B3983741 : Blo 523799 3983741 := bstep (se 3 (by rfl) ⟨746951, by rfl⟩ : syracuseStep 3983741 = 1493903) B1493903
theorem B2738657 : Blo 523799 2738657 := bstep (se 2 (by rfl) ⟨1026996, by rfl⟩ : syracuseStep 2738657 = 2053993) B2053993
theorem B6081911 : Blo 523799 6081911 := bstep (se 1 (by rfl) ⟨4561433, by rfl⟩ : syracuseStep 6081911 = 9122867) B9122867
theorem B3591607 : Blo 523799 3591607 := bstep (se 1 (by rfl) ⟨2693705, by rfl⟩ : syracuseStep 3591607 = 5387411) B5387411
theorem B3362411 : Blo 523799 3362411 := bstep (se 1 (by rfl) ⟨2521808, by rfl⟩ : syracuseStep 3362411 = 5043617) B5043617
theorem B2838377 : Blo 523799 2838377 := bstep (se 2 (by rfl) ⟨1064391, by rfl⟩ : syracuseStep 2838377 = 2128783) B2128783
theorem B1495169 : Blo 523799 1495169 := bstep (se 2 (by rfl) ⟨560688, by rfl⟩ : syracuseStep 1495169 = 1121377) B1121377
theorem B1331387 : Blo 523799 1331387 := bstep (se 1 (by rfl) ⟨998540, by rfl⟩ : syracuseStep 1331387 = 1997081) B1997081
theorem B839911 : Blo 523799 839911 := bstep (se 1 (by rfl) ⟨629933, by rfl⟩ : syracuseStep 839911 = 1259867) B1259867
theorem B1331873 : Blo 523799 1331873 := bstep (se 2 (by rfl) ⟨499452, by rfl⟩ : syracuseStep 1331873 = 998905) B998905
theorem B27316997 : Blo 523799 27316997 := bstep (se 4 (by rfl) ⟨2560968, by rfl⟩ : syracuseStep 27316997 = 5121937) B5121937
theorem B10114145 : Blo 523799 10114145 := bstep (se 2 (by rfl) ⟨3792804, by rfl⟩ : syracuseStep 10114145 = 7585609) B7585609
theorem B1496171 : Blo 523799 1496171 := bstep (se 1 (by rfl) ⟨1122128, by rfl⟩ : syracuseStep 1496171 = 2244257) B2244257
theorem B3364051 : Blo 523799 3364051 := bstep (se 1 (by rfl) ⟨2523038, by rfl⟩ : syracuseStep 3364051 = 5046077) B5046077
theorem B1332571 : Blo 523799 1332571 := bstep (se 1 (by rfl) ⟨999428, by rfl⟩ : syracuseStep 1332571 = 1998857) B1998857
theorem B1594811 : Blo 523799 1594811 := bstep (se 1 (by rfl) ⟨1196108, by rfl⟩ : syracuseStep 1594811 = 2392217) B2392217
theorem B3004391 : Blo 523799 3004391 := bstep (se 1 (by rfl) ⟨2253293, by rfl⟩ : syracuseStep 3004391 = 4506587) B4506587
theorem B1333331 : Blo 523799 1333331 := bstep (se 1 (by rfl) ⟨999998, by rfl⟩ : syracuseStep 1333331 = 1999997) B1999997
theorem B841961 : Blo 523799 841961 := bstep (se 2 (by rfl) ⟨315735, by rfl⟩ : syracuseStep 841961 = 631471) B631471
theorem B5986547 : Blo 523799 5986547 := bstep (se 1 (by rfl) ⟨4489910, by rfl⟩ : syracuseStep 5986547 = 8979821) B8979821
theorem B3004847 : Blo 523799 3004847 := bstep (se 1 (by rfl) ⟨2253635, by rfl⟩ : syracuseStep 3004847 = 4507271) B4507271
theorem B1333817 : Blo 523799 1333817 := bstep (se 2 (by rfl) ⟨500181, by rfl⟩ : syracuseStep 1333817 = 1000363) B1000363
theorem B2153453 : Blo 523799 2153453 := bstep (se 3 (by rfl) ⟨403772, by rfl⟩ : syracuseStep 2153453 = 807545) B807545
theorem B1989623 : Blo 523799 1989623 := bstep (se 1 (by rfl) ⟨1492217, by rfl⟩ : syracuseStep 1989623 = 2984435) B2984435
theorem B7691321 : Blo 523799 7691321 := bstep (se 2 (by rfl) ⟨2884245, by rfl⟩ : syracuseStep 7691321 = 5768491) B5768491
theorem B842935 : Blo 523799 842935 := bstep (se 1 (by rfl) ⟨632201, by rfl⟩ : syracuseStep 842935 = 1264403) B1264403
theorem B1335163 : Blo 523799 1335163 := bstep (se 1 (by rfl) ⟨1001372, by rfl⟩ : syracuseStep 1335163 = 2002745) B2002745
theorem B2023643 : Blo 523799 2023643 := bstep (se 1 (by rfl) ⟨1517732, by rfl⟩ : syracuseStep 2023643 = 3035465) B3035465
theorem B1499417 : Blo 523799 1499417 := bstep (se 2 (by rfl) ⟨562281, by rfl⟩ : syracuseStep 1499417 = 1124563) B1124563
theorem B1335649 : Blo 523799 1335649 := bstep (se 2 (by rfl) ⟨500868, by rfl⟩ : syracuseStep 1335649 = 1001737) B1001737
theorem B4481405 : Blo 523799 4481405 := bstep (se 3 (by rfl) ⟨840263, by rfl⟩ : syracuseStep 4481405 = 1680527) B1680527
theorem B12771715 : Blo 523799 12771715 := bstep (se 1 (by rfl) ⟨9578786, by rfl⟩ : syracuseStep 12771715 = 19157573) B19157573
theorem B746491 : Blo 523799 746491 := bstep (se 1 (by rfl) ⟨559868, by rfl⟩ : syracuseStep 746491 = 1119737) B1119737
theorem B3368101 : Blo 523799 3368101 := bstep (se 4 (by rfl) ⟨315759, by rfl⟩ : syracuseStep 3368101 = 631519) B631519
theorem B2254013 : Blo 523799 2254013 := bstep (se 3 (by rfl) ⟨422627, by rfl⟩ : syracuseStep 2254013 = 845255) B845255
theorem B747191 : Blo 523799 747191 := bstep (se 1 (by rfl) ⟨560393, by rfl⟩ : syracuseStep 747191 = 1120787) B1120787
theorem B3794651 : Blo 523799 3794651 := bstep (se 1 (by rfl) ⟨2845988, by rfl⟩ : syracuseStep 3794651 = 5691977) B5691977
theorem B1501193 : Blo 523799 1501193 := bstep (se 2 (by rfl) ⟨562947, by rfl⟩ : syracuseStep 1501193 = 1125895) B1125895
theorem B3565601 : Blo 523799 3565601 := bstep (se 2 (by rfl) ⟨1337100, by rfl⟩ : syracuseStep 3565601 = 2674201) B2674201
theorem B2517101 : Blo 523799 2517101 := bstep (se 3 (by rfl) ⟨471956, by rfl⟩ : syracuseStep 2517101 = 943913) B943913
theorem B944951 : Blo 523799 944951 := bstep (se 1 (by rfl) ⟨708713, by rfl⟩ : syracuseStep 944951 = 1417427) B1417427
theorem B748615 : Blo 523799 748615 := bstep (se 1 (by rfl) ⟨561461, by rfl⟩ : syracuseStep 748615 = 1122923) B1122923
theorem B6810763 : Blo 523799 6810763 := bstep (se 1 (by rfl) ⟨5108072, by rfl⟩ : syracuseStep 6810763 = 10216145) B10216145
theorem B3796267 : Blo 523799 3796267 := bstep (se 1 (by rfl) ⟨2847200, by rfl⟩ : syracuseStep 3796267 = 5694401) B5694401
theorem B1994651 : Blo 523799 1994651 := bstep (se 1 (by rfl) ⟨1495988, by rfl⟩ : syracuseStep 1994651 = 2991977) B2991977
theorem B2551931 : Blo 523799 2551931 := bstep (se 1 (by rfl) ⟨1913948, by rfl⟩ : syracuseStep 2551931 = 3827897) B3827897
theorem B1896635 : Blo 523799 1896635 := bstep (se 1 (by rfl) ⟨1422476, by rfl⟩ : syracuseStep 1896635 = 2844953) B2844953
theorem B3993947 : Blo 523799 3993947 := bstep (se 1 (by rfl) ⟨2995460, by rfl⟩ : syracuseStep 3993947 = 5990921) B5990921
theorem B750073 : Blo 523799 750073 := bstep (se 2 (by rfl) ⟨281277, by rfl⟩ : syracuseStep 750073 = 562555) B562555
theorem B4485779 : Blo 523799 4485779 := bstep (se 1 (by rfl) ⟨3364334, by rfl⟩ : syracuseStep 4485779 = 6728669) B6728669
theorem B2421899 : Blo 523799 2421899 := bstep (se 1 (by rfl) ⟨1816424, by rfl⟩ : syracuseStep 2421899 = 3632849) B3632849
theorem B3372947 : Blo 523799 3372947 := bstep (se 1 (by rfl) ⟨2529710, by rfl⟩ : syracuseStep 3372947 = 5059421) B5059421
theorem B1996883 : Blo 523799 1996883 := bstep (se 1 (by rfl) ⟨1497662, by rfl⟩ : syracuseStep 1996883 = 2995325) B2995325
theorem B1439977 : Blo 523799 1439977 := bstep (se 2 (by rfl) ⟨539991, by rfl⟩ : syracuseStep 1439977 = 1079983) B1079983
theorem B1997369 : Blo 523799 1997369 := bstep (se 2 (by rfl) ⟨749013, by rfl⟩ : syracuseStep 1997369 = 1498027) B1498027
theorem B1800841 : Blo 523799 1800841 := bstep (se 2 (by rfl) ⟨675315, by rfl⟩ : syracuseStep 1800841 = 1350631) B1350631
theorem B1768283 : Blo 523799 1768283 := bstep (se 1 (by rfl) ⟨1326212, by rfl⟩ : syracuseStep 1768283 = 2652425) B2652425
theorem B949369 : Blo 523799 949369 := bstep (se 2 (by rfl) ⟨356013, by rfl⟩ : syracuseStep 949369 = 712027) B712027
theorem B884047 : Blo 523799 884047 := bstep (se 1 (by rfl) ⟨663035, by rfl⟩ : syracuseStep 884047 = 1326071) B1326071
theorem B1703263 : Blo 523799 1703263 := bstep (se 1 (by rfl) ⟨1277447, by rfl⟩ : syracuseStep 1703263 = 2554895) B2554895
theorem B785831 : Blo 523799 785831 := bstep (se 1 (by rfl) ⟨589373, by rfl⟩ : syracuseStep 785831 = 1178747) B1178747
theorem B884135 : Blo 523799 884135 := bstep (se 1 (by rfl) ⟨663101, by rfl⟩ : syracuseStep 884135 = 1326203) B1326203
theorem B785915 : Blo 523799 785915 := bstep (se 1 (by rfl) ⟨589436, by rfl⟩ : syracuseStep 785915 = 1178873) B1178873
theorem B884297 : Blo 523799 884297 := bstep (se 2 (by rfl) ⟨331611, by rfl⟩ : syracuseStep 884297 = 663223) B663223
theorem B1179215 : Blo 523799 1179215 := bstep (se 1 (by rfl) ⟨884411, by rfl⟩ : syracuseStep 1179215 = 1768823) B1768823
theorem B1769039 : Blo 523799 1769039 := bstep (se 1 (by rfl) ⟨1326779, by rfl⟩ : syracuseStep 1769039 = 2653559) B2653559
theorem B523867 : Blo 523799 523867 := bstep (se 1 (by rfl) ⟨392900, by rfl⟩ : syracuseStep 523867 = 785801) B785801
theorem B786011 : Blo 523799 786011 := bstep (se 1 (by rfl) ⟨589508, by rfl⟩ : syracuseStep 786011 = 1179017) B1179017
theorem B786095 : Blo 523799 786095 := bstep (se 1 (by rfl) ⟨589571, by rfl⟩ : syracuseStep 786095 = 1179143) B1179143
theorem B2653883 : Blo 523799 2653883 := bstep (se 1 (by rfl) ⟨1990412, by rfl⟩ : syracuseStep 2653883 = 3980825) B3980825
theorem B1769147 : Blo 523799 1769147 := bstep (se 1 (by rfl) ⟨1326860, by rfl⟩ : syracuseStep 1769147 = 2653721) B2653721
theorem B786215 : Blo 523799 786215 := bstep (se 1 (by rfl) ⟨589661, by rfl⟩ : syracuseStep 786215 = 1179323) B1179323
theorem B524103 : Blo 523799 524103 := bstep (se 1 (by rfl) ⟨393077, by rfl⟩ : syracuseStep 524103 = 786155) B786155
theorem B589639 : Blo 523799 589639 := bstep (se 1 (by rfl) ⟨442229, by rfl⟩ : syracuseStep 589639 = 884459) B884459
theorem B786299 : Blo 523799 786299 := bstep (se 1 (by rfl) ⟨589724, by rfl⟩ : syracuseStep 786299 = 1179449) B1179449
theorem B2129789 : Blo 523799 2129789 := bstep (se 3 (by rfl) ⟨399335, by rfl⟩ : syracuseStep 2129789 = 798671) B798671
theorem B524255 : Blo 523799 524255 := bstep (se 1 (by rfl) ⟨393191, by rfl⟩ : syracuseStep 524255 = 786383) B786383
theorem B7274681 : Blo 523799 7274681 := bstep (se 2 (by rfl) ⟨2728005, by rfl⟩ : syracuseStep 7274681 = 5456011) B5456011
theorem B786623 : Blo 523799 786623 := bstep (se 1 (by rfl) ⟨589967, by rfl⟩ : syracuseStep 786623 = 1179935) B1179935
theorem B524479 : Blo 523799 524479 := bstep (se 1 (by rfl) ⟨393359, by rfl⟩ : syracuseStep 524479 = 786719) B786719
theorem B524495 : Blo 523799 524495 := bstep (se 1 (by rfl) ⟨393371, by rfl⟩ : syracuseStep 524495 = 786743) B786743
theorem B524543 : Blo 523799 524543 := bstep (se 1 (by rfl) ⟨393407, by rfl⟩ : syracuseStep 524543 = 786815) B786815
theorem B5701919 : Blo 523799 5701919 := bstep (se 1 (by rfl) ⟨4276439, by rfl⟩ : syracuseStep 5701919 = 8552879) B8552879
theorem B524591 : Blo 523799 524591 := bstep (se 1 (by rfl) ⟨393443, by rfl⟩ : syracuseStep 524591 = 786887) B786887
theorem B524827 : Blo 523799 524827 := bstep (se 1 (by rfl) ⟨393620, by rfl⟩ : syracuseStep 524827 = 787241) B787241
theorem B524831 : Blo 523799 524831 := bstep (se 1 (by rfl) ⟨393623, by rfl⟩ : syracuseStep 524831 = 787247) B787247
theorem B787049 : Blo 523799 787049 := bstep (se 2 (by rfl) ⟨295143, by rfl⟩ : syracuseStep 787049 = 590287) B590287
theorem B787055 : Blo 523799 787055 := bstep (se 1 (by rfl) ⟨590291, by rfl⟩ : syracuseStep 787055 = 1180583) B1180583
theorem B524911 : Blo 523799 524911 := bstep (se 1 (by rfl) ⟨393683, by rfl⟩ : syracuseStep 524911 = 787367) B787367
theorem B590503 : Blo 523799 590503 := bstep (se 1 (by rfl) ⟨442877, by rfl⟩ : syracuseStep 590503 = 885755) B885755
theorem B524967 : Blo 523799 524967 := bstep (se 1 (by rfl) ⟨393725, by rfl⟩ : syracuseStep 524967 = 787451) B787451
theorem B525007 : Blo 523799 525007 := bstep (se 1 (by rfl) ⟨393755, by rfl⟩ : syracuseStep 525007 = 787511) B787511
theorem B525087 : Blo 523799 525087 := bstep (se 1 (by rfl) ⟨393815, by rfl⟩ : syracuseStep 525087 = 787631) B787631
theorem B1180457 : Blo 523799 1180457 := bstep (se 2 (by rfl) ⟨442671, by rfl⟩ : syracuseStep 1180457 = 885343) B885343
theorem B590791 : Blo 523799 590791 := bstep (se 1 (by rfl) ⟨443093, by rfl⟩ : syracuseStep 590791 = 886187) B886187
theorem B525359 : Blo 523799 525359 := bstep (se 1 (by rfl) ⟨394019, by rfl⟩ : syracuseStep 525359 = 788039) B788039
theorem B1180727 : Blo 523799 1180727 := bstep (se 1 (by rfl) ⟨885545, by rfl⟩ : syracuseStep 1180727 = 1771091) B1771091
theorem B525423 : Blo 523799 525423 := bstep (se 1 (by rfl) ⟨394067, by rfl⟩ : syracuseStep 525423 = 788135) B788135
theorem B525479 : Blo 523799 525479 := bstep (se 1 (by rfl) ⟨394109, by rfl⟩ : syracuseStep 525479 = 788219) B788219
theorem B525503 : Blo 523799 525503 := bstep (se 1 (by rfl) ⟨394127, by rfl⟩ : syracuseStep 525503 = 788255) B788255
theorem B787679 : Blo 523799 787679 := bstep (se 1 (by rfl) ⟨590759, by rfl⟩ : syracuseStep 787679 = 1181519) B1181519
theorem B525535 : Blo 523799 525535 := bstep (se 1 (by rfl) ⟨394151, by rfl⟩ : syracuseStep 525535 = 788303) B788303
theorem B1180907 : Blo 523799 1180907 := bstep (se 1 (by rfl) ⟨885680, by rfl⟩ : syracuseStep 1180907 = 1771361) B1771361
theorem B787691 : Blo 523799 787691 := bstep (se 1 (by rfl) ⟨590768, by rfl⟩ : syracuseStep 787691 = 1181537) B1181537
theorem B591151 : Blo 523799 591151 := bstep (se 1 (by rfl) ⟨443363, by rfl⟩ : syracuseStep 591151 = 886727) B886727
theorem B525615 : Blo 523799 525615 := bstep (se 1 (by rfl) ⟨394211, by rfl⟩ : syracuseStep 525615 = 788423) B788423
theorem B525851 : Blo 523799 525851 := bstep (se 1 (by rfl) ⟨394388, by rfl⟩ : syracuseStep 525851 = 788777) B788777
theorem B525855 : Blo 523799 525855 := bstep (se 1 (by rfl) ⟨394391, by rfl⟩ : syracuseStep 525855 = 788783) B788783
theorem B4490801 : Blo 523799 4490801 := bstep (se 2 (by rfl) ⟨1684050, by rfl⟩ : syracuseStep 4490801 = 3368101) B3368101
theorem B4687409 : Blo 523799 4687409 := bstep (se 2 (by rfl) ⟨1757778, by rfl⟩ : syracuseStep 4687409 = 3515557) B3515557
theorem B2655827 : Blo 523799 2655827 := bstep (se 1 (by rfl) ⟨1991870, by rfl⟩ : syracuseStep 2655827 = 3983741) B3983741
theorem B788075 : Blo 523799 788075 := bstep (se 1 (by rfl) ⟨591056, by rfl⟩ : syracuseStep 788075 = 1182113) B1182113
theorem B1771199 : Blo 523799 1771199 := bstep (se 1 (by rfl) ⟨1328399, by rfl⟩ : syracuseStep 1771199 = 2656799) B2656799
theorem B1181375 : Blo 523799 1181375 := bstep (se 1 (by rfl) ⟨886031, by rfl⟩ : syracuseStep 1181375 = 1772063) B1772063
theorem B788159 : Blo 523799 788159 := bstep (se 1 (by rfl) ⟨591119, by rfl⟩ : syracuseStep 788159 = 1182239) B1182239
theorem B526015 : Blo 523799 526015 := bstep (se 1 (by rfl) ⟨394511, by rfl⟩ : syracuseStep 526015 = 789023) B789023
theorem B5048075 : Blo 523799 5048075 := bstep (se 1 (by rfl) ⟨3786056, by rfl⟩ : syracuseStep 5048075 = 7572113) B7572113
theorem B591655 : Blo 523799 591655 := bstep (se 1 (by rfl) ⟨443741, by rfl⟩ : syracuseStep 591655 = 887483) B887483
theorem B788345 : Blo 523799 788345 := bstep (se 2 (by rfl) ⟨295629, by rfl⟩ : syracuseStep 788345 = 591259) B591259
theorem B526271 : Blo 523799 526271 := bstep (se 1 (by rfl) ⟨394703, by rfl⟩ : syracuseStep 526271 = 789407) B789407
theorem B526303 : Blo 523799 526303 := bstep (se 1 (by rfl) ⟨394727, by rfl⟩ : syracuseStep 526303 = 789455) B789455
theorem B526363 : Blo 523799 526363 := bstep (se 1 (by rfl) ⟨394772, by rfl⟩ : syracuseStep 526363 = 789545) B789545
theorem B526367 : Blo 523799 526367 := bstep (se 1 (by rfl) ⟨394775, by rfl⟩ : syracuseStep 526367 = 789551) B789551
theorem B526383 : Blo 523799 526383 := bstep (se 1 (by rfl) ⟨394787, by rfl⟩ : syracuseStep 526383 = 789575) B789575
theorem B526559 : Blo 523799 526559 := bstep (se 1 (by rfl) ⟨394919, by rfl⟩ : syracuseStep 526559 = 789839) B789839
theorem B526619 : Blo 523799 526619 := bstep (se 1 (by rfl) ⟨394964, by rfl⟩ : syracuseStep 526619 = 789929) B789929
theorem B526719 : Blo 523799 526719 := bstep (se 1 (by rfl) ⟨395039, by rfl⟩ : syracuseStep 526719 = 790079) B790079
theorem B526895 : Blo 523799 526895 := bstep (se 1 (by rfl) ⟨395171, by rfl⟩ : syracuseStep 526895 = 790343) B790343
theorem B1182311 : Blo 523799 1182311 := bstep (se 1 (by rfl) ⟨886733, by rfl⟩ : syracuseStep 1182311 = 1773467) B1773467
theorem B789095 : Blo 523799 789095 := bstep (se 1 (by rfl) ⟨591821, by rfl⟩ : syracuseStep 789095 = 1183643) B1183643
theorem B526951 : Blo 523799 526951 := bstep (se 1 (by rfl) ⟨395213, by rfl⟩ : syracuseStep 526951 = 790427) B790427
theorem B887591 : Blo 523799 887591 := bstep (se 1 (by rfl) ⟨665693, by rfl⟩ : syracuseStep 887591 = 1331387) B1331387
theorem B789287 : Blo 523799 789287 := bstep (se 1 (by rfl) ⟨591965, by rfl⟩ : syracuseStep 789287 = 1183931) B1183931
theorem B527327 : Blo 523799 527327 := bstep (se 1 (by rfl) ⟨395495, by rfl⟩ : syracuseStep 527327 = 790991) B790991
theorem B1182689 : Blo 523799 1182689 := bstep (se 2 (by rfl) ⟨443508, by rfl⟩ : syracuseStep 1182689 = 887017) B887017
theorem B527355 : Blo 523799 527355 := bstep (se 1 (by rfl) ⟨395516, by rfl⟩ : syracuseStep 527355 = 791033) B791033
theorem B527423 : Blo 523799 527423 := bstep (se 1 (by rfl) ⟨395567, by rfl⟩ : syracuseStep 527423 = 791135) B791135
theorem B887915 : Blo 523799 887915 := bstep (se 1 (by rfl) ⟨665936, by rfl⟩ : syracuseStep 887915 = 1331873) B1331873
theorem B789611 : Blo 523799 789611 := bstep (se 1 (by rfl) ⟨592208, by rfl⟩ : syracuseStep 789611 = 1184417) B1184417
theorem B1183067 : Blo 523799 1183067 := bstep (se 1 (by rfl) ⟨887300, by rfl⟩ : syracuseStep 1183067 = 1774601) B1774601
theorem B789851 : Blo 523799 789851 := bstep (se 1 (by rfl) ⟨592388, by rfl⟩ : syracuseStep 789851 = 1184777) B1184777
theorem B888185 : Blo 523799 888185 := bstep (se 2 (by rfl) ⟨333069, by rfl⟩ : syracuseStep 888185 = 666139) B666139
theorem B789881 : Blo 523799 789881 := bstep (se 2 (by rfl) ⟨296205, by rfl⟩ : syracuseStep 789881 = 592411) B592411
theorem B1772927 : Blo 523799 1772927 := bstep (se 1 (by rfl) ⟨1329695, by rfl⟩ : syracuseStep 1772927 = 2659391) B2659391
theorem B1183103 : Blo 523799 1183103 := bstep (se 1 (by rfl) ⟨887327, by rfl⟩ : syracuseStep 1183103 = 1774655) B1774655
theorem B789887 : Blo 523799 789887 := bstep (se 1 (by rfl) ⟨592415, by rfl⟩ : syracuseStep 789887 = 1184831) B1184831
theorem B527743 : Blo 523799 527743 := bstep (se 1 (by rfl) ⟨395807, by rfl⟩ : syracuseStep 527743 = 791615) B791615
theorem B527771 : Blo 523799 527771 := bstep (se 1 (by rfl) ⟨395828, by rfl⟩ : syracuseStep 527771 = 791657) B791657
theorem B790511 : Blo 523799 790511 := bstep (se 1 (by rfl) ⟨592883, by rfl⟩ : syracuseStep 790511 = 1185767) B1185767
theorem B2002927 : Blo 523799 2002927 := bstep (se 1 (by rfl) ⟨1502195, by rfl⟩ : syracuseStep 2002927 = 3004391) B3004391
theorem B790523 : Blo 523799 790523 := bstep (se 1 (by rfl) ⟨592892, by rfl⟩ : syracuseStep 790523 = 1185785) B1185785
theorem B888887 : Blo 523799 888887 := bstep (se 1 (by rfl) ⟨666665, by rfl⟩ : syracuseStep 888887 = 1333331) B1333331
theorem B790583 : Blo 523799 790583 := bstep (se 1 (by rfl) ⟨592937, by rfl⟩ : syracuseStep 790583 = 1185875) B1185875
theorem B790631 : Blo 523799 790631 := bstep (se 1 (by rfl) ⟨592973, by rfl⟩ : syracuseStep 790631 = 1185947) B1185947
theorem B2986145 : Blo 523799 2986145 := bstep (se 2 (by rfl) ⟨1119804, by rfl⟩ : syracuseStep 2986145 = 2239609) B2239609
theorem B790703 : Blo 523799 790703 := bstep (se 1 (by rfl) ⟨593027, by rfl⟩ : syracuseStep 790703 = 1186055) B1186055
theorem B9081017 : Blo 523799 9081017 := bstep (se 2 (by rfl) ⟨3405381, by rfl⟩ : syracuseStep 9081017 = 6810763) B6810763
theorem B2003231 : Blo 523799 2003231 := bstep (se 1 (by rfl) ⟨1502423, by rfl⟩ : syracuseStep 2003231 = 3004847) B3004847
theorem B889211 : Blo 523799 889211 := bstep (se 1 (by rfl) ⟨666908, by rfl⟩ : syracuseStep 889211 = 1333817) B1333817
theorem B790907 : Blo 523799 790907 := bstep (se 1 (by rfl) ⟨593180, by rfl⟩ : syracuseStep 790907 = 1186361) B1186361
theorem B4788809 : Blo 523799 4788809 := bstep (se 2 (by rfl) ⟨1795803, by rfl⟩ : syracuseStep 4788809 = 3591607) B3591607
theorem B889481 : Blo 523799 889481 := bstep (se 2 (by rfl) ⟨333555, by rfl⟩ : syracuseStep 889481 = 667111) B667111
theorem B791177 : Blo 523799 791177 := bstep (se 2 (by rfl) ⟨296691, by rfl⟩ : syracuseStep 791177 = 593383) B593383
theorem B791387 : Blo 523799 791387 := bstep (se 1 (by rfl) ⟨593540, by rfl⟩ : syracuseStep 791387 = 1187081) B1187081
theorem B1184975 : Blo 523799 1184975 := bstep (se 1 (by rfl) ⟨888731, by rfl⟩ : syracuseStep 1184975 = 1777463) B1777463
theorem B4035881 : Blo 523799 4035881 := bstep (se 2 (by rfl) ⟨1513455, by rfl⟩ : syracuseStep 4035881 = 3026911) B3026911
theorem B1185065 : Blo 523799 1185065 := bstep (se 2 (by rfl) ⟨444399, by rfl⟩ : syracuseStep 1185065 = 888799) B888799
theorem B4003181 : Blo 523799 4003181 := bstep (se 3 (by rfl) ⟨750596, by rfl⟩ : syracuseStep 4003181 = 1501193) B1501193
theorem B1349095 : Blo 523799 1349095 := bstep (se 1 (by rfl) ⟨1011821, by rfl⟩ : syracuseStep 1349095 = 2023643) B2023643
theorem B1185263 : Blo 523799 1185263 := bstep (se 1 (by rfl) ⟨888947, by rfl⟩ : syracuseStep 1185263 = 1777895) B1777895
theorem B3380737 : Blo 523799 3380737 := bstep (se 2 (by rfl) ⟨1267776, by rfl⟩ : syracuseStep 3380737 = 2535553) B2535553
theorem B2987603 : Blo 523799 2987603 := bstep (se 1 (by rfl) ⟨2240702, by rfl⟩ : syracuseStep 2987603 = 4481405) B4481405
theorem B1119881 : Blo 523799 1119881 := bstep (se 2 (by rfl) ⟨419955, by rfl⟩ : syracuseStep 1119881 = 839911) B839911
theorem B1119899 : Blo 523799 1119899 := bstep (se 1 (by rfl) ⟨839924, by rfl⟩ : syracuseStep 1119899 = 1679849) B1679849
theorem B4003667 : Blo 523799 4003667 := bstep (se 1 (by rfl) ⟨3002750, by rfl⟩ : syracuseStep 4003667 = 6005501) B6005501
theorem B1185659 : Blo 523799 1185659 := bstep (se 1 (by rfl) ⟨889244, by rfl⟩ : syracuseStep 1185659 = 1778489) B1778489
theorem B1775519 : Blo 523799 1775519 := bstep (se 1 (by rfl) ⟨1331639, by rfl⟩ : syracuseStep 1775519 = 2663279) B2663279
theorem B1185695 : Blo 523799 1185695 := bstep (se 1 (by rfl) ⟨889271, by rfl⟩ : syracuseStep 1185695 = 1778543) B1778543
theorem B1185929 : Blo 523799 1185929 := bstep (se 2 (by rfl) ⟨444723, by rfl⟩ : syracuseStep 1185929 = 889447) B889447
theorem B1513687 : Blo 523799 1513687 := bstep (se 1 (by rfl) ⟨1135265, by rfl⟩ : syracuseStep 1513687 = 2270531) B2270531
theorem B1186145 : Blo 523799 1186145 := bstep (se 2 (by rfl) ⟨444804, by rfl⟩ : syracuseStep 1186145 = 889609) B889609
theorem B1186235 : Blo 523799 1186235 := bstep (se 1 (by rfl) ⟨889676, by rfl⟩ : syracuseStep 1186235 = 1779353) B1779353
theorem B2529767 : Blo 523799 2529767 := bstep (se 1 (by rfl) ⟨1897325, by rfl⟩ : syracuseStep 2529767 = 3794651) B3794651
theorem B1678067 : Blo 523799 1678067 := bstep (se 1 (by rfl) ⟨1258550, by rfl⟩ : syracuseStep 1678067 = 2517101) B2517101
theorem B1186631 : Blo 523799 1186631 := bstep (se 1 (by rfl) ⟨889973, by rfl⟩ : syracuseStep 1186631 = 1779947) B1779947
theorem B1776761 : Blo 523799 1776761 := bstep (se 2 (by rfl) ⟨666285, by rfl⟩ : syracuseStep 1776761 = 1332571) B1332571
theorem B1186937 : Blo 523799 1186937 := bstep (se 2 (by rfl) ⟨445101, by rfl⟩ : syracuseStep 1186937 = 890203) B890203
theorem B1187495 : Blo 523799 1187495 := bstep (se 1 (by rfl) ⟨890621, by rfl⟩ : syracuseStep 1187495 = 1781243) B1781243
theorem B4005611 : Blo 523799 4005611 := bstep (se 1 (by rfl) ⟨3004208, by rfl⟩ : syracuseStep 4005611 = 6008417) B6008417
theorem B5742541 : Blo 523799 5742541 := bstep (se 3 (by rfl) ⟨1076726, by rfl⟩ : syracuseStep 5742541 = 2153453) B2153453
theorem B1122427 : Blo 523799 1122427 := bstep (se 1 (by rfl) ⟨841820, by rfl⟩ : syracuseStep 1122427 = 1683641) B1683641
theorem B2662631 : Blo 523799 2662631 := bstep (se 1 (by rfl) ⟨1996973, by rfl⟩ : syracuseStep 2662631 = 3993947) B3993947
theorem B2990519 : Blo 523799 2990519 := bstep (se 1 (by rfl) ⟨2242889, by rfl⟩ : syracuseStep 2990519 = 4485779) B4485779
theorem B1614599 : Blo 523799 1614599 := bstep (se 1 (by rfl) ⟨1210949, by rfl⟩ : syracuseStep 1614599 = 2421899) B2421899
theorem B2401121 : Blo 523799 2401121 := bstep (se 2 (by rfl) ⟨900420, by rfl⟩ : syracuseStep 2401121 = 1800841) B1800841
theorem B1123913 : Blo 523799 1123913 := bstep (se 2 (by rfl) ⟨421467, by rfl⟩ : syracuseStep 1123913 = 842935) B842935
theorem B2271017 : Blo 523799 2271017 := bstep (se 2 (by rfl) ⟨851631, by rfl⟩ : syracuseStep 2271017 = 1703263) B1703263
theorem B665911 : Blo 523799 665911 := bstep (se 1 (by rfl) ⟨499433, by rfl⟩ : syracuseStep 665911 = 998867) B998867
theorem B1780217 : Blo 523799 1780217 := bstep (se 2 (by rfl) ⟨667581, by rfl⟩ : syracuseStep 1780217 = 1335163) B1335163
theorem B1419859 : Blo 523799 1419859 := bstep (se 1 (by rfl) ⟨1064894, by rfl⟩ : syracuseStep 1419859 = 2129789) B2129789
theorem B2534111 : Blo 523799 2534111 := bstep (se 1 (by rfl) ⟨1900583, by rfl⟩ : syracuseStep 2534111 = 3801167) B3801167
theorem B1780487 : Blo 523799 1780487 := bstep (se 1 (by rfl) ⟨1335365, by rfl⟩ : syracuseStep 1780487 = 2670731) B2670731
theorem B1780703 : Blo 523799 1780703 := bstep (se 1 (by rfl) ⟨1335527, by rfl⟩ : syracuseStep 1780703 = 2671055) B2671055
theorem B1780865 : Blo 523799 1780865 := bstep (se 2 (by rfl) ⟨667824, by rfl⟩ : syracuseStep 1780865 = 1335649) B1335649
theorem B995321 : Blo 523799 995321 := bstep (se 2 (by rfl) ⟨373245, by rfl⟩ : syracuseStep 995321 = 746491) B746491
theorem B10072775 : Blo 523799 10072775 := bstep (se 1 (by rfl) ⟨7554581, by rfl⟩ : syracuseStep 10072775 = 15109163) B15109163
theorem B3781505 : Blo 523799 3781505 := bstep (se 2 (by rfl) ⟨1418064, by rfl⟩ : syracuseStep 3781505 = 2836129) B2836129
theorem B1684435 : Blo 523799 1684435 := bstep (se 1 (by rfl) ⟨1263326, by rfl⟩ : syracuseStep 1684435 = 2526653) B2526653
theorem B2241607 : Blo 523799 2241607 := bstep (se 1 (by rfl) ⟨1681205, by rfl⟩ : syracuseStep 2241607 = 3362411) B3362411
theorem B10073321 : Blo 523799 10073321 := bstep (se 2 (by rfl) ⟨3777495, by rfl⟩ : syracuseStep 10073321 = 7554991) B7554991
theorem B996779 : Blo 523799 996779 := bstep (se 1 (by rfl) ⟨747584, by rfl⟩ : syracuseStep 996779 = 1495169) B1495169
theorem B2995643 : Blo 523799 2995643 := bstep (se 1 (by rfl) ⟨2246732, by rfl⟩ : syracuseStep 2995643 = 4493465) B4493465
theorem B4568507 : Blo 523799 4568507 := bstep (se 1 (by rfl) ⟨3426380, by rfl⟩ : syracuseStep 4568507 = 6852761) B6852761
theorem B9221795 : Blo 523799 9221795 := bstep (se 1 (by rfl) ⟨6916346, by rfl⟩ : syracuseStep 9221795 = 13832693) B13832693
theorem B2668463 : Blo 523799 2668463 := bstep (se 1 (by rfl) ⟨2001347, by rfl⟩ : syracuseStep 2668463 = 4002695) B4002695
theorem B997447 : Blo 523799 997447 := bstep (se 1 (by rfl) ⟨748085, by rfl⟩ : syracuseStep 997447 = 1496171) B1496171
theorem B1063207 : Blo 523799 1063207 := bstep (se 1 (by rfl) ⟨797405, by rfl⟩ : syracuseStep 1063207 = 1594811) B1594811
theorem B998153 : Blo 523799 998153 := bstep (se 2 (by rfl) ⟨374307, by rfl⟩ : syracuseStep 998153 = 748615) B748615
theorem B5061689 : Blo 523799 5061689 := bstep (se 2 (by rfl) ⟨1898133, by rfl⟩ : syracuseStep 5061689 = 3796267) B3796267
theorem B1686587 : Blo 523799 1686587 := bstep (se 1 (by rfl) ⟨1264940, by rfl⟩ : syracuseStep 1686587 = 2529881) B2529881
theorem B3194099 : Blo 523799 3194099 := bstep (se 1 (by rfl) ⟨2395574, by rfl⟩ : syracuseStep 3194099 = 4791149) B4791149
theorem B1326415 : Blo 523799 1326415 := bstep (se 1 (by rfl) ⟨994811, by rfl⟩ : syracuseStep 1326415 = 1989623) B1989623
theorem B5127547 : Blo 523799 5127547 := bstep (se 1 (by rfl) ⟨3845660, by rfl⟩ : syracuseStep 5127547 = 7691321) B7691321
theorem B999611 : Blo 523799 999611 := bstep (se 1 (by rfl) ⟨749708, by rfl⟩ : syracuseStep 999611 = 1499417) B1499417
theorem B2245229 : Blo 523799 2245229 := bstep (se 3 (by rfl) ⟨420980, by rfl⟩ : syracuseStep 2245229 = 841961) B841961
theorem B1000097 : Blo 523799 1000097 := bstep (se 2 (by rfl) ⟨375036, by rfl⟩ : syracuseStep 1000097 = 750073) B750073
theorem B2671379 : Blo 523799 2671379 := bstep (se 1 (by rfl) ⟨2003534, by rfl⟩ : syracuseStep 2671379 = 4007069) B4007069
theorem B2377067 : Blo 523799 2377067 := bstep (se 1 (by rfl) ⟨1782800, by rfl⟩ : syracuseStep 2377067 = 3565601) B3565601
theorem B1329767 : Blo 523799 1329767 := bstep (se 1 (by rfl) ⟨997325, by rfl⟩ : syracuseStep 1329767 = 1994651) B1994651
theorem B4508297 : Blo 523799 4508297 := bstep (se 2 (by rfl) ⟨1690611, by rfl⟩ : syracuseStep 4508297 = 3381223) B3381223
theorem B1264423 : Blo 523799 1264423 := bstep (se 1 (by rfl) ⟨948317, by rfl⟩ : syracuseStep 1264423 = 1896635) B1896635
theorem B2739035 : Blo 523799 2739035 := bstep (se 1 (by rfl) ⟨2054276, by rfl⟩ : syracuseStep 2739035 = 4108553) B4108553
theorem B18205661 : Blo 523799 18205661 := bstep (se 3 (by rfl) ⟨3413561, by rfl⟩ : syracuseStep 18205661 = 6827123) B6827123
theorem B1919969 : Blo 523799 1919969 := bstep (se 2 (by rfl) ⟨719988, by rfl⟩ : syracuseStep 1919969 = 1439977) B1439977
theorem B2247689 : Blo 523799 2247689 := bstep (se 2 (by rfl) ⟨842883, by rfl⟩ : syracuseStep 2247689 = 1685767) B1685767
theorem B207867653 : Blo 523799 207867653 := bstep (se 4 (by rfl) ⟨19487592, by rfl⟩ : syracuseStep 207867653 = 38975185) B38975185
theorem B2248631 : Blo 523799 2248631 := bstep (se 1 (by rfl) ⟨1686473, by rfl⟩ : syracuseStep 2248631 = 3372947) B3372947
theorem B1331255 : Blo 523799 1331255 := bstep (se 1 (by rfl) ⟨998441, by rfl⟩ : syracuseStep 1331255 = 1996883) B1996883
theorem B839783 : Blo 523799 839783 := bstep (se 1 (by rfl) ⟨629837, by rfl⟩ : syracuseStep 839783 = 1259675) B1259675
theorem B1265825 : Blo 523799 1265825 := bstep (se 2 (by rfl) ⟨474684, by rfl⟩ : syracuseStep 1265825 = 949369) B949369
theorem B3002615 : Blo 523799 3002615 := bstep (se 1 (by rfl) ⟨2251961, by rfl⟩ : syracuseStep 3002615 = 4503923) B4503923
theorem B840059 : Blo 523799 840059 := bstep (se 1 (by rfl) ⟨630044, by rfl⟩ : syracuseStep 840059 = 1260089) B1260089
theorem B1331579 : Blo 523799 1331579 := bstep (se 1 (by rfl) ⟨998684, by rfl⟩ : syracuseStep 1331579 = 1997369) B1997369
theorem B10278103 : Blo 523799 10278103 := bstep (se 1 (by rfl) ⟨7708577, by rfl⟩ : syracuseStep 10278103 = 15417155) B15417155
theorem B7296551 : Blo 523799 7296551 := bstep (se 1 (by rfl) ⟨5472413, by rfl⟩ : syracuseStep 7296551 = 10944827) B10944827
theorem B17028953 : Blo 523799 17028953 := bstep (se 2 (by rfl) ⟨6385857, by rfl⟩ : syracuseStep 17028953 = 12771715) B12771715
theorem B11360249 : Blo 523799 11360249 := bstep (se 2 (by rfl) ⟨4260093, by rfl⟩ : syracuseStep 11360249 = 8520187) B8520187
theorem B2251091 : Blo 523799 2251091 := bstep (se 1 (by rfl) ⟨1688318, by rfl⟩ : syracuseStep 2251091 = 3376637) B3376637
theorem B331897175 : Blo 523799 331897175 := bstep (se 1 (by rfl) ⟨248922881, by rfl⟩ : syracuseStep 331897175 = 497845763) B497845763
theorem B18209123 : Blo 523799 18209123 := bstep (se 1 (by rfl) ⟨13656842, by rfl⟩ : syracuseStep 18209123 = 27313685) B27313685
theorem B1497503 : Blo 523799 1497503 := bstep (se 1 (by rfl) ⟨1123127, by rfl⟩ : syracuseStep 1497503 = 2246255) B2246255
theorem B6380369 : Blo 523799 6380369 := bstep (se 2 (by rfl) ⟨2392638, by rfl⟩ : syracuseStep 6380369 = 4785277) B4785277
theorem B1891183 : Blo 523799 1891183 := bstep (se 1 (by rfl) ⟨1418387, by rfl⟩ : syracuseStep 1891183 = 2836775) B2836775
theorem B4054607 : Blo 523799 4054607 := bstep (se 1 (by rfl) ⟨3040955, by rfl⟩ : syracuseStep 4054607 = 6081911) B6081911
theorem B1334951 : Blo 523799 1334951 := bstep (se 1 (by rfl) ⟨1001213, by rfl⟩ : syracuseStep 1334951 = 2002427) B2002427
theorem B1892251 : Blo 523799 1892251 := bstep (se 1 (by rfl) ⟨1419188, by rfl⟩ : syracuseStep 1892251 = 2838377) B2838377
theorem B2253055 : Blo 523799 2253055 := bstep (se 1 (by rfl) ⟨1689791, by rfl⟩ : syracuseStep 2253055 = 3379583) B3379583
theorem B17228161 : Blo 523799 17228161 := bstep (se 2 (by rfl) ⟨6460560, by rfl⟩ : syracuseStep 17228161 = 12921121) B12921121
theorem B18211331 : Blo 523799 18211331 := bstep (se 1 (by rfl) ⟨13658498, by rfl⟩ : syracuseStep 18211331 = 27316997) B27316997
theorem B5857879 : Blo 523799 5857879 := bstep (se 1 (by rfl) ⟨4393409, by rfl⟩ : syracuseStep 5857879 = 8786819) B8786819
theorem B6742763 : Blo 523799 6742763 := bstep (se 1 (by rfl) ⟨5057072, by rfl⟩ : syracuseStep 6742763 = 10114145) B10114145
theorem B1991567 : Blo 523799 1991567 := bstep (se 1 (by rfl) ⟨1493675, by rfl⟩ : syracuseStep 1991567 = 2987351) B2987351
theorem B3991031 : Blo 523799 3991031 := bstep (se 1 (by rfl) ⟨2993273, by rfl⟩ : syracuseStep 3991031 = 5986547) B5986547
theorem B1992509 : Blo 523799 1992509 := bstep (se 3 (by rfl) ⟨373595, by rfl⟩ : syracuseStep 1992509 = 747191) B747191
theorem B1993207 : Blo 523799 1993207 := bstep (se 1 (by rfl) ⟨1494905, by rfl⟩ : syracuseStep 1993207 = 2989811) B2989811
theorem B10120139 : Blo 523799 10120139 := bstep (se 1 (by rfl) ⟨7590104, by rfl⟩ : syracuseStep 10120139 = 15180209) B15180209
theorem B1994179 : Blo 523799 1994179 := bstep (se 1 (by rfl) ⟨1495634, by rfl⟩ : syracuseStep 1994179 = 2991269) B2991269
theorem B1502675 : Blo 523799 1502675 := bstep (se 1 (by rfl) ⟨1127006, by rfl⟩ : syracuseStep 1502675 = 2254013) B2254013
theorem B7303085 : Blo 523799 7303085 := bstep (se 3 (by rfl) ⟨1369328, by rfl⟩ : syracuseStep 7303085 = 2738657) B2738657
theorem B1994939 : Blo 523799 1994939 := bstep (se 1 (by rfl) ⟨1496204, by rfl⟩ : syracuseStep 1994939 = 2992409) B2992409
theorem B4485401 : Blo 523799 4485401 := bstep (se 2 (by rfl) ⟨1682025, by rfl⟩ : syracuseStep 4485401 = 3364051) B3364051
theorem B2126189 : Blo 523799 2126189 := bstep (se 3 (by rfl) ⟨398660, by rfl⟩ : syracuseStep 2126189 = 797321) B797321
theorem B2519869 : Blo 523799 2519869 := bstep (se 3 (by rfl) ⟨472475, by rfl⟩ : syracuseStep 2519869 = 944951) B944951
theorem B1996123 : Blo 523799 1996123 := bstep (se 1 (by rfl) ⟨1497092, by rfl⟩ : syracuseStep 1996123 = 2994185) B2994185
theorem B1701287 : Blo 523799 1701287 := bstep (se 1 (by rfl) ⟨1275965, by rfl⟩ : syracuseStep 1701287 = 2551931) B2551931
theorem B7272337 : Blo 523799 7272337 := bstep (se 2 (by rfl) ⟨2727126, by rfl⟩ : syracuseStep 7272337 = 5454253) B5454253
theorem B7698341 : Blo 523799 7698341 := bstep (se 4 (by rfl) ⟨721719, by rfl⟩ : syracuseStep 7698341 = 1443439) B1443439
theorem B2849231 : Blo 523799 2849231 := bstep (se 1 (by rfl) ⟨2136923, by rfl⟩ : syracuseStep 2849231 = 4273847) B4273847
theorem B1767905 : Blo 523799 1767905 := bstep (se 2 (by rfl) ⟨662964, by rfl⟩ : syracuseStep 1767905 = 1325929) B1325929
theorem B3045919 : Blo 523799 3045919 := bstep (se 1 (by rfl) ⟨2284439, by rfl⟩ : syracuseStep 3045919 = 4568879) B4568879
theorem B2128475 : Blo 523799 2128475 := bstep (se 1 (by rfl) ⟨1596356, by rfl⟩ : syracuseStep 2128475 = 3192713) B3192713
theorem B2456477 : Blo 523799 2456477 := bstep (se 3 (by rfl) ⟨460589, by rfl⟩ : syracuseStep 2456477 = 921179) B921179
theorem B1178729 : Blo 523799 1178729 := bstep (se 2 (by rfl) ⟨442023, by rfl⟩ : syracuseStep 1178729 = 884047) B884047
theorem B1178855 : Blo 523799 1178855 := bstep (se 1 (by rfl) ⟨884141, by rfl⟩ : syracuseStep 1178855 = 1768283) B1768283
theorem B523887 : Blo 523799 523887 := bstep (se 1 (by rfl) ⟨392915, by rfl⟩ : syracuseStep 523887 = 785831) B785831
theorem B589423 : Blo 523799 589423 := bstep (se 1 (by rfl) ⟨442067, by rfl⟩ : syracuseStep 589423 = 884135) B884135
theorem B523943 : Blo 523799 523943 := bstep (se 1 (by rfl) ⟨392957, by rfl⟩ : syracuseStep 523943 = 785915) B785915
theorem B589531 : Blo 523799 589531 := bstep (se 1 (by rfl) ⟨442148, by rfl⟩ : syracuseStep 589531 = 884297) B884297
theorem B786143 : Blo 523799 786143 := bstep (se 1 (by rfl) ⟨589607, by rfl⟩ : syracuseStep 786143 = 1179215) B1179215
theorem B1179359 : Blo 523799 1179359 := bstep (se 1 (by rfl) ⟨884519, by rfl⟩ : syracuseStep 1179359 = 1769039) B1769039
theorem B524007 : Blo 523799 524007 := bstep (se 1 (by rfl) ⟨393005, by rfl⟩ : syracuseStep 524007 = 786011) B786011
theorem B786185 : Blo 523799 786185 := bstep (se 2 (by rfl) ⟨294819, by rfl⟩ : syracuseStep 786185 = 589639) B589639
theorem B524063 : Blo 523799 524063 := bstep (se 1 (by rfl) ⟨393047, by rfl⟩ : syracuseStep 524063 = 786095) B786095
theorem B1769255 : Blo 523799 1769255 := bstep (se 1 (by rfl) ⟨1326941, by rfl⟩ : syracuseStep 1769255 = 2653883) B2653883
theorem B1179431 : Blo 523799 1179431 := bstep (se 1 (by rfl) ⟨884573, by rfl⟩ : syracuseStep 1179431 = 1769147) B1769147
theorem B1081127 : Blo 523799 1081127 := bstep (se 1 (by rfl) ⟨810845, by rfl⟩ : syracuseStep 1081127 = 1621691) B1621691
theorem B524143 : Blo 523799 524143 := bstep (se 1 (by rfl) ⟨393107, by rfl⟩ : syracuseStep 524143 = 786215) B786215
theorem B524199 : Blo 523799 524199 := bstep (se 1 (by rfl) ⟨393149, by rfl⟩ : syracuseStep 524199 = 786299) B786299
theorem B4849787 : Blo 523799 4849787 := bstep (se 1 (by rfl) ⟨3637340, by rfl⟩ : syracuseStep 4849787 = 7274681) B7274681
theorem B524415 : Blo 523799 524415 := bstep (se 1 (by rfl) ⟨393311, by rfl⟩ : syracuseStep 524415 = 786623) B786623
theorem B524699 : Blo 523799 524699 := bstep (se 1 (by rfl) ⟨393524, by rfl⟩ : syracuseStep 524699 = 787049) B787049
theorem B524703 : Blo 523799 524703 := bstep (se 1 (by rfl) ⟨393527, by rfl⟩ : syracuseStep 524703 = 787055) B787055
theorem B3375533 : Blo 523799 3375533 := bstep (se 3 (by rfl) ⟨632912, by rfl⟩ : syracuseStep 3375533 = 1265825) B1265825
theorem B22970881 : Blo 523799 22970881 := bstep (se 2 (by rfl) ⟨8614080, by rfl⟩ : syracuseStep 22970881 = 17228161) B17228161
theorem B786971 : Blo 523799 786971 := bstep (se 1 (by rfl) ⟨590228, by rfl⟩ : syracuseStep 786971 = 1180457) B1180457
theorem B787151 : Blo 523799 787151 := bstep (se 1 (by rfl) ⟨590363, by rfl⟩ : syracuseStep 787151 = 1180727) B1180727
theorem B15205117 : Blo 523799 15205117 := bstep (se 3 (by rfl) ⟨2850959, by rfl⟩ : syracuseStep 15205117 = 5701919) B5701919
theorem B525119 : Blo 523799 525119 := bstep (se 1 (by rfl) ⟨393839, by rfl⟩ : syracuseStep 525119 = 787679) B787679
theorem B787271 : Blo 523799 787271 := bstep (se 1 (by rfl) ⟨590453, by rfl⟩ : syracuseStep 787271 = 1180907) B1180907
theorem B525127 : Blo 523799 525127 := bstep (se 1 (by rfl) ⟨393845, by rfl⟩ : syracuseStep 525127 = 787691) B787691
theorem B787337 : Blo 523799 787337 := bstep (se 2 (by rfl) ⟨295251, by rfl⟩ : syracuseStep 787337 = 590503) B590503
theorem B1770551 : Blo 523799 1770551 := bstep (se 1 (by rfl) ⟨1327913, by rfl⟩ : syracuseStep 1770551 = 2655827) B2655827
theorem B525383 : Blo 523799 525383 := bstep (se 1 (by rfl) ⟨394037, by rfl⟩ : syracuseStep 525383 = 788075) B788075
theorem B1180799 : Blo 523799 1180799 := bstep (se 1 (by rfl) ⟨885599, by rfl⟩ : syracuseStep 1180799 = 1771199) B1771199
theorem B787583 : Blo 523799 787583 := bstep (se 1 (by rfl) ⟨590687, by rfl⟩ : syracuseStep 787583 = 1181375) B1181375
theorem B525439 : Blo 523799 525439 := bstep (se 1 (by rfl) ⟨394079, by rfl⟩ : syracuseStep 525439 = 788159) B788159
theorem B525563 : Blo 523799 525563 := bstep (se 1 (by rfl) ⟨394172, by rfl⟩ : syracuseStep 525563 = 788345) B788345
theorem B787721 : Blo 523799 787721 := bstep (se 2 (by rfl) ⟨295395, by rfl⟩ : syracuseStep 787721 = 590791) B590791
theorem B788201 : Blo 523799 788201 := bstep (se 2 (by rfl) ⟨295575, by rfl⟩ : syracuseStep 788201 = 591151) B591151
theorem B526063 : Blo 523799 526063 := bstep (se 1 (by rfl) ⟨394547, by rfl⟩ : syracuseStep 526063 = 789095) B789095
theorem B886511 : Blo 523799 886511 := bstep (se 1 (by rfl) ⟨664883, by rfl⟩ : syracuseStep 886511 = 1329767) B1329767
theorem B788207 : Blo 523799 788207 := bstep (se 1 (by rfl) ⟨591155, by rfl⟩ : syracuseStep 788207 = 1182311) B1182311
theorem B591727 : Blo 523799 591727 := bstep (se 1 (by rfl) ⟨443795, by rfl⟩ : syracuseStep 591727 = 887591) B887591
theorem B526191 : Blo 523799 526191 := bstep (se 1 (by rfl) ⟨394643, by rfl⟩ : syracuseStep 526191 = 789287) B789287
theorem B1279979 : Blo 523799 1279979 := bstep (se 1 (by rfl) ⟨959984, by rfl⟩ : syracuseStep 1279979 = 1919969) B1919969
theorem B788459 : Blo 523799 788459 := bstep (se 1 (by rfl) ⟨591344, by rfl⟩ : syracuseStep 788459 = 1182689) B1182689
theorem B591943 : Blo 523799 591943 := bstep (se 1 (by rfl) ⟨443957, by rfl⟩ : syracuseStep 591943 = 887915) B887915
theorem B526407 : Blo 523799 526407 := bstep (se 1 (by rfl) ⟨394805, by rfl⟩ : syracuseStep 526407 = 789611) B789611
theorem B788711 : Blo 523799 788711 := bstep (se 1 (by rfl) ⟨591533, by rfl⟩ : syracuseStep 788711 = 1183067) B1183067
theorem B526567 : Blo 523799 526567 := bstep (se 1 (by rfl) ⟨394925, by rfl⟩ : syracuseStep 526567 = 789851) B789851
theorem B592123 : Blo 523799 592123 := bstep (se 1 (by rfl) ⟨444092, by rfl⟩ : syracuseStep 592123 = 888185) B888185
theorem B526587 : Blo 523799 526587 := bstep (se 1 (by rfl) ⟨394940, by rfl⟩ : syracuseStep 526587 = 789881) B789881
theorem B1181951 : Blo 523799 1181951 := bstep (se 1 (by rfl) ⟨886463, by rfl⟩ : syracuseStep 1181951 = 1772927) B1772927
theorem B788735 : Blo 523799 788735 := bstep (se 1 (by rfl) ⟨591551, by rfl⟩ : syracuseStep 788735 = 1183103) B1183103
theorem B526591 : Blo 523799 526591 := bstep (se 1 (by rfl) ⟨394943, by rfl⟩ : syracuseStep 526591 = 789887) B789887
theorem B788873 : Blo 523799 788873 := bstep (se 2 (by rfl) ⟨295827, by rfl⟩ : syracuseStep 788873 = 591655) B591655
theorem B138578435 : Blo 523799 138578435 := bstep (se 1 (by rfl) ⟨103933826, by rfl⟩ : syracuseStep 138578435 = 207867653) B207867653
theorem B527007 : Blo 523799 527007 := bstep (se 1 (by rfl) ⟨395255, by rfl⟩ : syracuseStep 527007 = 790511) B790511
theorem B527015 : Blo 523799 527015 := bstep (se 1 (by rfl) ⟨395261, by rfl⟩ : syracuseStep 527015 = 790523) B790523
theorem B887503 : Blo 523799 887503 := bstep (se 1 (by rfl) ⟨665627, by rfl⟩ : syracuseStep 887503 = 1331255) B1331255
theorem B592591 : Blo 523799 592591 := bstep (se 1 (by rfl) ⟨444443, by rfl⟩ : syracuseStep 592591 = 888887) B888887
theorem B527055 : Blo 523799 527055 := bstep (se 1 (by rfl) ⟨395291, by rfl⟩ : syracuseStep 527055 = 790583) B790583
theorem B559855 : Blo 523799 559855 := bstep (se 1 (by rfl) ⟨419891, by rfl⟩ : syracuseStep 559855 = 839783) B839783
theorem B527087 : Blo 523799 527087 := bstep (se 1 (by rfl) ⟨395315, by rfl⟩ : syracuseStep 527087 = 790631) B790631
theorem B527135 : Blo 523799 527135 := bstep (se 1 (by rfl) ⟨395351, by rfl⟩ : syracuseStep 527135 = 790703) B790703
theorem B2001743 : Blo 523799 2001743 := bstep (se 1 (by rfl) ⟨1501307, by rfl⟩ : syracuseStep 2001743 = 3002615) B3002615
theorem B560039 : Blo 523799 560039 := bstep (se 1 (by rfl) ⟨420029, by rfl⟩ : syracuseStep 560039 = 840059) B840059
theorem B887719 : Blo 523799 887719 := bstep (se 1 (by rfl) ⟨665789, by rfl⟩ : syracuseStep 887719 = 1331579) B1331579
theorem B592807 : Blo 523799 592807 := bstep (se 1 (by rfl) ⟨444605, by rfl⟩ : syracuseStep 592807 = 889211) B889211
theorem B527271 : Blo 523799 527271 := bstep (se 1 (by rfl) ⟨395453, by rfl⟩ : syracuseStep 527271 = 790907) B790907
theorem B887881 : Blo 523799 887881 := bstep (se 2 (by rfl) ⟨332955, by rfl⟩ : syracuseStep 887881 = 665911) B665911
theorem B592987 : Blo 523799 592987 := bstep (se 1 (by rfl) ⟨444740, by rfl⟩ : syracuseStep 592987 = 889481) B889481
theorem B527451 : Blo 523799 527451 := bstep (se 1 (by rfl) ⟨395588, by rfl⟩ : syracuseStep 527451 = 791177) B791177
theorem B527591 : Blo 523799 527591 := bstep (se 1 (by rfl) ⟨395693, by rfl⟩ : syracuseStep 527591 = 791387) B791387
theorem B2657609 : Blo 523799 2657609 := bstep (se 2 (by rfl) ⟨996603, by rfl⟩ : syracuseStep 2657609 = 1993207) B1993207
theorem B789983 : Blo 523799 789983 := bstep (se 1 (by rfl) ⟨592487, by rfl⟩ : syracuseStep 789983 = 1184975) B1184975
theorem B2690587 : Blo 523799 2690587 := bstep (se 1 (by rfl) ⟨2017940, by rfl⟩ : syracuseStep 2690587 = 4035881) B4035881
theorem B790043 : Blo 523799 790043 := bstep (se 1 (by rfl) ⟨592532, by rfl⟩ : syracuseStep 790043 = 1185065) B1185065
theorem B790175 : Blo 523799 790175 := bstep (se 1 (by rfl) ⟨592631, by rfl⟩ : syracuseStep 790175 = 1185263) B1185263
theorem B790439 : Blo 523799 790439 := bstep (se 1 (by rfl) ⟨592829, by rfl⟩ : syracuseStep 790439 = 1185659) B1185659
theorem B1183679 : Blo 523799 1183679 := bstep (se 1 (by rfl) ⟨887759, by rfl⟩ : syracuseStep 1183679 = 1775519) B1775519
theorem B790463 : Blo 523799 790463 := bstep (se 1 (by rfl) ⟨592847, by rfl⟩ : syracuseStep 790463 = 1185695) B1185695
theorem B7573499 : Blo 523799 7573499 := bstep (se 1 (by rfl) ⟨5680124, by rfl⟩ : syracuseStep 7573499 = 11360249) B11360249
theorem B790619 : Blo 523799 790619 := bstep (se 1 (by rfl) ⟨592964, by rfl⟩ : syracuseStep 790619 = 1185929) B1185929
theorem B790763 : Blo 523799 790763 := bstep (se 1 (by rfl) ⟨593072, by rfl⟩ : syracuseStep 790763 = 1186145) B1186145
theorem B790823 : Blo 523799 790823 := bstep (se 1 (by rfl) ⟨593117, by rfl⟩ : syracuseStep 790823 = 1186235) B1186235
theorem B1118711 : Blo 523799 1118711 := bstep (se 1 (by rfl) ⟨839033, by rfl⟩ : syracuseStep 1118711 = 1678067) B1678067
theorem B791087 : Blo 523799 791087 := bstep (se 1 (by rfl) ⟨593315, by rfl⟩ : syracuseStep 791087 = 1186631) B1186631
theorem B2658905 : Blo 523799 2658905 := bstep (se 2 (by rfl) ⟨997089, by rfl⟩ : syracuseStep 2658905 = 1994179) B1994179
theorem B1184507 : Blo 523799 1184507 := bstep (se 1 (by rfl) ⟨888380, by rfl⟩ : syracuseStep 1184507 = 1776761) B1776761
theorem B791291 : Blo 523799 791291 := bstep (se 1 (by rfl) ⟨593468, by rfl⟩ : syracuseStep 791291 = 1186937) B1186937
theorem B889967 : Blo 523799 889967 := bstep (se 1 (by rfl) ⟨667475, by rfl⟩ : syracuseStep 889967 = 1334951) B1334951
theorem B791663 : Blo 523799 791663 := bstep (se 1 (by rfl) ⟨593747, by rfl⟩ : syracuseStep 791663 = 1187495) B1187495
theorem B1775087 : Blo 523799 1775087 := bstep (se 1 (by rfl) ⟨1331315, by rfl⟩ : syracuseStep 1775087 = 2662631) B2662631
theorem B4495175 : Blo 523799 4495175 := bstep (se 1 (by rfl) ⟨3371381, by rfl⟩ : syracuseStep 4495175 = 6742763) B6742763
theorem B2660687 : Blo 523799 2660687 := bstep (se 1 (by rfl) ⟨1995515, by rfl⟩ : syracuseStep 2660687 = 3991031) B3991031
theorem B2988809 : Blo 523799 2988809 := bstep (se 2 (by rfl) ⟨1120803, by rfl⟩ : syracuseStep 2988809 = 2241607) B2241607
theorem B5675933 : Blo 523799 5675933 := bstep (se 3 (by rfl) ⟨1064237, by rfl⟩ : syracuseStep 5675933 = 2128475) B2128475
theorem B13704137 : Blo 523799 13704137 := bstep (se 2 (by rfl) ⟨5139051, by rfl⟩ : syracuseStep 13704137 = 10278103) B10278103
theorem B1186811 : Blo 523799 1186811 := bstep (se 1 (by rfl) ⟨890108, by rfl⟩ : syracuseStep 1186811 = 1780217) B1780217
theorem B2661497 : Blo 523799 2661497 := bstep (se 2 (by rfl) ⟨998061, by rfl⟩ : syracuseStep 2661497 = 1996123) B1996123
theorem B1186991 : Blo 523799 1186991 := bstep (se 1 (by rfl) ⟨890243, by rfl⟩ : syracuseStep 1186991 = 1780487) B1780487
theorem B1187135 : Blo 523799 1187135 := bstep (se 1 (by rfl) ⟨890351, by rfl⟩ : syracuseStep 1187135 = 1780703) B1780703
theorem B1187243 : Blo 523799 1187243 := bstep (se 1 (by rfl) ⟨890432, by rfl⟩ : syracuseStep 1187243 = 1780865) B1780865
theorem B663547 : Blo 523799 663547 := bstep (se 1 (by rfl) ⟨497660, by rfl⟩ : syracuseStep 663547 = 995321) B995321
theorem B4497565 : Blo 523799 4497565 := bstep (se 3 (by rfl) ⟨843293, by rfl⟩ : syracuseStep 4497565 = 1686587) B1686587
theorem B2990267 : Blo 523799 2990267 := bstep (se 1 (by rfl) ⟨2242700, by rfl⟩ : syracuseStep 2990267 = 4485401) B4485401
theorem B1417459 : Blo 523799 1417459 := bstep (se 1 (by rfl) ⟨1063094, by rfl⟩ : syracuseStep 1417459 = 2126189) B2126189
theorem B1417609 : Blo 523799 1417609 := bstep (se 2 (by rfl) ⟨531603, by rfl⟩ : syracuseStep 1417609 = 1063207) B1063207
theorem B664519 : Blo 523799 664519 := bstep (se 1 (by rfl) ⟨498389, by rfl⟩ : syracuseStep 664519 = 996779) B996779
theorem B1778975 : Blo 523799 1778975 := bstep (se 1 (by rfl) ⟨1334231, by rfl⟩ : syracuseStep 1778975 = 2668463) B2668463
theorem B77899573 : Blo 523799 77899573 := bstep (se 5 (by rfl) ⟨3651542, by rfl⟩ : syracuseStep 77899573 = 7303085) B7303085
theorem B665435 : Blo 523799 665435 := bstep (se 1 (by rfl) ⟨499076, by rfl⟩ : syracuseStep 665435 = 998153) B998153
theorem B666407 : Blo 523799 666407 := bstep (se 1 (by rfl) ⟨499805, by rfl⟩ : syracuseStep 666407 = 999611) B999611
theorem B666731 : Blo 523799 666731 := bstep (se 1 (by rfl) ⟨500048, by rfl⟩ : syracuseStep 666731 = 1000097) B1000097
theorem B1780919 : Blo 523799 1780919 := bstep (se 1 (by rfl) ⟨1335689, by rfl⟩ : syracuseStep 1780919 = 2671379) B2671379
theorem B7810505 : Blo 523799 7810505 := bstep (se 2 (by rfl) ⟨2928939, by rfl⟩ : syracuseStep 7810505 = 5857879) B5857879
theorem B2993867 : Blo 523799 2993867 := bstep (se 1 (by rfl) ⟨2245400, by rfl⟩ : syracuseStep 2993867 = 4490801) B4490801
theorem B3124939 : Blo 523799 3124939 := bstep (se 1 (by rfl) ⟨2343704, by rfl⟩ : syracuseStep 3124939 = 4687409) B4687409
theorem B6402989 : Blo 523799 6402989 := bstep (se 3 (by rfl) ⟨1200560, by rfl⟩ : syracuseStep 6402989 = 2401121) B2401121
theorem B3192539 : Blo 523799 3192539 := bstep (se 1 (by rfl) ⟨2394404, by rfl⟩ : syracuseStep 3192539 = 4788809) B4788809
theorem B2668787 : Blo 523799 2668787 := bstep (se 1 (by rfl) ⟨2001590, by rfl⟩ : syracuseStep 2668787 = 4003181) B4003181
theorem B6338845 : Blo 523799 6338845 := bstep (se 3 (by rfl) ⟨1188533, by rfl⟩ : syracuseStep 6338845 = 2377067) B2377067
theorem B4864367 : Blo 523799 4864367 := bstep (se 1 (by rfl) ⟨3648275, by rfl⟩ : syracuseStep 4864367 = 7296551) B7296551
theorem B1685897 : Blo 523799 1685897 := bstep (se 2 (by rfl) ⟨632211, by rfl⟩ : syracuseStep 1685897 = 1264423) B1264423
theorem B2669111 : Blo 523799 2669111 := bstep (se 1 (by rfl) ⟨2001833, by rfl⟩ : syracuseStep 2669111 = 4003667) B4003667
theorem B11352635 : Blo 523799 11352635 := bstep (se 1 (by rfl) ⟨8514476, by rfl⟩ : syracuseStep 11352635 = 17028953) B17028953
theorem B2997101 : Blo 523799 2997101 := bstep (se 3 (by rfl) ⟨561956, by rfl⟩ : syracuseStep 2997101 = 1123913) B1123913
theorem B221264783 : Blo 523799 221264783 := bstep (se 1 (by rfl) ⟨165948587, by rfl⟩ : syracuseStep 221264783 = 331897175) B331897175
theorem B12139415 : Blo 523799 12139415 := bstep (se 1 (by rfl) ⟨9104561, by rfl⟩ : syracuseStep 12139415 = 18209123) B18209123
theorem B998335 : Blo 523799 998335 := bstep (se 1 (by rfl) ⟨748751, by rfl⟩ : syracuseStep 998335 = 1497503) B1497503
theorem B1686511 : Blo 523799 1686511 := bstep (se 1 (by rfl) ⟨1264883, by rfl⟩ : syracuseStep 1686511 = 2529767) B2529767
theorem B2703071 : Blo 523799 2703071 := bstep (se 1 (by rfl) ⟨2027303, by rfl⟩ : syracuseStep 2703071 = 4054607) B4054607
theorem B20528909 : Blo 523799 20528909 := bstep (se 3 (by rfl) ⟨3849170, by rfl⟩ : syracuseStep 20528909 = 7698341) B7698341
theorem B2670407 : Blo 523799 2670407 := bstep (se 1 (by rfl) ⟨2002805, by rfl⟩ : syracuseStep 2670407 = 4005611) B4005611
theorem B2670569 : Blo 523799 2670569 := bstep (se 2 (by rfl) ⟨1001463, by rfl⟩ : syracuseStep 2670569 = 2002927) B2002927
theorem B12140887 : Blo 523799 12140887 := bstep (se 1 (by rfl) ⟨9105665, by rfl⟩ : syracuseStep 12140887 = 18211331) B18211331
theorem B1327711 : Blo 523799 1327711 := bstep (se 1 (by rfl) ⟨995783, by rfl⟩ : syracuseStep 1327711 = 1991567) B1991567
theorem B3359825 : Blo 523799 3359825 := bstep (se 2 (by rfl) ⟨1259934, by rfl⟩ : syracuseStep 3359825 = 2519869) B2519869
theorem B1328339 : Blo 523799 1328339 := bstep (se 1 (by rfl) ⟨996254, by rfl⟩ : syracuseStep 1328339 = 1992509) B1992509
theorem B2245913 : Blo 523799 2245913 := bstep (se 2 (by rfl) ⟨842217, by rfl⟩ : syracuseStep 2245913 = 1684435) B1684435
theorem B1689407 : Blo 523799 1689407 := bstep (se 1 (by rfl) ⟨1267055, by rfl⟩ : syracuseStep 1689407 = 2534111) B2534111
theorem B4507649 : Blo 523799 4507649 := bstep (se 2 (by rfl) ⟨1690368, by rfl⟩ : syracuseStep 4507649 = 3380737) B3380737
theorem B1001783 : Blo 523799 1001783 := bstep (se 1 (by rfl) ⟨751337, by rfl⟩ : syracuseStep 1001783 = 1502675) B1502675
theorem B48548429 : Blo 523799 48548429 := bstep (se 3 (by rfl) ⟨9102830, by rfl⟩ : syracuseStep 48548429 = 18205661) B18205661
theorem B1329929 : Blo 523799 1329929 := bstep (se 2 (by rfl) ⟨498723, by rfl⟩ : syracuseStep 1329929 = 997447) B997447
theorem B1329959 : Blo 523799 1329959 := bstep (se 1 (by rfl) ⟨997469, by rfl⟩ : syracuseStep 1329959 = 1994939) B1994939
theorem B2018249 : Blo 523799 2018249 := bstep (se 2 (by rfl) ⟨756843, by rfl⟩ : syracuseStep 2018249 = 1513687) B1513687
theorem B1134191 : Blo 523799 1134191 := bstep (se 1 (by rfl) ⟨850643, by rfl⟩ : syracuseStep 1134191 = 1701287) B1701287
theorem B6147863 : Blo 523799 6147863 := bstep (se 1 (by rfl) ⟨4610897, by rfl⟩ : syracuseStep 6147863 = 9221795) B9221795
theorem B6836729 : Blo 523799 6836729 := bstep (se 2 (by rfl) ⟨2563773, by rfl⟩ : syracuseStep 6836729 = 5127547) B5127547
theorem B30626885 : Blo 523799 30626885 := bstep (se 4 (by rfl) ⟨2871270, by rfl⟩ : syracuseStep 30626885 = 5742541) B5742541
theorem B1496569 : Blo 523799 1496569 := bstep (se 2 (by rfl) ⟨561213, by rfl⟩ : syracuseStep 1496569 = 1122427) B1122427
theorem B3004073 : Blo 523799 3004073 := bstep (se 2 (by rfl) ⟨1126527, by rfl⟩ : syracuseStep 3004073 = 2253055) B2253055
theorem B1496819 : Blo 523799 1496819 := bstep (se 1 (by rfl) ⟨1122614, by rfl⟩ : syracuseStep 1496819 = 2245229) B2245229
theorem B3365383 : Blo 523799 3365383 := bstep (se 1 (by rfl) ⟨2524037, by rfl⟩ : syracuseStep 3365383 = 5048075) B5048075
theorem B3005531 : Blo 523799 3005531 := bstep (se 1 (by rfl) ⟨2254148, by rfl⟩ : syracuseStep 3005531 = 4508297) B4508297
theorem B1826023 : Blo 523799 1826023 := bstep (se 1 (by rfl) ⟨1369517, by rfl⟩ : syracuseStep 1826023 = 2739035) B2739035
theorem B1499087 : Blo 523799 1499087 := bstep (se 1 (by rfl) ⟨1124315, by rfl⟩ : syracuseStep 1499087 = 2248631) B2248631
theorem B1990763 : Blo 523799 1990763 := bstep (se 1 (by rfl) ⟨1493072, by rfl⟩ : syracuseStep 1990763 = 2986145) B2986145
theorem B6054011 : Blo 523799 6054011 := bstep (se 1 (by rfl) ⟨4540508, by rfl⟩ : syracuseStep 6054011 = 9081017) B9081017
theorem B1335487 : Blo 523799 1335487 := bstep (se 1 (by rfl) ⟨1001615, by rfl⟩ : syracuseStep 1335487 = 2003231) B2003231
theorem B1893145 : Blo 523799 1893145 := bstep (se 2 (by rfl) ⟨709929, by rfl⟩ : syracuseStep 1893145 = 1419859) B1419859
theorem B1991735 : Blo 523799 1991735 := bstep (se 1 (by rfl) ⟨1493801, by rfl⟩ : syracuseStep 1991735 = 2987603) B2987603
theorem B746587 : Blo 523799 746587 := bstep (se 1 (by rfl) ⟨559940, by rfl⟩ : syracuseStep 746587 = 1119881) B1119881
theorem B746599 : Blo 523799 746599 := bstep (se 1 (by rfl) ⟨559949, by rfl⟩ : syracuseStep 746599 = 1119899) B1119899
theorem B1500727 : Blo 523799 1500727 := bstep (se 1 (by rfl) ⟨1125545, by rfl⟩ : syracuseStep 1500727 = 2251091) B2251091
theorem B4253579 : Blo 523799 4253579 := bstep (se 1 (by rfl) ⟨3190184, by rfl⟩ : syracuseStep 4253579 = 6380369) B6380369
theorem B6056045 : Blo 523799 6056045 := bstep (se 3 (by rfl) ⟨1135508, by rfl⟩ : syracuseStep 6056045 = 2271017) B2271017
theorem B1993679 : Blo 523799 1993679 := bstep (se 1 (by rfl) ⟨1495259, by rfl⟩ : syracuseStep 1993679 = 2990519) B2990519
theorem B1076399 : Blo 523799 1076399 := bstep (se 1 (by rfl) ⟨807299, by rfl⟩ : syracuseStep 1076399 = 1614599) B1614599
theorem B6746759 : Blo 523799 6746759 := bstep (se 1 (by rfl) ⟨5060069, by rfl⟩ : syracuseStep 6746759 = 10120139) B10120139
theorem B1798793 : Blo 523799 1798793 := bstep (se 2 (by rfl) ⟨674547, by rfl⟩ : syracuseStep 1798793 = 1349095) B1349095
theorem B9696449 : Blo 523799 9696449 := bstep (se 2 (by rfl) ⟨3636168, by rfl⟩ : syracuseStep 9696449 = 7272337) B7272337
theorem B5993837 : Blo 523799 5993837 := bstep (se 3 (by rfl) ⟨1123844, by rfl⟩ : syracuseStep 5993837 = 2247689) B2247689
theorem B6715183 : Blo 523799 6715183 := bstep (se 1 (by rfl) ⟨5036387, by rfl⟩ : syracuseStep 6715183 = 10072775) B10072775
theorem B2521003 : Blo 523799 2521003 := bstep (se 1 (by rfl) ⟨1890752, by rfl⟩ : syracuseStep 2521003 = 3781505) B3781505
theorem B4061225 : Blo 523799 4061225 := bstep (se 2 (by rfl) ⟨1522959, by rfl⟩ : syracuseStep 4061225 = 3045919) B3045919
theorem B6715547 : Blo 523799 6715547 := bstep (se 1 (by rfl) ⟨5036660, by rfl⟩ : syracuseStep 6715547 = 10073321) B10073321
theorem B1997095 : Blo 523799 1997095 := bstep (se 1 (by rfl) ⟨1497821, by rfl⟩ : syracuseStep 1997095 = 2995643) B2995643
theorem B3045671 : Blo 523799 3045671 := bstep (se 1 (by rfl) ⟨2284253, by rfl⟩ : syracuseStep 3045671 = 4568507) B4568507
theorem B2521577 : Blo 523799 2521577 := bstep (se 2 (by rfl) ⟨945591, by rfl⟩ : syracuseStep 2521577 = 1891183) B1891183
theorem B1899487 : Blo 523799 1899487 := bstep (se 1 (by rfl) ⟨1424615, by rfl⟩ : syracuseStep 1899487 = 2849231) B2849231
theorem B1178603 : Blo 523799 1178603 := bstep (se 1 (by rfl) ⟨883952, by rfl⟩ : syracuseStep 1178603 = 1767905) B1767905
theorem B1768553 : Blo 523799 1768553 := bstep (se 2 (by rfl) ⟨663207, by rfl⟩ : syracuseStep 1768553 = 1326415) B1326415
theorem B1637651 : Blo 523799 1637651 := bstep (se 1 (by rfl) ⟨1228238, by rfl⟩ : syracuseStep 1637651 = 2456477) B2456477
theorem B3374459 : Blo 523799 3374459 := bstep (se 1 (by rfl) ⟨2530844, by rfl⟩ : syracuseStep 3374459 = 5061689) B5061689
theorem B785819 : Blo 523799 785819 := bstep (se 1 (by rfl) ⟨589364, by rfl⟩ : syracuseStep 785819 = 1178729) B1178729
theorem B785897 : Blo 523799 785897 := bstep (se 2 (by rfl) ⟨294711, by rfl⟩ : syracuseStep 785897 = 589423) B589423
theorem B785903 : Blo 523799 785903 := bstep (se 1 (by rfl) ⟨589427, by rfl⟩ : syracuseStep 785903 = 1178855) B1178855
theorem B2129399 : Blo 523799 2129399 := bstep (se 1 (by rfl) ⟨1597049, by rfl⟩ : syracuseStep 2129399 = 3194099) B3194099
theorem B786041 : Blo 523799 786041 := bstep (se 2 (by rfl) ⟨294765, by rfl⟩ : syracuseStep 786041 = 589531) B589531
theorem B524095 : Blo 523799 524095 := bstep (se 1 (by rfl) ⟨393071, by rfl⟩ : syracuseStep 524095 = 786143) B786143
theorem B786239 : Blo 523799 786239 := bstep (se 1 (by rfl) ⟨589679, by rfl⟩ : syracuseStep 786239 = 1179359) B1179359
theorem B524123 : Blo 523799 524123 := bstep (se 1 (by rfl) ⟨393092, by rfl⟩ : syracuseStep 524123 = 786185) B786185
theorem B786287 : Blo 523799 786287 := bstep (se 1 (by rfl) ⟨589715, by rfl⟩ : syracuseStep 786287 = 1179431) B1179431
theorem B1179503 : Blo 523799 1179503 := bstep (se 1 (by rfl) ⟨884627, by rfl⟩ : syracuseStep 1179503 = 1769255) B1769255
theorem B720751 : Blo 523799 720751 := bstep (se 1 (by rfl) ⟨540563, by rfl⟩ : syracuseStep 720751 = 1081127) B1081127
theorem B2523001 : Blo 523799 2523001 := bstep (se 2 (by rfl) ⟨946125, by rfl⟩ : syracuseStep 2523001 = 1892251) B1892251
theorem B5996753 : Blo 523799 5996753 := bstep (se 2 (by rfl) ⟨2248782, by rfl⟩ : syracuseStep 5996753 = 4497565) B4497565
theorem B524647 : Blo 523799 524647 := bstep (se 1 (by rfl) ⟨393485, by rfl⟩ : syracuseStep 524647 = 786971) B786971
theorem B16187849 : Blo 523799 16187849 := bstep (se 2 (by rfl) ⟨6070443, by rfl⟩ : syracuseStep 16187849 = 12140887) B12140887
theorem B524767 : Blo 523799 524767 := bstep (se 1 (by rfl) ⟨393575, by rfl⟩ : syracuseStep 524767 = 787151) B787151
theorem B524847 : Blo 523799 524847 := bstep (se 1 (by rfl) ⟨393635, by rfl⟩ : syracuseStep 524847 = 787271) B787271
theorem B524891 : Blo 523799 524891 := bstep (se 1 (by rfl) ⟨393668, by rfl⟩ : syracuseStep 524891 = 787337) B787337
theorem B1180367 : Blo 523799 1180367 := bstep (se 1 (by rfl) ⟨885275, by rfl⟩ : syracuseStep 1180367 = 1770551) B1770551
theorem B787199 : Blo 523799 787199 := bstep (se 1 (by rfl) ⟨590399, by rfl⟩ : syracuseStep 787199 = 1180799) B1180799
theorem B525055 : Blo 523799 525055 := bstep (se 1 (by rfl) ⟨393791, by rfl⟩ : syracuseStep 525055 = 787583) B787583
theorem B1770281 : Blo 523799 1770281 := bstep (se 2 (by rfl) ⟨663855, by rfl⟩ : syracuseStep 1770281 = 1327711) B1327711
theorem B885559 : Blo 523799 885559 := bstep (se 1 (by rfl) ⟨664169, by rfl⟩ : syracuseStep 885559 = 1328339) B1328339
theorem B525147 : Blo 523799 525147 := bstep (se 1 (by rfl) ⟨393860, by rfl⟩ : syracuseStep 525147 = 787721) B787721
theorem B2524193 : Blo 523799 2524193 := bstep (se 2 (by rfl) ⟨946572, by rfl⟩ : syracuseStep 2524193 = 1893145) B1893145
theorem B525467 : Blo 523799 525467 := bstep (se 1 (by rfl) ⟨394100, by rfl⟩ : syracuseStep 525467 = 788201) B788201
theorem B591007 : Blo 523799 591007 := bstep (se 1 (by rfl) ⟨443255, by rfl⟩ : syracuseStep 591007 = 886511) B886511
theorem B525471 : Blo 523799 525471 := bstep (se 1 (by rfl) ⟨394103, by rfl⟩ : syracuseStep 525471 = 788207) B788207
theorem B886025 : Blo 523799 886025 := bstep (se 2 (by rfl) ⟨332259, by rfl⟩ : syracuseStep 886025 = 664519) B664519
theorem B2983229 : Blo 523799 2983229 := bstep (se 3 (by rfl) ⟨559355, by rfl⟩ : syracuseStep 2983229 = 1118711) B1118711
theorem B853319 : Blo 523799 853319 := bstep (se 1 (by rfl) ⟨639989, by rfl⟩ : syracuseStep 853319 = 1279979) B1279979
theorem B525639 : Blo 523799 525639 := bstep (se 1 (by rfl) ⟨394229, by rfl⟩ : syracuseStep 525639 = 788459) B788459
theorem B525807 : Blo 523799 525807 := bstep (se 1 (by rfl) ⟨394355, by rfl⟩ : syracuseStep 525807 = 788711) B788711
theorem B787967 : Blo 523799 787967 := bstep (se 1 (by rfl) ⟨590975, by rfl⟩ : syracuseStep 787967 = 1181951) B1181951
theorem B525823 : Blo 523799 525823 := bstep (se 1 (by rfl) ⟨394367, by rfl⟩ : syracuseStep 525823 = 788735) B788735
theorem B525915 : Blo 523799 525915 := bstep (se 1 (by rfl) ⟨394436, by rfl⟩ : syracuseStep 525915 = 788873) B788873
theorem B886619 : Blo 523799 886619 := bstep (se 1 (by rfl) ⟨664964, by rfl⟩ : syracuseStep 886619 = 1329929) B1329929
theorem B886639 : Blo 523799 886639 := bstep (se 1 (by rfl) ⟨664979, by rfl⟩ : syracuseStep 886639 = 1329959) B1329959
theorem B1345499 : Blo 523799 1345499 := bstep (se 1 (by rfl) ⟨1009124, by rfl⟩ : syracuseStep 1345499 = 2018249) B2018249
theorem B2000969 : Blo 523799 2000969 := bstep (se 2 (by rfl) ⟨750363, by rfl⟩ : syracuseStep 2000969 = 1500727) B1500727
theorem B1771739 : Blo 523799 1771739 := bstep (se 1 (by rfl) ⟨1328804, by rfl⟩ : syracuseStep 1771739 = 2657609) B2657609
theorem B526655 : Blo 523799 526655 := bstep (se 1 (by rfl) ⟨394991, by rfl⟩ : syracuseStep 526655 = 789983) B789983
theorem B526695 : Blo 523799 526695 := bstep (se 1 (by rfl) ⟨395021, by rfl⟩ : syracuseStep 526695 = 790043) B790043
theorem B756127 : Blo 523799 756127 := bstep (se 1 (by rfl) ⟨567095, by rfl⟩ : syracuseStep 756127 = 1134191) B1134191
theorem B526783 : Blo 523799 526783 := bstep (se 1 (by rfl) ⟨395087, by rfl⟩ : syracuseStep 526783 = 790175) B790175
theorem B788969 : Blo 523799 788969 := bstep (se 2 (by rfl) ⟨295863, by rfl⟩ : syracuseStep 788969 = 591727) B591727
theorem B4098575 : Blo 523799 4098575 := bstep (se 1 (by rfl) ⟨3073931, by rfl⟩ : syracuseStep 4098575 = 6147863) B6147863
theorem B526959 : Blo 523799 526959 := bstep (se 1 (by rfl) ⟨395219, by rfl⟩ : syracuseStep 526959 = 790439) B790439
theorem B789119 : Blo 523799 789119 := bstep (se 1 (by rfl) ⟨591839, by rfl⟩ : syracuseStep 789119 = 1183679) B1183679
theorem B526975 : Blo 523799 526975 := bstep (se 1 (by rfl) ⟨395231, by rfl⟩ : syracuseStep 526975 = 790463) B790463
theorem B5048999 : Blo 523799 5048999 := bstep (se 1 (by rfl) ⟨3786749, by rfl⟩ : syracuseStep 5048999 = 7573499) B7573499
theorem B527079 : Blo 523799 527079 := bstep (se 1 (by rfl) ⟨395309, by rfl⟩ : syracuseStep 527079 = 790619) B790619
theorem B789257 : Blo 523799 789257 := bstep (se 2 (by rfl) ⟨295971, by rfl⟩ : syracuseStep 789257 = 591943) B591943
theorem B527175 : Blo 523799 527175 := bstep (se 1 (by rfl) ⟨395381, by rfl⟩ : syracuseStep 527175 = 790763) B790763
theorem B527215 : Blo 523799 527215 := bstep (se 1 (by rfl) ⟨395411, by rfl⟩ : syracuseStep 527215 = 790823) B790823
theorem B789497 : Blo 523799 789497 := bstep (se 2 (by rfl) ⟨296061, by rfl⟩ : syracuseStep 789497 = 592123) B592123
theorem B527391 : Blo 523799 527391 := bstep (se 1 (by rfl) ⟨395543, by rfl⟩ : syracuseStep 527391 = 791087) B791087
theorem B1772603 : Blo 523799 1772603 := bstep (se 1 (by rfl) ⟨1329452, by rfl⟩ : syracuseStep 1772603 = 2658905) B2658905
theorem B789671 : Blo 523799 789671 := bstep (se 1 (by rfl) ⟨592253, by rfl⟩ : syracuseStep 789671 = 1184507) B1184507
theorem B527527 : Blo 523799 527527 := bstep (se 1 (by rfl) ⟨395645, by rfl⟩ : syracuseStep 527527 = 791291) B791291
theorem B25857197 : Blo 523799 25857197 := bstep (se 3 (by rfl) ⟨4848224, by rfl⟩ : syracuseStep 25857197 = 9696449) B9696449
theorem B20417923 : Blo 523799 20417923 := bstep (se 1 (by rfl) ⟨15313442, by rfl⟩ : syracuseStep 20417923 = 30626885) B30626885
theorem B593311 : Blo 523799 593311 := bstep (se 1 (by rfl) ⟨444983, by rfl⟩ : syracuseStep 593311 = 889967) B889967
theorem B527775 : Blo 523799 527775 := bstep (se 1 (by rfl) ⟨395831, by rfl⟩ : syracuseStep 527775 = 791663) B791663
theorem B1183337 : Blo 523799 1183337 := bstep (se 2 (by rfl) ⟨443751, by rfl⟩ : syracuseStep 1183337 = 887503) B887503
theorem B790121 : Blo 523799 790121 := bstep (se 2 (by rfl) ⟨296295, by rfl⟩ : syracuseStep 790121 = 592591) B592591
theorem B1183391 : Blo 523799 1183391 := bstep (se 1 (by rfl) ⟨887543, by rfl⟩ : syracuseStep 1183391 = 1775087) B1775087
theorem B2002715 : Blo 523799 2002715 := bstep (se 1 (by rfl) ⟨1502036, by rfl⟩ : syracuseStep 2002715 = 3004073) B3004073
theorem B1183625 : Blo 523799 1183625 := bstep (se 2 (by rfl) ⟨443859, by rfl⟩ : syracuseStep 1183625 = 887719) B887719
theorem B790409 : Blo 523799 790409 := bstep (se 2 (by rfl) ⟨296403, by rfl⟩ : syracuseStep 790409 = 592807) B592807
theorem B2985893 : Blo 523799 2985893 := bstep (se 4 (by rfl) ⟨279927, by rfl⟩ : syracuseStep 2985893 = 559855) B559855
theorem B1183841 : Blo 523799 1183841 := bstep (se 2 (by rfl) ⟨443940, by rfl⟩ : syracuseStep 1183841 = 887881) B887881
theorem B790649 : Blo 523799 790649 := bstep (se 2 (by rfl) ⟨296493, by rfl⟩ : syracuseStep 790649 = 592987) B592987
theorem B1773791 : Blo 523799 1773791 := bstep (se 1 (by rfl) ⟨1330343, by rfl⟩ : syracuseStep 1773791 = 2660687) B2660687
theorem B791207 : Blo 523799 791207 := bstep (se 1 (by rfl) ⟨593405, by rfl⟩ : syracuseStep 791207 = 1186811) B1186811
theorem B2003687 : Blo 523799 2003687 := bstep (se 1 (by rfl) ⟨1502765, by rfl⟩ : syracuseStep 2003687 = 3005531) B3005531
theorem B1774331 : Blo 523799 1774331 := bstep (se 1 (by rfl) ⟨1330748, by rfl⟩ : syracuseStep 1774331 = 2661497) B2661497
theorem B791327 : Blo 523799 791327 := bstep (se 1 (by rfl) ⟨593495, by rfl⟩ : syracuseStep 791327 = 1186991) B1186991
theorem B791423 : Blo 523799 791423 := bstep (se 1 (by rfl) ⟨593567, by rfl⟩ : syracuseStep 791423 = 1187135) B1187135
theorem B1774493 : Blo 523799 1774493 := bstep (se 3 (by rfl) ⟨332717, by rfl⟩ : syracuseStep 1774493 = 665435) B665435
theorem B4166585 : Blo 523799 4166585 := bstep (se 2 (by rfl) ⟨1562469, by rfl⟩ : syracuseStep 4166585 = 3124939) B3124939
theorem B791495 : Blo 523799 791495 := bstep (se 1 (by rfl) ⟨593621, by rfl⟩ : syracuseStep 791495 = 1187243) B1187243
theorem B4036007 : Blo 523799 4036007 := bstep (se 1 (by rfl) ⟨3027005, by rfl⟩ : syracuseStep 4036007 = 6054011) B6054011
theorem B1185983 : Blo 523799 1185983 := bstep (se 1 (by rfl) ⟨889487, by rfl⟩ : syracuseStep 1185983 = 1778975) B1778975
theorem B6724205 : Blo 523799 6724205 := bstep (se 3 (by rfl) ⟨1260788, by rfl⟩ : syracuseStep 6724205 = 2521577) B2521577
theorem B4037363 : Blo 523799 4037363 := bstep (se 1 (by rfl) ⟨3028022, by rfl⟩ : syracuseStep 4037363 = 6056045) B6056045
theorem B1777085 : Blo 523799 1777085 := bstep (se 3 (by rfl) ⟨333203, by rfl⟩ : syracuseStep 1777085 = 666407) B666407
theorem B1187279 : Blo 523799 1187279 := bstep (se 1 (by rfl) ⟨890459, by rfl⟩ : syracuseStep 1187279 = 1780919) B1780919
theorem B8953577 : Blo 523799 8953577 := bstep (se 2 (by rfl) ⟨3357591, by rfl⟩ : syracuseStep 8953577 = 6715183) B6715183
theorem B1777949 : Blo 523799 1777949 := bstep (se 3 (by rfl) ⟨333365, by rfl⟩ : syracuseStep 1777949 = 666731) B666731
theorem B2662793 : Blo 523799 2662793 := bstep (se 2 (by rfl) ⟨998547, by rfl⟩ : syracuseStep 2662793 = 1997095) B1997095
theorem B4497839 : Blo 523799 4497839 := bstep (se 1 (by rfl) ⟨3373379, by rfl⟩ : syracuseStep 4497839 = 6746759) B6746759
theorem B4268659 : Blo 523799 4268659 := bstep (se 1 (by rfl) ⟨3201494, by rfl⟩ : syracuseStep 4268659 = 6402989) B6402989
theorem B2532649 : Blo 523799 2532649 := bstep (se 2 (by rfl) ⟨949743, by rfl⟩ : syracuseStep 2532649 = 1899487) B1899487
theorem B1779191 : Blo 523799 1779191 := bstep (se 1 (by rfl) ⟨1334393, by rfl⟩ : syracuseStep 1779191 = 2668787) B2668787
theorem B1123931 : Blo 523799 1123931 := bstep (se 1 (by rfl) ⟨842948, by rfl⟩ : syracuseStep 1123931 = 1685897) B1685897
theorem B2434697 : Blo 523799 2434697 := bstep (se 2 (by rfl) ⟨913011, by rfl⟩ : syracuseStep 2434697 = 1826023) B1826023
theorem B1779407 : Blo 523799 1779407 := bstep (se 1 (by rfl) ⟨1334555, by rfl⟩ : syracuseStep 1779407 = 2669111) B2669111
theorem B1091767 : Blo 523799 1091767 := bstep (se 1 (by rfl) ⟨818825, by rfl⟩ : syracuseStep 1091767 = 1637651) B1637651
theorem B1419599 : Blo 523799 1419599 := bstep (se 1 (by rfl) ⟨1064699, by rfl⟩ : syracuseStep 1419599 = 2129399) B2129399
theorem B961001 : Blo 523799 961001 := bstep (se 2 (by rfl) ⟨360375, by rfl⟩ : syracuseStep 961001 = 720751) B720751
theorem B1780271 : Blo 523799 1780271 := bstep (se 1 (by rfl) ⟨1335203, by rfl⟩ : syracuseStep 1780271 = 2670407) B2670407
theorem B1780379 : Blo 523799 1780379 := bstep (se 1 (by rfl) ⟨1335284, by rfl⟩ : syracuseStep 1780379 = 2670569) B2670569
theorem B1780649 : Blo 523799 1780649 := bstep (se 2 (by rfl) ⟨667743, by rfl⟩ : syracuseStep 1780649 = 1335487) B1335487
theorem B2239883 : Blo 523799 2239883 := bstep (se 1 (by rfl) ⟨1679912, by rfl⟩ : syracuseStep 2239883 = 3359825) B3359825
theorem B1126271 : Blo 523799 1126271 := bstep (se 1 (by rfl) ⟨844703, by rfl⟩ : syracuseStep 1126271 = 1689407) B1689407
theorem B18231277 : Blo 523799 18231277 := bstep (se 3 (by rfl) ⟨3418364, by rfl⟩ : syracuseStep 18231277 = 6836729) B6836729
theorem B995465 : Blo 523799 995465 := bstep (se 2 (by rfl) ⟨373299, by rfl⟩ : syracuseStep 995465 = 746599) B746599
theorem B667855 : Blo 523799 667855 := bstep (se 1 (by rfl) ⟨500891, by rfl⟩ : syracuseStep 667855 = 1001783) B1001783
theorem B92385623 : Blo 523799 92385623 := bstep (se 1 (by rfl) ⟨69289217, by rfl⟩ : syracuseStep 92385623 = 138578435) B138578435
theorem B2996783 : Blo 523799 2996783 := bstep (se 1 (by rfl) ⟨2247587, by rfl⟩ : syracuseStep 2996783 = 4495175) B4495175
theorem B3783955 : Blo 523799 3783955 := bstep (se 1 (by rfl) ⟨2837966, by rfl⟩ : syracuseStep 3783955 = 5675933) B5675933
theorem B999391 : Blo 523799 999391 := bstep (se 1 (by rfl) ⟨749543, by rfl⟩ : syracuseStep 999391 = 1499087) B1499087
theorem B1327175 : Blo 523799 1327175 := bstep (se 1 (by rfl) ⟨995381, by rfl⟩ : syracuseStep 1327175 = 1990763) B1990763
theorem B10829933 : Blo 523799 10829933 := bstep (se 3 (by rfl) ⟨2030612, by rfl⟩ : syracuseStep 10829933 = 4061225) B4061225
theorem B3981797 : Blo 523799 3981797 := bstep (se 4 (by rfl) ⟨373293, by rfl⟩ : syracuseStep 3981797 = 746587) B746587
theorem B1327823 : Blo 523799 1327823 := bstep (se 1 (by rfl) ⟨995867, by rfl⟩ : syracuseStep 1327823 = 1991735) B1991735
theorem B2835719 : Blo 523799 2835719 := bstep (se 1 (by rfl) ⟨2126789, by rfl⟩ : syracuseStep 2835719 = 4253579) B4253579
theorem B1329119 : Blo 523799 1329119 := bstep (se 1 (by rfl) ⟨996839, by rfl⟩ : syracuseStep 1329119 = 1993679) B1993679
theorem B1493437 : Blo 523799 1493437 := bstep (se 3 (by rfl) ⟨280019, by rfl⟩ : syracuseStep 1493437 = 560039) B560039
theorem B3361337 : Blo 523799 3361337 := bstep (se 2 (by rfl) ⟨1260501, by rfl⟩ : syracuseStep 3361337 = 2521003) B2521003
theorem B1199195 : Blo 523799 1199195 := bstep (se 1 (by rfl) ⟨899396, by rfl⟩ : syracuseStep 1199195 = 1798793) B1798793
theorem B1331113 : Blo 523799 1331113 := bstep (se 2 (by rfl) ⟨499167, by rfl⟩ : syracuseStep 1331113 = 998335) B998335
theorem B2248681 : Blo 523799 2248681 := bstep (se 2 (by rfl) ⟨843255, by rfl⟩ : syracuseStep 2248681 = 1686511) B1686511
theorem B4477031 : Blo 523799 4477031 := bstep (se 1 (by rfl) ⟨3357773, by rfl⟩ : syracuseStep 4477031 = 6715547) B6715547
theorem B147509855 : Blo 523799 147509855 := bstep (se 1 (by rfl) ⟨110632391, by rfl⟩ : syracuseStep 147509855 = 221264783) B221264783
theorem B2249639 : Blo 523799 2249639 := bstep (se 1 (by rfl) ⟨1687229, by rfl⟩ : syracuseStep 2249639 = 3374459) B3374459
theorem B3364001 : Blo 523799 3364001 := bstep (se 2 (by rfl) ⟨1261500, by rfl⟩ : syracuseStep 3364001 = 2523001) B2523001
theorem B13685939 : Blo 523799 13685939 := bstep (se 1 (by rfl) ⟨10264454, by rfl⟩ : syracuseStep 13685939 = 20528909) B20528909
theorem B3233191 : Blo 523799 3233191 := bstep (se 1 (by rfl) ⟨2424893, by rfl⟩ : syracuseStep 3233191 = 4849787) B4849787
theorem B2250355 : Blo 523799 2250355 := bstep (se 1 (by rfl) ⟨1687766, by rfl⟩ : syracuseStep 2250355 = 3375533) B3375533
theorem B1889945 : Blo 523799 1889945 := bstep (se 2 (by rfl) ⟨708729, by rfl⟩ : syracuseStep 1889945 = 1417459) B1417459
theorem B1890145 : Blo 523799 1890145 := bstep (se 2 (by rfl) ⟨708804, by rfl⟩ : syracuseStep 1890145 = 1417609) B1417609
theorem B30627841 : Blo 523799 30627841 := bstep (se 2 (by rfl) ⟨11485440, by rfl⟩ : syracuseStep 30627841 = 22970881) B22970881
theorem B1497275 : Blo 523799 1497275 := bstep (se 1 (by rfl) ⟨1122956, by rfl⟩ : syracuseStep 1497275 = 2245913) B2245913
theorem B20273489 : Blo 523799 20273489 := bstep (se 2 (by rfl) ⟨7602558, by rfl⟩ : syracuseStep 20273489 = 15205117) B15205117
theorem B3005099 : Blo 523799 3005099 := bstep (se 1 (by rfl) ⟨2253824, by rfl⟩ : syracuseStep 3005099 = 4507649) B4507649
theorem B32365619 : Blo 523799 32365619 := bstep (se 1 (by rfl) ⟨24274214, by rfl⟩ : syracuseStep 32365619 = 48548429) B48548429
theorem B1334495 : Blo 523799 1334495 := bstep (se 1 (by rfl) ⟨1000871, by rfl⟩ : syracuseStep 1334495 = 2001743) B2001743
theorem B1992539 : Blo 523799 1992539 := bstep (se 1 (by rfl) ⟨1494404, by rfl⟩ : syracuseStep 1992539 = 2988809) B2988809
theorem B8513437 : Blo 523799 8513437 := bstep (se 3 (by rfl) ⟨1596269, by rfl⟩ : syracuseStep 8513437 = 3192539) B3192539
theorem B9136091 : Blo 523799 9136091 := bstep (se 1 (by rfl) ⟨6852068, by rfl⟩ : syracuseStep 9136091 = 13704137) B13704137
theorem B3991517 : Blo 523799 3991517 := bstep (se 3 (by rfl) ⟨748409, by rfl⟩ : syracuseStep 3991517 = 1496819) B1496819
theorem B1993511 : Blo 523799 1993511 := bstep (se 1 (by rfl) ⟨1495133, by rfl⟩ : syracuseStep 1993511 = 2990267) B2990267
theorem B884729 : Blo 523799 884729 := bstep (se 2 (by rfl) ⟨331773, by rfl⟩ : syracuseStep 884729 = 663547) B663547
theorem B1995425 : Blo 523799 1995425 := bstep (se 2 (by rfl) ⟨748284, by rfl⟩ : syracuseStep 1995425 = 1496569) B1496569
theorem B717599 : Blo 523799 717599 := bstep (se 1 (by rfl) ⟨538199, by rfl⟩ : syracuseStep 717599 = 1076399) B1076399
theorem B5207003 : Blo 523799 5207003 := bstep (se 1 (by rfl) ⟨3905252, by rfl⟩ : syracuseStep 5207003 = 7810505) B7810505
theorem B1995911 : Blo 523799 1995911 := bstep (se 1 (by rfl) ⟨1496933, by rfl⟩ : syracuseStep 1995911 = 2993867) B2993867
theorem B14349797 : Blo 523799 14349797 := bstep (se 4 (by rfl) ⟨1345293, by rfl⟩ : syracuseStep 14349797 = 2690587) B2690587
theorem B8451793 : Blo 523799 8451793 := bstep (se 2 (by rfl) ⟨3169422, by rfl⟩ : syracuseStep 8451793 = 6338845) B6338845
theorem B4487177 : Blo 523799 4487177 := bstep (se 2 (by rfl) ⟨1682691, by rfl⟩ : syracuseStep 4487177 = 3365383) B3365383
theorem B3995891 : Blo 523799 3995891 := bstep (se 1 (by rfl) ⟨2996918, by rfl⟩ : syracuseStep 3995891 = 5993837) B5993837
theorem B2030447 : Blo 523799 2030447 := bstep (se 1 (by rfl) ⟨1522835, by rfl⟩ : syracuseStep 2030447 = 3045671) B3045671
theorem B3242911 : Blo 523799 3242911 := bstep (se 1 (by rfl) ⟨2432183, by rfl⟩ : syracuseStep 3242911 = 4864367) B4864367
theorem B415464389 : Blo 523799 415464389 := bstep (se 4 (by rfl) ⟨38949786, by rfl⟩ : syracuseStep 415464389 = 77899573) B77899573
theorem B7568423 : Blo 523799 7568423 := bstep (se 1 (by rfl) ⟨5676317, by rfl⟩ : syracuseStep 7568423 = 11352635) B11352635
theorem B1998067 : Blo 523799 1998067 := bstep (se 1 (by rfl) ⟨1498550, by rfl⟩ : syracuseStep 1998067 = 2997101) B2997101
theorem B8092943 : Blo 523799 8092943 := bstep (se 1 (by rfl) ⟨6069707, by rfl⟩ : syracuseStep 8092943 = 12139415) B12139415
theorem B785735 : Blo 523799 785735 := bstep (se 1 (by rfl) ⟨589301, by rfl⟩ : syracuseStep 785735 = 1178603) B1178603
theorem B1179035 : Blo 523799 1179035 := bstep (se 1 (by rfl) ⟨884276, by rfl⟩ : syracuseStep 1179035 = 1768553) B1768553
theorem B523879 : Blo 523799 523879 := bstep (se 1 (by rfl) ⟨392909, by rfl⟩ : syracuseStep 523879 = 785819) B785819
theorem B523931 : Blo 523799 523931 := bstep (se 1 (by rfl) ⟨392948, by rfl⟩ : syracuseStep 523931 = 785897) B785897
theorem B523935 : Blo 523799 523935 := bstep (se 1 (by rfl) ⟨392951, by rfl⟩ : syracuseStep 523935 = 785903) B785903
theorem B524027 : Blo 523799 524027 := bstep (se 1 (by rfl) ⟨393020, by rfl⟩ : syracuseStep 524027 = 786041) B786041
theorem B1802047 : Blo 523799 1802047 := bstep (se 1 (by rfl) ⟨1351535, by rfl⟩ : syracuseStep 1802047 = 2703071) B2703071
theorem B524159 : Blo 523799 524159 := bstep (se 1 (by rfl) ⟨393119, by rfl⟩ : syracuseStep 524159 = 786239) B786239
theorem B524191 : Blo 523799 524191 := bstep (se 1 (by rfl) ⟨393143, by rfl⟩ : syracuseStep 524191 = 786287) B786287
theorem B786335 : Blo 523799 786335 := bstep (se 1 (by rfl) ⟨589751, by rfl⟩ : syracuseStep 786335 = 1179503) B1179503
theorem B884783 : Blo 523799 884783 := bstep (se 1 (by rfl) ⟨663587, by rfl⟩ : syracuseStep 884783 = 1327175) B1327175
theorem B3997835 : Blo 523799 3997835 := bstep (se 1 (by rfl) ⟨2998376, by rfl⟩ : syracuseStep 3997835 = 5996753) B5996753
theorem B2654531 : Blo 523799 2654531 := bstep (se 1 (by rfl) ⟨1990898, by rfl⟩ : syracuseStep 2654531 = 3981797) B3981797
theorem B885215 : Blo 523799 885215 := bstep (se 1 (by rfl) ⟨663911, by rfl⟩ : syracuseStep 885215 = 1327823) B1327823
theorem B786911 : Blo 523799 786911 := bstep (se 1 (by rfl) ⟨590183, by rfl⟩ : syracuseStep 786911 = 1180367) B1180367
theorem B524799 : Blo 523799 524799 := bstep (se 1 (by rfl) ⟨393599, by rfl⟩ : syracuseStep 524799 = 787199) B787199
theorem B1180187 : Blo 523799 1180187 := bstep (se 1 (by rfl) ⟨885140, by rfl⟩ : syracuseStep 1180187 = 1770281) B1770281
theorem B590683 : Blo 523799 590683 := bstep (se 1 (by rfl) ⟨443012, by rfl⟩ : syracuseStep 590683 = 886025) B886025
theorem B525311 : Blo 523799 525311 := bstep (se 1 (by rfl) ⟨393983, by rfl⟩ : syracuseStep 525311 = 787967) B787967
theorem B1180745 : Blo 523799 1180745 := bstep (se 2 (by rfl) ⟨442779, by rfl⟩ : syracuseStep 1180745 = 885559) B885559
theorem B591079 : Blo 523799 591079 := bstep (se 1 (by rfl) ⟨443309, by rfl⟩ : syracuseStep 591079 = 886619) B886619
theorem B886079 : Blo 523799 886079 := bstep (se 1 (by rfl) ⟨664559, by rfl⟩ : syracuseStep 886079 = 1329119) B1329119
theorem B1181159 : Blo 523799 1181159 := bstep (se 1 (by rfl) ⟨885869, by rfl⟩ : syracuseStep 1181159 = 1771739) B1771739
theorem B788009 : Blo 523799 788009 := bstep (se 2 (by rfl) ⟨295503, by rfl⟩ : syracuseStep 788009 = 591007) B591007
theorem B525979 : Blo 523799 525979 := bstep (se 1 (by rfl) ⟨394484, by rfl⟩ : syracuseStep 525979 = 788969) B788969
theorem B3376865 : Blo 523799 3376865 := bstep (se 2 (by rfl) ⟨1266324, by rfl⟩ : syracuseStep 3376865 = 2532649) B2532649
theorem B526079 : Blo 523799 526079 := bstep (se 1 (by rfl) ⟨394559, by rfl⟩ : syracuseStep 526079 = 789119) B789119
theorem B526171 : Blo 523799 526171 := bstep (se 1 (by rfl) ⟨394628, by rfl⟩ : syracuseStep 526171 = 789257) B789257
theorem B526331 : Blo 523799 526331 := bstep (se 1 (by rfl) ⟨394748, by rfl⟩ : syracuseStep 526331 = 789497) B789497
theorem B1181735 : Blo 523799 1181735 := bstep (se 1 (by rfl) ⟨886301, by rfl⟩ : syracuseStep 1181735 = 1772603) B1772603
theorem B526447 : Blo 523799 526447 := bstep (se 1 (by rfl) ⟨394835, by rfl⟩ : syracuseStep 526447 = 789671) B789671
theorem B17238131 : Blo 523799 17238131 := bstep (se 1 (by rfl) ⟨12928598, by rfl⟩ : syracuseStep 17238131 = 25857197) B25857197
theorem B788891 : Blo 523799 788891 := bstep (se 1 (by rfl) ⟨591668, by rfl⟩ : syracuseStep 788891 = 1183337) B1183337
theorem B526747 : Blo 523799 526747 := bstep (se 1 (by rfl) ⟨395060, by rfl⟩ : syracuseStep 526747 = 790121) B790121
theorem B788927 : Blo 523799 788927 := bstep (se 1 (by rfl) ⟨591695, by rfl⟩ : syracuseStep 788927 = 1183391) B1183391
theorem B1182185 : Blo 523799 1182185 := bstep (se 2 (by rfl) ⟨443319, by rfl⟩ : syracuseStep 1182185 = 886639) B886639
theorem B789083 : Blo 523799 789083 := bstep (se 1 (by rfl) ⟨591812, by rfl⟩ : syracuseStep 789083 = 1183625) B1183625
theorem B526939 : Blo 523799 526939 := bstep (se 1 (by rfl) ⟨395204, by rfl⟩ : syracuseStep 526939 = 790409) B790409
theorem B789227 : Blo 523799 789227 := bstep (se 1 (by rfl) ⟨591920, by rfl⟩ : syracuseStep 789227 = 1183841) B1183841
theorem B2984687 : Blo 523799 2984687 := bstep (se 1 (by rfl) ⟨2238515, by rfl⟩ : syracuseStep 2984687 = 4477031) B4477031
theorem B527099 : Blo 523799 527099 := bstep (se 1 (by rfl) ⟨395324, by rfl⟩ : syracuseStep 527099 = 790649) B790649
theorem B1182527 : Blo 523799 1182527 := bstep (se 1 (by rfl) ⟨886895, by rfl⟩ : syracuseStep 1182527 = 1773791) B1773791
theorem B98339903 : Blo 523799 98339903 := bstep (se 1 (by rfl) ⟨73754927, by rfl⟩ : syracuseStep 98339903 = 147509855) B147509855
theorem B527471 : Blo 523799 527471 := bstep (se 1 (by rfl) ⟨395603, by rfl⟩ : syracuseStep 527471 = 791207) B791207
theorem B1182887 : Blo 523799 1182887 := bstep (se 1 (by rfl) ⟨887165, by rfl⟩ : syracuseStep 1182887 = 1774331) B1774331
theorem B527551 : Blo 523799 527551 := bstep (se 1 (by rfl) ⟨395663, by rfl⟩ : syracuseStep 527551 = 791327) B791327
theorem B527615 : Blo 523799 527615 := bstep (se 1 (by rfl) ⟨395711, by rfl⟩ : syracuseStep 527615 = 791423) B791423
theorem B1182995 : Blo 523799 1182995 := bstep (se 1 (by rfl) ⟨887246, by rfl⟩ : syracuseStep 1182995 = 1774493) B1774493
theorem B527663 : Blo 523799 527663 := bstep (se 1 (by rfl) ⟨395747, by rfl⟩ : syracuseStep 527663 = 791495) B791495
theorem B2690671 : Blo 523799 2690671 := bstep (se 1 (by rfl) ⟨2018003, by rfl⟩ : syracuseStep 2690671 = 4036007) B4036007
theorem B790655 : Blo 523799 790655 := bstep (se 1 (by rfl) ⟨592991, by rfl⟩ : syracuseStep 790655 = 1185983) B1185983
theorem B2003399 : Blo 523799 2003399 := bstep (se 1 (by rfl) ⟨1502549, by rfl⟩ : syracuseStep 2003399 = 3005099) B3005099
theorem B2691575 : Blo 523799 2691575 := bstep (se 1 (by rfl) ⟨2018681, by rfl⟩ : syracuseStep 2691575 = 4037363) B4037363
theorem B791081 : Blo 523799 791081 := bstep (se 2 (by rfl) ⟨296655, by rfl⟩ : syracuseStep 791081 = 593311) B593311
theorem B889663 : Blo 523799 889663 := bstep (se 1 (by rfl) ⟨667247, by rfl⟩ : syracuseStep 889663 = 1334495) B1334495
theorem B1184723 : Blo 523799 1184723 := bstep (se 1 (by rfl) ⟨888542, by rfl⟩ : syracuseStep 1184723 = 1777085) B1777085
theorem B791519 : Blo 523799 791519 := bstep (se 1 (by rfl) ⟨593639, by rfl⟩ : syracuseStep 791519 = 1187279) B1187279
theorem B5969051 : Blo 523799 5969051 := bstep (se 1 (by rfl) ⟨4476788, by rfl⟩ : syracuseStep 5969051 = 8953577) B8953577
theorem B1774817 : Blo 523799 1774817 := bstep (se 2 (by rfl) ⟨665556, by rfl⟩ : syracuseStep 1774817 = 1331113) B1331113
theorem B1185299 : Blo 523799 1185299 := bstep (se 1 (by rfl) ⟨888974, by rfl⟩ : syracuseStep 1185299 = 1777949) B1777949
theorem B1775195 : Blo 523799 1775195 := bstep (se 1 (by rfl) ⟨1331396, by rfl⟩ : syracuseStep 1775195 = 2662793) B2662793
theorem B890473 : Blo 523799 890473 := bstep (se 2 (by rfl) ⟨333927, by rfl⟩ : syracuseStep 890473 = 667855) B667855
theorem B1186127 : Blo 523799 1186127 := bstep (se 1 (by rfl) ⟨889595, by rfl⟩ : syracuseStep 1186127 = 1779191) B1779191
theorem B1186271 : Blo 523799 1186271 := bstep (se 1 (by rfl) ⟨889703, by rfl⟩ : syracuseStep 1186271 = 1779407) B1779407
theorem B2661011 : Blo 523799 2661011 := bstep (se 1 (by rfl) ⟨1995758, by rfl⟩ : syracuseStep 2661011 = 3991517) B3991517
theorem B1186847 : Blo 523799 1186847 := bstep (se 1 (by rfl) ⟨890135, by rfl⟩ : syracuseStep 1186847 = 1780271) B1780271
theorem B1186919 : Blo 523799 1186919 := bstep (se 1 (by rfl) ⟨890189, by rfl⟩ : syracuseStep 1186919 = 1780379) B1780379
theorem B1187099 : Blo 523799 1187099 := bstep (se 1 (by rfl) ⟨890324, by rfl⟩ : syracuseStep 1187099 = 1780649) B1780649
theorem B40837121 : Blo 523799 40837121 := bstep (se 2 (by rfl) ⟨15313920, by rfl⟩ : syracuseStep 40837121 = 30627841) B30627841
theorem B663643 : Blo 523799 663643 := bstep (se 1 (by rfl) ⟨497732, by rfl⟩ : syracuseStep 663643 = 995465) B995465
theorem B2991451 : Blo 523799 2991451 := bstep (se 1 (by rfl) ⟨2243588, by rfl⟩ : syracuseStep 2991451 = 4487177) B4487177
theorem B2663927 : Blo 523799 2663927 := bstep (se 1 (by rfl) ⟨1997945, by rfl⟩ : syracuseStep 2663927 = 3995891) B3995891
theorem B2664089 : Blo 523799 2664089 := bstep (se 2 (by rfl) ⟨999033, by rfl⟩ : syracuseStep 2664089 = 1998067) B1998067
theorem B1353631 : Blo 523799 1353631 := bstep (se 1 (by rfl) ⟨1015223, by rfl⟩ : syracuseStep 1353631 = 2030447) B2030447
theorem B2402729 : Blo 523799 2402729 := bstep (se 2 (by rfl) ⟨901023, by rfl⟩ : syracuseStep 2402729 = 1802047) B1802047
theorem B7219955 : Blo 523799 7219955 := bstep (se 1 (by rfl) ⟨5414966, by rfl⟩ : syracuseStep 7219955 = 10829933) B10829933
theorem B10791899 : Blo 523799 10791899 := bstep (se 1 (by rfl) ⟨8093924, by rfl⟩ : syracuseStep 10791899 = 16187849) B16187849
theorem B1682795 : Blo 523799 1682795 := bstep (se 1 (by rfl) ⟨1262096, by rfl⟩ : syracuseStep 1682795 = 2524193) B2524193
theorem B568879 : Blo 523799 568879 := bstep (se 1 (by rfl) ⟨426659, by rfl⟩ : syracuseStep 568879 = 853319) B853319
theorem B896999 : Blo 523799 896999 := bstep (se 1 (by rfl) ⟨672749, by rfl⟩ : syracuseStep 896999 = 1345499) B1345499
theorem B2732383 : Blo 523799 2732383 := bstep (se 1 (by rfl) ⟨2049287, by rfl⟩ : syracuseStep 2732383 = 4098575) B4098575
theorem B2240891 : Blo 523799 2240891 := bstep (se 1 (by rfl) ⟨1680668, by rfl⟩ : syracuseStep 2240891 = 3361337) B3361337
theorem B799463 : Blo 523799 799463 := bstep (se 1 (by rfl) ⟨599597, by rfl⟩ : syracuseStep 799463 = 1199195) B1199195
theorem B1913597 : Blo 523799 1913597 := bstep (se 3 (by rfl) ⟨358799, by rfl⟩ : syracuseStep 1913597 = 717599) B717599
theorem B11351249 : Blo 523799 11351249 := bstep (se 2 (by rfl) ⟨4256718, by rfl⟩ : syracuseStep 11351249 = 8513437) B8513437
theorem B1455689 : Blo 523799 1455689 := bstep (se 2 (by rfl) ⟨545883, by rfl⟩ : syracuseStep 1455689 = 1091767) B1091767
theorem B2242667 : Blo 523799 2242667 := bstep (se 1 (by rfl) ⟨1682000, by rfl⟩ : syracuseStep 2242667 = 3364001) B3364001
theorem B9123959 : Blo 523799 9123959 := bstep (se 1 (by rfl) ⟨6842969, by rfl⟩ : syracuseStep 9123959 = 13685939) B13685939
theorem B1259963 : Blo 523799 1259963 := bstep (se 1 (by rfl) ⟨944972, by rfl⟩ : syracuseStep 1259963 = 1889945) B1889945
theorem B998183 : Blo 523799 998183 := bstep (se 1 (by rfl) ⟨748637, by rfl⟩ : syracuseStep 998183 = 1497275) B1497275
theorem B13515659 : Blo 523799 13515659 := bstep (se 1 (by rfl) ⟨10136744, by rfl⟩ : syracuseStep 13515659 = 20273489) B20273489
theorem B21577079 : Blo 523799 21577079 := bstep (se 1 (by rfl) ⟨16182809, by rfl⟩ : syracuseStep 21577079 = 32365619) B32365619
theorem B2998241 : Blo 523799 2998241 := bstep (se 2 (by rfl) ⟨1124340, by rfl⟩ : syracuseStep 2998241 = 2248681) B2248681
theorem B2998559 : Blo 523799 2998559 := bstep (se 1 (by rfl) ⟨2248919, by rfl⟩ : syracuseStep 2998559 = 4497839) B4497839
theorem B1623131 : Blo 523799 1623131 := bstep (se 1 (by rfl) ⟨1217348, by rfl⟩ : syracuseStep 1623131 = 2434697) B2434697
theorem B1328359 : Blo 523799 1328359 := bstep (se 1 (by rfl) ⟨996269, by rfl⟩ : syracuseStep 1328359 = 1992539) B1992539
theorem B640667 : Blo 523799 640667 := bstep (se 1 (by rfl) ⟨480500, by rfl⟩ : syracuseStep 640667 = 961001) B961001
theorem B1329007 : Blo 523799 1329007 := bstep (se 1 (by rfl) ⟨996755, by rfl⟩ : syracuseStep 1329007 = 1993511) B1993511
theorem B4310921 : Blo 523799 4310921 := bstep (se 2 (by rfl) ⟨1616595, by rfl⟩ : syracuseStep 4310921 = 3233191) B3233191
theorem B3000473 : Blo 523799 3000473 := bstep (se 2 (by rfl) ⟨1125177, by rfl⟩ : syracuseStep 3000473 = 2250355) B2250355
theorem B1493255 : Blo 523799 1493255 := bstep (se 1 (by rfl) ⟨1119941, by rfl⟩ : syracuseStep 1493255 = 2239883) B2239883
theorem B61590415 : Blo 523799 61590415 := bstep (se 1 (by rfl) ⟨46192811, by rfl⟩ : syracuseStep 61590415 = 92385623) B92385623
theorem B1330283 : Blo 523799 1330283 := bstep (se 1 (by rfl) ⟨997712, by rfl⟩ : syracuseStep 1330283 = 1995425) B1995425
theorem B1330607 : Blo 523799 1330607 := bstep (se 1 (by rfl) ⟨997955, by rfl⟩ : syracuseStep 1330607 = 1995911) B1995911
theorem B10080773 : Blo 523799 10080773 := bstep (se 4 (by rfl) ⟨945072, by rfl⟩ : syracuseStep 10080773 = 1890145) B1890145
theorem B276976259 : Blo 523799 276976259 := bstep (se 1 (by rfl) ⟨207732194, by rfl⟩ : syracuseStep 276976259 = 415464389) B415464389
theorem B5395295 : Blo 523799 5395295 := bstep (se 1 (by rfl) ⟨4046471, by rfl⟩ : syracuseStep 5395295 = 8092943) B8092943
theorem B3003389 : Blo 523799 3003389 := bstep (se 3 (by rfl) ⟨563135, by rfl⟩ : syracuseStep 3003389 = 1126271) B1126271
theorem B1332521 : Blo 523799 1332521 := bstep (se 2 (by rfl) ⟨499695, by rfl⟩ : syracuseStep 1332521 = 999391) B999391
theorem B5691545 : Blo 523799 5691545 := bstep (se 2 (by rfl) ⟨2134329, by rfl⟩ : syracuseStep 5691545 = 4268659) B4268659
theorem B1890479 : Blo 523799 1890479 := bstep (se 1 (by rfl) ⟨1417859, by rfl⟩ : syracuseStep 1890479 = 2835719) B2835719
theorem B1988819 : Blo 523799 1988819 := bstep (se 1 (by rfl) ⟨1491614, by rfl⟩ : syracuseStep 1988819 = 2983229) B2983229
theorem B1333979 : Blo 523799 1333979 := bstep (se 1 (by rfl) ⟨1000484, by rfl⟩ : syracuseStep 1333979 = 2000969) B2000969
theorem B3365999 : Blo 523799 3365999 := bstep (se 1 (by rfl) ⟨2524499, by rfl⟩ : syracuseStep 3365999 = 5048999) B5048999
theorem B1335143 : Blo 523799 1335143 := bstep (se 1 (by rfl) ⟨1001357, by rfl⟩ : syracuseStep 1335143 = 2002715) B2002715
theorem B1990595 : Blo 523799 1990595 := bstep (se 1 (by rfl) ⟨1492946, by rfl⟩ : syracuseStep 1990595 = 2985893) B2985893
theorem B1335791 : Blo 523799 1335791 := bstep (se 1 (by rfl) ⟨1001843, by rfl⟩ : syracuseStep 1335791 = 2003687) B2003687
theorem B1008169 : Blo 523799 1008169 := bstep (se 2 (by rfl) ⟨378063, by rfl⟩ : syracuseStep 1008169 = 756127) B756127
theorem B1991249 : Blo 523799 1991249 := bstep (se 2 (by rfl) ⟨746718, by rfl⟩ : syracuseStep 1991249 = 1493437) B1493437
theorem B1499759 : Blo 523799 1499759 := bstep (se 1 (by rfl) ⟨1124819, by rfl⟩ : syracuseStep 1499759 = 2249639) B2249639
theorem B2777723 : Blo 523799 2777723 := bstep (se 1 (by rfl) ⟨2083292, by rfl⟩ : syracuseStep 2777723 = 4166585) B4166585
theorem B4482803 : Blo 523799 4482803 := bstep (se 1 (by rfl) ⟨3362102, by rfl⟩ : syracuseStep 4482803 = 6724205) B6724205
theorem B27223897 : Blo 523799 27223897 := bstep (se 2 (by rfl) ⟨10208961, by rfl⟩ : syracuseStep 27223897 = 20417923) B20417923
theorem B24308369 : Blo 523799 24308369 := bstep (se 2 (by rfl) ⟨9115638, by rfl⟩ : syracuseStep 24308369 = 18231277) B18231277
theorem B749287 : Blo 523799 749287 := bstep (se 1 (by rfl) ⟨561965, by rfl⟩ : syracuseStep 749287 = 1123931) B1123931
theorem B6090727 : Blo 523799 6090727 := bstep (se 1 (by rfl) ⟨4568045, by rfl⟩ : syracuseStep 6090727 = 9136091) B9136091
theorem B946399 : Blo 523799 946399 := bstep (se 1 (by rfl) ⟨709799, by rfl⟩ : syracuseStep 946399 = 1419599) B1419599
theorem B11269057 : Blo 523799 11269057 := bstep (se 2 (by rfl) ⟨4225896, by rfl⟩ : syracuseStep 11269057 = 8451793) B8451793
theorem B3471335 : Blo 523799 3471335 := bstep (se 1 (by rfl) ⟨2603501, by rfl⟩ : syracuseStep 3471335 = 5207003) B5207003
theorem B9566531 : Blo 523799 9566531 := bstep (se 1 (by rfl) ⟨7174898, by rfl⟩ : syracuseStep 9566531 = 14349797) B14349797
theorem B4323881 : Blo 523799 4323881 := bstep (se 2 (by rfl) ⟨1621455, by rfl⟩ : syracuseStep 4323881 = 3242911) B3242911
theorem B5045273 : Blo 523799 5045273 := bstep (se 2 (by rfl) ⟨1891977, by rfl⟩ : syracuseStep 5045273 = 3783955) B3783955
theorem B1997855 : Blo 523799 1997855 := bstep (se 1 (by rfl) ⟨1498391, by rfl⟩ : syracuseStep 1997855 = 2996783) B2996783
theorem B5045615 : Blo 523799 5045615 := bstep (se 1 (by rfl) ⟨3784211, by rfl⟩ : syracuseStep 5045615 = 7568423) B7568423
theorem B523823 : Blo 523799 523823 := bstep (se 1 (by rfl) ⟨392867, by rfl⟩ : syracuseStep 523823 = 785735) B785735
theorem B786023 : Blo 523799 786023 := bstep (se 1 (by rfl) ⟨589517, by rfl⟩ : syracuseStep 786023 = 1179035) B1179035
theorem B524223 : Blo 523799 524223 := bstep (se 1 (by rfl) ⟨393167, by rfl⟩ : syracuseStep 524223 = 786335) B786335
theorem B589819 : Blo 523799 589819 := bstep (se 1 (by rfl) ⟨442364, by rfl⟩ : syracuseStep 589819 = 884729) B884729
theorem B589855 : Blo 523799 589855 := bstep (se 1 (by rfl) ⟨442391, by rfl⟩ : syracuseStep 589855 = 884783) B884783
theorem B884857 : Blo 523799 884857 := bstep (se 2 (by rfl) ⟨331821, by rfl⟩ : syracuseStep 884857 = 663643) B663643
theorem B1999039 : Blo 523799 1999039 := bstep (se 1 (by rfl) ⟨1499279, by rfl⟩ : syracuseStep 1999039 = 2998559) B2998559
theorem B1769687 : Blo 523799 1769687 := bstep (se 1 (by rfl) ⟨1327265, by rfl⟩ : syracuseStep 1769687 = 2654531) B2654531
theorem B590143 : Blo 523799 590143 := bstep (se 1 (by rfl) ⟨442607, by rfl⟩ : syracuseStep 590143 = 885215) B885215
theorem B524607 : Blo 523799 524607 := bstep (se 1 (by rfl) ⟨393455, by rfl⟩ : syracuseStep 524607 = 786911) B786911
theorem B786791 : Blo 523799 786791 := bstep (se 1 (by rfl) ⟨590093, by rfl⟩ : syracuseStep 786791 = 1180187) B1180187
theorem B787163 : Blo 523799 787163 := bstep (se 1 (by rfl) ⟨590372, by rfl⟩ : syracuseStep 787163 = 1180745) B1180745
theorem B1082087 : Blo 523799 1082087 := bstep (se 1 (by rfl) ⟨811565, by rfl⟩ : syracuseStep 1082087 = 1623131) B1623131
theorem B590719 : Blo 523799 590719 := bstep (se 1 (by rfl) ⟨443039, by rfl⟩ : syracuseStep 590719 = 886079) B886079
theorem B787439 : Blo 523799 787439 := bstep (se 1 (by rfl) ⟨590579, by rfl⟩ : syracuseStep 787439 = 1181159) B1181159
theorem B525339 : Blo 523799 525339 := bstep (se 1 (by rfl) ⟨394004, by rfl⟩ : syracuseStep 525339 = 788009) B788009
theorem B787577 : Blo 523799 787577 := bstep (se 2 (by rfl) ⟨295341, by rfl⟩ : syracuseStep 787577 = 590683) B590683
theorem B787823 : Blo 523799 787823 := bstep (se 1 (by rfl) ⟨590867, by rfl⟩ : syracuseStep 787823 = 1181735) B1181735
theorem B2000315 : Blo 523799 2000315 := bstep (se 1 (by rfl) ⟨1500236, by rfl⟩ : syracuseStep 2000315 = 3000473) B3000473
theorem B525927 : Blo 523799 525927 := bstep (se 1 (by rfl) ⟨394445, by rfl⟩ : syracuseStep 525927 = 788891) B788891
theorem B525951 : Blo 523799 525951 := bstep (se 1 (by rfl) ⟨394463, by rfl⟩ : syracuseStep 525951 = 788927) B788927
theorem B1771145 : Blo 523799 1771145 := bstep (se 2 (by rfl) ⟨664179, by rfl⟩ : syracuseStep 1771145 = 1328359) B1328359
theorem B788105 : Blo 523799 788105 := bstep (se 2 (by rfl) ⟨295539, by rfl⟩ : syracuseStep 788105 = 591079) B591079
theorem B788123 : Blo 523799 788123 := bstep (se 1 (by rfl) ⟨591092, by rfl⟩ : syracuseStep 788123 = 1182185) B1182185
theorem B526055 : Blo 523799 526055 := bstep (se 1 (by rfl) ⟨394541, by rfl⟩ : syracuseStep 526055 = 789083) B789083
theorem B526151 : Blo 523799 526151 := bstep (se 1 (by rfl) ⟨394613, by rfl⟩ : syracuseStep 526151 = 789227) B789227
theorem B788351 : Blo 523799 788351 := bstep (se 1 (by rfl) ⟨591263, by rfl⟩ : syracuseStep 788351 = 1182527) B1182527
theorem B886855 : Blo 523799 886855 := bstep (se 1 (by rfl) ⟨665141, by rfl⟩ : syracuseStep 886855 = 1330283) B1330283
theorem B788591 : Blo 523799 788591 := bstep (se 1 (by rfl) ⟨591443, by rfl⟩ : syracuseStep 788591 = 1182887) B1182887
theorem B788663 : Blo 523799 788663 := bstep (se 1 (by rfl) ⟨591497, by rfl⟩ : syracuseStep 788663 = 1182995) B1182995
theorem B14387453 : Blo 523799 14387453 := bstep (se 3 (by rfl) ⟨2697647, by rfl⟩ : syracuseStep 14387453 = 5395295) B5395295
theorem B887071 : Blo 523799 887071 := bstep (se 1 (by rfl) ⟨665303, by rfl⟩ : syracuseStep 887071 = 1330607) B1330607
theorem B1772009 : Blo 523799 1772009 := bstep (se 2 (by rfl) ⟨664503, by rfl⟩ : syracuseStep 1772009 = 1329007) B1329007
theorem B1804841 : Blo 523799 1804841 := bstep (se 2 (by rfl) ⟨676815, by rfl⟩ : syracuseStep 1804841 = 1353631) B1353631
theorem B527103 : Blo 523799 527103 := bstep (se 1 (by rfl) ⟨395327, by rfl⟩ : syracuseStep 527103 = 790655) B790655
theorem B5376901 : Blo 523799 5376901 := bstep (se 4 (by rfl) ⟨504084, by rfl⟩ : syracuseStep 5376901 = 1008169) B1008169
theorem B6720515 : Blo 523799 6720515 := bstep (se 1 (by rfl) ⟨5040386, by rfl⟩ : syracuseStep 6720515 = 10080773) B10080773
theorem B527387 : Blo 523799 527387 := bstep (se 1 (by rfl) ⟨395540, by rfl⟩ : syracuseStep 527387 = 791081) B791081
theorem B184650839 : Blo 523799 184650839 := bstep (se 1 (by rfl) ⟨138488129, by rfl⟩ : syracuseStep 184650839 = 276976259) B276976259
theorem B789815 : Blo 523799 789815 := bstep (se 1 (by rfl) ⟨592361, by rfl⟩ : syracuseStep 789815 = 1184723) B1184723
theorem B527679 : Blo 523799 527679 := bstep (se 1 (by rfl) ⟨395759, by rfl⟩ : syracuseStep 527679 = 791519) B791519
theorem B2002259 : Blo 523799 2002259 := bstep (se 1 (by rfl) ⟨1501694, by rfl⟩ : syracuseStep 2002259 = 3003389) B3003389
theorem B1183211 : Blo 523799 1183211 := bstep (se 1 (by rfl) ⟨887408, by rfl⟩ : syracuseStep 1183211 = 1774817) B1774817
theorem B888347 : Blo 523799 888347 := bstep (se 1 (by rfl) ⟨666260, by rfl⟩ : syracuseStep 888347 = 1332521) B1332521
theorem B790199 : Blo 523799 790199 := bstep (se 1 (by rfl) ⟨592649, by rfl⟩ : syracuseStep 790199 = 1185299) B1185299
theorem B1183463 : Blo 523799 1183463 := bstep (se 1 (by rfl) ⟨887597, by rfl⟩ : syracuseStep 1183463 = 1775195) B1775195
theorem B82120553 : Blo 523799 82120553 := bstep (se 2 (by rfl) ⟨30795207, by rfl⟩ : syracuseStep 82120553 = 61590415) B61590415
theorem B790751 : Blo 523799 790751 := bstep (se 1 (by rfl) ⟨593063, by rfl⟩ : syracuseStep 790751 = 1186127) B1186127
theorem B790847 : Blo 523799 790847 := bstep (se 1 (by rfl) ⟨593135, by rfl⟩ : syracuseStep 790847 = 1186271) B1186271
theorem B1708445 : Blo 523799 1708445 := bstep (se 3 (by rfl) ⟨320333, by rfl⟩ : syracuseStep 1708445 = 640667) B640667
theorem B1774007 : Blo 523799 1774007 := bstep (se 1 (by rfl) ⟨1330505, by rfl⟩ : syracuseStep 1774007 = 2661011) B2661011
theorem B889319 : Blo 523799 889319 := bstep (se 1 (by rfl) ⟨666989, by rfl⟩ : syracuseStep 889319 = 1333979) B1333979
theorem B791231 : Blo 523799 791231 := bstep (se 1 (by rfl) ⟨593423, by rfl⟩ : syracuseStep 791231 = 1186847) B1186847
theorem B791279 : Blo 523799 791279 := bstep (se 1 (by rfl) ⟨593459, by rfl⟩ : syracuseStep 791279 = 1186919) B1186919
theorem B791399 : Blo 523799 791399 := bstep (se 1 (by rfl) ⟨593549, by rfl⟩ : syracuseStep 791399 = 1187099) B1187099
theorem B890095 : Blo 523799 890095 := bstep (se 1 (by rfl) ⟨667571, by rfl⟩ : syracuseStep 890095 = 1335143) B1335143
theorem B890527 : Blo 523799 890527 := bstep (se 1 (by rfl) ⟨667895, by rfl⟩ : syracuseStep 890527 = 1335791) B1335791
theorem B3643177 : Blo 523799 3643177 := bstep (se 2 (by rfl) ⟨1366191, by rfl⟩ : syracuseStep 3643177 = 2732383) B2732383
theorem B1775951 : Blo 523799 1775951 := bstep (se 1 (by rfl) ⟨1331963, by rfl⟩ : syracuseStep 1775951 = 2663927) B2663927
theorem B1186217 : Blo 523799 1186217 := bstep (se 2 (by rfl) ⟨444831, by rfl⟩ : syracuseStep 1186217 = 889663) B889663
theorem B1776059 : Blo 523799 1776059 := bstep (se 1 (by rfl) ⟨1332044, by rfl⟩ : syracuseStep 1776059 = 2664089) B2664089
theorem B2988535 : Blo 523799 2988535 := bstep (se 1 (by rfl) ⟨2241401, by rfl⟩ : syracuseStep 2988535 = 4482803) B4482803
theorem B2661821 : Blo 523799 2661821 := bstep (se 3 (by rfl) ⟨499091, by rfl⟩ : syracuseStep 2661821 = 998183) B998183
theorem B1187297 : Blo 523799 1187297 := bstep (se 2 (by rfl) ⟨445236, by rfl⟩ : syracuseStep 1187297 = 890473) B890473
theorem B1121863 : Blo 523799 1121863 := bstep (se 1 (by rfl) ⟨841397, by rfl⟩ : syracuseStep 1121863 = 1682795) B1682795
theorem B532975 : Blo 523799 532975 := bstep (se 1 (by rfl) ⟨399731, by rfl⟩ : syracuseStep 532975 = 799463) B799463
theorem B2665223 : Blo 523799 2665223 := bstep (se 1 (by rfl) ⟨1998917, by rfl⟩ : syracuseStep 2665223 = 3997835) B3997835
theorem B12136085 : Blo 523799 12136085 := bstep (se 6 (by rfl) ⟨284439, by rfl⟩ : syracuseStep 12136085 = 568879) B568879
theorem B183873397 : Blo 523799 183873397 := bstep (se 5 (by rfl) ⟨8619065, by rfl⟩ : syracuseStep 183873397 = 17238131) B17238131
theorem B995503 : Blo 523799 995503 := bstep (se 1 (by rfl) ⟨746627, by rfl⟩ : syracuseStep 995503 = 1493255) B1493255
theorem B3979367 : Blo 523799 3979367 := bstep (se 1 (by rfl) ⟨2984525, by rfl⟩ : syracuseStep 3979367 = 5969051) B5969051
theorem B1325879 : Blo 523799 1325879 := bstep (se 1 (by rfl) ⟨994409, by rfl⟩ : syracuseStep 1325879 = 1988819) B1988819
theorem B2243999 : Blo 523799 2243999 := bstep (se 1 (by rfl) ⟨1682999, by rfl⟩ : syracuseStep 2243999 = 3365999) B3365999
theorem B3587561 : Blo 523799 3587561 := bstep (se 2 (by rfl) ⟨1345335, by rfl⟩ : syracuseStep 3587561 = 2690671) B2690671
theorem B999049 : Blo 523799 999049 := bstep (se 2 (by rfl) ⟨374643, by rfl⟩ : syracuseStep 999049 = 749287) B749287
theorem B1327063 : Blo 523799 1327063 := bstep (se 1 (by rfl) ⟨995297, by rfl⟩ : syracuseStep 1327063 = 1990595) B1990595
theorem B1261865 : Blo 523799 1261865 := bstep (se 2 (by rfl) ⟨473199, by rfl⟩ : syracuseStep 1261865 = 946399) B946399
theorem B24330557 : Blo 523799 24330557 := bstep (se 3 (by rfl) ⟨4561979, by rfl⟩ : syracuseStep 24330557 = 9123959) B9123959
theorem B1327499 : Blo 523799 1327499 := bstep (se 1 (by rfl) ⟨995624, by rfl⟩ : syracuseStep 1327499 = 1991249) B1991249
theorem B999839 : Blo 523799 999839 := bstep (se 1 (by rfl) ⟨749879, by rfl⟩ : syracuseStep 999839 = 1499759) B1499759
theorem B1851815 : Blo 523799 1851815 := bstep (se 1 (by rfl) ⟨1388861, by rfl⟩ : syracuseStep 1851815 = 2777723) B2777723
theorem B15025409 : Blo 523799 15025409 := bstep (se 2 (by rfl) ⟨5634528, by rfl⟩ : syracuseStep 15025409 = 11269057) B11269057
theorem B16205579 : Blo 523799 16205579 := bstep (se 1 (by rfl) ⟨12154184, by rfl⟩ : syracuseStep 16205579 = 24308369) B24308369
theorem B7194599 : Blo 523799 7194599 := bstep (se 1 (by rfl) ⟨5395949, by rfl⟩ : syracuseStep 7194599 = 10791899) B10791899
theorem B1493927 : Blo 523799 1493927 := bstep (se 1 (by rfl) ⟨1120445, by rfl⟩ : syracuseStep 1493927 = 2240891) B2240891
theorem B970459 : Blo 523799 970459 := bstep (se 1 (by rfl) ⟨727844, by rfl⟩ : syracuseStep 970459 = 1455689) B1455689
theorem B2314223 : Blo 523799 2314223 := bstep (se 1 (by rfl) ⟨1735667, by rfl⟩ : syracuseStep 2314223 = 3471335) B3471335
theorem B1495111 : Blo 523799 1495111 := bstep (se 1 (by rfl) ⟨1121333, by rfl⟩ : syracuseStep 1495111 = 2242667) B2242667
theorem B6377687 : Blo 523799 6377687 := bstep (se 1 (by rfl) ⟨4783265, by rfl⟩ : syracuseStep 6377687 = 9566531) B9566531
theorem B839975 : Blo 523799 839975 := bstep (se 1 (by rfl) ⟨629981, by rfl⟩ : syracuseStep 839975 = 1259963) B1259963
theorem B3363515 : Blo 523799 3363515 := bstep (se 1 (by rfl) ⟨2522636, by rfl⟩ : syracuseStep 3363515 = 5045273) B5045273
theorem B1331903 : Blo 523799 1331903 := bstep (se 1 (by rfl) ⟨998927, by rfl⟩ : syracuseStep 1331903 = 1997855) B1997855
theorem B3363743 : Blo 523799 3363743 := bstep (se 1 (by rfl) ⟨2522807, by rfl⟩ : syracuseStep 3363743 = 5045615) B5045615
theorem B2251243 : Blo 523799 2251243 := bstep (se 1 (by rfl) ⟨1688432, by rfl⟩ : syracuseStep 2251243 = 3376865) B3376865
theorem B3988601 : Blo 523799 3988601 := bstep (se 2 (by rfl) ⟨1495725, by rfl⟩ : syracuseStep 3988601 = 2991451) B2991451
theorem B1989791 : Blo 523799 1989791 := bstep (se 1 (by rfl) ⟨1492343, by rfl⟩ : syracuseStep 1989791 = 2984687) B2984687
theorem B65559935 : Blo 523799 65559935 := bstep (se 1 (by rfl) ⟨49169951, by rfl⟩ : syracuseStep 65559935 = 98339903) B98339903
theorem B36298529 : Blo 523799 36298529 := bstep (se 2 (by rfl) ⟨13611948, by rfl⟩ : syracuseStep 36298529 = 27223897) B27223897
theorem B1335599 : Blo 523799 1335599 := bstep (se 1 (by rfl) ⟨1001699, by rfl⟩ : syracuseStep 1335599 = 2003399) B2003399
theorem B1794383 : Blo 523799 1794383 := bstep (se 1 (by rfl) ⟨1345787, by rfl⟩ : syracuseStep 1794383 = 2691575) B2691575
theorem B3794363 : Blo 523799 3794363 := bstep (se 1 (by rfl) ⟨2845772, by rfl⟩ : syracuseStep 3794363 = 5691545) B5691545
theorem B11495789 : Blo 523799 11495789 := bstep (se 3 (by rfl) ⟨2155460, by rfl⟩ : syracuseStep 11495789 = 4310921) B4310921
theorem B8120969 : Blo 523799 8120969 := bstep (se 2 (by rfl) ⟨3045363, by rfl⟩ : syracuseStep 8120969 = 6090727) B6090727
theorem B27224747 : Blo 523799 27224747 := bstep (se 1 (by rfl) ⟨20418560, by rfl⟩ : syracuseStep 27224747 = 40837121) B40837121
theorem B5041277 : Blo 523799 5041277 := bstep (se 3 (by rfl) ⟨945239, by rfl⟩ : syracuseStep 5041277 = 1890479) B1890479
theorem B1601819 : Blo 523799 1601819 := bstep (se 1 (by rfl) ⟨1201364, by rfl⟩ : syracuseStep 1601819 = 2402729) B2402729
theorem B4813303 : Blo 523799 4813303 := bstep (se 1 (by rfl) ⟨3609977, by rfl⟩ : syracuseStep 4813303 = 7219955) B7219955
theorem B1275731 : Blo 523799 1275731 := bstep (se 1 (by rfl) ⟨956798, by rfl⟩ : syracuseStep 1275731 = 1913597) B1913597
theorem B7567499 : Blo 523799 7567499 := bstep (se 1 (by rfl) ⟨5675624, by rfl⟩ : syracuseStep 7567499 = 11351249) B11351249
theorem B2882587 : Blo 523799 2882587 := bstep (se 1 (by rfl) ⟨2161940, by rfl⟩ : syracuseStep 2882587 = 4323881) B4323881
theorem B9010439 : Blo 523799 9010439 := bstep (se 1 (by rfl) ⟨6757829, by rfl⟩ : syracuseStep 9010439 = 13515659) B13515659
theorem B14384719 : Blo 523799 14384719 := bstep (se 1 (by rfl) ⟨10788539, by rfl⟩ : syracuseStep 14384719 = 21577079) B21577079
theorem B524015 : Blo 523799 524015 := bstep (se 1 (by rfl) ⟨393011, by rfl⟩ : syracuseStep 524015 = 786023) B786023
theorem B9567989 : Blo 523799 9567989 := bstep (se 5 (by rfl) ⟨448499, by rfl⟩ : syracuseStep 9567989 = 896999) B896999
theorem B1998827 : Blo 523799 1998827 := bstep (se 1 (by rfl) ⟨1499120, by rfl⟩ : syracuseStep 1998827 = 2998241) B2998241
theorem B786425 : Blo 523799 786425 := bstep (se 2 (by rfl) ⟨294909, by rfl⟩ : syracuseStep 786425 = 589819) B589819
theorem B786473 : Blo 523799 786473 := bstep (se 2 (by rfl) ⟨294927, by rfl⟩ : syracuseStep 786473 = 589855) B589855
theorem B1179791 : Blo 523799 1179791 := bstep (se 1 (by rfl) ⟨884843, by rfl⟩ : syracuseStep 1179791 = 1769687) B1769687
theorem B1179809 : Blo 523799 1179809 := bstep (se 2 (by rfl) ⟨442428, by rfl⟩ : syracuseStep 1179809 = 884857) B884857
theorem B16220371 : Blo 523799 16220371 := bstep (se 1 (by rfl) ⟨12165278, by rfl⟩ : syracuseStep 16220371 = 24330557) B24330557
theorem B524527 : Blo 523799 524527 := bstep (se 1 (by rfl) ⟨393395, by rfl⟩ : syracuseStep 524527 = 786791) B786791
theorem B884999 : Blo 523799 884999 := bstep (se 1 (by rfl) ⟨663749, by rfl⟩ : syracuseStep 884999 = 1327499) B1327499
theorem B786857 : Blo 523799 786857 := bstep (se 2 (by rfl) ⟨295071, by rfl⟩ : syracuseStep 786857 = 590143) B590143
theorem B524775 : Blo 523799 524775 := bstep (se 1 (by rfl) ⟨393581, by rfl⟩ : syracuseStep 524775 = 787163) B787163
theorem B721391 : Blo 523799 721391 := bstep (se 1 (by rfl) ⟨541043, by rfl⟩ : syracuseStep 721391 = 1082087) B1082087
theorem B524959 : Blo 523799 524959 := bstep (se 1 (by rfl) ⟨393719, by rfl⟩ : syracuseStep 524959 = 787439) B787439
theorem B525051 : Blo 523799 525051 := bstep (se 1 (by rfl) ⟨393788, by rfl⟩ : syracuseStep 525051 = 787577) B787577
theorem B525215 : Blo 523799 525215 := bstep (se 1 (by rfl) ⟨393911, by rfl⟩ : syracuseStep 525215 = 787823) B787823
theorem B1180763 : Blo 523799 1180763 := bstep (se 1 (by rfl) ⟨885572, by rfl⟩ : syracuseStep 1180763 = 1771145) B1771145
theorem B525403 : Blo 523799 525403 := bstep (se 1 (by rfl) ⟨394052, by rfl⟩ : syracuseStep 525403 = 788105) B788105
theorem B525415 : Blo 523799 525415 := bstep (se 1 (by rfl) ⟨394061, by rfl⟩ : syracuseStep 525415 = 788123) B788123
theorem B787625 : Blo 523799 787625 := bstep (se 2 (by rfl) ⟨295359, by rfl⟩ : syracuseStep 787625 = 590719) B590719
theorem B525567 : Blo 523799 525567 := bstep (se 1 (by rfl) ⟨394175, by rfl⟩ : syracuseStep 525567 = 788351) B788351
theorem B525727 : Blo 523799 525727 := bstep (se 1 (by rfl) ⟨394295, by rfl⟩ : syracuseStep 525727 = 788591) B788591
theorem B525775 : Blo 523799 525775 := bstep (se 1 (by rfl) ⟨394331, by rfl⟩ : syracuseStep 525775 = 788663) B788663
theorem B1181339 : Blo 523799 1181339 := bstep (se 1 (by rfl) ⟨886004, by rfl⟩ : syracuseStep 1181339 = 1772009) B1772009
theorem B526543 : Blo 523799 526543 := bstep (se 1 (by rfl) ⟨394907, by rfl⟩ : syracuseStep 526543 = 789815) B789815
theorem B788807 : Blo 523799 788807 := bstep (se 1 (by rfl) ⟨591605, by rfl⟩ : syracuseStep 788807 = 1183211) B1183211
theorem B592231 : Blo 523799 592231 := bstep (se 1 (by rfl) ⟨444173, by rfl⟩ : syracuseStep 592231 = 888347) B888347
theorem B526799 : Blo 523799 526799 := bstep (se 1 (by rfl) ⟨395099, by rfl⟩ : syracuseStep 526799 = 790199) B790199
theorem B788975 : Blo 523799 788975 := bstep (se 1 (by rfl) ⟨591731, by rfl⟩ : syracuseStep 788975 = 1183463) B1183463
theorem B1542815 : Blo 523799 1542815 := bstep (se 1 (by rfl) ⟨1157111, by rfl⟩ : syracuseStep 1542815 = 2314223) B2314223
theorem B1182473 : Blo 523799 1182473 := bstep (se 2 (by rfl) ⟨443427, by rfl⟩ : syracuseStep 1182473 = 886855) B886855
theorem B527167 : Blo 523799 527167 := bstep (se 1 (by rfl) ⟨395375, by rfl⟩ : syracuseStep 527167 = 790751) B790751
theorem B527231 : Blo 523799 527231 := bstep (se 1 (by rfl) ⟨395423, by rfl⟩ : syracuseStep 527231 = 790847) B790847
theorem B1182671 : Blo 523799 1182671 := bstep (se 1 (by rfl) ⟨887003, by rfl⟩ : syracuseStep 1182671 = 1774007) B1774007
theorem B592879 : Blo 523799 592879 := bstep (se 1 (by rfl) ⟨444659, by rfl⟩ : syracuseStep 592879 = 889319) B889319
theorem B1182761 : Blo 523799 1182761 := bstep (se 2 (by rfl) ⟨443535, by rfl⟩ : syracuseStep 1182761 = 887071) B887071
theorem B887935 : Blo 523799 887935 := bstep (se 1 (by rfl) ⟨665951, by rfl⟩ : syracuseStep 887935 = 1331903) B1331903
theorem B527487 : Blo 523799 527487 := bstep (se 1 (by rfl) ⟨395615, by rfl⟩ : syracuseStep 527487 = 791231) B791231
theorem B527519 : Blo 523799 527519 := bstep (se 1 (by rfl) ⟨395639, by rfl⟩ : syracuseStep 527519 = 791279) B791279
theorem B527599 : Blo 523799 527599 := bstep (se 1 (by rfl) ⟨395699, by rfl⟩ : syracuseStep 527599 = 791399) B791399
theorem B1183967 : Blo 523799 1183967 := bstep (se 1 (by rfl) ⟨887975, by rfl⟩ : syracuseStep 1183967 = 1775951) B1775951
theorem B790811 : Blo 523799 790811 := bstep (se 1 (by rfl) ⟨593108, by rfl⟩ : syracuseStep 790811 = 1186217) B1186217
theorem B1184039 : Blo 523799 1184039 := bstep (se 1 (by rfl) ⟨888029, by rfl⟩ : syracuseStep 1184039 = 1776059) B1776059
theorem B2659067 : Blo 523799 2659067 := bstep (se 1 (by rfl) ⟨1994300, by rfl⟩ : syracuseStep 2659067 = 3988601) B3988601
theorem B1774547 : Blo 523799 1774547 := bstep (se 1 (by rfl) ⟨1330910, by rfl⟩ : syracuseStep 1774547 = 2661821) B2661821
theorem B791531 : Blo 523799 791531 := bstep (se 1 (by rfl) ⟨593648, by rfl⟩ : syracuseStep 791531 = 1187297) B1187297
theorem B890399 : Blo 523799 890399 := bstep (se 1 (by rfl) ⟨667799, by rfl⟩ : syracuseStep 890399 = 1335599) B1335599
theorem B2529575 : Blo 523799 2529575 := bstep (se 1 (by rfl) ⟨1897181, by rfl⟩ : syracuseStep 2529575 = 3794363) B3794363
theorem B1186793 : Blo 523799 1186793 := bstep (se 2 (by rfl) ⟨445047, by rfl⟩ : syracuseStep 1186793 = 890095) B890095
theorem B5413979 : Blo 523799 5413979 := bstep (se 1 (by rfl) ⟨4060484, by rfl⟩ : syracuseStep 5413979 = 8120969) B8120969
theorem B1776815 : Blo 523799 1776815 := bstep (se 1 (by rfl) ⟨1332611, by rfl⟩ : syracuseStep 1776815 = 2665223) B2665223
theorem B1187369 : Blo 523799 1187369 := bstep (se 2 (by rfl) ⟨445263, by rfl⟩ : syracuseStep 1187369 = 890527) B890527
theorem B4857569 : Blo 523799 4857569 := bstep (se 2 (by rfl) ⟨1821588, by rfl⟩ : syracuseStep 4857569 = 3643177) B3643177
theorem B13607797 : Blo 523799 13607797 := bstep (se 5 (by rfl) ⟨637865, by rfl⟩ : syracuseStep 13607797 = 1275731) B1275731
theorem B3843449 : Blo 523799 3843449 := bstep (se 2 (by rfl) ⟨1441293, by rfl⟩ : syracuseStep 3843449 = 2882587) B2882587
theorem B19179625 : Blo 523799 19179625 := bstep (se 2 (by rfl) ⟨7192359, by rfl⟩ : syracuseStep 19179625 = 14384719) B14384719
theorem B6006959 : Blo 523799 6006959 := bstep (se 1 (by rfl) ⟨4505219, by rfl⟩ : syracuseStep 6006959 = 9010439) B9010439
theorem B2665385 : Blo 523799 2665385 := bstep (se 2 (by rfl) ⟨999519, by rfl⟩ : syracuseStep 2665385 = 1999039) B1999039
theorem B666559 : Blo 523799 666559 := bstep (se 1 (by rfl) ⟨499919, by rfl⟩ : syracuseStep 666559 = 999839) B999839
theorem B2239933 : Blo 523799 2239933 := bstep (se 3 (by rfl) ⟨419987, by rfl⟩ : syracuseStep 2239933 = 839975) B839975
theorem B4796399 : Blo 523799 4796399 := bstep (se 1 (by rfl) ⟨3597299, by rfl⟩ : syracuseStep 4796399 = 7194599) B7194599
theorem B995951 : Blo 523799 995951 := bstep (se 1 (by rfl) ⟨746963, by rfl⟩ : syracuseStep 995951 = 1493927) B1493927
theorem B2242343 : Blo 523799 2242343 := bstep (se 1 (by rfl) ⟨1681757, by rfl⟩ : syracuseStep 2242343 = 3363515) B3363515
theorem B2242495 : Blo 523799 2242495 := bstep (se 1 (by rfl) ⟨1681871, by rfl⟩ : syracuseStep 2242495 = 3363743) B3363743
theorem B1326527 : Blo 523799 1326527 := bstep (se 1 (by rfl) ⟨994895, by rfl⟩ : syracuseStep 1326527 = 1989791) B1989791
theorem B24199019 : Blo 523799 24199019 := bstep (se 1 (by rfl) ⟨18149264, by rfl⟩ : syracuseStep 24199019 = 36298529) B36298529
theorem B524283 : Blo 523799 524283 := bstep (se 1 (by rfl) ⟨393212, by rfl⟩ : syracuseStep 524283 = 786425) B786425
theorem B1196255 : Blo 523799 1196255 := bstep (se 1 (by rfl) ⟨897191, by rfl⟩ : syracuseStep 1196255 = 1794383) B1794383
theorem B1327337 : Blo 523799 1327337 := bstep (se 2 (by rfl) ⟨497751, by rfl⟩ : syracuseStep 1327337 = 995503) B995503
theorem B3360851 : Blo 523799 3360851 := bstep (se 1 (by rfl) ⟨2520638, by rfl⟩ : syracuseStep 3360851 = 5041277) B5041277
theorem B1067879 : Blo 523799 1067879 := bstep (se 1 (by rfl) ⟨800909, by rfl⟩ : syracuseStep 1067879 = 1601819) B1601819
theorem B3001657 : Blo 523799 3001657 := bstep (se 2 (by rfl) ⟨1125621, by rfl⟩ : syracuseStep 3001657 = 2251243) B2251243
theorem B3984713 : Blo 523799 3984713 := bstep (se 2 (by rfl) ⟨1494267, by rfl⟩ : syracuseStep 3984713 = 2988535) B2988535
theorem B1495817 : Blo 523799 1495817 := bstep (se 2 (by rfl) ⟨560931, by rfl⟩ : syracuseStep 1495817 = 1121863) B1121863
theorem B1332065 : Blo 523799 1332065 := bstep (se 2 (by rfl) ⟨499524, by rfl⟩ : syracuseStep 1332065 = 999049) B999049
theorem B1495999 : Blo 523799 1495999 := bstep (se 1 (by rfl) ⟨1121999, by rfl⟩ : syracuseStep 1495999 = 2243999) B2243999
theorem B6378659 : Blo 523799 6378659 := bstep (se 1 (by rfl) ⟨4783994, by rfl⟩ : syracuseStep 6378659 = 9567989) B9567989
theorem B1332551 : Blo 523799 1332551 := bstep (se 1 (by rfl) ⟨999413, by rfl⟩ : syracuseStep 1332551 = 1998827) B1998827
theorem B1234543 : Blo 523799 1234543 := bstep (se 1 (by rfl) ⟨925907, by rfl⟩ : syracuseStep 1234543 = 1851815) B1851815
theorem B710633 : Blo 523799 710633 := bstep (se 2 (by rfl) ⟨266487, by rfl⟩ : syracuseStep 710633 = 532975) B532975
theorem B3364973 : Blo 523799 3364973 := bstep (se 3 (by rfl) ⟨630932, by rfl⟩ : syracuseStep 3364973 = 1261865) B1261865
theorem B10016939 : Blo 523799 10016939 := bstep (se 1 (by rfl) ⟨7512704, by rfl⟩ : syracuseStep 10016939 = 15025409) B15025409
theorem B1333543 : Blo 523799 1333543 := bstep (se 1 (by rfl) ⟨1000157, by rfl⟩ : syracuseStep 1333543 = 2000315) B2000315
theorem B10803719 : Blo 523799 10803719 := bstep (se 1 (by rfl) ⟨8102789, by rfl⟩ : syracuseStep 10803719 = 16205579) B16205579
theorem B9591635 : Blo 523799 9591635 := bstep (se 1 (by rfl) ⟨7193726, by rfl⟩ : syracuseStep 9591635 = 14387453) B14387453
theorem B1203227 : Blo 523799 1203227 := bstep (se 1 (by rfl) ⟨902420, by rfl⟩ : syracuseStep 1203227 = 1804841) B1804841
theorem B4480343 : Blo 523799 4480343 := bstep (se 1 (by rfl) ⟨3360257, by rfl⟩ : syracuseStep 4480343 = 6720515) B6720515
theorem B123100559 : Blo 523799 123100559 := bstep (se 1 (by rfl) ⟨92325419, by rfl⟩ : syracuseStep 123100559 = 184650839) B184650839
theorem B1334839 : Blo 523799 1334839 := bstep (se 1 (by rfl) ⟨1001129, by rfl⟩ : syracuseStep 1334839 = 2002259) B2002259
theorem B54747035 : Blo 523799 54747035 := bstep (se 1 (by rfl) ⟨41060276, by rfl⟩ : syracuseStep 54747035 = 82120553) B82120553
theorem B4251791 : Blo 523799 4251791 := bstep (se 1 (by rfl) ⟨3188843, by rfl⟩ : syracuseStep 4251791 = 6377687) B6377687
theorem B1138963 : Blo 523799 1138963 := bstep (se 1 (by rfl) ⟨854222, by rfl⟩ : syracuseStep 1138963 = 1708445) B1708445
theorem B7169201 : Blo 523799 7169201 := bstep (se 2 (by rfl) ⟨2688450, by rfl⟩ : syracuseStep 7169201 = 5376901) B5376901
theorem B20703125 : Blo 523799 20703125 := bstep (se 6 (by rfl) ⟨485229, by rfl⟩ : syracuseStep 20703125 = 970459) B970459
theorem B43706623 : Blo 523799 43706623 := bstep (se 1 (by rfl) ⟨32779967, by rfl⟩ : syracuseStep 43706623 = 65559935) B65559935
theorem B245164529 : Blo 523799 245164529 := bstep (se 2 (by rfl) ⟨91936698, by rfl⟩ : syracuseStep 245164529 = 183873397) B183873397
theorem B1993481 : Blo 523799 1993481 := bstep (se 2 (by rfl) ⟨747555, by rfl⟩ : syracuseStep 1993481 = 1495111) B1495111
theorem B6417737 : Blo 523799 6417737 := bstep (se 2 (by rfl) ⟨2406651, by rfl⟩ : syracuseStep 6417737 = 4813303) B4813303
theorem B7663859 : Blo 523799 7663859 := bstep (se 1 (by rfl) ⟨5747894, by rfl⟩ : syracuseStep 7663859 = 11495789) B11495789
theorem B18149831 : Blo 523799 18149831 := bstep (se 1 (by rfl) ⟨13612373, by rfl⟩ : syracuseStep 18149831 = 27224747) B27224747
theorem B8090723 : Blo 523799 8090723 := bstep (se 1 (by rfl) ⟨6068042, by rfl⟩ : syracuseStep 8090723 = 12136085) B12136085
theorem B2652911 : Blo 523799 2652911 := bstep (se 1 (by rfl) ⟨1989683, by rfl⟩ : syracuseStep 2652911 = 3979367) B3979367
theorem B5044999 : Blo 523799 5044999 := bstep (se 1 (by rfl) ⟨3783749, by rfl⟩ : syracuseStep 5044999 = 7567499) B7567499
theorem B883919 : Blo 523799 883919 := bstep (se 1 (by rfl) ⟨662939, by rfl⟩ : syracuseStep 883919 = 1325879) B1325879
theorem B2391707 : Blo 523799 2391707 := bstep (se 1 (by rfl) ⟨1793780, by rfl⟩ : syracuseStep 2391707 = 3587561) B3587561
theorem B1769417 : Blo 523799 1769417 := bstep (se 2 (by rfl) ⟨663531, by rfl⟩ : syracuseStep 1769417 = 1327063) B1327063
theorem B524315 : Blo 523799 524315 := bstep (se 1 (by rfl) ⟨393236, by rfl⟩ : syracuseStep 524315 = 786473) B786473
theorem B786527 : Blo 523799 786527 := bstep (se 1 (by rfl) ⟨589895, by rfl⟩ : syracuseStep 786527 = 1179791) B1179791
theorem B786539 : Blo 523799 786539 := bstep (se 1 (by rfl) ⟨589904, by rfl⟩ : syracuseStep 786539 = 1179809) B1179809
theorem B884891 : Blo 523799 884891 := bstep (se 1 (by rfl) ⟨663668, by rfl⟩ : syracuseStep 884891 = 1327337) B1327337
theorem B589999 : Blo 523799 589999 := bstep (se 1 (by rfl) ⟨442499, by rfl⟩ : syracuseStep 589999 = 884999) B884999
theorem B21627161 : Blo 523799 21627161 := bstep (se 2 (by rfl) ⟨8110185, by rfl⟩ : syracuseStep 21627161 = 16220371) B16220371
theorem B524571 : Blo 523799 524571 := bstep (se 1 (by rfl) ⟨393428, by rfl⟩ : syracuseStep 524571 = 786857) B786857
theorem B787175 : Blo 523799 787175 := bstep (se 1 (by rfl) ⟨590381, by rfl⟩ : syracuseStep 787175 = 1180763) B1180763
theorem B525083 : Blo 523799 525083 := bstep (se 1 (by rfl) ⟨393812, by rfl⟩ : syracuseStep 525083 = 787625) B787625
theorem B787559 : Blo 523799 787559 := bstep (se 1 (by rfl) ⟨590669, by rfl⟩ : syracuseStep 787559 = 1181339) B1181339
theorem B525871 : Blo 523799 525871 := bstep (se 1 (by rfl) ⟨394403, by rfl⟩ : syracuseStep 525871 = 788807) B788807
theorem B525983 : Blo 523799 525983 := bstep (se 1 (by rfl) ⟨394487, by rfl⟩ : syracuseStep 525983 = 788975) B788975
theorem B788315 : Blo 523799 788315 := bstep (se 1 (by rfl) ⟨591236, by rfl⟩ : syracuseStep 788315 = 1182473) B1182473
theorem B788447 : Blo 523799 788447 := bstep (se 1 (by rfl) ⟨591335, by rfl⟩ : syracuseStep 788447 = 1182671) B1182671
theorem B788507 : Blo 523799 788507 := bstep (se 1 (by rfl) ⟨591380, by rfl⟩ : syracuseStep 788507 = 1182761) B1182761
theorem B2656475 : Blo 523799 2656475 := bstep (se 1 (by rfl) ⟨1992356, by rfl⟩ : syracuseStep 2656475 = 3984713) B3984713
theorem B789311 : Blo 523799 789311 := bstep (se 1 (by rfl) ⟨591983, by rfl⟩ : syracuseStep 789311 = 1183967) B1183967
theorem B527207 : Blo 523799 527207 := bstep (se 1 (by rfl) ⟨395405, by rfl⟩ : syracuseStep 527207 = 790811) B790811
theorem B789359 : Blo 523799 789359 := bstep (se 1 (by rfl) ⟨592019, by rfl⟩ : syracuseStep 789359 = 1184039) B1184039
theorem B789641 : Blo 523799 789641 := bstep (se 2 (by rfl) ⟨296115, by rfl⟩ : syracuseStep 789641 = 592231) B592231
theorem B1772711 : Blo 523799 1772711 := bstep (se 1 (by rfl) ⟨1329533, by rfl⟩ : syracuseStep 1772711 = 2659067) B2659067
theorem B888043 : Blo 523799 888043 := bstep (se 1 (by rfl) ⟨666032, by rfl⟩ : syracuseStep 888043 = 1332065) B1332065
theorem B1183031 : Blo 523799 1183031 := bstep (se 1 (by rfl) ⟨887273, by rfl⟩ : syracuseStep 1183031 = 1774547) B1774547
theorem B527687 : Blo 523799 527687 := bstep (se 1 (by rfl) ⟨395765, by rfl⟩ : syracuseStep 527687 = 791531) B791531
theorem B888367 : Blo 523799 888367 := bstep (se 1 (by rfl) ⟨666275, by rfl⟩ : syracuseStep 888367 = 1332551) B1332551
theorem B593599 : Blo 523799 593599 := bstep (se 1 (by rfl) ⟨445199, by rfl⟩ : syracuseStep 593599 = 890399) B890399
theorem B888745 : Blo 523799 888745 := bstep (se 2 (by rfl) ⟨333279, by rfl⟩ : syracuseStep 888745 = 666559) B666559
theorem B790505 : Blo 523799 790505 := bstep (se 2 (by rfl) ⟨296439, by rfl⟩ : syracuseStep 790505 = 592879) B592879
theorem B1183913 : Blo 523799 1183913 := bstep (se 2 (by rfl) ⟨443967, by rfl⟩ : syracuseStep 1183913 = 887935) B887935
theorem B4002209 : Blo 523799 4002209 := bstep (se 2 (by rfl) ⟨1500828, by rfl⟩ : syracuseStep 4002209 = 3001657) B3001657
theorem B6394423 : Blo 523799 6394423 := bstep (se 1 (by rfl) ⟨4795817, by rfl⟩ : syracuseStep 6394423 = 9591635) B9591635
theorem B2986577 : Blo 523799 2986577 := bstep (se 2 (by rfl) ⟨1119966, by rfl⟩ : syracuseStep 2986577 = 2239933) B2239933
theorem B791195 : Blo 523799 791195 := bstep (se 1 (by rfl) ⟨593396, by rfl⟩ : syracuseStep 791195 = 1186793) B1186793
theorem B1184543 : Blo 523799 1184543 := bstep (se 1 (by rfl) ⟨888407, by rfl⟩ : syracuseStep 1184543 = 1776815) B1776815
theorem B2986895 : Blo 523799 2986895 := bstep (se 1 (by rfl) ⟨2240171, by rfl⟩ : syracuseStep 2986895 = 4480343) B4480343
theorem B791579 : Blo 523799 791579 := bstep (se 1 (by rfl) ⟨593684, by rfl⟩ : syracuseStep 791579 = 1187369) B1187369
theorem B2562299 : Blo 523799 2562299 := bstep (se 1 (by rfl) ⟨1921724, by rfl⟩ : syracuseStep 2562299 = 3843449) B3843449
theorem B13802083 : Blo 523799 13802083 := bstep (se 1 (by rfl) ⟨10351562, by rfl⟩ : syracuseStep 13802083 = 20703125) B20703125
theorem B28809917 : Blo 523799 28809917 := bstep (se 3 (by rfl) ⟨5401859, by rfl⟩ : syracuseStep 28809917 = 10803719) B10803719
theorem B4004639 : Blo 523799 4004639 := bstep (se 1 (by rfl) ⟨3003479, by rfl⟩ : syracuseStep 4004639 = 6006959) B6006959
theorem B1776923 : Blo 523799 1776923 := bstep (se 1 (by rfl) ⟨1332692, by rfl⟩ : syracuseStep 1776923 = 2665385) B2665385
theorem B1646057 : Blo 523799 1646057 := bstep (se 2 (by rfl) ⟨617271, by rfl⟩ : syracuseStep 1646057 = 1234543) B1234543
theorem B2989993 : Blo 523799 2989993 := bstep (se 2 (by rfl) ⟨1121247, by rfl⟩ : syracuseStep 2989993 = 2242495) B2242495
theorem B12099887 : Blo 523799 12099887 := bstep (se 1 (by rfl) ⟨9074915, by rfl⟩ : syracuseStep 12099887 = 18149831) B18149831
theorem B1778057 : Blo 523799 1778057 := bstep (se 2 (by rfl) ⟨666771, by rfl⟩ : syracuseStep 1778057 = 1333543) B1333543
theorem B663967 : Blo 523799 663967 := bstep (se 1 (by rfl) ⟨497975, by rfl⟩ : syracuseStep 663967 = 995951) B995951
theorem B6726665 : Blo 523799 6726665 := bstep (se 2 (by rfl) ⟨2522499, by rfl⟩ : syracuseStep 6726665 = 5044999) B5044999
theorem B1779785 : Blo 523799 1779785 := bstep (se 2 (by rfl) ⟨667419, by rfl⟩ : syracuseStep 1779785 = 1334839) B1334839
theorem B16132679 : Blo 523799 16132679 := bstep (se 1 (by rfl) ⟨12099509, by rfl⟩ : syracuseStep 16132679 = 24199019) B24199019
theorem B1518617 : Blo 523799 1518617 := bstep (se 2 (by rfl) ⟨569481, by rfl⟩ : syracuseStep 1518617 = 1138963) B1138963
theorem B3190013 : Blo 523799 3190013 := bstep (se 3 (by rfl) ⟨598127, by rfl⟩ : syracuseStep 3190013 = 1196255) B1196255
theorem B2240567 : Blo 523799 2240567 := bstep (se 1 (by rfl) ⟨1680425, by rfl⟩ : syracuseStep 2240567 = 3360851) B3360851
theorem B1028543 : Blo 523799 1028543 := bstep (se 1 (by rfl) ⟨771407, by rfl⟩ : syracuseStep 1028543 = 1542815) B1542815
theorem B25572833 : Blo 523799 25572833 := bstep (se 2 (by rfl) ⟨9589812, by rfl⟩ : syracuseStep 25572833 = 19179625) B19179625
theorem B21575261 : Blo 523799 21575261 := bstep (se 3 (by rfl) ⟨4045361, by rfl⟩ : syracuseStep 21575261 = 8090723) B8090723
theorem B58275497 : Blo 523799 58275497 := bstep (se 2 (by rfl) ⟨21853311, by rfl⟩ : syracuseStep 58275497 = 43706623) B43706623
theorem B997211 : Blo 523799 997211 := bstep (se 1 (by rfl) ⟨747908, by rfl⟩ : syracuseStep 997211 = 1495817) B1495817
theorem B2243315 : Blo 523799 2243315 := bstep (se 1 (by rfl) ⟨1682486, by rfl⟩ : syracuseStep 2243315 = 3364973) B3364973
theorem B1686383 : Blo 523799 1686383 := bstep (se 1 (by rfl) ⟨1264787, by rfl⟩ : syracuseStep 1686383 = 2529575) B2529575
theorem B802151 : Blo 523799 802151 := bstep (se 1 (by rfl) ⟨601613, by rfl⟩ : syracuseStep 802151 = 1203227) B1203227
theorem B82067039 : Blo 523799 82067039 := bstep (se 1 (by rfl) ⟨61550279, by rfl⟩ : syracuseStep 82067039 = 123100559) B123100559
theorem B2834527 : Blo 523799 2834527 := bstep (se 1 (by rfl) ⟨2125895, by rfl⟩ : syracuseStep 2834527 = 4251791) B4251791
theorem B1328987 : Blo 523799 1328987 := bstep (se 1 (by rfl) ⟨996740, by rfl⟩ : syracuseStep 1328987 = 1993481) B1993481
theorem B4278491 : Blo 523799 4278491 := bstep (se 1 (by rfl) ⟨3208868, by rfl⟩ : syracuseStep 4278491 = 6417737) B6417737
theorem B3197599 : Blo 523799 3197599 := bstep (se 1 (by rfl) ⟨2398199, by rfl⟩ : syracuseStep 3197599 = 4796399) B4796399
theorem B14437277 : Blo 523799 14437277 := bstep (se 3 (by rfl) ⟨2706989, by rfl⟩ : syracuseStep 14437277 = 5413979) B5413979
theorem B1494895 : Blo 523799 1494895 := bstep (se 1 (by rfl) ⟨1121171, by rfl⟩ : syracuseStep 1494895 = 2242343) B2242343
theorem B6377885 : Blo 523799 6377885 := bstep (se 3 (by rfl) ⟨1195853, by rfl⟩ : syracuseStep 6377885 = 2391707) B2391707
theorem B18143729 : Blo 523799 18143729 := bstep (se 2 (by rfl) ⟨6803898, by rfl⟩ : syracuseStep 18143729 = 13607797) B13607797
theorem B711919 : Blo 523799 711919 := bstep (se 1 (by rfl) ⟨533939, by rfl⟩ : syracuseStep 711919 = 1067879) B1067879
theorem B4252439 : Blo 523799 4252439 := bstep (se 1 (by rfl) ⟨3189329, by rfl⟩ : syracuseStep 4252439 = 6378659) B6378659
theorem B6677959 : Blo 523799 6677959 := bstep (se 1 (by rfl) ⟨5008469, by rfl⟩ : syracuseStep 6677959 = 10016939) B10016939
theorem B3238379 : Blo 523799 3238379 := bstep (se 1 (by rfl) ⟨2428784, by rfl⟩ : syracuseStep 3238379 = 4857569) B4857569
theorem B7694837 : Blo 523799 7694837 := bstep (se 5 (by rfl) ⟨360695, by rfl⟩ : syracuseStep 7694837 = 721391) B721391
theorem B36498023 : Blo 523799 36498023 := bstep (se 1 (by rfl) ⟨27373517, by rfl⟩ : syracuseStep 36498023 = 54747035) B54747035
theorem B1895021 : Blo 523799 1895021 := bstep (se 3 (by rfl) ⟨355316, by rfl⟩ : syracuseStep 1895021 = 710633) B710633
theorem B4779467 : Blo 523799 4779467 := bstep (se 1 (by rfl) ⟨3584600, by rfl⟩ : syracuseStep 4779467 = 7169201) B7169201
theorem B1994665 : Blo 523799 1994665 := bstep (se 2 (by rfl) ⟨747999, by rfl⟩ : syracuseStep 1994665 = 1495999) B1495999
theorem B163443019 : Blo 523799 163443019 := bstep (se 1 (by rfl) ⟨122582264, by rfl⟩ : syracuseStep 163443019 = 245164529) B245164529
theorem B5109239 : Blo 523799 5109239 := bstep (se 1 (by rfl) ⟨3831929, by rfl⟩ : syracuseStep 5109239 = 7663859) B7663859
theorem B1768607 : Blo 523799 1768607 := bstep (se 1 (by rfl) ⟨1326455, by rfl⟩ : syracuseStep 1768607 = 2652911) B2652911
theorem B589279 : Blo 523799 589279 := bstep (se 1 (by rfl) ⟨441959, by rfl⟩ : syracuseStep 589279 = 883919) B883919
theorem B884351 : Blo 523799 884351 := bstep (se 1 (by rfl) ⟨663263, by rfl⟩ : syracuseStep 884351 = 1326527) B1326527
theorem B1179611 : Blo 523799 1179611 := bstep (se 1 (by rfl) ⟨884708, by rfl⟩ : syracuseStep 1179611 = 1769417) B1769417
theorem B524351 : Blo 523799 524351 := bstep (se 1 (by rfl) ⟨393263, by rfl⟩ : syracuseStep 524351 = 786527) B786527
theorem B524359 : Blo 523799 524359 := bstep (se 1 (by rfl) ⟨393269, by rfl⟩ : syracuseStep 524359 = 786539) B786539
theorem B589927 : Blo 523799 589927 := bstep (se 1 (by rfl) ⟨442445, by rfl⟩ : syracuseStep 589927 = 884891) B884891
theorem B14418107 : Blo 523799 14418107 := bstep (se 1 (by rfl) ⟨10813580, by rfl⟩ : syracuseStep 14418107 = 21627161) B21627161
theorem B786665 : Blo 523799 786665 := bstep (se 2 (by rfl) ⟨294999, by rfl⟩ : syracuseStep 786665 = 589999) B589999
theorem B524783 : Blo 523799 524783 := bstep (se 1 (by rfl) ⟨393587, by rfl⟩ : syracuseStep 524783 = 787175) B787175
theorem B885289 : Blo 523799 885289 := bstep (se 2 (by rfl) ⟨331983, by rfl⟩ : syracuseStep 885289 = 663967) B663967
theorem B525039 : Blo 523799 525039 := bstep (se 1 (by rfl) ⟨393779, by rfl⟩ : syracuseStep 525039 = 787559) B787559
theorem B885991 : Blo 523799 885991 := bstep (se 1 (by rfl) ⟨664493, by rfl⟩ : syracuseStep 885991 = 1328987) B1328987
theorem B525543 : Blo 523799 525543 := bstep (se 1 (by rfl) ⟨394157, by rfl⟩ : syracuseStep 525543 = 788315) B788315
theorem B525631 : Blo 523799 525631 := bstep (se 1 (by rfl) ⟨394223, by rfl⟩ : syracuseStep 525631 = 788447) B788447
theorem B525671 : Blo 523799 525671 := bstep (se 1 (by rfl) ⟨394253, by rfl⟩ : syracuseStep 525671 = 788507) B788507
theorem B1770983 : Blo 523799 1770983 := bstep (se 1 (by rfl) ⟨1328237, by rfl⟩ : syracuseStep 1770983 = 2656475) B2656475
theorem B2852327 : Blo 523799 2852327 := bstep (se 1 (by rfl) ⟨2139245, by rfl⟩ : syracuseStep 2852327 = 4278491) B4278491
theorem B526207 : Blo 523799 526207 := bstep (se 1 (by rfl) ⟨394655, by rfl⟩ : syracuseStep 526207 = 789311) B789311
theorem B526239 : Blo 523799 526239 := bstep (se 1 (by rfl) ⟨394679, by rfl⟩ : syracuseStep 526239 = 789359) B789359
theorem B11339837 : Blo 523799 11339837 := bstep (se 3 (by rfl) ⟨2126219, by rfl⟩ : syracuseStep 11339837 = 4252439) B4252439
theorem B526427 : Blo 523799 526427 := bstep (se 1 (by rfl) ⟨394820, by rfl⟩ : syracuseStep 526427 = 789641) B789641
theorem B1181807 : Blo 523799 1181807 := bstep (se 1 (by rfl) ⟨886355, by rfl⟩ : syracuseStep 1181807 = 1772711) B1772711
theorem B788687 : Blo 523799 788687 := bstep (se 1 (by rfl) ⟨591515, by rfl⟩ : syracuseStep 788687 = 1183031) B1183031
theorem B527003 : Blo 523799 527003 := bstep (se 1 (by rfl) ⟨395252, by rfl⟩ : syracuseStep 527003 = 790505) B790505
theorem B789275 : Blo 523799 789275 := bstep (se 1 (by rfl) ⟨591956, by rfl⟩ : syracuseStep 789275 = 1183913) B1183913
theorem B527463 : Blo 523799 527463 := bstep (se 1 (by rfl) ⟨395597, by rfl⟩ : syracuseStep 527463 = 791195) B791195
theorem B789695 : Blo 523799 789695 := bstep (se 1 (by rfl) ⟨592271, by rfl⟩ : syracuseStep 789695 = 1184543) B1184543
theorem B527719 : Blo 523799 527719 := bstep (se 1 (by rfl) ⟨395789, by rfl⟩ : syracuseStep 527719 = 791579) B791579
theorem B1708199 : Blo 523799 1708199 := bstep (se 1 (by rfl) ⟨1281149, by rfl⟩ : syracuseStep 1708199 = 2562299) B2562299
theorem B1184057 : Blo 523799 1184057 := bstep (se 2 (by rfl) ⟨444021, by rfl⟩ : syracuseStep 1184057 = 888043) B888043
theorem B12095819 : Blo 523799 12095819 := bstep (se 1 (by rfl) ⟨9071864, by rfl⟩ : syracuseStep 12095819 = 18143729) B18143729
theorem B19206611 : Blo 523799 19206611 := bstep (se 1 (by rfl) ⟨14404958, by rfl⟩ : syracuseStep 19206611 = 28809917) B28809917
theorem B1184489 : Blo 523799 1184489 := bstep (se 2 (by rfl) ⟨444183, by rfl⟩ : syracuseStep 1184489 = 888367) B888367
theorem B1184615 : Blo 523799 1184615 := bstep (se 1 (by rfl) ⟨888461, by rfl⟩ : syracuseStep 1184615 = 1776923) B1776923
theorem B2659229 : Blo 523799 2659229 := bstep (se 3 (by rfl) ⟨498605, by rfl⟩ : syracuseStep 2659229 = 997211) B997211
theorem B791465 : Blo 523799 791465 := bstep (se 2 (by rfl) ⟨296799, by rfl⟩ : syracuseStep 791465 = 593599) B593599
theorem B2659553 : Blo 523799 2659553 := bstep (se 2 (by rfl) ⟨997332, by rfl⟩ : syracuseStep 2659553 = 1994665) B1994665
theorem B1184993 : Blo 523799 1184993 := bstep (se 2 (by rfl) ⟨444372, by rfl⟩ : syracuseStep 1184993 = 888745) B888745
theorem B8066591 : Blo 523799 8066591 := bstep (se 1 (by rfl) ⟨6049943, by rfl⟩ : syracuseStep 8066591 = 12099887) B12099887
theorem B1185371 : Blo 523799 1185371 := bstep (se 1 (by rfl) ⟨889028, by rfl⟩ : syracuseStep 1185371 = 1778057) B1778057
theorem B8525897 : Blo 523799 8525897 := bstep (se 2 (by rfl) ⟨3197211, by rfl⟩ : syracuseStep 8525897 = 6394423) B6394423
theorem B1186523 : Blo 523799 1186523 := bstep (se 1 (by rfl) ⟨889892, by rfl⟩ : syracuseStep 1186523 = 1779785) B1779785
theorem B10755119 : Blo 523799 10755119 := bstep (se 1 (by rfl) ⟨8066339, by rfl⟩ : syracuseStep 10755119 = 16132679) B16132679
theorem B3186311 : Blo 523799 3186311 := bstep (se 1 (by rfl) ⟨2389733, by rfl⟩ : syracuseStep 3186311 = 4779467) B4779467
theorem B17048555 : Blo 523799 17048555 := bstep (se 1 (by rfl) ⟨12786416, by rfl⟩ : syracuseStep 17048555 = 25572833) B25572833
theorem B1124255 : Blo 523799 1124255 := bstep (se 1 (by rfl) ⟨843191, by rfl⟩ : syracuseStep 1124255 = 1686383) B1686383
theorem B534767 : Blo 523799 534767 := bstep (se 1 (by rfl) ⟨401075, by rfl⟩ : syracuseStep 534767 = 802151) B802151
theorem B3779369 : Blo 523799 3779369 := bstep (se 2 (by rfl) ⟨1417263, by rfl⟩ : syracuseStep 3779369 = 2834527) B2834527
theorem B2668139 : Blo 523799 2668139 := bstep (se 1 (by rfl) ⟨2001104, by rfl⟩ : syracuseStep 2668139 = 4002209) B4002209
theorem B73611109 : Blo 523799 73611109 := bstep (se 4 (by rfl) ⟨6901041, by rfl⟩ : syracuseStep 73611109 = 13802083) B13802083
theorem B17053861 : Blo 523799 17053861 := bstep (se 4 (by rfl) ⟨1598799, by rfl⟩ : syracuseStep 17053861 = 3197599) B3197599
theorem B155401325 : Blo 523799 155401325 := bstep (se 3 (by rfl) ⟨29137748, by rfl⟩ : syracuseStep 155401325 = 58275497) B58275497
theorem B2669759 : Blo 523799 2669759 := bstep (se 1 (by rfl) ⟨2002319, by rfl⟩ : syracuseStep 2669759 = 4004639) B4004639
theorem B1097371 : Blo 523799 1097371 := bstep (se 1 (by rfl) ⟨823028, by rfl⟩ : syracuseStep 1097371 = 1646057) B1646057
theorem B217924025 : Blo 523799 217924025 := bstep (se 2 (by rfl) ⟨81721509, by rfl⟩ : syracuseStep 217924025 = 163443019) B163443019
theorem B5129891 : Blo 523799 5129891 := bstep (se 1 (by rfl) ⟨3847418, by rfl⟩ : syracuseStep 5129891 = 7694837) B7694837
theorem B24332015 : Blo 523799 24332015 := bstep (se 1 (by rfl) ⟨18249011, by rfl⟩ : syracuseStep 24332015 = 36498023) B36498023
theorem B1263347 : Blo 523799 1263347 := bstep (se 1 (by rfl) ⟨947510, by rfl⟩ : syracuseStep 1263347 = 1895021) B1895021
theorem B5982173 : Blo 523799 5982173 := bstep (se 3 (by rfl) ⟨1121657, by rfl⟩ : syracuseStep 5982173 = 2243315) B2243315
theorem B1493711 : Blo 523799 1493711 := bstep (se 1 (by rfl) ⟨1120283, by rfl⟩ : syracuseStep 1493711 = 2240567) B2240567
theorem B54711359 : Blo 523799 54711359 := bstep (se 1 (by rfl) ⟨41033519, by rfl⟩ : syracuseStep 54711359 = 82067039) B82067039
theorem B3986657 : Blo 523799 3986657 := bstep (se 2 (by rfl) ⟨1494996, by rfl⟩ : syracuseStep 3986657 = 2989993) B2989993
theorem B2742781 : Blo 523799 2742781 := bstep (se 3 (by rfl) ⟨514271, by rfl⟩ : syracuseStep 2742781 = 1028543) B1028543
theorem B8903945 : Blo 523799 8903945 := bstep (se 2 (by rfl) ⟨3338979, by rfl⟩ : syracuseStep 8903945 = 6677959) B6677959
theorem B9624851 : Blo 523799 9624851 := bstep (se 1 (by rfl) ⟨7218638, by rfl⟩ : syracuseStep 9624851 = 14437277) B14437277
theorem B4251923 : Blo 523799 4251923 := bstep (se 1 (by rfl) ⟨3188942, by rfl⟩ : syracuseStep 4251923 = 6377885) B6377885
theorem B1991051 : Blo 523799 1991051 := bstep (se 1 (by rfl) ⟨1493288, by rfl⟩ : syracuseStep 1991051 = 2986577) B2986577
theorem B1991263 : Blo 523799 1991263 := bstep (se 1 (by rfl) ⟨1493447, by rfl⟩ : syracuseStep 1991263 = 2986895) B2986895
theorem B1993193 : Blo 523799 1993193 := bstep (se 2 (by rfl) ⟨747447, by rfl⟩ : syracuseStep 1993193 = 1494895) B1494895
theorem B4484443 : Blo 523799 4484443 := bstep (se 1 (by rfl) ⟨3363332, by rfl⟩ : syracuseStep 4484443 = 6726665) B6726665
theorem B2158919 : Blo 523799 2158919 := bstep (se 1 (by rfl) ⟨1619189, by rfl⟩ : syracuseStep 2158919 = 3238379) B3238379
theorem B1012411 : Blo 523799 1012411 := bstep (se 1 (by rfl) ⟨759308, by rfl⟩ : syracuseStep 1012411 = 1518617) B1518617
theorem B2126675 : Blo 523799 2126675 := bstep (se 1 (by rfl) ⟨1595006, by rfl⟩ : syracuseStep 2126675 = 3190013) B3190013
theorem B3406159 : Blo 523799 3406159 := bstep (se 1 (by rfl) ⟨2554619, by rfl⟩ : syracuseStep 3406159 = 5109239) B5109239
theorem B14383507 : Blo 523799 14383507 := bstep (se 1 (by rfl) ⟨10787630, by rfl⟩ : syracuseStep 14383507 = 21575261) B21575261
theorem B949225 : Blo 523799 949225 := bstep (se 2 (by rfl) ⟨355959, by rfl⟩ : syracuseStep 949225 = 711919) B711919
theorem B785705 : Blo 523799 785705 := bstep (se 2 (by rfl) ⟨294639, by rfl⟩ : syracuseStep 785705 = 589279) B589279
theorem B1179071 : Blo 523799 1179071 := bstep (se 1 (by rfl) ⟨884303, by rfl⟩ : syracuseStep 1179071 = 1768607) B1768607
theorem B589567 : Blo 523799 589567 := bstep (se 1 (by rfl) ⟨442175, by rfl⟩ : syracuseStep 589567 = 884351) B884351
theorem B786407 : Blo 523799 786407 := bstep (se 1 (by rfl) ⟨589805, by rfl⟩ : syracuseStep 786407 = 1179611) B1179611
theorem B786569 : Blo 523799 786569 := bstep (se 2 (by rfl) ⟨294963, by rfl⟩ : syracuseStep 786569 = 589927) B589927
theorem B524443 : Blo 523799 524443 := bstep (se 1 (by rfl) ⟨393332, by rfl⟩ : syracuseStep 524443 = 786665) B786665
theorem B1180385 : Blo 523799 1180385 := bstep (se 2 (by rfl) ⟨442644, by rfl⟩ : syracuseStep 1180385 = 885289) B885289
theorem B2655017 : Blo 523799 2655017 := bstep (se 2 (by rfl) ⟨995631, by rfl⟩ : syracuseStep 2655017 = 1991263) B1991263
theorem B1180655 : Blo 523799 1180655 := bstep (se 1 (by rfl) ⟨885491, by rfl⟩ : syracuseStep 1180655 = 1770983) B1770983
theorem B1901551 : Blo 523799 1901551 := bstep (se 1 (by rfl) ⟨1426163, by rfl⟩ : syracuseStep 1901551 = 2852327) B2852327
theorem B787871 : Blo 523799 787871 := bstep (se 1 (by rfl) ⟨590903, by rfl⟩ : syracuseStep 787871 = 1181807) B1181807
theorem B525791 : Blo 523799 525791 := bstep (se 1 (by rfl) ⟨394343, by rfl⟩ : syracuseStep 525791 = 788687) B788687
theorem B1181321 : Blo 523799 1181321 := bstep (se 2 (by rfl) ⟨442995, by rfl⟩ : syracuseStep 1181321 = 885991) B885991
theorem B526183 : Blo 523799 526183 := bstep (se 1 (by rfl) ⟨394637, by rfl⟩ : syracuseStep 526183 = 789275) B789275
theorem B526463 : Blo 523799 526463 := bstep (se 1 (by rfl) ⟨394847, by rfl⟩ : syracuseStep 526463 = 789695) B789695
theorem B5671133 : Blo 523799 5671133 := bstep (se 3 (by rfl) ⟨1063337, by rfl⟩ : syracuseStep 5671133 = 2126675) B2126675
theorem B789371 : Blo 523799 789371 := bstep (se 1 (by rfl) ⟨592028, by rfl⟩ : syracuseStep 789371 = 1184057) B1184057
theorem B8063879 : Blo 523799 8063879 := bstep (se 1 (by rfl) ⟨6047909, by rfl⟩ : syracuseStep 8063879 = 12095819) B12095819
theorem B789659 : Blo 523799 789659 := bstep (se 1 (by rfl) ⟨592244, by rfl⟩ : syracuseStep 789659 = 1184489) B1184489
theorem B789743 : Blo 523799 789743 := bstep (se 1 (by rfl) ⟨592307, by rfl⟩ : syracuseStep 789743 = 1184615) B1184615
theorem B1772819 : Blo 523799 1772819 := bstep (se 1 (by rfl) ⟨1329614, by rfl⟩ : syracuseStep 1772819 = 2659229) B2659229
theorem B527643 : Blo 523799 527643 := bstep (se 1 (by rfl) ⟨395732, by rfl⟩ : syracuseStep 527643 = 791465) B791465
theorem B36474239 : Blo 523799 36474239 := bstep (se 1 (by rfl) ⟨27355679, by rfl⟩ : syracuseStep 36474239 = 54711359) B54711359
theorem B2657771 : Blo 523799 2657771 := bstep (se 1 (by rfl) ⟨1993328, by rfl⟩ : syracuseStep 2657771 = 3986657) B3986657
theorem B1773035 : Blo 523799 1773035 := bstep (se 1 (by rfl) ⟨1329776, by rfl⟩ : syracuseStep 1773035 = 2659553) B2659553
theorem B789995 : Blo 523799 789995 := bstep (se 1 (by rfl) ⟨592496, by rfl⟩ : syracuseStep 789995 = 1184993) B1184993
theorem B5377727 : Blo 523799 5377727 := bstep (se 1 (by rfl) ⟨4033295, by rfl⟩ : syracuseStep 5377727 = 8066591) B8066591
theorem B790247 : Blo 523799 790247 := bstep (se 1 (by rfl) ⟨592685, by rfl⟩ : syracuseStep 790247 = 1185371) B1185371
theorem B791015 : Blo 523799 791015 := bstep (se 1 (by rfl) ⟨593261, by rfl⟩ : syracuseStep 791015 = 1186523) B1186523
theorem B64885373 : Blo 523799 64885373 := bstep (se 3 (by rfl) ⟨12166007, by rfl⟩ : syracuseStep 64885373 = 24332015) B24332015
theorem B5935963 : Blo 523799 5935963 := bstep (se 1 (by rfl) ⟨4451972, by rfl⟩ : syracuseStep 5935963 = 8903945) B8903945
theorem B1349881 : Blo 523799 1349881 := bstep (se 2 (by rfl) ⟨506205, by rfl⟩ : syracuseStep 1349881 = 1012411) B1012411
theorem B98148145 : Blo 523799 98148145 := bstep (se 2 (by rfl) ⟨36805554, by rfl⟩ : syracuseStep 98148145 = 73611109) B73611109
theorem B28680317 : Blo 523799 28680317 := bstep (se 3 (by rfl) ⟨5377559, by rfl⟩ : syracuseStep 28680317 = 10755119) B10755119
theorem B19178009 : Blo 523799 19178009 := bstep (se 2 (by rfl) ⟨7191753, by rfl⟩ : syracuseStep 19178009 = 14383507) B14383507
theorem B1778759 : Blo 523799 1778759 := bstep (se 1 (by rfl) ⟨1334069, by rfl⟩ : syracuseStep 1778759 = 2668139) B2668139
theorem B8496829 : Blo 523799 8496829 := bstep (se 3 (by rfl) ⟨1593155, by rfl⟩ : syracuseStep 8496829 = 3186311) B3186311
theorem B1779839 : Blo 523799 1779839 := bstep (se 1 (by rfl) ⟨1334879, by rfl⟩ : syracuseStep 1779839 = 2669759) B2669759
theorem B9612071 : Blo 523799 9612071 := bstep (se 1 (by rfl) ⟨7209053, by rfl⟩ : syracuseStep 9612071 = 14418107) B14418107
theorem B3419927 : Blo 523799 3419927 := bstep (se 1 (by rfl) ⟨2564945, by rfl⟩ : syracuseStep 3419927 = 5129891) B5129891
theorem B995807 : Blo 523799 995807 := bstep (se 1 (by rfl) ⟨746855, by rfl⟩ : syracuseStep 995807 = 1493711) B1493711
theorem B5683931 : Blo 523799 5683931 := bstep (se 1 (by rfl) ⟨4262948, by rfl⟩ : syracuseStep 5683931 = 8525897) B8525897
theorem B5979257 : Blo 523799 5979257 := bstep (se 2 (by rfl) ⟨2242221, by rfl⟩ : syracuseStep 5979257 = 4484443) B4484443
theorem B2834615 : Blo 523799 2834615 := bstep (se 1 (by rfl) ⟨2125961, by rfl⟩ : syracuseStep 2834615 = 4251923) B4251923
theorem B1327367 : Blo 523799 1327367 := bstep (se 1 (by rfl) ⟨995525, by rfl⟩ : syracuseStep 1327367 = 1991051) B1991051
theorem B1426045 : Blo 523799 1426045 := bstep (se 3 (by rfl) ⟨267383, by rfl⟩ : syracuseStep 1426045 = 534767) B534767
theorem B1328795 : Blo 523799 1328795 := bstep (se 1 (by rfl) ⟨996596, by rfl⟩ : syracuseStep 1328795 = 1993193) B1993193
theorem B4541545 : Blo 523799 4541545 := bstep (se 2 (by rfl) ⟨1703079, by rfl⟩ : syracuseStep 4541545 = 3406159) B3406159
theorem B3657041 : Blo 523799 3657041 := bstep (se 2 (by rfl) ⟨1371390, by rfl⟩ : syracuseStep 3657041 = 2742781) B2742781
theorem B5852645 : Blo 523799 5852645 := bstep (se 4 (by rfl) ⟨548685, by rfl⟩ : syracuseStep 5852645 = 1097371) B1097371
theorem B1265633 : Blo 523799 1265633 := bstep (se 2 (by rfl) ⟨474612, by rfl⟩ : syracuseStep 1265633 = 949225) B949225
theorem B103600883 : Blo 523799 103600883 := bstep (se 1 (by rfl) ⟨77700662, by rfl⟩ : syracuseStep 103600883 = 155401325) B155401325
theorem B581130733 : Blo 523799 581130733 := bstep (se 3 (by rfl) ⟨108962012, by rfl⟩ : syracuseStep 581130733 = 217924025) B217924025
theorem B842231 : Blo 523799 842231 := bstep (se 1 (by rfl) ⟨631673, by rfl⟩ : syracuseStep 842231 = 1263347) B1263347
theorem B3988115 : Blo 523799 3988115 := bstep (se 1 (by rfl) ⟨2991086, by rfl⟩ : syracuseStep 3988115 = 5982173) B5982173
theorem B7559891 : Blo 523799 7559891 := bstep (se 1 (by rfl) ⟨5669918, by rfl⟩ : syracuseStep 7559891 = 11339837) B11339837
theorem B1138799 : Blo 523799 1138799 := bstep (se 1 (by rfl) ⟨854099, by rfl⟩ : syracuseStep 1138799 = 1708199) B1708199
theorem B12804407 : Blo 523799 12804407 := bstep (se 1 (by rfl) ⟨9603305, by rfl⟩ : syracuseStep 12804407 = 19206611) B19206611
theorem B6416567 : Blo 523799 6416567 := bstep (se 1 (by rfl) ⟨4812425, by rfl⟩ : syracuseStep 6416567 = 9624851) B9624851
theorem B11365703 : Blo 523799 11365703 := bstep (se 1 (by rfl) ⟨8524277, by rfl⟩ : syracuseStep 11365703 = 17048555) B17048555
theorem B749503 : Blo 523799 749503 := bstep (se 1 (by rfl) ⟨562127, by rfl⟩ : syracuseStep 749503 = 1124255) B1124255
theorem B2519579 : Blo 523799 2519579 := bstep (se 1 (by rfl) ⟨1889684, by rfl⟩ : syracuseStep 2519579 = 3779369) B3779369
theorem B1439279 : Blo 523799 1439279 := bstep (se 1 (by rfl) ⟨1079459, by rfl⟩ : syracuseStep 1439279 = 2158919) B2158919
theorem B22738481 : Blo 523799 22738481 := bstep (se 2 (by rfl) ⟨8526930, by rfl⟩ : syracuseStep 22738481 = 17053861) B17053861
theorem B523803 : Blo 523799 523803 := bstep (se 1 (by rfl) ⟨392852, by rfl⟩ : syracuseStep 523803 = 785705) B785705
theorem B786047 : Blo 523799 786047 := bstep (se 1 (by rfl) ⟨589535, by rfl⟩ : syracuseStep 786047 = 1179071) B1179071
theorem B786089 : Blo 523799 786089 := bstep (se 2 (by rfl) ⟨294783, by rfl⟩ : syracuseStep 786089 = 589567) B589567
theorem B524271 : Blo 523799 524271 := bstep (se 1 (by rfl) ⟨393203, by rfl⟩ : syracuseStep 524271 = 786407) B786407
theorem B524379 : Blo 523799 524379 := bstep (se 1 (by rfl) ⟨393284, by rfl⟩ : syracuseStep 524379 = 786569) B786569
theorem B884911 : Blo 523799 884911 := bstep (se 1 (by rfl) ⟨663683, by rfl⟩ : syracuseStep 884911 = 1327367) B1327367
theorem B786923 : Blo 523799 786923 := bstep (se 1 (by rfl) ⟨590192, by rfl⟩ : syracuseStep 786923 = 1180385) B1180385
theorem B1770011 : Blo 523799 1770011 := bstep (se 1 (by rfl) ⟨1327508, by rfl⟩ : syracuseStep 1770011 = 2655017) B2655017
theorem B787103 : Blo 523799 787103 := bstep (se 1 (by rfl) ⟨590327, by rfl⟩ : syracuseStep 787103 = 1180655) B1180655
theorem B1901393 : Blo 523799 1901393 := bstep (se 2 (by rfl) ⟨713022, by rfl⟩ : syracuseStep 1901393 = 1426045) B1426045
theorem B525247 : Blo 523799 525247 := bstep (se 1 (by rfl) ⟨393935, by rfl⟩ : syracuseStep 525247 = 787871) B787871
theorem B787547 : Blo 523799 787547 := bstep (se 1 (by rfl) ⟨590660, by rfl⟩ : syracuseStep 787547 = 1181321) B1181321
theorem B885863 : Blo 523799 885863 := bstep (se 1 (by rfl) ⟨664397, by rfl⟩ : syracuseStep 885863 = 1328795) B1328795
theorem B526247 : Blo 523799 526247 := bstep (se 1 (by rfl) ⟨394685, by rfl⟩ : syracuseStep 526247 = 789371) B789371
theorem B526439 : Blo 523799 526439 := bstep (se 1 (by rfl) ⟨394829, by rfl⟩ : syracuseStep 526439 = 789659) B789659
theorem B526495 : Blo 523799 526495 := bstep (se 1 (by rfl) ⟨394871, by rfl⟩ : syracuseStep 526495 = 789743) B789743
theorem B1181879 : Blo 523799 1181879 := bstep (se 1 (by rfl) ⟨886409, by rfl⟩ : syracuseStep 1181879 = 1772819) B1772819
theorem B24316159 : Blo 523799 24316159 := bstep (se 1 (by rfl) ⟨18237119, by rfl⟩ : syracuseStep 24316159 = 36474239) B36474239
theorem B3901763 : Blo 523799 3901763 := bstep (se 1 (by rfl) ⟨2926322, by rfl⟩ : syracuseStep 3901763 = 5852645) B5852645
theorem B1771847 : Blo 523799 1771847 := bstep (se 1 (by rfl) ⟨1328885, by rfl⟩ : syracuseStep 1771847 = 2657771) B2657771
theorem B1182023 : Blo 523799 1182023 := bstep (se 1 (by rfl) ⟨886517, by rfl⟩ : syracuseStep 1182023 = 1773035) B1773035
theorem B526663 : Blo 523799 526663 := bstep (se 1 (by rfl) ⟨394997, by rfl⟩ : syracuseStep 526663 = 789995) B789995
theorem B526831 : Blo 523799 526831 := bstep (se 1 (by rfl) ⟨395123, by rfl⟩ : syracuseStep 526831 = 790247) B790247
theorem B527343 : Blo 523799 527343 := bstep (se 1 (by rfl) ⟨395507, by rfl⟩ : syracuseStep 527343 = 791015) B791015
theorem B43256915 : Blo 523799 43256915 := bstep (se 1 (by rfl) ⟨32442686, by rfl⟩ : syracuseStep 43256915 = 64885373) B64885373
theorem B561487 : Blo 523799 561487 := bstep (se 1 (by rfl) ⟨421115, by rfl⟩ : syracuseStep 561487 = 842231) B842231
theorem B2658743 : Blo 523799 2658743 := bstep (se 1 (by rfl) ⟨1994057, by rfl⟩ : syracuseStep 2658743 = 3988115) B3988115
theorem B12785339 : Blo 523799 12785339 := bstep (se 1 (by rfl) ⟨9589004, by rfl⟩ : syracuseStep 12785339 = 19178009) B19178009
theorem B1185839 : Blo 523799 1185839 := bstep (se 1 (by rfl) ⟨889379, by rfl⟩ : syracuseStep 1185839 = 1778759) B1778759
theorem B1186559 : Blo 523799 1186559 := bstep (se 1 (by rfl) ⟨889919, by rfl⟩ : syracuseStep 1186559 = 1779839) B1779839
theorem B7577135 : Blo 523799 7577135 := bstep (se 1 (by rfl) ⟨5682851, by rfl⟩ : syracuseStep 7577135 = 11365703) B11365703
theorem B21503677 : Blo 523799 21503677 := bstep (se 3 (by rfl) ⟨4031939, by rfl⟩ : syracuseStep 21503677 = 8063879) B8063879
theorem B663871 : Blo 523799 663871 := bstep (se 1 (by rfl) ⟨497903, by rfl⟩ : syracuseStep 663871 = 995807) B995807
theorem B1679719 : Blo 523799 1679719 := bstep (se 1 (by rfl) ⟨1259789, by rfl⟩ : syracuseStep 1679719 = 2519579) B2519579
theorem B774840977 : Blo 523799 774840977 := bstep (se 2 (by rfl) ⟨290565366, by rfl⟩ : syracuseStep 774840977 = 581130733) B581130733
theorem B959519 : Blo 523799 959519 := bstep (se 1 (by rfl) ⟨719639, by rfl⟩ : syracuseStep 959519 = 1439279) B1439279
theorem B2535401 : Blo 523799 2535401 := bstep (se 2 (by rfl) ⟨950775, by rfl⟩ : syracuseStep 2535401 = 1901551) B1901551
theorem B3780755 : Blo 523799 3780755 := bstep (se 1 (by rfl) ⟨2835566, by rfl⟩ : syracuseStep 3780755 = 5671133) B5671133
theorem B2438027 : Blo 523799 2438027 := bstep (se 1 (by rfl) ⟨1828520, by rfl⟩ : syracuseStep 2438027 = 3657041) B3657041
theorem B3585151 : Blo 523799 3585151 := bstep (se 1 (by rfl) ⟨2688863, by rfl⟩ : syracuseStep 3585151 = 5377727) B5377727
theorem B19120211 : Blo 523799 19120211 := bstep (se 1 (by rfl) ⟨14340158, by rfl⟩ : syracuseStep 19120211 = 28680317) B28680317
theorem B8536271 : Blo 523799 8536271 := bstep (se 1 (by rfl) ⟨6402203, by rfl⟩ : syracuseStep 8536271 = 12804407) B12804407
theorem B7914617 : Blo 523799 7914617 := bstep (se 2 (by rfl) ⟨2967981, by rfl⟩ : syracuseStep 7914617 = 5935963) B5935963
theorem B4277711 : Blo 523799 4277711 := bstep (se 1 (by rfl) ⟨3208283, by rfl⟩ : syracuseStep 4277711 = 6416567) B6416567
theorem B6408047 : Blo 523799 6408047 := bstep (se 1 (by rfl) ⟨4806035, by rfl⟩ : syracuseStep 6408047 = 9612071) B9612071
theorem B2279951 : Blo 523799 2279951 := bstep (se 1 (by rfl) ⟨1709963, by rfl⟩ : syracuseStep 2279951 = 3419927) B3419927
theorem B15158987 : Blo 523799 15158987 := bstep (se 1 (by rfl) ⟨11369240, by rfl⟩ : syracuseStep 15158987 = 22738481) B22738481
theorem B3789287 : Blo 523799 3789287 := bstep (se 1 (by rfl) ⟨2841965, by rfl⟩ : syracuseStep 3789287 = 5683931) B5683931
theorem B3986171 : Blo 523799 3986171 := bstep (se 1 (by rfl) ⟨2989628, by rfl⟩ : syracuseStep 3986171 = 5979257) B5979257
theorem B130864193 : Blo 523799 130864193 := bstep (se 2 (by rfl) ⟨49074072, by rfl⟩ : syracuseStep 130864193 = 98148145) B98148145
theorem B1889743 : Blo 523799 1889743 := bstep (se 1 (by rfl) ⟨1417307, by rfl⟩ : syracuseStep 1889743 = 2834615) B2834615
theorem B3036797 : Blo 523799 3036797 := bstep (se 3 (by rfl) ⟨569399, by rfl⟩ : syracuseStep 3036797 = 1138799) B1138799
theorem B7199365 : Blo 523799 7199365 := bstep (se 4 (by rfl) ⟨674940, by rfl⟩ : syracuseStep 7199365 = 1349881) B1349881
theorem B11329105 : Blo 523799 11329105 := bstep (se 2 (by rfl) ⟨4248414, by rfl⟩ : syracuseStep 11329105 = 8496829) B8496829
theorem B843755 : Blo 523799 843755 := bstep (se 1 (by rfl) ⟨632816, by rfl⟩ : syracuseStep 843755 = 1265633) B1265633
theorem B69067255 : Blo 523799 69067255 := bstep (se 1 (by rfl) ⟨51800441, by rfl⟩ : syracuseStep 69067255 = 103600883) B103600883
theorem B6055393 : Blo 523799 6055393 := bstep (se 2 (by rfl) ⟨2270772, by rfl⟩ : syracuseStep 6055393 = 4541545) B4541545
theorem B5039927 : Blo 523799 5039927 := bstep (se 1 (by rfl) ⟨3779945, by rfl⟩ : syracuseStep 5039927 = 7559891) B7559891
theorem B3997349 : Blo 523799 3997349 := bstep (se 4 (by rfl) ⟨374751, by rfl⟩ : syracuseStep 3997349 = 749503) B749503
theorem B524031 : Blo 523799 524031 := bstep (se 1 (by rfl) ⟨393023, by rfl⟩ : syracuseStep 524031 = 786047) B786047
theorem B524059 : Blo 523799 524059 := bstep (se 1 (by rfl) ⟨393044, by rfl⟩ : syracuseStep 524059 = 786089) B786089
theorem B12746807 : Blo 523799 12746807 := bstep (se 1 (by rfl) ⟨9560105, by rfl⟩ : syracuseStep 12746807 = 19120211) B19120211
theorem B1179881 : Blo 523799 1179881 := bstep (se 2 (by rfl) ⟨442455, by rfl⟩ : syracuseStep 1179881 = 884911) B884911
theorem B524615 : Blo 523799 524615 := bstep (se 1 (by rfl) ⟨393461, by rfl⟩ : syracuseStep 524615 = 786923) B786923
theorem B1180007 : Blo 523799 1180007 := bstep (se 1 (by rfl) ⟨885005, by rfl⟩ : syracuseStep 1180007 = 1770011) B1770011
theorem B885161 : Blo 523799 885161 := bstep (se 2 (by rfl) ⟨331935, by rfl⟩ : syracuseStep 885161 = 663871) B663871
theorem B524735 : Blo 523799 524735 := bstep (se 1 (by rfl) ⟨393551, by rfl⟩ : syracuseStep 524735 = 787103) B787103
theorem B525031 : Blo 523799 525031 := bstep (se 1 (by rfl) ⟨393773, by rfl⟩ : syracuseStep 525031 = 787547) B787547
theorem B590575 : Blo 523799 590575 := bstep (se 1 (by rfl) ⟨442931, by rfl⟩ : syracuseStep 590575 = 885863) B885863
theorem B5276411 : Blo 523799 5276411 := bstep (se 1 (by rfl) ⟨3957308, by rfl⟩ : syracuseStep 5276411 = 7914617) B7914617
theorem B2851807 : Blo 523799 2851807 := bstep (se 1 (by rfl) ⟨2138855, by rfl⟩ : syracuseStep 2851807 = 4277711) B4277711
theorem B787919 : Blo 523799 787919 := bstep (se 1 (by rfl) ⟨590939, by rfl⟩ : syracuseStep 787919 = 1181879) B1181879
theorem B1181231 : Blo 523799 1181231 := bstep (se 1 (by rfl) ⟨885923, by rfl⟩ : syracuseStep 1181231 = 1771847) B1771847
theorem B788015 : Blo 523799 788015 := bstep (se 1 (by rfl) ⟨591011, by rfl⟩ : syracuseStep 788015 = 1182023) B1182023
theorem B28837943 : Blo 523799 28837943 := bstep (se 1 (by rfl) ⟨21628457, by rfl⟩ : syracuseStep 28837943 = 43256915) B43256915
theorem B1772495 : Blo 523799 1772495 := bstep (se 1 (by rfl) ⟨1329371, by rfl⟩ : syracuseStep 1772495 = 2658743) B2658743
theorem B2526191 : Blo 523799 2526191 := bstep (se 1 (by rfl) ⟨1894643, by rfl⟩ : syracuseStep 2526191 = 3789287) B3789287
theorem B2657447 : Blo 523799 2657447 := bstep (se 1 (by rfl) ⟨1993085, by rfl⟩ : syracuseStep 2657447 = 3986171) B3986171
theorem B8523559 : Blo 523799 8523559 := bstep (se 1 (by rfl) ⟨6392669, by rfl⟩ : syracuseStep 8523559 = 12785339) B12785339
theorem B790559 : Blo 523799 790559 := bstep (se 1 (by rfl) ⟨592919, by rfl⟩ : syracuseStep 790559 = 1185839) B1185839
theorem B791039 : Blo 523799 791039 := bstep (se 1 (by rfl) ⟨593279, by rfl⟩ : syracuseStep 791039 = 1186559) B1186559
theorem B5051423 : Blo 523799 5051423 := bstep (se 1 (by rfl) ⟨3788567, by rfl⟩ : syracuseStep 5051423 = 7577135) B7577135
theorem B516560651 : Blo 523799 516560651 := bstep (se 1 (by rfl) ⟨387420488, by rfl⟩ : syracuseStep 516560651 = 774840977) B774840977
theorem B2664899 : Blo 523799 2664899 := bstep (se 1 (by rfl) ⟨1998674, by rfl⟩ : syracuseStep 2664899 = 3997349) B3997349
theorem B2239625 : Blo 523799 2239625 := bstep (se 2 (by rfl) ⟨839859, by rfl⟩ : syracuseStep 2239625 = 1679719) B1679719
theorem B92089673 : Blo 523799 92089673 := bstep (se 2 (by rfl) ⟨34533627, by rfl⟩ : syracuseStep 92089673 = 69067255) B69067255
theorem B4272031 : Blo 523799 4272031 := bstep (se 1 (by rfl) ⟨3204023, by rfl⟩ : syracuseStep 4272031 = 6408047) B6408047
theorem B2601175 : Blo 523799 2601175 := bstep (se 1 (by rfl) ⟨1950881, by rfl⟩ : syracuseStep 2601175 = 3901763) B3901763
theorem B1519967 : Blo 523799 1519967 := bstep (se 1 (by rfl) ⟨1139975, by rfl⟩ : syracuseStep 1519967 = 2279951) B2279951
theorem B8073857 : Blo 523799 8073857 := bstep (se 2 (by rfl) ⟨3027696, by rfl⟩ : syracuseStep 8073857 = 6055393) B6055393
theorem B10105991 : Blo 523799 10105991 := bstep (se 1 (by rfl) ⟨7579493, by rfl⟩ : syracuseStep 10105991 = 15158987) B15158987
theorem B32421545 : Blo 523799 32421545 := bstep (se 2 (by rfl) ⟨12158079, by rfl⟩ : syracuseStep 32421545 = 24316159) B24316159
theorem B87242795 : Blo 523799 87242795 := bstep (se 1 (by rfl) ⟨65432096, by rfl⟩ : syracuseStep 87242795 = 130864193) B130864193
theorem B19120805 : Blo 523799 19120805 := bstep (se 4 (by rfl) ⟨1792575, by rfl⟩ : syracuseStep 19120805 = 3585151) B3585151
theorem B639679 : Blo 523799 639679 := bstep (se 1 (by rfl) ⟨479759, by rfl⟩ : syracuseStep 639679 = 959519) B959519
theorem B3359951 : Blo 523799 3359951 := bstep (se 1 (by rfl) ⟨2519963, by rfl⟩ : syracuseStep 3359951 = 5039927) B5039927
theorem B1690267 : Blo 523799 1690267 := bstep (se 1 (by rfl) ⟨1267700, by rfl⟩ : syracuseStep 1690267 = 2535401) B2535401
theorem B1625351 : Blo 523799 1625351 := bstep (se 1 (by rfl) ⟨1219013, by rfl⟩ : syracuseStep 1625351 = 2438027) B2438027
theorem B2250013 : Blo 523799 2250013 := bstep (se 3 (by rfl) ⟨421877, by rfl⟩ : syracuseStep 2250013 = 843755) B843755
theorem B22763389 : Blo 523799 22763389 := bstep (se 3 (by rfl) ⟨4268135, by rfl⟩ : syracuseStep 22763389 = 8536271) B8536271
theorem B1267595 : Blo 523799 1267595 := bstep (se 1 (by rfl) ⟨950696, by rfl⟩ : syracuseStep 1267595 = 1901393) B1901393
theorem B2024531 : Blo 523799 2024531 := bstep (se 1 (by rfl) ⟨1518398, by rfl⟩ : syracuseStep 2024531 = 3036797) B3036797
theorem B748649 : Blo 523799 748649 := bstep (se 2 (by rfl) ⟨280743, by rfl⟩ : syracuseStep 748649 = 561487) B561487
theorem B2519657 : Blo 523799 2519657 := bstep (se 2 (by rfl) ⟨944871, by rfl⟩ : syracuseStep 2519657 = 1889743) B1889743
theorem B2520503 : Blo 523799 2520503 := bstep (se 1 (by rfl) ⟨1890377, by rfl⟩ : syracuseStep 2520503 = 3780755) B3780755
theorem B9599153 : Blo 523799 9599153 := bstep (se 2 (by rfl) ⟨3599682, by rfl⟩ : syracuseStep 9599153 = 7199365) B7199365
theorem B15105473 : Blo 523799 15105473 := bstep (se 2 (by rfl) ⟨5664552, by rfl⟩ : syracuseStep 15105473 = 11329105) B11329105
theorem B28671569 : Blo 523799 28671569 := bstep (se 2 (by rfl) ⟨10751838, by rfl⟩ : syracuseStep 28671569 = 21503677) B21503677
theorem B786587 : Blo 523799 786587 := bstep (se 1 (by rfl) ⟨589940, by rfl⟩ : syracuseStep 786587 = 1179881) B1179881
theorem B786671 : Blo 523799 786671 := bstep (se 1 (by rfl) ⟨590003, by rfl⟩ : syracuseStep 786671 = 1180007) B1180007
theorem B590107 : Blo 523799 590107 := bstep (se 1 (by rfl) ⟨442580, by rfl⟩ : syracuseStep 590107 = 885161) B885161
theorem B12747203 : Blo 523799 12747203 := bstep (se 1 (by rfl) ⟨9560402, by rfl⟩ : syracuseStep 12747203 = 19120805) B19120805
theorem B852905 : Blo 523799 852905 := bstep (se 2 (by rfl) ⟨319839, by rfl⟩ : syracuseStep 852905 = 639679) B639679
theorem B525279 : Blo 523799 525279 := bstep (se 1 (by rfl) ⟨393959, by rfl⟩ : syracuseStep 525279 = 787919) B787919
theorem B787433 : Blo 523799 787433 := bstep (se 2 (by rfl) ⟨295287, by rfl⟩ : syracuseStep 787433 = 590575) B590575
theorem B787487 : Blo 523799 787487 := bstep (se 1 (by rfl) ⟨590615, by rfl⟩ : syracuseStep 787487 = 1181231) B1181231
theorem B525343 : Blo 523799 525343 := bstep (se 1 (by rfl) ⟨394007, by rfl⟩ : syracuseStep 525343 = 788015) B788015
theorem B3802409 : Blo 523799 3802409 := bstep (se 2 (by rfl) ⟨1425903, by rfl⟩ : syracuseStep 3802409 = 2851807) B2851807
theorem B21530285 : Blo 523799 21530285 := bstep (se 3 (by rfl) ⟨4036928, by rfl⟩ : syracuseStep 21530285 = 8073857) B8073857
theorem B1181663 : Blo 523799 1181663 := bstep (se 1 (by rfl) ⟨886247, by rfl⟩ : syracuseStep 1181663 = 1772495) B1772495
theorem B1771631 : Blo 523799 1771631 := bstep (se 1 (by rfl) ⟨1328723, by rfl⟩ : syracuseStep 1771631 = 2657447) B2657447
theorem B527039 : Blo 523799 527039 := bstep (se 1 (by rfl) ⟨395279, by rfl⟩ : syracuseStep 527039 = 790559) B790559
theorem B527359 : Blo 523799 527359 := bstep (se 1 (by rfl) ⟨395519, by rfl⟩ : syracuseStep 527359 = 791039) B791039
theorem B25597741 : Blo 523799 25597741 := bstep (se 3 (by rfl) ⟨4799576, by rfl⟩ : syracuseStep 25597741 = 9599153) B9599153
theorem B1349687 : Blo 523799 1349687 := bstep (se 1 (by rfl) ⟨1012265, by rfl⟩ : syracuseStep 1349687 = 2024531) B2024531
theorem B1776599 : Blo 523799 1776599 := bstep (se 1 (by rfl) ⟨1332449, by rfl⟩ : syracuseStep 1776599 = 2664899) B2664899
theorem B30351185 : Blo 523799 30351185 := bstep (se 2 (by rfl) ⟨11381694, by rfl⟩ : syracuseStep 30351185 = 22763389) B22763389
theorem B1679771 : Blo 523799 1679771 := bstep (se 1 (by rfl) ⟨1259828, by rfl⟩ : syracuseStep 1679771 = 2519657) B2519657
theorem B4334269 : Blo 523799 4334269 := bstep (se 3 (by rfl) ⟨812675, by rfl⟩ : syracuseStep 4334269 = 1625351) B1625351
theorem B1680335 : Blo 523799 1680335 := bstep (se 1 (by rfl) ⟨1260251, by rfl⟩ : syracuseStep 1680335 = 2520503) B2520503
theorem B10070315 : Blo 523799 10070315 := bstep (se 1 (by rfl) ⟨7552736, by rfl⟩ : syracuseStep 10070315 = 15105473) B15105473
theorem B19114379 : Blo 523799 19114379 := bstep (se 1 (by rfl) ⟨14335784, by rfl⟩ : syracuseStep 19114379 = 28671569) B28671569
theorem B8497871 : Blo 523799 8497871 := bstep (se 1 (by rfl) ⟨6373403, by rfl⟩ : syracuseStep 8497871 = 12746807) B12746807
theorem B3517607 : Blo 523799 3517607 := bstep (se 1 (by rfl) ⟨2638205, by rfl⟩ : syracuseStep 3517607 = 5276411) B5276411
theorem B2239967 : Blo 523799 2239967 := bstep (se 1 (by rfl) ⟨1679975, by rfl⟩ : syracuseStep 2239967 = 3359951) B3359951
theorem B1684127 : Blo 523799 1684127 := bstep (se 1 (by rfl) ⟨1263095, by rfl⟩ : syracuseStep 1684127 = 2526191) B2526191
theorem B344373767 : Blo 523799 344373767 := bstep (se 1 (by rfl) ⟨258280325, by rfl⟩ : syracuseStep 344373767 = 516560651) B516560651
theorem B3000017 : Blo 523799 3000017 := bstep (se 2 (by rfl) ⟨1125006, by rfl⟩ : syracuseStep 3000017 = 2250013) B2250013
theorem B1493083 : Blo 523799 1493083 := bstep (se 1 (by rfl) ⟨1119812, by rfl⟩ : syracuseStep 1493083 = 2239625) B2239625
theorem B61393115 : Blo 523799 61393115 := bstep (se 1 (by rfl) ⟨46044836, by rfl⟩ : syracuseStep 61393115 = 92089673) B92089673
theorem B6737327 : Blo 523799 6737327 := bstep (se 1 (by rfl) ⟨5052995, by rfl⟩ : syracuseStep 6737327 = 10105991) B10105991
theorem B21614363 : Blo 523799 21614363 := bstep (se 1 (by rfl) ⟨16210772, by rfl⟩ : syracuseStep 21614363 = 32421545) B32421545
theorem B19225295 : Blo 523799 19225295 := bstep (se 1 (by rfl) ⟨14418971, by rfl⟩ : syracuseStep 19225295 = 28837943) B28837943
theorem B3367615 : Blo 523799 3367615 := bstep (se 1 (by rfl) ⟨2525711, by rfl⟩ : syracuseStep 3367615 = 5051423) B5051423
theorem B2253689 : Blo 523799 2253689 := bstep (se 2 (by rfl) ⟨845133, by rfl⟩ : syracuseStep 2253689 = 1690267) B1690267
theorem B845063 : Blo 523799 845063 := bstep (se 1 (by rfl) ⟨633797, by rfl⟩ : syracuseStep 845063 = 1267595) B1267595
theorem B11364745 : Blo 523799 11364745 := bstep (se 2 (by rfl) ⟨4261779, by rfl⟩ : syracuseStep 11364745 = 8523559) B8523559
theorem B5696041 : Blo 523799 5696041 := bstep (se 2 (by rfl) ⟨2136015, by rfl⟩ : syracuseStep 5696041 = 4272031) B4272031
theorem B3468233 : Blo 523799 3468233 := bstep (se 2 (by rfl) ⟨1300587, by rfl⟩ : syracuseStep 3468233 = 2601175) B2601175
theorem B1013311 : Blo 523799 1013311 := bstep (se 1 (by rfl) ⟨759983, by rfl⟩ : syracuseStep 1013311 = 1519967) B1519967
theorem B1996397 : Blo 523799 1996397 := bstep (se 3 (by rfl) ⟨374324, by rfl⟩ : syracuseStep 1996397 = 748649) B748649
theorem B58161863 : Blo 523799 58161863 := bstep (se 1 (by rfl) ⟨43621397, by rfl⟩ : syracuseStep 58161863 = 87242795) B87242795
theorem B524391 : Blo 523799 524391 := bstep (se 1 (by rfl) ⟨393293, by rfl⟩ : syracuseStep 524391 = 786587) B786587
theorem B524447 : Blo 523799 524447 := bstep (se 1 (by rfl) ⟨393335, by rfl⟩ : syracuseStep 524447 = 786671) B786671
theorem B786809 : Blo 523799 786809 := bstep (se 2 (by rfl) ⟨295053, by rfl⟩ : syracuseStep 786809 = 590107) B590107
theorem B524955 : Blo 523799 524955 := bstep (se 1 (by rfl) ⟨393716, by rfl⟩ : syracuseStep 524955 = 787433) B787433
theorem B524991 : Blo 523799 524991 := bstep (se 1 (by rfl) ⟨393743, by rfl⟩ : syracuseStep 524991 = 787487) B787487
theorem B4490153 : Blo 523799 4490153 := bstep (se 2 (by rfl) ⟨1683807, by rfl⟩ : syracuseStep 4490153 = 3367615) B3367615
theorem B14353523 : Blo 523799 14353523 := bstep (se 1 (by rfl) ⟨10765142, by rfl⟩ : syracuseStep 14353523 = 21530285) B21530285
theorem B2000011 : Blo 523799 2000011 := bstep (se 1 (by rfl) ⟨1500008, by rfl⟩ : syracuseStep 2000011 = 3000017) B3000017
theorem B787775 : Blo 523799 787775 := bstep (se 1 (by rfl) ⟨590831, by rfl⟩ : syracuseStep 787775 = 1181663) B1181663
theorem B1181087 : Blo 523799 1181087 := bstep (se 1 (by rfl) ⟨885815, by rfl⟩ : syracuseStep 1181087 = 1771631) B1771631
theorem B40928743 : Blo 523799 40928743 := bstep (se 1 (by rfl) ⟨30696557, by rfl⟩ : syracuseStep 40928743 = 61393115) B61393115
theorem B4491551 : Blo 523799 4491551 := bstep (se 1 (by rfl) ⟨3368663, by rfl⟩ : syracuseStep 4491551 = 6737327) B6737327
theorem B12816863 : Blo 523799 12816863 := bstep (se 1 (by rfl) ⟨9612647, by rfl⟩ : syracuseStep 12816863 = 19225295) B19225295
theorem B1184399 : Blo 523799 1184399 := bstep (se 1 (by rfl) ⟨888299, by rfl⟩ : syracuseStep 1184399 = 1776599) B1776599
theorem B1119847 : Blo 523799 1119847 := bstep (se 1 (by rfl) ⟨839885, by rfl⟩ : syracuseStep 1119847 = 1679771) B1679771
theorem B1120223 : Blo 523799 1120223 := bstep (se 1 (by rfl) ⟨840167, by rfl⟩ : syracuseStep 1120223 = 1680335) B1680335
theorem B563375 : Blo 523799 563375 := bstep (se 1 (by rfl) ⟨422531, by rfl⟩ : syracuseStep 563375 = 845063) B845063
theorem B1122751 : Blo 523799 1122751 := bstep (se 1 (by rfl) ⟨842063, by rfl⟩ : syracuseStep 1122751 = 1684127) B1684127
theorem B229582511 : Blo 523799 229582511 := bstep (se 1 (by rfl) ⟨172186883, by rfl⟩ : syracuseStep 229582511 = 344373767) B344373767
theorem B38774575 : Blo 523799 38774575 := bstep (se 1 (by rfl) ⟨29080931, by rfl⟩ : syracuseStep 38774575 = 58161863) B58161863
theorem B8498135 : Blo 523799 8498135 := bstep (se 1 (by rfl) ⟨6373601, by rfl⟩ : syracuseStep 8498135 = 12747203) B12747203
theorem B568603 : Blo 523799 568603 := bstep (se 1 (by rfl) ⟨426452, by rfl⟩ : syracuseStep 568603 = 852905) B852905
theorem B2534939 : Blo 523799 2534939 := bstep (se 1 (by rfl) ⟨1901204, by rfl⟩ : syracuseStep 2534939 = 3802409) B3802409
theorem B5779025 : Blo 523799 5779025 := bstep (se 2 (by rfl) ⟨2167134, by rfl⟩ : syracuseStep 5779025 = 4334269) B4334269
theorem B15152993 : Blo 523799 15152993 := bstep (se 2 (by rfl) ⟨5682372, by rfl⟩ : syracuseStep 15152993 = 11364745) B11364745
theorem B899791 : Blo 523799 899791 := bstep (se 1 (by rfl) ⟨674843, by rfl⟩ : syracuseStep 899791 = 1349687) B1349687
theorem B20234123 : Blo 523799 20234123 := bstep (se 1 (by rfl) ⟨15175592, by rfl⟩ : syracuseStep 20234123 = 30351185) B30351185
theorem B2312155 : Blo 523799 2312155 := bstep (se 1 (by rfl) ⟨1734116, by rfl⟩ : syracuseStep 2312155 = 3468233) B3468233
theorem B2345071 : Blo 523799 2345071 := bstep (se 1 (by rfl) ⟨1758803, by rfl⟩ : syracuseStep 2345071 = 3517607) B3517607
theorem B1493311 : Blo 523799 1493311 := bstep (se 1 (by rfl) ⟨1119983, by rfl⟩ : syracuseStep 1493311 = 2239967) B2239967
theorem B34130321 : Blo 523799 34130321 := bstep (se 2 (by rfl) ⟨12798870, by rfl⟩ : syracuseStep 34130321 = 25597741) B25597741
theorem B1330931 : Blo 523799 1330931 := bstep (se 1 (by rfl) ⟨998198, by rfl⟩ : syracuseStep 1330931 = 1996397) B1996397
theorem B14409575 : Blo 523799 14409575 := bstep (se 1 (by rfl) ⟨10807181, by rfl⟩ : syracuseStep 14409575 = 21614363) B21614363
theorem B1990777 : Blo 523799 1990777 := bstep (se 2 (by rfl) ⟨746541, by rfl⟩ : syracuseStep 1990777 = 1493083) B1493083
theorem B7594721 : Blo 523799 7594721 := bstep (se 2 (by rfl) ⟨2848020, by rfl⟩ : syracuseStep 7594721 = 5696041) B5696041
theorem B1502459 : Blo 523799 1502459 := bstep (se 1 (by rfl) ⟨1126844, by rfl⟩ : syracuseStep 1502459 = 2253689) B2253689
theorem B6713543 : Blo 523799 6713543 := bstep (se 1 (by rfl) ⟨5035157, by rfl⟩ : syracuseStep 6713543 = 10070315) B10070315
theorem B12742919 : Blo 523799 12742919 := bstep (se 1 (by rfl) ⟨9557189, by rfl⟩ : syracuseStep 12742919 = 19114379) B19114379
theorem B5665247 : Blo 523799 5665247 := bstep (se 1 (by rfl) ⟨4248935, by rfl⟩ : syracuseStep 5665247 = 8497871) B8497871
theorem B5404325 : Blo 523799 5404325 := bstep (se 4 (by rfl) ⟨506655, by rfl⟩ : syracuseStep 5404325 = 1013311) B1013311
theorem B2654369 : Blo 523799 2654369 := bstep (se 2 (by rfl) ⟨995388, by rfl⟩ : syracuseStep 2654369 = 1990777) B1990777
theorem B524539 : Blo 523799 524539 := bstep (se 1 (by rfl) ⟨393404, by rfl⟩ : syracuseStep 524539 = 786809) B786809
theorem B9569015 : Blo 523799 9569015 := bstep (se 1 (by rfl) ⟨7176761, by rfl⟩ : syracuseStep 9569015 = 14353523) B14353523
theorem B525183 : Blo 523799 525183 := bstep (se 1 (by rfl) ⟨393887, by rfl⟩ : syracuseStep 525183 = 787775) B787775
theorem B787391 : Blo 523799 787391 := bstep (se 1 (by rfl) ⟨590543, by rfl⟩ : syracuseStep 787391 = 1181087) B1181087
theorem B887287 : Blo 523799 887287 := bstep (se 1 (by rfl) ⟨665465, by rfl⟩ : syracuseStep 887287 = 1330931) B1330931
theorem B3082873 : Blo 523799 3082873 := bstep (se 2 (by rfl) ⟨1156077, by rfl⟩ : syracuseStep 3082873 = 2312155) B2312155
theorem B789599 : Blo 523799 789599 := bstep (se 1 (by rfl) ⟨592199, by rfl⟩ : syracuseStep 789599 = 1184399) B1184399
theorem B9606383 : Blo 523799 9606383 := bstep (se 1 (by rfl) ⟨7204787, by rfl⟩ : syracuseStep 9606383 = 14409575) B14409575
theorem B8495279 : Blo 523799 8495279 := bstep (se 1 (by rfl) ⟨6371459, by rfl⟩ : syracuseStep 8495279 = 12742919) B12742919
theorem B3776831 : Blo 523799 3776831 := bstep (se 1 (by rfl) ⟨2832623, by rfl⟩ : syracuseStep 3776831 = 5665247) B5665247
theorem B10101995 : Blo 523799 10101995 := bstep (se 1 (by rfl) ⟨7576496, by rfl⟩ : syracuseStep 10101995 = 15152993) B15152993
theorem B2993435 : Blo 523799 2993435 := bstep (se 1 (by rfl) ⟨2245076, by rfl⟩ : syracuseStep 2993435 = 4490153) B4490153
theorem B2666681 : Blo 523799 2666681 := bstep (se 2 (by rfl) ⟨1000005, by rfl⟩ : syracuseStep 2666681 = 2000011) B2000011
theorem B2994367 : Blo 523799 2994367 := bstep (se 1 (by rfl) ⟨2245775, by rfl⟩ : syracuseStep 2994367 = 4491551) B4491551
theorem B22753547 : Blo 523799 22753547 := bstep (se 1 (by rfl) ⟨17065160, by rfl⟩ : syracuseStep 22753547 = 34130321) B34130321
theorem B54571657 : Blo 523799 54571657 := bstep (se 2 (by rfl) ⟨20464371, by rfl⟩ : syracuseStep 54571657 = 40928743) B40928743
theorem B3126761 : Blo 523799 3126761 := bstep (se 2 (by rfl) ⟨1172535, by rfl⟩ : syracuseStep 3126761 = 2345071) B2345071
theorem B5063147 : Blo 523799 5063147 := bstep (se 1 (by rfl) ⟨3797360, by rfl⟩ : syracuseStep 5063147 = 7594721) B7594721
theorem B3032549 : Blo 523799 3032549 := bstep (se 4 (by rfl) ⟨284301, by rfl⟩ : syracuseStep 3032549 = 568603) B568603
theorem B1493129 : Blo 523799 1493129 := bstep (se 2 (by rfl) ⟨559923, by rfl⟩ : syracuseStep 1493129 = 1119847) B1119847
theorem B1001639 : Blo 523799 1001639 := bstep (se 1 (by rfl) ⟨751229, by rfl⟩ : syracuseStep 1001639 = 1502459) B1502459
theorem B1689959 : Blo 523799 1689959 := bstep (se 1 (by rfl) ⟨1267469, by rfl⟩ : syracuseStep 1689959 = 2534939) B2534939
theorem B3852683 : Blo 523799 3852683 := bstep (se 1 (by rfl) ⟨2889512, by rfl⟩ : syracuseStep 3852683 = 5779025) B5779025
theorem B4475695 : Blo 523799 4475695 := bstep (se 1 (by rfl) ⟨3356771, by rfl⟩ : syracuseStep 4475695 = 6713543) B6713543
theorem B13489415 : Blo 523799 13489415 := bstep (se 1 (by rfl) ⟨10117061, by rfl⟩ : syracuseStep 13489415 = 20234123) B20234123
theorem B5988005 : Blo 523799 5988005 := bstep (se 4 (by rfl) ⟨561375, by rfl⟩ : syracuseStep 5988005 = 1122751) B1122751
theorem B51699433 : Blo 523799 51699433 := bstep (se 2 (by rfl) ⟨19387287, by rfl⟩ : syracuseStep 51699433 = 38774575) B38774575
theorem B8544575 : Blo 523799 8544575 := bstep (se 1 (by rfl) ⟨6408431, by rfl⟩ : syracuseStep 8544575 = 12816863) B12816863
theorem B1991081 : Blo 523799 1991081 := bstep (se 2 (by rfl) ⟨746655, by rfl⟩ : syracuseStep 1991081 = 1493311) B1493311
theorem B746815 : Blo 523799 746815 := bstep (se 1 (by rfl) ⟨560111, by rfl⟩ : syracuseStep 746815 = 1120223) B1120223
theorem B19195541 : Blo 523799 19195541 := bstep (se 6 (by rfl) ⟨449895, by rfl⟩ : syracuseStep 19195541 = 899791) B899791
theorem B14411533 : Blo 523799 14411533 := bstep (se 3 (by rfl) ⟨2702162, by rfl⟩ : syracuseStep 14411533 = 5404325) B5404325
theorem B1502333 : Blo 523799 1502333 := bstep (se 3 (by rfl) ⟨281687, by rfl⟩ : syracuseStep 1502333 = 563375) B563375
theorem B153055007 : Blo 523799 153055007 := bstep (se 1 (by rfl) ⟨114791255, by rfl⟩ : syracuseStep 153055007 = 229582511) B229582511
theorem B5665423 : Blo 523799 5665423 := bstep (se 1 (by rfl) ⟨4249067, by rfl⟩ : syracuseStep 5665423 = 8498135) B8498135
theorem B1769579 : Blo 523799 1769579 := bstep (se 1 (by rfl) ⟨1327184, by rfl⟩ : syracuseStep 1769579 = 2654369) B2654369
theorem B3375431 : Blo 523799 3375431 := bstep (se 1 (by rfl) ⟨2531573, by rfl⟩ : syracuseStep 3375431 = 5063147) B5063147
theorem B524927 : Blo 523799 524927 := bstep (se 1 (by rfl) ⟨393695, by rfl⟩ : syracuseStep 524927 = 787391) B787391
theorem B526399 : Blo 523799 526399 := bstep (se 1 (by rfl) ⟨394799, by rfl⟩ : syracuseStep 526399 = 789599) B789599
theorem B1183049 : Blo 523799 1183049 := bstep (se 2 (by rfl) ⟨443643, by rfl⟩ : syracuseStep 1183049 = 887287) B887287
theorem B5967593 : Blo 523799 5967593 := bstep (se 2 (by rfl) ⟨2237847, by rfl⟩ : syracuseStep 5967593 = 4475695) B4475695
theorem B1777787 : Blo 523799 1777787 := bstep (se 1 (by rfl) ⟨1333340, by rfl⟩ : syracuseStep 1777787 = 2666681) B2666681
theorem B22785533 : Blo 523799 22785533 := bstep (se 3 (by rfl) ⟨4272287, by rfl⟩ : syracuseStep 22785533 = 8544575) B8544575
theorem B995419 : Blo 523799 995419 := bstep (se 1 (by rfl) ⟨746564, by rfl⟩ : syracuseStep 995419 = 1493129) B1493129
theorem B667759 : Blo 523799 667759 := bstep (se 1 (by rfl) ⟨500819, by rfl⟩ : syracuseStep 667759 = 1001639) B1001639
theorem B1126639 : Blo 523799 1126639 := bstep (se 1 (by rfl) ⟨844979, by rfl⟩ : syracuseStep 1126639 = 1689959) B1689959
theorem B2568455 : Blo 523799 2568455 := bstep (se 1 (by rfl) ⟨1926341, by rfl⟩ : syracuseStep 2568455 = 3852683) B3852683
theorem B995753 : Blo 523799 995753 := bstep (se 2 (by rfl) ⟨373407, by rfl⟩ : syracuseStep 995753 = 746815) B746815
theorem B19215377 : Blo 523799 19215377 := bstep (se 2 (by rfl) ⟨7205766, by rfl⟩ : syracuseStep 19215377 = 14411533) B14411533
theorem B6404255 : Blo 523799 6404255 := bstep (se 1 (by rfl) ⟨4803191, by rfl⟩ : syracuseStep 6404255 = 9606383) B9606383
theorem B4110497 : Blo 523799 4110497 := bstep (se 2 (by rfl) ⟨1541436, by rfl⟩ : syracuseStep 4110497 = 3082873) B3082873
theorem B8992943 : Blo 523799 8992943 := bstep (se 1 (by rfl) ⟨6744707, by rfl⟩ : syracuseStep 8992943 = 13489415) B13489415
theorem B1327387 : Blo 523799 1327387 := bstep (se 1 (by rfl) ⟨995540, by rfl⟩ : syracuseStep 1327387 = 1991081) B1991081
theorem B6734663 : Blo 523799 6734663 := bstep (se 1 (by rfl) ⟨5050997, by rfl⟩ : syracuseStep 6734663 = 10101995) B10101995
theorem B72762209 : Blo 523799 72762209 := bstep (se 2 (by rfl) ⟨27285828, by rfl⟩ : syracuseStep 72762209 = 54571657) B54571657
theorem B7553897 : Blo 523799 7553897 := bstep (se 2 (by rfl) ⟨2832711, by rfl⟩ : syracuseStep 7553897 = 5665423) B5665423
theorem B12797027 : Blo 523799 12797027 := bstep (se 1 (by rfl) ⟨9597770, by rfl⟩ : syracuseStep 12797027 = 19195541) B19195541
theorem B1001555 : Blo 523799 1001555 := bstep (se 1 (by rfl) ⟨751166, by rfl⟩ : syracuseStep 1001555 = 1502333) B1502333
theorem B2084507 : Blo 523799 2084507 := bstep (se 1 (by rfl) ⟨1563380, by rfl⟩ : syracuseStep 2084507 = 3126761) B3126761
theorem B68932577 : Blo 523799 68932577 := bstep (se 2 (by rfl) ⟨25849716, by rfl⟩ : syracuseStep 68932577 = 51699433) B51699433
theorem B6379343 : Blo 523799 6379343 := bstep (se 1 (by rfl) ⟨4784507, by rfl⟩ : syracuseStep 6379343 = 9569015) B9569015
theorem B2021699 : Blo 523799 2021699 := bstep (se 1 (by rfl) ⟨1516274, by rfl⟩ : syracuseStep 2021699 = 3032549) B3032549
theorem B3992003 : Blo 523799 3992003 := bstep (se 1 (by rfl) ⟨2994002, by rfl⟩ : syracuseStep 3992003 = 5988005) B5988005
theorem B5663519 : Blo 523799 5663519 := bstep (se 1 (by rfl) ⟨4247639, by rfl⟩ : syracuseStep 5663519 = 8495279) B8495279
theorem B2517887 : Blo 523799 2517887 := bstep (se 1 (by rfl) ⟨1888415, by rfl⟩ : syracuseStep 2517887 = 3776831) B3776831
theorem B3992489 : Blo 523799 3992489 := bstep (se 2 (by rfl) ⟨1497183, by rfl⟩ : syracuseStep 3992489 = 2994367) B2994367
theorem B1995623 : Blo 523799 1995623 := bstep (se 1 (by rfl) ⟨1496717, by rfl⟩ : syracuseStep 1995623 = 2993435) B2993435
theorem B102036671 : Blo 523799 102036671 := bstep (se 1 (by rfl) ⟨76527503, by rfl⟩ : syracuseStep 102036671 = 153055007) B153055007
theorem B15169031 : Blo 523799 15169031 := bstep (se 1 (by rfl) ⟨11376773, by rfl⟩ : syracuseStep 15169031 = 22753547) B22753547
theorem B1179719 : Blo 523799 1179719 := bstep (se 1 (by rfl) ⟨884789, by rfl⟩ : syracuseStep 1179719 = 1769579) B1769579
theorem B1769849 : Blo 523799 1769849 := bstep (se 2 (by rfl) ⟨663693, by rfl⟩ : syracuseStep 1769849 = 1327387) B1327387
theorem B4489775 : Blo 523799 4489775 := bstep (se 1 (by rfl) ⟨3367331, by rfl⟩ : syracuseStep 4489775 = 6734663) B6734663
theorem B2655341 : Blo 523799 2655341 := bstep (se 3 (by rfl) ⟨497876, by rfl⟩ : syracuseStep 2655341 = 995753) B995753
theorem B788699 : Blo 523799 788699 := bstep (se 1 (by rfl) ⟨591524, by rfl⟩ : syracuseStep 788699 = 1183049) B1183049
theorem B1185191 : Blo 523799 1185191 := bstep (se 1 (by rfl) ⟨888893, by rfl⟩ : syracuseStep 1185191 = 1777787) B1777787
theorem B890345 : Blo 523799 890345 := bstep (se 2 (by rfl) ⟨333879, by rfl⟩ : syracuseStep 890345 = 667759) B667759
theorem B2661335 : Blo 523799 2661335 := bstep (se 1 (by rfl) ⟨1996001, by rfl⟩ : syracuseStep 2661335 = 3992003) B3992003
theorem B3775679 : Blo 523799 3775679 := bstep (se 1 (by rfl) ⟨2831759, by rfl⟩ : syracuseStep 3775679 = 5663519) B5663519
theorem B1678591 : Blo 523799 1678591 := bstep (se 1 (by rfl) ⟨1258943, by rfl⟩ : syracuseStep 1678591 = 2517887) B2517887
theorem B2661659 : Blo 523799 2661659 := bstep (se 1 (by rfl) ⟨1996244, by rfl⟩ : syracuseStep 2661659 = 3992489) B3992489
theorem B1712303 : Blo 523799 1712303 := bstep (se 1 (by rfl) ⟨1284227, by rfl⟩ : syracuseStep 1712303 = 2568455) B2568455
theorem B4269503 : Blo 523799 4269503 := bstep (se 1 (by rfl) ⟨3202127, by rfl⟩ : syracuseStep 4269503 = 6404255) B6404255
theorem B48508139 : Blo 523799 48508139 := bstep (se 1 (by rfl) ⟨36381104, by rfl⟩ : syracuseStep 48508139 = 72762209) B72762209
theorem B8531351 : Blo 523799 8531351 := bstep (se 1 (by rfl) ⟨6398513, by rfl⟩ : syracuseStep 8531351 = 12797027) B12797027
theorem B667703 : Blo 523799 667703 := bstep (se 1 (by rfl) ⟨500777, by rfl⟩ : syracuseStep 667703 = 1001555) B1001555
theorem B1389671 : Blo 523799 1389671 := bstep (se 1 (by rfl) ⟨1042253, by rfl⟩ : syracuseStep 1389671 = 2084507) B2084507
theorem B3978395 : Blo 523799 3978395 := bstep (se 1 (by rfl) ⟨2983796, by rfl⟩ : syracuseStep 3978395 = 5967593) B5967593
theorem B1327225 : Blo 523799 1327225 := bstep (se 2 (by rfl) ⟨497709, by rfl⟩ : syracuseStep 1327225 = 995419) B995419
theorem B5391197 : Blo 523799 5391197 := bstep (se 3 (by rfl) ⟨1010849, by rfl⟩ : syracuseStep 5391197 = 2021699) B2021699
theorem B15190355 : Blo 523799 15190355 := bstep (se 1 (by rfl) ⟨11392766, by rfl⟩ : syracuseStep 15190355 = 22785533) B22785533
theorem B1330415 : Blo 523799 1330415 := bstep (se 1 (by rfl) ⟨997811, by rfl⟩ : syracuseStep 1330415 = 1995623) B1995623
theorem B10112687 : Blo 523799 10112687 := bstep (se 1 (by rfl) ⟨7584515, by rfl⟩ : syracuseStep 10112687 = 15169031) B15169031
theorem B2740331 : Blo 523799 2740331 := bstep (se 1 (by rfl) ⟨2055248, by rfl⟩ : syracuseStep 2740331 = 4110497) B4110497
theorem B2250287 : Blo 523799 2250287 := bstep (se 1 (by rfl) ⟨1687715, by rfl⟩ : syracuseStep 2250287 = 3375431) B3375431
theorem B5035931 : Blo 523799 5035931 := bstep (se 1 (by rfl) ⟨3776948, by rfl⟩ : syracuseStep 5035931 = 7553897) B7553897
theorem B183820205 : Blo 523799 183820205 := bstep (se 3 (by rfl) ⟨34466288, by rfl⟩ : syracuseStep 183820205 = 68932577) B68932577
theorem B4252895 : Blo 523799 4252895 := bstep (se 1 (by rfl) ⟨3189671, by rfl⟩ : syracuseStep 4252895 = 6379343) B6379343
theorem B1502185 : Blo 523799 1502185 := bstep (se 2 (by rfl) ⟨563319, by rfl⟩ : syracuseStep 1502185 = 1126639) B1126639
theorem B12810251 : Blo 523799 12810251 := bstep (se 1 (by rfl) ⟨9607688, by rfl⟩ : syracuseStep 12810251 = 19215377) B19215377
theorem B68024447 : Blo 523799 68024447 := bstep (se 1 (by rfl) ⟨51018335, by rfl⟩ : syracuseStep 68024447 = 102036671) B102036671
theorem B5995295 : Blo 523799 5995295 := bstep (se 1 (by rfl) ⟨4496471, by rfl⟩ : syracuseStep 5995295 = 8992943) B8992943
theorem B786479 : Blo 523799 786479 := bstep (se 1 (by rfl) ⟨589859, by rfl⟩ : syracuseStep 786479 = 1179719) B1179719
theorem B1769633 : Blo 523799 1769633 := bstep (se 2 (by rfl) ⟨663612, by rfl⟩ : syracuseStep 1769633 = 1327225) B1327225
theorem B1179899 : Blo 523799 1179899 := bstep (se 1 (by rfl) ⟨884924, by rfl⟩ : syracuseStep 1179899 = 1769849) B1769849
theorem B1770227 : Blo 523799 1770227 := bstep (se 1 (by rfl) ⟨1327670, by rfl⟩ : syracuseStep 1770227 = 2655341) B2655341
theorem B525799 : Blo 523799 525799 := bstep (se 1 (by rfl) ⟨394349, by rfl⟩ : syracuseStep 525799 = 788699) B788699
theorem B10126903 : Blo 523799 10126903 := bstep (se 1 (by rfl) ⟨7595177, by rfl⟩ : syracuseStep 10126903 = 15190355) B15190355
theorem B886943 : Blo 523799 886943 := bstep (se 1 (by rfl) ⟨665207, by rfl⟩ : syracuseStep 886943 = 1330415) B1330415
theorem B790127 : Blo 523799 790127 := bstep (se 1 (by rfl) ⟨592595, by rfl⟩ : syracuseStep 790127 = 1185191) B1185191
theorem B593563 : Blo 523799 593563 := bstep (se 1 (by rfl) ⟨445172, by rfl⟩ : syracuseStep 593563 = 890345) B890345
theorem B2002913 : Blo 523799 2002913 := bstep (se 2 (by rfl) ⟨751092, by rfl⟩ : syracuseStep 2002913 = 1502185) B1502185
theorem B1774223 : Blo 523799 1774223 := bstep (se 1 (by rfl) ⟨1330667, by rfl⟩ : syracuseStep 1774223 = 2661335) B2661335
theorem B1774439 : Blo 523799 1774439 := bstep (se 1 (by rfl) ⟨1330829, by rfl⟩ : syracuseStep 1774439 = 2661659) B2661659
theorem B926447 : Blo 523799 926447 := bstep (se 1 (by rfl) ⟨694835, by rfl⟩ : syracuseStep 926447 = 1389671) B1389671
theorem B2238121 : Blo 523799 2238121 := bstep (se 2 (by rfl) ⟨839295, by rfl⟩ : syracuseStep 2238121 = 1678591) B1678591
theorem B1780541 : Blo 523799 1780541 := bstep (se 3 (by rfl) ⟨333851, by rfl⟩ : syracuseStep 1780541 = 667703) B667703
theorem B2993183 : Blo 523799 2993183 := bstep (se 1 (by rfl) ⟨2244887, by rfl⟩ : syracuseStep 2993183 = 4489775) B4489775
theorem B3357287 : Blo 523799 3357287 := bstep (se 1 (by rfl) ⟨2517965, by rfl⟩ : syracuseStep 3357287 = 5035931) B5035931
theorem B2835263 : Blo 523799 2835263 := bstep (se 1 (by rfl) ⟨2126447, by rfl⟩ : syracuseStep 2835263 = 4252895) B4252895
theorem B5687567 : Blo 523799 5687567 := bstep (se 1 (by rfl) ⟨4265675, by rfl⟩ : syracuseStep 5687567 = 8531351) B8531351
theorem B8540167 : Blo 523799 8540167 := bstep (se 1 (by rfl) ⟨6405125, by rfl⟩ : syracuseStep 8540167 = 12810251) B12810251
theorem B3594131 : Blo 523799 3594131 := bstep (se 1 (by rfl) ⟨2695598, by rfl⟩ : syracuseStep 3594131 = 5391197) B5391197
theorem B6741791 : Blo 523799 6741791 := bstep (se 1 (by rfl) ⟨5056343, by rfl⟩ : syracuseStep 6741791 = 10112687) B10112687
theorem B1826887 : Blo 523799 1826887 := bstep (se 1 (by rfl) ⟨1370165, by rfl⟩ : syracuseStep 1826887 = 2740331) B2740331
theorem B1500191 : Blo 523799 1500191 := bstep (se 1 (by rfl) ⟨1125143, by rfl⟩ : syracuseStep 1500191 = 2250287) B2250287
theorem B2517119 : Blo 523799 2517119 := bstep (se 1 (by rfl) ⟨1887839, by rfl⟩ : syracuseStep 2517119 = 3775679) B3775679
theorem B122546803 : Blo 523799 122546803 := bstep (se 1 (by rfl) ⟨91910102, by rfl⟩ : syracuseStep 122546803 = 183820205) B183820205
theorem B1141535 : Blo 523799 1141535 := bstep (se 1 (by rfl) ⟨856151, by rfl⟩ : syracuseStep 1141535 = 1712303) B1712303
theorem B2846335 : Blo 523799 2846335 := bstep (se 1 (by rfl) ⟨2134751, by rfl⟩ : syracuseStep 2846335 = 4269503) B4269503
theorem B32338759 : Blo 523799 32338759 := bstep (se 1 (by rfl) ⟨24254069, by rfl⟩ : syracuseStep 32338759 = 48508139) B48508139
theorem B2652263 : Blo 523799 2652263 := bstep (se 1 (by rfl) ⟨1989197, by rfl⟩ : syracuseStep 2652263 = 3978395) B3978395
theorem B45349631 : Blo 523799 45349631 := bstep (se 1 (by rfl) ⟨34012223, by rfl⟩ : syracuseStep 45349631 = 68024447) B68024447
theorem B3996863 : Blo 523799 3996863 := bstep (se 1 (by rfl) ⟨2997647, by rfl⟩ : syracuseStep 3996863 = 5995295) B5995295
theorem B524319 : Blo 523799 524319 := bstep (se 1 (by rfl) ⟨393239, by rfl⟩ : syracuseStep 524319 = 786479) B786479
theorem B1179755 : Blo 523799 1179755 := bstep (se 1 (by rfl) ⟨884816, by rfl⟩ : syracuseStep 1179755 = 1769633) B1769633
theorem B786599 : Blo 523799 786599 := bstep (se 1 (by rfl) ⟨589949, by rfl⟩ : syracuseStep 786599 = 1179899) B1179899
theorem B1180151 : Blo 523799 1180151 := bstep (se 1 (by rfl) ⟨885113, by rfl⟩ : syracuseStep 1180151 = 1770227) B1770227
theorem B591295 : Blo 523799 591295 := bstep (se 1 (by rfl) ⟨443471, by rfl⟩ : syracuseStep 591295 = 886943) B886943
theorem B13502537 : Blo 523799 13502537 := bstep (se 2 (by rfl) ⟨5063451, by rfl⟩ : syracuseStep 13502537 = 10126903) B10126903
theorem B2984161 : Blo 523799 2984161 := bstep (se 2 (by rfl) ⟨1119060, by rfl⟩ : syracuseStep 2984161 = 2238121) B2238121
theorem B526751 : Blo 523799 526751 := bstep (se 1 (by rfl) ⟨395063, by rfl⟩ : syracuseStep 526751 = 790127) B790127
theorem B1182815 : Blo 523799 1182815 := bstep (se 1 (by rfl) ⟨887111, by rfl⟩ : syracuseStep 1182815 = 1774223) B1774223
theorem B1182959 : Blo 523799 1182959 := bstep (se 1 (by rfl) ⟨887219, by rfl⟩ : syracuseStep 1182959 = 1774439) B1774439
theorem B2396087 : Blo 523799 2396087 := bstep (se 1 (by rfl) ⟨1797065, by rfl⟩ : syracuseStep 2396087 = 3594131) B3594131
theorem B791417 : Blo 523799 791417 := bstep (se 2 (by rfl) ⟨296781, by rfl⟩ : syracuseStep 791417 = 593563) B593563
theorem B4494527 : Blo 523799 4494527 := bstep (se 1 (by rfl) ⟨3370895, by rfl⟩ : syracuseStep 4494527 = 6741791) B6741791
theorem B1678079 : Blo 523799 1678079 := bstep (se 1 (by rfl) ⟨1258559, by rfl⟩ : syracuseStep 1678079 = 2517119) B2517119
theorem B761023 : Blo 523799 761023 := bstep (se 1 (by rfl) ⟨570767, by rfl⟩ : syracuseStep 761023 = 1141535) B1141535
theorem B1187027 : Blo 523799 1187027 := bstep (se 1 (by rfl) ⟨890270, by rfl⟩ : syracuseStep 1187027 = 1780541) B1780541
theorem B2238191 : Blo 523799 2238191 := bstep (se 1 (by rfl) ⟨1678643, by rfl⟩ : syracuseStep 2238191 = 3357287) B3357287
theorem B2664575 : Blo 523799 2664575 := bstep (se 1 (by rfl) ⟨1998431, by rfl⟩ : syracuseStep 2664575 = 3996863) B3996863
theorem B2435849 : Blo 523799 2435849 := bstep (se 2 (by rfl) ⟨913443, by rfl⟩ : syracuseStep 2435849 = 1826887) B1826887
theorem B163395737 : Blo 523799 163395737 := bstep (se 2 (by rfl) ⟨61273401, by rfl⟩ : syracuseStep 163395737 = 122546803) B122546803
theorem B11386889 : Blo 523799 11386889 := bstep (se 2 (by rfl) ⟨4270083, by rfl⟩ : syracuseStep 11386889 = 8540167) B8540167
theorem B1000127 : Blo 523799 1000127 := bstep (se 1 (by rfl) ⟨750095, by rfl⟩ : syracuseStep 1000127 = 1500191) B1500191
theorem B9882101 : Blo 523799 9882101 := bstep (se 5 (by rfl) ⟨463223, by rfl⟩ : syracuseStep 9882101 = 926447) B926447
theorem B30233087 : Blo 523799 30233087 := bstep (se 1 (by rfl) ⟨22674815, by rfl⟩ : syracuseStep 30233087 = 45349631) B45349631
theorem B3791711 : Blo 523799 3791711 := bstep (se 1 (by rfl) ⟨2843783, by rfl⟩ : syracuseStep 3791711 = 5687567) B5687567
theorem B7560701 : Blo 523799 7560701 := bstep (se 3 (by rfl) ⟨1417631, by rfl⟩ : syracuseStep 7560701 = 2835263) B2835263
theorem B1335275 : Blo 523799 1335275 := bstep (se 1 (by rfl) ⟨1001456, by rfl⟩ : syracuseStep 1335275 = 2002913) B2002913
theorem B3795113 : Blo 523799 3795113 := bstep (se 2 (by rfl) ⟨1423167, by rfl⟩ : syracuseStep 3795113 = 2846335) B2846335
theorem B43118345 : Blo 523799 43118345 := bstep (se 2 (by rfl) ⟨16169379, by rfl⟩ : syracuseStep 43118345 = 32338759) B32338759
theorem B1995455 : Blo 523799 1995455 := bstep (se 1 (by rfl) ⟨1496591, by rfl⟩ : syracuseStep 1995455 = 2993183) B2993183
theorem B1768175 : Blo 523799 1768175 := bstep (se 1 (by rfl) ⟨1326131, by rfl⟩ : syracuseStep 1768175 = 2652263) B2652263
theorem B786503 : Blo 523799 786503 := bstep (se 1 (by rfl) ⟨589877, by rfl⟩ : syracuseStep 786503 = 1179755) B1179755
theorem B524399 : Blo 523799 524399 := bstep (se 1 (by rfl) ⟨393299, by rfl⟩ : syracuseStep 524399 = 786599) B786599
theorem B786767 : Blo 523799 786767 := bstep (se 1 (by rfl) ⟨590075, by rfl⟩ : syracuseStep 786767 = 1180151) B1180151
theorem B6588067 : Blo 523799 6588067 := bstep (se 1 (by rfl) ⟨4941050, by rfl⟩ : syracuseStep 6588067 = 9882101) B9882101
theorem B788393 : Blo 523799 788393 := bstep (se 2 (by rfl) ⟨295647, by rfl⟩ : syracuseStep 788393 = 591295) B591295
theorem B788543 : Blo 523799 788543 := bstep (se 1 (by rfl) ⟨591407, by rfl⟩ : syracuseStep 788543 = 1182815) B1182815
theorem B788639 : Blo 523799 788639 := bstep (se 1 (by rfl) ⟨591479, by rfl⟩ : syracuseStep 788639 = 1182959) B1182959
theorem B20155391 : Blo 523799 20155391 := bstep (se 1 (by rfl) ⟨15116543, by rfl⟩ : syracuseStep 20155391 = 30233087) B30233087
theorem B527611 : Blo 523799 527611 := bstep (se 1 (by rfl) ⟨395708, by rfl⟩ : syracuseStep 527611 = 791417) B791417
theorem B1118719 : Blo 523799 1118719 := bstep (se 1 (by rfl) ⟨839039, by rfl⟩ : syracuseStep 1118719 = 1678079) B1678079
theorem B2527807 : Blo 523799 2527807 := bstep (se 1 (by rfl) ⟨1895855, by rfl⟩ : syracuseStep 2527807 = 3791711) B3791711
theorem B791351 : Blo 523799 791351 := bstep (se 1 (by rfl) ⟨593513, by rfl⟩ : syracuseStep 791351 = 1187027) B1187027
theorem B890183 : Blo 523799 890183 := bstep (se 1 (by rfl) ⟨667637, by rfl⟩ : syracuseStep 890183 = 1335275) B1335275
theorem B1776383 : Blo 523799 1776383 := bstep (se 1 (by rfl) ⟨1332287, by rfl⟩ : syracuseStep 1776383 = 2664575) B2664575
theorem B2530075 : Blo 523799 2530075 := bstep (se 1 (by rfl) ⟨1897556, by rfl⟩ : syracuseStep 2530075 = 3795113) B3795113
theorem B28745563 : Blo 523799 28745563 := bstep (se 1 (by rfl) ⟨21559172, by rfl⟩ : syracuseStep 28745563 = 43118345) B43118345
theorem B108930491 : Blo 523799 108930491 := bstep (se 1 (by rfl) ⟨81697868, by rfl⟩ : syracuseStep 108930491 = 163395737) B163395737
theorem B2667005 : Blo 523799 2667005 := bstep (se 3 (by rfl) ⟨500063, by rfl⟩ : syracuseStep 2667005 = 1000127) B1000127
theorem B3978881 : Blo 523799 3978881 := bstep (se 2 (by rfl) ⟨1492080, by rfl⟩ : syracuseStep 3978881 = 2984161) B2984161
theorem B2996351 : Blo 523799 2996351 := bstep (se 1 (by rfl) ⟨2247263, by rfl⟩ : syracuseStep 2996351 = 4494527) B4494527
theorem B1492127 : Blo 523799 1492127 := bstep (se 1 (by rfl) ⟨1119095, by rfl⟩ : syracuseStep 1492127 = 2238191) B2238191
theorem B1623899 : Blo 523799 1623899 := bstep (se 1 (by rfl) ⟨1217924, by rfl⟩ : syracuseStep 1623899 = 2435849) B2435849
theorem B1330303 : Blo 523799 1330303 := bstep (se 1 (by rfl) ⟨997727, by rfl⟩ : syracuseStep 1330303 = 1995455) B1995455
theorem B7591259 : Blo 523799 7591259 := bstep (se 1 (by rfl) ⟨5693444, by rfl⟩ : syracuseStep 7591259 = 11386889) B11386889
theorem B9001691 : Blo 523799 9001691 := bstep (se 1 (by rfl) ⟨6751268, by rfl⟩ : syracuseStep 9001691 = 13502537) B13502537
theorem B1597391 : Blo 523799 1597391 := bstep (se 1 (by rfl) ⟨1198043, by rfl⟩ : syracuseStep 1597391 = 2396087) B2396087
theorem B5040467 : Blo 523799 5040467 := bstep (se 1 (by rfl) ⟨3780350, by rfl⟩ : syracuseStep 5040467 = 7560701) B7560701
theorem B1014697 : Blo 523799 1014697 := bstep (se 2 (by rfl) ⟨380511, by rfl⟩ : syracuseStep 1014697 = 761023) B761023
theorem B1178783 : Blo 523799 1178783 := bstep (se 1 (by rfl) ⟨884087, by rfl⟩ : syracuseStep 1178783 = 1768175) B1768175
theorem B524335 : Blo 523799 524335 := bstep (se 1 (by rfl) ⟨393251, by rfl⟩ : syracuseStep 524335 = 786503) B786503
theorem B524511 : Blo 523799 524511 := bstep (se 1 (by rfl) ⟨393383, by rfl⟩ : syracuseStep 524511 = 786767) B786767
theorem B525595 : Blo 523799 525595 := bstep (se 1 (by rfl) ⟨394196, by rfl⟩ : syracuseStep 525595 = 788393) B788393
theorem B525695 : Blo 523799 525695 := bstep (se 1 (by rfl) ⟨394271, by rfl⟩ : syracuseStep 525695 = 788543) B788543
theorem B525759 : Blo 523799 525759 := bstep (se 1 (by rfl) ⟨394319, by rfl⟩ : syracuseStep 525759 = 788639) B788639
theorem B13436927 : Blo 523799 13436927 := bstep (se 1 (by rfl) ⟨10077695, by rfl⟩ : syracuseStep 13436927 = 20155391) B20155391
theorem B8784089 : Blo 523799 8784089 := bstep (se 2 (by rfl) ⟨3294033, by rfl⟩ : syracuseStep 8784089 = 6588067) B6588067
theorem B527567 : Blo 523799 527567 := bstep (se 1 (by rfl) ⟨395675, by rfl⟩ : syracuseStep 527567 = 791351) B791351
theorem B593455 : Blo 523799 593455 := bstep (se 1 (by rfl) ⟨445091, by rfl⟩ : syracuseStep 593455 = 890183) B890183
theorem B1773737 : Blo 523799 1773737 := bstep (se 2 (by rfl) ⟨665151, by rfl⟩ : syracuseStep 1773737 = 1330303) B1330303
theorem B6001127 : Blo 523799 6001127 := bstep (se 1 (by rfl) ⟨4500845, by rfl⟩ : syracuseStep 6001127 = 9001691) B9001691
theorem B1184255 : Blo 523799 1184255 := bstep (se 1 (by rfl) ⟨888191, by rfl⟩ : syracuseStep 1184255 = 1776383) B1776383
theorem B5411717 : Blo 523799 5411717 := bstep (se 4 (by rfl) ⟨507348, by rfl⟩ : syracuseStep 5411717 = 1014697) B1014697
theorem B4330397 : Blo 523799 4330397 := bstep (se 3 (by rfl) ⟨811949, by rfl⟩ : syracuseStep 4330397 = 1623899) B1623899
theorem B72620327 : Blo 523799 72620327 := bstep (se 1 (by rfl) ⟨54465245, by rfl⟩ : syracuseStep 72620327 = 108930491) B108930491
theorem B1778003 : Blo 523799 1778003 := bstep (se 1 (by rfl) ⟨1333502, by rfl⟩ : syracuseStep 1778003 = 2667005) B2667005
theorem B994751 : Blo 523799 994751 := bstep (se 1 (by rfl) ⟨746063, by rfl⟩ : syracuseStep 994751 = 1492127) B1492127
theorem B5060839 : Blo 523799 5060839 := bstep (se 1 (by rfl) ⟨3795629, by rfl⟩ : syracuseStep 5060839 = 7591259) B7591259
theorem B1064927 : Blo 523799 1064927 := bstep (se 1 (by rfl) ⟨798695, by rfl⟩ : syracuseStep 1064927 = 1597391) B1597391
theorem B1491625 : Blo 523799 1491625 := bstep (se 2 (by rfl) ⟨559359, by rfl⟩ : syracuseStep 1491625 = 1118719) B1118719
theorem B3360311 : Blo 523799 3360311 := bstep (se 1 (by rfl) ⟨2520233, by rfl⟩ : syracuseStep 3360311 = 5040467) B5040467
theorem B38327417 : Blo 523799 38327417 := bstep (se 2 (by rfl) ⟨14372781, by rfl⟩ : syracuseStep 38327417 = 28745563) B28745563
theorem B3370409 : Blo 523799 3370409 := bstep (se 2 (by rfl) ⟨1263903, by rfl⟩ : syracuseStep 3370409 = 2527807) B2527807
theorem B3373433 : Blo 523799 3373433 := bstep (se 2 (by rfl) ⟨1265037, by rfl⟩ : syracuseStep 3373433 = 2530075) B2530075
theorem B2652587 : Blo 523799 2652587 := bstep (se 1 (by rfl) ⟨1989440, by rfl⟩ : syracuseStep 2652587 = 3978881) B3978881
theorem B1997567 : Blo 523799 1997567 := bstep (se 1 (by rfl) ⟨1498175, by rfl⟩ : syracuseStep 1997567 = 2996351) B2996351
theorem B785855 : Blo 523799 785855 := bstep (se 1 (by rfl) ⟨589391, by rfl⟩ : syracuseStep 785855 = 1178783) B1178783
theorem B1182491 : Blo 523799 1182491 := bstep (se 1 (by rfl) ⟨886868, by rfl⟩ : syracuseStep 1182491 = 1773737) B1773737
theorem B4000751 : Blo 523799 4000751 := bstep (se 1 (by rfl) ⟨3000563, by rfl⟩ : syracuseStep 4000751 = 6001127) B6001127
theorem B789503 : Blo 523799 789503 := bstep (se 1 (by rfl) ⟨592127, by rfl⟩ : syracuseStep 789503 = 1184255) B1184255
theorem B3607811 : Blo 523799 3607811 := bstep (se 1 (by rfl) ⟨2705858, by rfl⟩ : syracuseStep 3607811 = 5411717) B5411717
theorem B2886931 : Blo 523799 2886931 := bstep (se 1 (by rfl) ⟨2165198, by rfl⟩ : syracuseStep 2886931 = 4330397) B4330397
theorem B791273 : Blo 523799 791273 := bstep (se 2 (by rfl) ⟨296727, by rfl⟩ : syracuseStep 791273 = 593455) B593455
theorem B1185335 : Blo 523799 1185335 := bstep (se 1 (by rfl) ⟨889001, by rfl⟩ : syracuseStep 1185335 = 1778003) B1778003
theorem B663167 : Blo 523799 663167 := bstep (se 1 (by rfl) ⟨497375, by rfl⟩ : syracuseStep 663167 = 994751) B994751
theorem B2240207 : Blo 523799 2240207 := bstep (se 1 (by rfl) ⟨1680155, by rfl⟩ : syracuseStep 2240207 = 3360311) B3360311
theorem B8957951 : Blo 523799 8957951 := bstep (se 1 (by rfl) ⟨6718463, by rfl⟩ : syracuseStep 8957951 = 13436927) B13436927
theorem B48413551 : Blo 523799 48413551 := bstep (se 1 (by rfl) ⟨36310163, by rfl⟩ : syracuseStep 48413551 = 72620327) B72620327
theorem B2246939 : Blo 523799 2246939 := bstep (se 1 (by rfl) ⟨1685204, by rfl⟩ : syracuseStep 2246939 = 3370409) B3370409
theorem B2248955 : Blo 523799 2248955 := bstep (se 1 (by rfl) ⟨1686716, by rfl⟩ : syracuseStep 2248955 = 3373433) B3373433
theorem B1331711 : Blo 523799 1331711 := bstep (se 1 (by rfl) ⟨998783, by rfl⟩ : syracuseStep 1331711 = 1997567) B1997567
theorem B2839805 : Blo 523799 2839805 := bstep (se 3 (by rfl) ⟨532463, by rfl⟩ : syracuseStep 2839805 = 1064927) B1064927
theorem B1988833 : Blo 523799 1988833 := bstep (se 2 (by rfl) ⟨745812, by rfl⟩ : syracuseStep 1988833 = 1491625) B1491625
theorem B5856059 : Blo 523799 5856059 := bstep (se 1 (by rfl) ⟨4392044, by rfl⟩ : syracuseStep 5856059 = 8784089) B8784089
theorem B25551611 : Blo 523799 25551611 := bstep (se 1 (by rfl) ⟨19163708, by rfl⟩ : syracuseStep 25551611 = 38327417) B38327417
theorem B6747785 : Blo 523799 6747785 := bstep (se 2 (by rfl) ⟨2530419, by rfl⟩ : syracuseStep 6747785 = 5060839) B5060839
theorem B1768391 : Blo 523799 1768391 := bstep (se 1 (by rfl) ⟨1326293, by rfl⟩ : syracuseStep 1768391 = 2652587) B2652587
theorem B523903 : Blo 523799 523903 := bstep (se 1 (by rfl) ⟨392927, by rfl⟩ : syracuseStep 523903 = 785855) B785855
theorem B788327 : Blo 523799 788327 := bstep (se 1 (by rfl) ⟨591245, by rfl⟩ : syracuseStep 788327 = 1182491) B1182491
theorem B526335 : Blo 523799 526335 := bstep (se 1 (by rfl) ⟨394751, by rfl⟩ : syracuseStep 526335 = 789503) B789503
theorem B887807 : Blo 523799 887807 := bstep (se 1 (by rfl) ⟨665855, by rfl⟩ : syracuseStep 887807 = 1331711) B1331711
theorem B527515 : Blo 523799 527515 := bstep (se 1 (by rfl) ⟨395636, by rfl⟩ : syracuseStep 527515 = 791273) B791273
theorem B790223 : Blo 523799 790223 := bstep (se 1 (by rfl) ⟨592667, by rfl⟩ : syracuseStep 790223 = 1185335) B1185335
theorem B3904039 : Blo 523799 3904039 := bstep (se 1 (by rfl) ⟨2928029, by rfl⟩ : syracuseStep 3904039 = 5856059) B5856059
theorem B5971967 : Blo 523799 5971967 := bstep (se 1 (by rfl) ⟨4478975, by rfl⟩ : syracuseStep 5971967 = 8957951) B8957951
theorem B4498523 : Blo 523799 4498523 := bstep (se 1 (by rfl) ⟨3373892, by rfl⟩ : syracuseStep 4498523 = 6747785) B6747785
theorem B2667167 : Blo 523799 2667167 := bstep (se 1 (by rfl) ⟨2000375, by rfl⟩ : syracuseStep 2667167 = 4000751) B4000751
theorem B2405207 : Blo 523799 2405207 := bstep (se 1 (by rfl) ⟨1803905, by rfl⟩ : syracuseStep 2405207 = 3607811) B3607811
theorem B3849241 : Blo 523799 3849241 := bstep (se 2 (by rfl) ⟨1443465, by rfl⟩ : syracuseStep 3849241 = 2886931) B2886931
theorem B1493471 : Blo 523799 1493471 := bstep (se 1 (by rfl) ⟨1120103, by rfl⟩ : syracuseStep 1493471 = 2240207) B2240207
theorem B1497959 : Blo 523799 1497959 := bstep (se 1 (by rfl) ⟨1123469, by rfl⟩ : syracuseStep 1497959 = 2246939) B2246939
theorem B1499303 : Blo 523799 1499303 := bstep (se 1 (by rfl) ⟨1124477, by rfl⟩ : syracuseStep 1499303 = 2248955) B2248955
theorem B1893203 : Blo 523799 1893203 := bstep (se 1 (by rfl) ⟨1419902, by rfl⟩ : syracuseStep 1893203 = 2839805) B2839805
theorem B17034407 : Blo 523799 17034407 := bstep (se 1 (by rfl) ⟨12775805, by rfl⟩ : syracuseStep 17034407 = 25551611) B25551611
theorem B2651777 : Blo 523799 2651777 := bstep (se 2 (by rfl) ⟨994416, by rfl⟩ : syracuseStep 2651777 = 1988833) B1988833
theorem B64551401 : Blo 523799 64551401 := bstep (se 2 (by rfl) ⟨24206775, by rfl⟩ : syracuseStep 64551401 = 48413551) B48413551
theorem B1768445 : Blo 523799 1768445 := bstep (se 3 (by rfl) ⟨331583, by rfl⟩ : syracuseStep 1768445 = 663167) B663167
theorem B1178927 : Blo 523799 1178927 := bstep (se 1 (by rfl) ⟨884195, by rfl⟩ : syracuseStep 1178927 = 1768391) B1768391
theorem B525551 : Blo 523799 525551 := bstep (se 1 (by rfl) ⟨394163, by rfl⟩ : syracuseStep 525551 = 788327) B788327
theorem B591871 : Blo 523799 591871 := bstep (se 1 (by rfl) ⟨443903, by rfl⟩ : syracuseStep 591871 = 887807) B887807
theorem B526815 : Blo 523799 526815 := bstep (se 1 (by rfl) ⟨395111, by rfl⟩ : syracuseStep 526815 = 790223) B790223
theorem B1778111 : Blo 523799 1778111 := bstep (se 1 (by rfl) ⟨1333583, by rfl⟩ : syracuseStep 1778111 = 2667167) B2667167
theorem B43034267 : Blo 523799 43034267 := bstep (se 1 (by rfl) ⟨32275700, by rfl⟩ : syracuseStep 43034267 = 64551401) B64551401
theorem B995647 : Blo 523799 995647 := bstep (se 1 (by rfl) ⟨746735, by rfl⟩ : syracuseStep 995647 = 1493471) B1493471
theorem B998639 : Blo 523799 998639 := bstep (se 1 (by rfl) ⟨748979, by rfl⟩ : syracuseStep 998639 = 1497959) B1497959
theorem B3981311 : Blo 523799 3981311 := bstep (se 1 (by rfl) ⟨2985983, by rfl⟩ : syracuseStep 3981311 = 5971967) B5971967
theorem B999535 : Blo 523799 999535 := bstep (se 1 (by rfl) ⟨749651, by rfl⟩ : syracuseStep 999535 = 1499303) B1499303
theorem B1262135 : Blo 523799 1262135 := bstep (se 1 (by rfl) ⟨946601, by rfl⟩ : syracuseStep 1262135 = 1893203) B1893203
theorem B2999015 : Blo 523799 2999015 := bstep (se 1 (by rfl) ⟨2249261, by rfl⟩ : syracuseStep 2999015 = 4498523) B4498523
theorem B11356271 : Blo 523799 11356271 := bstep (se 1 (by rfl) ⟨8517203, by rfl⟩ : syracuseStep 11356271 = 17034407) B17034407
theorem B5132321 : Blo 523799 5132321 := bstep (se 2 (by rfl) ⟨1924620, by rfl⟩ : syracuseStep 5132321 = 3849241) B3849241
theorem B5205385 : Blo 523799 5205385 := bstep (se 2 (by rfl) ⟨1952019, by rfl⟩ : syracuseStep 5205385 = 3904039) B3904039
theorem B1603471 : Blo 523799 1603471 := bstep (se 1 (by rfl) ⟨1202603, by rfl⟩ : syracuseStep 1603471 = 2405207) B2405207
theorem B1767851 : Blo 523799 1767851 := bstep (se 1 (by rfl) ⟨1325888, by rfl⟩ : syracuseStep 1767851 = 2651777) B2651777
theorem B1178963 : Blo 523799 1178963 := bstep (se 1 (by rfl) ⟨884222, by rfl⟩ : syracuseStep 1178963 = 1768445) B1768445
theorem B785951 : Blo 523799 785951 := bstep (se 1 (by rfl) ⟨589463, by rfl⟩ : syracuseStep 785951 = 1178927) B1178927
theorem B1999343 : Blo 523799 1999343 := bstep (se 1 (by rfl) ⟨1499507, by rfl⟩ : syracuseStep 1999343 = 2999015) B2999015
theorem B7570847 : Blo 523799 7570847 := bstep (se 1 (by rfl) ⟨5678135, by rfl⟩ : syracuseStep 7570847 = 11356271) B11356271
theorem B789161 : Blo 523799 789161 := bstep (se 2 (by rfl) ⟨295935, by rfl⟩ : syracuseStep 789161 = 591871) B591871
theorem B1185407 : Blo 523799 1185407 := bstep (se 1 (by rfl) ⟨889055, by rfl⟩ : syracuseStep 1185407 = 1778111) B1778111
theorem B2137961 : Blo 523799 2137961 := bstep (se 2 (by rfl) ⟨801735, by rfl⟩ : syracuseStep 2137961 = 1603471) B1603471
theorem B665759 : Blo 523799 665759 := bstep (se 1 (by rfl) ⟨499319, by rfl⟩ : syracuseStep 665759 = 998639) B998639
theorem B3421547 : Blo 523799 3421547 := bstep (se 1 (by rfl) ⟨2566160, by rfl⟩ : syracuseStep 3421547 = 5132321) B5132321
theorem B1327529 : Blo 523799 1327529 := bstep (se 2 (by rfl) ⟨497823, by rfl⟩ : syracuseStep 1327529 = 995647) B995647
theorem B2654207 : Blo 523799 2654207 := bstep (se 1 (by rfl) ⟨1990655, by rfl⟩ : syracuseStep 2654207 = 3981311) B3981311
theorem B28689511 : Blo 523799 28689511 := bstep (se 1 (by rfl) ⟨21517133, by rfl⟩ : syracuseStep 28689511 = 43034267) B43034267
theorem B1332713 : Blo 523799 1332713 := bstep (se 2 (by rfl) ⟨499767, by rfl⟩ : syracuseStep 1332713 = 999535) B999535
theorem B841423 : Blo 523799 841423 := bstep (se 1 (by rfl) ⟨631067, by rfl⟩ : syracuseStep 841423 = 1262135) B1262135
theorem B6940513 : Blo 523799 6940513 := bstep (se 2 (by rfl) ⟨2602692, by rfl⟩ : syracuseStep 6940513 = 5205385) B5205385
theorem B1178567 : Blo 523799 1178567 := bstep (se 1 (by rfl) ⟨883925, by rfl⟩ : syracuseStep 1178567 = 1767851) B1767851
theorem B785975 : Blo 523799 785975 := bstep (se 1 (by rfl) ⟨589481, by rfl⟩ : syracuseStep 785975 = 1178963) B1178963
theorem B523967 : Blo 523799 523967 := bstep (se 1 (by rfl) ⟨392975, by rfl⟩ : syracuseStep 523967 = 785951) B785951
theorem B885019 : Blo 523799 885019 := bstep (se 1 (by rfl) ⟨663764, by rfl⟩ : syracuseStep 885019 = 1327529) B1327529
theorem B5047231 : Blo 523799 5047231 := bstep (se 1 (by rfl) ⟨3785423, by rfl⟩ : syracuseStep 5047231 = 7570847) B7570847
theorem B526107 : Blo 523799 526107 := bstep (se 1 (by rfl) ⟨394580, by rfl⟩ : syracuseStep 526107 = 789161) B789161
theorem B888475 : Blo 523799 888475 := bstep (se 1 (by rfl) ⟨666356, by rfl⟩ : syracuseStep 888475 = 1332713) B1332713
theorem B790271 : Blo 523799 790271 := bstep (se 1 (by rfl) ⟨592703, by rfl⟩ : syracuseStep 790271 = 1185407) B1185407
theorem B1775357 : Blo 523799 1775357 := bstep (se 3 (by rfl) ⟨332879, by rfl⟩ : syracuseStep 1775357 = 665759) B665759
theorem B1121897 : Blo 523799 1121897 := bstep (se 2 (by rfl) ⟨420711, by rfl⟩ : syracuseStep 1121897 = 841423) B841423
theorem B38252681 : Blo 523799 38252681 := bstep (se 2 (by rfl) ⟨14344755, by rfl⟩ : syracuseStep 38252681 = 28689511) B28689511
theorem B9254017 : Blo 523799 9254017 := bstep (se 2 (by rfl) ⟨3470256, by rfl⟩ : syracuseStep 9254017 = 6940513) B6940513
theorem B2281031 : Blo 523799 2281031 := bstep (se 1 (by rfl) ⟨1710773, by rfl⟩ : syracuseStep 2281031 = 3421547) B3421547
theorem B1332895 : Blo 523799 1332895 := bstep (se 1 (by rfl) ⟨999671, by rfl⟩ : syracuseStep 1332895 = 1999343) B1999343
theorem B1769471 : Blo 523799 1769471 := bstep (se 1 (by rfl) ⟨1327103, by rfl⟩ : syracuseStep 1769471 = 2654207) B2654207
theorem B785711 : Blo 523799 785711 := bstep (se 1 (by rfl) ⟨589283, by rfl⟩ : syracuseStep 785711 = 1178567) B1178567
theorem B5701229 : Blo 523799 5701229 := bstep (se 3 (by rfl) ⟨1068980, by rfl⟩ : syracuseStep 5701229 = 2137961) B2137961
theorem B523983 : Blo 523799 523983 := bstep (se 1 (by rfl) ⟨392987, by rfl⟩ : syracuseStep 523983 = 785975) B785975
theorem B1180025 : Blo 523799 1180025 := bstep (se 2 (by rfl) ⟨442509, by rfl⟩ : syracuseStep 1180025 = 885019) B885019
theorem B526847 : Blo 523799 526847 := bstep (se 1 (by rfl) ⟨395135, by rfl⟩ : syracuseStep 526847 = 790271) B790271
theorem B1183571 : Blo 523799 1183571 := bstep (se 1 (by rfl) ⟨887678, by rfl⟩ : syracuseStep 1183571 = 1775357) B1775357
theorem B1179647 : Blo 523799 1179647 := bstep (se 1 (by rfl) ⟨884735, by rfl⟩ : syracuseStep 1179647 = 1769471) B1769471
theorem B1184633 : Blo 523799 1184633 := bstep (se 2 (by rfl) ⟨444237, by rfl⟩ : syracuseStep 1184633 = 888475) B888475
theorem B1777193 : Blo 523799 1777193 := bstep (se 2 (by rfl) ⟨666447, by rfl⟩ : syracuseStep 1777193 = 1332895) B1332895
theorem B25501787 : Blo 523799 25501787 := bstep (se 1 (by rfl) ⟨19126340, by rfl⟩ : syracuseStep 25501787 = 38252681) B38252681
theorem B2991725 : Blo 523799 2991725 := bstep (se 3 (by rfl) ⟨560948, by rfl⟩ : syracuseStep 2991725 = 1121897) B1121897
theorem B6729641 : Blo 523799 6729641 := bstep (se 2 (by rfl) ⟨2523615, by rfl⟩ : syracuseStep 6729641 = 5047231) B5047231
theorem B1520687 : Blo 523799 1520687 := bstep (se 1 (by rfl) ⟨1140515, by rfl⟩ : syracuseStep 1520687 = 2281031) B2281031
theorem B12338689 : Blo 523799 12338689 := bstep (se 2 (by rfl) ⟨4627008, by rfl⟩ : syracuseStep 12338689 = 9254017) B9254017
theorem B523807 : Blo 523799 523807 := bstep (se 1 (by rfl) ⟨392855, by rfl⟩ : syracuseStep 523807 = 785711) B785711
theorem B3800819 : Blo 523799 3800819 := bstep (se 1 (by rfl) ⟨2850614, by rfl⟩ : syracuseStep 3800819 = 5701229) B5701229
theorem B786683 : Blo 523799 786683 := bstep (se 1 (by rfl) ⟨590012, by rfl⟩ : syracuseStep 786683 = 1180025) B1180025
theorem B16451585 : Blo 523799 16451585 := bstep (se 2 (by rfl) ⟨6169344, by rfl⟩ : syracuseStep 16451585 = 12338689) B12338689
theorem B789047 : Blo 523799 789047 := bstep (se 1 (by rfl) ⟨591785, by rfl⟩ : syracuseStep 789047 = 1183571) B1183571
theorem B789755 : Blo 523799 789755 := bstep (se 1 (by rfl) ⟨592316, by rfl⟩ : syracuseStep 789755 = 1184633) B1184633
theorem B1184795 : Blo 523799 1184795 := bstep (se 1 (by rfl) ⟨888596, by rfl⟩ : syracuseStep 1184795 = 1777193) B1777193
theorem B2533879 : Blo 523799 2533879 := bstep (se 1 (by rfl) ⟨1900409, by rfl⟩ : syracuseStep 2533879 = 3800819) B3800819
theorem B786431 : Blo 523799 786431 := bstep (se 1 (by rfl) ⟨589823, by rfl⟩ : syracuseStep 786431 = 1179647) B1179647
theorem B17001191 : Blo 523799 17001191 := bstep (se 1 (by rfl) ⟨12750893, by rfl⟩ : syracuseStep 17001191 = 25501787) B25501787
theorem B1994483 : Blo 523799 1994483 := bstep (se 1 (by rfl) ⟨1495862, by rfl⟩ : syracuseStep 1994483 = 2991725) B2991725
theorem B4486427 : Blo 523799 4486427 := bstep (se 1 (by rfl) ⟨3364820, by rfl⟩ : syracuseStep 4486427 = 6729641) B6729641
theorem B1013791 : Blo 523799 1013791 := bstep (se 1 (by rfl) ⟨760343, by rfl⟩ : syracuseStep 1013791 = 1520687) B1520687
theorem B524455 : Blo 523799 524455 := bstep (se 1 (by rfl) ⟨393341, by rfl⟩ : syracuseStep 524455 = 786683) B786683
theorem B526031 : Blo 523799 526031 := bstep (se 1 (by rfl) ⟨394523, by rfl⟩ : syracuseStep 526031 = 789047) B789047
theorem B526503 : Blo 523799 526503 := bstep (se 1 (by rfl) ⟨394877, by rfl⟩ : syracuseStep 526503 = 789755) B789755
theorem B3378505 : Blo 523799 3378505 := bstep (se 2 (by rfl) ⟨1266939, by rfl⟩ : syracuseStep 3378505 = 2533879) B2533879
theorem B789863 : Blo 523799 789863 := bstep (se 1 (by rfl) ⟨592397, by rfl⟩ : syracuseStep 789863 = 1184795) B1184795
theorem B1351721 : Blo 523799 1351721 := bstep (se 2 (by rfl) ⟨506895, by rfl⟩ : syracuseStep 1351721 = 1013791) B1013791
theorem B2990951 : Blo 523799 2990951 := bstep (se 1 (by rfl) ⟨2243213, by rfl⟩ : syracuseStep 2990951 = 4486427) B4486427
theorem B1329655 : Blo 523799 1329655 := bstep (se 1 (by rfl) ⟨997241, by rfl⟩ : syracuseStep 1329655 = 1994483) B1994483
theorem B10967723 : Blo 523799 10967723 := bstep (se 1 (by rfl) ⟨8225792, by rfl⟩ : syracuseStep 10967723 = 16451585) B16451585
theorem B11334127 : Blo 523799 11334127 := bstep (se 1 (by rfl) ⟨8500595, by rfl⟩ : syracuseStep 11334127 = 17001191) B17001191
theorem B524287 : Blo 523799 524287 := bstep (se 1 (by rfl) ⟨393215, by rfl⟩ : syracuseStep 524287 = 786431) B786431
theorem B526575 : Blo 523799 526575 := bstep (se 1 (by rfl) ⟨394931, by rfl⟩ : syracuseStep 526575 = 789863) B789863
theorem B1772873 : Blo 523799 1772873 := bstep (se 2 (by rfl) ⟨664827, by rfl⟩ : syracuseStep 1772873 = 1329655) B1329655
theorem B7311815 : Blo 523799 7311815 := bstep (se 1 (by rfl) ⟨5483861, by rfl⟩ : syracuseStep 7311815 = 10967723) B10967723
theorem B15112169 : Blo 523799 15112169 := bstep (se 2 (by rfl) ⟨5667063, by rfl⟩ : syracuseStep 15112169 = 11334127) B11334127
theorem B4504673 : Blo 523799 4504673 := bstep (se 2 (by rfl) ⟨1689252, by rfl⟩ : syracuseStep 4504673 = 3378505) B3378505
theorem B901147 : Blo 523799 901147 := bstep (se 1 (by rfl) ⟨675860, by rfl⟩ : syracuseStep 901147 = 1351721) B1351721
theorem B1993967 : Blo 523799 1993967 := bstep (se 1 (by rfl) ⟨1495475, by rfl⟩ : syracuseStep 1993967 = 2990951) B2990951
theorem B1181915 : Blo 523799 1181915 := bstep (se 1 (by rfl) ⟨886436, by rfl⟩ : syracuseStep 1181915 = 1772873) B1772873
theorem B10074779 : Blo 523799 10074779 := bstep (se 1 (by rfl) ⟨7556084, by rfl⟩ : syracuseStep 10074779 = 15112169) B15112169
theorem B1329311 : Blo 523799 1329311 := bstep (se 1 (by rfl) ⟨996983, by rfl⟩ : syracuseStep 1329311 = 1993967) B1993967
theorem B3003115 : Blo 523799 3003115 := bstep (se 1 (by rfl) ⟨2252336, by rfl⟩ : syracuseStep 3003115 = 4504673) B4504673
theorem B1201529 : Blo 523799 1201529 := bstep (se 2 (by rfl) ⟨450573, by rfl⟩ : syracuseStep 1201529 = 901147) B901147
theorem B4874543 : Blo 523799 4874543 := bstep (se 1 (by rfl) ⟨3655907, by rfl⟩ : syracuseStep 4874543 = 7311815) B7311815
theorem B886207 : Blo 523799 886207 := bstep (se 1 (by rfl) ⟨664655, by rfl⟩ : syracuseStep 886207 = 1329311) B1329311
theorem B787943 : Blo 523799 787943 := bstep (se 1 (by rfl) ⟨590957, by rfl⟩ : syracuseStep 787943 = 1181915) B1181915
theorem B3249695 : Blo 523799 3249695 := bstep (se 1 (by rfl) ⟨2437271, by rfl⟩ : syracuseStep 3249695 = 4874543) B4874543
theorem B4004153 : Blo 523799 4004153 := bstep (se 2 (by rfl) ⟨1501557, by rfl⟩ : syracuseStep 4004153 = 3003115) B3003115
theorem B801019 : Blo 523799 801019 := bstep (se 1 (by rfl) ⟨600764, by rfl⟩ : syracuseStep 801019 = 1201529) B1201529
theorem B6716519 : Blo 523799 6716519 := bstep (se 1 (by rfl) ⟨5037389, by rfl⟩ : syracuseStep 6716519 = 10074779) B10074779
theorem B525295 : Blo 523799 525295 := bstep (se 1 (by rfl) ⟨393971, by rfl⟩ : syracuseStep 525295 = 787943) B787943
theorem B1181609 : Blo 523799 1181609 := bstep (se 2 (by rfl) ⟨443103, by rfl⟩ : syracuseStep 1181609 = 886207) B886207
theorem B2166463 : Blo 523799 2166463 := bstep (se 1 (by rfl) ⟨1624847, by rfl⟩ : syracuseStep 2166463 = 3249695) B3249695
theorem B4272101 : Blo 523799 4272101 := bstep (se 4 (by rfl) ⟨400509, by rfl⟩ : syracuseStep 4272101 = 801019) B801019
theorem B2669435 : Blo 523799 2669435 := bstep (se 1 (by rfl) ⟨2002076, by rfl⟩ : syracuseStep 2669435 = 4004153) B4004153
theorem B4477679 : Blo 523799 4477679 := bstep (se 1 (by rfl) ⟨3358259, by rfl⟩ : syracuseStep 4477679 = 6716519) B6716519
theorem B787739 : Blo 523799 787739 := bstep (se 1 (by rfl) ⟨590804, by rfl⟩ : syracuseStep 787739 = 1181609) B1181609
theorem B2985119 : Blo 523799 2985119 := bstep (se 1 (by rfl) ⟨2238839, by rfl⟩ : syracuseStep 2985119 = 4477679) B4477679
theorem B2888617 : Blo 523799 2888617 := bstep (se 2 (by rfl) ⟨1083231, by rfl⟩ : syracuseStep 2888617 = 2166463) B2166463
theorem B1779623 : Blo 523799 1779623 := bstep (se 1 (by rfl) ⟨1334717, by rfl⟩ : syracuseStep 1779623 = 2669435) B2669435
theorem B2848067 : Blo 523799 2848067 := bstep (se 1 (by rfl) ⟨2136050, by rfl⟩ : syracuseStep 2848067 = 4272101) B4272101
theorem B525159 : Blo 523799 525159 := bstep (se 1 (by rfl) ⟨393869, by rfl⟩ : syracuseStep 525159 = 787739) B787739
theorem B1186415 : Blo 523799 1186415 := bstep (se 1 (by rfl) ⟨889811, by rfl⟩ : syracuseStep 1186415 = 1779623) B1779623
theorem B3851489 : Blo 523799 3851489 := bstep (se 2 (by rfl) ⟨1444308, by rfl⟩ : syracuseStep 3851489 = 2888617) B2888617
theorem B1990079 : Blo 523799 1990079 := bstep (se 1 (by rfl) ⟨1492559, by rfl⟩ : syracuseStep 1990079 = 2985119) B2985119
theorem B1898711 : Blo 523799 1898711 := bstep (se 1 (by rfl) ⟨1424033, by rfl⟩ : syracuseStep 1898711 = 2848067) B2848067
theorem B790943 : Blo 523799 790943 := bstep (se 1 (by rfl) ⟨593207, by rfl⟩ : syracuseStep 790943 = 1186415) B1186415
theorem B2567659 : Blo 523799 2567659 := bstep (se 1 (by rfl) ⟨1925744, by rfl⟩ : syracuseStep 2567659 = 3851489) B3851489
theorem B1326719 : Blo 523799 1326719 := bstep (se 1 (by rfl) ⟨995039, by rfl⟩ : syracuseStep 1326719 = 1990079) B1990079
theorem B1265807 : Blo 523799 1265807 := bstep (se 1 (by rfl) ⟨949355, by rfl⟩ : syracuseStep 1265807 = 1898711) B1898711
theorem B527295 : Blo 523799 527295 := bstep (se 1 (by rfl) ⟨395471, by rfl⟩ : syracuseStep 527295 = 790943) B790943
theorem B3423545 : Blo 523799 3423545 := bstep (se 2 (by rfl) ⟨1283829, by rfl⟩ : syracuseStep 3423545 = 2567659) B2567659
theorem B843871 : Blo 523799 843871 := bstep (se 1 (by rfl) ⟨632903, by rfl⟩ : syracuseStep 843871 = 1265807) B1265807
theorem B884479 : Blo 523799 884479 := bstep (se 1 (by rfl) ⟨663359, by rfl⟩ : syracuseStep 884479 = 1326719) B1326719
theorem B1125161 : Blo 523799 1125161 := bstep (se 2 (by rfl) ⟨421935, by rfl⟩ : syracuseStep 1125161 = 843871) B843871
theorem B2282363 : Blo 523799 2282363 := bstep (se 1 (by rfl) ⟨1711772, by rfl⟩ : syracuseStep 2282363 = 3423545) B3423545
theorem B1179305 : Blo 523799 1179305 := bstep (se 2 (by rfl) ⟨442239, by rfl⟩ : syracuseStep 1179305 = 884479) B884479
theorem B1521575 : Blo 523799 1521575 := bstep (se 1 (by rfl) ⟨1141181, by rfl⟩ : syracuseStep 1521575 = 2282363) B2282363
theorem B750107 : Blo 523799 750107 := bstep (se 1 (by rfl) ⟨562580, by rfl⟩ : syracuseStep 750107 = 1125161) B1125161
theorem B786203 : Blo 523799 786203 := bstep (se 1 (by rfl) ⟨589652, by rfl⟩ : syracuseStep 786203 = 1179305) B1179305
theorem B2000285 : Blo 523799 2000285 := bstep (se 3 (by rfl) ⟨375053, by rfl⟩ : syracuseStep 2000285 = 750107) B750107
theorem B1014383 : Blo 523799 1014383 := bstep (se 1 (by rfl) ⟨760787, by rfl⟩ : syracuseStep 1014383 = 1521575) B1521575
theorem B524135 : Blo 523799 524135 := bstep (se 1 (by rfl) ⟨393101, by rfl⟩ : syracuseStep 524135 = 786203) B786203
theorem B676255 : Blo 523799 676255 := bstep (se 1 (by rfl) ⟨507191, by rfl⟩ : syracuseStep 676255 = 1014383) B1014383
theorem B1333523 : Blo 523799 1333523 := bstep (se 1 (by rfl) ⟨1000142, by rfl⟩ : syracuseStep 1333523 = 2000285) B2000285
theorem B889015 : Blo 523799 889015 := bstep (se 1 (by rfl) ⟨666761, by rfl⟩ : syracuseStep 889015 = 1333523) B1333523
theorem B901673 : Blo 523799 901673 := bstep (se 2 (by rfl) ⟨338127, by rfl⟩ : syracuseStep 901673 = 676255) B676255
theorem B1185353 : Blo 523799 1185353 := bstep (se 2 (by rfl) ⟨444507, by rfl⟩ : syracuseStep 1185353 = 889015) B889015
theorem B601115 : Blo 523799 601115 := bstep (se 1 (by rfl) ⟨450836, by rfl⟩ : syracuseStep 601115 = 901673) B901673
theorem B790235 : Blo 523799 790235 := bstep (se 1 (by rfl) ⟨592676, by rfl⟩ : syracuseStep 790235 = 1185353) B1185353
theorem B1602973 : Blo 523799 1602973 := bstep (se 3 (by rfl) ⟨300557, by rfl⟩ : syracuseStep 1602973 = 601115) B601115
theorem B526823 : Blo 523799 526823 := bstep (se 1 (by rfl) ⟨395117, by rfl⟩ : syracuseStep 526823 = 790235) B790235
theorem B8549189 : Blo 523799 8549189 := bstep (se 4 (by rfl) ⟨801486, by rfl⟩ : syracuseStep 8549189 = 1602973) B1602973
theorem B5699459 : Blo 523799 5699459 := bstep (se 1 (by rfl) ⟨4274594, by rfl⟩ : syracuseStep 5699459 = 8549189) B8549189
theorem B3799639 : Blo 523799 3799639 := bstep (se 1 (by rfl) ⟨2849729, by rfl⟩ : syracuseStep 3799639 = 5699459) B5699459
theorem B5066185 : Blo 523799 5066185 := bstep (se 2 (by rfl) ⟨1899819, by rfl⟩ : syracuseStep 5066185 = 3799639) B3799639
theorem B6754913 : Blo 523799 6754913 := bstep (se 2 (by rfl) ⟨2533092, by rfl⟩ : syracuseStep 6754913 = 5066185) B5066185
theorem B4503275 : Blo 523799 4503275 := bstep (se 1 (by rfl) ⟨3377456, by rfl⟩ : syracuseStep 4503275 = 6754913) B6754913
theorem B3002183 : Blo 523799 3002183 := bstep (se 1 (by rfl) ⟨2251637, by rfl⟩ : syracuseStep 3002183 = 4503275) B4503275
theorem B2001455 : Blo 523799 2001455 := bstep (se 1 (by rfl) ⟨1501091, by rfl⟩ : syracuseStep 2001455 = 3002183) B3002183
theorem B1334303 : Blo 523799 1334303 := bstep (se 1 (by rfl) ⟨1000727, by rfl⟩ : syracuseStep 1334303 = 2001455) B2001455
theorem B889535 : Blo 523799 889535 := bstep (se 1 (by rfl) ⟨667151, by rfl⟩ : syracuseStep 889535 = 1334303) B1334303
theorem B593023 : Blo 523799 593023 := bstep (se 1 (by rfl) ⟨444767, by rfl⟩ : syracuseStep 593023 = 889535) B889535
theorem B790697 : Blo 523799 790697 := bstep (se 2 (by rfl) ⟨296511, by rfl⟩ : syracuseStep 790697 = 593023) B593023
theorem B527131 : Blo 523799 527131 := bstep (se 1 (by rfl) ⟨395348, by rfl⟩ : syracuseStep 527131 = 790697) B790697

theorem C0 (j : ℕ) (h1 : 130949 ≤ j) (h2 : j ≤ 131648) : Blo 523799 (4 * j + 3) := by
  interval_cases j
  · exact B523799
  · exact B523803
  · exact B523807
  · exact B523811
  · exact B523815
  · exact B523819
  · exact B523823
  · exact B523827
  · exact B523831
  · exact B523835
  · exact B523839
  · exact B523843
  · exact B523847
  · exact B523851
  · exact B523855
  · exact B523859
  · exact B523863
  · exact B523867
  · exact B523871
  · exact B523875
  · exact B523879
  · exact B523883
  · exact B523887
  · exact B523891
  · exact B523895
  · exact B523899
  · exact B523903
  · exact B523907
  · exact B523911
  · exact B523915
  · exact B523919
  · exact B523923
  · exact B523927
  · exact B523931
  · exact B523935
  · exact B523939
  · exact B523943
  · exact B523947
  · exact B523951
  · exact B523955
  · exact B523959
  · exact B523963
  · exact B523967
  · exact B523971
  · exact B523975
  · exact B523979
  · exact B523983
  · exact B523987
  · exact B523991
  · exact B523995
  · exact B523999
  · exact B524003
  · exact B524007
  · exact B524011
  · exact B524015
  · exact B524019
  · exact B524023
  · exact B524027
  · exact B524031
  · exact B524035
  · exact B524039
  · exact B524043
  · exact B524047
  · exact B524051
  · exact B524055
  · exact B524059
  · exact B524063
  · exact B524067
  · exact B524071
  · exact B524075
  · exact B524079
  · exact B524083
  · exact B524087
  · exact B524091
  · exact B524095
  · exact B524099
  · exact B524103
  · exact B524107
  · exact B524111
  · exact B524115
  · exact B524119
  · exact B524123
  · exact B524127
  · exact B524131
  · exact B524135
  · exact B524139
  · exact B524143
  · exact B524147
  · exact B524151
  · exact B524155
  · exact B524159
  · exact B524163
  · exact B524167
  · exact B524171
  · exact B524175
  · exact B524179
  · exact B524183
  · exact B524187
  · exact B524191
  · exact B524195
  · exact B524199
  · exact B524203
  · exact B524207
  · exact B524211
  · exact B524215
  · exact B524219
  · exact B524223
  · exact B524227
  · exact B524231
  · exact B524235
  · exact B524239
  · exact B524243
  · exact B524247
  · exact B524251
  · exact B524255
  · exact B524259
  · exact B524263
  · exact B524267
  · exact B524271
  · exact B524275
  · exact B524279
  · exact B524283
  · exact B524287
  · exact B524291
  · exact B524295
  · exact B524299
  · exact B524303
  · exact B524307
  · exact B524311
  · exact B524315
  · exact B524319
  · exact B524323
  · exact B524327
  · exact B524331
  · exact B524335
  · exact B524339
  · exact B524343
  · exact B524347
  · exact B524351
  · exact B524355
  · exact B524359
  · exact B524363
  · exact B524367
  · exact B524371
  · exact B524375
  · exact B524379
  · exact B524383
  · exact B524387
  · exact B524391
  · exact B524395
  · exact B524399
  · exact B524403
  · exact B524407
  · exact B524411
  · exact B524415
  · exact B524419
  · exact B524423
  · exact B524427
  · exact B524431
  · exact B524435
  · exact B524439
  · exact B524443
  · exact B524447
  · exact B524451
  · exact B524455
  · exact B524459
  · exact B524463
  · exact B524467
  · exact B524471
  · exact B524475
  · exact B524479
  · exact B524483
  · exact B524487
  · exact B524491
  · exact B524495
  · exact B524499
  · exact B524503
  · exact B524507
  · exact B524511
  · exact B524515
  · exact B524519
  · exact B524523
  · exact B524527
  · exact B524531
  · exact B524535
  · exact B524539
  · exact B524543
  · exact B524547
  · exact B524551
  · exact B524555
  · exact B524559
  · exact B524563
  · exact B524567
  · exact B524571
  · exact B524575
  · exact B524579
  · exact B524583
  · exact B524587
  · exact B524591
  · exact B524595
  · exact B524599
  · exact B524603
  · exact B524607
  · exact B524611
  · exact B524615
  · exact B524619
  · exact B524623
  · exact B524627
  · exact B524631
  · exact B524635
  · exact B524639
  · exact B524643
  · exact B524647
  · exact B524651
  · exact B524655
  · exact B524659
  · exact B524663
  · exact B524667
  · exact B524671
  · exact B524675
  · exact B524679
  · exact B524683
  · exact B524687
  · exact B524691
  · exact B524695
  · exact B524699
  · exact B524703
  · exact B524707
  · exact B524711
  · exact B524715
  · exact B524719
  · exact B524723
  · exact B524727
  · exact B524731
  · exact B524735
  · exact B524739
  · exact B524743
  · exact B524747
  · exact B524751
  · exact B524755
  · exact B524759
  · exact B524763
  · exact B524767
  · exact B524771
  · exact B524775
  · exact B524779
  · exact B524783
  · exact B524787
  · exact B524791
  · exact B524795
  · exact B524799
  · exact B524803
  · exact B524807
  · exact B524811
  · exact B524815
  · exact B524819
  · exact B524823
  · exact B524827
  · exact B524831
  · exact B524835
  · exact B524839
  · exact B524843
  · exact B524847
  · exact B524851
  · exact B524855
  · exact B524859
  · exact B524863
  · exact B524867
  · exact B524871
  · exact B524875
  · exact B524879
  · exact B524883
  · exact B524887
  · exact B524891
  · exact B524895
  · exact B524899
  · exact B524903
  · exact B524907
  · exact B524911
  · exact B524915
  · exact B524919
  · exact B524923
  · exact B524927
  · exact B524931
  · exact B524935
  · exact B524939
  · exact B524943
  · exact B524947
  · exact B524951
  · exact B524955
  · exact B524959
  · exact B524963
  · exact B524967
  · exact B524971
  · exact B524975
  · exact B524979
  · exact B524983
  · exact B524987
  · exact B524991
  · exact B524995
  · exact B524999
  · exact B525003
  · exact B525007
  · exact B525011
  · exact B525015
  · exact B525019
  · exact B525023
  · exact B525027
  · exact B525031
  · exact B525035
  · exact B525039
  · exact B525043
  · exact B525047
  · exact B525051
  · exact B525055
  · exact B525059
  · exact B525063
  · exact B525067
  · exact B525071
  · exact B525075
  · exact B525079
  · exact B525083
  · exact B525087
  · exact B525091
  · exact B525095
  · exact B525099
  · exact B525103
  · exact B525107
  · exact B525111
  · exact B525115
  · exact B525119
  · exact B525123
  · exact B525127
  · exact B525131
  · exact B525135
  · exact B525139
  · exact B525143
  · exact B525147
  · exact B525151
  · exact B525155
  · exact B525159
  · exact B525163
  · exact B525167
  · exact B525171
  · exact B525175
  · exact B525179
  · exact B525183
  · exact B525187
  · exact B525191
  · exact B525195
  · exact B525199
  · exact B525203
  · exact B525207
  · exact B525211
  · exact B525215
  · exact B525219
  · exact B525223
  · exact B525227
  · exact B525231
  · exact B525235
  · exact B525239
  · exact B525243
  · exact B525247
  · exact B525251
  · exact B525255
  · exact B525259
  · exact B525263
  · exact B525267
  · exact B525271
  · exact B525275
  · exact B525279
  · exact B525283
  · exact B525287
  · exact B525291
  · exact B525295
  · exact B525299
  · exact B525303
  · exact B525307
  · exact B525311
  · exact B525315
  · exact B525319
  · exact B525323
  · exact B525327
  · exact B525331
  · exact B525335
  · exact B525339
  · exact B525343
  · exact B525347
  · exact B525351
  · exact B525355
  · exact B525359
  · exact B525363
  · exact B525367
  · exact B525371
  · exact B525375
  · exact B525379
  · exact B525383
  · exact B525387
  · exact B525391
  · exact B525395
  · exact B525399
  · exact B525403
  · exact B525407
  · exact B525411
  · exact B525415
  · exact B525419
  · exact B525423
  · exact B525427
  · exact B525431
  · exact B525435
  · exact B525439
  · exact B525443
  · exact B525447
  · exact B525451
  · exact B525455
  · exact B525459
  · exact B525463
  · exact B525467
  · exact B525471
  · exact B525475
  · exact B525479
  · exact B525483
  · exact B525487
  · exact B525491
  · exact B525495
  · exact B525499
  · exact B525503
  · exact B525507
  · exact B525511
  · exact B525515
  · exact B525519
  · exact B525523
  · exact B525527
  · exact B525531
  · exact B525535
  · exact B525539
  · exact B525543
  · exact B525547
  · exact B525551
  · exact B525555
  · exact B525559
  · exact B525563
  · exact B525567
  · exact B525571
  · exact B525575
  · exact B525579
  · exact B525583
  · exact B525587
  · exact B525591
  · exact B525595
  · exact B525599
  · exact B525603
  · exact B525607
  · exact B525611
  · exact B525615
  · exact B525619
  · exact B525623
  · exact B525627
  · exact B525631
  · exact B525635
  · exact B525639
  · exact B525643
  · exact B525647
  · exact B525651
  · exact B525655
  · exact B525659
  · exact B525663
  · exact B525667
  · exact B525671
  · exact B525675
  · exact B525679
  · exact B525683
  · exact B525687
  · exact B525691
  · exact B525695
  · exact B525699
  · exact B525703
  · exact B525707
  · exact B525711
  · exact B525715
  · exact B525719
  · exact B525723
  · exact B525727
  · exact B525731
  · exact B525735
  · exact B525739
  · exact B525743
  · exact B525747
  · exact B525751
  · exact B525755
  · exact B525759
  · exact B525763
  · exact B525767
  · exact B525771
  · exact B525775
  · exact B525779
  · exact B525783
  · exact B525787
  · exact B525791
  · exact B525795
  · exact B525799
  · exact B525803
  · exact B525807
  · exact B525811
  · exact B525815
  · exact B525819
  · exact B525823
  · exact B525827
  · exact B525831
  · exact B525835
  · exact B525839
  · exact B525843
  · exact B525847
  · exact B525851
  · exact B525855
  · exact B525859
  · exact B525863
  · exact B525867
  · exact B525871
  · exact B525875
  · exact B525879
  · exact B525883
  · exact B525887
  · exact B525891
  · exact B525895
  · exact B525899
  · exact B525903
  · exact B525907
  · exact B525911
  · exact B525915
  · exact B525919
  · exact B525923
  · exact B525927
  · exact B525931
  · exact B525935
  · exact B525939
  · exact B525943
  · exact B525947
  · exact B525951
  · exact B525955
  · exact B525959
  · exact B525963
  · exact B525967
  · exact B525971
  · exact B525975
  · exact B525979
  · exact B525983
  · exact B525987
  · exact B525991
  · exact B525995
  · exact B525999
  · exact B526003
  · exact B526007
  · exact B526011
  · exact B526015
  · exact B526019
  · exact B526023
  · exact B526027
  · exact B526031
  · exact B526035
  · exact B526039
  · exact B526043
  · exact B526047
  · exact B526051
  · exact B526055
  · exact B526059
  · exact B526063
  · exact B526067
  · exact B526071
  · exact B526075
  · exact B526079
  · exact B526083
  · exact B526087
  · exact B526091
  · exact B526095
  · exact B526099
  · exact B526103
  · exact B526107
  · exact B526111
  · exact B526115
  · exact B526119
  · exact B526123
  · exact B526127
  · exact B526131
  · exact B526135
  · exact B526139
  · exact B526143
  · exact B526147
  · exact B526151
  · exact B526155
  · exact B526159
  · exact B526163
  · exact B526167
  · exact B526171
  · exact B526175
  · exact B526179
  · exact B526183
  · exact B526187
  · exact B526191
  · exact B526195
  · exact B526199
  · exact B526203
  · exact B526207
  · exact B526211
  · exact B526215
  · exact B526219
  · exact B526223
  · exact B526227
  · exact B526231
  · exact B526235
  · exact B526239
  · exact B526243
  · exact B526247
  · exact B526251
  · exact B526255
  · exact B526259
  · exact B526263
  · exact B526267
  · exact B526271
  · exact B526275
  · exact B526279
  · exact B526283
  · exact B526287
  · exact B526291
  · exact B526295
  · exact B526299
  · exact B526303
  · exact B526307
  · exact B526311
  · exact B526315
  · exact B526319
  · exact B526323
  · exact B526327
  · exact B526331
  · exact B526335
  · exact B526339
  · exact B526343
  · exact B526347
  · exact B526351
  · exact B526355
  · exact B526359
  · exact B526363
  · exact B526367
  · exact B526371
  · exact B526375
  · exact B526379
  · exact B526383
  · exact B526387
  · exact B526391
  · exact B526395
  · exact B526399
  · exact B526403
  · exact B526407
  · exact B526411
  · exact B526415
  · exact B526419
  · exact B526423
  · exact B526427
  · exact B526431
  · exact B526435
  · exact B526439
  · exact B526443
  · exact B526447
  · exact B526451
  · exact B526455
  · exact B526459
  · exact B526463
  · exact B526467
  · exact B526471
  · exact B526475
  · exact B526479
  · exact B526483
  · exact B526487
  · exact B526491
  · exact B526495
  · exact B526499
  · exact B526503
  · exact B526507
  · exact B526511
  · exact B526515
  · exact B526519
  · exact B526523
  · exact B526527
  · exact B526531
  · exact B526535
  · exact B526539
  · exact B526543
  · exact B526547
  · exact B526551
  · exact B526555
  · exact B526559
  · exact B526563
  · exact B526567
  · exact B526571
  · exact B526575
  · exact B526579
  · exact B526583
  · exact B526587
  · exact B526591
  · exact B526595

theorem C1 (j : ℕ) (h1 : 131649 ≤ j) (h2 : j ≤ 131949) : Blo 523799 (4 * j + 3) := by
  interval_cases j
  · exact B526599
  · exact B526603
  · exact B526607
  · exact B526611
  · exact B526615
  · exact B526619
  · exact B526623
  · exact B526627
  · exact B526631
  · exact B526635
  · exact B526639
  · exact B526643
  · exact B526647
  · exact B526651
  · exact B526655
  · exact B526659
  · exact B526663
  · exact B526667
  · exact B526671
  · exact B526675
  · exact B526679
  · exact B526683
  · exact B526687
  · exact B526691
  · exact B526695
  · exact B526699
  · exact B526703
  · exact B526707
  · exact B526711
  · exact B526715
  · exact B526719
  · exact B526723
  · exact B526727
  · exact B526731
  · exact B526735
  · exact B526739
  · exact B526743
  · exact B526747
  · exact B526751
  · exact B526755
  · exact B526759
  · exact B526763
  · exact B526767
  · exact B526771
  · exact B526775
  · exact B526779
  · exact B526783
  · exact B526787
  · exact B526791
  · exact B526795
  · exact B526799
  · exact B526803
  · exact B526807
  · exact B526811
  · exact B526815
  · exact B526819
  · exact B526823
  · exact B526827
  · exact B526831
  · exact B526835
  · exact B526839
  · exact B526843
  · exact B526847
  · exact B526851
  · exact B526855
  · exact B526859
  · exact B526863
  · exact B526867
  · exact B526871
  · exact B526875
  · exact B526879
  · exact B526883
  · exact B526887
  · exact B526891
  · exact B526895
  · exact B526899
  · exact B526903
  · exact B526907
  · exact B526911
  · exact B526915
  · exact B526919
  · exact B526923
  · exact B526927
  · exact B526931
  · exact B526935
  · exact B526939
  · exact B526943
  · exact B526947
  · exact B526951
  · exact B526955
  · exact B526959
  · exact B526963
  · exact B526967
  · exact B526971
  · exact B526975
  · exact B526979
  · exact B526983
  · exact B526987
  · exact B526991
  · exact B526995
  · exact B526999
  · exact B527003
  · exact B527007
  · exact B527011
  · exact B527015
  · exact B527019
  · exact B527023
  · exact B527027
  · exact B527031
  · exact B527035
  · exact B527039
  · exact B527043
  · exact B527047
  · exact B527051
  · exact B527055
  · exact B527059
  · exact B527063
  · exact B527067
  · exact B527071
  · exact B527075
  · exact B527079
  · exact B527083
  · exact B527087
  · exact B527091
  · exact B527095
  · exact B527099
  · exact B527103
  · exact B527107
  · exact B527111
  · exact B527115
  · exact B527119
  · exact B527123
  · exact B527127
  · exact B527131
  · exact B527135
  · exact B527139
  · exact B527143
  · exact B527147
  · exact B527151
  · exact B527155
  · exact B527159
  · exact B527163
  · exact B527167
  · exact B527171
  · exact B527175
  · exact B527179
  · exact B527183
  · exact B527187
  · exact B527191
  · exact B527195
  · exact B527199
  · exact B527203
  · exact B527207
  · exact B527211
  · exact B527215
  · exact B527219
  · exact B527223
  · exact B527227
  · exact B527231
  · exact B527235
  · exact B527239
  · exact B527243
  · exact B527247
  · exact B527251
  · exact B527255
  · exact B527259
  · exact B527263
  · exact B527267
  · exact B527271
  · exact B527275
  · exact B527279
  · exact B527283
  · exact B527287
  · exact B527291
  · exact B527295
  · exact B527299
  · exact B527303
  · exact B527307
  · exact B527311
  · exact B527315
  · exact B527319
  · exact B527323
  · exact B527327
  · exact B527331
  · exact B527335
  · exact B527339
  · exact B527343
  · exact B527347
  · exact B527351
  · exact B527355
  · exact B527359
  · exact B527363
  · exact B527367
  · exact B527371
  · exact B527375
  · exact B527379
  · exact B527383
  · exact B527387
  · exact B527391
  · exact B527395
  · exact B527399
  · exact B527403
  · exact B527407
  · exact B527411
  · exact B527415
  · exact B527419
  · exact B527423
  · exact B527427
  · exact B527431
  · exact B527435
  · exact B527439
  · exact B527443
  · exact B527447
  · exact B527451
  · exact B527455
  · exact B527459
  · exact B527463
  · exact B527467
  · exact B527471
  · exact B527475
  · exact B527479
  · exact B527483
  · exact B527487
  · exact B527491
  · exact B527495
  · exact B527499
  · exact B527503
  · exact B527507
  · exact B527511
  · exact B527515
  · exact B527519
  · exact B527523
  · exact B527527
  · exact B527531
  · exact B527535
  · exact B527539
  · exact B527543
  · exact B527547
  · exact B527551
  · exact B527555
  · exact B527559
  · exact B527563
  · exact B527567
  · exact B527571
  · exact B527575
  · exact B527579
  · exact B527583
  · exact B527587
  · exact B527591
  · exact B527595
  · exact B527599
  · exact B527603
  · exact B527607
  · exact B527611
  · exact B527615
  · exact B527619
  · exact B527623
  · exact B527627
  · exact B527631
  · exact B527635
  · exact B527639
  · exact B527643
  · exact B527647
  · exact B527651
  · exact B527655
  · exact B527659
  · exact B527663
  · exact B527667
  · exact B527671
  · exact B527675
  · exact B527679
  · exact B527683
  · exact B527687
  · exact B527691
  · exact B527695
  · exact B527699
  · exact B527703
  · exact B527707
  · exact B527711
  · exact B527715
  · exact B527719
  · exact B527723
  · exact B527727
  · exact B527731
  · exact B527735
  · exact B527739
  · exact B527743
  · exact B527747
  · exact B527751
  · exact B527755
  · exact B527759
  · exact B527763
  · exact B527767
  · exact B527771
  · exact B527775
  · exact B527779
  · exact B527783
  · exact B527787
  · exact B527791
  · exact B527795
  · exact B527799

theorem solution (m : ℕ) (hlo : 523799 ≤ m) (hhi : m ≤ 527799) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 130949 ≤ j := by omega
    have hj2 : j ≤ 131949 := by omega
    have hb : Blo 523799 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 131649 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
