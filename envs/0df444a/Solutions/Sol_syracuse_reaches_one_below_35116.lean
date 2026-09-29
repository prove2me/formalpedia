-- Prove2me | solution 1 for syracuse_reaches_one_below_35116
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T05:28:47.165475+00:00
-- url     : https://prove2.me/submissions/9082a5fd-e8fa-4102-870a-96f25865c37d

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_reaches_one_below_31115

set_option maxHeartbeats 1000000

open Nat

abbrev Reach (n : ℕ) : Prop := ∃ j : ℕ, syracuseStep^[j] n = 1

theorem se (a : ℕ) {y z : ℕ} (h : 3 * y + 1 = 2 ^ a * z) (hz : Odd z) :
    syracuseStep y = z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hz
  have hfac : (3 * y + 1).factorization 2 = a := by
    rw [h, Nat.factorization_mul (by positivity) hz0]
    simp [Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff])]
  show ordCompl[2] (3 * y + 1) = z
  rw [hfac, h, Nat.mul_div_cancel_left _ (by positivity)]

theorem rs {x y : ℕ} (h : syracuseStep x = y) (hy : Reach y) : Reach x := by
  obtain ⟨j, hj⟩ := hy
  exact ⟨j + 1, by rw [Function.iterate_add_apply, Function.iterate_one, h]; exact hj⟩

/-- Everything below the previously verified bound is already known to reach 1. -/
theorem B (n : ℕ) (h1 : 0 < n) (h2 : Odd n) (h3 : n ≤ 31114) : Reach n :=
  syracuse_reaches_one_below_31115 n h1 h2 h3
theorem R32769 : Reach 32769 := rs (se 2 (by rfl) ⟨12288, by rfl⟩) (B 24577 (by norm_num) ⟨12288, by rfl⟩ (by norm_num))
theorem R32773 : Reach 32773 := rs (se 4 (by rfl) ⟨3072, by rfl⟩) (B 6145 (by norm_num) ⟨3072, by rfl⟩ (by norm_num))
theorem R32777 : Reach 32777 := rs (se 2 (by rfl) ⟨12291, by rfl⟩) (B 24583 (by norm_num) ⟨12291, by rfl⟩ (by norm_num))
theorem R32781 : Reach 32781 := rs (se 3 (by rfl) ⟨6146, by rfl⟩) (B 12293 (by norm_num) ⟨6146, by rfl⟩ (by norm_num))
theorem R65549 : Reach 65549 := rs (se 3 (by rfl) ⟨12290, by rfl⟩) (B 24581 (by norm_num) ⟨12290, by rfl⟩ (by norm_num))
theorem R32785 : Reach 32785 := rs (se 2 (by rfl) ⟨12294, by rfl⟩) (B 24589 (by norm_num) ⟨12294, by rfl⟩ (by norm_num))
theorem R32789 : Reach 32789 := rs (se 6 (by rfl) ⟨768, by rfl⟩) (B 1537 (by norm_num) ⟨768, by rfl⟩ (by norm_num))
theorem R32793 : Reach 32793 := rs (se 2 (by rfl) ⟨12297, by rfl⟩) (B 24595 (by norm_num) ⟨12297, by rfl⟩ (by norm_num))
theorem R32797 : Reach 32797 := rs (se 3 (by rfl) ⟨6149, by rfl⟩) (B 12299 (by norm_num) ⟨6149, by rfl⟩ (by norm_num))
theorem R32801 : Reach 32801 := rs (se 2 (by rfl) ⟨12300, by rfl⟩) (B 24601 (by norm_num) ⟨12300, by rfl⟩ (by norm_num))
theorem R32805 : Reach 32805 := rs (se 4 (by rfl) ⟨3075, by rfl⟩) (B 6151 (by norm_num) ⟨3075, by rfl⟩ (by norm_num))
theorem R32809 : Reach 32809 := rs (se 2 (by rfl) ⟨12303, by rfl⟩) (B 24607 (by norm_num) ⟨12303, by rfl⟩ (by norm_num))
theorem R32813 : Reach 32813 := rs (se 3 (by rfl) ⟨6152, by rfl⟩) (B 12305 (by norm_num) ⟨6152, by rfl⟩ (by norm_num))
theorem R32817 : Reach 32817 := rs (se 2 (by rfl) ⟨12306, by rfl⟩) (B 24613 (by norm_num) ⟨12306, by rfl⟩ (by norm_num))
theorem R32821 : Reach 32821 := rs (se 5 (by rfl) ⟨1538, by rfl⟩) (B 3077 (by norm_num) ⟨1538, by rfl⟩ (by norm_num))
theorem R32825 : Reach 32825 := rs (se 2 (by rfl) ⟨12309, by rfl⟩) (B 24619 (by norm_num) ⟨12309, by rfl⟩ (by norm_num))
theorem R32829 : Reach 32829 := rs (se 3 (by rfl) ⟨6155, by rfl⟩) (B 12311 (by norm_num) ⟨6155, by rfl⟩ (by norm_num))
theorem R32833 : Reach 32833 := rs (se 2 (by rfl) ⟨12312, by rfl⟩) (B 24625 (by norm_num) ⟨12312, by rfl⟩ (by norm_num))
theorem R65605 : Reach 65605 := rs (se 4 (by rfl) ⟨6150, by rfl⟩) (B 12301 (by norm_num) ⟨6150, by rfl⟩ (by norm_num))
theorem R32837 : Reach 32837 := rs (se 4 (by rfl) ⟨3078, by rfl⟩) (B 6157 (by norm_num) ⟨3078, by rfl⟩ (by norm_num))
theorem R32841 : Reach 32841 := rs (se 2 (by rfl) ⟨12315, by rfl⟩) (B 24631 (by norm_num) ⟨12315, by rfl⟩ (by norm_num))
theorem R32845 : Reach 32845 := rs (se 3 (by rfl) ⟨6158, by rfl⟩) (B 12317 (by norm_num) ⟨6158, by rfl⟩ (by norm_num))
theorem R32849 : Reach 32849 := rs (se 2 (by rfl) ⟨12318, by rfl⟩) (B 24637 (by norm_num) ⟨12318, by rfl⟩ (by norm_num))
theorem R32853 : Reach 32853 := rs (se 8 (by rfl) ⟨192, by rfl⟩) (B 385 (by norm_num) ⟨192, by rfl⟩ (by norm_num))
theorem R32857 : Reach 32857 := rs (se 2 (by rfl) ⟨12321, by rfl⟩) (B 24643 (by norm_num) ⟨12321, by rfl⟩ (by norm_num))
theorem R32861 : Reach 32861 := rs (se 3 (by rfl) ⟨6161, by rfl⟩) (B 12323 (by norm_num) ⟨6161, by rfl⟩ (by norm_num))
theorem R32865 : Reach 32865 := rs (se 2 (by rfl) ⟨12324, by rfl⟩) (B 24649 (by norm_num) ⟨12324, by rfl⟩ (by norm_num))
theorem R32869 : Reach 32869 := rs (se 4 (by rfl) ⟨3081, by rfl⟩) (B 6163 (by norm_num) ⟨3081, by rfl⟩ (by norm_num))
theorem R98405 : Reach 98405 := rs (se 4 (by rfl) ⟨9225, by rfl⟩) (B 18451 (by norm_num) ⟨9225, by rfl⟩ (by norm_num))
theorem R32873 : Reach 32873 := rs (se 2 (by rfl) ⟨12327, by rfl⟩) (B 24655 (by norm_num) ⟨12327, by rfl⟩ (by norm_num))
theorem R32877 : Reach 32877 := rs (se 3 (by rfl) ⟨6164, by rfl⟩) (B 12329 (by norm_num) ⟨6164, by rfl⟩ (by norm_num))
theorem R32881 : Reach 32881 := rs (se 2 (by rfl) ⟨12330, by rfl⟩) (B 24661 (by norm_num) ⟨12330, by rfl⟩ (by norm_num))
theorem R32885 : Reach 32885 := rs (se 5 (by rfl) ⟨1541, by rfl⟩) (B 3083 (by norm_num) ⟨1541, by rfl⟩ (by norm_num))
theorem R32889 : Reach 32889 := rs (se 2 (by rfl) ⟨12333, by rfl⟩) (B 24667 (by norm_num) ⟨12333, by rfl⟩ (by norm_num))
theorem R32893 : Reach 32893 := rs (se 3 (by rfl) ⟨6167, by rfl⟩) (B 12335 (by norm_num) ⟨6167, by rfl⟩ (by norm_num))
theorem R32897 : Reach 32897 := rs (se 2 (by rfl) ⟨12336, by rfl⟩) (B 24673 (by norm_num) ⟨12336, by rfl⟩ (by norm_num))
theorem R32901 : Reach 32901 := rs (se 4 (by rfl) ⟨3084, by rfl⟩) (B 6169 (by norm_num) ⟨3084, by rfl⟩ (by norm_num))
theorem R32905 : Reach 32905 := rs (se 2 (by rfl) ⟨12339, by rfl⟩) (B 24679 (by norm_num) ⟨12339, by rfl⟩ (by norm_num))
theorem R32909 : Reach 32909 := rs (se 3 (by rfl) ⟨6170, by rfl⟩) (B 12341 (by norm_num) ⟨6170, by rfl⟩ (by norm_num))
theorem R32913 : Reach 32913 := rs (se 2 (by rfl) ⟨12342, by rfl⟩) (B 24685 (by norm_num) ⟨12342, by rfl⟩ (by norm_num))
theorem R32917 : Reach 32917 := rs (se 6 (by rfl) ⟨771, by rfl⟩) (B 1543 (by norm_num) ⟨771, by rfl⟩ (by norm_num))
theorem R32921 : Reach 32921 := rs (se 2 (by rfl) ⟨12345, by rfl⟩) (B 24691 (by norm_num) ⟨12345, by rfl⟩ (by norm_num))
theorem R32925 : Reach 32925 := rs (se 3 (by rfl) ⟨6173, by rfl⟩) (B 12347 (by norm_num) ⟨6173, by rfl⟩ (by norm_num))
theorem R32929 : Reach 32929 := rs (se 2 (by rfl) ⟨12348, by rfl⟩) (B 24697 (by norm_num) ⟨12348, by rfl⟩ (by norm_num))
theorem R32933 : Reach 32933 := rs (se 4 (by rfl) ⟨3087, by rfl⟩) (B 6175 (by norm_num) ⟨3087, by rfl⟩ (by norm_num))
theorem R65701 : Reach 65701 := rs (se 4 (by rfl) ⟨6159, by rfl⟩) (B 12319 (by norm_num) ⟨6159, by rfl⟩ (by norm_num))
theorem R32937 : Reach 32937 := rs (se 2 (by rfl) ⟨12351, by rfl⟩) (B 24703 (by norm_num) ⟨12351, by rfl⟩ (by norm_num))
theorem R32941 : Reach 32941 := rs (se 3 (by rfl) ⟨6176, by rfl⟩) (B 12353 (by norm_num) ⟨6176, by rfl⟩ (by norm_num))
theorem R32945 : Reach 32945 := rs (se 2 (by rfl) ⟨12354, by rfl⟩) (B 24709 (by norm_num) ⟨12354, by rfl⟩ (by norm_num))
theorem R32949 : Reach 32949 := rs (se 5 (by rfl) ⟨1544, by rfl⟩) (B 3089 (by norm_num) ⟨1544, by rfl⟩ (by norm_num))
theorem R32953 : Reach 32953 := rs (se 2 (by rfl) ⟨12357, by rfl⟩) (B 24715 (by norm_num) ⟨12357, by rfl⟩ (by norm_num))
theorem R32957 : Reach 32957 := rs (se 3 (by rfl) ⟨6179, by rfl⟩) (B 12359 (by norm_num) ⟨6179, by rfl⟩ (by norm_num))
theorem R32961 : Reach 32961 := rs (se 2 (by rfl) ⟨12360, by rfl⟩) (B 24721 (by norm_num) ⟨12360, by rfl⟩ (by norm_num))
theorem R32965 : Reach 32965 := rs (se 4 (by rfl) ⟨3090, by rfl⟩) (B 6181 (by norm_num) ⟨3090, by rfl⟩ (by norm_num))
theorem R32969 : Reach 32969 := rs (se 2 (by rfl) ⟨12363, by rfl⟩) (B 24727 (by norm_num) ⟨12363, by rfl⟩ (by norm_num))
theorem R32973 : Reach 32973 := rs (se 3 (by rfl) ⟨6182, by rfl⟩) (B 12365 (by norm_num) ⟨6182, by rfl⟩ (by norm_num))
theorem R32977 : Reach 32977 := rs (se 2 (by rfl) ⟨12366, by rfl⟩) (B 24733 (by norm_num) ⟨12366, by rfl⟩ (by norm_num))
theorem R32981 : Reach 32981 := rs (se 7 (by rfl) ⟨386, by rfl⟩) (B 773 (by norm_num) ⟨386, by rfl⟩ (by norm_num))
theorem R32985 : Reach 32985 := rs (se 2 (by rfl) ⟨12369, by rfl⟩) (B 24739 (by norm_num) ⟨12369, by rfl⟩ (by norm_num))
theorem R32989 : Reach 32989 := rs (se 3 (by rfl) ⟨6185, by rfl⟩) (B 12371 (by norm_num) ⟨6185, by rfl⟩ (by norm_num))
theorem R32993 : Reach 32993 := rs (se 2 (by rfl) ⟨12372, by rfl⟩) (B 24745 (by norm_num) ⟨12372, by rfl⟩ (by norm_num))
theorem R32997 : Reach 32997 := rs (se 4 (by rfl) ⟨3093, by rfl⟩) (B 6187 (by norm_num) ⟨3093, by rfl⟩ (by norm_num))
theorem R33001 : Reach 33001 := rs (se 2 (by rfl) ⟨12375, by rfl⟩) (B 24751 (by norm_num) ⟨12375, by rfl⟩ (by norm_num))
theorem R33005 : Reach 33005 := rs (se 3 (by rfl) ⟨6188, by rfl⟩) (B 12377 (by norm_num) ⟨6188, by rfl⟩ (by norm_num))
theorem R33009 : Reach 33009 := rs (se 2 (by rfl) ⟨12378, by rfl⟩) (B 24757 (by norm_num) ⟨12378, by rfl⟩ (by norm_num))
theorem R33013 : Reach 33013 := rs (se 5 (by rfl) ⟨1547, by rfl⟩) (B 3095 (by norm_num) ⟨1547, by rfl⟩ (by norm_num))
theorem R33017 : Reach 33017 := rs (se 2 (by rfl) ⟨12381, by rfl⟩) (B 24763 (by norm_num) ⟨12381, by rfl⟩ (by norm_num))
theorem R33021 : Reach 33021 := rs (se 3 (by rfl) ⟨6191, by rfl⟩) (B 12383 (by norm_num) ⟨6191, by rfl⟩ (by norm_num))
theorem R33025 : Reach 33025 := rs (se 2 (by rfl) ⟨12384, by rfl⟩) (B 24769 (by norm_num) ⟨12384, by rfl⟩ (by norm_num))
theorem R33029 : Reach 33029 := rs (se 4 (by rfl) ⟨3096, by rfl⟩) (B 6193 (by norm_num) ⟨3096, by rfl⟩ (by norm_num))
theorem R33033 : Reach 33033 := rs (se 2 (by rfl) ⟨12387, by rfl⟩) (B 24775 (by norm_num) ⟨12387, by rfl⟩ (by norm_num))
theorem R33037 : Reach 33037 := rs (se 3 (by rfl) ⟨6194, by rfl⟩) (B 12389 (by norm_num) ⟨6194, by rfl⟩ (by norm_num))
theorem R33041 : Reach 33041 := rs (se 2 (by rfl) ⟨12390, by rfl⟩) (B 24781 (by norm_num) ⟨12390, by rfl⟩ (by norm_num))
theorem R33045 : Reach 33045 := rs (se 6 (by rfl) ⟨774, by rfl⟩) (B 1549 (by norm_num) ⟨774, by rfl⟩ (by norm_num))
theorem R33049 : Reach 33049 := rs (se 2 (by rfl) ⟨12393, by rfl⟩) (B 24787 (by norm_num) ⟨12393, by rfl⟩ (by norm_num))
theorem R33053 : Reach 33053 := rs (se 3 (by rfl) ⟨6197, by rfl⟩) (B 12395 (by norm_num) ⟨6197, by rfl⟩ (by norm_num))
theorem R33057 : Reach 33057 := rs (se 2 (by rfl) ⟨12396, by rfl⟩) (B 24793 (by norm_num) ⟨12396, by rfl⟩ (by norm_num))
theorem R33061 : Reach 33061 := rs (se 4 (by rfl) ⟨3099, by rfl⟩) (B 6199 (by norm_num) ⟨3099, by rfl⟩ (by norm_num))
theorem R98597 : Reach 98597 := rs (se 4 (by rfl) ⟨9243, by rfl⟩) (B 18487 (by norm_num) ⟨9243, by rfl⟩ (by norm_num))
theorem R33065 : Reach 33065 := rs (se 2 (by rfl) ⟨12399, by rfl⟩) (B 24799 (by norm_num) ⟨12399, by rfl⟩ (by norm_num))
theorem R33069 : Reach 33069 := rs (se 3 (by rfl) ⟨6200, by rfl⟩) (B 12401 (by norm_num) ⟨6200, by rfl⟩ (by norm_num))
theorem R33073 : Reach 33073 := rs (se 2 (by rfl) ⟨12402, by rfl⟩) (B 24805 (by norm_num) ⟨12402, by rfl⟩ (by norm_num))
theorem R33077 : Reach 33077 := rs (se 5 (by rfl) ⟨1550, by rfl⟩) (B 3101 (by norm_num) ⟨1550, by rfl⟩ (by norm_num))
theorem R33081 : Reach 33081 := rs (se 2 (by rfl) ⟨12405, by rfl⟩) (B 24811 (by norm_num) ⟨12405, by rfl⟩ (by norm_num))
theorem R33085 : Reach 33085 := rs (se 3 (by rfl) ⟨6203, by rfl⟩) (B 12407 (by norm_num) ⟨6203, by rfl⟩ (by norm_num))
theorem R33089 : Reach 33089 := rs (se 2 (by rfl) ⟨12408, by rfl⟩) (B 24817 (by norm_num) ⟨12408, by rfl⟩ (by norm_num))
theorem R33093 : Reach 33093 := rs (se 4 (by rfl) ⟨3102, by rfl⟩) (B 6205 (by norm_num) ⟨3102, by rfl⟩ (by norm_num))
theorem R33097 : Reach 33097 := rs (se 2 (by rfl) ⟨12411, by rfl⟩) (B 24823 (by norm_num) ⟨12411, by rfl⟩ (by norm_num))
theorem R33101 : Reach 33101 := rs (se 3 (by rfl) ⟨6206, by rfl⟩) (B 12413 (by norm_num) ⟨6206, by rfl⟩ (by norm_num))
theorem R33105 : Reach 33105 := rs (se 2 (by rfl) ⟨12414, by rfl⟩) (B 24829 (by norm_num) ⟨12414, by rfl⟩ (by norm_num))
theorem R33109 : Reach 33109 := rs (se 10 (by rfl) ⟨48, by rfl⟩) (B 97 (by norm_num) ⟨48, by rfl⟩ (by norm_num))
theorem R33113 : Reach 33113 := rs (se 2 (by rfl) ⟨12417, by rfl⟩) (B 24835 (by norm_num) ⟨12417, by rfl⟩ (by norm_num))
theorem R33117 : Reach 33117 := rs (se 3 (by rfl) ⟨6209, by rfl⟩) (B 12419 (by norm_num) ⟨6209, by rfl⟩ (by norm_num))
theorem R33121 : Reach 33121 := rs (se 2 (by rfl) ⟨12420, by rfl⟩) (B 24841 (by norm_num) ⟨12420, by rfl⟩ (by norm_num))
theorem R33125 : Reach 33125 := rs (se 4 (by rfl) ⟨3105, by rfl⟩) (B 6211 (by norm_num) ⟨3105, by rfl⟩ (by norm_num))
theorem R33129 : Reach 33129 := rs (se 2 (by rfl) ⟨12423, by rfl⟩) (B 24847 (by norm_num) ⟨12423, by rfl⟩ (by norm_num))
theorem R33133 : Reach 33133 := rs (se 3 (by rfl) ⟨6212, by rfl⟩) (B 12425 (by norm_num) ⟨6212, by rfl⟩ (by norm_num))
theorem R33137 : Reach 33137 := rs (se 2 (by rfl) ⟨12426, by rfl⟩) (B 24853 (by norm_num) ⟨12426, by rfl⟩ (by norm_num))
theorem R33141 : Reach 33141 := rs (se 5 (by rfl) ⟨1553, by rfl⟩) (B 3107 (by norm_num) ⟨1553, by rfl⟩ (by norm_num))
theorem R33145 : Reach 33145 := rs (se 2 (by rfl) ⟨12429, by rfl⟩) (B 24859 (by norm_num) ⟨12429, by rfl⟩ (by norm_num))
theorem R33149 : Reach 33149 := rs (se 3 (by rfl) ⟨6215, by rfl⟩) (B 12431 (by norm_num) ⟨6215, by rfl⟩ (by norm_num))
theorem R33153 : Reach 33153 := rs (se 2 (by rfl) ⟨12432, by rfl⟩) (B 24865 (by norm_num) ⟨12432, by rfl⟩ (by norm_num))
theorem R33157 : Reach 33157 := rs (se 4 (by rfl) ⟨3108, by rfl⟩) (B 6217 (by norm_num) ⟨3108, by rfl⟩ (by norm_num))
theorem R33161 : Reach 33161 := rs (se 2 (by rfl) ⟨12435, by rfl⟩) (B 24871 (by norm_num) ⟨12435, by rfl⟩ (by norm_num))
theorem R33165 : Reach 33165 := rs (se 3 (by rfl) ⟨6218, by rfl⟩) (B 12437 (by norm_num) ⟨6218, by rfl⟩ (by norm_num))
theorem R33169 : Reach 33169 := rs (se 2 (by rfl) ⟨12438, by rfl⟩) (B 24877 (by norm_num) ⟨12438, by rfl⟩ (by norm_num))
theorem R33173 : Reach 33173 := rs (se 6 (by rfl) ⟨777, by rfl⟩) (B 1555 (by norm_num) ⟨777, by rfl⟩ (by norm_num))
theorem R33177 : Reach 33177 := rs (se 2 (by rfl) ⟨12441, by rfl⟩) (B 24883 (by norm_num) ⟨12441, by rfl⟩ (by norm_num))
theorem R33181 : Reach 33181 := rs (se 3 (by rfl) ⟨6221, by rfl⟩) (B 12443 (by norm_num) ⟨6221, by rfl⟩ (by norm_num))
theorem R33185 : Reach 33185 := rs (se 2 (by rfl) ⟨12444, by rfl⟩) (B 24889 (by norm_num) ⟨12444, by rfl⟩ (by norm_num))
theorem R33189 : Reach 33189 := rs (se 4 (by rfl) ⟨3111, by rfl⟩) (B 6223 (by norm_num) ⟨3111, by rfl⟩ (by norm_num))
theorem R33193 : Reach 33193 := rs (se 2 (by rfl) ⟨12447, by rfl⟩) (B 24895 (by norm_num) ⟨12447, by rfl⟩ (by norm_num))
theorem R33197 : Reach 33197 := rs (se 3 (by rfl) ⟨6224, by rfl⟩) (B 12449 (by norm_num) ⟨6224, by rfl⟩ (by norm_num))
theorem R33201 : Reach 33201 := rs (se 2 (by rfl) ⟨12450, by rfl⟩) (B 24901 (by norm_num) ⟨12450, by rfl⟩ (by norm_num))
theorem R33205 : Reach 33205 := rs (se 5 (by rfl) ⟨1556, by rfl⟩) (B 3113 (by norm_num) ⟨1556, by rfl⟩ (by norm_num))
theorem R33209 : Reach 33209 := rs (se 2 (by rfl) ⟨12453, by rfl⟩) (B 24907 (by norm_num) ⟨12453, by rfl⟩ (by norm_num))
theorem R33213 : Reach 33213 := rs (se 3 (by rfl) ⟨6227, by rfl⟩) (B 12455 (by norm_num) ⟨6227, by rfl⟩ (by norm_num))
theorem R33217 : Reach 33217 := rs (se 2 (by rfl) ⟨12456, by rfl⟩) (B 24913 (by norm_num) ⟨12456, by rfl⟩ (by norm_num))
theorem R33221 : Reach 33221 := rs (se 4 (by rfl) ⟨3114, by rfl⟩) (B 6229 (by norm_num) ⟨3114, by rfl⟩ (by norm_num))
theorem R33225 : Reach 33225 := rs (se 2 (by rfl) ⟨12459, by rfl⟩) (B 24919 (by norm_num) ⟨12459, by rfl⟩ (by norm_num))
theorem R33229 : Reach 33229 := rs (se 3 (by rfl) ⟨6230, by rfl⟩) (B 12461 (by norm_num) ⟨6230, by rfl⟩ (by norm_num))
theorem R33233 : Reach 33233 := rs (se 2 (by rfl) ⟨12462, by rfl⟩) (B 24925 (by norm_num) ⟨12462, by rfl⟩ (by norm_num))
theorem R33237 : Reach 33237 := rs (se 7 (by rfl) ⟨389, by rfl⟩) (B 779 (by norm_num) ⟨389, by rfl⟩ (by norm_num))
theorem R66005 : Reach 66005 := rs (se 7 (by rfl) ⟨773, by rfl⟩) (B 1547 (by norm_num) ⟨773, by rfl⟩ (by norm_num))
theorem R33241 : Reach 33241 := rs (se 2 (by rfl) ⟨12465, by rfl⟩) (B 24931 (by norm_num) ⟨12465, by rfl⟩ (by norm_num))
theorem R33245 : Reach 33245 := rs (se 3 (by rfl) ⟨6233, by rfl⟩) (B 12467 (by norm_num) ⟨6233, by rfl⟩ (by norm_num))
theorem R33249 : Reach 33249 := rs (se 2 (by rfl) ⟨12468, by rfl⟩) (B 24937 (by norm_num) ⟨12468, by rfl⟩ (by norm_num))
theorem R33253 : Reach 33253 := rs (se 4 (by rfl) ⟨3117, by rfl⟩) (B 6235 (by norm_num) ⟨3117, by rfl⟩ (by norm_num))
theorem R33257 : Reach 33257 := rs (se 2 (by rfl) ⟨12471, by rfl⟩) (B 24943 (by norm_num) ⟨12471, by rfl⟩ (by norm_num))
theorem R33261 : Reach 33261 := rs (se 3 (by rfl) ⟨6236, by rfl⟩) (B 12473 (by norm_num) ⟨6236, by rfl⟩ (by norm_num))
theorem R33265 : Reach 33265 := rs (se 2 (by rfl) ⟨12474, by rfl⟩) (B 24949 (by norm_num) ⟨12474, by rfl⟩ (by norm_num))
theorem R33269 : Reach 33269 := rs (se 5 (by rfl) ⟨1559, by rfl⟩) (B 3119 (by norm_num) ⟨1559, by rfl⟩ (by norm_num))
theorem R33273 : Reach 33273 := rs (se 2 (by rfl) ⟨12477, by rfl⟩) (B 24955 (by norm_num) ⟨12477, by rfl⟩ (by norm_num))
theorem R33277 : Reach 33277 := rs (se 3 (by rfl) ⟨6239, by rfl⟩) (B 12479 (by norm_num) ⟨6239, by rfl⟩ (by norm_num))
theorem R33281 : Reach 33281 := rs (se 2 (by rfl) ⟨12480, by rfl⟩) (B 24961 (by norm_num) ⟨12480, by rfl⟩ (by norm_num))
theorem R33285 : Reach 33285 := rs (se 4 (by rfl) ⟨3120, by rfl⟩) (B 6241 (by norm_num) ⟨3120, by rfl⟩ (by norm_num))
theorem R33289 : Reach 33289 := rs (se 2 (by rfl) ⟨12483, by rfl⟩) (B 24967 (by norm_num) ⟨12483, by rfl⟩ (by norm_num))
theorem R33293 : Reach 33293 := rs (se 3 (by rfl) ⟨6242, by rfl⟩) (B 12485 (by norm_num) ⟨6242, by rfl⟩ (by norm_num))
theorem R33297 : Reach 33297 := rs (se 2 (by rfl) ⟨12486, by rfl⟩) (B 24973 (by norm_num) ⟨12486, by rfl⟩ (by norm_num))
theorem R33301 : Reach 33301 := rs (se 6 (by rfl) ⟨780, by rfl⟩) (B 1561 (by norm_num) ⟨780, by rfl⟩ (by norm_num))
theorem R33305 : Reach 33305 := rs (se 2 (by rfl) ⟨12489, by rfl⟩) (B 24979 (by norm_num) ⟨12489, by rfl⟩ (by norm_num))
theorem R33309 : Reach 33309 := rs (se 3 (by rfl) ⟨6245, by rfl⟩) (B 12491 (by norm_num) ⟨6245, by rfl⟩ (by norm_num))
theorem R33313 : Reach 33313 := rs (se 2 (by rfl) ⟨12492, by rfl⟩) (B 24985 (by norm_num) ⟨12492, by rfl⟩ (by norm_num))
theorem R33317 : Reach 33317 := rs (se 4 (by rfl) ⟨3123, by rfl⟩) (B 6247 (by norm_num) ⟨3123, by rfl⟩ (by norm_num))
theorem R33321 : Reach 33321 := rs (se 2 (by rfl) ⟨12495, by rfl⟩) (B 24991 (by norm_num) ⟨12495, by rfl⟩ (by norm_num))
theorem R33325 : Reach 33325 := rs (se 3 (by rfl) ⟨6248, by rfl⟩) (B 12497 (by norm_num) ⟨6248, by rfl⟩ (by norm_num))
theorem R33329 : Reach 33329 := rs (se 2 (by rfl) ⟨12498, by rfl⟩) (B 24997 (by norm_num) ⟨12498, by rfl⟩ (by norm_num))
theorem R33333 : Reach 33333 := rs (se 5 (by rfl) ⟨1562, by rfl⟩) (B 3125 (by norm_num) ⟨1562, by rfl⟩ (by norm_num))
theorem R33337 : Reach 33337 := rs (se 2 (by rfl) ⟨12501, by rfl⟩) (B 25003 (by norm_num) ⟨12501, by rfl⟩ (by norm_num))
theorem R33341 : Reach 33341 := rs (se 3 (by rfl) ⟨6251, by rfl⟩) (B 12503 (by norm_num) ⟨6251, by rfl⟩ (by norm_num))
theorem R33345 : Reach 33345 := rs (se 2 (by rfl) ⟨12504, by rfl⟩) (B 25009 (by norm_num) ⟨12504, by rfl⟩ (by norm_num))
theorem R33349 : Reach 33349 := rs (se 4 (by rfl) ⟨3126, by rfl⟩) (B 6253 (by norm_num) ⟨3126, by rfl⟩ (by norm_num))
theorem R33353 : Reach 33353 := rs (se 2 (by rfl) ⟨12507, by rfl⟩) (B 25015 (by norm_num) ⟨12507, by rfl⟩ (by norm_num))
theorem R33357 : Reach 33357 := rs (se 3 (by rfl) ⟨6254, by rfl⟩) (B 12509 (by norm_num) ⟨6254, by rfl⟩ (by norm_num))
theorem R33361 : Reach 33361 := rs (se 2 (by rfl) ⟨12510, by rfl⟩) (B 25021 (by norm_num) ⟨12510, by rfl⟩ (by norm_num))
theorem R33365 : Reach 33365 := rs (se 8 (by rfl) ⟨195, by rfl⟩) (B 391 (by norm_num) ⟨195, by rfl⟩ (by norm_num))
theorem R33369 : Reach 33369 := rs (se 2 (by rfl) ⟨12513, by rfl⟩) (B 25027 (by norm_num) ⟨12513, by rfl⟩ (by norm_num))
theorem R33373 : Reach 33373 := rs (se 3 (by rfl) ⟨6257, by rfl⟩) (B 12515 (by norm_num) ⟨6257, by rfl⟩ (by norm_num))
theorem R33377 : Reach 33377 := rs (se 2 (by rfl) ⟨12516, by rfl⟩) (B 25033 (by norm_num) ⟨12516, by rfl⟩ (by norm_num))
theorem R33381 : Reach 33381 := rs (se 4 (by rfl) ⟨3129, by rfl⟩) (B 6259 (by norm_num) ⟨3129, by rfl⟩ (by norm_num))
theorem R33385 : Reach 33385 := rs (se 2 (by rfl) ⟨12519, by rfl⟩) (B 25039 (by norm_num) ⟨12519, by rfl⟩ (by norm_num))
theorem R33389 : Reach 33389 := rs (se 3 (by rfl) ⟨6260, by rfl⟩) (B 12521 (by norm_num) ⟨6260, by rfl⟩ (by norm_num))
theorem R33393 : Reach 33393 := rs (se 2 (by rfl) ⟨12522, by rfl⟩) (B 25045 (by norm_num) ⟨12522, by rfl⟩ (by norm_num))
theorem R33397 : Reach 33397 := rs (se 5 (by rfl) ⟨1565, by rfl⟩) (B 3131 (by norm_num) ⟨1565, by rfl⟩ (by norm_num))
theorem R33401 : Reach 33401 := rs (se 2 (by rfl) ⟨12525, by rfl⟩) (B 25051 (by norm_num) ⟨12525, by rfl⟩ (by norm_num))
theorem R33405 : Reach 33405 := rs (se 3 (by rfl) ⟨6263, by rfl⟩) (B 12527 (by norm_num) ⟨6263, by rfl⟩ (by norm_num))
theorem R33409 : Reach 33409 := rs (se 2 (by rfl) ⟨12528, by rfl⟩) (B 25057 (by norm_num) ⟨12528, by rfl⟩ (by norm_num))
theorem R33413 : Reach 33413 := rs (se 4 (by rfl) ⟨3132, by rfl⟩) (B 6265 (by norm_num) ⟨3132, by rfl⟩ (by norm_num))
theorem R33417 : Reach 33417 := rs (se 2 (by rfl) ⟨12531, by rfl⟩) (B 25063 (by norm_num) ⟨12531, by rfl⟩ (by norm_num))
theorem R33421 : Reach 33421 := rs (se 3 (by rfl) ⟨6266, by rfl⟩) (B 12533 (by norm_num) ⟨6266, by rfl⟩ (by norm_num))
theorem R33425 : Reach 33425 := rs (se 2 (by rfl) ⟨12534, by rfl⟩) (B 25069 (by norm_num) ⟨12534, by rfl⟩ (by norm_num))
theorem R33429 : Reach 33429 := rs (se 6 (by rfl) ⟨783, by rfl⟩) (B 1567 (by norm_num) ⟨783, by rfl⟩ (by norm_num))
theorem R33433 : Reach 33433 := rs (se 2 (by rfl) ⟨12537, by rfl⟩) (B 25075 (by norm_num) ⟨12537, by rfl⟩ (by norm_num))
theorem R33437 : Reach 33437 := rs (se 3 (by rfl) ⟨6269, by rfl⟩) (B 12539 (by norm_num) ⟨6269, by rfl⟩ (by norm_num))
theorem R33441 : Reach 33441 := rs (se 2 (by rfl) ⟨12540, by rfl⟩) (B 25081 (by norm_num) ⟨12540, by rfl⟩ (by norm_num))
theorem R33445 : Reach 33445 := rs (se 4 (by rfl) ⟨3135, by rfl⟩) (B 6271 (by norm_num) ⟨3135, by rfl⟩ (by norm_num))
theorem R33449 : Reach 33449 := rs (se 2 (by rfl) ⟨12543, by rfl⟩) (B 25087 (by norm_num) ⟨12543, by rfl⟩ (by norm_num))
theorem R33453 : Reach 33453 := rs (se 3 (by rfl) ⟨6272, by rfl⟩) (B 12545 (by norm_num) ⟨6272, by rfl⟩ (by norm_num))
theorem R33457 : Reach 33457 := rs (se 2 (by rfl) ⟨12546, by rfl⟩) (B 25093 (by norm_num) ⟨12546, by rfl⟩ (by norm_num))
theorem R33461 : Reach 33461 := rs (se 5 (by rfl) ⟨1568, by rfl⟩) (B 3137 (by norm_num) ⟨1568, by rfl⟩ (by norm_num))
theorem R33465 : Reach 33465 := rs (se 2 (by rfl) ⟨12549, by rfl⟩) (B 25099 (by norm_num) ⟨12549, by rfl⟩ (by norm_num))
theorem R33469 : Reach 33469 := rs (se 3 (by rfl) ⟨6275, by rfl⟩) (B 12551 (by norm_num) ⟨6275, by rfl⟩ (by norm_num))
theorem R33473 : Reach 33473 := rs (se 2 (by rfl) ⟨12552, by rfl⟩) (B 25105 (by norm_num) ⟨12552, by rfl⟩ (by norm_num))
theorem R33477 : Reach 33477 := rs (se 4 (by rfl) ⟨3138, by rfl⟩) (B 6277 (by norm_num) ⟨3138, by rfl⟩ (by norm_num))
theorem R33481 : Reach 33481 := rs (se 2 (by rfl) ⟨12555, by rfl⟩) (B 25111 (by norm_num) ⟨12555, by rfl⟩ (by norm_num))
theorem R33485 : Reach 33485 := rs (se 3 (by rfl) ⟨6278, by rfl⟩) (B 12557 (by norm_num) ⟨6278, by rfl⟩ (by norm_num))
theorem R33489 : Reach 33489 := rs (se 2 (by rfl) ⟨12558, by rfl⟩) (B 25117 (by norm_num) ⟨12558, by rfl⟩ (by norm_num))
theorem R33493 : Reach 33493 := rs (se 7 (by rfl) ⟨392, by rfl⟩) (B 785 (by norm_num) ⟨392, by rfl⟩ (by norm_num))
theorem R33497 : Reach 33497 := rs (se 2 (by rfl) ⟨12561, by rfl⟩) (B 25123 (by norm_num) ⟨12561, by rfl⟩ (by norm_num))
theorem R33501 : Reach 33501 := rs (se 3 (by rfl) ⟨6281, by rfl⟩) (B 12563 (by norm_num) ⟨6281, by rfl⟩ (by norm_num))
theorem R33505 : Reach 33505 := rs (se 2 (by rfl) ⟨12564, by rfl⟩) (B 25129 (by norm_num) ⟨12564, by rfl⟩ (by norm_num))
theorem R131813 : Reach 131813 := rs (se 4 (by rfl) ⟨12357, by rfl⟩) (B 24715 (by norm_num) ⟨12357, by rfl⟩ (by norm_num))
theorem R33509 : Reach 33509 := rs (se 4 (by rfl) ⟨3141, by rfl⟩) (B 6283 (by norm_num) ⟨3141, by rfl⟩ (by norm_num))
theorem R33513 : Reach 33513 := rs (se 2 (by rfl) ⟨12567, by rfl⟩) (B 25135 (by norm_num) ⟨12567, by rfl⟩ (by norm_num))
theorem R33517 : Reach 33517 := rs (se 3 (by rfl) ⟨6284, by rfl⟩) (B 12569 (by norm_num) ⟨6284, by rfl⟩ (by norm_num))
theorem R33521 : Reach 33521 := rs (se 2 (by rfl) ⟨12570, by rfl⟩) (B 25141 (by norm_num) ⟨12570, by rfl⟩ (by norm_num))
theorem R33525 : Reach 33525 := rs (se 5 (by rfl) ⟨1571, by rfl⟩) (B 3143 (by norm_num) ⟨1571, by rfl⟩ (by norm_num))
theorem R33529 : Reach 33529 := rs (se 2 (by rfl) ⟨12573, by rfl⟩) (B 25147 (by norm_num) ⟨12573, by rfl⟩ (by norm_num))
theorem R33533 : Reach 33533 := rs (se 3 (by rfl) ⟨6287, by rfl⟩) (B 12575 (by norm_num) ⟨6287, by rfl⟩ (by norm_num))
theorem R33537 : Reach 33537 := rs (se 2 (by rfl) ⟨12576, by rfl⟩) (B 25153 (by norm_num) ⟨12576, by rfl⟩ (by norm_num))
theorem R33541 : Reach 33541 := rs (se 4 (by rfl) ⟨3144, by rfl⟩) (B 6289 (by norm_num) ⟨3144, by rfl⟩ (by norm_num))
theorem R33545 : Reach 33545 := rs (se 2 (by rfl) ⟨12579, by rfl⟩) (B 25159 (by norm_num) ⟨12579, by rfl⟩ (by norm_num))
theorem R33549 : Reach 33549 := rs (se 3 (by rfl) ⟨6290, by rfl⟩) (B 12581 (by norm_num) ⟨6290, by rfl⟩ (by norm_num))
theorem R33553 : Reach 33553 := rs (se 2 (by rfl) ⟨12582, by rfl⟩) (B 25165 (by norm_num) ⟨12582, by rfl⟩ (by norm_num))
theorem R33557 : Reach 33557 := rs (se 6 (by rfl) ⟨786, by rfl⟩) (B 1573 (by norm_num) ⟨786, by rfl⟩ (by norm_num))
theorem R33561 : Reach 33561 := rs (se 2 (by rfl) ⟨12585, by rfl⟩) (B 25171 (by norm_num) ⟨12585, by rfl⟩ (by norm_num))
theorem R33565 : Reach 33565 := rs (se 3 (by rfl) ⟨6293, by rfl⟩) (B 12587 (by norm_num) ⟨6293, by rfl⟩ (by norm_num))
theorem R33569 : Reach 33569 := rs (se 2 (by rfl) ⟨12588, by rfl⟩) (B 25177 (by norm_num) ⟨12588, by rfl⟩ (by norm_num))
theorem R33573 : Reach 33573 := rs (se 4 (by rfl) ⟨3147, by rfl⟩) (B 6295 (by norm_num) ⟨3147, by rfl⟩ (by norm_num))
theorem R33577 : Reach 33577 := rs (se 2 (by rfl) ⟨12591, by rfl⟩) (B 25183 (by norm_num) ⟨12591, by rfl⟩ (by norm_num))
theorem R33581 : Reach 33581 := rs (se 3 (by rfl) ⟨6296, by rfl⟩) (B 12593 (by norm_num) ⟨6296, by rfl⟩ (by norm_num))
theorem R33585 : Reach 33585 := rs (se 2 (by rfl) ⟨12594, by rfl⟩) (B 25189 (by norm_num) ⟨12594, by rfl⟩ (by norm_num))
theorem R33589 : Reach 33589 := rs (se 5 (by rfl) ⟨1574, by rfl⟩) (B 3149 (by norm_num) ⟨1574, by rfl⟩ (by norm_num))
theorem R33593 : Reach 33593 := rs (se 2 (by rfl) ⟨12597, by rfl⟩) (B 25195 (by norm_num) ⟨12597, by rfl⟩ (by norm_num))
theorem R33597 : Reach 33597 := rs (se 3 (by rfl) ⟨6299, by rfl⟩) (B 12599 (by norm_num) ⟨6299, by rfl⟩ (by norm_num))
theorem R33601 : Reach 33601 := rs (se 2 (by rfl) ⟨12600, by rfl⟩) (B 25201 (by norm_num) ⟨12600, by rfl⟩ (by norm_num))
theorem R33605 : Reach 33605 := rs (se 4 (by rfl) ⟨3150, by rfl⟩) (B 6301 (by norm_num) ⟨3150, by rfl⟩ (by norm_num))
theorem R33609 : Reach 33609 := rs (se 2 (by rfl) ⟨12603, by rfl⟩) (B 25207 (by norm_num) ⟨12603, by rfl⟩ (by norm_num))
theorem R33613 : Reach 33613 := rs (se 3 (by rfl) ⟨6302, by rfl⟩) (B 12605 (by norm_num) ⟨6302, by rfl⟩ (by norm_num))
theorem R33617 : Reach 33617 := rs (se 2 (by rfl) ⟨12606, by rfl⟩) (B 25213 (by norm_num) ⟨12606, by rfl⟩ (by norm_num))
theorem R33621 : Reach 33621 := rs (se 9 (by rfl) ⟨98, by rfl⟩) (B 197 (by norm_num) ⟨98, by rfl⟩ (by norm_num))
theorem R164693 : Reach 164693 := rs (se 9 (by rfl) ⟨482, by rfl⟩) (B 965 (by norm_num) ⟨482, by rfl⟩ (by norm_num))
theorem R33625 : Reach 33625 := rs (se 2 (by rfl) ⟨12609, by rfl⟩) (B 25219 (by norm_num) ⟨12609, by rfl⟩ (by norm_num))
theorem R33629 : Reach 33629 := rs (se 3 (by rfl) ⟨6305, by rfl⟩) (B 12611 (by norm_num) ⟨6305, by rfl⟩ (by norm_num))
theorem R33633 : Reach 33633 := rs (se 2 (by rfl) ⟨12612, by rfl⟩) (B 25225 (by norm_num) ⟨12612, by rfl⟩ (by norm_num))
theorem R33637 : Reach 33637 := rs (se 4 (by rfl) ⟨3153, by rfl⟩) (B 6307 (by norm_num) ⟨3153, by rfl⟩ (by norm_num))
theorem R33641 : Reach 33641 := rs (se 2 (by rfl) ⟨12615, by rfl⟩) (B 25231 (by norm_num) ⟨12615, by rfl⟩ (by norm_num))
theorem R33645 : Reach 33645 := rs (se 3 (by rfl) ⟨6308, by rfl⟩) (B 12617 (by norm_num) ⟨6308, by rfl⟩ (by norm_num))
theorem R33649 : Reach 33649 := rs (se 2 (by rfl) ⟨12618, by rfl⟩) (B 25237 (by norm_num) ⟨12618, by rfl⟩ (by norm_num))
theorem R33653 : Reach 33653 := rs (se 5 (by rfl) ⟨1577, by rfl⟩) (B 3155 (by norm_num) ⟨1577, by rfl⟩ (by norm_num))
theorem R33657 : Reach 33657 := rs (se 2 (by rfl) ⟨12621, by rfl⟩) (B 25243 (by norm_num) ⟨12621, by rfl⟩ (by norm_num))
theorem R33661 : Reach 33661 := rs (se 3 (by rfl) ⟨6311, by rfl⟩) (B 12623 (by norm_num) ⟨6311, by rfl⟩ (by norm_num))
theorem R33665 : Reach 33665 := rs (se 2 (by rfl) ⟨12624, by rfl⟩) (B 25249 (by norm_num) ⟨12624, by rfl⟩ (by norm_num))
theorem R33669 : Reach 33669 := rs (se 4 (by rfl) ⟨3156, by rfl⟩) (B 6313 (by norm_num) ⟨3156, by rfl⟩ (by norm_num))
theorem R33673 : Reach 33673 := rs (se 2 (by rfl) ⟨12627, by rfl⟩) (B 25255 (by norm_num) ⟨12627, by rfl⟩ (by norm_num))
theorem R33677 : Reach 33677 := rs (se 3 (by rfl) ⟨6314, by rfl⟩) (B 12629 (by norm_num) ⟨6314, by rfl⟩ (by norm_num))
theorem R33681 : Reach 33681 := rs (se 2 (by rfl) ⟨12630, by rfl⟩) (B 25261 (by norm_num) ⟨12630, by rfl⟩ (by norm_num))
theorem R33685 : Reach 33685 := rs (se 6 (by rfl) ⟨789, by rfl⟩) (B 1579 (by norm_num) ⟨789, by rfl⟩ (by norm_num))
theorem R33689 : Reach 33689 := rs (se 2 (by rfl) ⟨12633, by rfl⟩) (B 25267 (by norm_num) ⟨12633, by rfl⟩ (by norm_num))
theorem R33693 : Reach 33693 := rs (se 3 (by rfl) ⟨6317, by rfl⟩) (B 12635 (by norm_num) ⟨6317, by rfl⟩ (by norm_num))
theorem R33697 : Reach 33697 := rs (se 2 (by rfl) ⟨12636, by rfl⟩) (B 25273 (by norm_num) ⟨12636, by rfl⟩ (by norm_num))
theorem R33701 : Reach 33701 := rs (se 4 (by rfl) ⟨3159, by rfl⟩) (B 6319 (by norm_num) ⟨3159, by rfl⟩ (by norm_num))
theorem R33705 : Reach 33705 := rs (se 2 (by rfl) ⟨12639, by rfl⟩) (B 25279 (by norm_num) ⟨12639, by rfl⟩ (by norm_num))
theorem R33709 : Reach 33709 := rs (se 3 (by rfl) ⟨6320, by rfl⟩) (B 12641 (by norm_num) ⟨6320, by rfl⟩ (by norm_num))
theorem R33713 : Reach 33713 := rs (se 2 (by rfl) ⟨12642, by rfl⟩) (B 25285 (by norm_num) ⟨12642, by rfl⟩ (by norm_num))
theorem R33717 : Reach 33717 := rs (se 5 (by rfl) ⟨1580, by rfl⟩) (B 3161 (by norm_num) ⟨1580, by rfl⟩ (by norm_num))
theorem R33721 : Reach 33721 := rs (se 2 (by rfl) ⟨12645, by rfl⟩) (B 25291 (by norm_num) ⟨12645, by rfl⟩ (by norm_num))
theorem R33725 : Reach 33725 := rs (se 3 (by rfl) ⟨6323, by rfl⟩) (B 12647 (by norm_num) ⟨6323, by rfl⟩ (by norm_num))
theorem R33729 : Reach 33729 := rs (se 2 (by rfl) ⟨12648, by rfl⟩) (B 25297 (by norm_num) ⟨12648, by rfl⟩ (by norm_num))
theorem R33733 : Reach 33733 := rs (se 4 (by rfl) ⟨3162, by rfl⟩) (B 6325 (by norm_num) ⟨3162, by rfl⟩ (by norm_num))
theorem R33737 : Reach 33737 := rs (se 2 (by rfl) ⟨12651, by rfl⟩) (B 25303 (by norm_num) ⟨12651, by rfl⟩ (by norm_num))
theorem R33741 : Reach 33741 := rs (se 3 (by rfl) ⟨6326, by rfl⟩) (B 12653 (by norm_num) ⟨6326, by rfl⟩ (by norm_num))
theorem R33745 : Reach 33745 := rs (se 2 (by rfl) ⟨12654, by rfl⟩) (B 25309 (by norm_num) ⟨12654, by rfl⟩ (by norm_num))
theorem R33749 : Reach 33749 := rs (se 7 (by rfl) ⟨395, by rfl⟩) (B 791 (by norm_num) ⟨395, by rfl⟩ (by norm_num))
theorem R33753 : Reach 33753 := rs (se 2 (by rfl) ⟨12657, by rfl⟩) (B 25315 (by norm_num) ⟨12657, by rfl⟩ (by norm_num))
theorem R33757 : Reach 33757 := rs (se 3 (by rfl) ⟨6329, by rfl⟩) (B 12659 (by norm_num) ⟨6329, by rfl⟩ (by norm_num))
theorem R33761 : Reach 33761 := rs (se 2 (by rfl) ⟨12660, by rfl⟩) (B 25321 (by norm_num) ⟨12660, by rfl⟩ (by norm_num))
theorem R33765 : Reach 33765 := rs (se 4 (by rfl) ⟨3165, by rfl⟩) (B 6331 (by norm_num) ⟨3165, by rfl⟩ (by norm_num))
theorem R33769 : Reach 33769 := rs (se 2 (by rfl) ⟨12663, by rfl⟩) (B 25327 (by norm_num) ⟨12663, by rfl⟩ (by norm_num))
theorem R33773 : Reach 33773 := rs (se 3 (by rfl) ⟨6332, by rfl⟩) (B 12665 (by norm_num) ⟨6332, by rfl⟩ (by norm_num))
theorem R33777 : Reach 33777 := rs (se 2 (by rfl) ⟨12666, by rfl⟩) (B 25333 (by norm_num) ⟨12666, by rfl⟩ (by norm_num))
theorem R33781 : Reach 33781 := rs (se 5 (by rfl) ⟨1583, by rfl⟩) (B 3167 (by norm_num) ⟨1583, by rfl⟩ (by norm_num))
theorem R33785 : Reach 33785 := rs (se 2 (by rfl) ⟨12669, by rfl⟩) (B 25339 (by norm_num) ⟨12669, by rfl⟩ (by norm_num))
theorem R33789 : Reach 33789 := rs (se 3 (by rfl) ⟨6335, by rfl⟩) (B 12671 (by norm_num) ⟨6335, by rfl⟩ (by norm_num))
theorem R33793 : Reach 33793 := rs (se 2 (by rfl) ⟨12672, by rfl⟩) (B 25345 (by norm_num) ⟨12672, by rfl⟩ (by norm_num))
theorem R33797 : Reach 33797 := rs (se 4 (by rfl) ⟨3168, by rfl⟩) (B 6337 (by norm_num) ⟨3168, by rfl⟩ (by norm_num))
theorem R132101 : Reach 132101 := rs (se 4 (by rfl) ⟨12384, by rfl⟩) (B 24769 (by norm_num) ⟨12384, by rfl⟩ (by norm_num))
theorem R33801 : Reach 33801 := rs (se 2 (by rfl) ⟨12675, by rfl⟩) (B 25351 (by norm_num) ⟨12675, by rfl⟩ (by norm_num))
theorem R33805 : Reach 33805 := rs (se 3 (by rfl) ⟨6338, by rfl⟩) (B 12677 (by norm_num) ⟨6338, by rfl⟩ (by norm_num))
theorem R33809 : Reach 33809 := rs (se 2 (by rfl) ⟨12678, by rfl⟩) (B 25357 (by norm_num) ⟨12678, by rfl⟩ (by norm_num))
theorem R33813 : Reach 33813 := rs (se 6 (by rfl) ⟨792, by rfl⟩) (B 1585 (by norm_num) ⟨792, by rfl⟩ (by norm_num))
theorem R33817 : Reach 33817 := rs (se 2 (by rfl) ⟨12681, by rfl⟩) (B 25363 (by norm_num) ⟨12681, by rfl⟩ (by norm_num))
theorem R33821 : Reach 33821 := rs (se 3 (by rfl) ⟨6341, by rfl⟩) (B 12683 (by norm_num) ⟨6341, by rfl⟩ (by norm_num))
theorem R33825 : Reach 33825 := rs (se 2 (by rfl) ⟨12684, by rfl⟩) (B 25369 (by norm_num) ⟨12684, by rfl⟩ (by norm_num))
theorem R33829 : Reach 33829 := rs (se 4 (by rfl) ⟨3171, by rfl⟩) (B 6343 (by norm_num) ⟨3171, by rfl⟩ (by norm_num))
theorem R33833 : Reach 33833 := rs (se 2 (by rfl) ⟨12687, by rfl⟩) (B 25375 (by norm_num) ⟨12687, by rfl⟩ (by norm_num))
theorem R33837 : Reach 33837 := rs (se 3 (by rfl) ⟨6344, by rfl⟩) (B 12689 (by norm_num) ⟨6344, by rfl⟩ (by norm_num))
theorem R33841 : Reach 33841 := rs (se 2 (by rfl) ⟨12690, by rfl⟩) (B 25381 (by norm_num) ⟨12690, by rfl⟩ (by norm_num))
theorem R33845 : Reach 33845 := rs (se 5 (by rfl) ⟨1586, by rfl⟩) (B 3173 (by norm_num) ⟨1586, by rfl⟩ (by norm_num))
theorem R33849 : Reach 33849 := rs (se 2 (by rfl) ⟨12693, by rfl⟩) (B 25387 (by norm_num) ⟨12693, by rfl⟩ (by norm_num))
theorem R33853 : Reach 33853 := rs (se 3 (by rfl) ⟨6347, by rfl⟩) (B 12695 (by norm_num) ⟨6347, by rfl⟩ (by norm_num))
theorem R33857 : Reach 33857 := rs (se 2 (by rfl) ⟨12696, by rfl⟩) (B 25393 (by norm_num) ⟨12696, by rfl⟩ (by norm_num))
theorem R33861 : Reach 33861 := rs (se 4 (by rfl) ⟨3174, by rfl⟩) (B 6349 (by norm_num) ⟨3174, by rfl⟩ (by norm_num))
theorem R33865 : Reach 33865 := rs (se 2 (by rfl) ⟨12699, by rfl⟩) (B 25399 (by norm_num) ⟨12699, by rfl⟩ (by norm_num))
theorem R33869 : Reach 33869 := rs (se 3 (by rfl) ⟨6350, by rfl⟩) (B 12701 (by norm_num) ⟨6350, by rfl⟩ (by norm_num))
theorem R33873 : Reach 33873 := rs (se 2 (by rfl) ⟨12702, by rfl⟩) (B 25405 (by norm_num) ⟨12702, by rfl⟩ (by norm_num))
theorem R33877 : Reach 33877 := rs (se 8 (by rfl) ⟨198, by rfl⟩) (B 397 (by norm_num) ⟨198, by rfl⟩ (by norm_num))
theorem R33881 : Reach 33881 := rs (se 2 (by rfl) ⟨12705, by rfl⟩) (B 25411 (by norm_num) ⟨12705, by rfl⟩ (by norm_num))
theorem R66653 : Reach 66653 := rs (se 3 (by rfl) ⟨12497, by rfl⟩) (B 24995 (by norm_num) ⟨12497, by rfl⟩ (by norm_num))
theorem R33885 : Reach 33885 := rs (se 3 (by rfl) ⟨6353, by rfl⟩) (B 12707 (by norm_num) ⟨6353, by rfl⟩ (by norm_num))
theorem R33889 : Reach 33889 := rs (se 2 (by rfl) ⟨12708, by rfl⟩) (B 25417 (by norm_num) ⟨12708, by rfl⟩ (by norm_num))
theorem R33893 : Reach 33893 := rs (se 4 (by rfl) ⟨3177, by rfl⟩) (B 6355 (by norm_num) ⟨3177, by rfl⟩ (by norm_num))
theorem R33897 : Reach 33897 := rs (se 2 (by rfl) ⟨12711, by rfl⟩) (B 25423 (by norm_num) ⟨12711, by rfl⟩ (by norm_num))
theorem R33901 : Reach 33901 := rs (se 3 (by rfl) ⟨6356, by rfl⟩) (B 12713 (by norm_num) ⟨6356, by rfl⟩ (by norm_num))
theorem R33905 : Reach 33905 := rs (se 2 (by rfl) ⟨12714, by rfl⟩) (B 25429 (by norm_num) ⟨12714, by rfl⟩ (by norm_num))
theorem R33909 : Reach 33909 := rs (se 5 (by rfl) ⟨1589, by rfl⟩) (B 3179 (by norm_num) ⟨1589, by rfl⟩ (by norm_num))
theorem R33913 : Reach 33913 := rs (se 2 (by rfl) ⟨12717, by rfl⟩) (B 25435 (by norm_num) ⟨12717, by rfl⟩ (by norm_num))
theorem R33917 : Reach 33917 := rs (se 3 (by rfl) ⟨6359, by rfl⟩) (B 12719 (by norm_num) ⟨6359, by rfl⟩ (by norm_num))
theorem R33921 : Reach 33921 := rs (se 2 (by rfl) ⟨12720, by rfl⟩) (B 25441 (by norm_num) ⟨12720, by rfl⟩ (by norm_num))
theorem R33925 : Reach 33925 := rs (se 4 (by rfl) ⟨3180, by rfl⟩) (B 6361 (by norm_num) ⟨3180, by rfl⟩ (by norm_num))
theorem R33929 : Reach 33929 := rs (se 2 (by rfl) ⟨12723, by rfl⟩) (B 25447 (by norm_num) ⟨12723, by rfl⟩ (by norm_num))
theorem R33933 : Reach 33933 := rs (se 3 (by rfl) ⟨6362, by rfl⟩) (B 12725 (by norm_num) ⟨6362, by rfl⟩ (by norm_num))
theorem R33937 : Reach 33937 := rs (se 2 (by rfl) ⟨12726, by rfl⟩) (B 25453 (by norm_num) ⟨12726, by rfl⟩ (by norm_num))
theorem R33941 : Reach 33941 := rs (se 6 (by rfl) ⟨795, by rfl⟩) (B 1591 (by norm_num) ⟨795, by rfl⟩ (by norm_num))
theorem R33945 : Reach 33945 := rs (se 2 (by rfl) ⟨12729, by rfl⟩) (B 25459 (by norm_num) ⟨12729, by rfl⟩ (by norm_num))
theorem R33949 : Reach 33949 := rs (se 3 (by rfl) ⟨6365, by rfl⟩) (B 12731 (by norm_num) ⟨6365, by rfl⟩ (by norm_num))
theorem R33953 : Reach 33953 := rs (se 2 (by rfl) ⟨12732, by rfl⟩) (B 25465 (by norm_num) ⟨12732, by rfl⟩ (by norm_num))
theorem R33957 : Reach 33957 := rs (se 4 (by rfl) ⟨3183, by rfl⟩) (B 6367 (by norm_num) ⟨3183, by rfl⟩ (by norm_num))
theorem R33961 : Reach 33961 := rs (se 2 (by rfl) ⟨12735, by rfl⟩) (B 25471 (by norm_num) ⟨12735, by rfl⟩ (by norm_num))
theorem R33965 : Reach 33965 := rs (se 3 (by rfl) ⟨6368, by rfl⟩) (B 12737 (by norm_num) ⟨6368, by rfl⟩ (by norm_num))
theorem R33969 : Reach 33969 := rs (se 2 (by rfl) ⟨12738, by rfl⟩) (B 25477 (by norm_num) ⟨12738, by rfl⟩ (by norm_num))
theorem R33973 : Reach 33973 := rs (se 5 (by rfl) ⟨1592, by rfl⟩) (B 3185 (by norm_num) ⟨1592, by rfl⟩ (by norm_num))
theorem R33977 : Reach 33977 := rs (se 2 (by rfl) ⟨12741, by rfl⟩) (B 25483 (by norm_num) ⟨12741, by rfl⟩ (by norm_num))
theorem R33981 : Reach 33981 := rs (se 3 (by rfl) ⟨6371, by rfl⟩) (B 12743 (by norm_num) ⟨6371, by rfl⟩ (by norm_num))
theorem R33985 : Reach 33985 := rs (se 2 (by rfl) ⟨12744, by rfl⟩) (B 25489 (by norm_num) ⟨12744, by rfl⟩ (by norm_num))
theorem R33989 : Reach 33989 := rs (se 4 (by rfl) ⟨3186, by rfl⟩) (B 6373 (by norm_num) ⟨3186, by rfl⟩ (by norm_num))
theorem R33993 : Reach 33993 := rs (se 2 (by rfl) ⟨12747, by rfl⟩) (B 25495 (by norm_num) ⟨12747, by rfl⟩ (by norm_num))
theorem R33997 : Reach 33997 := rs (se 3 (by rfl) ⟨6374, by rfl⟩) (B 12749 (by norm_num) ⟨6374, by rfl⟩ (by norm_num))
theorem R34001 : Reach 34001 := rs (se 2 (by rfl) ⟨12750, by rfl⟩) (B 25501 (by norm_num) ⟨12750, by rfl⟩ (by norm_num))
theorem R165077 : Reach 165077 := rs (se 7 (by rfl) ⟨1934, by rfl⟩) (B 3869 (by norm_num) ⟨1934, by rfl⟩ (by norm_num))
theorem R34005 : Reach 34005 := rs (se 7 (by rfl) ⟨398, by rfl⟩) (B 797 (by norm_num) ⟨398, by rfl⟩ (by norm_num))
theorem R34009 : Reach 34009 := rs (se 2 (by rfl) ⟨12753, by rfl⟩) (B 25507 (by norm_num) ⟨12753, by rfl⟩ (by norm_num))
theorem R34013 : Reach 34013 := rs (se 3 (by rfl) ⟨6377, by rfl⟩) (B 12755 (by norm_num) ⟨6377, by rfl⟩ (by norm_num))
theorem R34017 : Reach 34017 := rs (se 2 (by rfl) ⟨12756, by rfl⟩) (B 25513 (by norm_num) ⟨12756, by rfl⟩ (by norm_num))
theorem R34021 : Reach 34021 := rs (se 4 (by rfl) ⟨3189, by rfl⟩) (B 6379 (by norm_num) ⟨3189, by rfl⟩ (by norm_num))
theorem R34025 : Reach 34025 := rs (se 2 (by rfl) ⟨12759, by rfl⟩) (B 25519 (by norm_num) ⟨12759, by rfl⟩ (by norm_num))
theorem R34029 : Reach 34029 := rs (se 3 (by rfl) ⟨6380, by rfl⟩) (B 12761 (by norm_num) ⟨6380, by rfl⟩ (by norm_num))
theorem R34033 : Reach 34033 := rs (se 2 (by rfl) ⟨12762, by rfl⟩) (B 25525 (by norm_num) ⟨12762, by rfl⟩ (by norm_num))
theorem R34037 : Reach 34037 := rs (se 5 (by rfl) ⟨1595, by rfl⟩) (B 3191 (by norm_num) ⟨1595, by rfl⟩ (by norm_num))
theorem R34041 : Reach 34041 := rs (se 2 (by rfl) ⟨12765, by rfl⟩) (B 25531 (by norm_num) ⟨12765, by rfl⟩ (by norm_num))
theorem R34045 : Reach 34045 := rs (se 3 (by rfl) ⟨6383, by rfl⟩) (B 12767 (by norm_num) ⟨6383, by rfl⟩ (by norm_num))
theorem R34049 : Reach 34049 := rs (se 2 (by rfl) ⟨12768, by rfl⟩) (B 25537 (by norm_num) ⟨12768, by rfl⟩ (by norm_num))
theorem R165125 : Reach 165125 := rs (se 4 (by rfl) ⟨15480, by rfl⟩) (B 30961 (by norm_num) ⟨15480, by rfl⟩ (by norm_num))
theorem R34053 : Reach 34053 := rs (se 4 (by rfl) ⟨3192, by rfl⟩) (B 6385 (by norm_num) ⟨3192, by rfl⟩ (by norm_num))
theorem R99589 : Reach 99589 := rs (se 4 (by rfl) ⟨9336, by rfl⟩) (B 18673 (by norm_num) ⟨9336, by rfl⟩ (by norm_num))
theorem R34057 : Reach 34057 := rs (se 2 (by rfl) ⟨12771, by rfl⟩) (B 25543 (by norm_num) ⟨12771, by rfl⟩ (by norm_num))
theorem R34061 : Reach 34061 := rs (se 3 (by rfl) ⟨6386, by rfl⟩) (B 12773 (by norm_num) ⟨6386, by rfl⟩ (by norm_num))
theorem R34065 : Reach 34065 := rs (se 2 (by rfl) ⟨12774, by rfl⟩) (B 25549 (by norm_num) ⟨12774, by rfl⟩ (by norm_num))
theorem R34069 : Reach 34069 := rs (se 6 (by rfl) ⟨798, by rfl⟩) (B 1597 (by norm_num) ⟨798, by rfl⟩ (by norm_num))
theorem R34073 : Reach 34073 := rs (se 2 (by rfl) ⟨12777, by rfl⟩) (B 25555 (by norm_num) ⟨12777, by rfl⟩ (by norm_num))
theorem R34077 : Reach 34077 := rs (se 3 (by rfl) ⟨6389, by rfl⟩) (B 12779 (by norm_num) ⟨6389, by rfl⟩ (by norm_num))
theorem R34081 : Reach 34081 := rs (se 2 (by rfl) ⟨12780, by rfl⟩) (B 25561 (by norm_num) ⟨12780, by rfl⟩ (by norm_num))
theorem R34085 : Reach 34085 := rs (se 4 (by rfl) ⟨3195, by rfl⟩) (B 6391 (by norm_num) ⟨3195, by rfl⟩ (by norm_num))
theorem R34089 : Reach 34089 := rs (se 2 (by rfl) ⟨12783, by rfl⟩) (B 25567 (by norm_num) ⟨12783, by rfl⟩ (by norm_num))
theorem R34093 : Reach 34093 := rs (se 3 (by rfl) ⟨6392, by rfl⟩) (B 12785 (by norm_num) ⟨6392, by rfl⟩ (by norm_num))
theorem R34097 : Reach 34097 := rs (se 2 (by rfl) ⟨12786, by rfl⟩) (B 25573 (by norm_num) ⟨12786, by rfl⟩ (by norm_num))
theorem R34101 : Reach 34101 := rs (se 5 (by rfl) ⟨1598, by rfl⟩) (B 3197 (by norm_num) ⟨1598, by rfl⟩ (by norm_num))
theorem R34105 : Reach 34105 := rs (se 2 (by rfl) ⟨12789, by rfl⟩) (B 25579 (by norm_num) ⟨12789, by rfl⟩ (by norm_num))
theorem R34109 : Reach 34109 := rs (se 3 (by rfl) ⟨6395, by rfl⟩) (B 12791 (by norm_num) ⟨6395, by rfl⟩ (by norm_num))
theorem R34113 : Reach 34113 := rs (se 2 (by rfl) ⟨12792, by rfl⟩) (B 25585 (by norm_num) ⟨12792, by rfl⟩ (by norm_num))
theorem R34117 : Reach 34117 := rs (se 4 (by rfl) ⟨3198, by rfl⟩) (B 6397 (by norm_num) ⟨3198, by rfl⟩ (by norm_num))
theorem R34121 : Reach 34121 := rs (se 2 (by rfl) ⟨12795, by rfl⟩) (B 25591 (by norm_num) ⟨12795, by rfl⟩ (by norm_num))
theorem R34125 : Reach 34125 := rs (se 3 (by rfl) ⟨6398, by rfl⟩) (B 12797 (by norm_num) ⟨6398, by rfl⟩ (by norm_num))
theorem R34129 : Reach 34129 := rs (se 2 (by rfl) ⟨12798, by rfl⟩) (B 25597 (by norm_num) ⟨12798, by rfl⟩ (by norm_num))
theorem R66901 : Reach 66901 := rs (se 12 (by rfl) ⟨24, by rfl⟩) (B 49 (by norm_num) ⟨24, by rfl⟩ (by norm_num))
theorem R34133 : Reach 34133 := rs (se 12 (by rfl) ⟨12, by rfl⟩) (B 25 (by norm_num) ⟨12, by rfl⟩ (by norm_num))
theorem R34137 : Reach 34137 := rs (se 2 (by rfl) ⟨12801, by rfl⟩) (B 25603 (by norm_num) ⟨12801, by rfl⟩ (by norm_num))
theorem R34141 : Reach 34141 := rs (se 3 (by rfl) ⟨6401, by rfl⟩) (B 12803 (by norm_num) ⟨6401, by rfl⟩ (by norm_num))
theorem R34145 : Reach 34145 := rs (se 2 (by rfl) ⟨12804, by rfl⟩) (B 25609 (by norm_num) ⟨12804, by rfl⟩ (by norm_num))
theorem R34149 : Reach 34149 := rs (se 4 (by rfl) ⟨3201, by rfl⟩) (B 6403 (by norm_num) ⟨3201, by rfl⟩ (by norm_num))
theorem R34153 : Reach 34153 := rs (se 2 (by rfl) ⟨12807, by rfl⟩) (B 25615 (by norm_num) ⟨12807, by rfl⟩ (by norm_num))
theorem R34157 : Reach 34157 := rs (se 3 (by rfl) ⟨6404, by rfl⟩) (B 12809 (by norm_num) ⟨6404, by rfl⟩ (by norm_num))
theorem R34161 : Reach 34161 := rs (se 2 (by rfl) ⟨12810, by rfl⟩) (B 25621 (by norm_num) ⟨12810, by rfl⟩ (by norm_num))
theorem R34165 : Reach 34165 := rs (se 5 (by rfl) ⟨1601, by rfl⟩) (B 3203 (by norm_num) ⟨1601, by rfl⟩ (by norm_num))
theorem R34169 : Reach 34169 := rs (se 2 (by rfl) ⟨12813, by rfl⟩) (B 25627 (by norm_num) ⟨12813, by rfl⟩ (by norm_num))
theorem R34173 : Reach 34173 := rs (se 3 (by rfl) ⟨6407, by rfl⟩) (B 12815 (by norm_num) ⟨6407, by rfl⟩ (by norm_num))
theorem R34177 : Reach 34177 := rs (se 2 (by rfl) ⟨12816, by rfl⟩) (B 25633 (by norm_num) ⟨12816, by rfl⟩ (by norm_num))
theorem R34181 : Reach 34181 := rs (se 4 (by rfl) ⟨3204, by rfl⟩) (B 6409 (by norm_num) ⟨3204, by rfl⟩ (by norm_num))
theorem R34185 : Reach 34185 := rs (se 2 (by rfl) ⟨12819, by rfl⟩) (B 25639 (by norm_num) ⟨12819, by rfl⟩ (by norm_num))
theorem R34189 : Reach 34189 := rs (se 3 (by rfl) ⟨6410, by rfl⟩) (B 12821 (by norm_num) ⟨6410, by rfl⟩ (by norm_num))
theorem R34193 : Reach 34193 := rs (se 2 (by rfl) ⟨12822, by rfl⟩) (B 25645 (by norm_num) ⟨12822, by rfl⟩ (by norm_num))
theorem R99733 : Reach 99733 := rs (se 6 (by rfl) ⟨2337, by rfl⟩) (B 4675 (by norm_num) ⟨2337, by rfl⟩ (by norm_num))
theorem R34197 : Reach 34197 := rs (se 6 (by rfl) ⟨801, by rfl⟩) (B 1603 (by norm_num) ⟨801, by rfl⟩ (by norm_num))
theorem R34201 : Reach 34201 := rs (se 2 (by rfl) ⟨12825, by rfl⟩) (B 25651 (by norm_num) ⟨12825, by rfl⟩ (by norm_num))
theorem R34205 : Reach 34205 := rs (se 3 (by rfl) ⟨6413, by rfl⟩) (B 12827 (by norm_num) ⟨6413, by rfl⟩ (by norm_num))
theorem R34209 : Reach 34209 := rs (se 2 (by rfl) ⟨12828, by rfl⟩) (B 25657 (by norm_num) ⟨12828, by rfl⟩ (by norm_num))
theorem R34213 : Reach 34213 := rs (se 4 (by rfl) ⟨3207, by rfl⟩) (B 6415 (by norm_num) ⟨3207, by rfl⟩ (by norm_num))
theorem R34217 : Reach 34217 := rs (se 2 (by rfl) ⟨12831, by rfl⟩) (B 25663 (by norm_num) ⟨12831, by rfl⟩ (by norm_num))
theorem R34221 : Reach 34221 := rs (se 3 (by rfl) ⟨6416, by rfl⟩) (B 12833 (by norm_num) ⟨6416, by rfl⟩ (by norm_num))
theorem R34225 : Reach 34225 := rs (se 2 (by rfl) ⟨12834, by rfl⟩) (B 25669 (by norm_num) ⟨12834, by rfl⟩ (by norm_num))
theorem R34229 : Reach 34229 := rs (se 5 (by rfl) ⟨1604, by rfl⟩) (B 3209 (by norm_num) ⟨1604, by rfl⟩ (by norm_num))
theorem R34233 : Reach 34233 := rs (se 2 (by rfl) ⟨12837, by rfl⟩) (B 25675 (by norm_num) ⟨12837, by rfl⟩ (by norm_num))
theorem R34237 : Reach 34237 := rs (se 3 (by rfl) ⟨6419, by rfl⟩) (B 12839 (by norm_num) ⟨6419, by rfl⟩ (by norm_num))
theorem R34241 : Reach 34241 := rs (se 2 (by rfl) ⟨12840, by rfl⟩) (B 25681 (by norm_num) ⟨12840, by rfl⟩ (by norm_num))
theorem R34245 : Reach 34245 := rs (se 4 (by rfl) ⟨3210, by rfl⟩) (B 6421 (by norm_num) ⟨3210, by rfl⟩ (by norm_num))
theorem R34249 : Reach 34249 := rs (se 2 (by rfl) ⟨12843, by rfl⟩) (B 25687 (by norm_num) ⟨12843, by rfl⟩ (by norm_num))
theorem R34253 : Reach 34253 := rs (se 3 (by rfl) ⟨6422, by rfl⟩) (B 12845 (by norm_num) ⟨6422, by rfl⟩ (by norm_num))
theorem R34257 : Reach 34257 := rs (se 2 (by rfl) ⟨12846, by rfl⟩) (B 25693 (by norm_num) ⟨12846, by rfl⟩ (by norm_num))
theorem R34261 : Reach 34261 := rs (se 7 (by rfl) ⟨401, by rfl⟩) (B 803 (by norm_num) ⟨401, by rfl⟩ (by norm_num))
theorem R34265 : Reach 34265 := rs (se 2 (by rfl) ⟨12849, by rfl⟩) (B 25699 (by norm_num) ⟨12849, by rfl⟩ (by norm_num))
theorem R34269 : Reach 34269 := rs (se 3 (by rfl) ⟨6425, by rfl⟩) (B 12851 (by norm_num) ⟨6425, by rfl⟩ (by norm_num))
theorem R34273 : Reach 34273 := rs (se 2 (by rfl) ⟨12852, by rfl⟩) (B 25705 (by norm_num) ⟨12852, by rfl⟩ (by norm_num))
theorem R34277 : Reach 34277 := rs (se 4 (by rfl) ⟨3213, by rfl⟩) (B 6427 (by norm_num) ⟨3213, by rfl⟩ (by norm_num))
theorem R34281 : Reach 34281 := rs (se 2 (by rfl) ⟨12855, by rfl⟩) (B 25711 (by norm_num) ⟨12855, by rfl⟩ (by norm_num))
theorem R34285 : Reach 34285 := rs (se 3 (by rfl) ⟨6428, by rfl⟩) (B 12857 (by norm_num) ⟨6428, by rfl⟩ (by norm_num))
theorem R34289 : Reach 34289 := rs (se 2 (by rfl) ⟨12858, by rfl⟩) (B 25717 (by norm_num) ⟨12858, by rfl⟩ (by norm_num))
theorem R34293 : Reach 34293 := rs (se 5 (by rfl) ⟨1607, by rfl⟩) (B 3215 (by norm_num) ⟨1607, by rfl⟩ (by norm_num))
theorem R34297 : Reach 34297 := rs (se 2 (by rfl) ⟨12861, by rfl⟩) (B 25723 (by norm_num) ⟨12861, by rfl⟩ (by norm_num))
theorem R34301 : Reach 34301 := rs (se 3 (by rfl) ⟨6431, by rfl⟩) (B 12863 (by norm_num) ⟨6431, by rfl⟩ (by norm_num))
theorem R34305 : Reach 34305 := rs (se 2 (by rfl) ⟨12864, by rfl⟩) (B 25729 (by norm_num) ⟨12864, by rfl⟩ (by norm_num))
theorem R34309 : Reach 34309 := rs (se 4 (by rfl) ⟨3216, by rfl⟩) (B 6433 (by norm_num) ⟨3216, by rfl⟩ (by norm_num))
theorem R34313 : Reach 34313 := rs (se 2 (by rfl) ⟨12867, by rfl⟩) (B 25735 (by norm_num) ⟨12867, by rfl⟩ (by norm_num))
theorem R34317 : Reach 34317 := rs (se 3 (by rfl) ⟨6434, by rfl⟩) (B 12869 (by norm_num) ⟨6434, by rfl⟩ (by norm_num))
theorem R34321 : Reach 34321 := rs (se 2 (by rfl) ⟨12870, by rfl⟩) (B 25741 (by norm_num) ⟨12870, by rfl⟩ (by norm_num))
theorem R34325 : Reach 34325 := rs (se 6 (by rfl) ⟨804, by rfl⟩) (B 1609 (by norm_num) ⟨804, by rfl⟩ (by norm_num))
theorem R34329 : Reach 34329 := rs (se 2 (by rfl) ⟨12873, by rfl⟩) (B 25747 (by norm_num) ⟨12873, by rfl⟩ (by norm_num))
theorem R34333 : Reach 34333 := rs (se 3 (by rfl) ⟨6437, by rfl⟩) (B 12875 (by norm_num) ⟨6437, by rfl⟩ (by norm_num))
theorem R34337 : Reach 34337 := rs (se 2 (by rfl) ⟨12876, by rfl⟩) (B 25753 (by norm_num) ⟨12876, by rfl⟩ (by norm_num))
theorem R34341 : Reach 34341 := rs (se 4 (by rfl) ⟨3219, by rfl⟩) (B 6439 (by norm_num) ⟨3219, by rfl⟩ (by norm_num))
theorem R34345 : Reach 34345 := rs (se 2 (by rfl) ⟨12879, by rfl⟩) (B 25759 (by norm_num) ⟨12879, by rfl⟩ (by norm_num))
theorem R34349 : Reach 34349 := rs (se 3 (by rfl) ⟨6440, by rfl⟩) (B 12881 (by norm_num) ⟨6440, by rfl⟩ (by norm_num))
theorem R34353 : Reach 34353 := rs (se 2 (by rfl) ⟨12882, by rfl⟩) (B 25765 (by norm_num) ⟨12882, by rfl⟩ (by norm_num))
theorem R34357 : Reach 34357 := rs (se 5 (by rfl) ⟨1610, by rfl⟩) (B 3221 (by norm_num) ⟨1610, by rfl⟩ (by norm_num))
theorem R198197 : Reach 198197 := rs (se 5 (by rfl) ⟨9290, by rfl⟩) (B 18581 (by norm_num) ⟨9290, by rfl⟩ (by norm_num))
theorem R34361 : Reach 34361 := rs (se 2 (by rfl) ⟨12885, by rfl⟩) (B 25771 (by norm_num) ⟨12885, by rfl⟩ (by norm_num))
theorem R34365 : Reach 34365 := rs (se 3 (by rfl) ⟨6443, by rfl⟩) (B 12887 (by norm_num) ⟨6443, by rfl⟩ (by norm_num))
theorem R34369 : Reach 34369 := rs (se 2 (by rfl) ⟨12888, by rfl⟩) (B 25777 (by norm_num) ⟨12888, by rfl⟩ (by norm_num))
theorem R34373 : Reach 34373 := rs (se 4 (by rfl) ⟨3222, by rfl⟩) (B 6445 (by norm_num) ⟨3222, by rfl⟩ (by norm_num))
theorem R34377 : Reach 34377 := rs (se 2 (by rfl) ⟨12891, by rfl⟩) (B 25783 (by norm_num) ⟨12891, by rfl⟩ (by norm_num))
theorem R34381 : Reach 34381 := rs (se 3 (by rfl) ⟨6446, by rfl⟩) (B 12893 (by norm_num) ⟨6446, by rfl⟩ (by norm_num))
theorem R34385 : Reach 34385 := rs (se 2 (by rfl) ⟨12894, by rfl⟩) (B 25789 (by norm_num) ⟨12894, by rfl⟩ (by norm_num))
theorem R34389 : Reach 34389 := rs (se 8 (by rfl) ⟨201, by rfl⟩) (B 403 (by norm_num) ⟨201, by rfl⟩ (by norm_num))
theorem R34393 : Reach 34393 := rs (se 2 (by rfl) ⟨12897, by rfl⟩) (B 25795 (by norm_num) ⟨12897, by rfl⟩ (by norm_num))
theorem R34397 : Reach 34397 := rs (se 3 (by rfl) ⟨6449, by rfl⟩) (B 12899 (by norm_num) ⟨6449, by rfl⟩ (by norm_num))
theorem R34401 : Reach 34401 := rs (se 2 (by rfl) ⟨12900, by rfl⟩) (B 25801 (by norm_num) ⟨12900, by rfl⟩ (by norm_num))
theorem R34405 : Reach 34405 := rs (se 4 (by rfl) ⟨3225, by rfl⟩) (B 6451 (by norm_num) ⟨3225, by rfl⟩ (by norm_num))
theorem R34409 : Reach 34409 := rs (se 2 (by rfl) ⟨12903, by rfl⟩) (B 25807 (by norm_num) ⟨12903, by rfl⟩ (by norm_num))
theorem R34413 : Reach 34413 := rs (se 3 (by rfl) ⟨6452, by rfl⟩) (B 12905 (by norm_num) ⟨6452, by rfl⟩ (by norm_num))
theorem R34417 : Reach 34417 := rs (se 2 (by rfl) ⟨12906, by rfl⟩) (B 25813 (by norm_num) ⟨12906, by rfl⟩ (by norm_num))
theorem R34421 : Reach 34421 := rs (se 5 (by rfl) ⟨1613, by rfl⟩) (B 3227 (by norm_num) ⟨1613, by rfl⟩ (by norm_num))
theorem R34425 : Reach 34425 := rs (se 2 (by rfl) ⟨12909, by rfl⟩) (B 25819 (by norm_num) ⟨12909, by rfl⟩ (by norm_num))
theorem R34429 : Reach 34429 := rs (se 3 (by rfl) ⟨6455, by rfl⟩) (B 12911 (by norm_num) ⟨6455, by rfl⟩ (by norm_num))
theorem R34433 : Reach 34433 := rs (se 2 (by rfl) ⟨12912, by rfl⟩) (B 25825 (by norm_num) ⟨12912, by rfl⟩ (by norm_num))
theorem R34437 : Reach 34437 := rs (se 4 (by rfl) ⟨3228, by rfl⟩) (B 6457 (by norm_num) ⟨3228, by rfl⟩ (by norm_num))
theorem R34441 : Reach 34441 := rs (se 2 (by rfl) ⟨12915, by rfl⟩) (B 25831 (by norm_num) ⟨12915, by rfl⟩ (by norm_num))
theorem R34445 : Reach 34445 := rs (se 3 (by rfl) ⟨6458, by rfl⟩) (B 12917 (by norm_num) ⟨6458, by rfl⟩ (by norm_num))
theorem R34449 : Reach 34449 := rs (se 2 (by rfl) ⟨12918, by rfl⟩) (B 25837 (by norm_num) ⟨12918, by rfl⟩ (by norm_num))
theorem R34453 : Reach 34453 := rs (se 6 (by rfl) ⟨807, by rfl⟩) (B 1615 (by norm_num) ⟨807, by rfl⟩ (by norm_num))
theorem R34457 : Reach 34457 := rs (se 2 (by rfl) ⟨12921, by rfl⟩) (B 25843 (by norm_num) ⟨12921, by rfl⟩ (by norm_num))
theorem R34461 : Reach 34461 := rs (se 3 (by rfl) ⟨6461, by rfl⟩) (B 12923 (by norm_num) ⟨6461, by rfl⟩ (by norm_num))
theorem R34465 : Reach 34465 := rs (se 2 (by rfl) ⟨12924, by rfl⟩) (B 25849 (by norm_num) ⟨12924, by rfl⟩ (by norm_num))
theorem R34469 : Reach 34469 := rs (se 4 (by rfl) ⟨3231, by rfl⟩) (B 6463 (by norm_num) ⟨3231, by rfl⟩ (by norm_num))
theorem R34473 : Reach 34473 := rs (se 2 (by rfl) ⟨12927, by rfl⟩) (B 25855 (by norm_num) ⟨12927, by rfl⟩ (by norm_num))
theorem R34477 : Reach 34477 := rs (se 3 (by rfl) ⟨6464, by rfl⟩) (B 12929 (by norm_num) ⟨6464, by rfl⟩ (by norm_num))
theorem R34481 : Reach 34481 := rs (se 2 (by rfl) ⟨12930, by rfl⟩) (B 25861 (by norm_num) ⟨12930, by rfl⟩ (by norm_num))
theorem R34485 : Reach 34485 := rs (se 5 (by rfl) ⟨1616, by rfl⟩) (B 3233 (by norm_num) ⟨1616, by rfl⟩ (by norm_num))
theorem R34489 : Reach 34489 := rs (se 2 (by rfl) ⟨12933, by rfl⟩) (B 25867 (by norm_num) ⟨12933, by rfl⟩ (by norm_num))
theorem R34493 : Reach 34493 := rs (se 3 (by rfl) ⟨6467, by rfl⟩) (B 12935 (by norm_num) ⟨6467, by rfl⟩ (by norm_num))
theorem R34497 : Reach 34497 := rs (se 2 (by rfl) ⟨12936, by rfl⟩) (B 25873 (by norm_num) ⟨12936, by rfl⟩ (by norm_num))
theorem R34501 : Reach 34501 := rs (se 4 (by rfl) ⟨3234, by rfl⟩) (B 6469 (by norm_num) ⟨3234, by rfl⟩ (by norm_num))
theorem R34505 : Reach 34505 := rs (se 2 (by rfl) ⟨12939, by rfl⟩) (B 25879 (by norm_num) ⟨12939, by rfl⟩ (by norm_num))
theorem R34509 : Reach 34509 := rs (se 3 (by rfl) ⟨6470, by rfl⟩) (B 12941 (by norm_num) ⟨6470, by rfl⟩ (by norm_num))
theorem R34513 : Reach 34513 := rs (se 2 (by rfl) ⟨12942, by rfl⟩) (B 25885 (by norm_num) ⟨12942, by rfl⟩ (by norm_num))
theorem R34517 : Reach 34517 := rs (se 7 (by rfl) ⟨404, by rfl⟩) (B 809 (by norm_num) ⟨404, by rfl⟩ (by norm_num))
theorem R34521 : Reach 34521 := rs (se 2 (by rfl) ⟨12945, by rfl⟩) (B 25891 (by norm_num) ⟨12945, by rfl⟩ (by norm_num))
theorem R34525 : Reach 34525 := rs (se 3 (by rfl) ⟨6473, by rfl⟩) (B 12947 (by norm_num) ⟨6473, by rfl⟩ (by norm_num))
theorem R34529 : Reach 34529 := rs (se 2 (by rfl) ⟨12948, by rfl⟩) (B 25897 (by norm_num) ⟨12948, by rfl⟩ (by norm_num))
theorem R34533 : Reach 34533 := rs (se 4 (by rfl) ⟨3237, by rfl⟩) (B 6475 (by norm_num) ⟨3237, by rfl⟩ (by norm_num))
theorem R34537 : Reach 34537 := rs (se 2 (by rfl) ⟨12951, by rfl⟩) (B 25903 (by norm_num) ⟨12951, by rfl⟩ (by norm_num))
theorem R34541 : Reach 34541 := rs (se 3 (by rfl) ⟨6476, by rfl⟩) (B 12953 (by norm_num) ⟨6476, by rfl⟩ (by norm_num))
theorem R34545 : Reach 34545 := rs (se 2 (by rfl) ⟨12954, by rfl⟩) (B 25909 (by norm_num) ⟨12954, by rfl⟩ (by norm_num))
theorem R34549 : Reach 34549 := rs (se 5 (by rfl) ⟨1619, by rfl⟩) (B 3239 (by norm_num) ⟨1619, by rfl⟩ (by norm_num))
theorem R34553 : Reach 34553 := rs (se 2 (by rfl) ⟨12957, by rfl⟩) (B 25915 (by norm_num) ⟨12957, by rfl⟩ (by norm_num))
theorem R34557 : Reach 34557 := rs (se 3 (by rfl) ⟨6479, by rfl⟩) (B 12959 (by norm_num) ⟨6479, by rfl⟩ (by norm_num))
theorem R34561 : Reach 34561 := rs (se 2 (by rfl) ⟨12960, by rfl⟩) (B 25921 (by norm_num) ⟨12960, by rfl⟩ (by norm_num))
theorem R34565 : Reach 34565 := rs (se 4 (by rfl) ⟨3240, by rfl⟩) (B 6481 (by norm_num) ⟨3240, by rfl⟩ (by norm_num))
theorem R34569 : Reach 34569 := rs (se 2 (by rfl) ⟨12963, by rfl⟩) (B 25927 (by norm_num) ⟨12963, by rfl⟩ (by norm_num))
theorem R34573 : Reach 34573 := rs (se 3 (by rfl) ⟨6482, by rfl⟩) (B 12965 (by norm_num) ⟨6482, by rfl⟩ (by norm_num))
theorem R34577 : Reach 34577 := rs (se 2 (by rfl) ⟨12966, by rfl⟩) (B 25933 (by norm_num) ⟨12966, by rfl⟩ (by norm_num))
theorem R34581 : Reach 34581 := rs (se 6 (by rfl) ⟨810, by rfl⟩) (B 1621 (by norm_num) ⟨810, by rfl⟩ (by norm_num))
theorem R34585 : Reach 34585 := rs (se 2 (by rfl) ⟨12969, by rfl⟩) (B 25939 (by norm_num) ⟨12969, by rfl⟩ (by norm_num))
theorem R34589 : Reach 34589 := rs (se 3 (by rfl) ⟨6485, by rfl⟩) (B 12971 (by norm_num) ⟨6485, by rfl⟩ (by norm_num))
theorem R34593 : Reach 34593 := rs (se 2 (by rfl) ⟨12972, by rfl⟩) (B 25945 (by norm_num) ⟨12972, by rfl⟩ (by norm_num))
theorem R100133 : Reach 100133 := rs (se 4 (by rfl) ⟨9387, by rfl⟩) (B 18775 (by norm_num) ⟨9387, by rfl⟩ (by norm_num))
theorem R34597 : Reach 34597 := rs (se 4 (by rfl) ⟨3243, by rfl⟩) (B 6487 (by norm_num) ⟨3243, by rfl⟩ (by norm_num))
theorem R34601 : Reach 34601 := rs (se 2 (by rfl) ⟨12975, by rfl⟩) (B 25951 (by norm_num) ⟨12975, by rfl⟩ (by norm_num))
theorem R34605 : Reach 34605 := rs (se 3 (by rfl) ⟨6488, by rfl⟩) (B 12977 (by norm_num) ⟨6488, by rfl⟩ (by norm_num))
theorem R34609 : Reach 34609 := rs (se 2 (by rfl) ⟨12978, by rfl⟩) (B 25957 (by norm_num) ⟨12978, by rfl⟩ (by norm_num))
theorem R34613 : Reach 34613 := rs (se 5 (by rfl) ⟨1622, by rfl⟩) (B 3245 (by norm_num) ⟨1622, by rfl⟩ (by norm_num))
theorem R34617 : Reach 34617 := rs (se 2 (by rfl) ⟨12981, by rfl⟩) (B 25963 (by norm_num) ⟨12981, by rfl⟩ (by norm_num))
theorem R34621 : Reach 34621 := rs (se 3 (by rfl) ⟨6491, by rfl⟩) (B 12983 (by norm_num) ⟨6491, by rfl⟩ (by norm_num))
theorem R34625 : Reach 34625 := rs (se 2 (by rfl) ⟨12984, by rfl⟩) (B 25969 (by norm_num) ⟨12984, by rfl⟩ (by norm_num))
theorem R34629 : Reach 34629 := rs (se 4 (by rfl) ⟨3246, by rfl⟩) (B 6493 (by norm_num) ⟨3246, by rfl⟩ (by norm_num))
theorem R34633 : Reach 34633 := rs (se 2 (by rfl) ⟨12987, by rfl⟩) (B 25975 (by norm_num) ⟨12987, by rfl⟩ (by norm_num))
theorem R67405 : Reach 67405 := rs (se 3 (by rfl) ⟨12638, by rfl⟩) (B 25277 (by norm_num) ⟨12638, by rfl⟩ (by norm_num))
theorem R34637 : Reach 34637 := rs (se 3 (by rfl) ⟨6494, by rfl⟩) (B 12989 (by norm_num) ⟨6494, by rfl⟩ (by norm_num))
theorem R34641 : Reach 34641 := rs (se 2 (by rfl) ⟨12990, by rfl⟩) (B 25981 (by norm_num) ⟨12990, by rfl⟩ (by norm_num))
theorem R132949 : Reach 132949 := rs (se 9 (by rfl) ⟨389, by rfl⟩) (B 779 (by norm_num) ⟨389, by rfl⟩ (by norm_num))
theorem R34645 : Reach 34645 := rs (se 9 (by rfl) ⟨101, by rfl⟩) (B 203 (by norm_num) ⟨101, by rfl⟩ (by norm_num))
theorem R34649 : Reach 34649 := rs (se 2 (by rfl) ⟨12993, by rfl⟩) (B 25987 (by norm_num) ⟨12993, by rfl⟩ (by norm_num))
theorem R34653 : Reach 34653 := rs (se 3 (by rfl) ⟨6497, by rfl⟩) (B 12995 (by norm_num) ⟨6497, by rfl⟩ (by norm_num))
theorem R34657 : Reach 34657 := rs (se 2 (by rfl) ⟨12996, by rfl⟩) (B 25993 (by norm_num) ⟨12996, by rfl⟩ (by norm_num))
theorem R34661 : Reach 34661 := rs (se 4 (by rfl) ⟨3249, by rfl⟩) (B 6499 (by norm_num) ⟨3249, by rfl⟩ (by norm_num))
theorem R34665 : Reach 34665 := rs (se 2 (by rfl) ⟨12999, by rfl⟩) (B 25999 (by norm_num) ⟨12999, by rfl⟩ (by norm_num))
theorem R34669 : Reach 34669 := rs (se 3 (by rfl) ⟨6500, by rfl⟩) (B 13001 (by norm_num) ⟨6500, by rfl⟩ (by norm_num))
theorem R34673 : Reach 34673 := rs (se 2 (by rfl) ⟨13002, by rfl⟩) (B 26005 (by norm_num) ⟨13002, by rfl⟩ (by norm_num))
theorem R34677 : Reach 34677 := rs (se 5 (by rfl) ⟨1625, by rfl⟩) (B 3251 (by norm_num) ⟨1625, by rfl⟩ (by norm_num))
theorem R34681 : Reach 34681 := rs (se 2 (by rfl) ⟨13005, by rfl⟩) (B 26011 (by norm_num) ⟨13005, by rfl⟩ (by norm_num))
theorem R34685 : Reach 34685 := rs (se 3 (by rfl) ⟨6503, by rfl⟩) (B 13007 (by norm_num) ⟨6503, by rfl⟩ (by norm_num))
theorem R34689 : Reach 34689 := rs (se 2 (by rfl) ⟨13008, by rfl⟩) (B 26017 (by norm_num) ⟨13008, by rfl⟩ (by norm_num))
theorem R132997 : Reach 132997 := rs (se 4 (by rfl) ⟨12468, by rfl⟩) (B 24937 (by norm_num) ⟨12468, by rfl⟩ (by norm_num))
theorem R34693 : Reach 34693 := rs (se 4 (by rfl) ⟨3252, by rfl⟩) (B 6505 (by norm_num) ⟨3252, by rfl⟩ (by norm_num))
theorem R34697 : Reach 34697 := rs (se 2 (by rfl) ⟨13011, by rfl⟩) (B 26023 (by norm_num) ⟨13011, by rfl⟩ (by norm_num))
theorem R34701 : Reach 34701 := rs (se 3 (by rfl) ⟨6506, by rfl⟩) (B 13013 (by norm_num) ⟨6506, by rfl⟩ (by norm_num))
theorem R34705 : Reach 34705 := rs (se 2 (by rfl) ⟨13014, by rfl⟩) (B 26029 (by norm_num) ⟨13014, by rfl⟩ (by norm_num))
theorem R34709 : Reach 34709 := rs (se 6 (by rfl) ⟨813, by rfl⟩) (B 1627 (by norm_num) ⟨813, by rfl⟩ (by norm_num))
theorem R34713 : Reach 34713 := rs (se 2 (by rfl) ⟨13017, by rfl⟩) (B 26035 (by norm_num) ⟨13017, by rfl⟩ (by norm_num))
theorem R34717 : Reach 34717 := rs (se 3 (by rfl) ⟨6509, by rfl⟩) (B 13019 (by norm_num) ⟨6509, by rfl⟩ (by norm_num))
theorem R34721 : Reach 34721 := rs (se 2 (by rfl) ⟨13020, by rfl⟩) (B 26041 (by norm_num) ⟨13020, by rfl⟩ (by norm_num))
theorem R34725 : Reach 34725 := rs (se 4 (by rfl) ⟨3255, by rfl⟩) (B 6511 (by norm_num) ⟨3255, by rfl⟩ (by norm_num))
theorem R34729 : Reach 34729 := rs (se 2 (by rfl) ⟨13023, by rfl⟩) (B 26047 (by norm_num) ⟨13023, by rfl⟩ (by norm_num))
theorem R34733 : Reach 34733 := rs (se 3 (by rfl) ⟨6512, by rfl⟩) (B 13025 (by norm_num) ⟨6512, by rfl⟩ (by norm_num))
theorem R34737 : Reach 34737 := rs (se 2 (by rfl) ⟨13026, by rfl⟩) (B 26053 (by norm_num) ⟨13026, by rfl⟩ (by norm_num))
theorem R34741 : Reach 34741 := rs (se 5 (by rfl) ⟨1628, by rfl⟩) (B 3257 (by norm_num) ⟨1628, by rfl⟩ (by norm_num))
theorem R296885 : Reach 296885 := rs (se 5 (by rfl) ⟨13916, by rfl⟩) (B 27833 (by norm_num) ⟨13916, by rfl⟩ (by norm_num))
theorem R34745 : Reach 34745 := rs (se 2 (by rfl) ⟨13029, by rfl⟩) (B 26059 (by norm_num) ⟨13029, by rfl⟩ (by norm_num))
theorem R34749 : Reach 34749 := rs (se 3 (by rfl) ⟨6515, by rfl⟩) (B 13031 (by norm_num) ⟨6515, by rfl⟩ (by norm_num))
theorem R34753 : Reach 34753 := rs (se 2 (by rfl) ⟨13032, by rfl⟩) (B 26065 (by norm_num) ⟨13032, by rfl⟩ (by norm_num))
theorem R34757 : Reach 34757 := rs (se 4 (by rfl) ⟨3258, by rfl⟩) (B 6517 (by norm_num) ⟨3258, by rfl⟩ (by norm_num))
theorem R34761 : Reach 34761 := rs (se 2 (by rfl) ⟨13035, by rfl⟩) (B 26071 (by norm_num) ⟨13035, by rfl⟩ (by norm_num))
theorem R34765 : Reach 34765 := rs (se 3 (by rfl) ⟨6518, by rfl⟩) (B 13037 (by norm_num) ⟨6518, by rfl⟩ (by norm_num))
theorem R34769 : Reach 34769 := rs (se 2 (by rfl) ⟨13038, by rfl⟩) (B 26077 (by norm_num) ⟨13038, by rfl⟩ (by norm_num))
theorem R755669 : Reach 755669 := rs (se 7 (by rfl) ⟨8855, by rfl⟩) (B 17711 (by norm_num) ⟨8855, by rfl⟩ (by norm_num))
theorem R34773 : Reach 34773 := rs (se 7 (by rfl) ⟨407, by rfl⟩) (B 815 (by norm_num) ⟨407, by rfl⟩ (by norm_num))
theorem R34777 : Reach 34777 := rs (se 2 (by rfl) ⟨13041, by rfl⟩) (B 26083 (by norm_num) ⟨13041, by rfl⟩ (by norm_num))
theorem R34781 : Reach 34781 := rs (se 3 (by rfl) ⟨6521, by rfl⟩) (B 13043 (by norm_num) ⟨6521, by rfl⟩ (by norm_num))
theorem R34785 : Reach 34785 := rs (se 2 (by rfl) ⟨13044, by rfl⟩) (B 26089 (by norm_num) ⟨13044, by rfl⟩ (by norm_num))
theorem R34789 : Reach 34789 := rs (se 4 (by rfl) ⟨3261, by rfl⟩) (B 6523 (by norm_num) ⟨3261, by rfl⟩ (by norm_num))
theorem R34793 : Reach 34793 := rs (se 2 (by rfl) ⟨13047, by rfl⟩) (B 26095 (by norm_num) ⟨13047, by rfl⟩ (by norm_num))
theorem R34797 : Reach 34797 := rs (se 3 (by rfl) ⟨6524, by rfl⟩) (B 13049 (by norm_num) ⟨6524, by rfl⟩ (by norm_num))
theorem R34801 : Reach 34801 := rs (se 2 (by rfl) ⟨13050, by rfl⟩) (B 26101 (by norm_num) ⟨13050, by rfl⟩ (by norm_num))
theorem R34805 : Reach 34805 := rs (se 5 (by rfl) ⟨1631, by rfl⟩) (B 3263 (by norm_num) ⟨1631, by rfl⟩ (by norm_num))
theorem R34809 : Reach 34809 := rs (se 2 (by rfl) ⟨13053, by rfl⟩) (B 26107 (by norm_num) ⟨13053, by rfl⟩ (by norm_num))
theorem R34813 : Reach 34813 := rs (se 3 (by rfl) ⟨6527, by rfl⟩) (B 13055 (by norm_num) ⟨6527, by rfl⟩ (by norm_num))
theorem R34817 : Reach 34817 := rs (se 2 (by rfl) ⟨13056, by rfl⟩) (B 26113 (by norm_num) ⟨13056, by rfl⟩ (by norm_num))
theorem R34821 : Reach 34821 := rs (se 4 (by rfl) ⟨3264, by rfl⟩) (B 6529 (by norm_num) ⟨3264, by rfl⟩ (by norm_num))
theorem R34825 : Reach 34825 := rs (se 2 (by rfl) ⟨13059, by rfl⟩) (B 26119 (by norm_num) ⟨13059, by rfl⟩ (by norm_num))
theorem R34829 : Reach 34829 := rs (se 3 (by rfl) ⟨6530, by rfl⟩) (B 13061 (by norm_num) ⟨6530, by rfl⟩ (by norm_num))
theorem R34833 : Reach 34833 := rs (se 2 (by rfl) ⟨13062, by rfl⟩) (B 26125 (by norm_num) ⟨13062, by rfl⟩ (by norm_num))
theorem R34837 : Reach 34837 := rs (se 6 (by rfl) ⟨816, by rfl⟩) (B 1633 (by norm_num) ⟨816, by rfl⟩ (by norm_num))
theorem R34841 : Reach 34841 := rs (se 2 (by rfl) ⟨13065, by rfl⟩) (B 26131 (by norm_num) ⟨13065, by rfl⟩ (by norm_num))
theorem R34845 : Reach 34845 := rs (se 3 (by rfl) ⟨6533, by rfl⟩) (B 13067 (by norm_num) ⟨6533, by rfl⟩ (by norm_num))
theorem R34849 : Reach 34849 := rs (se 2 (by rfl) ⟨13068, by rfl⟩) (B 26137 (by norm_num) ⟨13068, by rfl⟩ (by norm_num))
theorem R133157 : Reach 133157 := rs (se 4 (by rfl) ⟨12483, by rfl⟩) (B 24967 (by norm_num) ⟨12483, by rfl⟩ (by norm_num))
theorem R34853 : Reach 34853 := rs (se 4 (by rfl) ⟨3267, by rfl⟩) (B 6535 (by norm_num) ⟨3267, by rfl⟩ (by norm_num))
theorem R34857 : Reach 34857 := rs (se 2 (by rfl) ⟨13071, by rfl⟩) (B 26143 (by norm_num) ⟨13071, by rfl⟩ (by norm_num))
theorem R34861 : Reach 34861 := rs (se 3 (by rfl) ⟨6536, by rfl⟩) (B 13073 (by norm_num) ⟨6536, by rfl⟩ (by norm_num))
theorem R34865 : Reach 34865 := rs (se 2 (by rfl) ⟨13074, by rfl⟩) (B 26149 (by norm_num) ⟨13074, by rfl⟩ (by norm_num))
theorem R34869 : Reach 34869 := rs (se 5 (by rfl) ⟨1634, by rfl⟩) (B 3269 (by norm_num) ⟨1634, by rfl⟩ (by norm_num))
theorem R34873 : Reach 34873 := rs (se 2 (by rfl) ⟨13077, by rfl⟩) (B 26155 (by norm_num) ⟨13077, by rfl⟩ (by norm_num))
theorem R34877 : Reach 34877 := rs (se 3 (by rfl) ⟨6539, by rfl⟩) (B 13079 (by norm_num) ⟨6539, by rfl⟩ (by norm_num))
theorem R34881 : Reach 34881 := rs (se 2 (by rfl) ⟨13080, by rfl⟩) (B 26161 (by norm_num) ⟨13080, by rfl⟩ (by norm_num))
theorem R34885 : Reach 34885 := rs (se 4 (by rfl) ⟨3270, by rfl⟩) (B 6541 (by norm_num) ⟨3270, by rfl⟩ (by norm_num))
theorem R34889 : Reach 34889 := rs (se 2 (by rfl) ⟨13083, by rfl⟩) (B 26167 (by norm_num) ⟨13083, by rfl⟩ (by norm_num))
theorem R34893 : Reach 34893 := rs (se 3 (by rfl) ⟨6542, by rfl⟩) (B 13085 (by norm_num) ⟨6542, by rfl⟩ (by norm_num))
theorem R34897 : Reach 34897 := rs (se 2 (by rfl) ⟨13086, by rfl⟩) (B 26173 (by norm_num) ⟨13086, by rfl⟩ (by norm_num))
theorem R34901 : Reach 34901 := rs (se 8 (by rfl) ⟨204, by rfl⟩) (B 409 (by norm_num) ⟨204, by rfl⟩ (by norm_num))
theorem R34905 : Reach 34905 := rs (se 2 (by rfl) ⟨13089, by rfl⟩) (B 26179 (by norm_num) ⟨13089, by rfl⟩ (by norm_num))
theorem R34909 : Reach 34909 := rs (se 3 (by rfl) ⟨6545, by rfl⟩) (B 13091 (by norm_num) ⟨6545, by rfl⟩ (by norm_num))
theorem R34913 : Reach 34913 := rs (se 2 (by rfl) ⟨13092, by rfl⟩) (B 26185 (by norm_num) ⟨13092, by rfl⟩ (by norm_num))
theorem R34917 : Reach 34917 := rs (se 4 (by rfl) ⟨3273, by rfl⟩) (B 6547 (by norm_num) ⟨3273, by rfl⟩ (by norm_num))
theorem R34921 : Reach 34921 := rs (se 2 (by rfl) ⟨13095, by rfl⟩) (B 26191 (by norm_num) ⟨13095, by rfl⟩ (by norm_num))
theorem R34925 : Reach 34925 := rs (se 3 (by rfl) ⟨6548, by rfl⟩) (B 13097 (by norm_num) ⟨6548, by rfl⟩ (by norm_num))
theorem R34929 : Reach 34929 := rs (se 2 (by rfl) ⟨13098, by rfl⟩) (B 26197 (by norm_num) ⟨13098, by rfl⟩ (by norm_num))
theorem R34933 : Reach 34933 := rs (se 5 (by rfl) ⟨1637, by rfl⟩) (B 3275 (by norm_num) ⟨1637, by rfl⟩ (by norm_num))
theorem R34937 : Reach 34937 := rs (se 2 (by rfl) ⟨13101, by rfl⟩) (B 26203 (by norm_num) ⟨13101, by rfl⟩ (by norm_num))
theorem R34941 : Reach 34941 := rs (se 3 (by rfl) ⟨6551, by rfl⟩) (B 13103 (by norm_num) ⟨6551, by rfl⟩ (by norm_num))
theorem R34945 : Reach 34945 := rs (se 2 (by rfl) ⟨13104, by rfl⟩) (B 26209 (by norm_num) ⟨13104, by rfl⟩ (by norm_num))
theorem R34949 : Reach 34949 := rs (se 4 (by rfl) ⟨3276, by rfl⟩) (B 6553 (by norm_num) ⟨3276, by rfl⟩ (by norm_num))
theorem R34953 : Reach 34953 := rs (se 2 (by rfl) ⟨13107, by rfl⟩) (B 26215 (by norm_num) ⟨13107, by rfl⟩ (by norm_num))
theorem R34957 : Reach 34957 := rs (se 3 (by rfl) ⟨6554, by rfl⟩) (B 13109 (by norm_num) ⟨6554, by rfl⟩ (by norm_num))
theorem R34961 : Reach 34961 := rs (se 2 (by rfl) ⟨13110, by rfl⟩) (B 26221 (by norm_num) ⟨13110, by rfl⟩ (by norm_num))
theorem R34965 : Reach 34965 := rs (se 6 (by rfl) ⟨819, by rfl⟩) (B 1639 (by norm_num) ⟨819, by rfl⟩ (by norm_num))
theorem R34969 : Reach 34969 := rs (se 2 (by rfl) ⟨13113, by rfl⟩) (B 26227 (by norm_num) ⟨13113, by rfl⟩ (by norm_num))
theorem R34973 : Reach 34973 := rs (se 3 (by rfl) ⟨6557, by rfl⟩) (B 13115 (by norm_num) ⟨6557, by rfl⟩ (by norm_num))
theorem R34977 : Reach 34977 := rs (se 2 (by rfl) ⟨13116, by rfl⟩) (B 26233 (by norm_num) ⟨13116, by rfl⟩ (by norm_num))
theorem R133285 : Reach 133285 := rs (se 4 (by rfl) ⟨12495, by rfl⟩) (B 24991 (by norm_num) ⟨12495, by rfl⟩ (by norm_num))
theorem R34981 : Reach 34981 := rs (se 4 (by rfl) ⟨3279, by rfl⟩) (B 6559 (by norm_num) ⟨3279, by rfl⟩ (by norm_num))
theorem R34985 : Reach 34985 := rs (se 2 (by rfl) ⟨13119, by rfl⟩) (B 26239 (by norm_num) ⟨13119, by rfl⟩ (by norm_num))
theorem R34989 : Reach 34989 := rs (se 3 (by rfl) ⟨6560, by rfl⟩) (B 13121 (by norm_num) ⟨6560, by rfl⟩ (by norm_num))
theorem R34993 : Reach 34993 := rs (se 2 (by rfl) ⟨13122, by rfl⟩) (B 26245 (by norm_num) ⟨13122, by rfl⟩ (by norm_num))
theorem R34997 : Reach 34997 := rs (se 5 (by rfl) ⟨1640, by rfl⟩) (B 3281 (by norm_num) ⟨1640, by rfl⟩ (by norm_num))
theorem R35001 : Reach 35001 := rs (se 2 (by rfl) ⟨13125, by rfl⟩) (B 26251 (by norm_num) ⟨13125, by rfl⟩ (by norm_num))
theorem R35005 : Reach 35005 := rs (se 3 (by rfl) ⟨6563, by rfl⟩) (B 13127 (by norm_num) ⟨6563, by rfl⟩ (by norm_num))
theorem R35009 : Reach 35009 := rs (se 2 (by rfl) ⟨13128, by rfl⟩) (B 26257 (by norm_num) ⟨13128, by rfl⟩ (by norm_num))
theorem R35013 : Reach 35013 := rs (se 4 (by rfl) ⟨3282, by rfl⟩) (B 6565 (by norm_num) ⟨3282, by rfl⟩ (by norm_num))
theorem R35017 : Reach 35017 := rs (se 2 (by rfl) ⟨13131, by rfl⟩) (B 26263 (by norm_num) ⟨13131, by rfl⟩ (by norm_num))
theorem R35021 : Reach 35021 := rs (se 3 (by rfl) ⟨6566, by rfl⟩) (B 13133 (by norm_num) ⟨6566, by rfl⟩ (by norm_num))
theorem R35025 : Reach 35025 := rs (se 2 (by rfl) ⟨13134, by rfl⟩) (B 26269 (by norm_num) ⟨13134, by rfl⟩ (by norm_num))
theorem R35029 : Reach 35029 := rs (se 7 (by rfl) ⟨410, by rfl⟩) (B 821 (by norm_num) ⟨410, by rfl⟩ (by norm_num))
theorem R35033 : Reach 35033 := rs (se 2 (by rfl) ⟨13137, by rfl⟩) (B 26275 (by norm_num) ⟨13137, by rfl⟩ (by norm_num))
theorem R35037 : Reach 35037 := rs (se 3 (by rfl) ⟨6569, by rfl⟩) (B 13139 (by norm_num) ⟨6569, by rfl⟩ (by norm_num))
theorem R35041 : Reach 35041 := rs (se 2 (by rfl) ⟨13140, by rfl⟩) (B 26281 (by norm_num) ⟨13140, by rfl⟩ (by norm_num))
theorem R35045 : Reach 35045 := rs (se 4 (by rfl) ⟨3285, by rfl⟩) (B 6571 (by norm_num) ⟨3285, by rfl⟩ (by norm_num))
theorem R35049 : Reach 35049 := rs (se 2 (by rfl) ⟨13143, by rfl⟩) (B 26287 (by norm_num) ⟨13143, by rfl⟩ (by norm_num))
theorem R35053 : Reach 35053 := rs (se 3 (by rfl) ⟨6572, by rfl⟩) (B 13145 (by norm_num) ⟨6572, by rfl⟩ (by norm_num))
theorem R35057 : Reach 35057 := rs (se 2 (by rfl) ⟨13146, by rfl⟩) (B 26293 (by norm_num) ⟨13146, by rfl⟩ (by norm_num))
theorem R35061 : Reach 35061 := rs (se 5 (by rfl) ⟨1643, by rfl⟩) (B 3287 (by norm_num) ⟨1643, by rfl⟩ (by norm_num))
theorem R35065 : Reach 35065 := rs (se 2 (by rfl) ⟨13149, by rfl⟩) (B 26299 (by norm_num) ⟨13149, by rfl⟩ (by norm_num))
theorem R35069 : Reach 35069 := rs (se 3 (by rfl) ⟨6575, by rfl⟩) (B 13151 (by norm_num) ⟨6575, by rfl⟩ (by norm_num))
theorem R35073 : Reach 35073 := rs (se 2 (by rfl) ⟨13152, by rfl⟩) (B 26305 (by norm_num) ⟨13152, by rfl⟩ (by norm_num))
theorem R35077 : Reach 35077 := rs (se 4 (by rfl) ⟨3288, by rfl⟩) (B 6577 (by norm_num) ⟨3288, by rfl⟩ (by norm_num))
theorem R35081 : Reach 35081 := rs (se 2 (by rfl) ⟨13155, by rfl⟩) (B 26311 (by norm_num) ⟨13155, by rfl⟩ (by norm_num))
theorem R35085 : Reach 35085 := rs (se 3 (by rfl) ⟨6578, by rfl⟩) (B 13157 (by norm_num) ⟨6578, by rfl⟩ (by norm_num))
theorem R35089 : Reach 35089 := rs (se 2 (by rfl) ⟨13158, by rfl⟩) (B 26317 (by norm_num) ⟨13158, by rfl⟩ (by norm_num))
theorem R35093 : Reach 35093 := rs (se 6 (by rfl) ⟨822, by rfl⟩) (B 1645 (by norm_num) ⟨822, by rfl⟩ (by norm_num))
theorem R35097 : Reach 35097 := rs (se 2 (by rfl) ⟨13161, by rfl⟩) (B 26323 (by norm_num) ⟨13161, by rfl⟩ (by norm_num))
theorem R35101 : Reach 35101 := rs (se 3 (by rfl) ⟨6581, by rfl⟩) (B 13163 (by norm_num) ⟨6581, by rfl⟩ (by norm_num))
theorem R35105 : Reach 35105 := rs (se 2 (by rfl) ⟨13164, by rfl⟩) (B 26329 (by norm_num) ⟨13164, by rfl⟩ (by norm_num))
theorem R35109 : Reach 35109 := rs (se 4 (by rfl) ⟨3291, by rfl⟩) (B 6583 (by norm_num) ⟨3291, by rfl⟩ (by norm_num))
theorem R35113 : Reach 35113 := rs (se 2 (by rfl) ⟨13167, by rfl⟩) (B 26335 (by norm_num) ⟨13167, by rfl⟩ (by norm_num))
theorem R35149 : Reach 35149 := rs (se 3 (by rfl) ⟨6590, by rfl⟩) (B 13181 (by norm_num) ⟨6590, by rfl⟩ (by norm_num))
theorem R35185 : Reach 35185 := rs (se 2 (by rfl) ⟨13194, by rfl⟩) (B 26389 (by norm_num) ⟨13194, by rfl⟩ (by norm_num))
theorem R35197 : Reach 35197 := rs (se 3 (by rfl) ⟨6599, by rfl⟩) (B 13199 (by norm_num) ⟨6599, by rfl⟩ (by norm_num))
theorem R35221 : Reach 35221 := rs (se 6 (by rfl) ⟨825, by rfl⟩) (B 1651 (by norm_num) ⟨825, by rfl⟩ (by norm_num))
theorem R35257 : Reach 35257 := rs (se 2 (by rfl) ⟨13221, by rfl⟩) (B 26443 (by norm_num) ⟨13221, by rfl⟩ (by norm_num))
theorem R68045 : Reach 68045 := rs (se 3 (by rfl) ⟨12758, by rfl⟩) (B 25517 (by norm_num) ⟨12758, by rfl⟩ (by norm_num))
theorem R35293 : Reach 35293 := rs (se 3 (by rfl) ⟨6617, by rfl⟩) (B 13235 (by norm_num) ⟨6617, by rfl⟩ (by norm_num))
theorem R35317 : Reach 35317 := rs (se 5 (by rfl) ⟨1655, by rfl⟩) (B 3311 (by norm_num) ⟨1655, by rfl⟩ (by norm_num))
theorem R35329 : Reach 35329 := rs (se 2 (by rfl) ⟨13248, by rfl⟩) (B 26497 (by norm_num) ⟨13248, by rfl⟩ (by norm_num))
theorem R68117 : Reach 68117 := rs (se 6 (by rfl) ⟨1596, by rfl⟩) (B 3193 (by norm_num) ⟨1596, by rfl⟩ (by norm_num))
theorem R35365 : Reach 35365 := rs (se 4 (by rfl) ⟨3315, by rfl⟩) (B 6631 (by norm_num) ⟨3315, by rfl⟩ (by norm_num))
theorem R35401 : Reach 35401 := rs (se 2 (by rfl) ⟨13275, by rfl⟩) (B 26551 (by norm_num) ⟨13275, by rfl⟩ (by norm_num))
theorem R35437 : Reach 35437 := rs (se 3 (by rfl) ⟨6644, by rfl⟩) (B 13289 (by norm_num) ⟨6644, by rfl⟩ (by norm_num))
theorem R35473 : Reach 35473 := rs (se 2 (by rfl) ⟨13302, by rfl⟩) (B 26605 (by norm_num) ⟨13302, by rfl⟩ (by norm_num))
theorem R35509 : Reach 35509 := rs (se 5 (by rfl) ⟨1664, by rfl⟩) (B 3329 (by norm_num) ⟨1664, by rfl⟩ (by norm_num))
theorem R68293 : Reach 68293 := rs (se 4 (by rfl) ⟨6402, by rfl⟩) (B 12805 (by norm_num) ⟨6402, by rfl⟩ (by norm_num))
theorem R199381 : Reach 199381 := rs (se 7 (by rfl) ⟨2336, by rfl⟩) (B 4673 (by norm_num) ⟨2336, by rfl⟩ (by norm_num))
theorem R35545 : Reach 35545 := rs (se 2 (by rfl) ⟨13329, by rfl⟩) (B 26659 (by norm_num) ⟨13329, by rfl⟩ (by norm_num))
theorem R35569 : Reach 35569 := rs (se 2 (by rfl) ⟨13338, by rfl⟩) (B 26677 (by norm_num) ⟨13338, by rfl⟩ (by norm_num))
theorem R35573 : Reach 35573 := rs (se 5 (by rfl) ⟨1667, by rfl⟩) (B 3335 (by norm_num) ⟨1667, by rfl⟩ (by norm_num))
theorem R35581 : Reach 35581 := rs (se 3 (by rfl) ⟨6671, by rfl⟩) (B 13343 (by norm_num) ⟨6671, by rfl⟩ (by norm_num))
theorem R35617 : Reach 35617 := rs (se 2 (by rfl) ⟨13356, by rfl⟩) (B 26713 (by norm_num) ⟨13356, by rfl⟩ (by norm_num))
theorem R35653 : Reach 35653 := rs (se 4 (by rfl) ⟨3342, by rfl⟩) (B 6685 (by norm_num) ⟨3342, by rfl⟩ (by norm_num))
theorem R35689 : Reach 35689 := rs (se 2 (by rfl) ⟨13383, by rfl⟩) (B 26767 (by norm_num) ⟨13383, by rfl⟩ (by norm_num))
theorem R35725 : Reach 35725 := rs (se 3 (by rfl) ⟨6698, by rfl⟩) (B 13397 (by norm_num) ⟨6698, by rfl⟩ (by norm_num))
theorem R35761 : Reach 35761 := rs (se 2 (by rfl) ⟨13410, by rfl⟩) (B 26821 (by norm_num) ⟨13410, by rfl⟩ (by norm_num))
theorem R35797 : Reach 35797 := rs (se 7 (by rfl) ⟨419, by rfl⟩) (B 839 (by norm_num) ⟨419, by rfl⟩ (by norm_num))
theorem R35833 : Reach 35833 := rs (se 2 (by rfl) ⟨13437, by rfl⟩) (B 26875 (by norm_num) ⟨13437, by rfl⟩ (by norm_num))
theorem R35869 : Reach 35869 := rs (se 3 (by rfl) ⟨6725, by rfl⟩) (B 13451 (by norm_num) ⟨6725, by rfl⟩ (by norm_num))
theorem R35905 : Reach 35905 := rs (se 2 (by rfl) ⟨13464, by rfl⟩) (B 26929 (by norm_num) ⟨13464, by rfl⟩ (by norm_num))
theorem R35941 : Reach 35941 := rs (se 4 (by rfl) ⟨3369, by rfl⟩) (B 6739 (by norm_num) ⟨3369, by rfl⟩ (by norm_num))
theorem R35977 : Reach 35977 := rs (se 2 (by rfl) ⟨13491, by rfl⟩) (B 26983 (by norm_num) ⟨13491, by rfl⟩ (by norm_num))
theorem R36013 : Reach 36013 := rs (se 3 (by rfl) ⟨6752, by rfl⟩) (B 13505 (by norm_num) ⟨6752, by rfl⟩ (by norm_num))
theorem R68789 : Reach 68789 := rs (se 5 (by rfl) ⟨3224, by rfl⟩) (B 6449 (by norm_num) ⟨3224, by rfl⟩ (by norm_num))
theorem R36049 : Reach 36049 := rs (se 2 (by rfl) ⟨13518, by rfl⟩) (B 27037 (by norm_num) ⟨13518, by rfl⟩ (by norm_num))
theorem R36077 : Reach 36077 := rs (se 3 (by rfl) ⟨6764, by rfl⟩) (B 13529 (by norm_num) ⟨6764, by rfl⟩ (by norm_num))
theorem R36085 : Reach 36085 := rs (se 5 (by rfl) ⟨1691, by rfl⟩) (B 3383 (by norm_num) ⟨1691, by rfl⟩ (by norm_num))
theorem R36121 : Reach 36121 := rs (se 2 (by rfl) ⟨13545, by rfl⟩) (B 27091 (by norm_num) ⟨13545, by rfl⟩ (by norm_num))
theorem R36137 : Reach 36137 := rs (se 2 (by rfl) ⟨13551, by rfl⟩) (B 27103 (by norm_num) ⟨13551, by rfl⟩ (by norm_num))
theorem R36157 : Reach 36157 := rs (se 3 (by rfl) ⟨6779, by rfl⟩) (B 13559 (by norm_num) ⟨6779, by rfl⟩ (by norm_num))
theorem R36193 : Reach 36193 := rs (se 2 (by rfl) ⟨13572, by rfl⟩) (B 27145 (by norm_num) ⟨13572, by rfl⟩ (by norm_num))
theorem R36229 : Reach 36229 := rs (se 4 (by rfl) ⟨3396, by rfl⟩) (B 6793 (by norm_num) ⟨3396, by rfl⟩ (by norm_num))
theorem R36265 : Reach 36265 := rs (se 2 (by rfl) ⟨13599, by rfl⟩) (B 27199 (by norm_num) ⟨13599, by rfl⟩ (by norm_num))
theorem R36301 : Reach 36301 := rs (se 3 (by rfl) ⟨6806, by rfl⟩) (B 13613 (by norm_num) ⟨6806, by rfl⟩ (by norm_num))
theorem R36325 : Reach 36325 := rs (se 4 (by rfl) ⟨3405, by rfl⟩) (B 6811 (by norm_num) ⟨3405, by rfl⟩ (by norm_num))
theorem R36337 : Reach 36337 := rs (se 2 (by rfl) ⟨13626, by rfl⟩) (B 27253 (by norm_num) ⟨13626, by rfl⟩ (by norm_num))
theorem R36373 : Reach 36373 := rs (se 6 (by rfl) ⟨852, by rfl⟩) (B 1705 (by norm_num) ⟨852, by rfl⟩ (by norm_num))
theorem R36409 : Reach 36409 := rs (se 2 (by rfl) ⟨13653, by rfl⟩) (B 27307 (by norm_num) ⟨13653, by rfl⟩ (by norm_num))
theorem R36445 : Reach 36445 := rs (se 3 (by rfl) ⟨6833, by rfl⟩) (B 13667 (by norm_num) ⟨6833, by rfl⟩ (by norm_num))
theorem R36481 : Reach 36481 := rs (se 2 (by rfl) ⟨13680, by rfl⟩) (B 27361 (by norm_num) ⟨13680, by rfl⟩ (by norm_num))
theorem R36517 : Reach 36517 := rs (se 4 (by rfl) ⟨3423, by rfl⟩) (B 6847 (by norm_num) ⟨3423, by rfl⟩ (by norm_num))
theorem R36553 : Reach 36553 := rs (se 2 (by rfl) ⟨13707, by rfl⟩) (B 27415 (by norm_num) ⟨13707, by rfl⟩ (by norm_num))
theorem R36589 : Reach 36589 := rs (se 3 (by rfl) ⟨6860, by rfl⟩) (B 13721 (by norm_num) ⟨6860, by rfl⟩ (by norm_num))
theorem R167669 : Reach 167669 := rs (se 5 (by rfl) ⟨7859, by rfl⟩) (B 15719 (by norm_num) ⟨7859, by rfl⟩ (by norm_num))
theorem R36625 : Reach 36625 := rs (se 2 (by rfl) ⟨13734, by rfl⟩) (B 27469 (by norm_num) ⟨13734, by rfl⟩ (by norm_num))
theorem R102197 : Reach 102197 := rs (se 5 (by rfl) ⟨4790, by rfl⟩) (B 9581 (by norm_num) ⟨4790, by rfl⟩ (by norm_num))
theorem R36661 : Reach 36661 := rs (se 5 (by rfl) ⟨1718, by rfl⟩) (B 3437 (by norm_num) ⟨1718, by rfl⟩ (by norm_num))
theorem R36697 : Reach 36697 := rs (se 2 (by rfl) ⟨13761, by rfl⟩) (B 27523 (by norm_num) ⟨13761, by rfl⟩ (by norm_num))
theorem R36733 : Reach 36733 := rs (se 3 (by rfl) ⟨6887, by rfl⟩) (B 13775 (by norm_num) ⟨6887, by rfl⟩ (by norm_num))
theorem R36769 : Reach 36769 := rs (se 2 (by rfl) ⟨13788, by rfl⟩) (B 27577 (by norm_num) ⟨13788, by rfl⟩ (by norm_num))
theorem R36805 : Reach 36805 := rs (se 4 (by rfl) ⟨3450, by rfl⟩) (B 6901 (by norm_num) ⟨3450, by rfl⟩ (by norm_num))
theorem R36841 : Reach 36841 := rs (se 2 (by rfl) ⟨13815, by rfl⟩) (B 27631 (by norm_num) ⟨13815, by rfl⟩ (by norm_num))
theorem R36877 : Reach 36877 := rs (se 3 (by rfl) ⟨6914, by rfl⟩) (B 13829 (by norm_num) ⟨6914, by rfl⟩ (by norm_num))
theorem R69677 : Reach 69677 := rs (se 3 (by rfl) ⟨13064, by rfl⟩) (B 26129 (by norm_num) ⟨13064, by rfl⟩ (by norm_num))
theorem R36913 : Reach 36913 := rs (se 2 (by rfl) ⟨13842, by rfl⟩) (B 27685 (by norm_num) ⟨13842, by rfl⟩ (by norm_num))
theorem R36949 : Reach 36949 := rs (se 8 (by rfl) ⟨216, by rfl⟩) (B 433 (by norm_num) ⟨216, by rfl⟩ (by norm_num))
theorem R36985 : Reach 36985 := rs (se 2 (by rfl) ⟨13869, by rfl⟩) (B 27739 (by norm_num) ⟨13869, by rfl⟩ (by norm_num))
theorem R37021 : Reach 37021 := rs (se 3 (by rfl) ⟨6941, by rfl⟩) (B 13883 (by norm_num) ⟨6941, by rfl⟩ (by norm_num))
theorem R69797 : Reach 69797 := rs (se 4 (by rfl) ⟨6543, by rfl⟩) (B 13087 (by norm_num) ⟨6543, by rfl⟩ (by norm_num))
theorem R102565 : Reach 102565 := rs (se 4 (by rfl) ⟨9615, by rfl⟩) (B 19231 (by norm_num) ⟨9615, by rfl⟩ (by norm_num))
theorem R37057 : Reach 37057 := rs (se 2 (by rfl) ⟨13896, by rfl⟩) (B 27793 (by norm_num) ⟨13896, by rfl⟩ (by norm_num))
theorem R37093 : Reach 37093 := rs (se 4 (by rfl) ⟨3477, by rfl⟩) (B 6955 (by norm_num) ⟨3477, by rfl⟩ (by norm_num))
theorem R69869 : Reach 69869 := rs (se 3 (by rfl) ⟨13100, by rfl⟩) (B 26201 (by norm_num) ⟨13100, by rfl⟩ (by norm_num))
theorem R37129 : Reach 37129 := rs (se 2 (by rfl) ⟨13923, by rfl⟩) (B 27847 (by norm_num) ⟨13923, by rfl⟩ (by norm_num))
theorem R37145 : Reach 37145 := rs (se 2 (by rfl) ⟨13929, by rfl⟩) (B 27859 (by norm_num) ⟨13929, by rfl⟩ (by norm_num))
theorem R37165 : Reach 37165 := rs (se 3 (by rfl) ⟨6968, by rfl⟩) (B 13937 (by norm_num) ⟨6968, by rfl⟩ (by norm_num))
theorem R37201 : Reach 37201 := rs (se 2 (by rfl) ⟨13950, by rfl⟩) (B 27901 (by norm_num) ⟨13950, by rfl⟩ (by norm_num))
theorem R37237 : Reach 37237 := rs (se 5 (by rfl) ⟨1745, by rfl⟩) (B 3491 (by norm_num) ⟨1745, by rfl⟩ (by norm_num))
theorem R70037 : Reach 70037 := rs (se 6 (by rfl) ⟨1641, by rfl⟩) (B 3283 (by norm_num) ⟨1641, by rfl⟩ (by norm_num))
theorem R37273 : Reach 37273 := rs (se 2 (by rfl) ⟨13977, by rfl⟩) (B 27955 (by norm_num) ⟨13977, by rfl⟩ (by norm_num))
theorem R37309 : Reach 37309 := rs (se 3 (by rfl) ⟨6995, by rfl⟩) (B 13991 (by norm_num) ⟨6995, by rfl⟩ (by norm_num))
theorem R70109 : Reach 70109 := rs (se 3 (by rfl) ⟨13145, by rfl⟩) (B 26291 (by norm_num) ⟨13145, by rfl⟩ (by norm_num))
theorem R37345 : Reach 37345 := rs (se 2 (by rfl) ⟨14004, by rfl⟩) (B 28009 (by norm_num) ⟨14004, by rfl⟩ (by norm_num))
theorem R37381 : Reach 37381 := rs (se 4 (by rfl) ⟨3504, by rfl⟩) (B 7009 (by norm_num) ⟨3504, by rfl⟩ (by norm_num))
theorem R70181 : Reach 70181 := rs (se 4 (by rfl) ⟨6579, by rfl⟩) (B 13159 (by norm_num) ⟨6579, by rfl⟩ (by norm_num))
theorem R37417 : Reach 37417 := rs (se 2 (by rfl) ⟨14031, by rfl⟩) (B 28063 (by norm_num) ⟨14031, by rfl⟩ (by norm_num))
theorem R37441 : Reach 37441 := rs (se 2 (by rfl) ⟨14040, by rfl⟩) (B 28081 (by norm_num) ⟨14040, by rfl⟩ (by norm_num))
theorem R37453 : Reach 37453 := rs (se 3 (by rfl) ⟨7022, by rfl⟩) (B 14045 (by norm_num) ⟨7022, by rfl⟩ (by norm_num))
theorem R70253 : Reach 70253 := rs (se 3 (by rfl) ⟨13172, by rfl⟩) (B 26345 (by norm_num) ⟨13172, by rfl⟩ (by norm_num))
theorem R37489 : Reach 37489 := rs (se 2 (by rfl) ⟨14058, by rfl⟩) (B 28117 (by norm_num) ⟨14058, by rfl⟩ (by norm_num))
theorem R37525 : Reach 37525 := rs (se 6 (by rfl) ⟨879, by rfl⟩) (B 1759 (by norm_num) ⟨879, by rfl⟩ (by norm_num))
theorem R135845 : Reach 135845 := rs (se 4 (by rfl) ⟨12735, by rfl⟩) (B 25471 (by norm_num) ⟨12735, by rfl⟩ (by norm_num))
theorem R70325 : Reach 70325 := rs (se 5 (by rfl) ⟨3296, by rfl⟩) (B 6593 (by norm_num) ⟨3296, by rfl⟩ (by norm_num))
theorem R37561 : Reach 37561 := rs (se 2 (by rfl) ⟨14085, by rfl⟩) (B 28171 (by norm_num) ⟨14085, by rfl⟩ (by norm_num))
theorem R37597 : Reach 37597 := rs (se 3 (by rfl) ⟨7049, by rfl⟩) (B 14099 (by norm_num) ⟨7049, by rfl⟩ (by norm_num))
theorem R70397 : Reach 70397 := rs (se 3 (by rfl) ⟨13199, by rfl⟩) (B 26399 (by norm_num) ⟨13199, by rfl⟩ (by norm_num))
theorem R37633 : Reach 37633 := rs (se 2 (by rfl) ⟨14112, by rfl⟩) (B 28225 (by norm_num) ⟨14112, by rfl⟩ (by norm_num))
theorem R70429 : Reach 70429 := rs (se 3 (by rfl) ⟨13205, by rfl⟩) (B 26411 (by norm_num) ⟨13205, by rfl⟩ (by norm_num))
theorem R37669 : Reach 37669 := rs (se 4 (by rfl) ⟨3531, by rfl⟩) (B 7063 (by norm_num) ⟨3531, by rfl⟩ (by norm_num))
theorem R135989 : Reach 135989 := rs (se 5 (by rfl) ⟨6374, by rfl⟩) (B 12749 (by norm_num) ⟨6374, by rfl⟩ (by norm_num))
theorem R70469 : Reach 70469 := rs (se 4 (by rfl) ⟨6606, by rfl⟩) (B 13213 (by norm_num) ⟨6606, by rfl⟩ (by norm_num))
theorem R37705 : Reach 37705 := rs (se 2 (by rfl) ⟨14139, by rfl⟩) (B 28279 (by norm_num) ⟨14139, by rfl⟩ (by norm_num))
theorem R299861 : Reach 299861 := rs (se 9 (by rfl) ⟨878, by rfl⟩) (B 1757 (by norm_num) ⟨878, by rfl⟩ (by norm_num))
theorem R37741 : Reach 37741 := rs (se 3 (by rfl) ⟨7076, by rfl⟩) (B 14153 (by norm_num) ⟨7076, by rfl⟩ (by norm_num))
theorem R103285 : Reach 103285 := rs (se 5 (by rfl) ⟨4841, by rfl⟩) (B 9683 (by norm_num) ⟨4841, by rfl⟩ (by norm_num))
theorem R70541 : Reach 70541 := rs (se 3 (by rfl) ⟨13226, by rfl⟩) (B 26453 (by norm_num) ⟨13226, by rfl⟩ (by norm_num))
theorem R37777 : Reach 37777 := rs (se 2 (by rfl) ⟨14166, by rfl⟩) (B 28333 (by norm_num) ⟨14166, by rfl⟩ (by norm_num))
theorem R37813 : Reach 37813 := rs (se 5 (by rfl) ⟨1772, by rfl⟩) (B 3545 (by norm_num) ⟨1772, by rfl⟩ (by norm_num))
theorem R70613 : Reach 70613 := rs (se 7 (by rfl) ⟨827, by rfl⟩) (B 1655 (by norm_num) ⟨827, by rfl⟩ (by norm_num))
theorem R37849 : Reach 37849 := rs (se 2 (by rfl) ⟨14193, by rfl⟩) (B 28387 (by norm_num) ⟨14193, by rfl⟩ (by norm_num))
theorem R37885 : Reach 37885 := rs (se 3 (by rfl) ⟨7103, by rfl⟩) (B 14207 (by norm_num) ⟨7103, by rfl⟩ (by norm_num))
theorem R70685 : Reach 70685 := rs (se 3 (by rfl) ⟨13253, by rfl⟩) (B 26507 (by norm_num) ⟨13253, by rfl⟩ (by norm_num))
theorem R37921 : Reach 37921 := rs (se 2 (by rfl) ⟨14220, by rfl⟩) (B 28441 (by norm_num) ⟨14220, by rfl⟩ (by norm_num))
theorem R37957 : Reach 37957 := rs (se 4 (by rfl) ⟨3558, by rfl⟩) (B 7117 (by norm_num) ⟨3558, by rfl⟩ (by norm_num))
theorem R70757 : Reach 70757 := rs (se 4 (by rfl) ⟨6633, by rfl⟩) (B 13267 (by norm_num) ⟨6633, by rfl⟩ (by norm_num))
theorem R37993 : Reach 37993 := rs (se 2 (by rfl) ⟨14247, by rfl⟩) (B 28495 (by norm_num) ⟨14247, by rfl⟩ (by norm_num))
theorem R38029 : Reach 38029 := rs (se 3 (by rfl) ⟨7130, by rfl⟩) (B 14261 (by norm_num) ⟨7130, by rfl⟩ (by norm_num))
theorem R70829 : Reach 70829 := rs (se 3 (by rfl) ⟨13280, by rfl⟩) (B 26561 (by norm_num) ⟨13280, by rfl⟩ (by norm_num))
theorem R38065 : Reach 38065 := rs (se 2 (by rfl) ⟨14274, by rfl⟩) (B 28549 (by norm_num) ⟨14274, by rfl⟩ (by norm_num))
theorem R38101 : Reach 38101 := rs (se 7 (by rfl) ⟨446, by rfl⟩) (B 893 (by norm_num) ⟨446, by rfl⟩ (by norm_num))
theorem R38117 : Reach 38117 := rs (se 4 (by rfl) ⟨3573, by rfl⟩) (B 7147 (by norm_num) ⟨3573, by rfl⟩ (by norm_num))
theorem R70901 : Reach 70901 := rs (se 5 (by rfl) ⟨3323, by rfl⟩) (B 6647 (by norm_num) ⟨3323, by rfl⟩ (by norm_num))
theorem R38137 : Reach 38137 := rs (se 2 (by rfl) ⟨14301, by rfl⟩) (B 28603 (by norm_num) ⟨14301, by rfl⟩ (by norm_num))
theorem R38173 : Reach 38173 := rs (se 3 (by rfl) ⟨7157, by rfl⟩) (B 14315 (by norm_num) ⟨7157, by rfl⟩ (by norm_num))
theorem R70973 : Reach 70973 := rs (se 3 (by rfl) ⟨13307, by rfl⟩) (B 26615 (by norm_num) ⟨13307, by rfl⟩ (by norm_num))
theorem R38209 : Reach 38209 := rs (se 2 (by rfl) ⟨14328, by rfl⟩) (B 28657 (by norm_num) ⟨14328, by rfl⟩ (by norm_num))
theorem R38245 : Reach 38245 := rs (se 4 (by rfl) ⟨3585, by rfl⟩) (B 7171 (by norm_num) ⟨3585, by rfl⟩ (by norm_num))
theorem R71045 : Reach 71045 := rs (se 4 (by rfl) ⟨6660, by rfl⟩) (B 13321 (by norm_num) ⟨6660, by rfl⟩ (by norm_num))
theorem R38281 : Reach 38281 := rs (se 2 (by rfl) ⟨14355, by rfl⟩) (B 28711 (by norm_num) ⟨14355, by rfl⟩ (by norm_num))
theorem R71069 : Reach 71069 := rs (se 3 (by rfl) ⟨13325, by rfl⟩) (B 26651 (by norm_num) ⟨13325, by rfl⟩ (by norm_num))
theorem R38317 : Reach 38317 := rs (se 3 (by rfl) ⟨7184, by rfl⟩) (B 14369 (by norm_num) ⟨7184, by rfl⟩ (by norm_num))
theorem R71117 : Reach 71117 := rs (se 3 (by rfl) ⟨13334, by rfl⟩) (B 26669 (by norm_num) ⟨13334, by rfl⟩ (by norm_num))
theorem R38353 : Reach 38353 := rs (se 2 (by rfl) ⟨14382, by rfl⟩) (B 28765 (by norm_num) ⟨14382, by rfl⟩ (by norm_num))
theorem R38389 : Reach 38389 := rs (se 5 (by rfl) ⟨1799, by rfl⟩) (B 3599 (by norm_num) ⟨1799, by rfl⟩ (by norm_num))
theorem R71189 : Reach 71189 := rs (se 6 (by rfl) ⟨1668, by rfl⟩) (B 3337 (by norm_num) ⟨1668, by rfl⟩ (by norm_num))
theorem R38425 : Reach 38425 := rs (se 2 (by rfl) ⟨14409, by rfl⟩) (B 28819 (by norm_num) ⟨14409, by rfl⟩ (by norm_num))
theorem R38461 : Reach 38461 := rs (se 3 (by rfl) ⟨7211, by rfl⟩) (B 14423 (by norm_num) ⟨7211, by rfl⟩ (by norm_num))
theorem R71261 : Reach 71261 := rs (se 3 (by rfl) ⟨13361, by rfl⟩) (B 26723 (by norm_num) ⟨13361, by rfl⟩ (by norm_num))
theorem R38497 : Reach 38497 := rs (se 2 (by rfl) ⟨14436, by rfl⟩) (B 28873 (by norm_num) ⟨14436, by rfl⟩ (by norm_num))
theorem R38533 : Reach 38533 := rs (se 4 (by rfl) ⟨3612, by rfl⟩) (B 7225 (by norm_num) ⟨3612, by rfl⟩ (by norm_num))
theorem R71317 : Reach 71317 := rs (se 6 (by rfl) ⟨1671, by rfl⟩) (B 3343 (by norm_num) ⟨1671, by rfl⟩ (by norm_num))
theorem R71333 : Reach 71333 := rs (se 4 (by rfl) ⟨6687, by rfl⟩) (B 13375 (by norm_num) ⟨6687, by rfl⟩ (by norm_num))
theorem R38569 : Reach 38569 := rs (se 2 (by rfl) ⟨14463, by rfl⟩) (B 28927 (by norm_num) ⟨14463, by rfl⟩ (by norm_num))
theorem R136885 : Reach 136885 := rs (se 5 (by rfl) ⟨6416, by rfl⟩) (B 12833 (by norm_num) ⟨6416, by rfl⟩ (by norm_num))
theorem R38605 : Reach 38605 := rs (se 3 (by rfl) ⟨7238, by rfl⟩) (B 14477 (by norm_num) ⟨7238, by rfl⟩ (by norm_num))
theorem R71405 : Reach 71405 := rs (se 3 (by rfl) ⟨13388, by rfl⟩) (B 26777 (by norm_num) ⟨13388, by rfl⟩ (by norm_num))
theorem R38641 : Reach 38641 := rs (se 2 (by rfl) ⟨14490, by rfl⟩) (B 28981 (by norm_num) ⟨14490, by rfl⟩ (by norm_num))
theorem R71437 : Reach 71437 := rs (se 3 (by rfl) ⟨13394, by rfl⟩) (B 26789 (by norm_num) ⟨13394, by rfl⟩ (by norm_num))
theorem R38677 : Reach 38677 := rs (se 6 (by rfl) ⟨906, by rfl⟩) (B 1813 (by norm_num) ⟨906, by rfl⟩ (by norm_num))
theorem R136997 : Reach 136997 := rs (se 4 (by rfl) ⟨12843, by rfl⟩) (B 25687 (by norm_num) ⟨12843, by rfl⟩ (by norm_num))
theorem R71477 : Reach 71477 := rs (se 5 (by rfl) ⟨3350, by rfl⟩) (B 6701 (by norm_num) ⟨3350, by rfl⟩ (by norm_num))
theorem R38713 : Reach 38713 := rs (se 2 (by rfl) ⟨14517, by rfl⟩) (B 29035 (by norm_num) ⟨14517, by rfl⟩ (by norm_num))
theorem R38749 : Reach 38749 := rs (se 3 (by rfl) ⟨7265, by rfl⟩) (B 14531 (by norm_num) ⟨7265, by rfl⟩ (by norm_num))
theorem R71549 : Reach 71549 := rs (se 3 (by rfl) ⟨13415, by rfl⟩) (B 26831 (by norm_num) ⟨13415, by rfl⟩ (by norm_num))
theorem R38785 : Reach 38785 := rs (se 2 (by rfl) ⟨14544, by rfl⟩) (B 29089 (by norm_num) ⟨14544, by rfl⟩ (by norm_num))
theorem R268181 : Reach 268181 := rs (se 6 (by rfl) ⟨6285, by rfl⟩) (B 12571 (by norm_num) ⟨6285, by rfl⟩ (by norm_num))
theorem R38809 : Reach 38809 := rs (se 2 (by rfl) ⟨14553, by rfl⟩) (B 29107 (by norm_num) ⟨14553, by rfl⟩ (by norm_num))
theorem R38821 : Reach 38821 := rs (se 4 (by rfl) ⟨3639, by rfl⟩) (B 7279 (by norm_num) ⟨3639, by rfl⟩ (by norm_num))
theorem R71621 : Reach 71621 := rs (se 4 (by rfl) ⟨6714, by rfl⟩) (B 13429 (by norm_num) ⟨6714, by rfl⟩ (by norm_num))
theorem R38857 : Reach 38857 := rs (se 2 (by rfl) ⟨14571, by rfl⟩) (B 29143 (by norm_num) ⟨14571, by rfl⟩ (by norm_num))
theorem R38893 : Reach 38893 := rs (se 3 (by rfl) ⟨7292, by rfl⟩) (B 14585 (by norm_num) ⟨7292, by rfl⟩ (by norm_num))
theorem R104453 : Reach 104453 := rs (se 4 (by rfl) ⟨9792, by rfl⟩) (B 19585 (by norm_num) ⟨9792, by rfl⟩ (by norm_num))
theorem R71693 : Reach 71693 := rs (se 3 (by rfl) ⟨13442, by rfl⟩) (B 26885 (by norm_num) ⟨13442, by rfl⟩ (by norm_num))
theorem R38929 : Reach 38929 := rs (se 2 (by rfl) ⟨14598, by rfl⟩) (B 29197 (by norm_num) ⟨14598, by rfl⟩ (by norm_num))
theorem R38965 : Reach 38965 := rs (se 5 (by rfl) ⟨1826, by rfl⟩) (B 3653 (by norm_num) ⟨1826, by rfl⟩ (by norm_num))
theorem R71765 : Reach 71765 := rs (se 8 (by rfl) ⟨420, by rfl⟩) (B 841 (by norm_num) ⟨420, by rfl⟩ (by norm_num))
theorem R39001 : Reach 39001 := rs (se 2 (by rfl) ⟨14625, by rfl⟩) (B 29251 (by norm_num) ⟨14625, by rfl⟩ (by norm_num))
theorem R39037 : Reach 39037 := rs (se 3 (by rfl) ⟨7319, by rfl⟩) (B 14639 (by norm_num) ⟨7319, by rfl⟩ (by norm_num))
theorem R71837 : Reach 71837 := rs (se 3 (by rfl) ⟨13469, by rfl⟩) (B 26939 (by norm_num) ⟨13469, by rfl⟩ (by norm_num))
theorem R39073 : Reach 39073 := rs (se 2 (by rfl) ⟨14652, by rfl⟩) (B 29305 (by norm_num) ⟨14652, by rfl⟩ (by norm_num))
theorem R39109 : Reach 39109 := rs (se 4 (by rfl) ⟨3666, by rfl⟩) (B 7333 (by norm_num) ⟨3666, by rfl⟩ (by norm_num))
theorem R71909 : Reach 71909 := rs (se 4 (by rfl) ⟨6741, by rfl⟩) (B 13483 (by norm_num) ⟨6741, by rfl⟩ (by norm_num))
theorem R39145 : Reach 39145 := rs (se 2 (by rfl) ⟨14679, by rfl⟩) (B 29359 (by norm_num) ⟨14679, by rfl⟩ (by norm_num))
theorem R39181 : Reach 39181 := rs (se 3 (by rfl) ⟨7346, by rfl⟩) (B 14693 (by norm_num) ⟨7346, by rfl⟩ (by norm_num))
theorem R170261 : Reach 170261 := rs (se 6 (by rfl) ⟨3990, by rfl⟩) (B 7981 (by norm_num) ⟨3990, by rfl⟩ (by norm_num))
theorem R71981 : Reach 71981 := rs (se 3 (by rfl) ⟨13496, by rfl⟩) (B 26993 (by norm_num) ⟨13496, by rfl⟩ (by norm_num))
theorem R39217 : Reach 39217 := rs (se 2 (by rfl) ⟨14706, by rfl⟩) (B 29413 (by norm_num) ⟨14706, by rfl⟩ (by norm_num))
theorem R39253 : Reach 39253 := rs (se 10 (by rfl) ⟨57, by rfl⟩) (B 115 (by norm_num) ⟨57, by rfl⟩ (by norm_num))
theorem R72053 : Reach 72053 := rs (se 5 (by rfl) ⟨3377, by rfl⟩) (B 6755 (by norm_num) ⟨3377, by rfl⟩ (by norm_num))
theorem R39289 : Reach 39289 := rs (se 2 (by rfl) ⟨14733, by rfl⟩) (B 29467 (by norm_num) ⟨14733, by rfl⟩ (by norm_num))
theorem R39325 : Reach 39325 := rs (se 3 (by rfl) ⟨7373, by rfl⟩) (B 14747 (by norm_num) ⟨7373, by rfl⟩ (by norm_num))
theorem R72125 : Reach 72125 := rs (se 3 (by rfl) ⟨13523, by rfl⟩) (B 27047 (by norm_num) ⟨13523, by rfl⟩ (by norm_num))
theorem R39361 : Reach 39361 := rs (se 2 (by rfl) ⟨14760, by rfl⟩) (B 29521 (by norm_num) ⟨14760, by rfl⟩ (by norm_num))
theorem R39397 : Reach 39397 := rs (se 4 (by rfl) ⟨3693, by rfl⟩) (B 7387 (by norm_num) ⟨3693, by rfl⟩ (by norm_num))
theorem R72197 : Reach 72197 := rs (se 4 (by rfl) ⟨6768, by rfl⟩) (B 13537 (by norm_num) ⟨6768, by rfl⟩ (by norm_num))
theorem R39433 : Reach 39433 := rs (se 2 (by rfl) ⟨14787, by rfl⟩) (B 29575 (by norm_num) ⟨14787, by rfl⟩ (by norm_num))
theorem R39457 : Reach 39457 := rs (se 2 (by rfl) ⟨14796, by rfl⟩) (B 29593 (by norm_num) ⟨14796, by rfl⟩ (by norm_num))
theorem R39469 : Reach 39469 := rs (se 3 (by rfl) ⟨7400, by rfl⟩) (B 14801 (by norm_num) ⟨7400, by rfl⟩ (by norm_num))
theorem R105029 : Reach 105029 := rs (se 4 (by rfl) ⟨9846, by rfl⟩) (B 19693 (by norm_num) ⟨9846, by rfl⟩ (by norm_num))
theorem R72269 : Reach 72269 := rs (se 3 (by rfl) ⟨13550, by rfl⟩) (B 27101 (by norm_num) ⟨13550, by rfl⟩ (by norm_num))
theorem R39505 : Reach 39505 := rs (se 2 (by rfl) ⟨14814, by rfl⟩) (B 29629 (by norm_num) ⟨14814, by rfl⟩ (by norm_num))
theorem R203381 : Reach 203381 := rs (se 5 (by rfl) ⟨9533, by rfl⟩) (B 19067 (by norm_num) ⟨9533, by rfl⟩ (by norm_num))
theorem R72325 : Reach 72325 := rs (se 4 (by rfl) ⟨6780, by rfl⟩) (B 13561 (by norm_num) ⟨6780, by rfl⟩ (by norm_num))
theorem R72341 : Reach 72341 := rs (se 6 (by rfl) ⟨1695, by rfl⟩) (B 3391 (by norm_num) ⟨1695, by rfl⟩ (by norm_num))
theorem R39629 : Reach 39629 := rs (se 3 (by rfl) ⟨7430, by rfl⟩) (B 14861 (by norm_num) ⟨7430, by rfl⟩ (by norm_num))
theorem R72413 : Reach 72413 := rs (se 3 (by rfl) ⟨13577, by rfl⟩) (B 27155 (by norm_num) ⟨13577, by rfl⟩ (by norm_num))
theorem R39685 : Reach 39685 := rs (se 4 (by rfl) ⟨3720, by rfl⟩) (B 7441 (by norm_num) ⟨3720, by rfl⟩ (by norm_num))
theorem R72485 : Reach 72485 := rs (se 4 (by rfl) ⟨6795, by rfl⟩) (B 13591 (by norm_num) ⟨6795, by rfl⟩ (by norm_num))
theorem R203573 : Reach 203573 := rs (se 5 (by rfl) ⟨9542, by rfl⟩) (B 19085 (by norm_num) ⟨9542, by rfl⟩ (by norm_num))
theorem R39781 : Reach 39781 := rs (se 4 (by rfl) ⟨3729, by rfl⟩) (B 7459 (by norm_num) ⟨3729, by rfl⟩ (by norm_num))
theorem R72557 : Reach 72557 := rs (se 3 (by rfl) ⟨13604, by rfl⟩) (B 27209 (by norm_num) ⟨13604, by rfl⟩ (by norm_num))
theorem R72581 : Reach 72581 := rs (se 4 (by rfl) ⟨6804, by rfl⟩) (B 13609 (by norm_num) ⟨6804, by rfl⟩ (by norm_num))
theorem R72629 : Reach 72629 := rs (se 5 (by rfl) ⟨3404, by rfl⟩) (B 6809 (by norm_num) ⟨3404, by rfl⟩ (by norm_num))
theorem R105461 : Reach 105461 := rs (se 5 (by rfl) ⟨4943, by rfl⟩) (B 9887 (by norm_num) ⟨4943, by rfl⟩ (by norm_num))
theorem R72701 : Reach 72701 := rs (se 3 (by rfl) ⟨13631, by rfl⟩) (B 27263 (by norm_num) ⟨13631, by rfl⟩ (by norm_num))
theorem R39953 : Reach 39953 := rs (se 2 (by rfl) ⟨14982, by rfl⟩) (B 29965 (by norm_num) ⟨14982, by rfl⟩ (by norm_num))
theorem R564245 : Reach 564245 := rs (se 6 (by rfl) ⟨13224, by rfl⟩) (B 26449 (by norm_num) ⟨13224, by rfl⟩ (by norm_num))
theorem R72773 : Reach 72773 := rs (se 4 (by rfl) ⟨6822, by rfl⟩) (B 13645 (by norm_num) ⟨6822, by rfl⟩ (by norm_num))
theorem R40009 : Reach 40009 := rs (se 2 (by rfl) ⟨15003, by rfl⟩) (B 30007 (by norm_num) ⟨15003, by rfl⟩ (by norm_num))
theorem R72821 : Reach 72821 := rs (se 5 (by rfl) ⟨3413, by rfl⟩) (B 6827 (by norm_num) ⟨3413, by rfl⟩ (by norm_num))
theorem R72845 : Reach 72845 := rs (se 3 (by rfl) ⟨13658, by rfl⟩) (B 27317 (by norm_num) ⟨13658, by rfl⟩ (by norm_num))
theorem R40105 : Reach 40105 := rs (se 2 (by rfl) ⟨15039, by rfl⟩) (B 30079 (by norm_num) ⟨15039, by rfl⟩ (by norm_num))
theorem R72917 : Reach 72917 := rs (se 7 (by rfl) ⟨854, by rfl⟩) (B 1709 (by norm_num) ⟨854, by rfl⟩ (by norm_num))
theorem R72989 : Reach 72989 := rs (se 3 (by rfl) ⟨13685, by rfl⟩) (B 27371 (by norm_num) ⟨13685, by rfl⟩ (by norm_num))
theorem R40277 : Reach 40277 := rs (se 11 (by rfl) ⟨29, by rfl⟩) (B 59 (by norm_num) ⟨29, by rfl⟩ (by norm_num))
theorem R40285 : Reach 40285 := rs (se 3 (by rfl) ⟨7553, by rfl⟩) (B 15107 (by norm_num) ⟨7553, by rfl⟩ (by norm_num))
theorem R73061 : Reach 73061 := rs (se 4 (by rfl) ⟨6849, by rfl⟩) (B 13699 (by norm_num) ⟨6849, by rfl⟩ (by norm_num))
theorem R40333 : Reach 40333 := rs (se 3 (by rfl) ⟨7562, by rfl⟩) (B 15125 (by norm_num) ⟨7562, by rfl⟩ (by norm_num))
theorem R105893 : Reach 105893 := rs (se 4 (by rfl) ⟨9927, by rfl⟩) (B 19855 (by norm_num) ⟨9927, by rfl⟩ (by norm_num))
theorem R73133 : Reach 73133 := rs (se 3 (by rfl) ⟨13712, by rfl⟩) (B 27425 (by norm_num) ⟨13712, by rfl⟩ (by norm_num))
theorem R40429 : Reach 40429 := rs (se 3 (by rfl) ⟨7580, by rfl⟩) (B 15161 (by norm_num) ⟨7580, by rfl⟩ (by norm_num))
theorem R73205 : Reach 73205 := rs (se 5 (by rfl) ⟨3431, by rfl⟩) (B 6863 (by norm_num) ⟨3431, by rfl⟩ (by norm_num))
theorem R138773 : Reach 138773 := rs (se 6 (by rfl) ⟨3252, by rfl⟩) (B 6505 (by norm_num) ⟨3252, by rfl⟩ (by norm_num))
theorem R73277 : Reach 73277 := rs (se 3 (by rfl) ⟨13739, by rfl⟩) (B 27479 (by norm_num) ⟨13739, by rfl⟩ (by norm_num))
theorem R73325 : Reach 73325 := rs (se 3 (by rfl) ⟨13748, by rfl⟩) (B 27497 (by norm_num) ⟨13748, by rfl⟩ (by norm_num))
theorem R73333 : Reach 73333 := rs (se 5 (by rfl) ⟨3437, by rfl⟩) (B 6875 (by norm_num) ⟨3437, by rfl⟩ (by norm_num))
theorem R73349 : Reach 73349 := rs (se 4 (by rfl) ⟨6876, by rfl⟩) (B 13753 (by norm_num) ⟨6876, by rfl⟩ (by norm_num))
theorem R40601 : Reach 40601 := rs (se 2 (by rfl) ⟨15225, by rfl⟩) (B 30451 (by norm_num) ⟨15225, by rfl⟩ (by norm_num))
theorem R73421 : Reach 73421 := rs (se 3 (by rfl) ⟨13766, by rfl⟩) (B 27533 (by norm_num) ⟨13766, by rfl⟩ (by norm_num))
theorem R40657 : Reach 40657 := rs (se 2 (by rfl) ⟨15246, by rfl⟩) (B 30493 (by norm_num) ⟨15246, by rfl⟩ (by norm_num))
theorem R73493 : Reach 73493 := rs (se 6 (by rfl) ⟨1722, by rfl⟩) (B 3445 (by norm_num) ⟨1722, by rfl⟩ (by norm_num))
theorem R40753 : Reach 40753 := rs (se 2 (by rfl) ⟨15282, by rfl⟩) (B 30565 (by norm_num) ⟨15282, by rfl⟩ (by norm_num))
theorem R106309 : Reach 106309 := rs (se 4 (by rfl) ⟨9966, by rfl⟩) (B 19933 (by norm_num) ⟨9966, by rfl⟩ (by norm_num))
theorem R106325 : Reach 106325 := rs (se 9 (by rfl) ⟨311, by rfl⟩) (B 623 (by norm_num) ⟨311, by rfl⟩ (by norm_num))
theorem R73565 : Reach 73565 := rs (se 3 (by rfl) ⟨13793, by rfl⟩) (B 27587 (by norm_num) ⟨13793, by rfl⟩ (by norm_num))
theorem R40865 : Reach 40865 := rs (se 2 (by rfl) ⟨15324, by rfl⟩) (B 30649 (by norm_num) ⟨15324, by rfl⟩ (by norm_num))
theorem R73637 : Reach 73637 := rs (se 4 (by rfl) ⟨6903, by rfl⟩) (B 13807 (by norm_num) ⟨6903, by rfl⟩ (by norm_num))
theorem R40925 : Reach 40925 := rs (se 3 (by rfl) ⟨7673, by rfl⟩) (B 15347 (by norm_num) ⟨7673, by rfl⟩ (by norm_num))
theorem R73709 : Reach 73709 := rs (se 3 (by rfl) ⟨13820, by rfl⟩) (B 27641 (by norm_num) ⟨13820, by rfl⟩ (by norm_num))
theorem R40981 : Reach 40981 := rs (se 6 (by rfl) ⟨960, by rfl⟩) (B 1921 (by norm_num) ⟨960, by rfl⟩ (by norm_num))
theorem R73781 : Reach 73781 := rs (se 5 (by rfl) ⟨3458, by rfl⟩) (B 6917 (by norm_num) ⟨3458, by rfl⟩ (by norm_num))
theorem R41029 : Reach 41029 := rs (se 4 (by rfl) ⟨3846, by rfl⟩) (B 7693 (by norm_num) ⟨3846, by rfl⟩ (by norm_num))
theorem R41033 : Reach 41033 := rs (se 2 (by rfl) ⟨15387, by rfl⟩) (B 30775 (by norm_num) ⟨15387, by rfl⟩ (by norm_num))
theorem R237653 : Reach 237653 := rs (se 8 (by rfl) ⟨1392, by rfl⟩) (B 2785 (by norm_num) ⟨1392, by rfl⟩ (by norm_num))
theorem R41053 : Reach 41053 := rs (se 3 (by rfl) ⟨7697, by rfl⟩) (B 15395 (by norm_num) ⟨7697, by rfl⟩ (by norm_num))
theorem R41077 : Reach 41077 := rs (se 5 (by rfl) ⟨1925, by rfl⟩) (B 3851 (by norm_num) ⟨1925, by rfl⟩ (by norm_num))
theorem R73853 : Reach 73853 := rs (se 3 (by rfl) ⟨13847, by rfl⟩) (B 27695 (by norm_num) ⟨13847, by rfl⟩ (by norm_num))
theorem R139445 : Reach 139445 := rs (se 5 (by rfl) ⟨6536, by rfl⟩) (B 13073 (by norm_num) ⟨6536, by rfl⟩ (by norm_num))
theorem R73925 : Reach 73925 := rs (se 4 (by rfl) ⟨6930, by rfl⟩) (B 13861 (by norm_num) ⟨6930, by rfl⟩ (by norm_num))
theorem R106757 : Reach 106757 := rs (se 4 (by rfl) ⟨10008, by rfl⟩) (B 20017 (by norm_num) ⟨10008, by rfl⟩ (by norm_num))
theorem R73997 : Reach 73997 := rs (se 3 (by rfl) ⟨13874, by rfl⟩) (B 27749 (by norm_num) ⟨13874, by rfl⟩ (by norm_num))
theorem R41249 : Reach 41249 := rs (se 2 (by rfl) ⟨15468, by rfl⟩) (B 30937 (by norm_num) ⟨15468, by rfl⟩ (by norm_num))
theorem R74069 : Reach 74069 := rs (se 10 (by rfl) ⟨108, by rfl⟩) (B 217 (by norm_num) ⟨108, by rfl⟩ (by norm_num))
theorem R41305 : Reach 41305 := rs (se 2 (by rfl) ⟨15489, by rfl⟩) (B 30979 (by norm_num) ⟨15489, by rfl⟩ (by norm_num))
theorem R74141 : Reach 74141 := rs (se 3 (by rfl) ⟨13901, by rfl⟩) (B 27803 (by norm_num) ⟨13901, by rfl⟩ (by norm_num))
theorem R41401 : Reach 41401 := rs (se 2 (by rfl) ⟨15525, by rfl⟩) (B 31051 (by norm_num) ⟨15525, by rfl⟩ (by norm_num))
theorem R74213 : Reach 74213 := rs (se 4 (by rfl) ⟨6957, by rfl⟩) (B 13915 (by norm_num) ⟨6957, by rfl⟩ (by norm_num))
theorem R74285 : Reach 74285 := rs (se 3 (by rfl) ⟨13928, by rfl⟩) (B 27857 (by norm_num) ⟨13928, by rfl⟩ (by norm_num))
theorem R41573 : Reach 41573 := rs (se 4 (by rfl) ⟨3897, by rfl⟩) (B 7795 (by norm_num) ⟨3897, by rfl⟩ (by norm_num))
theorem R74357 : Reach 74357 := rs (se 5 (by rfl) ⟨3485, by rfl⟩) (B 6971 (by norm_num) ⟨3485, by rfl⟩ (by norm_num))
theorem R41629 : Reach 41629 := rs (se 3 (by rfl) ⟨7805, by rfl⟩) (B 15611 (by norm_num) ⟨7805, by rfl⟩ (by norm_num))
theorem R107189 : Reach 107189 := rs (se 5 (by rfl) ⟨5024, by rfl⟩) (B 10049 (by norm_num) ⟨5024, by rfl⟩ (by norm_num))
theorem R74429 : Reach 74429 := rs (se 3 (by rfl) ⟨13955, by rfl⟩) (B 27911 (by norm_num) ⟨13955, by rfl⟩ (by norm_num))
theorem R74461 : Reach 74461 := rs (se 3 (by rfl) ⟨13961, by rfl⟩) (B 27923 (by norm_num) ⟨13961, by rfl⟩ (by norm_num))
theorem R41725 : Reach 41725 := rs (se 3 (by rfl) ⟨7823, by rfl⟩) (B 15647 (by norm_num) ⟨7823, by rfl⟩ (by norm_num))
theorem R74501 : Reach 74501 := rs (se 4 (by rfl) ⟨6984, by rfl⟩) (B 13969 (by norm_num) ⟨6984, by rfl⟩ (by norm_num))
theorem R172853 : Reach 172853 := rs (se 5 (by rfl) ⟨8102, by rfl⟩) (B 16205 (by norm_num) ⟨8102, by rfl⟩ (by norm_num))
theorem R74573 : Reach 74573 := rs (se 3 (by rfl) ⟨13982, by rfl⟩) (B 27965 (by norm_num) ⟨13982, by rfl⟩ (by norm_num))
theorem R74645 : Reach 74645 := rs (se 6 (by rfl) ⟨1749, by rfl⟩) (B 3499 (by norm_num) ⟨1749, by rfl⟩ (by norm_num))
theorem R74717 : Reach 74717 := rs (se 3 (by rfl) ⟨14009, by rfl⟩) (B 28019 (by norm_num) ⟨14009, by rfl⟩ (by norm_num))
theorem R74789 : Reach 74789 := rs (se 4 (by rfl) ⟨7011, by rfl⟩) (B 14023 (by norm_num) ⟨7011, by rfl⟩ (by norm_num))
theorem R74837 : Reach 74837 := rs (se 8 (by rfl) ⟨438, by rfl⟩) (B 877 (by norm_num) ⟨438, by rfl⟩ (by norm_num))
theorem R42077 : Reach 42077 := rs (se 3 (by rfl) ⟨7889, by rfl⟩) (B 15779 (by norm_num) ⟨7889, by rfl⟩ (by norm_num))
theorem R107621 : Reach 107621 := rs (se 4 (by rfl) ⟨10089, by rfl⟩) (B 20179 (by norm_num) ⟨10089, by rfl⟩ (by norm_num))
theorem R74861 : Reach 74861 := rs (se 3 (by rfl) ⟨14036, by rfl⟩) (B 28073 (by norm_num) ⟨14036, by rfl⟩ (by norm_num))
theorem R107669 : Reach 107669 := rs (se 6 (by rfl) ⟨2523, by rfl⟩) (B 5047 (by norm_num) ⟨2523, by rfl⟩ (by norm_num))
theorem R74933 : Reach 74933 := rs (se 5 (by rfl) ⟨3512, by rfl⟩) (B 7025 (by norm_num) ⟨3512, by rfl⟩ (by norm_num))
theorem R42221 : Reach 42221 := rs (se 3 (by rfl) ⟨7916, by rfl⟩) (B 15833 (by norm_num) ⟨7916, by rfl⟩ (by norm_num))
theorem R75005 : Reach 75005 := rs (se 3 (by rfl) ⟨14063, by rfl⟩) (B 28127 (by norm_num) ⟨14063, by rfl⟩ (by norm_num))
theorem R140549 : Reach 140549 := rs (se 4 (by rfl) ⟨13176, by rfl⟩) (B 26353 (by norm_num) ⟨13176, by rfl⟩ (by norm_num))
theorem R42277 : Reach 42277 := rs (se 4 (by rfl) ⟨3963, by rfl⟩) (B 7927 (by norm_num) ⟨3963, by rfl⟩ (by norm_num))
theorem R75077 : Reach 75077 := rs (se 4 (by rfl) ⟨7038, by rfl⟩) (B 14077 (by norm_num) ⟨7038, by rfl⟩ (by norm_num))
theorem R42373 : Reach 42373 := rs (se 4 (by rfl) ⟨3972, by rfl⟩) (B 7945 (by norm_num) ⟨3972, by rfl⟩ (by norm_num))
theorem R75149 : Reach 75149 := rs (se 3 (by rfl) ⟨14090, by rfl⟩) (B 28181 (by norm_num) ⟨14090, by rfl⟩ (by norm_num))
theorem R75221 : Reach 75221 := rs (se 7 (by rfl) ⟨881, by rfl⟩) (B 1763 (by norm_num) ⟨881, by rfl⟩ (by norm_num))
theorem R42493 : Reach 42493 := rs (se 3 (by rfl) ⟨7967, by rfl⟩) (B 15935 (by norm_num) ⟨7967, by rfl⟩ (by norm_num))
theorem R108053 : Reach 108053 := rs (se 6 (by rfl) ⟨2532, by rfl⟩) (B 5065 (by norm_num) ⟨2532, by rfl⟩ (by norm_num))
theorem R75293 : Reach 75293 := rs (se 3 (by rfl) ⟨14117, by rfl⟩) (B 28235 (by norm_num) ⟨14117, by rfl⟩ (by norm_num))
theorem R42557 : Reach 42557 := rs (se 3 (by rfl) ⟨7979, by rfl⟩) (B 15959 (by norm_num) ⟨7979, by rfl⟩ (by norm_num))
theorem R75349 : Reach 75349 := rs (se 8 (by rfl) ⟨441, by rfl⟩) (B 883 (by norm_num) ⟨441, by rfl⟩ (by norm_num))
theorem R75365 : Reach 75365 := rs (se 4 (by rfl) ⟨7065, by rfl⟩) (B 14131 (by norm_num) ⟨7065, by rfl⟩ (by norm_num))
theorem R75437 : Reach 75437 := rs (se 3 (by rfl) ⟨14144, by rfl⟩) (B 28289 (by norm_num) ⟨14144, by rfl⟩ (by norm_num))
theorem R75485 : Reach 75485 := rs (se 3 (by rfl) ⟨14153, by rfl⟩) (B 28307 (by norm_num) ⟨14153, by rfl⟩ (by norm_num))
theorem R75509 : Reach 75509 := rs (se 5 (by rfl) ⟨3539, by rfl⟩) (B 7079 (by norm_num) ⟨3539, by rfl⟩ (by norm_num))
theorem R75581 : Reach 75581 := rs (se 3 (by rfl) ⟨14171, by rfl⟩) (B 28343 (by norm_num) ⟨14171, by rfl⟩ (by norm_num))
theorem R42869 : Reach 42869 := rs (se 5 (by rfl) ⟨2009, by rfl⟩) (B 4019 (by norm_num) ⟨2009, by rfl⟩ (by norm_num))
theorem R75653 : Reach 75653 := rs (se 4 (by rfl) ⟨7092, by rfl⟩) (B 14185 (by norm_num) ⟨7092, by rfl⟩ (by norm_num))
theorem R42925 : Reach 42925 := rs (se 3 (by rfl) ⟨8048, by rfl⟩) (B 16097 (by norm_num) ⟨8048, by rfl⟩ (by norm_num))
theorem R108485 : Reach 108485 := rs (se 4 (by rfl) ⟨10170, by rfl⟩) (B 20341 (by norm_num) ⟨10170, by rfl⟩ (by norm_num))
theorem R75725 : Reach 75725 := rs (se 3 (by rfl) ⟨14198, by rfl⟩) (B 28397 (by norm_num) ⟨14198, by rfl⟩ (by norm_num))
theorem R567253 : Reach 567253 := rs (se 7 (by rfl) ⟨6647, by rfl⟩) (B 13295 (by norm_num) ⟨6647, by rfl⟩ (by norm_num))
theorem R75757 : Reach 75757 := rs (se 3 (by rfl) ⟨14204, by rfl⟩) (B 28409 (by norm_num) ⟨14204, by rfl⟩ (by norm_num))
theorem R43021 : Reach 43021 := rs (se 3 (by rfl) ⟨8066, by rfl⟩) (B 16133 (by norm_num) ⟨8066, by rfl⟩ (by norm_num))
theorem R75797 : Reach 75797 := rs (se 6 (by rfl) ⟨1776, by rfl⟩) (B 3553 (by norm_num) ⟨1776, by rfl⟩ (by norm_num))
theorem R75869 : Reach 75869 := rs (se 3 (by rfl) ⟨14225, by rfl⟩) (B 28451 (by norm_num) ⟨14225, by rfl⟩ (by norm_num))
theorem R75941 : Reach 75941 := rs (se 4 (by rfl) ⟨7119, by rfl⟩) (B 14239 (by norm_num) ⟨7119, by rfl⟩ (by norm_num))
theorem R76013 : Reach 76013 := rs (se 3 (by rfl) ⟨14252, by rfl⟩) (B 28505 (by norm_num) ⟨14252, by rfl⟩ (by norm_num))
theorem R76085 : Reach 76085 := rs (se 5 (by rfl) ⟨3566, by rfl⟩) (B 7133 (by norm_num) ⟨3566, by rfl⟩ (by norm_num))
theorem R108917 : Reach 108917 := rs (se 5 (by rfl) ⟨5105, by rfl⟩) (B 10211 (by norm_num) ⟨5105, by rfl⟩ (by norm_num))
theorem R76157 : Reach 76157 := rs (se 3 (by rfl) ⟨14279, by rfl⟩) (B 28559 (by norm_num) ⟨14279, by rfl⟩ (by norm_num))
theorem R43429 : Reach 43429 := rs (se 4 (by rfl) ⟨4071, by rfl⟩) (B 8143 (by norm_num) ⟨4071, by rfl⟩ (by norm_num))
theorem R76229 : Reach 76229 := rs (se 4 (by rfl) ⟨7146, by rfl⟩) (B 14293 (by norm_num) ⟨7146, by rfl⟩ (by norm_num))
theorem R43517 : Reach 43517 := rs (se 3 (by rfl) ⟨8159, by rfl⟩) (B 16319 (by norm_num) ⟨8159, by rfl⟩ (by norm_num))
theorem R76301 : Reach 76301 := rs (se 3 (by rfl) ⟨14306, by rfl⟩) (B 28613 (by norm_num) ⟨14306, by rfl⟩ (by norm_num))
theorem R43573 : Reach 43573 := rs (se 5 (by rfl) ⟨2042, by rfl⟩) (B 4085 (by norm_num) ⟨2042, by rfl⟩ (by norm_num))
theorem R76349 : Reach 76349 := rs (se 3 (by rfl) ⟨14315, by rfl⟩) (B 28631 (by norm_num) ⟨14315, by rfl⟩ (by norm_num))
theorem R76373 : Reach 76373 := rs (se 8 (by rfl) ⟨447, by rfl⟩) (B 895 (by norm_num) ⟨447, by rfl⟩ (by norm_num))
theorem R43669 : Reach 43669 := rs (se 6 (by rfl) ⟨1023, by rfl⟩) (B 2047 (by norm_num) ⟨1023, by rfl⟩ (by norm_num))
theorem R76445 : Reach 76445 := rs (se 3 (by rfl) ⟨14333, by rfl⟩) (B 28667 (by norm_num) ⟨14333, by rfl⟩ (by norm_num))
theorem R76517 : Reach 76517 := rs (se 4 (by rfl) ⟨7173, by rfl⟩) (B 14347 (by norm_num) ⟨7173, by rfl⟩ (by norm_num))
theorem R109349 : Reach 109349 := rs (se 4 (by rfl) ⟨10251, by rfl⟩) (B 20503 (by norm_num) ⟨10251, by rfl⟩ (by norm_num))
theorem R76589 : Reach 76589 := rs (se 3 (by rfl) ⟨14360, by rfl⟩) (B 28721 (by norm_num) ⟨14360, by rfl⟩ (by norm_num))
theorem R76661 : Reach 76661 := rs (se 5 (by rfl) ⟨3593, by rfl⟩) (B 7187 (by norm_num) ⟨3593, by rfl⟩ (by norm_num))
theorem R76733 : Reach 76733 := rs (se 3 (by rfl) ⟨14387, by rfl⟩) (B 28775 (by norm_num) ⟨14387, by rfl⟩ (by norm_num))
theorem R76805 : Reach 76805 := rs (se 4 (by rfl) ⟨7200, by rfl⟩) (B 14401 (by norm_num) ⟨7200, by rfl⟩ (by norm_num))
theorem R76877 : Reach 76877 := rs (se 3 (by rfl) ⟨14414, by rfl⟩) (B 28829 (by norm_num) ⟨14414, by rfl⟩ (by norm_num))
theorem R44165 : Reach 44165 := rs (se 4 (by rfl) ⟨4140, by rfl⟩) (B 8281 (by norm_num) ⟨4140, by rfl⟩ (by norm_num))
theorem R76949 : Reach 76949 := rs (se 6 (by rfl) ⟨1803, by rfl⟩) (B 3607 (by norm_num) ⟨1803, by rfl⟩ (by norm_num))
theorem R44221 : Reach 44221 := rs (se 3 (by rfl) ⟨8291, by rfl⟩) (B 16583 (by norm_num) ⟨8291, by rfl⟩ (by norm_num))
theorem R109781 : Reach 109781 := rs (se 7 (by rfl) ⟨1286, by rfl⟩) (B 2573 (by norm_num) ⟨1286, by rfl⟩ (by norm_num))
theorem R77021 : Reach 77021 := rs (se 3 (by rfl) ⟨14441, by rfl⟩) (B 28883 (by norm_num) ⟨14441, by rfl⟩ (by norm_num))
theorem R44317 : Reach 44317 := rs (se 3 (by rfl) ⟨8309, by rfl⟩) (B 16619 (by norm_num) ⟨8309, by rfl⟩ (by norm_num))
theorem R77093 : Reach 77093 := rs (se 4 (by rfl) ⟨7227, by rfl⟩) (B 14455 (by norm_num) ⟨7227, by rfl⟩ (by norm_num))
theorem R175445 : Reach 175445 := rs (se 11 (by rfl) ⟨128, by rfl⟩) (B 257 (by norm_num) ⟨128, by rfl⟩ (by norm_num))
theorem R77165 : Reach 77165 := rs (se 3 (by rfl) ⟨14468, by rfl⟩) (B 28937 (by norm_num) ⟨14468, by rfl⟩ (by norm_num))
theorem R77237 : Reach 77237 := rs (se 5 (by rfl) ⟨3620, by rfl⟩) (B 7241 (by norm_num) ⟨3620, by rfl⟩ (by norm_num))
theorem R77309 : Reach 77309 := rs (se 3 (by rfl) ⟨14495, by rfl⟩) (B 28991 (by norm_num) ⟨14495, by rfl⟩ (by norm_num))
theorem R77381 : Reach 77381 := rs (se 4 (by rfl) ⟨7254, by rfl⟩) (B 14509 (by norm_num) ⟨7254, by rfl⟩ (by norm_num))
theorem R77429 : Reach 77429 := rs (se 5 (by rfl) ⟨3629, by rfl⟩) (B 7259 (by norm_num) ⟨3629, by rfl⟩ (by norm_num))
theorem R110213 : Reach 110213 := rs (se 4 (by rfl) ⟨10332, by rfl⟩) (B 20665 (by norm_num) ⟨10332, by rfl⟩ (by norm_num))
theorem R77453 : Reach 77453 := rs (se 3 (by rfl) ⟨14522, by rfl⟩) (B 29045 (by norm_num) ⟨14522, by rfl⟩ (by norm_num))
theorem R143045 : Reach 143045 := rs (se 4 (by rfl) ⟨13410, by rfl⟩) (B 26821 (by norm_num) ⟨13410, by rfl⟩ (by norm_num))
theorem R77525 : Reach 77525 := rs (se 7 (by rfl) ⟨908, by rfl⟩) (B 1817 (by norm_num) ⟨908, by rfl⟩ (by norm_num))
theorem R77597 : Reach 77597 := rs (se 3 (by rfl) ⟨14549, by rfl⟩) (B 29099 (by norm_num) ⟨14549, by rfl⟩ (by norm_num))
theorem R77669 : Reach 77669 := rs (se 4 (by rfl) ⟨7281, by rfl⟩) (B 14563 (by norm_num) ⟨7281, by rfl⟩ (by norm_num))
theorem R44965 : Reach 44965 := rs (se 4 (by rfl) ⟨4215, by rfl⟩) (B 8431 (by norm_num) ⟨4215, by rfl⟩ (by norm_num))
theorem R77741 : Reach 77741 := rs (se 3 (by rfl) ⟨14576, by rfl⟩) (B 29153 (by norm_num) ⟨14576, by rfl⟩ (by norm_num))
theorem R77813 : Reach 77813 := rs (se 5 (by rfl) ⟨3647, by rfl⟩) (B 7295 (by norm_num) ⟨3647, by rfl⟩ (by norm_num))
theorem R110645 : Reach 110645 := rs (se 5 (by rfl) ⟨5186, by rfl⟩) (B 10373 (by norm_num) ⟨5186, by rfl⟩ (by norm_num))
theorem R77885 : Reach 77885 := rs (se 3 (by rfl) ⟨14603, by rfl⟩) (B 29207 (by norm_num) ⟨14603, by rfl⟩ (by norm_num))
theorem R77957 : Reach 77957 := rs (se 4 (by rfl) ⟨7308, by rfl⟩) (B 14617 (by norm_num) ⟨7308, by rfl⟩ (by norm_num))
theorem R78029 : Reach 78029 := rs (se 3 (by rfl) ⟨14630, by rfl⟩) (B 29261 (by norm_num) ⟨14630, by rfl⟩ (by norm_num))
theorem R45293 : Reach 45293 := rs (se 3 (by rfl) ⟨8492, by rfl⟩) (B 16985 (by norm_num) ⟨8492, by rfl⟩ (by norm_num))
theorem R45301 : Reach 45301 := rs (se 5 (by rfl) ⟨2123, by rfl⟩) (B 4247 (by norm_num) ⟨2123, by rfl⟩ (by norm_num))
theorem R45325 : Reach 45325 := rs (se 3 (by rfl) ⟨8498, by rfl⟩) (B 16997 (by norm_num) ⟨8498, by rfl⟩ (by norm_num))
theorem R78101 : Reach 78101 := rs (se 6 (by rfl) ⟨1830, by rfl⟩) (B 3661 (by norm_num) ⟨1830, by rfl⟩ (by norm_num))
theorem R78173 : Reach 78173 := rs (se 3 (by rfl) ⟨14657, by rfl⟩) (B 29315 (by norm_num) ⟨14657, by rfl⟩ (by norm_num))
theorem R78245 : Reach 78245 := rs (se 4 (by rfl) ⟨7335, by rfl⟩) (B 14671 (by norm_num) ⟨7335, by rfl⟩ (by norm_num))
theorem R45517 : Reach 45517 := rs (se 3 (by rfl) ⟨8534, by rfl⟩) (B 17069 (by norm_num) ⟨8534, by rfl⟩ (by norm_num))
theorem R111077 : Reach 111077 := rs (se 4 (by rfl) ⟨10413, by rfl⟩) (B 20827 (by norm_num) ⟨10413, by rfl⟩ (by norm_num))
theorem R78317 : Reach 78317 := rs (se 3 (by rfl) ⟨14684, by rfl⟩) (B 29369 (by norm_num) ⟨14684, by rfl⟩ (by norm_num))
theorem R78389 : Reach 78389 := rs (se 5 (by rfl) ⟨3674, by rfl⟩) (B 7349 (by norm_num) ⟨3674, by rfl⟩ (by norm_num))
theorem R78461 : Reach 78461 := rs (se 3 (by rfl) ⟨14711, by rfl⟩) (B 29423 (by norm_num) ⟨14711, by rfl⟩ (by norm_num))
theorem R78533 : Reach 78533 := rs (se 4 (by rfl) ⟨7362, by rfl⟩) (B 14725 (by norm_num) ⟨7362, by rfl⟩ (by norm_num))
theorem R78605 : Reach 78605 := rs (se 3 (by rfl) ⟨14738, by rfl⟩) (B 29477 (by norm_num) ⟨14738, by rfl⟩ (by norm_num))
theorem R45893 : Reach 45893 := rs (se 4 (by rfl) ⟨4302, by rfl⟩) (B 8605 (by norm_num) ⟨4302, by rfl⟩ (by norm_num))
theorem R78677 : Reach 78677 := rs (se 9 (by rfl) ⟨230, by rfl⟩) (B 461 (by norm_num) ⟨230, by rfl⟩ (by norm_num))
theorem R78725 : Reach 78725 := rs (se 4 (by rfl) ⟨7380, by rfl⟩) (B 14761 (by norm_num) ⟨7380, by rfl⟩ (by norm_num))
theorem R111509 : Reach 111509 := rs (se 6 (by rfl) ⟨2613, by rfl⟩) (B 5227 (by norm_num) ⟨2613, by rfl⟩ (by norm_num))
theorem R78749 : Reach 78749 := rs (se 3 (by rfl) ⟨14765, by rfl⟩) (B 29531 (by norm_num) ⟨14765, by rfl⟩ (by norm_num))
theorem R78821 : Reach 78821 := rs (se 4 (by rfl) ⟨7389, by rfl⟩) (B 14779 (by norm_num) ⟨7389, by rfl⟩ (by norm_num))
theorem R78853 : Reach 78853 := rs (se 4 (by rfl) ⟨7392, by rfl⟩) (B 14785 (by norm_num) ⟨7392, by rfl⟩ (by norm_num))
theorem R46093 : Reach 46093 := rs (se 3 (by rfl) ⟨8642, by rfl⟩) (B 17285 (by norm_num) ⟨8642, by rfl⟩ (by norm_num))
theorem R78893 : Reach 78893 := rs (se 3 (by rfl) ⟨14792, by rfl⟩) (B 29585 (by norm_num) ⟨14792, by rfl⟩ (by norm_num))
theorem R78965 : Reach 78965 := rs (se 5 (by rfl) ⟨3701, by rfl⟩) (B 7403 (by norm_num) ⟨3701, by rfl⟩ (by norm_num))
theorem R373909 : Reach 373909 := rs (se 6 (by rfl) ⟨8763, by rfl⟩) (B 17527 (by norm_num) ⟨8763, by rfl⟩ (by norm_num))
theorem R79109 : Reach 79109 := rs (se 4 (by rfl) ⟨7416, by rfl⟩) (B 14833 (by norm_num) ⟨7416, by rfl⟩ (by norm_num))
theorem R79157 : Reach 79157 := rs (se 5 (by rfl) ⟨3710, by rfl⟩) (B 7421 (by norm_num) ⟨3710, by rfl⟩ (by norm_num))
theorem R111941 : Reach 111941 := rs (se 4 (by rfl) ⟨10494, by rfl⟩) (B 20989 (by norm_num) ⟨10494, by rfl⟩ (by norm_num))
theorem R144821 : Reach 144821 := rs (se 5 (by rfl) ⟨6788, by rfl⟩) (B 13577 (by norm_num) ⟨6788, by rfl⟩ (by norm_num))
theorem R79309 : Reach 79309 := rs (se 3 (by rfl) ⟨14870, by rfl⟩) (B 29741 (by norm_num) ⟨14870, by rfl⟩ (by norm_num))
theorem R46685 : Reach 46685 := rs (se 3 (by rfl) ⟨8753, by rfl⟩) (B 17507 (by norm_num) ⟨8753, by rfl⟩ (by norm_num))
theorem R46709 : Reach 46709 := rs (se 5 (by rfl) ⟨2189, by rfl⟩) (B 4379 (by norm_num) ⟨2189, by rfl⟩ (by norm_num))
theorem R46733 : Reach 46733 := rs (se 3 (by rfl) ⟨8762, by rfl⟩) (B 17525 (by norm_num) ⟨8762, by rfl⟩ (by norm_num))
theorem R79501 : Reach 79501 := rs (se 3 (by rfl) ⟨14906, by rfl⟩) (B 29813 (by norm_num) ⟨14906, by rfl⟩ (by norm_num))
theorem R46757 : Reach 46757 := rs (se 4 (by rfl) ⟨4383, by rfl⟩) (B 8767 (by norm_num) ⟨4383, by rfl⟩ (by norm_num))
theorem R145061 : Reach 145061 := rs (se 4 (by rfl) ⟨13599, by rfl⟩) (B 27199 (by norm_num) ⟨13599, by rfl⟩ (by norm_num))
theorem R46781 : Reach 46781 := rs (se 3 (by rfl) ⟨8771, by rfl⟩) (B 17543 (by norm_num) ⟨8771, by rfl⟩ (by norm_num))
theorem R46805 : Reach 46805 := rs (se 7 (by rfl) ⟨548, by rfl⟩) (B 1097 (by norm_num) ⟨548, by rfl⟩ (by norm_num))
theorem R112357 : Reach 112357 := rs (se 4 (by rfl) ⟨10533, by rfl⟩) (B 21067 (by norm_num) ⟨10533, by rfl⟩ (by norm_num))
theorem R46829 : Reach 46829 := rs (se 3 (by rfl) ⟨8780, by rfl⟩) (B 17561 (by norm_num) ⟨8780, by rfl⟩ (by norm_num))
theorem R112373 : Reach 112373 := rs (se 5 (by rfl) ⟨5267, by rfl⟩) (B 10535 (by norm_num) ⟨5267, by rfl⟩ (by norm_num))
theorem R79613 : Reach 79613 := rs (se 3 (by rfl) ⟨14927, by rfl⟩) (B 29855 (by norm_num) ⟨14927, by rfl⟩ (by norm_num))
theorem R46853 : Reach 46853 := rs (se 4 (by rfl) ⟨4392, by rfl⟩) (B 8785 (by norm_num) ⟨4392, by rfl⟩ (by norm_num))
theorem R46877 : Reach 46877 := rs (se 3 (by rfl) ⟨8789, by rfl⟩) (B 17579 (by norm_num) ⟨8789, by rfl⟩ (by norm_num))
theorem R46901 : Reach 46901 := rs (se 5 (by rfl) ⟨2198, by rfl⟩) (B 4397 (by norm_num) ⟨2198, by rfl⟩ (by norm_num))
theorem R46925 : Reach 46925 := rs (se 3 (by rfl) ⟨8798, by rfl⟩) (B 17597 (by norm_num) ⟨8798, by rfl⟩ (by norm_num))
theorem R46949 : Reach 46949 := rs (se 4 (by rfl) ⟨4401, by rfl⟩) (B 8803 (by norm_num) ⟨4401, by rfl⟩ (by norm_num))
theorem R178037 : Reach 178037 := rs (se 5 (by rfl) ⟨8345, by rfl⟩) (B 16691 (by norm_num) ⟨8345, by rfl⟩ (by norm_num))
theorem R46973 : Reach 46973 := rs (se 3 (by rfl) ⟨8807, by rfl⟩) (B 17615 (by norm_num) ⟨8807, by rfl⟩ (by norm_num))
theorem R46997 : Reach 46997 := rs (se 6 (by rfl) ⟨1101, by rfl⟩) (B 2203 (by norm_num) ⟨1101, by rfl⟩ (by norm_num))
theorem R47021 : Reach 47021 := rs (se 3 (by rfl) ⟨8816, by rfl⟩) (B 17633 (by norm_num) ⟨8816, by rfl⟩ (by norm_num))
theorem R79805 : Reach 79805 := rs (se 3 (by rfl) ⟨14963, by rfl⟩) (B 29927 (by norm_num) ⟨14963, by rfl⟩ (by norm_num))
theorem R47045 : Reach 47045 := rs (se 4 (by rfl) ⟨4410, by rfl⟩) (B 8821 (by norm_num) ⟨4410, by rfl⟩ (by norm_num))
theorem R47069 : Reach 47069 := rs (se 3 (by rfl) ⟨8825, by rfl⟩) (B 17651 (by norm_num) ⟨8825, by rfl⟩ (by norm_num))
theorem R47093 : Reach 47093 := rs (se 5 (by rfl) ⟨2207, by rfl⟩) (B 4415 (by norm_num) ⟨2207, by rfl⟩ (by norm_num))
theorem R47117 : Reach 47117 := rs (se 3 (by rfl) ⟨8834, by rfl⟩) (B 17669 (by norm_num) ⟨8834, by rfl⟩ (by norm_num))
theorem R47141 : Reach 47141 := rs (se 4 (by rfl) ⟨4419, by rfl⟩) (B 8839 (by norm_num) ⟨4419, by rfl⟩ (by norm_num))
theorem R47165 : Reach 47165 := rs (se 3 (by rfl) ⟨8843, by rfl⟩) (B 17687 (by norm_num) ⟨8843, by rfl⟩ (by norm_num))
theorem R47189 : Reach 47189 := rs (se 8 (by rfl) ⟨276, by rfl⟩) (B 553 (by norm_num) ⟨276, by rfl⟩ (by norm_num))
theorem R47213 : Reach 47213 := rs (se 3 (by rfl) ⟨8852, by rfl⟩) (B 17705 (by norm_num) ⟨8852, by rfl⟩ (by norm_num))
theorem R47237 : Reach 47237 := rs (se 4 (by rfl) ⟨4428, by rfl⟩) (B 8857 (by norm_num) ⟨4428, by rfl⟩ (by norm_num))
theorem R47261 : Reach 47261 := rs (se 3 (by rfl) ⟨8861, by rfl⟩) (B 17723 (by norm_num) ⟨8861, by rfl⟩ (by norm_num))
theorem R112805 : Reach 112805 := rs (se 4 (by rfl) ⟨10575, by rfl⟩) (B 21151 (by norm_num) ⟨10575, by rfl⟩ (by norm_num))
theorem R47285 : Reach 47285 := rs (se 5 (by rfl) ⟨2216, by rfl⟩) (B 4433 (by norm_num) ⟨2216, by rfl⟩ (by norm_num))
theorem R47309 : Reach 47309 := rs (se 3 (by rfl) ⟨8870, by rfl⟩) (B 17741 (by norm_num) ⟨8870, by rfl⟩ (by norm_num))
theorem R211157 : Reach 211157 := rs (se 7 (by rfl) ⟨2474, by rfl⟩) (B 4949 (by norm_num) ⟨2474, by rfl⟩ (by norm_num))
theorem R47317 : Reach 47317 := rs (se 7 (by rfl) ⟨554, by rfl⟩) (B 1109 (by norm_num) ⟨554, by rfl⟩ (by norm_num))
theorem R47333 : Reach 47333 := rs (se 4 (by rfl) ⟨4437, by rfl⟩) (B 8875 (by norm_num) ⟨4437, by rfl⟩ (by norm_num))
theorem R47357 : Reach 47357 := rs (se 3 (by rfl) ⟨8879, by rfl⟩) (B 17759 (by norm_num) ⟨8879, by rfl⟩ (by norm_num))
theorem R47381 : Reach 47381 := rs (se 6 (by rfl) ⟨1110, by rfl⟩) (B 2221 (by norm_num) ⟨1110, by rfl⟩ (by norm_num))
theorem R80149 : Reach 80149 := rs (se 6 (by rfl) ⟨1878, by rfl⟩) (B 3757 (by norm_num) ⟨1878, by rfl⟩ (by norm_num))
theorem R47405 : Reach 47405 := rs (se 3 (by rfl) ⟨8888, by rfl⟩) (B 17777 (by norm_num) ⟨8888, by rfl⟩ (by norm_num))
theorem R47429 : Reach 47429 := rs (se 4 (by rfl) ⟨4446, by rfl⟩) (B 8893 (by norm_num) ⟨4446, by rfl⟩ (by norm_num))
theorem R47453 : Reach 47453 := rs (se 3 (by rfl) ⟨8897, by rfl⟩) (B 17795 (by norm_num) ⟨8897, by rfl⟩ (by norm_num))
theorem R47477 : Reach 47477 := rs (se 5 (by rfl) ⟨2225, by rfl⟩) (B 4451 (by norm_num) ⟨2225, by rfl⟩ (by norm_num))
theorem R80261 : Reach 80261 := rs (se 4 (by rfl) ⟨7524, by rfl⟩) (B 15049 (by norm_num) ⟨7524, by rfl⟩ (by norm_num))
theorem R47501 : Reach 47501 := rs (se 3 (by rfl) ⟨8906, by rfl⟩) (B 17813 (by norm_num) ⟨8906, by rfl⟩ (by norm_num))
theorem R47525 : Reach 47525 := rs (se 4 (by rfl) ⟨4455, by rfl⟩) (B 8911 (by norm_num) ⟨4455, by rfl⟩ (by norm_num))
theorem R47549 : Reach 47549 := rs (se 3 (by rfl) ⟨8915, by rfl⟩) (B 17831 (by norm_num) ⟨8915, by rfl⟩ (by norm_num))
theorem R47573 : Reach 47573 := rs (se 7 (by rfl) ⟨557, by rfl⟩) (B 1115 (by norm_num) ⟨557, by rfl⟩ (by norm_num))
theorem R47597 : Reach 47597 := rs (se 3 (by rfl) ⟨8924, by rfl⟩) (B 17849 (by norm_num) ⟨8924, by rfl⟩ (by norm_num))
theorem R47621 : Reach 47621 := rs (se 4 (by rfl) ⟨4464, by rfl⟩) (B 8929 (by norm_num) ⟨4464, by rfl⟩ (by norm_num))
theorem R47645 : Reach 47645 := rs (se 3 (by rfl) ⟨8933, by rfl⟩) (B 17867 (by norm_num) ⟨8933, by rfl⟩ (by norm_num))
theorem R47669 : Reach 47669 := rs (se 5 (by rfl) ⟨2234, by rfl⟩) (B 4469 (by norm_num) ⟨2234, by rfl⟩ (by norm_num))
theorem R80453 : Reach 80453 := rs (se 4 (by rfl) ⟨7542, by rfl⟩) (B 15085 (by norm_num) ⟨7542, by rfl⟩ (by norm_num))
theorem R47693 : Reach 47693 := rs (se 3 (by rfl) ⟨8942, by rfl⟩) (B 17885 (by norm_num) ⟨8942, by rfl⟩ (by norm_num))
theorem R113237 : Reach 113237 := rs (se 8 (by rfl) ⟨663, by rfl⟩) (B 1327 (by norm_num) ⟨663, by rfl⟩ (by norm_num))
theorem R47717 : Reach 47717 := rs (se 4 (by rfl) ⟨4473, by rfl⟩) (B 8947 (by norm_num) ⟨4473, by rfl⟩ (by norm_num))
theorem R113269 : Reach 113269 := rs (se 5 (by rfl) ⟨5309, by rfl⟩) (B 10619 (by norm_num) ⟨5309, by rfl⟩ (by norm_num))
theorem R47741 : Reach 47741 := rs (se 3 (by rfl) ⟨8951, by rfl⟩) (B 17903 (by norm_num) ⟨8951, by rfl⟩ (by norm_num))
theorem R47765 : Reach 47765 := rs (se 6 (by rfl) ⟨1119, by rfl⟩) (B 2239 (by norm_num) ⟨1119, by rfl⟩ (by norm_num))
theorem R277141 : Reach 277141 := rs (se 6 (by rfl) ⟨6495, by rfl⟩) (B 12991 (by norm_num) ⟨6495, by rfl⟩ (by norm_num))
theorem R47789 : Reach 47789 := rs (se 3 (by rfl) ⟨8960, by rfl⟩) (B 17921 (by norm_num) ⟨8960, by rfl⟩ (by norm_num))
theorem R47813 : Reach 47813 := rs (se 4 (by rfl) ⟨4482, by rfl⟩) (B 8965 (by norm_num) ⟨4482, by rfl⟩ (by norm_num))
theorem R47837 : Reach 47837 := rs (se 3 (by rfl) ⟨8969, by rfl⟩) (B 17939 (by norm_num) ⟨8969, by rfl⟩ (by norm_num))
theorem R47861 : Reach 47861 := rs (se 5 (by rfl) ⟨2243, by rfl⟩) (B 4487 (by norm_num) ⟨2243, by rfl⟩ (by norm_num))
theorem R47885 : Reach 47885 := rs (se 3 (by rfl) ⟨8978, by rfl⟩) (B 17957 (by norm_num) ⟨8978, by rfl⟩ (by norm_num))
theorem R47909 : Reach 47909 := rs (se 4 (by rfl) ⟨4491, by rfl⟩) (B 8983 (by norm_num) ⟨4491, by rfl⟩ (by norm_num))
theorem R47933 : Reach 47933 := rs (se 3 (by rfl) ⟨8987, by rfl⟩) (B 17975 (by norm_num) ⟨8987, by rfl⟩ (by norm_num))
theorem R47957 : Reach 47957 := rs (se 9 (by rfl) ⟨140, by rfl⟩) (B 281 (by norm_num) ⟨140, by rfl⟩ (by norm_num))
theorem R47981 : Reach 47981 := rs (se 3 (by rfl) ⟨8996, by rfl⟩) (B 17993 (by norm_num) ⟨8996, by rfl⟩ (by norm_num))
theorem R47989 : Reach 47989 := rs (se 5 (by rfl) ⟨2249, by rfl⟩) (B 4499 (by norm_num) ⟨2249, by rfl⟩ (by norm_num))
theorem R48005 : Reach 48005 := rs (se 4 (by rfl) ⟨4500, by rfl⟩) (B 9001 (by norm_num) ⟨4500, by rfl⟩ (by norm_num))
theorem R80797 : Reach 80797 := rs (se 3 (by rfl) ⟨15149, by rfl⟩) (B 30299 (by norm_num) ⟨15149, by rfl⟩ (by norm_num))
theorem R48029 : Reach 48029 := rs (se 3 (by rfl) ⟨9005, by rfl⟩) (B 18011 (by norm_num) ⟨9005, by rfl⟩ (by norm_num))
theorem R48053 : Reach 48053 := rs (se 5 (by rfl) ⟨2252, by rfl⟩) (B 4505 (by norm_num) ⟨2252, by rfl⟩ (by norm_num))
theorem R48077 : Reach 48077 := rs (se 3 (by rfl) ⟨9014, by rfl⟩) (B 18029 (by norm_num) ⟨9014, by rfl⟩ (by norm_num))
theorem R48101 : Reach 48101 := rs (se 4 (by rfl) ⟨4509, by rfl⟩) (B 9019 (by norm_num) ⟨4509, by rfl⟩ (by norm_num))
theorem R48109 : Reach 48109 := rs (se 3 (by rfl) ⟨9020, by rfl⟩) (B 18041 (by norm_num) ⟨9020, by rfl⟩ (by norm_num))
theorem R80885 : Reach 80885 := rs (se 5 (by rfl) ⟨3791, by rfl⟩) (B 7583 (by norm_num) ⟨3791, by rfl⟩ (by norm_num))
theorem R48125 : Reach 48125 := rs (se 3 (by rfl) ⟨9023, by rfl⟩) (B 18047 (by norm_num) ⟨9023, by rfl⟩ (by norm_num))
theorem R113669 : Reach 113669 := rs (se 4 (by rfl) ⟨10656, by rfl⟩) (B 21313 (by norm_num) ⟨10656, by rfl⟩ (by norm_num))
theorem R80909 : Reach 80909 := rs (se 3 (by rfl) ⟨15170, by rfl⟩) (B 30341 (by norm_num) ⟨15170, by rfl⟩ (by norm_num))
theorem R48149 : Reach 48149 := rs (se 6 (by rfl) ⟨1128, by rfl⟩) (B 2257 (by norm_num) ⟨1128, by rfl⟩ (by norm_num))
theorem R48173 : Reach 48173 := rs (se 3 (by rfl) ⟨9032, by rfl⟩) (B 18065 (by norm_num) ⟨9032, by rfl⟩ (by norm_num))
theorem R113717 : Reach 113717 := rs (se 5 (by rfl) ⟨5330, by rfl⟩) (B 10661 (by norm_num) ⟨5330, by rfl⟩ (by norm_num))
theorem R48197 : Reach 48197 := rs (se 4 (by rfl) ⟨4518, by rfl⟩) (B 9037 (by norm_num) ⟨4518, by rfl⟩ (by norm_num))
theorem R48205 : Reach 48205 := rs (se 3 (by rfl) ⟨9038, by rfl⟩) (B 18077 (by norm_num) ⟨9038, by rfl⟩ (by norm_num))
theorem R48221 : Reach 48221 := rs (se 3 (by rfl) ⟨9041, by rfl⟩) (B 18083 (by norm_num) ⟨9041, by rfl⟩ (by norm_num))
theorem R48245 : Reach 48245 := rs (se 5 (by rfl) ⟨2261, by rfl⟩) (B 4523 (by norm_num) ⟨2261, by rfl⟩ (by norm_num))
theorem R48269 : Reach 48269 := rs (se 3 (by rfl) ⟨9050, by rfl⟩) (B 18101 (by norm_num) ⟨9050, by rfl⟩ (by norm_num))
theorem R48293 : Reach 48293 := rs (se 4 (by rfl) ⟨4527, by rfl⟩) (B 9055 (by norm_num) ⟨4527, by rfl⟩ (by norm_num))
theorem R48317 : Reach 48317 := rs (se 3 (by rfl) ⟨9059, by rfl⟩) (B 18119 (by norm_num) ⟨9059, by rfl⟩ (by norm_num))
theorem R113861 : Reach 113861 := rs (se 4 (by rfl) ⟨10674, by rfl⟩) (B 21349 (by norm_num) ⟨10674, by rfl⟩ (by norm_num))
theorem R81101 : Reach 81101 := rs (se 3 (by rfl) ⟨15206, by rfl⟩) (B 30413 (by norm_num) ⟨15206, by rfl⟩ (by norm_num))
theorem R48341 : Reach 48341 := rs (se 7 (by rfl) ⟨566, by rfl⟩) (B 1133 (by norm_num) ⟨566, by rfl⟩ (by norm_num))
theorem R48365 : Reach 48365 := rs (se 3 (by rfl) ⟨9068, by rfl⟩) (B 18137 (by norm_num) ⟨9068, by rfl⟩ (by norm_num))
theorem R48389 : Reach 48389 := rs (se 4 (by rfl) ⟨4536, by rfl⟩) (B 9073 (by norm_num) ⟨4536, by rfl⟩ (by norm_num))
theorem R48413 : Reach 48413 := rs (se 3 (by rfl) ⟨9077, by rfl⟩) (B 18155 (by norm_num) ⟨9077, by rfl⟩ (by norm_num))
theorem R48437 : Reach 48437 := rs (se 5 (by rfl) ⟨2270, by rfl⟩) (B 4541 (by norm_num) ⟨2270, by rfl⟩ (by norm_num))
theorem R48461 : Reach 48461 := rs (se 3 (by rfl) ⟨9086, by rfl⟩) (B 18173 (by norm_num) ⟨9086, by rfl⟩ (by norm_num))
theorem R48485 : Reach 48485 := rs (se 4 (by rfl) ⟨4545, by rfl⟩) (B 9091 (by norm_num) ⟨4545, by rfl⟩ (by norm_num))
theorem R48509 : Reach 48509 := rs (se 3 (by rfl) ⟨9095, by rfl⟩) (B 18191 (by norm_num) ⟨9095, by rfl⟩ (by norm_num))
theorem R48533 : Reach 48533 := rs (se 6 (by rfl) ⟨1137, by rfl⟩) (B 2275 (by norm_num) ⟨1137, by rfl⟩ (by norm_num))
theorem R48557 : Reach 48557 := rs (se 3 (by rfl) ⟨9104, by rfl⟩) (B 18209 (by norm_num) ⟨9104, by rfl⟩ (by norm_num))
theorem R114101 : Reach 114101 := rs (se 5 (by rfl) ⟨5348, by rfl⟩) (B 10697 (by norm_num) ⟨5348, by rfl⟩ (by norm_num))
theorem R48581 : Reach 48581 := rs (se 4 (by rfl) ⟨4554, by rfl⟩) (B 9109 (by norm_num) ⟨4554, by rfl⟩ (by norm_num))
theorem R48605 : Reach 48605 := rs (se 3 (by rfl) ⟨9113, by rfl⟩) (B 18227 (by norm_num) ⟨9113, by rfl⟩ (by norm_num))
theorem R48629 : Reach 48629 := rs (se 5 (by rfl) ⟨2279, by rfl⟩) (B 4559 (by norm_num) ⟨2279, by rfl⟩ (by norm_num))
theorem R48653 : Reach 48653 := rs (se 3 (by rfl) ⟨9122, by rfl⟩) (B 18245 (by norm_num) ⟨9122, by rfl⟩ (by norm_num))
theorem R81445 : Reach 81445 := rs (se 4 (by rfl) ⟨7635, by rfl⟩) (B 15271 (by norm_num) ⟨7635, by rfl⟩ (by norm_num))
theorem R48677 : Reach 48677 := rs (se 4 (by rfl) ⟨4563, by rfl⟩) (B 9127 (by norm_num) ⟨4563, by rfl⟩ (by norm_num))
theorem R48701 : Reach 48701 := rs (se 3 (by rfl) ⟨9131, by rfl⟩) (B 18263 (by norm_num) ⟨9131, by rfl⟩ (by norm_num))
theorem R48725 : Reach 48725 := rs (se 8 (by rfl) ⟨285, by rfl⟩) (B 571 (by norm_num) ⟨285, by rfl⟩ (by norm_num))
theorem R48749 : Reach 48749 := rs (se 3 (by rfl) ⟨9140, by rfl⟩) (B 18281 (by norm_num) ⟨9140, by rfl⟩ (by norm_num))
theorem R48773 : Reach 48773 := rs (se 4 (by rfl) ⟨4572, by rfl⟩) (B 9145 (by norm_num) ⟨4572, by rfl⟩ (by norm_num))
theorem R81557 : Reach 81557 := rs (se 6 (by rfl) ⟨1911, by rfl⟩) (B 3823 (by norm_num) ⟨1911, by rfl⟩ (by norm_num))
theorem R48797 : Reach 48797 := rs (se 3 (by rfl) ⟨9149, by rfl⟩) (B 18299 (by norm_num) ⟨9149, by rfl⟩ (by norm_num))
theorem R245429 : Reach 245429 := rs (se 5 (by rfl) ⟨11504, by rfl⟩) (B 23009 (by norm_num) ⟨11504, by rfl⟩ (by norm_num))
theorem R48821 : Reach 48821 := rs (se 5 (by rfl) ⟨2288, by rfl⟩) (B 4577 (by norm_num) ⟨2288, by rfl⟩ (by norm_num))
theorem R48845 : Reach 48845 := rs (se 3 (by rfl) ⟨9158, by rfl⟩) (B 18317 (by norm_num) ⟨9158, by rfl⟩ (by norm_num))
theorem R114389 : Reach 114389 := rs (se 7 (by rfl) ⟨1340, by rfl⟩) (B 2681 (by norm_num) ⟨1340, by rfl⟩ (by norm_num))
theorem R48869 : Reach 48869 := rs (se 4 (by rfl) ⟨4581, by rfl⟩) (B 9163 (by norm_num) ⟨4581, by rfl⟩ (by norm_num))
theorem R48893 : Reach 48893 := rs (se 3 (by rfl) ⟨9167, by rfl⟩) (B 18335 (by norm_num) ⟨9167, by rfl⟩ (by norm_num))
theorem R48917 : Reach 48917 := rs (se 6 (by rfl) ⟨1146, by rfl⟩) (B 2293 (by norm_num) ⟨1146, by rfl⟩ (by norm_num))
theorem R48941 : Reach 48941 := rs (se 3 (by rfl) ⟨9176, by rfl⟩) (B 18353 (by norm_num) ⟨9176, by rfl⟩ (by norm_num))
theorem R48965 : Reach 48965 := rs (se 4 (by rfl) ⟨4590, by rfl⟩) (B 9181 (by norm_num) ⟨4590, by rfl⟩ (by norm_num))
theorem R81749 : Reach 81749 := rs (se 9 (by rfl) ⟨239, by rfl⟩) (B 479 (by norm_num) ⟨239, by rfl⟩ (by norm_num))
theorem R48989 : Reach 48989 := rs (se 3 (by rfl) ⟨9185, by rfl⟩) (B 18371 (by norm_num) ⟨9185, by rfl⟩ (by norm_num))
theorem R114533 : Reach 114533 := rs (se 4 (by rfl) ⟨10737, by rfl⟩) (B 21475 (by norm_num) ⟨10737, by rfl⟩ (by norm_num))
theorem R49013 : Reach 49013 := rs (se 5 (by rfl) ⟨2297, by rfl⟩) (B 4595 (by norm_num) ⟨2297, by rfl⟩ (by norm_num))
theorem R49037 : Reach 49037 := rs (se 3 (by rfl) ⟨9194, by rfl⟩) (B 18389 (by norm_num) ⟨9194, by rfl⟩ (by norm_num))
theorem R147349 : Reach 147349 := rs (se 6 (by rfl) ⟨3453, by rfl⟩) (B 6907 (by norm_num) ⟨3453, by rfl⟩ (by norm_num))
theorem R49061 : Reach 49061 := rs (se 4 (by rfl) ⟨4599, by rfl⟩) (B 9199 (by norm_num) ⟨4599, by rfl⟩ (by norm_num))
theorem R49085 : Reach 49085 := rs (se 3 (by rfl) ⟨9203, by rfl⟩) (B 18407 (by norm_num) ⟨9203, by rfl⟩ (by norm_num))
theorem R49109 : Reach 49109 := rs (se 7 (by rfl) ⟨575, by rfl⟩) (B 1151 (by norm_num) ⟨575, by rfl⟩ (by norm_num))
theorem R49133 : Reach 49133 := rs (se 3 (by rfl) ⟨9212, by rfl⟩) (B 18425 (by norm_num) ⟨9212, by rfl⟩ (by norm_num))
theorem R49157 : Reach 49157 := rs (se 4 (by rfl) ⟨4608, by rfl⟩) (B 9217 (by norm_num) ⟨4608, by rfl⟩ (by norm_num))
theorem R180245 : Reach 180245 := rs (se 6 (by rfl) ⟨4224, by rfl⟩) (B 8449 (by norm_num) ⟨4224, by rfl⟩ (by norm_num))
theorem R49181 : Reach 49181 := rs (se 3 (by rfl) ⟨9221, by rfl⟩) (B 18443 (by norm_num) ⟨9221, by rfl⟩ (by norm_num))
theorem R49205 : Reach 49205 := rs (se 5 (by rfl) ⟨2306, by rfl⟩) (B 4613 (by norm_num) ⟨2306, by rfl⟩ (by norm_num))
theorem R49229 : Reach 49229 := rs (se 3 (by rfl) ⟨9230, by rfl⟩) (B 18461 (by norm_num) ⟨9230, by rfl⟩ (by norm_num))
theorem R49253 : Reach 49253 := rs (se 4 (by rfl) ⟨4617, by rfl⟩) (B 9235 (by norm_num) ⟨4617, by rfl⟩ (by norm_num))
theorem R49277 : Reach 49277 := rs (se 3 (by rfl) ⟨9239, by rfl⟩) (B 18479 (by norm_num) ⟨9239, by rfl⟩ (by norm_num))
theorem R49301 : Reach 49301 := rs (se 6 (by rfl) ⟨1155, by rfl⟩) (B 2311 (by norm_num) ⟨1155, by rfl⟩ (by norm_num))
theorem R82093 : Reach 82093 := rs (se 3 (by rfl) ⟨15392, by rfl⟩) (B 30785 (by norm_num) ⟨15392, by rfl⟩ (by norm_num))
theorem R49325 : Reach 49325 := rs (se 3 (by rfl) ⟨9248, by rfl⟩) (B 18497 (by norm_num) ⟨9248, by rfl⟩ (by norm_num))
theorem R114869 : Reach 114869 := rs (se 5 (by rfl) ⟨5384, by rfl⟩) (B 10769 (by norm_num) ⟨5384, by rfl⟩ (by norm_num))
theorem R49349 : Reach 49349 := rs (se 4 (by rfl) ⟨4626, by rfl⟩) (B 9253 (by norm_num) ⟨4626, by rfl⟩ (by norm_num))
theorem R49373 : Reach 49373 := rs (se 3 (by rfl) ⟨9257, by rfl⟩) (B 18515 (by norm_num) ⟨9257, by rfl⟩ (by norm_num))
theorem R49397 : Reach 49397 := rs (se 5 (by rfl) ⟨2315, by rfl⟩) (B 4631 (by norm_num) ⟨2315, by rfl⟩ (by norm_num))
theorem R49421 : Reach 49421 := rs (se 3 (by rfl) ⟨9266, by rfl⟩) (B 18533 (by norm_num) ⟨9266, by rfl⟩ (by norm_num))
theorem R114965 : Reach 114965 := rs (se 6 (by rfl) ⟨2694, by rfl⟩) (B 5389 (by norm_num) ⟨2694, by rfl⟩ (by norm_num))
theorem R82205 : Reach 82205 := rs (se 3 (by rfl) ⟨15413, by rfl⟩) (B 30827 (by norm_num) ⟨15413, by rfl⟩ (by norm_num))
theorem R49445 : Reach 49445 := rs (se 4 (by rfl) ⟨4635, by rfl⟩) (B 9271 (by norm_num) ⟨4635, by rfl⟩ (by norm_num))
theorem R49469 : Reach 49469 := rs (se 3 (by rfl) ⟨9275, by rfl⟩) (B 18551 (by norm_num) ⟨9275, by rfl⟩ (by norm_num))
theorem R49493 : Reach 49493 := rs (se 10 (by rfl) ⟨72, by rfl⟩) (B 145 (by norm_num) ⟨72, by rfl⟩ (by norm_num))
theorem R49517 : Reach 49517 := rs (se 3 (by rfl) ⟨9284, by rfl⟩) (B 18569 (by norm_num) ⟨9284, by rfl⟩ (by norm_num))
theorem R82301 : Reach 82301 := rs (se 3 (by rfl) ⟨15431, by rfl⟩) (B 30863 (by norm_num) ⟨15431, by rfl⟩ (by norm_num))
theorem R49541 : Reach 49541 := rs (se 4 (by rfl) ⟨4644, by rfl⟩) (B 9289 (by norm_num) ⟨4644, by rfl⟩ (by norm_num))
theorem R82309 : Reach 82309 := rs (se 4 (by rfl) ⟨7716, by rfl⟩) (B 15433 (by norm_num) ⟨7716, by rfl⟩ (by norm_num))
theorem R49565 : Reach 49565 := rs (se 3 (by rfl) ⟨9293, by rfl⟩) (B 18587 (by norm_num) ⟨9293, by rfl⟩ (by norm_num))
theorem R49589 : Reach 49589 := rs (se 5 (by rfl) ⟨2324, by rfl⟩) (B 4649 (by norm_num) ⟨2324, by rfl⟩ (by norm_num))
theorem R49613 : Reach 49613 := rs (se 3 (by rfl) ⟨9302, by rfl⟩) (B 18605 (by norm_num) ⟨9302, by rfl⟩ (by norm_num))
theorem R82397 : Reach 82397 := rs (se 3 (by rfl) ⟨15449, by rfl⟩) (B 30899 (by norm_num) ⟨15449, by rfl⟩ (by norm_num))
theorem R49637 : Reach 49637 := rs (se 4 (by rfl) ⟨4653, by rfl⟩) (B 9307 (by norm_num) ⟨4653, by rfl⟩ (by norm_num))
theorem R49661 : Reach 49661 := rs (se 3 (by rfl) ⟨9311, by rfl⟩) (B 18623 (by norm_num) ⟨9311, by rfl⟩ (by norm_num))
theorem R49685 : Reach 49685 := rs (se 6 (by rfl) ⟨1164, by rfl⟩) (B 2329 (by norm_num) ⟨1164, by rfl⟩ (by norm_num))
theorem R49709 : Reach 49709 := rs (se 3 (by rfl) ⟨9320, by rfl⟩) (B 18641 (by norm_num) ⟨9320, by rfl⟩ (by norm_num))
theorem R49733 : Reach 49733 := rs (se 4 (by rfl) ⟨4662, by rfl⟩) (B 9325 (by norm_num) ⟨4662, by rfl⟩ (by norm_num))
theorem R49757 : Reach 49757 := rs (se 3 (by rfl) ⟨9329, by rfl⟩) (B 18659 (by norm_num) ⟨9329, by rfl⟩ (by norm_num))
theorem R148085 : Reach 148085 := rs (se 5 (by rfl) ⟨6941, by rfl⟩) (B 13883 (by norm_num) ⟨6941, by rfl⟩ (by norm_num))
theorem R49781 : Reach 49781 := rs (se 5 (by rfl) ⟨2333, by rfl⟩) (B 4667 (by norm_num) ⟨2333, by rfl⟩ (by norm_num))
theorem R49805 : Reach 49805 := rs (se 3 (by rfl) ⟨9338, by rfl⟩) (B 18677 (by norm_num) ⟨9338, by rfl⟩ (by norm_num))
theorem R49829 : Reach 49829 := rs (se 4 (by rfl) ⟨4671, by rfl⟩) (B 9343 (by norm_num) ⟨4671, by rfl⟩ (by norm_num))
theorem R49853 : Reach 49853 := rs (se 3 (by rfl) ⟨9347, by rfl⟩) (B 18695 (by norm_num) ⟨9347, by rfl⟩ (by norm_num))
theorem R115397 : Reach 115397 := rs (se 4 (by rfl) ⟨10818, by rfl⟩) (B 21637 (by norm_num) ⟨10818, by rfl⟩ (by norm_num))
theorem R49877 : Reach 49877 := rs (se 7 (by rfl) ⟨584, by rfl⟩) (B 1169 (by norm_num) ⟨584, by rfl⟩ (by norm_num))
theorem R49901 : Reach 49901 := rs (se 3 (by rfl) ⟨9356, by rfl⟩) (B 18713 (by norm_num) ⟨9356, by rfl⟩ (by norm_num))
theorem R49925 : Reach 49925 := rs (se 4 (by rfl) ⟨4680, by rfl⟩) (B 9361 (by norm_num) ⟨4680, by rfl⟩ (by norm_num))
theorem R377621 : Reach 377621 := rs (se 6 (by rfl) ⟨8850, by rfl⟩) (B 17701 (by norm_num) ⟨8850, by rfl⟩ (by norm_num))
theorem R49949 : Reach 49949 := rs (se 3 (by rfl) ⟨9365, by rfl⟩) (B 18731 (by norm_num) ⟨9365, by rfl⟩ (by norm_num))
theorem R82741 : Reach 82741 := rs (se 5 (by rfl) ⟨3878, by rfl⟩) (B 7757 (by norm_num) ⟨3878, by rfl⟩ (by norm_num))
theorem R49973 : Reach 49973 := rs (se 5 (by rfl) ⟨2342, by rfl⟩) (B 4685 (by norm_num) ⟨2342, by rfl⟩ (by norm_num))
theorem R49997 : Reach 49997 := rs (se 3 (by rfl) ⟨9374, by rfl⟩) (B 18749 (by norm_num) ⟨9374, by rfl⟩ (by norm_num))
theorem R50021 : Reach 50021 := rs (se 4 (by rfl) ⟨4689, by rfl⟩) (B 9379 (by norm_num) ⟨4689, by rfl⟩ (by norm_num))
theorem R50045 : Reach 50045 := rs (se 3 (by rfl) ⟨9383, by rfl⟩) (B 18767 (by norm_num) ⟨9383, by rfl⟩ (by norm_num))
theorem R50069 : Reach 50069 := rs (se 6 (by rfl) ⟨1173, by rfl⟩) (B 2347 (by norm_num) ⟨1173, by rfl⟩ (by norm_num))
theorem R82853 : Reach 82853 := rs (se 4 (by rfl) ⟨7767, by rfl⟩) (B 15535 (by norm_num) ⟨7767, by rfl⟩ (by norm_num))
theorem R50093 : Reach 50093 := rs (se 3 (by rfl) ⟨9392, by rfl⟩) (B 18785 (by norm_num) ⟨9392, by rfl⟩ (by norm_num))
theorem R50117 : Reach 50117 := rs (se 4 (by rfl) ⟨4698, by rfl⟩) (B 9397 (by norm_num) ⟨4698, by rfl⟩ (by norm_num))
theorem R50141 : Reach 50141 := rs (se 3 (by rfl) ⟨9401, by rfl⟩) (B 18803 (by norm_num) ⟨9401, by rfl⟩ (by norm_num))
theorem R50165 : Reach 50165 := rs (se 5 (by rfl) ⟨2351, by rfl⟩) (B 4703 (by norm_num) ⟨2351, by rfl⟩ (by norm_num))
theorem R50189 : Reach 50189 := rs (se 3 (by rfl) ⟨9410, by rfl⟩) (B 18821 (by norm_num) ⟨9410, by rfl⟩ (by norm_num))
theorem R50213 : Reach 50213 := rs (se 4 (by rfl) ⟨4707, by rfl⟩) (B 9415 (by norm_num) ⟨4707, by rfl⟩ (by norm_num))
theorem R82981 : Reach 82981 := rs (se 4 (by rfl) ⟨7779, by rfl⟩) (B 15559 (by norm_num) ⟨7779, by rfl⟩ (by norm_num))
theorem R50237 : Reach 50237 := rs (se 3 (by rfl) ⟨9419, by rfl⟩) (B 18839 (by norm_num) ⟨9419, by rfl⟩ (by norm_num))
theorem R50261 : Reach 50261 := rs (se 8 (by rfl) ⟨294, by rfl⟩) (B 589 (by norm_num) ⟨294, by rfl⟩ (by norm_num))
theorem R83045 : Reach 83045 := rs (se 4 (by rfl) ⟨7785, by rfl⟩) (B 15571 (by norm_num) ⟨7785, by rfl⟩ (by norm_num))
theorem R50285 : Reach 50285 := rs (se 3 (by rfl) ⟨9428, by rfl⟩) (B 18857 (by norm_num) ⟨9428, by rfl⟩ (by norm_num))
theorem R115829 : Reach 115829 := rs (se 5 (by rfl) ⟨5429, by rfl⟩) (B 10859 (by norm_num) ⟨5429, by rfl⟩ (by norm_num))
theorem R50309 : Reach 50309 := rs (se 4 (by rfl) ⟨4716, by rfl⟩) (B 9433 (by norm_num) ⟨4716, by rfl⟩ (by norm_num))
theorem R50333 : Reach 50333 := rs (se 3 (by rfl) ⟨9437, by rfl⟩) (B 18875 (by norm_num) ⟨9437, by rfl⟩ (by norm_num))
theorem R50357 : Reach 50357 := rs (se 5 (by rfl) ⟨2360, by rfl⟩) (B 4721 (by norm_num) ⟨2360, by rfl⟩ (by norm_num))
theorem R50381 : Reach 50381 := rs (se 3 (by rfl) ⟨9446, by rfl⟩) (B 18893 (by norm_num) ⟨9446, by rfl⟩ (by norm_num))
theorem R50405 : Reach 50405 := rs (se 4 (by rfl) ⟨4725, by rfl⟩) (B 9451 (by norm_num) ⟨4725, by rfl⟩ (by norm_num))
theorem R50429 : Reach 50429 := rs (se 3 (by rfl) ⟨9455, by rfl⟩) (B 18911 (by norm_num) ⟨9455, by rfl⟩ (by norm_num))
theorem R50453 : Reach 50453 := rs (se 6 (by rfl) ⟨1182, by rfl⟩) (B 2365 (by norm_num) ⟨1182, by rfl⟩ (by norm_num))
theorem R50477 : Reach 50477 := rs (se 3 (by rfl) ⟨9464, by rfl⟩) (B 18929 (by norm_num) ⟨9464, by rfl⟩ (by norm_num))
theorem R50501 : Reach 50501 := rs (se 4 (by rfl) ⟨4734, by rfl⟩) (B 9469 (by norm_num) ⟨4734, by rfl⟩ (by norm_num))
theorem R50525 : Reach 50525 := rs (se 3 (by rfl) ⟨9473, by rfl⟩) (B 18947 (by norm_num) ⟨9473, by rfl⟩ (by norm_num))
theorem R148837 : Reach 148837 := rs (se 4 (by rfl) ⟨13953, by rfl⟩) (B 27907 (by norm_num) ⟨13953, by rfl⟩ (by norm_num))
theorem R50549 : Reach 50549 := rs (se 5 (by rfl) ⟨2369, by rfl⟩) (B 4739 (by norm_num) ⟨2369, by rfl⟩ (by norm_num))
theorem R148853 : Reach 148853 := rs (se 5 (by rfl) ⟨6977, by rfl⟩) (B 13955 (by norm_num) ⟨6977, by rfl⟩ (by norm_num))
theorem R50573 : Reach 50573 := rs (se 3 (by rfl) ⟨9482, by rfl⟩) (B 18965 (by norm_num) ⟨9482, by rfl⟩ (by norm_num))
theorem R50597 : Reach 50597 := rs (se 4 (by rfl) ⟨4743, by rfl⟩) (B 9487 (by norm_num) ⟨4743, by rfl⟩ (by norm_num))
theorem R50621 : Reach 50621 := rs (se 3 (by rfl) ⟨9491, by rfl⟩) (B 18983 (by norm_num) ⟨9491, by rfl⟩ (by norm_num))
theorem R50645 : Reach 50645 := rs (se 7 (by rfl) ⟨593, by rfl⟩) (B 1187 (by norm_num) ⟨593, by rfl⟩ (by norm_num))
theorem R50669 : Reach 50669 := rs (se 3 (by rfl) ⟨9500, by rfl⟩) (B 19001 (by norm_num) ⟨9500, by rfl⟩ (by norm_num))
theorem R50693 : Reach 50693 := rs (se 4 (by rfl) ⟨4752, by rfl⟩) (B 9505 (by norm_num) ⟨4752, by rfl⟩ (by norm_num))
theorem R50717 : Reach 50717 := rs (se 3 (by rfl) ⟨9509, by rfl⟩) (B 19019 (by norm_num) ⟨9509, by rfl⟩ (by norm_num))
theorem R116261 : Reach 116261 := rs (se 4 (by rfl) ⟨10899, by rfl⟩) (B 21799 (by norm_num) ⟨10899, by rfl⟩ (by norm_num))
theorem R50741 : Reach 50741 := rs (se 5 (by rfl) ⟨2378, by rfl⟩) (B 4757 (by norm_num) ⟨2378, by rfl⟩ (by norm_num))
theorem R50765 : Reach 50765 := rs (se 3 (by rfl) ⟨9518, by rfl⟩) (B 19037 (by norm_num) ⟨9518, by rfl⟩ (by norm_num))
theorem R50789 : Reach 50789 := rs (se 4 (by rfl) ⟨4761, by rfl⟩) (B 9523 (by norm_num) ⟨4761, by rfl⟩ (by norm_num))
theorem R50797 : Reach 50797 := rs (se 3 (by rfl) ⟨9524, by rfl⟩) (B 19049 (by norm_num) ⟨9524, by rfl⟩ (by norm_num))
theorem R50813 : Reach 50813 := rs (se 3 (by rfl) ⟨9527, by rfl⟩) (B 19055 (by norm_num) ⟨9527, by rfl⟩ (by norm_num))
theorem R50837 : Reach 50837 := rs (se 6 (by rfl) ⟨1191, by rfl⟩) (B 2383 (by norm_num) ⟨1191, by rfl⟩ (by norm_num))
theorem R50861 : Reach 50861 := rs (se 3 (by rfl) ⟨9536, by rfl⟩) (B 19073 (by norm_num) ⟨9536, by rfl⟩ (by norm_num))
theorem R50885 : Reach 50885 := rs (se 4 (by rfl) ⟨4770, by rfl⟩) (B 9541 (by norm_num) ⟨4770, by rfl⟩ (by norm_num))
theorem R50909 : Reach 50909 := rs (se 3 (by rfl) ⟨9545, by rfl⟩) (B 19091 (by norm_num) ⟨9545, by rfl⟩ (by norm_num))
theorem R50933 : Reach 50933 := rs (se 5 (by rfl) ⟨2387, by rfl⟩) (B 4775 (by norm_num) ⟨2387, by rfl⟩ (by norm_num))
theorem R50957 : Reach 50957 := rs (se 3 (by rfl) ⟨9554, by rfl⟩) (B 19109 (by norm_num) ⟨9554, by rfl⟩ (by norm_num))
theorem R50981 : Reach 50981 := rs (se 4 (by rfl) ⟨4779, by rfl⟩) (B 9559 (by norm_num) ⟨4779, by rfl⟩ (by norm_num))
theorem R51005 : Reach 51005 := rs (se 3 (by rfl) ⟨9563, by rfl⟩) (B 19127 (by norm_num) ⟨9563, by rfl⟩ (by norm_num))
theorem R51029 : Reach 51029 := rs (se 9 (by rfl) ⟨149, by rfl⟩) (B 299 (by norm_num) ⟨149, by rfl⟩ (by norm_num))
theorem R51053 : Reach 51053 := rs (se 3 (by rfl) ⟨9572, by rfl⟩) (B 19145 (by norm_num) ⟨9572, by rfl⟩ (by norm_num))
theorem R51077 : Reach 51077 := rs (se 4 (by rfl) ⟨4788, by rfl⟩) (B 9577 (by norm_num) ⟨4788, by rfl⟩ (by norm_num))
theorem R83861 : Reach 83861 := rs (se 6 (by rfl) ⟨1965, by rfl⟩) (B 3931 (by norm_num) ⟨1965, by rfl⟩ (by norm_num))
theorem R51101 : Reach 51101 := rs (se 3 (by rfl) ⟨9581, by rfl⟩) (B 19163 (by norm_num) ⟨9581, by rfl⟩ (by norm_num))
theorem R51125 : Reach 51125 := rs (se 5 (by rfl) ⟨2396, by rfl⟩) (B 4793 (by norm_num) ⟨2396, by rfl⟩ (by norm_num))
theorem R51133 : Reach 51133 := rs (se 3 (by rfl) ⟨9587, by rfl⟩) (B 19175 (by norm_num) ⟨9587, by rfl⟩ (by norm_num))
theorem R51149 : Reach 51149 := rs (se 3 (by rfl) ⟨9590, by rfl⟩) (B 19181 (by norm_num) ⟨9590, by rfl⟩ (by norm_num))
theorem R116693 : Reach 116693 := rs (se 7 (by rfl) ⟨1367, by rfl⟩) (B 2735 (by norm_num) ⟨1367, by rfl⟩ (by norm_num))
theorem R51173 : Reach 51173 := rs (se 4 (by rfl) ⟨4797, by rfl⟩) (B 9595 (by norm_num) ⟨4797, by rfl⟩ (by norm_num))
theorem R51197 : Reach 51197 := rs (se 3 (by rfl) ⟨9599, by rfl⟩) (B 19199 (by norm_num) ⟨9599, by rfl⟩ (by norm_num))
theorem R51221 : Reach 51221 := rs (se 6 (by rfl) ⟨1200, by rfl⟩) (B 2401 (by norm_num) ⟨1200, by rfl⟩ (by norm_num))
theorem R51245 : Reach 51245 := rs (se 3 (by rfl) ⟨9608, by rfl⟩) (B 19217 (by norm_num) ⟨9608, by rfl⟩ (by norm_num))
theorem R84037 : Reach 84037 := rs (se 4 (by rfl) ⟨7878, by rfl⟩) (B 15757 (by norm_num) ⟨7878, by rfl⟩ (by norm_num))
theorem R51269 : Reach 51269 := rs (se 4 (by rfl) ⟨4806, by rfl⟩) (B 9613 (by norm_num) ⟨4806, by rfl⟩ (by norm_num))
theorem R51293 : Reach 51293 := rs (se 3 (by rfl) ⟨9617, by rfl⟩) (B 19235 (by norm_num) ⟨9617, by rfl⟩ (by norm_num))
theorem R51317 : Reach 51317 := rs (se 5 (by rfl) ⟨2405, by rfl⟩) (B 4811 (by norm_num) ⟨2405, by rfl⟩ (by norm_num))
theorem R51341 : Reach 51341 := rs (se 3 (by rfl) ⟨9626, by rfl⟩) (B 19253 (by norm_num) ⟨9626, by rfl⟩ (by norm_num))
theorem R51365 : Reach 51365 := rs (se 4 (by rfl) ⟨4815, by rfl⟩) (B 9631 (by norm_num) ⟨4815, by rfl⟩ (by norm_num))
theorem R84149 : Reach 84149 := rs (se 5 (by rfl) ⟨3944, by rfl⟩) (B 7889 (by norm_num) ⟨3944, by rfl⟩ (by norm_num))
theorem R51389 : Reach 51389 := rs (se 3 (by rfl) ⟨9635, by rfl⟩) (B 19271 (by norm_num) ⟨9635, by rfl⟩ (by norm_num))
theorem R51413 : Reach 51413 := rs (se 7 (by rfl) ⟨602, by rfl⟩) (B 1205 (by norm_num) ⟨602, by rfl⟩ (by norm_num))
theorem R248021 : Reach 248021 := rs (se 7 (by rfl) ⟨2906, by rfl⟩) (B 5813 (by norm_num) ⟨2906, by rfl⟩ (by norm_num))
theorem R51437 : Reach 51437 := rs (se 3 (by rfl) ⟨9644, by rfl⟩) (B 19289 (by norm_num) ⟨9644, by rfl⟩ (by norm_num))
theorem R51461 : Reach 51461 := rs (se 4 (by rfl) ⟨4824, by rfl⟩) (B 9649 (by norm_num) ⟨4824, by rfl⟩ (by norm_num))
theorem R51485 : Reach 51485 := rs (se 3 (by rfl) ⟨9653, by rfl⟩) (B 19307 (by norm_num) ⟨9653, by rfl⟩ (by norm_num))
theorem R51509 : Reach 51509 := rs (se 5 (by rfl) ⟨2414, by rfl⟩) (B 4829 (by norm_num) ⟨2414, by rfl⟩ (by norm_num))
theorem R51533 : Reach 51533 := rs (se 3 (by rfl) ⟨9662, by rfl⟩) (B 19325 (by norm_num) ⟨9662, by rfl⟩ (by norm_num))
theorem R51557 : Reach 51557 := rs (se 4 (by rfl) ⟨4833, by rfl⟩) (B 9667 (by norm_num) ⟨4833, by rfl⟩ (by norm_num))
theorem R84341 : Reach 84341 := rs (se 5 (by rfl) ⟨3953, by rfl⟩) (B 7907 (by norm_num) ⟨3953, by rfl⟩ (by norm_num))
theorem R51581 : Reach 51581 := rs (se 3 (by rfl) ⟨9671, by rfl⟩) (B 19343 (by norm_num) ⟨9671, by rfl⟩ (by norm_num))
theorem R117125 : Reach 117125 := rs (se 4 (by rfl) ⟨10980, by rfl⟩) (B 21961 (by norm_num) ⟨10980, by rfl⟩ (by norm_num))
theorem R346517 : Reach 346517 := rs (se 6 (by rfl) ⟨8121, by rfl⟩) (B 16243 (by norm_num) ⟨8121, by rfl⟩ (by norm_num))
theorem R51605 : Reach 51605 := rs (se 6 (by rfl) ⟨1209, by rfl⟩) (B 2419 (by norm_num) ⟨1209, by rfl⟩ (by norm_num))
theorem R51629 : Reach 51629 := rs (se 3 (by rfl) ⟨9680, by rfl⟩) (B 19361 (by norm_num) ⟨9680, by rfl⟩ (by norm_num))
theorem R51653 : Reach 51653 := rs (se 4 (by rfl) ⟨4842, by rfl⟩) (B 9685 (by norm_num) ⟨4842, by rfl⟩ (by norm_num))
theorem R51677 : Reach 51677 := rs (se 3 (by rfl) ⟨9689, by rfl⟩) (B 19379 (by norm_num) ⟨9689, by rfl⟩ (by norm_num))
theorem R51701 : Reach 51701 := rs (se 5 (by rfl) ⟨2423, by rfl⟩) (B 4847 (by norm_num) ⟨2423, by rfl⟩ (by norm_num))
theorem R51725 : Reach 51725 := rs (se 3 (by rfl) ⟨9698, by rfl⟩) (B 19397 (by norm_num) ⟨9698, by rfl⟩ (by norm_num))
theorem R51749 : Reach 51749 := rs (se 4 (by rfl) ⟨4851, by rfl⟩) (B 9703 (by norm_num) ⟨4851, by rfl⟩ (by norm_num))
theorem R182837 : Reach 182837 := rs (se 5 (by rfl) ⟨8570, by rfl⟩) (B 17141 (by norm_num) ⟨8570, by rfl⟩ (by norm_num))
theorem R51773 : Reach 51773 := rs (se 3 (by rfl) ⟨9707, by rfl⟩) (B 19415 (by norm_num) ⟨9707, by rfl⟩ (by norm_num))
theorem R51797 : Reach 51797 := rs (se 8 (by rfl) ⟨303, by rfl⟩) (B 607 (by norm_num) ⟨303, by rfl⟩ (by norm_num))
theorem R51821 : Reach 51821 := rs (se 3 (by rfl) ⟨9716, by rfl⟩) (B 19433 (by norm_num) ⟨9716, by rfl⟩ (by norm_num))
theorem R51845 : Reach 51845 := rs (se 4 (by rfl) ⟨4860, by rfl⟩) (B 9721 (by norm_num) ⟨4860, by rfl⟩ (by norm_num))
theorem R51869 : Reach 51869 := rs (se 3 (by rfl) ⟨9725, by rfl⟩) (B 19451 (by norm_num) ⟨9725, by rfl⟩ (by norm_num))
theorem R51893 : Reach 51893 := rs (se 5 (by rfl) ⟨2432, by rfl⟩) (B 4865 (by norm_num) ⟨2432, by rfl⟩ (by norm_num))
theorem R51917 : Reach 51917 := rs (se 3 (by rfl) ⟨9734, by rfl⟩) (B 19469 (by norm_num) ⟨9734, by rfl⟩ (by norm_num))
theorem R51941 : Reach 51941 := rs (se 4 (by rfl) ⟨4869, by rfl⟩) (B 9739 (by norm_num) ⟨4869, by rfl⟩ (by norm_num))
theorem R51965 : Reach 51965 := rs (se 3 (by rfl) ⟨9743, by rfl⟩) (B 19487 (by norm_num) ⟨9743, by rfl⟩ (by norm_num))
theorem R51989 : Reach 51989 := rs (se 6 (by rfl) ⟨1218, by rfl⟩) (B 2437 (by norm_num) ⟨1218, by rfl⟩ (by norm_num))
theorem R52013 : Reach 52013 := rs (se 3 (by rfl) ⟨9752, by rfl⟩) (B 19505 (by norm_num) ⟨9752, by rfl⟩ (by norm_num))
theorem R117557 : Reach 117557 := rs (se 5 (by rfl) ⟨5510, by rfl⟩) (B 11021 (by norm_num) ⟨5510, by rfl⟩ (by norm_num))
theorem R52037 : Reach 52037 := rs (se 4 (by rfl) ⟨4878, by rfl⟩) (B 9757 (by norm_num) ⟨4878, by rfl⟩ (by norm_num))
theorem R52061 : Reach 52061 := rs (se 3 (by rfl) ⟨9761, by rfl⟩) (B 19523 (by norm_num) ⟨9761, by rfl⟩ (by norm_num))
theorem R52085 : Reach 52085 := rs (se 5 (by rfl) ⟨2441, by rfl⟩) (B 4883 (by norm_num) ⟨2441, by rfl⟩ (by norm_num))
theorem R52109 : Reach 52109 := rs (se 3 (by rfl) ⟨9770, by rfl⟩) (B 19541 (by norm_num) ⟨9770, by rfl⟩ (by norm_num))
theorem R52133 : Reach 52133 := rs (se 4 (by rfl) ⟨4887, by rfl⟩) (B 9775 (by norm_num) ⟨4887, by rfl⟩ (by norm_num))
theorem R52157 : Reach 52157 := rs (se 3 (by rfl) ⟨9779, by rfl⟩) (B 19559 (by norm_num) ⟨9779, by rfl⟩ (by norm_num))
theorem R52181 : Reach 52181 := rs (se 7 (by rfl) ⟨611, by rfl⟩) (B 1223 (by norm_num) ⟨611, by rfl⟩ (by norm_num))
theorem R52205 : Reach 52205 := rs (se 3 (by rfl) ⟨9788, by rfl⟩) (B 19577 (by norm_num) ⟨9788, by rfl⟩ (by norm_num))
theorem R52229 : Reach 52229 := rs (se 4 (by rfl) ⟨4896, by rfl⟩) (B 9793 (by norm_num) ⟨4896, by rfl⟩ (by norm_num))
theorem R52253 : Reach 52253 := rs (se 3 (by rfl) ⟨9797, by rfl⟩) (B 19595 (by norm_num) ⟨9797, by rfl⟩ (by norm_num))
theorem R52277 : Reach 52277 := rs (se 5 (by rfl) ⟨2450, by rfl⟩) (B 4901 (by norm_num) ⟨2450, by rfl⟩ (by norm_num))
theorem R52301 : Reach 52301 := rs (se 3 (by rfl) ⟨9806, by rfl⟩) (B 19613 (by norm_num) ⟨9806, by rfl⟩ (by norm_num))
theorem R52325 : Reach 52325 := rs (se 4 (by rfl) ⟨4905, by rfl⟩) (B 9811 (by norm_num) ⟨4905, by rfl⟩ (by norm_num))
theorem R52349 : Reach 52349 := rs (se 3 (by rfl) ⟨9815, by rfl⟩) (B 19631 (by norm_num) ⟨9815, by rfl⟩ (by norm_num))
theorem R117893 : Reach 117893 := rs (se 4 (by rfl) ⟨11052, by rfl⟩) (B 22105 (by norm_num) ⟨11052, by rfl⟩ (by norm_num))
theorem R52373 : Reach 52373 := rs (se 6 (by rfl) ⟨1227, by rfl⟩) (B 2455 (by norm_num) ⟨1227, by rfl⟩ (by norm_num))
theorem R52397 : Reach 52397 := rs (se 3 (by rfl) ⟨9824, by rfl⟩) (B 19649 (by norm_num) ⟨9824, by rfl⟩ (by norm_num))
theorem R52421 : Reach 52421 := rs (se 4 (by rfl) ⟨4914, by rfl⟩) (B 9829 (by norm_num) ⟨4914, by rfl⟩ (by norm_num))
theorem R52445 : Reach 52445 := rs (se 3 (by rfl) ⟨9833, by rfl⟩) (B 19667 (by norm_num) ⟨9833, by rfl⟩ (by norm_num))
theorem R117989 : Reach 117989 := rs (se 4 (by rfl) ⟨11061, by rfl⟩) (B 22123 (by norm_num) ⟨11061, by rfl⟩ (by norm_num))
theorem R52469 : Reach 52469 := rs (se 5 (by rfl) ⟨2459, by rfl⟩) (B 4919 (by norm_num) ⟨2459, by rfl⟩ (by norm_num))
theorem R52493 : Reach 52493 := rs (se 3 (by rfl) ⟨9842, by rfl⟩) (B 19685 (by norm_num) ⟨9842, by rfl⟩ (by norm_num))
theorem R52517 : Reach 52517 := rs (se 4 (by rfl) ⟨4923, by rfl⟩) (B 9847 (by norm_num) ⟨4923, by rfl⟩ (by norm_num))
theorem R52541 : Reach 52541 := rs (se 3 (by rfl) ⟨9851, by rfl⟩) (B 19703 (by norm_num) ⟨9851, by rfl⟩ (by norm_num))
theorem R85333 : Reach 85333 := rs (se 11 (by rfl) ⟨62, by rfl⟩) (B 125 (by norm_num) ⟨62, by rfl⟩ (by norm_num))
theorem R52565 : Reach 52565 := rs (se 11 (by rfl) ⟨38, by rfl⟩) (B 77 (by norm_num) ⟨38, by rfl⟩ (by norm_num))
theorem R52589 : Reach 52589 := rs (se 3 (by rfl) ⟨9860, by rfl⟩) (B 19721 (by norm_num) ⟨9860, by rfl⟩ (by norm_num))
theorem R52613 : Reach 52613 := rs (se 4 (by rfl) ⟨4932, by rfl⟩) (B 9865 (by norm_num) ⟨4932, by rfl⟩ (by norm_num))
theorem R52637 : Reach 52637 := rs (se 3 (by rfl) ⟨9869, by rfl⟩) (B 19739 (by norm_num) ⟨9869, by rfl⟩ (by norm_num))
theorem R52661 : Reach 52661 := rs (se 5 (by rfl) ⟨2468, by rfl⟩) (B 4937 (by norm_num) ⟨2468, by rfl⟩ (by norm_num))
theorem R85445 : Reach 85445 := rs (se 4 (by rfl) ⟨8010, by rfl⟩) (B 16021 (by norm_num) ⟨8010, by rfl⟩ (by norm_num))
theorem R52693 : Reach 52693 := rs (se 7 (by rfl) ⟨617, by rfl⟩) (B 1235 (by norm_num) ⟨617, by rfl⟩ (by norm_num))
theorem R52717 : Reach 52717 := rs (se 3 (by rfl) ⟨9884, by rfl⟩) (B 19769 (by norm_num) ⟨9884, by rfl⟩ (by norm_num))
theorem R52805 : Reach 52805 := rs (se 4 (by rfl) ⟨4950, by rfl⟩) (B 9901 (by norm_num) ⟨4950, by rfl⟩ (by norm_num))
theorem R85637 : Reach 85637 := rs (se 4 (by rfl) ⟨8028, by rfl⟩) (B 16057 (by norm_num) ⟨8028, by rfl⟩ (by norm_num))
theorem R118421 : Reach 118421 := rs (se 6 (by rfl) ⟨2775, by rfl⟩) (B 5551 (by norm_num) ⟨2775, by rfl⟩ (by norm_num))
theorem R52933 : Reach 52933 := rs (se 4 (by rfl) ⟨4962, by rfl⟩) (B 9925 (by norm_num) ⟨4962, by rfl⟩ (by norm_num))
theorem R151237 : Reach 151237 := rs (se 4 (by rfl) ⟨14178, by rfl⟩) (B 28357 (by norm_num) ⟨14178, by rfl⟩ (by norm_num))
theorem R53021 : Reach 53021 := rs (se 3 (by rfl) ⟨9941, by rfl⟩) (B 19883 (by norm_num) ⟨9941, by rfl⟩ (by norm_num))
theorem R53149 : Reach 53149 := rs (se 3 (by rfl) ⟨9965, by rfl⟩) (B 19931 (by norm_num) ⟨9965, by rfl⟩ (by norm_num))
theorem R53237 : Reach 53237 := rs (se 5 (by rfl) ⟨2495, by rfl⟩) (B 4991 (by norm_num) ⟨2495, by rfl⟩ (by norm_num))
theorem R53365 : Reach 53365 := rs (se 5 (by rfl) ⟨2501, by rfl⟩) (B 5003 (by norm_num) ⟨2501, by rfl⟩ (by norm_num))
theorem R151733 : Reach 151733 := rs (se 5 (by rfl) ⟨7112, by rfl⟩) (B 14225 (by norm_num) ⟨7112, by rfl⟩ (by norm_num))
theorem R250037 : Reach 250037 := rs (se 5 (by rfl) ⟨11720, by rfl⟩) (B 23441 (by norm_num) ⟨11720, by rfl⟩ (by norm_num))
theorem R53453 : Reach 53453 := rs (se 3 (by rfl) ⟨10022, by rfl⟩) (B 20045 (by norm_num) ⟨10022, by rfl⟩ (by norm_num))
theorem R217333 : Reach 217333 := rs (se 5 (by rfl) ⟨10187, by rfl⟩) (B 20375 (by norm_num) ⟨10187, by rfl⟩ (by norm_num))
theorem R53581 : Reach 53581 := rs (se 3 (by rfl) ⟨10046, by rfl⟩) (B 20093 (by norm_num) ⟨10046, by rfl⟩ (by norm_num))
theorem R53669 : Reach 53669 := rs (se 4 (by rfl) ⟨5031, by rfl⟩) (B 10063 (by norm_num) ⟨5031, by rfl⟩ (by norm_num))
theorem R53797 : Reach 53797 := rs (se 4 (by rfl) ⟨5043, by rfl⟩) (B 10087 (by norm_num) ⟨5043, by rfl⟩ (by norm_num))
theorem R53821 : Reach 53821 := rs (se 3 (by rfl) ⟨10091, by rfl⟩) (B 20183 (by norm_num) ⟨10091, by rfl⟩ (by norm_num))
theorem R86629 : Reach 86629 := rs (se 4 (by rfl) ⟨8121, by rfl⟩) (B 16243 (by norm_num) ⟨8121, by rfl⟩ (by norm_num))
theorem R53885 : Reach 53885 := rs (se 3 (by rfl) ⟨10103, by rfl⟩) (B 20207 (by norm_num) ⟨10103, by rfl⟩ (by norm_num))
theorem R86741 : Reach 86741 := rs (se 7 (by rfl) ⟨1016, by rfl⟩) (B 2033 (by norm_num) ⟨1016, by rfl⟩ (by norm_num))
theorem R54013 : Reach 54013 := rs (se 3 (by rfl) ⟨10127, by rfl⟩) (B 20255 (by norm_num) ⟨10127, by rfl⟩ (by norm_num))
theorem R54037 : Reach 54037 := rs (se 6 (by rfl) ⟨1266, by rfl⟩) (B 2533 (by norm_num) ⟨1266, by rfl⟩ (by norm_num))
theorem R54101 : Reach 54101 := rs (se 9 (by rfl) ⟨158, by rfl⟩) (B 317 (by norm_num) ⟨158, by rfl⟩ (by norm_num))
theorem R86933 : Reach 86933 := rs (se 6 (by rfl) ⟨2037, by rfl⟩) (B 4075 (by norm_num) ⟨2037, by rfl⟩ (by norm_num))
theorem R54229 : Reach 54229 := rs (se 7 (by rfl) ⟨635, by rfl⟩) (B 1271 (by norm_num) ⟨635, by rfl⟩ (by norm_num))
theorem R807893 : Reach 807893 := rs (se 7 (by rfl) ⟨9467, by rfl⟩) (B 18935 (by norm_num) ⟨9467, by rfl⟩ (by norm_num))
theorem R54245 : Reach 54245 := rs (se 4 (by rfl) ⟨5085, by rfl⟩) (B 10171 (by norm_num) ⟨5085, by rfl⟩ (by norm_num))
theorem R54317 : Reach 54317 := rs (se 3 (by rfl) ⟨10184, by rfl⟩) (B 20369 (by norm_num) ⟨10184, by rfl⟩ (by norm_num))
theorem R119893 : Reach 119893 := rs (se 8 (by rfl) ⟨702, by rfl⟩) (B 1405 (by norm_num) ⟨702, by rfl⟩ (by norm_num))
theorem R250997 : Reach 250997 := rs (se 5 (by rfl) ⟨11765, by rfl⟩) (B 23531 (by norm_num) ⟨11765, by rfl⟩ (by norm_num))
theorem R54445 : Reach 54445 := rs (se 3 (by rfl) ⟨10208, by rfl⟩) (B 20417 (by norm_num) ⟨10208, by rfl⟩ (by norm_num))
theorem R54533 : Reach 54533 := rs (se 4 (by rfl) ⟨5112, by rfl⟩) (B 10225 (by norm_num) ⟨5112, by rfl⟩ (by norm_num))
theorem R120149 : Reach 120149 := rs (se 15 (by rfl) ⟨5, by rfl⟩) (B 11 (by norm_num) ⟨5, by rfl⟩ (by norm_num))
theorem R54661 : Reach 54661 := rs (se 4 (by rfl) ⟨5124, by rfl⟩) (B 10249 (by norm_num) ⟨5124, by rfl⟩ (by norm_num))
theorem R87493 : Reach 87493 := rs (se 4 (by rfl) ⟨8202, by rfl⟩) (B 16405 (by norm_num) ⟨8202, by rfl⟩ (by norm_num))
theorem R54749 : Reach 54749 := rs (se 3 (by rfl) ⟨10265, by rfl⟩) (B 20531 (by norm_num) ⟨10265, by rfl⟩ (by norm_num))
theorem R54877 : Reach 54877 := rs (se 3 (by rfl) ⟨10289, by rfl⟩) (B 20579 (by norm_num) ⟨10289, by rfl⟩ (by norm_num))
theorem R120437 : Reach 120437 := rs (se 5 (by rfl) ⟨5645, by rfl⟩) (B 11291 (by norm_num) ⟨5645, by rfl⟩ (by norm_num))
theorem R54965 : Reach 54965 := rs (se 5 (by rfl) ⟨2576, by rfl⟩) (B 5153 (by norm_num) ⟨2576, by rfl⟩ (by norm_num))
theorem R55093 : Reach 55093 := rs (se 5 (by rfl) ⟨2582, by rfl⟩) (B 5165 (by norm_num) ⟨2582, by rfl⟩ (by norm_num))
theorem R87925 : Reach 87925 := rs (se 5 (by rfl) ⟨4121, by rfl⟩) (B 8243 (by norm_num) ⟨4121, by rfl⟩ (by norm_num))
theorem R55181 : Reach 55181 := rs (se 3 (by rfl) ⟨10346, by rfl⟩) (B 20693 (by norm_num) ⟨10346, by rfl⟩ (by norm_num))
theorem R88037 : Reach 88037 := rs (se 4 (by rfl) ⟨8253, by rfl⟩) (B 16507 (by norm_num) ⟨8253, by rfl⟩ (by norm_num))
theorem R55309 : Reach 55309 := rs (se 3 (by rfl) ⟨10370, by rfl⟩) (B 20741 (by norm_num) ⟨10370, by rfl⟩ (by norm_num))
theorem R55333 : Reach 55333 := rs (se 4 (by rfl) ⟨5187, by rfl⟩) (B 10375 (by norm_num) ⟨5187, by rfl⟩ (by norm_num))
theorem R55397 : Reach 55397 := rs (se 4 (by rfl) ⟨5193, by rfl⟩) (B 10387 (by norm_num) ⟨5193, by rfl⟩ (by norm_num))
theorem R88229 : Reach 88229 := rs (se 4 (by rfl) ⟨8271, by rfl⟩) (B 16543 (by norm_num) ⟨8271, by rfl⟩ (by norm_num))
theorem R55525 : Reach 55525 := rs (se 4 (by rfl) ⟨5205, by rfl⟩) (B 10411 (by norm_num) ⟨5205, by rfl⟩ (by norm_num))
theorem R55613 : Reach 55613 := rs (se 3 (by rfl) ⟨10427, by rfl⟩) (B 20855 (by norm_num) ⟨10427, by rfl⟩ (by norm_num))
theorem R252341 : Reach 252341 := rs (se 5 (by rfl) ⟨11828, by rfl⟩) (B 23657 (by norm_num) ⟨11828, by rfl⟩ (by norm_num))
theorem R55741 : Reach 55741 := rs (se 3 (by rfl) ⟨10451, by rfl⟩) (B 20903 (by norm_num) ⟨10451, by rfl⟩ (by norm_num))
theorem R55829 : Reach 55829 := rs (se 6 (by rfl) ⟨1308, by rfl⟩) (B 2617 (by norm_num) ⟨1308, by rfl⟩ (by norm_num))
theorem R318005 : Reach 318005 := rs (se 5 (by rfl) ⟨14906, by rfl⟩) (B 29813 (by norm_num) ⟨14906, by rfl⟩ (by norm_num))
theorem R55885 : Reach 55885 := rs (se 3 (by rfl) ⟨10478, by rfl⟩) (B 20957 (by norm_num) ⟨10478, by rfl⟩ (by norm_num))
theorem R88661 : Reach 88661 := rs (se 8 (by rfl) ⟨519, by rfl⟩) (B 1039 (by norm_num) ⟨519, by rfl⟩ (by norm_num))
theorem R121445 : Reach 121445 := rs (se 4 (by rfl) ⟨11385, by rfl⟩) (B 22771 (by norm_num) ⟨11385, by rfl⟩ (by norm_num))
theorem R55957 : Reach 55957 := rs (se 6 (by rfl) ⟨1311, by rfl⟩) (B 2623 (by norm_num) ⟨1311, by rfl⟩ (by norm_num))
theorem R56045 : Reach 56045 := rs (se 3 (by rfl) ⟨10508, by rfl⟩) (B 21017 (by norm_num) ⟨10508, by rfl⟩ (by norm_num))
theorem R121621 : Reach 121621 := rs (se 6 (by rfl) ⟨2850, by rfl⟩) (B 5701 (by norm_num) ⟨2850, by rfl⟩ (by norm_num))
theorem R56141 : Reach 56141 := rs (se 3 (by rfl) ⟨10526, by rfl⟩) (B 21053 (by norm_num) ⟨10526, by rfl⟩ (by norm_num))
theorem R56173 : Reach 56173 := rs (se 3 (by rfl) ⟨10532, by rfl⟩) (B 21065 (by norm_num) ⟨10532, by rfl⟩ (by norm_num))
theorem R121733 : Reach 121733 := rs (se 4 (by rfl) ⟨11412, by rfl⟩) (B 22825 (by norm_num) ⟨11412, by rfl⟩ (by norm_num))
theorem R56261 : Reach 56261 := rs (se 4 (by rfl) ⟨5274, by rfl⟩) (B 10549 (by norm_num) ⟨5274, by rfl⟩ (by norm_num))
theorem R89029 : Reach 89029 := rs (se 4 (by rfl) ⟨8346, by rfl⟩) (B 16693 (by norm_num) ⟨8346, by rfl⟩ (by norm_num))
theorem R56389 : Reach 56389 := rs (se 4 (by rfl) ⟨5286, by rfl⟩) (B 10573 (by norm_num) ⟨5286, by rfl⟩ (by norm_num))
theorem R121925 : Reach 121925 := rs (se 4 (by rfl) ⟨11430, by rfl⟩) (B 22861 (by norm_num) ⟨11430, by rfl⟩ (by norm_num))
theorem R56477 : Reach 56477 := rs (se 3 (by rfl) ⟨10589, by rfl⟩) (B 21179 (by norm_num) ⟨10589, by rfl⟩ (by norm_num))
theorem R89333 : Reach 89333 := rs (se 5 (by rfl) ⟨4187, by rfl⟩) (B 8375 (by norm_num) ⟨4187, by rfl⟩ (by norm_num))
theorem R253205 : Reach 253205 := rs (se 6 (by rfl) ⟨5934, by rfl⟩) (B 11869 (by norm_num) ⟨5934, by rfl⟩ (by norm_num))
theorem R56605 : Reach 56605 := rs (se 3 (by rfl) ⟨10613, by rfl⟩) (B 21227 (by norm_num) ⟨10613, by rfl⟩ (by norm_num))
theorem R122165 : Reach 122165 := rs (se 5 (by rfl) ⟨5726, by rfl⟩) (B 11453 (by norm_num) ⟨5726, by rfl⟩ (by norm_num))
theorem R56693 : Reach 56693 := rs (se 5 (by rfl) ⟨2657, by rfl⟩) (B 5315 (by norm_num) ⟨2657, by rfl⟩ (by norm_num))
theorem R56821 : Reach 56821 := rs (se 5 (by rfl) ⟨2663, by rfl⟩) (B 5327 (by norm_num) ⟨2663, by rfl⟩ (by norm_num))
theorem R155141 : Reach 155141 := rs (se 4 (by rfl) ⟨14544, by rfl⟩) (B 29089 (by norm_num) ⟨14544, by rfl⟩ (by norm_num))
theorem R56909 : Reach 56909 := rs (se 3 (by rfl) ⟨10670, by rfl⟩) (B 21341 (by norm_num) ⟨10670, by rfl⟩ (by norm_num))
theorem R57037 : Reach 57037 := rs (se 3 (by rfl) ⟨10694, by rfl⟩) (B 21389 (by norm_num) ⟨10694, by rfl⟩ (by norm_num))
theorem R57125 : Reach 57125 := rs (se 4 (by rfl) ⟨5355, by rfl⟩) (B 10711 (by norm_num) ⟨5355, by rfl⟩ (by norm_num))
theorem R89957 : Reach 89957 := rs (se 4 (by rfl) ⟨8433, by rfl⟩) (B 16867 (by norm_num) ⟨8433, by rfl⟩ (by norm_num))
theorem R57253 : Reach 57253 := rs (se 4 (by rfl) ⟨5367, by rfl⟩) (B 10735 (by norm_num) ⟨5367, by rfl⟩ (by norm_num))
theorem R57341 : Reach 57341 := rs (se 3 (by rfl) ⟨10751, by rfl⟩) (B 21503 (by norm_num) ⟨10751, by rfl⟩ (by norm_num))
theorem R57469 : Reach 57469 := rs (se 3 (by rfl) ⟨10775, by rfl⟩) (B 21551 (by norm_num) ⟨10775, by rfl⟩ (by norm_num))
theorem R57557 : Reach 57557 := rs (se 7 (by rfl) ⟨674, by rfl⟩) (B 1349 (by norm_num) ⟨674, by rfl⟩ (by norm_num))
theorem R57685 : Reach 57685 := rs (se 10 (by rfl) ⟨84, by rfl⟩) (B 169 (by norm_num) ⟨84, by rfl⟩ (by norm_num))
theorem R90533 : Reach 90533 := rs (se 4 (by rfl) ⟨8487, by rfl⟩) (B 16975 (by norm_num) ⟨8487, by rfl⟩ (by norm_num))
theorem R57773 : Reach 57773 := rs (se 3 (by rfl) ⟨10832, by rfl⟩) (B 21665 (by norm_num) ⟨10832, by rfl⟩ (by norm_num))
theorem R57781 : Reach 57781 := rs (se 5 (by rfl) ⟨2708, by rfl⟩) (B 5417 (by norm_num) ⟨2708, by rfl⟩ (by norm_num))
theorem R57853 : Reach 57853 := rs (se 3 (by rfl) ⟨10847, by rfl⟩) (B 21695 (by norm_num) ⟨10847, by rfl⟩ (by norm_num))
theorem R57901 : Reach 57901 := rs (se 3 (by rfl) ⟨10856, by rfl⟩) (B 21713 (by norm_num) ⟨10856, by rfl⟩ (by norm_num))
theorem R57989 : Reach 57989 := rs (se 4 (by rfl) ⟨5436, by rfl⟩) (B 10873 (by norm_num) ⟨5436, by rfl⟩ (by norm_num))
theorem R58117 : Reach 58117 := rs (se 4 (by rfl) ⟨5448, by rfl⟩) (B 10897 (by norm_num) ⟨5448, by rfl⟩ (by norm_num))
theorem R58205 : Reach 58205 := rs (se 3 (by rfl) ⟨10913, by rfl⟩) (B 21827 (by norm_num) ⟨10913, by rfl⟩ (by norm_num))
theorem R58333 : Reach 58333 := rs (se 3 (by rfl) ⟨10937, by rfl⟩) (B 21875 (by norm_num) ⟨10937, by rfl⟩ (by norm_num))
theorem R58421 : Reach 58421 := rs (se 5 (by rfl) ⟨2738, by rfl⟩) (B 5477 (by norm_num) ⟨2738, by rfl⟩ (by norm_num))
theorem R124037 : Reach 124037 := rs (se 4 (by rfl) ⟨11628, by rfl⟩) (B 23257 (by norm_num) ⟨11628, by rfl⟩ (by norm_num))
theorem R58549 : Reach 58549 := rs (se 5 (by rfl) ⟨2744, by rfl⟩) (B 5489 (by norm_num) ⟨2744, by rfl⟩ (by norm_num))
theorem R58637 : Reach 58637 := rs (se 3 (by rfl) ⟨10994, by rfl⟩) (B 21989 (by norm_num) ⟨10994, by rfl⟩ (by norm_num))
theorem R58765 : Reach 58765 := rs (se 3 (by rfl) ⟨11018, by rfl⟩) (B 22037 (by norm_num) ⟨11018, by rfl⟩ (by norm_num))
theorem R124325 : Reach 124325 := rs (se 4 (by rfl) ⟨11655, by rfl⟩) (B 23311 (by norm_num) ⟨11655, by rfl⟩ (by norm_num))
theorem R157157 : Reach 157157 := rs (se 4 (by rfl) ⟨14733, by rfl⟩) (B 29467 (by norm_num) ⟨14733, by rfl⟩ (by norm_num))
theorem R58853 : Reach 58853 := rs (se 4 (by rfl) ⟨5517, by rfl⟩) (B 11035 (by norm_num) ⟨5517, by rfl⟩ (by norm_num))
theorem R58877 : Reach 58877 := rs (se 3 (by rfl) ⟨11039, by rfl⟩) (B 22079 (by norm_num) ⟨11039, by rfl⟩ (by norm_num))
theorem R58981 : Reach 58981 := rs (se 4 (by rfl) ⟨5529, by rfl⟩) (B 11059 (by norm_num) ⟨5529, by rfl⟩ (by norm_num))
theorem R190133 : Reach 190133 := rs (se 5 (by rfl) ⟨8912, by rfl⟩) (B 17825 (by norm_num) ⟨8912, by rfl⟩ (by norm_num))
theorem R59069 : Reach 59069 := rs (se 3 (by rfl) ⟨11075, by rfl⟩) (B 22151 (by norm_num) ⟨11075, by rfl⟩ (by norm_num))
theorem R59125 : Reach 59125 := rs (se 5 (by rfl) ⟨2771, by rfl⟩) (B 5543 (by norm_num) ⟨2771, by rfl⟩ (by norm_num))
theorem R59165 : Reach 59165 := rs (se 3 (by rfl) ⟨11093, by rfl⟩) (B 22187 (by norm_num) ⟨11093, by rfl⟩ (by norm_num))
theorem R59197 : Reach 59197 := rs (se 3 (by rfl) ⟨11099, by rfl⟩) (B 22199 (by norm_num) ⟨11099, by rfl⟩ (by norm_num))
theorem R59285 : Reach 59285 := rs (se 6 (by rfl) ⟨1389, by rfl⟩) (B 2779 (by norm_num) ⟨1389, by rfl⟩ (by norm_num))
theorem R92117 : Reach 92117 := rs (se 7 (by rfl) ⟨1079, by rfl⟩) (B 2159 (by norm_num) ⟨1079, by rfl⟩ (by norm_num))
theorem R59429 : Reach 59429 := rs (se 4 (by rfl) ⟨5571, by rfl⟩) (B 11143 (by norm_num) ⟨5571, by rfl⟩ (by norm_num))
theorem R59549 : Reach 59549 := rs (se 3 (by rfl) ⟨11165, by rfl⟩) (B 22331 (by norm_num) ⟨11165, by rfl⟩ (by norm_num))
theorem R157909 : Reach 157909 := rs (se 7 (by rfl) ⟨1850, by rfl⟩) (B 3701 (by norm_num) ⟨1850, by rfl⟩ (by norm_num))
theorem R59717 : Reach 59717 := rs (se 4 (by rfl) ⟨5598, by rfl⟩) (B 11197 (by norm_num) ⟨5598, by rfl⟩ (by norm_num))
theorem R59869 : Reach 59869 := rs (se 3 (by rfl) ⟨11225, by rfl⟩) (B 22451 (by norm_num) ⟨11225, by rfl⟩ (by norm_num))
theorem R125509 : Reach 125509 := rs (se 4 (by rfl) ⟨11766, by rfl⟩) (B 23533 (by norm_num) ⟨11766, by rfl⟩ (by norm_num))
theorem R92789 : Reach 92789 := rs (se 5 (by rfl) ⟨4349, by rfl⟩) (B 8699 (by norm_num) ⟨4349, by rfl⟩ (by norm_num))
theorem R60173 : Reach 60173 := rs (se 3 (by rfl) ⟨11282, by rfl⟩) (B 22565 (by norm_num) ⟨11282, by rfl⟩ (by norm_num))
theorem R125813 : Reach 125813 := rs (se 5 (by rfl) ⟨5897, by rfl⟩) (B 11795 (by norm_num) ⟨5897, by rfl⟩ (by norm_num))
theorem R158597 : Reach 158597 := rs (se 4 (by rfl) ⟨14868, by rfl⟩) (B 29737 (by norm_num) ⟨14868, by rfl⟩ (by norm_num))
theorem R93109 : Reach 93109 := rs (se 5 (by rfl) ⟨4364, by rfl⟩) (B 8729 (by norm_num) ⟨4364, by rfl⟩ (by norm_num))
theorem R125941 : Reach 125941 := rs (se 5 (by rfl) ⟨5903, by rfl⟩) (B 11807 (by norm_num) ⟨5903, by rfl⟩ (by norm_num))
theorem R93221 : Reach 93221 := rs (se 4 (by rfl) ⟨8739, by rfl⟩) (B 17479 (by norm_num) ⟨8739, by rfl⟩ (by norm_num))
theorem R224693 : Reach 224693 := rs (se 5 (by rfl) ⟨10532, by rfl⟩) (B 21065 (by norm_num) ⟨10532, by rfl⟩ (by norm_num))
theorem R60893 : Reach 60893 := rs (se 3 (by rfl) ⟨11417, by rfl⟩) (B 22835 (by norm_num) ⟨11417, by rfl⟩ (by norm_num))
theorem R60925 : Reach 60925 := rs (se 3 (by rfl) ⟨11423, by rfl⟩) (B 22847 (by norm_num) ⟨11423, by rfl⟩ (by norm_num))
theorem R61069 : Reach 61069 := rs (se 3 (by rfl) ⟨11450, by rfl⟩) (B 22901 (by norm_num) ⟨11450, by rfl⟩ (by norm_num))
theorem R192149 : Reach 192149 := rs (se 6 (by rfl) ⟨4503, by rfl⟩) (B 9007 (by norm_num) ⟨4503, by rfl⟩ (by norm_num))
theorem R93973 : Reach 93973 := rs (se 6 (by rfl) ⟨2202, by rfl⟩) (B 4405 (by norm_num) ⟨2202, by rfl⟩ (by norm_num))
theorem R61229 : Reach 61229 := rs (se 3 (by rfl) ⟨11480, by rfl⟩) (B 22961 (by norm_num) ⟨11480, by rfl⟩ (by norm_num))
theorem R61373 : Reach 61373 := rs (se 3 (by rfl) ⟨11507, by rfl⟩) (B 23015 (by norm_num) ⟨11507, by rfl⟩ (by norm_num))
theorem R159893 : Reach 159893 := rs (se 6 (by rfl) ⟨3747, by rfl⟩) (B 7495 (by norm_num) ⟨3747, by rfl⟩ (by norm_num))
theorem R61661 : Reach 61661 := rs (se 3 (by rfl) ⟨11561, by rfl⟩) (B 23123 (by norm_num) ⟨11561, by rfl⟩ (by norm_num))
theorem R61789 : Reach 61789 := rs (se 3 (by rfl) ⟨11585, by rfl⟩) (B 23171 (by norm_num) ⟨11585, by rfl⟩ (by norm_num))
theorem R94565 : Reach 94565 := rs (se 4 (by rfl) ⟨8865, by rfl⟩) (B 17731 (by norm_num) ⟨8865, by rfl⟩ (by norm_num))
theorem R61813 : Reach 61813 := rs (se 5 (by rfl) ⟨2897, by rfl⟩) (B 5795 (by norm_num) ⟨2897, by rfl⟩ (by norm_num))
theorem R62117 : Reach 62117 := rs (se 4 (by rfl) ⟨5823, by rfl⟩) (B 11647 (by norm_num) ⟨5823, by rfl⟩ (by norm_num))
theorem R62381 : Reach 62381 := rs (se 3 (by rfl) ⟨11696, by rfl⟩) (B 23393 (by norm_num) ⟨11696, by rfl⟩ (by norm_num))
theorem R127925 : Reach 127925 := rs (se 5 (by rfl) ⟨5996, by rfl⟩) (B 11993 (by norm_num) ⟨5996, by rfl⟩ (by norm_num))
theorem R128213 : Reach 128213 := rs (se 7 (by rfl) ⟨1502, by rfl⟩) (B 3005 (by norm_num) ⟨1502, by rfl⟩ (by norm_num))
theorem R62869 : Reach 62869 := rs (se 6 (by rfl) ⟨1473, by rfl⟩) (B 2947 (by norm_num) ⟨1473, by rfl⟩ (by norm_num))
theorem R161189 : Reach 161189 := rs (se 4 (by rfl) ⟨15111, by rfl⟩) (B 30223 (by norm_num) ⟨15111, by rfl⟩ (by norm_num))
theorem R63013 : Reach 63013 := rs (se 4 (by rfl) ⟨5907, by rfl⟩) (B 11815 (by norm_num) ⟨5907, by rfl⟩ (by norm_num))
theorem R1799765 : Reach 1799765 := rs (se 8 (by rfl) ⟨10545, by rfl⟩) (B 21091 (by norm_num) ⟨10545, by rfl⟩ (by norm_num))
theorem R63173 : Reach 63173 := rs (se 4 (by rfl) ⟨5922, by rfl⟩) (B 11845 (by norm_num) ⟨5922, by rfl⟩ (by norm_num))
theorem R63317 : Reach 63317 := rs (se 9 (by rfl) ⟨185, by rfl⟩) (B 371 (by norm_num) ⟨185, by rfl⟩ (by norm_num))
theorem R391189 : Reach 391189 := rs (se 6 (by rfl) ⟨9168, by rfl⟩) (B 18337 (by norm_num) ⟨9168, by rfl⟩ (by norm_num))
theorem R63605 : Reach 63605 := rs (se 5 (by rfl) ⟨2981, by rfl⟩) (B 5963 (by norm_num) ⟨2981, by rfl⟩ (by norm_num))
theorem R63757 : Reach 63757 := rs (se 3 (by rfl) ⟨11954, by rfl⟩) (B 23909 (by norm_num) ⟨11954, by rfl⟩ (by norm_num))
theorem R129397 : Reach 129397 := rs (se 5 (by rfl) ⟨6065, by rfl⟩) (B 12131 (by norm_num) ⟨6065, by rfl⟩ (by norm_num))
theorem R31117 : Reach 31117 := rs (se 3 (by rfl) ⟨5834, by rfl⟩) (B 11669 (by norm_num) ⟨5834, by rfl⟩ (by norm_num))
theorem R31121 : Reach 31121 := rs (se 2 (by rfl) ⟨11670, by rfl⟩) (B 23341 (by norm_num) ⟨11670, by rfl⟩ (by norm_num))
theorem R31125 : Reach 31125 := rs (se 6 (by rfl) ⟨729, by rfl⟩) (B 1459 (by norm_num) ⟨729, by rfl⟩ (by norm_num))
theorem R63893 : Reach 63893 := rs (se 6 (by rfl) ⟨1497, by rfl⟩) (B 2995 (by norm_num) ⟨1497, by rfl⟩ (by norm_num))
theorem R31129 : Reach 31129 := rs (se 2 (by rfl) ⟨11673, by rfl⟩) (B 23347 (by norm_num) ⟨11673, by rfl⟩ (by norm_num))
theorem R31133 : Reach 31133 := rs (se 3 (by rfl) ⟨5837, by rfl⟩) (B 11675 (by norm_num) ⟨5837, by rfl⟩ (by norm_num))
theorem R31137 : Reach 31137 := rs (se 2 (by rfl) ⟨11676, by rfl⟩) (B 23353 (by norm_num) ⟨11676, by rfl⟩ (by norm_num))
theorem R31141 : Reach 31141 := rs (se 4 (by rfl) ⟨2919, by rfl⟩) (B 5839 (by norm_num) ⟨2919, by rfl⟩ (by norm_num))
theorem R31145 : Reach 31145 := rs (se 2 (by rfl) ⟨11679, by rfl⟩) (B 23359 (by norm_num) ⟨11679, by rfl⟩ (by norm_num))
theorem R31149 : Reach 31149 := rs (se 3 (by rfl) ⟨5840, by rfl⟩) (B 11681 (by norm_num) ⟨5840, by rfl⟩ (by norm_num))
theorem R31153 : Reach 31153 := rs (se 2 (by rfl) ⟨11682, by rfl⟩) (B 23365 (by norm_num) ⟨11682, by rfl⟩ (by norm_num))
theorem R31157 : Reach 31157 := rs (se 5 (by rfl) ⟨1460, by rfl⟩) (B 2921 (by norm_num) ⟨1460, by rfl⟩ (by norm_num))
theorem R31161 : Reach 31161 := rs (se 2 (by rfl) ⟨11685, by rfl⟩) (B 23371 (by norm_num) ⟨11685, by rfl⟩ (by norm_num))
theorem R31165 : Reach 31165 := rs (se 3 (by rfl) ⟨5843, by rfl⟩) (B 11687 (by norm_num) ⟨5843, by rfl⟩ (by norm_num))
theorem R31169 : Reach 31169 := rs (se 2 (by rfl) ⟨11688, by rfl⟩) (B 23377 (by norm_num) ⟨11688, by rfl⟩ (by norm_num))
theorem R31173 : Reach 31173 := rs (se 4 (by rfl) ⟨2922, by rfl⟩) (B 5845 (by norm_num) ⟨2922, by rfl⟩ (by norm_num))
theorem R31177 : Reach 31177 := rs (se 2 (by rfl) ⟨11691, by rfl⟩) (B 23383 (by norm_num) ⟨11691, by rfl⟩ (by norm_num))
theorem R31181 : Reach 31181 := rs (se 3 (by rfl) ⟨5846, by rfl⟩) (B 11693 (by norm_num) ⟨5846, by rfl⟩ (by norm_num))
theorem R31185 : Reach 31185 := rs (se 2 (by rfl) ⟨11694, by rfl⟩) (B 23389 (by norm_num) ⟨11694, by rfl⟩ (by norm_num))
theorem R31189 : Reach 31189 := rs (se 7 (by rfl) ⟨365, by rfl⟩) (B 731 (by norm_num) ⟨365, by rfl⟩ (by norm_num))
theorem R31193 : Reach 31193 := rs (se 2 (by rfl) ⟨11697, by rfl⟩) (B 23395 (by norm_num) ⟨11697, by rfl⟩ (by norm_num))
theorem R31197 : Reach 31197 := rs (se 3 (by rfl) ⟨5849, by rfl⟩) (B 11699 (by norm_num) ⟨5849, by rfl⟩ (by norm_num))
theorem R31201 : Reach 31201 := rs (se 2 (by rfl) ⟨11700, by rfl⟩) (B 23401 (by norm_num) ⟨11700, by rfl⟩ (by norm_num))
theorem R31205 : Reach 31205 := rs (se 4 (by rfl) ⟨2925, by rfl⟩) (B 5851 (by norm_num) ⟨2925, by rfl⟩ (by norm_num))
theorem R31209 : Reach 31209 := rs (se 2 (by rfl) ⟨11703, by rfl⟩) (B 23407 (by norm_num) ⟨11703, by rfl⟩ (by norm_num))
theorem R31213 : Reach 31213 := rs (se 3 (by rfl) ⟨5852, by rfl⟩) (B 11705 (by norm_num) ⟨5852, by rfl⟩ (by norm_num))
theorem R31217 : Reach 31217 := rs (se 2 (by rfl) ⟨11706, by rfl⟩) (B 23413 (by norm_num) ⟨11706, by rfl⟩ (by norm_num))
theorem R31221 : Reach 31221 := rs (se 5 (by rfl) ⟨1463, by rfl⟩) (B 2927 (by norm_num) ⟨1463, by rfl⟩ (by norm_num))
theorem R31225 : Reach 31225 := rs (se 2 (by rfl) ⟨11709, by rfl⟩) (B 23419 (by norm_num) ⟨11709, by rfl⟩ (by norm_num))
theorem R31229 : Reach 31229 := rs (se 3 (by rfl) ⟨5855, by rfl⟩) (B 11711 (by norm_num) ⟨5855, by rfl⟩ (by norm_num))
theorem R31233 : Reach 31233 := rs (se 2 (by rfl) ⟨11712, by rfl⟩) (B 23425 (by norm_num) ⟨11712, by rfl⟩ (by norm_num))
theorem R31237 : Reach 31237 := rs (se 4 (by rfl) ⟨2928, by rfl⟩) (B 5857 (by norm_num) ⟨2928, by rfl⟩ (by norm_num))
theorem R31241 : Reach 31241 := rs (se 2 (by rfl) ⟨11715, by rfl⟩) (B 23431 (by norm_num) ⟨11715, by rfl⟩ (by norm_num))
theorem R31245 : Reach 31245 := rs (se 3 (by rfl) ⟨5858, by rfl⟩) (B 11717 (by norm_num) ⟨5858, by rfl⟩ (by norm_num))
theorem R31249 : Reach 31249 := rs (se 2 (by rfl) ⟨11718, by rfl⟩) (B 23437 (by norm_num) ⟨11718, by rfl⟩ (by norm_num))
theorem R31253 : Reach 31253 := rs (se 6 (by rfl) ⟨732, by rfl⟩) (B 1465 (by norm_num) ⟨732, by rfl⟩ (by norm_num))
theorem R31257 : Reach 31257 := rs (se 2 (by rfl) ⟨11721, by rfl⟩) (B 23443 (by norm_num) ⟨11721, by rfl⟩ (by norm_num))
theorem R31261 : Reach 31261 := rs (se 3 (by rfl) ⟨5861, by rfl⟩) (B 11723 (by norm_num) ⟨5861, by rfl⟩ (by norm_num))
theorem R31265 : Reach 31265 := rs (se 2 (by rfl) ⟨11724, by rfl⟩) (B 23449 (by norm_num) ⟨11724, by rfl⟩ (by norm_num))
theorem R31269 : Reach 31269 := rs (se 4 (by rfl) ⟨2931, by rfl⟩) (B 5863 (by norm_num) ⟨2931, by rfl⟩ (by norm_num))
theorem R31273 : Reach 31273 := rs (se 2 (by rfl) ⟨11727, by rfl⟩) (B 23455 (by norm_num) ⟨11727, by rfl⟩ (by norm_num))
theorem R31277 : Reach 31277 := rs (se 3 (by rfl) ⟨5864, by rfl⟩) (B 11729 (by norm_num) ⟨5864, by rfl⟩ (by norm_num))
theorem R31281 : Reach 31281 := rs (se 2 (by rfl) ⟨11730, by rfl⟩) (B 23461 (by norm_num) ⟨11730, by rfl⟩ (by norm_num))
theorem R96821 : Reach 96821 := rs (se 5 (by rfl) ⟨4538, by rfl⟩) (B 9077 (by norm_num) ⟨4538, by rfl⟩ (by norm_num))
theorem R31285 : Reach 31285 := rs (se 5 (by rfl) ⟨1466, by rfl⟩) (B 2933 (by norm_num) ⟨1466, by rfl⟩ (by norm_num))
theorem R227893 : Reach 227893 := rs (se 5 (by rfl) ⟨10682, by rfl⟩) (B 21365 (by norm_num) ⟨10682, by rfl⟩ (by norm_num))
theorem R31289 : Reach 31289 := rs (se 2 (by rfl) ⟨11733, by rfl⟩) (B 23467 (by norm_num) ⟨11733, by rfl⟩ (by norm_num))
theorem R31293 : Reach 31293 := rs (se 3 (by rfl) ⟨5867, by rfl⟩) (B 11735 (by norm_num) ⟨5867, by rfl⟩ (by norm_num))
theorem R64061 : Reach 64061 := rs (se 3 (by rfl) ⟨12011, by rfl⟩) (B 24023 (by norm_num) ⟨12011, by rfl⟩ (by norm_num))
theorem R31297 : Reach 31297 := rs (se 2 (by rfl) ⟨11736, by rfl⟩) (B 23473 (by norm_num) ⟨11736, by rfl⟩ (by norm_num))
theorem R31301 : Reach 31301 := rs (se 4 (by rfl) ⟨2934, by rfl⟩) (B 5869 (by norm_num) ⟨2934, by rfl⟩ (by norm_num))
theorem R31305 : Reach 31305 := rs (se 2 (by rfl) ⟨11739, by rfl⟩) (B 23479 (by norm_num) ⟨11739, by rfl⟩ (by norm_num))
theorem R31309 : Reach 31309 := rs (se 3 (by rfl) ⟨5870, by rfl⟩) (B 11741 (by norm_num) ⟨5870, by rfl⟩ (by norm_num))
theorem R31313 : Reach 31313 := rs (se 2 (by rfl) ⟨11742, by rfl⟩) (B 23485 (by norm_num) ⟨11742, by rfl⟩ (by norm_num))
theorem R31317 : Reach 31317 := rs (se 8 (by rfl) ⟨183, by rfl⟩) (B 367 (by norm_num) ⟨183, by rfl⟩ (by norm_num))
theorem R31321 : Reach 31321 := rs (se 2 (by rfl) ⟨11745, by rfl⟩) (B 23491 (by norm_num) ⟨11745, by rfl⟩ (by norm_num))
theorem R31325 : Reach 31325 := rs (se 3 (by rfl) ⟨5873, by rfl⟩) (B 11747 (by norm_num) ⟨5873, by rfl⟩ (by norm_num))
theorem R31329 : Reach 31329 := rs (se 2 (by rfl) ⟨11748, by rfl⟩) (B 23497 (by norm_num) ⟨11748, by rfl⟩ (by norm_num))
theorem R31333 : Reach 31333 := rs (se 4 (by rfl) ⟨2937, by rfl⟩) (B 5875 (by norm_num) ⟨2937, by rfl⟩ (by norm_num))
theorem R31337 : Reach 31337 := rs (se 2 (by rfl) ⟨11751, by rfl⟩) (B 23503 (by norm_num) ⟨11751, by rfl⟩ (by norm_num))
theorem R31341 : Reach 31341 := rs (se 3 (by rfl) ⟨5876, by rfl⟩) (B 11753 (by norm_num) ⟨5876, by rfl⟩ (by norm_num))
theorem R31345 : Reach 31345 := rs (se 2 (by rfl) ⟨11754, by rfl⟩) (B 23509 (by norm_num) ⟨11754, by rfl⟩ (by norm_num))
theorem R31349 : Reach 31349 := rs (se 5 (by rfl) ⟨1469, by rfl⟩) (B 2939 (by norm_num) ⟨1469, by rfl⟩ (by norm_num))
theorem R31353 : Reach 31353 := rs (se 2 (by rfl) ⟨11757, by rfl⟩) (B 23515 (by norm_num) ⟨11757, by rfl⟩ (by norm_num))
theorem R31357 : Reach 31357 := rs (se 3 (by rfl) ⟨5879, by rfl⟩) (B 11759 (by norm_num) ⟨5879, by rfl⟩ (by norm_num))
theorem R31361 : Reach 31361 := rs (se 2 (by rfl) ⟨11760, by rfl⟩) (B 23521 (by norm_num) ⟨11760, by rfl⟩ (by norm_num))
theorem R31365 : Reach 31365 := rs (se 4 (by rfl) ⟨2940, by rfl⟩) (B 5881 (by norm_num) ⟨2940, by rfl⟩ (by norm_num))
theorem R31369 : Reach 31369 := rs (se 2 (by rfl) ⟨11763, by rfl⟩) (B 23527 (by norm_num) ⟨11763, by rfl⟩ (by norm_num))
theorem R31373 : Reach 31373 := rs (se 3 (by rfl) ⟨5882, by rfl⟩) (B 11765 (by norm_num) ⟨5882, by rfl⟩ (by norm_num))
theorem R31377 : Reach 31377 := rs (se 2 (by rfl) ⟨11766, by rfl⟩) (B 23533 (by norm_num) ⟨11766, by rfl⟩ (by norm_num))
theorem R31381 : Reach 31381 := rs (se 6 (by rfl) ⟨735, by rfl⟩) (B 1471 (by norm_num) ⟨735, by rfl⟩ (by norm_num))
theorem R31385 : Reach 31385 := rs (se 2 (by rfl) ⟨11769, by rfl⟩) (B 23539 (by norm_num) ⟨11769, by rfl⟩ (by norm_num))
theorem R31389 : Reach 31389 := rs (se 3 (by rfl) ⟨5885, by rfl⟩) (B 11771 (by norm_num) ⟨5885, by rfl⟩ (by norm_num))
theorem R31393 : Reach 31393 := rs (se 2 (by rfl) ⟨11772, by rfl⟩) (B 23545 (by norm_num) ⟨11772, by rfl⟩ (by norm_num))
theorem R31397 : Reach 31397 := rs (se 4 (by rfl) ⟨2943, by rfl⟩) (B 5887 (by norm_num) ⟨2943, by rfl⟩ (by norm_num))
theorem R129701 : Reach 129701 := rs (se 4 (by rfl) ⟨12159, by rfl⟩) (B 24319 (by norm_num) ⟨12159, by rfl⟩ (by norm_num))
theorem R31401 : Reach 31401 := rs (se 2 (by rfl) ⟨11775, by rfl⟩) (B 23551 (by norm_num) ⟨11775, by rfl⟩ (by norm_num))
theorem R31405 : Reach 31405 := rs (se 3 (by rfl) ⟨5888, by rfl⟩) (B 11777 (by norm_num) ⟨5888, by rfl⟩ (by norm_num))
theorem R31409 : Reach 31409 := rs (se 2 (by rfl) ⟨11778, by rfl⟩) (B 23557 (by norm_num) ⟨11778, by rfl⟩ (by norm_num))
theorem R31413 : Reach 31413 := rs (se 5 (by rfl) ⟨1472, by rfl⟩) (B 2945 (by norm_num) ⟨1472, by rfl⟩ (by norm_num))
theorem R162485 : Reach 162485 := rs (se 5 (by rfl) ⟨7616, by rfl⟩) (B 15233 (by norm_num) ⟨7616, by rfl⟩ (by norm_num))
theorem R31417 : Reach 31417 := rs (se 2 (by rfl) ⟨11781, by rfl⟩) (B 23563 (by norm_num) ⟨11781, by rfl⟩ (by norm_num))
theorem R31421 : Reach 31421 := rs (se 3 (by rfl) ⟨5891, by rfl⟩) (B 11783 (by norm_num) ⟨5891, by rfl⟩ (by norm_num))
theorem R31425 : Reach 31425 := rs (se 2 (by rfl) ⟨11784, by rfl⟩) (B 23569 (by norm_num) ⟨11784, by rfl⟩ (by norm_num))
theorem R31429 : Reach 31429 := rs (se 4 (by rfl) ⟨2946, by rfl⟩) (B 5893 (by norm_num) ⟨2946, by rfl⟩ (by norm_num))
theorem R31433 : Reach 31433 := rs (se 2 (by rfl) ⟨11787, by rfl⟩) (B 23575 (by norm_num) ⟨11787, by rfl⟩ (by norm_num))
theorem R31437 : Reach 31437 := rs (se 3 (by rfl) ⟨5894, by rfl⟩) (B 11789 (by norm_num) ⟨5894, by rfl⟩ (by norm_num))
theorem R31441 : Reach 31441 := rs (se 2 (by rfl) ⟨11790, by rfl⟩) (B 23581 (by norm_num) ⟨11790, by rfl⟩ (by norm_num))
theorem R31445 : Reach 31445 := rs (se 7 (by rfl) ⟨368, by rfl⟩) (B 737 (by norm_num) ⟨368, by rfl⟩ (by norm_num))
theorem R31449 : Reach 31449 := rs (se 2 (by rfl) ⟨11793, by rfl⟩) (B 23587 (by norm_num) ⟨11793, by rfl⟩ (by norm_num))
theorem R31453 : Reach 31453 := rs (se 3 (by rfl) ⟨5897, by rfl⟩) (B 11795 (by norm_num) ⟨5897, by rfl⟩ (by norm_num))
theorem R31457 : Reach 31457 := rs (se 2 (by rfl) ⟨11796, by rfl⟩) (B 23593 (by norm_num) ⟨11796, by rfl⟩ (by norm_num))
theorem R31461 : Reach 31461 := rs (se 4 (by rfl) ⟨2949, by rfl⟩) (B 5899 (by norm_num) ⟨2949, by rfl⟩ (by norm_num))
theorem R31465 : Reach 31465 := rs (se 2 (by rfl) ⟨11799, by rfl⟩) (B 23599 (by norm_num) ⟨11799, by rfl⟩ (by norm_num))
theorem R31469 : Reach 31469 := rs (se 3 (by rfl) ⟨5900, by rfl⟩) (B 11801 (by norm_num) ⟨5900, by rfl⟩ (by norm_num))
theorem R31473 : Reach 31473 := rs (se 2 (by rfl) ⟨11802, by rfl⟩) (B 23605 (by norm_num) ⟨11802, by rfl⟩ (by norm_num))
theorem R31477 : Reach 31477 := rs (se 5 (by rfl) ⟨1475, by rfl⟩) (B 2951 (by norm_num) ⟨1475, by rfl⟩ (by norm_num))
theorem R31481 : Reach 31481 := rs (se 2 (by rfl) ⟨11805, by rfl⟩) (B 23611 (by norm_num) ⟨11805, by rfl⟩ (by norm_num))
theorem R31485 : Reach 31485 := rs (se 3 (by rfl) ⟨5903, by rfl⟩) (B 11807 (by norm_num) ⟨5903, by rfl⟩ (by norm_num))
theorem R31489 : Reach 31489 := rs (se 2 (by rfl) ⟨11808, by rfl⟩) (B 23617 (by norm_num) ⟨11808, by rfl⟩ (by norm_num))
theorem R31493 : Reach 31493 := rs (se 4 (by rfl) ⟨2952, by rfl⟩) (B 5905 (by norm_num) ⟨2952, by rfl⟩ (by norm_num))
theorem R31497 : Reach 31497 := rs (se 2 (by rfl) ⟨11811, by rfl⟩) (B 23623 (by norm_num) ⟨11811, by rfl⟩ (by norm_num))
theorem R31501 : Reach 31501 := rs (se 3 (by rfl) ⟨5906, by rfl⟩) (B 11813 (by norm_num) ⟨5906, by rfl⟩ (by norm_num))
theorem R31505 : Reach 31505 := rs (se 2 (by rfl) ⟨11814, by rfl⟩) (B 23629 (by norm_num) ⟨11814, by rfl⟩ (by norm_num))
theorem R31509 : Reach 31509 := rs (se 6 (by rfl) ⟨738, by rfl⟩) (B 1477 (by norm_num) ⟨738, by rfl⟩ (by norm_num))
theorem R31513 : Reach 31513 := rs (se 2 (by rfl) ⟨11817, by rfl⟩) (B 23635 (by norm_num) ⟨11817, by rfl⟩ (by norm_num))
theorem R31517 : Reach 31517 := rs (se 3 (by rfl) ⟨5909, by rfl⟩) (B 11819 (by norm_num) ⟨5909, by rfl⟩ (by norm_num))
theorem R31521 : Reach 31521 := rs (se 2 (by rfl) ⟨11820, by rfl⟩) (B 23641 (by norm_num) ⟨11820, by rfl⟩ (by norm_num))
theorem R31525 : Reach 31525 := rs (se 4 (by rfl) ⟨2955, by rfl⟩) (B 5911 (by norm_num) ⟨2955, by rfl⟩ (by norm_num))
theorem R31529 : Reach 31529 := rs (se 2 (by rfl) ⟨11823, by rfl⟩) (B 23647 (by norm_num) ⟨11823, by rfl⟩ (by norm_num))
theorem R31533 : Reach 31533 := rs (se 3 (by rfl) ⟨5912, by rfl⟩) (B 11825 (by norm_num) ⟨5912, by rfl⟩ (by norm_num))
theorem R31537 : Reach 31537 := rs (se 2 (by rfl) ⟨11826, by rfl⟩) (B 23653 (by norm_num) ⟨11826, by rfl⟩ (by norm_num))
theorem R31541 : Reach 31541 := rs (se 5 (by rfl) ⟨1478, by rfl⟩) (B 2957 (by norm_num) ⟨1478, by rfl⟩ (by norm_num))
theorem R31545 : Reach 31545 := rs (se 2 (by rfl) ⟨11829, by rfl⟩) (B 23659 (by norm_num) ⟨11829, by rfl⟩ (by norm_num))
theorem R31549 : Reach 31549 := rs (se 3 (by rfl) ⟨5915, by rfl⟩) (B 11831 (by norm_num) ⟨5915, by rfl⟩ (by norm_num))
theorem R31553 : Reach 31553 := rs (se 2 (by rfl) ⟨11832, by rfl⟩) (B 23665 (by norm_num) ⟨11832, by rfl⟩ (by norm_num))
theorem R31557 : Reach 31557 := rs (se 4 (by rfl) ⟨2958, by rfl⟩) (B 5917 (by norm_num) ⟨2958, by rfl⟩ (by norm_num))
theorem R31561 : Reach 31561 := rs (se 2 (by rfl) ⟨11835, by rfl⟩) (B 23671 (by norm_num) ⟨11835, by rfl⟩ (by norm_num))
theorem R31565 : Reach 31565 := rs (se 3 (by rfl) ⟨5918, by rfl⟩) (B 11837 (by norm_num) ⟨5918, by rfl⟩ (by norm_num))
theorem R31569 : Reach 31569 := rs (se 2 (by rfl) ⟨11838, by rfl⟩) (B 23677 (by norm_num) ⟨11838, by rfl⟩ (by norm_num))
theorem R31573 : Reach 31573 := rs (se 9 (by rfl) ⟨92, by rfl⟩) (B 185 (by norm_num) ⟨92, by rfl⟩ (by norm_num))
theorem R31577 : Reach 31577 := rs (se 2 (by rfl) ⟨11841, by rfl⟩) (B 23683 (by norm_num) ⟨11841, by rfl⟩ (by norm_num))
theorem R31581 : Reach 31581 := rs (se 3 (by rfl) ⟨5921, by rfl⟩) (B 11843 (by norm_num) ⟨5921, by rfl⟩ (by norm_num))
theorem R31585 : Reach 31585 := rs (se 2 (by rfl) ⟨11844, by rfl⟩) (B 23689 (by norm_num) ⟨11844, by rfl⟩ (by norm_num))
theorem R31589 : Reach 31589 := rs (se 4 (by rfl) ⟨2961, by rfl⟩) (B 5923 (by norm_num) ⟨2961, by rfl⟩ (by norm_num))
theorem R31593 : Reach 31593 := rs (se 2 (by rfl) ⟨11847, by rfl⟩) (B 23695 (by norm_num) ⟨11847, by rfl⟩ (by norm_num))
theorem R31597 : Reach 31597 := rs (se 3 (by rfl) ⟨5924, by rfl⟩) (B 11849 (by norm_num) ⟨5924, by rfl⟩ (by norm_num))
theorem R31601 : Reach 31601 := rs (se 2 (by rfl) ⟨11850, by rfl⟩) (B 23701 (by norm_num) ⟨11850, by rfl⟩ (by norm_num))
theorem R31605 : Reach 31605 := rs (se 5 (by rfl) ⟨1481, by rfl⟩) (B 2963 (by norm_num) ⟨1481, by rfl⟩ (by norm_num))
theorem R260981 : Reach 260981 := rs (se 5 (by rfl) ⟨12233, by rfl⟩) (B 24467 (by norm_num) ⟨12233, by rfl⟩ (by norm_num))
theorem R31609 : Reach 31609 := rs (se 2 (by rfl) ⟨11853, by rfl⟩) (B 23707 (by norm_num) ⟨11853, by rfl⟩ (by norm_num))
theorem R31613 : Reach 31613 := rs (se 3 (by rfl) ⟨5927, by rfl⟩) (B 11855 (by norm_num) ⟨5927, by rfl⟩ (by norm_num))
theorem R31617 : Reach 31617 := rs (se 2 (by rfl) ⟨11856, by rfl⟩) (B 23713 (by norm_num) ⟨11856, by rfl⟩ (by norm_num))
theorem R31621 : Reach 31621 := rs (se 4 (by rfl) ⟨2964, by rfl⟩) (B 5929 (by norm_num) ⟨2964, by rfl⟩ (by norm_num))
theorem R31625 : Reach 31625 := rs (se 2 (by rfl) ⟨11859, by rfl⟩) (B 23719 (by norm_num) ⟨11859, by rfl⟩ (by norm_num))
theorem R31629 : Reach 31629 := rs (se 3 (by rfl) ⟨5930, by rfl⟩) (B 11861 (by norm_num) ⟨5930, by rfl⟩ (by norm_num))
theorem R31633 : Reach 31633 := rs (se 2 (by rfl) ⟨11862, by rfl⟩) (B 23725 (by norm_num) ⟨11862, by rfl⟩ (by norm_num))
theorem R31637 : Reach 31637 := rs (se 6 (by rfl) ⟨741, by rfl⟩) (B 1483 (by norm_num) ⟨741, by rfl⟩ (by norm_num))
theorem R31641 : Reach 31641 := rs (se 2 (by rfl) ⟨11865, by rfl⟩) (B 23731 (by norm_num) ⟨11865, by rfl⟩ (by norm_num))
theorem R31645 : Reach 31645 := rs (se 3 (by rfl) ⟨5933, by rfl⟩) (B 11867 (by norm_num) ⟨5933, by rfl⟩ (by norm_num))
theorem R31649 : Reach 31649 := rs (se 2 (by rfl) ⟨11868, by rfl⟩) (B 23737 (by norm_num) ⟨11868, by rfl⟩ (by norm_num))
theorem R31653 : Reach 31653 := rs (se 4 (by rfl) ⟨2967, by rfl⟩) (B 5935 (by norm_num) ⟨2967, by rfl⟩ (by norm_num))
theorem R31657 : Reach 31657 := rs (se 2 (by rfl) ⟨11871, by rfl⟩) (B 23743 (by norm_num) ⟨11871, by rfl⟩ (by norm_num))
theorem R31661 : Reach 31661 := rs (se 3 (by rfl) ⟨5936, by rfl⟩) (B 11873 (by norm_num) ⟨5936, by rfl⟩ (by norm_num))
theorem R31665 : Reach 31665 := rs (se 2 (by rfl) ⟨11874, by rfl⟩) (B 23749 (by norm_num) ⟨11874, by rfl⟩ (by norm_num))
theorem R31669 : Reach 31669 := rs (se 5 (by rfl) ⟨1484, by rfl⟩) (B 2969 (by norm_num) ⟨1484, by rfl⟩ (by norm_num))
theorem R31673 : Reach 31673 := rs (se 2 (by rfl) ⟨11877, by rfl⟩) (B 23755 (by norm_num) ⟨11877, by rfl⟩ (by norm_num))
theorem R31677 : Reach 31677 := rs (se 3 (by rfl) ⟨5939, by rfl⟩) (B 11879 (by norm_num) ⟨5939, by rfl⟩ (by norm_num))
theorem R31681 : Reach 31681 := rs (se 2 (by rfl) ⟨11880, by rfl⟩) (B 23761 (by norm_num) ⟨11880, by rfl⟩ (by norm_num))
theorem R31685 : Reach 31685 := rs (se 4 (by rfl) ⟨2970, by rfl⟩) (B 5941 (by norm_num) ⟨2970, by rfl⟩ (by norm_num))
theorem R31689 : Reach 31689 := rs (se 2 (by rfl) ⟨11883, by rfl⟩) (B 23767 (by norm_num) ⟨11883, by rfl⟩ (by norm_num))
theorem R31693 : Reach 31693 := rs (se 3 (by rfl) ⟨5942, by rfl⟩) (B 11885 (by norm_num) ⟨5942, by rfl⟩ (by norm_num))
theorem R31697 : Reach 31697 := rs (se 2 (by rfl) ⟨11886, by rfl⟩) (B 23773 (by norm_num) ⟨11886, by rfl⟩ (by norm_num))
theorem R31701 : Reach 31701 := rs (se 7 (by rfl) ⟨371, by rfl⟩) (B 743 (by norm_num) ⟨371, by rfl⟩ (by norm_num))
theorem R31705 : Reach 31705 := rs (se 2 (by rfl) ⟨11889, by rfl⟩) (B 23779 (by norm_num) ⟨11889, by rfl⟩ (by norm_num))
theorem R31709 : Reach 31709 := rs (se 3 (by rfl) ⟨5945, by rfl⟩) (B 11891 (by norm_num) ⟨5945, by rfl⟩ (by norm_num))
theorem R31713 : Reach 31713 := rs (se 2 (by rfl) ⟨11892, by rfl⟩) (B 23785 (by norm_num) ⟨11892, by rfl⟩ (by norm_num))
theorem R31717 : Reach 31717 := rs (se 4 (by rfl) ⟨2973, by rfl⟩) (B 5947 (by norm_num) ⟨2973, by rfl⟩ (by norm_num))
theorem R31721 : Reach 31721 := rs (se 2 (by rfl) ⟨11895, by rfl⟩) (B 23791 (by norm_num) ⟨11895, by rfl⟩ (by norm_num))
theorem R31725 : Reach 31725 := rs (se 3 (by rfl) ⟨5948, by rfl⟩) (B 11897 (by norm_num) ⟨5948, by rfl⟩ (by norm_num))
theorem R31729 : Reach 31729 := rs (se 2 (by rfl) ⟨11898, by rfl⟩) (B 23797 (by norm_num) ⟨11898, by rfl⟩ (by norm_num))
theorem R31733 : Reach 31733 := rs (se 5 (by rfl) ⟨1487, by rfl⟩) (B 2975 (by norm_num) ⟨1487, by rfl⟩ (by norm_num))
theorem R31737 : Reach 31737 := rs (se 2 (by rfl) ⟨11901, by rfl⟩) (B 23803 (by norm_num) ⟨11901, by rfl⟩ (by norm_num))
theorem R31741 : Reach 31741 := rs (se 3 (by rfl) ⟨5951, by rfl⟩) (B 11903 (by norm_num) ⟨5951, by rfl⟩ (by norm_num))
theorem R31745 : Reach 31745 := rs (se 2 (by rfl) ⟨11904, by rfl⟩) (B 23809 (by norm_num) ⟨11904, by rfl⟩ (by norm_num))
theorem R31749 : Reach 31749 := rs (se 4 (by rfl) ⟨2976, by rfl⟩) (B 5953 (by norm_num) ⟨2976, by rfl⟩ (by norm_num))
theorem R31753 : Reach 31753 := rs (se 2 (by rfl) ⟨11907, by rfl⟩) (B 23815 (by norm_num) ⟨11907, by rfl⟩ (by norm_num))
theorem R31757 : Reach 31757 := rs (se 3 (by rfl) ⟨5954, by rfl⟩) (B 11909 (by norm_num) ⟨5954, by rfl⟩ (by norm_num))
theorem R31761 : Reach 31761 := rs (se 2 (by rfl) ⟨11910, by rfl⟩) (B 23821 (by norm_num) ⟨11910, by rfl⟩ (by norm_num))
theorem R31765 : Reach 31765 := rs (se 6 (by rfl) ⟨744, by rfl⟩) (B 1489 (by norm_num) ⟨744, by rfl⟩ (by norm_num))
theorem R97301 : Reach 97301 := rs (se 6 (by rfl) ⟨2280, by rfl⟩) (B 4561 (by norm_num) ⟨2280, by rfl⟩ (by norm_num))
theorem R31769 : Reach 31769 := rs (se 2 (by rfl) ⟨11913, by rfl⟩) (B 23827 (by norm_num) ⟨11913, by rfl⟩ (by norm_num))
theorem R31773 : Reach 31773 := rs (se 3 (by rfl) ⟨5957, by rfl⟩) (B 11915 (by norm_num) ⟨5957, by rfl⟩ (by norm_num))
theorem R31777 : Reach 31777 := rs (se 2 (by rfl) ⟨11916, by rfl⟩) (B 23833 (by norm_num) ⟨11916, by rfl⟩ (by norm_num))
theorem R31781 : Reach 31781 := rs (se 4 (by rfl) ⟨2979, by rfl⟩) (B 5959 (by norm_num) ⟨2979, by rfl⟩ (by norm_num))
theorem R31785 : Reach 31785 := rs (se 2 (by rfl) ⟨11919, by rfl⟩) (B 23839 (by norm_num) ⟨11919, by rfl⟩ (by norm_num))
theorem R31789 : Reach 31789 := rs (se 3 (by rfl) ⟨5960, by rfl⟩) (B 11921 (by norm_num) ⟨5960, by rfl⟩ (by norm_num))
theorem R31793 : Reach 31793 := rs (se 2 (by rfl) ⟨11922, by rfl⟩) (B 23845 (by norm_num) ⟨11922, by rfl⟩ (by norm_num))
theorem R31797 : Reach 31797 := rs (se 5 (by rfl) ⟨1490, by rfl⟩) (B 2981 (by norm_num) ⟨1490, by rfl⟩ (by norm_num))
theorem R31801 : Reach 31801 := rs (se 2 (by rfl) ⟨11925, by rfl⟩) (B 23851 (by norm_num) ⟨11925, by rfl⟩ (by norm_num))
theorem R31805 : Reach 31805 := rs (se 3 (by rfl) ⟨5963, by rfl⟩) (B 11927 (by norm_num) ⟨5963, by rfl⟩ (by norm_num))
theorem R31809 : Reach 31809 := rs (se 2 (by rfl) ⟨11928, by rfl⟩) (B 23857 (by norm_num) ⟨11928, by rfl⟩ (by norm_num))
theorem R31813 : Reach 31813 := rs (se 4 (by rfl) ⟨2982, by rfl⟩) (B 5965 (by norm_num) ⟨2982, by rfl⟩ (by norm_num))
theorem R31817 : Reach 31817 := rs (se 2 (by rfl) ⟨11931, by rfl⟩) (B 23863 (by norm_num) ⟨11931, by rfl⟩ (by norm_num))
theorem R31821 : Reach 31821 := rs (se 3 (by rfl) ⟨5966, by rfl⟩) (B 11933 (by norm_num) ⟨5966, by rfl⟩ (by norm_num))
theorem R31825 : Reach 31825 := rs (se 2 (by rfl) ⟨11934, by rfl⟩) (B 23869 (by norm_num) ⟨11934, by rfl⟩ (by norm_num))
theorem R31829 : Reach 31829 := rs (se 8 (by rfl) ⟨186, by rfl⟩) (B 373 (by norm_num) ⟨186, by rfl⟩ (by norm_num))
theorem R31833 : Reach 31833 := rs (se 2 (by rfl) ⟨11937, by rfl⟩) (B 23875 (by norm_num) ⟨11937, by rfl⟩ (by norm_num))
theorem R31837 : Reach 31837 := rs (se 3 (by rfl) ⟨5969, by rfl⟩) (B 11939 (by norm_num) ⟨5969, by rfl⟩ (by norm_num))
theorem R31841 : Reach 31841 := rs (se 2 (by rfl) ⟨11940, by rfl⟩) (B 23881 (by norm_num) ⟨11940, by rfl⟩ (by norm_num))
theorem R31845 : Reach 31845 := rs (se 4 (by rfl) ⟨2985, by rfl⟩) (B 5971 (by norm_num) ⟨2985, by rfl⟩ (by norm_num))
theorem R31849 : Reach 31849 := rs (se 2 (by rfl) ⟨11943, by rfl⟩) (B 23887 (by norm_num) ⟨11943, by rfl⟩ (by norm_num))
theorem R31853 : Reach 31853 := rs (se 3 (by rfl) ⟨5972, by rfl⟩) (B 11945 (by norm_num) ⟨5972, by rfl⟩ (by norm_num))
theorem R31857 : Reach 31857 := rs (se 2 (by rfl) ⟨11946, by rfl⟩) (B 23893 (by norm_num) ⟨11946, by rfl⟩ (by norm_num))
theorem R31861 : Reach 31861 := rs (se 5 (by rfl) ⟨1493, by rfl⟩) (B 2987 (by norm_num) ⟨1493, by rfl⟩ (by norm_num))
theorem R31865 : Reach 31865 := rs (se 2 (by rfl) ⟨11949, by rfl⟩) (B 23899 (by norm_num) ⟨11949, by rfl⟩ (by norm_num))
theorem R31869 : Reach 31869 := rs (se 3 (by rfl) ⟨5975, by rfl⟩) (B 11951 (by norm_num) ⟨5975, by rfl⟩ (by norm_num))
theorem R31873 : Reach 31873 := rs (se 2 (by rfl) ⟨11952, by rfl⟩) (B 23905 (by norm_num) ⟨11952, by rfl⟩ (by norm_num))
theorem R31877 : Reach 31877 := rs (se 4 (by rfl) ⟨2988, by rfl⟩) (B 5977 (by norm_num) ⟨2988, by rfl⟩ (by norm_num))
theorem R31881 : Reach 31881 := rs (se 2 (by rfl) ⟨11955, by rfl⟩) (B 23911 (by norm_num) ⟨11955, by rfl⟩ (by norm_num))
theorem R31885 : Reach 31885 := rs (se 3 (by rfl) ⟨5978, by rfl⟩) (B 11957 (by norm_num) ⟨5978, by rfl⟩ (by norm_num))
theorem R31889 : Reach 31889 := rs (se 2 (by rfl) ⟨11958, by rfl⟩) (B 23917 (by norm_num) ⟨11958, by rfl⟩ (by norm_num))
theorem R31893 : Reach 31893 := rs (se 6 (by rfl) ⟨747, by rfl⟩) (B 1495 (by norm_num) ⟨747, by rfl⟩ (by norm_num))
theorem R31897 : Reach 31897 := rs (se 2 (by rfl) ⟨11961, by rfl⟩) (B 23923 (by norm_num) ⟨11961, by rfl⟩ (by norm_num))
theorem R31901 : Reach 31901 := rs (se 3 (by rfl) ⟨5981, by rfl⟩) (B 11963 (by norm_num) ⟨5981, by rfl⟩ (by norm_num))
theorem R31905 : Reach 31905 := rs (se 2 (by rfl) ⟨11964, by rfl⟩) (B 23929 (by norm_num) ⟨11964, by rfl⟩ (by norm_num))
theorem R31909 : Reach 31909 := rs (se 4 (by rfl) ⟨2991, by rfl⟩) (B 5983 (by norm_num) ⟨2991, by rfl⟩ (by norm_num))
theorem R31913 : Reach 31913 := rs (se 2 (by rfl) ⟨11967, by rfl⟩) (B 23935 (by norm_num) ⟨11967, by rfl⟩ (by norm_num))
theorem R31917 : Reach 31917 := rs (se 3 (by rfl) ⟨5984, by rfl⟩) (B 11969 (by norm_num) ⟨5984, by rfl⟩ (by norm_num))
theorem R31921 : Reach 31921 := rs (se 2 (by rfl) ⟨11970, by rfl⟩) (B 23941 (by norm_num) ⟨11970, by rfl⟩ (by norm_num))
theorem R31925 : Reach 31925 := rs (se 5 (by rfl) ⟨1496, by rfl⟩) (B 2993 (by norm_num) ⟨1496, by rfl⟩ (by norm_num))
theorem R31929 : Reach 31929 := rs (se 2 (by rfl) ⟨11973, by rfl⟩) (B 23947 (by norm_num) ⟨11973, by rfl⟩ (by norm_num))
theorem R31933 : Reach 31933 := rs (se 3 (by rfl) ⟨5987, by rfl⟩) (B 11975 (by norm_num) ⟨5987, by rfl⟩ (by norm_num))
theorem R31937 : Reach 31937 := rs (se 2 (by rfl) ⟨11976, by rfl⟩) (B 23953 (by norm_num) ⟨11976, by rfl⟩ (by norm_num))
theorem R31941 : Reach 31941 := rs (se 4 (by rfl) ⟨2994, by rfl⟩) (B 5989 (by norm_num) ⟨2994, by rfl⟩ (by norm_num))
theorem R31945 : Reach 31945 := rs (se 2 (by rfl) ⟨11979, by rfl⟩) (B 23959 (by norm_num) ⟨11979, by rfl⟩ (by norm_num))
theorem R31949 : Reach 31949 := rs (se 3 (by rfl) ⟨5990, by rfl⟩) (B 11981 (by norm_num) ⟨5990, by rfl⟩ (by norm_num))
theorem R31953 : Reach 31953 := rs (se 2 (by rfl) ⟨11982, by rfl⟩) (B 23965 (by norm_num) ⟨11982, by rfl⟩ (by norm_num))
theorem R31957 : Reach 31957 := rs (se 7 (by rfl) ⟨374, by rfl⟩) (B 749 (by norm_num) ⟨374, by rfl⟩ (by norm_num))
theorem R31961 : Reach 31961 := rs (se 2 (by rfl) ⟨11985, by rfl⟩) (B 23971 (by norm_num) ⟨11985, by rfl⟩ (by norm_num))
theorem R31965 : Reach 31965 := rs (se 3 (by rfl) ⟨5993, by rfl⟩) (B 11987 (by norm_num) ⟨5993, by rfl⟩ (by norm_num))
theorem R31969 : Reach 31969 := rs (se 2 (by rfl) ⟨11988, by rfl⟩) (B 23977 (by norm_num) ⟨11988, by rfl⟩ (by norm_num))
theorem R31973 : Reach 31973 := rs (se 4 (by rfl) ⟨2997, by rfl⟩) (B 5995 (by norm_num) ⟨2997, by rfl⟩ (by norm_num))
theorem R31977 : Reach 31977 := rs (se 2 (by rfl) ⟨11991, by rfl⟩) (B 23983 (by norm_num) ⟨11991, by rfl⟩ (by norm_num))
theorem R31981 : Reach 31981 := rs (se 3 (by rfl) ⟨5996, by rfl⟩) (B 11993 (by norm_num) ⟨5996, by rfl⟩ (by norm_num))
theorem R31985 : Reach 31985 := rs (se 2 (by rfl) ⟨11994, by rfl⟩) (B 23989 (by norm_num) ⟨11994, by rfl⟩ (by norm_num))
theorem R31989 : Reach 31989 := rs (se 5 (by rfl) ⟨1499, by rfl⟩) (B 2999 (by norm_num) ⟨1499, by rfl⟩ (by norm_num))
theorem R31993 : Reach 31993 := rs (se 2 (by rfl) ⟨11997, by rfl⟩) (B 23995 (by norm_num) ⟨11997, by rfl⟩ (by norm_num))
theorem R31997 : Reach 31997 := rs (se 3 (by rfl) ⟨5999, by rfl⟩) (B 11999 (by norm_num) ⟨5999, by rfl⟩ (by norm_num))
theorem R32001 : Reach 32001 := rs (se 2 (by rfl) ⟨12000, by rfl⟩) (B 24001 (by norm_num) ⟨12000, by rfl⟩ (by norm_num))
theorem R32005 : Reach 32005 := rs (se 4 (by rfl) ⟨3000, by rfl⟩) (B 6001 (by norm_num) ⟨3000, by rfl⟩ (by norm_num))
theorem R32009 : Reach 32009 := rs (se 2 (by rfl) ⟨12003, by rfl⟩) (B 24007 (by norm_num) ⟨12003, by rfl⟩ (by norm_num))
theorem R32013 : Reach 32013 := rs (se 3 (by rfl) ⟨6002, by rfl⟩) (B 12005 (by norm_num) ⟨6002, by rfl⟩ (by norm_num))
theorem R32017 : Reach 32017 := rs (se 2 (by rfl) ⟨12006, by rfl⟩) (B 24013 (by norm_num) ⟨12006, by rfl⟩ (by norm_num))
theorem R32021 : Reach 32021 := rs (se 6 (by rfl) ⟨750, by rfl⟩) (B 1501 (by norm_num) ⟨750, by rfl⟩ (by norm_num))
theorem R32025 : Reach 32025 := rs (se 2 (by rfl) ⟨12009, by rfl⟩) (B 24019 (by norm_num) ⟨12009, by rfl⟩ (by norm_num))
theorem R32029 : Reach 32029 := rs (se 3 (by rfl) ⟨6005, by rfl⟩) (B 12011 (by norm_num) ⟨6005, by rfl⟩ (by norm_num))
theorem R32033 : Reach 32033 := rs (se 2 (by rfl) ⟨12012, by rfl⟩) (B 24025 (by norm_num) ⟨12012, by rfl⟩ (by norm_num))
theorem R32037 : Reach 32037 := rs (se 4 (by rfl) ⟨3003, by rfl⟩) (B 6007 (by norm_num) ⟨3003, by rfl⟩ (by norm_num))
theorem R32041 : Reach 32041 := rs (se 2 (by rfl) ⟨12015, by rfl⟩) (B 24031 (by norm_num) ⟨12015, by rfl⟩ (by norm_num))
theorem R32045 : Reach 32045 := rs (se 3 (by rfl) ⟨6008, by rfl⟩) (B 12017 (by norm_num) ⟨6008, by rfl⟩ (by norm_num))
theorem R64813 : Reach 64813 := rs (se 3 (by rfl) ⟨12152, by rfl⟩) (B 24305 (by norm_num) ⟨12152, by rfl⟩ (by norm_num))
theorem R32049 : Reach 32049 := rs (se 2 (by rfl) ⟨12018, by rfl⟩) (B 24037 (by norm_num) ⟨12018, by rfl⟩ (by norm_num))
theorem R32053 : Reach 32053 := rs (se 5 (by rfl) ⟨1502, by rfl⟩) (B 3005 (by norm_num) ⟨1502, by rfl⟩ (by norm_num))
theorem R32057 : Reach 32057 := rs (se 2 (by rfl) ⟨12021, by rfl⟩) (B 24043 (by norm_num) ⟨12021, by rfl⟩ (by norm_num))
theorem R32061 : Reach 32061 := rs (se 3 (by rfl) ⟨6011, by rfl⟩) (B 12023 (by norm_num) ⟨6011, by rfl⟩ (by norm_num))
theorem R32065 : Reach 32065 := rs (se 2 (by rfl) ⟨12024, by rfl⟩) (B 24049 (by norm_num) ⟨12024, by rfl⟩ (by norm_num))
theorem R32069 : Reach 32069 := rs (se 4 (by rfl) ⟨3006, by rfl⟩) (B 6013 (by norm_num) ⟨3006, by rfl⟩ (by norm_num))
theorem R32073 : Reach 32073 := rs (se 2 (by rfl) ⟨12027, by rfl⟩) (B 24055 (by norm_num) ⟨12027, by rfl⟩ (by norm_num))
theorem R32077 : Reach 32077 := rs (se 3 (by rfl) ⟨6014, by rfl⟩) (B 12029 (by norm_num) ⟨6014, by rfl⟩ (by norm_num))
theorem R32081 : Reach 32081 := rs (se 2 (by rfl) ⟨12030, by rfl⟩) (B 24061 (by norm_num) ⟨12030, by rfl⟩ (by norm_num))
theorem R32085 : Reach 32085 := rs (se 11 (by rfl) ⟨23, by rfl⟩) (B 47 (by norm_num) ⟨23, by rfl⟩ (by norm_num))
theorem R32089 : Reach 32089 := rs (se 2 (by rfl) ⟨12033, by rfl⟩) (B 24067 (by norm_num) ⟨12033, by rfl⟩ (by norm_num))
theorem R32093 : Reach 32093 := rs (se 3 (by rfl) ⟨6017, by rfl⟩) (B 12035 (by norm_num) ⟨6017, by rfl⟩ (by norm_num))
theorem R32097 : Reach 32097 := rs (se 2 (by rfl) ⟨12036, by rfl⟩) (B 24073 (by norm_num) ⟨12036, by rfl⟩ (by norm_num))
theorem R32101 : Reach 32101 := rs (se 4 (by rfl) ⟨3009, by rfl⟩) (B 6019 (by norm_num) ⟨3009, by rfl⟩ (by norm_num))
theorem R32105 : Reach 32105 := rs (se 2 (by rfl) ⟨12039, by rfl⟩) (B 24079 (by norm_num) ⟨12039, by rfl⟩ (by norm_num))
theorem R32109 : Reach 32109 := rs (se 3 (by rfl) ⟨6020, by rfl⟩) (B 12041 (by norm_num) ⟨6020, by rfl⟩ (by norm_num))
theorem R32113 : Reach 32113 := rs (se 2 (by rfl) ⟨12042, by rfl⟩) (B 24085 (by norm_num) ⟨12042, by rfl⟩ (by norm_num))
theorem R32117 : Reach 32117 := rs (se 5 (by rfl) ⟨1505, by rfl⟩) (B 3011 (by norm_num) ⟨1505, by rfl⟩ (by norm_num))
theorem R32121 : Reach 32121 := rs (se 2 (by rfl) ⟨12045, by rfl⟩) (B 24091 (by norm_num) ⟨12045, by rfl⟩ (by norm_num))
theorem R32125 : Reach 32125 := rs (se 3 (by rfl) ⟨6023, by rfl⟩) (B 12047 (by norm_num) ⟨6023, by rfl⟩ (by norm_num))
theorem R32129 : Reach 32129 := rs (se 2 (by rfl) ⟨12048, by rfl⟩) (B 24097 (by norm_num) ⟨12048, by rfl⟩ (by norm_num))
theorem R32133 : Reach 32133 := rs (se 4 (by rfl) ⟨3012, by rfl⟩) (B 6025 (by norm_num) ⟨3012, by rfl⟩ (by norm_num))
theorem R32137 : Reach 32137 := rs (se 2 (by rfl) ⟨12051, by rfl⟩) (B 24103 (by norm_num) ⟨12051, by rfl⟩ (by norm_num))
theorem R32141 : Reach 32141 := rs (se 3 (by rfl) ⟨6026, by rfl⟩) (B 12053 (by norm_num) ⟨6026, by rfl⟩ (by norm_num))
theorem R32145 : Reach 32145 := rs (se 2 (by rfl) ⟨12054, by rfl⟩) (B 24109 (by norm_num) ⟨12054, by rfl⟩ (by norm_num))
theorem R32149 : Reach 32149 := rs (se 6 (by rfl) ⟨753, by rfl⟩) (B 1507 (by norm_num) ⟨753, by rfl⟩ (by norm_num))
theorem R32153 : Reach 32153 := rs (se 2 (by rfl) ⟨12057, by rfl⟩) (B 24115 (by norm_num) ⟨12057, by rfl⟩ (by norm_num))
theorem R32157 : Reach 32157 := rs (se 3 (by rfl) ⟨6029, by rfl⟩) (B 12059 (by norm_num) ⟨6029, by rfl⟩ (by norm_num))
theorem R32161 : Reach 32161 := rs (se 2 (by rfl) ⟨12060, by rfl⟩) (B 24121 (by norm_num) ⟨12060, by rfl⟩ (by norm_num))
theorem R32165 : Reach 32165 := rs (se 4 (by rfl) ⟨3015, by rfl⟩) (B 6031 (by norm_num) ⟨3015, by rfl⟩ (by norm_num))
theorem R32169 : Reach 32169 := rs (se 2 (by rfl) ⟨12063, by rfl⟩) (B 24127 (by norm_num) ⟨12063, by rfl⟩ (by norm_num))
theorem R32173 : Reach 32173 := rs (se 3 (by rfl) ⟨6032, by rfl⟩) (B 12065 (by norm_num) ⟨6032, by rfl⟩ (by norm_num))
theorem R32177 : Reach 32177 := rs (se 2 (by rfl) ⟨12066, by rfl⟩) (B 24133 (by norm_num) ⟨12066, by rfl⟩ (by norm_num))
theorem R32181 : Reach 32181 := rs (se 5 (by rfl) ⟨1508, by rfl⟩) (B 3017 (by norm_num) ⟨1508, by rfl⟩ (by norm_num))
theorem R32185 : Reach 32185 := rs (se 2 (by rfl) ⟨12069, by rfl⟩) (B 24139 (by norm_num) ⟨12069, by rfl⟩ (by norm_num))
theorem R32189 : Reach 32189 := rs (se 3 (by rfl) ⟨6035, by rfl⟩) (B 12071 (by norm_num) ⟨6035, by rfl⟩ (by norm_num))
theorem R64957 : Reach 64957 := rs (se 3 (by rfl) ⟨12179, by rfl⟩) (B 24359 (by norm_num) ⟨12179, by rfl⟩ (by norm_num))
theorem R32193 : Reach 32193 := rs (se 2 (by rfl) ⟨12072, by rfl⟩) (B 24145 (by norm_num) ⟨12072, by rfl⟩ (by norm_num))
theorem R32197 : Reach 32197 := rs (se 4 (by rfl) ⟨3018, by rfl⟩) (B 6037 (by norm_num) ⟨3018, by rfl⟩ (by norm_num))
theorem R32201 : Reach 32201 := rs (se 2 (by rfl) ⟨12075, by rfl⟩) (B 24151 (by norm_num) ⟨12075, by rfl⟩ (by norm_num))
theorem R32205 : Reach 32205 := rs (se 3 (by rfl) ⟨6038, by rfl⟩) (B 12077 (by norm_num) ⟨6038, by rfl⟩ (by norm_num))
theorem R32209 : Reach 32209 := rs (se 2 (by rfl) ⟨12078, by rfl⟩) (B 24157 (by norm_num) ⟨12078, by rfl⟩ (by norm_num))
theorem R32213 : Reach 32213 := rs (se 7 (by rfl) ⟨377, by rfl⟩) (B 755 (by norm_num) ⟨377, by rfl⟩ (by norm_num))
theorem R32217 : Reach 32217 := rs (se 2 (by rfl) ⟨12081, by rfl⟩) (B 24163 (by norm_num) ⟨12081, by rfl⟩ (by norm_num))
theorem R32221 : Reach 32221 := rs (se 3 (by rfl) ⟨6041, by rfl⟩) (B 12083 (by norm_num) ⟨6041, by rfl⟩ (by norm_num))
theorem R32225 : Reach 32225 := rs (se 2 (by rfl) ⟨12084, by rfl⟩) (B 24169 (by norm_num) ⟨12084, by rfl⟩ (by norm_num))
theorem R32229 : Reach 32229 := rs (se 4 (by rfl) ⟨3021, by rfl⟩) (B 6043 (by norm_num) ⟨3021, by rfl⟩ (by norm_num))
theorem R32233 : Reach 32233 := rs (se 2 (by rfl) ⟨12087, by rfl⟩) (B 24175 (by norm_num) ⟨12087, by rfl⟩ (by norm_num))
theorem R32237 : Reach 32237 := rs (se 3 (by rfl) ⟨6044, by rfl⟩) (B 12089 (by norm_num) ⟨6044, by rfl⟩ (by norm_num))
theorem R32241 : Reach 32241 := rs (se 2 (by rfl) ⟨12090, by rfl⟩) (B 24181 (by norm_num) ⟨12090, by rfl⟩ (by norm_num))
theorem R32245 : Reach 32245 := rs (se 5 (by rfl) ⟨1511, by rfl⟩) (B 3023 (by norm_num) ⟨1511, by rfl⟩ (by norm_num))
theorem R32249 : Reach 32249 := rs (se 2 (by rfl) ⟨12093, by rfl⟩) (B 24187 (by norm_num) ⟨12093, by rfl⟩ (by norm_num))
theorem R32253 : Reach 32253 := rs (se 3 (by rfl) ⟨6047, by rfl⟩) (B 12095 (by norm_num) ⟨6047, by rfl⟩ (by norm_num))
theorem R32257 : Reach 32257 := rs (se 2 (by rfl) ⟨12096, by rfl⟩) (B 24193 (by norm_num) ⟨12096, by rfl⟩ (by norm_num))
theorem R32261 : Reach 32261 := rs (se 4 (by rfl) ⟨3024, by rfl⟩) (B 6049 (by norm_num) ⟨3024, by rfl⟩ (by norm_num))
theorem R32265 : Reach 32265 := rs (se 2 (by rfl) ⟨12099, by rfl⟩) (B 24199 (by norm_num) ⟨12099, by rfl⟩ (by norm_num))
theorem R32269 : Reach 32269 := rs (se 3 (by rfl) ⟨6050, by rfl⟩) (B 12101 (by norm_num) ⟨6050, by rfl⟩ (by norm_num))
theorem R32273 : Reach 32273 := rs (se 2 (by rfl) ⟨12102, by rfl⟩) (B 24205 (by norm_num) ⟨12102, by rfl⟩ (by norm_num))
theorem R32277 : Reach 32277 := rs (se 6 (by rfl) ⟨756, by rfl⟩) (B 1513 (by norm_num) ⟨756, by rfl⟩ (by norm_num))
theorem R32281 : Reach 32281 := rs (se 2 (by rfl) ⟨12105, by rfl⟩) (B 24211 (by norm_num) ⟨12105, by rfl⟩ (by norm_num))
theorem R32285 : Reach 32285 := rs (se 3 (by rfl) ⟨6053, by rfl⟩) (B 12107 (by norm_num) ⟨6053, by rfl⟩ (by norm_num))
theorem R32289 : Reach 32289 := rs (se 2 (by rfl) ⟨12108, by rfl⟩) (B 24217 (by norm_num) ⟨12108, by rfl⟩ (by norm_num))
theorem R32293 : Reach 32293 := rs (se 4 (by rfl) ⟨3027, by rfl⟩) (B 6055 (by norm_num) ⟨3027, by rfl⟩ (by norm_num))
theorem R32297 : Reach 32297 := rs (se 2 (by rfl) ⟨12111, by rfl⟩) (B 24223 (by norm_num) ⟨12111, by rfl⟩ (by norm_num))
theorem R32301 : Reach 32301 := rs (se 3 (by rfl) ⟨6056, by rfl⟩) (B 12113 (by norm_num) ⟨6056, by rfl⟩ (by norm_num))
theorem R32305 : Reach 32305 := rs (se 2 (by rfl) ⟨12114, by rfl⟩) (B 24229 (by norm_num) ⟨12114, by rfl⟩ (by norm_num))
theorem R32309 : Reach 32309 := rs (se 5 (by rfl) ⟨1514, by rfl⟩) (B 3029 (by norm_num) ⟨1514, by rfl⟩ (by norm_num))
theorem R32313 : Reach 32313 := rs (se 2 (by rfl) ⟨12117, by rfl⟩) (B 24235 (by norm_num) ⟨12117, by rfl⟩ (by norm_num))
theorem R32317 : Reach 32317 := rs (se 3 (by rfl) ⟨6059, by rfl⟩) (B 12119 (by norm_num) ⟨6059, by rfl⟩ (by norm_num))
theorem R32321 : Reach 32321 := rs (se 2 (by rfl) ⟨12120, by rfl⟩) (B 24241 (by norm_num) ⟨12120, by rfl⟩ (by norm_num))
theorem R32325 : Reach 32325 := rs (se 4 (by rfl) ⟨3030, by rfl⟩) (B 6061 (by norm_num) ⟨3030, by rfl⟩ (by norm_num))
theorem R32329 : Reach 32329 := rs (se 2 (by rfl) ⟨12123, by rfl⟩) (B 24247 (by norm_num) ⟨12123, by rfl⟩ (by norm_num))
theorem R32333 : Reach 32333 := rs (se 3 (by rfl) ⟨6062, by rfl⟩) (B 12125 (by norm_num) ⟨6062, by rfl⟩ (by norm_num))
theorem R32337 : Reach 32337 := rs (se 2 (by rfl) ⟨12126, by rfl⟩) (B 24253 (by norm_num) ⟨12126, by rfl⟩ (by norm_num))
theorem R32341 : Reach 32341 := rs (se 8 (by rfl) ⟨189, by rfl⟩) (B 379 (by norm_num) ⟨189, by rfl⟩ (by norm_num))
theorem R32345 : Reach 32345 := rs (se 2 (by rfl) ⟨12129, by rfl⟩) (B 24259 (by norm_num) ⟨12129, by rfl⟩ (by norm_num))
theorem R32349 : Reach 32349 := rs (se 3 (by rfl) ⟨6065, by rfl⟩) (B 12131 (by norm_num) ⟨6065, by rfl⟩ (by norm_num))
theorem R65117 : Reach 65117 := rs (se 3 (by rfl) ⟨12209, by rfl⟩) (B 24419 (by norm_num) ⟨12209, by rfl⟩ (by norm_num))
theorem R32353 : Reach 32353 := rs (se 2 (by rfl) ⟨12132, by rfl⟩) (B 24265 (by norm_num) ⟨12132, by rfl⟩ (by norm_num))
theorem R32357 : Reach 32357 := rs (se 4 (by rfl) ⟨3033, by rfl⟩) (B 6067 (by norm_num) ⟨3033, by rfl⟩ (by norm_num))
theorem R32361 : Reach 32361 := rs (se 2 (by rfl) ⟨12135, by rfl⟩) (B 24271 (by norm_num) ⟨12135, by rfl⟩ (by norm_num))
theorem R32365 : Reach 32365 := rs (se 3 (by rfl) ⟨6068, by rfl⟩) (B 12137 (by norm_num) ⟨6068, by rfl⟩ (by norm_num))
theorem R32369 : Reach 32369 := rs (se 2 (by rfl) ⟨12138, by rfl⟩) (B 24277 (by norm_num) ⟨12138, by rfl⟩ (by norm_num))
theorem R32373 : Reach 32373 := rs (se 5 (by rfl) ⟨1517, by rfl⟩) (B 3035 (by norm_num) ⟨1517, by rfl⟩ (by norm_num))
theorem R32377 : Reach 32377 := rs (se 2 (by rfl) ⟨12141, by rfl⟩) (B 24283 (by norm_num) ⟨12141, by rfl⟩ (by norm_num))
theorem R32381 : Reach 32381 := rs (se 3 (by rfl) ⟨6071, by rfl⟩) (B 12143 (by norm_num) ⟨6071, by rfl⟩ (by norm_num))
theorem R32385 : Reach 32385 := rs (se 2 (by rfl) ⟨12144, by rfl⟩) (B 24289 (by norm_num) ⟨12144, by rfl⟩ (by norm_num))
theorem R32389 : Reach 32389 := rs (se 4 (by rfl) ⟨3036, by rfl⟩) (B 6073 (by norm_num) ⟨3036, by rfl⟩ (by norm_num))
theorem R32393 : Reach 32393 := rs (se 2 (by rfl) ⟨12147, by rfl⟩) (B 24295 (by norm_num) ⟨12147, by rfl⟩ (by norm_num))
theorem R32397 : Reach 32397 := rs (se 3 (by rfl) ⟨6074, by rfl⟩) (B 12149 (by norm_num) ⟨6074, by rfl⟩ (by norm_num))
theorem R32401 : Reach 32401 := rs (se 2 (by rfl) ⟨12150, by rfl⟩) (B 24301 (by norm_num) ⟨12150, by rfl⟩ (by norm_num))
theorem R32405 : Reach 32405 := rs (se 6 (by rfl) ⟨759, by rfl⟩) (B 1519 (by norm_num) ⟨759, by rfl⟩ (by norm_num))
theorem R32409 : Reach 32409 := rs (se 2 (by rfl) ⟨12153, by rfl⟩) (B 24307 (by norm_num) ⟨12153, by rfl⟩ (by norm_num))
theorem R32413 : Reach 32413 := rs (se 3 (by rfl) ⟨6077, by rfl⟩) (B 12155 (by norm_num) ⟨6077, by rfl⟩ (by norm_num))
theorem R32417 : Reach 32417 := rs (se 2 (by rfl) ⟨12156, by rfl⟩) (B 24313 (by norm_num) ⟨12156, by rfl⟩ (by norm_num))
theorem R32421 : Reach 32421 := rs (se 4 (by rfl) ⟨3039, by rfl⟩) (B 6079 (by norm_num) ⟨3039, by rfl⟩ (by norm_num))
theorem R32425 : Reach 32425 := rs (se 2 (by rfl) ⟨12159, by rfl⟩) (B 24319 (by norm_num) ⟨12159, by rfl⟩ (by norm_num))
theorem R32429 : Reach 32429 := rs (se 3 (by rfl) ⟨6080, by rfl⟩) (B 12161 (by norm_num) ⟨6080, by rfl⟩ (by norm_num))
theorem R32433 : Reach 32433 := rs (se 2 (by rfl) ⟨12162, by rfl⟩) (B 24325 (by norm_num) ⟨12162, by rfl⟩ (by norm_num))
theorem R32437 : Reach 32437 := rs (se 5 (by rfl) ⟨1520, by rfl⟩) (B 3041 (by norm_num) ⟨1520, by rfl⟩ (by norm_num))
theorem R32441 : Reach 32441 := rs (se 2 (by rfl) ⟨12165, by rfl⟩) (B 24331 (by norm_num) ⟨12165, by rfl⟩ (by norm_num))
theorem R32445 : Reach 32445 := rs (se 3 (by rfl) ⟨6083, by rfl⟩) (B 12167 (by norm_num) ⟨6083, by rfl⟩ (by norm_num))
theorem R32449 : Reach 32449 := rs (se 2 (by rfl) ⟨12168, by rfl⟩) (B 24337 (by norm_num) ⟨12168, by rfl⟩ (by norm_num))
theorem R32453 : Reach 32453 := rs (se 4 (by rfl) ⟨3042, by rfl⟩) (B 6085 (by norm_num) ⟨3042, by rfl⟩ (by norm_num))
theorem R32457 : Reach 32457 := rs (se 2 (by rfl) ⟨12171, by rfl⟩) (B 24343 (by norm_num) ⟨12171, by rfl⟩ (by norm_num))
theorem R32461 : Reach 32461 := rs (se 3 (by rfl) ⟨6086, by rfl⟩) (B 12173 (by norm_num) ⟨6086, by rfl⟩ (by norm_num))
theorem R32465 : Reach 32465 := rs (se 2 (by rfl) ⟨12174, by rfl⟩) (B 24349 (by norm_num) ⟨12174, by rfl⟩ (by norm_num))
theorem R32469 : Reach 32469 := rs (se 7 (by rfl) ⟨380, by rfl⟩) (B 761 (by norm_num) ⟨380, by rfl⟩ (by norm_num))
theorem R98005 : Reach 98005 := rs (se 7 (by rfl) ⟨1148, by rfl⟩) (B 2297 (by norm_num) ⟨1148, by rfl⟩ (by norm_num))
theorem R32473 : Reach 32473 := rs (se 2 (by rfl) ⟨12177, by rfl⟩) (B 24355 (by norm_num) ⟨12177, by rfl⟩ (by norm_num))
theorem R32477 : Reach 32477 := rs (se 3 (by rfl) ⟨6089, by rfl⟩) (B 12179 (by norm_num) ⟨6089, by rfl⟩ (by norm_num))
theorem R32481 : Reach 32481 := rs (se 2 (by rfl) ⟨12180, by rfl⟩) (B 24361 (by norm_num) ⟨12180, by rfl⟩ (by norm_num))
theorem R32485 : Reach 32485 := rs (se 4 (by rfl) ⟨3045, by rfl⟩) (B 6091 (by norm_num) ⟨3045, by rfl⟩ (by norm_num))
theorem R32489 : Reach 32489 := rs (se 2 (by rfl) ⟨12183, by rfl⟩) (B 24367 (by norm_num) ⟨12183, by rfl⟩ (by norm_num))
theorem R32493 : Reach 32493 := rs (se 3 (by rfl) ⟨6092, by rfl⟩) (B 12185 (by norm_num) ⟨6092, by rfl⟩ (by norm_num))
theorem R65261 : Reach 65261 := rs (se 3 (by rfl) ⟨12236, by rfl⟩) (B 24473 (by norm_num) ⟨12236, by rfl⟩ (by norm_num))
theorem R32497 : Reach 32497 := rs (se 2 (by rfl) ⟨12186, by rfl⟩) (B 24373 (by norm_num) ⟨12186, by rfl⟩ (by norm_num))
theorem R32501 : Reach 32501 := rs (se 5 (by rfl) ⟨1523, by rfl⟩) (B 3047 (by norm_num) ⟨1523, by rfl⟩ (by norm_num))
theorem R32505 : Reach 32505 := rs (se 2 (by rfl) ⟨12189, by rfl⟩) (B 24379 (by norm_num) ⟨12189, by rfl⟩ (by norm_num))
theorem R32509 : Reach 32509 := rs (se 3 (by rfl) ⟨6095, by rfl⟩) (B 12191 (by norm_num) ⟨6095, by rfl⟩ (by norm_num))
theorem R32513 : Reach 32513 := rs (se 2 (by rfl) ⟨12192, by rfl⟩) (B 24385 (by norm_num) ⟨12192, by rfl⟩ (by norm_num))
theorem R32517 : Reach 32517 := rs (se 4 (by rfl) ⟨3048, by rfl⟩) (B 6097 (by norm_num) ⟨3048, by rfl⟩ (by norm_num))
theorem R32521 : Reach 32521 := rs (se 2 (by rfl) ⟨12195, by rfl⟩) (B 24391 (by norm_num) ⟨12195, by rfl⟩ (by norm_num))
theorem R32525 : Reach 32525 := rs (se 3 (by rfl) ⟨6098, by rfl⟩) (B 12197 (by norm_num) ⟨6098, by rfl⟩ (by norm_num))
theorem R32529 : Reach 32529 := rs (se 2 (by rfl) ⟨12198, by rfl⟩) (B 24397 (by norm_num) ⟨12198, by rfl⟩ (by norm_num))
theorem R32533 : Reach 32533 := rs (se 6 (by rfl) ⟨762, by rfl⟩) (B 1525 (by norm_num) ⟨762, by rfl⟩ (by norm_num))
theorem R32537 : Reach 32537 := rs (se 2 (by rfl) ⟨12201, by rfl⟩) (B 24403 (by norm_num) ⟨12201, by rfl⟩ (by norm_num))
theorem R32541 : Reach 32541 := rs (se 3 (by rfl) ⟨6101, by rfl⟩) (B 12203 (by norm_num) ⟨6101, by rfl⟩ (by norm_num))
theorem R32545 : Reach 32545 := rs (se 2 (by rfl) ⟨12204, by rfl⟩) (B 24409 (by norm_num) ⟨12204, by rfl⟩ (by norm_num))
theorem R32549 : Reach 32549 := rs (se 4 (by rfl) ⟨3051, by rfl⟩) (B 6103 (by norm_num) ⟨3051, by rfl⟩ (by norm_num))
theorem R32553 : Reach 32553 := rs (se 2 (by rfl) ⟨12207, by rfl⟩) (B 24415 (by norm_num) ⟨12207, by rfl⟩ (by norm_num))
theorem R32557 : Reach 32557 := rs (se 3 (by rfl) ⟨6104, by rfl⟩) (B 12209 (by norm_num) ⟨6104, by rfl⟩ (by norm_num))
theorem R32561 : Reach 32561 := rs (se 2 (by rfl) ⟨12210, by rfl⟩) (B 24421 (by norm_num) ⟨12210, by rfl⟩ (by norm_num))
theorem R32565 : Reach 32565 := rs (se 5 (by rfl) ⟨1526, by rfl⟩) (B 3053 (by norm_num) ⟨1526, by rfl⟩ (by norm_num))
theorem R32569 : Reach 32569 := rs (se 2 (by rfl) ⟨12213, by rfl⟩) (B 24427 (by norm_num) ⟨12213, by rfl⟩ (by norm_num))
theorem R32573 : Reach 32573 := rs (se 3 (by rfl) ⟨6107, by rfl⟩) (B 12215 (by norm_num) ⟨6107, by rfl⟩ (by norm_num))
theorem R32577 : Reach 32577 := rs (se 2 (by rfl) ⟨12216, by rfl⟩) (B 24433 (by norm_num) ⟨12216, by rfl⟩ (by norm_num))
theorem R32581 : Reach 32581 := rs (se 4 (by rfl) ⟨3054, by rfl⟩) (B 6109 (by norm_num) ⟨3054, by rfl⟩ (by norm_num))
theorem R32585 : Reach 32585 := rs (se 2 (by rfl) ⟨12219, by rfl⟩) (B 24439 (by norm_num) ⟨12219, by rfl⟩ (by norm_num))
theorem R32589 : Reach 32589 := rs (se 3 (by rfl) ⟨6110, by rfl⟩) (B 12221 (by norm_num) ⟨6110, by rfl⟩ (by norm_num))
theorem R32593 : Reach 32593 := rs (se 2 (by rfl) ⟨12222, by rfl⟩) (B 24445 (by norm_num) ⟨12222, by rfl⟩ (by norm_num))
theorem R32597 : Reach 32597 := rs (se 9 (by rfl) ⟨95, by rfl⟩) (B 191 (by norm_num) ⟨95, by rfl⟩ (by norm_num))
theorem R32601 : Reach 32601 := rs (se 2 (by rfl) ⟨12225, by rfl⟩) (B 24451 (by norm_num) ⟨12225, by rfl⟩ (by norm_num))
theorem R32605 : Reach 32605 := rs (se 3 (by rfl) ⟨6113, by rfl⟩) (B 12227 (by norm_num) ⟨6113, by rfl⟩ (by norm_num))
theorem R32609 : Reach 32609 := rs (se 2 (by rfl) ⟨12228, by rfl⟩) (B 24457 (by norm_num) ⟨12228, by rfl⟩ (by norm_num))
theorem R32613 : Reach 32613 := rs (se 4 (by rfl) ⟨3057, by rfl⟩) (B 6115 (by norm_num) ⟨3057, by rfl⟩ (by norm_num))
theorem R32617 : Reach 32617 := rs (se 2 (by rfl) ⟨12231, by rfl⟩) (B 24463 (by norm_num) ⟨12231, by rfl⟩ (by norm_num))
theorem R32621 : Reach 32621 := rs (se 3 (by rfl) ⟨6116, by rfl⟩) (B 12233 (by norm_num) ⟨6116, by rfl⟩ (by norm_num))
theorem R32625 : Reach 32625 := rs (se 2 (by rfl) ⟨12234, by rfl⟩) (B 24469 (by norm_num) ⟨12234, by rfl⟩ (by norm_num))
theorem R32629 : Reach 32629 := rs (se 5 (by rfl) ⟨1529, by rfl⟩) (B 3059 (by norm_num) ⟨1529, by rfl⟩ (by norm_num))
theorem R98165 : Reach 98165 := rs (se 5 (by rfl) ⟨4601, by rfl⟩) (B 9203 (by norm_num) ⟨4601, by rfl⟩ (by norm_num))
theorem R32633 : Reach 32633 := rs (se 2 (by rfl) ⟨12237, by rfl⟩) (B 24475 (by norm_num) ⟨12237, by rfl⟩ (by norm_num))
theorem R32637 : Reach 32637 := rs (se 3 (by rfl) ⟨6119, by rfl⟩) (B 12239 (by norm_num) ⟨6119, by rfl⟩ (by norm_num))
theorem R32641 : Reach 32641 := rs (se 2 (by rfl) ⟨12240, by rfl⟩) (B 24481 (by norm_num) ⟨12240, by rfl⟩ (by norm_num))
theorem R32645 : Reach 32645 := rs (se 4 (by rfl) ⟨3060, by rfl⟩) (B 6121 (by norm_num) ⟨3060, by rfl⟩ (by norm_num))
theorem R32649 : Reach 32649 := rs (se 2 (by rfl) ⟨12243, by rfl⟩) (B 24487 (by norm_num) ⟨12243, by rfl⟩ (by norm_num))
theorem R32653 : Reach 32653 := rs (se 3 (by rfl) ⟨6122, by rfl⟩) (B 12245 (by norm_num) ⟨6122, by rfl⟩ (by norm_num))
theorem R32657 : Reach 32657 := rs (se 2 (by rfl) ⟨12246, by rfl⟩) (B 24493 (by norm_num) ⟨12246, by rfl⟩ (by norm_num))
theorem R32661 : Reach 32661 := rs (se 6 (by rfl) ⟨765, by rfl⟩) (B 1531 (by norm_num) ⟨765, by rfl⟩ (by norm_num))
theorem R32665 : Reach 32665 := rs (se 2 (by rfl) ⟨12249, by rfl⟩) (B 24499 (by norm_num) ⟨12249, by rfl⟩ (by norm_num))
theorem R32669 : Reach 32669 := rs (se 3 (by rfl) ⟨6125, by rfl⟩) (B 12251 (by norm_num) ⟨6125, by rfl⟩ (by norm_num))
theorem R32673 : Reach 32673 := rs (se 2 (by rfl) ⟨12252, by rfl⟩) (B 24505 (by norm_num) ⟨12252, by rfl⟩ (by norm_num))
theorem R32677 : Reach 32677 := rs (se 4 (by rfl) ⟨3063, by rfl⟩) (B 6127 (by norm_num) ⟨3063, by rfl⟩ (by norm_num))
theorem R32681 : Reach 32681 := rs (se 2 (by rfl) ⟨12255, by rfl⟩) (B 24511 (by norm_num) ⟨12255, by rfl⟩ (by norm_num))
theorem R32685 : Reach 32685 := rs (se 3 (by rfl) ⟨6128, by rfl⟩) (B 12257 (by norm_num) ⟨6128, by rfl⟩ (by norm_num))
theorem R32689 : Reach 32689 := rs (se 2 (by rfl) ⟨12258, by rfl⟩) (B 24517 (by norm_num) ⟨12258, by rfl⟩ (by norm_num))
theorem R32693 : Reach 32693 := rs (se 5 (by rfl) ⟨1532, by rfl⟩) (B 3065 (by norm_num) ⟨1532, by rfl⟩ (by norm_num))
theorem R32697 : Reach 32697 := rs (se 2 (by rfl) ⟨12261, by rfl⟩) (B 24523 (by norm_num) ⟨12261, by rfl⟩ (by norm_num))
theorem R32701 : Reach 32701 := rs (se 3 (by rfl) ⟨6131, by rfl⟩) (B 12263 (by norm_num) ⟨6131, by rfl⟩ (by norm_num))
theorem R32705 : Reach 32705 := rs (se 2 (by rfl) ⟨12264, by rfl⟩) (B 24529 (by norm_num) ⟨12264, by rfl⟩ (by norm_num))
theorem R163781 : Reach 163781 := rs (se 4 (by rfl) ⟨15354, by rfl⟩) (B 30709 (by norm_num) ⟨15354, by rfl⟩ (by norm_num))
theorem R32709 : Reach 32709 := rs (se 4 (by rfl) ⟨3066, by rfl⟩) (B 6133 (by norm_num) ⟨3066, by rfl⟩ (by norm_num))
theorem R32713 : Reach 32713 := rs (se 2 (by rfl) ⟨12267, by rfl⟩) (B 24535 (by norm_num) ⟨12267, by rfl⟩ (by norm_num))
theorem R32717 : Reach 32717 := rs (se 3 (by rfl) ⟨6134, by rfl⟩) (B 12269 (by norm_num) ⟨6134, by rfl⟩ (by norm_num))
theorem R32721 : Reach 32721 := rs (se 2 (by rfl) ⟨12270, by rfl⟩) (B 24541 (by norm_num) ⟨12270, by rfl⟩ (by norm_num))
theorem R32725 : Reach 32725 := rs (se 7 (by rfl) ⟨383, by rfl⟩) (B 767 (by norm_num) ⟨383, by rfl⟩ (by norm_num))
theorem R32729 : Reach 32729 := rs (se 2 (by rfl) ⟨12273, by rfl⟩) (B 24547 (by norm_num) ⟨12273, by rfl⟩ (by norm_num))
theorem R32733 : Reach 32733 := rs (se 3 (by rfl) ⟨6137, by rfl⟩) (B 12275 (by norm_num) ⟨6137, by rfl⟩ (by norm_num))
theorem R32737 : Reach 32737 := rs (se 2 (by rfl) ⟨12276, by rfl⟩) (B 24553 (by norm_num) ⟨12276, by rfl⟩ (by norm_num))
theorem R32741 : Reach 32741 := rs (se 4 (by rfl) ⟨3069, by rfl⟩) (B 6139 (by norm_num) ⟨3069, by rfl⟩ (by norm_num))
theorem R32745 : Reach 32745 := rs (se 2 (by rfl) ⟨12279, by rfl⟩) (B 24559 (by norm_num) ⟨12279, by rfl⟩ (by norm_num))
theorem R32749 : Reach 32749 := rs (se 3 (by rfl) ⟨6140, by rfl⟩) (B 12281 (by norm_num) ⟨6140, by rfl⟩ (by norm_num))
theorem R32753 : Reach 32753 := rs (se 2 (by rfl) ⟨12282, by rfl⟩) (B 24565 (by norm_num) ⟨12282, by rfl⟩ (by norm_num))
theorem R32757 : Reach 32757 := rs (se 5 (by rfl) ⟨1535, by rfl⟩) (B 3071 (by norm_num) ⟨1535, by rfl⟩ (by norm_num))
theorem R32761 : Reach 32761 := rs (se 2 (by rfl) ⟨12285, by rfl⟩) (B 24571 (by norm_num) ⟨12285, by rfl⟩ (by norm_num))
theorem R32765 : Reach 32765 := rs (se 3 (by rfl) ⟨6143, by rfl⟩) (B 12287 (by norm_num) ⟨6143, by rfl⟩ (by norm_num))
theorem R32771 : Reach 32771 := rs (se 1 (by rfl) ⟨24578, by rfl⟩) R49157
theorem R32787 : Reach 32787 := rs (se 1 (by rfl) ⟨24590, by rfl⟩) R49181
theorem R32803 : Reach 32803 := rs (se 1 (by rfl) ⟨24602, by rfl⟩) R49205
theorem R32819 : Reach 32819 := rs (se 1 (by rfl) ⟨24614, by rfl⟩) R49229
theorem R32835 : Reach 32835 := rs (se 1 (by rfl) ⟨24626, by rfl⟩) R49253
theorem R65603 : Reach 65603 := rs (se 1 (by rfl) ⟨49202, by rfl⟩) R98405
theorem R32851 : Reach 32851 := rs (se 1 (by rfl) ⟨24638, by rfl⟩) R49277
theorem R32867 : Reach 32867 := rs (se 1 (by rfl) ⟨24650, by rfl⟩) R49301
theorem R32883 : Reach 32883 := rs (se 1 (by rfl) ⟨24662, by rfl⟩) R49325
theorem R32899 : Reach 32899 := rs (se 1 (by rfl) ⟨24674, by rfl⟩) R49349
theorem R32915 : Reach 32915 := rs (se 1 (by rfl) ⟨24686, by rfl⟩) R49373
theorem R32931 : Reach 32931 := rs (se 1 (by rfl) ⟨24698, by rfl⟩) R49397
theorem R32947 : Reach 32947 := rs (se 1 (by rfl) ⟨24710, by rfl⟩) R49421
theorem R32963 : Reach 32963 := rs (se 1 (by rfl) ⟨24722, by rfl⟩) R49445
theorem R295109 : Reach 295109 := rs (se 4 (by rfl) ⟨27666, by rfl⟩) R55333
theorem R32979 : Reach 32979 := rs (se 1 (by rfl) ⟨24734, by rfl⟩) R49469
theorem R32995 : Reach 32995 := rs (se 1 (by rfl) ⟨24746, by rfl⟩) R49493
theorem R33011 : Reach 33011 := rs (se 1 (by rfl) ⟨24758, by rfl⟩) R49517
theorem R33027 : Reach 33027 := rs (se 1 (by rfl) ⟨24770, by rfl⟩) R49541
theorem R131341 : Reach 131341 := rs (se 3 (by rfl) ⟨24626, by rfl⟩) R49253
theorem R33043 : Reach 33043 := rs (se 1 (by rfl) ⟨24782, by rfl⟩) R49565
theorem R33059 : Reach 33059 := rs (se 1 (by rfl) ⟨24794, by rfl⟩) R49589
theorem R33075 : Reach 33075 := rs (se 1 (by rfl) ⟨24806, by rfl⟩) R49613
theorem R33091 : Reach 33091 := rs (se 1 (by rfl) ⟨24818, by rfl⟩) R49637
theorem R33107 : Reach 33107 := rs (se 1 (by rfl) ⟨24830, by rfl⟩) R49661
theorem R33123 : Reach 33123 := rs (se 1 (by rfl) ⟨24842, by rfl⟩) R49685
theorem R33139 : Reach 33139 := rs (se 1 (by rfl) ⟨24854, by rfl⟩) R49709
theorem R33155 : Reach 33155 := rs (se 1 (by rfl) ⟨24866, by rfl⟩) R49733
theorem R33171 : Reach 33171 := rs (se 1 (by rfl) ⟨24878, by rfl⟩) R49757
theorem R98723 : Reach 98723 := rs (se 1 (by rfl) ⟨74042, by rfl⟩) R148085
theorem R33187 : Reach 33187 := rs (se 1 (by rfl) ⟨24890, by rfl⟩) R49781
theorem R33203 : Reach 33203 := rs (se 1 (by rfl) ⟨24902, by rfl⟩) R49805
theorem R33219 : Reach 33219 := rs (se 1 (by rfl) ⟨24914, by rfl⟩) R49829
theorem R33235 : Reach 33235 := rs (se 1 (by rfl) ⟨24926, by rfl⟩) R49853
theorem R33251 : Reach 33251 := rs (se 1 (by rfl) ⟨24938, by rfl⟩) R49877
theorem R33267 : Reach 33267 := rs (se 1 (by rfl) ⟨24950, by rfl⟩) R49901
theorem R33283 : Reach 33283 := rs (se 1 (by rfl) ⟨24962, by rfl⟩) R49925
theorem R33299 : Reach 33299 := rs (se 1 (by rfl) ⟨24974, by rfl⟩) R49949
theorem R33315 : Reach 33315 := rs (se 1 (by rfl) ⟨24986, by rfl⟩) R49973
theorem R33331 : Reach 33331 := rs (se 1 (by rfl) ⟨24998, by rfl⟩) R49997
theorem R33347 : Reach 33347 := rs (se 1 (by rfl) ⟨25010, by rfl⟩) R50021
theorem R164429 : Reach 164429 := rs (se 3 (by rfl) ⟨30830, by rfl⟩) R61661
theorem R33363 : Reach 33363 := rs (se 1 (by rfl) ⟨25022, by rfl⟩) R50045
theorem R33379 : Reach 33379 := rs (se 1 (by rfl) ⟨25034, by rfl⟩) R50069
theorem R33395 : Reach 33395 := rs (se 1 (by rfl) ⟨25046, by rfl⟩) R50093
theorem R33411 : Reach 33411 := rs (se 1 (by rfl) ⟨25058, by rfl⟩) R50117
theorem R33427 : Reach 33427 := rs (se 1 (by rfl) ⟨25070, by rfl⟩) R50141
theorem R33443 : Reach 33443 := rs (se 1 (by rfl) ⟨25082, by rfl⟩) R50165
theorem R33459 : Reach 33459 := rs (se 1 (by rfl) ⟨25094, by rfl⟩) R50189
theorem R33475 : Reach 33475 := rs (se 1 (by rfl) ⟨25106, by rfl⟩) R50213
theorem R33491 : Reach 33491 := rs (se 1 (by rfl) ⟨25118, by rfl⟩) R50237
theorem R33507 : Reach 33507 := rs (se 1 (by rfl) ⟨25130, by rfl⟩) R50261
theorem R99053 : Reach 99053 := rs (se 3 (by rfl) ⟨18572, by rfl⟩) R37145
theorem R33523 : Reach 33523 := rs (se 1 (by rfl) ⟨25142, by rfl⟩) R50285
theorem R33539 : Reach 33539 := rs (se 1 (by rfl) ⟨25154, by rfl⟩) R50309
theorem R262925 : Reach 262925 := rs (se 3 (by rfl) ⟨49298, by rfl⟩) R98597
theorem R33555 : Reach 33555 := rs (se 1 (by rfl) ⟨25166, by rfl⟩) R50333
theorem R33571 : Reach 33571 := rs (se 1 (by rfl) ⟨25178, by rfl⟩) R50357
theorem R33587 : Reach 33587 := rs (se 1 (by rfl) ⟨25190, by rfl⟩) R50381
theorem R33603 : Reach 33603 := rs (se 1 (by rfl) ⟨25202, by rfl⟩) R50405
theorem R33619 : Reach 33619 := rs (se 1 (by rfl) ⟨25214, by rfl⟩) R50429
theorem R33635 : Reach 33635 := rs (se 1 (by rfl) ⟨25226, by rfl⟩) R50453
theorem R33651 : Reach 33651 := rs (se 1 (by rfl) ⟨25238, by rfl⟩) R50477
theorem R33667 : Reach 33667 := rs (se 1 (by rfl) ⟨25250, by rfl⟩) R50501
theorem R33683 : Reach 33683 := rs (se 1 (by rfl) ⟨25262, by rfl⟩) R50525
theorem R33699 : Reach 33699 := rs (se 1 (by rfl) ⟨25274, by rfl⟩) R50549
theorem R99235 : Reach 99235 := rs (se 1 (by rfl) ⟨74426, by rfl⟩) R148853
theorem R33715 : Reach 33715 := rs (se 1 (by rfl) ⟨25286, by rfl⟩) R50573
theorem R33731 : Reach 33731 := rs (se 1 (by rfl) ⟨25298, by rfl⟩) R50597
theorem R99281 : Reach 99281 := rs (se 2 (by rfl) ⟨37230, by rfl⟩) R74461
theorem R33747 : Reach 33747 := rs (se 1 (by rfl) ⟨25310, by rfl⟩) R50621
theorem R33763 : Reach 33763 := rs (se 1 (by rfl) ⟨25322, by rfl⟩) R50645
theorem R33779 : Reach 33779 := rs (se 1 (by rfl) ⟨25334, by rfl⟩) R50669
theorem R33795 : Reach 33795 := rs (se 1 (by rfl) ⟨25346, by rfl⟩) R50693
theorem R33811 : Reach 33811 := rs (se 1 (by rfl) ⟨25358, by rfl⟩) R50717
theorem R33827 : Reach 33827 := rs (se 1 (by rfl) ⟨25370, by rfl⟩) R50741
theorem R132131 : Reach 132131 := rs (se 1 (by rfl) ⟨99098, by rfl⟩) R198197
theorem R33843 : Reach 33843 := rs (se 1 (by rfl) ⟨25382, by rfl⟩) R50765
theorem R33859 : Reach 33859 := rs (se 1 (by rfl) ⟨25394, by rfl⟩) R50789
theorem R33875 : Reach 33875 := rs (se 1 (by rfl) ⟨25406, by rfl⟩) R50813
theorem R33891 : Reach 33891 := rs (se 1 (by rfl) ⟨25418, by rfl⟩) R50837
theorem R33907 : Reach 33907 := rs (se 1 (by rfl) ⟨25430, by rfl⟩) R50861
theorem R33923 : Reach 33923 := rs (se 1 (by rfl) ⟨25442, by rfl⟩) R50885
theorem R33939 : Reach 33939 := rs (se 1 (by rfl) ⟨25454, by rfl⟩) R50909
theorem R33955 : Reach 33955 := rs (se 1 (by rfl) ⟨25466, by rfl⟩) R50933
theorem R33971 : Reach 33971 := rs (se 1 (by rfl) ⟨25478, by rfl⟩) R50957
theorem R66755 : Reach 66755 := rs (se 1 (by rfl) ⟨50066, by rfl⟩) R100133
theorem R33987 : Reach 33987 := rs (se 1 (by rfl) ⟨25490, by rfl⟩) R50981
theorem R34003 : Reach 34003 := rs (se 1 (by rfl) ⟨25502, by rfl⟩) R51005
theorem R34019 : Reach 34019 := rs (se 1 (by rfl) ⟨25514, by rfl⟩) R51029
theorem R34035 : Reach 34035 := rs (se 1 (by rfl) ⟨25526, by rfl⟩) R51053
theorem R34051 : Reach 34051 := rs (se 1 (by rfl) ⟨25538, by rfl⟩) R51077
theorem R34067 : Reach 34067 := rs (se 1 (by rfl) ⟨25550, by rfl⟩) R51101
theorem R34083 : Reach 34083 := rs (se 1 (by rfl) ⟨25562, by rfl⟩) R51125
theorem R197923 : Reach 197923 := rs (se 1 (by rfl) ⟨148442, by rfl⟩) R296885
theorem R34099 : Reach 34099 := rs (se 1 (by rfl) ⟨25574, by rfl⟩) R51149
theorem R34115 : Reach 34115 := rs (se 1 (by rfl) ⟨25586, by rfl⟩) R51173
theorem R34131 : Reach 34131 := rs (se 1 (by rfl) ⟨25598, by rfl⟩) R51197
theorem R34147 : Reach 34147 := rs (se 1 (by rfl) ⟨25610, by rfl⟩) R51221
theorem R34163 : Reach 34163 := rs (se 1 (by rfl) ⟨25622, by rfl⟩) R51245
theorem R34179 : Reach 34179 := rs (se 1 (by rfl) ⟨25634, by rfl⟩) R51269
theorem R34195 : Reach 34195 := rs (se 1 (by rfl) ⟨25646, by rfl⟩) R51293
theorem R34211 : Reach 34211 := rs (se 1 (by rfl) ⟨25658, by rfl⟩) R51317
theorem R34227 : Reach 34227 := rs (se 1 (by rfl) ⟨25670, by rfl⟩) R51341
theorem R34243 : Reach 34243 := rs (se 1 (by rfl) ⟨25682, by rfl⟩) R51365
theorem R34259 : Reach 34259 := rs (se 1 (by rfl) ⟨25694, by rfl⟩) R51389
theorem R34275 : Reach 34275 := rs (se 1 (by rfl) ⟨25706, by rfl⟩) R51413
theorem R165347 : Reach 165347 := rs (se 1 (by rfl) ⟨124010, by rfl⟩) R248021
theorem R34291 : Reach 34291 := rs (se 1 (by rfl) ⟨25718, by rfl⟩) R51437
theorem R34307 : Reach 34307 := rs (se 1 (by rfl) ⟨25730, by rfl⟩) R51461
theorem R34323 : Reach 34323 := rs (se 1 (by rfl) ⟨25742, by rfl⟩) R51485
theorem R34339 : Reach 34339 := rs (se 1 (by rfl) ⟨25754, by rfl⟩) R51509
theorem R34355 : Reach 34355 := rs (se 1 (by rfl) ⟨25766, by rfl⟩) R51533
theorem R34371 : Reach 34371 := rs (se 1 (by rfl) ⟨25778, by rfl⟩) R51557
theorem R34387 : Reach 34387 := rs (se 1 (by rfl) ⟨25790, by rfl⟩) R51581
theorem R231011 : Reach 231011 := rs (se 1 (by rfl) ⟨173258, by rfl⟩) R346517
theorem R34403 : Reach 34403 := rs (se 1 (by rfl) ⟨25802, by rfl⟩) R51605
theorem R34419 : Reach 34419 := rs (se 1 (by rfl) ⟨25814, by rfl⟩) R51629
theorem R34435 : Reach 34435 := rs (se 1 (by rfl) ⟨25826, by rfl⟩) R51653
theorem R34451 : Reach 34451 := rs (se 1 (by rfl) ⟨25838, by rfl⟩) R51677
theorem R34467 : Reach 34467 := rs (se 1 (by rfl) ⟨25850, by rfl⟩) R51701
theorem R132785 : Reach 132785 := rs (se 2 (by rfl) ⟨49794, by rfl⟩) R99589
theorem R34483 : Reach 34483 := rs (se 1 (by rfl) ⟨25862, by rfl⟩) R51725
theorem R34499 : Reach 34499 := rs (se 1 (by rfl) ⟨25874, by rfl⟩) R51749
theorem R34515 : Reach 34515 := rs (se 1 (by rfl) ⟨25886, by rfl⟩) R51773
theorem R34531 : Reach 34531 := rs (se 1 (by rfl) ⟨25898, by rfl⟩) R51797
theorem R34547 : Reach 34547 := rs (se 1 (by rfl) ⟨25910, by rfl⟩) R51821
theorem R34563 : Reach 34563 := rs (se 1 (by rfl) ⟨25922, by rfl⟩) R51845
theorem R34579 : Reach 34579 := rs (se 1 (by rfl) ⟨25934, by rfl⟩) R51869
theorem R34595 : Reach 34595 := rs (se 1 (by rfl) ⟨25946, by rfl⟩) R51893
theorem R198449 : Reach 198449 := rs (se 2 (by rfl) ⟨74418, by rfl⟩) R148837
theorem R34611 : Reach 34611 := rs (se 1 (by rfl) ⟨25958, by rfl⟩) R51917
theorem R34627 : Reach 34627 := rs (se 1 (by rfl) ⟨25970, by rfl⟩) R51941
theorem R34643 : Reach 34643 := rs (se 1 (by rfl) ⟨25982, by rfl⟩) R51965
theorem R34659 : Reach 34659 := rs (se 1 (by rfl) ⟨25994, by rfl⟩) R51989
theorem R132977 : Reach 132977 := rs (se 2 (by rfl) ⟨49866, by rfl⟩) R99733
theorem R34675 : Reach 34675 := rs (se 1 (by rfl) ⟨26006, by rfl⟩) R52013
theorem R34691 : Reach 34691 := rs (se 1 (by rfl) ⟨26018, by rfl⟩) R52037
theorem R34707 : Reach 34707 := rs (se 1 (by rfl) ⟨26030, by rfl⟩) R52061
theorem R34723 : Reach 34723 := rs (se 1 (by rfl) ⟨26042, by rfl⟩) R52085
theorem R34739 : Reach 34739 := rs (se 1 (by rfl) ⟨26054, by rfl⟩) R52109
theorem R34755 : Reach 34755 := rs (se 1 (by rfl) ⟨26066, by rfl⟩) R52133
theorem R34771 : Reach 34771 := rs (se 1 (by rfl) ⟨26078, by rfl⟩) R52157
theorem R34787 : Reach 34787 := rs (se 1 (by rfl) ⟨26090, by rfl⟩) R52181
theorem R34803 : Reach 34803 := rs (se 1 (by rfl) ⟨26102, by rfl⟩) R52205
theorem R34819 : Reach 34819 := rs (se 1 (by rfl) ⟨26114, by rfl⟩) R52229
theorem R34835 : Reach 34835 := rs (se 1 (by rfl) ⟨26126, by rfl⟩) R52253
theorem R34851 : Reach 34851 := rs (se 1 (by rfl) ⟨26138, by rfl⟩) R52277
theorem R34867 : Reach 34867 := rs (se 1 (by rfl) ⟨26150, by rfl⟩) R52301
theorem R34883 : Reach 34883 := rs (se 1 (by rfl) ⟨26162, by rfl⟩) R52325
theorem R34899 : Reach 34899 := rs (se 1 (by rfl) ⟨26174, by rfl⟩) R52349
theorem R34915 : Reach 34915 := rs (se 1 (by rfl) ⟨26186, by rfl⟩) R52373
theorem R34931 : Reach 34931 := rs (se 1 (by rfl) ⟨26198, by rfl⟩) R52397
theorem R34947 : Reach 34947 := rs (se 1 (by rfl) ⟨26210, by rfl⟩) R52421
theorem R67729 : Reach 67729 := rs (se 2 (by rfl) ⟨25398, by rfl⟩) R50797
theorem R34963 : Reach 34963 := rs (se 1 (by rfl) ⟨26222, by rfl⟩) R52445
theorem R34979 : Reach 34979 := rs (se 1 (by rfl) ⟨26234, by rfl⟩) R52469
theorem R34995 : Reach 34995 := rs (se 1 (by rfl) ⟨26246, by rfl⟩) R52493
theorem R35011 : Reach 35011 := rs (se 1 (by rfl) ⟨26258, by rfl⟩) R52517
theorem R35027 : Reach 35027 := rs (se 1 (by rfl) ⟨26270, by rfl⟩) R52541
theorem R35043 : Reach 35043 := rs (se 1 (by rfl) ⟨26282, by rfl⟩) R52565
theorem R35059 : Reach 35059 := rs (se 1 (by rfl) ⟨26294, by rfl⟩) R52589
theorem R35075 : Reach 35075 := rs (se 1 (by rfl) ⟨26306, by rfl⟩) R52613
theorem R35091 : Reach 35091 := rs (se 1 (by rfl) ⟨26318, by rfl⟩) R52637
theorem R35107 : Reach 35107 := rs (se 1 (by rfl) ⟨26330, by rfl⟩) R52661
theorem R35203 : Reach 35203 := rs (se 1 (by rfl) ⟨26402, by rfl⟩) R52805
theorem R166349 : Reach 166349 := rs (se 3 (by rfl) ⟨31190, by rfl⟩) R62381
theorem R35347 : Reach 35347 := rs (se 1 (by rfl) ⟨26510, by rfl⟩) R53021
theorem R68131 : Reach 68131 := rs (se 1 (by rfl) ⟨51098, by rfl⟩) R102197
theorem R68177 : Reach 68177 := rs (se 2 (by rfl) ⟨25566, by rfl⟩) R51133
theorem R756337 : Reach 756337 := rs (se 2 (by rfl) ⟨283626, by rfl⟩) R567253
theorem R101009 : Reach 101009 := rs (se 2 (by rfl) ⟨37878, by rfl⟩) R75757
theorem R35491 : Reach 35491 := rs (se 1 (by rfl) ⟨26618, by rfl⟩) R53237
theorem R101155 : Reach 101155 := rs (se 1 (by rfl) ⟨75866, by rfl⟩) R151733
theorem R166691 : Reach 166691 := rs (se 1 (by rfl) ⟨125018, by rfl⟩) R250037
theorem R35635 : Reach 35635 := rs (se 1 (by rfl) ⟨26726, by rfl⟩) R53453
theorem R35779 : Reach 35779 := rs (se 1 (by rfl) ⟨26834, by rfl⟩) R53669
theorem R199685 : Reach 199685 := rs (se 4 (by rfl) ⟨18720, by rfl⟩) R37441
theorem R35923 : Reach 35923 := rs (se 1 (by rfl) ⟨26942, by rfl⟩) R53885
theorem R199907 : Reach 199907 := rs (se 1 (by rfl) ⟨149930, by rfl⟩) R299861
theorem R36067 : Reach 36067 := rs (se 1 (by rfl) ⟨27050, by rfl⟩) R54101
theorem R101645 : Reach 101645 := rs (se 3 (by rfl) ⟨19058, by rfl⟩) R38117
theorem R36163 : Reach 36163 := rs (se 1 (by rfl) ⟨27122, by rfl⟩) R54245
theorem R36211 : Reach 36211 := rs (se 1 (by rfl) ⟨27158, by rfl⟩) R54317
theorem R167345 : Reach 167345 := rs (se 2 (by rfl) ⟨62754, by rfl⟩) R125509
theorem R36355 : Reach 36355 := rs (se 1 (by rfl) ⟨27266, by rfl⟩) R54533
theorem R265841 : Reach 265841 := rs (se 2 (by rfl) ⟨99690, by rfl⟩) R199381
theorem R36499 : Reach 36499 := rs (se 1 (by rfl) ⟨27374, by rfl⟩) R54749
theorem R36643 : Reach 36643 := rs (se 1 (by rfl) ⟨27482, by rfl⟩) R54965
theorem R36787 : Reach 36787 := rs (se 1 (by rfl) ⟨27590, by rfl⟩) R55181
theorem R167921 : Reach 167921 := rs (se 2 (by rfl) ⟨62970, by rfl⟩) R125941
theorem R69635 : Reach 69635 := rs (se 1 (by rfl) ⟨52226, by rfl⟩) R104453
theorem R36931 : Reach 36931 := rs (se 1 (by rfl) ⟨27698, by rfl⟩) R55397
theorem R37075 : Reach 37075 := rs (se 1 (by rfl) ⟨27806, by rfl⟩) R55613
theorem R168227 : Reach 168227 := rs (se 1 (by rfl) ⟨126170, by rfl⟩) R252341
theorem R758069 : Reach 758069 := rs (se 5 (by rfl) ⟨35534, by rfl⟩) R71069
theorem R37219 : Reach 37219 := rs (se 1 (by rfl) ⟨27914, by rfl⟩) R55829
theorem R70019 : Reach 70019 := rs (se 1 (by rfl) ⟨52514, by rfl⟩) R105029
theorem R135587 : Reach 135587 := rs (se 1 (by rfl) ⟨101690, by rfl⟩) R203381
theorem R37363 : Reach 37363 := rs (se 1 (by rfl) ⟨28022, by rfl⟩) R56045
theorem R135715 : Reach 135715 := rs (se 1 (by rfl) ⟨101786, by rfl⟩) R203573
theorem R37427 : Reach 37427 := rs (se 1 (by rfl) ⟨28070, by rfl⟩) R56141
theorem R37507 : Reach 37507 := rs (se 1 (by rfl) ⟨28130, by rfl⟩) R56261
theorem R70289 : Reach 70289 := rs (se 2 (by rfl) ⟨26358, by rfl⟩) R52717
theorem R70307 : Reach 70307 := rs (se 1 (by rfl) ⟨52730, by rfl⟩) R105461
theorem R37651 : Reach 37651 := rs (se 1 (by rfl) ⟨28238, by rfl⟩) R56477
theorem R168803 : Reach 168803 := rs (se 1 (by rfl) ⟨126602, by rfl⟩) R253205
theorem R37795 : Reach 37795 := rs (se 1 (by rfl) ⟨28346, by rfl⟩) R56693
theorem R70577 : Reach 70577 := rs (se 2 (by rfl) ⟨26466, by rfl⟩) R52933
theorem R201649 : Reach 201649 := rs (se 2 (by rfl) ⟨75618, by rfl⟩) R151237
theorem R70595 : Reach 70595 := rs (se 1 (by rfl) ⟨52946, by rfl⟩) R105893
theorem R103427 : Reach 103427 := rs (se 1 (by rfl) ⟨77570, by rfl⟩) R155141
theorem R168965 : Reach 168965 := rs (se 4 (by rfl) ⟨15840, by rfl⟩) R31681
theorem R37939 : Reach 37939 := rs (se 1 (by rfl) ⟨28454, by rfl⟩) R56909
theorem R38083 : Reach 38083 := rs (se 1 (by rfl) ⟨28562, by rfl⟩) R57125
theorem R70865 : Reach 70865 := rs (se 2 (by rfl) ⟨26574, by rfl⟩) R53149
theorem R70883 : Reach 70883 := rs (se 1 (by rfl) ⟨53162, by rfl⟩) R106325
theorem R38227 : Reach 38227 := rs (se 1 (by rfl) ⟨28670, by rfl⟩) R57341
theorem R38371 : Reach 38371 := rs (se 1 (by rfl) ⟨28778, by rfl⟩) R57557
theorem R71153 : Reach 71153 := rs (se 2 (by rfl) ⟨26682, by rfl⟩) R53365
theorem R71171 : Reach 71171 := rs (se 1 (by rfl) ⟨53378, by rfl⟩) R106757
theorem R38515 : Reach 38515 := rs (se 1 (by rfl) ⟨28886, by rfl⟩) R57773
theorem R169613 : Reach 169613 := rs (se 3 (by rfl) ⟨31802, by rfl⟩) R63605
theorem R38659 : Reach 38659 := rs (se 1 (by rfl) ⟨28994, by rfl⟩) R57989
theorem R71441 : Reach 71441 := rs (se 2 (by rfl) ⟨26790, by rfl⟩) R53581
theorem R71459 : Reach 71459 := rs (se 1 (by rfl) ⟨53594, by rfl⟩) R107189
theorem R38803 : Reach 38803 := rs (se 1 (by rfl) ⟨29102, by rfl⟩) R58205
theorem R38947 : Reach 38947 := rs (se 1 (by rfl) ⟨29210, by rfl⟩) R58421
theorem R71729 : Reach 71729 := rs (se 2 (by rfl) ⟨26898, by rfl⟩) R53797
theorem R71747 : Reach 71747 := rs (se 1 (by rfl) ⟨53810, by rfl⟩) R107621
theorem R71761 : Reach 71761 := rs (se 2 (by rfl) ⟨26910, by rfl⟩) R53821
theorem R71779 : Reach 71779 := rs (se 1 (by rfl) ⟨53834, by rfl⟩) R107669
theorem R39091 : Reach 39091 := rs (se 1 (by rfl) ⟨29318, by rfl⟩) R58637
theorem R104771 : Reach 104771 := rs (se 1 (by rfl) ⟨78578, by rfl⟩) R157157
theorem R39235 : Reach 39235 := rs (se 1 (by rfl) ⟨29426, by rfl⟩) R58853
theorem R72017 : Reach 72017 := rs (se 2 (by rfl) ⟨27006, by rfl⟩) R54013
theorem R39251 : Reach 39251 := rs (se 1 (by rfl) ⟨29438, by rfl⟩) R58877
theorem R72035 : Reach 72035 := rs (se 1 (by rfl) ⟨54026, by rfl⟩) R108053
theorem R170381 : Reach 170381 := rs (se 3 (by rfl) ⟨31946, by rfl⟩) R63893
theorem R39379 : Reach 39379 := rs (se 1 (by rfl) ⟨29534, by rfl⟩) R59069
theorem R137713 : Reach 137713 := rs (se 2 (by rfl) ⟨51642, by rfl⟩) R103285
theorem R39443 : Reach 39443 := rs (se 1 (by rfl) ⟨29582, by rfl⟩) R59165
theorem R39523 : Reach 39523 := rs (se 1 (by rfl) ⟨29642, by rfl⟩) R59285
theorem R72305 : Reach 72305 := rs (se 2 (by rfl) ⟨27114, by rfl⟩) R54229
theorem R72323 : Reach 72323 := rs (se 1 (by rfl) ⟨54242, by rfl⟩) R108485
theorem R105137 : Reach 105137 := rs (se 2 (by rfl) ⟨39426, by rfl⟩) R78853
theorem R39619 : Reach 39619 := rs (se 1 (by rfl) ⟨29714, by rfl⟩) R59429
theorem R137933 : Reach 137933 := rs (se 3 (by rfl) ⟨25862, by rfl⟩) R51725
theorem R203597 : Reach 203597 := rs (se 3 (by rfl) ⟨38174, by rfl⟩) R76349
theorem R498545 : Reach 498545 := rs (se 2 (by rfl) ⟨186954, by rfl⟩) R373909
theorem R236429 : Reach 236429 := rs (se 3 (by rfl) ⟨44330, by rfl⟩) R88661
theorem R72593 : Reach 72593 := rs (se 2 (by rfl) ⟨27222, by rfl⟩) R54445
theorem R72611 : Reach 72611 := rs (se 1 (by rfl) ⟨54458, by rfl⟩) R108917
theorem R72881 : Reach 72881 := rs (se 2 (by rfl) ⟨27330, by rfl⟩) R54661
theorem R40115 : Reach 40115 := rs (se 1 (by rfl) ⟨30086, by rfl⟩) R60173
theorem R72899 : Reach 72899 := rs (se 1 (by rfl) ⟨54674, by rfl⟩) R109349
theorem R105677 : Reach 105677 := rs (se 3 (by rfl) ⟨19814, by rfl⟩) R39629
theorem R105731 : Reach 105731 := rs (se 1 (by rfl) ⟨79298, by rfl⟩) R158597
theorem R335285 : Reach 335285 := rs (se 5 (by rfl) ⟨15716, by rfl⟩) R31433
theorem R73169 : Reach 73169 := rs (se 2 (by rfl) ⟨27438, by rfl⟩) R54877
theorem R73187 : Reach 73187 := rs (se 1 (by rfl) ⟨54890, by rfl⟩) R109781
theorem R106001 : Reach 106001 := rs (se 2 (by rfl) ⟨39750, by rfl⟩) R79501
theorem R335501 : Reach 335501 := rs (se 3 (by rfl) ⟨62906, by rfl⟩) R125813
theorem R40595 : Reach 40595 := rs (se 1 (by rfl) ⟨30446, by rfl⟩) R60893
theorem R73457 : Reach 73457 := rs (se 2 (by rfl) ⟨27546, by rfl⟩) R55093
theorem R73475 : Reach 73475 := rs (se 1 (by rfl) ⟨55106, by rfl⟩) R110213
theorem R40819 : Reach 40819 := rs (se 1 (by rfl) ⟨30614, by rfl⟩) R61229
theorem R40915 : Reach 40915 := rs (se 1 (by rfl) ⟨30686, by rfl⟩) R61373
theorem R73745 : Reach 73745 := rs (se 2 (by rfl) ⟨27654, by rfl⟩) R55309
theorem R73763 : Reach 73763 := rs (se 1 (by rfl) ⟨55322, by rfl⟩) R110645
theorem R106541 : Reach 106541 := rs (se 3 (by rfl) ⟨19976, by rfl⟩) R39953
theorem R106595 : Reach 106595 := rs (se 1 (by rfl) ⟨79946, by rfl⟩) R159893
theorem R74033 : Reach 74033 := rs (se 2 (by rfl) ⟨27762, by rfl⟩) R55525
theorem R74051 : Reach 74051 := rs (se 1 (by rfl) ⟨55538, by rfl⟩) R111077
theorem R106865 : Reach 106865 := rs (se 2 (by rfl) ⟨40074, by rfl⟩) R80149
theorem R41411 : Reach 41411 := rs (se 1 (by rfl) ⟨31058, by rfl⟩) R62117
theorem R401861 : Reach 401861 := rs (se 4 (by rfl) ⟨37674, by rfl⟩) R75349
theorem R172529 : Reach 172529 := rs (se 2 (by rfl) ⟨64698, by rfl⟩) R129397
theorem R74321 : Reach 74321 := rs (se 2 (by rfl) ⟨27870, by rfl⟩) R55741
theorem R74339 : Reach 74339 := rs (se 1 (by rfl) ⟨55754, by rfl⟩) R111509
theorem R303857 : Reach 303857 := rs (se 2 (by rfl) ⟨113946, by rfl⟩) R227893
theorem R74513 : Reach 74513 := rs (se 2 (by rfl) ⟨27942, by rfl⟩) R55885
theorem R74609 : Reach 74609 := rs (se 2 (by rfl) ⟨27978, by rfl⟩) R55957
theorem R369521 : Reach 369521 := rs (se 2 (by rfl) ⟨138570, by rfl⟩) R277141
theorem R74627 : Reach 74627 := rs (se 1 (by rfl) ⟨55970, by rfl⟩) R111941
theorem R107405 : Reach 107405 := rs (se 3 (by rfl) ⟨20138, by rfl⟩) R40277
theorem R107459 : Reach 107459 := rs (se 1 (by rfl) ⟨80594, by rfl⟩) R161189
theorem R41953 : Reach 41953 := rs (se 2 (by rfl) ⟨15732, by rfl⟩) R31465
theorem R42049 : Reach 42049 := rs (se 2 (by rfl) ⟨15768, by rfl⟩) R31537
theorem R42115 : Reach 42115 := rs (se 1 (by rfl) ⟨31586, by rfl⟩) R63173
theorem R74897 : Reach 74897 := rs (se 2 (by rfl) ⟨28086, by rfl⟩) R56173
theorem R74915 : Reach 74915 := rs (se 1 (by rfl) ⟨56186, by rfl⟩) R112373
theorem R599237 : Reach 599237 := rs (se 4 (by rfl) ⟨56178, by rfl⟩) R112357
theorem R107729 : Reach 107729 := rs (se 2 (by rfl) ⟨40398, by rfl⟩) R80797
theorem R42211 : Reach 42211 := rs (se 1 (by rfl) ⟨31658, by rfl⟩) R63317
theorem R75185 : Reach 75185 := rs (se 2 (by rfl) ⟨28194, by rfl⟩) R56389
theorem R75203 : Reach 75203 := rs (se 1 (by rfl) ⟨56402, by rfl⟩) R112805
theorem R140771 : Reach 140771 := rs (se 1 (by rfl) ⟨105578, by rfl⟩) R211157
theorem R173573 : Reach 173573 := rs (se 4 (by rfl) ⟨16272, by rfl⟩) R32545
theorem R42545 : Reach 42545 := rs (se 2 (by rfl) ⟨15954, by rfl⟩) R31909
theorem R75473 : Reach 75473 := rs (se 2 (by rfl) ⟨28302, by rfl⟩) R56605
theorem R42707 : Reach 42707 := rs (se 1 (by rfl) ⟨32030, by rfl⟩) R64061
theorem R75491 : Reach 75491 := rs (se 1 (by rfl) ⟨56618, by rfl⟩) R113237
theorem R108269 : Reach 108269 := rs (se 3 (by rfl) ⟨20300, by rfl⟩) R40601
theorem R108323 : Reach 108323 := rs (se 1 (by rfl) ⟨81242, by rfl⟩) R162485
theorem R42817 : Reach 42817 := rs (se 2 (by rfl) ⟨16056, by rfl⟩) R32113
theorem R173987 : Reach 173987 := rs (se 1 (by rfl) ⟨130490, by rfl⟩) R260981
theorem R75761 : Reach 75761 := rs (se 2 (by rfl) ⟨28410, by rfl⟩) R56821
theorem R75779 : Reach 75779 := rs (se 1 (by rfl) ⟨56834, by rfl⟩) R113669
theorem R75811 : Reach 75811 := rs (se 1 (by rfl) ⟨56858, by rfl⟩) R113717
theorem R108593 : Reach 108593 := rs (se 2 (by rfl) ⟨40722, by rfl⟩) R81445
theorem R174149 : Reach 174149 := rs (se 4 (by rfl) ⟨16326, by rfl⟩) R32653
theorem R75907 : Reach 75907 := rs (se 1 (by rfl) ⟨56930, by rfl⟩) R113861
theorem R206981 : Reach 206981 := rs (se 4 (by rfl) ⟨19404, by rfl⟩) R38809
theorem R43249 : Reach 43249 := rs (se 2 (by rfl) ⟨16218, by rfl⟩) R32437
theorem R76049 : Reach 76049 := rs (se 2 (by rfl) ⟨28518, by rfl⟩) R57037
theorem R76067 : Reach 76067 := rs (se 1 (by rfl) ⟨57050, by rfl⟩) R114101
theorem R43345 : Reach 43345 := rs (se 2 (by rfl) ⟨16254, by rfl⟩) R32509
theorem R43411 : Reach 43411 := rs (se 1 (by rfl) ⟨32558, by rfl⟩) R65117
theorem R108973 : Reach 108973 := rs (se 3 (by rfl) ⟨20432, by rfl⟩) R40865
theorem R141745 : Reach 141745 := rs (se 2 (by rfl) ⟨53154, by rfl⟩) R106309
theorem R76259 : Reach 76259 := rs (se 1 (by rfl) ⟨57194, by rfl⟩) R114389
theorem R43507 : Reach 43507 := rs (se 1 (by rfl) ⟨32630, by rfl⟩) R65261
theorem R76337 : Reach 76337 := rs (se 2 (by rfl) ⟨28626, by rfl⟩) R57253
theorem R76355 : Reach 76355 := rs (se 1 (by rfl) ⟨57266, by rfl⟩) R114533
theorem R109133 : Reach 109133 := rs (se 3 (by rfl) ⟨20462, by rfl⟩) R40925
theorem R109187 : Reach 109187 := rs (se 1 (by rfl) ⟨81890, by rfl⟩) R163781
theorem R174797 : Reach 174797 := rs (se 3 (by rfl) ⟨32774, by rfl⟩) R65549
theorem R43841 : Reach 43841 := rs (se 2 (by rfl) ⟨16440, by rfl⟩) R32881
theorem R76625 : Reach 76625 := rs (se 2 (by rfl) ⟨28734, by rfl⟩) R57469
theorem R76643 : Reach 76643 := rs (se 1 (by rfl) ⟨57482, by rfl⟩) R114965
theorem R109421 : Reach 109421 := rs (se 3 (by rfl) ⟨20516, by rfl⟩) R41033
theorem R109457 : Reach 109457 := rs (se 2 (by rfl) ⟨41046, by rfl⟩) R82093
theorem R44003 : Reach 44003 := rs (se 1 (by rfl) ⟨33002, by rfl⟩) R66005
theorem R76913 : Reach 76913 := rs (se 2 (by rfl) ⟨28842, by rfl⟩) R57685
theorem R76931 : Reach 76931 := rs (se 1 (by rfl) ⟨57698, by rfl⟩) R115397
theorem R306317 : Reach 306317 := rs (se 3 (by rfl) ⟨57434, by rfl⟩) R114869
theorem R109745 : Reach 109745 := rs (se 2 (by rfl) ⟨41154, by rfl⟩) R82309
theorem R109795 : Reach 109795 := rs (se 1 (by rfl) ⟨82346, by rfl⟩) R164693
theorem R77041 : Reach 77041 := rs (se 2 (by rfl) ⟨28890, by rfl⟩) R57781
theorem R44401 : Reach 44401 := rs (se 2 (by rfl) ⟨16650, by rfl⟩) R33301
theorem R77201 : Reach 77201 := rs (se 2 (by rfl) ⟨28950, by rfl⟩) R57901
theorem R44435 : Reach 44435 := rs (se 1 (by rfl) ⟨33326, by rfl⟩) R66653
theorem R77219 : Reach 77219 := rs (se 1 (by rfl) ⟨57914, by rfl⟩) R115829
theorem R109997 : Reach 109997 := rs (se 3 (by rfl) ⟨20624, by rfl⟩) R41249
theorem R110051 : Reach 110051 := rs (se 1 (by rfl) ⟨82538, by rfl⟩) R165077
theorem R110083 : Reach 110083 := rs (se 1 (by rfl) ⟨82562, by rfl⟩) R165125
theorem R77489 : Reach 77489 := rs (se 2 (by rfl) ⟨29058, by rfl⟩) R58117
theorem R77507 : Reach 77507 := rs (se 1 (by rfl) ⟨58130, by rfl⟩) R116261
theorem R110321 : Reach 110321 := rs (se 2 (by rfl) ⟨41370, by rfl⟩) R82741
theorem R44993 : Reach 44993 := rs (se 2 (by rfl) ⟨16872, by rfl⟩) R33745
theorem R77777 : Reach 77777 := rs (se 2 (by rfl) ⟨29166, by rfl⟩) R58333
theorem R77795 : Reach 77795 := rs (se 1 (by rfl) ⟨58346, by rfl⟩) R116693
theorem R45073 : Reach 45073 := rs (se 2 (by rfl) ⟨16902, by rfl⟩) R33805
theorem R110641 : Reach 110641 := rs (se 2 (by rfl) ⟨41490, by rfl⟩) R82981
theorem R78065 : Reach 78065 := rs (se 2 (by rfl) ⟨29274, by rfl⟩) R58549
theorem R78083 : Reach 78083 := rs (se 1 (by rfl) ⟨58562, by rfl⟩) R117125
theorem R110861 : Reach 110861 := rs (se 3 (by rfl) ⟨20786, by rfl⟩) R41573
theorem R78353 : Reach 78353 := rs (se 2 (by rfl) ⟨29382, by rfl⟩) R58765
theorem R78371 : Reach 78371 := rs (se 1 (by rfl) ⟨58778, by rfl⟩) R117557
theorem R45859 : Reach 45859 := rs (se 1 (by rfl) ⟨34394, by rfl⟩) R68789
theorem R78641 : Reach 78641 := rs (se 2 (by rfl) ⟨29490, by rfl⟩) R58981
theorem R78659 : Reach 78659 := rs (se 1 (by rfl) ⟨58994, by rfl⟩) R117989
theorem R78833 : Reach 78833 := rs (se 2 (by rfl) ⟨29562, by rfl⟩) R59125
theorem R78929 : Reach 78929 := rs (se 2 (by rfl) ⟨29598, by rfl⟩) R59197
theorem R78947 : Reach 78947 := rs (se 1 (by rfl) ⟨59210, by rfl⟩) R118421
theorem R177265 : Reach 177265 := rs (se 2 (by rfl) ⟨66474, by rfl⟩) R132949
theorem R111779 : Reach 111779 := rs (se 1 (by rfl) ⟨83834, by rfl⟩) R167669
theorem R177329 : Reach 177329 := rs (se 2 (by rfl) ⟨66498, by rfl⟩) R132997
theorem R177349 : Reach 177349 := rs (se 4 (by rfl) ⟨16626, by rfl⟩) R33253
theorem R46337 : Reach 46337 := rs (se 2 (by rfl) ⟨17376, by rfl⟩) R34753
theorem R308549 : Reach 308549 := rs (se 4 (by rfl) ⟨28926, by rfl⟩) R57853
theorem R46451 : Reach 46451 := rs (se 1 (by rfl) ⟨34838, by rfl⟩) R69677
theorem R112049 : Reach 112049 := rs (se 2 (by rfl) ⟨42018, by rfl⟩) R84037
theorem R46531 : Reach 46531 := rs (se 1 (by rfl) ⟨34898, by rfl⟩) R69797
theorem R177713 : Reach 177713 := rs (se 2 (by rfl) ⟨66642, by rfl⟩) R133285
theorem R112205 : Reach 112205 := rs (se 3 (by rfl) ⟨21038, by rfl⟩) R42077
theorem R46673 : Reach 46673 := rs (se 2 (by rfl) ⟨17502, by rfl⟩) R35005
theorem R46691 : Reach 46691 := rs (se 1 (by rfl) ⟨35018, by rfl⟩) R70037
theorem R210545 : Reach 210545 := rs (se 2 (by rfl) ⟨78954, by rfl⟩) R157909
theorem R46721 : Reach 46721 := rs (se 2 (by rfl) ⟨17520, by rfl⟩) R35041
theorem R669325 : Reach 669325 := rs (se 3 (by rfl) ⟨125498, by rfl⟩) R250997
theorem R46739 : Reach 46739 := rs (se 1 (by rfl) ⟨35054, by rfl⟩) R70109
theorem R46769 : Reach 46769 := rs (se 2 (by rfl) ⟨17538, by rfl⟩) R35077
theorem R46787 : Reach 46787 := rs (se 1 (by rfl) ⟨35090, by rfl⟩) R70181
theorem R46817 : Reach 46817 := rs (se 2 (by rfl) ⟨17556, by rfl⟩) R35113
theorem R46835 : Reach 46835 := rs (se 1 (by rfl) ⟨35126, by rfl⟩) R70253
theorem R46865 : Reach 46865 := rs (se 2 (by rfl) ⟨17574, by rfl⟩) R35149
theorem R46883 : Reach 46883 := rs (se 1 (by rfl) ⟨35162, by rfl⟩) R70325
theorem R46913 : Reach 46913 := rs (se 2 (by rfl) ⟨17592, by rfl⟩) R35185
theorem R46931 : Reach 46931 := rs (se 1 (by rfl) ⟨35198, by rfl⟩) R70397
theorem R46961 : Reach 46961 := rs (se 2 (by rfl) ⟨17610, by rfl⟩) R35221
theorem R46979 : Reach 46979 := rs (se 1 (by rfl) ⟨35234, by rfl⟩) R70469
theorem R47009 : Reach 47009 := rs (se 2 (by rfl) ⟨17628, by rfl⟩) R35257
theorem R47027 : Reach 47027 := rs (se 1 (by rfl) ⟨35270, by rfl⟩) R70541
theorem R112589 : Reach 112589 := rs (se 3 (by rfl) ⟨21110, by rfl⟩) R42221
theorem R47057 : Reach 47057 := rs (se 2 (by rfl) ⟨17646, by rfl⟩) R35293
theorem R79825 : Reach 79825 := rs (se 2 (by rfl) ⟨29934, by rfl⟩) R59869
theorem R47075 : Reach 47075 := rs (se 1 (by rfl) ⟨35306, by rfl⟩) R70613
theorem R538595 : Reach 538595 := rs (se 1 (by rfl) ⟨403946, by rfl⟩) R807893
theorem R47089 : Reach 47089 := rs (se 2 (by rfl) ⟨17658, by rfl⟩) R35317
theorem R47105 : Reach 47105 := rs (se 2 (by rfl) ⟨17664, by rfl⟩) R35329
theorem R145421 : Reach 145421 := rs (se 3 (by rfl) ⟨27266, by rfl⟩) R54533
theorem R374797 : Reach 374797 := rs (se 3 (by rfl) ⟨70274, by rfl⟩) R140549
theorem R47123 : Reach 47123 := rs (se 1 (by rfl) ⟨35342, by rfl⟩) R70685
theorem R47153 : Reach 47153 := rs (se 2 (by rfl) ⟨17682, by rfl⟩) R35365
theorem R47171 : Reach 47171 := rs (se 1 (by rfl) ⟨35378, by rfl⟩) R70757
theorem R47201 : Reach 47201 := rs (se 2 (by rfl) ⟨17700, by rfl⟩) R35401
theorem R47219 : Reach 47219 := rs (se 1 (by rfl) ⟨35414, by rfl⟩) R70829
theorem R47249 : Reach 47249 := rs (se 2 (by rfl) ⟨17718, by rfl⟩) R35437
theorem R47267 : Reach 47267 := rs (se 1 (by rfl) ⟨35450, by rfl⟩) R70901
theorem R47297 : Reach 47297 := rs (se 2 (by rfl) ⟨17736, by rfl⟩) R35473
theorem R47315 : Reach 47315 := rs (se 1 (by rfl) ⟨35486, by rfl⟩) R70973
theorem R80099 : Reach 80099 := rs (se 1 (by rfl) ⟨60074, by rfl⟩) R120149
theorem R47345 : Reach 47345 := rs (se 2 (by rfl) ⟨17754, by rfl⟩) R35509
theorem R47363 : Reach 47363 := rs (se 1 (by rfl) ⟨35522, by rfl⟩) R71045
theorem R47393 : Reach 47393 := rs (se 2 (by rfl) ⟨17772, by rfl⟩) R35545
theorem R47411 : Reach 47411 := rs (se 1 (by rfl) ⟨35558, by rfl⟩) R71117
theorem R47441 : Reach 47441 := rs (se 2 (by rfl) ⟨17790, by rfl⟩) R35581
theorem R47459 : Reach 47459 := rs (se 1 (by rfl) ⟨35594, by rfl⟩) R71189
theorem R47489 : Reach 47489 := rs (se 2 (by rfl) ⟨17808, by rfl⟩) R35617
theorem R47507 : Reach 47507 := rs (se 1 (by rfl) ⟨35630, by rfl⟩) R71261
theorem R80291 : Reach 80291 := rs (se 1 (by rfl) ⟨60218, by rfl⟩) R120437
theorem R47537 : Reach 47537 := rs (se 2 (by rfl) ⟨17826, by rfl⟩) R35653
theorem R47555 : Reach 47555 := rs (se 1 (by rfl) ⟨35666, by rfl⟩) R71333
theorem R47585 : Reach 47585 := rs (se 2 (by rfl) ⟨17844, by rfl⟩) R35689
theorem R47603 : Reach 47603 := rs (se 1 (by rfl) ⟨35702, by rfl⟩) R71405
theorem R47633 : Reach 47633 := rs (se 2 (by rfl) ⟨17862, by rfl⟩) R35725
theorem R47651 : Reach 47651 := rs (se 1 (by rfl) ⟨35738, by rfl⟩) R71477
theorem R47681 : Reach 47681 := rs (se 2 (by rfl) ⟨17880, by rfl⟩) R35761
theorem R47699 : Reach 47699 := rs (se 1 (by rfl) ⟨35774, by rfl⟩) R71549
theorem R178787 : Reach 178787 := rs (se 1 (by rfl) ⟨134090, by rfl⟩) R268181
theorem R47729 : Reach 47729 := rs (se 2 (by rfl) ⟨17898, by rfl⟩) R35797
theorem R47747 : Reach 47747 := rs (se 1 (by rfl) ⟨35810, by rfl⟩) R71621
theorem R47777 : Reach 47777 := rs (se 2 (by rfl) ⟨17916, by rfl⟩) R35833
theorem R47795 : Reach 47795 := rs (se 1 (by rfl) ⟨35846, by rfl⟩) R71693
theorem R47825 : Reach 47825 := rs (se 2 (by rfl) ⟨17934, by rfl⟩) R35869
theorem R47843 : Reach 47843 := rs (se 1 (by rfl) ⟨35882, by rfl⟩) R71765
theorem R47873 : Reach 47873 := rs (se 2 (by rfl) ⟨17952, by rfl⟩) R35905
theorem R47891 : Reach 47891 := rs (se 1 (by rfl) ⟨35918, by rfl⟩) R71837
theorem R47921 : Reach 47921 := rs (se 2 (by rfl) ⟨17970, by rfl⟩) R35941
theorem R47939 : Reach 47939 := rs (se 1 (by rfl) ⟨35954, by rfl⟩) R71909
theorem R113485 : Reach 113485 := rs (se 3 (by rfl) ⟨21278, by rfl⟩) R42557
theorem R47969 : Reach 47969 := rs (se 2 (by rfl) ⟨17988, by rfl⟩) R35977
theorem R113507 : Reach 113507 := rs (se 1 (by rfl) ⟨85130, by rfl⟩) R170261
theorem R47987 : Reach 47987 := rs (se 1 (by rfl) ⟨35990, by rfl⟩) R71981
theorem R48017 : Reach 48017 := rs (se 2 (by rfl) ⟨18006, by rfl⟩) R36013
theorem R48035 : Reach 48035 := rs (se 1 (by rfl) ⟨36026, by rfl⟩) R72053
theorem R48065 : Reach 48065 := rs (se 2 (by rfl) ⟨18024, by rfl⟩) R36049
theorem R48083 : Reach 48083 := rs (se 1 (by rfl) ⟨36062, by rfl⟩) R72125
theorem R48113 : Reach 48113 := rs (se 2 (by rfl) ⟨18042, by rfl⟩) R36085
theorem R48131 : Reach 48131 := rs (se 1 (by rfl) ⟨36098, by rfl⟩) R72197
theorem R48161 : Reach 48161 := rs (se 2 (by rfl) ⟨18060, by rfl⟩) R36121
theorem R212003 : Reach 212003 := rs (se 1 (by rfl) ⟨159002, by rfl⟩) R318005
theorem R48179 : Reach 48179 := rs (se 1 (by rfl) ⟨36134, by rfl⟩) R72269
theorem R80963 : Reach 80963 := rs (se 1 (by rfl) ⟨60722, by rfl⟩) R121445
theorem R48209 : Reach 48209 := rs (se 2 (by rfl) ⟨18078, by rfl⟩) R36157
theorem R48227 : Reach 48227 := rs (se 1 (by rfl) ⟨36170, by rfl⟩) R72341
theorem R113777 : Reach 113777 := rs (se 2 (by rfl) ⟨42666, by rfl⟩) R85333
theorem R48257 : Reach 48257 := rs (se 2 (by rfl) ⟨18096, by rfl⟩) R36193
theorem R48275 : Reach 48275 := rs (se 1 (by rfl) ⟨36206, by rfl⟩) R72413
theorem R48305 : Reach 48305 := rs (se 2 (by rfl) ⟨18114, by rfl⟩) R36229
theorem R48323 : Reach 48323 := rs (se 1 (by rfl) ⟨36242, by rfl⟩) R72485
theorem R48353 : Reach 48353 := rs (se 2 (by rfl) ⟨18132, by rfl⟩) R36265
theorem R48371 : Reach 48371 := rs (se 1 (by rfl) ⟨36278, by rfl⟩) R72557
theorem R81155 : Reach 81155 := rs (se 1 (by rfl) ⟨60866, by rfl⟩) R121733
theorem R48401 : Reach 48401 := rs (se 2 (by rfl) ⟨18150, by rfl⟩) R36301
theorem R48419 : Reach 48419 := rs (se 1 (by rfl) ⟨36314, by rfl⟩) R72629
theorem R48433 : Reach 48433 := rs (se 2 (by rfl) ⟨18162, by rfl⟩) R36325
theorem R48449 : Reach 48449 := rs (se 2 (by rfl) ⟨18168, by rfl⟩) R36337
theorem R81233 : Reach 81233 := rs (se 2 (by rfl) ⟨30462, by rfl⟩) R60925
theorem R48467 : Reach 48467 := rs (se 1 (by rfl) ⟨36350, by rfl⟩) R72701
theorem R376163 : Reach 376163 := rs (se 1 (by rfl) ⟨282122, by rfl⟩) R564245
theorem R48497 : Reach 48497 := rs (se 2 (by rfl) ⟨18186, by rfl⟩) R36373
theorem R81283 : Reach 81283 := rs (se 1 (by rfl) ⟨60962, by rfl⟩) R121925
theorem R48515 : Reach 48515 := rs (se 1 (by rfl) ⟨36386, by rfl⟩) R72773
theorem R48545 : Reach 48545 := rs (se 2 (by rfl) ⟨18204, by rfl⟩) R36409
theorem R48547 : Reach 48547 := rs (se 1 (by rfl) ⟨36410, by rfl⟩) R72821
theorem R48563 : Reach 48563 := rs (se 1 (by rfl) ⟨36422, by rfl⟩) R72845
theorem R48593 : Reach 48593 := rs (se 2 (by rfl) ⟨18222, by rfl⟩) R36445
theorem R48611 : Reach 48611 := rs (se 1 (by rfl) ⟨36458, by rfl⟩) R72917
theorem R48641 : Reach 48641 := rs (se 2 (by rfl) ⟨18240, by rfl⟩) R36481
theorem R81425 : Reach 81425 := rs (se 2 (by rfl) ⟨30534, by rfl⟩) R61069
theorem R48659 : Reach 48659 := rs (se 1 (by rfl) ⟨36494, by rfl⟩) R72989
theorem R81443 : Reach 81443 := rs (se 1 (by rfl) ⟨61082, by rfl⟩) R122165
theorem R48689 : Reach 48689 := rs (se 2 (by rfl) ⟨18258, by rfl⟩) R36517
theorem R48707 : Reach 48707 := rs (se 1 (by rfl) ⟨36530, by rfl⟩) R73061
theorem R48737 : Reach 48737 := rs (se 2 (by rfl) ⟨18276, by rfl⟩) R36553
theorem R48755 : Reach 48755 := rs (se 1 (by rfl) ⟨36566, by rfl⟩) R73133
theorem R114317 : Reach 114317 := rs (se 3 (by rfl) ⟨21434, by rfl⟩) R42869
theorem R48785 : Reach 48785 := rs (se 2 (by rfl) ⟨18294, by rfl⟩) R36589
theorem R48803 : Reach 48803 := rs (se 1 (by rfl) ⟨36602, by rfl⟩) R73205
theorem R48833 : Reach 48833 := rs (se 2 (by rfl) ⟨18312, by rfl⟩) R36625
theorem R474821 : Reach 474821 := rs (se 4 (by rfl) ⟨44514, by rfl⟩) R89029
theorem R48851 : Reach 48851 := rs (se 1 (by rfl) ⟨36638, by rfl⟩) R73277
theorem R48881 : Reach 48881 := rs (se 2 (by rfl) ⟨18330, by rfl⟩) R36661
theorem R48899 : Reach 48899 := rs (se 1 (by rfl) ⟨36674, by rfl⟩) R73349
theorem R48929 : Reach 48929 := rs (se 2 (by rfl) ⟨18348, by rfl⟩) R36697
theorem R48947 : Reach 48947 := rs (se 1 (by rfl) ⟨36710, by rfl⟩) R73421
theorem R48977 : Reach 48977 := rs (se 2 (by rfl) ⟨18366, by rfl⟩) R36733
theorem R48995 : Reach 48995 := rs (se 1 (by rfl) ⟨36746, by rfl⟩) R73493
theorem R49025 : Reach 49025 := rs (se 2 (by rfl) ⟨18384, by rfl⟩) R36769
theorem R2015117 : Reach 2015117 := rs (se 3 (by rfl) ⟨377834, by rfl⟩) R755669
theorem R49043 : Reach 49043 := rs (se 1 (by rfl) ⟨36782, by rfl⟩) R73565
theorem R49073 : Reach 49073 := rs (se 2 (by rfl) ⟨18402, by rfl⟩) R36805
theorem R49091 : Reach 49091 := rs (se 1 (by rfl) ⟨36818, by rfl⟩) R73637
theorem R49121 : Reach 49121 := rs (se 2 (by rfl) ⟨18420, by rfl⟩) R36841
theorem R49139 : Reach 49139 := rs (se 1 (by rfl) ⟨36854, by rfl⟩) R73709
theorem R49169 : Reach 49169 := rs (se 2 (by rfl) ⟨18438, by rfl⟩) R36877
theorem R49187 : Reach 49187 := rs (se 1 (by rfl) ⟨36890, by rfl⟩) R73781
theorem R49217 : Reach 49217 := rs (se 2 (by rfl) ⟨18456, by rfl⟩) R36913
theorem R49235 : Reach 49235 := rs (se 1 (by rfl) ⟨36926, by rfl⟩) R73853
theorem R49265 : Reach 49265 := rs (se 2 (by rfl) ⟨18474, by rfl⟩) R36949
theorem R49283 : Reach 49283 := rs (se 1 (by rfl) ⟨36962, by rfl⟩) R73925
theorem R49313 : Reach 49313 := rs (se 2 (by rfl) ⟨18492, by rfl⟩) R36985
theorem R49331 : Reach 49331 := rs (se 1 (by rfl) ⟨36998, by rfl⟩) R73997
theorem R49361 : Reach 49361 := rs (se 2 (by rfl) ⟨18510, by rfl⟩) R37021
theorem R49379 : Reach 49379 := rs (se 1 (by rfl) ⟨37034, by rfl⟩) R74069
theorem R49409 : Reach 49409 := rs (se 2 (by rfl) ⟨18528, by rfl⟩) R37057
theorem R49427 : Reach 49427 := rs (se 1 (by rfl) ⟨37070, by rfl⟩) R74141
theorem R49457 : Reach 49457 := rs (se 2 (by rfl) ⟨18546, by rfl⟩) R37093
theorem R49475 : Reach 49475 := rs (se 1 (by rfl) ⟨37106, by rfl⟩) R74213
theorem R49505 : Reach 49505 := rs (se 2 (by rfl) ⟨18564, by rfl⟩) R37129
theorem R49523 : Reach 49523 := rs (se 1 (by rfl) ⟨37142, by rfl⟩) R74285
theorem R49553 : Reach 49553 := rs (se 2 (by rfl) ⟨18582, by rfl⟩) R37165
theorem R49571 : Reach 49571 := rs (se 1 (by rfl) ⟨37178, by rfl⟩) R74357
theorem R49601 : Reach 49601 := rs (se 2 (by rfl) ⟨18600, by rfl⟩) R37201
theorem R82385 : Reach 82385 := rs (se 2 (by rfl) ⟨30894, by rfl⟩) R61789
theorem R49619 : Reach 49619 := rs (se 1 (by rfl) ⟨37214, by rfl⟩) R74429
theorem R82417 : Reach 82417 := rs (se 2 (by rfl) ⟨30906, by rfl⟩) R61813
theorem R49649 : Reach 49649 := rs (se 2 (by rfl) ⟨18618, by rfl⟩) R37237
theorem R49667 : Reach 49667 := rs (se 1 (by rfl) ⟨37250, by rfl⟩) R74501
theorem R49697 : Reach 49697 := rs (se 2 (by rfl) ⟨18636, by rfl⟩) R37273
theorem R115235 : Reach 115235 := rs (se 1 (by rfl) ⟨86426, by rfl⟩) R172853
theorem R49715 : Reach 49715 := rs (se 1 (by rfl) ⟨37286, by rfl⟩) R74573
theorem R49745 : Reach 49745 := rs (se 2 (by rfl) ⟨18654, by rfl⟩) R37309
theorem R49763 : Reach 49763 := rs (se 1 (by rfl) ⟨37322, by rfl⟩) R74645
theorem R49793 : Reach 49793 := rs (se 2 (by rfl) ⟨18672, by rfl⟩) R37345
theorem R49811 : Reach 49811 := rs (se 1 (by rfl) ⟨37358, by rfl⟩) R74717
theorem R49841 : Reach 49841 := rs (se 2 (by rfl) ⟨18690, by rfl⟩) R37381
theorem R49859 : Reach 49859 := rs (se 1 (by rfl) ⟨37394, by rfl⟩) R74789
theorem R49889 : Reach 49889 := rs (se 2 (by rfl) ⟨18708, by rfl⟩) R37417
theorem R49891 : Reach 49891 := rs (se 1 (by rfl) ⟨37418, by rfl⟩) R74837
theorem R49907 : Reach 49907 := rs (se 1 (by rfl) ⟨37430, by rfl⟩) R74861
theorem R82691 : Reach 82691 := rs (se 1 (by rfl) ⟨62018, by rfl⟩) R124037
theorem R49937 : Reach 49937 := rs (se 2 (by rfl) ⟨18726, by rfl⟩) R37453
theorem R49955 : Reach 49955 := rs (se 1 (by rfl) ⟨37466, by rfl⟩) R74933
theorem R115505 : Reach 115505 := rs (se 2 (by rfl) ⟨43314, by rfl⟩) R86629
theorem R49985 : Reach 49985 := rs (se 2 (by rfl) ⟨18744, by rfl⟩) R37489
theorem R50003 : Reach 50003 := rs (se 1 (by rfl) ⟨37502, by rfl⟩) R75005
theorem R50033 : Reach 50033 := rs (se 2 (by rfl) ⟨18762, by rfl⟩) R37525
theorem R50051 : Reach 50051 := rs (se 1 (by rfl) ⟨37538, by rfl⟩) R75077
theorem R50081 : Reach 50081 := rs (se 2 (by rfl) ⟨18780, by rfl⟩) R37561
theorem R50099 : Reach 50099 := rs (se 1 (by rfl) ⟨37574, by rfl⟩) R75149
theorem R82883 : Reach 82883 := rs (se 1 (by rfl) ⟨62162, by rfl⟩) R124325
theorem R50129 : Reach 50129 := rs (se 2 (by rfl) ⟨18798, by rfl⟩) R37597
theorem R50147 : Reach 50147 := rs (se 1 (by rfl) ⟨37610, by rfl⟩) R75221
theorem R50177 : Reach 50177 := rs (se 2 (by rfl) ⟨18816, by rfl⟩) R37633
theorem R50195 : Reach 50195 := rs (se 1 (by rfl) ⟨37646, by rfl⟩) R75293
theorem R50225 : Reach 50225 := rs (se 2 (by rfl) ⟨18834, by rfl⟩) R37669
theorem R50243 : Reach 50243 := rs (se 1 (by rfl) ⟨37682, by rfl⟩) R75365
theorem R50273 : Reach 50273 := rs (se 2 (by rfl) ⟨18852, by rfl⟩) R37705
theorem R50291 : Reach 50291 := rs (se 1 (by rfl) ⟨37718, by rfl⟩) R75437
theorem R50321 : Reach 50321 := rs (se 2 (by rfl) ⟨18870, by rfl⟩) R37741
theorem R50323 : Reach 50323 := rs (se 1 (by rfl) ⟨37742, by rfl⟩) R75485
theorem R50339 : Reach 50339 := rs (se 1 (by rfl) ⟨37754, by rfl⟩) R75509
theorem R50369 : Reach 50369 := rs (se 2 (by rfl) ⟨18888, by rfl⟩) R37777
theorem R181453 : Reach 181453 := rs (se 3 (by rfl) ⟨34022, by rfl⟩) R68045
theorem R50387 : Reach 50387 := rs (se 1 (by rfl) ⟨37790, by rfl⟩) R75581
theorem R50417 : Reach 50417 := rs (se 2 (by rfl) ⟨18906, by rfl⟩) R37813
theorem R50435 : Reach 50435 := rs (se 1 (by rfl) ⟨37826, by rfl⟩) R75653
theorem R83213 : Reach 83213 := rs (se 3 (by rfl) ⟨15602, by rfl⟩) R31205
theorem R50465 : Reach 50465 := rs (se 2 (by rfl) ⟨18924, by rfl⟩) R37849
theorem R50483 : Reach 50483 := rs (se 1 (by rfl) ⟨37862, by rfl⟩) R75725
theorem R116045 : Reach 116045 := rs (se 3 (by rfl) ⟨21758, by rfl⟩) R43517
theorem R50513 : Reach 50513 := rs (se 2 (by rfl) ⟨18942, by rfl⟩) R37885
theorem R50531 : Reach 50531 := rs (se 1 (by rfl) ⟨37898, by rfl⟩) R75797
theorem R50561 : Reach 50561 := rs (se 2 (by rfl) ⟨18960, by rfl⟩) R37921
theorem R181645 : Reach 181645 := rs (se 3 (by rfl) ⟨34058, by rfl⟩) R68117
theorem R50579 : Reach 50579 := rs (se 1 (by rfl) ⟨37934, by rfl⟩) R75869
theorem R50609 : Reach 50609 := rs (se 2 (by rfl) ⟨18978, by rfl⟩) R37957
theorem R50627 : Reach 50627 := rs (se 1 (by rfl) ⟨37970, by rfl⟩) R75941
theorem R50657 : Reach 50657 := rs (se 2 (by rfl) ⟨18996, by rfl⟩) R37993
theorem R50675 : Reach 50675 := rs (se 1 (by rfl) ⟨38006, by rfl⟩) R76013
theorem R50705 : Reach 50705 := rs (se 2 (by rfl) ⟨19014, by rfl⟩) R38029
theorem R50723 : Reach 50723 := rs (se 1 (by rfl) ⟨38042, by rfl⟩) R76085
theorem R83501 : Reach 83501 := rs (se 3 (by rfl) ⟨15656, by rfl⟩) R31313
theorem R50753 : Reach 50753 := rs (se 2 (by rfl) ⟨19032, by rfl⟩) R38065
theorem R50771 : Reach 50771 := rs (se 1 (by rfl) ⟨38078, by rfl⟩) R76157
theorem R50801 : Reach 50801 := rs (se 2 (by rfl) ⟨19050, by rfl⟩) R38101
theorem R50819 : Reach 50819 := rs (se 1 (by rfl) ⟨38114, by rfl⟩) R76229
theorem R50849 : Reach 50849 := rs (se 2 (by rfl) ⟨19068, by rfl⟩) R38137
theorem R50867 : Reach 50867 := rs (se 1 (by rfl) ⟨38150, by rfl⟩) R76301
theorem R50897 : Reach 50897 := rs (se 2 (by rfl) ⟨19086, by rfl⟩) R38173
theorem R50915 : Reach 50915 := rs (se 1 (by rfl) ⟨38186, by rfl⟩) R76373
theorem R83693 : Reach 83693 := rs (se 3 (by rfl) ⟨15692, by rfl⟩) R31385
theorem R50945 : Reach 50945 := rs (se 2 (by rfl) ⟨19104, by rfl⟩) R38209
theorem R50963 : Reach 50963 := rs (se 1 (by rfl) ⟨38222, by rfl⟩) R76445
theorem R50993 : Reach 50993 := rs (se 2 (by rfl) ⟨19122, by rfl⟩) R38245
theorem R51011 : Reach 51011 := rs (se 1 (by rfl) ⟨38258, by rfl⟩) R76517
theorem R51041 : Reach 51041 := rs (se 2 (by rfl) ⟨19140, by rfl⟩) R38281
theorem R83825 : Reach 83825 := rs (se 2 (by rfl) ⟨31434, by rfl⟩) R62869
theorem R51059 : Reach 51059 := rs (se 1 (by rfl) ⟨38294, by rfl⟩) R76589
theorem R51089 : Reach 51089 := rs (se 2 (by rfl) ⟨19158, by rfl⟩) R38317
theorem R83875 : Reach 83875 := rs (se 1 (by rfl) ⟨62906, by rfl⟩) R125813
theorem R51107 : Reach 51107 := rs (se 1 (by rfl) ⟨38330, by rfl⟩) R76661
theorem R116657 : Reach 116657 := rs (se 2 (by rfl) ⟨43746, by rfl⟩) R87493
theorem R51137 : Reach 51137 := rs (se 2 (by rfl) ⟨19176, by rfl⟩) R38353
theorem R51155 : Reach 51155 := rs (se 1 (by rfl) ⟨38366, by rfl⟩) R76733
theorem R51185 : Reach 51185 := rs (se 2 (by rfl) ⟨19194, by rfl⟩) R38389
theorem R51203 : Reach 51203 := rs (se 1 (by rfl) ⟨38402, by rfl⟩) R76805
theorem R51233 : Reach 51233 := rs (se 2 (by rfl) ⟨19212, by rfl⟩) R38425
theorem R84017 : Reach 84017 := rs (se 2 (by rfl) ⟨31506, by rfl⟩) R63013
theorem R51251 : Reach 51251 := rs (se 1 (by rfl) ⟨38438, by rfl⟩) R76877
theorem R51281 : Reach 51281 := rs (se 2 (by rfl) ⟨19230, by rfl⟩) R38461
theorem R51299 : Reach 51299 := rs (se 1 (by rfl) ⟨38474, by rfl⟩) R76949
theorem R51329 : Reach 51329 := rs (se 2 (by rfl) ⟨19248, by rfl⟩) R38497
theorem R51347 : Reach 51347 := rs (se 1 (by rfl) ⟨38510, by rfl⟩) R77021
theorem R51377 : Reach 51377 := rs (se 2 (by rfl) ⟨19266, by rfl⟩) R38533
theorem R51395 : Reach 51395 := rs (se 1 (by rfl) ⟨38546, by rfl⟩) R77093
theorem R51425 : Reach 51425 := rs (se 2 (by rfl) ⟨19284, by rfl⟩) R38569
theorem R116963 : Reach 116963 := rs (se 1 (by rfl) ⟨87722, by rfl⟩) R175445
theorem R182513 : Reach 182513 := rs (se 2 (by rfl) ⟨68442, by rfl⟩) R136885
theorem R51443 : Reach 51443 := rs (se 1 (by rfl) ⟨38582, by rfl⟩) R77165
theorem R51473 : Reach 51473 := rs (se 2 (by rfl) ⟨19302, by rfl⟩) R38605
theorem R51491 : Reach 51491 := rs (se 1 (by rfl) ⟨38618, by rfl⟩) R77237
theorem R149795 : Reach 149795 := rs (se 1 (by rfl) ⟨112346, by rfl⟩) R224693
theorem R51521 : Reach 51521 := rs (se 2 (by rfl) ⟨19320, by rfl⟩) R38641
theorem R51539 : Reach 51539 := rs (se 1 (by rfl) ⟨38654, by rfl⟩) R77309
theorem R51569 : Reach 51569 := rs (se 2 (by rfl) ⟨19338, by rfl⟩) R38677
theorem R51587 : Reach 51587 := rs (se 1 (by rfl) ⟨38690, by rfl⟩) R77381
theorem R51617 : Reach 51617 := rs (se 2 (by rfl) ⟨19356, by rfl⟩) R38713
theorem R51619 : Reach 51619 := rs (se 1 (by rfl) ⟨38714, by rfl⟩) R77429
theorem R51635 : Reach 51635 := rs (se 1 (by rfl) ⟨38726, by rfl⟩) R77453
theorem R281029 : Reach 281029 := rs (se 4 (by rfl) ⟨26346, by rfl⟩) R52693
theorem R51665 : Reach 51665 := rs (se 2 (by rfl) ⟨19374, by rfl⟩) R38749
theorem R51683 : Reach 51683 := rs (se 1 (by rfl) ⟨38762, by rfl⟩) R77525
theorem R117233 : Reach 117233 := rs (se 2 (by rfl) ⟨43962, by rfl⟩) R87925
theorem R51713 : Reach 51713 := rs (se 2 (by rfl) ⟨19392, by rfl⟩) R38785
theorem R51731 : Reach 51731 := rs (se 1 (by rfl) ⟨38798, by rfl⟩) R77597
theorem R51745 : Reach 51745 := rs (se 2 (by rfl) ⟨19404, by rfl⟩) R38809
theorem R51761 : Reach 51761 := rs (se 2 (by rfl) ⟨19410, by rfl⟩) R38821
theorem R51779 : Reach 51779 := rs (se 1 (by rfl) ⟨38834, by rfl⟩) R77669
theorem R51809 : Reach 51809 := rs (se 2 (by rfl) ⟨19428, by rfl⟩) R38857
theorem R51827 : Reach 51827 := rs (se 1 (by rfl) ⟨38870, by rfl⟩) R77741
theorem R215693 : Reach 215693 := rs (se 3 (by rfl) ⟨40442, by rfl⟩) R80885
theorem R51857 : Reach 51857 := rs (se 2 (by rfl) ⟨19446, by rfl⟩) R38893
theorem R51875 : Reach 51875 := rs (se 1 (by rfl) ⟨38906, by rfl⟩) R77813
theorem R84653 : Reach 84653 := rs (se 3 (by rfl) ⟨15872, by rfl⟩) R31745
theorem R51905 : Reach 51905 := rs (se 2 (by rfl) ⟨19464, by rfl⟩) R38929
theorem R84685 : Reach 84685 := rs (se 3 (by rfl) ⟨15878, by rfl⟩) R31757
theorem R51923 : Reach 51923 := rs (se 1 (by rfl) ⟨38942, by rfl⟩) R77885
theorem R51953 : Reach 51953 := rs (se 2 (by rfl) ⟨19482, by rfl⟩) R38965
theorem R51971 : Reach 51971 := rs (se 1 (by rfl) ⟨38978, by rfl⟩) R77957
theorem R52001 : Reach 52001 := rs (se 2 (by rfl) ⟨19500, by rfl⟩) R39001
theorem R52019 : Reach 52019 := rs (se 1 (by rfl) ⟨39014, by rfl⟩) R78029
theorem R52049 : Reach 52049 := rs (se 2 (by rfl) ⟨19518, by rfl⟩) R39037
theorem R52067 : Reach 52067 := rs (se 1 (by rfl) ⟨39050, by rfl⟩) R78101
theorem R84845 : Reach 84845 := rs (se 3 (by rfl) ⟨15908, by rfl⟩) R31817
theorem R52097 : Reach 52097 := rs (se 2 (by rfl) ⟨19536, by rfl⟩) R39073
theorem R52115 : Reach 52115 := rs (se 1 (by rfl) ⟨39086, by rfl⟩) R78173
theorem R52145 : Reach 52145 := rs (se 2 (by rfl) ⟨19554, by rfl⟩) R39109
theorem R52163 : Reach 52163 := rs (se 1 (by rfl) ⟨39122, by rfl⟩) R78245
theorem R52193 : Reach 52193 := rs (se 2 (by rfl) ⟨19572, by rfl⟩) R39145
theorem R52211 : Reach 52211 := rs (se 1 (by rfl) ⟨39158, by rfl⟩) R78317
theorem R314381 : Reach 314381 := rs (se 3 (by rfl) ⟨58946, by rfl⟩) R117893
theorem R117773 : Reach 117773 := rs (se 3 (by rfl) ⟨22082, by rfl⟩) R44165
theorem R85009 : Reach 85009 := rs (se 2 (by rfl) ⟨31878, by rfl⟩) R63757
theorem R52241 : Reach 52241 := rs (se 2 (by rfl) ⟨19590, by rfl⟩) R39181
theorem R52259 : Reach 52259 := rs (se 1 (by rfl) ⟨39194, by rfl⟩) R78389
theorem R52289 : Reach 52289 := rs (se 2 (by rfl) ⟨19608, by rfl⟩) R39217
theorem R52307 : Reach 52307 := rs (se 1 (by rfl) ⟨39230, by rfl⟩) R78461
theorem R52337 : Reach 52337 := rs (se 2 (by rfl) ⟨19626, by rfl⟩) R39253
theorem R52355 : Reach 52355 := rs (se 1 (by rfl) ⟨39266, by rfl⟩) R78533
theorem R52385 : Reach 52385 := rs (se 2 (by rfl) ⟨19644, by rfl⟩) R39289
theorem R52403 : Reach 52403 := rs (se 1 (by rfl) ⟨39302, by rfl⟩) R78605
theorem R52433 : Reach 52433 := rs (se 2 (by rfl) ⟨19662, by rfl⟩) R39325
theorem R52451 : Reach 52451 := rs (se 1 (by rfl) ⟨39338, by rfl⟩) R78677
theorem R52481 : Reach 52481 := rs (se 2 (by rfl) ⟨19680, by rfl⟩) R39361
theorem R52483 : Reach 52483 := rs (se 1 (by rfl) ⟨39362, by rfl⟩) R78725
theorem R52499 : Reach 52499 := rs (se 1 (by rfl) ⟨39374, by rfl⟩) R78749
theorem R85283 : Reach 85283 := rs (se 1 (by rfl) ⟨63962, by rfl⟩) R127925
theorem R52529 : Reach 52529 := rs (se 2 (by rfl) ⟨19698, by rfl⟩) R39397
theorem R52547 : Reach 52547 := rs (se 1 (by rfl) ⟨39410, by rfl⟩) R78821
theorem R52577 : Reach 52577 := rs (se 2 (by rfl) ⟨19716, by rfl⟩) R39433
theorem R52595 : Reach 52595 := rs (se 1 (by rfl) ⟨39446, by rfl⟩) R78893
theorem R52609 : Reach 52609 := rs (se 2 (by rfl) ⟨19728, by rfl⟩) R39457
theorem R52625 : Reach 52625 := rs (se 2 (by rfl) ⟨19734, by rfl⟩) R39469
theorem R52643 : Reach 52643 := rs (se 1 (by rfl) ⟨39482, by rfl⟩) R78965
theorem R52673 : Reach 52673 := rs (se 2 (by rfl) ⟨19752, by rfl⟩) R39505
theorem R85475 : Reach 85475 := rs (se 1 (by rfl) ⟨64106, by rfl⟩) R128213
theorem R151025 : Reach 151025 := rs (se 2 (by rfl) ⟨56634, by rfl⟩) R113269
theorem R52739 : Reach 52739 := rs (se 1 (by rfl) ⟨39554, by rfl⟩) R79109
theorem R52771 : Reach 52771 := rs (se 1 (by rfl) ⟨39578, by rfl⟩) R79157
theorem R183941 : Reach 183941 := rs (se 4 (by rfl) ⟨17244, by rfl⟩) R34489
theorem R52913 : Reach 52913 := rs (se 2 (by rfl) ⟨19842, by rfl⟩) R39685
theorem R1199843 : Reach 1199843 := rs (se 1 (by rfl) ⟨899882, by rfl⟩) R1799765
theorem R53041 : Reach 53041 := rs (se 2 (by rfl) ⟨19890, by rfl⟩) R39781
theorem R53075 : Reach 53075 := rs (se 1 (by rfl) ⟨39806, by rfl⟩) R79613
theorem R118691 : Reach 118691 := rs (se 1 (by rfl) ⟨89018, by rfl⟩) R178037
theorem R118705 : Reach 118705 := rs (se 2 (by rfl) ⟨44514, by rfl⟩) R89029
theorem R53203 : Reach 53203 := rs (se 1 (by rfl) ⟨39902, by rfl⟩) R79805
theorem R86093 : Reach 86093 := rs (se 3 (by rfl) ⟨16142, by rfl⟩) R32285
theorem R53345 : Reach 53345 := rs (se 2 (by rfl) ⟨20004, by rfl⟩) R40009
theorem R53473 : Reach 53473 := rs (se 2 (by rfl) ⟨20052, by rfl⟩) R40105
theorem R53507 : Reach 53507 := rs (se 1 (by rfl) ⟨40130, by rfl⟩) R80261
theorem R86285 : Reach 86285 := rs (se 3 (by rfl) ⟨16178, by rfl⟩) R32357
theorem R53635 : Reach 53635 := rs (se 1 (by rfl) ⟨40226, by rfl⟩) R80453
theorem R86417 : Reach 86417 := rs (se 2 (by rfl) ⟨32406, by rfl⟩) R64813
theorem R86467 : Reach 86467 := rs (se 1 (by rfl) ⟨64850, by rfl⟩) R129701
theorem R53713 : Reach 53713 := rs (se 2 (by rfl) ⟨20142, by rfl⟩) R40285
theorem R53777 : Reach 53777 := rs (se 2 (by rfl) ⟨20166, by rfl⟩) R40333
theorem R348725 : Reach 348725 := rs (se 5 (by rfl) ⟨16346, by rfl⟩) R32693
theorem R86609 : Reach 86609 := rs (se 2 (by rfl) ⟨32478, by rfl⟩) R64957
theorem R53905 : Reach 53905 := rs (se 2 (by rfl) ⟨20214, by rfl⟩) R40429
theorem R53939 : Reach 53939 := rs (se 1 (by rfl) ⟨40454, by rfl⟩) R80909
theorem R54067 : Reach 54067 := rs (se 1 (by rfl) ⟨40550, by rfl⟩) R81101
theorem R349109 : Reach 349109 := rs (se 5 (by rfl) ⟨16364, by rfl⟩) R32729
theorem R54209 : Reach 54209 := rs (se 2 (by rfl) ⟨20328, by rfl⟩) R40657
theorem R54337 : Reach 54337 := rs (se 2 (by rfl) ⟨20376, by rfl⟩) R40753
theorem R54371 : Reach 54371 := rs (se 1 (by rfl) ⟨40778, by rfl⟩) R81557
theorem R54499 : Reach 54499 := rs (se 1 (by rfl) ⟨40874, by rfl⟩) R81749
theorem R87277 : Reach 87277 := rs (se 3 (by rfl) ⟨16364, by rfl⟩) R32729
theorem R120163 : Reach 120163 := rs (se 1 (by rfl) ⟨90122, by rfl⟩) R180245
theorem R54641 : Reach 54641 := rs (se 2 (by rfl) ⟨20490, by rfl⟩) R40981
theorem R87473 : Reach 87473 := rs (se 2 (by rfl) ⟨32802, by rfl⟩) R65605
theorem R54737 : Reach 54737 := rs (se 2 (by rfl) ⟨20526, by rfl⟩) R41053
theorem R54769 : Reach 54769 := rs (se 2 (by rfl) ⟨20538, by rfl⟩) R41077
theorem R54803 : Reach 54803 := rs (se 1 (by rfl) ⟨41102, by rfl⟩) R82205
theorem R87601 : Reach 87601 := rs (se 2 (by rfl) ⟨32850, by rfl⟩) R65701
theorem R54931 : Reach 54931 := rs (se 1 (by rfl) ⟨41198, by rfl⟩) R82397
theorem R218821 : Reach 218821 := rs (se 4 (by rfl) ⟨20514, by rfl⟩) R41029
theorem R55073 : Reach 55073 := rs (se 2 (by rfl) ⟨20652, by rfl⟩) R41305
theorem R87875 : Reach 87875 := rs (se 1 (by rfl) ⟨65906, by rfl⟩) R131813
theorem R251747 : Reach 251747 := rs (se 1 (by rfl) ⟨188810, by rfl⟩) R377621
theorem R55201 : Reach 55201 := rs (se 2 (by rfl) ⟨20700, by rfl⟩) R41401
theorem R55235 : Reach 55235 := rs (se 1 (by rfl) ⟨41426, by rfl⟩) R82853
theorem R120781 : Reach 120781 := rs (se 3 (by rfl) ⟨22646, by rfl⟩) R45293
theorem R186317 : Reach 186317 := rs (se 3 (by rfl) ⟨34934, by rfl⟩) R69869
theorem R88067 : Reach 88067 := rs (se 1 (by rfl) ⟨66050, by rfl⟩) R132101
theorem R55363 : Reach 55363 := rs (se 1 (by rfl) ⟨41522, by rfl⟩) R83045
theorem R547013 : Reach 547013 := rs (se 4 (by rfl) ⟨51282, by rfl⟩) R102565
theorem R55505 : Reach 55505 := rs (se 2 (by rfl) ⟨20814, by rfl⟩) R41629
theorem R252173 : Reach 252173 := rs (se 3 (by rfl) ⟨47282, by rfl⟩) R94565
theorem R55633 : Reach 55633 := rs (se 2 (by rfl) ⟨20862, by rfl⟩) R41725
theorem R55907 : Reach 55907 := rs (se 1 (by rfl) ⟨41930, by rfl⟩) R83861
theorem R88685 : Reach 88685 := rs (se 3 (by rfl) ⟨16628, by rfl⟩) R33257
theorem R88771 : Reach 88771 := rs (se 1 (by rfl) ⟨66578, by rfl⟩) R133157
theorem R88813 : Reach 88813 := rs (se 3 (by rfl) ⟨16652, by rfl⟩) R33305
theorem R56099 : Reach 56099 := rs (se 1 (by rfl) ⟨42074, by rfl⟩) R84149
theorem R88877 : Reach 88877 := rs (se 3 (by rfl) ⟨16664, by rfl⟩) R33329
theorem R56227 : Reach 56227 := rs (se 1 (by rfl) ⟨42170, by rfl⟩) R84341
theorem R56369 : Reach 56369 := rs (se 2 (by rfl) ⟨21138, by rfl⟩) R42277
theorem R89201 : Reach 89201 := rs (se 2 (by rfl) ⟨33450, by rfl⟩) R66901
theorem R56497 : Reach 56497 := rs (se 2 (by rfl) ⟨21186, by rfl⟩) R42373
theorem R187717 : Reach 187717 := rs (se 4 (by rfl) ⟨17598, by rfl⟩) R35197
theorem R56657 : Reach 56657 := rs (se 2 (by rfl) ⟨21246, by rfl⟩) R42493
theorem R89549 : Reach 89549 := rs (se 3 (by rfl) ⟨16790, by rfl⟩) R33581
theorem R122381 : Reach 122381 := rs (se 3 (by rfl) ⟨22946, by rfl⟩) R45893
theorem R56963 : Reach 56963 := rs (se 1 (by rfl) ⟨42722, by rfl⟩) R85445
theorem R57091 : Reach 57091 := rs (se 1 (by rfl) ⟨42818, by rfl⟩) R85637
theorem R89873 : Reach 89873 := rs (se 2 (by rfl) ⟨33702, by rfl⟩) R67405
theorem R384821 : Reach 384821 := rs (se 5 (by rfl) ⟨18038, by rfl⟩) R36077
theorem R57233 : Reach 57233 := rs (se 2 (by rfl) ⟨21462, by rfl⟩) R42925
theorem R57361 : Reach 57361 := rs (se 2 (by rfl) ⟨21510, by rfl⟩) R43021
theorem R90563 : Reach 90563 := rs (se 1 (by rfl) ⟨67922, by rfl⟩) R135845
theorem R57827 : Reach 57827 := rs (se 1 (by rfl) ⟨43370, by rfl⟩) R86741
theorem R90659 : Reach 90659 := rs (se 1 (by rfl) ⟨67994, by rfl⟩) R135989
theorem R57905 : Reach 57905 := rs (se 2 (by rfl) ⟨21714, by rfl⟩) R43429
theorem R57955 : Reach 57955 := rs (se 1 (by rfl) ⟨43466, by rfl⟩) R86933
theorem R58097 : Reach 58097 := rs (se 2 (by rfl) ⟨21786, by rfl⟩) R43573
theorem R90989 : Reach 90989 := rs (se 3 (by rfl) ⟨17060, by rfl⟩) R34121
theorem R58225 : Reach 58225 := rs (se 2 (by rfl) ⟨21834, by rfl⟩) R43669
theorem R91057 : Reach 91057 := rs (se 2 (by rfl) ⟨34146, by rfl⟩) R68293
theorem R91331 : Reach 91331 := rs (se 1 (by rfl) ⟨68498, by rfl⟩) R136997
theorem R124145 : Reach 124145 := rs (se 2 (by rfl) ⟨46554, by rfl⟩) R93109
theorem R189701 : Reach 189701 := rs (se 4 (by rfl) ⟨17784, by rfl⟩) R35569
theorem R877877 : Reach 877877 := rs (se 5 (by rfl) ⟨41150, by rfl⟩) R82301
theorem R58691 : Reach 58691 := rs (se 1 (by rfl) ⟨44018, by rfl⟩) R88037
theorem R58819 : Reach 58819 := rs (se 1 (by rfl) ⟨44114, by rfl⟩) R88229
theorem R288197 : Reach 288197 := rs (se 4 (by rfl) ⟨27018, by rfl⟩) R54037
theorem R58961 : Reach 58961 := rs (se 2 (by rfl) ⟨22110, by rfl⟩) R44221
theorem R59089 : Reach 59089 := rs (se 2 (by rfl) ⟨22158, by rfl⟩) R44317
theorem R92173 : Reach 92173 := rs (se 3 (by rfl) ⟨17282, by rfl⟩) R34565
theorem R125069 : Reach 125069 := rs (se 3 (by rfl) ⟨23450, by rfl⟩) R46901
theorem R59555 : Reach 59555 := rs (se 1 (by rfl) ⟨44666, by rfl⟩) R89333
theorem R92333 : Reach 92333 := rs (se 3 (by rfl) ⟨17312, by rfl⟩) R34625
theorem R92515 : Reach 92515 := rs (se 1 (by rfl) ⟨69386, by rfl⟩) R138773
theorem R125297 : Reach 125297 := rs (se 2 (by rfl) ⟨46986, by rfl⟩) R93973
theorem R59953 : Reach 59953 := rs (se 2 (by rfl) ⟨22482, by rfl⟩) R44965
theorem R59971 : Reach 59971 := rs (se 1 (by rfl) ⟨44978, by rfl⟩) R89957
theorem R158435 : Reach 158435 := rs (se 1 (by rfl) ⟨118826, by rfl⟩) R237653
theorem R92963 : Reach 92963 := rs (se 1 (by rfl) ⟨69722, by rfl⟩) R139445
theorem R60355 : Reach 60355 := rs (se 1 (by rfl) ⟨45266, by rfl⟩) R90533
theorem R60401 : Reach 60401 := rs (se 2 (by rfl) ⟨22650, by rfl⟩) R45301
theorem R289777 : Reach 289777 := rs (se 2 (by rfl) ⟨108666, by rfl⟩) R217333
theorem R60433 : Reach 60433 := rs (se 2 (by rfl) ⟨22662, by rfl⟩) R45325
theorem R257093 : Reach 257093 := rs (se 4 (by rfl) ⟨24102, by rfl⟩) R48205
theorem R158797 : Reach 158797 := rs (se 3 (by rfl) ⟨29774, by rfl⟩) R59549
theorem R60689 : Reach 60689 := rs (se 2 (by rfl) ⟨22758, by rfl⟩) R45517
theorem R159245 : Reach 159245 := rs (se 3 (by rfl) ⟨29858, by rfl⟩) R59717
theorem R93905 : Reach 93905 := rs (se 2 (by rfl) ⟨35214, by rfl⟩) R70429
theorem R126755 : Reach 126755 := rs (se 1 (by rfl) ⟨95066, by rfl⟩) R190133
theorem R61411 : Reach 61411 := rs (se 1 (by rfl) ⟨46058, by rfl⟩) R92117
theorem R61457 : Reach 61457 := rs (se 2 (by rfl) ⟨23046, by rfl⟩) R46093
theorem R159857 : Reach 159857 := rs (se 2 (by rfl) ⟨59946, by rfl⟩) R119893
theorem R487565 : Reach 487565 := rs (se 3 (by rfl) ⟨91418, by rfl⟩) R182837
theorem R61859 : Reach 61859 := rs (se 1 (by rfl) ⟨46394, by rfl⟩) R92789
theorem R94861 : Reach 94861 := rs (se 3 (by rfl) ⟨17786, by rfl⟩) R35573
theorem R62147 : Reach 62147 := rs (se 1 (by rfl) ⟨46610, by rfl⟩) R93221
theorem R127757 : Reach 127757 := rs (se 3 (by rfl) ⟨23954, by rfl⟩) R47909
theorem R95089 : Reach 95089 := rs (se 2 (by rfl) ⟨35658, by rfl⟩) R71317
theorem R193549 : Reach 193549 := rs (se 3 (by rfl) ⟨36290, by rfl⟩) R72581
theorem R95249 : Reach 95249 := rs (se 2 (by rfl) ⟨35718, by rfl⟩) R71437
theorem R422981 : Reach 422981 := rs (se 4 (by rfl) ⟨39654, by rfl⟩) R79309
theorem R128099 : Reach 128099 := rs (se 1 (by rfl) ⟨96074, by rfl⟩) R192149
theorem R95363 : Reach 95363 := rs (se 1 (by rfl) ⟨71522, by rfl⟩) R143045
theorem R521585 : Reach 521585 := rs (se 2 (by rfl) ⟨195594, by rfl⟩) R391189
theorem R259469 : Reach 259469 := rs (se 3 (by rfl) ⟨48650, by rfl⟩) R97301
theorem R325133 : Reach 325133 := rs (se 3 (by rfl) ⟨60962, by rfl⟩) R121925
theorem R63089 : Reach 63089 := rs (se 2 (by rfl) ⟨23658, by rfl⟩) R47317
theorem R96365 : Reach 96365 := rs (se 3 (by rfl) ⟨18068, by rfl⟩) R36137
theorem R96433 : Reach 96433 := rs (se 2 (by rfl) ⟨36162, by rfl⟩) R72325
theorem R96547 : Reach 96547 := rs (se 1 (by rfl) ⟨72410, by rfl⟩) R144821
theorem R162161 : Reach 162161 := rs (se 2 (by rfl) ⟨60810, by rfl⟩) R121621
theorem R31123 : Reach 31123 := rs (se 1 (by rfl) ⟨23342, by rfl⟩) R46685
theorem R31139 : Reach 31139 := rs (se 1 (by rfl) ⟨23354, by rfl⟩) R46709
theorem R31155 : Reach 31155 := rs (se 1 (by rfl) ⟨23366, by rfl⟩) R46733
theorem R96707 : Reach 96707 := rs (se 1 (by rfl) ⟨72530, by rfl⟩) R145061
theorem R31171 : Reach 31171 := rs (se 1 (by rfl) ⟨23378, by rfl⟩) R46757
theorem R31187 : Reach 31187 := rs (se 1 (by rfl) ⟨23390, by rfl⟩) R46781
theorem R31203 : Reach 31203 := rs (se 1 (by rfl) ⟨23402, by rfl⟩) R46805
theorem R63985 : Reach 63985 := rs (se 2 (by rfl) ⟨23994, by rfl⟩) R47989
theorem R31219 : Reach 31219 := rs (se 1 (by rfl) ⟨23414, by rfl⟩) R46829
theorem R31235 : Reach 31235 := rs (se 1 (by rfl) ⟨23426, by rfl⟩) R46853
theorem R31251 : Reach 31251 := rs (se 1 (by rfl) ⟨23438, by rfl⟩) R46877
theorem R31267 : Reach 31267 := rs (se 1 (by rfl) ⟨23450, by rfl⟩) R46901
theorem R31283 : Reach 31283 := rs (se 1 (by rfl) ⟨23462, by rfl⟩) R46925
theorem R31299 : Reach 31299 := rs (se 1 (by rfl) ⟨23474, by rfl⟩) R46949
theorem R31315 : Reach 31315 := rs (se 1 (by rfl) ⟨23486, by rfl⟩) R46973
theorem R31331 : Reach 31331 := rs (se 1 (by rfl) ⟨23498, by rfl⟩) R46997
theorem R31347 : Reach 31347 := rs (se 1 (by rfl) ⟨23510, by rfl⟩) R47021
theorem R31363 : Reach 31363 := rs (se 1 (by rfl) ⟨23522, by rfl⟩) R47045
theorem R64145 : Reach 64145 := rs (se 2 (by rfl) ⟨24054, by rfl⟩) R48109
theorem R31379 : Reach 31379 := rs (se 1 (by rfl) ⟨23534, by rfl⟩) R47069
theorem R31395 : Reach 31395 := rs (se 1 (by rfl) ⟨23546, by rfl⟩) R47093
theorem R31411 : Reach 31411 := rs (se 1 (by rfl) ⟨23558, by rfl⟩) R47117
theorem R31427 : Reach 31427 := rs (se 1 (by rfl) ⟨23570, by rfl⟩) R47141
theorem R31443 : Reach 31443 := rs (se 1 (by rfl) ⟨23582, by rfl⟩) R47165
theorem R31459 : Reach 31459 := rs (se 1 (by rfl) ⟨23594, by rfl⟩) R47189
theorem R31475 : Reach 31475 := rs (se 1 (by rfl) ⟨23606, by rfl⟩) R47213
theorem R31491 : Reach 31491 := rs (se 1 (by rfl) ⟨23618, by rfl⟩) R47237
theorem R31507 : Reach 31507 := rs (se 1 (by rfl) ⟨23630, by rfl⟩) R47261
theorem R31523 : Reach 31523 := rs (se 1 (by rfl) ⟨23642, by rfl⟩) R47285
theorem R31539 : Reach 31539 := rs (se 1 (by rfl) ⟨23654, by rfl⟩) R47309
theorem R31555 : Reach 31555 := rs (se 1 (by rfl) ⟨23666, by rfl⟩) R47333
theorem R129869 : Reach 129869 := rs (se 3 (by rfl) ⟨24350, by rfl⟩) R48701
theorem R31571 : Reach 31571 := rs (se 1 (by rfl) ⟨23678, by rfl⟩) R47357
theorem R31587 : Reach 31587 := rs (se 1 (by rfl) ⟨23690, by rfl⟩) R47381
theorem R31603 : Reach 31603 := rs (se 1 (by rfl) ⟨23702, by rfl⟩) R47405
theorem R31619 : Reach 31619 := rs (se 1 (by rfl) ⟨23714, by rfl⟩) R47429
theorem R31635 : Reach 31635 := rs (se 1 (by rfl) ⟨23726, by rfl⟩) R47453
theorem R31651 : Reach 31651 := rs (se 1 (by rfl) ⟨23738, by rfl⟩) R47477
theorem R31667 : Reach 31667 := rs (se 1 (by rfl) ⟨23750, by rfl⟩) R47501
theorem R31683 : Reach 31683 := rs (se 1 (by rfl) ⟨23762, by rfl⟩) R47525
theorem R195533 : Reach 195533 := rs (se 3 (by rfl) ⟨36662, by rfl⟩) R73325
theorem R31699 : Reach 31699 := rs (se 1 (by rfl) ⟨23774, by rfl⟩) R47549
theorem R31715 : Reach 31715 := rs (se 1 (by rfl) ⟨23786, by rfl⟩) R47573
theorem R31731 : Reach 31731 := rs (se 1 (by rfl) ⟨23798, by rfl⟩) R47597
theorem R31747 : Reach 31747 := rs (se 1 (by rfl) ⟨23810, by rfl⟩) R47621
theorem R31763 : Reach 31763 := rs (se 1 (by rfl) ⟨23822, by rfl⟩) R47645
theorem R64547 : Reach 64547 := rs (se 1 (by rfl) ⟨48410, by rfl⟩) R96821
theorem R31779 : Reach 31779 := rs (se 1 (by rfl) ⟨23834, by rfl⟩) R47669
theorem R31795 : Reach 31795 := rs (se 1 (by rfl) ⟨23846, by rfl⟩) R47693
theorem R31811 : Reach 31811 := rs (se 1 (by rfl) ⟨23858, by rfl⟩) R47717
theorem R31827 : Reach 31827 := rs (se 1 (by rfl) ⟨23870, by rfl⟩) R47741
theorem R31843 : Reach 31843 := rs (se 1 (by rfl) ⟨23882, by rfl⟩) R47765
theorem R31859 : Reach 31859 := rs (se 1 (by rfl) ⟨23894, by rfl⟩) R47789
theorem R31875 : Reach 31875 := rs (se 1 (by rfl) ⟨23906, by rfl⟩) R47813
theorem R31891 : Reach 31891 := rs (se 1 (by rfl) ⟨23918, by rfl⟩) R47837
theorem R31907 : Reach 31907 := rs (se 1 (by rfl) ⟨23930, by rfl⟩) R47861
theorem R31923 : Reach 31923 := rs (se 1 (by rfl) ⟨23942, by rfl⟩) R47885
theorem R31939 : Reach 31939 := rs (se 1 (by rfl) ⟨23954, by rfl⟩) R47909
theorem R31955 : Reach 31955 := rs (se 1 (by rfl) ⟨23966, by rfl⟩) R47933
theorem R31971 : Reach 31971 := rs (se 1 (by rfl) ⟨23978, by rfl⟩) R47957
theorem R31987 : Reach 31987 := rs (se 1 (by rfl) ⟨23990, by rfl⟩) R47981
theorem R32003 : Reach 32003 := rs (se 1 (by rfl) ⟨24002, by rfl⟩) R48005
theorem R32019 : Reach 32019 := rs (se 1 (by rfl) ⟨24014, by rfl⟩) R48029
theorem R32035 : Reach 32035 := rs (se 1 (by rfl) ⟨24026, by rfl⟩) R48053
theorem R32051 : Reach 32051 := rs (se 1 (by rfl) ⟨24038, by rfl⟩) R48077
theorem R32067 : Reach 32067 := rs (se 1 (by rfl) ⟨24050, by rfl⟩) R48101
theorem R32083 : Reach 32083 := rs (se 1 (by rfl) ⟨24062, by rfl⟩) R48125
theorem R32099 : Reach 32099 := rs (se 1 (by rfl) ⟨24074, by rfl⟩) R48149
theorem R32115 : Reach 32115 := rs (se 1 (by rfl) ⟨24086, by rfl⟩) R48173
theorem R32131 : Reach 32131 := rs (se 1 (by rfl) ⟨24098, by rfl⟩) R48197
theorem R32147 : Reach 32147 := rs (se 1 (by rfl) ⟨24110, by rfl⟩) R48221
theorem R32163 : Reach 32163 := rs (se 1 (by rfl) ⟨24122, by rfl⟩) R48245
theorem R32179 : Reach 32179 := rs (se 1 (by rfl) ⟨24134, by rfl⟩) R48269
theorem R32195 : Reach 32195 := rs (se 1 (by rfl) ⟨24146, by rfl⟩) R48293
theorem R32211 : Reach 32211 := rs (se 1 (by rfl) ⟨24158, by rfl⟩) R48317
theorem R32227 : Reach 32227 := rs (se 1 (by rfl) ⟨24170, by rfl⟩) R48341
theorem R97777 : Reach 97777 := rs (se 2 (by rfl) ⟨36666, by rfl⟩) R73333
theorem R32243 : Reach 32243 := rs (se 1 (by rfl) ⟨24182, by rfl⟩) R48365
theorem R32259 : Reach 32259 := rs (se 1 (by rfl) ⟨24194, by rfl⟩) R48389
theorem R32275 : Reach 32275 := rs (se 1 (by rfl) ⟨24206, by rfl⟩) R48413
theorem R32291 : Reach 32291 := rs (se 1 (by rfl) ⟨24218, by rfl⟩) R48437
theorem R32307 : Reach 32307 := rs (se 1 (by rfl) ⟨24230, by rfl⟩) R48461
theorem R32323 : Reach 32323 := rs (se 1 (by rfl) ⟨24242, by rfl⟩) R48485
theorem R32339 : Reach 32339 := rs (se 1 (by rfl) ⟨24254, by rfl⟩) R48509
theorem R32355 : Reach 32355 := rs (se 1 (by rfl) ⟨24266, by rfl⟩) R48533
theorem R130673 : Reach 130673 := rs (se 2 (by rfl) ⟨49002, by rfl⟩) R98005
theorem R32371 : Reach 32371 := rs (se 1 (by rfl) ⟨24278, by rfl⟩) R48557
theorem R32387 : Reach 32387 := rs (se 1 (by rfl) ⟨24290, by rfl⟩) R48581
theorem R32403 : Reach 32403 := rs (se 1 (by rfl) ⟨24302, by rfl⟩) R48605
theorem R32419 : Reach 32419 := rs (se 1 (by rfl) ⟨24314, by rfl⟩) R48629
theorem R32435 : Reach 32435 := rs (se 1 (by rfl) ⟨24326, by rfl⟩) R48653
theorem R32451 : Reach 32451 := rs (se 1 (by rfl) ⟨24338, by rfl⟩) R48677
theorem R32467 : Reach 32467 := rs (se 1 (by rfl) ⟨24350, by rfl⟩) R48701
theorem R32483 : Reach 32483 := rs (se 1 (by rfl) ⟨24362, by rfl⟩) R48725
theorem R32499 : Reach 32499 := rs (se 1 (by rfl) ⟨24374, by rfl⟩) R48749
theorem R32515 : Reach 32515 := rs (se 1 (by rfl) ⟨24386, by rfl⟩) R48773
theorem R32531 : Reach 32531 := rs (se 1 (by rfl) ⟨24398, by rfl⟩) R48797
theorem R163619 : Reach 163619 := rs (se 1 (by rfl) ⟨122714, by rfl⟩) R245429
theorem R32547 : Reach 32547 := rs (se 1 (by rfl) ⟨24410, by rfl⟩) R48821
theorem R32563 : Reach 32563 := rs (se 1 (by rfl) ⟨24422, by rfl⟩) R48845
theorem R32579 : Reach 32579 := rs (se 1 (by rfl) ⟨24434, by rfl⟩) R48869
theorem R32595 : Reach 32595 := rs (se 1 (by rfl) ⟨24446, by rfl⟩) R48893
theorem R32611 : Reach 32611 := rs (se 1 (by rfl) ⟨24458, by rfl⟩) R48917
theorem R196465 : Reach 196465 := rs (se 2 (by rfl) ⟨73674, by rfl⟩) R147349
theorem R32627 : Reach 32627 := rs (se 1 (by rfl) ⟨24470, by rfl⟩) R48941
theorem R32643 : Reach 32643 := rs (se 1 (by rfl) ⟨24482, by rfl⟩) R48965
theorem R32659 : Reach 32659 := rs (se 1 (by rfl) ⟨24494, by rfl⟩) R48989
theorem R32675 : Reach 32675 := rs (se 1 (by rfl) ⟨24506, by rfl⟩) R49013
theorem R65443 : Reach 65443 := rs (se 1 (by rfl) ⟨49082, by rfl⟩) R98165
theorem R32691 : Reach 32691 := rs (se 1 (by rfl) ⟨24518, by rfl⟩) R49037
theorem R32707 : Reach 32707 := rs (se 1 (by rfl) ⟨24530, by rfl⟩) R49061
theorem R32723 : Reach 32723 := rs (se 1 (by rfl) ⟨24542, by rfl⟩) R49085
theorem R32739 : Reach 32739 := rs (se 1 (by rfl) ⟨24554, by rfl⟩) R49109
theorem R32755 : Reach 32755 := rs (se 1 (by rfl) ⟨24566, by rfl⟩) R49133
theorem R32779 : Reach 32779 := rs (se 1 (by rfl) ⟨24584, by rfl⟩) R49169
theorem R32791 : Reach 32791 := rs (se 1 (by rfl) ⟨24593, by rfl⟩) R49187
theorem R32811 : Reach 32811 := rs (se 1 (by rfl) ⟨24608, by rfl⟩) R49217
theorem R163885 : Reach 163885 := rs (se 3 (by rfl) ⟨30728, by rfl⟩) R61457
theorem R32823 : Reach 32823 := rs (se 1 (by rfl) ⟨24617, by rfl⟩) R49235
theorem R32843 : Reach 32843 := rs (se 1 (by rfl) ⟨24632, by rfl⟩) R49265
theorem R32855 : Reach 32855 := rs (se 1 (by rfl) ⟨24641, by rfl⟩) R49283
theorem R32875 : Reach 32875 := rs (se 1 (by rfl) ⟨24656, by rfl⟩) R49313
theorem R32887 : Reach 32887 := rs (se 1 (by rfl) ⟨24665, by rfl⟩) R49331
theorem R196739 : Reach 196739 := rs (se 1 (by rfl) ⟨147554, by rfl⟩) R295109
theorem R32907 : Reach 32907 := rs (se 1 (by rfl) ⟨24680, by rfl⟩) R49361
theorem R32919 : Reach 32919 := rs (se 1 (by rfl) ⟨24689, by rfl⟩) R49379
theorem R32939 : Reach 32939 := rs (se 1 (by rfl) ⟨24704, by rfl⟩) R49409
theorem R32951 : Reach 32951 := rs (se 1 (by rfl) ⟨24713, by rfl⟩) R49427
theorem R32971 : Reach 32971 := rs (se 1 (by rfl) ⟨24728, by rfl⟩) R49457
theorem R32983 : Reach 32983 := rs (se 1 (by rfl) ⟨24737, by rfl⟩) R49475
theorem R33003 : Reach 33003 := rs (se 1 (by rfl) ⟨24752, by rfl⟩) R49505
theorem R33015 : Reach 33015 := rs (se 1 (by rfl) ⟨24761, by rfl⟩) R49523
theorem R33035 : Reach 33035 := rs (se 1 (by rfl) ⟨24776, by rfl⟩) R49553
theorem R65815 : Reach 65815 := rs (se 1 (by rfl) ⟨49361, by rfl⟩) R98723
theorem R33047 : Reach 33047 := rs (se 1 (by rfl) ⟨24785, by rfl⟩) R49571
theorem R33067 : Reach 33067 := rs (se 1 (by rfl) ⟨24800, by rfl⟩) R49601
theorem R33079 : Reach 33079 := rs (se 1 (by rfl) ⟨24809, by rfl⟩) R49619
theorem R33099 : Reach 33099 := rs (se 1 (by rfl) ⟨24824, by rfl⟩) R49649
theorem R33111 : Reach 33111 := rs (se 1 (by rfl) ⟨24833, by rfl⟩) R49667
theorem R33131 : Reach 33131 := rs (se 1 (by rfl) ⟨24848, by rfl⟩) R49697
theorem R33143 : Reach 33143 := rs (se 1 (by rfl) ⟨24857, by rfl⟩) R49715
theorem R33163 : Reach 33163 := rs (se 1 (by rfl) ⟨24872, by rfl⟩) R49745
theorem R33175 : Reach 33175 := rs (se 1 (by rfl) ⟨24881, by rfl⟩) R49763
theorem R33195 : Reach 33195 := rs (se 1 (by rfl) ⟨24896, by rfl⟩) R49793
theorem R33207 : Reach 33207 := rs (se 1 (by rfl) ⟨24905, by rfl⟩) R49811
theorem R33227 : Reach 33227 := rs (se 1 (by rfl) ⟨24920, by rfl⟩) R49841
theorem R33239 : Reach 33239 := rs (se 1 (by rfl) ⟨24929, by rfl⟩) R49859
theorem R33259 : Reach 33259 := rs (se 1 (by rfl) ⟨24944, by rfl⟩) R49889
theorem R66035 : Reach 66035 := rs (se 1 (by rfl) ⟨49526, by rfl⟩) R99053
theorem R33271 : Reach 33271 := rs (se 1 (by rfl) ⟨24953, by rfl⟩) R49907
theorem R33291 : Reach 33291 := rs (se 1 (by rfl) ⟨24968, by rfl⟩) R49937
theorem R33303 : Reach 33303 := rs (se 1 (by rfl) ⟨24977, by rfl⟩) R49955
theorem R33323 : Reach 33323 := rs (se 1 (by rfl) ⟨24992, by rfl⟩) R49985
theorem R33335 : Reach 33335 := rs (se 1 (by rfl) ⟨25001, by rfl⟩) R50003
theorem R33355 : Reach 33355 := rs (se 1 (by rfl) ⟨25016, by rfl⟩) R50033
theorem R33367 : Reach 33367 := rs (se 1 (by rfl) ⟨25025, by rfl⟩) R50051
theorem R33387 : Reach 33387 := rs (se 1 (by rfl) ⟨25040, by rfl⟩) R50081
theorem R33399 : Reach 33399 := rs (se 1 (by rfl) ⟨25049, by rfl⟩) R50099
theorem R33419 : Reach 33419 := rs (se 1 (by rfl) ⟨25064, by rfl⟩) R50129
theorem R66187 : Reach 66187 := rs (se 1 (by rfl) ⟨49640, by rfl⟩) R99281
theorem R33431 : Reach 33431 := rs (se 1 (by rfl) ⟨25073, by rfl⟩) R50147
theorem R33451 : Reach 33451 := rs (se 1 (by rfl) ⟨25088, by rfl⟩) R50177
theorem R33463 : Reach 33463 := rs (se 1 (by rfl) ⟨25097, by rfl⟩) R50195
theorem R33483 : Reach 33483 := rs (se 1 (by rfl) ⟨25112, by rfl⟩) R50225
theorem R33495 : Reach 33495 := rs (se 1 (by rfl) ⟨25121, by rfl⟩) R50243
theorem R33515 : Reach 33515 := rs (se 1 (by rfl) ⟨25136, by rfl⟩) R50273
theorem R33527 : Reach 33527 := rs (se 1 (by rfl) ⟨25145, by rfl⟩) R50291
theorem R33547 : Reach 33547 := rs (se 1 (by rfl) ⟨25160, by rfl⟩) R50321
theorem R33559 : Reach 33559 := rs (se 1 (by rfl) ⟨25169, by rfl⟩) R50339
theorem R33579 : Reach 33579 := rs (se 1 (by rfl) ⟨25184, by rfl⟩) R50369
theorem R33591 : Reach 33591 := rs (se 1 (by rfl) ⟨25193, by rfl⟩) R50387
theorem R33611 : Reach 33611 := rs (se 1 (by rfl) ⟨25208, by rfl⟩) R50417
theorem R33623 : Reach 33623 := rs (se 1 (by rfl) ⟨25217, by rfl⟩) R50435
theorem R33643 : Reach 33643 := rs (se 1 (by rfl) ⟨25232, by rfl⟩) R50465
theorem R33655 : Reach 33655 := rs (se 1 (by rfl) ⟨25241, by rfl⟩) R50483
theorem R33675 : Reach 33675 := rs (se 1 (by rfl) ⟨25256, by rfl⟩) R50513
theorem R33687 : Reach 33687 := rs (se 1 (by rfl) ⟨25265, by rfl⟩) R50531
theorem R33707 : Reach 33707 := rs (se 1 (by rfl) ⟨25280, by rfl⟩) R50561
theorem R33719 : Reach 33719 := rs (se 1 (by rfl) ⟨25289, by rfl⟩) R50579
theorem R33739 : Reach 33739 := rs (se 1 (by rfl) ⟨25304, by rfl⟩) R50609
theorem R33751 : Reach 33751 := rs (se 1 (by rfl) ⟨25313, by rfl⟩) R50627
theorem R66521 : Reach 66521 := rs (se 2 (by rfl) ⟨24945, by rfl⟩) R49891
theorem R33771 : Reach 33771 := rs (se 1 (by rfl) ⟨25328, by rfl⟩) R50657
theorem R33783 : Reach 33783 := rs (se 1 (by rfl) ⟨25337, by rfl⟩) R50675
theorem R33803 : Reach 33803 := rs (se 1 (by rfl) ⟨25352, by rfl⟩) R50705
theorem R33815 : Reach 33815 := rs (se 1 (by rfl) ⟨25361, by rfl⟩) R50723
theorem R33835 : Reach 33835 := rs (se 1 (by rfl) ⟨25376, by rfl⟩) R50753
theorem R33847 : Reach 33847 := rs (se 1 (by rfl) ⟨25385, by rfl⟩) R50771
theorem R33867 : Reach 33867 := rs (se 1 (by rfl) ⟨25400, by rfl⟩) R50801
theorem R33879 : Reach 33879 := rs (se 1 (by rfl) ⟨25409, by rfl⟩) R50819
theorem R33899 : Reach 33899 := rs (se 1 (by rfl) ⟨25424, by rfl⟩) R50849
theorem R33911 : Reach 33911 := rs (se 1 (by rfl) ⟨25433, by rfl⟩) R50867
theorem R33931 : Reach 33931 := rs (se 1 (by rfl) ⟨25448, by rfl⟩) R50897
theorem R33943 : Reach 33943 := rs (se 1 (by rfl) ⟨25457, by rfl⟩) R50915
theorem R33963 : Reach 33963 := rs (se 1 (by rfl) ⟨25472, by rfl⟩) R50945
theorem R33975 : Reach 33975 := rs (se 1 (by rfl) ⟨25481, by rfl⟩) R50963
theorem R33995 : Reach 33995 := rs (se 1 (by rfl) ⟨25496, by rfl⟩) R50993
theorem R132299 : Reach 132299 := rs (se 1 (by rfl) ⟨99224, by rfl⟩) R198449
theorem R34007 : Reach 34007 := rs (se 1 (by rfl) ⟨25505, by rfl⟩) R51011
theorem R132313 : Reach 132313 := rs (se 2 (by rfl) ⟨49617, by rfl⟩) R99235
theorem R34027 : Reach 34027 := rs (se 1 (by rfl) ⟨25520, by rfl⟩) R51041
theorem R34039 : Reach 34039 := rs (se 1 (by rfl) ⟨25529, by rfl⟩) R51059
theorem R34059 : Reach 34059 := rs (se 1 (by rfl) ⟨25544, by rfl⟩) R51089
theorem R34071 : Reach 34071 := rs (se 1 (by rfl) ⟨25553, by rfl⟩) R51107
theorem R34091 : Reach 34091 := rs (se 1 (by rfl) ⟨25568, by rfl⟩) R51137
theorem R34103 : Reach 34103 := rs (se 1 (by rfl) ⟨25577, by rfl⟩) R51155
theorem R34123 : Reach 34123 := rs (se 1 (by rfl) ⟨25592, by rfl⟩) R51185
theorem R34135 : Reach 34135 := rs (se 1 (by rfl) ⟨25601, by rfl⟩) R51203
theorem R34155 : Reach 34155 := rs (se 1 (by rfl) ⟨25616, by rfl⟩) R51233
theorem R34167 : Reach 34167 := rs (se 1 (by rfl) ⟨25625, by rfl⟩) R51251
theorem R34187 : Reach 34187 := rs (se 1 (by rfl) ⟨25640, by rfl⟩) R51281
theorem R34199 : Reach 34199 := rs (se 1 (by rfl) ⟨25649, by rfl⟩) R51299
theorem R34219 : Reach 34219 := rs (se 1 (by rfl) ⟨25664, by rfl⟩) R51329
theorem R34231 : Reach 34231 := rs (se 1 (by rfl) ⟨25673, by rfl⟩) R51347
theorem R34251 : Reach 34251 := rs (se 1 (by rfl) ⟨25688, by rfl⟩) R51377
theorem R34263 : Reach 34263 := rs (se 1 (by rfl) ⟨25697, by rfl⟩) R51395
theorem R99805 : Reach 99805 := rs (se 3 (by rfl) ⟨18713, by rfl⟩) R37427
theorem R34283 : Reach 34283 := rs (se 1 (by rfl) ⟨25712, by rfl⟩) R51425
theorem R34295 : Reach 34295 := rs (se 1 (by rfl) ⟨25721, by rfl⟩) R51443
theorem R34315 : Reach 34315 := rs (se 1 (by rfl) ⟨25736, by rfl⟩) R51473
theorem R34327 : Reach 34327 := rs (se 1 (by rfl) ⟨25745, by rfl⟩) R51491
theorem R99863 : Reach 99863 := rs (se 1 (by rfl) ⟨74897, by rfl⟩) R149795
theorem R67097 : Reach 67097 := rs (se 2 (by rfl) ⟨25161, by rfl⟩) R50323
theorem R34347 : Reach 34347 := rs (se 1 (by rfl) ⟨25760, by rfl⟩) R51521
theorem R34359 : Reach 34359 := rs (se 1 (by rfl) ⟨25769, by rfl⟩) R51539
theorem R34379 : Reach 34379 := rs (se 1 (by rfl) ⟨25784, by rfl⟩) R51569
theorem R34391 : Reach 34391 := rs (se 1 (by rfl) ⟨25793, by rfl⟩) R51587
theorem R34411 : Reach 34411 := rs (se 1 (by rfl) ⟨25808, by rfl⟩) R51617
theorem R34423 : Reach 34423 := rs (se 1 (by rfl) ⟨25817, by rfl⟩) R51635
theorem R34443 : Reach 34443 := rs (se 1 (by rfl) ⟨25832, by rfl⟩) R51665
theorem R34455 : Reach 34455 := rs (se 1 (by rfl) ⟨25841, by rfl⟩) R51683
theorem R34475 : Reach 34475 := rs (se 1 (by rfl) ⟨25856, by rfl⟩) R51713
theorem R34487 : Reach 34487 := rs (se 1 (by rfl) ⟨25865, by rfl⟩) R51731
theorem R34507 : Reach 34507 := rs (se 1 (by rfl) ⟨25880, by rfl⟩) R51761
theorem R34519 : Reach 34519 := rs (se 1 (by rfl) ⟨25889, by rfl⟩) R51779
theorem R263897 : Reach 263897 := rs (se 2 (by rfl) ⟨98961, by rfl⟩) R197923
theorem R34539 : Reach 34539 := rs (se 1 (by rfl) ⟨25904, by rfl⟩) R51809
theorem R34551 : Reach 34551 := rs (se 1 (by rfl) ⟨25913, by rfl⟩) R51827
theorem R67339 : Reach 67339 := rs (se 1 (by rfl) ⟨50504, by rfl⟩) R101009
theorem R34571 : Reach 34571 := rs (se 1 (by rfl) ⟨25928, by rfl⟩) R51857
theorem R34583 : Reach 34583 := rs (se 1 (by rfl) ⟨25937, by rfl⟩) R51875
theorem R34603 : Reach 34603 := rs (se 1 (by rfl) ⟨25952, by rfl⟩) R51905
theorem R34615 : Reach 34615 := rs (se 1 (by rfl) ⟨25961, by rfl⟩) R51923
theorem R34635 : Reach 34635 := rs (se 1 (by rfl) ⟨25976, by rfl⟩) R51953
theorem R34647 : Reach 34647 := rs (se 1 (by rfl) ⟨25985, by rfl⟩) R51971
theorem R165725 : Reach 165725 := rs (se 3 (by rfl) ⟨31073, by rfl⟩) R62147
theorem R34667 : Reach 34667 := rs (se 1 (by rfl) ⟨26000, by rfl⟩) R52001
theorem R34679 : Reach 34679 := rs (se 1 (by rfl) ⟨26009, by rfl⟩) R52019
theorem R34699 : Reach 34699 := rs (se 1 (by rfl) ⟨26024, by rfl⟩) R52049
theorem R34711 : Reach 34711 := rs (se 1 (by rfl) ⟨26033, by rfl⟩) R52067
theorem R34731 : Reach 34731 := rs (se 1 (by rfl) ⟨26048, by rfl⟩) R52097
theorem R34743 : Reach 34743 := rs (se 1 (by rfl) ⟨26057, by rfl⟩) R52115
theorem R34763 : Reach 34763 := rs (se 1 (by rfl) ⟨26072, by rfl⟩) R52145
theorem R34775 : Reach 34775 := rs (se 1 (by rfl) ⟨26081, by rfl⟩) R52163
theorem R34795 : Reach 34795 := rs (se 1 (by rfl) ⟨26096, by rfl⟩) R52193
theorem R34807 : Reach 34807 := rs (se 1 (by rfl) ⟨26105, by rfl⟩) R52211
theorem R133123 : Reach 133123 := rs (se 1 (by rfl) ⟨99842, by rfl⟩) R199685
theorem R34827 : Reach 34827 := rs (se 1 (by rfl) ⟨26120, by rfl⟩) R52241
theorem R34839 : Reach 34839 := rs (se 1 (by rfl) ⟨26129, by rfl⟩) R52259
theorem R34859 : Reach 34859 := rs (se 1 (by rfl) ⟨26144, by rfl⟩) R52289
theorem R34871 : Reach 34871 := rs (se 1 (by rfl) ⟨26153, by rfl⟩) R52307
theorem R34891 : Reach 34891 := rs (se 1 (by rfl) ⟨26168, by rfl⟩) R52337
theorem R34903 : Reach 34903 := rs (se 1 (by rfl) ⟨26177, by rfl⟩) R52355
theorem R165989 : Reach 165989 := rs (se 4 (by rfl) ⟨15561, by rfl⟩) R31123
theorem R34923 : Reach 34923 := rs (se 1 (by rfl) ⟨26192, by rfl⟩) R52385
theorem R34935 : Reach 34935 := rs (se 1 (by rfl) ⟨26201, by rfl⟩) R52403
theorem R34955 : Reach 34955 := rs (se 1 (by rfl) ⟨26216, by rfl⟩) R52433
theorem R133271 : Reach 133271 := rs (se 1 (by rfl) ⟨99953, by rfl⟩) R199907
theorem R34967 : Reach 34967 := rs (se 1 (by rfl) ⟨26225, by rfl⟩) R52451
theorem R34987 : Reach 34987 := rs (se 1 (by rfl) ⟨26240, by rfl⟩) R52481
theorem R67763 : Reach 67763 := rs (se 1 (by rfl) ⟨50822, by rfl⟩) R101645
theorem R34999 : Reach 34999 := rs (se 1 (by rfl) ⟨26249, by rfl⟩) R52499
theorem R35019 : Reach 35019 := rs (se 1 (by rfl) ⟨26264, by rfl⟩) R52529
theorem R35031 : Reach 35031 := rs (se 1 (by rfl) ⟨26273, by rfl⟩) R52547
theorem R35051 : Reach 35051 := rs (se 1 (by rfl) ⟨26288, by rfl⟩) R52577
theorem R35063 : Reach 35063 := rs (se 1 (by rfl) ⟨26297, by rfl⟩) R52595
theorem R35083 : Reach 35083 := rs (se 1 (by rfl) ⟨26312, by rfl⟩) R52625
theorem R35095 : Reach 35095 := rs (se 1 (by rfl) ⟨26321, by rfl⟩) R52643
theorem R35115 : Reach 35115 := rs (se 1 (by rfl) ⟨26336, by rfl⟩) R52673
theorem R35159 : Reach 35159 := rs (se 1 (by rfl) ⟨26369, by rfl⟩) R52739
theorem R35275 : Reach 35275 := rs (se 1 (by rfl) ⟨26456, by rfl⟩) R52913
theorem R35383 : Reach 35383 := rs (se 1 (by rfl) ⟨26537, by rfl⟩) R53075
theorem R101081 : Reach 101081 := rs (se 2 (by rfl) ⟨37905, by rfl⟩) R75811
theorem R35563 : Reach 35563 := rs (se 1 (by rfl) ⟨26672, by rfl⟩) R53345
theorem R35671 : Reach 35671 := rs (se 1 (by rfl) ⟨26753, by rfl⟩) R53507
theorem R35851 : Reach 35851 := rs (se 1 (by rfl) ⟨26888, by rfl⟩) R53777
theorem R232483 : Reach 232483 := rs (se 1 (by rfl) ⟨174362, by rfl⟩) R348725
theorem R35959 : Reach 35959 := rs (se 1 (by rfl) ⟨26969, by rfl⟩) R53939
theorem R68825 : Reach 68825 := rs (se 2 (by rfl) ⟨25809, by rfl⟩) R51619
theorem R232739 : Reach 232739 := rs (se 1 (by rfl) ⟨174554, by rfl⟩) R349109
theorem R36139 : Reach 36139 := rs (se 1 (by rfl) ⟨27104, by rfl⟩) R54209
theorem R68951 : Reach 68951 := rs (se 1 (by rfl) ⟨51713, by rfl⟩) R103427
theorem R68993 : Reach 68993 := rs (se 2 (by rfl) ⟨25872, by rfl⟩) R51745
theorem R36247 : Reach 36247 := rs (se 1 (by rfl) ⟨27185, by rfl⟩) R54371
theorem R36427 : Reach 36427 := rs (se 1 (by rfl) ⟨27320, by rfl⟩) R54641
theorem R36535 : Reach 36535 := rs (se 1 (by rfl) ⟨27401, by rfl⟩) R54803
theorem R134873 : Reach 134873 := rs (se 2 (by rfl) ⟨50577, by rfl⟩) R101155
theorem R36715 : Reach 36715 := rs (se 1 (by rfl) ⟨27536, by rfl⟩) R55073
theorem R167831 : Reach 167831 := rs (se 1 (by rfl) ⟨125873, by rfl⟩) R251747
theorem R36823 : Reach 36823 := rs (se 1 (by rfl) ⟨27617, by rfl⟩) R55235
theorem R364675 : Reach 364675 := rs (se 1 (by rfl) ⟨273506, by rfl⟩) R547013
theorem R37003 : Reach 37003 := rs (se 1 (by rfl) ⟨27752, by rfl⟩) R55505
theorem R168115 : Reach 168115 := rs (se 1 (by rfl) ⟨126086, by rfl⟩) R252173
theorem R102721 : Reach 102721 := rs (se 2 (by rfl) ⟨38520, by rfl⟩) R77041
theorem R69977 : Reach 69977 := rs (se 2 (by rfl) ⟨26241, by rfl⟩) R52483
theorem R37271 : Reach 37271 := rs (se 1 (by rfl) ⟨27953, by rfl⟩) R55907
theorem R70091 : Reach 70091 := rs (se 1 (by rfl) ⟨52568, by rfl⟩) R105137
theorem R70145 : Reach 70145 := rs (se 2 (by rfl) ⟨26304, by rfl⟩) R52609
theorem R37399 : Reach 37399 := rs (se 1 (by rfl) ⟨28049, by rfl⟩) R56099
theorem R135731 : Reach 135731 := rs (se 1 (by rfl) ⟨101798, by rfl⟩) R203597
theorem R332363 : Reach 332363 := rs (se 1 (by rfl) ⟨249272, by rfl⟩) R498545
theorem R37579 : Reach 37579 := rs (se 1 (by rfl) ⟨28184, by rfl⟩) R56369
theorem R70361 : Reach 70361 := rs (se 2 (by rfl) ⟨26385, by rfl⟩) R52771
theorem R70451 : Reach 70451 := rs (se 1 (by rfl) ⟨52838, by rfl⟩) R105677
theorem R70487 : Reach 70487 := rs (se 1 (by rfl) ⟨52865, by rfl⟩) R105731
theorem R70667 : Reach 70667 := rs (se 1 (by rfl) ⟨53000, by rfl⟩) R106001
theorem R70721 : Reach 70721 := rs (se 2 (by rfl) ⟨26520, by rfl⟩) R53041
theorem R37975 : Reach 37975 := rs (se 1 (by rfl) ⟨28481, by rfl⟩) R56963
theorem R38155 : Reach 38155 := rs (se 1 (by rfl) ⟨28616, by rfl⟩) R57233
theorem R70937 : Reach 70937 := rs (se 2 (by rfl) ⟨26601, by rfl⟩) R53203
theorem R71027 : Reach 71027 := rs (se 1 (by rfl) ⟨53270, by rfl⟩) R106541
theorem R71063 : Reach 71063 := rs (se 1 (by rfl) ⟨53297, by rfl⟩) R106595
theorem R71243 : Reach 71243 := rs (se 1 (by rfl) ⟨53432, by rfl⟩) R106865
theorem R71297 : Reach 71297 := rs (se 2 (by rfl) ⟨26736, by rfl⟩) R53473
theorem R267907 : Reach 267907 := rs (se 1 (by rfl) ⟨200930, by rfl⟩) R401861
theorem R38551 : Reach 38551 := rs (se 1 (by rfl) ⟨28913, by rfl⟩) R57827
theorem R38603 : Reach 38603 := rs (se 1 (by rfl) ⟨28952, by rfl⟩) R57905
theorem R202571 : Reach 202571 := rs (se 1 (by rfl) ⟨151928, by rfl⟩) R303857
theorem R38731 : Reach 38731 := rs (se 1 (by rfl) ⟨29048, by rfl⟩) R58097
theorem R71513 : Reach 71513 := rs (se 2 (by rfl) ⟨26817, by rfl⟩) R53635
theorem R71603 : Reach 71603 := rs (se 1 (by rfl) ⟨53702, by rfl⟩) R107405
theorem R71617 : Reach 71617 := rs (se 2 (by rfl) ⟨26856, by rfl⟩) R53713
theorem R71639 : Reach 71639 := rs (se 1 (by rfl) ⟨53729, by rfl⟩) R107459
theorem R399491 : Reach 399491 := rs (se 1 (by rfl) ⟨299618, by rfl⟩) R599237
theorem R71819 : Reach 71819 := rs (se 1 (by rfl) ⟨53864, by rfl⟩) R107729
theorem R137389 : Reach 137389 := rs (se 3 (by rfl) ⟨25760, by rfl⟩) R51521
theorem R71873 : Reach 71873 := rs (se 2 (by rfl) ⟨26952, by rfl⟩) R53905
theorem R39127 : Reach 39127 := rs (se 1 (by rfl) ⟨29345, by rfl⟩) R58691
theorem R104669 : Reach 104669 := rs (se 3 (by rfl) ⟨19625, by rfl⟩) R39251
theorem R39307 : Reach 39307 := rs (se 1 (by rfl) ⟨29480, by rfl⟩) R58961
theorem R72089 : Reach 72089 := rs (se 2 (by rfl) ⟨27033, by rfl⟩) R54067
theorem R137645 : Reach 137645 := rs (se 3 (by rfl) ⟨25808, by rfl⟩) R51617
theorem R72179 : Reach 72179 := rs (se 1 (by rfl) ⟨54134, by rfl⟩) R108269
theorem R72215 : Reach 72215 := rs (se 1 (by rfl) ⟨54161, by rfl⟩) R108323
theorem R268865 : Reach 268865 := rs (se 2 (by rfl) ⟨100824, by rfl⟩) R201649
theorem R203357 : Reach 203357 := rs (se 3 (by rfl) ⟨38129, by rfl⟩) R76259
theorem R72395 : Reach 72395 := rs (se 1 (by rfl) ⟨54296, by rfl⟩) R108593
theorem R105181 : Reach 105181 := rs (se 3 (by rfl) ⟨19721, by rfl⟩) R39443
theorem R72449 : Reach 72449 := rs (se 2 (by rfl) ⟨27168, by rfl⟩) R54337
theorem R137987 : Reach 137987 := rs (se 1 (by rfl) ⟨103490, by rfl⟩) R206981
theorem R39703 : Reach 39703 := rs (se 1 (by rfl) ⟨29777, by rfl⟩) R59555
theorem R236465 : Reach 236465 := rs (se 2 (by rfl) ⟨88674, by rfl⟩) R177349
theorem R72665 : Reach 72665 := rs (se 2 (by rfl) ⟨27249, by rfl⟩) R54499
theorem R72755 : Reach 72755 := rs (se 1 (by rfl) ⟨54566, by rfl⟩) R109133
theorem R72791 : Reach 72791 := rs (se 1 (by rfl) ⟨54593, by rfl⟩) R109187
theorem R105623 : Reach 105623 := rs (se 1 (by rfl) ⟨79217, by rfl⟩) R158435
theorem R72947 : Reach 72947 := rs (se 1 (by rfl) ⟨54710, by rfl⟩) R109421
theorem R72971 : Reach 72971 := rs (se 1 (by rfl) ⟨54728, by rfl⟩) R109457
theorem R73025 : Reach 73025 := rs (se 2 (by rfl) ⟨27384, by rfl⟩) R54769
theorem R40267 : Reach 40267 := rs (se 1 (by rfl) ⟨30200, by rfl⟩) R60401
theorem R171395 : Reach 171395 := rs (se 1 (by rfl) ⟨128546, by rfl⟩) R257093
theorem R204211 : Reach 204211 := rs (se 1 (by rfl) ⟨153158, by rfl⟩) R306317
theorem R73163 : Reach 73163 := rs (se 1 (by rfl) ⟨54872, by rfl⟩) R109745
theorem R892433 : Reach 892433 := rs (se 2 (by rfl) ⟨334662, by rfl⟩) R669325
theorem R73241 : Reach 73241 := rs (se 2 (by rfl) ⟨27465, by rfl⟩) R54931
theorem R73331 : Reach 73331 := rs (se 1 (by rfl) ⟨54998, by rfl⟩) R109997
theorem R73367 : Reach 73367 := rs (se 1 (by rfl) ⟨55025, by rfl⟩) R110051
theorem R106163 : Reach 106163 := rs (se 1 (by rfl) ⟨79622, by rfl⟩) R159245
theorem R73547 : Reach 73547 := rs (se 1 (by rfl) ⟨55160, by rfl⟩) R110321
theorem R73601 : Reach 73601 := rs (se 2 (by rfl) ⟨27600, by rfl⟩) R55201
theorem R106433 : Reach 106433 := rs (se 2 (by rfl) ⟨39912, by rfl⟩) R79825
theorem R499729 : Reach 499729 := rs (se 2 (by rfl) ⟨187398, by rfl⟩) R374797
theorem R106571 : Reach 106571 := rs (se 1 (by rfl) ⟨79928, by rfl⟩) R159857
theorem R73817 : Reach 73817 := rs (se 2 (by rfl) ⟨27681, by rfl⟩) R55363
theorem R73907 : Reach 73907 := rs (se 1 (by rfl) ⟨55430, by rfl⟩) R110861
theorem R41239 : Reach 41239 := rs (se 1 (by rfl) ⟨30929, by rfl⟩) R61859
theorem R74177 : Reach 74177 := rs (se 2 (by rfl) ⟨27816, by rfl⟩) R55633
theorem R106973 : Reach 106973 := rs (se 3 (by rfl) ⟨20057, by rfl⟩) R40115
theorem R74519 : Reach 74519 := rs (se 1 (by rfl) ⟨55889, by rfl⟩) R111779
theorem R205699 : Reach 205699 := rs (se 1 (by rfl) ⟨154274, by rfl⟩) R308549
theorem R172979 : Reach 172979 := rs (se 1 (by rfl) ⟨129734, by rfl⟩) R259469
theorem R74699 : Reach 74699 := rs (se 1 (by rfl) ⟨56024, by rfl⟩) R112049
theorem R74803 : Reach 74803 := rs (se 1 (by rfl) ⟨56102, by rfl⟩) R112205
theorem R140363 : Reach 140363 := rs (se 1 (by rfl) ⟨105272, by rfl⟩) R210545
theorem R42059 : Reach 42059 := rs (se 1 (by rfl) ⟨31544, by rfl⟩) R63089
theorem R74969 : Reach 74969 := rs (se 2 (by rfl) ⟨28113, by rfl⟩) R56227
theorem R402733 : Reach 402733 := rs (se 3 (by rfl) ⟨75512, by rfl⟩) R151025
theorem R75059 : Reach 75059 := rs (se 1 (by rfl) ⟨56294, by rfl⟩) R112589
theorem R75329 : Reach 75329 := rs (se 2 (by rfl) ⟨28248, by rfl⟩) R56497
theorem R108107 : Reach 108107 := rs (se 1 (by rfl) ⟨81080, by rfl⟩) R162161
theorem R108253 : Reach 108253 := rs (se 3 (by rfl) ⟨20297, by rfl⟩) R40595
theorem R42763 : Reach 42763 := rs (se 1 (by rfl) ⟨32072, by rfl⟩) R64145
theorem R108377 : Reach 108377 := rs (se 2 (by rfl) ⟨40641, by rfl⟩) R81283
theorem R75671 : Reach 75671 := rs (se 1 (by rfl) ⟨56753, by rfl⟩) R113507
theorem R141335 : Reach 141335 := rs (se 1 (by rfl) ⟨106001, by rfl⟩) R212003
theorem R43031 : Reach 43031 := rs (se 1 (by rfl) ⟨32273, by rfl⟩) R64547
theorem R75851 : Reach 75851 := rs (se 1 (by rfl) ⟨56888, by rfl⟩) R113777
theorem R76121 : Reach 76121 := rs (se 2 (by rfl) ⟨28545, by rfl⟩) R57091
theorem R76211 : Reach 76211 := rs (se 1 (by rfl) ⟨57158, by rfl⟩) R114317
theorem R109079 : Reach 109079 := rs (se 1 (by rfl) ⟨81809, by rfl⟩) R163619
theorem R76481 : Reach 76481 := rs (se 2 (by rfl) ⟨28680, by rfl⟩) R57361
theorem R43735 : Reach 43735 := rs (se 1 (by rfl) ⟨32801, by rfl⟩) R65603
theorem R43993 : Reach 43993 := rs (se 2 (by rfl) ⟨16497, by rfl⟩) R32995
theorem R175121 : Reach 175121 := rs (se 2 (by rfl) ⟨65670, by rfl⟩) R131341
theorem R76823 : Reach 76823 := rs (se 1 (by rfl) ⟨57617, by rfl⟩) R115235
theorem R109619 : Reach 109619 := rs (se 1 (by rfl) ⟨82214, by rfl⟩) R164429
theorem R175283 : Reach 175283 := rs (se 1 (by rfl) ⟨131462, by rfl⟩) R262925
theorem R77003 : Reach 77003 := rs (se 1 (by rfl) ⟨57752, by rfl⟩) R115505
theorem R109889 : Reach 109889 := rs (se 2 (by rfl) ⟨41208, by rfl⟩) R82417
theorem R404837 : Reach 404837 := rs (se 4 (by rfl) ⟨37953, by rfl⟩) R75907
theorem R77273 : Reach 77273 := rs (se 2 (by rfl) ⟨28977, by rfl⟩) R57955
theorem R77363 : Reach 77363 := rs (se 1 (by rfl) ⟨58022, by rfl⟩) R116045
theorem R110231 : Reach 110231 := rs (se 1 (by rfl) ⟨82673, by rfl⟩) R165347
theorem R77633 : Reach 77633 := rs (se 2 (by rfl) ⟨29112, by rfl⟩) R58225
theorem R110429 : Reach 110429 := rs (se 3 (by rfl) ⟨20705, by rfl⟩) R41411
theorem R241501 : Reach 241501 := rs (se 3 (by rfl) ⟨45281, by rfl⟩) R90563
theorem R77771 : Reach 77771 := rs (se 1 (by rfl) ⟨58328, by rfl⟩) R116657
theorem R77975 : Reach 77975 := rs (se 1 (by rfl) ⟨58481, by rfl⟩) R116963
theorem R241937 : Reach 241937 := rs (se 2 (by rfl) ⟨90726, by rfl⟩) R181453
theorem R110899 : Reach 110899 := rs (se 1 (by rfl) ⟨83174, by rfl⟩) R166349
theorem R78155 : Reach 78155 := rs (se 1 (by rfl) ⟨58616, by rfl⟩) R117233
theorem R45451 : Reach 45451 := rs (se 1 (by rfl) ⟨34088, by rfl⟩) R68177
theorem R143795 : Reach 143795 := rs (se 1 (by rfl) ⟨107846, by rfl⟩) R215693
theorem R111127 : Reach 111127 := rs (se 1 (by rfl) ⟨83345, by rfl⟩) R166691
theorem R78425 : Reach 78425 := rs (se 2 (by rfl) ⟨29409, by rfl⟩) R58819
theorem R176741 : Reach 176741 := rs (se 4 (by rfl) ⟨16569, by rfl⟩) R33139
theorem R209587 : Reach 209587 := rs (se 1 (by rfl) ⟨157190, by rfl⟩) R314381
theorem R78515 : Reach 78515 := rs (se 1 (by rfl) ⟨58886, by rfl⟩) R117773
theorem R45785 : Reach 45785 := rs (se 2 (by rfl) ⟨17169, by rfl⟩) R34339
theorem R78785 : Reach 78785 := rs (se 2 (by rfl) ⟨29544, by rfl⟩) R59089
theorem R111563 : Reach 111563 := rs (se 1 (by rfl) ⟨83672, by rfl⟩) R167345
theorem R177227 : Reach 177227 := rs (se 1 (by rfl) ⟨132920, by rfl⟩) R265841
theorem R799895 : Reach 799895 := rs (se 1 (by rfl) ⟨599921, by rfl⟩) R1199843
theorem R111833 : Reach 111833 := rs (se 2 (by rfl) ⟨41937, by rfl⟩) R83875
theorem R79127 : Reach 79127 := rs (se 1 (by rfl) ⟨59345, by rfl⟩) R118691
theorem R111947 : Reach 111947 := rs (se 1 (by rfl) ⟨83960, by rfl⟩) R167921
theorem R46423 : Reach 46423 := rs (se 1 (by rfl) ⟨34817, by rfl⟩) R69635
theorem R46489 : Reach 46489 := rs (se 2 (by rfl) ⟨17433, by rfl⟩) R34867
theorem R112151 : Reach 112151 := rs (se 1 (by rfl) ⟨84113, by rfl⟩) R168227
theorem R505379 : Reach 505379 := rs (se 1 (by rfl) ⟨379034, by rfl⟩) R758069
theorem R46679 : Reach 46679 := rs (se 1 (by rfl) ⟨35009, by rfl⟩) R70019
theorem R341597 : Reach 341597 := rs (se 3 (by rfl) ⟨64049, by rfl⟩) R128099
theorem R46745 : Reach 46745 := rs (se 2 (by rfl) ⟨17529, by rfl⟩) R35059
theorem R46859 : Reach 46859 := rs (se 1 (by rfl) ⟨35144, by rfl⟩) R70289
theorem R46871 : Reach 46871 := rs (se 1 (by rfl) ⟨35153, by rfl⟩) R70307
theorem R46937 : Reach 46937 := rs (se 2 (by rfl) ⟨17601, by rfl⟩) R35203
theorem R178013 : Reach 178013 := rs (se 3 (by rfl) ⟨33377, by rfl⟩) R66755
theorem R145297 : Reach 145297 := rs (se 2 (by rfl) ⟨54486, by rfl⟩) R108973
theorem R112535 : Reach 112535 := rs (se 1 (by rfl) ⟨84401, by rfl⟩) R168803
theorem R374705 : Reach 374705 := rs (se 2 (by rfl) ⟨140514, by rfl⟩) R281029
theorem R47051 : Reach 47051 := rs (se 1 (by rfl) ⟨35288, by rfl⟩) R70577
theorem R47063 : Reach 47063 := rs (se 1 (by rfl) ⟨35297, by rfl⟩) R70595
theorem R112643 : Reach 112643 := rs (se 1 (by rfl) ⟨84482, by rfl⟩) R168965
theorem R47129 : Reach 47129 := rs (se 2 (by rfl) ⟨17673, by rfl⟩) R35347
theorem R79937 : Reach 79937 := rs (se 2 (by rfl) ⟨29976, by rfl⟩) R59953
theorem R79961 : Reach 79961 := rs (se 2 (by rfl) ⟨29985, by rfl⟩) R59971
theorem R47243 : Reach 47243 := rs (se 1 (by rfl) ⟨35432, by rfl⟩) R70865
theorem R47255 : Reach 47255 := rs (se 1 (by rfl) ⟨35441, by rfl⟩) R70883
theorem R47321 : Reach 47321 := rs (se 2 (by rfl) ⟨17745, by rfl⟩) R35491
theorem R112913 : Reach 112913 := rs (se 2 (by rfl) ⟨42342, by rfl⟩) R84685
theorem R145709 : Reach 145709 := rs (se 3 (by rfl) ⟨27320, by rfl⟩) R54641
theorem R47435 : Reach 47435 := rs (se 1 (by rfl) ⟨35576, by rfl⟩) R71153
theorem R47447 : Reach 47447 := rs (se 1 (by rfl) ⟨35585, by rfl⟩) R71171
theorem R47513 : Reach 47513 := rs (se 2 (by rfl) ⟨17817, by rfl⟩) R35635
theorem R113075 : Reach 113075 := rs (se 1 (by rfl) ⟨84806, by rfl⟩) R169613
theorem R47627 : Reach 47627 := rs (se 1 (by rfl) ⟨35720, by rfl⟩) R71441
theorem R47639 : Reach 47639 := rs (se 1 (by rfl) ⟨35729, by rfl⟩) R71459
theorem R80473 : Reach 80473 := rs (se 2 (by rfl) ⟨30177, by rfl⟩) R60355
theorem R47705 : Reach 47705 := rs (se 2 (by rfl) ⟨17889, by rfl⟩) R35779
theorem R113345 : Reach 113345 := rs (se 2 (by rfl) ⟨42504, by rfl⟩) R85009
theorem R47819 : Reach 47819 := rs (se 1 (by rfl) ⟨35864, by rfl⟩) R71729
theorem R47831 : Reach 47831 := rs (se 1 (by rfl) ⟨35873, by rfl⟩) R71747
theorem R211729 : Reach 211729 := rs (se 2 (by rfl) ⟨79398, by rfl⟩) R158797
theorem R47897 : Reach 47897 := rs (se 2 (by rfl) ⟨17961, by rfl⟩) R35923
theorem R113453 : Reach 113453 := rs (se 3 (by rfl) ⟨21272, by rfl⟩) R42545
theorem R48011 : Reach 48011 := rs (se 1 (by rfl) ⟨36008, by rfl⟩) R72017
theorem R48023 : Reach 48023 := rs (se 1 (by rfl) ⟨36017, by rfl⟩) R72035
theorem R48089 : Reach 48089 := rs (se 2 (by rfl) ⟨18033, by rfl⟩) R36067
theorem R146393 : Reach 146393 := rs (se 2 (by rfl) ⟨54897, by rfl⟩) R109795
theorem R48203 : Reach 48203 := rs (se 1 (by rfl) ⟨36152, by rfl⟩) R72305
theorem R48215 : Reach 48215 := rs (se 1 (by rfl) ⟨36161, by rfl⟩) R72323
theorem R48217 : Reach 48217 := rs (se 2 (by rfl) ⟨18081, by rfl⟩) R36163
theorem R48281 : Reach 48281 := rs (se 2 (by rfl) ⟨18105, by rfl⟩) R36211
theorem R113885 : Reach 113885 := rs (se 3 (by rfl) ⟨21353, by rfl⟩) R42707
theorem R48395 : Reach 48395 := rs (se 1 (by rfl) ⟨36296, by rfl⟩) R72593
theorem R48407 : Reach 48407 := rs (se 1 (by rfl) ⟨36305, by rfl⟩) R72611
theorem R146777 : Reach 146777 := rs (se 2 (by rfl) ⟨55041, by rfl⟩) R110083
theorem R48473 : Reach 48473 := rs (se 2 (by rfl) ⟨18177, by rfl⟩) R36355
theorem R48587 : Reach 48587 := rs (se 1 (by rfl) ⟨36440, by rfl⟩) R72881
theorem R48599 : Reach 48599 := rs (se 1 (by rfl) ⟨36449, by rfl⟩) R72899
theorem R48665 : Reach 48665 := rs (se 2 (by rfl) ⟨18249, by rfl⟩) R36499
theorem R48779 : Reach 48779 := rs (se 1 (by rfl) ⟨36584, by rfl⟩) R73169
theorem R48791 : Reach 48791 := rs (se 1 (by rfl) ⟨36593, by rfl⟩) R73187
theorem R81587 : Reach 81587 := rs (se 1 (by rfl) ⟨61190, by rfl⟩) R122381
theorem R48857 : Reach 48857 := rs (se 2 (by rfl) ⟨18321, by rfl⟩) R36643
theorem R48971 : Reach 48971 := rs (se 1 (by rfl) ⟨36728, by rfl⟩) R73457
theorem R48983 : Reach 48983 := rs (se 1 (by rfl) ⟨36737, by rfl⟩) R73475
theorem R49049 : Reach 49049 := rs (se 2 (by rfl) ⟨18393, by rfl⟩) R36787
theorem R81881 : Reach 81881 := rs (se 2 (by rfl) ⟨30705, by rfl⟩) R61411
theorem R49163 : Reach 49163 := rs (se 1 (by rfl) ⟨36872, by rfl⟩) R73745
theorem R49175 : Reach 49175 := rs (se 1 (by rfl) ⟨36881, by rfl⟩) R73763
theorem R147521 : Reach 147521 := rs (se 2 (by rfl) ⟨55320, by rfl⟩) R110641
theorem R49241 : Reach 49241 := rs (se 2 (by rfl) ⟨18465, by rfl⟩) R36931
theorem R49355 : Reach 49355 := rs (se 1 (by rfl) ⟨37016, by rfl⟩) R74033
theorem R49367 : Reach 49367 := rs (se 1 (by rfl) ⟨37025, by rfl⟩) R74051
theorem R49433 : Reach 49433 := rs (se 2 (by rfl) ⟨18537, by rfl⟩) R37075
theorem R115019 : Reach 115019 := rs (se 1 (by rfl) ⟨86264, by rfl⟩) R172529
theorem R49547 : Reach 49547 := rs (se 1 (by rfl) ⟨37160, by rfl⟩) R74321
theorem R49559 : Reach 49559 := rs (se 1 (by rfl) ⟨37169, by rfl⟩) R74339
theorem R49625 : Reach 49625 := rs (se 2 (by rfl) ⟨18609, by rfl⟩) R37219
theorem R49675 : Reach 49675 := rs (se 1 (by rfl) ⟨37256, by rfl⟩) R74513
theorem R49739 : Reach 49739 := rs (se 1 (by rfl) ⟨37304, by rfl⟩) R74609
theorem R246347 : Reach 246347 := rs (se 1 (by rfl) ⟨184760, by rfl⟩) R369521
theorem R49751 : Reach 49751 := rs (se 1 (by rfl) ⟨37313, by rfl⟩) R74627
theorem R115289 : Reach 115289 := rs (se 2 (by rfl) ⟨43233, by rfl⟩) R86467
theorem R49817 : Reach 49817 := rs (se 2 (by rfl) ⟨18681, by rfl⟩) R37363
theorem R180953 : Reach 180953 := rs (se 2 (by rfl) ⟨67857, by rfl⟩) R135715
theorem R49931 : Reach 49931 := rs (se 1 (by rfl) ⟨37448, by rfl⟩) R74897
theorem R49943 : Reach 49943 := rs (se 1 (by rfl) ⟨37457, by rfl⟩) R74915
theorem R82763 : Reach 82763 := rs (se 1 (by rfl) ⟨62072, by rfl⟩) R124145
theorem R50009 : Reach 50009 := rs (se 2 (by rfl) ⟨18753, by rfl⟩) R37507
theorem R279389 : Reach 279389 := rs (se 3 (by rfl) ⟨52385, by rfl⟩) R104771
theorem R50123 : Reach 50123 := rs (se 1 (by rfl) ⟨37592, by rfl⟩) R75185
theorem R50135 : Reach 50135 := rs (se 1 (by rfl) ⟨37601, by rfl⟩) R75203
theorem R115715 : Reach 115715 := rs (se 1 (by rfl) ⟨86786, by rfl⟩) R173573
theorem R50201 : Reach 50201 := rs (se 2 (by rfl) ⟨18825, by rfl⟩) R37651
theorem R50315 : Reach 50315 := rs (se 1 (by rfl) ⟨37736, by rfl⟩) R75473
theorem R50327 : Reach 50327 := rs (se 1 (by rfl) ⟨37745, by rfl⟩) R75491
theorem R50393 : Reach 50393 := rs (se 2 (by rfl) ⟨18897, by rfl⟩) R37795
theorem R115991 : Reach 115991 := rs (se 1 (by rfl) ⟨86993, by rfl⟩) R173987
theorem R50507 : Reach 50507 := rs (se 1 (by rfl) ⟨37880, by rfl⟩) R75761
theorem R50519 : Reach 50519 := rs (se 1 (by rfl) ⟨37889, by rfl⟩) R75779
theorem R116099 : Reach 116099 := rs (se 1 (by rfl) ⟨87074, by rfl⟩) R174149
theorem R50585 : Reach 50585 := rs (se 2 (by rfl) ⟨18969, by rfl⟩) R37939
theorem R50699 : Reach 50699 := rs (se 1 (by rfl) ⟨38024, by rfl⟩) R76049
theorem R50711 : Reach 50711 := rs (se 1 (by rfl) ⟨38033, by rfl⟩) R76067
theorem R83531 : Reach 83531 := rs (se 1 (by rfl) ⟨62648, by rfl⟩) R125297
theorem R50777 : Reach 50777 := rs (se 2 (by rfl) ⟨19041, by rfl⟩) R38083
theorem R116369 : Reach 116369 := rs (se 2 (by rfl) ⟨43638, by rfl⟩) R87277
theorem R50891 : Reach 50891 := rs (se 1 (by rfl) ⟨38168, by rfl⟩) R76337
theorem R50903 : Reach 50903 := rs (se 1 (by rfl) ⟨38177, by rfl⟩) R76355
theorem R50969 : Reach 50969 := rs (se 2 (by rfl) ⟨19113, by rfl⟩) R38227
theorem R116531 : Reach 116531 := rs (se 1 (by rfl) ⟨87398, by rfl⟩) R174797
theorem R51083 : Reach 51083 := rs (se 1 (by rfl) ⟨38312, by rfl⟩) R76625
theorem R51095 : Reach 51095 := rs (se 1 (by rfl) ⟨38321, by rfl⟩) R76643
theorem R51161 : Reach 51161 := rs (se 2 (by rfl) ⟨19185, by rfl⟩) R38371
theorem R116801 : Reach 116801 := rs (se 2 (by rfl) ⟨43800, by rfl⟩) R87601
theorem R968773 : Reach 968773 := rs (se 4 (by rfl) ⟨90822, by rfl⟩) R181645
theorem R51275 : Reach 51275 := rs (se 1 (by rfl) ⟨38456, by rfl⟩) R76913
theorem R51287 : Reach 51287 := rs (se 1 (by rfl) ⟨38465, by rfl⟩) R76931
theorem R247901 : Reach 247901 := rs (se 3 (by rfl) ⟨46481, by rfl⟩) R92963
theorem R51353 : Reach 51353 := rs (se 2 (by rfl) ⟨19257, by rfl⟩) R38515
theorem R116909 : Reach 116909 := rs (se 3 (by rfl) ⟨21920, by rfl⟩) R43841
theorem R51467 : Reach 51467 := rs (se 1 (by rfl) ⟨38600, by rfl⟩) R77201
theorem R51479 : Reach 51479 := rs (se 1 (by rfl) ⟨38609, by rfl⟩) R77219
theorem R51545 : Reach 51545 := rs (se 2 (by rfl) ⟨19329, by rfl⟩) R38659
theorem R51659 : Reach 51659 := rs (se 1 (by rfl) ⟨38744, by rfl⟩) R77489
theorem R51671 : Reach 51671 := rs (se 1 (by rfl) ⟨38753, by rfl⟩) R77507
theorem R84503 : Reach 84503 := rs (se 1 (by rfl) ⟨63377, by rfl⟩) R126755
theorem R51737 : Reach 51737 := rs (se 2 (by rfl) ⟨19401, by rfl⟩) R38803
theorem R117341 : Reach 117341 := rs (se 3 (by rfl) ⟨22001, by rfl⟩) R44003
theorem R51851 : Reach 51851 := rs (se 1 (by rfl) ⟨38888, by rfl⟩) R77777
theorem R51863 : Reach 51863 := rs (se 1 (by rfl) ⟨38897, by rfl⟩) R77795
theorem R51929 : Reach 51929 := rs (se 2 (by rfl) ⟨19473, by rfl⟩) R38947
theorem R52043 : Reach 52043 := rs (se 1 (by rfl) ⟨39032, by rfl⟩) R78065
theorem R52055 : Reach 52055 := rs (se 1 (by rfl) ⟨39041, by rfl⟩) R78083
theorem R84829 : Reach 84829 := rs (se 3 (by rfl) ⟨15905, by rfl⟩) R31811
theorem R52121 : Reach 52121 := rs (se 2 (by rfl) ⟨19545, by rfl⟩) R39091
theorem R52235 : Reach 52235 := rs (se 1 (by rfl) ⟨39176, by rfl⟩) R78353
theorem R52247 : Reach 52247 := rs (se 1 (by rfl) ⟨39185, by rfl⟩) R78371
theorem R52313 : Reach 52313 := rs (se 2 (by rfl) ⟨19617, by rfl⟩) R39235
theorem R85171 : Reach 85171 := rs (se 1 (by rfl) ⟨63878, by rfl⟩) R127757
theorem R52427 : Reach 52427 := rs (se 1 (by rfl) ⟨39320, by rfl⟩) R78641
theorem R52439 : Reach 52439 := rs (se 1 (by rfl) ⟨39329, by rfl⟩) R78659
theorem R52505 : Reach 52505 := rs (se 2 (by rfl) ⟨19689, by rfl⟩) R39379
theorem R183617 : Reach 183617 := rs (se 2 (by rfl) ⟨68856, by rfl⟩) R137713
theorem R85313 : Reach 85313 := rs (se 2 (by rfl) ⟨31992, by rfl⟩) R63985
theorem R52555 : Reach 52555 := rs (se 1 (by rfl) ⟨39416, by rfl⟩) R78833
theorem R281987 : Reach 281987 := rs (se 1 (by rfl) ⟨211490, by rfl⟩) R422981
theorem R52619 : Reach 52619 := rs (se 1 (by rfl) ⟨39464, by rfl⟩) R78929
theorem R52631 : Reach 52631 := rs (se 1 (by rfl) ⟨39473, by rfl⟩) R78947
theorem R118219 : Reach 118219 := rs (se 1 (by rfl) ⟨88664, by rfl⟩) R177329
theorem R52697 : Reach 52697 := rs (se 2 (by rfl) ⟨19761, by rfl⟩) R39523
theorem R151085 : Reach 151085 := rs (se 3 (by rfl) ⟨28328, by rfl⟩) R56657
theorem R347723 : Reach 347723 := rs (se 1 (by rfl) ⟨260792, by rfl⟩) R521585
theorem R52825 : Reach 52825 := rs (se 2 (by rfl) ⟨19809, by rfl⟩) R39619
theorem R118361 : Reach 118361 := rs (se 2 (by rfl) ⟨44385, by rfl⟩) R88771
theorem R118417 : Reach 118417 := rs (se 2 (by rfl) ⟨44406, by rfl⟩) R88813
theorem R216755 : Reach 216755 := rs (se 1 (by rfl) ⟨162566, by rfl⟩) R325133
theorem R118475 : Reach 118475 := rs (se 1 (by rfl) ⟨88856, by rfl⟩) R177713
theorem R118493 : Reach 118493 := rs (se 3 (by rfl) ⟨22217, by rfl⟩) R44435
theorem R151313 : Reach 151313 := rs (se 2 (by rfl) ⟨56742, by rfl⟩) R113485
theorem R85981 : Reach 85981 := rs (se 3 (by rfl) ⟨16121, by rfl⟩) R32243
theorem R217181 : Reach 217181 := rs (se 3 (by rfl) ⟨40721, by rfl⟩) R81443
theorem R53399 : Reach 53399 := rs (se 1 (by rfl) ⟨40049, by rfl⟩) R80099
theorem R53527 : Reach 53527 := rs (se 1 (by rfl) ⟨40145, by rfl⟩) R80291
theorem R119191 : Reach 119191 := rs (se 1 (by rfl) ⟨89393, by rfl⟩) R178787
theorem R250289 : Reach 250289 := rs (se 2 (by rfl) ⟨93858, by rfl⟩) R187717
theorem R86579 : Reach 86579 := rs (se 1 (by rfl) ⟨64934, by rfl⟩) R129869
theorem R184933 : Reach 184933 := rs (se 4 (by rfl) ⟨17337, by rfl⟩) R34675
theorem R53975 : Reach 53975 := rs (se 1 (by rfl) ⟨40481, by rfl⟩) R80963
theorem R54103 : Reach 54103 := rs (se 1 (by rfl) ⟨40577, by rfl⟩) R81155
theorem R54155 : Reach 54155 := rs (se 1 (by rfl) ⟨40616, by rfl⟩) R81233
theorem R250775 : Reach 250775 := rs (se 1 (by rfl) ⟨188081, by rfl⟩) R376163
theorem R54283 : Reach 54283 := rs (se 1 (by rfl) ⟨40712, by rfl⟩) R81425
theorem R87115 : Reach 87115 := rs (se 1 (by rfl) ⟨65336, by rfl⟩) R130673
theorem R316547 : Reach 316547 := rs (se 1 (by rfl) ⟨237410, by rfl⟩) R474821
theorem R54425 : Reach 54425 := rs (se 2 (by rfl) ⟨20409, by rfl⟩) R40819
theorem R119981 : Reach 119981 := rs (se 3 (by rfl) ⟨22496, by rfl⟩) R44993
theorem R87257 : Reach 87257 := rs (se 2 (by rfl) ⟨32721, by rfl⟩) R65443
theorem R54553 : Reach 54553 := rs (se 2 (by rfl) ⟨20457, by rfl⟩) R40915
theorem R87389 : Reach 87389 := rs (se 3 (by rfl) ⟨16385, by rfl⟩) R32771
theorem R54923 : Reach 54923 := rs (se 1 (by rfl) ⟨41192, by rfl⟩) R82385
theorem R55127 : Reach 55127 := rs (se 1 (by rfl) ⟨41345, by rfl⟩) R82691
theorem R55255 : Reach 55255 := rs (se 1 (by rfl) ⟨41441, by rfl⟩) R82883
theorem R88087 : Reach 88087 := rs (se 1 (by rfl) ⟨66065, by rfl⟩) R132131
theorem R55475 : Reach 55475 := rs (se 1 (by rfl) ⟨41606, by rfl⟩) R83213
theorem R55667 : Reach 55667 := rs (se 1 (by rfl) ⟨41750, by rfl⟩) R83501
theorem R154007 : Reach 154007 := rs (se 1 (by rfl) ⟨115505, by rfl⟩) R231011
theorem R88523 : Reach 88523 := rs (se 1 (by rfl) ⟨66392, by rfl⟩) R132785
theorem R55795 : Reach 55795 := rs (se 1 (by rfl) ⟨41846, by rfl⟩) R83693
theorem R121409 : Reach 121409 := rs (se 2 (by rfl) ⟨45528, by rfl⟩) R91057
theorem R88651 : Reach 88651 := rs (se 1 (by rfl) ⟨66488, by rfl⟩) R132977
theorem R55883 : Reach 55883 := rs (se 1 (by rfl) ⟨41912, by rfl⟩) R83825
theorem R55937 : Reach 55937 := rs (se 2 (by rfl) ⟨20976, by rfl⟩) R41953
theorem R56011 : Reach 56011 := rs (se 1 (by rfl) ⟨42008, by rfl⟩) R84017
theorem R56065 : Reach 56065 := rs (se 2 (by rfl) ⟨21024, by rfl⟩) R42049
theorem R1334069 : Reach 1334069 := rs (se 5 (by rfl) ⟨62534, by rfl⟩) R125069
theorem R121675 : Reach 121675 := rs (se 1 (by rfl) ⟨91256, by rfl⟩) R182513
theorem R56153 : Reach 56153 := rs (se 2 (by rfl) ⟨21057, by rfl⟩) R42115
theorem R56281 : Reach 56281 := rs (se 2 (by rfl) ⟨21105, by rfl⟩) R42211
theorem R56435 : Reach 56435 := rs (se 1 (by rfl) ⟨42326, by rfl⟩) R84653
theorem R56855 : Reach 56855 := rs (se 1 (by rfl) ⟨42641, by rfl⟩) R85283
theorem R56983 : Reach 56983 := rs (se 1 (by rfl) ⟨42737, by rfl⟩) R85475
theorem R57089 : Reach 57089 := rs (se 2 (by rfl) ⟨21408, by rfl⟩) R42817
theorem R122627 : Reach 122627 := rs (se 1 (by rfl) ⟨91970, by rfl⟩) R183941
theorem R122897 : Reach 122897 := rs (se 2 (by rfl) ⟨46086, by rfl⟩) R92173
theorem R57395 : Reach 57395 := rs (se 1 (by rfl) ⟨43046, by rfl⟩) R86093
theorem R57523 : Reach 57523 := rs (se 1 (by rfl) ⟨43142, by rfl⟩) R86285
theorem R90305 : Reach 90305 := rs (se 2 (by rfl) ⟨33864, by rfl⟩) R67729
theorem R57611 : Reach 57611 := rs (se 1 (by rfl) ⟨43208, by rfl⟩) R86417
theorem R90391 : Reach 90391 := rs (se 1 (by rfl) ⟨67793, by rfl⟩) R135587
theorem R57665 : Reach 57665 := rs (se 2 (by rfl) ⟨21624, by rfl⟩) R43249
theorem R57739 : Reach 57739 := rs (se 1 (by rfl) ⟨43304, by rfl⟩) R86609
theorem R57793 : Reach 57793 := rs (se 2 (by rfl) ⟨21672, by rfl⟩) R43345
theorem R123353 : Reach 123353 := rs (se 2 (by rfl) ⟨46257, by rfl⟩) R92515
theorem R57881 : Reach 57881 := rs (se 2 (by rfl) ⟨21705, by rfl⟩) R43411
theorem R188993 : Reach 188993 := rs (se 2 (by rfl) ⟨70872, by rfl⟩) R141745
theorem R58009 : Reach 58009 := rs (se 2 (by rfl) ⟨21753, by rfl⟩) R43507
theorem R123565 : Reach 123565 := rs (se 3 (by rfl) ⟨23168, by rfl⟩) R46337
theorem R90841 : Reach 90841 := rs (se 2 (by rfl) ⟨34065, by rfl⟩) R68131
theorem R1008449 : Reach 1008449 := rs (se 2 (by rfl) ⟨378168, by rfl⟩) R756337
theorem R58315 : Reach 58315 := rs (se 1 (by rfl) ⟨43736, by rfl⟩) R87473
theorem R123869 : Reach 123869 := rs (se 3 (by rfl) ⟨23225, by rfl⟩) R46451
theorem R2057237 : Reach 2057237 := rs (se 6 (by rfl) ⟨48216, by rfl⟩) R96433
theorem R58583 : Reach 58583 := rs (se 1 (by rfl) ⟨43937, by rfl⟩) R87875
theorem R124211 : Reach 124211 := rs (se 1 (by rfl) ⟨93158, by rfl⟩) R186317
theorem R386369 : Reach 386369 := rs (se 2 (by rfl) ⟨144888, by rfl⟩) R289777
theorem R58711 : Reach 58711 := rs (se 1 (by rfl) ⟨44033, by rfl⟩) R88067
theorem R59123 : Reach 59123 := rs (se 1 (by rfl) ⟨44342, by rfl⟩) R88685
theorem R91955 : Reach 91955 := rs (se 1 (by rfl) ⟨68966, by rfl⟩) R137933
theorem R59201 : Reach 59201 := rs (se 2 (by rfl) ⟨22200, by rfl⟩) R44401
theorem R59251 : Reach 59251 := rs (se 1 (by rfl) ⟨44438, by rfl⟩) R88877
theorem R157619 : Reach 157619 := rs (se 1 (by rfl) ⟨118214, by rfl⟩) R236429
theorem R59467 : Reach 59467 := rs (se 1 (by rfl) ⟨44600, by rfl⟩) R89201
theorem R583861 : Reach 583861 := rs (se 5 (by rfl) ⟨27368, by rfl⟩) R54737
theorem R223523 : Reach 223523 := rs (se 1 (by rfl) ⟨167642, by rfl⟩) R335285
theorem R59699 : Reach 59699 := rs (se 1 (by rfl) ⟨44774, by rfl⟩) R89549
theorem R223667 : Reach 223667 := rs (se 1 (by rfl) ⟨167750, by rfl⟩) R335501
theorem R59915 : Reach 59915 := rs (se 1 (by rfl) ⟨44936, by rfl⟩) R89873
theorem R256547 : Reach 256547 := rs (se 1 (by rfl) ⟨192410, by rfl⟩) R384821
theorem R158273 : Reach 158273 := rs (se 2 (by rfl) ⟨59352, by rfl⟩) R118705
theorem R92765 : Reach 92765 := rs (se 3 (by rfl) ⟨17393, by rfl⟩) R34787
theorem R60097 : Reach 60097 := rs (se 2 (by rfl) ⟨22536, by rfl⟩) R45073
theorem R322309 : Reach 322309 := rs (se 4 (by rfl) ⟨30216, by rfl⟩) R60433
theorem R60439 : Reach 60439 := rs (se 1 (by rfl) ⟨45329, by rfl⟩) R90659
theorem R60659 : Reach 60659 := rs (se 1 (by rfl) ⟨45494, by rfl⟩) R90989
theorem R945413 : Reach 945413 := rs (se 4 (by rfl) ⟨88632, by rfl⟩) R177265
theorem R60887 : Reach 60887 := rs (se 1 (by rfl) ⟨45665, by rfl⟩) R91331
theorem R126467 : Reach 126467 := rs (se 1 (by rfl) ⟨94850, by rfl⟩) R189701
theorem R126481 : Reach 126481 := rs (se 2 (by rfl) ⟨47430, by rfl⟩) R94861
theorem R585251 : Reach 585251 := rs (se 1 (by rfl) ⟨438938, by rfl⟩) R877877
theorem R192131 : Reach 192131 := rs (se 1 (by rfl) ⟨144098, by rfl⟩) R288197
theorem R93847 : Reach 93847 := rs (se 1 (by rfl) ⟨70385, by rfl⟩) R140771
theorem R454349 : Reach 454349 := rs (se 3 (by rfl) ⟨85190, by rfl⟩) R170381
theorem R61145 : Reach 61145 := rs (se 2 (by rfl) ⟨22929, by rfl⟩) R45859
theorem R126785 : Reach 126785 := rs (se 2 (by rfl) ⟨47544, by rfl⟩) R95089
theorem R258065 : Reach 258065 := rs (se 2 (by rfl) ⟨96774, by rfl⟩) R193549
theorem R61555 : Reach 61555 := rs (se 1 (by rfl) ⟨46166, by rfl⟩) R92333
theorem R160217 : Reach 160217 := rs (se 2 (by rfl) ⟨60081, by rfl⟩) R120163
theorem R127453 : Reach 127453 := rs (se 3 (by rfl) ⟨23897, by rfl⟩) R47795
theorem R62041 : Reach 62041 := rs (se 2 (by rfl) ⟨23265, by rfl⟩) R46531
theorem R127837 : Reach 127837 := rs (se 3 (by rfl) ⟨23969, by rfl⟩) R47939
theorem R291761 : Reach 291761 := rs (se 2 (by rfl) ⟨109410, by rfl⟩) R218821
theorem R226253 : Reach 226253 := rs (se 3 (by rfl) ⟨42422, by rfl⟩) R84845
theorem R62603 : Reach 62603 := rs (se 1 (by rfl) ⟨46952, by rfl⟩) R93905
theorem R161041 : Reach 161041 := rs (se 2 (by rfl) ⟨60390, by rfl⟩) R120781
theorem R62785 : Reach 62785 := rs (se 2 (by rfl) ⟨23544, by rfl⟩) R47089
theorem R325043 : Reach 325043 := rs (se 1 (by rfl) ⟨243782, by rfl⟩) R487565
theorem R95681 : Reach 95681 := rs (se 2 (by rfl) ⟨35880, by rfl⟩) R71761
theorem R95705 : Reach 95705 := rs (se 2 (by rfl) ⟨35889, by rfl⟩) R71779
theorem R128729 : Reach 128729 := rs (se 2 (by rfl) ⟨48273, by rfl⟩) R96547
theorem R522101 : Reach 522101 := rs (se 5 (by rfl) ⟨24473, by rfl⟩) R48947
theorem R63499 : Reach 63499 := rs (se 1 (by rfl) ⟨47624, by rfl⟩) R95249
theorem R161837 : Reach 161837 := rs (se 3 (by rfl) ⟨30344, by rfl⟩) R60689
theorem R63575 : Reach 63575 := rs (se 1 (by rfl) ⟨47681, by rfl⟩) R95363
theorem R31115 : Reach 31115 := rs (se 1 (by rfl) ⟨23336, by rfl⟩) R46673
theorem R31127 : Reach 31127 := rs (se 1 (by rfl) ⟨23345, by rfl⟩) R46691
theorem R31147 : Reach 31147 := rs (se 1 (by rfl) ⟨23360, by rfl⟩) R46721
theorem R31159 : Reach 31159 := rs (se 1 (by rfl) ⟨23369, by rfl⟩) R46739
theorem R31179 : Reach 31179 := rs (se 1 (by rfl) ⟨23384, by rfl⟩) R46769
theorem R31191 : Reach 31191 := rs (se 1 (by rfl) ⟨23393, by rfl⟩) R46787
theorem R31211 : Reach 31211 := rs (se 1 (by rfl) ⟨23408, by rfl⟩) R46817
theorem R31223 : Reach 31223 := rs (se 1 (by rfl) ⟨23417, by rfl⟩) R46835
theorem R31243 : Reach 31243 := rs (se 1 (by rfl) ⟨23432, by rfl⟩) R46865
theorem R31255 : Reach 31255 := rs (se 1 (by rfl) ⟨23441, by rfl⟩) R46883
theorem R31275 : Reach 31275 := rs (se 1 (by rfl) ⟨23456, by rfl⟩) R46913
theorem R31287 : Reach 31287 := rs (se 1 (by rfl) ⟨23465, by rfl⟩) R46931
theorem R31307 : Reach 31307 := rs (se 1 (by rfl) ⟨23480, by rfl⟩) R46961
theorem R31319 : Reach 31319 := rs (se 1 (by rfl) ⟨23489, by rfl⟩) R46979
theorem R31339 : Reach 31339 := rs (se 1 (by rfl) ⟨23504, by rfl⟩) R47009
theorem R31351 : Reach 31351 := rs (se 1 (by rfl) ⟨23513, by rfl⟩) R47027
theorem R31371 : Reach 31371 := rs (se 1 (by rfl) ⟨23528, by rfl⟩) R47057
theorem R31383 : Reach 31383 := rs (se 1 (by rfl) ⟨23537, by rfl⟩) R47075
theorem R359063 : Reach 359063 := rs (se 1 (by rfl) ⟨269297, by rfl⟩) R538595
theorem R31403 : Reach 31403 := rs (se 1 (by rfl) ⟨23552, by rfl⟩) R47105
theorem R96947 : Reach 96947 := rs (se 1 (by rfl) ⟨72710, by rfl⟩) R145421
theorem R31415 : Reach 31415 := rs (se 1 (by rfl) ⟨23561, by rfl⟩) R47123
theorem R31435 : Reach 31435 := rs (se 1 (by rfl) ⟨23576, by rfl⟩) R47153
theorem R31447 : Reach 31447 := rs (se 1 (by rfl) ⟨23585, by rfl⟩) R47171
theorem R31467 : Reach 31467 := rs (se 1 (by rfl) ⟨23600, by rfl⟩) R47201
theorem R64243 : Reach 64243 := rs (se 1 (by rfl) ⟨48182, by rfl⟩) R96365
theorem R31479 : Reach 31479 := rs (se 1 (by rfl) ⟨23609, by rfl⟩) R47219
theorem R31499 : Reach 31499 := rs (se 1 (by rfl) ⟨23624, by rfl⟩) R47249
theorem R31511 : Reach 31511 := rs (se 1 (by rfl) ⟨23633, by rfl⟩) R47267
theorem R31531 : Reach 31531 := rs (se 1 (by rfl) ⟨23648, by rfl⟩) R47297
theorem R31543 : Reach 31543 := rs (se 1 (by rfl) ⟨23657, by rfl⟩) R47315
theorem R31563 : Reach 31563 := rs (se 1 (by rfl) ⟨23672, by rfl⟩) R47345
theorem R31575 : Reach 31575 := rs (se 1 (by rfl) ⟨23681, by rfl⟩) R47363
theorem R31595 : Reach 31595 := rs (se 1 (by rfl) ⟨23696, by rfl⟩) R47393
theorem R31607 : Reach 31607 := rs (se 1 (by rfl) ⟨23705, by rfl⟩) R47411
theorem R31627 : Reach 31627 := rs (se 1 (by rfl) ⟨23720, by rfl⟩) R47441
theorem R31639 : Reach 31639 := rs (se 1 (by rfl) ⟨23729, by rfl⟩) R47459
theorem R31659 : Reach 31659 := rs (se 1 (by rfl) ⟨23744, by rfl⟩) R47489
theorem R31671 : Reach 31671 := rs (se 1 (by rfl) ⟨23753, by rfl⟩) R47507
theorem R31691 : Reach 31691 := rs (se 1 (by rfl) ⟨23768, by rfl⟩) R47537
theorem R31703 : Reach 31703 := rs (se 1 (by rfl) ⟨23777, by rfl⟩) R47555
theorem R64471 : Reach 64471 := rs (se 1 (by rfl) ⟨48353, by rfl⟩) R96707
theorem R31723 : Reach 31723 := rs (se 1 (by rfl) ⟨23792, by rfl⟩) R47585
theorem R31735 : Reach 31735 := rs (se 1 (by rfl) ⟨23801, by rfl⟩) R47603
theorem R31755 : Reach 31755 := rs (se 1 (by rfl) ⟨23816, by rfl⟩) R47633
theorem R31767 : Reach 31767 := rs (se 1 (by rfl) ⟨23825, by rfl⟩) R47651
theorem R31787 : Reach 31787 := rs (se 1 (by rfl) ⟨23840, by rfl⟩) R47681
theorem R31799 : Reach 31799 := rs (se 1 (by rfl) ⟨23849, by rfl⟩) R47699
theorem R64577 : Reach 64577 := rs (se 2 (by rfl) ⟨24216, by rfl⟩) R48433
theorem R31819 : Reach 31819 := rs (se 1 (by rfl) ⟨23864, by rfl⟩) R47729
theorem R31831 : Reach 31831 := rs (se 1 (by rfl) ⟨23873, by rfl⟩) R47747
theorem R31851 : Reach 31851 := rs (se 1 (by rfl) ⟨23888, by rfl⟩) R47777
theorem R31863 : Reach 31863 := rs (se 1 (by rfl) ⟨23897, by rfl⟩) R47795
theorem R31883 : Reach 31883 := rs (se 1 (by rfl) ⟨23912, by rfl⟩) R47825
theorem R31895 : Reach 31895 := rs (se 1 (by rfl) ⟨23921, by rfl⟩) R47843
theorem R31915 : Reach 31915 := rs (se 1 (by rfl) ⟨23936, by rfl⟩) R47873
theorem R31927 : Reach 31927 := rs (se 1 (by rfl) ⟨23945, by rfl⟩) R47891
theorem R31947 : Reach 31947 := rs (se 1 (by rfl) ⟨23960, by rfl⟩) R47921
theorem R31959 : Reach 31959 := rs (se 1 (by rfl) ⟨23969, by rfl⟩) R47939
theorem R64729 : Reach 64729 := rs (se 2 (by rfl) ⟨24273, by rfl⟩) R48547
theorem R31979 : Reach 31979 := rs (se 1 (by rfl) ⟨23984, by rfl⟩) R47969
theorem R31991 : Reach 31991 := rs (se 1 (by rfl) ⟨23993, by rfl⟩) R47987
theorem R32011 : Reach 32011 := rs (se 1 (by rfl) ⟨24008, by rfl⟩) R48017
theorem R32023 : Reach 32023 := rs (se 1 (by rfl) ⟨24017, by rfl⟩) R48035
theorem R32043 : Reach 32043 := rs (se 1 (by rfl) ⟨24032, by rfl⟩) R48065
theorem R130355 : Reach 130355 := rs (se 1 (by rfl) ⟨97766, by rfl⟩) R195533
theorem R32055 : Reach 32055 := rs (se 1 (by rfl) ⟨24041, by rfl⟩) R48083
theorem R130369 : Reach 130369 := rs (se 2 (by rfl) ⟨48888, by rfl⟩) R97777
theorem R32075 : Reach 32075 := rs (se 1 (by rfl) ⟨24056, by rfl⟩) R48113
theorem R32087 : Reach 32087 := rs (se 1 (by rfl) ⟨24065, by rfl⟩) R48131
theorem R32107 : Reach 32107 := rs (se 1 (by rfl) ⟨24080, by rfl⟩) R48161
theorem R32119 : Reach 32119 := rs (se 1 (by rfl) ⟨24089, by rfl⟩) R48179
theorem R32139 : Reach 32139 := rs (se 1 (by rfl) ⟨24104, by rfl⟩) R48209
theorem R32151 : Reach 32151 := rs (se 1 (by rfl) ⟨24113, by rfl⟩) R48227
theorem R32171 : Reach 32171 := rs (se 1 (by rfl) ⟨24128, by rfl⟩) R48257
theorem R32183 : Reach 32183 := rs (se 1 (by rfl) ⟨24137, by rfl⟩) R48275
theorem R32203 : Reach 32203 := rs (se 1 (by rfl) ⟨24152, by rfl⟩) R48305
theorem R32215 : Reach 32215 := rs (se 1 (by rfl) ⟨24161, by rfl⟩) R48323
theorem R32235 : Reach 32235 := rs (se 1 (by rfl) ⟨24176, by rfl⟩) R48353
theorem R32247 : Reach 32247 := rs (se 1 (by rfl) ⟨24185, by rfl⟩) R48371
theorem R32267 : Reach 32267 := rs (se 1 (by rfl) ⟨24200, by rfl⟩) R48401
theorem R32279 : Reach 32279 := rs (se 1 (by rfl) ⟨24209, by rfl⟩) R48419
theorem R32299 : Reach 32299 := rs (se 1 (by rfl) ⟨24224, by rfl⟩) R48449
theorem R32311 : Reach 32311 := rs (se 1 (by rfl) ⟨24233, by rfl⟩) R48467
theorem R32331 : Reach 32331 := rs (se 1 (by rfl) ⟨24248, by rfl⟩) R48497
theorem R32343 : Reach 32343 := rs (se 1 (by rfl) ⟨24257, by rfl⟩) R48515
theorem R32363 : Reach 32363 := rs (se 1 (by rfl) ⟨24272, by rfl⟩) R48545
theorem R32375 : Reach 32375 := rs (se 1 (by rfl) ⟨24281, by rfl⟩) R48563
theorem R32395 : Reach 32395 := rs (se 1 (by rfl) ⟨24296, by rfl⟩) R48593
theorem R32407 : Reach 32407 := rs (se 1 (by rfl) ⟨24305, by rfl⟩) R48611
theorem R32427 : Reach 32427 := rs (se 1 (by rfl) ⟨24320, by rfl⟩) R48641
theorem R32439 : Reach 32439 := rs (se 1 (by rfl) ⟨24329, by rfl⟩) R48659
theorem R32459 : Reach 32459 := rs (se 1 (by rfl) ⟨24344, by rfl⟩) R48689
theorem R32471 : Reach 32471 := rs (se 1 (by rfl) ⟨24353, by rfl⟩) R48707
theorem R32491 : Reach 32491 := rs (se 1 (by rfl) ⟨24368, by rfl⟩) R48737
theorem R32503 : Reach 32503 := rs (se 1 (by rfl) ⟨24377, by rfl⟩) R48755
theorem R32523 : Reach 32523 := rs (se 1 (by rfl) ⟨24392, by rfl⟩) R48785
theorem R32535 : Reach 32535 := rs (se 1 (by rfl) ⟨24401, by rfl⟩) R48803
theorem R32555 : Reach 32555 := rs (se 1 (by rfl) ⟨24416, by rfl⟩) R48833
theorem R32567 : Reach 32567 := rs (se 1 (by rfl) ⟨24425, by rfl⟩) R48851
theorem R261953 : Reach 261953 := rs (se 2 (by rfl) ⟨98232, by rfl⟩) R196465
theorem R32587 : Reach 32587 := rs (se 1 (by rfl) ⟨24440, by rfl⟩) R48881
theorem R32599 : Reach 32599 := rs (se 1 (by rfl) ⟨24449, by rfl⟩) R48899
theorem R32619 : Reach 32619 := rs (se 1 (by rfl) ⟨24464, by rfl⟩) R48929
theorem R32631 : Reach 32631 := rs (se 1 (by rfl) ⟨24473, by rfl⟩) R48947
theorem R32651 : Reach 32651 := rs (se 1 (by rfl) ⟨24488, by rfl⟩) R48977
theorem R32663 : Reach 32663 := rs (se 1 (by rfl) ⟨24497, by rfl⟩) R48995
theorem R32683 : Reach 32683 := rs (se 1 (by rfl) ⟨24512, by rfl⟩) R49025
theorem R1343411 : Reach 1343411 := rs (se 1 (by rfl) ⟨1007558, by rfl⟩) R2015117
theorem R32695 : Reach 32695 := rs (se 1 (by rfl) ⟨24521, by rfl⟩) R49043
theorem R32715 : Reach 32715 := rs (se 1 (by rfl) ⟨24536, by rfl⟩) R49073
theorem R32727 : Reach 32727 := rs (se 1 (by rfl) ⟨24545, by rfl⟩) R49091
theorem R32747 : Reach 32747 := rs (se 1 (by rfl) ⟨24560, by rfl⟩) R49121
theorem R32759 : Reach 32759 := rs (se 1 (by rfl) ⟨24569, by rfl⟩) R49139
theorem R32775 : Reach 32775 := rs (se 1 (by rfl) ⟨24581, by rfl⟩) R49163
theorem R32783 : Reach 32783 := rs (se 1 (by rfl) ⟨24587, by rfl⟩) R49175
theorem R98347 : Reach 98347 := rs (se 1 (by rfl) ⟨73760, by rfl⟩) R147521
theorem R32827 : Reach 32827 := rs (se 1 (by rfl) ⟨24620, by rfl⟩) R49241
theorem R131159 : Reach 131159 := rs (se 1 (by rfl) ⟨98369, by rfl⟩) R196739
theorem R32903 : Reach 32903 := rs (se 1 (by rfl) ⟨24677, by rfl⟩) R49355
theorem R32911 : Reach 32911 := rs (se 1 (by rfl) ⟨24683, by rfl⟩) R49367
theorem R32955 : Reach 32955 := rs (se 1 (by rfl) ⟨24716, by rfl⟩) R49433
theorem R40337621 : Reach 40337621 := rs (se 7 (by rfl) ⟨472706, by rfl⟩) R945413
theorem R33031 : Reach 33031 := rs (se 1 (by rfl) ⟨24773, by rfl⟩) R49547
theorem R33039 : Reach 33039 := rs (se 1 (by rfl) ⟨24779, by rfl⟩) R49559
theorem R33083 : Reach 33083 := rs (se 1 (by rfl) ⟨24812, by rfl⟩) R49625
theorem R33159 : Reach 33159 := rs (se 1 (by rfl) ⟨24869, by rfl⟩) R49739
theorem R164231 : Reach 164231 := rs (se 1 (by rfl) ⟨123173, by rfl⟩) R246347
theorem R33167 : Reach 33167 := rs (se 1 (by rfl) ⟨24875, by rfl⟩) R49751
theorem R33211 : Reach 33211 := rs (se 1 (by rfl) ⟨24908, by rfl⟩) R49817
theorem R33287 : Reach 33287 := rs (se 1 (by rfl) ⟨24965, by rfl⟩) R49931
theorem R33295 : Reach 33295 := rs (se 1 (by rfl) ⟨24971, by rfl⟩) R49943
theorem R33339 : Reach 33339 := rs (se 1 (by rfl) ⟨25004, by rfl⟩) R50009
theorem R131645 : Reach 131645 := rs (se 3 (by rfl) ⟨24683, by rfl⟩) R49367
theorem R33415 : Reach 33415 := rs (se 1 (by rfl) ⟨25061, by rfl⟩) R50123
theorem R33423 : Reach 33423 := rs (se 1 (by rfl) ⟨25067, by rfl⟩) R50135
theorem R66233 : Reach 66233 := rs (se 2 (by rfl) ⟨24837, by rfl⟩) R49675
theorem R33467 : Reach 33467 := rs (se 1 (by rfl) ⟨25100, by rfl⟩) R50201
theorem R33543 : Reach 33543 := rs (se 1 (by rfl) ⟨25157, by rfl⟩) R50315
theorem R33551 : Reach 33551 := rs (se 1 (by rfl) ⟨25163, by rfl⟩) R50327
theorem R33595 : Reach 33595 := rs (se 1 (by rfl) ⟨25196, by rfl⟩) R50393
theorem R33671 : Reach 33671 := rs (se 1 (by rfl) ⟨25253, by rfl⟩) R50507
theorem R33679 : Reach 33679 := rs (se 1 (by rfl) ⟨25259, by rfl⟩) R50519
theorem R164753 : Reach 164753 := rs (se 2 (by rfl) ⟨61782, by rfl⟩) R123565
theorem R33723 : Reach 33723 := rs (se 1 (by rfl) ⟨25292, by rfl⟩) R50585
theorem R33799 : Reach 33799 := rs (se 1 (by rfl) ⟨25349, by rfl⟩) R50699
theorem R33807 : Reach 33807 := rs (se 1 (by rfl) ⟨25355, by rfl⟩) R50711
theorem R66575 : Reach 66575 := rs (se 1 (by rfl) ⟨49931, by rfl⟩) R99863
theorem R33851 : Reach 33851 := rs (se 1 (by rfl) ⟨25388, by rfl⟩) R50777
theorem R99389 : Reach 99389 := rs (se 3 (by rfl) ⟨18635, by rfl⟩) R37271
theorem R33927 : Reach 33927 := rs (se 1 (by rfl) ⟨25445, by rfl⟩) R50891
theorem R33935 : Reach 33935 := rs (se 1 (by rfl) ⟨25451, by rfl⟩) R50903
theorem R33979 : Reach 33979 := rs (se 1 (by rfl) ⟨25484, by rfl⟩) R50969
theorem R34055 : Reach 34055 := rs (se 1 (by rfl) ⟨25541, by rfl⟩) R51083
theorem R34063 : Reach 34063 := rs (se 1 (by rfl) ⟨25547, by rfl⟩) R51095
theorem R34107 : Reach 34107 := rs (se 1 (by rfl) ⟨25580, by rfl⟩) R51161
theorem R34183 : Reach 34183 := rs (se 1 (by rfl) ⟨25637, by rfl⟩) R51275
theorem R34191 : Reach 34191 := rs (se 1 (by rfl) ⟨25643, by rfl⟩) R51287
theorem R99737 : Reach 99737 := rs (se 2 (by rfl) ⟨37401, by rfl⟩) R74803
theorem R34235 : Reach 34235 := rs (se 1 (by rfl) ⟨25676, by rfl⟩) R51353
theorem R34311 : Reach 34311 := rs (se 1 (by rfl) ⟨25733, by rfl⟩) R51467
theorem R34319 : Reach 34319 := rs (se 1 (by rfl) ⟨25739, by rfl⟩) R51479
theorem R886301 : Reach 886301 := rs (se 3 (by rfl) ⟨166181, by rfl⟩) R332363
theorem R34363 : Reach 34363 := rs (se 1 (by rfl) ⟨25772, by rfl⟩) R51545
theorem R34439 : Reach 34439 := rs (se 1 (by rfl) ⟨25829, by rfl⟩) R51659
theorem R34447 : Reach 34447 := rs (se 1 (by rfl) ⟨25835, by rfl⟩) R51671
theorem R34491 : Reach 34491 := rs (se 1 (by rfl) ⟨25868, by rfl⟩) R51737
theorem R34567 : Reach 34567 := rs (se 1 (by rfl) ⟨25925, by rfl⟩) R51851
theorem R34575 : Reach 34575 := rs (se 1 (by rfl) ⟨25931, by rfl⟩) R51863
theorem R67387 : Reach 67387 := rs (se 1 (by rfl) ⟨50540, by rfl⟩) R101081
theorem R34619 : Reach 34619 := rs (se 1 (by rfl) ⟨25964, by rfl⟩) R51929
theorem R34695 : Reach 34695 := rs (se 1 (by rfl) ⟨26021, by rfl⟩) R52043
theorem R34703 : Reach 34703 := rs (se 1 (by rfl) ⟨26027, by rfl⟩) R52055
theorem R34747 : Reach 34747 := rs (se 1 (by rfl) ⟨26060, by rfl⟩) R52121
theorem R133073 : Reach 133073 := rs (se 2 (by rfl) ⟨49902, by rfl⟩) R99805
theorem R34823 : Reach 34823 := rs (se 1 (by rfl) ⟨26117, by rfl⟩) R52235
theorem R34831 : Reach 34831 := rs (se 1 (by rfl) ⟨26123, by rfl⟩) R52247
theorem R34875 : Reach 34875 := rs (se 1 (by rfl) ⟨26156, by rfl⟩) R52313
theorem R34951 : Reach 34951 := rs (se 1 (by rfl) ⟨26213, by rfl⟩) R52427
theorem R34959 : Reach 34959 := rs (se 1 (by rfl) ⟨26219, by rfl⟩) R52439
theorem R35003 : Reach 35003 := rs (se 1 (by rfl) ⟨26252, by rfl⟩) R52505
theorem R35079 : Reach 35079 := rs (se 1 (by rfl) ⟨26309, by rfl⟩) R52619
theorem R35087 : Reach 35087 := rs (se 1 (by rfl) ⟨26315, by rfl⟩) R52631
theorem R35131 : Reach 35131 := rs (se 1 (by rfl) ⟨26348, by rfl⟩) R52697
theorem R100723 : Reach 100723 := rs (se 1 (by rfl) ⟨75542, by rfl⟩) R151085
theorem R231815 : Reach 231815 := rs (se 1 (by rfl) ⟨173861, by rfl⟩) R347723
theorem R35599 : Reach 35599 := rs (se 1 (by rfl) ⟨26699, by rfl⟩) R53399
theorem R166859 : Reach 166859 := rs (se 1 (by rfl) ⟨125144, by rfl⟩) R250289
theorem R35983 : Reach 35983 := rs (se 1 (by rfl) ⟨26987, by rfl⟩) R53975
theorem R36103 : Reach 36103 := rs (se 1 (by rfl) ⟨27077, by rfl⟩) R54155
theorem R167183 : Reach 167183 := rs (se 1 (by rfl) ⟨125387, by rfl⟩) R250775
theorem R36283 : Reach 36283 := rs (se 1 (by rfl) ⟨27212, by rfl⟩) R54425
theorem R331229 : Reach 331229 := rs (se 3 (by rfl) ⟨62105, by rfl⟩) R124211
theorem R298525 : Reach 298525 := rs (se 3 (by rfl) ⟨55973, by rfl⟩) R111947
theorem R429745 : Reach 429745 := rs (se 2 (by rfl) ⟨161154, by rfl⟩) R322309
theorem R135047 : Reach 135047 := rs (se 1 (by rfl) ⟨101285, by rfl⟩) R202571
theorem R36751 : Reach 36751 := rs (se 1 (by rfl) ⟨27563, by rfl⟩) R55127
theorem R266327 : Reach 266327 := rs (se 1 (by rfl) ⟨199745, by rfl⟩) R399491
theorem R36983 : Reach 36983 := rs (se 1 (by rfl) ⟨27737, by rfl⟩) R55475
theorem R69779 : Reach 69779 := rs (se 1 (by rfl) ⟨52334, by rfl⟩) R104669
theorem R37111 : Reach 37111 := rs (se 1 (by rfl) ⟨27833, by rfl⟩) R55667
theorem R102671 : Reach 102671 := rs (se 1 (by rfl) ⟨77003, by rfl⟩) R154007
theorem R37255 : Reach 37255 := rs (se 1 (by rfl) ⟨27941, by rfl⟩) R55883
theorem R37291 : Reach 37291 := rs (se 1 (by rfl) ⟨27968, by rfl⟩) R55937
theorem R70073 : Reach 70073 := rs (se 2 (by rfl) ⟨26277, by rfl⟩) R52555
theorem R102941 : Reach 102941 := rs (se 3 (by rfl) ⟨19301, by rfl⟩) R38603
theorem R889379 : Reach 889379 := rs (se 1 (by rfl) ⟨667034, by rfl⟩) R1334069
theorem R37435 : Reach 37435 := rs (se 1 (by rfl) ⟨28076, by rfl⟩) R56153
theorem R168641 : Reach 168641 := rs (se 2 (by rfl) ⟨63240, by rfl⟩) R126481
theorem R70415 : Reach 70415 := rs (se 1 (by rfl) ⟨52811, by rfl⟩) R105623
theorem R70433 : Reach 70433 := rs (se 2 (by rfl) ⟨26412, by rfl⟩) R52825
theorem R594955 : Reach 594955 := rs (se 1 (by rfl) ⟨446216, by rfl⟩) R892433
theorem R37903 : Reach 37903 := rs (se 1 (by rfl) ⟨28427, by rfl⟩) R56855
theorem R70775 : Reach 70775 := rs (se 1 (by rfl) ⟨53081, by rfl⟩) R106163
theorem R38059 : Reach 38059 := rs (se 1 (by rfl) ⟨28544, by rfl⟩) R57089
theorem R70955 : Reach 70955 := rs (se 1 (by rfl) ⟨53216, by rfl⟩) R106433
theorem R38263 : Reach 38263 := rs (se 1 (by rfl) ⟨28697, by rfl⟩) R57395
theorem R71047 : Reach 71047 := rs (se 1 (by rfl) ⟨53285, by rfl⟩) R106571
theorem R38407 : Reach 38407 := rs (se 1 (by rfl) ⟨28805, by rfl⟩) R57611
theorem R38443 : Reach 38443 := rs (se 1 (by rfl) ⟨28832, by rfl⟩) R57665
theorem R661069 : Reach 661069 := rs (se 3 (by rfl) ⟨123950, by rfl⟩) R247901
theorem R71315 : Reach 71315 := rs (se 1 (by rfl) ⟨53486, by rfl⟩) R106973
theorem R38587 : Reach 38587 := rs (se 1 (by rfl) ⟨28940, by rfl⟩) R57881
theorem R71369 : Reach 71369 := rs (se 2 (by rfl) ⟨26763, by rfl⟩) R53527
theorem R136961 : Reach 136961 := rs (se 2 (by rfl) ⟨51360, by rfl⟩) R102721
theorem R169937 : Reach 169937 := rs (se 2 (by rfl) ⟨63726, by rfl⟩) R127453
theorem R39055 : Reach 39055 := rs (se 1 (by rfl) ⟨29291, by rfl⟩) R58583
theorem R72071 : Reach 72071 := rs (se 1 (by rfl) ⟨54053, by rfl⟩) R108107
theorem R72137 : Reach 72137 := rs (se 2 (by rfl) ⟨27051, by rfl⟩) R54103
theorem R39415 : Reach 39415 := rs (se 1 (by rfl) ⟨29561, by rfl⟩) R59123
theorem R39467 : Reach 39467 := rs (se 1 (by rfl) ⟨29600, by rfl⟩) R59201
theorem R72251 : Reach 72251 := rs (se 1 (by rfl) ⟨54188, by rfl⟩) R108377
theorem R105079 : Reach 105079 := rs (se 1 (by rfl) ⟨78809, by rfl⟩) R157619
theorem R72377 : Reach 72377 := rs (se 2 (by rfl) ⟨27141, by rfl⟩) R54283
theorem R39799 : Reach 39799 := rs (se 1 (by rfl) ⟨29849, by rfl⟩) R59699
theorem R39943 : Reach 39943 := rs (se 1 (by rfl) ⟨29957, by rfl⟩) R59915
theorem R72719 : Reach 72719 := rs (se 1 (by rfl) ⟨54539, by rfl⟩) R109079
theorem R171031 : Reach 171031 := rs (se 1 (by rfl) ⟨128273, by rfl⟩) R256547
theorem R72737 : Reach 72737 := rs (se 2 (by rfl) ⟨27276, by rfl⟩) R54553
theorem R105515 : Reach 105515 := rs (se 1 (by rfl) ⟨79136, by rfl⟩) R158273
theorem R73079 : Reach 73079 := rs (se 1 (by rfl) ⟨54809, by rfl⟩) R109619
theorem R40439 : Reach 40439 := rs (se 1 (by rfl) ⟨30329, by rfl⟩) R60659
theorem R73259 : Reach 73259 := rs (se 1 (by rfl) ⟨54944, by rfl⟩) R109889
theorem R269891 : Reach 269891 := rs (se 1 (by rfl) ⟨202418, by rfl⟩) R404837
theorem R40591 : Reach 40591 := rs (se 1 (by rfl) ⟨30443, by rfl⟩) R60887
theorem R73487 : Reach 73487 := rs (se 1 (by rfl) ⟨55115, by rfl⟩) R110231
theorem R302899 : Reach 302899 := rs (se 1 (by rfl) ⟨227174, by rfl⟩) R454349
theorem R40763 : Reach 40763 := rs (se 1 (by rfl) ⟨30572, by rfl⟩) R61145
theorem R73619 : Reach 73619 := rs (se 1 (by rfl) ⟨55214, by rfl⟩) R110429
theorem R73673 : Reach 73673 := rs (se 2 (by rfl) ⟨27627, by rfl⟩) R55255
theorem R172043 : Reach 172043 := rs (se 1 (by rfl) ⟨129032, by rfl⟩) R258065
theorem R172205 : Reach 172205 := rs (se 3 (by rfl) ⟨32288, by rfl⟩) R64577
theorem R106811 : Reach 106811 := rs (se 1 (by rfl) ⟨80108, by rfl⟩) R160217
theorem R74375 : Reach 74375 := rs (se 1 (by rfl) ⟨55781, by rfl⟩) R111563
theorem R74393 : Reach 74393 := rs (se 2 (by rfl) ⟨27897, by rfl⟩) R55795
theorem R41735 : Reach 41735 := rs (se 1 (by rfl) ⟨31301, by rfl⟩) R62603
theorem R533263 : Reach 533263 := rs (se 1 (by rfl) ⟨399947, by rfl⟩) R799895
theorem R107297 : Reach 107297 := rs (se 2 (by rfl) ⟨40236, by rfl⟩) R80473
theorem R74555 : Reach 74555 := rs (se 1 (by rfl) ⟨55916, by rfl⟩) R111833
theorem R74681 : Reach 74681 := rs (se 2 (by rfl) ⟨28005, by rfl⟩) R56011
theorem R74753 : Reach 74753 := rs (se 2 (by rfl) ⟨28032, by rfl⟩) R56065
theorem R74767 : Reach 74767 := rs (se 1 (by rfl) ⟨56075, by rfl⟩) R112151
theorem R336919 : Reach 336919 := rs (se 1 (by rfl) ⟨252689, by rfl⟩) R505379
theorem R75023 : Reach 75023 := rs (se 1 (by rfl) ⟨56267, by rfl⟩) R112535
theorem R75041 : Reach 75041 := rs (se 2 (by rfl) ⟨28140, by rfl⟩) R56281
theorem R75095 : Reach 75095 := rs (se 1 (by rfl) ⟨56321, by rfl⟩) R112643
theorem R107891 : Reach 107891 := rs (se 1 (by rfl) ⟨80918, by rfl⟩) R161837
theorem R42383 : Reach 42383 := rs (se 1 (by rfl) ⟨31787, by rfl⟩) R63575
theorem R75275 : Reach 75275 := rs (se 1 (by rfl) ⟨56456, by rfl⟩) R112913
theorem R42553 : Reach 42553 := rs (se 2 (by rfl) ⟨15957, by rfl⟩) R31915
theorem R75383 : Reach 75383 := rs (se 1 (by rfl) ⟨56537, by rfl⟩) R113075
theorem R42697 : Reach 42697 := rs (se 2 (by rfl) ⟨16011, by rfl⟩) R32023
theorem R173825 : Reach 173825 := rs (se 2 (by rfl) ⟨65184, by rfl⟩) R130369
theorem R239375 : Reach 239375 := rs (se 1 (by rfl) ⟨179531, by rfl⟩) R359063
theorem R75563 : Reach 75563 := rs (se 1 (by rfl) ⟨56672, by rfl⟩) R113345
theorem R75635 : Reach 75635 := rs (se 1 (by rfl) ⟨56726, by rfl⟩) R113453
theorem R272281 : Reach 272281 := rs (se 2 (by rfl) ⟨102105, by rfl⟩) R204211
theorem R403501 : Reach 403501 := rs (se 3 (by rfl) ⟨75656, by rfl⟩) R151313
theorem R75923 : Reach 75923 := rs (se 1 (by rfl) ⟨56942, by rfl⟩) R113885
theorem R43193 : Reach 43193 := rs (se 2 (by rfl) ⟨16197, by rfl⟩) R32395
theorem R75977 : Reach 75977 := rs (se 2 (by rfl) ⟨28491, by rfl⟩) R56983
theorem R174635 : Reach 174635 := rs (se 1 (by rfl) ⟨130976, by rfl⟩) R261953
theorem R895607 : Reach 895607 := rs (se 1 (by rfl) ⟨671705, by rfl⟩) R1343411
theorem R666305 : Reach 666305 := rs (se 2 (by rfl) ⟨249864, by rfl⟩) R499729
theorem R76679 : Reach 76679 := rs (se 1 (by rfl) ⟨57509, by rfl⟩) R115019
theorem R76697 : Reach 76697 := rs (se 2 (by rfl) ⟨28761, by rfl⟩) R57523
theorem R76859 : Reach 76859 := rs (se 1 (by rfl) ⟨57644, by rfl⟩) R115289
theorem R76985 : Reach 76985 := rs (se 2 (by rfl) ⟨28869, by rfl⟩) R57739
theorem R77057 : Reach 77057 := rs (se 2 (by rfl) ⟨28896, by rfl⟩) R57793
theorem R77327 : Reach 77327 := rs (se 1 (by rfl) ⟨57995, by rfl⟩) R115991
theorem R77345 : Reach 77345 := rs (se 2 (by rfl) ⟨29004, by rfl⟩) R58009
theorem R77399 : Reach 77399 := rs (se 1 (by rfl) ⟨58049, by rfl⟩) R116099
theorem R44731 : Reach 44731 := rs (se 1 (by rfl) ⟨33548, by rfl⟩) R67097
theorem R77579 : Reach 77579 := rs (se 1 (by rfl) ⟨58184, by rfl⟩) R116369
theorem R175931 : Reach 175931 := rs (se 1 (by rfl) ⟨131948, by rfl⟩) R263897
theorem R274265 : Reach 274265 := rs (se 2 (by rfl) ⟨102849, by rfl⟩) R205699
theorem R77687 : Reach 77687 := rs (se 1 (by rfl) ⟨58265, by rfl⟩) R116531
theorem R110483 : Reach 110483 := rs (se 1 (by rfl) ⟨82862, by rfl⟩) R165725
theorem R77753 : Reach 77753 := rs (se 2 (by rfl) ⟨29157, by rfl⟩) R58315
theorem R176093 : Reach 176093 := rs (se 3 (by rfl) ⟨33017, by rfl⟩) R66035
theorem R77867 : Reach 77867 := rs (se 1 (by rfl) ⟨58400, by rfl⟩) R116801
theorem R110659 : Reach 110659 := rs (se 1 (by rfl) ⟨82994, by rfl⟩) R165989
theorem R77939 : Reach 77939 := rs (se 1 (by rfl) ⟨58454, by rfl⟩) R116909
theorem R176417 : Reach 176417 := rs (se 2 (by rfl) ⟨66156, by rfl⟩) R132313
theorem R536977 : Reach 536977 := rs (se 2 (by rfl) ⟨201366, by rfl⟩) R402733
theorem R78227 : Reach 78227 := rs (se 1 (by rfl) ⟨58670, by rfl⟩) R117341
theorem R78281 : Reach 78281 := rs (se 2 (by rfl) ⟨29355, by rfl⟩) R58711
theorem R45883 : Reach 45883 := rs (se 1 (by rfl) ⟨34412, by rfl⟩) R68825
theorem R144337 : Reach 144337 := rs (se 2 (by rfl) ⟨54126, by rfl⟩) R108253
theorem R78907 : Reach 78907 := rs (se 1 (by rfl) ⟨59180, by rfl⟩) R118361
theorem R144503 : Reach 144503 := rs (se 1 (by rfl) ⟨108377, by rfl⟩) R216755
theorem R78983 : Reach 78983 := rs (se 1 (by rfl) ⟨59237, by rfl⟩) R118475
theorem R78995 : Reach 78995 := rs (se 1 (by rfl) ⟨59246, by rfl⟩) R118493
theorem R79001 : Reach 79001 := rs (se 2 (by rfl) ⟨29625, by rfl⟩) R59251
theorem R177389 : Reach 177389 := rs (se 3 (by rfl) ⟨33260, by rfl⟩) R66521
theorem R111887 : Reach 111887 := rs (se 1 (by rfl) ⟨83915, by rfl⟩) R167831
theorem R177497 : Reach 177497 := rs (se 2 (by rfl) ⟨66561, by rfl⟩) R133123
theorem R308573 : Reach 308573 := rs (se 3 (by rfl) ⟨57857, by rfl⟩) R115715
theorem R144787 : Reach 144787 := rs (se 1 (by rfl) ⟨108590, by rfl⟩) R217181
theorem R1291697 : Reach 1291697 := rs (se 2 (by rfl) ⟨484386, by rfl⟩) R968773
theorem R79289 : Reach 79289 := rs (se 2 (by rfl) ⟨29733, by rfl⟩) R59467
theorem R112157 : Reach 112157 := rs (se 3 (by rfl) ⟨21029, by rfl⟩) R42059
theorem R46651 : Reach 46651 := rs (se 1 (by rfl) ⟨34988, by rfl⟩) R69977
theorem R46727 : Reach 46727 := rs (se 1 (by rfl) ⟨35045, by rfl⟩) R70091
theorem R46763 : Reach 46763 := rs (se 1 (by rfl) ⟨35072, by rfl⟩) R70145
theorem R46793 : Reach 46793 := rs (se 2 (by rfl) ⟨17547, by rfl⟩) R35095
theorem R46907 : Reach 46907 := rs (se 1 (by rfl) ⟨35180, by rfl⟩) R70361
theorem R46967 : Reach 46967 := rs (se 1 (by rfl) ⟨35225, by rfl⟩) R70451
theorem R46991 : Reach 46991 := rs (se 1 (by rfl) ⟨35243, by rfl⟩) R70487
theorem R47033 : Reach 47033 := rs (se 2 (by rfl) ⟨17637, by rfl⟩) R35275
theorem R47111 : Reach 47111 := rs (se 1 (by rfl) ⟨35333, by rfl⟩) R70667
theorem R47147 : Reach 47147 := rs (se 1 (by rfl) ⟨35360, by rfl⟩) R70721
theorem R47177 : Reach 47177 := rs (se 2 (by rfl) ⟨17691, by rfl⟩) R35383
theorem R211031 : Reach 211031 := rs (se 1 (by rfl) ⟨158273, by rfl⟩) R316547
theorem R79987 : Reach 79987 := rs (se 1 (by rfl) ⟨59990, by rfl⟩) R119981
theorem R47291 : Reach 47291 := rs (se 1 (by rfl) ⟨35468, by rfl⟩) R70937
theorem R47351 : Reach 47351 := rs (se 1 (by rfl) ⟨35513, by rfl⟩) R71027
theorem R80129 : Reach 80129 := rs (se 2 (by rfl) ⟨30048, by rfl⟩) R60097
theorem R47375 : Reach 47375 := rs (se 1 (by rfl) ⟨35531, by rfl⟩) R71063
theorem R178469 : Reach 178469 := rs (se 4 (by rfl) ⟨16731, by rfl⟩) R33463
theorem R47417 : Reach 47417 := rs (se 2 (by rfl) ⟨17781, by rfl⟩) R35563
theorem R47495 : Reach 47495 := rs (se 1 (by rfl) ⟨35621, by rfl⟩) R71243
theorem R47531 : Reach 47531 := rs (se 1 (by rfl) ⟨35648, by rfl⟩) R71297
theorem R47561 : Reach 47561 := rs (se 2 (by rfl) ⟨17835, by rfl⟩) R35671
theorem R113105 : Reach 113105 := rs (se 2 (by rfl) ⟨42414, by rfl⟩) R84829
theorem R47675 : Reach 47675 := rs (se 1 (by rfl) ⟨35756, by rfl⟩) R71513
theorem R47735 : Reach 47735 := rs (se 1 (by rfl) ⟨35801, by rfl⟩) R71603
theorem R47759 : Reach 47759 := rs (se 1 (by rfl) ⟨35819, by rfl⟩) R71639
theorem R735925 : Reach 735925 := rs (se 5 (by rfl) ⟨34496, by rfl⟩) R68993
theorem R47801 : Reach 47801 := rs (se 2 (by rfl) ⟨17925, by rfl⟩) R35851
theorem R80585 : Reach 80585 := rs (se 2 (by rfl) ⟨30219, by rfl⟩) R60439
theorem R309977 : Reach 309977 := rs (se 2 (by rfl) ⟨116241, by rfl⟩) R232483
theorem R47879 : Reach 47879 := rs (se 1 (by rfl) ⟨35909, by rfl⟩) R71819
theorem R47915 : Reach 47915 := rs (se 1 (by rfl) ⟨35936, by rfl⟩) R71873
theorem R47945 : Reach 47945 := rs (se 2 (by rfl) ⟨17979, by rfl⟩) R35959
theorem R113561 : Reach 113561 := rs (se 2 (by rfl) ⟨42585, by rfl⟩) R85171
theorem R48059 : Reach 48059 := rs (se 1 (by rfl) ⟨36044, by rfl⟩) R72089
theorem R48119 : Reach 48119 := rs (se 1 (by rfl) ⟨36089, by rfl⟩) R72179
theorem R48143 : Reach 48143 := rs (se 1 (by rfl) ⟨36107, by rfl⟩) R72215
theorem R146461 : Reach 146461 := rs (se 3 (by rfl) ⟨27461, by rfl⟩) R54923
theorem R179243 : Reach 179243 := rs (se 1 (by rfl) ⟨134432, by rfl⟩) R268865
theorem R80939 : Reach 80939 := rs (se 1 (by rfl) ⟨60704, by rfl⟩) R121409
theorem R48185 : Reach 48185 := rs (se 2 (by rfl) ⟨18069, by rfl⟩) R36139
theorem R48263 : Reach 48263 := rs (se 1 (by rfl) ⟨36197, by rfl⟩) R72395
theorem R48299 : Reach 48299 := rs (se 1 (by rfl) ⟨36224, by rfl⟩) R72449
theorem R48329 : Reach 48329 := rs (se 2 (by rfl) ⟨18123, by rfl⟩) R36247
theorem R2243861 : Reach 2243861 := rs (se 6 (by rfl) ⟨52590, by rfl⟩) R105181
theorem R48443 : Reach 48443 := rs (se 1 (by rfl) ⟨36332, by rfl⟩) R72665
theorem R48503 : Reach 48503 := rs (se 1 (by rfl) ⟨36377, by rfl⟩) R72755
theorem R48527 : Reach 48527 := rs (se 1 (by rfl) ⟨36395, by rfl⟩) R72791
theorem R48569 : Reach 48569 := rs (se 2 (by rfl) ⟨18213, by rfl⟩) R36427
theorem R245213 : Reach 245213 := rs (se 3 (by rfl) ⟨45977, by rfl⟩) R91955
theorem R48647 : Reach 48647 := rs (se 1 (by rfl) ⟨36485, by rfl⟩) R72971
theorem R48683 : Reach 48683 := rs (se 1 (by rfl) ⟨36512, by rfl⟩) R73025
theorem R48713 : Reach 48713 := rs (se 2 (by rfl) ⟨18267, by rfl⟩) R36535
theorem R114263 : Reach 114263 := rs (se 1 (by rfl) ⟨85697, by rfl⟩) R171395
theorem R48775 : Reach 48775 := rs (se 1 (by rfl) ⟨36581, by rfl⟩) R73163
theorem R48827 : Reach 48827 := rs (se 1 (by rfl) ⟨36620, by rfl⟩) R73241
theorem R48887 : Reach 48887 := rs (se 1 (by rfl) ⟨36665, by rfl⟩) R73331
theorem R48911 : Reach 48911 := rs (se 1 (by rfl) ⟨36683, by rfl⟩) R73367
theorem R48953 : Reach 48953 := rs (se 2 (by rfl) ⟨18357, by rfl⟩) R36715
theorem R81751 : Reach 81751 := rs (se 1 (by rfl) ⟨61313, by rfl⟩) R122627
theorem R49031 : Reach 49031 := rs (se 1 (by rfl) ⟨36773, by rfl⟩) R73547
theorem R49067 : Reach 49067 := rs (se 1 (by rfl) ⟨36800, by rfl⟩) R73601
theorem R49097 : Reach 49097 := rs (se 2 (by rfl) ⟨18411, by rfl⟩) R36823
theorem R114641 : Reach 114641 := rs (se 2 (by rfl) ⟨42990, by rfl⟩) R85981
theorem R81931 : Reach 81931 := rs (se 1 (by rfl) ⟨61448, by rfl⟩) R122897
theorem R49211 : Reach 49211 := rs (se 1 (by rfl) ⟨36908, by rfl⟩) R73817
theorem R114749 : Reach 114749 := rs (se 3 (by rfl) ⟨21515, by rfl⟩) R43031
theorem R49271 : Reach 49271 := rs (se 1 (by rfl) ⟨36953, by rfl⟩) R73907
theorem R82073 : Reach 82073 := rs (se 2 (by rfl) ⟨30777, by rfl⟩) R61555
theorem R49337 : Reach 49337 := rs (se 2 (by rfl) ⟨18501, by rfl⟩) R37003
theorem R213229 : Reach 213229 := rs (se 3 (by rfl) ⟨39980, by rfl⟩) R79961
theorem R540917 : Reach 540917 := rs (se 5 (by rfl) ⟨25355, by rfl⟩) R50711
theorem R49451 : Reach 49451 := rs (se 1 (by rfl) ⟨37088, by rfl⟩) R74177
theorem R82235 : Reach 82235 := rs (se 1 (by rfl) ⟨61676, by rfl⟩) R123353
theorem R147865 : Reach 147865 := rs (se 2 (by rfl) ⟨55449, by rfl⟩) R110899
theorem R180701 : Reach 180701 := rs (se 3 (by rfl) ⟨33881, by rfl⟩) R67763
theorem R49679 : Reach 49679 := rs (se 1 (by rfl) ⟨37259, by rfl⟩) R74519
theorem R672299 : Reach 672299 := rs (se 1 (by rfl) ⟨504224, by rfl⟩) R1008449
theorem R115319 : Reach 115319 := rs (se 1 (by rfl) ⟨86489, by rfl⟩) R172979
theorem R49799 : Reach 49799 := rs (se 1 (by rfl) ⟨37349, by rfl⟩) R74699
theorem R82579 : Reach 82579 := rs (se 1 (by rfl) ⟨61934, by rfl⟩) R123869
theorem R49865 : Reach 49865 := rs (se 2 (by rfl) ⟨18699, by rfl⟩) R37399
theorem R148169 : Reach 148169 := rs (se 2 (by rfl) ⟨55563, by rfl⟩) R111127
theorem R82721 : Reach 82721 := rs (se 2 (by rfl) ⟨31020, by rfl⟩) R62041
theorem R246577 : Reach 246577 := rs (se 2 (by rfl) ⟨92466, by rfl⟩) R184933
theorem R49979 : Reach 49979 := rs (se 1 (by rfl) ⟨37484, by rfl⟩) R74969
theorem R50039 : Reach 50039 := rs (se 1 (by rfl) ⟨37529, by rfl⟩) R75059
theorem R279449 : Reach 279449 := rs (se 2 (by rfl) ⟨104793, by rfl⟩) R209587
theorem R50105 : Reach 50105 := rs (se 2 (by rfl) ⟨18789, by rfl⟩) R37579
theorem R50219 : Reach 50219 := rs (se 1 (by rfl) ⟨37664, by rfl⟩) R75329
theorem R50447 : Reach 50447 := rs (se 1 (by rfl) ⟨37835, by rfl⟩) R75671
theorem R83261 : Reach 83261 := rs (se 3 (by rfl) ⟨15611, by rfl⟩) R31223
theorem R50567 : Reach 50567 := rs (se 1 (by rfl) ⟨37925, by rfl⟩) R75851
theorem R116153 : Reach 116153 := rs (se 2 (by rfl) ⟨43557, by rfl⟩) R87115
theorem R50633 : Reach 50633 := rs (se 2 (by rfl) ⟨18987, by rfl⟩) R37975
theorem R149015 : Reach 149015 := rs (se 1 (by rfl) ⟨111761, by rfl⟩) R223523
theorem R50747 : Reach 50747 := rs (se 1 (by rfl) ⟨38060, by rfl⟩) R76121
theorem R542285 : Reach 542285 := rs (se 3 (by rfl) ⟨101678, by rfl⟩) R203357
theorem R247373 : Reach 247373 := rs (se 3 (by rfl) ⟨46382, by rfl⟩) R92765
theorem R50807 : Reach 50807 := rs (se 1 (by rfl) ⟨38105, by rfl⟩) R76211
theorem R149111 : Reach 149111 := rs (se 1 (by rfl) ⟨111833, by rfl⟩) R223667
theorem R50873 : Reach 50873 := rs (se 2 (by rfl) ⟨19077, by rfl⟩) R38155
theorem R214721 : Reach 214721 := rs (se 2 (by rfl) ⟨80520, by rfl⟩) R161041
theorem R83713 : Reach 83713 := rs (se 2 (by rfl) ⟨31392, by rfl⟩) R62785
theorem R50987 : Reach 50987 := rs (se 1 (by rfl) ⟨38240, by rfl⟩) R76481
theorem R116747 : Reach 116747 := rs (se 1 (by rfl) ⟨87560, by rfl⟩) R175121
theorem R51215 : Reach 51215 := rs (se 1 (by rfl) ⟨38411, by rfl⟩) R76823
theorem R116855 : Reach 116855 := rs (se 1 (by rfl) ⟨87641, by rfl⟩) R175283
theorem R51335 : Reach 51335 := rs (se 1 (by rfl) ⟨38501, by rfl⟩) R77003
theorem R51401 : Reach 51401 := rs (se 2 (by rfl) ⟨19275, by rfl⟩) R38551
theorem R51515 : Reach 51515 := rs (se 1 (by rfl) ⟨38636, by rfl⟩) R77273
theorem R84311 : Reach 84311 := rs (se 1 (by rfl) ⟨63233, by rfl⟩) R126467
theorem R51575 : Reach 51575 := rs (se 1 (by rfl) ⟨38681, by rfl⟩) R77363
theorem R51641 : Reach 51641 := rs (se 2 (by rfl) ⟨19365, by rfl⟩) R38731
theorem R84523 : Reach 84523 := rs (se 1 (by rfl) ⟨63392, by rfl⟩) R126785
theorem R51755 : Reach 51755 := rs (se 1 (by rfl) ⟨38816, by rfl⟩) R77633
theorem R51847 : Reach 51847 := rs (se 1 (by rfl) ⟨38885, by rfl⟩) R77771
theorem R84665 : Reach 84665 := rs (se 2 (by rfl) ⟨31749, by rfl⟩) R63499
theorem R117449 : Reach 117449 := rs (se 2 (by rfl) ⟨44043, by rfl⟩) R88087
theorem R51983 : Reach 51983 := rs (se 1 (by rfl) ⟨38987, by rfl⟩) R77975
theorem R84797 : Reach 84797 := rs (se 3 (by rfl) ⟨15899, by rfl⟩) R31799
theorem R52103 : Reach 52103 := rs (se 1 (by rfl) ⟨39077, by rfl⟩) R78155
theorem R183185 : Reach 183185 := rs (se 2 (by rfl) ⟨68694, by rfl⟩) R137389
theorem R52169 : Reach 52169 := rs (se 2 (by rfl) ⟨19563, by rfl⟩) R39127
theorem R150493 : Reach 150493 := rs (se 3 (by rfl) ⟨28217, by rfl⟩) R56435
theorem R52283 : Reach 52283 := rs (se 1 (by rfl) ⟨39212, by rfl⟩) R78425
theorem R117827 : Reach 117827 := rs (se 1 (by rfl) ⟨88370, by rfl⟩) R176741
theorem R52343 : Reach 52343 := rs (se 1 (by rfl) ⟨39257, by rfl⟩) R78515
theorem R52409 : Reach 52409 := rs (se 2 (by rfl) ⟨19653, by rfl⟩) R39307
theorem R52523 : Reach 52523 := rs (se 1 (by rfl) ⟨39392, by rfl⟩) R78785
theorem R150835 : Reach 150835 := rs (se 1 (by rfl) ⟨113126, by rfl⟩) R226253
theorem R118151 : Reach 118151 := rs (se 1 (by rfl) ⟨88613, by rfl⟩) R177227
theorem R118201 : Reach 118201 := rs (se 2 (by rfl) ⟨44325, by rfl⟩) R88651
theorem R52751 : Reach 52751 := rs (se 1 (by rfl) ⟨39563, by rfl⟩) R79127
theorem R183869 : Reach 183869 := rs (se 3 (by rfl) ⟨34475, by rfl⟩) R68951
theorem R216695 : Reach 216695 := rs (se 1 (by rfl) ⟨162521, by rfl⟩) R325043
theorem R85657 : Reach 85657 := rs (se 2 (by rfl) ⟨32121, by rfl⟩) R64243
theorem R282305 : Reach 282305 := rs (se 2 (by rfl) ⟨105864, by rfl⟩) R211729
theorem R52937 : Reach 52937 := rs (se 2 (by rfl) ⟨19851, by rfl⟩) R39703
theorem R85819 : Reach 85819 := rs (se 1 (by rfl) ⟨64364, by rfl⟩) R128729
theorem R118675 : Reach 118675 := rs (se 1 (by rfl) ⟨89006, by rfl⟩) R178013
theorem R348067 : Reach 348067 := rs (se 1 (by rfl) ⟨261050, by rfl⟩) R522101
theorem R85961 : Reach 85961 := rs (se 2 (by rfl) ⟨32235, by rfl⟩) R64471
theorem R249803 : Reach 249803 := rs (se 1 (by rfl) ⟨187352, by rfl⟩) R374705
theorem R53291 : Reach 53291 := rs (se 1 (by rfl) ⟨39968, by rfl⟩) R79937
theorem R86305 : Reach 86305 := rs (se 2 (by rfl) ⟨32364, by rfl⟩) R64729
theorem R53689 : Reach 53689 := rs (se 2 (by rfl) ⟨20133, by rfl⟩) R40267
theorem R774917 : Reach 774917 := rs (se 4 (by rfl) ⟨72648, by rfl⟩) R145297
theorem R86845 : Reach 86845 := rs (se 3 (by rfl) ⟨16283, by rfl⟩) R32567
theorem R86903 : Reach 86903 := rs (se 1 (by rfl) ⟨65177, by rfl⟩) R130355
theorem R54391 : Reach 54391 := rs (se 1 (by rfl) ⟨40793, by rfl⟩) R81587
theorem R54587 : Reach 54587 := rs (se 1 (by rfl) ⟨40940, by rfl⟩) R81881
theorem R218513 : Reach 218513 := rs (se 2 (by rfl) ⟨81942, by rfl⟩) R163885
theorem R87581 : Reach 87581 := rs (se 3 (by rfl) ⟨16421, by rfl⟩) R32843
theorem R54985 : Reach 54985 := rs (se 2 (by rfl) ⟨20619, by rfl⟩) R41239
theorem R120521 : Reach 120521 := rs (se 2 (by rfl) ⟨45195, by rfl⟩) R90391
theorem R120635 : Reach 120635 := rs (se 1 (by rfl) ⟨90476, by rfl⟩) R180953
theorem R55175 : Reach 55175 := rs (se 1 (by rfl) ⟨41381, by rfl⟩) R82763
theorem R186259 : Reach 186259 := rs (se 1 (by rfl) ⟨139694, by rfl⟩) R279389
theorem R88199 : Reach 88199 := rs (se 1 (by rfl) ⟨66149, by rfl⟩) R132299
theorem R88249 : Reach 88249 := rs (se 2 (by rfl) ⟨33093, by rfl⟩) R66187
theorem R121121 : Reach 121121 := rs (se 2 (by rfl) ⟨45420, by rfl⟩) R90841
theorem R55687 : Reach 55687 := rs (se 1 (by rfl) ⟨41765, by rfl⟩) R83531
theorem R383453 : Reach 383453 := rs (se 3 (by rfl) ⟨71897, by rfl⟩) R143795
theorem R88847 : Reach 88847 := rs (se 1 (by rfl) ⟨66635, by rfl⟩) R133271
theorem R351013 : Reach 351013 := rs (se 4 (by rfl) ⟨32907, by rfl⟩) R65815
theorem R56335 : Reach 56335 := rs (se 1 (by rfl) ⟨42251, by rfl⟩) R84503
theorem R122093 : Reach 122093 := rs (se 3 (by rfl) ⟨22892, by rfl⟩) R45785
theorem R155159 : Reach 155159 := rs (se 1 (by rfl) ⟨116369, by rfl⟩) R232739
theorem R56875 : Reach 56875 := rs (se 1 (by rfl) ⟨42656, by rfl⟩) R85313
theorem R122411 : Reach 122411 := rs (se 1 (by rfl) ⟨91808, by rfl⟩) R183617
theorem R187991 : Reach 187991 := rs (se 1 (by rfl) ⟨140993, by rfl⟩) R281987
theorem R57017 : Reach 57017 := rs (se 2 (by rfl) ⟨21381, by rfl⟩) R42763
theorem R89785 : Reach 89785 := rs (se 2 (by rfl) ⟨33669, by rfl⟩) R67339
theorem R89915 : Reach 89915 := rs (se 1 (by rfl) ⟨67436, by rfl⟩) R134873
theorem R778481 : Reach 778481 := rs (se 2 (by rfl) ⟨291930, by rfl⟩) R583861
theorem R90487 : Reach 90487 := rs (se 1 (by rfl) ⟨67865, by rfl⟩) R135731
theorem R57719 : Reach 57719 := rs (se 1 (by rfl) ⟨43289, by rfl⟩) R86579
theorem R58171 : Reach 58171 := rs (se 1 (by rfl) ⟨43628, by rfl⟩) R87257
theorem R58259 : Reach 58259 := rs (se 1 (by rfl) ⟨43694, by rfl⟩) R87389
theorem R58313 : Reach 58313 := rs (se 2 (by rfl) ⟨21867, by rfl⟩) R43735
theorem R255149 : Reach 255149 := rs (se 3 (by rfl) ⟨47840, by rfl⟩) R95681
theorem R58657 : Reach 58657 := rs (se 2 (by rfl) ⟨21996, by rfl⟩) R43993
theorem R91763 : Reach 91763 := rs (se 1 (by rfl) ⟨68822, by rfl⟩) R137645
theorem R59015 : Reach 59015 := rs (se 1 (by rfl) ⟨44261, by rfl⟩) R88523
theorem R681797 : Reach 681797 := rs (se 4 (by rfl) ⟨63918, by rfl⟩) R127837
theorem R91991 : Reach 91991 := rs (se 1 (by rfl) ⟨68993, by rfl⟩) R137987
theorem R157625 : Reach 157625 := rs (se 2 (by rfl) ⟨59109, by rfl⟩) R118219
theorem R157643 : Reach 157643 := rs (se 1 (by rfl) ⟨118232, by rfl⟩) R236465
theorem R157889 : Reach 157889 := rs (se 2 (by rfl) ⟨59208, by rfl⟩) R118417
theorem R125129 : Reach 125129 := rs (se 2 (by rfl) ⟨46923, by rfl⟩) R93847
theorem R125165 : Reach 125165 := rs (se 3 (by rfl) ⟨23468, by rfl⟩) R46937
theorem R322001 : Reach 322001 := rs (se 2 (by rfl) ⟨120750, by rfl⟩) R241501
theorem R60203 : Reach 60203 := rs (se 1 (by rfl) ⟨45152, by rfl⟩) R90305
theorem R486233 : Reach 486233 := rs (se 2 (by rfl) ⟨182337, by rfl⟩) R364675
theorem R224153 : Reach 224153 := rs (se 2 (by rfl) ⟨84057, by rfl⟩) R168115
theorem R125981 : Reach 125981 := rs (se 3 (by rfl) ⟨23621, by rfl⟩) R47243
theorem R125995 : Reach 125995 := rs (se 1 (by rfl) ⟨94496, by rfl⟩) R188993
theorem R60601 : Reach 60601 := rs (se 2 (by rfl) ⟨22725, by rfl⟩) R45451
theorem R158921 : Reach 158921 := rs (se 2 (by rfl) ⟨59595, by rfl⟩) R119191
theorem R1371491 : Reach 1371491 := rs (se 1 (by rfl) ⟨1028618, by rfl⟩) R2057237
theorem R93575 : Reach 93575 := rs (se 1 (by rfl) ⟨70181, by rfl⟩) R140363
theorem R257579 : Reach 257579 := rs (se 1 (by rfl) ⟨193184, by rfl⟩) R386369
theorem R93757 : Reach 93757 := rs (se 3 (by rfl) ⟨17579, by rfl⟩) R35159
theorem R94223 : Reach 94223 := rs (se 1 (by rfl) ⟨70667, by rfl⟩) R141335
theorem R127037 : Reach 127037 := rs (se 3 (by rfl) ⟨23819, by rfl⟩) R47639
theorem R61897 : Reach 61897 := rs (se 2 (by rfl) ⟨23211, by rfl⟩) R46423
theorem R61985 : Reach 61985 := rs (se 2 (by rfl) ⟨23244, by rfl⟩) R46489
theorem R357209 : Reach 357209 := rs (se 2 (by rfl) ⟨133953, by rfl⟩) R267907
theorem R390167 : Reach 390167 := rs (se 1 (by rfl) ⟨292625, by rfl⟩) R585251
theorem R128087 : Reach 128087 := rs (se 1 (by rfl) ⟨96065, by rfl⟩) R192131
theorem R95489 : Reach 95489 := rs (se 2 (by rfl) ⟨35808, by rfl⟩) R71617
theorem R161291 : Reach 161291 := rs (se 1 (by rfl) ⟨120968, by rfl⟩) R241937
theorem R194507 : Reach 194507 := rs (se 1 (by rfl) ⟨145880, by rfl⟩) R291761
theorem R194525 : Reach 194525 := rs (se 3 (by rfl) ⟨36473, by rfl⟩) R72947
theorem R391405 : Reach 391405 := rs (se 3 (by rfl) ⟨73388, by rfl⟩) R146777
theorem R63803 : Reach 63803 := rs (se 1 (by rfl) ⟨47852, by rfl⟩) R95705
theorem R31119 : Reach 31119 := rs (se 1 (by rfl) ⟨23339, by rfl⟩) R46679
theorem R227731 : Reach 227731 := rs (se 1 (by rfl) ⟨170798, by rfl⟩) R341597
theorem R162233 : Reach 162233 := rs (se 2 (by rfl) ⟨60837, by rfl⟩) R121675
theorem R31163 : Reach 31163 := rs (se 1 (by rfl) ⟨23372, by rfl⟩) R46745
theorem R31239 : Reach 31239 := rs (se 1 (by rfl) ⟨23429, by rfl⟩) R46859
theorem R31247 : Reach 31247 := rs (se 1 (by rfl) ⟨23435, by rfl⟩) R46871
theorem R31291 : Reach 31291 := rs (se 1 (by rfl) ⟨23468, by rfl⟩) R46937
theorem R31367 : Reach 31367 := rs (se 1 (by rfl) ⟨23525, by rfl⟩) R47051
theorem R31375 : Reach 31375 := rs (se 1 (by rfl) ⟨23531, by rfl⟩) R47063
theorem R31419 : Reach 31419 := rs (se 1 (by rfl) ⟨23564, by rfl⟩) R47129
theorem R31495 : Reach 31495 := rs (se 1 (by rfl) ⟨23621, by rfl⟩) R47243
theorem R31503 : Reach 31503 := rs (se 1 (by rfl) ⟨23627, by rfl⟩) R47255
theorem R64289 : Reach 64289 := rs (se 2 (by rfl) ⟨24108, by rfl⟩) R48217
theorem R31547 : Reach 31547 := rs (se 1 (by rfl) ⟨23660, by rfl⟩) R47321
theorem R97139 : Reach 97139 := rs (se 1 (by rfl) ⟨72854, by rfl⟩) R145709
theorem R31623 : Reach 31623 := rs (se 1 (by rfl) ⟨23717, by rfl⟩) R47435
theorem R31631 : Reach 31631 := rs (se 1 (by rfl) ⟨23723, by rfl⟩) R47447
theorem R31675 : Reach 31675 := rs (se 1 (by rfl) ⟨23756, by rfl⟩) R47513
theorem R31751 : Reach 31751 := rs (se 1 (by rfl) ⟨23813, by rfl⟩) R47627
theorem R31759 : Reach 31759 := rs (se 1 (by rfl) ⟨23819, by rfl⟩) R47639
theorem R31803 : Reach 31803 := rs (se 1 (by rfl) ⟨23852, by rfl⟩) R47705
theorem R64631 : Reach 64631 := rs (se 1 (by rfl) ⟨48473, by rfl⟩) R96947
theorem R31879 : Reach 31879 := rs (se 1 (by rfl) ⟨23909, by rfl⟩) R47819
theorem R31887 : Reach 31887 := rs (se 1 (by rfl) ⟨23915, by rfl⟩) R47831
theorem R31931 : Reach 31931 := rs (se 1 (by rfl) ⟨23948, by rfl⟩) R47897
theorem R32007 : Reach 32007 := rs (se 1 (by rfl) ⟨24005, by rfl⟩) R48011
theorem R32015 : Reach 32015 := rs (se 1 (by rfl) ⟨24011, by rfl⟩) R48023
theorem R32059 : Reach 32059 := rs (se 1 (by rfl) ⟨24044, by rfl⟩) R48089
theorem R97595 : Reach 97595 := rs (se 1 (by rfl) ⟨73196, by rfl⟩) R146393
theorem R32135 : Reach 32135 := rs (se 1 (by rfl) ⟨24101, by rfl⟩) R48203
theorem R32143 : Reach 32143 := rs (se 1 (by rfl) ⟨24107, by rfl⟩) R48215
theorem R32187 : Reach 32187 := rs (se 1 (by rfl) ⟨24140, by rfl⟩) R48281
theorem R32263 : Reach 32263 := rs (se 1 (by rfl) ⟨24197, by rfl⟩) R48395
theorem R32271 : Reach 32271 := rs (se 1 (by rfl) ⟨24203, by rfl⟩) R48407
theorem R32315 : Reach 32315 := rs (se 1 (by rfl) ⟨24236, by rfl⟩) R48473
theorem R32391 : Reach 32391 := rs (se 1 (by rfl) ⟨24293, by rfl⟩) R48587
theorem R32399 : Reach 32399 := rs (se 1 (by rfl) ⟨24299, by rfl⟩) R48599
theorem R32443 : Reach 32443 := rs (se 1 (by rfl) ⟨24332, by rfl⟩) R48665
theorem R32519 : Reach 32519 := rs (se 1 (by rfl) ⟨24389, by rfl⟩) R48779
theorem R32527 : Reach 32527 := rs (se 1 (by rfl) ⟨24395, by rfl⟩) R48791
theorem R32571 : Reach 32571 := rs (se 1 (by rfl) ⟨24428, by rfl⟩) R48857
theorem R32647 : Reach 32647 := rs (se 1 (by rfl) ⟨24485, by rfl⟩) R48971
theorem R32655 : Reach 32655 := rs (se 1 (by rfl) ⟨24491, by rfl⟩) R48983
theorem R32699 : Reach 32699 := rs (se 1 (by rfl) ⟨24524, by rfl⟩) R49049
theorem R32807 : Reach 32807 := rs (se 1 (by rfl) ⟨24605, by rfl⟩) R49211
theorem R131129 : Reach 131129 := rs (se 2 (by rfl) ⟨49173, by rfl⟩) R98347
theorem R32847 : Reach 32847 := rs (se 1 (by rfl) ⟨24635, by rfl⟩) R49271
theorem R32891 : Reach 32891 := rs (se 1 (by rfl) ⟨24668, by rfl⟩) R49337
theorem R360611 : Reach 360611 := rs (se 1 (by rfl) ⟨270458, by rfl⟩) R540917
theorem R32967 : Reach 32967 := rs (se 1 (by rfl) ⟨24725, by rfl⟩) R49451
theorem R98621 : Reach 98621 := rs (se 3 (by rfl) ⟨18491, by rfl⟩) R36983
theorem R33119 : Reach 33119 := rs (se 1 (by rfl) ⟨24839, by rfl⟩) R49679
theorem R33199 : Reach 33199 := rs (se 1 (by rfl) ⟨24899, by rfl⟩) R49799
theorem R33243 : Reach 33243 := rs (se 1 (by rfl) ⟨24932, by rfl⟩) R49865
theorem R197153 : Reach 197153 := rs (se 2 (by rfl) ⟨73932, by rfl⟩) R147865
theorem R33319 : Reach 33319 := rs (se 1 (by rfl) ⟨24989, by rfl⟩) R49979
theorem R33359 : Reach 33359 := rs (se 1 (by rfl) ⟨25019, by rfl⟩) R50039
theorem R33403 : Reach 33403 := rs (se 1 (by rfl) ⟨25052, by rfl⟩) R50105
theorem R33479 : Reach 33479 := rs (se 1 (by rfl) ⟨25109, by rfl⟩) R50219
theorem R33631 : Reach 33631 := rs (se 1 (by rfl) ⟨25223, by rfl⟩) R50447
theorem R33711 : Reach 33711 := rs (se 1 (by rfl) ⟨25283, by rfl⟩) R50567
theorem R66491 : Reach 66491 := rs (se 1 (by rfl) ⟨49868, by rfl⟩) R99737
theorem R33755 : Reach 33755 := rs (se 1 (by rfl) ⟨25316, by rfl⟩) R50633
theorem R99343 : Reach 99343 := rs (se 1 (by rfl) ⟨74507, by rfl⟩) R149015
theorem R590867 : Reach 590867 := rs (se 1 (by rfl) ⟨443150, by rfl⟩) R886301
theorem R33831 : Reach 33831 := rs (se 1 (by rfl) ⟨25373, by rfl⟩) R50747
theorem R361523 : Reach 361523 := rs (se 1 (by rfl) ⟨271142, by rfl⟩) R542285
theorem R164915 : Reach 164915 := rs (se 1 (by rfl) ⟨123686, by rfl⟩) R247373
theorem R328769 : Reach 328769 := rs (se 2 (by rfl) ⟨123288, by rfl⟩) R246577
theorem R33871 : Reach 33871 := rs (se 1 (by rfl) ⟨25403, by rfl⟩) R50807
theorem R99407 : Reach 99407 := rs (se 1 (by rfl) ⟨74555, by rfl⟩) R149111
theorem R33915 : Reach 33915 := rs (se 1 (by rfl) ⟨25436, by rfl⟩) R50873
theorem R33991 : Reach 33991 := rs (se 1 (by rfl) ⟨25493, by rfl⟩) R50987
theorem R34143 : Reach 34143 := rs (se 1 (by rfl) ⟨25607, by rfl⟩) R51215
theorem R99689 : Reach 99689 := rs (se 2 (by rfl) ⟨37383, by rfl⟩) R74767
theorem R34223 : Reach 34223 := rs (se 1 (by rfl) ⟨25667, by rfl⟩) R51335
theorem R34267 : Reach 34267 := rs (se 1 (by rfl) ⟨25700, by rfl⟩) R51401
theorem R34343 : Reach 34343 := rs (se 1 (by rfl) ⟨25757, by rfl⟩) R51515
theorem R34383 : Reach 34383 := rs (se 1 (by rfl) ⟨25787, by rfl⟩) R51575
theorem R34427 : Reach 34427 := rs (se 1 (by rfl) ⟨25820, by rfl⟩) R51641
theorem R34503 : Reach 34503 := rs (se 1 (by rfl) ⟨25877, by rfl⟩) R51755
theorem R34655 : Reach 34655 := rs (se 1 (by rfl) ⟨25991, by rfl⟩) R51983
theorem R395117 : Reach 395117 := rs (se 3 (by rfl) ⟨74084, by rfl⟩) R148169
theorem R34735 : Reach 34735 := rs (se 1 (by rfl) ⟨26051, by rfl⟩) R52103
theorem R34779 : Reach 34779 := rs (se 1 (by rfl) ⟨26084, by rfl⟩) R52169
theorem R34855 : Reach 34855 := rs (se 1 (by rfl) ⟨26141, by rfl⟩) R52283
theorem R34895 : Reach 34895 := rs (se 1 (by rfl) ⟨26171, by rfl⟩) R52343
theorem R34939 : Reach 34939 := rs (se 1 (by rfl) ⟨26204, by rfl⟩) R52409
theorem R35015 : Reach 35015 := rs (se 1 (by rfl) ⟨26261, by rfl⟩) R52523
theorem R35167 : Reach 35167 := rs (se 1 (by rfl) ⟨26375, by rfl⟩) R52751
theorem R35291 : Reach 35291 := rs (se 1 (by rfl) ⟨26468, by rfl⟩) R52937
theorem R133613 : Reach 133613 := rs (se 3 (by rfl) ⟨25052, by rfl⟩) R50105
theorem R363041 : Reach 363041 := rs (se 2 (by rfl) ⟨136140, by rfl⟩) R272281
theorem R166535 : Reach 166535 := rs (se 1 (by rfl) ⟨124901, by rfl⟩) R249803
theorem R35527 : Reach 35527 := rs (se 1 (by rfl) ⟨26645, by rfl⟩) R53291
theorem R265037 : Reach 265037 := rs (se 3 (by rfl) ⟨49694, by rfl⟩) R99389
theorem R68447 : Reach 68447 := rs (se 1 (by rfl) ⟨51335, by rfl⟩) R102671
theorem R68627 : Reach 68627 := rs (se 1 (by rfl) ⟨51470, by rfl⟩) R102941
theorem R592919 : Reach 592919 := rs (se 1 (by rfl) ⟨444689, by rfl⟩) R889379
theorem R134297 : Reach 134297 := rs (se 2 (by rfl) ⟨50361, by rfl⟩) R100723
theorem R36391 : Reach 36391 := rs (se 1 (by rfl) ⟨27293, by rfl⟩) R54587
theorem R200657 : Reach 200657 := rs (se 2 (by rfl) ⟨75246, by rfl⟩) R150493
theorem R430109 : Reach 430109 := rs (se 3 (by rfl) ⟨80645, by rfl⟩) R161291
theorem R167993 : Reach 167993 := rs (se 2 (by rfl) ⟨62997, by rfl⟩) R125995
theorem R201113 : Reach 201113 := rs (se 2 (by rfl) ⟨75417, by rfl⟩) R150835
theorem R70343 : Reach 70343 := rs (se 1 (by rfl) ⟨52757, by rfl⟩) R105515
theorem R398033 : Reach 398033 := rs (se 2 (by rfl) ⟨149262, by rfl⟩) R298525
theorem R103439 : Reach 103439 := rs (se 1 (by rfl) ⟨77579, by rfl⟩) R155159
theorem R38011 : Reach 38011 := rs (se 1 (by rfl) ⟨28508, by rfl⟩) R57017
theorem R464089 : Reach 464089 := rs (se 2 (by rfl) ⟨174033, by rfl⟩) R348067
theorem R71207 : Reach 71207 := rs (se 1 (by rfl) ⟨53405, by rfl⟩) R106811
theorem R38479 : Reach 38479 := rs (se 1 (by rfl) ⟨28859, by rfl⟩) R57719
theorem R71531 : Reach 71531 := rs (se 1 (by rfl) ⟨53648, by rfl⟩) R107297
theorem R71585 : Reach 71585 := rs (se 2 (by rfl) ⟨26844, by rfl⟩) R53689
theorem R38839 : Reach 38839 := rs (se 1 (by rfl) ⟨29129, by rfl⟩) R58259
theorem R38875 : Reach 38875 := rs (se 1 (by rfl) ⟨29156, by rfl⟩) R58313
theorem R170099 : Reach 170099 := rs (se 1 (by rfl) ⟨127574, by rfl⟩) R255149
theorem R202981 : Reach 202981 := rs (se 4 (by rfl) ⟨19029, by rfl⟩) R38059
theorem R71927 : Reach 71927 := rs (se 1 (by rfl) ⟨53945, by rfl⟩) R107891
theorem R39343 : Reach 39343 := rs (se 1 (by rfl) ⟨29507, by rfl⟩) R59015
theorem R105083 : Reach 105083 := rs (se 1 (by rfl) ⟨78812, by rfl⟩) R157625
theorem R105095 : Reach 105095 := rs (se 1 (by rfl) ⟨78821, by rfl⟩) R157643
theorem R793273 : Reach 793273 := rs (se 2 (by rfl) ⟨297477, by rfl⟩) R594955
theorem R105209 : Reach 105209 := rs (se 2 (by rfl) ⟨39453, by rfl⟩) R78907
theorem R105245 : Reach 105245 := rs (se 3 (by rfl) ⟨19733, by rfl⟩) R39467
theorem R105259 : Reach 105259 := rs (se 1 (by rfl) ⟨78944, by rfl⟩) R157889
theorem R72521 : Reach 72521 := rs (se 2 (by rfl) ⟨27195, by rfl⟩) R54391
theorem R597071 : Reach 597071 := rs (se 1 (by rfl) ⟨447803, by rfl⟩) R895607
theorem R40135 : Reach 40135 := rs (se 1 (by rfl) ⟨30101, by rfl⟩) R60203
theorem R105947 : Reach 105947 := rs (se 1 (by rfl) ⟨79460, by rfl⟩) R158921
theorem R73313 : Reach 73313 := rs (se 2 (by rfl) ⟨27492, by rfl⟩) R54985
theorem R171719 : Reach 171719 := rs (se 1 (by rfl) ⟨128789, by rfl⟩) R257579
theorem R73655 : Reach 73655 := rs (se 1 (by rfl) ⟨55241, by rfl⟩) R110483
theorem R106649 : Reach 106649 := rs (se 2 (by rfl) ⟨39993, by rfl⟩) R79987
theorem R139421 : Reach 139421 := rs (se 3 (by rfl) ⟨26141, by rfl⟩) R52283
theorem R41323 : Reach 41323 := rs (se 1 (by rfl) ⟨30992, by rfl⟩) R61985
theorem R74249 : Reach 74249 := rs (se 2 (by rfl) ⟨27843, by rfl⟩) R55687
theorem R303641 : Reach 303641 := rs (se 2 (by rfl) ⟨113865, by rfl⟩) R227731
theorem R238139 : Reach 238139 := rs (se 1 (by rfl) ⟨178604, by rfl⟩) R357209
theorem R140105 : Reach 140105 := rs (se 2 (by rfl) ⟨52539, by rfl⟩) R105079
theorem R74591 : Reach 74591 := rs (se 1 (by rfl) ⟨55943, by rfl⟩) R111887
theorem R205715 : Reach 205715 := rs (se 1 (by rfl) ⟨154286, by rfl⟩) R308573
theorem R861131 : Reach 861131 := rs (se 1 (by rfl) ⟨645848, by rfl⟩) R1291697
theorem R238565 : Reach 238565 := rs (se 4 (by rfl) ⟨22365, by rfl⟩) R44731
theorem R74771 : Reach 74771 := rs (se 1 (by rfl) ⟨56078, by rfl⟩) R112157
theorem R468017 : Reach 468017 := rs (se 2 (by rfl) ⟨175506, by rfl⟩) R351013
theorem R533749 : Reach 533749 := rs (se 5 (by rfl) ⟨25019, by rfl⟩) R50039
theorem R107837 : Reach 107837 := rs (se 3 (by rfl) ⟨20219, by rfl⟩) R40439
theorem R75113 : Reach 75113 := rs (se 2 (by rfl) ⟨28167, by rfl⟩) R56335
theorem R140687 : Reach 140687 := rs (se 1 (by rfl) ⟨105515, by rfl⟩) R211031
theorem R42535 : Reach 42535 := rs (se 1 (by rfl) ⟨31901, by rfl⟩) R63803
theorem R108155 : Reach 108155 := rs (se 1 (by rfl) ⟨81116, by rfl⟩) R162233
theorem R75403 : Reach 75403 := rs (se 1 (by rfl) ⟨56552, by rfl⟩) R113105
theorem R206651 : Reach 206651 := rs (se 1 (by rfl) ⟨154988, by rfl⟩) R309977
theorem R42859 : Reach 42859 := rs (se 1 (by rfl) ⟨32144, by rfl⟩) R64289
theorem R75707 : Reach 75707 := rs (se 1 (by rfl) ⟨56780, by rfl⟩) R113561
theorem R75833 : Reach 75833 := rs (se 2 (by rfl) ⟨28437, by rfl⟩) R56875
theorem R43087 : Reach 43087 := rs (se 1 (by rfl) ⟨32315, by rfl⟩) R64631
theorem R632933 : Reach 632933 := rs (se 4 (by rfl) ⟨59337, by rfl⟩) R118675
theorem R108701 : Reach 108701 := rs (se 3 (by rfl) ⟨20381, by rfl⟩) R40763
theorem R239773 : Reach 239773 := rs (se 3 (by rfl) ⟨44957, by rfl⟩) R89915
theorem R76175 : Reach 76175 := rs (se 1 (by rfl) ⟨57131, by rfl⟩) R114263
theorem R403865 : Reach 403865 := rs (se 2 (by rfl) ⟨151449, by rfl⟩) R302899
theorem R109001 : Reach 109001 := rs (se 2 (by rfl) ⟨40875, by rfl⟩) R81751
theorem R76427 : Reach 76427 := rs (se 1 (by rfl) ⟨57320, by rfl⟩) R114641
theorem R109241 : Reach 109241 := rs (se 2 (by rfl) ⟨40965, by rfl⟩) R81931
theorem R76499 : Reach 76499 := rs (se 1 (by rfl) ⟨57374, by rfl⟩) R114749
theorem R109487 : Reach 109487 := rs (se 1 (by rfl) ⟨82115, by rfl⟩) R164231
theorem R76879 : Reach 76879 := rs (se 1 (by rfl) ⟨57659, by rfl⟩) R115319
theorem R44155 : Reach 44155 := rs (se 1 (by rfl) ⟨33116, by rfl⟩) R66233
theorem R109835 : Reach 109835 := rs (se 1 (by rfl) ⟨82376, by rfl⟩) R164753
theorem R44383 : Reach 44383 := rs (se 1 (by rfl) ⟨33287, by rfl⟩) R66575
theorem R110105 : Reach 110105 := rs (se 2 (by rfl) ⟨41289, by rfl⟩) R82579
theorem R77435 : Reach 77435 := rs (se 1 (by rfl) ⟨58076, by rfl⟩) R116153
theorem R77561 : Reach 77561 := rs (se 2 (by rfl) ⟨29085, by rfl⟩) R58171
theorem R143147 : Reach 143147 := rs (se 1 (by rfl) ⟨107360, by rfl⟩) R214721
theorem R77831 : Reach 77831 := rs (se 1 (by rfl) ⟨58373, by rfl⟩) R116747
theorem R77903 : Reach 77903 := rs (se 1 (by rfl) ⟨58427, by rfl⟩) R116855
theorem R78209 : Reach 78209 := rs (se 2 (by rfl) ⟨29328, by rfl⟩) R58657
theorem R78299 : Reach 78299 := rs (se 1 (by rfl) ⟨58724, by rfl⟩) R117449
theorem R111239 : Reach 111239 := rs (se 1 (by rfl) ⟨83429, by rfl⟩) R166859
theorem R111293 : Reach 111293 := rs (se 3 (by rfl) ⟨20867, by rfl⟩) R41735
theorem R78551 : Reach 78551 := rs (se 1 (by rfl) ⟨58913, by rfl⟩) R117827
theorem R111455 : Reach 111455 := rs (se 1 (by rfl) ⟨83591, by rfl⟩) R167183
theorem R78767 : Reach 78767 := rs (se 1 (by rfl) ⟨59075, by rfl⟩) R118151
theorem R111617 : Reach 111617 := rs (se 2 (by rfl) ⟨41856, by rfl⟩) R83713
theorem R144463 : Reach 144463 := rs (se 1 (by rfl) ⟨108347, by rfl⟩) R216695
theorem R177551 : Reach 177551 := rs (se 1 (by rfl) ⟨133163, by rfl⟩) R266327
theorem R538001 : Reach 538001 := rs (se 2 (by rfl) ⟨201750, by rfl⟩) R403501
theorem R46715 : Reach 46715 := rs (se 1 (by rfl) ⟨35036, by rfl⟩) R70073
theorem R46841 : Reach 46841 := rs (se 2 (by rfl) ⟨17565, by rfl⟩) R35131
theorem R112427 : Reach 112427 := rs (se 1 (by rfl) ⟨84320, by rfl⟩) R168641
theorem R46943 : Reach 46943 := rs (se 1 (by rfl) ⟨35207, by rfl⟩) R70415
theorem R46955 : Reach 46955 := rs (se 1 (by rfl) ⟨35216, by rfl⟩) R70433
theorem R276517 : Reach 276517 := rs (se 4 (by rfl) ⟨25923, by rfl⟩) R51847
theorem R112697 : Reach 112697 := rs (se 2 (by rfl) ⟨42261, by rfl⟩) R84523
theorem R47183 : Reach 47183 := rs (se 1 (by rfl) ⟨35387, by rfl⟩) R70775
theorem R47303 : Reach 47303 := rs (se 1 (by rfl) ⟨35477, by rfl⟩) R70955
theorem R145675 : Reach 145675 := rs (se 1 (by rfl) ⟨109256, by rfl⟩) R218513
theorem R47465 : Reach 47465 := rs (se 2 (by rfl) ⟨17799, by rfl⟩) R35599
theorem R113021 : Reach 113021 := rs (se 3 (by rfl) ⟨21191, by rfl⟩) R42383
theorem R47543 : Reach 47543 := rs (se 1 (by rfl) ⟨35657, by rfl⟩) R71315
theorem R47579 : Reach 47579 := rs (se 1 (by rfl) ⟨35684, by rfl⟩) R71369
theorem R80347 : Reach 80347 := rs (se 1 (by rfl) ⟨60260, by rfl⟩) R120521
theorem R80423 : Reach 80423 := rs (se 1 (by rfl) ⟨60317, by rfl⟩) R120635
theorem R113291 : Reach 113291 := rs (se 1 (by rfl) ⟨84968, by rfl⟩) R169937
theorem R80747 : Reach 80747 := rs (se 1 (by rfl) ⟨60560, by rfl⟩) R121121
theorem R80801 : Reach 80801 := rs (se 2 (by rfl) ⟨30300, by rfl⟩) R60601
theorem R48047 : Reach 48047 := rs (se 1 (by rfl) ⟨36035, by rfl⟩) R72071
theorem R48137 : Reach 48137 := rs (se 2 (by rfl) ⟨18051, by rfl⟩) R36103
theorem R48167 : Reach 48167 := rs (se 1 (by rfl) ⟨36125, by rfl⟩) R72251
theorem R48251 : Reach 48251 := rs (se 1 (by rfl) ⟨36188, by rfl⟩) R72377
theorem R48377 : Reach 48377 := rs (se 2 (by rfl) ⟨18141, by rfl⟩) R36283
theorem R48479 : Reach 48479 := rs (se 1 (by rfl) ⟨36359, by rfl⟩) R72719
theorem R48491 : Reach 48491 := rs (se 1 (by rfl) ⟨36368, by rfl⟩) R72737
theorem R81395 : Reach 81395 := rs (se 1 (by rfl) ⟨61046, by rfl⟩) R122093
theorem R114209 : Reach 114209 := rs (se 2 (by rfl) ⟨42828, by rfl⟩) R85657
theorem R572993 : Reach 572993 := rs (se 2 (by rfl) ⟨214872, by rfl⟩) R429745
theorem R48719 : Reach 48719 := rs (se 1 (by rfl) ⟨36539, by rfl⟩) R73079
theorem R147133 : Reach 147133 := rs (se 3 (by rfl) ⟨27587, by rfl⟩) R55175
theorem R81607 : Reach 81607 := rs (se 1 (by rfl) ⟨61205, by rfl⟩) R122411
theorem R48839 : Reach 48839 := rs (se 1 (by rfl) ⟨36629, by rfl⟩) R73259
theorem R179927 : Reach 179927 := rs (se 1 (by rfl) ⟨134945, by rfl⟩) R269891
theorem R114425 : Reach 114425 := rs (se 2 (by rfl) ⟨42909, by rfl⟩) R85819
theorem R49001 : Reach 49001 := rs (se 2 (by rfl) ⟨18375, by rfl⟩) R36751
theorem R49079 : Reach 49079 := rs (se 1 (by rfl) ⟨36809, by rfl⟩) R73619
theorem R49115 : Reach 49115 := rs (se 1 (by rfl) ⟨36836, by rfl⟩) R73673
theorem R114695 : Reach 114695 := rs (se 1 (by rfl) ⟨86021, by rfl⟩) R172043
theorem R213029 : Reach 213029 := rs (se 4 (by rfl) ⟨19971, by rfl⟩) R39943
theorem R147545 : Reach 147545 := rs (se 2 (by rfl) ⟨55329, by rfl⟩) R110659
theorem R114803 : Reach 114803 := rs (se 1 (by rfl) ⟨86102, by rfl⟩) R172205
theorem R49481 : Reach 49481 := rs (se 2 (by rfl) ⟨18555, by rfl⟩) R37111
theorem R115073 : Reach 115073 := rs (se 2 (by rfl) ⟨43152, by rfl⟩) R86305
theorem R49583 : Reach 49583 := rs (se 1 (by rfl) ⟨37187, by rfl⟩) R74375
theorem R49595 : Reach 49595 := rs (se 1 (by rfl) ⟨37196, by rfl⟩) R74393
theorem R115181 : Reach 115181 := rs (se 3 (by rfl) ⟨21596, by rfl⟩) R43193
theorem R49673 : Reach 49673 := rs (se 2 (by rfl) ⟨18627, by rfl⟩) R37255
theorem R49703 : Reach 49703 := rs (se 1 (by rfl) ⟨37277, by rfl⟩) R74555
theorem R49721 : Reach 49721 := rs (se 2 (by rfl) ⟨18645, by rfl⟩) R37291
theorem R82529 : Reach 82529 := rs (se 2 (by rfl) ⟨30948, by rfl⟩) R61897
theorem R49787 : Reach 49787 := rs (se 1 (by rfl) ⟨37340, by rfl⟩) R74681
theorem R49835 : Reach 49835 := rs (se 1 (by rfl) ⟨37376, by rfl⟩) R74753
theorem R49913 : Reach 49913 := rs (se 2 (by rfl) ⟨18717, by rfl⟩) R37435
theorem R50015 : Reach 50015 := rs (se 1 (by rfl) ⟨37511, by rfl⟩) R75023
theorem R50027 : Reach 50027 := rs (se 1 (by rfl) ⟨37520, by rfl⟩) R75041
theorem R50063 : Reach 50063 := rs (se 1 (by rfl) ⟨37547, by rfl⟩) R75095
theorem R50183 : Reach 50183 := rs (se 1 (by rfl) ⟨37637, by rfl⟩) R75275
theorem R50255 : Reach 50255 := rs (se 1 (by rfl) ⟨37691, by rfl⟩) R75383
theorem R115793 : Reach 115793 := rs (se 2 (by rfl) ⟨43422, by rfl⟩) R86845
theorem R115883 : Reach 115883 := rs (se 1 (by rfl) ⟨86912, by rfl⟩) R173825
theorem R50375 : Reach 50375 := rs (se 1 (by rfl) ⟨37781, by rfl⟩) R75563
theorem R50423 : Reach 50423 := rs (se 1 (by rfl) ⟨37817, by rfl⟩) R75635
theorem R50537 : Reach 50537 := rs (se 2 (by rfl) ⟨18951, by rfl⟩) R37903
theorem R50615 : Reach 50615 := rs (se 1 (by rfl) ⟨37961, by rfl⟩) R75923
theorem R83419 : Reach 83419 := rs (se 1 (by rfl) ⟨62564, by rfl⟩) R125129
theorem R50651 : Reach 50651 := rs (se 1 (by rfl) ⟨37988, by rfl⟩) R75977
theorem R83443 : Reach 83443 := rs (se 1 (by rfl) ⟨62582, by rfl⟩) R125165
theorem R214667 : Reach 214667 := rs (se 1 (by rfl) ⟨161000, by rfl⟩) R322001
theorem R116423 : Reach 116423 := rs (se 1 (by rfl) ⟨87317, by rfl⟩) R174635
theorem R444203 : Reach 444203 := rs (se 1 (by rfl) ⟨333152, by rfl⟩) R666305
theorem R51017 : Reach 51017 := rs (se 2 (by rfl) ⟨19131, by rfl⟩) R38263
theorem R51119 : Reach 51119 := rs (se 1 (by rfl) ⟨38339, by rfl⟩) R76679
theorem R51131 : Reach 51131 := rs (se 1 (by rfl) ⟨38348, by rfl⟩) R76697
theorem R149435 : Reach 149435 := rs (se 1 (by rfl) ⟨112076, by rfl⟩) R224153
theorem R51209 : Reach 51209 := rs (se 2 (by rfl) ⟨19203, by rfl⟩) R38407
theorem R83987 : Reach 83987 := rs (se 1 (by rfl) ⟨62990, by rfl⟩) R125981
theorem R51239 : Reach 51239 := rs (se 1 (by rfl) ⟨38429, by rfl⟩) R76859
theorem R51257 : Reach 51257 := rs (se 2 (by rfl) ⟨19221, by rfl⟩) R38443
theorem R51323 : Reach 51323 := rs (se 1 (by rfl) ⟨38492, by rfl⟩) R76985
theorem R51371 : Reach 51371 := rs (se 1 (by rfl) ⟨38528, by rfl⟩) R77057
theorem R51449 : Reach 51449 := rs (se 2 (by rfl) ⟨19293, by rfl⟩) R38587
theorem R51551 : Reach 51551 := rs (se 1 (by rfl) ⟨38663, by rfl⟩) R77327
theorem R51563 : Reach 51563 := rs (se 1 (by rfl) ⟨38672, by rfl⟩) R77345
theorem R51599 : Reach 51599 := rs (se 1 (by rfl) ⟨38699, by rfl⟩) R77399
theorem R51719 : Reach 51719 := rs (se 1 (by rfl) ⟨38789, by rfl⟩) R77579
theorem R248345 : Reach 248345 := rs (se 2 (by rfl) ⟨93129, by rfl⟩) R186259
theorem R117287 : Reach 117287 := rs (se 1 (by rfl) ⟨87965, by rfl⟩) R175931
theorem R182843 : Reach 182843 := rs (se 1 (by rfl) ⟨137132, by rfl⟩) R274265
theorem R51791 : Reach 51791 := rs (se 1 (by rfl) ⟨38843, by rfl⟩) R77687
theorem R51835 : Reach 51835 := rs (se 1 (by rfl) ⟨38876, by rfl⟩) R77753
theorem R117395 : Reach 117395 := rs (se 1 (by rfl) ⟨88046, by rfl⟩) R176093
theorem R51911 : Reach 51911 := rs (se 1 (by rfl) ⟨38933, by rfl⟩) R77867
theorem R84691 : Reach 84691 := rs (se 1 (by rfl) ⟨63518, by rfl⟩) R127037
theorem R51959 : Reach 51959 := rs (se 1 (by rfl) ⟨38969, by rfl⟩) R77939
theorem R52073 : Reach 52073 := rs (se 2 (by rfl) ⟨19527, by rfl⟩) R39055
theorem R117611 : Reach 117611 := rs (se 1 (by rfl) ⟨88208, by rfl⟩) R176417
theorem R117665 : Reach 117665 := rs (se 2 (by rfl) ⟨44124, by rfl⟩) R88249
theorem R52151 : Reach 52151 := rs (se 1 (by rfl) ⟨39113, by rfl⟩) R78227
theorem R52187 : Reach 52187 := rs (se 1 (by rfl) ⟨39140, by rfl⟩) R78281
theorem R52553 : Reach 52553 := rs (se 2 (by rfl) ⟨19707, by rfl⟩) R39415
theorem R85391 : Reach 85391 := rs (se 1 (by rfl) ⟨64043, by rfl⟩) R128087
theorem R52655 : Reach 52655 := rs (se 1 (by rfl) ⟨39491, by rfl⟩) R78983
theorem R52663 : Reach 52663 := rs (se 1 (by rfl) ⟨39497, by rfl⟩) R78995
theorem R52667 : Reach 52667 := rs (se 1 (by rfl) ⟨39500, by rfl⟩) R79001
theorem R118259 : Reach 118259 := rs (se 1 (by rfl) ⟨88694, by rfl⟩) R177389
theorem R118331 : Reach 118331 := rs (se 1 (by rfl) ⟨88748, by rfl⟩) R177497
theorem R52859 : Reach 52859 := rs (se 1 (by rfl) ⟨39644, by rfl⟩) R79289
theorem R53065 : Reach 53065 := rs (se 2 (by rfl) ⟨19899, by rfl⟩) R39799
theorem R53257 : Reach 53257 := rs (se 2 (by rfl) ⟨19971, by rfl⟩) R39943
theorem R53419 : Reach 53419 := rs (se 1 (by rfl) ⟨40064, by rfl⟩) R80129
theorem R118979 : Reach 118979 := rs (se 1 (by rfl) ⟨89234, by rfl⟩) R178469
theorem R53723 : Reach 53723 := rs (se 1 (by rfl) ⟨40292, by rfl⟩) R80585
theorem R119495 : Reach 119495 := rs (se 1 (by rfl) ⟨89621, by rfl⟩) R179243
theorem R53959 : Reach 53959 := rs (se 1 (by rfl) ⟨40469, by rfl⟩) R80939
theorem R1495907 : Reach 1495907 := rs (se 1 (by rfl) ⟨1121930, by rfl⟩) R2243861
theorem R54121 : Reach 54121 := rs (se 2 (by rfl) ⟨20295, by rfl⟩) R40591
theorem R119713 : Reach 119713 := rs (se 2 (by rfl) ⟨44892, by rfl⟩) R89785
theorem R251261 : Reach 251261 := rs (se 3 (by rfl) ⟨47111, by rfl⟩) R94223
theorem R87439 : Reach 87439 := rs (se 1 (by rfl) ⟨65579, by rfl⟩) R131159
theorem R54715 : Reach 54715 := rs (se 1 (by rfl) ⟨41036, by rfl⟩) R82073
theorem R26891747 : Reach 26891747 := rs (se 1 (by rfl) ⟨20168810, by rfl⟩) R40337621
theorem R54823 : Reach 54823 := rs (se 1 (by rfl) ⟨41117, by rfl⟩) R82235
theorem R284305 : Reach 284305 := rs (se 2 (by rfl) ⟨106614, by rfl⟩) R213229
theorem R120467 : Reach 120467 := rs (se 1 (by rfl) ⟨90350, by rfl⟩) R180701
theorem R448199 : Reach 448199 := rs (se 1 (by rfl) ⟨336149, by rfl⟩) R672299
theorem R87763 : Reach 87763 := rs (se 1 (by rfl) ⟨65822, by rfl⟩) R131645
theorem R186077 : Reach 186077 := rs (se 3 (by rfl) ⟨34889, by rfl⟩) R69779
theorem R120649 : Reach 120649 := rs (se 2 (by rfl) ⟨45243, by rfl⟩) R90487
theorem R55147 : Reach 55147 := rs (se 1 (by rfl) ⟨41360, by rfl⟩) R82721
theorem R186299 : Reach 186299 := rs (se 1 (by rfl) ⟨139724, by rfl⟩) R279449
theorem R55507 : Reach 55507 := rs (se 1 (by rfl) ⟨41630, by rfl⟩) R83261
theorem R711017 : Reach 711017 := rs (se 2 (by rfl) ⟨266631, by rfl⟩) R533263
theorem R88715 : Reach 88715 := rs (se 1 (by rfl) ⟨66536, by rfl⟩) R133073
theorem R449225 : Reach 449225 := rs (se 2 (by rfl) ⟨168459, by rfl⟩) R336919
theorem R56207 : Reach 56207 := rs (se 1 (by rfl) ⟨42155, by rfl⟩) R84311
theorem R154543 : Reach 154543 := rs (se 1 (by rfl) ⟨115907, by rfl⟩) R231815
theorem R56443 : Reach 56443 := rs (se 1 (by rfl) ⟨42332, by rfl⟩) R84665
theorem R56531 : Reach 56531 := rs (se 1 (by rfl) ⟨42398, by rfl⟩) R84797
theorem R122123 : Reach 122123 := rs (se 1 (by rfl) ⟨91592, by rfl⟩) R183185
theorem R56737 : Reach 56737 := rs (se 2 (by rfl) ⟨21276, by rfl⟩) R42553
theorem R56929 : Reach 56929 := rs (se 2 (by rfl) ⟨21348, by rfl⟩) R42697
theorem R220819 : Reach 220819 := rs (se 1 (by rfl) ⟨165614, by rfl⟩) R331229
theorem R122579 : Reach 122579 := rs (se 1 (by rfl) ⟨91934, by rfl⟩) R183869
theorem R89849 : Reach 89849 := rs (se 2 (by rfl) ⟨33693, by rfl⟩) R67387
theorem R188203 : Reach 188203 := rs (se 1 (by rfl) ⟨141152, by rfl⟩) R282305
theorem R57307 : Reach 57307 := rs (se 1 (by rfl) ⟨42980, by rfl⟩) R85961
theorem R516611 : Reach 516611 := rs (se 1 (by rfl) ⟨387458, by rfl⟩) R774917
theorem R57935 : Reach 57935 := rs (se 1 (by rfl) ⟨43451, by rfl⟩) R86903
theorem R58387 : Reach 58387 := rs (se 1 (by rfl) ⟨43790, by rfl⟩) R87581
theorem R91307 : Reach 91307 := rs (se 1 (by rfl) ⟨68480, by rfl⟩) R136961
theorem R58799 : Reach 58799 := rs (se 1 (by rfl) ⟨44099, by rfl⟩) R88199
theorem R255635 : Reach 255635 := rs (se 1 (by rfl) ⟨191726, by rfl⟩) R383453
theorem R59231 : Reach 59231 := rs (se 1 (by rfl) ⟨44423, by rfl⟩) R88847
theorem R157601 : Reach 157601 := rs (se 2 (by rfl) ⟨59100, by rfl⟩) R118201
theorem R125009 : Reach 125009 := rs (se 2 (by rfl) ⟨46878, by rfl⟩) R93757
theorem R125327 : Reach 125327 := rs (se 1 (by rfl) ⟨93995, by rfl⟩) R187991
theorem R518987 : Reach 518987 := rs (se 1 (by rfl) ⟨389240, by rfl⟩) R778481
theorem R715969 : Reach 715969 := rs (se 2 (by rfl) ⟨268488, by rfl⟩) R536977
theorem R126269 : Reach 126269 := rs (se 3 (by rfl) ⟨23675, by rfl⟩) R47351
theorem R191909 : Reach 191909 := rs (se 4 (by rfl) ⟨17991, by rfl⟩) R35983
theorem R61175 : Reach 61175 := rs (se 1 (by rfl) ⟨45881, by rfl⟩) R91763
theorem R61177 : Reach 61177 := rs (se 2 (by rfl) ⟨22941, by rfl⟩) R45883
theorem R159583 : Reach 159583 := rs (se 1 (by rfl) ⟨119687, by rfl⟩) R239375
theorem R192365 : Reach 192365 := rs (se 3 (by rfl) ⟨36068, by rfl⟩) R72137
theorem R454531 : Reach 454531 := rs (se 1 (by rfl) ⟨340898, by rfl⟩) R681797
theorem R61327 : Reach 61327 := rs (se 1 (by rfl) ⟨45995, by rfl⟩) R91991
theorem R192449 : Reach 192449 := rs (se 2 (by rfl) ⟨72168, by rfl⟩) R144337
theorem R94729 : Reach 94729 := rs (se 2 (by rfl) ⟨35523, by rfl⟩) R71047
theorem R193049 : Reach 193049 := rs (se 2 (by rfl) ⟨72393, by rfl⟩) R144787
theorem R324155 : Reach 324155 := rs (se 1 (by rfl) ⟨243116, by rfl⟩) R486233
theorem R62201 : Reach 62201 := rs (se 2 (by rfl) ⟨23325, by rfl⟩) R46651
theorem R881425 : Reach 881425 := rs (se 2 (by rfl) ⟨330534, by rfl⟩) R661069
theorem R160541 : Reach 160541 := rs (se 3 (by rfl) ⟨30101, by rfl⟩) R60203
theorem R914327 : Reach 914327 := rs (se 1 (by rfl) ⟨685745, by rfl⟩) R1371491
theorem R62383 : Reach 62383 := rs (se 1 (by rfl) ⟨46787, by rfl⟩) R93575
theorem R259037 : Reach 259037 := rs (se 3 (by rfl) ⟨48569, by rfl⟩) R97139
theorem R521873 : Reach 521873 := rs (se 2 (by rfl) ⟨195702, by rfl⟩) R391405
theorem R260111 : Reach 260111 := rs (se 1 (by rfl) ⟨195083, by rfl⟩) R390167
theorem R96335 : Reach 96335 := rs (se 1 (by rfl) ⟨72251, by rfl⟩) R144503
theorem R63659 : Reach 63659 := rs (se 1 (by rfl) ⟨47744, by rfl⟩) R95489
theorem R981233 : Reach 981233 := rs (se 2 (by rfl) ⟨367962, by rfl⟩) R735925
theorem R31151 : Reach 31151 := rs (se 1 (by rfl) ⟨23363, by rfl⟩) R46727
theorem R31175 : Reach 31175 := rs (se 1 (by rfl) ⟨23381, by rfl⟩) R46763
theorem R31195 : Reach 31195 := rs (se 1 (by rfl) ⟨23396, by rfl⟩) R46793
theorem R31271 : Reach 31271 := rs (se 1 (by rfl) ⟨23453, by rfl⟩) R46907
theorem R31311 : Reach 31311 := rs (se 1 (by rfl) ⟨23483, by rfl⟩) R46967
theorem R31327 : Reach 31327 := rs (se 1 (by rfl) ⟨23495, by rfl⟩) R46991
theorem R31355 : Reach 31355 := rs (se 1 (by rfl) ⟨23516, by rfl⟩) R47033
theorem R129671 : Reach 129671 := rs (se 1 (by rfl) ⟨97253, by rfl⟩) R194507
theorem R129683 : Reach 129683 := rs (se 1 (by rfl) ⟨97262, by rfl⟩) R194525
theorem R31407 : Reach 31407 := rs (se 1 (by rfl) ⟨23555, by rfl⟩) R47111
theorem R31431 : Reach 31431 := rs (se 1 (by rfl) ⟨23573, by rfl⟩) R47147
theorem R228041 : Reach 228041 := rs (se 2 (by rfl) ⟨85515, by rfl⟩) R171031
theorem R195281 : Reach 195281 := rs (se 2 (by rfl) ⟨73230, by rfl⟩) R146461
theorem R31451 : Reach 31451 := rs (se 1 (by rfl) ⟨23588, by rfl⟩) R47177
theorem R31527 : Reach 31527 := rs (se 1 (by rfl) ⟨23645, by rfl⟩) R47291
theorem R31567 : Reach 31567 := rs (se 1 (by rfl) ⟨23675, by rfl⟩) R47351
theorem R31583 : Reach 31583 := rs (se 1 (by rfl) ⟨23687, by rfl⟩) R47375
theorem R31611 : Reach 31611 := rs (se 1 (by rfl) ⟨23708, by rfl⟩) R47417
theorem R31663 : Reach 31663 := rs (se 1 (by rfl) ⟨23747, by rfl⟩) R47495
theorem R31687 : Reach 31687 := rs (se 1 (by rfl) ⟨23765, by rfl⟩) R47531
theorem R31707 : Reach 31707 := rs (se 1 (by rfl) ⟨23780, by rfl⟩) R47561
theorem R31783 : Reach 31783 := rs (se 1 (by rfl) ⟨23837, by rfl⟩) R47675
theorem R31823 : Reach 31823 := rs (se 1 (by rfl) ⟨23867, by rfl⟩) R47735
theorem R31839 : Reach 31839 := rs (se 1 (by rfl) ⟨23879, by rfl⟩) R47759
theorem R31867 : Reach 31867 := rs (se 1 (by rfl) ⟨23900, by rfl⟩) R47801
theorem R31919 : Reach 31919 := rs (se 1 (by rfl) ⟨23939, by rfl⟩) R47879
theorem R31943 : Reach 31943 := rs (se 1 (by rfl) ⟨23957, by rfl⟩) R47915
theorem R31963 : Reach 31963 := rs (se 1 (by rfl) ⟨23972, by rfl⟩) R47945
theorem R32039 : Reach 32039 := rs (se 1 (by rfl) ⟨24029, by rfl⟩) R48059
theorem R32079 : Reach 32079 := rs (se 1 (by rfl) ⟨24059, by rfl⟩) R48119
theorem R32095 : Reach 32095 := rs (se 1 (by rfl) ⟨24071, by rfl⟩) R48143
theorem R32123 : Reach 32123 := rs (se 1 (by rfl) ⟨24092, by rfl⟩) R48185
theorem R195965 : Reach 195965 := rs (se 3 (by rfl) ⟨36743, by rfl⟩) R73487
theorem R32175 : Reach 32175 := rs (se 1 (by rfl) ⟨24131, by rfl⟩) R48263
theorem R32199 : Reach 32199 := rs (se 1 (by rfl) ⟨24149, by rfl⟩) R48299
theorem R32219 : Reach 32219 := rs (se 1 (by rfl) ⟨24164, by rfl⟩) R48329
theorem R65033 : Reach 65033 := rs (se 2 (by rfl) ⟨24387, by rfl⟩) R48775
theorem R32295 : Reach 32295 := rs (se 1 (by rfl) ⟨24221, by rfl⟩) R48443
theorem R65063 : Reach 65063 := rs (se 1 (by rfl) ⟨48797, by rfl⟩) R97595
theorem R32335 : Reach 32335 := rs (se 1 (by rfl) ⟨24251, by rfl⟩) R48503
theorem R32351 : Reach 32351 := rs (se 1 (by rfl) ⟨24263, by rfl⟩) R48527
theorem R32379 : Reach 32379 := rs (se 1 (by rfl) ⟨24284, by rfl⟩) R48569
theorem R163475 : Reach 163475 := rs (se 1 (by rfl) ⟨122606, by rfl⟩) R245213
theorem R32431 : Reach 32431 := rs (se 1 (by rfl) ⟨24323, by rfl⟩) R48647
theorem R360125 : Reach 360125 := rs (se 3 (by rfl) ⟨67523, by rfl⟩) R135047
theorem R32455 : Reach 32455 := rs (se 1 (by rfl) ⟨24341, by rfl⟩) R48683
theorem R32475 : Reach 32475 := rs (se 1 (by rfl) ⟨24356, by rfl⟩) R48713
theorem R32551 : Reach 32551 := rs (se 1 (by rfl) ⟨24413, by rfl⟩) R48827
theorem R32591 : Reach 32591 := rs (se 1 (by rfl) ⟨24443, by rfl⟩) R48887
theorem R32607 : Reach 32607 := rs (se 1 (by rfl) ⟨24455, by rfl⟩) R48911
theorem R32635 : Reach 32635 := rs (se 1 (by rfl) ⟨24476, by rfl⟩) R48953
theorem R32687 : Reach 32687 := rs (se 1 (by rfl) ⟨24515, by rfl⟩) R49031
theorem R32711 : Reach 32711 := rs (se 1 (by rfl) ⟨24533, by rfl⟩) R49067
theorem R32731 : Reach 32731 := rs (se 1 (by rfl) ⟨24548, by rfl⟩) R49097
theorem R98363 : Reach 98363 := rs (se 1 (by rfl) ⟨73772, by rfl⟩) R147545
theorem R1474757 : Reach 1474757 := rs (se 4 (by rfl) ⟨138258, by rfl⟩) R276517
theorem R65747 : Reach 65747 := rs (se 1 (by rfl) ⟨49310, by rfl⟩) R98621
theorem R32987 : Reach 32987 := rs (se 1 (by rfl) ⟨24740, by rfl⟩) R49481
theorem R33055 : Reach 33055 := rs (se 1 (by rfl) ⟨24791, by rfl⟩) R49583
theorem R33063 : Reach 33063 := rs (se 1 (by rfl) ⟨24797, by rfl⟩) R49595
theorem R33115 : Reach 33115 := rs (se 1 (by rfl) ⟨24836, by rfl⟩) R49673
theorem R131435 : Reach 131435 := rs (se 1 (by rfl) ⟨98576, by rfl⟩) R197153
theorem R33135 : Reach 33135 := rs (se 1 (by rfl) ⟨24851, by rfl⟩) R49703
theorem R33147 : Reach 33147 := rs (se 1 (by rfl) ⟨24860, by rfl⟩) R49721
theorem R33191 : Reach 33191 := rs (se 1 (by rfl) ⟨24893, by rfl⟩) R49787
theorem R33223 : Reach 33223 := rs (se 1 (by rfl) ⟨24917, by rfl⟩) R49835
theorem R33275 : Reach 33275 := rs (se 1 (by rfl) ⟨24956, by rfl⟩) R49913
theorem R33343 : Reach 33343 := rs (se 1 (by rfl) ⟨25007, by rfl⟩) R50015
theorem R33351 : Reach 33351 := rs (se 1 (by rfl) ⟨25013, by rfl⟩) R50027
theorem R33375 : Reach 33375 := rs (se 1 (by rfl) ⟨25031, by rfl⟩) R50063
theorem R33455 : Reach 33455 := rs (se 1 (by rfl) ⟨25091, by rfl⟩) R50183
theorem R393911 : Reach 393911 := rs (se 1 (by rfl) ⟨295433, by rfl⟩) R590867
theorem R33503 : Reach 33503 := rs (se 1 (by rfl) ⟨25127, by rfl⟩) R50255
theorem R66271 : Reach 66271 := rs (se 1 (by rfl) ⟨49703, by rfl⟩) R99407
theorem R33583 : Reach 33583 := rs (se 1 (by rfl) ⟨25187, by rfl⟩) R50375
theorem R33615 : Reach 33615 := rs (se 1 (by rfl) ⟨25211, by rfl⟩) R50423
theorem R33691 : Reach 33691 := rs (se 1 (by rfl) ⟨25268, by rfl⟩) R50537
theorem R33743 : Reach 33743 := rs (se 1 (by rfl) ⟨25307, by rfl⟩) R50615
theorem R33767 : Reach 33767 := rs (se 1 (by rfl) ⟨25325, by rfl⟩) R50651
theorem R296135 : Reach 296135 := rs (se 1 (by rfl) ⟨222101, by rfl⟩) R444203
theorem R34011 : Reach 34011 := rs (se 1 (by rfl) ⟨25508, by rfl⟩) R51017
theorem R263411 : Reach 263411 := rs (se 1 (by rfl) ⟨197558, by rfl⟩) R395117
theorem R34079 : Reach 34079 := rs (se 1 (by rfl) ⟨25559, by rfl⟩) R51119
theorem R34087 : Reach 34087 := rs (se 1 (by rfl) ⟨25565, by rfl⟩) R51131
theorem R99623 : Reach 99623 := rs (se 1 (by rfl) ⟨74717, by rfl⟩) R149435
theorem R34139 : Reach 34139 := rs (se 1 (by rfl) ⟨25604, by rfl⟩) R51209
theorem R132457 : Reach 132457 := rs (se 2 (by rfl) ⟨49671, by rfl⟩) R99343
theorem R34159 : Reach 34159 := rs (se 1 (by rfl) ⟨25619, by rfl⟩) R51239
theorem R34171 : Reach 34171 := rs (se 1 (by rfl) ⟨25628, by rfl⟩) R51257
theorem R34215 : Reach 34215 := rs (se 1 (by rfl) ⟨25661, by rfl⟩) R51323
theorem R34247 : Reach 34247 := rs (se 1 (by rfl) ⟨25685, by rfl⟩) R51371
theorem R34299 : Reach 34299 := rs (se 1 (by rfl) ⟨25724, by rfl⟩) R51449
theorem R34367 : Reach 34367 := rs (se 1 (by rfl) ⟨25775, by rfl⟩) R51551
theorem R34375 : Reach 34375 := rs (se 1 (by rfl) ⟨25781, by rfl⟩) R51563
theorem R34399 : Reach 34399 := rs (se 1 (by rfl) ⟨25799, by rfl⟩) R51599
theorem R34479 : Reach 34479 := rs (se 1 (by rfl) ⟨25859, by rfl⟩) R51719
theorem R165563 : Reach 165563 := rs (se 1 (by rfl) ⟨124172, by rfl⟩) R248345
theorem R34527 : Reach 34527 := rs (se 1 (by rfl) ⟨25895, by rfl⟩) R51791
theorem R34607 : Reach 34607 := rs (se 1 (by rfl) ⟨25955, by rfl⟩) R51911
theorem R34639 : Reach 34639 := rs (se 1 (by rfl) ⟨25979, by rfl⟩) R51959
theorem R34715 : Reach 34715 := rs (se 1 (by rfl) ⟨26036, by rfl⟩) R52073
theorem R34767 : Reach 34767 := rs (se 1 (by rfl) ⟨26075, by rfl⟩) R52151
theorem R34791 : Reach 34791 := rs (se 1 (by rfl) ⟨26093, by rfl⟩) R52187
theorem R395279 : Reach 395279 := rs (se 1 (by rfl) ⟨296459, by rfl⟩) R592919
theorem R35035 : Reach 35035 := rs (se 1 (by rfl) ⟨26276, by rfl⟩) R52553
theorem R35103 : Reach 35103 := rs (se 1 (by rfl) ⟨26327, by rfl⟩) R52655
theorem R35111 : Reach 35111 := rs (se 1 (by rfl) ⟨26333, by rfl⟩) R52667
theorem R35239 : Reach 35239 := rs (se 1 (by rfl) ⟨26429, by rfl⟩) R52859
theorem R166373 : Reach 166373 := rs (se 4 (by rfl) ⟨15597, by rfl⟩) R31195
theorem R2296349 : Reach 2296349 := rs (se 3 (by rfl) ⟨430565, by rfl⟩) R861131
theorem R134075 : Reach 134075 := rs (se 1 (by rfl) ⟨100556, by rfl⟩) R201113
theorem R35815 : Reach 35815 := rs (se 1 (by rfl) ⟨26861, by rfl⟩) R53723
theorem R265355 : Reach 265355 := rs (se 1 (by rfl) ⟨199016, by rfl⟩) R398033
theorem R68959 : Reach 68959 := rs (se 1 (by rfl) ⟨51719, by rfl⟩) R103439
theorem R69113 : Reach 69113 := rs (se 2 (by rfl) ⟨25917, by rfl⟩) R51835
theorem R167507 : Reach 167507 := rs (se 1 (by rfl) ⟨125630, by rfl⟩) R251261
theorem R265837 : Reach 265837 := rs (se 3 (by rfl) ⟨49844, by rfl⟩) R99689
theorem R17927831 : Reach 17927831 := rs (se 1 (by rfl) ⟨13445873, by rfl⟩) R26891747
theorem R298799 : Reach 298799 := rs (se 1 (by rfl) ⟨224099, by rfl⟩) R448199
theorem R102505 : Reach 102505 := rs (se 2 (by rfl) ⟨38439, by rfl⟩) R76879
theorem R954625 : Reach 954625 := rs (se 2 (by rfl) ⟨357984, by rfl⟩) R715969
theorem R70055 : Reach 70055 := rs (se 1 (by rfl) ⟨52541, by rfl⟩) R105083
theorem R299483 : Reach 299483 := rs (se 1 (by rfl) ⟨224612, by rfl⟩) R449225
theorem R70139 : Reach 70139 := rs (se 1 (by rfl) ⟨52604, by rfl⟩) R105209
theorem R70163 : Reach 70163 := rs (se 1 (by rfl) ⟨52622, by rfl⟩) R105245
theorem R70217 : Reach 70217 := rs (se 2 (by rfl) ⟨26331, by rfl⟩) R52663
theorem R37471 : Reach 37471 := rs (se 1 (by rfl) ⟨28103, by rfl⟩) R56207
theorem R398047 : Reach 398047 := rs (se 1 (by rfl) ⟨298535, by rfl⟩) R597071
theorem R37687 : Reach 37687 := rs (se 1 (by rfl) ⟨28265, by rfl⟩) R56531
theorem R70631 : Reach 70631 := rs (se 1 (by rfl) ⟨52973, by rfl⟩) R105947
theorem R71009 : Reach 71009 := rs (se 2 (by rfl) ⟨26628, by rfl⟩) R53257
theorem R693629 : Reach 693629 := rs (se 3 (by rfl) ⟨130055, by rfl⟩) R260111
theorem R71099 : Reach 71099 := rs (se 1 (by rfl) ⟨53324, by rfl⟩) R106649
theorem R71225 : Reach 71225 := rs (se 2 (by rfl) ⟨26709, by rfl⟩) R53419
theorem R202427 : Reach 202427 := rs (se 1 (by rfl) ⟨151820, by rfl⟩) R303641
theorem R38623 : Reach 38623 := rs (se 1 (by rfl) ⟨28967, by rfl⟩) R57935
theorem R137143 : Reach 137143 := rs (se 1 (by rfl) ⟨102857, by rfl⟩) R205715
theorem R71891 : Reach 71891 := rs (se 1 (by rfl) ⟨53918, by rfl⟩) R107837
theorem R71945 : Reach 71945 := rs (se 2 (by rfl) ⟨26979, by rfl⟩) R53959
theorem R39199 : Reach 39199 := rs (se 1 (by rfl) ⟨29399, by rfl⟩) R58799
theorem R72103 : Reach 72103 := rs (se 1 (by rfl) ⟨54077, by rfl⟩) R108155
theorem R170423 : Reach 170423 := rs (se 1 (by rfl) ⟨127817, by rfl⟩) R255635
theorem R72161 : Reach 72161 := rs (se 2 (by rfl) ⟨27060, by rfl⟩) R54121
theorem R39487 : Reach 39487 := rs (se 1 (by rfl) ⟨29615, by rfl⟩) R59231
theorem R105067 : Reach 105067 := rs (se 1 (by rfl) ⟨78800, by rfl⟩) R157601
theorem R72467 : Reach 72467 := rs (se 1 (by rfl) ⟨54350, by rfl⟩) R108701
theorem R269243 : Reach 269243 := rs (se 1 (by rfl) ⟨201932, by rfl⟩) R403865
theorem R72667 : Reach 72667 := rs (se 1 (by rfl) ⟨54500, by rfl⟩) R109001
theorem R72827 : Reach 72827 := rs (se 1 (by rfl) ⟨54620, by rfl⟩) R109241
theorem R72953 : Reach 72953 := rs (se 2 (by rfl) ⟨27357, by rfl⟩) R54715
theorem R72991 : Reach 72991 := rs (se 1 (by rfl) ⟨54743, by rfl⟩) R109487
theorem R73097 : Reach 73097 := rs (se 2 (by rfl) ⟨27411, by rfl⟩) R54823
theorem R73223 : Reach 73223 := rs (se 1 (by rfl) ⟨54917, by rfl⟩) R109835
theorem R73403 : Reach 73403 := rs (se 1 (by rfl) ⟨55052, by rfl⟩) R110105
theorem R73529 : Reach 73529 := rs (se 2 (by rfl) ⟨27573, by rfl⟩) R55147
theorem R74009 : Reach 74009 := rs (se 2 (by rfl) ⟨27753, by rfl⟩) R55507
theorem R270641 : Reach 270641 := rs (se 2 (by rfl) ⟨101490, by rfl⟩) R202981
theorem R74159 : Reach 74159 := rs (se 1 (by rfl) ⟨55619, by rfl⟩) R111239
theorem R74195 : Reach 74195 := rs (se 1 (by rfl) ⟨55646, by rfl⟩) R111293
theorem R41467 : Reach 41467 := rs (se 1 (by rfl) ⟨31100, by rfl⟩) R62201
theorem R107027 : Reach 107027 := rs (se 1 (by rfl) ⟨80270, by rfl⟩) R160541
theorem R74303 : Reach 74303 := rs (se 1 (by rfl) ⟨55727, by rfl⟩) R111455
theorem R107129 : Reach 107129 := rs (se 2 (by rfl) ⟨40173, by rfl⟩) R80347
theorem R172691 : Reach 172691 := rs (se 1 (by rfl) ⟨129518, by rfl⟩) R259037
theorem R74411 : Reach 74411 := rs (se 1 (by rfl) ⟨55808, by rfl⟩) R111617
theorem R402149 : Reach 402149 := rs (se 4 (by rfl) ⟨37701, by rfl⟩) R75403
theorem R1057697 : Reach 1057697 := rs (se 2 (by rfl) ⟨396636, by rfl⟩) R793273
theorem R140345 : Reach 140345 := rs (se 2 (by rfl) ⟨52629, by rfl⟩) R105259
theorem R140413 : Reach 140413 := rs (se 3 (by rfl) ⟨26327, by rfl⟩) R52655
theorem R74951 : Reach 74951 := rs (se 1 (by rfl) ⟨56213, by rfl⟩) R112427
theorem R206057 : Reach 206057 := rs (se 2 (by rfl) ⟨77271, by rfl⟩) R154543
theorem R75131 : Reach 75131 := rs (se 1 (by rfl) ⟨56348, by rfl⟩) R112697
theorem R173501 : Reach 173501 := rs (se 3 (by rfl) ⟨32531, by rfl⟩) R65063
theorem R42439 : Reach 42439 := rs (se 1 (by rfl) ⟨31829, by rfl⟩) R63659
theorem R75257 : Reach 75257 := rs (se 2 (by rfl) ⟨28221, by rfl⟩) R56443
theorem R75347 : Reach 75347 := rs (se 1 (by rfl) ⟨56510, by rfl⟩) R113021
theorem R75527 : Reach 75527 := rs (se 1 (by rfl) ⟨56645, by rfl⟩) R113291
theorem R75649 : Reach 75649 := rs (se 2 (by rfl) ⟨28368, by rfl⟩) R56737
theorem R239597 : Reach 239597 := rs (se 3 (by rfl) ⟨44924, by rfl⟩) R89849
theorem R75905 : Reach 75905 := rs (se 2 (by rfl) ⟨28464, by rfl⟩) R56929
theorem R108809 : Reach 108809 := rs (se 2 (by rfl) ⟨40803, by rfl⟩) R81607
theorem R43355 : Reach 43355 := rs (se 1 (by rfl) ⟨32516, by rfl⟩) R65033
theorem R76139 : Reach 76139 := rs (se 1 (by rfl) ⟨57104, by rfl⟩) R114209
theorem R108983 : Reach 108983 := rs (se 1 (by rfl) ⟨81737, by rfl⟩) R163475
theorem R240083 : Reach 240083 := rs (se 1 (by rfl) ⟨180062, by rfl⟩) R360125
theorem R76283 : Reach 76283 := rs (se 1 (by rfl) ⟨57212, by rfl⟩) R114425
theorem R535085 : Reach 535085 := rs (se 3 (by rfl) ⟨100328, by rfl⟩) R200657
theorem R76409 : Reach 76409 := rs (se 2 (by rfl) ⟨28653, by rfl⟩) R57307
theorem R76463 : Reach 76463 := rs (se 1 (by rfl) ⟨57347, by rfl⟩) R114695
theorem R142019 : Reach 142019 := rs (se 1 (by rfl) ⟨106514, by rfl⟩) R213029
theorem R76535 : Reach 76535 := rs (se 1 (by rfl) ⟨57401, by rfl⟩) R114803
theorem R240407 : Reach 240407 := rs (se 1 (by rfl) ⟨180305, by rfl⟩) R360611
theorem R76715 : Reach 76715 := rs (se 1 (by rfl) ⟨57536, by rfl⟩) R115073
theorem R76787 : Reach 76787 := rs (se 1 (by rfl) ⟨57590, by rfl⟩) R115181
theorem R371789 : Reach 371789 := rs (se 3 (by rfl) ⟨69710, by rfl⟩) R139421
theorem R44327 : Reach 44327 := rs (se 1 (by rfl) ⟨33245, by rfl⟩) R66491
theorem R241015 : Reach 241015 := rs (se 1 (by rfl) ⟨180761, by rfl⟩) R361523
theorem R109943 : Reach 109943 := rs (se 1 (by rfl) ⟨82457, by rfl⟩) R164915
theorem R77195 : Reach 77195 := rs (se 1 (by rfl) ⟨57896, by rfl⟩) R115793
theorem R77255 : Reach 77255 := rs (se 1 (by rfl) ⟨57941, by rfl⟩) R115883
theorem R143111 : Reach 143111 := rs (se 1 (by rfl) ⟨107333, by rfl⟩) R214667
theorem R77615 : Reach 77615 := rs (se 1 (by rfl) ⟨58211, by rfl⟩) R116423
theorem R77849 : Reach 77849 := rs (se 2 (by rfl) ⟨29193, by rfl⟩) R58387
theorem R242027 : Reach 242027 := rs (se 1 (by rfl) ⟨181520, by rfl⟩) R363041
theorem R78191 : Reach 78191 := rs (se 1 (by rfl) ⟨58643, by rfl⟩) R117287
theorem R111023 : Reach 111023 := rs (se 1 (by rfl) ⟨83267, by rfl⟩) R166535
theorem R78263 : Reach 78263 := rs (se 1 (by rfl) ⟨58697, by rfl⟩) R117395
theorem R45631 : Reach 45631 := rs (se 1 (by rfl) ⟨34223, by rfl⟩) R68447
theorem R78407 : Reach 78407 := rs (se 1 (by rfl) ⟨58805, by rfl⟩) R117611
theorem R78443 : Reach 78443 := rs (se 1 (by rfl) ⟨58832, by rfl⟩) R117665
theorem R111257 : Reach 111257 := rs (se 2 (by rfl) ⟨41721, by rfl⟩) R83443
theorem R45751 : Reach 45751 := rs (se 1 (by rfl) ⟨34313, by rfl⟩) R68627
theorem R78839 : Reach 78839 := rs (se 1 (by rfl) ⟨59129, by rfl⟩) R118259
theorem R78887 : Reach 78887 := rs (se 1 (by rfl) ⟨59165, by rfl⟩) R118331
theorem R111995 : Reach 111995 := rs (se 1 (by rfl) ⟨83996, by rfl⟩) R167993
theorem R79319 : Reach 79319 := rs (se 1 (by rfl) ⟨59489, by rfl⟩) R118979
theorem R243485 : Reach 243485 := rs (se 3 (by rfl) ⟨45653, by rfl⟩) R91307
theorem R46889 : Reach 46889 := rs (se 2 (by rfl) ⟨17583, by rfl⟩) R35167
theorem R46895 : Reach 46895 := rs (se 1 (by rfl) ⟨35171, by rfl⟩) R70343
theorem R79663 : Reach 79663 := rs (se 1 (by rfl) ⟨59747, by rfl⟩) R119495
theorem R997271 : Reach 997271 := rs (se 1 (by rfl) ⟨747953, by rfl⟩) R1495907
theorem R47369 : Reach 47369 := rs (se 2 (by rfl) ⟨17763, by rfl⟩) R35527
theorem R112921 : Reach 112921 := rs (se 2 (by rfl) ⟨42345, by rfl⟩) R84691
theorem R47471 : Reach 47471 := rs (se 1 (by rfl) ⟨35603, by rfl⟩) R71207
theorem R80311 : Reach 80311 := rs (se 1 (by rfl) ⟨60233, by rfl⟩) R120467
theorem R47687 : Reach 47687 := rs (se 1 (by rfl) ⟨35765, by rfl⟩) R71531
theorem R47723 : Reach 47723 := rs (se 1 (by rfl) ⟨35792, by rfl⟩) R71585
theorem R113399 : Reach 113399 := rs (se 1 (by rfl) ⟨85049, by rfl⟩) R170099
theorem R47951 : Reach 47951 := rs (se 1 (by rfl) ⟨35963, by rfl⟩) R71927
theorem R474011 : Reach 474011 := rs (se 1 (by rfl) ⟨355508, by rfl⟩) R711017
theorem R48347 : Reach 48347 := rs (se 1 (by rfl) ⟨36260, by rfl⟩) R72521
theorem R48521 : Reach 48521 := rs (se 2 (by rfl) ⟨18195, by rfl⟩) R36391
theorem R81415 : Reach 81415 := rs (se 1 (by rfl) ⟨61061, by rfl⟩) R122123
theorem R81569 : Reach 81569 := rs (se 2 (by rfl) ⟨30588, by rfl⟩) R61177
theorem R48875 : Reach 48875 := rs (se 1 (by rfl) ⟨36656, by rfl⟩) R73313
theorem R212777 : Reach 212777 := rs (se 2 (by rfl) ⟨79791, by rfl⟩) R159583
theorem R114479 : Reach 114479 := rs (se 1 (by rfl) ⟨85859, by rfl⟩) R171719
theorem R81719 : Reach 81719 := rs (se 1 (by rfl) ⟨61289, by rfl⟩) R122579
theorem R606041 : Reach 606041 := rs (se 2 (by rfl) ⟨227265, by rfl⟩) R454531
theorem R81769 : Reach 81769 := rs (se 2 (by rfl) ⟨30663, by rfl⟩) R61327
theorem R49103 : Reach 49103 := rs (se 1 (by rfl) ⟨36827, by rfl⟩) R73655
theorem R344407 : Reach 344407 := rs (se 1 (by rfl) ⟨258305, by rfl⟩) R516611
theorem R49499 : Reach 49499 := rs (se 1 (by rfl) ⟨37124, by rfl⟩) R74249
theorem R49727 : Reach 49727 := rs (se 1 (by rfl) ⟨37295, by rfl⟩) R74591
theorem R574087 : Reach 574087 := rs (se 1 (by rfl) ⟨430565, by rfl⟩) R861131
theorem R49847 : Reach 49847 := rs (se 1 (by rfl) ⟨37385, by rfl⟩) R74771
theorem R312011 : Reach 312011 := rs (se 1 (by rfl) ⟨234008, by rfl⟩) R468017
theorem R50075 : Reach 50075 := rs (se 1 (by rfl) ⟨37556, by rfl⟩) R75113
theorem R83177 : Reach 83177 := rs (se 2 (by rfl) ⟨31191, by rfl⟩) R62383
theorem R50471 : Reach 50471 := rs (se 1 (by rfl) ⟨37853, by rfl⟩) R75707
theorem R50555 : Reach 50555 := rs (se 1 (by rfl) ⟨37916, by rfl⟩) R75833
theorem R83339 : Reach 83339 := rs (se 1 (by rfl) ⟨62504, by rfl⟩) R125009
theorem R83389 : Reach 83389 := rs (se 3 (by rfl) ⟨15635, by rfl⟩) R31271
theorem R50681 : Reach 50681 := rs (se 2 (by rfl) ⟨19005, by rfl⟩) R38011
theorem R83551 : Reach 83551 := rs (se 1 (by rfl) ⟨62663, by rfl⟩) R125327
theorem R50783 : Reach 50783 := rs (se 1 (by rfl) ⟨38087, by rfl⟩) R76175
theorem R280253 : Reach 280253 := rs (se 3 (by rfl) ⟨52547, by rfl⟩) R105095
theorem R50951 : Reach 50951 := rs (se 1 (by rfl) ⟨38213, by rfl⟩) R76427
theorem R50999 : Reach 50999 := rs (se 1 (by rfl) ⟨38249, by rfl⟩) R76499
theorem R116585 : Reach 116585 := rs (se 2 (by rfl) ⟨43719, by rfl⟩) R87439
theorem R345991 : Reach 345991 := rs (se 1 (by rfl) ⟨259493, by rfl⟩) R518987
theorem R51305 : Reach 51305 := rs (se 2 (by rfl) ⟨19239, by rfl⟩) R38479
theorem R379073 : Reach 379073 := rs (se 2 (by rfl) ⟨142152, by rfl⟩) R284305
theorem R706765 : Reach 706765 := rs (se 3 (by rfl) ⟨132518, by rfl⟩) R265037
theorem R84179 : Reach 84179 := rs (se 1 (by rfl) ⟨63134, by rfl⟩) R126269
theorem R117017 : Reach 117017 := rs (se 2 (by rfl) ⟨43881, by rfl⟩) R87763
theorem R51623 : Reach 51623 := rs (se 1 (by rfl) ⟨38717, by rfl⟩) R77435
theorem R444901 : Reach 444901 := rs (se 4 (by rfl) ⟨41709, by rfl⟩) R83419
theorem R51707 : Reach 51707 := rs (se 1 (by rfl) ⟨38780, by rfl⟩) R77561
theorem R51785 : Reach 51785 := rs (se 2 (by rfl) ⟨19419, by rfl⟩) R38839
theorem R51833 : Reach 51833 := rs (se 2 (by rfl) ⟨19437, by rfl⟩) R38875
theorem R51887 : Reach 51887 := rs (se 1 (by rfl) ⟨38915, by rfl⟩) R77831
theorem R51935 : Reach 51935 := rs (se 1 (by rfl) ⟨38951, by rfl⟩) R77903
theorem R52139 : Reach 52139 := rs (se 1 (by rfl) ⟨39104, by rfl⟩) R78209
theorem R52199 : Reach 52199 := rs (se 1 (by rfl) ⟨39149, by rfl⟩) R78299
theorem R216103 : Reach 216103 := rs (se 1 (by rfl) ⟨162077, by rfl⟩) R324155
theorem R52367 : Reach 52367 := rs (se 1 (by rfl) ⟨39275, by rfl⟩) R78551
theorem R52457 : Reach 52457 := rs (se 2 (by rfl) ⟨19671, by rfl⟩) R39343
theorem R609551 : Reach 609551 := rs (se 1 (by rfl) ⟨457163, by rfl⟩) R914327
theorem R52511 : Reach 52511 := rs (se 1 (by rfl) ⟨39383, by rfl⟩) R78767
theorem R118367 : Reach 118367 := rs (se 1 (by rfl) ⟨88775, by rfl⟩) R177551
theorem R347915 : Reach 347915 := rs (se 1 (by rfl) ⟨260936, by rfl⟩) R521873
theorem R53513 : Reach 53513 := rs (se 2 (by rfl) ⟨20067, by rfl⟩) R40135
theorem R53615 : Reach 53615 := rs (se 1 (by rfl) ⟨40211, by rfl⟩) R80423
theorem R283013 : Reach 283013 := rs (se 4 (by rfl) ⟨26532, by rfl⟩) R53065
theorem R86447 : Reach 86447 := rs (se 1 (by rfl) ⟨64835, by rfl⟩) R129671
theorem R86455 : Reach 86455 := rs (se 1 (by rfl) ⟨64841, by rfl⟩) R129683
theorem R152027 : Reach 152027 := rs (se 1 (by rfl) ⟨114020, by rfl⟩) R228041
theorem R53831 : Reach 53831 := rs (se 1 (by rfl) ⟨40373, by rfl⟩) R80747
theorem R53867 : Reach 53867 := rs (se 1 (by rfl) ⟨40400, by rfl⟩) R80801
theorem R54263 : Reach 54263 := rs (se 1 (by rfl) ⟨40697, by rfl⟩) R81395
theorem R381995 : Reach 381995 := rs (se 1 (by rfl) ⟨286496, by rfl⟩) R572993
theorem R250937 : Reach 250937 := rs (se 2 (by rfl) ⟨94101, by rfl⟩) R188203
theorem R119951 : Reach 119951 := rs (se 1 (by rfl) ⟨89963, by rfl⟩) R179927
theorem R87419 : Reach 87419 := rs (se 1 (by rfl) ⟨65564, by rfl⟩) R131129
theorem R55019 : Reach 55019 := rs (se 1 (by rfl) ⟨41264, by rfl⟩) R82529
theorem R55097 : Reach 55097 := rs (se 2 (by rfl) ⟨20661, by rfl⟩) R41323
theorem R219179 : Reach 219179 := rs (se 1 (by rfl) ⟨164384, by rfl⟩) R328769
theorem R350837 : Reach 350837 := rs (se 5 (by rfl) ⟨16445, by rfl⟩) R32891
theorem R55991 : Reach 55991 := rs (se 1 (by rfl) ⟨41993, by rfl⟩) R83987
theorem R711665 : Reach 711665 := rs (se 2 (by rfl) ⟨266874, by rfl⟩) R533749
theorem R89075 : Reach 89075 := rs (se 1 (by rfl) ⟨66806, by rfl⟩) R133613
theorem R121895 : Reach 121895 := rs (se 1 (by rfl) ⟨91421, by rfl⟩) R182843
theorem R56713 : Reach 56713 := rs (se 2 (by rfl) ⟨21267, by rfl⟩) R42535
theorem R89531 : Reach 89531 := rs (se 1 (by rfl) ⟨67148, by rfl⟩) R134297
theorem R56927 : Reach 56927 := rs (se 1 (by rfl) ⟨42695, by rfl⟩) R85391
theorem R57145 : Reach 57145 := rs (se 2 (by rfl) ⟨21429, by rfl⟩) R42859
theorem R286739 : Reach 286739 := rs (se 1 (by rfl) ⟨215054, by rfl⟩) R430109
theorem R57449 : Reach 57449 := rs (se 2 (by rfl) ⟨21543, by rfl⟩) R43087
theorem R319697 : Reach 319697 := rs (se 2 (by rfl) ⟨119886, by rfl⟩) R239773
theorem R124051 : Reach 124051 := rs (se 1 (by rfl) ⟨93038, by rfl⟩) R186077
theorem R124199 : Reach 124199 := rs (se 1 (by rfl) ⟨93149, by rfl⟩) R186299
theorem R58873 : Reach 58873 := rs (se 2 (by rfl) ⟨22077, by rfl⟩) R44155
theorem R59143 : Reach 59143 := rs (se 1 (by rfl) ⟨44357, by rfl⟩) R88715
theorem R59177 : Reach 59177 := rs (se 2 (by rfl) ⟨22191, by rfl⟩) R44383
theorem R551069 : Reach 551069 := rs (se 3 (by rfl) ⟨103325, by rfl⟩) R206651
theorem R157949 : Reach 157949 := rs (se 3 (by rfl) ⟨29615, by rfl⟩) R59231
theorem R158759 : Reach 158759 := rs (se 1 (by rfl) ⟨119069, by rfl⟩) R238139
theorem R93403 : Reach 93403 := rs (se 1 (by rfl) ⟨70052, by rfl⟩) R140105
theorem R159043 : Reach 159043 := rs (se 1 (by rfl) ⟨119282, by rfl⟩) R238565
theorem R126305 : Reach 126305 := rs (se 2 (by rfl) ⟨47364, by rfl⟩) R94729
theorem R93791 : Reach 93791 := rs (se 1 (by rfl) ⟨70343, by rfl⟩) R140687
theorem R1175233 : Reach 1175233 := rs (se 2 (by rfl) ⟨440712, by rfl⟩) R881425
theorem R159617 : Reach 159617 := rs (se 2 (by rfl) ⟨59856, by rfl⟩) R119713
theorem R421955 : Reach 421955 := rs (se 1 (by rfl) ⟨316466, by rfl⟩) R632933
theorem R192617 : Reach 192617 := rs (se 2 (by rfl) ⟨72231, by rfl⟩) R144463
theorem R618785 : Reach 618785 := rs (se 2 (by rfl) ⟨232044, by rfl⟩) R464089
theorem R127939 : Reach 127939 := rs (se 1 (by rfl) ⟨95954, by rfl⟩) R191909
theorem R160865 : Reach 160865 := rs (se 2 (by rfl) ⟨60324, by rfl⟩) R120649
theorem R95431 : Reach 95431 := rs (se 1 (by rfl) ⟨71573, by rfl⟩) R143147
theorem R128243 : Reach 128243 := rs (se 1 (by rfl) ⟨96182, by rfl⟩) R192365
theorem R128299 : Reach 128299 := rs (se 1 (by rfl) ⟨96224, by rfl⟩) R192449
theorem R194233 : Reach 194233 := rs (se 2 (by rfl) ⟨72837, by rfl⟩) R145675
theorem R128699 : Reach 128699 := rs (se 1 (by rfl) ⟨96524, by rfl⟩) R193049
theorem R358667 : Reach 358667 := rs (se 1 (by rfl) ⟨269000, by rfl⟩) R538001
theorem R31143 : Reach 31143 := rs (se 1 (by rfl) ⟨23357, by rfl⟩) R46715
theorem R1505749 : Reach 1505749 := rs (se 7 (by rfl) ⟨17645, by rfl⟩) R35291
theorem R31227 : Reach 31227 := rs (se 1 (by rfl) ⟨23420, by rfl⟩) R46841
theorem R31295 : Reach 31295 := rs (se 1 (by rfl) ⟨23471, by rfl⟩) R46943
theorem R31303 : Reach 31303 := rs (se 1 (by rfl) ⟨23477, by rfl⟩) R46955
theorem R31455 : Reach 31455 := rs (se 1 (by rfl) ⟨23591, by rfl⟩) R47183
theorem R64223 : Reach 64223 := rs (se 1 (by rfl) ⟨48167, by rfl⟩) R96335
theorem R31535 : Reach 31535 := rs (se 1 (by rfl) ⟨23651, by rfl⟩) R47303
theorem R654155 : Reach 654155 := rs (se 1 (by rfl) ⟨490616, by rfl⟩) R981233
theorem R31643 : Reach 31643 := rs (se 1 (by rfl) ⟨23732, by rfl⟩) R47465
theorem R31695 : Reach 31695 := rs (se 1 (by rfl) ⟨23771, by rfl⟩) R47543
theorem R31719 : Reach 31719 := rs (se 1 (by rfl) ⟨23789, by rfl⟩) R47579
theorem R130187 : Reach 130187 := rs (se 1 (by rfl) ⟨97640, by rfl⟩) R195281
theorem R32031 : Reach 32031 := rs (se 1 (by rfl) ⟨24023, by rfl⟩) R48047
theorem R163133 : Reach 163133 := rs (se 3 (by rfl) ⟨30587, by rfl⟩) R61175
theorem R32091 : Reach 32091 := rs (se 1 (by rfl) ⟨24068, by rfl⟩) R48137
theorem R32111 : Reach 32111 := rs (se 1 (by rfl) ⟨24083, by rfl⟩) R48167
theorem R32167 : Reach 32167 := rs (se 1 (by rfl) ⟨24125, by rfl⟩) R48251
theorem R32251 : Reach 32251 := rs (se 1 (by rfl) ⟨24188, by rfl⟩) R48377
theorem R294425 : Reach 294425 := rs (se 2 (by rfl) ⟨110409, by rfl⟩) R220819
theorem R32319 : Reach 32319 := rs (se 1 (by rfl) ⟨24239, by rfl⟩) R48479
theorem R32327 : Reach 32327 := rs (se 1 (by rfl) ⟨24245, by rfl⟩) R48491
theorem R196177 : Reach 196177 := rs (se 2 (by rfl) ⟨73566, by rfl⟩) R147133
theorem R130643 : Reach 130643 := rs (se 1 (by rfl) ⟨97982, by rfl⟩) R195965
theorem R32479 : Reach 32479 := rs (se 1 (by rfl) ⟨24359, by rfl⟩) R48719
theorem R32559 : Reach 32559 := rs (se 1 (by rfl) ⟨24419, by rfl⟩) R48839
theorem R32667 : Reach 32667 := rs (se 1 (by rfl) ⟨24500, by rfl⟩) R49001
theorem R32719 : Reach 32719 := rs (se 1 (by rfl) ⟨24539, by rfl⟩) R49079
theorem R32743 : Reach 32743 := rs (se 1 (by rfl) ⟨24557, by rfl⟩) R49115
theorem R65575 : Reach 65575 := rs (se 1 (by rfl) ⟨49181, by rfl⟩) R98363
theorem R983171 : Reach 983171 := rs (se 1 (by rfl) ⟨737378, by rfl⟩) R1474757
theorem R32999 : Reach 32999 := rs (se 1 (by rfl) ⟨24749, by rfl⟩) R49499
theorem R33151 : Reach 33151 := rs (se 1 (by rfl) ⟨24863, by rfl⟩) R49727
theorem R459209 : Reach 459209 := rs (se 2 (by rfl) ⟨172203, by rfl⟩) R344407
theorem R262607 : Reach 262607 := rs (se 1 (by rfl) ⟨196955, by rfl⟩) R393911
theorem R33231 : Reach 33231 := rs (se 1 (by rfl) ⟨24923, by rfl⟩) R49847
theorem R33383 : Reach 33383 := rs (se 1 (by rfl) ⟨25037, by rfl⟩) R50075
theorem R197423 : Reach 197423 := rs (se 1 (by rfl) ⟨148067, by rfl⟩) R296135
theorem R33647 : Reach 33647 := rs (se 1 (by rfl) ⟨25235, by rfl⟩) R50471
theorem R66415 : Reach 66415 := rs (se 1 (by rfl) ⟨49811, by rfl⟩) R99623
theorem R33703 : Reach 33703 := rs (se 1 (by rfl) ⟨25277, by rfl⟩) R50555
theorem R33787 : Reach 33787 := rs (se 1 (by rfl) ⟨25340, by rfl⟩) R50681
theorem R33855 : Reach 33855 := rs (se 1 (by rfl) ⟨25391, by rfl⟩) R50783
theorem R33967 : Reach 33967 := rs (se 1 (by rfl) ⟨25475, by rfl⟩) R50951
theorem R33999 : Reach 33999 := rs (se 1 (by rfl) ⟨25499, by rfl⟩) R50999
theorem R263519 : Reach 263519 := rs (se 1 (by rfl) ⟨197639, by rfl⟩) R395279
theorem R34203 : Reach 34203 := rs (se 1 (by rfl) ⟨25652, by rfl⟩) R51305
theorem R165401 : Reach 165401 := rs (se 2 (by rfl) ⟨62025, by rfl⟩) R124051
theorem R34415 : Reach 34415 := rs (se 1 (by rfl) ⟨25811, by rfl⟩) R51623
theorem R34471 : Reach 34471 := rs (se 1 (by rfl) ⟨25853, by rfl⟩) R51707
theorem R34523 : Reach 34523 := rs (se 1 (by rfl) ⟨25892, by rfl⟩) R51785
theorem R34555 : Reach 34555 := rs (se 1 (by rfl) ⟨25916, by rfl⟩) R51833
theorem R34591 : Reach 34591 := rs (se 1 (by rfl) ⟨25943, by rfl⟩) R51887
theorem R34623 : Reach 34623 := rs (se 1 (by rfl) ⟨25967, by rfl⟩) R51935
theorem R34759 : Reach 34759 := rs (se 1 (by rfl) ⟨26069, by rfl⟩) R52139
theorem R34799 : Reach 34799 := rs (se 1 (by rfl) ⟨26099, by rfl⟩) R52199
theorem R34911 : Reach 34911 := rs (se 1 (by rfl) ⟨26183, by rfl⟩) R52367
theorem R34971 : Reach 34971 := rs (se 1 (by rfl) ⟨26228, by rfl⟩) R52457
theorem R35007 : Reach 35007 := rs (se 1 (by rfl) ⟨26255, by rfl⟩) R52511
theorem R100865 : Reach 100865 := rs (se 2 (by rfl) ⟨37824, by rfl⟩) R75649
theorem R231943 : Reach 231943 := rs (se 1 (by rfl) ⟨173957, by rfl⟩) R347915
theorem R461321 : Reach 461321 := rs (se 2 (by rfl) ⟨172995, by rfl⟩) R345991
theorem R199199 : Reach 199199 := rs (se 1 (by rfl) ⟨149399, by rfl⟩) R298799
theorem R35675 : Reach 35675 := rs (se 1 (by rfl) ⟨26756, by rfl⟩) R53513
theorem R35743 : Reach 35743 := rs (se 1 (by rfl) ⟨26807, by rfl⟩) R53615
theorem R101351 : Reach 101351 := rs (se 1 (by rfl) ⟨76013, by rfl⟩) R152027
theorem R199655 : Reach 199655 := rs (se 1 (by rfl) ⟨149741, by rfl⟩) R299483
theorem R35887 : Reach 35887 := rs (se 1 (by rfl) ⟨26915, by rfl⟩) R53831
theorem R35911 : Reach 35911 := rs (se 1 (by rfl) ⟨26933, by rfl⟩) R53867
theorem R593201 : Reach 593201 := rs (se 2 (by rfl) ⟨222450, by rfl⟩) R444901
theorem R36175 : Reach 36175 := rs (se 1 (by rfl) ⟨27131, by rfl⟩) R54263
theorem R167291 : Reach 167291 := rs (se 1 (by rfl) ⟨125468, by rfl⟩) R250937
theorem R462419 : Reach 462419 := rs (se 1 (by rfl) ⟨346814, by rfl⟩) R693629
theorem R134951 : Reach 134951 := rs (se 1 (by rfl) ⟨101213, by rfl⟩) R202427
theorem R36679 : Reach 36679 := rs (se 1 (by rfl) ⟨27509, by rfl⟩) R55019
theorem R36731 : Reach 36731 := rs (se 1 (by rfl) ⟨27548, by rfl⟩) R55097
theorem R233891 : Reach 233891 := rs (se 1 (by rfl) ⟨175418, by rfl⟩) R350837
theorem R37327 : Reach 37327 := rs (se 1 (by rfl) ⟨27995, by rfl⟩) R55991
theorem R37951 : Reach 37951 := rs (se 1 (by rfl) ⟨28463, by rfl⟩) R56927
theorem R38299 : Reach 38299 := rs (se 1 (by rfl) ⟨28724, by rfl⟩) R57449
theorem R136673 : Reach 136673 := rs (se 2 (by rfl) ⟨51252, by rfl⟩) R102505
theorem R71351 : Reach 71351 := rs (se 1 (by rfl) ⟨53513, by rfl⟩) R107027
theorem R137371 : Reach 137371 := rs (se 1 (by rfl) ⟨103028, by rfl⟩) R206057
theorem R530729 : Reach 530729 := rs (se 2 (by rfl) ⟨199023, by rfl⟩) R398047
theorem R39451 : Reach 39451 := rs (se 1 (by rfl) ⟨29588, by rfl⟩) R59177
theorem R170585 : Reach 170585 := rs (se 2 (by rfl) ⟨63969, by rfl⟩) R127939
theorem R367379 : Reach 367379 := rs (se 1 (by rfl) ⟨275534, by rfl⟩) R551069
theorem R105299 : Reach 105299 := rs (se 1 (by rfl) ⟨78974, by rfl⟩) R157949
theorem R72539 : Reach 72539 := rs (se 1 (by rfl) ⟨54404, by rfl⟩) R108809
theorem R171065 : Reach 171065 := rs (se 2 (by rfl) ⟨64149, by rfl⟩) R128299
theorem R105839 : Reach 105839 := rs (se 1 (by rfl) ⟨79379, by rfl⟩) R158759
theorem R171557 : Reach 171557 := rs (se 4 (by rfl) ⟨16083, by rfl⟩) R32167
theorem R73295 : Reach 73295 := rs (se 1 (by rfl) ⟨54971, by rfl⟩) R109943
theorem R106217 : Reach 106217 := rs (se 2 (by rfl) ⟨39831, by rfl⟩) R79663
theorem R74015 : Reach 74015 := rs (se 1 (by rfl) ⟨55511, by rfl⟩) R111023
theorem R74171 : Reach 74171 := rs (se 1 (by rfl) ⟨55628, by rfl⟩) R111257
theorem R107081 : Reach 107081 := rs (se 2 (by rfl) ⟨40155, by rfl⟩) R80311
theorem R2007665 : Reach 2007665 := rs (se 2 (by rfl) ⟨752874, by rfl⟩) R1505749
theorem R107243 : Reach 107243 := rs (se 1 (by rfl) ⟨80432, by rfl⟩) R160865
theorem R140089 : Reach 140089 := rs (se 2 (by rfl) ⟨52533, by rfl⟩) R105067
theorem R74663 : Reach 74663 := rs (se 1 (by rfl) ⟨55997, by rfl⟩) R111995
theorem R664847 : Reach 664847 := rs (se 1 (by rfl) ⟨498635, by rfl⟩) R997271
theorem R239111 : Reach 239111 := rs (se 1 (by rfl) ⟨179333, by rfl⟩) R358667
theorem R42815 : Reach 42815 := rs (se 1 (by rfl) ⟨32111, by rfl⟩) R64223
theorem R75599 : Reach 75599 := rs (se 1 (by rfl) ⟨56699, by rfl⟩) R113399
theorem R75617 : Reach 75617 := rs (se 2 (by rfl) ⟨28356, by rfl⟩) R56713
theorem R436103 : Reach 436103 := rs (se 1 (by rfl) ⟨327077, by rfl⟩) R654155
theorem R108553 : Reach 108553 := rs (se 2 (by rfl) ⟨40707, by rfl⟩) R81415
theorem R108755 : Reach 108755 := rs (se 1 (by rfl) ⟨81566, by rfl⟩) R163133
theorem R731429 : Reach 731429 := rs (se 4 (by rfl) ⟨68571, by rfl⟩) R137143
theorem R76193 : Reach 76193 := rs (se 2 (by rfl) ⟨28572, by rfl⟩) R57145
theorem R109025 : Reach 109025 := rs (se 2 (by rfl) ⟨40884, by rfl⟩) R81769
theorem R141851 : Reach 141851 := rs (se 1 (by rfl) ⟨106388, by rfl⟩) R212777
theorem R76319 : Reach 76319 := rs (se 1 (by rfl) ⟨57239, by rfl⟩) R114479
theorem R404027 : Reach 404027 := rs (se 1 (by rfl) ⟨303020, by rfl⟩) R606041
theorem R43831 : Reach 43831 := rs (se 1 (by rfl) ⟨32873, by rfl⟩) R65747
theorem R208007 : Reach 208007 := rs (se 1 (by rfl) ⟨156005, by rfl⟩) R312011
theorem R175607 : Reach 175607 := rs (se 1 (by rfl) ⟨131705, by rfl⟩) R263411
theorem R765449 : Reach 765449 := rs (se 2 (by rfl) ⟨287043, by rfl⟩) R574087
theorem R110375 : Reach 110375 := rs (se 1 (by rfl) ⟨82781, by rfl⟩) R165563
theorem R77723 : Reach 77723 := rs (se 1 (by rfl) ⟨58292, by rfl⟩) R116585
theorem R602245 : Reach 602245 := rs (se 4 (by rfl) ⟨56460, by rfl⟩) R112921
theorem R78011 : Reach 78011 := rs (se 1 (by rfl) ⟨58508, by rfl⟩) R117017
theorem R110915 : Reach 110915 := rs (se 1 (by rfl) ⟨83186, by rfl⟩) R166373
theorem R176609 : Reach 176609 := rs (se 2 (by rfl) ⟨66228, by rfl⟩) R132457
theorem R111185 : Reach 111185 := rs (se 2 (by rfl) ⟨41694, by rfl⟩) R83389
theorem R78497 : Reach 78497 := rs (se 2 (by rfl) ⟨29436, by rfl⟩) R58873
theorem R176903 : Reach 176903 := rs (se 1 (by rfl) ⟨132677, by rfl⟩) R265355
theorem R111401 : Reach 111401 := rs (se 2 (by rfl) ⟨41775, by rfl⟩) R83551
theorem R406367 : Reach 406367 := rs (se 1 (by rfl) ⟨304775, by rfl⟩) R609551
theorem R78857 : Reach 78857 := rs (se 2 (by rfl) ⟨29571, by rfl⟩) R59143
theorem R111671 : Reach 111671 := rs (se 1 (by rfl) ⟨83753, by rfl⟩) R167507
theorem R78911 : Reach 78911 := rs (se 1 (by rfl) ⟨59183, by rfl⟩) R118367
theorem R46703 : Reach 46703 := rs (se 1 (by rfl) ⟨35027, by rfl⟩) R70055
theorem R46759 : Reach 46759 := rs (se 1 (by rfl) ⟨35069, by rfl⟩) R70139
theorem R46775 : Reach 46775 := rs (se 1 (by rfl) ⟨35081, by rfl⟩) R70163
theorem R46811 : Reach 46811 := rs (se 1 (by rfl) ⟨35108, by rfl⟩) R70217
theorem R46985 : Reach 46985 := rs (se 2 (by rfl) ⟨17619, by rfl⟩) R35239
theorem R47087 : Reach 47087 := rs (se 1 (by rfl) ⟨35315, by rfl⟩) R70631
theorem R79967 : Reach 79967 := rs (se 1 (by rfl) ⟨59975, by rfl⟩) R119951
theorem R47339 : Reach 47339 := rs (se 1 (by rfl) ⟨35504, by rfl⟩) R71009
theorem R47399 : Reach 47399 := rs (se 1 (by rfl) ⟨35549, by rfl⟩) R71099
theorem R47483 : Reach 47483 := rs (se 1 (by rfl) ⟨35612, by rfl⟩) R71225
theorem R47753 : Reach 47753 := rs (se 2 (by rfl) ⟨17907, by rfl⟩) R35815
theorem R146119 : Reach 146119 := rs (se 1 (by rfl) ⟨109589, by rfl⟩) R219179
theorem R47927 : Reach 47927 := rs (se 1 (by rfl) ⟨35945, by rfl⟩) R71891
theorem R47963 : Reach 47963 := rs (se 1 (by rfl) ⟨35972, by rfl⟩) R71945
theorem R113615 : Reach 113615 := rs (se 1 (by rfl) ⟨85211, by rfl⟩) R170423
theorem R48107 : Reach 48107 := rs (se 1 (by rfl) ⟨36080, by rfl⟩) R72161
theorem R212057 : Reach 212057 := rs (se 2 (by rfl) ⟨79521, by rfl⟩) R159043
theorem R48311 : Reach 48311 := rs (se 1 (by rfl) ⟨36233, by rfl⟩) R72467
theorem R179495 : Reach 179495 := rs (se 1 (by rfl) ⟨134621, by rfl⟩) R269243
theorem R474443 : Reach 474443 := rs (se 1 (by rfl) ⟨355832, by rfl⟩) R711665
theorem R81263 : Reach 81263 := rs (se 1 (by rfl) ⟨60947, by rfl⟩) R121895
theorem R48551 : Reach 48551 := rs (se 1 (by rfl) ⟨36413, by rfl⟩) R72827
theorem R48635 : Reach 48635 := rs (se 1 (by rfl) ⟨36476, by rfl⟩) R72953
theorem R48731 : Reach 48731 := rs (se 1 (by rfl) ⟨36548, by rfl⟩) R73097
theorem R48815 : Reach 48815 := rs (se 1 (by rfl) ⟨36611, by rfl⟩) R73223
theorem R48935 : Reach 48935 := rs (se 1 (by rfl) ⟨36701, by rfl⟩) R73403
theorem R49019 : Reach 49019 := rs (se 1 (by rfl) ⟨36764, by rfl⟩) R73529
theorem R213131 : Reach 213131 := rs (se 1 (by rfl) ⟨159848, by rfl⟩) R319697
theorem R49339 : Reach 49339 := rs (se 1 (by rfl) ⟨37004, by rfl⟩) R74009
theorem R180427 : Reach 180427 := rs (se 1 (by rfl) ⟨135320, by rfl⟩) R270641
theorem R49439 : Reach 49439 := rs (se 1 (by rfl) ⟨37079, by rfl⟩) R74159
theorem R49463 : Reach 49463 := rs (se 1 (by rfl) ⟨37097, by rfl⟩) R74195
theorem R49535 : Reach 49535 := rs (se 1 (by rfl) ⟨37151, by rfl⟩) R74303
theorem R115127 : Reach 115127 := rs (se 1 (by rfl) ⟨86345, by rfl⟩) R172691
theorem R49607 : Reach 49607 := rs (se 1 (by rfl) ⟨37205, by rfl⟩) R74411
theorem R115273 : Reach 115273 := rs (se 2 (by rfl) ⟨43227, by rfl⟩) R86455
theorem R705131 : Reach 705131 := rs (se 1 (by rfl) ⟨528848, by rfl⟩) R1057697
theorem R49961 : Reach 49961 := rs (se 2 (by rfl) ⟨18735, by rfl⟩) R37471
theorem R49967 : Reach 49967 := rs (se 1 (by rfl) ⟨37475, by rfl⟩) R74951
theorem R82799 : Reach 82799 := rs (se 1 (by rfl) ⟨62099, by rfl⟩) R124199
theorem R115613 : Reach 115613 := rs (se 3 (by rfl) ⟨21677, by rfl⟩) R43355
theorem R50087 : Reach 50087 := rs (se 1 (by rfl) ⟨37565, by rfl⟩) R75131
theorem R115667 : Reach 115667 := rs (se 1 (by rfl) ⟨86750, by rfl⟩) R173501
theorem R50171 : Reach 50171 := rs (se 1 (by rfl) ⟨37628, by rfl⟩) R75257
theorem R50231 : Reach 50231 := rs (se 1 (by rfl) ⟨37673, by rfl⟩) R75347
theorem R50249 : Reach 50249 := rs (se 2 (by rfl) ⟨18843, by rfl⟩) R37687
theorem R50351 : Reach 50351 := rs (se 1 (by rfl) ⟨37763, by rfl⟩) R75527
theorem R50603 : Reach 50603 := rs (se 1 (by rfl) ⟨37952, by rfl⟩) R75905
theorem R50759 : Reach 50759 := rs (se 1 (by rfl) ⟨38069, by rfl⟩) R76139
theorem R50855 : Reach 50855 := rs (se 1 (by rfl) ⟨38141, by rfl⟩) R76283
theorem R50939 : Reach 50939 := rs (se 1 (by rfl) ⟨38204, by rfl⟩) R76409
theorem R50975 : Reach 50975 := rs (se 1 (by rfl) ⟨38231, by rfl⟩) R76463
theorem R51023 : Reach 51023 := rs (se 1 (by rfl) ⟨38267, by rfl⟩) R76535
theorem R51143 : Reach 51143 := rs (se 1 (by rfl) ⟨38357, by rfl⟩) R76715
theorem R51191 : Reach 51191 := rs (se 1 (by rfl) ⟨38393, by rfl⟩) R76787
theorem R247859 : Reach 247859 := rs (se 1 (by rfl) ⟨185894, by rfl⟩) R371789
theorem R84203 : Reach 84203 := rs (se 1 (by rfl) ⟨63152, by rfl⟩) R126305
theorem R51463 : Reach 51463 := rs (se 1 (by rfl) ⟨38597, by rfl⟩) R77195
theorem R51497 : Reach 51497 := rs (se 2 (by rfl) ⟨19311, by rfl⟩) R38623
theorem R51503 : Reach 51503 := rs (se 1 (by rfl) ⟨38627, by rfl⟩) R77255
theorem R51743 : Reach 51743 := rs (se 1 (by rfl) ⟨38807, by rfl⟩) R77615
theorem R51899 : Reach 51899 := rs (se 1 (by rfl) ⟨38924, by rfl⟩) R77849
theorem R281303 : Reach 281303 := rs (se 1 (by rfl) ⟨210977, by rfl⟩) R421955
theorem R412523 : Reach 412523 := rs (se 1 (by rfl) ⟨309392, by rfl⟩) R618785
theorem R52127 : Reach 52127 := rs (se 1 (by rfl) ⟨39095, by rfl⟩) R78191
theorem R52175 : Reach 52175 := rs (se 1 (by rfl) ⟨39131, by rfl⟩) R78263
theorem R52265 : Reach 52265 := rs (se 2 (by rfl) ⟨19599, by rfl⟩) R39199
theorem R52271 : Reach 52271 := rs (se 1 (by rfl) ⟨39203, by rfl⟩) R78407
theorem R52295 : Reach 52295 := rs (se 1 (by rfl) ⟨39221, by rfl⟩) R78443
theorem R52559 : Reach 52559 := rs (se 1 (by rfl) ⟨39419, by rfl⟩) R78839
theorem R52591 : Reach 52591 := rs (se 1 (by rfl) ⟨39443, by rfl⟩) R78887
theorem R52649 : Reach 52649 := rs (se 2 (by rfl) ⟨19743, by rfl⟩) R39487
theorem R118205 : Reach 118205 := rs (se 3 (by rfl) ⟨22163, by rfl⟩) R44327
theorem R85495 : Reach 85495 := rs (se 1 (by rfl) ⟨64121, by rfl⟩) R128243
theorem R52879 : Reach 52879 := rs (se 1 (by rfl) ⟨39659, by rfl⟩) R79319
theorem R85799 : Reach 85799 := rs (se 1 (by rfl) ⟨64349, by rfl⟩) R128699
theorem R184301 : Reach 184301 := rs (se 3 (by rfl) ⟨34556, by rfl⟩) R69113
theorem R316007 : Reach 316007 := rs (se 1 (by rfl) ⟨237005, by rfl⟩) R474011
theorem R86791 : Reach 86791 := rs (se 1 (by rfl) ⟨65093, by rfl⟩) R130187
theorem R87095 : Reach 87095 := rs (se 1 (by rfl) ⟨65321, by rfl⟩) R130643
theorem R54379 : Reach 54379 := rs (se 1 (by rfl) ⟨40784, by rfl⟩) R81569
theorem R54479 : Reach 54479 := rs (se 1 (by rfl) ⟨40859, by rfl⟩) R81719
theorem R87623 : Reach 87623 := rs (se 1 (by rfl) ⟨65717, by rfl⟩) R131435
theorem R55289 : Reach 55289 := rs (se 2 (by rfl) ⟨20733, by rfl⟩) R41467
theorem R55451 : Reach 55451 := rs (se 1 (by rfl) ⟨41588, by rfl⟩) R83177
theorem R55559 : Reach 55559 := rs (se 1 (by rfl) ⟨41669, by rfl⟩) R83339
theorem R88361 : Reach 88361 := rs (se 2 (by rfl) ⟨33135, by rfl⟩) R66271
theorem R186835 : Reach 186835 := rs (se 1 (by rfl) ⟨140126, by rfl⟩) R280253
theorem R252715 : Reach 252715 := rs (se 1 (by rfl) ⟨189536, by rfl⟩) R379073
theorem R56119 : Reach 56119 := rs (se 1 (by rfl) ⟨42089, by rfl⟩) R84179
theorem R187217 : Reach 187217 := rs (se 2 (by rfl) ⟨70206, by rfl⟩) R140413
theorem R285677 : Reach 285677 := rs (se 3 (by rfl) ⟨53564, by rfl⟩) R107129
theorem R1530899 : Reach 1530899 := rs (se 1 (by rfl) ⟨1148174, by rfl⟩) R2296349
theorem R56585 : Reach 56585 := rs (se 2 (by rfl) ⟨21219, by rfl⟩) R42439
theorem R1072397 : Reach 1072397 := rs (se 3 (by rfl) ⟨201074, by rfl⟩) R402149
theorem R89383 : Reach 89383 := rs (se 1 (by rfl) ⟨67037, by rfl⟩) R134075
theorem R11951887 : Reach 11951887 := rs (se 1 (by rfl) ⟨8963915, by rfl⟩) R17927831
theorem R188675 : Reach 188675 := rs (se 1 (by rfl) ⟨141506, by rfl⟩) R283013
theorem R942353 : Reach 942353 := rs (se 2 (by rfl) ⟨353382, by rfl⟩) R706765
theorem R57631 : Reach 57631 := rs (se 1 (by rfl) ⟨43223, by rfl⟩) R86447
theorem R254663 : Reach 254663 := rs (se 1 (by rfl) ⟨190997, by rfl⟩) R381995
theorem R58279 : Reach 58279 := rs (se 1 (by rfl) ⟨43709, by rfl⟩) R87419
theorem R288137 : Reach 288137 := rs (se 2 (by rfl) ⟨108051, by rfl⟩) R216103
theorem R124537 : Reach 124537 := rs (se 2 (by rfl) ⟨46701, by rfl⟩) R93403
theorem R91945 : Reach 91945 := rs (se 2 (by rfl) ⟨34479, by rfl⟩) R68959
theorem R321353 : Reach 321353 := rs (se 2 (by rfl) ⟨120507, by rfl⟩) R241015
theorem R59383 : Reach 59383 := rs (se 1 (by rfl) ⟨44537, by rfl⟩) R89075
theorem R354449 : Reach 354449 := rs (se 2 (by rfl) ⟨132918, by rfl⟩) R265837
theorem R1566977 : Reach 1566977 := rs (se 2 (by rfl) ⟨587616, by rfl⟩) R1175233
theorem R59687 : Reach 59687 := rs (se 1 (by rfl) ⟨44765, by rfl⟩) R89531
theorem R92573 : Reach 92573 := rs (se 3 (by rfl) ⟨17357, by rfl⟩) R34715
theorem R191159 : Reach 191159 := rs (se 1 (by rfl) ⟨143369, by rfl⟩) R286739
theorem R1272833 : Reach 1272833 := rs (se 2 (by rfl) ⟨477312, by rfl⟩) R954625
theorem R93563 : Reach 93563 := rs (se 1 (by rfl) ⟨70172, by rfl⟩) R140345
theorem R60841 : Reach 60841 := rs (se 2 (by rfl) ⟨22815, by rfl⟩) R45631
theorem R61001 : Reach 61001 := rs (se 2 (by rfl) ⟨22875, by rfl⟩) R45751
theorem R290621 : Reach 290621 := rs (se 3 (by rfl) ⟨54491, by rfl⟩) R108983
theorem R159731 : Reach 159731 := rs (se 1 (by rfl) ⟨119798, by rfl⟩) R239597
theorem R389285 : Reach 389285 := rs (se 4 (by rfl) ⟨36495, by rfl⟩) R72991
theorem R127241 : Reach 127241 := rs (se 2 (by rfl) ⟨47715, by rfl⟩) R95431
theorem R160055 : Reach 160055 := rs (se 1 (by rfl) ⟨120041, by rfl⟩) R240083
theorem R356723 : Reach 356723 := rs (se 1 (by rfl) ⟨267542, by rfl⟩) R535085
theorem R94679 : Reach 94679 := rs (se 1 (by rfl) ⟨71009, by rfl⟩) R142019
theorem R160271 : Reach 160271 := rs (se 1 (by rfl) ⟨120203, by rfl⟩) R240407
theorem R258977 : Reach 258977 := rs (se 2 (by rfl) ⟨97116, by rfl⟩) R194233
theorem R62527 : Reach 62527 := rs (se 1 (by rfl) ⟨46895, by rfl⟩) R93791
theorem R95407 : Reach 95407 := rs (se 1 (by rfl) ⟨71555, by rfl⟩) R143111
theorem R128411 : Reach 128411 := rs (se 1 (by rfl) ⟨96308, by rfl⟩) R192617
theorem R161351 : Reach 161351 := rs (se 1 (by rfl) ⟨121013, by rfl⟩) R242027
theorem R96137 : Reach 96137 := rs (se 2 (by rfl) ⟨36051, by rfl⟩) R72103
theorem R162323 : Reach 162323 := rs (se 1 (by rfl) ⟨121742, by rfl⟩) R243485
theorem R31259 : Reach 31259 := rs (se 1 (by rfl) ⟨23444, by rfl⟩) R46889
theorem R31263 : Reach 31263 := rs (se 1 (by rfl) ⟨23447, by rfl⟩) R46895
theorem R96889 : Reach 96889 := rs (se 2 (by rfl) ⟨36333, by rfl⟩) R72667
theorem R31579 : Reach 31579 := rs (se 1 (by rfl) ⟨23684, by rfl⟩) R47369
theorem R31647 : Reach 31647 := rs (se 1 (by rfl) ⟨23735, by rfl⟩) R47471
theorem R31791 : Reach 31791 := rs (se 1 (by rfl) ⟨23843, by rfl⟩) R47687
theorem R31815 : Reach 31815 := rs (se 1 (by rfl) ⟨23861, by rfl⟩) R47723
theorem R31967 : Reach 31967 := rs (se 1 (by rfl) ⟨23975, by rfl⟩) R47951
theorem R261569 : Reach 261569 := rs (se 2 (by rfl) ⟨98088, by rfl⟩) R196177
theorem R32231 : Reach 32231 := rs (se 1 (by rfl) ⟨24173, by rfl⟩) R48347
theorem R32347 : Reach 32347 := rs (se 1 (by rfl) ⟨24260, by rfl⟩) R48521
theorem R425645 : Reach 425645 := rs (se 3 (by rfl) ⟨79808, by rfl⟩) R159617
theorem R196283 : Reach 196283 := rs (se 1 (by rfl) ⟨147212, by rfl⟩) R294425
theorem R32583 : Reach 32583 := rs (se 1 (by rfl) ⟨24437, by rfl⟩) R48875
theorem R32735 : Reach 32735 := rs (se 1 (by rfl) ⟨24551, by rfl⟩) R49103
theorem R655447 : Reach 655447 := rs (se 1 (by rfl) ⟨491585, by rfl⟩) R983171
theorem R32959 : Reach 32959 := rs (se 1 (by rfl) ⟨24719, by rfl⟩) R49439
theorem R32975 : Reach 32975 := rs (se 1 (by rfl) ⟨24731, by rfl⟩) R49463
theorem R65785 : Reach 65785 := rs (se 2 (by rfl) ⟨24669, by rfl⟩) R49339
theorem R33023 : Reach 33023 := rs (se 1 (by rfl) ⟨24767, by rfl⟩) R49535
theorem R33071 : Reach 33071 := rs (se 1 (by rfl) ⟨24803, by rfl⟩) R49607
theorem R33307 : Reach 33307 := rs (se 1 (by rfl) ⟨24980, by rfl⟩) R49961
theorem R33311 : Reach 33311 := rs (se 1 (by rfl) ⟨24983, by rfl⟩) R49967
theorem R131615 : Reach 131615 := rs (se 1 (by rfl) ⟨98711, by rfl⟩) R197423
theorem R33391 : Reach 33391 := rs (se 1 (by rfl) ⟨25043, by rfl⟩) R50087
theorem R33447 : Reach 33447 := rs (se 1 (by rfl) ⟨25085, by rfl⟩) R50171
theorem R3211973 : Reach 3211973 := rs (se 4 (by rfl) ⟨301122, by rfl⟩) R602245
theorem R33487 : Reach 33487 := rs (se 1 (by rfl) ⟨25115, by rfl⟩) R50231
theorem R33499 : Reach 33499 := rs (se 1 (by rfl) ⟨25124, by rfl⟩) R50249
theorem R33567 : Reach 33567 := rs (se 1 (by rfl) ⟨25175, by rfl⟩) R50351
theorem R33735 : Reach 33735 := rs (se 1 (by rfl) ⟨25301, by rfl⟩) R50603
theorem R33839 : Reach 33839 := rs (se 1 (by rfl) ⟨25379, by rfl⟩) R50759
theorem R33903 : Reach 33903 := rs (se 1 (by rfl) ⟨25427, by rfl⟩) R50855
theorem R33959 : Reach 33959 := rs (se 1 (by rfl) ⟨25469, by rfl⟩) R50939
theorem R33983 : Reach 33983 := rs (se 1 (by rfl) ⟨25487, by rfl⟩) R50975
theorem R34015 : Reach 34015 := rs (se 1 (by rfl) ⟨25511, by rfl⟩) R51023
theorem R34095 : Reach 34095 := rs (se 1 (by rfl) ⟨25571, by rfl⟩) R51143
theorem R34127 : Reach 34127 := rs (se 1 (by rfl) ⟨25595, by rfl⟩) R51191
theorem R165239 : Reach 165239 := rs (se 1 (by rfl) ⟨123929, by rfl⟩) R247859
theorem R34331 : Reach 34331 := rs (se 1 (by rfl) ⟨25748, by rfl⟩) R51497
theorem R34335 : Reach 34335 := rs (se 1 (by rfl) ⟨25751, by rfl⟩) R51503
theorem R67243 : Reach 67243 := rs (se 1 (by rfl) ⟨50432, by rfl⟩) R100865
theorem R132799 : Reach 132799 := rs (se 1 (by rfl) ⟨99599, by rfl⟩) R199199
theorem R34495 : Reach 34495 := rs (se 1 (by rfl) ⟨25871, by rfl⟩) R51743
theorem R34599 : Reach 34599 := rs (se 1 (by rfl) ⟨25949, by rfl⟩) R51899
theorem R34751 : Reach 34751 := rs (se 1 (by rfl) ⟨26063, by rfl⟩) R52127
theorem R34783 : Reach 34783 := rs (se 1 (by rfl) ⟨26087, by rfl⟩) R52175
theorem R67567 : Reach 67567 := rs (se 1 (by rfl) ⟨50675, by rfl⟩) R101351
theorem R133103 : Reach 133103 := rs (se 1 (by rfl) ⟨99827, by rfl⟩) R199655
theorem R34843 : Reach 34843 := rs (se 1 (by rfl) ⟨26132, by rfl⟩) R52265
theorem R34847 : Reach 34847 := rs (se 1 (by rfl) ⟨26135, by rfl⟩) R52271
theorem R34863 : Reach 34863 := rs (se 1 (by rfl) ⟨26147, by rfl⟩) R52295
theorem R166049 : Reach 166049 := rs (se 2 (by rfl) ⟨62268, by rfl⟩) R124537
theorem R35039 : Reach 35039 := rs (se 1 (by rfl) ⟨26279, by rfl⟩) R52559
theorem R35099 : Reach 35099 := rs (se 1 (by rfl) ⟨26324, by rfl⟩) R52649
theorem R16714421 : Reach 16714421 := rs (se 5 (by rfl) ⟨783488, by rfl⟩) R1566977
theorem R68617 : Reach 68617 := rs (se 2 (by rfl) ⟨25731, by rfl⟩) R51463
theorem R36319 : Reach 36319 := rs (se 1 (by rfl) ⟨27239, by rfl⟩) R54479
theorem R36859 : Reach 36859 := rs (se 1 (by rfl) ⟨27644, by rfl⟩) R55289
theorem R36967 : Reach 36967 := rs (se 1 (by rfl) ⟨27725, by rfl⟩) R55451
theorem R37039 : Reach 37039 := rs (se 1 (by rfl) ⟨27779, by rfl⟩) R55559
theorem R70121 : Reach 70121 := rs (se 2 (by rfl) ⟨26295, by rfl⟩) R52591
theorem R70199 : Reach 70199 := rs (se 1 (by rfl) ⟨52649, by rfl⟩) R105299
theorem R1020599 : Reach 1020599 := rs (se 1 (by rfl) ⟨765449, by rfl⟩) R1530899
theorem R37723 : Reach 37723 := rs (se 1 (by rfl) ⟨28292, by rfl⟩) R56585
theorem R70505 : Reach 70505 := rs (se 2 (by rfl) ⟨26439, by rfl⟩) R52879
theorem R70559 : Reach 70559 := rs (se 1 (by rfl) ⟨52919, by rfl⟩) R105839
theorem R70811 : Reach 70811 := rs (se 1 (by rfl) ⟨53108, by rfl⟩) R106217
theorem R628235 : Reach 628235 := rs (se 1 (by rfl) ⟨471176, by rfl⟩) R942353
theorem R202405 : Reach 202405 := rs (se 4 (by rfl) ⟨18975, by rfl⟩) R37951
theorem R71387 : Reach 71387 := rs (se 1 (by rfl) ⟨53540, by rfl⟩) R107081
theorem R169775 : Reach 169775 := rs (se 1 (by rfl) ⟨127331, by rfl⟩) R254663
theorem R71495 : Reach 71495 := rs (se 1 (by rfl) ⟨53621, by rfl⟩) R107243
theorem R236299 : Reach 236299 := rs (se 1 (by rfl) ⟨177224, by rfl⟩) R354449
theorem R72503 : Reach 72503 := rs (se 1 (by rfl) ⟨54377, by rfl⟩) R108755
theorem R72505 : Reach 72505 := rs (se 2 (by rfl) ⟨27189, by rfl⟩) R54379
theorem R39791 : Reach 39791 := rs (se 1 (by rfl) ⟨29843, by rfl⟩) R59687
theorem R72683 : Reach 72683 := rs (se 1 (by rfl) ⟨54512, by rfl⟩) R109025
theorem R269351 : Reach 269351 := rs (se 1 (by rfl) ⟨202013, by rfl⟩) R404027
theorem R138671 : Reach 138671 := rs (se 1 (by rfl) ⟨104003, by rfl⟩) R208007
theorem R40667 : Reach 40667 := rs (se 1 (by rfl) ⟨30500, by rfl⟩) R61001
theorem R73583 : Reach 73583 := rs (se 1 (by rfl) ⟨55187, by rfl⟩) R110375
theorem R106487 : Reach 106487 := rs (se 1 (by rfl) ⟨79865, by rfl⟩) R159731
theorem R106703 : Reach 106703 := rs (se 1 (by rfl) ⟨80027, by rfl⟩) R160055
theorem R73943 : Reach 73943 := rs (se 1 (by rfl) ⟨55457, by rfl⟩) R110915
theorem R237815 : Reach 237815 := rs (se 1 (by rfl) ⟨178361, by rfl⟩) R356723
theorem R106847 : Reach 106847 := rs (se 1 (by rfl) ⟨80135, by rfl⟩) R160271
theorem R74123 : Reach 74123 := rs (se 1 (by rfl) ⟨55592, by rfl⟩) R111185
theorem R74267 : Reach 74267 := rs (se 1 (by rfl) ⟨55700, by rfl⟩) R111401
theorem R270911 : Reach 270911 := rs (se 1 (by rfl) ⟨203183, by rfl⟩) R406367
theorem R172651 : Reach 172651 := rs (se 1 (by rfl) ⟨129488, by rfl⟩) R258977
theorem R2859725 : Reach 2859725 := rs (se 3 (by rfl) ⟨536198, by rfl⟩) R1072397
theorem R74447 : Reach 74447 := rs (se 1 (by rfl) ⟨55835, by rfl⟩) R111671
theorem R1581869 : Reach 1581869 := rs (se 3 (by rfl) ⟨296600, by rfl⟩) R593201
theorem R107567 : Reach 107567 := rs (se 1 (by rfl) ⟨80675, by rfl⟩) R161351
theorem R336953 : Reach 336953 := rs (se 2 (by rfl) ⟨126357, by rfl⟩) R252715
theorem R74825 : Reach 74825 := rs (se 2 (by rfl) ⟨28059, by rfl⟩) R56119
theorem R697517 : Reach 697517 := rs (se 3 (by rfl) ⟨130784, by rfl⟩) R261569
theorem R108215 : Reach 108215 := rs (se 1 (by rfl) ⟨81161, by rfl⟩) R162323
theorem R75743 : Reach 75743 := rs (se 1 (by rfl) ⟨56807, by rfl⟩) R113615
theorem R141371 : Reach 141371 := rs (se 1 (by rfl) ⟨106028, by rfl⟩) R212057
theorem R15935849 : Reach 15935849 := rs (se 2 (by rfl) ⟨5975943, by rfl⟩) R11951887
theorem R142087 : Reach 142087 := rs (se 1 (by rfl) ⟨106565, by rfl⟩) R213131
theorem R240569 : Reach 240569 := rs (se 2 (by rfl) ⟨90213, by rfl⟩) R180427
theorem R76751 : Reach 76751 := rs (se 1 (by rfl) ⟨57563, by rfl⟩) R115127
theorem R306139 : Reach 306139 := rs (se 1 (by rfl) ⟨229604, by rfl⟩) R459209
theorem R76841 : Reach 76841 := rs (se 2 (by rfl) ⟨28815, by rfl⟩) R57631
theorem R470087 : Reach 470087 := rs (se 1 (by rfl) ⟨352565, by rfl⟩) R705131
theorem R77075 : Reach 77075 := rs (se 1 (by rfl) ⟨57806, by rfl⟩) R115613
theorem R77111 : Reach 77111 := rs (se 1 (by rfl) ⟨57833, by rfl⟩) R115667
theorem R175679 : Reach 175679 := rs (se 1 (by rfl) ⟨131759, by rfl⟩) R263519
theorem R110267 : Reach 110267 := rs (se 1 (by rfl) ⟨82700, by rfl⟩) R165401
theorem R700285 : Reach 700285 := rs (se 3 (by rfl) ⟨131303, by rfl⟩) R262607
theorem R77705 : Reach 77705 := rs (se 2 (by rfl) ⟨29139, by rfl⟩) R58279
theorem R45289 : Reach 45289 := rs (se 2 (by rfl) ⟨16983, by rfl⟩) R33967
theorem R307547 : Reach 307547 := rs (se 1 (by rfl) ⟨230660, by rfl⟩) R461321
theorem R275015 : Reach 275015 := rs (se 1 (by rfl) ⟨206261, by rfl⟩) R412523
theorem R111527 : Reach 111527 := rs (se 1 (by rfl) ⟨83645, by rfl⟩) R167291
theorem R78803 : Reach 78803 := rs (se 1 (by rfl) ⟨59102, by rfl⟩) R118205
theorem R308279 : Reach 308279 := rs (se 1 (by rfl) ⟨231209, by rfl⟩) R462419
theorem R79177 : Reach 79177 := rs (se 2 (by rfl) ⟨29691, by rfl⟩) R59383
theorem R144737 : Reach 144737 := rs (se 2 (by rfl) ⟨54276, by rfl⟩) R108553
theorem R210671 : Reach 210671 := rs (se 1 (by rfl) ⟨158003, by rfl⟩) R316007
theorem R309257 : Reach 309257 := rs (se 2 (by rfl) ⟨115971, by rfl⟩) R231943
theorem R47567 : Reach 47567 := rs (se 1 (by rfl) ⟨35675, by rfl⟩) R71351
theorem R47657 : Reach 47657 := rs (se 2 (by rfl) ⟨17871, by rfl⟩) R35743
theorem R47849 : Reach 47849 := rs (se 2 (by rfl) ⟨17943, by rfl⟩) R35887
theorem R47881 : Reach 47881 := rs (se 2 (by rfl) ⟨17955, by rfl⟩) R35911
theorem R113723 : Reach 113723 := rs (se 1 (by rfl) ⟨85292, by rfl⟩) R170585
theorem R48233 : Reach 48233 := rs (se 2 (by rfl) ⟨18087, by rfl⟩) R36175
theorem R244919 : Reach 244919 := rs (se 1 (by rfl) ⟨183689, by rfl⟩) R367379
theorem R81121 : Reach 81121 := rs (se 2 (by rfl) ⟨30420, by rfl⟩) R60841
theorem R48359 : Reach 48359 := rs (se 1 (by rfl) ⟨36269, by rfl⟩) R72539
theorem R113993 : Reach 113993 := rs (se 2 (by rfl) ⟨42747, by rfl⟩) R85495
theorem R114043 : Reach 114043 := rs (se 1 (by rfl) ⟨85532, by rfl⟩) R171065
theorem R114173 : Reach 114173 := rs (se 3 (by rfl) ⟨21407, by rfl⟩) R42815
theorem R114371 : Reach 114371 := rs (se 1 (by rfl) ⟨85778, by rfl⟩) R171557
theorem R48863 : Reach 48863 := rs (se 1 (by rfl) ⟨36647, by rfl⟩) R73295
theorem R48905 : Reach 48905 := rs (se 2 (by rfl) ⟨18339, by rfl⟩) R36679
theorem R49343 : Reach 49343 := rs (se 1 (by rfl) ⟨37007, by rfl⟩) R74015
theorem R49447 : Reach 49447 := rs (se 1 (by rfl) ⟨37085, by rfl⟩) R74171
theorem R49769 : Reach 49769 := rs (se 2 (by rfl) ⟨18663, by rfl⟩) R37327
theorem R49775 : Reach 49775 := rs (se 1 (by rfl) ⟨37331, by rfl⟩) R74663
theorem R443231 : Reach 443231 := rs (se 1 (by rfl) ⟨332423, by rfl⟩) R664847
theorem R508837 : Reach 508837 := rs (se 4 (by rfl) ⟨47703, by rfl⟩) R95407
theorem R115721 : Reach 115721 := rs (se 2 (by rfl) ⟨43395, by rfl⟩) R86791
theorem R214235 : Reach 214235 := rs (se 1 (by rfl) ⟨160676, by rfl⟩) R321353
theorem R50399 : Reach 50399 := rs (se 1 (by rfl) ⟨37799, by rfl⟩) R75599
theorem R50411 : Reach 50411 := rs (se 1 (by rfl) ⟨37808, by rfl⟩) R75617
theorem R378269 : Reach 378269 := rs (se 3 (by rfl) ⟨70925, by rfl⟩) R141851
theorem R83369 : Reach 83369 := rs (se 2 (by rfl) ⟨31263, by rfl⟩) R62527
theorem R50795 : Reach 50795 := rs (se 1 (by rfl) ⟨38096, by rfl⟩) R76193
theorem R50879 : Reach 50879 := rs (se 1 (by rfl) ⟨38159, by rfl⟩) R76319
theorem R51065 : Reach 51065 := rs (se 2 (by rfl) ⟨19149, by rfl⟩) R38299
theorem R117071 : Reach 117071 := rs (se 1 (by rfl) ⟨87803, by rfl⟩) R175607
theorem R510299 : Reach 510299 := rs (se 1 (by rfl) ⟨382724, by rfl⟩) R765449
theorem R51815 : Reach 51815 := rs (se 1 (by rfl) ⟨38861, by rfl⟩) R77723
theorem R52007 : Reach 52007 := rs (se 1 (by rfl) ⟨39005, by rfl⟩) R78011
theorem R84827 : Reach 84827 := rs (se 1 (by rfl) ⟨63620, by rfl⟩) R127241
theorem R183161 : Reach 183161 := rs (se 2 (by rfl) ⟨68685, by rfl⟩) R137371
theorem R117739 : Reach 117739 := rs (se 1 (by rfl) ⟨88304, by rfl⟩) R176609
theorem R52331 : Reach 52331 := rs (se 1 (by rfl) ⟨39248, by rfl⟩) R78497
theorem R117935 : Reach 117935 := rs (se 1 (by rfl) ⟨88451, by rfl⟩) R176903
theorem R249113 : Reach 249113 := rs (se 2 (by rfl) ⟨93417, by rfl⟩) R186835
theorem R52571 : Reach 52571 := rs (se 1 (by rfl) ⟨39428, by rfl⟩) R78857
theorem R150893 : Reach 150893 := rs (se 3 (by rfl) ⟨28292, by rfl⟩) R56585
theorem R52601 : Reach 52601 := rs (se 2 (by rfl) ⟨19725, by rfl⟩) R39451
theorem R52607 : Reach 52607 := rs (se 1 (by rfl) ⟨39455, by rfl⟩) R78911
theorem R85607 : Reach 85607 := rs (se 1 (by rfl) ⟨64205, by rfl⟩) R128411
theorem R380533 : Reach 380533 := rs (se 5 (by rfl) ⟨17837, by rfl⟩) R35675
theorem R53311 : Reach 53311 := rs (se 1 (by rfl) ⟨39983, by rfl⟩) R79967
theorem R119177 : Reach 119177 := rs (se 2 (by rfl) ⟨44691, by rfl⟩) R89383
theorem R119663 : Reach 119663 := rs (se 1 (by rfl) ⟨89747, by rfl⟩) R179495
theorem R316295 : Reach 316295 := rs (se 1 (by rfl) ⟨237221, by rfl⟩) R474443
theorem R54175 : Reach 54175 := rs (se 1 (by rfl) ⟨40631, by rfl⟩) R81263
theorem R283763 : Reach 283763 := rs (se 1 (by rfl) ⟨212822, by rfl⟩) R425645
theorem R349733 : Reach 349733 := rs (se 4 (by rfl) ⟨32787, by rfl⟩) R65575
theorem R55199 : Reach 55199 := rs (se 1 (by rfl) ⟨41399, by rfl⟩) R82799
theorem R186785 : Reach 186785 := rs (se 2 (by rfl) ⟨70044, by rfl⟩) R140089
theorem R88553 : Reach 88553 := rs (se 2 (by rfl) ⟨33207, by rfl⟩) R66415
theorem R56135 : Reach 56135 := rs (se 1 (by rfl) ⟨42101, by rfl⟩) R84203
theorem R187535 : Reach 187535 := rs (se 1 (by rfl) ⟨140651, by rfl⟩) R281303
theorem R122593 : Reach 122593 := rs (se 2 (by rfl) ⟨45972, by rfl⟩) R91945
theorem R57199 : Reach 57199 := rs (se 1 (by rfl) ⟨42899, by rfl⟩) R85799
theorem R122867 : Reach 122867 := rs (se 1 (by rfl) ⟨92150, by rfl⟩) R184301
theorem R155927 : Reach 155927 := rs (se 1 (by rfl) ⟨116945, by rfl⟩) R233891
theorem R614789 : Reach 614789 := rs (se 4 (by rfl) ⟨57636, by rfl⟩) R115273
theorem R58063 : Reach 58063 := rs (se 1 (by rfl) ⟨43547, by rfl⟩) R87095
theorem R91115 : Reach 91115 := rs (se 1 (by rfl) ⟨68336, by rfl⟩) R136673
theorem R58415 : Reach 58415 := rs (se 1 (by rfl) ⟨43811, by rfl⟩) R87623
theorem R58441 : Reach 58441 := rs (se 2 (by rfl) ⟨21915, by rfl⟩) R43831
theorem R353819 : Reach 353819 := rs (se 1 (by rfl) ⟨265364, by rfl⟩) R530729
theorem R58907 : Reach 58907 := rs (se 1 (by rfl) ⟨44180, by rfl⟩) R88361
theorem R124811 : Reach 124811 := rs (se 1 (by rfl) ⟨93608, by rfl⟩) R187217
theorem R190451 : Reach 190451 := rs (se 1 (by rfl) ⟨142838, by rfl⟩) R285677
theorem R125783 : Reach 125783 := rs (se 1 (by rfl) ⟨94337, by rfl⟩) R188675
theorem R1338443 : Reach 1338443 := rs (se 1 (by rfl) ⟨1003832, by rfl⟩) R2007665
theorem R192091 : Reach 192091 := rs (se 1 (by rfl) ⟨144068, by rfl⟩) R288137
theorem R159407 : Reach 159407 := rs (se 1 (by rfl) ⟨119555, by rfl⟩) R239111
theorem R290735 : Reach 290735 := rs (se 1 (by rfl) ⟨218051, by rfl⟩) R436103
theorem R487619 : Reach 487619 := rs (se 1 (by rfl) ⟨365714, by rfl⟩) R731429
theorem R61715 : Reach 61715 := rs (se 1 (by rfl) ⟨46286, by rfl⟩) R92573
theorem R127439 : Reach 127439 := rs (se 1 (by rfl) ⟨95579, by rfl⟩) R191159
theorem R848555 : Reach 848555 := rs (se 1 (by rfl) ⟨636416, by rfl⟩) R1272833
theorem R62345 : Reach 62345 := rs (se 2 (by rfl) ⟨23379, by rfl⟩) R46759
theorem R62375 : Reach 62375 := rs (se 1 (by rfl) ⟨46781, by rfl⟩) R93563
theorem R193747 : Reach 193747 := rs (se 1 (by rfl) ⟨145310, by rfl⟩) R290621
theorem R259523 : Reach 259523 := rs (se 1 (by rfl) ⟨194642, by rfl⟩) R389285
theorem R63119 : Reach 63119 := rs (se 1 (by rfl) ⟨47339, by rfl⟩) R94679
theorem R129185 : Reach 129185 := rs (se 2 (by rfl) ⟨48444, by rfl⟩) R96889
theorem R194825 : Reach 194825 := rs (se 2 (by rfl) ⟨73059, by rfl⟩) R146119
theorem R31135 : Reach 31135 := rs (se 1 (by rfl) ⟨23351, by rfl⟩) R46703
theorem R31183 : Reach 31183 := rs (se 1 (by rfl) ⟨23387, by rfl⟩) R46775
theorem R31207 : Reach 31207 := rs (se 1 (by rfl) ⟨23405, by rfl⟩) R46811
theorem R64091 : Reach 64091 := rs (se 1 (by rfl) ⟨48068, by rfl⟩) R96137
theorem R31323 : Reach 31323 := rs (se 1 (by rfl) ⟨23492, by rfl⟩) R46985
theorem R31391 : Reach 31391 := rs (se 1 (by rfl) ⟨23543, by rfl⟩) R47087
theorem R31559 : Reach 31559 := rs (se 1 (by rfl) ⟨23669, by rfl⟩) R47339
theorem R31599 : Reach 31599 := rs (se 1 (by rfl) ⟨23699, by rfl⟩) R47399
theorem R31655 : Reach 31655 := rs (se 1 (by rfl) ⟨23741, by rfl⟩) R47483
theorem R31835 : Reach 31835 := rs (se 1 (by rfl) ⟨23876, by rfl⟩) R47753
theorem R31951 : Reach 31951 := rs (se 1 (by rfl) ⟨23963, by rfl⟩) R47927
theorem R31975 : Reach 31975 := rs (se 1 (by rfl) ⟨23981, by rfl⟩) R47963
theorem R32071 : Reach 32071 := rs (se 1 (by rfl) ⟨24053, by rfl⟩) R48107
theorem R359869 : Reach 359869 := rs (se 3 (by rfl) ⟨67475, by rfl⟩) R134951
theorem R32207 : Reach 32207 := rs (se 1 (by rfl) ⟨24155, by rfl⟩) R48311
theorem R32367 : Reach 32367 := rs (se 1 (by rfl) ⟨24275, by rfl⟩) R48551
theorem R97949 : Reach 97949 := rs (se 3 (by rfl) ⟨18365, by rfl⟩) R36731
theorem R32423 : Reach 32423 := rs (se 1 (by rfl) ⟨24317, by rfl⟩) R48635
theorem R32487 : Reach 32487 := rs (se 1 (by rfl) ⟨24365, by rfl⟩) R48731
theorem R32543 : Reach 32543 := rs (se 1 (by rfl) ⟨24407, by rfl⟩) R48815
theorem R130855 : Reach 130855 := rs (se 1 (by rfl) ⟨98141, by rfl⟩) R196283
theorem R32623 : Reach 32623 := rs (se 1 (by rfl) ⟨24467, by rfl⟩) R48935
theorem R32679 : Reach 32679 := rs (se 1 (by rfl) ⟨24509, by rfl⟩) R49019
theorem R32895 : Reach 32895 := rs (se 1 (by rfl) ⟨24671, by rfl⟩) R49343
theorem R65929 : Reach 65929 := rs (se 2 (by rfl) ⟨24723, by rfl⟩) R49447
theorem R33179 : Reach 33179 := rs (se 1 (by rfl) ⟨24884, by rfl⟩) R49769
theorem R33183 : Reach 33183 := rs (se 1 (by rfl) ⟨24887, by rfl⟩) R49775
theorem R295487 : Reach 295487 := rs (se 1 (by rfl) ⟨221615, by rfl⟩) R443231
theorem R230201 : Reach 230201 := rs (se 2 (by rfl) ⟨86325, by rfl⟩) R172651
theorem R33599 : Reach 33599 := rs (se 1 (by rfl) ⟨25199, by rfl⟩) R50399
theorem R33607 : Reach 33607 := rs (se 1 (by rfl) ⟨25205, by rfl⟩) R50411
theorem R33863 : Reach 33863 := rs (se 1 (by rfl) ⟨25397, by rfl⟩) R50795
theorem R33919 : Reach 33919 := rs (se 1 (by rfl) ⟨25439, by rfl⟩) R50879
theorem R34043 : Reach 34043 := rs (se 1 (by rfl) ⟨25532, by rfl⟩) R51065
theorem R722429 : Reach 722429 := rs (se 3 (by rfl) ⟨135455, by rfl⟩) R270911
theorem R34543 : Reach 34543 := rs (se 1 (by rfl) ⟨25907, by rfl⟩) R51815
theorem R11142947 : Reach 11142947 := rs (se 1 (by rfl) ⟨8357210, by rfl⟩) R16714421
theorem R34671 : Reach 34671 := rs (se 1 (by rfl) ⟨26003, by rfl⟩) R52007
theorem R34887 : Reach 34887 := rs (se 1 (by rfl) ⟨26165, by rfl⟩) R52331
theorem R35047 : Reach 35047 := rs (se 1 (by rfl) ⟨26285, by rfl⟩) R52571
theorem R100595 : Reach 100595 := rs (se 1 (by rfl) ⟨75446, by rfl⟩) R150893
theorem R35067 : Reach 35067 := rs (se 1 (by rfl) ⟨26300, by rfl⟩) R52601
theorem R35071 : Reach 35071 := rs (se 1 (by rfl) ⟨26303, by rfl⟩) R52607
theorem R166333 : Reach 166333 := rs (se 3 (by rfl) ⟨31187, by rfl⟩) R62375
theorem R233155 : Reach 233155 := rs (se 1 (by rfl) ⟨174866, by rfl⟩) R349733
theorem R168317 : Reach 168317 := rs (se 3 (by rfl) ⟨31559, by rfl⟩) R63119
theorem R37423 : Reach 37423 := rs (se 1 (by rfl) ⟨28067, by rfl⟩) R56135
theorem R627941 : Reach 627941 := rs (se 4 (by rfl) ⟨58869, by rfl⟩) R117739
theorem R70991 : Reach 70991 := rs (se 1 (by rfl) ⟨53243, by rfl⟩) R106487
theorem R365957 : Reach 365957 := rs (se 4 (by rfl) ⟨34308, by rfl⟩) R68617
theorem R71081 : Reach 71081 := rs (se 2 (by rfl) ⟨26655, by rfl⟩) R53311
theorem R71135 : Reach 71135 := rs (se 1 (by rfl) ⟨53351, by rfl⟩) R106703
theorem R103951 : Reach 103951 := rs (se 1 (by rfl) ⟨77963, by rfl⟩) R155927
theorem R71231 : Reach 71231 := rs (se 1 (by rfl) ⟨53423, by rfl⟩) R106847
theorem R1054579 : Reach 1054579 := rs (se 1 (by rfl) ⟨790934, by rfl⟩) R1581869
theorem R71711 : Reach 71711 := rs (se 1 (by rfl) ⟨53783, by rfl⟩) R107567
theorem R465011 : Reach 465011 := rs (se 1 (by rfl) ⟨348758, by rfl⟩) R697517
theorem R235879 : Reach 235879 := rs (se 1 (by rfl) ⟨176909, by rfl⟩) R353819
theorem R39271 : Reach 39271 := rs (se 1 (by rfl) ⟨29453, by rfl⟩) R58907
theorem R72143 : Reach 72143 := rs (se 1 (by rfl) ⟨54107, by rfl⟩) R108215
theorem R72233 : Reach 72233 := rs (se 2 (by rfl) ⟨27087, by rfl⟩) R54175
theorem R236141 : Reach 236141 := rs (se 3 (by rfl) ⟨44276, by rfl⟩) R88553
theorem R10623899 : Reach 10623899 := rs (se 1 (by rfl) ⟨7967924, by rfl⟩) R15935849
theorem R170909 : Reach 170909 := rs (se 3 (by rfl) ⟨32045, by rfl⟩) R64091
theorem R105569 : Reach 105569 := rs (se 2 (by rfl) ⟨39588, by rfl⟩) R79177
theorem R892295 : Reach 892295 := rs (se 1 (by rfl) ⟨669221, by rfl⟩) R1338443
theorem R269873 : Reach 269873 := rs (se 2 (by rfl) ⟨101202, by rfl⟩) R202405
theorem R106109 : Reach 106109 := rs (se 3 (by rfl) ⟨19895, by rfl⟩) R39791
theorem R106271 : Reach 106271 := rs (se 1 (by rfl) ⟨79703, by rfl⟩) R159407
theorem R73511 : Reach 73511 := rs (se 1 (by rfl) ⟨55133, by rfl⟩) R110267
theorem R41143 : Reach 41143 := rs (se 1 (by rfl) ⟨30857, by rfl⟩) R61715
theorem R205031 : Reach 205031 := rs (se 1 (by rfl) ⟨153773, by rfl⟩) R307547
theorem R565703 : Reach 565703 := rs (se 1 (by rfl) ⟨424277, by rfl⟩) R848555
theorem R41563 : Reach 41563 := rs (se 1 (by rfl) ⟨31172, by rfl⟩) R62345
theorem R74351 : Reach 74351 := rs (se 1 (by rfl) ⟨55763, by rfl⟩) R111527
theorem R205519 : Reach 205519 := rs (se 1 (by rfl) ⟨154139, by rfl⟩) R308279
theorem R664301 : Reach 664301 := rs (se 3 (by rfl) ⟨124556, by rfl⟩) R249113
theorem R173015 : Reach 173015 := rs (se 1 (by rfl) ⟨129761, by rfl⟩) R259523
theorem R140447 : Reach 140447 := rs (se 1 (by rfl) ⟨105335, by rfl⟩) R210671
theorem R206171 : Reach 206171 := rs (se 1 (by rfl) ⟨154628, by rfl⟩) R309257
theorem R42601 : Reach 42601 := rs (se 2 (by rfl) ⟨15975, by rfl⟩) R31951
theorem R108161 : Reach 108161 := rs (se 2 (by rfl) ⟨40560, by rfl⟩) R81121
theorem R108445 : Reach 108445 := rs (se 3 (by rfl) ⟨20333, by rfl⟩) R40667
theorem R75815 : Reach 75815 := rs (se 1 (by rfl) ⟨56861, by rfl⟩) R113723
theorem R75995 : Reach 75995 := rs (se 1 (by rfl) ⟨56996, by rfl⟩) R113993
theorem R76115 : Reach 76115 := rs (se 1 (by rfl) ⟨57086, by rfl⟩) R114173
theorem R174473 : Reach 174473 := rs (se 2 (by rfl) ⟨65427, by rfl⟩) R130855
theorem R76247 : Reach 76247 := rs (se 1 (by rfl) ⟨57185, by rfl⟩) R114371
theorem R76265 : Reach 76265 := rs (se 2 (by rfl) ⟨28599, by rfl⟩) R57199
theorem R2141315 : Reach 2141315 := rs (se 1 (by rfl) ⟨1605986, by rfl⟩) R3211973
theorem R77147 : Reach 77147 := rs (se 1 (by rfl) ⟨57860, by rfl⟩) R115721
theorem R142823 : Reach 142823 := rs (se 1 (by rfl) ⟨107117, by rfl⟩) R214235
theorem R110159 : Reach 110159 := rs (se 1 (by rfl) ⟨82619, by rfl⟩) R165239
theorem R77417 : Reach 77417 := rs (se 2 (by rfl) ⟨29031, by rfl⟩) R58063
theorem R241541 : Reach 241541 := rs (se 4 (by rfl) ⟨22644, by rfl⟩) R45289
theorem R77921 : Reach 77921 := rs (se 2 (by rfl) ⟨29220, by rfl⟩) R58441
theorem R110699 : Reach 110699 := rs (se 1 (by rfl) ⟨83024, by rfl⟩) R166049
theorem R78047 : Reach 78047 := rs (se 1 (by rfl) ⟨58535, by rfl⟩) R117071
theorem R340199 : Reach 340199 := rs (se 1 (by rfl) ⟨255149, by rfl⟩) R510299
theorem R78623 : Reach 78623 := rs (se 1 (by rfl) ⟨58967, by rfl⟩) R117935
theorem R177065 : Reach 177065 := rs (se 2 (by rfl) ⟨66399, by rfl⟩) R132799
theorem R79451 : Reach 79451 := rs (se 1 (by rfl) ⟨59588, by rfl⟩) R119177
theorem R46747 : Reach 46747 := rs (se 1 (by rfl) ⟨35060, by rfl⟩) R70121
theorem R46799 : Reach 46799 := rs (se 1 (by rfl) ⟨35099, by rfl⟩) R70199
theorem R47003 : Reach 47003 := rs (se 1 (by rfl) ⟨35252, by rfl⟩) R70505
theorem R79775 : Reach 79775 := rs (se 1 (by rfl) ⟨59831, by rfl⟩) R119663
theorem R210863 : Reach 210863 := rs (se 1 (by rfl) ⟨158147, by rfl⟩) R316295
theorem R47039 : Reach 47039 := rs (se 1 (by rfl) ⟨35279, by rfl⟩) R70559
theorem R47207 : Reach 47207 := rs (se 1 (by rfl) ⟨35405, by rfl⟩) R70811
theorem R47591 : Reach 47591 := rs (se 1 (by rfl) ⟨35693, by rfl⟩) R71387
theorem R113183 : Reach 113183 := rs (se 1 (by rfl) ⟨84887, by rfl⟩) R169775
theorem R47663 : Reach 47663 := rs (se 1 (by rfl) ⟨35747, by rfl⟩) R71495
theorem R408185 : Reach 408185 := rs (se 2 (by rfl) ⟨153069, by rfl⟩) R306139
theorem R48335 : Reach 48335 := rs (se 1 (by rfl) ⟨36251, by rfl⟩) R72503
theorem R48425 : Reach 48425 := rs (se 2 (by rfl) ⟨18159, by rfl⟩) R36319
theorem R48455 : Reach 48455 := rs (se 1 (by rfl) ⟨36341, by rfl⟩) R72683
theorem R179567 : Reach 179567 := rs (se 1 (by rfl) ⟨134675, by rfl⟩) R269351
theorem R507377 : Reach 507377 := rs (se 2 (by rfl) ⟨190266, by rfl⟩) R380533
theorem R147197 : Reach 147197 := rs (se 3 (by rfl) ⟨27599, by rfl⟩) R55199
theorem R933713 : Reach 933713 := rs (se 2 (by rfl) ⟨350142, by rfl⟩) R700285
theorem R49055 : Reach 49055 := rs (se 1 (by rfl) ⟨36791, by rfl⟩) R73583
theorem R81911 : Reach 81911 := rs (se 1 (by rfl) ⟨61433, by rfl⟩) R122867
theorem R49145 : Reach 49145 := rs (se 2 (by rfl) ⟨18429, by rfl⟩) R36859
theorem R49289 : Reach 49289 := rs (se 2 (by rfl) ⟨18483, by rfl⟩) R36967
theorem R49295 : Reach 49295 := rs (se 1 (by rfl) ⟨36971, by rfl⟩) R73943
theorem R49385 : Reach 49385 := rs (se 2 (by rfl) ⟨18519, by rfl⟩) R37039
theorem R409859 : Reach 409859 := rs (se 1 (by rfl) ⟨307394, by rfl⟩) R614789
theorem R49415 : Reach 49415 := rs (se 1 (by rfl) ⟨37061, by rfl⟩) R74123
theorem R49511 : Reach 49511 := rs (se 1 (by rfl) ⟨37133, by rfl⟩) R74267
theorem R49631 : Reach 49631 := rs (se 1 (by rfl) ⟨37223, by rfl⟩) R74447
theorem R49883 : Reach 49883 := rs (se 1 (by rfl) ⟨37412, by rfl⟩) R74825
theorem R50297 : Reach 50297 := rs (se 2 (by rfl) ⟨18861, by rfl⟩) R37723
theorem R83207 : Reach 83207 := rs (se 1 (by rfl) ⟨62405, by rfl⟩) R124811
theorem R50495 : Reach 50495 := rs (se 1 (by rfl) ⟨37871, by rfl⟩) R75743
theorem R83855 : Reach 83855 := rs (se 1 (by rfl) ⟨62891, by rfl⟩) R125783
theorem R51167 : Reach 51167 := rs (se 1 (by rfl) ⟨38375, by rfl⟩) R76751
theorem R51227 : Reach 51227 := rs (se 1 (by rfl) ⟨38420, by rfl⟩) R76841
theorem R313391 : Reach 313391 := rs (se 1 (by rfl) ⟨235043, by rfl⟩) R470087
theorem R51383 : Reach 51383 := rs (se 1 (by rfl) ⟨38537, by rfl⟩) R77075
theorem R51407 : Reach 51407 := rs (se 1 (by rfl) ⟨38555, by rfl⟩) R77111
theorem R117119 : Reach 117119 := rs (se 1 (by rfl) ⟨87839, by rfl⟩) R175679
theorem R51803 : Reach 51803 := rs (se 1 (by rfl) ⟨38852, by rfl⟩) R77705
theorem R84959 : Reach 84959 := rs (se 1 (by rfl) ⟨63719, by rfl⟩) R127439
theorem R183343 : Reach 183343 := rs (se 1 (by rfl) ⟨137507, by rfl⟩) R275015
theorem R52535 : Reach 52535 := rs (se 1 (by rfl) ⟨39401, by rfl⟩) R78803
theorem R315065 : Reach 315065 := rs (se 2 (by rfl) ⟨118149, by rfl⟩) R236299
theorem R86123 : Reach 86123 := rs (se 1 (by rfl) ⟨64592, by rfl⟩) R129185
theorem R152057 : Reach 152057 := rs (se 2 (by rfl) ⟨57021, by rfl⟩) R114043
theorem R479825 : Reach 479825 := rs (se 2 (by rfl) ⟨179934, by rfl⟩) R359869
theorem R873929 : Reach 873929 := rs (se 2 (by rfl) ⟨327723, by rfl⟩) R655447
theorem R87713 : Reach 87713 := rs (se 2 (by rfl) ⟨32892, by rfl⟩) R65785
theorem R87743 : Reach 87743 := rs (se 1 (by rfl) ⟨65807, by rfl⟩) R131615
theorem R252179 : Reach 252179 := rs (se 1 (by rfl) ⟨189134, by rfl⟩) R378269
theorem R55579 : Reach 55579 := rs (se 1 (by rfl) ⟨41684, by rfl⟩) R83369
theorem R678449 : Reach 678449 := rs (se 2 (by rfl) ⟨254418, by rfl⟩) R508837
theorem R88735 : Reach 88735 := rs (se 1 (by rfl) ⟨66551, by rfl⟩) R133103
theorem R7625933 : Reach 7625933 := rs (se 3 (by rfl) ⟨1429862, by rfl⟩) R2859725
theorem R56551 : Reach 56551 := rs (se 1 (by rfl) ⟨42413, by rfl⟩) R84827
theorem R122107 : Reach 122107 := rs (se 1 (by rfl) ⟨91580, by rfl⟩) R183161
theorem R89657 : Reach 89657 := rs (se 2 (by rfl) ⟨33621, by rfl⟩) R67243
theorem R57071 : Reach 57071 := rs (se 1 (by rfl) ⟨42803, by rfl⟩) R85607
theorem R90089 : Reach 90089 := rs (se 2 (by rfl) ⟨33783, by rfl⟩) R67567
theorem R155773 : Reach 155773 := rs (se 3 (by rfl) ⟨29207, by rfl⟩) R58415
theorem R680399 : Reach 680399 := rs (se 1 (by rfl) ⟨510299, by rfl⟩) R1020599
theorem R189175 : Reach 189175 := rs (se 1 (by rfl) ⟨141881, by rfl⟩) R283763
theorem R418823 : Reach 418823 := rs (se 1 (by rfl) ⟨314117, by rfl⟩) R628235
theorem R189449 : Reach 189449 := rs (se 2 (by rfl) ⟨71043, by rfl⟩) R142087
theorem R124523 : Reach 124523 := rs (se 1 (by rfl) ⟨93392, by rfl⟩) R186785
theorem R59035 : Reach 59035 := rs (se 1 (by rfl) ⟨44276, by rfl⟩) R88553
theorem R125023 : Reach 125023 := rs (se 1 (by rfl) ⟨93767, by rfl⟩) R187535
theorem R256121 : Reach 256121 := rs (se 2 (by rfl) ⟨96045, by rfl⟩) R192091
theorem R92447 : Reach 92447 := rs (se 1 (by rfl) ⟨69335, by rfl⟩) R138671
theorem R158543 : Reach 158543 := rs (se 1 (by rfl) ⟨118907, by rfl⟩) R237815
theorem R60743 : Reach 60743 := rs (se 1 (by rfl) ⟨45557, by rfl⟩) R91115
theorem R224635 : Reach 224635 := rs (se 1 (by rfl) ⟨168476, by rfl⟩) R336953
theorem R126967 : Reach 126967 := rs (se 1 (by rfl) ⟨95225, by rfl⟩) R190451
theorem R94247 : Reach 94247 := rs (se 1 (by rfl) ⟨70685, by rfl⟩) R141371
theorem R258329 : Reach 258329 := rs (se 2 (by rfl) ⟨96873, by rfl⟩) R193747
theorem R160379 : Reach 160379 := rs (se 1 (by rfl) ⟨120284, by rfl⟩) R240569
theorem R193823 : Reach 193823 := rs (se 1 (by rfl) ⟨145367, by rfl⟩) R290735
theorem R325079 : Reach 325079 := rs (se 1 (by rfl) ⟨243809, by rfl⟩) R487619
theorem R96491 : Reach 96491 := rs (se 1 (by rfl) ⟨72368, by rfl⟩) R144737
theorem R63841 : Reach 63841 := rs (se 2 (by rfl) ⟨23940, by rfl⟩) R47881
theorem R96673 : Reach 96673 := rs (se 2 (by rfl) ⟨36252, by rfl⟩) R72505
theorem R129883 : Reach 129883 := rs (se 1 (by rfl) ⟨97412, by rfl⟩) R194825
theorem R31711 : Reach 31711 := rs (se 1 (by rfl) ⟨23783, by rfl⟩) R47567
theorem R31771 : Reach 31771 := rs (se 1 (by rfl) ⟨23828, by rfl⟩) R47657
theorem R31899 : Reach 31899 := rs (se 1 (by rfl) ⟨23924, by rfl⟩) R47849
theorem R32155 : Reach 32155 := rs (se 1 (by rfl) ⟨24116, by rfl⟩) R48233
theorem R163279 : Reach 163279 := rs (se 1 (by rfl) ⟨122459, by rfl⟩) R244919
theorem R32239 : Reach 32239 := rs (se 1 (by rfl) ⟨24179, by rfl⟩) R48359
theorem R163457 : Reach 163457 := rs (se 2 (by rfl) ⟨61296, by rfl⟩) R122593
theorem R65299 : Reach 65299 := rs (se 1 (by rfl) ⟨48974, by rfl⟩) R97949
theorem R32575 : Reach 32575 := rs (se 1 (by rfl) ⟨24431, by rfl⟩) R48863
theorem R32603 : Reach 32603 := rs (se 1 (by rfl) ⟨24452, by rfl⟩) R48905
theorem R32859 : Reach 32859 := rs (se 1 (by rfl) ⟨24644, by rfl⟩) R49289
theorem R32863 : Reach 32863 := rs (se 1 (by rfl) ⟨24647, by rfl⟩) R49295
theorem R32923 : Reach 32923 := rs (se 1 (by rfl) ⟨24692, by rfl⟩) R49385
theorem R32943 : Reach 32943 := rs (se 1 (by rfl) ⟨24707, by rfl⟩) R49415
theorem R33007 : Reach 33007 := rs (se 1 (by rfl) ⟨24755, by rfl⟩) R49511
theorem R33087 : Reach 33087 := rs (se 1 (by rfl) ⟨24815, by rfl⟩) R49631
theorem R196991 : Reach 196991 := rs (se 1 (by rfl) ⟨147743, by rfl⟩) R295487
theorem R33255 : Reach 33255 := rs (se 1 (by rfl) ⟨24941, by rfl⟩) R49883
theorem R33531 : Reach 33531 := rs (se 1 (by rfl) ⟨25148, by rfl⟩) R50297
theorem R33663 : Reach 33663 := rs (se 1 (by rfl) ⟨25247, by rfl⟩) R50495
theorem R34111 : Reach 34111 := rs (se 1 (by rfl) ⟨25583, by rfl⟩) R51167
theorem R34151 : Reach 34151 := rs (se 1 (by rfl) ⟨25613, by rfl⟩) R51227
theorem R34255 : Reach 34255 := rs (se 1 (by rfl) ⟨25691, by rfl⟩) R51383
theorem R34271 : Reach 34271 := rs (se 1 (by rfl) ⟨25703, by rfl⟩) R51407
theorem R67063 : Reach 67063 := rs (se 1 (by rfl) ⟨50297, by rfl⟩) R100595
theorem R34535 : Reach 34535 := rs (se 1 (by rfl) ⟨25901, by rfl⟩) R51803
theorem R35023 : Reach 35023 := rs (se 1 (by rfl) ⟨26267, by rfl⟩) R52535
theorem R166697 : Reach 166697 := rs (se 2 (by rfl) ⟨62511, by rfl⟩) R125023
theorem R2330477 : Reach 2330477 := rs (se 3 (by rfl) ⟨436964, by rfl⟩) R873929
theorem R168119 : Reach 168119 := rs (se 1 (by rfl) ⟨126089, by rfl⟩) R252179
theorem R299513 : Reach 299513 := rs (se 2 (by rfl) ⟨112317, by rfl⟩) R224635
theorem R7082599 : Reach 7082599 := rs (se 1 (by rfl) ⟨5311949, by rfl⟩) R10623899
theorem R70379 : Reach 70379 := rs (se 1 (by rfl) ⟨52784, by rfl⟩) R105569
theorem R5083955 : Reach 5083955 := rs (se 1 (by rfl) ⟨3812966, by rfl⟩) R7625933
theorem R594863 : Reach 594863 := rs (se 1 (by rfl) ⟨446147, by rfl⟩) R892295
theorem R70739 : Reach 70739 := rs (se 1 (by rfl) ⟨53054, by rfl⟩) R106109
theorem R562301 : Reach 562301 := rs (se 3 (by rfl) ⟨105431, by rfl⟩) R210863
theorem R38047 : Reach 38047 := rs (se 1 (by rfl) ⟨28535, by rfl⟩) R57071
theorem R70847 : Reach 70847 := rs (se 1 (by rfl) ⟨53135, by rfl⟩) R106271
theorem R169289 : Reach 169289 := rs (se 2 (by rfl) ⟨63483, by rfl⟩) R126967
theorem R137447 : Reach 137447 := rs (se 1 (by rfl) ⟨103085, by rfl⟩) R206171
theorem R72107 : Reach 72107 := rs (se 1 (by rfl) ⟨54080, by rfl⟩) R108161
theorem R170747 : Reach 170747 := rs (se 1 (by rfl) ⟨128060, by rfl⟩) R256121
theorem R105695 : Reach 105695 := rs (se 1 (by rfl) ⟨79271, by rfl⟩) R158543
theorem R138601 : Reach 138601 := rs (se 2 (by rfl) ⟨51975, by rfl⟩) R103951
theorem R40495 : Reach 40495 := rs (se 1 (by rfl) ⟨30371, by rfl⟩) R60743
theorem R73439 : Reach 73439 := rs (se 1 (by rfl) ⟨55079, by rfl⟩) R110159
theorem R73799 : Reach 73799 := rs (se 1 (by rfl) ⟨55349, by rfl⟩) R110699
theorem R172219 : Reach 172219 := rs (se 1 (by rfl) ⟨129164, by rfl⟩) R258329
theorem R74105 : Reach 74105 := rs (se 2 (by rfl) ⟨27789, by rfl⟩) R55579
theorem R106919 : Reach 106919 := rs (se 1 (by rfl) ⟨80189, by rfl⟩) R160379
theorem R173177 : Reach 173177 := rs (se 2 (by rfl) ⟨64941, by rfl⟩) R129883
theorem R75401 : Reach 75401 := rs (se 2 (by rfl) ⟨28275, by rfl⟩) R56551
theorem R75455 : Reach 75455 := rs (se 1 (by rfl) ⟨56591, by rfl⟩) R113183
theorem R272123 : Reach 272123 := rs (se 1 (by rfl) ⟨204092, by rfl⟩) R408185
theorem R338251 : Reach 338251 := rs (se 1 (by rfl) ⟨253688, by rfl⟩) R507377
theorem R108971 : Reach 108971 := rs (se 1 (by rfl) ⟨81728, by rfl⟩) R163457
theorem R207697 : Reach 207697 := rs (se 2 (by rfl) ⟨77886, by rfl⟩) R155773
theorem R273239 : Reach 273239 := rs (se 1 (by rfl) ⟨204929, by rfl⟩) R409859
theorem R274025 : Reach 274025 := rs (se 2 (by rfl) ⟨102759, by rfl⟩) R205519
theorem R405485 : Reach 405485 := rs (se 3 (by rfl) ⟨76028, by rfl⟩) R152057
theorem R208927 : Reach 208927 := rs (se 1 (by rfl) ⟨156695, by rfl⟩) R313391
theorem R78079 : Reach 78079 := rs (se 1 (by rfl) ⟨58559, by rfl⟩) R117119
theorem R1258021 : Reach 1258021 := rs (se 4 (by rfl) ⟨117939, by rfl⟩) R235879
theorem R78713 : Reach 78713 := rs (se 2 (by rfl) ⟨29517, by rfl⟩) R59035
theorem R210043 : Reach 210043 := rs (se 1 (by rfl) ⟨157532, by rfl⟩) R315065
theorem R144593 : Reach 144593 := rs (se 2 (by rfl) ⟨54222, by rfl⟩) R108445
theorem R112211 : Reach 112211 := rs (se 1 (by rfl) ⟨84158, by rfl⟩) R168317
theorem R47327 : Reach 47327 := rs (se 1 (by rfl) ⟨35495, by rfl⟩) R70991
theorem R243971 : Reach 243971 := rs (se 1 (by rfl) ⟨182978, by rfl⟩) R365957
theorem R47387 : Reach 47387 := rs (se 1 (by rfl) ⟨35540, by rfl⟩) R71081
theorem R47423 : Reach 47423 := rs (se 1 (by rfl) ⟨35567, by rfl⟩) R71135
theorem R47807 : Reach 47807 := rs (se 1 (by rfl) ⟨35855, by rfl⟩) R71711
theorem R244457 : Reach 244457 := rs (se 2 (by rfl) ⟨91671, by rfl⟩) R183343
theorem R310007 : Reach 310007 := rs (se 1 (by rfl) ⟨232505, by rfl⟩) R465011
theorem R48095 : Reach 48095 := rs (se 1 (by rfl) ⟨36071, by rfl⟩) R72143
theorem R48155 : Reach 48155 := rs (se 1 (by rfl) ⟨36116, by rfl⟩) R72233
theorem R113939 : Reach 113939 := rs (se 1 (by rfl) ⟨85454, by rfl⟩) R170909
theorem R310873 : Reach 310873 := rs (se 2 (by rfl) ⟨116577, by rfl⟩) R233155
theorem R179915 : Reach 179915 := rs (se 1 (by rfl) ⟨134936, by rfl⟩) R269873
theorem R49007 : Reach 49007 := rs (se 1 (by rfl) ⟨36755, by rfl⟩) R73511
theorem R377135 : Reach 377135 := rs (se 1 (by rfl) ⟨282851, by rfl⟩) R565703
theorem R49567 : Reach 49567 := rs (se 1 (by rfl) ⟨37175, by rfl⟩) R74351
theorem R442867 : Reach 442867 := rs (se 1 (by rfl) ⟨332150, by rfl⟩) R664301
theorem R115343 : Reach 115343 := rs (se 1 (by rfl) ⟨86507, by rfl⟩) R173015
theorem R279215 : Reach 279215 := rs (se 1 (by rfl) ⟨209411, by rfl⟩) R418823
theorem R49897 : Reach 49897 := rs (se 2 (by rfl) ⟨18711, by rfl⟩) R37423
theorem R83015 : Reach 83015 := rs (se 1 (by rfl) ⟨62261, by rfl⟩) R124523
theorem R50543 : Reach 50543 := rs (se 1 (by rfl) ⟨37907, by rfl⟩) R75815
theorem R50663 : Reach 50663 := rs (se 1 (by rfl) ⟨37997, by rfl⟩) R75995
theorem R50743 : Reach 50743 := rs (se 1 (by rfl) ⟨38057, by rfl⟩) R76115
theorem R116315 : Reach 116315 := rs (se 1 (by rfl) ⟨87236, by rfl⟩) R174473
theorem R50831 : Reach 50831 := rs (se 1 (by rfl) ⟨38123, by rfl⟩) R76247
theorem R50843 : Reach 50843 := rs (se 1 (by rfl) ⟨38132, by rfl⟩) R76265
theorem R1427543 : Reach 1427543 := rs (se 1 (by rfl) ⟨1070657, by rfl⟩) R2141315
theorem R51431 : Reach 51431 := rs (se 1 (by rfl) ⟨38573, by rfl⟩) R77147
theorem R51611 : Reach 51611 := rs (se 1 (by rfl) ⟨38708, by rfl⟩) R77417
theorem R870821 : Reach 870821 := rs (se 4 (by rfl) ⟨81639, by rfl⟩) R163279
theorem R51947 : Reach 51947 := rs (se 1 (by rfl) ⟨38960, by rfl⟩) R77921
theorem R52031 : Reach 52031 := rs (se 1 (by rfl) ⟨39023, by rfl⟩) R78047
theorem R85121 : Reach 85121 := rs (se 2 (by rfl) ⟨31920, by rfl⟩) R63841
theorem R52361 : Reach 52361 := rs (se 2 (by rfl) ⟨19635, by rfl⟩) R39271
theorem R52415 : Reach 52415 := rs (se 1 (by rfl) ⟨39311, by rfl⟩) R78623
theorem R118043 : Reach 118043 := rs (se 1 (by rfl) ⟨88532, by rfl⟩) R177065
theorem R249317 : Reach 249317 := rs (se 4 (by rfl) ⟨23373, by rfl⟩) R46747
theorem R118313 : Reach 118313 := rs (se 2 (by rfl) ⟨44367, by rfl⟩) R88735
theorem R216719 : Reach 216719 := rs (se 1 (by rfl) ⟨162539, by rfl⟩) R325079
theorem R52967 : Reach 52967 := rs (se 1 (by rfl) ⟨39725, by rfl⟩) R79451
theorem R53183 : Reach 53183 := rs (se 1 (by rfl) ⟨39887, by rfl⟩) R79775
theorem R119711 : Reach 119711 := rs (se 1 (by rfl) ⟨89783, by rfl⟩) R179567
theorem R87065 : Reach 87065 := rs (se 2 (by rfl) ⟨32649, by rfl⟩) R65299
theorem R54607 : Reach 54607 := rs (se 1 (by rfl) ⟨40955, by rfl⟩) R81911
theorem R54857 : Reach 54857 := rs (se 2 (by rfl) ⟨20571, by rfl⟩) R41143
theorem R87905 : Reach 87905 := rs (se 2 (by rfl) ⟨32964, by rfl⟩) R65929
theorem R153467 : Reach 153467 := rs (se 1 (by rfl) ⟨115100, by rfl⟩) R230201
theorem R546749 : Reach 546749 := rs (se 3 (by rfl) ⟨102515, by rfl⟩) R205031
theorem R55417 : Reach 55417 := rs (se 2 (by rfl) ⟨20781, by rfl⟩) R41563
theorem R55471 : Reach 55471 := rs (se 1 (by rfl) ⟨41603, by rfl⟩) R83207
theorem R252233 : Reach 252233 := rs (se 2 (by rfl) ⟨94587, by rfl⟩) R189175
theorem R481619 : Reach 481619 := rs (se 1 (by rfl) ⟨361214, by rfl⟩) R722429
theorem R7428631 : Reach 7428631 := rs (se 1 (by rfl) ⟨5571473, by rfl⟩) R11142947
theorem R55903 : Reach 55903 := rs (se 1 (by rfl) ⟨41927, by rfl⟩) R83855
theorem R56639 : Reach 56639 := rs (se 1 (by rfl) ⟨42479, by rfl⟩) R84959
theorem R56801 : Reach 56801 := rs (se 2 (by rfl) ⟨21300, by rfl⟩) R42601
theorem R57415 : Reach 57415 := rs (se 1 (by rfl) ⟨43061, by rfl⟩) R86123
theorem R319883 : Reach 319883 := rs (se 1 (by rfl) ⟨239912, by rfl⟩) R479825
theorem R221777 : Reach 221777 := rs (se 2 (by rfl) ⟨83166, by rfl⟩) R166333
theorem R418627 : Reach 418627 := rs (se 1 (by rfl) ⟨313970, by rfl⟩) R627941
theorem R58475 : Reach 58475 := rs (se 1 (by rfl) ⟨43856, by rfl⟩) R87713
theorem R58495 : Reach 58495 := rs (se 1 (by rfl) ⟨43871, by rfl⟩) R87743
theorem R189949 : Reach 189949 := rs (se 3 (by rfl) ⟨35615, by rfl⟩) R71231
theorem R452299 : Reach 452299 := rs (se 1 (by rfl) ⟨339224, by rfl⟩) R678449
theorem R157427 : Reach 157427 := rs (se 1 (by rfl) ⟨118070, by rfl⟩) R236141
theorem R59771 : Reach 59771 := rs (se 1 (by rfl) ⟨44828, by rfl⟩) R89657
theorem R60059 : Reach 60059 := rs (se 1 (by rfl) ⟨45044, by rfl⟩) R90089
theorem R453599 : Reach 453599 := rs (se 1 (by rfl) ⟨340199, by rfl⟩) R680399
theorem R126299 : Reach 126299 := rs (se 1 (by rfl) ⟨94724, by rfl⟩) R189449
theorem R93631 : Reach 93631 := rs (se 1 (by rfl) ⟨70223, by rfl⟩) R140447
theorem R61631 : Reach 61631 := rs (se 1 (by rfl) ⟨46223, by rfl⟩) R92447
theorem R95215 : Reach 95215 := rs (se 1 (by rfl) ⟨71411, by rfl⟩) R142823
theorem R1406105 : Reach 1406105 := rs (se 2 (by rfl) ⟨527289, by rfl⟩) R1054579
theorem R161027 : Reach 161027 := rs (se 1 (by rfl) ⟨120770, by rfl⟩) R241541
theorem R62831 : Reach 62831 := rs (se 1 (by rfl) ⟨47123, by rfl⟩) R94247
theorem R226799 : Reach 226799 := rs (se 1 (by rfl) ⟨170099, by rfl⟩) R340199
theorem R128897 : Reach 128897 := rs (se 2 (by rfl) ⟨48336, by rfl⟩) R96673
theorem R129215 : Reach 129215 := rs (se 1 (by rfl) ⟨96911, by rfl⟩) R193823
theorem R31199 : Reach 31199 := rs (se 1 (by rfl) ⟨23399, by rfl⟩) R46799
theorem R31335 : Reach 31335 := rs (se 1 (by rfl) ⟨23501, by rfl⟩) R47003
theorem R31359 : Reach 31359 := rs (se 1 (by rfl) ⟨23519, by rfl⟩) R47039
theorem R31471 : Reach 31471 := rs (se 1 (by rfl) ⟨23603, by rfl⟩) R47207
theorem R64327 : Reach 64327 := rs (se 1 (by rfl) ⟨48245, by rfl⟩) R96491
theorem R31727 : Reach 31727 := rs (se 1 (by rfl) ⟨23795, by rfl⟩) R47591
theorem R162809 : Reach 162809 := rs (se 2 (by rfl) ⟨61053, by rfl⟩) R122107
theorem R31775 : Reach 31775 := rs (se 1 (by rfl) ⟨23831, by rfl⟩) R47663
theorem R32223 : Reach 32223 := rs (se 1 (by rfl) ⟨24167, by rfl⟩) R48335
theorem R32283 : Reach 32283 := rs (se 1 (by rfl) ⟨24212, by rfl⟩) R48425
theorem R32303 : Reach 32303 := rs (se 1 (by rfl) ⟨24227, by rfl⟩) R48455
theorem R98131 : Reach 98131 := rs (se 1 (by rfl) ⟨73598, by rfl⟩) R147197
theorem R622475 : Reach 622475 := rs (se 1 (by rfl) ⟨466856, by rfl⟩) R933713
theorem R32703 : Reach 32703 := rs (se 1 (by rfl) ⟨24527, by rfl⟩) R49055
theorem R32763 : Reach 32763 := rs (se 1 (by rfl) ⟨24572, by rfl⟩) R49145
theorem R229625 : Reach 229625 := rs (se 2 (by rfl) ⟨86109, by rfl⟩) R172219
theorem R131327 : Reach 131327 := rs (se 1 (by rfl) ⟨98495, by rfl⟩) R196991
theorem R66089 : Reach 66089 := rs (se 2 (by rfl) ⟨24783, by rfl⟩) R49567
theorem R590489 : Reach 590489 := rs (se 2 (by rfl) ⟨221433, by rfl⟩) R442867
theorem R33695 : Reach 33695 := rs (se 1 (by rfl) ⟨25271, by rfl⟩) R50543
theorem R66529 : Reach 66529 := rs (se 2 (by rfl) ⟨24948, by rfl⟩) R49897
theorem R33775 : Reach 33775 := rs (se 1 (by rfl) ⟨25331, by rfl⟩) R50663
theorem R853021 : Reach 853021 := rs (se 3 (by rfl) ⟨159941, by rfl⟩) R319883
theorem R33887 : Reach 33887 := rs (se 1 (by rfl) ⟨25415, by rfl⟩) R50831
theorem R33895 : Reach 33895 := rs (se 1 (by rfl) ⟨25421, by rfl⟩) R50843
theorem R951695 : Reach 951695 := rs (se 1 (by rfl) ⟨713771, by rfl⟩) R1427543
theorem R34287 : Reach 34287 := rs (se 1 (by rfl) ⟨25715, by rfl⟩) R51431
theorem R34407 : Reach 34407 := rs (se 1 (by rfl) ⟨25805, by rfl⟩) R51611
theorem R34631 : Reach 34631 := rs (se 1 (by rfl) ⟨25973, by rfl⟩) R51947
theorem R34687 : Reach 34687 := rs (se 1 (by rfl) ⟨26015, by rfl⟩) R52031
theorem R67657 : Reach 67657 := rs (se 2 (by rfl) ⟨25371, by rfl⟩) R50743
theorem R34907 : Reach 34907 := rs (se 1 (by rfl) ⟨26180, by rfl⟩) R52361
theorem R34943 : Reach 34943 := rs (se 1 (by rfl) ⟨26207, by rfl⟩) R52415
theorem R166211 : Reach 166211 := rs (se 1 (by rfl) ⟨124658, by rfl⟩) R249317
theorem R35311 : Reach 35311 := rs (se 1 (by rfl) ⟨26483, by rfl⟩) R52967
theorem R35455 : Reach 35455 := rs (se 1 (by rfl) ⟨26591, by rfl⟩) R53183
theorem R199675 : Reach 199675 := rs (se 1 (by rfl) ⟨149756, by rfl⟩) R299513
theorem R396575 : Reach 396575 := rs (se 1 (by rfl) ⟨297431, by rfl⟩) R594863
theorem R36571 : Reach 36571 := rs (se 1 (by rfl) ⟨27428, by rfl⟩) R54857
theorem R167845 : Reach 167845 := rs (se 4 (by rfl) ⟨15735, by rfl⟩) R31471
theorem R102311 : Reach 102311 := rs (se 1 (by rfl) ⟨76733, by rfl⟩) R153467
theorem R364499 : Reach 364499 := rs (se 1 (by rfl) ⟨273374, by rfl⟩) R546749
theorem R168155 : Reach 168155 := rs (se 1 (by rfl) ⟨126116, by rfl⟩) R252233
theorem R2232677 : Reach 2232677 := rs (se 4 (by rfl) ⟨209313, by rfl⟩) R418627
theorem R70463 : Reach 70463 := rs (se 1 (by rfl) ⟨52847, by rfl⟩) R105695
theorem R37759 : Reach 37759 := rs (se 1 (by rfl) ⟨28319, by rfl⟩) R56639
theorem R37867 : Reach 37867 := rs (se 1 (by rfl) ⟨28400, by rfl⟩) R56801
theorem R71279 : Reach 71279 := rs (se 1 (by rfl) ⟨53459, by rfl⟩) R106919
theorem R104105 : Reach 104105 := rs (se 2 (by rfl) ⟨39039, by rfl⟩) R78079
theorem R1677361 : Reach 1677361 := rs (se 2 (by rfl) ⟨629010, by rfl⟩) R1258021
theorem R38983 : Reach 38983 := rs (se 1 (by rfl) ⟨29237, by rfl⟩) R58475
theorem R9443465 : Reach 9443465 := rs (se 2 (by rfl) ⟨3541299, by rfl⟩) R7082599
theorem R104951 : Reach 104951 := rs (se 1 (by rfl) ⟨78713, by rfl⟩) R157427
theorem R39847 : Reach 39847 := rs (se 1 (by rfl) ⟨29885, by rfl⟩) R59771
theorem R72647 : Reach 72647 := rs (se 1 (by rfl) ⟨54485, by rfl⟩) R108971
theorem R72809 : Reach 72809 := rs (se 2 (by rfl) ⟨27303, by rfl⟩) R54607
theorem R826685 : Reach 826685 := rs (se 3 (by rfl) ⟨155003, by rfl⟩) R310007
theorem R302399 : Reach 302399 := rs (se 1 (by rfl) ⟨226799, by rfl⟩) R453599
theorem R270323 : Reach 270323 := rs (se 1 (by rfl) ⟨202742, by rfl⟩) R405485
theorem R41087 : Reach 41087 := rs (se 1 (by rfl) ⟨30815, by rfl⟩) R61631
theorem R73889 : Reach 73889 := rs (se 2 (by rfl) ⟨27708, by rfl⟩) R55417
theorem R73961 : Reach 73961 := rs (se 2 (by rfl) ⟨27735, by rfl⟩) R55471
theorem R9904841 : Reach 9904841 := rs (se 2 (by rfl) ⟨3714315, by rfl⟩) R7428631
theorem R74537 : Reach 74537 := rs (se 2 (by rfl) ⟨27951, by rfl⟩) R55903
theorem R107351 : Reach 107351 := rs (se 1 (by rfl) ⟨80513, by rfl⟩) R161027
theorem R41887 : Reach 41887 := rs (se 1 (by rfl) ⟨31415, by rfl⟩) R62831
theorem R74807 : Reach 74807 := rs (se 1 (by rfl) ⟨56105, by rfl⟩) R112211
theorem R108539 : Reach 108539 := rs (se 1 (by rfl) ⟨81404, by rfl⟩) R162809
theorem R75959 : Reach 75959 := rs (se 1 (by rfl) ⟨56969, by rfl⟩) R113939
theorem R76553 : Reach 76553 := rs (se 2 (by rfl) ⟨28707, by rfl⟩) R57415
theorem R43897 : Reach 43897 := rs (se 2 (by rfl) ⟨16461, by rfl⟩) R32923
theorem R76895 : Reach 76895 := rs (se 1 (by rfl) ⟨57671, by rfl⟩) R115343
theorem R77543 : Reach 77543 := rs (se 1 (by rfl) ⟨58157, by rfl⟩) R116315
theorem R77993 : Reach 77993 := rs (se 2 (by rfl) ⟨29247, by rfl⟩) R58495
theorem R111131 : Reach 111131 := rs (se 1 (by rfl) ⟨83348, by rfl⟩) R166697
theorem R78695 : Reach 78695 := rs (se 1 (by rfl) ⟨59021, by rfl⟩) R118043
theorem R603065 : Reach 603065 := rs (se 2 (by rfl) ⟨226149, by rfl⟩) R452299
theorem R78875 : Reach 78875 := rs (se 1 (by rfl) ⟨59156, by rfl⟩) R118313
theorem R144479 : Reach 144479 := rs (se 1 (by rfl) ⟨108359, by rfl⟩) R216719
theorem R1553651 : Reach 1553651 := rs (se 1 (by rfl) ⟨1165238, by rfl⟩) R2330477
theorem R112079 : Reach 112079 := rs (se 1 (by rfl) ⟨84059, by rfl⟩) R168119
theorem R46697 : Reach 46697 := rs (se 2 (by rfl) ⟨17511, by rfl⟩) R35023
theorem R46919 : Reach 46919 := rs (se 1 (by rfl) ⟨35189, by rfl⟩) R70379
theorem R3389303 : Reach 3389303 := rs (se 1 (by rfl) ⟨2541977, by rfl⟩) R5083955
theorem R79807 : Reach 79807 := rs (se 1 (by rfl) ⟨59855, by rfl⟩) R119711
theorem R47159 : Reach 47159 := rs (se 1 (by rfl) ⟨35369, by rfl⟩) R70739
theorem R374867 : Reach 374867 := rs (se 1 (by rfl) ⟨281150, by rfl⟩) R562301
theorem R47231 : Reach 47231 := rs (se 1 (by rfl) ⟨35423, by rfl⟩) R70847
theorem R112859 : Reach 112859 := rs (se 1 (by rfl) ⟨84644, by rfl⟩) R169289
theorem R276929 : Reach 276929 := rs (se 2 (by rfl) ⟨103848, by rfl⟩) R207697
theorem R48071 : Reach 48071 := rs (se 1 (by rfl) ⟨36053, by rfl⟩) R72107
theorem R113831 : Reach 113831 := rs (se 1 (by rfl) ⟨85373, by rfl⟩) R170747
theorem R48959 : Reach 48959 := rs (se 1 (by rfl) ⟨36719, by rfl⟩) R73439
theorem R278569 : Reach 278569 := rs (se 2 (by rfl) ⟨104463, by rfl⟩) R208927
theorem R49199 : Reach 49199 := rs (se 1 (by rfl) ⟨36899, by rfl⟩) R73799
theorem R49403 : Reach 49403 := rs (se 1 (by rfl) ⟨37052, by rfl⟩) R74105
theorem R147851 : Reach 147851 := rs (se 1 (by rfl) ⟨110888, by rfl⟩) R221777
theorem R115451 : Reach 115451 := rs (se 1 (by rfl) ⟨86588, by rfl⟩) R173177
theorem R50267 : Reach 50267 := rs (se 1 (by rfl) ⟨37700, by rfl⟩) R75401
theorem R50303 : Reach 50303 := rs (se 1 (by rfl) ⟨37727, by rfl⟩) R75455
theorem R181415 : Reach 181415 := rs (se 1 (by rfl) ⟨136061, by rfl⟩) R272123
theorem R280057 : Reach 280057 := rs (se 2 (by rfl) ⟨105021, by rfl⟩) R210043
theorem R50729 : Reach 50729 := rs (se 2 (by rfl) ⟨19023, by rfl⟩) R38047
theorem R182159 : Reach 182159 := rs (se 1 (by rfl) ⟨136619, by rfl⟩) R273239
theorem R84199 : Reach 84199 := rs (se 1 (by rfl) ⟨63149, by rfl⟩) R126299
theorem R182683 : Reach 182683 := rs (se 1 (by rfl) ⟨137012, by rfl⟩) R274025
theorem R52475 : Reach 52475 := rs (se 1 (by rfl) ⟨39356, by rfl⟩) R78713
theorem R937403 : Reach 937403 := rs (se 1 (by rfl) ⟨703052, by rfl⟩) R1406105
theorem R151199 : Reach 151199 := rs (se 1 (by rfl) ⟨113399, by rfl⟩) R226799
theorem R85769 : Reach 85769 := rs (se 2 (by rfl) ⟨32163, by rfl⟩) R64327
theorem R85931 : Reach 85931 := rs (se 1 (by rfl) ⟨64448, by rfl⟩) R128897
theorem R151469 : Reach 151469 := rs (se 3 (by rfl) ⟨28400, by rfl⟩) R56801
theorem R86143 : Reach 86143 := rs (se 1 (by rfl) ⟨64607, by rfl⟩) R129215
theorem R184801 : Reach 184801 := rs (se 2 (by rfl) ⟨69300, by rfl⟩) R138601
theorem R479773 : Reach 479773 := rs (se 3 (by rfl) ⟨89957, by rfl⟩) R179915
theorem R53993 : Reach 53993 := rs (se 2 (by rfl) ⟨20247, by rfl⟩) R40495
theorem R414497 : Reach 414497 := rs (se 2 (by rfl) ⟨155436, by rfl⟩) R310873
theorem R414983 : Reach 414983 := rs (se 1 (by rfl) ⟨311237, by rfl⟩) R622475
theorem R251423 : Reach 251423 := rs (se 1 (by rfl) ⟨188567, by rfl⟩) R377135
theorem R186143 : Reach 186143 := rs (se 1 (by rfl) ⟨139607, by rfl⟩) R279215
theorem R55343 : Reach 55343 := rs (se 1 (by rfl) ⟨41507, by rfl⟩) R83015
theorem R580547 : Reach 580547 := rs (se 1 (by rfl) ⟨435410, by rfl⟩) R870821
theorem R89417 : Reach 89417 := rs (se 2 (by rfl) ⟨33531, by rfl⟩) R67063
theorem R253265 : Reach 253265 := rs (se 2 (by rfl) ⟨94974, by rfl⟩) R189949
theorem R56747 : Reach 56747 := rs (se 1 (by rfl) ⟨42560, by rfl⟩) R85121
theorem R451001 : Reach 451001 := rs (se 2 (by rfl) ⟨169125, by rfl⟩) R338251
theorem R58043 : Reach 58043 := rs (se 1 (by rfl) ⟨43532, by rfl⟩) R87065
theorem R58603 : Reach 58603 := rs (se 1 (by rfl) ⟨43952, by rfl⟩) R87905
theorem R91631 : Reach 91631 := rs (se 1 (by rfl) ⟨68723, by rfl⟩) R137447
theorem R321079 : Reach 321079 := rs (se 1 (by rfl) ⟨240809, by rfl⟩) R481619
theorem R124841 : Reach 124841 := rs (se 2 (by rfl) ⟨46815, by rfl⟩) R93631
theorem R126953 : Reach 126953 := rs (se 2 (by rfl) ⟨47607, by rfl⟩) R95215
theorem R160157 : Reach 160157 := rs (se 3 (by rfl) ⟨30029, by rfl⟩) R60059
theorem R96395 : Reach 96395 := rs (se 1 (by rfl) ⟨72296, by rfl⟩) R144593
theorem R31551 : Reach 31551 := rs (se 1 (by rfl) ⟨23663, by rfl⟩) R47327
theorem R162647 : Reach 162647 := rs (se 1 (by rfl) ⟨121985, by rfl⟩) R243971
theorem R31591 : Reach 31591 := rs (se 1 (by rfl) ⟨23693, by rfl⟩) R47387
theorem R31615 : Reach 31615 := rs (se 1 (by rfl) ⟨23711, by rfl⟩) R47423
theorem R31871 : Reach 31871 := rs (se 1 (by rfl) ⟨23903, by rfl⟩) R47807
theorem R162971 : Reach 162971 := rs (se 1 (by rfl) ⟨122228, by rfl⟩) R244457
theorem R32063 : Reach 32063 := rs (se 1 (by rfl) ⟨24047, by rfl⟩) R48095
theorem R32103 : Reach 32103 := rs (se 1 (by rfl) ⟨24077, by rfl⟩) R48155
theorem R130841 : Reach 130841 := rs (se 2 (by rfl) ⟨49065, by rfl⟩) R98131
theorem R32671 : Reach 32671 := rs (se 1 (by rfl) ⟨24503, by rfl⟩) R49007
theorem R32799 : Reach 32799 := rs (se 1 (by rfl) ⟨24599, by rfl⟩) R49199
theorem R32935 : Reach 32935 := rs (se 1 (by rfl) ⟨24701, by rfl⟩) R49403
theorem R98567 : Reach 98567 := rs (se 1 (by rfl) ⟨73925, by rfl⟩) R147851
theorem R393659 : Reach 393659 := rs (se 1 (by rfl) ⟨295244, by rfl⟩) R590489
theorem R33511 : Reach 33511 := rs (se 1 (by rfl) ⟨25133, by rfl⟩) R50267
theorem R33535 : Reach 33535 := rs (se 1 (by rfl) ⟨25151, by rfl⟩) R50303
theorem R33819 : Reach 33819 := rs (se 1 (by rfl) ⟨25364, by rfl⟩) R50729
theorem R428105 : Reach 428105 := rs (se 2 (by rfl) ⟨160539, by rfl⟩) R321079
theorem R34983 : Reach 34983 := rs (se 1 (by rfl) ⟨26237, by rfl⟩) R52475
theorem R264383 : Reach 264383 := rs (se 1 (by rfl) ⟨198287, by rfl⟩) R396575
theorem R624935 : Reach 624935 := rs (se 1 (by rfl) ⟨468701, by rfl⟩) R937403
theorem R100799 : Reach 100799 := rs (se 1 (by rfl) ⟨75599, by rfl⟩) R151199
theorem R68207 : Reach 68207 := rs (se 1 (by rfl) ⟨51155, by rfl⟩) R102311
theorem R100979 : Reach 100979 := rs (se 1 (by rfl) ⟨75734, by rfl⟩) R151469
theorem R35995 : Reach 35995 := rs (se 1 (by rfl) ⟨26996, by rfl⟩) R53993
theorem R167615 : Reach 167615 := rs (se 1 (by rfl) ⟨125711, by rfl⟩) R251423
theorem R36895 : Reach 36895 := rs (se 1 (by rfl) ⟨27671, by rfl⟩) R55343
theorem R6295643 : Reach 6295643 := rs (se 1 (by rfl) ⟨4721732, by rfl⟩) R9443465
theorem R69967 : Reach 69967 := rs (se 1 (by rfl) ⟨52475, by rfl⟩) R104951
theorem R496381 : Reach 496381 := rs (se 3 (by rfl) ⟨93071, by rfl⟩) R186143
theorem R201599 : Reach 201599 := rs (se 1 (by rfl) ⟨151199, by rfl⟩) R302399
theorem R37831 : Reach 37831 := rs (se 1 (by rfl) ⟨28373, by rfl⟩) R56747
theorem R300667 : Reach 300667 := rs (se 1 (by rfl) ⟨225500, by rfl⟩) R451001
theorem R38695 : Reach 38695 := rs (se 1 (by rfl) ⟨29021, by rfl⟩) R58043
theorem R71567 : Reach 71567 := rs (se 1 (by rfl) ⟨53675, by rfl⟩) R107351
theorem R72359 : Reach 72359 := rs (se 1 (by rfl) ⟨54269, by rfl⟩) R108539
theorem R106409 : Reach 106409 := rs (se 2 (by rfl) ⟨39903, by rfl⟩) R79807
theorem R2236481 : Reach 2236481 := rs (se 2 (by rfl) ⟨838680, by rfl⟩) R1677361
theorem R106771 : Reach 106771 := rs (se 1 (by rfl) ⟨80078, by rfl⟩) R160157
theorem R74087 : Reach 74087 := rs (se 1 (by rfl) ⟨55565, by rfl⟩) R111131
theorem R402043 : Reach 402043 := rs (se 1 (by rfl) ⟨301532, by rfl⟩) R603065
theorem R74719 : Reach 74719 := rs (se 1 (by rfl) ⟨56039, by rfl⟩) R112079
theorem R75239 : Reach 75239 := rs (se 1 (by rfl) ⟨56429, by rfl⟩) R112859
theorem R108431 : Reach 108431 := rs (se 1 (by rfl) ⟨81323, by rfl⟩) R162647
theorem R108647 : Reach 108647 := rs (se 1 (by rfl) ⟨81485, by rfl⟩) R162971
theorem R75887 : Reach 75887 := rs (se 1 (by rfl) ⟨56915, by rfl⟩) R113831
theorem R371425 : Reach 371425 := rs (se 2 (by rfl) ⟨139284, by rfl⟩) R278569
theorem R109565 : Reach 109565 := rs (se 3 (by rfl) ⟨20543, by rfl⟩) R41087
theorem R44059 : Reach 44059 := rs (se 1 (by rfl) ⟨33044, by rfl⟩) R66089
theorem R76967 : Reach 76967 := rs (se 1 (by rfl) ⟨57725, by rfl⟩) R115451
theorem R634463 : Reach 634463 := rs (se 1 (by rfl) ⟨475847, by rfl⟩) R951695
theorem R45193 : Reach 45193 := rs (se 2 (by rfl) ⟨16947, by rfl⟩) R33895
theorem R110807 : Reach 110807 := rs (se 1 (by rfl) ⟨83105, by rfl⟩) R166211
theorem R78137 : Reach 78137 := rs (se 2 (by rfl) ⟨29301, by rfl⟩) R58603
theorem R373409 : Reach 373409 := rs (se 2 (by rfl) ⟨140028, by rfl⟩) R280057
theorem R242999 : Reach 242999 := rs (se 1 (by rfl) ⟨182249, by rfl⟩) R364499
theorem R112103 : Reach 112103 := rs (se 1 (by rfl) ⟨84077, by rfl⟩) R168155
theorem R1488451 : Reach 1488451 := rs (se 1 (by rfl) ⟨1116338, by rfl⟩) R2232677
theorem R112265 : Reach 112265 := rs (se 2 (by rfl) ⟨42099, by rfl⟩) R84199
theorem R243577 : Reach 243577 := rs (se 2 (by rfl) ⟨91341, by rfl⟩) R182683
theorem R46975 : Reach 46975 := rs (se 1 (by rfl) ⟨35231, by rfl⟩) R70463
theorem R47081 : Reach 47081 := rs (se 2 (by rfl) ⟨17655, by rfl⟩) R35311
theorem R47273 : Reach 47273 := rs (se 2 (by rfl) ⟨17727, by rfl⟩) R35455
theorem R276655 : Reach 276655 := rs (se 1 (by rfl) ⟨207491, by rfl⟩) R414983
theorem R47519 : Reach 47519 := rs (se 1 (by rfl) ⟨35639, by rfl⟩) R71279
theorem R277613 : Reach 277613 := rs (se 3 (by rfl) ⟨52052, by rfl⟩) R104105
theorem R48431 : Reach 48431 := rs (se 1 (by rfl) ⟨36323, by rfl⟩) R72647
theorem R48539 : Reach 48539 := rs (se 1 (by rfl) ⟨36404, by rfl⟩) R72809
theorem R48761 : Reach 48761 := rs (se 2 (by rfl) ⟨18285, by rfl⟩) R36571
theorem R1064933 : Reach 1064933 := rs (se 4 (by rfl) ⟨99837, by rfl⟩) R199675
theorem R180215 : Reach 180215 := rs (se 1 (by rfl) ⟨135161, by rfl⟩) R270323
theorem R49259 : Reach 49259 := rs (se 1 (by rfl) ⟨36944, by rfl⟩) R73889
theorem R49307 : Reach 49307 := rs (se 1 (by rfl) ⟨36980, by rfl⟩) R73961
theorem R114857 : Reach 114857 := rs (se 2 (by rfl) ⟨43071, by rfl⟩) R86143
theorem R6603227 : Reach 6603227 := rs (se 1 (by rfl) ⟨4952420, by rfl⟩) R9904841
theorem R49691 : Reach 49691 := rs (se 1 (by rfl) ⟨37268, by rfl⟩) R74537
theorem R246401 : Reach 246401 := rs (se 2 (by rfl) ⟨92400, by rfl⟩) R184801
theorem R49871 : Reach 49871 := rs (se 1 (by rfl) ⟨37403, by rfl⟩) R74807
theorem R639697 : Reach 639697 := rs (se 2 (by rfl) ⟨239886, by rfl⟩) R479773
theorem R50345 : Reach 50345 := rs (se 2 (by rfl) ⟨18879, by rfl⟩) R37759
theorem R83227 : Reach 83227 := rs (se 1 (by rfl) ⟨62420, by rfl⟩) R124841
theorem R50489 : Reach 50489 := rs (se 2 (by rfl) ⟨18933, by rfl⟩) R37867
theorem R50639 : Reach 50639 := rs (se 1 (by rfl) ⟨37979, by rfl⟩) R75959
theorem R51035 : Reach 51035 := rs (se 1 (by rfl) ⟨38276, by rfl⟩) R76553
theorem R51263 : Reach 51263 := rs (se 1 (by rfl) ⟨38447, by rfl⟩) R76895
theorem R51695 : Reach 51695 := rs (se 1 (by rfl) ⟨38771, by rfl⟩) R77543
theorem R84635 : Reach 84635 := rs (se 1 (by rfl) ⟨63476, by rfl⟩) R126953
theorem R51977 : Reach 51977 := rs (se 2 (by rfl) ⟨19491, by rfl⟩) R38983
theorem R51995 : Reach 51995 := rs (se 1 (by rfl) ⟨38996, by rfl⟩) R77993
theorem R84989 : Reach 84989 := rs (se 3 (by rfl) ⟨15935, by rfl⟩) R31871
theorem R52463 : Reach 52463 := rs (se 1 (by rfl) ⟨39347, by rfl⟩) R78695
theorem R52583 : Reach 52583 := rs (se 1 (by rfl) ⟨39437, by rfl⟩) R78875
theorem R1035767 : Reach 1035767 := rs (se 1 (by rfl) ⟨776825, by rfl⟩) R1553651
theorem R675373 : Reach 675373 := rs (se 3 (by rfl) ⟨126632, by rfl⟩) R253265
theorem R53129 : Reach 53129 := rs (se 2 (by rfl) ⟨19923, by rfl⟩) R39847
theorem R249911 : Reach 249911 := rs (se 1 (by rfl) ⟨187433, by rfl⟩) R374867
theorem R184619 : Reach 184619 := rs (se 1 (by rfl) ⟨138464, by rfl⟩) R276929
theorem R87227 : Reach 87227 := rs (se 1 (by rfl) ⟨65420, by rfl⟩) R130841
theorem R153083 : Reach 153083 := rs (se 1 (by rfl) ⟨114812, by rfl⟩) R229625
theorem R87551 : Reach 87551 := rs (se 1 (by rfl) ⟨65663, by rfl⟩) R131327
theorem R120943 : Reach 120943 := rs (se 1 (by rfl) ⟨90707, by rfl⟩) R181415
theorem R55849 : Reach 55849 := rs (se 2 (by rfl) ⟨20943, by rfl⟩) R41887
theorem R121439 : Reach 121439 := rs (se 1 (by rfl) ⟨91079, by rfl⟩) R182159
theorem R88705 : Reach 88705 := rs (se 2 (by rfl) ⟨33264, by rfl⟩) R66529
theorem R1137361 : Reach 1137361 := rs (se 2 (by rfl) ⟨426510, by rfl⟩) R853021
theorem R1105325 : Reach 1105325 := rs (se 3 (by rfl) ⟨207248, by rfl⟩) R414497
theorem R57179 : Reach 57179 := rs (se 1 (by rfl) ⟨42884, by rfl⟩) R85769
theorem R57287 : Reach 57287 := rs (se 1 (by rfl) ⟨42965, by rfl⟩) R85931
theorem R90209 : Reach 90209 := rs (se 2 (by rfl) ⟨33828, by rfl⟩) R67657
theorem R58529 : Reach 58529 := rs (se 2 (by rfl) ⟨21948, by rfl⟩) R43897
theorem R387031 : Reach 387031 := rs (se 1 (by rfl) ⟨290273, by rfl⟩) R580547
theorem R551123 : Reach 551123 := rs (se 1 (by rfl) ⟨413342, by rfl⟩) R826685
theorem R59611 : Reach 59611 := rs (se 1 (by rfl) ⟨44708, by rfl⟩) R89417
theorem R9038141 : Reach 9038141 := rs (se 3 (by rfl) ⟨1694651, by rfl⟩) R3389303
theorem R223793 : Reach 223793 := rs (se 2 (by rfl) ⟨83922, by rfl⟩) R167845
theorem R257053 : Reach 257053 := rs (se 3 (by rfl) ⟨48197, by rfl⟩) R96395
theorem R61087 : Reach 61087 := rs (se 1 (by rfl) ⟨45815, by rfl⟩) R91631
theorem R96319 : Reach 96319 := rs (se 1 (by rfl) ⟨72239, by rfl⟩) R144479
theorem R31131 : Reach 31131 := rs (se 1 (by rfl) ⟨23348, by rfl⟩) R46697
theorem R31279 : Reach 31279 := rs (se 1 (by rfl) ⟨23459, by rfl⟩) R46919
theorem R31439 : Reach 31439 := rs (se 1 (by rfl) ⟨23579, by rfl⟩) R47159
theorem R31487 : Reach 31487 := rs (se 1 (by rfl) ⟨23615, by rfl⟩) R47231
theorem R32047 : Reach 32047 := rs (se 1 (by rfl) ⟨24035, by rfl⟩) R48071
theorem R32639 : Reach 32639 := rs (se 1 (by rfl) ⟨24479, by rfl⟩) R48959
theorem R32839 : Reach 32839 := rs (se 1 (by rfl) ⟨24629, by rfl⟩) R49259
theorem R32871 : Reach 32871 := rs (se 1 (by rfl) ⟨24653, by rfl⟩) R49307
theorem R65711 : Reach 65711 := rs (se 1 (by rfl) ⟨49283, by rfl⟩) R98567
theorem R262439 : Reach 262439 := rs (se 1 (by rfl) ⟨196829, by rfl⟩) R393659
theorem R33127 : Reach 33127 := rs (se 1 (by rfl) ⟨24845, by rfl⟩) R49691
theorem R164267 : Reach 164267 := rs (se 1 (by rfl) ⟨123200, by rfl⟩) R246401
theorem R33247 : Reach 33247 := rs (se 1 (by rfl) ⟨24935, by rfl⟩) R49871
theorem R33563 : Reach 33563 := rs (se 1 (by rfl) ⟨25172, by rfl⟩) R50345
theorem R33659 : Reach 33659 := rs (se 1 (by rfl) ⟨25244, by rfl⟩) R50489
theorem R852929 : Reach 852929 := rs (se 2 (by rfl) ⟨319848, by rfl⟩) R639697
theorem R33759 : Reach 33759 := rs (se 1 (by rfl) ⟨25319, by rfl⟩) R50639
theorem R34023 : Reach 34023 := rs (se 1 (by rfl) ⟨25517, by rfl⟩) R51035
theorem R99625 : Reach 99625 := rs (se 2 (by rfl) ⟨37359, by rfl⟩) R74719
theorem R34175 : Reach 34175 := rs (se 1 (by rfl) ⟨25631, by rfl⟩) R51263
theorem R67199 : Reach 67199 := rs (se 1 (by rfl) ⟨50399, by rfl⟩) R100799
theorem R34463 : Reach 34463 := rs (se 1 (by rfl) ⟨25847, by rfl⟩) R51695
theorem R67319 : Reach 67319 := rs (se 1 (by rfl) ⟨50489, by rfl⟩) R100979
theorem R34651 : Reach 34651 := rs (se 1 (by rfl) ⟨25988, by rfl⟩) R51977
theorem R34663 : Reach 34663 := rs (se 1 (by rfl) ⟨25997, by rfl⟩) R51995
theorem R34975 : Reach 34975 := rs (se 1 (by rfl) ⟨26231, by rfl⟩) R52463
theorem R35055 : Reach 35055 := rs (se 1 (by rfl) ⟨26291, by rfl⟩) R52583
theorem R35419 : Reach 35419 := rs (se 1 (by rfl) ⟨26564, by rfl⟩) R53129
theorem R166607 : Reach 166607 := rs (se 1 (by rfl) ⟨124955, by rfl⟩) R249911
theorem R4197095 : Reach 4197095 := rs (se 1 (by rfl) ⟨3147821, by rfl⟩) R6295643
theorem R134399 : Reach 134399 := rs (se 1 (by rfl) ⟨100799, by rfl⟩) R201599
theorem R495233 : Reach 495233 := rs (se 2 (by rfl) ⟨185712, by rfl⟩) R371425
theorem R102055 : Reach 102055 := rs (se 1 (by rfl) ⟨76541, by rfl⟩) R153083
theorem R38119 : Reach 38119 := rs (se 1 (by rfl) ⟨28589, by rfl⟩) R57179
theorem R70939 : Reach 70939 := rs (se 1 (by rfl) ⟨53204, by rfl⟩) R106409
theorem R38191 : Reach 38191 := rs (se 1 (by rfl) ⟨28643, by rfl⟩) R57287
theorem R39019 : Reach 39019 := rs (se 1 (by rfl) ⟨29264, by rfl⟩) R58529
theorem R661841 : Reach 661841 := rs (se 2 (by rfl) ⟨248190, by rfl⟩) R496381
theorem R72287 : Reach 72287 := rs (se 1 (by rfl) ⟨54215, by rfl⟩) R108431
theorem R72431 : Reach 72431 := rs (se 1 (by rfl) ⟨54323, by rfl⟩) R108647
theorem R367415 : Reach 367415 := rs (se 1 (by rfl) ⟨275561, by rfl⟩) R551123
theorem R73043 : Reach 73043 := rs (se 1 (by rfl) ⟨54782, by rfl⟩) R109565
theorem R400889 : Reach 400889 := rs (se 2 (by rfl) ⟨150333, by rfl⟩) R300667
theorem R73871 : Reach 73871 := rs (se 1 (by rfl) ⟨55403, by rfl⟩) R110807
theorem R368873 : Reach 368873 := rs (se 2 (by rfl) ⟨138327, by rfl⟩) R276655
theorem R74465 : Reach 74465 := rs (se 2 (by rfl) ⟨27924, by rfl⟩) R55849
theorem R1516481 : Reach 1516481 := rs (se 2 (by rfl) ⟨568680, by rfl⟩) R1137361
theorem R74735 : Reach 74735 := rs (se 1 (by rfl) ⟨56051, by rfl⟩) R112103
theorem R74843 : Reach 74843 := rs (se 1 (by rfl) ⟨56132, by rfl⟩) R112265
theorem R2762045 : Reach 2762045 := rs (se 3 (by rfl) ⟨517883, by rfl⟩) R1035767
theorem R76571 : Reach 76571 := rs (se 1 (by rfl) ⟨57428, by rfl⟩) R114857
theorem R4402151 : Reach 4402151 := rs (se 1 (by rfl) ⟨3301613, by rfl⟩) R6603227
theorem R142361 : Reach 142361 := rs (se 2 (by rfl) ⟨53385, by rfl⟩) R106771
theorem R536057 : Reach 536057 := rs (se 2 (by rfl) ⟨201021, by rfl⟩) R402043
theorem R176255 : Reach 176255 := rs (se 1 (by rfl) ⟨132191, by rfl⟩) R264383
theorem R110969 : Reach 110969 := rs (se 2 (by rfl) ⟨41613, by rfl⟩) R83227
theorem R373157 : Reach 373157 := rs (se 4 (by rfl) ⟨34983, by rfl⟩) R69967
theorem R111743 : Reach 111743 := rs (se 1 (by rfl) ⟨83807, by rfl⟩) R167615
theorem R79481 : Reach 79481 := rs (se 2 (by rfl) ⟨29805, by rfl⟩) R59611
theorem R47711 : Reach 47711 := rs (se 1 (by rfl) ⟨35783, by rfl⟩) R71567
theorem R342737 : Reach 342737 := rs (se 2 (by rfl) ⟨128526, by rfl⟩) R257053
theorem R47993 : Reach 47993 := rs (se 2 (by rfl) ⟨17997, by rfl⟩) R35995
theorem R80959 : Reach 80959 := rs (se 1 (by rfl) ⟨60719, by rfl⟩) R121439
theorem R48239 : Reach 48239 := rs (se 1 (by rfl) ⟨36179, by rfl⟩) R72359
theorem R900497 : Reach 900497 := rs (se 2 (by rfl) ⟨337686, by rfl⟩) R675373
theorem R81449 : Reach 81449 := rs (se 2 (by rfl) ⟨30543, by rfl⟩) R61087
theorem R736883 : Reach 736883 := rs (se 1 (by rfl) ⟨552662, by rfl⟩) R1105325
theorem R49193 : Reach 49193 := rs (se 2 (by rfl) ⟨18447, by rfl⟩) R36895
theorem R1490987 : Reach 1490987 := rs (se 1 (by rfl) ⟨1118240, by rfl⟩) R2236481
theorem R49391 : Reach 49391 := rs (se 1 (by rfl) ⟨37043, by rfl⟩) R74087
theorem R50159 : Reach 50159 := rs (se 1 (by rfl) ⟨37619, by rfl⟩) R75239
theorem R50441 : Reach 50441 := rs (se 2 (by rfl) ⟨18915, by rfl⟩) R37831
theorem R50591 : Reach 50591 := rs (se 1 (by rfl) ⟨37943, by rfl⟩) R75887
theorem R181885 : Reach 181885 := rs (se 3 (by rfl) ⟨34103, by rfl⟩) R68207
theorem R149195 : Reach 149195 := rs (se 1 (by rfl) ⟨111896, by rfl⟩) R223793
theorem R1984601 : Reach 1984601 := rs (se 2 (by rfl) ⟨744225, by rfl⟩) R1488451
theorem R51311 : Reach 51311 := rs (se 1 (by rfl) ⟨38483, by rfl⟩) R76967
theorem R51593 : Reach 51593 := rs (se 2 (by rfl) ⟨19347, by rfl⟩) R38695
theorem R52091 : Reach 52091 := rs (se 1 (by rfl) ⟨39068, by rfl⟩) R78137
theorem R248939 : Reach 248939 := rs (se 1 (by rfl) ⟨186704, by rfl⟩) R373409
theorem R118273 : Reach 118273 := rs (se 2 (by rfl) ⟨44352, by rfl⟩) R88705
theorem R1299077 : Reach 1299077 := rs (se 4 (by rfl) ⟨121788, by rfl⟩) R243577
theorem R185075 : Reach 185075 := rs (se 1 (by rfl) ⟨138806, by rfl⟩) R277613
theorem R709955 : Reach 709955 := rs (se 1 (by rfl) ⟨532466, by rfl⟩) R1064933
theorem R120143 : Reach 120143 := rs (se 1 (by rfl) ⟨90107, by rfl⟩) R180215
theorem R645029 : Reach 645029 := rs (se 4 (by rfl) ⟨60471, by rfl⟩) R120943
theorem R285403 : Reach 285403 := rs (se 1 (by rfl) ⟨214052, by rfl⟩) R428105
theorem R416623 : Reach 416623 := rs (se 1 (by rfl) ⟨312467, by rfl⟩) R624935
theorem R56423 : Reach 56423 := rs (se 1 (by rfl) ⟨42317, by rfl⟩) R84635
theorem R56659 : Reach 56659 := rs (se 1 (by rfl) ⟨42494, by rfl⟩) R84989
theorem R516041 : Reach 516041 := rs (se 2 (by rfl) ⟨193515, by rfl⟩) R387031
theorem R123079 : Reach 123079 := rs (se 1 (by rfl) ⟨92309, by rfl⟩) R184619
theorem R58151 : Reach 58151 := rs (se 1 (by rfl) ⟨43613, by rfl⟩) R87227
theorem R58367 : Reach 58367 := rs (se 1 (by rfl) ⟨43775, by rfl⟩) R87551
theorem R58745 : Reach 58745 := rs (se 2 (by rfl) ⟨22029, by rfl⟩) R44059
theorem R60139 : Reach 60139 := rs (se 1 (by rfl) ⟨45104, by rfl⟩) R90209
theorem R60257 : Reach 60257 := rs (se 2 (by rfl) ⟨22596, by rfl⟩) R45193
theorem R6025427 : Reach 6025427 := rs (se 1 (by rfl) ⟨4519070, by rfl⟩) R9038141
theorem R422975 : Reach 422975 := rs (se 1 (by rfl) ⟨317231, by rfl⟩) R634463
theorem R62633 : Reach 62633 := rs (se 2 (by rfl) ⟨23487, by rfl⟩) R46975
theorem R128425 : Reach 128425 := rs (se 2 (by rfl) ⟨48159, by rfl⟩) R96319
theorem R161999 : Reach 161999 := rs (se 1 (by rfl) ⟨121499, by rfl⟩) R242999
theorem R31387 : Reach 31387 := rs (se 1 (by rfl) ⟨23540, by rfl⟩) R47081
theorem R31515 : Reach 31515 := rs (se 1 (by rfl) ⟨23636, by rfl⟩) R47273
theorem R31679 : Reach 31679 := rs (se 1 (by rfl) ⟨23759, by rfl⟩) R47519
theorem R32287 : Reach 32287 := rs (se 1 (by rfl) ⟨24215, by rfl⟩) R48431
theorem R32359 : Reach 32359 := rs (se 1 (by rfl) ⟨24269, by rfl⟩) R48539
theorem R32507 : Reach 32507 := rs (se 1 (by rfl) ⟨24380, by rfl⟩) R48761
theorem R32795 : Reach 32795 := rs (se 1 (by rfl) ⟨24596, by rfl⟩) R49193
theorem R32927 : Reach 32927 := rs (se 1 (by rfl) ⟨24695, by rfl⟩) R49391
theorem R164105 : Reach 164105 := rs (se 2 (by rfl) ⟨61539, by rfl⟩) R123079
theorem R33439 : Reach 33439 := rs (se 1 (by rfl) ⟨25079, by rfl⟩) R50159
theorem R33627 : Reach 33627 := rs (se 1 (by rfl) ⟨25220, by rfl⟩) R50441
theorem R33727 : Reach 33727 := rs (se 1 (by rfl) ⟨25295, by rfl⟩) R50591
theorem R99463 : Reach 99463 := rs (se 1 (by rfl) ⟨74597, by rfl⟩) R149195
theorem R34207 : Reach 34207 := rs (se 1 (by rfl) ⟨25655, by rfl⟩) R51311
theorem R34395 : Reach 34395 := rs (se 1 (by rfl) ⟨25796, by rfl⟩) R51593
theorem R132833 : Reach 132833 := rs (se 2 (by rfl) ⟨49812, by rfl⟩) R99625
theorem R34727 : Reach 34727 := rs (se 1 (by rfl) ⟨26045, by rfl⟩) R52091
theorem R165959 : Reach 165959 := rs (se 1 (by rfl) ⟨124469, by rfl⟩) R248939
theorem R330155 : Reach 330155 := rs (se 1 (by rfl) ⟨247616, by rfl⟩) R495233
theorem R167021 : Reach 167021 := rs (se 3 (by rfl) ⟨31316, by rfl⟩) R62633
theorem R430019 : Reach 430019 := rs (se 1 (by rfl) ⟨322514, by rfl⟩) R645029
theorem R37615 : Reach 37615 := rs (se 1 (by rfl) ⟨28211, by rfl⟩) R56423
theorem R136073 : Reach 136073 := rs (se 2 (by rfl) ⟨51027, by rfl⟩) R102055
theorem R267259 : Reach 267259 := rs (se 1 (by rfl) ⟨200444, by rfl⟩) R400889
theorem R38767 : Reach 38767 := rs (se 1 (by rfl) ⟨29075, by rfl⟩) R58151
theorem R38911 : Reach 38911 := rs (se 1 (by rfl) ⟨29183, by rfl⟩) R58367
theorem R1841363 : Reach 1841363 := rs (se 1 (by rfl) ⟨1381022, by rfl⟩) R2762045
theorem R39163 : Reach 39163 := rs (se 1 (by rfl) ⟨29372, by rfl⟩) R58745
theorem R171233 : Reach 171233 := rs (se 2 (by rfl) ⟨64212, by rfl⟩) R128425
theorem R40171 : Reach 40171 := rs (se 1 (by rfl) ⟨30128, by rfl⟩) R60257
theorem R73979 : Reach 73979 := rs (se 1 (by rfl) ⟨55484, by rfl⟩) R110969
theorem R74495 : Reach 74495 := rs (se 1 (by rfl) ⟨55871, by rfl⟩) R111743
theorem R107945 : Reach 107945 := rs (se 2 (by rfl) ⟨40479, by rfl⟩) R80959
theorem R107999 : Reach 107999 := rs (se 1 (by rfl) ⟨80999, by rfl⟩) R161999
theorem R75545 : Reach 75545 := rs (se 2 (by rfl) ⟨28329, by rfl⟩) R56659
theorem R600331 : Reach 600331 := rs (se 1 (by rfl) ⟨450248, by rfl⟩) R900497
theorem R3975965 : Reach 3975965 := rs (se 3 (by rfl) ⟨745493, by rfl⟩) R1490987
theorem R43807 : Reach 43807 := rs (se 1 (by rfl) ⟨32855, by rfl⟩) R65711
theorem R174959 : Reach 174959 := rs (se 1 (by rfl) ⟨131219, by rfl⟩) R262439
theorem R109511 : Reach 109511 := rs (se 1 (by rfl) ⟨82133, by rfl⟩) R164267
theorem R568619 : Reach 568619 := rs (se 1 (by rfl) ⟨426464, by rfl⟩) R852929
theorem R44879 : Reach 44879 := rs (se 1 (by rfl) ⟨33659, by rfl⟩) R67319
theorem R1323067 : Reach 1323067 := rs (se 1 (by rfl) ⟨992300, by rfl⟩) R1984601
theorem R111071 : Reach 111071 := rs (se 1 (by rfl) ⟨83303, by rfl⟩) R166607
theorem R2798063 : Reach 2798063 := rs (se 1 (by rfl) ⟨2098547, by rfl⟩) R4197095
theorem R242513 : Reach 242513 := rs (se 2 (by rfl) ⟨90942, by rfl⟩) R181885
theorem R866051 : Reach 866051 := rs (se 1 (by rfl) ⟨649538, by rfl⟩) R1299077
theorem R47225 : Reach 47225 := rs (se 2 (by rfl) ⟨17709, by rfl⟩) R35419
theorem R473303 : Reach 473303 := rs (se 1 (by rfl) ⟨354977, by rfl⟩) R709955
theorem R80185 : Reach 80185 := rs (se 2 (by rfl) ⟨30069, by rfl⟩) R60139
theorem R441227 : Reach 441227 := rs (se 1 (by rfl) ⟨330920, by rfl⟩) R661841
theorem R48191 : Reach 48191 := rs (se 1 (by rfl) ⟨36143, by rfl⟩) R72287
theorem R48287 : Reach 48287 := rs (se 1 (by rfl) ⟨36215, by rfl⟩) R72431
theorem R244943 : Reach 244943 := rs (se 1 (by rfl) ⟨183707, by rfl⟩) R367415
theorem R48695 : Reach 48695 := rs (se 1 (by rfl) ⟨36521, by rfl⟩) R73043
theorem R344027 : Reach 344027 := rs (se 1 (by rfl) ⟨258020, by rfl⟩) R516041
theorem R49247 : Reach 49247 := rs (se 1 (by rfl) ⟨36935, by rfl⟩) R73871
theorem R245915 : Reach 245915 := rs (se 1 (by rfl) ⟨184436, by rfl⟩) R368873
theorem R49643 : Reach 49643 := rs (se 1 (by rfl) ⟨37232, by rfl⟩) R74465
theorem R49823 : Reach 49823 := rs (se 1 (by rfl) ⟨37367, by rfl⟩) R74735
theorem R49895 : Reach 49895 := rs (se 1 (by rfl) ⟨37421, by rfl⟩) R74843
theorem R378341 : Reach 378341 := rs (se 4 (by rfl) ⟨35469, by rfl⟩) R70939
theorem R50825 : Reach 50825 := rs (se 2 (by rfl) ⟨19059, by rfl⟩) R38119
theorem R50921 : Reach 50921 := rs (se 2 (by rfl) ⟨19095, by rfl⟩) R38191
theorem R51047 : Reach 51047 := rs (se 1 (by rfl) ⟨38285, by rfl⟩) R76571
theorem R2934767 : Reach 2934767 := rs (se 1 (by rfl) ⟨2201075, by rfl⟩) R4402151
theorem R117503 : Reach 117503 := rs (se 1 (by rfl) ⟨88127, by rfl⟩) R176255
theorem R4016951 : Reach 4016951 := rs (se 1 (by rfl) ⟨3012713, by rfl⟩) R6025427
theorem R52025 : Reach 52025 := rs (se 2 (by rfl) ⟨19509, by rfl⟩) R39019
theorem R248771 : Reach 248771 := rs (se 1 (by rfl) ⟨186578, by rfl⟩) R373157
theorem R281983 : Reach 281983 := rs (se 1 (by rfl) ⟨211487, by rfl⟩) R422975
theorem R380537 : Reach 380537 := rs (se 2 (by rfl) ⟨142701, by rfl⟩) R285403
theorem R52987 : Reach 52987 := rs (se 1 (by rfl) ⟨39740, by rfl⟩) R79481
theorem R54299 : Reach 54299 := rs (se 1 (by rfl) ⟨40724, by rfl⟩) R81449
theorem R186533 : Reach 186533 := rs (se 4 (by rfl) ⟨17487, by rfl⟩) R34975
theorem R89599 : Reach 89599 := rs (se 1 (by rfl) ⟨67199, by rfl⟩) R134399
theorem R123383 : Reach 123383 := rs (se 1 (by rfl) ⟨92537, by rfl⟩) R185075
theorem R320381 : Reach 320381 := rs (se 3 (by rfl) ⟨60071, by rfl⟩) R120143
theorem R157697 : Reach 157697 := rs (se 2 (by rfl) ⟨59136, by rfl⟩) R118273
theorem R1010987 : Reach 1010987 := rs (se 1 (by rfl) ⟨758240, by rfl⟩) R1516481
theorem R716789 : Reach 716789 := rs (se 5 (by rfl) ⟨33599, by rfl⟩) R67199
theorem R94907 : Reach 94907 := rs (se 1 (by rfl) ⟨71180, by rfl⟩) R142361
theorem R357371 : Reach 357371 := rs (se 1 (by rfl) ⟨268028, by rfl⟩) R536057
theorem R555497 : Reach 555497 := rs (se 2 (by rfl) ⟨208311, by rfl⟩) R416623
theorem R31807 : Reach 31807 := rs (se 1 (by rfl) ⟨23855, by rfl⟩) R47711
theorem R228491 : Reach 228491 := rs (se 1 (by rfl) ⟨171368, by rfl⟩) R342737
theorem R31995 : Reach 31995 := rs (se 1 (by rfl) ⟨23996, by rfl⟩) R47993
theorem R32159 : Reach 32159 := rs (se 1 (by rfl) ⟨24119, by rfl⟩) R48239
theorem R491255 : Reach 491255 := rs (se 1 (by rfl) ⟨368441, by rfl⟩) R736883
theorem R32831 : Reach 32831 := rs (se 1 (by rfl) ⟨24623, by rfl⟩) R49247
theorem R163943 : Reach 163943 := rs (se 1 (by rfl) ⟨122957, by rfl⟩) R245915
theorem R33095 : Reach 33095 := rs (se 1 (by rfl) ⟨24821, by rfl⟩) R49643
theorem R33215 : Reach 33215 := rs (se 1 (by rfl) ⟨24911, by rfl⟩) R49823
theorem R33263 : Reach 33263 := rs (se 1 (by rfl) ⟨24947, by rfl⟩) R49895
theorem R33883 : Reach 33883 := rs (se 1 (by rfl) ⟨25412, by rfl⟩) R50825
theorem R33947 : Reach 33947 := rs (se 1 (by rfl) ⟨25460, by rfl⟩) R50921
theorem R34031 : Reach 34031 := rs (se 1 (by rfl) ⟨25523, by rfl⟩) R51047
theorem R132617 : Reach 132617 := rs (se 2 (by rfl) ⟨49731, by rfl⟩) R99463
theorem R34683 : Reach 34683 := rs (se 1 (by rfl) ⟨26012, by rfl⟩) R52025
theorem R165847 : Reach 165847 := rs (se 1 (by rfl) ⟨124385, by rfl⟩) R248771
theorem R70649 : Reach 70649 := rs (se 2 (by rfl) ⟨26493, by rfl⟩) R52987
theorem R71963 : Reach 71963 := rs (se 1 (by rfl) ⟨53972, by rfl⟩) R107945
theorem R71999 : Reach 71999 := rs (se 1 (by rfl) ⟨53999, by rfl⟩) R107999
theorem R105131 : Reach 105131 := rs (se 1 (by rfl) ⟨78848, by rfl⟩) R157697
theorem R73007 : Reach 73007 := rs (se 1 (by rfl) ⟨54755, by rfl⟩) R109511
theorem R74047 : Reach 74047 := rs (se 1 (by rfl) ⟨55535, by rfl⟩) R111071
theorem R106913 : Reach 106913 := rs (se 2 (by rfl) ⟨40092, by rfl⟩) R80185
theorem R238247 : Reach 238247 := rs (se 1 (by rfl) ⟨178685, by rfl⟩) R357371
theorem R370331 : Reach 370331 := rs (se 1 (by rfl) ⟨277748, by rfl⟩) R555497
theorem R1911437 : Reach 1911437 := rs (se 3 (by rfl) ⟨358394, by rfl⟩) R716789
theorem R109403 : Reach 109403 := rs (se 1 (by rfl) ⟨82052, by rfl⟩) R164105
theorem R110639 : Reach 110639 := rs (se 1 (by rfl) ⟨82979, by rfl⟩) R165959
theorem R78335 : Reach 78335 := rs (se 1 (by rfl) ⟨58751, by rfl⟩) R117503
theorem R111347 : Reach 111347 := rs (se 1 (by rfl) ⟨83510, by rfl⟩) R167021
theorem R144797 : Reach 144797 := rs (se 3 (by rfl) ⟨27149, by rfl⟩) R54299
theorem R800441 : Reach 800441 := rs (se 2 (by rfl) ⟨300165, by rfl⟩) R600331
theorem R1227575 : Reach 1227575 := rs (se 1 (by rfl) ⟨920681, by rfl⟩) R1841363
theorem R375977 : Reach 375977 := rs (se 2 (by rfl) ⟨140991, by rfl⟩) R281983
theorem R114155 : Reach 114155 := rs (se 1 (by rfl) ⟨85616, by rfl⟩) R171233
theorem R49319 : Reach 49319 := rs (se 1 (by rfl) ⟨36989, by rfl⟩) R73979
theorem R82255 : Reach 82255 := rs (se 1 (by rfl) ⟨61691, by rfl⟩) R123383
theorem R49663 : Reach 49663 := rs (se 1 (by rfl) ⟨37247, by rfl⟩) R74495
theorem R1262141 : Reach 1262141 := rs (se 3 (by rfl) ⟨236651, by rfl⟩) R473303
theorem R213587 : Reach 213587 := rs (se 1 (by rfl) ⟨160190, by rfl⟩) R320381
theorem R50153 : Reach 50153 := rs (se 2 (by rfl) ⟨18807, by rfl⟩) R37615
theorem R50363 : Reach 50363 := rs (se 1 (by rfl) ⟨37772, by rfl⟩) R75545
theorem R116639 : Reach 116639 := rs (se 1 (by rfl) ⟨87479, by rfl⟩) R174959
theorem R673991 : Reach 673991 := rs (se 1 (by rfl) ⟨505493, by rfl⟩) R1010987
theorem R379079 : Reach 379079 := rs (se 1 (by rfl) ⟨284309, by rfl⟩) R568619
theorem R51689 : Reach 51689 := rs (se 2 (by rfl) ⟨19383, by rfl⟩) R38767
theorem R51881 : Reach 51881 := rs (se 2 (by rfl) ⟨19455, by rfl⟩) R38911
theorem R52217 : Reach 52217 := rs (se 2 (by rfl) ⟨19581, by rfl⟩) R39163
theorem R577367 : Reach 577367 := rs (se 1 (by rfl) ⟨433025, by rfl⟩) R866051
theorem R53561 : Reach 53561 := rs (se 2 (by rfl) ⟨20085, by rfl⟩) R40171
theorem R119465 : Reach 119465 := rs (se 2 (by rfl) ⟨44799, by rfl⟩) R89599
theorem R152327 : Reach 152327 := rs (se 1 (by rfl) ⟨114245, by rfl⟩) R228491
theorem R119677 : Reach 119677 := rs (se 3 (by rfl) ⟨22439, by rfl⟩) R44879
theorem R252227 : Reach 252227 := rs (se 1 (by rfl) ⟨189170, by rfl⟩) R378341
theorem R88555 : Reach 88555 := rs (se 1 (by rfl) ⟨66416, by rfl⟩) R132833
theorem R1956511 : Reach 1956511 := rs (se 1 (by rfl) ⟨1467383, by rfl⟩) R2934767
theorem R220103 : Reach 220103 := rs (se 1 (by rfl) ⟨165077, by rfl⟩) R330155
theorem R2677967 : Reach 2677967 := rs (se 1 (by rfl) ⟨2008475, by rfl⟩) R4016951
theorem R253691 : Reach 253691 := rs (se 1 (by rfl) ⟨190268, by rfl⟩) R380537
theorem R286679 : Reach 286679 := rs (se 1 (by rfl) ⟨215009, by rfl⟩) R430019
theorem R90715 : Reach 90715 := rs (se 1 (by rfl) ⟨68036, by rfl⟩) R136073
theorem R58409 : Reach 58409 := rs (se 2 (by rfl) ⟨21903, by rfl⟩) R43807
theorem R124355 : Reach 124355 := rs (se 1 (by rfl) ⟨93266, by rfl⟩) R186533
theorem R1764089 : Reach 1764089 := rs (se 2 (by rfl) ⟨661533, by rfl⟩) R1323067
theorem R356345 : Reach 356345 := rs (se 2 (by rfl) ⟨133629, by rfl⟩) R267259
theorem R2650643 : Reach 2650643 := rs (se 1 (by rfl) ⟨1987982, by rfl⟩) R3975965
theorem R1865375 : Reach 1865375 := rs (se 1 (by rfl) ⟨1399031, by rfl⟩) R2798063
theorem R63271 : Reach 63271 := rs (se 1 (by rfl) ⟨47453, by rfl⟩) R94907
theorem R161675 : Reach 161675 := rs (se 1 (by rfl) ⟨121256, by rfl⟩) R242513
theorem R31483 : Reach 31483 := rs (se 1 (by rfl) ⟨23612, by rfl⟩) R47225
theorem R294151 : Reach 294151 := rs (se 1 (by rfl) ⟨220613, by rfl⟩) R441227
theorem R32127 : Reach 32127 := rs (se 1 (by rfl) ⟨24095, by rfl⟩) R48191
theorem R32191 : Reach 32191 := rs (se 1 (by rfl) ⟨24143, by rfl⟩) R48287
theorem R163295 : Reach 163295 := rs (se 1 (by rfl) ⟨122471, by rfl⟩) R244943
theorem R32463 : Reach 32463 := rs (se 1 (by rfl) ⟨24347, by rfl⟩) R48695
theorem R327503 : Reach 327503 := rs (se 1 (by rfl) ⟨245627, by rfl⟩) R491255
theorem R229351 : Reach 229351 := rs (se 1 (by rfl) ⟨172013, by rfl⟩) R344027
theorem R32879 : Reach 32879 := rs (se 1 (by rfl) ⟨24659, by rfl⟩) R49319
theorem R98729 : Reach 98729 := rs (se 2 (by rfl) ⟨37023, by rfl⟩) R74047
theorem R33435 : Reach 33435 := rs (se 1 (by rfl) ⟨25076, by rfl⟩) R50153
theorem R33575 : Reach 33575 := rs (se 1 (by rfl) ⟨25181, by rfl⟩) R50363
theorem R34459 : Reach 34459 := rs (se 1 (by rfl) ⟨25844, by rfl⟩) R51689
theorem R34587 : Reach 34587 := rs (se 1 (by rfl) ⟨25940, by rfl⟩) R51881
theorem R34811 : Reach 34811 := rs (se 1 (by rfl) ⟨26108, by rfl⟩) R52217
theorem R133741 : Reach 133741 := rs (se 3 (by rfl) ⟨25076, by rfl⟩) R50153
theorem R264869 : Reach 264869 := rs (se 4 (by rfl) ⟨24831, by rfl⟩) R49663
theorem R35707 : Reach 35707 := rs (se 1 (by rfl) ⟨26780, by rfl⟩) R53561
theorem R1544501 : Reach 1544501 := rs (se 5 (by rfl) ⟨72398, by rfl⟩) R144797
theorem R70087 : Reach 70087 := rs (se 1 (by rfl) ⟨52565, by rfl⟩) R105131
theorem R169127 : Reach 169127 := rs (se 1 (by rfl) ⟨126845, by rfl⟩) R253691
theorem R71275 : Reach 71275 := rs (se 1 (by rfl) ⟨53456, by rfl⟩) R106913
theorem R38939 : Reach 38939 := rs (se 1 (by rfl) ⟨29204, by rfl⟩) R58409
theorem R72935 : Reach 72935 := rs (se 1 (by rfl) ⟨54701, by rfl⟩) R109403
theorem R237563 : Reach 237563 := rs (se 1 (by rfl) ⟨178172, by rfl⟩) R356345
theorem R73759 : Reach 73759 := rs (se 1 (by rfl) ⟨55319, by rfl⟩) R110639
theorem R74231 : Reach 74231 := rs (se 1 (by rfl) ⟨55673, by rfl⟩) R111347
theorem R533627 : Reach 533627 := rs (se 1 (by rfl) ⟨400220, by rfl⟩) R800441
theorem R107783 : Reach 107783 := rs (se 1 (by rfl) ⟨80837, by rfl⟩) R161675
theorem R108863 : Reach 108863 := rs (se 1 (by rfl) ⟨81647, by rfl⟩) R163295
theorem R76103 : Reach 76103 := rs (se 1 (by rfl) ⟨57077, by rfl⟩) R114155
theorem R305801 : Reach 305801 := rs (se 2 (by rfl) ⟨114675, by rfl⟩) R229351
theorem R109295 : Reach 109295 := rs (se 1 (by rfl) ⟨81971, by rfl⟩) R163943
theorem R142391 : Reach 142391 := rs (se 1 (by rfl) ⟨106793, by rfl⟩) R213587
theorem R109673 : Reach 109673 := rs (se 2 (by rfl) ⟨41127, by rfl⟩) R82255
theorem R77759 : Reach 77759 := rs (se 1 (by rfl) ⟨58319, by rfl⟩) R116639
theorem R406205 : Reach 406205 := rs (se 3 (by rfl) ⟨76163, by rfl⟩) R152327
theorem R79643 : Reach 79643 := rs (se 1 (by rfl) ⟨59732, by rfl⟩) R119465
theorem R47099 : Reach 47099 := rs (se 1 (by rfl) ⟨35324, by rfl⟩) R70649
theorem R47975 : Reach 47975 := rs (se 1 (by rfl) ⟨35981, by rfl⟩) R71963
theorem R47999 : Reach 47999 := rs (se 1 (by rfl) ⟨35999, by rfl⟩) R71999
theorem R146735 : Reach 146735 := rs (se 1 (by rfl) ⟨110051, by rfl⟩) R220103
theorem R1785311 : Reach 1785311 := rs (se 1 (by rfl) ⟨1338983, by rfl⟩) R2677967
theorem R48671 : Reach 48671 := rs (se 1 (by rfl) ⟨36503, by rfl⟩) R73007
theorem R672605 : Reach 672605 := rs (se 3 (by rfl) ⟨126113, by rfl⟩) R252227
theorem R82903 : Reach 82903 := rs (se 1 (by rfl) ⟨62177, by rfl⟩) R124355
theorem R246887 : Reach 246887 := rs (se 1 (by rfl) ⟨185165, by rfl⟩) R370331
theorem R84361 : Reach 84361 := rs (se 2 (by rfl) ⟨31635, by rfl⟩) R63271
theorem R52223 : Reach 52223 := rs (se 1 (by rfl) ⟨39167, by rfl⟩) R78335
theorem R118073 : Reach 118073 := rs (se 2 (by rfl) ⟨44277, by rfl⟩) R88555
theorem R2608681 : Reach 2608681 := rs (se 2 (by rfl) ⟨978255, by rfl⟩) R1956511
theorem R250651 : Reach 250651 := rs (se 1 (by rfl) ⟨187988, by rfl⟩) R375977
theorem R218335 : Reach 218335 := rs (se 1 (by rfl) ⟨163751, by rfl⟩) R327503
theorem R841427 : Reach 841427 := rs (se 1 (by rfl) ⟨631070, by rfl⟩) R1262141
theorem R120953 : Reach 120953 := rs (se 2 (by rfl) ⟨45357, by rfl⟩) R90715
theorem R88411 : Reach 88411 := rs (se 1 (by rfl) ⟨66308, by rfl⟩) R132617
theorem R88573 : Reach 88573 := rs (se 3 (by rfl) ⟨16607, by rfl⟩) R33215
theorem R252719 : Reach 252719 := rs (se 1 (by rfl) ⟨189539, by rfl⟩) R379079
theorem R449327 : Reach 449327 := rs (se 1 (by rfl) ⟨336995, by rfl⟩) R673991
theorem R384911 : Reach 384911 := rs (se 1 (by rfl) ⟨288683, by rfl⟩) R577367
theorem R221129 : Reach 221129 := rs (se 2 (by rfl) ⟨82923, by rfl⟩) R165847
theorem R191119 : Reach 191119 := rs (se 1 (by rfl) ⟨143339, by rfl⟩) R286679
theorem R158831 : Reach 158831 := rs (se 1 (by rfl) ⟨119123, by rfl⟩) R238247
theorem R159569 : Reach 159569 := rs (se 2 (by rfl) ⟨59838, by rfl⟩) R119677
theorem R1274291 : Reach 1274291 := rs (se 1 (by rfl) ⟨955718, by rfl⟩) R1911437
theorem R1176059 : Reach 1176059 := rs (se 1 (by rfl) ⟨882044, by rfl⟩) R1764089
theorem R1767095 : Reach 1767095 := rs (se 1 (by rfl) ⟨1325321, by rfl⟩) R2650643
theorem R1243583 : Reach 1243583 := rs (se 1 (by rfl) ⟨932687, by rfl⟩) R1865375
theorem R392201 : Reach 392201 := rs (se 2 (by rfl) ⟨147075, by rfl⟩) R294151
theorem R818383 : Reach 818383 := rs (se 1 (by rfl) ⟨613787, by rfl⟩) R1227575
theorem R98345 : Reach 98345 := rs (se 2 (by rfl) ⟨36879, by rfl⟩) R73759
theorem R65819 : Reach 65819 := rs (se 1 (by rfl) ⟨49364, by rfl⟩) R98729
theorem R164591 : Reach 164591 := rs (se 1 (by rfl) ⟨123443, by rfl⟩) R246887
theorem R34815 : Reach 34815 := rs (se 1 (by rfl) ⟨26111, by rfl⟩) R52223
theorem R560951 : Reach 560951 := rs (se 1 (by rfl) ⟨420713, by rfl⟩) R841427
theorem R299551 : Reach 299551 := rs (se 1 (by rfl) ⟨224663, by rfl⟩) R449327
theorem R168479 : Reach 168479 := rs (se 1 (by rfl) ⟨126359, by rfl⟩) R252719
theorem R3478241 : Reach 3478241 := rs (se 2 (by rfl) ⟨1304340, by rfl⟩) R2608681
theorem R103837 : Reach 103837 := rs (se 3 (by rfl) ⟨19469, by rfl⟩) R38939
theorem R71855 : Reach 71855 := rs (se 1 (by rfl) ⟨53891, by rfl⟩) R107783
theorem R334201 : Reach 334201 := rs (se 2 (by rfl) ⟨125325, by rfl⟩) R250651
theorem R72575 : Reach 72575 := rs (se 1 (by rfl) ⟨54431, by rfl⟩) R108863
theorem R203867 : Reach 203867 := rs (se 1 (by rfl) ⟨152900, by rfl⟩) R305801
theorem R72863 : Reach 72863 := rs (se 1 (by rfl) ⟨54647, by rfl⟩) R109295
theorem R73115 : Reach 73115 := rs (se 1 (by rfl) ⟨54836, by rfl⟩) R109673
theorem R105887 : Reach 105887 := rs (se 1 (by rfl) ⟨79415, by rfl⟩) R158831
theorem R106379 : Reach 106379 := rs (se 1 (by rfl) ⟨79784, by rfl⟩) R159569
theorem R270803 : Reach 270803 := rs (se 1 (by rfl) ⟨203102, by rfl⟩) R406205
theorem R1091177 : Reach 1091177 := rs (se 2 (by rfl) ⟨409191, by rfl⟩) R818383
theorem R829055 : Reach 829055 := rs (se 1 (by rfl) ⟨621791, by rfl⟩) R1243583
theorem R1190207 : Reach 1190207 := rs (se 1 (by rfl) ⟨892655, by rfl⟩) R1785311
theorem R110537 : Reach 110537 := rs (se 2 (by rfl) ⟨41451, by rfl⟩) R82903
theorem R176579 : Reach 176579 := rs (se 1 (by rfl) ⟨132434, by rfl⟩) R264869
theorem R78715 : Reach 78715 := rs (se 1 (by rfl) ⟨59036, by rfl⟩) R118073
theorem R1029667 : Reach 1029667 := rs (se 1 (by rfl) ⟨772250, by rfl⟩) R1544501
theorem R112481 : Reach 112481 := rs (se 2 (by rfl) ⟨42180, by rfl⟩) R84361
theorem R112751 : Reach 112751 := rs (se 1 (by rfl) ⟨84563, by rfl⟩) R169127
theorem R178321 : Reach 178321 := rs (se 2 (by rfl) ⟨66870, by rfl⟩) R133741
theorem R47609 : Reach 47609 := rs (se 2 (by rfl) ⟨17853, by rfl⟩) R35707
theorem R80635 : Reach 80635 := rs (se 1 (by rfl) ⟨60476, by rfl⟩) R120953
theorem R48623 : Reach 48623 := rs (se 1 (by rfl) ⟨36467, by rfl⟩) R72935
theorem R147419 : Reach 147419 := rs (se 1 (by rfl) ⟨110564, by rfl⟩) R221129
theorem R49487 : Reach 49487 := rs (se 1 (by rfl) ⟨37115, by rfl⟩) R74231
theorem R50735 : Reach 50735 := rs (se 1 (by rfl) ⟨38051, by rfl⟩) R76103
theorem R51839 : Reach 51839 := rs (se 1 (by rfl) ⟨38879, by rfl⟩) R77759
theorem R117881 : Reach 117881 := rs (se 2 (by rfl) ⟨44205, by rfl⟩) R88411
theorem R118097 : Reach 118097 := rs (se 2 (by rfl) ⟨44286, by rfl⟩) R88573
theorem R53095 : Reach 53095 := rs (se 1 (by rfl) ⟨39821, by rfl⟩) R79643
theorem R254825 : Reach 254825 := rs (se 2 (by rfl) ⟨95559, by rfl⟩) R191119
theorem R256607 : Reach 256607 := rs (se 1 (by rfl) ⟨192455, by rfl⟩) R384911
theorem R158375 : Reach 158375 := rs (se 1 (by rfl) ⟨118781, by rfl⟩) R237563
theorem R93449 : Reach 93449 := rs (se 2 (by rfl) ⟨35043, by rfl⟩) R70087
theorem R355751 : Reach 355751 := rs (se 1 (by rfl) ⟨266813, by rfl⟩) R533627
theorem R291113 : Reach 291113 := rs (se 2 (by rfl) ⟨109167, by rfl⟩) R218335
theorem R94927 : Reach 94927 := rs (se 1 (by rfl) ⟨71195, by rfl⟩) R142391
theorem R95033 : Reach 95033 := rs (se 2 (by rfl) ⟨35637, by rfl⟩) R71275
theorem R849527 : Reach 849527 := rs (se 1 (by rfl) ⟨637145, by rfl⟩) R1274291
theorem R784039 : Reach 784039 := rs (se 1 (by rfl) ⟨588029, by rfl⟩) R1176059
theorem R7174453 : Reach 7174453 := rs (se 5 (by rfl) ⟨336302, by rfl⟩) R672605
theorem R1178063 : Reach 1178063 := rs (se 1 (by rfl) ⟨883547, by rfl⟩) R1767095
theorem R31399 : Reach 31399 := rs (se 1 (by rfl) ⟨23549, by rfl⟩) R47099
theorem R31983 : Reach 31983 := rs (se 1 (by rfl) ⟨23987, by rfl⟩) R47975
theorem R31999 : Reach 31999 := rs (se 1 (by rfl) ⟨23999, by rfl⟩) R47999
theorem R261467 : Reach 261467 := rs (se 1 (by rfl) ⟨196100, by rfl⟩) R392201
theorem R97823 : Reach 97823 := rs (se 1 (by rfl) ⟨73367, by rfl⟩) R146735
theorem R32447 : Reach 32447 := rs (se 1 (by rfl) ⟨24335, by rfl⟩) R48671
theorem R262253 : Reach 262253 := rs (se 3 (by rfl) ⟨49172, by rfl⟩) R98345
theorem R32991 : Reach 32991 := rs (se 1 (by rfl) ⟨24743, by rfl⟩) R49487
theorem R33823 : Reach 33823 := rs (se 1 (by rfl) ⟨25367, by rfl⟩) R50735
theorem R34559 : Reach 34559 := rs (se 1 (by rfl) ⟨25919, by rfl⟩) R51839
theorem R9275309 : Reach 9275309 := rs (se 3 (by rfl) ⟨1739120, by rfl⟩) R3478241
theorem R135911 : Reach 135911 := rs (se 1 (by rfl) ⟨101933, by rfl⟩) R203867
theorem R70793 : Reach 70793 := rs (se 2 (by rfl) ⟨26547, by rfl⟩) R53095
theorem R70919 : Reach 70919 := rs (se 1 (by rfl) ⟨53189, by rfl⟩) R106379
theorem R169883 : Reach 169883 := rs (se 1 (by rfl) ⟨127412, by rfl⟩) R254825
theorem R399401 : Reach 399401 := rs (se 2 (by rfl) ⟨149775, by rfl⟩) R299551
theorem R727451 : Reach 727451 := rs (se 1 (by rfl) ⟨545588, by rfl⟩) R1091177
theorem R793471 : Reach 793471 := rs (se 1 (by rfl) ⟨595103, by rfl⟩) R1190207
theorem R171071 : Reach 171071 := rs (se 1 (by rfl) ⟨128303, by rfl⟩) R256607
theorem R138449 : Reach 138449 := rs (se 2 (by rfl) ⟨51918, by rfl⟩) R103837
theorem R237167 : Reach 237167 := rs (se 1 (by rfl) ⟨177875, by rfl⟩) R355751
theorem R73691 : Reach 73691 := rs (se 1 (by rfl) ⟨55268, by rfl⟩) R110537
theorem R237761 : Reach 237761 := rs (se 2 (by rfl) ⟨89160, by rfl⟩) R178321
theorem R107513 : Reach 107513 := rs (se 2 (by rfl) ⟨40317, by rfl⟩) R80635
theorem R566351 : Reach 566351 := rs (se 1 (by rfl) ⟨424763, by rfl⟩) R849527
theorem R74987 : Reach 74987 := rs (se 1 (by rfl) ⟨56240, by rfl⟩) R112481
theorem R75167 : Reach 75167 := rs (se 1 (by rfl) ⟨56375, by rfl⟩) R112751
theorem R174311 : Reach 174311 := rs (se 1 (by rfl) ⟨130733, by rfl⟩) R261467
theorem R109727 : Reach 109727 := rs (se 1 (by rfl) ⟨82295, by rfl⟩) R164591
theorem R175517 : Reach 175517 := rs (se 3 (by rfl) ⟨32909, by rfl⟩) R65819
theorem R78587 : Reach 78587 := rs (se 1 (by rfl) ⟨58940, by rfl⟩) R117881
theorem R78731 : Reach 78731 := rs (se 1 (by rfl) ⟨59048, by rfl⟩) R118097
theorem R373967 : Reach 373967 := rs (se 1 (by rfl) ⟨280475, by rfl⟩) R560951
theorem R112319 : Reach 112319 := rs (se 1 (by rfl) ⟨84239, by rfl⟩) R168479
theorem R47903 : Reach 47903 := rs (se 1 (by rfl) ⟨35927, by rfl⟩) R71855
theorem R48383 : Reach 48383 := rs (se 1 (by rfl) ⟨36287, by rfl⟩) R72575
theorem R48575 : Reach 48575 := rs (se 1 (by rfl) ⟨36431, by rfl⟩) R72863
theorem R48743 : Reach 48743 := rs (se 1 (by rfl) ⟨36557, by rfl⟩) R73115
theorem R180535 : Reach 180535 := rs (se 1 (by rfl) ⟨135401, by rfl⟩) R270803
theorem R117719 : Reach 117719 := rs (se 1 (by rfl) ⟨88289, by rfl⟩) R176579
theorem R445601 : Reach 445601 := rs (se 2 (by rfl) ⟨167100, by rfl⟩) R334201
theorem R282365 : Reach 282365 := rs (se 3 (by rfl) ⟨52943, by rfl⟩) R105887
theorem R419813 : Reach 419813 := rs (se 4 (by rfl) ⟨39357, by rfl⟩) R78715
theorem R126569 : Reach 126569 := rs (se 2 (by rfl) ⟨47463, by rfl⟩) R94927
theorem R552703 : Reach 552703 := rs (se 1 (by rfl) ⟨414527, by rfl⟩) R829055
theorem R422333 : Reach 422333 := rs (se 3 (by rfl) ⟨79187, by rfl⟩) R158375
theorem R1372889 : Reach 1372889 := rs (se 2 (by rfl) ⟨514833, by rfl⟩) R1029667
theorem R62299 : Reach 62299 := rs (se 1 (by rfl) ⟨46724, by rfl⟩) R93449
theorem R1045385 : Reach 1045385 := rs (se 2 (by rfl) ⟨392019, by rfl⟩) R784039
theorem R194075 : Reach 194075 := rs (se 1 (by rfl) ⟨145556, by rfl⟩) R291113
theorem R9565937 : Reach 9565937 := rs (se 2 (by rfl) ⟨3587226, by rfl⟩) R7174453
theorem R63355 : Reach 63355 := rs (se 1 (by rfl) ⟨47516, by rfl⟩) R95033
theorem R785375 : Reach 785375 := rs (se 1 (by rfl) ⟨589031, by rfl⟩) R1178063
theorem R31739 : Reach 31739 := rs (se 1 (by rfl) ⟨23804, by rfl⟩) R47609
theorem R32415 : Reach 32415 := rs (se 1 (by rfl) ⟨24311, by rfl⟩) R48623
theorem R65215 : Reach 65215 := rs (se 1 (by rfl) ⟨48911, by rfl⟩) R97823
theorem R98279 : Reach 98279 := rs (se 1 (by rfl) ⟨73709, by rfl⟩) R147419
theorem R297067 : Reach 297067 := rs (se 1 (by rfl) ⟨222800, by rfl⟩) R445601
theorem R266267 : Reach 266267 := rs (se 1 (by rfl) ⟨199700, by rfl⟩) R399401
theorem R71675 : Reach 71675 := rs (se 1 (by rfl) ⟨53756, by rfl⟩) R107513
theorem R73151 : Reach 73151 := rs (se 1 (by rfl) ⟨54863, by rfl⟩) R109727
theorem R696923 : Reach 696923 := rs (se 1 (by rfl) ⟨522692, by rfl⟩) R1045385
theorem R74879 : Reach 74879 := rs (se 1 (by rfl) ⟨56159, by rfl⟩) R112319
theorem R1057961 : Reach 1057961 := rs (se 2 (by rfl) ⟨396735, by rfl⟩) R793471
theorem R337517 : Reach 337517 := rs (se 3 (by rfl) ⟨63284, by rfl⟩) R126569
theorem R174835 : Reach 174835 := rs (se 1 (by rfl) ⟨131126, by rfl⟩) R262253
theorem R240713 : Reach 240713 := rs (se 2 (by rfl) ⟨90267, by rfl⟩) R180535
theorem R78479 : Reach 78479 := rs (se 1 (by rfl) ⟨58859, by rfl⟩) R117719
theorem R47195 : Reach 47195 := rs (se 1 (by rfl) ⟨35396, by rfl⟩) R70793
theorem R47279 : Reach 47279 := rs (se 1 (by rfl) ⟨35459, by rfl⟩) R70919
theorem R113255 : Reach 113255 := rs (se 1 (by rfl) ⟨84941, by rfl⟩) R169883
theorem R114047 : Reach 114047 := rs (se 1 (by rfl) ⟨85535, by rfl⟩) R171071
theorem R736937 : Reach 736937 := rs (se 2 (by rfl) ⟨276351, by rfl⟩) R552703
theorem R49127 : Reach 49127 := rs (se 1 (by rfl) ⟨36845, by rfl⟩) R73691
theorem R377567 : Reach 377567 := rs (se 1 (by rfl) ⟨283175, by rfl⟩) R566351
theorem R49991 : Reach 49991 := rs (se 1 (by rfl) ⟨37493, by rfl⟩) R74987
theorem R50111 : Reach 50111 := rs (se 1 (by rfl) ⟨37583, by rfl⟩) R75167
theorem R83065 : Reach 83065 := rs (se 2 (by rfl) ⟨31149, by rfl⟩) R62299
theorem R279875 : Reach 279875 := rs (se 1 (by rfl) ⟨209906, by rfl⟩) R419813
theorem R116207 : Reach 116207 := rs (se 1 (by rfl) ⟨87155, by rfl⟩) R174311
theorem R117011 : Reach 117011 := rs (se 1 (by rfl) ⟨87758, by rfl⟩) R175517
theorem R84473 : Reach 84473 := rs (se 2 (by rfl) ⟨31677, by rfl⟩) R63355
theorem R281555 : Reach 281555 := rs (se 1 (by rfl) ⟨211166, by rfl⟩) R422333
theorem R52391 : Reach 52391 := rs (se 1 (by rfl) ⟨39293, by rfl⟩) R78587
theorem R52487 : Reach 52487 := rs (se 1 (by rfl) ⟨39365, by rfl⟩) R78731
theorem R249311 : Reach 249311 := rs (se 1 (by rfl) ⟨186983, by rfl⟩) R373967
theorem R6377291 : Reach 6377291 := rs (se 1 (by rfl) ⟨4782968, by rfl⟩) R9565937
theorem R86953 : Reach 86953 := rs (se 2 (by rfl) ⟨32607, by rfl⟩) R65215
theorem R6183539 : Reach 6183539 := rs (se 1 (by rfl) ⟨4637654, by rfl⟩) R9275309
theorem R188243 : Reach 188243 := rs (se 1 (by rfl) ⟨141182, by rfl⟩) R282365
theorem R90607 : Reach 90607 := rs (se 1 (by rfl) ⟨67955, by rfl⟩) R135911
theorem R484967 : Reach 484967 := rs (se 1 (by rfl) ⟨363725, by rfl⟩) R727451
theorem R92299 : Reach 92299 := rs (se 1 (by rfl) ⟨69224, by rfl⟩) R138449
theorem R158111 : Reach 158111 := rs (se 1 (by rfl) ⟨118583, by rfl⟩) R237167
theorem R158507 : Reach 158507 := rs (se 1 (by rfl) ⟨118880, by rfl⟩) R237761
theorem R915259 : Reach 915259 := rs (se 1 (by rfl) ⟨686444, by rfl⟩) R1372889
theorem R129383 : Reach 129383 := rs (se 1 (by rfl) ⟨97037, by rfl⟩) R194075
theorem R31935 : Reach 31935 := rs (se 1 (by rfl) ⟨23951, by rfl⟩) R47903
theorem R523583 : Reach 523583 := rs (se 1 (by rfl) ⟨392687, by rfl⟩) R785375
theorem R32255 : Reach 32255 := rs (se 1 (by rfl) ⟨24191, by rfl⟩) R48383
theorem R32383 : Reach 32383 := rs (se 1 (by rfl) ⟨24287, by rfl⟩) R48575
theorem R32495 : Reach 32495 := rs (se 1 (by rfl) ⟨24371, by rfl⟩) R48743
theorem R65519 : Reach 65519 := rs (se 1 (by rfl) ⟨49139, by rfl⟩) R98279
theorem R33327 : Reach 33327 := rs (se 1 (by rfl) ⟨24995, by rfl⟩) R49991
theorem R33407 : Reach 33407 := rs (se 1 (by rfl) ⟨25055, by rfl⟩) R50111
theorem R34927 : Reach 34927 := rs (se 1 (by rfl) ⟨26195, by rfl⟩) R52391
theorem R34991 : Reach 34991 := rs (se 1 (by rfl) ⟨26243, by rfl⟩) R52487
theorem R166207 : Reach 166207 := rs (se 1 (by rfl) ⟨124655, by rfl⟩) R249311
theorem R396089 : Reach 396089 := rs (se 2 (by rfl) ⟨148533, by rfl⟩) R297067
theorem R233113 : Reach 233113 := rs (se 2 (by rfl) ⟨87417, by rfl⟩) R174835
theorem R464615 : Reach 464615 := rs (se 1 (by rfl) ⟨348461, by rfl⟩) R696923
theorem R105407 : Reach 105407 := rs (se 1 (by rfl) ⟨79055, by rfl⟩) R158111
theorem R105671 : Reach 105671 := rs (se 1 (by rfl) ⟨79253, by rfl⟩) R158507
theorem R1220345 : Reach 1220345 := rs (se 2 (by rfl) ⟨457629, by rfl⟩) R915259
theorem R75503 : Reach 75503 := rs (se 1 (by rfl) ⟨56627, by rfl⟩) R113255
theorem R76031 : Reach 76031 := rs (se 1 (by rfl) ⟨57023, by rfl⟩) R114047
theorem R43679 : Reach 43679 := rs (se 1 (by rfl) ⟨32759, by rfl⟩) R65519
theorem R77471 : Reach 77471 := rs (se 1 (by rfl) ⟨58103, by rfl⟩) R116207
theorem R110753 : Reach 110753 := rs (se 2 (by rfl) ⟨41532, by rfl⟩) R83065
theorem R78007 : Reach 78007 := rs (se 1 (by rfl) ⟨58505, by rfl⟩) R117011
theorem R177511 : Reach 177511 := rs (se 1 (by rfl) ⟨133133, by rfl⟩) R266267
theorem R47783 : Reach 47783 := rs (se 1 (by rfl) ⟨35837, by rfl⟩) R71675
theorem R48767 : Reach 48767 := rs (se 1 (by rfl) ⟨36575, by rfl⟩) R73151
theorem R49919 : Reach 49919 := rs (se 1 (by rfl) ⟨37439, by rfl⟩) R74879
theorem R705307 : Reach 705307 := rs (se 1 (by rfl) ⟨528980, by rfl⟩) R1057961
theorem R115937 : Reach 115937 := rs (se 2 (by rfl) ⟨43476, by rfl⟩) R86953
theorem R52319 : Reach 52319 := rs (se 1 (by rfl) ⟨39239, by rfl⟩) R78479
theorem R86255 : Reach 86255 := rs (se 1 (by rfl) ⟨64691, by rfl⟩) R129383
theorem R349055 : Reach 349055 := rs (se 1 (by rfl) ⟨261791, by rfl⟩) R523583
theorem R251711 : Reach 251711 := rs (se 1 (by rfl) ⟨188783, by rfl⟩) R377567
theorem R120809 : Reach 120809 := rs (se 2 (by rfl) ⟨45303, by rfl⟩) R90607
theorem R186583 : Reach 186583 := rs (se 1 (by rfl) ⟨139937, by rfl⟩) R279875
theorem R56315 : Reach 56315 := rs (se 1 (by rfl) ⟨42236, by rfl⟩) R84473
theorem R187703 : Reach 187703 := rs (se 1 (by rfl) ⟨140777, by rfl⟩) R281555
theorem R4251527 : Reach 4251527 := rs (se 1 (by rfl) ⟨3188645, by rfl⟩) R6377291
theorem R123065 : Reach 123065 := rs (se 2 (by rfl) ⟨46149, by rfl⟩) R92299
theorem R4122359 : Reach 4122359 := rs (se 1 (by rfl) ⟨3091769, by rfl⟩) R6183539
theorem R125495 : Reach 125495 := rs (se 1 (by rfl) ⟨94121, by rfl⟩) R188243
theorem R323311 : Reach 323311 := rs (se 1 (by rfl) ⟨242483, by rfl⟩) R484967
theorem R225011 : Reach 225011 := rs (se 1 (by rfl) ⟨168758, by rfl⟩) R337517
theorem R160475 : Reach 160475 := rs (se 1 (by rfl) ⟨120356, by rfl⟩) R240713
theorem R31463 : Reach 31463 := rs (se 1 (by rfl) ⟨23597, by rfl⟩) R47195
theorem R31519 : Reach 31519 := rs (se 1 (by rfl) ⟨23639, by rfl⟩) R47279
theorem R491291 : Reach 491291 := rs (se 1 (by rfl) ⟨368468, by rfl⟩) R736937
theorem R32751 : Reach 32751 := rs (se 1 (by rfl) ⟨24563, by rfl⟩) R49127
theorem R33279 : Reach 33279 := rs (se 1 (by rfl) ⟨24959, by rfl⟩) R49919
theorem R264059 : Reach 264059 := rs (se 1 (by rfl) ⟨198044, by rfl⟩) R396089
theorem R427933 : Reach 427933 := rs (se 3 (by rfl) ⟨80237, by rfl⟩) R160475
theorem R34879 : Reach 34879 := rs (se 1 (by rfl) ⟨26159, by rfl⟩) R52319
theorem R232703 : Reach 232703 := rs (se 1 (by rfl) ⟨174527, by rfl⟩) R349055
theorem R167807 : Reach 167807 := rs (se 1 (by rfl) ⟨125855, by rfl⟩) R251711
theorem R201341 : Reach 201341 := rs (se 3 (by rfl) ⟨37751, by rfl⟩) R75503
theorem R70271 : Reach 70271 := rs (se 1 (by rfl) ⟨52703, by rfl⟩) R105407
theorem R37543 : Reach 37543 := rs (se 1 (by rfl) ⟨28157, by rfl⟩) R56315
theorem R431081 : Reach 431081 := rs (se 2 (by rfl) ⟨161655, by rfl⟩) R323311
theorem R104009 : Reach 104009 := rs (se 2 (by rfl) ⟨39003, by rfl⟩) R78007
theorem R236681 : Reach 236681 := rs (se 2 (by rfl) ⟨88755, by rfl⟩) R177511
theorem R73835 : Reach 73835 := rs (se 1 (by rfl) ⟨55376, by rfl⟩) R110753
theorem R77291 : Reach 77291 := rs (se 1 (by rfl) ⟨57968, by rfl⟩) R115937
theorem R309743 : Reach 309743 := rs (se 1 (by rfl) ⟨232307, by rfl⟩) R464615
theorem R310817 : Reach 310817 := rs (se 2 (by rfl) ⟨116556, by rfl⟩) R233113
theorem R2834351 : Reach 2834351 := rs (se 1 (by rfl) ⟨2125763, by rfl⟩) R4251527
theorem R82043 : Reach 82043 := rs (se 1 (by rfl) ⟨61532, by rfl⟩) R123065
theorem R50687 : Reach 50687 := rs (se 1 (by rfl) ⟨38015, by rfl⟩) R76031
theorem R83663 : Reach 83663 := rs (se 1 (by rfl) ⟨62747, by rfl⟩) R125495
theorem R116477 : Reach 116477 := rs (se 3 (by rfl) ⟨21839, by rfl⟩) R43679
theorem R51647 : Reach 51647 := rs (se 1 (by rfl) ⟨38735, by rfl⟩) R77471
theorem R150007 : Reach 150007 := rs (se 1 (by rfl) ⟨112505, by rfl⟩) R225011
theorem R248777 : Reach 248777 := rs (se 2 (by rfl) ⟨93291, by rfl⟩) R186583
theorem R281789 : Reach 281789 := rs (se 3 (by rfl) ⟨52835, by rfl⟩) R105671
theorem R940409 : Reach 940409 := rs (se 2 (by rfl) ⟨352653, by rfl⟩) R705307
theorem R57503 : Reach 57503 := rs (se 1 (by rfl) ⟨43127, by rfl⟩) R86255
theorem R221609 : Reach 221609 := rs (se 2 (by rfl) ⟨83103, by rfl⟩) R166207
theorem R125135 : Reach 125135 := rs (se 1 (by rfl) ⟨93851, by rfl⟩) R187703
theorem R813563 : Reach 813563 := rs (se 1 (by rfl) ⟨610172, by rfl⟩) R1220345
theorem R322157 : Reach 322157 := rs (se 3 (by rfl) ⟨60404, by rfl⟩) R120809
theorem R2748239 : Reach 2748239 := rs (se 1 (by rfl) ⟨2061179, by rfl⟩) R4122359
theorem R31855 : Reach 31855 := rs (se 1 (by rfl) ⟨23891, by rfl⟩) R47783
theorem R32511 : Reach 32511 := rs (se 1 (by rfl) ⟨24383, by rfl⟩) R48767
theorem R327527 : Reach 327527 := rs (se 1 (by rfl) ⟨245645, by rfl⟩) R491291
theorem R33791 : Reach 33791 := rs (se 1 (by rfl) ⟨25343, by rfl⟩) R50687
theorem R34431 : Reach 34431 := rs (se 1 (by rfl) ⟨25823, by rfl⟩) R51647
theorem R165851 : Reach 165851 := rs (se 1 (by rfl) ⟨124388, by rfl⟩) R248777
theorem R134227 : Reach 134227 := rs (se 1 (by rfl) ⟨100670, by rfl⟩) R201341
theorem R200009 : Reach 200009 := rs (se 2 (by rfl) ⟨75003, by rfl⟩) R150007
theorem R626939 : Reach 626939 := rs (se 1 (by rfl) ⟨470204, by rfl⟩) R940409
theorem R38335 : Reach 38335 := rs (se 1 (by rfl) ⟨28751, by rfl⟩) R57503
theorem R206495 : Reach 206495 := rs (se 1 (by rfl) ⟨154871, by rfl⟩) R309743
theorem R207211 : Reach 207211 := rs (se 1 (by rfl) ⟨155408, by rfl⟩) R310817
theorem R77651 : Reach 77651 := rs (se 1 (by rfl) ⟨58238, by rfl⟩) R116477
theorem R176039 : Reach 176039 := rs (se 1 (by rfl) ⟨132029, by rfl⟩) R264059
theorem R570577 : Reach 570577 := rs (se 2 (by rfl) ⟨213966, by rfl⟩) R427933
theorem R111871 : Reach 111871 := rs (se 1 (by rfl) ⟨83903, by rfl⟩) R167807
theorem R46847 : Reach 46847 := rs (se 1 (by rfl) ⟨35135, by rfl⟩) R70271
theorem R277357 : Reach 277357 := rs (se 3 (by rfl) ⟨52004, by rfl⟩) R104009
theorem R49223 : Reach 49223 := rs (se 1 (by rfl) ⟨36917, by rfl⟩) R73835
theorem R147739 : Reach 147739 := rs (se 1 (by rfl) ⟨110804, by rfl⟩) R221609
theorem R50057 : Reach 50057 := rs (se 2 (by rfl) ⟨18771, by rfl⟩) R37543
theorem R83423 : Reach 83423 := rs (se 1 (by rfl) ⟨62567, by rfl⟩) R125135
theorem R542375 : Reach 542375 := rs (se 1 (by rfl) ⟨406781, by rfl⟩) R813563
theorem R214771 : Reach 214771 := rs (se 1 (by rfl) ⟨161078, by rfl⟩) R322157
theorem R51527 : Reach 51527 := rs (se 1 (by rfl) ⟨38645, by rfl⟩) R77291
theorem R218351 : Reach 218351 := rs (se 1 (by rfl) ⟨163763, by rfl⟩) R327527
theorem R1889567 : Reach 1889567 := rs (se 1 (by rfl) ⟨1417175, by rfl⟩) R2834351
theorem R54695 : Reach 54695 := rs (se 1 (by rfl) ⟨41021, by rfl⟩) R82043
theorem R55775 : Reach 55775 := rs (se 1 (by rfl) ⟨41831, by rfl⟩) R83663
theorem R187859 : Reach 187859 := rs (se 1 (by rfl) ⟨140894, by rfl⟩) R281789
theorem R155135 : Reach 155135 := rs (se 1 (by rfl) ⟨116351, by rfl⟩) R232703
theorem R287387 : Reach 287387 := rs (se 1 (by rfl) ⟨215540, by rfl⟩) R431081
theorem R157787 : Reach 157787 := rs (se 1 (by rfl) ⟨118340, by rfl⟩) R236681
theorem R1832159 : Reach 1832159 := rs (se 1 (by rfl) ⟨1374119, by rfl⟩) R2748239
theorem R32815 : Reach 32815 := rs (se 1 (by rfl) ⟨24611, by rfl⟩) R49223
theorem R196985 : Reach 196985 := rs (se 2 (by rfl) ⟨73869, by rfl⟩) R147739
theorem R33371 : Reach 33371 := rs (se 1 (by rfl) ⟨25028, by rfl⟩) R50057
theorem R361583 : Reach 361583 := rs (se 1 (by rfl) ⟨271187, by rfl⟩) R542375
theorem R34351 : Reach 34351 := rs (se 1 (by rfl) ⟨25763, by rfl⟩) R51527
theorem R133339 : Reach 133339 := rs (se 1 (by rfl) ⟨100004, by rfl⟩) R200009
theorem R36463 : Reach 36463 := rs (se 1 (by rfl) ⟨27347, by rfl⟩) R54695
theorem R37183 : Reach 37183 := rs (se 1 (by rfl) ⟨27887, by rfl⟩) R55775
theorem R103423 : Reach 103423 := rs (se 1 (by rfl) ⟨77567, by rfl⟩) R155135
theorem R137663 : Reach 137663 := rs (se 1 (by rfl) ⟨103247, by rfl⟩) R206495
theorem R105191 : Reach 105191 := rs (se 1 (by rfl) ⟨78893, by rfl⟩) R157787
theorem R760769 : Reach 760769 := rs (se 2 (by rfl) ⟨285288, by rfl⟩) R570577
theorem R1221439 : Reach 1221439 := rs (se 1 (by rfl) ⟨916079, by rfl⟩) R1832159
theorem R369809 : Reach 369809 := rs (se 2 (by rfl) ⟨138678, by rfl⟩) R277357
theorem R110567 : Reach 110567 := rs (se 1 (by rfl) ⟨82925, by rfl⟩) R165851
theorem R276281 : Reach 276281 := rs (se 2 (by rfl) ⟨103605, by rfl⟩) R207211
theorem R145567 : Reach 145567 := rs (se 1 (by rfl) ⟨109175, by rfl⟩) R218351
theorem R1259711 : Reach 1259711 := rs (se 1 (by rfl) ⟨944783, by rfl⟩) R1889567
theorem R178969 : Reach 178969 := rs (se 2 (by rfl) ⟨67113, by rfl⟩) R134227
theorem R149161 : Reach 149161 := rs (se 2 (by rfl) ⟨55935, by rfl⟩) R111871
theorem R51113 : Reach 51113 := rs (se 2 (by rfl) ⟨19167, by rfl⟩) R38335
theorem R51767 : Reach 51767 := rs (se 1 (by rfl) ⟨38825, by rfl⟩) R77651
theorem R117359 : Reach 117359 := rs (se 1 (by rfl) ⟨88019, by rfl⟩) R176039
theorem R55615 : Reach 55615 := rs (se 1 (by rfl) ⟨41711, by rfl⟩) R83423
theorem R286361 : Reach 286361 := rs (se 2 (by rfl) ⟨107385, by rfl⟩) R214771
theorem R417959 : Reach 417959 := rs (se 1 (by rfl) ⟨313469, by rfl⟩) R626939
theorem R125239 : Reach 125239 := rs (se 1 (by rfl) ⟨93929, by rfl⟩) R187859
theorem R191591 : Reach 191591 := rs (se 1 (by rfl) ⟨143693, by rfl⟩) R287387
theorem R31231 : Reach 31231 := rs (se 1 (by rfl) ⟨23423, by rfl⟩) R46847
theorem R131323 : Reach 131323 := rs (se 1 (by rfl) ⟨98492, by rfl⟩) R196985
theorem R34075 : Reach 34075 := rs (se 1 (by rfl) ⟨25556, by rfl⟩) R51113
theorem R34511 : Reach 34511 := rs (se 1 (by rfl) ⟨25883, by rfl⟩) R51767
theorem R198881 : Reach 198881 := rs (se 2 (by rfl) ⟨74580, by rfl⟩) R149161
theorem R166985 : Reach 166985 := rs (se 2 (by rfl) ⟨62619, by rfl⟩) R125239
theorem R70127 : Reach 70127 := rs (se 1 (by rfl) ⟨52595, by rfl⟩) R105191
theorem R137897 : Reach 137897 := rs (se 2 (by rfl) ⟨51711, by rfl⟩) R103423
theorem R73711 : Reach 73711 := rs (se 1 (by rfl) ⟨55283, by rfl⟩) R110567
theorem R74153 : Reach 74153 := rs (se 2 (by rfl) ⟨27807, by rfl⟩) R55615
theorem R238625 : Reach 238625 := rs (se 2 (by rfl) ⟨89484, by rfl⟩) R178969
theorem R241055 : Reach 241055 := rs (se 1 (by rfl) ⟨180791, by rfl⟩) R361583
theorem R78239 : Reach 78239 := rs (se 1 (by rfl) ⟨58679, by rfl⟩) R117359
theorem R177785 : Reach 177785 := rs (se 2 (by rfl) ⟨66669, by rfl⟩) R133339
theorem R507179 : Reach 507179 := rs (se 1 (by rfl) ⟨380384, by rfl⟩) R760769
theorem R48617 : Reach 48617 := rs (se 2 (by rfl) ⟨18231, by rfl⟩) R36463
theorem R278639 : Reach 278639 := rs (se 1 (by rfl) ⟨208979, by rfl⟩) R417959
theorem R49577 : Reach 49577 := rs (se 2 (by rfl) ⟨18591, by rfl⟩) R37183
theorem R246539 : Reach 246539 := rs (se 1 (by rfl) ⟨184904, by rfl⟩) R369809
theorem R184187 : Reach 184187 := rs (se 1 (by rfl) ⟨138140, by rfl⟩) R276281
theorem R839807 : Reach 839807 := rs (se 1 (by rfl) ⟨629855, by rfl⟩) R1259711
theorem R1628585 : Reach 1628585 := rs (se 2 (by rfl) ⟨610719, by rfl⟩) R1221439
theorem R91775 : Reach 91775 := rs (se 1 (by rfl) ⟨68831, by rfl⟩) R137663
theorem R190907 : Reach 190907 := rs (se 1 (by rfl) ⟨143180, by rfl⟩) R286361
theorem R127727 : Reach 127727 := rs (se 1 (by rfl) ⟨95795, by rfl⟩) R191591
theorem R194089 : Reach 194089 := rs (se 2 (by rfl) ⟨72783, by rfl⟩) R145567
theorem R33051 : Reach 33051 := rs (se 1 (by rfl) ⟨24788, by rfl⟩) R49577
theorem R164359 : Reach 164359 := rs (se 1 (by rfl) ⟨123269, by rfl⟩) R246539
theorem R197741 : Reach 197741 := rs (se 3 (by rfl) ⟨37076, by rfl⟩) R74153
theorem R132587 : Reach 132587 := rs (se 1 (by rfl) ⟨99440, by rfl⟩) R198881
theorem R559871 : Reach 559871 := rs (se 1 (by rfl) ⟨419903, by rfl⟩) R839807
theorem R1085723 : Reach 1085723 := rs (se 1 (by rfl) ⟨814292, by rfl⟩) R1628585
theorem R1352477 : Reach 1352477 := rs (se 3 (by rfl) ⟨253589, by rfl⟩) R507179
theorem R175097 : Reach 175097 := rs (se 2 (by rfl) ⟨65661, by rfl⟩) R131323
theorem R111323 : Reach 111323 := rs (se 1 (by rfl) ⟨83492, by rfl⟩) R166985
theorem R46751 : Reach 46751 := rs (se 1 (by rfl) ⟨35063, by rfl⟩) R70127
theorem R52159 : Reach 52159 := rs (se 1 (by rfl) ⟨39119, by rfl⟩) R78239
theorem R85151 : Reach 85151 := rs (se 1 (by rfl) ⟨63863, by rfl⟩) R127727
theorem R118523 : Reach 118523 := rs (se 1 (by rfl) ⟨88892, by rfl⟩) R177785
theorem R185759 : Reach 185759 := rs (se 1 (by rfl) ⟨139319, by rfl⟩) R278639
theorem R122791 : Reach 122791 := rs (se 1 (by rfl) ⟨92093, by rfl⟩) R184187
theorem R91931 : Reach 91931 := rs (se 1 (by rfl) ⟨68948, by rfl⟩) R137897
theorem R159083 : Reach 159083 := rs (se 1 (by rfl) ⟨119312, by rfl⟩) R238625
theorem R61183 : Reach 61183 := rs (se 1 (by rfl) ⟨45887, by rfl⟩) R91775
theorem R127271 : Reach 127271 := rs (se 1 (by rfl) ⟨95453, by rfl⟩) R190907
theorem R258785 : Reach 258785 := rs (se 2 (by rfl) ⟨97044, by rfl⟩) R194089
theorem R160703 : Reach 160703 := rs (se 1 (by rfl) ⟨120527, by rfl⟩) R241055
theorem R32411 : Reach 32411 := rs (se 1 (by rfl) ⟨24308, by rfl⟩) R48617
theorem R98281 : Reach 98281 := rs (se 2 (by rfl) ⟨36855, by rfl⟩) R73711
theorem R131827 : Reach 131827 := rs (se 1 (by rfl) ⟨98870, by rfl⟩) R197741
theorem R3606605 : Reach 3606605 := rs (se 3 (by rfl) ⟨676238, by rfl⟩) R1352477
theorem R723815 : Reach 723815 := rs (se 1 (by rfl) ⟨542861, by rfl⟩) R1085723
theorem R69545 : Reach 69545 := rs (se 2 (by rfl) ⟨26079, by rfl⟩) R52159
theorem R106055 : Reach 106055 := rs (se 1 (by rfl) ⟨79541, by rfl⟩) R159083
theorem R74215 : Reach 74215 := rs (se 1 (by rfl) ⟨55661, by rfl⟩) R111323
theorem R172523 : Reach 172523 := rs (se 1 (by rfl) ⟨129392, by rfl⟩) R258785
theorem R107135 : Reach 107135 := rs (se 1 (by rfl) ⟨80351, by rfl⟩) R160703
theorem R373247 : Reach 373247 := rs (se 1 (by rfl) ⟨279935, by rfl⟩) R559871
theorem R79015 : Reach 79015 := rs (se 1 (by rfl) ⟨59261, by rfl⟩) R118523
theorem R245149 : Reach 245149 := rs (se 3 (by rfl) ⟨45965, by rfl⟩) R91931
theorem R81577 : Reach 81577 := rs (se 2 (by rfl) ⟨30591, by rfl⟩) R61183
theorem R116731 : Reach 116731 := rs (se 1 (by rfl) ⟨87548, by rfl⟩) R175097
theorem R84847 : Reach 84847 := rs (se 1 (by rfl) ⟨63635, by rfl⟩) R127271
theorem R219145 : Reach 219145 := rs (se 2 (by rfl) ⟨82179, by rfl⟩) R164359
theorem R88391 : Reach 88391 := rs (se 1 (by rfl) ⟨66293, by rfl⟩) R132587
theorem R56767 : Reach 56767 := rs (se 1 (by rfl) ⟨42575, by rfl⟩) R85151
theorem R123839 : Reach 123839 := rs (se 1 (by rfl) ⟨92879, by rfl⟩) R185759
theorem R31167 : Reach 31167 := rs (se 1 (by rfl) ⟨23375, by rfl⟩) R46751
theorem R163721 : Reach 163721 := rs (se 2 (by rfl) ⟨61395, by rfl⟩) R122791
theorem R131041 : Reach 131041 := rs (se 2 (by rfl) ⟨49140, by rfl⟩) R98281
theorem R395813 : Reach 395813 := rs (se 4 (by rfl) ⟨37107, by rfl⟩) R74215
theorem R70703 : Reach 70703 := rs (se 1 (by rfl) ⟨53027, by rfl⟩) R106055
theorem R71423 : Reach 71423 := rs (se 1 (by rfl) ⟨53567, by rfl⟩) R107135
theorem R105353 : Reach 105353 := rs (se 2 (by rfl) ⟨39507, by rfl⟩) R79015
theorem R435077 : Reach 435077 := rs (se 4 (by rfl) ⟨40788, by rfl⟩) R81577
theorem R75689 : Reach 75689 := rs (se 2 (by rfl) ⟨28383, by rfl⟩) R56767
theorem R109147 : Reach 109147 := rs (se 1 (by rfl) ⟨81860, by rfl⟩) R163721
theorem R174721 : Reach 174721 := rs (se 2 (by rfl) ⟨65520, by rfl⟩) R131041
theorem R175769 : Reach 175769 := rs (se 2 (by rfl) ⟨65913, by rfl⟩) R131827
theorem R2404403 : Reach 2404403 := rs (se 1 (by rfl) ⟨1803302, by rfl⟩) R3606605
theorem R46363 : Reach 46363 := rs (se 1 (by rfl) ⟨34772, by rfl⟩) R69545
theorem R113129 : Reach 113129 := rs (se 2 (by rfl) ⟨42423, by rfl⟩) R84847
theorem R115015 : Reach 115015 := rs (se 1 (by rfl) ⟨86261, by rfl⟩) R172523
theorem R82559 : Reach 82559 := rs (se 1 (by rfl) ⟨61919, by rfl⟩) R123839
theorem R248831 : Reach 248831 := rs (se 1 (by rfl) ⟨186623, by rfl⟩) R373247
theorem R482543 : Reach 482543 := rs (se 1 (by rfl) ⟨361907, by rfl⟩) R723815
theorem R155641 : Reach 155641 := rs (se 2 (by rfl) ⟨58365, by rfl⟩) R116731
theorem R58927 : Reach 58927 := rs (se 1 (by rfl) ⟨44195, by rfl⟩) R88391
theorem R1307461 : Reach 1307461 := rs (se 4 (by rfl) ⟨122574, by rfl⟩) R245149
theorem R292193 : Reach 292193 := rs (se 2 (by rfl) ⟨109572, by rfl⟩) R219145
theorem R165887 : Reach 165887 := rs (se 1 (by rfl) ⟨124415, by rfl⟩) R248831
theorem R232961 : Reach 232961 := rs (se 2 (by rfl) ⟨87360, by rfl⟩) R174721
theorem R70235 : Reach 70235 := rs (se 1 (by rfl) ⟨52676, by rfl⟩) R105353
theorem R1743281 : Reach 1743281 := rs (se 2 (by rfl) ⟨653730, by rfl⟩) R1307461
theorem R1055501 : Reach 1055501 := rs (se 3 (by rfl) ⟨197906, by rfl⟩) R395813
theorem R75419 : Reach 75419 := rs (se 1 (by rfl) ⟨56564, by rfl⟩) R113129
theorem R207521 : Reach 207521 := rs (se 2 (by rfl) ⟨77820, by rfl⟩) R155641
theorem R78569 : Reach 78569 := rs (se 2 (by rfl) ⟨29463, by rfl⟩) R58927
theorem R47135 : Reach 47135 := rs (se 1 (by rfl) ⟨35351, by rfl⟩) R70703
theorem R145529 : Reach 145529 := rs (se 2 (by rfl) ⟨54573, by rfl⟩) R109147
theorem R47615 : Reach 47615 := rs (se 1 (by rfl) ⟨35711, by rfl⟩) R71423
theorem R50459 : Reach 50459 := rs (se 1 (by rfl) ⟨37844, by rfl⟩) R75689
theorem R117179 : Reach 117179 := rs (se 1 (by rfl) ⟨87884, by rfl⟩) R175769
theorem R55039 : Reach 55039 := rs (se 1 (by rfl) ⟨41279, by rfl⟩) R82559
theorem R153353 : Reach 153353 := rs (se 2 (by rfl) ⟨57507, by rfl⟩) R115015
theorem R321695 : Reach 321695 := rs (se 1 (by rfl) ⟨241271, by rfl⟩) R482543
theorem R290051 : Reach 290051 := rs (se 1 (by rfl) ⟨217538, by rfl⟩) R435077
theorem R61817 : Reach 61817 := rs (se 2 (by rfl) ⟨23181, by rfl⟩) R46363
theorem R1602935 : Reach 1602935 := rs (se 1 (by rfl) ⟨1202201, by rfl⟩) R2404403
theorem R194795 : Reach 194795 := rs (se 1 (by rfl) ⟨146096, by rfl⟩) R292193
theorem R33639 : Reach 33639 := rs (se 1 (by rfl) ⟨25229, by rfl⟩) R50459
theorem R164845 : Reach 164845 := rs (se 3 (by rfl) ⟨30908, by rfl⟩) R61817
theorem R102235 : Reach 102235 := rs (se 1 (by rfl) ⟨76676, by rfl⟩) R153353
theorem R138347 : Reach 138347 := rs (se 1 (by rfl) ⟨103760, by rfl⟩) R207521
theorem R73385 : Reach 73385 := rs (se 2 (by rfl) ⟨27519, by rfl⟩) R55039
theorem R110591 : Reach 110591 := rs (se 1 (by rfl) ⟨82943, by rfl⟩) R165887
theorem R78119 : Reach 78119 := rs (se 1 (by rfl) ⟨58589, by rfl⟩) R117179
theorem R46823 : Reach 46823 := rs (se 1 (by rfl) ⟨35117, by rfl⟩) R70235
theorem R1162187 : Reach 1162187 := rs (se 1 (by rfl) ⟨871640, by rfl⟩) R1743281
theorem R703667 : Reach 703667 := rs (se 1 (by rfl) ⟨527750, by rfl⟩) R1055501
theorem R50279 : Reach 50279 := rs (se 1 (by rfl) ⟨37709, by rfl⟩) R75419
theorem R214463 : Reach 214463 := rs (se 1 (by rfl) ⟨160847, by rfl⟩) R321695
theorem R52379 : Reach 52379 := rs (se 1 (by rfl) ⟨39284, by rfl⟩) R78569
theorem R1068623 : Reach 1068623 := rs (se 1 (by rfl) ⟨801467, by rfl⟩) R1602935
theorem R193367 : Reach 193367 := rs (se 1 (by rfl) ⟨145025, by rfl⟩) R290051
theorem R621229 : Reach 621229 := rs (se 3 (by rfl) ⟨116480, by rfl⟩) R232961
theorem R31423 : Reach 31423 := rs (se 1 (by rfl) ⟨23567, by rfl⟩) R47135
theorem R97019 : Reach 97019 := rs (se 1 (by rfl) ⟨72764, by rfl⟩) R145529
theorem R129863 : Reach 129863 := rs (se 1 (by rfl) ⟨97397, by rfl⟩) R194795
theorem R31743 : Reach 31743 := rs (se 1 (by rfl) ⟨23807, by rfl⟩) R47615
theorem R33519 : Reach 33519 := rs (se 1 (by rfl) ⟨25139, by rfl⟩) R50279
theorem R34919 : Reach 34919 := rs (se 1 (by rfl) ⟨26189, by rfl⟩) R52379
theorem R136313 : Reach 136313 := rs (se 2 (by rfl) ⟨51117, by rfl⟩) R102235
theorem R73727 : Reach 73727 := rs (se 1 (by rfl) ⟨55295, by rfl⟩) R110591
theorem R828305 : Reach 828305 := rs (se 2 (by rfl) ⟨310614, by rfl⟩) R621229
theorem R41897 : Reach 41897 := rs (se 2 (by rfl) ⟨15711, by rfl⟩) R31423
theorem R469111 : Reach 469111 := rs (se 1 (by rfl) ⟨351833, by rfl⟩) R703667
theorem R142975 : Reach 142975 := rs (se 1 (by rfl) ⟨107231, by rfl⟩) R214463
theorem R48923 : Reach 48923 := rs (se 1 (by rfl) ⟨36692, by rfl⟩) R73385
theorem R52079 : Reach 52079 := rs (se 1 (by rfl) ⟨39059, by rfl⟩) R78119
theorem R86575 : Reach 86575 := rs (se 1 (by rfl) ⟨64931, by rfl⟩) R129863
theorem R774791 : Reach 774791 := rs (se 1 (by rfl) ⟨581093, by rfl⟩) R1162187
theorem R712415 : Reach 712415 := rs (se 1 (by rfl) ⟨534311, by rfl⟩) R1068623
theorem R92231 : Reach 92231 := rs (se 1 (by rfl) ⟨69173, by rfl⟩) R138347
theorem R879173 : Reach 879173 := rs (se 4 (by rfl) ⟨82422, by rfl⟩) R164845
theorem R128911 : Reach 128911 := rs (se 1 (by rfl) ⟨96683, by rfl⟩) R193367
theorem R31215 : Reach 31215 := rs (se 1 (by rfl) ⟨23411, by rfl⟩) R46823
theorem R64679 : Reach 64679 := rs (se 1 (by rfl) ⟨48509, by rfl⟩) R97019
theorem R34719 : Reach 34719 := rs (se 1 (by rfl) ⟨26039, by rfl⟩) R52079
theorem R625481 : Reach 625481 := rs (se 2 (by rfl) ⟨234555, by rfl⟩) R469111
theorem R171881 : Reach 171881 := rs (se 2 (by rfl) ⟨64455, by rfl⟩) R128911
theorem R172477 : Reach 172477 := rs (se 3 (by rfl) ⟨32339, by rfl⟩) R64679
theorem R762533 : Reach 762533 := rs (se 4 (by rfl) ⟨71487, by rfl⟩) R142975
theorem R111725 : Reach 111725 := rs (se 3 (by rfl) ⟨20948, by rfl⟩) R41897
theorem R49151 : Reach 49151 := rs (se 1 (by rfl) ⟨36863, by rfl⟩) R73727
theorem R115433 : Reach 115433 := rs (se 2 (by rfl) ⟨43287, by rfl⟩) R86575
theorem R516527 : Reach 516527 := rs (se 1 (by rfl) ⟨387395, by rfl⟩) R774791
theorem R90875 : Reach 90875 := rs (se 1 (by rfl) ⟨68156, by rfl⟩) R136313
theorem R190633 : Reach 190633 := rs (se 2 (by rfl) ⟨71487, by rfl⟩) R142975
theorem R552203 : Reach 552203 := rs (se 1 (by rfl) ⟨414152, by rfl⟩) R828305
theorem R61487 : Reach 61487 := rs (se 1 (by rfl) ⟨46115, by rfl⟩) R92231
theorem R586115 : Reach 586115 := rs (se 1 (by rfl) ⟨439586, by rfl⟩) R879173
theorem R1899773 : Reach 1899773 := rs (se 3 (by rfl) ⟨356207, by rfl⟩) R712415
theorem R32615 : Reach 32615 := rs (se 1 (by rfl) ⟨24461, by rfl⟩) R48923
theorem R229969 : Reach 229969 := rs (se 2 (by rfl) ⟨86238, by rfl⟩) R172477
theorem R368135 : Reach 368135 := rs (se 1 (by rfl) ⟨276101, by rfl⟩) R552203
theorem R40991 : Reach 40991 := rs (se 1 (by rfl) ⟨30743, by rfl⟩) R61487
theorem R74483 : Reach 74483 := rs (se 1 (by rfl) ⟨55862, by rfl⟩) R111725
theorem R76955 : Reach 76955 := rs (se 1 (by rfl) ⟨57716, by rfl⟩) R115433
theorem R114587 : Reach 114587 := rs (se 1 (by rfl) ⟨85940, by rfl⟩) R171881
theorem R344351 : Reach 344351 := rs (se 1 (by rfl) ⟨258263, by rfl⟩) R516527
theorem R508355 : Reach 508355 := rs (se 1 (by rfl) ⟨381266, by rfl⟩) R762533
theorem R1266515 : Reach 1266515 := rs (se 1 (by rfl) ⟨949886, by rfl⟩) R1899773
theorem R416987 : Reach 416987 := rs (se 1 (by rfl) ⟨312740, by rfl⟩) R625481
theorem R254177 : Reach 254177 := rs (se 2 (by rfl) ⟨95316, by rfl⟩) R190633
theorem R60583 : Reach 60583 := rs (se 1 (by rfl) ⟨45437, by rfl⟩) R90875
theorem R390743 : Reach 390743 := rs (se 1 (by rfl) ⟨293057, by rfl⟩) R586115
theorem R32767 : Reach 32767 := rs (se 1 (by rfl) ⟨24575, by rfl⟩) R49151
theorem R229567 : Reach 229567 := rs (se 1 (by rfl) ⟨172175, by rfl⟩) R344351
theorem R169451 : Reach 169451 := rs (se 1 (by rfl) ⟨127088, by rfl⟩) R254177
theorem R205213 : Reach 205213 := rs (se 3 (by rfl) ⟨38477, by rfl⟩) R76955
theorem R76391 : Reach 76391 := rs (se 1 (by rfl) ⟨57293, by rfl⟩) R114587
theorem R109309 : Reach 109309 := rs (se 3 (by rfl) ⟨20495, by rfl⟩) R40991
theorem R338903 : Reach 338903 := rs (se 1 (by rfl) ⟨254177, by rfl⟩) R508355
theorem R306625 : Reach 306625 := rs (se 2 (by rfl) ⟨114984, by rfl⟩) R229969
theorem R80777 : Reach 80777 := rs (se 2 (by rfl) ⟨30291, by rfl⟩) R60583
theorem R277991 : Reach 277991 := rs (se 1 (by rfl) ⟨208493, by rfl⟩) R416987
theorem R245423 : Reach 245423 := rs (se 1 (by rfl) ⟨184067, by rfl⟩) R368135
theorem R49655 : Reach 49655 := rs (se 1 (by rfl) ⟨37241, by rfl⟩) R74483
theorem R844343 : Reach 844343 := rs (se 1 (by rfl) ⟨633257, by rfl⟩) R1266515
theorem R260495 : Reach 260495 := rs (se 1 (by rfl) ⟨195371, by rfl⟩) R390743
theorem R33103 : Reach 33103 := rs (se 1 (by rfl) ⟨24827, by rfl⟩) R49655
theorem R562895 : Reach 562895 := rs (se 1 (by rfl) ⟨422171, by rfl⟩) R844343
theorem R173663 : Reach 173663 := rs (se 1 (by rfl) ⟨130247, by rfl⟩) R260495
theorem R306089 : Reach 306089 := rs (se 2 (by rfl) ⟨114783, by rfl⟩) R229567
theorem R273617 : Reach 273617 := rs (se 2 (by rfl) ⟨102606, by rfl⟩) R205213
theorem R112967 : Reach 112967 := rs (se 1 (by rfl) ⟨84725, by rfl⟩) R169451
theorem R145745 : Reach 145745 := rs (se 2 (by rfl) ⟨54654, by rfl⟩) R109309
theorem R408833 : Reach 408833 := rs (se 2 (by rfl) ⟨153312, by rfl⟩) R306625
theorem R50927 : Reach 50927 := rs (se 1 (by rfl) ⟨38195, by rfl⟩) R76391
theorem R53851 : Reach 53851 := rs (se 1 (by rfl) ⟨40388, by rfl⟩) R80777
theorem R185327 : Reach 185327 := rs (se 1 (by rfl) ⟨138995, by rfl⟩) R277991
theorem R225935 : Reach 225935 := rs (se 1 (by rfl) ⟨169451, by rfl⟩) R338903
theorem R163615 : Reach 163615 := rs (se 1 (by rfl) ⟨122711, by rfl⟩) R245423
theorem R33951 : Reach 33951 := rs (se 1 (by rfl) ⟨25463, by rfl⟩) R50927
theorem R71801 : Reach 71801 := rs (se 2 (by rfl) ⟨26925, by rfl⟩) R53851
theorem R204059 : Reach 204059 := rs (se 1 (by rfl) ⟨153044, by rfl⟩) R306089
theorem R75311 : Reach 75311 := rs (se 1 (by rfl) ⟨56483, by rfl⟩) R112967
theorem R272555 : Reach 272555 := rs (se 1 (by rfl) ⟨204416, by rfl⟩) R408833
theorem R375263 : Reach 375263 := rs (se 1 (by rfl) ⟨281447, by rfl⟩) R562895
theorem R115775 : Reach 115775 := rs (se 1 (by rfl) ⟨86831, by rfl⟩) R173663
theorem R182411 : Reach 182411 := rs (se 1 (by rfl) ⟨136808, by rfl⟩) R273617
theorem R150623 : Reach 150623 := rs (se 1 (by rfl) ⟨112967, by rfl⟩) R225935
theorem R218153 : Reach 218153 := rs (se 2 (by rfl) ⟨81807, by rfl⟩) R163615
theorem R123551 : Reach 123551 := rs (se 1 (by rfl) ⟨92663, by rfl⟩) R185327
theorem R97163 : Reach 97163 := rs (se 1 (by rfl) ⟨72872, by rfl⟩) R145745
theorem R100415 : Reach 100415 := rs (se 1 (by rfl) ⟨75311, by rfl⟩) R150623
theorem R136039 : Reach 136039 := rs (se 1 (by rfl) ⟨102029, by rfl⟩) R204059
theorem R77183 : Reach 77183 := rs (se 1 (by rfl) ⟨57887, by rfl⟩) R115775
theorem R47867 : Reach 47867 := rs (se 1 (by rfl) ⟨35900, by rfl⟩) R71801
theorem R82367 : Reach 82367 := rs (se 1 (by rfl) ⟨61775, by rfl⟩) R123551
theorem R50207 : Reach 50207 := rs (se 1 (by rfl) ⟨37655, by rfl⟩) R75311
theorem R181703 : Reach 181703 := rs (se 1 (by rfl) ⟨136277, by rfl⟩) R272555
theorem R250175 : Reach 250175 := rs (se 1 (by rfl) ⟨187631, by rfl⟩) R375263
theorem R121607 : Reach 121607 := rs (se 1 (by rfl) ⟨91205, by rfl⟩) R182411
theorem R581741 : Reach 581741 := rs (se 3 (by rfl) ⟨109076, by rfl⟩) R218153
theorem R64775 : Reach 64775 := rs (se 1 (by rfl) ⟨48581, by rfl⟩) R97163
theorem R33471 : Reach 33471 := rs (se 1 (by rfl) ⟨25103, by rfl⟩) R50207
theorem R66943 : Reach 66943 := rs (se 1 (by rfl) ⟨50207, by rfl⟩) R100415
theorem R43183 : Reach 43183 := rs (se 1 (by rfl) ⟨32387, by rfl⟩) R64775
theorem R667133 : Reach 667133 := rs (se 3 (by rfl) ⟨125087, by rfl⟩) R250175
theorem R81071 : Reach 81071 := rs (se 1 (by rfl) ⟨60803, by rfl⟩) R121607
theorem R181385 : Reach 181385 := rs (se 2 (by rfl) ⟨68019, by rfl⟩) R136039
theorem R51455 : Reach 51455 := rs (se 1 (by rfl) ⟨38591, by rfl⟩) R77183
theorem R54911 : Reach 54911 := rs (se 1 (by rfl) ⟨41183, by rfl⟩) R82367
theorem R121135 : Reach 121135 := rs (se 1 (by rfl) ⟨90851, by rfl⟩) R181703
theorem R387827 : Reach 387827 := rs (se 1 (by rfl) ⟨290870, by rfl⟩) R581741
theorem R31911 : Reach 31911 := rs (se 1 (by rfl) ⟨23933, by rfl⟩) R47867
theorem R34303 : Reach 34303 := rs (se 1 (by rfl) ⟨25727, by rfl⟩) R51455
theorem R36607 : Reach 36607 := rs (se 1 (by rfl) ⟨27455, by rfl⟩) R54911
theorem R444755 : Reach 444755 := rs (se 1 (by rfl) ⟨333566, by rfl⟩) R667133
theorem R54047 : Reach 54047 := rs (se 1 (by rfl) ⟨40535, by rfl⟩) R81071
theorem R120923 : Reach 120923 := rs (se 1 (by rfl) ⟨90692, by rfl⟩) R181385
theorem R89257 : Reach 89257 := rs (se 2 (by rfl) ⟨33471, by rfl⟩) R66943
theorem R57577 : Reach 57577 := rs (se 2 (by rfl) ⟨21591, by rfl⟩) R43183
theorem R258551 : Reach 258551 := rs (se 1 (by rfl) ⟨193913, by rfl⟩) R387827
theorem R161513 : Reach 161513 := rs (se 2 (by rfl) ⟨60567, by rfl⟩) R121135
theorem R296503 : Reach 296503 := rs (se 1 (by rfl) ⟨222377, by rfl⟩) R444755
theorem R36031 : Reach 36031 := rs (se 1 (by rfl) ⟨27023, by rfl⟩) R54047
theorem R172367 : Reach 172367 := rs (se 1 (by rfl) ⟨129275, by rfl⟩) R258551
theorem R107675 : Reach 107675 := rs (se 1 (by rfl) ⟨80756, by rfl⟩) R161513
theorem R76769 : Reach 76769 := rs (se 2 (by rfl) ⟨28788, by rfl⟩) R57577
theorem R80615 : Reach 80615 := rs (se 1 (by rfl) ⟨60461, by rfl⟩) R120923
theorem R48809 : Reach 48809 := rs (se 2 (by rfl) ⟨18303, by rfl⟩) R36607
theorem R119009 : Reach 119009 := rs (se 2 (by rfl) ⟨44628, by rfl⟩) R89257
theorem R6325397 : Reach 6325397 := rs (se 6 (by rfl) ⟨148251, by rfl⟩) R296503
theorem R71783 : Reach 71783 := rs (se 1 (by rfl) ⟨53837, by rfl⟩) R107675
theorem R79339 : Reach 79339 := rs (se 1 (by rfl) ⟨59504, by rfl⟩) R119009
theorem R48041 : Reach 48041 := rs (se 2 (by rfl) ⟨18015, by rfl⟩) R36031
theorem R114911 : Reach 114911 := rs (se 1 (by rfl) ⟨86183, by rfl⟩) R172367
theorem R51179 : Reach 51179 := rs (se 1 (by rfl) ⟨38384, by rfl⟩) R76769
theorem R53743 : Reach 53743 := rs (se 1 (by rfl) ⟨40307, by rfl⟩) R80615
theorem R317357 : Reach 317357 := rs (se 3 (by rfl) ⟨59504, by rfl⟩) R119009
theorem R130157 : Reach 130157 := rs (se 3 (by rfl) ⟨24404, by rfl⟩) R48809
theorem R32539 : Reach 32539 := rs (se 1 (by rfl) ⟨24404, by rfl⟩) R48809
theorem R34119 : Reach 34119 := rs (se 1 (by rfl) ⟨25589, by rfl⟩) R51179
theorem R71657 : Reach 71657 := rs (se 2 (by rfl) ⟨26871, by rfl⟩) R53743
theorem R105785 : Reach 105785 := rs (se 2 (by rfl) ⟨39669, by rfl⟩) R79339
theorem R76607 : Reach 76607 := rs (se 1 (by rfl) ⟨57455, by rfl⟩) R114911
theorem R211571 : Reach 211571 := rs (se 1 (by rfl) ⟨158678, by rfl⟩) R317357
theorem R47855 : Reach 47855 := rs (se 1 (by rfl) ⟨35891, by rfl⟩) R71783
theorem R86771 : Reach 86771 := rs (se 1 (by rfl) ⟨65078, by rfl⟩) R130157
theorem R4216931 : Reach 4216931 := rs (se 1 (by rfl) ⟨3162698, by rfl⟩) R6325397
theorem R32027 : Reach 32027 := rs (se 1 (by rfl) ⟨24020, by rfl⟩) R48041
theorem R70523 : Reach 70523 := rs (se 1 (by rfl) ⟨52892, by rfl⟩) R105785
theorem R141047 : Reach 141047 := rs (se 1 (by rfl) ⟨105785, by rfl⟩) R211571
theorem R47771 : Reach 47771 := rs (se 1 (by rfl) ⟨35828, by rfl⟩) R71657
theorem R51071 : Reach 51071 := rs (se 1 (by rfl) ⟨38303, by rfl⟩) R76607
theorem R57847 : Reach 57847 := rs (se 1 (by rfl) ⟨43385, by rfl⟩) R86771
theorem R2811287 : Reach 2811287 := rs (se 1 (by rfl) ⟨2108465, by rfl⟩) R4216931
theorem R31903 : Reach 31903 := rs (se 1 (by rfl) ⟨23927, by rfl⟩) R47855
theorem R34047 : Reach 34047 := rs (se 1 (by rfl) ⟨25535, by rfl⟩) R51071
theorem R1874191 : Reach 1874191 := rs (se 1 (by rfl) ⟨1405643, by rfl⟩) R2811287
theorem R77129 : Reach 77129 := rs (se 2 (by rfl) ⟨28923, by rfl⟩) R57847
theorem R47015 : Reach 47015 := rs (se 1 (by rfl) ⟨35261, by rfl⟩) R70523
theorem R94031 : Reach 94031 := rs (se 1 (by rfl) ⟨70523, by rfl⟩) R141047
theorem R31847 : Reach 31847 := rs (se 1 (by rfl) ⟨23885, by rfl⟩) R47771
theorem R2498921 : Reach 2498921 := rs (se 2 (by rfl) ⟨937095, by rfl⟩) R1874191
theorem R51419 : Reach 51419 := rs (se 1 (by rfl) ⟨38564, by rfl⟩) R77129
theorem R62687 : Reach 62687 := rs (se 1 (by rfl) ⟨47015, by rfl⟩) R94031
theorem R31343 : Reach 31343 := rs (se 1 (by rfl) ⟨23507, by rfl⟩) R47015
theorem R34279 : Reach 34279 := rs (se 1 (by rfl) ⟨25709, by rfl⟩) R51419
theorem R41791 : Reach 41791 := rs (se 1 (by rfl) ⟨31343, by rfl⟩) R62687
theorem R1665947 : Reach 1665947 := rs (se 1 (by rfl) ⟨1249460, by rfl⟩) R2498921
theorem R55721 : Reach 55721 := rs (se 2 (by rfl) ⟨20895, by rfl⟩) R41791
theorem R1110631 : Reach 1110631 := rs (se 1 (by rfl) ⟨832973, by rfl⟩) R1665947
theorem R37147 : Reach 37147 := rs (se 1 (by rfl) ⟨27860, by rfl⟩) R55721
theorem R1480841 : Reach 1480841 := rs (se 2 (by rfl) ⟨555315, by rfl⟩) R1110631
theorem R987227 : Reach 987227 := rs (se 1 (by rfl) ⟨740420, by rfl⟩) R1480841
theorem R49529 : Reach 49529 := rs (se 2 (by rfl) ⟨18573, by rfl⟩) R37147
theorem R33019 : Reach 33019 := rs (se 1 (by rfl) ⟨24764, by rfl⟩) R49529
theorem R658151 : Reach 658151 := rs (se 1 (by rfl) ⟨493613, by rfl⟩) R987227
theorem R438767 : Reach 438767 := rs (se 1 (by rfl) ⟨329075, by rfl⟩) R658151
theorem R292511 : Reach 292511 := rs (se 1 (by rfl) ⟨219383, by rfl⟩) R438767
theorem R195007 : Reach 195007 := rs (se 1 (by rfl) ⟨146255, by rfl⟩) R292511
theorem R260009 : Reach 260009 := rs (se 2 (by rfl) ⟨97503, by rfl⟩) R195007
theorem R173339 : Reach 173339 := rs (se 1 (by rfl) ⟨130004, by rfl⟩) R260009
theorem R115559 : Reach 115559 := rs (se 1 (by rfl) ⟨86669, by rfl⟩) R173339
theorem R77039 : Reach 77039 := rs (se 1 (by rfl) ⟨57779, by rfl⟩) R115559
theorem R51359 : Reach 51359 := rs (se 1 (by rfl) ⟨38519, by rfl⟩) R77039
theorem R34239 : Reach 34239 := rs (se 1 (by rfl) ⟨25679, by rfl⟩) R51359

theorem C0 (j : ℕ) (h1 : 15557 ≤ j) (h2 : j ≤ 16256) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R31115
  · exact R31117
  · exact R31119
  · exact R31121
  · exact R31123
  · exact R31125
  · exact R31127
  · exact R31129
  · exact R31131
  · exact R31133
  · exact R31135
  · exact R31137
  · exact R31139
  · exact R31141
  · exact R31143
  · exact R31145
  · exact R31147
  · exact R31149
  · exact R31151
  · exact R31153
  · exact R31155
  · exact R31157
  · exact R31159
  · exact R31161
  · exact R31163
  · exact R31165
  · exact R31167
  · exact R31169
  · exact R31171
  · exact R31173
  · exact R31175
  · exact R31177
  · exact R31179
  · exact R31181
  · exact R31183
  · exact R31185
  · exact R31187
  · exact R31189
  · exact R31191
  · exact R31193
  · exact R31195
  · exact R31197
  · exact R31199
  · exact R31201
  · exact R31203
  · exact R31205
  · exact R31207
  · exact R31209
  · exact R31211
  · exact R31213
  · exact R31215
  · exact R31217
  · exact R31219
  · exact R31221
  · exact R31223
  · exact R31225
  · exact R31227
  · exact R31229
  · exact R31231
  · exact R31233
  · exact R31235
  · exact R31237
  · exact R31239
  · exact R31241
  · exact R31243
  · exact R31245
  · exact R31247
  · exact R31249
  · exact R31251
  · exact R31253
  · exact R31255
  · exact R31257
  · exact R31259
  · exact R31261
  · exact R31263
  · exact R31265
  · exact R31267
  · exact R31269
  · exact R31271
  · exact R31273
  · exact R31275
  · exact R31277
  · exact R31279
  · exact R31281
  · exact R31283
  · exact R31285
  · exact R31287
  · exact R31289
  · exact R31291
  · exact R31293
  · exact R31295
  · exact R31297
  · exact R31299
  · exact R31301
  · exact R31303
  · exact R31305
  · exact R31307
  · exact R31309
  · exact R31311
  · exact R31313
  · exact R31315
  · exact R31317
  · exact R31319
  · exact R31321
  · exact R31323
  · exact R31325
  · exact R31327
  · exact R31329
  · exact R31331
  · exact R31333
  · exact R31335
  · exact R31337
  · exact R31339
  · exact R31341
  · exact R31343
  · exact R31345
  · exact R31347
  · exact R31349
  · exact R31351
  · exact R31353
  · exact R31355
  · exact R31357
  · exact R31359
  · exact R31361
  · exact R31363
  · exact R31365
  · exact R31367
  · exact R31369
  · exact R31371
  · exact R31373
  · exact R31375
  · exact R31377
  · exact R31379
  · exact R31381
  · exact R31383
  · exact R31385
  · exact R31387
  · exact R31389
  · exact R31391
  · exact R31393
  · exact R31395
  · exact R31397
  · exact R31399
  · exact R31401
  · exact R31403
  · exact R31405
  · exact R31407
  · exact R31409
  · exact R31411
  · exact R31413
  · exact R31415
  · exact R31417
  · exact R31419
  · exact R31421
  · exact R31423
  · exact R31425
  · exact R31427
  · exact R31429
  · exact R31431
  · exact R31433
  · exact R31435
  · exact R31437
  · exact R31439
  · exact R31441
  · exact R31443
  · exact R31445
  · exact R31447
  · exact R31449
  · exact R31451
  · exact R31453
  · exact R31455
  · exact R31457
  · exact R31459
  · exact R31461
  · exact R31463
  · exact R31465
  · exact R31467
  · exact R31469
  · exact R31471
  · exact R31473
  · exact R31475
  · exact R31477
  · exact R31479
  · exact R31481
  · exact R31483
  · exact R31485
  · exact R31487
  · exact R31489
  · exact R31491
  · exact R31493
  · exact R31495
  · exact R31497
  · exact R31499
  · exact R31501
  · exact R31503
  · exact R31505
  · exact R31507
  · exact R31509
  · exact R31511
  · exact R31513
  · exact R31515
  · exact R31517
  · exact R31519
  · exact R31521
  · exact R31523
  · exact R31525
  · exact R31527
  · exact R31529
  · exact R31531
  · exact R31533
  · exact R31535
  · exact R31537
  · exact R31539
  · exact R31541
  · exact R31543
  · exact R31545
  · exact R31547
  · exact R31549
  · exact R31551
  · exact R31553
  · exact R31555
  · exact R31557
  · exact R31559
  · exact R31561
  · exact R31563
  · exact R31565
  · exact R31567
  · exact R31569
  · exact R31571
  · exact R31573
  · exact R31575
  · exact R31577
  · exact R31579
  · exact R31581
  · exact R31583
  · exact R31585
  · exact R31587
  · exact R31589
  · exact R31591
  · exact R31593
  · exact R31595
  · exact R31597
  · exact R31599
  · exact R31601
  · exact R31603
  · exact R31605
  · exact R31607
  · exact R31609
  · exact R31611
  · exact R31613
  · exact R31615
  · exact R31617
  · exact R31619
  · exact R31621
  · exact R31623
  · exact R31625
  · exact R31627
  · exact R31629
  · exact R31631
  · exact R31633
  · exact R31635
  · exact R31637
  · exact R31639
  · exact R31641
  · exact R31643
  · exact R31645
  · exact R31647
  · exact R31649
  · exact R31651
  · exact R31653
  · exact R31655
  · exact R31657
  · exact R31659
  · exact R31661
  · exact R31663
  · exact R31665
  · exact R31667
  · exact R31669
  · exact R31671
  · exact R31673
  · exact R31675
  · exact R31677
  · exact R31679
  · exact R31681
  · exact R31683
  · exact R31685
  · exact R31687
  · exact R31689
  · exact R31691
  · exact R31693
  · exact R31695
  · exact R31697
  · exact R31699
  · exact R31701
  · exact R31703
  · exact R31705
  · exact R31707
  · exact R31709
  · exact R31711
  · exact R31713
  · exact R31715
  · exact R31717
  · exact R31719
  · exact R31721
  · exact R31723
  · exact R31725
  · exact R31727
  · exact R31729
  · exact R31731
  · exact R31733
  · exact R31735
  · exact R31737
  · exact R31739
  · exact R31741
  · exact R31743
  · exact R31745
  · exact R31747
  · exact R31749
  · exact R31751
  · exact R31753
  · exact R31755
  · exact R31757
  · exact R31759
  · exact R31761
  · exact R31763
  · exact R31765
  · exact R31767
  · exact R31769
  · exact R31771
  · exact R31773
  · exact R31775
  · exact R31777
  · exact R31779
  · exact R31781
  · exact R31783
  · exact R31785
  · exact R31787
  · exact R31789
  · exact R31791
  · exact R31793
  · exact R31795
  · exact R31797
  · exact R31799
  · exact R31801
  · exact R31803
  · exact R31805
  · exact R31807
  · exact R31809
  · exact R31811
  · exact R31813
  · exact R31815
  · exact R31817
  · exact R31819
  · exact R31821
  · exact R31823
  · exact R31825
  · exact R31827
  · exact R31829
  · exact R31831
  · exact R31833
  · exact R31835
  · exact R31837
  · exact R31839
  · exact R31841
  · exact R31843
  · exact R31845
  · exact R31847
  · exact R31849
  · exact R31851
  · exact R31853
  · exact R31855
  · exact R31857
  · exact R31859
  · exact R31861
  · exact R31863
  · exact R31865
  · exact R31867
  · exact R31869
  · exact R31871
  · exact R31873
  · exact R31875
  · exact R31877
  · exact R31879
  · exact R31881
  · exact R31883
  · exact R31885
  · exact R31887
  · exact R31889
  · exact R31891
  · exact R31893
  · exact R31895
  · exact R31897
  · exact R31899
  · exact R31901
  · exact R31903
  · exact R31905
  · exact R31907
  · exact R31909
  · exact R31911
  · exact R31913
  · exact R31915
  · exact R31917
  · exact R31919
  · exact R31921
  · exact R31923
  · exact R31925
  · exact R31927
  · exact R31929
  · exact R31931
  · exact R31933
  · exact R31935
  · exact R31937
  · exact R31939
  · exact R31941
  · exact R31943
  · exact R31945
  · exact R31947
  · exact R31949
  · exact R31951
  · exact R31953
  · exact R31955
  · exact R31957
  · exact R31959
  · exact R31961
  · exact R31963
  · exact R31965
  · exact R31967
  · exact R31969
  · exact R31971
  · exact R31973
  · exact R31975
  · exact R31977
  · exact R31979
  · exact R31981
  · exact R31983
  · exact R31985
  · exact R31987
  · exact R31989
  · exact R31991
  · exact R31993
  · exact R31995
  · exact R31997
  · exact R31999
  · exact R32001
  · exact R32003
  · exact R32005
  · exact R32007
  · exact R32009
  · exact R32011
  · exact R32013
  · exact R32015
  · exact R32017
  · exact R32019
  · exact R32021
  · exact R32023
  · exact R32025
  · exact R32027
  · exact R32029
  · exact R32031
  · exact R32033
  · exact R32035
  · exact R32037
  · exact R32039
  · exact R32041
  · exact R32043
  · exact R32045
  · exact R32047
  · exact R32049
  · exact R32051
  · exact R32053
  · exact R32055
  · exact R32057
  · exact R32059
  · exact R32061
  · exact R32063
  · exact R32065
  · exact R32067
  · exact R32069
  · exact R32071
  · exact R32073
  · exact R32075
  · exact R32077
  · exact R32079
  · exact R32081
  · exact R32083
  · exact R32085
  · exact R32087
  · exact R32089
  · exact R32091
  · exact R32093
  · exact R32095
  · exact R32097
  · exact R32099
  · exact R32101
  · exact R32103
  · exact R32105
  · exact R32107
  · exact R32109
  · exact R32111
  · exact R32113
  · exact R32115
  · exact R32117
  · exact R32119
  · exact R32121
  · exact R32123
  · exact R32125
  · exact R32127
  · exact R32129
  · exact R32131
  · exact R32133
  · exact R32135
  · exact R32137
  · exact R32139
  · exact R32141
  · exact R32143
  · exact R32145
  · exact R32147
  · exact R32149
  · exact R32151
  · exact R32153
  · exact R32155
  · exact R32157
  · exact R32159
  · exact R32161
  · exact R32163
  · exact R32165
  · exact R32167
  · exact R32169
  · exact R32171
  · exact R32173
  · exact R32175
  · exact R32177
  · exact R32179
  · exact R32181
  · exact R32183
  · exact R32185
  · exact R32187
  · exact R32189
  · exact R32191
  · exact R32193
  · exact R32195
  · exact R32197
  · exact R32199
  · exact R32201
  · exact R32203
  · exact R32205
  · exact R32207
  · exact R32209
  · exact R32211
  · exact R32213
  · exact R32215
  · exact R32217
  · exact R32219
  · exact R32221
  · exact R32223
  · exact R32225
  · exact R32227
  · exact R32229
  · exact R32231
  · exact R32233
  · exact R32235
  · exact R32237
  · exact R32239
  · exact R32241
  · exact R32243
  · exact R32245
  · exact R32247
  · exact R32249
  · exact R32251
  · exact R32253
  · exact R32255
  · exact R32257
  · exact R32259
  · exact R32261
  · exact R32263
  · exact R32265
  · exact R32267
  · exact R32269
  · exact R32271
  · exact R32273
  · exact R32275
  · exact R32277
  · exact R32279
  · exact R32281
  · exact R32283
  · exact R32285
  · exact R32287
  · exact R32289
  · exact R32291
  · exact R32293
  · exact R32295
  · exact R32297
  · exact R32299
  · exact R32301
  · exact R32303
  · exact R32305
  · exact R32307
  · exact R32309
  · exact R32311
  · exact R32313
  · exact R32315
  · exact R32317
  · exact R32319
  · exact R32321
  · exact R32323
  · exact R32325
  · exact R32327
  · exact R32329
  · exact R32331
  · exact R32333
  · exact R32335
  · exact R32337
  · exact R32339
  · exact R32341
  · exact R32343
  · exact R32345
  · exact R32347
  · exact R32349
  · exact R32351
  · exact R32353
  · exact R32355
  · exact R32357
  · exact R32359
  · exact R32361
  · exact R32363
  · exact R32365
  · exact R32367
  · exact R32369
  · exact R32371
  · exact R32373
  · exact R32375
  · exact R32377
  · exact R32379
  · exact R32381
  · exact R32383
  · exact R32385
  · exact R32387
  · exact R32389
  · exact R32391
  · exact R32393
  · exact R32395
  · exact R32397
  · exact R32399
  · exact R32401
  · exact R32403
  · exact R32405
  · exact R32407
  · exact R32409
  · exact R32411
  · exact R32413
  · exact R32415
  · exact R32417
  · exact R32419
  · exact R32421
  · exact R32423
  · exact R32425
  · exact R32427
  · exact R32429
  · exact R32431
  · exact R32433
  · exact R32435
  · exact R32437
  · exact R32439
  · exact R32441
  · exact R32443
  · exact R32445
  · exact R32447
  · exact R32449
  · exact R32451
  · exact R32453
  · exact R32455
  · exact R32457
  · exact R32459
  · exact R32461
  · exact R32463
  · exact R32465
  · exact R32467
  · exact R32469
  · exact R32471
  · exact R32473
  · exact R32475
  · exact R32477
  · exact R32479
  · exact R32481
  · exact R32483
  · exact R32485
  · exact R32487
  · exact R32489
  · exact R32491
  · exact R32493
  · exact R32495
  · exact R32497
  · exact R32499
  · exact R32501
  · exact R32503
  · exact R32505
  · exact R32507
  · exact R32509
  · exact R32511
  · exact R32513

theorem C1 (j : ℕ) (h1 : 16257 ≤ j) (h2 : j ≤ 16956) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R32515
  · exact R32517
  · exact R32519
  · exact R32521
  · exact R32523
  · exact R32525
  · exact R32527
  · exact R32529
  · exact R32531
  · exact R32533
  · exact R32535
  · exact R32537
  · exact R32539
  · exact R32541
  · exact R32543
  · exact R32545
  · exact R32547
  · exact R32549
  · exact R32551
  · exact R32553
  · exact R32555
  · exact R32557
  · exact R32559
  · exact R32561
  · exact R32563
  · exact R32565
  · exact R32567
  · exact R32569
  · exact R32571
  · exact R32573
  · exact R32575
  · exact R32577
  · exact R32579
  · exact R32581
  · exact R32583
  · exact R32585
  · exact R32587
  · exact R32589
  · exact R32591
  · exact R32593
  · exact R32595
  · exact R32597
  · exact R32599
  · exact R32601
  · exact R32603
  · exact R32605
  · exact R32607
  · exact R32609
  · exact R32611
  · exact R32613
  · exact R32615
  · exact R32617
  · exact R32619
  · exact R32621
  · exact R32623
  · exact R32625
  · exact R32627
  · exact R32629
  · exact R32631
  · exact R32633
  · exact R32635
  · exact R32637
  · exact R32639
  · exact R32641
  · exact R32643
  · exact R32645
  · exact R32647
  · exact R32649
  · exact R32651
  · exact R32653
  · exact R32655
  · exact R32657
  · exact R32659
  · exact R32661
  · exact R32663
  · exact R32665
  · exact R32667
  · exact R32669
  · exact R32671
  · exact R32673
  · exact R32675
  · exact R32677
  · exact R32679
  · exact R32681
  · exact R32683
  · exact R32685
  · exact R32687
  · exact R32689
  · exact R32691
  · exact R32693
  · exact R32695
  · exact R32697
  · exact R32699
  · exact R32701
  · exact R32703
  · exact R32705
  · exact R32707
  · exact R32709
  · exact R32711
  · exact R32713
  · exact R32715
  · exact R32717
  · exact R32719
  · exact R32721
  · exact R32723
  · exact R32725
  · exact R32727
  · exact R32729
  · exact R32731
  · exact R32733
  · exact R32735
  · exact R32737
  · exact R32739
  · exact R32741
  · exact R32743
  · exact R32745
  · exact R32747
  · exact R32749
  · exact R32751
  · exact R32753
  · exact R32755
  · exact R32757
  · exact R32759
  · exact R32761
  · exact R32763
  · exact R32765
  · exact R32767
  · exact R32769
  · exact R32771
  · exact R32773
  · exact R32775
  · exact R32777
  · exact R32779
  · exact R32781
  · exact R32783
  · exact R32785
  · exact R32787
  · exact R32789
  · exact R32791
  · exact R32793
  · exact R32795
  · exact R32797
  · exact R32799
  · exact R32801
  · exact R32803
  · exact R32805
  · exact R32807
  · exact R32809
  · exact R32811
  · exact R32813
  · exact R32815
  · exact R32817
  · exact R32819
  · exact R32821
  · exact R32823
  · exact R32825
  · exact R32827
  · exact R32829
  · exact R32831
  · exact R32833
  · exact R32835
  · exact R32837
  · exact R32839
  · exact R32841
  · exact R32843
  · exact R32845
  · exact R32847
  · exact R32849
  · exact R32851
  · exact R32853
  · exact R32855
  · exact R32857
  · exact R32859
  · exact R32861
  · exact R32863
  · exact R32865
  · exact R32867
  · exact R32869
  · exact R32871
  · exact R32873
  · exact R32875
  · exact R32877
  · exact R32879
  · exact R32881
  · exact R32883
  · exact R32885
  · exact R32887
  · exact R32889
  · exact R32891
  · exact R32893
  · exact R32895
  · exact R32897
  · exact R32899
  · exact R32901
  · exact R32903
  · exact R32905
  · exact R32907
  · exact R32909
  · exact R32911
  · exact R32913
  · exact R32915
  · exact R32917
  · exact R32919
  · exact R32921
  · exact R32923
  · exact R32925
  · exact R32927
  · exact R32929
  · exact R32931
  · exact R32933
  · exact R32935
  · exact R32937
  · exact R32939
  · exact R32941
  · exact R32943
  · exact R32945
  · exact R32947
  · exact R32949
  · exact R32951
  · exact R32953
  · exact R32955
  · exact R32957
  · exact R32959
  · exact R32961
  · exact R32963
  · exact R32965
  · exact R32967
  · exact R32969
  · exact R32971
  · exact R32973
  · exact R32975
  · exact R32977
  · exact R32979
  · exact R32981
  · exact R32983
  · exact R32985
  · exact R32987
  · exact R32989
  · exact R32991
  · exact R32993
  · exact R32995
  · exact R32997
  · exact R32999
  · exact R33001
  · exact R33003
  · exact R33005
  · exact R33007
  · exact R33009
  · exact R33011
  · exact R33013
  · exact R33015
  · exact R33017
  · exact R33019
  · exact R33021
  · exact R33023
  · exact R33025
  · exact R33027
  · exact R33029
  · exact R33031
  · exact R33033
  · exact R33035
  · exact R33037
  · exact R33039
  · exact R33041
  · exact R33043
  · exact R33045
  · exact R33047
  · exact R33049
  · exact R33051
  · exact R33053
  · exact R33055
  · exact R33057
  · exact R33059
  · exact R33061
  · exact R33063
  · exact R33065
  · exact R33067
  · exact R33069
  · exact R33071
  · exact R33073
  · exact R33075
  · exact R33077
  · exact R33079
  · exact R33081
  · exact R33083
  · exact R33085
  · exact R33087
  · exact R33089
  · exact R33091
  · exact R33093
  · exact R33095
  · exact R33097
  · exact R33099
  · exact R33101
  · exact R33103
  · exact R33105
  · exact R33107
  · exact R33109
  · exact R33111
  · exact R33113
  · exact R33115
  · exact R33117
  · exact R33119
  · exact R33121
  · exact R33123
  · exact R33125
  · exact R33127
  · exact R33129
  · exact R33131
  · exact R33133
  · exact R33135
  · exact R33137
  · exact R33139
  · exact R33141
  · exact R33143
  · exact R33145
  · exact R33147
  · exact R33149
  · exact R33151
  · exact R33153
  · exact R33155
  · exact R33157
  · exact R33159
  · exact R33161
  · exact R33163
  · exact R33165
  · exact R33167
  · exact R33169
  · exact R33171
  · exact R33173
  · exact R33175
  · exact R33177
  · exact R33179
  · exact R33181
  · exact R33183
  · exact R33185
  · exact R33187
  · exact R33189
  · exact R33191
  · exact R33193
  · exact R33195
  · exact R33197
  · exact R33199
  · exact R33201
  · exact R33203
  · exact R33205
  · exact R33207
  · exact R33209
  · exact R33211
  · exact R33213
  · exact R33215
  · exact R33217
  · exact R33219
  · exact R33221
  · exact R33223
  · exact R33225
  · exact R33227
  · exact R33229
  · exact R33231
  · exact R33233
  · exact R33235
  · exact R33237
  · exact R33239
  · exact R33241
  · exact R33243
  · exact R33245
  · exact R33247
  · exact R33249
  · exact R33251
  · exact R33253
  · exact R33255
  · exact R33257
  · exact R33259
  · exact R33261
  · exact R33263
  · exact R33265
  · exact R33267
  · exact R33269
  · exact R33271
  · exact R33273
  · exact R33275
  · exact R33277
  · exact R33279
  · exact R33281
  · exact R33283
  · exact R33285
  · exact R33287
  · exact R33289
  · exact R33291
  · exact R33293
  · exact R33295
  · exact R33297
  · exact R33299
  · exact R33301
  · exact R33303
  · exact R33305
  · exact R33307
  · exact R33309
  · exact R33311
  · exact R33313
  · exact R33315
  · exact R33317
  · exact R33319
  · exact R33321
  · exact R33323
  · exact R33325
  · exact R33327
  · exact R33329
  · exact R33331
  · exact R33333
  · exact R33335
  · exact R33337
  · exact R33339
  · exact R33341
  · exact R33343
  · exact R33345
  · exact R33347
  · exact R33349
  · exact R33351
  · exact R33353
  · exact R33355
  · exact R33357
  · exact R33359
  · exact R33361
  · exact R33363
  · exact R33365
  · exact R33367
  · exact R33369
  · exact R33371
  · exact R33373
  · exact R33375
  · exact R33377
  · exact R33379
  · exact R33381
  · exact R33383
  · exact R33385
  · exact R33387
  · exact R33389
  · exact R33391
  · exact R33393
  · exact R33395
  · exact R33397
  · exact R33399
  · exact R33401
  · exact R33403
  · exact R33405
  · exact R33407
  · exact R33409
  · exact R33411
  · exact R33413
  · exact R33415
  · exact R33417
  · exact R33419
  · exact R33421
  · exact R33423
  · exact R33425
  · exact R33427
  · exact R33429
  · exact R33431
  · exact R33433
  · exact R33435
  · exact R33437
  · exact R33439
  · exact R33441
  · exact R33443
  · exact R33445
  · exact R33447
  · exact R33449
  · exact R33451
  · exact R33453
  · exact R33455
  · exact R33457
  · exact R33459
  · exact R33461
  · exact R33463
  · exact R33465
  · exact R33467
  · exact R33469
  · exact R33471
  · exact R33473
  · exact R33475
  · exact R33477
  · exact R33479
  · exact R33481
  · exact R33483
  · exact R33485
  · exact R33487
  · exact R33489
  · exact R33491
  · exact R33493
  · exact R33495
  · exact R33497
  · exact R33499
  · exact R33501
  · exact R33503
  · exact R33505
  · exact R33507
  · exact R33509
  · exact R33511
  · exact R33513
  · exact R33515
  · exact R33517
  · exact R33519
  · exact R33521
  · exact R33523
  · exact R33525
  · exact R33527
  · exact R33529
  · exact R33531
  · exact R33533
  · exact R33535
  · exact R33537
  · exact R33539
  · exact R33541
  · exact R33543
  · exact R33545
  · exact R33547
  · exact R33549
  · exact R33551
  · exact R33553
  · exact R33555
  · exact R33557
  · exact R33559
  · exact R33561
  · exact R33563
  · exact R33565
  · exact R33567
  · exact R33569
  · exact R33571
  · exact R33573
  · exact R33575
  · exact R33577
  · exact R33579
  · exact R33581
  · exact R33583
  · exact R33585
  · exact R33587
  · exact R33589
  · exact R33591
  · exact R33593
  · exact R33595
  · exact R33597
  · exact R33599
  · exact R33601
  · exact R33603
  · exact R33605
  · exact R33607
  · exact R33609
  · exact R33611
  · exact R33613
  · exact R33615
  · exact R33617
  · exact R33619
  · exact R33621
  · exact R33623
  · exact R33625
  · exact R33627
  · exact R33629
  · exact R33631
  · exact R33633
  · exact R33635
  · exact R33637
  · exact R33639
  · exact R33641
  · exact R33643
  · exact R33645
  · exact R33647
  · exact R33649
  · exact R33651
  · exact R33653
  · exact R33655
  · exact R33657
  · exact R33659
  · exact R33661
  · exact R33663
  · exact R33665
  · exact R33667
  · exact R33669
  · exact R33671
  · exact R33673
  · exact R33675
  · exact R33677
  · exact R33679
  · exact R33681
  · exact R33683
  · exact R33685
  · exact R33687
  · exact R33689
  · exact R33691
  · exact R33693
  · exact R33695
  · exact R33697
  · exact R33699
  · exact R33701
  · exact R33703
  · exact R33705
  · exact R33707
  · exact R33709
  · exact R33711
  · exact R33713
  · exact R33715
  · exact R33717
  · exact R33719
  · exact R33721
  · exact R33723
  · exact R33725
  · exact R33727
  · exact R33729
  · exact R33731
  · exact R33733
  · exact R33735
  · exact R33737
  · exact R33739
  · exact R33741
  · exact R33743
  · exact R33745
  · exact R33747
  · exact R33749
  · exact R33751
  · exact R33753
  · exact R33755
  · exact R33757
  · exact R33759
  · exact R33761
  · exact R33763
  · exact R33765
  · exact R33767
  · exact R33769
  · exact R33771
  · exact R33773
  · exact R33775
  · exact R33777
  · exact R33779
  · exact R33781
  · exact R33783
  · exact R33785
  · exact R33787
  · exact R33789
  · exact R33791
  · exact R33793
  · exact R33795
  · exact R33797
  · exact R33799
  · exact R33801
  · exact R33803
  · exact R33805
  · exact R33807
  · exact R33809
  · exact R33811
  · exact R33813
  · exact R33815
  · exact R33817
  · exact R33819
  · exact R33821
  · exact R33823
  · exact R33825
  · exact R33827
  · exact R33829
  · exact R33831
  · exact R33833
  · exact R33835
  · exact R33837
  · exact R33839
  · exact R33841
  · exact R33843
  · exact R33845
  · exact R33847
  · exact R33849
  · exact R33851
  · exact R33853
  · exact R33855
  · exact R33857
  · exact R33859
  · exact R33861
  · exact R33863
  · exact R33865
  · exact R33867
  · exact R33869
  · exact R33871
  · exact R33873
  · exact R33875
  · exact R33877
  · exact R33879
  · exact R33881
  · exact R33883
  · exact R33885
  · exact R33887
  · exact R33889
  · exact R33891
  · exact R33893
  · exact R33895
  · exact R33897
  · exact R33899
  · exact R33901
  · exact R33903
  · exact R33905
  · exact R33907
  · exact R33909
  · exact R33911
  · exact R33913

theorem C2 (j : ℕ) (h1 : 16957 ≤ j) (h2 : j ≤ 17557) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R33915
  · exact R33917
  · exact R33919
  · exact R33921
  · exact R33923
  · exact R33925
  · exact R33927
  · exact R33929
  · exact R33931
  · exact R33933
  · exact R33935
  · exact R33937
  · exact R33939
  · exact R33941
  · exact R33943
  · exact R33945
  · exact R33947
  · exact R33949
  · exact R33951
  · exact R33953
  · exact R33955
  · exact R33957
  · exact R33959
  · exact R33961
  · exact R33963
  · exact R33965
  · exact R33967
  · exact R33969
  · exact R33971
  · exact R33973
  · exact R33975
  · exact R33977
  · exact R33979
  · exact R33981
  · exact R33983
  · exact R33985
  · exact R33987
  · exact R33989
  · exact R33991
  · exact R33993
  · exact R33995
  · exact R33997
  · exact R33999
  · exact R34001
  · exact R34003
  · exact R34005
  · exact R34007
  · exact R34009
  · exact R34011
  · exact R34013
  · exact R34015
  · exact R34017
  · exact R34019
  · exact R34021
  · exact R34023
  · exact R34025
  · exact R34027
  · exact R34029
  · exact R34031
  · exact R34033
  · exact R34035
  · exact R34037
  · exact R34039
  · exact R34041
  · exact R34043
  · exact R34045
  · exact R34047
  · exact R34049
  · exact R34051
  · exact R34053
  · exact R34055
  · exact R34057
  · exact R34059
  · exact R34061
  · exact R34063
  · exact R34065
  · exact R34067
  · exact R34069
  · exact R34071
  · exact R34073
  · exact R34075
  · exact R34077
  · exact R34079
  · exact R34081
  · exact R34083
  · exact R34085
  · exact R34087
  · exact R34089
  · exact R34091
  · exact R34093
  · exact R34095
  · exact R34097
  · exact R34099
  · exact R34101
  · exact R34103
  · exact R34105
  · exact R34107
  · exact R34109
  · exact R34111
  · exact R34113
  · exact R34115
  · exact R34117
  · exact R34119
  · exact R34121
  · exact R34123
  · exact R34125
  · exact R34127
  · exact R34129
  · exact R34131
  · exact R34133
  · exact R34135
  · exact R34137
  · exact R34139
  · exact R34141
  · exact R34143
  · exact R34145
  · exact R34147
  · exact R34149
  · exact R34151
  · exact R34153
  · exact R34155
  · exact R34157
  · exact R34159
  · exact R34161
  · exact R34163
  · exact R34165
  · exact R34167
  · exact R34169
  · exact R34171
  · exact R34173
  · exact R34175
  · exact R34177
  · exact R34179
  · exact R34181
  · exact R34183
  · exact R34185
  · exact R34187
  · exact R34189
  · exact R34191
  · exact R34193
  · exact R34195
  · exact R34197
  · exact R34199
  · exact R34201
  · exact R34203
  · exact R34205
  · exact R34207
  · exact R34209
  · exact R34211
  · exact R34213
  · exact R34215
  · exact R34217
  · exact R34219
  · exact R34221
  · exact R34223
  · exact R34225
  · exact R34227
  · exact R34229
  · exact R34231
  · exact R34233
  · exact R34235
  · exact R34237
  · exact R34239
  · exact R34241
  · exact R34243
  · exact R34245
  · exact R34247
  · exact R34249
  · exact R34251
  · exact R34253
  · exact R34255
  · exact R34257
  · exact R34259
  · exact R34261
  · exact R34263
  · exact R34265
  · exact R34267
  · exact R34269
  · exact R34271
  · exact R34273
  · exact R34275
  · exact R34277
  · exact R34279
  · exact R34281
  · exact R34283
  · exact R34285
  · exact R34287
  · exact R34289
  · exact R34291
  · exact R34293
  · exact R34295
  · exact R34297
  · exact R34299
  · exact R34301
  · exact R34303
  · exact R34305
  · exact R34307
  · exact R34309
  · exact R34311
  · exact R34313
  · exact R34315
  · exact R34317
  · exact R34319
  · exact R34321
  · exact R34323
  · exact R34325
  · exact R34327
  · exact R34329
  · exact R34331
  · exact R34333
  · exact R34335
  · exact R34337
  · exact R34339
  · exact R34341
  · exact R34343
  · exact R34345
  · exact R34347
  · exact R34349
  · exact R34351
  · exact R34353
  · exact R34355
  · exact R34357
  · exact R34359
  · exact R34361
  · exact R34363
  · exact R34365
  · exact R34367
  · exact R34369
  · exact R34371
  · exact R34373
  · exact R34375
  · exact R34377
  · exact R34379
  · exact R34381
  · exact R34383
  · exact R34385
  · exact R34387
  · exact R34389
  · exact R34391
  · exact R34393
  · exact R34395
  · exact R34397
  · exact R34399
  · exact R34401
  · exact R34403
  · exact R34405
  · exact R34407
  · exact R34409
  · exact R34411
  · exact R34413
  · exact R34415
  · exact R34417
  · exact R34419
  · exact R34421
  · exact R34423
  · exact R34425
  · exact R34427
  · exact R34429
  · exact R34431
  · exact R34433
  · exact R34435
  · exact R34437
  · exact R34439
  · exact R34441
  · exact R34443
  · exact R34445
  · exact R34447
  · exact R34449
  · exact R34451
  · exact R34453
  · exact R34455
  · exact R34457
  · exact R34459
  · exact R34461
  · exact R34463
  · exact R34465
  · exact R34467
  · exact R34469
  · exact R34471
  · exact R34473
  · exact R34475
  · exact R34477
  · exact R34479
  · exact R34481
  · exact R34483
  · exact R34485
  · exact R34487
  · exact R34489
  · exact R34491
  · exact R34493
  · exact R34495
  · exact R34497
  · exact R34499
  · exact R34501
  · exact R34503
  · exact R34505
  · exact R34507
  · exact R34509
  · exact R34511
  · exact R34513
  · exact R34515
  · exact R34517
  · exact R34519
  · exact R34521
  · exact R34523
  · exact R34525
  · exact R34527
  · exact R34529
  · exact R34531
  · exact R34533
  · exact R34535
  · exact R34537
  · exact R34539
  · exact R34541
  · exact R34543
  · exact R34545
  · exact R34547
  · exact R34549
  · exact R34551
  · exact R34553
  · exact R34555
  · exact R34557
  · exact R34559
  · exact R34561
  · exact R34563
  · exact R34565
  · exact R34567
  · exact R34569
  · exact R34571
  · exact R34573
  · exact R34575
  · exact R34577
  · exact R34579
  · exact R34581
  · exact R34583
  · exact R34585
  · exact R34587
  · exact R34589
  · exact R34591
  · exact R34593
  · exact R34595
  · exact R34597
  · exact R34599
  · exact R34601
  · exact R34603
  · exact R34605
  · exact R34607
  · exact R34609
  · exact R34611
  · exact R34613
  · exact R34615
  · exact R34617
  · exact R34619
  · exact R34621
  · exact R34623
  · exact R34625
  · exact R34627
  · exact R34629
  · exact R34631
  · exact R34633
  · exact R34635
  · exact R34637
  · exact R34639
  · exact R34641
  · exact R34643
  · exact R34645
  · exact R34647
  · exact R34649
  · exact R34651
  · exact R34653
  · exact R34655
  · exact R34657
  · exact R34659
  · exact R34661
  · exact R34663
  · exact R34665
  · exact R34667
  · exact R34669
  · exact R34671
  · exact R34673
  · exact R34675
  · exact R34677
  · exact R34679
  · exact R34681
  · exact R34683
  · exact R34685
  · exact R34687
  · exact R34689
  · exact R34691
  · exact R34693
  · exact R34695
  · exact R34697
  · exact R34699
  · exact R34701
  · exact R34703
  · exact R34705
  · exact R34707
  · exact R34709
  · exact R34711
  · exact R34713
  · exact R34715
  · exact R34717
  · exact R34719
  · exact R34721
  · exact R34723
  · exact R34725
  · exact R34727
  · exact R34729
  · exact R34731
  · exact R34733
  · exact R34735
  · exact R34737
  · exact R34739
  · exact R34741
  · exact R34743
  · exact R34745
  · exact R34747
  · exact R34749
  · exact R34751
  · exact R34753
  · exact R34755
  · exact R34757
  · exact R34759
  · exact R34761
  · exact R34763
  · exact R34765
  · exact R34767
  · exact R34769
  · exact R34771
  · exact R34773
  · exact R34775
  · exact R34777
  · exact R34779
  · exact R34781
  · exact R34783
  · exact R34785
  · exact R34787
  · exact R34789
  · exact R34791
  · exact R34793
  · exact R34795
  · exact R34797
  · exact R34799
  · exact R34801
  · exact R34803
  · exact R34805
  · exact R34807
  · exact R34809
  · exact R34811
  · exact R34813
  · exact R34815
  · exact R34817
  · exact R34819
  · exact R34821
  · exact R34823
  · exact R34825
  · exact R34827
  · exact R34829
  · exact R34831
  · exact R34833
  · exact R34835
  · exact R34837
  · exact R34839
  · exact R34841
  · exact R34843
  · exact R34845
  · exact R34847
  · exact R34849
  · exact R34851
  · exact R34853
  · exact R34855
  · exact R34857
  · exact R34859
  · exact R34861
  · exact R34863
  · exact R34865
  · exact R34867
  · exact R34869
  · exact R34871
  · exact R34873
  · exact R34875
  · exact R34877
  · exact R34879
  · exact R34881
  · exact R34883
  · exact R34885
  · exact R34887
  · exact R34889
  · exact R34891
  · exact R34893
  · exact R34895
  · exact R34897
  · exact R34899
  · exact R34901
  · exact R34903
  · exact R34905
  · exact R34907
  · exact R34909
  · exact R34911
  · exact R34913
  · exact R34915
  · exact R34917
  · exact R34919
  · exact R34921
  · exact R34923
  · exact R34925
  · exact R34927
  · exact R34929
  · exact R34931
  · exact R34933
  · exact R34935
  · exact R34937
  · exact R34939
  · exact R34941
  · exact R34943
  · exact R34945
  · exact R34947
  · exact R34949
  · exact R34951
  · exact R34953
  · exact R34955
  · exact R34957
  · exact R34959
  · exact R34961
  · exact R34963
  · exact R34965
  · exact R34967
  · exact R34969
  · exact R34971
  · exact R34973
  · exact R34975
  · exact R34977
  · exact R34979
  · exact R34981
  · exact R34983
  · exact R34985
  · exact R34987
  · exact R34989
  · exact R34991
  · exact R34993
  · exact R34995
  · exact R34997
  · exact R34999
  · exact R35001
  · exact R35003
  · exact R35005
  · exact R35007
  · exact R35009
  · exact R35011
  · exact R35013
  · exact R35015
  · exact R35017
  · exact R35019
  · exact R35021
  · exact R35023
  · exact R35025
  · exact R35027
  · exact R35029
  · exact R35031
  · exact R35033
  · exact R35035
  · exact R35037
  · exact R35039
  · exact R35041
  · exact R35043
  · exact R35045
  · exact R35047
  · exact R35049
  · exact R35051
  · exact R35053
  · exact R35055
  · exact R35057
  · exact R35059
  · exact R35061
  · exact R35063
  · exact R35065
  · exact R35067
  · exact R35069
  · exact R35071
  · exact R35073
  · exact R35075
  · exact R35077
  · exact R35079
  · exact R35081
  · exact R35083
  · exact R35085
  · exact R35087
  · exact R35089
  · exact R35091
  · exact R35093
  · exact R35095
  · exact R35097
  · exact R35099
  · exact R35101
  · exact R35103
  · exact R35105
  · exact R35107
  · exact R35109
  · exact R35111
  · exact R35113
  · exact R35115

theorem solution (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 35115) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by
  rcases Nat.lt_or_ge m 31115 with hlo | hlo
  · exact syracuse_reaches_one_below_31115 m hm hodd (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := by obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
  rcases Nat.lt_or_ge j 16257 with h0 | h0
  · exact C0 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 16957 with h1 | h1
  · exact C1 j (by omega) (by omega)
  exact C2 j (by omega) (by omega)
