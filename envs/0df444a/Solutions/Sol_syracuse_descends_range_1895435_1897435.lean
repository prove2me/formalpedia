-- Prove2me | solution 1 for syracuse_descends_range_1895435_1897435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:46:45.790489+00:00
-- url     : https://prove2.me/submissions/2606222d-6655-4edf-b41e-481e805bff25

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

theorem B2132365 : Blo 1895435 2132365 := bbase (se 3 (by rfl) ⟨399818, by rfl⟩ : syracuseStep 2132365 = 799637) (by norm_num)
theorem B2843153 : Blo 1895435 2843153 := bstep (se 2 (by rfl) ⟨1066182, by rfl⟩ : syracuseStep 2843153 = 2132365) B2132365
theorem B1895435 : Blo 1895435 1895435 := bstep (se 1 (by rfl) ⟨1421576, by rfl⟩ : syracuseStep 1895435 = 2843153) B2843153
theorem B6397109 : Blo 1895435 6397109 := bbase (se 5 (by rfl) ⟨299864, by rfl⟩ : syracuseStep 6397109 = 599729) (by norm_num)
theorem B4264739 : Blo 1895435 4264739 := bstep (se 1 (by rfl) ⟨3198554, by rfl⟩ : syracuseStep 4264739 = 6397109) B6397109
theorem B2843159 : Blo 1895435 2843159 := bstep (se 1 (by rfl) ⟨2132369, by rfl⟩ : syracuseStep 2843159 = 4264739) B4264739
theorem B1895439 : Blo 1895435 1895439 := bstep (se 1 (by rfl) ⟨1421579, by rfl⟩ : syracuseStep 1895439 = 2843159) B2843159
theorem B2843165 : Blo 1895435 2843165 := bbase (se 3 (by rfl) ⟨533093, by rfl⟩ : syracuseStep 2843165 = 1066187) (by norm_num)
theorem B1895443 : Blo 1895435 1895443 := bstep (se 1 (by rfl) ⟨1421582, by rfl⟩ : syracuseStep 1895443 = 2843165) B2843165
theorem B4264757 : Blo 1895435 4264757 := bbase (se 5 (by rfl) ⟨199910, by rfl⟩ : syracuseStep 4264757 = 399821) (by norm_num)
theorem B2843171 : Blo 1895435 2843171 := bstep (se 1 (by rfl) ⟨2132378, by rfl⟩ : syracuseStep 2843171 = 4264757) B4264757
theorem B1895447 : Blo 1895435 1895447 := bstep (se 1 (by rfl) ⟨1421585, by rfl⟩ : syracuseStep 1895447 = 2843171) B2843171
theorem B1921313 : Blo 1895435 1921313 := bbase (se 2 (by rfl) ⟨720492, by rfl⟩ : syracuseStep 1921313 = 1440985) (by norm_num)
theorem B5123501 : Blo 1895435 5123501 := bstep (se 3 (by rfl) ⟨960656, by rfl⟩ : syracuseStep 5123501 = 1921313) B1921313
theorem B3415667 : Blo 1895435 3415667 := bstep (se 1 (by rfl) ⟨2561750, by rfl⟩ : syracuseStep 3415667 = 5123501) B5123501
theorem B9108445 : Blo 1895435 9108445 := bstep (se 3 (by rfl) ⟨1707833, by rfl⟩ : syracuseStep 9108445 = 3415667) B3415667
theorem B12144593 : Blo 1895435 12144593 := bstep (se 2 (by rfl) ⟨4554222, by rfl⟩ : syracuseStep 12144593 = 9108445) B9108445
theorem B8096395 : Blo 1895435 8096395 := bstep (se 1 (by rfl) ⟨6072296, by rfl⟩ : syracuseStep 8096395 = 12144593) B12144593
theorem B10795193 : Blo 1895435 10795193 := bstep (se 2 (by rfl) ⟨4048197, by rfl⟩ : syracuseStep 10795193 = 8096395) B8096395
theorem B7196795 : Blo 1895435 7196795 := bstep (se 1 (by rfl) ⟨5397596, by rfl⟩ : syracuseStep 7196795 = 10795193) B10795193
theorem B4797863 : Blo 1895435 4797863 := bstep (se 1 (by rfl) ⟨3598397, by rfl⟩ : syracuseStep 4797863 = 7196795) B7196795
theorem B3198575 : Blo 1895435 3198575 := bstep (se 1 (by rfl) ⟨2398931, by rfl⟩ : syracuseStep 3198575 = 4797863) B4797863
theorem B2132383 : Blo 1895435 2132383 := bstep (se 1 (by rfl) ⟨1599287, by rfl⟩ : syracuseStep 2132383 = 3198575) B3198575
theorem B2843177 : Blo 1895435 2843177 := bstep (se 2 (by rfl) ⟨1066191, by rfl⟩ : syracuseStep 2843177 = 2132383) B2132383
theorem B1895451 : Blo 1895435 1895451 := bstep (se 1 (by rfl) ⟨1421588, by rfl⟩ : syracuseStep 1895451 = 2843177) B2843177
theorem B16413749 : Blo 1895435 16413749 := bbase (se 5 (by rfl) ⟨769394, by rfl⟩ : syracuseStep 16413749 = 1538789) (by norm_num)
theorem B10942499 : Blo 1895435 10942499 := bstep (se 1 (by rfl) ⟨8206874, by rfl⟩ : syracuseStep 10942499 = 16413749) B16413749
theorem B29179997 : Blo 1895435 29179997 := bstep (se 3 (by rfl) ⟨5471249, by rfl⟩ : syracuseStep 29179997 = 10942499) B10942499
theorem B19453331 : Blo 1895435 19453331 := bstep (se 1 (by rfl) ⟨14589998, by rfl⟩ : syracuseStep 19453331 = 29179997) B29179997
theorem B51875549 : Blo 1895435 51875549 := bstep (se 3 (by rfl) ⟨9726665, by rfl⟩ : syracuseStep 51875549 = 19453331) B19453331
theorem B34583699 : Blo 1895435 34583699 := bstep (se 1 (by rfl) ⟨25937774, by rfl⟩ : syracuseStep 34583699 = 51875549) B51875549
theorem B23055799 : Blo 1895435 23055799 := bstep (se 1 (by rfl) ⟨17291849, by rfl⟩ : syracuseStep 23055799 = 34583699) B34583699
theorem B30741065 : Blo 1895435 30741065 := bstep (se 2 (by rfl) ⟨11527899, by rfl⟩ : syracuseStep 30741065 = 23055799) B23055799
theorem B20494043 : Blo 1895435 20494043 := bstep (se 1 (by rfl) ⟨15370532, by rfl⟩ : syracuseStep 20494043 = 30741065) B30741065
theorem B13662695 : Blo 1895435 13662695 := bstep (se 1 (by rfl) ⟨10247021, by rfl⟩ : syracuseStep 13662695 = 20494043) B20494043
theorem B9108463 : Blo 1895435 9108463 := bstep (se 1 (by rfl) ⟨6831347, by rfl⟩ : syracuseStep 9108463 = 13662695) B13662695
theorem B12144617 : Blo 1895435 12144617 := bstep (se 2 (by rfl) ⟨4554231, by rfl⟩ : syracuseStep 12144617 = 9108463) B9108463
theorem B8096411 : Blo 1895435 8096411 := bstep (se 1 (by rfl) ⟨6072308, by rfl⟩ : syracuseStep 8096411 = 12144617) B12144617
theorem B5397607 : Blo 1895435 5397607 := bstep (se 1 (by rfl) ⟨4048205, by rfl⟩ : syracuseStep 5397607 = 8096411) B8096411
theorem B7196809 : Blo 1895435 7196809 := bstep (se 2 (by rfl) ⟨2698803, by rfl⟩ : syracuseStep 7196809 = 5397607) B5397607
theorem B9595745 : Blo 1895435 9595745 := bstep (se 2 (by rfl) ⟨3598404, by rfl⟩ : syracuseStep 9595745 = 7196809) B7196809
theorem B6397163 : Blo 1895435 6397163 := bstep (se 1 (by rfl) ⟨4797872, by rfl⟩ : syracuseStep 6397163 = 9595745) B9595745
theorem B4264775 : Blo 1895435 4264775 := bstep (se 1 (by rfl) ⟨3198581, by rfl⟩ : syracuseStep 4264775 = 6397163) B6397163
theorem B2843183 : Blo 1895435 2843183 := bstep (se 1 (by rfl) ⟨2132387, by rfl⟩ : syracuseStep 2843183 = 4264775) B4264775
theorem B1895455 : Blo 1895435 1895455 := bstep (se 1 (by rfl) ⟨1421591, by rfl⟩ : syracuseStep 1895455 = 2843183) B2843183
theorem B2843189 : Blo 1895435 2843189 := bbase (se 5 (by rfl) ⟨133274, by rfl⟩ : syracuseStep 2843189 = 266549) (by norm_num)
theorem B1895459 : Blo 1895435 1895459 := bstep (se 1 (by rfl) ⟨1421594, by rfl⟩ : syracuseStep 1895459 = 2843189) B2843189
theorem B4797893 : Blo 1895435 4797893 := bbase (se 4 (by rfl) ⟨449802, by rfl⟩ : syracuseStep 4797893 = 899605) (by norm_num)
theorem B3198595 : Blo 1895435 3198595 := bstep (se 1 (by rfl) ⟨2398946, by rfl⟩ : syracuseStep 3198595 = 4797893) B4797893
theorem B4264793 : Blo 1895435 4264793 := bstep (se 2 (by rfl) ⟨1599297, by rfl⟩ : syracuseStep 4264793 = 3198595) B3198595
theorem B2843195 : Blo 1895435 2843195 := bstep (se 1 (by rfl) ⟨2132396, by rfl⟩ : syracuseStep 2843195 = 4264793) B4264793
theorem B1895463 : Blo 1895435 1895463 := bstep (se 1 (by rfl) ⟨1421597, by rfl⟩ : syracuseStep 1895463 = 2843195) B2843195
theorem B2132401 : Blo 1895435 2132401 := bbase (se 2 (by rfl) ⟨799650, by rfl⟩ : syracuseStep 2132401 = 1599301) (by norm_num)
theorem B2843201 : Blo 1895435 2843201 := bstep (se 2 (by rfl) ⟨1066200, by rfl⟩ : syracuseStep 2843201 = 2132401) B2132401
theorem B1895467 : Blo 1895435 1895467 := bstep (se 1 (by rfl) ⟨1421600, by rfl⟩ : syracuseStep 1895467 = 2843201) B2843201
theorem B5397653 : Blo 1895435 5397653 := bbase (se 6 (by rfl) ⟨126507, by rfl⟩ : syracuseStep 5397653 = 253015) (by norm_num)
theorem B3598435 : Blo 1895435 3598435 := bstep (se 1 (by rfl) ⟨2698826, by rfl⟩ : syracuseStep 3598435 = 5397653) B5397653
theorem B4797913 : Blo 1895435 4797913 := bstep (se 2 (by rfl) ⟨1799217, by rfl⟩ : syracuseStep 4797913 = 3598435) B3598435
theorem B6397217 : Blo 1895435 6397217 := bstep (se 2 (by rfl) ⟨2398956, by rfl⟩ : syracuseStep 6397217 = 4797913) B4797913
theorem B4264811 : Blo 1895435 4264811 := bstep (se 1 (by rfl) ⟨3198608, by rfl⟩ : syracuseStep 4264811 = 6397217) B6397217
theorem B2843207 : Blo 1895435 2843207 := bstep (se 1 (by rfl) ⟨2132405, by rfl⟩ : syracuseStep 2843207 = 4264811) B4264811
theorem B1895471 : Blo 1895435 1895471 := bstep (se 1 (by rfl) ⟨1421603, by rfl⟩ : syracuseStep 1895471 = 2843207) B2843207
theorem B2843213 : Blo 1895435 2843213 := bbase (se 3 (by rfl) ⟨533102, by rfl⟩ : syracuseStep 2843213 = 1066205) (by norm_num)
theorem B1895475 : Blo 1895435 1895475 := bstep (se 1 (by rfl) ⟨1421606, by rfl⟩ : syracuseStep 1895475 = 2843213) B2843213
theorem B4264829 : Blo 1895435 4264829 := bbase (se 3 (by rfl) ⟨799655, by rfl⟩ : syracuseStep 4264829 = 1599311) (by norm_num)
theorem B2843219 : Blo 1895435 2843219 := bstep (se 1 (by rfl) ⟨2132414, by rfl⟩ : syracuseStep 2843219 = 4264829) B4264829
theorem B1895479 : Blo 1895435 1895479 := bstep (se 1 (by rfl) ⟨1421609, by rfl⟩ : syracuseStep 1895479 = 2843219) B2843219
theorem B3198629 : Blo 1895435 3198629 := bbase (se 4 (by rfl) ⟨299871, by rfl⟩ : syracuseStep 3198629 = 599743) (by norm_num)
theorem B2132419 : Blo 1895435 2132419 := bstep (se 1 (by rfl) ⟨1599314, by rfl⟩ : syracuseStep 2132419 = 3198629) B3198629
theorem B2843225 : Blo 1895435 2843225 := bstep (se 2 (by rfl) ⟨1066209, by rfl⟩ : syracuseStep 2843225 = 2132419) B2132419
theorem B1895483 : Blo 1895435 1895483 := bstep (se 1 (by rfl) ⟨1421612, by rfl⟩ : syracuseStep 1895483 = 2843225) B2843225
theorem B2024137 : Blo 1895435 2024137 := bbase (se 2 (by rfl) ⟨759051, by rfl⟩ : syracuseStep 2024137 = 1518103) (by norm_num)
theorem B2698849 : Blo 1895435 2698849 := bstep (se 2 (by rfl) ⟨1012068, by rfl⟩ : syracuseStep 2698849 = 2024137) B2024137
theorem B14393861 : Blo 1895435 14393861 := bstep (se 4 (by rfl) ⟨1349424, by rfl⟩ : syracuseStep 14393861 = 2698849) B2698849
theorem B9595907 : Blo 1895435 9595907 := bstep (se 1 (by rfl) ⟨7196930, by rfl⟩ : syracuseStep 9595907 = 14393861) B14393861
theorem B6397271 : Blo 1895435 6397271 := bstep (se 1 (by rfl) ⟨4797953, by rfl⟩ : syracuseStep 6397271 = 9595907) B9595907
theorem B4264847 : Blo 1895435 4264847 := bstep (se 1 (by rfl) ⟨3198635, by rfl⟩ : syracuseStep 4264847 = 6397271) B6397271
theorem B2843231 : Blo 1895435 2843231 := bstep (se 1 (by rfl) ⟨2132423, by rfl⟩ : syracuseStep 2843231 = 4264847) B4264847
theorem B1895487 : Blo 1895435 1895487 := bstep (se 1 (by rfl) ⟨1421615, by rfl⟩ : syracuseStep 1895487 = 2843231) B2843231
theorem B2843237 : Blo 1895435 2843237 := bbase (se 4 (by rfl) ⟨266553, by rfl⟩ : syracuseStep 2843237 = 533107) (by norm_num)
theorem B1895491 : Blo 1895435 1895491 := bstep (se 1 (by rfl) ⟨1421618, by rfl⟩ : syracuseStep 1895491 = 2843237) B2843237
theorem B2698861 : Blo 1895435 2698861 := bbase (se 3 (by rfl) ⟨506036, by rfl⟩ : syracuseStep 2698861 = 1012073) (by norm_num)
theorem B3598481 : Blo 1895435 3598481 := bstep (se 2 (by rfl) ⟨1349430, by rfl⟩ : syracuseStep 3598481 = 2698861) B2698861
theorem B2398987 : Blo 1895435 2398987 := bstep (se 1 (by rfl) ⟨1799240, by rfl⟩ : syracuseStep 2398987 = 3598481) B3598481
theorem B3198649 : Blo 1895435 3198649 := bstep (se 2 (by rfl) ⟨1199493, by rfl⟩ : syracuseStep 3198649 = 2398987) B2398987
theorem B4264865 : Blo 1895435 4264865 := bstep (se 2 (by rfl) ⟨1599324, by rfl⟩ : syracuseStep 4264865 = 3198649) B3198649
theorem B2843243 : Blo 1895435 2843243 := bstep (se 1 (by rfl) ⟨2132432, by rfl⟩ : syracuseStep 2843243 = 4264865) B4264865
theorem B1895495 : Blo 1895435 1895495 := bstep (se 1 (by rfl) ⟨1421621, by rfl⟩ : syracuseStep 1895495 = 2843243) B2843243
theorem B2132437 : Blo 1895435 2132437 := bbase (se 7 (by rfl) ⟨24989, by rfl⟩ : syracuseStep 2132437 = 49979) (by norm_num)
theorem B2843249 : Blo 1895435 2843249 := bstep (se 2 (by rfl) ⟨1066218, by rfl⟩ : syracuseStep 2843249 = 2132437) B2132437
theorem B1895499 : Blo 1895435 1895499 := bstep (se 1 (by rfl) ⟨1421624, by rfl⟩ : syracuseStep 1895499 = 2843249) B2843249
theorem B2398997 : Blo 1895435 2398997 := bbase (se 6 (by rfl) ⟨56226, by rfl⟩ : syracuseStep 2398997 = 112453) (by norm_num)
theorem B6397325 : Blo 1895435 6397325 := bstep (se 3 (by rfl) ⟨1199498, by rfl⟩ : syracuseStep 6397325 = 2398997) B2398997
theorem B4264883 : Blo 1895435 4264883 := bstep (se 1 (by rfl) ⟨3198662, by rfl⟩ : syracuseStep 4264883 = 6397325) B6397325
theorem B2843255 : Blo 1895435 2843255 := bstep (se 1 (by rfl) ⟨2132441, by rfl⟩ : syracuseStep 2843255 = 4264883) B4264883
theorem B1895503 : Blo 1895435 1895503 := bstep (se 1 (by rfl) ⟨1421627, by rfl⟩ : syracuseStep 1895503 = 2843255) B2843255
theorem B2843261 : Blo 1895435 2843261 := bbase (se 3 (by rfl) ⟨533111, by rfl⟩ : syracuseStep 2843261 = 1066223) (by norm_num)
theorem B1895507 : Blo 1895435 1895507 := bstep (se 1 (by rfl) ⟨1421630, by rfl⟩ : syracuseStep 1895507 = 2843261) B2843261
theorem B4264901 : Blo 1895435 4264901 := bbase (se 4 (by rfl) ⟨399834, by rfl⟩ : syracuseStep 4264901 = 799669) (by norm_num)
theorem B2843267 : Blo 1895435 2843267 := bstep (se 1 (by rfl) ⟨2132450, by rfl⟩ : syracuseStep 2843267 = 4264901) B4264901
theorem B1895511 : Blo 1895435 1895511 := bstep (se 1 (by rfl) ⟨1421633, by rfl⟩ : syracuseStep 1895511 = 2843267) B2843267
theorem B2051785 : Blo 1895435 2051785 := bbase (se 2 (by rfl) ⟨769419, by rfl⟩ : syracuseStep 2051785 = 1538839) (by norm_num)
theorem B2735713 : Blo 1895435 2735713 := bstep (se 2 (by rfl) ⟨1025892, by rfl⟩ : syracuseStep 2735713 = 2051785) B2051785
theorem B14590469 : Blo 1895435 14590469 := bstep (se 4 (by rfl) ⟨1367856, by rfl⟩ : syracuseStep 14590469 = 2735713) B2735713
theorem B9726979 : Blo 1895435 9726979 := bstep (se 1 (by rfl) ⟨7295234, by rfl⟩ : syracuseStep 9726979 = 14590469) B14590469
theorem B12969305 : Blo 1895435 12969305 := bstep (se 2 (by rfl) ⟨4863489, by rfl⟩ : syracuseStep 12969305 = 9726979) B9726979
theorem B8646203 : Blo 1895435 8646203 := bstep (se 1 (by rfl) ⟨6484652, by rfl⟩ : syracuseStep 8646203 = 12969305) B12969305
theorem B5764135 : Blo 1895435 5764135 := bstep (se 1 (by rfl) ⟨4323101, by rfl⟩ : syracuseStep 5764135 = 8646203) B8646203
theorem B7685513 : Blo 1895435 7685513 := bstep (se 2 (by rfl) ⟨2882067, by rfl⟩ : syracuseStep 7685513 = 5764135) B5764135
theorem B5123675 : Blo 1895435 5123675 := bstep (se 1 (by rfl) ⟨3842756, by rfl⟩ : syracuseStep 5123675 = 7685513) B7685513
theorem B3415783 : Blo 1895435 3415783 := bstep (se 1 (by rfl) ⟨2561837, by rfl⟩ : syracuseStep 3415783 = 5123675) B5123675
theorem B4554377 : Blo 1895435 4554377 := bstep (se 2 (by rfl) ⟨1707891, by rfl⟩ : syracuseStep 4554377 = 3415783) B3415783
theorem B3036251 : Blo 1895435 3036251 := bstep (se 1 (by rfl) ⟨2277188, by rfl⟩ : syracuseStep 3036251 = 4554377) B4554377
theorem B8096669 : Blo 1895435 8096669 := bstep (se 3 (by rfl) ⟨1518125, by rfl⟩ : syracuseStep 8096669 = 3036251) B3036251
theorem B5397779 : Blo 1895435 5397779 := bstep (se 1 (by rfl) ⟨4048334, by rfl⟩ : syracuseStep 5397779 = 8096669) B8096669
theorem B3598519 : Blo 1895435 3598519 := bstep (se 1 (by rfl) ⟨2698889, by rfl⟩ : syracuseStep 3598519 = 5397779) B5397779
theorem B4798025 : Blo 1895435 4798025 := bstep (se 2 (by rfl) ⟨1799259, by rfl⟩ : syracuseStep 4798025 = 3598519) B3598519
theorem B3198683 : Blo 1895435 3198683 := bstep (se 1 (by rfl) ⟨2399012, by rfl⟩ : syracuseStep 3198683 = 4798025) B4798025
theorem B2132455 : Blo 1895435 2132455 := bstep (se 1 (by rfl) ⟨1599341, by rfl⟩ : syracuseStep 2132455 = 3198683) B3198683
theorem B2843273 : Blo 1895435 2843273 := bstep (se 2 (by rfl) ⟨1066227, by rfl⟩ : syracuseStep 2843273 = 2132455) B2132455
theorem B1895515 : Blo 1895435 1895515 := bstep (se 1 (by rfl) ⟨1421636, by rfl⟩ : syracuseStep 1895515 = 2843273) B2843273
theorem B9596069 : Blo 1895435 9596069 := bbase (se 4 (by rfl) ⟨899631, by rfl⟩ : syracuseStep 9596069 = 1799263) (by norm_num)
theorem B6397379 : Blo 1895435 6397379 := bstep (se 1 (by rfl) ⟨4798034, by rfl⟩ : syracuseStep 6397379 = 9596069) B9596069
theorem B4264919 : Blo 1895435 4264919 := bstep (se 1 (by rfl) ⟨3198689, by rfl⟩ : syracuseStep 4264919 = 6397379) B6397379
theorem B2843279 : Blo 1895435 2843279 := bstep (se 1 (by rfl) ⟨2132459, by rfl⟩ : syracuseStep 2843279 = 4264919) B4264919
theorem B1895519 : Blo 1895435 1895519 := bstep (se 1 (by rfl) ⟨1421639, by rfl⟩ : syracuseStep 1895519 = 2843279) B2843279
theorem B2843285 : Blo 1895435 2843285 := bbase (se 6 (by rfl) ⟨66639, by rfl⟩ : syracuseStep 2843285 = 133279) (by norm_num)
theorem B1895523 : Blo 1895435 1895523 := bstep (se 1 (by rfl) ⟨1421642, by rfl⟩ : syracuseStep 1895523 = 2843285) B2843285
theorem B8207189 : Blo 1895435 8207189 := bbase (se 9 (by rfl) ⟨24044, by rfl⟩ : syracuseStep 8207189 = 48089) (by norm_num)
theorem B5471459 : Blo 1895435 5471459 := bstep (se 1 (by rfl) ⟨4103594, by rfl⟩ : syracuseStep 5471459 = 8207189) B8207189
theorem B3647639 : Blo 1895435 3647639 := bstep (se 1 (by rfl) ⟨2735729, by rfl⟩ : syracuseStep 3647639 = 5471459) B5471459
theorem B9727037 : Blo 1895435 9727037 := bstep (se 3 (by rfl) ⟨1823819, by rfl⟩ : syracuseStep 9727037 = 3647639) B3647639
theorem B6484691 : Blo 1895435 6484691 := bstep (se 1 (by rfl) ⟨4863518, by rfl⟩ : syracuseStep 6484691 = 9727037) B9727037
theorem B4323127 : Blo 1895435 4323127 := bstep (se 1 (by rfl) ⟨3242345, by rfl⟩ : syracuseStep 4323127 = 6484691) B6484691
theorem B5764169 : Blo 1895435 5764169 := bstep (se 2 (by rfl) ⟨2161563, by rfl⟩ : syracuseStep 5764169 = 4323127) B4323127
theorem B15371117 : Blo 1895435 15371117 := bstep (se 3 (by rfl) ⟨2882084, by rfl⟩ : syracuseStep 15371117 = 5764169) B5764169
theorem B10247411 : Blo 1895435 10247411 := bstep (se 1 (by rfl) ⟨7685558, by rfl⟩ : syracuseStep 10247411 = 15371117) B15371117
theorem B27326429 : Blo 1895435 27326429 := bstep (se 3 (by rfl) ⟨5123705, by rfl⟩ : syracuseStep 27326429 = 10247411) B10247411
theorem B18217619 : Blo 1895435 18217619 := bstep (se 1 (by rfl) ⟨13663214, by rfl⟩ : syracuseStep 18217619 = 27326429) B27326429
theorem B12145079 : Blo 1895435 12145079 := bstep (se 1 (by rfl) ⟨9108809, by rfl⟩ : syracuseStep 12145079 = 18217619) B18217619
theorem B8096719 : Blo 1895435 8096719 := bstep (se 1 (by rfl) ⟨6072539, by rfl⟩ : syracuseStep 8096719 = 12145079) B12145079
theorem B10795625 : Blo 1895435 10795625 := bstep (se 2 (by rfl) ⟨4048359, by rfl⟩ : syracuseStep 10795625 = 8096719) B8096719
theorem B7197083 : Blo 1895435 7197083 := bstep (se 1 (by rfl) ⟨5397812, by rfl⟩ : syracuseStep 7197083 = 10795625) B10795625
theorem B4798055 : Blo 1895435 4798055 := bstep (se 1 (by rfl) ⟨3598541, by rfl⟩ : syracuseStep 4798055 = 7197083) B7197083
theorem B3198703 : Blo 1895435 3198703 := bstep (se 1 (by rfl) ⟨2399027, by rfl⟩ : syracuseStep 3198703 = 4798055) B4798055
theorem B4264937 : Blo 1895435 4264937 := bstep (se 2 (by rfl) ⟨1599351, by rfl⟩ : syracuseStep 4264937 = 3198703) B3198703
theorem B2843291 : Blo 1895435 2843291 := bstep (se 1 (by rfl) ⟨2132468, by rfl⟩ : syracuseStep 2843291 = 4264937) B4264937
theorem B1895527 : Blo 1895435 1895527 := bstep (se 1 (by rfl) ⟨1421645, by rfl⟩ : syracuseStep 1895527 = 2843291) B2843291
theorem B2132473 : Blo 1895435 2132473 := bbase (se 2 (by rfl) ⟨799677, by rfl⟩ : syracuseStep 2132473 = 1599355) (by norm_num)
theorem B2843297 : Blo 1895435 2843297 := bstep (se 2 (by rfl) ⟨1066236, by rfl⟩ : syracuseStep 2843297 = 2132473) B2132473
theorem B1895531 : Blo 1895435 1895531 := bstep (se 1 (by rfl) ⟨1421648, by rfl⟩ : syracuseStep 1895531 = 2843297) B2843297
theorem B6072565 : Blo 1895435 6072565 := bbase (se 5 (by rfl) ⟨284651, by rfl⟩ : syracuseStep 6072565 = 569303) (by norm_num)
theorem B8096753 : Blo 1895435 8096753 := bstep (se 2 (by rfl) ⟨3036282, by rfl⟩ : syracuseStep 8096753 = 6072565) B6072565
theorem B5397835 : Blo 1895435 5397835 := bstep (se 1 (by rfl) ⟨4048376, by rfl⟩ : syracuseStep 5397835 = 8096753) B8096753
theorem B7197113 : Blo 1895435 7197113 := bstep (se 2 (by rfl) ⟨2698917, by rfl⟩ : syracuseStep 7197113 = 5397835) B5397835
theorem B4798075 : Blo 1895435 4798075 := bstep (se 1 (by rfl) ⟨3598556, by rfl⟩ : syracuseStep 4798075 = 7197113) B7197113
theorem B6397433 : Blo 1895435 6397433 := bstep (se 2 (by rfl) ⟨2399037, by rfl⟩ : syracuseStep 6397433 = 4798075) B4798075
theorem B4264955 : Blo 1895435 4264955 := bstep (se 1 (by rfl) ⟨3198716, by rfl⟩ : syracuseStep 4264955 = 6397433) B6397433
theorem B2843303 : Blo 1895435 2843303 := bstep (se 1 (by rfl) ⟨2132477, by rfl⟩ : syracuseStep 2843303 = 4264955) B4264955
theorem B1895535 : Blo 1895435 1895535 := bstep (se 1 (by rfl) ⟨1421651, by rfl⟩ : syracuseStep 1895535 = 2843303) B2843303
theorem B2843309 : Blo 1895435 2843309 := bbase (se 3 (by rfl) ⟨533120, by rfl⟩ : syracuseStep 2843309 = 1066241) (by norm_num)
theorem B1895539 : Blo 1895435 1895539 := bstep (se 1 (by rfl) ⟨1421654, by rfl⟩ : syracuseStep 1895539 = 2843309) B2843309
theorem B4264973 : Blo 1895435 4264973 := bbase (se 3 (by rfl) ⟨799682, by rfl⟩ : syracuseStep 4264973 = 1599365) (by norm_num)
theorem B2843315 : Blo 1895435 2843315 := bstep (se 1 (by rfl) ⟨2132486, by rfl⟩ : syracuseStep 2843315 = 4264973) B4264973
theorem B1895543 : Blo 1895435 1895543 := bstep (se 1 (by rfl) ⟨1421657, by rfl⟩ : syracuseStep 1895543 = 2843315) B2843315
theorem B2399053 : Blo 1895435 2399053 := bbase (se 3 (by rfl) ⟨449822, by rfl⟩ : syracuseStep 2399053 = 899645) (by norm_num)
theorem B3198737 : Blo 1895435 3198737 := bstep (se 2 (by rfl) ⟨1199526, by rfl⟩ : syracuseStep 3198737 = 2399053) B2399053
theorem B2132491 : Blo 1895435 2132491 := bstep (se 1 (by rfl) ⟨1599368, by rfl⟩ : syracuseStep 2132491 = 3198737) B3198737
theorem B2843321 : Blo 1895435 2843321 := bstep (se 2 (by rfl) ⟨1066245, by rfl⟩ : syracuseStep 2843321 = 2132491) B2132491
theorem B1895547 : Blo 1895435 1895547 := bstep (se 1 (by rfl) ⟨1421660, by rfl⟩ : syracuseStep 1895547 = 2843321) B2843321
theorem B4323181 : Blo 1895435 4323181 := bbase (se 3 (by rfl) ⟨810596, by rfl⟩ : syracuseStep 4323181 = 1621193) (by norm_num)
theorem B5764241 : Blo 1895435 5764241 := bstep (se 2 (by rfl) ⟨2161590, by rfl⟩ : syracuseStep 5764241 = 4323181) B4323181
theorem B15371309 : Blo 1895435 15371309 := bstep (se 3 (by rfl) ⟨2882120, by rfl⟩ : syracuseStep 15371309 = 5764241) B5764241
theorem B40990157 : Blo 1895435 40990157 := bstep (se 3 (by rfl) ⟨7685654, by rfl⟩ : syracuseStep 40990157 = 15371309) B15371309
theorem B27326771 : Blo 1895435 27326771 := bstep (se 1 (by rfl) ⟨20495078, by rfl⟩ : syracuseStep 27326771 = 40990157) B40990157
theorem B18217847 : Blo 1895435 18217847 := bstep (se 1 (by rfl) ⟨13663385, by rfl⟩ : syracuseStep 18217847 = 27326771) B27326771
theorem B12145231 : Blo 1895435 12145231 := bstep (se 1 (by rfl) ⟨9108923, by rfl⟩ : syracuseStep 12145231 = 18217847) B18217847
theorem B16193641 : Blo 1895435 16193641 := bstep (se 2 (by rfl) ⟨6072615, by rfl⟩ : syracuseStep 16193641 = 12145231) B12145231
theorem B21591521 : Blo 1895435 21591521 := bstep (se 2 (by rfl) ⟨8096820, by rfl⟩ : syracuseStep 21591521 = 16193641) B16193641
theorem B14394347 : Blo 1895435 14394347 := bstep (se 1 (by rfl) ⟨10795760, by rfl⟩ : syracuseStep 14394347 = 21591521) B21591521
theorem B9596231 : Blo 1895435 9596231 := bstep (se 1 (by rfl) ⟨7197173, by rfl⟩ : syracuseStep 9596231 = 14394347) B14394347
theorem B6397487 : Blo 1895435 6397487 := bstep (se 1 (by rfl) ⟨4798115, by rfl⟩ : syracuseStep 6397487 = 9596231) B9596231
theorem B4264991 : Blo 1895435 4264991 := bstep (se 1 (by rfl) ⟨3198743, by rfl⟩ : syracuseStep 4264991 = 6397487) B6397487
theorem B2843327 : Blo 1895435 2843327 := bstep (se 1 (by rfl) ⟨2132495, by rfl⟩ : syracuseStep 2843327 = 4264991) B4264991
theorem B1895551 : Blo 1895435 1895551 := bstep (se 1 (by rfl) ⟨1421663, by rfl⟩ : syracuseStep 1895551 = 2843327) B2843327
theorem B2843333 : Blo 1895435 2843333 := bbase (se 4 (by rfl) ⟨266562, by rfl⟩ : syracuseStep 2843333 = 533125) (by norm_num)
theorem B1895555 : Blo 1895435 1895555 := bstep (se 1 (by rfl) ⟨1421666, by rfl⟩ : syracuseStep 1895555 = 2843333) B2843333
theorem B3198757 : Blo 1895435 3198757 := bbase (se 4 (by rfl) ⟨299883, by rfl⟩ : syracuseStep 3198757 = 599767) (by norm_num)
theorem B4265009 : Blo 1895435 4265009 := bstep (se 2 (by rfl) ⟨1599378, by rfl⟩ : syracuseStep 4265009 = 3198757) B3198757
theorem B2843339 : Blo 1895435 2843339 := bstep (se 1 (by rfl) ⟨2132504, by rfl⟩ : syracuseStep 2843339 = 4265009) B4265009
theorem B1895559 : Blo 1895435 1895559 := bstep (se 1 (by rfl) ⟨1421669, by rfl⟩ : syracuseStep 1895559 = 2843339) B2843339
theorem B2132509 : Blo 1895435 2132509 := bbase (se 3 (by rfl) ⟨399845, by rfl⟩ : syracuseStep 2132509 = 799691) (by norm_num)
theorem B2843345 : Blo 1895435 2843345 := bstep (se 2 (by rfl) ⟨1066254, by rfl⟩ : syracuseStep 2843345 = 2132509) B2132509
theorem B1895563 : Blo 1895435 1895563 := bstep (se 1 (by rfl) ⟨1421672, by rfl⟩ : syracuseStep 1895563 = 2843345) B2843345
theorem B6397541 : Blo 1895435 6397541 := bbase (se 4 (by rfl) ⟨599769, by rfl⟩ : syracuseStep 6397541 = 1199539) (by norm_num)
theorem B4265027 : Blo 1895435 4265027 := bstep (se 1 (by rfl) ⟨3198770, by rfl⟩ : syracuseStep 4265027 = 6397541) B6397541
theorem B2843351 : Blo 1895435 2843351 := bstep (se 1 (by rfl) ⟨2132513, by rfl⟩ : syracuseStep 2843351 = 4265027) B4265027
theorem B1895567 : Blo 1895435 1895567 := bstep (se 1 (by rfl) ⟨1421675, by rfl⟩ : syracuseStep 1895567 = 2843351) B2843351
theorem B2843357 : Blo 1895435 2843357 := bbase (se 3 (by rfl) ⟨533129, by rfl⟩ : syracuseStep 2843357 = 1066259) (by norm_num)
theorem B1895571 : Blo 1895435 1895571 := bstep (se 1 (by rfl) ⟨1421678, by rfl⟩ : syracuseStep 1895571 = 2843357) B2843357
theorem B4265045 : Blo 1895435 4265045 := bbase (se 8 (by rfl) ⟨24990, by rfl⟩ : syracuseStep 4265045 = 49981) (by norm_num)
theorem B2843363 : Blo 1895435 2843363 := bstep (se 1 (by rfl) ⟨2132522, by rfl⟩ : syracuseStep 2843363 = 4265045) B4265045
theorem B1895575 : Blo 1895435 1895575 := bstep (se 1 (by rfl) ⟨1421681, by rfl⟩ : syracuseStep 1895575 = 2843363) B2843363
theorem B9109061 : Blo 1895435 9109061 := bbase (se 4 (by rfl) ⟨853974, by rfl⟩ : syracuseStep 9109061 = 1707949) (by norm_num)
theorem B6072707 : Blo 1895435 6072707 := bstep (se 1 (by rfl) ⟨4554530, by rfl⟩ : syracuseStep 6072707 = 9109061) B9109061
theorem B4048471 : Blo 1895435 4048471 := bstep (se 1 (by rfl) ⟨3036353, by rfl⟩ : syracuseStep 4048471 = 6072707) B6072707
theorem B5397961 : Blo 1895435 5397961 := bstep (se 2 (by rfl) ⟨2024235, by rfl⟩ : syracuseStep 5397961 = 4048471) B4048471
theorem B7197281 : Blo 1895435 7197281 := bstep (se 2 (by rfl) ⟨2698980, by rfl⟩ : syracuseStep 7197281 = 5397961) B5397961
theorem B4798187 : Blo 1895435 4798187 := bstep (se 1 (by rfl) ⟨3598640, by rfl⟩ : syracuseStep 4798187 = 7197281) B7197281
theorem B3198791 : Blo 1895435 3198791 := bstep (se 1 (by rfl) ⟨2399093, by rfl⟩ : syracuseStep 3198791 = 4798187) B4798187
theorem B2132527 : Blo 1895435 2132527 := bstep (se 1 (by rfl) ⟨1599395, by rfl⟩ : syracuseStep 2132527 = 3198791) B3198791
theorem B2843369 : Blo 1895435 2843369 := bstep (se 2 (by rfl) ⟨1066263, by rfl⟩ : syracuseStep 2843369 = 2132527) B2132527
theorem B1895579 : Blo 1895435 1895579 := bstep (se 1 (by rfl) ⟨1421684, by rfl⟩ : syracuseStep 1895579 = 2843369) B2843369
theorem B5471621 : Blo 1895435 5471621 := bbase (se 4 (by rfl) ⟨512964, by rfl⟩ : syracuseStep 5471621 = 1025929) (by norm_num)
theorem B3647747 : Blo 1895435 3647747 := bstep (se 1 (by rfl) ⟨2735810, by rfl⟩ : syracuseStep 3647747 = 5471621) B5471621
theorem B2431831 : Blo 1895435 2431831 := bstep (se 1 (by rfl) ⟨1823873, by rfl⟩ : syracuseStep 2431831 = 3647747) B3647747
theorem B3242441 : Blo 1895435 3242441 := bstep (se 2 (by rfl) ⟨1215915, by rfl⟩ : syracuseStep 3242441 = 2431831) B2431831
theorem B2161627 : Blo 1895435 2161627 := bstep (se 1 (by rfl) ⟨1621220, by rfl⟩ : syracuseStep 2161627 = 3242441) B3242441
theorem B11528677 : Blo 1895435 11528677 := bstep (se 4 (by rfl) ⟨1080813, by rfl⟩ : syracuseStep 11528677 = 2161627) B2161627
theorem B15371569 : Blo 1895435 15371569 := bstep (se 2 (by rfl) ⟨5764338, by rfl⟩ : syracuseStep 15371569 = 11528677) B11528677
theorem B20495425 : Blo 1895435 20495425 := bstep (se 2 (by rfl) ⟨7685784, by rfl⟩ : syracuseStep 20495425 = 15371569) B15371569
theorem B27327233 : Blo 1895435 27327233 := bstep (se 2 (by rfl) ⟨10247712, by rfl⟩ : syracuseStep 27327233 = 20495425) B20495425
theorem B18218155 : Blo 1895435 18218155 := bstep (se 1 (by rfl) ⟨13663616, by rfl⟩ : syracuseStep 18218155 = 27327233) B27327233
theorem B24290873 : Blo 1895435 24290873 := bstep (se 2 (by rfl) ⟨9109077, by rfl⟩ : syracuseStep 24290873 = 18218155) B18218155
theorem B16193915 : Blo 1895435 16193915 := bstep (se 1 (by rfl) ⟨12145436, by rfl⟩ : syracuseStep 16193915 = 24290873) B24290873
theorem B10795943 : Blo 1895435 10795943 := bstep (se 1 (by rfl) ⟨8096957, by rfl⟩ : syracuseStep 10795943 = 16193915) B16193915
theorem B7197295 : Blo 1895435 7197295 := bstep (se 1 (by rfl) ⟨5397971, by rfl⟩ : syracuseStep 7197295 = 10795943) B10795943
theorem B9596393 : Blo 1895435 9596393 := bstep (se 2 (by rfl) ⟨3598647, by rfl⟩ : syracuseStep 9596393 = 7197295) B7197295
theorem B6397595 : Blo 1895435 6397595 := bstep (se 1 (by rfl) ⟨4798196, by rfl⟩ : syracuseStep 6397595 = 9596393) B9596393
theorem B4265063 : Blo 1895435 4265063 := bstep (se 1 (by rfl) ⟨3198797, by rfl⟩ : syracuseStep 4265063 = 6397595) B6397595
theorem B2843375 : Blo 1895435 2843375 := bstep (se 1 (by rfl) ⟨2132531, by rfl⟩ : syracuseStep 2843375 = 4265063) B4265063
theorem B1895583 : Blo 1895435 1895583 := bstep (se 1 (by rfl) ⟨1421687, by rfl⟩ : syracuseStep 1895583 = 2843375) B2843375
theorem B2843381 : Blo 1895435 2843381 := bbase (se 5 (by rfl) ⟨133283, by rfl⟩ : syracuseStep 2843381 = 266567) (by norm_num)
theorem B1895587 : Blo 1895435 1895587 := bstep (se 1 (by rfl) ⟨1421690, by rfl⟩ : syracuseStep 1895587 = 2843381) B2843381
theorem B7295525 : Blo 1895435 7295525 := bbase (se 4 (by rfl) ⟨683955, by rfl⟩ : syracuseStep 7295525 = 1367911) (by norm_num)
theorem B4863683 : Blo 1895435 4863683 := bstep (se 1 (by rfl) ⟨3647762, by rfl⟩ : syracuseStep 4863683 = 7295525) B7295525
theorem B12969821 : Blo 1895435 12969821 := bstep (se 3 (by rfl) ⟨2431841, by rfl⟩ : syracuseStep 12969821 = 4863683) B4863683
theorem B34586189 : Blo 1895435 34586189 := bstep (se 3 (by rfl) ⟨6484910, by rfl⟩ : syracuseStep 34586189 = 12969821) B12969821
theorem B23057459 : Blo 1895435 23057459 := bstep (se 1 (by rfl) ⟨17293094, by rfl⟩ : syracuseStep 23057459 = 34586189) B34586189
theorem B15371639 : Blo 1895435 15371639 := bstep (se 1 (by rfl) ⟨11528729, by rfl⟩ : syracuseStep 15371639 = 23057459) B23057459
theorem B10247759 : Blo 1895435 10247759 := bstep (se 1 (by rfl) ⟨7685819, by rfl⟩ : syracuseStep 10247759 = 15371639) B15371639
theorem B6831839 : Blo 1895435 6831839 := bstep (se 1 (by rfl) ⟨5123879, by rfl⟩ : syracuseStep 6831839 = 10247759) B10247759
theorem B4554559 : Blo 1895435 4554559 := bstep (se 1 (by rfl) ⟨3415919, by rfl⟩ : syracuseStep 4554559 = 6831839) B6831839
theorem B6072745 : Blo 1895435 6072745 := bstep (se 2 (by rfl) ⟨2277279, by rfl⟩ : syracuseStep 6072745 = 4554559) B4554559
theorem B8096993 : Blo 1895435 8096993 := bstep (se 2 (by rfl) ⟨3036372, by rfl⟩ : syracuseStep 8096993 = 6072745) B6072745
theorem B5397995 : Blo 1895435 5397995 := bstep (se 1 (by rfl) ⟨4048496, by rfl⟩ : syracuseStep 5397995 = 8096993) B8096993
theorem B3598663 : Blo 1895435 3598663 := bstep (se 1 (by rfl) ⟨2698997, by rfl⟩ : syracuseStep 3598663 = 5397995) B5397995
theorem B4798217 : Blo 1895435 4798217 := bstep (se 2 (by rfl) ⟨1799331, by rfl⟩ : syracuseStep 4798217 = 3598663) B3598663
theorem B3198811 : Blo 1895435 3198811 := bstep (se 1 (by rfl) ⟨2399108, by rfl⟩ : syracuseStep 3198811 = 4798217) B4798217
theorem B4265081 : Blo 1895435 4265081 := bstep (se 2 (by rfl) ⟨1599405, by rfl⟩ : syracuseStep 4265081 = 3198811) B3198811
theorem B2843387 : Blo 1895435 2843387 := bstep (se 1 (by rfl) ⟨2132540, by rfl⟩ : syracuseStep 2843387 = 4265081) B4265081
theorem B1895591 : Blo 1895435 1895591 := bstep (se 1 (by rfl) ⟨1421693, by rfl⟩ : syracuseStep 1895591 = 2843387) B2843387
theorem B2132545 : Blo 1895435 2132545 := bbase (se 2 (by rfl) ⟨799704, by rfl⟩ : syracuseStep 2132545 = 1599409) (by norm_num)
theorem B2843393 : Blo 1895435 2843393 := bstep (se 2 (by rfl) ⟨1066272, by rfl⟩ : syracuseStep 2843393 = 2132545) B2132545
theorem B1895595 : Blo 1895435 1895595 := bstep (se 1 (by rfl) ⟨1421696, by rfl⟩ : syracuseStep 1895595 = 2843393) B2843393
theorem B4798237 : Blo 1895435 4798237 := bbase (se 3 (by rfl) ⟨899669, by rfl⟩ : syracuseStep 4798237 = 1799339) (by norm_num)
theorem B6397649 : Blo 1895435 6397649 := bstep (se 2 (by rfl) ⟨2399118, by rfl⟩ : syracuseStep 6397649 = 4798237) B4798237
theorem B4265099 : Blo 1895435 4265099 := bstep (se 1 (by rfl) ⟨3198824, by rfl⟩ : syracuseStep 4265099 = 6397649) B6397649
theorem B2843399 : Blo 1895435 2843399 := bstep (se 1 (by rfl) ⟨2132549, by rfl⟩ : syracuseStep 2843399 = 4265099) B4265099
theorem B1895599 : Blo 1895435 1895599 := bstep (se 1 (by rfl) ⟨1421699, by rfl⟩ : syracuseStep 1895599 = 2843399) B2843399
theorem B2843405 : Blo 1895435 2843405 := bbase (se 3 (by rfl) ⟨533138, by rfl⟩ : syracuseStep 2843405 = 1066277) (by norm_num)
theorem B1895603 : Blo 1895435 1895603 := bstep (se 1 (by rfl) ⟨1421702, by rfl⟩ : syracuseStep 1895603 = 2843405) B2843405
theorem B4265117 : Blo 1895435 4265117 := bbase (se 3 (by rfl) ⟨799709, by rfl⟩ : syracuseStep 4265117 = 1599419) (by norm_num)
theorem B2843411 : Blo 1895435 2843411 := bstep (se 1 (by rfl) ⟨2132558, by rfl⟩ : syracuseStep 2843411 = 4265117) B4265117
theorem B1895607 : Blo 1895435 1895607 := bstep (se 1 (by rfl) ⟨1421705, by rfl⟩ : syracuseStep 1895607 = 2843411) B2843411
theorem B3198845 : Blo 1895435 3198845 := bbase (se 3 (by rfl) ⟨599783, by rfl⟩ : syracuseStep 3198845 = 1199567) (by norm_num)
theorem B2132563 : Blo 1895435 2132563 := bstep (se 1 (by rfl) ⟨1599422, by rfl⟩ : syracuseStep 2132563 = 3198845) B3198845
theorem B2843417 : Blo 1895435 2843417 := bstep (se 2 (by rfl) ⟨1066281, by rfl⟩ : syracuseStep 2843417 = 2132563) B2132563
theorem B1895611 : Blo 1895435 1895611 := bstep (se 1 (by rfl) ⟨1421708, by rfl⟩ : syracuseStep 1895611 = 2843417) B2843417
theorem B6072821 : Blo 1895435 6072821 := bbase (se 5 (by rfl) ⟨284663, by rfl⟩ : syracuseStep 6072821 = 569327) (by norm_num)
theorem B4048547 : Blo 1895435 4048547 := bstep (se 1 (by rfl) ⟨3036410, by rfl⟩ : syracuseStep 4048547 = 6072821) B6072821
theorem B10796125 : Blo 1895435 10796125 := bstep (se 3 (by rfl) ⟨2024273, by rfl⟩ : syracuseStep 10796125 = 4048547) B4048547
theorem B14394833 : Blo 1895435 14394833 := bstep (se 2 (by rfl) ⟨5398062, by rfl⟩ : syracuseStep 14394833 = 10796125) B10796125
theorem B9596555 : Blo 1895435 9596555 := bstep (se 1 (by rfl) ⟨7197416, by rfl⟩ : syracuseStep 9596555 = 14394833) B14394833
theorem B6397703 : Blo 1895435 6397703 := bstep (se 1 (by rfl) ⟨4798277, by rfl⟩ : syracuseStep 6397703 = 9596555) B9596555
theorem B4265135 : Blo 1895435 4265135 := bstep (se 1 (by rfl) ⟨3198851, by rfl⟩ : syracuseStep 4265135 = 6397703) B6397703
theorem B2843423 : Blo 1895435 2843423 := bstep (se 1 (by rfl) ⟨2132567, by rfl⟩ : syracuseStep 2843423 = 4265135) B4265135
theorem B1895615 : Blo 1895435 1895615 := bstep (se 1 (by rfl) ⟨1421711, by rfl⟩ : syracuseStep 1895615 = 2843423) B2843423
theorem B2843429 : Blo 1895435 2843429 := bbase (se 4 (by rfl) ⟨266571, by rfl⟩ : syracuseStep 2843429 = 533143) (by norm_num)
theorem B1895619 : Blo 1895435 1895619 := bstep (se 1 (by rfl) ⟨1421714, by rfl⟩ : syracuseStep 1895619 = 2843429) B2843429
theorem B2399149 : Blo 1895435 2399149 := bbase (se 3 (by rfl) ⟨449840, by rfl⟩ : syracuseStep 2399149 = 899681) (by norm_num)
theorem B3198865 : Blo 1895435 3198865 := bstep (se 2 (by rfl) ⟨1199574, by rfl⟩ : syracuseStep 3198865 = 2399149) B2399149
theorem B4265153 : Blo 1895435 4265153 := bstep (se 2 (by rfl) ⟨1599432, by rfl⟩ : syracuseStep 4265153 = 3198865) B3198865
theorem B2843435 : Blo 1895435 2843435 := bstep (se 1 (by rfl) ⟨2132576, by rfl⟩ : syracuseStep 2843435 = 4265153) B4265153
theorem B1895623 : Blo 1895435 1895623 := bstep (se 1 (by rfl) ⟨1421717, by rfl⟩ : syracuseStep 1895623 = 2843435) B2843435
theorem B2132581 : Blo 1895435 2132581 := bbase (se 4 (by rfl) ⟨199929, by rfl⟩ : syracuseStep 2132581 = 399859) (by norm_num)
theorem B2843441 : Blo 1895435 2843441 := bstep (se 2 (by rfl) ⟨1066290, by rfl⟩ : syracuseStep 2843441 = 2132581) B2132581
theorem B1895627 : Blo 1895435 1895627 := bstep (se 1 (by rfl) ⟨1421720, by rfl⟩ : syracuseStep 1895627 = 2843441) B2843441
theorem B3036437 : Blo 1895435 3036437 := bbase (se 6 (by rfl) ⟨71166, by rfl⟩ : syracuseStep 3036437 = 142333) (by norm_num)
theorem B2024291 : Blo 1895435 2024291 := bstep (se 1 (by rfl) ⟨1518218, by rfl⟩ : syracuseStep 2024291 = 3036437) B3036437
theorem B5398109 : Blo 1895435 5398109 := bstep (se 3 (by rfl) ⟨1012145, by rfl⟩ : syracuseStep 5398109 = 2024291) B2024291
theorem B3598739 : Blo 1895435 3598739 := bstep (se 1 (by rfl) ⟨2699054, by rfl⟩ : syracuseStep 3598739 = 5398109) B5398109
theorem B2399159 : Blo 1895435 2399159 := bstep (se 1 (by rfl) ⟨1799369, by rfl⟩ : syracuseStep 2399159 = 3598739) B3598739
theorem B6397757 : Blo 1895435 6397757 := bstep (se 3 (by rfl) ⟨1199579, by rfl⟩ : syracuseStep 6397757 = 2399159) B2399159
theorem B4265171 : Blo 1895435 4265171 := bstep (se 1 (by rfl) ⟨3198878, by rfl⟩ : syracuseStep 4265171 = 6397757) B6397757
theorem B2843447 : Blo 1895435 2843447 := bstep (se 1 (by rfl) ⟨2132585, by rfl⟩ : syracuseStep 2843447 = 4265171) B4265171
theorem B1895631 : Blo 1895435 1895631 := bstep (se 1 (by rfl) ⟨1421723, by rfl⟩ : syracuseStep 1895631 = 2843447) B2843447
theorem B2843453 : Blo 1895435 2843453 := bbase (se 3 (by rfl) ⟨533147, by rfl⟩ : syracuseStep 2843453 = 1066295) (by norm_num)
theorem B1895635 : Blo 1895435 1895635 := bstep (se 1 (by rfl) ⟨1421726, by rfl⟩ : syracuseStep 1895635 = 2843453) B2843453
theorem B4265189 : Blo 1895435 4265189 := bbase (se 4 (by rfl) ⟨399861, by rfl⟩ : syracuseStep 4265189 = 799723) (by norm_num)
theorem B2843459 : Blo 1895435 2843459 := bstep (se 1 (by rfl) ⟨2132594, by rfl⟩ : syracuseStep 2843459 = 4265189) B4265189
theorem B1895639 : Blo 1895435 1895639 := bstep (se 1 (by rfl) ⟨1421729, by rfl⟩ : syracuseStep 1895639 = 2843459) B2843459
theorem B4798349 : Blo 1895435 4798349 := bbase (se 3 (by rfl) ⟨899690, by rfl⟩ : syracuseStep 4798349 = 1799381) (by norm_num)
theorem B3198899 : Blo 1895435 3198899 := bstep (se 1 (by rfl) ⟨2399174, by rfl⟩ : syracuseStep 3198899 = 4798349) B4798349
theorem B2132599 : Blo 1895435 2132599 := bstep (se 1 (by rfl) ⟨1599449, by rfl⟩ : syracuseStep 2132599 = 3198899) B3198899
theorem B2843465 : Blo 1895435 2843465 := bstep (se 2 (by rfl) ⟨1066299, by rfl⟩ : syracuseStep 2843465 = 2132599) B2132599
theorem B1895643 : Blo 1895435 1895643 := bstep (se 1 (by rfl) ⟨1421732, by rfl⟩ : syracuseStep 1895643 = 2843465) B2843465
theorem B2699077 : Blo 1895435 2699077 := bbase (se 4 (by rfl) ⟨253038, by rfl⟩ : syracuseStep 2699077 = 506077) (by norm_num)
theorem B3598769 : Blo 1895435 3598769 := bstep (se 2 (by rfl) ⟨1349538, by rfl⟩ : syracuseStep 3598769 = 2699077) B2699077
theorem B9596717 : Blo 1895435 9596717 := bstep (se 3 (by rfl) ⟨1799384, by rfl⟩ : syracuseStep 9596717 = 3598769) B3598769
theorem B6397811 : Blo 1895435 6397811 := bstep (se 1 (by rfl) ⟨4798358, by rfl⟩ : syracuseStep 6397811 = 9596717) B9596717
theorem B4265207 : Blo 1895435 4265207 := bstep (se 1 (by rfl) ⟨3198905, by rfl⟩ : syracuseStep 4265207 = 6397811) B6397811
theorem B2843471 : Blo 1895435 2843471 := bstep (se 1 (by rfl) ⟨2132603, by rfl⟩ : syracuseStep 2843471 = 4265207) B4265207
theorem B1895647 : Blo 1895435 1895647 := bstep (se 1 (by rfl) ⟨1421735, by rfl⟩ : syracuseStep 1895647 = 2843471) B2843471
theorem B2843477 : Blo 1895435 2843477 := bbase (se 9 (by rfl) ⟨8330, by rfl⟩ : syracuseStep 2843477 = 16661) (by norm_num)
theorem B1895651 : Blo 1895435 1895651 := bstep (se 1 (by rfl) ⟨1421738, by rfl⟩ : syracuseStep 1895651 = 2843477) B2843477
theorem B5124053 : Blo 1895435 5124053 := bbase (se 7 (by rfl) ⟨60047, by rfl⟩ : syracuseStep 5124053 = 120095) (by norm_num)
theorem B3416035 : Blo 1895435 3416035 := bstep (se 1 (by rfl) ⟨2562026, by rfl⟩ : syracuseStep 3416035 = 5124053) B5124053
theorem B4554713 : Blo 1895435 4554713 := bstep (se 2 (by rfl) ⟨1708017, by rfl⟩ : syracuseStep 4554713 = 3416035) B3416035
theorem B3036475 : Blo 1895435 3036475 := bstep (se 1 (by rfl) ⟨2277356, by rfl⟩ : syracuseStep 3036475 = 4554713) B4554713
theorem B4048633 : Blo 1895435 4048633 := bstep (se 2 (by rfl) ⟨1518237, by rfl⟩ : syracuseStep 4048633 = 3036475) B3036475
theorem B5398177 : Blo 1895435 5398177 := bstep (se 2 (by rfl) ⟨2024316, by rfl⟩ : syracuseStep 5398177 = 4048633) B4048633
theorem B7197569 : Blo 1895435 7197569 := bstep (se 2 (by rfl) ⟨2699088, by rfl⟩ : syracuseStep 7197569 = 5398177) B5398177
theorem B4798379 : Blo 1895435 4798379 := bstep (se 1 (by rfl) ⟨3598784, by rfl⟩ : syracuseStep 4798379 = 7197569) B7197569
theorem B3198919 : Blo 1895435 3198919 := bstep (se 1 (by rfl) ⟨2399189, by rfl⟩ : syracuseStep 3198919 = 4798379) B4798379
theorem B4265225 : Blo 1895435 4265225 := bstep (se 2 (by rfl) ⟨1599459, by rfl⟩ : syracuseStep 4265225 = 3198919) B3198919
theorem B2843483 : Blo 1895435 2843483 := bstep (se 1 (by rfl) ⟨2132612, by rfl⟩ : syracuseStep 2843483 = 4265225) B4265225
theorem B1895655 : Blo 1895435 1895655 := bstep (se 1 (by rfl) ⟨1421741, by rfl⟩ : syracuseStep 1895655 = 2843483) B2843483
theorem B2132617 : Blo 1895435 2132617 := bbase (se 2 (by rfl) ⟨799731, by rfl⟩ : syracuseStep 2132617 = 1599463) (by norm_num)
theorem B2843489 : Blo 1895435 2843489 := bstep (se 2 (by rfl) ⟨1066308, by rfl⟩ : syracuseStep 2843489 = 2132617) B2132617
theorem B1895659 : Blo 1895435 1895659 := bstep (se 1 (by rfl) ⟨1421744, by rfl⟩ : syracuseStep 1895659 = 2843489) B2843489
theorem B4323437 : Blo 1895435 4323437 := bbase (se 3 (by rfl) ⟨810644, by rfl⟩ : syracuseStep 4323437 = 1621289) (by norm_num)
theorem B2882291 : Blo 1895435 2882291 := bstep (se 1 (by rfl) ⟨2161718, by rfl⟩ : syracuseStep 2882291 = 4323437) B4323437
theorem B7686109 : Blo 1895435 7686109 := bstep (se 3 (by rfl) ⟨1441145, by rfl⟩ : syracuseStep 7686109 = 2882291) B2882291
theorem B40992581 : Blo 1895435 40992581 := bstep (se 4 (by rfl) ⟨3843054, by rfl⟩ : syracuseStep 40992581 = 7686109) B7686109
theorem B27328387 : Blo 1895435 27328387 := bstep (se 1 (by rfl) ⟨20496290, by rfl⟩ : syracuseStep 27328387 = 40992581) B40992581
theorem B36437849 : Blo 1895435 36437849 := bstep (se 2 (by rfl) ⟨13664193, by rfl⟩ : syracuseStep 36437849 = 27328387) B27328387
theorem B24291899 : Blo 1895435 24291899 := bstep (se 1 (by rfl) ⟨18218924, by rfl⟩ : syracuseStep 24291899 = 36437849) B36437849
theorem B16194599 : Blo 1895435 16194599 := bstep (se 1 (by rfl) ⟨12145949, by rfl⟩ : syracuseStep 16194599 = 24291899) B24291899
theorem B10796399 : Blo 1895435 10796399 := bstep (se 1 (by rfl) ⟨8097299, by rfl⟩ : syracuseStep 10796399 = 16194599) B16194599
theorem B7197599 : Blo 1895435 7197599 := bstep (se 1 (by rfl) ⟨5398199, by rfl⟩ : syracuseStep 7197599 = 10796399) B10796399
theorem B4798399 : Blo 1895435 4798399 := bstep (se 1 (by rfl) ⟨3598799, by rfl⟩ : syracuseStep 4798399 = 7197599) B7197599
theorem B6397865 : Blo 1895435 6397865 := bstep (se 2 (by rfl) ⟨2399199, by rfl⟩ : syracuseStep 6397865 = 4798399) B4798399
theorem B4265243 : Blo 1895435 4265243 := bstep (se 1 (by rfl) ⟨3198932, by rfl⟩ : syracuseStep 4265243 = 6397865) B6397865
theorem B2843495 : Blo 1895435 2843495 := bstep (se 1 (by rfl) ⟨2132621, by rfl⟩ : syracuseStep 2843495 = 4265243) B4265243
theorem B1895663 : Blo 1895435 1895663 := bstep (se 1 (by rfl) ⟨1421747, by rfl⟩ : syracuseStep 1895663 = 2843495) B2843495
theorem B2843501 : Blo 1895435 2843501 := bbase (se 3 (by rfl) ⟨533156, by rfl⟩ : syracuseStep 2843501 = 1066313) (by norm_num)
theorem B1895667 : Blo 1895435 1895667 := bstep (se 1 (by rfl) ⟨1421750, by rfl⟩ : syracuseStep 1895667 = 2843501) B2843501
theorem B4265261 : Blo 1895435 4265261 := bbase (se 3 (by rfl) ⟨799736, by rfl⟩ : syracuseStep 4265261 = 1599473) (by norm_num)
theorem B2843507 : Blo 1895435 2843507 := bstep (se 1 (by rfl) ⟨2132630, by rfl⟩ : syracuseStep 2843507 = 4265261) B4265261
theorem B1895671 : Blo 1895435 1895671 := bstep (se 1 (by rfl) ⟨1421753, by rfl⟩ : syracuseStep 1895671 = 2843507) B2843507
theorem B2161733 : Blo 1895435 2161733 := bbase (se 4 (by rfl) ⟨202662, by rfl⟩ : syracuseStep 2161733 = 405325) (by norm_num)
theorem B5764621 : Blo 1895435 5764621 := bstep (se 3 (by rfl) ⟨1080866, by rfl⟩ : syracuseStep 5764621 = 2161733) B2161733
theorem B7686161 : Blo 1895435 7686161 := bstep (se 2 (by rfl) ⟨2882310, by rfl⟩ : syracuseStep 7686161 = 5764621) B5764621
theorem B5124107 : Blo 1895435 5124107 := bstep (se 1 (by rfl) ⟨3843080, by rfl⟩ : syracuseStep 5124107 = 7686161) B7686161
theorem B13664285 : Blo 1895435 13664285 := bstep (se 3 (by rfl) ⟨2562053, by rfl⟩ : syracuseStep 13664285 = 5124107) B5124107
theorem B9109523 : Blo 1895435 9109523 := bstep (se 1 (by rfl) ⟨6832142, by rfl⟩ : syracuseStep 9109523 = 13664285) B13664285
theorem B6073015 : Blo 1895435 6073015 := bstep (se 1 (by rfl) ⟨4554761, by rfl⟩ : syracuseStep 6073015 = 9109523) B9109523
theorem B8097353 : Blo 1895435 8097353 := bstep (se 2 (by rfl) ⟨3036507, by rfl⟩ : syracuseStep 8097353 = 6073015) B6073015
theorem B5398235 : Blo 1895435 5398235 := bstep (se 1 (by rfl) ⟨4048676, by rfl⟩ : syracuseStep 5398235 = 8097353) B8097353
theorem B3598823 : Blo 1895435 3598823 := bstep (se 1 (by rfl) ⟨2699117, by rfl⟩ : syracuseStep 3598823 = 5398235) B5398235
theorem B2399215 : Blo 1895435 2399215 := bstep (se 1 (by rfl) ⟨1799411, by rfl⟩ : syracuseStep 2399215 = 3598823) B3598823
theorem B3198953 : Blo 1895435 3198953 := bstep (se 2 (by rfl) ⟨1199607, by rfl⟩ : syracuseStep 3198953 = 2399215) B2399215
theorem B2132635 : Blo 1895435 2132635 := bstep (se 1 (by rfl) ⟨1599476, by rfl⟩ : syracuseStep 2132635 = 3198953) B3198953
theorem B2843513 : Blo 1895435 2843513 := bstep (se 2 (by rfl) ⟨1066317, by rfl⟩ : syracuseStep 2843513 = 2132635) B2132635
theorem B1895675 : Blo 1895435 1895675 := bstep (se 1 (by rfl) ⟨1421756, by rfl⟩ : syracuseStep 1895675 = 2843513) B2843513
theorem B3416077 : Blo 1895435 3416077 := bbase (se 3 (by rfl) ⟨640514, by rfl⟩ : syracuseStep 3416077 = 1281029) (by norm_num)
theorem B18219077 : Blo 1895435 18219077 := bstep (se 4 (by rfl) ⟨1708038, by rfl⟩ : syracuseStep 18219077 = 3416077) B3416077
theorem B12146051 : Blo 1895435 12146051 := bstep (se 1 (by rfl) ⟨9109538, by rfl⟩ : syracuseStep 12146051 = 18219077) B18219077
theorem B32389469 : Blo 1895435 32389469 := bstep (se 3 (by rfl) ⟨6073025, by rfl⟩ : syracuseStep 32389469 = 12146051) B12146051
theorem B21592979 : Blo 1895435 21592979 := bstep (se 1 (by rfl) ⟨16194734, by rfl⟩ : syracuseStep 21592979 = 32389469) B32389469
theorem B14395319 : Blo 1895435 14395319 := bstep (se 1 (by rfl) ⟨10796489, by rfl⟩ : syracuseStep 14395319 = 21592979) B21592979
theorem B9596879 : Blo 1895435 9596879 := bstep (se 1 (by rfl) ⟨7197659, by rfl⟩ : syracuseStep 9596879 = 14395319) B14395319
theorem B6397919 : Blo 1895435 6397919 := bstep (se 1 (by rfl) ⟨4798439, by rfl⟩ : syracuseStep 6397919 = 9596879) B9596879
theorem B4265279 : Blo 1895435 4265279 := bstep (se 1 (by rfl) ⟨3198959, by rfl⟩ : syracuseStep 4265279 = 6397919) B6397919
theorem B2843519 : Blo 1895435 2843519 := bstep (se 1 (by rfl) ⟨2132639, by rfl⟩ : syracuseStep 2843519 = 4265279) B4265279
theorem B1895679 : Blo 1895435 1895679 := bstep (se 1 (by rfl) ⟨1421759, by rfl⟩ : syracuseStep 1895679 = 2843519) B2843519
theorem B2843525 : Blo 1895435 2843525 := bbase (se 4 (by rfl) ⟨266580, by rfl⟩ : syracuseStep 2843525 = 533161) (by norm_num)
theorem B1895683 : Blo 1895435 1895683 := bstep (se 1 (by rfl) ⟨1421762, by rfl⟩ : syracuseStep 1895683 = 2843525) B2843525
theorem B3198973 : Blo 1895435 3198973 := bbase (se 3 (by rfl) ⟨599807, by rfl⟩ : syracuseStep 3198973 = 1199615) (by norm_num)
theorem B4265297 : Blo 1895435 4265297 := bstep (se 2 (by rfl) ⟨1599486, by rfl⟩ : syracuseStep 4265297 = 3198973) B3198973
theorem B2843531 : Blo 1895435 2843531 := bstep (se 1 (by rfl) ⟨2132648, by rfl⟩ : syracuseStep 2843531 = 4265297) B4265297
theorem B1895687 : Blo 1895435 1895687 := bstep (se 1 (by rfl) ⟨1421765, by rfl⟩ : syracuseStep 1895687 = 2843531) B2843531
theorem B2132653 : Blo 1895435 2132653 := bbase (se 3 (by rfl) ⟨399872, by rfl⟩ : syracuseStep 2132653 = 799745) (by norm_num)
theorem B2843537 : Blo 1895435 2843537 := bstep (se 2 (by rfl) ⟨1066326, by rfl⟩ : syracuseStep 2843537 = 2132653) B2132653
theorem B1895691 : Blo 1895435 1895691 := bstep (se 1 (by rfl) ⟨1421768, by rfl⟩ : syracuseStep 1895691 = 2843537) B2843537
theorem B6397973 : Blo 1895435 6397973 := bbase (se 6 (by rfl) ⟨149952, by rfl⟩ : syracuseStep 6397973 = 299905) (by norm_num)
theorem B4265315 : Blo 1895435 4265315 := bstep (se 1 (by rfl) ⟨3198986, by rfl⟩ : syracuseStep 4265315 = 6397973) B6397973
theorem B2843543 : Blo 1895435 2843543 := bstep (se 1 (by rfl) ⟨2132657, by rfl⟩ : syracuseStep 2843543 = 4265315) B4265315
theorem B1895695 : Blo 1895435 1895695 := bstep (se 1 (by rfl) ⟨1421771, by rfl⟩ : syracuseStep 1895695 = 2843543) B2843543
theorem B2843549 : Blo 1895435 2843549 := bbase (se 3 (by rfl) ⟨533165, by rfl⟩ : syracuseStep 2843549 = 1066331) (by norm_num)
theorem B1895699 : Blo 1895435 1895699 := bstep (se 1 (by rfl) ⟨1421774, by rfl⟩ : syracuseStep 1895699 = 2843549) B2843549
theorem B4265333 : Blo 1895435 4265333 := bbase (se 5 (by rfl) ⟨199937, by rfl⟩ : syracuseStep 4265333 = 399875) (by norm_num)
theorem B2843555 : Blo 1895435 2843555 := bstep (se 1 (by rfl) ⟨2132666, by rfl⟩ : syracuseStep 2843555 = 4265333) B4265333
theorem B1895703 : Blo 1895435 1895703 := bstep (se 1 (by rfl) ⟨1421777, by rfl⟩ : syracuseStep 1895703 = 2843555) B2843555
theorem B2161769 : Blo 1895435 2161769 := bbase (se 2 (by rfl) ⟨810663, by rfl⟩ : syracuseStep 2161769 = 1621327) (by norm_num)
theorem B5764717 : Blo 1895435 5764717 := bstep (se 3 (by rfl) ⟨1080884, by rfl⟩ : syracuseStep 5764717 = 2161769) B2161769
theorem B7686289 : Blo 1895435 7686289 := bstep (se 2 (by rfl) ⟨2882358, by rfl⟩ : syracuseStep 7686289 = 5764717) B5764717
theorem B10248385 : Blo 1895435 10248385 := bstep (se 2 (by rfl) ⟨3843144, by rfl⟩ : syracuseStep 10248385 = 7686289) B7686289
theorem B13664513 : Blo 1895435 13664513 := bstep (se 2 (by rfl) ⟨5124192, by rfl⟩ : syracuseStep 13664513 = 10248385) B10248385
theorem B9109675 : Blo 1895435 9109675 := bstep (se 1 (by rfl) ⟨6832256, by rfl⟩ : syracuseStep 9109675 = 13664513) B13664513
theorem B12146233 : Blo 1895435 12146233 := bstep (se 2 (by rfl) ⟨4554837, by rfl⟩ : syracuseStep 12146233 = 9109675) B9109675
theorem B16194977 : Blo 1895435 16194977 := bstep (se 2 (by rfl) ⟨6073116, by rfl⟩ : syracuseStep 16194977 = 12146233) B12146233
theorem B10796651 : Blo 1895435 10796651 := bstep (se 1 (by rfl) ⟨8097488, by rfl⟩ : syracuseStep 10796651 = 16194977) B16194977
theorem B7197767 : Blo 1895435 7197767 := bstep (se 1 (by rfl) ⟨5398325, by rfl⟩ : syracuseStep 7197767 = 10796651) B10796651
theorem B4798511 : Blo 1895435 4798511 := bstep (se 1 (by rfl) ⟨3598883, by rfl⟩ : syracuseStep 4798511 = 7197767) B7197767
theorem B3199007 : Blo 1895435 3199007 := bstep (se 1 (by rfl) ⟨2399255, by rfl⟩ : syracuseStep 3199007 = 4798511) B4798511
theorem B2132671 : Blo 1895435 2132671 := bstep (se 1 (by rfl) ⟨1599503, by rfl⟩ : syracuseStep 2132671 = 3199007) B3199007
theorem B2843561 : Blo 1895435 2843561 := bstep (se 2 (by rfl) ⟨1066335, by rfl⟩ : syracuseStep 2843561 = 2132671) B2132671
theorem B1895707 : Blo 1895435 1895707 := bstep (se 1 (by rfl) ⟨1421780, by rfl⟩ : syracuseStep 1895707 = 2843561) B2843561
theorem B7197781 : Blo 1895435 7197781 := bbase (se 8 (by rfl) ⟨42174, by rfl⟩ : syracuseStep 7197781 = 84349) (by norm_num)
theorem B9597041 : Blo 1895435 9597041 := bstep (se 2 (by rfl) ⟨3598890, by rfl⟩ : syracuseStep 9597041 = 7197781) B7197781
theorem B6398027 : Blo 1895435 6398027 := bstep (se 1 (by rfl) ⟨4798520, by rfl⟩ : syracuseStep 6398027 = 9597041) B9597041
theorem B4265351 : Blo 1895435 4265351 := bstep (se 1 (by rfl) ⟨3199013, by rfl⟩ : syracuseStep 4265351 = 6398027) B6398027
theorem B2843567 : Blo 1895435 2843567 := bstep (se 1 (by rfl) ⟨2132675, by rfl⟩ : syracuseStep 2843567 = 4265351) B4265351
theorem B1895711 : Blo 1895435 1895711 := bstep (se 1 (by rfl) ⟨1421783, by rfl⟩ : syracuseStep 1895711 = 2843567) B2843567
theorem B2843573 : Blo 1895435 2843573 := bbase (se 5 (by rfl) ⟨133292, by rfl⟩ : syracuseStep 2843573 = 266585) (by norm_num)
theorem B1895715 : Blo 1895435 1895715 := bstep (se 1 (by rfl) ⟨1421786, by rfl⟩ : syracuseStep 1895715 = 2843573) B2843573
theorem B4798541 : Blo 1895435 4798541 := bbase (se 3 (by rfl) ⟨899726, by rfl⟩ : syracuseStep 4798541 = 1799453) (by norm_num)
theorem B3199027 : Blo 1895435 3199027 := bstep (se 1 (by rfl) ⟨2399270, by rfl⟩ : syracuseStep 3199027 = 4798541) B4798541
theorem B4265369 : Blo 1895435 4265369 := bstep (se 2 (by rfl) ⟨1599513, by rfl⟩ : syracuseStep 4265369 = 3199027) B3199027
theorem B2843579 : Blo 1895435 2843579 := bstep (se 1 (by rfl) ⟨2132684, by rfl⟩ : syracuseStep 2843579 = 4265369) B4265369
theorem B1895719 : Blo 1895435 1895719 := bstep (se 1 (by rfl) ⟨1421789, by rfl⟩ : syracuseStep 1895719 = 2843579) B2843579
theorem B2132689 : Blo 1895435 2132689 := bbase (se 2 (by rfl) ⟨799758, by rfl⟩ : syracuseStep 2132689 = 1599517) (by norm_num)
theorem B2843585 : Blo 1895435 2843585 := bstep (se 2 (by rfl) ⟨1066344, by rfl⟩ : syracuseStep 2843585 = 2132689) B2132689
theorem B1895723 : Blo 1895435 1895723 := bstep (se 1 (by rfl) ⟨1421792, by rfl⟩ : syracuseStep 1895723 = 2843585) B2843585
theorem B3416165 : Blo 1895435 3416165 := bbase (se 4 (by rfl) ⟨320265, by rfl⟩ : syracuseStep 3416165 = 640531) (by norm_num)
theorem B2277443 : Blo 1895435 2277443 := bstep (se 1 (by rfl) ⟨1708082, by rfl⟩ : syracuseStep 2277443 = 3416165) B3416165
theorem B6073181 : Blo 1895435 6073181 := bstep (se 3 (by rfl) ⟨1138721, by rfl⟩ : syracuseStep 6073181 = 2277443) B2277443
theorem B4048787 : Blo 1895435 4048787 := bstep (se 1 (by rfl) ⟨3036590, by rfl⟩ : syracuseStep 4048787 = 6073181) B6073181
theorem B2699191 : Blo 1895435 2699191 := bstep (se 1 (by rfl) ⟨2024393, by rfl⟩ : syracuseStep 2699191 = 4048787) B4048787
theorem B3598921 : Blo 1895435 3598921 := bstep (se 2 (by rfl) ⟨1349595, by rfl⟩ : syracuseStep 3598921 = 2699191) B2699191
theorem B4798561 : Blo 1895435 4798561 := bstep (se 2 (by rfl) ⟨1799460, by rfl⟩ : syracuseStep 4798561 = 3598921) B3598921
theorem B6398081 : Blo 1895435 6398081 := bstep (se 2 (by rfl) ⟨2399280, by rfl⟩ : syracuseStep 6398081 = 4798561) B4798561
theorem B4265387 : Blo 1895435 4265387 := bstep (se 1 (by rfl) ⟨3199040, by rfl⟩ : syracuseStep 4265387 = 6398081) B6398081
theorem B2843591 : Blo 1895435 2843591 := bstep (se 1 (by rfl) ⟨2132693, by rfl⟩ : syracuseStep 2843591 = 4265387) B4265387
theorem B1895727 : Blo 1895435 1895727 := bstep (se 1 (by rfl) ⟨1421795, by rfl⟩ : syracuseStep 1895727 = 2843591) B2843591
theorem B2843597 : Blo 1895435 2843597 := bbase (se 3 (by rfl) ⟨533174, by rfl⟩ : syracuseStep 2843597 = 1066349) (by norm_num)
theorem B1895731 : Blo 1895435 1895731 := bstep (se 1 (by rfl) ⟨1421798, by rfl⟩ : syracuseStep 1895731 = 2843597) B2843597
theorem B4265405 : Blo 1895435 4265405 := bbase (se 3 (by rfl) ⟨799763, by rfl⟩ : syracuseStep 4265405 = 1599527) (by norm_num)
theorem B2843603 : Blo 1895435 2843603 := bstep (se 1 (by rfl) ⟨2132702, by rfl⟩ : syracuseStep 2843603 = 4265405) B4265405
theorem B1895735 : Blo 1895435 1895735 := bstep (se 1 (by rfl) ⟨1421801, by rfl⟩ : syracuseStep 1895735 = 2843603) B2843603
theorem B3199061 : Blo 1895435 3199061 := bbase (se 8 (by rfl) ⟨18744, by rfl⟩ : syracuseStep 3199061 = 37489) (by norm_num)
theorem B2132707 : Blo 1895435 2132707 := bstep (se 1 (by rfl) ⟨1599530, by rfl⟩ : syracuseStep 2132707 = 3199061) B3199061
theorem B2843609 : Blo 1895435 2843609 := bstep (se 2 (by rfl) ⟨1066353, by rfl⟩ : syracuseStep 2843609 = 2132707) B2132707
theorem B1895739 : Blo 1895435 1895739 := bstep (se 1 (by rfl) ⟨1421804, by rfl⟩ : syracuseStep 1895739 = 2843609) B2843609
theorem B2882413 : Blo 1895435 2882413 := bbase (se 3 (by rfl) ⟨540452, by rfl⟩ : syracuseStep 2882413 = 1080905) (by norm_num)
theorem B3843217 : Blo 1895435 3843217 := bstep (se 2 (by rfl) ⟨1441206, by rfl⟩ : syracuseStep 3843217 = 2882413) B2882413
theorem B20497157 : Blo 1895435 20497157 := bstep (se 4 (by rfl) ⟨1921608, by rfl⟩ : syracuseStep 20497157 = 3843217) B3843217
theorem B13664771 : Blo 1895435 13664771 := bstep (se 1 (by rfl) ⟨10248578, by rfl⟩ : syracuseStep 13664771 = 20497157) B20497157
theorem B9109847 : Blo 1895435 9109847 := bstep (se 1 (by rfl) ⟨6832385, by rfl⟩ : syracuseStep 9109847 = 13664771) B13664771
theorem B6073231 : Blo 1895435 6073231 := bstep (se 1 (by rfl) ⟨4554923, by rfl⟩ : syracuseStep 6073231 = 9109847) B9109847
theorem B8097641 : Blo 1895435 8097641 := bstep (se 2 (by rfl) ⟨3036615, by rfl⟩ : syracuseStep 8097641 = 6073231) B6073231
theorem B5398427 : Blo 1895435 5398427 := bstep (se 1 (by rfl) ⟨4048820, by rfl⟩ : syracuseStep 5398427 = 8097641) B8097641
theorem B14395805 : Blo 1895435 14395805 := bstep (se 3 (by rfl) ⟨2699213, by rfl⟩ : syracuseStep 14395805 = 5398427) B5398427
theorem B9597203 : Blo 1895435 9597203 := bstep (se 1 (by rfl) ⟨7197902, by rfl⟩ : syracuseStep 9597203 = 14395805) B14395805
theorem B6398135 : Blo 1895435 6398135 := bstep (se 1 (by rfl) ⟨4798601, by rfl⟩ : syracuseStep 6398135 = 9597203) B9597203
theorem B4265423 : Blo 1895435 4265423 := bstep (se 1 (by rfl) ⟨3199067, by rfl⟩ : syracuseStep 4265423 = 6398135) B6398135
theorem B2843615 : Blo 1895435 2843615 := bstep (se 1 (by rfl) ⟨2132711, by rfl⟩ : syracuseStep 2843615 = 4265423) B4265423
theorem B1895743 : Blo 1895435 1895743 := bstep (se 1 (by rfl) ⟨1421807, by rfl⟩ : syracuseStep 1895743 = 2843615) B2843615
theorem B2843621 : Blo 1895435 2843621 := bbase (se 4 (by rfl) ⟨266589, by rfl⟩ : syracuseStep 2843621 = 533179) (by norm_num)
theorem B1895747 : Blo 1895435 1895747 := bstep (se 1 (by rfl) ⟨1421810, by rfl⟩ : syracuseStep 1895747 = 2843621) B2843621
theorem B3036629 : Blo 1895435 3036629 := bbase (se 7 (by rfl) ⟨35585, by rfl⟩ : syracuseStep 3036629 = 71171) (by norm_num)
theorem B8097677 : Blo 1895435 8097677 := bstep (se 3 (by rfl) ⟨1518314, by rfl⟩ : syracuseStep 8097677 = 3036629) B3036629
theorem B5398451 : Blo 1895435 5398451 := bstep (se 1 (by rfl) ⟨4048838, by rfl⟩ : syracuseStep 5398451 = 8097677) B8097677
theorem B3598967 : Blo 1895435 3598967 := bstep (se 1 (by rfl) ⟨2699225, by rfl⟩ : syracuseStep 3598967 = 5398451) B5398451
theorem B2399311 : Blo 1895435 2399311 := bstep (se 1 (by rfl) ⟨1799483, by rfl⟩ : syracuseStep 2399311 = 3598967) B3598967
theorem B3199081 : Blo 1895435 3199081 := bstep (se 2 (by rfl) ⟨1199655, by rfl⟩ : syracuseStep 3199081 = 2399311) B2399311
theorem B4265441 : Blo 1895435 4265441 := bstep (se 2 (by rfl) ⟨1599540, by rfl⟩ : syracuseStep 4265441 = 3199081) B3199081
theorem B2843627 : Blo 1895435 2843627 := bstep (se 1 (by rfl) ⟨2132720, by rfl⟩ : syracuseStep 2843627 = 4265441) B4265441
theorem B1895751 : Blo 1895435 1895751 := bstep (se 1 (by rfl) ⟨1421813, by rfl⟩ : syracuseStep 1895751 = 2843627) B2843627
theorem B2132725 : Blo 1895435 2132725 := bbase (se 5 (by rfl) ⟨99971, by rfl⟩ : syracuseStep 2132725 = 199943) (by norm_num)
theorem B2843633 : Blo 1895435 2843633 := bstep (se 2 (by rfl) ⟨1066362, by rfl⟩ : syracuseStep 2843633 = 2132725) B2132725
theorem B1895755 : Blo 1895435 1895755 := bstep (se 1 (by rfl) ⟨1421816, by rfl⟩ : syracuseStep 1895755 = 2843633) B2843633
theorem B2399321 : Blo 1895435 2399321 := bbase (se 2 (by rfl) ⟨899745, by rfl⟩ : syracuseStep 2399321 = 1799491) (by norm_num)
theorem B6398189 : Blo 1895435 6398189 := bstep (se 3 (by rfl) ⟨1199660, by rfl⟩ : syracuseStep 6398189 = 2399321) B2399321
theorem B4265459 : Blo 1895435 4265459 := bstep (se 1 (by rfl) ⟨3199094, by rfl⟩ : syracuseStep 4265459 = 6398189) B6398189
theorem B2843639 : Blo 1895435 2843639 := bstep (se 1 (by rfl) ⟨2132729, by rfl⟩ : syracuseStep 2843639 = 4265459) B4265459
theorem B1895759 : Blo 1895435 1895759 := bstep (se 1 (by rfl) ⟨1421819, by rfl⟩ : syracuseStep 1895759 = 2843639) B2843639
theorem B2843645 : Blo 1895435 2843645 := bbase (se 3 (by rfl) ⟨533183, by rfl⟩ : syracuseStep 2843645 = 1066367) (by norm_num)
theorem B1895763 : Blo 1895435 1895763 := bstep (se 1 (by rfl) ⟨1421822, by rfl⟩ : syracuseStep 1895763 = 2843645) B2843645
theorem B4265477 : Blo 1895435 4265477 := bbase (se 4 (by rfl) ⟨399888, by rfl⟩ : syracuseStep 4265477 = 799777) (by norm_num)
theorem B2843651 : Blo 1895435 2843651 := bstep (se 1 (by rfl) ⟨2132738, by rfl⟩ : syracuseStep 2843651 = 4265477) B4265477
theorem B1895767 : Blo 1895435 1895767 := bstep (se 1 (by rfl) ⟨1421825, by rfl⟩ : syracuseStep 1895767 = 2843651) B2843651
theorem B3599005 : Blo 1895435 3599005 := bbase (se 3 (by rfl) ⟨674813, by rfl⟩ : syracuseStep 3599005 = 1349627) (by norm_num)
theorem B4798673 : Blo 1895435 4798673 := bstep (se 2 (by rfl) ⟨1799502, by rfl⟩ : syracuseStep 4798673 = 3599005) B3599005
theorem B3199115 : Blo 1895435 3199115 := bstep (se 1 (by rfl) ⟨2399336, by rfl⟩ : syracuseStep 3199115 = 4798673) B4798673
theorem B2132743 : Blo 1895435 2132743 := bstep (se 1 (by rfl) ⟨1599557, by rfl⟩ : syracuseStep 2132743 = 3199115) B3199115
theorem B2843657 : Blo 1895435 2843657 := bstep (se 2 (by rfl) ⟨1066371, by rfl⟩ : syracuseStep 2843657 = 2132743) B2132743
theorem B1895771 : Blo 1895435 1895771 := bstep (se 1 (by rfl) ⟨1421828, by rfl⟩ : syracuseStep 1895771 = 2843657) B2843657
theorem B9597365 : Blo 1895435 9597365 := bbase (se 5 (by rfl) ⟨449876, by rfl⟩ : syracuseStep 9597365 = 899753) (by norm_num)
theorem B6398243 : Blo 1895435 6398243 := bstep (se 1 (by rfl) ⟨4798682, by rfl⟩ : syracuseStep 6398243 = 9597365) B9597365
theorem B4265495 : Blo 1895435 4265495 := bstep (se 1 (by rfl) ⟨3199121, by rfl⟩ : syracuseStep 4265495 = 6398243) B6398243
theorem B2843663 : Blo 1895435 2843663 := bstep (se 1 (by rfl) ⟨2132747, by rfl⟩ : syracuseStep 2843663 = 4265495) B4265495
theorem B1895775 : Blo 1895435 1895775 := bstep (se 1 (by rfl) ⟨1421831, by rfl⟩ : syracuseStep 1895775 = 2843663) B2843663
theorem B2843669 : Blo 1895435 2843669 := bbase (se 6 (by rfl) ⟨66648, by rfl⟩ : syracuseStep 2843669 = 133297) (by norm_num)
theorem B1895779 : Blo 1895435 1895779 := bstep (se 1 (by rfl) ⟨1421834, by rfl⟩ : syracuseStep 1895779 = 2843669) B2843669
theorem B4930541 : Blo 1895435 4930541 := bbase (se 3 (by rfl) ⟨924476, by rfl⟩ : syracuseStep 4930541 = 1848953) (by norm_num)
theorem B3287027 : Blo 1895435 3287027 := bstep (se 1 (by rfl) ⟨2465270, by rfl⟩ : syracuseStep 3287027 = 4930541) B4930541
theorem B8765405 : Blo 1895435 8765405 := bstep (se 3 (by rfl) ⟨1643513, by rfl⟩ : syracuseStep 8765405 = 3287027) B3287027
theorem B5843603 : Blo 1895435 5843603 := bstep (se 1 (by rfl) ⟨4382702, by rfl⟩ : syracuseStep 5843603 = 8765405) B8765405
theorem B3895735 : Blo 1895435 3895735 := bstep (se 1 (by rfl) ⟨2921801, by rfl⟩ : syracuseStep 3895735 = 5843603) B5843603
theorem B5194313 : Blo 1895435 5194313 := bstep (se 2 (by rfl) ⟨1947867, by rfl⟩ : syracuseStep 5194313 = 3895735) B3895735
theorem B3462875 : Blo 1895435 3462875 := bstep (se 1 (by rfl) ⟨2597156, by rfl⟩ : syracuseStep 3462875 = 5194313) B5194313
theorem B2308583 : Blo 1895435 2308583 := bstep (se 1 (by rfl) ⟨1731437, by rfl⟩ : syracuseStep 2308583 = 3462875) B3462875
theorem B6156221 : Blo 1895435 6156221 := bstep (se 3 (by rfl) ⟨1154291, by rfl⟩ : syracuseStep 6156221 = 2308583) B2308583
theorem B16416589 : Blo 1895435 16416589 := bstep (se 3 (by rfl) ⟨3078110, by rfl⟩ : syracuseStep 16416589 = 6156221) B6156221
theorem B21888785 : Blo 1895435 21888785 := bstep (se 2 (by rfl) ⟨8208294, by rfl⟩ : syracuseStep 21888785 = 16416589) B16416589
theorem B14592523 : Blo 1895435 14592523 := bstep (se 1 (by rfl) ⟨10944392, by rfl⟩ : syracuseStep 14592523 = 21888785) B21888785
theorem B19456697 : Blo 1895435 19456697 := bstep (se 2 (by rfl) ⟨7296261, by rfl⟩ : syracuseStep 19456697 = 14592523) B14592523
theorem B51884525 : Blo 1895435 51884525 := bstep (se 3 (by rfl) ⟨9728348, by rfl⟩ : syracuseStep 51884525 = 19456697) B19456697
theorem B34589683 : Blo 1895435 34589683 := bstep (se 1 (by rfl) ⟨25942262, by rfl⟩ : syracuseStep 34589683 = 51884525) B51884525
theorem B46119577 : Blo 1895435 46119577 := bstep (se 2 (by rfl) ⟨17294841, by rfl⟩ : syracuseStep 46119577 = 34589683) B34589683
theorem B61492769 : Blo 1895435 61492769 := bstep (se 2 (by rfl) ⟨23059788, by rfl⟩ : syracuseStep 61492769 = 46119577) B46119577
theorem B40995179 : Blo 1895435 40995179 := bstep (se 1 (by rfl) ⟨30746384, by rfl⟩ : syracuseStep 40995179 = 61492769) B61492769
theorem B27330119 : Blo 1895435 27330119 := bstep (se 1 (by rfl) ⟨20497589, by rfl⟩ : syracuseStep 27330119 = 40995179) B40995179
theorem B18220079 : Blo 1895435 18220079 := bstep (se 1 (by rfl) ⟨13665059, by rfl⟩ : syracuseStep 18220079 = 27330119) B27330119
theorem B12146719 : Blo 1895435 12146719 := bstep (se 1 (by rfl) ⟨9110039, by rfl⟩ : syracuseStep 12146719 = 18220079) B18220079
theorem B16195625 : Blo 1895435 16195625 := bstep (se 2 (by rfl) ⟨6073359, by rfl⟩ : syracuseStep 16195625 = 12146719) B12146719
theorem B10797083 : Blo 1895435 10797083 := bstep (se 1 (by rfl) ⟨8097812, by rfl⟩ : syracuseStep 10797083 = 16195625) B16195625
theorem B7198055 : Blo 1895435 7198055 := bstep (se 1 (by rfl) ⟨5398541, by rfl⟩ : syracuseStep 7198055 = 10797083) B10797083
theorem B4798703 : Blo 1895435 4798703 := bstep (se 1 (by rfl) ⟨3599027, by rfl⟩ : syracuseStep 4798703 = 7198055) B7198055
theorem B3199135 : Blo 1895435 3199135 := bstep (se 1 (by rfl) ⟨2399351, by rfl⟩ : syracuseStep 3199135 = 4798703) B4798703
theorem B4265513 : Blo 1895435 4265513 := bstep (se 2 (by rfl) ⟨1599567, by rfl⟩ : syracuseStep 4265513 = 3199135) B3199135
theorem B2843675 : Blo 1895435 2843675 := bstep (se 1 (by rfl) ⟨2132756, by rfl⟩ : syracuseStep 2843675 = 4265513) B4265513
theorem B1895783 : Blo 1895435 1895783 := bstep (se 1 (by rfl) ⟨1421837, by rfl⟩ : syracuseStep 1895783 = 2843675) B2843675
theorem B2132761 : Blo 1895435 2132761 := bbase (se 2 (by rfl) ⟨799785, by rfl⟩ : syracuseStep 2132761 = 1599571) (by norm_num)
theorem B2843681 : Blo 1895435 2843681 := bstep (se 2 (by rfl) ⟨1066380, by rfl⟩ : syracuseStep 2843681 = 2132761) B2132761
theorem B1895787 : Blo 1895435 1895787 := bstep (se 1 (by rfl) ⟨1421840, by rfl⟩ : syracuseStep 1895787 = 2843681) B2843681
theorem B7198085 : Blo 1895435 7198085 := bbase (se 4 (by rfl) ⟨674820, by rfl⟩ : syracuseStep 7198085 = 1349641) (by norm_num)
theorem B4798723 : Blo 1895435 4798723 := bstep (se 1 (by rfl) ⟨3599042, by rfl⟩ : syracuseStep 4798723 = 7198085) B7198085
theorem B6398297 : Blo 1895435 6398297 := bstep (se 2 (by rfl) ⟨2399361, by rfl⟩ : syracuseStep 6398297 = 4798723) B4798723
theorem B4265531 : Blo 1895435 4265531 := bstep (se 1 (by rfl) ⟨3199148, by rfl⟩ : syracuseStep 4265531 = 6398297) B6398297
theorem B2843687 : Blo 1895435 2843687 := bstep (se 1 (by rfl) ⟨2132765, by rfl⟩ : syracuseStep 2843687 = 4265531) B4265531
theorem B1895791 : Blo 1895435 1895791 := bstep (se 1 (by rfl) ⟨1421843, by rfl⟩ : syracuseStep 1895791 = 2843687) B2843687
theorem B2843693 : Blo 1895435 2843693 := bbase (se 3 (by rfl) ⟨533192, by rfl⟩ : syracuseStep 2843693 = 1066385) (by norm_num)
theorem B1895795 : Blo 1895435 1895795 := bstep (se 1 (by rfl) ⟨1421846, by rfl⟩ : syracuseStep 1895795 = 2843693) B2843693
theorem B4265549 : Blo 1895435 4265549 := bbase (se 3 (by rfl) ⟨799790, by rfl⟩ : syracuseStep 4265549 = 1599581) (by norm_num)
theorem B2843699 : Blo 1895435 2843699 := bstep (se 1 (by rfl) ⟨2132774, by rfl⟩ : syracuseStep 2843699 = 4265549) B4265549
theorem B1895799 : Blo 1895435 1895799 := bstep (se 1 (by rfl) ⟨1421849, by rfl⟩ : syracuseStep 1895799 = 2843699) B2843699
theorem B2399377 : Blo 1895435 2399377 := bbase (se 2 (by rfl) ⟨899766, by rfl⟩ : syracuseStep 2399377 = 1799533) (by norm_num)
theorem B3199169 : Blo 1895435 3199169 := bstep (se 2 (by rfl) ⟨1199688, by rfl⟩ : syracuseStep 3199169 = 2399377) B2399377
theorem B2132779 : Blo 1895435 2132779 := bstep (se 1 (by rfl) ⟨1599584, by rfl⟩ : syracuseStep 2132779 = 3199169) B3199169
theorem B2843705 : Blo 1895435 2843705 := bstep (se 2 (by rfl) ⟨1066389, by rfl⟩ : syracuseStep 2843705 = 2132779) B2132779
theorem B1895803 : Blo 1895435 1895803 := bstep (se 1 (by rfl) ⟨1421852, by rfl⟩ : syracuseStep 1895803 = 2843705) B2843705
theorem B4048957 : Blo 1895435 4048957 := bbase (se 3 (by rfl) ⟨759179, by rfl⟩ : syracuseStep 4048957 = 1518359) (by norm_num)
theorem B21594437 : Blo 1895435 21594437 := bstep (se 4 (by rfl) ⟨2024478, by rfl⟩ : syracuseStep 21594437 = 4048957) B4048957
theorem B14396291 : Blo 1895435 14396291 := bstep (se 1 (by rfl) ⟨10797218, by rfl⟩ : syracuseStep 14396291 = 21594437) B21594437
theorem B9597527 : Blo 1895435 9597527 := bstep (se 1 (by rfl) ⟨7198145, by rfl⟩ : syracuseStep 9597527 = 14396291) B14396291
theorem B6398351 : Blo 1895435 6398351 := bstep (se 1 (by rfl) ⟨4798763, by rfl⟩ : syracuseStep 6398351 = 9597527) B9597527
theorem B4265567 : Blo 1895435 4265567 := bstep (se 1 (by rfl) ⟨3199175, by rfl⟩ : syracuseStep 4265567 = 6398351) B6398351
theorem B2843711 : Blo 1895435 2843711 := bstep (se 1 (by rfl) ⟨2132783, by rfl⟩ : syracuseStep 2843711 = 4265567) B4265567
theorem B1895807 : Blo 1895435 1895807 := bstep (se 1 (by rfl) ⟨1421855, by rfl⟩ : syracuseStep 1895807 = 2843711) B2843711
theorem B2843717 : Blo 1895435 2843717 := bbase (se 4 (by rfl) ⟨266598, by rfl⟩ : syracuseStep 2843717 = 533197) (by norm_num)
theorem B1895811 : Blo 1895435 1895811 := bstep (se 1 (by rfl) ⟨1421858, by rfl⟩ : syracuseStep 1895811 = 2843717) B2843717
theorem B3199189 : Blo 1895435 3199189 := bbase (se 7 (by rfl) ⟨37490, by rfl⟩ : syracuseStep 3199189 = 74981) (by norm_num)
theorem B4265585 : Blo 1895435 4265585 := bstep (se 2 (by rfl) ⟨1599594, by rfl⟩ : syracuseStep 4265585 = 3199189) B3199189
theorem B2843723 : Blo 1895435 2843723 := bstep (se 1 (by rfl) ⟨2132792, by rfl⟩ : syracuseStep 2843723 = 4265585) B4265585
theorem B1895815 : Blo 1895435 1895815 := bstep (se 1 (by rfl) ⟨1421861, by rfl⟩ : syracuseStep 1895815 = 2843723) B2843723
theorem B2132797 : Blo 1895435 2132797 := bbase (se 3 (by rfl) ⟨399899, by rfl⟩ : syracuseStep 2132797 = 799799) (by norm_num)
theorem B2843729 : Blo 1895435 2843729 := bstep (se 2 (by rfl) ⟨1066398, by rfl⟩ : syracuseStep 2843729 = 2132797) B2132797
theorem B1895819 : Blo 1895435 1895819 := bstep (se 1 (by rfl) ⟨1421864, by rfl⟩ : syracuseStep 1895819 = 2843729) B2843729
theorem B6398405 : Blo 1895435 6398405 := bbase (se 4 (by rfl) ⟨599850, by rfl⟩ : syracuseStep 6398405 = 1199701) (by norm_num)
theorem B4265603 : Blo 1895435 4265603 := bstep (se 1 (by rfl) ⟨3199202, by rfl⟩ : syracuseStep 4265603 = 6398405) B6398405
theorem B2843735 : Blo 1895435 2843735 := bstep (se 1 (by rfl) ⟨2132801, by rfl⟩ : syracuseStep 2843735 = 4265603) B4265603
theorem B1895823 : Blo 1895435 1895823 := bstep (se 1 (by rfl) ⟨1421867, by rfl⟩ : syracuseStep 1895823 = 2843735) B2843735
theorem B2843741 : Blo 1895435 2843741 := bbase (se 3 (by rfl) ⟨533201, by rfl⟩ : syracuseStep 2843741 = 1066403) (by norm_num)
theorem B1895827 : Blo 1895435 1895827 := bstep (se 1 (by rfl) ⟨1421870, by rfl⟩ : syracuseStep 1895827 = 2843741) B2843741
theorem B4265621 : Blo 1895435 4265621 := bbase (se 6 (by rfl) ⟨99975, by rfl⟩ : syracuseStep 4265621 = 199951) (by norm_num)
theorem B2843747 : Blo 1895435 2843747 := bstep (se 1 (by rfl) ⟨2132810, by rfl⟩ : syracuseStep 2843747 = 4265621) B4265621
theorem B1895831 : Blo 1895435 1895831 := bstep (se 1 (by rfl) ⟨1421873, by rfl⟩ : syracuseStep 1895831 = 2843747) B2843747
theorem B2024509 : Blo 1895435 2024509 := bbase (se 3 (by rfl) ⟨379595, by rfl⟩ : syracuseStep 2024509 = 759191) (by norm_num)
theorem B2699345 : Blo 1895435 2699345 := bstep (se 2 (by rfl) ⟨1012254, by rfl⟩ : syracuseStep 2699345 = 2024509) B2024509
theorem B7198253 : Blo 1895435 7198253 := bstep (se 3 (by rfl) ⟨1349672, by rfl⟩ : syracuseStep 7198253 = 2699345) B2699345
theorem B4798835 : Blo 1895435 4798835 := bstep (se 1 (by rfl) ⟨3599126, by rfl⟩ : syracuseStep 4798835 = 7198253) B7198253
theorem B3199223 : Blo 1895435 3199223 := bstep (se 1 (by rfl) ⟨2399417, by rfl⟩ : syracuseStep 3199223 = 4798835) B4798835
theorem B2132815 : Blo 1895435 2132815 := bstep (se 1 (by rfl) ⟨1599611, by rfl⟩ : syracuseStep 2132815 = 3199223) B3199223
theorem B2843753 : Blo 1895435 2843753 := bstep (se 2 (by rfl) ⟨1066407, by rfl⟩ : syracuseStep 2843753 = 2132815) B2132815
theorem B1895835 : Blo 1895435 1895835 := bstep (se 1 (by rfl) ⟨1421876, by rfl⟩ : syracuseStep 1895835 = 2843753) B2843753
theorem B2277577 : Blo 1895435 2277577 := bbase (se 2 (by rfl) ⟨854091, by rfl⟩ : syracuseStep 2277577 = 1708183) (by norm_num)
theorem B12147077 : Blo 1895435 12147077 := bstep (se 4 (by rfl) ⟨1138788, by rfl⟩ : syracuseStep 12147077 = 2277577) B2277577
theorem B8098051 : Blo 1895435 8098051 := bstep (se 1 (by rfl) ⟨6073538, by rfl⟩ : syracuseStep 8098051 = 12147077) B12147077
theorem B10797401 : Blo 1895435 10797401 := bstep (se 2 (by rfl) ⟨4049025, by rfl⟩ : syracuseStep 10797401 = 8098051) B8098051
theorem B7198267 : Blo 1895435 7198267 := bstep (se 1 (by rfl) ⟨5398700, by rfl⟩ : syracuseStep 7198267 = 10797401) B10797401
theorem B9597689 : Blo 1895435 9597689 := bstep (se 2 (by rfl) ⟨3599133, by rfl⟩ : syracuseStep 9597689 = 7198267) B7198267
theorem B6398459 : Blo 1895435 6398459 := bstep (se 1 (by rfl) ⟨4798844, by rfl⟩ : syracuseStep 6398459 = 9597689) B9597689
theorem B4265639 : Blo 1895435 4265639 := bstep (se 1 (by rfl) ⟨3199229, by rfl⟩ : syracuseStep 4265639 = 6398459) B6398459
theorem B2843759 : Blo 1895435 2843759 := bstep (se 1 (by rfl) ⟨2132819, by rfl⟩ : syracuseStep 2843759 = 4265639) B4265639
theorem B1895839 : Blo 1895435 1895839 := bstep (se 1 (by rfl) ⟨1421879, by rfl⟩ : syracuseStep 1895839 = 2843759) B2843759
theorem B2843765 : Blo 1895435 2843765 := bbase (se 5 (by rfl) ⟨133301, by rfl⟩ : syracuseStep 2843765 = 266603) (by norm_num)
theorem B1895843 : Blo 1895435 1895843 := bstep (se 1 (by rfl) ⟨1421882, by rfl⟩ : syracuseStep 1895843 = 2843765) B2843765
theorem B3599149 : Blo 1895435 3599149 := bbase (se 3 (by rfl) ⟨674840, by rfl⟩ : syracuseStep 3599149 = 1349681) (by norm_num)
theorem B4798865 : Blo 1895435 4798865 := bstep (se 2 (by rfl) ⟨1799574, by rfl⟩ : syracuseStep 4798865 = 3599149) B3599149
theorem B3199243 : Blo 1895435 3199243 := bstep (se 1 (by rfl) ⟨2399432, by rfl⟩ : syracuseStep 3199243 = 4798865) B4798865
theorem B4265657 : Blo 1895435 4265657 := bstep (se 2 (by rfl) ⟨1599621, by rfl⟩ : syracuseStep 4265657 = 3199243) B3199243
theorem B2843771 : Blo 1895435 2843771 := bstep (se 1 (by rfl) ⟨2132828, by rfl⟩ : syracuseStep 2843771 = 4265657) B4265657
theorem B1895847 : Blo 1895435 1895847 := bstep (se 1 (by rfl) ⟨1421885, by rfl⟩ : syracuseStep 1895847 = 2843771) B2843771
theorem B2132833 : Blo 1895435 2132833 := bbase (se 2 (by rfl) ⟨799812, by rfl⟩ : syracuseStep 2132833 = 1599625) (by norm_num)
theorem B2843777 : Blo 1895435 2843777 := bstep (se 2 (by rfl) ⟨1066416, by rfl⟩ : syracuseStep 2843777 = 2132833) B2132833
theorem B1895851 : Blo 1895435 1895851 := bstep (se 1 (by rfl) ⟨1421888, by rfl⟩ : syracuseStep 1895851 = 2843777) B2843777
theorem B4798885 : Blo 1895435 4798885 := bbase (se 4 (by rfl) ⟨449895, by rfl⟩ : syracuseStep 4798885 = 899791) (by norm_num)
theorem B6398513 : Blo 1895435 6398513 := bstep (se 2 (by rfl) ⟨2399442, by rfl⟩ : syracuseStep 6398513 = 4798885) B4798885
theorem B4265675 : Blo 1895435 4265675 := bstep (se 1 (by rfl) ⟨3199256, by rfl⟩ : syracuseStep 4265675 = 6398513) B6398513
theorem B2843783 : Blo 1895435 2843783 := bstep (se 1 (by rfl) ⟨2132837, by rfl⟩ : syracuseStep 2843783 = 4265675) B4265675
theorem B1895855 : Blo 1895435 1895855 := bstep (se 1 (by rfl) ⟨1421891, by rfl⟩ : syracuseStep 1895855 = 2843783) B2843783
theorem B2843789 : Blo 1895435 2843789 := bbase (se 3 (by rfl) ⟨533210, by rfl⟩ : syracuseStep 2843789 = 1066421) (by norm_num)
theorem B1895859 : Blo 1895435 1895859 := bstep (se 1 (by rfl) ⟨1421894, by rfl⟩ : syracuseStep 1895859 = 2843789) B2843789
theorem B4265693 : Blo 1895435 4265693 := bbase (se 3 (by rfl) ⟨799817, by rfl⟩ : syracuseStep 4265693 = 1599635) (by norm_num)
theorem B2843795 : Blo 1895435 2843795 := bstep (se 1 (by rfl) ⟨2132846, by rfl⟩ : syracuseStep 2843795 = 4265693) B4265693
theorem B1895863 : Blo 1895435 1895863 := bstep (se 1 (by rfl) ⟨1421897, by rfl⟩ : syracuseStep 1895863 = 2843795) B2843795
theorem B3199277 : Blo 1895435 3199277 := bbase (se 3 (by rfl) ⟨599864, by rfl⟩ : syracuseStep 3199277 = 1199729) (by norm_num)
theorem B2132851 : Blo 1895435 2132851 := bstep (se 1 (by rfl) ⟨1599638, by rfl⟩ : syracuseStep 2132851 = 3199277) B3199277
theorem B2843801 : Blo 1895435 2843801 := bstep (se 2 (by rfl) ⟨1066425, by rfl⟩ : syracuseStep 2843801 = 2132851) B2132851
theorem B1895867 : Blo 1895435 1895867 := bstep (se 1 (by rfl) ⟨1421900, by rfl⟩ : syracuseStep 1895867 = 2843801) B2843801
theorem B8208677 : Blo 1895435 8208677 := bbase (se 4 (by rfl) ⟨769563, by rfl⟩ : syracuseStep 8208677 = 1539127) (by norm_num)
theorem B5472451 : Blo 1895435 5472451 := bstep (se 1 (by rfl) ⟨4104338, by rfl⟩ : syracuseStep 5472451 = 8208677) B8208677
theorem B29186405 : Blo 1895435 29186405 := bstep (se 4 (by rfl) ⟨2736225, by rfl⟩ : syracuseStep 29186405 = 5472451) B5472451
theorem B19457603 : Blo 1895435 19457603 := bstep (se 1 (by rfl) ⟨14593202, by rfl⟩ : syracuseStep 19457603 = 29186405) B29186405
theorem B12971735 : Blo 1895435 12971735 := bstep (se 1 (by rfl) ⟨9728801, by rfl⟩ : syracuseStep 12971735 = 19457603) B19457603
theorem B8647823 : Blo 1895435 8647823 := bstep (se 1 (by rfl) ⟨6485867, by rfl⟩ : syracuseStep 8647823 = 12971735) B12971735
theorem B5765215 : Blo 1895435 5765215 := bstep (se 1 (by rfl) ⟨4323911, by rfl⟩ : syracuseStep 5765215 = 8647823) B8647823
theorem B7686953 : Blo 1895435 7686953 := bstep (se 2 (by rfl) ⟨2882607, by rfl⟩ : syracuseStep 7686953 = 5765215) B5765215
theorem B5124635 : Blo 1895435 5124635 := bstep (se 1 (by rfl) ⟨3843476, by rfl⟩ : syracuseStep 5124635 = 7686953) B7686953
theorem B3416423 : Blo 1895435 3416423 := bstep (se 1 (by rfl) ⟨2562317, by rfl⟩ : syracuseStep 3416423 = 5124635) B5124635
theorem B36441845 : Blo 1895435 36441845 := bstep (se 5 (by rfl) ⟨1708211, by rfl⟩ : syracuseStep 36441845 = 3416423) B3416423
theorem B24294563 : Blo 1895435 24294563 := bstep (se 1 (by rfl) ⟨18220922, by rfl⟩ : syracuseStep 24294563 = 36441845) B36441845
theorem B16196375 : Blo 1895435 16196375 := bstep (se 1 (by rfl) ⟨12147281, by rfl⟩ : syracuseStep 16196375 = 24294563) B24294563
theorem B10797583 : Blo 1895435 10797583 := bstep (se 1 (by rfl) ⟨8098187, by rfl⟩ : syracuseStep 10797583 = 16196375) B16196375
theorem B14396777 : Blo 1895435 14396777 := bstep (se 2 (by rfl) ⟨5398791, by rfl⟩ : syracuseStep 14396777 = 10797583) B10797583
theorem B9597851 : Blo 1895435 9597851 := bstep (se 1 (by rfl) ⟨7198388, by rfl⟩ : syracuseStep 9597851 = 14396777) B14396777
theorem B6398567 : Blo 1895435 6398567 := bstep (se 1 (by rfl) ⟨4798925, by rfl⟩ : syracuseStep 6398567 = 9597851) B9597851
theorem B4265711 : Blo 1895435 4265711 := bstep (se 1 (by rfl) ⟨3199283, by rfl⟩ : syracuseStep 4265711 = 6398567) B6398567
theorem B2843807 : Blo 1895435 2843807 := bstep (se 1 (by rfl) ⟨2132855, by rfl⟩ : syracuseStep 2843807 = 4265711) B4265711
theorem B1895871 : Blo 1895435 1895871 := bstep (se 1 (by rfl) ⟨1421903, by rfl⟩ : syracuseStep 1895871 = 2843807) B2843807
theorem B2843813 : Blo 1895435 2843813 := bbase (se 4 (by rfl) ⟨266607, by rfl⟩ : syracuseStep 2843813 = 533215) (by norm_num)
theorem B1895875 : Blo 1895435 1895875 := bstep (se 1 (by rfl) ⟨1421906, by rfl⟩ : syracuseStep 1895875 = 2843813) B2843813
theorem B2399473 : Blo 1895435 2399473 := bbase (se 2 (by rfl) ⟨899802, by rfl⟩ : syracuseStep 2399473 = 1799605) (by norm_num)
theorem B3199297 : Blo 1895435 3199297 := bstep (se 2 (by rfl) ⟨1199736, by rfl⟩ : syracuseStep 3199297 = 2399473) B2399473
theorem B4265729 : Blo 1895435 4265729 := bstep (se 2 (by rfl) ⟨1599648, by rfl⟩ : syracuseStep 4265729 = 3199297) B3199297
theorem B2843819 : Blo 1895435 2843819 := bstep (se 1 (by rfl) ⟨2132864, by rfl⟩ : syracuseStep 2843819 = 4265729) B4265729
theorem B1895879 : Blo 1895435 1895879 := bstep (se 1 (by rfl) ⟨1421909, by rfl⟩ : syracuseStep 1895879 = 2843819) B2843819
theorem B2132869 : Blo 1895435 2132869 := bbase (se 4 (by rfl) ⟨199956, by rfl⟩ : syracuseStep 2132869 = 399913) (by norm_num)
theorem B2843825 : Blo 1895435 2843825 := bstep (se 2 (by rfl) ⟨1066434, by rfl⟩ : syracuseStep 2843825 = 2132869) B2132869
theorem B1895883 : Blo 1895435 1895883 := bstep (se 1 (by rfl) ⟨1421912, by rfl⟩ : syracuseStep 1895883 = 2843825) B2843825
theorem B4864445 : Blo 1895435 4864445 := bbase (se 3 (by rfl) ⟨912083, by rfl⟩ : syracuseStep 4864445 = 1824167) (by norm_num)
theorem B3242963 : Blo 1895435 3242963 := bstep (se 1 (by rfl) ⟨2432222, by rfl⟩ : syracuseStep 3242963 = 4864445) B4864445
theorem B2161975 : Blo 1895435 2161975 := bstep (se 1 (by rfl) ⟨1621481, by rfl⟩ : syracuseStep 2161975 = 3242963) B3242963
theorem B2882633 : Blo 1895435 2882633 := bstep (se 2 (by rfl) ⟨1080987, by rfl⟩ : syracuseStep 2882633 = 2161975) B2161975
theorem B7687021 : Blo 1895435 7687021 := bstep (se 3 (by rfl) ⟨1441316, by rfl⟩ : syracuseStep 7687021 = 2882633) B2882633
theorem B10249361 : Blo 1895435 10249361 := bstep (se 2 (by rfl) ⟨3843510, by rfl⟩ : syracuseStep 10249361 = 7687021) B7687021
theorem B6832907 : Blo 1895435 6832907 := bstep (se 1 (by rfl) ⟨5124680, by rfl⟩ : syracuseStep 6832907 = 10249361) B10249361
theorem B4555271 : Blo 1895435 4555271 := bstep (se 1 (by rfl) ⟨3416453, by rfl⟩ : syracuseStep 4555271 = 6832907) B6832907
theorem B3036847 : Blo 1895435 3036847 := bstep (se 1 (by rfl) ⟨2277635, by rfl⟩ : syracuseStep 3036847 = 4555271) B4555271
theorem B4049129 : Blo 1895435 4049129 := bstep (se 2 (by rfl) ⟨1518423, by rfl⟩ : syracuseStep 4049129 = 3036847) B3036847
theorem B2699419 : Blo 1895435 2699419 := bstep (se 1 (by rfl) ⟨2024564, by rfl⟩ : syracuseStep 2699419 = 4049129) B4049129
theorem B3599225 : Blo 1895435 3599225 := bstep (se 2 (by rfl) ⟨1349709, by rfl⟩ : syracuseStep 3599225 = 2699419) B2699419
theorem B2399483 : Blo 1895435 2399483 := bstep (se 1 (by rfl) ⟨1799612, by rfl⟩ : syracuseStep 2399483 = 3599225) B3599225
theorem B6398621 : Blo 1895435 6398621 := bstep (se 3 (by rfl) ⟨1199741, by rfl⟩ : syracuseStep 6398621 = 2399483) B2399483
theorem B4265747 : Blo 1895435 4265747 := bstep (se 1 (by rfl) ⟨3199310, by rfl⟩ : syracuseStep 4265747 = 6398621) B6398621
theorem B2843831 : Blo 1895435 2843831 := bstep (se 1 (by rfl) ⟨2132873, by rfl⟩ : syracuseStep 2843831 = 4265747) B4265747
theorem B1895887 : Blo 1895435 1895887 := bstep (se 1 (by rfl) ⟨1421915, by rfl⟩ : syracuseStep 1895887 = 2843831) B2843831
theorem B2843837 : Blo 1895435 2843837 := bbase (se 3 (by rfl) ⟨533219, by rfl⟩ : syracuseStep 2843837 = 1066439) (by norm_num)
theorem B1895891 : Blo 1895435 1895891 := bstep (se 1 (by rfl) ⟨1421918, by rfl⟩ : syracuseStep 1895891 = 2843837) B2843837
theorem B4265765 : Blo 1895435 4265765 := bbase (se 4 (by rfl) ⟨399915, by rfl⟩ : syracuseStep 4265765 = 799831) (by norm_num)
theorem B2843843 : Blo 1895435 2843843 := bstep (se 1 (by rfl) ⟨2132882, by rfl⟩ : syracuseStep 2843843 = 4265765) B4265765
theorem B1895895 : Blo 1895435 1895895 := bstep (se 1 (by rfl) ⟨1421921, by rfl⟩ : syracuseStep 1895895 = 2843843) B2843843
theorem B4798997 : Blo 1895435 4798997 := bbase (se 6 (by rfl) ⟨112476, by rfl⟩ : syracuseStep 4798997 = 224953) (by norm_num)
theorem B3199331 : Blo 1895435 3199331 := bstep (se 1 (by rfl) ⟨2399498, by rfl⟩ : syracuseStep 3199331 = 4798997) B4798997
theorem B2132887 : Blo 1895435 2132887 := bstep (se 1 (by rfl) ⟨1599665, by rfl⟩ : syracuseStep 2132887 = 3199331) B3199331
theorem B2843849 : Blo 1895435 2843849 := bstep (se 2 (by rfl) ⟨1066443, by rfl⟩ : syracuseStep 2843849 = 2132887) B2132887
theorem B1895899 : Blo 1895435 1895899 := bstep (se 1 (by rfl) ⟨1421924, by rfl⟩ : syracuseStep 1895899 = 2843849) B2843849
theorem B8098325 : Blo 1895435 8098325 := bbase (se 6 (by rfl) ⟨189804, by rfl⟩ : syracuseStep 8098325 = 379609) (by norm_num)
theorem B5398883 : Blo 1895435 5398883 := bstep (se 1 (by rfl) ⟨4049162, by rfl⟩ : syracuseStep 5398883 = 8098325) B8098325
theorem B3599255 : Blo 1895435 3599255 := bstep (se 1 (by rfl) ⟨2699441, by rfl⟩ : syracuseStep 3599255 = 5398883) B5398883
theorem B9598013 : Blo 1895435 9598013 := bstep (se 3 (by rfl) ⟨1799627, by rfl⟩ : syracuseStep 9598013 = 3599255) B3599255
theorem B6398675 : Blo 1895435 6398675 := bstep (se 1 (by rfl) ⟨4799006, by rfl⟩ : syracuseStep 6398675 = 9598013) B9598013
theorem B4265783 : Blo 1895435 4265783 := bstep (se 1 (by rfl) ⟨3199337, by rfl⟩ : syracuseStep 4265783 = 6398675) B6398675
theorem B2843855 : Blo 1895435 2843855 := bstep (se 1 (by rfl) ⟨2132891, by rfl⟩ : syracuseStep 2843855 = 4265783) B4265783
theorem B1895903 : Blo 1895435 1895903 := bstep (se 1 (by rfl) ⟨1421927, by rfl⟩ : syracuseStep 1895903 = 2843855) B2843855
theorem B2843861 : Blo 1895435 2843861 := bbase (se 7 (by rfl) ⟨33326, by rfl⟩ : syracuseStep 2843861 = 66653) (by norm_num)
theorem B1895907 : Blo 1895435 1895907 := bstep (se 1 (by rfl) ⟨1421930, by rfl⟩ : syracuseStep 1895907 = 2843861) B2843861
theorem B2699453 : Blo 1895435 2699453 := bbase (se 3 (by rfl) ⟨506147, by rfl⟩ : syracuseStep 2699453 = 1012295) (by norm_num)
theorem B7198541 : Blo 1895435 7198541 := bstep (se 3 (by rfl) ⟨1349726, by rfl⟩ : syracuseStep 7198541 = 2699453) B2699453
theorem B4799027 : Blo 1895435 4799027 := bstep (se 1 (by rfl) ⟨3599270, by rfl⟩ : syracuseStep 4799027 = 7198541) B7198541
theorem B3199351 : Blo 1895435 3199351 := bstep (se 1 (by rfl) ⟨2399513, by rfl⟩ : syracuseStep 3199351 = 4799027) B4799027
theorem B4265801 : Blo 1895435 4265801 := bstep (se 2 (by rfl) ⟨1599675, by rfl⟩ : syracuseStep 4265801 = 3199351) B3199351
theorem B2843867 : Blo 1895435 2843867 := bstep (se 1 (by rfl) ⟨2132900, by rfl⟩ : syracuseStep 2843867 = 4265801) B4265801
theorem B1895911 : Blo 1895435 1895911 := bstep (se 1 (by rfl) ⟨1421933, by rfl⟩ : syracuseStep 1895911 = 2843867) B2843867
theorem B2132905 : Blo 1895435 2132905 := bbase (se 2 (by rfl) ⟨799839, by rfl⟩ : syracuseStep 2132905 = 1599679) (by norm_num)
theorem B2843873 : Blo 1895435 2843873 := bstep (se 2 (by rfl) ⟨1066452, by rfl⟩ : syracuseStep 2843873 = 2132905) B2132905
theorem B1895915 : Blo 1895435 1895915 := bstep (se 1 (by rfl) ⟨1421936, by rfl⟩ : syracuseStep 1895915 = 2843873) B2843873
theorem B9110693 : Blo 1895435 9110693 := bbase (se 4 (by rfl) ⟨854127, by rfl⟩ : syracuseStep 9110693 = 1708255) (by norm_num)
theorem B6073795 : Blo 1895435 6073795 := bstep (se 1 (by rfl) ⟨4555346, by rfl⟩ : syracuseStep 6073795 = 9110693) B9110693
theorem B8098393 : Blo 1895435 8098393 := bstep (se 2 (by rfl) ⟨3036897, by rfl⟩ : syracuseStep 8098393 = 6073795) B6073795
theorem B10797857 : Blo 1895435 10797857 := bstep (se 2 (by rfl) ⟨4049196, by rfl⟩ : syracuseStep 10797857 = 8098393) B8098393
theorem B7198571 : Blo 1895435 7198571 := bstep (se 1 (by rfl) ⟨5398928, by rfl⟩ : syracuseStep 7198571 = 10797857) B10797857
theorem B4799047 : Blo 1895435 4799047 := bstep (se 1 (by rfl) ⟨3599285, by rfl⟩ : syracuseStep 4799047 = 7198571) B7198571
theorem B6398729 : Blo 1895435 6398729 := bstep (se 2 (by rfl) ⟨2399523, by rfl⟩ : syracuseStep 6398729 = 4799047) B4799047
theorem B4265819 : Blo 1895435 4265819 := bstep (se 1 (by rfl) ⟨3199364, by rfl⟩ : syracuseStep 4265819 = 6398729) B6398729
theorem B2843879 : Blo 1895435 2843879 := bstep (se 1 (by rfl) ⟨2132909, by rfl⟩ : syracuseStep 2843879 = 4265819) B4265819
theorem B1895919 : Blo 1895435 1895919 := bstep (se 1 (by rfl) ⟨1421939, by rfl⟩ : syracuseStep 1895919 = 2843879) B2843879
theorem B2843885 : Blo 1895435 2843885 := bbase (se 3 (by rfl) ⟨533228, by rfl⟩ : syracuseStep 2843885 = 1066457) (by norm_num)
theorem B1895923 : Blo 1895435 1895923 := bstep (se 1 (by rfl) ⟨1421942, by rfl⟩ : syracuseStep 1895923 = 2843885) B2843885
theorem B4265837 : Blo 1895435 4265837 := bbase (se 3 (by rfl) ⟨799844, by rfl⟩ : syracuseStep 4265837 = 1599689) (by norm_num)
theorem B2843891 : Blo 1895435 2843891 := bstep (se 1 (by rfl) ⟨2132918, by rfl⟩ : syracuseStep 2843891 = 4265837) B4265837
theorem B1895927 : Blo 1895435 1895927 := bstep (se 1 (by rfl) ⟨1421945, by rfl⟩ : syracuseStep 1895927 = 2843891) B2843891
theorem B3599309 : Blo 1895435 3599309 := bbase (se 3 (by rfl) ⟨674870, by rfl⟩ : syracuseStep 3599309 = 1349741) (by norm_num)
theorem B2399539 : Blo 1895435 2399539 := bstep (se 1 (by rfl) ⟨1799654, by rfl⟩ : syracuseStep 2399539 = 3599309) B3599309
theorem B3199385 : Blo 1895435 3199385 := bstep (se 2 (by rfl) ⟨1199769, by rfl⟩ : syracuseStep 3199385 = 2399539) B2399539
theorem B2132923 : Blo 1895435 2132923 := bstep (se 1 (by rfl) ⟨1599692, by rfl⟩ : syracuseStep 2132923 = 3199385) B3199385
theorem B2843897 : Blo 1895435 2843897 := bstep (se 2 (by rfl) ⟨1066461, by rfl⟩ : syracuseStep 2843897 = 2132923) B2132923
theorem B1895931 : Blo 1895435 1895931 := bstep (se 1 (by rfl) ⟨1421948, by rfl⟩ : syracuseStep 1895931 = 2843897) B2843897
theorem B6486085 : Blo 1895435 6486085 := bbase (se 4 (by rfl) ⟨608070, by rfl⟩ : syracuseStep 6486085 = 1216141) (by norm_num)
theorem B34592453 : Blo 1895435 34592453 := bstep (se 4 (by rfl) ⟨3243042, by rfl⟩ : syracuseStep 34592453 = 6486085) B6486085
theorem B23061635 : Blo 1895435 23061635 := bstep (se 1 (by rfl) ⟨17296226, by rfl⟩ : syracuseStep 23061635 = 34592453) B34592453
theorem B15374423 : Blo 1895435 15374423 := bstep (se 1 (by rfl) ⟨11530817, by rfl⟩ : syracuseStep 15374423 = 23061635) B23061635
theorem B10249615 : Blo 1895435 10249615 := bstep (se 1 (by rfl) ⟨7687211, by rfl⟩ : syracuseStep 10249615 = 15374423) B15374423
theorem B13666153 : Blo 1895435 13666153 := bstep (se 2 (by rfl) ⟨5124807, by rfl⟩ : syracuseStep 13666153 = 10249615) B10249615
theorem B18221537 : Blo 1895435 18221537 := bstep (se 2 (by rfl) ⟨6833076, by rfl⟩ : syracuseStep 18221537 = 13666153) B13666153
theorem B48590765 : Blo 1895435 48590765 := bstep (se 3 (by rfl) ⟨9110768, by rfl⟩ : syracuseStep 48590765 = 18221537) B18221537
theorem B32393843 : Blo 1895435 32393843 := bstep (se 1 (by rfl) ⟨24295382, by rfl⟩ : syracuseStep 32393843 = 48590765) B48590765
theorem B21595895 : Blo 1895435 21595895 := bstep (se 1 (by rfl) ⟨16196921, by rfl⟩ : syracuseStep 21595895 = 32393843) B32393843
theorem B14397263 : Blo 1895435 14397263 := bstep (se 1 (by rfl) ⟨10797947, by rfl⟩ : syracuseStep 14397263 = 21595895) B21595895
theorem B9598175 : Blo 1895435 9598175 := bstep (se 1 (by rfl) ⟨7198631, by rfl⟩ : syracuseStep 9598175 = 14397263) B14397263
theorem B6398783 : Blo 1895435 6398783 := bstep (se 1 (by rfl) ⟨4799087, by rfl⟩ : syracuseStep 6398783 = 9598175) B9598175
theorem B4265855 : Blo 1895435 4265855 := bstep (se 1 (by rfl) ⟨3199391, by rfl⟩ : syracuseStep 4265855 = 6398783) B6398783
theorem B2843903 : Blo 1895435 2843903 := bstep (se 1 (by rfl) ⟨2132927, by rfl⟩ : syracuseStep 2843903 = 4265855) B4265855
theorem B1895935 : Blo 1895435 1895935 := bstep (se 1 (by rfl) ⟨1421951, by rfl⟩ : syracuseStep 1895935 = 2843903) B2843903
theorem B2843909 : Blo 1895435 2843909 := bbase (se 4 (by rfl) ⟨266616, by rfl⟩ : syracuseStep 2843909 = 533233) (by norm_num)
theorem B1895939 : Blo 1895435 1895939 := bstep (se 1 (by rfl) ⟨1421954, by rfl⟩ : syracuseStep 1895939 = 2843909) B2843909
theorem B3199405 : Blo 1895435 3199405 := bbase (se 3 (by rfl) ⟨599888, by rfl⟩ : syracuseStep 3199405 = 1199777) (by norm_num)
theorem B4265873 : Blo 1895435 4265873 := bstep (se 2 (by rfl) ⟨1599702, by rfl⟩ : syracuseStep 4265873 = 3199405) B3199405
theorem B2843915 : Blo 1895435 2843915 := bstep (se 1 (by rfl) ⟨2132936, by rfl⟩ : syracuseStep 2843915 = 4265873) B4265873
theorem B1895943 : Blo 1895435 1895943 := bstep (se 1 (by rfl) ⟨1421957, by rfl⟩ : syracuseStep 1895943 = 2843915) B2843915
theorem B2132941 : Blo 1895435 2132941 := bbase (se 3 (by rfl) ⟨399926, by rfl⟩ : syracuseStep 2132941 = 799853) (by norm_num)
theorem B2843921 : Blo 1895435 2843921 := bstep (se 2 (by rfl) ⟨1066470, by rfl⟩ : syracuseStep 2843921 = 2132941) B2132941
theorem B1895947 : Blo 1895435 1895947 := bstep (se 1 (by rfl) ⟨1421960, by rfl⟩ : syracuseStep 1895947 = 2843921) B2843921
theorem B6398837 : Blo 1895435 6398837 := bbase (se 5 (by rfl) ⟨299945, by rfl⟩ : syracuseStep 6398837 = 599891) (by norm_num)
theorem B4265891 : Blo 1895435 4265891 := bstep (se 1 (by rfl) ⟨3199418, by rfl⟩ : syracuseStep 4265891 = 6398837) B6398837
theorem B2843927 : Blo 1895435 2843927 := bstep (se 1 (by rfl) ⟨2132945, by rfl⟩ : syracuseStep 2843927 = 4265891) B4265891
theorem B1895951 : Blo 1895435 1895951 := bstep (se 1 (by rfl) ⟨1421963, by rfl⟩ : syracuseStep 1895951 = 2843927) B2843927
theorem B2843933 : Blo 1895435 2843933 := bbase (se 3 (by rfl) ⟨533237, by rfl⟩ : syracuseStep 2843933 = 1066475) (by norm_num)
theorem B1895955 : Blo 1895435 1895955 := bstep (se 1 (by rfl) ⟨1421966, by rfl⟩ : syracuseStep 1895955 = 2843933) B2843933
theorem B4265909 : Blo 1895435 4265909 := bbase (se 5 (by rfl) ⟨199964, by rfl⟩ : syracuseStep 4265909 = 399929) (by norm_num)
theorem B2843939 : Blo 1895435 2843939 := bstep (se 1 (by rfl) ⟨2132954, by rfl⟩ : syracuseStep 2843939 = 4265909) B4265909
theorem B1895959 : Blo 1895435 1895959 := bstep (se 1 (by rfl) ⟨1421969, by rfl⟩ : syracuseStep 1895959 = 2843939) B2843939
theorem B4555453 : Blo 1895435 4555453 := bbase (se 3 (by rfl) ⟨854147, by rfl⟩ : syracuseStep 4555453 = 1708295) (by norm_num)
theorem B6073937 : Blo 1895435 6073937 := bstep (se 2 (by rfl) ⟨2277726, by rfl⟩ : syracuseStep 6073937 = 4555453) B4555453
theorem B4049291 : Blo 1895435 4049291 := bstep (se 1 (by rfl) ⟨3036968, by rfl⟩ : syracuseStep 4049291 = 6073937) B6073937
theorem B10798109 : Blo 1895435 10798109 := bstep (se 3 (by rfl) ⟨2024645, by rfl⟩ : syracuseStep 10798109 = 4049291) B4049291
theorem B7198739 : Blo 1895435 7198739 := bstep (se 1 (by rfl) ⟨5399054, by rfl⟩ : syracuseStep 7198739 = 10798109) B10798109
theorem B4799159 : Blo 1895435 4799159 := bstep (se 1 (by rfl) ⟨3599369, by rfl⟩ : syracuseStep 4799159 = 7198739) B7198739
theorem B3199439 : Blo 1895435 3199439 := bstep (se 1 (by rfl) ⟨2399579, by rfl⟩ : syracuseStep 3199439 = 4799159) B4799159
theorem B2132959 : Blo 1895435 2132959 := bstep (se 1 (by rfl) ⟨1599719, by rfl⟩ : syracuseStep 2132959 = 3199439) B3199439
theorem B2843945 : Blo 1895435 2843945 := bstep (se 2 (by rfl) ⟨1066479, by rfl⟩ : syracuseStep 2843945 = 2132959) B2132959
theorem B1895963 : Blo 1895435 1895963 := bstep (se 1 (by rfl) ⟨1421972, by rfl⟩ : syracuseStep 1895963 = 2843945) B2843945
theorem B3416597 : Blo 1895435 3416597 := bbase (se 6 (by rfl) ⟨80076, by rfl⟩ : syracuseStep 3416597 = 160153) (by norm_num)
theorem B2277731 : Blo 1895435 2277731 := bstep (se 1 (by rfl) ⟨1708298, by rfl⟩ : syracuseStep 2277731 = 3416597) B3416597
theorem B6073949 : Blo 1895435 6073949 := bstep (se 3 (by rfl) ⟨1138865, by rfl⟩ : syracuseStep 6073949 = 2277731) B2277731
theorem B4049299 : Blo 1895435 4049299 := bstep (se 1 (by rfl) ⟨3036974, by rfl⟩ : syracuseStep 4049299 = 6073949) B6073949
theorem B5399065 : Blo 1895435 5399065 := bstep (se 2 (by rfl) ⟨2024649, by rfl⟩ : syracuseStep 5399065 = 4049299) B4049299
theorem B7198753 : Blo 1895435 7198753 := bstep (se 2 (by rfl) ⟨2699532, by rfl⟩ : syracuseStep 7198753 = 5399065) B5399065
theorem B9598337 : Blo 1895435 9598337 := bstep (se 2 (by rfl) ⟨3599376, by rfl⟩ : syracuseStep 9598337 = 7198753) B7198753
theorem B6398891 : Blo 1895435 6398891 := bstep (se 1 (by rfl) ⟨4799168, by rfl⟩ : syracuseStep 6398891 = 9598337) B9598337
theorem B4265927 : Blo 1895435 4265927 := bstep (se 1 (by rfl) ⟨3199445, by rfl⟩ : syracuseStep 4265927 = 6398891) B6398891
theorem B2843951 : Blo 1895435 2843951 := bstep (se 1 (by rfl) ⟨2132963, by rfl⟩ : syracuseStep 2843951 = 4265927) B4265927
theorem B1895967 : Blo 1895435 1895967 := bstep (se 1 (by rfl) ⟨1421975, by rfl⟩ : syracuseStep 1895967 = 2843951) B2843951
theorem B2843957 : Blo 1895435 2843957 := bbase (se 5 (by rfl) ⟨133310, by rfl⟩ : syracuseStep 2843957 = 266621) (by norm_num)
theorem B1895971 : Blo 1895435 1895971 := bstep (se 1 (by rfl) ⟨1421978, by rfl⟩ : syracuseStep 1895971 = 2843957) B2843957
theorem B4799189 : Blo 1895435 4799189 := bbase (se 7 (by rfl) ⟨56240, by rfl⟩ : syracuseStep 4799189 = 112481) (by norm_num)
theorem B3199459 : Blo 1895435 3199459 := bstep (se 1 (by rfl) ⟨2399594, by rfl⟩ : syracuseStep 3199459 = 4799189) B4799189
theorem B4265945 : Blo 1895435 4265945 := bstep (se 2 (by rfl) ⟨1599729, by rfl⟩ : syracuseStep 4265945 = 3199459) B3199459
theorem B2843963 : Blo 1895435 2843963 := bstep (se 1 (by rfl) ⟨2132972, by rfl⟩ : syracuseStep 2843963 = 4265945) B4265945
theorem B1895975 : Blo 1895435 1895975 := bstep (se 1 (by rfl) ⟨1421981, by rfl⟩ : syracuseStep 1895975 = 2843963) B2843963
theorem B2132977 : Blo 1895435 2132977 := bbase (se 2 (by rfl) ⟨799866, by rfl⟩ : syracuseStep 2132977 = 1599733) (by norm_num)
theorem B2843969 : Blo 1895435 2843969 := bstep (se 2 (by rfl) ⟨1066488, by rfl⟩ : syracuseStep 2843969 = 2132977) B2132977
theorem B1895979 : Blo 1895435 1895979 := bstep (se 1 (by rfl) ⟨1421984, by rfl⟩ : syracuseStep 1895979 = 2843969) B2843969
theorem B10249877 : Blo 1895435 10249877 := bbase (se 6 (by rfl) ⟨240231, by rfl⟩ : syracuseStep 10249877 = 480463) (by norm_num)
theorem B6833251 : Blo 1895435 6833251 := bstep (se 1 (by rfl) ⟨5124938, by rfl⟩ : syracuseStep 6833251 = 10249877) B10249877
theorem B9111001 : Blo 1895435 9111001 := bstep (se 2 (by rfl) ⟨3416625, by rfl⟩ : syracuseStep 9111001 = 6833251) B6833251
theorem B12148001 : Blo 1895435 12148001 := bstep (se 2 (by rfl) ⟨4555500, by rfl⟩ : syracuseStep 12148001 = 9111001) B9111001
theorem B8098667 : Blo 1895435 8098667 := bstep (se 1 (by rfl) ⟨6074000, by rfl⟩ : syracuseStep 8098667 = 12148001) B12148001
theorem B5399111 : Blo 1895435 5399111 := bstep (se 1 (by rfl) ⟨4049333, by rfl⟩ : syracuseStep 5399111 = 8098667) B8098667
theorem B3599407 : Blo 1895435 3599407 := bstep (se 1 (by rfl) ⟨2699555, by rfl⟩ : syracuseStep 3599407 = 5399111) B5399111
theorem B4799209 : Blo 1895435 4799209 := bstep (se 2 (by rfl) ⟨1799703, by rfl⟩ : syracuseStep 4799209 = 3599407) B3599407
theorem B6398945 : Blo 1895435 6398945 := bstep (se 2 (by rfl) ⟨2399604, by rfl⟩ : syracuseStep 6398945 = 4799209) B4799209
theorem B4265963 : Blo 1895435 4265963 := bstep (se 1 (by rfl) ⟨3199472, by rfl⟩ : syracuseStep 4265963 = 6398945) B6398945
theorem B2843975 : Blo 1895435 2843975 := bstep (se 1 (by rfl) ⟨2132981, by rfl⟩ : syracuseStep 2843975 = 4265963) B4265963
theorem B1895983 : Blo 1895435 1895983 := bstep (se 1 (by rfl) ⟨1421987, by rfl⟩ : syracuseStep 1895983 = 2843975) B2843975
theorem B2843981 : Blo 1895435 2843981 := bbase (se 3 (by rfl) ⟨533246, by rfl⟩ : syracuseStep 2843981 = 1066493) (by norm_num)
theorem B1895987 : Blo 1895435 1895987 := bstep (se 1 (by rfl) ⟨1421990, by rfl⟩ : syracuseStep 1895987 = 2843981) B2843981
theorem B4265981 : Blo 1895435 4265981 := bbase (se 3 (by rfl) ⟨799871, by rfl⟩ : syracuseStep 4265981 = 1599743) (by norm_num)
theorem B2843987 : Blo 1895435 2843987 := bstep (se 1 (by rfl) ⟨2132990, by rfl⟩ : syracuseStep 2843987 = 4265981) B4265981
theorem B1895991 : Blo 1895435 1895991 := bstep (se 1 (by rfl) ⟨1421993, by rfl⟩ : syracuseStep 1895991 = 2843987) B2843987
theorem B3199493 : Blo 1895435 3199493 := bbase (se 4 (by rfl) ⟨299952, by rfl⟩ : syracuseStep 3199493 = 599905) (by norm_num)
theorem B2132995 : Blo 1895435 2132995 := bstep (se 1 (by rfl) ⟨1599746, by rfl⟩ : syracuseStep 2132995 = 3199493) B3199493
theorem B2843993 : Blo 1895435 2843993 := bstep (se 2 (by rfl) ⟨1066497, by rfl⟩ : syracuseStep 2843993 = 2132995) B2132995
theorem B1895995 : Blo 1895435 1895995 := bstep (se 1 (by rfl) ⟨1421996, by rfl⟩ : syracuseStep 1895995 = 2843993) B2843993
theorem B14397749 : Blo 1895435 14397749 := bbase (se 5 (by rfl) ⟨674894, by rfl⟩ : syracuseStep 14397749 = 1349789) (by norm_num)
theorem B9598499 : Blo 1895435 9598499 := bstep (se 1 (by rfl) ⟨7198874, by rfl⟩ : syracuseStep 9598499 = 14397749) B14397749
theorem B6398999 : Blo 1895435 6398999 := bstep (se 1 (by rfl) ⟨4799249, by rfl⟩ : syracuseStep 6398999 = 9598499) B9598499
theorem B4265999 : Blo 1895435 4265999 := bstep (se 1 (by rfl) ⟨3199499, by rfl⟩ : syracuseStep 4265999 = 6398999) B6398999
theorem B2843999 : Blo 1895435 2843999 := bstep (se 1 (by rfl) ⟨2132999, by rfl⟩ : syracuseStep 2843999 = 4265999) B4265999
theorem B1895999 : Blo 1895435 1895999 := bstep (se 1 (by rfl) ⟨1421999, by rfl⟩ : syracuseStep 1895999 = 2843999) B2843999
theorem B2844005 : Blo 1895435 2844005 := bbase (se 4 (by rfl) ⟨266625, by rfl⟩ : syracuseStep 2844005 = 533251) (by norm_num)
theorem B1896003 : Blo 1895435 1896003 := bstep (se 1 (by rfl) ⟨1422002, by rfl⟩ : syracuseStep 1896003 = 2844005) B2844005
theorem B3599453 : Blo 1895435 3599453 := bbase (se 3 (by rfl) ⟨674897, by rfl⟩ : syracuseStep 3599453 = 1349795) (by norm_num)
theorem B2399635 : Blo 1895435 2399635 := bstep (se 1 (by rfl) ⟨1799726, by rfl⟩ : syracuseStep 2399635 = 3599453) B3599453
theorem B3199513 : Blo 1895435 3199513 := bstep (se 2 (by rfl) ⟨1199817, by rfl⟩ : syracuseStep 3199513 = 2399635) B2399635
theorem B4266017 : Blo 1895435 4266017 := bstep (se 2 (by rfl) ⟨1599756, by rfl⟩ : syracuseStep 4266017 = 3199513) B3199513
theorem B2844011 : Blo 1895435 2844011 := bstep (se 1 (by rfl) ⟨2133008, by rfl⟩ : syracuseStep 2844011 = 4266017) B4266017
theorem B1896007 : Blo 1895435 1896007 := bstep (se 1 (by rfl) ⟨1422005, by rfl⟩ : syracuseStep 1896007 = 2844011) B2844011
theorem B2133013 : Blo 1895435 2133013 := bbase (se 6 (by rfl) ⟨49992, by rfl⟩ : syracuseStep 2133013 = 99985) (by norm_num)
theorem B2844017 : Blo 1895435 2844017 := bstep (se 2 (by rfl) ⟨1066506, by rfl⟩ : syracuseStep 2844017 = 2133013) B2133013
theorem B1896011 : Blo 1895435 1896011 := bstep (se 1 (by rfl) ⟨1422008, by rfl⟩ : syracuseStep 1896011 = 2844017) B2844017
theorem B2399645 : Blo 1895435 2399645 := bbase (se 3 (by rfl) ⟨449933, by rfl⟩ : syracuseStep 2399645 = 899867) (by norm_num)
theorem B6399053 : Blo 1895435 6399053 := bstep (se 3 (by rfl) ⟨1199822, by rfl⟩ : syracuseStep 6399053 = 2399645) B2399645
theorem B4266035 : Blo 1895435 4266035 := bstep (se 1 (by rfl) ⟨3199526, by rfl⟩ : syracuseStep 4266035 = 6399053) B6399053
theorem B2844023 : Blo 1895435 2844023 := bstep (se 1 (by rfl) ⟨2133017, by rfl⟩ : syracuseStep 2844023 = 4266035) B4266035
theorem B1896015 : Blo 1895435 1896015 := bstep (se 1 (by rfl) ⟨1422011, by rfl⟩ : syracuseStep 1896015 = 2844023) B2844023
theorem B2844029 : Blo 1895435 2844029 := bbase (se 3 (by rfl) ⟨533255, by rfl⟩ : syracuseStep 2844029 = 1066511) (by norm_num)
theorem B1896019 : Blo 1895435 1896019 := bstep (se 1 (by rfl) ⟨1422014, by rfl⟩ : syracuseStep 1896019 = 2844029) B2844029
theorem B4266053 : Blo 1895435 4266053 := bbase (se 4 (by rfl) ⟨399942, by rfl⟩ : syracuseStep 4266053 = 799885) (by norm_num)
theorem B2844035 : Blo 1895435 2844035 := bstep (se 1 (by rfl) ⟨2133026, by rfl⟩ : syracuseStep 2844035 = 4266053) B4266053
theorem B1896023 : Blo 1895435 1896023 := bstep (se 1 (by rfl) ⟨1422017, by rfl⟩ : syracuseStep 1896023 = 2844035) B2844035
theorem B5399237 : Blo 1895435 5399237 := bbase (se 4 (by rfl) ⟨506178, by rfl⟩ : syracuseStep 5399237 = 1012357) (by norm_num)
theorem B3599491 : Blo 1895435 3599491 := bstep (se 1 (by rfl) ⟨2699618, by rfl⟩ : syracuseStep 3599491 = 5399237) B5399237
theorem B4799321 : Blo 1895435 4799321 := bstep (se 2 (by rfl) ⟨1799745, by rfl⟩ : syracuseStep 4799321 = 3599491) B3599491
theorem B3199547 : Blo 1895435 3199547 := bstep (se 1 (by rfl) ⟨2399660, by rfl⟩ : syracuseStep 3199547 = 4799321) B4799321
theorem B2133031 : Blo 1895435 2133031 := bstep (se 1 (by rfl) ⟨1599773, by rfl⟩ : syracuseStep 2133031 = 3199547) B3199547
theorem B2844041 : Blo 1895435 2844041 := bstep (se 2 (by rfl) ⟨1066515, by rfl⟩ : syracuseStep 2844041 = 2133031) B2133031
theorem B1896027 : Blo 1895435 1896027 := bstep (se 1 (by rfl) ⟨1422020, by rfl⟩ : syracuseStep 1896027 = 2844041) B2844041
theorem B9598661 : Blo 1895435 9598661 := bbase (se 4 (by rfl) ⟨899874, by rfl⟩ : syracuseStep 9598661 = 1799749) (by norm_num)
theorem B6399107 : Blo 1895435 6399107 := bstep (se 1 (by rfl) ⟨4799330, by rfl⟩ : syracuseStep 6399107 = 9598661) B9598661
theorem B4266071 : Blo 1895435 4266071 := bstep (se 1 (by rfl) ⟨3199553, by rfl⟩ : syracuseStep 4266071 = 6399107) B6399107
theorem B2844047 : Blo 1895435 2844047 := bstep (se 1 (by rfl) ⟨2133035, by rfl⟩ : syracuseStep 2844047 = 4266071) B4266071
theorem B1896031 : Blo 1895435 1896031 := bstep (se 1 (by rfl) ⟨1422023, by rfl⟩ : syracuseStep 1896031 = 2844047) B2844047
theorem B2844053 : Blo 1895435 2844053 := bbase (se 6 (by rfl) ⟨66657, by rfl⟩ : syracuseStep 2844053 = 133315) (by norm_num)
theorem B1896035 : Blo 1895435 1896035 := bstep (se 1 (by rfl) ⟨1422026, by rfl⟩ : syracuseStep 1896035 = 2844053) B2844053
theorem B4049453 : Blo 1895435 4049453 := bbase (se 3 (by rfl) ⟨759272, by rfl⟩ : syracuseStep 4049453 = 1518545) (by norm_num)
theorem B10798541 : Blo 1895435 10798541 := bstep (se 3 (by rfl) ⟨2024726, by rfl⟩ : syracuseStep 10798541 = 4049453) B4049453
theorem B7199027 : Blo 1895435 7199027 := bstep (se 1 (by rfl) ⟨5399270, by rfl⟩ : syracuseStep 7199027 = 10798541) B10798541
theorem B4799351 : Blo 1895435 4799351 := bstep (se 1 (by rfl) ⟨3599513, by rfl⟩ : syracuseStep 4799351 = 7199027) B7199027
theorem B3199567 : Blo 1895435 3199567 := bstep (se 1 (by rfl) ⟨2399675, by rfl⟩ : syracuseStep 3199567 = 4799351) B4799351
theorem B4266089 : Blo 1895435 4266089 := bstep (se 2 (by rfl) ⟨1599783, by rfl⟩ : syracuseStep 4266089 = 3199567) B3199567
theorem B2844059 : Blo 1895435 2844059 := bstep (se 1 (by rfl) ⟨2133044, by rfl⟩ : syracuseStep 2844059 = 4266089) B4266089
theorem B1896039 : Blo 1895435 1896039 := bstep (se 1 (by rfl) ⟨1422029, by rfl⟩ : syracuseStep 1896039 = 2844059) B2844059
theorem B2133049 : Blo 1895435 2133049 := bbase (se 2 (by rfl) ⟨799893, by rfl⟩ : syracuseStep 2133049 = 1599787) (by norm_num)
theorem B2844065 : Blo 1895435 2844065 := bstep (se 2 (by rfl) ⟨1066524, by rfl⟩ : syracuseStep 2844065 = 2133049) B2133049
theorem B1896043 : Blo 1895435 1896043 := bstep (se 1 (by rfl) ⟨1422032, by rfl⟩ : syracuseStep 1896043 = 2844065) B2844065
theorem B7687669 : Blo 1895435 7687669 := bbase (se 5 (by rfl) ⟨360359, by rfl⟩ : syracuseStep 7687669 = 720719) (by norm_num)
theorem B10250225 : Blo 1895435 10250225 := bstep (se 2 (by rfl) ⟨3843834, by rfl⟩ : syracuseStep 10250225 = 7687669) B7687669
theorem B6833483 : Blo 1895435 6833483 := bstep (se 1 (by rfl) ⟨5125112, by rfl⟩ : syracuseStep 6833483 = 10250225) B10250225
theorem B4555655 : Blo 1895435 4555655 := bstep (se 1 (by rfl) ⟨3416741, by rfl⟩ : syracuseStep 4555655 = 6833483) B6833483
theorem B3037103 : Blo 1895435 3037103 := bstep (se 1 (by rfl) ⟨2277827, by rfl⟩ : syracuseStep 3037103 = 4555655) B4555655
theorem B2024735 : Blo 1895435 2024735 := bstep (se 1 (by rfl) ⟨1518551, by rfl⟩ : syracuseStep 2024735 = 3037103) B3037103
theorem B5399293 : Blo 1895435 5399293 := bstep (se 3 (by rfl) ⟨1012367, by rfl⟩ : syracuseStep 5399293 = 2024735) B2024735
theorem B7199057 : Blo 1895435 7199057 := bstep (se 2 (by rfl) ⟨2699646, by rfl⟩ : syracuseStep 7199057 = 5399293) B5399293
theorem B4799371 : Blo 1895435 4799371 := bstep (se 1 (by rfl) ⟨3599528, by rfl⟩ : syracuseStep 4799371 = 7199057) B7199057
theorem B6399161 : Blo 1895435 6399161 := bstep (se 2 (by rfl) ⟨2399685, by rfl⟩ : syracuseStep 6399161 = 4799371) B4799371
theorem B4266107 : Blo 1895435 4266107 := bstep (se 1 (by rfl) ⟨3199580, by rfl⟩ : syracuseStep 4266107 = 6399161) B6399161
theorem B2844071 : Blo 1895435 2844071 := bstep (se 1 (by rfl) ⟨2133053, by rfl⟩ : syracuseStep 2844071 = 4266107) B4266107
theorem B1896047 : Blo 1895435 1896047 := bstep (se 1 (by rfl) ⟨1422035, by rfl⟩ : syracuseStep 1896047 = 2844071) B2844071
theorem B2844077 : Blo 1895435 2844077 := bbase (se 3 (by rfl) ⟨533264, by rfl⟩ : syracuseStep 2844077 = 1066529) (by norm_num)
theorem B1896051 : Blo 1895435 1896051 := bstep (se 1 (by rfl) ⟨1422038, by rfl⟩ : syracuseStep 1896051 = 2844077) B2844077
theorem B4266125 : Blo 1895435 4266125 := bbase (se 3 (by rfl) ⟨799898, by rfl⟩ : syracuseStep 4266125 = 1599797) (by norm_num)
theorem B2844083 : Blo 1895435 2844083 := bstep (se 1 (by rfl) ⟨2133062, by rfl⟩ : syracuseStep 2844083 = 4266125) B4266125
theorem B1896055 : Blo 1895435 1896055 := bstep (se 1 (by rfl) ⟨1422041, by rfl⟩ : syracuseStep 1896055 = 2844083) B2844083
theorem B2399701 : Blo 1895435 2399701 := bbase (se 7 (by rfl) ⟨28121, by rfl⟩ : syracuseStep 2399701 = 56243) (by norm_num)
theorem B3199601 : Blo 1895435 3199601 := bstep (se 2 (by rfl) ⟨1199850, by rfl⟩ : syracuseStep 3199601 = 2399701) B2399701
theorem B2133067 : Blo 1895435 2133067 := bstep (se 1 (by rfl) ⟨1599800, by rfl⟩ : syracuseStep 2133067 = 3199601) B3199601
theorem B2844089 : Blo 1895435 2844089 := bstep (se 2 (by rfl) ⟨1066533, by rfl⟩ : syracuseStep 2844089 = 2133067) B2133067
theorem B1896059 : Blo 1895435 1896059 := bstep (se 1 (by rfl) ⟨1422044, by rfl⟩ : syracuseStep 1896059 = 2844089) B2844089
theorem B12973045 : Blo 1895435 12973045 := bbase (se 5 (by rfl) ⟨608111, by rfl⟩ : syracuseStep 12973045 = 1216223) (by norm_num)
theorem B17297393 : Blo 1895435 17297393 := bstep (se 2 (by rfl) ⟨6486522, by rfl⟩ : syracuseStep 17297393 = 12973045) B12973045
theorem B184505525 : Blo 1895435 184505525 := bstep (se 5 (by rfl) ⟨8648696, by rfl⟩ : syracuseStep 184505525 = 17297393) B17297393
theorem B123003683 : Blo 1895435 123003683 := bstep (se 1 (by rfl) ⟨92252762, by rfl⟩ : syracuseStep 123003683 = 184505525) B184505525
theorem B82002455 : Blo 1895435 82002455 := bstep (se 1 (by rfl) ⟨61501841, by rfl⟩ : syracuseStep 82002455 = 123003683) B123003683
theorem B54668303 : Blo 1895435 54668303 := bstep (se 1 (by rfl) ⟨41001227, by rfl⟩ : syracuseStep 54668303 = 82002455) B82002455
theorem B36445535 : Blo 1895435 36445535 := bstep (se 1 (by rfl) ⟨27334151, by rfl⟩ : syracuseStep 36445535 = 54668303) B54668303
theorem B24297023 : Blo 1895435 24297023 := bstep (se 1 (by rfl) ⟨18222767, by rfl⟩ : syracuseStep 24297023 = 36445535) B36445535
theorem B16198015 : Blo 1895435 16198015 := bstep (se 1 (by rfl) ⟨12148511, by rfl⟩ : syracuseStep 16198015 = 24297023) B24297023
theorem B21597353 : Blo 1895435 21597353 := bstep (se 2 (by rfl) ⟨8099007, by rfl⟩ : syracuseStep 21597353 = 16198015) B16198015
theorem B14398235 : Blo 1895435 14398235 := bstep (se 1 (by rfl) ⟨10798676, by rfl⟩ : syracuseStep 14398235 = 21597353) B21597353
theorem B9598823 : Blo 1895435 9598823 := bstep (se 1 (by rfl) ⟨7199117, by rfl⟩ : syracuseStep 9598823 = 14398235) B14398235
theorem B6399215 : Blo 1895435 6399215 := bstep (se 1 (by rfl) ⟨4799411, by rfl⟩ : syracuseStep 6399215 = 9598823) B9598823
theorem B4266143 : Blo 1895435 4266143 := bstep (se 1 (by rfl) ⟨3199607, by rfl⟩ : syracuseStep 4266143 = 6399215) B6399215
theorem B2844095 : Blo 1895435 2844095 := bstep (se 1 (by rfl) ⟨2133071, by rfl⟩ : syracuseStep 2844095 = 4266143) B4266143
theorem B1896063 : Blo 1895435 1896063 := bstep (se 1 (by rfl) ⟨1422047, by rfl⟩ : syracuseStep 1896063 = 2844095) B2844095
theorem B2844101 : Blo 1895435 2844101 := bbase (se 4 (by rfl) ⟨266634, by rfl⟩ : syracuseStep 2844101 = 533269) (by norm_num)
theorem B1896067 : Blo 1895435 1896067 := bstep (se 1 (by rfl) ⟨1422050, by rfl⟩ : syracuseStep 1896067 = 2844101) B2844101
theorem B3199621 : Blo 1895435 3199621 := bbase (se 4 (by rfl) ⟨299964, by rfl⟩ : syracuseStep 3199621 = 599929) (by norm_num)
theorem B4266161 : Blo 1895435 4266161 := bstep (se 2 (by rfl) ⟨1599810, by rfl⟩ : syracuseStep 4266161 = 3199621) B3199621
theorem B2844107 : Blo 1895435 2844107 := bstep (se 1 (by rfl) ⟨2133080, by rfl⟩ : syracuseStep 2844107 = 4266161) B4266161
theorem B1896071 : Blo 1895435 1896071 := bstep (se 1 (by rfl) ⟨1422053, by rfl⟩ : syracuseStep 1896071 = 2844107) B2844107
theorem B2133085 : Blo 1895435 2133085 := bbase (se 3 (by rfl) ⟨399953, by rfl⟩ : syracuseStep 2133085 = 799907) (by norm_num)
theorem B2844113 : Blo 1895435 2844113 := bstep (se 2 (by rfl) ⟨1066542, by rfl⟩ : syracuseStep 2844113 = 2133085) B2133085
theorem B1896075 : Blo 1895435 1896075 := bstep (se 1 (by rfl) ⟨1422056, by rfl⟩ : syracuseStep 1896075 = 2844113) B2844113
theorem B6399269 : Blo 1895435 6399269 := bbase (se 4 (by rfl) ⟨599931, by rfl⟩ : syracuseStep 6399269 = 1199863) (by norm_num)
theorem B4266179 : Blo 1895435 4266179 := bstep (se 1 (by rfl) ⟨3199634, by rfl⟩ : syracuseStep 4266179 = 6399269) B6399269
theorem B2844119 : Blo 1895435 2844119 := bstep (se 1 (by rfl) ⟨2133089, by rfl⟩ : syracuseStep 2844119 = 4266179) B4266179
theorem B1896079 : Blo 1895435 1896079 := bstep (se 1 (by rfl) ⟨1422059, by rfl⟩ : syracuseStep 1896079 = 2844119) B2844119
theorem B2844125 : Blo 1895435 2844125 := bbase (se 3 (by rfl) ⟨533273, by rfl⟩ : syracuseStep 2844125 = 1066547) (by norm_num)
theorem B1896083 : Blo 1895435 1896083 := bstep (se 1 (by rfl) ⟨1422062, by rfl⟩ : syracuseStep 1896083 = 2844125) B2844125
theorem B4266197 : Blo 1895435 4266197 := bbase (se 7 (by rfl) ⟨49994, by rfl⟩ : syracuseStep 4266197 = 99989) (by norm_num)
theorem B2844131 : Blo 1895435 2844131 := bstep (se 1 (by rfl) ⟨2133098, by rfl⟩ : syracuseStep 2844131 = 4266197) B4266197
theorem B1896087 : Blo 1895435 1896087 := bstep (se 1 (by rfl) ⟨1422065, by rfl⟩ : syracuseStep 1896087 = 2844131) B2844131
theorem B4160821 : Blo 1895435 4160821 := bbase (se 5 (by rfl) ⟨195038, by rfl⟩ : syracuseStep 4160821 = 390077) (by norm_num)
theorem B5547761 : Blo 1895435 5547761 := bstep (se 2 (by rfl) ⟨2080410, by rfl⟩ : syracuseStep 5547761 = 4160821) B4160821
theorem B3698507 : Blo 1895435 3698507 := bstep (se 1 (by rfl) ⟨2773880, by rfl⟩ : syracuseStep 3698507 = 5547761) B5547761
theorem B2465671 : Blo 1895435 2465671 := bstep (se 1 (by rfl) ⟨1849253, by rfl⟩ : syracuseStep 2465671 = 3698507) B3698507
theorem B3287561 : Blo 1895435 3287561 := bstep (se 2 (by rfl) ⟨1232835, by rfl⟩ : syracuseStep 3287561 = 2465671) B2465671
theorem B8766829 : Blo 1895435 8766829 := bstep (se 3 (by rfl) ⟨1643780, by rfl⟩ : syracuseStep 8766829 = 3287561) B3287561
theorem B11689105 : Blo 1895435 11689105 := bstep (se 2 (by rfl) ⟨4383414, by rfl⟩ : syracuseStep 11689105 = 8766829) B8766829
theorem B15585473 : Blo 1895435 15585473 := bstep (se 2 (by rfl) ⟨5844552, by rfl⟩ : syracuseStep 15585473 = 11689105) B11689105
theorem B41561261 : Blo 1895435 41561261 := bstep (se 3 (by rfl) ⟨7792736, by rfl⟩ : syracuseStep 41561261 = 15585473) B15585473
theorem B27707507 : Blo 1895435 27707507 := bstep (se 1 (by rfl) ⟨20780630, by rfl⟩ : syracuseStep 27707507 = 41561261) B41561261
theorem B18471671 : Blo 1895435 18471671 := bstep (se 1 (by rfl) ⟨13853753, by rfl⟩ : syracuseStep 18471671 = 27707507) B27707507
theorem B12314447 : Blo 1895435 12314447 := bstep (se 1 (by rfl) ⟨9235835, by rfl⟩ : syracuseStep 12314447 = 18471671) B18471671
theorem B8209631 : Blo 1895435 8209631 := bstep (se 1 (by rfl) ⟨6157223, by rfl⟩ : syracuseStep 8209631 = 12314447) B12314447
theorem B21892349 : Blo 1895435 21892349 := bstep (se 3 (by rfl) ⟨4104815, by rfl⟩ : syracuseStep 21892349 = 8209631) B8209631
theorem B14594899 : Blo 1895435 14594899 := bstep (se 1 (by rfl) ⟨10946174, by rfl⟩ : syracuseStep 14594899 = 21892349) B21892349
theorem B19459865 : Blo 1895435 19459865 := bstep (se 2 (by rfl) ⟨7297449, by rfl⟩ : syracuseStep 19459865 = 14594899) B14594899
theorem B12973243 : Blo 1895435 12973243 := bstep (se 1 (by rfl) ⟨9729932, by rfl⟩ : syracuseStep 12973243 = 19459865) B19459865
theorem B17297657 : Blo 1895435 17297657 := bstep (se 2 (by rfl) ⟨6486621, by rfl⟩ : syracuseStep 17297657 = 12973243) B12973243
theorem B11531771 : Blo 1895435 11531771 := bstep (se 1 (by rfl) ⟨8648828, by rfl⟩ : syracuseStep 11531771 = 17297657) B17297657
theorem B7687847 : Blo 1895435 7687847 := bstep (se 1 (by rfl) ⟨5765885, by rfl⟩ : syracuseStep 7687847 = 11531771) B11531771
theorem B5125231 : Blo 1895435 5125231 := bstep (se 1 (by rfl) ⟨3843923, by rfl⟩ : syracuseStep 5125231 = 7687847) B7687847
theorem B6833641 : Blo 1895435 6833641 := bstep (se 2 (by rfl) ⟨2562615, by rfl⟩ : syracuseStep 6833641 = 5125231) B5125231
theorem B9111521 : Blo 1895435 9111521 := bstep (se 2 (by rfl) ⟨3416820, by rfl⟩ : syracuseStep 9111521 = 6833641) B6833641
theorem B6074347 : Blo 1895435 6074347 := bstep (se 1 (by rfl) ⟨4555760, by rfl⟩ : syracuseStep 6074347 = 9111521) B9111521
theorem B8099129 : Blo 1895435 8099129 := bstep (se 2 (by rfl) ⟨3037173, by rfl⟩ : syracuseStep 8099129 = 6074347) B6074347
theorem B5399419 : Blo 1895435 5399419 := bstep (se 1 (by rfl) ⟨4049564, by rfl⟩ : syracuseStep 5399419 = 8099129) B8099129
theorem B7199225 : Blo 1895435 7199225 := bstep (se 2 (by rfl) ⟨2699709, by rfl⟩ : syracuseStep 7199225 = 5399419) B5399419
theorem B4799483 : Blo 1895435 4799483 := bstep (se 1 (by rfl) ⟨3599612, by rfl⟩ : syracuseStep 4799483 = 7199225) B7199225
theorem B3199655 : Blo 1895435 3199655 := bstep (se 1 (by rfl) ⟨2399741, by rfl⟩ : syracuseStep 3199655 = 4799483) B4799483
theorem B2133103 : Blo 1895435 2133103 := bstep (se 1 (by rfl) ⟨1599827, by rfl⟩ : syracuseStep 2133103 = 3199655) B3199655
theorem B2844137 : Blo 1895435 2844137 := bstep (se 2 (by rfl) ⟨1066551, by rfl⟩ : syracuseStep 2844137 = 2133103) B2133103
theorem B1896091 : Blo 1895435 1896091 := bstep (se 1 (by rfl) ⟨1422068, by rfl⟩ : syracuseStep 1896091 = 2844137) B2844137
theorem B6157237 : Blo 1895435 6157237 := bbase (se 5 (by rfl) ⟨288620, by rfl⟩ : syracuseStep 6157237 = 577241) (by norm_num)
theorem B8209649 : Blo 1895435 8209649 := bstep (se 2 (by rfl) ⟨3078618, by rfl⟩ : syracuseStep 8209649 = 6157237) B6157237
theorem B5473099 : Blo 1895435 5473099 := bstep (se 1 (by rfl) ⟨4104824, by rfl⟩ : syracuseStep 5473099 = 8209649) B8209649
theorem B7297465 : Blo 1895435 7297465 := bstep (se 2 (by rfl) ⟨2736549, by rfl⟩ : syracuseStep 7297465 = 5473099) B5473099
theorem B9729953 : Blo 1895435 9729953 := bstep (se 2 (by rfl) ⟨3648732, by rfl⟩ : syracuseStep 9729953 = 7297465) B7297465
theorem B6486635 : Blo 1895435 6486635 := bstep (se 1 (by rfl) ⟨4864976, by rfl⟩ : syracuseStep 6486635 = 9729953) B9729953
theorem B4324423 : Blo 1895435 4324423 := bstep (se 1 (by rfl) ⟨3243317, by rfl⟩ : syracuseStep 4324423 = 6486635) B6486635
theorem B5765897 : Blo 1895435 5765897 := bstep (se 2 (by rfl) ⟨2162211, by rfl⟩ : syracuseStep 5765897 = 4324423) B4324423
theorem B3843931 : Blo 1895435 3843931 := bstep (se 1 (by rfl) ⟨2882948, by rfl⟩ : syracuseStep 3843931 = 5765897) B5765897
theorem B5125241 : Blo 1895435 5125241 := bstep (se 2 (by rfl) ⟨1921965, by rfl⟩ : syracuseStep 5125241 = 3843931) B3843931
theorem B3416827 : Blo 1895435 3416827 := bstep (se 1 (by rfl) ⟨2562620, by rfl⟩ : syracuseStep 3416827 = 5125241) B5125241
theorem B4555769 : Blo 1895435 4555769 := bstep (se 2 (by rfl) ⟨1708413, by rfl⟩ : syracuseStep 4555769 = 3416827) B3416827
theorem B12148717 : Blo 1895435 12148717 := bstep (se 3 (by rfl) ⟨2277884, by rfl⟩ : syracuseStep 12148717 = 4555769) B4555769
theorem B16198289 : Blo 1895435 16198289 := bstep (se 2 (by rfl) ⟨6074358, by rfl⟩ : syracuseStep 16198289 = 12148717) B12148717
theorem B10798859 : Blo 1895435 10798859 := bstep (se 1 (by rfl) ⟨8099144, by rfl⟩ : syracuseStep 10798859 = 16198289) B16198289
theorem B7199239 : Blo 1895435 7199239 := bstep (se 1 (by rfl) ⟨5399429, by rfl⟩ : syracuseStep 7199239 = 10798859) B10798859
theorem B9598985 : Blo 1895435 9598985 := bstep (se 2 (by rfl) ⟨3599619, by rfl⟩ : syracuseStep 9598985 = 7199239) B7199239
theorem B6399323 : Blo 1895435 6399323 := bstep (se 1 (by rfl) ⟨4799492, by rfl⟩ : syracuseStep 6399323 = 9598985) B9598985
theorem B4266215 : Blo 1895435 4266215 := bstep (se 1 (by rfl) ⟨3199661, by rfl⟩ : syracuseStep 4266215 = 6399323) B6399323
theorem B2844143 : Blo 1895435 2844143 := bstep (se 1 (by rfl) ⟨2133107, by rfl⟩ : syracuseStep 2844143 = 4266215) B4266215
theorem B1896095 : Blo 1895435 1896095 := bstep (se 1 (by rfl) ⟨1422071, by rfl⟩ : syracuseStep 1896095 = 2844143) B2844143
theorem B2844149 : Blo 1895435 2844149 := bbase (se 5 (by rfl) ⟨133319, by rfl⟩ : syracuseStep 2844149 = 266639) (by norm_num)
theorem B1896099 : Blo 1895435 1896099 := bstep (se 1 (by rfl) ⟨1422074, by rfl⟩ : syracuseStep 1896099 = 2844149) B2844149
theorem B3843949 : Blo 1895435 3843949 := bbase (se 3 (by rfl) ⟨720740, by rfl⟩ : syracuseStep 3843949 = 1441481) (by norm_num)
theorem B5125265 : Blo 1895435 5125265 := bstep (se 2 (by rfl) ⟨1921974, by rfl⟩ : syracuseStep 5125265 = 3843949) B3843949
theorem B3416843 : Blo 1895435 3416843 := bstep (se 1 (by rfl) ⟨2562632, by rfl⟩ : syracuseStep 3416843 = 5125265) B5125265
theorem B2277895 : Blo 1895435 2277895 := bstep (se 1 (by rfl) ⟨1708421, by rfl⟩ : syracuseStep 2277895 = 3416843) B3416843
theorem B3037193 : Blo 1895435 3037193 := bstep (se 2 (by rfl) ⟨1138947, by rfl⟩ : syracuseStep 3037193 = 2277895) B2277895
theorem B2024795 : Blo 1895435 2024795 := bstep (se 1 (by rfl) ⟨1518596, by rfl⟩ : syracuseStep 2024795 = 3037193) B3037193
theorem B5399453 : Blo 1895435 5399453 := bstep (se 3 (by rfl) ⟨1012397, by rfl⟩ : syracuseStep 5399453 = 2024795) B2024795
theorem B3599635 : Blo 1895435 3599635 := bstep (se 1 (by rfl) ⟨2699726, by rfl⟩ : syracuseStep 3599635 = 5399453) B5399453
theorem B4799513 : Blo 1895435 4799513 := bstep (se 2 (by rfl) ⟨1799817, by rfl⟩ : syracuseStep 4799513 = 3599635) B3599635
theorem B3199675 : Blo 1895435 3199675 := bstep (se 1 (by rfl) ⟨2399756, by rfl⟩ : syracuseStep 3199675 = 4799513) B4799513
theorem B4266233 : Blo 1895435 4266233 := bstep (se 2 (by rfl) ⟨1599837, by rfl⟩ : syracuseStep 4266233 = 3199675) B3199675
theorem B2844155 : Blo 1895435 2844155 := bstep (se 1 (by rfl) ⟨2133116, by rfl⟩ : syracuseStep 2844155 = 4266233) B4266233
theorem B1896103 : Blo 1895435 1896103 := bstep (se 1 (by rfl) ⟨1422077, by rfl⟩ : syracuseStep 1896103 = 2844155) B2844155
theorem B2133121 : Blo 1895435 2133121 := bbase (se 2 (by rfl) ⟨799920, by rfl⟩ : syracuseStep 2133121 = 1599841) (by norm_num)
theorem B2844161 : Blo 1895435 2844161 := bstep (se 2 (by rfl) ⟨1066560, by rfl⟩ : syracuseStep 2844161 = 2133121) B2133121
theorem B1896107 : Blo 1895435 1896107 := bstep (se 1 (by rfl) ⟨1422080, by rfl⟩ : syracuseStep 1896107 = 2844161) B2844161
theorem B4799533 : Blo 1895435 4799533 := bbase (se 3 (by rfl) ⟨899912, by rfl⟩ : syracuseStep 4799533 = 1799825) (by norm_num)
theorem B6399377 : Blo 1895435 6399377 := bstep (se 2 (by rfl) ⟨2399766, by rfl⟩ : syracuseStep 6399377 = 4799533) B4799533
theorem B4266251 : Blo 1895435 4266251 := bstep (se 1 (by rfl) ⟨3199688, by rfl⟩ : syracuseStep 4266251 = 6399377) B6399377
theorem B2844167 : Blo 1895435 2844167 := bstep (se 1 (by rfl) ⟨2133125, by rfl⟩ : syracuseStep 2844167 = 4266251) B4266251
theorem B1896111 : Blo 1895435 1896111 := bstep (se 1 (by rfl) ⟨1422083, by rfl⟩ : syracuseStep 1896111 = 2844167) B2844167
theorem B2844173 : Blo 1895435 2844173 := bbase (se 3 (by rfl) ⟨533282, by rfl⟩ : syracuseStep 2844173 = 1066565) (by norm_num)
theorem B1896115 : Blo 1895435 1896115 := bstep (se 1 (by rfl) ⟨1422086, by rfl⟩ : syracuseStep 1896115 = 2844173) B2844173
theorem B4266269 : Blo 1895435 4266269 := bbase (se 3 (by rfl) ⟨799925, by rfl⟩ : syracuseStep 4266269 = 1599851) (by norm_num)
theorem B2844179 : Blo 1895435 2844179 := bstep (se 1 (by rfl) ⟨2133134, by rfl⟩ : syracuseStep 2844179 = 4266269) B4266269
theorem B1896119 : Blo 1895435 1896119 := bstep (se 1 (by rfl) ⟨1422089, by rfl⟩ : syracuseStep 1896119 = 2844179) B2844179
theorem B3199709 : Blo 1895435 3199709 := bbase (se 3 (by rfl) ⟨599945, by rfl⟩ : syracuseStep 3199709 = 1199891) (by norm_num)
theorem B2133139 : Blo 1895435 2133139 := bstep (se 1 (by rfl) ⟨1599854, by rfl⟩ : syracuseStep 2133139 = 3199709) B3199709
theorem B2844185 : Blo 1895435 2844185 := bstep (se 2 (by rfl) ⟨1066569, by rfl⟩ : syracuseStep 2844185 = 2133139) B2133139
theorem B1896123 : Blo 1895435 1896123 := bstep (se 1 (by rfl) ⟨1422092, by rfl⟩ : syracuseStep 1896123 = 2844185) B2844185
theorem B3416885 : Blo 1895435 3416885 := bbase (se 5 (by rfl) ⟨160166, by rfl⟩ : syracuseStep 3416885 = 320333) (by norm_num)
theorem B2277923 : Blo 1895435 2277923 := bstep (se 1 (by rfl) ⟨1708442, by rfl⟩ : syracuseStep 2277923 = 3416885) B3416885
theorem B6074461 : Blo 1895435 6074461 := bstep (se 3 (by rfl) ⟨1138961, by rfl⟩ : syracuseStep 6074461 = 2277923) B2277923
theorem B8099281 : Blo 1895435 8099281 := bstep (se 2 (by rfl) ⟨3037230, by rfl⟩ : syracuseStep 8099281 = 6074461) B6074461
theorem B10799041 : Blo 1895435 10799041 := bstep (se 2 (by rfl) ⟨4049640, by rfl⟩ : syracuseStep 10799041 = 8099281) B8099281
theorem B14398721 : Blo 1895435 14398721 := bstep (se 2 (by rfl) ⟨5399520, by rfl⟩ : syracuseStep 14398721 = 10799041) B10799041
theorem B9599147 : Blo 1895435 9599147 := bstep (se 1 (by rfl) ⟨7199360, by rfl⟩ : syracuseStep 9599147 = 14398721) B14398721
theorem B6399431 : Blo 1895435 6399431 := bstep (se 1 (by rfl) ⟨4799573, by rfl⟩ : syracuseStep 6399431 = 9599147) B9599147
theorem B4266287 : Blo 1895435 4266287 := bstep (se 1 (by rfl) ⟨3199715, by rfl⟩ : syracuseStep 4266287 = 6399431) B6399431
theorem B2844191 : Blo 1895435 2844191 := bstep (se 1 (by rfl) ⟨2133143, by rfl⟩ : syracuseStep 2844191 = 4266287) B4266287
theorem B1896127 : Blo 1895435 1896127 := bstep (se 1 (by rfl) ⟨1422095, by rfl⟩ : syracuseStep 1896127 = 2844191) B2844191
theorem B2844197 : Blo 1895435 2844197 := bbase (se 4 (by rfl) ⟨266643, by rfl⟩ : syracuseStep 2844197 = 533287) (by norm_num)
theorem B1896131 : Blo 1895435 1896131 := bstep (se 1 (by rfl) ⟨1422098, by rfl⟩ : syracuseStep 1896131 = 2844197) B2844197
theorem B2399797 : Blo 1895435 2399797 := bbase (se 5 (by rfl) ⟨112490, by rfl⟩ : syracuseStep 2399797 = 224981) (by norm_num)
theorem B3199729 : Blo 1895435 3199729 := bstep (se 2 (by rfl) ⟨1199898, by rfl⟩ : syracuseStep 3199729 = 2399797) B2399797
theorem B4266305 : Blo 1895435 4266305 := bstep (se 2 (by rfl) ⟨1599864, by rfl⟩ : syracuseStep 4266305 = 3199729) B3199729
theorem B2844203 : Blo 1895435 2844203 := bstep (se 1 (by rfl) ⟨2133152, by rfl⟩ : syracuseStep 2844203 = 4266305) B4266305
theorem B1896135 : Blo 1895435 1896135 := bstep (se 1 (by rfl) ⟨1422101, by rfl⟩ : syracuseStep 1896135 = 2844203) B2844203
theorem B2133157 : Blo 1895435 2133157 := bbase (se 4 (by rfl) ⟨199983, by rfl⟩ : syracuseStep 2133157 = 399967) (by norm_num)
theorem B2844209 : Blo 1895435 2844209 := bstep (se 2 (by rfl) ⟨1066578, by rfl⟩ : syracuseStep 2844209 = 2133157) B2133157
theorem B1896139 : Blo 1895435 1896139 := bstep (se 1 (by rfl) ⟨1422104, by rfl⟩ : syracuseStep 1896139 = 2844209) B2844209
theorem B18223541 : Blo 1895435 18223541 := bbase (se 5 (by rfl) ⟨854228, by rfl⟩ : syracuseStep 18223541 = 1708457) (by norm_num)
theorem B12149027 : Blo 1895435 12149027 := bstep (se 1 (by rfl) ⟨9111770, by rfl⟩ : syracuseStep 12149027 = 18223541) B18223541
theorem B8099351 : Blo 1895435 8099351 := bstep (se 1 (by rfl) ⟨6074513, by rfl⟩ : syracuseStep 8099351 = 12149027) B12149027
theorem B5399567 : Blo 1895435 5399567 := bstep (se 1 (by rfl) ⟨4049675, by rfl⟩ : syracuseStep 5399567 = 8099351) B8099351
theorem B3599711 : Blo 1895435 3599711 := bstep (se 1 (by rfl) ⟨2699783, by rfl⟩ : syracuseStep 3599711 = 5399567) B5399567
theorem B2399807 : Blo 1895435 2399807 := bstep (se 1 (by rfl) ⟨1799855, by rfl⟩ : syracuseStep 2399807 = 3599711) B3599711
theorem B6399485 : Blo 1895435 6399485 := bstep (se 3 (by rfl) ⟨1199903, by rfl⟩ : syracuseStep 6399485 = 2399807) B2399807
theorem B4266323 : Blo 1895435 4266323 := bstep (se 1 (by rfl) ⟨3199742, by rfl⟩ : syracuseStep 4266323 = 6399485) B6399485
theorem B2844215 : Blo 1895435 2844215 := bstep (se 1 (by rfl) ⟨2133161, by rfl⟩ : syracuseStep 2844215 = 4266323) B4266323
theorem B1896143 : Blo 1895435 1896143 := bstep (se 1 (by rfl) ⟨1422107, by rfl⟩ : syracuseStep 1896143 = 2844215) B2844215
theorem B2844221 : Blo 1895435 2844221 := bbase (se 3 (by rfl) ⟨533291, by rfl⟩ : syracuseStep 2844221 = 1066583) (by norm_num)
theorem B1896147 : Blo 1895435 1896147 := bstep (se 1 (by rfl) ⟨1422110, by rfl⟩ : syracuseStep 1896147 = 2844221) B2844221
theorem B4266341 : Blo 1895435 4266341 := bbase (se 4 (by rfl) ⟨399969, by rfl⟩ : syracuseStep 4266341 = 799939) (by norm_num)
theorem B2844227 : Blo 1895435 2844227 := bstep (se 1 (by rfl) ⟨2133170, by rfl⟩ : syracuseStep 2844227 = 4266341) B4266341
theorem B1896151 : Blo 1895435 1896151 := bstep (se 1 (by rfl) ⟨1422113, by rfl⟩ : syracuseStep 1896151 = 2844227) B2844227
theorem B4799645 : Blo 1895435 4799645 := bbase (se 3 (by rfl) ⟨899933, by rfl⟩ : syracuseStep 4799645 = 1799867) (by norm_num)
theorem B3199763 : Blo 1895435 3199763 := bstep (se 1 (by rfl) ⟨2399822, by rfl⟩ : syracuseStep 3199763 = 4799645) B4799645
theorem B2133175 : Blo 1895435 2133175 := bstep (se 1 (by rfl) ⟨1599881, by rfl⟩ : syracuseStep 2133175 = 3199763) B3199763
theorem B2844233 : Blo 1895435 2844233 := bstep (se 2 (by rfl) ⟨1066587, by rfl⟩ : syracuseStep 2844233 = 2133175) B2133175
theorem B1896155 : Blo 1895435 1896155 := bstep (se 1 (by rfl) ⟨1422116, by rfl⟩ : syracuseStep 1896155 = 2844233) B2844233
theorem B3599741 : Blo 1895435 3599741 := bbase (se 3 (by rfl) ⟨674951, by rfl⟩ : syracuseStep 3599741 = 1349903) (by norm_num)
theorem B9599309 : Blo 1895435 9599309 := bstep (se 3 (by rfl) ⟨1799870, by rfl⟩ : syracuseStep 9599309 = 3599741) B3599741
theorem B6399539 : Blo 1895435 6399539 := bstep (se 1 (by rfl) ⟨4799654, by rfl⟩ : syracuseStep 6399539 = 9599309) B9599309
theorem B4266359 : Blo 1895435 4266359 := bstep (se 1 (by rfl) ⟨3199769, by rfl⟩ : syracuseStep 4266359 = 6399539) B6399539
theorem B2844239 : Blo 1895435 2844239 := bstep (se 1 (by rfl) ⟨2133179, by rfl⟩ : syracuseStep 2844239 = 4266359) B4266359
theorem B1896159 : Blo 1895435 1896159 := bstep (se 1 (by rfl) ⟨1422119, by rfl⟩ : syracuseStep 1896159 = 2844239) B2844239
theorem B2844245 : Blo 1895435 2844245 := bbase (se 8 (by rfl) ⟨16665, by rfl⟩ : syracuseStep 2844245 = 33331) (by norm_num)
theorem B1896163 : Blo 1895435 1896163 := bstep (se 1 (by rfl) ⟨1422122, by rfl⟩ : syracuseStep 1896163 = 2844245) B2844245
theorem B3332549 : Blo 1895435 3332549 := bbase (se 4 (by rfl) ⟨312426, by rfl⟩ : syracuseStep 3332549 = 624853) (by norm_num)
theorem B8886797 : Blo 1895435 8886797 := bstep (se 3 (by rfl) ⟨1666274, by rfl⟩ : syracuseStep 8886797 = 3332549) B3332549
theorem B5924531 : Blo 1895435 5924531 := bstep (se 1 (by rfl) ⟨4443398, by rfl⟩ : syracuseStep 5924531 = 8886797) B8886797
theorem B3949687 : Blo 1895435 3949687 := bstep (se 1 (by rfl) ⟨2962265, by rfl⟩ : syracuseStep 3949687 = 5924531) B5924531
theorem B21064997 : Blo 1895435 21064997 := bstep (se 4 (by rfl) ⟨1974843, by rfl⟩ : syracuseStep 21064997 = 3949687) B3949687
theorem B14043331 : Blo 1895435 14043331 := bstep (se 1 (by rfl) ⟨10532498, by rfl⟩ : syracuseStep 14043331 = 21064997) B21064997
theorem B18724441 : Blo 1895435 18724441 := bstep (se 2 (by rfl) ⟨7021665, by rfl⟩ : syracuseStep 18724441 = 14043331) B14043331
theorem B24965921 : Blo 1895435 24965921 := bstep (se 2 (by rfl) ⟨9362220, by rfl⟩ : syracuseStep 24965921 = 18724441) B18724441
theorem B66575789 : Blo 1895435 66575789 := bstep (se 3 (by rfl) ⟨12482960, by rfl⟩ : syracuseStep 66575789 = 24965921) B24965921
theorem B44383859 : Blo 1895435 44383859 := bstep (se 1 (by rfl) ⟨33287894, by rfl⟩ : syracuseStep 44383859 = 66575789) B66575789
theorem B29589239 : Blo 1895435 29589239 := bstep (se 1 (by rfl) ⟨22191929, by rfl⟩ : syracuseStep 29589239 = 44383859) B44383859
theorem B78904637 : Blo 1895435 78904637 := bstep (se 3 (by rfl) ⟨14794619, by rfl⟩ : syracuseStep 78904637 = 29589239) B29589239
theorem B52603091 : Blo 1895435 52603091 := bstep (se 1 (by rfl) ⟨39452318, by rfl⟩ : syracuseStep 52603091 = 78904637) B78904637
theorem B35068727 : Blo 1895435 35068727 := bstep (se 1 (by rfl) ⟨26301545, by rfl⟩ : syracuseStep 35068727 = 52603091) B52603091
theorem B23379151 : Blo 1895435 23379151 := bstep (se 1 (by rfl) ⟨17534363, by rfl⟩ : syracuseStep 23379151 = 35068727) B35068727
theorem B31172201 : Blo 1895435 31172201 := bstep (se 2 (by rfl) ⟨11689575, by rfl⟩ : syracuseStep 31172201 = 23379151) B23379151
theorem B20781467 : Blo 1895435 20781467 := bstep (se 1 (by rfl) ⟨15586100, by rfl⟩ : syracuseStep 20781467 = 31172201) B31172201
theorem B13854311 : Blo 1895435 13854311 := bstep (se 1 (by rfl) ⟨10390733, by rfl⟩ : syracuseStep 13854311 = 20781467) B20781467
theorem B9236207 : Blo 1895435 9236207 := bstep (se 1 (by rfl) ⟨6927155, by rfl⟩ : syracuseStep 9236207 = 13854311) B13854311
theorem B6157471 : Blo 1895435 6157471 := bstep (se 1 (by rfl) ⟨4618103, by rfl⟩ : syracuseStep 6157471 = 9236207) B9236207
theorem B8209961 : Blo 1895435 8209961 := bstep (se 2 (by rfl) ⟨3078735, by rfl⟩ : syracuseStep 8209961 = 6157471) B6157471
theorem B5473307 : Blo 1895435 5473307 := bstep (se 1 (by rfl) ⟨4104980, by rfl⟩ : syracuseStep 5473307 = 8209961) B8209961
theorem B3648871 : Blo 1895435 3648871 := bstep (se 1 (by rfl) ⟨2736653, by rfl⟩ : syracuseStep 3648871 = 5473307) B5473307
theorem B19460645 : Blo 1895435 19460645 := bstep (se 4 (by rfl) ⟨1824435, by rfl⟩ : syracuseStep 19460645 = 3648871) B3648871
theorem B12973763 : Blo 1895435 12973763 := bstep (se 1 (by rfl) ⟨9730322, by rfl⟩ : syracuseStep 12973763 = 19460645) B19460645
theorem B8649175 : Blo 1895435 8649175 := bstep (se 1 (by rfl) ⟨6486881, by rfl⟩ : syracuseStep 8649175 = 12973763) B12973763
theorem B11532233 : Blo 1895435 11532233 := bstep (se 2 (by rfl) ⟨4324587, by rfl⟩ : syracuseStep 11532233 = 8649175) B8649175
theorem B7688155 : Blo 1895435 7688155 := bstep (se 1 (by rfl) ⟨5766116, by rfl⟩ : syracuseStep 7688155 = 11532233) B11532233
theorem B10250873 : Blo 1895435 10250873 := bstep (se 2 (by rfl) ⟨3844077, by rfl⟩ : syracuseStep 10250873 = 7688155) B7688155
theorem B6833915 : Blo 1895435 6833915 := bstep (se 1 (by rfl) ⟨5125436, by rfl⟩ : syracuseStep 6833915 = 10250873) B10250873
theorem B4555943 : Blo 1895435 4555943 := bstep (se 1 (by rfl) ⟨3416957, by rfl⟩ : syracuseStep 4555943 = 6833915) B6833915
theorem B3037295 : Blo 1895435 3037295 := bstep (se 1 (by rfl) ⟨2277971, by rfl⟩ : syracuseStep 3037295 = 4555943) B4555943
theorem B8099453 : Blo 1895435 8099453 := bstep (se 3 (by rfl) ⟨1518647, by rfl⟩ : syracuseStep 8099453 = 3037295) B3037295
theorem B5399635 : Blo 1895435 5399635 := bstep (se 1 (by rfl) ⟨4049726, by rfl⟩ : syracuseStep 5399635 = 8099453) B8099453
theorem B7199513 : Blo 1895435 7199513 := bstep (se 2 (by rfl) ⟨2699817, by rfl⟩ : syracuseStep 7199513 = 5399635) B5399635
theorem B4799675 : Blo 1895435 4799675 := bstep (se 1 (by rfl) ⟨3599756, by rfl⟩ : syracuseStep 4799675 = 7199513) B7199513
theorem B3199783 : Blo 1895435 3199783 := bstep (se 1 (by rfl) ⟨2399837, by rfl⟩ : syracuseStep 3199783 = 4799675) B4799675
theorem B4266377 : Blo 1895435 4266377 := bstep (se 2 (by rfl) ⟨1599891, by rfl⟩ : syracuseStep 4266377 = 3199783) B3199783
theorem B2844251 : Blo 1895435 2844251 := bstep (se 1 (by rfl) ⟨2133188, by rfl⟩ : syracuseStep 2844251 = 4266377) B4266377
theorem B1896167 : Blo 1895435 1896167 := bstep (se 1 (by rfl) ⟨1422125, by rfl⟩ : syracuseStep 1896167 = 2844251) B2844251
theorem B2133193 : Blo 1895435 2133193 := bbase (se 2 (by rfl) ⟨799947, by rfl⟩ : syracuseStep 2133193 = 1599895) (by norm_num)
theorem B2844257 : Blo 1895435 2844257 := bstep (se 2 (by rfl) ⟨1066596, by rfl⟩ : syracuseStep 2844257 = 2133193) B2133193
theorem B1896171 : Blo 1895435 1896171 := bstep (se 1 (by rfl) ⟨1422128, by rfl⟩ : syracuseStep 1896171 = 2844257) B2844257
theorem B3844093 : Blo 1895435 3844093 := bbase (se 3 (by rfl) ⟨720767, by rfl⟩ : syracuseStep 3844093 = 1441535) (by norm_num)
theorem B5125457 : Blo 1895435 5125457 := bstep (se 2 (by rfl) ⟨1922046, by rfl⟩ : syracuseStep 5125457 = 3844093) B3844093
theorem B13667885 : Blo 1895435 13667885 := bstep (se 3 (by rfl) ⟨2562728, by rfl⟩ : syracuseStep 13667885 = 5125457) B5125457
theorem B9111923 : Blo 1895435 9111923 := bstep (se 1 (by rfl) ⟨6833942, by rfl⟩ : syracuseStep 9111923 = 13667885) B13667885
theorem B6074615 : Blo 1895435 6074615 := bstep (se 1 (by rfl) ⟨4555961, by rfl⟩ : syracuseStep 6074615 = 9111923) B9111923
theorem B16198973 : Blo 1895435 16198973 := bstep (se 3 (by rfl) ⟨3037307, by rfl⟩ : syracuseStep 16198973 = 6074615) B6074615
theorem B10799315 : Blo 1895435 10799315 := bstep (se 1 (by rfl) ⟨8099486, by rfl⟩ : syracuseStep 10799315 = 16198973) B16198973
theorem B7199543 : Blo 1895435 7199543 := bstep (se 1 (by rfl) ⟨5399657, by rfl⟩ : syracuseStep 7199543 = 10799315) B10799315
theorem B4799695 : Blo 1895435 4799695 := bstep (se 1 (by rfl) ⟨3599771, by rfl⟩ : syracuseStep 4799695 = 7199543) B7199543
theorem B6399593 : Blo 1895435 6399593 := bstep (se 2 (by rfl) ⟨2399847, by rfl⟩ : syracuseStep 6399593 = 4799695) B4799695
theorem B4266395 : Blo 1895435 4266395 := bstep (se 1 (by rfl) ⟨3199796, by rfl⟩ : syracuseStep 4266395 = 6399593) B6399593
theorem B2844263 : Blo 1895435 2844263 := bstep (se 1 (by rfl) ⟨2133197, by rfl⟩ : syracuseStep 2844263 = 4266395) B4266395
theorem B1896175 : Blo 1895435 1896175 := bstep (se 1 (by rfl) ⟨1422131, by rfl⟩ : syracuseStep 1896175 = 2844263) B2844263
theorem B2844269 : Blo 1895435 2844269 := bbase (se 3 (by rfl) ⟨533300, by rfl⟩ : syracuseStep 2844269 = 1066601) (by norm_num)
theorem B1896179 : Blo 1895435 1896179 := bstep (se 1 (by rfl) ⟨1422134, by rfl⟩ : syracuseStep 1896179 = 2844269) B2844269
theorem B4266413 : Blo 1895435 4266413 := bbase (se 3 (by rfl) ⟨799952, by rfl⟩ : syracuseStep 4266413 = 1599905) (by norm_num)
theorem B2844275 : Blo 1895435 2844275 := bstep (se 1 (by rfl) ⟨2133206, by rfl⟩ : syracuseStep 2844275 = 4266413) B4266413
theorem B1896183 : Blo 1895435 1896183 := bstep (se 1 (by rfl) ⟨1422137, by rfl⟩ : syracuseStep 1896183 = 2844275) B2844275
theorem B2024885 : Blo 1895435 2024885 := bbase (se 5 (by rfl) ⟨94916, by rfl⟩ : syracuseStep 2024885 = 189833) (by norm_num)
theorem B5399693 : Blo 1895435 5399693 := bstep (se 3 (by rfl) ⟨1012442, by rfl⟩ : syracuseStep 5399693 = 2024885) B2024885
theorem B3599795 : Blo 1895435 3599795 := bstep (se 1 (by rfl) ⟨2699846, by rfl⟩ : syracuseStep 3599795 = 5399693) B5399693
theorem B2399863 : Blo 1895435 2399863 := bstep (se 1 (by rfl) ⟨1799897, by rfl⟩ : syracuseStep 2399863 = 3599795) B3599795
theorem B3199817 : Blo 1895435 3199817 := bstep (se 2 (by rfl) ⟨1199931, by rfl⟩ : syracuseStep 3199817 = 2399863) B2399863
theorem B2133211 : Blo 1895435 2133211 := bstep (se 1 (by rfl) ⟨1599908, by rfl⟩ : syracuseStep 2133211 = 3199817) B3199817
theorem B2844281 : Blo 1895435 2844281 := bstep (se 2 (by rfl) ⟨1066605, by rfl⟩ : syracuseStep 2844281 = 2133211) B2133211
theorem B1896187 : Blo 1895435 1896187 := bstep (se 1 (by rfl) ⟨1422140, by rfl⟩ : syracuseStep 1896187 = 2844281) B2844281
theorem B3078773 : Blo 1895435 3078773 := bbase (se 5 (by rfl) ⟨144317, by rfl⟩ : syracuseStep 3078773 = 288635) (by norm_num)
theorem B2052515 : Blo 1895435 2052515 := bstep (se 1 (by rfl) ⟨1539386, by rfl⟩ : syracuseStep 2052515 = 3078773) B3078773
theorem B5473373 : Blo 1895435 5473373 := bstep (se 3 (by rfl) ⟨1026257, by rfl⟩ : syracuseStep 5473373 = 2052515) B2052515
theorem B14595661 : Blo 1895435 14595661 := bstep (se 3 (by rfl) ⟨2736686, by rfl⟩ : syracuseStep 14595661 = 5473373) B5473373
theorem B19460881 : Blo 1895435 19460881 := bstep (se 2 (by rfl) ⟨7297830, by rfl⟩ : syracuseStep 19460881 = 14595661) B14595661
theorem B103791365 : Blo 1895435 103791365 := bstep (se 4 (by rfl) ⟨9730440, by rfl⟩ : syracuseStep 103791365 = 19460881) B19460881
theorem B69194243 : Blo 1895435 69194243 := bstep (se 1 (by rfl) ⟨51895682, by rfl⟩ : syracuseStep 69194243 = 103791365) B103791365
theorem B46129495 : Blo 1895435 46129495 := bstep (se 1 (by rfl) ⟨34597121, by rfl⟩ : syracuseStep 46129495 = 69194243) B69194243
theorem B61505993 : Blo 1895435 61505993 := bstep (se 2 (by rfl) ⟨23064747, by rfl⟩ : syracuseStep 61505993 = 46129495) B46129495
theorem B41003995 : Blo 1895435 41003995 := bstep (se 1 (by rfl) ⟨30752996, by rfl⟩ : syracuseStep 41003995 = 61505993) B61505993
theorem B54671993 : Blo 1895435 54671993 := bstep (se 2 (by rfl) ⟨20501997, by rfl⟩ : syracuseStep 54671993 = 41003995) B41003995
theorem B36447995 : Blo 1895435 36447995 := bstep (se 1 (by rfl) ⟨27335996, by rfl⟩ : syracuseStep 36447995 = 54671993) B54671993
theorem B24298663 : Blo 1895435 24298663 := bstep (se 1 (by rfl) ⟨18223997, by rfl⟩ : syracuseStep 24298663 = 36447995) B36447995
theorem B32398217 : Blo 1895435 32398217 := bstep (se 2 (by rfl) ⟨12149331, by rfl⟩ : syracuseStep 32398217 = 24298663) B24298663
theorem B21598811 : Blo 1895435 21598811 := bstep (se 1 (by rfl) ⟨16199108, by rfl⟩ : syracuseStep 21598811 = 32398217) B32398217
theorem B14399207 : Blo 1895435 14399207 := bstep (se 1 (by rfl) ⟨10799405, by rfl⟩ : syracuseStep 14399207 = 21598811) B21598811
theorem B9599471 : Blo 1895435 9599471 := bstep (se 1 (by rfl) ⟨7199603, by rfl⟩ : syracuseStep 9599471 = 14399207) B14399207
theorem B6399647 : Blo 1895435 6399647 := bstep (se 1 (by rfl) ⟨4799735, by rfl⟩ : syracuseStep 6399647 = 9599471) B9599471
theorem B4266431 : Blo 1895435 4266431 := bstep (se 1 (by rfl) ⟨3199823, by rfl⟩ : syracuseStep 4266431 = 6399647) B6399647
theorem B2844287 : Blo 1895435 2844287 := bstep (se 1 (by rfl) ⟨2133215, by rfl⟩ : syracuseStep 2844287 = 4266431) B4266431
theorem B1896191 : Blo 1895435 1896191 := bstep (se 1 (by rfl) ⟨1422143, by rfl⟩ : syracuseStep 1896191 = 2844287) B2844287
theorem B2844293 : Blo 1895435 2844293 := bbase (se 4 (by rfl) ⟨266652, by rfl⟩ : syracuseStep 2844293 = 533305) (by norm_num)
theorem B1896195 : Blo 1895435 1896195 := bstep (se 1 (by rfl) ⟨1422146, by rfl⟩ : syracuseStep 1896195 = 2844293) B2844293
theorem B3199837 : Blo 1895435 3199837 := bbase (se 3 (by rfl) ⟨599969, by rfl⟩ : syracuseStep 3199837 = 1199939) (by norm_num)
theorem B4266449 : Blo 1895435 4266449 := bstep (se 2 (by rfl) ⟨1599918, by rfl⟩ : syracuseStep 4266449 = 3199837) B3199837
theorem B2844299 : Blo 1895435 2844299 := bstep (se 1 (by rfl) ⟨2133224, by rfl⟩ : syracuseStep 2844299 = 4266449) B4266449
theorem B1896199 : Blo 1895435 1896199 := bstep (se 1 (by rfl) ⟨1422149, by rfl⟩ : syracuseStep 1896199 = 2844299) B2844299
theorem B2133229 : Blo 1895435 2133229 := bbase (se 3 (by rfl) ⟨399980, by rfl⟩ : syracuseStep 2133229 = 799961) (by norm_num)
theorem B2844305 : Blo 1895435 2844305 := bstep (se 2 (by rfl) ⟨1066614, by rfl⟩ : syracuseStep 2844305 = 2133229) B2133229
theorem B1896203 : Blo 1895435 1896203 := bstep (se 1 (by rfl) ⟨1422152, by rfl⟩ : syracuseStep 1896203 = 2844305) B2844305
theorem B6399701 : Blo 1895435 6399701 := bbase (se 7 (by rfl) ⟨74996, by rfl⟩ : syracuseStep 6399701 = 149993) (by norm_num)
theorem B4266467 : Blo 1895435 4266467 := bstep (se 1 (by rfl) ⟨3199850, by rfl⟩ : syracuseStep 4266467 = 6399701) B6399701
theorem B2844311 : Blo 1895435 2844311 := bstep (se 1 (by rfl) ⟨2133233, by rfl⟩ : syracuseStep 2844311 = 4266467) B4266467
theorem B1896207 : Blo 1895435 1896207 := bstep (se 1 (by rfl) ⟨1422155, by rfl⟩ : syracuseStep 1896207 = 2844311) B2844311
theorem B2844317 : Blo 1895435 2844317 := bbase (se 3 (by rfl) ⟨533309, by rfl⟩ : syracuseStep 2844317 = 1066619) (by norm_num)
theorem B1896211 : Blo 1895435 1896211 := bstep (se 1 (by rfl) ⟨1422158, by rfl⟩ : syracuseStep 1896211 = 2844317) B2844317
theorem B4266485 : Blo 1895435 4266485 := bbase (se 5 (by rfl) ⟨199991, by rfl⟩ : syracuseStep 4266485 = 399983) (by norm_num)
theorem B2844323 : Blo 1895435 2844323 := bstep (se 1 (by rfl) ⟨2133242, by rfl⟩ : syracuseStep 2844323 = 4266485) B4266485
theorem B1896215 : Blo 1895435 1896215 := bstep (se 1 (by rfl) ⟨1422161, by rfl⟩ : syracuseStep 1896215 = 2844323) B2844323
theorem B4105093 : Blo 1895435 4105093 := bbase (se 4 (by rfl) ⟨384852, by rfl⟩ : syracuseStep 4105093 = 769705) (by norm_num)
theorem B5473457 : Blo 1895435 5473457 := bstep (se 2 (by rfl) ⟨2052546, by rfl⟩ : syracuseStep 5473457 = 4105093) B4105093
theorem B3648971 : Blo 1895435 3648971 := bstep (se 1 (by rfl) ⟨2736728, by rfl⟩ : syracuseStep 3648971 = 5473457) B5473457
theorem B2432647 : Blo 1895435 2432647 := bstep (se 1 (by rfl) ⟨1824485, by rfl⟩ : syracuseStep 2432647 = 3648971) B3648971
theorem B3243529 : Blo 1895435 3243529 := bstep (se 2 (by rfl) ⟨1216323, by rfl⟩ : syracuseStep 3243529 = 2432647) B2432647
theorem B17298821 : Blo 1895435 17298821 := bstep (se 4 (by rfl) ⟨1621764, by rfl⟩ : syracuseStep 17298821 = 3243529) B3243529
theorem B11532547 : Blo 1895435 11532547 := bstep (se 1 (by rfl) ⟨8649410, by rfl⟩ : syracuseStep 11532547 = 17298821) B17298821
theorem B15376729 : Blo 1895435 15376729 := bstep (se 2 (by rfl) ⟨5766273, by rfl⟩ : syracuseStep 15376729 = 11532547) B11532547
theorem B20502305 : Blo 1895435 20502305 := bstep (se 2 (by rfl) ⟨7688364, by rfl⟩ : syracuseStep 20502305 = 15376729) B15376729
theorem B13668203 : Blo 1895435 13668203 := bstep (se 1 (by rfl) ⟨10251152, by rfl⟩ : syracuseStep 13668203 = 20502305) B20502305
theorem B36448541 : Blo 1895435 36448541 := bstep (se 3 (by rfl) ⟨6834101, by rfl⟩ : syracuseStep 36448541 = 13668203) B13668203
theorem B24299027 : Blo 1895435 24299027 := bstep (se 1 (by rfl) ⟨18224270, by rfl⟩ : syracuseStep 24299027 = 36448541) B36448541
theorem B16199351 : Blo 1895435 16199351 := bstep (se 1 (by rfl) ⟨12149513, by rfl⟩ : syracuseStep 16199351 = 24299027) B24299027
theorem B10799567 : Blo 1895435 10799567 := bstep (se 1 (by rfl) ⟨8099675, by rfl⟩ : syracuseStep 10799567 = 16199351) B16199351
theorem B7199711 : Blo 1895435 7199711 := bstep (se 1 (by rfl) ⟨5399783, by rfl⟩ : syracuseStep 7199711 = 10799567) B10799567
theorem B4799807 : Blo 1895435 4799807 := bstep (se 1 (by rfl) ⟨3599855, by rfl⟩ : syracuseStep 4799807 = 7199711) B7199711
theorem B3199871 : Blo 1895435 3199871 := bstep (se 1 (by rfl) ⟨2399903, by rfl⟩ : syracuseStep 3199871 = 4799807) B4799807
theorem B2133247 : Blo 1895435 2133247 := bstep (se 1 (by rfl) ⟨1599935, by rfl⟩ : syracuseStep 2133247 = 3199871) B3199871
theorem B2844329 : Blo 1895435 2844329 := bstep (se 2 (by rfl) ⟨1066623, by rfl⟩ : syracuseStep 2844329 = 2133247) B2133247
theorem B1896219 : Blo 1895435 1896219 := bstep (se 1 (by rfl) ⟨1422164, by rfl⟩ : syracuseStep 1896219 = 2844329) B2844329
theorem B5125589 : Blo 1895435 5125589 := bbase (se 7 (by rfl) ⟨60065, by rfl⟩ : syracuseStep 5125589 = 120131) (by norm_num)
theorem B3417059 : Blo 1895435 3417059 := bstep (se 1 (by rfl) ⟨2562794, by rfl⟩ : syracuseStep 3417059 = 5125589) B5125589
theorem B2278039 : Blo 1895435 2278039 := bstep (se 1 (by rfl) ⟨1708529, by rfl⟩ : syracuseStep 2278039 = 3417059) B3417059
theorem B3037385 : Blo 1895435 3037385 := bstep (se 2 (by rfl) ⟨1139019, by rfl⟩ : syracuseStep 3037385 = 2278039) B2278039
theorem B2024923 : Blo 1895435 2024923 := bstep (se 1 (by rfl) ⟨1518692, by rfl⟩ : syracuseStep 2024923 = 3037385) B3037385
theorem B2699897 : Blo 1895435 2699897 := bstep (se 2 (by rfl) ⟨1012461, by rfl⟩ : syracuseStep 2699897 = 2024923) B2024923
theorem B7199725 : Blo 1895435 7199725 := bstep (se 3 (by rfl) ⟨1349948, by rfl⟩ : syracuseStep 7199725 = 2699897) B2699897
theorem B9599633 : Blo 1895435 9599633 := bstep (se 2 (by rfl) ⟨3599862, by rfl⟩ : syracuseStep 9599633 = 7199725) B7199725
theorem B6399755 : Blo 1895435 6399755 := bstep (se 1 (by rfl) ⟨4799816, by rfl⟩ : syracuseStep 6399755 = 9599633) B9599633
theorem B4266503 : Blo 1895435 4266503 := bstep (se 1 (by rfl) ⟨3199877, by rfl⟩ : syracuseStep 4266503 = 6399755) B6399755
theorem B2844335 : Blo 1895435 2844335 := bstep (se 1 (by rfl) ⟨2133251, by rfl⟩ : syracuseStep 2844335 = 4266503) B4266503
theorem B1896223 : Blo 1895435 1896223 := bstep (se 1 (by rfl) ⟨1422167, by rfl⟩ : syracuseStep 1896223 = 2844335) B2844335
theorem B2844341 : Blo 1895435 2844341 := bbase (se 5 (by rfl) ⟨133328, by rfl⟩ : syracuseStep 2844341 = 266657) (by norm_num)
theorem B1896227 : Blo 1895435 1896227 := bstep (se 1 (by rfl) ⟨1422170, by rfl⟩ : syracuseStep 1896227 = 2844341) B2844341
theorem B4799837 : Blo 1895435 4799837 := bbase (se 3 (by rfl) ⟨899969, by rfl⟩ : syracuseStep 4799837 = 1799939) (by norm_num)
theorem B3199891 : Blo 1895435 3199891 := bstep (se 1 (by rfl) ⟨2399918, by rfl⟩ : syracuseStep 3199891 = 4799837) B4799837
theorem B4266521 : Blo 1895435 4266521 := bstep (se 2 (by rfl) ⟨1599945, by rfl⟩ : syracuseStep 4266521 = 3199891) B3199891
theorem B2844347 : Blo 1895435 2844347 := bstep (se 1 (by rfl) ⟨2133260, by rfl⟩ : syracuseStep 2844347 = 4266521) B4266521
theorem B1896231 : Blo 1895435 1896231 := bstep (se 1 (by rfl) ⟨1422173, by rfl⟩ : syracuseStep 1896231 = 2844347) B2844347
theorem B2133265 : Blo 1895435 2133265 := bbase (se 2 (by rfl) ⟨799974, by rfl⟩ : syracuseStep 2133265 = 1599949) (by norm_num)
theorem B2844353 : Blo 1895435 2844353 := bstep (se 2 (by rfl) ⟨1066632, by rfl⟩ : syracuseStep 2844353 = 2133265) B2133265
theorem B1896235 : Blo 1895435 1896235 := bstep (se 1 (by rfl) ⟨1422176, by rfl⟩ : syracuseStep 1896235 = 2844353) B2844353
theorem B3599893 : Blo 1895435 3599893 := bbase (se 6 (by rfl) ⟨84372, by rfl⟩ : syracuseStep 3599893 = 168745) (by norm_num)
theorem B4799857 : Blo 1895435 4799857 := bstep (se 2 (by rfl) ⟨1799946, by rfl⟩ : syracuseStep 4799857 = 3599893) B3599893
theorem B6399809 : Blo 1895435 6399809 := bstep (se 2 (by rfl) ⟨2399928, by rfl⟩ : syracuseStep 6399809 = 4799857) B4799857
theorem B4266539 : Blo 1895435 4266539 := bstep (se 1 (by rfl) ⟨3199904, by rfl⟩ : syracuseStep 4266539 = 6399809) B6399809
theorem B2844359 : Blo 1895435 2844359 := bstep (se 1 (by rfl) ⟨2133269, by rfl⟩ : syracuseStep 2844359 = 4266539) B4266539
theorem B1896239 : Blo 1895435 1896239 := bstep (se 1 (by rfl) ⟨1422179, by rfl⟩ : syracuseStep 1896239 = 2844359) B2844359
theorem B2844365 : Blo 1895435 2844365 := bbase (se 3 (by rfl) ⟨533318, by rfl⟩ : syracuseStep 2844365 = 1066637) (by norm_num)
theorem B1896243 : Blo 1895435 1896243 := bstep (se 1 (by rfl) ⟨1422182, by rfl⟩ : syracuseStep 1896243 = 2844365) B2844365
theorem B4266557 : Blo 1895435 4266557 := bbase (se 3 (by rfl) ⟨799979, by rfl⟩ : syracuseStep 4266557 = 1599959) (by norm_num)
theorem B2844371 : Blo 1895435 2844371 := bstep (se 1 (by rfl) ⟨2133278, by rfl⟩ : syracuseStep 2844371 = 4266557) B4266557
theorem B1896247 : Blo 1895435 1896247 := bstep (se 1 (by rfl) ⟨1422185, by rfl⟩ : syracuseStep 1896247 = 2844371) B2844371
theorem B3199925 : Blo 1895435 3199925 := bbase (se 5 (by rfl) ⟨149996, by rfl⟩ : syracuseStep 3199925 = 299993) (by norm_num)
theorem B2133283 : Blo 1895435 2133283 := bstep (se 1 (by rfl) ⟨1599962, by rfl⟩ : syracuseStep 2133283 = 3199925) B3199925
theorem B2844377 : Blo 1895435 2844377 := bstep (se 2 (by rfl) ⟨1066641, by rfl⟩ : syracuseStep 2844377 = 2133283) B2133283
theorem B1896251 : Blo 1895435 1896251 := bstep (se 1 (by rfl) ⟨1422188, by rfl⟩ : syracuseStep 1896251 = 2844377) B2844377
theorem B2024957 : Blo 1895435 2024957 := bbase (se 3 (by rfl) ⟨379679, by rfl⟩ : syracuseStep 2024957 = 759359) (by norm_num)
theorem B5399885 : Blo 1895435 5399885 := bstep (se 3 (by rfl) ⟨1012478, by rfl⟩ : syracuseStep 5399885 = 2024957) B2024957
theorem B14399693 : Blo 1895435 14399693 := bstep (se 3 (by rfl) ⟨2699942, by rfl⟩ : syracuseStep 14399693 = 5399885) B5399885
theorem B9599795 : Blo 1895435 9599795 := bstep (se 1 (by rfl) ⟨7199846, by rfl⟩ : syracuseStep 9599795 = 14399693) B14399693
theorem B6399863 : Blo 1895435 6399863 := bstep (se 1 (by rfl) ⟨4799897, by rfl⟩ : syracuseStep 6399863 = 9599795) B9599795
theorem B4266575 : Blo 1895435 4266575 := bstep (se 1 (by rfl) ⟨3199931, by rfl⟩ : syracuseStep 4266575 = 6399863) B6399863
theorem B2844383 : Blo 1895435 2844383 := bstep (se 1 (by rfl) ⟨2133287, by rfl⟩ : syracuseStep 2844383 = 4266575) B4266575
theorem B1896255 : Blo 1895435 1896255 := bstep (se 1 (by rfl) ⟨1422191, by rfl⟩ : syracuseStep 1896255 = 2844383) B2844383
theorem B2844389 : Blo 1895435 2844389 := bbase (se 4 (by rfl) ⟨266661, by rfl⟩ : syracuseStep 2844389 = 533323) (by norm_num)
theorem B1896259 : Blo 1895435 1896259 := bstep (se 1 (by rfl) ⟨1422194, by rfl⟩ : syracuseStep 1896259 = 2844389) B2844389
theorem B5399909 : Blo 1895435 5399909 := bbase (se 4 (by rfl) ⟨506241, by rfl⟩ : syracuseStep 5399909 = 1012483) (by norm_num)
theorem B3599939 : Blo 1895435 3599939 := bstep (se 1 (by rfl) ⟨2699954, by rfl⟩ : syracuseStep 3599939 = 5399909) B5399909
theorem B2399959 : Blo 1895435 2399959 := bstep (se 1 (by rfl) ⟨1799969, by rfl⟩ : syracuseStep 2399959 = 3599939) B3599939
theorem B3199945 : Blo 1895435 3199945 := bstep (se 2 (by rfl) ⟨1199979, by rfl⟩ : syracuseStep 3199945 = 2399959) B2399959
theorem B4266593 : Blo 1895435 4266593 := bstep (se 2 (by rfl) ⟨1599972, by rfl⟩ : syracuseStep 4266593 = 3199945) B3199945
theorem B2844395 : Blo 1895435 2844395 := bstep (se 1 (by rfl) ⟨2133296, by rfl⟩ : syracuseStep 2844395 = 4266593) B4266593
theorem B1896263 : Blo 1895435 1896263 := bstep (se 1 (by rfl) ⟨1422197, by rfl⟩ : syracuseStep 1896263 = 2844395) B2844395
theorem B2133301 : Blo 1895435 2133301 := bbase (se 5 (by rfl) ⟨99998, by rfl⟩ : syracuseStep 2133301 = 199997) (by norm_num)
theorem B2844401 : Blo 1895435 2844401 := bstep (se 2 (by rfl) ⟨1066650, by rfl⟩ : syracuseStep 2844401 = 2133301) B2133301
theorem B1896267 : Blo 1895435 1896267 := bstep (se 1 (by rfl) ⟨1422200, by rfl⟩ : syracuseStep 1896267 = 2844401) B2844401
theorem B2399969 : Blo 1895435 2399969 := bbase (se 2 (by rfl) ⟨899988, by rfl⟩ : syracuseStep 2399969 = 1799977) (by norm_num)
theorem B6399917 : Blo 1895435 6399917 := bstep (se 3 (by rfl) ⟨1199984, by rfl⟩ : syracuseStep 6399917 = 2399969) B2399969
theorem B4266611 : Blo 1895435 4266611 := bstep (se 1 (by rfl) ⟨3199958, by rfl⟩ : syracuseStep 4266611 = 6399917) B6399917
theorem B2844407 : Blo 1895435 2844407 := bstep (se 1 (by rfl) ⟨2133305, by rfl⟩ : syracuseStep 2844407 = 4266611) B4266611
theorem B1896271 : Blo 1895435 1896271 := bstep (se 1 (by rfl) ⟨1422203, by rfl⟩ : syracuseStep 1896271 = 2844407) B2844407
theorem B2844413 : Blo 1895435 2844413 := bbase (se 3 (by rfl) ⟨533327, by rfl⟩ : syracuseStep 2844413 = 1066655) (by norm_num)
theorem B1896275 : Blo 1895435 1896275 := bstep (se 1 (by rfl) ⟨1422206, by rfl⟩ : syracuseStep 1896275 = 2844413) B2844413
theorem B4266629 : Blo 1895435 4266629 := bbase (se 4 (by rfl) ⟨399996, by rfl⟩ : syracuseStep 4266629 = 799993) (by norm_num)
theorem B2844419 : Blo 1895435 2844419 := bstep (se 1 (by rfl) ⟨2133314, by rfl⟩ : syracuseStep 2844419 = 4266629) B4266629
theorem B1896279 : Blo 1895435 1896279 := bstep (se 1 (by rfl) ⟨1422209, by rfl⟩ : syracuseStep 1896279 = 2844419) B2844419
theorem B4324853 : Blo 1895435 4324853 := bbase (se 5 (by rfl) ⟨202727, by rfl⟩ : syracuseStep 4324853 = 405455) (by norm_num)
theorem B11532941 : Blo 1895435 11532941 := bstep (se 3 (by rfl) ⟨2162426, by rfl⟩ : syracuseStep 11532941 = 4324853) B4324853
theorem B7688627 : Blo 1895435 7688627 := bstep (se 1 (by rfl) ⟨5766470, by rfl⟩ : syracuseStep 7688627 = 11532941) B11532941
theorem B5125751 : Blo 1895435 5125751 := bstep (se 1 (by rfl) ⟨3844313, by rfl⟩ : syracuseStep 5125751 = 7688627) B7688627
theorem B3417167 : Blo 1895435 3417167 := bstep (se 1 (by rfl) ⟨2562875, by rfl⟩ : syracuseStep 3417167 = 5125751) B5125751
theorem B9112445 : Blo 1895435 9112445 := bstep (se 3 (by rfl) ⟨1708583, by rfl⟩ : syracuseStep 9112445 = 3417167) B3417167
theorem B6074963 : Blo 1895435 6074963 := bstep (se 1 (by rfl) ⟨4556222, by rfl⟩ : syracuseStep 6074963 = 9112445) B9112445
theorem B4049975 : Blo 1895435 4049975 := bstep (se 1 (by rfl) ⟨3037481, by rfl⟩ : syracuseStep 4049975 = 6074963) B6074963
theorem B2699983 : Blo 1895435 2699983 := bstep (se 1 (by rfl) ⟨2024987, by rfl⟩ : syracuseStep 2699983 = 4049975) B4049975
theorem B3599977 : Blo 1895435 3599977 := bstep (se 2 (by rfl) ⟨1349991, by rfl⟩ : syracuseStep 3599977 = 2699983) B2699983
theorem B4799969 : Blo 1895435 4799969 := bstep (se 2 (by rfl) ⟨1799988, by rfl⟩ : syracuseStep 4799969 = 3599977) B3599977
theorem B3199979 : Blo 1895435 3199979 := bstep (se 1 (by rfl) ⟨2399984, by rfl⟩ : syracuseStep 3199979 = 4799969) B4799969
theorem B2133319 : Blo 1895435 2133319 := bstep (se 1 (by rfl) ⟨1599989, by rfl⟩ : syracuseStep 2133319 = 3199979) B3199979
theorem B2844425 : Blo 1895435 2844425 := bstep (se 2 (by rfl) ⟨1066659, by rfl⟩ : syracuseStep 2844425 = 2133319) B2133319
theorem B1896283 : Blo 1895435 1896283 := bstep (se 1 (by rfl) ⟨1422212, by rfl⟩ : syracuseStep 1896283 = 2844425) B2844425
theorem B9599957 : Blo 1895435 9599957 := bbase (se 7 (by rfl) ⟨112499, by rfl⟩ : syracuseStep 9599957 = 224999) (by norm_num)
theorem B6399971 : Blo 1895435 6399971 := bstep (se 1 (by rfl) ⟨4799978, by rfl⟩ : syracuseStep 6399971 = 9599957) B9599957
theorem B4266647 : Blo 1895435 4266647 := bstep (se 1 (by rfl) ⟨3199985, by rfl⟩ : syracuseStep 4266647 = 6399971) B6399971
theorem B2844431 : Blo 1895435 2844431 := bstep (se 1 (by rfl) ⟨2133323, by rfl⟩ : syracuseStep 2844431 = 4266647) B4266647
theorem B1896287 : Blo 1895435 1896287 := bstep (se 1 (by rfl) ⟨1422215, by rfl⟩ : syracuseStep 1896287 = 2844431) B2844431
theorem B2844437 : Blo 1895435 2844437 := bbase (se 6 (by rfl) ⟨66666, by rfl⟩ : syracuseStep 2844437 = 133333) (by norm_num)
theorem B1896291 : Blo 1895435 1896291 := bstep (se 1 (by rfl) ⟨1422218, by rfl⟩ : syracuseStep 1896291 = 2844437) B2844437
theorem B2922589 : Blo 1895435 2922589 := bbase (se 3 (by rfl) ⟨547985, by rfl⟩ : syracuseStep 2922589 = 1095971) (by norm_num)
theorem B249394261 : Blo 1895435 249394261 := bstep (se 8 (by rfl) ⟨1461294, by rfl⟩ : syracuseStep 249394261 = 2922589) B2922589
theorem B332525681 : Blo 1895435 332525681 := bstep (se 2 (by rfl) ⟨124697130, by rfl⟩ : syracuseStep 332525681 = 249394261) B249394261
theorem B221683787 : Blo 1895435 221683787 := bstep (se 1 (by rfl) ⟨166262840, by rfl⟩ : syracuseStep 221683787 = 332525681) B332525681
theorem B147789191 : Blo 1895435 147789191 := bstep (se 1 (by rfl) ⟨110841893, by rfl⟩ : syracuseStep 147789191 = 221683787) B221683787
theorem B98526127 : Blo 1895435 98526127 := bstep (se 1 (by rfl) ⟨73894595, by rfl⟩ : syracuseStep 98526127 = 147789191) B147789191
theorem B131368169 : Blo 1895435 131368169 := bstep (se 2 (by rfl) ⟨49263063, by rfl⟩ : syracuseStep 131368169 = 98526127) B98526127
theorem B350315117 : Blo 1895435 350315117 := bstep (se 3 (by rfl) ⟨65684084, by rfl⟩ : syracuseStep 350315117 = 131368169) B131368169
theorem B233543411 : Blo 1895435 233543411 := bstep (se 1 (by rfl) ⟨175157558, by rfl⟩ : syracuseStep 233543411 = 350315117) B350315117
theorem B155695607 : Blo 1895435 155695607 := bstep (se 1 (by rfl) ⟨116771705, by rfl⟩ : syracuseStep 155695607 = 233543411) B233543411
theorem B103797071 : Blo 1895435 103797071 := bstep (se 1 (by rfl) ⟨77847803, by rfl⟩ : syracuseStep 103797071 = 155695607) B155695607
theorem B69198047 : Blo 1895435 69198047 := bstep (se 1 (by rfl) ⟨51898535, by rfl⟩ : syracuseStep 69198047 = 103797071) B103797071
theorem B46132031 : Blo 1895435 46132031 := bstep (se 1 (by rfl) ⟨34599023, by rfl⟩ : syracuseStep 46132031 = 69198047) B69198047
theorem B123018749 : Blo 1895435 123018749 := bstep (se 3 (by rfl) ⟨23066015, by rfl⟩ : syracuseStep 123018749 = 46132031) B46132031
theorem B82012499 : Blo 1895435 82012499 := bstep (se 1 (by rfl) ⟨61509374, by rfl⟩ : syracuseStep 82012499 = 123018749) B123018749
theorem B54674999 : Blo 1895435 54674999 := bstep (se 1 (by rfl) ⟨41006249, by rfl⟩ : syracuseStep 54674999 = 82012499) B82012499
theorem B36449999 : Blo 1895435 36449999 := bstep (se 1 (by rfl) ⟨27337499, by rfl⟩ : syracuseStep 36449999 = 54674999) B54674999
theorem B24299999 : Blo 1895435 24299999 := bstep (se 1 (by rfl) ⟨18224999, by rfl⟩ : syracuseStep 24299999 = 36449999) B36449999
theorem B16199999 : Blo 1895435 16199999 := bstep (se 1 (by rfl) ⟨12149999, by rfl⟩ : syracuseStep 16199999 = 24299999) B24299999
theorem B10799999 : Blo 1895435 10799999 := bstep (se 1 (by rfl) ⟨8099999, by rfl⟩ : syracuseStep 10799999 = 16199999) B16199999
theorem B7199999 : Blo 1895435 7199999 := bstep (se 1 (by rfl) ⟨5399999, by rfl⟩ : syracuseStep 7199999 = 10799999) B10799999
theorem B4799999 : Blo 1895435 4799999 := bstep (se 1 (by rfl) ⟨3599999, by rfl⟩ : syracuseStep 4799999 = 7199999) B7199999
theorem B3199999 : Blo 1895435 3199999 := bstep (se 1 (by rfl) ⟨2399999, by rfl⟩ : syracuseStep 3199999 = 4799999) B4799999
theorem B4266665 : Blo 1895435 4266665 := bstep (se 2 (by rfl) ⟨1599999, by rfl⟩ : syracuseStep 4266665 = 3199999) B3199999
theorem B2844443 : Blo 1895435 2844443 := bstep (se 1 (by rfl) ⟨2133332, by rfl⟩ : syracuseStep 2844443 = 4266665) B4266665
theorem B1896295 : Blo 1895435 1896295 := bstep (se 1 (by rfl) ⟨1422221, by rfl⟩ : syracuseStep 1896295 = 2844443) B2844443
theorem B2133337 : Blo 1895435 2133337 := bbase (se 2 (by rfl) ⟨800001, by rfl⟩ : syracuseStep 2133337 = 1600003) (by norm_num)
theorem B2844449 : Blo 1895435 2844449 := bstep (se 2 (by rfl) ⟨1066668, by rfl⟩ : syracuseStep 2844449 = 2133337) B2133337
theorem B1896299 : Blo 1895435 1896299 := bstep (se 1 (by rfl) ⟨1422224, by rfl⟩ : syracuseStep 1896299 = 2844449) B2844449
theorem B1922177 : Blo 1895435 1922177 := bbase (se 2 (by rfl) ⟨720816, by rfl⟩ : syracuseStep 1922177 = 1441633) (by norm_num)
theorem B5125805 : Blo 1895435 5125805 := bstep (se 3 (by rfl) ⟨961088, by rfl⟩ : syracuseStep 5125805 = 1922177) B1922177
theorem B3417203 : Blo 1895435 3417203 := bstep (se 1 (by rfl) ⟨2562902, by rfl⟩ : syracuseStep 3417203 = 5125805) B5125805
theorem B2278135 : Blo 1895435 2278135 := bstep (se 1 (by rfl) ⟨1708601, by rfl⟩ : syracuseStep 2278135 = 3417203) B3417203
theorem B3037513 : Blo 1895435 3037513 := bstep (se 2 (by rfl) ⟨1139067, by rfl⟩ : syracuseStep 3037513 = 2278135) B2278135
theorem B4050017 : Blo 1895435 4050017 := bstep (se 2 (by rfl) ⟨1518756, by rfl⟩ : syracuseStep 4050017 = 3037513) B3037513
theorem B2700011 : Blo 1895435 2700011 := bstep (se 1 (by rfl) ⟨2025008, by rfl⟩ : syracuseStep 2700011 = 4050017) B4050017
theorem B7200029 : Blo 1895435 7200029 := bstep (se 3 (by rfl) ⟨1350005, by rfl⟩ : syracuseStep 7200029 = 2700011) B2700011
theorem B4800019 : Blo 1895435 4800019 := bstep (se 1 (by rfl) ⟨3600014, by rfl⟩ : syracuseStep 4800019 = 7200029) B7200029
theorem B6400025 : Blo 1895435 6400025 := bstep (se 2 (by rfl) ⟨2400009, by rfl⟩ : syracuseStep 6400025 = 4800019) B4800019
theorem B4266683 : Blo 1895435 4266683 := bstep (se 1 (by rfl) ⟨3200012, by rfl⟩ : syracuseStep 4266683 = 6400025) B6400025
theorem B2844455 : Blo 1895435 2844455 := bstep (se 1 (by rfl) ⟨2133341, by rfl⟩ : syracuseStep 2844455 = 4266683) B4266683
theorem B1896303 : Blo 1895435 1896303 := bstep (se 1 (by rfl) ⟨1422227, by rfl⟩ : syracuseStep 1896303 = 2844455) B2844455
theorem B2844461 : Blo 1895435 2844461 := bbase (se 3 (by rfl) ⟨533336, by rfl⟩ : syracuseStep 2844461 = 1066673) (by norm_num)
theorem B1896307 : Blo 1895435 1896307 := bstep (se 1 (by rfl) ⟨1422230, by rfl⟩ : syracuseStep 1896307 = 2844461) B2844461
theorem B4266701 : Blo 1895435 4266701 := bbase (se 3 (by rfl) ⟨800006, by rfl⟩ : syracuseStep 4266701 = 1600013) (by norm_num)
theorem B2844467 : Blo 1895435 2844467 := bstep (se 1 (by rfl) ⟨2133350, by rfl⟩ : syracuseStep 2844467 = 4266701) B4266701
theorem B1896311 : Blo 1895435 1896311 := bstep (se 1 (by rfl) ⟨1422233, by rfl⟩ : syracuseStep 1896311 = 2844467) B2844467
theorem B2400025 : Blo 1895435 2400025 := bbase (se 2 (by rfl) ⟨900009, by rfl⟩ : syracuseStep 2400025 = 1800019) (by norm_num)
theorem B3200033 : Blo 1895435 3200033 := bstep (se 2 (by rfl) ⟨1200012, by rfl⟩ : syracuseStep 3200033 = 2400025) B2400025
theorem B2133355 : Blo 1895435 2133355 := bstep (se 1 (by rfl) ⟨1600016, by rfl⟩ : syracuseStep 2133355 = 3200033) B3200033
theorem B2844473 : Blo 1895435 2844473 := bstep (se 2 (by rfl) ⟨1066677, by rfl⟩ : syracuseStep 2844473 = 2133355) B2133355
theorem B1896315 : Blo 1895435 1896315 := bstep (se 1 (by rfl) ⟨1422236, by rfl⟩ : syracuseStep 1896315 = 2844473) B2844473
theorem B8100101 : Blo 1895435 8100101 := bbase (se 4 (by rfl) ⟨759384, by rfl⟩ : syracuseStep 8100101 = 1518769) (by norm_num)
theorem B21600269 : Blo 1895435 21600269 := bstep (se 3 (by rfl) ⟨4050050, by rfl⟩ : syracuseStep 21600269 = 8100101) B8100101
theorem B14400179 : Blo 1895435 14400179 := bstep (se 1 (by rfl) ⟨10800134, by rfl⟩ : syracuseStep 14400179 = 21600269) B21600269
theorem B9600119 : Blo 1895435 9600119 := bstep (se 1 (by rfl) ⟨7200089, by rfl⟩ : syracuseStep 9600119 = 14400179) B14400179
theorem B6400079 : Blo 1895435 6400079 := bstep (se 1 (by rfl) ⟨4800059, by rfl⟩ : syracuseStep 6400079 = 9600119) B9600119
theorem B4266719 : Blo 1895435 4266719 := bstep (se 1 (by rfl) ⟨3200039, by rfl⟩ : syracuseStep 4266719 = 6400079) B6400079
theorem B2844479 : Blo 1895435 2844479 := bstep (se 1 (by rfl) ⟨2133359, by rfl⟩ : syracuseStep 2844479 = 4266719) B4266719
theorem B1896319 : Blo 1895435 1896319 := bstep (se 1 (by rfl) ⟨1422239, by rfl⟩ : syracuseStep 1896319 = 2844479) B2844479
theorem B2844485 : Blo 1895435 2844485 := bbase (se 4 (by rfl) ⟨266670, by rfl⟩ : syracuseStep 2844485 = 533341) (by norm_num)
theorem B1896323 : Blo 1895435 1896323 := bstep (se 1 (by rfl) ⟨1422242, by rfl⟩ : syracuseStep 1896323 = 2844485) B2844485
theorem B3200053 : Blo 1895435 3200053 := bbase (se 5 (by rfl) ⟨150002, by rfl⟩ : syracuseStep 3200053 = 300005) (by norm_num)
theorem B4266737 : Blo 1895435 4266737 := bstep (se 2 (by rfl) ⟨1600026, by rfl⟩ : syracuseStep 4266737 = 3200053) B3200053
theorem B2844491 : Blo 1895435 2844491 := bstep (se 1 (by rfl) ⟨2133368, by rfl⟩ : syracuseStep 2844491 = 4266737) B4266737
theorem B1896327 : Blo 1895435 1896327 := bstep (se 1 (by rfl) ⟨1422245, by rfl⟩ : syracuseStep 1896327 = 2844491) B2844491
theorem B2133373 : Blo 1895435 2133373 := bbase (se 3 (by rfl) ⟨400007, by rfl⟩ : syracuseStep 2133373 = 800015) (by norm_num)
theorem B2844497 : Blo 1895435 2844497 := bstep (se 2 (by rfl) ⟨1066686, by rfl⟩ : syracuseStep 2844497 = 2133373) B2133373
theorem B1896331 : Blo 1895435 1896331 := bstep (se 1 (by rfl) ⟨1422248, by rfl⟩ : syracuseStep 1896331 = 2844497) B2844497
theorem B6400133 : Blo 1895435 6400133 := bbase (se 4 (by rfl) ⟨600012, by rfl⟩ : syracuseStep 6400133 = 1200025) (by norm_num)
theorem B4266755 : Blo 1895435 4266755 := bstep (se 1 (by rfl) ⟨3200066, by rfl⟩ : syracuseStep 4266755 = 6400133) B6400133
theorem B2844503 : Blo 1895435 2844503 := bstep (se 1 (by rfl) ⟨2133377, by rfl⟩ : syracuseStep 2844503 = 4266755) B4266755
theorem B1896335 : Blo 1895435 1896335 := bstep (se 1 (by rfl) ⟨1422251, by rfl⟩ : syracuseStep 1896335 = 2844503) B2844503
theorem B2844509 : Blo 1895435 2844509 := bbase (se 3 (by rfl) ⟨533345, by rfl⟩ : syracuseStep 2844509 = 1066691) (by norm_num)
theorem B1896339 : Blo 1895435 1896339 := bstep (se 1 (by rfl) ⟨1422254, by rfl⟩ : syracuseStep 1896339 = 2844509) B2844509
theorem B4266773 : Blo 1895435 4266773 := bbase (se 6 (by rfl) ⟨100002, by rfl⟩ : syracuseStep 4266773 = 200005) (by norm_num)
theorem B2844515 : Blo 1895435 2844515 := bstep (se 1 (by rfl) ⟨2133386, by rfl⟩ : syracuseStep 2844515 = 4266773) B4266773
theorem B1896343 : Blo 1895435 1896343 := bstep (se 1 (by rfl) ⟨1422257, by rfl⟩ : syracuseStep 1896343 = 2844515) B2844515
theorem B7200197 : Blo 1895435 7200197 := bbase (se 4 (by rfl) ⟨675018, by rfl⟩ : syracuseStep 7200197 = 1350037) (by norm_num)
theorem B4800131 : Blo 1895435 4800131 := bstep (se 1 (by rfl) ⟨3600098, by rfl⟩ : syracuseStep 4800131 = 7200197) B7200197
theorem B3200087 : Blo 1895435 3200087 := bstep (se 1 (by rfl) ⟨2400065, by rfl⟩ : syracuseStep 3200087 = 4800131) B4800131
theorem B2133391 : Blo 1895435 2133391 := bstep (se 1 (by rfl) ⟨1600043, by rfl⟩ : syracuseStep 2133391 = 3200087) B3200087
theorem B2844521 : Blo 1895435 2844521 := bstep (se 2 (by rfl) ⟨1066695, by rfl⟩ : syracuseStep 2844521 = 2133391) B2133391
theorem B1896347 : Blo 1895435 1896347 := bstep (se 1 (by rfl) ⟨1422260, by rfl⟩ : syracuseStep 1896347 = 2844521) B2844521
theorem B1922225 : Blo 1895435 1922225 := bbase (se 2 (by rfl) ⟨720834, by rfl⟩ : syracuseStep 1922225 = 1441669) (by norm_num)
theorem B5125933 : Blo 1895435 5125933 := bstep (se 3 (by rfl) ⟨961112, by rfl⟩ : syracuseStep 5125933 = 1922225) B1922225
theorem B6834577 : Blo 1895435 6834577 := bstep (se 2 (by rfl) ⟨2562966, by rfl⟩ : syracuseStep 6834577 = 5125933) B5125933
theorem B9112769 : Blo 1895435 9112769 := bstep (se 2 (by rfl) ⟨3417288, by rfl⟩ : syracuseStep 9112769 = 6834577) B6834577
theorem B6075179 : Blo 1895435 6075179 := bstep (se 1 (by rfl) ⟨4556384, by rfl⟩ : syracuseStep 6075179 = 9112769) B9112769
theorem B4050119 : Blo 1895435 4050119 := bstep (se 1 (by rfl) ⟨3037589, by rfl⟩ : syracuseStep 4050119 = 6075179) B6075179
theorem B10800317 : Blo 1895435 10800317 := bstep (se 3 (by rfl) ⟨2025059, by rfl⟩ : syracuseStep 10800317 = 4050119) B4050119
theorem B7200211 : Blo 1895435 7200211 := bstep (se 1 (by rfl) ⟨5400158, by rfl⟩ : syracuseStep 7200211 = 10800317) B10800317
theorem B9600281 : Blo 1895435 9600281 := bstep (se 2 (by rfl) ⟨3600105, by rfl⟩ : syracuseStep 9600281 = 7200211) B7200211
theorem B6400187 : Blo 1895435 6400187 := bstep (se 1 (by rfl) ⟨4800140, by rfl⟩ : syracuseStep 6400187 = 9600281) B9600281
theorem B4266791 : Blo 1895435 4266791 := bstep (se 1 (by rfl) ⟨3200093, by rfl⟩ : syracuseStep 4266791 = 6400187) B6400187
theorem B2844527 : Blo 1895435 2844527 := bstep (se 1 (by rfl) ⟨2133395, by rfl⟩ : syracuseStep 2844527 = 4266791) B4266791
theorem B1896351 : Blo 1895435 1896351 := bstep (se 1 (by rfl) ⟨1422263, by rfl⟩ : syracuseStep 1896351 = 2844527) B2844527
theorem B2844533 : Blo 1895435 2844533 := bbase (se 5 (by rfl) ⟨133337, by rfl⟩ : syracuseStep 2844533 = 266675) (by norm_num)
theorem B1896355 : Blo 1895435 1896355 := bstep (se 1 (by rfl) ⟨1422266, by rfl⟩ : syracuseStep 1896355 = 2844533) B2844533
theorem B4556405 : Blo 1895435 4556405 := bbase (se 5 (by rfl) ⟨213581, by rfl⟩ : syracuseStep 4556405 = 427163) (by norm_num)
theorem B3037603 : Blo 1895435 3037603 := bstep (se 1 (by rfl) ⟨2278202, by rfl⟩ : syracuseStep 3037603 = 4556405) B4556405
theorem B4050137 : Blo 1895435 4050137 := bstep (se 2 (by rfl) ⟨1518801, by rfl⟩ : syracuseStep 4050137 = 3037603) B3037603
theorem B2700091 : Blo 1895435 2700091 := bstep (se 1 (by rfl) ⟨2025068, by rfl⟩ : syracuseStep 2700091 = 4050137) B4050137
theorem B3600121 : Blo 1895435 3600121 := bstep (se 2 (by rfl) ⟨1350045, by rfl⟩ : syracuseStep 3600121 = 2700091) B2700091
theorem B4800161 : Blo 1895435 4800161 := bstep (se 2 (by rfl) ⟨1800060, by rfl⟩ : syracuseStep 4800161 = 3600121) B3600121
theorem B3200107 : Blo 1895435 3200107 := bstep (se 1 (by rfl) ⟨2400080, by rfl⟩ : syracuseStep 3200107 = 4800161) B4800161
theorem B4266809 : Blo 1895435 4266809 := bstep (se 2 (by rfl) ⟨1600053, by rfl⟩ : syracuseStep 4266809 = 3200107) B3200107
theorem B2844539 : Blo 1895435 2844539 := bstep (se 1 (by rfl) ⟨2133404, by rfl⟩ : syracuseStep 2844539 = 4266809) B4266809
theorem B1896359 : Blo 1895435 1896359 := bstep (se 1 (by rfl) ⟨1422269, by rfl⟩ : syracuseStep 1896359 = 2844539) B2844539
theorem B2133409 : Blo 1895435 2133409 := bbase (se 2 (by rfl) ⟨800028, by rfl⟩ : syracuseStep 2133409 = 1600057) (by norm_num)
theorem B2844545 : Blo 1895435 2844545 := bstep (se 2 (by rfl) ⟨1066704, by rfl⟩ : syracuseStep 2844545 = 2133409) B2133409
theorem B1896363 : Blo 1895435 1896363 := bstep (se 1 (by rfl) ⟨1422272, by rfl⟩ : syracuseStep 1896363 = 2844545) B2844545
theorem B4800181 : Blo 1895435 4800181 := bbase (se 5 (by rfl) ⟨225008, by rfl⟩ : syracuseStep 4800181 = 450017) (by norm_num)
theorem B6400241 : Blo 1895435 6400241 := bstep (se 2 (by rfl) ⟨2400090, by rfl⟩ : syracuseStep 6400241 = 4800181) B4800181
theorem B4266827 : Blo 1895435 4266827 := bstep (se 1 (by rfl) ⟨3200120, by rfl⟩ : syracuseStep 4266827 = 6400241) B6400241
theorem B2844551 : Blo 1895435 2844551 := bstep (se 1 (by rfl) ⟨2133413, by rfl⟩ : syracuseStep 2844551 = 4266827) B4266827
theorem B1896367 : Blo 1895435 1896367 := bstep (se 1 (by rfl) ⟨1422275, by rfl⟩ : syracuseStep 1896367 = 2844551) B2844551
theorem B2844557 : Blo 1895435 2844557 := bbase (se 3 (by rfl) ⟨533354, by rfl⟩ : syracuseStep 2844557 = 1066709) (by norm_num)
theorem B1896371 : Blo 1895435 1896371 := bstep (se 1 (by rfl) ⟨1422278, by rfl⟩ : syracuseStep 1896371 = 2844557) B2844557
theorem B4266845 : Blo 1895435 4266845 := bbase (se 3 (by rfl) ⟨800033, by rfl⟩ : syracuseStep 4266845 = 1600067) (by norm_num)
theorem B2844563 : Blo 1895435 2844563 := bstep (se 1 (by rfl) ⟨2133422, by rfl⟩ : syracuseStep 2844563 = 4266845) B4266845
theorem B1896375 : Blo 1895435 1896375 := bstep (se 1 (by rfl) ⟨1422281, by rfl⟩ : syracuseStep 1896375 = 2844563) B2844563
theorem B3200141 : Blo 1895435 3200141 := bbase (se 3 (by rfl) ⟨600026, by rfl⟩ : syracuseStep 3200141 = 1200053) (by norm_num)
theorem B2133427 : Blo 1895435 2133427 := bstep (se 1 (by rfl) ⟨1600070, by rfl⟩ : syracuseStep 2133427 = 3200141) B3200141
theorem B2844569 : Blo 1895435 2844569 := bstep (se 2 (by rfl) ⟨1066713, by rfl⟩ : syracuseStep 2844569 = 2133427) B2133427
theorem B1896379 : Blo 1895435 1896379 := bstep (se 1 (by rfl) ⟨1422284, by rfl⟩ : syracuseStep 1896379 = 2844569) B2844569
theorem B4556461 : Blo 1895435 4556461 := bbase (se 3 (by rfl) ⟨854336, by rfl⟩ : syracuseStep 4556461 = 1708673) (by norm_num)
theorem B6075281 : Blo 1895435 6075281 := bstep (se 2 (by rfl) ⟨2278230, by rfl⟩ : syracuseStep 6075281 = 4556461) B4556461
theorem B16200749 : Blo 1895435 16200749 := bstep (se 3 (by rfl) ⟨3037640, by rfl⟩ : syracuseStep 16200749 = 6075281) B6075281
theorem B10800499 : Blo 1895435 10800499 := bstep (se 1 (by rfl) ⟨8100374, by rfl⟩ : syracuseStep 10800499 = 16200749) B16200749
theorem B14400665 : Blo 1895435 14400665 := bstep (se 2 (by rfl) ⟨5400249, by rfl⟩ : syracuseStep 14400665 = 10800499) B10800499
theorem B9600443 : Blo 1895435 9600443 := bstep (se 1 (by rfl) ⟨7200332, by rfl⟩ : syracuseStep 9600443 = 14400665) B14400665
theorem B6400295 : Blo 1895435 6400295 := bstep (se 1 (by rfl) ⟨4800221, by rfl⟩ : syracuseStep 6400295 = 9600443) B9600443
theorem B4266863 : Blo 1895435 4266863 := bstep (se 1 (by rfl) ⟨3200147, by rfl⟩ : syracuseStep 4266863 = 6400295) B6400295
theorem B2844575 : Blo 1895435 2844575 := bstep (se 1 (by rfl) ⟨2133431, by rfl⟩ : syracuseStep 2844575 = 4266863) B4266863
theorem B1896383 : Blo 1895435 1896383 := bstep (se 1 (by rfl) ⟨1422287, by rfl⟩ : syracuseStep 1896383 = 2844575) B2844575
theorem B2844581 : Blo 1895435 2844581 := bbase (se 4 (by rfl) ⟨266679, by rfl⟩ : syracuseStep 2844581 = 533359) (by norm_num)
theorem B1896387 : Blo 1895435 1896387 := bstep (se 1 (by rfl) ⟨1422290, by rfl⟩ : syracuseStep 1896387 = 2844581) B2844581
theorem B2400121 : Blo 1895435 2400121 := bbase (se 2 (by rfl) ⟨900045, by rfl⟩ : syracuseStep 2400121 = 1800091) (by norm_num)
theorem B3200161 : Blo 1895435 3200161 := bstep (se 2 (by rfl) ⟨1200060, by rfl⟩ : syracuseStep 3200161 = 2400121) B2400121
theorem B4266881 : Blo 1895435 4266881 := bstep (se 2 (by rfl) ⟨1600080, by rfl⟩ : syracuseStep 4266881 = 3200161) B3200161
theorem B2844587 : Blo 1895435 2844587 := bstep (se 1 (by rfl) ⟨2133440, by rfl⟩ : syracuseStep 2844587 = 4266881) B4266881
theorem B1896391 : Blo 1895435 1896391 := bstep (se 1 (by rfl) ⟨1422293, by rfl⟩ : syracuseStep 1896391 = 2844587) B2844587
theorem B2133445 : Blo 1895435 2133445 := bbase (se 4 (by rfl) ⟨200010, by rfl⟩ : syracuseStep 2133445 = 400021) (by norm_num)
theorem B2844593 : Blo 1895435 2844593 := bstep (se 2 (by rfl) ⟨1066722, by rfl⟩ : syracuseStep 2844593 = 2133445) B2133445
theorem B1896395 : Blo 1895435 1896395 := bstep (se 1 (by rfl) ⟨1422296, by rfl⟩ : syracuseStep 1896395 = 2844593) B2844593
theorem B3600197 : Blo 1895435 3600197 := bbase (se 4 (by rfl) ⟨337518, by rfl⟩ : syracuseStep 3600197 = 675037) (by norm_num)
theorem B2400131 : Blo 1895435 2400131 := bstep (se 1 (by rfl) ⟨1800098, by rfl⟩ : syracuseStep 2400131 = 3600197) B3600197
theorem B6400349 : Blo 1895435 6400349 := bstep (se 3 (by rfl) ⟨1200065, by rfl⟩ : syracuseStep 6400349 = 2400131) B2400131
theorem B4266899 : Blo 1895435 4266899 := bstep (se 1 (by rfl) ⟨3200174, by rfl⟩ : syracuseStep 4266899 = 6400349) B6400349
theorem B2844599 : Blo 1895435 2844599 := bstep (se 1 (by rfl) ⟨2133449, by rfl⟩ : syracuseStep 2844599 = 4266899) B4266899
theorem B1896399 : Blo 1895435 1896399 := bstep (se 1 (by rfl) ⟨1422299, by rfl⟩ : syracuseStep 1896399 = 2844599) B2844599
theorem B2844605 : Blo 1895435 2844605 := bbase (se 3 (by rfl) ⟨533363, by rfl⟩ : syracuseStep 2844605 = 1066727) (by norm_num)
theorem B1896403 : Blo 1895435 1896403 := bstep (se 1 (by rfl) ⟨1422302, by rfl⟩ : syracuseStep 1896403 = 2844605) B2844605
theorem B4266917 : Blo 1895435 4266917 := bbase (se 4 (by rfl) ⟨400023, by rfl⟩ : syracuseStep 4266917 = 800047) (by norm_num)
theorem B2844611 : Blo 1895435 2844611 := bstep (se 1 (by rfl) ⟨2133458, by rfl⟩ : syracuseStep 2844611 = 4266917) B4266917
theorem B1896407 : Blo 1895435 1896407 := bstep (se 1 (by rfl) ⟨1422305, by rfl⟩ : syracuseStep 1896407 = 2844611) B2844611
theorem B4800293 : Blo 1895435 4800293 := bbase (se 4 (by rfl) ⟨450027, by rfl⟩ : syracuseStep 4800293 = 900055) (by norm_num)
theorem B3200195 : Blo 1895435 3200195 := bstep (se 1 (by rfl) ⟨2400146, by rfl⟩ : syracuseStep 3200195 = 4800293) B4800293
theorem B2133463 : Blo 1895435 2133463 := bstep (se 1 (by rfl) ⟨1600097, by rfl⟩ : syracuseStep 2133463 = 3200195) B3200195
theorem B2844617 : Blo 1895435 2844617 := bstep (se 2 (by rfl) ⟨1066731, by rfl⟩ : syracuseStep 2844617 = 2133463) B2133463
theorem B1896411 : Blo 1895435 1896411 := bstep (se 1 (by rfl) ⟨1422308, by rfl⟩ : syracuseStep 1896411 = 2844617) B2844617
theorem B5400341 : Blo 1895435 5400341 := bbase (se 6 (by rfl) ⟨126570, by rfl⟩ : syracuseStep 5400341 = 253141) (by norm_num)
theorem B3600227 : Blo 1895435 3600227 := bstep (se 1 (by rfl) ⟨2700170, by rfl⟩ : syracuseStep 3600227 = 5400341) B5400341
theorem B9600605 : Blo 1895435 9600605 := bstep (se 3 (by rfl) ⟨1800113, by rfl⟩ : syracuseStep 9600605 = 3600227) B3600227
theorem B6400403 : Blo 1895435 6400403 := bstep (se 1 (by rfl) ⟨4800302, by rfl⟩ : syracuseStep 6400403 = 9600605) B9600605
theorem B4266935 : Blo 1895435 4266935 := bstep (se 1 (by rfl) ⟨3200201, by rfl⟩ : syracuseStep 4266935 = 6400403) B6400403
theorem B2844623 : Blo 1895435 2844623 := bstep (se 1 (by rfl) ⟨2133467, by rfl⟩ : syracuseStep 2844623 = 4266935) B4266935
theorem B1896415 : Blo 1895435 1896415 := bstep (se 1 (by rfl) ⟨1422311, by rfl⟩ : syracuseStep 1896415 = 2844623) B2844623
theorem B2844629 : Blo 1895435 2844629 := bbase (se 7 (by rfl) ⟨33335, by rfl⟩ : syracuseStep 2844629 = 66671) (by norm_num)
theorem B1896419 : Blo 1895435 1896419 := bstep (se 1 (by rfl) ⟨1422314, by rfl⟩ : syracuseStep 1896419 = 2844629) B2844629
theorem B7200485 : Blo 1895435 7200485 := bbase (se 4 (by rfl) ⟨675045, by rfl⟩ : syracuseStep 7200485 = 1350091) (by norm_num)
theorem B4800323 : Blo 1895435 4800323 := bstep (se 1 (by rfl) ⟨3600242, by rfl⟩ : syracuseStep 4800323 = 7200485) B7200485
theorem B3200215 : Blo 1895435 3200215 := bstep (se 1 (by rfl) ⟨2400161, by rfl⟩ : syracuseStep 3200215 = 4800323) B4800323
theorem B4266953 : Blo 1895435 4266953 := bstep (se 2 (by rfl) ⟨1600107, by rfl⟩ : syracuseStep 4266953 = 3200215) B3200215
theorem B2844635 : Blo 1895435 2844635 := bstep (se 1 (by rfl) ⟨2133476, by rfl⟩ : syracuseStep 2844635 = 4266953) B4266953
theorem B1896423 : Blo 1895435 1896423 := bstep (se 1 (by rfl) ⟨1422317, by rfl⟩ : syracuseStep 1896423 = 2844635) B2844635
theorem B2133481 : Blo 1895435 2133481 := bbase (se 2 (by rfl) ⟨800055, by rfl⟩ : syracuseStep 2133481 = 1600111) (by norm_num)
theorem B2844641 : Blo 1895435 2844641 := bstep (se 2 (by rfl) ⟨1066740, by rfl⟩ : syracuseStep 2844641 = 2133481) B2133481
theorem B1896427 : Blo 1895435 1896427 := bstep (se 1 (by rfl) ⟨1422320, by rfl⟩ : syracuseStep 1896427 = 2844641) B2844641
theorem B2025145 : Blo 1895435 2025145 := bbase (se 2 (by rfl) ⟨759429, by rfl⟩ : syracuseStep 2025145 = 1518859) (by norm_num)
theorem B10800773 : Blo 1895435 10800773 := bstep (se 4 (by rfl) ⟨1012572, by rfl⟩ : syracuseStep 10800773 = 2025145) B2025145
theorem B7200515 : Blo 1895435 7200515 := bstep (se 1 (by rfl) ⟨5400386, by rfl⟩ : syracuseStep 7200515 = 10800773) B10800773
theorem B4800343 : Blo 1895435 4800343 := bstep (se 1 (by rfl) ⟨3600257, by rfl⟩ : syracuseStep 4800343 = 7200515) B7200515
theorem B6400457 : Blo 1895435 6400457 := bstep (se 2 (by rfl) ⟨2400171, by rfl⟩ : syracuseStep 6400457 = 4800343) B4800343
theorem B4266971 : Blo 1895435 4266971 := bstep (se 1 (by rfl) ⟨3200228, by rfl⟩ : syracuseStep 4266971 = 6400457) B6400457
theorem B2844647 : Blo 1895435 2844647 := bstep (se 1 (by rfl) ⟨2133485, by rfl⟩ : syracuseStep 2844647 = 4266971) B4266971
theorem B1896431 : Blo 1895435 1896431 := bstep (se 1 (by rfl) ⟨1422323, by rfl⟩ : syracuseStep 1896431 = 2844647) B2844647
theorem B2844653 : Blo 1895435 2844653 := bbase (se 3 (by rfl) ⟨533372, by rfl⟩ : syracuseStep 2844653 = 1066745) (by norm_num)
theorem B1896435 : Blo 1895435 1896435 := bstep (se 1 (by rfl) ⟨1422326, by rfl⟩ : syracuseStep 1896435 = 2844653) B2844653
theorem B4266989 : Blo 1895435 4266989 := bbase (se 3 (by rfl) ⟨800060, by rfl⟩ : syracuseStep 4266989 = 1600121) (by norm_num)
theorem B2844659 : Blo 1895435 2844659 := bstep (se 1 (by rfl) ⟨2133494, by rfl⟩ : syracuseStep 2844659 = 4266989) B4266989
theorem B1896439 : Blo 1895435 1896439 := bstep (se 1 (by rfl) ⟨1422329, by rfl⟩ : syracuseStep 1896439 = 2844659) B2844659
theorem B4050317 : Blo 1895435 4050317 := bbase (se 3 (by rfl) ⟨759434, by rfl⟩ : syracuseStep 4050317 = 1518869) (by norm_num)
theorem B2700211 : Blo 1895435 2700211 := bstep (se 1 (by rfl) ⟨2025158, by rfl⟩ : syracuseStep 2700211 = 4050317) B4050317
theorem B3600281 : Blo 1895435 3600281 := bstep (se 2 (by rfl) ⟨1350105, by rfl⟩ : syracuseStep 3600281 = 2700211) B2700211
theorem B2400187 : Blo 1895435 2400187 := bstep (se 1 (by rfl) ⟨1800140, by rfl⟩ : syracuseStep 2400187 = 3600281) B3600281
theorem B3200249 : Blo 1895435 3200249 := bstep (se 2 (by rfl) ⟨1200093, by rfl⟩ : syracuseStep 3200249 = 2400187) B2400187
theorem B2133499 : Blo 1895435 2133499 := bstep (se 1 (by rfl) ⟨1600124, by rfl⟩ : syracuseStep 2133499 = 3200249) B3200249
theorem B2844665 : Blo 1895435 2844665 := bstep (se 2 (by rfl) ⟨1066749, by rfl⟩ : syracuseStep 2844665 = 2133499) B2133499
theorem B1896443 : Blo 1895435 1896443 := bstep (se 1 (by rfl) ⟨1422332, by rfl⟩ : syracuseStep 1896443 = 2844665) B2844665
theorem B8436757 : Blo 1895435 8436757 := bbase (se 6 (by rfl) ⟨197736, by rfl⟩ : syracuseStep 8436757 = 395473) (by norm_num)
theorem B11249009 : Blo 1895435 11249009 := bstep (se 2 (by rfl) ⟨4218378, by rfl⟩ : syracuseStep 11249009 = 8436757) B8436757
theorem B7499339 : Blo 1895435 7499339 := bstep (se 1 (by rfl) ⟨5624504, by rfl⟩ : syracuseStep 7499339 = 11249009) B11249009
theorem B4999559 : Blo 1895435 4999559 := bstep (se 1 (by rfl) ⟨3749669, by rfl⟩ : syracuseStep 4999559 = 7499339) B7499339
theorem B13332157 : Blo 1895435 13332157 := bstep (se 3 (by rfl) ⟨2499779, by rfl⟩ : syracuseStep 13332157 = 4999559) B4999559
theorem B71104837 : Blo 1895435 71104837 := bstep (se 4 (by rfl) ⟨6666078, by rfl⟩ : syracuseStep 71104837 = 13332157) B13332157
theorem B94806449 : Blo 1895435 94806449 := bstep (se 2 (by rfl) ⟨35552418, by rfl⟩ : syracuseStep 94806449 = 71104837) B71104837
theorem B63204299 : Blo 1895435 63204299 := bstep (se 1 (by rfl) ⟨47403224, by rfl⟩ : syracuseStep 63204299 = 94806449) B94806449
theorem B42136199 : Blo 1895435 42136199 := bstep (se 1 (by rfl) ⟨31602149, by rfl⟩ : syracuseStep 42136199 = 63204299) B63204299
theorem B28090799 : Blo 1895435 28090799 := bstep (se 1 (by rfl) ⟨21068099, by rfl⟩ : syracuseStep 28090799 = 42136199) B42136199
theorem B18727199 : Blo 1895435 18727199 := bstep (se 1 (by rfl) ⟨14045399, by rfl⟩ : syracuseStep 18727199 = 28090799) B28090799
theorem B12484799 : Blo 1895435 12484799 := bstep (se 1 (by rfl) ⟨9363599, by rfl⟩ : syracuseStep 12484799 = 18727199) B18727199
theorem B8323199 : Blo 1895435 8323199 := bstep (se 1 (by rfl) ⟨6242399, by rfl⟩ : syracuseStep 8323199 = 12484799) B12484799
theorem B5548799 : Blo 1895435 5548799 := bstep (se 1 (by rfl) ⟨4161599, by rfl⟩ : syracuseStep 5548799 = 8323199) B8323199
theorem B3699199 : Blo 1895435 3699199 := bstep (se 1 (by rfl) ⟨2774399, by rfl⟩ : syracuseStep 3699199 = 5548799) B5548799
theorem B4932265 : Blo 1895435 4932265 := bstep (se 2 (by rfl) ⟨1849599, by rfl⟩ : syracuseStep 4932265 = 3699199) B3699199
theorem B6576353 : Blo 1895435 6576353 := bstep (se 2 (by rfl) ⟨2466132, by rfl⟩ : syracuseStep 6576353 = 4932265) B4932265
theorem B4384235 : Blo 1895435 4384235 := bstep (se 1 (by rfl) ⟨3288176, by rfl⟩ : syracuseStep 4384235 = 6576353) B6576353
theorem B2922823 : Blo 1895435 2922823 := bstep (se 1 (by rfl) ⟨2192117, by rfl⟩ : syracuseStep 2922823 = 4384235) B4384235
theorem B15588389 : Blo 1895435 15588389 := bstep (se 4 (by rfl) ⟨1461411, by rfl⟩ : syracuseStep 15588389 = 2922823) B2922823
theorem B41569037 : Blo 1895435 41569037 := bstep (se 3 (by rfl) ⟨7794194, by rfl⟩ : syracuseStep 41569037 = 15588389) B15588389
theorem B27712691 : Blo 1895435 27712691 := bstep (se 1 (by rfl) ⟨20784518, by rfl⟩ : syracuseStep 27712691 = 41569037) B41569037
theorem B18475127 : Blo 1895435 18475127 := bstep (se 1 (by rfl) ⟨13856345, by rfl⟩ : syracuseStep 18475127 = 27712691) B27712691
theorem B12316751 : Blo 1895435 12316751 := bstep (se 1 (by rfl) ⟨9237563, by rfl⟩ : syracuseStep 12316751 = 18475127) B18475127
theorem B525514709 : Blo 1895435 525514709 := bstep (se 7 (by rfl) ⟨6158375, by rfl⟩ : syracuseStep 525514709 = 12316751) B12316751
theorem B350343139 : Blo 1895435 350343139 := bstep (se 1 (by rfl) ⟨262757354, by rfl⟩ : syracuseStep 350343139 = 525514709) B525514709
theorem B467124185 : Blo 1895435 467124185 := bstep (se 2 (by rfl) ⟨175171569, by rfl⟩ : syracuseStep 467124185 = 350343139) B350343139
theorem B311416123 : Blo 1895435 311416123 := bstep (se 1 (by rfl) ⟨233562092, by rfl⟩ : syracuseStep 311416123 = 467124185) B467124185
theorem B415221497 : Blo 1895435 415221497 := bstep (se 2 (by rfl) ⟨155708061, by rfl⟩ : syracuseStep 415221497 = 311416123) B311416123
theorem B276814331 : Blo 1895435 276814331 := bstep (se 1 (by rfl) ⟨207610748, by rfl⟩ : syracuseStep 276814331 = 415221497) B415221497
theorem B184542887 : Blo 1895435 184542887 := bstep (se 1 (by rfl) ⟨138407165, by rfl⟩ : syracuseStep 184542887 = 276814331) B276814331
theorem B123028591 : Blo 1895435 123028591 := bstep (se 1 (by rfl) ⟨92271443, by rfl⟩ : syracuseStep 123028591 = 184542887) B184542887
theorem B164038121 : Blo 1895435 164038121 := bstep (se 2 (by rfl) ⟨61514295, by rfl⟩ : syracuseStep 164038121 = 123028591) B123028591
theorem B109358747 : Blo 1895435 109358747 := bstep (se 1 (by rfl) ⟨82019060, by rfl⟩ : syracuseStep 109358747 = 164038121) B164038121
theorem B72905831 : Blo 1895435 72905831 := bstep (se 1 (by rfl) ⟨54679373, by rfl⟩ : syracuseStep 72905831 = 109358747) B109358747
theorem B48603887 : Blo 1895435 48603887 := bstep (se 1 (by rfl) ⟨36452915, by rfl⟩ : syracuseStep 48603887 = 72905831) B72905831
theorem B32402591 : Blo 1895435 32402591 := bstep (se 1 (by rfl) ⟨24301943, by rfl⟩ : syracuseStep 32402591 = 48603887) B48603887
theorem B21601727 : Blo 1895435 21601727 := bstep (se 1 (by rfl) ⟨16201295, by rfl⟩ : syracuseStep 21601727 = 32402591) B32402591
theorem B14401151 : Blo 1895435 14401151 := bstep (se 1 (by rfl) ⟨10800863, by rfl⟩ : syracuseStep 14401151 = 21601727) B21601727
theorem B9600767 : Blo 1895435 9600767 := bstep (se 1 (by rfl) ⟨7200575, by rfl⟩ : syracuseStep 9600767 = 14401151) B14401151
theorem B6400511 : Blo 1895435 6400511 := bstep (se 1 (by rfl) ⟨4800383, by rfl⟩ : syracuseStep 6400511 = 9600767) B9600767
theorem B4267007 : Blo 1895435 4267007 := bstep (se 1 (by rfl) ⟨3200255, by rfl⟩ : syracuseStep 4267007 = 6400511) B6400511
theorem B2844671 : Blo 1895435 2844671 := bstep (se 1 (by rfl) ⟨2133503, by rfl⟩ : syracuseStep 2844671 = 4267007) B4267007
theorem B1896447 : Blo 1895435 1896447 := bstep (se 1 (by rfl) ⟨1422335, by rfl⟩ : syracuseStep 1896447 = 2844671) B2844671
theorem B2844677 : Blo 1895435 2844677 := bbase (se 4 (by rfl) ⟨266688, by rfl⟩ : syracuseStep 2844677 = 533377) (by norm_num)
theorem B1896451 : Blo 1895435 1896451 := bstep (se 1 (by rfl) ⟨1422338, by rfl⟩ : syracuseStep 1896451 = 2844677) B2844677
theorem B3200269 : Blo 1895435 3200269 := bbase (se 3 (by rfl) ⟨600050, by rfl⟩ : syracuseStep 3200269 = 1200101) (by norm_num)
theorem B4267025 : Blo 1895435 4267025 := bstep (se 2 (by rfl) ⟨1600134, by rfl⟩ : syracuseStep 4267025 = 3200269) B3200269
theorem B2844683 : Blo 1895435 2844683 := bstep (se 1 (by rfl) ⟨2133512, by rfl⟩ : syracuseStep 2844683 = 4267025) B4267025
theorem B1896455 : Blo 1895435 1896455 := bstep (se 1 (by rfl) ⟨1422341, by rfl⟩ : syracuseStep 1896455 = 2844683) B2844683
theorem B2133517 : Blo 1895435 2133517 := bbase (se 3 (by rfl) ⟨400034, by rfl⟩ : syracuseStep 2133517 = 800069) (by norm_num)
theorem B2844689 : Blo 1895435 2844689 := bstep (se 2 (by rfl) ⟨1066758, by rfl⟩ : syracuseStep 2844689 = 2133517) B2133517
theorem B1896459 : Blo 1895435 1896459 := bstep (se 1 (by rfl) ⟨1422344, by rfl⟩ : syracuseStep 1896459 = 2844689) B2844689
theorem B6400565 : Blo 1895435 6400565 := bbase (se 5 (by rfl) ⟨300026, by rfl⟩ : syracuseStep 6400565 = 600053) (by norm_num)
theorem B4267043 : Blo 1895435 4267043 := bstep (se 1 (by rfl) ⟨3200282, by rfl⟩ : syracuseStep 4267043 = 6400565) B6400565
theorem B2844695 : Blo 1895435 2844695 := bstep (se 1 (by rfl) ⟨2133521, by rfl⟩ : syracuseStep 2844695 = 4267043) B4267043
theorem B1896463 : Blo 1895435 1896463 := bstep (se 1 (by rfl) ⟨1422347, by rfl⟩ : syracuseStep 1896463 = 2844695) B2844695
theorem B2844701 : Blo 1895435 2844701 := bbase (se 3 (by rfl) ⟨533381, by rfl⟩ : syracuseStep 2844701 = 1066763) (by norm_num)
theorem B1896467 : Blo 1895435 1896467 := bstep (se 1 (by rfl) ⟨1422350, by rfl⟩ : syracuseStep 1896467 = 2844701) B2844701
theorem B4267061 : Blo 1895435 4267061 := bbase (se 5 (by rfl) ⟨200018, by rfl⟩ : syracuseStep 4267061 = 400037) (by norm_num)
theorem B2844707 : Blo 1895435 2844707 := bstep (se 1 (by rfl) ⟨2133530, by rfl⟩ : syracuseStep 2844707 = 4267061) B4267061
theorem B1896471 : Blo 1895435 1896471 := bstep (se 1 (by rfl) ⟨1422353, by rfl⟩ : syracuseStep 1896471 = 2844707) B2844707
theorem B3079237 : Blo 1895435 3079237 := bbase (se 4 (by rfl) ⟨288678, by rfl⟩ : syracuseStep 3079237 = 577357) (by norm_num)
theorem B4105649 : Blo 1895435 4105649 := bstep (se 2 (by rfl) ⟨1539618, by rfl⟩ : syracuseStep 4105649 = 3079237) B3079237
theorem B2737099 : Blo 1895435 2737099 := bstep (se 1 (by rfl) ⟨2052824, by rfl⟩ : syracuseStep 2737099 = 4105649) B4105649
theorem B3649465 : Blo 1895435 3649465 := bstep (se 2 (by rfl) ⟨1368549, by rfl⟩ : syracuseStep 3649465 = 2737099) B2737099
theorem B4865953 : Blo 1895435 4865953 := bstep (se 2 (by rfl) ⟨1824732, by rfl⟩ : syracuseStep 4865953 = 3649465) B3649465
theorem B6487937 : Blo 1895435 6487937 := bstep (se 2 (by rfl) ⟨2432976, by rfl⟩ : syracuseStep 6487937 = 4865953) B4865953
theorem B4325291 : Blo 1895435 4325291 := bstep (se 1 (by rfl) ⟨3243968, by rfl⟩ : syracuseStep 4325291 = 6487937) B6487937
theorem B2883527 : Blo 1895435 2883527 := bstep (se 1 (by rfl) ⟨2162645, by rfl⟩ : syracuseStep 2883527 = 4325291) B4325291
theorem B1922351 : Blo 1895435 1922351 := bstep (se 1 (by rfl) ⟨1441763, by rfl⟩ : syracuseStep 1922351 = 2883527) B2883527
theorem B5126269 : Blo 1895435 5126269 := bstep (se 3 (by rfl) ⟨961175, by rfl⟩ : syracuseStep 5126269 = 1922351) B1922351
theorem B6835025 : Blo 1895435 6835025 := bstep (se 2 (by rfl) ⟨2563134, by rfl⟩ : syracuseStep 6835025 = 5126269) B5126269
theorem B4556683 : Blo 1895435 4556683 := bstep (se 1 (by rfl) ⟨3417512, by rfl⟩ : syracuseStep 4556683 = 6835025) B6835025
theorem B6075577 : Blo 1895435 6075577 := bstep (se 2 (by rfl) ⟨2278341, by rfl⟩ : syracuseStep 6075577 = 4556683) B4556683
theorem B8100769 : Blo 1895435 8100769 := bstep (se 2 (by rfl) ⟨3037788, by rfl⟩ : syracuseStep 8100769 = 6075577) B6075577
theorem B10801025 : Blo 1895435 10801025 := bstep (se 2 (by rfl) ⟨4050384, by rfl⟩ : syracuseStep 10801025 = 8100769) B8100769
theorem B7200683 : Blo 1895435 7200683 := bstep (se 1 (by rfl) ⟨5400512, by rfl⟩ : syracuseStep 7200683 = 10801025) B10801025
theorem B4800455 : Blo 1895435 4800455 := bstep (se 1 (by rfl) ⟨3600341, by rfl⟩ : syracuseStep 4800455 = 7200683) B7200683
theorem B3200303 : Blo 1895435 3200303 := bstep (se 1 (by rfl) ⟨2400227, by rfl⟩ : syracuseStep 3200303 = 4800455) B4800455
theorem B2133535 : Blo 1895435 2133535 := bstep (se 1 (by rfl) ⟨1600151, by rfl⟩ : syracuseStep 2133535 = 3200303) B3200303
theorem B2844713 : Blo 1895435 2844713 := bstep (se 2 (by rfl) ⟨1066767, by rfl⟩ : syracuseStep 2844713 = 2133535) B2133535
theorem B1896475 : Blo 1895435 1896475 := bstep (se 1 (by rfl) ⟨1422356, by rfl⟩ : syracuseStep 1896475 = 2844713) B2844713
theorem B6075589 : Blo 1895435 6075589 := bbase (se 4 (by rfl) ⟨569586, by rfl⟩ : syracuseStep 6075589 = 1139173) (by norm_num)
theorem B8100785 : Blo 1895435 8100785 := bstep (se 2 (by rfl) ⟨3037794, by rfl⟩ : syracuseStep 8100785 = 6075589) B6075589
theorem B5400523 : Blo 1895435 5400523 := bstep (se 1 (by rfl) ⟨4050392, by rfl⟩ : syracuseStep 5400523 = 8100785) B8100785
theorem B7200697 : Blo 1895435 7200697 := bstep (se 2 (by rfl) ⟨2700261, by rfl⟩ : syracuseStep 7200697 = 5400523) B5400523
theorem B9600929 : Blo 1895435 9600929 := bstep (se 2 (by rfl) ⟨3600348, by rfl⟩ : syracuseStep 9600929 = 7200697) B7200697
theorem B6400619 : Blo 1895435 6400619 := bstep (se 1 (by rfl) ⟨4800464, by rfl⟩ : syracuseStep 6400619 = 9600929) B9600929
theorem B4267079 : Blo 1895435 4267079 := bstep (se 1 (by rfl) ⟨3200309, by rfl⟩ : syracuseStep 4267079 = 6400619) B6400619
theorem B2844719 : Blo 1895435 2844719 := bstep (se 1 (by rfl) ⟨2133539, by rfl⟩ : syracuseStep 2844719 = 4267079) B4267079
theorem B1896479 : Blo 1895435 1896479 := bstep (se 1 (by rfl) ⟨1422359, by rfl⟩ : syracuseStep 1896479 = 2844719) B2844719
theorem B2844725 : Blo 1895435 2844725 := bbase (se 5 (by rfl) ⟨133346, by rfl⟩ : syracuseStep 2844725 = 266693) (by norm_num)
theorem B1896483 : Blo 1895435 1896483 := bstep (se 1 (by rfl) ⟨1422362, by rfl⟩ : syracuseStep 1896483 = 2844725) B2844725
theorem B4800485 : Blo 1895435 4800485 := bbase (se 4 (by rfl) ⟨450045, by rfl⟩ : syracuseStep 4800485 = 900091) (by norm_num)
theorem B3200323 : Blo 1895435 3200323 := bstep (se 1 (by rfl) ⟨2400242, by rfl⟩ : syracuseStep 3200323 = 4800485) B4800485
theorem B4267097 : Blo 1895435 4267097 := bstep (se 2 (by rfl) ⟨1600161, by rfl⟩ : syracuseStep 4267097 = 3200323) B3200323
theorem B2844731 : Blo 1895435 2844731 := bstep (se 1 (by rfl) ⟨2133548, by rfl⟩ : syracuseStep 2844731 = 4267097) B4267097
theorem B1896487 : Blo 1895435 1896487 := bstep (se 1 (by rfl) ⟨1422365, by rfl⟩ : syracuseStep 1896487 = 2844731) B2844731
theorem B2133553 : Blo 1895435 2133553 := bbase (se 2 (by rfl) ⟨800082, by rfl⟩ : syracuseStep 2133553 = 1600165) (by norm_num)
theorem B2844737 : Blo 1895435 2844737 := bstep (se 2 (by rfl) ⟨1066776, by rfl⟩ : syracuseStep 2844737 = 2133553) B2133553
theorem B1896491 : Blo 1895435 1896491 := bstep (se 1 (by rfl) ⟨1422368, by rfl⟩ : syracuseStep 1896491 = 2844737) B2844737
theorem B2883557 : Blo 1895435 2883557 := bbase (se 4 (by rfl) ⟨270333, by rfl⟩ : syracuseStep 2883557 = 540667) (by norm_num)
theorem B7689485 : Blo 1895435 7689485 := bstep (se 3 (by rfl) ⟨1441778, by rfl⟩ : syracuseStep 7689485 = 2883557) B2883557
theorem B5126323 : Blo 1895435 5126323 := bstep (se 1 (by rfl) ⟨3844742, by rfl⟩ : syracuseStep 5126323 = 7689485) B7689485
theorem B6835097 : Blo 1895435 6835097 := bstep (se 2 (by rfl) ⟨2563161, by rfl⟩ : syracuseStep 6835097 = 5126323) B5126323
theorem B4556731 : Blo 1895435 4556731 := bstep (se 1 (by rfl) ⟨3417548, by rfl⟩ : syracuseStep 4556731 = 6835097) B6835097
theorem B6075641 : Blo 1895435 6075641 := bstep (se 2 (by rfl) ⟨2278365, by rfl⟩ : syracuseStep 6075641 = 4556731) B4556731
theorem B4050427 : Blo 1895435 4050427 := bstep (se 1 (by rfl) ⟨3037820, by rfl⟩ : syracuseStep 4050427 = 6075641) B6075641
theorem B5400569 : Blo 1895435 5400569 := bstep (se 2 (by rfl) ⟨2025213, by rfl⟩ : syracuseStep 5400569 = 4050427) B4050427
theorem B3600379 : Blo 1895435 3600379 := bstep (se 1 (by rfl) ⟨2700284, by rfl⟩ : syracuseStep 3600379 = 5400569) B5400569
theorem B4800505 : Blo 1895435 4800505 := bstep (se 2 (by rfl) ⟨1800189, by rfl⟩ : syracuseStep 4800505 = 3600379) B3600379
theorem B6400673 : Blo 1895435 6400673 := bstep (se 2 (by rfl) ⟨2400252, by rfl⟩ : syracuseStep 6400673 = 4800505) B4800505
theorem B4267115 : Blo 1895435 4267115 := bstep (se 1 (by rfl) ⟨3200336, by rfl⟩ : syracuseStep 4267115 = 6400673) B6400673
theorem B2844743 : Blo 1895435 2844743 := bstep (se 1 (by rfl) ⟨2133557, by rfl⟩ : syracuseStep 2844743 = 4267115) B4267115
theorem B1896495 : Blo 1895435 1896495 := bstep (se 1 (by rfl) ⟨1422371, by rfl⟩ : syracuseStep 1896495 = 2844743) B2844743
theorem B2844749 : Blo 1895435 2844749 := bbase (se 3 (by rfl) ⟨533390, by rfl⟩ : syracuseStep 2844749 = 1066781) (by norm_num)
theorem B1896499 : Blo 1895435 1896499 := bstep (se 1 (by rfl) ⟨1422374, by rfl⟩ : syracuseStep 1896499 = 2844749) B2844749
theorem B4267133 : Blo 1895435 4267133 := bbase (se 3 (by rfl) ⟨800087, by rfl⟩ : syracuseStep 4267133 = 1600175) (by norm_num)
theorem B2844755 : Blo 1895435 2844755 := bstep (se 1 (by rfl) ⟨2133566, by rfl⟩ : syracuseStep 2844755 = 4267133) B4267133
theorem B1896503 : Blo 1895435 1896503 := bstep (se 1 (by rfl) ⟨1422377, by rfl⟩ : syracuseStep 1896503 = 2844755) B2844755
theorem B3200357 : Blo 1895435 3200357 := bbase (se 4 (by rfl) ⟨300033, by rfl⟩ : syracuseStep 3200357 = 600067) (by norm_num)
theorem B2133571 : Blo 1895435 2133571 := bstep (se 1 (by rfl) ⟨1600178, by rfl⟩ : syracuseStep 2133571 = 3200357) B3200357
theorem B2844761 : Blo 1895435 2844761 := bstep (se 2 (by rfl) ⟨1066785, by rfl⟩ : syracuseStep 2844761 = 2133571) B2133571
theorem B1896507 : Blo 1895435 1896507 := bstep (se 1 (by rfl) ⟨1422380, by rfl⟩ : syracuseStep 1896507 = 2844761) B2844761
theorem B4050461 : Blo 1895435 4050461 := bbase (se 3 (by rfl) ⟨759461, by rfl⟩ : syracuseStep 4050461 = 1518923) (by norm_num)
theorem B2700307 : Blo 1895435 2700307 := bstep (se 1 (by rfl) ⟨2025230, by rfl⟩ : syracuseStep 2700307 = 4050461) B4050461
theorem B14401637 : Blo 1895435 14401637 := bstep (se 4 (by rfl) ⟨1350153, by rfl⟩ : syracuseStep 14401637 = 2700307) B2700307
theorem B9601091 : Blo 1895435 9601091 := bstep (se 1 (by rfl) ⟨7200818, by rfl⟩ : syracuseStep 9601091 = 14401637) B14401637
theorem B6400727 : Blo 1895435 6400727 := bstep (se 1 (by rfl) ⟨4800545, by rfl⟩ : syracuseStep 6400727 = 9601091) B9601091
theorem B4267151 : Blo 1895435 4267151 := bstep (se 1 (by rfl) ⟨3200363, by rfl⟩ : syracuseStep 4267151 = 6400727) B6400727
theorem B2844767 : Blo 1895435 2844767 := bstep (se 1 (by rfl) ⟨2133575, by rfl⟩ : syracuseStep 2844767 = 4267151) B4267151
theorem B1896511 : Blo 1895435 1896511 := bstep (se 1 (by rfl) ⟨1422383, by rfl⟩ : syracuseStep 1896511 = 2844767) B2844767
theorem B2844773 : Blo 1895435 2844773 := bbase (se 4 (by rfl) ⟨266697, by rfl⟩ : syracuseStep 2844773 = 533395) (by norm_num)
theorem B1896515 : Blo 1895435 1896515 := bstep (se 1 (by rfl) ⟨1422386, by rfl⟩ : syracuseStep 1896515 = 2844773) B2844773
theorem B3464221 : Blo 1895435 3464221 := bbase (se 3 (by rfl) ⟨649541, by rfl⟩ : syracuseStep 3464221 = 1299083) (by norm_num)
theorem B4618961 : Blo 1895435 4618961 := bstep (se 2 (by rfl) ⟨1732110, by rfl⟩ : syracuseStep 4618961 = 3464221) B3464221
theorem B3079307 : Blo 1895435 3079307 := bstep (se 1 (by rfl) ⟨2309480, by rfl⟩ : syracuseStep 3079307 = 4618961) B4618961
theorem B8211485 : Blo 1895435 8211485 := bstep (se 3 (by rfl) ⟨1539653, by rfl⟩ : syracuseStep 8211485 = 3079307) B3079307
theorem B5474323 : Blo 1895435 5474323 := bstep (se 1 (by rfl) ⟨4105742, by rfl⟩ : syracuseStep 5474323 = 8211485) B8211485
theorem B29196389 : Blo 1895435 29196389 := bstep (se 4 (by rfl) ⟨2737161, by rfl⟩ : syracuseStep 29196389 = 5474323) B5474323
theorem B19464259 : Blo 1895435 19464259 := bstep (se 1 (by rfl) ⟨14598194, by rfl⟩ : syracuseStep 19464259 = 29196389) B29196389
theorem B25952345 : Blo 1895435 25952345 := bstep (se 2 (by rfl) ⟨9732129, by rfl⟩ : syracuseStep 25952345 = 19464259) B19464259
theorem B17301563 : Blo 1895435 17301563 := bstep (se 1 (by rfl) ⟨12976172, by rfl⟩ : syracuseStep 17301563 = 25952345) B25952345
theorem B11534375 : Blo 1895435 11534375 := bstep (se 1 (by rfl) ⟨8650781, by rfl⟩ : syracuseStep 11534375 = 17301563) B17301563
theorem B7689583 : Blo 1895435 7689583 := bstep (se 1 (by rfl) ⟨5767187, by rfl⟩ : syracuseStep 7689583 = 11534375) B11534375
theorem B10252777 : Blo 1895435 10252777 := bstep (se 2 (by rfl) ⟨3844791, by rfl⟩ : syracuseStep 10252777 = 7689583) B7689583
theorem B13670369 : Blo 1895435 13670369 := bstep (se 2 (by rfl) ⟨5126388, by rfl⟩ : syracuseStep 13670369 = 10252777) B10252777
theorem B9113579 : Blo 1895435 9113579 := bstep (se 1 (by rfl) ⟨6835184, by rfl⟩ : syracuseStep 9113579 = 13670369) B13670369
theorem B6075719 : Blo 1895435 6075719 := bstep (se 1 (by rfl) ⟨4556789, by rfl⟩ : syracuseStep 6075719 = 9113579) B9113579
theorem B4050479 : Blo 1895435 4050479 := bstep (se 1 (by rfl) ⟨3037859, by rfl⟩ : syracuseStep 4050479 = 6075719) B6075719
theorem B2700319 : Blo 1895435 2700319 := bstep (se 1 (by rfl) ⟨2025239, by rfl⟩ : syracuseStep 2700319 = 4050479) B4050479
theorem B3600425 : Blo 1895435 3600425 := bstep (se 2 (by rfl) ⟨1350159, by rfl⟩ : syracuseStep 3600425 = 2700319) B2700319
theorem B2400283 : Blo 1895435 2400283 := bstep (se 1 (by rfl) ⟨1800212, by rfl⟩ : syracuseStep 2400283 = 3600425) B3600425
theorem B3200377 : Blo 1895435 3200377 := bstep (se 2 (by rfl) ⟨1200141, by rfl⟩ : syracuseStep 3200377 = 2400283) B2400283
theorem B4267169 : Blo 1895435 4267169 := bstep (se 2 (by rfl) ⟨1600188, by rfl⟩ : syracuseStep 4267169 = 3200377) B3200377
theorem B2844779 : Blo 1895435 2844779 := bstep (se 1 (by rfl) ⟨2133584, by rfl⟩ : syracuseStep 2844779 = 4267169) B4267169
theorem B1896519 : Blo 1895435 1896519 := bstep (se 1 (by rfl) ⟨1422389, by rfl⟩ : syracuseStep 1896519 = 2844779) B2844779
theorem B2133589 : Blo 1895435 2133589 := bbase (se 8 (by rfl) ⟨12501, by rfl⟩ : syracuseStep 2133589 = 25003) (by norm_num)
theorem B2844785 : Blo 1895435 2844785 := bstep (se 2 (by rfl) ⟨1066794, by rfl⟩ : syracuseStep 2844785 = 2133589) B2133589
theorem B1896523 : Blo 1895435 1896523 := bstep (se 1 (by rfl) ⟨1422392, by rfl⟩ : syracuseStep 1896523 = 2844785) B2844785
theorem B2400293 : Blo 1895435 2400293 := bbase (se 4 (by rfl) ⟨225027, by rfl⟩ : syracuseStep 2400293 = 450055) (by norm_num)
theorem B6400781 : Blo 1895435 6400781 := bstep (se 3 (by rfl) ⟨1200146, by rfl⟩ : syracuseStep 6400781 = 2400293) B2400293
theorem B4267187 : Blo 1895435 4267187 := bstep (se 1 (by rfl) ⟨3200390, by rfl⟩ : syracuseStep 4267187 = 6400781) B6400781
theorem B2844791 : Blo 1895435 2844791 := bstep (se 1 (by rfl) ⟨2133593, by rfl⟩ : syracuseStep 2844791 = 4267187) B4267187
theorem B1896527 : Blo 1895435 1896527 := bstep (se 1 (by rfl) ⟨1422395, by rfl⟩ : syracuseStep 1896527 = 2844791) B2844791
theorem B2844797 : Blo 1895435 2844797 := bbase (se 3 (by rfl) ⟨533399, by rfl⟩ : syracuseStep 2844797 = 1066799) (by norm_num)
theorem B1896531 : Blo 1895435 1896531 := bstep (se 1 (by rfl) ⟨1422398, by rfl⟩ : syracuseStep 1896531 = 2844797) B2844797
theorem B4267205 : Blo 1895435 4267205 := bbase (se 4 (by rfl) ⟨400050, by rfl⟩ : syracuseStep 4267205 = 800101) (by norm_num)
theorem B2844803 : Blo 1895435 2844803 := bstep (se 1 (by rfl) ⟨2133602, by rfl⟩ : syracuseStep 2844803 = 4267205) B4267205
theorem B1896535 : Blo 1895435 1896535 := bstep (se 1 (by rfl) ⟨1422401, by rfl⟩ : syracuseStep 1896535 = 2844803) B2844803
theorem B4556837 : Blo 1895435 4556837 := bbase (se 4 (by rfl) ⟨427203, by rfl⟩ : syracuseStep 4556837 = 854407) (by norm_num)
theorem B12151565 : Blo 1895435 12151565 := bstep (se 3 (by rfl) ⟨2278418, by rfl⟩ : syracuseStep 12151565 = 4556837) B4556837
theorem B8101043 : Blo 1895435 8101043 := bstep (se 1 (by rfl) ⟨6075782, by rfl⟩ : syracuseStep 8101043 = 12151565) B12151565
theorem B5400695 : Blo 1895435 5400695 := bstep (se 1 (by rfl) ⟨4050521, by rfl⟩ : syracuseStep 5400695 = 8101043) B8101043
theorem B3600463 : Blo 1895435 3600463 := bstep (se 1 (by rfl) ⟨2700347, by rfl⟩ : syracuseStep 3600463 = 5400695) B5400695
theorem B4800617 : Blo 1895435 4800617 := bstep (se 2 (by rfl) ⟨1800231, by rfl⟩ : syracuseStep 4800617 = 3600463) B3600463
theorem B3200411 : Blo 1895435 3200411 := bstep (se 1 (by rfl) ⟨2400308, by rfl⟩ : syracuseStep 3200411 = 4800617) B4800617
theorem B2133607 : Blo 1895435 2133607 := bstep (se 1 (by rfl) ⟨1600205, by rfl⟩ : syracuseStep 2133607 = 3200411) B3200411
theorem B2844809 : Blo 1895435 2844809 := bstep (se 2 (by rfl) ⟨1066803, by rfl⟩ : syracuseStep 2844809 = 2133607) B2133607
theorem B1896539 : Blo 1895435 1896539 := bstep (se 1 (by rfl) ⟨1422404, by rfl⟩ : syracuseStep 1896539 = 2844809) B2844809
theorem B9601253 : Blo 1895435 9601253 := bbase (se 4 (by rfl) ⟨900117, by rfl⟩ : syracuseStep 9601253 = 1800235) (by norm_num)
theorem B6400835 : Blo 1895435 6400835 := bstep (se 1 (by rfl) ⟨4800626, by rfl⟩ : syracuseStep 6400835 = 9601253) B9601253
theorem B4267223 : Blo 1895435 4267223 := bstep (se 1 (by rfl) ⟨3200417, by rfl⟩ : syracuseStep 4267223 = 6400835) B6400835
theorem B2844815 : Blo 1895435 2844815 := bstep (se 1 (by rfl) ⟨2133611, by rfl⟩ : syracuseStep 2844815 = 4267223) B4267223
theorem B1896543 : Blo 1895435 1896543 := bstep (se 1 (by rfl) ⟨1422407, by rfl⟩ : syracuseStep 1896543 = 2844815) B2844815
theorem B2844821 : Blo 1895435 2844821 := bbase (se 6 (by rfl) ⟨66675, by rfl⟩ : syracuseStep 2844821 = 133351) (by norm_num)
theorem B1896547 : Blo 1895435 1896547 := bstep (se 1 (by rfl) ⟨1422410, by rfl⟩ : syracuseStep 1896547 = 2844821) B2844821
theorem B8101093 : Blo 1895435 8101093 := bbase (se 4 (by rfl) ⟨759477, by rfl⟩ : syracuseStep 8101093 = 1518955) (by norm_num)
theorem B10801457 : Blo 1895435 10801457 := bstep (se 2 (by rfl) ⟨4050546, by rfl⟩ : syracuseStep 10801457 = 8101093) B8101093
theorem B7200971 : Blo 1895435 7200971 := bstep (se 1 (by rfl) ⟨5400728, by rfl⟩ : syracuseStep 7200971 = 10801457) B10801457
theorem B4800647 : Blo 1895435 4800647 := bstep (se 1 (by rfl) ⟨3600485, by rfl⟩ : syracuseStep 4800647 = 7200971) B7200971
theorem B3200431 : Blo 1895435 3200431 := bstep (se 1 (by rfl) ⟨2400323, by rfl⟩ : syracuseStep 3200431 = 4800647) B4800647
theorem B4267241 : Blo 1895435 4267241 := bstep (se 2 (by rfl) ⟨1600215, by rfl⟩ : syracuseStep 4267241 = 3200431) B3200431
theorem B2844827 : Blo 1895435 2844827 := bstep (se 1 (by rfl) ⟨2133620, by rfl⟩ : syracuseStep 2844827 = 4267241) B4267241
theorem B1896551 : Blo 1895435 1896551 := bstep (se 1 (by rfl) ⟨1422413, by rfl⟩ : syracuseStep 1896551 = 2844827) B2844827
theorem B2133625 : Blo 1895435 2133625 := bbase (se 2 (by rfl) ⟨800109, by rfl⟩ : syracuseStep 2133625 = 1600219) (by norm_num)
theorem B2844833 : Blo 1895435 2844833 := bstep (se 2 (by rfl) ⟨1066812, by rfl⟩ : syracuseStep 2844833 = 2133625) B2133625
theorem B1896555 : Blo 1895435 1896555 := bstep (se 1 (by rfl) ⟨1422416, by rfl⟩ : syracuseStep 1896555 = 2844833) B2844833
theorem B4105829 : Blo 1895435 4105829 := bbase (se 4 (by rfl) ⟨384921, by rfl⟩ : syracuseStep 4105829 = 769843) (by norm_num)
theorem B2737219 : Blo 1895435 2737219 := bstep (se 1 (by rfl) ⟨2052914, by rfl⟩ : syracuseStep 2737219 = 4105829) B4105829
theorem B3649625 : Blo 1895435 3649625 := bstep (se 2 (by rfl) ⟨1368609, by rfl⟩ : syracuseStep 3649625 = 2737219) B2737219
theorem B2433083 : Blo 1895435 2433083 := bstep (se 1 (by rfl) ⟨1824812, by rfl⟩ : syracuseStep 2433083 = 3649625) B3649625
theorem B25952885 : Blo 1895435 25952885 := bstep (se 5 (by rfl) ⟨1216541, by rfl⟩ : syracuseStep 25952885 = 2433083) B2433083
theorem B17301923 : Blo 1895435 17301923 := bstep (se 1 (by rfl) ⟨12976442, by rfl⟩ : syracuseStep 17301923 = 25952885) B25952885
theorem B11534615 : Blo 1895435 11534615 := bstep (se 1 (by rfl) ⟨8650961, by rfl⟩ : syracuseStep 11534615 = 17301923) B17301923
theorem B7689743 : Blo 1895435 7689743 := bstep (se 1 (by rfl) ⟨5767307, by rfl⟩ : syracuseStep 7689743 = 11534615) B11534615
theorem B5126495 : Blo 1895435 5126495 := bstep (se 1 (by rfl) ⟨3844871, by rfl⟩ : syracuseStep 5126495 = 7689743) B7689743
theorem B13670653 : Blo 1895435 13670653 := bstep (se 3 (by rfl) ⟨2563247, by rfl⟩ : syracuseStep 13670653 = 5126495) B5126495
theorem B18227537 : Blo 1895435 18227537 := bstep (se 2 (by rfl) ⟨6835326, by rfl⟩ : syracuseStep 18227537 = 13670653) B13670653
theorem B12151691 : Blo 1895435 12151691 := bstep (se 1 (by rfl) ⟨9113768, by rfl⟩ : syracuseStep 12151691 = 18227537) B18227537
theorem B8101127 : Blo 1895435 8101127 := bstep (se 1 (by rfl) ⟨6075845, by rfl⟩ : syracuseStep 8101127 = 12151691) B12151691
theorem B5400751 : Blo 1895435 5400751 := bstep (se 1 (by rfl) ⟨4050563, by rfl⟩ : syracuseStep 5400751 = 8101127) B8101127
theorem B7201001 : Blo 1895435 7201001 := bstep (se 2 (by rfl) ⟨2700375, by rfl⟩ : syracuseStep 7201001 = 5400751) B5400751
theorem B4800667 : Blo 1895435 4800667 := bstep (se 1 (by rfl) ⟨3600500, by rfl⟩ : syracuseStep 4800667 = 7201001) B7201001
theorem B6400889 : Blo 1895435 6400889 := bstep (se 2 (by rfl) ⟨2400333, by rfl⟩ : syracuseStep 6400889 = 4800667) B4800667
theorem B4267259 : Blo 1895435 4267259 := bstep (se 1 (by rfl) ⟨3200444, by rfl⟩ : syracuseStep 4267259 = 6400889) B6400889
theorem B2844839 : Blo 1895435 2844839 := bstep (se 1 (by rfl) ⟨2133629, by rfl⟩ : syracuseStep 2844839 = 4267259) B4267259
theorem B1896559 : Blo 1895435 1896559 := bstep (se 1 (by rfl) ⟨1422419, by rfl⟩ : syracuseStep 1896559 = 2844839) B2844839
theorem B2844845 : Blo 1895435 2844845 := bbase (se 3 (by rfl) ⟨533408, by rfl⟩ : syracuseStep 2844845 = 1066817) (by norm_num)
theorem B1896563 : Blo 1895435 1896563 := bstep (se 1 (by rfl) ⟨1422422, by rfl⟩ : syracuseStep 1896563 = 2844845) B2844845
theorem B4267277 : Blo 1895435 4267277 := bbase (se 3 (by rfl) ⟨800114, by rfl⟩ : syracuseStep 4267277 = 1600229) (by norm_num)
theorem B2844851 : Blo 1895435 2844851 := bstep (se 1 (by rfl) ⟨2133638, by rfl⟩ : syracuseStep 2844851 = 4267277) B4267277
theorem B1896567 : Blo 1895435 1896567 := bstep (se 1 (by rfl) ⟨1422425, by rfl⟩ : syracuseStep 1896567 = 2844851) B2844851
theorem B2400349 : Blo 1895435 2400349 := bbase (se 3 (by rfl) ⟨450065, by rfl⟩ : syracuseStep 2400349 = 900131) (by norm_num)
theorem B3200465 : Blo 1895435 3200465 := bstep (se 2 (by rfl) ⟨1200174, by rfl⟩ : syracuseStep 3200465 = 2400349) B2400349
theorem B2133643 : Blo 1895435 2133643 := bstep (se 1 (by rfl) ⟨1600232, by rfl⟩ : syracuseStep 2133643 = 3200465) B3200465
theorem B2844857 : Blo 1895435 2844857 := bstep (se 2 (by rfl) ⟨1066821, by rfl⟩ : syracuseStep 2844857 = 2133643) B2133643
theorem B1896571 : Blo 1895435 1896571 := bstep (se 1 (by rfl) ⟨1422428, by rfl⟩ : syracuseStep 1896571 = 2844857) B2844857
theorem B16202389 : Blo 1895435 16202389 := bbase (se 6 (by rfl) ⟨379743, by rfl⟩ : syracuseStep 16202389 = 759487) (by norm_num)
theorem B21603185 : Blo 1895435 21603185 := bstep (se 2 (by rfl) ⟨8101194, by rfl⟩ : syracuseStep 21603185 = 16202389) B16202389
theorem B14402123 : Blo 1895435 14402123 := bstep (se 1 (by rfl) ⟨10801592, by rfl⟩ : syracuseStep 14402123 = 21603185) B21603185
theorem B9601415 : Blo 1895435 9601415 := bstep (se 1 (by rfl) ⟨7201061, by rfl⟩ : syracuseStep 9601415 = 14402123) B14402123
theorem B6400943 : Blo 1895435 6400943 := bstep (se 1 (by rfl) ⟨4800707, by rfl⟩ : syracuseStep 6400943 = 9601415) B9601415
theorem B4267295 : Blo 1895435 4267295 := bstep (se 1 (by rfl) ⟨3200471, by rfl⟩ : syracuseStep 4267295 = 6400943) B6400943
theorem B2844863 : Blo 1895435 2844863 := bstep (se 1 (by rfl) ⟨2133647, by rfl⟩ : syracuseStep 2844863 = 4267295) B4267295
theorem B1896575 : Blo 1895435 1896575 := bstep (se 1 (by rfl) ⟨1422431, by rfl⟩ : syracuseStep 1896575 = 2844863) B2844863
theorem B2844869 : Blo 1895435 2844869 := bbase (se 4 (by rfl) ⟨266706, by rfl⟩ : syracuseStep 2844869 = 533413) (by norm_num)
theorem B1896579 : Blo 1895435 1896579 := bstep (se 1 (by rfl) ⟨1422434, by rfl⟩ : syracuseStep 1896579 = 2844869) B2844869
theorem B3200485 : Blo 1895435 3200485 := bbase (se 4 (by rfl) ⟨300045, by rfl⟩ : syracuseStep 3200485 = 600091) (by norm_num)
theorem B4267313 : Blo 1895435 4267313 := bstep (se 2 (by rfl) ⟨1600242, by rfl⟩ : syracuseStep 4267313 = 3200485) B3200485
theorem B2844875 : Blo 1895435 2844875 := bstep (se 1 (by rfl) ⟨2133656, by rfl⟩ : syracuseStep 2844875 = 4267313) B4267313
theorem B1896583 : Blo 1895435 1896583 := bstep (se 1 (by rfl) ⟨1422437, by rfl⟩ : syracuseStep 1896583 = 2844875) B2844875
theorem B2133661 : Blo 1895435 2133661 := bbase (se 3 (by rfl) ⟨400061, by rfl⟩ : syracuseStep 2133661 = 800123) (by norm_num)
theorem B2844881 : Blo 1895435 2844881 := bstep (se 2 (by rfl) ⟨1066830, by rfl⟩ : syracuseStep 2844881 = 2133661) B2133661
theorem B1896587 : Blo 1895435 1896587 := bstep (se 1 (by rfl) ⟨1422440, by rfl⟩ : syracuseStep 1896587 = 2844881) B2844881
theorem B6400997 : Blo 1895435 6400997 := bbase (se 4 (by rfl) ⟨600093, by rfl⟩ : syracuseStep 6400997 = 1200187) (by norm_num)
theorem B4267331 : Blo 1895435 4267331 := bstep (se 1 (by rfl) ⟨3200498, by rfl⟩ : syracuseStep 4267331 = 6400997) B6400997
theorem B2844887 : Blo 1895435 2844887 := bstep (se 1 (by rfl) ⟨2133665, by rfl⟩ : syracuseStep 2844887 = 4267331) B4267331
theorem B1896591 : Blo 1895435 1896591 := bstep (se 1 (by rfl) ⟨1422443, by rfl⟩ : syracuseStep 1896591 = 2844887) B2844887
theorem B2844893 : Blo 1895435 2844893 := bbase (se 3 (by rfl) ⟨533417, by rfl⟩ : syracuseStep 2844893 = 1066835) (by norm_num)
theorem B1896595 : Blo 1895435 1896595 := bstep (se 1 (by rfl) ⟨1422446, by rfl⟩ : syracuseStep 1896595 = 2844893) B2844893
theorem B4267349 : Blo 1895435 4267349 := bbase (se 11 (by rfl) ⟨3125, by rfl⟩ : syracuseStep 4267349 = 6251) (by norm_num)
theorem B2844899 : Blo 1895435 2844899 := bstep (se 1 (by rfl) ⟨2133674, by rfl⟩ : syracuseStep 2844899 = 4267349) B4267349
theorem B1896599 : Blo 1895435 1896599 := bstep (se 1 (by rfl) ⟨1422449, by rfl⟩ : syracuseStep 1896599 = 2844899) B2844899
theorem B2025329 : Blo 1895435 2025329 := bbase (se 2 (by rfl) ⟨759498, by rfl⟩ : syracuseStep 2025329 = 1518997) (by norm_num)
theorem B5400877 : Blo 1895435 5400877 := bstep (se 3 (by rfl) ⟨1012664, by rfl⟩ : syracuseStep 5400877 = 2025329) B2025329
theorem B7201169 : Blo 1895435 7201169 := bstep (se 2 (by rfl) ⟨2700438, by rfl⟩ : syracuseStep 7201169 = 5400877) B5400877
theorem B4800779 : Blo 1895435 4800779 := bstep (se 1 (by rfl) ⟨3600584, by rfl⟩ : syracuseStep 4800779 = 7201169) B7201169
theorem B3200519 : Blo 1895435 3200519 := bstep (se 1 (by rfl) ⟨2400389, by rfl⟩ : syracuseStep 3200519 = 4800779) B4800779
theorem B2133679 : Blo 1895435 2133679 := bstep (se 1 (by rfl) ⟨1600259, by rfl⟩ : syracuseStep 2133679 = 3200519) B3200519
theorem B2844905 : Blo 1895435 2844905 := bstep (se 2 (by rfl) ⟨1066839, by rfl⟩ : syracuseStep 2844905 = 2133679) B2133679
theorem B1896603 : Blo 1895435 1896603 := bstep (se 1 (by rfl) ⟨1422452, by rfl⟩ : syracuseStep 1896603 = 2844905) B2844905
theorem B17302357 : Blo 1895435 17302357 := bbase (se 9 (by rfl) ⟨50690, by rfl⟩ : syracuseStep 17302357 = 101381) (by norm_num)
theorem B23069809 : Blo 1895435 23069809 := bstep (se 2 (by rfl) ⟨8651178, by rfl⟩ : syracuseStep 23069809 = 17302357) B17302357
theorem B30759745 : Blo 1895435 30759745 := bstep (se 2 (by rfl) ⟨11534904, by rfl⟩ : syracuseStep 30759745 = 23069809) B23069809
theorem B41012993 : Blo 1895435 41012993 := bstep (se 2 (by rfl) ⟨15379872, by rfl⟩ : syracuseStep 41012993 = 30759745) B30759745
theorem B27341995 : Blo 1895435 27341995 := bstep (se 1 (by rfl) ⟨20506496, by rfl⟩ : syracuseStep 27341995 = 41012993) B41012993
theorem B36455993 : Blo 1895435 36455993 := bstep (se 2 (by rfl) ⟨13670997, by rfl⟩ : syracuseStep 36455993 = 27341995) B27341995
theorem B24303995 : Blo 1895435 24303995 := bstep (se 1 (by rfl) ⟨18227996, by rfl⟩ : syracuseStep 24303995 = 36455993) B36455993
theorem B16202663 : Blo 1895435 16202663 := bstep (se 1 (by rfl) ⟨12151997, by rfl⟩ : syracuseStep 16202663 = 24303995) B24303995
theorem B10801775 : Blo 1895435 10801775 := bstep (se 1 (by rfl) ⟨8101331, by rfl⟩ : syracuseStep 10801775 = 16202663) B16202663
theorem B7201183 : Blo 1895435 7201183 := bstep (se 1 (by rfl) ⟨5400887, by rfl⟩ : syracuseStep 7201183 = 10801775) B10801775
theorem B9601577 : Blo 1895435 9601577 := bstep (se 2 (by rfl) ⟨3600591, by rfl⟩ : syracuseStep 9601577 = 7201183) B7201183
theorem B6401051 : Blo 1895435 6401051 := bstep (se 1 (by rfl) ⟨4800788, by rfl⟩ : syracuseStep 6401051 = 9601577) B9601577
theorem B4267367 : Blo 1895435 4267367 := bstep (se 1 (by rfl) ⟨3200525, by rfl⟩ : syracuseStep 4267367 = 6401051) B6401051
theorem B2844911 : Blo 1895435 2844911 := bstep (se 1 (by rfl) ⟨2133683, by rfl⟩ : syracuseStep 2844911 = 4267367) B4267367
theorem B1896607 : Blo 1895435 1896607 := bstep (se 1 (by rfl) ⟨1422455, by rfl⟩ : syracuseStep 1896607 = 2844911) B2844911
theorem B2844917 : Blo 1895435 2844917 := bbase (se 5 (by rfl) ⟨133355, by rfl⟩ : syracuseStep 2844917 = 266711) (by norm_num)
theorem B1896611 : Blo 1895435 1896611 := bstep (se 1 (by rfl) ⟨1422458, by rfl⟩ : syracuseStep 1896611 = 2844917) B2844917
theorem B2923085 : Blo 1895435 2923085 := bbase (se 3 (by rfl) ⟨548078, by rfl⟩ : syracuseStep 2923085 = 1096157) (by norm_num)
theorem B7794893 : Blo 1895435 7794893 := bstep (se 3 (by rfl) ⟨1461542, by rfl⟩ : syracuseStep 7794893 = 2923085) B2923085
theorem B5196595 : Blo 1895435 5196595 := bstep (se 1 (by rfl) ⟨3897446, by rfl⟩ : syracuseStep 5196595 = 7794893) B7794893
theorem B6928793 : Blo 1895435 6928793 := bstep (se 2 (by rfl) ⟨2598297, by rfl⟩ : syracuseStep 6928793 = 5196595) B5196595
theorem B4619195 : Blo 1895435 4619195 := bstep (se 1 (by rfl) ⟨3464396, by rfl⟩ : syracuseStep 4619195 = 6928793) B6928793
theorem B3079463 : Blo 1895435 3079463 := bstep (se 1 (by rfl) ⟨2309597, by rfl⟩ : syracuseStep 3079463 = 4619195) B4619195
theorem B8211901 : Blo 1895435 8211901 := bstep (se 3 (by rfl) ⟨1539731, by rfl⟩ : syracuseStep 8211901 = 3079463) B3079463
theorem B10949201 : Blo 1895435 10949201 := bstep (se 2 (by rfl) ⟨4105950, by rfl⟩ : syracuseStep 10949201 = 8211901) B8211901
theorem B7299467 : Blo 1895435 7299467 := bstep (se 1 (by rfl) ⟨5474600, by rfl⟩ : syracuseStep 7299467 = 10949201) B10949201
theorem B4866311 : Blo 1895435 4866311 := bstep (se 1 (by rfl) ⟨3649733, by rfl⟩ : syracuseStep 4866311 = 7299467) B7299467
theorem B3244207 : Blo 1895435 3244207 := bstep (se 1 (by rfl) ⟨2433155, by rfl⟩ : syracuseStep 3244207 = 4866311) B4866311
theorem B4325609 : Blo 1895435 4325609 := bstep (se 2 (by rfl) ⟨1622103, by rfl⟩ : syracuseStep 4325609 = 3244207) B3244207
theorem B11534957 : Blo 1895435 11534957 := bstep (se 3 (by rfl) ⟨2162804, by rfl⟩ : syracuseStep 11534957 = 4325609) B4325609
theorem B7689971 : Blo 1895435 7689971 := bstep (se 1 (by rfl) ⟨5767478, by rfl⟩ : syracuseStep 7689971 = 11534957) B11534957
theorem B5126647 : Blo 1895435 5126647 := bstep (se 1 (by rfl) ⟨3844985, by rfl⟩ : syracuseStep 5126647 = 7689971) B7689971
theorem B6835529 : Blo 1895435 6835529 := bstep (se 2 (by rfl) ⟨2563323, by rfl⟩ : syracuseStep 6835529 = 5126647) B5126647
theorem B18228077 : Blo 1895435 18228077 := bstep (se 3 (by rfl) ⟨3417764, by rfl⟩ : syracuseStep 18228077 = 6835529) B6835529
theorem B12152051 : Blo 1895435 12152051 := bstep (se 1 (by rfl) ⟨9114038, by rfl⟩ : syracuseStep 12152051 = 18228077) B18228077
theorem B8101367 : Blo 1895435 8101367 := bstep (se 1 (by rfl) ⟨6076025, by rfl⟩ : syracuseStep 8101367 = 12152051) B12152051
theorem B5400911 : Blo 1895435 5400911 := bstep (se 1 (by rfl) ⟨4050683, by rfl⟩ : syracuseStep 5400911 = 8101367) B8101367
theorem B3600607 : Blo 1895435 3600607 := bstep (se 1 (by rfl) ⟨2700455, by rfl⟩ : syracuseStep 3600607 = 5400911) B5400911
theorem B4800809 : Blo 1895435 4800809 := bstep (se 2 (by rfl) ⟨1800303, by rfl⟩ : syracuseStep 4800809 = 3600607) B3600607
theorem B3200539 : Blo 1895435 3200539 := bstep (se 1 (by rfl) ⟨2400404, by rfl⟩ : syracuseStep 3200539 = 4800809) B4800809
theorem B4267385 : Blo 1895435 4267385 := bstep (se 2 (by rfl) ⟨1600269, by rfl⟩ : syracuseStep 4267385 = 3200539) B3200539
theorem B2844923 : Blo 1895435 2844923 := bstep (se 1 (by rfl) ⟨2133692, by rfl⟩ : syracuseStep 2844923 = 4267385) B4267385
theorem B1896615 : Blo 1895435 1896615 := bstep (se 1 (by rfl) ⟨1422461, by rfl⟩ : syracuseStep 1896615 = 2844923) B2844923
theorem B2133697 : Blo 1895435 2133697 := bbase (se 2 (by rfl) ⟨800136, by rfl⟩ : syracuseStep 2133697 = 1600273) (by norm_num)
theorem B2844929 : Blo 1895435 2844929 := bstep (se 2 (by rfl) ⟨1066848, by rfl⟩ : syracuseStep 2844929 = 2133697) B2133697
theorem B1896619 : Blo 1895435 1896619 := bstep (se 1 (by rfl) ⟨1422464, by rfl⟩ : syracuseStep 1896619 = 2844929) B2844929
theorem B4800829 : Blo 1895435 4800829 := bbase (se 3 (by rfl) ⟨900155, by rfl⟩ : syracuseStep 4800829 = 1800311) (by norm_num)
theorem B6401105 : Blo 1895435 6401105 := bstep (se 2 (by rfl) ⟨2400414, by rfl⟩ : syracuseStep 6401105 = 4800829) B4800829
theorem B4267403 : Blo 1895435 4267403 := bstep (se 1 (by rfl) ⟨3200552, by rfl⟩ : syracuseStep 4267403 = 6401105) B6401105
theorem B2844935 : Blo 1895435 2844935 := bstep (se 1 (by rfl) ⟨2133701, by rfl⟩ : syracuseStep 2844935 = 4267403) B4267403
theorem B1896623 : Blo 1895435 1896623 := bstep (se 1 (by rfl) ⟨1422467, by rfl⟩ : syracuseStep 1896623 = 2844935) B2844935
theorem B2844941 : Blo 1895435 2844941 := bbase (se 3 (by rfl) ⟨533426, by rfl⟩ : syracuseStep 2844941 = 1066853) (by norm_num)
theorem B1896627 : Blo 1895435 1896627 := bstep (se 1 (by rfl) ⟨1422470, by rfl⟩ : syracuseStep 1896627 = 2844941) B2844941
theorem B4267421 : Blo 1895435 4267421 := bbase (se 3 (by rfl) ⟨800141, by rfl⟩ : syracuseStep 4267421 = 1600283) (by norm_num)
theorem B2844947 : Blo 1895435 2844947 := bstep (se 1 (by rfl) ⟨2133710, by rfl⟩ : syracuseStep 2844947 = 4267421) B4267421
theorem B1896631 : Blo 1895435 1896631 := bstep (se 1 (by rfl) ⟨1422473, by rfl⟩ : syracuseStep 1896631 = 2844947) B2844947
theorem B3200573 : Blo 1895435 3200573 := bbase (se 3 (by rfl) ⟨600107, by rfl⟩ : syracuseStep 3200573 = 1200215) (by norm_num)
theorem B2133715 : Blo 1895435 2133715 := bstep (se 1 (by rfl) ⟨1600286, by rfl⟩ : syracuseStep 2133715 = 3200573) B3200573
theorem B2844953 : Blo 1895435 2844953 := bstep (se 2 (by rfl) ⟨1066857, by rfl⟩ : syracuseStep 2844953 = 2133715) B2133715
theorem B1896635 : Blo 1895435 1896635 := bstep (se 1 (by rfl) ⟨1422476, by rfl⟩ : syracuseStep 1896635 = 2844953) B2844953
theorem B4557077 : Blo 1895435 4557077 := bbase (se 6 (by rfl) ⟨106806, by rfl⟩ : syracuseStep 4557077 = 213613) (by norm_num)
theorem B3038051 : Blo 1895435 3038051 := bstep (se 1 (by rfl) ⟨2278538, by rfl⟩ : syracuseStep 3038051 = 4557077) B4557077
theorem B2025367 : Blo 1895435 2025367 := bstep (se 1 (by rfl) ⟨1519025, by rfl⟩ : syracuseStep 2025367 = 3038051) B3038051
theorem B10801957 : Blo 1895435 10801957 := bstep (se 4 (by rfl) ⟨1012683, by rfl⟩ : syracuseStep 10801957 = 2025367) B2025367
theorem B14402609 : Blo 1895435 14402609 := bstep (se 2 (by rfl) ⟨5400978, by rfl⟩ : syracuseStep 14402609 = 10801957) B10801957
theorem B9601739 : Blo 1895435 9601739 := bstep (se 1 (by rfl) ⟨7201304, by rfl⟩ : syracuseStep 9601739 = 14402609) B14402609
theorem B6401159 : Blo 1895435 6401159 := bstep (se 1 (by rfl) ⟨4800869, by rfl⟩ : syracuseStep 6401159 = 9601739) B9601739
theorem B4267439 : Blo 1895435 4267439 := bstep (se 1 (by rfl) ⟨3200579, by rfl⟩ : syracuseStep 4267439 = 6401159) B6401159
theorem B2844959 : Blo 1895435 2844959 := bstep (se 1 (by rfl) ⟨2133719, by rfl⟩ : syracuseStep 2844959 = 4267439) B4267439
theorem B1896639 : Blo 1895435 1896639 := bstep (se 1 (by rfl) ⟨1422479, by rfl⟩ : syracuseStep 1896639 = 2844959) B2844959
theorem B2844965 : Blo 1895435 2844965 := bbase (se 4 (by rfl) ⟨266715, by rfl⟩ : syracuseStep 2844965 = 533431) (by norm_num)
theorem B1896643 : Blo 1895435 1896643 := bstep (se 1 (by rfl) ⟨1422482, by rfl⟩ : syracuseStep 1896643 = 2844965) B2844965
theorem B2400445 : Blo 1895435 2400445 := bbase (se 3 (by rfl) ⟨450083, by rfl⟩ : syracuseStep 2400445 = 900167) (by norm_num)
theorem B3200593 : Blo 1895435 3200593 := bstep (se 2 (by rfl) ⟨1200222, by rfl⟩ : syracuseStep 3200593 = 2400445) B2400445
theorem B4267457 : Blo 1895435 4267457 := bstep (se 2 (by rfl) ⟨1600296, by rfl⟩ : syracuseStep 4267457 = 3200593) B3200593
theorem B2844971 : Blo 1895435 2844971 := bstep (se 1 (by rfl) ⟨2133728, by rfl⟩ : syracuseStep 2844971 = 4267457) B4267457
theorem B1896647 : Blo 1895435 1896647 := bstep (se 1 (by rfl) ⟨1422485, by rfl⟩ : syracuseStep 1896647 = 2844971) B2844971
theorem B2133733 : Blo 1895435 2133733 := bbase (se 4 (by rfl) ⟨200037, by rfl⟩ : syracuseStep 2133733 = 400075) (by norm_num)
theorem B2844977 : Blo 1895435 2844977 := bstep (se 2 (by rfl) ⟨1066866, by rfl⟩ : syracuseStep 2844977 = 2133733) B2133733
theorem B1896651 : Blo 1895435 1896651 := bstep (se 1 (by rfl) ⟨1422488, by rfl⟩ : syracuseStep 1896651 = 2844977) B2844977
theorem B3038077 : Blo 1895435 3038077 := bbase (se 3 (by rfl) ⟨569639, by rfl⟩ : syracuseStep 3038077 = 1139279) (by norm_num)
theorem B4050769 : Blo 1895435 4050769 := bstep (se 2 (by rfl) ⟨1519038, by rfl⟩ : syracuseStep 4050769 = 3038077) B3038077
theorem B5401025 : Blo 1895435 5401025 := bstep (se 2 (by rfl) ⟨2025384, by rfl⟩ : syracuseStep 5401025 = 4050769) B4050769
theorem B3600683 : Blo 1895435 3600683 := bstep (se 1 (by rfl) ⟨2700512, by rfl⟩ : syracuseStep 3600683 = 5401025) B5401025
theorem B2400455 : Blo 1895435 2400455 := bstep (se 1 (by rfl) ⟨1800341, by rfl⟩ : syracuseStep 2400455 = 3600683) B3600683
theorem B6401213 : Blo 1895435 6401213 := bstep (se 3 (by rfl) ⟨1200227, by rfl⟩ : syracuseStep 6401213 = 2400455) B2400455
theorem B4267475 : Blo 1895435 4267475 := bstep (se 1 (by rfl) ⟨3200606, by rfl⟩ : syracuseStep 4267475 = 6401213) B6401213
theorem B2844983 : Blo 1895435 2844983 := bstep (se 1 (by rfl) ⟨2133737, by rfl⟩ : syracuseStep 2844983 = 4267475) B4267475
theorem B1896655 : Blo 1895435 1896655 := bstep (se 1 (by rfl) ⟨1422491, by rfl⟩ : syracuseStep 1896655 = 2844983) B2844983
theorem B2844989 : Blo 1895435 2844989 := bbase (se 3 (by rfl) ⟨533435, by rfl⟩ : syracuseStep 2844989 = 1066871) (by norm_num)
theorem B1896659 : Blo 1895435 1896659 := bstep (se 1 (by rfl) ⟨1422494, by rfl⟩ : syracuseStep 1896659 = 2844989) B2844989
theorem B4267493 : Blo 1895435 4267493 := bbase (se 4 (by rfl) ⟨400077, by rfl⟩ : syracuseStep 4267493 = 800155) (by norm_num)
theorem B2844995 : Blo 1895435 2844995 := bstep (se 1 (by rfl) ⟨2133746, by rfl⟩ : syracuseStep 2844995 = 4267493) B4267493
theorem B1896663 : Blo 1895435 1896663 := bstep (se 1 (by rfl) ⟨1422497, by rfl⟩ : syracuseStep 1896663 = 2844995) B2844995
theorem B4800941 : Blo 1895435 4800941 := bbase (se 3 (by rfl) ⟨900176, by rfl⟩ : syracuseStep 4800941 = 1800353) (by norm_num)
theorem B3200627 : Blo 1895435 3200627 := bstep (se 1 (by rfl) ⟨2400470, by rfl⟩ : syracuseStep 3200627 = 4800941) B4800941
theorem B2133751 : Blo 1895435 2133751 := bstep (se 1 (by rfl) ⟨1600313, by rfl⟩ : syracuseStep 2133751 = 3200627) B3200627
theorem B2845001 : Blo 1895435 2845001 := bstep (se 2 (by rfl) ⟨1066875, by rfl⟩ : syracuseStep 2845001 = 2133751) B2133751
theorem B1896667 : Blo 1895435 1896667 := bstep (se 1 (by rfl) ⟨1422500, by rfl⟩ : syracuseStep 1896667 = 2845001) B2845001
theorem B2278577 : Blo 1895435 2278577 := bbase (se 2 (by rfl) ⟨854466, by rfl⟩ : syracuseStep 2278577 = 1708933) (by norm_num)
theorem B6076205 : Blo 1895435 6076205 := bstep (se 3 (by rfl) ⟨1139288, by rfl⟩ : syracuseStep 6076205 = 2278577) B2278577
theorem B4050803 : Blo 1895435 4050803 := bstep (se 1 (by rfl) ⟨3038102, by rfl⟩ : syracuseStep 4050803 = 6076205) B6076205
theorem B2700535 : Blo 1895435 2700535 := bstep (se 1 (by rfl) ⟨2025401, by rfl⟩ : syracuseStep 2700535 = 4050803) B4050803
theorem B3600713 : Blo 1895435 3600713 := bstep (se 2 (by rfl) ⟨1350267, by rfl⟩ : syracuseStep 3600713 = 2700535) B2700535
theorem B9601901 : Blo 1895435 9601901 := bstep (se 3 (by rfl) ⟨1800356, by rfl⟩ : syracuseStep 9601901 = 3600713) B3600713
theorem B6401267 : Blo 1895435 6401267 := bstep (se 1 (by rfl) ⟨4800950, by rfl⟩ : syracuseStep 6401267 = 9601901) B9601901
theorem B4267511 : Blo 1895435 4267511 := bstep (se 1 (by rfl) ⟨3200633, by rfl⟩ : syracuseStep 4267511 = 6401267) B6401267
theorem B2845007 : Blo 1895435 2845007 := bstep (se 1 (by rfl) ⟨2133755, by rfl⟩ : syracuseStep 2845007 = 4267511) B4267511
theorem B1896671 : Blo 1895435 1896671 := bstep (se 1 (by rfl) ⟨1422503, by rfl⟩ : syracuseStep 1896671 = 2845007) B2845007
theorem B2845013 : Blo 1895435 2845013 := bbase (se 10 (by rfl) ⟨4167, by rfl⟩ : syracuseStep 2845013 = 8335) (by norm_num)
theorem B1896675 : Blo 1895435 1896675 := bstep (se 1 (by rfl) ⟨1422506, by rfl⟩ : syracuseStep 1896675 = 2845013) B2845013
theorem B5401093 : Blo 1895435 5401093 := bbase (se 4 (by rfl) ⟨506352, by rfl⟩ : syracuseStep 5401093 = 1012705) (by norm_num)
theorem B7201457 : Blo 1895435 7201457 := bstep (se 2 (by rfl) ⟨2700546, by rfl⟩ : syracuseStep 7201457 = 5401093) B5401093
theorem B4800971 : Blo 1895435 4800971 := bstep (se 1 (by rfl) ⟨3600728, by rfl⟩ : syracuseStep 4800971 = 7201457) B7201457
theorem B3200647 : Blo 1895435 3200647 := bstep (se 1 (by rfl) ⟨2400485, by rfl⟩ : syracuseStep 3200647 = 4800971) B4800971
theorem B4267529 : Blo 1895435 4267529 := bstep (se 2 (by rfl) ⟨1600323, by rfl⟩ : syracuseStep 4267529 = 3200647) B3200647
theorem B2845019 : Blo 1895435 2845019 := bstep (se 1 (by rfl) ⟨2133764, by rfl⟩ : syracuseStep 2845019 = 4267529) B4267529
theorem B1896679 : Blo 1895435 1896679 := bstep (se 1 (by rfl) ⟨1422509, by rfl⟩ : syracuseStep 1896679 = 2845019) B2845019
theorem B2133769 : Blo 1895435 2133769 := bbase (se 2 (by rfl) ⟨800163, by rfl⟩ : syracuseStep 2133769 = 1600327) (by norm_num)
theorem B2845025 : Blo 1895435 2845025 := bstep (se 2 (by rfl) ⟨1066884, by rfl⟩ : syracuseStep 2845025 = 2133769) B2133769
theorem B1896683 : Blo 1895435 1896683 := bstep (se 1 (by rfl) ⟨1422512, by rfl⟩ : syracuseStep 1896683 = 2845025) B2845025
theorem B30761045 : Blo 1895435 30761045 := bbase (se 8 (by rfl) ⟨180240, by rfl⟩ : syracuseStep 30761045 = 360481) (by norm_num)
theorem B20507363 : Blo 1895435 20507363 := bstep (se 1 (by rfl) ⟨15380522, by rfl⟩ : syracuseStep 20507363 = 30761045) B30761045
theorem B13671575 : Blo 1895435 13671575 := bstep (se 1 (by rfl) ⟨10253681, by rfl⟩ : syracuseStep 13671575 = 20507363) B20507363
theorem B9114383 : Blo 1895435 9114383 := bstep (se 1 (by rfl) ⟨6835787, by rfl⟩ : syracuseStep 9114383 = 13671575) B13671575
theorem B24305021 : Blo 1895435 24305021 := bstep (se 3 (by rfl) ⟨4557191, by rfl⟩ : syracuseStep 24305021 = 9114383) B9114383
theorem B16203347 : Blo 1895435 16203347 := bstep (se 1 (by rfl) ⟨12152510, by rfl⟩ : syracuseStep 16203347 = 24305021) B24305021
theorem B10802231 : Blo 1895435 10802231 := bstep (se 1 (by rfl) ⟨8101673, by rfl⟩ : syracuseStep 10802231 = 16203347) B16203347
theorem B7201487 : Blo 1895435 7201487 := bstep (se 1 (by rfl) ⟨5401115, by rfl⟩ : syracuseStep 7201487 = 10802231) B10802231
theorem B4800991 : Blo 1895435 4800991 := bstep (se 1 (by rfl) ⟨3600743, by rfl⟩ : syracuseStep 4800991 = 7201487) B7201487
theorem B6401321 : Blo 1895435 6401321 := bstep (se 2 (by rfl) ⟨2400495, by rfl⟩ : syracuseStep 6401321 = 4800991) B4800991
theorem B4267547 : Blo 1895435 4267547 := bstep (se 1 (by rfl) ⟨3200660, by rfl⟩ : syracuseStep 4267547 = 6401321) B6401321
theorem B2845031 : Blo 1895435 2845031 := bstep (se 1 (by rfl) ⟨2133773, by rfl⟩ : syracuseStep 2845031 = 4267547) B4267547
theorem B1896687 : Blo 1895435 1896687 := bstep (se 1 (by rfl) ⟨1422515, by rfl⟩ : syracuseStep 1896687 = 2845031) B2845031
theorem B2845037 : Blo 1895435 2845037 := bbase (se 3 (by rfl) ⟨533444, by rfl⟩ : syracuseStep 2845037 = 1066889) (by norm_num)
theorem B1896691 : Blo 1895435 1896691 := bstep (se 1 (by rfl) ⟨1422518, by rfl⟩ : syracuseStep 1896691 = 2845037) B2845037
theorem B4267565 : Blo 1895435 4267565 := bbase (se 3 (by rfl) ⟨800168, by rfl⟩ : syracuseStep 4267565 = 1600337) (by norm_num)
theorem B2845043 : Blo 1895435 2845043 := bstep (se 1 (by rfl) ⟨2133782, by rfl⟩ : syracuseStep 2845043 = 4267565) B4267565
theorem B1896695 : Blo 1895435 1896695 := bstep (se 1 (by rfl) ⟨1422521, by rfl⟩ : syracuseStep 1896695 = 2845043) B2845043
theorem B41014997 : Blo 1895435 41014997 := bbase (se 7 (by rfl) ⟨480644, by rfl⟩ : syracuseStep 41014997 = 961289) (by norm_num)
theorem B27343331 : Blo 1895435 27343331 := bstep (se 1 (by rfl) ⟨20507498, by rfl⟩ : syracuseStep 27343331 = 41014997) B41014997
theorem B18228887 : Blo 1895435 18228887 := bstep (se 1 (by rfl) ⟨13671665, by rfl⟩ : syracuseStep 18228887 = 27343331) B27343331
theorem B12152591 : Blo 1895435 12152591 := bstep (se 1 (by rfl) ⟨9114443, by rfl⟩ : syracuseStep 12152591 = 18228887) B18228887
theorem B8101727 : Blo 1895435 8101727 := bstep (se 1 (by rfl) ⟨6076295, by rfl⟩ : syracuseStep 8101727 = 12152591) B12152591
theorem B5401151 : Blo 1895435 5401151 := bstep (se 1 (by rfl) ⟨4050863, by rfl⟩ : syracuseStep 5401151 = 8101727) B8101727
theorem B3600767 : Blo 1895435 3600767 := bstep (se 1 (by rfl) ⟨2700575, by rfl⟩ : syracuseStep 3600767 = 5401151) B5401151
theorem B2400511 : Blo 1895435 2400511 := bstep (se 1 (by rfl) ⟨1800383, by rfl⟩ : syracuseStep 2400511 = 3600767) B3600767
theorem B3200681 : Blo 1895435 3200681 := bstep (se 2 (by rfl) ⟨1200255, by rfl⟩ : syracuseStep 3200681 = 2400511) B2400511
theorem B2133787 : Blo 1895435 2133787 := bstep (se 1 (by rfl) ⟨1600340, by rfl⟩ : syracuseStep 2133787 = 3200681) B3200681
theorem B2845049 : Blo 1895435 2845049 := bstep (se 2 (by rfl) ⟨1066893, by rfl⟩ : syracuseStep 2845049 = 2133787) B2133787
theorem B1896699 : Blo 1895435 1896699 := bstep (se 1 (by rfl) ⟨1422524, by rfl⟩ : syracuseStep 1896699 = 2845049) B2845049
theorem B5126885 : Blo 1895435 5126885 := bbase (se 4 (by rfl) ⟨480645, by rfl⟩ : syracuseStep 5126885 = 961291) (by norm_num)
theorem B3417923 : Blo 1895435 3417923 := bstep (se 1 (by rfl) ⟨2563442, by rfl⟩ : syracuseStep 3417923 = 5126885) B5126885
theorem B2278615 : Blo 1895435 2278615 := bstep (se 1 (by rfl) ⟨1708961, by rfl⟩ : syracuseStep 2278615 = 3417923) B3417923
theorem B3038153 : Blo 1895435 3038153 := bstep (se 2 (by rfl) ⟨1139307, by rfl⟩ : syracuseStep 3038153 = 2278615) B2278615
theorem B32406965 : Blo 1895435 32406965 := bstep (se 5 (by rfl) ⟨1519076, by rfl⟩ : syracuseStep 32406965 = 3038153) B3038153
theorem B21604643 : Blo 1895435 21604643 := bstep (se 1 (by rfl) ⟨16203482, by rfl⟩ : syracuseStep 21604643 = 32406965) B32406965
theorem B14403095 : Blo 1895435 14403095 := bstep (se 1 (by rfl) ⟨10802321, by rfl⟩ : syracuseStep 14403095 = 21604643) B21604643
theorem B9602063 : Blo 1895435 9602063 := bstep (se 1 (by rfl) ⟨7201547, by rfl⟩ : syracuseStep 9602063 = 14403095) B14403095
theorem B6401375 : Blo 1895435 6401375 := bstep (se 1 (by rfl) ⟨4801031, by rfl⟩ : syracuseStep 6401375 = 9602063) B9602063
theorem B4267583 : Blo 1895435 4267583 := bstep (se 1 (by rfl) ⟨3200687, by rfl⟩ : syracuseStep 4267583 = 6401375) B6401375
theorem B2845055 : Blo 1895435 2845055 := bstep (se 1 (by rfl) ⟨2133791, by rfl⟩ : syracuseStep 2845055 = 4267583) B4267583
theorem B1896703 : Blo 1895435 1896703 := bstep (se 1 (by rfl) ⟨1422527, by rfl⟩ : syracuseStep 1896703 = 2845055) B2845055
theorem B2845061 : Blo 1895435 2845061 := bbase (se 4 (by rfl) ⟨266724, by rfl⟩ : syracuseStep 2845061 = 533449) (by norm_num)
theorem B1896707 : Blo 1895435 1896707 := bstep (se 1 (by rfl) ⟨1422530, by rfl⟩ : syracuseStep 1896707 = 2845061) B2845061
theorem B3200701 : Blo 1895435 3200701 := bbase (se 3 (by rfl) ⟨600131, by rfl⟩ : syracuseStep 3200701 = 1200263) (by norm_num)
theorem B4267601 : Blo 1895435 4267601 := bstep (se 2 (by rfl) ⟨1600350, by rfl⟩ : syracuseStep 4267601 = 3200701) B3200701
theorem B2845067 : Blo 1895435 2845067 := bstep (se 1 (by rfl) ⟨2133800, by rfl⟩ : syracuseStep 2845067 = 4267601) B4267601
theorem B1896711 : Blo 1895435 1896711 := bstep (se 1 (by rfl) ⟨1422533, by rfl⟩ : syracuseStep 1896711 = 2845067) B2845067
theorem B2133805 : Blo 1895435 2133805 := bbase (se 3 (by rfl) ⟨400088, by rfl⟩ : syracuseStep 2133805 = 800177) (by norm_num)
theorem B2845073 : Blo 1895435 2845073 := bstep (se 2 (by rfl) ⟨1066902, by rfl⟩ : syracuseStep 2845073 = 2133805) B2133805
theorem B1896715 : Blo 1895435 1896715 := bstep (se 1 (by rfl) ⟨1422536, by rfl⟩ : syracuseStep 1896715 = 2845073) B2845073
theorem B6401429 : Blo 1895435 6401429 := bbase (se 6 (by rfl) ⟨150033, by rfl⟩ : syracuseStep 6401429 = 300067) (by norm_num)
theorem B4267619 : Blo 1895435 4267619 := bstep (se 1 (by rfl) ⟨3200714, by rfl⟩ : syracuseStep 4267619 = 6401429) B6401429
theorem B2845079 : Blo 1895435 2845079 := bstep (se 1 (by rfl) ⟨2133809, by rfl⟩ : syracuseStep 2845079 = 4267619) B4267619
theorem B1896719 : Blo 1895435 1896719 := bstep (se 1 (by rfl) ⟨1422539, by rfl⟩ : syracuseStep 1896719 = 2845079) B2845079
theorem B2845085 : Blo 1895435 2845085 := bbase (se 3 (by rfl) ⟨533453, by rfl⟩ : syracuseStep 2845085 = 1066907) (by norm_num)
theorem B1896723 : Blo 1895435 1896723 := bstep (se 1 (by rfl) ⟨1422542, by rfl⟩ : syracuseStep 1896723 = 2845085) B2845085
theorem B4267637 : Blo 1895435 4267637 := bbase (se 5 (by rfl) ⟨200045, by rfl⟩ : syracuseStep 4267637 = 400091) (by norm_num)
theorem B2845091 : Blo 1895435 2845091 := bstep (se 1 (by rfl) ⟨2133818, by rfl⟩ : syracuseStep 2845091 = 4267637) B4267637
theorem B1896727 : Blo 1895435 1896727 := bstep (se 1 (by rfl) ⟨1422545, by rfl⟩ : syracuseStep 1896727 = 2845091) B2845091
theorem B2278649 : Blo 1895435 2278649 := bbase (se 2 (by rfl) ⟨854493, by rfl⟩ : syracuseStep 2278649 = 1708987) (by norm_num)
theorem B6076397 : Blo 1895435 6076397 := bstep (se 3 (by rfl) ⟨1139324, by rfl⟩ : syracuseStep 6076397 = 2278649) B2278649
theorem B16203725 : Blo 1895435 16203725 := bstep (se 3 (by rfl) ⟨3038198, by rfl⟩ : syracuseStep 16203725 = 6076397) B6076397
theorem B10802483 : Blo 1895435 10802483 := bstep (se 1 (by rfl) ⟨8101862, by rfl⟩ : syracuseStep 10802483 = 16203725) B16203725
theorem B7201655 : Blo 1895435 7201655 := bstep (se 1 (by rfl) ⟨5401241, by rfl⟩ : syracuseStep 7201655 = 10802483) B10802483
theorem B4801103 : Blo 1895435 4801103 := bstep (se 1 (by rfl) ⟨3600827, by rfl⟩ : syracuseStep 4801103 = 7201655) B7201655
theorem B3200735 : Blo 1895435 3200735 := bstep (se 1 (by rfl) ⟨2400551, by rfl⟩ : syracuseStep 3200735 = 4801103) B4801103
theorem B2133823 : Blo 1895435 2133823 := bstep (se 1 (by rfl) ⟨1600367, by rfl⟩ : syracuseStep 2133823 = 3200735) B3200735
theorem B2845097 : Blo 1895435 2845097 := bstep (se 2 (by rfl) ⟨1066911, by rfl⟩ : syracuseStep 2845097 = 2133823) B2133823
theorem B1896731 : Blo 1895435 1896731 := bstep (se 1 (by rfl) ⟨1422548, by rfl⟩ : syracuseStep 1896731 = 2845097) B2845097
theorem B7201669 : Blo 1895435 7201669 := bbase (se 4 (by rfl) ⟨675156, by rfl⟩ : syracuseStep 7201669 = 1350313) (by norm_num)
theorem B9602225 : Blo 1895435 9602225 := bstep (se 2 (by rfl) ⟨3600834, by rfl⟩ : syracuseStep 9602225 = 7201669) B7201669
theorem B6401483 : Blo 1895435 6401483 := bstep (se 1 (by rfl) ⟨4801112, by rfl⟩ : syracuseStep 6401483 = 9602225) B9602225
theorem B4267655 : Blo 1895435 4267655 := bstep (se 1 (by rfl) ⟨3200741, by rfl⟩ : syracuseStep 4267655 = 6401483) B6401483
theorem B2845103 : Blo 1895435 2845103 := bstep (se 1 (by rfl) ⟨2133827, by rfl⟩ : syracuseStep 2845103 = 4267655) B4267655
theorem B1896735 : Blo 1895435 1896735 := bstep (se 1 (by rfl) ⟨1422551, by rfl⟩ : syracuseStep 1896735 = 2845103) B2845103
theorem B2845109 : Blo 1895435 2845109 := bbase (se 5 (by rfl) ⟨133364, by rfl⟩ : syracuseStep 2845109 = 266729) (by norm_num)
theorem B1896739 : Blo 1895435 1896739 := bstep (se 1 (by rfl) ⟨1422554, by rfl⟩ : syracuseStep 1896739 = 2845109) B2845109
theorem B4801133 : Blo 1895435 4801133 := bbase (se 3 (by rfl) ⟨900212, by rfl⟩ : syracuseStep 4801133 = 1800425) (by norm_num)
theorem B3200755 : Blo 1895435 3200755 := bstep (se 1 (by rfl) ⟨2400566, by rfl⟩ : syracuseStep 3200755 = 4801133) B4801133
theorem B4267673 : Blo 1895435 4267673 := bstep (se 2 (by rfl) ⟨1600377, by rfl⟩ : syracuseStep 4267673 = 3200755) B3200755
theorem B2845115 : Blo 1895435 2845115 := bstep (se 1 (by rfl) ⟨2133836, by rfl⟩ : syracuseStep 2845115 = 4267673) B4267673
theorem B1896743 : Blo 1895435 1896743 := bstep (se 1 (by rfl) ⟨1422557, by rfl⟩ : syracuseStep 1896743 = 2845115) B2845115
theorem B2133841 : Blo 1895435 2133841 := bbase (se 2 (by rfl) ⟨800190, by rfl⟩ : syracuseStep 2133841 = 1600381) (by norm_num)
theorem B2845121 : Blo 1895435 2845121 := bstep (se 2 (by rfl) ⟨1066920, by rfl⟩ : syracuseStep 2845121 = 2133841) B2133841
theorem B1896747 : Blo 1895435 1896747 := bstep (se 1 (by rfl) ⟨1422560, by rfl⟩ : syracuseStep 1896747 = 2845121) B2845121
theorem B6836021 : Blo 1895435 6836021 := bbase (se 5 (by rfl) ⟨320438, by rfl⟩ : syracuseStep 6836021 = 640877) (by norm_num)
theorem B4557347 : Blo 1895435 4557347 := bstep (se 1 (by rfl) ⟨3418010, by rfl⟩ : syracuseStep 4557347 = 6836021) B6836021
theorem B3038231 : Blo 1895435 3038231 := bstep (se 1 (by rfl) ⟨2278673, by rfl⟩ : syracuseStep 3038231 = 4557347) B4557347
theorem B2025487 : Blo 1895435 2025487 := bstep (se 1 (by rfl) ⟨1519115, by rfl⟩ : syracuseStep 2025487 = 3038231) B3038231
theorem B2700649 : Blo 1895435 2700649 := bstep (se 2 (by rfl) ⟨1012743, by rfl⟩ : syracuseStep 2700649 = 2025487) B2025487
theorem B3600865 : Blo 1895435 3600865 := bstep (se 2 (by rfl) ⟨1350324, by rfl⟩ : syracuseStep 3600865 = 2700649) B2700649
theorem B4801153 : Blo 1895435 4801153 := bstep (se 2 (by rfl) ⟨1800432, by rfl⟩ : syracuseStep 4801153 = 3600865) B3600865
theorem B6401537 : Blo 1895435 6401537 := bstep (se 2 (by rfl) ⟨2400576, by rfl⟩ : syracuseStep 6401537 = 4801153) B4801153
theorem B4267691 : Blo 1895435 4267691 := bstep (se 1 (by rfl) ⟨3200768, by rfl⟩ : syracuseStep 4267691 = 6401537) B6401537
theorem B2845127 : Blo 1895435 2845127 := bstep (se 1 (by rfl) ⟨2133845, by rfl⟩ : syracuseStep 2845127 = 4267691) B4267691
theorem B1896751 : Blo 1895435 1896751 := bstep (se 1 (by rfl) ⟨1422563, by rfl⟩ : syracuseStep 1896751 = 2845127) B2845127
theorem B2845133 : Blo 1895435 2845133 := bbase (se 3 (by rfl) ⟨533462, by rfl⟩ : syracuseStep 2845133 = 1066925) (by norm_num)
theorem B1896755 : Blo 1895435 1896755 := bstep (se 1 (by rfl) ⟨1422566, by rfl⟩ : syracuseStep 1896755 = 2845133) B2845133
theorem B4267709 : Blo 1895435 4267709 := bbase (se 3 (by rfl) ⟨800195, by rfl⟩ : syracuseStep 4267709 = 1600391) (by norm_num)
theorem B2845139 : Blo 1895435 2845139 := bstep (se 1 (by rfl) ⟨2133854, by rfl⟩ : syracuseStep 2845139 = 4267709) B4267709
theorem B1896759 : Blo 1895435 1896759 := bstep (se 1 (by rfl) ⟨1422569, by rfl⟩ : syracuseStep 1896759 = 2845139) B2845139
theorem B3200789 : Blo 1895435 3200789 := bbase (se 6 (by rfl) ⟨75018, by rfl⟩ : syracuseStep 3200789 = 150037) (by norm_num)
theorem B2133859 : Blo 1895435 2133859 := bstep (se 1 (by rfl) ⟨1600394, by rfl⟩ : syracuseStep 2133859 = 3200789) B3200789
theorem B2845145 : Blo 1895435 2845145 := bstep (se 2 (by rfl) ⟨1066929, by rfl⟩ : syracuseStep 2845145 = 2133859) B2133859
theorem B1896763 : Blo 1895435 1896763 := bstep (se 1 (by rfl) ⟨1422572, by rfl⟩ : syracuseStep 1896763 = 2845145) B2845145
theorem B16425109 : Blo 1895435 16425109 := bbase (se 6 (by rfl) ⟨384963, by rfl⟩ : syracuseStep 16425109 = 769927) (by norm_num)
theorem B21900145 : Blo 1895435 21900145 := bstep (se 2 (by rfl) ⟨8212554, by rfl⟩ : syracuseStep 21900145 = 16425109) B16425109
theorem B29200193 : Blo 1895435 29200193 := bstep (se 2 (by rfl) ⟨10950072, by rfl⟩ : syracuseStep 29200193 = 21900145) B21900145
theorem B19466795 : Blo 1895435 19466795 := bstep (se 1 (by rfl) ⟨14600096, by rfl⟩ : syracuseStep 19466795 = 29200193) B29200193
theorem B12977863 : Blo 1895435 12977863 := bstep (se 1 (by rfl) ⟨9733397, by rfl⟩ : syracuseStep 12977863 = 19466795) B19466795
theorem B69215269 : Blo 1895435 69215269 := bstep (se 4 (by rfl) ⟨6488931, by rfl⟩ : syracuseStep 69215269 = 12977863) B12977863
theorem B92287025 : Blo 1895435 92287025 := bstep (se 2 (by rfl) ⟨34607634, by rfl⟩ : syracuseStep 92287025 = 69215269) B69215269
theorem B61524683 : Blo 1895435 61524683 := bstep (se 1 (by rfl) ⟨46143512, by rfl⟩ : syracuseStep 61524683 = 92287025) B92287025
theorem B41016455 : Blo 1895435 41016455 := bstep (se 1 (by rfl) ⟨30762341, by rfl⟩ : syracuseStep 41016455 = 61524683) B61524683
theorem B27344303 : Blo 1895435 27344303 := bstep (se 1 (by rfl) ⟨20508227, by rfl⟩ : syracuseStep 27344303 = 41016455) B41016455
theorem B18229535 : Blo 1895435 18229535 := bstep (se 1 (by rfl) ⟨13672151, by rfl⟩ : syracuseStep 18229535 = 27344303) B27344303
theorem B12153023 : Blo 1895435 12153023 := bstep (se 1 (by rfl) ⟨9114767, by rfl⟩ : syracuseStep 12153023 = 18229535) B18229535
theorem B8102015 : Blo 1895435 8102015 := bstep (se 1 (by rfl) ⟨6076511, by rfl⟩ : syracuseStep 8102015 = 12153023) B12153023
theorem B5401343 : Blo 1895435 5401343 := bstep (se 1 (by rfl) ⟨4051007, by rfl⟩ : syracuseStep 5401343 = 8102015) B8102015
theorem B14403581 : Blo 1895435 14403581 := bstep (se 3 (by rfl) ⟨2700671, by rfl⟩ : syracuseStep 14403581 = 5401343) B5401343
theorem B9602387 : Blo 1895435 9602387 := bstep (se 1 (by rfl) ⟨7201790, by rfl⟩ : syracuseStep 9602387 = 14403581) B14403581
theorem B6401591 : Blo 1895435 6401591 := bstep (se 1 (by rfl) ⟨4801193, by rfl⟩ : syracuseStep 6401591 = 9602387) B9602387
theorem B4267727 : Blo 1895435 4267727 := bstep (se 1 (by rfl) ⟨3200795, by rfl⟩ : syracuseStep 4267727 = 6401591) B6401591
theorem B2845151 : Blo 1895435 2845151 := bstep (se 1 (by rfl) ⟨2133863, by rfl⟩ : syracuseStep 2845151 = 4267727) B4267727
theorem B1896767 : Blo 1895435 1896767 := bstep (se 1 (by rfl) ⟨1422575, by rfl⟩ : syracuseStep 1896767 = 2845151) B2845151
theorem B2845157 : Blo 1895435 2845157 := bbase (se 4 (by rfl) ⟨266733, by rfl⟩ : syracuseStep 2845157 = 533467) (by norm_num)
theorem B1896771 : Blo 1895435 1896771 := bstep (se 1 (by rfl) ⟨1422578, by rfl⟩ : syracuseStep 1896771 = 2845157) B2845157
theorem B12153077 : Blo 1895435 12153077 := bbase (se 5 (by rfl) ⟨569675, by rfl⟩ : syracuseStep 12153077 = 1139351) (by norm_num)
theorem B8102051 : Blo 1895435 8102051 := bstep (se 1 (by rfl) ⟨6076538, by rfl⟩ : syracuseStep 8102051 = 12153077) B12153077
theorem B5401367 : Blo 1895435 5401367 := bstep (se 1 (by rfl) ⟨4051025, by rfl⟩ : syracuseStep 5401367 = 8102051) B8102051
theorem B3600911 : Blo 1895435 3600911 := bstep (se 1 (by rfl) ⟨2700683, by rfl⟩ : syracuseStep 3600911 = 5401367) B5401367
theorem B2400607 : Blo 1895435 2400607 := bstep (se 1 (by rfl) ⟨1800455, by rfl⟩ : syracuseStep 2400607 = 3600911) B3600911
theorem B3200809 : Blo 1895435 3200809 := bstep (se 2 (by rfl) ⟨1200303, by rfl⟩ : syracuseStep 3200809 = 2400607) B2400607
theorem B4267745 : Blo 1895435 4267745 := bstep (se 2 (by rfl) ⟨1600404, by rfl⟩ : syracuseStep 4267745 = 3200809) B3200809
theorem B2845163 : Blo 1895435 2845163 := bstep (se 1 (by rfl) ⟨2133872, by rfl⟩ : syracuseStep 2845163 = 4267745) B4267745
theorem B1896775 : Blo 1895435 1896775 := bstep (se 1 (by rfl) ⟨1422581, by rfl⟩ : syracuseStep 1896775 = 2845163) B2845163
theorem B2133877 : Blo 1895435 2133877 := bbase (se 5 (by rfl) ⟨100025, by rfl⟩ : syracuseStep 2133877 = 200051) (by norm_num)
theorem B2845169 : Blo 1895435 2845169 := bstep (se 2 (by rfl) ⟨1066938, by rfl⟩ : syracuseStep 2845169 = 2133877) B2133877
theorem B1896779 : Blo 1895435 1896779 := bstep (se 1 (by rfl) ⟨1422584, by rfl⟩ : syracuseStep 1896779 = 2845169) B2845169
theorem B2400617 : Blo 1895435 2400617 := bbase (se 2 (by rfl) ⟨900231, by rfl⟩ : syracuseStep 2400617 = 1800463) (by norm_num)
theorem B6401645 : Blo 1895435 6401645 := bstep (se 3 (by rfl) ⟨1200308, by rfl⟩ : syracuseStep 6401645 = 2400617) B2400617
theorem B4267763 : Blo 1895435 4267763 := bstep (se 1 (by rfl) ⟨3200822, by rfl⟩ : syracuseStep 4267763 = 6401645) B6401645
theorem B2845175 : Blo 1895435 2845175 := bstep (se 1 (by rfl) ⟨2133881, by rfl⟩ : syracuseStep 2845175 = 4267763) B4267763
theorem B1896783 : Blo 1895435 1896783 := bstep (se 1 (by rfl) ⟨1422587, by rfl⟩ : syracuseStep 1896783 = 2845175) B2845175
theorem B2845181 : Blo 1895435 2845181 := bbase (se 3 (by rfl) ⟨533471, by rfl⟩ : syracuseStep 2845181 = 1066943) (by norm_num)
theorem B1896787 : Blo 1895435 1896787 := bstep (se 1 (by rfl) ⟨1422590, by rfl⟩ : syracuseStep 1896787 = 2845181) B2845181
theorem B4267781 : Blo 1895435 4267781 := bbase (se 4 (by rfl) ⟨400104, by rfl⟩ : syracuseStep 4267781 = 800209) (by norm_num)
theorem B2845187 : Blo 1895435 2845187 := bstep (se 1 (by rfl) ⟨2133890, by rfl⟩ : syracuseStep 2845187 = 4267781) B4267781
theorem B1896791 : Blo 1895435 1896791 := bstep (se 1 (by rfl) ⟨1422593, by rfl⟩ : syracuseStep 1896791 = 2845187) B2845187
theorem B3600949 : Blo 1895435 3600949 := bbase (se 5 (by rfl) ⟨168794, by rfl⟩ : syracuseStep 3600949 = 337589) (by norm_num)
theorem B4801265 : Blo 1895435 4801265 := bstep (se 2 (by rfl) ⟨1800474, by rfl⟩ : syracuseStep 4801265 = 3600949) B3600949
theorem B3200843 : Blo 1895435 3200843 := bstep (se 1 (by rfl) ⟨2400632, by rfl⟩ : syracuseStep 3200843 = 4801265) B4801265
theorem B2133895 : Blo 1895435 2133895 := bstep (se 1 (by rfl) ⟨1600421, by rfl⟩ : syracuseStep 2133895 = 3200843) B3200843
theorem B2845193 : Blo 1895435 2845193 := bstep (se 2 (by rfl) ⟨1066947, by rfl⟩ : syracuseStep 2845193 = 2133895) B2133895
theorem B1896795 : Blo 1895435 1896795 := bstep (se 1 (by rfl) ⟨1422596, by rfl⟩ : syracuseStep 1896795 = 2845193) B2845193
theorem B9602549 : Blo 1895435 9602549 := bbase (se 5 (by rfl) ⟨450119, by rfl⟩ : syracuseStep 9602549 = 900239) (by norm_num)
theorem B6401699 : Blo 1895435 6401699 := bstep (se 1 (by rfl) ⟨4801274, by rfl⟩ : syracuseStep 6401699 = 9602549) B9602549
theorem B4267799 : Blo 1895435 4267799 := bstep (se 1 (by rfl) ⟨3200849, by rfl⟩ : syracuseStep 4267799 = 6401699) B6401699
theorem B2845199 : Blo 1895435 2845199 := bstep (se 1 (by rfl) ⟨2133899, by rfl⟩ : syracuseStep 2845199 = 4267799) B4267799
theorem B1896799 : Blo 1895435 1896799 := bstep (se 1 (by rfl) ⟨1422599, by rfl⟩ : syracuseStep 1896799 = 2845199) B2845199
theorem B2845205 : Blo 1895435 2845205 := bbase (se 6 (by rfl) ⟨66684, by rfl⟩ : syracuseStep 2845205 = 133369) (by norm_num)
theorem B1896803 : Blo 1895435 1896803 := bstep (se 1 (by rfl) ⟨1422602, by rfl⟩ : syracuseStep 1896803 = 2845205) B2845205
theorem B16204373 : Blo 1895435 16204373 := bbase (se 8 (by rfl) ⟨94947, by rfl⟩ : syracuseStep 16204373 = 189895) (by norm_num)
theorem B10802915 : Blo 1895435 10802915 := bstep (se 1 (by rfl) ⟨8102186, by rfl⟩ : syracuseStep 10802915 = 16204373) B16204373
theorem B7201943 : Blo 1895435 7201943 := bstep (se 1 (by rfl) ⟨5401457, by rfl⟩ : syracuseStep 7201943 = 10802915) B10802915
theorem B4801295 : Blo 1895435 4801295 := bstep (se 1 (by rfl) ⟨3600971, by rfl⟩ : syracuseStep 4801295 = 7201943) B7201943
theorem B3200863 : Blo 1895435 3200863 := bstep (se 1 (by rfl) ⟨2400647, by rfl⟩ : syracuseStep 3200863 = 4801295) B4801295
theorem B4267817 : Blo 1895435 4267817 := bstep (se 2 (by rfl) ⟨1600431, by rfl⟩ : syracuseStep 4267817 = 3200863) B3200863
theorem B2845211 : Blo 1895435 2845211 := bstep (se 1 (by rfl) ⟨2133908, by rfl⟩ : syracuseStep 2845211 = 4267817) B4267817
theorem B1896807 : Blo 1895435 1896807 := bstep (se 1 (by rfl) ⟨1422605, by rfl⟩ : syracuseStep 1896807 = 2845211) B2845211
theorem B2133913 : Blo 1895435 2133913 := bbase (se 2 (by rfl) ⟨800217, by rfl⟩ : syracuseStep 2133913 = 1600435) (by norm_num)
theorem B2845217 : Blo 1895435 2845217 := bstep (se 2 (by rfl) ⟨1066956, by rfl⟩ : syracuseStep 2845217 = 2133913) B2133913
theorem B1896811 : Blo 1895435 1896811 := bstep (se 1 (by rfl) ⟨1422608, by rfl⟩ : syracuseStep 1896811 = 2845217) B2845217
theorem B7201973 : Blo 1895435 7201973 := bbase (se 5 (by rfl) ⟨337592, by rfl⟩ : syracuseStep 7201973 = 675185) (by norm_num)
theorem B4801315 : Blo 1895435 4801315 := bstep (se 1 (by rfl) ⟨3600986, by rfl⟩ : syracuseStep 4801315 = 7201973) B7201973
theorem B6401753 : Blo 1895435 6401753 := bstep (se 2 (by rfl) ⟨2400657, by rfl⟩ : syracuseStep 6401753 = 4801315) B4801315
theorem B4267835 : Blo 1895435 4267835 := bstep (se 1 (by rfl) ⟨3200876, by rfl⟩ : syracuseStep 4267835 = 6401753) B6401753
theorem B2845223 : Blo 1895435 2845223 := bstep (se 1 (by rfl) ⟨2133917, by rfl⟩ : syracuseStep 2845223 = 4267835) B4267835
theorem B1896815 : Blo 1895435 1896815 := bstep (se 1 (by rfl) ⟨1422611, by rfl⟩ : syracuseStep 1896815 = 2845223) B2845223
theorem B2845229 : Blo 1895435 2845229 := bbase (se 3 (by rfl) ⟨533480, by rfl⟩ : syracuseStep 2845229 = 1066961) (by norm_num)
theorem B1896819 : Blo 1895435 1896819 := bstep (se 1 (by rfl) ⟨1422614, by rfl⟩ : syracuseStep 1896819 = 2845229) B2845229
theorem B4267853 : Blo 1895435 4267853 := bbase (se 3 (by rfl) ⟨800222, by rfl⟩ : syracuseStep 4267853 = 1600445) (by norm_num)
theorem B2845235 : Blo 1895435 2845235 := bstep (se 1 (by rfl) ⟨2133926, by rfl⟩ : syracuseStep 2845235 = 4267853) B4267853
theorem B1896823 : Blo 1895435 1896823 := bstep (se 1 (by rfl) ⟨1422617, by rfl⟩ : syracuseStep 1896823 = 2845235) B2845235
theorem B2400673 : Blo 1895435 2400673 := bbase (se 2 (by rfl) ⟨900252, by rfl⟩ : syracuseStep 2400673 = 1800505) (by norm_num)
theorem B3200897 : Blo 1895435 3200897 := bstep (se 2 (by rfl) ⟨1200336, by rfl⟩ : syracuseStep 3200897 = 2400673) B2400673
theorem B2133931 : Blo 1895435 2133931 := bstep (se 1 (by rfl) ⟨1600448, by rfl⟩ : syracuseStep 2133931 = 3200897) B3200897
theorem B2845241 : Blo 1895435 2845241 := bstep (se 2 (by rfl) ⟨1066965, by rfl⟩ : syracuseStep 2845241 = 2133931) B2133931
theorem B1896827 : Blo 1895435 1896827 := bstep (se 1 (by rfl) ⟨1422620, by rfl⟩ : syracuseStep 1896827 = 2845241) B2845241
theorem B21606101 : Blo 1895435 21606101 := bbase (se 7 (by rfl) ⟨253196, by rfl⟩ : syracuseStep 21606101 = 506393) (by norm_num)
theorem B14404067 : Blo 1895435 14404067 := bstep (se 1 (by rfl) ⟨10803050, by rfl⟩ : syracuseStep 14404067 = 21606101) B21606101
theorem B9602711 : Blo 1895435 9602711 := bstep (se 1 (by rfl) ⟨7202033, by rfl⟩ : syracuseStep 9602711 = 14404067) B14404067
theorem B6401807 : Blo 1895435 6401807 := bstep (se 1 (by rfl) ⟨4801355, by rfl⟩ : syracuseStep 6401807 = 9602711) B9602711
theorem B4267871 : Blo 1895435 4267871 := bstep (se 1 (by rfl) ⟨3200903, by rfl⟩ : syracuseStep 4267871 = 6401807) B6401807
theorem B2845247 : Blo 1895435 2845247 := bstep (se 1 (by rfl) ⟨2133935, by rfl⟩ : syracuseStep 2845247 = 4267871) B4267871
theorem B1896831 : Blo 1895435 1896831 := bstep (se 1 (by rfl) ⟨1422623, by rfl⟩ : syracuseStep 1896831 = 2845247) B2845247
theorem B2845253 : Blo 1895435 2845253 := bbase (se 4 (by rfl) ⟨266742, by rfl⟩ : syracuseStep 2845253 = 533485) (by norm_num)
theorem B1896835 : Blo 1895435 1896835 := bstep (se 1 (by rfl) ⟨1422626, by rfl⟩ : syracuseStep 1896835 = 2845253) B2845253
theorem B3200917 : Blo 1895435 3200917 := bbase (se 6 (by rfl) ⟨75021, by rfl⟩ : syracuseStep 3200917 = 150043) (by norm_num)
theorem B4267889 : Blo 1895435 4267889 := bstep (se 2 (by rfl) ⟨1600458, by rfl⟩ : syracuseStep 4267889 = 3200917) B3200917
theorem B2845259 : Blo 1895435 2845259 := bstep (se 1 (by rfl) ⟨2133944, by rfl⟩ : syracuseStep 2845259 = 4267889) B4267889
theorem B1896839 : Blo 1895435 1896839 := bstep (se 1 (by rfl) ⟨1422629, by rfl⟩ : syracuseStep 1896839 = 2845259) B2845259
theorem B2133949 : Blo 1895435 2133949 := bbase (se 3 (by rfl) ⟨400115, by rfl⟩ : syracuseStep 2133949 = 800231) (by norm_num)
theorem B2845265 : Blo 1895435 2845265 := bstep (se 2 (by rfl) ⟨1066974, by rfl⟩ : syracuseStep 2845265 = 2133949) B2133949
theorem B1896843 : Blo 1895435 1896843 := bstep (se 1 (by rfl) ⟨1422632, by rfl⟩ : syracuseStep 1896843 = 2845265) B2845265
theorem B6401861 : Blo 1895435 6401861 := bbase (se 4 (by rfl) ⟨600174, by rfl⟩ : syracuseStep 6401861 = 1200349) (by norm_num)
theorem B4267907 : Blo 1895435 4267907 := bstep (se 1 (by rfl) ⟨3200930, by rfl⟩ : syracuseStep 4267907 = 6401861) B6401861
theorem B2845271 : Blo 1895435 2845271 := bstep (se 1 (by rfl) ⟨2133953, by rfl⟩ : syracuseStep 2845271 = 4267907) B4267907
theorem B1896847 : Blo 1895435 1896847 := bstep (se 1 (by rfl) ⟨1422635, by rfl⟩ : syracuseStep 1896847 = 2845271) B2845271
theorem B2845277 : Blo 1895435 2845277 := bbase (se 3 (by rfl) ⟨533489, by rfl⟩ : syracuseStep 2845277 = 1066979) (by norm_num)
theorem B1896851 : Blo 1895435 1896851 := bstep (se 1 (by rfl) ⟨1422638, by rfl⟩ : syracuseStep 1896851 = 2845277) B2845277
theorem B4267925 : Blo 1895435 4267925 := bbase (se 6 (by rfl) ⟨100029, by rfl⟩ : syracuseStep 4267925 = 200059) (by norm_num)
theorem B2845283 : Blo 1895435 2845283 := bstep (se 1 (by rfl) ⟨2133962, by rfl⟩ : syracuseStep 2845283 = 4267925) B4267925
theorem B1896855 : Blo 1895435 1896855 := bstep (se 1 (by rfl) ⟨1422641, by rfl⟩ : syracuseStep 1896855 = 2845283) B2845283
theorem B4051205 : Blo 1895435 4051205 := bbase (se 4 (by rfl) ⟨379800, by rfl⟩ : syracuseStep 4051205 = 759601) (by norm_num)
theorem B2700803 : Blo 1895435 2700803 := bstep (se 1 (by rfl) ⟨2025602, by rfl⟩ : syracuseStep 2700803 = 4051205) B4051205
theorem B7202141 : Blo 1895435 7202141 := bstep (se 3 (by rfl) ⟨1350401, by rfl⟩ : syracuseStep 7202141 = 2700803) B2700803
theorem B4801427 : Blo 1895435 4801427 := bstep (se 1 (by rfl) ⟨3601070, by rfl⟩ : syracuseStep 4801427 = 7202141) B7202141
theorem B3200951 : Blo 1895435 3200951 := bstep (se 1 (by rfl) ⟨2400713, by rfl⟩ : syracuseStep 3200951 = 4801427) B4801427
theorem B2133967 : Blo 1895435 2133967 := bstep (se 1 (by rfl) ⟨1600475, by rfl⟩ : syracuseStep 2133967 = 3200951) B3200951
theorem B2845289 : Blo 1895435 2845289 := bstep (se 2 (by rfl) ⟨1066983, by rfl⟩ : syracuseStep 2845289 = 2133967) B2133967
theorem B1896859 : Blo 1895435 1896859 := bstep (se 1 (by rfl) ⟨1422644, by rfl⟩ : syracuseStep 1896859 = 2845289) B2845289
theorem B5127317 : Blo 1895435 5127317 := bbase (se 6 (by rfl) ⟨120171, by rfl⟩ : syracuseStep 5127317 = 240343) (by norm_num)
theorem B3418211 : Blo 1895435 3418211 := bstep (se 1 (by rfl) ⟨2563658, by rfl⟩ : syracuseStep 3418211 = 5127317) B5127317
theorem B9115229 : Blo 1895435 9115229 := bstep (se 3 (by rfl) ⟨1709105, by rfl⟩ : syracuseStep 9115229 = 3418211) B3418211
theorem B6076819 : Blo 1895435 6076819 := bstep (se 1 (by rfl) ⟨4557614, by rfl⟩ : syracuseStep 6076819 = 9115229) B9115229
theorem B8102425 : Blo 1895435 8102425 := bstep (se 2 (by rfl) ⟨3038409, by rfl⟩ : syracuseStep 8102425 = 6076819) B6076819
theorem B10803233 : Blo 1895435 10803233 := bstep (se 2 (by rfl) ⟨4051212, by rfl⟩ : syracuseStep 10803233 = 8102425) B8102425
theorem B7202155 : Blo 1895435 7202155 := bstep (se 1 (by rfl) ⟨5401616, by rfl⟩ : syracuseStep 7202155 = 10803233) B10803233
theorem B9602873 : Blo 1895435 9602873 := bstep (se 2 (by rfl) ⟨3601077, by rfl⟩ : syracuseStep 9602873 = 7202155) B7202155
theorem B6401915 : Blo 1895435 6401915 := bstep (se 1 (by rfl) ⟨4801436, by rfl⟩ : syracuseStep 6401915 = 9602873) B9602873
theorem B4267943 : Blo 1895435 4267943 := bstep (se 1 (by rfl) ⟨3200957, by rfl⟩ : syracuseStep 4267943 = 6401915) B6401915
theorem B2845295 : Blo 1895435 2845295 := bstep (se 1 (by rfl) ⟨2133971, by rfl⟩ : syracuseStep 2845295 = 4267943) B4267943
theorem B1896863 : Blo 1895435 1896863 := bstep (se 1 (by rfl) ⟨1422647, by rfl⟩ : syracuseStep 1896863 = 2845295) B2845295
theorem B2845301 : Blo 1895435 2845301 := bbase (se 5 (by rfl) ⟨133373, by rfl⟩ : syracuseStep 2845301 = 266747) (by norm_num)
theorem B1896867 : Blo 1895435 1896867 := bstep (se 1 (by rfl) ⟨1422650, by rfl⟩ : syracuseStep 1896867 = 2845301) B2845301
theorem B3601093 : Blo 1895435 3601093 := bbase (se 4 (by rfl) ⟨337602, by rfl⟩ : syracuseStep 3601093 = 675205) (by norm_num)
theorem B4801457 : Blo 1895435 4801457 := bstep (se 2 (by rfl) ⟨1800546, by rfl⟩ : syracuseStep 4801457 = 3601093) B3601093
theorem B3200971 : Blo 1895435 3200971 := bstep (se 1 (by rfl) ⟨2400728, by rfl⟩ : syracuseStep 3200971 = 4801457) B4801457
theorem B4267961 : Blo 1895435 4267961 := bstep (se 2 (by rfl) ⟨1600485, by rfl⟩ : syracuseStep 4267961 = 3200971) B3200971
theorem B2845307 : Blo 1895435 2845307 := bstep (se 1 (by rfl) ⟨2133980, by rfl⟩ : syracuseStep 2845307 = 4267961) B4267961
theorem B1896871 : Blo 1895435 1896871 := bstep (se 1 (by rfl) ⟨1422653, by rfl⟩ : syracuseStep 1896871 = 2845307) B2845307
theorem B2133985 : Blo 1895435 2133985 := bbase (se 2 (by rfl) ⟨800244, by rfl⟩ : syracuseStep 2133985 = 1600489) (by norm_num)
theorem B2845313 : Blo 1895435 2845313 := bstep (se 2 (by rfl) ⟨1066992, by rfl⟩ : syracuseStep 2845313 = 2133985) B2133985
theorem B1896875 : Blo 1895435 1896875 := bstep (se 1 (by rfl) ⟨1422656, by rfl⟩ : syracuseStep 1896875 = 2845313) B2845313
theorem B4801477 : Blo 1895435 4801477 := bbase (se 4 (by rfl) ⟨450138, by rfl⟩ : syracuseStep 4801477 = 900277) (by norm_num)
theorem B6401969 : Blo 1895435 6401969 := bstep (se 2 (by rfl) ⟨2400738, by rfl⟩ : syracuseStep 6401969 = 4801477) B4801477
theorem B4267979 : Blo 1895435 4267979 := bstep (se 1 (by rfl) ⟨3200984, by rfl⟩ : syracuseStep 4267979 = 6401969) B6401969
theorem B2845319 : Blo 1895435 2845319 := bstep (se 1 (by rfl) ⟨2133989, by rfl⟩ : syracuseStep 2845319 = 4267979) B4267979
theorem B1896879 : Blo 1895435 1896879 := bstep (se 1 (by rfl) ⟨1422659, by rfl⟩ : syracuseStep 1896879 = 2845319) B2845319
theorem B2845325 : Blo 1895435 2845325 := bbase (se 3 (by rfl) ⟨533498, by rfl⟩ : syracuseStep 2845325 = 1066997) (by norm_num)
theorem B1896883 : Blo 1895435 1896883 := bstep (se 1 (by rfl) ⟨1422662, by rfl⟩ : syracuseStep 1896883 = 2845325) B2845325
theorem B4267997 : Blo 1895435 4267997 := bbase (se 3 (by rfl) ⟨800249, by rfl⟩ : syracuseStep 4267997 = 1600499) (by norm_num)
theorem B2845331 : Blo 1895435 2845331 := bstep (se 1 (by rfl) ⟨2133998, by rfl⟩ : syracuseStep 2845331 = 4267997) B4267997
theorem B1896887 : Blo 1895435 1896887 := bstep (se 1 (by rfl) ⟨1422665, by rfl⟩ : syracuseStep 1896887 = 2845331) B2845331
theorem B3201005 : Blo 1895435 3201005 := bbase (se 3 (by rfl) ⟨600188, by rfl⟩ : syracuseStep 3201005 = 1200377) (by norm_num)
theorem B2134003 : Blo 1895435 2134003 := bstep (se 1 (by rfl) ⟨1600502, by rfl⟩ : syracuseStep 2134003 = 3201005) B3201005
theorem B2845337 : Blo 1895435 2845337 := bstep (se 2 (by rfl) ⟨1067001, by rfl⟩ : syracuseStep 2845337 = 2134003) B2134003
theorem B1896891 : Blo 1895435 1896891 := bstep (se 1 (by rfl) ⟨1422668, by rfl⟩ : syracuseStep 1896891 = 2845337) B2845337
theorem B9365813 : Blo 1895435 9365813 := bbase (se 5 (by rfl) ⟨439022, by rfl⟩ : syracuseStep 9365813 = 878045) (by norm_num)
theorem B6243875 : Blo 1895435 6243875 := bstep (se 1 (by rfl) ⟨4682906, by rfl⟩ : syracuseStep 6243875 = 9365813) B9365813
theorem B4162583 : Blo 1895435 4162583 := bstep (se 1 (by rfl) ⟨3121937, by rfl⟩ : syracuseStep 4162583 = 6243875) B6243875
theorem B11100221 : Blo 1895435 11100221 := bstep (se 3 (by rfl) ⟨2081291, by rfl⟩ : syracuseStep 11100221 = 4162583) B4162583
theorem B473609429 : Blo 1895435 473609429 := bstep (se 7 (by rfl) ⟨5550110, by rfl⟩ : syracuseStep 473609429 = 11100221) B11100221
theorem B315739619 : Blo 1895435 315739619 := bstep (se 1 (by rfl) ⟨236804714, by rfl⟩ : syracuseStep 315739619 = 473609429) B473609429
theorem B210493079 : Blo 1895435 210493079 := bstep (se 1 (by rfl) ⟨157869809, by rfl⟩ : syracuseStep 210493079 = 315739619) B315739619
theorem B140328719 : Blo 1895435 140328719 := bstep (se 1 (by rfl) ⟨105246539, by rfl⟩ : syracuseStep 140328719 = 210493079) B210493079
theorem B93552479 : Blo 1895435 93552479 := bstep (se 1 (by rfl) ⟨70164359, by rfl⟩ : syracuseStep 93552479 = 140328719) B140328719
theorem B62368319 : Blo 1895435 62368319 := bstep (se 1 (by rfl) ⟨46776239, by rfl⟩ : syracuseStep 62368319 = 93552479) B93552479
theorem B41578879 : Blo 1895435 41578879 := bstep (se 1 (by rfl) ⟨31184159, by rfl⟩ : syracuseStep 41578879 = 62368319) B62368319
theorem B55438505 : Blo 1895435 55438505 := bstep (se 2 (by rfl) ⟨20789439, by rfl⟩ : syracuseStep 55438505 = 41578879) B41578879
theorem B36959003 : Blo 1895435 36959003 := bstep (se 1 (by rfl) ⟨27719252, by rfl⟩ : syracuseStep 36959003 = 55438505) B55438505
theorem B24639335 : Blo 1895435 24639335 := bstep (se 1 (by rfl) ⟨18479501, by rfl⟩ : syracuseStep 24639335 = 36959003) B36959003
theorem B16426223 : Blo 1895435 16426223 := bstep (se 1 (by rfl) ⟨12319667, by rfl⟩ : syracuseStep 16426223 = 24639335) B24639335
theorem B10950815 : Blo 1895435 10950815 := bstep (se 1 (by rfl) ⟨8213111, by rfl⟩ : syracuseStep 10950815 = 16426223) B16426223
theorem B7300543 : Blo 1895435 7300543 := bstep (se 1 (by rfl) ⟨5475407, by rfl⟩ : syracuseStep 7300543 = 10950815) B10950815
theorem B9734057 : Blo 1895435 9734057 := bstep (se 2 (by rfl) ⟨3650271, by rfl⟩ : syracuseStep 9734057 = 7300543) B7300543
theorem B6489371 : Blo 1895435 6489371 := bstep (se 1 (by rfl) ⟨4867028, by rfl⟩ : syracuseStep 6489371 = 9734057) B9734057
theorem B4326247 : Blo 1895435 4326247 := bstep (se 1 (by rfl) ⟨3244685, by rfl⟩ : syracuseStep 4326247 = 6489371) B6489371
theorem B5768329 : Blo 1895435 5768329 := bstep (se 2 (by rfl) ⟨2163123, by rfl⟩ : syracuseStep 5768329 = 4326247) B4326247
theorem B7691105 : Blo 1895435 7691105 := bstep (se 2 (by rfl) ⟨2884164, by rfl⟩ : syracuseStep 7691105 = 5768329) B5768329
theorem B5127403 : Blo 1895435 5127403 := bstep (se 1 (by rfl) ⟨3845552, by rfl⟩ : syracuseStep 5127403 = 7691105) B7691105
theorem B6836537 : Blo 1895435 6836537 := bstep (se 2 (by rfl) ⟨2563701, by rfl⟩ : syracuseStep 6836537 = 5127403) B5127403
theorem B4557691 : Blo 1895435 4557691 := bstep (se 1 (by rfl) ⟨3418268, by rfl⟩ : syracuseStep 4557691 = 6836537) B6836537
theorem B24307685 : Blo 1895435 24307685 := bstep (se 4 (by rfl) ⟨2278845, by rfl⟩ : syracuseStep 24307685 = 4557691) B4557691
theorem B16205123 : Blo 1895435 16205123 := bstep (se 1 (by rfl) ⟨12153842, by rfl⟩ : syracuseStep 16205123 = 24307685) B24307685
theorem B10803415 : Blo 1895435 10803415 := bstep (se 1 (by rfl) ⟨8102561, by rfl⟩ : syracuseStep 10803415 = 16205123) B16205123
theorem B14404553 : Blo 1895435 14404553 := bstep (se 2 (by rfl) ⟨5401707, by rfl⟩ : syracuseStep 14404553 = 10803415) B10803415
theorem B9603035 : Blo 1895435 9603035 := bstep (se 1 (by rfl) ⟨7202276, by rfl⟩ : syracuseStep 9603035 = 14404553) B14404553
theorem B6402023 : Blo 1895435 6402023 := bstep (se 1 (by rfl) ⟨4801517, by rfl⟩ : syracuseStep 6402023 = 9603035) B9603035
theorem B4268015 : Blo 1895435 4268015 := bstep (se 1 (by rfl) ⟨3201011, by rfl⟩ : syracuseStep 4268015 = 6402023) B6402023
theorem B2845343 : Blo 1895435 2845343 := bstep (se 1 (by rfl) ⟨2134007, by rfl⟩ : syracuseStep 2845343 = 4268015) B4268015
theorem B1896895 : Blo 1895435 1896895 := bstep (se 1 (by rfl) ⟨1422671, by rfl⟩ : syracuseStep 1896895 = 2845343) B2845343
theorem B2845349 : Blo 1895435 2845349 := bbase (se 4 (by rfl) ⟨266751, by rfl⟩ : syracuseStep 2845349 = 533503) (by norm_num)
theorem B1896899 : Blo 1895435 1896899 := bstep (se 1 (by rfl) ⟨1422674, by rfl⟩ : syracuseStep 1896899 = 2845349) B2845349
theorem B2400769 : Blo 1895435 2400769 := bbase (se 2 (by rfl) ⟨900288, by rfl⟩ : syracuseStep 2400769 = 1800577) (by norm_num)
theorem B3201025 : Blo 1895435 3201025 := bstep (se 2 (by rfl) ⟨1200384, by rfl⟩ : syracuseStep 3201025 = 2400769) B2400769
theorem B4268033 : Blo 1895435 4268033 := bstep (se 2 (by rfl) ⟨1600512, by rfl⟩ : syracuseStep 4268033 = 3201025) B3201025
theorem B2845355 : Blo 1895435 2845355 := bstep (se 1 (by rfl) ⟨2134016, by rfl⟩ : syracuseStep 2845355 = 4268033) B4268033
theorem B1896903 : Blo 1895435 1896903 := bstep (se 1 (by rfl) ⟨1422677, by rfl⟩ : syracuseStep 1896903 = 2845355) B2845355
theorem B2134021 : Blo 1895435 2134021 := bbase (se 4 (by rfl) ⟨200064, by rfl⟩ : syracuseStep 2134021 = 400129) (by norm_num)
theorem B2845361 : Blo 1895435 2845361 := bstep (se 2 (by rfl) ⟨1067010, by rfl⟩ : syracuseStep 2845361 = 2134021) B2134021
theorem B1896907 : Blo 1895435 1896907 := bstep (se 1 (by rfl) ⟨1422680, by rfl⟩ : syracuseStep 1896907 = 2845361) B2845361
theorem B2700877 : Blo 1895435 2700877 := bbase (se 3 (by rfl) ⟨506414, by rfl⟩ : syracuseStep 2700877 = 1012829) (by norm_num)
theorem B3601169 : Blo 1895435 3601169 := bstep (se 2 (by rfl) ⟨1350438, by rfl⟩ : syracuseStep 3601169 = 2700877) B2700877
theorem B2400779 : Blo 1895435 2400779 := bstep (se 1 (by rfl) ⟨1800584, by rfl⟩ : syracuseStep 2400779 = 3601169) B3601169
theorem B6402077 : Blo 1895435 6402077 := bstep (se 3 (by rfl) ⟨1200389, by rfl⟩ : syracuseStep 6402077 = 2400779) B2400779
theorem B4268051 : Blo 1895435 4268051 := bstep (se 1 (by rfl) ⟨3201038, by rfl⟩ : syracuseStep 4268051 = 6402077) B6402077
theorem B2845367 : Blo 1895435 2845367 := bstep (se 1 (by rfl) ⟨2134025, by rfl⟩ : syracuseStep 2845367 = 4268051) B4268051
theorem B1896911 : Blo 1895435 1896911 := bstep (se 1 (by rfl) ⟨1422683, by rfl⟩ : syracuseStep 1896911 = 2845367) B2845367
theorem B2845373 : Blo 1895435 2845373 := bbase (se 3 (by rfl) ⟨533507, by rfl⟩ : syracuseStep 2845373 = 1067015) (by norm_num)
theorem B1896915 : Blo 1895435 1896915 := bstep (se 1 (by rfl) ⟨1422686, by rfl⟩ : syracuseStep 1896915 = 2845373) B2845373
theorem B4268069 : Blo 1895435 4268069 := bbase (se 4 (by rfl) ⟨400131, by rfl⟩ : syracuseStep 4268069 = 800263) (by norm_num)
theorem B2845379 : Blo 1895435 2845379 := bstep (se 1 (by rfl) ⟨2134034, by rfl⟩ : syracuseStep 2845379 = 4268069) B4268069
theorem B1896919 : Blo 1895435 1896919 := bstep (se 1 (by rfl) ⟨1422689, by rfl⟩ : syracuseStep 1896919 = 2845379) B2845379
theorem B4801589 : Blo 1895435 4801589 := bbase (se 5 (by rfl) ⟨225074, by rfl⟩ : syracuseStep 4801589 = 450149) (by norm_num)
theorem B3201059 : Blo 1895435 3201059 := bstep (se 1 (by rfl) ⟨2400794, by rfl⟩ : syracuseStep 3201059 = 4801589) B4801589
theorem B2134039 : Blo 1895435 2134039 := bstep (se 1 (by rfl) ⟨1600529, by rfl⟩ : syracuseStep 2134039 = 3201059) B3201059
theorem B2845385 : Blo 1895435 2845385 := bstep (se 2 (by rfl) ⟨1067019, by rfl⟩ : syracuseStep 2845385 = 2134039) B2134039
theorem B1896923 : Blo 1895435 1896923 := bstep (se 1 (by rfl) ⟨1422692, by rfl⟩ : syracuseStep 1896923 = 2845385) B2845385
theorem B1922809 : Blo 1895435 1922809 := bbase (se 2 (by rfl) ⟨721053, by rfl⟩ : syracuseStep 1922809 = 1442107) (by norm_num)
theorem B2563745 : Blo 1895435 2563745 := bstep (se 2 (by rfl) ⟨961404, by rfl⟩ : syracuseStep 2563745 = 1922809) B1922809
theorem B6836653 : Blo 1895435 6836653 := bstep (se 3 (by rfl) ⟨1281872, by rfl⟩ : syracuseStep 6836653 = 2563745) B2563745
theorem B9115537 : Blo 1895435 9115537 := bstep (se 2 (by rfl) ⟨3418326, by rfl⟩ : syracuseStep 9115537 = 6836653) B6836653
theorem B12154049 : Blo 1895435 12154049 := bstep (se 2 (by rfl) ⟨4557768, by rfl⟩ : syracuseStep 12154049 = 9115537) B9115537
theorem B8102699 : Blo 1895435 8102699 := bstep (se 1 (by rfl) ⟨6077024, by rfl⟩ : syracuseStep 8102699 = 12154049) B12154049
theorem B5401799 : Blo 1895435 5401799 := bstep (se 1 (by rfl) ⟨4051349, by rfl⟩ : syracuseStep 5401799 = 8102699) B8102699
theorem B3601199 : Blo 1895435 3601199 := bstep (se 1 (by rfl) ⟨2700899, by rfl⟩ : syracuseStep 3601199 = 5401799) B5401799
theorem B9603197 : Blo 1895435 9603197 := bstep (se 3 (by rfl) ⟨1800599, by rfl⟩ : syracuseStep 9603197 = 3601199) B3601199
theorem B6402131 : Blo 1895435 6402131 := bstep (se 1 (by rfl) ⟨4801598, by rfl⟩ : syracuseStep 6402131 = 9603197) B9603197
theorem B4268087 : Blo 1895435 4268087 := bstep (se 1 (by rfl) ⟨3201065, by rfl⟩ : syracuseStep 4268087 = 6402131) B6402131
theorem B2845391 : Blo 1895435 2845391 := bstep (se 1 (by rfl) ⟨2134043, by rfl⟩ : syracuseStep 2845391 = 4268087) B4268087
theorem B1896927 : Blo 1895435 1896927 := bstep (se 1 (by rfl) ⟨1422695, by rfl⟩ : syracuseStep 1896927 = 2845391) B2845391
theorem B2845397 : Blo 1895435 2845397 := bbase (se 7 (by rfl) ⟨33344, by rfl⟩ : syracuseStep 2845397 = 66689) (by norm_num)
theorem B1896931 : Blo 1895435 1896931 := bstep (se 1 (by rfl) ⟨1422698, by rfl⟩ : syracuseStep 1896931 = 2845397) B2845397
theorem B7691269 : Blo 1895435 7691269 := bbase (se 4 (by rfl) ⟨721056, by rfl⟩ : syracuseStep 7691269 = 1442113) (by norm_num)
theorem B10255025 : Blo 1895435 10255025 := bstep (se 2 (by rfl) ⟨3845634, by rfl⟩ : syracuseStep 10255025 = 7691269) B7691269
theorem B6836683 : Blo 1895435 6836683 := bstep (se 1 (by rfl) ⟨5127512, by rfl⟩ : syracuseStep 6836683 = 10255025) B10255025
theorem B9115577 : Blo 1895435 9115577 := bstep (se 2 (by rfl) ⟨3418341, by rfl⟩ : syracuseStep 9115577 = 6836683) B6836683
theorem B6077051 : Blo 1895435 6077051 := bstep (se 1 (by rfl) ⟨4557788, by rfl⟩ : syracuseStep 6077051 = 9115577) B9115577
theorem B4051367 : Blo 1895435 4051367 := bstep (se 1 (by rfl) ⟨3038525, by rfl⟩ : syracuseStep 4051367 = 6077051) B6077051
theorem B2700911 : Blo 1895435 2700911 := bstep (se 1 (by rfl) ⟨2025683, by rfl⟩ : syracuseStep 2700911 = 4051367) B4051367
theorem B7202429 : Blo 1895435 7202429 := bstep (se 3 (by rfl) ⟨1350455, by rfl⟩ : syracuseStep 7202429 = 2700911) B2700911
theorem B4801619 : Blo 1895435 4801619 := bstep (se 1 (by rfl) ⟨3601214, by rfl⟩ : syracuseStep 4801619 = 7202429) B7202429
theorem B3201079 : Blo 1895435 3201079 := bstep (se 1 (by rfl) ⟨2400809, by rfl⟩ : syracuseStep 3201079 = 4801619) B4801619
theorem B4268105 : Blo 1895435 4268105 := bstep (se 2 (by rfl) ⟨1600539, by rfl⟩ : syracuseStep 4268105 = 3201079) B3201079
theorem B2845403 : Blo 1895435 2845403 := bstep (se 1 (by rfl) ⟨2134052, by rfl⟩ : syracuseStep 2845403 = 4268105) B4268105
theorem B1896935 : Blo 1895435 1896935 := bstep (se 1 (by rfl) ⟨1422701, by rfl⟩ : syracuseStep 1896935 = 2845403) B2845403
theorem B2134057 : Blo 1895435 2134057 := bbase (se 2 (by rfl) ⟨800271, by rfl⟩ : syracuseStep 2134057 = 1600543) (by norm_num)
theorem B2845409 : Blo 1895435 2845409 := bstep (se 2 (by rfl) ⟨1067028, by rfl⟩ : syracuseStep 2845409 = 2134057) B2134057
theorem B1896939 : Blo 1895435 1896939 := bstep (se 1 (by rfl) ⟨1422704, by rfl⟩ : syracuseStep 1896939 = 2845409) B2845409
theorem B11536949 : Blo 1895435 11536949 := bbase (se 5 (by rfl) ⟨540794, by rfl⟩ : syracuseStep 11536949 = 1081589) (by norm_num)
theorem B30765197 : Blo 1895435 30765197 := bstep (se 3 (by rfl) ⟨5768474, by rfl⟩ : syracuseStep 30765197 = 11536949) B11536949
theorem B20510131 : Blo 1895435 20510131 := bstep (se 1 (by rfl) ⟨15382598, by rfl⟩ : syracuseStep 20510131 = 30765197) B30765197
theorem B27346841 : Blo 1895435 27346841 := bstep (se 2 (by rfl) ⟨10255065, by rfl⟩ : syracuseStep 27346841 = 20510131) B20510131
theorem B18231227 : Blo 1895435 18231227 := bstep (se 1 (by rfl) ⟨13673420, by rfl⟩ : syracuseStep 18231227 = 27346841) B27346841
theorem B12154151 : Blo 1895435 12154151 := bstep (se 1 (by rfl) ⟨9115613, by rfl⟩ : syracuseStep 12154151 = 18231227) B18231227
theorem B8102767 : Blo 1895435 8102767 := bstep (se 1 (by rfl) ⟨6077075, by rfl⟩ : syracuseStep 8102767 = 12154151) B12154151
theorem B10803689 : Blo 1895435 10803689 := bstep (se 2 (by rfl) ⟨4051383, by rfl⟩ : syracuseStep 10803689 = 8102767) B8102767
theorem B7202459 : Blo 1895435 7202459 := bstep (se 1 (by rfl) ⟨5401844, by rfl⟩ : syracuseStep 7202459 = 10803689) B10803689
theorem B4801639 : Blo 1895435 4801639 := bstep (se 1 (by rfl) ⟨3601229, by rfl⟩ : syracuseStep 4801639 = 7202459) B7202459
theorem B6402185 : Blo 1895435 6402185 := bstep (se 2 (by rfl) ⟨2400819, by rfl⟩ : syracuseStep 6402185 = 4801639) B4801639
theorem B4268123 : Blo 1895435 4268123 := bstep (se 1 (by rfl) ⟨3201092, by rfl⟩ : syracuseStep 4268123 = 6402185) B6402185
theorem B2845415 : Blo 1895435 2845415 := bstep (se 1 (by rfl) ⟨2134061, by rfl⟩ : syracuseStep 2845415 = 4268123) B4268123
theorem B1896943 : Blo 1895435 1896943 := bstep (se 1 (by rfl) ⟨1422707, by rfl⟩ : syracuseStep 1896943 = 2845415) B2845415
theorem B2845421 : Blo 1895435 2845421 := bbase (se 3 (by rfl) ⟨533516, by rfl⟩ : syracuseStep 2845421 = 1067033) (by norm_num)
theorem B1896947 : Blo 1895435 1896947 := bstep (se 1 (by rfl) ⟨1422710, by rfl⟩ : syracuseStep 1896947 = 2845421) B2845421
theorem B4268141 : Blo 1895435 4268141 := bbase (se 3 (by rfl) ⟨800276, by rfl⟩ : syracuseStep 4268141 = 1600553) (by norm_num)
theorem B2845427 : Blo 1895435 2845427 := bstep (se 1 (by rfl) ⟨2134070, by rfl⟩ : syracuseStep 2845427 = 4268141) B4268141
theorem B1896951 : Blo 1895435 1896951 := bstep (se 1 (by rfl) ⟨1422713, by rfl⟩ : syracuseStep 1896951 = 2845427) B2845427
theorem B3601253 : Blo 1895435 3601253 := bbase (se 4 (by rfl) ⟨337617, by rfl⟩ : syracuseStep 3601253 = 675235) (by norm_num)
theorem B2400835 : Blo 1895435 2400835 := bstep (se 1 (by rfl) ⟨1800626, by rfl⟩ : syracuseStep 2400835 = 3601253) B3601253
theorem B3201113 : Blo 1895435 3201113 := bstep (se 2 (by rfl) ⟨1200417, by rfl⟩ : syracuseStep 3201113 = 2400835) B2400835
theorem B2134075 : Blo 1895435 2134075 := bstep (se 1 (by rfl) ⟨1600556, by rfl⟩ : syracuseStep 2134075 = 3201113) B3201113
theorem B2845433 : Blo 1895435 2845433 := bstep (se 2 (by rfl) ⟨1067037, by rfl⟩ : syracuseStep 2845433 = 2134075) B2134075
theorem B1896955 : Blo 1895435 1896955 := bstep (se 1 (by rfl) ⟨1422716, by rfl⟩ : syracuseStep 1896955 = 2845433) B2845433
theorem B4106693 : Blo 1895435 4106693 := bbase (se 4 (by rfl) ⟨385002, by rfl⟩ : syracuseStep 4106693 = 770005) (by norm_num)
theorem B10951181 : Blo 1895435 10951181 := bstep (se 3 (by rfl) ⟨2053346, by rfl⟩ : syracuseStep 10951181 = 4106693) B4106693
theorem B7300787 : Blo 1895435 7300787 := bstep (se 1 (by rfl) ⟨5475590, by rfl⟩ : syracuseStep 7300787 = 10951181) B10951181
theorem B19468765 : Blo 1895435 19468765 := bstep (se 3 (by rfl) ⟨3650393, by rfl⟩ : syracuseStep 19468765 = 7300787) B7300787
theorem B25958353 : Blo 1895435 25958353 := bstep (se 2 (by rfl) ⟨9734382, by rfl⟩ : syracuseStep 25958353 = 19468765) B19468765
theorem B34611137 : Blo 1895435 34611137 := bstep (se 2 (by rfl) ⟨12979176, by rfl⟩ : syracuseStep 34611137 = 25958353) B25958353
theorem B23074091 : Blo 1895435 23074091 := bstep (se 1 (by rfl) ⟨17305568, by rfl⟩ : syracuseStep 23074091 = 34611137) B34611137
theorem B15382727 : Blo 1895435 15382727 := bstep (se 1 (by rfl) ⟨11537045, by rfl⟩ : syracuseStep 15382727 = 23074091) B23074091
theorem B10255151 : Blo 1895435 10255151 := bstep (se 1 (by rfl) ⟨7691363, by rfl⟩ : syracuseStep 10255151 = 15382727) B15382727
theorem B6836767 : Blo 1895435 6836767 := bstep (se 1 (by rfl) ⟨5127575, by rfl⟩ : syracuseStep 6836767 = 10255151) B10255151
theorem B36462757 : Blo 1895435 36462757 := bstep (se 4 (by rfl) ⟨3418383, by rfl⟩ : syracuseStep 36462757 = 6836767) B6836767
theorem B48617009 : Blo 1895435 48617009 := bstep (se 2 (by rfl) ⟨18231378, by rfl⟩ : syracuseStep 48617009 = 36462757) B36462757
theorem B32411339 : Blo 1895435 32411339 := bstep (se 1 (by rfl) ⟨24308504, by rfl⟩ : syracuseStep 32411339 = 48617009) B48617009
theorem B21607559 : Blo 1895435 21607559 := bstep (se 1 (by rfl) ⟨16205669, by rfl⟩ : syracuseStep 21607559 = 32411339) B32411339
theorem B14405039 : Blo 1895435 14405039 := bstep (se 1 (by rfl) ⟨10803779, by rfl⟩ : syracuseStep 14405039 = 21607559) B21607559
theorem B9603359 : Blo 1895435 9603359 := bstep (se 1 (by rfl) ⟨7202519, by rfl⟩ : syracuseStep 9603359 = 14405039) B14405039
theorem B6402239 : Blo 1895435 6402239 := bstep (se 1 (by rfl) ⟨4801679, by rfl⟩ : syracuseStep 6402239 = 9603359) B9603359
theorem B4268159 : Blo 1895435 4268159 := bstep (se 1 (by rfl) ⟨3201119, by rfl⟩ : syracuseStep 4268159 = 6402239) B6402239
theorem B2845439 : Blo 1895435 2845439 := bstep (se 1 (by rfl) ⟨2134079, by rfl⟩ : syracuseStep 2845439 = 4268159) B4268159
theorem B1896959 : Blo 1895435 1896959 := bstep (se 1 (by rfl) ⟨1422719, by rfl⟩ : syracuseStep 1896959 = 2845439) B2845439
theorem B2845445 : Blo 1895435 2845445 := bbase (se 4 (by rfl) ⟨266760, by rfl⟩ : syracuseStep 2845445 = 533521) (by norm_num)
theorem B1896963 : Blo 1895435 1896963 := bstep (se 1 (by rfl) ⟨1422722, by rfl⟩ : syracuseStep 1896963 = 2845445) B2845445
theorem B3201133 : Blo 1895435 3201133 := bbase (se 3 (by rfl) ⟨600212, by rfl⟩ : syracuseStep 3201133 = 1200425) (by norm_num)
theorem B4268177 : Blo 1895435 4268177 := bstep (se 2 (by rfl) ⟨1600566, by rfl⟩ : syracuseStep 4268177 = 3201133) B3201133
theorem B2845451 : Blo 1895435 2845451 := bstep (se 1 (by rfl) ⟨2134088, by rfl⟩ : syracuseStep 2845451 = 4268177) B4268177
theorem B1896967 : Blo 1895435 1896967 := bstep (se 1 (by rfl) ⟨1422725, by rfl⟩ : syracuseStep 1896967 = 2845451) B2845451
theorem B2134093 : Blo 1895435 2134093 := bbase (se 3 (by rfl) ⟨400142, by rfl⟩ : syracuseStep 2134093 = 800285) (by norm_num)
theorem B2845457 : Blo 1895435 2845457 := bstep (se 2 (by rfl) ⟨1067046, by rfl⟩ : syracuseStep 2845457 = 2134093) B2134093
theorem B1896971 : Blo 1895435 1896971 := bstep (se 1 (by rfl) ⟨1422728, by rfl⟩ : syracuseStep 1896971 = 2845457) B2845457
theorem B6402293 : Blo 1895435 6402293 := bbase (se 5 (by rfl) ⟨300107, by rfl⟩ : syracuseStep 6402293 = 600215) (by norm_num)
theorem B4268195 : Blo 1895435 4268195 := bstep (se 1 (by rfl) ⟨3201146, by rfl⟩ : syracuseStep 4268195 = 6402293) B6402293
theorem B2845463 : Blo 1895435 2845463 := bstep (se 1 (by rfl) ⟨2134097, by rfl⟩ : syracuseStep 2845463 = 4268195) B4268195
theorem B1896975 : Blo 1895435 1896975 := bstep (se 1 (by rfl) ⟨1422731, by rfl⟩ : syracuseStep 1896975 = 2845463) B2845463
theorem B2845469 : Blo 1895435 2845469 := bbase (se 3 (by rfl) ⟨533525, by rfl⟩ : syracuseStep 2845469 = 1067051) (by norm_num)
theorem B1896979 : Blo 1895435 1896979 := bstep (se 1 (by rfl) ⟨1422734, by rfl⟩ : syracuseStep 1896979 = 2845469) B2845469
theorem B4268213 : Blo 1895435 4268213 := bbase (se 5 (by rfl) ⟨200072, by rfl⟩ : syracuseStep 4268213 = 400145) (by norm_num)
theorem B2845475 : Blo 1895435 2845475 := bstep (se 1 (by rfl) ⟨2134106, by rfl⟩ : syracuseStep 2845475 = 4268213) B4268213
theorem B1896983 : Blo 1895435 1896983 := bstep (se 1 (by rfl) ⟨1422737, by rfl⟩ : syracuseStep 1896983 = 2845475) B2845475
theorem B2278957 : Blo 1895435 2278957 := bbase (se 3 (by rfl) ⟨427304, by rfl⟩ : syracuseStep 2278957 = 854609) (by norm_num)
theorem B3038609 : Blo 1895435 3038609 := bstep (se 2 (by rfl) ⟨1139478, by rfl⟩ : syracuseStep 3038609 = 2278957) B2278957
theorem B2025739 : Blo 1895435 2025739 := bstep (se 1 (by rfl) ⟨1519304, by rfl⟩ : syracuseStep 2025739 = 3038609) B3038609
theorem B10803941 : Blo 1895435 10803941 := bstep (se 4 (by rfl) ⟨1012869, by rfl⟩ : syracuseStep 10803941 = 2025739) B2025739
theorem B7202627 : Blo 1895435 7202627 := bstep (se 1 (by rfl) ⟨5401970, by rfl⟩ : syracuseStep 7202627 = 10803941) B10803941
theorem B4801751 : Blo 1895435 4801751 := bstep (se 1 (by rfl) ⟨3601313, by rfl⟩ : syracuseStep 4801751 = 7202627) B7202627
theorem B3201167 : Blo 1895435 3201167 := bstep (se 1 (by rfl) ⟨2400875, by rfl⟩ : syracuseStep 3201167 = 4801751) B4801751
theorem B2134111 : Blo 1895435 2134111 := bstep (se 1 (by rfl) ⟨1600583, by rfl⟩ : syracuseStep 2134111 = 3201167) B3201167
theorem B2845481 : Blo 1895435 2845481 := bstep (se 2 (by rfl) ⟨1067055, by rfl⟩ : syracuseStep 2845481 = 2134111) B2134111
theorem B1896987 : Blo 1895435 1896987 := bstep (se 1 (by rfl) ⟨1422740, by rfl⟩ : syracuseStep 1896987 = 2845481) B2845481
theorem B6836885 : Blo 1895435 6836885 := bbase (se 6 (by rfl) ⟨160239, by rfl⟩ : syracuseStep 6836885 = 320479) (by norm_num)
theorem B4557923 : Blo 1895435 4557923 := bstep (se 1 (by rfl) ⟨3418442, by rfl⟩ : syracuseStep 4557923 = 6836885) B6836885
theorem B3038615 : Blo 1895435 3038615 := bstep (se 1 (by rfl) ⟨2278961, by rfl⟩ : syracuseStep 3038615 = 4557923) B4557923
theorem B2025743 : Blo 1895435 2025743 := bstep (se 1 (by rfl) ⟨1519307, by rfl⟩ : syracuseStep 2025743 = 3038615) B3038615
theorem B5401981 : Blo 1895435 5401981 := bstep (se 3 (by rfl) ⟨1012871, by rfl⟩ : syracuseStep 5401981 = 2025743) B2025743
theorem B7202641 : Blo 1895435 7202641 := bstep (se 2 (by rfl) ⟨2700990, by rfl⟩ : syracuseStep 7202641 = 5401981) B5401981
theorem B9603521 : Blo 1895435 9603521 := bstep (se 2 (by rfl) ⟨3601320, by rfl⟩ : syracuseStep 9603521 = 7202641) B7202641
theorem B6402347 : Blo 1895435 6402347 := bstep (se 1 (by rfl) ⟨4801760, by rfl⟩ : syracuseStep 6402347 = 9603521) B9603521
theorem B4268231 : Blo 1895435 4268231 := bstep (se 1 (by rfl) ⟨3201173, by rfl⟩ : syracuseStep 4268231 = 6402347) B6402347
theorem B2845487 : Blo 1895435 2845487 := bstep (se 1 (by rfl) ⟨2134115, by rfl⟩ : syracuseStep 2845487 = 4268231) B4268231
theorem B1896991 : Blo 1895435 1896991 := bstep (se 1 (by rfl) ⟨1422743, by rfl⟩ : syracuseStep 1896991 = 2845487) B2845487
theorem B2845493 : Blo 1895435 2845493 := bbase (se 5 (by rfl) ⟨133382, by rfl⟩ : syracuseStep 2845493 = 266765) (by norm_num)
theorem B1896995 : Blo 1895435 1896995 := bstep (se 1 (by rfl) ⟨1422746, by rfl⟩ : syracuseStep 1896995 = 2845493) B2845493
theorem B4801781 : Blo 1895435 4801781 := bbase (se 5 (by rfl) ⟨225083, by rfl⟩ : syracuseStep 4801781 = 450167) (by norm_num)
theorem B3201187 : Blo 1895435 3201187 := bstep (se 1 (by rfl) ⟨2400890, by rfl⟩ : syracuseStep 3201187 = 4801781) B4801781
theorem B4268249 : Blo 1895435 4268249 := bstep (se 2 (by rfl) ⟨1600593, by rfl⟩ : syracuseStep 4268249 = 3201187) B3201187
theorem B2845499 : Blo 1895435 2845499 := bstep (se 1 (by rfl) ⟨2134124, by rfl⟩ : syracuseStep 2845499 = 4268249) B4268249
theorem B1896999 : Blo 1895435 1896999 := bstep (se 1 (by rfl) ⟨1422749, by rfl⟩ : syracuseStep 1896999 = 2845499) B2845499
theorem B2134129 : Blo 1895435 2134129 := bbase (se 2 (by rfl) ⟨800298, by rfl⟩ : syracuseStep 2134129 = 1600597) (by norm_num)
theorem B2845505 : Blo 1895435 2845505 := bstep (se 2 (by rfl) ⟨1067064, by rfl⟩ : syracuseStep 2845505 = 2134129) B2134129
theorem B1897003 : Blo 1895435 1897003 := bstep (se 1 (by rfl) ⟨1422752, by rfl⟩ : syracuseStep 1897003 = 2845505) B2845505
theorem B13156597 : Blo 1895435 13156597 := bbase (se 5 (by rfl) ⟨616715, by rfl⟩ : syracuseStep 13156597 = 1233431) (by norm_num)
theorem B17542129 : Blo 1895435 17542129 := bstep (se 2 (by rfl) ⟨6578298, by rfl⟩ : syracuseStep 17542129 = 13156597) B13156597
theorem B23389505 : Blo 1895435 23389505 := bstep (se 2 (by rfl) ⟨8771064, by rfl⟩ : syracuseStep 23389505 = 17542129) B17542129
theorem B15593003 : Blo 1895435 15593003 := bstep (se 1 (by rfl) ⟨11694752, by rfl⟩ : syracuseStep 15593003 = 23389505) B23389505
theorem B10395335 : Blo 1895435 10395335 := bstep (se 1 (by rfl) ⟨7796501, by rfl⟩ : syracuseStep 10395335 = 15593003) B15593003
theorem B27720893 : Blo 1895435 27720893 := bstep (se 3 (by rfl) ⟨5197667, by rfl⟩ : syracuseStep 27720893 = 10395335) B10395335
theorem B18480595 : Blo 1895435 18480595 := bstep (se 1 (by rfl) ⟨13860446, by rfl⟩ : syracuseStep 18480595 = 27720893) B27720893
theorem B24640793 : Blo 1895435 24640793 := bstep (se 2 (by rfl) ⟨9240297, by rfl⟩ : syracuseStep 24640793 = 18480595) B18480595
theorem B16427195 : Blo 1895435 16427195 := bstep (se 1 (by rfl) ⟨12320396, by rfl⟩ : syracuseStep 16427195 = 24640793) B24640793
theorem B10951463 : Blo 1895435 10951463 := bstep (se 1 (by rfl) ⟨8213597, by rfl⟩ : syracuseStep 10951463 = 16427195) B16427195
theorem B29203901 : Blo 1895435 29203901 := bstep (se 3 (by rfl) ⟨5475731, by rfl⟩ : syracuseStep 29203901 = 10951463) B10951463
theorem B19469267 : Blo 1895435 19469267 := bstep (se 1 (by rfl) ⟨14601950, by rfl⟩ : syracuseStep 19469267 = 29203901) B29203901
theorem B12979511 : Blo 1895435 12979511 := bstep (se 1 (by rfl) ⟨9734633, by rfl⟩ : syracuseStep 12979511 = 19469267) B19469267
theorem B8653007 : Blo 1895435 8653007 := bstep (se 1 (by rfl) ⟨6489755, by rfl⟩ : syracuseStep 8653007 = 12979511) B12979511
theorem B5768671 : Blo 1895435 5768671 := bstep (se 1 (by rfl) ⟨4326503, by rfl⟩ : syracuseStep 5768671 = 8653007) B8653007
theorem B7691561 : Blo 1895435 7691561 := bstep (se 2 (by rfl) ⟨2884335, by rfl⟩ : syracuseStep 7691561 = 5768671) B5768671
theorem B5127707 : Blo 1895435 5127707 := bstep (se 1 (by rfl) ⟨3845780, by rfl⟩ : syracuseStep 5127707 = 7691561) B7691561
theorem B3418471 : Blo 1895435 3418471 := bstep (se 1 (by rfl) ⟨2563853, by rfl⟩ : syracuseStep 3418471 = 5127707) B5127707
theorem B4557961 : Blo 1895435 4557961 := bstep (se 2 (by rfl) ⟨1709235, by rfl⟩ : syracuseStep 4557961 = 3418471) B3418471
theorem B6077281 : Blo 1895435 6077281 := bstep (se 2 (by rfl) ⟨2278980, by rfl⟩ : syracuseStep 6077281 = 4557961) B4557961
theorem B8103041 : Blo 1895435 8103041 := bstep (se 2 (by rfl) ⟨3038640, by rfl⟩ : syracuseStep 8103041 = 6077281) B6077281
theorem B5402027 : Blo 1895435 5402027 := bstep (se 1 (by rfl) ⟨4051520, by rfl⟩ : syracuseStep 5402027 = 8103041) B8103041
theorem B3601351 : Blo 1895435 3601351 := bstep (se 1 (by rfl) ⟨2701013, by rfl⟩ : syracuseStep 3601351 = 5402027) B5402027
theorem B4801801 : Blo 1895435 4801801 := bstep (se 2 (by rfl) ⟨1800675, by rfl⟩ : syracuseStep 4801801 = 3601351) B3601351
theorem B6402401 : Blo 1895435 6402401 := bstep (se 2 (by rfl) ⟨2400900, by rfl⟩ : syracuseStep 6402401 = 4801801) B4801801
theorem B4268267 : Blo 1895435 4268267 := bstep (se 1 (by rfl) ⟨3201200, by rfl⟩ : syracuseStep 4268267 = 6402401) B6402401
theorem B2845511 : Blo 1895435 2845511 := bstep (se 1 (by rfl) ⟨2134133, by rfl⟩ : syracuseStep 2845511 = 4268267) B4268267
theorem B1897007 : Blo 1895435 1897007 := bstep (se 1 (by rfl) ⟨1422755, by rfl⟩ : syracuseStep 1897007 = 2845511) B2845511
theorem B2845517 : Blo 1895435 2845517 := bbase (se 3 (by rfl) ⟨533534, by rfl⟩ : syracuseStep 2845517 = 1067069) (by norm_num)
theorem B1897011 : Blo 1895435 1897011 := bstep (se 1 (by rfl) ⟨1422758, by rfl⟩ : syracuseStep 1897011 = 2845517) B2845517
theorem B4268285 : Blo 1895435 4268285 := bbase (se 3 (by rfl) ⟨800303, by rfl⟩ : syracuseStep 4268285 = 1600607) (by norm_num)
theorem B2845523 : Blo 1895435 2845523 := bstep (se 1 (by rfl) ⟨2134142, by rfl⟩ : syracuseStep 2845523 = 4268285) B4268285
theorem B1897015 : Blo 1895435 1897015 := bstep (se 1 (by rfl) ⟨1422761, by rfl⟩ : syracuseStep 1897015 = 2845523) B2845523
theorem B3201221 : Blo 1895435 3201221 := bbase (se 4 (by rfl) ⟨300114, by rfl⟩ : syracuseStep 3201221 = 600229) (by norm_num)
theorem B2134147 : Blo 1895435 2134147 := bstep (se 1 (by rfl) ⟨1600610, by rfl⟩ : syracuseStep 2134147 = 3201221) B3201221
theorem B2845529 : Blo 1895435 2845529 := bstep (se 2 (by rfl) ⟨1067073, by rfl⟩ : syracuseStep 2845529 = 2134147) B2134147
theorem B1897019 : Blo 1895435 1897019 := bstep (se 1 (by rfl) ⟨1422764, by rfl⟩ : syracuseStep 1897019 = 2845529) B2845529
theorem B14405525 : Blo 1895435 14405525 := bbase (se 6 (by rfl) ⟨337629, by rfl⟩ : syracuseStep 14405525 = 675259) (by norm_num)
theorem B9603683 : Blo 1895435 9603683 := bstep (se 1 (by rfl) ⟨7202762, by rfl⟩ : syracuseStep 9603683 = 14405525) B14405525
theorem B6402455 : Blo 1895435 6402455 := bstep (se 1 (by rfl) ⟨4801841, by rfl⟩ : syracuseStep 6402455 = 9603683) B9603683
theorem B4268303 : Blo 1895435 4268303 := bstep (se 1 (by rfl) ⟨3201227, by rfl⟩ : syracuseStep 4268303 = 6402455) B6402455
theorem B2845535 : Blo 1895435 2845535 := bstep (se 1 (by rfl) ⟨2134151, by rfl⟩ : syracuseStep 2845535 = 4268303) B4268303
theorem B1897023 : Blo 1895435 1897023 := bstep (se 1 (by rfl) ⟨1422767, by rfl⟩ : syracuseStep 1897023 = 2845535) B2845535
theorem B2845541 : Blo 1895435 2845541 := bbase (se 4 (by rfl) ⟨266769, by rfl⟩ : syracuseStep 2845541 = 533539) (by norm_num)
theorem B1897027 : Blo 1895435 1897027 := bstep (se 1 (by rfl) ⟨1422770, by rfl⟩ : syracuseStep 1897027 = 2845541) B2845541
theorem B3601397 : Blo 1895435 3601397 := bbase (se 5 (by rfl) ⟨168815, by rfl⟩ : syracuseStep 3601397 = 337631) (by norm_num)
theorem B2400931 : Blo 1895435 2400931 := bstep (se 1 (by rfl) ⟨1800698, by rfl⟩ : syracuseStep 2400931 = 3601397) B3601397
theorem B3201241 : Blo 1895435 3201241 := bstep (se 2 (by rfl) ⟨1200465, by rfl⟩ : syracuseStep 3201241 = 2400931) B2400931
theorem B4268321 : Blo 1895435 4268321 := bstep (se 2 (by rfl) ⟨1600620, by rfl⟩ : syracuseStep 4268321 = 3201241) B3201241
theorem B2845547 : Blo 1895435 2845547 := bstep (se 1 (by rfl) ⟨2134160, by rfl⟩ : syracuseStep 2845547 = 4268321) B4268321
theorem B1897031 : Blo 1895435 1897031 := bstep (se 1 (by rfl) ⟨1422773, by rfl⟩ : syracuseStep 1897031 = 2845547) B2845547
theorem B2134165 : Blo 1895435 2134165 := bbase (se 6 (by rfl) ⟨50019, by rfl⟩ : syracuseStep 2134165 = 100039) (by norm_num)
theorem B2845553 : Blo 1895435 2845553 := bstep (se 2 (by rfl) ⟨1067082, by rfl⟩ : syracuseStep 2845553 = 2134165) B2134165
theorem B1897035 : Blo 1895435 1897035 := bstep (se 1 (by rfl) ⟨1422776, by rfl⟩ : syracuseStep 1897035 = 2845553) B2845553
theorem B2400941 : Blo 1895435 2400941 := bbase (se 3 (by rfl) ⟨450176, by rfl⟩ : syracuseStep 2400941 = 900353) (by norm_num)
theorem B6402509 : Blo 1895435 6402509 := bstep (se 3 (by rfl) ⟨1200470, by rfl⟩ : syracuseStep 6402509 = 2400941) B2400941
theorem B4268339 : Blo 1895435 4268339 := bstep (se 1 (by rfl) ⟨3201254, by rfl⟩ : syracuseStep 4268339 = 6402509) B6402509
theorem B2845559 : Blo 1895435 2845559 := bstep (se 1 (by rfl) ⟨2134169, by rfl⟩ : syracuseStep 2845559 = 4268339) B4268339
theorem B1897039 : Blo 1895435 1897039 := bstep (se 1 (by rfl) ⟨1422779, by rfl⟩ : syracuseStep 1897039 = 2845559) B2845559
theorem B2845565 : Blo 1895435 2845565 := bbase (se 3 (by rfl) ⟨533543, by rfl⟩ : syracuseStep 2845565 = 1067087) (by norm_num)
theorem B1897043 : Blo 1895435 1897043 := bstep (se 1 (by rfl) ⟨1422782, by rfl⟩ : syracuseStep 1897043 = 2845565) B2845565
theorem B4268357 : Blo 1895435 4268357 := bbase (se 4 (by rfl) ⟨400158, by rfl⟩ : syracuseStep 4268357 = 800317) (by norm_num)
theorem B2845571 : Blo 1895435 2845571 := bstep (se 1 (by rfl) ⟨2134178, by rfl⟩ : syracuseStep 2845571 = 4268357) B4268357
theorem B1897047 : Blo 1895435 1897047 := bstep (se 1 (by rfl) ⟨1422785, by rfl⟩ : syracuseStep 1897047 = 2845571) B2845571
theorem B19469717 : Blo 1895435 19469717 := bbase (se 6 (by rfl) ⟨456321, by rfl⟩ : syracuseStep 19469717 = 912643) (by norm_num)
theorem B12979811 : Blo 1895435 12979811 := bstep (se 1 (by rfl) ⟨9734858, by rfl⟩ : syracuseStep 12979811 = 19469717) B19469717
theorem B34612829 : Blo 1895435 34612829 := bstep (se 3 (by rfl) ⟨6489905, by rfl⟩ : syracuseStep 34612829 = 12979811) B12979811
theorem B23075219 : Blo 1895435 23075219 := bstep (se 1 (by rfl) ⟨17306414, by rfl⟩ : syracuseStep 23075219 = 34612829) B34612829
theorem B15383479 : Blo 1895435 15383479 := bstep (se 1 (by rfl) ⟨11537609, by rfl⟩ : syracuseStep 15383479 = 23075219) B23075219
theorem B20511305 : Blo 1895435 20511305 := bstep (se 2 (by rfl) ⟨7691739, by rfl⟩ : syracuseStep 20511305 = 15383479) B15383479
theorem B13674203 : Blo 1895435 13674203 := bstep (se 1 (by rfl) ⟨10255652, by rfl⟩ : syracuseStep 13674203 = 20511305) B20511305
theorem B9116135 : Blo 1895435 9116135 := bstep (se 1 (by rfl) ⟨6837101, by rfl⟩ : syracuseStep 9116135 = 13674203) B13674203
theorem B6077423 : Blo 1895435 6077423 := bstep (se 1 (by rfl) ⟨4558067, by rfl⟩ : syracuseStep 6077423 = 9116135) B9116135
theorem B4051615 : Blo 1895435 4051615 := bstep (se 1 (by rfl) ⟨3038711, by rfl⟩ : syracuseStep 4051615 = 6077423) B6077423
theorem B5402153 : Blo 1895435 5402153 := bstep (se 2 (by rfl) ⟨2025807, by rfl⟩ : syracuseStep 5402153 = 4051615) B4051615
theorem B3601435 : Blo 1895435 3601435 := bstep (se 1 (by rfl) ⟨2701076, by rfl⟩ : syracuseStep 3601435 = 5402153) B5402153
theorem B4801913 : Blo 1895435 4801913 := bstep (se 2 (by rfl) ⟨1800717, by rfl⟩ : syracuseStep 4801913 = 3601435) B3601435
theorem B3201275 : Blo 1895435 3201275 := bstep (se 1 (by rfl) ⟨2400956, by rfl⟩ : syracuseStep 3201275 = 4801913) B4801913
theorem B2134183 : Blo 1895435 2134183 := bstep (se 1 (by rfl) ⟨1600637, by rfl⟩ : syracuseStep 2134183 = 3201275) B3201275
theorem B2845577 : Blo 1895435 2845577 := bstep (se 2 (by rfl) ⟨1067091, by rfl⟩ : syracuseStep 2845577 = 2134183) B2134183
theorem B1897051 : Blo 1895435 1897051 := bstep (se 1 (by rfl) ⟨1422788, by rfl⟩ : syracuseStep 1897051 = 2845577) B2845577
theorem B9603845 : Blo 1895435 9603845 := bbase (se 4 (by rfl) ⟨900360, by rfl⟩ : syracuseStep 9603845 = 1800721) (by norm_num)
theorem B6402563 : Blo 1895435 6402563 := bstep (se 1 (by rfl) ⟨4801922, by rfl⟩ : syracuseStep 6402563 = 9603845) B9603845
theorem B4268375 : Blo 1895435 4268375 := bstep (se 1 (by rfl) ⟨3201281, by rfl⟩ : syracuseStep 4268375 = 6402563) B6402563
theorem B2845583 : Blo 1895435 2845583 := bstep (se 1 (by rfl) ⟨2134187, by rfl⟩ : syracuseStep 2845583 = 4268375) B4268375
theorem B1897055 : Blo 1895435 1897055 := bstep (se 1 (by rfl) ⟨1422791, by rfl⟩ : syracuseStep 1897055 = 2845583) B2845583
theorem B2845589 : Blo 1895435 2845589 := bbase (se 6 (by rfl) ⟨66693, by rfl⟩ : syracuseStep 2845589 = 133387) (by norm_num)
theorem B1897059 : Blo 1895435 1897059 := bstep (se 1 (by rfl) ⟨1422794, by rfl⟩ : syracuseStep 1897059 = 2845589) B2845589
theorem B10804373 : Blo 1895435 10804373 := bbase (se 6 (by rfl) ⟨253227, by rfl⟩ : syracuseStep 10804373 = 506455) (by norm_num)
theorem B7202915 : Blo 1895435 7202915 := bstep (se 1 (by rfl) ⟨5402186, by rfl⟩ : syracuseStep 7202915 = 10804373) B10804373
theorem B4801943 : Blo 1895435 4801943 := bstep (se 1 (by rfl) ⟨3601457, by rfl⟩ : syracuseStep 4801943 = 7202915) B7202915
theorem B3201295 : Blo 1895435 3201295 := bstep (se 1 (by rfl) ⟨2400971, by rfl⟩ : syracuseStep 3201295 = 4801943) B4801943
theorem B4268393 : Blo 1895435 4268393 := bstep (se 2 (by rfl) ⟨1600647, by rfl⟩ : syracuseStep 4268393 = 3201295) B3201295
theorem B2845595 : Blo 1895435 2845595 := bstep (se 1 (by rfl) ⟨2134196, by rfl⟩ : syracuseStep 2845595 = 4268393) B4268393
theorem B1897063 : Blo 1895435 1897063 := bstep (se 1 (by rfl) ⟨1422797, by rfl⟩ : syracuseStep 1897063 = 2845595) B2845595
theorem B2134201 : Blo 1895435 2134201 := bbase (se 2 (by rfl) ⟨800325, by rfl⟩ : syracuseStep 2134201 = 1600651) (by norm_num)
theorem B2845601 : Blo 1895435 2845601 := bstep (se 2 (by rfl) ⟨1067100, by rfl⟩ : syracuseStep 2845601 = 2134201) B2134201
theorem B1897067 : Blo 1895435 1897067 := bstep (se 1 (by rfl) ⟨1422800, by rfl⟩ : syracuseStep 1897067 = 2845601) B2845601
theorem B6837173 : Blo 1895435 6837173 := bbase (se 5 (by rfl) ⟨320492, by rfl⟩ : syracuseStep 6837173 = 640985) (by norm_num)
theorem B4558115 : Blo 1895435 4558115 := bstep (se 1 (by rfl) ⟨3418586, by rfl⟩ : syracuseStep 4558115 = 6837173) B6837173
theorem B3038743 : Blo 1895435 3038743 := bstep (se 1 (by rfl) ⟨2279057, by rfl⟩ : syracuseStep 3038743 = 4558115) B4558115
theorem B4051657 : Blo 1895435 4051657 := bstep (se 2 (by rfl) ⟨1519371, by rfl⟩ : syracuseStep 4051657 = 3038743) B3038743
theorem B5402209 : Blo 1895435 5402209 := bstep (se 2 (by rfl) ⟨2025828, by rfl⟩ : syracuseStep 5402209 = 4051657) B4051657
theorem B7202945 : Blo 1895435 7202945 := bstep (se 2 (by rfl) ⟨2701104, by rfl⟩ : syracuseStep 7202945 = 5402209) B5402209
theorem B4801963 : Blo 1895435 4801963 := bstep (se 1 (by rfl) ⟨3601472, by rfl⟩ : syracuseStep 4801963 = 7202945) B7202945
theorem B6402617 : Blo 1895435 6402617 := bstep (se 2 (by rfl) ⟨2400981, by rfl⟩ : syracuseStep 6402617 = 4801963) B4801963
theorem B4268411 : Blo 1895435 4268411 := bstep (se 1 (by rfl) ⟨3201308, by rfl⟩ : syracuseStep 4268411 = 6402617) B6402617
theorem B2845607 : Blo 1895435 2845607 := bstep (se 1 (by rfl) ⟨2134205, by rfl⟩ : syracuseStep 2845607 = 4268411) B4268411
theorem B1897071 : Blo 1895435 1897071 := bstep (se 1 (by rfl) ⟨1422803, by rfl⟩ : syracuseStep 1897071 = 2845607) B2845607
theorem B2845613 : Blo 1895435 2845613 := bbase (se 3 (by rfl) ⟨533552, by rfl⟩ : syracuseStep 2845613 = 1067105) (by norm_num)
theorem B1897075 : Blo 1895435 1897075 := bstep (se 1 (by rfl) ⟨1422806, by rfl⟩ : syracuseStep 1897075 = 2845613) B2845613
theorem B4268429 : Blo 1895435 4268429 := bbase (se 3 (by rfl) ⟨800330, by rfl⟩ : syracuseStep 4268429 = 1600661) (by norm_num)
theorem B2845619 : Blo 1895435 2845619 := bstep (se 1 (by rfl) ⟨2134214, by rfl⟩ : syracuseStep 2845619 = 4268429) B4268429
theorem B1897079 : Blo 1895435 1897079 := bstep (se 1 (by rfl) ⟨1422809, by rfl⟩ : syracuseStep 1897079 = 2845619) B2845619
theorem B2400997 : Blo 1895435 2400997 := bbase (se 4 (by rfl) ⟨225093, by rfl⟩ : syracuseStep 2400997 = 450187) (by norm_num)
theorem B3201329 : Blo 1895435 3201329 := bstep (se 2 (by rfl) ⟨1200498, by rfl⟩ : syracuseStep 3201329 = 2400997) B2400997
theorem B2134219 : Blo 1895435 2134219 := bstep (se 1 (by rfl) ⟨1600664, by rfl⟩ : syracuseStep 2134219 = 3201329) B3201329
theorem B2845625 : Blo 1895435 2845625 := bstep (se 2 (by rfl) ⟨1067109, by rfl⟩ : syracuseStep 2845625 = 2134219) B2134219
theorem B1897083 : Blo 1895435 1897083 := bstep (se 1 (by rfl) ⟨1422812, by rfl⟩ : syracuseStep 1897083 = 2845625) B2845625
theorem B15383765 : Blo 1895435 15383765 := bbase (se 7 (by rfl) ⟨180278, by rfl⟩ : syracuseStep 15383765 = 360557) (by norm_num)
theorem B10255843 : Blo 1895435 10255843 := bstep (se 1 (by rfl) ⟨7691882, by rfl⟩ : syracuseStep 10255843 = 15383765) B15383765
theorem B13674457 : Blo 1895435 13674457 := bstep (se 2 (by rfl) ⟨5127921, by rfl⟩ : syracuseStep 13674457 = 10255843) B10255843
theorem B18232609 : Blo 1895435 18232609 := bstep (se 2 (by rfl) ⟨6837228, by rfl⟩ : syracuseStep 18232609 = 13674457) B13674457
theorem B24310145 : Blo 1895435 24310145 := bstep (se 2 (by rfl) ⟨9116304, by rfl⟩ : syracuseStep 24310145 = 18232609) B18232609
theorem B16206763 : Blo 1895435 16206763 := bstep (se 1 (by rfl) ⟨12155072, by rfl⟩ : syracuseStep 16206763 = 24310145) B24310145
theorem B21609017 : Blo 1895435 21609017 := bstep (se 2 (by rfl) ⟨8103381, by rfl⟩ : syracuseStep 21609017 = 16206763) B16206763
theorem B14406011 : Blo 1895435 14406011 := bstep (se 1 (by rfl) ⟨10804508, by rfl⟩ : syracuseStep 14406011 = 21609017) B21609017
theorem B9604007 : Blo 1895435 9604007 := bstep (se 1 (by rfl) ⟨7203005, by rfl⟩ : syracuseStep 9604007 = 14406011) B14406011
theorem B6402671 : Blo 1895435 6402671 := bstep (se 1 (by rfl) ⟨4802003, by rfl⟩ : syracuseStep 6402671 = 9604007) B9604007
theorem B4268447 : Blo 1895435 4268447 := bstep (se 1 (by rfl) ⟨3201335, by rfl⟩ : syracuseStep 4268447 = 6402671) B6402671
theorem B2845631 : Blo 1895435 2845631 := bstep (se 1 (by rfl) ⟨2134223, by rfl⟩ : syracuseStep 2845631 = 4268447) B4268447
theorem B1897087 : Blo 1895435 1897087 := bstep (se 1 (by rfl) ⟨1422815, by rfl⟩ : syracuseStep 1897087 = 2845631) B2845631
theorem B2845637 : Blo 1895435 2845637 := bbase (se 4 (by rfl) ⟨266778, by rfl⟩ : syracuseStep 2845637 = 533557) (by norm_num)
theorem B1897091 : Blo 1895435 1897091 := bstep (se 1 (by rfl) ⟨1422818, by rfl⟩ : syracuseStep 1897091 = 2845637) B2845637
theorem B3201349 : Blo 1895435 3201349 := bbase (se 4 (by rfl) ⟨300126, by rfl⟩ : syracuseStep 3201349 = 600253) (by norm_num)
theorem B4268465 : Blo 1895435 4268465 := bstep (se 2 (by rfl) ⟨1600674, by rfl⟩ : syracuseStep 4268465 = 3201349) B3201349
theorem B2845643 : Blo 1895435 2845643 := bstep (se 1 (by rfl) ⟨2134232, by rfl⟩ : syracuseStep 2845643 = 4268465) B4268465
theorem B1897095 : Blo 1895435 1897095 := bstep (se 1 (by rfl) ⟨1422821, by rfl⟩ : syracuseStep 1897095 = 2845643) B2845643
theorem B2134237 : Blo 1895435 2134237 := bbase (se 3 (by rfl) ⟨400169, by rfl⟩ : syracuseStep 2134237 = 800339) (by norm_num)
theorem B2845649 : Blo 1895435 2845649 := bstep (se 2 (by rfl) ⟨1067118, by rfl⟩ : syracuseStep 2845649 = 2134237) B2134237
theorem B1897099 : Blo 1895435 1897099 := bstep (se 1 (by rfl) ⟨1422824, by rfl⟩ : syracuseStep 1897099 = 2845649) B2845649
theorem B6402725 : Blo 1895435 6402725 := bbase (se 4 (by rfl) ⟨600255, by rfl⟩ : syracuseStep 6402725 = 1200511) (by norm_num)
theorem B4268483 : Blo 1895435 4268483 := bstep (se 1 (by rfl) ⟨3201362, by rfl⟩ : syracuseStep 4268483 = 6402725) B6402725
theorem B2845655 : Blo 1895435 2845655 := bstep (se 1 (by rfl) ⟨2134241, by rfl⟩ : syracuseStep 2845655 = 4268483) B4268483
theorem B1897103 : Blo 1895435 1897103 := bstep (se 1 (by rfl) ⟨1422827, by rfl⟩ : syracuseStep 1897103 = 2845655) B2845655
theorem B2845661 : Blo 1895435 2845661 := bbase (se 3 (by rfl) ⟨533561, by rfl⟩ : syracuseStep 2845661 = 1067123) (by norm_num)
theorem B1897107 : Blo 1895435 1897107 := bstep (se 1 (by rfl) ⟨1422830, by rfl⟩ : syracuseStep 1897107 = 2845661) B2845661
theorem B4268501 : Blo 1895435 4268501 := bbase (se 7 (by rfl) ⟨50021, by rfl⟩ : syracuseStep 4268501 = 100043) (by norm_num)
theorem B2845667 : Blo 1895435 2845667 := bstep (se 1 (by rfl) ⟨2134250, by rfl⟩ : syracuseStep 2845667 = 4268501) B4268501
theorem B1897111 : Blo 1895435 1897111 := bstep (se 1 (by rfl) ⟨1422833, by rfl⟩ : syracuseStep 1897111 = 2845667) B2845667
theorem B6160549 : Blo 1895435 6160549 := bbase (se 4 (by rfl) ⟨577551, by rfl⟩ : syracuseStep 6160549 = 1155103) (by norm_num)
theorem B8214065 : Blo 1895435 8214065 := bstep (se 2 (by rfl) ⟨3080274, by rfl⟩ : syracuseStep 8214065 = 6160549) B6160549
theorem B5476043 : Blo 1895435 5476043 := bstep (se 1 (by rfl) ⟨4107032, by rfl⟩ : syracuseStep 5476043 = 8214065) B8214065
theorem B14602781 : Blo 1895435 14602781 := bstep (se 3 (by rfl) ⟨2738021, by rfl⟩ : syracuseStep 14602781 = 5476043) B5476043
theorem B9735187 : Blo 1895435 9735187 := bstep (se 1 (by rfl) ⟨7301390, by rfl⟩ : syracuseStep 9735187 = 14602781) B14602781
theorem B12980249 : Blo 1895435 12980249 := bstep (se 2 (by rfl) ⟨4867593, by rfl⟩ : syracuseStep 12980249 = 9735187) B9735187
theorem B8653499 : Blo 1895435 8653499 := bstep (se 1 (by rfl) ⟨6490124, by rfl⟩ : syracuseStep 8653499 = 12980249) B12980249
theorem B5768999 : Blo 1895435 5768999 := bstep (se 1 (by rfl) ⟨4326749, by rfl⟩ : syracuseStep 5768999 = 8653499) B8653499
theorem B3845999 : Blo 1895435 3845999 := bstep (se 1 (by rfl) ⟨2884499, by rfl⟩ : syracuseStep 3845999 = 5768999) B5768999
theorem B10255997 : Blo 1895435 10255997 := bstep (se 3 (by rfl) ⟨1922999, by rfl⟩ : syracuseStep 10255997 = 3845999) B3845999
theorem B27349325 : Blo 1895435 27349325 := bstep (se 3 (by rfl) ⟨5127998, by rfl⟩ : syracuseStep 27349325 = 10255997) B10255997
theorem B18232883 : Blo 1895435 18232883 := bstep (se 1 (by rfl) ⟨13674662, by rfl⟩ : syracuseStep 18232883 = 27349325) B27349325
theorem B12155255 : Blo 1895435 12155255 := bstep (se 1 (by rfl) ⟨9116441, by rfl⟩ : syracuseStep 12155255 = 18232883) B18232883
theorem B8103503 : Blo 1895435 8103503 := bstep (se 1 (by rfl) ⟨6077627, by rfl⟩ : syracuseStep 8103503 = 12155255) B12155255
theorem B5402335 : Blo 1895435 5402335 := bstep (se 1 (by rfl) ⟨4051751, by rfl⟩ : syracuseStep 5402335 = 8103503) B8103503
theorem B7203113 : Blo 1895435 7203113 := bstep (se 2 (by rfl) ⟨2701167, by rfl⟩ : syracuseStep 7203113 = 5402335) B5402335
theorem B4802075 : Blo 1895435 4802075 := bstep (se 1 (by rfl) ⟨3601556, by rfl⟩ : syracuseStep 4802075 = 7203113) B7203113
theorem B3201383 : Blo 1895435 3201383 := bstep (se 1 (by rfl) ⟨2401037, by rfl⟩ : syracuseStep 3201383 = 4802075) B4802075
theorem B2134255 : Blo 1895435 2134255 := bstep (se 1 (by rfl) ⟨1600691, by rfl⟩ : syracuseStep 2134255 = 3201383) B3201383
theorem B2845673 : Blo 1895435 2845673 := bstep (se 2 (by rfl) ⟨1067127, by rfl⟩ : syracuseStep 2845673 = 2134255) B2134255
theorem B1897115 : Blo 1895435 1897115 := bstep (se 1 (by rfl) ⟨1422836, by rfl⟩ : syracuseStep 1897115 = 2845673) B2845673
theorem B3245069 : Blo 1895435 3245069 := bbase (se 3 (by rfl) ⟨608450, by rfl⟩ : syracuseStep 3245069 = 1216901) (by norm_num)
theorem B2163379 : Blo 1895435 2163379 := bstep (se 1 (by rfl) ⟨1622534, by rfl⟩ : syracuseStep 2163379 = 3245069) B3245069
theorem B2884505 : Blo 1895435 2884505 := bstep (se 2 (by rfl) ⟨1081689, by rfl⟩ : syracuseStep 2884505 = 2163379) B2163379
theorem B7692013 : Blo 1895435 7692013 := bstep (se 3 (by rfl) ⟨1442252, by rfl⟩ : syracuseStep 7692013 = 2884505) B2884505
theorem B10256017 : Blo 1895435 10256017 := bstep (se 2 (by rfl) ⟨3846006, by rfl⟩ : syracuseStep 10256017 = 7692013) B7692013
theorem B13674689 : Blo 1895435 13674689 := bstep (se 2 (by rfl) ⟨5128008, by rfl⟩ : syracuseStep 13674689 = 10256017) B10256017
theorem B9116459 : Blo 1895435 9116459 := bstep (se 1 (by rfl) ⟨6837344, by rfl⟩ : syracuseStep 9116459 = 13674689) B13674689
theorem B6077639 : Blo 1895435 6077639 := bstep (se 1 (by rfl) ⟨4558229, by rfl⟩ : syracuseStep 6077639 = 9116459) B9116459
theorem B16207037 : Blo 1895435 16207037 := bstep (se 3 (by rfl) ⟨3038819, by rfl⟩ : syracuseStep 16207037 = 6077639) B6077639
theorem B10804691 : Blo 1895435 10804691 := bstep (se 1 (by rfl) ⟨8103518, by rfl⟩ : syracuseStep 10804691 = 16207037) B16207037
theorem B7203127 : Blo 1895435 7203127 := bstep (se 1 (by rfl) ⟨5402345, by rfl⟩ : syracuseStep 7203127 = 10804691) B10804691
theorem B9604169 : Blo 1895435 9604169 := bstep (se 2 (by rfl) ⟨3601563, by rfl⟩ : syracuseStep 9604169 = 7203127) B7203127
theorem B6402779 : Blo 1895435 6402779 := bstep (se 1 (by rfl) ⟨4802084, by rfl⟩ : syracuseStep 6402779 = 9604169) B9604169
theorem B4268519 : Blo 1895435 4268519 := bstep (se 1 (by rfl) ⟨3201389, by rfl⟩ : syracuseStep 4268519 = 6402779) B6402779
theorem B2845679 : Blo 1895435 2845679 := bstep (se 1 (by rfl) ⟨2134259, by rfl⟩ : syracuseStep 2845679 = 4268519) B4268519
theorem B1897119 : Blo 1895435 1897119 := bstep (se 1 (by rfl) ⟨1422839, by rfl⟩ : syracuseStep 1897119 = 2845679) B2845679
theorem B2845685 : Blo 1895435 2845685 := bbase (se 5 (by rfl) ⟨133391, by rfl⟩ : syracuseStep 2845685 = 266783) (by norm_num)
theorem B1897123 : Blo 1895435 1897123 := bstep (se 1 (by rfl) ⟨1422842, by rfl⟩ : syracuseStep 1897123 = 2845685) B2845685
theorem B2279125 : Blo 1895435 2279125 := bbase (se 7 (by rfl) ⟨26708, by rfl⟩ : syracuseStep 2279125 = 53417) (by norm_num)
theorem B3038833 : Blo 1895435 3038833 := bstep (se 2 (by rfl) ⟨1139562, by rfl⟩ : syracuseStep 3038833 = 2279125) B2279125
theorem B4051777 : Blo 1895435 4051777 := bstep (se 2 (by rfl) ⟨1519416, by rfl⟩ : syracuseStep 4051777 = 3038833) B3038833
theorem B5402369 : Blo 1895435 5402369 := bstep (se 2 (by rfl) ⟨2025888, by rfl⟩ : syracuseStep 5402369 = 4051777) B4051777
theorem B3601579 : Blo 1895435 3601579 := bstep (se 1 (by rfl) ⟨2701184, by rfl⟩ : syracuseStep 3601579 = 5402369) B5402369
theorem B4802105 : Blo 1895435 4802105 := bstep (se 2 (by rfl) ⟨1800789, by rfl⟩ : syracuseStep 4802105 = 3601579) B3601579
theorem B3201403 : Blo 1895435 3201403 := bstep (se 1 (by rfl) ⟨2401052, by rfl⟩ : syracuseStep 3201403 = 4802105) B4802105
theorem B4268537 : Blo 1895435 4268537 := bstep (se 2 (by rfl) ⟨1600701, by rfl⟩ : syracuseStep 4268537 = 3201403) B3201403
theorem B2845691 : Blo 1895435 2845691 := bstep (se 1 (by rfl) ⟨2134268, by rfl⟩ : syracuseStep 2845691 = 4268537) B4268537
theorem B1897127 : Blo 1895435 1897127 := bstep (se 1 (by rfl) ⟨1422845, by rfl⟩ : syracuseStep 1897127 = 2845691) B2845691
theorem B2134273 : Blo 1895435 2134273 := bbase (se 2 (by rfl) ⟨800352, by rfl⟩ : syracuseStep 2134273 = 1600705) (by norm_num)
theorem B2845697 : Blo 1895435 2845697 := bstep (se 2 (by rfl) ⟨1067136, by rfl⟩ : syracuseStep 2845697 = 2134273) B2134273
theorem B1897131 : Blo 1895435 1897131 := bstep (se 1 (by rfl) ⟨1422848, by rfl⟩ : syracuseStep 1897131 = 2845697) B2845697
theorem B4802125 : Blo 1895435 4802125 := bbase (se 3 (by rfl) ⟨900398, by rfl⟩ : syracuseStep 4802125 = 1800797) (by norm_num)
theorem B6402833 : Blo 1895435 6402833 := bstep (se 2 (by rfl) ⟨2401062, by rfl⟩ : syracuseStep 6402833 = 4802125) B4802125
theorem B4268555 : Blo 1895435 4268555 := bstep (se 1 (by rfl) ⟨3201416, by rfl⟩ : syracuseStep 4268555 = 6402833) B6402833
theorem B2845703 : Blo 1895435 2845703 := bstep (se 1 (by rfl) ⟨2134277, by rfl⟩ : syracuseStep 2845703 = 4268555) B4268555
theorem B1897135 : Blo 1895435 1897135 := bstep (se 1 (by rfl) ⟨1422851, by rfl⟩ : syracuseStep 1897135 = 2845703) B2845703
theorem B2845709 : Blo 1895435 2845709 := bbase (se 3 (by rfl) ⟨533570, by rfl⟩ : syracuseStep 2845709 = 1067141) (by norm_num)
theorem B1897139 : Blo 1895435 1897139 := bstep (se 1 (by rfl) ⟨1422854, by rfl⟩ : syracuseStep 1897139 = 2845709) B2845709
theorem B4268573 : Blo 1895435 4268573 := bbase (se 3 (by rfl) ⟨800357, by rfl⟩ : syracuseStep 4268573 = 1600715) (by norm_num)
theorem B2845715 : Blo 1895435 2845715 := bstep (se 1 (by rfl) ⟨2134286, by rfl⟩ : syracuseStep 2845715 = 4268573) B4268573
theorem B1897143 : Blo 1895435 1897143 := bstep (se 1 (by rfl) ⟨1422857, by rfl⟩ : syracuseStep 1897143 = 2845715) B2845715
theorem B3201437 : Blo 1895435 3201437 := bbase (se 3 (by rfl) ⟨600269, by rfl⟩ : syracuseStep 3201437 = 1200539) (by norm_num)
theorem B2134291 : Blo 1895435 2134291 := bstep (se 1 (by rfl) ⟨1600718, by rfl⟩ : syracuseStep 2134291 = 3201437) B3201437
theorem B2845721 : Blo 1895435 2845721 := bstep (se 2 (by rfl) ⟨1067145, by rfl⟩ : syracuseStep 2845721 = 2134291) B2134291
theorem B1897147 : Blo 1895435 1897147 := bstep (se 1 (by rfl) ⟨1422860, by rfl⟩ : syracuseStep 1897147 = 2845721) B2845721
theorem B25960981 : Blo 1895435 25960981 := bbase (se 6 (by rfl) ⟨608460, by rfl⟩ : syracuseStep 25960981 = 1216921) (by norm_num)
theorem B34614641 : Blo 1895435 34614641 := bstep (se 2 (by rfl) ⟨12980490, by rfl⟩ : syracuseStep 34614641 = 25960981) B25960981
theorem B23076427 : Blo 1895435 23076427 := bstep (se 1 (by rfl) ⟨17307320, by rfl⟩ : syracuseStep 23076427 = 34614641) B34614641
theorem B30768569 : Blo 1895435 30768569 := bstep (se 2 (by rfl) ⟨11538213, by rfl⟩ : syracuseStep 30768569 = 23076427) B23076427
theorem B20512379 : Blo 1895435 20512379 := bstep (se 1 (by rfl) ⟨15384284, by rfl⟩ : syracuseStep 20512379 = 30768569) B30768569
theorem B13674919 : Blo 1895435 13674919 := bstep (se 1 (by rfl) ⟨10256189, by rfl⟩ : syracuseStep 13674919 = 20512379) B20512379
theorem B18233225 : Blo 1895435 18233225 := bstep (se 2 (by rfl) ⟨6837459, by rfl⟩ : syracuseStep 18233225 = 13674919) B13674919
theorem B12155483 : Blo 1895435 12155483 := bstep (se 1 (by rfl) ⟨9116612, by rfl⟩ : syracuseStep 12155483 = 18233225) B18233225
theorem B8103655 : Blo 1895435 8103655 := bstep (se 1 (by rfl) ⟨6077741, by rfl⟩ : syracuseStep 8103655 = 12155483) B12155483
theorem B10804873 : Blo 1895435 10804873 := bstep (se 2 (by rfl) ⟨4051827, by rfl⟩ : syracuseStep 10804873 = 8103655) B8103655
theorem B14406497 : Blo 1895435 14406497 := bstep (se 2 (by rfl) ⟨5402436, by rfl⟩ : syracuseStep 14406497 = 10804873) B10804873
theorem B9604331 : Blo 1895435 9604331 := bstep (se 1 (by rfl) ⟨7203248, by rfl⟩ : syracuseStep 9604331 = 14406497) B14406497
theorem B6402887 : Blo 1895435 6402887 := bstep (se 1 (by rfl) ⟨4802165, by rfl⟩ : syracuseStep 6402887 = 9604331) B9604331
theorem B4268591 : Blo 1895435 4268591 := bstep (se 1 (by rfl) ⟨3201443, by rfl⟩ : syracuseStep 4268591 = 6402887) B6402887
theorem B2845727 : Blo 1895435 2845727 := bstep (se 1 (by rfl) ⟨2134295, by rfl⟩ : syracuseStep 2845727 = 4268591) B4268591
theorem B1897151 : Blo 1895435 1897151 := bstep (se 1 (by rfl) ⟨1422863, by rfl⟩ : syracuseStep 1897151 = 2845727) B2845727
theorem B2845733 : Blo 1895435 2845733 := bbase (se 4 (by rfl) ⟨266787, by rfl⟩ : syracuseStep 2845733 = 533575) (by norm_num)
theorem B1897155 : Blo 1895435 1897155 := bstep (se 1 (by rfl) ⟨1422866, by rfl⟩ : syracuseStep 1897155 = 2845733) B2845733
theorem B2401093 : Blo 1895435 2401093 := bbase (se 4 (by rfl) ⟨225102, by rfl⟩ : syracuseStep 2401093 = 450205) (by norm_num)
theorem B3201457 : Blo 1895435 3201457 := bstep (se 2 (by rfl) ⟨1200546, by rfl⟩ : syracuseStep 3201457 = 2401093) B2401093
theorem B4268609 : Blo 1895435 4268609 := bstep (se 2 (by rfl) ⟨1600728, by rfl⟩ : syracuseStep 4268609 = 3201457) B3201457
theorem B2845739 : Blo 1895435 2845739 := bstep (se 1 (by rfl) ⟨2134304, by rfl⟩ : syracuseStep 2845739 = 4268609) B4268609
theorem B1897159 : Blo 1895435 1897159 := bstep (se 1 (by rfl) ⟨1422869, by rfl⟩ : syracuseStep 1897159 = 2845739) B2845739
theorem B2134309 : Blo 1895435 2134309 := bbase (se 4 (by rfl) ⟨200091, by rfl⟩ : syracuseStep 2134309 = 400183) (by norm_num)
theorem B2845745 : Blo 1895435 2845745 := bstep (se 2 (by rfl) ⟨1067154, by rfl⟩ : syracuseStep 2845745 = 2134309) B2134309
theorem B1897163 : Blo 1895435 1897163 := bstep (se 1 (by rfl) ⟨1422872, by rfl⟩ : syracuseStep 1897163 = 2845745) B2845745
theorem B2279173 : Blo 1895435 2279173 := bbase (se 4 (by rfl) ⟨213672, by rfl⟩ : syracuseStep 2279173 = 427345) (by norm_num)
theorem B3038897 : Blo 1895435 3038897 := bstep (se 2 (by rfl) ⟨1139586, by rfl⟩ : syracuseStep 3038897 = 2279173) B2279173
theorem B8103725 : Blo 1895435 8103725 := bstep (se 3 (by rfl) ⟨1519448, by rfl⟩ : syracuseStep 8103725 = 3038897) B3038897
theorem B5402483 : Blo 1895435 5402483 := bstep (se 1 (by rfl) ⟨4051862, by rfl⟩ : syracuseStep 5402483 = 8103725) B8103725
theorem B3601655 : Blo 1895435 3601655 := bstep (se 1 (by rfl) ⟨2701241, by rfl⟩ : syracuseStep 3601655 = 5402483) B5402483
theorem B2401103 : Blo 1895435 2401103 := bstep (se 1 (by rfl) ⟨1800827, by rfl⟩ : syracuseStep 2401103 = 3601655) B3601655
theorem B6402941 : Blo 1895435 6402941 := bstep (se 3 (by rfl) ⟨1200551, by rfl⟩ : syracuseStep 6402941 = 2401103) B2401103
theorem B4268627 : Blo 1895435 4268627 := bstep (se 1 (by rfl) ⟨3201470, by rfl⟩ : syracuseStep 4268627 = 6402941) B6402941
theorem B2845751 : Blo 1895435 2845751 := bstep (se 1 (by rfl) ⟨2134313, by rfl⟩ : syracuseStep 2845751 = 4268627) B4268627
theorem B1897167 : Blo 1895435 1897167 := bstep (se 1 (by rfl) ⟨1422875, by rfl⟩ : syracuseStep 1897167 = 2845751) B2845751
theorem B2845757 : Blo 1895435 2845757 := bbase (se 3 (by rfl) ⟨533579, by rfl⟩ : syracuseStep 2845757 = 1067159) (by norm_num)
theorem B1897171 : Blo 1895435 1897171 := bstep (se 1 (by rfl) ⟨1422878, by rfl⟩ : syracuseStep 1897171 = 2845757) B2845757
theorem B4268645 : Blo 1895435 4268645 := bbase (se 4 (by rfl) ⟨400185, by rfl⟩ : syracuseStep 4268645 = 800371) (by norm_num)
theorem B2845763 : Blo 1895435 2845763 := bstep (se 1 (by rfl) ⟨2134322, by rfl⟩ : syracuseStep 2845763 = 4268645) B4268645
theorem B1897175 : Blo 1895435 1897175 := bstep (se 1 (by rfl) ⟨1422881, by rfl⟩ : syracuseStep 1897175 = 2845763) B2845763
theorem B4802237 : Blo 1895435 4802237 := bbase (se 3 (by rfl) ⟨900419, by rfl⟩ : syracuseStep 4802237 = 1800839) (by norm_num)
theorem B3201491 : Blo 1895435 3201491 := bstep (se 1 (by rfl) ⟨2401118, by rfl⟩ : syracuseStep 3201491 = 4802237) B4802237
theorem B2134327 : Blo 1895435 2134327 := bstep (se 1 (by rfl) ⟨1600745, by rfl⟩ : syracuseStep 2134327 = 3201491) B3201491
theorem B2845769 : Blo 1895435 2845769 := bstep (se 2 (by rfl) ⟨1067163, by rfl⟩ : syracuseStep 2845769 = 2134327) B2134327
theorem B1897179 : Blo 1895435 1897179 := bstep (se 1 (by rfl) ⟨1422884, by rfl⟩ : syracuseStep 1897179 = 2845769) B2845769
theorem B3601685 : Blo 1895435 3601685 := bbase (se 6 (by rfl) ⟨84414, by rfl⟩ : syracuseStep 3601685 = 168829) (by norm_num)
theorem B9604493 : Blo 1895435 9604493 := bstep (se 3 (by rfl) ⟨1800842, by rfl⟩ : syracuseStep 9604493 = 3601685) B3601685
theorem B6402995 : Blo 1895435 6402995 := bstep (se 1 (by rfl) ⟨4802246, by rfl⟩ : syracuseStep 6402995 = 9604493) B9604493
theorem B4268663 : Blo 1895435 4268663 := bstep (se 1 (by rfl) ⟨3201497, by rfl⟩ : syracuseStep 4268663 = 6402995) B6402995
theorem B2845775 : Blo 1895435 2845775 := bstep (se 1 (by rfl) ⟨2134331, by rfl⟩ : syracuseStep 2845775 = 4268663) B4268663
theorem B1897183 : Blo 1895435 1897183 := bstep (se 1 (by rfl) ⟨1422887, by rfl⟩ : syracuseStep 1897183 = 2845775) B2845775
theorem B2845781 : Blo 1895435 2845781 := bbase (se 8 (by rfl) ⟨16674, by rfl⟩ : syracuseStep 2845781 = 33349) (by norm_num)
theorem B1897187 : Blo 1895435 1897187 := bstep (se 1 (by rfl) ⟨1422890, by rfl⟩ : syracuseStep 1897187 = 2845781) B2845781
theorem B6837605 : Blo 1895435 6837605 := bbase (se 4 (by rfl) ⟨641025, by rfl⟩ : syracuseStep 6837605 = 1282051) (by norm_num)
theorem B4558403 : Blo 1895435 4558403 := bstep (se 1 (by rfl) ⟨3418802, by rfl⟩ : syracuseStep 4558403 = 6837605) B6837605
theorem B12155741 : Blo 1895435 12155741 := bstep (se 3 (by rfl) ⟨2279201, by rfl⟩ : syracuseStep 12155741 = 4558403) B4558403
theorem B8103827 : Blo 1895435 8103827 := bstep (se 1 (by rfl) ⟨6077870, by rfl⟩ : syracuseStep 8103827 = 12155741) B12155741
theorem B5402551 : Blo 1895435 5402551 := bstep (se 1 (by rfl) ⟨4051913, by rfl⟩ : syracuseStep 5402551 = 8103827) B8103827
theorem B7203401 : Blo 1895435 7203401 := bstep (se 2 (by rfl) ⟨2701275, by rfl⟩ : syracuseStep 7203401 = 5402551) B5402551
theorem B4802267 : Blo 1895435 4802267 := bstep (se 1 (by rfl) ⟨3601700, by rfl⟩ : syracuseStep 4802267 = 7203401) B7203401
theorem B3201511 : Blo 1895435 3201511 := bstep (se 1 (by rfl) ⟨2401133, by rfl⟩ : syracuseStep 3201511 = 4802267) B4802267
theorem B4268681 : Blo 1895435 4268681 := bstep (se 2 (by rfl) ⟨1600755, by rfl⟩ : syracuseStep 4268681 = 3201511) B3201511
theorem B2845787 : Blo 1895435 2845787 := bstep (se 1 (by rfl) ⟨2134340, by rfl⟩ : syracuseStep 2845787 = 4268681) B4268681
theorem B1897191 : Blo 1895435 1897191 := bstep (se 1 (by rfl) ⟨1422893, by rfl⟩ : syracuseStep 1897191 = 2845787) B2845787
theorem B2134345 : Blo 1895435 2134345 := bbase (se 2 (by rfl) ⟨800379, by rfl⟩ : syracuseStep 2134345 = 1600759) (by norm_num)
theorem B2845793 : Blo 1895435 2845793 := bstep (se 2 (by rfl) ⟨1067172, by rfl⟩ : syracuseStep 2845793 = 2134345) B2134345
theorem B1897195 : Blo 1895435 1897195 := bstep (se 1 (by rfl) ⟨1422896, by rfl⟩ : syracuseStep 1897195 = 2845793) B2845793
theorem B5769253 : Blo 1895435 5769253 := bbase (se 4 (by rfl) ⟨540867, by rfl⟩ : syracuseStep 5769253 = 1081735) (by norm_num)
theorem B7692337 : Blo 1895435 7692337 := bstep (se 2 (by rfl) ⟨2884626, by rfl⟩ : syracuseStep 7692337 = 5769253) B5769253
theorem B41025797 : Blo 1895435 41025797 := bstep (se 4 (by rfl) ⟨3846168, by rfl⟩ : syracuseStep 41025797 = 7692337) B7692337
theorem B27350531 : Blo 1895435 27350531 := bstep (se 1 (by rfl) ⟨20512898, by rfl⟩ : syracuseStep 27350531 = 41025797) B41025797
theorem B18233687 : Blo 1895435 18233687 := bstep (se 1 (by rfl) ⟨13675265, by rfl⟩ : syracuseStep 18233687 = 27350531) B27350531
theorem B12155791 : Blo 1895435 12155791 := bstep (se 1 (by rfl) ⟨9116843, by rfl⟩ : syracuseStep 12155791 = 18233687) B18233687
theorem B16207721 : Blo 1895435 16207721 := bstep (se 2 (by rfl) ⟨6077895, by rfl⟩ : syracuseStep 16207721 = 12155791) B12155791
theorem B10805147 : Blo 1895435 10805147 := bstep (se 1 (by rfl) ⟨8103860, by rfl⟩ : syracuseStep 10805147 = 16207721) B16207721
theorem B7203431 : Blo 1895435 7203431 := bstep (se 1 (by rfl) ⟨5402573, by rfl⟩ : syracuseStep 7203431 = 10805147) B10805147
theorem B4802287 : Blo 1895435 4802287 := bstep (se 1 (by rfl) ⟨3601715, by rfl⟩ : syracuseStep 4802287 = 7203431) B7203431
theorem B6403049 : Blo 1895435 6403049 := bstep (se 2 (by rfl) ⟨2401143, by rfl⟩ : syracuseStep 6403049 = 4802287) B4802287
theorem B4268699 : Blo 1895435 4268699 := bstep (se 1 (by rfl) ⟨3201524, by rfl⟩ : syracuseStep 4268699 = 6403049) B6403049
theorem B2845799 : Blo 1895435 2845799 := bstep (se 1 (by rfl) ⟨2134349, by rfl⟩ : syracuseStep 2845799 = 4268699) B4268699
theorem B1897199 : Blo 1895435 1897199 := bstep (se 1 (by rfl) ⟨1422899, by rfl⟩ : syracuseStep 1897199 = 2845799) B2845799
theorem B2845805 : Blo 1895435 2845805 := bbase (se 3 (by rfl) ⟨533588, by rfl⟩ : syracuseStep 2845805 = 1067177) (by norm_num)
theorem B1897203 : Blo 1895435 1897203 := bstep (se 1 (by rfl) ⟨1422902, by rfl⟩ : syracuseStep 1897203 = 2845805) B2845805
theorem B4268717 : Blo 1895435 4268717 := bbase (se 3 (by rfl) ⟨800384, by rfl⟩ : syracuseStep 4268717 = 1600769) (by norm_num)
theorem B2845811 : Blo 1895435 2845811 := bstep (se 1 (by rfl) ⟨2134358, by rfl⟩ : syracuseStep 2845811 = 4268717) B4268717
theorem B1897207 : Blo 1895435 1897207 := bstep (se 1 (by rfl) ⟨1422905, by rfl⟩ : syracuseStep 1897207 = 2845811) B2845811
theorem B4051957 : Blo 1895435 4051957 := bbase (se 5 (by rfl) ⟨189935, by rfl⟩ : syracuseStep 4051957 = 379871) (by norm_num)
theorem B5402609 : Blo 1895435 5402609 := bstep (se 2 (by rfl) ⟨2025978, by rfl⟩ : syracuseStep 5402609 = 4051957) B4051957
theorem B3601739 : Blo 1895435 3601739 := bstep (se 1 (by rfl) ⟨2701304, by rfl⟩ : syracuseStep 3601739 = 5402609) B5402609
theorem B2401159 : Blo 1895435 2401159 := bstep (se 1 (by rfl) ⟨1800869, by rfl⟩ : syracuseStep 2401159 = 3601739) B3601739
theorem B3201545 : Blo 1895435 3201545 := bstep (se 2 (by rfl) ⟨1200579, by rfl⟩ : syracuseStep 3201545 = 2401159) B2401159
theorem B2134363 : Blo 1895435 2134363 := bstep (se 1 (by rfl) ⟨1600772, by rfl⟩ : syracuseStep 2134363 = 3201545) B3201545
theorem B2845817 : Blo 1895435 2845817 := bstep (se 2 (by rfl) ⟨1067181, by rfl⟩ : syracuseStep 2845817 = 2134363) B2134363
theorem B1897211 : Blo 1895435 1897211 := bstep (se 1 (by rfl) ⟨1422908, by rfl⟩ : syracuseStep 1897211 = 2845817) B2845817
theorem B2599117 : Blo 1895435 2599117 := bbase (se 3 (by rfl) ⟨487334, by rfl⟩ : syracuseStep 2599117 = 974669) (by norm_num)
theorem B55447829 : Blo 1895435 55447829 := bstep (se 6 (by rfl) ⟨1299558, by rfl⟩ : syracuseStep 55447829 = 2599117) B2599117
theorem B36965219 : Blo 1895435 36965219 := bstep (se 1 (by rfl) ⟨27723914, by rfl⟩ : syracuseStep 36965219 = 55447829) B55447829
theorem B98573917 : Blo 1895435 98573917 := bstep (se 3 (by rfl) ⟨18482609, by rfl⟩ : syracuseStep 98573917 = 36965219) B36965219
theorem B131431889 : Blo 1895435 131431889 := bstep (se 2 (by rfl) ⟨49286958, by rfl⟩ : syracuseStep 131431889 = 98573917) B98573917
theorem B87621259 : Blo 1895435 87621259 := bstep (se 1 (by rfl) ⟨65715944, by rfl⟩ : syracuseStep 87621259 = 131431889) B131431889
theorem B116828345 : Blo 1895435 116828345 := bstep (se 2 (by rfl) ⟨43810629, by rfl⟩ : syracuseStep 116828345 = 87621259) B87621259
theorem B77885563 : Blo 1895435 77885563 := bstep (se 1 (by rfl) ⟨58414172, by rfl⟩ : syracuseStep 77885563 = 116828345) B116828345
theorem B103847417 : Blo 1895435 103847417 := bstep (se 2 (by rfl) ⟨38942781, by rfl⟩ : syracuseStep 103847417 = 77885563) B77885563
theorem B69231611 : Blo 1895435 69231611 := bstep (se 1 (by rfl) ⟨51923708, by rfl⟩ : syracuseStep 69231611 = 103847417) B103847417
theorem B46154407 : Blo 1895435 46154407 := bstep (se 1 (by rfl) ⟨34615805, by rfl⟩ : syracuseStep 46154407 = 69231611) B69231611
theorem B61539209 : Blo 1895435 61539209 := bstep (se 2 (by rfl) ⟨23077203, by rfl⟩ : syracuseStep 61539209 = 46154407) B46154407
theorem B41026139 : Blo 1895435 41026139 := bstep (se 1 (by rfl) ⟨30769604, by rfl⟩ : syracuseStep 41026139 = 61539209) B61539209
theorem B27350759 : Blo 1895435 27350759 := bstep (se 1 (by rfl) ⟨20513069, by rfl⟩ : syracuseStep 27350759 = 41026139) B41026139
theorem B18233839 : Blo 1895435 18233839 := bstep (se 1 (by rfl) ⟨13675379, by rfl⟩ : syracuseStep 18233839 = 27350759) B27350759
theorem B24311785 : Blo 1895435 24311785 := bstep (se 2 (by rfl) ⟨9116919, by rfl⟩ : syracuseStep 24311785 = 18233839) B18233839
theorem B32415713 : Blo 1895435 32415713 := bstep (se 2 (by rfl) ⟨12155892, by rfl⟩ : syracuseStep 32415713 = 24311785) B24311785
theorem B21610475 : Blo 1895435 21610475 := bstep (se 1 (by rfl) ⟨16207856, by rfl⟩ : syracuseStep 21610475 = 32415713) B32415713
theorem B14406983 : Blo 1895435 14406983 := bstep (se 1 (by rfl) ⟨10805237, by rfl⟩ : syracuseStep 14406983 = 21610475) B21610475
theorem B9604655 : Blo 1895435 9604655 := bstep (se 1 (by rfl) ⟨7203491, by rfl⟩ : syracuseStep 9604655 = 14406983) B14406983
theorem B6403103 : Blo 1895435 6403103 := bstep (se 1 (by rfl) ⟨4802327, by rfl⟩ : syracuseStep 6403103 = 9604655) B9604655
theorem B4268735 : Blo 1895435 4268735 := bstep (se 1 (by rfl) ⟨3201551, by rfl⟩ : syracuseStep 4268735 = 6403103) B6403103
theorem B2845823 : Blo 1895435 2845823 := bstep (se 1 (by rfl) ⟨2134367, by rfl⟩ : syracuseStep 2845823 = 4268735) B4268735
theorem B1897215 : Blo 1895435 1897215 := bstep (se 1 (by rfl) ⟨1422911, by rfl⟩ : syracuseStep 1897215 = 2845823) B2845823
theorem B2845829 : Blo 1895435 2845829 := bbase (se 4 (by rfl) ⟨266796, by rfl⟩ : syracuseStep 2845829 = 533593) (by norm_num)
theorem B1897219 : Blo 1895435 1897219 := bstep (se 1 (by rfl) ⟨1422914, by rfl⟩ : syracuseStep 1897219 = 2845829) B2845829
theorem B3201565 : Blo 1895435 3201565 := bbase (se 3 (by rfl) ⟨600293, by rfl⟩ : syracuseStep 3201565 = 1200587) (by norm_num)
theorem B4268753 : Blo 1895435 4268753 := bstep (se 2 (by rfl) ⟨1600782, by rfl⟩ : syracuseStep 4268753 = 3201565) B3201565
theorem B2845835 : Blo 1895435 2845835 := bstep (se 1 (by rfl) ⟨2134376, by rfl⟩ : syracuseStep 2845835 = 4268753) B4268753
theorem B1897223 : Blo 1895435 1897223 := bstep (se 1 (by rfl) ⟨1422917, by rfl⟩ : syracuseStep 1897223 = 2845835) B2845835
theorem B2134381 : Blo 1895435 2134381 := bbase (se 3 (by rfl) ⟨400196, by rfl⟩ : syracuseStep 2134381 = 800393) (by norm_num)
theorem B2845841 : Blo 1895435 2845841 := bstep (se 2 (by rfl) ⟨1067190, by rfl⟩ : syracuseStep 2845841 = 2134381) B2134381
theorem B1897227 : Blo 1895435 1897227 := bstep (se 1 (by rfl) ⟨1422920, by rfl⟩ : syracuseStep 1897227 = 2845841) B2845841
theorem B6403157 : Blo 1895435 6403157 := bbase (se 8 (by rfl) ⟨37518, by rfl⟩ : syracuseStep 6403157 = 75037) (by norm_num)
theorem B4268771 : Blo 1895435 4268771 := bstep (se 1 (by rfl) ⟨3201578, by rfl⟩ : syracuseStep 4268771 = 6403157) B6403157
theorem B2845847 : Blo 1895435 2845847 := bstep (se 1 (by rfl) ⟨2134385, by rfl⟩ : syracuseStep 2845847 = 4268771) B4268771
theorem B1897231 : Blo 1895435 1897231 := bstep (se 1 (by rfl) ⟨1422923, by rfl⟩ : syracuseStep 1897231 = 2845847) B2845847
theorem B2845853 : Blo 1895435 2845853 := bbase (se 3 (by rfl) ⟨533597, by rfl⟩ : syracuseStep 2845853 = 1067195) (by norm_num)
theorem B1897235 : Blo 1895435 1897235 := bstep (se 1 (by rfl) ⟨1422926, by rfl⟩ : syracuseStep 1897235 = 2845853) B2845853
theorem B4268789 : Blo 1895435 4268789 := bbase (se 5 (by rfl) ⟨200099, by rfl⟩ : syracuseStep 4268789 = 400199) (by norm_num)
theorem B2845859 : Blo 1895435 2845859 := bstep (se 1 (by rfl) ⟨2134394, by rfl⟩ : syracuseStep 2845859 = 4268789) B4268789
theorem B1897239 : Blo 1895435 1897239 := bstep (se 1 (by rfl) ⟨1422929, by rfl⟩ : syracuseStep 1897239 = 2845859) B2845859
theorem B24312149 : Blo 1895435 24312149 := bbase (se 10 (by rfl) ⟨35613, by rfl⟩ : syracuseStep 24312149 = 71227) (by norm_num)
theorem B16208099 : Blo 1895435 16208099 := bstep (se 1 (by rfl) ⟨12156074, by rfl⟩ : syracuseStep 16208099 = 24312149) B24312149
theorem B10805399 : Blo 1895435 10805399 := bstep (se 1 (by rfl) ⟨8104049, by rfl⟩ : syracuseStep 10805399 = 16208099) B16208099
theorem B7203599 : Blo 1895435 7203599 := bstep (se 1 (by rfl) ⟨5402699, by rfl⟩ : syracuseStep 7203599 = 10805399) B10805399
theorem B4802399 : Blo 1895435 4802399 := bstep (se 1 (by rfl) ⟨3601799, by rfl⟩ : syracuseStep 4802399 = 7203599) B7203599
theorem B3201599 : Blo 1895435 3201599 := bstep (se 1 (by rfl) ⟨2401199, by rfl⟩ : syracuseStep 3201599 = 4802399) B4802399
theorem B2134399 : Blo 1895435 2134399 := bstep (se 1 (by rfl) ⟨1600799, by rfl⟩ : syracuseStep 2134399 = 3201599) B3201599
theorem B2845865 : Blo 1895435 2845865 := bstep (se 2 (by rfl) ⟨1067199, by rfl⟩ : syracuseStep 2845865 = 2134399) B2134399
theorem B1897243 : Blo 1895435 1897243 := bstep (se 1 (by rfl) ⟨1422932, by rfl⟩ : syracuseStep 1897243 = 2845865) B2845865
theorem B2279269 : Blo 1895435 2279269 := bbase (se 4 (by rfl) ⟨213681, by rfl⟩ : syracuseStep 2279269 = 427363) (by norm_num)
theorem B3039025 : Blo 1895435 3039025 := bstep (se 2 (by rfl) ⟨1139634, by rfl⟩ : syracuseStep 3039025 = 2279269) B2279269
theorem B4052033 : Blo 1895435 4052033 := bstep (se 2 (by rfl) ⟨1519512, by rfl⟩ : syracuseStep 4052033 = 3039025) B3039025
theorem B2701355 : Blo 1895435 2701355 := bstep (se 1 (by rfl) ⟨2026016, by rfl⟩ : syracuseStep 2701355 = 4052033) B4052033
theorem B7203613 : Blo 1895435 7203613 := bstep (se 3 (by rfl) ⟨1350677, by rfl⟩ : syracuseStep 7203613 = 2701355) B2701355
theorem B9604817 : Blo 1895435 9604817 := bstep (se 2 (by rfl) ⟨3601806, by rfl⟩ : syracuseStep 9604817 = 7203613) B7203613
theorem B6403211 : Blo 1895435 6403211 := bstep (se 1 (by rfl) ⟨4802408, by rfl⟩ : syracuseStep 6403211 = 9604817) B9604817
theorem B4268807 : Blo 1895435 4268807 := bstep (se 1 (by rfl) ⟨3201605, by rfl⟩ : syracuseStep 4268807 = 6403211) B6403211
theorem B2845871 : Blo 1895435 2845871 := bstep (se 1 (by rfl) ⟨2134403, by rfl⟩ : syracuseStep 2845871 = 4268807) B4268807
theorem B1897247 : Blo 1895435 1897247 := bstep (se 1 (by rfl) ⟨1422935, by rfl⟩ : syracuseStep 1897247 = 2845871) B2845871
theorem B2845877 : Blo 1895435 2845877 := bbase (se 5 (by rfl) ⟨133400, by rfl⟩ : syracuseStep 2845877 = 266801) (by norm_num)
theorem B1897251 : Blo 1895435 1897251 := bstep (se 1 (by rfl) ⟨1422938, by rfl⟩ : syracuseStep 1897251 = 2845877) B2845877
theorem B4802429 : Blo 1895435 4802429 := bbase (se 3 (by rfl) ⟨900455, by rfl⟩ : syracuseStep 4802429 = 1800911) (by norm_num)
theorem B3201619 : Blo 1895435 3201619 := bstep (se 1 (by rfl) ⟨2401214, by rfl⟩ : syracuseStep 3201619 = 4802429) B4802429
theorem B4268825 : Blo 1895435 4268825 := bstep (se 2 (by rfl) ⟨1600809, by rfl⟩ : syracuseStep 4268825 = 3201619) B3201619
theorem B2845883 : Blo 1895435 2845883 := bstep (se 1 (by rfl) ⟨2134412, by rfl⟩ : syracuseStep 2845883 = 4268825) B4268825
theorem B1897255 : Blo 1895435 1897255 := bstep (se 1 (by rfl) ⟨1422941, by rfl⟩ : syracuseStep 1897255 = 2845883) B2845883
theorem B2134417 : Blo 1895435 2134417 := bbase (se 2 (by rfl) ⟨800406, by rfl⟩ : syracuseStep 2134417 = 1600813) (by norm_num)
theorem B2845889 : Blo 1895435 2845889 := bstep (se 2 (by rfl) ⟨1067208, by rfl⟩ : syracuseStep 2845889 = 2134417) B2134417
theorem B1897259 : Blo 1895435 1897259 := bstep (se 1 (by rfl) ⟨1422944, by rfl⟩ : syracuseStep 1897259 = 2845889) B2845889
theorem B3601837 : Blo 1895435 3601837 := bbase (se 3 (by rfl) ⟨675344, by rfl⟩ : syracuseStep 3601837 = 1350689) (by norm_num)
theorem B4802449 : Blo 1895435 4802449 := bstep (se 2 (by rfl) ⟨1800918, by rfl⟩ : syracuseStep 4802449 = 3601837) B3601837
theorem B6403265 : Blo 1895435 6403265 := bstep (se 2 (by rfl) ⟨2401224, by rfl⟩ : syracuseStep 6403265 = 4802449) B4802449
theorem B4268843 : Blo 1895435 4268843 := bstep (se 1 (by rfl) ⟨3201632, by rfl⟩ : syracuseStep 4268843 = 6403265) B6403265
theorem B2845895 : Blo 1895435 2845895 := bstep (se 1 (by rfl) ⟨2134421, by rfl⟩ : syracuseStep 2845895 = 4268843) B4268843
theorem B1897263 : Blo 1895435 1897263 := bstep (se 1 (by rfl) ⟨1422947, by rfl⟩ : syracuseStep 1897263 = 2845895) B2845895
theorem B2845901 : Blo 1895435 2845901 := bbase (se 3 (by rfl) ⟨533606, by rfl⟩ : syracuseStep 2845901 = 1067213) (by norm_num)
theorem B1897267 : Blo 1895435 1897267 := bstep (se 1 (by rfl) ⟨1422950, by rfl⟩ : syracuseStep 1897267 = 2845901) B2845901
theorem B4268861 : Blo 1895435 4268861 := bbase (se 3 (by rfl) ⟨800411, by rfl⟩ : syracuseStep 4268861 = 1600823) (by norm_num)
theorem B2845907 : Blo 1895435 2845907 := bstep (se 1 (by rfl) ⟨2134430, by rfl⟩ : syracuseStep 2845907 = 4268861) B4268861
theorem B1897271 : Blo 1895435 1897271 := bstep (se 1 (by rfl) ⟨1422953, by rfl⟩ : syracuseStep 1897271 = 2845907) B2845907
theorem B3201653 : Blo 1895435 3201653 := bbase (se 5 (by rfl) ⟨150077, by rfl⟩ : syracuseStep 3201653 = 300155) (by norm_num)
theorem B2134435 : Blo 1895435 2134435 := bstep (se 1 (by rfl) ⟨1600826, by rfl⟩ : syracuseStep 2134435 = 3201653) B3201653
theorem B2845913 : Blo 1895435 2845913 := bstep (se 2 (by rfl) ⟨1067217, by rfl⟩ : syracuseStep 2845913 = 2134435) B2134435
theorem B1897275 : Blo 1895435 1897275 := bstep (se 1 (by rfl) ⟨1422956, by rfl⟩ : syracuseStep 1897275 = 2845913) B2845913
theorem B4052101 : Blo 1895435 4052101 := bbase (se 4 (by rfl) ⟨379884, by rfl⟩ : syracuseStep 4052101 = 759769) (by norm_num)
theorem B5402801 : Blo 1895435 5402801 := bstep (se 2 (by rfl) ⟨2026050, by rfl⟩ : syracuseStep 5402801 = 4052101) B4052101
theorem B14407469 : Blo 1895435 14407469 := bstep (se 3 (by rfl) ⟨2701400, by rfl⟩ : syracuseStep 14407469 = 5402801) B5402801
theorem B9604979 : Blo 1895435 9604979 := bstep (se 1 (by rfl) ⟨7203734, by rfl⟩ : syracuseStep 9604979 = 14407469) B14407469
theorem B6403319 : Blo 1895435 6403319 := bstep (se 1 (by rfl) ⟨4802489, by rfl⟩ : syracuseStep 6403319 = 9604979) B9604979
theorem B4268879 : Blo 1895435 4268879 := bstep (se 1 (by rfl) ⟨3201659, by rfl⟩ : syracuseStep 4268879 = 6403319) B6403319
theorem B2845919 : Blo 1895435 2845919 := bstep (se 1 (by rfl) ⟨2134439, by rfl⟩ : syracuseStep 2845919 = 4268879) B4268879
theorem B1897279 : Blo 1895435 1897279 := bstep (se 1 (by rfl) ⟨1422959, by rfl⟩ : syracuseStep 1897279 = 2845919) B2845919
theorem B2845925 : Blo 1895435 2845925 := bbase (se 4 (by rfl) ⟨266805, by rfl⟩ : syracuseStep 2845925 = 533611) (by norm_num)
theorem B1897283 : Blo 1895435 1897283 := bstep (se 1 (by rfl) ⟨1422962, by rfl⟩ : syracuseStep 1897283 = 2845925) B2845925
theorem B9117269 : Blo 1895435 9117269 := bbase (se 8 (by rfl) ⟨53421, by rfl⟩ : syracuseStep 9117269 = 106843) (by norm_num)
theorem B6078179 : Blo 1895435 6078179 := bstep (se 1 (by rfl) ⟨4558634, by rfl⟩ : syracuseStep 6078179 = 9117269) B9117269
theorem B4052119 : Blo 1895435 4052119 := bstep (se 1 (by rfl) ⟨3039089, by rfl⟩ : syracuseStep 4052119 = 6078179) B6078179
theorem B5402825 : Blo 1895435 5402825 := bstep (se 2 (by rfl) ⟨2026059, by rfl⟩ : syracuseStep 5402825 = 4052119) B4052119
theorem B3601883 : Blo 1895435 3601883 := bstep (se 1 (by rfl) ⟨2701412, by rfl⟩ : syracuseStep 3601883 = 5402825) B5402825
theorem B2401255 : Blo 1895435 2401255 := bstep (se 1 (by rfl) ⟨1800941, by rfl⟩ : syracuseStep 2401255 = 3601883) B3601883
theorem B3201673 : Blo 1895435 3201673 := bstep (se 2 (by rfl) ⟨1200627, by rfl⟩ : syracuseStep 3201673 = 2401255) B2401255
theorem B4268897 : Blo 1895435 4268897 := bstep (se 2 (by rfl) ⟨1600836, by rfl⟩ : syracuseStep 4268897 = 3201673) B3201673
theorem B2845931 : Blo 1895435 2845931 := bstep (se 1 (by rfl) ⟨2134448, by rfl⟩ : syracuseStep 2845931 = 4268897) B4268897
theorem B1897287 : Blo 1895435 1897287 := bstep (se 1 (by rfl) ⟨1422965, by rfl⟩ : syracuseStep 1897287 = 2845931) B2845931
theorem B2134453 : Blo 1895435 2134453 := bbase (se 5 (by rfl) ⟨100052, by rfl⟩ : syracuseStep 2134453 = 200105) (by norm_num)
theorem B2845937 : Blo 1895435 2845937 := bstep (se 2 (by rfl) ⟨1067226, by rfl⟩ : syracuseStep 2845937 = 2134453) B2134453
theorem B1897291 : Blo 1895435 1897291 := bstep (se 1 (by rfl) ⟨1422968, by rfl⟩ : syracuseStep 1897291 = 2845937) B2845937
theorem B2401265 : Blo 1895435 2401265 := bbase (se 2 (by rfl) ⟨900474, by rfl⟩ : syracuseStep 2401265 = 1800949) (by norm_num)
theorem B6403373 : Blo 1895435 6403373 := bstep (se 3 (by rfl) ⟨1200632, by rfl⟩ : syracuseStep 6403373 = 2401265) B2401265
theorem B4268915 : Blo 1895435 4268915 := bstep (se 1 (by rfl) ⟨3201686, by rfl⟩ : syracuseStep 4268915 = 6403373) B6403373
theorem B2845943 : Blo 1895435 2845943 := bstep (se 1 (by rfl) ⟨2134457, by rfl⟩ : syracuseStep 2845943 = 4268915) B4268915
theorem B1897295 : Blo 1895435 1897295 := bstep (se 1 (by rfl) ⟨1422971, by rfl⟩ : syracuseStep 1897295 = 2845943) B2845943
theorem B2845949 : Blo 1895435 2845949 := bbase (se 3 (by rfl) ⟨533615, by rfl⟩ : syracuseStep 2845949 = 1067231) (by norm_num)
theorem B1897299 : Blo 1895435 1897299 := bstep (se 1 (by rfl) ⟨1422974, by rfl⟩ : syracuseStep 1897299 = 2845949) B2845949
theorem B4268933 : Blo 1895435 4268933 := bbase (se 4 (by rfl) ⟨400212, by rfl⟩ : syracuseStep 4268933 = 800425) (by norm_num)
theorem B2845955 : Blo 1895435 2845955 := bstep (se 1 (by rfl) ⟨2134466, by rfl⟩ : syracuseStep 2845955 = 4268933) B4268933
theorem B1897303 : Blo 1895435 1897303 := bstep (se 1 (by rfl) ⟨1422977, by rfl⟩ : syracuseStep 1897303 = 2845955) B2845955
theorem B2026081 : Blo 1895435 2026081 := bbase (se 2 (by rfl) ⟨759780, by rfl⟩ : syracuseStep 2026081 = 1519561) (by norm_num)
theorem B2701441 : Blo 1895435 2701441 := bstep (se 2 (by rfl) ⟨1013040, by rfl⟩ : syracuseStep 2701441 = 2026081) B2026081
theorem B3601921 : Blo 1895435 3601921 := bstep (se 2 (by rfl) ⟨1350720, by rfl⟩ : syracuseStep 3601921 = 2701441) B2701441
theorem B4802561 : Blo 1895435 4802561 := bstep (se 2 (by rfl) ⟨1800960, by rfl⟩ : syracuseStep 4802561 = 3601921) B3601921
theorem B3201707 : Blo 1895435 3201707 := bstep (se 1 (by rfl) ⟨2401280, by rfl⟩ : syracuseStep 3201707 = 4802561) B4802561
theorem B2134471 : Blo 1895435 2134471 := bstep (se 1 (by rfl) ⟨1600853, by rfl⟩ : syracuseStep 2134471 = 3201707) B3201707
theorem B2845961 : Blo 1895435 2845961 := bstep (se 2 (by rfl) ⟨1067235, by rfl⟩ : syracuseStep 2845961 = 2134471) B2134471
theorem B1897307 : Blo 1895435 1897307 := bstep (se 1 (by rfl) ⟨1422980, by rfl⟩ : syracuseStep 1897307 = 2845961) B2845961
theorem B9605141 : Blo 1895435 9605141 := bbase (se 6 (by rfl) ⟨225120, by rfl⟩ : syracuseStep 9605141 = 450241) (by norm_num)
theorem B6403427 : Blo 1895435 6403427 := bstep (se 1 (by rfl) ⟨4802570, by rfl⟩ : syracuseStep 6403427 = 9605141) B9605141
theorem B4268951 : Blo 1895435 4268951 := bstep (se 1 (by rfl) ⟨3201713, by rfl⟩ : syracuseStep 4268951 = 6403427) B6403427
theorem B2845967 : Blo 1895435 2845967 := bstep (se 1 (by rfl) ⟨2134475, by rfl⟩ : syracuseStep 2845967 = 4268951) B4268951
theorem B1897311 : Blo 1895435 1897311 := bstep (se 1 (by rfl) ⟨1422983, by rfl⟩ : syracuseStep 1897311 = 2845967) B2845967
theorem B2845973 : Blo 1895435 2845973 := bbase (se 6 (by rfl) ⟨66702, by rfl⟩ : syracuseStep 2845973 = 133405) (by norm_num)
theorem B1897315 : Blo 1895435 1897315 := bstep (se 1 (by rfl) ⟨1422986, by rfl⟩ : syracuseStep 1897315 = 2845973) B2845973
theorem B20514197 : Blo 1895435 20514197 := bbase (se 6 (by rfl) ⟨480801, by rfl⟩ : syracuseStep 20514197 = 961603) (by norm_num)
theorem B13676131 : Blo 1895435 13676131 := bstep (se 1 (by rfl) ⟨10257098, by rfl⟩ : syracuseStep 13676131 = 20514197) B20514197
theorem B18234841 : Blo 1895435 18234841 := bstep (se 2 (by rfl) ⟨6838065, by rfl⟩ : syracuseStep 18234841 = 13676131) B13676131
theorem B24313121 : Blo 1895435 24313121 := bstep (se 2 (by rfl) ⟨9117420, by rfl⟩ : syracuseStep 24313121 = 18234841) B18234841
theorem B16208747 : Blo 1895435 16208747 := bstep (se 1 (by rfl) ⟨12156560, by rfl⟩ : syracuseStep 16208747 = 24313121) B24313121
theorem B10805831 : Blo 1895435 10805831 := bstep (se 1 (by rfl) ⟨8104373, by rfl⟩ : syracuseStep 10805831 = 16208747) B16208747
theorem B7203887 : Blo 1895435 7203887 := bstep (se 1 (by rfl) ⟨5402915, by rfl⟩ : syracuseStep 7203887 = 10805831) B10805831
theorem B4802591 : Blo 1895435 4802591 := bstep (se 1 (by rfl) ⟨3601943, by rfl⟩ : syracuseStep 4802591 = 7203887) B7203887
theorem B3201727 : Blo 1895435 3201727 := bstep (se 1 (by rfl) ⟨2401295, by rfl⟩ : syracuseStep 3201727 = 4802591) B4802591
theorem B4268969 : Blo 1895435 4268969 := bstep (se 2 (by rfl) ⟨1600863, by rfl⟩ : syracuseStep 4268969 = 3201727) B3201727
theorem B2845979 : Blo 1895435 2845979 := bstep (se 1 (by rfl) ⟨2134484, by rfl⟩ : syracuseStep 2845979 = 4268969) B4268969
theorem B1897319 : Blo 1895435 1897319 := bstep (se 1 (by rfl) ⟨1422989, by rfl⟩ : syracuseStep 1897319 = 2845979) B2845979
theorem B2134489 : Blo 1895435 2134489 := bbase (se 2 (by rfl) ⟨800433, by rfl⟩ : syracuseStep 2134489 = 1600867) (by norm_num)
theorem B2845985 : Blo 1895435 2845985 := bstep (se 2 (by rfl) ⟨1067244, by rfl⟩ : syracuseStep 2845985 = 2134489) B2134489
theorem B1897323 : Blo 1895435 1897323 := bstep (se 1 (by rfl) ⟨1422992, by rfl⟩ : syracuseStep 1897323 = 2845985) B2845985
theorem B2701469 : Blo 1895435 2701469 := bbase (se 3 (by rfl) ⟨506525, by rfl⟩ : syracuseStep 2701469 = 1013051) (by norm_num)
theorem B7203917 : Blo 1895435 7203917 := bstep (se 3 (by rfl) ⟨1350734, by rfl⟩ : syracuseStep 7203917 = 2701469) B2701469
theorem B4802611 : Blo 1895435 4802611 := bstep (se 1 (by rfl) ⟨3601958, by rfl⟩ : syracuseStep 4802611 = 7203917) B7203917
theorem B6403481 : Blo 1895435 6403481 := bstep (se 2 (by rfl) ⟨2401305, by rfl⟩ : syracuseStep 6403481 = 4802611) B4802611
theorem B4268987 : Blo 1895435 4268987 := bstep (se 1 (by rfl) ⟨3201740, by rfl⟩ : syracuseStep 4268987 = 6403481) B6403481
theorem B2845991 : Blo 1895435 2845991 := bstep (se 1 (by rfl) ⟨2134493, by rfl⟩ : syracuseStep 2845991 = 4268987) B4268987
theorem B1897327 : Blo 1895435 1897327 := bstep (se 1 (by rfl) ⟨1422995, by rfl⟩ : syracuseStep 1897327 = 2845991) B2845991
theorem B2845997 : Blo 1895435 2845997 := bbase (se 3 (by rfl) ⟨533624, by rfl⟩ : syracuseStep 2845997 = 1067249) (by norm_num)
theorem B1897331 : Blo 1895435 1897331 := bstep (se 1 (by rfl) ⟨1422998, by rfl⟩ : syracuseStep 1897331 = 2845997) B2845997
theorem B4269005 : Blo 1895435 4269005 := bbase (se 3 (by rfl) ⟨800438, by rfl⟩ : syracuseStep 4269005 = 1600877) (by norm_num)
theorem B2846003 : Blo 1895435 2846003 := bstep (se 1 (by rfl) ⟨2134502, by rfl⟩ : syracuseStep 2846003 = 4269005) B4269005
theorem B1897335 : Blo 1895435 1897335 := bstep (se 1 (by rfl) ⟨1423001, by rfl⟩ : syracuseStep 1897335 = 2846003) B2846003
theorem B2401321 : Blo 1895435 2401321 := bbase (se 2 (by rfl) ⟨900495, by rfl⟩ : syracuseStep 2401321 = 1800991) (by norm_num)
theorem B3201761 : Blo 1895435 3201761 := bstep (se 2 (by rfl) ⟨1200660, by rfl⟩ : syracuseStep 3201761 = 2401321) B2401321
theorem B2134507 : Blo 1895435 2134507 := bstep (se 1 (by rfl) ⟨1600880, by rfl⟩ : syracuseStep 2134507 = 3201761) B3201761
theorem B2846009 : Blo 1895435 2846009 := bstep (se 2 (by rfl) ⟨1067253, by rfl⟩ : syracuseStep 2846009 = 2134507) B2134507
theorem B1897339 : Blo 1895435 1897339 := bstep (se 1 (by rfl) ⟨1423004, by rfl⟩ : syracuseStep 1897339 = 2846009) B2846009
theorem B46157525 : Blo 1895435 46157525 := bbase (se 7 (by rfl) ⟨540908, by rfl⟩ : syracuseStep 46157525 = 1081817) (by norm_num)
theorem B30771683 : Blo 1895435 30771683 := bstep (se 1 (by rfl) ⟨23078762, by rfl⟩ : syracuseStep 30771683 = 46157525) B46157525
theorem B20514455 : Blo 1895435 20514455 := bstep (se 1 (by rfl) ⟨15385841, by rfl⟩ : syracuseStep 20514455 = 30771683) B30771683
theorem B13676303 : Blo 1895435 13676303 := bstep (se 1 (by rfl) ⟨10257227, by rfl⟩ : syracuseStep 13676303 = 20514455) B20514455
theorem B9117535 : Blo 1895435 9117535 := bstep (se 1 (by rfl) ⟨6838151, by rfl⟩ : syracuseStep 9117535 = 13676303) B13676303
theorem B12156713 : Blo 1895435 12156713 := bstep (se 2 (by rfl) ⟨4558767, by rfl⟩ : syracuseStep 12156713 = 9117535) B9117535
theorem B8104475 : Blo 1895435 8104475 := bstep (se 1 (by rfl) ⟨6078356, by rfl⟩ : syracuseStep 8104475 = 12156713) B12156713
theorem B21611933 : Blo 1895435 21611933 := bstep (se 3 (by rfl) ⟨4052237, by rfl⟩ : syracuseStep 21611933 = 8104475) B8104475
theorem B14407955 : Blo 1895435 14407955 := bstep (se 1 (by rfl) ⟨10805966, by rfl⟩ : syracuseStep 14407955 = 21611933) B21611933
theorem B9605303 : Blo 1895435 9605303 := bstep (se 1 (by rfl) ⟨7203977, by rfl⟩ : syracuseStep 9605303 = 14407955) B14407955
theorem B6403535 : Blo 1895435 6403535 := bstep (se 1 (by rfl) ⟨4802651, by rfl⟩ : syracuseStep 6403535 = 9605303) B9605303
theorem B4269023 : Blo 1895435 4269023 := bstep (se 1 (by rfl) ⟨3201767, by rfl⟩ : syracuseStep 4269023 = 6403535) B6403535
theorem B2846015 : Blo 1895435 2846015 := bstep (se 1 (by rfl) ⟨2134511, by rfl⟩ : syracuseStep 2846015 = 4269023) B4269023
theorem B1897343 : Blo 1895435 1897343 := bstep (se 1 (by rfl) ⟨1423007, by rfl⟩ : syracuseStep 1897343 = 2846015) B2846015
theorem B2846021 : Blo 1895435 2846021 := bbase (se 4 (by rfl) ⟨266814, by rfl⟩ : syracuseStep 2846021 = 533629) (by norm_num)
theorem B1897347 : Blo 1895435 1897347 := bstep (se 1 (by rfl) ⟨1423010, by rfl⟩ : syracuseStep 1897347 = 2846021) B2846021
theorem B3201781 : Blo 1895435 3201781 := bbase (se 5 (by rfl) ⟨150083, by rfl⟩ : syracuseStep 3201781 = 300167) (by norm_num)
theorem B4269041 : Blo 1895435 4269041 := bstep (se 2 (by rfl) ⟨1600890, by rfl⟩ : syracuseStep 4269041 = 3201781) B3201781
theorem B2846027 : Blo 1895435 2846027 := bstep (se 1 (by rfl) ⟨2134520, by rfl⟩ : syracuseStep 2846027 = 4269041) B4269041
theorem B1897351 : Blo 1895435 1897351 := bstep (se 1 (by rfl) ⟨1423013, by rfl⟩ : syracuseStep 1897351 = 2846027) B2846027
theorem B2134525 : Blo 1895435 2134525 := bbase (se 3 (by rfl) ⟨400223, by rfl⟩ : syracuseStep 2134525 = 800447) (by norm_num)
theorem B2846033 : Blo 1895435 2846033 := bstep (se 2 (by rfl) ⟨1067262, by rfl⟩ : syracuseStep 2846033 = 2134525) B2134525
theorem B1897355 : Blo 1895435 1897355 := bstep (se 1 (by rfl) ⟨1423016, by rfl⟩ : syracuseStep 1897355 = 2846033) B2846033
theorem B6403589 : Blo 1895435 6403589 := bbase (se 4 (by rfl) ⟨600336, by rfl⟩ : syracuseStep 6403589 = 1200673) (by norm_num)
theorem B4269059 : Blo 1895435 4269059 := bstep (se 1 (by rfl) ⟨3201794, by rfl⟩ : syracuseStep 4269059 = 6403589) B6403589
theorem B2846039 : Blo 1895435 2846039 := bstep (se 1 (by rfl) ⟨2134529, by rfl⟩ : syracuseStep 2846039 = 4269059) B4269059
theorem B1897359 : Blo 1895435 1897359 := bstep (se 1 (by rfl) ⟨1423019, by rfl⟩ : syracuseStep 1897359 = 2846039) B2846039
theorem B2846045 : Blo 1895435 2846045 := bbase (se 3 (by rfl) ⟨533633, by rfl⟩ : syracuseStep 2846045 = 1067267) (by norm_num)
theorem B1897363 : Blo 1895435 1897363 := bstep (se 1 (by rfl) ⟨1423022, by rfl⟩ : syracuseStep 1897363 = 2846045) B2846045
theorem B4269077 : Blo 1895435 4269077 := bbase (se 6 (by rfl) ⟨100056, by rfl⟩ : syracuseStep 4269077 = 200113) (by norm_num)
theorem B2846051 : Blo 1895435 2846051 := bstep (se 1 (by rfl) ⟨2134538, by rfl⟩ : syracuseStep 2846051 = 4269077) B4269077
theorem B1897367 : Blo 1895435 1897367 := bstep (se 1 (by rfl) ⟨1423025, by rfl⟩ : syracuseStep 1897367 = 2846051) B2846051
theorem B7204085 : Blo 1895435 7204085 := bbase (se 5 (by rfl) ⟨337691, by rfl⟩ : syracuseStep 7204085 = 675383) (by norm_num)
theorem B4802723 : Blo 1895435 4802723 := bstep (se 1 (by rfl) ⟨3602042, by rfl⟩ : syracuseStep 4802723 = 7204085) B7204085
theorem B3201815 : Blo 1895435 3201815 := bstep (se 1 (by rfl) ⟨2401361, by rfl⟩ : syracuseStep 3201815 = 4802723) B4802723
theorem B2134543 : Blo 1895435 2134543 := bstep (se 1 (by rfl) ⟨1600907, by rfl⟩ : syracuseStep 2134543 = 3201815) B3201815
theorem B2846057 : Blo 1895435 2846057 := bstep (se 2 (by rfl) ⟨1067271, by rfl⟩ : syracuseStep 2846057 = 2134543) B2134543
theorem B1897371 : Blo 1895435 1897371 := bstep (se 1 (by rfl) ⟨1423028, by rfl⟩ : syracuseStep 1897371 = 2846057) B2846057
theorem B2026153 : Blo 1895435 2026153 := bbase (se 2 (by rfl) ⟨759807, by rfl⟩ : syracuseStep 2026153 = 1519615) (by norm_num)
theorem B10806149 : Blo 1895435 10806149 := bstep (se 4 (by rfl) ⟨1013076, by rfl⟩ : syracuseStep 10806149 = 2026153) B2026153
theorem B7204099 : Blo 1895435 7204099 := bstep (se 1 (by rfl) ⟨5403074, by rfl⟩ : syracuseStep 7204099 = 10806149) B10806149
theorem B9605465 : Blo 1895435 9605465 := bstep (se 2 (by rfl) ⟨3602049, by rfl⟩ : syracuseStep 9605465 = 7204099) B7204099
theorem B6403643 : Blo 1895435 6403643 := bstep (se 1 (by rfl) ⟨4802732, by rfl⟩ : syracuseStep 6403643 = 9605465) B9605465
theorem B4269095 : Blo 1895435 4269095 := bstep (se 1 (by rfl) ⟨3201821, by rfl⟩ : syracuseStep 4269095 = 6403643) B6403643
theorem B2846063 : Blo 1895435 2846063 := bstep (se 1 (by rfl) ⟨2134547, by rfl⟩ : syracuseStep 2846063 = 4269095) B4269095
theorem B1897375 : Blo 1895435 1897375 := bstep (se 1 (by rfl) ⟨1423031, by rfl⟩ : syracuseStep 1897375 = 2846063) B2846063
theorem B2846069 : Blo 1895435 2846069 := bbase (se 5 (by rfl) ⟨133409, by rfl⟩ : syracuseStep 2846069 = 266819) (by norm_num)
theorem B1897379 : Blo 1895435 1897379 := bstep (se 1 (by rfl) ⟨1423034, by rfl⟩ : syracuseStep 1897379 = 2846069) B2846069
theorem B2701549 : Blo 1895435 2701549 := bbase (se 3 (by rfl) ⟨506540, by rfl⟩ : syracuseStep 2701549 = 1013081) (by norm_num)
theorem B3602065 : Blo 1895435 3602065 := bstep (se 2 (by rfl) ⟨1350774, by rfl⟩ : syracuseStep 3602065 = 2701549) B2701549
theorem B4802753 : Blo 1895435 4802753 := bstep (se 2 (by rfl) ⟨1801032, by rfl⟩ : syracuseStep 4802753 = 3602065) B3602065
theorem B3201835 : Blo 1895435 3201835 := bstep (se 1 (by rfl) ⟨2401376, by rfl⟩ : syracuseStep 3201835 = 4802753) B4802753
theorem B4269113 : Blo 1895435 4269113 := bstep (se 2 (by rfl) ⟨1600917, by rfl⟩ : syracuseStep 4269113 = 3201835) B3201835
theorem B2846075 : Blo 1895435 2846075 := bstep (se 1 (by rfl) ⟨2134556, by rfl⟩ : syracuseStep 2846075 = 4269113) B4269113
theorem B1897383 : Blo 1895435 1897383 := bstep (se 1 (by rfl) ⟨1423037, by rfl⟩ : syracuseStep 1897383 = 2846075) B2846075
theorem B2134561 : Blo 1895435 2134561 := bbase (se 2 (by rfl) ⟨800460, by rfl⟩ : syracuseStep 2134561 = 1600921) (by norm_num)
theorem B2846081 : Blo 1895435 2846081 := bstep (se 2 (by rfl) ⟨1067280, by rfl⟩ : syracuseStep 2846081 = 2134561) B2134561
theorem B1897387 : Blo 1895435 1897387 := bstep (se 1 (by rfl) ⟨1423040, by rfl⟩ : syracuseStep 1897387 = 2846081) B2846081
theorem B4802773 : Blo 1895435 4802773 := bbase (se 7 (by rfl) ⟨56282, by rfl⟩ : syracuseStep 4802773 = 112565) (by norm_num)
theorem B6403697 : Blo 1895435 6403697 := bstep (se 2 (by rfl) ⟨2401386, by rfl⟩ : syracuseStep 6403697 = 4802773) B4802773
theorem B4269131 : Blo 1895435 4269131 := bstep (se 1 (by rfl) ⟨3201848, by rfl⟩ : syracuseStep 4269131 = 6403697) B6403697
theorem B2846087 : Blo 1895435 2846087 := bstep (se 1 (by rfl) ⟨2134565, by rfl⟩ : syracuseStep 2846087 = 4269131) B4269131
theorem B1897391 : Blo 1895435 1897391 := bstep (se 1 (by rfl) ⟨1423043, by rfl⟩ : syracuseStep 1897391 = 2846087) B2846087
theorem B2846093 : Blo 1895435 2846093 := bbase (se 3 (by rfl) ⟨533642, by rfl⟩ : syracuseStep 2846093 = 1067285) (by norm_num)
theorem B1897395 : Blo 1895435 1897395 := bstep (se 1 (by rfl) ⟨1423046, by rfl⟩ : syracuseStep 1897395 = 2846093) B2846093
theorem B4269149 : Blo 1895435 4269149 := bbase (se 3 (by rfl) ⟨800465, by rfl⟩ : syracuseStep 4269149 = 1600931) (by norm_num)
theorem B2846099 : Blo 1895435 2846099 := bstep (se 1 (by rfl) ⟨2134574, by rfl⟩ : syracuseStep 2846099 = 4269149) B4269149
theorem B1897399 : Blo 1895435 1897399 := bstep (se 1 (by rfl) ⟨1423049, by rfl⟩ : syracuseStep 1897399 = 2846099) B2846099
theorem B3201869 : Blo 1895435 3201869 := bbase (se 3 (by rfl) ⟨600350, by rfl⟩ : syracuseStep 3201869 = 1200701) (by norm_num)
theorem B2134579 : Blo 1895435 2134579 := bstep (se 1 (by rfl) ⟨1600934, by rfl⟩ : syracuseStep 2134579 = 3201869) B3201869
theorem B2846105 : Blo 1895435 2846105 := bstep (se 2 (by rfl) ⟨1067289, by rfl⟩ : syracuseStep 2846105 = 2134579) B2134579
theorem B1897403 : Blo 1895435 1897403 := bstep (se 1 (by rfl) ⟨1423052, by rfl⟩ : syracuseStep 1897403 = 2846105) B2846105
theorem B3080749 : Blo 1895435 3080749 := bbase (se 3 (by rfl) ⟨577640, by rfl⟩ : syracuseStep 3080749 = 1155281) (by norm_num)
theorem B4107665 : Blo 1895435 4107665 := bstep (se 2 (by rfl) ⟨1540374, by rfl⟩ : syracuseStep 4107665 = 3080749) B3080749
theorem B2738443 : Blo 1895435 2738443 := bstep (se 1 (by rfl) ⟨2053832, by rfl⟩ : syracuseStep 2738443 = 4107665) B4107665
theorem B3651257 : Blo 1895435 3651257 := bstep (se 2 (by rfl) ⟨1369221, by rfl⟩ : syracuseStep 3651257 = 2738443) B2738443
theorem B9736685 : Blo 1895435 9736685 := bstep (se 3 (by rfl) ⟨1825628, by rfl⟩ : syracuseStep 9736685 = 3651257) B3651257
theorem B6491123 : Blo 1895435 6491123 := bstep (se 1 (by rfl) ⟨4868342, by rfl⟩ : syracuseStep 6491123 = 9736685) B9736685
theorem B4327415 : Blo 1895435 4327415 := bstep (se 1 (by rfl) ⟨3245561, by rfl⟩ : syracuseStep 4327415 = 6491123) B6491123
theorem B2884943 : Blo 1895435 2884943 := bstep (se 1 (by rfl) ⟨2163707, by rfl⟩ : syracuseStep 2884943 = 4327415) B4327415
theorem B7693181 : Blo 1895435 7693181 := bstep (se 3 (by rfl) ⟨1442471, by rfl⟩ : syracuseStep 7693181 = 2884943) B2884943
theorem B5128787 : Blo 1895435 5128787 := bstep (se 1 (by rfl) ⟨3846590, by rfl⟩ : syracuseStep 5128787 = 7693181) B7693181
theorem B3419191 : Blo 1895435 3419191 := bstep (se 1 (by rfl) ⟨2564393, by rfl⟩ : syracuseStep 3419191 = 5128787) B5128787
theorem B18235685 : Blo 1895435 18235685 := bstep (se 4 (by rfl) ⟨1709595, by rfl⟩ : syracuseStep 18235685 = 3419191) B3419191
theorem B12157123 : Blo 1895435 12157123 := bstep (se 1 (by rfl) ⟨9117842, by rfl⟩ : syracuseStep 12157123 = 18235685) B18235685
theorem B16209497 : Blo 1895435 16209497 := bstep (se 2 (by rfl) ⟨6078561, by rfl⟩ : syracuseStep 16209497 = 12157123) B12157123
theorem B10806331 : Blo 1895435 10806331 := bstep (se 1 (by rfl) ⟨8104748, by rfl⟩ : syracuseStep 10806331 = 16209497) B16209497
theorem B14408441 : Blo 1895435 14408441 := bstep (se 2 (by rfl) ⟨5403165, by rfl⟩ : syracuseStep 14408441 = 10806331) B10806331
theorem B9605627 : Blo 1895435 9605627 := bstep (se 1 (by rfl) ⟨7204220, by rfl⟩ : syracuseStep 9605627 = 14408441) B14408441
theorem B6403751 : Blo 1895435 6403751 := bstep (se 1 (by rfl) ⟨4802813, by rfl⟩ : syracuseStep 6403751 = 9605627) B9605627
theorem B4269167 : Blo 1895435 4269167 := bstep (se 1 (by rfl) ⟨3201875, by rfl⟩ : syracuseStep 4269167 = 6403751) B6403751
theorem B2846111 : Blo 1895435 2846111 := bstep (se 1 (by rfl) ⟨2134583, by rfl⟩ : syracuseStep 2846111 = 4269167) B4269167
theorem B1897407 : Blo 1895435 1897407 := bstep (se 1 (by rfl) ⟨1423055, by rfl⟩ : syracuseStep 1897407 = 2846111) B2846111
theorem B2846117 : Blo 1895435 2846117 := bbase (se 4 (by rfl) ⟨266823, by rfl⟩ : syracuseStep 2846117 = 533647) (by norm_num)
theorem B1897411 : Blo 1895435 1897411 := bstep (se 1 (by rfl) ⟨1423058, by rfl⟩ : syracuseStep 1897411 = 2846117) B2846117
theorem B2401417 : Blo 1895435 2401417 := bbase (se 2 (by rfl) ⟨900531, by rfl⟩ : syracuseStep 2401417 = 1801063) (by norm_num)
theorem B3201889 : Blo 1895435 3201889 := bstep (se 2 (by rfl) ⟨1200708, by rfl⟩ : syracuseStep 3201889 = 2401417) B2401417
theorem B4269185 : Blo 1895435 4269185 := bstep (se 2 (by rfl) ⟨1600944, by rfl⟩ : syracuseStep 4269185 = 3201889) B3201889
theorem B2846123 : Blo 1895435 2846123 := bstep (se 1 (by rfl) ⟨2134592, by rfl⟩ : syracuseStep 2846123 = 4269185) B4269185
theorem B1897415 : Blo 1895435 1897415 := bstep (se 1 (by rfl) ⟨1423061, by rfl⟩ : syracuseStep 1897415 = 2846123) B2846123
theorem B2134597 : Blo 1895435 2134597 := bbase (se 4 (by rfl) ⟨200118, by rfl⟩ : syracuseStep 2134597 = 400237) (by norm_num)
theorem B2846129 : Blo 1895435 2846129 := bstep (se 2 (by rfl) ⟨1067298, by rfl⟩ : syracuseStep 2846129 = 2134597) B2134597
theorem B1897419 : Blo 1895435 1897419 := bstep (se 1 (by rfl) ⟨1423064, by rfl⟩ : syracuseStep 1897419 = 2846129) B2846129
theorem B3602141 : Blo 1895435 3602141 := bbase (se 3 (by rfl) ⟨675401, by rfl⟩ : syracuseStep 3602141 = 1350803) (by norm_num)
theorem B2401427 : Blo 1895435 2401427 := bstep (se 1 (by rfl) ⟨1801070, by rfl⟩ : syracuseStep 2401427 = 3602141) B3602141
theorem B6403805 : Blo 1895435 6403805 := bstep (se 3 (by rfl) ⟨1200713, by rfl⟩ : syracuseStep 6403805 = 2401427) B2401427
theorem B4269203 : Blo 1895435 4269203 := bstep (se 1 (by rfl) ⟨3201902, by rfl⟩ : syracuseStep 4269203 = 6403805) B6403805
theorem B2846135 : Blo 1895435 2846135 := bstep (se 1 (by rfl) ⟨2134601, by rfl⟩ : syracuseStep 2846135 = 4269203) B4269203
theorem B1897423 : Blo 1895435 1897423 := bstep (se 1 (by rfl) ⟨1423067, by rfl⟩ : syracuseStep 1897423 = 2846135) B2846135
theorem B2846141 : Blo 1895435 2846141 := bbase (se 3 (by rfl) ⟨533651, by rfl⟩ : syracuseStep 2846141 = 1067303) (by norm_num)
theorem B1897427 : Blo 1895435 1897427 := bstep (se 1 (by rfl) ⟨1423070, by rfl⟩ : syracuseStep 1897427 = 2846141) B2846141
theorem B4269221 : Blo 1895435 4269221 := bbase (se 4 (by rfl) ⟨400239, by rfl⟩ : syracuseStep 4269221 = 800479) (by norm_num)
theorem B2846147 : Blo 1895435 2846147 := bstep (se 1 (by rfl) ⟨2134610, by rfl⟩ : syracuseStep 2846147 = 4269221) B4269221
theorem B1897431 : Blo 1895435 1897431 := bstep (se 1 (by rfl) ⟨1423073, by rfl⟩ : syracuseStep 1897431 = 2846147) B2846147
theorem B4802885 : Blo 1895435 4802885 := bbase (se 4 (by rfl) ⟨450270, by rfl⟩ : syracuseStep 4802885 = 900541) (by norm_num)
theorem B3201923 : Blo 1895435 3201923 := bstep (se 1 (by rfl) ⟨2401442, by rfl⟩ : syracuseStep 3201923 = 4802885) B4802885
theorem B2134615 : Blo 1895435 2134615 := bstep (se 1 (by rfl) ⟨1600961, by rfl⟩ : syracuseStep 2134615 = 3201923) B3201923
theorem B2846153 : Blo 1895435 2846153 := bstep (se 2 (by rfl) ⟨1067307, by rfl⟩ : syracuseStep 2846153 = 2134615) B2134615
theorem B1897435 : Blo 1895435 1897435 := bstep (se 1 (by rfl) ⟨1423076, by rfl⟩ : syracuseStep 1897435 = 2846153) B2846153
theorem C0 (j : ℕ) (h1 : 473858 ≤ j) (h2 : j ≤ 474358) : Blo 1895435 (4 * j + 3) := by
  interval_cases j
  · exact B1895435
  · exact B1895439
  · exact B1895443
  · exact B1895447
  · exact B1895451
  · exact B1895455
  · exact B1895459
  · exact B1895463
  · exact B1895467
  · exact B1895471
  · exact B1895475
  · exact B1895479
  · exact B1895483
  · exact B1895487
  · exact B1895491
  · exact B1895495
  · exact B1895499
  · exact B1895503
  · exact B1895507
  · exact B1895511
  · exact B1895515
  · exact B1895519
  · exact B1895523
  · exact B1895527
  · exact B1895531
  · exact B1895535
  · exact B1895539
  · exact B1895543
  · exact B1895547
  · exact B1895551
  · exact B1895555
  · exact B1895559
  · exact B1895563
  · exact B1895567
  · exact B1895571
  · exact B1895575
  · exact B1895579
  · exact B1895583
  · exact B1895587
  · exact B1895591
  · exact B1895595
  · exact B1895599
  · exact B1895603
  · exact B1895607
  · exact B1895611
  · exact B1895615
  · exact B1895619
  · exact B1895623
  · exact B1895627
  · exact B1895631
  · exact B1895635
  · exact B1895639
  · exact B1895643
  · exact B1895647
  · exact B1895651
  · exact B1895655
  · exact B1895659
  · exact B1895663
  · exact B1895667
  · exact B1895671
  · exact B1895675
  · exact B1895679
  · exact B1895683
  · exact B1895687
  · exact B1895691
  · exact B1895695
  · exact B1895699
  · exact B1895703
  · exact B1895707
  · exact B1895711
  · exact B1895715
  · exact B1895719
  · exact B1895723
  · exact B1895727
  · exact B1895731
  · exact B1895735
  · exact B1895739
  · exact B1895743
  · exact B1895747
  · exact B1895751
  · exact B1895755
  · exact B1895759
  · exact B1895763
  · exact B1895767
  · exact B1895771
  · exact B1895775
  · exact B1895779
  · exact B1895783
  · exact B1895787
  · exact B1895791
  · exact B1895795
  · exact B1895799
  · exact B1895803
  · exact B1895807
  · exact B1895811
  · exact B1895815
  · exact B1895819
  · exact B1895823
  · exact B1895827
  · exact B1895831
  · exact B1895835
  · exact B1895839
  · exact B1895843
  · exact B1895847
  · exact B1895851
  · exact B1895855
  · exact B1895859
  · exact B1895863
  · exact B1895867
  · exact B1895871
  · exact B1895875
  · exact B1895879
  · exact B1895883
  · exact B1895887
  · exact B1895891
  · exact B1895895
  · exact B1895899
  · exact B1895903
  · exact B1895907
  · exact B1895911
  · exact B1895915
  · exact B1895919
  · exact B1895923
  · exact B1895927
  · exact B1895931
  · exact B1895935
  · exact B1895939
  · exact B1895943
  · exact B1895947
  · exact B1895951
  · exact B1895955
  · exact B1895959
  · exact B1895963
  · exact B1895967
  · exact B1895971
  · exact B1895975
  · exact B1895979
  · exact B1895983
  · exact B1895987
  · exact B1895991
  · exact B1895995
  · exact B1895999
  · exact B1896003
  · exact B1896007
  · exact B1896011
  · exact B1896015
  · exact B1896019
  · exact B1896023
  · exact B1896027
  · exact B1896031
  · exact B1896035
  · exact B1896039
  · exact B1896043
  · exact B1896047
  · exact B1896051
  · exact B1896055
  · exact B1896059
  · exact B1896063
  · exact B1896067
  · exact B1896071
  · exact B1896075
  · exact B1896079
  · exact B1896083
  · exact B1896087
  · exact B1896091
  · exact B1896095
  · exact B1896099
  · exact B1896103
  · exact B1896107
  · exact B1896111
  · exact B1896115
  · exact B1896119
  · exact B1896123
  · exact B1896127
  · exact B1896131
  · exact B1896135
  · exact B1896139
  · exact B1896143
  · exact B1896147
  · exact B1896151
  · exact B1896155
  · exact B1896159
  · exact B1896163
  · exact B1896167
  · exact B1896171
  · exact B1896175
  · exact B1896179
  · exact B1896183
  · exact B1896187
  · exact B1896191
  · exact B1896195
  · exact B1896199
  · exact B1896203
  · exact B1896207
  · exact B1896211
  · exact B1896215
  · exact B1896219
  · exact B1896223
  · exact B1896227
  · exact B1896231
  · exact B1896235
  · exact B1896239
  · exact B1896243
  · exact B1896247
  · exact B1896251
  · exact B1896255
  · exact B1896259
  · exact B1896263
  · exact B1896267
  · exact B1896271
  · exact B1896275
  · exact B1896279
  · exact B1896283
  · exact B1896287
  · exact B1896291
  · exact B1896295
  · exact B1896299
  · exact B1896303
  · exact B1896307
  · exact B1896311
  · exact B1896315
  · exact B1896319
  · exact B1896323
  · exact B1896327
  · exact B1896331
  · exact B1896335
  · exact B1896339
  · exact B1896343
  · exact B1896347
  · exact B1896351
  · exact B1896355
  · exact B1896359
  · exact B1896363
  · exact B1896367
  · exact B1896371
  · exact B1896375
  · exact B1896379
  · exact B1896383
  · exact B1896387
  · exact B1896391
  · exact B1896395
  · exact B1896399
  · exact B1896403
  · exact B1896407
  · exact B1896411
  · exact B1896415
  · exact B1896419
  · exact B1896423
  · exact B1896427
  · exact B1896431
  · exact B1896435
  · exact B1896439
  · exact B1896443
  · exact B1896447
  · exact B1896451
  · exact B1896455
  · exact B1896459
  · exact B1896463
  · exact B1896467
  · exact B1896471
  · exact B1896475
  · exact B1896479
  · exact B1896483
  · exact B1896487
  · exact B1896491
  · exact B1896495
  · exact B1896499
  · exact B1896503
  · exact B1896507
  · exact B1896511
  · exact B1896515
  · exact B1896519
  · exact B1896523
  · exact B1896527
  · exact B1896531
  · exact B1896535
  · exact B1896539
  · exact B1896543
  · exact B1896547
  · exact B1896551
  · exact B1896555
  · exact B1896559
  · exact B1896563
  · exact B1896567
  · exact B1896571
  · exact B1896575
  · exact B1896579
  · exact B1896583
  · exact B1896587
  · exact B1896591
  · exact B1896595
  · exact B1896599
  · exact B1896603
  · exact B1896607
  · exact B1896611
  · exact B1896615
  · exact B1896619
  · exact B1896623
  · exact B1896627
  · exact B1896631
  · exact B1896635
  · exact B1896639
  · exact B1896643
  · exact B1896647
  · exact B1896651
  · exact B1896655
  · exact B1896659
  · exact B1896663
  · exact B1896667
  · exact B1896671
  · exact B1896675
  · exact B1896679
  · exact B1896683
  · exact B1896687
  · exact B1896691
  · exact B1896695
  · exact B1896699
  · exact B1896703
  · exact B1896707
  · exact B1896711
  · exact B1896715
  · exact B1896719
  · exact B1896723
  · exact B1896727
  · exact B1896731
  · exact B1896735
  · exact B1896739
  · exact B1896743
  · exact B1896747
  · exact B1896751
  · exact B1896755
  · exact B1896759
  · exact B1896763
  · exact B1896767
  · exact B1896771
  · exact B1896775
  · exact B1896779
  · exact B1896783
  · exact B1896787
  · exact B1896791
  · exact B1896795
  · exact B1896799
  · exact B1896803
  · exact B1896807
  · exact B1896811
  · exact B1896815
  · exact B1896819
  · exact B1896823
  · exact B1896827
  · exact B1896831
  · exact B1896835
  · exact B1896839
  · exact B1896843
  · exact B1896847
  · exact B1896851
  · exact B1896855
  · exact B1896859
  · exact B1896863
  · exact B1896867
  · exact B1896871
  · exact B1896875
  · exact B1896879
  · exact B1896883
  · exact B1896887
  · exact B1896891
  · exact B1896895
  · exact B1896899
  · exact B1896903
  · exact B1896907
  · exact B1896911
  · exact B1896915
  · exact B1896919
  · exact B1896923
  · exact B1896927
  · exact B1896931
  · exact B1896935
  · exact B1896939
  · exact B1896943
  · exact B1896947
  · exact B1896951
  · exact B1896955
  · exact B1896959
  · exact B1896963
  · exact B1896967
  · exact B1896971
  · exact B1896975
  · exact B1896979
  · exact B1896983
  · exact B1896987
  · exact B1896991
  · exact B1896995
  · exact B1896999
  · exact B1897003
  · exact B1897007
  · exact B1897011
  · exact B1897015
  · exact B1897019
  · exact B1897023
  · exact B1897027
  · exact B1897031
  · exact B1897035
  · exact B1897039
  · exact B1897043
  · exact B1897047
  · exact B1897051
  · exact B1897055
  · exact B1897059
  · exact B1897063
  · exact B1897067
  · exact B1897071
  · exact B1897075
  · exact B1897079
  · exact B1897083
  · exact B1897087
  · exact B1897091
  · exact B1897095
  · exact B1897099
  · exact B1897103
  · exact B1897107
  · exact B1897111
  · exact B1897115
  · exact B1897119
  · exact B1897123
  · exact B1897127
  · exact B1897131
  · exact B1897135
  · exact B1897139
  · exact B1897143
  · exact B1897147
  · exact B1897151
  · exact B1897155
  · exact B1897159
  · exact B1897163
  · exact B1897167
  · exact B1897171
  · exact B1897175
  · exact B1897179
  · exact B1897183
  · exact B1897187
  · exact B1897191
  · exact B1897195
  · exact B1897199
  · exact B1897203
  · exact B1897207
  · exact B1897211
  · exact B1897215
  · exact B1897219
  · exact B1897223
  · exact B1897227
  · exact B1897231
  · exact B1897235
  · exact B1897239
  · exact B1897243
  · exact B1897247
  · exact B1897251
  · exact B1897255
  · exact B1897259
  · exact B1897263
  · exact B1897267
  · exact B1897271
  · exact B1897275
  · exact B1897279
  · exact B1897283
  · exact B1897287
  · exact B1897291
  · exact B1897295
  · exact B1897299
  · exact B1897303
  · exact B1897307
  · exact B1897311
  · exact B1897315
  · exact B1897319
  · exact B1897323
  · exact B1897327
  · exact B1897331
  · exact B1897335
  · exact B1897339
  · exact B1897343
  · exact B1897347
  · exact B1897351
  · exact B1897355
  · exact B1897359
  · exact B1897363
  · exact B1897367
  · exact B1897371
  · exact B1897375
  · exact B1897379
  · exact B1897383
  · exact B1897387
  · exact B1897391
  · exact B1897395
  · exact B1897399
  · exact B1897403
  · exact B1897407
  · exact B1897411
  · exact B1897415
  · exact B1897419
  · exact B1897423
  · exact B1897427
  · exact B1897431
  · exact B1897435
theorem solution (m : ℕ) (hlo : 1895435 ≤ m) (hhi : m ≤ 1897435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 473858 ≤ j := by omega
    have hj2 : j ≤ 474358 := by omega
    have hb : Blo 1895435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
