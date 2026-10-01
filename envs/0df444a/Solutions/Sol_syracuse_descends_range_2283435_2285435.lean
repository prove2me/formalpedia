-- Prove2me | solution 1 for syracuse_descends_range_2283435_2285435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:49:39.392151+00:00
-- url     : https://prove2.me/submissions/ca0de9bf-54b7-42c5-b19e-1af3a19b9811

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

theorem B2568865 : Blo 2283435 2568865 := bbase (se 2 (by rfl) ⟨963324, by rfl⟩ : syracuseStep 2568865 = 1926649) (by norm_num)
theorem B3425153 : Blo 2283435 3425153 := bstep (se 2 (by rfl) ⟨1284432, by rfl⟩ : syracuseStep 3425153 = 2568865) B2568865
theorem B2283435 : Blo 2283435 2283435 := bstep (se 1 (by rfl) ⟨1712576, by rfl⟩ : syracuseStep 2283435 = 3425153) B3425153
theorem B5779957 : Blo 2283435 5779957 := bbase (se 5 (by rfl) ⟨270935, by rfl⟩ : syracuseStep 5779957 = 541871) (by norm_num)
theorem B7706609 : Blo 2283435 7706609 := bstep (se 2 (by rfl) ⟨2889978, by rfl⟩ : syracuseStep 7706609 = 5779957) B5779957
theorem B5137739 : Blo 2283435 5137739 := bstep (se 1 (by rfl) ⟨3853304, by rfl⟩ : syracuseStep 5137739 = 7706609) B7706609
theorem B3425159 : Blo 2283435 3425159 := bstep (se 1 (by rfl) ⟨2568869, by rfl⟩ : syracuseStep 3425159 = 5137739) B5137739
theorem B2283439 : Blo 2283435 2283439 := bstep (se 1 (by rfl) ⟨1712579, by rfl⟩ : syracuseStep 2283439 = 3425159) B3425159
theorem B3425165 : Blo 2283435 3425165 := bbase (se 3 (by rfl) ⟨642218, by rfl⟩ : syracuseStep 3425165 = 1284437) (by norm_num)
theorem B2283443 : Blo 2283435 2283443 := bstep (se 1 (by rfl) ⟨1712582, by rfl⟩ : syracuseStep 2283443 = 3425165) B3425165
theorem B5137757 : Blo 2283435 5137757 := bbase (se 3 (by rfl) ⟨963329, by rfl⟩ : syracuseStep 5137757 = 1926659) (by norm_num)
theorem B3425171 : Blo 2283435 3425171 := bstep (se 1 (by rfl) ⟨2568878, by rfl⟩ : syracuseStep 3425171 = 5137757) B5137757
theorem B2283447 : Blo 2283435 2283447 := bstep (se 1 (by rfl) ⟨1712585, by rfl⟩ : syracuseStep 2283447 = 3425171) B3425171
theorem B3853325 : Blo 2283435 3853325 := bbase (se 3 (by rfl) ⟨722498, by rfl⟩ : syracuseStep 3853325 = 1444997) (by norm_num)
theorem B2568883 : Blo 2283435 2568883 := bstep (se 1 (by rfl) ⟨1926662, by rfl⟩ : syracuseStep 2568883 = 3853325) B3853325
theorem B3425177 : Blo 2283435 3425177 := bstep (se 2 (by rfl) ⟨1284441, by rfl⟩ : syracuseStep 3425177 = 2568883) B2568883
theorem B2283451 : Blo 2283435 2283451 := bstep (se 1 (by rfl) ⟨1712588, by rfl⟩ : syracuseStep 2283451 = 3425177) B3425177
theorem B4629221 : Blo 2283435 4629221 := bbase (se 4 (by rfl) ⟨433989, by rfl⟩ : syracuseStep 4629221 = 867979) (by norm_num)
theorem B3086147 : Blo 2283435 3086147 := bstep (se 1 (by rfl) ⟨2314610, by rfl⟩ : syracuseStep 3086147 = 4629221) B4629221
theorem B8229725 : Blo 2283435 8229725 := bstep (se 3 (by rfl) ⟨1543073, by rfl⟩ : syracuseStep 8229725 = 3086147) B3086147
theorem B5486483 : Blo 2283435 5486483 := bstep (se 1 (by rfl) ⟨4114862, by rfl⟩ : syracuseStep 5486483 = 8229725) B8229725
theorem B3657655 : Blo 2283435 3657655 := bstep (se 1 (by rfl) ⟨2743241, by rfl⟩ : syracuseStep 3657655 = 5486483) B5486483
theorem B19507493 : Blo 2283435 19507493 := bstep (se 4 (by rfl) ⟨1828827, by rfl⟩ : syracuseStep 19507493 = 3657655) B3657655
theorem B13004995 : Blo 2283435 13004995 := bstep (se 1 (by rfl) ⟨9753746, by rfl⟩ : syracuseStep 13004995 = 19507493) B19507493
theorem B17339993 : Blo 2283435 17339993 := bstep (se 2 (by rfl) ⟨6502497, by rfl⟩ : syracuseStep 17339993 = 13004995) B13004995
theorem B11559995 : Blo 2283435 11559995 := bstep (se 1 (by rfl) ⟨8669996, by rfl⟩ : syracuseStep 11559995 = 17339993) B17339993
theorem B7706663 : Blo 2283435 7706663 := bstep (se 1 (by rfl) ⟨5779997, by rfl⟩ : syracuseStep 7706663 = 11559995) B11559995
theorem B5137775 : Blo 2283435 5137775 := bstep (se 1 (by rfl) ⟨3853331, by rfl⟩ : syracuseStep 5137775 = 7706663) B7706663
theorem B3425183 : Blo 2283435 3425183 := bstep (se 1 (by rfl) ⟨2568887, by rfl⟩ : syracuseStep 3425183 = 5137775) B5137775
theorem B2283455 : Blo 2283435 2283455 := bstep (se 1 (by rfl) ⟨1712591, by rfl⟩ : syracuseStep 2283455 = 3425183) B3425183
theorem B3425189 : Blo 2283435 3425189 := bbase (se 4 (by rfl) ⟨321111, by rfl⟩ : syracuseStep 3425189 = 642223) (by norm_num)
theorem B2283459 : Blo 2283435 2283459 := bstep (se 1 (by rfl) ⟨1712594, by rfl⟩ : syracuseStep 2283459 = 3425189) B3425189
theorem B2890009 : Blo 2283435 2890009 := bbase (se 2 (by rfl) ⟨1083753, by rfl⟩ : syracuseStep 2890009 = 2167507) (by norm_num)
theorem B3853345 : Blo 2283435 3853345 := bstep (se 2 (by rfl) ⟨1445004, by rfl⟩ : syracuseStep 3853345 = 2890009) B2890009
theorem B5137793 : Blo 2283435 5137793 := bstep (se 2 (by rfl) ⟨1926672, by rfl⟩ : syracuseStep 5137793 = 3853345) B3853345
theorem B3425195 : Blo 2283435 3425195 := bstep (se 1 (by rfl) ⟨2568896, by rfl⟩ : syracuseStep 3425195 = 5137793) B5137793
theorem B2283463 : Blo 2283435 2283463 := bstep (se 1 (by rfl) ⟨1712597, by rfl⟩ : syracuseStep 2283463 = 3425195) B3425195
theorem B2568901 : Blo 2283435 2568901 := bbase (se 4 (by rfl) ⟨240834, by rfl⟩ : syracuseStep 2568901 = 481669) (by norm_num)
theorem B3425201 : Blo 2283435 3425201 := bstep (se 2 (by rfl) ⟨1284450, by rfl⟩ : syracuseStep 3425201 = 2568901) B2568901
theorem B2283467 : Blo 2283435 2283467 := bstep (se 1 (by rfl) ⟨1712600, by rfl⟩ : syracuseStep 2283467 = 3425201) B3425201
theorem B4335029 : Blo 2283435 4335029 := bbase (se 5 (by rfl) ⟨203204, by rfl⟩ : syracuseStep 4335029 = 406409) (by norm_num)
theorem B2890019 : Blo 2283435 2890019 := bstep (se 1 (by rfl) ⟨2167514, by rfl⟩ : syracuseStep 2890019 = 4335029) B4335029
theorem B7706717 : Blo 2283435 7706717 := bstep (se 3 (by rfl) ⟨1445009, by rfl⟩ : syracuseStep 7706717 = 2890019) B2890019
theorem B5137811 : Blo 2283435 5137811 := bstep (se 1 (by rfl) ⟨3853358, by rfl⟩ : syracuseStep 5137811 = 7706717) B7706717
theorem B3425207 : Blo 2283435 3425207 := bstep (se 1 (by rfl) ⟨2568905, by rfl⟩ : syracuseStep 3425207 = 5137811) B5137811
theorem B2283471 : Blo 2283435 2283471 := bstep (se 1 (by rfl) ⟨1712603, by rfl⟩ : syracuseStep 2283471 = 3425207) B3425207
theorem B3425213 : Blo 2283435 3425213 := bbase (se 3 (by rfl) ⟨642227, by rfl⟩ : syracuseStep 3425213 = 1284455) (by norm_num)
theorem B2283475 : Blo 2283435 2283475 := bstep (se 1 (by rfl) ⟨1712606, by rfl⟩ : syracuseStep 2283475 = 3425213) B3425213
theorem B5137829 : Blo 2283435 5137829 := bbase (se 4 (by rfl) ⟨481671, by rfl⟩ : syracuseStep 5137829 = 963343) (by norm_num)
theorem B3425219 : Blo 2283435 3425219 := bstep (se 1 (by rfl) ⟨2568914, by rfl⟩ : syracuseStep 3425219 = 5137829) B5137829
theorem B2283479 : Blo 2283435 2283479 := bstep (se 1 (by rfl) ⟨1712609, by rfl⟩ : syracuseStep 2283479 = 3425219) B3425219
theorem B5780069 : Blo 2283435 5780069 := bbase (se 4 (by rfl) ⟨541881, by rfl⟩ : syracuseStep 5780069 = 1083763) (by norm_num)
theorem B3853379 : Blo 2283435 3853379 := bstep (se 1 (by rfl) ⟨2890034, by rfl⟩ : syracuseStep 3853379 = 5780069) B5780069
theorem B2568919 : Blo 2283435 2568919 := bstep (se 1 (by rfl) ⟨1926689, by rfl⟩ : syracuseStep 2568919 = 3853379) B3853379
theorem B3425225 : Blo 2283435 3425225 := bstep (se 2 (by rfl) ⟨1284459, by rfl⟩ : syracuseStep 3425225 = 2568919) B2568919
theorem B2283483 : Blo 2283435 2283483 := bstep (se 1 (by rfl) ⟨1712612, by rfl⟩ : syracuseStep 2283483 = 3425225) B3425225
theorem B6256597 : Blo 2283435 6256597 := bbase (se 7 (by rfl) ⟨73319, by rfl⟩ : syracuseStep 6256597 = 146639) (by norm_num)
theorem B8342129 : Blo 2283435 8342129 := bstep (se 2 (by rfl) ⟨3128298, by rfl⟩ : syracuseStep 8342129 = 6256597) B6256597
theorem B22245677 : Blo 2283435 22245677 := bstep (se 3 (by rfl) ⟨4171064, by rfl⟩ : syracuseStep 22245677 = 8342129) B8342129
theorem B14830451 : Blo 2283435 14830451 := bstep (se 1 (by rfl) ⟨11122838, by rfl⟩ : syracuseStep 14830451 = 22245677) B22245677
theorem B9886967 : Blo 2283435 9886967 := bstep (se 1 (by rfl) ⟨7415225, by rfl⟩ : syracuseStep 9886967 = 14830451) B14830451
theorem B6591311 : Blo 2283435 6591311 := bstep (se 1 (by rfl) ⟨4943483, by rfl⟩ : syracuseStep 6591311 = 9886967) B9886967
theorem B4394207 : Blo 2283435 4394207 := bstep (se 1 (by rfl) ⟨3295655, by rfl⟩ : syracuseStep 4394207 = 6591311) B6591311
theorem B11717885 : Blo 2283435 11717885 := bstep (se 3 (by rfl) ⟨2197103, by rfl⟩ : syracuseStep 11717885 = 4394207) B4394207
theorem B7811923 : Blo 2283435 7811923 := bstep (se 1 (by rfl) ⟨5858942, by rfl⟩ : syracuseStep 7811923 = 11717885) B11717885
theorem B10415897 : Blo 2283435 10415897 := bstep (se 2 (by rfl) ⟨3905961, by rfl⟩ : syracuseStep 10415897 = 7811923) B7811923
theorem B6943931 : Blo 2283435 6943931 := bstep (se 1 (by rfl) ⟨5207948, by rfl⟩ : syracuseStep 6943931 = 10415897) B10415897
theorem B4629287 : Blo 2283435 4629287 := bstep (se 1 (by rfl) ⟨3471965, by rfl⟩ : syracuseStep 4629287 = 6943931) B6943931
theorem B3086191 : Blo 2283435 3086191 := bstep (se 1 (by rfl) ⟨2314643, by rfl⟩ : syracuseStep 3086191 = 4629287) B4629287
theorem B4114921 : Blo 2283435 4114921 := bstep (se 2 (by rfl) ⟨1543095, by rfl⟩ : syracuseStep 4114921 = 3086191) B3086191
theorem B5486561 : Blo 2283435 5486561 := bstep (se 2 (by rfl) ⟨2057460, by rfl⟩ : syracuseStep 5486561 = 4114921) B4114921
theorem B3657707 : Blo 2283435 3657707 := bstep (se 1 (by rfl) ⟨2743280, by rfl⟩ : syracuseStep 3657707 = 5486561) B5486561
theorem B2438471 : Blo 2283435 2438471 := bstep (se 1 (by rfl) ⟨1828853, by rfl⟩ : syracuseStep 2438471 = 3657707) B3657707
theorem B6502589 : Blo 2283435 6502589 := bstep (se 3 (by rfl) ⟨1219235, by rfl⟩ : syracuseStep 6502589 = 2438471) B2438471
theorem B4335059 : Blo 2283435 4335059 := bstep (se 1 (by rfl) ⟨3251294, by rfl⟩ : syracuseStep 4335059 = 6502589) B6502589
theorem B11560157 : Blo 2283435 11560157 := bstep (se 3 (by rfl) ⟨2167529, by rfl⟩ : syracuseStep 11560157 = 4335059) B4335059
theorem B7706771 : Blo 2283435 7706771 := bstep (se 1 (by rfl) ⟨5780078, by rfl⟩ : syracuseStep 7706771 = 11560157) B11560157
theorem B5137847 : Blo 2283435 5137847 := bstep (se 1 (by rfl) ⟨3853385, by rfl⟩ : syracuseStep 5137847 = 7706771) B7706771
theorem B3425231 : Blo 2283435 3425231 := bstep (se 1 (by rfl) ⟨2568923, by rfl⟩ : syracuseStep 3425231 = 5137847) B5137847
theorem B2283487 : Blo 2283435 2283487 := bstep (se 1 (by rfl) ⟨1712615, by rfl⟩ : syracuseStep 2283487 = 3425231) B3425231
theorem B3425237 : Blo 2283435 3425237 := bbase (se 7 (by rfl) ⟨40139, by rfl⟩ : syracuseStep 3425237 = 80279) (by norm_num)
theorem B2283491 : Blo 2283435 2283491 := bstep (se 1 (by rfl) ⟨1712618, by rfl⟩ : syracuseStep 2283491 = 3425237) B3425237
theorem B8670149 : Blo 2283435 8670149 := bbase (se 4 (by rfl) ⟨812826, by rfl⟩ : syracuseStep 8670149 = 1625653) (by norm_num)
theorem B5780099 : Blo 2283435 5780099 := bstep (se 1 (by rfl) ⟨4335074, by rfl⟩ : syracuseStep 5780099 = 8670149) B8670149
theorem B3853399 : Blo 2283435 3853399 := bstep (se 1 (by rfl) ⟨2890049, by rfl⟩ : syracuseStep 3853399 = 5780099) B5780099
theorem B5137865 : Blo 2283435 5137865 := bstep (se 2 (by rfl) ⟨1926699, by rfl⟩ : syracuseStep 5137865 = 3853399) B3853399
theorem B3425243 : Blo 2283435 3425243 := bstep (se 1 (by rfl) ⟨2568932, by rfl⟩ : syracuseStep 3425243 = 5137865) B5137865
theorem B2283495 : Blo 2283435 2283495 := bstep (se 1 (by rfl) ⟨1712621, by rfl⟩ : syracuseStep 2283495 = 3425243) B3425243
theorem B2568937 : Blo 2283435 2568937 := bbase (se 2 (by rfl) ⟨963351, by rfl⟩ : syracuseStep 2568937 = 1926703) (by norm_num)
theorem B3425249 : Blo 2283435 3425249 := bstep (se 2 (by rfl) ⟨1284468, by rfl⟩ : syracuseStep 3425249 = 2568937) B2568937
theorem B2283499 : Blo 2283435 2283499 := bstep (se 1 (by rfl) ⟨1712624, by rfl⟩ : syracuseStep 2283499 = 3425249) B3425249
theorem B13005269 : Blo 2283435 13005269 := bbase (se 7 (by rfl) ⟨152405, by rfl⟩ : syracuseStep 13005269 = 304811) (by norm_num)
theorem B8670179 : Blo 2283435 8670179 := bstep (se 1 (by rfl) ⟨6502634, by rfl⟩ : syracuseStep 8670179 = 13005269) B13005269
theorem B5780119 : Blo 2283435 5780119 := bstep (se 1 (by rfl) ⟨4335089, by rfl⟩ : syracuseStep 5780119 = 8670179) B8670179
theorem B7706825 : Blo 2283435 7706825 := bstep (se 2 (by rfl) ⟨2890059, by rfl⟩ : syracuseStep 7706825 = 5780119) B5780119
theorem B5137883 : Blo 2283435 5137883 := bstep (se 1 (by rfl) ⟨3853412, by rfl⟩ : syracuseStep 5137883 = 7706825) B7706825
theorem B3425255 : Blo 2283435 3425255 := bstep (se 1 (by rfl) ⟨2568941, by rfl⟩ : syracuseStep 3425255 = 5137883) B5137883
theorem B2283503 : Blo 2283435 2283503 := bstep (se 1 (by rfl) ⟨1712627, by rfl⟩ : syracuseStep 2283503 = 3425255) B3425255
theorem B3425261 : Blo 2283435 3425261 := bbase (se 3 (by rfl) ⟨642236, by rfl⟩ : syracuseStep 3425261 = 1284473) (by norm_num)
theorem B2283507 : Blo 2283435 2283507 := bstep (se 1 (by rfl) ⟨1712630, by rfl⟩ : syracuseStep 2283507 = 3425261) B3425261
theorem B5137901 : Blo 2283435 5137901 := bbase (se 3 (by rfl) ⟨963356, by rfl⟩ : syracuseStep 5137901 = 1926713) (by norm_num)
theorem B3425267 : Blo 2283435 3425267 := bstep (se 1 (by rfl) ⟨2568950, by rfl⟩ : syracuseStep 3425267 = 5137901) B5137901
theorem B2283511 : Blo 2283435 2283511 := bstep (se 1 (by rfl) ⟨1712633, by rfl⟩ : syracuseStep 2283511 = 3425267) B3425267
theorem B5486629 : Blo 2283435 5486629 := bbase (se 4 (by rfl) ⟨514371, by rfl⟩ : syracuseStep 5486629 = 1028743) (by norm_num)
theorem B7315505 : Blo 2283435 7315505 := bstep (se 2 (by rfl) ⟨2743314, by rfl⟩ : syracuseStep 7315505 = 5486629) B5486629
theorem B4877003 : Blo 2283435 4877003 := bstep (se 1 (by rfl) ⟨3657752, by rfl⟩ : syracuseStep 4877003 = 7315505) B7315505
theorem B3251335 : Blo 2283435 3251335 := bstep (se 1 (by rfl) ⟨2438501, by rfl⟩ : syracuseStep 3251335 = 4877003) B4877003
theorem B4335113 : Blo 2283435 4335113 := bstep (se 2 (by rfl) ⟨1625667, by rfl⟩ : syracuseStep 4335113 = 3251335) B3251335
theorem B2890075 : Blo 2283435 2890075 := bstep (se 1 (by rfl) ⟨2167556, by rfl⟩ : syracuseStep 2890075 = 4335113) B4335113
theorem B3853433 : Blo 2283435 3853433 := bstep (se 2 (by rfl) ⟨1445037, by rfl⟩ : syracuseStep 3853433 = 2890075) B2890075
theorem B2568955 : Blo 2283435 2568955 := bstep (se 1 (by rfl) ⟨1926716, by rfl⟩ : syracuseStep 2568955 = 3853433) B3853433
theorem B3425273 : Blo 2283435 3425273 := bstep (se 2 (by rfl) ⟨1284477, by rfl⟩ : syracuseStep 3425273 = 2568955) B2568955
theorem B2283515 : Blo 2283435 2283515 := bstep (se 1 (by rfl) ⟨1712636, by rfl⟩ : syracuseStep 2283515 = 3425273) B3425273
theorem B4943549 : Blo 2283435 4943549 := bbase (se 3 (by rfl) ⟨926915, by rfl⟩ : syracuseStep 4943549 = 1853831) (by norm_num)
theorem B13182797 : Blo 2283435 13182797 := bstep (se 3 (by rfl) ⟨2471774, by rfl⟩ : syracuseStep 13182797 = 4943549) B4943549
theorem B8788531 : Blo 2283435 8788531 := bstep (se 1 (by rfl) ⟨6591398, by rfl⟩ : syracuseStep 8788531 = 13182797) B13182797
theorem B11718041 : Blo 2283435 11718041 := bstep (se 2 (by rfl) ⟨4394265, by rfl⟩ : syracuseStep 11718041 = 8788531) B8788531
theorem B31248109 : Blo 2283435 31248109 := bstep (se 3 (by rfl) ⟨5859020, by rfl⟩ : syracuseStep 31248109 = 11718041) B11718041
theorem B41664145 : Blo 2283435 41664145 := bstep (se 2 (by rfl) ⟨15624054, by rfl⟩ : syracuseStep 41664145 = 31248109) B31248109
theorem B55552193 : Blo 2283435 55552193 := bstep (se 2 (by rfl) ⟨20832072, by rfl⟩ : syracuseStep 55552193 = 41664145) B41664145
theorem B37034795 : Blo 2283435 37034795 := bstep (se 1 (by rfl) ⟨27776096, by rfl⟩ : syracuseStep 37034795 = 55552193) B55552193
theorem B24689863 : Blo 2283435 24689863 := bstep (se 1 (by rfl) ⟨18517397, by rfl⟩ : syracuseStep 24689863 = 37034795) B37034795
theorem B131679269 : Blo 2283435 131679269 := bstep (se 4 (by rfl) ⟨12344931, by rfl⟩ : syracuseStep 131679269 = 24689863) B24689863
theorem B87786179 : Blo 2283435 87786179 := bstep (se 1 (by rfl) ⟨65839634, by rfl⟩ : syracuseStep 87786179 = 131679269) B131679269
theorem B58524119 : Blo 2283435 58524119 := bstep (se 1 (by rfl) ⟨43893089, by rfl⟩ : syracuseStep 58524119 = 87786179) B87786179
theorem B39016079 : Blo 2283435 39016079 := bstep (se 1 (by rfl) ⟨29262059, by rfl⟩ : syracuseStep 39016079 = 58524119) B58524119
theorem B26010719 : Blo 2283435 26010719 := bstep (se 1 (by rfl) ⟨19508039, by rfl⟩ : syracuseStep 26010719 = 39016079) B39016079
theorem B17340479 : Blo 2283435 17340479 := bstep (se 1 (by rfl) ⟨13005359, by rfl⟩ : syracuseStep 17340479 = 26010719) B26010719
theorem B11560319 : Blo 2283435 11560319 := bstep (se 1 (by rfl) ⟨8670239, by rfl⟩ : syracuseStep 11560319 = 17340479) B17340479
theorem B7706879 : Blo 2283435 7706879 := bstep (se 1 (by rfl) ⟨5780159, by rfl⟩ : syracuseStep 7706879 = 11560319) B11560319
theorem B5137919 : Blo 2283435 5137919 := bstep (se 1 (by rfl) ⟨3853439, by rfl⟩ : syracuseStep 5137919 = 7706879) B7706879
theorem B3425279 : Blo 2283435 3425279 := bstep (se 1 (by rfl) ⟨2568959, by rfl⟩ : syracuseStep 3425279 = 5137919) B5137919
theorem B2283519 : Blo 2283435 2283519 := bstep (se 1 (by rfl) ⟨1712639, by rfl⟩ : syracuseStep 2283519 = 3425279) B3425279
theorem B3425285 : Blo 2283435 3425285 := bbase (se 4 (by rfl) ⟨321120, by rfl⟩ : syracuseStep 3425285 = 642241) (by norm_num)
theorem B2283523 : Blo 2283435 2283523 := bstep (se 1 (by rfl) ⟨1712642, by rfl⟩ : syracuseStep 2283523 = 3425285) B3425285
theorem B3853453 : Blo 2283435 3853453 := bbase (se 3 (by rfl) ⟨722522, by rfl⟩ : syracuseStep 3853453 = 1445045) (by norm_num)
theorem B5137937 : Blo 2283435 5137937 := bstep (se 2 (by rfl) ⟨1926726, by rfl⟩ : syracuseStep 5137937 = 3853453) B3853453
theorem B3425291 : Blo 2283435 3425291 := bstep (se 1 (by rfl) ⟨2568968, by rfl⟩ : syracuseStep 3425291 = 5137937) B5137937
theorem B2283527 : Blo 2283435 2283527 := bstep (se 1 (by rfl) ⟨1712645, by rfl⟩ : syracuseStep 2283527 = 3425291) B3425291
theorem B2568973 : Blo 2283435 2568973 := bbase (se 3 (by rfl) ⟨481682, by rfl⟩ : syracuseStep 2568973 = 963365) (by norm_num)
theorem B3425297 : Blo 2283435 3425297 := bstep (se 2 (by rfl) ⟨1284486, by rfl⟩ : syracuseStep 3425297 = 2568973) B2568973
theorem B2283531 : Blo 2283435 2283531 := bstep (se 1 (by rfl) ⟨1712648, by rfl⟩ : syracuseStep 2283531 = 3425297) B3425297
theorem B7706933 : Blo 2283435 7706933 := bbase (se 5 (by rfl) ⟨361262, by rfl⟩ : syracuseStep 7706933 = 722525) (by norm_num)
theorem B5137955 : Blo 2283435 5137955 := bstep (se 1 (by rfl) ⟨3853466, by rfl⟩ : syracuseStep 5137955 = 7706933) B7706933
theorem B3425303 : Blo 2283435 3425303 := bstep (se 1 (by rfl) ⟨2568977, by rfl⟩ : syracuseStep 3425303 = 5137955) B5137955
theorem B2283535 : Blo 2283435 2283535 := bstep (se 1 (by rfl) ⟨1712651, by rfl⟩ : syracuseStep 2283535 = 3425303) B3425303
theorem B3425309 : Blo 2283435 3425309 := bbase (se 3 (by rfl) ⟨642245, by rfl⟩ : syracuseStep 3425309 = 1284491) (by norm_num)
theorem B2283539 : Blo 2283435 2283539 := bstep (se 1 (by rfl) ⟨1712654, by rfl⟩ : syracuseStep 2283539 = 3425309) B3425309
theorem B5137973 : Blo 2283435 5137973 := bbase (se 5 (by rfl) ⟨240842, by rfl⟩ : syracuseStep 5137973 = 481685) (by norm_num)
theorem B3425315 : Blo 2283435 3425315 := bstep (se 1 (by rfl) ⟨2568986, by rfl⟩ : syracuseStep 3425315 = 5137973) B5137973
theorem B2283543 : Blo 2283435 2283543 := bstep (se 1 (by rfl) ⟨1712657, by rfl⟩ : syracuseStep 2283543 = 3425315) B3425315
theorem B4115029 : Blo 2283435 4115029 := bbase (se 8 (by rfl) ⟨24111, by rfl⟩ : syracuseStep 4115029 = 48223) (by norm_num)
theorem B5486705 : Blo 2283435 5486705 := bstep (se 2 (by rfl) ⟨2057514, by rfl⟩ : syracuseStep 5486705 = 4115029) B4115029
theorem B3657803 : Blo 2283435 3657803 := bstep (se 1 (by rfl) ⟨2743352, by rfl⟩ : syracuseStep 3657803 = 5486705) B5486705
theorem B9754141 : Blo 2283435 9754141 := bstep (se 3 (by rfl) ⟨1828901, by rfl⟩ : syracuseStep 9754141 = 3657803) B3657803
theorem B13005521 : Blo 2283435 13005521 := bstep (se 2 (by rfl) ⟨4877070, by rfl⟩ : syracuseStep 13005521 = 9754141) B9754141
theorem B8670347 : Blo 2283435 8670347 := bstep (se 1 (by rfl) ⟨6502760, by rfl⟩ : syracuseStep 8670347 = 13005521) B13005521
theorem B5780231 : Blo 2283435 5780231 := bstep (se 1 (by rfl) ⟨4335173, by rfl⟩ : syracuseStep 5780231 = 8670347) B8670347
theorem B3853487 : Blo 2283435 3853487 := bstep (se 1 (by rfl) ⟨2890115, by rfl⟩ : syracuseStep 3853487 = 5780231) B5780231
theorem B2568991 : Blo 2283435 2568991 := bstep (se 1 (by rfl) ⟨1926743, by rfl⟩ : syracuseStep 2568991 = 3853487) B3853487
theorem B3425321 : Blo 2283435 3425321 := bstep (se 2 (by rfl) ⟨1284495, by rfl⟩ : syracuseStep 3425321 = 2568991) B2568991
theorem B2283547 : Blo 2283435 2283547 := bstep (se 1 (by rfl) ⟨1712660, by rfl⟩ : syracuseStep 2283547 = 3425321) B3425321
theorem B2743357 : Blo 2283435 2743357 := bbase (se 3 (by rfl) ⟨514379, by rfl⟩ : syracuseStep 2743357 = 1028759) (by norm_num)
theorem B3657809 : Blo 2283435 3657809 := bstep (se 2 (by rfl) ⟨1371678, by rfl⟩ : syracuseStep 3657809 = 2743357) B2743357
theorem B9754157 : Blo 2283435 9754157 := bstep (se 3 (by rfl) ⟨1828904, by rfl⟩ : syracuseStep 9754157 = 3657809) B3657809
theorem B6502771 : Blo 2283435 6502771 := bstep (se 1 (by rfl) ⟨4877078, by rfl⟩ : syracuseStep 6502771 = 9754157) B9754157
theorem B8670361 : Blo 2283435 8670361 := bstep (se 2 (by rfl) ⟨3251385, by rfl⟩ : syracuseStep 8670361 = 6502771) B6502771
theorem B11560481 : Blo 2283435 11560481 := bstep (se 2 (by rfl) ⟨4335180, by rfl⟩ : syracuseStep 11560481 = 8670361) B8670361
theorem B7706987 : Blo 2283435 7706987 := bstep (se 1 (by rfl) ⟨5780240, by rfl⟩ : syracuseStep 7706987 = 11560481) B11560481
theorem B5137991 : Blo 2283435 5137991 := bstep (se 1 (by rfl) ⟨3853493, by rfl⟩ : syracuseStep 5137991 = 7706987) B7706987
theorem B3425327 : Blo 2283435 3425327 := bstep (se 1 (by rfl) ⟨2568995, by rfl⟩ : syracuseStep 3425327 = 5137991) B5137991
theorem B2283551 : Blo 2283435 2283551 := bstep (se 1 (by rfl) ⟨1712663, by rfl⟩ : syracuseStep 2283551 = 3425327) B3425327
theorem B3425333 : Blo 2283435 3425333 := bbase (se 5 (by rfl) ⟨160562, by rfl⟩ : syracuseStep 3425333 = 321125) (by norm_num)
theorem B2283555 : Blo 2283435 2283555 := bstep (se 1 (by rfl) ⟨1712666, by rfl⟩ : syracuseStep 2283555 = 3425333) B3425333
theorem B5780261 : Blo 2283435 5780261 := bbase (se 4 (by rfl) ⟨541899, by rfl⟩ : syracuseStep 5780261 = 1083799) (by norm_num)
theorem B3853507 : Blo 2283435 3853507 := bstep (se 1 (by rfl) ⟨2890130, by rfl⟩ : syracuseStep 3853507 = 5780261) B5780261
theorem B5138009 : Blo 2283435 5138009 := bstep (se 2 (by rfl) ⟨1926753, by rfl⟩ : syracuseStep 5138009 = 3853507) B3853507
theorem B3425339 : Blo 2283435 3425339 := bstep (se 1 (by rfl) ⟨2569004, by rfl⟩ : syracuseStep 3425339 = 5138009) B5138009
theorem B2283559 : Blo 2283435 2283559 := bstep (se 1 (by rfl) ⟨1712669, by rfl⟩ : syracuseStep 2283559 = 3425339) B3425339
theorem B2569009 : Blo 2283435 2569009 := bbase (se 2 (by rfl) ⟨963378, by rfl⟩ : syracuseStep 2569009 = 1926757) (by norm_num)
theorem B3425345 : Blo 2283435 3425345 := bstep (se 2 (by rfl) ⟨1284504, by rfl⟩ : syracuseStep 3425345 = 2569009) B2569009
theorem B2283563 : Blo 2283435 2283563 := bstep (se 1 (by rfl) ⟨1712672, by rfl⟩ : syracuseStep 2283563 = 3425345) B3425345
theorem B7812197 : Blo 2283435 7812197 := bbase (se 4 (by rfl) ⟨732393, by rfl⟩ : syracuseStep 7812197 = 1464787) (by norm_num)
theorem B5208131 : Blo 2283435 5208131 := bstep (se 1 (by rfl) ⟨3906098, by rfl⟩ : syracuseStep 5208131 = 7812197) B7812197
theorem B3472087 : Blo 2283435 3472087 := bstep (se 1 (by rfl) ⟨2604065, by rfl⟩ : syracuseStep 3472087 = 5208131) B5208131
theorem B4629449 : Blo 2283435 4629449 := bstep (se 2 (by rfl) ⟨1736043, by rfl⟩ : syracuseStep 4629449 = 3472087) B3472087
theorem B3086299 : Blo 2283435 3086299 := bstep (se 1 (by rfl) ⟨2314724, by rfl⟩ : syracuseStep 3086299 = 4629449) B4629449
theorem B4115065 : Blo 2283435 4115065 := bstep (se 2 (by rfl) ⟨1543149, by rfl⟩ : syracuseStep 4115065 = 3086299) B3086299
theorem B5486753 : Blo 2283435 5486753 := bstep (se 2 (by rfl) ⟨2057532, by rfl⟩ : syracuseStep 5486753 = 4115065) B4115065
theorem B3657835 : Blo 2283435 3657835 := bstep (se 1 (by rfl) ⟨2743376, by rfl⟩ : syracuseStep 3657835 = 5486753) B5486753
theorem B4877113 : Blo 2283435 4877113 := bstep (se 2 (by rfl) ⟨1828917, by rfl⟩ : syracuseStep 4877113 = 3657835) B3657835
theorem B6502817 : Blo 2283435 6502817 := bstep (se 2 (by rfl) ⟨2438556, by rfl⟩ : syracuseStep 6502817 = 4877113) B4877113
theorem B4335211 : Blo 2283435 4335211 := bstep (se 1 (by rfl) ⟨3251408, by rfl⟩ : syracuseStep 4335211 = 6502817) B6502817
theorem B5780281 : Blo 2283435 5780281 := bstep (se 2 (by rfl) ⟨2167605, by rfl⟩ : syracuseStep 5780281 = 4335211) B4335211
theorem B7707041 : Blo 2283435 7707041 := bstep (se 2 (by rfl) ⟨2890140, by rfl⟩ : syracuseStep 7707041 = 5780281) B5780281
theorem B5138027 : Blo 2283435 5138027 := bstep (se 1 (by rfl) ⟨3853520, by rfl⟩ : syracuseStep 5138027 = 7707041) B7707041
theorem B3425351 : Blo 2283435 3425351 := bstep (se 1 (by rfl) ⟨2569013, by rfl⟩ : syracuseStep 3425351 = 5138027) B5138027
theorem B2283567 : Blo 2283435 2283567 := bstep (se 1 (by rfl) ⟨1712675, by rfl⟩ : syracuseStep 2283567 = 3425351) B3425351
theorem B3425357 : Blo 2283435 3425357 := bbase (se 3 (by rfl) ⟨642254, by rfl⟩ : syracuseStep 3425357 = 1284509) (by norm_num)
theorem B2283571 : Blo 2283435 2283571 := bstep (se 1 (by rfl) ⟨1712678, by rfl⟩ : syracuseStep 2283571 = 3425357) B3425357
theorem B5138045 : Blo 2283435 5138045 := bbase (se 3 (by rfl) ⟨963383, by rfl⟩ : syracuseStep 5138045 = 1926767) (by norm_num)
theorem B3425363 : Blo 2283435 3425363 := bstep (se 1 (by rfl) ⟨2569022, by rfl⟩ : syracuseStep 3425363 = 5138045) B5138045
theorem B2283575 : Blo 2283435 2283575 := bstep (se 1 (by rfl) ⟨1712681, by rfl⟩ : syracuseStep 2283575 = 3425363) B3425363
theorem B3853541 : Blo 2283435 3853541 := bbase (se 4 (by rfl) ⟨361269, by rfl⟩ : syracuseStep 3853541 = 722539) (by norm_num)
theorem B2569027 : Blo 2283435 2569027 := bstep (se 1 (by rfl) ⟨1926770, by rfl⟩ : syracuseStep 2569027 = 3853541) B3853541
theorem B3425369 : Blo 2283435 3425369 := bstep (se 2 (by rfl) ⟨1284513, by rfl⟩ : syracuseStep 3425369 = 2569027) B2569027
theorem B2283579 : Blo 2283435 2283579 := bstep (se 1 (by rfl) ⟨1712684, by rfl⟩ : syracuseStep 2283579 = 3425369) B3425369
theorem B3906125 : Blo 2283435 3906125 := bbase (se 3 (by rfl) ⟨732398, by rfl⟩ : syracuseStep 3906125 = 1464797) (by norm_num)
theorem B2604083 : Blo 2283435 2604083 := bstep (se 1 (by rfl) ⟨1953062, by rfl⟩ : syracuseStep 2604083 = 3906125) B3906125
theorem B6944221 : Blo 2283435 6944221 := bstep (se 3 (by rfl) ⟨1302041, by rfl⟩ : syracuseStep 6944221 = 2604083) B2604083
theorem B9258961 : Blo 2283435 9258961 := bstep (se 2 (by rfl) ⟨3472110, by rfl⟩ : syracuseStep 9258961 = 6944221) B6944221
theorem B12345281 : Blo 2283435 12345281 := bstep (se 2 (by rfl) ⟨4629480, by rfl⟩ : syracuseStep 12345281 = 9258961) B9258961
theorem B8230187 : Blo 2283435 8230187 := bstep (se 1 (by rfl) ⟨6172640, by rfl⟩ : syracuseStep 8230187 = 12345281) B12345281
theorem B5486791 : Blo 2283435 5486791 := bstep (se 1 (by rfl) ⟨4115093, by rfl⟩ : syracuseStep 5486791 = 8230187) B8230187
theorem B7315721 : Blo 2283435 7315721 := bstep (se 2 (by rfl) ⟨2743395, by rfl⟩ : syracuseStep 7315721 = 5486791) B5486791
theorem B4877147 : Blo 2283435 4877147 := bstep (se 1 (by rfl) ⟨3657860, by rfl⟩ : syracuseStep 4877147 = 7315721) B7315721
theorem B3251431 : Blo 2283435 3251431 := bstep (se 1 (by rfl) ⟨2438573, by rfl⟩ : syracuseStep 3251431 = 4877147) B4877147
theorem B17340965 : Blo 2283435 17340965 := bstep (se 4 (by rfl) ⟨1625715, by rfl⟩ : syracuseStep 17340965 = 3251431) B3251431
theorem B11560643 : Blo 2283435 11560643 := bstep (se 1 (by rfl) ⟨8670482, by rfl⟩ : syracuseStep 11560643 = 17340965) B17340965
theorem B7707095 : Blo 2283435 7707095 := bstep (se 1 (by rfl) ⟨5780321, by rfl⟩ : syracuseStep 7707095 = 11560643) B11560643
theorem B5138063 : Blo 2283435 5138063 := bstep (se 1 (by rfl) ⟨3853547, by rfl⟩ : syracuseStep 5138063 = 7707095) B7707095
theorem B3425375 : Blo 2283435 3425375 := bstep (se 1 (by rfl) ⟨2569031, by rfl⟩ : syracuseStep 3425375 = 5138063) B5138063
theorem B2283583 : Blo 2283435 2283583 := bstep (se 1 (by rfl) ⟨1712687, by rfl⟩ : syracuseStep 2283583 = 3425375) B3425375
theorem B3425381 : Blo 2283435 3425381 := bbase (se 4 (by rfl) ⟨321129, by rfl⟩ : syracuseStep 3425381 = 642259) (by norm_num)
theorem B2283587 : Blo 2283435 2283587 := bstep (se 1 (by rfl) ⟨1712690, by rfl⟩ : syracuseStep 2283587 = 3425381) B3425381
theorem B4877165 : Blo 2283435 4877165 := bbase (se 3 (by rfl) ⟨914468, by rfl⟩ : syracuseStep 4877165 = 1828937) (by norm_num)
theorem B3251443 : Blo 2283435 3251443 := bstep (se 1 (by rfl) ⟨2438582, by rfl⟩ : syracuseStep 3251443 = 4877165) B4877165
theorem B4335257 : Blo 2283435 4335257 := bstep (se 2 (by rfl) ⟨1625721, by rfl⟩ : syracuseStep 4335257 = 3251443) B3251443
theorem B2890171 : Blo 2283435 2890171 := bstep (se 1 (by rfl) ⟨2167628, by rfl⟩ : syracuseStep 2890171 = 4335257) B4335257
theorem B3853561 : Blo 2283435 3853561 := bstep (se 2 (by rfl) ⟨1445085, by rfl⟩ : syracuseStep 3853561 = 2890171) B2890171
theorem B5138081 : Blo 2283435 5138081 := bstep (se 2 (by rfl) ⟨1926780, by rfl⟩ : syracuseStep 5138081 = 3853561) B3853561
theorem B3425387 : Blo 2283435 3425387 := bstep (se 1 (by rfl) ⟨2569040, by rfl⟩ : syracuseStep 3425387 = 5138081) B5138081
theorem B2283591 : Blo 2283435 2283591 := bstep (se 1 (by rfl) ⟨1712693, by rfl⟩ : syracuseStep 2283591 = 3425387) B3425387
theorem B2569045 : Blo 2283435 2569045 := bbase (se 9 (by rfl) ⟨7526, by rfl⟩ : syracuseStep 2569045 = 15053) (by norm_num)
theorem B3425393 : Blo 2283435 3425393 := bstep (se 2 (by rfl) ⟨1284522, by rfl⟩ : syracuseStep 3425393 = 2569045) B2569045
theorem B2283595 : Blo 2283435 2283595 := bstep (se 1 (by rfl) ⟨1712696, by rfl⟩ : syracuseStep 2283595 = 3425393) B3425393
theorem B2890181 : Blo 2283435 2890181 := bbase (se 4 (by rfl) ⟨270954, by rfl⟩ : syracuseStep 2890181 = 541909) (by norm_num)
theorem B7707149 : Blo 2283435 7707149 := bstep (se 3 (by rfl) ⟨1445090, by rfl⟩ : syracuseStep 7707149 = 2890181) B2890181
theorem B5138099 : Blo 2283435 5138099 := bstep (se 1 (by rfl) ⟨3853574, by rfl⟩ : syracuseStep 5138099 = 7707149) B7707149
theorem B3425399 : Blo 2283435 3425399 := bstep (se 1 (by rfl) ⟨2569049, by rfl⟩ : syracuseStep 3425399 = 5138099) B5138099
theorem B2283599 : Blo 2283435 2283599 := bstep (se 1 (by rfl) ⟨1712699, by rfl⟩ : syracuseStep 2283599 = 3425399) B3425399
theorem B3425405 : Blo 2283435 3425405 := bbase (se 3 (by rfl) ⟨642263, by rfl⟩ : syracuseStep 3425405 = 1284527) (by norm_num)
theorem B2283603 : Blo 2283435 2283603 := bstep (se 1 (by rfl) ⟨1712702, by rfl⟩ : syracuseStep 2283603 = 3425405) B3425405
theorem B5138117 : Blo 2283435 5138117 := bbase (se 4 (by rfl) ⟨481698, by rfl⟩ : syracuseStep 5138117 = 963397) (by norm_num)
theorem B3425411 : Blo 2283435 3425411 := bstep (se 1 (by rfl) ⟨2569058, by rfl⟩ : syracuseStep 3425411 = 5138117) B5138117
theorem B2283607 : Blo 2283435 2283607 := bstep (se 1 (by rfl) ⟨1712705, by rfl⟩ : syracuseStep 2283607 = 3425411) B3425411
theorem B3906173 : Blo 2283435 3906173 := bbase (se 3 (by rfl) ⟨732407, by rfl⟩ : syracuseStep 3906173 = 1464815) (by norm_num)
theorem B2604115 : Blo 2283435 2604115 := bstep (se 1 (by rfl) ⟨1953086, by rfl⟩ : syracuseStep 2604115 = 3906173) B3906173
theorem B3472153 : Blo 2283435 3472153 := bstep (se 2 (by rfl) ⟨1302057, by rfl⟩ : syracuseStep 3472153 = 2604115) B2604115
theorem B18518149 : Blo 2283435 18518149 := bstep (se 4 (by rfl) ⟨1736076, by rfl⟩ : syracuseStep 18518149 = 3472153) B3472153
theorem B24690865 : Blo 2283435 24690865 := bstep (se 2 (by rfl) ⟨9259074, by rfl⟩ : syracuseStep 24690865 = 18518149) B18518149
theorem B32921153 : Blo 2283435 32921153 := bstep (se 2 (by rfl) ⟨12345432, by rfl⟩ : syracuseStep 32921153 = 24690865) B24690865
theorem B21947435 : Blo 2283435 21947435 := bstep (se 1 (by rfl) ⟨16460576, by rfl⟩ : syracuseStep 21947435 = 32921153) B32921153
theorem B14631623 : Blo 2283435 14631623 := bstep (se 1 (by rfl) ⟨10973717, by rfl⟩ : syracuseStep 14631623 = 21947435) B21947435
theorem B9754415 : Blo 2283435 9754415 := bstep (se 1 (by rfl) ⟨7315811, by rfl⟩ : syracuseStep 9754415 = 14631623) B14631623
theorem B6502943 : Blo 2283435 6502943 := bstep (se 1 (by rfl) ⟨4877207, by rfl⟩ : syracuseStep 6502943 = 9754415) B9754415
theorem B4335295 : Blo 2283435 4335295 := bstep (se 1 (by rfl) ⟨3251471, by rfl⟩ : syracuseStep 4335295 = 6502943) B6502943
theorem B5780393 : Blo 2283435 5780393 := bstep (se 2 (by rfl) ⟨2167647, by rfl⟩ : syracuseStep 5780393 = 4335295) B4335295
theorem B3853595 : Blo 2283435 3853595 := bstep (se 1 (by rfl) ⟨2890196, by rfl⟩ : syracuseStep 3853595 = 5780393) B5780393
theorem B2569063 : Blo 2283435 2569063 := bstep (se 1 (by rfl) ⟨1926797, by rfl⟩ : syracuseStep 2569063 = 3853595) B3853595
theorem B3425417 : Blo 2283435 3425417 := bstep (se 2 (by rfl) ⟨1284531, by rfl⟩ : syracuseStep 3425417 = 2569063) B2569063
theorem B2283611 : Blo 2283435 2283611 := bstep (se 1 (by rfl) ⟨1712708, by rfl⟩ : syracuseStep 2283611 = 3425417) B3425417
theorem B11560805 : Blo 2283435 11560805 := bbase (se 4 (by rfl) ⟨1083825, by rfl⟩ : syracuseStep 11560805 = 2167651) (by norm_num)
theorem B7707203 : Blo 2283435 7707203 := bstep (se 1 (by rfl) ⟨5780402, by rfl⟩ : syracuseStep 7707203 = 11560805) B11560805
theorem B5138135 : Blo 2283435 5138135 := bstep (se 1 (by rfl) ⟨3853601, by rfl⟩ : syracuseStep 5138135 = 7707203) B7707203
theorem B3425423 : Blo 2283435 3425423 := bstep (se 1 (by rfl) ⟨2569067, by rfl⟩ : syracuseStep 3425423 = 5138135) B5138135
theorem B2283615 : Blo 2283435 2283615 := bstep (se 1 (by rfl) ⟨1712711, by rfl⟩ : syracuseStep 2283615 = 3425423) B3425423
theorem B3425429 : Blo 2283435 3425429 := bbase (se 6 (by rfl) ⟨80283, by rfl⟩ : syracuseStep 3425429 = 160567) (by norm_num)
theorem B2283619 : Blo 2283435 2283619 := bstep (se 1 (by rfl) ⟨1712714, by rfl⟩ : syracuseStep 2283619 = 3425429) B3425429
theorem B2929645 : Blo 2283435 2929645 := bbase (se 3 (by rfl) ⟨549308, by rfl⟩ : syracuseStep 2929645 = 1098617) (by norm_num)
theorem B3906193 : Blo 2283435 3906193 := bstep (se 2 (by rfl) ⟨1464822, by rfl⟩ : syracuseStep 3906193 = 2929645) B2929645
theorem B5208257 : Blo 2283435 5208257 := bstep (se 2 (by rfl) ⟨1953096, by rfl⟩ : syracuseStep 5208257 = 3906193) B3906193
theorem B13888685 : Blo 2283435 13888685 := bstep (se 3 (by rfl) ⟨2604128, by rfl⟩ : syracuseStep 13888685 = 5208257) B5208257
theorem B9259123 : Blo 2283435 9259123 := bstep (se 1 (by rfl) ⟨6944342, by rfl⟩ : syracuseStep 9259123 = 13888685) B13888685
theorem B12345497 : Blo 2283435 12345497 := bstep (se 2 (by rfl) ⟨4629561, by rfl⟩ : syracuseStep 12345497 = 9259123) B9259123
theorem B8230331 : Blo 2283435 8230331 := bstep (se 1 (by rfl) ⟨6172748, by rfl⟩ : syracuseStep 8230331 = 12345497) B12345497
theorem B5486887 : Blo 2283435 5486887 := bstep (se 1 (by rfl) ⟨4115165, by rfl⟩ : syracuseStep 5486887 = 8230331) B8230331
theorem B7315849 : Blo 2283435 7315849 := bstep (se 2 (by rfl) ⟨2743443, by rfl⟩ : syracuseStep 7315849 = 5486887) B5486887
theorem B9754465 : Blo 2283435 9754465 := bstep (se 2 (by rfl) ⟨3657924, by rfl⟩ : syracuseStep 9754465 = 7315849) B7315849
theorem B13005953 : Blo 2283435 13005953 := bstep (se 2 (by rfl) ⟨4877232, by rfl⟩ : syracuseStep 13005953 = 9754465) B9754465
theorem B8670635 : Blo 2283435 8670635 := bstep (se 1 (by rfl) ⟨6502976, by rfl⟩ : syracuseStep 8670635 = 13005953) B13005953
theorem B5780423 : Blo 2283435 5780423 := bstep (se 1 (by rfl) ⟨4335317, by rfl⟩ : syracuseStep 5780423 = 8670635) B8670635
theorem B3853615 : Blo 2283435 3853615 := bstep (se 1 (by rfl) ⟨2890211, by rfl⟩ : syracuseStep 3853615 = 5780423) B5780423
theorem B5138153 : Blo 2283435 5138153 := bstep (se 2 (by rfl) ⟨1926807, by rfl⟩ : syracuseStep 5138153 = 3853615) B3853615
theorem B3425435 : Blo 2283435 3425435 := bstep (se 1 (by rfl) ⟨2569076, by rfl⟩ : syracuseStep 3425435 = 5138153) B5138153
theorem B2283623 : Blo 2283435 2283623 := bstep (se 1 (by rfl) ⟨1712717, by rfl⟩ : syracuseStep 2283623 = 3425435) B3425435
theorem B2569081 : Blo 2283435 2569081 := bbase (se 2 (by rfl) ⟨963405, by rfl⟩ : syracuseStep 2569081 = 1926811) (by norm_num)
theorem B3425441 : Blo 2283435 3425441 := bstep (se 2 (by rfl) ⟨1284540, by rfl⟩ : syracuseStep 3425441 = 2569081) B2569081
theorem B2283627 : Blo 2283435 2283627 := bstep (se 1 (by rfl) ⟨1712720, by rfl⟩ : syracuseStep 2283627 = 3425441) B3425441
theorem B2743453 : Blo 2283435 2743453 := bbase (se 3 (by rfl) ⟨514397, by rfl⟩ : syracuseStep 2743453 = 1028795) (by norm_num)
theorem B14631749 : Blo 2283435 14631749 := bstep (se 4 (by rfl) ⟨1371726, by rfl⟩ : syracuseStep 14631749 = 2743453) B2743453
theorem B9754499 : Blo 2283435 9754499 := bstep (se 1 (by rfl) ⟨7315874, by rfl⟩ : syracuseStep 9754499 = 14631749) B14631749
theorem B6502999 : Blo 2283435 6502999 := bstep (se 1 (by rfl) ⟨4877249, by rfl⟩ : syracuseStep 6502999 = 9754499) B9754499
theorem B8670665 : Blo 2283435 8670665 := bstep (se 2 (by rfl) ⟨3251499, by rfl⟩ : syracuseStep 8670665 = 6502999) B6502999
theorem B5780443 : Blo 2283435 5780443 := bstep (se 1 (by rfl) ⟨4335332, by rfl⟩ : syracuseStep 5780443 = 8670665) B8670665
theorem B7707257 : Blo 2283435 7707257 := bstep (se 2 (by rfl) ⟨2890221, by rfl⟩ : syracuseStep 7707257 = 5780443) B5780443
theorem B5138171 : Blo 2283435 5138171 := bstep (se 1 (by rfl) ⟨3853628, by rfl⟩ : syracuseStep 5138171 = 7707257) B7707257
theorem B3425447 : Blo 2283435 3425447 := bstep (se 1 (by rfl) ⟨2569085, by rfl⟩ : syracuseStep 3425447 = 5138171) B5138171
theorem B2283631 : Blo 2283435 2283631 := bstep (se 1 (by rfl) ⟨1712723, by rfl⟩ : syracuseStep 2283631 = 3425447) B3425447
theorem B3425453 : Blo 2283435 3425453 := bbase (se 3 (by rfl) ⟨642272, by rfl⟩ : syracuseStep 3425453 = 1284545) (by norm_num)
theorem B2283635 : Blo 2283435 2283635 := bstep (se 1 (by rfl) ⟨1712726, by rfl⟩ : syracuseStep 2283635 = 3425453) B3425453
theorem B5138189 : Blo 2283435 5138189 := bbase (se 3 (by rfl) ⟨963410, by rfl⟩ : syracuseStep 5138189 = 1926821) (by norm_num)
theorem B3425459 : Blo 2283435 3425459 := bstep (se 1 (by rfl) ⟨2569094, by rfl⟩ : syracuseStep 3425459 = 5138189) B5138189
theorem B2283639 : Blo 2283435 2283639 := bstep (se 1 (by rfl) ⟨1712729, by rfl⟩ : syracuseStep 2283639 = 3425459) B3425459
theorem B2890237 : Blo 2283435 2890237 := bbase (se 3 (by rfl) ⟨541919, by rfl⟩ : syracuseStep 2890237 = 1083839) (by norm_num)
theorem B3853649 : Blo 2283435 3853649 := bstep (se 2 (by rfl) ⟨1445118, by rfl⟩ : syracuseStep 3853649 = 2890237) B2890237
theorem B2569099 : Blo 2283435 2569099 := bstep (se 1 (by rfl) ⟨1926824, by rfl⟩ : syracuseStep 2569099 = 3853649) B3853649
theorem B3425465 : Blo 2283435 3425465 := bstep (se 2 (by rfl) ⟨1284549, by rfl⟩ : syracuseStep 3425465 = 2569099) B2569099
theorem B2283643 : Blo 2283435 2283643 := bstep (se 1 (by rfl) ⟨1712732, by rfl⟩ : syracuseStep 2283643 = 3425465) B3425465
theorem B7315925 : Blo 2283435 7315925 := bbase (se 7 (by rfl) ⟨85733, by rfl⟩ : syracuseStep 7315925 = 171467) (by norm_num)
theorem B19509133 : Blo 2283435 19509133 := bstep (se 3 (by rfl) ⟨3657962, by rfl⟩ : syracuseStep 19509133 = 7315925) B7315925
theorem B26012177 : Blo 2283435 26012177 := bstep (se 2 (by rfl) ⟨9754566, by rfl⟩ : syracuseStep 26012177 = 19509133) B19509133
theorem B17341451 : Blo 2283435 17341451 := bstep (se 1 (by rfl) ⟨13006088, by rfl⟩ : syracuseStep 17341451 = 26012177) B26012177
theorem B11560967 : Blo 2283435 11560967 := bstep (se 1 (by rfl) ⟨8670725, by rfl⟩ : syracuseStep 11560967 = 17341451) B17341451
theorem B7707311 : Blo 2283435 7707311 := bstep (se 1 (by rfl) ⟨5780483, by rfl⟩ : syracuseStep 7707311 = 11560967) B11560967
theorem B5138207 : Blo 2283435 5138207 := bstep (se 1 (by rfl) ⟨3853655, by rfl⟩ : syracuseStep 5138207 = 7707311) B7707311
theorem B3425471 : Blo 2283435 3425471 := bstep (se 1 (by rfl) ⟨2569103, by rfl⟩ : syracuseStep 3425471 = 5138207) B5138207
theorem B2283647 : Blo 2283435 2283647 := bstep (se 1 (by rfl) ⟨1712735, by rfl⟩ : syracuseStep 2283647 = 3425471) B3425471
theorem B3425477 : Blo 2283435 3425477 := bbase (se 4 (by rfl) ⟨321138, by rfl⟩ : syracuseStep 3425477 = 642277) (by norm_num)
theorem B2283651 : Blo 2283435 2283651 := bstep (se 1 (by rfl) ⟨1712738, by rfl⟩ : syracuseStep 2283651 = 3425477) B3425477
theorem B3853669 : Blo 2283435 3853669 := bbase (se 4 (by rfl) ⟨361281, by rfl⟩ : syracuseStep 3853669 = 722563) (by norm_num)
theorem B5138225 : Blo 2283435 5138225 := bstep (se 2 (by rfl) ⟨1926834, by rfl⟩ : syracuseStep 5138225 = 3853669) B3853669
theorem B3425483 : Blo 2283435 3425483 := bstep (se 1 (by rfl) ⟨2569112, by rfl⟩ : syracuseStep 3425483 = 5138225) B5138225
theorem B2283655 : Blo 2283435 2283655 := bstep (se 1 (by rfl) ⟨1712741, by rfl⟩ : syracuseStep 2283655 = 3425483) B3425483
theorem B2569117 : Blo 2283435 2569117 := bbase (se 3 (by rfl) ⟨481709, by rfl⟩ : syracuseStep 2569117 = 963419) (by norm_num)
theorem B3425489 : Blo 2283435 3425489 := bstep (se 2 (by rfl) ⟨1284558, by rfl⟩ : syracuseStep 3425489 = 2569117) B2569117
theorem B2283659 : Blo 2283435 2283659 := bstep (se 1 (by rfl) ⟨1712744, by rfl⟩ : syracuseStep 2283659 = 3425489) B3425489
theorem B7707365 : Blo 2283435 7707365 := bbase (se 4 (by rfl) ⟨722565, by rfl⟩ : syracuseStep 7707365 = 1445131) (by norm_num)
theorem B5138243 : Blo 2283435 5138243 := bstep (se 1 (by rfl) ⟨3853682, by rfl⟩ : syracuseStep 5138243 = 7707365) B7707365
theorem B3425495 : Blo 2283435 3425495 := bstep (se 1 (by rfl) ⟨2569121, by rfl⟩ : syracuseStep 3425495 = 5138243) B5138243
theorem B2283663 : Blo 2283435 2283663 := bstep (se 1 (by rfl) ⟨1712747, by rfl⟩ : syracuseStep 2283663 = 3425495) B3425495
theorem B3425501 : Blo 2283435 3425501 := bbase (se 3 (by rfl) ⟨642281, by rfl⟩ : syracuseStep 3425501 = 1284563) (by norm_num)
theorem B2283667 : Blo 2283435 2283667 := bstep (se 1 (by rfl) ⟨1712750, by rfl⟩ : syracuseStep 2283667 = 3425501) B3425501
theorem B5138261 : Blo 2283435 5138261 := bbase (se 9 (by rfl) ⟨15053, by rfl⟩ : syracuseStep 5138261 = 30107) (by norm_num)
theorem B3425507 : Blo 2283435 3425507 := bstep (se 1 (by rfl) ⟨2569130, by rfl⟩ : syracuseStep 3425507 = 5138261) B5138261
theorem B2283671 : Blo 2283435 2283671 := bstep (se 1 (by rfl) ⟨1712753, by rfl⟩ : syracuseStep 2283671 = 3425507) B3425507
theorem B6503125 : Blo 2283435 6503125 := bbase (se 7 (by rfl) ⟨76208, by rfl⟩ : syracuseStep 6503125 = 152417) (by norm_num)
theorem B8670833 : Blo 2283435 8670833 := bstep (se 2 (by rfl) ⟨3251562, by rfl⟩ : syracuseStep 8670833 = 6503125) B6503125
theorem B5780555 : Blo 2283435 5780555 := bstep (se 1 (by rfl) ⟨4335416, by rfl⟩ : syracuseStep 5780555 = 8670833) B8670833
theorem B3853703 : Blo 2283435 3853703 := bstep (se 1 (by rfl) ⟨2890277, by rfl⟩ : syracuseStep 3853703 = 5780555) B5780555
theorem B2569135 : Blo 2283435 2569135 := bstep (se 1 (by rfl) ⟨1926851, by rfl⟩ : syracuseStep 2569135 = 3853703) B3853703
theorem B3425513 : Blo 2283435 3425513 := bstep (se 2 (by rfl) ⟨1284567, by rfl⟩ : syracuseStep 3425513 = 2569135) B2569135
theorem B2283675 : Blo 2283435 2283675 := bstep (se 1 (by rfl) ⟨1712756, by rfl⟩ : syracuseStep 2283675 = 3425513) B3425513
theorem B2505673 : Blo 2283435 2505673 := bbase (se 2 (by rfl) ⟨939627, by rfl⟩ : syracuseStep 2505673 = 1879255) (by norm_num)
theorem B213817429 : Blo 2283435 213817429 := bstep (se 8 (by rfl) ⟨1252836, by rfl⟩ : syracuseStep 213817429 = 2505673) B2505673
theorem B285089905 : Blo 2283435 285089905 := bstep (se 2 (by rfl) ⟨106908714, by rfl⟩ : syracuseStep 285089905 = 213817429) B213817429
theorem B380119873 : Blo 2283435 380119873 := bstep (se 2 (by rfl) ⟨142544952, by rfl⟩ : syracuseStep 380119873 = 285089905) B285089905
theorem B506826497 : Blo 2283435 506826497 := bstep (se 2 (by rfl) ⟨190059936, by rfl⟩ : syracuseStep 506826497 = 380119873) B380119873
theorem B337884331 : Blo 2283435 337884331 := bstep (se 1 (by rfl) ⟨253413248, by rfl⟩ : syracuseStep 337884331 = 506826497) B506826497
theorem B450512441 : Blo 2283435 450512441 := bstep (se 2 (by rfl) ⟨168942165, by rfl⟩ : syracuseStep 450512441 = 337884331) B337884331
theorem B300341627 : Blo 2283435 300341627 := bstep (se 1 (by rfl) ⟨225256220, by rfl⟩ : syracuseStep 300341627 = 450512441) B450512441
theorem B200227751 : Blo 2283435 200227751 := bstep (se 1 (by rfl) ⟨150170813, by rfl⟩ : syracuseStep 200227751 = 300341627) B300341627
theorem B133485167 : Blo 2283435 133485167 := bstep (se 1 (by rfl) ⟨100113875, by rfl⟩ : syracuseStep 133485167 = 200227751) B200227751
theorem B88990111 : Blo 2283435 88990111 := bstep (se 1 (by rfl) ⟨66742583, by rfl⟩ : syracuseStep 88990111 = 133485167) B133485167
theorem B118653481 : Blo 2283435 118653481 := bstep (se 2 (by rfl) ⟨44495055, by rfl⟩ : syracuseStep 118653481 = 88990111) B88990111
theorem B632818565 : Blo 2283435 632818565 := bstep (se 4 (by rfl) ⟨59326740, by rfl⟩ : syracuseStep 632818565 = 118653481) B118653481
theorem B421879043 : Blo 2283435 421879043 := bstep (se 1 (by rfl) ⟨316409282, by rfl⟩ : syracuseStep 421879043 = 632818565) B632818565
theorem B281252695 : Blo 2283435 281252695 := bstep (se 1 (by rfl) ⟨210939521, by rfl⟩ : syracuseStep 281252695 = 421879043) B421879043
theorem B375003593 : Blo 2283435 375003593 := bstep (se 2 (by rfl) ⟨140626347, by rfl⟩ : syracuseStep 375003593 = 281252695) B281252695
theorem B250002395 : Blo 2283435 250002395 := bstep (se 1 (by rfl) ⟨187501796, by rfl⟩ : syracuseStep 250002395 = 375003593) B375003593
theorem B166668263 : Blo 2283435 166668263 := bstep (se 1 (by rfl) ⟨125001197, by rfl⟩ : syracuseStep 166668263 = 250002395) B250002395
theorem B111112175 : Blo 2283435 111112175 := bstep (se 1 (by rfl) ⟨83334131, by rfl⟩ : syracuseStep 111112175 = 166668263) B166668263
theorem B74074783 : Blo 2283435 74074783 := bstep (se 1 (by rfl) ⟨55556087, by rfl⟩ : syracuseStep 74074783 = 111112175) B111112175
theorem B98766377 : Blo 2283435 98766377 := bstep (se 2 (by rfl) ⟨37037391, by rfl⟩ : syracuseStep 98766377 = 74074783) B74074783
theorem B65844251 : Blo 2283435 65844251 := bstep (se 1 (by rfl) ⟨49383188, by rfl⟩ : syracuseStep 65844251 = 98766377) B98766377
theorem B43896167 : Blo 2283435 43896167 := bstep (se 1 (by rfl) ⟨32922125, by rfl⟩ : syracuseStep 43896167 = 65844251) B65844251
theorem B29264111 : Blo 2283435 29264111 := bstep (se 1 (by rfl) ⟨21948083, by rfl⟩ : syracuseStep 29264111 = 43896167) B43896167
theorem B19509407 : Blo 2283435 19509407 := bstep (se 1 (by rfl) ⟨14632055, by rfl⟩ : syracuseStep 19509407 = 29264111) B29264111
theorem B13006271 : Blo 2283435 13006271 := bstep (se 1 (by rfl) ⟨9754703, by rfl⟩ : syracuseStep 13006271 = 19509407) B19509407
theorem B8670847 : Blo 2283435 8670847 := bstep (se 1 (by rfl) ⟨6503135, by rfl⟩ : syracuseStep 8670847 = 13006271) B13006271
theorem B11561129 : Blo 2283435 11561129 := bstep (se 2 (by rfl) ⟨4335423, by rfl⟩ : syracuseStep 11561129 = 8670847) B8670847
theorem B7707419 : Blo 2283435 7707419 := bstep (se 1 (by rfl) ⟨5780564, by rfl⟩ : syracuseStep 7707419 = 11561129) B11561129
theorem B5138279 : Blo 2283435 5138279 := bstep (se 1 (by rfl) ⟨3853709, by rfl⟩ : syracuseStep 5138279 = 7707419) B7707419
theorem B3425519 : Blo 2283435 3425519 := bstep (se 1 (by rfl) ⟨2569139, by rfl⟩ : syracuseStep 3425519 = 5138279) B5138279
theorem B2283679 : Blo 2283435 2283679 := bstep (se 1 (by rfl) ⟨1712759, by rfl⟩ : syracuseStep 2283679 = 3425519) B3425519
theorem B3425525 : Blo 2283435 3425525 := bbase (se 5 (by rfl) ⟨160571, by rfl⟩ : syracuseStep 3425525 = 321143) (by norm_num)
theorem B2283683 : Blo 2283435 2283683 := bstep (se 1 (by rfl) ⟨1712762, by rfl⟩ : syracuseStep 2283683 = 3425525) B3425525
theorem B3086461 : Blo 2283435 3086461 := bbase (se 3 (by rfl) ⟨578711, by rfl⟩ : syracuseStep 3086461 = 1157423) (by norm_num)
theorem B4115281 : Blo 2283435 4115281 := bstep (se 2 (by rfl) ⟨1543230, by rfl⟩ : syracuseStep 4115281 = 3086461) B3086461
theorem B5487041 : Blo 2283435 5487041 := bstep (se 2 (by rfl) ⟨2057640, by rfl⟩ : syracuseStep 5487041 = 4115281) B4115281
theorem B14632109 : Blo 2283435 14632109 := bstep (se 3 (by rfl) ⟨2743520, by rfl⟩ : syracuseStep 14632109 = 5487041) B5487041
theorem B9754739 : Blo 2283435 9754739 := bstep (se 1 (by rfl) ⟨7316054, by rfl⟩ : syracuseStep 9754739 = 14632109) B14632109
theorem B6503159 : Blo 2283435 6503159 := bstep (se 1 (by rfl) ⟨4877369, by rfl⟩ : syracuseStep 6503159 = 9754739) B9754739
theorem B4335439 : Blo 2283435 4335439 := bstep (se 1 (by rfl) ⟨3251579, by rfl⟩ : syracuseStep 4335439 = 6503159) B6503159
theorem B5780585 : Blo 2283435 5780585 := bstep (se 2 (by rfl) ⟨2167719, by rfl⟩ : syracuseStep 5780585 = 4335439) B4335439
theorem B3853723 : Blo 2283435 3853723 := bstep (se 1 (by rfl) ⟨2890292, by rfl⟩ : syracuseStep 3853723 = 5780585) B5780585
theorem B5138297 : Blo 2283435 5138297 := bstep (se 2 (by rfl) ⟨1926861, by rfl⟩ : syracuseStep 5138297 = 3853723) B3853723
theorem B3425531 : Blo 2283435 3425531 := bstep (se 1 (by rfl) ⟨2569148, by rfl⟩ : syracuseStep 3425531 = 5138297) B5138297
theorem B2283687 : Blo 2283435 2283687 := bstep (se 1 (by rfl) ⟨1712765, by rfl⟩ : syracuseStep 2283687 = 3425531) B3425531
theorem B2569153 : Blo 2283435 2569153 := bbase (se 2 (by rfl) ⟨963432, by rfl⟩ : syracuseStep 2569153 = 1926865) (by norm_num)
theorem B3425537 : Blo 2283435 3425537 := bstep (se 2 (by rfl) ⟨1284576, by rfl⟩ : syracuseStep 3425537 = 2569153) B2569153
theorem B2283691 : Blo 2283435 2283691 := bstep (se 1 (by rfl) ⟨1712768, by rfl⟩ : syracuseStep 2283691 = 3425537) B3425537
theorem B5780605 : Blo 2283435 5780605 := bbase (se 3 (by rfl) ⟨1083863, by rfl⟩ : syracuseStep 5780605 = 2167727) (by norm_num)
theorem B7707473 : Blo 2283435 7707473 := bstep (se 2 (by rfl) ⟨2890302, by rfl⟩ : syracuseStep 7707473 = 5780605) B5780605
theorem B5138315 : Blo 2283435 5138315 := bstep (se 1 (by rfl) ⟨3853736, by rfl⟩ : syracuseStep 5138315 = 7707473) B7707473
theorem B3425543 : Blo 2283435 3425543 := bstep (se 1 (by rfl) ⟨2569157, by rfl⟩ : syracuseStep 3425543 = 5138315) B5138315
theorem B2283695 : Blo 2283435 2283695 := bstep (se 1 (by rfl) ⟨1712771, by rfl⟩ : syracuseStep 2283695 = 3425543) B3425543
theorem B3425549 : Blo 2283435 3425549 := bbase (se 3 (by rfl) ⟨642290, by rfl⟩ : syracuseStep 3425549 = 1284581) (by norm_num)
theorem B2283699 : Blo 2283435 2283699 := bstep (se 1 (by rfl) ⟨1712774, by rfl⟩ : syracuseStep 2283699 = 3425549) B3425549
theorem B5138333 : Blo 2283435 5138333 := bbase (se 3 (by rfl) ⟨963437, by rfl⟩ : syracuseStep 5138333 = 1926875) (by norm_num)
theorem B3425555 : Blo 2283435 3425555 := bstep (se 1 (by rfl) ⟨2569166, by rfl⟩ : syracuseStep 3425555 = 5138333) B5138333
theorem B2283703 : Blo 2283435 2283703 := bstep (se 1 (by rfl) ⟨1712777, by rfl⟩ : syracuseStep 2283703 = 3425555) B3425555
theorem B3853757 : Blo 2283435 3853757 := bbase (se 3 (by rfl) ⟨722579, by rfl⟩ : syracuseStep 3853757 = 1445159) (by norm_num)
theorem B2569171 : Blo 2283435 2569171 := bstep (se 1 (by rfl) ⟨1926878, by rfl⟩ : syracuseStep 2569171 = 3853757) B3853757
theorem B3425561 : Blo 2283435 3425561 := bstep (se 2 (by rfl) ⟨1284585, by rfl⟩ : syracuseStep 3425561 = 2569171) B2569171
theorem B2283707 : Blo 2283435 2283707 := bstep (se 1 (by rfl) ⟨1712780, by rfl⟩ : syracuseStep 2283707 = 3425561) B3425561
theorem B13006453 : Blo 2283435 13006453 := bbase (se 5 (by rfl) ⟨609677, by rfl⟩ : syracuseStep 13006453 = 1219355) (by norm_num)
theorem B17341937 : Blo 2283435 17341937 := bstep (se 2 (by rfl) ⟨6503226, by rfl⟩ : syracuseStep 17341937 = 13006453) B13006453
theorem B11561291 : Blo 2283435 11561291 := bstep (se 1 (by rfl) ⟨8670968, by rfl⟩ : syracuseStep 11561291 = 17341937) B17341937
theorem B7707527 : Blo 2283435 7707527 := bstep (se 1 (by rfl) ⟨5780645, by rfl⟩ : syracuseStep 7707527 = 11561291) B11561291
theorem B5138351 : Blo 2283435 5138351 := bstep (se 1 (by rfl) ⟨3853763, by rfl⟩ : syracuseStep 5138351 = 7707527) B7707527
theorem B3425567 : Blo 2283435 3425567 := bstep (se 1 (by rfl) ⟨2569175, by rfl⟩ : syracuseStep 3425567 = 5138351) B5138351
theorem B2283711 : Blo 2283435 2283711 := bstep (se 1 (by rfl) ⟨1712783, by rfl⟩ : syracuseStep 2283711 = 3425567) B3425567
theorem B3425573 : Blo 2283435 3425573 := bbase (se 4 (by rfl) ⟨321147, by rfl⟩ : syracuseStep 3425573 = 642295) (by norm_num)
theorem B2283715 : Blo 2283435 2283715 := bstep (se 1 (by rfl) ⟨1712786, by rfl⟩ : syracuseStep 2283715 = 3425573) B3425573
theorem B2890333 : Blo 2283435 2890333 := bbase (se 3 (by rfl) ⟨541937, by rfl⟩ : syracuseStep 2890333 = 1083875) (by norm_num)
theorem B3853777 : Blo 2283435 3853777 := bstep (se 2 (by rfl) ⟨1445166, by rfl⟩ : syracuseStep 3853777 = 2890333) B2890333
theorem B5138369 : Blo 2283435 5138369 := bstep (se 2 (by rfl) ⟨1926888, by rfl⟩ : syracuseStep 5138369 = 3853777) B3853777
theorem B3425579 : Blo 2283435 3425579 := bstep (se 1 (by rfl) ⟨2569184, by rfl⟩ : syracuseStep 3425579 = 5138369) B5138369
theorem B2283719 : Blo 2283435 2283719 := bstep (se 1 (by rfl) ⟨1712789, by rfl⟩ : syracuseStep 2283719 = 3425579) B3425579
theorem B2569189 : Blo 2283435 2569189 := bbase (se 4 (by rfl) ⟨240861, by rfl⟩ : syracuseStep 2569189 = 481723) (by norm_num)
theorem B3425585 : Blo 2283435 3425585 := bstep (se 2 (by rfl) ⟨1284594, by rfl⟩ : syracuseStep 3425585 = 2569189) B2569189
theorem B2283723 : Blo 2283435 2283723 := bstep (se 1 (by rfl) ⟨1712792, by rfl⟩ : syracuseStep 2283723 = 3425585) B3425585
theorem B4629773 : Blo 2283435 4629773 := bbase (se 3 (by rfl) ⟨868082, by rfl⟩ : syracuseStep 4629773 = 1736165) (by norm_num)
theorem B3086515 : Blo 2283435 3086515 := bstep (se 1 (by rfl) ⟨2314886, by rfl⟩ : syracuseStep 3086515 = 4629773) B4629773
theorem B16461413 : Blo 2283435 16461413 := bstep (se 4 (by rfl) ⟨1543257, by rfl⟩ : syracuseStep 16461413 = 3086515) B3086515
theorem B10974275 : Blo 2283435 10974275 := bstep (se 1 (by rfl) ⟨8230706, by rfl⟩ : syracuseStep 10974275 = 16461413) B16461413
theorem B7316183 : Blo 2283435 7316183 := bstep (se 1 (by rfl) ⟨5487137, by rfl⟩ : syracuseStep 7316183 = 10974275) B10974275
theorem B4877455 : Blo 2283435 4877455 := bstep (se 1 (by rfl) ⟨3658091, by rfl⟩ : syracuseStep 4877455 = 7316183) B7316183
theorem B6503273 : Blo 2283435 6503273 := bstep (se 2 (by rfl) ⟨2438727, by rfl⟩ : syracuseStep 6503273 = 4877455) B4877455
theorem B4335515 : Blo 2283435 4335515 := bstep (se 1 (by rfl) ⟨3251636, by rfl⟩ : syracuseStep 4335515 = 6503273) B6503273
theorem B2890343 : Blo 2283435 2890343 := bstep (se 1 (by rfl) ⟨2167757, by rfl⟩ : syracuseStep 2890343 = 4335515) B4335515
theorem B7707581 : Blo 2283435 7707581 := bstep (se 3 (by rfl) ⟨1445171, by rfl⟩ : syracuseStep 7707581 = 2890343) B2890343
theorem B5138387 : Blo 2283435 5138387 := bstep (se 1 (by rfl) ⟨3853790, by rfl⟩ : syracuseStep 5138387 = 7707581) B7707581
theorem B3425591 : Blo 2283435 3425591 := bstep (se 1 (by rfl) ⟨2569193, by rfl⟩ : syracuseStep 3425591 = 5138387) B5138387
theorem B2283727 : Blo 2283435 2283727 := bstep (se 1 (by rfl) ⟨1712795, by rfl⟩ : syracuseStep 2283727 = 3425591) B3425591
theorem B3425597 : Blo 2283435 3425597 := bbase (se 3 (by rfl) ⟨642299, by rfl⟩ : syracuseStep 3425597 = 1284599) (by norm_num)
theorem B2283731 : Blo 2283435 2283731 := bstep (se 1 (by rfl) ⟨1712798, by rfl⟩ : syracuseStep 2283731 = 3425597) B3425597
theorem B5138405 : Blo 2283435 5138405 := bbase (se 4 (by rfl) ⟨481725, by rfl⟩ : syracuseStep 5138405 = 963451) (by norm_num)
theorem B3425603 : Blo 2283435 3425603 := bstep (se 1 (by rfl) ⟨2569202, by rfl⟩ : syracuseStep 3425603 = 5138405) B5138405
theorem B2283735 : Blo 2283435 2283735 := bstep (se 1 (by rfl) ⟨1712801, by rfl⟩ : syracuseStep 2283735 = 3425603) B3425603
theorem B5780717 : Blo 2283435 5780717 := bbase (se 3 (by rfl) ⟨1083884, by rfl⟩ : syracuseStep 5780717 = 2167769) (by norm_num)
theorem B3853811 : Blo 2283435 3853811 := bstep (se 1 (by rfl) ⟨2890358, by rfl⟩ : syracuseStep 3853811 = 5780717) B5780717
theorem B2569207 : Blo 2283435 2569207 := bstep (se 1 (by rfl) ⟨1926905, by rfl⟩ : syracuseStep 2569207 = 3853811) B3853811
theorem B3425609 : Blo 2283435 3425609 := bstep (se 2 (by rfl) ⟨1284603, by rfl⟩ : syracuseStep 3425609 = 2569207) B2569207
theorem B2283739 : Blo 2283435 2283739 := bstep (se 1 (by rfl) ⟨1712804, by rfl⟩ : syracuseStep 2283739 = 3425609) B3425609
theorem B3658117 : Blo 2283435 3658117 := bbase (se 4 (by rfl) ⟨342948, by rfl⟩ : syracuseStep 3658117 = 685897) (by norm_num)
theorem B4877489 : Blo 2283435 4877489 := bstep (se 2 (by rfl) ⟨1829058, by rfl⟩ : syracuseStep 4877489 = 3658117) B3658117
theorem B3251659 : Blo 2283435 3251659 := bstep (se 1 (by rfl) ⟨2438744, by rfl⟩ : syracuseStep 3251659 = 4877489) B4877489
theorem B4335545 : Blo 2283435 4335545 := bstep (se 2 (by rfl) ⟨1625829, by rfl⟩ : syracuseStep 4335545 = 3251659) B3251659
theorem B11561453 : Blo 2283435 11561453 := bstep (se 3 (by rfl) ⟨2167772, by rfl⟩ : syracuseStep 11561453 = 4335545) B4335545
theorem B7707635 : Blo 2283435 7707635 := bstep (se 1 (by rfl) ⟨5780726, by rfl⟩ : syracuseStep 7707635 = 11561453) B11561453
theorem B5138423 : Blo 2283435 5138423 := bstep (se 1 (by rfl) ⟨3853817, by rfl⟩ : syracuseStep 5138423 = 7707635) B7707635
theorem B3425615 : Blo 2283435 3425615 := bstep (se 1 (by rfl) ⟨2569211, by rfl⟩ : syracuseStep 3425615 = 5138423) B5138423
theorem B2283743 : Blo 2283435 2283743 := bstep (se 1 (by rfl) ⟨1712807, by rfl⟩ : syracuseStep 2283743 = 3425615) B3425615
theorem B3425621 : Blo 2283435 3425621 := bbase (se 12 (by rfl) ⟨1254, by rfl⟩ : syracuseStep 3425621 = 2509) (by norm_num)
theorem B2283747 : Blo 2283435 2283747 := bstep (se 1 (by rfl) ⟨1712810, by rfl⟩ : syracuseStep 2283747 = 3425621) B3425621
theorem B2438753 : Blo 2283435 2438753 := bbase (se 2 (by rfl) ⟨914532, by rfl⟩ : syracuseStep 2438753 = 1829065) (by norm_num)
theorem B6503341 : Blo 2283435 6503341 := bstep (se 3 (by rfl) ⟨1219376, by rfl⟩ : syracuseStep 6503341 = 2438753) B2438753
theorem B8671121 : Blo 2283435 8671121 := bstep (se 2 (by rfl) ⟨3251670, by rfl⟩ : syracuseStep 8671121 = 6503341) B6503341
theorem B5780747 : Blo 2283435 5780747 := bstep (se 1 (by rfl) ⟨4335560, by rfl⟩ : syracuseStep 5780747 = 8671121) B8671121
theorem B3853831 : Blo 2283435 3853831 := bstep (se 1 (by rfl) ⟨2890373, by rfl⟩ : syracuseStep 3853831 = 5780747) B5780747
theorem B5138441 : Blo 2283435 5138441 := bstep (se 2 (by rfl) ⟨1926915, by rfl⟩ : syracuseStep 5138441 = 3853831) B3853831
theorem B3425627 : Blo 2283435 3425627 := bstep (se 1 (by rfl) ⟨2569220, by rfl⟩ : syracuseStep 3425627 = 5138441) B5138441
theorem B2283751 : Blo 2283435 2283751 := bstep (se 1 (by rfl) ⟨1712813, by rfl⟩ : syracuseStep 2283751 = 3425627) B3425627
theorem B2569225 : Blo 2283435 2569225 := bbase (se 2 (by rfl) ⟨963459, by rfl⟩ : syracuseStep 2569225 = 1926919) (by norm_num)
theorem B3425633 : Blo 2283435 3425633 := bstep (se 2 (by rfl) ⟨1284612, by rfl⟩ : syracuseStep 3425633 = 2569225) B2569225
theorem B2283755 : Blo 2283435 2283755 := bstep (se 1 (by rfl) ⟨1712816, by rfl⟩ : syracuseStep 2283755 = 3425633) B3425633
theorem B21948853 : Blo 2283435 21948853 := bbase (se 5 (by rfl) ⟨1028852, by rfl⟩ : syracuseStep 21948853 = 2057705) (by norm_num)
theorem B29265137 : Blo 2283435 29265137 := bstep (se 2 (by rfl) ⟨10974426, by rfl⟩ : syracuseStep 29265137 = 21948853) B21948853
theorem B19510091 : Blo 2283435 19510091 := bstep (se 1 (by rfl) ⟨14632568, by rfl⟩ : syracuseStep 19510091 = 29265137) B29265137
theorem B13006727 : Blo 2283435 13006727 := bstep (se 1 (by rfl) ⟨9755045, by rfl⟩ : syracuseStep 13006727 = 19510091) B19510091
theorem B8671151 : Blo 2283435 8671151 := bstep (se 1 (by rfl) ⟨6503363, by rfl⟩ : syracuseStep 8671151 = 13006727) B13006727
theorem B5780767 : Blo 2283435 5780767 := bstep (se 1 (by rfl) ⟨4335575, by rfl⟩ : syracuseStep 5780767 = 8671151) B8671151
theorem B7707689 : Blo 2283435 7707689 := bstep (se 2 (by rfl) ⟨2890383, by rfl⟩ : syracuseStep 7707689 = 5780767) B5780767
theorem B5138459 : Blo 2283435 5138459 := bstep (se 1 (by rfl) ⟨3853844, by rfl⟩ : syracuseStep 5138459 = 7707689) B7707689
theorem B3425639 : Blo 2283435 3425639 := bstep (se 1 (by rfl) ⟨2569229, by rfl⟩ : syracuseStep 3425639 = 5138459) B5138459
theorem B2283759 : Blo 2283435 2283759 := bstep (se 1 (by rfl) ⟨1712819, by rfl⟩ : syracuseStep 2283759 = 3425639) B3425639
theorem B3425645 : Blo 2283435 3425645 := bbase (se 3 (by rfl) ⟨642308, by rfl⟩ : syracuseStep 3425645 = 1284617) (by norm_num)
theorem B2283763 : Blo 2283435 2283763 := bstep (se 1 (by rfl) ⟨1712822, by rfl⟩ : syracuseStep 2283763 = 3425645) B3425645
theorem B5138477 : Blo 2283435 5138477 := bbase (se 3 (by rfl) ⟨963464, by rfl⟩ : syracuseStep 5138477 = 1926929) (by norm_num)
theorem B3425651 : Blo 2283435 3425651 := bstep (se 1 (by rfl) ⟨2569238, by rfl⟩ : syracuseStep 3425651 = 5138477) B5138477
theorem B2283767 : Blo 2283435 2283767 := bstep (se 1 (by rfl) ⟨1712825, by rfl⟩ : syracuseStep 2283767 = 3425651) B3425651
theorem B3472397 : Blo 2283435 3472397 := bbase (se 3 (by rfl) ⟨651074, by rfl⟩ : syracuseStep 3472397 = 1302149) (by norm_num)
theorem B2314931 : Blo 2283435 2314931 := bstep (se 1 (by rfl) ⟨1736198, by rfl⟩ : syracuseStep 2314931 = 3472397) B3472397
theorem B24692597 : Blo 2283435 24692597 := bstep (se 5 (by rfl) ⟨1157465, by rfl⟩ : syracuseStep 24692597 = 2314931) B2314931
theorem B16461731 : Blo 2283435 16461731 := bstep (se 1 (by rfl) ⟨12346298, by rfl⟩ : syracuseStep 16461731 = 24692597) B24692597
theorem B10974487 : Blo 2283435 10974487 := bstep (se 1 (by rfl) ⟨8230865, by rfl⟩ : syracuseStep 10974487 = 16461731) B16461731
theorem B14632649 : Blo 2283435 14632649 := bstep (se 2 (by rfl) ⟨5487243, by rfl⟩ : syracuseStep 14632649 = 10974487) B10974487
theorem B9755099 : Blo 2283435 9755099 := bstep (se 1 (by rfl) ⟨7316324, by rfl⟩ : syracuseStep 9755099 = 14632649) B14632649
theorem B6503399 : Blo 2283435 6503399 := bstep (se 1 (by rfl) ⟨4877549, by rfl⟩ : syracuseStep 6503399 = 9755099) B9755099
theorem B4335599 : Blo 2283435 4335599 := bstep (se 1 (by rfl) ⟨3251699, by rfl⟩ : syracuseStep 4335599 = 6503399) B6503399
theorem B2890399 : Blo 2283435 2890399 := bstep (se 1 (by rfl) ⟨2167799, by rfl⟩ : syracuseStep 2890399 = 4335599) B4335599
theorem B3853865 : Blo 2283435 3853865 := bstep (se 2 (by rfl) ⟨1445199, by rfl⟩ : syracuseStep 3853865 = 2890399) B2890399
theorem B2569243 : Blo 2283435 2569243 := bstep (se 1 (by rfl) ⟨1926932, by rfl⟩ : syracuseStep 2569243 = 3853865) B3853865
theorem B3425657 : Blo 2283435 3425657 := bstep (se 2 (by rfl) ⟨1284621, by rfl⟩ : syracuseStep 3425657 = 2569243) B2569243
theorem B2283771 : Blo 2283435 2283771 := bstep (se 1 (by rfl) ⟨1712828, by rfl⟩ : syracuseStep 2283771 = 3425657) B3425657
theorem B10417205 : Blo 2283435 10417205 := bbase (se 5 (by rfl) ⟨488306, by rfl⟩ : syracuseStep 10417205 = 976613) (by norm_num)
theorem B27779213 : Blo 2283435 27779213 := bstep (se 3 (by rfl) ⟨5208602, by rfl⟩ : syracuseStep 27779213 = 10417205) B10417205
theorem B18519475 : Blo 2283435 18519475 := bstep (se 1 (by rfl) ⟨13889606, by rfl⟩ : syracuseStep 18519475 = 27779213) B27779213
theorem B24692633 : Blo 2283435 24692633 := bstep (se 2 (by rfl) ⟨9259737, by rfl⟩ : syracuseStep 24692633 = 18519475) B18519475
theorem B16461755 : Blo 2283435 16461755 := bstep (se 1 (by rfl) ⟨12346316, by rfl⟩ : syracuseStep 16461755 = 24692633) B24692633
theorem B10974503 : Blo 2283435 10974503 := bstep (se 1 (by rfl) ⟨8230877, by rfl⟩ : syracuseStep 10974503 = 16461755) B16461755
theorem B7316335 : Blo 2283435 7316335 := bstep (se 1 (by rfl) ⟨5487251, by rfl⟩ : syracuseStep 7316335 = 10974503) B10974503
theorem B39020453 : Blo 2283435 39020453 := bstep (se 4 (by rfl) ⟨3658167, by rfl⟩ : syracuseStep 39020453 = 7316335) B7316335
theorem B26013635 : Blo 2283435 26013635 := bstep (se 1 (by rfl) ⟨19510226, by rfl⟩ : syracuseStep 26013635 = 39020453) B39020453
theorem B17342423 : Blo 2283435 17342423 := bstep (se 1 (by rfl) ⟨13006817, by rfl⟩ : syracuseStep 17342423 = 26013635) B26013635
theorem B11561615 : Blo 2283435 11561615 := bstep (se 1 (by rfl) ⟨8671211, by rfl⟩ : syracuseStep 11561615 = 17342423) B17342423
theorem B7707743 : Blo 2283435 7707743 := bstep (se 1 (by rfl) ⟨5780807, by rfl⟩ : syracuseStep 7707743 = 11561615) B11561615
theorem B5138495 : Blo 2283435 5138495 := bstep (se 1 (by rfl) ⟨3853871, by rfl⟩ : syracuseStep 5138495 = 7707743) B7707743
theorem B3425663 : Blo 2283435 3425663 := bstep (se 1 (by rfl) ⟨2569247, by rfl⟩ : syracuseStep 3425663 = 5138495) B5138495
theorem B2283775 : Blo 2283435 2283775 := bstep (se 1 (by rfl) ⟨1712831, by rfl⟩ : syracuseStep 2283775 = 3425663) B3425663
theorem B3425669 : Blo 2283435 3425669 := bbase (se 4 (by rfl) ⟨321156, by rfl⟩ : syracuseStep 3425669 = 642313) (by norm_num)
theorem B2283779 : Blo 2283435 2283779 := bstep (se 1 (by rfl) ⟨1712834, by rfl⟩ : syracuseStep 2283779 = 3425669) B3425669
theorem B3853885 : Blo 2283435 3853885 := bbase (se 3 (by rfl) ⟨722603, by rfl⟩ : syracuseStep 3853885 = 1445207) (by norm_num)
theorem B5138513 : Blo 2283435 5138513 := bstep (se 2 (by rfl) ⟨1926942, by rfl⟩ : syracuseStep 5138513 = 3853885) B3853885
theorem B3425675 : Blo 2283435 3425675 := bstep (se 1 (by rfl) ⟨2569256, by rfl⟩ : syracuseStep 3425675 = 5138513) B5138513
theorem B2283783 : Blo 2283435 2283783 := bstep (se 1 (by rfl) ⟨1712837, by rfl⟩ : syracuseStep 2283783 = 3425675) B3425675
theorem B2569261 : Blo 2283435 2569261 := bbase (se 3 (by rfl) ⟨481736, by rfl⟩ : syracuseStep 2569261 = 963473) (by norm_num)
theorem B3425681 : Blo 2283435 3425681 := bstep (se 2 (by rfl) ⟨1284630, by rfl⟩ : syracuseStep 3425681 = 2569261) B2569261
theorem B2283787 : Blo 2283435 2283787 := bstep (se 1 (by rfl) ⟨1712840, by rfl⟩ : syracuseStep 2283787 = 3425681) B3425681
theorem B7707797 : Blo 2283435 7707797 := bbase (se 6 (by rfl) ⟨180651, by rfl⟩ : syracuseStep 7707797 = 361303) (by norm_num)
theorem B5138531 : Blo 2283435 5138531 := bstep (se 1 (by rfl) ⟨3853898, by rfl⟩ : syracuseStep 5138531 = 7707797) B7707797
theorem B3425687 : Blo 2283435 3425687 := bstep (se 1 (by rfl) ⟨2569265, by rfl⟩ : syracuseStep 3425687 = 5138531) B5138531
theorem B2283791 : Blo 2283435 2283791 := bstep (se 1 (by rfl) ⟨1712843, by rfl⟩ : syracuseStep 2283791 = 3425687) B3425687
theorem B3425693 : Blo 2283435 3425693 := bbase (se 3 (by rfl) ⟨642317, by rfl⟩ : syracuseStep 3425693 = 1284635) (by norm_num)
theorem B2283795 : Blo 2283435 2283795 := bstep (se 1 (by rfl) ⟨1712846, by rfl⟩ : syracuseStep 2283795 = 3425693) B3425693
theorem B5138549 : Blo 2283435 5138549 := bbase (se 5 (by rfl) ⟨240869, by rfl⟩ : syracuseStep 5138549 = 481739) (by norm_num)
theorem B3425699 : Blo 2283435 3425699 := bstep (se 1 (by rfl) ⟨2569274, by rfl⟩ : syracuseStep 3425699 = 5138549) B5138549
theorem B2283799 : Blo 2283435 2283799 := bstep (se 1 (by rfl) ⟨1712849, by rfl⟩ : syracuseStep 2283799 = 3425699) B3425699
theorem B3658213 : Blo 2283435 3658213 := bbase (se 4 (by rfl) ⟨342957, by rfl⟩ : syracuseStep 3658213 = 685915) (by norm_num)
theorem B19510469 : Blo 2283435 19510469 := bstep (se 4 (by rfl) ⟨1829106, by rfl⟩ : syracuseStep 19510469 = 3658213) B3658213
theorem B13006979 : Blo 2283435 13006979 := bstep (se 1 (by rfl) ⟨9755234, by rfl⟩ : syracuseStep 13006979 = 19510469) B19510469
theorem B8671319 : Blo 2283435 8671319 := bstep (se 1 (by rfl) ⟨6503489, by rfl⟩ : syracuseStep 8671319 = 13006979) B13006979
theorem B5780879 : Blo 2283435 5780879 := bstep (se 1 (by rfl) ⟨4335659, by rfl⟩ : syracuseStep 5780879 = 8671319) B8671319
theorem B3853919 : Blo 2283435 3853919 := bstep (se 1 (by rfl) ⟨2890439, by rfl⟩ : syracuseStep 3853919 = 5780879) B5780879
theorem B2569279 : Blo 2283435 2569279 := bstep (se 1 (by rfl) ⟨1926959, by rfl⟩ : syracuseStep 2569279 = 3853919) B3853919
theorem B3425705 : Blo 2283435 3425705 := bstep (se 2 (by rfl) ⟨1284639, by rfl⟩ : syracuseStep 3425705 = 2569279) B2569279
theorem B2283803 : Blo 2283435 2283803 := bstep (se 1 (by rfl) ⟨1712852, by rfl⟩ : syracuseStep 2283803 = 3425705) B3425705
theorem B8671333 : Blo 2283435 8671333 := bbase (se 4 (by rfl) ⟨812937, by rfl⟩ : syracuseStep 8671333 = 1625875) (by norm_num)
theorem B11561777 : Blo 2283435 11561777 := bstep (se 2 (by rfl) ⟨4335666, by rfl⟩ : syracuseStep 11561777 = 8671333) B8671333
theorem B7707851 : Blo 2283435 7707851 := bstep (se 1 (by rfl) ⟨5780888, by rfl⟩ : syracuseStep 7707851 = 11561777) B11561777
theorem B5138567 : Blo 2283435 5138567 := bstep (se 1 (by rfl) ⟨3853925, by rfl⟩ : syracuseStep 5138567 = 7707851) B7707851
theorem B3425711 : Blo 2283435 3425711 := bstep (se 1 (by rfl) ⟨2569283, by rfl⟩ : syracuseStep 3425711 = 5138567) B5138567
theorem B2283807 : Blo 2283435 2283807 := bstep (se 1 (by rfl) ⟨1712855, by rfl⟩ : syracuseStep 2283807 = 3425711) B3425711
theorem B3425717 : Blo 2283435 3425717 := bbase (se 5 (by rfl) ⟨160580, by rfl⟩ : syracuseStep 3425717 = 321161) (by norm_num)
theorem B2283811 : Blo 2283435 2283811 := bstep (se 1 (by rfl) ⟨1712858, by rfl⟩ : syracuseStep 2283811 = 3425717) B3425717
theorem B5780909 : Blo 2283435 5780909 := bbase (se 3 (by rfl) ⟨1083920, by rfl⟩ : syracuseStep 5780909 = 2167841) (by norm_num)
theorem B3853939 : Blo 2283435 3853939 := bstep (se 1 (by rfl) ⟨2890454, by rfl⟩ : syracuseStep 3853939 = 5780909) B5780909
theorem B5138585 : Blo 2283435 5138585 := bstep (se 2 (by rfl) ⟨1926969, by rfl⟩ : syracuseStep 5138585 = 3853939) B3853939
theorem B3425723 : Blo 2283435 3425723 := bstep (se 1 (by rfl) ⟨2569292, by rfl⟩ : syracuseStep 3425723 = 5138585) B5138585
theorem B2283815 : Blo 2283435 2283815 := bstep (se 1 (by rfl) ⟨1712861, by rfl⟩ : syracuseStep 2283815 = 3425723) B3425723
theorem B2569297 : Blo 2283435 2569297 := bbase (se 2 (by rfl) ⟨963486, by rfl⟩ : syracuseStep 2569297 = 1926973) (by norm_num)
theorem B3425729 : Blo 2283435 3425729 := bstep (se 2 (by rfl) ⟨1284648, by rfl⟩ : syracuseStep 3425729 = 2569297) B2569297
theorem B2283819 : Blo 2283435 2283819 := bstep (se 1 (by rfl) ⟨1712864, by rfl⟩ : syracuseStep 2283819 = 3425729) B3425729
theorem B3251773 : Blo 2283435 3251773 := bbase (se 3 (by rfl) ⟨609707, by rfl⟩ : syracuseStep 3251773 = 1219415) (by norm_num)
theorem B4335697 : Blo 2283435 4335697 := bstep (se 2 (by rfl) ⟨1625886, by rfl⟩ : syracuseStep 4335697 = 3251773) B3251773
theorem B5780929 : Blo 2283435 5780929 := bstep (se 2 (by rfl) ⟨2167848, by rfl⟩ : syracuseStep 5780929 = 4335697) B4335697
theorem B7707905 : Blo 2283435 7707905 := bstep (se 2 (by rfl) ⟨2890464, by rfl⟩ : syracuseStep 7707905 = 5780929) B5780929
theorem B5138603 : Blo 2283435 5138603 := bstep (se 1 (by rfl) ⟨3853952, by rfl⟩ : syracuseStep 5138603 = 7707905) B7707905
theorem B3425735 : Blo 2283435 3425735 := bstep (se 1 (by rfl) ⟨2569301, by rfl⟩ : syracuseStep 3425735 = 5138603) B5138603
theorem B2283823 : Blo 2283435 2283823 := bstep (se 1 (by rfl) ⟨1712867, by rfl⟩ : syracuseStep 2283823 = 3425735) B3425735
theorem B3425741 : Blo 2283435 3425741 := bbase (se 3 (by rfl) ⟨642326, by rfl⟩ : syracuseStep 3425741 = 1284653) (by norm_num)
theorem B2283827 : Blo 2283435 2283827 := bstep (se 1 (by rfl) ⟨1712870, by rfl⟩ : syracuseStep 2283827 = 3425741) B3425741
theorem B5138621 : Blo 2283435 5138621 := bbase (se 3 (by rfl) ⟨963491, by rfl⟩ : syracuseStep 5138621 = 1926983) (by norm_num)
theorem B3425747 : Blo 2283435 3425747 := bstep (se 1 (by rfl) ⟨2569310, by rfl⟩ : syracuseStep 3425747 = 5138621) B5138621
theorem B2283831 : Blo 2283435 2283831 := bstep (se 1 (by rfl) ⟨1712873, by rfl⟩ : syracuseStep 2283831 = 3425747) B3425747
theorem B3853973 : Blo 2283435 3853973 := bbase (se 6 (by rfl) ⟨90327, by rfl⟩ : syracuseStep 3853973 = 180655) (by norm_num)
theorem B2569315 : Blo 2283435 2569315 := bstep (se 1 (by rfl) ⟨1926986, by rfl⟩ : syracuseStep 2569315 = 3853973) B3853973
theorem B3425753 : Blo 2283435 3425753 := bstep (se 2 (by rfl) ⟨1284657, by rfl⟩ : syracuseStep 3425753 = 2569315) B2569315
theorem B2283835 : Blo 2283435 2283835 := bstep (se 1 (by rfl) ⟨1712876, by rfl⟩ : syracuseStep 2283835 = 3425753) B3425753
theorem B11719685 : Blo 2283435 11719685 := bbase (se 4 (by rfl) ⟨1098720, by rfl⟩ : syracuseStep 11719685 = 2197441) (by norm_num)
theorem B31252493 : Blo 2283435 31252493 := bstep (se 3 (by rfl) ⟨5859842, by rfl⟩ : syracuseStep 31252493 = 11719685) B11719685
theorem B20834995 : Blo 2283435 20834995 := bstep (se 1 (by rfl) ⟨15626246, by rfl⟩ : syracuseStep 20834995 = 31252493) B31252493
theorem B27779993 : Blo 2283435 27779993 := bstep (se 2 (by rfl) ⟨10417497, by rfl⟩ : syracuseStep 27779993 = 20834995) B20834995
theorem B18519995 : Blo 2283435 18519995 := bstep (se 1 (by rfl) ⟨13889996, by rfl⟩ : syracuseStep 18519995 = 27779993) B27779993
theorem B12346663 : Blo 2283435 12346663 := bstep (se 1 (by rfl) ⟨9259997, by rfl⟩ : syracuseStep 12346663 = 18519995) B18519995
theorem B16462217 : Blo 2283435 16462217 := bstep (se 2 (by rfl) ⟨6173331, by rfl⟩ : syracuseStep 16462217 = 12346663) B12346663
theorem B10974811 : Blo 2283435 10974811 := bstep (se 1 (by rfl) ⟨8231108, by rfl⟩ : syracuseStep 10974811 = 16462217) B16462217
theorem B14633081 : Blo 2283435 14633081 := bstep (se 2 (by rfl) ⟨5487405, by rfl⟩ : syracuseStep 14633081 = 10974811) B10974811
theorem B9755387 : Blo 2283435 9755387 := bstep (se 1 (by rfl) ⟨7316540, by rfl⟩ : syracuseStep 9755387 = 14633081) B14633081
theorem B6503591 : Blo 2283435 6503591 := bstep (se 1 (by rfl) ⟨4877693, by rfl⟩ : syracuseStep 6503591 = 9755387) B9755387
theorem B17342909 : Blo 2283435 17342909 := bstep (se 3 (by rfl) ⟨3251795, by rfl⟩ : syracuseStep 17342909 = 6503591) B6503591
theorem B11561939 : Blo 2283435 11561939 := bstep (se 1 (by rfl) ⟨8671454, by rfl⟩ : syracuseStep 11561939 = 17342909) B17342909
theorem B7707959 : Blo 2283435 7707959 := bstep (se 1 (by rfl) ⟨5780969, by rfl⟩ : syracuseStep 7707959 = 11561939) B11561939
theorem B5138639 : Blo 2283435 5138639 := bstep (se 1 (by rfl) ⟨3853979, by rfl⟩ : syracuseStep 5138639 = 7707959) B7707959
theorem B3425759 : Blo 2283435 3425759 := bstep (se 1 (by rfl) ⟨2569319, by rfl⟩ : syracuseStep 3425759 = 5138639) B5138639
theorem B2283839 : Blo 2283435 2283839 := bstep (se 1 (by rfl) ⟨1712879, by rfl⟩ : syracuseStep 2283839 = 3425759) B3425759
theorem B3425765 : Blo 2283435 3425765 := bbase (se 4 (by rfl) ⟨321165, by rfl⟩ : syracuseStep 3425765 = 642331) (by norm_num)
theorem B2283843 : Blo 2283435 2283843 := bstep (se 1 (by rfl) ⟨1712882, by rfl⟩ : syracuseStep 2283843 = 3425765) B3425765
theorem B5638181 : Blo 2283435 5638181 := bbase (se 4 (by rfl) ⟨528579, by rfl⟩ : syracuseStep 5638181 = 1057159) (by norm_num)
theorem B15035149 : Blo 2283435 15035149 := bstep (se 3 (by rfl) ⟨2819090, by rfl⟩ : syracuseStep 15035149 = 5638181) B5638181
theorem B80187461 : Blo 2283435 80187461 := bstep (se 4 (by rfl) ⟨7517574, by rfl⟩ : syracuseStep 80187461 = 15035149) B15035149
theorem B53458307 : Blo 2283435 53458307 := bstep (se 1 (by rfl) ⟨40093730, by rfl⟩ : syracuseStep 53458307 = 80187461) B80187461
theorem B35638871 : Blo 2283435 35638871 := bstep (se 1 (by rfl) ⟨26729153, by rfl⟩ : syracuseStep 35638871 = 53458307) B53458307
theorem B95036989 : Blo 2283435 95036989 := bstep (se 3 (by rfl) ⟨17819435, by rfl⟩ : syracuseStep 95036989 = 35638871) B35638871
theorem B126715985 : Blo 2283435 126715985 := bstep (se 2 (by rfl) ⟨47518494, by rfl⟩ : syracuseStep 126715985 = 95036989) B95036989
theorem B84477323 : Blo 2283435 84477323 := bstep (se 1 (by rfl) ⟨63357992, by rfl⟩ : syracuseStep 84477323 = 126715985) B126715985
theorem B56318215 : Blo 2283435 56318215 := bstep (se 1 (by rfl) ⟨42238661, by rfl⟩ : syracuseStep 56318215 = 84477323) B84477323
theorem B75090953 : Blo 2283435 75090953 := bstep (se 2 (by rfl) ⟨28159107, by rfl⟩ : syracuseStep 75090953 = 56318215) B56318215
theorem B50060635 : Blo 2283435 50060635 := bstep (se 1 (by rfl) ⟨37545476, by rfl⟩ : syracuseStep 50060635 = 75090953) B75090953
theorem B266990053 : Blo 2283435 266990053 := bstep (se 4 (by rfl) ⟨25030317, by rfl⟩ : syracuseStep 266990053 = 50060635) B50060635
theorem B355986737 : Blo 2283435 355986737 := bstep (se 2 (by rfl) ⟨133495026, by rfl⟩ : syracuseStep 355986737 = 266990053) B266990053
theorem B237324491 : Blo 2283435 237324491 := bstep (se 1 (by rfl) ⟨177993368, by rfl⟩ : syracuseStep 237324491 = 355986737) B355986737
theorem B158216327 : Blo 2283435 158216327 := bstep (se 1 (by rfl) ⟨118662245, by rfl⟩ : syracuseStep 158216327 = 237324491) B237324491
theorem B105477551 : Blo 2283435 105477551 := bstep (se 1 (by rfl) ⟨79108163, by rfl⟩ : syracuseStep 105477551 = 158216327) B158216327
theorem B70318367 : Blo 2283435 70318367 := bstep (se 1 (by rfl) ⟨52738775, by rfl⟩ : syracuseStep 70318367 = 105477551) B105477551
theorem B46878911 : Blo 2283435 46878911 := bstep (se 1 (by rfl) ⟨35159183, by rfl⟩ : syracuseStep 46878911 = 70318367) B70318367
theorem B31252607 : Blo 2283435 31252607 := bstep (se 1 (by rfl) ⟨23439455, by rfl⟩ : syracuseStep 31252607 = 46878911) B46878911
theorem B20835071 : Blo 2283435 20835071 := bstep (se 1 (by rfl) ⟨15626303, by rfl⟩ : syracuseStep 20835071 = 31252607) B31252607
theorem B13890047 : Blo 2283435 13890047 := bstep (se 1 (by rfl) ⟨10417535, by rfl⟩ : syracuseStep 13890047 = 20835071) B20835071
theorem B37040125 : Blo 2283435 37040125 := bstep (se 3 (by rfl) ⟨6945023, by rfl⟩ : syracuseStep 37040125 = 13890047) B13890047
theorem B49386833 : Blo 2283435 49386833 := bstep (se 2 (by rfl) ⟨18520062, by rfl⟩ : syracuseStep 49386833 = 37040125) B37040125
theorem B32924555 : Blo 2283435 32924555 := bstep (se 1 (by rfl) ⟨24693416, by rfl⟩ : syracuseStep 32924555 = 49386833) B49386833
theorem B21949703 : Blo 2283435 21949703 := bstep (se 1 (by rfl) ⟨16462277, by rfl⟩ : syracuseStep 21949703 = 32924555) B32924555
theorem B14633135 : Blo 2283435 14633135 := bstep (se 1 (by rfl) ⟨10974851, by rfl⟩ : syracuseStep 14633135 = 21949703) B21949703
theorem B9755423 : Blo 2283435 9755423 := bstep (se 1 (by rfl) ⟨7316567, by rfl⟩ : syracuseStep 9755423 = 14633135) B14633135
theorem B6503615 : Blo 2283435 6503615 := bstep (se 1 (by rfl) ⟨4877711, by rfl⟩ : syracuseStep 6503615 = 9755423) B9755423
theorem B4335743 : Blo 2283435 4335743 := bstep (se 1 (by rfl) ⟨3251807, by rfl⟩ : syracuseStep 4335743 = 6503615) B6503615
theorem B2890495 : Blo 2283435 2890495 := bstep (se 1 (by rfl) ⟨2167871, by rfl⟩ : syracuseStep 2890495 = 4335743) B4335743
theorem B3853993 : Blo 2283435 3853993 := bstep (se 2 (by rfl) ⟨1445247, by rfl⟩ : syracuseStep 3853993 = 2890495) B2890495
theorem B5138657 : Blo 2283435 5138657 := bstep (se 2 (by rfl) ⟨1926996, by rfl⟩ : syracuseStep 5138657 = 3853993) B3853993
theorem B3425771 : Blo 2283435 3425771 := bstep (se 1 (by rfl) ⟨2569328, by rfl⟩ : syracuseStep 3425771 = 5138657) B5138657
theorem B2283847 : Blo 2283435 2283847 := bstep (se 1 (by rfl) ⟨1712885, by rfl⟩ : syracuseStep 2283847 = 3425771) B3425771
theorem B2569333 : Blo 2283435 2569333 := bbase (se 5 (by rfl) ⟨120437, by rfl⟩ : syracuseStep 2569333 = 240875) (by norm_num)
theorem B3425777 : Blo 2283435 3425777 := bstep (se 2 (by rfl) ⟨1284666, by rfl⟩ : syracuseStep 3425777 = 2569333) B2569333
theorem B2283851 : Blo 2283435 2283851 := bstep (se 1 (by rfl) ⟨1712888, by rfl⟩ : syracuseStep 2283851 = 3425777) B3425777
theorem B2890505 : Blo 2283435 2890505 := bbase (se 2 (by rfl) ⟨1083939, by rfl⟩ : syracuseStep 2890505 = 2167879) (by norm_num)
theorem B7708013 : Blo 2283435 7708013 := bstep (se 3 (by rfl) ⟨1445252, by rfl⟩ : syracuseStep 7708013 = 2890505) B2890505
theorem B5138675 : Blo 2283435 5138675 := bstep (se 1 (by rfl) ⟨3854006, by rfl⟩ : syracuseStep 5138675 = 7708013) B7708013
theorem B3425783 : Blo 2283435 3425783 := bstep (se 1 (by rfl) ⟨2569337, by rfl⟩ : syracuseStep 3425783 = 5138675) B5138675
theorem B2283855 : Blo 2283435 2283855 := bstep (se 1 (by rfl) ⟨1712891, by rfl⟩ : syracuseStep 2283855 = 3425783) B3425783
theorem B3425789 : Blo 2283435 3425789 := bbase (se 3 (by rfl) ⟨642335, by rfl⟩ : syracuseStep 3425789 = 1284671) (by norm_num)
theorem B2283859 : Blo 2283435 2283859 := bstep (se 1 (by rfl) ⟨1712894, by rfl⟩ : syracuseStep 2283859 = 3425789) B3425789
theorem B5138693 : Blo 2283435 5138693 := bbase (se 4 (by rfl) ⟨481752, by rfl⟩ : syracuseStep 5138693 = 963505) (by norm_num)
theorem B3425795 : Blo 2283435 3425795 := bstep (se 1 (by rfl) ⟨2569346, by rfl⟩ : syracuseStep 3425795 = 5138693) B5138693
theorem B2283863 : Blo 2283435 2283863 := bstep (se 1 (by rfl) ⟨1712897, by rfl⟩ : syracuseStep 2283863 = 3425795) B3425795
theorem B4335781 : Blo 2283435 4335781 := bbase (se 4 (by rfl) ⟨406479, by rfl⟩ : syracuseStep 4335781 = 812959) (by norm_num)
theorem B5781041 : Blo 2283435 5781041 := bstep (se 2 (by rfl) ⟨2167890, by rfl⟩ : syracuseStep 5781041 = 4335781) B4335781
theorem B3854027 : Blo 2283435 3854027 := bstep (se 1 (by rfl) ⟨2890520, by rfl⟩ : syracuseStep 3854027 = 5781041) B5781041
theorem B2569351 : Blo 2283435 2569351 := bstep (se 1 (by rfl) ⟨1927013, by rfl⟩ : syracuseStep 2569351 = 3854027) B3854027
theorem B3425801 : Blo 2283435 3425801 := bstep (se 2 (by rfl) ⟨1284675, by rfl⟩ : syracuseStep 3425801 = 2569351) B2569351
theorem B2283867 : Blo 2283435 2283867 := bstep (se 1 (by rfl) ⟨1712900, by rfl⟩ : syracuseStep 2283867 = 3425801) B3425801
theorem B11562101 : Blo 2283435 11562101 := bbase (se 5 (by rfl) ⟨541973, by rfl⟩ : syracuseStep 11562101 = 1083947) (by norm_num)
theorem B7708067 : Blo 2283435 7708067 := bstep (se 1 (by rfl) ⟨5781050, by rfl⟩ : syracuseStep 7708067 = 11562101) B11562101
theorem B5138711 : Blo 2283435 5138711 := bstep (se 1 (by rfl) ⟨3854033, by rfl⟩ : syracuseStep 5138711 = 7708067) B7708067
theorem B3425807 : Blo 2283435 3425807 := bstep (se 1 (by rfl) ⟨2569355, by rfl⟩ : syracuseStep 3425807 = 5138711) B5138711
theorem B2283871 : Blo 2283435 2283871 := bstep (se 1 (by rfl) ⟨1712903, by rfl⟩ : syracuseStep 2283871 = 3425807) B3425807
theorem B3425813 : Blo 2283435 3425813 := bbase (se 6 (by rfl) ⟨80292, by rfl⟩ : syracuseStep 3425813 = 160585) (by norm_num)
theorem B2283875 : Blo 2283435 2283875 := bstep (se 1 (by rfl) ⟨1712906, by rfl⟩ : syracuseStep 2283875 = 3425813) B3425813
theorem B2604421 : Blo 2283435 2604421 := bbase (se 4 (by rfl) ⟨244164, by rfl⟩ : syracuseStep 2604421 = 488329) (by norm_num)
theorem B3472561 : Blo 2283435 3472561 := bstep (se 2 (by rfl) ⟨1302210, by rfl⟩ : syracuseStep 3472561 = 2604421) B2604421
theorem B4630081 : Blo 2283435 4630081 := bstep (se 2 (by rfl) ⟨1736280, by rfl⟩ : syracuseStep 4630081 = 3472561) B3472561
theorem B6173441 : Blo 2283435 6173441 := bstep (se 2 (by rfl) ⟨2315040, by rfl⟩ : syracuseStep 6173441 = 4630081) B4630081
theorem B4115627 : Blo 2283435 4115627 := bstep (se 1 (by rfl) ⟨3086720, by rfl⟩ : syracuseStep 4115627 = 6173441) B6173441
theorem B2743751 : Blo 2283435 2743751 := bstep (se 1 (by rfl) ⟨2057813, by rfl⟩ : syracuseStep 2743751 = 4115627) B4115627
theorem B7316669 : Blo 2283435 7316669 := bstep (se 3 (by rfl) ⟨1371875, by rfl⟩ : syracuseStep 7316669 = 2743751) B2743751
theorem B19511117 : Blo 2283435 19511117 := bstep (se 3 (by rfl) ⟨3658334, by rfl⟩ : syracuseStep 19511117 = 7316669) B7316669
theorem B13007411 : Blo 2283435 13007411 := bstep (se 1 (by rfl) ⟨9755558, by rfl⟩ : syracuseStep 13007411 = 19511117) B19511117
theorem B8671607 : Blo 2283435 8671607 := bstep (se 1 (by rfl) ⟨6503705, by rfl⟩ : syracuseStep 8671607 = 13007411) B13007411
theorem B5781071 : Blo 2283435 5781071 := bstep (se 1 (by rfl) ⟨4335803, by rfl⟩ : syracuseStep 5781071 = 8671607) B8671607
theorem B3854047 : Blo 2283435 3854047 := bstep (se 1 (by rfl) ⟨2890535, by rfl⟩ : syracuseStep 3854047 = 5781071) B5781071
theorem B5138729 : Blo 2283435 5138729 := bstep (se 2 (by rfl) ⟨1927023, by rfl⟩ : syracuseStep 5138729 = 3854047) B3854047
theorem B3425819 : Blo 2283435 3425819 := bstep (se 1 (by rfl) ⟨2569364, by rfl⟩ : syracuseStep 3425819 = 5138729) B5138729
theorem B2283879 : Blo 2283435 2283879 := bstep (se 1 (by rfl) ⟨1712909, by rfl⟩ : syracuseStep 2283879 = 3425819) B3425819
theorem B2569369 : Blo 2283435 2569369 := bbase (se 2 (by rfl) ⟨963513, by rfl⟩ : syracuseStep 2569369 = 1927027) (by norm_num)
theorem B3425825 : Blo 2283435 3425825 := bstep (se 2 (by rfl) ⟨1284684, by rfl⟩ : syracuseStep 3425825 = 2569369) B2569369
theorem B2283883 : Blo 2283435 2283883 := bstep (se 1 (by rfl) ⟨1712912, by rfl⟩ : syracuseStep 2283883 = 3425825) B3425825
theorem B8671637 : Blo 2283435 8671637 := bbase (se 6 (by rfl) ⟨203241, by rfl⟩ : syracuseStep 8671637 = 406483) (by norm_num)
theorem B5781091 : Blo 2283435 5781091 := bstep (se 1 (by rfl) ⟨4335818, by rfl⟩ : syracuseStep 5781091 = 8671637) B8671637
theorem B7708121 : Blo 2283435 7708121 := bstep (se 2 (by rfl) ⟨2890545, by rfl⟩ : syracuseStep 7708121 = 5781091) B5781091
theorem B5138747 : Blo 2283435 5138747 := bstep (se 1 (by rfl) ⟨3854060, by rfl⟩ : syracuseStep 5138747 = 7708121) B7708121
theorem B3425831 : Blo 2283435 3425831 := bstep (se 1 (by rfl) ⟨2569373, by rfl⟩ : syracuseStep 3425831 = 5138747) B5138747
theorem B2283887 : Blo 2283435 2283887 := bstep (se 1 (by rfl) ⟨1712915, by rfl⟩ : syracuseStep 2283887 = 3425831) B3425831
theorem B3425837 : Blo 2283435 3425837 := bbase (se 3 (by rfl) ⟨642344, by rfl⟩ : syracuseStep 3425837 = 1284689) (by norm_num)
theorem B2283891 : Blo 2283435 2283891 := bstep (se 1 (by rfl) ⟨1712918, by rfl⟩ : syracuseStep 2283891 = 3425837) B3425837
theorem B5138765 : Blo 2283435 5138765 := bbase (se 3 (by rfl) ⟨963518, by rfl⟩ : syracuseStep 5138765 = 1927037) (by norm_num)
theorem B3425843 : Blo 2283435 3425843 := bstep (se 1 (by rfl) ⟨2569382, by rfl⟩ : syracuseStep 3425843 = 5138765) B5138765
theorem B2283895 : Blo 2283435 2283895 := bstep (se 1 (by rfl) ⟨1712921, by rfl⟩ : syracuseStep 2283895 = 3425843) B3425843
theorem B2890561 : Blo 2283435 2890561 := bbase (se 2 (by rfl) ⟨1083960, by rfl⟩ : syracuseStep 2890561 = 2167921) (by norm_num)
theorem B3854081 : Blo 2283435 3854081 := bstep (se 2 (by rfl) ⟨1445280, by rfl⟩ : syracuseStep 3854081 = 2890561) B2890561
theorem B2569387 : Blo 2283435 2569387 := bstep (se 1 (by rfl) ⟨1927040, by rfl⟩ : syracuseStep 2569387 = 3854081) B3854081
theorem B3425849 : Blo 2283435 3425849 := bstep (se 2 (by rfl) ⟨1284693, by rfl⟩ : syracuseStep 3425849 = 2569387) B2569387
theorem B2283899 : Blo 2283435 2283899 := bstep (se 1 (by rfl) ⟨1712924, by rfl⟩ : syracuseStep 2283899 = 3425849) B3425849
theorem B3658373 : Blo 2283435 3658373 := bbase (se 4 (by rfl) ⟨342972, by rfl⟩ : syracuseStep 3658373 = 685945) (by norm_num)
theorem B2438915 : Blo 2283435 2438915 := bstep (se 1 (by rfl) ⟨1829186, by rfl⟩ : syracuseStep 2438915 = 3658373) B3658373
theorem B26015093 : Blo 2283435 26015093 := bstep (se 5 (by rfl) ⟨1219457, by rfl⟩ : syracuseStep 26015093 = 2438915) B2438915
theorem B17343395 : Blo 2283435 17343395 := bstep (se 1 (by rfl) ⟨13007546, by rfl⟩ : syracuseStep 17343395 = 26015093) B26015093
theorem B11562263 : Blo 2283435 11562263 := bstep (se 1 (by rfl) ⟨8671697, by rfl⟩ : syracuseStep 11562263 = 17343395) B17343395
theorem B7708175 : Blo 2283435 7708175 := bstep (se 1 (by rfl) ⟨5781131, by rfl⟩ : syracuseStep 7708175 = 11562263) B11562263
theorem B5138783 : Blo 2283435 5138783 := bstep (se 1 (by rfl) ⟨3854087, by rfl⟩ : syracuseStep 5138783 = 7708175) B7708175
theorem B3425855 : Blo 2283435 3425855 := bstep (se 1 (by rfl) ⟨2569391, by rfl⟩ : syracuseStep 3425855 = 5138783) B5138783
theorem B2283903 : Blo 2283435 2283903 := bstep (se 1 (by rfl) ⟨1712927, by rfl⟩ : syracuseStep 2283903 = 3425855) B3425855
theorem B3425861 : Blo 2283435 3425861 := bbase (se 4 (by rfl) ⟨321174, by rfl⟩ : syracuseStep 3425861 = 642349) (by norm_num)
theorem B2283907 : Blo 2283435 2283907 := bstep (se 1 (by rfl) ⟨1712930, by rfl⟩ : syracuseStep 2283907 = 3425861) B3425861
theorem B3854101 : Blo 2283435 3854101 := bbase (se 6 (by rfl) ⟨90330, by rfl⟩ : syracuseStep 3854101 = 180661) (by norm_num)
theorem B5138801 : Blo 2283435 5138801 := bstep (se 2 (by rfl) ⟨1927050, by rfl⟩ : syracuseStep 5138801 = 3854101) B3854101
theorem B3425867 : Blo 2283435 3425867 := bstep (se 1 (by rfl) ⟨2569400, by rfl⟩ : syracuseStep 3425867 = 5138801) B5138801
theorem B2283911 : Blo 2283435 2283911 := bstep (se 1 (by rfl) ⟨1712933, by rfl⟩ : syracuseStep 2283911 = 3425867) B3425867
theorem B2569405 : Blo 2283435 2569405 := bbase (se 3 (by rfl) ⟨481763, by rfl⟩ : syracuseStep 2569405 = 963527) (by norm_num)
theorem B3425873 : Blo 2283435 3425873 := bstep (se 2 (by rfl) ⟨1284702, by rfl⟩ : syracuseStep 3425873 = 2569405) B2569405
theorem B2283915 : Blo 2283435 2283915 := bstep (se 1 (by rfl) ⟨1712936, by rfl⟩ : syracuseStep 2283915 = 3425873) B3425873
theorem B7708229 : Blo 2283435 7708229 := bbase (se 4 (by rfl) ⟨722646, by rfl⟩ : syracuseStep 7708229 = 1445293) (by norm_num)
theorem B5138819 : Blo 2283435 5138819 := bstep (se 1 (by rfl) ⟨3854114, by rfl⟩ : syracuseStep 5138819 = 7708229) B7708229
theorem B3425879 : Blo 2283435 3425879 := bstep (se 1 (by rfl) ⟨2569409, by rfl⟩ : syracuseStep 3425879 = 5138819) B5138819
theorem B2283919 : Blo 2283435 2283919 := bstep (se 1 (by rfl) ⟨1712939, by rfl⟩ : syracuseStep 2283919 = 3425879) B3425879
theorem B3425885 : Blo 2283435 3425885 := bbase (se 3 (by rfl) ⟨642353, by rfl⟩ : syracuseStep 3425885 = 1284707) (by norm_num)
theorem B2283923 : Blo 2283435 2283923 := bstep (se 1 (by rfl) ⟨1712942, by rfl⟩ : syracuseStep 2283923 = 3425885) B3425885
theorem B5138837 : Blo 2283435 5138837 := bbase (se 6 (by rfl) ⟨120441, by rfl⟩ : syracuseStep 5138837 = 240883) (by norm_num)
theorem B3425891 : Blo 2283435 3425891 := bstep (se 1 (by rfl) ⟨2569418, by rfl⟩ : syracuseStep 3425891 = 5138837) B5138837
theorem B2283927 : Blo 2283435 2283927 := bstep (se 1 (by rfl) ⟨1712945, by rfl⟩ : syracuseStep 2283927 = 3425891) B3425891
theorem B7316837 : Blo 2283435 7316837 := bbase (se 4 (by rfl) ⟨685953, by rfl⟩ : syracuseStep 7316837 = 1371907) (by norm_num)
theorem B4877891 : Blo 2283435 4877891 := bstep (se 1 (by rfl) ⟨3658418, by rfl⟩ : syracuseStep 4877891 = 7316837) B7316837
theorem B3251927 : Blo 2283435 3251927 := bstep (se 1 (by rfl) ⟨2438945, by rfl⟩ : syracuseStep 3251927 = 4877891) B4877891
theorem B8671805 : Blo 2283435 8671805 := bstep (se 3 (by rfl) ⟨1625963, by rfl⟩ : syracuseStep 8671805 = 3251927) B3251927
theorem B5781203 : Blo 2283435 5781203 := bstep (se 1 (by rfl) ⟨4335902, by rfl⟩ : syracuseStep 5781203 = 8671805) B8671805
theorem B3854135 : Blo 2283435 3854135 := bstep (se 1 (by rfl) ⟨2890601, by rfl⟩ : syracuseStep 3854135 = 5781203) B5781203
theorem B2569423 : Blo 2283435 2569423 := bstep (se 1 (by rfl) ⟨1927067, by rfl⟩ : syracuseStep 2569423 = 3854135) B3854135
theorem B3425897 : Blo 2283435 3425897 := bstep (se 2 (by rfl) ⟨1284711, by rfl⟩ : syracuseStep 3425897 = 2569423) B2569423
theorem B2283931 : Blo 2283435 2283931 := bstep (se 1 (by rfl) ⟨1712948, by rfl⟩ : syracuseStep 2283931 = 3425897) B3425897
theorem B9755797 : Blo 2283435 9755797 := bbase (se 6 (by rfl) ⟨228651, by rfl⟩ : syracuseStep 9755797 = 457303) (by norm_num)
theorem B13007729 : Blo 2283435 13007729 := bstep (se 2 (by rfl) ⟨4877898, by rfl⟩ : syracuseStep 13007729 = 9755797) B9755797
theorem B8671819 : Blo 2283435 8671819 := bstep (se 1 (by rfl) ⟨6503864, by rfl⟩ : syracuseStep 8671819 = 13007729) B13007729
theorem B11562425 : Blo 2283435 11562425 := bstep (se 2 (by rfl) ⟨4335909, by rfl⟩ : syracuseStep 11562425 = 8671819) B8671819
theorem B7708283 : Blo 2283435 7708283 := bstep (se 1 (by rfl) ⟨5781212, by rfl⟩ : syracuseStep 7708283 = 11562425) B11562425
theorem B5138855 : Blo 2283435 5138855 := bstep (se 1 (by rfl) ⟨3854141, by rfl⟩ : syracuseStep 5138855 = 7708283) B7708283
theorem B3425903 : Blo 2283435 3425903 := bstep (se 1 (by rfl) ⟨2569427, by rfl⟩ : syracuseStep 3425903 = 5138855) B5138855
theorem B2283935 : Blo 2283435 2283935 := bstep (se 1 (by rfl) ⟨1712951, by rfl⟩ : syracuseStep 2283935 = 3425903) B3425903
theorem B3425909 : Blo 2283435 3425909 := bbase (se 5 (by rfl) ⟨160589, by rfl⟩ : syracuseStep 3425909 = 321179) (by norm_num)
theorem B2283939 : Blo 2283435 2283939 := bstep (se 1 (by rfl) ⟨1712954, by rfl⟩ : syracuseStep 2283939 = 3425909) B3425909
theorem B4335925 : Blo 2283435 4335925 := bbase (se 5 (by rfl) ⟨203246, by rfl⟩ : syracuseStep 4335925 = 406493) (by norm_num)
theorem B5781233 : Blo 2283435 5781233 := bstep (se 2 (by rfl) ⟨2167962, by rfl⟩ : syracuseStep 5781233 = 4335925) B4335925
theorem B3854155 : Blo 2283435 3854155 := bstep (se 1 (by rfl) ⟨2890616, by rfl⟩ : syracuseStep 3854155 = 5781233) B5781233
theorem B5138873 : Blo 2283435 5138873 := bstep (se 2 (by rfl) ⟨1927077, by rfl⟩ : syracuseStep 5138873 = 3854155) B3854155
theorem B3425915 : Blo 2283435 3425915 := bstep (se 1 (by rfl) ⟨2569436, by rfl⟩ : syracuseStep 3425915 = 5138873) B5138873
theorem B2283943 : Blo 2283435 2283943 := bstep (se 1 (by rfl) ⟨1712957, by rfl⟩ : syracuseStep 2283943 = 3425915) B3425915
theorem B2569441 : Blo 2283435 2569441 := bbase (se 2 (by rfl) ⟨963540, by rfl⟩ : syracuseStep 2569441 = 1927081) (by norm_num)
theorem B3425921 : Blo 2283435 3425921 := bstep (se 2 (by rfl) ⟨1284720, by rfl⟩ : syracuseStep 3425921 = 2569441) B2569441
theorem B2283947 : Blo 2283435 2283947 := bstep (se 1 (by rfl) ⟨1712960, by rfl⟩ : syracuseStep 2283947 = 3425921) B3425921
theorem B5781253 : Blo 2283435 5781253 := bbase (se 4 (by rfl) ⟨541992, by rfl⟩ : syracuseStep 5781253 = 1083985) (by norm_num)
theorem B7708337 : Blo 2283435 7708337 := bstep (se 2 (by rfl) ⟨2890626, by rfl⟩ : syracuseStep 7708337 = 5781253) B5781253
theorem B5138891 : Blo 2283435 5138891 := bstep (se 1 (by rfl) ⟨3854168, by rfl⟩ : syracuseStep 5138891 = 7708337) B7708337
theorem B3425927 : Blo 2283435 3425927 := bstep (se 1 (by rfl) ⟨2569445, by rfl⟩ : syracuseStep 3425927 = 5138891) B5138891
theorem B2283951 : Blo 2283435 2283951 := bstep (se 1 (by rfl) ⟨1712963, by rfl⟩ : syracuseStep 2283951 = 3425927) B3425927
theorem B3425933 : Blo 2283435 3425933 := bbase (se 3 (by rfl) ⟨642362, by rfl⟩ : syracuseStep 3425933 = 1284725) (by norm_num)
theorem B2283955 : Blo 2283435 2283955 := bstep (se 1 (by rfl) ⟨1712966, by rfl⟩ : syracuseStep 2283955 = 3425933) B3425933
theorem B5138909 : Blo 2283435 5138909 := bbase (se 3 (by rfl) ⟨963545, by rfl⟩ : syracuseStep 5138909 = 1927091) (by norm_num)
theorem B3425939 : Blo 2283435 3425939 := bstep (se 1 (by rfl) ⟨2569454, by rfl⟩ : syracuseStep 3425939 = 5138909) B5138909
theorem B2283959 : Blo 2283435 2283959 := bstep (se 1 (by rfl) ⟨1712969, by rfl⟩ : syracuseStep 2283959 = 3425939) B3425939
theorem B3854189 : Blo 2283435 3854189 := bbase (se 3 (by rfl) ⟨722660, by rfl⟩ : syracuseStep 3854189 = 1445321) (by norm_num)
theorem B2569459 : Blo 2283435 2569459 := bstep (se 1 (by rfl) ⟨1927094, by rfl⟩ : syracuseStep 2569459 = 3854189) B3854189
theorem B3425945 : Blo 2283435 3425945 := bstep (se 2 (by rfl) ⟨1284729, by rfl⟩ : syracuseStep 3425945 = 2569459) B2569459
theorem B2283963 : Blo 2283435 2283963 := bstep (se 1 (by rfl) ⟨1712972, by rfl⟩ : syracuseStep 2283963 = 3425945) B3425945
theorem B2315129 : Blo 2283435 2315129 := bbase (se 2 (by rfl) ⟨868173, by rfl⟩ : syracuseStep 2315129 = 1736347) (by norm_num)
theorem B6173677 : Blo 2283435 6173677 := bstep (se 3 (by rfl) ⟨1157564, by rfl⟩ : syracuseStep 6173677 = 2315129) B2315129
theorem B32926277 : Blo 2283435 32926277 := bstep (se 4 (by rfl) ⟨3086838, by rfl⟩ : syracuseStep 32926277 = 6173677) B6173677
theorem B21950851 : Blo 2283435 21950851 := bstep (se 1 (by rfl) ⟨16463138, by rfl⟩ : syracuseStep 21950851 = 32926277) B32926277
theorem B29267801 : Blo 2283435 29267801 := bstep (se 2 (by rfl) ⟨10975425, by rfl⟩ : syracuseStep 29267801 = 21950851) B21950851
theorem B19511867 : Blo 2283435 19511867 := bstep (se 1 (by rfl) ⟨14633900, by rfl⟩ : syracuseStep 19511867 = 29267801) B29267801
theorem B13007911 : Blo 2283435 13007911 := bstep (se 1 (by rfl) ⟨9755933, by rfl⟩ : syracuseStep 13007911 = 19511867) B19511867
theorem B17343881 : Blo 2283435 17343881 := bstep (se 2 (by rfl) ⟨6503955, by rfl⟩ : syracuseStep 17343881 = 13007911) B13007911
theorem B11562587 : Blo 2283435 11562587 := bstep (se 1 (by rfl) ⟨8671940, by rfl⟩ : syracuseStep 11562587 = 17343881) B17343881
theorem B7708391 : Blo 2283435 7708391 := bstep (se 1 (by rfl) ⟨5781293, by rfl⟩ : syracuseStep 7708391 = 11562587) B11562587
theorem B5138927 : Blo 2283435 5138927 := bstep (se 1 (by rfl) ⟨3854195, by rfl⟩ : syracuseStep 5138927 = 7708391) B7708391
theorem B3425951 : Blo 2283435 3425951 := bstep (se 1 (by rfl) ⟨2569463, by rfl⟩ : syracuseStep 3425951 = 5138927) B5138927
theorem B2283967 : Blo 2283435 2283967 := bstep (se 1 (by rfl) ⟨1712975, by rfl⟩ : syracuseStep 2283967 = 3425951) B3425951
theorem B3425957 : Blo 2283435 3425957 := bbase (se 4 (by rfl) ⟨321183, by rfl⟩ : syracuseStep 3425957 = 642367) (by norm_num)
theorem B2283971 : Blo 2283435 2283971 := bstep (se 1 (by rfl) ⟨1712978, by rfl⟩ : syracuseStep 2283971 = 3425957) B3425957
theorem B2890657 : Blo 2283435 2890657 := bbase (se 2 (by rfl) ⟨1083996, by rfl⟩ : syracuseStep 2890657 = 2167993) (by norm_num)
theorem B3854209 : Blo 2283435 3854209 := bstep (se 2 (by rfl) ⟨1445328, by rfl⟩ : syracuseStep 3854209 = 2890657) B2890657
theorem B5138945 : Blo 2283435 5138945 := bstep (se 2 (by rfl) ⟨1927104, by rfl⟩ : syracuseStep 5138945 = 3854209) B3854209
theorem B3425963 : Blo 2283435 3425963 := bstep (se 1 (by rfl) ⟨2569472, by rfl⟩ : syracuseStep 3425963 = 5138945) B5138945
theorem B2283975 : Blo 2283435 2283975 := bstep (se 1 (by rfl) ⟨1712981, by rfl⟩ : syracuseStep 2283975 = 3425963) B3425963
theorem B2569477 : Blo 2283435 2569477 := bbase (se 4 (by rfl) ⟨240888, by rfl⟩ : syracuseStep 2569477 = 481777) (by norm_num)
theorem B3425969 : Blo 2283435 3425969 := bstep (se 2 (by rfl) ⟨1284738, by rfl⟩ : syracuseStep 3425969 = 2569477) B2569477
theorem B2283979 : Blo 2283435 2283979 := bstep (se 1 (by rfl) ⟨1712984, by rfl⟩ : syracuseStep 2283979 = 3425969) B3425969
theorem B2439001 : Blo 2283435 2439001 := bbase (se 2 (by rfl) ⟨914625, by rfl⟩ : syracuseStep 2439001 = 1829251) (by norm_num)
theorem B3252001 : Blo 2283435 3252001 := bstep (se 2 (by rfl) ⟨1219500, by rfl⟩ : syracuseStep 3252001 = 2439001) B2439001
theorem B4336001 : Blo 2283435 4336001 := bstep (se 2 (by rfl) ⟨1626000, by rfl⟩ : syracuseStep 4336001 = 3252001) B3252001
theorem B2890667 : Blo 2283435 2890667 := bstep (se 1 (by rfl) ⟨2168000, by rfl⟩ : syracuseStep 2890667 = 4336001) B4336001
theorem B7708445 : Blo 2283435 7708445 := bstep (se 3 (by rfl) ⟨1445333, by rfl⟩ : syracuseStep 7708445 = 2890667) B2890667
theorem B5138963 : Blo 2283435 5138963 := bstep (se 1 (by rfl) ⟨3854222, by rfl⟩ : syracuseStep 5138963 = 7708445) B7708445
theorem B3425975 : Blo 2283435 3425975 := bstep (se 1 (by rfl) ⟨2569481, by rfl⟩ : syracuseStep 3425975 = 5138963) B5138963
theorem B2283983 : Blo 2283435 2283983 := bstep (se 1 (by rfl) ⟨1712987, by rfl⟩ : syracuseStep 2283983 = 3425975) B3425975
theorem B3425981 : Blo 2283435 3425981 := bbase (se 3 (by rfl) ⟨642371, by rfl⟩ : syracuseStep 3425981 = 1284743) (by norm_num)
theorem B2283987 : Blo 2283435 2283987 := bstep (se 1 (by rfl) ⟨1712990, by rfl⟩ : syracuseStep 2283987 = 3425981) B3425981
theorem B5138981 : Blo 2283435 5138981 := bbase (se 4 (by rfl) ⟨481779, by rfl⟩ : syracuseStep 5138981 = 963559) (by norm_num)
theorem B3425987 : Blo 2283435 3425987 := bstep (se 1 (by rfl) ⟨2569490, by rfl⟩ : syracuseStep 3425987 = 5138981) B5138981
theorem B2283991 : Blo 2283435 2283991 := bstep (se 1 (by rfl) ⟨1712993, by rfl⟩ : syracuseStep 2283991 = 3425987) B3425987
theorem B5781365 : Blo 2283435 5781365 := bbase (se 5 (by rfl) ⟨271001, by rfl⟩ : syracuseStep 5781365 = 542003) (by norm_num)
theorem B3854243 : Blo 2283435 3854243 := bstep (se 1 (by rfl) ⟨2890682, by rfl⟩ : syracuseStep 3854243 = 5781365) B5781365
theorem B2569495 : Blo 2283435 2569495 := bstep (se 1 (by rfl) ⟨1927121, by rfl⟩ : syracuseStep 2569495 = 3854243) B3854243
theorem B3425993 : Blo 2283435 3425993 := bstep (se 2 (by rfl) ⟨1284747, by rfl⟩ : syracuseStep 3425993 = 2569495) B2569495
theorem B2283995 : Blo 2283435 2283995 := bstep (se 1 (by rfl) ⟨1712996, by rfl⟩ : syracuseStep 2283995 = 3425993) B3425993
theorem B2604557 : Blo 2283435 2604557 := bbase (se 3 (by rfl) ⟨488354, by rfl⟩ : syracuseStep 2604557 = 976709) (by norm_num)
theorem B6945485 : Blo 2283435 6945485 := bstep (se 3 (by rfl) ⟨1302278, by rfl⟩ : syracuseStep 6945485 = 2604557) B2604557
theorem B18521293 : Blo 2283435 18521293 := bstep (se 3 (by rfl) ⟨3472742, by rfl⟩ : syracuseStep 18521293 = 6945485) B6945485
theorem B24695057 : Blo 2283435 24695057 := bstep (se 2 (by rfl) ⟨9260646, by rfl⟩ : syracuseStep 24695057 = 18521293) B18521293
theorem B16463371 : Blo 2283435 16463371 := bstep (se 1 (by rfl) ⟨12347528, by rfl⟩ : syracuseStep 16463371 = 24695057) B24695057
theorem B21951161 : Blo 2283435 21951161 := bstep (se 2 (by rfl) ⟨8231685, by rfl⟩ : syracuseStep 21951161 = 16463371) B16463371
theorem B14634107 : Blo 2283435 14634107 := bstep (se 1 (by rfl) ⟨10975580, by rfl⟩ : syracuseStep 14634107 = 21951161) B21951161
theorem B9756071 : Blo 2283435 9756071 := bstep (se 1 (by rfl) ⟨7317053, by rfl⟩ : syracuseStep 9756071 = 14634107) B14634107
theorem B6504047 : Blo 2283435 6504047 := bstep (se 1 (by rfl) ⟨4878035, by rfl⟩ : syracuseStep 6504047 = 9756071) B9756071
theorem B4336031 : Blo 2283435 4336031 := bstep (se 1 (by rfl) ⟨3252023, by rfl⟩ : syracuseStep 4336031 = 6504047) B6504047
theorem B11562749 : Blo 2283435 11562749 := bstep (se 3 (by rfl) ⟨2168015, by rfl⟩ : syracuseStep 11562749 = 4336031) B4336031
theorem B7708499 : Blo 2283435 7708499 := bstep (se 1 (by rfl) ⟨5781374, by rfl⟩ : syracuseStep 7708499 = 11562749) B11562749
theorem B5138999 : Blo 2283435 5138999 := bstep (se 1 (by rfl) ⟨3854249, by rfl⟩ : syracuseStep 5138999 = 7708499) B7708499
theorem B3425999 : Blo 2283435 3425999 := bstep (se 1 (by rfl) ⟨2569499, by rfl⟩ : syracuseStep 3425999 = 5138999) B5138999
theorem B2283999 : Blo 2283435 2283999 := bstep (se 1 (by rfl) ⟨1712999, by rfl⟩ : syracuseStep 2283999 = 3425999) B3425999
theorem B3426005 : Blo 2283435 3426005 := bbase (se 7 (by rfl) ⟨40148, by rfl⟩ : syracuseStep 3426005 = 80297) (by norm_num)
theorem B2284003 : Blo 2283435 2284003 := bstep (se 1 (by rfl) ⟨1713002, by rfl⟩ : syracuseStep 2284003 = 3426005) B3426005
theorem B4878053 : Blo 2283435 4878053 := bbase (se 4 (by rfl) ⟨457317, by rfl⟩ : syracuseStep 4878053 = 914635) (by norm_num)
theorem B3252035 : Blo 2283435 3252035 := bstep (se 1 (by rfl) ⟨2439026, by rfl⟩ : syracuseStep 3252035 = 4878053) B4878053
theorem B8672093 : Blo 2283435 8672093 := bstep (se 3 (by rfl) ⟨1626017, by rfl⟩ : syracuseStep 8672093 = 3252035) B3252035
theorem B5781395 : Blo 2283435 5781395 := bstep (se 1 (by rfl) ⟨4336046, by rfl⟩ : syracuseStep 5781395 = 8672093) B8672093
theorem B3854263 : Blo 2283435 3854263 := bstep (se 1 (by rfl) ⟨2890697, by rfl⟩ : syracuseStep 3854263 = 5781395) B5781395
theorem B5139017 : Blo 2283435 5139017 := bstep (se 2 (by rfl) ⟨1927131, by rfl⟩ : syracuseStep 5139017 = 3854263) B3854263
theorem B3426011 : Blo 2283435 3426011 := bstep (se 1 (by rfl) ⟨2569508, by rfl⟩ : syracuseStep 3426011 = 5139017) B5139017
theorem B2284007 : Blo 2283435 2284007 := bstep (se 1 (by rfl) ⟨1713005, by rfl⟩ : syracuseStep 2284007 = 3426011) B3426011
theorem B2569513 : Blo 2283435 2569513 := bbase (se 2 (by rfl) ⟨963567, by rfl⟩ : syracuseStep 2569513 = 1927135) (by norm_num)
theorem B3426017 : Blo 2283435 3426017 := bstep (se 2 (by rfl) ⟨1284756, by rfl⟩ : syracuseStep 3426017 = 2569513) B2569513
theorem B2284011 : Blo 2283435 2284011 := bstep (se 1 (by rfl) ⟨1713008, by rfl⟩ : syracuseStep 2284011 = 3426017) B3426017
theorem B76121045 : Blo 2283435 76121045 := bbase (se 7 (by rfl) ⟨892043, by rfl⟩ : syracuseStep 76121045 = 1784087) (by norm_num)
theorem B50747363 : Blo 2283435 50747363 := bstep (se 1 (by rfl) ⟨38060522, by rfl⟩ : syracuseStep 50747363 = 76121045) B76121045
theorem B33831575 : Blo 2283435 33831575 := bstep (se 1 (by rfl) ⟨25373681, by rfl⟩ : syracuseStep 33831575 = 50747363) B50747363
theorem B22554383 : Blo 2283435 22554383 := bstep (se 1 (by rfl) ⟨16915787, by rfl⟩ : syracuseStep 22554383 = 33831575) B33831575
theorem B60145021 : Blo 2283435 60145021 := bstep (se 3 (by rfl) ⟨11277191, by rfl⟩ : syracuseStep 60145021 = 22554383) B22554383
theorem B80193361 : Blo 2283435 80193361 := bstep (se 2 (by rfl) ⟨30072510, by rfl⟩ : syracuseStep 80193361 = 60145021) B60145021
theorem B106924481 : Blo 2283435 106924481 := bstep (se 2 (by rfl) ⟨40096680, by rfl⟩ : syracuseStep 106924481 = 80193361) B80193361
theorem B71282987 : Blo 2283435 71282987 := bstep (se 1 (by rfl) ⟨53462240, by rfl⟩ : syracuseStep 71282987 = 106924481) B106924481
theorem B47521991 : Blo 2283435 47521991 := bstep (se 1 (by rfl) ⟨35641493, by rfl⟩ : syracuseStep 47521991 = 71282987) B71282987
theorem B31681327 : Blo 2283435 31681327 := bstep (se 1 (by rfl) ⟨23760995, by rfl⟩ : syracuseStep 31681327 = 47521991) B47521991
theorem B42241769 : Blo 2283435 42241769 := bstep (se 2 (by rfl) ⟨15840663, by rfl⟩ : syracuseStep 42241769 = 31681327) B31681327
theorem B28161179 : Blo 2283435 28161179 := bstep (se 1 (by rfl) ⟨21120884, by rfl⟩ : syracuseStep 28161179 = 42241769) B42241769
theorem B18774119 : Blo 2283435 18774119 := bstep (se 1 (by rfl) ⟨14080589, by rfl⟩ : syracuseStep 18774119 = 28161179) B28161179
theorem B50064317 : Blo 2283435 50064317 := bstep (se 3 (by rfl) ⟨9387059, by rfl⟩ : syracuseStep 50064317 = 18774119) B18774119
theorem B33376211 : Blo 2283435 33376211 := bstep (se 1 (by rfl) ⟨25032158, by rfl⟩ : syracuseStep 33376211 = 50064317) B50064317
theorem B22250807 : Blo 2283435 22250807 := bstep (se 1 (by rfl) ⟨16688105, by rfl⟩ : syracuseStep 22250807 = 33376211) B33376211
theorem B14833871 : Blo 2283435 14833871 := bstep (se 1 (by rfl) ⟨11125403, by rfl⟩ : syracuseStep 14833871 = 22250807) B22250807
theorem B9889247 : Blo 2283435 9889247 := bstep (se 1 (by rfl) ⟨7416935, by rfl⟩ : syracuseStep 9889247 = 14833871) B14833871
theorem B26371325 : Blo 2283435 26371325 := bstep (se 3 (by rfl) ⟨4944623, by rfl⟩ : syracuseStep 26371325 = 9889247) B9889247
theorem B17580883 : Blo 2283435 17580883 := bstep (se 1 (by rfl) ⟨13185662, by rfl⟩ : syracuseStep 17580883 = 26371325) B26371325
theorem B23441177 : Blo 2283435 23441177 := bstep (se 2 (by rfl) ⟨8790441, by rfl⟩ : syracuseStep 23441177 = 17580883) B17580883
theorem B62509805 : Blo 2283435 62509805 := bstep (se 3 (by rfl) ⟨11720588, by rfl⟩ : syracuseStep 62509805 = 23441177) B23441177
theorem B41673203 : Blo 2283435 41673203 := bstep (se 1 (by rfl) ⟨31254902, by rfl⟩ : syracuseStep 41673203 = 62509805) B62509805
theorem B27782135 : Blo 2283435 27782135 := bstep (se 1 (by rfl) ⟨20836601, by rfl⟩ : syracuseStep 27782135 = 41673203) B41673203
theorem B18521423 : Blo 2283435 18521423 := bstep (se 1 (by rfl) ⟨13891067, by rfl⟩ : syracuseStep 18521423 = 27782135) B27782135
theorem B12347615 : Blo 2283435 12347615 := bstep (se 1 (by rfl) ⟨9260711, by rfl⟩ : syracuseStep 12347615 = 18521423) B18521423
theorem B8231743 : Blo 2283435 8231743 := bstep (se 1 (by rfl) ⟨6173807, by rfl⟩ : syracuseStep 8231743 = 12347615) B12347615
theorem B10975657 : Blo 2283435 10975657 := bstep (se 2 (by rfl) ⟨4115871, by rfl⟩ : syracuseStep 10975657 = 8231743) B8231743
theorem B14634209 : Blo 2283435 14634209 := bstep (se 2 (by rfl) ⟨5487828, by rfl⟩ : syracuseStep 14634209 = 10975657) B10975657
theorem B9756139 : Blo 2283435 9756139 := bstep (se 1 (by rfl) ⟨7317104, by rfl⟩ : syracuseStep 9756139 = 14634209) B14634209
theorem B13008185 : Blo 2283435 13008185 := bstep (se 2 (by rfl) ⟨4878069, by rfl⟩ : syracuseStep 13008185 = 9756139) B9756139
theorem B8672123 : Blo 2283435 8672123 := bstep (se 1 (by rfl) ⟨6504092, by rfl⟩ : syracuseStep 8672123 = 13008185) B13008185
theorem B5781415 : Blo 2283435 5781415 := bstep (se 1 (by rfl) ⟨4336061, by rfl⟩ : syracuseStep 5781415 = 8672123) B8672123
theorem B7708553 : Blo 2283435 7708553 := bstep (se 2 (by rfl) ⟨2890707, by rfl⟩ : syracuseStep 7708553 = 5781415) B5781415
theorem B5139035 : Blo 2283435 5139035 := bstep (se 1 (by rfl) ⟨3854276, by rfl⟩ : syracuseStep 5139035 = 7708553) B7708553
theorem B3426023 : Blo 2283435 3426023 := bstep (se 1 (by rfl) ⟨2569517, by rfl⟩ : syracuseStep 3426023 = 5139035) B5139035
theorem B2284015 : Blo 2283435 2284015 := bstep (se 1 (by rfl) ⟨1713011, by rfl⟩ : syracuseStep 2284015 = 3426023) B3426023
theorem B3426029 : Blo 2283435 3426029 := bbase (se 3 (by rfl) ⟨642380, by rfl⟩ : syracuseStep 3426029 = 1284761) (by norm_num)
theorem B2284019 : Blo 2283435 2284019 := bstep (se 1 (by rfl) ⟨1713014, by rfl⟩ : syracuseStep 2284019 = 3426029) B3426029
theorem B5139053 : Blo 2283435 5139053 := bbase (se 3 (by rfl) ⟨963572, by rfl⟩ : syracuseStep 5139053 = 1927145) (by norm_num)
theorem B3426035 : Blo 2283435 3426035 := bstep (se 1 (by rfl) ⟨2569526, by rfl⟩ : syracuseStep 3426035 = 5139053) B5139053
theorem B2284023 : Blo 2283435 2284023 := bstep (se 1 (by rfl) ⟨1713017, by rfl⟩ : syracuseStep 2284023 = 3426035) B3426035
theorem B4336085 : Blo 2283435 4336085 := bbase (se 7 (by rfl) ⟨50813, by rfl⟩ : syracuseStep 4336085 = 101627) (by norm_num)
theorem B2890723 : Blo 2283435 2890723 := bstep (se 1 (by rfl) ⟨2168042, by rfl⟩ : syracuseStep 2890723 = 4336085) B4336085
theorem B3854297 : Blo 2283435 3854297 := bstep (se 2 (by rfl) ⟨1445361, by rfl⟩ : syracuseStep 3854297 = 2890723) B2890723
theorem B2569531 : Blo 2283435 2569531 := bstep (se 1 (by rfl) ⟨1927148, by rfl⟩ : syracuseStep 2569531 = 3854297) B3854297
theorem B3426041 : Blo 2283435 3426041 := bstep (se 2 (by rfl) ⟨1284765, by rfl⟩ : syracuseStep 3426041 = 2569531) B2569531
theorem B2284027 : Blo 2283435 2284027 := bstep (se 1 (by rfl) ⟨1713020, by rfl⟩ : syracuseStep 2284027 = 3426041) B3426041
theorem B140648021 : Blo 2283435 140648021 := bbase (se 8 (by rfl) ⟨824109, by rfl⟩ : syracuseStep 140648021 = 1648219) (by norm_num)
theorem B93765347 : Blo 2283435 93765347 := bstep (se 1 (by rfl) ⟨70324010, by rfl⟩ : syracuseStep 93765347 = 140648021) B140648021
theorem B62510231 : Blo 2283435 62510231 := bstep (se 1 (by rfl) ⟨46882673, by rfl⟩ : syracuseStep 62510231 = 93765347) B93765347
theorem B41673487 : Blo 2283435 41673487 := bstep (se 1 (by rfl) ⟨31255115, by rfl⟩ : syracuseStep 41673487 = 62510231) B62510231
theorem B55564649 : Blo 2283435 55564649 := bstep (se 2 (by rfl) ⟨20836743, by rfl⟩ : syracuseStep 55564649 = 41673487) B41673487
theorem B37043099 : Blo 2283435 37043099 := bstep (se 1 (by rfl) ⟨27782324, by rfl⟩ : syracuseStep 37043099 = 55564649) B55564649
theorem B24695399 : Blo 2283435 24695399 := bstep (se 1 (by rfl) ⟨18521549, by rfl⟩ : syracuseStep 24695399 = 37043099) B37043099
theorem B65854397 : Blo 2283435 65854397 := bstep (se 3 (by rfl) ⟨12347699, by rfl⟩ : syracuseStep 65854397 = 24695399) B24695399
theorem B43902931 : Blo 2283435 43902931 := bstep (se 1 (by rfl) ⟨32927198, by rfl⟩ : syracuseStep 43902931 = 65854397) B65854397
theorem B58537241 : Blo 2283435 58537241 := bstep (se 2 (by rfl) ⟨21951465, by rfl⟩ : syracuseStep 58537241 = 43902931) B43902931
theorem B39024827 : Blo 2283435 39024827 := bstep (se 1 (by rfl) ⟨29268620, by rfl⟩ : syracuseStep 39024827 = 58537241) B58537241
theorem B26016551 : Blo 2283435 26016551 := bstep (se 1 (by rfl) ⟨19512413, by rfl⟩ : syracuseStep 26016551 = 39024827) B39024827
theorem B17344367 : Blo 2283435 17344367 := bstep (se 1 (by rfl) ⟨13008275, by rfl⟩ : syracuseStep 17344367 = 26016551) B26016551
theorem B11562911 : Blo 2283435 11562911 := bstep (se 1 (by rfl) ⟨8672183, by rfl⟩ : syracuseStep 11562911 = 17344367) B17344367
theorem B7708607 : Blo 2283435 7708607 := bstep (se 1 (by rfl) ⟨5781455, by rfl⟩ : syracuseStep 7708607 = 11562911) B11562911
theorem B5139071 : Blo 2283435 5139071 := bstep (se 1 (by rfl) ⟨3854303, by rfl⟩ : syracuseStep 5139071 = 7708607) B7708607
theorem B3426047 : Blo 2283435 3426047 := bstep (se 1 (by rfl) ⟨2569535, by rfl⟩ : syracuseStep 3426047 = 5139071) B5139071
theorem B2284031 : Blo 2283435 2284031 := bstep (se 1 (by rfl) ⟨1713023, by rfl⟩ : syracuseStep 2284031 = 3426047) B3426047
theorem B3426053 : Blo 2283435 3426053 := bbase (se 4 (by rfl) ⟨321192, by rfl⟩ : syracuseStep 3426053 = 642385) (by norm_num)
theorem B2284035 : Blo 2283435 2284035 := bstep (se 1 (by rfl) ⟨1713026, by rfl⟩ : syracuseStep 2284035 = 3426053) B3426053
theorem B3854317 : Blo 2283435 3854317 := bbase (se 3 (by rfl) ⟨722684, by rfl⟩ : syracuseStep 3854317 = 1445369) (by norm_num)
theorem B5139089 : Blo 2283435 5139089 := bstep (se 2 (by rfl) ⟨1927158, by rfl⟩ : syracuseStep 5139089 = 3854317) B3854317
theorem B3426059 : Blo 2283435 3426059 := bstep (se 1 (by rfl) ⟨2569544, by rfl⟩ : syracuseStep 3426059 = 5139089) B5139089
theorem B2284039 : Blo 2283435 2284039 := bstep (se 1 (by rfl) ⟨1713029, by rfl⟩ : syracuseStep 2284039 = 3426059) B3426059
theorem B2569549 : Blo 2283435 2569549 := bbase (se 3 (by rfl) ⟨481790, by rfl⟩ : syracuseStep 2569549 = 963581) (by norm_num)
theorem B3426065 : Blo 2283435 3426065 := bstep (se 2 (by rfl) ⟨1284774, by rfl⟩ : syracuseStep 3426065 = 2569549) B2569549
theorem B2284043 : Blo 2283435 2284043 := bstep (se 1 (by rfl) ⟨1713032, by rfl⟩ : syracuseStep 2284043 = 3426065) B3426065
theorem B7708661 : Blo 2283435 7708661 := bbase (se 5 (by rfl) ⟨361343, by rfl⟩ : syracuseStep 7708661 = 722687) (by norm_num)
theorem B5139107 : Blo 2283435 5139107 := bstep (se 1 (by rfl) ⟨3854330, by rfl⟩ : syracuseStep 5139107 = 7708661) B7708661
theorem B3426071 : Blo 2283435 3426071 := bstep (se 1 (by rfl) ⟨2569553, by rfl⟩ : syracuseStep 3426071 = 5139107) B5139107
theorem B2284047 : Blo 2283435 2284047 := bstep (se 1 (by rfl) ⟨1713035, by rfl⟩ : syracuseStep 2284047 = 3426071) B3426071
theorem B3426077 : Blo 2283435 3426077 := bbase (se 3 (by rfl) ⟨642389, by rfl⟩ : syracuseStep 3426077 = 1284779) (by norm_num)
theorem B2284051 : Blo 2283435 2284051 := bstep (se 1 (by rfl) ⟨1713038, by rfl⟩ : syracuseStep 2284051 = 3426077) B3426077
theorem B5139125 : Blo 2283435 5139125 := bbase (se 5 (by rfl) ⟨240896, by rfl⟩ : syracuseStep 5139125 = 481793) (by norm_num)
theorem B3426083 : Blo 2283435 3426083 := bstep (se 1 (by rfl) ⟨2569562, by rfl⟩ : syracuseStep 3426083 = 5139125) B5139125
theorem B2284055 : Blo 2283435 2284055 := bstep (se 1 (by rfl) ⟨1713041, by rfl⟩ : syracuseStep 2284055 = 3426083) B3426083
theorem B13008437 : Blo 2283435 13008437 := bbase (se 5 (by rfl) ⟨609770, by rfl⟩ : syracuseStep 13008437 = 1219541) (by norm_num)
theorem B8672291 : Blo 2283435 8672291 := bstep (se 1 (by rfl) ⟨6504218, by rfl⟩ : syracuseStep 8672291 = 13008437) B13008437
theorem B5781527 : Blo 2283435 5781527 := bstep (se 1 (by rfl) ⟨4336145, by rfl⟩ : syracuseStep 5781527 = 8672291) B8672291
theorem B3854351 : Blo 2283435 3854351 := bstep (se 1 (by rfl) ⟨2890763, by rfl⟩ : syracuseStep 3854351 = 5781527) B5781527
theorem B2569567 : Blo 2283435 2569567 := bstep (se 1 (by rfl) ⟨1927175, by rfl⟩ : syracuseStep 2569567 = 3854351) B3854351
theorem B3426089 : Blo 2283435 3426089 := bstep (se 2 (by rfl) ⟨1284783, by rfl⟩ : syracuseStep 3426089 = 2569567) B2569567
theorem B2284059 : Blo 2283435 2284059 := bstep (se 1 (by rfl) ⟨1713044, by rfl⟩ : syracuseStep 2284059 = 3426089) B3426089
theorem B6504229 : Blo 2283435 6504229 := bbase (se 4 (by rfl) ⟨609771, by rfl⟩ : syracuseStep 6504229 = 1219543) (by norm_num)
theorem B8672305 : Blo 2283435 8672305 := bstep (se 2 (by rfl) ⟨3252114, by rfl⟩ : syracuseStep 8672305 = 6504229) B6504229
theorem B11563073 : Blo 2283435 11563073 := bstep (se 2 (by rfl) ⟨4336152, by rfl⟩ : syracuseStep 11563073 = 8672305) B8672305
theorem B7708715 : Blo 2283435 7708715 := bstep (se 1 (by rfl) ⟨5781536, by rfl⟩ : syracuseStep 7708715 = 11563073) B11563073
theorem B5139143 : Blo 2283435 5139143 := bstep (se 1 (by rfl) ⟨3854357, by rfl⟩ : syracuseStep 5139143 = 7708715) B7708715
theorem B3426095 : Blo 2283435 3426095 := bstep (se 1 (by rfl) ⟨2569571, by rfl⟩ : syracuseStep 3426095 = 5139143) B5139143
theorem B2284063 : Blo 2283435 2284063 := bstep (se 1 (by rfl) ⟨1713047, by rfl⟩ : syracuseStep 2284063 = 3426095) B3426095
theorem B3426101 : Blo 2283435 3426101 := bbase (se 5 (by rfl) ⟨160598, by rfl⟩ : syracuseStep 3426101 = 321197) (by norm_num)
theorem B2284067 : Blo 2283435 2284067 := bstep (se 1 (by rfl) ⟨1713050, by rfl⟩ : syracuseStep 2284067 = 3426101) B3426101
theorem B5781557 : Blo 2283435 5781557 := bbase (se 5 (by rfl) ⟨271010, by rfl⟩ : syracuseStep 5781557 = 542021) (by norm_num)
theorem B3854371 : Blo 2283435 3854371 := bstep (se 1 (by rfl) ⟨2890778, by rfl⟩ : syracuseStep 3854371 = 5781557) B5781557
theorem B5139161 : Blo 2283435 5139161 := bstep (se 2 (by rfl) ⟨1927185, by rfl⟩ : syracuseStep 5139161 = 3854371) B3854371
theorem B3426107 : Blo 2283435 3426107 := bstep (se 1 (by rfl) ⟨2569580, by rfl⟩ : syracuseStep 3426107 = 5139161) B5139161
theorem B2284071 : Blo 2283435 2284071 := bstep (se 1 (by rfl) ⟨1713053, by rfl⟩ : syracuseStep 2284071 = 3426107) B3426107
theorem B2569585 : Blo 2283435 2569585 := bbase (se 2 (by rfl) ⟨963594, by rfl⟩ : syracuseStep 2569585 = 1927189) (by norm_num)
theorem B3426113 : Blo 2283435 3426113 := bstep (se 2 (by rfl) ⟨1284792, by rfl⟩ : syracuseStep 3426113 = 2569585) B2569585
theorem B2284075 : Blo 2283435 2284075 := bstep (se 1 (by rfl) ⟨1713056, by rfl⟩ : syracuseStep 2284075 = 3426113) B3426113
theorem B3906973 : Blo 2283435 3906973 := bbase (se 3 (by rfl) ⟨732557, by rfl⟩ : syracuseStep 3906973 = 1465115) (by norm_num)
theorem B20837189 : Blo 2283435 20837189 := bstep (se 4 (by rfl) ⟨1953486, by rfl⟩ : syracuseStep 20837189 = 3906973) B3906973
theorem B13891459 : Blo 2283435 13891459 := bstep (se 1 (by rfl) ⟨10418594, by rfl⟩ : syracuseStep 13891459 = 20837189) B20837189
theorem B18521945 : Blo 2283435 18521945 := bstep (se 2 (by rfl) ⟨6945729, by rfl⟩ : syracuseStep 18521945 = 13891459) B13891459
theorem B12347963 : Blo 2283435 12347963 := bstep (se 1 (by rfl) ⟨9260972, by rfl⟩ : syracuseStep 12347963 = 18521945) B18521945
theorem B8231975 : Blo 2283435 8231975 := bstep (se 1 (by rfl) ⟨6173981, by rfl⟩ : syracuseStep 8231975 = 12347963) B12347963
theorem B5487983 : Blo 2283435 5487983 := bstep (se 1 (by rfl) ⟨4115987, by rfl⟩ : syracuseStep 5487983 = 8231975) B8231975
theorem B3658655 : Blo 2283435 3658655 := bstep (se 1 (by rfl) ⟨2743991, by rfl⟩ : syracuseStep 3658655 = 5487983) B5487983
theorem B9756413 : Blo 2283435 9756413 := bstep (se 3 (by rfl) ⟨1829327, by rfl⟩ : syracuseStep 9756413 = 3658655) B3658655
theorem B6504275 : Blo 2283435 6504275 := bstep (se 1 (by rfl) ⟨4878206, by rfl⟩ : syracuseStep 6504275 = 9756413) B9756413
theorem B4336183 : Blo 2283435 4336183 := bstep (se 1 (by rfl) ⟨3252137, by rfl⟩ : syracuseStep 4336183 = 6504275) B6504275
theorem B5781577 : Blo 2283435 5781577 := bstep (se 2 (by rfl) ⟨2168091, by rfl⟩ : syracuseStep 5781577 = 4336183) B4336183
theorem B7708769 : Blo 2283435 7708769 := bstep (se 2 (by rfl) ⟨2890788, by rfl⟩ : syracuseStep 7708769 = 5781577) B5781577
theorem B5139179 : Blo 2283435 5139179 := bstep (se 1 (by rfl) ⟨3854384, by rfl⟩ : syracuseStep 5139179 = 7708769) B7708769
theorem B3426119 : Blo 2283435 3426119 := bstep (se 1 (by rfl) ⟨2569589, by rfl⟩ : syracuseStep 3426119 = 5139179) B5139179
theorem B2284079 : Blo 2283435 2284079 := bstep (se 1 (by rfl) ⟨1713059, by rfl⟩ : syracuseStep 2284079 = 3426119) B3426119
theorem B3426125 : Blo 2283435 3426125 := bbase (se 3 (by rfl) ⟨642398, by rfl⟩ : syracuseStep 3426125 = 1284797) (by norm_num)
theorem B2284083 : Blo 2283435 2284083 := bstep (se 1 (by rfl) ⟨1713062, by rfl⟩ : syracuseStep 2284083 = 3426125) B3426125
theorem B5139197 : Blo 2283435 5139197 := bbase (se 3 (by rfl) ⟨963599, by rfl⟩ : syracuseStep 5139197 = 1927199) (by norm_num)
theorem B3426131 : Blo 2283435 3426131 := bstep (se 1 (by rfl) ⟨2569598, by rfl⟩ : syracuseStep 3426131 = 5139197) B5139197
theorem B2284087 : Blo 2283435 2284087 := bstep (se 1 (by rfl) ⟨1713065, by rfl⟩ : syracuseStep 2284087 = 3426131) B3426131
theorem B3854405 : Blo 2283435 3854405 := bbase (se 4 (by rfl) ⟨361350, by rfl⟩ : syracuseStep 3854405 = 722701) (by norm_num)
theorem B2569603 : Blo 2283435 2569603 := bstep (se 1 (by rfl) ⟨1927202, by rfl⟩ : syracuseStep 2569603 = 3854405) B3854405
theorem B3426137 : Blo 2283435 3426137 := bstep (se 2 (by rfl) ⟨1284801, by rfl⟩ : syracuseStep 3426137 = 2569603) B2569603
theorem B2284091 : Blo 2283435 2284091 := bstep (se 1 (by rfl) ⟨1713068, by rfl⟩ : syracuseStep 2284091 = 3426137) B3426137
theorem B17344853 : Blo 2283435 17344853 := bbase (se 10 (by rfl) ⟨25407, by rfl⟩ : syracuseStep 17344853 = 50815) (by norm_num)
theorem B11563235 : Blo 2283435 11563235 := bstep (se 1 (by rfl) ⟨8672426, by rfl⟩ : syracuseStep 11563235 = 17344853) B17344853
theorem B7708823 : Blo 2283435 7708823 := bstep (se 1 (by rfl) ⟨5781617, by rfl⟩ : syracuseStep 7708823 = 11563235) B11563235
theorem B5139215 : Blo 2283435 5139215 := bstep (se 1 (by rfl) ⟨3854411, by rfl⟩ : syracuseStep 5139215 = 7708823) B7708823
theorem B3426143 : Blo 2283435 3426143 := bstep (se 1 (by rfl) ⟨2569607, by rfl⟩ : syracuseStep 3426143 = 5139215) B5139215
theorem B2284095 : Blo 2283435 2284095 := bstep (se 1 (by rfl) ⟨1713071, by rfl⟩ : syracuseStep 2284095 = 3426143) B3426143
theorem B3426149 : Blo 2283435 3426149 := bbase (se 4 (by rfl) ⟨321201, by rfl⟩ : syracuseStep 3426149 = 642403) (by norm_num)
theorem B2284099 : Blo 2283435 2284099 := bstep (se 1 (by rfl) ⟨1713074, by rfl⟩ : syracuseStep 2284099 = 3426149) B3426149
theorem B4336229 : Blo 2283435 4336229 := bbase (se 4 (by rfl) ⟨406521, by rfl⟩ : syracuseStep 4336229 = 813043) (by norm_num)
theorem B2890819 : Blo 2283435 2890819 := bstep (se 1 (by rfl) ⟨2168114, by rfl⟩ : syracuseStep 2890819 = 4336229) B4336229
theorem B3854425 : Blo 2283435 3854425 := bstep (se 2 (by rfl) ⟨1445409, by rfl⟩ : syracuseStep 3854425 = 2890819) B2890819
theorem B5139233 : Blo 2283435 5139233 := bstep (se 2 (by rfl) ⟨1927212, by rfl⟩ : syracuseStep 5139233 = 3854425) B3854425
theorem B3426155 : Blo 2283435 3426155 := bstep (se 1 (by rfl) ⟨2569616, by rfl⟩ : syracuseStep 3426155 = 5139233) B5139233
theorem B2284103 : Blo 2283435 2284103 := bstep (se 1 (by rfl) ⟨1713077, by rfl⟩ : syracuseStep 2284103 = 3426155) B3426155
theorem B2569621 : Blo 2283435 2569621 := bbase (se 6 (by rfl) ⟨60225, by rfl⟩ : syracuseStep 2569621 = 120451) (by norm_num)
theorem B3426161 : Blo 2283435 3426161 := bstep (se 2 (by rfl) ⟨1284810, by rfl⟩ : syracuseStep 3426161 = 2569621) B2569621
theorem B2284107 : Blo 2283435 2284107 := bstep (se 1 (by rfl) ⟨1713080, by rfl⟩ : syracuseStep 2284107 = 3426161) B3426161
theorem B2890829 : Blo 2283435 2890829 := bbase (se 3 (by rfl) ⟨542030, by rfl⟩ : syracuseStep 2890829 = 1084061) (by norm_num)
theorem B7708877 : Blo 2283435 7708877 := bstep (se 3 (by rfl) ⟨1445414, by rfl⟩ : syracuseStep 7708877 = 2890829) B2890829
theorem B5139251 : Blo 2283435 5139251 := bstep (se 1 (by rfl) ⟨3854438, by rfl⟩ : syracuseStep 5139251 = 7708877) B7708877
theorem B3426167 : Blo 2283435 3426167 := bstep (se 1 (by rfl) ⟨2569625, by rfl⟩ : syracuseStep 3426167 = 5139251) B5139251
theorem B2284111 : Blo 2283435 2284111 := bstep (se 1 (by rfl) ⟨1713083, by rfl⟩ : syracuseStep 2284111 = 3426167) B3426167
theorem B3426173 : Blo 2283435 3426173 := bbase (se 3 (by rfl) ⟨642407, by rfl⟩ : syracuseStep 3426173 = 1284815) (by norm_num)
theorem B2284115 : Blo 2283435 2284115 := bstep (se 1 (by rfl) ⟨1713086, by rfl⟩ : syracuseStep 2284115 = 3426173) B3426173
theorem B5139269 : Blo 2283435 5139269 := bbase (se 4 (by rfl) ⟨481806, by rfl⟩ : syracuseStep 5139269 = 963613) (by norm_num)
theorem B3426179 : Blo 2283435 3426179 := bstep (se 1 (by rfl) ⟨2569634, by rfl⟩ : syracuseStep 3426179 = 5139269) B5139269
theorem B2284119 : Blo 2283435 2284119 := bstep (se 1 (by rfl) ⟨1713089, by rfl⟩ : syracuseStep 2284119 = 3426179) B3426179
theorem B4878301 : Blo 2283435 4878301 := bbase (se 3 (by rfl) ⟨914681, by rfl⟩ : syracuseStep 4878301 = 1829363) (by norm_num)
theorem B6504401 : Blo 2283435 6504401 := bstep (se 2 (by rfl) ⟨2439150, by rfl⟩ : syracuseStep 6504401 = 4878301) B4878301
theorem B4336267 : Blo 2283435 4336267 := bstep (se 1 (by rfl) ⟨3252200, by rfl⟩ : syracuseStep 4336267 = 6504401) B6504401
theorem B5781689 : Blo 2283435 5781689 := bstep (se 2 (by rfl) ⟨2168133, by rfl⟩ : syracuseStep 5781689 = 4336267) B4336267
theorem B3854459 : Blo 2283435 3854459 := bstep (se 1 (by rfl) ⟨2890844, by rfl⟩ : syracuseStep 3854459 = 5781689) B5781689
theorem B2569639 : Blo 2283435 2569639 := bstep (se 1 (by rfl) ⟨1927229, by rfl⟩ : syracuseStep 2569639 = 3854459) B3854459
theorem B3426185 : Blo 2283435 3426185 := bstep (se 2 (by rfl) ⟨1284819, by rfl⟩ : syracuseStep 3426185 = 2569639) B2569639
theorem B2284123 : Blo 2283435 2284123 := bstep (se 1 (by rfl) ⟨1713092, by rfl⟩ : syracuseStep 2284123 = 3426185) B3426185
theorem B11563397 : Blo 2283435 11563397 := bbase (se 4 (by rfl) ⟨1084068, by rfl⟩ : syracuseStep 11563397 = 2168137) (by norm_num)
theorem B7708931 : Blo 2283435 7708931 := bstep (se 1 (by rfl) ⟨5781698, by rfl⟩ : syracuseStep 7708931 = 11563397) B11563397
theorem B5139287 : Blo 2283435 5139287 := bstep (se 1 (by rfl) ⟨3854465, by rfl⟩ : syracuseStep 5139287 = 7708931) B7708931
theorem B3426191 : Blo 2283435 3426191 := bstep (se 1 (by rfl) ⟨2569643, by rfl⟩ : syracuseStep 3426191 = 5139287) B5139287
theorem B2284127 : Blo 2283435 2284127 := bstep (se 1 (by rfl) ⟨1713095, by rfl⟩ : syracuseStep 2284127 = 3426191) B3426191
theorem B3426197 : Blo 2283435 3426197 := bbase (se 6 (by rfl) ⟨80301, by rfl⟩ : syracuseStep 3426197 = 160603) (by norm_num)
theorem B2284131 : Blo 2283435 2284131 := bstep (se 1 (by rfl) ⟨1713098, by rfl⟩ : syracuseStep 2284131 = 3426197) B3426197
theorem B2506177 : Blo 2283435 2506177 := bbase (se 2 (by rfl) ⟨939816, by rfl⟩ : syracuseStep 2506177 = 1879633) (by norm_num)
theorem B3341569 : Blo 2283435 3341569 := bstep (se 2 (by rfl) ⟨1253088, by rfl⟩ : syracuseStep 3341569 = 2506177) B2506177
theorem B4455425 : Blo 2283435 4455425 := bstep (se 2 (by rfl) ⟨1670784, by rfl⟩ : syracuseStep 4455425 = 3341569) B3341569
theorem B11881133 : Blo 2283435 11881133 := bstep (se 3 (by rfl) ⟨2227712, by rfl⟩ : syracuseStep 11881133 = 4455425) B4455425
theorem B7920755 : Blo 2283435 7920755 := bstep (se 1 (by rfl) ⟨5940566, by rfl⟩ : syracuseStep 7920755 = 11881133) B11881133
theorem B5280503 : Blo 2283435 5280503 := bstep (se 1 (by rfl) ⟨3960377, by rfl⟩ : syracuseStep 5280503 = 7920755) B7920755
theorem B56325365 : Blo 2283435 56325365 := bstep (se 5 (by rfl) ⟨2640251, by rfl⟩ : syracuseStep 56325365 = 5280503) B5280503
theorem B37550243 : Blo 2283435 37550243 := bstep (se 1 (by rfl) ⟨28162682, by rfl⟩ : syracuseStep 37550243 = 56325365) B56325365
theorem B25033495 : Blo 2283435 25033495 := bstep (se 1 (by rfl) ⟨18775121, by rfl⟩ : syracuseStep 25033495 = 37550243) B37550243
theorem B33377993 : Blo 2283435 33377993 := bstep (se 2 (by rfl) ⟨12516747, by rfl⟩ : syracuseStep 33377993 = 25033495) B25033495
theorem B22251995 : Blo 2283435 22251995 := bstep (se 1 (by rfl) ⟨16688996, by rfl⟩ : syracuseStep 22251995 = 33377993) B33377993
theorem B14834663 : Blo 2283435 14834663 := bstep (se 1 (by rfl) ⟨11125997, by rfl⟩ : syracuseStep 14834663 = 22251995) B22251995
theorem B9889775 : Blo 2283435 9889775 := bstep (se 1 (by rfl) ⟨7417331, by rfl⟩ : syracuseStep 9889775 = 14834663) B14834663
theorem B6593183 : Blo 2283435 6593183 := bstep (se 1 (by rfl) ⟨4944887, by rfl⟩ : syracuseStep 6593183 = 9889775) B9889775
theorem B4395455 : Blo 2283435 4395455 := bstep (se 1 (by rfl) ⟨3296591, by rfl⟩ : syracuseStep 4395455 = 6593183) B6593183
theorem B2930303 : Blo 2283435 2930303 := bstep (se 1 (by rfl) ⟨2197727, by rfl⟩ : syracuseStep 2930303 = 4395455) B4395455
theorem B7814141 : Blo 2283435 7814141 := bstep (se 3 (by rfl) ⟨1465151, by rfl⟩ : syracuseStep 7814141 = 2930303) B2930303
theorem B5209427 : Blo 2283435 5209427 := bstep (se 1 (by rfl) ⟨3907070, by rfl⟩ : syracuseStep 5209427 = 7814141) B7814141
theorem B3472951 : Blo 2283435 3472951 := bstep (se 1 (by rfl) ⟨2604713, by rfl⟩ : syracuseStep 3472951 = 5209427) B5209427
theorem B4630601 : Blo 2283435 4630601 := bstep (se 2 (by rfl) ⟨1736475, by rfl⟩ : syracuseStep 4630601 = 3472951) B3472951
theorem B3087067 : Blo 2283435 3087067 := bstep (se 1 (by rfl) ⟨2315300, by rfl⟩ : syracuseStep 3087067 = 4630601) B4630601
theorem B4116089 : Blo 2283435 4116089 := bstep (se 2 (by rfl) ⟨1543533, by rfl⟩ : syracuseStep 4116089 = 3087067) B3087067
theorem B2744059 : Blo 2283435 2744059 := bstep (se 1 (by rfl) ⟨2058044, by rfl⟩ : syracuseStep 2744059 = 4116089) B4116089
theorem B3658745 : Blo 2283435 3658745 := bstep (se 2 (by rfl) ⟨1372029, by rfl⟩ : syracuseStep 3658745 = 2744059) B2744059
theorem B2439163 : Blo 2283435 2439163 := bstep (se 1 (by rfl) ⟨1829372, by rfl⟩ : syracuseStep 2439163 = 3658745) B3658745
theorem B13008869 : Blo 2283435 13008869 := bstep (se 4 (by rfl) ⟨1219581, by rfl⟩ : syracuseStep 13008869 = 2439163) B2439163
theorem B8672579 : Blo 2283435 8672579 := bstep (se 1 (by rfl) ⟨6504434, by rfl⟩ : syracuseStep 8672579 = 13008869) B13008869
theorem B5781719 : Blo 2283435 5781719 := bstep (se 1 (by rfl) ⟨4336289, by rfl⟩ : syracuseStep 5781719 = 8672579) B8672579
theorem B3854479 : Blo 2283435 3854479 := bstep (se 1 (by rfl) ⟨2890859, by rfl⟩ : syracuseStep 3854479 = 5781719) B5781719
theorem B5139305 : Blo 2283435 5139305 := bstep (se 2 (by rfl) ⟨1927239, by rfl⟩ : syracuseStep 5139305 = 3854479) B3854479
theorem B3426203 : Blo 2283435 3426203 := bstep (se 1 (by rfl) ⟨2569652, by rfl⟩ : syracuseStep 3426203 = 5139305) B5139305
theorem B2284135 : Blo 2283435 2284135 := bstep (se 1 (by rfl) ⟨1713101, by rfl⟩ : syracuseStep 2284135 = 3426203) B3426203
theorem B2569657 : Blo 2283435 2569657 := bbase (se 2 (by rfl) ⟨963621, by rfl⟩ : syracuseStep 2569657 = 1927243) (by norm_num)
theorem B3426209 : Blo 2283435 3426209 := bstep (se 2 (by rfl) ⟨1284828, by rfl⟩ : syracuseStep 3426209 = 2569657) B2569657
theorem B2284139 : Blo 2283435 2284139 := bstep (se 1 (by rfl) ⟨1713104, by rfl⟩ : syracuseStep 2284139 = 3426209) B3426209
theorem B3087077 : Blo 2283435 3087077 := bbase (se 4 (by rfl) ⟨289413, by rfl⟩ : syracuseStep 3087077 = 578827) (by norm_num)
theorem B8232205 : Blo 2283435 8232205 := bstep (se 3 (by rfl) ⟨1543538, by rfl⟩ : syracuseStep 8232205 = 3087077) B3087077
theorem B10976273 : Blo 2283435 10976273 := bstep (se 2 (by rfl) ⟨4116102, by rfl⟩ : syracuseStep 10976273 = 8232205) B8232205
theorem B7317515 : Blo 2283435 7317515 := bstep (se 1 (by rfl) ⟨5488136, by rfl⟩ : syracuseStep 7317515 = 10976273) B10976273
theorem B4878343 : Blo 2283435 4878343 := bstep (se 1 (by rfl) ⟨3658757, by rfl⟩ : syracuseStep 4878343 = 7317515) B7317515
theorem B6504457 : Blo 2283435 6504457 := bstep (se 2 (by rfl) ⟨2439171, by rfl⟩ : syracuseStep 6504457 = 4878343) B4878343
theorem B8672609 : Blo 2283435 8672609 := bstep (se 2 (by rfl) ⟨3252228, by rfl⟩ : syracuseStep 8672609 = 6504457) B6504457
theorem B5781739 : Blo 2283435 5781739 := bstep (se 1 (by rfl) ⟨4336304, by rfl⟩ : syracuseStep 5781739 = 8672609) B8672609
theorem B7708985 : Blo 2283435 7708985 := bstep (se 2 (by rfl) ⟨2890869, by rfl⟩ : syracuseStep 7708985 = 5781739) B5781739
theorem B5139323 : Blo 2283435 5139323 := bstep (se 1 (by rfl) ⟨3854492, by rfl⟩ : syracuseStep 5139323 = 7708985) B7708985
theorem B3426215 : Blo 2283435 3426215 := bstep (se 1 (by rfl) ⟨2569661, by rfl⟩ : syracuseStep 3426215 = 5139323) B5139323
theorem B2284143 : Blo 2283435 2284143 := bstep (se 1 (by rfl) ⟨1713107, by rfl⟩ : syracuseStep 2284143 = 3426215) B3426215
theorem B3426221 : Blo 2283435 3426221 := bbase (se 3 (by rfl) ⟨642416, by rfl⟩ : syracuseStep 3426221 = 1284833) (by norm_num)
theorem B2284147 : Blo 2283435 2284147 := bstep (se 1 (by rfl) ⟨1713110, by rfl⟩ : syracuseStep 2284147 = 3426221) B3426221
theorem B5139341 : Blo 2283435 5139341 := bbase (se 3 (by rfl) ⟨963626, by rfl⟩ : syracuseStep 5139341 = 1927253) (by norm_num)
theorem B3426227 : Blo 2283435 3426227 := bstep (se 1 (by rfl) ⟨2569670, by rfl⟩ : syracuseStep 3426227 = 5139341) B5139341
theorem B2284151 : Blo 2283435 2284151 := bstep (se 1 (by rfl) ⟨1713113, by rfl⟩ : syracuseStep 2284151 = 3426227) B3426227
theorem B2890885 : Blo 2283435 2890885 := bbase (se 4 (by rfl) ⟨271020, by rfl⟩ : syracuseStep 2890885 = 542041) (by norm_num)
theorem B3854513 : Blo 2283435 3854513 := bstep (se 2 (by rfl) ⟨1445442, by rfl⟩ : syracuseStep 3854513 = 2890885) B2890885
theorem B2569675 : Blo 2283435 2569675 := bstep (se 1 (by rfl) ⟨1927256, by rfl⟩ : syracuseStep 2569675 = 3854513) B3854513
theorem B3426233 : Blo 2283435 3426233 := bstep (se 2 (by rfl) ⟨1284837, by rfl⟩ : syracuseStep 3426233 = 2569675) B2569675
theorem B2284155 : Blo 2283435 2284155 := bstep (se 1 (by rfl) ⟨1713116, by rfl⟩ : syracuseStep 2284155 = 3426233) B3426233
theorem B6174197 : Blo 2283435 6174197 := bbase (se 5 (by rfl) ⟨289415, by rfl⟩ : syracuseStep 6174197 = 578831) (by norm_num)
theorem B4116131 : Blo 2283435 4116131 := bstep (se 1 (by rfl) ⟨3087098, by rfl⟩ : syracuseStep 4116131 = 6174197) B6174197
theorem B2744087 : Blo 2283435 2744087 := bstep (se 1 (by rfl) ⟨2058065, by rfl⟩ : syracuseStep 2744087 = 4116131) B4116131
theorem B29270261 : Blo 2283435 29270261 := bstep (se 5 (by rfl) ⟨1372043, by rfl⟩ : syracuseStep 29270261 = 2744087) B2744087
theorem B19513507 : Blo 2283435 19513507 := bstep (se 1 (by rfl) ⟨14635130, by rfl⟩ : syracuseStep 19513507 = 29270261) B29270261
theorem B26018009 : Blo 2283435 26018009 := bstep (se 2 (by rfl) ⟨9756753, by rfl⟩ : syracuseStep 26018009 = 19513507) B19513507
theorem B17345339 : Blo 2283435 17345339 := bstep (se 1 (by rfl) ⟨13009004, by rfl⟩ : syracuseStep 17345339 = 26018009) B26018009
theorem B11563559 : Blo 2283435 11563559 := bstep (se 1 (by rfl) ⟨8672669, by rfl⟩ : syracuseStep 11563559 = 17345339) B17345339
theorem B7709039 : Blo 2283435 7709039 := bstep (se 1 (by rfl) ⟨5781779, by rfl⟩ : syracuseStep 7709039 = 11563559) B11563559
theorem B5139359 : Blo 2283435 5139359 := bstep (se 1 (by rfl) ⟨3854519, by rfl⟩ : syracuseStep 5139359 = 7709039) B7709039
theorem B3426239 : Blo 2283435 3426239 := bstep (se 1 (by rfl) ⟨2569679, by rfl⟩ : syracuseStep 3426239 = 5139359) B5139359
theorem B2284159 : Blo 2283435 2284159 := bstep (se 1 (by rfl) ⟨1713119, by rfl⟩ : syracuseStep 2284159 = 3426239) B3426239
theorem B3426245 : Blo 2283435 3426245 := bbase (se 4 (by rfl) ⟨321210, by rfl⟩ : syracuseStep 3426245 = 642421) (by norm_num)
theorem B2284163 : Blo 2283435 2284163 := bstep (se 1 (by rfl) ⟨1713122, by rfl⟩ : syracuseStep 2284163 = 3426245) B3426245
theorem B3854533 : Blo 2283435 3854533 := bbase (se 4 (by rfl) ⟨361362, by rfl⟩ : syracuseStep 3854533 = 722725) (by norm_num)
theorem B5139377 : Blo 2283435 5139377 := bstep (se 2 (by rfl) ⟨1927266, by rfl⟩ : syracuseStep 5139377 = 3854533) B3854533
theorem B3426251 : Blo 2283435 3426251 := bstep (se 1 (by rfl) ⟨2569688, by rfl⟩ : syracuseStep 3426251 = 5139377) B5139377
theorem B2284167 : Blo 2283435 2284167 := bstep (se 1 (by rfl) ⟨1713125, by rfl⟩ : syracuseStep 2284167 = 3426251) B3426251
theorem B2569693 : Blo 2283435 2569693 := bbase (se 3 (by rfl) ⟨481817, by rfl⟩ : syracuseStep 2569693 = 963635) (by norm_num)
theorem B3426257 : Blo 2283435 3426257 := bstep (se 2 (by rfl) ⟨1284846, by rfl⟩ : syracuseStep 3426257 = 2569693) B2569693
theorem B2284171 : Blo 2283435 2284171 := bstep (se 1 (by rfl) ⟨1713128, by rfl⟩ : syracuseStep 2284171 = 3426257) B3426257
theorem B7709093 : Blo 2283435 7709093 := bbase (se 4 (by rfl) ⟨722727, by rfl⟩ : syracuseStep 7709093 = 1445455) (by norm_num)
theorem B5139395 : Blo 2283435 5139395 := bstep (se 1 (by rfl) ⟨3854546, by rfl⟩ : syracuseStep 5139395 = 7709093) B7709093
theorem B3426263 : Blo 2283435 3426263 := bstep (se 1 (by rfl) ⟨2569697, by rfl⟩ : syracuseStep 3426263 = 5139395) B5139395
theorem B2284175 : Blo 2283435 2284175 := bstep (se 1 (by rfl) ⟨1713131, by rfl⟩ : syracuseStep 2284175 = 3426263) B3426263
theorem B3426269 : Blo 2283435 3426269 := bbase (se 3 (by rfl) ⟨642425, by rfl⟩ : syracuseStep 3426269 = 1284851) (by norm_num)
theorem B2284179 : Blo 2283435 2284179 := bstep (se 1 (by rfl) ⟨1713134, by rfl⟩ : syracuseStep 2284179 = 3426269) B3426269
theorem B5139413 : Blo 2283435 5139413 := bbase (se 7 (by rfl) ⟨60227, by rfl⟩ : syracuseStep 5139413 = 120455) (by norm_num)
theorem B3426275 : Blo 2283435 3426275 := bstep (se 1 (by rfl) ⟨2569706, by rfl⟩ : syracuseStep 3426275 = 5139413) B5139413
theorem B2284183 : Blo 2283435 2284183 := bstep (se 1 (by rfl) ⟨1713137, by rfl⟩ : syracuseStep 2284183 = 3426275) B3426275
theorem B10976485 : Blo 2283435 10976485 := bbase (se 4 (by rfl) ⟨1029045, by rfl⟩ : syracuseStep 10976485 = 2058091) (by norm_num)
theorem B14635313 : Blo 2283435 14635313 := bstep (se 2 (by rfl) ⟨5488242, by rfl⟩ : syracuseStep 14635313 = 10976485) B10976485
theorem B9756875 : Blo 2283435 9756875 := bstep (se 1 (by rfl) ⟨7317656, by rfl⟩ : syracuseStep 9756875 = 14635313) B14635313
theorem B6504583 : Blo 2283435 6504583 := bstep (se 1 (by rfl) ⟨4878437, by rfl⟩ : syracuseStep 6504583 = 9756875) B9756875
theorem B8672777 : Blo 2283435 8672777 := bstep (se 2 (by rfl) ⟨3252291, by rfl⟩ : syracuseStep 8672777 = 6504583) B6504583
theorem B5781851 : Blo 2283435 5781851 := bstep (se 1 (by rfl) ⟨4336388, by rfl⟩ : syracuseStep 5781851 = 8672777) B8672777
theorem B3854567 : Blo 2283435 3854567 := bstep (se 1 (by rfl) ⟨2890925, by rfl⟩ : syracuseStep 3854567 = 5781851) B5781851
theorem B2569711 : Blo 2283435 2569711 := bstep (se 1 (by rfl) ⟨1927283, by rfl⟩ : syracuseStep 2569711 = 3854567) B3854567
theorem B3426281 : Blo 2283435 3426281 := bstep (se 2 (by rfl) ⟨1284855, by rfl⟩ : syracuseStep 3426281 = 2569711) B2569711
theorem B2284187 : Blo 2283435 2284187 := bstep (se 1 (by rfl) ⟨1713140, by rfl⟩ : syracuseStep 2284187 = 3426281) B3426281
theorem B19513781 : Blo 2283435 19513781 := bbase (se 5 (by rfl) ⟨914708, by rfl⟩ : syracuseStep 19513781 = 1829417) (by norm_num)
theorem B13009187 : Blo 2283435 13009187 := bstep (se 1 (by rfl) ⟨9756890, by rfl⟩ : syracuseStep 13009187 = 19513781) B19513781
theorem B8672791 : Blo 2283435 8672791 := bstep (se 1 (by rfl) ⟨6504593, by rfl⟩ : syracuseStep 8672791 = 13009187) B13009187
theorem B11563721 : Blo 2283435 11563721 := bstep (se 2 (by rfl) ⟨4336395, by rfl⟩ : syracuseStep 11563721 = 8672791) B8672791
theorem B7709147 : Blo 2283435 7709147 := bstep (se 1 (by rfl) ⟨5781860, by rfl⟩ : syracuseStep 7709147 = 11563721) B11563721
theorem B5139431 : Blo 2283435 5139431 := bstep (se 1 (by rfl) ⟨3854573, by rfl⟩ : syracuseStep 5139431 = 7709147) B7709147
theorem B3426287 : Blo 2283435 3426287 := bstep (se 1 (by rfl) ⟨2569715, by rfl⟩ : syracuseStep 3426287 = 5139431) B5139431
theorem B2284191 : Blo 2283435 2284191 := bstep (se 1 (by rfl) ⟨1713143, by rfl⟩ : syracuseStep 2284191 = 3426287) B3426287
theorem B3426293 : Blo 2283435 3426293 := bbase (se 5 (by rfl) ⟨160607, by rfl⟩ : syracuseStep 3426293 = 321215) (by norm_num)
theorem B2284195 : Blo 2283435 2284195 := bstep (se 1 (by rfl) ⟨1713146, by rfl⟩ : syracuseStep 2284195 = 3426293) B3426293
theorem B41676565 : Blo 2283435 41676565 := bbase (se 6 (by rfl) ⟨976794, by rfl⟩ : syracuseStep 41676565 = 1953589) (by norm_num)
theorem B55568753 : Blo 2283435 55568753 := bstep (se 2 (by rfl) ⟨20838282, by rfl⟩ : syracuseStep 55568753 = 41676565) B41676565
theorem B37045835 : Blo 2283435 37045835 := bstep (se 1 (by rfl) ⟨27784376, by rfl⟩ : syracuseStep 37045835 = 55568753) B55568753
theorem B24697223 : Blo 2283435 24697223 := bstep (se 1 (by rfl) ⟨18522917, by rfl⟩ : syracuseStep 24697223 = 37045835) B37045835
theorem B16464815 : Blo 2283435 16464815 := bstep (se 1 (by rfl) ⟨12348611, by rfl⟩ : syracuseStep 16464815 = 24697223) B24697223
theorem B10976543 : Blo 2283435 10976543 := bstep (se 1 (by rfl) ⟨8232407, by rfl⟩ : syracuseStep 10976543 = 16464815) B16464815
theorem B7317695 : Blo 2283435 7317695 := bstep (se 1 (by rfl) ⟨5488271, by rfl⟩ : syracuseStep 7317695 = 10976543) B10976543
theorem B4878463 : Blo 2283435 4878463 := bstep (se 1 (by rfl) ⟨3658847, by rfl⟩ : syracuseStep 4878463 = 7317695) B7317695
theorem B6504617 : Blo 2283435 6504617 := bstep (se 2 (by rfl) ⟨2439231, by rfl⟩ : syracuseStep 6504617 = 4878463) B4878463
theorem B4336411 : Blo 2283435 4336411 := bstep (se 1 (by rfl) ⟨3252308, by rfl⟩ : syracuseStep 4336411 = 6504617) B6504617
theorem B5781881 : Blo 2283435 5781881 := bstep (se 2 (by rfl) ⟨2168205, by rfl⟩ : syracuseStep 5781881 = 4336411) B4336411
theorem B3854587 : Blo 2283435 3854587 := bstep (se 1 (by rfl) ⟨2890940, by rfl⟩ : syracuseStep 3854587 = 5781881) B5781881
theorem B5139449 : Blo 2283435 5139449 := bstep (se 2 (by rfl) ⟨1927293, by rfl⟩ : syracuseStep 5139449 = 3854587) B3854587
theorem B3426299 : Blo 2283435 3426299 := bstep (se 1 (by rfl) ⟨2569724, by rfl⟩ : syracuseStep 3426299 = 5139449) B5139449
theorem B2284199 : Blo 2283435 2284199 := bstep (se 1 (by rfl) ⟨1713149, by rfl⟩ : syracuseStep 2284199 = 3426299) B3426299
theorem B2569729 : Blo 2283435 2569729 := bbase (se 2 (by rfl) ⟨963648, by rfl⟩ : syracuseStep 2569729 = 1927297) (by norm_num)
theorem B3426305 : Blo 2283435 3426305 := bstep (se 2 (by rfl) ⟨1284864, by rfl⟩ : syracuseStep 3426305 = 2569729) B2569729
theorem B2284203 : Blo 2283435 2284203 := bstep (se 1 (by rfl) ⟨1713152, by rfl⟩ : syracuseStep 2284203 = 3426305) B3426305
theorem B5781901 : Blo 2283435 5781901 := bbase (se 3 (by rfl) ⟨1084106, by rfl⟩ : syracuseStep 5781901 = 2168213) (by norm_num)
theorem B7709201 : Blo 2283435 7709201 := bstep (se 2 (by rfl) ⟨2890950, by rfl⟩ : syracuseStep 7709201 = 5781901) B5781901
theorem B5139467 : Blo 2283435 5139467 := bstep (se 1 (by rfl) ⟨3854600, by rfl⟩ : syracuseStep 5139467 = 7709201) B7709201
theorem B3426311 : Blo 2283435 3426311 := bstep (se 1 (by rfl) ⟨2569733, by rfl⟩ : syracuseStep 3426311 = 5139467) B5139467
theorem B2284207 : Blo 2283435 2284207 := bstep (se 1 (by rfl) ⟨1713155, by rfl⟩ : syracuseStep 2284207 = 3426311) B3426311
theorem B3426317 : Blo 2283435 3426317 := bbase (se 3 (by rfl) ⟨642434, by rfl⟩ : syracuseStep 3426317 = 1284869) (by norm_num)
theorem B2284211 : Blo 2283435 2284211 := bstep (se 1 (by rfl) ⟨1713158, by rfl⟩ : syracuseStep 2284211 = 3426317) B3426317
theorem B5139485 : Blo 2283435 5139485 := bbase (se 3 (by rfl) ⟨963653, by rfl⟩ : syracuseStep 5139485 = 1927307) (by norm_num)
theorem B3426323 : Blo 2283435 3426323 := bstep (se 1 (by rfl) ⟨2569742, by rfl⟩ : syracuseStep 3426323 = 5139485) B5139485
theorem B2284215 : Blo 2283435 2284215 := bstep (se 1 (by rfl) ⟨1713161, by rfl⟩ : syracuseStep 2284215 = 3426323) B3426323
theorem B3854621 : Blo 2283435 3854621 := bbase (se 3 (by rfl) ⟨722741, by rfl⟩ : syracuseStep 3854621 = 1445483) (by norm_num)
theorem B2569747 : Blo 2283435 2569747 := bstep (se 1 (by rfl) ⟨1927310, by rfl⟩ : syracuseStep 2569747 = 3854621) B3854621
theorem B3426329 : Blo 2283435 3426329 := bstep (se 2 (by rfl) ⟨1284873, by rfl⟩ : syracuseStep 3426329 = 2569747) B2569747
theorem B2284219 : Blo 2283435 2284219 := bstep (se 1 (by rfl) ⟨1713164, by rfl⟩ : syracuseStep 2284219 = 3426329) B3426329
theorem B14635541 : Blo 2283435 14635541 := bbase (se 6 (by rfl) ⟨343020, by rfl⟩ : syracuseStep 14635541 = 686041) (by norm_num)
theorem B9757027 : Blo 2283435 9757027 := bstep (se 1 (by rfl) ⟨7317770, by rfl⟩ : syracuseStep 9757027 = 14635541) B14635541
theorem B13009369 : Blo 2283435 13009369 := bstep (se 2 (by rfl) ⟨4878513, by rfl⟩ : syracuseStep 13009369 = 9757027) B9757027
theorem B17345825 : Blo 2283435 17345825 := bstep (se 2 (by rfl) ⟨6504684, by rfl⟩ : syracuseStep 17345825 = 13009369) B13009369
theorem B11563883 : Blo 2283435 11563883 := bstep (se 1 (by rfl) ⟨8672912, by rfl⟩ : syracuseStep 11563883 = 17345825) B17345825
theorem B7709255 : Blo 2283435 7709255 := bstep (se 1 (by rfl) ⟨5781941, by rfl⟩ : syracuseStep 7709255 = 11563883) B11563883
theorem B5139503 : Blo 2283435 5139503 := bstep (se 1 (by rfl) ⟨3854627, by rfl⟩ : syracuseStep 5139503 = 7709255) B7709255
theorem B3426335 : Blo 2283435 3426335 := bstep (se 1 (by rfl) ⟨2569751, by rfl⟩ : syracuseStep 3426335 = 5139503) B5139503
theorem B2284223 : Blo 2283435 2284223 := bstep (se 1 (by rfl) ⟨1713167, by rfl⟩ : syracuseStep 2284223 = 3426335) B3426335
theorem B3426341 : Blo 2283435 3426341 := bbase (se 4 (by rfl) ⟨321219, by rfl⟩ : syracuseStep 3426341 = 642439) (by norm_num)
theorem B2284227 : Blo 2283435 2284227 := bstep (se 1 (by rfl) ⟨1713170, by rfl⟩ : syracuseStep 2284227 = 3426341) B3426341
theorem B2890981 : Blo 2283435 2890981 := bbase (se 4 (by rfl) ⟨271029, by rfl⟩ : syracuseStep 2890981 = 542059) (by norm_num)
theorem B3854641 : Blo 2283435 3854641 := bstep (se 2 (by rfl) ⟨1445490, by rfl⟩ : syracuseStep 3854641 = 2890981) B2890981
theorem B5139521 : Blo 2283435 5139521 := bstep (se 2 (by rfl) ⟨1927320, by rfl⟩ : syracuseStep 5139521 = 3854641) B3854641
theorem B3426347 : Blo 2283435 3426347 := bstep (se 1 (by rfl) ⟨2569760, by rfl⟩ : syracuseStep 3426347 = 5139521) B5139521
theorem B2284231 : Blo 2283435 2284231 := bstep (se 1 (by rfl) ⟨1713173, by rfl⟩ : syracuseStep 2284231 = 3426347) B3426347
theorem B2569765 : Blo 2283435 2569765 := bbase (se 4 (by rfl) ⟨240915, by rfl⟩ : syracuseStep 2569765 = 481831) (by norm_num)
theorem B3426353 : Blo 2283435 3426353 := bstep (se 2 (by rfl) ⟨1284882, by rfl⟩ : syracuseStep 3426353 = 2569765) B2569765
theorem B2284235 : Blo 2283435 2284235 := bstep (se 1 (by rfl) ⟨1713176, by rfl⟩ : syracuseStep 2284235 = 3426353) B3426353
theorem B4945109 : Blo 2283435 4945109 := bbase (se 7 (by rfl) ⟨57950, by rfl⟩ : syracuseStep 4945109 = 115901) (by norm_num)
theorem B13186957 : Blo 2283435 13186957 := bstep (se 3 (by rfl) ⟨2472554, by rfl⟩ : syracuseStep 13186957 = 4945109) B4945109
theorem B17582609 : Blo 2283435 17582609 := bstep (se 2 (by rfl) ⟨6593478, by rfl⟩ : syracuseStep 17582609 = 13186957) B13186957
theorem B46886957 : Blo 2283435 46886957 := bstep (se 3 (by rfl) ⟨8791304, by rfl⟩ : syracuseStep 46886957 = 17582609) B17582609
theorem B31257971 : Blo 2283435 31257971 := bstep (se 1 (by rfl) ⟨23443478, by rfl⟩ : syracuseStep 31257971 = 46886957) B46886957
theorem B20838647 : Blo 2283435 20838647 := bstep (se 1 (by rfl) ⟨15628985, by rfl⟩ : syracuseStep 20838647 = 31257971) B31257971
theorem B55569725 : Blo 2283435 55569725 := bstep (se 3 (by rfl) ⟨10419323, by rfl⟩ : syracuseStep 55569725 = 20838647) B20838647
theorem B37046483 : Blo 2283435 37046483 := bstep (se 1 (by rfl) ⟨27784862, by rfl⟩ : syracuseStep 37046483 = 55569725) B55569725
theorem B24697655 : Blo 2283435 24697655 := bstep (se 1 (by rfl) ⟨18523241, by rfl⟩ : syracuseStep 24697655 = 37046483) B37046483
theorem B16465103 : Blo 2283435 16465103 := bstep (se 1 (by rfl) ⟨12348827, by rfl⟩ : syracuseStep 16465103 = 24697655) B24697655
theorem B10976735 : Blo 2283435 10976735 := bstep (se 1 (by rfl) ⟨8232551, by rfl⟩ : syracuseStep 10976735 = 16465103) B16465103
theorem B7317823 : Blo 2283435 7317823 := bstep (se 1 (by rfl) ⟨5488367, by rfl⟩ : syracuseStep 7317823 = 10976735) B10976735
theorem B9757097 : Blo 2283435 9757097 := bstep (se 2 (by rfl) ⟨3658911, by rfl⟩ : syracuseStep 9757097 = 7317823) B7317823
theorem B6504731 : Blo 2283435 6504731 := bstep (se 1 (by rfl) ⟨4878548, by rfl⟩ : syracuseStep 6504731 = 9757097) B9757097
theorem B4336487 : Blo 2283435 4336487 := bstep (se 1 (by rfl) ⟨3252365, by rfl⟩ : syracuseStep 4336487 = 6504731) B6504731
theorem B2890991 : Blo 2283435 2890991 := bstep (se 1 (by rfl) ⟨2168243, by rfl⟩ : syracuseStep 2890991 = 4336487) B4336487
theorem B7709309 : Blo 2283435 7709309 := bstep (se 3 (by rfl) ⟨1445495, by rfl⟩ : syracuseStep 7709309 = 2890991) B2890991
theorem B5139539 : Blo 2283435 5139539 := bstep (se 1 (by rfl) ⟨3854654, by rfl⟩ : syracuseStep 5139539 = 7709309) B7709309
theorem B3426359 : Blo 2283435 3426359 := bstep (se 1 (by rfl) ⟨2569769, by rfl⟩ : syracuseStep 3426359 = 5139539) B5139539
theorem B2284239 : Blo 2283435 2284239 := bstep (se 1 (by rfl) ⟨1713179, by rfl⟩ : syracuseStep 2284239 = 3426359) B3426359
theorem B3426365 : Blo 2283435 3426365 := bbase (se 3 (by rfl) ⟨642443, by rfl⟩ : syracuseStep 3426365 = 1284887) (by norm_num)
theorem B2284243 : Blo 2283435 2284243 := bstep (se 1 (by rfl) ⟨1713182, by rfl⟩ : syracuseStep 2284243 = 3426365) B3426365
theorem B5139557 : Blo 2283435 5139557 := bbase (se 4 (by rfl) ⟨481833, by rfl⟩ : syracuseStep 5139557 = 963667) (by norm_num)
theorem B3426371 : Blo 2283435 3426371 := bstep (se 1 (by rfl) ⟨2569778, by rfl⟩ : syracuseStep 3426371 = 5139557) B5139557
theorem B2284247 : Blo 2283435 2284247 := bstep (se 1 (by rfl) ⟨1713185, by rfl⟩ : syracuseStep 2284247 = 3426371) B3426371
theorem B5782013 : Blo 2283435 5782013 := bbase (se 3 (by rfl) ⟨1084127, by rfl⟩ : syracuseStep 5782013 = 2168255) (by norm_num)
theorem B3854675 : Blo 2283435 3854675 := bstep (se 1 (by rfl) ⟨2891006, by rfl⟩ : syracuseStep 3854675 = 5782013) B5782013
theorem B2569783 : Blo 2283435 2569783 := bstep (se 1 (by rfl) ⟨1927337, by rfl⟩ : syracuseStep 2569783 = 3854675) B3854675
theorem B3426377 : Blo 2283435 3426377 := bstep (se 2 (by rfl) ⟨1284891, by rfl⟩ : syracuseStep 3426377 = 2569783) B2569783
theorem B2284251 : Blo 2283435 2284251 := bstep (se 1 (by rfl) ⟨1713188, by rfl⟩ : syracuseStep 2284251 = 3426377) B3426377
theorem B4336517 : Blo 2283435 4336517 := bbase (se 4 (by rfl) ⟨406548, by rfl⟩ : syracuseStep 4336517 = 813097) (by norm_num)
theorem B11564045 : Blo 2283435 11564045 := bstep (se 3 (by rfl) ⟨2168258, by rfl⟩ : syracuseStep 11564045 = 4336517) B4336517
theorem B7709363 : Blo 2283435 7709363 := bstep (se 1 (by rfl) ⟨5782022, by rfl⟩ : syracuseStep 7709363 = 11564045) B11564045
theorem B5139575 : Blo 2283435 5139575 := bstep (se 1 (by rfl) ⟨3854681, by rfl⟩ : syracuseStep 5139575 = 7709363) B7709363
theorem B3426383 : Blo 2283435 3426383 := bstep (se 1 (by rfl) ⟨2569787, by rfl⟩ : syracuseStep 3426383 = 5139575) B5139575
theorem B2284255 : Blo 2283435 2284255 := bstep (se 1 (by rfl) ⟨1713191, by rfl⟩ : syracuseStep 2284255 = 3426383) B3426383
theorem B3426389 : Blo 2283435 3426389 := bbase (se 8 (by rfl) ⟨20076, by rfl⟩ : syracuseStep 3426389 = 40153) (by norm_num)
theorem B2284259 : Blo 2283435 2284259 := bstep (se 1 (by rfl) ⟨1713194, by rfl⟩ : syracuseStep 2284259 = 3426389) B3426389
theorem B5209717 : Blo 2283435 5209717 := bbase (se 5 (by rfl) ⟨244205, by rfl⟩ : syracuseStep 5209717 = 488411) (by norm_num)
theorem B6946289 : Blo 2283435 6946289 := bstep (se 2 (by rfl) ⟨2604858, by rfl⟩ : syracuseStep 6946289 = 5209717) B5209717
theorem B4630859 : Blo 2283435 4630859 := bstep (se 1 (by rfl) ⟨3473144, by rfl⟩ : syracuseStep 4630859 = 6946289) B6946289
theorem B3087239 : Blo 2283435 3087239 := bstep (se 1 (by rfl) ⟨2315429, by rfl⟩ : syracuseStep 3087239 = 4630859) B4630859
theorem B32930549 : Blo 2283435 32930549 := bstep (se 5 (by rfl) ⟨1543619, by rfl⟩ : syracuseStep 32930549 = 3087239) B3087239
theorem B21953699 : Blo 2283435 21953699 := bstep (se 1 (by rfl) ⟨16465274, by rfl⟩ : syracuseStep 21953699 = 32930549) B32930549
theorem B14635799 : Blo 2283435 14635799 := bstep (se 1 (by rfl) ⟨10976849, by rfl⟩ : syracuseStep 14635799 = 21953699) B21953699
theorem B9757199 : Blo 2283435 9757199 := bstep (se 1 (by rfl) ⟨7317899, by rfl⟩ : syracuseStep 9757199 = 14635799) B14635799
theorem B6504799 : Blo 2283435 6504799 := bstep (se 1 (by rfl) ⟨4878599, by rfl⟩ : syracuseStep 6504799 = 9757199) B9757199
theorem B8673065 : Blo 2283435 8673065 := bstep (se 2 (by rfl) ⟨3252399, by rfl⟩ : syracuseStep 8673065 = 6504799) B6504799
theorem B5782043 : Blo 2283435 5782043 := bstep (se 1 (by rfl) ⟨4336532, by rfl⟩ : syracuseStep 5782043 = 8673065) B8673065
theorem B3854695 : Blo 2283435 3854695 := bstep (se 1 (by rfl) ⟨2891021, by rfl⟩ : syracuseStep 3854695 = 5782043) B5782043
theorem B5139593 : Blo 2283435 5139593 := bstep (se 2 (by rfl) ⟨1927347, by rfl⟩ : syracuseStep 5139593 = 3854695) B3854695
theorem B3426395 : Blo 2283435 3426395 := bstep (se 1 (by rfl) ⟨2569796, by rfl⟩ : syracuseStep 3426395 = 5139593) B5139593
theorem B2284263 : Blo 2283435 2284263 := bstep (se 1 (by rfl) ⟨1713197, by rfl⟩ : syracuseStep 2284263 = 3426395) B3426395
theorem B2569801 : Blo 2283435 2569801 := bbase (se 2 (by rfl) ⟨963675, by rfl⟩ : syracuseStep 2569801 = 1927351) (by norm_num)
theorem B3426401 : Blo 2283435 3426401 := bstep (se 2 (by rfl) ⟨1284900, by rfl⟩ : syracuseStep 3426401 = 2569801) B2569801
theorem B2284267 : Blo 2283435 2284267 := bstep (se 1 (by rfl) ⟨1713200, by rfl⟩ : syracuseStep 2284267 = 3426401) B3426401
theorem B9261749 : Blo 2283435 9261749 := bbase (se 5 (by rfl) ⟨434144, by rfl⟩ : syracuseStep 9261749 = 868289) (by norm_num)
theorem B24697997 : Blo 2283435 24697997 := bstep (se 3 (by rfl) ⟨4630874, by rfl⟩ : syracuseStep 24697997 = 9261749) B9261749
theorem B16465331 : Blo 2283435 16465331 := bstep (se 1 (by rfl) ⟨12348998, by rfl⟩ : syracuseStep 16465331 = 24697997) B24697997
theorem B10976887 : Blo 2283435 10976887 := bstep (se 1 (by rfl) ⟨8232665, by rfl⟩ : syracuseStep 10976887 = 16465331) B16465331
theorem B14635849 : Blo 2283435 14635849 := bstep (se 2 (by rfl) ⟨5488443, by rfl⟩ : syracuseStep 14635849 = 10976887) B10976887
theorem B19514465 : Blo 2283435 19514465 := bstep (se 2 (by rfl) ⟨7317924, by rfl⟩ : syracuseStep 19514465 = 14635849) B14635849
theorem B13009643 : Blo 2283435 13009643 := bstep (se 1 (by rfl) ⟨9757232, by rfl⟩ : syracuseStep 13009643 = 19514465) B19514465
theorem B8673095 : Blo 2283435 8673095 := bstep (se 1 (by rfl) ⟨6504821, by rfl⟩ : syracuseStep 8673095 = 13009643) B13009643
theorem B5782063 : Blo 2283435 5782063 := bstep (se 1 (by rfl) ⟨4336547, by rfl⟩ : syracuseStep 5782063 = 8673095) B8673095
theorem B7709417 : Blo 2283435 7709417 := bstep (se 2 (by rfl) ⟨2891031, by rfl⟩ : syracuseStep 7709417 = 5782063) B5782063
theorem B5139611 : Blo 2283435 5139611 := bstep (se 1 (by rfl) ⟨3854708, by rfl⟩ : syracuseStep 5139611 = 7709417) B7709417
theorem B3426407 : Blo 2283435 3426407 := bstep (se 1 (by rfl) ⟨2569805, by rfl⟩ : syracuseStep 3426407 = 5139611) B5139611
theorem B2284271 : Blo 2283435 2284271 := bstep (se 1 (by rfl) ⟨1713203, by rfl⟩ : syracuseStep 2284271 = 3426407) B3426407
theorem B3426413 : Blo 2283435 3426413 := bbase (se 3 (by rfl) ⟨642452, by rfl⟩ : syracuseStep 3426413 = 1284905) (by norm_num)
theorem B2284275 : Blo 2283435 2284275 := bstep (se 1 (by rfl) ⟨1713206, by rfl⟩ : syracuseStep 2284275 = 3426413) B3426413
theorem B5139629 : Blo 2283435 5139629 := bbase (se 3 (by rfl) ⟨963680, by rfl⟩ : syracuseStep 5139629 = 1927361) (by norm_num)
theorem B3426419 : Blo 2283435 3426419 := bstep (se 1 (by rfl) ⟨2569814, by rfl⟩ : syracuseStep 3426419 = 5139629) B5139629
theorem B2284279 : Blo 2283435 2284279 := bstep (se 1 (by rfl) ⟨1713209, by rfl⟩ : syracuseStep 2284279 = 3426419) B3426419
theorem B2744237 : Blo 2283435 2744237 := bbase (se 3 (by rfl) ⟨514544, by rfl⟩ : syracuseStep 2744237 = 1029089) (by norm_num)
theorem B7317965 : Blo 2283435 7317965 := bstep (se 3 (by rfl) ⟨1372118, by rfl⟩ : syracuseStep 7317965 = 2744237) B2744237
theorem B4878643 : Blo 2283435 4878643 := bstep (se 1 (by rfl) ⟨3658982, by rfl⟩ : syracuseStep 4878643 = 7317965) B7317965
theorem B6504857 : Blo 2283435 6504857 := bstep (se 2 (by rfl) ⟨2439321, by rfl⟩ : syracuseStep 6504857 = 4878643) B4878643
theorem B4336571 : Blo 2283435 4336571 := bstep (se 1 (by rfl) ⟨3252428, by rfl⟩ : syracuseStep 4336571 = 6504857) B6504857
theorem B2891047 : Blo 2283435 2891047 := bstep (se 1 (by rfl) ⟨2168285, by rfl⟩ : syracuseStep 2891047 = 4336571) B4336571
theorem B3854729 : Blo 2283435 3854729 := bstep (se 2 (by rfl) ⟨1445523, by rfl⟩ : syracuseStep 3854729 = 2891047) B2891047
theorem B2569819 : Blo 2283435 2569819 := bstep (se 1 (by rfl) ⟨1927364, by rfl⟩ : syracuseStep 2569819 = 3854729) B3854729
theorem B3426425 : Blo 2283435 3426425 := bstep (se 2 (by rfl) ⟨1284909, by rfl⟩ : syracuseStep 3426425 = 2569819) B2569819
theorem B2284283 : Blo 2283435 2284283 := bstep (se 1 (by rfl) ⟨1713212, by rfl⟩ : syracuseStep 2284283 = 3426425) B3426425
theorem B21123413 : Blo 2283435 21123413 := bbase (se 10 (by rfl) ⟨30942, by rfl⟩ : syracuseStep 21123413 = 61885) (by norm_num)
theorem B14082275 : Blo 2283435 14082275 := bstep (se 1 (by rfl) ⟨10561706, by rfl⟩ : syracuseStep 14082275 = 21123413) B21123413
theorem B9388183 : Blo 2283435 9388183 := bstep (se 1 (by rfl) ⟨7041137, by rfl⟩ : syracuseStep 9388183 = 14082275) B14082275
theorem B12517577 : Blo 2283435 12517577 := bstep (se 2 (by rfl) ⟨4694091, by rfl⟩ : syracuseStep 12517577 = 9388183) B9388183
theorem B8345051 : Blo 2283435 8345051 := bstep (se 1 (by rfl) ⟨6258788, by rfl⟩ : syracuseStep 8345051 = 12517577) B12517577
theorem B5563367 : Blo 2283435 5563367 := bstep (se 1 (by rfl) ⟨4172525, by rfl⟩ : syracuseStep 5563367 = 8345051) B8345051
theorem B3708911 : Blo 2283435 3708911 := bstep (se 1 (by rfl) ⟨2781683, by rfl⟩ : syracuseStep 3708911 = 5563367) B5563367
theorem B2472607 : Blo 2283435 2472607 := bstep (se 1 (by rfl) ⟨1854455, by rfl⟩ : syracuseStep 2472607 = 3708911) B3708911
theorem B3296809 : Blo 2283435 3296809 := bstep (se 2 (by rfl) ⟨1236303, by rfl⟩ : syracuseStep 3296809 = 2472607) B2472607
theorem B4395745 : Blo 2283435 4395745 := bstep (se 2 (by rfl) ⟨1648404, by rfl⟩ : syracuseStep 4395745 = 3296809) B3296809
theorem B5860993 : Blo 2283435 5860993 := bstep (se 2 (by rfl) ⟨2197872, by rfl⟩ : syracuseStep 5860993 = 4395745) B4395745
theorem B7814657 : Blo 2283435 7814657 := bstep (se 2 (by rfl) ⟨2930496, by rfl⟩ : syracuseStep 7814657 = 5860993) B5860993
theorem B5209771 : Blo 2283435 5209771 := bstep (se 1 (by rfl) ⟨3907328, by rfl⟩ : syracuseStep 5209771 = 7814657) B7814657
theorem B6946361 : Blo 2283435 6946361 := bstep (se 2 (by rfl) ⟨2604885, by rfl⟩ : syracuseStep 6946361 = 5209771) B5209771
theorem B4630907 : Blo 2283435 4630907 := bstep (se 1 (by rfl) ⟨3473180, by rfl⟩ : syracuseStep 4630907 = 6946361) B6946361
theorem B3087271 : Blo 2283435 3087271 := bstep (se 1 (by rfl) ⟨2315453, by rfl⟩ : syracuseStep 3087271 = 4630907) B4630907
theorem B16465445 : Blo 2283435 16465445 := bstep (se 4 (by rfl) ⟨1543635, by rfl⟩ : syracuseStep 16465445 = 3087271) B3087271
theorem B10976963 : Blo 2283435 10976963 := bstep (se 1 (by rfl) ⟨8232722, by rfl⟩ : syracuseStep 10976963 = 16465445) B16465445
theorem B29271901 : Blo 2283435 29271901 := bstep (se 3 (by rfl) ⟨5488481, by rfl⟩ : syracuseStep 29271901 = 10976963) B10976963
theorem B39029201 : Blo 2283435 39029201 := bstep (se 2 (by rfl) ⟨14635950, by rfl⟩ : syracuseStep 39029201 = 29271901) B29271901
theorem B26019467 : Blo 2283435 26019467 := bstep (se 1 (by rfl) ⟨19514600, by rfl⟩ : syracuseStep 26019467 = 39029201) B39029201
theorem B17346311 : Blo 2283435 17346311 := bstep (se 1 (by rfl) ⟨13009733, by rfl⟩ : syracuseStep 17346311 = 26019467) B26019467
theorem B11564207 : Blo 2283435 11564207 := bstep (se 1 (by rfl) ⟨8673155, by rfl⟩ : syracuseStep 11564207 = 17346311) B17346311
theorem B7709471 : Blo 2283435 7709471 := bstep (se 1 (by rfl) ⟨5782103, by rfl⟩ : syracuseStep 7709471 = 11564207) B11564207
theorem B5139647 : Blo 2283435 5139647 := bstep (se 1 (by rfl) ⟨3854735, by rfl⟩ : syracuseStep 5139647 = 7709471) B7709471
theorem B3426431 : Blo 2283435 3426431 := bstep (se 1 (by rfl) ⟨2569823, by rfl⟩ : syracuseStep 3426431 = 5139647) B5139647
theorem B2284287 : Blo 2283435 2284287 := bstep (se 1 (by rfl) ⟨1713215, by rfl⟩ : syracuseStep 2284287 = 3426431) B3426431
theorem B3426437 : Blo 2283435 3426437 := bbase (se 4 (by rfl) ⟨321228, by rfl⟩ : syracuseStep 3426437 = 642457) (by norm_num)
theorem B2284291 : Blo 2283435 2284291 := bstep (se 1 (by rfl) ⟨1713218, by rfl⟩ : syracuseStep 2284291 = 3426437) B3426437
theorem B3854749 : Blo 2283435 3854749 := bbase (se 3 (by rfl) ⟨722765, by rfl⟩ : syracuseStep 3854749 = 1445531) (by norm_num)
theorem B5139665 : Blo 2283435 5139665 := bstep (se 2 (by rfl) ⟨1927374, by rfl⟩ : syracuseStep 5139665 = 3854749) B3854749
theorem B3426443 : Blo 2283435 3426443 := bstep (se 1 (by rfl) ⟨2569832, by rfl⟩ : syracuseStep 3426443 = 5139665) B5139665
theorem B2284295 : Blo 2283435 2284295 := bstep (se 1 (by rfl) ⟨1713221, by rfl⟩ : syracuseStep 2284295 = 3426443) B3426443
theorem B2569837 : Blo 2283435 2569837 := bbase (se 3 (by rfl) ⟨481844, by rfl⟩ : syracuseStep 2569837 = 963689) (by norm_num)
theorem B3426449 : Blo 2283435 3426449 := bstep (se 2 (by rfl) ⟨1284918, by rfl⟩ : syracuseStep 3426449 = 2569837) B2569837
theorem B2284299 : Blo 2283435 2284299 := bstep (se 1 (by rfl) ⟨1713224, by rfl⟩ : syracuseStep 2284299 = 3426449) B3426449
theorem B7709525 : Blo 2283435 7709525 := bbase (se 9 (by rfl) ⟨22586, by rfl⟩ : syracuseStep 7709525 = 45173) (by norm_num)
theorem B5139683 : Blo 2283435 5139683 := bstep (se 1 (by rfl) ⟨3854762, by rfl⟩ : syracuseStep 5139683 = 7709525) B7709525
theorem B3426455 : Blo 2283435 3426455 := bstep (se 1 (by rfl) ⟨2569841, by rfl⟩ : syracuseStep 3426455 = 5139683) B5139683
theorem B2284303 : Blo 2283435 2284303 := bstep (se 1 (by rfl) ⟨1713227, by rfl⟩ : syracuseStep 2284303 = 3426455) B3426455
theorem B3426461 : Blo 2283435 3426461 := bbase (se 3 (by rfl) ⟨642461, by rfl⟩ : syracuseStep 3426461 = 1284923) (by norm_num)
theorem B2284307 : Blo 2283435 2284307 := bstep (se 1 (by rfl) ⟨1713230, by rfl⟩ : syracuseStep 2284307 = 3426461) B3426461
theorem B5139701 : Blo 2283435 5139701 := bbase (se 5 (by rfl) ⟨240923, by rfl⟩ : syracuseStep 5139701 = 481847) (by norm_num)
theorem B3426467 : Blo 2283435 3426467 := bstep (se 1 (by rfl) ⟨2569850, by rfl⟩ : syracuseStep 3426467 = 5139701) B5139701
theorem B2284311 : Blo 2283435 2284311 := bstep (se 1 (by rfl) ⟨1713233, by rfl⟩ : syracuseStep 2284311 = 3426467) B3426467
theorem B49396949 : Blo 2283435 49396949 := bbase (se 7 (by rfl) ⟨578870, by rfl⟩ : syracuseStep 49396949 = 1157741) (by norm_num)
theorem B32931299 : Blo 2283435 32931299 := bstep (se 1 (by rfl) ⟨24698474, by rfl⟩ : syracuseStep 32931299 = 49396949) B49396949
theorem B21954199 : Blo 2283435 21954199 := bstep (se 1 (by rfl) ⟨16465649, by rfl⟩ : syracuseStep 21954199 = 32931299) B32931299
theorem B29272265 : Blo 2283435 29272265 := bstep (se 2 (by rfl) ⟨10977099, by rfl⟩ : syracuseStep 29272265 = 21954199) B21954199
theorem B19514843 : Blo 2283435 19514843 := bstep (se 1 (by rfl) ⟨14636132, by rfl⟩ : syracuseStep 19514843 = 29272265) B29272265
theorem B13009895 : Blo 2283435 13009895 := bstep (se 1 (by rfl) ⟨9757421, by rfl⟩ : syracuseStep 13009895 = 19514843) B19514843
theorem B8673263 : Blo 2283435 8673263 := bstep (se 1 (by rfl) ⟨6504947, by rfl⟩ : syracuseStep 8673263 = 13009895) B13009895
theorem B5782175 : Blo 2283435 5782175 := bstep (se 1 (by rfl) ⟨4336631, by rfl⟩ : syracuseStep 5782175 = 8673263) B8673263
theorem B3854783 : Blo 2283435 3854783 := bstep (se 1 (by rfl) ⟨2891087, by rfl⟩ : syracuseStep 3854783 = 5782175) B5782175
theorem B2569855 : Blo 2283435 2569855 := bstep (se 1 (by rfl) ⟨1927391, by rfl⟩ : syracuseStep 2569855 = 3854783) B3854783
theorem B3426473 : Blo 2283435 3426473 := bstep (se 2 (by rfl) ⟨1284927, by rfl⟩ : syracuseStep 3426473 = 2569855) B2569855
theorem B2284315 : Blo 2283435 2284315 := bstep (se 1 (by rfl) ⟨1713236, by rfl⟩ : syracuseStep 2284315 = 3426473) B3426473
theorem B55571669 : Blo 2283435 55571669 := bbase (se 7 (by rfl) ⟨651230, by rfl⟩ : syracuseStep 55571669 = 1302461) (by norm_num)
theorem B37047779 : Blo 2283435 37047779 := bstep (se 1 (by rfl) ⟨27785834, by rfl⟩ : syracuseStep 37047779 = 55571669) B55571669
theorem B24698519 : Blo 2283435 24698519 := bstep (se 1 (by rfl) ⟨18523889, by rfl⟩ : syracuseStep 24698519 = 37047779) B37047779
theorem B16465679 : Blo 2283435 16465679 := bstep (se 1 (by rfl) ⟨12349259, by rfl⟩ : syracuseStep 16465679 = 24698519) B24698519
theorem B10977119 : Blo 2283435 10977119 := bstep (se 1 (by rfl) ⟨8232839, by rfl⟩ : syracuseStep 10977119 = 16465679) B16465679
theorem B7318079 : Blo 2283435 7318079 := bstep (se 1 (by rfl) ⟨5488559, by rfl⟩ : syracuseStep 7318079 = 10977119) B10977119
theorem B4878719 : Blo 2283435 4878719 := bstep (se 1 (by rfl) ⟨3659039, by rfl⟩ : syracuseStep 4878719 = 7318079) B7318079
theorem B3252479 : Blo 2283435 3252479 := bstep (se 1 (by rfl) ⟨2439359, by rfl⟩ : syracuseStep 3252479 = 4878719) B4878719
theorem B8673277 : Blo 2283435 8673277 := bstep (se 3 (by rfl) ⟨1626239, by rfl⟩ : syracuseStep 8673277 = 3252479) B3252479
theorem B11564369 : Blo 2283435 11564369 := bstep (se 2 (by rfl) ⟨4336638, by rfl⟩ : syracuseStep 11564369 = 8673277) B8673277
theorem B7709579 : Blo 2283435 7709579 := bstep (se 1 (by rfl) ⟨5782184, by rfl⟩ : syracuseStep 7709579 = 11564369) B11564369
theorem B5139719 : Blo 2283435 5139719 := bstep (se 1 (by rfl) ⟨3854789, by rfl⟩ : syracuseStep 5139719 = 7709579) B7709579
theorem B3426479 : Blo 2283435 3426479 := bstep (se 1 (by rfl) ⟨2569859, by rfl⟩ : syracuseStep 3426479 = 5139719) B5139719
theorem B2284319 : Blo 2283435 2284319 := bstep (se 1 (by rfl) ⟨1713239, by rfl⟩ : syracuseStep 2284319 = 3426479) B3426479
theorem B3426485 : Blo 2283435 3426485 := bbase (se 5 (by rfl) ⟨160616, by rfl⟩ : syracuseStep 3426485 = 321233) (by norm_num)
theorem B2284323 : Blo 2283435 2284323 := bstep (se 1 (by rfl) ⟨1713242, by rfl⟩ : syracuseStep 2284323 = 3426485) B3426485
theorem B5782205 : Blo 2283435 5782205 := bbase (se 3 (by rfl) ⟨1084163, by rfl⟩ : syracuseStep 5782205 = 2168327) (by norm_num)
theorem B3854803 : Blo 2283435 3854803 := bstep (se 1 (by rfl) ⟨2891102, by rfl⟩ : syracuseStep 3854803 = 5782205) B5782205
theorem B5139737 : Blo 2283435 5139737 := bstep (se 2 (by rfl) ⟨1927401, by rfl⟩ : syracuseStep 5139737 = 3854803) B3854803
theorem B3426491 : Blo 2283435 3426491 := bstep (se 1 (by rfl) ⟨2569868, by rfl⟩ : syracuseStep 3426491 = 5139737) B5139737
theorem B2284327 : Blo 2283435 2284327 := bstep (se 1 (by rfl) ⟨1713245, by rfl⟩ : syracuseStep 2284327 = 3426491) B3426491
theorem B2569873 : Blo 2283435 2569873 := bbase (se 2 (by rfl) ⟨963702, by rfl⟩ : syracuseStep 2569873 = 1927405) (by norm_num)
theorem B3426497 : Blo 2283435 3426497 := bstep (se 2 (by rfl) ⟨1284936, by rfl⟩ : syracuseStep 3426497 = 2569873) B2569873
theorem B2284331 : Blo 2283435 2284331 := bstep (se 1 (by rfl) ⟨1713248, by rfl⟩ : syracuseStep 2284331 = 3426497) B3426497
theorem B4336669 : Blo 2283435 4336669 := bbase (se 3 (by rfl) ⟨813125, by rfl⟩ : syracuseStep 4336669 = 1626251) (by norm_num)
theorem B5782225 : Blo 2283435 5782225 := bstep (se 2 (by rfl) ⟨2168334, by rfl⟩ : syracuseStep 5782225 = 4336669) B4336669
theorem B7709633 : Blo 2283435 7709633 := bstep (se 2 (by rfl) ⟨2891112, by rfl⟩ : syracuseStep 7709633 = 5782225) B5782225
theorem B5139755 : Blo 2283435 5139755 := bstep (se 1 (by rfl) ⟨3854816, by rfl⟩ : syracuseStep 5139755 = 7709633) B7709633
theorem B3426503 : Blo 2283435 3426503 := bstep (se 1 (by rfl) ⟨2569877, by rfl⟩ : syracuseStep 3426503 = 5139755) B5139755
theorem B2284335 : Blo 2283435 2284335 := bstep (se 1 (by rfl) ⟨1713251, by rfl⟩ : syracuseStep 2284335 = 3426503) B3426503
theorem B3426509 : Blo 2283435 3426509 := bbase (se 3 (by rfl) ⟨642470, by rfl⟩ : syracuseStep 3426509 = 1284941) (by norm_num)
theorem B2284339 : Blo 2283435 2284339 := bstep (se 1 (by rfl) ⟨1713254, by rfl⟩ : syracuseStep 2284339 = 3426509) B3426509
theorem B5139773 : Blo 2283435 5139773 := bbase (se 3 (by rfl) ⟨963707, by rfl⟩ : syracuseStep 5139773 = 1927415) (by norm_num)
theorem B3426515 : Blo 2283435 3426515 := bstep (se 1 (by rfl) ⟨2569886, by rfl⟩ : syracuseStep 3426515 = 5139773) B5139773
theorem B2284343 : Blo 2283435 2284343 := bstep (se 1 (by rfl) ⟨1713257, by rfl⟩ : syracuseStep 2284343 = 3426515) B3426515
theorem B3854837 : Blo 2283435 3854837 := bbase (se 5 (by rfl) ⟨180695, by rfl⟩ : syracuseStep 3854837 = 361391) (by norm_num)
theorem B2569891 : Blo 2283435 2569891 := bstep (se 1 (by rfl) ⟨1927418, by rfl⟩ : syracuseStep 2569891 = 3854837) B3854837
theorem B3426521 : Blo 2283435 3426521 := bstep (se 2 (by rfl) ⟨1284945, by rfl⟩ : syracuseStep 3426521 = 2569891) B2569891
theorem B2284347 : Blo 2283435 2284347 := bstep (se 1 (by rfl) ⟨1713260, by rfl⟩ : syracuseStep 2284347 = 3426521) B3426521
theorem B7318181 : Blo 2283435 7318181 := bbase (se 4 (by rfl) ⟨686079, by rfl⟩ : syracuseStep 7318181 = 1372159) (by norm_num)
theorem B4878787 : Blo 2283435 4878787 := bstep (se 1 (by rfl) ⟨3659090, by rfl⟩ : syracuseStep 4878787 = 7318181) B7318181
theorem B6505049 : Blo 2283435 6505049 := bstep (se 2 (by rfl) ⟨2439393, by rfl⟩ : syracuseStep 6505049 = 4878787) B4878787
theorem B17346797 : Blo 2283435 17346797 := bstep (se 3 (by rfl) ⟨3252524, by rfl⟩ : syracuseStep 17346797 = 6505049) B6505049
theorem B11564531 : Blo 2283435 11564531 := bstep (se 1 (by rfl) ⟨8673398, by rfl⟩ : syracuseStep 11564531 = 17346797) B17346797
theorem B7709687 : Blo 2283435 7709687 := bstep (se 1 (by rfl) ⟨5782265, by rfl⟩ : syracuseStep 7709687 = 11564531) B11564531
theorem B5139791 : Blo 2283435 5139791 := bstep (se 1 (by rfl) ⟨3854843, by rfl⟩ : syracuseStep 5139791 = 7709687) B7709687
theorem B3426527 : Blo 2283435 3426527 := bstep (se 1 (by rfl) ⟨2569895, by rfl⟩ : syracuseStep 3426527 = 5139791) B5139791
theorem B2284351 : Blo 2283435 2284351 := bstep (se 1 (by rfl) ⟨1713263, by rfl⟩ : syracuseStep 2284351 = 3426527) B3426527
theorem B3426533 : Blo 2283435 3426533 := bbase (se 4 (by rfl) ⟨321237, by rfl⟩ : syracuseStep 3426533 = 642475) (by norm_num)
theorem B2284355 : Blo 2283435 2284355 := bstep (se 1 (by rfl) ⟨1713266, by rfl⟩ : syracuseStep 2284355 = 3426533) B3426533
theorem B4878805 : Blo 2283435 4878805 := bbase (se 7 (by rfl) ⟨57173, by rfl⟩ : syracuseStep 4878805 = 114347) (by norm_num)
theorem B6505073 : Blo 2283435 6505073 := bstep (se 2 (by rfl) ⟨2439402, by rfl⟩ : syracuseStep 6505073 = 4878805) B4878805
theorem B4336715 : Blo 2283435 4336715 := bstep (se 1 (by rfl) ⟨3252536, by rfl⟩ : syracuseStep 4336715 = 6505073) B6505073
theorem B2891143 : Blo 2283435 2891143 := bstep (se 1 (by rfl) ⟨2168357, by rfl⟩ : syracuseStep 2891143 = 4336715) B4336715
theorem B3854857 : Blo 2283435 3854857 := bstep (se 2 (by rfl) ⟨1445571, by rfl⟩ : syracuseStep 3854857 = 2891143) B2891143
theorem B5139809 : Blo 2283435 5139809 := bstep (se 2 (by rfl) ⟨1927428, by rfl⟩ : syracuseStep 5139809 = 3854857) B3854857
theorem B3426539 : Blo 2283435 3426539 := bstep (se 1 (by rfl) ⟨2569904, by rfl⟩ : syracuseStep 3426539 = 5139809) B5139809
theorem B2284359 : Blo 2283435 2284359 := bstep (se 1 (by rfl) ⟨1713269, by rfl⟩ : syracuseStep 2284359 = 3426539) B3426539
theorem B2569909 : Blo 2283435 2569909 := bbase (se 5 (by rfl) ⟨120464, by rfl⟩ : syracuseStep 2569909 = 240929) (by norm_num)
theorem B3426545 : Blo 2283435 3426545 := bstep (se 2 (by rfl) ⟨1284954, by rfl⟩ : syracuseStep 3426545 = 2569909) B2569909
theorem B2284363 : Blo 2283435 2284363 := bstep (se 1 (by rfl) ⟨1713272, by rfl⟩ : syracuseStep 2284363 = 3426545) B3426545
theorem B2891153 : Blo 2283435 2891153 := bbase (se 2 (by rfl) ⟨1084182, by rfl⟩ : syracuseStep 2891153 = 2168365) (by norm_num)
theorem B7709741 : Blo 2283435 7709741 := bstep (se 3 (by rfl) ⟨1445576, by rfl⟩ : syracuseStep 7709741 = 2891153) B2891153
theorem B5139827 : Blo 2283435 5139827 := bstep (se 1 (by rfl) ⟨3854870, by rfl⟩ : syracuseStep 5139827 = 7709741) B7709741
theorem B3426551 : Blo 2283435 3426551 := bstep (se 1 (by rfl) ⟨2569913, by rfl⟩ : syracuseStep 3426551 = 5139827) B5139827
theorem B2284367 : Blo 2283435 2284367 := bstep (se 1 (by rfl) ⟨1713275, by rfl⟩ : syracuseStep 2284367 = 3426551) B3426551
theorem B3426557 : Blo 2283435 3426557 := bbase (se 3 (by rfl) ⟨642479, by rfl⟩ : syracuseStep 3426557 = 1284959) (by norm_num)
theorem B2284371 : Blo 2283435 2284371 := bstep (se 1 (by rfl) ⟨1713278, by rfl⟩ : syracuseStep 2284371 = 3426557) B3426557
theorem B5139845 : Blo 2283435 5139845 := bbase (se 4 (by rfl) ⟨481860, by rfl⟩ : syracuseStep 5139845 = 963721) (by norm_num)
theorem B3426563 : Blo 2283435 3426563 := bstep (se 1 (by rfl) ⟨2569922, by rfl⟩ : syracuseStep 3426563 = 5139845) B5139845
theorem B2284375 : Blo 2283435 2284375 := bstep (se 1 (by rfl) ⟨1713281, by rfl⟩ : syracuseStep 2284375 = 3426563) B3426563
theorem B3252565 : Blo 2283435 3252565 := bbase (se 10 (by rfl) ⟨4764, by rfl⟩ : syracuseStep 3252565 = 9529) (by norm_num)
theorem B4336753 : Blo 2283435 4336753 := bstep (se 2 (by rfl) ⟨1626282, by rfl⟩ : syracuseStep 4336753 = 3252565) B3252565
theorem B5782337 : Blo 2283435 5782337 := bstep (se 2 (by rfl) ⟨2168376, by rfl⟩ : syracuseStep 5782337 = 4336753) B4336753
theorem B3854891 : Blo 2283435 3854891 := bstep (se 1 (by rfl) ⟨2891168, by rfl⟩ : syracuseStep 3854891 = 5782337) B5782337
theorem B2569927 : Blo 2283435 2569927 := bstep (se 1 (by rfl) ⟨1927445, by rfl⟩ : syracuseStep 2569927 = 3854891) B3854891
theorem B3426569 : Blo 2283435 3426569 := bstep (se 2 (by rfl) ⟨1284963, by rfl⟩ : syracuseStep 3426569 = 2569927) B2569927
theorem B2284379 : Blo 2283435 2284379 := bstep (se 1 (by rfl) ⟨1713284, by rfl⟩ : syracuseStep 2284379 = 3426569) B3426569
theorem B11564693 : Blo 2283435 11564693 := bbase (se 6 (by rfl) ⟨271047, by rfl⟩ : syracuseStep 11564693 = 542095) (by norm_num)
theorem B7709795 : Blo 2283435 7709795 := bstep (se 1 (by rfl) ⟨5782346, by rfl⟩ : syracuseStep 7709795 = 11564693) B11564693
theorem B5139863 : Blo 2283435 5139863 := bstep (se 1 (by rfl) ⟨3854897, by rfl⟩ : syracuseStep 5139863 = 7709795) B7709795
theorem B3426575 : Blo 2283435 3426575 := bstep (se 1 (by rfl) ⟨2569931, by rfl⟩ : syracuseStep 3426575 = 5139863) B5139863
theorem B2284383 : Blo 2283435 2284383 := bstep (se 1 (by rfl) ⟨1713287, by rfl⟩ : syracuseStep 2284383 = 3426575) B3426575
theorem B3426581 : Blo 2283435 3426581 := bbase (se 6 (by rfl) ⟨80310, by rfl⟩ : syracuseStep 3426581 = 160621) (by norm_num)
theorem B2284387 : Blo 2283435 2284387 := bstep (se 1 (by rfl) ⟨1713290, by rfl⟩ : syracuseStep 2284387 = 3426581) B3426581
theorem B29273237 : Blo 2283435 29273237 := bbase (se 6 (by rfl) ⟨686091, by rfl⟩ : syracuseStep 29273237 = 1372183) (by norm_num)
theorem B19515491 : Blo 2283435 19515491 := bstep (se 1 (by rfl) ⟨14636618, by rfl⟩ : syracuseStep 19515491 = 29273237) B29273237
theorem B13010327 : Blo 2283435 13010327 := bstep (se 1 (by rfl) ⟨9757745, by rfl⟩ : syracuseStep 13010327 = 19515491) B19515491
theorem B8673551 : Blo 2283435 8673551 := bstep (se 1 (by rfl) ⟨6505163, by rfl⟩ : syracuseStep 8673551 = 13010327) B13010327
theorem B5782367 : Blo 2283435 5782367 := bstep (se 1 (by rfl) ⟨4336775, by rfl⟩ : syracuseStep 5782367 = 8673551) B8673551
theorem B3854911 : Blo 2283435 3854911 := bstep (se 1 (by rfl) ⟨2891183, by rfl⟩ : syracuseStep 3854911 = 5782367) B5782367
theorem B5139881 : Blo 2283435 5139881 := bstep (se 2 (by rfl) ⟨1927455, by rfl⟩ : syracuseStep 5139881 = 3854911) B3854911
theorem B3426587 : Blo 2283435 3426587 := bstep (se 1 (by rfl) ⟨2569940, by rfl⟩ : syracuseStep 3426587 = 5139881) B5139881
theorem B2284391 : Blo 2283435 2284391 := bstep (se 1 (by rfl) ⟨1713293, by rfl⟩ : syracuseStep 2284391 = 3426587) B3426587
theorem B2569945 : Blo 2283435 2569945 := bbase (se 2 (by rfl) ⟨963729, by rfl⟩ : syracuseStep 2569945 = 1927459) (by norm_num)
theorem B3426593 : Blo 2283435 3426593 := bstep (se 2 (by rfl) ⟨1284972, by rfl⟩ : syracuseStep 3426593 = 2569945) B2569945
theorem B2284395 : Blo 2283435 2284395 := bstep (se 1 (by rfl) ⟨1713296, by rfl⟩ : syracuseStep 2284395 = 3426593) B3426593
theorem B2439445 : Blo 2283435 2439445 := bbase (se 6 (by rfl) ⟨57174, by rfl⟩ : syracuseStep 2439445 = 114349) (by norm_num)
theorem B3252593 : Blo 2283435 3252593 := bstep (se 2 (by rfl) ⟨1219722, by rfl⟩ : syracuseStep 3252593 = 2439445) B2439445
theorem B8673581 : Blo 2283435 8673581 := bstep (se 3 (by rfl) ⟨1626296, by rfl⟩ : syracuseStep 8673581 = 3252593) B3252593
theorem B5782387 : Blo 2283435 5782387 := bstep (se 1 (by rfl) ⟨4336790, by rfl⟩ : syracuseStep 5782387 = 8673581) B8673581
theorem B7709849 : Blo 2283435 7709849 := bstep (se 2 (by rfl) ⟨2891193, by rfl⟩ : syracuseStep 7709849 = 5782387) B5782387
theorem B5139899 : Blo 2283435 5139899 := bstep (se 1 (by rfl) ⟨3854924, by rfl⟩ : syracuseStep 5139899 = 7709849) B7709849
theorem B3426599 : Blo 2283435 3426599 := bstep (se 1 (by rfl) ⟨2569949, by rfl⟩ : syracuseStep 3426599 = 5139899) B5139899
theorem B2284399 : Blo 2283435 2284399 := bstep (se 1 (by rfl) ⟨1713299, by rfl⟩ : syracuseStep 2284399 = 3426599) B3426599
theorem B3426605 : Blo 2283435 3426605 := bbase (se 3 (by rfl) ⟨642488, by rfl⟩ : syracuseStep 3426605 = 1284977) (by norm_num)
theorem B2284403 : Blo 2283435 2284403 := bstep (se 1 (by rfl) ⟨1713302, by rfl⟩ : syracuseStep 2284403 = 3426605) B3426605
theorem B5139917 : Blo 2283435 5139917 := bbase (se 3 (by rfl) ⟨963734, by rfl⟩ : syracuseStep 5139917 = 1927469) (by norm_num)
theorem B3426611 : Blo 2283435 3426611 := bstep (se 1 (by rfl) ⟨2569958, by rfl⟩ : syracuseStep 3426611 = 5139917) B5139917
theorem B2284407 : Blo 2283435 2284407 := bstep (se 1 (by rfl) ⟨1713305, by rfl⟩ : syracuseStep 2284407 = 3426611) B3426611
theorem B2891209 : Blo 2283435 2891209 := bbase (se 2 (by rfl) ⟨1084203, by rfl⟩ : syracuseStep 2891209 = 2168407) (by norm_num)
theorem B3854945 : Blo 2283435 3854945 := bstep (se 2 (by rfl) ⟨1445604, by rfl⟩ : syracuseStep 3854945 = 2891209) B2891209
theorem B2569963 : Blo 2283435 2569963 := bstep (se 1 (by rfl) ⟨1927472, by rfl⟩ : syracuseStep 2569963 = 3854945) B3854945
theorem B3426617 : Blo 2283435 3426617 := bstep (se 2 (by rfl) ⟨1284981, by rfl⟩ : syracuseStep 3426617 = 2569963) B2569963
theorem B2284411 : Blo 2283435 2284411 := bstep (se 1 (by rfl) ⟨1713308, by rfl⟩ : syracuseStep 2284411 = 3426617) B3426617
theorem B21955157 : Blo 2283435 21955157 := bbase (se 8 (by rfl) ⟨128643, by rfl⟩ : syracuseStep 21955157 = 257287) (by norm_num)
theorem B14636771 : Blo 2283435 14636771 := bstep (se 1 (by rfl) ⟨10977578, by rfl⟩ : syracuseStep 14636771 = 21955157) B21955157
theorem B9757847 : Blo 2283435 9757847 := bstep (se 1 (by rfl) ⟨7318385, by rfl⟩ : syracuseStep 9757847 = 14636771) B14636771
theorem B26020925 : Blo 2283435 26020925 := bstep (se 3 (by rfl) ⟨4878923, by rfl⟩ : syracuseStep 26020925 = 9757847) B9757847
theorem B17347283 : Blo 2283435 17347283 := bstep (se 1 (by rfl) ⟨13010462, by rfl⟩ : syracuseStep 17347283 = 26020925) B26020925
theorem B11564855 : Blo 2283435 11564855 := bstep (se 1 (by rfl) ⟨8673641, by rfl⟩ : syracuseStep 11564855 = 17347283) B17347283
theorem B7709903 : Blo 2283435 7709903 := bstep (se 1 (by rfl) ⟨5782427, by rfl⟩ : syracuseStep 7709903 = 11564855) B11564855
theorem B5139935 : Blo 2283435 5139935 := bstep (se 1 (by rfl) ⟨3854951, by rfl⟩ : syracuseStep 5139935 = 7709903) B7709903
theorem B3426623 : Blo 2283435 3426623 := bstep (se 1 (by rfl) ⟨2569967, by rfl⟩ : syracuseStep 3426623 = 5139935) B5139935
theorem B2284415 : Blo 2283435 2284415 := bstep (se 1 (by rfl) ⟨1713311, by rfl⟩ : syracuseStep 2284415 = 3426623) B3426623
theorem B3426629 : Blo 2283435 3426629 := bbase (se 4 (by rfl) ⟨321246, by rfl⟩ : syracuseStep 3426629 = 642493) (by norm_num)
theorem B2284419 : Blo 2283435 2284419 := bstep (se 1 (by rfl) ⟨1713314, by rfl⟩ : syracuseStep 2284419 = 3426629) B3426629
theorem B3854965 : Blo 2283435 3854965 := bbase (se 5 (by rfl) ⟨180701, by rfl⟩ : syracuseStep 3854965 = 361403) (by norm_num)
theorem B5139953 : Blo 2283435 5139953 := bstep (se 2 (by rfl) ⟨1927482, by rfl⟩ : syracuseStep 5139953 = 3854965) B3854965
theorem B3426635 : Blo 2283435 3426635 := bstep (se 1 (by rfl) ⟨2569976, by rfl⟩ : syracuseStep 3426635 = 5139953) B5139953
theorem B2284423 : Blo 2283435 2284423 := bstep (se 1 (by rfl) ⟨1713317, by rfl⟩ : syracuseStep 2284423 = 3426635) B3426635
theorem B2569981 : Blo 2283435 2569981 := bbase (se 3 (by rfl) ⟨481871, by rfl⟩ : syracuseStep 2569981 = 963743) (by norm_num)
theorem B3426641 : Blo 2283435 3426641 := bstep (se 2 (by rfl) ⟨1284990, by rfl⟩ : syracuseStep 3426641 = 2569981) B2569981
theorem B2284427 : Blo 2283435 2284427 := bstep (se 1 (by rfl) ⟨1713320, by rfl⟩ : syracuseStep 2284427 = 3426641) B3426641
theorem B7709957 : Blo 2283435 7709957 := bbase (se 4 (by rfl) ⟨722808, by rfl⟩ : syracuseStep 7709957 = 1445617) (by norm_num)
theorem B5139971 : Blo 2283435 5139971 := bstep (se 1 (by rfl) ⟨3854978, by rfl⟩ : syracuseStep 5139971 = 7709957) B7709957
theorem B3426647 : Blo 2283435 3426647 := bstep (se 1 (by rfl) ⟨2569985, by rfl⟩ : syracuseStep 3426647 = 5139971) B5139971
theorem B2284431 : Blo 2283435 2284431 := bstep (se 1 (by rfl) ⟨1713323, by rfl⟩ : syracuseStep 2284431 = 3426647) B3426647
theorem B3426653 : Blo 2283435 3426653 := bbase (se 3 (by rfl) ⟨642497, by rfl⟩ : syracuseStep 3426653 = 1284995) (by norm_num)
theorem B2284435 : Blo 2283435 2284435 := bstep (se 1 (by rfl) ⟨1713326, by rfl⟩ : syracuseStep 2284435 = 3426653) B3426653
theorem B5139989 : Blo 2283435 5139989 := bbase (se 6 (by rfl) ⟨120468, by rfl⟩ : syracuseStep 5139989 = 240937) (by norm_num)
theorem B3426659 : Blo 2283435 3426659 := bstep (se 1 (by rfl) ⟨2569994, by rfl⟩ : syracuseStep 3426659 = 5139989) B5139989
theorem B2284439 : Blo 2283435 2284439 := bstep (se 1 (by rfl) ⟨1713329, by rfl⟩ : syracuseStep 2284439 = 3426659) B3426659
theorem B8673749 : Blo 2283435 8673749 := bbase (se 7 (by rfl) ⟨101645, by rfl⟩ : syracuseStep 8673749 = 203291) (by norm_num)
theorem B5782499 : Blo 2283435 5782499 := bstep (se 1 (by rfl) ⟨4336874, by rfl⟩ : syracuseStep 5782499 = 8673749) B8673749
theorem B3854999 : Blo 2283435 3854999 := bstep (se 1 (by rfl) ⟨2891249, by rfl⟩ : syracuseStep 3854999 = 5782499) B5782499
theorem B2569999 : Blo 2283435 2569999 := bstep (se 1 (by rfl) ⟨1927499, by rfl⟩ : syracuseStep 2569999 = 3854999) B3854999
theorem B3426665 : Blo 2283435 3426665 := bstep (se 2 (by rfl) ⟨1284999, by rfl⟩ : syracuseStep 3426665 = 2569999) B2569999
theorem B2284443 : Blo 2283435 2284443 := bstep (se 1 (by rfl) ⟨1713332, by rfl⟩ : syracuseStep 2284443 = 3426665) B3426665
theorem B13010645 : Blo 2283435 13010645 := bbase (se 7 (by rfl) ⟨152468, by rfl⟩ : syracuseStep 13010645 = 304937) (by norm_num)
theorem B8673763 : Blo 2283435 8673763 := bstep (se 1 (by rfl) ⟨6505322, by rfl⟩ : syracuseStep 8673763 = 13010645) B13010645
theorem B11565017 : Blo 2283435 11565017 := bstep (se 2 (by rfl) ⟨4336881, by rfl⟩ : syracuseStep 11565017 = 8673763) B8673763
theorem B7710011 : Blo 2283435 7710011 := bstep (se 1 (by rfl) ⟨5782508, by rfl⟩ : syracuseStep 7710011 = 11565017) B11565017
theorem B5140007 : Blo 2283435 5140007 := bstep (se 1 (by rfl) ⟨3855005, by rfl⟩ : syracuseStep 5140007 = 7710011) B7710011
theorem B3426671 : Blo 2283435 3426671 := bstep (se 1 (by rfl) ⟨2570003, by rfl⟩ : syracuseStep 3426671 = 5140007) B5140007
theorem B2284447 : Blo 2283435 2284447 := bstep (se 1 (by rfl) ⟨1713335, by rfl⟩ : syracuseStep 2284447 = 3426671) B3426671
theorem B3426677 : Blo 2283435 3426677 := bbase (se 5 (by rfl) ⟨160625, by rfl⟩ : syracuseStep 3426677 = 321251) (by norm_num)
theorem B2284451 : Blo 2283435 2284451 := bstep (se 1 (by rfl) ⟨1713338, by rfl⟩ : syracuseStep 2284451 = 3426677) B3426677
theorem B2439505 : Blo 2283435 2439505 := bbase (se 2 (by rfl) ⟨914814, by rfl⟩ : syracuseStep 2439505 = 1829629) (by norm_num)
theorem B3252673 : Blo 2283435 3252673 := bstep (se 2 (by rfl) ⟨1219752, by rfl⟩ : syracuseStep 3252673 = 2439505) B2439505
theorem B4336897 : Blo 2283435 4336897 := bstep (se 2 (by rfl) ⟨1626336, by rfl⟩ : syracuseStep 4336897 = 3252673) B3252673
theorem B5782529 : Blo 2283435 5782529 := bstep (se 2 (by rfl) ⟨2168448, by rfl⟩ : syracuseStep 5782529 = 4336897) B4336897
theorem B3855019 : Blo 2283435 3855019 := bstep (se 1 (by rfl) ⟨2891264, by rfl⟩ : syracuseStep 3855019 = 5782529) B5782529
theorem B5140025 : Blo 2283435 5140025 := bstep (se 2 (by rfl) ⟨1927509, by rfl⟩ : syracuseStep 5140025 = 3855019) B3855019
theorem B3426683 : Blo 2283435 3426683 := bstep (se 1 (by rfl) ⟨2570012, by rfl⟩ : syracuseStep 3426683 = 5140025) B5140025
theorem B2284455 : Blo 2283435 2284455 := bstep (se 1 (by rfl) ⟨1713341, by rfl⟩ : syracuseStep 2284455 = 3426683) B3426683
theorem B2570017 : Blo 2283435 2570017 := bbase (se 2 (by rfl) ⟨963756, by rfl⟩ : syracuseStep 2570017 = 1927513) (by norm_num)
theorem B3426689 : Blo 2283435 3426689 := bstep (se 2 (by rfl) ⟨1285008, by rfl⟩ : syracuseStep 3426689 = 2570017) B2570017
theorem B2284459 : Blo 2283435 2284459 := bstep (se 1 (by rfl) ⟨1713344, by rfl⟩ : syracuseStep 2284459 = 3426689) B3426689
theorem B5782549 : Blo 2283435 5782549 := bbase (se 6 (by rfl) ⟨135528, by rfl⟩ : syracuseStep 5782549 = 271057) (by norm_num)
theorem B7710065 : Blo 2283435 7710065 := bstep (se 2 (by rfl) ⟨2891274, by rfl⟩ : syracuseStep 7710065 = 5782549) B5782549
theorem B5140043 : Blo 2283435 5140043 := bstep (se 1 (by rfl) ⟨3855032, by rfl⟩ : syracuseStep 5140043 = 7710065) B7710065
theorem B3426695 : Blo 2283435 3426695 := bstep (se 1 (by rfl) ⟨2570021, by rfl⟩ : syracuseStep 3426695 = 5140043) B5140043
theorem B2284463 : Blo 2283435 2284463 := bstep (se 1 (by rfl) ⟨1713347, by rfl⟩ : syracuseStep 2284463 = 3426695) B3426695
theorem B3426701 : Blo 2283435 3426701 := bbase (se 3 (by rfl) ⟨642506, by rfl⟩ : syracuseStep 3426701 = 1285013) (by norm_num)
theorem B2284467 : Blo 2283435 2284467 := bstep (se 1 (by rfl) ⟨1713350, by rfl⟩ : syracuseStep 2284467 = 3426701) B3426701
theorem B5140061 : Blo 2283435 5140061 := bbase (se 3 (by rfl) ⟨963761, by rfl⟩ : syracuseStep 5140061 = 1927523) (by norm_num)
theorem B3426707 : Blo 2283435 3426707 := bstep (se 1 (by rfl) ⟨2570030, by rfl⟩ : syracuseStep 3426707 = 5140061) B5140061
theorem B2284471 : Blo 2283435 2284471 := bstep (se 1 (by rfl) ⟨1713353, by rfl⟩ : syracuseStep 2284471 = 3426707) B3426707
theorem B3855053 : Blo 2283435 3855053 := bbase (se 3 (by rfl) ⟨722822, by rfl⟩ : syracuseStep 3855053 = 1445645) (by norm_num)
theorem B2570035 : Blo 2283435 2570035 := bstep (se 1 (by rfl) ⟨1927526, by rfl⟩ : syracuseStep 2570035 = 3855053) B3855053
theorem B3426713 : Blo 2283435 3426713 := bstep (se 2 (by rfl) ⟨1285017, by rfl⟩ : syracuseStep 3426713 = 2570035) B2570035
theorem B2284475 : Blo 2283435 2284475 := bstep (se 1 (by rfl) ⟨1713356, by rfl⟩ : syracuseStep 2284475 = 3426713) B3426713
theorem B5861485 : Blo 2283435 5861485 := bbase (se 3 (by rfl) ⟨1099028, by rfl⟩ : syracuseStep 5861485 = 2198057) (by norm_num)
theorem B7815313 : Blo 2283435 7815313 := bstep (se 2 (by rfl) ⟨2930742, by rfl⟩ : syracuseStep 7815313 = 5861485) B5861485
theorem B10420417 : Blo 2283435 10420417 := bstep (se 2 (by rfl) ⟨3907656, by rfl⟩ : syracuseStep 10420417 = 7815313) B7815313
theorem B13893889 : Blo 2283435 13893889 := bstep (se 2 (by rfl) ⟨5210208, by rfl⟩ : syracuseStep 13893889 = 10420417) B10420417
theorem B18525185 : Blo 2283435 18525185 := bstep (se 2 (by rfl) ⟨6946944, by rfl⟩ : syracuseStep 18525185 = 13893889) B13893889
theorem B12350123 : Blo 2283435 12350123 := bstep (se 1 (by rfl) ⟨9262592, by rfl⟩ : syracuseStep 12350123 = 18525185) B18525185
theorem B8233415 : Blo 2283435 8233415 := bstep (se 1 (by rfl) ⟨6175061, by rfl⟩ : syracuseStep 8233415 = 12350123) B12350123
theorem B5488943 : Blo 2283435 5488943 := bstep (se 1 (by rfl) ⟨4116707, by rfl⟩ : syracuseStep 5488943 = 8233415) B8233415
theorem B14637181 : Blo 2283435 14637181 := bstep (se 3 (by rfl) ⟨2744471, by rfl⟩ : syracuseStep 14637181 = 5488943) B5488943
theorem B19516241 : Blo 2283435 19516241 := bstep (se 2 (by rfl) ⟨7318590, by rfl⟩ : syracuseStep 19516241 = 14637181) B14637181
theorem B13010827 : Blo 2283435 13010827 := bstep (se 1 (by rfl) ⟨9758120, by rfl⟩ : syracuseStep 13010827 = 19516241) B19516241
theorem B17347769 : Blo 2283435 17347769 := bstep (se 2 (by rfl) ⟨6505413, by rfl⟩ : syracuseStep 17347769 = 13010827) B13010827
theorem B11565179 : Blo 2283435 11565179 := bstep (se 1 (by rfl) ⟨8673884, by rfl⟩ : syracuseStep 11565179 = 17347769) B17347769
theorem B7710119 : Blo 2283435 7710119 := bstep (se 1 (by rfl) ⟨5782589, by rfl⟩ : syracuseStep 7710119 = 11565179) B11565179
theorem B5140079 : Blo 2283435 5140079 := bstep (se 1 (by rfl) ⟨3855059, by rfl⟩ : syracuseStep 5140079 = 7710119) B7710119
theorem B3426719 : Blo 2283435 3426719 := bstep (se 1 (by rfl) ⟨2570039, by rfl⟩ : syracuseStep 3426719 = 5140079) B5140079
theorem B2284479 : Blo 2283435 2284479 := bstep (se 1 (by rfl) ⟨1713359, by rfl⟩ : syracuseStep 2284479 = 3426719) B3426719
theorem B3426725 : Blo 2283435 3426725 := bbase (se 4 (by rfl) ⟨321255, by rfl⟩ : syracuseStep 3426725 = 642511) (by norm_num)
theorem B2284483 : Blo 2283435 2284483 := bstep (se 1 (by rfl) ⟨1713362, by rfl⟩ : syracuseStep 2284483 = 3426725) B3426725
theorem B2891305 : Blo 2283435 2891305 := bbase (se 2 (by rfl) ⟨1084239, by rfl⟩ : syracuseStep 2891305 = 2168479) (by norm_num)
theorem B3855073 : Blo 2283435 3855073 := bstep (se 2 (by rfl) ⟨1445652, by rfl⟩ : syracuseStep 3855073 = 2891305) B2891305
theorem B5140097 : Blo 2283435 5140097 := bstep (se 2 (by rfl) ⟨1927536, by rfl⟩ : syracuseStep 5140097 = 3855073) B3855073
theorem B3426731 : Blo 2283435 3426731 := bstep (se 1 (by rfl) ⟨2570048, by rfl⟩ : syracuseStep 3426731 = 5140097) B5140097
theorem B2284487 : Blo 2283435 2284487 := bstep (se 1 (by rfl) ⟨1713365, by rfl⟩ : syracuseStep 2284487 = 3426731) B3426731
theorem B2570053 : Blo 2283435 2570053 := bbase (se 4 (by rfl) ⟨240942, by rfl⟩ : syracuseStep 2570053 = 481885) (by norm_num)
theorem B3426737 : Blo 2283435 3426737 := bstep (se 2 (by rfl) ⟨1285026, by rfl⟩ : syracuseStep 3426737 = 2570053) B2570053
theorem B2284491 : Blo 2283435 2284491 := bstep (se 1 (by rfl) ⟨1713368, by rfl⟩ : syracuseStep 2284491 = 3426737) B3426737
theorem B4336973 : Blo 2283435 4336973 := bbase (se 3 (by rfl) ⟨813182, by rfl⟩ : syracuseStep 4336973 = 1626365) (by norm_num)
theorem B2891315 : Blo 2283435 2891315 := bstep (se 1 (by rfl) ⟨2168486, by rfl⟩ : syracuseStep 2891315 = 4336973) B4336973
theorem B7710173 : Blo 2283435 7710173 := bstep (se 3 (by rfl) ⟨1445657, by rfl⟩ : syracuseStep 7710173 = 2891315) B2891315
theorem B5140115 : Blo 2283435 5140115 := bstep (se 1 (by rfl) ⟨3855086, by rfl⟩ : syracuseStep 5140115 = 7710173) B7710173
theorem B3426743 : Blo 2283435 3426743 := bstep (se 1 (by rfl) ⟨2570057, by rfl⟩ : syracuseStep 3426743 = 5140115) B5140115
theorem B2284495 : Blo 2283435 2284495 := bstep (se 1 (by rfl) ⟨1713371, by rfl⟩ : syracuseStep 2284495 = 3426743) B3426743
theorem B3426749 : Blo 2283435 3426749 := bbase (se 3 (by rfl) ⟨642515, by rfl⟩ : syracuseStep 3426749 = 1285031) (by norm_num)
theorem B2284499 : Blo 2283435 2284499 := bstep (se 1 (by rfl) ⟨1713374, by rfl⟩ : syracuseStep 2284499 = 3426749) B3426749
theorem B5140133 : Blo 2283435 5140133 := bbase (se 4 (by rfl) ⟨481887, by rfl⟩ : syracuseStep 5140133 = 963775) (by norm_num)
theorem B3426755 : Blo 2283435 3426755 := bstep (se 1 (by rfl) ⟨2570066, by rfl⟩ : syracuseStep 3426755 = 5140133) B5140133
theorem B2284503 : Blo 2283435 2284503 := bstep (se 1 (by rfl) ⟨1713377, by rfl⟩ : syracuseStep 2284503 = 3426755) B3426755
theorem B5782661 : Blo 2283435 5782661 := bbase (se 4 (by rfl) ⟨542124, by rfl⟩ : syracuseStep 5782661 = 1084249) (by norm_num)
theorem B3855107 : Blo 2283435 3855107 := bstep (se 1 (by rfl) ⟨2891330, by rfl⟩ : syracuseStep 3855107 = 5782661) B5782661
theorem B2570071 : Blo 2283435 2570071 := bstep (se 1 (by rfl) ⟨1927553, by rfl⟩ : syracuseStep 2570071 = 3855107) B3855107
theorem B3426761 : Blo 2283435 3426761 := bstep (se 2 (by rfl) ⟨1285035, by rfl⟩ : syracuseStep 3426761 = 2570071) B2570071
theorem B2284507 : Blo 2283435 2284507 := bstep (se 1 (by rfl) ⟨1713380, by rfl⟩ : syracuseStep 2284507 = 3426761) B3426761
theorem B5489021 : Blo 2283435 5489021 := bbase (se 3 (by rfl) ⟨1029191, by rfl⟩ : syracuseStep 5489021 = 2058383) (by norm_num)
theorem B3659347 : Blo 2283435 3659347 := bstep (se 1 (by rfl) ⟨2744510, by rfl⟩ : syracuseStep 3659347 = 5489021) B5489021
theorem B4879129 : Blo 2283435 4879129 := bstep (se 2 (by rfl) ⟨1829673, by rfl⟩ : syracuseStep 4879129 = 3659347) B3659347
theorem B6505505 : Blo 2283435 6505505 := bstep (se 2 (by rfl) ⟨2439564, by rfl⟩ : syracuseStep 6505505 = 4879129) B4879129
theorem B4337003 : Blo 2283435 4337003 := bstep (se 1 (by rfl) ⟨3252752, by rfl⟩ : syracuseStep 4337003 = 6505505) B6505505
theorem B11565341 : Blo 2283435 11565341 := bstep (se 3 (by rfl) ⟨2168501, by rfl⟩ : syracuseStep 11565341 = 4337003) B4337003
theorem B7710227 : Blo 2283435 7710227 := bstep (se 1 (by rfl) ⟨5782670, by rfl⟩ : syracuseStep 7710227 = 11565341) B11565341
theorem B5140151 : Blo 2283435 5140151 := bstep (se 1 (by rfl) ⟨3855113, by rfl⟩ : syracuseStep 5140151 = 7710227) B7710227
theorem B3426767 : Blo 2283435 3426767 := bstep (se 1 (by rfl) ⟨2570075, by rfl⟩ : syracuseStep 3426767 = 5140151) B5140151
theorem B2284511 : Blo 2283435 2284511 := bstep (se 1 (by rfl) ⟨1713383, by rfl⟩ : syracuseStep 2284511 = 3426767) B3426767
theorem B3426773 : Blo 2283435 3426773 := bbase (se 7 (by rfl) ⟨40157, by rfl⟩ : syracuseStep 3426773 = 80315) (by norm_num)
theorem B2284515 : Blo 2283435 2284515 := bstep (se 1 (by rfl) ⟨1713386, by rfl⟩ : syracuseStep 2284515 = 3426773) B3426773
theorem B8674037 : Blo 2283435 8674037 := bbase (se 5 (by rfl) ⟨406595, by rfl⟩ : syracuseStep 8674037 = 813191) (by norm_num)
theorem B5782691 : Blo 2283435 5782691 := bstep (se 1 (by rfl) ⟨4337018, by rfl⟩ : syracuseStep 5782691 = 8674037) B8674037
theorem B3855127 : Blo 2283435 3855127 := bstep (se 1 (by rfl) ⟨2891345, by rfl⟩ : syracuseStep 3855127 = 5782691) B5782691
theorem B5140169 : Blo 2283435 5140169 := bstep (se 2 (by rfl) ⟨1927563, by rfl⟩ : syracuseStep 5140169 = 3855127) B3855127
theorem B3426779 : Blo 2283435 3426779 := bstep (se 1 (by rfl) ⟨2570084, by rfl⟩ : syracuseStep 3426779 = 5140169) B5140169
theorem B2284519 : Blo 2283435 2284519 := bstep (se 1 (by rfl) ⟨1713389, by rfl⟩ : syracuseStep 2284519 = 3426779) B3426779
theorem B2570089 : Blo 2283435 2570089 := bbase (se 2 (by rfl) ⟨963783, by rfl⟩ : syracuseStep 2570089 = 1927567) (by norm_num)
theorem B3426785 : Blo 2283435 3426785 := bstep (se 2 (by rfl) ⟨1285044, by rfl⟩ : syracuseStep 3426785 = 2570089) B2570089
theorem B2284523 : Blo 2283435 2284523 := bstep (se 1 (by rfl) ⟨1713392, by rfl⟩ : syracuseStep 2284523 = 3426785) B3426785
theorem B8233589 : Blo 2283435 8233589 := bbase (se 5 (by rfl) ⟨385949, by rfl⟩ : syracuseStep 8233589 = 771899) (by norm_num)
theorem B5489059 : Blo 2283435 5489059 := bstep (se 1 (by rfl) ⟨4116794, by rfl⟩ : syracuseStep 5489059 = 8233589) B8233589
theorem B7318745 : Blo 2283435 7318745 := bstep (se 2 (by rfl) ⟨2744529, by rfl⟩ : syracuseStep 7318745 = 5489059) B5489059
theorem B4879163 : Blo 2283435 4879163 := bstep (se 1 (by rfl) ⟨3659372, by rfl⟩ : syracuseStep 4879163 = 7318745) B7318745
theorem B13011101 : Blo 2283435 13011101 := bstep (se 3 (by rfl) ⟨2439581, by rfl⟩ : syracuseStep 13011101 = 4879163) B4879163
theorem B8674067 : Blo 2283435 8674067 := bstep (se 1 (by rfl) ⟨6505550, by rfl⟩ : syracuseStep 8674067 = 13011101) B13011101
theorem B5782711 : Blo 2283435 5782711 := bstep (se 1 (by rfl) ⟨4337033, by rfl⟩ : syracuseStep 5782711 = 8674067) B8674067
theorem B7710281 : Blo 2283435 7710281 := bstep (se 2 (by rfl) ⟨2891355, by rfl⟩ : syracuseStep 7710281 = 5782711) B5782711
theorem B5140187 : Blo 2283435 5140187 := bstep (se 1 (by rfl) ⟨3855140, by rfl⟩ : syracuseStep 5140187 = 7710281) B7710281
theorem B3426791 : Blo 2283435 3426791 := bstep (se 1 (by rfl) ⟨2570093, by rfl⟩ : syracuseStep 3426791 = 5140187) B5140187
theorem B2284527 : Blo 2283435 2284527 := bstep (se 1 (by rfl) ⟨1713395, by rfl⟩ : syracuseStep 2284527 = 3426791) B3426791
theorem B3426797 : Blo 2283435 3426797 := bbase (se 3 (by rfl) ⟨642524, by rfl⟩ : syracuseStep 3426797 = 1285049) (by norm_num)
theorem B2284531 : Blo 2283435 2284531 := bstep (se 1 (by rfl) ⟨1713398, by rfl⟩ : syracuseStep 2284531 = 3426797) B3426797
theorem B5140205 : Blo 2283435 5140205 := bbase (se 3 (by rfl) ⟨963788, by rfl⟩ : syracuseStep 5140205 = 1927577) (by norm_num)
theorem B3426803 : Blo 2283435 3426803 := bstep (se 1 (by rfl) ⟨2570102, by rfl⟩ : syracuseStep 3426803 = 5140205) B5140205
theorem B2284535 : Blo 2283435 2284535 := bstep (se 1 (by rfl) ⟨1713401, by rfl⟩ : syracuseStep 2284535 = 3426803) B3426803
theorem B2744545 : Blo 2283435 2744545 := bbase (se 2 (by rfl) ⟨1029204, by rfl⟩ : syracuseStep 2744545 = 2058409) (by norm_num)
theorem B3659393 : Blo 2283435 3659393 := bstep (se 2 (by rfl) ⟨1372272, by rfl⟩ : syracuseStep 3659393 = 2744545) B2744545
theorem B2439595 : Blo 2283435 2439595 := bstep (se 1 (by rfl) ⟨1829696, by rfl⟩ : syracuseStep 2439595 = 3659393) B3659393
theorem B3252793 : Blo 2283435 3252793 := bstep (se 2 (by rfl) ⟨1219797, by rfl⟩ : syracuseStep 3252793 = 2439595) B2439595
theorem B4337057 : Blo 2283435 4337057 := bstep (se 2 (by rfl) ⟨1626396, by rfl⟩ : syracuseStep 4337057 = 3252793) B3252793
theorem B2891371 : Blo 2283435 2891371 := bstep (se 1 (by rfl) ⟨2168528, by rfl⟩ : syracuseStep 2891371 = 4337057) B4337057
theorem B3855161 : Blo 2283435 3855161 := bstep (se 2 (by rfl) ⟨1445685, by rfl⟩ : syracuseStep 3855161 = 2891371) B2891371
theorem B2570107 : Blo 2283435 2570107 := bstep (se 1 (by rfl) ⟨1927580, by rfl⟩ : syracuseStep 2570107 = 3855161) B3855161
theorem B3426809 : Blo 2283435 3426809 := bstep (se 2 (by rfl) ⟨1285053, by rfl⟩ : syracuseStep 3426809 = 2570107) B2570107
theorem B2284539 : Blo 2283435 2284539 := bstep (se 1 (by rfl) ⟨1713404, by rfl⟩ : syracuseStep 2284539 = 3426809) B3426809
theorem B3811229 : Blo 2283435 3811229 := bbase (se 3 (by rfl) ⟨714605, by rfl⟩ : syracuseStep 3811229 = 1429211) (by norm_num)
theorem B162612437 : Blo 2283435 162612437 := bstep (se 7 (by rfl) ⟨1905614, by rfl⟩ : syracuseStep 162612437 = 3811229) B3811229
theorem B433633165 : Blo 2283435 433633165 := bstep (se 3 (by rfl) ⟨81306218, by rfl⟩ : syracuseStep 433633165 = 162612437) B162612437
theorem B2312710213 : Blo 2283435 2312710213 := bstep (se 4 (by rfl) ⟨216816582, by rfl⟩ : syracuseStep 2312710213 = 433633165) B433633165
theorem B3083613617 : Blo 2283435 3083613617 := bstep (se 2 (by rfl) ⟨1156355106, by rfl⟩ : syracuseStep 3083613617 = 2312710213) B2312710213
theorem B2055742411 : Blo 2283435 2055742411 := bstep (se 1 (by rfl) ⟨1541806808, by rfl⟩ : syracuseStep 2055742411 = 3083613617) B3083613617
theorem B2740989881 : Blo 2283435 2740989881 := bstep (se 2 (by rfl) ⟨1027871205, by rfl⟩ : syracuseStep 2740989881 = 2055742411) B2055742411
theorem B7309306349 : Blo 2283435 7309306349 := bstep (se 3 (by rfl) ⟨1370494940, by rfl⟩ : syracuseStep 7309306349 = 2740989881) B2740989881
theorem B4872870899 : Blo 2283435 4872870899 := bstep (se 1 (by rfl) ⟨3654653174, by rfl⟩ : syracuseStep 4872870899 = 7309306349) B7309306349
theorem B3248580599 : Blo 2283435 3248580599 := bstep (se 1 (by rfl) ⟨2436435449, by rfl⟩ : syracuseStep 3248580599 = 4872870899) B4872870899
theorem B2165720399 : Blo 2283435 2165720399 := bstep (se 1 (by rfl) ⟨1624290299, by rfl⟩ : syracuseStep 2165720399 = 3248580599) B3248580599
theorem B1443813599 : Blo 2283435 1443813599 := bstep (se 1 (by rfl) ⟨1082860199, by rfl⟩ : syracuseStep 1443813599 = 2165720399) B2165720399
theorem B962542399 : Blo 2283435 962542399 := bstep (se 1 (by rfl) ⟨721906799, by rfl⟩ : syracuseStep 962542399 = 1443813599) B1443813599
theorem B1283389865 : Blo 2283435 1283389865 := bstep (se 2 (by rfl) ⟨481271199, by rfl⟩ : syracuseStep 1283389865 = 962542399) B962542399
theorem B855593243 : Blo 2283435 855593243 := bstep (se 1 (by rfl) ⟨641694932, by rfl⟩ : syracuseStep 855593243 = 1283389865) B1283389865
theorem B570395495 : Blo 2283435 570395495 := bstep (se 1 (by rfl) ⟨427796621, by rfl⟩ : syracuseStep 570395495 = 855593243) B855593243
theorem B380263663 : Blo 2283435 380263663 := bstep (se 1 (by rfl) ⟨285197747, by rfl⟩ : syracuseStep 380263663 = 570395495) B570395495
theorem B507018217 : Blo 2283435 507018217 := bstep (se 2 (by rfl) ⟨190131831, by rfl⟩ : syracuseStep 507018217 = 380263663) B380263663
theorem B676024289 : Blo 2283435 676024289 := bstep (se 2 (by rfl) ⟨253509108, by rfl⟩ : syracuseStep 676024289 = 507018217) B507018217
theorem B450682859 : Blo 2283435 450682859 := bstep (se 1 (by rfl) ⟨338012144, by rfl⟩ : syracuseStep 450682859 = 676024289) B676024289
theorem B300455239 : Blo 2283435 300455239 := bstep (se 1 (by rfl) ⟨225341429, by rfl⟩ : syracuseStep 300455239 = 450682859) B450682859
theorem B400606985 : Blo 2283435 400606985 := bstep (se 2 (by rfl) ⟨150227619, by rfl⟩ : syracuseStep 400606985 = 300455239) B300455239
theorem B1068285293 : Blo 2283435 1068285293 := bstep (se 3 (by rfl) ⟨200303492, by rfl⟩ : syracuseStep 1068285293 = 400606985) B400606985
theorem B712190195 : Blo 2283435 712190195 := bstep (se 1 (by rfl) ⟨534142646, by rfl⟩ : syracuseStep 712190195 = 1068285293) B1068285293
theorem B474793463 : Blo 2283435 474793463 := bstep (se 1 (by rfl) ⟨356095097, by rfl⟩ : syracuseStep 474793463 = 712190195) B712190195
theorem B316528975 : Blo 2283435 316528975 := bstep (se 1 (by rfl) ⟨237396731, by rfl⟩ : syracuseStep 316528975 = 474793463) B474793463
theorem B422038633 : Blo 2283435 422038633 := bstep (se 2 (by rfl) ⟨158264487, by rfl⟩ : syracuseStep 422038633 = 316528975) B316528975
theorem B562718177 : Blo 2283435 562718177 := bstep (se 2 (by rfl) ⟨211019316, by rfl⟩ : syracuseStep 562718177 = 422038633) B422038633
theorem B375145451 : Blo 2283435 375145451 := bstep (se 1 (by rfl) ⟨281359088, by rfl⟩ : syracuseStep 375145451 = 562718177) B562718177
theorem B250096967 : Blo 2283435 250096967 := bstep (se 1 (by rfl) ⟨187572725, by rfl⟩ : syracuseStep 250096967 = 375145451) B375145451
theorem B166731311 : Blo 2283435 166731311 := bstep (se 1 (by rfl) ⟨125048483, by rfl⟩ : syracuseStep 166731311 = 250096967) B250096967
theorem B111154207 : Blo 2283435 111154207 := bstep (se 1 (by rfl) ⟨83365655, by rfl⟩ : syracuseStep 111154207 = 166731311) B166731311
theorem B148205609 : Blo 2283435 148205609 := bstep (se 2 (by rfl) ⟨55577103, by rfl⟩ : syracuseStep 148205609 = 111154207) B111154207
theorem B98803739 : Blo 2283435 98803739 := bstep (se 1 (by rfl) ⟨74102804, by rfl⟩ : syracuseStep 98803739 = 148205609) B148205609
theorem B65869159 : Blo 2283435 65869159 := bstep (se 1 (by rfl) ⟨49401869, by rfl⟩ : syracuseStep 65869159 = 98803739) B98803739
theorem B87825545 : Blo 2283435 87825545 := bstep (se 2 (by rfl) ⟨32934579, by rfl⟩ : syracuseStep 87825545 = 65869159) B65869159
theorem B58550363 : Blo 2283435 58550363 := bstep (se 1 (by rfl) ⟨43912772, by rfl⟩ : syracuseStep 58550363 = 87825545) B87825545
theorem B39033575 : Blo 2283435 39033575 := bstep (se 1 (by rfl) ⟨29275181, by rfl⟩ : syracuseStep 39033575 = 58550363) B58550363
theorem B26022383 : Blo 2283435 26022383 := bstep (se 1 (by rfl) ⟨19516787, by rfl⟩ : syracuseStep 26022383 = 39033575) B39033575
theorem B17348255 : Blo 2283435 17348255 := bstep (se 1 (by rfl) ⟨13011191, by rfl⟩ : syracuseStep 17348255 = 26022383) B26022383
theorem B11565503 : Blo 2283435 11565503 := bstep (se 1 (by rfl) ⟨8674127, by rfl⟩ : syracuseStep 11565503 = 17348255) B17348255
theorem B7710335 : Blo 2283435 7710335 := bstep (se 1 (by rfl) ⟨5782751, by rfl⟩ : syracuseStep 7710335 = 11565503) B11565503
theorem B5140223 : Blo 2283435 5140223 := bstep (se 1 (by rfl) ⟨3855167, by rfl⟩ : syracuseStep 5140223 = 7710335) B7710335
theorem B3426815 : Blo 2283435 3426815 := bstep (se 1 (by rfl) ⟨2570111, by rfl⟩ : syracuseStep 3426815 = 5140223) B5140223
theorem B2284543 : Blo 2283435 2284543 := bstep (se 1 (by rfl) ⟨1713407, by rfl⟩ : syracuseStep 2284543 = 3426815) B3426815
theorem B3426821 : Blo 2283435 3426821 := bbase (se 4 (by rfl) ⟨321264, by rfl⟩ : syracuseStep 3426821 = 642529) (by norm_num)
theorem B2284547 : Blo 2283435 2284547 := bstep (se 1 (by rfl) ⟨1713410, by rfl⟩ : syracuseStep 2284547 = 3426821) B3426821
theorem B3855181 : Blo 2283435 3855181 := bbase (se 3 (by rfl) ⟨722846, by rfl⟩ : syracuseStep 3855181 = 1445693) (by norm_num)
theorem B5140241 : Blo 2283435 5140241 := bstep (se 2 (by rfl) ⟨1927590, by rfl⟩ : syracuseStep 5140241 = 3855181) B3855181
theorem B3426827 : Blo 2283435 3426827 := bstep (se 1 (by rfl) ⟨2570120, by rfl⟩ : syracuseStep 3426827 = 5140241) B5140241
theorem B2284551 : Blo 2283435 2284551 := bstep (se 1 (by rfl) ⟨1713413, by rfl⟩ : syracuseStep 2284551 = 3426827) B3426827
theorem B2570125 : Blo 2283435 2570125 := bbase (se 3 (by rfl) ⟨481898, by rfl⟩ : syracuseStep 2570125 = 963797) (by norm_num)
theorem B3426833 : Blo 2283435 3426833 := bstep (se 2 (by rfl) ⟨1285062, by rfl⟩ : syracuseStep 3426833 = 2570125) B2570125
theorem B2284555 : Blo 2283435 2284555 := bstep (se 1 (by rfl) ⟨1713416, by rfl⟩ : syracuseStep 2284555 = 3426833) B3426833
theorem B7710389 : Blo 2283435 7710389 := bbase (se 5 (by rfl) ⟨361424, by rfl⟩ : syracuseStep 7710389 = 722849) (by norm_num)
theorem B5140259 : Blo 2283435 5140259 := bstep (se 1 (by rfl) ⟨3855194, by rfl⟩ : syracuseStep 5140259 = 7710389) B7710389
theorem B3426839 : Blo 2283435 3426839 := bstep (se 1 (by rfl) ⟨2570129, by rfl⟩ : syracuseStep 3426839 = 5140259) B5140259
theorem B2284559 : Blo 2283435 2284559 := bstep (se 1 (by rfl) ⟨1713419, by rfl⟩ : syracuseStep 2284559 = 3426839) B3426839
theorem B3426845 : Blo 2283435 3426845 := bbase (se 3 (by rfl) ⟨642533, by rfl⟩ : syracuseStep 3426845 = 1285067) (by norm_num)
theorem B2284563 : Blo 2283435 2284563 := bstep (se 1 (by rfl) ⟨1713422, by rfl⟩ : syracuseStep 2284563 = 3426845) B3426845
theorem B5140277 : Blo 2283435 5140277 := bbase (se 5 (by rfl) ⟨240950, by rfl⟩ : syracuseStep 5140277 = 481901) (by norm_num)
theorem B3426851 : Blo 2283435 3426851 := bstep (se 1 (by rfl) ⟨2570138, by rfl⟩ : syracuseStep 3426851 = 5140277) B5140277
theorem B2284567 : Blo 2283435 2284567 := bstep (se 1 (by rfl) ⟨1713425, by rfl⟩ : syracuseStep 2284567 = 3426851) B3426851
theorem B5489165 : Blo 2283435 5489165 := bbase (se 3 (by rfl) ⟨1029218, by rfl⟩ : syracuseStep 5489165 = 2058437) (by norm_num)
theorem B14637773 : Blo 2283435 14637773 := bstep (se 3 (by rfl) ⟨2744582, by rfl⟩ : syracuseStep 14637773 = 5489165) B5489165
theorem B9758515 : Blo 2283435 9758515 := bstep (se 1 (by rfl) ⟨7318886, by rfl⟩ : syracuseStep 9758515 = 14637773) B14637773
theorem B13011353 : Blo 2283435 13011353 := bstep (se 2 (by rfl) ⟨4879257, by rfl⟩ : syracuseStep 13011353 = 9758515) B9758515
theorem B8674235 : Blo 2283435 8674235 := bstep (se 1 (by rfl) ⟨6505676, by rfl⟩ : syracuseStep 8674235 = 13011353) B13011353
theorem B5782823 : Blo 2283435 5782823 := bstep (se 1 (by rfl) ⟨4337117, by rfl⟩ : syracuseStep 5782823 = 8674235) B8674235
theorem B3855215 : Blo 2283435 3855215 := bstep (se 1 (by rfl) ⟨2891411, by rfl⟩ : syracuseStep 3855215 = 5782823) B5782823
theorem B2570143 : Blo 2283435 2570143 := bstep (se 1 (by rfl) ⟨1927607, by rfl⟩ : syracuseStep 2570143 = 3855215) B3855215
theorem B3426857 : Blo 2283435 3426857 := bstep (se 2 (by rfl) ⟨1285071, by rfl⟩ : syracuseStep 3426857 = 2570143) B2570143
theorem B2284571 : Blo 2283435 2284571 := bstep (se 1 (by rfl) ⟨1713428, by rfl⟩ : syracuseStep 2284571 = 3426857) B3426857
theorem B3087661 : Blo 2283435 3087661 := bbase (se 3 (by rfl) ⟨578936, by rfl⟩ : syracuseStep 3087661 = 1157873) (by norm_num)
theorem B4116881 : Blo 2283435 4116881 := bstep (se 2 (by rfl) ⟨1543830, by rfl⟩ : syracuseStep 4116881 = 3087661) B3087661
theorem B2744587 : Blo 2283435 2744587 := bstep (se 1 (by rfl) ⟨2058440, by rfl⟩ : syracuseStep 2744587 = 4116881) B4116881
theorem B14637797 : Blo 2283435 14637797 := bstep (se 4 (by rfl) ⟨1372293, by rfl⟩ : syracuseStep 14637797 = 2744587) B2744587
theorem B9758531 : Blo 2283435 9758531 := bstep (se 1 (by rfl) ⟨7318898, by rfl⟩ : syracuseStep 9758531 = 14637797) B14637797
theorem B6505687 : Blo 2283435 6505687 := bstep (se 1 (by rfl) ⟨4879265, by rfl⟩ : syracuseStep 6505687 = 9758531) B9758531
theorem B8674249 : Blo 2283435 8674249 := bstep (se 2 (by rfl) ⟨3252843, by rfl⟩ : syracuseStep 8674249 = 6505687) B6505687
theorem B11565665 : Blo 2283435 11565665 := bstep (se 2 (by rfl) ⟨4337124, by rfl⟩ : syracuseStep 11565665 = 8674249) B8674249
theorem B7710443 : Blo 2283435 7710443 := bstep (se 1 (by rfl) ⟨5782832, by rfl⟩ : syracuseStep 7710443 = 11565665) B11565665
theorem B5140295 : Blo 2283435 5140295 := bstep (se 1 (by rfl) ⟨3855221, by rfl⟩ : syracuseStep 5140295 = 7710443) B7710443
theorem B3426863 : Blo 2283435 3426863 := bstep (se 1 (by rfl) ⟨2570147, by rfl⟩ : syracuseStep 3426863 = 5140295) B5140295
theorem B2284575 : Blo 2283435 2284575 := bstep (se 1 (by rfl) ⟨1713431, by rfl⟩ : syracuseStep 2284575 = 3426863) B3426863
theorem B3426869 : Blo 2283435 3426869 := bbase (se 5 (by rfl) ⟨160634, by rfl⟩ : syracuseStep 3426869 = 321269) (by norm_num)
theorem B2284579 : Blo 2283435 2284579 := bstep (se 1 (by rfl) ⟨1713434, by rfl⟩ : syracuseStep 2284579 = 3426869) B3426869
theorem B5782853 : Blo 2283435 5782853 := bbase (se 4 (by rfl) ⟨542142, by rfl⟩ : syracuseStep 5782853 = 1084285) (by norm_num)
theorem B3855235 : Blo 2283435 3855235 := bstep (se 1 (by rfl) ⟨2891426, by rfl⟩ : syracuseStep 3855235 = 5782853) B5782853
theorem B5140313 : Blo 2283435 5140313 := bstep (se 2 (by rfl) ⟨1927617, by rfl⟩ : syracuseStep 5140313 = 3855235) B3855235
theorem B3426875 : Blo 2283435 3426875 := bstep (se 1 (by rfl) ⟨2570156, by rfl⟩ : syracuseStep 3426875 = 5140313) B5140313
theorem B2284583 : Blo 2283435 2284583 := bstep (se 1 (by rfl) ⟨1713437, by rfl⟩ : syracuseStep 2284583 = 3426875) B3426875
theorem B2570161 : Blo 2283435 2570161 := bbase (se 2 (by rfl) ⟨963810, by rfl⟩ : syracuseStep 2570161 = 1927621) (by norm_num)
theorem B3426881 : Blo 2283435 3426881 := bstep (se 2 (by rfl) ⟨1285080, by rfl⟩ : syracuseStep 3426881 = 2570161) B2570161
theorem B2284587 : Blo 2283435 2284587 := bstep (se 1 (by rfl) ⟨1713440, by rfl⟩ : syracuseStep 2284587 = 3426881) B3426881
theorem B6505733 : Blo 2283435 6505733 := bbase (se 4 (by rfl) ⟨609912, by rfl⟩ : syracuseStep 6505733 = 1219825) (by norm_num)
theorem B4337155 : Blo 2283435 4337155 := bstep (se 1 (by rfl) ⟨3252866, by rfl⟩ : syracuseStep 4337155 = 6505733) B6505733
theorem B5782873 : Blo 2283435 5782873 := bstep (se 2 (by rfl) ⟨2168577, by rfl⟩ : syracuseStep 5782873 = 4337155) B4337155
theorem B7710497 : Blo 2283435 7710497 := bstep (se 2 (by rfl) ⟨2891436, by rfl⟩ : syracuseStep 7710497 = 5782873) B5782873
theorem B5140331 : Blo 2283435 5140331 := bstep (se 1 (by rfl) ⟨3855248, by rfl⟩ : syracuseStep 5140331 = 7710497) B7710497
theorem B3426887 : Blo 2283435 3426887 := bstep (se 1 (by rfl) ⟨2570165, by rfl⟩ : syracuseStep 3426887 = 5140331) B5140331
theorem B2284591 : Blo 2283435 2284591 := bstep (se 1 (by rfl) ⟨1713443, by rfl⟩ : syracuseStep 2284591 = 3426887) B3426887
theorem B3426893 : Blo 2283435 3426893 := bbase (se 3 (by rfl) ⟨642542, by rfl⟩ : syracuseStep 3426893 = 1285085) (by norm_num)
theorem B2284595 : Blo 2283435 2284595 := bstep (se 1 (by rfl) ⟨1713446, by rfl⟩ : syracuseStep 2284595 = 3426893) B3426893
theorem B5140349 : Blo 2283435 5140349 := bbase (se 3 (by rfl) ⟨963815, by rfl⟩ : syracuseStep 5140349 = 1927631) (by norm_num)
theorem B3426899 : Blo 2283435 3426899 := bstep (se 1 (by rfl) ⟨2570174, by rfl⟩ : syracuseStep 3426899 = 5140349) B5140349
theorem B2284599 : Blo 2283435 2284599 := bstep (se 1 (by rfl) ⟨1713449, by rfl⟩ : syracuseStep 2284599 = 3426899) B3426899
theorem B3855269 : Blo 2283435 3855269 := bbase (se 4 (by rfl) ⟨361431, by rfl⟩ : syracuseStep 3855269 = 722863) (by norm_num)
theorem B2570179 : Blo 2283435 2570179 := bstep (se 1 (by rfl) ⟨1927634, by rfl⟩ : syracuseStep 2570179 = 3855269) B3855269
theorem B3426905 : Blo 2283435 3426905 := bstep (se 2 (by rfl) ⟨1285089, by rfl⟩ : syracuseStep 3426905 = 2570179) B2570179
theorem B2284603 : Blo 2283435 2284603 := bstep (se 1 (by rfl) ⟨1713452, by rfl⟩ : syracuseStep 2284603 = 3426905) B3426905
theorem B3659501 : Blo 2283435 3659501 := bbase (se 3 (by rfl) ⟨686156, by rfl⟩ : syracuseStep 3659501 = 1372313) (by norm_num)
theorem B2439667 : Blo 2283435 2439667 := bstep (se 1 (by rfl) ⟨1829750, by rfl⟩ : syracuseStep 2439667 = 3659501) B3659501
theorem B3252889 : Blo 2283435 3252889 := bstep (se 2 (by rfl) ⟨1219833, by rfl⟩ : syracuseStep 3252889 = 2439667) B2439667
theorem B17348741 : Blo 2283435 17348741 := bstep (se 4 (by rfl) ⟨1626444, by rfl⟩ : syracuseStep 17348741 = 3252889) B3252889
theorem B11565827 : Blo 2283435 11565827 := bstep (se 1 (by rfl) ⟨8674370, by rfl⟩ : syracuseStep 11565827 = 17348741) B17348741
theorem B7710551 : Blo 2283435 7710551 := bstep (se 1 (by rfl) ⟨5782913, by rfl⟩ : syracuseStep 7710551 = 11565827) B11565827
theorem B5140367 : Blo 2283435 5140367 := bstep (se 1 (by rfl) ⟨3855275, by rfl⟩ : syracuseStep 5140367 = 7710551) B7710551
theorem B3426911 : Blo 2283435 3426911 := bstep (se 1 (by rfl) ⟨2570183, by rfl⟩ : syracuseStep 3426911 = 5140367) B5140367
theorem B2284607 : Blo 2283435 2284607 := bstep (se 1 (by rfl) ⟨1713455, by rfl⟩ : syracuseStep 2284607 = 3426911) B3426911
theorem B3426917 : Blo 2283435 3426917 := bbase (se 4 (by rfl) ⟨321273, by rfl⟩ : syracuseStep 3426917 = 642547) (by norm_num)
theorem B2284611 : Blo 2283435 2284611 := bstep (se 1 (by rfl) ⟨1713458, by rfl⟩ : syracuseStep 2284611 = 3426917) B3426917
theorem B3252901 : Blo 2283435 3252901 := bbase (se 4 (by rfl) ⟨304959, by rfl⟩ : syracuseStep 3252901 = 609919) (by norm_num)
theorem B4337201 : Blo 2283435 4337201 := bstep (se 2 (by rfl) ⟨1626450, by rfl⟩ : syracuseStep 4337201 = 3252901) B3252901
theorem B2891467 : Blo 2283435 2891467 := bstep (se 1 (by rfl) ⟨2168600, by rfl⟩ : syracuseStep 2891467 = 4337201) B4337201
theorem B3855289 : Blo 2283435 3855289 := bstep (se 2 (by rfl) ⟨1445733, by rfl⟩ : syracuseStep 3855289 = 2891467) B2891467
theorem B5140385 : Blo 2283435 5140385 := bstep (se 2 (by rfl) ⟨1927644, by rfl⟩ : syracuseStep 5140385 = 3855289) B3855289
theorem B3426923 : Blo 2283435 3426923 := bstep (se 1 (by rfl) ⟨2570192, by rfl⟩ : syracuseStep 3426923 = 5140385) B5140385
theorem B2284615 : Blo 2283435 2284615 := bstep (se 1 (by rfl) ⟨1713461, by rfl⟩ : syracuseStep 2284615 = 3426923) B3426923
theorem B2570197 : Blo 2283435 2570197 := bbase (se 7 (by rfl) ⟨30119, by rfl⟩ : syracuseStep 2570197 = 60239) (by norm_num)
theorem B3426929 : Blo 2283435 3426929 := bstep (se 2 (by rfl) ⟨1285098, by rfl⟩ : syracuseStep 3426929 = 2570197) B2570197
theorem B2284619 : Blo 2283435 2284619 := bstep (se 1 (by rfl) ⟨1713464, by rfl⟩ : syracuseStep 2284619 = 3426929) B3426929
theorem B2891477 : Blo 2283435 2891477 := bbase (se 7 (by rfl) ⟨33884, by rfl⟩ : syracuseStep 2891477 = 67769) (by norm_num)
theorem B7710605 : Blo 2283435 7710605 := bstep (se 3 (by rfl) ⟨1445738, by rfl⟩ : syracuseStep 7710605 = 2891477) B2891477
theorem B5140403 : Blo 2283435 5140403 := bstep (se 1 (by rfl) ⟨3855302, by rfl⟩ : syracuseStep 5140403 = 7710605) B7710605
theorem B3426935 : Blo 2283435 3426935 := bstep (se 1 (by rfl) ⟨2570201, by rfl⟩ : syracuseStep 3426935 = 5140403) B5140403
theorem B2284623 : Blo 2283435 2284623 := bstep (se 1 (by rfl) ⟨1713467, by rfl⟩ : syracuseStep 2284623 = 3426935) B3426935
theorem B3426941 : Blo 2283435 3426941 := bbase (se 3 (by rfl) ⟨642551, by rfl⟩ : syracuseStep 3426941 = 1285103) (by norm_num)
theorem B2284627 : Blo 2283435 2284627 := bstep (se 1 (by rfl) ⟨1713470, by rfl⟩ : syracuseStep 2284627 = 3426941) B3426941
theorem B5140421 : Blo 2283435 5140421 := bbase (se 4 (by rfl) ⟨481914, by rfl⟩ : syracuseStep 5140421 = 963829) (by norm_num)
theorem B3426947 : Blo 2283435 3426947 := bstep (se 1 (by rfl) ⟨2570210, by rfl⟩ : syracuseStep 3426947 = 5140421) B5140421
theorem B2284631 : Blo 2283435 2284631 := bstep (se 1 (by rfl) ⟨1713473, by rfl⟩ : syracuseStep 2284631 = 3426947) B3426947
theorem B9758789 : Blo 2283435 9758789 := bbase (se 4 (by rfl) ⟨914886, by rfl⟩ : syracuseStep 9758789 = 1829773) (by norm_num)
theorem B6505859 : Blo 2283435 6505859 := bstep (se 1 (by rfl) ⟨4879394, by rfl⟩ : syracuseStep 6505859 = 9758789) B9758789
theorem B4337239 : Blo 2283435 4337239 := bstep (se 1 (by rfl) ⟨3252929, by rfl⟩ : syracuseStep 4337239 = 6505859) B6505859
theorem B5782985 : Blo 2283435 5782985 := bstep (se 2 (by rfl) ⟨2168619, by rfl⟩ : syracuseStep 5782985 = 4337239) B4337239
theorem B3855323 : Blo 2283435 3855323 := bstep (se 1 (by rfl) ⟨2891492, by rfl⟩ : syracuseStep 3855323 = 5782985) B5782985
theorem B2570215 : Blo 2283435 2570215 := bstep (se 1 (by rfl) ⟨1927661, by rfl⟩ : syracuseStep 2570215 = 3855323) B3855323
theorem B3426953 : Blo 2283435 3426953 := bstep (se 2 (by rfl) ⟨1285107, by rfl⟩ : syracuseStep 3426953 = 2570215) B2570215
theorem B2284635 : Blo 2283435 2284635 := bstep (se 1 (by rfl) ⟨1713476, by rfl⟩ : syracuseStep 2284635 = 3426953) B3426953
theorem B11565989 : Blo 2283435 11565989 := bbase (se 4 (by rfl) ⟨1084311, by rfl⟩ : syracuseStep 11565989 = 2168623) (by norm_num)
theorem B7710659 : Blo 2283435 7710659 := bstep (se 1 (by rfl) ⟨5782994, by rfl⟩ : syracuseStep 7710659 = 11565989) B11565989
theorem B5140439 : Blo 2283435 5140439 := bstep (se 1 (by rfl) ⟨3855329, by rfl⟩ : syracuseStep 5140439 = 7710659) B7710659
theorem B3426959 : Blo 2283435 3426959 := bstep (se 1 (by rfl) ⟨2570219, by rfl⟩ : syracuseStep 3426959 = 5140439) B5140439
theorem B2284639 : Blo 2283435 2284639 := bstep (se 1 (by rfl) ⟨1713479, by rfl⟩ : syracuseStep 2284639 = 3426959) B3426959
theorem B3426965 : Blo 2283435 3426965 := bbase (se 6 (by rfl) ⟨80319, by rfl⟩ : syracuseStep 3426965 = 160639) (by norm_num)
theorem B2284643 : Blo 2283435 2284643 := bstep (se 1 (by rfl) ⟨1713482, by rfl⟩ : syracuseStep 2284643 = 3426965) B3426965
theorem B8234021 : Blo 2283435 8234021 := bbase (se 4 (by rfl) ⟨771939, by rfl⟩ : syracuseStep 8234021 = 1543879) (by norm_num)
theorem B21957389 : Blo 2283435 21957389 := bstep (se 3 (by rfl) ⟨4117010, by rfl⟩ : syracuseStep 21957389 = 8234021) B8234021
theorem B14638259 : Blo 2283435 14638259 := bstep (se 1 (by rfl) ⟨10978694, by rfl⟩ : syracuseStep 14638259 = 21957389) B21957389
theorem B9758839 : Blo 2283435 9758839 := bstep (se 1 (by rfl) ⟨7319129, by rfl⟩ : syracuseStep 9758839 = 14638259) B14638259
theorem B13011785 : Blo 2283435 13011785 := bstep (se 2 (by rfl) ⟨4879419, by rfl⟩ : syracuseStep 13011785 = 9758839) B9758839
theorem B8674523 : Blo 2283435 8674523 := bstep (se 1 (by rfl) ⟨6505892, by rfl⟩ : syracuseStep 8674523 = 13011785) B13011785
theorem B5783015 : Blo 2283435 5783015 := bstep (se 1 (by rfl) ⟨4337261, by rfl⟩ : syracuseStep 5783015 = 8674523) B8674523
theorem B3855343 : Blo 2283435 3855343 := bstep (se 1 (by rfl) ⟨2891507, by rfl⟩ : syracuseStep 3855343 = 5783015) B5783015
theorem B5140457 : Blo 2283435 5140457 := bstep (se 2 (by rfl) ⟨1927671, by rfl⟩ : syracuseStep 5140457 = 3855343) B3855343
theorem B3426971 : Blo 2283435 3426971 := bstep (se 1 (by rfl) ⟨2570228, by rfl⟩ : syracuseStep 3426971 = 5140457) B5140457
theorem B2284647 : Blo 2283435 2284647 := bstep (se 1 (by rfl) ⟨1713485, by rfl⟩ : syracuseStep 2284647 = 3426971) B3426971
theorem B2570233 : Blo 2283435 2570233 := bbase (se 2 (by rfl) ⟨963837, by rfl⟩ : syracuseStep 2570233 = 1927675) (by norm_num)
theorem B3426977 : Blo 2283435 3426977 := bstep (se 2 (by rfl) ⟨1285116, by rfl⟩ : syracuseStep 3426977 = 2570233) B2570233
theorem B2284651 : Blo 2283435 2284651 := bstep (se 1 (by rfl) ⟨1713488, by rfl⟩ : syracuseStep 2284651 = 3426977) B3426977
theorem B3473741 : Blo 2283435 3473741 := bbase (se 3 (by rfl) ⟨651326, by rfl⟩ : syracuseStep 3473741 = 1302653) (by norm_num)
theorem B2315827 : Blo 2283435 2315827 := bstep (se 1 (by rfl) ⟨1736870, by rfl⟩ : syracuseStep 2315827 = 3473741) B3473741
theorem B3087769 : Blo 2283435 3087769 := bstep (se 2 (by rfl) ⟨1157913, by rfl⟩ : syracuseStep 3087769 = 2315827) B2315827
theorem B4117025 : Blo 2283435 4117025 := bstep (se 2 (by rfl) ⟨1543884, by rfl⟩ : syracuseStep 4117025 = 3087769) B3087769
theorem B10978733 : Blo 2283435 10978733 := bstep (se 3 (by rfl) ⟨2058512, by rfl⟩ : syracuseStep 10978733 = 4117025) B4117025
theorem B7319155 : Blo 2283435 7319155 := bstep (se 1 (by rfl) ⟨5489366, by rfl⟩ : syracuseStep 7319155 = 10978733) B10978733
theorem B9758873 : Blo 2283435 9758873 := bstep (se 2 (by rfl) ⟨3659577, by rfl⟩ : syracuseStep 9758873 = 7319155) B7319155
theorem B6505915 : Blo 2283435 6505915 := bstep (se 1 (by rfl) ⟨4879436, by rfl⟩ : syracuseStep 6505915 = 9758873) B9758873
theorem B8674553 : Blo 2283435 8674553 := bstep (se 2 (by rfl) ⟨3252957, by rfl⟩ : syracuseStep 8674553 = 6505915) B6505915
theorem B5783035 : Blo 2283435 5783035 := bstep (se 1 (by rfl) ⟨4337276, by rfl⟩ : syracuseStep 5783035 = 8674553) B8674553
theorem B7710713 : Blo 2283435 7710713 := bstep (se 2 (by rfl) ⟨2891517, by rfl⟩ : syracuseStep 7710713 = 5783035) B5783035
theorem B5140475 : Blo 2283435 5140475 := bstep (se 1 (by rfl) ⟨3855356, by rfl⟩ : syracuseStep 5140475 = 7710713) B7710713
theorem B3426983 : Blo 2283435 3426983 := bstep (se 1 (by rfl) ⟨2570237, by rfl⟩ : syracuseStep 3426983 = 5140475) B5140475
theorem B2284655 : Blo 2283435 2284655 := bstep (se 1 (by rfl) ⟨1713491, by rfl⟩ : syracuseStep 2284655 = 3426983) B3426983
theorem B3426989 : Blo 2283435 3426989 := bbase (se 3 (by rfl) ⟨642560, by rfl⟩ : syracuseStep 3426989 = 1285121) (by norm_num)
theorem B2284659 : Blo 2283435 2284659 := bstep (se 1 (by rfl) ⟨1713494, by rfl⟩ : syracuseStep 2284659 = 3426989) B3426989
theorem B5140493 : Blo 2283435 5140493 := bbase (se 3 (by rfl) ⟨963842, by rfl⟩ : syracuseStep 5140493 = 1927685) (by norm_num)
theorem B3426995 : Blo 2283435 3426995 := bstep (se 1 (by rfl) ⟨2570246, by rfl⟩ : syracuseStep 3426995 = 5140493) B5140493
theorem B2284663 : Blo 2283435 2284663 := bstep (se 1 (by rfl) ⟨1713497, by rfl⟩ : syracuseStep 2284663 = 3426995) B3426995
theorem B2891533 : Blo 2283435 2891533 := bbase (se 3 (by rfl) ⟨542162, by rfl⟩ : syracuseStep 2891533 = 1084325) (by norm_num)
theorem B3855377 : Blo 2283435 3855377 := bstep (se 2 (by rfl) ⟨1445766, by rfl⟩ : syracuseStep 3855377 = 2891533) B2891533
theorem B2570251 : Blo 2283435 2570251 := bstep (se 1 (by rfl) ⟨1927688, by rfl⟩ : syracuseStep 2570251 = 3855377) B3855377
theorem B3427001 : Blo 2283435 3427001 := bstep (se 2 (by rfl) ⟨1285125, by rfl⟩ : syracuseStep 3427001 = 2570251) B2570251
theorem B2284667 : Blo 2283435 2284667 := bstep (se 1 (by rfl) ⟨1713500, by rfl⟩ : syracuseStep 2284667 = 3427001) B3427001
theorem B16468213 : Blo 2283435 16468213 := bbase (se 5 (by rfl) ⟨771947, by rfl⟩ : syracuseStep 16468213 = 1543895) (by norm_num)
theorem B21957617 : Blo 2283435 21957617 := bstep (se 2 (by rfl) ⟨8234106, by rfl⟩ : syracuseStep 21957617 = 16468213) B16468213
theorem B14638411 : Blo 2283435 14638411 := bstep (se 1 (by rfl) ⟨10978808, by rfl⟩ : syracuseStep 14638411 = 21957617) B21957617
theorem B19517881 : Blo 2283435 19517881 := bstep (se 2 (by rfl) ⟨7319205, by rfl⟩ : syracuseStep 19517881 = 14638411) B14638411
theorem B26023841 : Blo 2283435 26023841 := bstep (se 2 (by rfl) ⟨9758940, by rfl⟩ : syracuseStep 26023841 = 19517881) B19517881
theorem B17349227 : Blo 2283435 17349227 := bstep (se 1 (by rfl) ⟨13011920, by rfl⟩ : syracuseStep 17349227 = 26023841) B26023841
theorem B11566151 : Blo 2283435 11566151 := bstep (se 1 (by rfl) ⟨8674613, by rfl⟩ : syracuseStep 11566151 = 17349227) B17349227
theorem B7710767 : Blo 2283435 7710767 := bstep (se 1 (by rfl) ⟨5783075, by rfl⟩ : syracuseStep 7710767 = 11566151) B11566151
theorem B5140511 : Blo 2283435 5140511 := bstep (se 1 (by rfl) ⟨3855383, by rfl⟩ : syracuseStep 5140511 = 7710767) B7710767
theorem B3427007 : Blo 2283435 3427007 := bstep (se 1 (by rfl) ⟨2570255, by rfl⟩ : syracuseStep 3427007 = 5140511) B5140511
theorem B2284671 : Blo 2283435 2284671 := bstep (se 1 (by rfl) ⟨1713503, by rfl⟩ : syracuseStep 2284671 = 3427007) B3427007
theorem B3427013 : Blo 2283435 3427013 := bbase (se 4 (by rfl) ⟨321282, by rfl⟩ : syracuseStep 3427013 = 642565) (by norm_num)
theorem B2284675 : Blo 2283435 2284675 := bstep (se 1 (by rfl) ⟨1713506, by rfl⟩ : syracuseStep 2284675 = 3427013) B3427013
theorem B3855397 : Blo 2283435 3855397 := bbase (se 4 (by rfl) ⟨361443, by rfl⟩ : syracuseStep 3855397 = 722887) (by norm_num)
theorem B5140529 : Blo 2283435 5140529 := bstep (se 2 (by rfl) ⟨1927698, by rfl⟩ : syracuseStep 5140529 = 3855397) B3855397
theorem B3427019 : Blo 2283435 3427019 := bstep (se 1 (by rfl) ⟨2570264, by rfl⟩ : syracuseStep 3427019 = 5140529) B5140529
theorem B2284679 : Blo 2283435 2284679 := bstep (se 1 (by rfl) ⟨1713509, by rfl⟩ : syracuseStep 2284679 = 3427019) B3427019
theorem B2570269 : Blo 2283435 2570269 := bbase (se 3 (by rfl) ⟨481925, by rfl⟩ : syracuseStep 2570269 = 963851) (by norm_num)
theorem B3427025 : Blo 2283435 3427025 := bstep (se 2 (by rfl) ⟨1285134, by rfl⟩ : syracuseStep 3427025 = 2570269) B2570269
theorem B2284683 : Blo 2283435 2284683 := bstep (se 1 (by rfl) ⟨1713512, by rfl⟩ : syracuseStep 2284683 = 3427025) B3427025
theorem B7710821 : Blo 2283435 7710821 := bbase (se 4 (by rfl) ⟨722889, by rfl⟩ : syracuseStep 7710821 = 1445779) (by norm_num)
theorem B5140547 : Blo 2283435 5140547 := bstep (se 1 (by rfl) ⟨3855410, by rfl⟩ : syracuseStep 5140547 = 7710821) B7710821
theorem B3427031 : Blo 2283435 3427031 := bstep (se 1 (by rfl) ⟨2570273, by rfl⟩ : syracuseStep 3427031 = 5140547) B5140547
theorem B2284687 : Blo 2283435 2284687 := bstep (se 1 (by rfl) ⟨1713515, by rfl⟩ : syracuseStep 2284687 = 3427031) B3427031
theorem B3427037 : Blo 2283435 3427037 := bbase (se 3 (by rfl) ⟨642569, by rfl⟩ : syracuseStep 3427037 = 1285139) (by norm_num)
theorem B2284691 : Blo 2283435 2284691 := bstep (se 1 (by rfl) ⟨1713518, by rfl⟩ : syracuseStep 2284691 = 3427037) B3427037
theorem B5140565 : Blo 2283435 5140565 := bbase (se 8 (by rfl) ⟨30120, by rfl⟩ : syracuseStep 5140565 = 60241) (by norm_num)
theorem B3427043 : Blo 2283435 3427043 := bstep (se 1 (by rfl) ⟨2570282, by rfl⟩ : syracuseStep 3427043 = 5140565) B5140565
theorem B2284695 : Blo 2283435 2284695 := bstep (se 1 (by rfl) ⟨1713521, by rfl⟩ : syracuseStep 2284695 = 3427043) B3427043
theorem B3087829 : Blo 2283435 3087829 := bbase (se 7 (by rfl) ⟨36185, by rfl⟩ : syracuseStep 3087829 = 72371) (by norm_num)
theorem B4117105 : Blo 2283435 4117105 := bstep (se 2 (by rfl) ⟨1543914, by rfl⟩ : syracuseStep 4117105 = 3087829) B3087829
theorem B5489473 : Blo 2283435 5489473 := bstep (se 2 (by rfl) ⟨2058552, by rfl⟩ : syracuseStep 5489473 = 4117105) B4117105
theorem B7319297 : Blo 2283435 7319297 := bstep (se 2 (by rfl) ⟨2744736, by rfl⟩ : syracuseStep 7319297 = 5489473) B5489473
theorem B4879531 : Blo 2283435 4879531 := bstep (se 1 (by rfl) ⟨3659648, by rfl⟩ : syracuseStep 4879531 = 7319297) B7319297
theorem B6506041 : Blo 2283435 6506041 := bstep (se 2 (by rfl) ⟨2439765, by rfl⟩ : syracuseStep 6506041 = 4879531) B4879531
theorem B8674721 : Blo 2283435 8674721 := bstep (se 2 (by rfl) ⟨3253020, by rfl⟩ : syracuseStep 8674721 = 6506041) B6506041
theorem B5783147 : Blo 2283435 5783147 := bstep (se 1 (by rfl) ⟨4337360, by rfl⟩ : syracuseStep 5783147 = 8674721) B8674721
theorem B3855431 : Blo 2283435 3855431 := bstep (se 1 (by rfl) ⟨2891573, by rfl⟩ : syracuseStep 3855431 = 5783147) B5783147
theorem B2570287 : Blo 2283435 2570287 := bstep (se 1 (by rfl) ⟨1927715, by rfl⟩ : syracuseStep 2570287 = 3855431) B3855431
theorem B3427049 : Blo 2283435 3427049 := bstep (se 2 (by rfl) ⟨1285143, by rfl⟩ : syracuseStep 3427049 = 2570287) B2570287
theorem B2284699 : Blo 2283435 2284699 := bstep (se 1 (by rfl) ⟨1713524, by rfl⟩ : syracuseStep 2284699 = 3427049) B3427049
theorem B3473813 : Blo 2283435 3473813 := bbase (se 6 (by rfl) ⟨81417, by rfl⟩ : syracuseStep 3473813 = 162835) (by norm_num)
theorem B9263501 : Blo 2283435 9263501 := bstep (se 3 (by rfl) ⟨1736906, by rfl⟩ : syracuseStep 9263501 = 3473813) B3473813
theorem B6175667 : Blo 2283435 6175667 := bstep (se 1 (by rfl) ⟨4631750, by rfl⟩ : syracuseStep 6175667 = 9263501) B9263501
theorem B4117111 : Blo 2283435 4117111 := bstep (se 1 (by rfl) ⟨3087833, by rfl⟩ : syracuseStep 4117111 = 6175667) B6175667
theorem B21957925 : Blo 2283435 21957925 := bstep (se 4 (by rfl) ⟨2058555, by rfl⟩ : syracuseStep 21957925 = 4117111) B4117111
theorem B29277233 : Blo 2283435 29277233 := bstep (se 2 (by rfl) ⟨10978962, by rfl⟩ : syracuseStep 29277233 = 21957925) B21957925
theorem B19518155 : Blo 2283435 19518155 := bstep (se 1 (by rfl) ⟨14638616, by rfl⟩ : syracuseStep 19518155 = 29277233) B29277233
theorem B13012103 : Blo 2283435 13012103 := bstep (se 1 (by rfl) ⟨9759077, by rfl⟩ : syracuseStep 13012103 = 19518155) B19518155
theorem B8674735 : Blo 2283435 8674735 := bstep (se 1 (by rfl) ⟨6506051, by rfl⟩ : syracuseStep 8674735 = 13012103) B13012103
theorem B11566313 : Blo 2283435 11566313 := bstep (se 2 (by rfl) ⟨4337367, by rfl⟩ : syracuseStep 11566313 = 8674735) B8674735
theorem B7710875 : Blo 2283435 7710875 := bstep (se 1 (by rfl) ⟨5783156, by rfl⟩ : syracuseStep 7710875 = 11566313) B11566313
theorem B5140583 : Blo 2283435 5140583 := bstep (se 1 (by rfl) ⟨3855437, by rfl⟩ : syracuseStep 5140583 = 7710875) B7710875
theorem B3427055 : Blo 2283435 3427055 := bstep (se 1 (by rfl) ⟨2570291, by rfl⟩ : syracuseStep 3427055 = 5140583) B5140583
theorem B2284703 : Blo 2283435 2284703 := bstep (se 1 (by rfl) ⟨1713527, by rfl⟩ : syracuseStep 2284703 = 3427055) B3427055
theorem B3427061 : Blo 2283435 3427061 := bbase (se 5 (by rfl) ⟨160643, by rfl⟩ : syracuseStep 3427061 = 321287) (by norm_num)
theorem B2284707 : Blo 2283435 2284707 := bstep (se 1 (by rfl) ⟨1713530, by rfl⟩ : syracuseStep 2284707 = 3427061) B3427061
theorem B10421477 : Blo 2283435 10421477 := bbase (se 4 (by rfl) ⟨977013, by rfl⟩ : syracuseStep 10421477 = 1954027) (by norm_num)
theorem B6947651 : Blo 2283435 6947651 := bstep (se 1 (by rfl) ⟨5210738, by rfl⟩ : syracuseStep 6947651 = 10421477) B10421477
theorem B18527069 : Blo 2283435 18527069 := bstep (se 3 (by rfl) ⟨3473825, by rfl⟩ : syracuseStep 18527069 = 6947651) B6947651
theorem B12351379 : Blo 2283435 12351379 := bstep (se 1 (by rfl) ⟨9263534, by rfl⟩ : syracuseStep 12351379 = 18527069) B18527069
theorem B16468505 : Blo 2283435 16468505 := bstep (se 2 (by rfl) ⟨6175689, by rfl⟩ : syracuseStep 16468505 = 12351379) B12351379
theorem B10979003 : Blo 2283435 10979003 := bstep (se 1 (by rfl) ⟨8234252, by rfl⟩ : syracuseStep 10979003 = 16468505) B16468505
theorem B7319335 : Blo 2283435 7319335 := bstep (se 1 (by rfl) ⟨5489501, by rfl⟩ : syracuseStep 7319335 = 10979003) B10979003
theorem B9759113 : Blo 2283435 9759113 := bstep (se 2 (by rfl) ⟨3659667, by rfl⟩ : syracuseStep 9759113 = 7319335) B7319335
theorem B6506075 : Blo 2283435 6506075 := bstep (se 1 (by rfl) ⟨4879556, by rfl⟩ : syracuseStep 6506075 = 9759113) B9759113
theorem B4337383 : Blo 2283435 4337383 := bstep (se 1 (by rfl) ⟨3253037, by rfl⟩ : syracuseStep 4337383 = 6506075) B6506075
theorem B5783177 : Blo 2283435 5783177 := bstep (se 2 (by rfl) ⟨2168691, by rfl⟩ : syracuseStep 5783177 = 4337383) B4337383
theorem B3855451 : Blo 2283435 3855451 := bstep (se 1 (by rfl) ⟨2891588, by rfl⟩ : syracuseStep 3855451 = 5783177) B5783177
theorem B5140601 : Blo 2283435 5140601 := bstep (se 2 (by rfl) ⟨1927725, by rfl⟩ : syracuseStep 5140601 = 3855451) B3855451
theorem B3427067 : Blo 2283435 3427067 := bstep (se 1 (by rfl) ⟨2570300, by rfl⟩ : syracuseStep 3427067 = 5140601) B5140601
theorem B2284711 : Blo 2283435 2284711 := bstep (se 1 (by rfl) ⟨1713533, by rfl⟩ : syracuseStep 2284711 = 3427067) B3427067
theorem B2570305 : Blo 2283435 2570305 := bbase (se 2 (by rfl) ⟨963864, by rfl⟩ : syracuseStep 2570305 = 1927729) (by norm_num)
theorem B3427073 : Blo 2283435 3427073 := bstep (se 2 (by rfl) ⟨1285152, by rfl⟩ : syracuseStep 3427073 = 2570305) B2570305
theorem B2284715 : Blo 2283435 2284715 := bstep (se 1 (by rfl) ⟨1713536, by rfl⟩ : syracuseStep 2284715 = 3427073) B3427073
theorem B5783197 : Blo 2283435 5783197 := bbase (se 3 (by rfl) ⟨1084349, by rfl⟩ : syracuseStep 5783197 = 2168699) (by norm_num)
theorem B7710929 : Blo 2283435 7710929 := bstep (se 2 (by rfl) ⟨2891598, by rfl⟩ : syracuseStep 7710929 = 5783197) B5783197
theorem B5140619 : Blo 2283435 5140619 := bstep (se 1 (by rfl) ⟨3855464, by rfl⟩ : syracuseStep 5140619 = 7710929) B7710929
theorem B3427079 : Blo 2283435 3427079 := bstep (se 1 (by rfl) ⟨2570309, by rfl⟩ : syracuseStep 3427079 = 5140619) B5140619
theorem B2284719 : Blo 2283435 2284719 := bstep (se 1 (by rfl) ⟨1713539, by rfl⟩ : syracuseStep 2284719 = 3427079) B3427079
theorem B3427085 : Blo 2283435 3427085 := bbase (se 3 (by rfl) ⟨642578, by rfl⟩ : syracuseStep 3427085 = 1285157) (by norm_num)
theorem B2284723 : Blo 2283435 2284723 := bstep (se 1 (by rfl) ⟨1713542, by rfl⟩ : syracuseStep 2284723 = 3427085) B3427085
theorem B5140637 : Blo 2283435 5140637 := bbase (se 3 (by rfl) ⟨963869, by rfl⟩ : syracuseStep 5140637 = 1927739) (by norm_num)
theorem B3427091 : Blo 2283435 3427091 := bstep (se 1 (by rfl) ⟨2570318, by rfl⟩ : syracuseStep 3427091 = 5140637) B5140637
theorem B2284727 : Blo 2283435 2284727 := bstep (se 1 (by rfl) ⟨1713545, by rfl⟩ : syracuseStep 2284727 = 3427091) B3427091
theorem B3855485 : Blo 2283435 3855485 := bbase (se 3 (by rfl) ⟨722903, by rfl⟩ : syracuseStep 3855485 = 1445807) (by norm_num)
theorem B2570323 : Blo 2283435 2570323 := bstep (se 1 (by rfl) ⟨1927742, by rfl⟩ : syracuseStep 2570323 = 3855485) B3855485
theorem B3427097 : Blo 2283435 3427097 := bstep (se 2 (by rfl) ⟨1285161, by rfl⟩ : syracuseStep 3427097 = 2570323) B2570323
theorem B2284731 : Blo 2283435 2284731 := bstep (se 1 (by rfl) ⟨1713548, by rfl⟩ : syracuseStep 2284731 = 3427097) B3427097
theorem B3087877 : Blo 2283435 3087877 := bbase (se 4 (by rfl) ⟨289488, by rfl⟩ : syracuseStep 3087877 = 578977) (by norm_num)
theorem B4117169 : Blo 2283435 4117169 := bstep (se 2 (by rfl) ⟨1543938, by rfl⟩ : syracuseStep 4117169 = 3087877) B3087877
theorem B10979117 : Blo 2283435 10979117 := bstep (se 3 (by rfl) ⟨2058584, by rfl⟩ : syracuseStep 10979117 = 4117169) B4117169
theorem B7319411 : Blo 2283435 7319411 := bstep (se 1 (by rfl) ⟨5489558, by rfl⟩ : syracuseStep 7319411 = 10979117) B10979117
theorem B4879607 : Blo 2283435 4879607 := bstep (se 1 (by rfl) ⟨3659705, by rfl⟩ : syracuseStep 4879607 = 7319411) B7319411
theorem B13012285 : Blo 2283435 13012285 := bstep (se 3 (by rfl) ⟨2439803, by rfl⟩ : syracuseStep 13012285 = 4879607) B4879607
theorem B17349713 : Blo 2283435 17349713 := bstep (se 2 (by rfl) ⟨6506142, by rfl⟩ : syracuseStep 17349713 = 13012285) B13012285
theorem B11566475 : Blo 2283435 11566475 := bstep (se 1 (by rfl) ⟨8674856, by rfl⟩ : syracuseStep 11566475 = 17349713) B17349713
theorem B7710983 : Blo 2283435 7710983 := bstep (se 1 (by rfl) ⟨5783237, by rfl⟩ : syracuseStep 7710983 = 11566475) B11566475
theorem B5140655 : Blo 2283435 5140655 := bstep (se 1 (by rfl) ⟨3855491, by rfl⟩ : syracuseStep 5140655 = 7710983) B7710983
theorem B3427103 : Blo 2283435 3427103 := bstep (se 1 (by rfl) ⟨2570327, by rfl⟩ : syracuseStep 3427103 = 5140655) B5140655
theorem B2284735 : Blo 2283435 2284735 := bstep (se 1 (by rfl) ⟨1713551, by rfl⟩ : syracuseStep 2284735 = 3427103) B3427103
theorem B3427109 : Blo 2283435 3427109 := bbase (se 4 (by rfl) ⟨321291, by rfl⟩ : syracuseStep 3427109 = 642583) (by norm_num)
theorem B2284739 : Blo 2283435 2284739 := bstep (se 1 (by rfl) ⟨1713554, by rfl⟩ : syracuseStep 2284739 = 3427109) B3427109
theorem B2891629 : Blo 2283435 2891629 := bbase (se 3 (by rfl) ⟨542180, by rfl⟩ : syracuseStep 2891629 = 1084361) (by norm_num)
theorem B3855505 : Blo 2283435 3855505 := bstep (se 2 (by rfl) ⟨1445814, by rfl⟩ : syracuseStep 3855505 = 2891629) B2891629
theorem B5140673 : Blo 2283435 5140673 := bstep (se 2 (by rfl) ⟨1927752, by rfl⟩ : syracuseStep 5140673 = 3855505) B3855505
theorem B3427115 : Blo 2283435 3427115 := bstep (se 1 (by rfl) ⟨2570336, by rfl⟩ : syracuseStep 3427115 = 5140673) B5140673
theorem B2284743 : Blo 2283435 2284743 := bstep (se 1 (by rfl) ⟨1713557, by rfl⟩ : syracuseStep 2284743 = 3427115) B3427115
theorem B2570341 : Blo 2283435 2570341 := bbase (se 4 (by rfl) ⟨240969, by rfl⟩ : syracuseStep 2570341 = 481939) (by norm_num)
theorem B3427121 : Blo 2283435 3427121 := bstep (se 2 (by rfl) ⟨1285170, by rfl⟩ : syracuseStep 3427121 = 2570341) B2570341
theorem B2284747 : Blo 2283435 2284747 := bstep (se 1 (by rfl) ⟨1713560, by rfl⟩ : syracuseStep 2284747 = 3427121) B3427121
theorem B2439821 : Blo 2283435 2439821 := bbase (se 3 (by rfl) ⟨457466, by rfl⟩ : syracuseStep 2439821 = 914933) (by norm_num)
theorem B6506189 : Blo 2283435 6506189 := bstep (se 3 (by rfl) ⟨1219910, by rfl⟩ : syracuseStep 6506189 = 2439821) B2439821
theorem B4337459 : Blo 2283435 4337459 := bstep (se 1 (by rfl) ⟨3253094, by rfl⟩ : syracuseStep 4337459 = 6506189) B6506189
theorem B2891639 : Blo 2283435 2891639 := bstep (se 1 (by rfl) ⟨2168729, by rfl⟩ : syracuseStep 2891639 = 4337459) B4337459
theorem B7711037 : Blo 2283435 7711037 := bstep (se 3 (by rfl) ⟨1445819, by rfl⟩ : syracuseStep 7711037 = 2891639) B2891639
theorem B5140691 : Blo 2283435 5140691 := bstep (se 1 (by rfl) ⟨3855518, by rfl⟩ : syracuseStep 5140691 = 7711037) B7711037
theorem B3427127 : Blo 2283435 3427127 := bstep (se 1 (by rfl) ⟨2570345, by rfl⟩ : syracuseStep 3427127 = 5140691) B5140691
theorem B2284751 : Blo 2283435 2284751 := bstep (se 1 (by rfl) ⟨1713563, by rfl⟩ : syracuseStep 2284751 = 3427127) B3427127
theorem B3427133 : Blo 2283435 3427133 := bbase (se 3 (by rfl) ⟨642587, by rfl⟩ : syracuseStep 3427133 = 1285175) (by norm_num)
theorem B2284755 : Blo 2283435 2284755 := bstep (se 1 (by rfl) ⟨1713566, by rfl⟩ : syracuseStep 2284755 = 3427133) B3427133
theorem B5140709 : Blo 2283435 5140709 := bbase (se 4 (by rfl) ⟨481941, by rfl⟩ : syracuseStep 5140709 = 963883) (by norm_num)
theorem B3427139 : Blo 2283435 3427139 := bstep (se 1 (by rfl) ⟨2570354, by rfl⟩ : syracuseStep 3427139 = 5140709) B5140709
theorem B2284759 : Blo 2283435 2284759 := bstep (se 1 (by rfl) ⟨1713569, by rfl⟩ : syracuseStep 2284759 = 3427139) B3427139
theorem B5783309 : Blo 2283435 5783309 := bbase (se 3 (by rfl) ⟨1084370, by rfl⟩ : syracuseStep 5783309 = 2168741) (by norm_num)
theorem B3855539 : Blo 2283435 3855539 := bstep (se 1 (by rfl) ⟨2891654, by rfl⟩ : syracuseStep 3855539 = 5783309) B5783309
theorem B2570359 : Blo 2283435 2570359 := bstep (se 1 (by rfl) ⟨1927769, by rfl⟩ : syracuseStep 2570359 = 3855539) B3855539
theorem B3427145 : Blo 2283435 3427145 := bstep (se 2 (by rfl) ⟨1285179, by rfl⟩ : syracuseStep 3427145 = 2570359) B2570359
theorem B2284763 : Blo 2283435 2284763 := bstep (se 1 (by rfl) ⟨1713572, by rfl⟩ : syracuseStep 2284763 = 3427145) B3427145
theorem B3253117 : Blo 2283435 3253117 := bbase (se 3 (by rfl) ⟨609959, by rfl⟩ : syracuseStep 3253117 = 1219919) (by norm_num)
theorem B4337489 : Blo 2283435 4337489 := bstep (se 2 (by rfl) ⟨1626558, by rfl⟩ : syracuseStep 4337489 = 3253117) B3253117
theorem B11566637 : Blo 2283435 11566637 := bstep (se 3 (by rfl) ⟨2168744, by rfl⟩ : syracuseStep 11566637 = 4337489) B4337489
theorem B7711091 : Blo 2283435 7711091 := bstep (se 1 (by rfl) ⟨5783318, by rfl⟩ : syracuseStep 7711091 = 11566637) B11566637
theorem B5140727 : Blo 2283435 5140727 := bstep (se 1 (by rfl) ⟨3855545, by rfl⟩ : syracuseStep 5140727 = 7711091) B7711091
theorem B3427151 : Blo 2283435 3427151 := bstep (se 1 (by rfl) ⟨2570363, by rfl⟩ : syracuseStep 3427151 = 5140727) B5140727
theorem B2284767 : Blo 2283435 2284767 := bstep (se 1 (by rfl) ⟨1713575, by rfl⟩ : syracuseStep 2284767 = 3427151) B3427151
theorem B3427157 : Blo 2283435 3427157 := bbase (se 9 (by rfl) ⟨10040, by rfl⟩ : syracuseStep 3427157 = 20081) (by norm_num)
theorem B2284771 : Blo 2283435 2284771 := bstep (se 1 (by rfl) ⟨1713578, by rfl⟩ : syracuseStep 2284771 = 3427157) B3427157
theorem B4879693 : Blo 2283435 4879693 := bbase (se 3 (by rfl) ⟨914942, by rfl⟩ : syracuseStep 4879693 = 1829885) (by norm_num)
theorem B6506257 : Blo 2283435 6506257 := bstep (se 2 (by rfl) ⟨2439846, by rfl⟩ : syracuseStep 6506257 = 4879693) B4879693
theorem B8675009 : Blo 2283435 8675009 := bstep (se 2 (by rfl) ⟨3253128, by rfl⟩ : syracuseStep 8675009 = 6506257) B6506257
theorem B5783339 : Blo 2283435 5783339 := bstep (se 1 (by rfl) ⟨4337504, by rfl⟩ : syracuseStep 5783339 = 8675009) B8675009
theorem B3855559 : Blo 2283435 3855559 := bstep (se 1 (by rfl) ⟨2891669, by rfl⟩ : syracuseStep 3855559 = 5783339) B5783339
theorem B5140745 : Blo 2283435 5140745 := bstep (se 2 (by rfl) ⟨1927779, by rfl⟩ : syracuseStep 5140745 = 3855559) B3855559
theorem B3427163 : Blo 2283435 3427163 := bstep (se 1 (by rfl) ⟨2570372, by rfl⟩ : syracuseStep 3427163 = 5140745) B5140745
theorem B2284775 : Blo 2283435 2284775 := bstep (se 1 (by rfl) ⟨1713581, by rfl⟩ : syracuseStep 2284775 = 3427163) B3427163
theorem B2570377 : Blo 2283435 2570377 := bbase (se 2 (by rfl) ⟨963891, by rfl⟩ : syracuseStep 2570377 = 1927783) (by norm_num)
theorem B3427169 : Blo 2283435 3427169 := bstep (se 2 (by rfl) ⟨1285188, by rfl⟩ : syracuseStep 3427169 = 2570377) B2570377
theorem B2284779 : Blo 2283435 2284779 := bstep (se 1 (by rfl) ⟨1713584, by rfl⟩ : syracuseStep 2284779 = 3427169) B3427169
theorem B2931133 : Blo 2283435 2931133 := bbase (se 3 (by rfl) ⟨549587, by rfl⟩ : syracuseStep 2931133 = 1099175) (by norm_num)
theorem B3908177 : Blo 2283435 3908177 := bstep (se 2 (by rfl) ⟨1465566, by rfl⟩ : syracuseStep 3908177 = 2931133) B2931133
theorem B2605451 : Blo 2283435 2605451 := bstep (se 1 (by rfl) ⟨1954088, by rfl⟩ : syracuseStep 2605451 = 3908177) B3908177
theorem B6947869 : Blo 2283435 6947869 := bstep (se 3 (by rfl) ⟨1302725, by rfl⟩ : syracuseStep 6947869 = 2605451) B2605451
theorem B9263825 : Blo 2283435 9263825 := bstep (se 2 (by rfl) ⟨3473934, by rfl⟩ : syracuseStep 9263825 = 6947869) B6947869
theorem B6175883 : Blo 2283435 6175883 := bstep (se 1 (by rfl) ⟨4631912, by rfl⟩ : syracuseStep 6175883 = 9263825) B9263825
theorem B16469021 : Blo 2283435 16469021 := bstep (se 3 (by rfl) ⟨3087941, by rfl⟩ : syracuseStep 16469021 = 6175883) B6175883
theorem B43917389 : Blo 2283435 43917389 := bstep (se 3 (by rfl) ⟨8234510, by rfl⟩ : syracuseStep 43917389 = 16469021) B16469021
theorem B29278259 : Blo 2283435 29278259 := bstep (se 1 (by rfl) ⟨21958694, by rfl⟩ : syracuseStep 29278259 = 43917389) B43917389
theorem B19518839 : Blo 2283435 19518839 := bstep (se 1 (by rfl) ⟨14639129, by rfl⟩ : syracuseStep 19518839 = 29278259) B29278259
theorem B13012559 : Blo 2283435 13012559 := bstep (se 1 (by rfl) ⟨9759419, by rfl⟩ : syracuseStep 13012559 = 19518839) B19518839
theorem B8675039 : Blo 2283435 8675039 := bstep (se 1 (by rfl) ⟨6506279, by rfl⟩ : syracuseStep 8675039 = 13012559) B13012559
theorem B5783359 : Blo 2283435 5783359 := bstep (se 1 (by rfl) ⟨4337519, by rfl⟩ : syracuseStep 5783359 = 8675039) B8675039
theorem B7711145 : Blo 2283435 7711145 := bstep (se 2 (by rfl) ⟨2891679, by rfl⟩ : syracuseStep 7711145 = 5783359) B5783359
theorem B5140763 : Blo 2283435 5140763 := bstep (se 1 (by rfl) ⟨3855572, by rfl⟩ : syracuseStep 5140763 = 7711145) B7711145
theorem B3427175 : Blo 2283435 3427175 := bstep (se 1 (by rfl) ⟨2570381, by rfl⟩ : syracuseStep 3427175 = 5140763) B5140763
theorem B2284783 : Blo 2283435 2284783 := bstep (se 1 (by rfl) ⟨1713587, by rfl⟩ : syracuseStep 2284783 = 3427175) B3427175
theorem B3427181 : Blo 2283435 3427181 := bbase (se 3 (by rfl) ⟨642596, by rfl⟩ : syracuseStep 3427181 = 1285193) (by norm_num)
theorem B2284787 : Blo 2283435 2284787 := bstep (se 1 (by rfl) ⟨1713590, by rfl⟩ : syracuseStep 2284787 = 3427181) B3427181
theorem B5140781 : Blo 2283435 5140781 := bbase (se 3 (by rfl) ⟨963896, by rfl⟩ : syracuseStep 5140781 = 1927793) (by norm_num)
theorem B3427187 : Blo 2283435 3427187 := bstep (se 1 (by rfl) ⟨2570390, by rfl⟩ : syracuseStep 3427187 = 5140781) B5140781
theorem B2284791 : Blo 2283435 2284791 := bstep (se 1 (by rfl) ⟨1713593, by rfl⟩ : syracuseStep 2284791 = 3427187) B3427187
theorem B7319605 : Blo 2283435 7319605 := bbase (se 5 (by rfl) ⟨343106, by rfl⟩ : syracuseStep 7319605 = 686213) (by norm_num)
theorem B9759473 : Blo 2283435 9759473 := bstep (se 2 (by rfl) ⟨3659802, by rfl⟩ : syracuseStep 9759473 = 7319605) B7319605
theorem B6506315 : Blo 2283435 6506315 := bstep (se 1 (by rfl) ⟨4879736, by rfl⟩ : syracuseStep 6506315 = 9759473) B9759473
theorem B4337543 : Blo 2283435 4337543 := bstep (se 1 (by rfl) ⟨3253157, by rfl⟩ : syracuseStep 4337543 = 6506315) B6506315
theorem B2891695 : Blo 2283435 2891695 := bstep (se 1 (by rfl) ⟨2168771, by rfl⟩ : syracuseStep 2891695 = 4337543) B4337543
theorem B3855593 : Blo 2283435 3855593 := bstep (se 2 (by rfl) ⟨1445847, by rfl⟩ : syracuseStep 3855593 = 2891695) B2891695
theorem B2570395 : Blo 2283435 2570395 := bstep (se 1 (by rfl) ⟨1927796, by rfl⟩ : syracuseStep 2570395 = 3855593) B3855593
theorem B3427193 : Blo 2283435 3427193 := bstep (se 2 (by rfl) ⟨1285197, by rfl⟩ : syracuseStep 3427193 = 2570395) B2570395
theorem B2284795 : Blo 2283435 2284795 := bstep (se 1 (by rfl) ⟨1713596, by rfl⟩ : syracuseStep 2284795 = 3427193) B3427193
theorem B6595093 : Blo 2283435 6595093 := bbase (se 6 (by rfl) ⟨154572, by rfl⟩ : syracuseStep 6595093 = 309145) (by norm_num)
theorem B35173829 : Blo 2283435 35173829 := bstep (se 4 (by rfl) ⟨3297546, by rfl⟩ : syracuseStep 35173829 = 6595093) B6595093
theorem B23449219 : Blo 2283435 23449219 := bstep (se 1 (by rfl) ⟨17586914, by rfl⟩ : syracuseStep 23449219 = 35173829) B35173829
theorem B125062501 : Blo 2283435 125062501 := bstep (se 4 (by rfl) ⟨11724609, by rfl⟩ : syracuseStep 125062501 = 23449219) B23449219
theorem B166750001 : Blo 2283435 166750001 := bstep (se 2 (by rfl) ⟨62531250, by rfl⟩ : syracuseStep 166750001 = 125062501) B125062501
theorem B111166667 : Blo 2283435 111166667 := bstep (se 1 (by rfl) ⟨83375000, by rfl⟩ : syracuseStep 111166667 = 166750001) B166750001
theorem B74111111 : Blo 2283435 74111111 := bstep (se 1 (by rfl) ⟨55583333, by rfl⟩ : syracuseStep 74111111 = 111166667) B111166667
theorem B49407407 : Blo 2283435 49407407 := bstep (se 1 (by rfl) ⟨37055555, by rfl⟩ : syracuseStep 49407407 = 74111111) B74111111
theorem B32938271 : Blo 2283435 32938271 := bstep (se 1 (by rfl) ⟨24703703, by rfl⟩ : syracuseStep 32938271 = 49407407) B49407407
theorem B21958847 : Blo 2283435 21958847 := bstep (se 1 (by rfl) ⟨16469135, by rfl⟩ : syracuseStep 21958847 = 32938271) B32938271
theorem B14639231 : Blo 2283435 14639231 := bstep (se 1 (by rfl) ⟨10979423, by rfl⟩ : syracuseStep 14639231 = 21958847) B21958847
theorem B39037949 : Blo 2283435 39037949 := bstep (se 3 (by rfl) ⟨7319615, by rfl⟩ : syracuseStep 39037949 = 14639231) B14639231
theorem B26025299 : Blo 2283435 26025299 := bstep (se 1 (by rfl) ⟨19518974, by rfl⟩ : syracuseStep 26025299 = 39037949) B39037949
theorem B17350199 : Blo 2283435 17350199 := bstep (se 1 (by rfl) ⟨13012649, by rfl⟩ : syracuseStep 17350199 = 26025299) B26025299
theorem B11566799 : Blo 2283435 11566799 := bstep (se 1 (by rfl) ⟨8675099, by rfl⟩ : syracuseStep 11566799 = 17350199) B17350199
theorem B7711199 : Blo 2283435 7711199 := bstep (se 1 (by rfl) ⟨5783399, by rfl⟩ : syracuseStep 7711199 = 11566799) B11566799
theorem B5140799 : Blo 2283435 5140799 := bstep (se 1 (by rfl) ⟨3855599, by rfl⟩ : syracuseStep 5140799 = 7711199) B7711199
theorem B3427199 : Blo 2283435 3427199 := bstep (se 1 (by rfl) ⟨2570399, by rfl⟩ : syracuseStep 3427199 = 5140799) B5140799
theorem B2284799 : Blo 2283435 2284799 := bstep (se 1 (by rfl) ⟨1713599, by rfl⟩ : syracuseStep 2284799 = 3427199) B3427199
theorem B3427205 : Blo 2283435 3427205 := bbase (se 4 (by rfl) ⟨321300, by rfl⟩ : syracuseStep 3427205 = 642601) (by norm_num)
theorem B2284803 : Blo 2283435 2284803 := bstep (se 1 (by rfl) ⟨1713602, by rfl⟩ : syracuseStep 2284803 = 3427205) B3427205
theorem B3855613 : Blo 2283435 3855613 := bbase (se 3 (by rfl) ⟨722927, by rfl⟩ : syracuseStep 3855613 = 1445855) (by norm_num)
theorem B5140817 : Blo 2283435 5140817 := bstep (se 2 (by rfl) ⟨1927806, by rfl⟩ : syracuseStep 5140817 = 3855613) B3855613
theorem B3427211 : Blo 2283435 3427211 := bstep (se 1 (by rfl) ⟨2570408, by rfl⟩ : syracuseStep 3427211 = 5140817) B5140817
theorem B2284807 : Blo 2283435 2284807 := bstep (se 1 (by rfl) ⟨1713605, by rfl⟩ : syracuseStep 2284807 = 3427211) B3427211
theorem B2570413 : Blo 2283435 2570413 := bbase (se 3 (by rfl) ⟨481952, by rfl⟩ : syracuseStep 2570413 = 963905) (by norm_num)
theorem B3427217 : Blo 2283435 3427217 := bstep (se 2 (by rfl) ⟨1285206, by rfl⟩ : syracuseStep 3427217 = 2570413) B2570413
theorem B2284811 : Blo 2283435 2284811 := bstep (se 1 (by rfl) ⟨1713608, by rfl⟩ : syracuseStep 2284811 = 3427217) B3427217
theorem B7711253 : Blo 2283435 7711253 := bbase (se 6 (by rfl) ⟨180732, by rfl⟩ : syracuseStep 7711253 = 361465) (by norm_num)
theorem B5140835 : Blo 2283435 5140835 := bstep (se 1 (by rfl) ⟨3855626, by rfl⟩ : syracuseStep 5140835 = 7711253) B7711253
theorem B3427223 : Blo 2283435 3427223 := bstep (se 1 (by rfl) ⟨2570417, by rfl⟩ : syracuseStep 3427223 = 5140835) B5140835
theorem B2284815 : Blo 2283435 2284815 := bstep (se 1 (by rfl) ⟨1713611, by rfl⟩ : syracuseStep 2284815 = 3427223) B3427223
theorem B3427229 : Blo 2283435 3427229 := bbase (se 3 (by rfl) ⟨642605, by rfl⟩ : syracuseStep 3427229 = 1285211) (by norm_num)
theorem B2284819 : Blo 2283435 2284819 := bstep (se 1 (by rfl) ⟨1713614, by rfl⟩ : syracuseStep 2284819 = 3427229) B3427229
theorem B5140853 : Blo 2283435 5140853 := bbase (se 5 (by rfl) ⟨240977, by rfl⟩ : syracuseStep 5140853 = 481955) (by norm_num)
theorem B3427235 : Blo 2283435 3427235 := bstep (se 1 (by rfl) ⟨2570426, by rfl⟩ : syracuseStep 3427235 = 5140853) B5140853
theorem B2284823 : Blo 2283435 2284823 := bstep (se 1 (by rfl) ⟨1713617, by rfl⟩ : syracuseStep 2284823 = 3427235) B3427235
theorem B14639413 : Blo 2283435 14639413 := bbase (se 5 (by rfl) ⟨686222, by rfl⟩ : syracuseStep 14639413 = 1372445) (by norm_num)
theorem B19519217 : Blo 2283435 19519217 := bstep (se 2 (by rfl) ⟨7319706, by rfl⟩ : syracuseStep 19519217 = 14639413) B14639413
theorem B13012811 : Blo 2283435 13012811 := bstep (se 1 (by rfl) ⟨9759608, by rfl⟩ : syracuseStep 13012811 = 19519217) B19519217
theorem B8675207 : Blo 2283435 8675207 := bstep (se 1 (by rfl) ⟨6506405, by rfl⟩ : syracuseStep 8675207 = 13012811) B13012811
theorem B5783471 : Blo 2283435 5783471 := bstep (se 1 (by rfl) ⟨4337603, by rfl⟩ : syracuseStep 5783471 = 8675207) B8675207
theorem B3855647 : Blo 2283435 3855647 := bstep (se 1 (by rfl) ⟨2891735, by rfl⟩ : syracuseStep 3855647 = 5783471) B5783471
theorem B2570431 : Blo 2283435 2570431 := bstep (se 1 (by rfl) ⟨1927823, by rfl⟩ : syracuseStep 2570431 = 3855647) B3855647
theorem B3427241 : Blo 2283435 3427241 := bstep (se 2 (by rfl) ⟨1285215, by rfl⟩ : syracuseStep 3427241 = 2570431) B2570431
theorem B2284827 : Blo 2283435 2284827 := bstep (se 1 (by rfl) ⟨1713620, by rfl⟩ : syracuseStep 2284827 = 3427241) B3427241
theorem B8675221 : Blo 2283435 8675221 := bbase (se 6 (by rfl) ⟨203325, by rfl⟩ : syracuseStep 8675221 = 406651) (by norm_num)
theorem B11566961 : Blo 2283435 11566961 := bstep (se 2 (by rfl) ⟨4337610, by rfl⟩ : syracuseStep 11566961 = 8675221) B8675221
theorem B7711307 : Blo 2283435 7711307 := bstep (se 1 (by rfl) ⟨5783480, by rfl⟩ : syracuseStep 7711307 = 11566961) B11566961
theorem B5140871 : Blo 2283435 5140871 := bstep (se 1 (by rfl) ⟨3855653, by rfl⟩ : syracuseStep 5140871 = 7711307) B7711307
theorem B3427247 : Blo 2283435 3427247 := bstep (se 1 (by rfl) ⟨2570435, by rfl⟩ : syracuseStep 3427247 = 5140871) B5140871
theorem B2284831 : Blo 2283435 2284831 := bstep (se 1 (by rfl) ⟨1713623, by rfl⟩ : syracuseStep 2284831 = 3427247) B3427247
theorem B3427253 : Blo 2283435 3427253 := bbase (se 5 (by rfl) ⟨160652, by rfl⟩ : syracuseStep 3427253 = 321305) (by norm_num)
theorem B2284835 : Blo 2283435 2284835 := bstep (se 1 (by rfl) ⟨1713626, by rfl⟩ : syracuseStep 2284835 = 3427253) B3427253
theorem B5783501 : Blo 2283435 5783501 := bbase (se 3 (by rfl) ⟨1084406, by rfl⟩ : syracuseStep 5783501 = 2168813) (by norm_num)
theorem B3855667 : Blo 2283435 3855667 := bstep (se 1 (by rfl) ⟨2891750, by rfl⟩ : syracuseStep 3855667 = 5783501) B5783501
theorem B5140889 : Blo 2283435 5140889 := bstep (se 2 (by rfl) ⟨1927833, by rfl⟩ : syracuseStep 5140889 = 3855667) B3855667
theorem B3427259 : Blo 2283435 3427259 := bstep (se 1 (by rfl) ⟨2570444, by rfl⟩ : syracuseStep 3427259 = 5140889) B5140889
theorem B2284839 : Blo 2283435 2284839 := bstep (se 1 (by rfl) ⟨1713629, by rfl⟩ : syracuseStep 2284839 = 3427259) B3427259
theorem B2570449 : Blo 2283435 2570449 := bbase (se 2 (by rfl) ⟨963918, by rfl⟩ : syracuseStep 2570449 = 1927837) (by norm_num)
theorem B3427265 : Blo 2283435 3427265 := bstep (se 2 (by rfl) ⟨1285224, by rfl⟩ : syracuseStep 3427265 = 2570449) B2570449
theorem B2284843 : Blo 2283435 2284843 := bstep (se 1 (by rfl) ⟨1713632, by rfl⟩ : syracuseStep 2284843 = 3427265) B3427265
theorem B42257173 : Blo 2283435 42257173 := bbase (se 6 (by rfl) ⟨990402, by rfl⟩ : syracuseStep 42257173 = 1980805) (by norm_num)
theorem B56342897 : Blo 2283435 56342897 := bstep (se 2 (by rfl) ⟨21128586, by rfl⟩ : syracuseStep 56342897 = 42257173) B42257173
theorem B37561931 : Blo 2283435 37561931 := bstep (se 1 (by rfl) ⟨28171448, by rfl⟩ : syracuseStep 37561931 = 56342897) B56342897
theorem B25041287 : Blo 2283435 25041287 := bstep (se 1 (by rfl) ⟨18780965, by rfl⟩ : syracuseStep 25041287 = 37561931) B37561931
theorem B16694191 : Blo 2283435 16694191 := bstep (se 1 (by rfl) ⟨12520643, by rfl⟩ : syracuseStep 16694191 = 25041287) B25041287
theorem B22258921 : Blo 2283435 22258921 := bstep (se 2 (by rfl) ⟨8347095, by rfl⟩ : syracuseStep 22258921 = 16694191) B16694191
theorem B29678561 : Blo 2283435 29678561 := bstep (se 2 (by rfl) ⟨11129460, by rfl⟩ : syracuseStep 29678561 = 22258921) B22258921
theorem B19785707 : Blo 2283435 19785707 := bstep (se 1 (by rfl) ⟨14839280, by rfl⟩ : syracuseStep 19785707 = 29678561) B29678561
theorem B13190471 : Blo 2283435 13190471 := bstep (se 1 (by rfl) ⟨9892853, by rfl⟩ : syracuseStep 13190471 = 19785707) B19785707
theorem B8793647 : Blo 2283435 8793647 := bstep (se 1 (by rfl) ⟨6595235, by rfl⟩ : syracuseStep 8793647 = 13190471) B13190471
theorem B5862431 : Blo 2283435 5862431 := bstep (se 1 (by rfl) ⟨4396823, by rfl⟩ : syracuseStep 5862431 = 8793647) B8793647
theorem B3908287 : Blo 2283435 3908287 := bstep (se 1 (by rfl) ⟨2931215, by rfl⟩ : syracuseStep 3908287 = 5862431) B5862431
theorem B5211049 : Blo 2283435 5211049 := bstep (se 2 (by rfl) ⟨1954143, by rfl⟩ : syracuseStep 5211049 = 3908287) B3908287
theorem B6948065 : Blo 2283435 6948065 := bstep (se 2 (by rfl) ⟨2605524, by rfl⟩ : syracuseStep 6948065 = 5211049) B5211049
theorem B18528173 : Blo 2283435 18528173 := bstep (se 3 (by rfl) ⟨3474032, by rfl⟩ : syracuseStep 18528173 = 6948065) B6948065
theorem B12352115 : Blo 2283435 12352115 := bstep (se 1 (by rfl) ⟨9264086, by rfl⟩ : syracuseStep 12352115 = 18528173) B18528173
theorem B8234743 : Blo 2283435 8234743 := bstep (se 1 (by rfl) ⟨6176057, by rfl⟩ : syracuseStep 8234743 = 12352115) B12352115
theorem B10979657 : Blo 2283435 10979657 := bstep (se 2 (by rfl) ⟨4117371, by rfl⟩ : syracuseStep 10979657 = 8234743) B8234743
theorem B7319771 : Blo 2283435 7319771 := bstep (se 1 (by rfl) ⟨5489828, by rfl⟩ : syracuseStep 7319771 = 10979657) B10979657
theorem B4879847 : Blo 2283435 4879847 := bstep (se 1 (by rfl) ⟨3659885, by rfl⟩ : syracuseStep 4879847 = 7319771) B7319771
theorem B3253231 : Blo 2283435 3253231 := bstep (se 1 (by rfl) ⟨2439923, by rfl⟩ : syracuseStep 3253231 = 4879847) B4879847
theorem B4337641 : Blo 2283435 4337641 := bstep (se 2 (by rfl) ⟨1626615, by rfl⟩ : syracuseStep 4337641 = 3253231) B3253231
theorem B5783521 : Blo 2283435 5783521 := bstep (se 2 (by rfl) ⟨2168820, by rfl⟩ : syracuseStep 5783521 = 4337641) B4337641
theorem B7711361 : Blo 2283435 7711361 := bstep (se 2 (by rfl) ⟨2891760, by rfl⟩ : syracuseStep 7711361 = 5783521) B5783521
theorem B5140907 : Blo 2283435 5140907 := bstep (se 1 (by rfl) ⟨3855680, by rfl⟩ : syracuseStep 5140907 = 7711361) B7711361
theorem B3427271 : Blo 2283435 3427271 := bstep (se 1 (by rfl) ⟨2570453, by rfl⟩ : syracuseStep 3427271 = 5140907) B5140907
theorem B2284847 : Blo 2283435 2284847 := bstep (se 1 (by rfl) ⟨1713635, by rfl⟩ : syracuseStep 2284847 = 3427271) B3427271
theorem B3427277 : Blo 2283435 3427277 := bbase (se 3 (by rfl) ⟨642614, by rfl⟩ : syracuseStep 3427277 = 1285229) (by norm_num)
theorem B2284851 : Blo 2283435 2284851 := bstep (se 1 (by rfl) ⟨1713638, by rfl⟩ : syracuseStep 2284851 = 3427277) B3427277
theorem B5140925 : Blo 2283435 5140925 := bbase (se 3 (by rfl) ⟨963923, by rfl⟩ : syracuseStep 5140925 = 1927847) (by norm_num)
theorem B3427283 : Blo 2283435 3427283 := bstep (se 1 (by rfl) ⟨2570462, by rfl⟩ : syracuseStep 3427283 = 5140925) B5140925
theorem B2284855 : Blo 2283435 2284855 := bstep (se 1 (by rfl) ⟨1713641, by rfl⟩ : syracuseStep 2284855 = 3427283) B3427283
theorem B3855701 : Blo 2283435 3855701 := bbase (se 15 (by rfl) ⟨176, by rfl⟩ : syracuseStep 3855701 = 353) (by norm_num)
theorem B2570467 : Blo 2283435 2570467 := bstep (se 1 (by rfl) ⟨1927850, by rfl⟩ : syracuseStep 2570467 = 3855701) B3855701
theorem B3427289 : Blo 2283435 3427289 := bstep (se 2 (by rfl) ⟨1285233, by rfl⟩ : syracuseStep 3427289 = 2570467) B2570467
theorem B2284859 : Blo 2283435 2284859 := bstep (se 1 (by rfl) ⟨1713644, by rfl⟩ : syracuseStep 2284859 = 3427289) B3427289
theorem B2744933 : Blo 2283435 2744933 := bbase (se 4 (by rfl) ⟨257337, by rfl⟩ : syracuseStep 2744933 = 514675) (by norm_num)
theorem B7319821 : Blo 2283435 7319821 := bstep (se 3 (by rfl) ⟨1372466, by rfl⟩ : syracuseStep 7319821 = 2744933) B2744933
theorem B9759761 : Blo 2283435 9759761 := bstep (se 2 (by rfl) ⟨3659910, by rfl⟩ : syracuseStep 9759761 = 7319821) B7319821
theorem B6506507 : Blo 2283435 6506507 := bstep (se 1 (by rfl) ⟨4879880, by rfl⟩ : syracuseStep 6506507 = 9759761) B9759761
theorem B17350685 : Blo 2283435 17350685 := bstep (se 3 (by rfl) ⟨3253253, by rfl⟩ : syracuseStep 17350685 = 6506507) B6506507
theorem B11567123 : Blo 2283435 11567123 := bstep (se 1 (by rfl) ⟨8675342, by rfl⟩ : syracuseStep 11567123 = 17350685) B17350685
theorem B7711415 : Blo 2283435 7711415 := bstep (se 1 (by rfl) ⟨5783561, by rfl⟩ : syracuseStep 7711415 = 11567123) B11567123
theorem B5140943 : Blo 2283435 5140943 := bstep (se 1 (by rfl) ⟨3855707, by rfl⟩ : syracuseStep 5140943 = 7711415) B7711415
theorem B3427295 : Blo 2283435 3427295 := bstep (se 1 (by rfl) ⟨2570471, by rfl⟩ : syracuseStep 3427295 = 5140943) B5140943
theorem B2284863 : Blo 2283435 2284863 := bstep (se 1 (by rfl) ⟨1713647, by rfl⟩ : syracuseStep 2284863 = 3427295) B3427295
theorem B3427301 : Blo 2283435 3427301 := bbase (se 4 (by rfl) ⟨321309, by rfl⟩ : syracuseStep 3427301 = 642619) (by norm_num)
theorem B2284867 : Blo 2283435 2284867 := bstep (se 1 (by rfl) ⟨1713650, by rfl⟩ : syracuseStep 2284867 = 3427301) B3427301
theorem B9759797 : Blo 2283435 9759797 := bbase (se 5 (by rfl) ⟨457490, by rfl⟩ : syracuseStep 9759797 = 914981) (by norm_num)
theorem B6506531 : Blo 2283435 6506531 := bstep (se 1 (by rfl) ⟨4879898, by rfl⟩ : syracuseStep 6506531 = 9759797) B9759797
theorem B4337687 : Blo 2283435 4337687 := bstep (se 1 (by rfl) ⟨3253265, by rfl⟩ : syracuseStep 4337687 = 6506531) B6506531
theorem B2891791 : Blo 2283435 2891791 := bstep (se 1 (by rfl) ⟨2168843, by rfl⟩ : syracuseStep 2891791 = 4337687) B4337687
theorem B3855721 : Blo 2283435 3855721 := bstep (se 2 (by rfl) ⟨1445895, by rfl⟩ : syracuseStep 3855721 = 2891791) B2891791
theorem B5140961 : Blo 2283435 5140961 := bstep (se 2 (by rfl) ⟨1927860, by rfl⟩ : syracuseStep 5140961 = 3855721) B3855721
theorem B3427307 : Blo 2283435 3427307 := bstep (se 1 (by rfl) ⟨2570480, by rfl⟩ : syracuseStep 3427307 = 5140961) B5140961
theorem B2284871 : Blo 2283435 2284871 := bstep (se 1 (by rfl) ⟨1713653, by rfl⟩ : syracuseStep 2284871 = 3427307) B3427307
theorem B2570485 : Blo 2283435 2570485 := bbase (se 5 (by rfl) ⟨120491, by rfl⟩ : syracuseStep 2570485 = 240983) (by norm_num)
theorem B3427313 : Blo 2283435 3427313 := bstep (se 2 (by rfl) ⟨1285242, by rfl⟩ : syracuseStep 3427313 = 2570485) B2570485
theorem B2284875 : Blo 2283435 2284875 := bstep (se 1 (by rfl) ⟨1713656, by rfl⟩ : syracuseStep 2284875 = 3427313) B3427313
theorem B2891801 : Blo 2283435 2891801 := bbase (se 2 (by rfl) ⟨1084425, by rfl⟩ : syracuseStep 2891801 = 2168851) (by norm_num)
theorem B7711469 : Blo 2283435 7711469 := bstep (se 3 (by rfl) ⟨1445900, by rfl⟩ : syracuseStep 7711469 = 2891801) B2891801
theorem B5140979 : Blo 2283435 5140979 := bstep (se 1 (by rfl) ⟨3855734, by rfl⟩ : syracuseStep 5140979 = 7711469) B7711469
theorem B3427319 : Blo 2283435 3427319 := bstep (se 1 (by rfl) ⟨2570489, by rfl⟩ : syracuseStep 3427319 = 5140979) B5140979
theorem B2284879 : Blo 2283435 2284879 := bstep (se 1 (by rfl) ⟨1713659, by rfl⟩ : syracuseStep 2284879 = 3427319) B3427319
theorem B3427325 : Blo 2283435 3427325 := bbase (se 3 (by rfl) ⟨642623, by rfl⟩ : syracuseStep 3427325 = 1285247) (by norm_num)
theorem B2284883 : Blo 2283435 2284883 := bstep (se 1 (by rfl) ⟨1713662, by rfl⟩ : syracuseStep 2284883 = 3427325) B3427325
theorem B5140997 : Blo 2283435 5140997 := bbase (se 4 (by rfl) ⟨481968, by rfl⟩ : syracuseStep 5140997 = 963937) (by norm_num)
theorem B3427331 : Blo 2283435 3427331 := bstep (se 1 (by rfl) ⟨2570498, by rfl⟩ : syracuseStep 3427331 = 5140997) B5140997
theorem B2284887 : Blo 2283435 2284887 := bstep (se 1 (by rfl) ⟨1713665, by rfl⟩ : syracuseStep 2284887 = 3427331) B3427331
theorem B4337725 : Blo 2283435 4337725 := bbase (se 3 (by rfl) ⟨813323, by rfl⟩ : syracuseStep 4337725 = 1626647) (by norm_num)
theorem B5783633 : Blo 2283435 5783633 := bstep (se 2 (by rfl) ⟨2168862, by rfl⟩ : syracuseStep 5783633 = 4337725) B4337725
theorem B3855755 : Blo 2283435 3855755 := bstep (se 1 (by rfl) ⟨2891816, by rfl⟩ : syracuseStep 3855755 = 5783633) B5783633
theorem B2570503 : Blo 2283435 2570503 := bstep (se 1 (by rfl) ⟨1927877, by rfl⟩ : syracuseStep 2570503 = 3855755) B3855755
theorem B3427337 : Blo 2283435 3427337 := bstep (se 2 (by rfl) ⟨1285251, by rfl⟩ : syracuseStep 3427337 = 2570503) B2570503
theorem B2284891 : Blo 2283435 2284891 := bstep (se 1 (by rfl) ⟨1713668, by rfl⟩ : syracuseStep 2284891 = 3427337) B3427337
theorem B11567285 : Blo 2283435 11567285 := bbase (se 5 (by rfl) ⟨542216, by rfl⟩ : syracuseStep 11567285 = 1084433) (by norm_num)
theorem B7711523 : Blo 2283435 7711523 := bstep (se 1 (by rfl) ⟨5783642, by rfl⟩ : syracuseStep 7711523 = 11567285) B11567285
theorem B5141015 : Blo 2283435 5141015 := bstep (se 1 (by rfl) ⟨3855761, by rfl⟩ : syracuseStep 5141015 = 7711523) B7711523
theorem B3427343 : Blo 2283435 3427343 := bstep (se 1 (by rfl) ⟨2570507, by rfl⟩ : syracuseStep 3427343 = 5141015) B5141015
theorem B2284895 : Blo 2283435 2284895 := bstep (se 1 (by rfl) ⟨1713671, by rfl⟩ : syracuseStep 2284895 = 3427343) B3427343
theorem B3427349 : Blo 2283435 3427349 := bbase (se 6 (by rfl) ⟨80328, by rfl⟩ : syracuseStep 3427349 = 160657) (by norm_num)
theorem B2284899 : Blo 2283435 2284899 := bstep (se 1 (by rfl) ⟨1713674, by rfl⟩ : syracuseStep 2284899 = 3427349) B3427349
theorem B2473273 : Blo 2283435 2473273 := bbase (se 2 (by rfl) ⟨927477, by rfl⟩ : syracuseStep 2473273 = 1854955) (by norm_num)
theorem B3297697 : Blo 2283435 3297697 := bstep (se 2 (by rfl) ⟨1236636, by rfl⟩ : syracuseStep 3297697 = 2473273) B2473273
theorem B70350869 : Blo 2283435 70350869 := bstep (se 6 (by rfl) ⟨1648848, by rfl⟩ : syracuseStep 70350869 = 3297697) B3297697
theorem B187602317 : Blo 2283435 187602317 := bstep (se 3 (by rfl) ⟨35175434, by rfl⟩ : syracuseStep 187602317 = 70350869) B70350869
theorem B125068211 : Blo 2283435 125068211 := bstep (se 1 (by rfl) ⟨93801158, by rfl⟩ : syracuseStep 125068211 = 187602317) B187602317
theorem B83378807 : Blo 2283435 83378807 := bstep (se 1 (by rfl) ⟨62534105, by rfl⟩ : syracuseStep 83378807 = 125068211) B125068211
theorem B55585871 : Blo 2283435 55585871 := bstep (se 1 (by rfl) ⟨41689403, by rfl⟩ : syracuseStep 55585871 = 83378807) B83378807
theorem B37057247 : Blo 2283435 37057247 := bstep (se 1 (by rfl) ⟨27792935, by rfl⟩ : syracuseStep 37057247 = 55585871) B55585871
theorem B24704831 : Blo 2283435 24704831 := bstep (se 1 (by rfl) ⟨18528623, by rfl⟩ : syracuseStep 24704831 = 37057247) B37057247
theorem B16469887 : Blo 2283435 16469887 := bstep (se 1 (by rfl) ⟨12352415, by rfl⟩ : syracuseStep 16469887 = 24704831) B24704831
theorem B21959849 : Blo 2283435 21959849 := bstep (se 2 (by rfl) ⟨8234943, by rfl⟩ : syracuseStep 21959849 = 16469887) B16469887
theorem B14639899 : Blo 2283435 14639899 := bstep (se 1 (by rfl) ⟨10979924, by rfl⟩ : syracuseStep 14639899 = 21959849) B21959849
theorem B19519865 : Blo 2283435 19519865 := bstep (se 2 (by rfl) ⟨7319949, by rfl⟩ : syracuseStep 19519865 = 14639899) B14639899
theorem B13013243 : Blo 2283435 13013243 := bstep (se 1 (by rfl) ⟨9759932, by rfl⟩ : syracuseStep 13013243 = 19519865) B19519865
theorem B8675495 : Blo 2283435 8675495 := bstep (se 1 (by rfl) ⟨6506621, by rfl⟩ : syracuseStep 8675495 = 13013243) B13013243
theorem B5783663 : Blo 2283435 5783663 := bstep (se 1 (by rfl) ⟨4337747, by rfl⟩ : syracuseStep 5783663 = 8675495) B8675495
theorem B3855775 : Blo 2283435 3855775 := bstep (se 1 (by rfl) ⟨2891831, by rfl⟩ : syracuseStep 3855775 = 5783663) B5783663
theorem B5141033 : Blo 2283435 5141033 := bstep (se 2 (by rfl) ⟨1927887, by rfl⟩ : syracuseStep 5141033 = 3855775) B3855775
theorem B3427355 : Blo 2283435 3427355 := bstep (se 1 (by rfl) ⟨2570516, by rfl⟩ : syracuseStep 3427355 = 5141033) B5141033
theorem B2284903 : Blo 2283435 2284903 := bstep (se 1 (by rfl) ⟨1713677, by rfl⟩ : syracuseStep 2284903 = 3427355) B3427355
theorem B2570521 : Blo 2283435 2570521 := bbase (se 2 (by rfl) ⟨963945, by rfl⟩ : syracuseStep 2570521 = 1927891) (by norm_num)
theorem B3427361 : Blo 2283435 3427361 := bstep (se 2 (by rfl) ⟨1285260, by rfl⟩ : syracuseStep 3427361 = 2570521) B2570521
theorem B2284907 : Blo 2283435 2284907 := bstep (se 1 (by rfl) ⟨1713680, by rfl⟩ : syracuseStep 2284907 = 3427361) B3427361
theorem B8675525 : Blo 2283435 8675525 := bbase (se 4 (by rfl) ⟨813330, by rfl⟩ : syracuseStep 8675525 = 1626661) (by norm_num)
theorem B5783683 : Blo 2283435 5783683 := bstep (se 1 (by rfl) ⟨4337762, by rfl⟩ : syracuseStep 5783683 = 8675525) B8675525
theorem B7711577 : Blo 2283435 7711577 := bstep (se 2 (by rfl) ⟨2891841, by rfl⟩ : syracuseStep 7711577 = 5783683) B5783683
theorem B5141051 : Blo 2283435 5141051 := bstep (se 1 (by rfl) ⟨3855788, by rfl⟩ : syracuseStep 5141051 = 7711577) B7711577
theorem B3427367 : Blo 2283435 3427367 := bstep (se 1 (by rfl) ⟨2570525, by rfl⟩ : syracuseStep 3427367 = 5141051) B5141051
theorem B2284911 : Blo 2283435 2284911 := bstep (se 1 (by rfl) ⟨1713683, by rfl⟩ : syracuseStep 2284911 = 3427367) B3427367
theorem B3427373 : Blo 2283435 3427373 := bbase (se 3 (by rfl) ⟨642632, by rfl⟩ : syracuseStep 3427373 = 1285265) (by norm_num)
theorem B2284915 : Blo 2283435 2284915 := bstep (se 1 (by rfl) ⟨1713686, by rfl⟩ : syracuseStep 2284915 = 3427373) B3427373
theorem B5141069 : Blo 2283435 5141069 := bbase (se 3 (by rfl) ⟨963950, by rfl⟩ : syracuseStep 5141069 = 1927901) (by norm_num)
theorem B3427379 : Blo 2283435 3427379 := bstep (se 1 (by rfl) ⟨2570534, by rfl⟩ : syracuseStep 3427379 = 5141069) B5141069
theorem B2284919 : Blo 2283435 2284919 := bstep (se 1 (by rfl) ⟨1713689, by rfl⟩ : syracuseStep 2284919 = 3427379) B3427379
theorem B2891857 : Blo 2283435 2891857 := bbase (se 2 (by rfl) ⟨1084446, by rfl⟩ : syracuseStep 2891857 = 2168893) (by norm_num)
theorem B3855809 : Blo 2283435 3855809 := bstep (se 2 (by rfl) ⟨1445928, by rfl⟩ : syracuseStep 3855809 = 2891857) B2891857
theorem B2570539 : Blo 2283435 2570539 := bstep (se 1 (by rfl) ⟨1927904, by rfl⟩ : syracuseStep 2570539 = 3855809) B3855809
theorem B3427385 : Blo 2283435 3427385 := bstep (se 2 (by rfl) ⟨1285269, by rfl⟩ : syracuseStep 3427385 = 2570539) B2570539
theorem B2284923 : Blo 2283435 2284923 := bstep (se 1 (by rfl) ⟨1713692, by rfl⟩ : syracuseStep 2284923 = 3427385) B3427385
theorem B3660013 : Blo 2283435 3660013 := bbase (se 3 (by rfl) ⟨686252, by rfl⟩ : syracuseStep 3660013 = 1372505) (by norm_num)
theorem B4880017 : Blo 2283435 4880017 := bstep (se 2 (by rfl) ⟨1830006, by rfl⟩ : syracuseStep 4880017 = 3660013) B3660013
theorem B26026757 : Blo 2283435 26026757 := bstep (se 4 (by rfl) ⟨2440008, by rfl⟩ : syracuseStep 26026757 = 4880017) B4880017
theorem B17351171 : Blo 2283435 17351171 := bstep (se 1 (by rfl) ⟨13013378, by rfl⟩ : syracuseStep 17351171 = 26026757) B26026757
theorem B11567447 : Blo 2283435 11567447 := bstep (se 1 (by rfl) ⟨8675585, by rfl⟩ : syracuseStep 11567447 = 17351171) B17351171
theorem B7711631 : Blo 2283435 7711631 := bstep (se 1 (by rfl) ⟨5783723, by rfl⟩ : syracuseStep 7711631 = 11567447) B11567447
theorem B5141087 : Blo 2283435 5141087 := bstep (se 1 (by rfl) ⟨3855815, by rfl⟩ : syracuseStep 5141087 = 7711631) B7711631
theorem B3427391 : Blo 2283435 3427391 := bstep (se 1 (by rfl) ⟨2570543, by rfl⟩ : syracuseStep 3427391 = 5141087) B5141087
theorem B2284927 : Blo 2283435 2284927 := bstep (se 1 (by rfl) ⟨1713695, by rfl⟩ : syracuseStep 2284927 = 3427391) B3427391
theorem B3427397 : Blo 2283435 3427397 := bbase (se 4 (by rfl) ⟨321318, by rfl⟩ : syracuseStep 3427397 = 642637) (by norm_num)
theorem B2284931 : Blo 2283435 2284931 := bstep (se 1 (by rfl) ⟨1713698, by rfl⟩ : syracuseStep 2284931 = 3427397) B3427397
theorem B3855829 : Blo 2283435 3855829 := bbase (se 7 (by rfl) ⟨45185, by rfl⟩ : syracuseStep 3855829 = 90371) (by norm_num)
theorem B5141105 : Blo 2283435 5141105 := bstep (se 2 (by rfl) ⟨1927914, by rfl⟩ : syracuseStep 5141105 = 3855829) B3855829
theorem B3427403 : Blo 2283435 3427403 := bstep (se 1 (by rfl) ⟨2570552, by rfl⟩ : syracuseStep 3427403 = 5141105) B5141105
theorem B2284935 : Blo 2283435 2284935 := bstep (se 1 (by rfl) ⟨1713701, by rfl⟩ : syracuseStep 2284935 = 3427403) B3427403
theorem B2570557 : Blo 2283435 2570557 := bbase (se 3 (by rfl) ⟨481979, by rfl⟩ : syracuseStep 2570557 = 963959) (by norm_num)
theorem B3427409 : Blo 2283435 3427409 := bstep (se 2 (by rfl) ⟨1285278, by rfl⟩ : syracuseStep 3427409 = 2570557) B2570557
theorem B2284939 : Blo 2283435 2284939 := bstep (se 1 (by rfl) ⟨1713704, by rfl⟩ : syracuseStep 2284939 = 3427409) B3427409
theorem B7711685 : Blo 2283435 7711685 := bbase (se 4 (by rfl) ⟨722970, by rfl⟩ : syracuseStep 7711685 = 1445941) (by norm_num)
theorem B5141123 : Blo 2283435 5141123 := bstep (se 1 (by rfl) ⟨3855842, by rfl⟩ : syracuseStep 5141123 = 7711685) B7711685
theorem B3427415 : Blo 2283435 3427415 := bstep (se 1 (by rfl) ⟨2570561, by rfl⟩ : syracuseStep 3427415 = 5141123) B5141123
theorem B2284943 : Blo 2283435 2284943 := bstep (se 1 (by rfl) ⟨1713707, by rfl⟩ : syracuseStep 2284943 = 3427415) B3427415
theorem B3427421 : Blo 2283435 3427421 := bbase (se 3 (by rfl) ⟨642641, by rfl⟩ : syracuseStep 3427421 = 1285283) (by norm_num)
theorem B2284947 : Blo 2283435 2284947 := bstep (se 1 (by rfl) ⟨1713710, by rfl⟩ : syracuseStep 2284947 = 3427421) B3427421
theorem B5141141 : Blo 2283435 5141141 := bbase (se 6 (by rfl) ⟨120495, by rfl⟩ : syracuseStep 5141141 = 240991) (by norm_num)
theorem B3427427 : Blo 2283435 3427427 := bstep (se 1 (by rfl) ⟨2570570, by rfl⟩ : syracuseStep 3427427 = 5141141) B5141141
theorem B2284951 : Blo 2283435 2284951 := bstep (se 1 (by rfl) ⟨1713713, by rfl⟩ : syracuseStep 2284951 = 3427427) B3427427
theorem B5862709 : Blo 2283435 5862709 := bbase (se 5 (by rfl) ⟨274814, by rfl⟩ : syracuseStep 5862709 = 549629) (by norm_num)
theorem B31267781 : Blo 2283435 31267781 := bstep (se 4 (by rfl) ⟨2931354, by rfl⟩ : syracuseStep 31267781 = 5862709) B5862709
theorem B20845187 : Blo 2283435 20845187 := bstep (se 1 (by rfl) ⟨15633890, by rfl⟩ : syracuseStep 20845187 = 31267781) B31267781
theorem B13896791 : Blo 2283435 13896791 := bstep (se 1 (by rfl) ⟨10422593, by rfl⟩ : syracuseStep 13896791 = 20845187) B20845187
theorem B9264527 : Blo 2283435 9264527 := bstep (se 1 (by rfl) ⟨6948395, by rfl⟩ : syracuseStep 9264527 = 13896791) B13896791
theorem B6176351 : Blo 2283435 6176351 := bstep (se 1 (by rfl) ⟨4632263, by rfl⟩ : syracuseStep 6176351 = 9264527) B9264527
theorem B4117567 : Blo 2283435 4117567 := bstep (se 1 (by rfl) ⟨3088175, by rfl⟩ : syracuseStep 4117567 = 6176351) B6176351
theorem B5490089 : Blo 2283435 5490089 := bstep (se 2 (by rfl) ⟨2058783, by rfl⟩ : syracuseStep 5490089 = 4117567) B4117567
theorem B3660059 : Blo 2283435 3660059 := bstep (se 1 (by rfl) ⟨2745044, by rfl⟩ : syracuseStep 3660059 = 5490089) B5490089
theorem B2440039 : Blo 2283435 2440039 := bstep (se 1 (by rfl) ⟨1830029, by rfl⟩ : syracuseStep 2440039 = 3660059) B3660059
theorem B3253385 : Blo 2283435 3253385 := bstep (se 2 (by rfl) ⟨1220019, by rfl⟩ : syracuseStep 3253385 = 2440039) B2440039
theorem B8675693 : Blo 2283435 8675693 := bstep (se 3 (by rfl) ⟨1626692, by rfl⟩ : syracuseStep 8675693 = 3253385) B3253385
theorem B5783795 : Blo 2283435 5783795 := bstep (se 1 (by rfl) ⟨4337846, by rfl⟩ : syracuseStep 5783795 = 8675693) B8675693
theorem B3855863 : Blo 2283435 3855863 := bstep (se 1 (by rfl) ⟨2891897, by rfl⟩ : syracuseStep 3855863 = 5783795) B5783795
theorem B2570575 : Blo 2283435 2570575 := bstep (se 1 (by rfl) ⟨1927931, by rfl⟩ : syracuseStep 2570575 = 3855863) B3855863
theorem B3427433 : Blo 2283435 3427433 := bstep (se 2 (by rfl) ⟨1285287, by rfl⟩ : syracuseStep 3427433 = 2570575) B2570575
theorem B2284955 : Blo 2283435 2284955 := bstep (se 1 (by rfl) ⟨1713716, by rfl⟩ : syracuseStep 2284955 = 3427433) B3427433
theorem B5282405 : Blo 2283435 5282405 := bbase (se 4 (by rfl) ⟨495225, by rfl⟩ : syracuseStep 5282405 = 990451) (by norm_num)
theorem B3521603 : Blo 2283435 3521603 := bstep (se 1 (by rfl) ⟨2641202, by rfl⟩ : syracuseStep 3521603 = 5282405) B5282405
theorem B9390941 : Blo 2283435 9390941 := bstep (se 3 (by rfl) ⟨1760801, by rfl⟩ : syracuseStep 9390941 = 3521603) B3521603
theorem B6260627 : Blo 2283435 6260627 := bstep (se 1 (by rfl) ⟨4695470, by rfl⟩ : syracuseStep 6260627 = 9390941) B9390941
theorem B4173751 : Blo 2283435 4173751 := bstep (se 1 (by rfl) ⟨3130313, by rfl⟩ : syracuseStep 4173751 = 6260627) B6260627
theorem B22260005 : Blo 2283435 22260005 := bstep (se 4 (by rfl) ⟨2086875, by rfl⟩ : syracuseStep 22260005 = 4173751) B4173751
theorem B14840003 : Blo 2283435 14840003 := bstep (se 1 (by rfl) ⟨11130002, by rfl⟩ : syracuseStep 14840003 = 22260005) B22260005
theorem B9893335 : Blo 2283435 9893335 := bstep (se 1 (by rfl) ⟨7420001, by rfl⟩ : syracuseStep 9893335 = 14840003) B14840003
theorem B13191113 : Blo 2283435 13191113 := bstep (se 2 (by rfl) ⟨4946667, by rfl⟩ : syracuseStep 13191113 = 9893335) B9893335
theorem B35176301 : Blo 2283435 35176301 := bstep (se 3 (by rfl) ⟨6595556, by rfl⟩ : syracuseStep 35176301 = 13191113) B13191113
theorem B23450867 : Blo 2283435 23450867 := bstep (se 1 (by rfl) ⟨17588150, by rfl⟩ : syracuseStep 23450867 = 35176301) B35176301
theorem B15633911 : Blo 2283435 15633911 := bstep (se 1 (by rfl) ⟨11725433, by rfl⟩ : syracuseStep 15633911 = 23450867) B23450867
theorem B10422607 : Blo 2283435 10422607 := bstep (se 1 (by rfl) ⟨7816955, by rfl⟩ : syracuseStep 10422607 = 15633911) B15633911
theorem B13896809 : Blo 2283435 13896809 := bstep (se 2 (by rfl) ⟨5211303, by rfl⟩ : syracuseStep 13896809 = 10422607) B10422607
theorem B9264539 : Blo 2283435 9264539 := bstep (se 1 (by rfl) ⟨6948404, by rfl⟩ : syracuseStep 9264539 = 13896809) B13896809
theorem B6176359 : Blo 2283435 6176359 := bstep (se 1 (by rfl) ⟨4632269, by rfl⟩ : syracuseStep 6176359 = 9264539) B9264539
theorem B8235145 : Blo 2283435 8235145 := bstep (se 2 (by rfl) ⟨3088179, by rfl⟩ : syracuseStep 8235145 = 6176359) B6176359
theorem B10980193 : Blo 2283435 10980193 := bstep (se 2 (by rfl) ⟨4117572, by rfl⟩ : syracuseStep 10980193 = 8235145) B8235145
theorem B14640257 : Blo 2283435 14640257 := bstep (se 2 (by rfl) ⟨5490096, by rfl⟩ : syracuseStep 14640257 = 10980193) B10980193
theorem B9760171 : Blo 2283435 9760171 := bstep (se 1 (by rfl) ⟨7320128, by rfl⟩ : syracuseStep 9760171 = 14640257) B14640257
theorem B13013561 : Blo 2283435 13013561 := bstep (se 2 (by rfl) ⟨4880085, by rfl⟩ : syracuseStep 13013561 = 9760171) B9760171
theorem B8675707 : Blo 2283435 8675707 := bstep (se 1 (by rfl) ⟨6506780, by rfl⟩ : syracuseStep 8675707 = 13013561) B13013561
theorem B11567609 : Blo 2283435 11567609 := bstep (se 2 (by rfl) ⟨4337853, by rfl⟩ : syracuseStep 11567609 = 8675707) B8675707
theorem B7711739 : Blo 2283435 7711739 := bstep (se 1 (by rfl) ⟨5783804, by rfl⟩ : syracuseStep 7711739 = 11567609) B11567609
theorem B5141159 : Blo 2283435 5141159 := bstep (se 1 (by rfl) ⟨3855869, by rfl⟩ : syracuseStep 5141159 = 7711739) B7711739
theorem B3427439 : Blo 2283435 3427439 := bstep (se 1 (by rfl) ⟨2570579, by rfl⟩ : syracuseStep 3427439 = 5141159) B5141159
theorem B2284959 : Blo 2283435 2284959 := bstep (se 1 (by rfl) ⟨1713719, by rfl⟩ : syracuseStep 2284959 = 3427439) B3427439
theorem B3427445 : Blo 2283435 3427445 := bbase (se 5 (by rfl) ⟨160661, by rfl⟩ : syracuseStep 3427445 = 321323) (by norm_num)
theorem B2284963 : Blo 2283435 2284963 := bstep (se 1 (by rfl) ⟨1713722, by rfl⟩ : syracuseStep 2284963 = 3427445) B3427445
theorem B4337869 : Blo 2283435 4337869 := bbase (se 3 (by rfl) ⟨813350, by rfl⟩ : syracuseStep 4337869 = 1626701) (by norm_num)
theorem B5783825 : Blo 2283435 5783825 := bstep (se 2 (by rfl) ⟨2168934, by rfl⟩ : syracuseStep 5783825 = 4337869) B4337869
theorem B3855883 : Blo 2283435 3855883 := bstep (se 1 (by rfl) ⟨2891912, by rfl⟩ : syracuseStep 3855883 = 5783825) B5783825
theorem B5141177 : Blo 2283435 5141177 := bstep (se 2 (by rfl) ⟨1927941, by rfl⟩ : syracuseStep 5141177 = 3855883) B3855883
theorem B3427451 : Blo 2283435 3427451 := bstep (se 1 (by rfl) ⟨2570588, by rfl⟩ : syracuseStep 3427451 = 5141177) B5141177
theorem B2284967 : Blo 2283435 2284967 := bstep (se 1 (by rfl) ⟨1713725, by rfl⟩ : syracuseStep 2284967 = 3427451) B3427451
theorem B2570593 : Blo 2283435 2570593 := bbase (se 2 (by rfl) ⟨963972, by rfl⟩ : syracuseStep 2570593 = 1927945) (by norm_num)
theorem B3427457 : Blo 2283435 3427457 := bstep (se 2 (by rfl) ⟨1285296, by rfl⟩ : syracuseStep 3427457 = 2570593) B2570593
theorem B2284971 : Blo 2283435 2284971 := bstep (se 1 (by rfl) ⟨1713728, by rfl⟩ : syracuseStep 2284971 = 3427457) B3427457
theorem B5783845 : Blo 2283435 5783845 := bbase (se 4 (by rfl) ⟨542235, by rfl⟩ : syracuseStep 5783845 = 1084471) (by norm_num)
theorem B7711793 : Blo 2283435 7711793 := bstep (se 2 (by rfl) ⟨2891922, by rfl⟩ : syracuseStep 7711793 = 5783845) B5783845
theorem B5141195 : Blo 2283435 5141195 := bstep (se 1 (by rfl) ⟨3855896, by rfl⟩ : syracuseStep 5141195 = 7711793) B7711793
theorem B3427463 : Blo 2283435 3427463 := bstep (se 1 (by rfl) ⟨2570597, by rfl⟩ : syracuseStep 3427463 = 5141195) B5141195
theorem B2284975 : Blo 2283435 2284975 := bstep (se 1 (by rfl) ⟨1713731, by rfl⟩ : syracuseStep 2284975 = 3427463) B3427463
theorem B3427469 : Blo 2283435 3427469 := bbase (se 3 (by rfl) ⟨642650, by rfl⟩ : syracuseStep 3427469 = 1285301) (by norm_num)
theorem B2284979 : Blo 2283435 2284979 := bstep (se 1 (by rfl) ⟨1713734, by rfl⟩ : syracuseStep 2284979 = 3427469) B3427469
theorem B5141213 : Blo 2283435 5141213 := bbase (se 3 (by rfl) ⟨963977, by rfl⟩ : syracuseStep 5141213 = 1927955) (by norm_num)
theorem B3427475 : Blo 2283435 3427475 := bstep (se 1 (by rfl) ⟨2570606, by rfl⟩ : syracuseStep 3427475 = 5141213) B5141213
theorem B2284983 : Blo 2283435 2284983 := bstep (se 1 (by rfl) ⟨1713737, by rfl⟩ : syracuseStep 2284983 = 3427475) B3427475
theorem B3855917 : Blo 2283435 3855917 := bbase (se 3 (by rfl) ⟨722984, by rfl⟩ : syracuseStep 3855917 = 1445969) (by norm_num)
theorem B2570611 : Blo 2283435 2570611 := bstep (se 1 (by rfl) ⟨1927958, by rfl⟩ : syracuseStep 2570611 = 3855917) B3855917
theorem B3427481 : Blo 2283435 3427481 := bstep (se 2 (by rfl) ⟨1285305, by rfl⟩ : syracuseStep 3427481 = 2570611) B2570611
theorem B2284987 : Blo 2283435 2284987 := bstep (se 1 (by rfl) ⟨1713740, by rfl⟩ : syracuseStep 2284987 = 3427481) B3427481
theorem B28173205 : Blo 2283435 28173205 := bbase (se 6 (by rfl) ⟨660309, by rfl⟩ : syracuseStep 28173205 = 1320619) (by norm_num)
theorem B37564273 : Blo 2283435 37564273 := bstep (se 2 (by rfl) ⟨14086602, by rfl⟩ : syracuseStep 37564273 = 28173205) B28173205
theorem B50085697 : Blo 2283435 50085697 := bstep (se 2 (by rfl) ⟨18782136, by rfl⟩ : syracuseStep 50085697 = 37564273) B37564273
theorem B66780929 : Blo 2283435 66780929 := bstep (se 2 (by rfl) ⟨25042848, by rfl⟩ : syracuseStep 66780929 = 50085697) B50085697
theorem B44520619 : Blo 2283435 44520619 := bstep (se 1 (by rfl) ⟨33390464, by rfl⟩ : syracuseStep 44520619 = 66780929) B66780929
theorem B59360825 : Blo 2283435 59360825 := bstep (se 2 (by rfl) ⟨22260309, by rfl⟩ : syracuseStep 59360825 = 44520619) B44520619
theorem B39573883 : Blo 2283435 39573883 := bstep (se 1 (by rfl) ⟨29680412, by rfl⟩ : syracuseStep 39573883 = 59360825) B59360825
theorem B52765177 : Blo 2283435 52765177 := bstep (se 2 (by rfl) ⟨19786941, by rfl⟩ : syracuseStep 52765177 = 39573883) B39573883
theorem B70353569 : Blo 2283435 70353569 := bstep (se 2 (by rfl) ⟨26382588, by rfl⟩ : syracuseStep 70353569 = 52765177) B52765177
theorem B187609517 : Blo 2283435 187609517 := bstep (se 3 (by rfl) ⟨35176784, by rfl⟩ : syracuseStep 187609517 = 70353569) B70353569
theorem B125073011 : Blo 2283435 125073011 := bstep (se 1 (by rfl) ⟨93804758, by rfl⟩ : syracuseStep 125073011 = 187609517) B187609517
theorem B83382007 : Blo 2283435 83382007 := bstep (se 1 (by rfl) ⟨62536505, by rfl⟩ : syracuseStep 83382007 = 125073011) B125073011
theorem B111176009 : Blo 2283435 111176009 := bstep (se 2 (by rfl) ⟨41691003, by rfl⟩ : syracuseStep 111176009 = 83382007) B83382007
theorem B74117339 : Blo 2283435 74117339 := bstep (se 1 (by rfl) ⟨55588004, by rfl⟩ : syracuseStep 74117339 = 111176009) B111176009
theorem B49411559 : Blo 2283435 49411559 := bstep (se 1 (by rfl) ⟨37058669, by rfl⟩ : syracuseStep 49411559 = 74117339) B74117339
theorem B32941039 : Blo 2283435 32941039 := bstep (se 1 (by rfl) ⟨24705779, by rfl⟩ : syracuseStep 32941039 = 49411559) B49411559
theorem B43921385 : Blo 2283435 43921385 := bstep (se 2 (by rfl) ⟨16470519, by rfl⟩ : syracuseStep 43921385 = 32941039) B32941039
theorem B29280923 : Blo 2283435 29280923 := bstep (se 1 (by rfl) ⟨21960692, by rfl⟩ : syracuseStep 29280923 = 43921385) B43921385
theorem B19520615 : Blo 2283435 19520615 := bstep (se 1 (by rfl) ⟨14640461, by rfl⟩ : syracuseStep 19520615 = 29280923) B29280923
theorem B13013743 : Blo 2283435 13013743 := bstep (se 1 (by rfl) ⟨9760307, by rfl⟩ : syracuseStep 13013743 = 19520615) B19520615
theorem B17351657 : Blo 2283435 17351657 := bstep (se 2 (by rfl) ⟨6506871, by rfl⟩ : syracuseStep 17351657 = 13013743) B13013743
theorem B11567771 : Blo 2283435 11567771 := bstep (se 1 (by rfl) ⟨8675828, by rfl⟩ : syracuseStep 11567771 = 17351657) B17351657
theorem B7711847 : Blo 2283435 7711847 := bstep (se 1 (by rfl) ⟨5783885, by rfl⟩ : syracuseStep 7711847 = 11567771) B11567771
theorem B5141231 : Blo 2283435 5141231 := bstep (se 1 (by rfl) ⟨3855923, by rfl⟩ : syracuseStep 5141231 = 7711847) B7711847
theorem B3427487 : Blo 2283435 3427487 := bstep (se 1 (by rfl) ⟨2570615, by rfl⟩ : syracuseStep 3427487 = 5141231) B5141231
theorem B2284991 : Blo 2283435 2284991 := bstep (se 1 (by rfl) ⟨1713743, by rfl⟩ : syracuseStep 2284991 = 3427487) B3427487
theorem B3427493 : Blo 2283435 3427493 := bbase (se 4 (by rfl) ⟨321327, by rfl⟩ : syracuseStep 3427493 = 642655) (by norm_num)
theorem B2284995 : Blo 2283435 2284995 := bstep (se 1 (by rfl) ⟨1713746, by rfl⟩ : syracuseStep 2284995 = 3427493) B3427493
theorem B2891953 : Blo 2283435 2891953 := bbase (se 2 (by rfl) ⟨1084482, by rfl⟩ : syracuseStep 2891953 = 2168965) (by norm_num)
theorem B3855937 : Blo 2283435 3855937 := bstep (se 2 (by rfl) ⟨1445976, by rfl⟩ : syracuseStep 3855937 = 2891953) B2891953
theorem B5141249 : Blo 2283435 5141249 := bstep (se 2 (by rfl) ⟨1927968, by rfl⟩ : syracuseStep 5141249 = 3855937) B3855937
theorem B3427499 : Blo 2283435 3427499 := bstep (se 1 (by rfl) ⟨2570624, by rfl⟩ : syracuseStep 3427499 = 5141249) B5141249
theorem B2284999 : Blo 2283435 2284999 := bstep (se 1 (by rfl) ⟨1713749, by rfl⟩ : syracuseStep 2284999 = 3427499) B3427499
theorem B2570629 : Blo 2283435 2570629 := bbase (se 4 (by rfl) ⟨240996, by rfl⟩ : syracuseStep 2570629 = 481993) (by norm_num)
theorem B3427505 : Blo 2283435 3427505 := bstep (se 2 (by rfl) ⟨1285314, by rfl⟩ : syracuseStep 3427505 = 2570629) B2570629
theorem B2285003 : Blo 2283435 2285003 := bstep (se 1 (by rfl) ⟨1713752, by rfl⟩ : syracuseStep 2285003 = 3427505) B3427505
theorem B4880189 : Blo 2283435 4880189 := bbase (se 3 (by rfl) ⟨915035, by rfl⟩ : syracuseStep 4880189 = 1830071) (by norm_num)
theorem B3253459 : Blo 2283435 3253459 := bstep (se 1 (by rfl) ⟨2440094, by rfl⟩ : syracuseStep 3253459 = 4880189) B4880189
theorem B4337945 : Blo 2283435 4337945 := bstep (se 2 (by rfl) ⟨1626729, by rfl⟩ : syracuseStep 4337945 = 3253459) B3253459
theorem B2891963 : Blo 2283435 2891963 := bstep (se 1 (by rfl) ⟨2168972, by rfl⟩ : syracuseStep 2891963 = 4337945) B4337945
theorem B7711901 : Blo 2283435 7711901 := bstep (se 3 (by rfl) ⟨1445981, by rfl⟩ : syracuseStep 7711901 = 2891963) B2891963
theorem B5141267 : Blo 2283435 5141267 := bstep (se 1 (by rfl) ⟨3855950, by rfl⟩ : syracuseStep 5141267 = 7711901) B7711901
theorem B3427511 : Blo 2283435 3427511 := bstep (se 1 (by rfl) ⟨2570633, by rfl⟩ : syracuseStep 3427511 = 5141267) B5141267
theorem B2285007 : Blo 2283435 2285007 := bstep (se 1 (by rfl) ⟨1713755, by rfl⟩ : syracuseStep 2285007 = 3427511) B3427511
theorem B3427517 : Blo 2283435 3427517 := bbase (se 3 (by rfl) ⟨642659, by rfl⟩ : syracuseStep 3427517 = 1285319) (by norm_num)
theorem B2285011 : Blo 2283435 2285011 := bstep (se 1 (by rfl) ⟨1713758, by rfl⟩ : syracuseStep 2285011 = 3427517) B3427517
theorem B5141285 : Blo 2283435 5141285 := bbase (se 4 (by rfl) ⟨481995, by rfl⟩ : syracuseStep 5141285 = 963991) (by norm_num)
theorem B3427523 : Blo 2283435 3427523 := bstep (se 1 (by rfl) ⟨2570642, by rfl⟩ : syracuseStep 3427523 = 5141285) B5141285
theorem B2285015 : Blo 2283435 2285015 := bstep (se 1 (by rfl) ⟨1713761, by rfl⟩ : syracuseStep 2285015 = 3427523) B3427523
theorem B5783957 : Blo 2283435 5783957 := bbase (se 6 (by rfl) ⟨135561, by rfl⟩ : syracuseStep 5783957 = 271123) (by norm_num)
theorem B3855971 : Blo 2283435 3855971 := bstep (se 1 (by rfl) ⟨2891978, by rfl⟩ : syracuseStep 3855971 = 5783957) B5783957
theorem B2570647 : Blo 2283435 2570647 := bstep (se 1 (by rfl) ⟨1927985, by rfl⟩ : syracuseStep 2570647 = 3855971) B3855971
theorem B3427529 : Blo 2283435 3427529 := bstep (se 2 (by rfl) ⟨1285323, by rfl⟩ : syracuseStep 3427529 = 2570647) B2570647
theorem B2285019 : Blo 2283435 2285019 := bstep (se 1 (by rfl) ⟨1713764, by rfl⟩ : syracuseStep 2285019 = 3427529) B3427529
theorem B6176533 : Blo 2283435 6176533 := bbase (se 6 (by rfl) ⟨144762, by rfl⟩ : syracuseStep 6176533 = 289525) (by norm_num)
theorem B8235377 : Blo 2283435 8235377 := bstep (se 2 (by rfl) ⟨3088266, by rfl⟩ : syracuseStep 8235377 = 6176533) B6176533
theorem B5490251 : Blo 2283435 5490251 := bstep (se 1 (by rfl) ⟨4117688, by rfl⟩ : syracuseStep 5490251 = 8235377) B8235377
theorem B3660167 : Blo 2283435 3660167 := bstep (se 1 (by rfl) ⟨2745125, by rfl⟩ : syracuseStep 3660167 = 5490251) B5490251
theorem B9760445 : Blo 2283435 9760445 := bstep (se 3 (by rfl) ⟨1830083, by rfl⟩ : syracuseStep 9760445 = 3660167) B3660167
theorem B6506963 : Blo 2283435 6506963 := bstep (se 1 (by rfl) ⟨4880222, by rfl⟩ : syracuseStep 6506963 = 9760445) B9760445
theorem B4337975 : Blo 2283435 4337975 := bstep (se 1 (by rfl) ⟨3253481, by rfl⟩ : syracuseStep 4337975 = 6506963) B6506963
theorem B11567933 : Blo 2283435 11567933 := bstep (se 3 (by rfl) ⟨2168987, by rfl⟩ : syracuseStep 11567933 = 4337975) B4337975
theorem B7711955 : Blo 2283435 7711955 := bstep (se 1 (by rfl) ⟨5783966, by rfl⟩ : syracuseStep 7711955 = 11567933) B11567933
theorem B5141303 : Blo 2283435 5141303 := bstep (se 1 (by rfl) ⟨3855977, by rfl⟩ : syracuseStep 5141303 = 7711955) B7711955
theorem B3427535 : Blo 2283435 3427535 := bstep (se 1 (by rfl) ⟨2570651, by rfl⟩ : syracuseStep 3427535 = 5141303) B5141303
theorem B2285023 : Blo 2283435 2285023 := bstep (se 1 (by rfl) ⟨1713767, by rfl⟩ : syracuseStep 2285023 = 3427535) B3427535
theorem B3427541 : Blo 2283435 3427541 := bbase (se 7 (by rfl) ⟨40166, by rfl⟩ : syracuseStep 3427541 = 80333) (by norm_num)
theorem B2285027 : Blo 2283435 2285027 := bstep (se 1 (by rfl) ⟨1713770, by rfl⟩ : syracuseStep 2285027 = 3427541) B3427541
theorem B3253493 : Blo 2283435 3253493 := bbase (se 5 (by rfl) ⟨152507, by rfl⟩ : syracuseStep 3253493 = 305015) (by norm_num)
theorem B8675981 : Blo 2283435 8675981 := bstep (se 3 (by rfl) ⟨1626746, by rfl⟩ : syracuseStep 8675981 = 3253493) B3253493
theorem B5783987 : Blo 2283435 5783987 := bstep (se 1 (by rfl) ⟨4337990, by rfl⟩ : syracuseStep 5783987 = 8675981) B8675981
theorem B3855991 : Blo 2283435 3855991 := bstep (se 1 (by rfl) ⟨2891993, by rfl⟩ : syracuseStep 3855991 = 5783987) B5783987
theorem B5141321 : Blo 2283435 5141321 := bstep (se 2 (by rfl) ⟨1927995, by rfl⟩ : syracuseStep 5141321 = 3855991) B3855991
theorem B3427547 : Blo 2283435 3427547 := bstep (se 1 (by rfl) ⟨2570660, by rfl⟩ : syracuseStep 3427547 = 5141321) B5141321
theorem B2285031 : Blo 2283435 2285031 := bstep (se 1 (by rfl) ⟨1713773, by rfl⟩ : syracuseStep 2285031 = 3427547) B3427547
theorem B2570665 : Blo 2283435 2570665 := bbase (se 2 (by rfl) ⟨963999, by rfl⟩ : syracuseStep 2570665 = 1927999) (by norm_num)
theorem B3427553 : Blo 2283435 3427553 := bstep (se 2 (by rfl) ⟨1285332, by rfl⟩ : syracuseStep 3427553 = 2570665) B2570665
theorem B2285035 : Blo 2283435 2285035 := bstep (se 1 (by rfl) ⟨1713776, by rfl⟩ : syracuseStep 2285035 = 3427553) B3427553
theorem B4117717 : Blo 2283435 4117717 := bbase (se 7 (by rfl) ⟨48254, by rfl⟩ : syracuseStep 4117717 = 96509) (by norm_num)
theorem B5490289 : Blo 2283435 5490289 := bstep (se 2 (by rfl) ⟨2058858, by rfl⟩ : syracuseStep 5490289 = 4117717) B4117717
theorem B7320385 : Blo 2283435 7320385 := bstep (se 2 (by rfl) ⟨2745144, by rfl⟩ : syracuseStep 7320385 = 5490289) B5490289
theorem B9760513 : Blo 2283435 9760513 := bstep (se 2 (by rfl) ⟨3660192, by rfl⟩ : syracuseStep 9760513 = 7320385) B7320385
theorem B13014017 : Blo 2283435 13014017 := bstep (se 2 (by rfl) ⟨4880256, by rfl⟩ : syracuseStep 13014017 = 9760513) B9760513
theorem B8676011 : Blo 2283435 8676011 := bstep (se 1 (by rfl) ⟨6507008, by rfl⟩ : syracuseStep 8676011 = 13014017) B13014017
theorem B5784007 : Blo 2283435 5784007 := bstep (se 1 (by rfl) ⟨4338005, by rfl⟩ : syracuseStep 5784007 = 8676011) B8676011
theorem B7712009 : Blo 2283435 7712009 := bstep (se 2 (by rfl) ⟨2892003, by rfl⟩ : syracuseStep 7712009 = 5784007) B5784007
theorem B5141339 : Blo 2283435 5141339 := bstep (se 1 (by rfl) ⟨3856004, by rfl⟩ : syracuseStep 5141339 = 7712009) B7712009
theorem B3427559 : Blo 2283435 3427559 := bstep (se 1 (by rfl) ⟨2570669, by rfl⟩ : syracuseStep 3427559 = 5141339) B5141339
theorem B2285039 : Blo 2283435 2285039 := bstep (se 1 (by rfl) ⟨1713779, by rfl⟩ : syracuseStep 2285039 = 3427559) B3427559
theorem B3427565 : Blo 2283435 3427565 := bbase (se 3 (by rfl) ⟨642668, by rfl⟩ : syracuseStep 3427565 = 1285337) (by norm_num)
theorem B2285043 : Blo 2283435 2285043 := bstep (se 1 (by rfl) ⟨1713782, by rfl⟩ : syracuseStep 2285043 = 3427565) B3427565
theorem B5141357 : Blo 2283435 5141357 := bbase (se 3 (by rfl) ⟨964004, by rfl⟩ : syracuseStep 5141357 = 1928009) (by norm_num)
theorem B3427571 : Blo 2283435 3427571 := bstep (se 1 (by rfl) ⟨2570678, by rfl⟩ : syracuseStep 3427571 = 5141357) B5141357
theorem B2285047 : Blo 2283435 2285047 := bstep (se 1 (by rfl) ⟨1713785, by rfl⟩ : syracuseStep 2285047 = 3427571) B3427571
theorem B4338029 : Blo 2283435 4338029 := bbase (se 3 (by rfl) ⟨813380, by rfl⟩ : syracuseStep 4338029 = 1626761) (by norm_num)
theorem B2892019 : Blo 2283435 2892019 := bstep (se 1 (by rfl) ⟨2169014, by rfl⟩ : syracuseStep 2892019 = 4338029) B4338029
theorem B3856025 : Blo 2283435 3856025 := bstep (se 2 (by rfl) ⟨1446009, by rfl⟩ : syracuseStep 3856025 = 2892019) B2892019
theorem B2570683 : Blo 2283435 2570683 := bstep (se 1 (by rfl) ⟨1928012, by rfl⟩ : syracuseStep 2570683 = 3856025) B3856025
theorem B3427577 : Blo 2283435 3427577 := bstep (se 2 (by rfl) ⟨1285341, by rfl⟩ : syracuseStep 3427577 = 2570683) B2570683
theorem B2285051 : Blo 2283435 2285051 := bstep (se 1 (by rfl) ⟨1713788, by rfl⟩ : syracuseStep 2285051 = 3427577) B3427577
theorem B17588885 : Blo 2283435 17588885 := bbase (se 6 (by rfl) ⟨412239, by rfl⟩ : syracuseStep 17588885 = 824479) (by norm_num)
theorem B46903693 : Blo 2283435 46903693 := bstep (se 3 (by rfl) ⟨8794442, by rfl⟩ : syracuseStep 46903693 = 17588885) B17588885
theorem B62538257 : Blo 2283435 62538257 := bstep (se 2 (by rfl) ⟨23451846, by rfl⟩ : syracuseStep 62538257 = 46903693) B46903693
theorem B41692171 : Blo 2283435 41692171 := bstep (se 1 (by rfl) ⟨31269128, by rfl⟩ : syracuseStep 41692171 = 62538257) B62538257
theorem B55589561 : Blo 2283435 55589561 := bstep (se 2 (by rfl) ⟨20846085, by rfl⟩ : syracuseStep 55589561 = 41692171) B41692171
theorem B37059707 : Blo 2283435 37059707 := bstep (se 1 (by rfl) ⟨27794780, by rfl⟩ : syracuseStep 37059707 = 55589561) B55589561
theorem B24706471 : Blo 2283435 24706471 := bstep (se 1 (by rfl) ⟨18529853, by rfl⟩ : syracuseStep 24706471 = 37059707) B37059707
theorem B32941961 : Blo 2283435 32941961 := bstep (se 2 (by rfl) ⟨12353235, by rfl⟩ : syracuseStep 32941961 = 24706471) B24706471
theorem B21961307 : Blo 2283435 21961307 := bstep (se 1 (by rfl) ⟨16470980, by rfl⟩ : syracuseStep 21961307 = 32941961) B32941961
theorem B58563485 : Blo 2283435 58563485 := bstep (se 3 (by rfl) ⟨10980653, by rfl⟩ : syracuseStep 58563485 = 21961307) B21961307
theorem B39042323 : Blo 2283435 39042323 := bstep (se 1 (by rfl) ⟨29281742, by rfl⟩ : syracuseStep 39042323 = 58563485) B58563485
theorem B26028215 : Blo 2283435 26028215 := bstep (se 1 (by rfl) ⟨19521161, by rfl⟩ : syracuseStep 26028215 = 39042323) B39042323
theorem B17352143 : Blo 2283435 17352143 := bstep (se 1 (by rfl) ⟨13014107, by rfl⟩ : syracuseStep 17352143 = 26028215) B26028215
theorem B11568095 : Blo 2283435 11568095 := bstep (se 1 (by rfl) ⟨8676071, by rfl⟩ : syracuseStep 11568095 = 17352143) B17352143
theorem B7712063 : Blo 2283435 7712063 := bstep (se 1 (by rfl) ⟨5784047, by rfl⟩ : syracuseStep 7712063 = 11568095) B11568095
theorem B5141375 : Blo 2283435 5141375 := bstep (se 1 (by rfl) ⟨3856031, by rfl⟩ : syracuseStep 5141375 = 7712063) B7712063
theorem B3427583 : Blo 2283435 3427583 := bstep (se 1 (by rfl) ⟨2570687, by rfl⟩ : syracuseStep 3427583 = 5141375) B5141375
theorem B2285055 : Blo 2283435 2285055 := bstep (se 1 (by rfl) ⟨1713791, by rfl⟩ : syracuseStep 2285055 = 3427583) B3427583
theorem B3427589 : Blo 2283435 3427589 := bbase (se 4 (by rfl) ⟨321336, by rfl⟩ : syracuseStep 3427589 = 642673) (by norm_num)
theorem B2285059 : Blo 2283435 2285059 := bstep (se 1 (by rfl) ⟨1713794, by rfl⟩ : syracuseStep 2285059 = 3427589) B3427589
theorem B3856045 : Blo 2283435 3856045 := bbase (se 3 (by rfl) ⟨723008, by rfl⟩ : syracuseStep 3856045 = 1446017) (by norm_num)
theorem B5141393 : Blo 2283435 5141393 := bstep (se 2 (by rfl) ⟨1928022, by rfl⟩ : syracuseStep 5141393 = 3856045) B3856045
theorem B3427595 : Blo 2283435 3427595 := bstep (se 1 (by rfl) ⟨2570696, by rfl⟩ : syracuseStep 3427595 = 5141393) B5141393
theorem B2285063 : Blo 2283435 2285063 := bstep (se 1 (by rfl) ⟨1713797, by rfl⟩ : syracuseStep 2285063 = 3427595) B3427595
theorem B2570701 : Blo 2283435 2570701 := bbase (se 3 (by rfl) ⟨482006, by rfl⟩ : syracuseStep 2570701 = 964013) (by norm_num)
theorem B3427601 : Blo 2283435 3427601 := bstep (se 2 (by rfl) ⟨1285350, by rfl⟩ : syracuseStep 3427601 = 2570701) B2570701
theorem B2285067 : Blo 2283435 2285067 := bstep (se 1 (by rfl) ⟨1713800, by rfl⟩ : syracuseStep 2285067 = 3427601) B3427601
theorem B7712117 : Blo 2283435 7712117 := bbase (se 5 (by rfl) ⟨361505, by rfl⟩ : syracuseStep 7712117 = 723011) (by norm_num)
theorem B5141411 : Blo 2283435 5141411 := bstep (se 1 (by rfl) ⟨3856058, by rfl⟩ : syracuseStep 5141411 = 7712117) B7712117
theorem B3427607 : Blo 2283435 3427607 := bstep (se 1 (by rfl) ⟨2570705, by rfl⟩ : syracuseStep 3427607 = 5141411) B5141411
theorem B2285071 : Blo 2283435 2285071 := bstep (se 1 (by rfl) ⟨1713803, by rfl⟩ : syracuseStep 2285071 = 3427607) B3427607
theorem B3427613 : Blo 2283435 3427613 := bbase (se 3 (by rfl) ⟨642677, by rfl⟩ : syracuseStep 3427613 = 1285355) (by norm_num)
theorem B2285075 : Blo 2283435 2285075 := bstep (se 1 (by rfl) ⟨1713806, by rfl⟩ : syracuseStep 2285075 = 3427613) B3427613
theorem B5141429 : Blo 2283435 5141429 := bbase (se 5 (by rfl) ⟨241004, by rfl⟩ : syracuseStep 5141429 = 482009) (by norm_num)
theorem B3427619 : Blo 2283435 3427619 := bstep (se 1 (by rfl) ⟨2570714, by rfl⟩ : syracuseStep 3427619 = 5141429) B5141429
theorem B2285079 : Blo 2283435 2285079 := bstep (se 1 (by rfl) ⟨1713809, by rfl⟩ : syracuseStep 2285079 = 3427619) B3427619
theorem B7817381 : Blo 2283435 7817381 := bbase (se 4 (by rfl) ⟨732879, by rfl⟩ : syracuseStep 7817381 = 1465759) (by norm_num)
theorem B5211587 : Blo 2283435 5211587 := bstep (se 1 (by rfl) ⟨3908690, by rfl⟩ : syracuseStep 5211587 = 7817381) B7817381
theorem B13897565 : Blo 2283435 13897565 := bstep (se 3 (by rfl) ⟨2605793, by rfl⟩ : syracuseStep 13897565 = 5211587) B5211587
theorem B9265043 : Blo 2283435 9265043 := bstep (se 1 (by rfl) ⟨6948782, by rfl⟩ : syracuseStep 9265043 = 13897565) B13897565
theorem B24706781 : Blo 2283435 24706781 := bstep (se 3 (by rfl) ⟨4632521, by rfl⟩ : syracuseStep 24706781 = 9265043) B9265043
theorem B16471187 : Blo 2283435 16471187 := bstep (se 1 (by rfl) ⟨12353390, by rfl⟩ : syracuseStep 16471187 = 24706781) B24706781
theorem B10980791 : Blo 2283435 10980791 := bstep (se 1 (by rfl) ⟨8235593, by rfl⟩ : syracuseStep 10980791 = 16471187) B16471187
theorem B7320527 : Blo 2283435 7320527 := bstep (se 1 (by rfl) ⟨5490395, by rfl⟩ : syracuseStep 7320527 = 10980791) B10980791
theorem B4880351 : Blo 2283435 4880351 := bstep (se 1 (by rfl) ⟨3660263, by rfl⟩ : syracuseStep 4880351 = 7320527) B7320527
theorem B13014269 : Blo 2283435 13014269 := bstep (se 3 (by rfl) ⟨2440175, by rfl⟩ : syracuseStep 13014269 = 4880351) B4880351
theorem B8676179 : Blo 2283435 8676179 := bstep (se 1 (by rfl) ⟨6507134, by rfl⟩ : syracuseStep 8676179 = 13014269) B13014269
theorem B5784119 : Blo 2283435 5784119 := bstep (se 1 (by rfl) ⟨4338089, by rfl⟩ : syracuseStep 5784119 = 8676179) B8676179
theorem B3856079 : Blo 2283435 3856079 := bstep (se 1 (by rfl) ⟨2892059, by rfl⟩ : syracuseStep 3856079 = 5784119) B5784119
theorem B2570719 : Blo 2283435 2570719 := bstep (se 1 (by rfl) ⟨1928039, by rfl⟩ : syracuseStep 2570719 = 3856079) B3856079
theorem B3427625 : Blo 2283435 3427625 := bstep (se 2 (by rfl) ⟨1285359, by rfl⟩ : syracuseStep 3427625 = 2570719) B2570719
theorem B2285083 : Blo 2283435 2285083 := bstep (se 1 (by rfl) ⟨1713812, by rfl⟩ : syracuseStep 2285083 = 3427625) B3427625
theorem B3474397 : Blo 2283435 3474397 := bbase (se 3 (by rfl) ⟨651449, by rfl⟩ : syracuseStep 3474397 = 1302899) (by norm_num)
theorem B18530117 : Blo 2283435 18530117 := bstep (se 4 (by rfl) ⟨1737198, by rfl⟩ : syracuseStep 18530117 = 3474397) B3474397
theorem B12353411 : Blo 2283435 12353411 := bstep (se 1 (by rfl) ⟨9265058, by rfl⟩ : syracuseStep 12353411 = 18530117) B18530117
theorem B8235607 : Blo 2283435 8235607 := bstep (se 1 (by rfl) ⟨6176705, by rfl⟩ : syracuseStep 8235607 = 12353411) B12353411
theorem B10980809 : Blo 2283435 10980809 := bstep (se 2 (by rfl) ⟨4117803, by rfl⟩ : syracuseStep 10980809 = 8235607) B8235607
theorem B7320539 : Blo 2283435 7320539 := bstep (se 1 (by rfl) ⟨5490404, by rfl⟩ : syracuseStep 7320539 = 10980809) B10980809
theorem B4880359 : Blo 2283435 4880359 := bstep (se 1 (by rfl) ⟨3660269, by rfl⟩ : syracuseStep 4880359 = 7320539) B7320539
theorem B6507145 : Blo 2283435 6507145 := bstep (se 2 (by rfl) ⟨2440179, by rfl⟩ : syracuseStep 6507145 = 4880359) B4880359
theorem B8676193 : Blo 2283435 8676193 := bstep (se 2 (by rfl) ⟨3253572, by rfl⟩ : syracuseStep 8676193 = 6507145) B6507145
theorem B11568257 : Blo 2283435 11568257 := bstep (se 2 (by rfl) ⟨4338096, by rfl⟩ : syracuseStep 11568257 = 8676193) B8676193
theorem B7712171 : Blo 2283435 7712171 := bstep (se 1 (by rfl) ⟨5784128, by rfl⟩ : syracuseStep 7712171 = 11568257) B11568257
theorem B5141447 : Blo 2283435 5141447 := bstep (se 1 (by rfl) ⟨3856085, by rfl⟩ : syracuseStep 5141447 = 7712171) B7712171
theorem B3427631 : Blo 2283435 3427631 := bstep (se 1 (by rfl) ⟨2570723, by rfl⟩ : syracuseStep 3427631 = 5141447) B5141447
theorem B2285087 : Blo 2283435 2285087 := bstep (se 1 (by rfl) ⟨1713815, by rfl⟩ : syracuseStep 2285087 = 3427631) B3427631
theorem B3427637 : Blo 2283435 3427637 := bbase (se 5 (by rfl) ⟨160670, by rfl⟩ : syracuseStep 3427637 = 321341) (by norm_num)
theorem B2285091 : Blo 2283435 2285091 := bstep (se 1 (by rfl) ⟨1713818, by rfl⟩ : syracuseStep 2285091 = 3427637) B3427637
theorem B5784149 : Blo 2283435 5784149 := bbase (se 8 (by rfl) ⟨33891, by rfl⟩ : syracuseStep 5784149 = 67783) (by norm_num)
theorem B3856099 : Blo 2283435 3856099 := bstep (se 1 (by rfl) ⟨2892074, by rfl⟩ : syracuseStep 3856099 = 5784149) B5784149
theorem B5141465 : Blo 2283435 5141465 := bstep (se 2 (by rfl) ⟨1928049, by rfl⟩ : syracuseStep 5141465 = 3856099) B3856099
theorem B3427643 : Blo 2283435 3427643 := bstep (se 1 (by rfl) ⟨2570732, by rfl⟩ : syracuseStep 3427643 = 5141465) B5141465
theorem B2285095 : Blo 2283435 2285095 := bstep (se 1 (by rfl) ⟨1713821, by rfl⟩ : syracuseStep 2285095 = 3427643) B3427643
theorem B2570737 : Blo 2283435 2570737 := bbase (se 2 (by rfl) ⟨964026, by rfl⟩ : syracuseStep 2570737 = 1928053) (by norm_num)
theorem B3427649 : Blo 2283435 3427649 := bstep (se 2 (by rfl) ⟨1285368, by rfl⟩ : syracuseStep 3427649 = 2570737) B2570737
theorem B2285099 : Blo 2283435 2285099 := bstep (se 1 (by rfl) ⟨1713824, by rfl⟩ : syracuseStep 2285099 = 3427649) B3427649
theorem B2316281 : Blo 2283435 2316281 := bbase (se 2 (by rfl) ⟨868605, by rfl⟩ : syracuseStep 2316281 = 1737211) (by norm_num)
theorem B6176749 : Blo 2283435 6176749 := bstep (se 3 (by rfl) ⟨1158140, by rfl⟩ : syracuseStep 6176749 = 2316281) B2316281
theorem B8235665 : Blo 2283435 8235665 := bstep (se 2 (by rfl) ⟨3088374, by rfl⟩ : syracuseStep 8235665 = 6176749) B6176749
theorem B5490443 : Blo 2283435 5490443 := bstep (se 1 (by rfl) ⟨4117832, by rfl⟩ : syracuseStep 5490443 = 8235665) B8235665
theorem B14641181 : Blo 2283435 14641181 := bstep (se 3 (by rfl) ⟨2745221, by rfl⟩ : syracuseStep 14641181 = 5490443) B5490443
theorem B9760787 : Blo 2283435 9760787 := bstep (se 1 (by rfl) ⟨7320590, by rfl⟩ : syracuseStep 9760787 = 14641181) B14641181
theorem B6507191 : Blo 2283435 6507191 := bstep (se 1 (by rfl) ⟨4880393, by rfl⟩ : syracuseStep 6507191 = 9760787) B9760787
theorem B4338127 : Blo 2283435 4338127 := bstep (se 1 (by rfl) ⟨3253595, by rfl⟩ : syracuseStep 4338127 = 6507191) B6507191
theorem B5784169 : Blo 2283435 5784169 := bstep (se 2 (by rfl) ⟨2169063, by rfl⟩ : syracuseStep 5784169 = 4338127) B4338127
theorem B7712225 : Blo 2283435 7712225 := bstep (se 2 (by rfl) ⟨2892084, by rfl⟩ : syracuseStep 7712225 = 5784169) B5784169
theorem B5141483 : Blo 2283435 5141483 := bstep (se 1 (by rfl) ⟨3856112, by rfl⟩ : syracuseStep 5141483 = 7712225) B7712225
theorem B3427655 : Blo 2283435 3427655 := bstep (se 1 (by rfl) ⟨2570741, by rfl⟩ : syracuseStep 3427655 = 5141483) B5141483
theorem B2285103 : Blo 2283435 2285103 := bstep (se 1 (by rfl) ⟨1713827, by rfl⟩ : syracuseStep 2285103 = 3427655) B3427655
theorem B3427661 : Blo 2283435 3427661 := bbase (se 3 (by rfl) ⟨642686, by rfl⟩ : syracuseStep 3427661 = 1285373) (by norm_num)
theorem B2285107 : Blo 2283435 2285107 := bstep (se 1 (by rfl) ⟨1713830, by rfl⟩ : syracuseStep 2285107 = 3427661) B3427661
theorem B5141501 : Blo 2283435 5141501 := bbase (se 3 (by rfl) ⟨964031, by rfl⟩ : syracuseStep 5141501 = 1928063) (by norm_num)
theorem B3427667 : Blo 2283435 3427667 := bstep (se 1 (by rfl) ⟨2570750, by rfl⟩ : syracuseStep 3427667 = 5141501) B5141501
theorem B2285111 : Blo 2283435 2285111 := bstep (se 1 (by rfl) ⟨1713833, by rfl⟩ : syracuseStep 2285111 = 3427667) B3427667
theorem B3856133 : Blo 2283435 3856133 := bbase (se 4 (by rfl) ⟨361512, by rfl⟩ : syracuseStep 3856133 = 723025) (by norm_num)
theorem B2570755 : Blo 2283435 2570755 := bstep (se 1 (by rfl) ⟨1928066, by rfl⟩ : syracuseStep 2570755 = 3856133) B3856133
theorem B3427673 : Blo 2283435 3427673 := bstep (se 2 (by rfl) ⟨1285377, by rfl⟩ : syracuseStep 3427673 = 2570755) B2570755
theorem B2285115 : Blo 2283435 2285115 := bstep (se 1 (by rfl) ⟨1713836, by rfl⟩ : syracuseStep 2285115 = 3427673) B3427673
theorem B17352629 : Blo 2283435 17352629 := bbase (se 5 (by rfl) ⟨813404, by rfl⟩ : syracuseStep 17352629 = 1626809) (by norm_num)
theorem B11568419 : Blo 2283435 11568419 := bstep (se 1 (by rfl) ⟨8676314, by rfl⟩ : syracuseStep 11568419 = 17352629) B17352629
theorem B7712279 : Blo 2283435 7712279 := bstep (se 1 (by rfl) ⟨5784209, by rfl⟩ : syracuseStep 7712279 = 11568419) B11568419
theorem B5141519 : Blo 2283435 5141519 := bstep (se 1 (by rfl) ⟨3856139, by rfl⟩ : syracuseStep 5141519 = 7712279) B7712279
theorem B3427679 : Blo 2283435 3427679 := bstep (se 1 (by rfl) ⟨2570759, by rfl⟩ : syracuseStep 3427679 = 5141519) B5141519
theorem B2285119 : Blo 2283435 2285119 := bstep (se 1 (by rfl) ⟨1713839, by rfl⟩ : syracuseStep 2285119 = 3427679) B3427679
theorem B3427685 : Blo 2283435 3427685 := bbase (se 4 (by rfl) ⟨321345, by rfl⟩ : syracuseStep 3427685 = 642691) (by norm_num)
theorem B2285123 : Blo 2283435 2285123 := bstep (se 1 (by rfl) ⟨1713842, by rfl⟩ : syracuseStep 2285123 = 3427685) B3427685
theorem B4338173 : Blo 2283435 4338173 := bbase (se 3 (by rfl) ⟨813407, by rfl⟩ : syracuseStep 4338173 = 1626815) (by norm_num)
theorem B2892115 : Blo 2283435 2892115 := bstep (se 1 (by rfl) ⟨2169086, by rfl⟩ : syracuseStep 2892115 = 4338173) B4338173
theorem B3856153 : Blo 2283435 3856153 := bstep (se 2 (by rfl) ⟨1446057, by rfl⟩ : syracuseStep 3856153 = 2892115) B2892115
theorem B5141537 : Blo 2283435 5141537 := bstep (se 2 (by rfl) ⟨1928076, by rfl⟩ : syracuseStep 5141537 = 3856153) B3856153
theorem B3427691 : Blo 2283435 3427691 := bstep (se 1 (by rfl) ⟨2570768, by rfl⟩ : syracuseStep 3427691 = 5141537) B5141537
theorem B2285127 : Blo 2283435 2285127 := bstep (se 1 (by rfl) ⟨1713845, by rfl⟩ : syracuseStep 2285127 = 3427691) B3427691
theorem B2570773 : Blo 2283435 2570773 := bbase (se 6 (by rfl) ⟨60252, by rfl⟩ : syracuseStep 2570773 = 120505) (by norm_num)
theorem B3427697 : Blo 2283435 3427697 := bstep (se 2 (by rfl) ⟨1285386, by rfl⟩ : syracuseStep 3427697 = 2570773) B2570773
theorem B2285131 : Blo 2283435 2285131 := bstep (se 1 (by rfl) ⟨1713848, by rfl⟩ : syracuseStep 2285131 = 3427697) B3427697
theorem B2892125 : Blo 2283435 2892125 := bbase (se 3 (by rfl) ⟨542273, by rfl⟩ : syracuseStep 2892125 = 1084547) (by norm_num)
theorem B7712333 : Blo 2283435 7712333 := bstep (se 3 (by rfl) ⟨1446062, by rfl⟩ : syracuseStep 7712333 = 2892125) B2892125
theorem B5141555 : Blo 2283435 5141555 := bstep (se 1 (by rfl) ⟨3856166, by rfl⟩ : syracuseStep 5141555 = 7712333) B7712333
theorem B3427703 : Blo 2283435 3427703 := bstep (se 1 (by rfl) ⟨2570777, by rfl⟩ : syracuseStep 3427703 = 5141555) B5141555
theorem B2285135 : Blo 2283435 2285135 := bstep (se 1 (by rfl) ⟨1713851, by rfl⟩ : syracuseStep 2285135 = 3427703) B3427703
theorem B3427709 : Blo 2283435 3427709 := bbase (se 3 (by rfl) ⟨642695, by rfl⟩ : syracuseStep 3427709 = 1285391) (by norm_num)
theorem B2285139 : Blo 2283435 2285139 := bstep (se 1 (by rfl) ⟨1713854, by rfl⟩ : syracuseStep 2285139 = 3427709) B3427709
theorem B5141573 : Blo 2283435 5141573 := bbase (se 4 (by rfl) ⟨482022, by rfl⟩ : syracuseStep 5141573 = 964045) (by norm_num)
theorem B3427715 : Blo 2283435 3427715 := bstep (se 1 (by rfl) ⟨2570786, by rfl⟩ : syracuseStep 3427715 = 5141573) B5141573
theorem B2285143 : Blo 2283435 2285143 := bstep (se 1 (by rfl) ⟨1713857, by rfl⟩ : syracuseStep 2285143 = 3427715) B3427715
theorem B6507317 : Blo 2283435 6507317 := bbase (se 5 (by rfl) ⟨305030, by rfl⟩ : syracuseStep 6507317 = 610061) (by norm_num)
theorem B4338211 : Blo 2283435 4338211 := bstep (se 1 (by rfl) ⟨3253658, by rfl⟩ : syracuseStep 4338211 = 6507317) B6507317
theorem B5784281 : Blo 2283435 5784281 := bstep (se 2 (by rfl) ⟨2169105, by rfl⟩ : syracuseStep 5784281 = 4338211) B4338211
theorem B3856187 : Blo 2283435 3856187 := bstep (se 1 (by rfl) ⟨2892140, by rfl⟩ : syracuseStep 3856187 = 5784281) B5784281
theorem B2570791 : Blo 2283435 2570791 := bstep (se 1 (by rfl) ⟨1928093, by rfl⟩ : syracuseStep 2570791 = 3856187) B3856187
theorem B3427721 : Blo 2283435 3427721 := bstep (se 2 (by rfl) ⟨1285395, by rfl⟩ : syracuseStep 3427721 = 2570791) B2570791
theorem B2285147 : Blo 2283435 2285147 := bstep (se 1 (by rfl) ⟨1713860, by rfl⟩ : syracuseStep 2285147 = 3427721) B3427721
theorem B11568581 : Blo 2283435 11568581 := bbase (se 4 (by rfl) ⟨1084554, by rfl⟩ : syracuseStep 11568581 = 2169109) (by norm_num)
theorem B7712387 : Blo 2283435 7712387 := bstep (se 1 (by rfl) ⟨5784290, by rfl⟩ : syracuseStep 7712387 = 11568581) B11568581
theorem B5141591 : Blo 2283435 5141591 := bstep (se 1 (by rfl) ⟨3856193, by rfl⟩ : syracuseStep 5141591 = 7712387) B7712387
theorem B3427727 : Blo 2283435 3427727 := bstep (se 1 (by rfl) ⟨2570795, by rfl⟩ : syracuseStep 3427727 = 5141591) B5141591
theorem B2285151 : Blo 2283435 2285151 := bstep (se 1 (by rfl) ⟨1713863, by rfl⟩ : syracuseStep 2285151 = 3427727) B3427727
theorem B3427733 : Blo 2283435 3427733 := bbase (se 6 (by rfl) ⟨80337, by rfl⟩ : syracuseStep 3427733 = 160675) (by norm_num)
theorem B2285155 : Blo 2283435 2285155 := bstep (se 1 (by rfl) ⟨1713866, by rfl⟩ : syracuseStep 2285155 = 3427733) B3427733
theorem B2745289 : Blo 2283435 2745289 := bbase (se 2 (by rfl) ⟨1029483, by rfl⟩ : syracuseStep 2745289 = 2058967) (by norm_num)
theorem B3660385 : Blo 2283435 3660385 := bstep (se 2 (by rfl) ⟨1372644, by rfl⟩ : syracuseStep 3660385 = 2745289) B2745289
theorem B4880513 : Blo 2283435 4880513 := bstep (se 2 (by rfl) ⟨1830192, by rfl⟩ : syracuseStep 4880513 = 3660385) B3660385
theorem B13014701 : Blo 2283435 13014701 := bstep (se 3 (by rfl) ⟨2440256, by rfl⟩ : syracuseStep 13014701 = 4880513) B4880513
theorem B8676467 : Blo 2283435 8676467 := bstep (se 1 (by rfl) ⟨6507350, by rfl⟩ : syracuseStep 8676467 = 13014701) B13014701
theorem B5784311 : Blo 2283435 5784311 := bstep (se 1 (by rfl) ⟨4338233, by rfl⟩ : syracuseStep 5784311 = 8676467) B8676467
theorem B3856207 : Blo 2283435 3856207 := bstep (se 1 (by rfl) ⟨2892155, by rfl⟩ : syracuseStep 3856207 = 5784311) B5784311
theorem B5141609 : Blo 2283435 5141609 := bstep (se 2 (by rfl) ⟨1928103, by rfl⟩ : syracuseStep 5141609 = 3856207) B3856207
theorem B3427739 : Blo 2283435 3427739 := bstep (se 1 (by rfl) ⟨2570804, by rfl⟩ : syracuseStep 3427739 = 5141609) B5141609
theorem B2285159 : Blo 2283435 2285159 := bstep (se 1 (by rfl) ⟨1713869, by rfl⟩ : syracuseStep 2285159 = 3427739) B3427739
theorem B2570809 : Blo 2283435 2570809 := bbase (se 2 (by rfl) ⟨964053, by rfl⟩ : syracuseStep 2570809 = 1928107) (by norm_num)
theorem B3427745 : Blo 2283435 3427745 := bstep (se 2 (by rfl) ⟨1285404, by rfl⟩ : syracuseStep 3427745 = 2570809) B2570809
theorem B2285163 : Blo 2283435 2285163 := bstep (se 1 (by rfl) ⟨1713872, by rfl⟩ : syracuseStep 2285163 = 3427745) B3427745
theorem B2440265 : Blo 2283435 2440265 := bbase (se 2 (by rfl) ⟨915099, by rfl⟩ : syracuseStep 2440265 = 1830199) (by norm_num)
theorem B6507373 : Blo 2283435 6507373 := bstep (se 3 (by rfl) ⟨1220132, by rfl⟩ : syracuseStep 6507373 = 2440265) B2440265
theorem B8676497 : Blo 2283435 8676497 := bstep (se 2 (by rfl) ⟨3253686, by rfl⟩ : syracuseStep 8676497 = 6507373) B6507373
theorem B5784331 : Blo 2283435 5784331 := bstep (se 1 (by rfl) ⟨4338248, by rfl⟩ : syracuseStep 5784331 = 8676497) B8676497
theorem B7712441 : Blo 2283435 7712441 := bstep (se 2 (by rfl) ⟨2892165, by rfl⟩ : syracuseStep 7712441 = 5784331) B5784331
theorem B5141627 : Blo 2283435 5141627 := bstep (se 1 (by rfl) ⟨3856220, by rfl⟩ : syracuseStep 5141627 = 7712441) B7712441
theorem B3427751 : Blo 2283435 3427751 := bstep (se 1 (by rfl) ⟨2570813, by rfl⟩ : syracuseStep 3427751 = 5141627) B5141627
theorem B2285167 : Blo 2283435 2285167 := bstep (se 1 (by rfl) ⟨1713875, by rfl⟩ : syracuseStep 2285167 = 3427751) B3427751
theorem B3427757 : Blo 2283435 3427757 := bbase (se 3 (by rfl) ⟨642704, by rfl⟩ : syracuseStep 3427757 = 1285409) (by norm_num)
theorem B2285171 : Blo 2283435 2285171 := bstep (se 1 (by rfl) ⟨1713878, by rfl⟩ : syracuseStep 2285171 = 3427757) B3427757
theorem B5141645 : Blo 2283435 5141645 := bbase (se 3 (by rfl) ⟨964058, by rfl⟩ : syracuseStep 5141645 = 1928117) (by norm_num)
theorem B3427763 : Blo 2283435 3427763 := bstep (se 1 (by rfl) ⟨2570822, by rfl⟩ : syracuseStep 3427763 = 5141645) B5141645
theorem B2285175 : Blo 2283435 2285175 := bstep (se 1 (by rfl) ⟨1713881, by rfl⟩ : syracuseStep 2285175 = 3427763) B3427763
theorem B2892181 : Blo 2283435 2892181 := bbase (se 6 (by rfl) ⟨67785, by rfl⟩ : syracuseStep 2892181 = 135571) (by norm_num)
theorem B3856241 : Blo 2283435 3856241 := bstep (se 2 (by rfl) ⟨1446090, by rfl⟩ : syracuseStep 3856241 = 2892181) B2892181
theorem B2570827 : Blo 2283435 2570827 := bstep (se 1 (by rfl) ⟨1928120, by rfl⟩ : syracuseStep 2570827 = 3856241) B3856241
theorem B3427769 : Blo 2283435 3427769 := bstep (se 2 (by rfl) ⟨1285413, by rfl⟩ : syracuseStep 3427769 = 2570827) B2570827
theorem B2285179 : Blo 2283435 2285179 := bstep (se 1 (by rfl) ⟨1713884, by rfl⟩ : syracuseStep 2285179 = 3427769) B3427769
theorem B83389013 : Blo 2283435 83389013 := bbase (se 8 (by rfl) ⟨488607, by rfl⟩ : syracuseStep 83389013 = 977215) (by norm_num)
theorem B55592675 : Blo 2283435 55592675 := bstep (se 1 (by rfl) ⟨41694506, by rfl⟩ : syracuseStep 55592675 = 83389013) B83389013
theorem B37061783 : Blo 2283435 37061783 := bstep (se 1 (by rfl) ⟨27796337, by rfl⟩ : syracuseStep 37061783 = 55592675) B55592675
theorem B24707855 : Blo 2283435 24707855 := bstep (se 1 (by rfl) ⟨18530891, by rfl⟩ : syracuseStep 24707855 = 37061783) B37061783
theorem B65887613 : Blo 2283435 65887613 := bstep (se 3 (by rfl) ⟨12353927, by rfl⟩ : syracuseStep 65887613 = 24707855) B24707855
theorem B43925075 : Blo 2283435 43925075 := bstep (se 1 (by rfl) ⟨32943806, by rfl⟩ : syracuseStep 43925075 = 65887613) B65887613
theorem B29283383 : Blo 2283435 29283383 := bstep (se 1 (by rfl) ⟨21962537, by rfl⟩ : syracuseStep 29283383 = 43925075) B43925075
theorem B19522255 : Blo 2283435 19522255 := bstep (se 1 (by rfl) ⟨14641691, by rfl⟩ : syracuseStep 19522255 = 29283383) B29283383
theorem B26029673 : Blo 2283435 26029673 := bstep (se 2 (by rfl) ⟨9761127, by rfl⟩ : syracuseStep 26029673 = 19522255) B19522255
theorem B17353115 : Blo 2283435 17353115 := bstep (se 1 (by rfl) ⟨13014836, by rfl⟩ : syracuseStep 17353115 = 26029673) B26029673
theorem B11568743 : Blo 2283435 11568743 := bstep (se 1 (by rfl) ⟨8676557, by rfl⟩ : syracuseStep 11568743 = 17353115) B17353115
theorem B7712495 : Blo 2283435 7712495 := bstep (se 1 (by rfl) ⟨5784371, by rfl⟩ : syracuseStep 7712495 = 11568743) B11568743
theorem B5141663 : Blo 2283435 5141663 := bstep (se 1 (by rfl) ⟨3856247, by rfl⟩ : syracuseStep 5141663 = 7712495) B7712495
theorem B3427775 : Blo 2283435 3427775 := bstep (se 1 (by rfl) ⟨2570831, by rfl⟩ : syracuseStep 3427775 = 5141663) B5141663
theorem B2285183 : Blo 2283435 2285183 := bstep (se 1 (by rfl) ⟨1713887, by rfl⟩ : syracuseStep 2285183 = 3427775) B3427775
theorem B3427781 : Blo 2283435 3427781 := bbase (se 4 (by rfl) ⟨321354, by rfl⟩ : syracuseStep 3427781 = 642709) (by norm_num)
theorem B2285187 : Blo 2283435 2285187 := bstep (se 1 (by rfl) ⟨1713890, by rfl⟩ : syracuseStep 2285187 = 3427781) B3427781
theorem B3856261 : Blo 2283435 3856261 := bbase (se 4 (by rfl) ⟨361524, by rfl⟩ : syracuseStep 3856261 = 723049) (by norm_num)
theorem B5141681 : Blo 2283435 5141681 := bstep (se 2 (by rfl) ⟨1928130, by rfl⟩ : syracuseStep 5141681 = 3856261) B3856261
theorem B3427787 : Blo 2283435 3427787 := bstep (se 1 (by rfl) ⟨2570840, by rfl⟩ : syracuseStep 3427787 = 5141681) B5141681
theorem B2285191 : Blo 2283435 2285191 := bstep (se 1 (by rfl) ⟨1713893, by rfl⟩ : syracuseStep 2285191 = 3427787) B3427787
theorem B2570845 : Blo 2283435 2570845 := bbase (se 3 (by rfl) ⟨482033, by rfl⟩ : syracuseStep 2570845 = 964067) (by norm_num)
theorem B3427793 : Blo 2283435 3427793 := bstep (se 2 (by rfl) ⟨1285422, by rfl⟩ : syracuseStep 3427793 = 2570845) B2570845
theorem B2285195 : Blo 2283435 2285195 := bstep (se 1 (by rfl) ⟨1713896, by rfl⟩ : syracuseStep 2285195 = 3427793) B3427793
theorem B7712549 : Blo 2283435 7712549 := bbase (se 4 (by rfl) ⟨723051, by rfl⟩ : syracuseStep 7712549 = 1446103) (by norm_num)
theorem B5141699 : Blo 2283435 5141699 := bstep (se 1 (by rfl) ⟨3856274, by rfl⟩ : syracuseStep 5141699 = 7712549) B7712549
theorem B3427799 : Blo 2283435 3427799 := bstep (se 1 (by rfl) ⟨2570849, by rfl⟩ : syracuseStep 3427799 = 5141699) B5141699
theorem B2285199 : Blo 2283435 2285199 := bstep (se 1 (by rfl) ⟨1713899, by rfl⟩ : syracuseStep 2285199 = 3427799) B3427799
theorem B3427805 : Blo 2283435 3427805 := bbase (se 3 (by rfl) ⟨642713, by rfl⟩ : syracuseStep 3427805 = 1285427) (by norm_num)
theorem B2285203 : Blo 2283435 2285203 := bstep (se 1 (by rfl) ⟨1713902, by rfl⟩ : syracuseStep 2285203 = 3427805) B3427805
theorem B5141717 : Blo 2283435 5141717 := bbase (se 7 (by rfl) ⟨60254, by rfl⟩ : syracuseStep 5141717 = 120509) (by norm_num)
theorem B3427811 : Blo 2283435 3427811 := bstep (se 1 (by rfl) ⟨2570858, by rfl⟩ : syracuseStep 3427811 = 5141717) B5141717
theorem B2285207 : Blo 2283435 2285207 := bstep (se 1 (by rfl) ⟨1713905, by rfl⟩ : syracuseStep 2285207 = 3427811) B3427811
theorem B18531125 : Blo 2283435 18531125 := bbase (se 5 (by rfl) ⟨868646, by rfl⟩ : syracuseStep 18531125 = 1737293) (by norm_num)
theorem B12354083 : Blo 2283435 12354083 := bstep (se 1 (by rfl) ⟨9265562, by rfl⟩ : syracuseStep 12354083 = 18531125) B18531125
theorem B8236055 : Blo 2283435 8236055 := bstep (se 1 (by rfl) ⟨6177041, by rfl⟩ : syracuseStep 8236055 = 12354083) B12354083
theorem B5490703 : Blo 2283435 5490703 := bstep (se 1 (by rfl) ⟨4118027, by rfl⟩ : syracuseStep 5490703 = 8236055) B8236055
theorem B7320937 : Blo 2283435 7320937 := bstep (se 2 (by rfl) ⟨2745351, by rfl⟩ : syracuseStep 7320937 = 5490703) B5490703
theorem B9761249 : Blo 2283435 9761249 := bstep (se 2 (by rfl) ⟨3660468, by rfl⟩ : syracuseStep 9761249 = 7320937) B7320937
theorem B6507499 : Blo 2283435 6507499 := bstep (se 1 (by rfl) ⟨4880624, by rfl⟩ : syracuseStep 6507499 = 9761249) B9761249
theorem B8676665 : Blo 2283435 8676665 := bstep (se 2 (by rfl) ⟨3253749, by rfl⟩ : syracuseStep 8676665 = 6507499) B6507499
theorem B5784443 : Blo 2283435 5784443 := bstep (se 1 (by rfl) ⟨4338332, by rfl⟩ : syracuseStep 5784443 = 8676665) B8676665
theorem B3856295 : Blo 2283435 3856295 := bstep (se 1 (by rfl) ⟨2892221, by rfl⟩ : syracuseStep 3856295 = 5784443) B5784443
theorem B2570863 : Blo 2283435 2570863 := bstep (se 1 (by rfl) ⟨1928147, by rfl⟩ : syracuseStep 2570863 = 3856295) B3856295
theorem B3427817 : Blo 2283435 3427817 := bstep (se 2 (by rfl) ⟨1285431, by rfl⟩ : syracuseStep 3427817 = 2570863) B2570863
theorem B2285211 : Blo 2283435 2285211 := bstep (se 1 (by rfl) ⟨1713908, by rfl⟩ : syracuseStep 2285211 = 3427817) B3427817
theorem B4947221 : Blo 2283435 4947221 := bbase (se 6 (by rfl) ⟨115950, by rfl⟩ : syracuseStep 4947221 = 231901) (by norm_num)
theorem B13192589 : Blo 2283435 13192589 := bstep (se 3 (by rfl) ⟨2473610, by rfl⟩ : syracuseStep 13192589 = 4947221) B4947221
theorem B35180237 : Blo 2283435 35180237 := bstep (se 3 (by rfl) ⟨6596294, by rfl⟩ : syracuseStep 35180237 = 13192589) B13192589
theorem B23453491 : Blo 2283435 23453491 := bstep (se 1 (by rfl) ⟨17590118, by rfl⟩ : syracuseStep 23453491 = 35180237) B35180237
theorem B31271321 : Blo 2283435 31271321 := bstep (se 2 (by rfl) ⟨11726745, by rfl⟩ : syracuseStep 31271321 = 23453491) B23453491
theorem B20847547 : Blo 2283435 20847547 := bstep (se 1 (by rfl) ⟨15635660, by rfl⟩ : syracuseStep 20847547 = 31271321) B31271321
theorem B27796729 : Blo 2283435 27796729 := bstep (se 2 (by rfl) ⟨10423773, by rfl⟩ : syracuseStep 27796729 = 20847547) B20847547
theorem B37062305 : Blo 2283435 37062305 := bstep (se 2 (by rfl) ⟨13898364, by rfl⟩ : syracuseStep 37062305 = 27796729) B27796729
theorem B24708203 : Blo 2283435 24708203 := bstep (se 1 (by rfl) ⟨18531152, by rfl⟩ : syracuseStep 24708203 = 37062305) B37062305
theorem B16472135 : Blo 2283435 16472135 := bstep (se 1 (by rfl) ⟨12354101, by rfl⟩ : syracuseStep 16472135 = 24708203) B24708203
theorem B10981423 : Blo 2283435 10981423 := bstep (se 1 (by rfl) ⟨8236067, by rfl⟩ : syracuseStep 10981423 = 16472135) B16472135
theorem B14641897 : Blo 2283435 14641897 := bstep (se 2 (by rfl) ⟨5490711, by rfl⟩ : syracuseStep 14641897 = 10981423) B10981423
theorem B19522529 : Blo 2283435 19522529 := bstep (se 2 (by rfl) ⟨7320948, by rfl⟩ : syracuseStep 19522529 = 14641897) B14641897
theorem B13015019 : Blo 2283435 13015019 := bstep (se 1 (by rfl) ⟨9761264, by rfl⟩ : syracuseStep 13015019 = 19522529) B19522529
theorem B8676679 : Blo 2283435 8676679 := bstep (se 1 (by rfl) ⟨6507509, by rfl⟩ : syracuseStep 8676679 = 13015019) B13015019
theorem B11568905 : Blo 2283435 11568905 := bstep (se 2 (by rfl) ⟨4338339, by rfl⟩ : syracuseStep 11568905 = 8676679) B8676679
theorem B7712603 : Blo 2283435 7712603 := bstep (se 1 (by rfl) ⟨5784452, by rfl⟩ : syracuseStep 7712603 = 11568905) B11568905
theorem B5141735 : Blo 2283435 5141735 := bstep (se 1 (by rfl) ⟨3856301, by rfl⟩ : syracuseStep 5141735 = 7712603) B7712603
theorem B3427823 : Blo 2283435 3427823 := bstep (se 1 (by rfl) ⟨2570867, by rfl⟩ : syracuseStep 3427823 = 5141735) B5141735
theorem B2285215 : Blo 2283435 2285215 := bstep (se 1 (by rfl) ⟨1713911, by rfl⟩ : syracuseStep 2285215 = 3427823) B3427823
theorem B3427829 : Blo 2283435 3427829 := bbase (se 5 (by rfl) ⟨160679, by rfl⟩ : syracuseStep 3427829 = 321359) (by norm_num)
theorem B2285219 : Blo 2283435 2285219 := bstep (se 1 (by rfl) ⟨1713914, by rfl⟩ : syracuseStep 2285219 = 3427829) B3427829
theorem B2440325 : Blo 2283435 2440325 := bbase (se 4 (by rfl) ⟨228780, by rfl⟩ : syracuseStep 2440325 = 457561) (by norm_num)
theorem B6507533 : Blo 2283435 6507533 := bstep (se 3 (by rfl) ⟨1220162, by rfl⟩ : syracuseStep 6507533 = 2440325) B2440325
theorem B4338355 : Blo 2283435 4338355 := bstep (se 1 (by rfl) ⟨3253766, by rfl⟩ : syracuseStep 4338355 = 6507533) B6507533
theorem B5784473 : Blo 2283435 5784473 := bstep (se 2 (by rfl) ⟨2169177, by rfl⟩ : syracuseStep 5784473 = 4338355) B4338355
theorem B3856315 : Blo 2283435 3856315 := bstep (se 1 (by rfl) ⟨2892236, by rfl⟩ : syracuseStep 3856315 = 5784473) B5784473
theorem B5141753 : Blo 2283435 5141753 := bstep (se 2 (by rfl) ⟨1928157, by rfl⟩ : syracuseStep 5141753 = 3856315) B3856315
theorem B3427835 : Blo 2283435 3427835 := bstep (se 1 (by rfl) ⟨2570876, by rfl⟩ : syracuseStep 3427835 = 5141753) B5141753
theorem B2285223 : Blo 2283435 2285223 := bstep (se 1 (by rfl) ⟨1713917, by rfl⟩ : syracuseStep 2285223 = 3427835) B3427835
theorem B2570881 : Blo 2283435 2570881 := bbase (se 2 (by rfl) ⟨964080, by rfl⟩ : syracuseStep 2570881 = 1928161) (by norm_num)
theorem B3427841 : Blo 2283435 3427841 := bstep (se 2 (by rfl) ⟨1285440, by rfl⟩ : syracuseStep 3427841 = 2570881) B2570881
theorem B2285227 : Blo 2283435 2285227 := bstep (se 1 (by rfl) ⟨1713920, by rfl⟩ : syracuseStep 2285227 = 3427841) B3427841
theorem B5784493 : Blo 2283435 5784493 := bbase (se 3 (by rfl) ⟨1084592, by rfl⟩ : syracuseStep 5784493 = 2169185) (by norm_num)
theorem B7712657 : Blo 2283435 7712657 := bstep (se 2 (by rfl) ⟨2892246, by rfl⟩ : syracuseStep 7712657 = 5784493) B5784493
theorem B5141771 : Blo 2283435 5141771 := bstep (se 1 (by rfl) ⟨3856328, by rfl⟩ : syracuseStep 5141771 = 7712657) B7712657
theorem B3427847 : Blo 2283435 3427847 := bstep (se 1 (by rfl) ⟨2570885, by rfl⟩ : syracuseStep 3427847 = 5141771) B5141771
theorem B2285231 : Blo 2283435 2285231 := bstep (se 1 (by rfl) ⟨1713923, by rfl⟩ : syracuseStep 2285231 = 3427847) B3427847
theorem B3427853 : Blo 2283435 3427853 := bbase (se 3 (by rfl) ⟨642722, by rfl⟩ : syracuseStep 3427853 = 1285445) (by norm_num)
theorem B2285235 : Blo 2283435 2285235 := bstep (se 1 (by rfl) ⟨1713926, by rfl⟩ : syracuseStep 2285235 = 3427853) B3427853
theorem B5141789 : Blo 2283435 5141789 := bbase (se 3 (by rfl) ⟨964085, by rfl⟩ : syracuseStep 5141789 = 1928171) (by norm_num)
theorem B3427859 : Blo 2283435 3427859 := bstep (se 1 (by rfl) ⟨2570894, by rfl⟩ : syracuseStep 3427859 = 5141789) B5141789
theorem B2285239 : Blo 2283435 2285239 := bstep (se 1 (by rfl) ⟨1713929, by rfl⟩ : syracuseStep 2285239 = 3427859) B3427859
theorem B3856349 : Blo 2283435 3856349 := bbase (se 3 (by rfl) ⟨723065, by rfl⟩ : syracuseStep 3856349 = 1446131) (by norm_num)
theorem B2570899 : Blo 2283435 2570899 := bstep (se 1 (by rfl) ⟨1928174, by rfl⟩ : syracuseStep 2570899 = 3856349) B3856349
theorem B3427865 : Blo 2283435 3427865 := bstep (se 2 (by rfl) ⟨1285449, by rfl⟩ : syracuseStep 3427865 = 2570899) B2570899
theorem B2285243 : Blo 2283435 2285243 := bstep (se 1 (by rfl) ⟨1713932, by rfl⟩ : syracuseStep 2285243 = 3427865) B3427865
theorem B18531413 : Blo 2283435 18531413 := bbase (se 8 (by rfl) ⟨108582, by rfl⟩ : syracuseStep 18531413 = 217165) (by norm_num)
theorem B12354275 : Blo 2283435 12354275 := bstep (se 1 (by rfl) ⟨9265706, by rfl⟩ : syracuseStep 12354275 = 18531413) B18531413
theorem B8236183 : Blo 2283435 8236183 := bstep (se 1 (by rfl) ⟨6177137, by rfl⟩ : syracuseStep 8236183 = 12354275) B12354275
theorem B10981577 : Blo 2283435 10981577 := bstep (se 2 (by rfl) ⟨4118091, by rfl⟩ : syracuseStep 10981577 = 8236183) B8236183
theorem B7321051 : Blo 2283435 7321051 := bstep (se 1 (by rfl) ⟨5490788, by rfl⟩ : syracuseStep 7321051 = 10981577) B10981577
theorem B9761401 : Blo 2283435 9761401 := bstep (se 2 (by rfl) ⟨3660525, by rfl⟩ : syracuseStep 9761401 = 7321051) B7321051
theorem B13015201 : Blo 2283435 13015201 := bstep (se 2 (by rfl) ⟨4880700, by rfl⟩ : syracuseStep 13015201 = 9761401) B9761401
theorem B17353601 : Blo 2283435 17353601 := bstep (se 2 (by rfl) ⟨6507600, by rfl⟩ : syracuseStep 17353601 = 13015201) B13015201
theorem B11569067 : Blo 2283435 11569067 := bstep (se 1 (by rfl) ⟨8676800, by rfl⟩ : syracuseStep 11569067 = 17353601) B17353601
theorem B7712711 : Blo 2283435 7712711 := bstep (se 1 (by rfl) ⟨5784533, by rfl⟩ : syracuseStep 7712711 = 11569067) B11569067
theorem B5141807 : Blo 2283435 5141807 := bstep (se 1 (by rfl) ⟨3856355, by rfl⟩ : syracuseStep 5141807 = 7712711) B7712711
theorem B3427871 : Blo 2283435 3427871 := bstep (se 1 (by rfl) ⟨2570903, by rfl⟩ : syracuseStep 3427871 = 5141807) B5141807
theorem B2285247 : Blo 2283435 2285247 := bstep (se 1 (by rfl) ⟨1713935, by rfl⟩ : syracuseStep 2285247 = 3427871) B3427871
theorem B3427877 : Blo 2283435 3427877 := bbase (se 4 (by rfl) ⟨321363, by rfl⟩ : syracuseStep 3427877 = 642727) (by norm_num)
theorem B2285251 : Blo 2283435 2285251 := bstep (se 1 (by rfl) ⟨1713938, by rfl⟩ : syracuseStep 2285251 = 3427877) B3427877
theorem B2892277 : Blo 2283435 2892277 := bbase (se 5 (by rfl) ⟨135575, by rfl⟩ : syracuseStep 2892277 = 271151) (by norm_num)
theorem B3856369 : Blo 2283435 3856369 := bstep (se 2 (by rfl) ⟨1446138, by rfl⟩ : syracuseStep 3856369 = 2892277) B2892277
theorem B5141825 : Blo 2283435 5141825 := bstep (se 2 (by rfl) ⟨1928184, by rfl⟩ : syracuseStep 5141825 = 3856369) B3856369
theorem B3427883 : Blo 2283435 3427883 := bstep (se 1 (by rfl) ⟨2570912, by rfl⟩ : syracuseStep 3427883 = 5141825) B5141825
theorem B2285255 : Blo 2283435 2285255 := bstep (se 1 (by rfl) ⟨1713941, by rfl⟩ : syracuseStep 2285255 = 3427883) B3427883
theorem B2570917 : Blo 2283435 2570917 := bbase (se 4 (by rfl) ⟨241023, by rfl⟩ : syracuseStep 2570917 = 482047) (by norm_num)
theorem B3427889 : Blo 2283435 3427889 := bstep (se 2 (by rfl) ⟨1285458, by rfl⟩ : syracuseStep 3427889 = 2570917) B2570917
theorem B2285259 : Blo 2283435 2285259 := bstep (se 1 (by rfl) ⟨1713944, by rfl⟩ : syracuseStep 2285259 = 3427889) B3427889
theorem B11751509 : Blo 2283435 11751509 := bbase (se 8 (by rfl) ⟨68856, by rfl⟩ : syracuseStep 11751509 = 137713) (by norm_num)
theorem B7834339 : Blo 2283435 7834339 := bstep (se 1 (by rfl) ⟨5875754, by rfl⟩ : syracuseStep 7834339 = 11751509) B11751509
theorem B41783141 : Blo 2283435 41783141 := bstep (se 4 (by rfl) ⟨3917169, by rfl⟩ : syracuseStep 41783141 = 7834339) B7834339
theorem B27855427 : Blo 2283435 27855427 := bstep (se 1 (by rfl) ⟨20891570, by rfl⟩ : syracuseStep 27855427 = 41783141) B41783141
theorem B37140569 : Blo 2283435 37140569 := bstep (se 2 (by rfl) ⟨13927713, by rfl⟩ : syracuseStep 37140569 = 27855427) B27855427
theorem B24760379 : Blo 2283435 24760379 := bstep (se 1 (by rfl) ⟨18570284, by rfl⟩ : syracuseStep 24760379 = 37140569) B37140569
theorem B16506919 : Blo 2283435 16506919 := bstep (se 1 (by rfl) ⟨12380189, by rfl⟩ : syracuseStep 16506919 = 24760379) B24760379
theorem B88036901 : Blo 2283435 88036901 := bstep (se 4 (by rfl) ⟨8253459, by rfl⟩ : syracuseStep 88036901 = 16506919) B16506919
theorem B58691267 : Blo 2283435 58691267 := bstep (se 1 (by rfl) ⟨44018450, by rfl⟩ : syracuseStep 58691267 = 88036901) B88036901
theorem B39127511 : Blo 2283435 39127511 := bstep (se 1 (by rfl) ⟨29345633, by rfl⟩ : syracuseStep 39127511 = 58691267) B58691267
theorem B26085007 : Blo 2283435 26085007 := bstep (se 1 (by rfl) ⟨19563755, by rfl⟩ : syracuseStep 26085007 = 39127511) B39127511
theorem B34780009 : Blo 2283435 34780009 := bstep (se 2 (by rfl) ⟨13042503, by rfl⟩ : syracuseStep 34780009 = 26085007) B26085007
theorem B46373345 : Blo 2283435 46373345 := bstep (se 2 (by rfl) ⟨17390004, by rfl⟩ : syracuseStep 46373345 = 34780009) B34780009
theorem B30915563 : Blo 2283435 30915563 := bstep (se 1 (by rfl) ⟨23186672, by rfl⟩ : syracuseStep 30915563 = 46373345) B46373345
theorem B329766005 : Blo 2283435 329766005 := bstep (se 5 (by rfl) ⟨15457781, by rfl⟩ : syracuseStep 329766005 = 30915563) B30915563
theorem B219844003 : Blo 2283435 219844003 := bstep (se 1 (by rfl) ⟨164883002, by rfl⟩ : syracuseStep 219844003 = 329766005) B329766005
theorem B293125337 : Blo 2283435 293125337 := bstep (se 2 (by rfl) ⟨109922001, by rfl⟩ : syracuseStep 293125337 = 219844003) B219844003
theorem B195416891 : Blo 2283435 195416891 := bstep (se 1 (by rfl) ⟨146562668, by rfl⟩ : syracuseStep 195416891 = 293125337) B293125337
theorem B130277927 : Blo 2283435 130277927 := bstep (se 1 (by rfl) ⟨97708445, by rfl⟩ : syracuseStep 130277927 = 195416891) B195416891
theorem B347407805 : Blo 2283435 347407805 := bstep (se 3 (by rfl) ⟨65138963, by rfl⟩ : syracuseStep 347407805 = 130277927) B130277927
theorem B231605203 : Blo 2283435 231605203 := bstep (se 1 (by rfl) ⟨173703902, by rfl⟩ : syracuseStep 231605203 = 347407805) B347407805
theorem B308806937 : Blo 2283435 308806937 := bstep (se 2 (by rfl) ⟨115802601, by rfl⟩ : syracuseStep 308806937 = 231605203) B231605203
theorem B205871291 : Blo 2283435 205871291 := bstep (se 1 (by rfl) ⟨154403468, by rfl⟩ : syracuseStep 205871291 = 308806937) B308806937
theorem B137247527 : Blo 2283435 137247527 := bstep (se 1 (by rfl) ⟨102935645, by rfl⟩ : syracuseStep 137247527 = 205871291) B205871291
theorem B91498351 : Blo 2283435 91498351 := bstep (se 1 (by rfl) ⟨68623763, by rfl⟩ : syracuseStep 91498351 = 137247527) B137247527
theorem B121997801 : Blo 2283435 121997801 := bstep (se 2 (by rfl) ⟨45749175, by rfl⟩ : syracuseStep 121997801 = 91498351) B91498351
theorem B81331867 : Blo 2283435 81331867 := bstep (se 1 (by rfl) ⟨60998900, by rfl⟩ : syracuseStep 81331867 = 121997801) B121997801
theorem B108442489 : Blo 2283435 108442489 := bstep (se 2 (by rfl) ⟨40665933, by rfl⟩ : syracuseStep 108442489 = 81331867) B81331867
theorem B144589985 : Blo 2283435 144589985 := bstep (se 2 (by rfl) ⟨54221244, by rfl⟩ : syracuseStep 144589985 = 108442489) B108442489
theorem B96393323 : Blo 2283435 96393323 := bstep (se 1 (by rfl) ⟨72294992, by rfl⟩ : syracuseStep 96393323 = 144589985) B144589985
theorem B64262215 : Blo 2283435 64262215 := bstep (se 1 (by rfl) ⟨48196661, by rfl⟩ : syracuseStep 64262215 = 96393323) B96393323
theorem B85682953 : Blo 2283435 85682953 := bstep (se 2 (by rfl) ⟨32131107, by rfl⟩ : syracuseStep 85682953 = 64262215) B64262215
theorem B456975749 : Blo 2283435 456975749 := bstep (se 4 (by rfl) ⟨42841476, by rfl⟩ : syracuseStep 456975749 = 85682953) B85682953
theorem B304650499 : Blo 2283435 304650499 := bstep (se 1 (by rfl) ⟨228487874, by rfl⟩ : syracuseStep 304650499 = 456975749) B456975749
theorem B406200665 : Blo 2283435 406200665 := bstep (se 2 (by rfl) ⟨152325249, by rfl⟩ : syracuseStep 406200665 = 304650499) B304650499
theorem B270800443 : Blo 2283435 270800443 := bstep (se 1 (by rfl) ⟨203100332, by rfl⟩ : syracuseStep 270800443 = 406200665) B406200665
theorem B361067257 : Blo 2283435 361067257 := bstep (se 2 (by rfl) ⟨135400221, by rfl⟩ : syracuseStep 361067257 = 270800443) B270800443
theorem B481423009 : Blo 2283435 481423009 := bstep (se 2 (by rfl) ⟨180533628, by rfl⟩ : syracuseStep 481423009 = 361067257) B361067257
theorem B641897345 : Blo 2283435 641897345 := bstep (se 2 (by rfl) ⟨240711504, by rfl⟩ : syracuseStep 641897345 = 481423009) B481423009
theorem B1711726253 : Blo 2283435 1711726253 := bstep (se 3 (by rfl) ⟨320948672, by rfl⟩ : syracuseStep 1711726253 = 641897345) B641897345
theorem B1141150835 : Blo 2283435 1141150835 := bstep (se 1 (by rfl) ⟨855863126, by rfl⟩ : syracuseStep 1141150835 = 1711726253) B1711726253
theorem B760767223 : Blo 2283435 760767223 := bstep (se 1 (by rfl) ⟨570575417, by rfl⟩ : syracuseStep 760767223 = 1141150835) B1141150835
theorem B1014356297 : Blo 2283435 1014356297 := bstep (se 2 (by rfl) ⟨380383611, by rfl⟩ : syracuseStep 1014356297 = 760767223) B760767223
theorem B676237531 : Blo 2283435 676237531 := bstep (se 1 (by rfl) ⟨507178148, by rfl⟩ : syracuseStep 676237531 = 1014356297) B1014356297
theorem B901650041 : Blo 2283435 901650041 := bstep (se 2 (by rfl) ⟨338118765, by rfl⟩ : syracuseStep 901650041 = 676237531) B676237531
theorem B601100027 : Blo 2283435 601100027 := bstep (se 1 (by rfl) ⟨450825020, by rfl⟩ : syracuseStep 601100027 = 901650041) B901650041
theorem B400733351 : Blo 2283435 400733351 := bstep (se 1 (by rfl) ⟨300550013, by rfl⟩ : syracuseStep 400733351 = 601100027) B601100027
theorem B267155567 : Blo 2283435 267155567 := bstep (se 1 (by rfl) ⟨200366675, by rfl⟩ : syracuseStep 267155567 = 400733351) B400733351
theorem B178103711 : Blo 2283435 178103711 := bstep (se 1 (by rfl) ⟨133577783, by rfl⟩ : syracuseStep 178103711 = 267155567) B267155567
theorem B118735807 : Blo 2283435 118735807 := bstep (se 1 (by rfl) ⟨89051855, by rfl⟩ : syracuseStep 118735807 = 178103711) B178103711
theorem B158314409 : Blo 2283435 158314409 := bstep (se 2 (by rfl) ⟨59367903, by rfl⟩ : syracuseStep 158314409 = 118735807) B118735807
theorem B105542939 : Blo 2283435 105542939 := bstep (se 1 (by rfl) ⟨79157204, by rfl⟩ : syracuseStep 105542939 = 158314409) B158314409
theorem B70361959 : Blo 2283435 70361959 := bstep (se 1 (by rfl) ⟨52771469, by rfl⟩ : syracuseStep 70361959 = 105542939) B105542939
theorem B93815945 : Blo 2283435 93815945 := bstep (se 2 (by rfl) ⟨35180979, by rfl⟩ : syracuseStep 93815945 = 70361959) B70361959
theorem B62543963 : Blo 2283435 62543963 := bstep (se 1 (by rfl) ⟨46907972, by rfl⟩ : syracuseStep 62543963 = 93815945) B93815945
theorem B41695975 : Blo 2283435 41695975 := bstep (se 1 (by rfl) ⟨31271981, by rfl⟩ : syracuseStep 41695975 = 62543963) B62543963
theorem B55594633 : Blo 2283435 55594633 := bstep (se 2 (by rfl) ⟨20847987, by rfl⟩ : syracuseStep 55594633 = 41695975) B41695975
theorem B74126177 : Blo 2283435 74126177 := bstep (se 2 (by rfl) ⟨27797316, by rfl⟩ : syracuseStep 74126177 = 55594633) B55594633
theorem B49417451 : Blo 2283435 49417451 := bstep (se 1 (by rfl) ⟨37063088, by rfl⟩ : syracuseStep 49417451 = 74126177) B74126177
theorem B32944967 : Blo 2283435 32944967 := bstep (se 1 (by rfl) ⟨24708725, by rfl⟩ : syracuseStep 32944967 = 49417451) B49417451
theorem B21963311 : Blo 2283435 21963311 := bstep (se 1 (by rfl) ⟨16472483, by rfl⟩ : syracuseStep 21963311 = 32944967) B32944967
theorem B14642207 : Blo 2283435 14642207 := bstep (se 1 (by rfl) ⟨10981655, by rfl⟩ : syracuseStep 14642207 = 21963311) B21963311
theorem B9761471 : Blo 2283435 9761471 := bstep (se 1 (by rfl) ⟨7321103, by rfl⟩ : syracuseStep 9761471 = 14642207) B14642207
theorem B6507647 : Blo 2283435 6507647 := bstep (se 1 (by rfl) ⟨4880735, by rfl⟩ : syracuseStep 6507647 = 9761471) B9761471
theorem B4338431 : Blo 2283435 4338431 := bstep (se 1 (by rfl) ⟨3253823, by rfl⟩ : syracuseStep 4338431 = 6507647) B6507647
theorem B2892287 : Blo 2283435 2892287 := bstep (se 1 (by rfl) ⟨2169215, by rfl⟩ : syracuseStep 2892287 = 4338431) B4338431
theorem B7712765 : Blo 2283435 7712765 := bstep (se 3 (by rfl) ⟨1446143, by rfl⟩ : syracuseStep 7712765 = 2892287) B2892287
theorem B5141843 : Blo 2283435 5141843 := bstep (se 1 (by rfl) ⟨3856382, by rfl⟩ : syracuseStep 5141843 = 7712765) B7712765
theorem B3427895 : Blo 2283435 3427895 := bstep (se 1 (by rfl) ⟨2570921, by rfl⟩ : syracuseStep 3427895 = 5141843) B5141843
theorem B2285263 : Blo 2283435 2285263 := bstep (se 1 (by rfl) ⟨1713947, by rfl⟩ : syracuseStep 2285263 = 3427895) B3427895
theorem B3427901 : Blo 2283435 3427901 := bbase (se 3 (by rfl) ⟨642731, by rfl⟩ : syracuseStep 3427901 = 1285463) (by norm_num)
theorem B2285267 : Blo 2283435 2285267 := bstep (se 1 (by rfl) ⟨1713950, by rfl⟩ : syracuseStep 2285267 = 3427901) B3427901
theorem B5141861 : Blo 2283435 5141861 := bbase (se 4 (by rfl) ⟨482049, by rfl⟩ : syracuseStep 5141861 = 964099) (by norm_num)
theorem B3427907 : Blo 2283435 3427907 := bstep (se 1 (by rfl) ⟨2570930, by rfl⟩ : syracuseStep 3427907 = 5141861) B5141861
theorem B2285271 : Blo 2283435 2285271 := bstep (se 1 (by rfl) ⟨1713953, by rfl⟩ : syracuseStep 2285271 = 3427907) B3427907
theorem B5784605 : Blo 2283435 5784605 := bbase (se 3 (by rfl) ⟨1084613, by rfl⟩ : syracuseStep 5784605 = 2169227) (by norm_num)
theorem B3856403 : Blo 2283435 3856403 := bstep (se 1 (by rfl) ⟨2892302, by rfl⟩ : syracuseStep 3856403 = 5784605) B5784605
theorem B2570935 : Blo 2283435 2570935 := bstep (se 1 (by rfl) ⟨1928201, by rfl⟩ : syracuseStep 2570935 = 3856403) B3856403
theorem B3427913 : Blo 2283435 3427913 := bstep (se 2 (by rfl) ⟨1285467, by rfl⟩ : syracuseStep 3427913 = 2570935) B2570935
theorem B2285275 : Blo 2283435 2285275 := bstep (se 1 (by rfl) ⟨1713956, by rfl⟩ : syracuseStep 2285275 = 3427913) B3427913
theorem B4338461 : Blo 2283435 4338461 := bbase (se 3 (by rfl) ⟨813461, by rfl⟩ : syracuseStep 4338461 = 1626923) (by norm_num)
theorem B11569229 : Blo 2283435 11569229 := bstep (se 3 (by rfl) ⟨2169230, by rfl⟩ : syracuseStep 11569229 = 4338461) B4338461
theorem B7712819 : Blo 2283435 7712819 := bstep (se 1 (by rfl) ⟨5784614, by rfl⟩ : syracuseStep 7712819 = 11569229) B11569229
theorem B5141879 : Blo 2283435 5141879 := bstep (se 1 (by rfl) ⟨3856409, by rfl⟩ : syracuseStep 5141879 = 7712819) B7712819
theorem B3427919 : Blo 2283435 3427919 := bstep (se 1 (by rfl) ⟨2570939, by rfl⟩ : syracuseStep 3427919 = 5141879) B5141879
theorem B2285279 : Blo 2283435 2285279 := bstep (se 1 (by rfl) ⟨1713959, by rfl⟩ : syracuseStep 2285279 = 3427919) B3427919
theorem B3427925 : Blo 2283435 3427925 := bbase (se 8 (by rfl) ⟨20085, by rfl⟩ : syracuseStep 3427925 = 40171) (by norm_num)
theorem B2285283 : Blo 2283435 2285283 := bstep (se 1 (by rfl) ⟨1713962, by rfl⟩ : syracuseStep 2285283 = 3427925) B3427925
theorem B9761573 : Blo 2283435 9761573 := bbase (se 4 (by rfl) ⟨915147, by rfl⟩ : syracuseStep 9761573 = 1830295) (by norm_num)
theorem B6507715 : Blo 2283435 6507715 := bstep (se 1 (by rfl) ⟨4880786, by rfl⟩ : syracuseStep 6507715 = 9761573) B9761573
theorem B8676953 : Blo 2283435 8676953 := bstep (se 2 (by rfl) ⟨3253857, by rfl⟩ : syracuseStep 8676953 = 6507715) B6507715
theorem B5784635 : Blo 2283435 5784635 := bstep (se 1 (by rfl) ⟨4338476, by rfl⟩ : syracuseStep 5784635 = 8676953) B8676953
theorem B3856423 : Blo 2283435 3856423 := bstep (se 1 (by rfl) ⟨2892317, by rfl⟩ : syracuseStep 3856423 = 5784635) B5784635
theorem B5141897 : Blo 2283435 5141897 := bstep (se 2 (by rfl) ⟨1928211, by rfl⟩ : syracuseStep 5141897 = 3856423) B3856423
theorem B3427931 : Blo 2283435 3427931 := bstep (se 1 (by rfl) ⟨2570948, by rfl⟩ : syracuseStep 3427931 = 5141897) B5141897
theorem B2285287 : Blo 2283435 2285287 := bstep (se 1 (by rfl) ⟨1713965, by rfl⟩ : syracuseStep 2285287 = 3427931) B3427931
theorem B2570953 : Blo 2283435 2570953 := bbase (se 2 (by rfl) ⟨964107, by rfl⟩ : syracuseStep 2570953 = 1928215) (by norm_num)
theorem B3427937 : Blo 2283435 3427937 := bstep (se 2 (by rfl) ⟨1285476, by rfl⟩ : syracuseStep 3427937 = 2570953) B2570953
theorem B2285291 : Blo 2283435 2285291 := bstep (se 1 (by rfl) ⟨1713968, by rfl⟩ : syracuseStep 2285291 = 3427937) B3427937
theorem B7321205 : Blo 2283435 7321205 := bbase (se 5 (by rfl) ⟨343181, by rfl⟩ : syracuseStep 7321205 = 686363) (by norm_num)
theorem B19523213 : Blo 2283435 19523213 := bstep (se 3 (by rfl) ⟨3660602, by rfl⟩ : syracuseStep 19523213 = 7321205) B7321205
theorem B13015475 : Blo 2283435 13015475 := bstep (se 1 (by rfl) ⟨9761606, by rfl⟩ : syracuseStep 13015475 = 19523213) B19523213
theorem B8676983 : Blo 2283435 8676983 := bstep (se 1 (by rfl) ⟨6507737, by rfl⟩ : syracuseStep 8676983 = 13015475) B13015475
theorem B5784655 : Blo 2283435 5784655 := bstep (se 1 (by rfl) ⟨4338491, by rfl⟩ : syracuseStep 5784655 = 8676983) B8676983
theorem B7712873 : Blo 2283435 7712873 := bstep (se 2 (by rfl) ⟨2892327, by rfl⟩ : syracuseStep 7712873 = 5784655) B5784655
theorem B5141915 : Blo 2283435 5141915 := bstep (se 1 (by rfl) ⟨3856436, by rfl⟩ : syracuseStep 5141915 = 7712873) B7712873
theorem B3427943 : Blo 2283435 3427943 := bstep (se 1 (by rfl) ⟨2570957, by rfl⟩ : syracuseStep 3427943 = 5141915) B5141915
theorem B2285295 : Blo 2283435 2285295 := bstep (se 1 (by rfl) ⟨1713971, by rfl⟩ : syracuseStep 2285295 = 3427943) B3427943
theorem B3427949 : Blo 2283435 3427949 := bbase (se 3 (by rfl) ⟨642740, by rfl⟩ : syracuseStep 3427949 = 1285481) (by norm_num)
theorem B2285299 : Blo 2283435 2285299 := bstep (se 1 (by rfl) ⟨1713974, by rfl⟩ : syracuseStep 2285299 = 3427949) B3427949
theorem B5141933 : Blo 2283435 5141933 := bbase (se 3 (by rfl) ⟨964112, by rfl⟩ : syracuseStep 5141933 = 1928225) (by norm_num)
theorem B3427955 : Blo 2283435 3427955 := bstep (se 1 (by rfl) ⟨2570966, by rfl⟩ : syracuseStep 3427955 = 5141933) B5141933
theorem B2285303 : Blo 2283435 2285303 := bstep (se 1 (by rfl) ⟨1713977, by rfl⟩ : syracuseStep 2285303 = 3427955) B3427955
theorem B3474733 : Blo 2283435 3474733 := bbase (se 3 (by rfl) ⟨651512, by rfl⟩ : syracuseStep 3474733 = 1303025) (by norm_num)
theorem B4632977 : Blo 2283435 4632977 := bstep (se 2 (by rfl) ⟨1737366, by rfl⟩ : syracuseStep 4632977 = 3474733) B3474733
theorem B12354605 : Blo 2283435 12354605 := bstep (se 3 (by rfl) ⟨2316488, by rfl⟩ : syracuseStep 12354605 = 4632977) B4632977
theorem B8236403 : Blo 2283435 8236403 := bstep (se 1 (by rfl) ⟨6177302, by rfl⟩ : syracuseStep 8236403 = 12354605) B12354605
theorem B5490935 : Blo 2283435 5490935 := bstep (se 1 (by rfl) ⟨4118201, by rfl⟩ : syracuseStep 5490935 = 8236403) B8236403
theorem B3660623 : Blo 2283435 3660623 := bstep (se 1 (by rfl) ⟨2745467, by rfl⟩ : syracuseStep 3660623 = 5490935) B5490935
theorem B2440415 : Blo 2283435 2440415 := bstep (se 1 (by rfl) ⟨1830311, by rfl⟩ : syracuseStep 2440415 = 3660623) B3660623
theorem B6507773 : Blo 2283435 6507773 := bstep (se 3 (by rfl) ⟨1220207, by rfl⟩ : syracuseStep 6507773 = 2440415) B2440415
theorem B4338515 : Blo 2283435 4338515 := bstep (se 1 (by rfl) ⟨3253886, by rfl⟩ : syracuseStep 4338515 = 6507773) B6507773
theorem B2892343 : Blo 2283435 2892343 := bstep (se 1 (by rfl) ⟨2169257, by rfl⟩ : syracuseStep 2892343 = 4338515) B4338515
theorem B3856457 : Blo 2283435 3856457 := bstep (se 2 (by rfl) ⟨1446171, by rfl⟩ : syracuseStep 3856457 = 2892343) B2892343
theorem B2570971 : Blo 2283435 2570971 := bstep (se 1 (by rfl) ⟨1928228, by rfl⟩ : syracuseStep 2570971 = 3856457) B3856457
theorem B3427961 : Blo 2283435 3427961 := bstep (se 2 (by rfl) ⟨1285485, by rfl⟩ : syracuseStep 3427961 = 2570971) B2570971
theorem B2285307 : Blo 2283435 2285307 := bstep (se 1 (by rfl) ⟨1713980, by rfl⟩ : syracuseStep 2285307 = 3427961) B3427961
theorem B6261589 : Blo 2283435 6261589 := bbase (se 9 (by rfl) ⟨18344, by rfl⟩ : syracuseStep 6261589 = 36689) (by norm_num)
theorem B33395141 : Blo 2283435 33395141 := bstep (se 4 (by rfl) ⟨3130794, by rfl⟩ : syracuseStep 33395141 = 6261589) B6261589
theorem B22263427 : Blo 2283435 22263427 := bstep (se 1 (by rfl) ⟨16697570, by rfl⟩ : syracuseStep 22263427 = 33395141) B33395141
theorem B29684569 : Blo 2283435 29684569 := bstep (se 2 (by rfl) ⟨11131713, by rfl⟩ : syracuseStep 29684569 = 22263427) B22263427
theorem B39579425 : Blo 2283435 39579425 := bstep (se 2 (by rfl) ⟨14842284, by rfl⟩ : syracuseStep 39579425 = 29684569) B29684569
theorem B26386283 : Blo 2283435 26386283 := bstep (se 1 (by rfl) ⟨19789712, by rfl⟩ : syracuseStep 26386283 = 39579425) B39579425
theorem B17590855 : Blo 2283435 17590855 := bstep (se 1 (by rfl) ⟨13193141, by rfl⟩ : syracuseStep 17590855 = 26386283) B26386283
theorem B23454473 : Blo 2283435 23454473 := bstep (se 2 (by rfl) ⟨8795427, by rfl⟩ : syracuseStep 23454473 = 17590855) B17590855
theorem B250181045 : Blo 2283435 250181045 := bstep (se 5 (by rfl) ⟨11727236, by rfl⟩ : syracuseStep 250181045 = 23454473) B23454473
theorem B166787363 : Blo 2283435 166787363 := bstep (se 1 (by rfl) ⟨125090522, by rfl⟩ : syracuseStep 166787363 = 250181045) B250181045
theorem B111191575 : Blo 2283435 111191575 := bstep (se 1 (by rfl) ⟨83393681, by rfl⟩ : syracuseStep 111191575 = 166787363) B166787363
theorem B148255433 : Blo 2283435 148255433 := bstep (se 2 (by rfl) ⟨55595787, by rfl⟩ : syracuseStep 148255433 = 111191575) B111191575
theorem B98836955 : Blo 2283435 98836955 := bstep (se 1 (by rfl) ⟨74127716, by rfl⟩ : syracuseStep 98836955 = 148255433) B148255433
theorem B65891303 : Blo 2283435 65891303 := bstep (se 1 (by rfl) ⟨49418477, by rfl⟩ : syracuseStep 65891303 = 98836955) B98836955
theorem B43927535 : Blo 2283435 43927535 := bstep (se 1 (by rfl) ⟨32945651, by rfl⟩ : syracuseStep 43927535 = 65891303) B65891303
theorem B29285023 : Blo 2283435 29285023 := bstep (se 1 (by rfl) ⟨21963767, by rfl⟩ : syracuseStep 29285023 = 43927535) B43927535
theorem B39046697 : Blo 2283435 39046697 := bstep (se 2 (by rfl) ⟨14642511, by rfl⟩ : syracuseStep 39046697 = 29285023) B29285023
theorem B26031131 : Blo 2283435 26031131 := bstep (se 1 (by rfl) ⟨19523348, by rfl⟩ : syracuseStep 26031131 = 39046697) B39046697
theorem B17354087 : Blo 2283435 17354087 := bstep (se 1 (by rfl) ⟨13015565, by rfl⟩ : syracuseStep 17354087 = 26031131) B26031131
theorem B11569391 : Blo 2283435 11569391 := bstep (se 1 (by rfl) ⟨8677043, by rfl⟩ : syracuseStep 11569391 = 17354087) B17354087
theorem B7712927 : Blo 2283435 7712927 := bstep (se 1 (by rfl) ⟨5784695, by rfl⟩ : syracuseStep 7712927 = 11569391) B11569391
theorem B5141951 : Blo 2283435 5141951 := bstep (se 1 (by rfl) ⟨3856463, by rfl⟩ : syracuseStep 5141951 = 7712927) B7712927
theorem B3427967 : Blo 2283435 3427967 := bstep (se 1 (by rfl) ⟨2570975, by rfl⟩ : syracuseStep 3427967 = 5141951) B5141951
theorem B2285311 : Blo 2283435 2285311 := bstep (se 1 (by rfl) ⟨1713983, by rfl⟩ : syracuseStep 2285311 = 3427967) B3427967
theorem B3427973 : Blo 2283435 3427973 := bbase (se 4 (by rfl) ⟨321372, by rfl⟩ : syracuseStep 3427973 = 642745) (by norm_num)
theorem B2285315 : Blo 2283435 2285315 := bstep (se 1 (by rfl) ⟨1713986, by rfl⟩ : syracuseStep 2285315 = 3427973) B3427973
theorem B3856477 : Blo 2283435 3856477 := bbase (se 3 (by rfl) ⟨723089, by rfl⟩ : syracuseStep 3856477 = 1446179) (by norm_num)
theorem B5141969 : Blo 2283435 5141969 := bstep (se 2 (by rfl) ⟨1928238, by rfl⟩ : syracuseStep 5141969 = 3856477) B3856477
theorem B3427979 : Blo 2283435 3427979 := bstep (se 1 (by rfl) ⟨2570984, by rfl⟩ : syracuseStep 3427979 = 5141969) B5141969
theorem B2285319 : Blo 2283435 2285319 := bstep (se 1 (by rfl) ⟨1713989, by rfl⟩ : syracuseStep 2285319 = 3427979) B3427979
theorem B2570989 : Blo 2283435 2570989 := bbase (se 3 (by rfl) ⟨482060, by rfl⟩ : syracuseStep 2570989 = 964121) (by norm_num)
theorem B3427985 : Blo 2283435 3427985 := bstep (se 2 (by rfl) ⟨1285494, by rfl⟩ : syracuseStep 3427985 = 2570989) B2570989
theorem B2285323 : Blo 2283435 2285323 := bstep (se 1 (by rfl) ⟨1713992, by rfl⟩ : syracuseStep 2285323 = 3427985) B3427985
theorem B7712981 : Blo 2283435 7712981 := bbase (se 7 (by rfl) ⟨90386, by rfl⟩ : syracuseStep 7712981 = 180773) (by norm_num)
theorem B5141987 : Blo 2283435 5141987 := bstep (se 1 (by rfl) ⟨3856490, by rfl⟩ : syracuseStep 5141987 = 7712981) B7712981
theorem B3427991 : Blo 2283435 3427991 := bstep (se 1 (by rfl) ⟨2570993, by rfl⟩ : syracuseStep 3427991 = 5141987) B5141987
theorem B2285327 : Blo 2283435 2285327 := bstep (se 1 (by rfl) ⟨1713995, by rfl⟩ : syracuseStep 2285327 = 3427991) B3427991
theorem B3427997 : Blo 2283435 3427997 := bbase (se 3 (by rfl) ⟨642749, by rfl⟩ : syracuseStep 3427997 = 1285499) (by norm_num)
theorem B2285331 : Blo 2283435 2285331 := bstep (se 1 (by rfl) ⟨1713998, by rfl⟩ : syracuseStep 2285331 = 3427997) B3427997
theorem B5142005 : Blo 2283435 5142005 := bbase (se 5 (by rfl) ⟨241031, by rfl⟩ : syracuseStep 5142005 = 482063) (by norm_num)
theorem B3428003 : Blo 2283435 3428003 := bstep (se 1 (by rfl) ⟨2571002, by rfl⟩ : syracuseStep 3428003 = 5142005) B5142005
theorem B2285335 : Blo 2283435 2285335 := bstep (se 1 (by rfl) ⟨1714001, by rfl⟩ : syracuseStep 2285335 = 3428003) B3428003
theorem B12354773 : Blo 2283435 12354773 := bbase (se 7 (by rfl) ⟨144782, by rfl⟩ : syracuseStep 12354773 = 289565) (by norm_num)
theorem B32946061 : Blo 2283435 32946061 := bstep (se 3 (by rfl) ⟨6177386, by rfl⟩ : syracuseStep 32946061 = 12354773) B12354773
theorem B43928081 : Blo 2283435 43928081 := bstep (se 2 (by rfl) ⟨16473030, by rfl⟩ : syracuseStep 43928081 = 32946061) B32946061
theorem B29285387 : Blo 2283435 29285387 := bstep (se 1 (by rfl) ⟨21964040, by rfl⟩ : syracuseStep 29285387 = 43928081) B43928081
theorem B19523591 : Blo 2283435 19523591 := bstep (se 1 (by rfl) ⟨14642693, by rfl⟩ : syracuseStep 19523591 = 29285387) B29285387
theorem B13015727 : Blo 2283435 13015727 := bstep (se 1 (by rfl) ⟨9761795, by rfl⟩ : syracuseStep 13015727 = 19523591) B19523591
theorem B8677151 : Blo 2283435 8677151 := bstep (se 1 (by rfl) ⟨6507863, by rfl⟩ : syracuseStep 8677151 = 13015727) B13015727
theorem B5784767 : Blo 2283435 5784767 := bstep (se 1 (by rfl) ⟨4338575, by rfl⟩ : syracuseStep 5784767 = 8677151) B8677151
theorem B3856511 : Blo 2283435 3856511 := bstep (se 1 (by rfl) ⟨2892383, by rfl⟩ : syracuseStep 3856511 = 5784767) B5784767
theorem B2571007 : Blo 2283435 2571007 := bstep (se 1 (by rfl) ⟨1928255, by rfl⟩ : syracuseStep 2571007 = 3856511) B3856511
theorem B3428009 : Blo 2283435 3428009 := bstep (se 2 (by rfl) ⟨1285503, by rfl⟩ : syracuseStep 3428009 = 2571007) B2571007
theorem B2285339 : Blo 2283435 2285339 := bstep (se 1 (by rfl) ⟨1714004, by rfl⟩ : syracuseStep 2285339 = 3428009) B3428009
theorem B2440453 : Blo 2283435 2440453 := bbase (se 4 (by rfl) ⟨228792, by rfl⟩ : syracuseStep 2440453 = 457585) (by norm_num)
theorem B3253937 : Blo 2283435 3253937 := bstep (se 2 (by rfl) ⟨1220226, by rfl⟩ : syracuseStep 3253937 = 2440453) B2440453
theorem B8677165 : Blo 2283435 8677165 := bstep (se 3 (by rfl) ⟨1626968, by rfl⟩ : syracuseStep 8677165 = 3253937) B3253937
theorem B11569553 : Blo 2283435 11569553 := bstep (se 2 (by rfl) ⟨4338582, by rfl⟩ : syracuseStep 11569553 = 8677165) B8677165
theorem B7713035 : Blo 2283435 7713035 := bstep (se 1 (by rfl) ⟨5784776, by rfl⟩ : syracuseStep 7713035 = 11569553) B11569553
theorem B5142023 : Blo 2283435 5142023 := bstep (se 1 (by rfl) ⟨3856517, by rfl⟩ : syracuseStep 5142023 = 7713035) B7713035
theorem B3428015 : Blo 2283435 3428015 := bstep (se 1 (by rfl) ⟨2571011, by rfl⟩ : syracuseStep 3428015 = 5142023) B5142023
theorem B2285343 : Blo 2283435 2285343 := bstep (se 1 (by rfl) ⟨1714007, by rfl⟩ : syracuseStep 2285343 = 3428015) B3428015
theorem B3428021 : Blo 2283435 3428021 := bbase (se 5 (by rfl) ⟨160688, by rfl⟩ : syracuseStep 3428021 = 321377) (by norm_num)
theorem B2285347 : Blo 2283435 2285347 := bstep (se 1 (by rfl) ⟨1714010, by rfl⟩ : syracuseStep 2285347 = 3428021) B3428021
theorem B5784797 : Blo 2283435 5784797 := bbase (se 3 (by rfl) ⟨1084649, by rfl⟩ : syracuseStep 5784797 = 2169299) (by norm_num)
theorem B3856531 : Blo 2283435 3856531 := bstep (se 1 (by rfl) ⟨2892398, by rfl⟩ : syracuseStep 3856531 = 5784797) B5784797
theorem B5142041 : Blo 2283435 5142041 := bstep (se 2 (by rfl) ⟨1928265, by rfl⟩ : syracuseStep 5142041 = 3856531) B3856531
theorem B3428027 : Blo 2283435 3428027 := bstep (se 1 (by rfl) ⟨2571020, by rfl⟩ : syracuseStep 3428027 = 5142041) B5142041
theorem B2285351 : Blo 2283435 2285351 := bstep (se 1 (by rfl) ⟨1714013, by rfl⟩ : syracuseStep 2285351 = 3428027) B3428027
theorem B2571025 : Blo 2283435 2571025 := bbase (se 2 (by rfl) ⟨964134, by rfl⟩ : syracuseStep 2571025 = 1928269) (by norm_num)
theorem B3428033 : Blo 2283435 3428033 := bstep (se 2 (by rfl) ⟨1285512, by rfl⟩ : syracuseStep 3428033 = 2571025) B2571025
theorem B2285355 : Blo 2283435 2285355 := bstep (se 1 (by rfl) ⟨1714016, by rfl⟩ : syracuseStep 2285355 = 3428033) B3428033
theorem B4338613 : Blo 2283435 4338613 := bbase (se 5 (by rfl) ⟨203372, by rfl⟩ : syracuseStep 4338613 = 406745) (by norm_num)
theorem B5784817 : Blo 2283435 5784817 := bstep (se 2 (by rfl) ⟨2169306, by rfl⟩ : syracuseStep 5784817 = 4338613) B4338613
theorem B7713089 : Blo 2283435 7713089 := bstep (se 2 (by rfl) ⟨2892408, by rfl⟩ : syracuseStep 7713089 = 5784817) B5784817
theorem B5142059 : Blo 2283435 5142059 := bstep (se 1 (by rfl) ⟨3856544, by rfl⟩ : syracuseStep 5142059 = 7713089) B7713089
theorem B3428039 : Blo 2283435 3428039 := bstep (se 1 (by rfl) ⟨2571029, by rfl⟩ : syracuseStep 3428039 = 5142059) B5142059
theorem B2285359 : Blo 2283435 2285359 := bstep (se 1 (by rfl) ⟨1714019, by rfl⟩ : syracuseStep 2285359 = 3428039) B3428039
theorem B3428045 : Blo 2283435 3428045 := bbase (se 3 (by rfl) ⟨642758, by rfl⟩ : syracuseStep 3428045 = 1285517) (by norm_num)
theorem B2285363 : Blo 2283435 2285363 := bstep (se 1 (by rfl) ⟨1714022, by rfl⟩ : syracuseStep 2285363 = 3428045) B3428045
theorem B5142077 : Blo 2283435 5142077 := bbase (se 3 (by rfl) ⟨964139, by rfl⟩ : syracuseStep 5142077 = 1928279) (by norm_num)
theorem B3428051 : Blo 2283435 3428051 := bstep (se 1 (by rfl) ⟨2571038, by rfl⟩ : syracuseStep 3428051 = 5142077) B5142077
theorem B2285367 : Blo 2283435 2285367 := bstep (se 1 (by rfl) ⟨1714025, by rfl⟩ : syracuseStep 2285367 = 3428051) B3428051
theorem B3856565 : Blo 2283435 3856565 := bbase (se 5 (by rfl) ⟨180776, by rfl⟩ : syracuseStep 3856565 = 361553) (by norm_num)
theorem B2571043 : Blo 2283435 2571043 := bstep (se 1 (by rfl) ⟨1928282, by rfl⟩ : syracuseStep 2571043 = 3856565) B3856565
theorem B3428057 : Blo 2283435 3428057 := bstep (se 2 (by rfl) ⟨1285521, by rfl⟩ : syracuseStep 3428057 = 2571043) B2571043
theorem B2285371 : Blo 2283435 2285371 := bstep (se 1 (by rfl) ⟨1714028, by rfl⟩ : syracuseStep 2285371 = 3428057) B3428057
theorem B2316557 : Blo 2283435 2316557 := bbase (se 3 (by rfl) ⟨434354, by rfl⟩ : syracuseStep 2316557 = 868709) (by norm_num)
theorem B6177485 : Blo 2283435 6177485 := bstep (se 3 (by rfl) ⟨1158278, by rfl⟩ : syracuseStep 6177485 = 2316557) B2316557
theorem B4118323 : Blo 2283435 4118323 := bstep (se 1 (by rfl) ⟨3088742, by rfl⟩ : syracuseStep 4118323 = 6177485) B6177485
theorem B5491097 : Blo 2283435 5491097 := bstep (se 2 (by rfl) ⟨2059161, by rfl⟩ : syracuseStep 5491097 = 4118323) B4118323
theorem B3660731 : Blo 2283435 3660731 := bstep (se 1 (by rfl) ⟨2745548, by rfl⟩ : syracuseStep 3660731 = 5491097) B5491097
theorem B2440487 : Blo 2283435 2440487 := bstep (se 1 (by rfl) ⟨1830365, by rfl⟩ : syracuseStep 2440487 = 3660731) B3660731
theorem B6507965 : Blo 2283435 6507965 := bstep (se 3 (by rfl) ⟨1220243, by rfl⟩ : syracuseStep 6507965 = 2440487) B2440487
theorem B17354573 : Blo 2283435 17354573 := bstep (se 3 (by rfl) ⟨3253982, by rfl⟩ : syracuseStep 17354573 = 6507965) B6507965
theorem B11569715 : Blo 2283435 11569715 := bstep (se 1 (by rfl) ⟨8677286, by rfl⟩ : syracuseStep 11569715 = 17354573) B17354573
theorem B7713143 : Blo 2283435 7713143 := bstep (se 1 (by rfl) ⟨5784857, by rfl⟩ : syracuseStep 7713143 = 11569715) B11569715
theorem B5142095 : Blo 2283435 5142095 := bstep (se 1 (by rfl) ⟨3856571, by rfl⟩ : syracuseStep 5142095 = 7713143) B7713143
theorem B3428063 : Blo 2283435 3428063 := bstep (se 1 (by rfl) ⟨2571047, by rfl⟩ : syracuseStep 3428063 = 5142095) B5142095
theorem B2285375 : Blo 2283435 2285375 := bstep (se 1 (by rfl) ⟨1714031, by rfl⟩ : syracuseStep 2285375 = 3428063) B3428063
theorem B3428069 : Blo 2283435 3428069 := bbase (se 4 (by rfl) ⟨321381, by rfl⟩ : syracuseStep 3428069 = 642763) (by norm_num)
theorem B2285379 : Blo 2283435 2285379 := bstep (se 1 (by rfl) ⟨1714034, by rfl⟩ : syracuseStep 2285379 = 3428069) B3428069
theorem B6507989 : Blo 2283435 6507989 := bbase (se 7 (by rfl) ⟨76265, by rfl⟩ : syracuseStep 6507989 = 152531) (by norm_num)
theorem B4338659 : Blo 2283435 4338659 := bstep (se 1 (by rfl) ⟨3253994, by rfl⟩ : syracuseStep 4338659 = 6507989) B6507989
theorem B2892439 : Blo 2283435 2892439 := bstep (se 1 (by rfl) ⟨2169329, by rfl⟩ : syracuseStep 2892439 = 4338659) B4338659
theorem B3856585 : Blo 2283435 3856585 := bstep (se 2 (by rfl) ⟨1446219, by rfl⟩ : syracuseStep 3856585 = 2892439) B2892439
theorem B5142113 : Blo 2283435 5142113 := bstep (se 2 (by rfl) ⟨1928292, by rfl⟩ : syracuseStep 5142113 = 3856585) B3856585
theorem B3428075 : Blo 2283435 3428075 := bstep (se 1 (by rfl) ⟨2571056, by rfl⟩ : syracuseStep 3428075 = 5142113) B5142113
theorem B2285383 : Blo 2283435 2285383 := bstep (se 1 (by rfl) ⟨1714037, by rfl⟩ : syracuseStep 2285383 = 3428075) B3428075
theorem B2571061 : Blo 2283435 2571061 := bbase (se 5 (by rfl) ⟨120518, by rfl⟩ : syracuseStep 2571061 = 241037) (by norm_num)
theorem B3428081 : Blo 2283435 3428081 := bstep (se 2 (by rfl) ⟨1285530, by rfl⟩ : syracuseStep 3428081 = 2571061) B2571061
theorem B2285387 : Blo 2283435 2285387 := bstep (se 1 (by rfl) ⟨1714040, by rfl⟩ : syracuseStep 2285387 = 3428081) B3428081
theorem B2892449 : Blo 2283435 2892449 := bbase (se 2 (by rfl) ⟨1084668, by rfl⟩ : syracuseStep 2892449 = 2169337) (by norm_num)
theorem B7713197 : Blo 2283435 7713197 := bstep (se 3 (by rfl) ⟨1446224, by rfl⟩ : syracuseStep 7713197 = 2892449) B2892449
theorem B5142131 : Blo 2283435 5142131 := bstep (se 1 (by rfl) ⟨3856598, by rfl⟩ : syracuseStep 5142131 = 7713197) B7713197
theorem B3428087 : Blo 2283435 3428087 := bstep (se 1 (by rfl) ⟨2571065, by rfl⟩ : syracuseStep 3428087 = 5142131) B5142131
theorem B2285391 : Blo 2283435 2285391 := bstep (se 1 (by rfl) ⟨1714043, by rfl⟩ : syracuseStep 2285391 = 3428087) B3428087
theorem B3428093 : Blo 2283435 3428093 := bbase (se 3 (by rfl) ⟨642767, by rfl⟩ : syracuseStep 3428093 = 1285535) (by norm_num)
theorem B2285395 : Blo 2283435 2285395 := bstep (se 1 (by rfl) ⟨1714046, by rfl⟩ : syracuseStep 2285395 = 3428093) B3428093
theorem B5142149 : Blo 2283435 5142149 := bbase (se 4 (by rfl) ⟨482076, by rfl⟩ : syracuseStep 5142149 = 964153) (by norm_num)
theorem B3428099 : Blo 2283435 3428099 := bstep (se 1 (by rfl) ⟨2571074, by rfl⟩ : syracuseStep 3428099 = 5142149) B5142149
theorem B2285399 : Blo 2283435 2285399 := bstep (se 1 (by rfl) ⟨1714049, by rfl⟩ : syracuseStep 2285399 = 3428099) B3428099
theorem B5491165 : Blo 2283435 5491165 := bbase (se 3 (by rfl) ⟨1029593, by rfl⟩ : syracuseStep 5491165 = 2059187) (by norm_num)
theorem B7321553 : Blo 2283435 7321553 := bstep (se 2 (by rfl) ⟨2745582, by rfl⟩ : syracuseStep 7321553 = 5491165) B5491165
theorem B4881035 : Blo 2283435 4881035 := bstep (se 1 (by rfl) ⟨3660776, by rfl⟩ : syracuseStep 4881035 = 7321553) B7321553
theorem B3254023 : Blo 2283435 3254023 := bstep (se 1 (by rfl) ⟨2440517, by rfl⟩ : syracuseStep 3254023 = 4881035) B4881035
theorem B4338697 : Blo 2283435 4338697 := bstep (se 2 (by rfl) ⟨1627011, by rfl⟩ : syracuseStep 4338697 = 3254023) B3254023
theorem B5784929 : Blo 2283435 5784929 := bstep (se 2 (by rfl) ⟨2169348, by rfl⟩ : syracuseStep 5784929 = 4338697) B4338697
theorem B3856619 : Blo 2283435 3856619 := bstep (se 1 (by rfl) ⟨2892464, by rfl⟩ : syracuseStep 3856619 = 5784929) B5784929
theorem B2571079 : Blo 2283435 2571079 := bstep (se 1 (by rfl) ⟨1928309, by rfl⟩ : syracuseStep 2571079 = 3856619) B3856619
theorem B3428105 : Blo 2283435 3428105 := bstep (se 2 (by rfl) ⟨1285539, by rfl⟩ : syracuseStep 3428105 = 2571079) B2571079
theorem B2285403 : Blo 2283435 2285403 := bstep (se 1 (by rfl) ⟨1714052, by rfl⟩ : syracuseStep 2285403 = 3428105) B3428105
theorem B11569877 : Blo 2283435 11569877 := bbase (se 7 (by rfl) ⟨135584, by rfl⟩ : syracuseStep 11569877 = 271169) (by norm_num)
theorem B7713251 : Blo 2283435 7713251 := bstep (se 1 (by rfl) ⟨5784938, by rfl⟩ : syracuseStep 7713251 = 11569877) B11569877
theorem B5142167 : Blo 2283435 5142167 := bstep (se 1 (by rfl) ⟨3856625, by rfl⟩ : syracuseStep 5142167 = 7713251) B7713251
theorem B3428111 : Blo 2283435 3428111 := bstep (se 1 (by rfl) ⟨2571083, by rfl⟩ : syracuseStep 3428111 = 5142167) B5142167
theorem B2285407 : Blo 2283435 2285407 := bstep (se 1 (by rfl) ⟨1714055, by rfl⟩ : syracuseStep 2285407 = 3428111) B3428111
theorem B3428117 : Blo 2283435 3428117 := bbase (se 6 (by rfl) ⟨80346, by rfl⟩ : syracuseStep 3428117 = 160693) (by norm_num)
theorem B2285411 : Blo 2283435 2285411 := bstep (se 1 (by rfl) ⟨1714058, by rfl⟩ : syracuseStep 2285411 = 3428117) B3428117
theorem B35183317 : Blo 2283435 35183317 := bbase (se 7 (by rfl) ⟨412304, by rfl⟩ : syracuseStep 35183317 = 824609) (by norm_num)
theorem B46911089 : Blo 2283435 46911089 := bstep (se 2 (by rfl) ⟨17591658, by rfl⟩ : syracuseStep 46911089 = 35183317) B35183317
theorem B31274059 : Blo 2283435 31274059 := bstep (se 1 (by rfl) ⟨23455544, by rfl⟩ : syracuseStep 31274059 = 46911089) B46911089
theorem B41698745 : Blo 2283435 41698745 := bstep (se 2 (by rfl) ⟨15637029, by rfl⟩ : syracuseStep 41698745 = 31274059) B31274059
theorem B27799163 : Blo 2283435 27799163 := bstep (se 1 (by rfl) ⟨20849372, by rfl⟩ : syracuseStep 27799163 = 41698745) B41698745
theorem B18532775 : Blo 2283435 18532775 := bstep (se 1 (by rfl) ⟨13899581, by rfl⟩ : syracuseStep 18532775 = 27799163) B27799163
theorem B12355183 : Blo 2283435 12355183 := bstep (se 1 (by rfl) ⟨9266387, by rfl⟩ : syracuseStep 12355183 = 18532775) B18532775
theorem B65894309 : Blo 2283435 65894309 := bstep (se 4 (by rfl) ⟨6177591, by rfl⟩ : syracuseStep 65894309 = 12355183) B12355183
theorem B43929539 : Blo 2283435 43929539 := bstep (se 1 (by rfl) ⟨32947154, by rfl⟩ : syracuseStep 43929539 = 65894309) B65894309
theorem B29286359 : Blo 2283435 29286359 := bstep (se 1 (by rfl) ⟨21964769, by rfl⟩ : syracuseStep 29286359 = 43929539) B43929539
theorem B19524239 : Blo 2283435 19524239 := bstep (se 1 (by rfl) ⟨14643179, by rfl⟩ : syracuseStep 19524239 = 29286359) B29286359
theorem B13016159 : Blo 2283435 13016159 := bstep (se 1 (by rfl) ⟨9762119, by rfl⟩ : syracuseStep 13016159 = 19524239) B19524239
theorem B8677439 : Blo 2283435 8677439 := bstep (se 1 (by rfl) ⟨6508079, by rfl⟩ : syracuseStep 8677439 = 13016159) B13016159
theorem B5784959 : Blo 2283435 5784959 := bstep (se 1 (by rfl) ⟨4338719, by rfl⟩ : syracuseStep 5784959 = 8677439) B8677439
theorem B3856639 : Blo 2283435 3856639 := bstep (se 1 (by rfl) ⟨2892479, by rfl⟩ : syracuseStep 3856639 = 5784959) B5784959
theorem B5142185 : Blo 2283435 5142185 := bstep (se 2 (by rfl) ⟨1928319, by rfl⟩ : syracuseStep 5142185 = 3856639) B3856639
theorem B3428123 : Blo 2283435 3428123 := bstep (se 1 (by rfl) ⟨2571092, by rfl⟩ : syracuseStep 3428123 = 5142185) B5142185
theorem B2285415 : Blo 2283435 2285415 := bstep (se 1 (by rfl) ⟨1714061, by rfl⟩ : syracuseStep 2285415 = 3428123) B3428123
theorem B2571097 : Blo 2283435 2571097 := bbase (se 2 (by rfl) ⟨964161, by rfl⟩ : syracuseStep 2571097 = 1928323) (by norm_num)
theorem B3428129 : Blo 2283435 3428129 := bstep (se 2 (by rfl) ⟨1285548, by rfl⟩ : syracuseStep 3428129 = 2571097) B2571097
theorem B2285419 : Blo 2283435 2285419 := bstep (se 1 (by rfl) ⟨1714064, by rfl⟩ : syracuseStep 2285419 = 3428129) B3428129
theorem B4881077 : Blo 2283435 4881077 := bbase (se 5 (by rfl) ⟨228800, by rfl⟩ : syracuseStep 4881077 = 457601) (by norm_num)
theorem B3254051 : Blo 2283435 3254051 := bstep (se 1 (by rfl) ⟨2440538, by rfl⟩ : syracuseStep 3254051 = 4881077) B4881077
theorem B8677469 : Blo 2283435 8677469 := bstep (se 3 (by rfl) ⟨1627025, by rfl⟩ : syracuseStep 8677469 = 3254051) B3254051
theorem B5784979 : Blo 2283435 5784979 := bstep (se 1 (by rfl) ⟨4338734, by rfl⟩ : syracuseStep 5784979 = 8677469) B8677469
theorem B7713305 : Blo 2283435 7713305 := bstep (se 2 (by rfl) ⟨2892489, by rfl⟩ : syracuseStep 7713305 = 5784979) B5784979
theorem B5142203 : Blo 2283435 5142203 := bstep (se 1 (by rfl) ⟨3856652, by rfl⟩ : syracuseStep 5142203 = 7713305) B7713305
theorem B3428135 : Blo 2283435 3428135 := bstep (se 1 (by rfl) ⟨2571101, by rfl⟩ : syracuseStep 3428135 = 5142203) B5142203
theorem B2285423 : Blo 2283435 2285423 := bstep (se 1 (by rfl) ⟨1714067, by rfl⟩ : syracuseStep 2285423 = 3428135) B3428135
theorem B3428141 : Blo 2283435 3428141 := bbase (se 3 (by rfl) ⟨642776, by rfl⟩ : syracuseStep 3428141 = 1285553) (by norm_num)
theorem B2285427 : Blo 2283435 2285427 := bstep (se 1 (by rfl) ⟨1714070, by rfl⟩ : syracuseStep 2285427 = 3428141) B3428141
theorem B5142221 : Blo 2283435 5142221 := bbase (se 3 (by rfl) ⟨964166, by rfl⟩ : syracuseStep 5142221 = 1928333) (by norm_num)
theorem B3428147 : Blo 2283435 3428147 := bstep (se 1 (by rfl) ⟨2571110, by rfl⟩ : syracuseStep 3428147 = 5142221) B5142221
theorem B2285431 : Blo 2283435 2285431 := bstep (se 1 (by rfl) ⟨1714073, by rfl⟩ : syracuseStep 2285431 = 3428147) B3428147
theorem B2892505 : Blo 2283435 2892505 := bbase (se 2 (by rfl) ⟨1084689, by rfl⟩ : syracuseStep 2892505 = 2169379) (by norm_num)
theorem B3856673 : Blo 2283435 3856673 := bstep (se 2 (by rfl) ⟨1446252, by rfl⟩ : syracuseStep 3856673 = 2892505) B2892505
theorem B2571115 : Blo 2283435 2571115 := bstep (se 1 (by rfl) ⟨1928336, by rfl⟩ : syracuseStep 2571115 = 3856673) B3856673
theorem B3428153 : Blo 2283435 3428153 := bstep (se 2 (by rfl) ⟨1285557, by rfl⟩ : syracuseStep 3428153 = 2571115) B2571115
theorem B2285435 : Blo 2283435 2285435 := bstep (se 1 (by rfl) ⟨1714076, by rfl⟩ : syracuseStep 2285435 = 3428153) B3428153
theorem C0 (j : ℕ) (h1 : 570858 ≤ j) (h2 : j ≤ 571358) : Blo 2283435 (4 * j + 3) := by
  interval_cases j
  · exact B2283435
  · exact B2283439
  · exact B2283443
  · exact B2283447
  · exact B2283451
  · exact B2283455
  · exact B2283459
  · exact B2283463
  · exact B2283467
  · exact B2283471
  · exact B2283475
  · exact B2283479
  · exact B2283483
  · exact B2283487
  · exact B2283491
  · exact B2283495
  · exact B2283499
  · exact B2283503
  · exact B2283507
  · exact B2283511
  · exact B2283515
  · exact B2283519
  · exact B2283523
  · exact B2283527
  · exact B2283531
  · exact B2283535
  · exact B2283539
  · exact B2283543
  · exact B2283547
  · exact B2283551
  · exact B2283555
  · exact B2283559
  · exact B2283563
  · exact B2283567
  · exact B2283571
  · exact B2283575
  · exact B2283579
  · exact B2283583
  · exact B2283587
  · exact B2283591
  · exact B2283595
  · exact B2283599
  · exact B2283603
  · exact B2283607
  · exact B2283611
  · exact B2283615
  · exact B2283619
  · exact B2283623
  · exact B2283627
  · exact B2283631
  · exact B2283635
  · exact B2283639
  · exact B2283643
  · exact B2283647
  · exact B2283651
  · exact B2283655
  · exact B2283659
  · exact B2283663
  · exact B2283667
  · exact B2283671
  · exact B2283675
  · exact B2283679
  · exact B2283683
  · exact B2283687
  · exact B2283691
  · exact B2283695
  · exact B2283699
  · exact B2283703
  · exact B2283707
  · exact B2283711
  · exact B2283715
  · exact B2283719
  · exact B2283723
  · exact B2283727
  · exact B2283731
  · exact B2283735
  · exact B2283739
  · exact B2283743
  · exact B2283747
  · exact B2283751
  · exact B2283755
  · exact B2283759
  · exact B2283763
  · exact B2283767
  · exact B2283771
  · exact B2283775
  · exact B2283779
  · exact B2283783
  · exact B2283787
  · exact B2283791
  · exact B2283795
  · exact B2283799
  · exact B2283803
  · exact B2283807
  · exact B2283811
  · exact B2283815
  · exact B2283819
  · exact B2283823
  · exact B2283827
  · exact B2283831
  · exact B2283835
  · exact B2283839
  · exact B2283843
  · exact B2283847
  · exact B2283851
  · exact B2283855
  · exact B2283859
  · exact B2283863
  · exact B2283867
  · exact B2283871
  · exact B2283875
  · exact B2283879
  · exact B2283883
  · exact B2283887
  · exact B2283891
  · exact B2283895
  · exact B2283899
  · exact B2283903
  · exact B2283907
  · exact B2283911
  · exact B2283915
  · exact B2283919
  · exact B2283923
  · exact B2283927
  · exact B2283931
  · exact B2283935
  · exact B2283939
  · exact B2283943
  · exact B2283947
  · exact B2283951
  · exact B2283955
  · exact B2283959
  · exact B2283963
  · exact B2283967
  · exact B2283971
  · exact B2283975
  · exact B2283979
  · exact B2283983
  · exact B2283987
  · exact B2283991
  · exact B2283995
  · exact B2283999
  · exact B2284003
  · exact B2284007
  · exact B2284011
  · exact B2284015
  · exact B2284019
  · exact B2284023
  · exact B2284027
  · exact B2284031
  · exact B2284035
  · exact B2284039
  · exact B2284043
  · exact B2284047
  · exact B2284051
  · exact B2284055
  · exact B2284059
  · exact B2284063
  · exact B2284067
  · exact B2284071
  · exact B2284075
  · exact B2284079
  · exact B2284083
  · exact B2284087
  · exact B2284091
  · exact B2284095
  · exact B2284099
  · exact B2284103
  · exact B2284107
  · exact B2284111
  · exact B2284115
  · exact B2284119
  · exact B2284123
  · exact B2284127
  · exact B2284131
  · exact B2284135
  · exact B2284139
  · exact B2284143
  · exact B2284147
  · exact B2284151
  · exact B2284155
  · exact B2284159
  · exact B2284163
  · exact B2284167
  · exact B2284171
  · exact B2284175
  · exact B2284179
  · exact B2284183
  · exact B2284187
  · exact B2284191
  · exact B2284195
  · exact B2284199
  · exact B2284203
  · exact B2284207
  · exact B2284211
  · exact B2284215
  · exact B2284219
  · exact B2284223
  · exact B2284227
  · exact B2284231
  · exact B2284235
  · exact B2284239
  · exact B2284243
  · exact B2284247
  · exact B2284251
  · exact B2284255
  · exact B2284259
  · exact B2284263
  · exact B2284267
  · exact B2284271
  · exact B2284275
  · exact B2284279
  · exact B2284283
  · exact B2284287
  · exact B2284291
  · exact B2284295
  · exact B2284299
  · exact B2284303
  · exact B2284307
  · exact B2284311
  · exact B2284315
  · exact B2284319
  · exact B2284323
  · exact B2284327
  · exact B2284331
  · exact B2284335
  · exact B2284339
  · exact B2284343
  · exact B2284347
  · exact B2284351
  · exact B2284355
  · exact B2284359
  · exact B2284363
  · exact B2284367
  · exact B2284371
  · exact B2284375
  · exact B2284379
  · exact B2284383
  · exact B2284387
  · exact B2284391
  · exact B2284395
  · exact B2284399
  · exact B2284403
  · exact B2284407
  · exact B2284411
  · exact B2284415
  · exact B2284419
  · exact B2284423
  · exact B2284427
  · exact B2284431
  · exact B2284435
  · exact B2284439
  · exact B2284443
  · exact B2284447
  · exact B2284451
  · exact B2284455
  · exact B2284459
  · exact B2284463
  · exact B2284467
  · exact B2284471
  · exact B2284475
  · exact B2284479
  · exact B2284483
  · exact B2284487
  · exact B2284491
  · exact B2284495
  · exact B2284499
  · exact B2284503
  · exact B2284507
  · exact B2284511
  · exact B2284515
  · exact B2284519
  · exact B2284523
  · exact B2284527
  · exact B2284531
  · exact B2284535
  · exact B2284539
  · exact B2284543
  · exact B2284547
  · exact B2284551
  · exact B2284555
  · exact B2284559
  · exact B2284563
  · exact B2284567
  · exact B2284571
  · exact B2284575
  · exact B2284579
  · exact B2284583
  · exact B2284587
  · exact B2284591
  · exact B2284595
  · exact B2284599
  · exact B2284603
  · exact B2284607
  · exact B2284611
  · exact B2284615
  · exact B2284619
  · exact B2284623
  · exact B2284627
  · exact B2284631
  · exact B2284635
  · exact B2284639
  · exact B2284643
  · exact B2284647
  · exact B2284651
  · exact B2284655
  · exact B2284659
  · exact B2284663
  · exact B2284667
  · exact B2284671
  · exact B2284675
  · exact B2284679
  · exact B2284683
  · exact B2284687
  · exact B2284691
  · exact B2284695
  · exact B2284699
  · exact B2284703
  · exact B2284707
  · exact B2284711
  · exact B2284715
  · exact B2284719
  · exact B2284723
  · exact B2284727
  · exact B2284731
  · exact B2284735
  · exact B2284739
  · exact B2284743
  · exact B2284747
  · exact B2284751
  · exact B2284755
  · exact B2284759
  · exact B2284763
  · exact B2284767
  · exact B2284771
  · exact B2284775
  · exact B2284779
  · exact B2284783
  · exact B2284787
  · exact B2284791
  · exact B2284795
  · exact B2284799
  · exact B2284803
  · exact B2284807
  · exact B2284811
  · exact B2284815
  · exact B2284819
  · exact B2284823
  · exact B2284827
  · exact B2284831
  · exact B2284835
  · exact B2284839
  · exact B2284843
  · exact B2284847
  · exact B2284851
  · exact B2284855
  · exact B2284859
  · exact B2284863
  · exact B2284867
  · exact B2284871
  · exact B2284875
  · exact B2284879
  · exact B2284883
  · exact B2284887
  · exact B2284891
  · exact B2284895
  · exact B2284899
  · exact B2284903
  · exact B2284907
  · exact B2284911
  · exact B2284915
  · exact B2284919
  · exact B2284923
  · exact B2284927
  · exact B2284931
  · exact B2284935
  · exact B2284939
  · exact B2284943
  · exact B2284947
  · exact B2284951
  · exact B2284955
  · exact B2284959
  · exact B2284963
  · exact B2284967
  · exact B2284971
  · exact B2284975
  · exact B2284979
  · exact B2284983
  · exact B2284987
  · exact B2284991
  · exact B2284995
  · exact B2284999
  · exact B2285003
  · exact B2285007
  · exact B2285011
  · exact B2285015
  · exact B2285019
  · exact B2285023
  · exact B2285027
  · exact B2285031
  · exact B2285035
  · exact B2285039
  · exact B2285043
  · exact B2285047
  · exact B2285051
  · exact B2285055
  · exact B2285059
  · exact B2285063
  · exact B2285067
  · exact B2285071
  · exact B2285075
  · exact B2285079
  · exact B2285083
  · exact B2285087
  · exact B2285091
  · exact B2285095
  · exact B2285099
  · exact B2285103
  · exact B2285107
  · exact B2285111
  · exact B2285115
  · exact B2285119
  · exact B2285123
  · exact B2285127
  · exact B2285131
  · exact B2285135
  · exact B2285139
  · exact B2285143
  · exact B2285147
  · exact B2285151
  · exact B2285155
  · exact B2285159
  · exact B2285163
  · exact B2285167
  · exact B2285171
  · exact B2285175
  · exact B2285179
  · exact B2285183
  · exact B2285187
  · exact B2285191
  · exact B2285195
  · exact B2285199
  · exact B2285203
  · exact B2285207
  · exact B2285211
  · exact B2285215
  · exact B2285219
  · exact B2285223
  · exact B2285227
  · exact B2285231
  · exact B2285235
  · exact B2285239
  · exact B2285243
  · exact B2285247
  · exact B2285251
  · exact B2285255
  · exact B2285259
  · exact B2285263
  · exact B2285267
  · exact B2285271
  · exact B2285275
  · exact B2285279
  · exact B2285283
  · exact B2285287
  · exact B2285291
  · exact B2285295
  · exact B2285299
  · exact B2285303
  · exact B2285307
  · exact B2285311
  · exact B2285315
  · exact B2285319
  · exact B2285323
  · exact B2285327
  · exact B2285331
  · exact B2285335
  · exact B2285339
  · exact B2285343
  · exact B2285347
  · exact B2285351
  · exact B2285355
  · exact B2285359
  · exact B2285363
  · exact B2285367
  · exact B2285371
  · exact B2285375
  · exact B2285379
  · exact B2285383
  · exact B2285387
  · exact B2285391
  · exact B2285395
  · exact B2285399
  · exact B2285403
  · exact B2285407
  · exact B2285411
  · exact B2285415
  · exact B2285419
  · exact B2285423
  · exact B2285427
  · exact B2285431
  · exact B2285435
theorem solution (m : ℕ) (hlo : 2283435 ≤ m) (hhi : m ≤ 2285435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 570858 ≤ j := by omega
    have hj2 : j ≤ 571358 := by omega
    have hb : Blo 2283435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
