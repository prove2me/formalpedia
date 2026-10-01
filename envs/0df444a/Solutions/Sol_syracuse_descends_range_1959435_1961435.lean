-- Prove2me | solution 1 for syracuse_descends_range_1959435_1961435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:47:49.918737+00:00
-- url     : https://prove2.me/submissions/2a6212f4-7b4a-46e2-877d-2408b979b5d8

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

theorem B2204365 : Blo 1959435 2204365 := bbase (se 3 (by rfl) ⟨413318, by rfl⟩ : syracuseStep 2204365 = 826637) (by norm_num)
theorem B2939153 : Blo 1959435 2939153 := bstep (se 2 (by rfl) ⟨1102182, by rfl⟩ : syracuseStep 2939153 = 2204365) B2204365
theorem B1959435 : Blo 1959435 1959435 := bstep (se 1 (by rfl) ⟨1469576, by rfl⟩ : syracuseStep 1959435 = 2939153) B2939153
theorem B6613109 : Blo 1959435 6613109 := bbase (se 5 (by rfl) ⟨309989, by rfl⟩ : syracuseStep 6613109 = 619979) (by norm_num)
theorem B4408739 : Blo 1959435 4408739 := bstep (se 1 (by rfl) ⟨3306554, by rfl⟩ : syracuseStep 4408739 = 6613109) B6613109
theorem B2939159 : Blo 1959435 2939159 := bstep (se 1 (by rfl) ⟨2204369, by rfl⟩ : syracuseStep 2939159 = 4408739) B4408739
theorem B1959439 : Blo 1959435 1959439 := bstep (se 1 (by rfl) ⟨1469579, by rfl⟩ : syracuseStep 1959439 = 2939159) B2939159
theorem B2939165 : Blo 1959435 2939165 := bbase (se 3 (by rfl) ⟨551093, by rfl⟩ : syracuseStep 2939165 = 1102187) (by norm_num)
theorem B1959443 : Blo 1959435 1959443 := bstep (se 1 (by rfl) ⟨1469582, by rfl⟩ : syracuseStep 1959443 = 2939165) B2939165
theorem B4408757 : Blo 1959435 4408757 := bbase (se 5 (by rfl) ⟨206660, by rfl⟩ : syracuseStep 4408757 = 413321) (by norm_num)
theorem B2939171 : Blo 1959435 2939171 := bstep (se 1 (by rfl) ⟨2204378, by rfl⟩ : syracuseStep 2939171 = 4408757) B4408757
theorem B1959447 : Blo 1959435 1959447 := bstep (se 1 (by rfl) ⟨1469585, by rfl⟩ : syracuseStep 1959447 = 2939171) B2939171
theorem B4184885 : Blo 1959435 4184885 := bbase (se 5 (by rfl) ⟨196166, by rfl⟩ : syracuseStep 4184885 = 392333) (by norm_num)
theorem B11159693 : Blo 1959435 11159693 := bstep (se 3 (by rfl) ⟨2092442, by rfl⟩ : syracuseStep 11159693 = 4184885) B4184885
theorem B7439795 : Blo 1959435 7439795 := bstep (se 1 (by rfl) ⟨5579846, by rfl⟩ : syracuseStep 7439795 = 11159693) B11159693
theorem B4959863 : Blo 1959435 4959863 := bstep (se 1 (by rfl) ⟨3719897, by rfl⟩ : syracuseStep 4959863 = 7439795) B7439795
theorem B3306575 : Blo 1959435 3306575 := bstep (se 1 (by rfl) ⟨2479931, by rfl⟩ : syracuseStep 3306575 = 4959863) B4959863
theorem B2204383 : Blo 1959435 2204383 := bstep (se 1 (by rfl) ⟨1653287, by rfl⟩ : syracuseStep 2204383 = 3306575) B3306575
theorem B2939177 : Blo 1959435 2939177 := bstep (se 2 (by rfl) ⟨1102191, by rfl⟩ : syracuseStep 2939177 = 2204383) B2204383
theorem B1959451 : Blo 1959435 1959451 := bstep (se 1 (by rfl) ⟨1469588, by rfl⟩ : syracuseStep 1959451 = 2939177) B2939177
theorem B4184893 : Blo 1959435 4184893 := bbase (se 3 (by rfl) ⟨784667, by rfl⟩ : syracuseStep 4184893 = 1569335) (by norm_num)
theorem B5579857 : Blo 1959435 5579857 := bstep (se 2 (by rfl) ⟨2092446, by rfl⟩ : syracuseStep 5579857 = 4184893) B4184893
theorem B7439809 : Blo 1959435 7439809 := bstep (se 2 (by rfl) ⟨2789928, by rfl⟩ : syracuseStep 7439809 = 5579857) B5579857
theorem B9919745 : Blo 1959435 9919745 := bstep (se 2 (by rfl) ⟨3719904, by rfl⟩ : syracuseStep 9919745 = 7439809) B7439809
theorem B6613163 : Blo 1959435 6613163 := bstep (se 1 (by rfl) ⟨4959872, by rfl⟩ : syracuseStep 6613163 = 9919745) B9919745
theorem B4408775 : Blo 1959435 4408775 := bstep (se 1 (by rfl) ⟨3306581, by rfl⟩ : syracuseStep 4408775 = 6613163) B6613163
theorem B2939183 : Blo 1959435 2939183 := bstep (se 1 (by rfl) ⟨2204387, by rfl⟩ : syracuseStep 2939183 = 4408775) B4408775
theorem B1959455 : Blo 1959435 1959455 := bstep (se 1 (by rfl) ⟨1469591, by rfl⟩ : syracuseStep 1959455 = 2939183) B2939183
theorem B2939189 : Blo 1959435 2939189 := bbase (se 5 (by rfl) ⟨137774, by rfl⟩ : syracuseStep 2939189 = 275549) (by norm_num)
theorem B1959459 : Blo 1959435 1959459 := bstep (se 1 (by rfl) ⟨1469594, by rfl⟩ : syracuseStep 1959459 = 2939189) B2939189
theorem B4959893 : Blo 1959435 4959893 := bbase (se 6 (by rfl) ⟨116247, by rfl⟩ : syracuseStep 4959893 = 232495) (by norm_num)
theorem B3306595 : Blo 1959435 3306595 := bstep (se 1 (by rfl) ⟨2479946, by rfl⟩ : syracuseStep 3306595 = 4959893) B4959893
theorem B4408793 : Blo 1959435 4408793 := bstep (se 2 (by rfl) ⟨1653297, by rfl⟩ : syracuseStep 4408793 = 3306595) B3306595
theorem B2939195 : Blo 1959435 2939195 := bstep (se 1 (by rfl) ⟨2204396, by rfl⟩ : syracuseStep 2939195 = 4408793) B4408793
theorem B1959463 : Blo 1959435 1959463 := bstep (se 1 (by rfl) ⟨1469597, by rfl⟩ : syracuseStep 1959463 = 2939195) B2939195
theorem B2204401 : Blo 1959435 2204401 := bbase (se 2 (by rfl) ⟨826650, by rfl⟩ : syracuseStep 2204401 = 1653301) (by norm_num)
theorem B2939201 : Blo 1959435 2939201 := bstep (se 2 (by rfl) ⟨1102200, by rfl⟩ : syracuseStep 2939201 = 2204401) B2204401
theorem B1959467 : Blo 1959435 1959467 := bstep (se 1 (by rfl) ⟨1469600, by rfl⟩ : syracuseStep 1959467 = 2939201) B2939201
theorem B2264969 : Blo 1959435 2264969 := bbase (se 2 (by rfl) ⟨849363, by rfl⟩ : syracuseStep 2264969 = 1698727) (by norm_num)
theorem B6039917 : Blo 1959435 6039917 := bstep (se 3 (by rfl) ⟨1132484, by rfl⟩ : syracuseStep 6039917 = 2264969) B2264969
theorem B4026611 : Blo 1959435 4026611 := bstep (se 1 (by rfl) ⟨3019958, by rfl⟩ : syracuseStep 4026611 = 6039917) B6039917
theorem B2684407 : Blo 1959435 2684407 := bstep (se 1 (by rfl) ⟨2013305, by rfl⟩ : syracuseStep 2684407 = 4026611) B4026611
theorem B3579209 : Blo 1959435 3579209 := bstep (se 2 (by rfl) ⟨1342203, by rfl⟩ : syracuseStep 3579209 = 2684407) B2684407
theorem B2386139 : Blo 1959435 2386139 := bstep (se 1 (by rfl) ⟨1789604, by rfl⟩ : syracuseStep 2386139 = 3579209) B3579209
theorem B6363037 : Blo 1959435 6363037 := bstep (se 3 (by rfl) ⟨1193069, by rfl⟩ : syracuseStep 6363037 = 2386139) B2386139
theorem B8484049 : Blo 1959435 8484049 := bstep (se 2 (by rfl) ⟨3181518, by rfl⟩ : syracuseStep 8484049 = 6363037) B6363037
theorem B11312065 : Blo 1959435 11312065 := bstep (se 2 (by rfl) ⟨4242024, by rfl⟩ : syracuseStep 11312065 = 8484049) B8484049
theorem B15082753 : Blo 1959435 15082753 := bstep (se 2 (by rfl) ⟨5656032, by rfl⟩ : syracuseStep 15082753 = 11312065) B11312065
theorem B20110337 : Blo 1959435 20110337 := bstep (se 2 (by rfl) ⟨7541376, by rfl⟩ : syracuseStep 20110337 = 15082753) B15082753
theorem B13406891 : Blo 1959435 13406891 := bstep (se 1 (by rfl) ⟨10055168, by rfl⟩ : syracuseStep 13406891 = 20110337) B20110337
theorem B35751709 : Blo 1959435 35751709 := bstep (se 3 (by rfl) ⟨6703445, by rfl⟩ : syracuseStep 35751709 = 13406891) B13406891
theorem B47668945 : Blo 1959435 47668945 := bstep (se 2 (by rfl) ⟨17875854, by rfl⟩ : syracuseStep 47668945 = 35751709) B35751709
theorem B63558593 : Blo 1959435 63558593 := bstep (se 2 (by rfl) ⟨23834472, by rfl⟩ : syracuseStep 63558593 = 47668945) B47668945
theorem B42372395 : Blo 1959435 42372395 := bstep (se 1 (by rfl) ⟨31779296, by rfl⟩ : syracuseStep 42372395 = 63558593) B63558593
theorem B28248263 : Blo 1959435 28248263 := bstep (se 1 (by rfl) ⟨21186197, by rfl⟩ : syracuseStep 28248263 = 42372395) B42372395
theorem B18832175 : Blo 1959435 18832175 := bstep (se 1 (by rfl) ⟨14124131, by rfl⟩ : syracuseStep 18832175 = 28248263) B28248263
theorem B12554783 : Blo 1959435 12554783 := bstep (se 1 (by rfl) ⟨9416087, by rfl⟩ : syracuseStep 12554783 = 18832175) B18832175
theorem B8369855 : Blo 1959435 8369855 := bstep (se 1 (by rfl) ⟨6277391, by rfl⟩ : syracuseStep 8369855 = 12554783) B12554783
theorem B5579903 : Blo 1959435 5579903 := bstep (se 1 (by rfl) ⟨4184927, by rfl⟩ : syracuseStep 5579903 = 8369855) B8369855
theorem B3719935 : Blo 1959435 3719935 := bstep (se 1 (by rfl) ⟨2789951, by rfl⟩ : syracuseStep 3719935 = 5579903) B5579903
theorem B4959913 : Blo 1959435 4959913 := bstep (se 2 (by rfl) ⟨1859967, by rfl⟩ : syracuseStep 4959913 = 3719935) B3719935
theorem B6613217 : Blo 1959435 6613217 := bstep (se 2 (by rfl) ⟨2479956, by rfl⟩ : syracuseStep 6613217 = 4959913) B4959913
theorem B4408811 : Blo 1959435 4408811 := bstep (se 1 (by rfl) ⟨3306608, by rfl⟩ : syracuseStep 4408811 = 6613217) B6613217
theorem B2939207 : Blo 1959435 2939207 := bstep (se 1 (by rfl) ⟨2204405, by rfl⟩ : syracuseStep 2939207 = 4408811) B4408811
theorem B1959471 : Blo 1959435 1959471 := bstep (se 1 (by rfl) ⟨1469603, by rfl⟩ : syracuseStep 1959471 = 2939207) B2939207
theorem B2939213 : Blo 1959435 2939213 := bbase (se 3 (by rfl) ⟨551102, by rfl⟩ : syracuseStep 2939213 = 1102205) (by norm_num)
theorem B1959475 : Blo 1959435 1959475 := bstep (se 1 (by rfl) ⟨1469606, by rfl⟩ : syracuseStep 1959475 = 2939213) B2939213
theorem B4408829 : Blo 1959435 4408829 := bbase (se 3 (by rfl) ⟨826655, by rfl⟩ : syracuseStep 4408829 = 1653311) (by norm_num)
theorem B2939219 : Blo 1959435 2939219 := bstep (se 1 (by rfl) ⟨2204414, by rfl⟩ : syracuseStep 2939219 = 4408829) B4408829
theorem B1959479 : Blo 1959435 1959479 := bstep (se 1 (by rfl) ⟨1469609, by rfl⟩ : syracuseStep 1959479 = 2939219) B2939219
theorem B3306629 : Blo 1959435 3306629 := bbase (se 4 (by rfl) ⟨309996, by rfl⟩ : syracuseStep 3306629 = 619993) (by norm_num)
theorem B2204419 : Blo 1959435 2204419 := bstep (se 1 (by rfl) ⟨1653314, by rfl⟩ : syracuseStep 2204419 = 3306629) B3306629
theorem B2939225 : Blo 1959435 2939225 := bstep (se 2 (by rfl) ⟨1102209, by rfl⟩ : syracuseStep 2939225 = 2204419) B2204419
theorem B1959483 : Blo 1959435 1959483 := bstep (se 1 (by rfl) ⟨1469612, by rfl⟩ : syracuseStep 1959483 = 2939225) B2939225
theorem B14879861 : Blo 1959435 14879861 := bbase (se 5 (by rfl) ⟨697493, by rfl⟩ : syracuseStep 14879861 = 1394987) (by norm_num)
theorem B9919907 : Blo 1959435 9919907 := bstep (se 1 (by rfl) ⟨7439930, by rfl⟩ : syracuseStep 9919907 = 14879861) B14879861
theorem B6613271 : Blo 1959435 6613271 := bstep (se 1 (by rfl) ⟨4959953, by rfl⟩ : syracuseStep 6613271 = 9919907) B9919907
theorem B4408847 : Blo 1959435 4408847 := bstep (se 1 (by rfl) ⟨3306635, by rfl⟩ : syracuseStep 4408847 = 6613271) B6613271
theorem B2939231 : Blo 1959435 2939231 := bstep (se 1 (by rfl) ⟨2204423, by rfl⟩ : syracuseStep 2939231 = 4408847) B4408847
theorem B1959487 : Blo 1959435 1959487 := bstep (se 1 (by rfl) ⟨1469615, by rfl⟩ : syracuseStep 1959487 = 2939231) B2939231
theorem B2939237 : Blo 1959435 2939237 := bbase (se 4 (by rfl) ⟨275553, by rfl⟩ : syracuseStep 2939237 = 551107) (by norm_num)
theorem B1959491 : Blo 1959435 1959491 := bstep (se 1 (by rfl) ⟨1469618, by rfl⟩ : syracuseStep 1959491 = 2939237) B2939237
theorem B3719981 : Blo 1959435 3719981 := bbase (se 3 (by rfl) ⟨697496, by rfl⟩ : syracuseStep 3719981 = 1394993) (by norm_num)
theorem B2479987 : Blo 1959435 2479987 := bstep (se 1 (by rfl) ⟨1859990, by rfl⟩ : syracuseStep 2479987 = 3719981) B3719981
theorem B3306649 : Blo 1959435 3306649 := bstep (se 2 (by rfl) ⟨1239993, by rfl⟩ : syracuseStep 3306649 = 2479987) B2479987
theorem B4408865 : Blo 1959435 4408865 := bstep (se 2 (by rfl) ⟨1653324, by rfl⟩ : syracuseStep 4408865 = 3306649) B3306649
theorem B2939243 : Blo 1959435 2939243 := bstep (se 1 (by rfl) ⟨2204432, by rfl⟩ : syracuseStep 2939243 = 4408865) B4408865
theorem B1959495 : Blo 1959435 1959495 := bstep (se 1 (by rfl) ⟨1469621, by rfl⟩ : syracuseStep 1959495 = 2939243) B2939243
theorem B2204437 : Blo 1959435 2204437 := bbase (se 6 (by rfl) ⟨51666, by rfl⟩ : syracuseStep 2204437 = 103333) (by norm_num)
theorem B2939249 : Blo 1959435 2939249 := bstep (se 2 (by rfl) ⟨1102218, by rfl⟩ : syracuseStep 2939249 = 2204437) B2204437
theorem B1959499 : Blo 1959435 1959499 := bstep (se 1 (by rfl) ⟨1469624, by rfl⟩ : syracuseStep 1959499 = 2939249) B2939249
theorem B2479997 : Blo 1959435 2479997 := bbase (se 3 (by rfl) ⟨464999, by rfl⟩ : syracuseStep 2479997 = 929999) (by norm_num)
theorem B6613325 : Blo 1959435 6613325 := bstep (se 3 (by rfl) ⟨1239998, by rfl⟩ : syracuseStep 6613325 = 2479997) B2479997
theorem B4408883 : Blo 1959435 4408883 := bstep (se 1 (by rfl) ⟨3306662, by rfl⟩ : syracuseStep 4408883 = 6613325) B6613325
theorem B2939255 : Blo 1959435 2939255 := bstep (se 1 (by rfl) ⟨2204441, by rfl⟩ : syracuseStep 2939255 = 4408883) B4408883
theorem B1959503 : Blo 1959435 1959503 := bstep (se 1 (by rfl) ⟨1469627, by rfl⟩ : syracuseStep 1959503 = 2939255) B2939255
theorem B2939261 : Blo 1959435 2939261 := bbase (se 3 (by rfl) ⟨551111, by rfl⟩ : syracuseStep 2939261 = 1102223) (by norm_num)
theorem B1959507 : Blo 1959435 1959507 := bstep (se 1 (by rfl) ⟨1469630, by rfl⟩ : syracuseStep 1959507 = 2939261) B2939261
theorem B4408901 : Blo 1959435 4408901 := bbase (se 4 (by rfl) ⟨413334, by rfl⟩ : syracuseStep 4408901 = 826669) (by norm_num)
theorem B2939267 : Blo 1959435 2939267 := bstep (se 1 (by rfl) ⟨2204450, by rfl⟩ : syracuseStep 2939267 = 4408901) B4408901
theorem B1959511 : Blo 1959435 1959511 := bstep (se 1 (by rfl) ⟨1469633, by rfl⟩ : syracuseStep 1959511 = 2939267) B2939267
theorem B8938133 : Blo 1959435 8938133 := bbase (se 6 (by rfl) ⟨209487, by rfl⟩ : syracuseStep 8938133 = 418975) (by norm_num)
theorem B5958755 : Blo 1959435 5958755 := bstep (se 1 (by rfl) ⟨4469066, by rfl⟩ : syracuseStep 5958755 = 8938133) B8938133
theorem B3972503 : Blo 1959435 3972503 := bstep (se 1 (by rfl) ⟨2979377, by rfl⟩ : syracuseStep 3972503 = 5958755) B5958755
theorem B10593341 : Blo 1959435 10593341 := bstep (se 3 (by rfl) ⟨1986251, by rfl⟩ : syracuseStep 10593341 = 3972503) B3972503
theorem B7062227 : Blo 1959435 7062227 := bstep (se 1 (by rfl) ⟨5296670, by rfl⟩ : syracuseStep 7062227 = 10593341) B10593341
theorem B4708151 : Blo 1959435 4708151 := bstep (se 1 (by rfl) ⟨3531113, by rfl⟩ : syracuseStep 4708151 = 7062227) B7062227
theorem B3138767 : Blo 1959435 3138767 := bstep (se 1 (by rfl) ⟨2354075, by rfl⟩ : syracuseStep 3138767 = 4708151) B4708151
theorem B2092511 : Blo 1959435 2092511 := bstep (se 1 (by rfl) ⟨1569383, by rfl⟩ : syracuseStep 2092511 = 3138767) B3138767
theorem B5580029 : Blo 1959435 5580029 := bstep (se 3 (by rfl) ⟨1046255, by rfl⟩ : syracuseStep 5580029 = 2092511) B2092511
theorem B3720019 : Blo 1959435 3720019 := bstep (se 1 (by rfl) ⟨2790014, by rfl⟩ : syracuseStep 3720019 = 5580029) B5580029
theorem B4960025 : Blo 1959435 4960025 := bstep (se 2 (by rfl) ⟨1860009, by rfl⟩ : syracuseStep 4960025 = 3720019) B3720019
theorem B3306683 : Blo 1959435 3306683 := bstep (se 1 (by rfl) ⟨2480012, by rfl⟩ : syracuseStep 3306683 = 4960025) B4960025
theorem B2204455 : Blo 1959435 2204455 := bstep (se 1 (by rfl) ⟨1653341, by rfl⟩ : syracuseStep 2204455 = 3306683) B3306683
theorem B2939273 : Blo 1959435 2939273 := bstep (se 2 (by rfl) ⟨1102227, by rfl⟩ : syracuseStep 2939273 = 2204455) B2204455
theorem B1959515 : Blo 1959435 1959515 := bstep (se 1 (by rfl) ⟨1469636, by rfl⟩ : syracuseStep 1959515 = 2939273) B2939273
theorem B9920069 : Blo 1959435 9920069 := bbase (se 4 (by rfl) ⟨930006, by rfl⟩ : syracuseStep 9920069 = 1860013) (by norm_num)
theorem B6613379 : Blo 1959435 6613379 := bstep (se 1 (by rfl) ⟨4960034, by rfl⟩ : syracuseStep 6613379 = 9920069) B9920069
theorem B4408919 : Blo 1959435 4408919 := bstep (se 1 (by rfl) ⟨3306689, by rfl⟩ : syracuseStep 4408919 = 6613379) B6613379
theorem B2939279 : Blo 1959435 2939279 := bstep (se 1 (by rfl) ⟨2204459, by rfl⟩ : syracuseStep 2939279 = 4408919) B4408919
theorem B1959519 : Blo 1959435 1959519 := bstep (se 1 (by rfl) ⟨1469639, by rfl⟩ : syracuseStep 1959519 = 2939279) B2939279
theorem B2939285 : Blo 1959435 2939285 := bbase (se 6 (by rfl) ⟨68889, by rfl⟩ : syracuseStep 2939285 = 137779) (by norm_num)
theorem B1959523 : Blo 1959435 1959523 := bstep (se 1 (by rfl) ⟨1469642, by rfl⟩ : syracuseStep 1959523 = 2939285) B2939285
theorem B9416357 : Blo 1959435 9416357 := bbase (se 4 (by rfl) ⟨882783, by rfl⟩ : syracuseStep 9416357 = 1765567) (by norm_num)
theorem B6277571 : Blo 1959435 6277571 := bstep (se 1 (by rfl) ⟨4708178, by rfl⟩ : syracuseStep 6277571 = 9416357) B9416357
theorem B4185047 : Blo 1959435 4185047 := bstep (se 1 (by rfl) ⟨3138785, by rfl⟩ : syracuseStep 4185047 = 6277571) B6277571
theorem B11160125 : Blo 1959435 11160125 := bstep (se 3 (by rfl) ⟨2092523, by rfl⟩ : syracuseStep 11160125 = 4185047) B4185047
theorem B7440083 : Blo 1959435 7440083 := bstep (se 1 (by rfl) ⟨5580062, by rfl⟩ : syracuseStep 7440083 = 11160125) B11160125
theorem B4960055 : Blo 1959435 4960055 := bstep (se 1 (by rfl) ⟨3720041, by rfl⟩ : syracuseStep 4960055 = 7440083) B7440083
theorem B3306703 : Blo 1959435 3306703 := bstep (se 1 (by rfl) ⟨2480027, by rfl⟩ : syracuseStep 3306703 = 4960055) B4960055
theorem B4408937 : Blo 1959435 4408937 := bstep (se 2 (by rfl) ⟨1653351, by rfl⟩ : syracuseStep 4408937 = 3306703) B3306703
theorem B2939291 : Blo 1959435 2939291 := bstep (se 1 (by rfl) ⟨2204468, by rfl⟩ : syracuseStep 2939291 = 4408937) B4408937
theorem B1959527 : Blo 1959435 1959527 := bstep (se 1 (by rfl) ⟨1469645, by rfl⟩ : syracuseStep 1959527 = 2939291) B2939291
theorem B2204473 : Blo 1959435 2204473 := bbase (se 2 (by rfl) ⟨826677, by rfl⟩ : syracuseStep 2204473 = 1653355) (by norm_num)
theorem B2939297 : Blo 1959435 2939297 := bstep (se 2 (by rfl) ⟨1102236, by rfl⟩ : syracuseStep 2939297 = 2204473) B2204473
theorem B1959531 : Blo 1959435 1959531 := bstep (se 1 (by rfl) ⟨1469648, by rfl⟩ : syracuseStep 1959531 = 2939297) B2939297
theorem B5580085 : Blo 1959435 5580085 := bbase (se 5 (by rfl) ⟨261566, by rfl⟩ : syracuseStep 5580085 = 523133) (by norm_num)
theorem B7440113 : Blo 1959435 7440113 := bstep (se 2 (by rfl) ⟨2790042, by rfl⟩ : syracuseStep 7440113 = 5580085) B5580085
theorem B4960075 : Blo 1959435 4960075 := bstep (se 1 (by rfl) ⟨3720056, by rfl⟩ : syracuseStep 4960075 = 7440113) B7440113
theorem B6613433 : Blo 1959435 6613433 := bstep (se 2 (by rfl) ⟨2480037, by rfl⟩ : syracuseStep 6613433 = 4960075) B4960075
theorem B4408955 : Blo 1959435 4408955 := bstep (se 1 (by rfl) ⟨3306716, by rfl⟩ : syracuseStep 4408955 = 6613433) B6613433
theorem B2939303 : Blo 1959435 2939303 := bstep (se 1 (by rfl) ⟨2204477, by rfl⟩ : syracuseStep 2939303 = 4408955) B4408955
theorem B1959535 : Blo 1959435 1959535 := bstep (se 1 (by rfl) ⟨1469651, by rfl⟩ : syracuseStep 1959535 = 2939303) B2939303
theorem B2939309 : Blo 1959435 2939309 := bbase (se 3 (by rfl) ⟨551120, by rfl⟩ : syracuseStep 2939309 = 1102241) (by norm_num)
theorem B1959539 : Blo 1959435 1959539 := bstep (se 1 (by rfl) ⟨1469654, by rfl⟩ : syracuseStep 1959539 = 2939309) B2939309
theorem B4408973 : Blo 1959435 4408973 := bbase (se 3 (by rfl) ⟨826682, by rfl⟩ : syracuseStep 4408973 = 1653365) (by norm_num)
theorem B2939315 : Blo 1959435 2939315 := bstep (se 1 (by rfl) ⟨2204486, by rfl⟩ : syracuseStep 2939315 = 4408973) B4408973
theorem B1959543 : Blo 1959435 1959543 := bstep (se 1 (by rfl) ⟨1469657, by rfl⟩ : syracuseStep 1959543 = 2939315) B2939315
theorem B2480053 : Blo 1959435 2480053 := bbase (se 5 (by rfl) ⟨116252, by rfl⟩ : syracuseStep 2480053 = 232505) (by norm_num)
theorem B3306737 : Blo 1959435 3306737 := bstep (se 2 (by rfl) ⟨1240026, by rfl⟩ : syracuseStep 3306737 = 2480053) B2480053
theorem B2204491 : Blo 1959435 2204491 := bstep (se 1 (by rfl) ⟨1653368, by rfl⟩ : syracuseStep 2204491 = 3306737) B3306737
theorem B2939321 : Blo 1959435 2939321 := bstep (se 2 (by rfl) ⟨1102245, by rfl⟩ : syracuseStep 2939321 = 2204491) B2204491
theorem B1959547 : Blo 1959435 1959547 := bstep (se 1 (by rfl) ⟨1469660, by rfl⟩ : syracuseStep 1959547 = 2939321) B2939321
theorem B5027789 : Blo 1959435 5027789 := bbase (se 3 (by rfl) ⟨942710, by rfl⟩ : syracuseStep 5027789 = 1885421) (by norm_num)
theorem B13407437 : Blo 1959435 13407437 := bstep (se 3 (by rfl) ⟨2513894, by rfl⟩ : syracuseStep 13407437 = 5027789) B5027789
theorem B8938291 : Blo 1959435 8938291 := bstep (se 1 (by rfl) ⟨6703718, by rfl⟩ : syracuseStep 8938291 = 13407437) B13407437
theorem B11917721 : Blo 1959435 11917721 := bstep (se 2 (by rfl) ⟨4469145, by rfl⟩ : syracuseStep 11917721 = 8938291) B8938291
theorem B7945147 : Blo 1959435 7945147 := bstep (se 1 (by rfl) ⟨5958860, by rfl⟩ : syracuseStep 7945147 = 11917721) B11917721
theorem B42374117 : Blo 1959435 42374117 := bstep (se 4 (by rfl) ⟨3972573, by rfl⟩ : syracuseStep 42374117 = 7945147) B7945147
theorem B28249411 : Blo 1959435 28249411 := bstep (se 1 (by rfl) ⟨21187058, by rfl⟩ : syracuseStep 28249411 = 42374117) B42374117
theorem B37665881 : Blo 1959435 37665881 := bstep (se 2 (by rfl) ⟨14124705, by rfl⟩ : syracuseStep 37665881 = 28249411) B28249411
theorem B25110587 : Blo 1959435 25110587 := bstep (se 1 (by rfl) ⟨18832940, by rfl⟩ : syracuseStep 25110587 = 37665881) B37665881
theorem B16740391 : Blo 1959435 16740391 := bstep (se 1 (by rfl) ⟨12555293, by rfl⟩ : syracuseStep 16740391 = 25110587) B25110587
theorem B22320521 : Blo 1959435 22320521 := bstep (se 2 (by rfl) ⟨8370195, by rfl⟩ : syracuseStep 22320521 = 16740391) B16740391
theorem B14880347 : Blo 1959435 14880347 := bstep (se 1 (by rfl) ⟨11160260, by rfl⟩ : syracuseStep 14880347 = 22320521) B22320521
theorem B9920231 : Blo 1959435 9920231 := bstep (se 1 (by rfl) ⟨7440173, by rfl⟩ : syracuseStep 9920231 = 14880347) B14880347
theorem B6613487 : Blo 1959435 6613487 := bstep (se 1 (by rfl) ⟨4960115, by rfl⟩ : syracuseStep 6613487 = 9920231) B9920231
theorem B4408991 : Blo 1959435 4408991 := bstep (se 1 (by rfl) ⟨3306743, by rfl⟩ : syracuseStep 4408991 = 6613487) B6613487
theorem B2939327 : Blo 1959435 2939327 := bstep (se 1 (by rfl) ⟨2204495, by rfl⟩ : syracuseStep 2939327 = 4408991) B4408991
theorem B1959551 : Blo 1959435 1959551 := bstep (se 1 (by rfl) ⟨1469663, by rfl⟩ : syracuseStep 1959551 = 2939327) B2939327
theorem B2939333 : Blo 1959435 2939333 := bbase (se 4 (by rfl) ⟨275562, by rfl⟩ : syracuseStep 2939333 = 551125) (by norm_num)
theorem B1959555 : Blo 1959435 1959555 := bstep (se 1 (by rfl) ⟨1469666, by rfl⟩ : syracuseStep 1959555 = 2939333) B2939333
theorem B3306757 : Blo 1959435 3306757 := bbase (se 4 (by rfl) ⟨310008, by rfl⟩ : syracuseStep 3306757 = 620017) (by norm_num)
theorem B4409009 : Blo 1959435 4409009 := bstep (se 2 (by rfl) ⟨1653378, by rfl⟩ : syracuseStep 4409009 = 3306757) B3306757
theorem B2939339 : Blo 1959435 2939339 := bstep (se 1 (by rfl) ⟨2204504, by rfl⟩ : syracuseStep 2939339 = 4409009) B4409009
theorem B1959559 : Blo 1959435 1959559 := bstep (se 1 (by rfl) ⟨1469669, by rfl⟩ : syracuseStep 1959559 = 2939339) B2939339
theorem B2204509 : Blo 1959435 2204509 := bbase (se 3 (by rfl) ⟨413345, by rfl⟩ : syracuseStep 2204509 = 826691) (by norm_num)
theorem B2939345 : Blo 1959435 2939345 := bstep (se 2 (by rfl) ⟨1102254, by rfl⟩ : syracuseStep 2939345 = 2204509) B2204509
theorem B1959563 : Blo 1959435 1959563 := bstep (se 1 (by rfl) ⟨1469672, by rfl⟩ : syracuseStep 1959563 = 2939345) B2939345
theorem B6613541 : Blo 1959435 6613541 := bbase (se 4 (by rfl) ⟨620019, by rfl⟩ : syracuseStep 6613541 = 1240039) (by norm_num)
theorem B4409027 : Blo 1959435 4409027 := bstep (se 1 (by rfl) ⟨3306770, by rfl⟩ : syracuseStep 4409027 = 6613541) B6613541
theorem B2939351 : Blo 1959435 2939351 := bstep (se 1 (by rfl) ⟨2204513, by rfl⟩ : syracuseStep 2939351 = 4409027) B4409027
theorem B1959567 : Blo 1959435 1959567 := bstep (se 1 (by rfl) ⟨1469675, by rfl⟩ : syracuseStep 1959567 = 2939351) B2939351
theorem B2939357 : Blo 1959435 2939357 := bbase (se 3 (by rfl) ⟨551129, by rfl⟩ : syracuseStep 2939357 = 1102259) (by norm_num)
theorem B1959571 : Blo 1959435 1959571 := bstep (se 1 (by rfl) ⟨1469678, by rfl⟩ : syracuseStep 1959571 = 2939357) B2939357
theorem B4409045 : Blo 1959435 4409045 := bbase (se 7 (by rfl) ⟨51668, by rfl⟩ : syracuseStep 4409045 = 103337) (by norm_num)
theorem B2939363 : Blo 1959435 2939363 := bstep (se 1 (by rfl) ⟨2204522, by rfl⟩ : syracuseStep 2939363 = 4409045) B4409045
theorem B1959575 : Blo 1959435 1959575 := bstep (se 1 (by rfl) ⟨1469681, by rfl⟩ : syracuseStep 1959575 = 2939363) B2939363
theorem B3138869 : Blo 1959435 3138869 := bbase (se 5 (by rfl) ⟨147134, by rfl⟩ : syracuseStep 3138869 = 294269) (by norm_num)
theorem B8370317 : Blo 1959435 8370317 := bstep (se 3 (by rfl) ⟨1569434, by rfl⟩ : syracuseStep 8370317 = 3138869) B3138869
theorem B5580211 : Blo 1959435 5580211 := bstep (se 1 (by rfl) ⟨4185158, by rfl⟩ : syracuseStep 5580211 = 8370317) B8370317
theorem B7440281 : Blo 1959435 7440281 := bstep (se 2 (by rfl) ⟨2790105, by rfl⟩ : syracuseStep 7440281 = 5580211) B5580211
theorem B4960187 : Blo 1959435 4960187 := bstep (se 1 (by rfl) ⟨3720140, by rfl⟩ : syracuseStep 4960187 = 7440281) B7440281
theorem B3306791 : Blo 1959435 3306791 := bstep (se 1 (by rfl) ⟨2480093, by rfl⟩ : syracuseStep 3306791 = 4960187) B4960187
theorem B2204527 : Blo 1959435 2204527 := bstep (se 1 (by rfl) ⟨1653395, by rfl⟩ : syracuseStep 2204527 = 3306791) B3306791
theorem B2939369 : Blo 1959435 2939369 := bstep (se 2 (by rfl) ⟨1102263, by rfl⟩ : syracuseStep 2939369 = 2204527) B2204527
theorem B1959579 : Blo 1959435 1959579 := bstep (se 1 (by rfl) ⟨1469684, by rfl⟩ : syracuseStep 1959579 = 2939369) B2939369
theorem B20385877 : Blo 1959435 20385877 := bbase (se 8 (by rfl) ⟨119448, by rfl⟩ : syracuseStep 20385877 = 238897) (by norm_num)
theorem B27181169 : Blo 1959435 27181169 := bstep (se 2 (by rfl) ⟨10192938, by rfl⟩ : syracuseStep 27181169 = 20385877) B20385877
theorem B18120779 : Blo 1959435 18120779 := bstep (se 1 (by rfl) ⟨13590584, by rfl⟩ : syracuseStep 18120779 = 27181169) B27181169
theorem B12080519 : Blo 1959435 12080519 := bstep (se 1 (by rfl) ⟨9060389, by rfl⟩ : syracuseStep 12080519 = 18120779) B18120779
theorem B8053679 : Blo 1959435 8053679 := bstep (se 1 (by rfl) ⟨6040259, by rfl⟩ : syracuseStep 8053679 = 12080519) B12080519
theorem B21476477 : Blo 1959435 21476477 := bstep (se 3 (by rfl) ⟨4026839, by rfl⟩ : syracuseStep 21476477 = 8053679) B8053679
theorem B14317651 : Blo 1959435 14317651 := bstep (se 1 (by rfl) ⟨10738238, by rfl⟩ : syracuseStep 14317651 = 21476477) B21476477
theorem B19090201 : Blo 1959435 19090201 := bstep (se 2 (by rfl) ⟨7158825, by rfl⟩ : syracuseStep 19090201 = 14317651) B14317651
theorem B25453601 : Blo 1959435 25453601 := bstep (se 2 (by rfl) ⟨9545100, by rfl⟩ : syracuseStep 25453601 = 19090201) B19090201
theorem B16969067 : Blo 1959435 16969067 := bstep (se 1 (by rfl) ⟨12726800, by rfl⟩ : syracuseStep 16969067 = 25453601) B25453601
theorem B11312711 : Blo 1959435 11312711 := bstep (se 1 (by rfl) ⟨8484533, by rfl⟩ : syracuseStep 11312711 = 16969067) B16969067
theorem B7541807 : Blo 1959435 7541807 := bstep (se 1 (by rfl) ⟨5656355, by rfl⟩ : syracuseStep 7541807 = 11312711) B11312711
theorem B20111485 : Blo 1959435 20111485 := bstep (se 3 (by rfl) ⟨3770903, by rfl⟩ : syracuseStep 20111485 = 7541807) B7541807
theorem B26815313 : Blo 1959435 26815313 := bstep (se 2 (by rfl) ⟨10055742, by rfl⟩ : syracuseStep 26815313 = 20111485) B20111485
theorem B17876875 : Blo 1959435 17876875 := bstep (se 1 (by rfl) ⟨13407656, by rfl⟩ : syracuseStep 17876875 = 26815313) B26815313
theorem B23835833 : Blo 1959435 23835833 := bstep (se 2 (by rfl) ⟨8938437, by rfl⟩ : syracuseStep 23835833 = 17876875) B17876875
theorem B15890555 : Blo 1959435 15890555 := bstep (se 1 (by rfl) ⟨11917916, by rfl⟩ : syracuseStep 15890555 = 23835833) B23835833
theorem B10593703 : Blo 1959435 10593703 := bstep (se 1 (by rfl) ⟨7945277, by rfl⟩ : syracuseStep 10593703 = 15890555) B15890555
theorem B14124937 : Blo 1959435 14124937 := bstep (se 2 (by rfl) ⟨5296851, by rfl⟩ : syracuseStep 14124937 = 10593703) B10593703
theorem B18833249 : Blo 1959435 18833249 := bstep (se 2 (by rfl) ⟨7062468, by rfl⟩ : syracuseStep 18833249 = 14124937) B14124937
theorem B12555499 : Blo 1959435 12555499 := bstep (se 1 (by rfl) ⟨9416624, by rfl⟩ : syracuseStep 12555499 = 18833249) B18833249
theorem B16740665 : Blo 1959435 16740665 := bstep (se 2 (by rfl) ⟨6277749, by rfl⟩ : syracuseStep 16740665 = 12555499) B12555499
theorem B11160443 : Blo 1959435 11160443 := bstep (se 1 (by rfl) ⟨8370332, by rfl⟩ : syracuseStep 11160443 = 16740665) B16740665
theorem B7440295 : Blo 1959435 7440295 := bstep (se 1 (by rfl) ⟨5580221, by rfl⟩ : syracuseStep 7440295 = 11160443) B11160443
theorem B9920393 : Blo 1959435 9920393 := bstep (se 2 (by rfl) ⟨3720147, by rfl⟩ : syracuseStep 9920393 = 7440295) B7440295
theorem B6613595 : Blo 1959435 6613595 := bstep (se 1 (by rfl) ⟨4960196, by rfl⟩ : syracuseStep 6613595 = 9920393) B9920393
theorem B4409063 : Blo 1959435 4409063 := bstep (se 1 (by rfl) ⟨3306797, by rfl⟩ : syracuseStep 4409063 = 6613595) B6613595
theorem B2939375 : Blo 1959435 2939375 := bstep (se 1 (by rfl) ⟨2204531, by rfl⟩ : syracuseStep 2939375 = 4409063) B4409063
theorem B1959583 : Blo 1959435 1959583 := bstep (se 1 (by rfl) ⟨1469687, by rfl⟩ : syracuseStep 1959583 = 2939375) B2939375
theorem B2939381 : Blo 1959435 2939381 := bbase (se 5 (by rfl) ⟨137783, by rfl⟩ : syracuseStep 2939381 = 275567) (by norm_num)
theorem B1959587 : Blo 1959435 1959587 := bstep (se 1 (by rfl) ⟨1469690, by rfl⟩ : syracuseStep 1959587 = 2939381) B2939381
theorem B5580245 : Blo 1959435 5580245 := bbase (se 7 (by rfl) ⟨65393, by rfl⟩ : syracuseStep 5580245 = 130787) (by norm_num)
theorem B3720163 : Blo 1959435 3720163 := bstep (se 1 (by rfl) ⟨2790122, by rfl⟩ : syracuseStep 3720163 = 5580245) B5580245
theorem B4960217 : Blo 1959435 4960217 := bstep (se 2 (by rfl) ⟨1860081, by rfl⟩ : syracuseStep 4960217 = 3720163) B3720163
theorem B3306811 : Blo 1959435 3306811 := bstep (se 1 (by rfl) ⟨2480108, by rfl⟩ : syracuseStep 3306811 = 4960217) B4960217
theorem B4409081 : Blo 1959435 4409081 := bstep (se 2 (by rfl) ⟨1653405, by rfl⟩ : syracuseStep 4409081 = 3306811) B3306811
theorem B2939387 : Blo 1959435 2939387 := bstep (se 1 (by rfl) ⟨2204540, by rfl⟩ : syracuseStep 2939387 = 4409081) B4409081
theorem B1959591 : Blo 1959435 1959591 := bstep (se 1 (by rfl) ⟨1469693, by rfl⟩ : syracuseStep 1959591 = 2939387) B2939387
theorem B2204545 : Blo 1959435 2204545 := bbase (se 2 (by rfl) ⟨826704, by rfl⟩ : syracuseStep 2204545 = 1653409) (by norm_num)
theorem B2939393 : Blo 1959435 2939393 := bstep (se 2 (by rfl) ⟨1102272, by rfl⟩ : syracuseStep 2939393 = 2204545) B2204545
theorem B1959595 : Blo 1959435 1959595 := bstep (se 1 (by rfl) ⟨1469696, by rfl⟩ : syracuseStep 1959595 = 2939393) B2939393
theorem B4960237 : Blo 1959435 4960237 := bbase (se 3 (by rfl) ⟨930044, by rfl⟩ : syracuseStep 4960237 = 1860089) (by norm_num)
theorem B6613649 : Blo 1959435 6613649 := bstep (se 2 (by rfl) ⟨2480118, by rfl⟩ : syracuseStep 6613649 = 4960237) B4960237
theorem B4409099 : Blo 1959435 4409099 := bstep (se 1 (by rfl) ⟨3306824, by rfl⟩ : syracuseStep 4409099 = 6613649) B6613649
theorem B2939399 : Blo 1959435 2939399 := bstep (se 1 (by rfl) ⟨2204549, by rfl⟩ : syracuseStep 2939399 = 4409099) B4409099
theorem B1959599 : Blo 1959435 1959599 := bstep (se 1 (by rfl) ⟨1469699, by rfl⟩ : syracuseStep 1959599 = 2939399) B2939399
theorem B2939405 : Blo 1959435 2939405 := bbase (se 3 (by rfl) ⟨551138, by rfl⟩ : syracuseStep 2939405 = 1102277) (by norm_num)
theorem B1959603 : Blo 1959435 1959603 := bstep (se 1 (by rfl) ⟨1469702, by rfl⟩ : syracuseStep 1959603 = 2939405) B2939405
theorem B4409117 : Blo 1959435 4409117 := bbase (se 3 (by rfl) ⟨826709, by rfl⟩ : syracuseStep 4409117 = 1653419) (by norm_num)
theorem B2939411 : Blo 1959435 2939411 := bstep (se 1 (by rfl) ⟨2204558, by rfl⟩ : syracuseStep 2939411 = 4409117) B4409117
theorem B1959607 : Blo 1959435 1959607 := bstep (se 1 (by rfl) ⟨1469705, by rfl⟩ : syracuseStep 1959607 = 2939411) B2939411
theorem B3306845 : Blo 1959435 3306845 := bbase (se 3 (by rfl) ⟨620033, by rfl⟩ : syracuseStep 3306845 = 1240067) (by norm_num)
theorem B2204563 : Blo 1959435 2204563 := bstep (se 1 (by rfl) ⟨1653422, by rfl⟩ : syracuseStep 2204563 = 3306845) B3306845
theorem B2939417 : Blo 1959435 2939417 := bstep (se 2 (by rfl) ⟨1102281, by rfl⟩ : syracuseStep 2939417 = 2204563) B2204563
theorem B1959611 : Blo 1959435 1959611 := bstep (se 1 (by rfl) ⟨1469708, by rfl⟩ : syracuseStep 1959611 = 2939417) B2939417
theorem B8370469 : Blo 1959435 8370469 := bbase (se 4 (by rfl) ⟨784731, by rfl⟩ : syracuseStep 8370469 = 1569463) (by norm_num)
theorem B11160625 : Blo 1959435 11160625 := bstep (se 2 (by rfl) ⟨4185234, by rfl⟩ : syracuseStep 11160625 = 8370469) B8370469
theorem B14880833 : Blo 1959435 14880833 := bstep (se 2 (by rfl) ⟨5580312, by rfl⟩ : syracuseStep 14880833 = 11160625) B11160625
theorem B9920555 : Blo 1959435 9920555 := bstep (se 1 (by rfl) ⟨7440416, by rfl⟩ : syracuseStep 9920555 = 14880833) B14880833
theorem B6613703 : Blo 1959435 6613703 := bstep (se 1 (by rfl) ⟨4960277, by rfl⟩ : syracuseStep 6613703 = 9920555) B9920555
theorem B4409135 : Blo 1959435 4409135 := bstep (se 1 (by rfl) ⟨3306851, by rfl⟩ : syracuseStep 4409135 = 6613703) B6613703
theorem B2939423 : Blo 1959435 2939423 := bstep (se 1 (by rfl) ⟨2204567, by rfl⟩ : syracuseStep 2939423 = 4409135) B4409135
theorem B1959615 : Blo 1959435 1959615 := bstep (se 1 (by rfl) ⟨1469711, by rfl⟩ : syracuseStep 1959615 = 2939423) B2939423
theorem B2939429 : Blo 1959435 2939429 := bbase (se 4 (by rfl) ⟨275571, by rfl⟩ : syracuseStep 2939429 = 551143) (by norm_num)
theorem B1959619 : Blo 1959435 1959619 := bstep (se 1 (by rfl) ⟨1469714, by rfl⟩ : syracuseStep 1959619 = 2939429) B2939429
theorem B2480149 : Blo 1959435 2480149 := bbase (se 6 (by rfl) ⟨58128, by rfl⟩ : syracuseStep 2480149 = 116257) (by norm_num)
theorem B3306865 : Blo 1959435 3306865 := bstep (se 2 (by rfl) ⟨1240074, by rfl⟩ : syracuseStep 3306865 = 2480149) B2480149
theorem B4409153 : Blo 1959435 4409153 := bstep (se 2 (by rfl) ⟨1653432, by rfl⟩ : syracuseStep 4409153 = 3306865) B3306865
theorem B2939435 : Blo 1959435 2939435 := bstep (se 1 (by rfl) ⟨2204576, by rfl⟩ : syracuseStep 2939435 = 4409153) B4409153
theorem B1959623 : Blo 1959435 1959623 := bstep (se 1 (by rfl) ⟨1469717, by rfl⟩ : syracuseStep 1959623 = 2939435) B2939435
theorem B2204581 : Blo 1959435 2204581 := bbase (se 4 (by rfl) ⟨206679, by rfl⟩ : syracuseStep 2204581 = 413359) (by norm_num)
theorem B2939441 : Blo 1959435 2939441 := bstep (se 2 (by rfl) ⟨1102290, by rfl⟩ : syracuseStep 2939441 = 2204581) B2204581
theorem B1959627 : Blo 1959435 1959627 := bstep (se 1 (by rfl) ⟨1469720, by rfl⟩ : syracuseStep 1959627 = 2939441) B2939441
theorem B2234665 : Blo 1959435 2234665 := bbase (se 2 (by rfl) ⟨837999, by rfl⟩ : syracuseStep 2234665 = 1675999) (by norm_num)
theorem B2979553 : Blo 1959435 2979553 := bstep (se 2 (by rfl) ⟨1117332, by rfl⟩ : syracuseStep 2979553 = 2234665) B2234665
theorem B3972737 : Blo 1959435 3972737 := bstep (se 2 (by rfl) ⟨1489776, by rfl⟩ : syracuseStep 3972737 = 2979553) B2979553
theorem B10593965 : Blo 1959435 10593965 := bstep (se 3 (by rfl) ⟨1986368, by rfl⟩ : syracuseStep 10593965 = 3972737) B3972737
theorem B7062643 : Blo 1959435 7062643 := bstep (se 1 (by rfl) ⟨5296982, by rfl⟩ : syracuseStep 7062643 = 10593965) B10593965
theorem B9416857 : Blo 1959435 9416857 := bstep (se 2 (by rfl) ⟨3531321, by rfl⟩ : syracuseStep 9416857 = 7062643) B7062643
theorem B12555809 : Blo 1959435 12555809 := bstep (se 2 (by rfl) ⟨4708428, by rfl⟩ : syracuseStep 12555809 = 9416857) B9416857
theorem B8370539 : Blo 1959435 8370539 := bstep (se 1 (by rfl) ⟨6277904, by rfl⟩ : syracuseStep 8370539 = 12555809) B12555809
theorem B5580359 : Blo 1959435 5580359 := bstep (se 1 (by rfl) ⟨4185269, by rfl⟩ : syracuseStep 5580359 = 8370539) B8370539
theorem B3720239 : Blo 1959435 3720239 := bstep (se 1 (by rfl) ⟨2790179, by rfl⟩ : syracuseStep 3720239 = 5580359) B5580359
theorem B2480159 : Blo 1959435 2480159 := bstep (se 1 (by rfl) ⟨1860119, by rfl⟩ : syracuseStep 2480159 = 3720239) B3720239
theorem B6613757 : Blo 1959435 6613757 := bstep (se 3 (by rfl) ⟨1240079, by rfl⟩ : syracuseStep 6613757 = 2480159) B2480159
theorem B4409171 : Blo 1959435 4409171 := bstep (se 1 (by rfl) ⟨3306878, by rfl⟩ : syracuseStep 4409171 = 6613757) B6613757
theorem B2939447 : Blo 1959435 2939447 := bstep (se 1 (by rfl) ⟨2204585, by rfl⟩ : syracuseStep 2939447 = 4409171) B4409171
theorem B1959631 : Blo 1959435 1959631 := bstep (se 1 (by rfl) ⟨1469723, by rfl⟩ : syracuseStep 1959631 = 2939447) B2939447
theorem B2939453 : Blo 1959435 2939453 := bbase (se 3 (by rfl) ⟨551147, by rfl⟩ : syracuseStep 2939453 = 1102295) (by norm_num)
theorem B1959635 : Blo 1959435 1959635 := bstep (se 1 (by rfl) ⟨1469726, by rfl⟩ : syracuseStep 1959635 = 2939453) B2939453
theorem B4409189 : Blo 1959435 4409189 := bbase (se 4 (by rfl) ⟨413361, by rfl⟩ : syracuseStep 4409189 = 826723) (by norm_num)
theorem B2939459 : Blo 1959435 2939459 := bstep (se 1 (by rfl) ⟨2204594, by rfl⟩ : syracuseStep 2939459 = 4409189) B4409189
theorem B1959639 : Blo 1959435 1959639 := bstep (se 1 (by rfl) ⟨1469729, by rfl⟩ : syracuseStep 1959639 = 2939459) B2939459
theorem B4960349 : Blo 1959435 4960349 := bbase (se 3 (by rfl) ⟨930065, by rfl⟩ : syracuseStep 4960349 = 1860131) (by norm_num)
theorem B3306899 : Blo 1959435 3306899 := bstep (se 1 (by rfl) ⟨2480174, by rfl⟩ : syracuseStep 3306899 = 4960349) B4960349
theorem B2204599 : Blo 1959435 2204599 := bstep (se 1 (by rfl) ⟨1653449, by rfl⟩ : syracuseStep 2204599 = 3306899) B3306899
theorem B2939465 : Blo 1959435 2939465 := bstep (se 2 (by rfl) ⟨1102299, by rfl⟩ : syracuseStep 2939465 = 2204599) B2204599
theorem B1959643 : Blo 1959435 1959643 := bstep (se 1 (by rfl) ⟨1469732, by rfl⟩ : syracuseStep 1959643 = 2939465) B2939465
theorem B3720269 : Blo 1959435 3720269 := bbase (se 3 (by rfl) ⟨697550, by rfl⟩ : syracuseStep 3720269 = 1395101) (by norm_num)
theorem B9920717 : Blo 1959435 9920717 := bstep (se 3 (by rfl) ⟨1860134, by rfl⟩ : syracuseStep 9920717 = 3720269) B3720269
theorem B6613811 : Blo 1959435 6613811 := bstep (se 1 (by rfl) ⟨4960358, by rfl⟩ : syracuseStep 6613811 = 9920717) B9920717
theorem B4409207 : Blo 1959435 4409207 := bstep (se 1 (by rfl) ⟨3306905, by rfl⟩ : syracuseStep 4409207 = 6613811) B6613811
theorem B2939471 : Blo 1959435 2939471 := bstep (se 1 (by rfl) ⟨2204603, by rfl⟩ : syracuseStep 2939471 = 4409207) B4409207
theorem B1959647 : Blo 1959435 1959647 := bstep (se 1 (by rfl) ⟨1469735, by rfl⟩ : syracuseStep 1959647 = 2939471) B2939471
theorem B2939477 : Blo 1959435 2939477 := bbase (se 8 (by rfl) ⟨17223, by rfl⟩ : syracuseStep 2939477 = 34447) (by norm_num)
theorem B1959651 : Blo 1959435 1959651 := bstep (se 1 (by rfl) ⟨1469738, by rfl⟩ : syracuseStep 1959651 = 2939477) B2939477
theorem B3531365 : Blo 1959435 3531365 := bbase (se 4 (by rfl) ⟨331065, by rfl⟩ : syracuseStep 3531365 = 662131) (by norm_num)
theorem B2354243 : Blo 1959435 2354243 := bstep (se 1 (by rfl) ⟨1765682, by rfl⟩ : syracuseStep 2354243 = 3531365) B3531365
theorem B6277981 : Blo 1959435 6277981 := bstep (se 3 (by rfl) ⟨1177121, by rfl⟩ : syracuseStep 6277981 = 2354243) B2354243
theorem B8370641 : Blo 1959435 8370641 := bstep (se 2 (by rfl) ⟨3138990, by rfl⟩ : syracuseStep 8370641 = 6277981) B6277981
theorem B5580427 : Blo 1959435 5580427 := bstep (se 1 (by rfl) ⟨4185320, by rfl⟩ : syracuseStep 5580427 = 8370641) B8370641
theorem B7440569 : Blo 1959435 7440569 := bstep (se 2 (by rfl) ⟨2790213, by rfl⟩ : syracuseStep 7440569 = 5580427) B5580427
theorem B4960379 : Blo 1959435 4960379 := bstep (se 1 (by rfl) ⟨3720284, by rfl⟩ : syracuseStep 4960379 = 7440569) B7440569
theorem B3306919 : Blo 1959435 3306919 := bstep (se 1 (by rfl) ⟨2480189, by rfl⟩ : syracuseStep 3306919 = 4960379) B4960379
theorem B4409225 : Blo 1959435 4409225 := bstep (se 2 (by rfl) ⟨1653459, by rfl⟩ : syracuseStep 4409225 = 3306919) B3306919
theorem B2939483 : Blo 1959435 2939483 := bstep (se 1 (by rfl) ⟨2204612, by rfl⟩ : syracuseStep 2939483 = 4409225) B4409225
theorem B1959655 : Blo 1959435 1959655 := bstep (se 1 (by rfl) ⟨1469741, by rfl⟩ : syracuseStep 1959655 = 2939483) B2939483
theorem B2204617 : Blo 1959435 2204617 := bbase (se 2 (by rfl) ⟨826731, by rfl⟩ : syracuseStep 2204617 = 1653463) (by norm_num)
theorem B2939489 : Blo 1959435 2939489 := bstep (se 2 (by rfl) ⟨1102308, by rfl⟩ : syracuseStep 2939489 = 2204617) B2204617
theorem B1959659 : Blo 1959435 1959659 := bstep (se 1 (by rfl) ⟨1469744, by rfl⟩ : syracuseStep 1959659 = 2939489) B2939489
theorem B1986401 : Blo 1959435 1986401 := bbase (se 2 (by rfl) ⟨744900, by rfl⟩ : syracuseStep 1986401 = 1489801) (by norm_num)
theorem B5297069 : Blo 1959435 5297069 := bstep (se 3 (by rfl) ⟨993200, by rfl⟩ : syracuseStep 5297069 = 1986401) B1986401
theorem B3531379 : Blo 1959435 3531379 := bstep (se 1 (by rfl) ⟨2648534, by rfl⟩ : syracuseStep 3531379 = 5297069) B5297069
theorem B4708505 : Blo 1959435 4708505 := bstep (se 2 (by rfl) ⟨1765689, by rfl⟩ : syracuseStep 4708505 = 3531379) B3531379
theorem B3139003 : Blo 1959435 3139003 := bstep (se 1 (by rfl) ⟨2354252, by rfl⟩ : syracuseStep 3139003 = 4708505) B4708505
theorem B16741349 : Blo 1959435 16741349 := bstep (se 4 (by rfl) ⟨1569501, by rfl⟩ : syracuseStep 16741349 = 3139003) B3139003
theorem B11160899 : Blo 1959435 11160899 := bstep (se 1 (by rfl) ⟨8370674, by rfl⟩ : syracuseStep 11160899 = 16741349) B16741349
theorem B7440599 : Blo 1959435 7440599 := bstep (se 1 (by rfl) ⟨5580449, by rfl⟩ : syracuseStep 7440599 = 11160899) B11160899
theorem B4960399 : Blo 1959435 4960399 := bstep (se 1 (by rfl) ⟨3720299, by rfl⟩ : syracuseStep 4960399 = 7440599) B7440599
theorem B6613865 : Blo 1959435 6613865 := bstep (se 2 (by rfl) ⟨2480199, by rfl⟩ : syracuseStep 6613865 = 4960399) B4960399
theorem B4409243 : Blo 1959435 4409243 := bstep (se 1 (by rfl) ⟨3306932, by rfl⟩ : syracuseStep 4409243 = 6613865) B6613865
theorem B2939495 : Blo 1959435 2939495 := bstep (se 1 (by rfl) ⟨2204621, by rfl⟩ : syracuseStep 2939495 = 4409243) B4409243
theorem B1959663 : Blo 1959435 1959663 := bstep (se 1 (by rfl) ⟨1469747, by rfl⟩ : syracuseStep 1959663 = 2939495) B2939495
theorem B2939501 : Blo 1959435 2939501 := bbase (se 3 (by rfl) ⟨551156, by rfl⟩ : syracuseStep 2939501 = 1102313) (by norm_num)
theorem B1959667 : Blo 1959435 1959667 := bstep (se 1 (by rfl) ⟨1469750, by rfl⟩ : syracuseStep 1959667 = 2939501) B2939501
theorem B4409261 : Blo 1959435 4409261 := bbase (se 3 (by rfl) ⟨826736, by rfl⟩ : syracuseStep 4409261 = 1653473) (by norm_num)
theorem B2939507 : Blo 1959435 2939507 := bstep (se 1 (by rfl) ⟨2204630, by rfl⟩ : syracuseStep 2939507 = 4409261) B4409261
theorem B1959671 : Blo 1959435 1959671 := bstep (se 1 (by rfl) ⟨1469753, by rfl⟩ : syracuseStep 1959671 = 2939507) B2939507
theorem B5580485 : Blo 1959435 5580485 := bbase (se 4 (by rfl) ⟨523170, by rfl⟩ : syracuseStep 5580485 = 1046341) (by norm_num)
theorem B3720323 : Blo 1959435 3720323 := bstep (se 1 (by rfl) ⟨2790242, by rfl⟩ : syracuseStep 3720323 = 5580485) B5580485
theorem B2480215 : Blo 1959435 2480215 := bstep (se 1 (by rfl) ⟨1860161, by rfl⟩ : syracuseStep 2480215 = 3720323) B3720323
theorem B3306953 : Blo 1959435 3306953 := bstep (se 2 (by rfl) ⟨1240107, by rfl⟩ : syracuseStep 3306953 = 2480215) B2480215
theorem B2204635 : Blo 1959435 2204635 := bstep (se 1 (by rfl) ⟨1653476, by rfl⟩ : syracuseStep 2204635 = 3306953) B3306953
theorem B2939513 : Blo 1959435 2939513 := bstep (se 2 (by rfl) ⟨1102317, by rfl⟩ : syracuseStep 2939513 = 2204635) B2204635
theorem B1959675 : Blo 1959435 1959675 := bstep (se 1 (by rfl) ⟨1469756, by rfl⟩ : syracuseStep 1959675 = 2939513) B2939513
theorem B11313269 : Blo 1959435 11313269 := bbase (se 5 (by rfl) ⟨530309, by rfl⟩ : syracuseStep 11313269 = 1060619) (by norm_num)
theorem B7542179 : Blo 1959435 7542179 := bstep (se 1 (by rfl) ⟨5656634, by rfl⟩ : syracuseStep 7542179 = 11313269) B11313269
theorem B5028119 : Blo 1959435 5028119 := bstep (se 1 (by rfl) ⟨3771089, by rfl⟩ : syracuseStep 5028119 = 7542179) B7542179
theorem B3352079 : Blo 1959435 3352079 := bstep (se 1 (by rfl) ⟨2514059, by rfl⟩ : syracuseStep 3352079 = 5028119) B5028119
theorem B2234719 : Blo 1959435 2234719 := bstep (se 1 (by rfl) ⟨1676039, by rfl⟩ : syracuseStep 2234719 = 3352079) B3352079
theorem B11918501 : Blo 1959435 11918501 := bstep (se 4 (by rfl) ⟨1117359, by rfl⟩ : syracuseStep 11918501 = 2234719) B2234719
theorem B7945667 : Blo 1959435 7945667 := bstep (se 1 (by rfl) ⟨5959250, by rfl⟩ : syracuseStep 7945667 = 11918501) B11918501
theorem B5297111 : Blo 1959435 5297111 := bstep (se 1 (by rfl) ⟨3972833, by rfl⟩ : syracuseStep 5297111 = 7945667) B7945667
theorem B3531407 : Blo 1959435 3531407 := bstep (se 1 (by rfl) ⟨2648555, by rfl⟩ : syracuseStep 3531407 = 5297111) B5297111
theorem B37668341 : Blo 1959435 37668341 := bstep (se 5 (by rfl) ⟨1765703, by rfl⟩ : syracuseStep 37668341 = 3531407) B3531407
theorem B25112227 : Blo 1959435 25112227 := bstep (se 1 (by rfl) ⟨18834170, by rfl⟩ : syracuseStep 25112227 = 37668341) B37668341
theorem B33482969 : Blo 1959435 33482969 := bstep (se 2 (by rfl) ⟨12556113, by rfl⟩ : syracuseStep 33482969 = 25112227) B25112227
theorem B22321979 : Blo 1959435 22321979 := bstep (se 1 (by rfl) ⟨16741484, by rfl⟩ : syracuseStep 22321979 = 33482969) B33482969
theorem B14881319 : Blo 1959435 14881319 := bstep (se 1 (by rfl) ⟨11160989, by rfl⟩ : syracuseStep 14881319 = 22321979) B22321979
theorem B9920879 : Blo 1959435 9920879 := bstep (se 1 (by rfl) ⟨7440659, by rfl⟩ : syracuseStep 9920879 = 14881319) B14881319
theorem B6613919 : Blo 1959435 6613919 := bstep (se 1 (by rfl) ⟨4960439, by rfl⟩ : syracuseStep 6613919 = 9920879) B9920879
theorem B4409279 : Blo 1959435 4409279 := bstep (se 1 (by rfl) ⟨3306959, by rfl⟩ : syracuseStep 4409279 = 6613919) B6613919
theorem B2939519 : Blo 1959435 2939519 := bstep (se 1 (by rfl) ⟨2204639, by rfl⟩ : syracuseStep 2939519 = 4409279) B4409279
theorem B1959679 : Blo 1959435 1959679 := bstep (se 1 (by rfl) ⟨1469759, by rfl⟩ : syracuseStep 1959679 = 2939519) B2939519
theorem B2939525 : Blo 1959435 2939525 := bbase (se 4 (by rfl) ⟨275580, by rfl⟩ : syracuseStep 2939525 = 551161) (by norm_num)
theorem B1959683 : Blo 1959435 1959683 := bstep (se 1 (by rfl) ⟨1469762, by rfl⟩ : syracuseStep 1959683 = 2939525) B2939525
theorem B3306973 : Blo 1959435 3306973 := bbase (se 3 (by rfl) ⟨620057, by rfl⟩ : syracuseStep 3306973 = 1240115) (by norm_num)
theorem B4409297 : Blo 1959435 4409297 := bstep (se 2 (by rfl) ⟨1653486, by rfl⟩ : syracuseStep 4409297 = 3306973) B3306973
theorem B2939531 : Blo 1959435 2939531 := bstep (se 1 (by rfl) ⟨2204648, by rfl⟩ : syracuseStep 2939531 = 4409297) B4409297
theorem B1959687 : Blo 1959435 1959687 := bstep (se 1 (by rfl) ⟨1469765, by rfl⟩ : syracuseStep 1959687 = 2939531) B2939531
theorem B2204653 : Blo 1959435 2204653 := bbase (se 3 (by rfl) ⟨413372, by rfl⟩ : syracuseStep 2204653 = 826745) (by norm_num)
theorem B2939537 : Blo 1959435 2939537 := bstep (se 2 (by rfl) ⟨1102326, by rfl⟩ : syracuseStep 2939537 = 2204653) B2204653
theorem B1959691 : Blo 1959435 1959691 := bstep (se 1 (by rfl) ⟨1469768, by rfl⟩ : syracuseStep 1959691 = 2939537) B2939537
theorem B6613973 : Blo 1959435 6613973 := bbase (se 7 (by rfl) ⟨77507, by rfl⟩ : syracuseStep 6613973 = 155015) (by norm_num)
theorem B4409315 : Blo 1959435 4409315 := bstep (se 1 (by rfl) ⟨3306986, by rfl⟩ : syracuseStep 4409315 = 6613973) B6613973
theorem B2939543 : Blo 1959435 2939543 := bstep (se 1 (by rfl) ⟨2204657, by rfl⟩ : syracuseStep 2939543 = 4409315) B4409315
theorem B1959695 : Blo 1959435 1959695 := bstep (se 1 (by rfl) ⟨1469771, by rfl⟩ : syracuseStep 1959695 = 2939543) B2939543
theorem B2939549 : Blo 1959435 2939549 := bbase (se 3 (by rfl) ⟨551165, by rfl⟩ : syracuseStep 2939549 = 1102331) (by norm_num)
theorem B1959699 : Blo 1959435 1959699 := bstep (se 1 (by rfl) ⟨1469774, by rfl⟩ : syracuseStep 1959699 = 2939549) B2939549
theorem B4409333 : Blo 1959435 4409333 := bbase (se 5 (by rfl) ⟨206687, by rfl⟩ : syracuseStep 4409333 = 413375) (by norm_num)
theorem B2939555 : Blo 1959435 2939555 := bstep (se 1 (by rfl) ⟨2204666, by rfl⟩ : syracuseStep 2939555 = 4409333) B4409333
theorem B1959703 : Blo 1959435 1959703 := bstep (se 1 (by rfl) ⟨1469777, by rfl⟩ : syracuseStep 1959703 = 2939555) B2939555
theorem B7945781 : Blo 1959435 7945781 := bbase (se 5 (by rfl) ⟨372458, by rfl⟩ : syracuseStep 7945781 = 744917) (by norm_num)
theorem B84754997 : Blo 1959435 84754997 := bstep (se 5 (by rfl) ⟨3972890, by rfl⟩ : syracuseStep 84754997 = 7945781) B7945781
theorem B56503331 : Blo 1959435 56503331 := bstep (se 1 (by rfl) ⟨42377498, by rfl⟩ : syracuseStep 56503331 = 84754997) B84754997
theorem B37668887 : Blo 1959435 37668887 := bstep (se 1 (by rfl) ⟨28251665, by rfl⟩ : syracuseStep 37668887 = 56503331) B56503331
theorem B25112591 : Blo 1959435 25112591 := bstep (se 1 (by rfl) ⟨18834443, by rfl⟩ : syracuseStep 25112591 = 37668887) B37668887
theorem B16741727 : Blo 1959435 16741727 := bstep (se 1 (by rfl) ⟨12556295, by rfl⟩ : syracuseStep 16741727 = 25112591) B25112591
theorem B11161151 : Blo 1959435 11161151 := bstep (se 1 (by rfl) ⟨8370863, by rfl⟩ : syracuseStep 11161151 = 16741727) B16741727
theorem B7440767 : Blo 1959435 7440767 := bstep (se 1 (by rfl) ⟨5580575, by rfl⟩ : syracuseStep 7440767 = 11161151) B11161151
theorem B4960511 : Blo 1959435 4960511 := bstep (se 1 (by rfl) ⟨3720383, by rfl⟩ : syracuseStep 4960511 = 7440767) B7440767
theorem B3307007 : Blo 1959435 3307007 := bstep (se 1 (by rfl) ⟨2480255, by rfl⟩ : syracuseStep 3307007 = 4960511) B4960511
theorem B2204671 : Blo 1959435 2204671 := bstep (se 1 (by rfl) ⟨1653503, by rfl⟩ : syracuseStep 2204671 = 3307007) B3307007
theorem B2939561 : Blo 1959435 2939561 := bstep (se 2 (by rfl) ⟨1102335, by rfl⟩ : syracuseStep 2939561 = 2204671) B2204671
theorem B1959707 : Blo 1959435 1959707 := bstep (se 1 (by rfl) ⟨1469780, by rfl⟩ : syracuseStep 1959707 = 2939561) B2939561
theorem B2790293 : Blo 1959435 2790293 := bbase (se 6 (by rfl) ⟨65397, by rfl⟩ : syracuseStep 2790293 = 130795) (by norm_num)
theorem B7440781 : Blo 1959435 7440781 := bstep (se 3 (by rfl) ⟨1395146, by rfl⟩ : syracuseStep 7440781 = 2790293) B2790293
theorem B9921041 : Blo 1959435 9921041 := bstep (se 2 (by rfl) ⟨3720390, by rfl⟩ : syracuseStep 9921041 = 7440781) B7440781
theorem B6614027 : Blo 1959435 6614027 := bstep (se 1 (by rfl) ⟨4960520, by rfl⟩ : syracuseStep 6614027 = 9921041) B9921041
theorem B4409351 : Blo 1959435 4409351 := bstep (se 1 (by rfl) ⟨3307013, by rfl⟩ : syracuseStep 4409351 = 6614027) B6614027
theorem B2939567 : Blo 1959435 2939567 := bstep (se 1 (by rfl) ⟨2204675, by rfl⟩ : syracuseStep 2939567 = 4409351) B4409351
theorem B1959711 : Blo 1959435 1959711 := bstep (se 1 (by rfl) ⟨1469783, by rfl⟩ : syracuseStep 1959711 = 2939567) B2939567
theorem B2939573 : Blo 1959435 2939573 := bbase (se 5 (by rfl) ⟨137792, by rfl⟩ : syracuseStep 2939573 = 275585) (by norm_num)
theorem B1959715 : Blo 1959435 1959715 := bstep (se 1 (by rfl) ⟨1469786, by rfl⟩ : syracuseStep 1959715 = 2939573) B2939573
theorem B4960541 : Blo 1959435 4960541 := bbase (se 3 (by rfl) ⟨930101, by rfl⟩ : syracuseStep 4960541 = 1860203) (by norm_num)
theorem B3307027 : Blo 1959435 3307027 := bstep (se 1 (by rfl) ⟨2480270, by rfl⟩ : syracuseStep 3307027 = 4960541) B4960541
theorem B4409369 : Blo 1959435 4409369 := bstep (se 2 (by rfl) ⟨1653513, by rfl⟩ : syracuseStep 4409369 = 3307027) B3307027
theorem B2939579 : Blo 1959435 2939579 := bstep (se 1 (by rfl) ⟨2204684, by rfl⟩ : syracuseStep 2939579 = 4409369) B4409369
theorem B1959719 : Blo 1959435 1959719 := bstep (se 1 (by rfl) ⟨1469789, by rfl⟩ : syracuseStep 1959719 = 2939579) B2939579
theorem B2204689 : Blo 1959435 2204689 := bbase (se 2 (by rfl) ⟨826758, by rfl⟩ : syracuseStep 2204689 = 1653517) (by norm_num)
theorem B2939585 : Blo 1959435 2939585 := bstep (se 2 (by rfl) ⟨1102344, by rfl⟩ : syracuseStep 2939585 = 2204689) B2204689
theorem B1959723 : Blo 1959435 1959723 := bstep (se 1 (by rfl) ⟨1469792, by rfl⟩ : syracuseStep 1959723 = 2939585) B2939585
theorem B3720421 : Blo 1959435 3720421 := bbase (se 4 (by rfl) ⟨348789, by rfl⟩ : syracuseStep 3720421 = 697579) (by norm_num)
theorem B4960561 : Blo 1959435 4960561 := bstep (se 2 (by rfl) ⟨1860210, by rfl⟩ : syracuseStep 4960561 = 3720421) B3720421
theorem B6614081 : Blo 1959435 6614081 := bstep (se 2 (by rfl) ⟨2480280, by rfl⟩ : syracuseStep 6614081 = 4960561) B4960561
theorem B4409387 : Blo 1959435 4409387 := bstep (se 1 (by rfl) ⟨3307040, by rfl⟩ : syracuseStep 4409387 = 6614081) B6614081
theorem B2939591 : Blo 1959435 2939591 := bstep (se 1 (by rfl) ⟨2204693, by rfl⟩ : syracuseStep 2939591 = 4409387) B4409387
theorem B1959727 : Blo 1959435 1959727 := bstep (se 1 (by rfl) ⟨1469795, by rfl⟩ : syracuseStep 1959727 = 2939591) B2939591
theorem B2939597 : Blo 1959435 2939597 := bbase (se 3 (by rfl) ⟨551174, by rfl⟩ : syracuseStep 2939597 = 1102349) (by norm_num)
theorem B1959731 : Blo 1959435 1959731 := bstep (se 1 (by rfl) ⟨1469798, by rfl⟩ : syracuseStep 1959731 = 2939597) B2939597
theorem B4409405 : Blo 1959435 4409405 := bbase (se 3 (by rfl) ⟨826763, by rfl⟩ : syracuseStep 4409405 = 1653527) (by norm_num)
theorem B2939603 : Blo 1959435 2939603 := bstep (se 1 (by rfl) ⟨2204702, by rfl⟩ : syracuseStep 2939603 = 4409405) B4409405
theorem B1959735 : Blo 1959435 1959735 := bstep (se 1 (by rfl) ⟨1469801, by rfl⟩ : syracuseStep 1959735 = 2939603) B2939603
theorem B3307061 : Blo 1959435 3307061 := bbase (se 5 (by rfl) ⟨155018, by rfl⟩ : syracuseStep 3307061 = 310037) (by norm_num)
theorem B2204707 : Blo 1959435 2204707 := bstep (se 1 (by rfl) ⟨1653530, by rfl⟩ : syracuseStep 2204707 = 3307061) B3307061
theorem B2939609 : Blo 1959435 2939609 := bstep (se 2 (by rfl) ⟨1102353, by rfl⟩ : syracuseStep 2939609 = 2204707) B2204707
theorem B1959739 : Blo 1959435 1959739 := bstep (se 1 (by rfl) ⟨1469804, by rfl⟩ : syracuseStep 1959739 = 2939609) B2939609
theorem B5580677 : Blo 1959435 5580677 := bbase (se 4 (by rfl) ⟨523188, by rfl⟩ : syracuseStep 5580677 = 1046377) (by norm_num)
theorem B14881805 : Blo 1959435 14881805 := bstep (se 3 (by rfl) ⟨2790338, by rfl⟩ : syracuseStep 14881805 = 5580677) B5580677
theorem B9921203 : Blo 1959435 9921203 := bstep (se 1 (by rfl) ⟨7440902, by rfl⟩ : syracuseStep 9921203 = 14881805) B14881805
theorem B6614135 : Blo 1959435 6614135 := bstep (se 1 (by rfl) ⟨4960601, by rfl⟩ : syracuseStep 6614135 = 9921203) B9921203
theorem B4409423 : Blo 1959435 4409423 := bstep (se 1 (by rfl) ⟨3307067, by rfl⟩ : syracuseStep 4409423 = 6614135) B6614135
theorem B2939615 : Blo 1959435 2939615 := bstep (se 1 (by rfl) ⟨2204711, by rfl⟩ : syracuseStep 2939615 = 4409423) B4409423
theorem B1959743 : Blo 1959435 1959743 := bstep (se 1 (by rfl) ⟨1469807, by rfl⟩ : syracuseStep 1959743 = 2939615) B2939615
theorem B2939621 : Blo 1959435 2939621 := bbase (se 4 (by rfl) ⟨275589, by rfl⟩ : syracuseStep 2939621 = 551179) (by norm_num)
theorem B1959747 : Blo 1959435 1959747 := bstep (se 1 (by rfl) ⟨1469810, by rfl⟩ : syracuseStep 1959747 = 2939621) B2939621
theorem B3352205 : Blo 1959435 3352205 := bbase (se 3 (by rfl) ⟨628538, by rfl⟩ : syracuseStep 3352205 = 1257077) (by norm_num)
theorem B2234803 : Blo 1959435 2234803 := bstep (se 1 (by rfl) ⟨1676102, by rfl⟩ : syracuseStep 2234803 = 3352205) B3352205
theorem B2979737 : Blo 1959435 2979737 := bstep (se 2 (by rfl) ⟨1117401, by rfl⟩ : syracuseStep 2979737 = 2234803) B2234803
theorem B1986491 : Blo 1959435 1986491 := bstep (se 1 (by rfl) ⟨1489868, by rfl⟩ : syracuseStep 1986491 = 2979737) B2979737
theorem B5297309 : Blo 1959435 5297309 := bstep (se 3 (by rfl) ⟨993245, by rfl⟩ : syracuseStep 5297309 = 1986491) B1986491
theorem B3531539 : Blo 1959435 3531539 := bstep (se 1 (by rfl) ⟨2648654, by rfl⟩ : syracuseStep 3531539 = 5297309) B5297309
theorem B2354359 : Blo 1959435 2354359 := bstep (se 1 (by rfl) ⟨1765769, by rfl⟩ : syracuseStep 2354359 = 3531539) B3531539
theorem B3139145 : Blo 1959435 3139145 := bstep (se 2 (by rfl) ⟨1177179, by rfl⟩ : syracuseStep 3139145 = 2354359) B2354359
theorem B2092763 : Blo 1959435 2092763 := bstep (se 1 (by rfl) ⟨1569572, by rfl⟩ : syracuseStep 2092763 = 3139145) B3139145
theorem B5580701 : Blo 1959435 5580701 := bstep (se 3 (by rfl) ⟨1046381, by rfl⟩ : syracuseStep 5580701 = 2092763) B2092763
theorem B3720467 : Blo 1959435 3720467 := bstep (se 1 (by rfl) ⟨2790350, by rfl⟩ : syracuseStep 3720467 = 5580701) B5580701
theorem B2480311 : Blo 1959435 2480311 := bstep (se 1 (by rfl) ⟨1860233, by rfl⟩ : syracuseStep 2480311 = 3720467) B3720467
theorem B3307081 : Blo 1959435 3307081 := bstep (se 2 (by rfl) ⟨1240155, by rfl⟩ : syracuseStep 3307081 = 2480311) B2480311
theorem B4409441 : Blo 1959435 4409441 := bstep (se 2 (by rfl) ⟨1653540, by rfl⟩ : syracuseStep 4409441 = 3307081) B3307081
theorem B2939627 : Blo 1959435 2939627 := bstep (se 1 (by rfl) ⟨2204720, by rfl⟩ : syracuseStep 2939627 = 4409441) B4409441
theorem B1959751 : Blo 1959435 1959751 := bstep (se 1 (by rfl) ⟨1469813, by rfl⟩ : syracuseStep 1959751 = 2939627) B2939627
theorem B2204725 : Blo 1959435 2204725 := bbase (se 5 (by rfl) ⟨103346, by rfl⟩ : syracuseStep 2204725 = 206693) (by norm_num)
theorem B2939633 : Blo 1959435 2939633 := bstep (se 2 (by rfl) ⟨1102362, by rfl⟩ : syracuseStep 2939633 = 2204725) B2204725
theorem B1959755 : Blo 1959435 1959755 := bstep (se 1 (by rfl) ⟨1469816, by rfl⟩ : syracuseStep 1959755 = 2939633) B2939633
theorem B2480321 : Blo 1959435 2480321 := bbase (se 2 (by rfl) ⟨930120, by rfl⟩ : syracuseStep 2480321 = 1860241) (by norm_num)
theorem B6614189 : Blo 1959435 6614189 := bstep (se 3 (by rfl) ⟨1240160, by rfl⟩ : syracuseStep 6614189 = 2480321) B2480321
theorem B4409459 : Blo 1959435 4409459 := bstep (se 1 (by rfl) ⟨3307094, by rfl⟩ : syracuseStep 4409459 = 6614189) B6614189
theorem B2939639 : Blo 1959435 2939639 := bstep (se 1 (by rfl) ⟨2204729, by rfl⟩ : syracuseStep 2939639 = 4409459) B4409459
theorem B1959759 : Blo 1959435 1959759 := bstep (se 1 (by rfl) ⟨1469819, by rfl⟩ : syracuseStep 1959759 = 2939639) B2939639
theorem B2939645 : Blo 1959435 2939645 := bbase (se 3 (by rfl) ⟨551183, by rfl⟩ : syracuseStep 2939645 = 1102367) (by norm_num)
theorem B1959763 : Blo 1959435 1959763 := bstep (se 1 (by rfl) ⟨1469822, by rfl⟩ : syracuseStep 1959763 = 2939645) B2939645
theorem B4409477 : Blo 1959435 4409477 := bbase (se 4 (by rfl) ⟨413388, by rfl⟩ : syracuseStep 4409477 = 826777) (by norm_num)
theorem B2939651 : Blo 1959435 2939651 := bstep (se 1 (by rfl) ⟨2204738, by rfl⟩ : syracuseStep 2939651 = 4409477) B4409477
theorem B1959767 : Blo 1959435 1959767 := bstep (se 1 (by rfl) ⟨1469825, by rfl⟩ : syracuseStep 1959767 = 2939651) B2939651
theorem B3771269 : Blo 1959435 3771269 := bbase (se 4 (by rfl) ⟨353556, by rfl⟩ : syracuseStep 3771269 = 707113) (by norm_num)
theorem B2514179 : Blo 1959435 2514179 := bstep (se 1 (by rfl) ⟨1885634, by rfl⟩ : syracuseStep 2514179 = 3771269) B3771269
theorem B6704477 : Blo 1959435 6704477 := bstep (se 3 (by rfl) ⟨1257089, by rfl⟩ : syracuseStep 6704477 = 2514179) B2514179
theorem B4469651 : Blo 1959435 4469651 := bstep (se 1 (by rfl) ⟨3352238, by rfl⟩ : syracuseStep 4469651 = 6704477) B6704477
theorem B2979767 : Blo 1959435 2979767 := bstep (se 1 (by rfl) ⟨2234825, by rfl⟩ : syracuseStep 2979767 = 4469651) B4469651
theorem B7946045 : Blo 1959435 7946045 := bstep (se 3 (by rfl) ⟨1489883, by rfl⟩ : syracuseStep 7946045 = 2979767) B2979767
theorem B5297363 : Blo 1959435 5297363 := bstep (se 1 (by rfl) ⟨3973022, by rfl⟩ : syracuseStep 5297363 = 7946045) B7946045
theorem B3531575 : Blo 1959435 3531575 := bstep (se 1 (by rfl) ⟨2648681, by rfl⟩ : syracuseStep 3531575 = 5297363) B5297363
theorem B2354383 : Blo 1959435 2354383 := bstep (se 1 (by rfl) ⟨1765787, by rfl⟩ : syracuseStep 2354383 = 3531575) B3531575
theorem B3139177 : Blo 1959435 3139177 := bstep (se 2 (by rfl) ⟨1177191, by rfl⟩ : syracuseStep 3139177 = 2354383) B2354383
theorem B4185569 : Blo 1959435 4185569 := bstep (se 2 (by rfl) ⟨1569588, by rfl⟩ : syracuseStep 4185569 = 3139177) B3139177
theorem B2790379 : Blo 1959435 2790379 := bstep (se 1 (by rfl) ⟨2092784, by rfl⟩ : syracuseStep 2790379 = 4185569) B4185569
theorem B3720505 : Blo 1959435 3720505 := bstep (se 2 (by rfl) ⟨1395189, by rfl⟩ : syracuseStep 3720505 = 2790379) B2790379
theorem B4960673 : Blo 1959435 4960673 := bstep (se 2 (by rfl) ⟨1860252, by rfl⟩ : syracuseStep 4960673 = 3720505) B3720505
theorem B3307115 : Blo 1959435 3307115 := bstep (se 1 (by rfl) ⟨2480336, by rfl⟩ : syracuseStep 3307115 = 4960673) B4960673
theorem B2204743 : Blo 1959435 2204743 := bstep (se 1 (by rfl) ⟨1653557, by rfl⟩ : syracuseStep 2204743 = 3307115) B3307115
theorem B2939657 : Blo 1959435 2939657 := bstep (se 2 (by rfl) ⟨1102371, by rfl⟩ : syracuseStep 2939657 = 2204743) B2204743
theorem B1959771 : Blo 1959435 1959771 := bstep (se 1 (by rfl) ⟨1469828, by rfl⟩ : syracuseStep 1959771 = 2939657) B2939657
theorem B9921365 : Blo 1959435 9921365 := bbase (se 9 (by rfl) ⟨29066, by rfl⟩ : syracuseStep 9921365 = 58133) (by norm_num)
theorem B6614243 : Blo 1959435 6614243 := bstep (se 1 (by rfl) ⟨4960682, by rfl⟩ : syracuseStep 6614243 = 9921365) B9921365
theorem B4409495 : Blo 1959435 4409495 := bstep (se 1 (by rfl) ⟨3307121, by rfl⟩ : syracuseStep 4409495 = 6614243) B6614243
theorem B2939663 : Blo 1959435 2939663 := bstep (se 1 (by rfl) ⟨2204747, by rfl⟩ : syracuseStep 2939663 = 4409495) B4409495
theorem B1959775 : Blo 1959435 1959775 := bstep (se 1 (by rfl) ⟨1469831, by rfl⟩ : syracuseStep 1959775 = 2939663) B2939663
theorem B2939669 : Blo 1959435 2939669 := bbase (se 6 (by rfl) ⟨68898, by rfl⟩ : syracuseStep 2939669 = 137797) (by norm_num)
theorem B1959779 : Blo 1959435 1959779 := bstep (se 1 (by rfl) ⟨1469834, by rfl⟩ : syracuseStep 1959779 = 2939669) B2939669
theorem B4242701 : Blo 1959435 4242701 := bbase (se 3 (by rfl) ⟨795506, by rfl⟩ : syracuseStep 4242701 = 1591013) (by norm_num)
theorem B2828467 : Blo 1959435 2828467 := bstep (se 1 (by rfl) ⟨2121350, by rfl⟩ : syracuseStep 2828467 = 4242701) B4242701
theorem B3771289 : Blo 1959435 3771289 := bstep (se 2 (by rfl) ⟨1414233, by rfl⟩ : syracuseStep 3771289 = 2828467) B2828467
theorem B5028385 : Blo 1959435 5028385 := bstep (se 2 (by rfl) ⟨1885644, by rfl⟩ : syracuseStep 5028385 = 3771289) B3771289
theorem B6704513 : Blo 1959435 6704513 := bstep (se 2 (by rfl) ⟨2514192, by rfl⟩ : syracuseStep 6704513 = 5028385) B5028385
theorem B4469675 : Blo 1959435 4469675 := bstep (se 1 (by rfl) ⟨3352256, by rfl⟩ : syracuseStep 4469675 = 6704513) B6704513
theorem B11919133 : Blo 1959435 11919133 := bstep (se 3 (by rfl) ⟨2234837, by rfl⟩ : syracuseStep 11919133 = 4469675) B4469675
theorem B63568709 : Blo 1959435 63568709 := bstep (se 4 (by rfl) ⟨5959566, by rfl⟩ : syracuseStep 63568709 = 11919133) B11919133
theorem B42379139 : Blo 1959435 42379139 := bstep (se 1 (by rfl) ⟨31784354, by rfl⟩ : syracuseStep 42379139 = 63568709) B63568709
theorem B28252759 : Blo 1959435 28252759 := bstep (se 1 (by rfl) ⟨21189569, by rfl⟩ : syracuseStep 28252759 = 42379139) B42379139
theorem B37670345 : Blo 1959435 37670345 := bstep (se 2 (by rfl) ⟨14126379, by rfl⟩ : syracuseStep 37670345 = 28252759) B28252759
theorem B25113563 : Blo 1959435 25113563 := bstep (se 1 (by rfl) ⟨18835172, by rfl⟩ : syracuseStep 25113563 = 37670345) B37670345
theorem B16742375 : Blo 1959435 16742375 := bstep (se 1 (by rfl) ⟨12556781, by rfl⟩ : syracuseStep 16742375 = 25113563) B25113563
theorem B11161583 : Blo 1959435 11161583 := bstep (se 1 (by rfl) ⟨8371187, by rfl⟩ : syracuseStep 11161583 = 16742375) B16742375
theorem B7441055 : Blo 1959435 7441055 := bstep (se 1 (by rfl) ⟨5580791, by rfl⟩ : syracuseStep 7441055 = 11161583) B11161583
theorem B4960703 : Blo 1959435 4960703 := bstep (se 1 (by rfl) ⟨3720527, by rfl⟩ : syracuseStep 4960703 = 7441055) B7441055
theorem B3307135 : Blo 1959435 3307135 := bstep (se 1 (by rfl) ⟨2480351, by rfl⟩ : syracuseStep 3307135 = 4960703) B4960703
theorem B4409513 : Blo 1959435 4409513 := bstep (se 2 (by rfl) ⟨1653567, by rfl⟩ : syracuseStep 4409513 = 3307135) B3307135
theorem B2939675 : Blo 1959435 2939675 := bstep (se 1 (by rfl) ⟨2204756, by rfl⟩ : syracuseStep 2939675 = 4409513) B4409513
theorem B1959783 : Blo 1959435 1959783 := bstep (se 1 (by rfl) ⟨1469837, by rfl⟩ : syracuseStep 1959783 = 2939675) B2939675
theorem B2204761 : Blo 1959435 2204761 := bbase (se 2 (by rfl) ⟨826785, by rfl⟩ : syracuseStep 2204761 = 1653571) (by norm_num)
theorem B2939681 : Blo 1959435 2939681 := bstep (se 2 (by rfl) ⟨1102380, by rfl⟩ : syracuseStep 2939681 = 2204761) B2204761
theorem B1959787 : Blo 1959435 1959787 := bstep (se 1 (by rfl) ⟨1469840, by rfl⟩ : syracuseStep 1959787 = 2939681) B2939681
theorem B4708813 : Blo 1959435 4708813 := bbase (se 3 (by rfl) ⟨882902, by rfl⟩ : syracuseStep 4708813 = 1765805) (by norm_num)
theorem B6278417 : Blo 1959435 6278417 := bstep (se 2 (by rfl) ⟨2354406, by rfl⟩ : syracuseStep 6278417 = 4708813) B4708813
theorem B4185611 : Blo 1959435 4185611 := bstep (se 1 (by rfl) ⟨3139208, by rfl⟩ : syracuseStep 4185611 = 6278417) B6278417
theorem B2790407 : Blo 1959435 2790407 := bstep (se 1 (by rfl) ⟨2092805, by rfl⟩ : syracuseStep 2790407 = 4185611) B4185611
theorem B7441085 : Blo 1959435 7441085 := bstep (se 3 (by rfl) ⟨1395203, by rfl⟩ : syracuseStep 7441085 = 2790407) B2790407
theorem B4960723 : Blo 1959435 4960723 := bstep (se 1 (by rfl) ⟨3720542, by rfl⟩ : syracuseStep 4960723 = 7441085) B7441085
theorem B6614297 : Blo 1959435 6614297 := bstep (se 2 (by rfl) ⟨2480361, by rfl⟩ : syracuseStep 6614297 = 4960723) B4960723
theorem B4409531 : Blo 1959435 4409531 := bstep (se 1 (by rfl) ⟨3307148, by rfl⟩ : syracuseStep 4409531 = 6614297) B6614297
theorem B2939687 : Blo 1959435 2939687 := bstep (se 1 (by rfl) ⟨2204765, by rfl⟩ : syracuseStep 2939687 = 4409531) B4409531
theorem B1959791 : Blo 1959435 1959791 := bstep (se 1 (by rfl) ⟨1469843, by rfl⟩ : syracuseStep 1959791 = 2939687) B2939687
theorem B2939693 : Blo 1959435 2939693 := bbase (se 3 (by rfl) ⟨551192, by rfl⟩ : syracuseStep 2939693 = 1102385) (by norm_num)
theorem B1959795 : Blo 1959435 1959795 := bstep (se 1 (by rfl) ⟨1469846, by rfl⟩ : syracuseStep 1959795 = 2939693) B2939693
theorem B4409549 : Blo 1959435 4409549 := bbase (se 3 (by rfl) ⟨826790, by rfl⟩ : syracuseStep 4409549 = 1653581) (by norm_num)
theorem B2939699 : Blo 1959435 2939699 := bstep (se 1 (by rfl) ⟨2204774, by rfl⟩ : syracuseStep 2939699 = 4409549) B4409549
theorem B1959799 : Blo 1959435 1959799 := bstep (se 1 (by rfl) ⟨1469849, by rfl⟩ : syracuseStep 1959799 = 2939699) B2939699
theorem B2480377 : Blo 1959435 2480377 := bbase (se 2 (by rfl) ⟨930141, by rfl⟩ : syracuseStep 2480377 = 1860283) (by norm_num)
theorem B3307169 : Blo 1959435 3307169 := bstep (se 2 (by rfl) ⟨1240188, by rfl⟩ : syracuseStep 3307169 = 2480377) B2480377
theorem B2204779 : Blo 1959435 2204779 := bstep (se 1 (by rfl) ⟨1653584, by rfl⟩ : syracuseStep 2204779 = 3307169) B3307169
theorem B2939705 : Blo 1959435 2939705 := bstep (se 2 (by rfl) ⟨1102389, by rfl⟩ : syracuseStep 2939705 = 2204779) B2204779
theorem B1959803 : Blo 1959435 1959803 := bstep (se 1 (by rfl) ⟨1469852, by rfl⟩ : syracuseStep 1959803 = 2939705) B2939705
theorem B9417701 : Blo 1959435 9417701 := bbase (se 4 (by rfl) ⟨882909, by rfl⟩ : syracuseStep 9417701 = 1765819) (by norm_num)
theorem B6278467 : Blo 1959435 6278467 := bstep (se 1 (by rfl) ⟨4708850, by rfl⟩ : syracuseStep 6278467 = 9417701) B9417701
theorem B8371289 : Blo 1959435 8371289 := bstep (se 2 (by rfl) ⟨3139233, by rfl⟩ : syracuseStep 8371289 = 6278467) B6278467
theorem B22323437 : Blo 1959435 22323437 := bstep (se 3 (by rfl) ⟨4185644, by rfl⟩ : syracuseStep 22323437 = 8371289) B8371289
theorem B14882291 : Blo 1959435 14882291 := bstep (se 1 (by rfl) ⟨11161718, by rfl⟩ : syracuseStep 14882291 = 22323437) B22323437
theorem B9921527 : Blo 1959435 9921527 := bstep (se 1 (by rfl) ⟨7441145, by rfl⟩ : syracuseStep 9921527 = 14882291) B14882291
theorem B6614351 : Blo 1959435 6614351 := bstep (se 1 (by rfl) ⟨4960763, by rfl⟩ : syracuseStep 6614351 = 9921527) B9921527
theorem B4409567 : Blo 1959435 4409567 := bstep (se 1 (by rfl) ⟨3307175, by rfl⟩ : syracuseStep 4409567 = 6614351) B6614351
theorem B2939711 : Blo 1959435 2939711 := bstep (se 1 (by rfl) ⟨2204783, by rfl⟩ : syracuseStep 2939711 = 4409567) B4409567
theorem B1959807 : Blo 1959435 1959807 := bstep (se 1 (by rfl) ⟨1469855, by rfl⟩ : syracuseStep 1959807 = 2939711) B2939711
theorem B2939717 : Blo 1959435 2939717 := bbase (se 4 (by rfl) ⟨275598, by rfl⟩ : syracuseStep 2939717 = 551197) (by norm_num)
theorem B1959811 : Blo 1959435 1959811 := bstep (se 1 (by rfl) ⟨1469858, by rfl⟩ : syracuseStep 1959811 = 2939717) B2939717
theorem B3307189 : Blo 1959435 3307189 := bbase (se 5 (by rfl) ⟨155024, by rfl⟩ : syracuseStep 3307189 = 310049) (by norm_num)
theorem B4409585 : Blo 1959435 4409585 := bstep (se 2 (by rfl) ⟨1653594, by rfl⟩ : syracuseStep 4409585 = 3307189) B3307189
theorem B2939723 : Blo 1959435 2939723 := bstep (se 1 (by rfl) ⟨2204792, by rfl⟩ : syracuseStep 2939723 = 4409585) B4409585
theorem B1959815 : Blo 1959435 1959815 := bstep (se 1 (by rfl) ⟨1469861, by rfl⟩ : syracuseStep 1959815 = 2939723) B2939723
theorem B2204797 : Blo 1959435 2204797 := bbase (se 3 (by rfl) ⟨413399, by rfl⟩ : syracuseStep 2204797 = 826799) (by norm_num)
theorem B2939729 : Blo 1959435 2939729 := bstep (se 2 (by rfl) ⟨1102398, by rfl⟩ : syracuseStep 2939729 = 2204797) B2204797
theorem B1959819 : Blo 1959435 1959819 := bstep (se 1 (by rfl) ⟨1469864, by rfl⟩ : syracuseStep 1959819 = 2939729) B2939729
theorem B6614405 : Blo 1959435 6614405 := bbase (se 4 (by rfl) ⟨620100, by rfl⟩ : syracuseStep 6614405 = 1240201) (by norm_num)
theorem B4409603 : Blo 1959435 4409603 := bstep (se 1 (by rfl) ⟨3307202, by rfl⟩ : syracuseStep 4409603 = 6614405) B6614405
theorem B2939735 : Blo 1959435 2939735 := bstep (se 1 (by rfl) ⟨2204801, by rfl⟩ : syracuseStep 2939735 = 4409603) B4409603
theorem B1959823 : Blo 1959435 1959823 := bstep (se 1 (by rfl) ⟨1469867, by rfl⟩ : syracuseStep 1959823 = 2939735) B2939735
theorem B2939741 : Blo 1959435 2939741 := bbase (se 3 (by rfl) ⟨551201, by rfl⟩ : syracuseStep 2939741 = 1102403) (by norm_num)
theorem B1959827 : Blo 1959435 1959827 := bstep (se 1 (by rfl) ⟨1469870, by rfl⟩ : syracuseStep 1959827 = 2939741) B2939741
theorem B4409621 : Blo 1959435 4409621 := bbase (se 6 (by rfl) ⟨103350, by rfl⟩ : syracuseStep 4409621 = 206701) (by norm_num)
theorem B2939747 : Blo 1959435 2939747 := bstep (se 1 (by rfl) ⟨2204810, by rfl⟩ : syracuseStep 2939747 = 4409621) B4409621
theorem B1959831 : Blo 1959435 1959831 := bstep (se 1 (by rfl) ⟨1469873, by rfl⟩ : syracuseStep 1959831 = 2939747) B2939747
theorem B7441253 : Blo 1959435 7441253 := bbase (se 4 (by rfl) ⟨697617, by rfl⟩ : syracuseStep 7441253 = 1395235) (by norm_num)
theorem B4960835 : Blo 1959435 4960835 := bstep (se 1 (by rfl) ⟨3720626, by rfl⟩ : syracuseStep 4960835 = 7441253) B7441253
theorem B3307223 : Blo 1959435 3307223 := bstep (se 1 (by rfl) ⟨2480417, by rfl⟩ : syracuseStep 3307223 = 4960835) B4960835
theorem B2204815 : Blo 1959435 2204815 := bstep (se 1 (by rfl) ⟨1653611, by rfl⟩ : syracuseStep 2204815 = 3307223) B3307223
theorem B2939753 : Blo 1959435 2939753 := bstep (se 2 (by rfl) ⟨1102407, by rfl⟩ : syracuseStep 2939753 = 2204815) B2204815
theorem B1959835 : Blo 1959435 1959835 := bstep (se 1 (by rfl) ⟨1469876, by rfl⟩ : syracuseStep 1959835 = 2939753) B2939753
theorem B3139285 : Blo 1959435 3139285 := bbase (se 7 (by rfl) ⟨36788, by rfl⟩ : syracuseStep 3139285 = 73577) (by norm_num)
theorem B4185713 : Blo 1959435 4185713 := bstep (se 2 (by rfl) ⟨1569642, by rfl⟩ : syracuseStep 4185713 = 3139285) B3139285
theorem B11161901 : Blo 1959435 11161901 := bstep (se 3 (by rfl) ⟨2092856, by rfl⟩ : syracuseStep 11161901 = 4185713) B4185713
theorem B7441267 : Blo 1959435 7441267 := bstep (se 1 (by rfl) ⟨5580950, by rfl⟩ : syracuseStep 7441267 = 11161901) B11161901
theorem B9921689 : Blo 1959435 9921689 := bstep (se 2 (by rfl) ⟨3720633, by rfl⟩ : syracuseStep 9921689 = 7441267) B7441267
theorem B6614459 : Blo 1959435 6614459 := bstep (se 1 (by rfl) ⟨4960844, by rfl⟩ : syracuseStep 6614459 = 9921689) B9921689
theorem B4409639 : Blo 1959435 4409639 := bstep (se 1 (by rfl) ⟨3307229, by rfl⟩ : syracuseStep 4409639 = 6614459) B6614459
theorem B2939759 : Blo 1959435 2939759 := bstep (se 1 (by rfl) ⟨2204819, by rfl⟩ : syracuseStep 2939759 = 4409639) B4409639
theorem B1959839 : Blo 1959435 1959839 := bstep (se 1 (by rfl) ⟨1469879, by rfl⟩ : syracuseStep 1959839 = 2939759) B2939759
theorem B2939765 : Blo 1959435 2939765 := bbase (se 5 (by rfl) ⟨137801, by rfl⟩ : syracuseStep 2939765 = 275603) (by norm_num)
theorem B1959843 : Blo 1959435 1959843 := bstep (se 1 (by rfl) ⟨1469882, by rfl⟩ : syracuseStep 1959843 = 2939765) B2939765
theorem B6278597 : Blo 1959435 6278597 := bbase (se 4 (by rfl) ⟨588618, by rfl⟩ : syracuseStep 6278597 = 1177237) (by norm_num)
theorem B4185731 : Blo 1959435 4185731 := bstep (se 1 (by rfl) ⟨3139298, by rfl⟩ : syracuseStep 4185731 = 6278597) B6278597
theorem B2790487 : Blo 1959435 2790487 := bstep (se 1 (by rfl) ⟨2092865, by rfl⟩ : syracuseStep 2790487 = 4185731) B4185731
theorem B3720649 : Blo 1959435 3720649 := bstep (se 2 (by rfl) ⟨1395243, by rfl⟩ : syracuseStep 3720649 = 2790487) B2790487
theorem B4960865 : Blo 1959435 4960865 := bstep (se 2 (by rfl) ⟨1860324, by rfl⟩ : syracuseStep 4960865 = 3720649) B3720649
theorem B3307243 : Blo 1959435 3307243 := bstep (se 1 (by rfl) ⟨2480432, by rfl⟩ : syracuseStep 3307243 = 4960865) B4960865
theorem B4409657 : Blo 1959435 4409657 := bstep (se 2 (by rfl) ⟨1653621, by rfl⟩ : syracuseStep 4409657 = 3307243) B3307243
theorem B2939771 : Blo 1959435 2939771 := bstep (se 1 (by rfl) ⟨2204828, by rfl⟩ : syracuseStep 2939771 = 4409657) B4409657
theorem B1959847 : Blo 1959435 1959847 := bstep (se 1 (by rfl) ⟨1469885, by rfl⟩ : syracuseStep 1959847 = 2939771) B2939771
theorem B2204833 : Blo 1959435 2204833 := bbase (se 2 (by rfl) ⟨826812, by rfl⟩ : syracuseStep 2204833 = 1653625) (by norm_num)
theorem B2939777 : Blo 1959435 2939777 := bstep (se 2 (by rfl) ⟨1102416, by rfl⟩ : syracuseStep 2939777 = 2204833) B2204833
theorem B1959851 : Blo 1959435 1959851 := bstep (se 1 (by rfl) ⟨1469888, by rfl⟩ : syracuseStep 1959851 = 2939777) B2939777
theorem B4960885 : Blo 1959435 4960885 := bbase (se 5 (by rfl) ⟨232541, by rfl⟩ : syracuseStep 4960885 = 465083) (by norm_num)
theorem B6614513 : Blo 1959435 6614513 := bstep (se 2 (by rfl) ⟨2480442, by rfl⟩ : syracuseStep 6614513 = 4960885) B4960885
theorem B4409675 : Blo 1959435 4409675 := bstep (se 1 (by rfl) ⟨3307256, by rfl⟩ : syracuseStep 4409675 = 6614513) B6614513
theorem B2939783 : Blo 1959435 2939783 := bstep (se 1 (by rfl) ⟨2204837, by rfl⟩ : syracuseStep 2939783 = 4409675) B4409675
theorem B1959855 : Blo 1959435 1959855 := bstep (se 1 (by rfl) ⟨1469891, by rfl⟩ : syracuseStep 1959855 = 2939783) B2939783
theorem B2939789 : Blo 1959435 2939789 := bbase (se 3 (by rfl) ⟨551210, by rfl⟩ : syracuseStep 2939789 = 1102421) (by norm_num)
theorem B1959859 : Blo 1959435 1959859 := bstep (se 1 (by rfl) ⟨1469894, by rfl⟩ : syracuseStep 1959859 = 2939789) B2939789
theorem B4409693 : Blo 1959435 4409693 := bbase (se 3 (by rfl) ⟨826817, by rfl⟩ : syracuseStep 4409693 = 1653635) (by norm_num)
theorem B2939795 : Blo 1959435 2939795 := bstep (se 1 (by rfl) ⟨2204846, by rfl⟩ : syracuseStep 2939795 = 4409693) B4409693
theorem B1959863 : Blo 1959435 1959863 := bstep (se 1 (by rfl) ⟨1469897, by rfl⟩ : syracuseStep 1959863 = 2939795) B2939795
theorem B3307277 : Blo 1959435 3307277 := bbase (se 3 (by rfl) ⟨620114, by rfl⟩ : syracuseStep 3307277 = 1240229) (by norm_num)
theorem B2204851 : Blo 1959435 2204851 := bstep (se 1 (by rfl) ⟨1653638, by rfl⟩ : syracuseStep 2204851 = 3307277) B3307277
theorem B2939801 : Blo 1959435 2939801 := bstep (se 2 (by rfl) ⟨1102425, by rfl⟩ : syracuseStep 2939801 = 2204851) B2204851
theorem B1959867 : Blo 1959435 1959867 := bstep (se 1 (by rfl) ⟨1469900, by rfl⟩ : syracuseStep 1959867 = 2939801) B2939801
theorem B16743125 : Blo 1959435 16743125 := bbase (se 7 (by rfl) ⟨196208, by rfl⟩ : syracuseStep 16743125 = 392417) (by norm_num)
theorem B11162083 : Blo 1959435 11162083 := bstep (se 1 (by rfl) ⟨8371562, by rfl⟩ : syracuseStep 11162083 = 16743125) B16743125
theorem B14882777 : Blo 1959435 14882777 := bstep (se 2 (by rfl) ⟨5581041, by rfl⟩ : syracuseStep 14882777 = 11162083) B11162083
theorem B9921851 : Blo 1959435 9921851 := bstep (se 1 (by rfl) ⟨7441388, by rfl⟩ : syracuseStep 9921851 = 14882777) B14882777
theorem B6614567 : Blo 1959435 6614567 := bstep (se 1 (by rfl) ⟨4960925, by rfl⟩ : syracuseStep 6614567 = 9921851) B9921851
theorem B4409711 : Blo 1959435 4409711 := bstep (se 1 (by rfl) ⟨3307283, by rfl⟩ : syracuseStep 4409711 = 6614567) B6614567
theorem B2939807 : Blo 1959435 2939807 := bstep (se 1 (by rfl) ⟨2204855, by rfl⟩ : syracuseStep 2939807 = 4409711) B4409711
theorem B1959871 : Blo 1959435 1959871 := bstep (se 1 (by rfl) ⟨1469903, by rfl⟩ : syracuseStep 1959871 = 2939807) B2939807
theorem B2939813 : Blo 1959435 2939813 := bbase (se 4 (by rfl) ⟨275607, by rfl⟩ : syracuseStep 2939813 = 551215) (by norm_num)
theorem B1959875 : Blo 1959435 1959875 := bstep (se 1 (by rfl) ⟨1469906, by rfl⟩ : syracuseStep 1959875 = 2939813) B2939813
theorem B2480473 : Blo 1959435 2480473 := bbase (se 2 (by rfl) ⟨930177, by rfl⟩ : syracuseStep 2480473 = 1860355) (by norm_num)
theorem B3307297 : Blo 1959435 3307297 := bstep (se 2 (by rfl) ⟨1240236, by rfl⟩ : syracuseStep 3307297 = 2480473) B2480473
theorem B4409729 : Blo 1959435 4409729 := bstep (se 2 (by rfl) ⟨1653648, by rfl⟩ : syracuseStep 4409729 = 3307297) B3307297
theorem B2939819 : Blo 1959435 2939819 := bstep (se 1 (by rfl) ⟨2204864, by rfl⟩ : syracuseStep 2939819 = 4409729) B4409729
theorem B1959879 : Blo 1959435 1959879 := bstep (se 1 (by rfl) ⟨1469909, by rfl⟩ : syracuseStep 1959879 = 2939819) B2939819
theorem B2204869 : Blo 1959435 2204869 := bbase (se 4 (by rfl) ⟨206706, by rfl⟩ : syracuseStep 2204869 = 413413) (by norm_num)
theorem B2939825 : Blo 1959435 2939825 := bstep (se 2 (by rfl) ⟨1102434, by rfl⟩ : syracuseStep 2939825 = 2204869) B2204869
theorem B1959883 : Blo 1959435 1959883 := bstep (se 1 (by rfl) ⟨1469912, by rfl⟩ : syracuseStep 1959883 = 2939825) B2939825
theorem B3720725 : Blo 1959435 3720725 := bbase (se 6 (by rfl) ⟨87204, by rfl⟩ : syracuseStep 3720725 = 174409) (by norm_num)
theorem B2480483 : Blo 1959435 2480483 := bstep (se 1 (by rfl) ⟨1860362, by rfl⟩ : syracuseStep 2480483 = 3720725) B3720725
theorem B6614621 : Blo 1959435 6614621 := bstep (se 3 (by rfl) ⟨1240241, by rfl⟩ : syracuseStep 6614621 = 2480483) B2480483
theorem B4409747 : Blo 1959435 4409747 := bstep (se 1 (by rfl) ⟨3307310, by rfl⟩ : syracuseStep 4409747 = 6614621) B6614621
theorem B2939831 : Blo 1959435 2939831 := bstep (se 1 (by rfl) ⟨2204873, by rfl⟩ : syracuseStep 2939831 = 4409747) B4409747
theorem B1959887 : Blo 1959435 1959887 := bstep (se 1 (by rfl) ⟨1469915, by rfl⟩ : syracuseStep 1959887 = 2939831) B2939831
theorem B2939837 : Blo 1959435 2939837 := bbase (se 3 (by rfl) ⟨551219, by rfl⟩ : syracuseStep 2939837 = 1102439) (by norm_num)
theorem B1959891 : Blo 1959435 1959891 := bstep (se 1 (by rfl) ⟨1469918, by rfl⟩ : syracuseStep 1959891 = 2939837) B2939837
theorem B4409765 : Blo 1959435 4409765 := bbase (se 4 (by rfl) ⟨413415, by rfl⟩ : syracuseStep 4409765 = 826831) (by norm_num)
theorem B2939843 : Blo 1959435 2939843 := bstep (se 1 (by rfl) ⟨2204882, by rfl⟩ : syracuseStep 2939843 = 4409765) B4409765
theorem B1959895 : Blo 1959435 1959895 := bstep (se 1 (by rfl) ⟨1469921, by rfl⟩ : syracuseStep 1959895 = 2939843) B2939843
theorem B4960997 : Blo 1959435 4960997 := bbase (se 4 (by rfl) ⟨465093, by rfl⟩ : syracuseStep 4960997 = 930187) (by norm_num)
theorem B3307331 : Blo 1959435 3307331 := bstep (se 1 (by rfl) ⟨2480498, by rfl⟩ : syracuseStep 3307331 = 4960997) B4960997
theorem B2204887 : Blo 1959435 2204887 := bstep (se 1 (by rfl) ⟨1653665, by rfl⟩ : syracuseStep 2204887 = 3307331) B3307331
theorem B2939849 : Blo 1959435 2939849 := bstep (se 2 (by rfl) ⟨1102443, by rfl⟩ : syracuseStep 2939849 = 2204887) B2204887
theorem B1959899 : Blo 1959435 1959899 := bstep (se 1 (by rfl) ⟨1469924, by rfl⟩ : syracuseStep 1959899 = 2939849) B2939849
theorem B2092925 : Blo 1959435 2092925 := bbase (se 3 (by rfl) ⟨392423, by rfl⟩ : syracuseStep 2092925 = 784847) (by norm_num)
theorem B5581133 : Blo 1959435 5581133 := bstep (se 3 (by rfl) ⟨1046462, by rfl⟩ : syracuseStep 5581133 = 2092925) B2092925
theorem B3720755 : Blo 1959435 3720755 := bstep (se 1 (by rfl) ⟨2790566, by rfl⟩ : syracuseStep 3720755 = 5581133) B5581133
theorem B9922013 : Blo 1959435 9922013 := bstep (se 3 (by rfl) ⟨1860377, by rfl⟩ : syracuseStep 9922013 = 3720755) B3720755
theorem B6614675 : Blo 1959435 6614675 := bstep (se 1 (by rfl) ⟨4961006, by rfl⟩ : syracuseStep 6614675 = 9922013) B9922013
theorem B4409783 : Blo 1959435 4409783 := bstep (se 1 (by rfl) ⟨3307337, by rfl⟩ : syracuseStep 4409783 = 6614675) B6614675
theorem B2939855 : Blo 1959435 2939855 := bstep (se 1 (by rfl) ⟨2204891, by rfl⟩ : syracuseStep 2939855 = 4409783) B4409783
theorem B1959903 : Blo 1959435 1959903 := bstep (se 1 (by rfl) ⟨1469927, by rfl⟩ : syracuseStep 1959903 = 2939855) B2939855
theorem B2939861 : Blo 1959435 2939861 := bbase (se 7 (by rfl) ⟨34451, by rfl⟩ : syracuseStep 2939861 = 68903) (by norm_num)
theorem B1959907 : Blo 1959435 1959907 := bstep (se 1 (by rfl) ⟨1469930, by rfl⟩ : syracuseStep 1959907 = 2939861) B2939861
theorem B7441541 : Blo 1959435 7441541 := bbase (se 4 (by rfl) ⟨697644, by rfl⟩ : syracuseStep 7441541 = 1395289) (by norm_num)
theorem B4961027 : Blo 1959435 4961027 := bstep (se 1 (by rfl) ⟨3720770, by rfl⟩ : syracuseStep 4961027 = 7441541) B7441541
theorem B3307351 : Blo 1959435 3307351 := bstep (se 1 (by rfl) ⟨2480513, by rfl⟩ : syracuseStep 3307351 = 4961027) B4961027
theorem B4409801 : Blo 1959435 4409801 := bstep (se 2 (by rfl) ⟨1653675, by rfl⟩ : syracuseStep 4409801 = 3307351) B3307351
theorem B2939867 : Blo 1959435 2939867 := bstep (se 1 (by rfl) ⟨2204900, by rfl⟩ : syracuseStep 2939867 = 4409801) B4409801
theorem B1959911 : Blo 1959435 1959911 := bstep (se 1 (by rfl) ⟨1469933, by rfl⟩ : syracuseStep 1959911 = 2939867) B2939867
theorem B2204905 : Blo 1959435 2204905 := bbase (se 2 (by rfl) ⟨826839, by rfl⟩ : syracuseStep 2204905 = 1653679) (by norm_num)
theorem B2939873 : Blo 1959435 2939873 := bstep (se 2 (by rfl) ⟨1102452, by rfl⟩ : syracuseStep 2939873 = 2204905) B2204905
theorem B1959915 : Blo 1959435 1959915 := bstep (se 1 (by rfl) ⟨1469936, by rfl⟩ : syracuseStep 1959915 = 2939873) B2939873
theorem B11162357 : Blo 1959435 11162357 := bbase (se 5 (by rfl) ⟨523235, by rfl⟩ : syracuseStep 11162357 = 1046471) (by norm_num)
theorem B7441571 : Blo 1959435 7441571 := bstep (se 1 (by rfl) ⟨5581178, by rfl⟩ : syracuseStep 7441571 = 11162357) B11162357
theorem B4961047 : Blo 1959435 4961047 := bstep (se 1 (by rfl) ⟨3720785, by rfl⟩ : syracuseStep 4961047 = 7441571) B7441571
theorem B6614729 : Blo 1959435 6614729 := bstep (se 2 (by rfl) ⟨2480523, by rfl⟩ : syracuseStep 6614729 = 4961047) B4961047
theorem B4409819 : Blo 1959435 4409819 := bstep (se 1 (by rfl) ⟨3307364, by rfl⟩ : syracuseStep 4409819 = 6614729) B6614729
theorem B2939879 : Blo 1959435 2939879 := bstep (se 1 (by rfl) ⟨2204909, by rfl⟩ : syracuseStep 2939879 = 4409819) B4409819
theorem B1959919 : Blo 1959435 1959919 := bstep (se 1 (by rfl) ⟨1469939, by rfl⟩ : syracuseStep 1959919 = 2939879) B2939879
theorem B2939885 : Blo 1959435 2939885 := bbase (se 3 (by rfl) ⟨551228, by rfl⟩ : syracuseStep 2939885 = 1102457) (by norm_num)
theorem B1959923 : Blo 1959435 1959923 := bstep (se 1 (by rfl) ⟨1469942, by rfl⟩ : syracuseStep 1959923 = 2939885) B2939885
theorem B4409837 : Blo 1959435 4409837 := bbase (se 3 (by rfl) ⟨826844, by rfl⟩ : syracuseStep 4409837 = 1653689) (by norm_num)
theorem B2939891 : Blo 1959435 2939891 := bstep (se 1 (by rfl) ⟨2204918, by rfl⟩ : syracuseStep 2939891 = 4409837) B4409837
theorem B1959927 : Blo 1959435 1959927 := bstep (se 1 (by rfl) ⟨1469945, by rfl⟩ : syracuseStep 1959927 = 2939891) B2939891
theorem B7946693 : Blo 1959435 7946693 := bbase (se 4 (by rfl) ⟨745002, by rfl⟩ : syracuseStep 7946693 = 1490005) (by norm_num)
theorem B5297795 : Blo 1959435 5297795 := bstep (se 1 (by rfl) ⟨3973346, by rfl⟩ : syracuseStep 5297795 = 7946693) B7946693
theorem B3531863 : Blo 1959435 3531863 := bstep (se 1 (by rfl) ⟨2648897, by rfl⟩ : syracuseStep 3531863 = 5297795) B5297795
theorem B9418301 : Blo 1959435 9418301 := bstep (se 3 (by rfl) ⟨1765931, by rfl⟩ : syracuseStep 9418301 = 3531863) B3531863
theorem B6278867 : Blo 1959435 6278867 := bstep (se 1 (by rfl) ⟨4709150, by rfl⟩ : syracuseStep 6278867 = 9418301) B9418301
theorem B4185911 : Blo 1959435 4185911 := bstep (se 1 (by rfl) ⟨3139433, by rfl⟩ : syracuseStep 4185911 = 6278867) B6278867
theorem B2790607 : Blo 1959435 2790607 := bstep (se 1 (by rfl) ⟨2092955, by rfl⟩ : syracuseStep 2790607 = 4185911) B4185911
theorem B3720809 : Blo 1959435 3720809 := bstep (se 2 (by rfl) ⟨1395303, by rfl⟩ : syracuseStep 3720809 = 2790607) B2790607
theorem B2480539 : Blo 1959435 2480539 := bstep (se 1 (by rfl) ⟨1860404, by rfl⟩ : syracuseStep 2480539 = 3720809) B3720809
theorem B3307385 : Blo 1959435 3307385 := bstep (se 2 (by rfl) ⟨1240269, by rfl⟩ : syracuseStep 3307385 = 2480539) B2480539
theorem B2204923 : Blo 1959435 2204923 := bstep (se 1 (by rfl) ⟨1653692, by rfl⟩ : syracuseStep 2204923 = 3307385) B3307385
theorem B2939897 : Blo 1959435 2939897 := bstep (se 2 (by rfl) ⟨1102461, by rfl⟩ : syracuseStep 2939897 = 2204923) B2204923
theorem B1959931 : Blo 1959435 1959931 := bstep (se 1 (by rfl) ⟨1469948, by rfl⟩ : syracuseStep 1959931 = 2939897) B2939897
theorem B9185653 : Blo 1959435 9185653 := bbase (se 5 (by rfl) ⟨430577, by rfl⟩ : syracuseStep 9185653 = 861155) (by norm_num)
theorem B12247537 : Blo 1959435 12247537 := bstep (se 2 (by rfl) ⟨4592826, by rfl⟩ : syracuseStep 12247537 = 9185653) B9185653
theorem B16330049 : Blo 1959435 16330049 := bstep (se 2 (by rfl) ⟨6123768, by rfl⟩ : syracuseStep 16330049 = 12247537) B12247537
theorem B10886699 : Blo 1959435 10886699 := bstep (se 1 (by rfl) ⟨8165024, by rfl⟩ : syracuseStep 10886699 = 16330049) B16330049
theorem B7257799 : Blo 1959435 7257799 := bstep (se 1 (by rfl) ⟨5443349, by rfl⟩ : syracuseStep 7257799 = 10886699) B10886699
theorem B9677065 : Blo 1959435 9677065 := bstep (se 2 (by rfl) ⟨3628899, by rfl⟩ : syracuseStep 9677065 = 7257799) B7257799
theorem B12902753 : Blo 1959435 12902753 := bstep (se 2 (by rfl) ⟨4838532, by rfl⟩ : syracuseStep 12902753 = 9677065) B9677065
theorem B8601835 : Blo 1959435 8601835 := bstep (se 1 (by rfl) ⟨6451376, by rfl⟩ : syracuseStep 8601835 = 12902753) B12902753
theorem B11469113 : Blo 1959435 11469113 := bstep (se 2 (by rfl) ⟨4300917, by rfl⟩ : syracuseStep 11469113 = 8601835) B8601835
theorem B7646075 : Blo 1959435 7646075 := bstep (se 1 (by rfl) ⟨5734556, by rfl⟩ : syracuseStep 7646075 = 11469113) B11469113
theorem B5097383 : Blo 1959435 5097383 := bstep (se 1 (by rfl) ⟨3823037, by rfl⟩ : syracuseStep 5097383 = 7646075) B7646075
theorem B3398255 : Blo 1959435 3398255 := bstep (se 1 (by rfl) ⟨2548691, by rfl⟩ : syracuseStep 3398255 = 5097383) B5097383
theorem B144992213 : Blo 1959435 144992213 := bstep (se 7 (by rfl) ⟨1699127, by rfl⟩ : syracuseStep 144992213 = 3398255) B3398255
theorem B96661475 : Blo 1959435 96661475 := bstep (se 1 (by rfl) ⟨72496106, by rfl⟩ : syracuseStep 96661475 = 144992213) B144992213
theorem B64440983 : Blo 1959435 64440983 := bstep (se 1 (by rfl) ⟨48330737, by rfl⟩ : syracuseStep 64440983 = 96661475) B96661475
theorem B42960655 : Blo 1959435 42960655 := bstep (se 1 (by rfl) ⟨32220491, by rfl⟩ : syracuseStep 42960655 = 64440983) B64440983
theorem B229123493 : Blo 1959435 229123493 := bstep (se 4 (by rfl) ⟨21480327, by rfl⟩ : syracuseStep 229123493 = 42960655) B42960655
theorem B152748995 : Blo 1959435 152748995 := bstep (se 1 (by rfl) ⟨114561746, by rfl⟩ : syracuseStep 152748995 = 229123493) B229123493
theorem B407330653 : Blo 1959435 407330653 := bstep (se 3 (by rfl) ⟨76374497, by rfl⟩ : syracuseStep 407330653 = 152748995) B152748995
theorem B543107537 : Blo 1959435 543107537 := bstep (se 2 (by rfl) ⟨203665326, by rfl⟩ : syracuseStep 543107537 = 407330653) B407330653
theorem B362071691 : Blo 1959435 362071691 := bstep (se 1 (by rfl) ⟨271553768, by rfl⟩ : syracuseStep 362071691 = 543107537) B543107537
theorem B241381127 : Blo 1959435 241381127 := bstep (se 1 (by rfl) ⟨181035845, by rfl⟩ : syracuseStep 241381127 = 362071691) B362071691
theorem B160920751 : Blo 1959435 160920751 := bstep (se 1 (by rfl) ⟨120690563, by rfl⟩ : syracuseStep 160920751 = 241381127) B241381127
theorem B214561001 : Blo 1959435 214561001 := bstep (se 2 (by rfl) ⟨80460375, by rfl⟩ : syracuseStep 214561001 = 160920751) B160920751
theorem B143040667 : Blo 1959435 143040667 := bstep (se 1 (by rfl) ⟨107280500, by rfl⟩ : syracuseStep 143040667 = 214561001) B214561001
theorem B190720889 : Blo 1959435 190720889 := bstep (se 2 (by rfl) ⟨71520333, by rfl⟩ : syracuseStep 190720889 = 143040667) B143040667
theorem B127147259 : Blo 1959435 127147259 := bstep (se 1 (by rfl) ⟨95360444, by rfl⟩ : syracuseStep 127147259 = 190720889) B190720889
theorem B84764839 : Blo 1959435 84764839 := bstep (se 1 (by rfl) ⟨63573629, by rfl⟩ : syracuseStep 84764839 = 127147259) B127147259
theorem B113019785 : Blo 1959435 113019785 := bstep (se 2 (by rfl) ⟨42382419, by rfl⟩ : syracuseStep 113019785 = 84764839) B84764839
theorem B75346523 : Blo 1959435 75346523 := bstep (se 1 (by rfl) ⟨56509892, by rfl⟩ : syracuseStep 75346523 = 113019785) B113019785
theorem B50231015 : Blo 1959435 50231015 := bstep (se 1 (by rfl) ⟨37673261, by rfl⟩ : syracuseStep 50231015 = 75346523) B75346523
theorem B33487343 : Blo 1959435 33487343 := bstep (se 1 (by rfl) ⟨25115507, by rfl⟩ : syracuseStep 33487343 = 50231015) B50231015
theorem B22324895 : Blo 1959435 22324895 := bstep (se 1 (by rfl) ⟨16743671, by rfl⟩ : syracuseStep 22324895 = 33487343) B33487343
theorem B14883263 : Blo 1959435 14883263 := bstep (se 1 (by rfl) ⟨11162447, by rfl⟩ : syracuseStep 14883263 = 22324895) B22324895
theorem B9922175 : Blo 1959435 9922175 := bstep (se 1 (by rfl) ⟨7441631, by rfl⟩ : syracuseStep 9922175 = 14883263) B14883263
theorem B6614783 : Blo 1959435 6614783 := bstep (se 1 (by rfl) ⟨4961087, by rfl⟩ : syracuseStep 6614783 = 9922175) B9922175
theorem B4409855 : Blo 1959435 4409855 := bstep (se 1 (by rfl) ⟨3307391, by rfl⟩ : syracuseStep 4409855 = 6614783) B6614783
theorem B2939903 : Blo 1959435 2939903 := bstep (se 1 (by rfl) ⟨2204927, by rfl⟩ : syracuseStep 2939903 = 4409855) B4409855
theorem B1959935 : Blo 1959435 1959935 := bstep (se 1 (by rfl) ⟨1469951, by rfl⟩ : syracuseStep 1959935 = 2939903) B2939903
theorem B2939909 : Blo 1959435 2939909 := bbase (se 4 (by rfl) ⟨275616, by rfl⟩ : syracuseStep 2939909 = 551233) (by norm_num)
theorem B1959939 : Blo 1959435 1959939 := bstep (se 1 (by rfl) ⟨1469954, by rfl⟩ : syracuseStep 1959939 = 2939909) B2939909
theorem B3307405 : Blo 1959435 3307405 := bbase (se 3 (by rfl) ⟨620138, by rfl⟩ : syracuseStep 3307405 = 1240277) (by norm_num)
theorem B4409873 : Blo 1959435 4409873 := bstep (se 2 (by rfl) ⟨1653702, by rfl⟩ : syracuseStep 4409873 = 3307405) B3307405
theorem B2939915 : Blo 1959435 2939915 := bstep (se 1 (by rfl) ⟨2204936, by rfl⟩ : syracuseStep 2939915 = 4409873) B4409873
theorem B1959943 : Blo 1959435 1959943 := bstep (se 1 (by rfl) ⟨1469957, by rfl⟩ : syracuseStep 1959943 = 2939915) B2939915
theorem B2204941 : Blo 1959435 2204941 := bbase (se 3 (by rfl) ⟨413426, by rfl⟩ : syracuseStep 2204941 = 826853) (by norm_num)
theorem B2939921 : Blo 1959435 2939921 := bstep (se 2 (by rfl) ⟨1102470, by rfl⟩ : syracuseStep 2939921 = 2204941) B2204941
theorem B1959947 : Blo 1959435 1959947 := bstep (se 1 (by rfl) ⟨1469960, by rfl⟩ : syracuseStep 1959947 = 2939921) B2939921
theorem B6614837 : Blo 1959435 6614837 := bbase (se 5 (by rfl) ⟨310070, by rfl⟩ : syracuseStep 6614837 = 620141) (by norm_num)
theorem B4409891 : Blo 1959435 4409891 := bstep (se 1 (by rfl) ⟨3307418, by rfl⟩ : syracuseStep 4409891 = 6614837) B6614837
theorem B2939927 : Blo 1959435 2939927 := bstep (se 1 (by rfl) ⟨2204945, by rfl⟩ : syracuseStep 2939927 = 4409891) B4409891
theorem B1959951 : Blo 1959435 1959951 := bstep (se 1 (by rfl) ⟨1469963, by rfl⟩ : syracuseStep 1959951 = 2939927) B2939927
theorem B2939933 : Blo 1959435 2939933 := bbase (se 3 (by rfl) ⟨551237, by rfl⟩ : syracuseStep 2939933 = 1102475) (by norm_num)
theorem B1959955 : Blo 1959435 1959955 := bstep (se 1 (by rfl) ⟨1469966, by rfl⟩ : syracuseStep 1959955 = 2939933) B2939933
theorem B4409909 : Blo 1959435 4409909 := bbase (se 5 (by rfl) ⟨206714, by rfl⟩ : syracuseStep 4409909 = 413429) (by norm_num)
theorem B2939939 : Blo 1959435 2939939 := bstep (se 1 (by rfl) ⟨2204954, by rfl⟩ : syracuseStep 2939939 = 4409909) B4409909
theorem B1959959 : Blo 1959435 1959959 := bstep (se 1 (by rfl) ⟨1469969, by rfl⟩ : syracuseStep 1959959 = 2939939) B2939939
theorem B8371957 : Blo 1959435 8371957 := bbase (se 5 (by rfl) ⟨392435, by rfl⟩ : syracuseStep 8371957 = 784871) (by norm_num)
theorem B11162609 : Blo 1959435 11162609 := bstep (se 2 (by rfl) ⟨4185978, by rfl⟩ : syracuseStep 11162609 = 8371957) B8371957
theorem B7441739 : Blo 1959435 7441739 := bstep (se 1 (by rfl) ⟨5581304, by rfl⟩ : syracuseStep 7441739 = 11162609) B11162609
theorem B4961159 : Blo 1959435 4961159 := bstep (se 1 (by rfl) ⟨3720869, by rfl⟩ : syracuseStep 4961159 = 7441739) B7441739
theorem B3307439 : Blo 1959435 3307439 := bstep (se 1 (by rfl) ⟨2480579, by rfl⟩ : syracuseStep 3307439 = 4961159) B4961159
theorem B2204959 : Blo 1959435 2204959 := bstep (se 1 (by rfl) ⟨1653719, by rfl⟩ : syracuseStep 2204959 = 3307439) B3307439
theorem B2939945 : Blo 1959435 2939945 := bstep (se 2 (by rfl) ⟨1102479, by rfl⟩ : syracuseStep 2939945 = 2204959) B2204959
theorem B1959963 : Blo 1959435 1959963 := bstep (se 1 (by rfl) ⟨1469972, by rfl⟩ : syracuseStep 1959963 = 2939945) B2939945
theorem B8371973 : Blo 1959435 8371973 := bbase (se 4 (by rfl) ⟨784872, by rfl⟩ : syracuseStep 8371973 = 1569745) (by norm_num)
theorem B5581315 : Blo 1959435 5581315 := bstep (se 1 (by rfl) ⟨4185986, by rfl⟩ : syracuseStep 5581315 = 8371973) B8371973
theorem B7441753 : Blo 1959435 7441753 := bstep (se 2 (by rfl) ⟨2790657, by rfl⟩ : syracuseStep 7441753 = 5581315) B5581315
theorem B9922337 : Blo 1959435 9922337 := bstep (se 2 (by rfl) ⟨3720876, by rfl⟩ : syracuseStep 9922337 = 7441753) B7441753
theorem B6614891 : Blo 1959435 6614891 := bstep (se 1 (by rfl) ⟨4961168, by rfl⟩ : syracuseStep 6614891 = 9922337) B9922337
theorem B4409927 : Blo 1959435 4409927 := bstep (se 1 (by rfl) ⟨3307445, by rfl⟩ : syracuseStep 4409927 = 6614891) B6614891
theorem B2939951 : Blo 1959435 2939951 := bstep (se 1 (by rfl) ⟨2204963, by rfl⟩ : syracuseStep 2939951 = 4409927) B4409927
theorem B1959967 : Blo 1959435 1959967 := bstep (se 1 (by rfl) ⟨1469975, by rfl⟩ : syracuseStep 1959967 = 2939951) B2939951
theorem B2939957 : Blo 1959435 2939957 := bbase (se 5 (by rfl) ⟨137810, by rfl⟩ : syracuseStep 2939957 = 275621) (by norm_num)
theorem B1959971 : Blo 1959435 1959971 := bstep (se 1 (by rfl) ⟨1469978, by rfl⟩ : syracuseStep 1959971 = 2939957) B2939957
theorem B4961189 : Blo 1959435 4961189 := bbase (se 4 (by rfl) ⟨465111, by rfl⟩ : syracuseStep 4961189 = 930223) (by norm_num)
theorem B3307459 : Blo 1959435 3307459 := bstep (se 1 (by rfl) ⟨2480594, by rfl⟩ : syracuseStep 3307459 = 4961189) B4961189
theorem B4409945 : Blo 1959435 4409945 := bstep (se 2 (by rfl) ⟨1653729, by rfl⟩ : syracuseStep 4409945 = 3307459) B3307459
theorem B2939963 : Blo 1959435 2939963 := bstep (se 1 (by rfl) ⟨2204972, by rfl⟩ : syracuseStep 2939963 = 4409945) B4409945
theorem B1959975 : Blo 1959435 1959975 := bstep (se 1 (by rfl) ⟨1469981, by rfl⟩ : syracuseStep 1959975 = 2939963) B2939963
theorem B2204977 : Blo 1959435 2204977 := bbase (se 2 (by rfl) ⟨826866, by rfl⟩ : syracuseStep 2204977 = 1653733) (by norm_num)
theorem B2939969 : Blo 1959435 2939969 := bstep (se 2 (by rfl) ⟨1102488, by rfl⟩ : syracuseStep 2939969 = 2204977) B2204977
theorem B1959979 : Blo 1959435 1959979 := bstep (se 1 (by rfl) ⟨1469984, by rfl⟩ : syracuseStep 1959979 = 2939969) B2939969
theorem B4186021 : Blo 1959435 4186021 := bbase (se 4 (by rfl) ⟨392439, by rfl⟩ : syracuseStep 4186021 = 784879) (by norm_num)
theorem B5581361 : Blo 1959435 5581361 := bstep (se 2 (by rfl) ⟨2093010, by rfl⟩ : syracuseStep 5581361 = 4186021) B4186021
theorem B3720907 : Blo 1959435 3720907 := bstep (se 1 (by rfl) ⟨2790680, by rfl⟩ : syracuseStep 3720907 = 5581361) B5581361
theorem B4961209 : Blo 1959435 4961209 := bstep (se 2 (by rfl) ⟨1860453, by rfl⟩ : syracuseStep 4961209 = 3720907) B3720907
theorem B6614945 : Blo 1959435 6614945 := bstep (se 2 (by rfl) ⟨2480604, by rfl⟩ : syracuseStep 6614945 = 4961209) B4961209
theorem B4409963 : Blo 1959435 4409963 := bstep (se 1 (by rfl) ⟨3307472, by rfl⟩ : syracuseStep 4409963 = 6614945) B6614945
theorem B2939975 : Blo 1959435 2939975 := bstep (se 1 (by rfl) ⟨2204981, by rfl⟩ : syracuseStep 2939975 = 4409963) B4409963
theorem B1959983 : Blo 1959435 1959983 := bstep (se 1 (by rfl) ⟨1469987, by rfl⟩ : syracuseStep 1959983 = 2939975) B2939975
theorem B2939981 : Blo 1959435 2939981 := bbase (se 3 (by rfl) ⟨551246, by rfl⟩ : syracuseStep 2939981 = 1102493) (by norm_num)
theorem B1959987 : Blo 1959435 1959987 := bstep (se 1 (by rfl) ⟨1469990, by rfl⟩ : syracuseStep 1959987 = 2939981) B2939981
theorem B4409981 : Blo 1959435 4409981 := bbase (se 3 (by rfl) ⟨826871, by rfl⟩ : syracuseStep 4409981 = 1653743) (by norm_num)
theorem B2939987 : Blo 1959435 2939987 := bstep (se 1 (by rfl) ⟨2204990, by rfl⟩ : syracuseStep 2939987 = 4409981) B4409981
theorem B1959991 : Blo 1959435 1959991 := bstep (se 1 (by rfl) ⟨1469993, by rfl⟩ : syracuseStep 1959991 = 2939987) B2939987
theorem B3307493 : Blo 1959435 3307493 := bbase (se 4 (by rfl) ⟨310077, by rfl⟩ : syracuseStep 3307493 = 620155) (by norm_num)
theorem B2204995 : Blo 1959435 2204995 := bstep (se 1 (by rfl) ⟨1653746, by rfl⟩ : syracuseStep 2204995 = 3307493) B3307493
theorem B2939993 : Blo 1959435 2939993 := bstep (se 2 (by rfl) ⟨1102497, by rfl⟩ : syracuseStep 2939993 = 2204995) B2204995
theorem B1959995 : Blo 1959435 1959995 := bstep (se 1 (by rfl) ⟨1469996, by rfl⟩ : syracuseStep 1959995 = 2939993) B2939993
theorem B5028941 : Blo 1959435 5028941 := bbase (se 3 (by rfl) ⟨942926, by rfl⟩ : syracuseStep 5028941 = 1885853) (by norm_num)
theorem B3352627 : Blo 1959435 3352627 := bstep (se 1 (by rfl) ⟨2514470, by rfl⟩ : syracuseStep 3352627 = 5028941) B5028941
theorem B4470169 : Blo 1959435 4470169 := bstep (se 2 (by rfl) ⟨1676313, by rfl⟩ : syracuseStep 4470169 = 3352627) B3352627
theorem B5960225 : Blo 1959435 5960225 := bstep (se 2 (by rfl) ⟨2235084, by rfl⟩ : syracuseStep 5960225 = 4470169) B4470169
theorem B3973483 : Blo 1959435 3973483 := bstep (se 1 (by rfl) ⟨2980112, by rfl⟩ : syracuseStep 3973483 = 5960225) B5960225
theorem B5297977 : Blo 1959435 5297977 := bstep (se 2 (by rfl) ⟨1986741, by rfl⟩ : syracuseStep 5297977 = 3973483) B3973483
theorem B7063969 : Blo 1959435 7063969 := bstep (se 2 (by rfl) ⟨2648988, by rfl⟩ : syracuseStep 7063969 = 5297977) B5297977
theorem B9418625 : Blo 1959435 9418625 := bstep (se 2 (by rfl) ⟨3531984, by rfl⟩ : syracuseStep 9418625 = 7063969) B7063969
theorem B6279083 : Blo 1959435 6279083 := bstep (se 1 (by rfl) ⟨4709312, by rfl⟩ : syracuseStep 6279083 = 9418625) B9418625
theorem B4186055 : Blo 1959435 4186055 := bstep (se 1 (by rfl) ⟨3139541, by rfl⟩ : syracuseStep 4186055 = 6279083) B6279083
theorem B2790703 : Blo 1959435 2790703 := bstep (se 1 (by rfl) ⟨2093027, by rfl⟩ : syracuseStep 2790703 = 4186055) B4186055
theorem B14883749 : Blo 1959435 14883749 := bstep (se 4 (by rfl) ⟨1395351, by rfl⟩ : syracuseStep 14883749 = 2790703) B2790703
theorem B9922499 : Blo 1959435 9922499 := bstep (se 1 (by rfl) ⟨7441874, by rfl⟩ : syracuseStep 9922499 = 14883749) B14883749
theorem B6614999 : Blo 1959435 6614999 := bstep (se 1 (by rfl) ⟨4961249, by rfl⟩ : syracuseStep 6614999 = 9922499) B9922499
theorem B4409999 : Blo 1959435 4409999 := bstep (se 1 (by rfl) ⟨3307499, by rfl⟩ : syracuseStep 4409999 = 6614999) B6614999
theorem B2939999 : Blo 1959435 2939999 := bstep (se 1 (by rfl) ⟨2204999, by rfl⟩ : syracuseStep 2939999 = 4409999) B4409999
theorem B1959999 : Blo 1959435 1959999 := bstep (se 1 (by rfl) ⟨1469999, by rfl⟩ : syracuseStep 1959999 = 2939999) B2939999
theorem B2940005 : Blo 1959435 2940005 := bbase (se 4 (by rfl) ⟨275625, by rfl⟩ : syracuseStep 2940005 = 551251) (by norm_num)
theorem B1960003 : Blo 1959435 1960003 := bstep (se 1 (by rfl) ⟨1470002, by rfl⟩ : syracuseStep 1960003 = 2940005) B2940005
theorem B4709333 : Blo 1959435 4709333 := bbase (se 7 (by rfl) ⟨55187, by rfl⟩ : syracuseStep 4709333 = 110375) (by norm_num)
theorem B3139555 : Blo 1959435 3139555 := bstep (se 1 (by rfl) ⟨2354666, by rfl⟩ : syracuseStep 3139555 = 4709333) B4709333
theorem B4186073 : Blo 1959435 4186073 := bstep (se 2 (by rfl) ⟨1569777, by rfl⟩ : syracuseStep 4186073 = 3139555) B3139555
theorem B2790715 : Blo 1959435 2790715 := bstep (se 1 (by rfl) ⟨2093036, by rfl⟩ : syracuseStep 2790715 = 4186073) B4186073
theorem B3720953 : Blo 1959435 3720953 := bstep (se 2 (by rfl) ⟨1395357, by rfl⟩ : syracuseStep 3720953 = 2790715) B2790715
theorem B2480635 : Blo 1959435 2480635 := bstep (se 1 (by rfl) ⟨1860476, by rfl⟩ : syracuseStep 2480635 = 3720953) B3720953
theorem B3307513 : Blo 1959435 3307513 := bstep (se 2 (by rfl) ⟨1240317, by rfl⟩ : syracuseStep 3307513 = 2480635) B2480635
theorem B4410017 : Blo 1959435 4410017 := bstep (se 2 (by rfl) ⟨1653756, by rfl⟩ : syracuseStep 4410017 = 3307513) B3307513
theorem B2940011 : Blo 1959435 2940011 := bstep (se 1 (by rfl) ⟨2205008, by rfl⟩ : syracuseStep 2940011 = 4410017) B4410017
theorem B1960007 : Blo 1959435 1960007 := bstep (se 1 (by rfl) ⟨1470005, by rfl⟩ : syracuseStep 1960007 = 2940011) B2940011
theorem B2205013 : Blo 1959435 2205013 := bbase (se 12 (by rfl) ⟨807, by rfl⟩ : syracuseStep 2205013 = 1615) (by norm_num)
theorem B2940017 : Blo 1959435 2940017 := bstep (se 2 (by rfl) ⟨1102506, by rfl⟩ : syracuseStep 2940017 = 2205013) B2205013
theorem B1960011 : Blo 1959435 1960011 := bstep (se 1 (by rfl) ⟨1470008, by rfl⟩ : syracuseStep 1960011 = 2940017) B2940017
theorem B2480645 : Blo 1959435 2480645 := bbase (se 4 (by rfl) ⟨232560, by rfl⟩ : syracuseStep 2480645 = 465121) (by norm_num)
theorem B6615053 : Blo 1959435 6615053 := bstep (se 3 (by rfl) ⟨1240322, by rfl⟩ : syracuseStep 6615053 = 2480645) B2480645
theorem B4410035 : Blo 1959435 4410035 := bstep (se 1 (by rfl) ⟨3307526, by rfl⟩ : syracuseStep 4410035 = 6615053) B6615053
theorem B2940023 : Blo 1959435 2940023 := bstep (se 1 (by rfl) ⟨2205017, by rfl⟩ : syracuseStep 2940023 = 4410035) B4410035
theorem B1960015 : Blo 1959435 1960015 := bstep (se 1 (by rfl) ⟨1470011, by rfl⟩ : syracuseStep 1960015 = 2940023) B2940023
theorem B2940029 : Blo 1959435 2940029 := bbase (se 3 (by rfl) ⟨551255, by rfl⟩ : syracuseStep 2940029 = 1102511) (by norm_num)
theorem B1960019 : Blo 1959435 1960019 := bstep (se 1 (by rfl) ⟨1470014, by rfl⟩ : syracuseStep 1960019 = 2940029) B2940029
theorem B4410053 : Blo 1959435 4410053 := bbase (se 4 (by rfl) ⟨413442, by rfl⟩ : syracuseStep 4410053 = 826885) (by norm_num)
theorem B2940035 : Blo 1959435 2940035 := bstep (se 1 (by rfl) ⟨2205026, by rfl⟩ : syracuseStep 2940035 = 4410053) B4410053
theorem B1960023 : Blo 1959435 1960023 := bstep (se 1 (by rfl) ⟨1470017, by rfl⟩ : syracuseStep 1960023 = 2940035) B2940035
theorem B5298053 : Blo 1959435 5298053 := bbase (se 4 (by rfl) ⟨496692, by rfl⟩ : syracuseStep 5298053 = 993385) (by norm_num)
theorem B14128141 : Blo 1959435 14128141 := bstep (se 3 (by rfl) ⟨2649026, by rfl⟩ : syracuseStep 14128141 = 5298053) B5298053
theorem B18837521 : Blo 1959435 18837521 := bstep (se 2 (by rfl) ⟨7064070, by rfl⟩ : syracuseStep 18837521 = 14128141) B14128141
theorem B12558347 : Blo 1959435 12558347 := bstep (se 1 (by rfl) ⟨9418760, by rfl⟩ : syracuseStep 12558347 = 18837521) B18837521
theorem B8372231 : Blo 1959435 8372231 := bstep (se 1 (by rfl) ⟨6279173, by rfl⟩ : syracuseStep 8372231 = 12558347) B12558347
theorem B5581487 : Blo 1959435 5581487 := bstep (se 1 (by rfl) ⟨4186115, by rfl⟩ : syracuseStep 5581487 = 8372231) B8372231
theorem B3720991 : Blo 1959435 3720991 := bstep (se 1 (by rfl) ⟨2790743, by rfl⟩ : syracuseStep 3720991 = 5581487) B5581487
theorem B4961321 : Blo 1959435 4961321 := bstep (se 2 (by rfl) ⟨1860495, by rfl⟩ : syracuseStep 4961321 = 3720991) B3720991
theorem B3307547 : Blo 1959435 3307547 := bstep (se 1 (by rfl) ⟨2480660, by rfl⟩ : syracuseStep 3307547 = 4961321) B4961321
theorem B2205031 : Blo 1959435 2205031 := bstep (se 1 (by rfl) ⟨1653773, by rfl⟩ : syracuseStep 2205031 = 3307547) B3307547
theorem B2940041 : Blo 1959435 2940041 := bstep (se 2 (by rfl) ⟨1102515, by rfl⟩ : syracuseStep 2940041 = 2205031) B2205031
theorem B1960027 : Blo 1959435 1960027 := bstep (se 1 (by rfl) ⟨1470020, by rfl⟩ : syracuseStep 1960027 = 2940041) B2940041
theorem B9922661 : Blo 1959435 9922661 := bbase (se 4 (by rfl) ⟨930249, by rfl⟩ : syracuseStep 9922661 = 1860499) (by norm_num)
theorem B6615107 : Blo 1959435 6615107 := bstep (se 1 (by rfl) ⟨4961330, by rfl⟩ : syracuseStep 6615107 = 9922661) B9922661
theorem B4410071 : Blo 1959435 4410071 := bstep (se 1 (by rfl) ⟨3307553, by rfl⟩ : syracuseStep 4410071 = 6615107) B6615107
theorem B2940047 : Blo 1959435 2940047 := bstep (se 1 (by rfl) ⟨2205035, by rfl⟩ : syracuseStep 2940047 = 4410071) B4410071
theorem B1960031 : Blo 1959435 1960031 := bstep (se 1 (by rfl) ⟨1470023, by rfl⟩ : syracuseStep 1960031 = 2940047) B2940047
theorem B2940053 : Blo 1959435 2940053 := bbase (se 6 (by rfl) ⟨68907, by rfl⟩ : syracuseStep 2940053 = 137815) (by norm_num)
theorem B1960035 : Blo 1959435 1960035 := bstep (se 1 (by rfl) ⟨1470026, by rfl⟩ : syracuseStep 1960035 = 2940053) B2940053
theorem B5298085 : Blo 1959435 5298085 := bbase (se 4 (by rfl) ⟨496695, by rfl⟩ : syracuseStep 5298085 = 993391) (by norm_num)
theorem B7064113 : Blo 1959435 7064113 := bstep (se 2 (by rfl) ⟨2649042, by rfl⟩ : syracuseStep 7064113 = 5298085) B5298085
theorem B9418817 : Blo 1959435 9418817 := bstep (se 2 (by rfl) ⟨3532056, by rfl⟩ : syracuseStep 9418817 = 7064113) B7064113
theorem B6279211 : Blo 1959435 6279211 := bstep (se 1 (by rfl) ⟨4709408, by rfl⟩ : syracuseStep 6279211 = 9418817) B9418817
theorem B8372281 : Blo 1959435 8372281 := bstep (se 2 (by rfl) ⟨3139605, by rfl⟩ : syracuseStep 8372281 = 6279211) B6279211
theorem B11163041 : Blo 1959435 11163041 := bstep (se 2 (by rfl) ⟨4186140, by rfl⟩ : syracuseStep 11163041 = 8372281) B8372281
theorem B7442027 : Blo 1959435 7442027 := bstep (se 1 (by rfl) ⟨5581520, by rfl⟩ : syracuseStep 7442027 = 11163041) B11163041
theorem B4961351 : Blo 1959435 4961351 := bstep (se 1 (by rfl) ⟨3721013, by rfl⟩ : syracuseStep 4961351 = 7442027) B7442027
theorem B3307567 : Blo 1959435 3307567 := bstep (se 1 (by rfl) ⟨2480675, by rfl⟩ : syracuseStep 3307567 = 4961351) B4961351
theorem B4410089 : Blo 1959435 4410089 := bstep (se 2 (by rfl) ⟨1653783, by rfl⟩ : syracuseStep 4410089 = 3307567) B3307567
theorem B2940059 : Blo 1959435 2940059 := bstep (se 1 (by rfl) ⟨2205044, by rfl⟩ : syracuseStep 2940059 = 4410089) B4410089
theorem B1960039 : Blo 1959435 1960039 := bstep (se 1 (by rfl) ⟨1470029, by rfl⟩ : syracuseStep 1960039 = 2940059) B2940059
theorem B2205049 : Blo 1959435 2205049 := bbase (se 2 (by rfl) ⟨826893, by rfl⟩ : syracuseStep 2205049 = 1653787) (by norm_num)
theorem B2940065 : Blo 1959435 2940065 := bstep (se 2 (by rfl) ⟨1102524, by rfl⟩ : syracuseStep 2940065 = 2205049) B2205049
theorem B1960043 : Blo 1959435 1960043 := bstep (se 1 (by rfl) ⟨1470032, by rfl⟩ : syracuseStep 1960043 = 2940065) B2940065
theorem B12083381 : Blo 1959435 12083381 := bbase (se 5 (by rfl) ⟨566408, by rfl⟩ : syracuseStep 12083381 = 1132817) (by norm_num)
theorem B8055587 : Blo 1959435 8055587 := bstep (se 1 (by rfl) ⟨6041690, by rfl⟩ : syracuseStep 8055587 = 12083381) B12083381
theorem B5370391 : Blo 1959435 5370391 := bstep (se 1 (by rfl) ⟨4027793, by rfl⟩ : syracuseStep 5370391 = 8055587) B8055587
theorem B28642085 : Blo 1959435 28642085 := bstep (se 4 (by rfl) ⟨2685195, by rfl⟩ : syracuseStep 28642085 = 5370391) B5370391
theorem B19094723 : Blo 1959435 19094723 := bstep (se 1 (by rfl) ⟨14321042, by rfl⟩ : syracuseStep 19094723 = 28642085) B28642085
theorem B12729815 : Blo 1959435 12729815 := bstep (se 1 (by rfl) ⟨9547361, by rfl⟩ : syracuseStep 12729815 = 19094723) B19094723
theorem B8486543 : Blo 1959435 8486543 := bstep (se 1 (by rfl) ⟨6364907, by rfl⟩ : syracuseStep 8486543 = 12729815) B12729815
theorem B5657695 : Blo 1959435 5657695 := bstep (se 1 (by rfl) ⟨4243271, by rfl⟩ : syracuseStep 5657695 = 8486543) B8486543
theorem B30174373 : Blo 1959435 30174373 := bstep (se 4 (by rfl) ⟨2828847, by rfl⟩ : syracuseStep 30174373 = 5657695) B5657695
theorem B40232497 : Blo 1959435 40232497 := bstep (se 2 (by rfl) ⟨15087186, by rfl⟩ : syracuseStep 40232497 = 30174373) B30174373
theorem B53643329 : Blo 1959435 53643329 := bstep (se 2 (by rfl) ⟨20116248, by rfl⟩ : syracuseStep 53643329 = 40232497) B40232497
theorem B35762219 : Blo 1959435 35762219 := bstep (se 1 (by rfl) ⟨26821664, by rfl⟩ : syracuseStep 35762219 = 53643329) B53643329
theorem B23841479 : Blo 1959435 23841479 := bstep (se 1 (by rfl) ⟨17881109, by rfl⟩ : syracuseStep 23841479 = 35762219) B35762219
theorem B15894319 : Blo 1959435 15894319 := bstep (se 1 (by rfl) ⟨11920739, by rfl⟩ : syracuseStep 15894319 = 23841479) B23841479
theorem B21192425 : Blo 1959435 21192425 := bstep (se 2 (by rfl) ⟨7947159, by rfl⟩ : syracuseStep 21192425 = 15894319) B15894319
theorem B14128283 : Blo 1959435 14128283 := bstep (se 1 (by rfl) ⟨10596212, by rfl⟩ : syracuseStep 14128283 = 21192425) B21192425
theorem B9418855 : Blo 1959435 9418855 := bstep (se 1 (by rfl) ⟨7064141, by rfl⟩ : syracuseStep 9418855 = 14128283) B14128283
theorem B12558473 : Blo 1959435 12558473 := bstep (se 2 (by rfl) ⟨4709427, by rfl⟩ : syracuseStep 12558473 = 9418855) B9418855
theorem B8372315 : Blo 1959435 8372315 := bstep (se 1 (by rfl) ⟨6279236, by rfl⟩ : syracuseStep 8372315 = 12558473) B12558473
theorem B5581543 : Blo 1959435 5581543 := bstep (se 1 (by rfl) ⟨4186157, by rfl⟩ : syracuseStep 5581543 = 8372315) B8372315
theorem B7442057 : Blo 1959435 7442057 := bstep (se 2 (by rfl) ⟨2790771, by rfl⟩ : syracuseStep 7442057 = 5581543) B5581543
theorem B4961371 : Blo 1959435 4961371 := bstep (se 1 (by rfl) ⟨3721028, by rfl⟩ : syracuseStep 4961371 = 7442057) B7442057
theorem B6615161 : Blo 1959435 6615161 := bstep (se 2 (by rfl) ⟨2480685, by rfl⟩ : syracuseStep 6615161 = 4961371) B4961371
theorem B4410107 : Blo 1959435 4410107 := bstep (se 1 (by rfl) ⟨3307580, by rfl⟩ : syracuseStep 4410107 = 6615161) B6615161
theorem B2940071 : Blo 1959435 2940071 := bstep (se 1 (by rfl) ⟨2205053, by rfl⟩ : syracuseStep 2940071 = 4410107) B4410107
theorem B1960047 : Blo 1959435 1960047 := bstep (se 1 (by rfl) ⟨1470035, by rfl⟩ : syracuseStep 1960047 = 2940071) B2940071
theorem B2940077 : Blo 1959435 2940077 := bbase (se 3 (by rfl) ⟨551264, by rfl⟩ : syracuseStep 2940077 = 1102529) (by norm_num)
theorem B1960051 : Blo 1959435 1960051 := bstep (se 1 (by rfl) ⟨1470038, by rfl⟩ : syracuseStep 1960051 = 2940077) B2940077
theorem B4410125 : Blo 1959435 4410125 := bbase (se 3 (by rfl) ⟨826898, by rfl⟩ : syracuseStep 4410125 = 1653797) (by norm_num)
theorem B2940083 : Blo 1959435 2940083 := bstep (se 1 (by rfl) ⟨2205062, by rfl⟩ : syracuseStep 2940083 = 4410125) B4410125
theorem B1960055 : Blo 1959435 1960055 := bstep (se 1 (by rfl) ⟨1470041, by rfl⟩ : syracuseStep 1960055 = 2940083) B2940083
theorem B2480701 : Blo 1959435 2480701 := bbase (se 3 (by rfl) ⟨465131, by rfl⟩ : syracuseStep 2480701 = 930263) (by norm_num)
theorem B3307601 : Blo 1959435 3307601 := bstep (se 2 (by rfl) ⟨1240350, by rfl⟩ : syracuseStep 3307601 = 2480701) B2480701
theorem B2205067 : Blo 1959435 2205067 := bstep (se 1 (by rfl) ⟨1653800, by rfl⟩ : syracuseStep 2205067 = 3307601) B3307601
theorem B2940089 : Blo 1959435 2940089 := bstep (se 2 (by rfl) ⟨1102533, by rfl⟩ : syracuseStep 2940089 = 2205067) B2205067
theorem B1960059 : Blo 1959435 1960059 := bstep (se 1 (by rfl) ⟨1470044, by rfl⟩ : syracuseStep 1960059 = 2940089) B2940089
theorem B5298149 : Blo 1959435 5298149 := bbase (se 4 (by rfl) ⟨496701, by rfl⟩ : syracuseStep 5298149 = 993403) (by norm_num)
theorem B14128397 : Blo 1959435 14128397 := bstep (se 3 (by rfl) ⟨2649074, by rfl⟩ : syracuseStep 14128397 = 5298149) B5298149
theorem B9418931 : Blo 1959435 9418931 := bstep (se 1 (by rfl) ⟨7064198, by rfl⟩ : syracuseStep 9418931 = 14128397) B14128397
theorem B6279287 : Blo 1959435 6279287 := bstep (se 1 (by rfl) ⟨4709465, by rfl⟩ : syracuseStep 6279287 = 9418931) B9418931
theorem B16744765 : Blo 1959435 16744765 := bstep (se 3 (by rfl) ⟨3139643, by rfl⟩ : syracuseStep 16744765 = 6279287) B6279287
theorem B22326353 : Blo 1959435 22326353 := bstep (se 2 (by rfl) ⟨8372382, by rfl⟩ : syracuseStep 22326353 = 16744765) B16744765
theorem B14884235 : Blo 1959435 14884235 := bstep (se 1 (by rfl) ⟨11163176, by rfl⟩ : syracuseStep 14884235 = 22326353) B22326353
theorem B9922823 : Blo 1959435 9922823 := bstep (se 1 (by rfl) ⟨7442117, by rfl⟩ : syracuseStep 9922823 = 14884235) B14884235
theorem B6615215 : Blo 1959435 6615215 := bstep (se 1 (by rfl) ⟨4961411, by rfl⟩ : syracuseStep 6615215 = 9922823) B9922823
theorem B4410143 : Blo 1959435 4410143 := bstep (se 1 (by rfl) ⟨3307607, by rfl⟩ : syracuseStep 4410143 = 6615215) B6615215
theorem B2940095 : Blo 1959435 2940095 := bstep (se 1 (by rfl) ⟨2205071, by rfl⟩ : syracuseStep 2940095 = 4410143) B4410143
theorem B1960063 : Blo 1959435 1960063 := bstep (se 1 (by rfl) ⟨1470047, by rfl⟩ : syracuseStep 1960063 = 2940095) B2940095
theorem B2940101 : Blo 1959435 2940101 := bbase (se 4 (by rfl) ⟨275634, by rfl⟩ : syracuseStep 2940101 = 551269) (by norm_num)
theorem B1960067 : Blo 1959435 1960067 := bstep (se 1 (by rfl) ⟨1470050, by rfl⟩ : syracuseStep 1960067 = 2940101) B2940101
theorem B3307621 : Blo 1959435 3307621 := bbase (se 4 (by rfl) ⟨310089, by rfl⟩ : syracuseStep 3307621 = 620179) (by norm_num)
theorem B4410161 : Blo 1959435 4410161 := bstep (se 2 (by rfl) ⟨1653810, by rfl⟩ : syracuseStep 4410161 = 3307621) B3307621
theorem B2940107 : Blo 1959435 2940107 := bstep (se 1 (by rfl) ⟨2205080, by rfl⟩ : syracuseStep 2940107 = 4410161) B4410161
theorem B1960071 : Blo 1959435 1960071 := bstep (se 1 (by rfl) ⟨1470053, by rfl⟩ : syracuseStep 1960071 = 2940107) B2940107
theorem B2205085 : Blo 1959435 2205085 := bbase (se 3 (by rfl) ⟨413453, by rfl⟩ : syracuseStep 2205085 = 826907) (by norm_num)
theorem B2940113 : Blo 1959435 2940113 := bstep (se 2 (by rfl) ⟨1102542, by rfl⟩ : syracuseStep 2940113 = 2205085) B2205085
theorem B1960075 : Blo 1959435 1960075 := bstep (se 1 (by rfl) ⟨1470056, by rfl⟩ : syracuseStep 1960075 = 2940113) B2940113
theorem B6615269 : Blo 1959435 6615269 := bbase (se 4 (by rfl) ⟨620181, by rfl⟩ : syracuseStep 6615269 = 1240363) (by norm_num)
theorem B4410179 : Blo 1959435 4410179 := bstep (se 1 (by rfl) ⟨3307634, by rfl⟩ : syracuseStep 4410179 = 6615269) B6615269
theorem B2940119 : Blo 1959435 2940119 := bstep (se 1 (by rfl) ⟨2205089, by rfl⟩ : syracuseStep 2940119 = 4410179) B4410179
theorem B1960079 : Blo 1959435 1960079 := bstep (se 1 (by rfl) ⟨1470059, by rfl⟩ : syracuseStep 1960079 = 2940119) B2940119
theorem B2940125 : Blo 1959435 2940125 := bbase (se 3 (by rfl) ⟨551273, by rfl⟩ : syracuseStep 2940125 = 1102547) (by norm_num)
theorem B1960083 : Blo 1959435 1960083 := bstep (se 1 (by rfl) ⟨1470062, by rfl⟩ : syracuseStep 1960083 = 2940125) B2940125
theorem B4410197 : Blo 1959435 4410197 := bbase (se 9 (by rfl) ⟨12920, by rfl⟩ : syracuseStep 4410197 = 25841) (by norm_num)
theorem B2940131 : Blo 1959435 2940131 := bstep (se 1 (by rfl) ⟨2205098, by rfl⟩ : syracuseStep 2940131 = 4410197) B4410197
theorem B1960087 : Blo 1959435 1960087 := bstep (se 1 (by rfl) ⟨1470065, by rfl⟩ : syracuseStep 1960087 = 2940131) B2940131
theorem B5581669 : Blo 1959435 5581669 := bbase (se 4 (by rfl) ⟨523281, by rfl⟩ : syracuseStep 5581669 = 1046563) (by norm_num)
theorem B7442225 : Blo 1959435 7442225 := bstep (se 2 (by rfl) ⟨2790834, by rfl⟩ : syracuseStep 7442225 = 5581669) B5581669
theorem B4961483 : Blo 1959435 4961483 := bstep (se 1 (by rfl) ⟨3721112, by rfl⟩ : syracuseStep 4961483 = 7442225) B7442225
theorem B3307655 : Blo 1959435 3307655 := bstep (se 1 (by rfl) ⟨2480741, by rfl⟩ : syracuseStep 3307655 = 4961483) B4961483
theorem B2205103 : Blo 1959435 2205103 := bstep (se 1 (by rfl) ⟨1653827, by rfl⟩ : syracuseStep 2205103 = 3307655) B3307655
theorem B2940137 : Blo 1959435 2940137 := bstep (se 2 (by rfl) ⟨1102551, by rfl⟩ : syracuseStep 2940137 = 2205103) B2205103
theorem B1960091 : Blo 1959435 1960091 := bstep (se 1 (by rfl) ⟨1470068, by rfl⟩ : syracuseStep 1960091 = 2940137) B2940137
theorem B8940773 : Blo 1959435 8940773 := bbase (se 4 (by rfl) ⟨838197, by rfl⟩ : syracuseStep 8940773 = 1676395) (by norm_num)
theorem B5960515 : Blo 1959435 5960515 := bstep (se 1 (by rfl) ⟨4470386, by rfl⟩ : syracuseStep 5960515 = 8940773) B8940773
theorem B7947353 : Blo 1959435 7947353 := bstep (se 2 (by rfl) ⟨2980257, by rfl⟩ : syracuseStep 7947353 = 5960515) B5960515
theorem B21192941 : Blo 1959435 21192941 := bstep (se 3 (by rfl) ⟨3973676, by rfl⟩ : syracuseStep 21192941 = 7947353) B7947353
theorem B56514509 : Blo 1959435 56514509 := bstep (se 3 (by rfl) ⟨10596470, by rfl⟩ : syracuseStep 56514509 = 21192941) B21192941
theorem B37676339 : Blo 1959435 37676339 := bstep (se 1 (by rfl) ⟨28257254, by rfl⟩ : syracuseStep 37676339 = 56514509) B56514509
theorem B25117559 : Blo 1959435 25117559 := bstep (se 1 (by rfl) ⟨18838169, by rfl⟩ : syracuseStep 25117559 = 37676339) B37676339
theorem B16745039 : Blo 1959435 16745039 := bstep (se 1 (by rfl) ⟨12558779, by rfl⟩ : syracuseStep 16745039 = 25117559) B25117559
theorem B11163359 : Blo 1959435 11163359 := bstep (se 1 (by rfl) ⟨8372519, by rfl⟩ : syracuseStep 11163359 = 16745039) B16745039
theorem B7442239 : Blo 1959435 7442239 := bstep (se 1 (by rfl) ⟨5581679, by rfl⟩ : syracuseStep 7442239 = 11163359) B11163359
theorem B9922985 : Blo 1959435 9922985 := bstep (se 2 (by rfl) ⟨3721119, by rfl⟩ : syracuseStep 9922985 = 7442239) B7442239
theorem B6615323 : Blo 1959435 6615323 := bstep (se 1 (by rfl) ⟨4961492, by rfl⟩ : syracuseStep 6615323 = 9922985) B9922985
theorem B4410215 : Blo 1959435 4410215 := bstep (se 1 (by rfl) ⟨3307661, by rfl⟩ : syracuseStep 4410215 = 6615323) B6615323
theorem B2940143 : Blo 1959435 2940143 := bstep (se 1 (by rfl) ⟨2205107, by rfl⟩ : syracuseStep 2940143 = 4410215) B4410215
theorem B1960095 : Blo 1959435 1960095 := bstep (se 1 (by rfl) ⟨1470071, by rfl⟩ : syracuseStep 1960095 = 2940143) B2940143
theorem B2940149 : Blo 1959435 2940149 := bbase (se 5 (by rfl) ⟨137819, by rfl⟩ : syracuseStep 2940149 = 275639) (by norm_num)
theorem B1960099 : Blo 1959435 1960099 := bstep (se 1 (by rfl) ⟨1470074, by rfl⟩ : syracuseStep 1960099 = 2940149) B2940149
theorem B9419125 : Blo 1959435 9419125 := bbase (se 5 (by rfl) ⟨441521, by rfl⟩ : syracuseStep 9419125 = 883043) (by norm_num)
theorem B12558833 : Blo 1959435 12558833 := bstep (se 2 (by rfl) ⟨4709562, by rfl⟩ : syracuseStep 12558833 = 9419125) B9419125
theorem B8372555 : Blo 1959435 8372555 := bstep (se 1 (by rfl) ⟨6279416, by rfl⟩ : syracuseStep 8372555 = 12558833) B12558833
theorem B5581703 : Blo 1959435 5581703 := bstep (se 1 (by rfl) ⟨4186277, by rfl⟩ : syracuseStep 5581703 = 8372555) B8372555
theorem B3721135 : Blo 1959435 3721135 := bstep (se 1 (by rfl) ⟨2790851, by rfl⟩ : syracuseStep 3721135 = 5581703) B5581703
theorem B4961513 : Blo 1959435 4961513 := bstep (se 2 (by rfl) ⟨1860567, by rfl⟩ : syracuseStep 4961513 = 3721135) B3721135
theorem B3307675 : Blo 1959435 3307675 := bstep (se 1 (by rfl) ⟨2480756, by rfl⟩ : syracuseStep 3307675 = 4961513) B4961513
theorem B4410233 : Blo 1959435 4410233 := bstep (se 2 (by rfl) ⟨1653837, by rfl⟩ : syracuseStep 4410233 = 3307675) B3307675
theorem B2940155 : Blo 1959435 2940155 := bstep (se 1 (by rfl) ⟨2205116, by rfl⟩ : syracuseStep 2940155 = 4410233) B4410233
theorem B1960103 : Blo 1959435 1960103 := bstep (se 1 (by rfl) ⟨1470077, by rfl⟩ : syracuseStep 1960103 = 2940155) B2940155
theorem B2205121 : Blo 1959435 2205121 := bbase (se 2 (by rfl) ⟨826920, by rfl⟩ : syracuseStep 2205121 = 1653841) (by norm_num)
theorem B2940161 : Blo 1959435 2940161 := bstep (se 2 (by rfl) ⟨1102560, by rfl⟩ : syracuseStep 2940161 = 2205121) B2205121
theorem B1960107 : Blo 1959435 1960107 := bstep (se 1 (by rfl) ⟨1470080, by rfl⟩ : syracuseStep 1960107 = 2940161) B2940161
theorem B4961533 : Blo 1959435 4961533 := bbase (se 3 (by rfl) ⟨930287, by rfl⟩ : syracuseStep 4961533 = 1860575) (by norm_num)
theorem B6615377 : Blo 1959435 6615377 := bstep (se 2 (by rfl) ⟨2480766, by rfl⟩ : syracuseStep 6615377 = 4961533) B4961533
theorem B4410251 : Blo 1959435 4410251 := bstep (se 1 (by rfl) ⟨3307688, by rfl⟩ : syracuseStep 4410251 = 6615377) B6615377
theorem B2940167 : Blo 1959435 2940167 := bstep (se 1 (by rfl) ⟨2205125, by rfl⟩ : syracuseStep 2940167 = 4410251) B4410251
theorem B1960111 : Blo 1959435 1960111 := bstep (se 1 (by rfl) ⟨1470083, by rfl⟩ : syracuseStep 1960111 = 2940167) B2940167
theorem B2940173 : Blo 1959435 2940173 := bbase (se 3 (by rfl) ⟨551282, by rfl⟩ : syracuseStep 2940173 = 1102565) (by norm_num)
theorem B1960115 : Blo 1959435 1960115 := bstep (se 1 (by rfl) ⟨1470086, by rfl⟩ : syracuseStep 1960115 = 2940173) B2940173
theorem B4410269 : Blo 1959435 4410269 := bbase (se 3 (by rfl) ⟨826925, by rfl⟩ : syracuseStep 4410269 = 1653851) (by norm_num)
theorem B2940179 : Blo 1959435 2940179 := bstep (se 1 (by rfl) ⟨2205134, by rfl⟩ : syracuseStep 2940179 = 4410269) B4410269
theorem B1960119 : Blo 1959435 1960119 := bstep (se 1 (by rfl) ⟨1470089, by rfl⟩ : syracuseStep 1960119 = 2940179) B2940179
theorem B3307709 : Blo 1959435 3307709 := bbase (se 3 (by rfl) ⟨620195, by rfl⟩ : syracuseStep 3307709 = 1240391) (by norm_num)
theorem B2205139 : Blo 1959435 2205139 := bstep (se 1 (by rfl) ⟨1653854, by rfl⟩ : syracuseStep 2205139 = 3307709) B3307709
theorem B2940185 : Blo 1959435 2940185 := bstep (se 2 (by rfl) ⟨1102569, by rfl⟩ : syracuseStep 2940185 = 2205139) B2205139
theorem B1960123 : Blo 1959435 1960123 := bstep (se 1 (by rfl) ⟨1470092, by rfl⟩ : syracuseStep 1960123 = 2940185) B2940185
theorem B11163541 : Blo 1959435 11163541 := bbase (se 6 (by rfl) ⟨261645, by rfl⟩ : syracuseStep 11163541 = 523291) (by norm_num)
theorem B14884721 : Blo 1959435 14884721 := bstep (se 2 (by rfl) ⟨5581770, by rfl⟩ : syracuseStep 14884721 = 11163541) B11163541
theorem B9923147 : Blo 1959435 9923147 := bstep (se 1 (by rfl) ⟨7442360, by rfl⟩ : syracuseStep 9923147 = 14884721) B14884721
theorem B6615431 : Blo 1959435 6615431 := bstep (se 1 (by rfl) ⟨4961573, by rfl⟩ : syracuseStep 6615431 = 9923147) B9923147
theorem B4410287 : Blo 1959435 4410287 := bstep (se 1 (by rfl) ⟨3307715, by rfl⟩ : syracuseStep 4410287 = 6615431) B6615431
theorem B2940191 : Blo 1959435 2940191 := bstep (se 1 (by rfl) ⟨2205143, by rfl⟩ : syracuseStep 2940191 = 4410287) B4410287
theorem B1960127 : Blo 1959435 1960127 := bstep (se 1 (by rfl) ⟨1470095, by rfl⟩ : syracuseStep 1960127 = 2940191) B2940191
theorem B2940197 : Blo 1959435 2940197 := bbase (se 4 (by rfl) ⟨275643, by rfl⟩ : syracuseStep 2940197 = 551287) (by norm_num)
theorem B1960131 : Blo 1959435 1960131 := bstep (se 1 (by rfl) ⟨1470098, by rfl⟩ : syracuseStep 1960131 = 2940197) B2940197
theorem B2480797 : Blo 1959435 2480797 := bbase (se 3 (by rfl) ⟨465149, by rfl⟩ : syracuseStep 2480797 = 930299) (by norm_num)
theorem B3307729 : Blo 1959435 3307729 := bstep (se 2 (by rfl) ⟨1240398, by rfl⟩ : syracuseStep 3307729 = 2480797) B2480797
theorem B4410305 : Blo 1959435 4410305 := bstep (se 2 (by rfl) ⟨1653864, by rfl⟩ : syracuseStep 4410305 = 3307729) B3307729
theorem B2940203 : Blo 1959435 2940203 := bstep (se 1 (by rfl) ⟨2205152, by rfl⟩ : syracuseStep 2940203 = 4410305) B4410305
theorem B1960135 : Blo 1959435 1960135 := bstep (se 1 (by rfl) ⟨1470101, by rfl⟩ : syracuseStep 1960135 = 2940203) B2940203
theorem B2205157 : Blo 1959435 2205157 := bbase (se 4 (by rfl) ⟨206733, by rfl⟩ : syracuseStep 2205157 = 413467) (by norm_num)
theorem B2940209 : Blo 1959435 2940209 := bstep (se 2 (by rfl) ⟨1102578, by rfl⟩ : syracuseStep 2940209 = 2205157) B2205157
theorem B1960139 : Blo 1959435 1960139 := bstep (se 1 (by rfl) ⟨1470104, by rfl⟩ : syracuseStep 1960139 = 2940209) B2940209
theorem B4773917 : Blo 1959435 4773917 := bbase (se 3 (by rfl) ⟨895109, by rfl⟩ : syracuseStep 4773917 = 1790219) (by norm_num)
theorem B3182611 : Blo 1959435 3182611 := bstep (se 1 (by rfl) ⟨2386958, by rfl⟩ : syracuseStep 3182611 = 4773917) B4773917
theorem B4243481 : Blo 1959435 4243481 := bstep (se 2 (by rfl) ⟨1591305, by rfl⟩ : syracuseStep 4243481 = 3182611) B3182611
theorem B2828987 : Blo 1959435 2828987 := bstep (se 1 (by rfl) ⟨2121740, by rfl⟩ : syracuseStep 2828987 = 4243481) B4243481
theorem B30175861 : Blo 1959435 30175861 := bstep (se 5 (by rfl) ⟨1414493, by rfl⟩ : syracuseStep 30175861 = 2828987) B2828987
theorem B40234481 : Blo 1959435 40234481 := bstep (se 2 (by rfl) ⟨15087930, by rfl⟩ : syracuseStep 40234481 = 30175861) B30175861
theorem B26822987 : Blo 1959435 26822987 := bstep (se 1 (by rfl) ⟨20117240, by rfl⟩ : syracuseStep 26822987 = 40234481) B40234481
theorem B17881991 : Blo 1959435 17881991 := bstep (se 1 (by rfl) ⟨13411493, by rfl⟩ : syracuseStep 17881991 = 26822987) B26822987
theorem B11921327 : Blo 1959435 11921327 := bstep (se 1 (by rfl) ⟨8940995, by rfl⟩ : syracuseStep 11921327 = 17881991) B17881991
theorem B7947551 : Blo 1959435 7947551 := bstep (se 1 (by rfl) ⟨5960663, by rfl⟩ : syracuseStep 7947551 = 11921327) B11921327
theorem B5298367 : Blo 1959435 5298367 := bstep (se 1 (by rfl) ⟨3973775, by rfl⟩ : syracuseStep 5298367 = 7947551) B7947551
theorem B7064489 : Blo 1959435 7064489 := bstep (se 2 (by rfl) ⟨2649183, by rfl⟩ : syracuseStep 7064489 = 5298367) B5298367
theorem B4709659 : Blo 1959435 4709659 := bstep (se 1 (by rfl) ⟨3532244, by rfl⟩ : syracuseStep 4709659 = 7064489) B7064489
theorem B6279545 : Blo 1959435 6279545 := bstep (se 2 (by rfl) ⟨2354829, by rfl⟩ : syracuseStep 6279545 = 4709659) B4709659
theorem B4186363 : Blo 1959435 4186363 := bstep (se 1 (by rfl) ⟨3139772, by rfl⟩ : syracuseStep 4186363 = 6279545) B6279545
theorem B5581817 : Blo 1959435 5581817 := bstep (se 2 (by rfl) ⟨2093181, by rfl⟩ : syracuseStep 5581817 = 4186363) B4186363
theorem B3721211 : Blo 1959435 3721211 := bstep (se 1 (by rfl) ⟨2790908, by rfl⟩ : syracuseStep 3721211 = 5581817) B5581817
theorem B2480807 : Blo 1959435 2480807 := bstep (se 1 (by rfl) ⟨1860605, by rfl⟩ : syracuseStep 2480807 = 3721211) B3721211
theorem B6615485 : Blo 1959435 6615485 := bstep (se 3 (by rfl) ⟨1240403, by rfl⟩ : syracuseStep 6615485 = 2480807) B2480807
theorem B4410323 : Blo 1959435 4410323 := bstep (se 1 (by rfl) ⟨3307742, by rfl⟩ : syracuseStep 4410323 = 6615485) B6615485
theorem B2940215 : Blo 1959435 2940215 := bstep (se 1 (by rfl) ⟨2205161, by rfl⟩ : syracuseStep 2940215 = 4410323) B4410323
theorem B1960143 : Blo 1959435 1960143 := bstep (se 1 (by rfl) ⟨1470107, by rfl⟩ : syracuseStep 1960143 = 2940215) B2940215
theorem B2940221 : Blo 1959435 2940221 := bbase (se 3 (by rfl) ⟨551291, by rfl⟩ : syracuseStep 2940221 = 1102583) (by norm_num)
theorem B1960147 : Blo 1959435 1960147 := bstep (se 1 (by rfl) ⟨1470110, by rfl⟩ : syracuseStep 1960147 = 2940221) B2940221
theorem B4410341 : Blo 1959435 4410341 := bbase (se 4 (by rfl) ⟨413469, by rfl⟩ : syracuseStep 4410341 = 826939) (by norm_num)
theorem B2940227 : Blo 1959435 2940227 := bstep (se 1 (by rfl) ⟨2205170, by rfl⟩ : syracuseStep 2940227 = 4410341) B4410341
theorem B1960151 : Blo 1959435 1960151 := bstep (se 1 (by rfl) ⟨1470113, by rfl⟩ : syracuseStep 1960151 = 2940227) B2940227
theorem B4961645 : Blo 1959435 4961645 := bbase (se 3 (by rfl) ⟨930308, by rfl⟩ : syracuseStep 4961645 = 1860617) (by norm_num)
theorem B3307763 : Blo 1959435 3307763 := bstep (se 1 (by rfl) ⟨2480822, by rfl⟩ : syracuseStep 3307763 = 4961645) B4961645
theorem B2205175 : Blo 1959435 2205175 := bstep (se 1 (by rfl) ⟨1653881, by rfl⟩ : syracuseStep 2205175 = 3307763) B3307763
theorem B2940233 : Blo 1959435 2940233 := bstep (se 2 (by rfl) ⟨1102587, by rfl⟩ : syracuseStep 2940233 = 2205175) B2205175
theorem B1960155 : Blo 1959435 1960155 := bstep (se 1 (by rfl) ⟨1470116, by rfl⟩ : syracuseStep 1960155 = 2940233) B2940233
theorem B4186397 : Blo 1959435 4186397 := bbase (se 3 (by rfl) ⟨784949, by rfl⟩ : syracuseStep 4186397 = 1569899) (by norm_num)
theorem B2790931 : Blo 1959435 2790931 := bstep (se 1 (by rfl) ⟨2093198, by rfl⟩ : syracuseStep 2790931 = 4186397) B4186397
theorem B3721241 : Blo 1959435 3721241 := bstep (se 2 (by rfl) ⟨1395465, by rfl⟩ : syracuseStep 3721241 = 2790931) B2790931
theorem B9923309 : Blo 1959435 9923309 := bstep (se 3 (by rfl) ⟨1860620, by rfl⟩ : syracuseStep 9923309 = 3721241) B3721241
theorem B6615539 : Blo 1959435 6615539 := bstep (se 1 (by rfl) ⟨4961654, by rfl⟩ : syracuseStep 6615539 = 9923309) B9923309
theorem B4410359 : Blo 1959435 4410359 := bstep (se 1 (by rfl) ⟨3307769, by rfl⟩ : syracuseStep 4410359 = 6615539) B6615539
theorem B2940239 : Blo 1959435 2940239 := bstep (se 1 (by rfl) ⟨2205179, by rfl⟩ : syracuseStep 2940239 = 4410359) B4410359
theorem B1960159 : Blo 1959435 1960159 := bstep (se 1 (by rfl) ⟨1470119, by rfl⟩ : syracuseStep 1960159 = 2940239) B2940239
theorem B2940245 : Blo 1959435 2940245 := bbase (se 11 (by rfl) ⟨2153, by rfl⟩ : syracuseStep 2940245 = 4307) (by norm_num)
theorem B1960163 : Blo 1959435 1960163 := bstep (se 1 (by rfl) ⟨1470122, by rfl⟩ : syracuseStep 1960163 = 2940245) B2940245
theorem B4709717 : Blo 1959435 4709717 := bbase (se 11 (by rfl) ⟨3449, by rfl⟩ : syracuseStep 4709717 = 6899) (by norm_num)
theorem B3139811 : Blo 1959435 3139811 := bstep (se 1 (by rfl) ⟨2354858, by rfl⟩ : syracuseStep 3139811 = 4709717) B4709717
theorem B2093207 : Blo 1959435 2093207 := bstep (se 1 (by rfl) ⟨1569905, by rfl⟩ : syracuseStep 2093207 = 3139811) B3139811
theorem B5581885 : Blo 1959435 5581885 := bstep (se 3 (by rfl) ⟨1046603, by rfl⟩ : syracuseStep 5581885 = 2093207) B2093207
theorem B7442513 : Blo 1959435 7442513 := bstep (se 2 (by rfl) ⟨2790942, by rfl⟩ : syracuseStep 7442513 = 5581885) B5581885
theorem B4961675 : Blo 1959435 4961675 := bstep (se 1 (by rfl) ⟨3721256, by rfl⟩ : syracuseStep 4961675 = 7442513) B7442513
theorem B3307783 : Blo 1959435 3307783 := bstep (se 1 (by rfl) ⟨2480837, by rfl⟩ : syracuseStep 3307783 = 4961675) B4961675
theorem B4410377 : Blo 1959435 4410377 := bstep (se 2 (by rfl) ⟨1653891, by rfl⟩ : syracuseStep 4410377 = 3307783) B3307783
theorem B2940251 : Blo 1959435 2940251 := bstep (se 1 (by rfl) ⟨2205188, by rfl⟩ : syracuseStep 2940251 = 4410377) B4410377
theorem B1960167 : Blo 1959435 1960167 := bstep (se 1 (by rfl) ⟨1470125, by rfl⟩ : syracuseStep 1960167 = 2940251) B2940251
theorem B2205193 : Blo 1959435 2205193 := bbase (se 2 (by rfl) ⟨826947, by rfl⟩ : syracuseStep 2205193 = 1653895) (by norm_num)
theorem B2940257 : Blo 1959435 2940257 := bstep (se 2 (by rfl) ⟨1102596, by rfl⟩ : syracuseStep 2940257 = 2205193) B2205193
theorem B1960171 : Blo 1959435 1960171 := bstep (se 1 (by rfl) ⟨1470128, by rfl⟩ : syracuseStep 1960171 = 2940257) B2940257
theorem B4243549 : Blo 1959435 4243549 := bbase (se 3 (by rfl) ⟨795665, by rfl⟩ : syracuseStep 4243549 = 1591331) (by norm_num)
theorem B5658065 : Blo 1959435 5658065 := bstep (se 2 (by rfl) ⟨2121774, by rfl⟩ : syracuseStep 5658065 = 4243549) B4243549
theorem B3772043 : Blo 1959435 3772043 := bstep (se 1 (by rfl) ⟨2829032, by rfl⟩ : syracuseStep 3772043 = 5658065) B5658065
theorem B2514695 : Blo 1959435 2514695 := bstep (se 1 (by rfl) ⟨1886021, by rfl⟩ : syracuseStep 2514695 = 3772043) B3772043
theorem B26823413 : Blo 1959435 26823413 := bstep (se 5 (by rfl) ⟨1257347, by rfl⟩ : syracuseStep 26823413 = 2514695) B2514695
theorem B71529101 : Blo 1959435 71529101 := bstep (se 3 (by rfl) ⟨13411706, by rfl⟩ : syracuseStep 71529101 = 26823413) B26823413
theorem B47686067 : Blo 1959435 47686067 := bstep (se 1 (by rfl) ⟨35764550, by rfl⟩ : syracuseStep 47686067 = 71529101) B71529101
theorem B31790711 : Blo 1959435 31790711 := bstep (se 1 (by rfl) ⟨23843033, by rfl⟩ : syracuseStep 31790711 = 47686067) B47686067
theorem B21193807 : Blo 1959435 21193807 := bstep (se 1 (by rfl) ⟨15895355, by rfl⟩ : syracuseStep 21193807 = 31790711) B31790711
theorem B28258409 : Blo 1959435 28258409 := bstep (se 2 (by rfl) ⟨10596903, by rfl⟩ : syracuseStep 28258409 = 21193807) B21193807
theorem B18838939 : Blo 1959435 18838939 := bstep (se 1 (by rfl) ⟨14129204, by rfl⟩ : syracuseStep 18838939 = 28258409) B28258409
theorem B25118585 : Blo 1959435 25118585 := bstep (se 2 (by rfl) ⟨9419469, by rfl⟩ : syracuseStep 25118585 = 18838939) B18838939
theorem B16745723 : Blo 1959435 16745723 := bstep (se 1 (by rfl) ⟨12559292, by rfl⟩ : syracuseStep 16745723 = 25118585) B25118585
theorem B11163815 : Blo 1959435 11163815 := bstep (se 1 (by rfl) ⟨8372861, by rfl⟩ : syracuseStep 11163815 = 16745723) B16745723
theorem B7442543 : Blo 1959435 7442543 := bstep (se 1 (by rfl) ⟨5581907, by rfl⟩ : syracuseStep 7442543 = 11163815) B11163815
theorem B4961695 : Blo 1959435 4961695 := bstep (se 1 (by rfl) ⟨3721271, by rfl⟩ : syracuseStep 4961695 = 7442543) B7442543
theorem B6615593 : Blo 1959435 6615593 := bstep (se 2 (by rfl) ⟨2480847, by rfl⟩ : syracuseStep 6615593 = 4961695) B4961695
theorem B4410395 : Blo 1959435 4410395 := bstep (se 1 (by rfl) ⟨3307796, by rfl⟩ : syracuseStep 4410395 = 6615593) B6615593
theorem B2940263 : Blo 1959435 2940263 := bstep (se 1 (by rfl) ⟨2205197, by rfl⟩ : syracuseStep 2940263 = 4410395) B4410395
theorem B1960175 : Blo 1959435 1960175 := bstep (se 1 (by rfl) ⟨1470131, by rfl⟩ : syracuseStep 1960175 = 2940263) B2940263
theorem B2940269 : Blo 1959435 2940269 := bbase (se 3 (by rfl) ⟨551300, by rfl⟩ : syracuseStep 2940269 = 1102601) (by norm_num)
theorem B1960179 : Blo 1959435 1960179 := bstep (se 1 (by rfl) ⟨1470134, by rfl⟩ : syracuseStep 1960179 = 2940269) B2940269
theorem B4410413 : Blo 1959435 4410413 := bbase (se 3 (by rfl) ⟨826952, by rfl⟩ : syracuseStep 4410413 = 1653905) (by norm_num)
theorem B2940275 : Blo 1959435 2940275 := bstep (se 1 (by rfl) ⟨2205206, by rfl⟩ : syracuseStep 2940275 = 4410413) B4410413
theorem B1960183 : Blo 1959435 1960183 := bstep (se 1 (by rfl) ⟨1470137, by rfl⟩ : syracuseStep 1960183 = 2940275) B2940275
theorem B4709765 : Blo 1959435 4709765 := bbase (se 4 (by rfl) ⟨441540, by rfl⟩ : syracuseStep 4709765 = 883081) (by norm_num)
theorem B12559373 : Blo 1959435 12559373 := bstep (se 3 (by rfl) ⟨2354882, by rfl⟩ : syracuseStep 12559373 = 4709765) B4709765
theorem B8372915 : Blo 1959435 8372915 := bstep (se 1 (by rfl) ⟨6279686, by rfl⟩ : syracuseStep 8372915 = 12559373) B12559373
theorem B5581943 : Blo 1959435 5581943 := bstep (se 1 (by rfl) ⟨4186457, by rfl⟩ : syracuseStep 5581943 = 8372915) B8372915
theorem B3721295 : Blo 1959435 3721295 := bstep (se 1 (by rfl) ⟨2790971, by rfl⟩ : syracuseStep 3721295 = 5581943) B5581943
theorem B2480863 : Blo 1959435 2480863 := bstep (se 1 (by rfl) ⟨1860647, by rfl⟩ : syracuseStep 2480863 = 3721295) B3721295
theorem B3307817 : Blo 1959435 3307817 := bstep (se 2 (by rfl) ⟨1240431, by rfl⟩ : syracuseStep 3307817 = 2480863) B2480863
theorem B2205211 : Blo 1959435 2205211 := bstep (se 1 (by rfl) ⟨1653908, by rfl⟩ : syracuseStep 2205211 = 3307817) B3307817
theorem B2940281 : Blo 1959435 2940281 := bstep (se 2 (by rfl) ⟨1102605, by rfl⟩ : syracuseStep 2940281 = 2205211) B2205211
theorem B1960187 : Blo 1959435 1960187 := bstep (se 1 (by rfl) ⟨1470140, by rfl⟩ : syracuseStep 1960187 = 2940281) B2940281
theorem B4709773 : Blo 1959435 4709773 := bbase (se 3 (by rfl) ⟨883082, by rfl⟩ : syracuseStep 4709773 = 1766165) (by norm_num)
theorem B6279697 : Blo 1959435 6279697 := bstep (se 2 (by rfl) ⟨2354886, by rfl⟩ : syracuseStep 6279697 = 4709773) B4709773
theorem B33491717 : Blo 1959435 33491717 := bstep (se 4 (by rfl) ⟨3139848, by rfl⟩ : syracuseStep 33491717 = 6279697) B6279697
theorem B22327811 : Blo 1959435 22327811 := bstep (se 1 (by rfl) ⟨16745858, by rfl⟩ : syracuseStep 22327811 = 33491717) B33491717
theorem B14885207 : Blo 1959435 14885207 := bstep (se 1 (by rfl) ⟨11163905, by rfl⟩ : syracuseStep 14885207 = 22327811) B22327811
theorem B9923471 : Blo 1959435 9923471 := bstep (se 1 (by rfl) ⟨7442603, by rfl⟩ : syracuseStep 9923471 = 14885207) B14885207
theorem B6615647 : Blo 1959435 6615647 := bstep (se 1 (by rfl) ⟨4961735, by rfl⟩ : syracuseStep 6615647 = 9923471) B9923471
theorem B4410431 : Blo 1959435 4410431 := bstep (se 1 (by rfl) ⟨3307823, by rfl⟩ : syracuseStep 4410431 = 6615647) B6615647
theorem B2940287 : Blo 1959435 2940287 := bstep (se 1 (by rfl) ⟨2205215, by rfl⟩ : syracuseStep 2940287 = 4410431) B4410431
theorem B1960191 : Blo 1959435 1960191 := bstep (se 1 (by rfl) ⟨1470143, by rfl⟩ : syracuseStep 1960191 = 2940287) B2940287
theorem B2940293 : Blo 1959435 2940293 := bbase (se 4 (by rfl) ⟨275652, by rfl⟩ : syracuseStep 2940293 = 551305) (by norm_num)
theorem B1960195 : Blo 1959435 1960195 := bstep (se 1 (by rfl) ⟨1470146, by rfl⟩ : syracuseStep 1960195 = 2940293) B2940293
theorem B3307837 : Blo 1959435 3307837 := bbase (se 3 (by rfl) ⟨620219, by rfl⟩ : syracuseStep 3307837 = 1240439) (by norm_num)
theorem B4410449 : Blo 1959435 4410449 := bstep (se 2 (by rfl) ⟨1653918, by rfl⟩ : syracuseStep 4410449 = 3307837) B3307837
theorem B2940299 : Blo 1959435 2940299 := bstep (se 1 (by rfl) ⟨2205224, by rfl⟩ : syracuseStep 2940299 = 4410449) B4410449
theorem B1960199 : Blo 1959435 1960199 := bstep (se 1 (by rfl) ⟨1470149, by rfl⟩ : syracuseStep 1960199 = 2940299) B2940299
theorem B2205229 : Blo 1959435 2205229 := bbase (se 3 (by rfl) ⟨413480, by rfl⟩ : syracuseStep 2205229 = 826961) (by norm_num)
theorem B2940305 : Blo 1959435 2940305 := bstep (se 2 (by rfl) ⟨1102614, by rfl⟩ : syracuseStep 2940305 = 2205229) B2205229
theorem B1960203 : Blo 1959435 1960203 := bstep (se 1 (by rfl) ⟨1470152, by rfl⟩ : syracuseStep 1960203 = 2940305) B2940305
theorem B6615701 : Blo 1959435 6615701 := bbase (se 6 (by rfl) ⟨155055, by rfl⟩ : syracuseStep 6615701 = 310111) (by norm_num)
theorem B4410467 : Blo 1959435 4410467 := bstep (se 1 (by rfl) ⟨3307850, by rfl⟩ : syracuseStep 4410467 = 6615701) B6615701
theorem B2940311 : Blo 1959435 2940311 := bstep (se 1 (by rfl) ⟨2205233, by rfl⟩ : syracuseStep 2940311 = 4410467) B4410467
theorem B1960207 : Blo 1959435 1960207 := bstep (se 1 (by rfl) ⟨1470155, by rfl⟩ : syracuseStep 1960207 = 2940311) B2940311
theorem B2940317 : Blo 1959435 2940317 := bbase (se 3 (by rfl) ⟨551309, by rfl⟩ : syracuseStep 2940317 = 1102619) (by norm_num)
theorem B1960211 : Blo 1959435 1960211 := bstep (se 1 (by rfl) ⟨1470158, by rfl⟩ : syracuseStep 1960211 = 2940317) B2940317
theorem B4410485 : Blo 1959435 4410485 := bbase (se 5 (by rfl) ⟨206741, by rfl⟩ : syracuseStep 4410485 = 413483) (by norm_num)
theorem B2940323 : Blo 1959435 2940323 := bstep (se 1 (by rfl) ⟨2205242, by rfl⟩ : syracuseStep 2940323 = 4410485) B4410485
theorem B1960215 : Blo 1959435 1960215 := bstep (se 1 (by rfl) ⟨1470161, by rfl⟩ : syracuseStep 1960215 = 2940323) B2940323
theorem B16746101 : Blo 1959435 16746101 := bbase (se 5 (by rfl) ⟨784973, by rfl⟩ : syracuseStep 16746101 = 1569947) (by norm_num)
theorem B11164067 : Blo 1959435 11164067 := bstep (se 1 (by rfl) ⟨8373050, by rfl⟩ : syracuseStep 11164067 = 16746101) B16746101
theorem B7442711 : Blo 1959435 7442711 := bstep (se 1 (by rfl) ⟨5582033, by rfl⟩ : syracuseStep 7442711 = 11164067) B11164067
theorem B4961807 : Blo 1959435 4961807 := bstep (se 1 (by rfl) ⟨3721355, by rfl⟩ : syracuseStep 4961807 = 7442711) B7442711
theorem B3307871 : Blo 1959435 3307871 := bstep (se 1 (by rfl) ⟨2480903, by rfl⟩ : syracuseStep 3307871 = 4961807) B4961807
theorem B2205247 : Blo 1959435 2205247 := bstep (se 1 (by rfl) ⟨1653935, by rfl⟩ : syracuseStep 2205247 = 3307871) B3307871
theorem B2940329 : Blo 1959435 2940329 := bstep (se 2 (by rfl) ⟨1102623, by rfl⟩ : syracuseStep 2940329 = 2205247) B2205247
theorem B1960219 : Blo 1959435 1960219 := bstep (se 1 (by rfl) ⟨1470164, by rfl⟩ : syracuseStep 1960219 = 2940329) B2940329
theorem B7442725 : Blo 1959435 7442725 := bbase (se 4 (by rfl) ⟨697755, by rfl⟩ : syracuseStep 7442725 = 1395511) (by norm_num)
theorem B9923633 : Blo 1959435 9923633 := bstep (se 2 (by rfl) ⟨3721362, by rfl⟩ : syracuseStep 9923633 = 7442725) B7442725
theorem B6615755 : Blo 1959435 6615755 := bstep (se 1 (by rfl) ⟨4961816, by rfl⟩ : syracuseStep 6615755 = 9923633) B9923633
theorem B4410503 : Blo 1959435 4410503 := bstep (se 1 (by rfl) ⟨3307877, by rfl⟩ : syracuseStep 4410503 = 6615755) B6615755
theorem B2940335 : Blo 1959435 2940335 := bstep (se 1 (by rfl) ⟨2205251, by rfl⟩ : syracuseStep 2940335 = 4410503) B4410503
theorem B1960223 : Blo 1959435 1960223 := bstep (se 1 (by rfl) ⟨1470167, by rfl⟩ : syracuseStep 1960223 = 2940335) B2940335
theorem B2940341 : Blo 1959435 2940341 := bbase (se 5 (by rfl) ⟨137828, by rfl⟩ : syracuseStep 2940341 = 275657) (by norm_num)
theorem B1960227 : Blo 1959435 1960227 := bstep (se 1 (by rfl) ⟨1470170, by rfl⟩ : syracuseStep 1960227 = 2940341) B2940341
theorem B4961837 : Blo 1959435 4961837 := bbase (se 3 (by rfl) ⟨930344, by rfl⟩ : syracuseStep 4961837 = 1860689) (by norm_num)
theorem B3307891 : Blo 1959435 3307891 := bstep (se 1 (by rfl) ⟨2480918, by rfl⟩ : syracuseStep 3307891 = 4961837) B4961837
theorem B4410521 : Blo 1959435 4410521 := bstep (se 2 (by rfl) ⟨1653945, by rfl⟩ : syracuseStep 4410521 = 3307891) B3307891
theorem B2940347 : Blo 1959435 2940347 := bstep (se 1 (by rfl) ⟨2205260, by rfl⟩ : syracuseStep 2940347 = 4410521) B4410521
theorem B1960231 : Blo 1959435 1960231 := bstep (se 1 (by rfl) ⟨1470173, by rfl⟩ : syracuseStep 1960231 = 2940347) B2940347
theorem B2205265 : Blo 1959435 2205265 := bbase (se 2 (by rfl) ⟨826974, by rfl⟩ : syracuseStep 2205265 = 1653949) (by norm_num)
theorem B2940353 : Blo 1959435 2940353 := bstep (se 2 (by rfl) ⟨1102632, by rfl⟩ : syracuseStep 2940353 = 2205265) B2205265
theorem B1960235 : Blo 1959435 1960235 := bstep (se 1 (by rfl) ⟨1470176, by rfl⟩ : syracuseStep 1960235 = 2940353) B2940353
theorem B2791045 : Blo 1959435 2791045 := bbase (se 4 (by rfl) ⟨261660, by rfl⟩ : syracuseStep 2791045 = 523321) (by norm_num)
theorem B3721393 : Blo 1959435 3721393 := bstep (se 2 (by rfl) ⟨1395522, by rfl⟩ : syracuseStep 3721393 = 2791045) B2791045
theorem B4961857 : Blo 1959435 4961857 := bstep (se 2 (by rfl) ⟨1860696, by rfl⟩ : syracuseStep 4961857 = 3721393) B3721393
theorem B6615809 : Blo 1959435 6615809 := bstep (se 2 (by rfl) ⟨2480928, by rfl⟩ : syracuseStep 6615809 = 4961857) B4961857
theorem B4410539 : Blo 1959435 4410539 := bstep (se 1 (by rfl) ⟨3307904, by rfl⟩ : syracuseStep 4410539 = 6615809) B6615809
theorem B2940359 : Blo 1959435 2940359 := bstep (se 1 (by rfl) ⟨2205269, by rfl⟩ : syracuseStep 2940359 = 4410539) B4410539
theorem B1960239 : Blo 1959435 1960239 := bstep (se 1 (by rfl) ⟨1470179, by rfl⟩ : syracuseStep 1960239 = 2940359) B2940359
theorem B2940365 : Blo 1959435 2940365 := bbase (se 3 (by rfl) ⟨551318, by rfl⟩ : syracuseStep 2940365 = 1102637) (by norm_num)
theorem B1960243 : Blo 1959435 1960243 := bstep (se 1 (by rfl) ⟨1470182, by rfl⟩ : syracuseStep 1960243 = 2940365) B2940365
theorem B4410557 : Blo 1959435 4410557 := bbase (se 3 (by rfl) ⟨826979, by rfl⟩ : syracuseStep 4410557 = 1653959) (by norm_num)
theorem B2940371 : Blo 1959435 2940371 := bstep (se 1 (by rfl) ⟨2205278, by rfl⟩ : syracuseStep 2940371 = 4410557) B4410557
theorem B1960247 : Blo 1959435 1960247 := bstep (se 1 (by rfl) ⟨1470185, by rfl⟩ : syracuseStep 1960247 = 2940371) B2940371
theorem B3307925 : Blo 1959435 3307925 := bbase (se 6 (by rfl) ⟨77529, by rfl⟩ : syracuseStep 3307925 = 155059) (by norm_num)
theorem B2205283 : Blo 1959435 2205283 := bstep (se 1 (by rfl) ⟨1653962, by rfl⟩ : syracuseStep 2205283 = 3307925) B3307925
theorem B2940377 : Blo 1959435 2940377 := bstep (se 2 (by rfl) ⟨1102641, by rfl⟩ : syracuseStep 2940377 = 2205283) B2205283
theorem B1960251 : Blo 1959435 1960251 := bstep (se 1 (by rfl) ⟨1470188, by rfl⟩ : syracuseStep 1960251 = 2940377) B2940377
theorem B11922005 : Blo 1959435 11922005 := bbase (se 8 (by rfl) ⟨69855, by rfl⟩ : syracuseStep 11922005 = 139711) (by norm_num)
theorem B7948003 : Blo 1959435 7948003 := bstep (se 1 (by rfl) ⟨5961002, by rfl⟩ : syracuseStep 7948003 = 11922005) B11922005
theorem B10597337 : Blo 1959435 10597337 := bstep (se 2 (by rfl) ⟨3974001, by rfl⟩ : syracuseStep 10597337 = 7948003) B7948003
theorem B7064891 : Blo 1959435 7064891 := bstep (se 1 (by rfl) ⟨5298668, by rfl⟩ : syracuseStep 7064891 = 10597337) B10597337
theorem B4709927 : Blo 1959435 4709927 := bstep (se 1 (by rfl) ⟨3532445, by rfl⟩ : syracuseStep 4709927 = 7064891) B7064891
theorem B12559805 : Blo 1959435 12559805 := bstep (se 3 (by rfl) ⟨2354963, by rfl⟩ : syracuseStep 12559805 = 4709927) B4709927
theorem B8373203 : Blo 1959435 8373203 := bstep (se 1 (by rfl) ⟨6279902, by rfl⟩ : syracuseStep 8373203 = 12559805) B12559805
theorem B5582135 : Blo 1959435 5582135 := bstep (se 1 (by rfl) ⟨4186601, by rfl⟩ : syracuseStep 5582135 = 8373203) B8373203
theorem B14885693 : Blo 1959435 14885693 := bstep (se 3 (by rfl) ⟨2791067, by rfl⟩ : syracuseStep 14885693 = 5582135) B5582135
theorem B9923795 : Blo 1959435 9923795 := bstep (se 1 (by rfl) ⟨7442846, by rfl⟩ : syracuseStep 9923795 = 14885693) B14885693
theorem B6615863 : Blo 1959435 6615863 := bstep (se 1 (by rfl) ⟨4961897, by rfl⟩ : syracuseStep 6615863 = 9923795) B9923795
theorem B4410575 : Blo 1959435 4410575 := bstep (se 1 (by rfl) ⟨3307931, by rfl⟩ : syracuseStep 4410575 = 6615863) B6615863
theorem B2940383 : Blo 1959435 2940383 := bstep (se 1 (by rfl) ⟨2205287, by rfl⟩ : syracuseStep 2940383 = 4410575) B4410575
theorem B1960255 : Blo 1959435 1960255 := bstep (se 1 (by rfl) ⟨1470191, by rfl⟩ : syracuseStep 1960255 = 2940383) B2940383
theorem B2940389 : Blo 1959435 2940389 := bbase (se 4 (by rfl) ⟨275661, by rfl⟩ : syracuseStep 2940389 = 551323) (by norm_num)
theorem B1960259 : Blo 1959435 1960259 := bstep (se 1 (by rfl) ⟨1470194, by rfl⟩ : syracuseStep 1960259 = 2940389) B2940389
theorem B7948037 : Blo 1959435 7948037 := bbase (se 4 (by rfl) ⟨745128, by rfl⟩ : syracuseStep 7948037 = 1490257) (by norm_num)
theorem B5298691 : Blo 1959435 5298691 := bstep (se 1 (by rfl) ⟨3974018, by rfl⟩ : syracuseStep 5298691 = 7948037) B7948037
theorem B7064921 : Blo 1959435 7064921 := bstep (se 2 (by rfl) ⟨2649345, by rfl⟩ : syracuseStep 7064921 = 5298691) B5298691
theorem B18839789 : Blo 1959435 18839789 := bstep (se 3 (by rfl) ⟨3532460, by rfl⟩ : syracuseStep 18839789 = 7064921) B7064921
theorem B12559859 : Blo 1959435 12559859 := bstep (se 1 (by rfl) ⟨9419894, by rfl⟩ : syracuseStep 12559859 = 18839789) B18839789
theorem B8373239 : Blo 1959435 8373239 := bstep (se 1 (by rfl) ⟨6279929, by rfl⟩ : syracuseStep 8373239 = 12559859) B12559859
theorem B5582159 : Blo 1959435 5582159 := bstep (se 1 (by rfl) ⟨4186619, by rfl⟩ : syracuseStep 5582159 = 8373239) B8373239
theorem B3721439 : Blo 1959435 3721439 := bstep (se 1 (by rfl) ⟨2791079, by rfl⟩ : syracuseStep 3721439 = 5582159) B5582159
theorem B2480959 : Blo 1959435 2480959 := bstep (se 1 (by rfl) ⟨1860719, by rfl⟩ : syracuseStep 2480959 = 3721439) B3721439
theorem B3307945 : Blo 1959435 3307945 := bstep (se 2 (by rfl) ⟨1240479, by rfl⟩ : syracuseStep 3307945 = 2480959) B2480959
theorem B4410593 : Blo 1959435 4410593 := bstep (se 2 (by rfl) ⟨1653972, by rfl⟩ : syracuseStep 4410593 = 3307945) B3307945
theorem B2940395 : Blo 1959435 2940395 := bstep (se 1 (by rfl) ⟨2205296, by rfl⟩ : syracuseStep 2940395 = 4410593) B4410593
theorem B1960263 : Blo 1959435 1960263 := bstep (se 1 (by rfl) ⟨1470197, by rfl⟩ : syracuseStep 1960263 = 2940395) B2940395
theorem B2205301 : Blo 1959435 2205301 := bbase (se 5 (by rfl) ⟨103373, by rfl⟩ : syracuseStep 2205301 = 206747) (by norm_num)
theorem B2940401 : Blo 1959435 2940401 := bstep (se 2 (by rfl) ⟨1102650, by rfl⟩ : syracuseStep 2940401 = 2205301) B2205301
theorem B1960267 : Blo 1959435 1960267 := bstep (se 1 (by rfl) ⟨1470200, by rfl⟩ : syracuseStep 1960267 = 2940401) B2940401
theorem B2480969 : Blo 1959435 2480969 := bbase (se 2 (by rfl) ⟨930363, by rfl⟩ : syracuseStep 2480969 = 1860727) (by norm_num)
theorem B6615917 : Blo 1959435 6615917 := bstep (se 3 (by rfl) ⟨1240484, by rfl⟩ : syracuseStep 6615917 = 2480969) B2480969
theorem B4410611 : Blo 1959435 4410611 := bstep (se 1 (by rfl) ⟨3307958, by rfl⟩ : syracuseStep 4410611 = 6615917) B6615917
theorem B2940407 : Blo 1959435 2940407 := bstep (se 1 (by rfl) ⟨2205305, by rfl⟩ : syracuseStep 2940407 = 4410611) B4410611
theorem B1960271 : Blo 1959435 1960271 := bstep (se 1 (by rfl) ⟨1470203, by rfl⟩ : syracuseStep 1960271 = 2940407) B2940407
theorem B2940413 : Blo 1959435 2940413 := bbase (se 3 (by rfl) ⟨551327, by rfl⟩ : syracuseStep 2940413 = 1102655) (by norm_num)
theorem B1960275 : Blo 1959435 1960275 := bstep (se 1 (by rfl) ⟨1470206, by rfl⟩ : syracuseStep 1960275 = 2940413) B2940413
theorem B4410629 : Blo 1959435 4410629 := bbase (se 4 (by rfl) ⟨413496, by rfl⟩ : syracuseStep 4410629 = 826993) (by norm_num)
theorem B2940419 : Blo 1959435 2940419 := bstep (se 1 (by rfl) ⟨2205314, by rfl⟩ : syracuseStep 2940419 = 4410629) B4410629
theorem B1960279 : Blo 1959435 1960279 := bstep (se 1 (by rfl) ⟨1470209, by rfl⟩ : syracuseStep 1960279 = 2940419) B2940419
theorem B3721477 : Blo 1959435 3721477 := bbase (se 4 (by rfl) ⟨348888, by rfl⟩ : syracuseStep 3721477 = 697777) (by norm_num)
theorem B4961969 : Blo 1959435 4961969 := bstep (se 2 (by rfl) ⟨1860738, by rfl⟩ : syracuseStep 4961969 = 3721477) B3721477
theorem B3307979 : Blo 1959435 3307979 := bstep (se 1 (by rfl) ⟨2480984, by rfl⟩ : syracuseStep 3307979 = 4961969) B4961969
theorem B2205319 : Blo 1959435 2205319 := bstep (se 1 (by rfl) ⟨1653989, by rfl⟩ : syracuseStep 2205319 = 3307979) B3307979
theorem B2940425 : Blo 1959435 2940425 := bstep (se 2 (by rfl) ⟨1102659, by rfl⟩ : syracuseStep 2940425 = 2205319) B2205319
theorem B1960283 : Blo 1959435 1960283 := bstep (se 1 (by rfl) ⟨1470212, by rfl⟩ : syracuseStep 1960283 = 2940425) B2940425
theorem B9923957 : Blo 1959435 9923957 := bbase (se 5 (by rfl) ⟨465185, by rfl⟩ : syracuseStep 9923957 = 930371) (by norm_num)
theorem B6615971 : Blo 1959435 6615971 := bstep (se 1 (by rfl) ⟨4961978, by rfl⟩ : syracuseStep 6615971 = 9923957) B9923957
theorem B4410647 : Blo 1959435 4410647 := bstep (se 1 (by rfl) ⟨3307985, by rfl⟩ : syracuseStep 4410647 = 6615971) B6615971
theorem B2940431 : Blo 1959435 2940431 := bstep (se 1 (by rfl) ⟨2205323, by rfl⟩ : syracuseStep 2940431 = 4410647) B4410647
theorem B1960287 : Blo 1959435 1960287 := bstep (se 1 (by rfl) ⟨1470215, by rfl⟩ : syracuseStep 1960287 = 2940431) B2940431
theorem B2940437 : Blo 1959435 2940437 := bbase (se 6 (by rfl) ⟨68916, by rfl⟩ : syracuseStep 2940437 = 137833) (by norm_num)
theorem B1960291 : Blo 1959435 1960291 := bstep (se 1 (by rfl) ⟨1470218, by rfl⟩ : syracuseStep 1960291 = 2940437) B2940437
theorem B31792661 : Blo 1959435 31792661 := bbase (se 6 (by rfl) ⟨745140, by rfl⟩ : syracuseStep 31792661 = 1490281) (by norm_num)
theorem B21195107 : Blo 1959435 21195107 := bstep (se 1 (by rfl) ⟨15896330, by rfl⟩ : syracuseStep 21195107 = 31792661) B31792661
theorem B14130071 : Blo 1959435 14130071 := bstep (se 1 (by rfl) ⟨10597553, by rfl⟩ : syracuseStep 14130071 = 21195107) B21195107
theorem B9420047 : Blo 1959435 9420047 := bstep (se 1 (by rfl) ⟨7065035, by rfl⟩ : syracuseStep 9420047 = 14130071) B14130071
theorem B6280031 : Blo 1959435 6280031 := bstep (se 1 (by rfl) ⟨4710023, by rfl⟩ : syracuseStep 6280031 = 9420047) B9420047
theorem B16746749 : Blo 1959435 16746749 := bstep (se 3 (by rfl) ⟨3140015, by rfl⟩ : syracuseStep 16746749 = 6280031) B6280031
theorem B11164499 : Blo 1959435 11164499 := bstep (se 1 (by rfl) ⟨8373374, by rfl⟩ : syracuseStep 11164499 = 16746749) B16746749
theorem B7442999 : Blo 1959435 7442999 := bstep (se 1 (by rfl) ⟨5582249, by rfl⟩ : syracuseStep 7442999 = 11164499) B11164499
theorem B4961999 : Blo 1959435 4961999 := bstep (se 1 (by rfl) ⟨3721499, by rfl⟩ : syracuseStep 4961999 = 7442999) B7442999
theorem B3307999 : Blo 1959435 3307999 := bstep (se 1 (by rfl) ⟨2480999, by rfl⟩ : syracuseStep 3307999 = 4961999) B4961999
theorem B4410665 : Blo 1959435 4410665 := bstep (se 2 (by rfl) ⟨1653999, by rfl⟩ : syracuseStep 4410665 = 3307999) B3307999
theorem B2940443 : Blo 1959435 2940443 := bstep (se 1 (by rfl) ⟨2205332, by rfl⟩ : syracuseStep 2940443 = 4410665) B4410665
theorem B1960295 : Blo 1959435 1960295 := bstep (se 1 (by rfl) ⟨1470221, by rfl⟩ : syracuseStep 1960295 = 2940443) B2940443
theorem B2205337 : Blo 1959435 2205337 := bbase (se 2 (by rfl) ⟨827001, by rfl⟩ : syracuseStep 2205337 = 1654003) (by norm_num)
theorem B2940449 : Blo 1959435 2940449 := bstep (se 2 (by rfl) ⟨1102668, by rfl⟩ : syracuseStep 2940449 = 2205337) B2205337
theorem B1960299 : Blo 1959435 1960299 := bstep (se 1 (by rfl) ⟨1470224, by rfl⟩ : syracuseStep 1960299 = 2940449) B2940449
theorem B7443029 : Blo 1959435 7443029 := bbase (se 8 (by rfl) ⟨43611, by rfl⟩ : syracuseStep 7443029 = 87223) (by norm_num)
theorem B4962019 : Blo 1959435 4962019 := bstep (se 1 (by rfl) ⟨3721514, by rfl⟩ : syracuseStep 4962019 = 7443029) B7443029
theorem B6616025 : Blo 1959435 6616025 := bstep (se 2 (by rfl) ⟨2481009, by rfl⟩ : syracuseStep 6616025 = 4962019) B4962019
theorem B4410683 : Blo 1959435 4410683 := bstep (se 1 (by rfl) ⟨3308012, by rfl⟩ : syracuseStep 4410683 = 6616025) B6616025
theorem B2940455 : Blo 1959435 2940455 := bstep (se 1 (by rfl) ⟨2205341, by rfl⟩ : syracuseStep 2940455 = 4410683) B4410683
theorem B1960303 : Blo 1959435 1960303 := bstep (se 1 (by rfl) ⟨1470227, by rfl⟩ : syracuseStep 1960303 = 2940455) B2940455
theorem B2940461 : Blo 1959435 2940461 := bbase (se 3 (by rfl) ⟨551336, by rfl⟩ : syracuseStep 2940461 = 1102673) (by norm_num)
theorem B1960307 : Blo 1959435 1960307 := bstep (se 1 (by rfl) ⟨1470230, by rfl⟩ : syracuseStep 1960307 = 2940461) B2940461
theorem B4410701 : Blo 1959435 4410701 := bbase (se 3 (by rfl) ⟨827006, by rfl⟩ : syracuseStep 4410701 = 1654013) (by norm_num)
theorem B2940467 : Blo 1959435 2940467 := bstep (se 1 (by rfl) ⟨2205350, by rfl⟩ : syracuseStep 2940467 = 4410701) B4410701
theorem B1960311 : Blo 1959435 1960311 := bstep (se 1 (by rfl) ⟨1470233, by rfl⟩ : syracuseStep 1960311 = 2940467) B2940467
theorem B2481025 : Blo 1959435 2481025 := bbase (se 2 (by rfl) ⟨930384, by rfl⟩ : syracuseStep 2481025 = 1860769) (by norm_num)
theorem B3308033 : Blo 1959435 3308033 := bstep (se 2 (by rfl) ⟨1240512, by rfl⟩ : syracuseStep 3308033 = 2481025) B2481025
theorem B2205355 : Blo 1959435 2205355 := bstep (se 1 (by rfl) ⟨1654016, by rfl⟩ : syracuseStep 2205355 = 3308033) B3308033
theorem B2940473 : Blo 1959435 2940473 := bstep (se 2 (by rfl) ⟨1102677, by rfl⟩ : syracuseStep 2940473 = 2205355) B2205355
theorem B1960315 : Blo 1959435 1960315 := bstep (se 1 (by rfl) ⟨1470236, by rfl⟩ : syracuseStep 1960315 = 2940473) B2940473
theorem B2093369 : Blo 1959435 2093369 := bbase (se 2 (by rfl) ⟨785013, by rfl⟩ : syracuseStep 2093369 = 1570027) (by norm_num)
theorem B22329269 : Blo 1959435 22329269 := bstep (se 5 (by rfl) ⟨1046684, by rfl⟩ : syracuseStep 22329269 = 2093369) B2093369
theorem B14886179 : Blo 1959435 14886179 := bstep (se 1 (by rfl) ⟨11164634, by rfl⟩ : syracuseStep 14886179 = 22329269) B22329269
theorem B9924119 : Blo 1959435 9924119 := bstep (se 1 (by rfl) ⟨7443089, by rfl⟩ : syracuseStep 9924119 = 14886179) B14886179
theorem B6616079 : Blo 1959435 6616079 := bstep (se 1 (by rfl) ⟨4962059, by rfl⟩ : syracuseStep 6616079 = 9924119) B9924119
theorem B4410719 : Blo 1959435 4410719 := bstep (se 1 (by rfl) ⟨3308039, by rfl⟩ : syracuseStep 4410719 = 6616079) B6616079
theorem B2940479 : Blo 1959435 2940479 := bstep (se 1 (by rfl) ⟨2205359, by rfl⟩ : syracuseStep 2940479 = 4410719) B4410719
theorem B1960319 : Blo 1959435 1960319 := bstep (se 1 (by rfl) ⟨1470239, by rfl⟩ : syracuseStep 1960319 = 2940479) B2940479
theorem B2940485 : Blo 1959435 2940485 := bbase (se 4 (by rfl) ⟨275670, by rfl⟩ : syracuseStep 2940485 = 551341) (by norm_num)
theorem B1960323 : Blo 1959435 1960323 := bstep (se 1 (by rfl) ⟨1470242, by rfl⟩ : syracuseStep 1960323 = 2940485) B2940485
theorem B3308053 : Blo 1959435 3308053 := bbase (se 6 (by rfl) ⟨77532, by rfl⟩ : syracuseStep 3308053 = 155065) (by norm_num)
theorem B4410737 : Blo 1959435 4410737 := bstep (se 2 (by rfl) ⟨1654026, by rfl⟩ : syracuseStep 4410737 = 3308053) B3308053
theorem B2940491 : Blo 1959435 2940491 := bstep (se 1 (by rfl) ⟨2205368, by rfl⟩ : syracuseStep 2940491 = 4410737) B4410737
theorem B1960327 : Blo 1959435 1960327 := bstep (se 1 (by rfl) ⟨1470245, by rfl⟩ : syracuseStep 1960327 = 2940491) B2940491
theorem B2205373 : Blo 1959435 2205373 := bbase (se 3 (by rfl) ⟨413507, by rfl⟩ : syracuseStep 2205373 = 827015) (by norm_num)
theorem B2940497 : Blo 1959435 2940497 := bstep (se 2 (by rfl) ⟨1102686, by rfl⟩ : syracuseStep 2940497 = 2205373) B2205373
theorem B1960331 : Blo 1959435 1960331 := bstep (se 1 (by rfl) ⟨1470248, by rfl⟩ : syracuseStep 1960331 = 2940497) B2940497
theorem B6616133 : Blo 1959435 6616133 := bbase (se 4 (by rfl) ⟨620262, by rfl⟩ : syracuseStep 6616133 = 1240525) (by norm_num)
theorem B4410755 : Blo 1959435 4410755 := bstep (se 1 (by rfl) ⟨3308066, by rfl⟩ : syracuseStep 4410755 = 6616133) B6616133
theorem B2940503 : Blo 1959435 2940503 := bstep (se 1 (by rfl) ⟨2205377, by rfl⟩ : syracuseStep 2940503 = 4410755) B4410755
theorem B1960335 : Blo 1959435 1960335 := bstep (se 1 (by rfl) ⟨1470251, by rfl⟩ : syracuseStep 1960335 = 2940503) B2940503
theorem B2940509 : Blo 1959435 2940509 := bbase (se 3 (by rfl) ⟨551345, by rfl⟩ : syracuseStep 2940509 = 1102691) (by norm_num)
theorem B1960339 : Blo 1959435 1960339 := bstep (se 1 (by rfl) ⟨1470254, by rfl⟩ : syracuseStep 1960339 = 2940509) B2940509
theorem B4410773 : Blo 1959435 4410773 := bbase (se 6 (by rfl) ⟨103377, by rfl⟩ : syracuseStep 4410773 = 206755) (by norm_num)
theorem B2940515 : Blo 1959435 2940515 := bstep (se 1 (by rfl) ⟨2205386, by rfl⟩ : syracuseStep 2940515 = 4410773) B4410773
theorem B1960343 : Blo 1959435 1960343 := bstep (se 1 (by rfl) ⟨1470257, by rfl⟩ : syracuseStep 1960343 = 2940515) B2940515
theorem B3974189 : Blo 1959435 3974189 := bbase (se 3 (by rfl) ⟨745160, by rfl⟩ : syracuseStep 3974189 = 1490321) (by norm_num)
theorem B10597837 : Blo 1959435 10597837 := bstep (se 3 (by rfl) ⟨1987094, by rfl⟩ : syracuseStep 10597837 = 3974189) B3974189
theorem B14130449 : Blo 1959435 14130449 := bstep (se 2 (by rfl) ⟨5298918, by rfl⟩ : syracuseStep 14130449 = 10597837) B10597837
theorem B9420299 : Blo 1959435 9420299 := bstep (se 1 (by rfl) ⟨7065224, by rfl⟩ : syracuseStep 9420299 = 14130449) B14130449
theorem B6280199 : Blo 1959435 6280199 := bstep (se 1 (by rfl) ⟨4710149, by rfl⟩ : syracuseStep 6280199 = 9420299) B9420299
theorem B4186799 : Blo 1959435 4186799 := bstep (se 1 (by rfl) ⟨3140099, by rfl⟩ : syracuseStep 4186799 = 6280199) B6280199
theorem B2791199 : Blo 1959435 2791199 := bstep (se 1 (by rfl) ⟨2093399, by rfl⟩ : syracuseStep 2791199 = 4186799) B4186799
theorem B7443197 : Blo 1959435 7443197 := bstep (se 3 (by rfl) ⟨1395599, by rfl⟩ : syracuseStep 7443197 = 2791199) B2791199
theorem B4962131 : Blo 1959435 4962131 := bstep (se 1 (by rfl) ⟨3721598, by rfl⟩ : syracuseStep 4962131 = 7443197) B7443197
theorem B3308087 : Blo 1959435 3308087 := bstep (se 1 (by rfl) ⟨2481065, by rfl⟩ : syracuseStep 3308087 = 4962131) B4962131
theorem B2205391 : Blo 1959435 2205391 := bstep (se 1 (by rfl) ⟨1654043, by rfl⟩ : syracuseStep 2205391 = 3308087) B3308087
theorem B2940521 : Blo 1959435 2940521 := bstep (se 2 (by rfl) ⟨1102695, by rfl⟩ : syracuseStep 2940521 = 2205391) B2205391
theorem B1960347 : Blo 1959435 1960347 := bstep (se 1 (by rfl) ⟨1470260, by rfl⟩ : syracuseStep 1960347 = 2940521) B2940521
theorem B3974197 : Blo 1959435 3974197 := bbase (se 5 (by rfl) ⟨186290, by rfl⟩ : syracuseStep 3974197 = 372581) (by norm_num)
theorem B5298929 : Blo 1959435 5298929 := bstep (se 2 (by rfl) ⟨1987098, by rfl⟩ : syracuseStep 5298929 = 3974197) B3974197
theorem B3532619 : Blo 1959435 3532619 := bstep (se 1 (by rfl) ⟨2649464, by rfl⟩ : syracuseStep 3532619 = 5298929) B5298929
theorem B2355079 : Blo 1959435 2355079 := bstep (se 1 (by rfl) ⟨1766309, by rfl⟩ : syracuseStep 2355079 = 3532619) B3532619
theorem B3140105 : Blo 1959435 3140105 := bstep (se 2 (by rfl) ⟨1177539, by rfl⟩ : syracuseStep 3140105 = 2355079) B2355079
theorem B8373613 : Blo 1959435 8373613 := bstep (se 3 (by rfl) ⟨1570052, by rfl⟩ : syracuseStep 8373613 = 3140105) B3140105
theorem B11164817 : Blo 1959435 11164817 := bstep (se 2 (by rfl) ⟨4186806, by rfl⟩ : syracuseStep 11164817 = 8373613) B8373613
theorem B7443211 : Blo 1959435 7443211 := bstep (se 1 (by rfl) ⟨5582408, by rfl⟩ : syracuseStep 7443211 = 11164817) B11164817
theorem B9924281 : Blo 1959435 9924281 := bstep (se 2 (by rfl) ⟨3721605, by rfl⟩ : syracuseStep 9924281 = 7443211) B7443211
theorem B6616187 : Blo 1959435 6616187 := bstep (se 1 (by rfl) ⟨4962140, by rfl⟩ : syracuseStep 6616187 = 9924281) B9924281
theorem B4410791 : Blo 1959435 4410791 := bstep (se 1 (by rfl) ⟨3308093, by rfl⟩ : syracuseStep 4410791 = 6616187) B6616187
theorem B2940527 : Blo 1959435 2940527 := bstep (se 1 (by rfl) ⟨2205395, by rfl⟩ : syracuseStep 2940527 = 4410791) B4410791
theorem B1960351 : Blo 1959435 1960351 := bstep (se 1 (by rfl) ⟨1470263, by rfl⟩ : syracuseStep 1960351 = 2940527) B2940527
theorem B2940533 : Blo 1959435 2940533 := bbase (se 5 (by rfl) ⟨137837, by rfl⟩ : syracuseStep 2940533 = 275675) (by norm_num)
theorem B1960355 : Blo 1959435 1960355 := bstep (se 1 (by rfl) ⟨1470266, by rfl⟩ : syracuseStep 1960355 = 2940533) B2940533
theorem B3721621 : Blo 1959435 3721621 := bbase (se 6 (by rfl) ⟨87225, by rfl⟩ : syracuseStep 3721621 = 174451) (by norm_num)
theorem B4962161 : Blo 1959435 4962161 := bstep (se 2 (by rfl) ⟨1860810, by rfl⟩ : syracuseStep 4962161 = 3721621) B3721621
theorem B3308107 : Blo 1959435 3308107 := bstep (se 1 (by rfl) ⟨2481080, by rfl⟩ : syracuseStep 3308107 = 4962161) B4962161
theorem B4410809 : Blo 1959435 4410809 := bstep (se 2 (by rfl) ⟨1654053, by rfl⟩ : syracuseStep 4410809 = 3308107) B3308107
theorem B2940539 : Blo 1959435 2940539 := bstep (se 1 (by rfl) ⟨2205404, by rfl⟩ : syracuseStep 2940539 = 4410809) B4410809
theorem B1960359 : Blo 1959435 1960359 := bstep (se 1 (by rfl) ⟨1470269, by rfl⟩ : syracuseStep 1960359 = 2940539) B2940539
theorem B2205409 : Blo 1959435 2205409 := bbase (se 2 (by rfl) ⟨827028, by rfl⟩ : syracuseStep 2205409 = 1654057) (by norm_num)
theorem B2940545 : Blo 1959435 2940545 := bstep (se 2 (by rfl) ⟨1102704, by rfl⟩ : syracuseStep 2940545 = 2205409) B2205409
theorem B1960363 : Blo 1959435 1960363 := bstep (se 1 (by rfl) ⟨1470272, by rfl⟩ : syracuseStep 1960363 = 2940545) B2940545
theorem B4962181 : Blo 1959435 4962181 := bbase (se 4 (by rfl) ⟨465204, by rfl⟩ : syracuseStep 4962181 = 930409) (by norm_num)
theorem B6616241 : Blo 1959435 6616241 := bstep (se 2 (by rfl) ⟨2481090, by rfl⟩ : syracuseStep 6616241 = 4962181) B4962181
theorem B4410827 : Blo 1959435 4410827 := bstep (se 1 (by rfl) ⟨3308120, by rfl⟩ : syracuseStep 4410827 = 6616241) B6616241
theorem B2940551 : Blo 1959435 2940551 := bstep (se 1 (by rfl) ⟨2205413, by rfl⟩ : syracuseStep 2940551 = 4410827) B4410827
theorem B1960367 : Blo 1959435 1960367 := bstep (se 1 (by rfl) ⟨1470275, by rfl⟩ : syracuseStep 1960367 = 2940551) B2940551
theorem B2940557 : Blo 1959435 2940557 := bbase (se 3 (by rfl) ⟨551354, by rfl⟩ : syracuseStep 2940557 = 1102709) (by norm_num)
theorem B1960371 : Blo 1959435 1960371 := bstep (se 1 (by rfl) ⟨1470278, by rfl⟩ : syracuseStep 1960371 = 2940557) B2940557
theorem B4410845 : Blo 1959435 4410845 := bbase (se 3 (by rfl) ⟨827033, by rfl⟩ : syracuseStep 4410845 = 1654067) (by norm_num)
theorem B2940563 : Blo 1959435 2940563 := bstep (se 1 (by rfl) ⟨2205422, by rfl⟩ : syracuseStep 2940563 = 4410845) B4410845
theorem B1960375 : Blo 1959435 1960375 := bstep (se 1 (by rfl) ⟨1470281, by rfl⟩ : syracuseStep 1960375 = 2940563) B2940563
theorem B3308141 : Blo 1959435 3308141 := bbase (se 3 (by rfl) ⟨620276, by rfl⟩ : syracuseStep 3308141 = 1240553) (by norm_num)
theorem B2205427 : Blo 1959435 2205427 := bstep (se 1 (by rfl) ⟨1654070, by rfl⟩ : syracuseStep 2205427 = 3308141) B3308141
theorem B2940569 : Blo 1959435 2940569 := bstep (se 2 (by rfl) ⟨1102713, by rfl⟩ : syracuseStep 2940569 = 2205427) B2205427
theorem B1960379 : Blo 1959435 1960379 := bstep (se 1 (by rfl) ⟨1470284, by rfl⟩ : syracuseStep 1960379 = 2940569) B2940569
theorem B6706565 : Blo 1959435 6706565 := bbase (se 4 (by rfl) ⟨628740, by rfl⟩ : syracuseStep 6706565 = 1257481) (by norm_num)
theorem B4471043 : Blo 1959435 4471043 := bstep (se 1 (by rfl) ⟨3353282, by rfl⟩ : syracuseStep 4471043 = 6706565) B6706565
theorem B47691125 : Blo 1959435 47691125 := bstep (se 5 (by rfl) ⟨2235521, by rfl⟩ : syracuseStep 47691125 = 4471043) B4471043
theorem B31794083 : Blo 1959435 31794083 := bstep (se 1 (by rfl) ⟨23845562, by rfl⟩ : syracuseStep 31794083 = 47691125) B47691125
theorem B21196055 : Blo 1959435 21196055 := bstep (se 1 (by rfl) ⟨15897041, by rfl⟩ : syracuseStep 21196055 = 31794083) B31794083
theorem B14130703 : Blo 1959435 14130703 := bstep (se 1 (by rfl) ⟨10598027, by rfl⟩ : syracuseStep 14130703 = 21196055) B21196055
theorem B18840937 : Blo 1959435 18840937 := bstep (se 2 (by rfl) ⟨7065351, by rfl⟩ : syracuseStep 18840937 = 14130703) B14130703
theorem B25121249 : Blo 1959435 25121249 := bstep (se 2 (by rfl) ⟨9420468, by rfl⟩ : syracuseStep 25121249 = 18840937) B18840937
theorem B16747499 : Blo 1959435 16747499 := bstep (se 1 (by rfl) ⟨12560624, by rfl⟩ : syracuseStep 16747499 = 25121249) B25121249
theorem B11164999 : Blo 1959435 11164999 := bstep (se 1 (by rfl) ⟨8373749, by rfl⟩ : syracuseStep 11164999 = 16747499) B16747499
theorem B14886665 : Blo 1959435 14886665 := bstep (se 2 (by rfl) ⟨5582499, by rfl⟩ : syracuseStep 14886665 = 11164999) B11164999
theorem B9924443 : Blo 1959435 9924443 := bstep (se 1 (by rfl) ⟨7443332, by rfl⟩ : syracuseStep 9924443 = 14886665) B14886665
theorem B6616295 : Blo 1959435 6616295 := bstep (se 1 (by rfl) ⟨4962221, by rfl⟩ : syracuseStep 6616295 = 9924443) B9924443
theorem B4410863 : Blo 1959435 4410863 := bstep (se 1 (by rfl) ⟨3308147, by rfl⟩ : syracuseStep 4410863 = 6616295) B6616295
theorem B2940575 : Blo 1959435 2940575 := bstep (se 1 (by rfl) ⟨2205431, by rfl⟩ : syracuseStep 2940575 = 4410863) B4410863
theorem B1960383 : Blo 1959435 1960383 := bstep (se 1 (by rfl) ⟨1470287, by rfl⟩ : syracuseStep 1960383 = 2940575) B2940575
theorem B2940581 : Blo 1959435 2940581 := bbase (se 4 (by rfl) ⟨275679, by rfl⟩ : syracuseStep 2940581 = 551359) (by norm_num)
theorem B1960387 : Blo 1959435 1960387 := bstep (se 1 (by rfl) ⟨1470290, by rfl⟩ : syracuseStep 1960387 = 2940581) B2940581
theorem B2481121 : Blo 1959435 2481121 := bbase (se 2 (by rfl) ⟨930420, by rfl⟩ : syracuseStep 2481121 = 1860841) (by norm_num)
theorem B3308161 : Blo 1959435 3308161 := bstep (se 2 (by rfl) ⟨1240560, by rfl⟩ : syracuseStep 3308161 = 2481121) B2481121
theorem B4410881 : Blo 1959435 4410881 := bstep (se 2 (by rfl) ⟨1654080, by rfl⟩ : syracuseStep 4410881 = 3308161) B3308161
theorem B2940587 : Blo 1959435 2940587 := bstep (se 1 (by rfl) ⟨2205440, by rfl⟩ : syracuseStep 2940587 = 4410881) B4410881
theorem B1960391 : Blo 1959435 1960391 := bstep (se 1 (by rfl) ⟨1470293, by rfl⟩ : syracuseStep 1960391 = 2940587) B2940587
theorem B2205445 : Blo 1959435 2205445 := bbase (se 4 (by rfl) ⟨206760, by rfl⟩ : syracuseStep 2205445 = 413521) (by norm_num)
theorem B2940593 : Blo 1959435 2940593 := bstep (se 2 (by rfl) ⟨1102722, by rfl⟩ : syracuseStep 2940593 = 2205445) B2205445
theorem B1960395 : Blo 1959435 1960395 := bstep (se 1 (by rfl) ⟨1470296, by rfl⟩ : syracuseStep 1960395 = 2940593) B2940593
theorem B7065413 : Blo 1959435 7065413 := bbase (se 4 (by rfl) ⟨662382, by rfl⟩ : syracuseStep 7065413 = 1324765) (by norm_num)
theorem B4710275 : Blo 1959435 4710275 := bstep (se 1 (by rfl) ⟨3532706, by rfl⟩ : syracuseStep 4710275 = 7065413) B7065413
theorem B3140183 : Blo 1959435 3140183 := bstep (se 1 (by rfl) ⟨2355137, by rfl⟩ : syracuseStep 3140183 = 4710275) B4710275
theorem B2093455 : Blo 1959435 2093455 := bstep (se 1 (by rfl) ⟨1570091, by rfl⟩ : syracuseStep 2093455 = 3140183) B3140183
theorem B2791273 : Blo 1959435 2791273 := bstep (se 2 (by rfl) ⟨1046727, by rfl⟩ : syracuseStep 2791273 = 2093455) B2093455
theorem B3721697 : Blo 1959435 3721697 := bstep (se 2 (by rfl) ⟨1395636, by rfl⟩ : syracuseStep 3721697 = 2791273) B2791273
theorem B2481131 : Blo 1959435 2481131 := bstep (se 1 (by rfl) ⟨1860848, by rfl⟩ : syracuseStep 2481131 = 3721697) B3721697
theorem B6616349 : Blo 1959435 6616349 := bstep (se 3 (by rfl) ⟨1240565, by rfl⟩ : syracuseStep 6616349 = 2481131) B2481131
theorem B4410899 : Blo 1959435 4410899 := bstep (se 1 (by rfl) ⟨3308174, by rfl⟩ : syracuseStep 4410899 = 6616349) B6616349
theorem B2940599 : Blo 1959435 2940599 := bstep (se 1 (by rfl) ⟨2205449, by rfl⟩ : syracuseStep 2940599 = 4410899) B4410899
theorem B1960399 : Blo 1959435 1960399 := bstep (se 1 (by rfl) ⟨1470299, by rfl⟩ : syracuseStep 1960399 = 2940599) B2940599
theorem B2940605 : Blo 1959435 2940605 := bbase (se 3 (by rfl) ⟨551363, by rfl⟩ : syracuseStep 2940605 = 1102727) (by norm_num)
theorem B1960403 : Blo 1959435 1960403 := bstep (se 1 (by rfl) ⟨1470302, by rfl⟩ : syracuseStep 1960403 = 2940605) B2940605
theorem B4410917 : Blo 1959435 4410917 := bbase (se 4 (by rfl) ⟨413523, by rfl⟩ : syracuseStep 4410917 = 827047) (by norm_num)
theorem B2940611 : Blo 1959435 2940611 := bstep (se 1 (by rfl) ⟨2205458, by rfl⟩ : syracuseStep 2940611 = 4410917) B4410917
theorem B1960407 : Blo 1959435 1960407 := bstep (se 1 (by rfl) ⟨1470305, by rfl⟩ : syracuseStep 1960407 = 2940611) B2940611
theorem B4962293 : Blo 1959435 4962293 := bbase (se 5 (by rfl) ⟨232607, by rfl⟩ : syracuseStep 4962293 = 465215) (by norm_num)
theorem B3308195 : Blo 1959435 3308195 := bstep (se 1 (by rfl) ⟨2481146, by rfl⟩ : syracuseStep 3308195 = 4962293) B4962293
theorem B2205463 : Blo 1959435 2205463 := bstep (se 1 (by rfl) ⟨1654097, by rfl⟩ : syracuseStep 2205463 = 3308195) B3308195
theorem B2940617 : Blo 1959435 2940617 := bstep (se 2 (by rfl) ⟨1102731, by rfl⟩ : syracuseStep 2940617 = 2205463) B2205463
theorem B1960411 : Blo 1959435 1960411 := bstep (se 1 (by rfl) ⟨1470308, by rfl⟩ : syracuseStep 1960411 = 2940617) B2940617
theorem B4028549 : Blo 1959435 4028549 := bbase (se 4 (by rfl) ⟨377676, by rfl⟩ : syracuseStep 4028549 = 755353) (by norm_num)
theorem B10742797 : Blo 1959435 10742797 := bstep (se 3 (by rfl) ⟨2014274, by rfl⟩ : syracuseStep 10742797 = 4028549) B4028549
theorem B14323729 : Blo 1959435 14323729 := bstep (se 2 (by rfl) ⟨5371398, by rfl⟩ : syracuseStep 14323729 = 10742797) B10742797
theorem B19098305 : Blo 1959435 19098305 := bstep (se 2 (by rfl) ⟨7161864, by rfl⟩ : syracuseStep 19098305 = 14323729) B14323729
theorem B12732203 : Blo 1959435 12732203 := bstep (se 1 (by rfl) ⟨9549152, by rfl⟩ : syracuseStep 12732203 = 19098305) B19098305
theorem B33952541 : Blo 1959435 33952541 := bstep (se 3 (by rfl) ⟨6366101, by rfl⟩ : syracuseStep 33952541 = 12732203) B12732203
theorem B90540109 : Blo 1959435 90540109 := bstep (se 3 (by rfl) ⟨16976270, by rfl⟩ : syracuseStep 90540109 = 33952541) B33952541
theorem B120720145 : Blo 1959435 120720145 := bstep (se 2 (by rfl) ⟨45270054, by rfl⟩ : syracuseStep 120720145 = 90540109) B90540109
theorem B160960193 : Blo 1959435 160960193 := bstep (se 2 (by rfl) ⟨60360072, by rfl⟩ : syracuseStep 160960193 = 120720145) B120720145
theorem B107306795 : Blo 1959435 107306795 := bstep (se 1 (by rfl) ⟨80480096, by rfl⟩ : syracuseStep 107306795 = 160960193) B160960193
theorem B71537863 : Blo 1959435 71537863 := bstep (se 1 (by rfl) ⟨53653397, by rfl⟩ : syracuseStep 71537863 = 107306795) B107306795
theorem B95383817 : Blo 1959435 95383817 := bstep (se 2 (by rfl) ⟨35768931, by rfl⟩ : syracuseStep 95383817 = 71537863) B71537863
theorem B63589211 : Blo 1959435 63589211 := bstep (se 1 (by rfl) ⟨47691908, by rfl⟩ : syracuseStep 63589211 = 95383817) B95383817
theorem B42392807 : Blo 1959435 42392807 := bstep (se 1 (by rfl) ⟨31794605, by rfl⟩ : syracuseStep 42392807 = 63589211) B63589211
theorem B28261871 : Blo 1959435 28261871 := bstep (se 1 (by rfl) ⟨21196403, by rfl⟩ : syracuseStep 28261871 = 42392807) B42392807
theorem B18841247 : Blo 1959435 18841247 := bstep (se 1 (by rfl) ⟨14130935, by rfl⟩ : syracuseStep 18841247 = 28261871) B28261871
theorem B12560831 : Blo 1959435 12560831 := bstep (se 1 (by rfl) ⟨9420623, by rfl⟩ : syracuseStep 12560831 = 18841247) B18841247
theorem B8373887 : Blo 1959435 8373887 := bstep (se 1 (by rfl) ⟨6280415, by rfl⟩ : syracuseStep 8373887 = 12560831) B12560831
theorem B5582591 : Blo 1959435 5582591 := bstep (se 1 (by rfl) ⟨4186943, by rfl⟩ : syracuseStep 5582591 = 8373887) B8373887
theorem B3721727 : Blo 1959435 3721727 := bstep (se 1 (by rfl) ⟨2791295, by rfl⟩ : syracuseStep 3721727 = 5582591) B5582591
theorem B9924605 : Blo 1959435 9924605 := bstep (se 3 (by rfl) ⟨1860863, by rfl⟩ : syracuseStep 9924605 = 3721727) B3721727
theorem B6616403 : Blo 1959435 6616403 := bstep (se 1 (by rfl) ⟨4962302, by rfl⟩ : syracuseStep 6616403 = 9924605) B9924605
theorem B4410935 : Blo 1959435 4410935 := bstep (se 1 (by rfl) ⟨3308201, by rfl⟩ : syracuseStep 4410935 = 6616403) B6616403
theorem B2940623 : Blo 1959435 2940623 := bstep (se 1 (by rfl) ⟨2205467, by rfl⟩ : syracuseStep 2940623 = 4410935) B4410935
theorem B1960415 : Blo 1959435 1960415 := bstep (se 1 (by rfl) ⟨1470311, by rfl⟩ : syracuseStep 1960415 = 2940623) B2940623
theorem B2940629 : Blo 1959435 2940629 := bbase (se 7 (by rfl) ⟨34460, by rfl⟩ : syracuseStep 2940629 = 68921) (by norm_num)
theorem B1960419 : Blo 1959435 1960419 := bstep (se 1 (by rfl) ⟨1470314, by rfl⟩ : syracuseStep 1960419 = 2940629) B2940629
theorem B3140221 : Blo 1959435 3140221 := bbase (se 3 (by rfl) ⟨588791, by rfl⟩ : syracuseStep 3140221 = 1177583) (by norm_num)
theorem B4186961 : Blo 1959435 4186961 := bstep (se 2 (by rfl) ⟨1570110, by rfl⟩ : syracuseStep 4186961 = 3140221) B3140221
theorem B2791307 : Blo 1959435 2791307 := bstep (se 1 (by rfl) ⟨2093480, by rfl⟩ : syracuseStep 2791307 = 4186961) B4186961
theorem B7443485 : Blo 1959435 7443485 := bstep (se 3 (by rfl) ⟨1395653, by rfl⟩ : syracuseStep 7443485 = 2791307) B2791307
theorem B4962323 : Blo 1959435 4962323 := bstep (se 1 (by rfl) ⟨3721742, by rfl⟩ : syracuseStep 4962323 = 7443485) B7443485
theorem B3308215 : Blo 1959435 3308215 := bstep (se 1 (by rfl) ⟨2481161, by rfl⟩ : syracuseStep 3308215 = 4962323) B4962323
theorem B4410953 : Blo 1959435 4410953 := bstep (se 2 (by rfl) ⟨1654107, by rfl⟩ : syracuseStep 4410953 = 3308215) B3308215
theorem B2940635 : Blo 1959435 2940635 := bstep (se 1 (by rfl) ⟨2205476, by rfl⟩ : syracuseStep 2940635 = 4410953) B4410953
theorem B1960423 : Blo 1959435 1960423 := bstep (se 1 (by rfl) ⟨1470317, by rfl⟩ : syracuseStep 1960423 = 2940635) B2940635
theorem B2205481 : Blo 1959435 2205481 := bbase (se 2 (by rfl) ⟨827055, by rfl⟩ : syracuseStep 2205481 = 1654111) (by norm_num)
theorem B2940641 : Blo 1959435 2940641 := bstep (se 2 (by rfl) ⟨1102740, by rfl⟩ : syracuseStep 2940641 = 2205481) B2205481
theorem B1960427 : Blo 1959435 1960427 := bstep (se 1 (by rfl) ⟨1470320, by rfl⟩ : syracuseStep 1960427 = 2940641) B2940641
theorem B8942309 : Blo 1959435 8942309 := bbase (se 4 (by rfl) ⟨838341, by rfl⟩ : syracuseStep 8942309 = 1676683) (by norm_num)
theorem B5961539 : Blo 1959435 5961539 := bstep (se 1 (by rfl) ⟨4471154, by rfl⟩ : syracuseStep 5961539 = 8942309) B8942309
theorem B3974359 : Blo 1959435 3974359 := bstep (se 1 (by rfl) ⟨2980769, by rfl⟩ : syracuseStep 3974359 = 5961539) B5961539
theorem B5299145 : Blo 1959435 5299145 := bstep (se 2 (by rfl) ⟨1987179, by rfl⟩ : syracuseStep 5299145 = 3974359) B3974359
theorem B3532763 : Blo 1959435 3532763 := bstep (se 1 (by rfl) ⟨2649572, by rfl⟩ : syracuseStep 3532763 = 5299145) B5299145
theorem B2355175 : Blo 1959435 2355175 := bstep (se 1 (by rfl) ⟨1766381, by rfl⟩ : syracuseStep 2355175 = 3532763) B3532763
theorem B12560933 : Blo 1959435 12560933 := bstep (se 4 (by rfl) ⟨1177587, by rfl⟩ : syracuseStep 12560933 = 2355175) B2355175
theorem B8373955 : Blo 1959435 8373955 := bstep (se 1 (by rfl) ⟨6280466, by rfl⟩ : syracuseStep 8373955 = 12560933) B12560933
theorem B11165273 : Blo 1959435 11165273 := bstep (se 2 (by rfl) ⟨4186977, by rfl⟩ : syracuseStep 11165273 = 8373955) B8373955
theorem B7443515 : Blo 1959435 7443515 := bstep (se 1 (by rfl) ⟨5582636, by rfl⟩ : syracuseStep 7443515 = 11165273) B11165273
theorem B4962343 : Blo 1959435 4962343 := bstep (se 1 (by rfl) ⟨3721757, by rfl⟩ : syracuseStep 4962343 = 7443515) B7443515
theorem B6616457 : Blo 1959435 6616457 := bstep (se 2 (by rfl) ⟨2481171, by rfl⟩ : syracuseStep 6616457 = 4962343) B4962343
theorem B4410971 : Blo 1959435 4410971 := bstep (se 1 (by rfl) ⟨3308228, by rfl⟩ : syracuseStep 4410971 = 6616457) B6616457
theorem B2940647 : Blo 1959435 2940647 := bstep (se 1 (by rfl) ⟨2205485, by rfl⟩ : syracuseStep 2940647 = 4410971) B4410971
theorem B1960431 : Blo 1959435 1960431 := bstep (se 1 (by rfl) ⟨1470323, by rfl⟩ : syracuseStep 1960431 = 2940647) B2940647
theorem B2940653 : Blo 1959435 2940653 := bbase (se 3 (by rfl) ⟨551372, by rfl⟩ : syracuseStep 2940653 = 1102745) (by norm_num)
theorem B1960435 : Blo 1959435 1960435 := bstep (se 1 (by rfl) ⟨1470326, by rfl⟩ : syracuseStep 1960435 = 2940653) B2940653
theorem B4410989 : Blo 1959435 4410989 := bbase (se 3 (by rfl) ⟨827060, by rfl⟩ : syracuseStep 4410989 = 1654121) (by norm_num)
theorem B2940659 : Blo 1959435 2940659 := bstep (se 1 (by rfl) ⟨2205494, by rfl⟩ : syracuseStep 2940659 = 4410989) B4410989
theorem B1960439 : Blo 1959435 1960439 := bstep (se 1 (by rfl) ⟨1470329, by rfl⟩ : syracuseStep 1960439 = 2940659) B2940659
theorem B3721781 : Blo 1959435 3721781 := bbase (se 5 (by rfl) ⟨174458, by rfl⟩ : syracuseStep 3721781 = 348917) (by norm_num)
theorem B2481187 : Blo 1959435 2481187 := bstep (se 1 (by rfl) ⟨1860890, by rfl⟩ : syracuseStep 2481187 = 3721781) B3721781
theorem B3308249 : Blo 1959435 3308249 := bstep (se 2 (by rfl) ⟨1240593, by rfl⟩ : syracuseStep 3308249 = 2481187) B2481187
theorem B2205499 : Blo 1959435 2205499 := bstep (se 1 (by rfl) ⟨1654124, by rfl⟩ : syracuseStep 2205499 = 3308249) B3308249
theorem B2940665 : Blo 1959435 2940665 := bstep (se 2 (by rfl) ⟨1102749, by rfl⟩ : syracuseStep 2940665 = 2205499) B2205499
theorem B1960443 : Blo 1959435 1960443 := bstep (se 1 (by rfl) ⟨1470332, by rfl⟩ : syracuseStep 1960443 = 2940665) B2940665
theorem B19098613 : Blo 1959435 19098613 := bbase (se 5 (by rfl) ⟨895247, by rfl⟩ : syracuseStep 19098613 = 1790495) (by norm_num)
theorem B25464817 : Blo 1959435 25464817 := bstep (se 2 (by rfl) ⟨9549306, by rfl⟩ : syracuseStep 25464817 = 19098613) B19098613
theorem B33953089 : Blo 1959435 33953089 := bstep (se 2 (by rfl) ⟨12732408, by rfl⟩ : syracuseStep 33953089 = 25464817) B25464817
theorem B45270785 : Blo 1959435 45270785 := bstep (se 2 (by rfl) ⟨16976544, by rfl⟩ : syracuseStep 45270785 = 33953089) B33953089
theorem B120722093 : Blo 1959435 120722093 := bstep (se 3 (by rfl) ⟨22635392, by rfl⟩ : syracuseStep 120722093 = 45270785) B45270785
theorem B80481395 : Blo 1959435 80481395 := bstep (se 1 (by rfl) ⟨60361046, by rfl⟩ : syracuseStep 80481395 = 120722093) B120722093
theorem B214617053 : Blo 1959435 214617053 := bstep (se 3 (by rfl) ⟨40240697, by rfl⟩ : syracuseStep 214617053 = 80481395) B80481395
theorem B143078035 : Blo 1959435 143078035 := bstep (se 1 (by rfl) ⟨107308526, by rfl⟩ : syracuseStep 143078035 = 214617053) B214617053
theorem B190770713 : Blo 1959435 190770713 := bstep (se 2 (by rfl) ⟨71539017, by rfl⟩ : syracuseStep 190770713 = 143078035) B143078035
theorem B127180475 : Blo 1959435 127180475 := bstep (se 1 (by rfl) ⟨95385356, by rfl⟩ : syracuseStep 127180475 = 190770713) B190770713
theorem B84786983 : Blo 1959435 84786983 := bstep (se 1 (by rfl) ⟨63590237, by rfl⟩ : syracuseStep 84786983 = 127180475) B127180475
theorem B56524655 : Blo 1959435 56524655 := bstep (se 1 (by rfl) ⟨42393491, by rfl⟩ : syracuseStep 56524655 = 84786983) B84786983
theorem B37683103 : Blo 1959435 37683103 := bstep (se 1 (by rfl) ⟨28262327, by rfl⟩ : syracuseStep 37683103 = 56524655) B56524655
theorem B50244137 : Blo 1959435 50244137 := bstep (se 2 (by rfl) ⟨18841551, by rfl⟩ : syracuseStep 50244137 = 37683103) B37683103
theorem B33496091 : Blo 1959435 33496091 := bstep (se 1 (by rfl) ⟨25122068, by rfl⟩ : syracuseStep 33496091 = 50244137) B50244137
theorem B22330727 : Blo 1959435 22330727 := bstep (se 1 (by rfl) ⟨16748045, by rfl⟩ : syracuseStep 22330727 = 33496091) B33496091
theorem B14887151 : Blo 1959435 14887151 := bstep (se 1 (by rfl) ⟨11165363, by rfl⟩ : syracuseStep 14887151 = 22330727) B22330727
theorem B9924767 : Blo 1959435 9924767 := bstep (se 1 (by rfl) ⟨7443575, by rfl⟩ : syracuseStep 9924767 = 14887151) B14887151
theorem B6616511 : Blo 1959435 6616511 := bstep (se 1 (by rfl) ⟨4962383, by rfl⟩ : syracuseStep 6616511 = 9924767) B9924767
theorem B4411007 : Blo 1959435 4411007 := bstep (se 1 (by rfl) ⟨3308255, by rfl⟩ : syracuseStep 4411007 = 6616511) B6616511
theorem B2940671 : Blo 1959435 2940671 := bstep (se 1 (by rfl) ⟨2205503, by rfl⟩ : syracuseStep 2940671 = 4411007) B4411007
theorem B1960447 : Blo 1959435 1960447 := bstep (se 1 (by rfl) ⟨1470335, by rfl⟩ : syracuseStep 1960447 = 2940671) B2940671
theorem B2940677 : Blo 1959435 2940677 := bbase (se 4 (by rfl) ⟨275688, by rfl⟩ : syracuseStep 2940677 = 551377) (by norm_num)
theorem B1960451 : Blo 1959435 1960451 := bstep (se 1 (by rfl) ⟨1470338, by rfl⟩ : syracuseStep 1960451 = 2940677) B2940677
theorem B3308269 : Blo 1959435 3308269 := bbase (se 3 (by rfl) ⟨620300, by rfl⟩ : syracuseStep 3308269 = 1240601) (by norm_num)
theorem B4411025 : Blo 1959435 4411025 := bstep (se 2 (by rfl) ⟨1654134, by rfl⟩ : syracuseStep 4411025 = 3308269) B3308269
theorem B2940683 : Blo 1959435 2940683 := bstep (se 1 (by rfl) ⟨2205512, by rfl⟩ : syracuseStep 2940683 = 4411025) B4411025
theorem B1960455 : Blo 1959435 1960455 := bstep (se 1 (by rfl) ⟨1470341, by rfl⟩ : syracuseStep 1960455 = 2940683) B2940683
theorem B2205517 : Blo 1959435 2205517 := bbase (se 3 (by rfl) ⟨413534, by rfl⟩ : syracuseStep 2205517 = 827069) (by norm_num)
theorem B2940689 : Blo 1959435 2940689 := bstep (se 2 (by rfl) ⟨1102758, by rfl⟩ : syracuseStep 2940689 = 2205517) B2205517
theorem B1960459 : Blo 1959435 1960459 := bstep (se 1 (by rfl) ⟨1470344, by rfl⟩ : syracuseStep 1960459 = 2940689) B2940689
theorem B6616565 : Blo 1959435 6616565 := bbase (se 5 (by rfl) ⟨310151, by rfl⟩ : syracuseStep 6616565 = 620303) (by norm_num)
theorem B4411043 : Blo 1959435 4411043 := bstep (se 1 (by rfl) ⟨3308282, by rfl⟩ : syracuseStep 4411043 = 6616565) B6616565
theorem B2940695 : Blo 1959435 2940695 := bstep (se 1 (by rfl) ⟨2205521, by rfl⟩ : syracuseStep 2940695 = 4411043) B4411043
theorem B1960463 : Blo 1959435 1960463 := bstep (se 1 (by rfl) ⟨1470347, by rfl⟩ : syracuseStep 1960463 = 2940695) B2940695
theorem B2940701 : Blo 1959435 2940701 := bbase (se 3 (by rfl) ⟨551381, by rfl⟩ : syracuseStep 2940701 = 1102763) (by norm_num)
theorem B1960467 : Blo 1959435 1960467 := bstep (se 1 (by rfl) ⟨1470350, by rfl⟩ : syracuseStep 1960467 = 2940701) B2940701
theorem B4411061 : Blo 1959435 4411061 := bbase (se 5 (by rfl) ⟨206768, by rfl⟩ : syracuseStep 4411061 = 413537) (by norm_num)
theorem B2940707 : Blo 1959435 2940707 := bstep (se 1 (by rfl) ⟨2205530, by rfl⟩ : syracuseStep 2940707 = 4411061) B4411061
theorem B1960471 : Blo 1959435 1960471 := bstep (se 1 (by rfl) ⟨1470353, by rfl⟩ : syracuseStep 1960471 = 2940707) B2940707
theorem B11165525 : Blo 1959435 11165525 := bbase (se 9 (by rfl) ⟨32711, by rfl⟩ : syracuseStep 11165525 = 65423) (by norm_num)
theorem B7443683 : Blo 1959435 7443683 := bstep (se 1 (by rfl) ⟨5582762, by rfl⟩ : syracuseStep 7443683 = 11165525) B11165525
theorem B4962455 : Blo 1959435 4962455 := bstep (se 1 (by rfl) ⟨3721841, by rfl⟩ : syracuseStep 4962455 = 7443683) B7443683
theorem B3308303 : Blo 1959435 3308303 := bstep (se 1 (by rfl) ⟨2481227, by rfl⟩ : syracuseStep 3308303 = 4962455) B4962455
theorem B2205535 : Blo 1959435 2205535 := bstep (se 1 (by rfl) ⟨1654151, by rfl⟩ : syracuseStep 2205535 = 3308303) B3308303
theorem B2940713 : Blo 1959435 2940713 := bstep (se 2 (by rfl) ⟨1102767, by rfl⟩ : syracuseStep 2940713 = 2205535) B2205535
theorem B1960475 : Blo 1959435 1960475 := bstep (se 1 (by rfl) ⟨1470356, by rfl⟩ : syracuseStep 1960475 = 2940713) B2940713
theorem B5582773 : Blo 1959435 5582773 := bbase (se 5 (by rfl) ⟨261692, by rfl⟩ : syracuseStep 5582773 = 523385) (by norm_num)
theorem B7443697 : Blo 1959435 7443697 := bstep (se 2 (by rfl) ⟨2791386, by rfl⟩ : syracuseStep 7443697 = 5582773) B5582773
theorem B9924929 : Blo 1959435 9924929 := bstep (se 2 (by rfl) ⟨3721848, by rfl⟩ : syracuseStep 9924929 = 7443697) B7443697
theorem B6616619 : Blo 1959435 6616619 := bstep (se 1 (by rfl) ⟨4962464, by rfl⟩ : syracuseStep 6616619 = 9924929) B9924929
theorem B4411079 : Blo 1959435 4411079 := bstep (se 1 (by rfl) ⟨3308309, by rfl⟩ : syracuseStep 4411079 = 6616619) B6616619
theorem B2940719 : Blo 1959435 2940719 := bstep (se 1 (by rfl) ⟨2205539, by rfl⟩ : syracuseStep 2940719 = 4411079) B4411079
theorem B1960479 : Blo 1959435 1960479 := bstep (se 1 (by rfl) ⟨1470359, by rfl⟩ : syracuseStep 1960479 = 2940719) B2940719
theorem B2940725 : Blo 1959435 2940725 := bbase (se 5 (by rfl) ⟨137846, by rfl⟩ : syracuseStep 2940725 = 275693) (by norm_num)
theorem B1960483 : Blo 1959435 1960483 := bstep (se 1 (by rfl) ⟨1470362, by rfl⟩ : syracuseStep 1960483 = 2940725) B2940725
theorem B4962485 : Blo 1959435 4962485 := bbase (se 5 (by rfl) ⟨232616, by rfl⟩ : syracuseStep 4962485 = 465233) (by norm_num)
theorem B3308323 : Blo 1959435 3308323 := bstep (se 1 (by rfl) ⟨2481242, by rfl⟩ : syracuseStep 3308323 = 4962485) B4962485
theorem B4411097 : Blo 1959435 4411097 := bstep (se 2 (by rfl) ⟨1654161, by rfl⟩ : syracuseStep 4411097 = 3308323) B3308323
theorem B2940731 : Blo 1959435 2940731 := bstep (se 1 (by rfl) ⟨2205548, by rfl⟩ : syracuseStep 2940731 = 4411097) B4411097
theorem B1960487 : Blo 1959435 1960487 := bstep (se 1 (by rfl) ⟨1470365, by rfl⟩ : syracuseStep 1960487 = 2940731) B2940731
theorem B2205553 : Blo 1959435 2205553 := bbase (se 2 (by rfl) ⟨827082, by rfl⟩ : syracuseStep 2205553 = 1654165) (by norm_num)
theorem B2940737 : Blo 1959435 2940737 := bstep (se 2 (by rfl) ⟨1102776, by rfl⟩ : syracuseStep 2940737 = 2205553) B2205553
theorem B1960491 : Blo 1959435 1960491 := bstep (se 1 (by rfl) ⟨1470368, by rfl⟩ : syracuseStep 1960491 = 2940737) B2940737
theorem B8374229 : Blo 1959435 8374229 := bbase (se 7 (by rfl) ⟨98135, by rfl⟩ : syracuseStep 8374229 = 196271) (by norm_num)
theorem B5582819 : Blo 1959435 5582819 := bstep (se 1 (by rfl) ⟨4187114, by rfl⟩ : syracuseStep 5582819 = 8374229) B8374229
theorem B3721879 : Blo 1959435 3721879 := bstep (se 1 (by rfl) ⟨2791409, by rfl⟩ : syracuseStep 3721879 = 5582819) B5582819
theorem B4962505 : Blo 1959435 4962505 := bstep (se 2 (by rfl) ⟨1860939, by rfl⟩ : syracuseStep 4962505 = 3721879) B3721879
theorem B6616673 : Blo 1959435 6616673 := bstep (se 2 (by rfl) ⟨2481252, by rfl⟩ : syracuseStep 6616673 = 4962505) B4962505
theorem B4411115 : Blo 1959435 4411115 := bstep (se 1 (by rfl) ⟨3308336, by rfl⟩ : syracuseStep 4411115 = 6616673) B6616673
theorem B2940743 : Blo 1959435 2940743 := bstep (se 1 (by rfl) ⟨2205557, by rfl⟩ : syracuseStep 2940743 = 4411115) B4411115
theorem B1960495 : Blo 1959435 1960495 := bstep (se 1 (by rfl) ⟨1470371, by rfl⟩ : syracuseStep 1960495 = 2940743) B2940743
theorem B2940749 : Blo 1959435 2940749 := bbase (se 3 (by rfl) ⟨551390, by rfl⟩ : syracuseStep 2940749 = 1102781) (by norm_num)
theorem B1960499 : Blo 1959435 1960499 := bstep (se 1 (by rfl) ⟨1470374, by rfl⟩ : syracuseStep 1960499 = 2940749) B2940749
theorem B4411133 : Blo 1959435 4411133 := bbase (se 3 (by rfl) ⟨827087, by rfl⟩ : syracuseStep 4411133 = 1654175) (by norm_num)
theorem B2940755 : Blo 1959435 2940755 := bstep (se 1 (by rfl) ⟨2205566, by rfl⟩ : syracuseStep 2940755 = 4411133) B4411133
theorem B1960503 : Blo 1959435 1960503 := bstep (se 1 (by rfl) ⟨1470377, by rfl⟩ : syracuseStep 1960503 = 2940755) B2940755
theorem B3308357 : Blo 1959435 3308357 := bbase (se 4 (by rfl) ⟨310158, by rfl⟩ : syracuseStep 3308357 = 620317) (by norm_num)
theorem B2205571 : Blo 1959435 2205571 := bstep (se 1 (by rfl) ⟨1654178, by rfl⟩ : syracuseStep 2205571 = 3308357) B3308357
theorem B2940761 : Blo 1959435 2940761 := bstep (se 2 (by rfl) ⟨1102785, by rfl⟩ : syracuseStep 2940761 = 2205571) B2205571
theorem B1960507 : Blo 1959435 1960507 := bstep (se 1 (by rfl) ⟨1470380, by rfl⟩ : syracuseStep 1960507 = 2940761) B2940761
theorem B14887637 : Blo 1959435 14887637 := bbase (se 7 (by rfl) ⟨174464, by rfl⟩ : syracuseStep 14887637 = 348929) (by norm_num)
theorem B9925091 : Blo 1959435 9925091 := bstep (se 1 (by rfl) ⟨7443818, by rfl⟩ : syracuseStep 9925091 = 14887637) B14887637
theorem B6616727 : Blo 1959435 6616727 := bstep (se 1 (by rfl) ⟨4962545, by rfl⟩ : syracuseStep 6616727 = 9925091) B9925091
theorem B4411151 : Blo 1959435 4411151 := bstep (se 1 (by rfl) ⟨3308363, by rfl⟩ : syracuseStep 4411151 = 6616727) B6616727
theorem B2940767 : Blo 1959435 2940767 := bstep (se 1 (by rfl) ⟨2205575, by rfl⟩ : syracuseStep 2940767 = 4411151) B4411151
theorem B1960511 : Blo 1959435 1960511 := bstep (se 1 (by rfl) ⟨1470383, by rfl⟩ : syracuseStep 1960511 = 2940767) B2940767
theorem B2940773 : Blo 1959435 2940773 := bbase (se 4 (by rfl) ⟨275697, by rfl⟩ : syracuseStep 2940773 = 551395) (by norm_num)
theorem B1960515 : Blo 1959435 1960515 := bstep (se 1 (by rfl) ⟨1470386, by rfl⟩ : syracuseStep 1960515 = 2940773) B2940773
theorem B3721925 : Blo 1959435 3721925 := bbase (se 4 (by rfl) ⟨348930, by rfl⟩ : syracuseStep 3721925 = 697861) (by norm_num)
theorem B2481283 : Blo 1959435 2481283 := bstep (se 1 (by rfl) ⟨1860962, by rfl⟩ : syracuseStep 2481283 = 3721925) B3721925
theorem B3308377 : Blo 1959435 3308377 := bstep (se 2 (by rfl) ⟨1240641, by rfl⟩ : syracuseStep 3308377 = 2481283) B2481283
theorem B4411169 : Blo 1959435 4411169 := bstep (se 2 (by rfl) ⟨1654188, by rfl⟩ : syracuseStep 4411169 = 3308377) B3308377
theorem B2940779 : Blo 1959435 2940779 := bstep (se 1 (by rfl) ⟨2205584, by rfl⟩ : syracuseStep 2940779 = 4411169) B4411169
theorem B1960519 : Blo 1959435 1960519 := bstep (se 1 (by rfl) ⟨1470389, by rfl⟩ : syracuseStep 1960519 = 2940779) B2940779
theorem B2205589 : Blo 1959435 2205589 := bbase (se 6 (by rfl) ⟨51693, by rfl⟩ : syracuseStep 2205589 = 103387) (by norm_num)
theorem B2940785 : Blo 1959435 2940785 := bstep (se 2 (by rfl) ⟨1102794, by rfl⟩ : syracuseStep 2940785 = 2205589) B2205589
theorem B1960523 : Blo 1959435 1960523 := bstep (se 1 (by rfl) ⟨1470392, by rfl⟩ : syracuseStep 1960523 = 2940785) B2940785
theorem B2481293 : Blo 1959435 2481293 := bbase (se 3 (by rfl) ⟨465242, by rfl⟩ : syracuseStep 2481293 = 930485) (by norm_num)
theorem B6616781 : Blo 1959435 6616781 := bstep (se 3 (by rfl) ⟨1240646, by rfl⟩ : syracuseStep 6616781 = 2481293) B2481293
theorem B4411187 : Blo 1959435 4411187 := bstep (se 1 (by rfl) ⟨3308390, by rfl⟩ : syracuseStep 4411187 = 6616781) B6616781
theorem B2940791 : Blo 1959435 2940791 := bstep (se 1 (by rfl) ⟨2205593, by rfl⟩ : syracuseStep 2940791 = 4411187) B4411187
theorem B1960527 : Blo 1959435 1960527 := bstep (se 1 (by rfl) ⟨1470395, by rfl⟩ : syracuseStep 1960527 = 2940791) B2940791
theorem B2940797 : Blo 1959435 2940797 := bbase (se 3 (by rfl) ⟨551399, by rfl⟩ : syracuseStep 2940797 = 1102799) (by norm_num)
theorem B1960531 : Blo 1959435 1960531 := bstep (se 1 (by rfl) ⟨1470398, by rfl⟩ : syracuseStep 1960531 = 2940797) B2940797
theorem B4411205 : Blo 1959435 4411205 := bbase (se 4 (by rfl) ⟨413550, by rfl⟩ : syracuseStep 4411205 = 827101) (by norm_num)
theorem B2940803 : Blo 1959435 2940803 := bstep (se 1 (by rfl) ⟨2205602, by rfl⟩ : syracuseStep 2940803 = 4411205) B4411205
theorem B1960535 : Blo 1959435 1960535 := bstep (se 1 (by rfl) ⟨1470401, by rfl⟩ : syracuseStep 1960535 = 2940803) B2940803
theorem B2235701 : Blo 1959435 2235701 := bbase (se 5 (by rfl) ⟨104798, by rfl⟩ : syracuseStep 2235701 = 209597) (by norm_num)
theorem B5961869 : Blo 1959435 5961869 := bstep (se 3 (by rfl) ⟨1117850, by rfl⟩ : syracuseStep 5961869 = 2235701) B2235701
theorem B3974579 : Blo 1959435 3974579 := bstep (se 1 (by rfl) ⟨2980934, by rfl⟩ : syracuseStep 3974579 = 5961869) B5961869
theorem B2649719 : Blo 1959435 2649719 := bstep (se 1 (by rfl) ⟨1987289, by rfl⟩ : syracuseStep 2649719 = 3974579) B3974579
theorem B7065917 : Blo 1959435 7065917 := bstep (se 3 (by rfl) ⟨1324859, by rfl⟩ : syracuseStep 7065917 = 2649719) B2649719
theorem B4710611 : Blo 1959435 4710611 := bstep (se 1 (by rfl) ⟨3532958, by rfl⟩ : syracuseStep 4710611 = 7065917) B7065917
theorem B3140407 : Blo 1959435 3140407 := bstep (se 1 (by rfl) ⟨2355305, by rfl⟩ : syracuseStep 3140407 = 4710611) B4710611
theorem B4187209 : Blo 1959435 4187209 := bstep (se 2 (by rfl) ⟨1570203, by rfl⟩ : syracuseStep 4187209 = 3140407) B3140407
theorem B5582945 : Blo 1959435 5582945 := bstep (se 2 (by rfl) ⟨2093604, by rfl⟩ : syracuseStep 5582945 = 4187209) B4187209
theorem B3721963 : Blo 1959435 3721963 := bstep (se 1 (by rfl) ⟨2791472, by rfl⟩ : syracuseStep 3721963 = 5582945) B5582945
theorem B4962617 : Blo 1959435 4962617 := bstep (se 2 (by rfl) ⟨1860981, by rfl⟩ : syracuseStep 4962617 = 3721963) B3721963
theorem B3308411 : Blo 1959435 3308411 := bstep (se 1 (by rfl) ⟨2481308, by rfl⟩ : syracuseStep 3308411 = 4962617) B4962617
theorem B2205607 : Blo 1959435 2205607 := bstep (se 1 (by rfl) ⟨1654205, by rfl⟩ : syracuseStep 2205607 = 3308411) B3308411
theorem B2940809 : Blo 1959435 2940809 := bstep (se 2 (by rfl) ⟨1102803, by rfl⟩ : syracuseStep 2940809 = 2205607) B2205607
theorem B1960539 : Blo 1959435 1960539 := bstep (se 1 (by rfl) ⟨1470404, by rfl⟩ : syracuseStep 1960539 = 2940809) B2940809
theorem B9925253 : Blo 1959435 9925253 := bbase (se 4 (by rfl) ⟨930492, by rfl⟩ : syracuseStep 9925253 = 1860985) (by norm_num)
theorem B6616835 : Blo 1959435 6616835 := bstep (se 1 (by rfl) ⟨4962626, by rfl⟩ : syracuseStep 6616835 = 9925253) B9925253
theorem B4411223 : Blo 1959435 4411223 := bstep (se 1 (by rfl) ⟨3308417, by rfl⟩ : syracuseStep 4411223 = 6616835) B6616835
theorem B2940815 : Blo 1959435 2940815 := bstep (se 1 (by rfl) ⟨2205611, by rfl⟩ : syracuseStep 2940815 = 4411223) B4411223
theorem B1960543 : Blo 1959435 1960543 := bstep (se 1 (by rfl) ⟨1470407, by rfl⟩ : syracuseStep 1960543 = 2940815) B2940815
theorem B2940821 : Blo 1959435 2940821 := bbase (se 6 (by rfl) ⟨68925, by rfl⟩ : syracuseStep 2940821 = 137851) (by norm_num)
theorem B1960547 : Blo 1959435 1960547 := bstep (se 1 (by rfl) ⟨1470410, by rfl⟩ : syracuseStep 1960547 = 2940821) B2940821
theorem B2093617 : Blo 1959435 2093617 := bbase (se 2 (by rfl) ⟨785106, by rfl⟩ : syracuseStep 2093617 = 1570213) (by norm_num)
theorem B11165957 : Blo 1959435 11165957 := bstep (se 4 (by rfl) ⟨1046808, by rfl⟩ : syracuseStep 11165957 = 2093617) B2093617
theorem B7443971 : Blo 1959435 7443971 := bstep (se 1 (by rfl) ⟨5582978, by rfl⟩ : syracuseStep 7443971 = 11165957) B11165957
theorem B4962647 : Blo 1959435 4962647 := bstep (se 1 (by rfl) ⟨3721985, by rfl⟩ : syracuseStep 4962647 = 7443971) B7443971
theorem B3308431 : Blo 1959435 3308431 := bstep (se 1 (by rfl) ⟨2481323, by rfl⟩ : syracuseStep 3308431 = 4962647) B4962647
theorem B4411241 : Blo 1959435 4411241 := bstep (se 2 (by rfl) ⟨1654215, by rfl⟩ : syracuseStep 4411241 = 3308431) B3308431
theorem B2940827 : Blo 1959435 2940827 := bstep (se 1 (by rfl) ⟨2205620, by rfl⟩ : syracuseStep 2940827 = 4411241) B4411241
theorem B1960551 : Blo 1959435 1960551 := bstep (se 1 (by rfl) ⟨1470413, by rfl⟩ : syracuseStep 1960551 = 2940827) B2940827
theorem B2205625 : Blo 1959435 2205625 := bbase (se 2 (by rfl) ⟨827109, by rfl⟩ : syracuseStep 2205625 = 1654219) (by norm_num)
theorem B2940833 : Blo 1959435 2940833 := bstep (se 2 (by rfl) ⟨1102812, by rfl⟩ : syracuseStep 2940833 = 2205625) B2205625
theorem B1960555 : Blo 1959435 1960555 := bstep (se 1 (by rfl) ⟨1470416, by rfl⟩ : syracuseStep 1960555 = 2940833) B2940833
theorem B2355329 : Blo 1959435 2355329 := bbase (se 2 (by rfl) ⟨883248, by rfl⟩ : syracuseStep 2355329 = 1766497) (by norm_num)
theorem B6280877 : Blo 1959435 6280877 := bstep (se 3 (by rfl) ⟨1177664, by rfl⟩ : syracuseStep 6280877 = 2355329) B2355329
theorem B4187251 : Blo 1959435 4187251 := bstep (se 1 (by rfl) ⟨3140438, by rfl⟩ : syracuseStep 4187251 = 6280877) B6280877
theorem B5583001 : Blo 1959435 5583001 := bstep (se 2 (by rfl) ⟨2093625, by rfl⟩ : syracuseStep 5583001 = 4187251) B4187251
theorem B7444001 : Blo 1959435 7444001 := bstep (se 2 (by rfl) ⟨2791500, by rfl⟩ : syracuseStep 7444001 = 5583001) B5583001
theorem B4962667 : Blo 1959435 4962667 := bstep (se 1 (by rfl) ⟨3722000, by rfl⟩ : syracuseStep 4962667 = 7444001) B7444001
theorem B6616889 : Blo 1959435 6616889 := bstep (se 2 (by rfl) ⟨2481333, by rfl⟩ : syracuseStep 6616889 = 4962667) B4962667
theorem B4411259 : Blo 1959435 4411259 := bstep (se 1 (by rfl) ⟨3308444, by rfl⟩ : syracuseStep 4411259 = 6616889) B6616889
theorem B2940839 : Blo 1959435 2940839 := bstep (se 1 (by rfl) ⟨2205629, by rfl⟩ : syracuseStep 2940839 = 4411259) B4411259
theorem B1960559 : Blo 1959435 1960559 := bstep (se 1 (by rfl) ⟨1470419, by rfl⟩ : syracuseStep 1960559 = 2940839) B2940839
theorem B2940845 : Blo 1959435 2940845 := bbase (se 3 (by rfl) ⟨551408, by rfl⟩ : syracuseStep 2940845 = 1102817) (by norm_num)
theorem B1960563 : Blo 1959435 1960563 := bstep (se 1 (by rfl) ⟨1470422, by rfl⟩ : syracuseStep 1960563 = 2940845) B2940845
theorem B4411277 : Blo 1959435 4411277 := bbase (se 3 (by rfl) ⟨827114, by rfl⟩ : syracuseStep 4411277 = 1654229) (by norm_num)
theorem B2940851 : Blo 1959435 2940851 := bstep (se 1 (by rfl) ⟨2205638, by rfl⟩ : syracuseStep 2940851 = 4411277) B4411277
theorem B1960567 : Blo 1959435 1960567 := bstep (se 1 (by rfl) ⟨1470425, by rfl⟩ : syracuseStep 1960567 = 2940851) B2940851
theorem B2481349 : Blo 1959435 2481349 := bbase (se 4 (by rfl) ⟨232626, by rfl⟩ : syracuseStep 2481349 = 465253) (by norm_num)
theorem B3308465 : Blo 1959435 3308465 := bstep (se 2 (by rfl) ⟨1240674, by rfl⟩ : syracuseStep 3308465 = 2481349) B2481349
theorem B2205643 : Blo 1959435 2205643 := bstep (se 1 (by rfl) ⟨1654232, by rfl⟩ : syracuseStep 2205643 = 3308465) B3308465
theorem B2940857 : Blo 1959435 2940857 := bstep (se 2 (by rfl) ⟨1102821, by rfl⟩ : syracuseStep 2940857 = 2205643) B2205643
theorem B1960571 : Blo 1959435 1960571 := bstep (se 1 (by rfl) ⟨1470428, by rfl⟩ : syracuseStep 1960571 = 2940857) B2940857
theorem B3772813 : Blo 1959435 3772813 := bbase (se 3 (by rfl) ⟨707402, by rfl⟩ : syracuseStep 3772813 = 1414805) (by norm_num)
theorem B5030417 : Blo 1959435 5030417 := bstep (se 2 (by rfl) ⟨1886406, by rfl⟩ : syracuseStep 5030417 = 3772813) B3772813
theorem B3353611 : Blo 1959435 3353611 := bstep (se 1 (by rfl) ⟨2515208, by rfl⟩ : syracuseStep 3353611 = 5030417) B5030417
theorem B4471481 : Blo 1959435 4471481 := bstep (se 2 (by rfl) ⟨1676805, by rfl⟩ : syracuseStep 4471481 = 3353611) B3353611
theorem B11923949 : Blo 1959435 11923949 := bstep (se 3 (by rfl) ⟨2235740, by rfl⟩ : syracuseStep 11923949 = 4471481) B4471481
theorem B31797197 : Blo 1959435 31797197 := bstep (se 3 (by rfl) ⟨5961974, by rfl⟩ : syracuseStep 31797197 = 11923949) B11923949
theorem B21198131 : Blo 1959435 21198131 := bstep (se 1 (by rfl) ⟨15898598, by rfl⟩ : syracuseStep 21198131 = 31797197) B31797197
theorem B14132087 : Blo 1959435 14132087 := bstep (se 1 (by rfl) ⟨10599065, by rfl⟩ : syracuseStep 14132087 = 21198131) B21198131
theorem B9421391 : Blo 1959435 9421391 := bstep (se 1 (by rfl) ⟨7066043, by rfl⟩ : syracuseStep 9421391 = 14132087) B14132087
theorem B25123709 : Blo 1959435 25123709 := bstep (se 3 (by rfl) ⟨4710695, by rfl⟩ : syracuseStep 25123709 = 9421391) B9421391
theorem B16749139 : Blo 1959435 16749139 := bstep (se 1 (by rfl) ⟨12561854, by rfl⟩ : syracuseStep 16749139 = 25123709) B25123709
theorem B22332185 : Blo 1959435 22332185 := bstep (se 2 (by rfl) ⟨8374569, by rfl⟩ : syracuseStep 22332185 = 16749139) B16749139
theorem B14888123 : Blo 1959435 14888123 := bstep (se 1 (by rfl) ⟨11166092, by rfl⟩ : syracuseStep 14888123 = 22332185) B22332185
theorem B9925415 : Blo 1959435 9925415 := bstep (se 1 (by rfl) ⟨7444061, by rfl⟩ : syracuseStep 9925415 = 14888123) B14888123
theorem B6616943 : Blo 1959435 6616943 := bstep (se 1 (by rfl) ⟨4962707, by rfl⟩ : syracuseStep 6616943 = 9925415) B9925415
theorem B4411295 : Blo 1959435 4411295 := bstep (se 1 (by rfl) ⟨3308471, by rfl⟩ : syracuseStep 4411295 = 6616943) B6616943
theorem B2940863 : Blo 1959435 2940863 := bstep (se 1 (by rfl) ⟨2205647, by rfl⟩ : syracuseStep 2940863 = 4411295) B4411295
theorem B1960575 : Blo 1959435 1960575 := bstep (se 1 (by rfl) ⟨1470431, by rfl⟩ : syracuseStep 1960575 = 2940863) B2940863
theorem B2940869 : Blo 1959435 2940869 := bbase (se 4 (by rfl) ⟨275706, by rfl⟩ : syracuseStep 2940869 = 551413) (by norm_num)
theorem B1960579 : Blo 1959435 1960579 := bstep (se 1 (by rfl) ⟨1470434, by rfl⟩ : syracuseStep 1960579 = 2940869) B2940869
theorem B3308485 : Blo 1959435 3308485 := bbase (se 4 (by rfl) ⟨310170, by rfl⟩ : syracuseStep 3308485 = 620341) (by norm_num)
theorem B4411313 : Blo 1959435 4411313 := bstep (se 2 (by rfl) ⟨1654242, by rfl⟩ : syracuseStep 4411313 = 3308485) B3308485
theorem B2940875 : Blo 1959435 2940875 := bstep (se 1 (by rfl) ⟨2205656, by rfl⟩ : syracuseStep 2940875 = 4411313) B4411313
theorem B1960583 : Blo 1959435 1960583 := bstep (se 1 (by rfl) ⟨1470437, by rfl⟩ : syracuseStep 1960583 = 2940875) B2940875
theorem B2205661 : Blo 1959435 2205661 := bbase (se 3 (by rfl) ⟨413561, by rfl⟩ : syracuseStep 2205661 = 827123) (by norm_num)
theorem B2940881 : Blo 1959435 2940881 := bstep (se 2 (by rfl) ⟨1102830, by rfl⟩ : syracuseStep 2940881 = 2205661) B2205661
theorem B1960587 : Blo 1959435 1960587 := bstep (se 1 (by rfl) ⟨1470440, by rfl⟩ : syracuseStep 1960587 = 2940881) B2940881
theorem B6616997 : Blo 1959435 6616997 := bbase (se 4 (by rfl) ⟨620343, by rfl⟩ : syracuseStep 6616997 = 1240687) (by norm_num)
theorem B4411331 : Blo 1959435 4411331 := bstep (se 1 (by rfl) ⟨3308498, by rfl⟩ : syracuseStep 4411331 = 6616997) B6616997
theorem B2940887 : Blo 1959435 2940887 := bstep (se 1 (by rfl) ⟨2205665, by rfl⟩ : syracuseStep 2940887 = 4411331) B4411331
theorem B1960591 : Blo 1959435 1960591 := bstep (se 1 (by rfl) ⟨1470443, by rfl⟩ : syracuseStep 1960591 = 2940887) B2940887
theorem B2940893 : Blo 1959435 2940893 := bbase (se 3 (by rfl) ⟨551417, by rfl⟩ : syracuseStep 2940893 = 1102835) (by norm_num)
theorem B1960595 : Blo 1959435 1960595 := bstep (se 1 (by rfl) ⟨1470446, by rfl⟩ : syracuseStep 1960595 = 2940893) B2940893
theorem B4411349 : Blo 1959435 4411349 := bbase (se 7 (by rfl) ⟨51695, by rfl⟩ : syracuseStep 4411349 = 103391) (by norm_num)
theorem B2940899 : Blo 1959435 2940899 := bstep (se 1 (by rfl) ⟨2205674, by rfl⟩ : syracuseStep 2940899 = 4411349) B4411349
theorem B1960599 : Blo 1959435 1960599 := bstep (se 1 (by rfl) ⟨1470449, by rfl⟩ : syracuseStep 1960599 = 2940899) B2940899
theorem B12562037 : Blo 1959435 12562037 := bbase (se 5 (by rfl) ⟨588845, by rfl⟩ : syracuseStep 12562037 = 1177691) (by norm_num)
theorem B8374691 : Blo 1959435 8374691 := bstep (se 1 (by rfl) ⟨6281018, by rfl⟩ : syracuseStep 8374691 = 12562037) B12562037
theorem B5583127 : Blo 1959435 5583127 := bstep (se 1 (by rfl) ⟨4187345, by rfl⟩ : syracuseStep 5583127 = 8374691) B8374691
theorem B7444169 : Blo 1959435 7444169 := bstep (se 2 (by rfl) ⟨2791563, by rfl⟩ : syracuseStep 7444169 = 5583127) B5583127
theorem B4962779 : Blo 1959435 4962779 := bstep (se 1 (by rfl) ⟨3722084, by rfl⟩ : syracuseStep 4962779 = 7444169) B7444169
theorem B3308519 : Blo 1959435 3308519 := bstep (se 1 (by rfl) ⟨2481389, by rfl⟩ : syracuseStep 3308519 = 4962779) B4962779
theorem B2205679 : Blo 1959435 2205679 := bstep (se 1 (by rfl) ⟨1654259, by rfl⟩ : syracuseStep 2205679 = 3308519) B3308519
theorem B2940905 : Blo 1959435 2940905 := bstep (se 2 (by rfl) ⟨1102839, by rfl⟩ : syracuseStep 2940905 = 2205679) B2205679
theorem B1960603 : Blo 1959435 1960603 := bstep (se 1 (by rfl) ⟨1470452, by rfl⟩ : syracuseStep 1960603 = 2940905) B2940905
theorem B4710773 : Blo 1959435 4710773 := bbase (se 5 (by rfl) ⟨220817, by rfl⟩ : syracuseStep 4710773 = 441635) (by norm_num)
theorem B3140515 : Blo 1959435 3140515 := bstep (se 1 (by rfl) ⟨2355386, by rfl⟩ : syracuseStep 3140515 = 4710773) B4710773
theorem B16749413 : Blo 1959435 16749413 := bstep (se 4 (by rfl) ⟨1570257, by rfl⟩ : syracuseStep 16749413 = 3140515) B3140515
theorem B11166275 : Blo 1959435 11166275 := bstep (se 1 (by rfl) ⟨8374706, by rfl⟩ : syracuseStep 11166275 = 16749413) B16749413
theorem B7444183 : Blo 1959435 7444183 := bstep (se 1 (by rfl) ⟨5583137, by rfl⟩ : syracuseStep 7444183 = 11166275) B11166275
theorem B9925577 : Blo 1959435 9925577 := bstep (se 2 (by rfl) ⟨3722091, by rfl⟩ : syracuseStep 9925577 = 7444183) B7444183
theorem B6617051 : Blo 1959435 6617051 := bstep (se 1 (by rfl) ⟨4962788, by rfl⟩ : syracuseStep 6617051 = 9925577) B9925577
theorem B4411367 : Blo 1959435 4411367 := bstep (se 1 (by rfl) ⟨3308525, by rfl⟩ : syracuseStep 4411367 = 6617051) B6617051
theorem B2940911 : Blo 1959435 2940911 := bstep (se 1 (by rfl) ⟨2205683, by rfl⟩ : syracuseStep 2940911 = 4411367) B4411367
theorem B1960607 : Blo 1959435 1960607 := bstep (se 1 (by rfl) ⟨1470455, by rfl⟩ : syracuseStep 1960607 = 2940911) B2940911
theorem B2940917 : Blo 1959435 2940917 := bbase (se 5 (by rfl) ⟨137855, by rfl⟩ : syracuseStep 2940917 = 275711) (by norm_num)
theorem B1960611 : Blo 1959435 1960611 := bstep (se 1 (by rfl) ⟨1470458, by rfl⟩ : syracuseStep 1960611 = 2940917) B2940917
theorem B2515261 : Blo 1959435 2515261 := bbase (se 3 (by rfl) ⟨471611, by rfl⟩ : syracuseStep 2515261 = 943223) (by norm_num)
theorem B3353681 : Blo 1959435 3353681 := bstep (se 2 (by rfl) ⟨1257630, by rfl⟩ : syracuseStep 3353681 = 2515261) B2515261
theorem B8943149 : Blo 1959435 8943149 := bstep (se 3 (by rfl) ⟨1676840, by rfl⟩ : syracuseStep 8943149 = 3353681) B3353681
theorem B5962099 : Blo 1959435 5962099 := bstep (se 1 (by rfl) ⟨4471574, by rfl⟩ : syracuseStep 5962099 = 8943149) B8943149
theorem B7949465 : Blo 1959435 7949465 := bstep (se 2 (by rfl) ⟨2981049, by rfl⟩ : syracuseStep 7949465 = 5962099) B5962099
theorem B5299643 : Blo 1959435 5299643 := bstep (se 1 (by rfl) ⟨3974732, by rfl⟩ : syracuseStep 5299643 = 7949465) B7949465
theorem B3533095 : Blo 1959435 3533095 := bstep (se 1 (by rfl) ⟨2649821, by rfl⟩ : syracuseStep 3533095 = 5299643) B5299643
theorem B4710793 : Blo 1959435 4710793 := bstep (se 2 (by rfl) ⟨1766547, by rfl⟩ : syracuseStep 4710793 = 3533095) B3533095
theorem B6281057 : Blo 1959435 6281057 := bstep (se 2 (by rfl) ⟨2355396, by rfl⟩ : syracuseStep 6281057 = 4710793) B4710793
theorem B4187371 : Blo 1959435 4187371 := bstep (se 1 (by rfl) ⟨3140528, by rfl⟩ : syracuseStep 4187371 = 6281057) B6281057
theorem B5583161 : Blo 1959435 5583161 := bstep (se 2 (by rfl) ⟨2093685, by rfl⟩ : syracuseStep 5583161 = 4187371) B4187371
theorem B3722107 : Blo 1959435 3722107 := bstep (se 1 (by rfl) ⟨2791580, by rfl⟩ : syracuseStep 3722107 = 5583161) B5583161
theorem B4962809 : Blo 1959435 4962809 := bstep (se 2 (by rfl) ⟨1861053, by rfl⟩ : syracuseStep 4962809 = 3722107) B3722107
theorem B3308539 : Blo 1959435 3308539 := bstep (se 1 (by rfl) ⟨2481404, by rfl⟩ : syracuseStep 3308539 = 4962809) B4962809
theorem B4411385 : Blo 1959435 4411385 := bstep (se 2 (by rfl) ⟨1654269, by rfl⟩ : syracuseStep 4411385 = 3308539) B3308539
theorem B2940923 : Blo 1959435 2940923 := bstep (se 1 (by rfl) ⟨2205692, by rfl⟩ : syracuseStep 2940923 = 4411385) B4411385
theorem B1960615 : Blo 1959435 1960615 := bstep (se 1 (by rfl) ⟨1470461, by rfl⟩ : syracuseStep 1960615 = 2940923) B2940923
theorem B2205697 : Blo 1959435 2205697 := bbase (se 2 (by rfl) ⟨827136, by rfl⟩ : syracuseStep 2205697 = 1654273) (by norm_num)
theorem B2940929 : Blo 1959435 2940929 := bstep (se 2 (by rfl) ⟨1102848, by rfl⟩ : syracuseStep 2940929 = 2205697) B2205697
theorem B1960619 : Blo 1959435 1960619 := bstep (se 1 (by rfl) ⟨1470464, by rfl⟩ : syracuseStep 1960619 = 2940929) B2940929
theorem B4962829 : Blo 1959435 4962829 := bbase (se 3 (by rfl) ⟨930530, by rfl⟩ : syracuseStep 4962829 = 1861061) (by norm_num)
theorem B6617105 : Blo 1959435 6617105 := bstep (se 2 (by rfl) ⟨2481414, by rfl⟩ : syracuseStep 6617105 = 4962829) B4962829
theorem B4411403 : Blo 1959435 4411403 := bstep (se 1 (by rfl) ⟨3308552, by rfl⟩ : syracuseStep 4411403 = 6617105) B6617105
theorem B2940935 : Blo 1959435 2940935 := bstep (se 1 (by rfl) ⟨2205701, by rfl⟩ : syracuseStep 2940935 = 4411403) B4411403
theorem B1960623 : Blo 1959435 1960623 := bstep (se 1 (by rfl) ⟨1470467, by rfl⟩ : syracuseStep 1960623 = 2940935) B2940935
theorem B2940941 : Blo 1959435 2940941 := bbase (se 3 (by rfl) ⟨551426, by rfl⟩ : syracuseStep 2940941 = 1102853) (by norm_num)
theorem B1960627 : Blo 1959435 1960627 := bstep (se 1 (by rfl) ⟨1470470, by rfl⟩ : syracuseStep 1960627 = 2940941) B2940941
theorem B4411421 : Blo 1959435 4411421 := bbase (se 3 (by rfl) ⟨827141, by rfl⟩ : syracuseStep 4411421 = 1654283) (by norm_num)
theorem B2940947 : Blo 1959435 2940947 := bstep (se 1 (by rfl) ⟨2205710, by rfl⟩ : syracuseStep 2940947 = 4411421) B4411421
theorem B1960631 : Blo 1959435 1960631 := bstep (se 1 (by rfl) ⟨1470473, by rfl⟩ : syracuseStep 1960631 = 2940947) B2940947
theorem B3308573 : Blo 1959435 3308573 := bbase (se 3 (by rfl) ⟨620357, by rfl⟩ : syracuseStep 3308573 = 1240715) (by norm_num)
theorem B2205715 : Blo 1959435 2205715 := bstep (se 1 (by rfl) ⟨1654286, by rfl⟩ : syracuseStep 2205715 = 3308573) B3308573
theorem B2940953 : Blo 1959435 2940953 := bstep (se 2 (by rfl) ⟨1102857, by rfl⟩ : syracuseStep 2940953 = 2205715) B2205715
theorem B1960635 : Blo 1959435 1960635 := bstep (se 1 (by rfl) ⟨1470476, by rfl⟩ : syracuseStep 1960635 = 2940953) B2940953
theorem B2649853 : Blo 1959435 2649853 := bbase (se 3 (by rfl) ⟨496847, by rfl⟩ : syracuseStep 2649853 = 993695) (by norm_num)
theorem B14132549 : Blo 1959435 14132549 := bstep (se 4 (by rfl) ⟨1324926, by rfl⟩ : syracuseStep 14132549 = 2649853) B2649853
theorem B9421699 : Blo 1959435 9421699 := bstep (se 1 (by rfl) ⟨7066274, by rfl⟩ : syracuseStep 9421699 = 14132549) B14132549
theorem B12562265 : Blo 1959435 12562265 := bstep (se 2 (by rfl) ⟨4710849, by rfl⟩ : syracuseStep 12562265 = 9421699) B9421699
theorem B8374843 : Blo 1959435 8374843 := bstep (se 1 (by rfl) ⟨6281132, by rfl⟩ : syracuseStep 8374843 = 12562265) B12562265
theorem B11166457 : Blo 1959435 11166457 := bstep (se 2 (by rfl) ⟨4187421, by rfl⟩ : syracuseStep 11166457 = 8374843) B8374843
theorem B14888609 : Blo 1959435 14888609 := bstep (se 2 (by rfl) ⟨5583228, by rfl⟩ : syracuseStep 14888609 = 11166457) B11166457
theorem B9925739 : Blo 1959435 9925739 := bstep (se 1 (by rfl) ⟨7444304, by rfl⟩ : syracuseStep 9925739 = 14888609) B14888609
theorem B6617159 : Blo 1959435 6617159 := bstep (se 1 (by rfl) ⟨4962869, by rfl⟩ : syracuseStep 6617159 = 9925739) B9925739
theorem B4411439 : Blo 1959435 4411439 := bstep (se 1 (by rfl) ⟨3308579, by rfl⟩ : syracuseStep 4411439 = 6617159) B6617159
theorem B2940959 : Blo 1959435 2940959 := bstep (se 1 (by rfl) ⟨2205719, by rfl⟩ : syracuseStep 2940959 = 4411439) B4411439
theorem B1960639 : Blo 1959435 1960639 := bstep (se 1 (by rfl) ⟨1470479, by rfl⟩ : syracuseStep 1960639 = 2940959) B2940959
theorem B2940965 : Blo 1959435 2940965 := bbase (se 4 (by rfl) ⟨275715, by rfl⟩ : syracuseStep 2940965 = 551431) (by norm_num)
theorem B1960643 : Blo 1959435 1960643 := bstep (se 1 (by rfl) ⟨1470482, by rfl⟩ : syracuseStep 1960643 = 2940965) B2940965
theorem B2481445 : Blo 1959435 2481445 := bbase (se 4 (by rfl) ⟨232635, by rfl⟩ : syracuseStep 2481445 = 465271) (by norm_num)
theorem B3308593 : Blo 1959435 3308593 := bstep (se 2 (by rfl) ⟨1240722, by rfl⟩ : syracuseStep 3308593 = 2481445) B2481445
theorem B4411457 : Blo 1959435 4411457 := bstep (se 2 (by rfl) ⟨1654296, by rfl⟩ : syracuseStep 4411457 = 3308593) B3308593
theorem B2940971 : Blo 1959435 2940971 := bstep (se 1 (by rfl) ⟨2205728, by rfl⟩ : syracuseStep 2940971 = 4411457) B4411457
theorem B1960647 : Blo 1959435 1960647 := bstep (se 1 (by rfl) ⟨1470485, by rfl⟩ : syracuseStep 1960647 = 2940971) B2940971
theorem B2205733 : Blo 1959435 2205733 := bbase (se 4 (by rfl) ⟨206787, by rfl⟩ : syracuseStep 2205733 = 413575) (by norm_num)
theorem B2940977 : Blo 1959435 2940977 := bstep (se 2 (by rfl) ⟨1102866, by rfl⟩ : syracuseStep 2940977 = 2205733) B2205733
theorem B1960651 : Blo 1959435 1960651 := bstep (se 1 (by rfl) ⟨1470488, by rfl⟩ : syracuseStep 1960651 = 2940977) B2940977
theorem B13414997 : Blo 1959435 13414997 := bbase (se 8 (by rfl) ⟨78603, by rfl⟩ : syracuseStep 13414997 = 157207) (by norm_num)
theorem B8943331 : Blo 1959435 8943331 := bstep (se 1 (by rfl) ⟨6707498, by rfl⟩ : syracuseStep 8943331 = 13414997) B13414997
theorem B11924441 : Blo 1959435 11924441 := bstep (se 2 (by rfl) ⟨4471665, by rfl⟩ : syracuseStep 11924441 = 8943331) B8943331
theorem B7949627 : Blo 1959435 7949627 := bstep (se 1 (by rfl) ⟨5962220, by rfl⟩ : syracuseStep 7949627 = 11924441) B11924441
theorem B5299751 : Blo 1959435 5299751 := bstep (se 1 (by rfl) ⟨3974813, by rfl⟩ : syracuseStep 5299751 = 7949627) B7949627
theorem B3533167 : Blo 1959435 3533167 := bstep (se 1 (by rfl) ⟨2649875, by rfl⟩ : syracuseStep 3533167 = 5299751) B5299751
theorem B4710889 : Blo 1959435 4710889 := bstep (se 2 (by rfl) ⟨1766583, by rfl⟩ : syracuseStep 4710889 = 3533167) B3533167
theorem B6281185 : Blo 1959435 6281185 := bstep (se 2 (by rfl) ⟨2355444, by rfl⟩ : syracuseStep 6281185 = 4710889) B4710889
theorem B8374913 : Blo 1959435 8374913 := bstep (se 2 (by rfl) ⟨3140592, by rfl⟩ : syracuseStep 8374913 = 6281185) B6281185
theorem B5583275 : Blo 1959435 5583275 := bstep (se 1 (by rfl) ⟨4187456, by rfl⟩ : syracuseStep 5583275 = 8374913) B8374913
theorem B3722183 : Blo 1959435 3722183 := bstep (se 1 (by rfl) ⟨2791637, by rfl⟩ : syracuseStep 3722183 = 5583275) B5583275
theorem B2481455 : Blo 1959435 2481455 := bstep (se 1 (by rfl) ⟨1861091, by rfl⟩ : syracuseStep 2481455 = 3722183) B3722183
theorem B6617213 : Blo 1959435 6617213 := bstep (se 3 (by rfl) ⟨1240727, by rfl⟩ : syracuseStep 6617213 = 2481455) B2481455
theorem B4411475 : Blo 1959435 4411475 := bstep (se 1 (by rfl) ⟨3308606, by rfl⟩ : syracuseStep 4411475 = 6617213) B6617213
theorem B2940983 : Blo 1959435 2940983 := bstep (se 1 (by rfl) ⟨2205737, by rfl⟩ : syracuseStep 2940983 = 4411475) B4411475
theorem B1960655 : Blo 1959435 1960655 := bstep (se 1 (by rfl) ⟨1470491, by rfl⟩ : syracuseStep 1960655 = 2940983) B2940983
theorem B2940989 : Blo 1959435 2940989 := bbase (se 3 (by rfl) ⟨551435, by rfl⟩ : syracuseStep 2940989 = 1102871) (by norm_num)
theorem B1960659 : Blo 1959435 1960659 := bstep (se 1 (by rfl) ⟨1470494, by rfl⟩ : syracuseStep 1960659 = 2940989) B2940989
theorem B4411493 : Blo 1959435 4411493 := bbase (se 4 (by rfl) ⟨413577, by rfl⟩ : syracuseStep 4411493 = 827155) (by norm_num)
theorem B2940995 : Blo 1959435 2940995 := bstep (se 1 (by rfl) ⟨2205746, by rfl⟩ : syracuseStep 2940995 = 4411493) B4411493
theorem B1960663 : Blo 1959435 1960663 := bstep (se 1 (by rfl) ⟨1470497, by rfl⟩ : syracuseStep 1960663 = 2940995) B2940995
theorem B4962941 : Blo 1959435 4962941 := bbase (se 3 (by rfl) ⟨930551, by rfl⟩ : syracuseStep 4962941 = 1861103) (by norm_num)
theorem B3308627 : Blo 1959435 3308627 := bstep (se 1 (by rfl) ⟨2481470, by rfl⟩ : syracuseStep 3308627 = 4962941) B4962941
theorem B2205751 : Blo 1959435 2205751 := bstep (se 1 (by rfl) ⟨1654313, by rfl⟩ : syracuseStep 2205751 = 3308627) B3308627
theorem B2941001 : Blo 1959435 2941001 := bstep (se 2 (by rfl) ⟨1102875, by rfl⟩ : syracuseStep 2941001 = 2205751) B2205751
theorem B1960667 : Blo 1959435 1960667 := bstep (se 1 (by rfl) ⟨1470500, by rfl⟩ : syracuseStep 1960667 = 2941001) B2941001
theorem B3722213 : Blo 1959435 3722213 := bbase (se 4 (by rfl) ⟨348957, by rfl⟩ : syracuseStep 3722213 = 697915) (by norm_num)
theorem B9925901 : Blo 1959435 9925901 := bstep (se 3 (by rfl) ⟨1861106, by rfl⟩ : syracuseStep 9925901 = 3722213) B3722213
theorem B6617267 : Blo 1959435 6617267 := bstep (se 1 (by rfl) ⟨4962950, by rfl⟩ : syracuseStep 6617267 = 9925901) B9925901
theorem B4411511 : Blo 1959435 4411511 := bstep (se 1 (by rfl) ⟨3308633, by rfl⟩ : syracuseStep 4411511 = 6617267) B6617267
theorem B2941007 : Blo 1959435 2941007 := bstep (se 1 (by rfl) ⟨2205755, by rfl⟩ : syracuseStep 2941007 = 4411511) B4411511
theorem B1960671 : Blo 1959435 1960671 := bstep (se 1 (by rfl) ⟨1470503, by rfl⟩ : syracuseStep 1960671 = 2941007) B2941007
theorem B2941013 : Blo 1959435 2941013 := bbase (se 8 (by rfl) ⟨17232, by rfl⟩ : syracuseStep 2941013 = 34465) (by norm_num)
theorem B1960675 : Blo 1959435 1960675 := bstep (se 1 (by rfl) ⟨1470506, by rfl⟩ : syracuseStep 1960675 = 2941013) B2941013
theorem B2420185 : Blo 1959435 2420185 := bbase (se 2 (by rfl) ⟨907569, by rfl⟩ : syracuseStep 2420185 = 1815139) (by norm_num)
theorem B3226913 : Blo 1959435 3226913 := bstep (se 2 (by rfl) ⟨1210092, by rfl⟩ : syracuseStep 3226913 = 2420185) B2420185
theorem B34420405 : Blo 1959435 34420405 := bstep (se 5 (by rfl) ⟨1613456, by rfl⟩ : syracuseStep 34420405 = 3226913) B3226913
theorem B45893873 : Blo 1959435 45893873 := bstep (se 2 (by rfl) ⟨17210202, by rfl⟩ : syracuseStep 45893873 = 34420405) B34420405
theorem B30595915 : Blo 1959435 30595915 := bstep (se 1 (by rfl) ⟨22946936, by rfl⟩ : syracuseStep 30595915 = 45893873) B45893873
theorem B40794553 : Blo 1959435 40794553 := bstep (se 2 (by rfl) ⟨15297957, by rfl⟩ : syracuseStep 40794553 = 30595915) B30595915
theorem B54392737 : Blo 1959435 54392737 := bstep (se 2 (by rfl) ⟨20397276, by rfl⟩ : syracuseStep 54392737 = 40794553) B40794553
theorem B72523649 : Blo 1959435 72523649 := bstep (se 2 (by rfl) ⟨27196368, by rfl⟩ : syracuseStep 72523649 = 54392737) B54392737
theorem B48349099 : Blo 1959435 48349099 := bstep (se 1 (by rfl) ⟨36261824, by rfl⟩ : syracuseStep 48349099 = 72523649) B72523649
theorem B64465465 : Blo 1959435 64465465 := bstep (se 2 (by rfl) ⟨24174549, by rfl⟩ : syracuseStep 64465465 = 48349099) B48349099
theorem B85953953 : Blo 1959435 85953953 := bstep (se 2 (by rfl) ⟨32232732, by rfl⟩ : syracuseStep 85953953 = 64465465) B64465465
theorem B57302635 : Blo 1959435 57302635 := bstep (se 1 (by rfl) ⟨42976976, by rfl⟩ : syracuseStep 57302635 = 85953953) B85953953
theorem B76403513 : Blo 1959435 76403513 := bstep (se 2 (by rfl) ⟨28651317, by rfl⟩ : syracuseStep 76403513 = 57302635) B57302635
theorem B50935675 : Blo 1959435 50935675 := bstep (se 1 (by rfl) ⟨38201756, by rfl⟩ : syracuseStep 50935675 = 76403513) B76403513
theorem B67914233 : Blo 1959435 67914233 := bstep (se 2 (by rfl) ⟨25467837, by rfl⟩ : syracuseStep 67914233 = 50935675) B50935675
theorem B45276155 : Blo 1959435 45276155 := bstep (se 1 (by rfl) ⟨33957116, by rfl⟩ : syracuseStep 45276155 = 67914233) B67914233
theorem B30184103 : Blo 1959435 30184103 := bstep (se 1 (by rfl) ⟨22638077, by rfl⟩ : syracuseStep 30184103 = 45276155) B45276155
theorem B80490941 : Blo 1959435 80490941 := bstep (se 3 (by rfl) ⟨15092051, by rfl⟩ : syracuseStep 80490941 = 30184103) B30184103
theorem B53660627 : Blo 1959435 53660627 := bstep (se 1 (by rfl) ⟨40245470, by rfl⟩ : syracuseStep 53660627 = 80490941) B80490941
theorem B35773751 : Blo 1959435 35773751 := bstep (se 1 (by rfl) ⟨26830313, by rfl⟩ : syracuseStep 35773751 = 53660627) B53660627
theorem B23849167 : Blo 1959435 23849167 := bstep (se 1 (by rfl) ⟨17886875, by rfl⟩ : syracuseStep 23849167 = 35773751) B35773751
theorem B31798889 : Blo 1959435 31798889 := bstep (se 2 (by rfl) ⟨11924583, by rfl⟩ : syracuseStep 31798889 = 23849167) B23849167
theorem B21199259 : Blo 1959435 21199259 := bstep (se 1 (by rfl) ⟨15899444, by rfl⟩ : syracuseStep 21199259 = 31798889) B31798889
theorem B14132839 : Blo 1959435 14132839 := bstep (se 1 (by rfl) ⟨10599629, by rfl⟩ : syracuseStep 14132839 = 21199259) B21199259
theorem B18843785 : Blo 1959435 18843785 := bstep (se 2 (by rfl) ⟨7066419, by rfl⟩ : syracuseStep 18843785 = 14132839) B14132839
theorem B12562523 : Blo 1959435 12562523 := bstep (se 1 (by rfl) ⟨9421892, by rfl⟩ : syracuseStep 12562523 = 18843785) B18843785
theorem B8375015 : Blo 1959435 8375015 := bstep (se 1 (by rfl) ⟨6281261, by rfl⟩ : syracuseStep 8375015 = 12562523) B12562523
theorem B5583343 : Blo 1959435 5583343 := bstep (se 1 (by rfl) ⟨4187507, by rfl⟩ : syracuseStep 5583343 = 8375015) B8375015
theorem B7444457 : Blo 1959435 7444457 := bstep (se 2 (by rfl) ⟨2791671, by rfl⟩ : syracuseStep 7444457 = 5583343) B5583343
theorem B4962971 : Blo 1959435 4962971 := bstep (se 1 (by rfl) ⟨3722228, by rfl⟩ : syracuseStep 4962971 = 7444457) B7444457
theorem B3308647 : Blo 1959435 3308647 := bstep (se 1 (by rfl) ⟨2481485, by rfl⟩ : syracuseStep 3308647 = 4962971) B4962971
theorem B4411529 : Blo 1959435 4411529 := bstep (se 2 (by rfl) ⟨1654323, by rfl⟩ : syracuseStep 4411529 = 3308647) B3308647
theorem B2941019 : Blo 1959435 2941019 := bstep (se 1 (by rfl) ⟨2205764, by rfl⟩ : syracuseStep 2941019 = 4411529) B4411529
theorem B1960679 : Blo 1959435 1960679 := bstep (se 1 (by rfl) ⟨1470509, by rfl⟩ : syracuseStep 1960679 = 2941019) B2941019
theorem B2205769 : Blo 1959435 2205769 := bbase (se 2 (by rfl) ⟨827163, by rfl⟩ : syracuseStep 2205769 = 1654327) (by norm_num)
theorem B2941025 : Blo 1959435 2941025 := bstep (se 2 (by rfl) ⟨1102884, by rfl⟩ : syracuseStep 2941025 = 2205769) B2205769
theorem B1960683 : Blo 1959435 1960683 := bstep (se 1 (by rfl) ⟨1470512, by rfl⟩ : syracuseStep 1960683 = 2941025) B2941025
theorem B4710965 : Blo 1959435 4710965 := bbase (se 5 (by rfl) ⟨220826, by rfl⟩ : syracuseStep 4710965 = 441653) (by norm_num)
theorem B12562573 : Blo 1959435 12562573 := bstep (se 3 (by rfl) ⟨2355482, by rfl⟩ : syracuseStep 12562573 = 4710965) B4710965
theorem B16750097 : Blo 1959435 16750097 := bstep (se 2 (by rfl) ⟨6281286, by rfl⟩ : syracuseStep 16750097 = 12562573) B12562573
theorem B11166731 : Blo 1959435 11166731 := bstep (se 1 (by rfl) ⟨8375048, by rfl⟩ : syracuseStep 11166731 = 16750097) B16750097
theorem B7444487 : Blo 1959435 7444487 := bstep (se 1 (by rfl) ⟨5583365, by rfl⟩ : syracuseStep 7444487 = 11166731) B11166731
theorem B4962991 : Blo 1959435 4962991 := bstep (se 1 (by rfl) ⟨3722243, by rfl⟩ : syracuseStep 4962991 = 7444487) B7444487
theorem B6617321 : Blo 1959435 6617321 := bstep (se 2 (by rfl) ⟨2481495, by rfl⟩ : syracuseStep 6617321 = 4962991) B4962991
theorem B4411547 : Blo 1959435 4411547 := bstep (se 1 (by rfl) ⟨3308660, by rfl⟩ : syracuseStep 4411547 = 6617321) B6617321
theorem B2941031 : Blo 1959435 2941031 := bstep (se 1 (by rfl) ⟨2205773, by rfl⟩ : syracuseStep 2941031 = 4411547) B4411547
theorem B1960687 : Blo 1959435 1960687 := bstep (se 1 (by rfl) ⟨1470515, by rfl⟩ : syracuseStep 1960687 = 2941031) B2941031
theorem B2941037 : Blo 1959435 2941037 := bbase (se 3 (by rfl) ⟨551444, by rfl⟩ : syracuseStep 2941037 = 1102889) (by norm_num)
theorem B1960691 : Blo 1959435 1960691 := bstep (se 1 (by rfl) ⟨1470518, by rfl⟩ : syracuseStep 1960691 = 2941037) B2941037
theorem B4411565 : Blo 1959435 4411565 := bbase (se 3 (by rfl) ⟨827168, by rfl⟩ : syracuseStep 4411565 = 1654337) (by norm_num)
theorem B2941043 : Blo 1959435 2941043 := bstep (se 1 (by rfl) ⟨2205782, by rfl⟩ : syracuseStep 2941043 = 4411565) B4411565
theorem B1960695 : Blo 1959435 1960695 := bstep (se 1 (by rfl) ⟨1470521, by rfl⟩ : syracuseStep 1960695 = 2941043) B2941043
theorem B3581453 : Blo 1959435 3581453 := bbase (se 3 (by rfl) ⟨671522, by rfl⟩ : syracuseStep 3581453 = 1343045) (by norm_num)
theorem B9550541 : Blo 1959435 9550541 := bstep (se 3 (by rfl) ⟨1790726, by rfl⟩ : syracuseStep 9550541 = 3581453) B3581453
theorem B6367027 : Blo 1959435 6367027 := bstep (se 1 (by rfl) ⟨4775270, by rfl⟩ : syracuseStep 6367027 = 9550541) B9550541
theorem B8489369 : Blo 1959435 8489369 := bstep (se 2 (by rfl) ⟨3183513, by rfl⟩ : syracuseStep 8489369 = 6367027) B6367027
theorem B5659579 : Blo 1959435 5659579 := bstep (se 1 (by rfl) ⟨4244684, by rfl⟩ : syracuseStep 5659579 = 8489369) B8489369
theorem B7546105 : Blo 1959435 7546105 := bstep (se 2 (by rfl) ⟨2829789, by rfl⟩ : syracuseStep 7546105 = 5659579) B5659579
theorem B40245893 : Blo 1959435 40245893 := bstep (se 4 (by rfl) ⟨3773052, by rfl⟩ : syracuseStep 40245893 = 7546105) B7546105
theorem B26830595 : Blo 1959435 26830595 := bstep (se 1 (by rfl) ⟨20122946, by rfl⟩ : syracuseStep 26830595 = 40245893) B40245893
theorem B17887063 : Blo 1959435 17887063 := bstep (se 1 (by rfl) ⟨13415297, by rfl⟩ : syracuseStep 17887063 = 26830595) B26830595
theorem B23849417 : Blo 1959435 23849417 := bstep (se 2 (by rfl) ⟨8943531, by rfl⟩ : syracuseStep 23849417 = 17887063) B17887063
theorem B15899611 : Blo 1959435 15899611 := bstep (se 1 (by rfl) ⟨11924708, by rfl⟩ : syracuseStep 15899611 = 23849417) B23849417
theorem B21199481 : Blo 1959435 21199481 := bstep (se 2 (by rfl) ⟨7949805, by rfl⟩ : syracuseStep 21199481 = 15899611) B15899611
theorem B14132987 : Blo 1959435 14132987 := bstep (se 1 (by rfl) ⟨10599740, by rfl⟩ : syracuseStep 14132987 = 21199481) B21199481
theorem B9421991 : Blo 1959435 9421991 := bstep (se 1 (by rfl) ⟨7066493, by rfl⟩ : syracuseStep 9421991 = 14132987) B14132987
theorem B6281327 : Blo 1959435 6281327 := bstep (se 1 (by rfl) ⟨4710995, by rfl⟩ : syracuseStep 6281327 = 9421991) B9421991
theorem B4187551 : Blo 1959435 4187551 := bstep (se 1 (by rfl) ⟨3140663, by rfl⟩ : syracuseStep 4187551 = 6281327) B6281327
theorem B5583401 : Blo 1959435 5583401 := bstep (se 2 (by rfl) ⟨2093775, by rfl⟩ : syracuseStep 5583401 = 4187551) B4187551
theorem B3722267 : Blo 1959435 3722267 := bstep (se 1 (by rfl) ⟨2791700, by rfl⟩ : syracuseStep 3722267 = 5583401) B5583401
theorem B2481511 : Blo 1959435 2481511 := bstep (se 1 (by rfl) ⟨1861133, by rfl⟩ : syracuseStep 2481511 = 3722267) B3722267
theorem B3308681 : Blo 1959435 3308681 := bstep (se 2 (by rfl) ⟨1240755, by rfl⟩ : syracuseStep 3308681 = 2481511) B2481511
theorem B2205787 : Blo 1959435 2205787 := bstep (se 1 (by rfl) ⟨1654340, by rfl⟩ : syracuseStep 2205787 = 3308681) B3308681
theorem B2941049 : Blo 1959435 2941049 := bstep (se 2 (by rfl) ⟨1102893, by rfl⟩ : syracuseStep 2941049 = 2205787) B2205787
theorem B1960699 : Blo 1959435 1960699 := bstep (se 1 (by rfl) ⟨1470524, by rfl⟩ : syracuseStep 1960699 = 2941049) B2941049
theorem B5659589 : Blo 1959435 5659589 := bbase (se 4 (by rfl) ⟨530586, by rfl⟩ : syracuseStep 5659589 = 1061173) (by norm_num)
theorem B15092237 : Blo 1959435 15092237 := bstep (se 3 (by rfl) ⟨2829794, by rfl⟩ : syracuseStep 15092237 = 5659589) B5659589
theorem B10061491 : Blo 1959435 10061491 := bstep (se 1 (by rfl) ⟨7546118, by rfl⟩ : syracuseStep 10061491 = 15092237) B15092237
theorem B13415321 : Blo 1959435 13415321 := bstep (se 2 (by rfl) ⟨5030745, by rfl⟩ : syracuseStep 13415321 = 10061491) B10061491
theorem B8943547 : Blo 1959435 8943547 := bstep (se 1 (by rfl) ⟨6707660, by rfl⟩ : syracuseStep 8943547 = 13415321) B13415321
theorem B11924729 : Blo 1959435 11924729 := bstep (se 2 (by rfl) ⟨4471773, by rfl⟩ : syracuseStep 11924729 = 8943547) B8943547
theorem B7949819 : Blo 1959435 7949819 := bstep (se 1 (by rfl) ⟨5962364, by rfl⟩ : syracuseStep 7949819 = 11924729) B11924729
theorem B5299879 : Blo 1959435 5299879 := bstep (se 1 (by rfl) ⟨3974909, by rfl⟩ : syracuseStep 5299879 = 7949819) B7949819
theorem B7066505 : Blo 1959435 7066505 := bstep (se 2 (by rfl) ⟨2649939, by rfl⟩ : syracuseStep 7066505 = 5299879) B5299879
theorem B4711003 : Blo 1959435 4711003 := bstep (se 1 (by rfl) ⟨3533252, by rfl⟩ : syracuseStep 4711003 = 7066505) B7066505
theorem B25125349 : Blo 1959435 25125349 := bstep (se 4 (by rfl) ⟨2355501, by rfl⟩ : syracuseStep 25125349 = 4711003) B4711003
theorem B33500465 : Blo 1959435 33500465 := bstep (se 2 (by rfl) ⟨12562674, by rfl⟩ : syracuseStep 33500465 = 25125349) B25125349
theorem B22333643 : Blo 1959435 22333643 := bstep (se 1 (by rfl) ⟨16750232, by rfl⟩ : syracuseStep 22333643 = 33500465) B33500465
theorem B14889095 : Blo 1959435 14889095 := bstep (se 1 (by rfl) ⟨11166821, by rfl⟩ : syracuseStep 14889095 = 22333643) B22333643
theorem B9926063 : Blo 1959435 9926063 := bstep (se 1 (by rfl) ⟨7444547, by rfl⟩ : syracuseStep 9926063 = 14889095) B14889095
theorem B6617375 : Blo 1959435 6617375 := bstep (se 1 (by rfl) ⟨4963031, by rfl⟩ : syracuseStep 6617375 = 9926063) B9926063
theorem B4411583 : Blo 1959435 4411583 := bstep (se 1 (by rfl) ⟨3308687, by rfl⟩ : syracuseStep 4411583 = 6617375) B6617375
theorem B2941055 : Blo 1959435 2941055 := bstep (se 1 (by rfl) ⟨2205791, by rfl⟩ : syracuseStep 2941055 = 4411583) B4411583
theorem B1960703 : Blo 1959435 1960703 := bstep (se 1 (by rfl) ⟨1470527, by rfl⟩ : syracuseStep 1960703 = 2941055) B2941055
theorem B2941061 : Blo 1959435 2941061 := bbase (se 4 (by rfl) ⟨275724, by rfl⟩ : syracuseStep 2941061 = 551449) (by norm_num)
theorem B1960707 : Blo 1959435 1960707 := bstep (se 1 (by rfl) ⟨1470530, by rfl⟩ : syracuseStep 1960707 = 2941061) B2941061
theorem B3308701 : Blo 1959435 3308701 := bbase (se 3 (by rfl) ⟨620381, by rfl⟩ : syracuseStep 3308701 = 1240763) (by norm_num)
theorem B4411601 : Blo 1959435 4411601 := bstep (se 2 (by rfl) ⟨1654350, by rfl⟩ : syracuseStep 4411601 = 3308701) B3308701
theorem B2941067 : Blo 1959435 2941067 := bstep (se 1 (by rfl) ⟨2205800, by rfl⟩ : syracuseStep 2941067 = 4411601) B4411601
theorem B1960711 : Blo 1959435 1960711 := bstep (se 1 (by rfl) ⟨1470533, by rfl⟩ : syracuseStep 1960711 = 2941067) B2941067
theorem B2205805 : Blo 1959435 2205805 := bbase (se 3 (by rfl) ⟨413588, by rfl⟩ : syracuseStep 2205805 = 827177) (by norm_num)
theorem B2941073 : Blo 1959435 2941073 := bstep (se 2 (by rfl) ⟨1102902, by rfl⟩ : syracuseStep 2941073 = 2205805) B2205805
theorem B1960715 : Blo 1959435 1960715 := bstep (se 1 (by rfl) ⟨1470536, by rfl⟩ : syracuseStep 1960715 = 2941073) B2941073
theorem B6617429 : Blo 1959435 6617429 := bbase (se 10 (by rfl) ⟨9693, by rfl⟩ : syracuseStep 6617429 = 19387) (by norm_num)
theorem B4411619 : Blo 1959435 4411619 := bstep (se 1 (by rfl) ⟨3308714, by rfl⟩ : syracuseStep 4411619 = 6617429) B6617429
theorem B2941079 : Blo 1959435 2941079 := bstep (se 1 (by rfl) ⟨2205809, by rfl⟩ : syracuseStep 2941079 = 4411619) B4411619
theorem B1960719 : Blo 1959435 1960719 := bstep (se 1 (by rfl) ⟨1470539, by rfl⟩ : syracuseStep 1960719 = 2941079) B2941079
theorem B2941085 : Blo 1959435 2941085 := bbase (se 3 (by rfl) ⟨551453, by rfl⟩ : syracuseStep 2941085 = 1102907) (by norm_num)
theorem B1960723 : Blo 1959435 1960723 := bstep (se 1 (by rfl) ⟨1470542, by rfl⟩ : syracuseStep 1960723 = 2941085) B2941085
theorem B4411637 : Blo 1959435 4411637 := bbase (se 5 (by rfl) ⟨206795, by rfl⟩ : syracuseStep 4411637 = 413591) (by norm_num)
theorem B2941091 : Blo 1959435 2941091 := bstep (se 1 (by rfl) ⟨2205818, by rfl⟩ : syracuseStep 2941091 = 4411637) B4411637
theorem B1960727 : Blo 1959435 1960727 := bstep (se 1 (by rfl) ⟨1470545, by rfl⟩ : syracuseStep 1960727 = 2941091) B2941091
theorem B3183565 : Blo 1959435 3183565 := bbase (se 3 (by rfl) ⟨596918, by rfl⟩ : syracuseStep 3183565 = 1193837) (by norm_num)
theorem B4244753 : Blo 1959435 4244753 := bstep (se 2 (by rfl) ⟨1591782, by rfl⟩ : syracuseStep 4244753 = 3183565) B3183565
theorem B2829835 : Blo 1959435 2829835 := bstep (se 1 (by rfl) ⟨2122376, by rfl⟩ : syracuseStep 2829835 = 4244753) B4244753
theorem B15092453 : Blo 1959435 15092453 := bstep (se 4 (by rfl) ⟨1414917, by rfl⟩ : syracuseStep 15092453 = 2829835) B2829835
theorem B40246541 : Blo 1959435 40246541 := bstep (se 3 (by rfl) ⟨7546226, by rfl⟩ : syracuseStep 40246541 = 15092453) B15092453
theorem B26831027 : Blo 1959435 26831027 := bstep (se 1 (by rfl) ⟨20123270, by rfl⟩ : syracuseStep 26831027 = 40246541) B40246541
theorem B17887351 : Blo 1959435 17887351 := bstep (se 1 (by rfl) ⟨13415513, by rfl⟩ : syracuseStep 17887351 = 26831027) B26831027
theorem B23849801 : Blo 1959435 23849801 := bstep (se 2 (by rfl) ⟨8943675, by rfl⟩ : syracuseStep 23849801 = 17887351) B17887351
theorem B15899867 : Blo 1959435 15899867 := bstep (se 1 (by rfl) ⟨11924900, by rfl⟩ : syracuseStep 15899867 = 23849801) B23849801
theorem B10599911 : Blo 1959435 10599911 := bstep (se 1 (by rfl) ⟨7949933, by rfl⟩ : syracuseStep 10599911 = 15899867) B15899867
theorem B7066607 : Blo 1959435 7066607 := bstep (se 1 (by rfl) ⟨5299955, by rfl⟩ : syracuseStep 7066607 = 10599911) B10599911
theorem B18844285 : Blo 1959435 18844285 := bstep (se 3 (by rfl) ⟨3533303, by rfl⟩ : syracuseStep 18844285 = 7066607) B7066607
theorem B25125713 : Blo 1959435 25125713 := bstep (se 2 (by rfl) ⟨9422142, by rfl⟩ : syracuseStep 25125713 = 18844285) B18844285
theorem B16750475 : Blo 1959435 16750475 := bstep (se 1 (by rfl) ⟨12562856, by rfl⟩ : syracuseStep 16750475 = 25125713) B25125713
theorem B11166983 : Blo 1959435 11166983 := bstep (se 1 (by rfl) ⟨8375237, by rfl⟩ : syracuseStep 11166983 = 16750475) B16750475
theorem B7444655 : Blo 1959435 7444655 := bstep (se 1 (by rfl) ⟨5583491, by rfl⟩ : syracuseStep 7444655 = 11166983) B11166983
theorem B4963103 : Blo 1959435 4963103 := bstep (se 1 (by rfl) ⟨3722327, by rfl⟩ : syracuseStep 4963103 = 7444655) B7444655
theorem B3308735 : Blo 1959435 3308735 := bstep (se 1 (by rfl) ⟨2481551, by rfl⟩ : syracuseStep 3308735 = 4963103) B4963103
theorem B2205823 : Blo 1959435 2205823 := bstep (se 1 (by rfl) ⟨1654367, by rfl⟩ : syracuseStep 2205823 = 3308735) B3308735
theorem B2941097 : Blo 1959435 2941097 := bstep (se 2 (by rfl) ⟨1102911, by rfl⟩ : syracuseStep 2941097 = 2205823) B2205823
theorem B1960731 : Blo 1959435 1960731 := bstep (se 1 (by rfl) ⟨1470548, by rfl⟩ : syracuseStep 1960731 = 2941097) B2941097
theorem B2797589 : Blo 1959435 2797589 := bbase (se 6 (by rfl) ⟨65568, by rfl⟩ : syracuseStep 2797589 = 131137) (by norm_num)
theorem B7460237 : Blo 1959435 7460237 := bstep (se 3 (by rfl) ⟨1398794, by rfl⟩ : syracuseStep 7460237 = 2797589) B2797589
theorem B4973491 : Blo 1959435 4973491 := bstep (se 1 (by rfl) ⟨3730118, by rfl⟩ : syracuseStep 4973491 = 7460237) B7460237
theorem B26525285 : Blo 1959435 26525285 := bstep (se 4 (by rfl) ⟨2486745, by rfl⟩ : syracuseStep 26525285 = 4973491) B4973491
theorem B17683523 : Blo 1959435 17683523 := bstep (se 1 (by rfl) ⟨13262642, by rfl⟩ : syracuseStep 17683523 = 26525285) B26525285
theorem B11789015 : Blo 1959435 11789015 := bstep (se 1 (by rfl) ⟨8841761, by rfl⟩ : syracuseStep 11789015 = 17683523) B17683523
theorem B125749493 : Blo 1959435 125749493 := bstep (se 5 (by rfl) ⟨5894507, by rfl⟩ : syracuseStep 125749493 = 11789015) B11789015
theorem B83832995 : Blo 1959435 83832995 := bstep (se 1 (by rfl) ⟨62874746, by rfl⟩ : syracuseStep 83832995 = 125749493) B125749493
theorem B55888663 : Blo 1959435 55888663 := bstep (se 1 (by rfl) ⟨41916497, by rfl⟩ : syracuseStep 55888663 = 83832995) B83832995
theorem B74518217 : Blo 1959435 74518217 := bstep (se 2 (by rfl) ⟨27944331, by rfl⟩ : syracuseStep 74518217 = 55888663) B55888663
theorem B49678811 : Blo 1959435 49678811 := bstep (se 1 (by rfl) ⟨37259108, by rfl⟩ : syracuseStep 49678811 = 74518217) B74518217
theorem B33119207 : Blo 1959435 33119207 := bstep (se 1 (by rfl) ⟨24839405, by rfl⟩ : syracuseStep 33119207 = 49678811) B49678811
theorem B22079471 : Blo 1959435 22079471 := bstep (se 1 (by rfl) ⟨16559603, by rfl⟩ : syracuseStep 22079471 = 33119207) B33119207
theorem B235514357 : Blo 1959435 235514357 := bstep (se 5 (by rfl) ⟨11039735, by rfl⟩ : syracuseStep 235514357 = 22079471) B22079471
theorem B157009571 : Blo 1959435 157009571 := bstep (se 1 (by rfl) ⟨117757178, by rfl⟩ : syracuseStep 157009571 = 235514357) B235514357
theorem B1674768757 : Blo 1959435 1674768757 := bstep (se 5 (by rfl) ⟨78504785, by rfl⟩ : syracuseStep 1674768757 = 157009571) B157009571
theorem B2233025009 : Blo 1959435 2233025009 := bstep (se 2 (by rfl) ⟨837384378, by rfl⟩ : syracuseStep 2233025009 = 1674768757) B1674768757
theorem B1488683339 : Blo 1959435 1488683339 := bstep (se 1 (by rfl) ⟨1116512504, by rfl⟩ : syracuseStep 1488683339 = 2233025009) B2233025009
theorem B992455559 : Blo 1959435 992455559 := bstep (se 1 (by rfl) ⟨744341669, by rfl⟩ : syracuseStep 992455559 = 1488683339) B1488683339
theorem B661637039 : Blo 1959435 661637039 := bstep (se 1 (by rfl) ⟨496227779, by rfl⟩ : syracuseStep 661637039 = 992455559) B992455559
theorem B1764365437 : Blo 1959435 1764365437 := bstep (se 3 (by rfl) ⟨330818519, by rfl⟩ : syracuseStep 1764365437 = 661637039) B661637039
theorem B2352487249 : Blo 1959435 2352487249 := bstep (se 2 (by rfl) ⟨882182718, by rfl⟩ : syracuseStep 2352487249 = 1764365437) B1764365437
theorem B3136649665 : Blo 1959435 3136649665 := bstep (se 2 (by rfl) ⟨1176243624, by rfl⟩ : syracuseStep 3136649665 = 2352487249) B2352487249
theorem B4182199553 : Blo 1959435 4182199553 := bstep (se 2 (by rfl) ⟨1568324832, by rfl⟩ : syracuseStep 4182199553 = 3136649665) B3136649665
theorem B2788133035 : Blo 1959435 2788133035 := bstep (se 1 (by rfl) ⟨2091099776, by rfl⟩ : syracuseStep 2788133035 = 4182199553) B4182199553
theorem B3717510713 : Blo 1959435 3717510713 := bstep (se 2 (by rfl) ⟨1394066517, by rfl⟩ : syracuseStep 3717510713 = 2788133035) B2788133035
theorem B2478340475 : Blo 1959435 2478340475 := bstep (se 1 (by rfl) ⟨1858755356, by rfl⟩ : syracuseStep 2478340475 = 3717510713) B3717510713
theorem B1652226983 : Blo 1959435 1652226983 := bstep (se 1 (by rfl) ⟨1239170237, by rfl⟩ : syracuseStep 1652226983 = 2478340475) B2478340475
theorem B1101484655 : Blo 1959435 1101484655 := bstep (se 1 (by rfl) ⟨826113491, by rfl⟩ : syracuseStep 1101484655 = 1652226983) B1652226983
theorem B734323103 : Blo 1959435 734323103 := bstep (se 1 (by rfl) ⟨550742327, by rfl⟩ : syracuseStep 734323103 = 1101484655) B1101484655
theorem B489548735 : Blo 1959435 489548735 := bstep (se 1 (by rfl) ⟨367161551, by rfl⟩ : syracuseStep 489548735 = 734323103) B734323103
theorem B326365823 : Blo 1959435 326365823 := bstep (se 1 (by rfl) ⟨244774367, by rfl⟩ : syracuseStep 326365823 = 489548735) B489548735
theorem B217577215 : Blo 1959435 217577215 := bstep (se 1 (by rfl) ⟨163182911, by rfl⟩ : syracuseStep 217577215 = 326365823) B326365823
theorem B290102953 : Blo 1959435 290102953 := bstep (se 2 (by rfl) ⟨108788607, by rfl⟩ : syracuseStep 290102953 = 217577215) B217577215
theorem B386803937 : Blo 1959435 386803937 := bstep (se 2 (by rfl) ⟨145051476, by rfl⟩ : syracuseStep 386803937 = 290102953) B290102953
theorem B257869291 : Blo 1959435 257869291 := bstep (se 1 (by rfl) ⟨193401968, by rfl⟩ : syracuseStep 257869291 = 386803937) B386803937
theorem B343825721 : Blo 1959435 343825721 := bstep (se 2 (by rfl) ⟨128934645, by rfl⟩ : syracuseStep 343825721 = 257869291) B257869291
theorem B229217147 : Blo 1959435 229217147 := bstep (se 1 (by rfl) ⟨171912860, by rfl⟩ : syracuseStep 229217147 = 343825721) B343825721
theorem B152811431 : Blo 1959435 152811431 := bstep (se 1 (by rfl) ⟨114608573, by rfl⟩ : syracuseStep 152811431 = 229217147) B229217147
theorem B101874287 : Blo 1959435 101874287 := bstep (se 1 (by rfl) ⟨76405715, by rfl⟩ : syracuseStep 101874287 = 152811431) B152811431
theorem B67916191 : Blo 1959435 67916191 := bstep (se 1 (by rfl) ⟨50937143, by rfl⟩ : syracuseStep 67916191 = 101874287) B101874287
theorem B90554921 : Blo 1959435 90554921 := bstep (se 2 (by rfl) ⟨33958095, by rfl⟩ : syracuseStep 90554921 = 67916191) B67916191
theorem B60369947 : Blo 1959435 60369947 := bstep (se 1 (by rfl) ⟨45277460, by rfl⟩ : syracuseStep 60369947 = 90554921) B90554921
theorem B40246631 : Blo 1959435 40246631 := bstep (se 1 (by rfl) ⟨30184973, by rfl⟩ : syracuseStep 40246631 = 60369947) B60369947
theorem B26831087 : Blo 1959435 26831087 := bstep (se 1 (by rfl) ⟨20123315, by rfl⟩ : syracuseStep 26831087 = 40246631) B40246631
theorem B17887391 : Blo 1959435 17887391 := bstep (se 1 (by rfl) ⟨13415543, by rfl⟩ : syracuseStep 17887391 = 26831087) B26831087
theorem B11924927 : Blo 1959435 11924927 := bstep (se 1 (by rfl) ⟨8943695, by rfl⟩ : syracuseStep 11924927 = 17887391) B17887391
theorem B7949951 : Blo 1959435 7949951 := bstep (se 1 (by rfl) ⟨5962463, by rfl⟩ : syracuseStep 7949951 = 11924927) B11924927
theorem B5299967 : Blo 1959435 5299967 := bstep (se 1 (by rfl) ⟨3974975, by rfl⟩ : syracuseStep 5299967 = 7949951) B7949951
theorem B3533311 : Blo 1959435 3533311 := bstep (se 1 (by rfl) ⟨2649983, by rfl⟩ : syracuseStep 3533311 = 5299967) B5299967
theorem B4711081 : Blo 1959435 4711081 := bstep (se 2 (by rfl) ⟨1766655, by rfl⟩ : syracuseStep 4711081 = 3533311) B3533311
theorem B6281441 : Blo 1959435 6281441 := bstep (se 2 (by rfl) ⟨2355540, by rfl⟩ : syracuseStep 6281441 = 4711081) B4711081
theorem B4187627 : Blo 1959435 4187627 := bstep (se 1 (by rfl) ⟨3140720, by rfl⟩ : syracuseStep 4187627 = 6281441) B6281441
theorem B2791751 : Blo 1959435 2791751 := bstep (se 1 (by rfl) ⟨2093813, by rfl⟩ : syracuseStep 2791751 = 4187627) B4187627
theorem B7444669 : Blo 1959435 7444669 := bstep (se 3 (by rfl) ⟨1395875, by rfl⟩ : syracuseStep 7444669 = 2791751) B2791751
theorem B9926225 : Blo 1959435 9926225 := bstep (se 2 (by rfl) ⟨3722334, by rfl⟩ : syracuseStep 9926225 = 7444669) B7444669
theorem B6617483 : Blo 1959435 6617483 := bstep (se 1 (by rfl) ⟨4963112, by rfl⟩ : syracuseStep 6617483 = 9926225) B9926225
theorem B4411655 : Blo 1959435 4411655 := bstep (se 1 (by rfl) ⟨3308741, by rfl⟩ : syracuseStep 4411655 = 6617483) B6617483
theorem B2941103 : Blo 1959435 2941103 := bstep (se 1 (by rfl) ⟨2205827, by rfl⟩ : syracuseStep 2941103 = 4411655) B4411655
theorem B1960735 : Blo 1959435 1960735 := bstep (se 1 (by rfl) ⟨1470551, by rfl⟩ : syracuseStep 1960735 = 2941103) B2941103
theorem B2941109 : Blo 1959435 2941109 := bbase (se 5 (by rfl) ⟨137864, by rfl⟩ : syracuseStep 2941109 = 275729) (by norm_num)
theorem B1960739 : Blo 1959435 1960739 := bstep (se 1 (by rfl) ⟨1470554, by rfl⟩ : syracuseStep 1960739 = 2941109) B2941109
theorem B4963133 : Blo 1959435 4963133 := bbase (se 3 (by rfl) ⟨930587, by rfl⟩ : syracuseStep 4963133 = 1861175) (by norm_num)
theorem B3308755 : Blo 1959435 3308755 := bstep (se 1 (by rfl) ⟨2481566, by rfl⟩ : syracuseStep 3308755 = 4963133) B4963133
theorem B4411673 : Blo 1959435 4411673 := bstep (se 2 (by rfl) ⟨1654377, by rfl⟩ : syracuseStep 4411673 = 3308755) B3308755
theorem B2941115 : Blo 1959435 2941115 := bstep (se 1 (by rfl) ⟨2205836, by rfl⟩ : syracuseStep 2941115 = 4411673) B4411673
theorem B1960743 : Blo 1959435 1960743 := bstep (se 1 (by rfl) ⟨1470557, by rfl⟩ : syracuseStep 1960743 = 2941115) B2941115
theorem B2205841 : Blo 1959435 2205841 := bbase (se 2 (by rfl) ⟨827190, by rfl⟩ : syracuseStep 2205841 = 1654381) (by norm_num)
theorem B2941121 : Blo 1959435 2941121 := bstep (se 2 (by rfl) ⟨1102920, by rfl⟩ : syracuseStep 2941121 = 2205841) B2205841
theorem B1960747 : Blo 1959435 1960747 := bstep (se 1 (by rfl) ⟨1470560, by rfl⟩ : syracuseStep 1960747 = 2941121) B2941121
theorem B3722365 : Blo 1959435 3722365 := bbase (se 3 (by rfl) ⟨697943, by rfl⟩ : syracuseStep 3722365 = 1395887) (by norm_num)
theorem B4963153 : Blo 1959435 4963153 := bstep (se 2 (by rfl) ⟨1861182, by rfl⟩ : syracuseStep 4963153 = 3722365) B3722365
theorem B6617537 : Blo 1959435 6617537 := bstep (se 2 (by rfl) ⟨2481576, by rfl⟩ : syracuseStep 6617537 = 4963153) B4963153
theorem B4411691 : Blo 1959435 4411691 := bstep (se 1 (by rfl) ⟨3308768, by rfl⟩ : syracuseStep 4411691 = 6617537) B6617537
theorem B2941127 : Blo 1959435 2941127 := bstep (se 1 (by rfl) ⟨2205845, by rfl⟩ : syracuseStep 2941127 = 4411691) B4411691
theorem B1960751 : Blo 1959435 1960751 := bstep (se 1 (by rfl) ⟨1470563, by rfl⟩ : syracuseStep 1960751 = 2941127) B2941127
theorem B2941133 : Blo 1959435 2941133 := bbase (se 3 (by rfl) ⟨551462, by rfl⟩ : syracuseStep 2941133 = 1102925) (by norm_num)
theorem B1960755 : Blo 1959435 1960755 := bstep (se 1 (by rfl) ⟨1470566, by rfl⟩ : syracuseStep 1960755 = 2941133) B2941133
theorem B4411709 : Blo 1959435 4411709 := bbase (se 3 (by rfl) ⟨827195, by rfl⟩ : syracuseStep 4411709 = 1654391) (by norm_num)
theorem B2941139 : Blo 1959435 2941139 := bstep (se 1 (by rfl) ⟨2205854, by rfl⟩ : syracuseStep 2941139 = 4411709) B4411709
theorem B1960759 : Blo 1959435 1960759 := bstep (se 1 (by rfl) ⟨1470569, by rfl⟩ : syracuseStep 1960759 = 2941139) B2941139
theorem B3308789 : Blo 1959435 3308789 := bbase (se 5 (by rfl) ⟨155099, by rfl⟩ : syracuseStep 3308789 = 310199) (by norm_num)
theorem B2205859 : Blo 1959435 2205859 := bstep (se 1 (by rfl) ⟨1654394, by rfl⟩ : syracuseStep 2205859 = 3308789) B3308789
theorem B2941145 : Blo 1959435 2941145 := bstep (se 2 (by rfl) ⟨1102929, by rfl⟩ : syracuseStep 2941145 = 2205859) B2205859
theorem B1960763 : Blo 1959435 1960763 := bstep (se 1 (by rfl) ⟨1470572, by rfl⟩ : syracuseStep 1960763 = 2941145) B2941145
theorem B188627285 : Blo 1959435 188627285 := bbase (se 10 (by rfl) ⟨276309, by rfl⟩ : syracuseStep 188627285 = 552619) (by norm_num)
theorem B125751523 : Blo 1959435 125751523 := bstep (se 1 (by rfl) ⟨94313642, by rfl⟩ : syracuseStep 125751523 = 188627285) B188627285
theorem B167668697 : Blo 1959435 167668697 := bstep (se 2 (by rfl) ⟨62875761, by rfl⟩ : syracuseStep 167668697 = 125751523) B125751523
theorem B111779131 : Blo 1959435 111779131 := bstep (se 1 (by rfl) ⟨83834348, by rfl⟩ : syracuseStep 111779131 = 167668697) B167668697
theorem B149038841 : Blo 1959435 149038841 := bstep (se 2 (by rfl) ⟨55889565, by rfl⟩ : syracuseStep 149038841 = 111779131) B111779131
theorem B99359227 : Blo 1959435 99359227 := bstep (se 1 (by rfl) ⟨74519420, by rfl⟩ : syracuseStep 99359227 = 149038841) B149038841
theorem B529915877 : Blo 1959435 529915877 := bstep (se 4 (by rfl) ⟨49679613, by rfl⟩ : syracuseStep 529915877 = 99359227) B99359227
theorem B353277251 : Blo 1959435 353277251 := bstep (se 1 (by rfl) ⟨264957938, by rfl⟩ : syracuseStep 353277251 = 529915877) B529915877
theorem B235518167 : Blo 1959435 235518167 := bstep (se 1 (by rfl) ⟨176638625, by rfl⟩ : syracuseStep 235518167 = 353277251) B353277251
theorem B157012111 : Blo 1959435 157012111 := bstep (se 1 (by rfl) ⟨117759083, by rfl⟩ : syracuseStep 157012111 = 235518167) B235518167
theorem B837397925 : Blo 1959435 837397925 := bstep (se 4 (by rfl) ⟨78506055, by rfl⟩ : syracuseStep 837397925 = 157012111) B157012111
theorem B558265283 : Blo 1959435 558265283 := bstep (se 1 (by rfl) ⟨418698962, by rfl⟩ : syracuseStep 558265283 = 837397925) B837397925
theorem B372176855 : Blo 1959435 372176855 := bstep (se 1 (by rfl) ⟨279132641, by rfl⟩ : syracuseStep 372176855 = 558265283) B558265283
theorem B248117903 : Blo 1959435 248117903 := bstep (se 1 (by rfl) ⟨186088427, by rfl⟩ : syracuseStep 248117903 = 372176855) B372176855
theorem B165411935 : Blo 1959435 165411935 := bstep (se 1 (by rfl) ⟨124058951, by rfl⟩ : syracuseStep 165411935 = 248117903) B248117903
theorem B110274623 : Blo 1959435 110274623 := bstep (se 1 (by rfl) ⟨82705967, by rfl⟩ : syracuseStep 110274623 = 165411935) B165411935
theorem B73516415 : Blo 1959435 73516415 := bstep (se 1 (by rfl) ⟨55137311, by rfl⟩ : syracuseStep 73516415 = 110274623) B110274623
theorem B196043773 : Blo 1959435 196043773 := bstep (se 3 (by rfl) ⟨36758207, by rfl⟩ : syracuseStep 196043773 = 73516415) B73516415
theorem B261391697 : Blo 1959435 261391697 := bstep (se 2 (by rfl) ⟨98021886, by rfl⟩ : syracuseStep 261391697 = 196043773) B196043773
theorem B174261131 : Blo 1959435 174261131 := bstep (se 1 (by rfl) ⟨130695848, by rfl⟩ : syracuseStep 174261131 = 261391697) B261391697
theorem B116174087 : Blo 1959435 116174087 := bstep (se 1 (by rfl) ⟨87130565, by rfl⟩ : syracuseStep 116174087 = 174261131) B174261131
theorem B77449391 : Blo 1959435 77449391 := bstep (se 1 (by rfl) ⟨58087043, by rfl⟩ : syracuseStep 77449391 = 116174087) B116174087
theorem B51632927 : Blo 1959435 51632927 := bstep (se 1 (by rfl) ⟨38724695, by rfl⟩ : syracuseStep 51632927 = 77449391) B77449391
theorem B34421951 : Blo 1959435 34421951 := bstep (se 1 (by rfl) ⟨25816463, by rfl⟩ : syracuseStep 34421951 = 51632927) B51632927
theorem B22947967 : Blo 1959435 22947967 := bstep (se 1 (by rfl) ⟨17210975, by rfl⟩ : syracuseStep 22947967 = 34421951) B34421951
theorem B122389157 : Blo 1959435 122389157 := bstep (se 4 (by rfl) ⟨11473983, by rfl⟩ : syracuseStep 122389157 = 22947967) B22947967
theorem B81592771 : Blo 1959435 81592771 := bstep (se 1 (by rfl) ⟨61194578, by rfl⟩ : syracuseStep 81592771 = 122389157) B122389157
theorem B108790361 : Blo 1959435 108790361 := bstep (se 2 (by rfl) ⟨40796385, by rfl⟩ : syracuseStep 108790361 = 81592771) B81592771
theorem B72526907 : Blo 1959435 72526907 := bstep (se 1 (by rfl) ⟨54395180, by rfl⟩ : syracuseStep 72526907 = 108790361) B108790361
theorem B48351271 : Blo 1959435 48351271 := bstep (se 1 (by rfl) ⟨36263453, by rfl⟩ : syracuseStep 48351271 = 72526907) B72526907
theorem B64468361 : Blo 1959435 64468361 := bstep (se 2 (by rfl) ⟨24175635, by rfl⟩ : syracuseStep 64468361 = 48351271) B48351271
theorem B42978907 : Blo 1959435 42978907 := bstep (se 1 (by rfl) ⟨32234180, by rfl⟩ : syracuseStep 42978907 = 64468361) B64468361
theorem B229220837 : Blo 1959435 229220837 := bstep (se 4 (by rfl) ⟨21489453, by rfl⟩ : syracuseStep 229220837 = 42978907) B42978907
theorem B152813891 : Blo 1959435 152813891 := bstep (se 1 (by rfl) ⟨114610418, by rfl⟩ : syracuseStep 152813891 = 229220837) B229220837
theorem B101875927 : Blo 1959435 101875927 := bstep (se 1 (by rfl) ⟨76406945, by rfl⟩ : syracuseStep 101875927 = 152813891) B152813891
theorem B135834569 : Blo 1959435 135834569 := bstep (se 2 (by rfl) ⟨50937963, by rfl⟩ : syracuseStep 135834569 = 101875927) B101875927
theorem B90556379 : Blo 1959435 90556379 := bstep (se 1 (by rfl) ⟨67917284, by rfl⟩ : syracuseStep 90556379 = 135834569) B135834569
theorem B60370919 : Blo 1959435 60370919 := bstep (se 1 (by rfl) ⟨45278189, by rfl⟩ : syracuseStep 60370919 = 90556379) B90556379
theorem B40247279 : Blo 1959435 40247279 := bstep (se 1 (by rfl) ⟨30185459, by rfl⟩ : syracuseStep 40247279 = 60370919) B60370919
theorem B26831519 : Blo 1959435 26831519 := bstep (se 1 (by rfl) ⟨20123639, by rfl⟩ : syracuseStep 26831519 = 40247279) B40247279
theorem B17887679 : Blo 1959435 17887679 := bstep (se 1 (by rfl) ⟨13415759, by rfl⟩ : syracuseStep 17887679 = 26831519) B26831519
theorem B11925119 : Blo 1959435 11925119 := bstep (se 1 (by rfl) ⟨8943839, by rfl⟩ : syracuseStep 11925119 = 17887679) B17887679
theorem B7950079 : Blo 1959435 7950079 := bstep (se 1 (by rfl) ⟨5962559, by rfl⟩ : syracuseStep 7950079 = 11925119) B11925119
theorem B10600105 : Blo 1959435 10600105 := bstep (se 2 (by rfl) ⟨3975039, by rfl⟩ : syracuseStep 10600105 = 7950079) B7950079
theorem B14133473 : Blo 1959435 14133473 := bstep (se 2 (by rfl) ⟨5300052, by rfl⟩ : syracuseStep 14133473 = 10600105) B10600105
theorem B9422315 : Blo 1959435 9422315 := bstep (se 1 (by rfl) ⟨7066736, by rfl⟩ : syracuseStep 9422315 = 14133473) B14133473
theorem B6281543 : Blo 1959435 6281543 := bstep (se 1 (by rfl) ⟨4711157, by rfl⟩ : syracuseStep 6281543 = 9422315) B9422315
theorem B4187695 : Blo 1959435 4187695 := bstep (se 1 (by rfl) ⟨3140771, by rfl⟩ : syracuseStep 4187695 = 6281543) B6281543
theorem B5583593 : Blo 1959435 5583593 := bstep (se 2 (by rfl) ⟨2093847, by rfl⟩ : syracuseStep 5583593 = 4187695) B4187695
theorem B14889581 : Blo 1959435 14889581 := bstep (se 3 (by rfl) ⟨2791796, by rfl⟩ : syracuseStep 14889581 = 5583593) B5583593
theorem B9926387 : Blo 1959435 9926387 := bstep (se 1 (by rfl) ⟨7444790, by rfl⟩ : syracuseStep 9926387 = 14889581) B14889581
theorem B6617591 : Blo 1959435 6617591 := bstep (se 1 (by rfl) ⟨4963193, by rfl⟩ : syracuseStep 6617591 = 9926387) B9926387
theorem B4411727 : Blo 1959435 4411727 := bstep (se 1 (by rfl) ⟨3308795, by rfl⟩ : syracuseStep 4411727 = 6617591) B6617591
theorem B2941151 : Blo 1959435 2941151 := bstep (se 1 (by rfl) ⟨2205863, by rfl⟩ : syracuseStep 2941151 = 4411727) B4411727
theorem B1960767 : Blo 1959435 1960767 := bstep (se 1 (by rfl) ⟨1470575, by rfl⟩ : syracuseStep 1960767 = 2941151) B2941151
theorem B2941157 : Blo 1959435 2941157 := bbase (se 4 (by rfl) ⟨275733, by rfl⟩ : syracuseStep 2941157 = 551467) (by norm_num)
theorem B1960771 : Blo 1959435 1960771 := bstep (se 1 (by rfl) ⟨1470578, by rfl⟩ : syracuseStep 1960771 = 2941157) B2941157
theorem B2355589 : Blo 1959435 2355589 := bbase (se 4 (by rfl) ⟨220836, by rfl⟩ : syracuseStep 2355589 = 441673) (by norm_num)
theorem B3140785 : Blo 1959435 3140785 := bstep (se 2 (by rfl) ⟨1177794, by rfl⟩ : syracuseStep 3140785 = 2355589) B2355589
theorem B4187713 : Blo 1959435 4187713 := bstep (se 2 (by rfl) ⟨1570392, by rfl⟩ : syracuseStep 4187713 = 3140785) B3140785
theorem B5583617 : Blo 1959435 5583617 := bstep (se 2 (by rfl) ⟨2093856, by rfl⟩ : syracuseStep 5583617 = 4187713) B4187713
theorem B3722411 : Blo 1959435 3722411 := bstep (se 1 (by rfl) ⟨2791808, by rfl⟩ : syracuseStep 3722411 = 5583617) B5583617
theorem B2481607 : Blo 1959435 2481607 := bstep (se 1 (by rfl) ⟨1861205, by rfl⟩ : syracuseStep 2481607 = 3722411) B3722411
theorem B3308809 : Blo 1959435 3308809 := bstep (se 2 (by rfl) ⟨1240803, by rfl⟩ : syracuseStep 3308809 = 2481607) B2481607
theorem B4411745 : Blo 1959435 4411745 := bstep (se 2 (by rfl) ⟨1654404, by rfl⟩ : syracuseStep 4411745 = 3308809) B3308809
theorem B2941163 : Blo 1959435 2941163 := bstep (se 1 (by rfl) ⟨2205872, by rfl⟩ : syracuseStep 2941163 = 4411745) B4411745
theorem B1960775 : Blo 1959435 1960775 := bstep (se 1 (by rfl) ⟨1470581, by rfl⟩ : syracuseStep 1960775 = 2941163) B2941163
theorem B2205877 : Blo 1959435 2205877 := bbase (se 5 (by rfl) ⟨103400, by rfl⟩ : syracuseStep 2205877 = 206801) (by norm_num)
theorem B2941169 : Blo 1959435 2941169 := bstep (se 2 (by rfl) ⟨1102938, by rfl⟩ : syracuseStep 2941169 = 2205877) B2205877
theorem B1960779 : Blo 1959435 1960779 := bstep (se 1 (by rfl) ⟨1470584, by rfl⟩ : syracuseStep 1960779 = 2941169) B2941169
theorem B2481617 : Blo 1959435 2481617 := bbase (se 2 (by rfl) ⟨930606, by rfl⟩ : syracuseStep 2481617 = 1861213) (by norm_num)
theorem B6617645 : Blo 1959435 6617645 := bstep (se 3 (by rfl) ⟨1240808, by rfl⟩ : syracuseStep 6617645 = 2481617) B2481617
theorem B4411763 : Blo 1959435 4411763 := bstep (se 1 (by rfl) ⟨3308822, by rfl⟩ : syracuseStep 4411763 = 6617645) B6617645
theorem B2941175 : Blo 1959435 2941175 := bstep (se 1 (by rfl) ⟨2205881, by rfl⟩ : syracuseStep 2941175 = 4411763) B4411763
theorem B1960783 : Blo 1959435 1960783 := bstep (se 1 (by rfl) ⟨1470587, by rfl⟩ : syracuseStep 1960783 = 2941175) B2941175
theorem B2941181 : Blo 1959435 2941181 := bbase (se 3 (by rfl) ⟨551471, by rfl⟩ : syracuseStep 2941181 = 1102943) (by norm_num)
theorem B1960787 : Blo 1959435 1960787 := bstep (se 1 (by rfl) ⟨1470590, by rfl⟩ : syracuseStep 1960787 = 2941181) B2941181
theorem B4411781 : Blo 1959435 4411781 := bbase (se 4 (by rfl) ⟨413604, by rfl⟩ : syracuseStep 4411781 = 827209) (by norm_num)
theorem B2941187 : Blo 1959435 2941187 := bstep (se 1 (by rfl) ⟨2205890, by rfl⟩ : syracuseStep 2941187 = 4411781) B4411781
theorem B1960791 : Blo 1959435 1960791 := bstep (se 1 (by rfl) ⟨1470593, by rfl⟩ : syracuseStep 1960791 = 2941187) B2941187
theorem B2791837 : Blo 1959435 2791837 := bbase (se 3 (by rfl) ⟨523469, by rfl⟩ : syracuseStep 2791837 = 1046939) (by norm_num)
theorem B3722449 : Blo 1959435 3722449 := bstep (se 2 (by rfl) ⟨1395918, by rfl⟩ : syracuseStep 3722449 = 2791837) B2791837
theorem B4963265 : Blo 1959435 4963265 := bstep (se 2 (by rfl) ⟨1861224, by rfl⟩ : syracuseStep 4963265 = 3722449) B3722449
theorem B3308843 : Blo 1959435 3308843 := bstep (se 1 (by rfl) ⟨2481632, by rfl⟩ : syracuseStep 3308843 = 4963265) B4963265
theorem B2205895 : Blo 1959435 2205895 := bstep (se 1 (by rfl) ⟨1654421, by rfl⟩ : syracuseStep 2205895 = 3308843) B3308843
theorem B2941193 : Blo 1959435 2941193 := bstep (se 2 (by rfl) ⟨1102947, by rfl⟩ : syracuseStep 2941193 = 2205895) B2205895
theorem B1960795 : Blo 1959435 1960795 := bstep (se 1 (by rfl) ⟨1470596, by rfl⟩ : syracuseStep 1960795 = 2941193) B2941193
theorem B9926549 : Blo 1959435 9926549 := bbase (se 6 (by rfl) ⟨232653, by rfl⟩ : syracuseStep 9926549 = 465307) (by norm_num)
theorem B6617699 : Blo 1959435 6617699 := bstep (se 1 (by rfl) ⟨4963274, by rfl⟩ : syracuseStep 6617699 = 9926549) B9926549
theorem B4411799 : Blo 1959435 4411799 := bstep (se 1 (by rfl) ⟨3308849, by rfl⟩ : syracuseStep 4411799 = 6617699) B6617699
theorem B2941199 : Blo 1959435 2941199 := bstep (se 1 (by rfl) ⟨2205899, by rfl⟩ : syracuseStep 2941199 = 4411799) B4411799
theorem B1960799 : Blo 1959435 1960799 := bstep (se 1 (by rfl) ⟨1470599, by rfl⟩ : syracuseStep 1960799 = 2941199) B2941199
theorem B2941205 : Blo 1959435 2941205 := bbase (se 6 (by rfl) ⟨68934, by rfl⟩ : syracuseStep 2941205 = 137869) (by norm_num)
theorem B1960803 : Blo 1959435 1960803 := bstep (se 1 (by rfl) ⟨1470602, by rfl⟩ : syracuseStep 1960803 = 2941205) B2941205
theorem B5031013 : Blo 1959435 5031013 := bbase (se 4 (by rfl) ⟨471657, by rfl⟩ : syracuseStep 5031013 = 943315) (by norm_num)
theorem B6708017 : Blo 1959435 6708017 := bstep (se 2 (by rfl) ⟨2515506, by rfl⟩ : syracuseStep 6708017 = 5031013) B5031013
theorem B4472011 : Blo 1959435 4472011 := bstep (se 1 (by rfl) ⟨3354008, by rfl⟩ : syracuseStep 4472011 = 6708017) B6708017
theorem B5962681 : Blo 1959435 5962681 := bstep (se 2 (by rfl) ⟨2236005, by rfl⟩ : syracuseStep 5962681 = 4472011) B4472011
theorem B7950241 : Blo 1959435 7950241 := bstep (se 2 (by rfl) ⟨2981340, by rfl⟩ : syracuseStep 7950241 = 5962681) B5962681
theorem B10600321 : Blo 1959435 10600321 := bstep (se 2 (by rfl) ⟨3975120, by rfl⟩ : syracuseStep 10600321 = 7950241) B7950241
theorem B14133761 : Blo 1959435 14133761 := bstep (se 2 (by rfl) ⟨5300160, by rfl⟩ : syracuseStep 14133761 = 10600321) B10600321
theorem B9422507 : Blo 1959435 9422507 := bstep (se 1 (by rfl) ⟨7066880, by rfl⟩ : syracuseStep 9422507 = 14133761) B14133761
theorem B25126685 : Blo 1959435 25126685 := bstep (se 3 (by rfl) ⟨4711253, by rfl⟩ : syracuseStep 25126685 = 9422507) B9422507
theorem B16751123 : Blo 1959435 16751123 := bstep (se 1 (by rfl) ⟨12563342, by rfl⟩ : syracuseStep 16751123 = 25126685) B25126685
theorem B11167415 : Blo 1959435 11167415 := bstep (se 1 (by rfl) ⟨8375561, by rfl⟩ : syracuseStep 11167415 = 16751123) B16751123
theorem B7444943 : Blo 1959435 7444943 := bstep (se 1 (by rfl) ⟨5583707, by rfl⟩ : syracuseStep 7444943 = 11167415) B11167415
theorem B4963295 : Blo 1959435 4963295 := bstep (se 1 (by rfl) ⟨3722471, by rfl⟩ : syracuseStep 4963295 = 7444943) B7444943
theorem B3308863 : Blo 1959435 3308863 := bstep (se 1 (by rfl) ⟨2481647, by rfl⟩ : syracuseStep 3308863 = 4963295) B4963295
theorem B4411817 : Blo 1959435 4411817 := bstep (se 2 (by rfl) ⟨1654431, by rfl⟩ : syracuseStep 4411817 = 3308863) B3308863
theorem B2941211 : Blo 1959435 2941211 := bstep (se 1 (by rfl) ⟨2205908, by rfl⟩ : syracuseStep 2941211 = 4411817) B4411817
theorem B1960807 : Blo 1959435 1960807 := bstep (se 1 (by rfl) ⟨1470605, by rfl⟩ : syracuseStep 1960807 = 2941211) B2941211
theorem B2205913 : Blo 1959435 2205913 := bbase (se 2 (by rfl) ⟨827217, by rfl⟩ : syracuseStep 2205913 = 1654435) (by norm_num)
theorem B2941217 : Blo 1959435 2941217 := bstep (se 2 (by rfl) ⟨1102956, by rfl⟩ : syracuseStep 2941217 = 2205913) B2205913
theorem B1960811 : Blo 1959435 1960811 := bstep (se 1 (by rfl) ⟨1470608, by rfl⟩ : syracuseStep 1960811 = 2941217) B2941217
theorem B2355637 : Blo 1959435 2355637 := bbase (se 5 (by rfl) ⟨110420, by rfl⟩ : syracuseStep 2355637 = 220841) (by norm_num)
theorem B3140849 : Blo 1959435 3140849 := bstep (se 2 (by rfl) ⟨1177818, by rfl⟩ : syracuseStep 3140849 = 2355637) B2355637
theorem B2093899 : Blo 1959435 2093899 := bstep (se 1 (by rfl) ⟨1570424, by rfl⟩ : syracuseStep 2093899 = 3140849) B3140849
theorem B2791865 : Blo 1959435 2791865 := bstep (se 2 (by rfl) ⟨1046949, by rfl⟩ : syracuseStep 2791865 = 2093899) B2093899
theorem B7444973 : Blo 1959435 7444973 := bstep (se 3 (by rfl) ⟨1395932, by rfl⟩ : syracuseStep 7444973 = 2791865) B2791865
theorem B4963315 : Blo 1959435 4963315 := bstep (se 1 (by rfl) ⟨3722486, by rfl⟩ : syracuseStep 4963315 = 7444973) B7444973
theorem B6617753 : Blo 1959435 6617753 := bstep (se 2 (by rfl) ⟨2481657, by rfl⟩ : syracuseStep 6617753 = 4963315) B4963315
theorem B4411835 : Blo 1959435 4411835 := bstep (se 1 (by rfl) ⟨3308876, by rfl⟩ : syracuseStep 4411835 = 6617753) B6617753
theorem B2941223 : Blo 1959435 2941223 := bstep (se 1 (by rfl) ⟨2205917, by rfl⟩ : syracuseStep 2941223 = 4411835) B4411835
theorem B1960815 : Blo 1959435 1960815 := bstep (se 1 (by rfl) ⟨1470611, by rfl⟩ : syracuseStep 1960815 = 2941223) B2941223
theorem B2941229 : Blo 1959435 2941229 := bbase (se 3 (by rfl) ⟨551480, by rfl⟩ : syracuseStep 2941229 = 1102961) (by norm_num)
theorem B1960819 : Blo 1959435 1960819 := bstep (se 1 (by rfl) ⟨1470614, by rfl⟩ : syracuseStep 1960819 = 2941229) B2941229
theorem B4411853 : Blo 1959435 4411853 := bbase (se 3 (by rfl) ⟨827222, by rfl⟩ : syracuseStep 4411853 = 1654445) (by norm_num)
theorem B2941235 : Blo 1959435 2941235 := bstep (se 1 (by rfl) ⟨2205926, by rfl⟩ : syracuseStep 2941235 = 4411853) B4411853
theorem B1960823 : Blo 1959435 1960823 := bstep (se 1 (by rfl) ⟨1470617, by rfl⟩ : syracuseStep 1960823 = 2941235) B2941235
theorem B2481673 : Blo 1959435 2481673 := bbase (se 2 (by rfl) ⟨930627, by rfl⟩ : syracuseStep 2481673 = 1861255) (by norm_num)
theorem B3308897 : Blo 1959435 3308897 := bstep (se 2 (by rfl) ⟨1240836, by rfl⟩ : syracuseStep 3308897 = 2481673) B2481673
theorem B2205931 : Blo 1959435 2205931 := bstep (se 1 (by rfl) ⟨1654448, by rfl⟩ : syracuseStep 2205931 = 3308897) B3308897
theorem B2941241 : Blo 1959435 2941241 := bstep (se 2 (by rfl) ⟨1102965, by rfl⟩ : syracuseStep 2941241 = 2205931) B2205931
theorem B1960827 : Blo 1959435 1960827 := bstep (se 1 (by rfl) ⟨1470620, by rfl⟩ : syracuseStep 1960827 = 2941241) B2941241
theorem B2515537 : Blo 1959435 2515537 := bbase (se 2 (by rfl) ⟨943326, by rfl⟩ : syracuseStep 2515537 = 1886653) (by norm_num)
theorem B3354049 : Blo 1959435 3354049 := bstep (se 2 (by rfl) ⟨1257768, by rfl⟩ : syracuseStep 3354049 = 2515537) B2515537
theorem B4472065 : Blo 1959435 4472065 := bstep (se 2 (by rfl) ⟨1677024, by rfl⟩ : syracuseStep 4472065 = 3354049) B3354049
theorem B5962753 : Blo 1959435 5962753 := bstep (se 2 (by rfl) ⟨2236032, by rfl⟩ : syracuseStep 5962753 = 4472065) B4472065
theorem B31801349 : Blo 1959435 31801349 := bstep (se 4 (by rfl) ⟨2981376, by rfl⟩ : syracuseStep 31801349 = 5962753) B5962753
theorem B21200899 : Blo 1959435 21200899 := bstep (se 1 (by rfl) ⟨15900674, by rfl⟩ : syracuseStep 21200899 = 31801349) B31801349
theorem B28267865 : Blo 1959435 28267865 := bstep (se 2 (by rfl) ⟨10600449, by rfl⟩ : syracuseStep 28267865 = 21200899) B21200899
theorem B18845243 : Blo 1959435 18845243 := bstep (se 1 (by rfl) ⟨14133932, by rfl⟩ : syracuseStep 18845243 = 28267865) B28267865
theorem B12563495 : Blo 1959435 12563495 := bstep (se 1 (by rfl) ⟨9422621, by rfl⟩ : syracuseStep 12563495 = 18845243) B18845243
theorem B8375663 : Blo 1959435 8375663 := bstep (se 1 (by rfl) ⟨6281747, by rfl⟩ : syracuseStep 8375663 = 12563495) B12563495
theorem B22335101 : Blo 1959435 22335101 := bstep (se 3 (by rfl) ⟨4187831, by rfl⟩ : syracuseStep 22335101 = 8375663) B8375663
theorem B14890067 : Blo 1959435 14890067 := bstep (se 1 (by rfl) ⟨11167550, by rfl⟩ : syracuseStep 14890067 = 22335101) B22335101
theorem B9926711 : Blo 1959435 9926711 := bstep (se 1 (by rfl) ⟨7445033, by rfl⟩ : syracuseStep 9926711 = 14890067) B14890067
theorem B6617807 : Blo 1959435 6617807 := bstep (se 1 (by rfl) ⟨4963355, by rfl⟩ : syracuseStep 6617807 = 9926711) B9926711
theorem B4411871 : Blo 1959435 4411871 := bstep (se 1 (by rfl) ⟨3308903, by rfl⟩ : syracuseStep 4411871 = 6617807) B6617807
theorem B2941247 : Blo 1959435 2941247 := bstep (se 1 (by rfl) ⟨2205935, by rfl⟩ : syracuseStep 2941247 = 4411871) B4411871
theorem B1960831 : Blo 1959435 1960831 := bstep (se 1 (by rfl) ⟨1470623, by rfl⟩ : syracuseStep 1960831 = 2941247) B2941247
theorem B2941253 : Blo 1959435 2941253 := bbase (se 4 (by rfl) ⟨275742, by rfl⟩ : syracuseStep 2941253 = 551485) (by norm_num)
theorem B1960835 : Blo 1959435 1960835 := bstep (se 1 (by rfl) ⟨1470626, by rfl⟩ : syracuseStep 1960835 = 2941253) B2941253
theorem B3308917 : Blo 1959435 3308917 := bbase (se 5 (by rfl) ⟨155105, by rfl⟩ : syracuseStep 3308917 = 310211) (by norm_num)
theorem B4411889 : Blo 1959435 4411889 := bstep (se 2 (by rfl) ⟨1654458, by rfl⟩ : syracuseStep 4411889 = 3308917) B3308917
theorem B2941259 : Blo 1959435 2941259 := bstep (se 1 (by rfl) ⟨2205944, by rfl⟩ : syracuseStep 2941259 = 4411889) B4411889
theorem B1960839 : Blo 1959435 1960839 := bstep (se 1 (by rfl) ⟨1470629, by rfl⟩ : syracuseStep 1960839 = 2941259) B2941259
theorem B2205949 : Blo 1959435 2205949 := bbase (se 3 (by rfl) ⟨413615, by rfl⟩ : syracuseStep 2205949 = 827231) (by norm_num)
theorem B2941265 : Blo 1959435 2941265 := bstep (se 2 (by rfl) ⟨1102974, by rfl⟩ : syracuseStep 2941265 = 2205949) B2205949
theorem B1960843 : Blo 1959435 1960843 := bstep (se 1 (by rfl) ⟨1470632, by rfl⟩ : syracuseStep 1960843 = 2941265) B2941265
theorem B6617861 : Blo 1959435 6617861 := bbase (se 4 (by rfl) ⟨620424, by rfl⟩ : syracuseStep 6617861 = 1240849) (by norm_num)
theorem B4411907 : Blo 1959435 4411907 := bstep (se 1 (by rfl) ⟨3308930, by rfl⟩ : syracuseStep 4411907 = 6617861) B6617861
theorem B2941271 : Blo 1959435 2941271 := bstep (se 1 (by rfl) ⟨2205953, by rfl⟩ : syracuseStep 2941271 = 4411907) B4411907
theorem B1960847 : Blo 1959435 1960847 := bstep (se 1 (by rfl) ⟨1470635, by rfl⟩ : syracuseStep 1960847 = 2941271) B2941271
theorem B2941277 : Blo 1959435 2941277 := bbase (se 3 (by rfl) ⟨551489, by rfl⟩ : syracuseStep 2941277 = 1102979) (by norm_num)
theorem B1960851 : Blo 1959435 1960851 := bstep (se 1 (by rfl) ⟨1470638, by rfl⟩ : syracuseStep 1960851 = 2941277) B2941277
theorem B4411925 : Blo 1959435 4411925 := bbase (se 6 (by rfl) ⟨103404, by rfl⟩ : syracuseStep 4411925 = 206809) (by norm_num)
theorem B2941283 : Blo 1959435 2941283 := bstep (se 1 (by rfl) ⟨2205962, by rfl⟩ : syracuseStep 2941283 = 4411925) B4411925
theorem B1960855 : Blo 1959435 1960855 := bstep (se 1 (by rfl) ⟨1470641, by rfl⟩ : syracuseStep 1960855 = 2941283) B2941283
theorem B7445141 : Blo 1959435 7445141 := bbase (se 6 (by rfl) ⟨174495, by rfl⟩ : syracuseStep 7445141 = 348991) (by norm_num)
theorem B4963427 : Blo 1959435 4963427 := bstep (se 1 (by rfl) ⟨3722570, by rfl⟩ : syracuseStep 4963427 = 7445141) B7445141
theorem B3308951 : Blo 1959435 3308951 := bstep (se 1 (by rfl) ⟨2481713, by rfl⟩ : syracuseStep 3308951 = 4963427) B4963427
theorem B2205967 : Blo 1959435 2205967 := bstep (se 1 (by rfl) ⟨1654475, by rfl⟩ : syracuseStep 2205967 = 3308951) B3308951
theorem B2941289 : Blo 1959435 2941289 := bstep (se 2 (by rfl) ⟨1102983, by rfl⟩ : syracuseStep 2941289 = 2205967) B2205967
theorem B1960859 : Blo 1959435 1960859 := bstep (se 1 (by rfl) ⟨1470644, by rfl⟩ : syracuseStep 1960859 = 2941289) B2941289
theorem B11167733 : Blo 1959435 11167733 := bbase (se 5 (by rfl) ⟨523487, by rfl⟩ : syracuseStep 11167733 = 1046975) (by norm_num)
theorem B7445155 : Blo 1959435 7445155 := bstep (se 1 (by rfl) ⟨5583866, by rfl⟩ : syracuseStep 7445155 = 11167733) B11167733
theorem B9926873 : Blo 1959435 9926873 := bstep (se 2 (by rfl) ⟨3722577, by rfl⟩ : syracuseStep 9926873 = 7445155) B7445155
theorem B6617915 : Blo 1959435 6617915 := bstep (se 1 (by rfl) ⟨4963436, by rfl⟩ : syracuseStep 6617915 = 9926873) B9926873
theorem B4411943 : Blo 1959435 4411943 := bstep (se 1 (by rfl) ⟨3308957, by rfl⟩ : syracuseStep 4411943 = 6617915) B6617915
theorem B2941295 : Blo 1959435 2941295 := bstep (se 1 (by rfl) ⟨2205971, by rfl⟩ : syracuseStep 2941295 = 4411943) B4411943
theorem B1960863 : Blo 1959435 1960863 := bstep (se 1 (by rfl) ⟨1470647, by rfl⟩ : syracuseStep 1960863 = 2941295) B2941295
theorem B2941301 : Blo 1959435 2941301 := bbase (se 5 (by rfl) ⟨137873, by rfl⟩ : syracuseStep 2941301 = 275747) (by norm_num)
theorem B1960867 : Blo 1959435 1960867 := bstep (se 1 (by rfl) ⟨1470650, by rfl⟩ : syracuseStep 1960867 = 2941301) B2941301
theorem B3533557 : Blo 1959435 3533557 := bbase (se 5 (by rfl) ⟨165635, by rfl⟩ : syracuseStep 3533557 = 331271) (by norm_num)
theorem B4711409 : Blo 1959435 4711409 := bstep (se 2 (by rfl) ⟨1766778, by rfl⟩ : syracuseStep 4711409 = 3533557) B3533557
theorem B3140939 : Blo 1959435 3140939 := bstep (se 1 (by rfl) ⟨2355704, by rfl⟩ : syracuseStep 3140939 = 4711409) B4711409
theorem B2093959 : Blo 1959435 2093959 := bstep (se 1 (by rfl) ⟨1570469, by rfl⟩ : syracuseStep 2093959 = 3140939) B3140939
theorem B2791945 : Blo 1959435 2791945 := bstep (se 2 (by rfl) ⟨1046979, by rfl⟩ : syracuseStep 2791945 = 2093959) B2093959
theorem B3722593 : Blo 1959435 3722593 := bstep (se 2 (by rfl) ⟨1395972, by rfl⟩ : syracuseStep 3722593 = 2791945) B2791945
theorem B4963457 : Blo 1959435 4963457 := bstep (se 2 (by rfl) ⟨1861296, by rfl⟩ : syracuseStep 4963457 = 3722593) B3722593
theorem B3308971 : Blo 1959435 3308971 := bstep (se 1 (by rfl) ⟨2481728, by rfl⟩ : syracuseStep 3308971 = 4963457) B4963457
theorem B4411961 : Blo 1959435 4411961 := bstep (se 2 (by rfl) ⟨1654485, by rfl⟩ : syracuseStep 4411961 = 3308971) B3308971
theorem B2941307 : Blo 1959435 2941307 := bstep (se 1 (by rfl) ⟨2205980, by rfl⟩ : syracuseStep 2941307 = 4411961) B4411961
theorem B1960871 : Blo 1959435 1960871 := bstep (se 1 (by rfl) ⟨1470653, by rfl⟩ : syracuseStep 1960871 = 2941307) B2941307
theorem B2205985 : Blo 1959435 2205985 := bbase (se 2 (by rfl) ⟨827244, by rfl⟩ : syracuseStep 2205985 = 1654489) (by norm_num)
theorem B2941313 : Blo 1959435 2941313 := bstep (se 2 (by rfl) ⟨1102992, by rfl⟩ : syracuseStep 2941313 = 2205985) B2205985
theorem B1960875 : Blo 1959435 1960875 := bstep (se 1 (by rfl) ⟨1470656, by rfl⟩ : syracuseStep 1960875 = 2941313) B2941313
theorem B4963477 : Blo 1959435 4963477 := bbase (se 6 (by rfl) ⟨116331, by rfl⟩ : syracuseStep 4963477 = 232663) (by norm_num)
theorem B6617969 : Blo 1959435 6617969 := bstep (se 2 (by rfl) ⟨2481738, by rfl⟩ : syracuseStep 6617969 = 4963477) B4963477
theorem B4411979 : Blo 1959435 4411979 := bstep (se 1 (by rfl) ⟨3308984, by rfl⟩ : syracuseStep 4411979 = 6617969) B6617969
theorem B2941319 : Blo 1959435 2941319 := bstep (se 1 (by rfl) ⟨2205989, by rfl⟩ : syracuseStep 2941319 = 4411979) B4411979
theorem B1960879 : Blo 1959435 1960879 := bstep (se 1 (by rfl) ⟨1470659, by rfl⟩ : syracuseStep 1960879 = 2941319) B2941319
theorem B2941325 : Blo 1959435 2941325 := bbase (se 3 (by rfl) ⟨551498, by rfl⟩ : syracuseStep 2941325 = 1102997) (by norm_num)
theorem B1960883 : Blo 1959435 1960883 := bstep (se 1 (by rfl) ⟨1470662, by rfl⟩ : syracuseStep 1960883 = 2941325) B2941325
theorem B4411997 : Blo 1959435 4411997 := bbase (se 3 (by rfl) ⟨827249, by rfl⟩ : syracuseStep 4411997 = 1654499) (by norm_num)
theorem B2941331 : Blo 1959435 2941331 := bstep (se 1 (by rfl) ⟨2205998, by rfl⟩ : syracuseStep 2941331 = 4411997) B4411997
theorem B1960887 : Blo 1959435 1960887 := bstep (se 1 (by rfl) ⟨1470665, by rfl⟩ : syracuseStep 1960887 = 2941331) B2941331
theorem B3309005 : Blo 1959435 3309005 := bbase (se 3 (by rfl) ⟨620438, by rfl⟩ : syracuseStep 3309005 = 1240877) (by norm_num)
theorem B2206003 : Blo 1959435 2206003 := bstep (se 1 (by rfl) ⟨1654502, by rfl⟩ : syracuseStep 2206003 = 3309005) B3309005
theorem B2941337 : Blo 1959435 2941337 := bstep (se 2 (by rfl) ⟨1103001, by rfl⟩ : syracuseStep 2941337 = 2206003) B2206003
theorem B1960891 : Blo 1959435 1960891 := bstep (se 1 (by rfl) ⟨1470668, by rfl⟩ : syracuseStep 1960891 = 2941337) B2941337
theorem B5962949 : Blo 1959435 5962949 := bbase (se 4 (by rfl) ⟨559026, by rfl⟩ : syracuseStep 5962949 = 1118053) (by norm_num)
theorem B3975299 : Blo 1959435 3975299 := bstep (se 1 (by rfl) ⟨2981474, by rfl⟩ : syracuseStep 3975299 = 5962949) B5962949
theorem B2650199 : Blo 1959435 2650199 := bstep (se 1 (by rfl) ⟨1987649, by rfl⟩ : syracuseStep 2650199 = 3975299) B3975299
theorem B7067197 : Blo 1959435 7067197 := bstep (se 3 (by rfl) ⟨1325099, by rfl⟩ : syracuseStep 7067197 = 2650199) B2650199
theorem B9422929 : Blo 1959435 9422929 := bstep (se 2 (by rfl) ⟨3533598, by rfl⟩ : syracuseStep 9422929 = 7067197) B7067197
theorem B12563905 : Blo 1959435 12563905 := bstep (se 2 (by rfl) ⟨4711464, by rfl⟩ : syracuseStep 12563905 = 9422929) B9422929
theorem B16751873 : Blo 1959435 16751873 := bstep (se 2 (by rfl) ⟨6281952, by rfl⟩ : syracuseStep 16751873 = 12563905) B12563905
theorem B11167915 : Blo 1959435 11167915 := bstep (se 1 (by rfl) ⟨8375936, by rfl⟩ : syracuseStep 11167915 = 16751873) B16751873
theorem B14890553 : Blo 1959435 14890553 := bstep (se 2 (by rfl) ⟨5583957, by rfl⟩ : syracuseStep 14890553 = 11167915) B11167915
theorem B9927035 : Blo 1959435 9927035 := bstep (se 1 (by rfl) ⟨7445276, by rfl⟩ : syracuseStep 9927035 = 14890553) B14890553
theorem B6618023 : Blo 1959435 6618023 := bstep (se 1 (by rfl) ⟨4963517, by rfl⟩ : syracuseStep 6618023 = 9927035) B9927035
theorem B4412015 : Blo 1959435 4412015 := bstep (se 1 (by rfl) ⟨3309011, by rfl⟩ : syracuseStep 4412015 = 6618023) B6618023
theorem B2941343 : Blo 1959435 2941343 := bstep (se 1 (by rfl) ⟨2206007, by rfl⟩ : syracuseStep 2941343 = 4412015) B4412015
theorem B1960895 : Blo 1959435 1960895 := bstep (se 1 (by rfl) ⟨1470671, by rfl⟩ : syracuseStep 1960895 = 2941343) B2941343
theorem B2941349 : Blo 1959435 2941349 := bbase (se 4 (by rfl) ⟨275751, by rfl⟩ : syracuseStep 2941349 = 551503) (by norm_num)
theorem B1960899 : Blo 1959435 1960899 := bstep (se 1 (by rfl) ⟨1470674, by rfl⟩ : syracuseStep 1960899 = 2941349) B2941349
theorem B2481769 : Blo 1959435 2481769 := bbase (se 2 (by rfl) ⟨930663, by rfl⟩ : syracuseStep 2481769 = 1861327) (by norm_num)
theorem B3309025 : Blo 1959435 3309025 := bstep (se 2 (by rfl) ⟨1240884, by rfl⟩ : syracuseStep 3309025 = 2481769) B2481769
theorem B4412033 : Blo 1959435 4412033 := bstep (se 2 (by rfl) ⟨1654512, by rfl⟩ : syracuseStep 4412033 = 3309025) B3309025
theorem B2941355 : Blo 1959435 2941355 := bstep (se 1 (by rfl) ⟨2206016, by rfl⟩ : syracuseStep 2941355 = 4412033) B4412033
theorem B1960903 : Blo 1959435 1960903 := bstep (se 1 (by rfl) ⟨1470677, by rfl⟩ : syracuseStep 1960903 = 2941355) B2941355
theorem B2206021 : Blo 1959435 2206021 := bbase (se 4 (by rfl) ⟨206814, by rfl⟩ : syracuseStep 2206021 = 413629) (by norm_num)
theorem B2941361 : Blo 1959435 2941361 := bstep (se 2 (by rfl) ⟨1103010, by rfl⟩ : syracuseStep 2941361 = 2206021) B2206021
theorem B1960907 : Blo 1959435 1960907 := bstep (se 1 (by rfl) ⟨1470680, by rfl⟩ : syracuseStep 1960907 = 2941361) B2941361
theorem B3722669 : Blo 1959435 3722669 := bbase (se 3 (by rfl) ⟨698000, by rfl⟩ : syracuseStep 3722669 = 1396001) (by norm_num)
theorem B2481779 : Blo 1959435 2481779 := bstep (se 1 (by rfl) ⟨1861334, by rfl⟩ : syracuseStep 2481779 = 3722669) B3722669
theorem B6618077 : Blo 1959435 6618077 := bstep (se 3 (by rfl) ⟨1240889, by rfl⟩ : syracuseStep 6618077 = 2481779) B2481779
theorem B4412051 : Blo 1959435 4412051 := bstep (se 1 (by rfl) ⟨3309038, by rfl⟩ : syracuseStep 4412051 = 6618077) B6618077
theorem B2941367 : Blo 1959435 2941367 := bstep (se 1 (by rfl) ⟨2206025, by rfl⟩ : syracuseStep 2941367 = 4412051) B4412051
theorem B1960911 : Blo 1959435 1960911 := bstep (se 1 (by rfl) ⟨1470683, by rfl⟩ : syracuseStep 1960911 = 2941367) B2941367
theorem B2941373 : Blo 1959435 2941373 := bbase (se 3 (by rfl) ⟨551507, by rfl⟩ : syracuseStep 2941373 = 1103015) (by norm_num)
theorem B1960915 : Blo 1959435 1960915 := bstep (se 1 (by rfl) ⟨1470686, by rfl⟩ : syracuseStep 1960915 = 2941373) B2941373
theorem B4412069 : Blo 1959435 4412069 := bbase (se 4 (by rfl) ⟨413631, by rfl⟩ : syracuseStep 4412069 = 827263) (by norm_num)
theorem B2941379 : Blo 1959435 2941379 := bstep (se 1 (by rfl) ⟨2206034, by rfl⟩ : syracuseStep 2941379 = 4412069) B4412069
theorem B1960919 : Blo 1959435 1960919 := bstep (se 1 (by rfl) ⟨1470689, by rfl⟩ : syracuseStep 1960919 = 2941379) B2941379
theorem B4963589 : Blo 1959435 4963589 := bbase (se 4 (by rfl) ⟨465336, by rfl⟩ : syracuseStep 4963589 = 930673) (by norm_num)
theorem B3309059 : Blo 1959435 3309059 := bstep (se 1 (by rfl) ⟨2481794, by rfl⟩ : syracuseStep 3309059 = 4963589) B4963589
theorem B2206039 : Blo 1959435 2206039 := bstep (se 1 (by rfl) ⟨1654529, by rfl⟩ : syracuseStep 2206039 = 3309059) B3309059
theorem B2941385 : Blo 1959435 2941385 := bstep (se 2 (by rfl) ⟨1103019, by rfl⟩ : syracuseStep 2941385 = 2206039) B2206039
theorem B1960923 : Blo 1959435 1960923 := bstep (se 1 (by rfl) ⟨1470692, by rfl⟩ : syracuseStep 1960923 = 2941385) B2941385
theorem B4188037 : Blo 1959435 4188037 := bbase (se 4 (by rfl) ⟨392628, by rfl⟩ : syracuseStep 4188037 = 785257) (by norm_num)
theorem B5584049 : Blo 1959435 5584049 := bstep (se 2 (by rfl) ⟨2094018, by rfl⟩ : syracuseStep 5584049 = 4188037) B4188037
theorem B3722699 : Blo 1959435 3722699 := bstep (se 1 (by rfl) ⟨2792024, by rfl⟩ : syracuseStep 3722699 = 5584049) B5584049
theorem B9927197 : Blo 1959435 9927197 := bstep (se 3 (by rfl) ⟨1861349, by rfl⟩ : syracuseStep 9927197 = 3722699) B3722699
theorem B6618131 : Blo 1959435 6618131 := bstep (se 1 (by rfl) ⟨4963598, by rfl⟩ : syracuseStep 6618131 = 9927197) B9927197
theorem B4412087 : Blo 1959435 4412087 := bstep (se 1 (by rfl) ⟨3309065, by rfl⟩ : syracuseStep 4412087 = 6618131) B6618131
theorem B2941391 : Blo 1959435 2941391 := bstep (se 1 (by rfl) ⟨2206043, by rfl⟩ : syracuseStep 2941391 = 4412087) B4412087
theorem B1960927 : Blo 1959435 1960927 := bstep (se 1 (by rfl) ⟨1470695, by rfl⟩ : syracuseStep 1960927 = 2941391) B2941391
theorem B2941397 : Blo 1959435 2941397 := bbase (se 7 (by rfl) ⟨34469, by rfl⟩ : syracuseStep 2941397 = 68939) (by norm_num)
theorem B1960931 : Blo 1959435 1960931 := bstep (se 1 (by rfl) ⟨1470698, by rfl⟩ : syracuseStep 1960931 = 2941397) B2941397
theorem B7445429 : Blo 1959435 7445429 := bbase (se 5 (by rfl) ⟨349004, by rfl⟩ : syracuseStep 7445429 = 698009) (by norm_num)
theorem B4963619 : Blo 1959435 4963619 := bstep (se 1 (by rfl) ⟨3722714, by rfl⟩ : syracuseStep 4963619 = 7445429) B7445429
theorem B3309079 : Blo 1959435 3309079 := bstep (se 1 (by rfl) ⟨2481809, by rfl⟩ : syracuseStep 3309079 = 4963619) B4963619
theorem B4412105 : Blo 1959435 4412105 := bstep (se 2 (by rfl) ⟨1654539, by rfl⟩ : syracuseStep 4412105 = 3309079) B3309079
theorem B2941403 : Blo 1959435 2941403 := bstep (se 1 (by rfl) ⟨2206052, by rfl⟩ : syracuseStep 2941403 = 4412105) B4412105
theorem B1960935 : Blo 1959435 1960935 := bstep (se 1 (by rfl) ⟨1470701, by rfl⟩ : syracuseStep 1960935 = 2941403) B2941403
theorem B2206057 : Blo 1959435 2206057 := bbase (se 2 (by rfl) ⟨827271, by rfl⟩ : syracuseStep 2206057 = 1654543) (by norm_num)
theorem B2941409 : Blo 1959435 2941409 := bstep (se 2 (by rfl) ⟨1103028, by rfl⟩ : syracuseStep 2941409 = 2206057) B2206057
theorem B1960939 : Blo 1959435 1960939 := bstep (se 1 (by rfl) ⟨1470704, by rfl⟩ : syracuseStep 1960939 = 2941409) B2941409
theorem B2515681 : Blo 1959435 2515681 := bbase (se 2 (by rfl) ⟨943380, by rfl⟩ : syracuseStep 2515681 = 1886761) (by norm_num)
theorem B13416965 : Blo 1959435 13416965 := bstep (se 4 (by rfl) ⟨1257840, by rfl⟩ : syracuseStep 13416965 = 2515681) B2515681
theorem B8944643 : Blo 1959435 8944643 := bstep (se 1 (by rfl) ⟨6708482, by rfl⟩ : syracuseStep 8944643 = 13416965) B13416965
theorem B5963095 : Blo 1959435 5963095 := bstep (se 1 (by rfl) ⟨4472321, by rfl⟩ : syracuseStep 5963095 = 8944643) B8944643
theorem B7950793 : Blo 1959435 7950793 := bstep (se 2 (by rfl) ⟨2981547, by rfl⟩ : syracuseStep 7950793 = 5963095) B5963095
theorem B10601057 : Blo 1959435 10601057 := bstep (se 2 (by rfl) ⟨3975396, by rfl⟩ : syracuseStep 10601057 = 7950793) B7950793
theorem B7067371 : Blo 1959435 7067371 := bstep (se 1 (by rfl) ⟨5300528, by rfl⟩ : syracuseStep 7067371 = 10601057) B10601057
theorem B9423161 : Blo 1959435 9423161 := bstep (se 2 (by rfl) ⟨3533685, by rfl⟩ : syracuseStep 9423161 = 7067371) B7067371
theorem B6282107 : Blo 1959435 6282107 := bstep (se 1 (by rfl) ⟨4711580, by rfl⟩ : syracuseStep 6282107 = 9423161) B9423161
theorem B4188071 : Blo 1959435 4188071 := bstep (se 1 (by rfl) ⟨3141053, by rfl⟩ : syracuseStep 4188071 = 6282107) B6282107
theorem B11168189 : Blo 1959435 11168189 := bstep (se 3 (by rfl) ⟨2094035, by rfl⟩ : syracuseStep 11168189 = 4188071) B4188071
theorem B7445459 : Blo 1959435 7445459 := bstep (se 1 (by rfl) ⟨5584094, by rfl⟩ : syracuseStep 7445459 = 11168189) B11168189
theorem B4963639 : Blo 1959435 4963639 := bstep (se 1 (by rfl) ⟨3722729, by rfl⟩ : syracuseStep 4963639 = 7445459) B7445459
theorem B6618185 : Blo 1959435 6618185 := bstep (se 2 (by rfl) ⟨2481819, by rfl⟩ : syracuseStep 6618185 = 4963639) B4963639
theorem B4412123 : Blo 1959435 4412123 := bstep (se 1 (by rfl) ⟨3309092, by rfl⟩ : syracuseStep 4412123 = 6618185) B6618185
theorem B2941415 : Blo 1959435 2941415 := bstep (se 1 (by rfl) ⟨2206061, by rfl⟩ : syracuseStep 2941415 = 4412123) B4412123
theorem B1960943 : Blo 1959435 1960943 := bstep (se 1 (by rfl) ⟨1470707, by rfl⟩ : syracuseStep 1960943 = 2941415) B2941415
theorem B2941421 : Blo 1959435 2941421 := bbase (se 3 (by rfl) ⟨551516, by rfl⟩ : syracuseStep 2941421 = 1103033) (by norm_num)
theorem B1960947 : Blo 1959435 1960947 := bstep (se 1 (by rfl) ⟨1470710, by rfl⟩ : syracuseStep 1960947 = 2941421) B2941421
theorem B4412141 : Blo 1959435 4412141 := bbase (se 3 (by rfl) ⟨827276, by rfl⟩ : syracuseStep 4412141 = 1654553) (by norm_num)
theorem B2941427 : Blo 1959435 2941427 := bstep (se 1 (by rfl) ⟨2206070, by rfl⟩ : syracuseStep 2941427 = 4412141) B4412141
theorem B1960951 : Blo 1959435 1960951 := bstep (se 1 (by rfl) ⟨1470713, by rfl⟩ : syracuseStep 1960951 = 2941427) B2941427
theorem B2094049 : Blo 1959435 2094049 := bbase (se 2 (by rfl) ⟨785268, by rfl⟩ : syracuseStep 2094049 = 1570537) (by norm_num)
theorem B2792065 : Blo 1959435 2792065 := bstep (se 2 (by rfl) ⟨1047024, by rfl⟩ : syracuseStep 2792065 = 2094049) B2094049
theorem B3722753 : Blo 1959435 3722753 := bstep (se 2 (by rfl) ⟨1396032, by rfl⟩ : syracuseStep 3722753 = 2792065) B2792065
theorem B2481835 : Blo 1959435 2481835 := bstep (se 1 (by rfl) ⟨1861376, by rfl⟩ : syracuseStep 2481835 = 3722753) B3722753
theorem B3309113 : Blo 1959435 3309113 := bstep (se 2 (by rfl) ⟨1240917, by rfl⟩ : syracuseStep 3309113 = 2481835) B2481835
theorem B2206075 : Blo 1959435 2206075 := bstep (se 1 (by rfl) ⟨1654556, by rfl⟩ : syracuseStep 2206075 = 3309113) B3309113
theorem B2941433 : Blo 1959435 2941433 := bstep (se 2 (by rfl) ⟨1103037, by rfl⟩ : syracuseStep 2941433 = 2206075) B2206075
theorem B1960955 : Blo 1959435 1960955 := bstep (se 1 (by rfl) ⟨1470716, by rfl⟩ : syracuseStep 1960955 = 2941433) B2941433
theorem B6044501 : Blo 1959435 6044501 := bbase (se 9 (by rfl) ⟨17708, by rfl⟩ : syracuseStep 6044501 = 35417) (by norm_num)
theorem B16118669 : Blo 1959435 16118669 := bstep (se 3 (by rfl) ⟨3022250, by rfl⟩ : syracuseStep 16118669 = 6044501) B6044501
theorem B10745779 : Blo 1959435 10745779 := bstep (se 1 (by rfl) ⟨8059334, by rfl⟩ : syracuseStep 10745779 = 16118669) B16118669
theorem B14327705 : Blo 1959435 14327705 := bstep (se 2 (by rfl) ⟨5372889, by rfl⟩ : syracuseStep 14327705 = 10745779) B10745779
theorem B9551803 : Blo 1959435 9551803 := bstep (se 1 (by rfl) ⟨7163852, by rfl⟩ : syracuseStep 9551803 = 14327705) B14327705
theorem B12735737 : Blo 1959435 12735737 := bstep (se 2 (by rfl) ⟨4775901, by rfl⟩ : syracuseStep 12735737 = 9551803) B9551803
theorem B8490491 : Blo 1959435 8490491 := bstep (se 1 (by rfl) ⟨6367868, by rfl⟩ : syracuseStep 8490491 = 12735737) B12735737
theorem B5660327 : Blo 1959435 5660327 := bstep (se 1 (by rfl) ⟨4245245, by rfl⟩ : syracuseStep 5660327 = 8490491) B8490491
theorem B3773551 : Blo 1959435 3773551 := bstep (se 1 (by rfl) ⟨2830163, by rfl⟩ : syracuseStep 3773551 = 5660327) B5660327
theorem B5031401 : Blo 1959435 5031401 := bstep (se 2 (by rfl) ⟨1886775, by rfl⟩ : syracuseStep 5031401 = 3773551) B3773551
theorem B53668277 : Blo 1959435 53668277 := bstep (se 5 (by rfl) ⟨2515700, by rfl⟩ : syracuseStep 53668277 = 5031401) B5031401
theorem B35778851 : Blo 1959435 35778851 := bstep (se 1 (by rfl) ⟨26834138, by rfl⟩ : syracuseStep 35778851 = 53668277) B53668277
theorem B23852567 : Blo 1959435 23852567 := bstep (se 1 (by rfl) ⟨17889425, by rfl⟩ : syracuseStep 23852567 = 35778851) B35778851
theorem B63606845 : Blo 1959435 63606845 := bstep (se 3 (by rfl) ⟨11926283, by rfl⟩ : syracuseStep 63606845 = 23852567) B23852567
theorem B42404563 : Blo 1959435 42404563 := bstep (se 1 (by rfl) ⟨31803422, by rfl⟩ : syracuseStep 42404563 = 63606845) B63606845
theorem B56539417 : Blo 1959435 56539417 := bstep (se 2 (by rfl) ⟨21202281, by rfl⟩ : syracuseStep 56539417 = 42404563) B42404563
theorem B75385889 : Blo 1959435 75385889 := bstep (se 2 (by rfl) ⟨28269708, by rfl⟩ : syracuseStep 75385889 = 56539417) B56539417
theorem B50257259 : Blo 1959435 50257259 := bstep (se 1 (by rfl) ⟨37692944, by rfl⟩ : syracuseStep 50257259 = 75385889) B75385889
theorem B33504839 : Blo 1959435 33504839 := bstep (se 1 (by rfl) ⟨25128629, by rfl⟩ : syracuseStep 33504839 = 50257259) B50257259
theorem B22336559 : Blo 1959435 22336559 := bstep (se 1 (by rfl) ⟨16752419, by rfl⟩ : syracuseStep 22336559 = 33504839) B33504839
theorem B14891039 : Blo 1959435 14891039 := bstep (se 1 (by rfl) ⟨11168279, by rfl⟩ : syracuseStep 14891039 = 22336559) B22336559
theorem B9927359 : Blo 1959435 9927359 := bstep (se 1 (by rfl) ⟨7445519, by rfl⟩ : syracuseStep 9927359 = 14891039) B14891039
theorem B6618239 : Blo 1959435 6618239 := bstep (se 1 (by rfl) ⟨4963679, by rfl⟩ : syracuseStep 6618239 = 9927359) B9927359
theorem B4412159 : Blo 1959435 4412159 := bstep (se 1 (by rfl) ⟨3309119, by rfl⟩ : syracuseStep 4412159 = 6618239) B6618239
theorem B2941439 : Blo 1959435 2941439 := bstep (se 1 (by rfl) ⟨2206079, by rfl⟩ : syracuseStep 2941439 = 4412159) B4412159
theorem B1960959 : Blo 1959435 1960959 := bstep (se 1 (by rfl) ⟨1470719, by rfl⟩ : syracuseStep 1960959 = 2941439) B2941439
theorem B2941445 : Blo 1959435 2941445 := bbase (se 4 (by rfl) ⟨275760, by rfl⟩ : syracuseStep 2941445 = 551521) (by norm_num)
theorem B1960963 : Blo 1959435 1960963 := bstep (se 1 (by rfl) ⟨1470722, by rfl⟩ : syracuseStep 1960963 = 2941445) B2941445
theorem B3309133 : Blo 1959435 3309133 := bbase (se 3 (by rfl) ⟨620462, by rfl⟩ : syracuseStep 3309133 = 1240925) (by norm_num)
theorem B4412177 : Blo 1959435 4412177 := bstep (se 2 (by rfl) ⟨1654566, by rfl⟩ : syracuseStep 4412177 = 3309133) B3309133
theorem B2941451 : Blo 1959435 2941451 := bstep (se 1 (by rfl) ⟨2206088, by rfl⟩ : syracuseStep 2941451 = 4412177) B4412177
theorem B1960967 : Blo 1959435 1960967 := bstep (se 1 (by rfl) ⟨1470725, by rfl⟩ : syracuseStep 1960967 = 2941451) B2941451
theorem B2206093 : Blo 1959435 2206093 := bbase (se 3 (by rfl) ⟨413642, by rfl⟩ : syracuseStep 2206093 = 827285) (by norm_num)
theorem B2941457 : Blo 1959435 2941457 := bstep (se 2 (by rfl) ⟨1103046, by rfl⟩ : syracuseStep 2941457 = 2206093) B2206093
theorem B1960971 : Blo 1959435 1960971 := bstep (se 1 (by rfl) ⟨1470728, by rfl⟩ : syracuseStep 1960971 = 2941457) B2941457
theorem B6618293 : Blo 1959435 6618293 := bbase (se 5 (by rfl) ⟨310232, by rfl⟩ : syracuseStep 6618293 = 620465) (by norm_num)
theorem B4412195 : Blo 1959435 4412195 := bstep (se 1 (by rfl) ⟨3309146, by rfl⟩ : syracuseStep 4412195 = 6618293) B6618293
theorem B2941463 : Blo 1959435 2941463 := bstep (se 1 (by rfl) ⟨2206097, by rfl⟩ : syracuseStep 2941463 = 4412195) B4412195
theorem B1960975 : Blo 1959435 1960975 := bstep (se 1 (by rfl) ⟨1470731, by rfl⟩ : syracuseStep 1960975 = 2941463) B2941463
theorem B2941469 : Blo 1959435 2941469 := bbase (se 3 (by rfl) ⟨551525, by rfl⟩ : syracuseStep 2941469 = 1103051) (by norm_num)
theorem B1960979 : Blo 1959435 1960979 := bstep (se 1 (by rfl) ⟨1470734, by rfl⟩ : syracuseStep 1960979 = 2941469) B2941469
theorem B4412213 : Blo 1959435 4412213 := bbase (se 5 (by rfl) ⟨206822, by rfl⟩ : syracuseStep 4412213 = 413645) (by norm_num)
theorem B2941475 : Blo 1959435 2941475 := bstep (se 1 (by rfl) ⟨2206106, by rfl⟩ : syracuseStep 2941475 = 4412213) B4412213
theorem B1960983 : Blo 1959435 1960983 := bstep (se 1 (by rfl) ⟨1470737, by rfl⟩ : syracuseStep 1960983 = 2941475) B2941475
theorem B3533765 : Blo 1959435 3533765 := bbase (se 4 (by rfl) ⟨331290, by rfl⟩ : syracuseStep 3533765 = 662581) (by norm_num)
theorem B9423373 : Blo 1959435 9423373 := bstep (se 3 (by rfl) ⟨1766882, by rfl⟩ : syracuseStep 9423373 = 3533765) B3533765
theorem B12564497 : Blo 1959435 12564497 := bstep (se 2 (by rfl) ⟨4711686, by rfl⟩ : syracuseStep 12564497 = 9423373) B9423373
theorem B8376331 : Blo 1959435 8376331 := bstep (se 1 (by rfl) ⟨6282248, by rfl⟩ : syracuseStep 8376331 = 12564497) B12564497
theorem B11168441 : Blo 1959435 11168441 := bstep (se 2 (by rfl) ⟨4188165, by rfl⟩ : syracuseStep 11168441 = 8376331) B8376331
theorem B7445627 : Blo 1959435 7445627 := bstep (se 1 (by rfl) ⟨5584220, by rfl⟩ : syracuseStep 7445627 = 11168441) B11168441
theorem B4963751 : Blo 1959435 4963751 := bstep (se 1 (by rfl) ⟨3722813, by rfl⟩ : syracuseStep 4963751 = 7445627) B7445627
theorem B3309167 : Blo 1959435 3309167 := bstep (se 1 (by rfl) ⟨2481875, by rfl⟩ : syracuseStep 3309167 = 4963751) B4963751
theorem B2206111 : Blo 1959435 2206111 := bstep (se 1 (by rfl) ⟨1654583, by rfl⟩ : syracuseStep 2206111 = 3309167) B3309167
theorem B2941481 : Blo 1959435 2941481 := bstep (se 2 (by rfl) ⟨1103055, by rfl⟩ : syracuseStep 2941481 = 2206111) B2206111
theorem B1960987 : Blo 1959435 1960987 := bstep (se 1 (by rfl) ⟨1470740, by rfl⟩ : syracuseStep 1960987 = 2941481) B2941481
theorem B26834581 : Blo 1959435 26834581 := bbase (se 6 (by rfl) ⟨628935, by rfl⟩ : syracuseStep 26834581 = 1257871) (by norm_num)
theorem B35779441 : Blo 1959435 35779441 := bstep (se 2 (by rfl) ⟨13417290, by rfl⟩ : syracuseStep 35779441 = 26834581) B26834581
theorem B47705921 : Blo 1959435 47705921 := bstep (se 2 (by rfl) ⟨17889720, by rfl⟩ : syracuseStep 47705921 = 35779441) B35779441
theorem B31803947 : Blo 1959435 31803947 := bstep (se 1 (by rfl) ⟨23852960, by rfl⟩ : syracuseStep 31803947 = 47705921) B47705921
theorem B21202631 : Blo 1959435 21202631 := bstep (se 1 (by rfl) ⟨15901973, by rfl⟩ : syracuseStep 21202631 = 31803947) B31803947
theorem B14135087 : Blo 1959435 14135087 := bstep (se 1 (by rfl) ⟨10601315, by rfl⟩ : syracuseStep 14135087 = 21202631) B21202631
theorem B9423391 : Blo 1959435 9423391 := bstep (se 1 (by rfl) ⟨7067543, by rfl⟩ : syracuseStep 9423391 = 14135087) B14135087
theorem B12564521 : Blo 1959435 12564521 := bstep (se 2 (by rfl) ⟨4711695, by rfl⟩ : syracuseStep 12564521 = 9423391) B9423391
theorem B8376347 : Blo 1959435 8376347 := bstep (se 1 (by rfl) ⟨6282260, by rfl⟩ : syracuseStep 8376347 = 12564521) B12564521
theorem B5584231 : Blo 1959435 5584231 := bstep (se 1 (by rfl) ⟨4188173, by rfl⟩ : syracuseStep 5584231 = 8376347) B8376347
theorem B7445641 : Blo 1959435 7445641 := bstep (se 2 (by rfl) ⟨2792115, by rfl⟩ : syracuseStep 7445641 = 5584231) B5584231
theorem B9927521 : Blo 1959435 9927521 := bstep (se 2 (by rfl) ⟨3722820, by rfl⟩ : syracuseStep 9927521 = 7445641) B7445641
theorem B6618347 : Blo 1959435 6618347 := bstep (se 1 (by rfl) ⟨4963760, by rfl⟩ : syracuseStep 6618347 = 9927521) B9927521
theorem B4412231 : Blo 1959435 4412231 := bstep (se 1 (by rfl) ⟨3309173, by rfl⟩ : syracuseStep 4412231 = 6618347) B6618347
theorem B2941487 : Blo 1959435 2941487 := bstep (se 1 (by rfl) ⟨2206115, by rfl⟩ : syracuseStep 2941487 = 4412231) B4412231
theorem B1960991 : Blo 1959435 1960991 := bstep (se 1 (by rfl) ⟨1470743, by rfl⟩ : syracuseStep 1960991 = 2941487) B2941487
theorem B2941493 : Blo 1959435 2941493 := bbase (se 5 (by rfl) ⟨137882, by rfl⟩ : syracuseStep 2941493 = 275765) (by norm_num)
theorem B1960995 : Blo 1959435 1960995 := bstep (se 1 (by rfl) ⟨1470746, by rfl⟩ : syracuseStep 1960995 = 2941493) B2941493
theorem B4963781 : Blo 1959435 4963781 := bbase (se 4 (by rfl) ⟨465354, by rfl⟩ : syracuseStep 4963781 = 930709) (by norm_num)
theorem B3309187 : Blo 1959435 3309187 := bstep (se 1 (by rfl) ⟨2481890, by rfl⟩ : syracuseStep 3309187 = 4963781) B4963781
theorem B4412249 : Blo 1959435 4412249 := bstep (se 2 (by rfl) ⟨1654593, by rfl⟩ : syracuseStep 4412249 = 3309187) B3309187
theorem B2941499 : Blo 1959435 2941499 := bstep (se 1 (by rfl) ⟨2206124, by rfl⟩ : syracuseStep 2941499 = 4412249) B4412249
theorem B1960999 : Blo 1959435 1960999 := bstep (se 1 (by rfl) ⟨1470749, by rfl⟩ : syracuseStep 1960999 = 2941499) B2941499
theorem B2206129 : Blo 1959435 2206129 := bbase (se 2 (by rfl) ⟨827298, by rfl⟩ : syracuseStep 2206129 = 1654597) (by norm_num)
theorem B2941505 : Blo 1959435 2941505 := bstep (se 2 (by rfl) ⟨1103064, by rfl⟩ : syracuseStep 2941505 = 2206129) B2206129
theorem B1961003 : Blo 1959435 1961003 := bstep (se 1 (by rfl) ⟨1470752, by rfl⟩ : syracuseStep 1961003 = 2941505) B2941505
theorem B5584277 : Blo 1959435 5584277 := bbase (se 6 (by rfl) ⟨130881, by rfl⟩ : syracuseStep 5584277 = 261763) (by norm_num)
theorem B3722851 : Blo 1959435 3722851 := bstep (se 1 (by rfl) ⟨2792138, by rfl⟩ : syracuseStep 3722851 = 5584277) B5584277
theorem B4963801 : Blo 1959435 4963801 := bstep (se 2 (by rfl) ⟨1861425, by rfl⟩ : syracuseStep 4963801 = 3722851) B3722851
theorem B6618401 : Blo 1959435 6618401 := bstep (se 2 (by rfl) ⟨2481900, by rfl⟩ : syracuseStep 6618401 = 4963801) B4963801
theorem B4412267 : Blo 1959435 4412267 := bstep (se 1 (by rfl) ⟨3309200, by rfl⟩ : syracuseStep 4412267 = 6618401) B6618401
theorem B2941511 : Blo 1959435 2941511 := bstep (se 1 (by rfl) ⟨2206133, by rfl⟩ : syracuseStep 2941511 = 4412267) B4412267
theorem B1961007 : Blo 1959435 1961007 := bstep (se 1 (by rfl) ⟨1470755, by rfl⟩ : syracuseStep 1961007 = 2941511) B2941511
theorem B2941517 : Blo 1959435 2941517 := bbase (se 3 (by rfl) ⟨551534, by rfl⟩ : syracuseStep 2941517 = 1103069) (by norm_num)
theorem B1961011 : Blo 1959435 1961011 := bstep (se 1 (by rfl) ⟨1470758, by rfl⟩ : syracuseStep 1961011 = 2941517) B2941517
theorem B4412285 : Blo 1959435 4412285 := bbase (se 3 (by rfl) ⟨827303, by rfl⟩ : syracuseStep 4412285 = 1654607) (by norm_num)
theorem B2941523 : Blo 1959435 2941523 := bstep (se 1 (by rfl) ⟨2206142, by rfl⟩ : syracuseStep 2941523 = 4412285) B4412285
theorem B1961015 : Blo 1959435 1961015 := bstep (se 1 (by rfl) ⟨1470761, by rfl⟩ : syracuseStep 1961015 = 2941523) B2941523
theorem B3309221 : Blo 1959435 3309221 := bbase (se 4 (by rfl) ⟨310239, by rfl⟩ : syracuseStep 3309221 = 620479) (by norm_num)
theorem B2206147 : Blo 1959435 2206147 := bstep (se 1 (by rfl) ⟨1654610, by rfl⟩ : syracuseStep 2206147 = 3309221) B3309221
theorem B2941529 : Blo 1959435 2941529 := bstep (se 2 (by rfl) ⟨1103073, by rfl⟩ : syracuseStep 2941529 = 2206147) B2206147
theorem B1961019 : Blo 1959435 1961019 := bstep (se 1 (by rfl) ⟨1470764, by rfl⟩ : syracuseStep 1961019 = 2941529) B2941529
theorem B2094121 : Blo 1959435 2094121 := bbase (se 2 (by rfl) ⟨785295, by rfl⟩ : syracuseStep 2094121 = 1570591) (by norm_num)
theorem B2792161 : Blo 1959435 2792161 := bstep (se 2 (by rfl) ⟨1047060, by rfl⟩ : syracuseStep 2792161 = 2094121) B2094121
theorem B14891525 : Blo 1959435 14891525 := bstep (se 4 (by rfl) ⟨1396080, by rfl⟩ : syracuseStep 14891525 = 2792161) B2792161
theorem B9927683 : Blo 1959435 9927683 := bstep (se 1 (by rfl) ⟨7445762, by rfl⟩ : syracuseStep 9927683 = 14891525) B14891525
theorem B6618455 : Blo 1959435 6618455 := bstep (se 1 (by rfl) ⟨4963841, by rfl⟩ : syracuseStep 6618455 = 9927683) B9927683
theorem B4412303 : Blo 1959435 4412303 := bstep (se 1 (by rfl) ⟨3309227, by rfl⟩ : syracuseStep 4412303 = 6618455) B6618455
theorem B2941535 : Blo 1959435 2941535 := bstep (se 1 (by rfl) ⟨2206151, by rfl⟩ : syracuseStep 2941535 = 4412303) B4412303
theorem B1961023 : Blo 1959435 1961023 := bstep (se 1 (by rfl) ⟨1470767, by rfl⟩ : syracuseStep 1961023 = 2941535) B2941535
theorem B2941541 : Blo 1959435 2941541 := bbase (se 4 (by rfl) ⟨275769, by rfl⟩ : syracuseStep 2941541 = 551539) (by norm_num)
theorem B1961027 : Blo 1959435 1961027 := bstep (se 1 (by rfl) ⟨1470770, by rfl⟩ : syracuseStep 1961027 = 2941541) B2941541
theorem B2792173 : Blo 1959435 2792173 := bbase (se 3 (by rfl) ⟨523532, by rfl⟩ : syracuseStep 2792173 = 1047065) (by norm_num)
theorem B3722897 : Blo 1959435 3722897 := bstep (se 2 (by rfl) ⟨1396086, by rfl⟩ : syracuseStep 3722897 = 2792173) B2792173
theorem B2481931 : Blo 1959435 2481931 := bstep (se 1 (by rfl) ⟨1861448, by rfl⟩ : syracuseStep 2481931 = 3722897) B3722897
theorem B3309241 : Blo 1959435 3309241 := bstep (se 2 (by rfl) ⟨1240965, by rfl⟩ : syracuseStep 3309241 = 2481931) B2481931
theorem B4412321 : Blo 1959435 4412321 := bstep (se 2 (by rfl) ⟨1654620, by rfl⟩ : syracuseStep 4412321 = 3309241) B3309241
theorem B2941547 : Blo 1959435 2941547 := bstep (se 1 (by rfl) ⟨2206160, by rfl⟩ : syracuseStep 2941547 = 4412321) B4412321
theorem B1961031 : Blo 1959435 1961031 := bstep (se 1 (by rfl) ⟨1470773, by rfl⟩ : syracuseStep 1961031 = 2941547) B2941547
theorem B2206165 : Blo 1959435 2206165 := bbase (se 7 (by rfl) ⟨25853, by rfl⟩ : syracuseStep 2206165 = 51707) (by norm_num)
theorem B2941553 : Blo 1959435 2941553 := bstep (se 2 (by rfl) ⟨1103082, by rfl⟩ : syracuseStep 2941553 = 2206165) B2206165
theorem B1961035 : Blo 1959435 1961035 := bstep (se 1 (by rfl) ⟨1470776, by rfl⟩ : syracuseStep 1961035 = 2941553) B2941553
theorem B2481941 : Blo 1959435 2481941 := bbase (se 6 (by rfl) ⟨58170, by rfl⟩ : syracuseStep 2481941 = 116341) (by norm_num)
theorem B6618509 : Blo 1959435 6618509 := bstep (se 3 (by rfl) ⟨1240970, by rfl⟩ : syracuseStep 6618509 = 2481941) B2481941
theorem B4412339 : Blo 1959435 4412339 := bstep (se 1 (by rfl) ⟨3309254, by rfl⟩ : syracuseStep 4412339 = 6618509) B6618509
theorem B2941559 : Blo 1959435 2941559 := bstep (se 1 (by rfl) ⟨2206169, by rfl⟩ : syracuseStep 2941559 = 4412339) B4412339
theorem B1961039 : Blo 1959435 1961039 := bstep (se 1 (by rfl) ⟨1470779, by rfl⟩ : syracuseStep 1961039 = 2941559) B2941559
theorem B2941565 : Blo 1959435 2941565 := bbase (se 3 (by rfl) ⟨551543, by rfl⟩ : syracuseStep 2941565 = 1103087) (by norm_num)
theorem B1961043 : Blo 1959435 1961043 := bstep (se 1 (by rfl) ⟨1470782, by rfl⟩ : syracuseStep 1961043 = 2941565) B2941565
theorem B4412357 : Blo 1959435 4412357 := bbase (se 4 (by rfl) ⟨413658, by rfl⟩ : syracuseStep 4412357 = 827317) (by norm_num)
theorem B2941571 : Blo 1959435 2941571 := bstep (se 1 (by rfl) ⟨2206178, by rfl⟩ : syracuseStep 2941571 = 4412357) B4412357
theorem B1961047 : Blo 1959435 1961047 := bstep (se 1 (by rfl) ⟨1470785, by rfl⟩ : syracuseStep 1961047 = 2941571) B2941571
theorem B2236285 : Blo 1959435 2236285 := bbase (se 3 (by rfl) ⟨419303, by rfl⟩ : syracuseStep 2236285 = 838607) (by norm_num)
theorem B2981713 : Blo 1959435 2981713 := bstep (se 2 (by rfl) ⟨1118142, by rfl⟩ : syracuseStep 2981713 = 2236285) B2236285
theorem B3975617 : Blo 1959435 3975617 := bstep (se 2 (by rfl) ⟨1490856, by rfl⟩ : syracuseStep 3975617 = 2981713) B2981713
theorem B2650411 : Blo 1959435 2650411 := bstep (se 1 (by rfl) ⟨1987808, by rfl⟩ : syracuseStep 2650411 = 3975617) B3975617
theorem B3533881 : Blo 1959435 3533881 := bstep (se 2 (by rfl) ⟨1325205, by rfl⟩ : syracuseStep 3533881 = 2650411) B2650411
theorem B4711841 : Blo 1959435 4711841 := bstep (se 2 (by rfl) ⟨1766940, by rfl⟩ : syracuseStep 4711841 = 3533881) B3533881
theorem B3141227 : Blo 1959435 3141227 := bstep (se 1 (by rfl) ⟨2355920, by rfl⟩ : syracuseStep 3141227 = 4711841) B4711841
theorem B8376605 : Blo 1959435 8376605 := bstep (se 3 (by rfl) ⟨1570613, by rfl⟩ : syracuseStep 8376605 = 3141227) B3141227
theorem B5584403 : Blo 1959435 5584403 := bstep (se 1 (by rfl) ⟨4188302, by rfl⟩ : syracuseStep 5584403 = 8376605) B8376605
theorem B3722935 : Blo 1959435 3722935 := bstep (se 1 (by rfl) ⟨2792201, by rfl⟩ : syracuseStep 3722935 = 5584403) B5584403
theorem B4963913 : Blo 1959435 4963913 := bstep (se 2 (by rfl) ⟨1861467, by rfl⟩ : syracuseStep 4963913 = 3722935) B3722935
theorem B3309275 : Blo 1959435 3309275 := bstep (se 1 (by rfl) ⟨2481956, by rfl⟩ : syracuseStep 3309275 = 4963913) B4963913
theorem B2206183 : Blo 1959435 2206183 := bstep (se 1 (by rfl) ⟨1654637, by rfl⟩ : syracuseStep 2206183 = 3309275) B3309275
theorem B2941577 : Blo 1959435 2941577 := bstep (se 2 (by rfl) ⟨1103091, by rfl⟩ : syracuseStep 2941577 = 2206183) B2206183
theorem B1961051 : Blo 1959435 1961051 := bstep (se 1 (by rfl) ⟨1470788, by rfl⟩ : syracuseStep 1961051 = 2941577) B2941577
theorem B9927845 : Blo 1959435 9927845 := bbase (se 4 (by rfl) ⟨930735, by rfl⟩ : syracuseStep 9927845 = 1861471) (by norm_num)
theorem B6618563 : Blo 1959435 6618563 := bstep (se 1 (by rfl) ⟨4963922, by rfl⟩ : syracuseStep 6618563 = 9927845) B9927845
theorem B4412375 : Blo 1959435 4412375 := bstep (se 1 (by rfl) ⟨3309281, by rfl⟩ : syracuseStep 4412375 = 6618563) B6618563
theorem B2941583 : Blo 1959435 2941583 := bstep (se 1 (by rfl) ⟨2206187, by rfl⟩ : syracuseStep 2941583 = 4412375) B4412375
theorem B1961055 : Blo 1959435 1961055 := bstep (se 1 (by rfl) ⟨1470791, by rfl⟩ : syracuseStep 1961055 = 2941583) B2941583
theorem B2941589 : Blo 1959435 2941589 := bbase (se 6 (by rfl) ⟨68943, by rfl⟩ : syracuseStep 2941589 = 137887) (by norm_num)
theorem B1961059 : Blo 1959435 1961059 := bstep (se 1 (by rfl) ⟨1470794, by rfl⟩ : syracuseStep 1961059 = 2941589) B2941589
theorem B20126677 : Blo 1959435 20126677 := bbase (se 7 (by rfl) ⟨235859, by rfl⟩ : syracuseStep 20126677 = 471719) (by norm_num)
theorem B26835569 : Blo 1959435 26835569 := bstep (se 2 (by rfl) ⟨10063338, by rfl⟩ : syracuseStep 26835569 = 20126677) B20126677
theorem B17890379 : Blo 1959435 17890379 := bstep (se 1 (by rfl) ⟨13417784, by rfl⟩ : syracuseStep 17890379 = 26835569) B26835569
theorem B11926919 : Blo 1959435 11926919 := bstep (se 1 (by rfl) ⟨8945189, by rfl⟩ : syracuseStep 11926919 = 17890379) B17890379
theorem B7951279 : Blo 1959435 7951279 := bstep (se 1 (by rfl) ⟨5963459, by rfl⟩ : syracuseStep 7951279 = 11926919) B11926919
theorem B10601705 : Blo 1959435 10601705 := bstep (se 2 (by rfl) ⟨3975639, by rfl⟩ : syracuseStep 10601705 = 7951279) B7951279
theorem B28271213 : Blo 1959435 28271213 := bstep (se 3 (by rfl) ⟨5300852, by rfl⟩ : syracuseStep 28271213 = 10601705) B10601705
theorem B18847475 : Blo 1959435 18847475 := bstep (se 1 (by rfl) ⟨14135606, by rfl⟩ : syracuseStep 18847475 = 28271213) B28271213
theorem B12564983 : Blo 1959435 12564983 := bstep (se 1 (by rfl) ⟨9423737, by rfl⟩ : syracuseStep 12564983 = 18847475) B18847475
theorem B8376655 : Blo 1959435 8376655 := bstep (se 1 (by rfl) ⟨6282491, by rfl⟩ : syracuseStep 8376655 = 12564983) B12564983
theorem B11168873 : Blo 1959435 11168873 := bstep (se 2 (by rfl) ⟨4188327, by rfl⟩ : syracuseStep 11168873 = 8376655) B8376655
theorem B7445915 : Blo 1959435 7445915 := bstep (se 1 (by rfl) ⟨5584436, by rfl⟩ : syracuseStep 7445915 = 11168873) B11168873
theorem B4963943 : Blo 1959435 4963943 := bstep (se 1 (by rfl) ⟨3722957, by rfl⟩ : syracuseStep 4963943 = 7445915) B7445915
theorem B3309295 : Blo 1959435 3309295 := bstep (se 1 (by rfl) ⟨2481971, by rfl⟩ : syracuseStep 3309295 = 4963943) B4963943
theorem B4412393 : Blo 1959435 4412393 := bstep (se 2 (by rfl) ⟨1654647, by rfl⟩ : syracuseStep 4412393 = 3309295) B3309295
theorem B2941595 : Blo 1959435 2941595 := bstep (se 1 (by rfl) ⟨2206196, by rfl⟩ : syracuseStep 2941595 = 4412393) B4412393
theorem B1961063 : Blo 1959435 1961063 := bstep (se 1 (by rfl) ⟨1470797, by rfl⟩ : syracuseStep 1961063 = 2941595) B2941595
theorem B2206201 : Blo 1959435 2206201 := bbase (se 2 (by rfl) ⟨827325, by rfl⟩ : syracuseStep 2206201 = 1654651) (by norm_num)
theorem B2941601 : Blo 1959435 2941601 := bstep (se 2 (by rfl) ⟨1103100, by rfl⟩ : syracuseStep 2941601 = 2206201) B2206201
theorem B1961067 : Blo 1959435 1961067 := bstep (se 1 (by rfl) ⟨1470800, by rfl⟩ : syracuseStep 1961067 = 2941601) B2941601
theorem B6282517 : Blo 1959435 6282517 := bbase (se 6 (by rfl) ⟨147246, by rfl⟩ : syracuseStep 6282517 = 294493) (by norm_num)
theorem B8376689 : Blo 1959435 8376689 := bstep (se 2 (by rfl) ⟨3141258, by rfl⟩ : syracuseStep 8376689 = 6282517) B6282517
theorem B5584459 : Blo 1959435 5584459 := bstep (se 1 (by rfl) ⟨4188344, by rfl⟩ : syracuseStep 5584459 = 8376689) B8376689
theorem B7445945 : Blo 1959435 7445945 := bstep (se 2 (by rfl) ⟨2792229, by rfl⟩ : syracuseStep 7445945 = 5584459) B5584459
theorem B4963963 : Blo 1959435 4963963 := bstep (se 1 (by rfl) ⟨3722972, by rfl⟩ : syracuseStep 4963963 = 7445945) B7445945
theorem B6618617 : Blo 1959435 6618617 := bstep (se 2 (by rfl) ⟨2481981, by rfl⟩ : syracuseStep 6618617 = 4963963) B4963963
theorem B4412411 : Blo 1959435 4412411 := bstep (se 1 (by rfl) ⟨3309308, by rfl⟩ : syracuseStep 4412411 = 6618617) B6618617
theorem B2941607 : Blo 1959435 2941607 := bstep (se 1 (by rfl) ⟨2206205, by rfl⟩ : syracuseStep 2941607 = 4412411) B4412411
theorem B1961071 : Blo 1959435 1961071 := bstep (se 1 (by rfl) ⟨1470803, by rfl⟩ : syracuseStep 1961071 = 2941607) B2941607
theorem B2941613 : Blo 1959435 2941613 := bbase (se 3 (by rfl) ⟨551552, by rfl⟩ : syracuseStep 2941613 = 1103105) (by norm_num)
theorem B1961075 : Blo 1959435 1961075 := bstep (se 1 (by rfl) ⟨1470806, by rfl⟩ : syracuseStep 1961075 = 2941613) B2941613
theorem B4412429 : Blo 1959435 4412429 := bbase (se 3 (by rfl) ⟨827330, by rfl⟩ : syracuseStep 4412429 = 1654661) (by norm_num)
theorem B2941619 : Blo 1959435 2941619 := bstep (se 1 (by rfl) ⟨2206214, by rfl⟩ : syracuseStep 2941619 = 4412429) B4412429
theorem B1961079 : Blo 1959435 1961079 := bstep (se 1 (by rfl) ⟨1470809, by rfl⟩ : syracuseStep 1961079 = 2941619) B2941619
theorem B2481997 : Blo 1959435 2481997 := bbase (se 3 (by rfl) ⟨465374, by rfl⟩ : syracuseStep 2481997 = 930749) (by norm_num)
theorem B3309329 : Blo 1959435 3309329 := bstep (se 2 (by rfl) ⟨1240998, by rfl⟩ : syracuseStep 3309329 = 2481997) B2481997
theorem B2206219 : Blo 1959435 2206219 := bstep (se 1 (by rfl) ⟨1654664, by rfl⟩ : syracuseStep 2206219 = 3309329) B3309329
theorem B2941625 : Blo 1959435 2941625 := bstep (se 2 (by rfl) ⟨1103109, by rfl⟩ : syracuseStep 2941625 = 2206219) B2206219
theorem B1961083 : Blo 1959435 1961083 := bstep (se 1 (by rfl) ⟨1470812, by rfl⟩ : syracuseStep 1961083 = 2941625) B2941625
theorem B2515865 : Blo 1959435 2515865 := bbase (se 2 (by rfl) ⟨943449, by rfl⟩ : syracuseStep 2515865 = 1886899) (by norm_num)
theorem B26835893 : Blo 1959435 26835893 := bstep (se 5 (by rfl) ⟨1257932, by rfl⟩ : syracuseStep 26835893 = 2515865) B2515865
theorem B17890595 : Blo 1959435 17890595 := bstep (se 1 (by rfl) ⟨13417946, by rfl⟩ : syracuseStep 17890595 = 26835893) B26835893
theorem B11927063 : Blo 1959435 11927063 := bstep (se 1 (by rfl) ⟨8945297, by rfl⟩ : syracuseStep 11927063 = 17890595) B17890595
theorem B7951375 : Blo 1959435 7951375 := bstep (se 1 (by rfl) ⟨5963531, by rfl⟩ : syracuseStep 7951375 = 11927063) B11927063
theorem B42407333 : Blo 1959435 42407333 := bstep (se 4 (by rfl) ⟨3975687, by rfl⟩ : syracuseStep 42407333 = 7951375) B7951375
theorem B28271555 : Blo 1959435 28271555 := bstep (se 1 (by rfl) ⟨21203666, by rfl⟩ : syracuseStep 28271555 = 42407333) B42407333
theorem B18847703 : Blo 1959435 18847703 := bstep (se 1 (by rfl) ⟨14135777, by rfl⟩ : syracuseStep 18847703 = 28271555) B28271555
theorem B12565135 : Blo 1959435 12565135 := bstep (se 1 (by rfl) ⟨9423851, by rfl⟩ : syracuseStep 12565135 = 18847703) B18847703
theorem B16753513 : Blo 1959435 16753513 := bstep (se 2 (by rfl) ⟨6282567, by rfl⟩ : syracuseStep 16753513 = 12565135) B12565135
theorem B22338017 : Blo 1959435 22338017 := bstep (se 2 (by rfl) ⟨8376756, by rfl⟩ : syracuseStep 22338017 = 16753513) B16753513
theorem B14892011 : Blo 1959435 14892011 := bstep (se 1 (by rfl) ⟨11169008, by rfl⟩ : syracuseStep 14892011 = 22338017) B22338017
theorem B9928007 : Blo 1959435 9928007 := bstep (se 1 (by rfl) ⟨7446005, by rfl⟩ : syracuseStep 9928007 = 14892011) B14892011
theorem B6618671 : Blo 1959435 6618671 := bstep (se 1 (by rfl) ⟨4964003, by rfl⟩ : syracuseStep 6618671 = 9928007) B9928007
theorem B4412447 : Blo 1959435 4412447 := bstep (se 1 (by rfl) ⟨3309335, by rfl⟩ : syracuseStep 4412447 = 6618671) B6618671
theorem B2941631 : Blo 1959435 2941631 := bstep (se 1 (by rfl) ⟨2206223, by rfl⟩ : syracuseStep 2941631 = 4412447) B4412447
theorem B1961087 : Blo 1959435 1961087 := bstep (se 1 (by rfl) ⟨1470815, by rfl⟩ : syracuseStep 1961087 = 2941631) B2941631
theorem B2941637 : Blo 1959435 2941637 := bbase (se 4 (by rfl) ⟨275778, by rfl⟩ : syracuseStep 2941637 = 551557) (by norm_num)
theorem B1961091 : Blo 1959435 1961091 := bstep (se 1 (by rfl) ⟨1470818, by rfl⟩ : syracuseStep 1961091 = 2941637) B2941637
theorem B3309349 : Blo 1959435 3309349 := bbase (se 4 (by rfl) ⟨310251, by rfl⟩ : syracuseStep 3309349 = 620503) (by norm_num)
theorem B4412465 : Blo 1959435 4412465 := bstep (se 2 (by rfl) ⟨1654674, by rfl⟩ : syracuseStep 4412465 = 3309349) B3309349
theorem B2941643 : Blo 1959435 2941643 := bstep (se 1 (by rfl) ⟨2206232, by rfl⟩ : syracuseStep 2941643 = 4412465) B4412465
theorem B1961095 : Blo 1959435 1961095 := bstep (se 1 (by rfl) ⟨1470821, by rfl⟩ : syracuseStep 1961095 = 2941643) B2941643
theorem B2206237 : Blo 1959435 2206237 := bbase (se 3 (by rfl) ⟨413669, by rfl⟩ : syracuseStep 2206237 = 827339) (by norm_num)
theorem B2941649 : Blo 1959435 2941649 := bstep (se 2 (by rfl) ⟨1103118, by rfl⟩ : syracuseStep 2941649 = 2206237) B2206237
theorem B1961099 : Blo 1959435 1961099 := bstep (se 1 (by rfl) ⟨1470824, by rfl⟩ : syracuseStep 1961099 = 2941649) B2941649
theorem B6618725 : Blo 1959435 6618725 := bbase (se 4 (by rfl) ⟨620505, by rfl⟩ : syracuseStep 6618725 = 1241011) (by norm_num)
theorem B4412483 : Blo 1959435 4412483 := bstep (se 1 (by rfl) ⟨3309362, by rfl⟩ : syracuseStep 4412483 = 6618725) B6618725
theorem B2941655 : Blo 1959435 2941655 := bstep (se 1 (by rfl) ⟨2206241, by rfl⟩ : syracuseStep 2941655 = 4412483) B4412483
theorem B1961103 : Blo 1959435 1961103 := bstep (se 1 (by rfl) ⟨1470827, by rfl⟩ : syracuseStep 1961103 = 2941655) B2941655
theorem B2941661 : Blo 1959435 2941661 := bbase (se 3 (by rfl) ⟨551561, by rfl⟩ : syracuseStep 2941661 = 1103123) (by norm_num)
theorem B1961107 : Blo 1959435 1961107 := bstep (se 1 (by rfl) ⟨1470830, by rfl⟩ : syracuseStep 1961107 = 2941661) B2941661
theorem B4412501 : Blo 1959435 4412501 := bbase (se 8 (by rfl) ⟨25854, by rfl⟩ : syracuseStep 4412501 = 51709) (by norm_num)
theorem B2941667 : Blo 1959435 2941667 := bstep (se 1 (by rfl) ⟨2206250, by rfl⟩ : syracuseStep 2941667 = 4412501) B4412501
theorem B1961111 : Blo 1959435 1961111 := bstep (se 1 (by rfl) ⟨1470833, by rfl⟩ : syracuseStep 1961111 = 2941667) B2941667
theorem B9423989 : Blo 1959435 9423989 := bbase (se 5 (by rfl) ⟨441749, by rfl⟩ : syracuseStep 9423989 = 883499) (by norm_num)
theorem B6282659 : Blo 1959435 6282659 := bstep (se 1 (by rfl) ⟨4711994, by rfl⟩ : syracuseStep 6282659 = 9423989) B9423989
theorem B4188439 : Blo 1959435 4188439 := bstep (se 1 (by rfl) ⟨3141329, by rfl⟩ : syracuseStep 4188439 = 6282659) B6282659
theorem B5584585 : Blo 1959435 5584585 := bstep (se 2 (by rfl) ⟨2094219, by rfl⟩ : syracuseStep 5584585 = 4188439) B4188439
theorem B7446113 : Blo 1959435 7446113 := bstep (se 2 (by rfl) ⟨2792292, by rfl⟩ : syracuseStep 7446113 = 5584585) B5584585
theorem B4964075 : Blo 1959435 4964075 := bstep (se 1 (by rfl) ⟨3723056, by rfl⟩ : syracuseStep 4964075 = 7446113) B7446113
theorem B3309383 : Blo 1959435 3309383 := bstep (se 1 (by rfl) ⟨2482037, by rfl⟩ : syracuseStep 3309383 = 4964075) B4964075
theorem B2206255 : Blo 1959435 2206255 := bstep (se 1 (by rfl) ⟨1654691, by rfl⟩ : syracuseStep 2206255 = 3309383) B3309383
theorem B2941673 : Blo 1959435 2941673 := bstep (se 2 (by rfl) ⟨1103127, by rfl⟩ : syracuseStep 2941673 = 2206255) B2206255
theorem B1961115 : Blo 1959435 1961115 := bstep (se 1 (by rfl) ⟨1470836, by rfl⟩ : syracuseStep 1961115 = 2941673) B2941673
theorem B2236361 : Blo 1959435 2236361 := bbase (se 2 (by rfl) ⟨838635, by rfl⟩ : syracuseStep 2236361 = 1677271) (by norm_num)
theorem B5963629 : Blo 1959435 5963629 := bstep (se 3 (by rfl) ⟨1118180, by rfl⟩ : syracuseStep 5963629 = 2236361) B2236361
theorem B7951505 : Blo 1959435 7951505 := bstep (se 2 (by rfl) ⟨2981814, by rfl⟩ : syracuseStep 7951505 = 5963629) B5963629
theorem B21204013 : Blo 1959435 21204013 := bstep (se 3 (by rfl) ⟨3975752, by rfl⟩ : syracuseStep 21204013 = 7951505) B7951505
theorem B28272017 : Blo 1959435 28272017 := bstep (se 2 (by rfl) ⟨10602006, by rfl⟩ : syracuseStep 28272017 = 21204013) B21204013
theorem B18848011 : Blo 1959435 18848011 := bstep (se 1 (by rfl) ⟨14136008, by rfl⟩ : syracuseStep 18848011 = 28272017) B28272017
theorem B25130681 : Blo 1959435 25130681 := bstep (se 2 (by rfl) ⟨9424005, by rfl⟩ : syracuseStep 25130681 = 18848011) B18848011
theorem B16753787 : Blo 1959435 16753787 := bstep (se 1 (by rfl) ⟨12565340, by rfl⟩ : syracuseStep 16753787 = 25130681) B25130681
theorem B11169191 : Blo 1959435 11169191 := bstep (se 1 (by rfl) ⟨8376893, by rfl⟩ : syracuseStep 11169191 = 16753787) B16753787
theorem B7446127 : Blo 1959435 7446127 := bstep (se 1 (by rfl) ⟨5584595, by rfl⟩ : syracuseStep 7446127 = 11169191) B11169191
theorem B9928169 : Blo 1959435 9928169 := bstep (se 2 (by rfl) ⟨3723063, by rfl⟩ : syracuseStep 9928169 = 7446127) B7446127
theorem B6618779 : Blo 1959435 6618779 := bstep (se 1 (by rfl) ⟨4964084, by rfl⟩ : syracuseStep 6618779 = 9928169) B9928169
theorem B4412519 : Blo 1959435 4412519 := bstep (se 1 (by rfl) ⟨3309389, by rfl⟩ : syracuseStep 4412519 = 6618779) B6618779
theorem B2941679 : Blo 1959435 2941679 := bstep (se 1 (by rfl) ⟨2206259, by rfl⟩ : syracuseStep 2941679 = 4412519) B4412519
theorem B1961119 : Blo 1959435 1961119 := bstep (se 1 (by rfl) ⟨1470839, by rfl⟩ : syracuseStep 1961119 = 2941679) B2941679
theorem B2941685 : Blo 1959435 2941685 := bbase (se 5 (by rfl) ⟨137891, by rfl⟩ : syracuseStep 2941685 = 275783) (by norm_num)
theorem B1961123 : Blo 1959435 1961123 := bstep (se 1 (by rfl) ⟨1470842, by rfl⟩ : syracuseStep 1961123 = 2941685) B2941685
theorem B1987885 : Blo 1959435 1987885 := bbase (se 3 (by rfl) ⟨372728, by rfl⟩ : syracuseStep 1987885 = 745457) (by norm_num)
theorem B10602053 : Blo 1959435 10602053 := bstep (se 4 (by rfl) ⟨993942, by rfl⟩ : syracuseStep 10602053 = 1987885) B1987885
theorem B7068035 : Blo 1959435 7068035 := bstep (se 1 (by rfl) ⟨5301026, by rfl⟩ : syracuseStep 7068035 = 10602053) B10602053
theorem B4712023 : Blo 1959435 4712023 := bstep (se 1 (by rfl) ⟨3534017, by rfl⟩ : syracuseStep 4712023 = 7068035) B7068035
theorem B6282697 : Blo 1959435 6282697 := bstep (se 2 (by rfl) ⟨2356011, by rfl⟩ : syracuseStep 6282697 = 4712023) B4712023
theorem B8376929 : Blo 1959435 8376929 := bstep (se 2 (by rfl) ⟨3141348, by rfl⟩ : syracuseStep 8376929 = 6282697) B6282697
theorem B5584619 : Blo 1959435 5584619 := bstep (se 1 (by rfl) ⟨4188464, by rfl⟩ : syracuseStep 5584619 = 8376929) B8376929
theorem B3723079 : Blo 1959435 3723079 := bstep (se 1 (by rfl) ⟨2792309, by rfl⟩ : syracuseStep 3723079 = 5584619) B5584619
theorem B4964105 : Blo 1959435 4964105 := bstep (se 2 (by rfl) ⟨1861539, by rfl⟩ : syracuseStep 4964105 = 3723079) B3723079
theorem B3309403 : Blo 1959435 3309403 := bstep (se 1 (by rfl) ⟨2482052, by rfl⟩ : syracuseStep 3309403 = 4964105) B4964105
theorem B4412537 : Blo 1959435 4412537 := bstep (se 2 (by rfl) ⟨1654701, by rfl⟩ : syracuseStep 4412537 = 3309403) B3309403
theorem B2941691 : Blo 1959435 2941691 := bstep (se 1 (by rfl) ⟨2206268, by rfl⟩ : syracuseStep 2941691 = 4412537) B4412537
theorem B1961127 : Blo 1959435 1961127 := bstep (se 1 (by rfl) ⟨1470845, by rfl⟩ : syracuseStep 1961127 = 2941691) B2941691
theorem B2206273 : Blo 1959435 2206273 := bbase (se 2 (by rfl) ⟨827352, by rfl⟩ : syracuseStep 2206273 = 1654705) (by norm_num)
theorem B2941697 : Blo 1959435 2941697 := bstep (se 2 (by rfl) ⟨1103136, by rfl⟩ : syracuseStep 2941697 = 2206273) B2206273
theorem B1961131 : Blo 1959435 1961131 := bstep (se 1 (by rfl) ⟨1470848, by rfl⟩ : syracuseStep 1961131 = 2941697) B2941697
theorem B4964125 : Blo 1959435 4964125 := bbase (se 3 (by rfl) ⟨930773, by rfl⟩ : syracuseStep 4964125 = 1861547) (by norm_num)
theorem B6618833 : Blo 1959435 6618833 := bstep (se 2 (by rfl) ⟨2482062, by rfl⟩ : syracuseStep 6618833 = 4964125) B4964125
theorem B4412555 : Blo 1959435 4412555 := bstep (se 1 (by rfl) ⟨3309416, by rfl⟩ : syracuseStep 4412555 = 6618833) B6618833
theorem B2941703 : Blo 1959435 2941703 := bstep (se 1 (by rfl) ⟨2206277, by rfl⟩ : syracuseStep 2941703 = 4412555) B4412555
theorem B1961135 : Blo 1959435 1961135 := bstep (se 1 (by rfl) ⟨1470851, by rfl⟩ : syracuseStep 1961135 = 2941703) B2941703
theorem B2941709 : Blo 1959435 2941709 := bbase (se 3 (by rfl) ⟨551570, by rfl⟩ : syracuseStep 2941709 = 1103141) (by norm_num)
theorem B1961139 : Blo 1959435 1961139 := bstep (se 1 (by rfl) ⟨1470854, by rfl⟩ : syracuseStep 1961139 = 2941709) B2941709
theorem B4412573 : Blo 1959435 4412573 := bbase (se 3 (by rfl) ⟨827357, by rfl⟩ : syracuseStep 4412573 = 1654715) (by norm_num)
theorem B2941715 : Blo 1959435 2941715 := bstep (se 1 (by rfl) ⟨2206286, by rfl⟩ : syracuseStep 2941715 = 4412573) B4412573
theorem B1961143 : Blo 1959435 1961143 := bstep (se 1 (by rfl) ⟨1470857, by rfl⟩ : syracuseStep 1961143 = 2941715) B2941715
theorem B3309437 : Blo 1959435 3309437 := bbase (se 3 (by rfl) ⟨620519, by rfl⟩ : syracuseStep 3309437 = 1241039) (by norm_num)
theorem B2206291 : Blo 1959435 2206291 := bstep (se 1 (by rfl) ⟨1654718, by rfl⟩ : syracuseStep 2206291 = 3309437) B3309437
theorem B2941721 : Blo 1959435 2941721 := bstep (se 2 (by rfl) ⟨1103145, by rfl⟩ : syracuseStep 2941721 = 2206291) B2206291
theorem B1961147 : Blo 1959435 1961147 := bstep (se 1 (by rfl) ⟨1470860, by rfl⟩ : syracuseStep 1961147 = 2941721) B2941721
theorem B6282773 : Blo 1959435 6282773 := bbase (se 6 (by rfl) ⟨147252, by rfl⟩ : syracuseStep 6282773 = 294505) (by norm_num)
theorem B4188515 : Blo 1959435 4188515 := bstep (se 1 (by rfl) ⟨3141386, by rfl⟩ : syracuseStep 4188515 = 6282773) B6282773
theorem B11169373 : Blo 1959435 11169373 := bstep (se 3 (by rfl) ⟨2094257, by rfl⟩ : syracuseStep 11169373 = 4188515) B4188515
theorem B14892497 : Blo 1959435 14892497 := bstep (se 2 (by rfl) ⟨5584686, by rfl⟩ : syracuseStep 14892497 = 11169373) B11169373
theorem B9928331 : Blo 1959435 9928331 := bstep (se 1 (by rfl) ⟨7446248, by rfl⟩ : syracuseStep 9928331 = 14892497) B14892497
theorem B6618887 : Blo 1959435 6618887 := bstep (se 1 (by rfl) ⟨4964165, by rfl⟩ : syracuseStep 6618887 = 9928331) B9928331
theorem B4412591 : Blo 1959435 4412591 := bstep (se 1 (by rfl) ⟨3309443, by rfl⟩ : syracuseStep 4412591 = 6618887) B6618887
theorem B2941727 : Blo 1959435 2941727 := bstep (se 1 (by rfl) ⟨2206295, by rfl⟩ : syracuseStep 2941727 = 4412591) B4412591
theorem B1961151 : Blo 1959435 1961151 := bstep (se 1 (by rfl) ⟨1470863, by rfl⟩ : syracuseStep 1961151 = 2941727) B2941727
theorem B2941733 : Blo 1959435 2941733 := bbase (se 4 (by rfl) ⟨275787, by rfl⟩ : syracuseStep 2941733 = 551575) (by norm_num)
theorem B1961155 : Blo 1959435 1961155 := bstep (se 1 (by rfl) ⟨1470866, by rfl⟩ : syracuseStep 1961155 = 2941733) B2941733
theorem B2482093 : Blo 1959435 2482093 := bbase (se 3 (by rfl) ⟨465392, by rfl⟩ : syracuseStep 2482093 = 930785) (by norm_num)
theorem B3309457 : Blo 1959435 3309457 := bstep (se 2 (by rfl) ⟨1241046, by rfl⟩ : syracuseStep 3309457 = 2482093) B2482093
theorem B4412609 : Blo 1959435 4412609 := bstep (se 2 (by rfl) ⟨1654728, by rfl⟩ : syracuseStep 4412609 = 3309457) B3309457
theorem B2941739 : Blo 1959435 2941739 := bstep (se 1 (by rfl) ⟨2206304, by rfl⟩ : syracuseStep 2941739 = 4412609) B4412609
theorem B1961159 : Blo 1959435 1961159 := bstep (se 1 (by rfl) ⟨1470869, by rfl⟩ : syracuseStep 1961159 = 2941739) B2941739
theorem B2206309 : Blo 1959435 2206309 := bbase (se 4 (by rfl) ⟨206841, by rfl⟩ : syracuseStep 2206309 = 413683) (by norm_num)
theorem B2941745 : Blo 1959435 2941745 := bstep (se 2 (by rfl) ⟨1103154, by rfl⟩ : syracuseStep 2941745 = 2206309) B2206309
theorem B1961163 : Blo 1959435 1961163 := bstep (se 1 (by rfl) ⟨1470872, by rfl⟩ : syracuseStep 1961163 = 2941745) B2941745
theorem B3141413 : Blo 1959435 3141413 := bbase (se 4 (by rfl) ⟨294507, by rfl⟩ : syracuseStep 3141413 = 589015) (by norm_num)
theorem B2094275 : Blo 1959435 2094275 := bstep (se 1 (by rfl) ⟨1570706, by rfl⟩ : syracuseStep 2094275 = 3141413) B3141413
theorem B5584733 : Blo 1959435 5584733 := bstep (se 3 (by rfl) ⟨1047137, by rfl⟩ : syracuseStep 5584733 = 2094275) B2094275
theorem B3723155 : Blo 1959435 3723155 := bstep (se 1 (by rfl) ⟨2792366, by rfl⟩ : syracuseStep 3723155 = 5584733) B5584733
theorem B2482103 : Blo 1959435 2482103 := bstep (se 1 (by rfl) ⟨1861577, by rfl⟩ : syracuseStep 2482103 = 3723155) B3723155
theorem B6618941 : Blo 1959435 6618941 := bstep (se 3 (by rfl) ⟨1241051, by rfl⟩ : syracuseStep 6618941 = 2482103) B2482103
theorem B4412627 : Blo 1959435 4412627 := bstep (se 1 (by rfl) ⟨3309470, by rfl⟩ : syracuseStep 4412627 = 6618941) B6618941
theorem B2941751 : Blo 1959435 2941751 := bstep (se 1 (by rfl) ⟨2206313, by rfl⟩ : syracuseStep 2941751 = 4412627) B4412627
theorem B1961167 : Blo 1959435 1961167 := bstep (se 1 (by rfl) ⟨1470875, by rfl⟩ : syracuseStep 1961167 = 2941751) B2941751
theorem B2941757 : Blo 1959435 2941757 := bbase (se 3 (by rfl) ⟨551579, by rfl⟩ : syracuseStep 2941757 = 1103159) (by norm_num)
theorem B1961171 : Blo 1959435 1961171 := bstep (se 1 (by rfl) ⟨1470878, by rfl⟩ : syracuseStep 1961171 = 2941757) B2941757
theorem B4412645 : Blo 1959435 4412645 := bbase (se 4 (by rfl) ⟨413685, by rfl⟩ : syracuseStep 4412645 = 827371) (by norm_num)
theorem B2941763 : Blo 1959435 2941763 := bstep (se 1 (by rfl) ⟨2206322, by rfl⟩ : syracuseStep 2941763 = 4412645) B4412645
theorem B1961175 : Blo 1959435 1961175 := bstep (se 1 (by rfl) ⟨1470881, by rfl⟩ : syracuseStep 1961175 = 2941763) B2941763
theorem B4964237 : Blo 1959435 4964237 := bbase (se 3 (by rfl) ⟨930794, by rfl⟩ : syracuseStep 4964237 = 1861589) (by norm_num)
theorem B3309491 : Blo 1959435 3309491 := bstep (se 1 (by rfl) ⟨2482118, by rfl⟩ : syracuseStep 3309491 = 4964237) B4964237
theorem B2206327 : Blo 1959435 2206327 := bstep (se 1 (by rfl) ⟨1654745, by rfl⟩ : syracuseStep 2206327 = 3309491) B3309491
theorem B2941769 : Blo 1959435 2941769 := bstep (se 2 (by rfl) ⟨1103163, by rfl⟩ : syracuseStep 2941769 = 2206327) B2206327
theorem B1961179 : Blo 1959435 1961179 := bstep (se 1 (by rfl) ⟨1470884, by rfl⟩ : syracuseStep 1961179 = 2941769) B2941769
theorem B2792389 : Blo 1959435 2792389 := bbase (se 4 (by rfl) ⟨261786, by rfl⟩ : syracuseStep 2792389 = 523573) (by norm_num)
theorem B3723185 : Blo 1959435 3723185 := bstep (se 2 (by rfl) ⟨1396194, by rfl⟩ : syracuseStep 3723185 = 2792389) B2792389
theorem B9928493 : Blo 1959435 9928493 := bstep (se 3 (by rfl) ⟨1861592, by rfl⟩ : syracuseStep 9928493 = 3723185) B3723185
theorem B6618995 : Blo 1959435 6618995 := bstep (se 1 (by rfl) ⟨4964246, by rfl⟩ : syracuseStep 6618995 = 9928493) B9928493
theorem B4412663 : Blo 1959435 4412663 := bstep (se 1 (by rfl) ⟨3309497, by rfl⟩ : syracuseStep 4412663 = 6618995) B6618995
theorem B2941775 : Blo 1959435 2941775 := bstep (se 1 (by rfl) ⟨2206331, by rfl⟩ : syracuseStep 2941775 = 4412663) B4412663
theorem B1961183 : Blo 1959435 1961183 := bstep (se 1 (by rfl) ⟨1470887, by rfl⟩ : syracuseStep 1961183 = 2941775) B2941775
theorem B2941781 : Blo 1959435 2941781 := bbase (se 9 (by rfl) ⟨8618, by rfl⟩ : syracuseStep 2941781 = 17237) (by norm_num)
theorem B1961187 : Blo 1959435 1961187 := bstep (se 1 (by rfl) ⟨1470890, by rfl⟩ : syracuseStep 1961187 = 2941781) B2941781
theorem B3534133 : Blo 1959435 3534133 := bbase (se 5 (by rfl) ⟨165662, by rfl⟩ : syracuseStep 3534133 = 331325) (by norm_num)
theorem B4712177 : Blo 1959435 4712177 := bstep (se 2 (by rfl) ⟨1767066, by rfl⟩ : syracuseStep 4712177 = 3534133) B3534133
theorem B3141451 : Blo 1959435 3141451 := bstep (se 1 (by rfl) ⟨2356088, by rfl⟩ : syracuseStep 3141451 = 4712177) B4712177
theorem B4188601 : Blo 1959435 4188601 := bstep (se 2 (by rfl) ⟨1570725, by rfl⟩ : syracuseStep 4188601 = 3141451) B3141451
theorem B5584801 : Blo 1959435 5584801 := bstep (se 2 (by rfl) ⟨2094300, by rfl⟩ : syracuseStep 5584801 = 4188601) B4188601
theorem B7446401 : Blo 1959435 7446401 := bstep (se 2 (by rfl) ⟨2792400, by rfl⟩ : syracuseStep 7446401 = 5584801) B5584801
theorem B4964267 : Blo 1959435 4964267 := bstep (se 1 (by rfl) ⟨3723200, by rfl⟩ : syracuseStep 4964267 = 7446401) B7446401
theorem B3309511 : Blo 1959435 3309511 := bstep (se 1 (by rfl) ⟨2482133, by rfl⟩ : syracuseStep 3309511 = 4964267) B4964267
theorem B4412681 : Blo 1959435 4412681 := bstep (se 2 (by rfl) ⟨1654755, by rfl⟩ : syracuseStep 4412681 = 3309511) B3309511
theorem B2941787 : Blo 1959435 2941787 := bstep (se 1 (by rfl) ⟨2206340, by rfl⟩ : syracuseStep 2941787 = 4412681) B4412681
theorem B1961191 : Blo 1959435 1961191 := bstep (se 1 (by rfl) ⟨1470893, by rfl⟩ : syracuseStep 1961191 = 2941787) B2941787
theorem B2206345 : Blo 1959435 2206345 := bbase (se 2 (by rfl) ⟨827379, by rfl⟩ : syracuseStep 2206345 = 1654759) (by norm_num)
theorem B2941793 : Blo 1959435 2941793 := bstep (se 2 (by rfl) ⟨1103172, by rfl⟩ : syracuseStep 2941793 = 2206345) B2206345
theorem B1961195 : Blo 1959435 1961195 := bstep (se 1 (by rfl) ⟨1470896, by rfl⟩ : syracuseStep 1961195 = 2941793) B2941793
theorem B15096053 : Blo 1959435 15096053 := bbase (se 5 (by rfl) ⟨707627, by rfl⟩ : syracuseStep 15096053 = 1415255) (by norm_num)
theorem B10064035 : Blo 1959435 10064035 := bstep (se 1 (by rfl) ⟨7548026, by rfl⟩ : syracuseStep 10064035 = 15096053) B15096053
theorem B13418713 : Blo 1959435 13418713 := bstep (se 2 (by rfl) ⟨5032017, by rfl⟩ : syracuseStep 13418713 = 10064035) B10064035
theorem B17891617 : Blo 1959435 17891617 := bstep (se 2 (by rfl) ⟨6709356, by rfl⟩ : syracuseStep 17891617 = 13418713) B13418713
theorem B23855489 : Blo 1959435 23855489 := bstep (se 2 (by rfl) ⟨8945808, by rfl⟩ : syracuseStep 23855489 = 17891617) B17891617
theorem B15903659 : Blo 1959435 15903659 := bstep (se 1 (by rfl) ⟨11927744, by rfl⟩ : syracuseStep 15903659 = 23855489) B23855489
theorem B42409757 : Blo 1959435 42409757 := bstep (se 3 (by rfl) ⟨7951829, by rfl⟩ : syracuseStep 42409757 = 15903659) B15903659
theorem B28273171 : Blo 1959435 28273171 := bstep (se 1 (by rfl) ⟨21204878, by rfl⟩ : syracuseStep 28273171 = 42409757) B42409757
theorem B37697561 : Blo 1959435 37697561 := bstep (se 2 (by rfl) ⟨14136585, by rfl⟩ : syracuseStep 37697561 = 28273171) B28273171
theorem B25131707 : Blo 1959435 25131707 := bstep (se 1 (by rfl) ⟨18848780, by rfl⟩ : syracuseStep 25131707 = 37697561) B37697561
theorem B16754471 : Blo 1959435 16754471 := bstep (se 1 (by rfl) ⟨12565853, by rfl⟩ : syracuseStep 16754471 = 25131707) B25131707
theorem B11169647 : Blo 1959435 11169647 := bstep (se 1 (by rfl) ⟨8377235, by rfl⟩ : syracuseStep 11169647 = 16754471) B16754471
theorem B7446431 : Blo 1959435 7446431 := bstep (se 1 (by rfl) ⟨5584823, by rfl⟩ : syracuseStep 7446431 = 11169647) B11169647
theorem B4964287 : Blo 1959435 4964287 := bstep (se 1 (by rfl) ⟨3723215, by rfl⟩ : syracuseStep 4964287 = 7446431) B7446431
theorem B6619049 : Blo 1959435 6619049 := bstep (se 2 (by rfl) ⟨2482143, by rfl⟩ : syracuseStep 6619049 = 4964287) B4964287
theorem B4412699 : Blo 1959435 4412699 := bstep (se 1 (by rfl) ⟨3309524, by rfl⟩ : syracuseStep 4412699 = 6619049) B6619049
theorem B2941799 : Blo 1959435 2941799 := bstep (se 1 (by rfl) ⟨2206349, by rfl⟩ : syracuseStep 2941799 = 4412699) B4412699
theorem B1961199 : Blo 1959435 1961199 := bstep (se 1 (by rfl) ⟨1470899, by rfl⟩ : syracuseStep 1961199 = 2941799) B2941799
theorem B2941805 : Blo 1959435 2941805 := bbase (se 3 (by rfl) ⟨551588, by rfl⟩ : syracuseStep 2941805 = 1103177) (by norm_num)
theorem B1961203 : Blo 1959435 1961203 := bstep (se 1 (by rfl) ⟨1470902, by rfl⟩ : syracuseStep 1961203 = 2941805) B2941805
theorem B4412717 : Blo 1959435 4412717 := bbase (se 3 (by rfl) ⟨827384, by rfl⟩ : syracuseStep 4412717 = 1654769) (by norm_num)
theorem B2941811 : Blo 1959435 2941811 := bstep (se 1 (by rfl) ⟨2206358, by rfl⟩ : syracuseStep 2941811 = 4412717) B4412717
theorem B1961207 : Blo 1959435 1961207 := bstep (se 1 (by rfl) ⟨1470905, by rfl⟩ : syracuseStep 1961207 = 2941811) B2941811
theorem B3975941 : Blo 1959435 3975941 := bbase (se 4 (by rfl) ⟨372744, by rfl⟩ : syracuseStep 3975941 = 745489) (by norm_num)
theorem B2650627 : Blo 1959435 2650627 := bstep (se 1 (by rfl) ⟨1987970, by rfl⟩ : syracuseStep 2650627 = 3975941) B3975941
theorem B14136677 : Blo 1959435 14136677 := bstep (se 4 (by rfl) ⟨1325313, by rfl⟩ : syracuseStep 14136677 = 2650627) B2650627
theorem B9424451 : Blo 1959435 9424451 := bstep (se 1 (by rfl) ⟨7068338, by rfl⟩ : syracuseStep 9424451 = 14136677) B14136677
theorem B6282967 : Blo 1959435 6282967 := bstep (se 1 (by rfl) ⟨4712225, by rfl⟩ : syracuseStep 6282967 = 9424451) B9424451
theorem B8377289 : Blo 1959435 8377289 := bstep (se 2 (by rfl) ⟨3141483, by rfl⟩ : syracuseStep 8377289 = 6282967) B6282967
theorem B5584859 : Blo 1959435 5584859 := bstep (se 1 (by rfl) ⟨4188644, by rfl⟩ : syracuseStep 5584859 = 8377289) B8377289
theorem B3723239 : Blo 1959435 3723239 := bstep (se 1 (by rfl) ⟨2792429, by rfl⟩ : syracuseStep 3723239 = 5584859) B5584859
theorem B2482159 : Blo 1959435 2482159 := bstep (se 1 (by rfl) ⟨1861619, by rfl⟩ : syracuseStep 2482159 = 3723239) B3723239
theorem B3309545 : Blo 1959435 3309545 := bstep (se 2 (by rfl) ⟨1241079, by rfl⟩ : syracuseStep 3309545 = 2482159) B2482159
theorem B2206363 : Blo 1959435 2206363 := bstep (se 1 (by rfl) ⟨1654772, by rfl⟩ : syracuseStep 2206363 = 3309545) B3309545
theorem B2941817 : Blo 1959435 2941817 := bstep (se 2 (by rfl) ⟨1103181, by rfl⟩ : syracuseStep 2941817 = 2206363) B2206363
theorem B1961211 : Blo 1959435 1961211 := bstep (se 1 (by rfl) ⟨1470908, by rfl⟩ : syracuseStep 1961211 = 2941817) B2941817
theorem B17891765 : Blo 1959435 17891765 := bbase (se 5 (by rfl) ⟨838676, by rfl⟩ : syracuseStep 17891765 = 1677353) (by norm_num)
theorem B11927843 : Blo 1959435 11927843 := bstep (se 1 (by rfl) ⟨8945882, by rfl⟩ : syracuseStep 11927843 = 17891765) B17891765
theorem B7951895 : Blo 1959435 7951895 := bstep (se 1 (by rfl) ⟨5963921, by rfl⟩ : syracuseStep 7951895 = 11927843) B11927843
theorem B5301263 : Blo 1959435 5301263 := bstep (se 1 (by rfl) ⟨3975947, by rfl⟩ : syracuseStep 5301263 = 7951895) B7951895
theorem B3534175 : Blo 1959435 3534175 := bstep (se 1 (by rfl) ⟨2650631, by rfl⟩ : syracuseStep 3534175 = 5301263) B5301263
theorem B18848933 : Blo 1959435 18848933 := bstep (se 4 (by rfl) ⟨1767087, by rfl⟩ : syracuseStep 18848933 = 3534175) B3534175
theorem B12565955 : Blo 1959435 12565955 := bstep (se 1 (by rfl) ⟨9424466, by rfl⟩ : syracuseStep 12565955 = 18848933) B18848933
theorem B33509213 : Blo 1959435 33509213 := bstep (se 3 (by rfl) ⟨6282977, by rfl⟩ : syracuseStep 33509213 = 12565955) B12565955
theorem B22339475 : Blo 1959435 22339475 := bstep (se 1 (by rfl) ⟨16754606, by rfl⟩ : syracuseStep 22339475 = 33509213) B33509213
theorem B14892983 : Blo 1959435 14892983 := bstep (se 1 (by rfl) ⟨11169737, by rfl⟩ : syracuseStep 14892983 = 22339475) B22339475
theorem B9928655 : Blo 1959435 9928655 := bstep (se 1 (by rfl) ⟨7446491, by rfl⟩ : syracuseStep 9928655 = 14892983) B14892983
theorem B6619103 : Blo 1959435 6619103 := bstep (se 1 (by rfl) ⟨4964327, by rfl⟩ : syracuseStep 6619103 = 9928655) B9928655
theorem B4412735 : Blo 1959435 4412735 := bstep (se 1 (by rfl) ⟨3309551, by rfl⟩ : syracuseStep 4412735 = 6619103) B6619103
theorem B2941823 : Blo 1959435 2941823 := bstep (se 1 (by rfl) ⟨2206367, by rfl⟩ : syracuseStep 2941823 = 4412735) B4412735
theorem B1961215 : Blo 1959435 1961215 := bstep (se 1 (by rfl) ⟨1470911, by rfl⟩ : syracuseStep 1961215 = 2941823) B2941823
theorem B2941829 : Blo 1959435 2941829 := bbase (se 4 (by rfl) ⟨275796, by rfl⟩ : syracuseStep 2941829 = 551593) (by norm_num)
theorem B1961219 : Blo 1959435 1961219 := bstep (se 1 (by rfl) ⟨1470914, by rfl⟩ : syracuseStep 1961219 = 2941829) B2941829
theorem B3309565 : Blo 1959435 3309565 := bbase (se 3 (by rfl) ⟨620543, by rfl⟩ : syracuseStep 3309565 = 1241087) (by norm_num)
theorem B4412753 : Blo 1959435 4412753 := bstep (se 2 (by rfl) ⟨1654782, by rfl⟩ : syracuseStep 4412753 = 3309565) B3309565
theorem B2941835 : Blo 1959435 2941835 := bstep (se 1 (by rfl) ⟨2206376, by rfl⟩ : syracuseStep 2941835 = 4412753) B4412753
theorem B1961223 : Blo 1959435 1961223 := bstep (se 1 (by rfl) ⟨1470917, by rfl⟩ : syracuseStep 1961223 = 2941835) B2941835
theorem B2206381 : Blo 1959435 2206381 := bbase (se 3 (by rfl) ⟨413696, by rfl⟩ : syracuseStep 2206381 = 827393) (by norm_num)
theorem B2941841 : Blo 1959435 2941841 := bstep (se 2 (by rfl) ⟨1103190, by rfl⟩ : syracuseStep 2941841 = 2206381) B2206381
theorem B1961227 : Blo 1959435 1961227 := bstep (se 1 (by rfl) ⟨1470920, by rfl⟩ : syracuseStep 1961227 = 2941841) B2941841
theorem B6619157 : Blo 1959435 6619157 := bbase (se 6 (by rfl) ⟨155136, by rfl⟩ : syracuseStep 6619157 = 310273) (by norm_num)
theorem B4412771 : Blo 1959435 4412771 := bstep (se 1 (by rfl) ⟨3309578, by rfl⟩ : syracuseStep 4412771 = 6619157) B6619157
theorem B2941847 : Blo 1959435 2941847 := bstep (se 1 (by rfl) ⟨2206385, by rfl⟩ : syracuseStep 2941847 = 4412771) B4412771
theorem B1961231 : Blo 1959435 1961231 := bstep (se 1 (by rfl) ⟨1470923, by rfl⟩ : syracuseStep 1961231 = 2941847) B2941847
theorem B2941853 : Blo 1959435 2941853 := bbase (se 3 (by rfl) ⟨551597, by rfl⟩ : syracuseStep 2941853 = 1103195) (by norm_num)
theorem B1961235 : Blo 1959435 1961235 := bstep (se 1 (by rfl) ⟨1470926, by rfl⟩ : syracuseStep 1961235 = 2941853) B2941853
theorem B4412789 : Blo 1959435 4412789 := bbase (se 5 (by rfl) ⟨206849, by rfl⟩ : syracuseStep 4412789 = 413699) (by norm_num)
theorem B2941859 : Blo 1959435 2941859 := bstep (se 1 (by rfl) ⟨2206394, by rfl⟩ : syracuseStep 2941859 = 4412789) B4412789
theorem B1961239 : Blo 1959435 1961239 := bstep (se 1 (by rfl) ⟨1470929, by rfl⟩ : syracuseStep 1961239 = 2941859) B2941859
theorem B16983445 : Blo 1959435 16983445 := bbase (se 6 (by rfl) ⟨398049, by rfl⟩ : syracuseStep 16983445 = 796099) (by norm_num)
theorem B22644593 : Blo 1959435 22644593 := bstep (se 2 (by rfl) ⟨8491722, by rfl⟩ : syracuseStep 22644593 = 16983445) B16983445
theorem B15096395 : Blo 1959435 15096395 := bstep (se 1 (by rfl) ⟨11322296, by rfl⟩ : syracuseStep 15096395 = 22644593) B22644593
theorem B10064263 : Blo 1959435 10064263 := bstep (se 1 (by rfl) ⟨7548197, by rfl⟩ : syracuseStep 10064263 = 15096395) B15096395
theorem B13419017 : Blo 1959435 13419017 := bstep (se 2 (by rfl) ⟨5032131, by rfl⟩ : syracuseStep 13419017 = 10064263) B10064263
theorem B8946011 : Blo 1959435 8946011 := bstep (se 1 (by rfl) ⟨6709508, by rfl⟩ : syracuseStep 8946011 = 13419017) B13419017
theorem B23856029 : Blo 1959435 23856029 := bstep (se 3 (by rfl) ⟨4473005, by rfl⟩ : syracuseStep 23856029 = 8946011) B8946011
theorem B15904019 : Blo 1959435 15904019 := bstep (se 1 (by rfl) ⟨11928014, by rfl⟩ : syracuseStep 15904019 = 23856029) B23856029
theorem B10602679 : Blo 1959435 10602679 := bstep (se 1 (by rfl) ⟨7952009, by rfl⟩ : syracuseStep 10602679 = 15904019) B15904019
theorem B14136905 : Blo 1959435 14136905 := bstep (se 2 (by rfl) ⟨5301339, by rfl⟩ : syracuseStep 14136905 = 10602679) B10602679
theorem B9424603 : Blo 1959435 9424603 := bstep (se 1 (by rfl) ⟨7068452, by rfl⟩ : syracuseStep 9424603 = 14136905) B14136905
theorem B12566137 : Blo 1959435 12566137 := bstep (se 2 (by rfl) ⟨4712301, by rfl⟩ : syracuseStep 12566137 = 9424603) B9424603
theorem B16754849 : Blo 1959435 16754849 := bstep (se 2 (by rfl) ⟨6283068, by rfl⟩ : syracuseStep 16754849 = 12566137) B12566137
theorem B11169899 : Blo 1959435 11169899 := bstep (se 1 (by rfl) ⟨8377424, by rfl⟩ : syracuseStep 11169899 = 16754849) B16754849
theorem B7446599 : Blo 1959435 7446599 := bstep (se 1 (by rfl) ⟨5584949, by rfl⟩ : syracuseStep 7446599 = 11169899) B11169899
theorem B4964399 : Blo 1959435 4964399 := bstep (se 1 (by rfl) ⟨3723299, by rfl⟩ : syracuseStep 4964399 = 7446599) B7446599
theorem B3309599 : Blo 1959435 3309599 := bstep (se 1 (by rfl) ⟨2482199, by rfl⟩ : syracuseStep 3309599 = 4964399) B4964399
theorem B2206399 : Blo 1959435 2206399 := bstep (se 1 (by rfl) ⟨1654799, by rfl⟩ : syracuseStep 2206399 = 3309599) B3309599
theorem B2941865 : Blo 1959435 2941865 := bstep (se 2 (by rfl) ⟨1103199, by rfl⟩ : syracuseStep 2941865 = 2206399) B2206399
theorem B1961243 : Blo 1959435 1961243 := bstep (se 1 (by rfl) ⟨1470932, by rfl⟩ : syracuseStep 1961243 = 2941865) B2941865
theorem B7446613 : Blo 1959435 7446613 := bbase (se 8 (by rfl) ⟨43632, by rfl⟩ : syracuseStep 7446613 = 87265) (by norm_num)
theorem B9928817 : Blo 1959435 9928817 := bstep (se 2 (by rfl) ⟨3723306, by rfl⟩ : syracuseStep 9928817 = 7446613) B7446613
theorem B6619211 : Blo 1959435 6619211 := bstep (se 1 (by rfl) ⟨4964408, by rfl⟩ : syracuseStep 6619211 = 9928817) B9928817
theorem B4412807 : Blo 1959435 4412807 := bstep (se 1 (by rfl) ⟨3309605, by rfl⟩ : syracuseStep 4412807 = 6619211) B6619211
theorem B2941871 : Blo 1959435 2941871 := bstep (se 1 (by rfl) ⟨2206403, by rfl⟩ : syracuseStep 2941871 = 4412807) B4412807
theorem B1961247 : Blo 1959435 1961247 := bstep (se 1 (by rfl) ⟨1470935, by rfl⟩ : syracuseStep 1961247 = 2941871) B2941871
theorem B2941877 : Blo 1959435 2941877 := bbase (se 5 (by rfl) ⟨137900, by rfl⟩ : syracuseStep 2941877 = 275801) (by norm_num)
theorem B1961251 : Blo 1959435 1961251 := bstep (se 1 (by rfl) ⟨1470938, by rfl⟩ : syracuseStep 1961251 = 2941877) B2941877
theorem B4964429 : Blo 1959435 4964429 := bbase (se 3 (by rfl) ⟨930830, by rfl⟩ : syracuseStep 4964429 = 1861661) (by norm_num)
theorem B3309619 : Blo 1959435 3309619 := bstep (se 1 (by rfl) ⟨2482214, by rfl⟩ : syracuseStep 3309619 = 4964429) B4964429
theorem B4412825 : Blo 1959435 4412825 := bstep (se 2 (by rfl) ⟨1654809, by rfl⟩ : syracuseStep 4412825 = 3309619) B3309619
theorem B2941883 : Blo 1959435 2941883 := bstep (se 1 (by rfl) ⟨2206412, by rfl⟩ : syracuseStep 2941883 = 4412825) B4412825
theorem B1961255 : Blo 1959435 1961255 := bstep (se 1 (by rfl) ⟨1470941, by rfl⟩ : syracuseStep 1961255 = 2941883) B2941883
theorem B2206417 : Blo 1959435 2206417 := bbase (se 2 (by rfl) ⟨827406, by rfl⟩ : syracuseStep 2206417 = 1654813) (by norm_num)
theorem B2941889 : Blo 1959435 2941889 := bstep (se 2 (by rfl) ⟨1103208, by rfl⟩ : syracuseStep 2941889 = 2206417) B2206417
theorem B1961259 : Blo 1959435 1961259 := bstep (se 1 (by rfl) ⟨1470944, by rfl⟩ : syracuseStep 1961259 = 2941889) B2941889
theorem B4473053 : Blo 1959435 4473053 := bbase (se 3 (by rfl) ⟨838697, by rfl⟩ : syracuseStep 4473053 = 1677395) (by norm_num)
theorem B2982035 : Blo 1959435 2982035 := bstep (se 1 (by rfl) ⟨2236526, by rfl⟩ : syracuseStep 2982035 = 4473053) B4473053
theorem B7952093 : Blo 1959435 7952093 := bstep (se 3 (by rfl) ⟨1491017, by rfl⟩ : syracuseStep 7952093 = 2982035) B2982035
theorem B5301395 : Blo 1959435 5301395 := bstep (se 1 (by rfl) ⟨3976046, by rfl⟩ : syracuseStep 5301395 = 7952093) B7952093
theorem B3534263 : Blo 1959435 3534263 := bstep (se 1 (by rfl) ⟨2650697, by rfl⟩ : syracuseStep 3534263 = 5301395) B5301395
theorem B2356175 : Blo 1959435 2356175 := bstep (se 1 (by rfl) ⟨1767131, by rfl⟩ : syracuseStep 2356175 = 3534263) B3534263
theorem B6283133 : Blo 1959435 6283133 := bstep (se 3 (by rfl) ⟨1178087, by rfl⟩ : syracuseStep 6283133 = 2356175) B2356175
theorem B4188755 : Blo 1959435 4188755 := bstep (se 1 (by rfl) ⟨3141566, by rfl⟩ : syracuseStep 4188755 = 6283133) B6283133
theorem B2792503 : Blo 1959435 2792503 := bstep (se 1 (by rfl) ⟨2094377, by rfl⟩ : syracuseStep 2792503 = 4188755) B4188755
theorem B3723337 : Blo 1959435 3723337 := bstep (se 2 (by rfl) ⟨1396251, by rfl⟩ : syracuseStep 3723337 = 2792503) B2792503
theorem B4964449 : Blo 1959435 4964449 := bstep (se 2 (by rfl) ⟨1861668, by rfl⟩ : syracuseStep 4964449 = 3723337) B3723337
theorem B6619265 : Blo 1959435 6619265 := bstep (se 2 (by rfl) ⟨2482224, by rfl⟩ : syracuseStep 6619265 = 4964449) B4964449
theorem B4412843 : Blo 1959435 4412843 := bstep (se 1 (by rfl) ⟨3309632, by rfl⟩ : syracuseStep 4412843 = 6619265) B6619265
theorem B2941895 : Blo 1959435 2941895 := bstep (se 1 (by rfl) ⟨2206421, by rfl⟩ : syracuseStep 2941895 = 4412843) B4412843
theorem B1961263 : Blo 1959435 1961263 := bstep (se 1 (by rfl) ⟨1470947, by rfl⟩ : syracuseStep 1961263 = 2941895) B2941895
theorem B2941901 : Blo 1959435 2941901 := bbase (se 3 (by rfl) ⟨551606, by rfl⟩ : syracuseStep 2941901 = 1103213) (by norm_num)
theorem B1961267 : Blo 1959435 1961267 := bstep (se 1 (by rfl) ⟨1470950, by rfl⟩ : syracuseStep 1961267 = 2941901) B2941901
theorem B4412861 : Blo 1959435 4412861 := bbase (se 3 (by rfl) ⟨827411, by rfl⟩ : syracuseStep 4412861 = 1654823) (by norm_num)
theorem B2941907 : Blo 1959435 2941907 := bstep (se 1 (by rfl) ⟨2206430, by rfl⟩ : syracuseStep 2941907 = 4412861) B4412861
theorem B1961271 : Blo 1959435 1961271 := bstep (se 1 (by rfl) ⟨1470953, by rfl⟩ : syracuseStep 1961271 = 2941907) B2941907
theorem B3309653 : Blo 1959435 3309653 := bbase (se 8 (by rfl) ⟨19392, by rfl⟩ : syracuseStep 3309653 = 38785) (by norm_num)
theorem B2206435 : Blo 1959435 2206435 := bstep (se 1 (by rfl) ⟨1654826, by rfl⟩ : syracuseStep 2206435 = 3309653) B3309653
theorem B2941913 : Blo 1959435 2941913 := bstep (se 2 (by rfl) ⟨1103217, by rfl⟩ : syracuseStep 2941913 = 2206435) B2206435
theorem B1961275 : Blo 1959435 1961275 := bstep (se 1 (by rfl) ⟨1470956, by rfl⟩ : syracuseStep 1961275 = 2941913) B2941913
theorem B15904309 : Blo 1959435 15904309 := bbase (se 5 (by rfl) ⟨745514, by rfl⟩ : syracuseStep 15904309 = 1491029) (by norm_num)
theorem B21205745 : Blo 1959435 21205745 := bstep (se 2 (by rfl) ⟨7952154, by rfl⟩ : syracuseStep 21205745 = 15904309) B15904309
theorem B14137163 : Blo 1959435 14137163 := bstep (se 1 (by rfl) ⟨10602872, by rfl⟩ : syracuseStep 14137163 = 21205745) B21205745
theorem B9424775 : Blo 1959435 9424775 := bstep (se 1 (by rfl) ⟨7068581, by rfl⟩ : syracuseStep 9424775 = 14137163) B14137163
theorem B6283183 : Blo 1959435 6283183 := bstep (se 1 (by rfl) ⟨4712387, by rfl⟩ : syracuseStep 6283183 = 9424775) B9424775
theorem B8377577 : Blo 1959435 8377577 := bstep (se 2 (by rfl) ⟨3141591, by rfl⟩ : syracuseStep 8377577 = 6283183) B6283183
theorem B5585051 : Blo 1959435 5585051 := bstep (se 1 (by rfl) ⟨4188788, by rfl⟩ : syracuseStep 5585051 = 8377577) B8377577
theorem B14893469 : Blo 1959435 14893469 := bstep (se 3 (by rfl) ⟨2792525, by rfl⟩ : syracuseStep 14893469 = 5585051) B5585051
theorem B9928979 : Blo 1959435 9928979 := bstep (se 1 (by rfl) ⟨7446734, by rfl⟩ : syracuseStep 9928979 = 14893469) B14893469
theorem B6619319 : Blo 1959435 6619319 := bstep (se 1 (by rfl) ⟨4964489, by rfl⟩ : syracuseStep 6619319 = 9928979) B9928979
theorem B4412879 : Blo 1959435 4412879 := bstep (se 1 (by rfl) ⟨3309659, by rfl⟩ : syracuseStep 4412879 = 6619319) B6619319
theorem B2941919 : Blo 1959435 2941919 := bstep (se 1 (by rfl) ⟨2206439, by rfl⟩ : syracuseStep 2941919 = 4412879) B4412879
theorem B1961279 : Blo 1959435 1961279 := bstep (se 1 (by rfl) ⟨1470959, by rfl⟩ : syracuseStep 1961279 = 2941919) B2941919
theorem B2941925 : Blo 1959435 2941925 := bbase (se 4 (by rfl) ⟨275805, by rfl⟩ : syracuseStep 2941925 = 551611) (by norm_num)
theorem B1961283 : Blo 1959435 1961283 := bstep (se 1 (by rfl) ⟨1470962, by rfl⟩ : syracuseStep 1961283 = 2941925) B2941925
theorem B3141605 : Blo 1959435 3141605 := bbase (se 4 (by rfl) ⟨294525, by rfl⟩ : syracuseStep 3141605 = 589051) (by norm_num)
theorem B8377613 : Blo 1959435 8377613 := bstep (se 3 (by rfl) ⟨1570802, by rfl⟩ : syracuseStep 8377613 = 3141605) B3141605
theorem B5585075 : Blo 1959435 5585075 := bstep (se 1 (by rfl) ⟨4188806, by rfl⟩ : syracuseStep 5585075 = 8377613) B8377613
theorem B3723383 : Blo 1959435 3723383 := bstep (se 1 (by rfl) ⟨2792537, by rfl⟩ : syracuseStep 3723383 = 5585075) B5585075
theorem B2482255 : Blo 1959435 2482255 := bstep (se 1 (by rfl) ⟨1861691, by rfl⟩ : syracuseStep 2482255 = 3723383) B3723383
theorem B3309673 : Blo 1959435 3309673 := bstep (se 2 (by rfl) ⟨1241127, by rfl⟩ : syracuseStep 3309673 = 2482255) B2482255
theorem B4412897 : Blo 1959435 4412897 := bstep (se 2 (by rfl) ⟨1654836, by rfl⟩ : syracuseStep 4412897 = 3309673) B3309673
theorem B2941931 : Blo 1959435 2941931 := bstep (se 1 (by rfl) ⟨2206448, by rfl⟩ : syracuseStep 2941931 = 4412897) B4412897
theorem B1961287 : Blo 1959435 1961287 := bstep (se 1 (by rfl) ⟨1470965, by rfl⟩ : syracuseStep 1961287 = 2941931) B2941931
theorem B2206453 : Blo 1959435 2206453 := bbase (se 5 (by rfl) ⟨103427, by rfl⟩ : syracuseStep 2206453 = 206855) (by norm_num)
theorem B2941937 : Blo 1959435 2941937 := bstep (se 2 (by rfl) ⟨1103226, by rfl⟩ : syracuseStep 2941937 = 2206453) B2206453
theorem B1961291 : Blo 1959435 1961291 := bstep (se 1 (by rfl) ⟨1470968, by rfl⟩ : syracuseStep 1961291 = 2941937) B2941937
theorem B2482265 : Blo 1959435 2482265 := bbase (se 2 (by rfl) ⟨930849, by rfl⟩ : syracuseStep 2482265 = 1861699) (by norm_num)
theorem B6619373 : Blo 1959435 6619373 := bstep (se 3 (by rfl) ⟨1241132, by rfl⟩ : syracuseStep 6619373 = 2482265) B2482265
theorem B4412915 : Blo 1959435 4412915 := bstep (se 1 (by rfl) ⟨3309686, by rfl⟩ : syracuseStep 4412915 = 6619373) B6619373
theorem B2941943 : Blo 1959435 2941943 := bstep (se 1 (by rfl) ⟨2206457, by rfl⟩ : syracuseStep 2941943 = 4412915) B4412915
theorem B1961295 : Blo 1959435 1961295 := bstep (se 1 (by rfl) ⟨1470971, by rfl⟩ : syracuseStep 1961295 = 2941943) B2941943
theorem B2941949 : Blo 1959435 2941949 := bbase (se 3 (by rfl) ⟨551615, by rfl⟩ : syracuseStep 2941949 = 1103231) (by norm_num)
theorem B1961299 : Blo 1959435 1961299 := bstep (se 1 (by rfl) ⟨1470974, by rfl⟩ : syracuseStep 1961299 = 2941949) B2941949
theorem B4412933 : Blo 1959435 4412933 := bbase (se 4 (by rfl) ⟨413712, by rfl⟩ : syracuseStep 4412933 = 827425) (by norm_num)
theorem B2941955 : Blo 1959435 2941955 := bstep (se 1 (by rfl) ⟨2206466, by rfl⟩ : syracuseStep 2941955 = 4412933) B4412933
theorem B1961303 : Blo 1959435 1961303 := bstep (se 1 (by rfl) ⟨1470977, by rfl⟩ : syracuseStep 1961303 = 2941955) B2941955
theorem B3723421 : Blo 1959435 3723421 := bbase (se 3 (by rfl) ⟨698141, by rfl⟩ : syracuseStep 3723421 = 1396283) (by norm_num)
theorem B4964561 : Blo 1959435 4964561 := bstep (se 2 (by rfl) ⟨1861710, by rfl⟩ : syracuseStep 4964561 = 3723421) B3723421
theorem B3309707 : Blo 1959435 3309707 := bstep (se 1 (by rfl) ⟨2482280, by rfl⟩ : syracuseStep 3309707 = 4964561) B4964561
theorem B2206471 : Blo 1959435 2206471 := bstep (se 1 (by rfl) ⟨1654853, by rfl⟩ : syracuseStep 2206471 = 3309707) B3309707
theorem B2941961 : Blo 1959435 2941961 := bstep (se 2 (by rfl) ⟨1103235, by rfl⟩ : syracuseStep 2941961 = 2206471) B2206471
theorem B1961307 : Blo 1959435 1961307 := bstep (se 1 (by rfl) ⟨1470980, by rfl⟩ : syracuseStep 1961307 = 2941961) B2941961
theorem B9929141 : Blo 1959435 9929141 := bbase (se 5 (by rfl) ⟨465428, by rfl⟩ : syracuseStep 9929141 = 930857) (by norm_num)
theorem B6619427 : Blo 1959435 6619427 := bstep (se 1 (by rfl) ⟨4964570, by rfl⟩ : syracuseStep 6619427 = 9929141) B9929141
theorem B4412951 : Blo 1959435 4412951 := bstep (se 1 (by rfl) ⟨3309713, by rfl⟩ : syracuseStep 4412951 = 6619427) B6619427
theorem B2941967 : Blo 1959435 2941967 := bstep (se 1 (by rfl) ⟨2206475, by rfl⟩ : syracuseStep 2941967 = 4412951) B4412951
theorem B1961311 : Blo 1959435 1961311 := bstep (se 1 (by rfl) ⟨1470983, by rfl⟩ : syracuseStep 1961311 = 2941967) B2941967
theorem B2941973 : Blo 1959435 2941973 := bbase (se 6 (by rfl) ⟨68952, by rfl⟩ : syracuseStep 2941973 = 137905) (by norm_num)
theorem B1961315 : Blo 1959435 1961315 := bstep (se 1 (by rfl) ⟨1470986, by rfl⟩ : syracuseStep 1961315 = 2941973) B2941973
theorem B5373877 : Blo 1959435 5373877 := bbase (se 5 (by rfl) ⟨251900, by rfl⟩ : syracuseStep 5373877 = 503801) (by norm_num)
theorem B7165169 : Blo 1959435 7165169 := bstep (se 2 (by rfl) ⟨2686938, by rfl⟩ : syracuseStep 7165169 = 5373877) B5373877
theorem B4776779 : Blo 1959435 4776779 := bstep (se 1 (by rfl) ⟨3582584, by rfl⟩ : syracuseStep 4776779 = 7165169) B7165169
theorem B3184519 : Blo 1959435 3184519 := bstep (se 1 (by rfl) ⟨2388389, by rfl⟩ : syracuseStep 3184519 = 4776779) B4776779
theorem B4246025 : Blo 1959435 4246025 := bstep (se 2 (by rfl) ⟨1592259, by rfl⟩ : syracuseStep 4246025 = 3184519) B3184519
theorem B45290933 : Blo 1959435 45290933 := bstep (se 5 (by rfl) ⟨2123012, by rfl⟩ : syracuseStep 45290933 = 4246025) B4246025
theorem B30193955 : Blo 1959435 30193955 := bstep (se 1 (by rfl) ⟨22645466, by rfl⟩ : syracuseStep 30193955 = 45290933) B45290933
theorem B20129303 : Blo 1959435 20129303 := bstep (se 1 (by rfl) ⟨15096977, by rfl⟩ : syracuseStep 20129303 = 30193955) B30193955
theorem B13419535 : Blo 1959435 13419535 := bstep (se 1 (by rfl) ⟨10064651, by rfl⟩ : syracuseStep 13419535 = 20129303) B20129303
theorem B17892713 : Blo 1959435 17892713 := bstep (se 2 (by rfl) ⟨6709767, by rfl⟩ : syracuseStep 17892713 = 13419535) B13419535
theorem B11928475 : Blo 1959435 11928475 := bstep (se 1 (by rfl) ⟨8946356, by rfl⟩ : syracuseStep 11928475 = 17892713) B17892713
theorem B63618533 : Blo 1959435 63618533 := bstep (se 4 (by rfl) ⟨5964237, by rfl⟩ : syracuseStep 63618533 = 11928475) B11928475
theorem B42412355 : Blo 1959435 42412355 := bstep (se 1 (by rfl) ⟨31809266, by rfl⟩ : syracuseStep 42412355 = 63618533) B63618533
theorem B28274903 : Blo 1959435 28274903 := bstep (se 1 (by rfl) ⟨21206177, by rfl⟩ : syracuseStep 28274903 = 42412355) B42412355
theorem B18849935 : Blo 1959435 18849935 := bstep (se 1 (by rfl) ⟨14137451, by rfl⟩ : syracuseStep 18849935 = 28274903) B28274903
theorem B12566623 : Blo 1959435 12566623 := bstep (se 1 (by rfl) ⟨9424967, by rfl⟩ : syracuseStep 12566623 = 18849935) B18849935
theorem B16755497 : Blo 1959435 16755497 := bstep (se 2 (by rfl) ⟨6283311, by rfl⟩ : syracuseStep 16755497 = 12566623) B12566623
theorem B11170331 : Blo 1959435 11170331 := bstep (se 1 (by rfl) ⟨8377748, by rfl⟩ : syracuseStep 11170331 = 16755497) B16755497
theorem B7446887 : Blo 1959435 7446887 := bstep (se 1 (by rfl) ⟨5585165, by rfl⟩ : syracuseStep 7446887 = 11170331) B11170331
theorem B4964591 : Blo 1959435 4964591 := bstep (se 1 (by rfl) ⟨3723443, by rfl⟩ : syracuseStep 4964591 = 7446887) B7446887
theorem B3309727 : Blo 1959435 3309727 := bstep (se 1 (by rfl) ⟨2482295, by rfl⟩ : syracuseStep 3309727 = 4964591) B4964591
theorem B4412969 : Blo 1959435 4412969 := bstep (se 2 (by rfl) ⟨1654863, by rfl⟩ : syracuseStep 4412969 = 3309727) B3309727
theorem B2941979 : Blo 1959435 2941979 := bstep (se 1 (by rfl) ⟨2206484, by rfl⟩ : syracuseStep 2941979 = 4412969) B4412969
theorem B1961319 : Blo 1959435 1961319 := bstep (se 1 (by rfl) ⟨1470989, by rfl⟩ : syracuseStep 1961319 = 2941979) B2941979
theorem B2206489 : Blo 1959435 2206489 := bbase (se 2 (by rfl) ⟨827433, by rfl⟩ : syracuseStep 2206489 = 1654867) (by norm_num)
theorem B2941985 : Blo 1959435 2941985 := bstep (se 2 (by rfl) ⟨1103244, by rfl⟩ : syracuseStep 2941985 = 2206489) B2206489
theorem B1961323 : Blo 1959435 1961323 := bstep (se 1 (by rfl) ⟨1470992, by rfl⟩ : syracuseStep 1961323 = 2941985) B2941985
theorem B7446917 : Blo 1959435 7446917 := bbase (se 4 (by rfl) ⟨698148, by rfl⟩ : syracuseStep 7446917 = 1396297) (by norm_num)
theorem B4964611 : Blo 1959435 4964611 := bstep (se 1 (by rfl) ⟨3723458, by rfl⟩ : syracuseStep 4964611 = 7446917) B7446917
theorem B6619481 : Blo 1959435 6619481 := bstep (se 2 (by rfl) ⟨2482305, by rfl⟩ : syracuseStep 6619481 = 4964611) B4964611
theorem B4412987 : Blo 1959435 4412987 := bstep (se 1 (by rfl) ⟨3309740, by rfl⟩ : syracuseStep 4412987 = 6619481) B6619481
theorem B2941991 : Blo 1959435 2941991 := bstep (se 1 (by rfl) ⟨2206493, by rfl⟩ : syracuseStep 2941991 = 4412987) B4412987
theorem B1961327 : Blo 1959435 1961327 := bstep (se 1 (by rfl) ⟨1470995, by rfl⟩ : syracuseStep 1961327 = 2941991) B2941991
theorem B2941997 : Blo 1959435 2941997 := bbase (se 3 (by rfl) ⟨551624, by rfl⟩ : syracuseStep 2941997 = 1103249) (by norm_num)
theorem B1961331 : Blo 1959435 1961331 := bstep (se 1 (by rfl) ⟨1470998, by rfl⟩ : syracuseStep 1961331 = 2941997) B2941997
theorem B4413005 : Blo 1959435 4413005 := bbase (se 3 (by rfl) ⟨827438, by rfl⟩ : syracuseStep 4413005 = 1654877) (by norm_num)
theorem B2942003 : Blo 1959435 2942003 := bstep (se 1 (by rfl) ⟨2206502, by rfl⟩ : syracuseStep 2942003 = 4413005) B4413005
theorem B1961335 : Blo 1959435 1961335 := bstep (se 1 (by rfl) ⟨1471001, by rfl⟩ : syracuseStep 1961335 = 2942003) B2942003
theorem B2482321 : Blo 1959435 2482321 := bbase (se 2 (by rfl) ⟨930870, by rfl⟩ : syracuseStep 2482321 = 1861741) (by norm_num)
theorem B3309761 : Blo 1959435 3309761 := bstep (se 2 (by rfl) ⟨1241160, by rfl⟩ : syracuseStep 3309761 = 2482321) B2482321
theorem B2206507 : Blo 1959435 2206507 := bstep (se 1 (by rfl) ⟨1654880, by rfl⟩ : syracuseStep 2206507 = 3309761) B3309761
theorem B2942009 : Blo 1959435 2942009 := bstep (se 2 (by rfl) ⟨1103253, by rfl⟩ : syracuseStep 2942009 = 2206507) B2206507
theorem B1961339 : Blo 1959435 1961339 := bstep (se 1 (by rfl) ⟨1471004, by rfl⟩ : syracuseStep 1961339 = 2942009) B2942009
theorem B4188925 : Blo 1959435 4188925 := bbase (se 3 (by rfl) ⟨785423, by rfl⟩ : syracuseStep 4188925 = 1570847) (by norm_num)
theorem B22340933 : Blo 1959435 22340933 := bstep (se 4 (by rfl) ⟨2094462, by rfl⟩ : syracuseStep 22340933 = 4188925) B4188925
theorem B14893955 : Blo 1959435 14893955 := bstep (se 1 (by rfl) ⟨11170466, by rfl⟩ : syracuseStep 14893955 = 22340933) B22340933
theorem B9929303 : Blo 1959435 9929303 := bstep (se 1 (by rfl) ⟨7446977, by rfl⟩ : syracuseStep 9929303 = 14893955) B14893955
theorem B6619535 : Blo 1959435 6619535 := bstep (se 1 (by rfl) ⟨4964651, by rfl⟩ : syracuseStep 6619535 = 9929303) B9929303
theorem B4413023 : Blo 1959435 4413023 := bstep (se 1 (by rfl) ⟨3309767, by rfl⟩ : syracuseStep 4413023 = 6619535) B6619535
theorem B2942015 : Blo 1959435 2942015 := bstep (se 1 (by rfl) ⟨2206511, by rfl⟩ : syracuseStep 2942015 = 4413023) B4413023
theorem B1961343 : Blo 1959435 1961343 := bstep (se 1 (by rfl) ⟨1471007, by rfl⟩ : syracuseStep 1961343 = 2942015) B2942015
theorem B2942021 : Blo 1959435 2942021 := bbase (se 4 (by rfl) ⟨275814, by rfl⟩ : syracuseStep 2942021 = 551629) (by norm_num)
theorem B1961347 : Blo 1959435 1961347 := bstep (se 1 (by rfl) ⟨1471010, by rfl⟩ : syracuseStep 1961347 = 2942021) B2942021
theorem B3309781 : Blo 1959435 3309781 := bbase (se 7 (by rfl) ⟨38786, by rfl⟩ : syracuseStep 3309781 = 77573) (by norm_num)
theorem B4413041 : Blo 1959435 4413041 := bstep (se 2 (by rfl) ⟨1654890, by rfl⟩ : syracuseStep 4413041 = 3309781) B3309781
theorem B2942027 : Blo 1959435 2942027 := bstep (se 1 (by rfl) ⟨2206520, by rfl⟩ : syracuseStep 2942027 = 4413041) B4413041
theorem B1961351 : Blo 1959435 1961351 := bstep (se 1 (by rfl) ⟨1471013, by rfl⟩ : syracuseStep 1961351 = 2942027) B2942027
theorem B2206525 : Blo 1959435 2206525 := bbase (se 3 (by rfl) ⟨413723, by rfl⟩ : syracuseStep 2206525 = 827447) (by norm_num)
theorem B2942033 : Blo 1959435 2942033 := bstep (se 2 (by rfl) ⟨1103262, by rfl⟩ : syracuseStep 2942033 = 2206525) B2206525
theorem B1961355 : Blo 1959435 1961355 := bstep (se 1 (by rfl) ⟨1471016, by rfl⟩ : syracuseStep 1961355 = 2942033) B2942033
theorem B6619589 : Blo 1959435 6619589 := bbase (se 4 (by rfl) ⟨620586, by rfl⟩ : syracuseStep 6619589 = 1241173) (by norm_num)
theorem B4413059 : Blo 1959435 4413059 := bstep (se 1 (by rfl) ⟨3309794, by rfl⟩ : syracuseStep 4413059 = 6619589) B6619589
theorem B2942039 : Blo 1959435 2942039 := bstep (se 1 (by rfl) ⟨2206529, by rfl⟩ : syracuseStep 2942039 = 4413059) B4413059
theorem B1961359 : Blo 1959435 1961359 := bstep (se 1 (by rfl) ⟨1471019, by rfl⟩ : syracuseStep 1961359 = 2942039) B2942039
theorem B2942045 : Blo 1959435 2942045 := bbase (se 3 (by rfl) ⟨551633, by rfl⟩ : syracuseStep 2942045 = 1103267) (by norm_num)
theorem B1961363 : Blo 1959435 1961363 := bstep (se 1 (by rfl) ⟨1471022, by rfl⟩ : syracuseStep 1961363 = 2942045) B2942045
theorem B4413077 : Blo 1959435 4413077 := bbase (se 6 (by rfl) ⟨103431, by rfl⟩ : syracuseStep 4413077 = 206863) (by norm_num)
theorem B2942051 : Blo 1959435 2942051 := bstep (se 1 (by rfl) ⟨2206538, by rfl⟩ : syracuseStep 2942051 = 4413077) B4413077
theorem B1961367 : Blo 1959435 1961367 := bstep (se 1 (by rfl) ⟨1471025, by rfl⟩ : syracuseStep 1961367 = 2942051) B2942051
theorem B2094493 : Blo 1959435 2094493 := bbase (se 3 (by rfl) ⟨392717, by rfl⟩ : syracuseStep 2094493 = 785435) (by norm_num)
theorem B2792657 : Blo 1959435 2792657 := bstep (se 2 (by rfl) ⟨1047246, by rfl⟩ : syracuseStep 2792657 = 2094493) B2094493
theorem B7447085 : Blo 1959435 7447085 := bstep (se 3 (by rfl) ⟨1396328, by rfl⟩ : syracuseStep 7447085 = 2792657) B2792657
theorem B4964723 : Blo 1959435 4964723 := bstep (se 1 (by rfl) ⟨3723542, by rfl⟩ : syracuseStep 4964723 = 7447085) B7447085
theorem B3309815 : Blo 1959435 3309815 := bstep (se 1 (by rfl) ⟨2482361, by rfl⟩ : syracuseStep 3309815 = 4964723) B4964723
theorem B2206543 : Blo 1959435 2206543 := bstep (se 1 (by rfl) ⟨1654907, by rfl⟩ : syracuseStep 2206543 = 3309815) B3309815
theorem B2942057 : Blo 1959435 2942057 := bstep (se 2 (by rfl) ⟨1103271, by rfl⟩ : syracuseStep 2942057 = 2206543) B2206543
theorem B1961371 : Blo 1959435 1961371 := bstep (se 1 (by rfl) ⟨1471028, by rfl⟩ : syracuseStep 1961371 = 2942057) B2942057
theorem B2356309 : Blo 1959435 2356309 := bbase (se 8 (by rfl) ⟨13806, by rfl⟩ : syracuseStep 2356309 = 27613) (by norm_num)
theorem B12566981 : Blo 1959435 12566981 := bstep (se 4 (by rfl) ⟨1178154, by rfl⟩ : syracuseStep 12566981 = 2356309) B2356309
theorem B8377987 : Blo 1959435 8377987 := bstep (se 1 (by rfl) ⟨6283490, by rfl⟩ : syracuseStep 8377987 = 12566981) B12566981
theorem B11170649 : Blo 1959435 11170649 := bstep (se 2 (by rfl) ⟨4188993, by rfl⟩ : syracuseStep 11170649 = 8377987) B8377987
theorem B7447099 : Blo 1959435 7447099 := bstep (se 1 (by rfl) ⟨5585324, by rfl⟩ : syracuseStep 7447099 = 11170649) B11170649
theorem B9929465 : Blo 1959435 9929465 := bstep (se 2 (by rfl) ⟨3723549, by rfl⟩ : syracuseStep 9929465 = 7447099) B7447099
theorem B6619643 : Blo 1959435 6619643 := bstep (se 1 (by rfl) ⟨4964732, by rfl⟩ : syracuseStep 6619643 = 9929465) B9929465
theorem B4413095 : Blo 1959435 4413095 := bstep (se 1 (by rfl) ⟨3309821, by rfl⟩ : syracuseStep 4413095 = 6619643) B6619643
theorem B2942063 : Blo 1959435 2942063 := bstep (se 1 (by rfl) ⟨2206547, by rfl⟩ : syracuseStep 2942063 = 4413095) B4413095
theorem B1961375 : Blo 1959435 1961375 := bstep (se 1 (by rfl) ⟨1471031, by rfl⟩ : syracuseStep 1961375 = 2942063) B2942063
theorem B2942069 : Blo 1959435 2942069 := bbase (se 5 (by rfl) ⟨137909, by rfl⟩ : syracuseStep 2942069 = 275819) (by norm_num)
theorem B1961379 : Blo 1959435 1961379 := bstep (se 1 (by rfl) ⟨1471034, by rfl⟩ : syracuseStep 1961379 = 2942069) B2942069
theorem B3723565 : Blo 1959435 3723565 := bbase (se 3 (by rfl) ⟨698168, by rfl⟩ : syracuseStep 3723565 = 1396337) (by norm_num)
theorem B4964753 : Blo 1959435 4964753 := bstep (se 2 (by rfl) ⟨1861782, by rfl⟩ : syracuseStep 4964753 = 3723565) B3723565
theorem B3309835 : Blo 1959435 3309835 := bstep (se 1 (by rfl) ⟨2482376, by rfl⟩ : syracuseStep 3309835 = 4964753) B4964753
theorem B4413113 : Blo 1959435 4413113 := bstep (se 2 (by rfl) ⟨1654917, by rfl⟩ : syracuseStep 4413113 = 3309835) B3309835
theorem B2942075 : Blo 1959435 2942075 := bstep (se 1 (by rfl) ⟨2206556, by rfl⟩ : syracuseStep 2942075 = 4413113) B4413113
theorem B1961383 : Blo 1959435 1961383 := bstep (se 1 (by rfl) ⟨1471037, by rfl⟩ : syracuseStep 1961383 = 2942075) B2942075
theorem B2206561 : Blo 1959435 2206561 := bbase (se 2 (by rfl) ⟨827460, by rfl⟩ : syracuseStep 2206561 = 1654921) (by norm_num)
theorem B2942081 : Blo 1959435 2942081 := bstep (se 2 (by rfl) ⟨1103280, by rfl⟩ : syracuseStep 2942081 = 2206561) B2206561
theorem B1961387 : Blo 1959435 1961387 := bstep (se 1 (by rfl) ⟨1471040, by rfl⟩ : syracuseStep 1961387 = 2942081) B2942081
theorem B4964773 : Blo 1959435 4964773 := bbase (se 4 (by rfl) ⟨465447, by rfl⟩ : syracuseStep 4964773 = 930895) (by norm_num)
theorem B6619697 : Blo 1959435 6619697 := bstep (se 2 (by rfl) ⟨2482386, by rfl⟩ : syracuseStep 6619697 = 4964773) B4964773
theorem B4413131 : Blo 1959435 4413131 := bstep (se 1 (by rfl) ⟨3309848, by rfl⟩ : syracuseStep 4413131 = 6619697) B6619697
theorem B2942087 : Blo 1959435 2942087 := bstep (se 1 (by rfl) ⟨2206565, by rfl⟩ : syracuseStep 2942087 = 4413131) B4413131
theorem B1961391 : Blo 1959435 1961391 := bstep (se 1 (by rfl) ⟨1471043, by rfl⟩ : syracuseStep 1961391 = 2942087) B2942087
theorem B2942093 : Blo 1959435 2942093 := bbase (se 3 (by rfl) ⟨551642, by rfl⟩ : syracuseStep 2942093 = 1103285) (by norm_num)
theorem B1961395 : Blo 1959435 1961395 := bstep (se 1 (by rfl) ⟨1471046, by rfl⟩ : syracuseStep 1961395 = 2942093) B2942093
theorem B4413149 : Blo 1959435 4413149 := bbase (se 3 (by rfl) ⟨827465, by rfl⟩ : syracuseStep 4413149 = 1654931) (by norm_num)
theorem B2942099 : Blo 1959435 2942099 := bstep (se 1 (by rfl) ⟨2206574, by rfl⟩ : syracuseStep 2942099 = 4413149) B4413149
theorem B1961399 : Blo 1959435 1961399 := bstep (se 1 (by rfl) ⟨1471049, by rfl⟩ : syracuseStep 1961399 = 2942099) B2942099
theorem B3309869 : Blo 1959435 3309869 := bbase (se 3 (by rfl) ⟨620600, by rfl⟩ : syracuseStep 3309869 = 1241201) (by norm_num)
theorem B2206579 : Blo 1959435 2206579 := bstep (se 1 (by rfl) ⟨1654934, by rfl⟩ : syracuseStep 2206579 = 3309869) B3309869
theorem B2942105 : Blo 1959435 2942105 := bstep (se 2 (by rfl) ⟨1103289, by rfl⟩ : syracuseStep 2942105 = 2206579) B2206579
theorem B1961403 : Blo 1959435 1961403 := bstep (se 1 (by rfl) ⟨1471052, by rfl⟩ : syracuseStep 1961403 = 2942105) B2942105
theorem B2982253 : Blo 1959435 2982253 := bbase (se 3 (by rfl) ⟨559172, by rfl⟩ : syracuseStep 2982253 = 1118345) (by norm_num)
theorem B3976337 : Blo 1959435 3976337 := bstep (se 2 (by rfl) ⟨1491126, by rfl⟩ : syracuseStep 3976337 = 2982253) B2982253
theorem B2650891 : Blo 1959435 2650891 := bstep (se 1 (by rfl) ⟨1988168, by rfl⟩ : syracuseStep 2650891 = 3976337) B3976337
theorem B3534521 : Blo 1959435 3534521 := bstep (se 2 (by rfl) ⟨1325445, by rfl⟩ : syracuseStep 3534521 = 2650891) B2650891
theorem B37701557 : Blo 1959435 37701557 := bstep (se 5 (by rfl) ⟨1767260, by rfl⟩ : syracuseStep 37701557 = 3534521) B3534521
theorem B25134371 : Blo 1959435 25134371 := bstep (se 1 (by rfl) ⟨18850778, by rfl⟩ : syracuseStep 25134371 = 37701557) B37701557
theorem B16756247 : Blo 1959435 16756247 := bstep (se 1 (by rfl) ⟨12567185, by rfl⟩ : syracuseStep 16756247 = 25134371) B25134371
theorem B11170831 : Blo 1959435 11170831 := bstep (se 1 (by rfl) ⟨8378123, by rfl⟩ : syracuseStep 11170831 = 16756247) B16756247
theorem B14894441 : Blo 1959435 14894441 := bstep (se 2 (by rfl) ⟨5585415, by rfl⟩ : syracuseStep 14894441 = 11170831) B11170831
theorem B9929627 : Blo 1959435 9929627 := bstep (se 1 (by rfl) ⟨7447220, by rfl⟩ : syracuseStep 9929627 = 14894441) B14894441
theorem B6619751 : Blo 1959435 6619751 := bstep (se 1 (by rfl) ⟨4964813, by rfl⟩ : syracuseStep 6619751 = 9929627) B9929627
theorem B4413167 : Blo 1959435 4413167 := bstep (se 1 (by rfl) ⟨3309875, by rfl⟩ : syracuseStep 4413167 = 6619751) B6619751
theorem B2942111 : Blo 1959435 2942111 := bstep (se 1 (by rfl) ⟨2206583, by rfl⟩ : syracuseStep 2942111 = 4413167) B4413167
theorem B1961407 : Blo 1959435 1961407 := bstep (se 1 (by rfl) ⟨1471055, by rfl⟩ : syracuseStep 1961407 = 2942111) B2942111
theorem B2942117 : Blo 1959435 2942117 := bbase (se 4 (by rfl) ⟨275823, by rfl⟩ : syracuseStep 2942117 = 551647) (by norm_num)
theorem B1961411 : Blo 1959435 1961411 := bstep (se 1 (by rfl) ⟨1471058, by rfl⟩ : syracuseStep 1961411 = 2942117) B2942117
theorem B2482417 : Blo 1959435 2482417 := bbase (se 2 (by rfl) ⟨930906, by rfl⟩ : syracuseStep 2482417 = 1861813) (by norm_num)
theorem B3309889 : Blo 1959435 3309889 := bstep (se 2 (by rfl) ⟨1241208, by rfl⟩ : syracuseStep 3309889 = 2482417) B2482417
theorem B4413185 : Blo 1959435 4413185 := bstep (se 2 (by rfl) ⟨1654944, by rfl⟩ : syracuseStep 4413185 = 3309889) B3309889
theorem B2942123 : Blo 1959435 2942123 := bstep (se 1 (by rfl) ⟨2206592, by rfl⟩ : syracuseStep 2942123 = 4413185) B4413185
theorem B1961415 : Blo 1959435 1961415 := bstep (se 1 (by rfl) ⟨1471061, by rfl⟩ : syracuseStep 1961415 = 2942123) B2942123
theorem B2206597 : Blo 1959435 2206597 := bbase (se 4 (by rfl) ⟨206868, by rfl⟩ : syracuseStep 2206597 = 413737) (by norm_num)
theorem B2942129 : Blo 1959435 2942129 := bstep (se 2 (by rfl) ⟨1103298, by rfl⟩ : syracuseStep 2942129 = 2206597) B2206597
theorem B1961419 : Blo 1959435 1961419 := bstep (se 1 (by rfl) ⟨1471064, by rfl⟩ : syracuseStep 1961419 = 2942129) B2942129
theorem B4246253 : Blo 1959435 4246253 := bbase (se 3 (by rfl) ⟨796172, by rfl⟩ : syracuseStep 4246253 = 1592345) (by norm_num)
theorem B2830835 : Blo 1959435 2830835 := bstep (se 1 (by rfl) ⟨2123126, by rfl⟩ : syracuseStep 2830835 = 4246253) B4246253
theorem B7548893 : Blo 1959435 7548893 := bstep (se 3 (by rfl) ⟨1415417, by rfl⟩ : syracuseStep 7548893 = 2830835) B2830835
theorem B5032595 : Blo 1959435 5032595 := bstep (se 1 (by rfl) ⟨3774446, by rfl⟩ : syracuseStep 5032595 = 7548893) B7548893
theorem B3355063 : Blo 1959435 3355063 := bstep (se 1 (by rfl) ⟨2516297, by rfl⟩ : syracuseStep 3355063 = 5032595) B5032595
theorem B17893669 : Blo 1959435 17893669 := bstep (se 4 (by rfl) ⟨1677531, by rfl⟩ : syracuseStep 17893669 = 3355063) B3355063
theorem B23858225 : Blo 1959435 23858225 := bstep (se 2 (by rfl) ⟨8946834, by rfl⟩ : syracuseStep 23858225 = 17893669) B17893669
theorem B15905483 : Blo 1959435 15905483 := bstep (se 1 (by rfl) ⟨11929112, by rfl⟩ : syracuseStep 15905483 = 23858225) B23858225
theorem B10603655 : Blo 1959435 10603655 := bstep (se 1 (by rfl) ⟨7952741, by rfl⟩ : syracuseStep 10603655 = 15905483) B15905483
theorem B7069103 : Blo 1959435 7069103 := bstep (se 1 (by rfl) ⟨5301827, by rfl⟩ : syracuseStep 7069103 = 10603655) B10603655
theorem B4712735 : Blo 1959435 4712735 := bstep (se 1 (by rfl) ⟨3534551, by rfl⟩ : syracuseStep 4712735 = 7069103) B7069103
theorem B3141823 : Blo 1959435 3141823 := bstep (se 1 (by rfl) ⟨2356367, by rfl⟩ : syracuseStep 3141823 = 4712735) B4712735
theorem B4189097 : Blo 1959435 4189097 := bstep (se 2 (by rfl) ⟨1570911, by rfl⟩ : syracuseStep 4189097 = 3141823) B3141823
theorem B2792731 : Blo 1959435 2792731 := bstep (se 1 (by rfl) ⟨2094548, by rfl⟩ : syracuseStep 2792731 = 4189097) B4189097
theorem B3723641 : Blo 1959435 3723641 := bstep (se 2 (by rfl) ⟨1396365, by rfl⟩ : syracuseStep 3723641 = 2792731) B2792731
theorem B2482427 : Blo 1959435 2482427 := bstep (se 1 (by rfl) ⟨1861820, by rfl⟩ : syracuseStep 2482427 = 3723641) B3723641
theorem B6619805 : Blo 1959435 6619805 := bstep (se 3 (by rfl) ⟨1241213, by rfl⟩ : syracuseStep 6619805 = 2482427) B2482427
theorem B4413203 : Blo 1959435 4413203 := bstep (se 1 (by rfl) ⟨3309902, by rfl⟩ : syracuseStep 4413203 = 6619805) B6619805
theorem B2942135 : Blo 1959435 2942135 := bstep (se 1 (by rfl) ⟨2206601, by rfl⟩ : syracuseStep 2942135 = 4413203) B4413203
theorem B1961423 : Blo 1959435 1961423 := bstep (se 1 (by rfl) ⟨1471067, by rfl⟩ : syracuseStep 1961423 = 2942135) B2942135
theorem B2942141 : Blo 1959435 2942141 := bbase (se 3 (by rfl) ⟨551651, by rfl⟩ : syracuseStep 2942141 = 1103303) (by norm_num)
theorem B1961427 : Blo 1959435 1961427 := bstep (se 1 (by rfl) ⟨1471070, by rfl⟩ : syracuseStep 1961427 = 2942141) B2942141
theorem B4413221 : Blo 1959435 4413221 := bbase (se 4 (by rfl) ⟨413739, by rfl⟩ : syracuseStep 4413221 = 827479) (by norm_num)
theorem B2942147 : Blo 1959435 2942147 := bstep (se 1 (by rfl) ⟨2206610, by rfl⟩ : syracuseStep 2942147 = 4413221) B4413221
theorem B1961431 : Blo 1959435 1961431 := bstep (se 1 (by rfl) ⟨1471073, by rfl⟩ : syracuseStep 1961431 = 2942147) B2942147
theorem B4964885 : Blo 1959435 4964885 := bbase (se 6 (by rfl) ⟨116364, by rfl⟩ : syracuseStep 4964885 = 232729) (by norm_num)
theorem B3309923 : Blo 1959435 3309923 := bstep (se 1 (by rfl) ⟨2482442, by rfl⟩ : syracuseStep 3309923 = 4964885) B4964885
theorem B2206615 : Blo 1959435 2206615 := bstep (se 1 (by rfl) ⟨1654961, by rfl⟩ : syracuseStep 2206615 = 3309923) B3309923
theorem B2942153 : Blo 1959435 2942153 := bstep (se 2 (by rfl) ⟨1103307, by rfl⟩ : syracuseStep 2942153 = 2206615) B2206615
theorem B1961435 : Blo 1959435 1961435 := bstep (se 1 (by rfl) ⟨1471076, by rfl⟩ : syracuseStep 1961435 = 2942153) B2942153
theorem C0 (j : ℕ) (h1 : 489858 ≤ j) (h2 : j ≤ 490358) : Blo 1959435 (4 * j + 3) := by
  interval_cases j
  · exact B1959435
  · exact B1959439
  · exact B1959443
  · exact B1959447
  · exact B1959451
  · exact B1959455
  · exact B1959459
  · exact B1959463
  · exact B1959467
  · exact B1959471
  · exact B1959475
  · exact B1959479
  · exact B1959483
  · exact B1959487
  · exact B1959491
  · exact B1959495
  · exact B1959499
  · exact B1959503
  · exact B1959507
  · exact B1959511
  · exact B1959515
  · exact B1959519
  · exact B1959523
  · exact B1959527
  · exact B1959531
  · exact B1959535
  · exact B1959539
  · exact B1959543
  · exact B1959547
  · exact B1959551
  · exact B1959555
  · exact B1959559
  · exact B1959563
  · exact B1959567
  · exact B1959571
  · exact B1959575
  · exact B1959579
  · exact B1959583
  · exact B1959587
  · exact B1959591
  · exact B1959595
  · exact B1959599
  · exact B1959603
  · exact B1959607
  · exact B1959611
  · exact B1959615
  · exact B1959619
  · exact B1959623
  · exact B1959627
  · exact B1959631
  · exact B1959635
  · exact B1959639
  · exact B1959643
  · exact B1959647
  · exact B1959651
  · exact B1959655
  · exact B1959659
  · exact B1959663
  · exact B1959667
  · exact B1959671
  · exact B1959675
  · exact B1959679
  · exact B1959683
  · exact B1959687
  · exact B1959691
  · exact B1959695
  · exact B1959699
  · exact B1959703
  · exact B1959707
  · exact B1959711
  · exact B1959715
  · exact B1959719
  · exact B1959723
  · exact B1959727
  · exact B1959731
  · exact B1959735
  · exact B1959739
  · exact B1959743
  · exact B1959747
  · exact B1959751
  · exact B1959755
  · exact B1959759
  · exact B1959763
  · exact B1959767
  · exact B1959771
  · exact B1959775
  · exact B1959779
  · exact B1959783
  · exact B1959787
  · exact B1959791
  · exact B1959795
  · exact B1959799
  · exact B1959803
  · exact B1959807
  · exact B1959811
  · exact B1959815
  · exact B1959819
  · exact B1959823
  · exact B1959827
  · exact B1959831
  · exact B1959835
  · exact B1959839
  · exact B1959843
  · exact B1959847
  · exact B1959851
  · exact B1959855
  · exact B1959859
  · exact B1959863
  · exact B1959867
  · exact B1959871
  · exact B1959875
  · exact B1959879
  · exact B1959883
  · exact B1959887
  · exact B1959891
  · exact B1959895
  · exact B1959899
  · exact B1959903
  · exact B1959907
  · exact B1959911
  · exact B1959915
  · exact B1959919
  · exact B1959923
  · exact B1959927
  · exact B1959931
  · exact B1959935
  · exact B1959939
  · exact B1959943
  · exact B1959947
  · exact B1959951
  · exact B1959955
  · exact B1959959
  · exact B1959963
  · exact B1959967
  · exact B1959971
  · exact B1959975
  · exact B1959979
  · exact B1959983
  · exact B1959987
  · exact B1959991
  · exact B1959995
  · exact B1959999
  · exact B1960003
  · exact B1960007
  · exact B1960011
  · exact B1960015
  · exact B1960019
  · exact B1960023
  · exact B1960027
  · exact B1960031
  · exact B1960035
  · exact B1960039
  · exact B1960043
  · exact B1960047
  · exact B1960051
  · exact B1960055
  · exact B1960059
  · exact B1960063
  · exact B1960067
  · exact B1960071
  · exact B1960075
  · exact B1960079
  · exact B1960083
  · exact B1960087
  · exact B1960091
  · exact B1960095
  · exact B1960099
  · exact B1960103
  · exact B1960107
  · exact B1960111
  · exact B1960115
  · exact B1960119
  · exact B1960123
  · exact B1960127
  · exact B1960131
  · exact B1960135
  · exact B1960139
  · exact B1960143
  · exact B1960147
  · exact B1960151
  · exact B1960155
  · exact B1960159
  · exact B1960163
  · exact B1960167
  · exact B1960171
  · exact B1960175
  · exact B1960179
  · exact B1960183
  · exact B1960187
  · exact B1960191
  · exact B1960195
  · exact B1960199
  · exact B1960203
  · exact B1960207
  · exact B1960211
  · exact B1960215
  · exact B1960219
  · exact B1960223
  · exact B1960227
  · exact B1960231
  · exact B1960235
  · exact B1960239
  · exact B1960243
  · exact B1960247
  · exact B1960251
  · exact B1960255
  · exact B1960259
  · exact B1960263
  · exact B1960267
  · exact B1960271
  · exact B1960275
  · exact B1960279
  · exact B1960283
  · exact B1960287
  · exact B1960291
  · exact B1960295
  · exact B1960299
  · exact B1960303
  · exact B1960307
  · exact B1960311
  · exact B1960315
  · exact B1960319
  · exact B1960323
  · exact B1960327
  · exact B1960331
  · exact B1960335
  · exact B1960339
  · exact B1960343
  · exact B1960347
  · exact B1960351
  · exact B1960355
  · exact B1960359
  · exact B1960363
  · exact B1960367
  · exact B1960371
  · exact B1960375
  · exact B1960379
  · exact B1960383
  · exact B1960387
  · exact B1960391
  · exact B1960395
  · exact B1960399
  · exact B1960403
  · exact B1960407
  · exact B1960411
  · exact B1960415
  · exact B1960419
  · exact B1960423
  · exact B1960427
  · exact B1960431
  · exact B1960435
  · exact B1960439
  · exact B1960443
  · exact B1960447
  · exact B1960451
  · exact B1960455
  · exact B1960459
  · exact B1960463
  · exact B1960467
  · exact B1960471
  · exact B1960475
  · exact B1960479
  · exact B1960483
  · exact B1960487
  · exact B1960491
  · exact B1960495
  · exact B1960499
  · exact B1960503
  · exact B1960507
  · exact B1960511
  · exact B1960515
  · exact B1960519
  · exact B1960523
  · exact B1960527
  · exact B1960531
  · exact B1960535
  · exact B1960539
  · exact B1960543
  · exact B1960547
  · exact B1960551
  · exact B1960555
  · exact B1960559
  · exact B1960563
  · exact B1960567
  · exact B1960571
  · exact B1960575
  · exact B1960579
  · exact B1960583
  · exact B1960587
  · exact B1960591
  · exact B1960595
  · exact B1960599
  · exact B1960603
  · exact B1960607
  · exact B1960611
  · exact B1960615
  · exact B1960619
  · exact B1960623
  · exact B1960627
  · exact B1960631
  · exact B1960635
  · exact B1960639
  · exact B1960643
  · exact B1960647
  · exact B1960651
  · exact B1960655
  · exact B1960659
  · exact B1960663
  · exact B1960667
  · exact B1960671
  · exact B1960675
  · exact B1960679
  · exact B1960683
  · exact B1960687
  · exact B1960691
  · exact B1960695
  · exact B1960699
  · exact B1960703
  · exact B1960707
  · exact B1960711
  · exact B1960715
  · exact B1960719
  · exact B1960723
  · exact B1960727
  · exact B1960731
  · exact B1960735
  · exact B1960739
  · exact B1960743
  · exact B1960747
  · exact B1960751
  · exact B1960755
  · exact B1960759
  · exact B1960763
  · exact B1960767
  · exact B1960771
  · exact B1960775
  · exact B1960779
  · exact B1960783
  · exact B1960787
  · exact B1960791
  · exact B1960795
  · exact B1960799
  · exact B1960803
  · exact B1960807
  · exact B1960811
  · exact B1960815
  · exact B1960819
  · exact B1960823
  · exact B1960827
  · exact B1960831
  · exact B1960835
  · exact B1960839
  · exact B1960843
  · exact B1960847
  · exact B1960851
  · exact B1960855
  · exact B1960859
  · exact B1960863
  · exact B1960867
  · exact B1960871
  · exact B1960875
  · exact B1960879
  · exact B1960883
  · exact B1960887
  · exact B1960891
  · exact B1960895
  · exact B1960899
  · exact B1960903
  · exact B1960907
  · exact B1960911
  · exact B1960915
  · exact B1960919
  · exact B1960923
  · exact B1960927
  · exact B1960931
  · exact B1960935
  · exact B1960939
  · exact B1960943
  · exact B1960947
  · exact B1960951
  · exact B1960955
  · exact B1960959
  · exact B1960963
  · exact B1960967
  · exact B1960971
  · exact B1960975
  · exact B1960979
  · exact B1960983
  · exact B1960987
  · exact B1960991
  · exact B1960995
  · exact B1960999
  · exact B1961003
  · exact B1961007
  · exact B1961011
  · exact B1961015
  · exact B1961019
  · exact B1961023
  · exact B1961027
  · exact B1961031
  · exact B1961035
  · exact B1961039
  · exact B1961043
  · exact B1961047
  · exact B1961051
  · exact B1961055
  · exact B1961059
  · exact B1961063
  · exact B1961067
  · exact B1961071
  · exact B1961075
  · exact B1961079
  · exact B1961083
  · exact B1961087
  · exact B1961091
  · exact B1961095
  · exact B1961099
  · exact B1961103
  · exact B1961107
  · exact B1961111
  · exact B1961115
  · exact B1961119
  · exact B1961123
  · exact B1961127
  · exact B1961131
  · exact B1961135
  · exact B1961139
  · exact B1961143
  · exact B1961147
  · exact B1961151
  · exact B1961155
  · exact B1961159
  · exact B1961163
  · exact B1961167
  · exact B1961171
  · exact B1961175
  · exact B1961179
  · exact B1961183
  · exact B1961187
  · exact B1961191
  · exact B1961195
  · exact B1961199
  · exact B1961203
  · exact B1961207
  · exact B1961211
  · exact B1961215
  · exact B1961219
  · exact B1961223
  · exact B1961227
  · exact B1961231
  · exact B1961235
  · exact B1961239
  · exact B1961243
  · exact B1961247
  · exact B1961251
  · exact B1961255
  · exact B1961259
  · exact B1961263
  · exact B1961267
  · exact B1961271
  · exact B1961275
  · exact B1961279
  · exact B1961283
  · exact B1961287
  · exact B1961291
  · exact B1961295
  · exact B1961299
  · exact B1961303
  · exact B1961307
  · exact B1961311
  · exact B1961315
  · exact B1961319
  · exact B1961323
  · exact B1961327
  · exact B1961331
  · exact B1961335
  · exact B1961339
  · exact B1961343
  · exact B1961347
  · exact B1961351
  · exact B1961355
  · exact B1961359
  · exact B1961363
  · exact B1961367
  · exact B1961371
  · exact B1961375
  · exact B1961379
  · exact B1961383
  · exact B1961387
  · exact B1961391
  · exact B1961395
  · exact B1961399
  · exact B1961403
  · exact B1961407
  · exact B1961411
  · exact B1961415
  · exact B1961419
  · exact B1961423
  · exact B1961427
  · exact B1961431
  · exact B1961435
theorem solution (m : ℕ) (hlo : 1959435 ≤ m) (hhi : m ≤ 1961435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 489858 ≤ j := by omega
    have hj2 : j ≤ 490358 := by omega
    have hb : Blo 1959435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
