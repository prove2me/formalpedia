-- Prove2me | solution 1 for syracuse_descends_range_1919435_1921435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:47:10.537707+00:00
-- url     : https://prove2.me/submissions/8dd7fc93-ea83-456d-9282-20985dca5e6e

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

theorem B2159365 : Blo 1919435 2159365 := bbase (se 4 (by rfl) ⟨202440, by rfl⟩ : syracuseStep 2159365 = 404881) (by norm_num)
theorem B2879153 : Blo 1919435 2879153 := bstep (se 2 (by rfl) ⟨1079682, by rfl⟩ : syracuseStep 2879153 = 2159365) B2159365
theorem B1919435 : Blo 1919435 1919435 := bstep (se 1 (by rfl) ⟨1439576, by rfl⟩ : syracuseStep 1919435 = 2879153) B2879153
theorem B3074573 : Blo 1919435 3074573 := bbase (se 3 (by rfl) ⟨576482, by rfl⟩ : syracuseStep 3074573 = 1152965) (by norm_num)
theorem B2049715 : Blo 1919435 2049715 := bstep (se 1 (by rfl) ⟨1537286, by rfl⟩ : syracuseStep 2049715 = 3074573) B3074573
theorem B2732953 : Blo 1919435 2732953 := bstep (se 2 (by rfl) ⟨1024857, by rfl⟩ : syracuseStep 2732953 = 2049715) B2049715
theorem B3643937 : Blo 1919435 3643937 := bstep (se 2 (by rfl) ⟨1366476, by rfl⟩ : syracuseStep 3643937 = 2732953) B2732953
theorem B2429291 : Blo 1919435 2429291 := bstep (se 1 (by rfl) ⟨1821968, by rfl⟩ : syracuseStep 2429291 = 3643937) B3643937
theorem B6478109 : Blo 1919435 6478109 := bstep (se 3 (by rfl) ⟨1214645, by rfl⟩ : syracuseStep 6478109 = 2429291) B2429291
theorem B4318739 : Blo 1919435 4318739 := bstep (se 1 (by rfl) ⟨3239054, by rfl⟩ : syracuseStep 4318739 = 6478109) B6478109
theorem B2879159 : Blo 1919435 2879159 := bstep (se 1 (by rfl) ⟨2159369, by rfl⟩ : syracuseStep 2879159 = 4318739) B4318739
theorem B1919439 : Blo 1919435 1919439 := bstep (se 1 (by rfl) ⟨1439579, by rfl⟩ : syracuseStep 1919439 = 2879159) B2879159
theorem B2879165 : Blo 1919435 2879165 := bbase (se 3 (by rfl) ⟨539843, by rfl⟩ : syracuseStep 2879165 = 1079687) (by norm_num)
theorem B1919443 : Blo 1919435 1919443 := bstep (se 1 (by rfl) ⟨1439582, by rfl⟩ : syracuseStep 1919443 = 2879165) B2879165
theorem B4318757 : Blo 1919435 4318757 := bbase (se 4 (by rfl) ⟨404883, by rfl⟩ : syracuseStep 4318757 = 809767) (by norm_num)
theorem B2879171 : Blo 1919435 2879171 := bstep (se 1 (by rfl) ⟨2159378, by rfl⟩ : syracuseStep 2879171 = 4318757) B4318757
theorem B1919447 : Blo 1919435 1919447 := bstep (se 1 (by rfl) ⟨1439585, by rfl⟩ : syracuseStep 1919447 = 2879171) B2879171
theorem B4858613 : Blo 1919435 4858613 := bbase (se 5 (by rfl) ⟨227747, by rfl⟩ : syracuseStep 4858613 = 455495) (by norm_num)
theorem B3239075 : Blo 1919435 3239075 := bstep (se 1 (by rfl) ⟨2429306, by rfl⟩ : syracuseStep 3239075 = 4858613) B4858613
theorem B2159383 : Blo 1919435 2159383 := bstep (se 1 (by rfl) ⟨1619537, by rfl⟩ : syracuseStep 2159383 = 3239075) B3239075
theorem B2879177 : Blo 1919435 2879177 := bstep (se 2 (by rfl) ⟨1079691, by rfl⟩ : syracuseStep 2879177 = 2159383) B2159383
theorem B1919451 : Blo 1919435 1919451 := bstep (se 1 (by rfl) ⟨1439588, by rfl⟩ : syracuseStep 1919451 = 2879177) B2879177
theorem B27671381 : Blo 1919435 27671381 := bbase (se 9 (by rfl) ⟨81068, by rfl⟩ : syracuseStep 27671381 = 162137) (by norm_num)
theorem B18447587 : Blo 1919435 18447587 := bstep (se 1 (by rfl) ⟨13835690, by rfl⟩ : syracuseStep 18447587 = 27671381) B27671381
theorem B12298391 : Blo 1919435 12298391 := bstep (se 1 (by rfl) ⟨9223793, by rfl⟩ : syracuseStep 12298391 = 18447587) B18447587
theorem B8198927 : Blo 1919435 8198927 := bstep (se 1 (by rfl) ⟨6149195, by rfl⟩ : syracuseStep 8198927 = 12298391) B12298391
theorem B5465951 : Blo 1919435 5465951 := bstep (se 1 (by rfl) ⟨4099463, by rfl⟩ : syracuseStep 5465951 = 8198927) B8198927
theorem B3643967 : Blo 1919435 3643967 := bstep (se 1 (by rfl) ⟨2732975, by rfl⟩ : syracuseStep 3643967 = 5465951) B5465951
theorem B9717245 : Blo 1919435 9717245 := bstep (se 3 (by rfl) ⟨1821983, by rfl⟩ : syracuseStep 9717245 = 3643967) B3643967
theorem B6478163 : Blo 1919435 6478163 := bstep (se 1 (by rfl) ⟨4858622, by rfl⟩ : syracuseStep 6478163 = 9717245) B9717245
theorem B4318775 : Blo 1919435 4318775 := bstep (se 1 (by rfl) ⟨3239081, by rfl⟩ : syracuseStep 4318775 = 6478163) B6478163
theorem B2879183 : Blo 1919435 2879183 := bstep (se 1 (by rfl) ⟨2159387, by rfl⟩ : syracuseStep 2879183 = 4318775) B4318775
theorem B1919455 : Blo 1919435 1919455 := bstep (se 1 (by rfl) ⟨1439591, by rfl⟩ : syracuseStep 1919455 = 2879183) B2879183
theorem B2879189 : Blo 1919435 2879189 := bbase (se 7 (by rfl) ⟨33740, by rfl⟩ : syracuseStep 2879189 = 67481) (by norm_num)
theorem B1919459 : Blo 1919435 1919459 := bstep (se 1 (by rfl) ⟨1439594, by rfl⟩ : syracuseStep 1919459 = 2879189) B2879189
theorem B4611917 : Blo 1919435 4611917 := bbase (se 3 (by rfl) ⟨864734, by rfl⟩ : syracuseStep 4611917 = 1729469) (by norm_num)
theorem B3074611 : Blo 1919435 3074611 := bstep (se 1 (by rfl) ⟨2305958, by rfl⟩ : syracuseStep 3074611 = 4611917) B4611917
theorem B4099481 : Blo 1919435 4099481 := bstep (se 2 (by rfl) ⟨1537305, by rfl⟩ : syracuseStep 4099481 = 3074611) B3074611
theorem B2732987 : Blo 1919435 2732987 := bstep (se 1 (by rfl) ⟨2049740, by rfl⟩ : syracuseStep 2732987 = 4099481) B4099481
theorem B7287965 : Blo 1919435 7287965 := bstep (se 3 (by rfl) ⟨1366493, by rfl⟩ : syracuseStep 7287965 = 2732987) B2732987
theorem B4858643 : Blo 1919435 4858643 := bstep (se 1 (by rfl) ⟨3643982, by rfl⟩ : syracuseStep 4858643 = 7287965) B7287965
theorem B3239095 : Blo 1919435 3239095 := bstep (se 1 (by rfl) ⟨2429321, by rfl⟩ : syracuseStep 3239095 = 4858643) B4858643
theorem B4318793 : Blo 1919435 4318793 := bstep (se 2 (by rfl) ⟨1619547, by rfl⟩ : syracuseStep 4318793 = 3239095) B3239095
theorem B2879195 : Blo 1919435 2879195 := bstep (se 1 (by rfl) ⟨2159396, by rfl⟩ : syracuseStep 2879195 = 4318793) B4318793
theorem B1919463 : Blo 1919435 1919463 := bstep (se 1 (by rfl) ⟨1439597, by rfl⟩ : syracuseStep 1919463 = 2879195) B2879195
theorem B2159401 : Blo 1919435 2159401 := bbase (se 2 (by rfl) ⟨809775, by rfl⟩ : syracuseStep 2159401 = 1619551) (by norm_num)
theorem B2879201 : Blo 1919435 2879201 := bstep (se 2 (by rfl) ⟨1079700, by rfl⟩ : syracuseStep 2879201 = 2159401) B2159401
theorem B1919467 : Blo 1919435 1919467 := bstep (se 1 (by rfl) ⟨1439600, by rfl⟩ : syracuseStep 1919467 = 2879201) B2879201
theorem B23347925 : Blo 1919435 23347925 := bbase (se 7 (by rfl) ⟨273608, by rfl⟩ : syracuseStep 23347925 = 547217) (by norm_num)
theorem B15565283 : Blo 1919435 15565283 := bstep (se 1 (by rfl) ⟨11673962, by rfl⟩ : syracuseStep 15565283 = 23347925) B23347925
theorem B10376855 : Blo 1919435 10376855 := bstep (se 1 (by rfl) ⟨7782641, by rfl⟩ : syracuseStep 10376855 = 15565283) B15565283
theorem B6917903 : Blo 1919435 6917903 := bstep (se 1 (by rfl) ⟨5188427, by rfl⟩ : syracuseStep 6917903 = 10376855) B10376855
theorem B4611935 : Blo 1919435 4611935 := bstep (se 1 (by rfl) ⟨3458951, by rfl⟩ : syracuseStep 4611935 = 6917903) B6917903
theorem B12298493 : Blo 1919435 12298493 := bstep (se 3 (by rfl) ⟨2305967, by rfl⟩ : syracuseStep 12298493 = 4611935) B4611935
theorem B8198995 : Blo 1919435 8198995 := bstep (se 1 (by rfl) ⟨6149246, by rfl⟩ : syracuseStep 8198995 = 12298493) B12298493
theorem B10931993 : Blo 1919435 10931993 := bstep (se 2 (by rfl) ⟨4099497, by rfl⟩ : syracuseStep 10931993 = 8198995) B8198995
theorem B7287995 : Blo 1919435 7287995 := bstep (se 1 (by rfl) ⟨5465996, by rfl⟩ : syracuseStep 7287995 = 10931993) B10931993
theorem B4858663 : Blo 1919435 4858663 := bstep (se 1 (by rfl) ⟨3643997, by rfl⟩ : syracuseStep 4858663 = 7287995) B7287995
theorem B6478217 : Blo 1919435 6478217 := bstep (se 2 (by rfl) ⟨2429331, by rfl⟩ : syracuseStep 6478217 = 4858663) B4858663
theorem B4318811 : Blo 1919435 4318811 := bstep (se 1 (by rfl) ⟨3239108, by rfl⟩ : syracuseStep 4318811 = 6478217) B6478217
theorem B2879207 : Blo 1919435 2879207 := bstep (se 1 (by rfl) ⟨2159405, by rfl⟩ : syracuseStep 2879207 = 4318811) B4318811
theorem B1919471 : Blo 1919435 1919471 := bstep (se 1 (by rfl) ⟨1439603, by rfl⟩ : syracuseStep 1919471 = 2879207) B2879207
theorem B2879213 : Blo 1919435 2879213 := bbase (se 3 (by rfl) ⟨539852, by rfl⟩ : syracuseStep 2879213 = 1079705) (by norm_num)
theorem B1919475 : Blo 1919435 1919475 := bstep (se 1 (by rfl) ⟨1439606, by rfl⟩ : syracuseStep 1919475 = 2879213) B2879213
theorem B4318829 : Blo 1919435 4318829 := bbase (se 3 (by rfl) ⟨809780, by rfl⟩ : syracuseStep 4318829 = 1619561) (by norm_num)
theorem B2879219 : Blo 1919435 2879219 := bstep (se 1 (by rfl) ⟨2159414, by rfl⟩ : syracuseStep 2879219 = 4318829) B4318829
theorem B1919479 : Blo 1919435 1919479 := bstep (se 1 (by rfl) ⟨1439609, by rfl⟩ : syracuseStep 1919479 = 2879219) B2879219
theorem B3644021 : Blo 1919435 3644021 := bbase (se 5 (by rfl) ⟨170813, by rfl⟩ : syracuseStep 3644021 = 341627) (by norm_num)
theorem B2429347 : Blo 1919435 2429347 := bstep (se 1 (by rfl) ⟨1822010, by rfl⟩ : syracuseStep 2429347 = 3644021) B3644021
theorem B3239129 : Blo 1919435 3239129 := bstep (se 2 (by rfl) ⟨1214673, by rfl⟩ : syracuseStep 3239129 = 2429347) B2429347
theorem B2159419 : Blo 1919435 2159419 := bstep (se 1 (by rfl) ⟨1619564, by rfl⟩ : syracuseStep 2159419 = 3239129) B3239129
theorem B2879225 : Blo 1919435 2879225 := bstep (se 2 (by rfl) ⟨1079709, by rfl⟩ : syracuseStep 2879225 = 2159419) B2159419
theorem B1919483 : Blo 1919435 1919483 := bstep (se 1 (by rfl) ⟨1439612, by rfl⟩ : syracuseStep 1919483 = 2879225) B2879225
theorem B2770309 : Blo 1919435 2770309 := bbase (se 4 (by rfl) ⟨259716, by rfl⟩ : syracuseStep 2770309 = 519433) (by norm_num)
theorem B3693745 : Blo 1919435 3693745 := bstep (se 2 (by rfl) ⟨1385154, by rfl⟩ : syracuseStep 3693745 = 2770309) B2770309
theorem B4924993 : Blo 1919435 4924993 := bstep (se 2 (by rfl) ⟨1846872, by rfl⟩ : syracuseStep 4924993 = 3693745) B3693745
theorem B6566657 : Blo 1919435 6566657 := bstep (se 2 (by rfl) ⟨2462496, by rfl⟩ : syracuseStep 6566657 = 4924993) B4924993
theorem B17511085 : Blo 1919435 17511085 := bstep (se 3 (by rfl) ⟨3283328, by rfl⟩ : syracuseStep 17511085 = 6566657) B6566657
theorem B93392453 : Blo 1919435 93392453 := bstep (se 4 (by rfl) ⟨8755542, by rfl⟩ : syracuseStep 93392453 = 17511085) B17511085
theorem B62261635 : Blo 1919435 62261635 := bstep (se 1 (by rfl) ⟨46696226, by rfl⟩ : syracuseStep 62261635 = 93392453) B93392453
theorem B83015513 : Blo 1919435 83015513 := bstep (se 2 (by rfl) ⟨31130817, by rfl⟩ : syracuseStep 83015513 = 62261635) B62261635
theorem B55343675 : Blo 1919435 55343675 := bstep (se 1 (by rfl) ⟨41507756, by rfl⟩ : syracuseStep 55343675 = 83015513) B83015513
theorem B36895783 : Blo 1919435 36895783 := bstep (se 1 (by rfl) ⟨27671837, by rfl⟩ : syracuseStep 36895783 = 55343675) B55343675
theorem B49194377 : Blo 1919435 49194377 := bstep (se 2 (by rfl) ⟨18447891, by rfl⟩ : syracuseStep 49194377 = 36895783) B36895783
theorem B32796251 : Blo 1919435 32796251 := bstep (se 1 (by rfl) ⟨24597188, by rfl⟩ : syracuseStep 32796251 = 49194377) B49194377
theorem B21864167 : Blo 1919435 21864167 := bstep (se 1 (by rfl) ⟨16398125, by rfl⟩ : syracuseStep 21864167 = 32796251) B32796251
theorem B14576111 : Blo 1919435 14576111 := bstep (se 1 (by rfl) ⟨10932083, by rfl⟩ : syracuseStep 14576111 = 21864167) B21864167
theorem B9717407 : Blo 1919435 9717407 := bstep (se 1 (by rfl) ⟨7288055, by rfl⟩ : syracuseStep 9717407 = 14576111) B14576111
theorem B6478271 : Blo 1919435 6478271 := bstep (se 1 (by rfl) ⟨4858703, by rfl⟩ : syracuseStep 6478271 = 9717407) B9717407
theorem B4318847 : Blo 1919435 4318847 := bstep (se 1 (by rfl) ⟨3239135, by rfl⟩ : syracuseStep 4318847 = 6478271) B6478271
theorem B2879231 : Blo 1919435 2879231 := bstep (se 1 (by rfl) ⟨2159423, by rfl⟩ : syracuseStep 2879231 = 4318847) B4318847
theorem B1919487 : Blo 1919435 1919487 := bstep (se 1 (by rfl) ⟨1439615, by rfl⟩ : syracuseStep 1919487 = 2879231) B2879231
theorem B2879237 : Blo 1919435 2879237 := bbase (se 4 (by rfl) ⟨269928, by rfl⟩ : syracuseStep 2879237 = 539857) (by norm_num)
theorem B1919491 : Blo 1919435 1919491 := bstep (se 1 (by rfl) ⟨1439618, by rfl⟩ : syracuseStep 1919491 = 2879237) B2879237
theorem B3239149 : Blo 1919435 3239149 := bbase (se 3 (by rfl) ⟨607340, by rfl⟩ : syracuseStep 3239149 = 1214681) (by norm_num)
theorem B4318865 : Blo 1919435 4318865 := bstep (se 2 (by rfl) ⟨1619574, by rfl⟩ : syracuseStep 4318865 = 3239149) B3239149
theorem B2879243 : Blo 1919435 2879243 := bstep (se 1 (by rfl) ⟨2159432, by rfl⟩ : syracuseStep 2879243 = 4318865) B4318865
theorem B1919495 : Blo 1919435 1919495 := bstep (se 1 (by rfl) ⟨1439621, by rfl⟩ : syracuseStep 1919495 = 2879243) B2879243
theorem B2159437 : Blo 1919435 2159437 := bbase (se 3 (by rfl) ⟨404894, by rfl⟩ : syracuseStep 2159437 = 809789) (by norm_num)
theorem B2879249 : Blo 1919435 2879249 := bstep (se 2 (by rfl) ⟨1079718, by rfl⟩ : syracuseStep 2879249 = 2159437) B2159437
theorem B1919499 : Blo 1919435 1919499 := bstep (se 1 (by rfl) ⟨1439624, by rfl⟩ : syracuseStep 1919499 = 2879249) B2879249
theorem B6478325 : Blo 1919435 6478325 := bbase (se 5 (by rfl) ⟨303671, by rfl⟩ : syracuseStep 6478325 = 607343) (by norm_num)
theorem B4318883 : Blo 1919435 4318883 := bstep (se 1 (by rfl) ⟨3239162, by rfl⟩ : syracuseStep 4318883 = 6478325) B6478325
theorem B2879255 : Blo 1919435 2879255 := bstep (se 1 (by rfl) ⟨2159441, by rfl⟩ : syracuseStep 2879255 = 4318883) B4318883
theorem B1919503 : Blo 1919435 1919503 := bstep (se 1 (by rfl) ⟨1439627, by rfl⟩ : syracuseStep 1919503 = 2879255) B2879255
theorem B2879261 : Blo 1919435 2879261 := bbase (se 3 (by rfl) ⟨539861, by rfl⟩ : syracuseStep 2879261 = 1079723) (by norm_num)
theorem B1919507 : Blo 1919435 1919507 := bstep (se 1 (by rfl) ⟨1439630, by rfl⟩ : syracuseStep 1919507 = 2879261) B2879261
theorem B4318901 : Blo 1919435 4318901 := bbase (se 5 (by rfl) ⟨202448, by rfl⟩ : syracuseStep 4318901 = 404897) (by norm_num)
theorem B2879267 : Blo 1919435 2879267 := bstep (se 1 (by rfl) ⟨2159450, by rfl⟩ : syracuseStep 2879267 = 4318901) B4318901
theorem B1919511 : Blo 1919435 1919511 := bstep (se 1 (by rfl) ⟨1439633, by rfl⟩ : syracuseStep 1919511 = 2879267) B2879267
theorem B10932245 : Blo 1919435 10932245 := bbase (se 6 (by rfl) ⟨256224, by rfl⟩ : syracuseStep 10932245 = 512449) (by norm_num)
theorem B7288163 : Blo 1919435 7288163 := bstep (se 1 (by rfl) ⟨5466122, by rfl⟩ : syracuseStep 7288163 = 10932245) B10932245
theorem B4858775 : Blo 1919435 4858775 := bstep (se 1 (by rfl) ⟨3644081, by rfl⟩ : syracuseStep 4858775 = 7288163) B7288163
theorem B3239183 : Blo 1919435 3239183 := bstep (se 1 (by rfl) ⟨2429387, by rfl⟩ : syracuseStep 3239183 = 4858775) B4858775
theorem B2159455 : Blo 1919435 2159455 := bstep (se 1 (by rfl) ⟨1619591, by rfl⟩ : syracuseStep 2159455 = 3239183) B3239183
theorem B2879273 : Blo 1919435 2879273 := bstep (se 2 (by rfl) ⟨1079727, by rfl⟩ : syracuseStep 2879273 = 2159455) B2159455
theorem B1919515 : Blo 1919435 1919515 := bstep (se 1 (by rfl) ⟨1439636, by rfl⟩ : syracuseStep 1919515 = 2879273) B2879273
theorem B5466133 : Blo 1919435 5466133 := bbase (se 6 (by rfl) ⟨128112, by rfl⟩ : syracuseStep 5466133 = 256225) (by norm_num)
theorem B7288177 : Blo 1919435 7288177 := bstep (se 2 (by rfl) ⟨2733066, by rfl⟩ : syracuseStep 7288177 = 5466133) B5466133
theorem B9717569 : Blo 1919435 9717569 := bstep (se 2 (by rfl) ⟨3644088, by rfl⟩ : syracuseStep 9717569 = 7288177) B7288177
theorem B6478379 : Blo 1919435 6478379 := bstep (se 1 (by rfl) ⟨4858784, by rfl⟩ : syracuseStep 6478379 = 9717569) B9717569
theorem B4318919 : Blo 1919435 4318919 := bstep (se 1 (by rfl) ⟨3239189, by rfl⟩ : syracuseStep 4318919 = 6478379) B6478379
theorem B2879279 : Blo 1919435 2879279 := bstep (se 1 (by rfl) ⟨2159459, by rfl⟩ : syracuseStep 2879279 = 4318919) B4318919
theorem B1919519 : Blo 1919435 1919519 := bstep (se 1 (by rfl) ⟨1439639, by rfl⟩ : syracuseStep 1919519 = 2879279) B2879279
theorem B2879285 : Blo 1919435 2879285 := bbase (se 5 (by rfl) ⟨134966, by rfl⟩ : syracuseStep 2879285 = 269933) (by norm_num)
theorem B1919523 : Blo 1919435 1919523 := bstep (se 1 (by rfl) ⟨1439642, by rfl⟩ : syracuseStep 1919523 = 2879285) B2879285
theorem B4858805 : Blo 1919435 4858805 := bbase (se 5 (by rfl) ⟨227756, by rfl⟩ : syracuseStep 4858805 = 455513) (by norm_num)
theorem B3239203 : Blo 1919435 3239203 := bstep (se 1 (by rfl) ⟨2429402, by rfl⟩ : syracuseStep 3239203 = 4858805) B4858805
theorem B4318937 : Blo 1919435 4318937 := bstep (se 2 (by rfl) ⟨1619601, by rfl⟩ : syracuseStep 4318937 = 3239203) B3239203
theorem B2879291 : Blo 1919435 2879291 := bstep (se 1 (by rfl) ⟨2159468, by rfl⟩ : syracuseStep 2879291 = 4318937) B4318937
theorem B1919527 : Blo 1919435 1919527 := bstep (se 1 (by rfl) ⟨1439645, by rfl⟩ : syracuseStep 1919527 = 2879291) B2879291
theorem B2159473 : Blo 1919435 2159473 := bbase (se 2 (by rfl) ⟨809802, by rfl⟩ : syracuseStep 2159473 = 1619605) (by norm_num)
theorem B2879297 : Blo 1919435 2879297 := bstep (se 2 (by rfl) ⟨1079736, by rfl⟩ : syracuseStep 2879297 = 2159473) B2159473
theorem B1919531 : Blo 1919435 1919531 := bstep (se 1 (by rfl) ⟨1439648, by rfl⟩ : syracuseStep 1919531 = 2879297) B2879297
theorem B8199269 : Blo 1919435 8199269 := bbase (se 4 (by rfl) ⟨768681, by rfl⟩ : syracuseStep 8199269 = 1537363) (by norm_num)
theorem B5466179 : Blo 1919435 5466179 := bstep (se 1 (by rfl) ⟨4099634, by rfl⟩ : syracuseStep 5466179 = 8199269) B8199269
theorem B3644119 : Blo 1919435 3644119 := bstep (se 1 (by rfl) ⟨2733089, by rfl⟩ : syracuseStep 3644119 = 5466179) B5466179
theorem B4858825 : Blo 1919435 4858825 := bstep (se 2 (by rfl) ⟨1822059, by rfl⟩ : syracuseStep 4858825 = 3644119) B3644119
theorem B6478433 : Blo 1919435 6478433 := bstep (se 2 (by rfl) ⟨2429412, by rfl⟩ : syracuseStep 6478433 = 4858825) B4858825
theorem B4318955 : Blo 1919435 4318955 := bstep (se 1 (by rfl) ⟨3239216, by rfl⟩ : syracuseStep 4318955 = 6478433) B6478433
theorem B2879303 : Blo 1919435 2879303 := bstep (se 1 (by rfl) ⟨2159477, by rfl⟩ : syracuseStep 2879303 = 4318955) B4318955
theorem B1919535 : Blo 1919435 1919535 := bstep (se 1 (by rfl) ⟨1439651, by rfl⟩ : syracuseStep 1919535 = 2879303) B2879303
theorem B2879309 : Blo 1919435 2879309 := bbase (se 3 (by rfl) ⟨539870, by rfl⟩ : syracuseStep 2879309 = 1079741) (by norm_num)
theorem B1919539 : Blo 1919435 1919539 := bstep (se 1 (by rfl) ⟨1439654, by rfl⟩ : syracuseStep 1919539 = 2879309) B2879309
theorem B4318973 : Blo 1919435 4318973 := bbase (se 3 (by rfl) ⟨809807, by rfl⟩ : syracuseStep 4318973 = 1619615) (by norm_num)
theorem B2879315 : Blo 1919435 2879315 := bstep (se 1 (by rfl) ⟨2159486, by rfl⟩ : syracuseStep 2879315 = 4318973) B4318973
theorem B1919543 : Blo 1919435 1919543 := bstep (se 1 (by rfl) ⟨1439657, by rfl⟩ : syracuseStep 1919543 = 2879315) B2879315
theorem B3239237 : Blo 1919435 3239237 := bbase (se 4 (by rfl) ⟨303678, by rfl⟩ : syracuseStep 3239237 = 607357) (by norm_num)
theorem B2159491 : Blo 1919435 2159491 := bstep (se 1 (by rfl) ⟨1619618, by rfl⟩ : syracuseStep 2159491 = 3239237) B3239237
theorem B2879321 : Blo 1919435 2879321 := bstep (se 2 (by rfl) ⟨1079745, by rfl⟩ : syracuseStep 2879321 = 2159491) B2159491
theorem B1919547 : Blo 1919435 1919547 := bstep (se 1 (by rfl) ⟨1439660, by rfl⟩ : syracuseStep 1919547 = 2879321) B2879321
theorem B14576597 : Blo 1919435 14576597 := bbase (se 7 (by rfl) ⟨170819, by rfl⟩ : syracuseStep 14576597 = 341639) (by norm_num)
theorem B9717731 : Blo 1919435 9717731 := bstep (se 1 (by rfl) ⟨7288298, by rfl⟩ : syracuseStep 9717731 = 14576597) B14576597
theorem B6478487 : Blo 1919435 6478487 := bstep (se 1 (by rfl) ⟨4858865, by rfl⟩ : syracuseStep 6478487 = 9717731) B9717731
theorem B4318991 : Blo 1919435 4318991 := bstep (se 1 (by rfl) ⟨3239243, by rfl⟩ : syracuseStep 4318991 = 6478487) B6478487
theorem B2879327 : Blo 1919435 2879327 := bstep (se 1 (by rfl) ⟨2159495, by rfl⟩ : syracuseStep 2879327 = 4318991) B4318991
theorem B1919551 : Blo 1919435 1919551 := bstep (se 1 (by rfl) ⟨1439663, by rfl⟩ : syracuseStep 1919551 = 2879327) B2879327
theorem B2879333 : Blo 1919435 2879333 := bbase (se 4 (by rfl) ⟨269937, by rfl⟩ : syracuseStep 2879333 = 539875) (by norm_num)
theorem B1919555 : Blo 1919435 1919555 := bstep (se 1 (by rfl) ⟨1439666, by rfl⟩ : syracuseStep 1919555 = 2879333) B2879333
theorem B3644165 : Blo 1919435 3644165 := bbase (se 4 (by rfl) ⟨341640, by rfl⟩ : syracuseStep 3644165 = 683281) (by norm_num)
theorem B2429443 : Blo 1919435 2429443 := bstep (se 1 (by rfl) ⟨1822082, by rfl⟩ : syracuseStep 2429443 = 3644165) B3644165
theorem B3239257 : Blo 1919435 3239257 := bstep (se 2 (by rfl) ⟨1214721, by rfl⟩ : syracuseStep 3239257 = 2429443) B2429443
theorem B4319009 : Blo 1919435 4319009 := bstep (se 2 (by rfl) ⟨1619628, by rfl⟩ : syracuseStep 4319009 = 3239257) B3239257
theorem B2879339 : Blo 1919435 2879339 := bstep (se 1 (by rfl) ⟨2159504, by rfl⟩ : syracuseStep 2879339 = 4319009) B4319009
theorem B1919559 : Blo 1919435 1919559 := bstep (se 1 (by rfl) ⟨1439669, by rfl⟩ : syracuseStep 1919559 = 2879339) B2879339
theorem B2159509 : Blo 1919435 2159509 := bbase (se 6 (by rfl) ⟨50613, by rfl⟩ : syracuseStep 2159509 = 101227) (by norm_num)
theorem B2879345 : Blo 1919435 2879345 := bstep (se 2 (by rfl) ⟨1079754, by rfl⟩ : syracuseStep 2879345 = 2159509) B2159509
theorem B1919563 : Blo 1919435 1919563 := bstep (se 1 (by rfl) ⟨1439672, by rfl⟩ : syracuseStep 1919563 = 2879345) B2879345
theorem B2429453 : Blo 1919435 2429453 := bbase (se 3 (by rfl) ⟨455522, by rfl⟩ : syracuseStep 2429453 = 911045) (by norm_num)
theorem B6478541 : Blo 1919435 6478541 := bstep (se 3 (by rfl) ⟨1214726, by rfl⟩ : syracuseStep 6478541 = 2429453) B2429453
theorem B4319027 : Blo 1919435 4319027 := bstep (se 1 (by rfl) ⟨3239270, by rfl⟩ : syracuseStep 4319027 = 6478541) B6478541
theorem B2879351 : Blo 1919435 2879351 := bstep (se 1 (by rfl) ⟨2159513, by rfl⟩ : syracuseStep 2879351 = 4319027) B4319027
theorem B1919567 : Blo 1919435 1919567 := bstep (se 1 (by rfl) ⟨1439675, by rfl⟩ : syracuseStep 1919567 = 2879351) B2879351
theorem B2879357 : Blo 1919435 2879357 := bbase (se 3 (by rfl) ⟨539879, by rfl⟩ : syracuseStep 2879357 = 1079759) (by norm_num)
theorem B1919571 : Blo 1919435 1919571 := bstep (se 1 (by rfl) ⟨1439678, by rfl⟩ : syracuseStep 1919571 = 2879357) B2879357
theorem B4319045 : Blo 1919435 4319045 := bbase (se 4 (by rfl) ⟨404910, by rfl⟩ : syracuseStep 4319045 = 809821) (by norm_num)
theorem B2879363 : Blo 1919435 2879363 := bstep (se 1 (by rfl) ⟨2159522, by rfl⟩ : syracuseStep 2879363 = 4319045) B4319045
theorem B1919575 : Blo 1919435 1919575 := bstep (se 1 (by rfl) ⟨1439681, by rfl⟩ : syracuseStep 1919575 = 2879363) B2879363
theorem B3074797 : Blo 1919435 3074797 := bbase (se 3 (by rfl) ⟨576524, by rfl⟩ : syracuseStep 3074797 = 1153049) (by norm_num)
theorem B4099729 : Blo 1919435 4099729 := bstep (se 2 (by rfl) ⟨1537398, by rfl⟩ : syracuseStep 4099729 = 3074797) B3074797
theorem B5466305 : Blo 1919435 5466305 := bstep (se 2 (by rfl) ⟨2049864, by rfl⟩ : syracuseStep 5466305 = 4099729) B4099729
theorem B3644203 : Blo 1919435 3644203 := bstep (se 1 (by rfl) ⟨2733152, by rfl⟩ : syracuseStep 3644203 = 5466305) B5466305
theorem B4858937 : Blo 1919435 4858937 := bstep (se 2 (by rfl) ⟨1822101, by rfl⟩ : syracuseStep 4858937 = 3644203) B3644203
theorem B3239291 : Blo 1919435 3239291 := bstep (se 1 (by rfl) ⟨2429468, by rfl⟩ : syracuseStep 3239291 = 4858937) B4858937
theorem B2159527 : Blo 1919435 2159527 := bstep (se 1 (by rfl) ⟨1619645, by rfl⟩ : syracuseStep 2159527 = 3239291) B3239291
theorem B2879369 : Blo 1919435 2879369 := bstep (se 2 (by rfl) ⟨1079763, by rfl⟩ : syracuseStep 2879369 = 2159527) B2159527
theorem B1919579 : Blo 1919435 1919579 := bstep (se 1 (by rfl) ⟨1439684, by rfl⟩ : syracuseStep 1919579 = 2879369) B2879369
theorem B9717893 : Blo 1919435 9717893 := bbase (se 4 (by rfl) ⟨911052, by rfl⟩ : syracuseStep 9717893 = 1822105) (by norm_num)
theorem B6478595 : Blo 1919435 6478595 := bstep (se 1 (by rfl) ⟨4858946, by rfl⟩ : syracuseStep 6478595 = 9717893) B9717893
theorem B4319063 : Blo 1919435 4319063 := bstep (se 1 (by rfl) ⟨3239297, by rfl⟩ : syracuseStep 4319063 = 6478595) B6478595
theorem B2879375 : Blo 1919435 2879375 := bstep (se 1 (by rfl) ⟨2159531, by rfl⟩ : syracuseStep 2879375 = 4319063) B4319063
theorem B1919583 : Blo 1919435 1919583 := bstep (se 1 (by rfl) ⟨1439687, by rfl⟩ : syracuseStep 1919583 = 2879375) B2879375
theorem B2879381 : Blo 1919435 2879381 := bbase (se 6 (by rfl) ⟨67485, by rfl⟩ : syracuseStep 2879381 = 134971) (by norm_num)
theorem B1919587 : Blo 1919435 1919587 := bstep (se 1 (by rfl) ⟨1439690, by rfl⟩ : syracuseStep 1919587 = 2879381) B2879381
theorem B2049877 : Blo 1919435 2049877 := bbase (se 9 (by rfl) ⟨6005, by rfl⟩ : syracuseStep 2049877 = 12011) (by norm_num)
theorem B10932677 : Blo 1919435 10932677 := bstep (se 4 (by rfl) ⟨1024938, by rfl⟩ : syracuseStep 10932677 = 2049877) B2049877
theorem B7288451 : Blo 1919435 7288451 := bstep (se 1 (by rfl) ⟨5466338, by rfl⟩ : syracuseStep 7288451 = 10932677) B10932677
theorem B4858967 : Blo 1919435 4858967 := bstep (se 1 (by rfl) ⟨3644225, by rfl⟩ : syracuseStep 4858967 = 7288451) B7288451
theorem B3239311 : Blo 1919435 3239311 := bstep (se 1 (by rfl) ⟨2429483, by rfl⟩ : syracuseStep 3239311 = 4858967) B4858967
theorem B4319081 : Blo 1919435 4319081 := bstep (se 2 (by rfl) ⟨1619655, by rfl⟩ : syracuseStep 4319081 = 3239311) B3239311
theorem B2879387 : Blo 1919435 2879387 := bstep (se 1 (by rfl) ⟨2159540, by rfl⟩ : syracuseStep 2879387 = 4319081) B4319081
theorem B1919591 : Blo 1919435 1919591 := bstep (se 1 (by rfl) ⟨1439693, by rfl⟩ : syracuseStep 1919591 = 2879387) B2879387
theorem B2159545 : Blo 1919435 2159545 := bbase (se 2 (by rfl) ⟨809829, by rfl⟩ : syracuseStep 2159545 = 1619659) (by norm_num)
theorem B2879393 : Blo 1919435 2879393 := bstep (se 2 (by rfl) ⟨1079772, by rfl⟩ : syracuseStep 2879393 = 2159545) B2159545
theorem B1919595 : Blo 1919435 1919595 := bstep (se 1 (by rfl) ⟨1439696, by rfl⟩ : syracuseStep 1919595 = 2879393) B2879393
theorem B3891581 : Blo 1919435 3891581 := bbase (se 3 (by rfl) ⟨729671, by rfl⟩ : syracuseStep 3891581 = 1459343) (by norm_num)
theorem B2594387 : Blo 1919435 2594387 := bstep (se 1 (by rfl) ⟨1945790, by rfl⟩ : syracuseStep 2594387 = 3891581) B3891581
theorem B6918365 : Blo 1919435 6918365 := bstep (se 3 (by rfl) ⟨1297193, by rfl⟩ : syracuseStep 6918365 = 2594387) B2594387
theorem B4612243 : Blo 1919435 4612243 := bstep (se 1 (by rfl) ⟨3459182, by rfl⟩ : syracuseStep 4612243 = 6918365) B6918365
theorem B6149657 : Blo 1919435 6149657 := bstep (se 2 (by rfl) ⟨2306121, by rfl⟩ : syracuseStep 6149657 = 4612243) B4612243
theorem B4099771 : Blo 1919435 4099771 := bstep (se 1 (by rfl) ⟨3074828, by rfl⟩ : syracuseStep 4099771 = 6149657) B6149657
theorem B5466361 : Blo 1919435 5466361 := bstep (se 2 (by rfl) ⟨2049885, by rfl⟩ : syracuseStep 5466361 = 4099771) B4099771
theorem B7288481 : Blo 1919435 7288481 := bstep (se 2 (by rfl) ⟨2733180, by rfl⟩ : syracuseStep 7288481 = 5466361) B5466361
theorem B4858987 : Blo 1919435 4858987 := bstep (se 1 (by rfl) ⟨3644240, by rfl⟩ : syracuseStep 4858987 = 7288481) B7288481
theorem B6478649 : Blo 1919435 6478649 := bstep (se 2 (by rfl) ⟨2429493, by rfl⟩ : syracuseStep 6478649 = 4858987) B4858987
theorem B4319099 : Blo 1919435 4319099 := bstep (se 1 (by rfl) ⟨3239324, by rfl⟩ : syracuseStep 4319099 = 6478649) B6478649
theorem B2879399 : Blo 1919435 2879399 := bstep (se 1 (by rfl) ⟨2159549, by rfl⟩ : syracuseStep 2879399 = 4319099) B4319099
theorem B1919599 : Blo 1919435 1919599 := bstep (se 1 (by rfl) ⟨1439699, by rfl⟩ : syracuseStep 1919599 = 2879399) B2879399
theorem B2879405 : Blo 1919435 2879405 := bbase (se 3 (by rfl) ⟨539888, by rfl⟩ : syracuseStep 2879405 = 1079777) (by norm_num)
theorem B1919603 : Blo 1919435 1919603 := bstep (se 1 (by rfl) ⟨1439702, by rfl⟩ : syracuseStep 1919603 = 2879405) B2879405
theorem B4319117 : Blo 1919435 4319117 := bbase (se 3 (by rfl) ⟨809834, by rfl⟩ : syracuseStep 4319117 = 1619669) (by norm_num)
theorem B2879411 : Blo 1919435 2879411 := bstep (se 1 (by rfl) ⟨2159558, by rfl⟩ : syracuseStep 2879411 = 4319117) B4319117
theorem B1919607 : Blo 1919435 1919607 := bstep (se 1 (by rfl) ⟨1439705, by rfl⟩ : syracuseStep 1919607 = 2879411) B2879411
theorem B2429509 : Blo 1919435 2429509 := bbase (se 4 (by rfl) ⟨227766, by rfl⟩ : syracuseStep 2429509 = 455533) (by norm_num)
theorem B3239345 : Blo 1919435 3239345 := bstep (se 2 (by rfl) ⟨1214754, by rfl⟩ : syracuseStep 3239345 = 2429509) B2429509
theorem B2159563 : Blo 1919435 2159563 := bstep (se 1 (by rfl) ⟨1619672, by rfl⟩ : syracuseStep 2159563 = 3239345) B3239345
theorem B2879417 : Blo 1919435 2879417 := bstep (se 2 (by rfl) ⟨1079781, by rfl⟩ : syracuseStep 2879417 = 2159563) B2159563
theorem B1919611 : Blo 1919435 1919611 := bstep (se 1 (by rfl) ⟨1439708, by rfl⟩ : syracuseStep 1919611 = 2879417) B2879417
theorem B6918421 : Blo 1919435 6918421 := bbase (se 6 (by rfl) ⟨162150, by rfl⟩ : syracuseStep 6918421 = 324301) (by norm_num)
theorem B9224561 : Blo 1919435 9224561 := bstep (se 2 (by rfl) ⟨3459210, by rfl⟩ : syracuseStep 9224561 = 6918421) B6918421
theorem B24598829 : Blo 1919435 24598829 := bstep (se 3 (by rfl) ⟨4612280, by rfl⟩ : syracuseStep 24598829 = 9224561) B9224561
theorem B16399219 : Blo 1919435 16399219 := bstep (se 1 (by rfl) ⟨12299414, by rfl⟩ : syracuseStep 16399219 = 24598829) B24598829
theorem B21865625 : Blo 1919435 21865625 := bstep (se 2 (by rfl) ⟨8199609, by rfl⟩ : syracuseStep 21865625 = 16399219) B16399219
theorem B14577083 : Blo 1919435 14577083 := bstep (se 1 (by rfl) ⟨10932812, by rfl⟩ : syracuseStep 14577083 = 21865625) B21865625
theorem B9718055 : Blo 1919435 9718055 := bstep (se 1 (by rfl) ⟨7288541, by rfl⟩ : syracuseStep 9718055 = 14577083) B14577083
theorem B6478703 : Blo 1919435 6478703 := bstep (se 1 (by rfl) ⟨4859027, by rfl⟩ : syracuseStep 6478703 = 9718055) B9718055
theorem B4319135 : Blo 1919435 4319135 := bstep (se 1 (by rfl) ⟨3239351, by rfl⟩ : syracuseStep 4319135 = 6478703) B6478703
theorem B2879423 : Blo 1919435 2879423 := bstep (se 1 (by rfl) ⟨2159567, by rfl⟩ : syracuseStep 2879423 = 4319135) B4319135
theorem B1919615 : Blo 1919435 1919615 := bstep (se 1 (by rfl) ⟨1439711, by rfl⟩ : syracuseStep 1919615 = 2879423) B2879423
theorem B2879429 : Blo 1919435 2879429 := bbase (se 4 (by rfl) ⟨269946, by rfl⟩ : syracuseStep 2879429 = 539893) (by norm_num)
theorem B1919619 : Blo 1919435 1919619 := bstep (se 1 (by rfl) ⟨1439714, by rfl⟩ : syracuseStep 1919619 = 2879429) B2879429
theorem B3239365 : Blo 1919435 3239365 := bbase (se 4 (by rfl) ⟨303690, by rfl⟩ : syracuseStep 3239365 = 607381) (by norm_num)
theorem B4319153 : Blo 1919435 4319153 := bstep (se 2 (by rfl) ⟨1619682, by rfl⟩ : syracuseStep 4319153 = 3239365) B3239365
theorem B2879435 : Blo 1919435 2879435 := bstep (se 1 (by rfl) ⟨2159576, by rfl⟩ : syracuseStep 2879435 = 4319153) B4319153
theorem B1919623 : Blo 1919435 1919623 := bstep (se 1 (by rfl) ⟨1439717, by rfl⟩ : syracuseStep 1919623 = 2879435) B2879435
theorem B2159581 : Blo 1919435 2159581 := bbase (se 3 (by rfl) ⟨404921, by rfl⟩ : syracuseStep 2159581 = 809843) (by norm_num)
theorem B2879441 : Blo 1919435 2879441 := bstep (se 2 (by rfl) ⟨1079790, by rfl⟩ : syracuseStep 2879441 = 2159581) B2159581
theorem B1919627 : Blo 1919435 1919627 := bstep (se 1 (by rfl) ⟨1439720, by rfl⟩ : syracuseStep 1919627 = 2879441) B2879441
theorem B6478757 : Blo 1919435 6478757 := bbase (se 4 (by rfl) ⟨607383, by rfl⟩ : syracuseStep 6478757 = 1214767) (by norm_num)
theorem B4319171 : Blo 1919435 4319171 := bstep (se 1 (by rfl) ⟨3239378, by rfl⟩ : syracuseStep 4319171 = 6478757) B6478757
theorem B2879447 : Blo 1919435 2879447 := bstep (se 1 (by rfl) ⟨2159585, by rfl⟩ : syracuseStep 2879447 = 4319171) B4319171
theorem B1919631 : Blo 1919435 1919631 := bstep (se 1 (by rfl) ⟨1439723, by rfl⟩ : syracuseStep 1919631 = 2879447) B2879447
theorem B2879453 : Blo 1919435 2879453 := bbase (se 3 (by rfl) ⟨539897, by rfl⟩ : syracuseStep 2879453 = 1079795) (by norm_num)
theorem B1919635 : Blo 1919435 1919635 := bstep (se 1 (by rfl) ⟨1439726, by rfl⟩ : syracuseStep 1919635 = 2879453) B2879453
theorem B4319189 : Blo 1919435 4319189 := bbase (se 7 (by rfl) ⟨50615, by rfl⟩ : syracuseStep 4319189 = 101231) (by norm_num)
theorem B2879459 : Blo 1919435 2879459 := bstep (se 1 (by rfl) ⟨2159594, by rfl⟩ : syracuseStep 2879459 = 4319189) B4319189
theorem B1919639 : Blo 1919435 1919639 := bstep (se 1 (by rfl) ⟨1439729, by rfl⟩ : syracuseStep 1919639 = 2879459) B2879459
theorem B4612349 : Blo 1919435 4612349 := bbase (se 3 (by rfl) ⟨864815, by rfl⟩ : syracuseStep 4612349 = 1729631) (by norm_num)
theorem B12299597 : Blo 1919435 12299597 := bstep (se 3 (by rfl) ⟨2306174, by rfl⟩ : syracuseStep 12299597 = 4612349) B4612349
theorem B8199731 : Blo 1919435 8199731 := bstep (se 1 (by rfl) ⟨6149798, by rfl⟩ : syracuseStep 8199731 = 12299597) B12299597
theorem B5466487 : Blo 1919435 5466487 := bstep (se 1 (by rfl) ⟨4099865, by rfl⟩ : syracuseStep 5466487 = 8199731) B8199731
theorem B7288649 : Blo 1919435 7288649 := bstep (se 2 (by rfl) ⟨2733243, by rfl⟩ : syracuseStep 7288649 = 5466487) B5466487
theorem B4859099 : Blo 1919435 4859099 := bstep (se 1 (by rfl) ⟨3644324, by rfl⟩ : syracuseStep 4859099 = 7288649) B7288649
theorem B3239399 : Blo 1919435 3239399 := bstep (se 1 (by rfl) ⟨2429549, by rfl⟩ : syracuseStep 3239399 = 4859099) B4859099
theorem B2159599 : Blo 1919435 2159599 := bstep (se 1 (by rfl) ⟨1619699, by rfl⟩ : syracuseStep 2159599 = 3239399) B3239399
theorem B2879465 : Blo 1919435 2879465 := bstep (se 2 (by rfl) ⟨1079799, by rfl⟩ : syracuseStep 2879465 = 2159599) B2159599
theorem B1919643 : Blo 1919435 1919643 := bstep (se 1 (by rfl) ⟨1439732, by rfl⟩ : syracuseStep 1919643 = 2879465) B2879465
theorem B3459269 : Blo 1919435 3459269 := bbase (se 4 (by rfl) ⟨324306, by rfl⟩ : syracuseStep 3459269 = 648613) (by norm_num)
theorem B2306179 : Blo 1919435 2306179 := bstep (se 1 (by rfl) ⟨1729634, by rfl⟩ : syracuseStep 2306179 = 3459269) B3459269
theorem B3074905 : Blo 1919435 3074905 := bstep (se 2 (by rfl) ⟨1153089, by rfl⟩ : syracuseStep 3074905 = 2306179) B2306179
theorem B16399493 : Blo 1919435 16399493 := bstep (se 4 (by rfl) ⟨1537452, by rfl⟩ : syracuseStep 16399493 = 3074905) B3074905
theorem B10932995 : Blo 1919435 10932995 := bstep (se 1 (by rfl) ⟨8199746, by rfl⟩ : syracuseStep 10932995 = 16399493) B16399493
theorem B7288663 : Blo 1919435 7288663 := bstep (se 1 (by rfl) ⟨5466497, by rfl⟩ : syracuseStep 7288663 = 10932995) B10932995
theorem B9718217 : Blo 1919435 9718217 := bstep (se 2 (by rfl) ⟨3644331, by rfl⟩ : syracuseStep 9718217 = 7288663) B7288663
theorem B6478811 : Blo 1919435 6478811 := bstep (se 1 (by rfl) ⟨4859108, by rfl⟩ : syracuseStep 6478811 = 9718217) B9718217
theorem B4319207 : Blo 1919435 4319207 := bstep (se 1 (by rfl) ⟨3239405, by rfl⟩ : syracuseStep 4319207 = 6478811) B6478811
theorem B2879471 : Blo 1919435 2879471 := bstep (se 1 (by rfl) ⟨2159603, by rfl⟩ : syracuseStep 2879471 = 4319207) B4319207
theorem B1919647 : Blo 1919435 1919647 := bstep (se 1 (by rfl) ⟨1439735, by rfl⟩ : syracuseStep 1919647 = 2879471) B2879471
theorem B2879477 : Blo 1919435 2879477 := bbase (se 5 (by rfl) ⟨134975, by rfl⟩ : syracuseStep 2879477 = 269951) (by norm_num)
theorem B1919651 : Blo 1919435 1919651 := bstep (se 1 (by rfl) ⟨1439738, by rfl⟩ : syracuseStep 1919651 = 2879477) B2879477
theorem B2306189 : Blo 1919435 2306189 := bbase (se 3 (by rfl) ⟨432410, by rfl⟩ : syracuseStep 2306189 = 864821) (by norm_num)
theorem B6149837 : Blo 1919435 6149837 := bstep (se 3 (by rfl) ⟨1153094, by rfl⟩ : syracuseStep 6149837 = 2306189) B2306189
theorem B4099891 : Blo 1919435 4099891 := bstep (se 1 (by rfl) ⟨3074918, by rfl⟩ : syracuseStep 4099891 = 6149837) B6149837
theorem B5466521 : Blo 1919435 5466521 := bstep (se 2 (by rfl) ⟨2049945, by rfl⟩ : syracuseStep 5466521 = 4099891) B4099891
theorem B3644347 : Blo 1919435 3644347 := bstep (se 1 (by rfl) ⟨2733260, by rfl⟩ : syracuseStep 3644347 = 5466521) B5466521
theorem B4859129 : Blo 1919435 4859129 := bstep (se 2 (by rfl) ⟨1822173, by rfl⟩ : syracuseStep 4859129 = 3644347) B3644347
theorem B3239419 : Blo 1919435 3239419 := bstep (se 1 (by rfl) ⟨2429564, by rfl⟩ : syracuseStep 3239419 = 4859129) B4859129
theorem B4319225 : Blo 1919435 4319225 := bstep (se 2 (by rfl) ⟨1619709, by rfl⟩ : syracuseStep 4319225 = 3239419) B3239419
theorem B2879483 : Blo 1919435 2879483 := bstep (se 1 (by rfl) ⟨2159612, by rfl⟩ : syracuseStep 2879483 = 4319225) B4319225
theorem B1919655 : Blo 1919435 1919655 := bstep (se 1 (by rfl) ⟨1439741, by rfl⟩ : syracuseStep 1919655 = 2879483) B2879483
theorem B2159617 : Blo 1919435 2159617 := bbase (se 2 (by rfl) ⟨809856, by rfl⟩ : syracuseStep 2159617 = 1619713) (by norm_num)
theorem B2879489 : Blo 1919435 2879489 := bstep (se 2 (by rfl) ⟨1079808, by rfl⟩ : syracuseStep 2879489 = 2159617) B2159617
theorem B1919659 : Blo 1919435 1919659 := bstep (se 1 (by rfl) ⟨1439744, by rfl⟩ : syracuseStep 1919659 = 2879489) B2879489
theorem B4859149 : Blo 1919435 4859149 := bbase (se 3 (by rfl) ⟨911090, by rfl⟩ : syracuseStep 4859149 = 1822181) (by norm_num)
theorem B6478865 : Blo 1919435 6478865 := bstep (se 2 (by rfl) ⟨2429574, by rfl⟩ : syracuseStep 6478865 = 4859149) B4859149
theorem B4319243 : Blo 1919435 4319243 := bstep (se 1 (by rfl) ⟨3239432, by rfl⟩ : syracuseStep 4319243 = 6478865) B6478865
theorem B2879495 : Blo 1919435 2879495 := bstep (se 1 (by rfl) ⟨2159621, by rfl⟩ : syracuseStep 2879495 = 4319243) B4319243
theorem B1919663 : Blo 1919435 1919663 := bstep (se 1 (by rfl) ⟨1439747, by rfl⟩ : syracuseStep 1919663 = 2879495) B2879495
theorem B2879501 : Blo 1919435 2879501 := bbase (se 3 (by rfl) ⟨539906, by rfl⟩ : syracuseStep 2879501 = 1079813) (by norm_num)
theorem B1919667 : Blo 1919435 1919667 := bstep (se 1 (by rfl) ⟨1439750, by rfl⟩ : syracuseStep 1919667 = 2879501) B2879501
theorem B4319261 : Blo 1919435 4319261 := bbase (se 3 (by rfl) ⟨809861, by rfl⟩ : syracuseStep 4319261 = 1619723) (by norm_num)
theorem B2879507 : Blo 1919435 2879507 := bstep (se 1 (by rfl) ⟨2159630, by rfl⟩ : syracuseStep 2879507 = 4319261) B4319261
theorem B1919671 : Blo 1919435 1919671 := bstep (se 1 (by rfl) ⟨1439753, by rfl⟩ : syracuseStep 1919671 = 2879507) B2879507
theorem B3239453 : Blo 1919435 3239453 := bbase (se 3 (by rfl) ⟨607397, by rfl⟩ : syracuseStep 3239453 = 1214795) (by norm_num)
theorem B2159635 : Blo 1919435 2159635 := bstep (se 1 (by rfl) ⟨1619726, by rfl⟩ : syracuseStep 2159635 = 3239453) B3239453
theorem B2879513 : Blo 1919435 2879513 := bstep (se 2 (by rfl) ⟨1079817, by rfl⟩ : syracuseStep 2879513 = 2159635) B2159635
theorem B1919675 : Blo 1919435 1919675 := bstep (se 1 (by rfl) ⟨1439756, by rfl⟩ : syracuseStep 1919675 = 2879513) B2879513
theorem B9224869 : Blo 1919435 9224869 := bbase (se 4 (by rfl) ⟨864831, by rfl⟩ : syracuseStep 9224869 = 1729663) (by norm_num)
theorem B12299825 : Blo 1919435 12299825 := bstep (se 2 (by rfl) ⟨4612434, by rfl⟩ : syracuseStep 12299825 = 9224869) B9224869
theorem B8199883 : Blo 1919435 8199883 := bstep (se 1 (by rfl) ⟨6149912, by rfl⟩ : syracuseStep 8199883 = 12299825) B12299825
theorem B10933177 : Blo 1919435 10933177 := bstep (se 2 (by rfl) ⟨4099941, by rfl⟩ : syracuseStep 10933177 = 8199883) B8199883
theorem B14577569 : Blo 1919435 14577569 := bstep (se 2 (by rfl) ⟨5466588, by rfl⟩ : syracuseStep 14577569 = 10933177) B10933177
theorem B9718379 : Blo 1919435 9718379 := bstep (se 1 (by rfl) ⟨7288784, by rfl⟩ : syracuseStep 9718379 = 14577569) B14577569
theorem B6478919 : Blo 1919435 6478919 := bstep (se 1 (by rfl) ⟨4859189, by rfl⟩ : syracuseStep 6478919 = 9718379) B9718379
theorem B4319279 : Blo 1919435 4319279 := bstep (se 1 (by rfl) ⟨3239459, by rfl⟩ : syracuseStep 4319279 = 6478919) B6478919
theorem B2879519 : Blo 1919435 2879519 := bstep (se 1 (by rfl) ⟨2159639, by rfl⟩ : syracuseStep 2879519 = 4319279) B4319279
theorem B1919679 : Blo 1919435 1919679 := bstep (se 1 (by rfl) ⟨1439759, by rfl⟩ : syracuseStep 1919679 = 2879519) B2879519
theorem B2879525 : Blo 1919435 2879525 := bbase (se 4 (by rfl) ⟨269955, by rfl⟩ : syracuseStep 2879525 = 539911) (by norm_num)
theorem B1919683 : Blo 1919435 1919683 := bstep (se 1 (by rfl) ⟨1439762, by rfl⟩ : syracuseStep 1919683 = 2879525) B2879525
theorem B2429605 : Blo 1919435 2429605 := bbase (se 4 (by rfl) ⟨227775, by rfl⟩ : syracuseStep 2429605 = 455551) (by norm_num)
theorem B3239473 : Blo 1919435 3239473 := bstep (se 2 (by rfl) ⟨1214802, by rfl⟩ : syracuseStep 3239473 = 2429605) B2429605
theorem B4319297 : Blo 1919435 4319297 := bstep (se 2 (by rfl) ⟨1619736, by rfl⟩ : syracuseStep 4319297 = 3239473) B3239473
theorem B2879531 : Blo 1919435 2879531 := bstep (se 1 (by rfl) ⟨2159648, by rfl⟩ : syracuseStep 2879531 = 4319297) B4319297
theorem B1919687 : Blo 1919435 1919687 := bstep (se 1 (by rfl) ⟨1439765, by rfl⟩ : syracuseStep 1919687 = 2879531) B2879531
theorem B2159653 : Blo 1919435 2159653 := bbase (se 4 (by rfl) ⟨202467, by rfl⟩ : syracuseStep 2159653 = 404935) (by norm_num)
theorem B2879537 : Blo 1919435 2879537 := bstep (se 2 (by rfl) ⟨1079826, by rfl⟩ : syracuseStep 2879537 = 2159653) B2159653
theorem B1919691 : Blo 1919435 1919691 := bstep (se 1 (by rfl) ⟨1439768, by rfl⟩ : syracuseStep 1919691 = 2879537) B2879537
theorem B2306237 : Blo 1919435 2306237 := bbase (se 3 (by rfl) ⟨432419, by rfl⟩ : syracuseStep 2306237 = 864839) (by norm_num)
theorem B6149965 : Blo 1919435 6149965 := bstep (se 3 (by rfl) ⟨1153118, by rfl⟩ : syracuseStep 6149965 = 2306237) B2306237
theorem B8199953 : Blo 1919435 8199953 := bstep (se 2 (by rfl) ⟨3074982, by rfl⟩ : syracuseStep 8199953 = 6149965) B6149965
theorem B5466635 : Blo 1919435 5466635 := bstep (se 1 (by rfl) ⟨4099976, by rfl⟩ : syracuseStep 5466635 = 8199953) B8199953
theorem B3644423 : Blo 1919435 3644423 := bstep (se 1 (by rfl) ⟨2733317, by rfl⟩ : syracuseStep 3644423 = 5466635) B5466635
theorem B2429615 : Blo 1919435 2429615 := bstep (se 1 (by rfl) ⟨1822211, by rfl⟩ : syracuseStep 2429615 = 3644423) B3644423
theorem B6478973 : Blo 1919435 6478973 := bstep (se 3 (by rfl) ⟨1214807, by rfl⟩ : syracuseStep 6478973 = 2429615) B2429615
theorem B4319315 : Blo 1919435 4319315 := bstep (se 1 (by rfl) ⟨3239486, by rfl⟩ : syracuseStep 4319315 = 6478973) B6478973
theorem B2879543 : Blo 1919435 2879543 := bstep (se 1 (by rfl) ⟨2159657, by rfl⟩ : syracuseStep 2879543 = 4319315) B4319315
theorem B1919695 : Blo 1919435 1919695 := bstep (se 1 (by rfl) ⟨1439771, by rfl⟩ : syracuseStep 1919695 = 2879543) B2879543
theorem B2879549 : Blo 1919435 2879549 := bbase (se 3 (by rfl) ⟨539915, by rfl⟩ : syracuseStep 2879549 = 1079831) (by norm_num)
theorem B1919699 : Blo 1919435 1919699 := bstep (se 1 (by rfl) ⟨1439774, by rfl⟩ : syracuseStep 1919699 = 2879549) B2879549
theorem B4319333 : Blo 1919435 4319333 := bbase (se 4 (by rfl) ⟨404937, by rfl⟩ : syracuseStep 4319333 = 809875) (by norm_num)
theorem B2879555 : Blo 1919435 2879555 := bstep (se 1 (by rfl) ⟨2159666, by rfl⟩ : syracuseStep 2879555 = 4319333) B4319333
theorem B1919703 : Blo 1919435 1919703 := bstep (se 1 (by rfl) ⟨1439777, by rfl⟩ : syracuseStep 1919703 = 2879555) B2879555
theorem B4859261 : Blo 1919435 4859261 := bbase (se 3 (by rfl) ⟨911111, by rfl⟩ : syracuseStep 4859261 = 1822223) (by norm_num)
theorem B3239507 : Blo 1919435 3239507 := bstep (se 1 (by rfl) ⟨2429630, by rfl⟩ : syracuseStep 3239507 = 4859261) B4859261
theorem B2159671 : Blo 1919435 2159671 := bstep (se 1 (by rfl) ⟨1619753, by rfl⟩ : syracuseStep 2159671 = 3239507) B3239507
theorem B2879561 : Blo 1919435 2879561 := bstep (se 2 (by rfl) ⟨1079835, by rfl⟩ : syracuseStep 2879561 = 2159671) B2159671
theorem B1919707 : Blo 1919435 1919707 := bstep (se 1 (by rfl) ⟨1439780, by rfl⟩ : syracuseStep 1919707 = 2879561) B2879561
theorem B3644453 : Blo 1919435 3644453 := bbase (se 4 (by rfl) ⟨341667, by rfl⟩ : syracuseStep 3644453 = 683335) (by norm_num)
theorem B9718541 : Blo 1919435 9718541 := bstep (se 3 (by rfl) ⟨1822226, by rfl⟩ : syracuseStep 9718541 = 3644453) B3644453
theorem B6479027 : Blo 1919435 6479027 := bstep (se 1 (by rfl) ⟨4859270, by rfl⟩ : syracuseStep 6479027 = 9718541) B9718541
theorem B4319351 : Blo 1919435 4319351 := bstep (se 1 (by rfl) ⟨3239513, by rfl⟩ : syracuseStep 4319351 = 6479027) B6479027
theorem B2879567 : Blo 1919435 2879567 := bstep (se 1 (by rfl) ⟨2159675, by rfl⟩ : syracuseStep 2879567 = 4319351) B4319351
theorem B1919711 : Blo 1919435 1919711 := bstep (se 1 (by rfl) ⟨1439783, by rfl⟩ : syracuseStep 1919711 = 2879567) B2879567
theorem B2879573 : Blo 1919435 2879573 := bbase (se 8 (by rfl) ⟨16872, by rfl⟩ : syracuseStep 2879573 = 33745) (by norm_num)
theorem B1919715 : Blo 1919435 1919715 := bstep (se 1 (by rfl) ⟨1439786, by rfl⟩ : syracuseStep 1919715 = 2879573) B2879573
theorem B2594549 : Blo 1919435 2594549 := bbase (se 5 (by rfl) ⟨121619, by rfl⟩ : syracuseStep 2594549 = 243239) (by norm_num)
theorem B6918797 : Blo 1919435 6918797 := bstep (se 3 (by rfl) ⟨1297274, by rfl⟩ : syracuseStep 6918797 = 2594549) B2594549
theorem B18450125 : Blo 1919435 18450125 := bstep (se 3 (by rfl) ⟨3459398, by rfl⟩ : syracuseStep 18450125 = 6918797) B6918797
theorem B12300083 : Blo 1919435 12300083 := bstep (se 1 (by rfl) ⟨9225062, by rfl⟩ : syracuseStep 12300083 = 18450125) B18450125
theorem B8200055 : Blo 1919435 8200055 := bstep (se 1 (by rfl) ⟨6150041, by rfl⟩ : syracuseStep 8200055 = 12300083) B12300083
theorem B5466703 : Blo 1919435 5466703 := bstep (se 1 (by rfl) ⟨4100027, by rfl⟩ : syracuseStep 5466703 = 8200055) B8200055
theorem B7288937 : Blo 1919435 7288937 := bstep (se 2 (by rfl) ⟨2733351, by rfl⟩ : syracuseStep 7288937 = 5466703) B5466703
theorem B4859291 : Blo 1919435 4859291 := bstep (se 1 (by rfl) ⟨3644468, by rfl⟩ : syracuseStep 4859291 = 7288937) B7288937
theorem B3239527 : Blo 1919435 3239527 := bstep (se 1 (by rfl) ⟨2429645, by rfl⟩ : syracuseStep 3239527 = 4859291) B4859291
theorem B4319369 : Blo 1919435 4319369 := bstep (se 2 (by rfl) ⟨1619763, by rfl⟩ : syracuseStep 4319369 = 3239527) B3239527
theorem B2879579 : Blo 1919435 2879579 := bstep (se 1 (by rfl) ⟨2159684, by rfl⟩ : syracuseStep 2879579 = 4319369) B4319369
theorem B1919719 : Blo 1919435 1919719 := bstep (se 1 (by rfl) ⟨1439789, by rfl⟩ : syracuseStep 1919719 = 2879579) B2879579
theorem B2159689 : Blo 1919435 2159689 := bbase (se 2 (by rfl) ⟨809883, by rfl⟩ : syracuseStep 2159689 = 1619767) (by norm_num)
theorem B2879585 : Blo 1919435 2879585 := bstep (se 2 (by rfl) ⟨1079844, by rfl⟩ : syracuseStep 2879585 = 2159689) B2159689
theorem B1919723 : Blo 1919435 1919723 := bstep (se 1 (by rfl) ⟨1439792, by rfl⟩ : syracuseStep 1919723 = 2879585) B2879585
theorem B3459413 : Blo 1919435 3459413 := bbase (se 10 (by rfl) ⟨5067, by rfl⟩ : syracuseStep 3459413 = 10135) (by norm_num)
theorem B2306275 : Blo 1919435 2306275 := bstep (se 1 (by rfl) ⟨1729706, by rfl⟩ : syracuseStep 2306275 = 3459413) B3459413
theorem B12300133 : Blo 1919435 12300133 := bstep (se 4 (by rfl) ⟨1153137, by rfl⟩ : syracuseStep 12300133 = 2306275) B2306275
theorem B16400177 : Blo 1919435 16400177 := bstep (se 2 (by rfl) ⟨6150066, by rfl⟩ : syracuseStep 16400177 = 12300133) B12300133
theorem B10933451 : Blo 1919435 10933451 := bstep (se 1 (by rfl) ⟨8200088, by rfl⟩ : syracuseStep 10933451 = 16400177) B16400177
theorem B7288967 : Blo 1919435 7288967 := bstep (se 1 (by rfl) ⟨5466725, by rfl⟩ : syracuseStep 7288967 = 10933451) B10933451
theorem B4859311 : Blo 1919435 4859311 := bstep (se 1 (by rfl) ⟨3644483, by rfl⟩ : syracuseStep 4859311 = 7288967) B7288967
theorem B6479081 : Blo 1919435 6479081 := bstep (se 2 (by rfl) ⟨2429655, by rfl⟩ : syracuseStep 6479081 = 4859311) B4859311
theorem B4319387 : Blo 1919435 4319387 := bstep (se 1 (by rfl) ⟨3239540, by rfl⟩ : syracuseStep 4319387 = 6479081) B6479081
theorem B2879591 : Blo 1919435 2879591 := bstep (se 1 (by rfl) ⟨2159693, by rfl⟩ : syracuseStep 2879591 = 4319387) B4319387
theorem B1919727 : Blo 1919435 1919727 := bstep (se 1 (by rfl) ⟨1439795, by rfl⟩ : syracuseStep 1919727 = 2879591) B2879591
theorem B2879597 : Blo 1919435 2879597 := bbase (se 3 (by rfl) ⟨539924, by rfl⟩ : syracuseStep 2879597 = 1079849) (by norm_num)
theorem B1919731 : Blo 1919435 1919731 := bstep (se 1 (by rfl) ⟨1439798, by rfl⟩ : syracuseStep 1919731 = 2879597) B2879597
theorem B4319405 : Blo 1919435 4319405 := bbase (se 3 (by rfl) ⟨809888, by rfl⟩ : syracuseStep 4319405 = 1619777) (by norm_num)
theorem B2879603 : Blo 1919435 2879603 := bstep (se 1 (by rfl) ⟨2159702, by rfl⟩ : syracuseStep 2879603 = 4319405) B4319405
theorem B1919735 : Blo 1919435 1919735 := bstep (se 1 (by rfl) ⟨1439801, by rfl⟩ : syracuseStep 1919735 = 2879603) B2879603
theorem B4378349 : Blo 1919435 4378349 := bbase (se 3 (by rfl) ⟨820940, by rfl⟩ : syracuseStep 4378349 = 1641881) (by norm_num)
theorem B2918899 : Blo 1919435 2918899 := bstep (se 1 (by rfl) ⟨2189174, by rfl⟩ : syracuseStep 2918899 = 4378349) B4378349
theorem B15567461 : Blo 1919435 15567461 := bstep (se 4 (by rfl) ⟨1459449, by rfl⟩ : syracuseStep 15567461 = 2918899) B2918899
theorem B10378307 : Blo 1919435 10378307 := bstep (se 1 (by rfl) ⟨7783730, by rfl⟩ : syracuseStep 10378307 = 15567461) B15567461
theorem B6918871 : Blo 1919435 6918871 := bstep (se 1 (by rfl) ⟨5189153, by rfl⟩ : syracuseStep 6918871 = 10378307) B10378307
theorem B9225161 : Blo 1919435 9225161 := bstep (se 2 (by rfl) ⟨3459435, by rfl⟩ : syracuseStep 9225161 = 6918871) B6918871
theorem B6150107 : Blo 1919435 6150107 := bstep (se 1 (by rfl) ⟨4612580, by rfl⟩ : syracuseStep 6150107 = 9225161) B9225161
theorem B4100071 : Blo 1919435 4100071 := bstep (se 1 (by rfl) ⟨3075053, by rfl⟩ : syracuseStep 4100071 = 6150107) B6150107
theorem B5466761 : Blo 1919435 5466761 := bstep (se 2 (by rfl) ⟨2050035, by rfl⟩ : syracuseStep 5466761 = 4100071) B4100071
theorem B3644507 : Blo 1919435 3644507 := bstep (se 1 (by rfl) ⟨2733380, by rfl⟩ : syracuseStep 3644507 = 5466761) B5466761
theorem B2429671 : Blo 1919435 2429671 := bstep (se 1 (by rfl) ⟨1822253, by rfl⟩ : syracuseStep 2429671 = 3644507) B3644507
theorem B3239561 : Blo 1919435 3239561 := bstep (se 2 (by rfl) ⟨1214835, by rfl⟩ : syracuseStep 3239561 = 2429671) B2429671
theorem B2159707 : Blo 1919435 2159707 := bstep (se 1 (by rfl) ⟨1619780, by rfl⟩ : syracuseStep 2159707 = 3239561) B3239561
theorem B2879609 : Blo 1919435 2879609 := bstep (se 2 (by rfl) ⟨1079853, by rfl⟩ : syracuseStep 2879609 = 2159707) B2159707
theorem B1919739 : Blo 1919435 1919739 := bstep (se 1 (by rfl) ⟨1439804, by rfl⟩ : syracuseStep 1919739 = 2879609) B2879609
theorem B24600469 : Blo 1919435 24600469 := bbase (se 6 (by rfl) ⟨576573, by rfl⟩ : syracuseStep 24600469 = 1153147) (by norm_num)
theorem B32800625 : Blo 1919435 32800625 := bstep (se 2 (by rfl) ⟨12300234, by rfl⟩ : syracuseStep 32800625 = 24600469) B24600469
theorem B21867083 : Blo 1919435 21867083 := bstep (se 1 (by rfl) ⟨16400312, by rfl⟩ : syracuseStep 21867083 = 32800625) B32800625
theorem B14578055 : Blo 1919435 14578055 := bstep (se 1 (by rfl) ⟨10933541, by rfl⟩ : syracuseStep 14578055 = 21867083) B21867083
theorem B9718703 : Blo 1919435 9718703 := bstep (se 1 (by rfl) ⟨7289027, by rfl⟩ : syracuseStep 9718703 = 14578055) B14578055
theorem B6479135 : Blo 1919435 6479135 := bstep (se 1 (by rfl) ⟨4859351, by rfl⟩ : syracuseStep 6479135 = 9718703) B9718703
theorem B4319423 : Blo 1919435 4319423 := bstep (se 1 (by rfl) ⟨3239567, by rfl⟩ : syracuseStep 4319423 = 6479135) B6479135
theorem B2879615 : Blo 1919435 2879615 := bstep (se 1 (by rfl) ⟨2159711, by rfl⟩ : syracuseStep 2879615 = 4319423) B4319423
theorem B1919743 : Blo 1919435 1919743 := bstep (se 1 (by rfl) ⟨1439807, by rfl⟩ : syracuseStep 1919743 = 2879615) B2879615
theorem B2879621 : Blo 1919435 2879621 := bbase (se 4 (by rfl) ⟨269964, by rfl⟩ : syracuseStep 2879621 = 539929) (by norm_num)
theorem B1919747 : Blo 1919435 1919747 := bstep (se 1 (by rfl) ⟨1439810, by rfl⟩ : syracuseStep 1919747 = 2879621) B2879621
theorem B3239581 : Blo 1919435 3239581 := bbase (se 3 (by rfl) ⟨607421, by rfl⟩ : syracuseStep 3239581 = 1214843) (by norm_num)
theorem B4319441 : Blo 1919435 4319441 := bstep (se 2 (by rfl) ⟨1619790, by rfl⟩ : syracuseStep 4319441 = 3239581) B3239581
theorem B2879627 : Blo 1919435 2879627 := bstep (se 1 (by rfl) ⟨2159720, by rfl⟩ : syracuseStep 2879627 = 4319441) B4319441
theorem B1919751 : Blo 1919435 1919751 := bstep (se 1 (by rfl) ⟨1439813, by rfl⟩ : syracuseStep 1919751 = 2879627) B2879627
theorem B2159725 : Blo 1919435 2159725 := bbase (se 3 (by rfl) ⟨404948, by rfl⟩ : syracuseStep 2159725 = 809897) (by norm_num)
theorem B2879633 : Blo 1919435 2879633 := bstep (se 2 (by rfl) ⟨1079862, by rfl⟩ : syracuseStep 2879633 = 2159725) B2159725
theorem B1919755 : Blo 1919435 1919755 := bstep (se 1 (by rfl) ⟨1439816, by rfl⟩ : syracuseStep 1919755 = 2879633) B2879633
theorem B6479189 : Blo 1919435 6479189 := bbase (se 11 (by rfl) ⟨4745, by rfl⟩ : syracuseStep 6479189 = 9491) (by norm_num)
theorem B4319459 : Blo 1919435 4319459 := bstep (se 1 (by rfl) ⟨3239594, by rfl⟩ : syracuseStep 4319459 = 6479189) B6479189
theorem B2879639 : Blo 1919435 2879639 := bstep (se 1 (by rfl) ⟨2159729, by rfl⟩ : syracuseStep 2879639 = 4319459) B4319459
theorem B1919759 : Blo 1919435 1919759 := bstep (se 1 (by rfl) ⟨1439819, by rfl⟩ : syracuseStep 1919759 = 2879639) B2879639
theorem B2879645 : Blo 1919435 2879645 := bbase (se 3 (by rfl) ⟨539933, by rfl⟩ : syracuseStep 2879645 = 1079867) (by norm_num)
theorem B1919763 : Blo 1919435 1919763 := bstep (se 1 (by rfl) ⟨1439822, by rfl⟩ : syracuseStep 1919763 = 2879645) B2879645
theorem B4319477 : Blo 1919435 4319477 := bbase (se 5 (by rfl) ⟨202475, by rfl⟩ : syracuseStep 4319477 = 404951) (by norm_num)
theorem B2879651 : Blo 1919435 2879651 := bstep (se 1 (by rfl) ⟨2159738, by rfl⟩ : syracuseStep 2879651 = 4319477) B4319477
theorem B1919767 : Blo 1919435 1919767 := bstep (se 1 (by rfl) ⟨1439825, by rfl⟩ : syracuseStep 1919767 = 2879651) B2879651
theorem B4378421 : Blo 1919435 4378421 := bbase (se 5 (by rfl) ⟨205238, by rfl⟩ : syracuseStep 4378421 = 410477) (by norm_num)
theorem B2918947 : Blo 1919435 2918947 := bstep (se 1 (by rfl) ⟨2189210, by rfl⟩ : syracuseStep 2918947 = 4378421) B4378421
theorem B3891929 : Blo 1919435 3891929 := bstep (se 2 (by rfl) ⟨1459473, by rfl⟩ : syracuseStep 3891929 = 2918947) B2918947
theorem B10378477 : Blo 1919435 10378477 := bstep (se 3 (by rfl) ⟨1945964, by rfl⟩ : syracuseStep 10378477 = 3891929) B3891929
theorem B13837969 : Blo 1919435 13837969 := bstep (se 2 (by rfl) ⟨5189238, by rfl⟩ : syracuseStep 13837969 = 10378477) B10378477
theorem B18450625 : Blo 1919435 18450625 := bstep (se 2 (by rfl) ⟨6918984, by rfl⟩ : syracuseStep 18450625 = 13837969) B13837969
theorem B24600833 : Blo 1919435 24600833 := bstep (se 2 (by rfl) ⟨9225312, by rfl⟩ : syracuseStep 24600833 = 18450625) B18450625
theorem B16400555 : Blo 1919435 16400555 := bstep (se 1 (by rfl) ⟨12300416, by rfl⟩ : syracuseStep 16400555 = 24600833) B24600833
theorem B10933703 : Blo 1919435 10933703 := bstep (se 1 (by rfl) ⟨8200277, by rfl⟩ : syracuseStep 10933703 = 16400555) B16400555
theorem B7289135 : Blo 1919435 7289135 := bstep (se 1 (by rfl) ⟨5466851, by rfl⟩ : syracuseStep 7289135 = 10933703) B10933703
theorem B4859423 : Blo 1919435 4859423 := bstep (se 1 (by rfl) ⟨3644567, by rfl⟩ : syracuseStep 4859423 = 7289135) B7289135
theorem B3239615 : Blo 1919435 3239615 := bstep (se 1 (by rfl) ⟨2429711, by rfl⟩ : syracuseStep 3239615 = 4859423) B4859423
theorem B2159743 : Blo 1919435 2159743 := bstep (se 1 (by rfl) ⟨1619807, by rfl⟩ : syracuseStep 2159743 = 3239615) B3239615
theorem B2879657 : Blo 1919435 2879657 := bstep (se 2 (by rfl) ⟨1079871, by rfl⟩ : syracuseStep 2879657 = 2159743) B2159743
theorem B1919771 : Blo 1919435 1919771 := bstep (se 1 (by rfl) ⟨1439828, by rfl⟩ : syracuseStep 1919771 = 2879657) B2879657
theorem B2306333 : Blo 1919435 2306333 := bbase (se 3 (by rfl) ⟨432437, by rfl⟩ : syracuseStep 2306333 = 864875) (by norm_num)
theorem B6150221 : Blo 1919435 6150221 := bstep (se 3 (by rfl) ⟨1153166, by rfl⟩ : syracuseStep 6150221 = 2306333) B2306333
theorem B4100147 : Blo 1919435 4100147 := bstep (se 1 (by rfl) ⟨3075110, by rfl⟩ : syracuseStep 4100147 = 6150221) B6150221
theorem B2733431 : Blo 1919435 2733431 := bstep (se 1 (by rfl) ⟨2050073, by rfl⟩ : syracuseStep 2733431 = 4100147) B4100147
theorem B7289149 : Blo 1919435 7289149 := bstep (se 3 (by rfl) ⟨1366715, by rfl⟩ : syracuseStep 7289149 = 2733431) B2733431
theorem B9718865 : Blo 1919435 9718865 := bstep (se 2 (by rfl) ⟨3644574, by rfl⟩ : syracuseStep 9718865 = 7289149) B7289149
theorem B6479243 : Blo 1919435 6479243 := bstep (se 1 (by rfl) ⟨4859432, by rfl⟩ : syracuseStep 6479243 = 9718865) B9718865
theorem B4319495 : Blo 1919435 4319495 := bstep (se 1 (by rfl) ⟨3239621, by rfl⟩ : syracuseStep 4319495 = 6479243) B6479243
theorem B2879663 : Blo 1919435 2879663 := bstep (se 1 (by rfl) ⟨2159747, by rfl⟩ : syracuseStep 2879663 = 4319495) B4319495
theorem B1919775 : Blo 1919435 1919775 := bstep (se 1 (by rfl) ⟨1439831, by rfl⟩ : syracuseStep 1919775 = 2879663) B2879663
theorem B2879669 : Blo 1919435 2879669 := bbase (se 5 (by rfl) ⟨134984, by rfl⟩ : syracuseStep 2879669 = 269969) (by norm_num)
theorem B1919779 : Blo 1919435 1919779 := bstep (se 1 (by rfl) ⟨1439834, by rfl⟩ : syracuseStep 1919779 = 2879669) B2879669
theorem B4859453 : Blo 1919435 4859453 := bbase (se 3 (by rfl) ⟨911147, by rfl⟩ : syracuseStep 4859453 = 1822295) (by norm_num)
theorem B3239635 : Blo 1919435 3239635 := bstep (se 1 (by rfl) ⟨2429726, by rfl⟩ : syracuseStep 3239635 = 4859453) B4859453
theorem B4319513 : Blo 1919435 4319513 := bstep (se 2 (by rfl) ⟨1619817, by rfl⟩ : syracuseStep 4319513 = 3239635) B3239635
theorem B2879675 : Blo 1919435 2879675 := bstep (se 1 (by rfl) ⟨2159756, by rfl⟩ : syracuseStep 2879675 = 4319513) B4319513
theorem B1919783 : Blo 1919435 1919783 := bstep (se 1 (by rfl) ⟨1439837, by rfl⟩ : syracuseStep 1919783 = 2879675) B2879675
theorem B2159761 : Blo 1919435 2159761 := bbase (se 2 (by rfl) ⟨809910, by rfl⟩ : syracuseStep 2159761 = 1619821) (by norm_num)
theorem B2879681 : Blo 1919435 2879681 := bstep (se 2 (by rfl) ⟨1079880, by rfl⟩ : syracuseStep 2879681 = 2159761) B2159761
theorem B1919787 : Blo 1919435 1919787 := bstep (se 1 (by rfl) ⟨1439840, by rfl⟩ : syracuseStep 1919787 = 2879681) B2879681
theorem B3644605 : Blo 1919435 3644605 := bbase (se 3 (by rfl) ⟨683363, by rfl⟩ : syracuseStep 3644605 = 1366727) (by norm_num)
theorem B4859473 : Blo 1919435 4859473 := bstep (se 2 (by rfl) ⟨1822302, by rfl⟩ : syracuseStep 4859473 = 3644605) B3644605
theorem B6479297 : Blo 1919435 6479297 := bstep (se 2 (by rfl) ⟨2429736, by rfl⟩ : syracuseStep 6479297 = 4859473) B4859473
theorem B4319531 : Blo 1919435 4319531 := bstep (se 1 (by rfl) ⟨3239648, by rfl⟩ : syracuseStep 4319531 = 6479297) B6479297
theorem B2879687 : Blo 1919435 2879687 := bstep (se 1 (by rfl) ⟨2159765, by rfl⟩ : syracuseStep 2879687 = 4319531) B4319531
theorem B1919791 : Blo 1919435 1919791 := bstep (se 1 (by rfl) ⟨1439843, by rfl⟩ : syracuseStep 1919791 = 2879687) B2879687
theorem B2879693 : Blo 1919435 2879693 := bbase (se 3 (by rfl) ⟨539942, by rfl⟩ : syracuseStep 2879693 = 1079885) (by norm_num)
theorem B1919795 : Blo 1919435 1919795 := bstep (se 1 (by rfl) ⟨1439846, by rfl⟩ : syracuseStep 1919795 = 2879693) B2879693
theorem B4319549 : Blo 1919435 4319549 := bbase (se 3 (by rfl) ⟨809915, by rfl⟩ : syracuseStep 4319549 = 1619831) (by norm_num)
theorem B2879699 : Blo 1919435 2879699 := bstep (se 1 (by rfl) ⟨2159774, by rfl⟩ : syracuseStep 2879699 = 4319549) B4319549
theorem B1919799 : Blo 1919435 1919799 := bstep (se 1 (by rfl) ⟨1439849, by rfl⟩ : syracuseStep 1919799 = 2879699) B2879699
theorem B3239669 : Blo 1919435 3239669 := bbase (se 5 (by rfl) ⟨151859, by rfl⟩ : syracuseStep 3239669 = 303719) (by norm_num)
theorem B2159779 : Blo 1919435 2159779 := bstep (se 1 (by rfl) ⟨1619834, by rfl⟩ : syracuseStep 2159779 = 3239669) B3239669
theorem B2879705 : Blo 1919435 2879705 := bstep (se 2 (by rfl) ⟨1079889, by rfl⟩ : syracuseStep 2879705 = 2159779) B2159779
theorem B1919803 : Blo 1919435 1919803 := bstep (se 1 (by rfl) ⟨1439852, by rfl⟩ : syracuseStep 1919803 = 2879705) B2879705
theorem B3459557 : Blo 1919435 3459557 := bbase (se 4 (by rfl) ⟨324333, by rfl⟩ : syracuseStep 3459557 = 648667) (by norm_num)
theorem B9225485 : Blo 1919435 9225485 := bstep (se 3 (by rfl) ⟨1729778, by rfl⟩ : syracuseStep 9225485 = 3459557) B3459557
theorem B6150323 : Blo 1919435 6150323 := bstep (se 1 (by rfl) ⟨4612742, by rfl⟩ : syracuseStep 6150323 = 9225485) B9225485
theorem B4100215 : Blo 1919435 4100215 := bstep (se 1 (by rfl) ⟨3075161, by rfl⟩ : syracuseStep 4100215 = 6150323) B6150323
theorem B5466953 : Blo 1919435 5466953 := bstep (se 2 (by rfl) ⟨2050107, by rfl⟩ : syracuseStep 5466953 = 4100215) B4100215
theorem B14578541 : Blo 1919435 14578541 := bstep (se 3 (by rfl) ⟨2733476, by rfl⟩ : syracuseStep 14578541 = 5466953) B5466953
theorem B9719027 : Blo 1919435 9719027 := bstep (se 1 (by rfl) ⟨7289270, by rfl⟩ : syracuseStep 9719027 = 14578541) B14578541
theorem B6479351 : Blo 1919435 6479351 := bstep (se 1 (by rfl) ⟨4859513, by rfl⟩ : syracuseStep 6479351 = 9719027) B9719027
theorem B4319567 : Blo 1919435 4319567 := bstep (se 1 (by rfl) ⟨3239675, by rfl⟩ : syracuseStep 4319567 = 6479351) B6479351
theorem B2879711 : Blo 1919435 2879711 := bstep (se 1 (by rfl) ⟨2159783, by rfl⟩ : syracuseStep 2879711 = 4319567) B4319567
theorem B1919807 : Blo 1919435 1919807 := bstep (se 1 (by rfl) ⟨1439855, by rfl⟩ : syracuseStep 1919807 = 2879711) B2879711
theorem B2879717 : Blo 1919435 2879717 := bbase (se 4 (by rfl) ⟨269973, by rfl⟩ : syracuseStep 2879717 = 539947) (by norm_num)
theorem B1919811 : Blo 1919435 1919811 := bstep (se 1 (by rfl) ⟨1439858, by rfl⟩ : syracuseStep 1919811 = 2879717) B2879717
theorem B3159661 : Blo 1919435 3159661 := bbase (se 3 (by rfl) ⟨592436, by rfl⟩ : syracuseStep 3159661 = 1184873) (by norm_num)
theorem B4212881 : Blo 1919435 4212881 := bstep (se 2 (by rfl) ⟨1579830, by rfl⟩ : syracuseStep 4212881 = 3159661) B3159661
theorem B2808587 : Blo 1919435 2808587 := bstep (se 1 (by rfl) ⟨2106440, by rfl⟩ : syracuseStep 2808587 = 4212881) B4212881
theorem B7489565 : Blo 1919435 7489565 := bstep (se 3 (by rfl) ⟨1404293, by rfl⟩ : syracuseStep 7489565 = 2808587) B2808587
theorem B4993043 : Blo 1919435 4993043 := bstep (se 1 (by rfl) ⟨3744782, by rfl⟩ : syracuseStep 4993043 = 7489565) B7489565
theorem B13314781 : Blo 1919435 13314781 := bstep (se 3 (by rfl) ⟨2496521, by rfl⟩ : syracuseStep 13314781 = 4993043) B4993043
theorem B17753041 : Blo 1919435 17753041 := bstep (se 2 (by rfl) ⟨6657390, by rfl⟩ : syracuseStep 17753041 = 13314781) B13314781
theorem B23670721 : Blo 1919435 23670721 := bstep (se 2 (by rfl) ⟨8876520, by rfl⟩ : syracuseStep 23670721 = 17753041) B17753041
theorem B126243845 : Blo 1919435 126243845 := bstep (se 4 (by rfl) ⟨11835360, by rfl⟩ : syracuseStep 126243845 = 23670721) B23670721
theorem B84162563 : Blo 1919435 84162563 := bstep (se 1 (by rfl) ⟨63121922, by rfl⟩ : syracuseStep 84162563 = 126243845) B126243845
theorem B56108375 : Blo 1919435 56108375 := bstep (se 1 (by rfl) ⟨42081281, by rfl⟩ : syracuseStep 56108375 = 84162563) B84162563
theorem B37405583 : Blo 1919435 37405583 := bstep (se 1 (by rfl) ⟨28054187, by rfl⟩ : syracuseStep 37405583 = 56108375) B56108375
theorem B24937055 : Blo 1919435 24937055 := bstep (se 1 (by rfl) ⟨18702791, by rfl⟩ : syracuseStep 24937055 = 37405583) B37405583
theorem B16624703 : Blo 1919435 16624703 := bstep (se 1 (by rfl) ⟨12468527, by rfl⟩ : syracuseStep 16624703 = 24937055) B24937055
theorem B44332541 : Blo 1919435 44332541 := bstep (se 3 (by rfl) ⟨8312351, by rfl⟩ : syracuseStep 44332541 = 16624703) B16624703
theorem B29555027 : Blo 1919435 29555027 := bstep (se 1 (by rfl) ⟨22166270, by rfl⟩ : syracuseStep 29555027 = 44332541) B44332541
theorem B19703351 : Blo 1919435 19703351 := bstep (se 1 (by rfl) ⟨14777513, by rfl⟩ : syracuseStep 19703351 = 29555027) B29555027
theorem B13135567 : Blo 1919435 13135567 := bstep (se 1 (by rfl) ⟨9851675, by rfl⟩ : syracuseStep 13135567 = 19703351) B19703351
theorem B17514089 : Blo 1919435 17514089 := bstep (se 2 (by rfl) ⟨6567783, by rfl⟩ : syracuseStep 17514089 = 13135567) B13135567
theorem B11676059 : Blo 1919435 11676059 := bstep (se 1 (by rfl) ⟨8757044, by rfl⟩ : syracuseStep 11676059 = 17514089) B17514089
theorem B7784039 : Blo 1919435 7784039 := bstep (se 1 (by rfl) ⟨5838029, by rfl⟩ : syracuseStep 7784039 = 11676059) B11676059
theorem B5189359 : Blo 1919435 5189359 := bstep (se 1 (by rfl) ⟨3892019, by rfl⟩ : syracuseStep 5189359 = 7784039) B7784039
theorem B6919145 : Blo 1919435 6919145 := bstep (se 2 (by rfl) ⟨2594679, by rfl⟩ : syracuseStep 6919145 = 5189359) B5189359
theorem B4612763 : Blo 1919435 4612763 := bstep (se 1 (by rfl) ⟨3459572, by rfl⟩ : syracuseStep 4612763 = 6919145) B6919145
theorem B3075175 : Blo 1919435 3075175 := bstep (se 1 (by rfl) ⟨2306381, by rfl⟩ : syracuseStep 3075175 = 4612763) B4612763
theorem B4100233 : Blo 1919435 4100233 := bstep (se 2 (by rfl) ⟨1537587, by rfl⟩ : syracuseStep 4100233 = 3075175) B3075175
theorem B5466977 : Blo 1919435 5466977 := bstep (se 2 (by rfl) ⟨2050116, by rfl⟩ : syracuseStep 5466977 = 4100233) B4100233
theorem B3644651 : Blo 1919435 3644651 := bstep (se 1 (by rfl) ⟨2733488, by rfl⟩ : syracuseStep 3644651 = 5466977) B5466977
theorem B2429767 : Blo 1919435 2429767 := bstep (se 1 (by rfl) ⟨1822325, by rfl⟩ : syracuseStep 2429767 = 3644651) B3644651
theorem B3239689 : Blo 1919435 3239689 := bstep (se 2 (by rfl) ⟨1214883, by rfl⟩ : syracuseStep 3239689 = 2429767) B2429767
theorem B4319585 : Blo 1919435 4319585 := bstep (se 2 (by rfl) ⟨1619844, by rfl⟩ : syracuseStep 4319585 = 3239689) B3239689
theorem B2879723 : Blo 1919435 2879723 := bstep (se 1 (by rfl) ⟨2159792, by rfl⟩ : syracuseStep 2879723 = 4319585) B4319585
theorem B1919815 : Blo 1919435 1919815 := bstep (se 1 (by rfl) ⟨1439861, by rfl⟩ : syracuseStep 1919815 = 2879723) B2879723
theorem B2159797 : Blo 1919435 2159797 := bbase (se 5 (by rfl) ⟨101240, by rfl⟩ : syracuseStep 2159797 = 202481) (by norm_num)
theorem B2879729 : Blo 1919435 2879729 := bstep (se 2 (by rfl) ⟨1079898, by rfl⟩ : syracuseStep 2879729 = 2159797) B2159797
theorem B1919819 : Blo 1919435 1919819 := bstep (se 1 (by rfl) ⟨1439864, by rfl⟩ : syracuseStep 1919819 = 2879729) B2879729
theorem B2429777 : Blo 1919435 2429777 := bbase (se 2 (by rfl) ⟨911166, by rfl⟩ : syracuseStep 2429777 = 1822333) (by norm_num)
theorem B6479405 : Blo 1919435 6479405 := bstep (se 3 (by rfl) ⟨1214888, by rfl⟩ : syracuseStep 6479405 = 2429777) B2429777
theorem B4319603 : Blo 1919435 4319603 := bstep (se 1 (by rfl) ⟨3239702, by rfl⟩ : syracuseStep 4319603 = 6479405) B6479405
theorem B2879735 : Blo 1919435 2879735 := bstep (se 1 (by rfl) ⟨2159801, by rfl⟩ : syracuseStep 2879735 = 4319603) B4319603
theorem B1919823 : Blo 1919435 1919823 := bstep (se 1 (by rfl) ⟨1439867, by rfl⟩ : syracuseStep 1919823 = 2879735) B2879735
theorem B2879741 : Blo 1919435 2879741 := bbase (se 3 (by rfl) ⟨539951, by rfl⟩ : syracuseStep 2879741 = 1079903) (by norm_num)
theorem B1919827 : Blo 1919435 1919827 := bstep (se 1 (by rfl) ⟨1439870, by rfl⟩ : syracuseStep 1919827 = 2879741) B2879741
theorem B4319621 : Blo 1919435 4319621 := bbase (se 4 (by rfl) ⟨404964, by rfl⟩ : syracuseStep 4319621 = 809929) (by norm_num)
theorem B2879747 : Blo 1919435 2879747 := bstep (se 1 (by rfl) ⟨2159810, by rfl⟩ : syracuseStep 2879747 = 4319621) B4319621
theorem B1919831 : Blo 1919435 1919831 := bstep (se 1 (by rfl) ⟨1439873, by rfl⟩ : syracuseStep 1919831 = 2879747) B2879747
theorem B2733517 : Blo 1919435 2733517 := bbase (se 3 (by rfl) ⟨512534, by rfl⟩ : syracuseStep 2733517 = 1025069) (by norm_num)
theorem B3644689 : Blo 1919435 3644689 := bstep (se 2 (by rfl) ⟨1366758, by rfl⟩ : syracuseStep 3644689 = 2733517) B2733517
theorem B4859585 : Blo 1919435 4859585 := bstep (se 2 (by rfl) ⟨1822344, by rfl⟩ : syracuseStep 4859585 = 3644689) B3644689
theorem B3239723 : Blo 1919435 3239723 := bstep (se 1 (by rfl) ⟨2429792, by rfl⟩ : syracuseStep 3239723 = 4859585) B4859585
theorem B2159815 : Blo 1919435 2159815 := bstep (se 1 (by rfl) ⟨1619861, by rfl⟩ : syracuseStep 2159815 = 3239723) B3239723
theorem B2879753 : Blo 1919435 2879753 := bstep (se 2 (by rfl) ⟨1079907, by rfl⟩ : syracuseStep 2879753 = 2159815) B2159815
theorem B1919835 : Blo 1919435 1919835 := bstep (se 1 (by rfl) ⟨1439876, by rfl⟩ : syracuseStep 1919835 = 2879753) B2879753
theorem B9719189 : Blo 1919435 9719189 := bbase (se 6 (by rfl) ⟨227793, by rfl⟩ : syracuseStep 9719189 = 455587) (by norm_num)
theorem B6479459 : Blo 1919435 6479459 := bstep (se 1 (by rfl) ⟨4859594, by rfl⟩ : syracuseStep 6479459 = 9719189) B9719189
theorem B4319639 : Blo 1919435 4319639 := bstep (se 1 (by rfl) ⟨3239729, by rfl⟩ : syracuseStep 4319639 = 6479459) B6479459
theorem B2879759 : Blo 1919435 2879759 := bstep (se 1 (by rfl) ⟨2159819, by rfl⟩ : syracuseStep 2879759 = 4319639) B4319639
theorem B1919839 : Blo 1919435 1919839 := bstep (se 1 (by rfl) ⟨1439879, by rfl⟩ : syracuseStep 1919839 = 2879759) B2879759
theorem B2879765 : Blo 1919435 2879765 := bbase (se 6 (by rfl) ⟨67494, by rfl⟩ : syracuseStep 2879765 = 134989) (by norm_num)
theorem B1919843 : Blo 1919435 1919843 := bstep (se 1 (by rfl) ⟨1439882, by rfl⟩ : syracuseStep 1919843 = 2879765) B2879765
theorem B3459629 : Blo 1919435 3459629 := bbase (se 3 (by rfl) ⟨648680, by rfl⟩ : syracuseStep 3459629 = 1297361) (by norm_num)
theorem B9225677 : Blo 1919435 9225677 := bstep (se 3 (by rfl) ⟨1729814, by rfl⟩ : syracuseStep 9225677 = 3459629) B3459629
theorem B24601805 : Blo 1919435 24601805 := bstep (se 3 (by rfl) ⟨4612838, by rfl⟩ : syracuseStep 24601805 = 9225677) B9225677
theorem B16401203 : Blo 1919435 16401203 := bstep (se 1 (by rfl) ⟨12300902, by rfl⟩ : syracuseStep 16401203 = 24601805) B24601805
theorem B10934135 : Blo 1919435 10934135 := bstep (se 1 (by rfl) ⟨8200601, by rfl⟩ : syracuseStep 10934135 = 16401203) B16401203
theorem B7289423 : Blo 1919435 7289423 := bstep (se 1 (by rfl) ⟨5467067, by rfl⟩ : syracuseStep 7289423 = 10934135) B10934135
theorem B4859615 : Blo 1919435 4859615 := bstep (se 1 (by rfl) ⟨3644711, by rfl⟩ : syracuseStep 4859615 = 7289423) B7289423
theorem B3239743 : Blo 1919435 3239743 := bstep (se 1 (by rfl) ⟨2429807, by rfl⟩ : syracuseStep 3239743 = 4859615) B4859615
theorem B4319657 : Blo 1919435 4319657 := bstep (se 2 (by rfl) ⟨1619871, by rfl⟩ : syracuseStep 4319657 = 3239743) B3239743
theorem B2879771 : Blo 1919435 2879771 := bstep (se 1 (by rfl) ⟨2159828, by rfl⟩ : syracuseStep 2879771 = 4319657) B4319657
theorem B1919847 : Blo 1919435 1919847 := bstep (se 1 (by rfl) ⟨1439885, by rfl⟩ : syracuseStep 1919847 = 2879771) B2879771
theorem B2159833 : Blo 1919435 2159833 := bbase (se 2 (by rfl) ⟨809937, by rfl⟩ : syracuseStep 2159833 = 1619875) (by norm_num)
theorem B2879777 : Blo 1919435 2879777 := bstep (se 2 (by rfl) ⟨1079916, by rfl⟩ : syracuseStep 2879777 = 2159833) B2159833
theorem B1919851 : Blo 1919435 1919851 := bstep (se 1 (by rfl) ⟨1439888, by rfl⟩ : syracuseStep 1919851 = 2879777) B2879777
theorem B3328765 : Blo 1919435 3328765 := bbase (se 3 (by rfl) ⟨624143, by rfl⟩ : syracuseStep 3328765 = 1248287) (by norm_num)
theorem B17753413 : Blo 1919435 17753413 := bstep (se 4 (by rfl) ⟨1664382, by rfl⟩ : syracuseStep 17753413 = 3328765) B3328765
theorem B23671217 : Blo 1919435 23671217 := bstep (se 2 (by rfl) ⟨8876706, by rfl⟩ : syracuseStep 23671217 = 17753413) B17753413
theorem B63123245 : Blo 1919435 63123245 := bstep (se 3 (by rfl) ⟨11835608, by rfl⟩ : syracuseStep 63123245 = 23671217) B23671217
theorem B42082163 : Blo 1919435 42082163 := bstep (se 1 (by rfl) ⟨31561622, by rfl⟩ : syracuseStep 42082163 = 63123245) B63123245
theorem B28054775 : Blo 1919435 28054775 := bstep (se 1 (by rfl) ⟨21041081, by rfl⟩ : syracuseStep 28054775 = 42082163) B42082163
theorem B18703183 : Blo 1919435 18703183 := bstep (se 1 (by rfl) ⟨14027387, by rfl⟩ : syracuseStep 18703183 = 28054775) B28054775
theorem B24937577 : Blo 1919435 24937577 := bstep (se 2 (by rfl) ⟨9351591, by rfl⟩ : syracuseStep 24937577 = 18703183) B18703183
theorem B16625051 : Blo 1919435 16625051 := bstep (se 1 (by rfl) ⟨12468788, by rfl⟩ : syracuseStep 16625051 = 24937577) B24937577
theorem B11083367 : Blo 1919435 11083367 := bstep (se 1 (by rfl) ⟨8312525, by rfl⟩ : syracuseStep 11083367 = 16625051) B16625051
theorem B7388911 : Blo 1919435 7388911 := bstep (se 1 (by rfl) ⟨5541683, by rfl⟩ : syracuseStep 7388911 = 11083367) B11083367
theorem B9851881 : Blo 1919435 9851881 := bstep (se 2 (by rfl) ⟨3694455, by rfl⟩ : syracuseStep 9851881 = 7388911) B7388911
theorem B13135841 : Blo 1919435 13135841 := bstep (se 2 (by rfl) ⟨4925940, by rfl⟩ : syracuseStep 13135841 = 9851881) B9851881
theorem B8757227 : Blo 1919435 8757227 := bstep (se 1 (by rfl) ⟨6567920, by rfl⟩ : syracuseStep 8757227 = 13135841) B13135841
theorem B5838151 : Blo 1919435 5838151 := bstep (se 1 (by rfl) ⟨4378613, by rfl⟩ : syracuseStep 5838151 = 8757227) B8757227
theorem B7784201 : Blo 1919435 7784201 := bstep (se 2 (by rfl) ⟨2919075, by rfl⟩ : syracuseStep 7784201 = 5838151) B5838151
theorem B5189467 : Blo 1919435 5189467 := bstep (se 1 (by rfl) ⟨3892100, by rfl⟩ : syracuseStep 5189467 = 7784201) B7784201
theorem B6919289 : Blo 1919435 6919289 := bstep (se 2 (by rfl) ⟨2594733, by rfl⟩ : syracuseStep 6919289 = 5189467) B5189467
theorem B4612859 : Blo 1919435 4612859 := bstep (se 1 (by rfl) ⟨3459644, by rfl⟩ : syracuseStep 4612859 = 6919289) B6919289
theorem B3075239 : Blo 1919435 3075239 := bstep (se 1 (by rfl) ⟨2306429, by rfl⟩ : syracuseStep 3075239 = 4612859) B4612859
theorem B2050159 : Blo 1919435 2050159 := bstep (se 1 (by rfl) ⟨1537619, by rfl⟩ : syracuseStep 2050159 = 3075239) B3075239
theorem B2733545 : Blo 1919435 2733545 := bstep (se 2 (by rfl) ⟨1025079, by rfl⟩ : syracuseStep 2733545 = 2050159) B2050159
theorem B7289453 : Blo 1919435 7289453 := bstep (se 3 (by rfl) ⟨1366772, by rfl⟩ : syracuseStep 7289453 = 2733545) B2733545
theorem B4859635 : Blo 1919435 4859635 := bstep (se 1 (by rfl) ⟨3644726, by rfl⟩ : syracuseStep 4859635 = 7289453) B7289453
theorem B6479513 : Blo 1919435 6479513 := bstep (se 2 (by rfl) ⟨2429817, by rfl⟩ : syracuseStep 6479513 = 4859635) B4859635
theorem B4319675 : Blo 1919435 4319675 := bstep (se 1 (by rfl) ⟨3239756, by rfl⟩ : syracuseStep 4319675 = 6479513) B6479513
theorem B2879783 : Blo 1919435 2879783 := bstep (se 1 (by rfl) ⟨2159837, by rfl⟩ : syracuseStep 2879783 = 4319675) B4319675
theorem B1919855 : Blo 1919435 1919855 := bstep (se 1 (by rfl) ⟨1439891, by rfl⟩ : syracuseStep 1919855 = 2879783) B2879783
theorem B2879789 : Blo 1919435 2879789 := bbase (se 3 (by rfl) ⟨539960, by rfl⟩ : syracuseStep 2879789 = 1079921) (by norm_num)
theorem B1919859 : Blo 1919435 1919859 := bstep (se 1 (by rfl) ⟨1439894, by rfl⟩ : syracuseStep 1919859 = 2879789) B2879789
theorem B4319693 : Blo 1919435 4319693 := bbase (se 3 (by rfl) ⟨809942, by rfl⟩ : syracuseStep 4319693 = 1619885) (by norm_num)
theorem B2879795 : Blo 1919435 2879795 := bstep (se 1 (by rfl) ⟨2159846, by rfl⟩ : syracuseStep 2879795 = 4319693) B4319693
theorem B1919863 : Blo 1919435 1919863 := bstep (se 1 (by rfl) ⟨1439897, by rfl⟩ : syracuseStep 1919863 = 2879795) B2879795
theorem B2429833 : Blo 1919435 2429833 := bbase (se 2 (by rfl) ⟨911187, by rfl⟩ : syracuseStep 2429833 = 1822375) (by norm_num)
theorem B3239777 : Blo 1919435 3239777 := bstep (se 2 (by rfl) ⟨1214916, by rfl⟩ : syracuseStep 3239777 = 2429833) B2429833
theorem B2159851 : Blo 1919435 2159851 := bstep (se 1 (by rfl) ⟨1619888, by rfl⟩ : syracuseStep 2159851 = 3239777) B3239777
theorem B2879801 : Blo 1919435 2879801 := bstep (se 2 (by rfl) ⟨1079925, by rfl⟩ : syracuseStep 2879801 = 2159851) B2159851
theorem B1919867 : Blo 1919435 1919867 := bstep (se 1 (by rfl) ⟨1439900, by rfl⟩ : syracuseStep 1919867 = 2879801) B2879801
theorem B2958925 : Blo 1919435 2958925 := bbase (se 3 (by rfl) ⟨554798, by rfl⟩ : syracuseStep 2958925 = 1109597) (by norm_num)
theorem B3945233 : Blo 1919435 3945233 := bstep (se 2 (by rfl) ⟨1479462, by rfl⟩ : syracuseStep 3945233 = 2958925) B2958925
theorem B10520621 : Blo 1919435 10520621 := bstep (se 3 (by rfl) ⟨1972616, by rfl⟩ : syracuseStep 10520621 = 3945233) B3945233
theorem B7013747 : Blo 1919435 7013747 := bstep (se 1 (by rfl) ⟨5260310, by rfl⟩ : syracuseStep 7013747 = 10520621) B10520621
theorem B4675831 : Blo 1919435 4675831 := bstep (se 1 (by rfl) ⟨3506873, by rfl⟩ : syracuseStep 4675831 = 7013747) B7013747
theorem B99751061 : Blo 1919435 99751061 := bstep (se 6 (by rfl) ⟨2337915, by rfl⟩ : syracuseStep 99751061 = 4675831) B4675831
theorem B266002829 : Blo 1919435 266002829 := bstep (se 3 (by rfl) ⟨49875530, by rfl⟩ : syracuseStep 266002829 = 99751061) B99751061
theorem B177335219 : Blo 1919435 177335219 := bstep (se 1 (by rfl) ⟨133001414, by rfl⟩ : syracuseStep 177335219 = 266002829) B266002829
theorem B118223479 : Blo 1919435 118223479 := bstep (se 1 (by rfl) ⟨88667609, by rfl⟩ : syracuseStep 118223479 = 177335219) B177335219
theorem B157631305 : Blo 1919435 157631305 := bstep (se 2 (by rfl) ⟨59111739, by rfl⟩ : syracuseStep 157631305 = 118223479) B118223479
theorem B210175073 : Blo 1919435 210175073 := bstep (se 2 (by rfl) ⟨78815652, by rfl⟩ : syracuseStep 210175073 = 157631305) B157631305
theorem B140116715 : Blo 1919435 140116715 := bstep (se 1 (by rfl) ⟨105087536, by rfl⟩ : syracuseStep 140116715 = 210175073) B210175073
theorem B93411143 : Blo 1919435 93411143 := bstep (se 1 (by rfl) ⟨70058357, by rfl⟩ : syracuseStep 93411143 = 140116715) B140116715
theorem B62274095 : Blo 1919435 62274095 := bstep (se 1 (by rfl) ⟨46705571, by rfl⟩ : syracuseStep 62274095 = 93411143) B93411143
theorem B41516063 : Blo 1919435 41516063 := bstep (se 1 (by rfl) ⟨31137047, by rfl⟩ : syracuseStep 41516063 = 62274095) B62274095
theorem B27677375 : Blo 1919435 27677375 := bstep (se 1 (by rfl) ⟨20758031, by rfl⟩ : syracuseStep 27677375 = 41516063) B41516063
theorem B18451583 : Blo 1919435 18451583 := bstep (se 1 (by rfl) ⟨13838687, by rfl⟩ : syracuseStep 18451583 = 27677375) B27677375
theorem B12301055 : Blo 1919435 12301055 := bstep (se 1 (by rfl) ⟨9225791, by rfl⟩ : syracuseStep 12301055 = 18451583) B18451583
theorem B8200703 : Blo 1919435 8200703 := bstep (se 1 (by rfl) ⟨6150527, by rfl⟩ : syracuseStep 8200703 = 12301055) B12301055
theorem B21868541 : Blo 1919435 21868541 := bstep (se 3 (by rfl) ⟨4100351, by rfl⟩ : syracuseStep 21868541 = 8200703) B8200703
theorem B14579027 : Blo 1919435 14579027 := bstep (se 1 (by rfl) ⟨10934270, by rfl⟩ : syracuseStep 14579027 = 21868541) B21868541
theorem B9719351 : Blo 1919435 9719351 := bstep (se 1 (by rfl) ⟨7289513, by rfl⟩ : syracuseStep 9719351 = 14579027) B14579027
theorem B6479567 : Blo 1919435 6479567 := bstep (se 1 (by rfl) ⟨4859675, by rfl⟩ : syracuseStep 6479567 = 9719351) B9719351
theorem B4319711 : Blo 1919435 4319711 := bstep (se 1 (by rfl) ⟨3239783, by rfl⟩ : syracuseStep 4319711 = 6479567) B6479567
theorem B2879807 : Blo 1919435 2879807 := bstep (se 1 (by rfl) ⟨2159855, by rfl⟩ : syracuseStep 2879807 = 4319711) B4319711
theorem B1919871 : Blo 1919435 1919871 := bstep (se 1 (by rfl) ⟨1439903, by rfl⟩ : syracuseStep 1919871 = 2879807) B2879807
theorem B2879813 : Blo 1919435 2879813 := bbase (se 4 (by rfl) ⟨269982, by rfl⟩ : syracuseStep 2879813 = 539965) (by norm_num)
theorem B1919875 : Blo 1919435 1919875 := bstep (se 1 (by rfl) ⟨1439906, by rfl⟩ : syracuseStep 1919875 = 2879813) B2879813
theorem B3239797 : Blo 1919435 3239797 := bbase (se 5 (by rfl) ⟨151865, by rfl⟩ : syracuseStep 3239797 = 303731) (by norm_num)
theorem B4319729 : Blo 1919435 4319729 := bstep (se 2 (by rfl) ⟨1619898, by rfl⟩ : syracuseStep 4319729 = 3239797) B3239797
theorem B2879819 : Blo 1919435 2879819 := bstep (se 1 (by rfl) ⟨2159864, by rfl⟩ : syracuseStep 2879819 = 4319729) B4319729
theorem B1919879 : Blo 1919435 1919879 := bstep (se 1 (by rfl) ⟨1439909, by rfl⟩ : syracuseStep 1919879 = 2879819) B2879819
theorem B2159869 : Blo 1919435 2159869 := bbase (se 3 (by rfl) ⟨404975, by rfl⟩ : syracuseStep 2159869 = 809951) (by norm_num)
theorem B2879825 : Blo 1919435 2879825 := bstep (se 2 (by rfl) ⟨1079934, by rfl⟩ : syracuseStep 2879825 = 2159869) B2159869
theorem B1919883 : Blo 1919435 1919883 := bstep (se 1 (by rfl) ⟨1439912, by rfl⟩ : syracuseStep 1919883 = 2879825) B2879825
theorem B6479621 : Blo 1919435 6479621 := bbase (se 4 (by rfl) ⟨607464, by rfl⟩ : syracuseStep 6479621 = 1214929) (by norm_num)
theorem B4319747 : Blo 1919435 4319747 := bstep (se 1 (by rfl) ⟨3239810, by rfl⟩ : syracuseStep 4319747 = 6479621) B6479621
theorem B2879831 : Blo 1919435 2879831 := bstep (se 1 (by rfl) ⟨2159873, by rfl⟩ : syracuseStep 2879831 = 4319747) B4319747
theorem B1919887 : Blo 1919435 1919887 := bstep (se 1 (by rfl) ⟨1439915, by rfl⟩ : syracuseStep 1919887 = 2879831) B2879831
theorem B2879837 : Blo 1919435 2879837 := bbase (se 3 (by rfl) ⟨539969, by rfl⟩ : syracuseStep 2879837 = 1079939) (by norm_num)
theorem B1919891 : Blo 1919435 1919891 := bstep (se 1 (by rfl) ⟨1439918, by rfl⟩ : syracuseStep 1919891 = 2879837) B2879837
theorem B4319765 : Blo 1919435 4319765 := bbase (se 6 (by rfl) ⟨101244, by rfl⟩ : syracuseStep 4319765 = 202489) (by norm_num)
theorem B2879843 : Blo 1919435 2879843 := bstep (se 1 (by rfl) ⟨2159882, by rfl⟩ : syracuseStep 2879843 = 4319765) B4319765
theorem B1919895 : Blo 1919435 1919895 := bstep (se 1 (by rfl) ⟨1439921, by rfl⟩ : syracuseStep 1919895 = 2879843) B2879843
theorem B7289621 : Blo 1919435 7289621 := bbase (se 6 (by rfl) ⟨170850, by rfl⟩ : syracuseStep 7289621 = 341701) (by norm_num)
theorem B4859747 : Blo 1919435 4859747 := bstep (se 1 (by rfl) ⟨3644810, by rfl⟩ : syracuseStep 4859747 = 7289621) B7289621
theorem B3239831 : Blo 1919435 3239831 := bstep (se 1 (by rfl) ⟨2429873, by rfl⟩ : syracuseStep 3239831 = 4859747) B4859747
theorem B2159887 : Blo 1919435 2159887 := bstep (se 1 (by rfl) ⟨1619915, by rfl⟩ : syracuseStep 2159887 = 3239831) B3239831
theorem B2879849 : Blo 1919435 2879849 := bstep (se 2 (by rfl) ⟨1079943, by rfl⟩ : syracuseStep 2879849 = 2159887) B2159887
theorem B1919899 : Blo 1919435 1919899 := bstep (se 1 (by rfl) ⟨1439924, by rfl⟩ : syracuseStep 1919899 = 2879849) B2879849
theorem B10934453 : Blo 1919435 10934453 := bbase (se 5 (by rfl) ⟨512552, by rfl⟩ : syracuseStep 10934453 = 1025105) (by norm_num)
theorem B7289635 : Blo 1919435 7289635 := bstep (se 1 (by rfl) ⟨5467226, by rfl⟩ : syracuseStep 7289635 = 10934453) B10934453
theorem B9719513 : Blo 1919435 9719513 := bstep (se 2 (by rfl) ⟨3644817, by rfl⟩ : syracuseStep 9719513 = 7289635) B7289635
theorem B6479675 : Blo 1919435 6479675 := bstep (se 1 (by rfl) ⟨4859756, by rfl⟩ : syracuseStep 6479675 = 9719513) B9719513
theorem B4319783 : Blo 1919435 4319783 := bstep (se 1 (by rfl) ⟨3239837, by rfl⟩ : syracuseStep 4319783 = 6479675) B6479675
theorem B2879855 : Blo 1919435 2879855 := bstep (se 1 (by rfl) ⟨2159891, by rfl⟩ : syracuseStep 2879855 = 4319783) B4319783
theorem B1919903 : Blo 1919435 1919903 := bstep (se 1 (by rfl) ⟨1439927, by rfl⟩ : syracuseStep 1919903 = 2879855) B2879855
theorem B2879861 : Blo 1919435 2879861 := bbase (se 5 (by rfl) ⟨134993, by rfl⟩ : syracuseStep 2879861 = 269987) (by norm_num)
theorem B1919907 : Blo 1919435 1919907 := bstep (se 1 (by rfl) ⟨1439930, by rfl⟩ : syracuseStep 1919907 = 2879861) B2879861
theorem B2306497 : Blo 1919435 2306497 := bbase (se 2 (by rfl) ⟨864936, by rfl⟩ : syracuseStep 2306497 = 1729873) (by norm_num)
theorem B3075329 : Blo 1919435 3075329 := bstep (se 2 (by rfl) ⟨1153248, by rfl⟩ : syracuseStep 3075329 = 2306497) B2306497
theorem B2050219 : Blo 1919435 2050219 := bstep (se 1 (by rfl) ⟨1537664, by rfl⟩ : syracuseStep 2050219 = 3075329) B3075329
theorem B2733625 : Blo 1919435 2733625 := bstep (se 2 (by rfl) ⟨1025109, by rfl⟩ : syracuseStep 2733625 = 2050219) B2050219
theorem B3644833 : Blo 1919435 3644833 := bstep (se 2 (by rfl) ⟨1366812, by rfl⟩ : syracuseStep 3644833 = 2733625) B2733625
theorem B4859777 : Blo 1919435 4859777 := bstep (se 2 (by rfl) ⟨1822416, by rfl⟩ : syracuseStep 4859777 = 3644833) B3644833
theorem B3239851 : Blo 1919435 3239851 := bstep (se 1 (by rfl) ⟨2429888, by rfl⟩ : syracuseStep 3239851 = 4859777) B4859777
theorem B4319801 : Blo 1919435 4319801 := bstep (se 2 (by rfl) ⟨1619925, by rfl⟩ : syracuseStep 4319801 = 3239851) B3239851
theorem B2879867 : Blo 1919435 2879867 := bstep (se 1 (by rfl) ⟨2159900, by rfl⟩ : syracuseStep 2879867 = 4319801) B4319801
theorem B1919911 : Blo 1919435 1919911 := bstep (se 1 (by rfl) ⟨1439933, by rfl⟩ : syracuseStep 1919911 = 2879867) B2879867
theorem B2159905 : Blo 1919435 2159905 := bbase (se 2 (by rfl) ⟨809964, by rfl⟩ : syracuseStep 2159905 = 1619929) (by norm_num)
theorem B2879873 : Blo 1919435 2879873 := bstep (se 2 (by rfl) ⟨1079952, by rfl⟩ : syracuseStep 2879873 = 2159905) B2159905
theorem B1919915 : Blo 1919435 1919915 := bstep (se 1 (by rfl) ⟨1439936, by rfl⟩ : syracuseStep 1919915 = 2879873) B2879873
theorem B4859797 : Blo 1919435 4859797 := bbase (se 6 (by rfl) ⟨113901, by rfl⟩ : syracuseStep 4859797 = 227803) (by norm_num)
theorem B6479729 : Blo 1919435 6479729 := bstep (se 2 (by rfl) ⟨2429898, by rfl⟩ : syracuseStep 6479729 = 4859797) B4859797
theorem B4319819 : Blo 1919435 4319819 := bstep (se 1 (by rfl) ⟨3239864, by rfl⟩ : syracuseStep 4319819 = 6479729) B6479729
theorem B2879879 : Blo 1919435 2879879 := bstep (se 1 (by rfl) ⟨2159909, by rfl⟩ : syracuseStep 2879879 = 4319819) B4319819
theorem B1919919 : Blo 1919435 1919919 := bstep (se 1 (by rfl) ⟨1439939, by rfl⟩ : syracuseStep 1919919 = 2879879) B2879879
theorem B2879885 : Blo 1919435 2879885 := bbase (se 3 (by rfl) ⟨539978, by rfl⟩ : syracuseStep 2879885 = 1079957) (by norm_num)
theorem B1919923 : Blo 1919435 1919923 := bstep (se 1 (by rfl) ⟨1439942, by rfl⟩ : syracuseStep 1919923 = 2879885) B2879885
theorem B4319837 : Blo 1919435 4319837 := bbase (se 3 (by rfl) ⟨809969, by rfl⟩ : syracuseStep 4319837 = 1619939) (by norm_num)
theorem B2879891 : Blo 1919435 2879891 := bstep (se 1 (by rfl) ⟨2159918, by rfl⟩ : syracuseStep 2879891 = 4319837) B4319837
theorem B1919927 : Blo 1919435 1919927 := bstep (se 1 (by rfl) ⟨1439945, by rfl⟩ : syracuseStep 1919927 = 2879891) B2879891
theorem B3239885 : Blo 1919435 3239885 := bbase (se 3 (by rfl) ⟨607478, by rfl⟩ : syracuseStep 3239885 = 1214957) (by norm_num)
theorem B2159923 : Blo 1919435 2159923 := bstep (se 1 (by rfl) ⟨1619942, by rfl⟩ : syracuseStep 2159923 = 3239885) B3239885
theorem B2879897 : Blo 1919435 2879897 := bstep (se 2 (by rfl) ⟨1079961, by rfl⟩ : syracuseStep 2879897 = 2159923) B2159923
theorem B1919931 : Blo 1919435 1919931 := bstep (se 1 (by rfl) ⟨1439948, by rfl⟩ : syracuseStep 1919931 = 2879897) B2879897
theorem B3892261 : Blo 1919435 3892261 := bbase (se 4 (by rfl) ⟨364899, by rfl⟩ : syracuseStep 3892261 = 729799) (by norm_num)
theorem B5189681 : Blo 1919435 5189681 := bstep (se 2 (by rfl) ⟨1946130, by rfl⟩ : syracuseStep 5189681 = 3892261) B3892261
theorem B13839149 : Blo 1919435 13839149 := bstep (se 3 (by rfl) ⟨2594840, by rfl⟩ : syracuseStep 13839149 = 5189681) B5189681
theorem B9226099 : Blo 1919435 9226099 := bstep (se 1 (by rfl) ⟨6919574, by rfl⟩ : syracuseStep 9226099 = 13839149) B13839149
theorem B12301465 : Blo 1919435 12301465 := bstep (se 2 (by rfl) ⟨4613049, by rfl⟩ : syracuseStep 12301465 = 9226099) B9226099
theorem B16401953 : Blo 1919435 16401953 := bstep (se 2 (by rfl) ⟨6150732, by rfl⟩ : syracuseStep 16401953 = 12301465) B12301465
theorem B10934635 : Blo 1919435 10934635 := bstep (se 1 (by rfl) ⟨8200976, by rfl⟩ : syracuseStep 10934635 = 16401953) B16401953
theorem B14579513 : Blo 1919435 14579513 := bstep (se 2 (by rfl) ⟨5467317, by rfl⟩ : syracuseStep 14579513 = 10934635) B10934635
theorem B9719675 : Blo 1919435 9719675 := bstep (se 1 (by rfl) ⟨7289756, by rfl⟩ : syracuseStep 9719675 = 14579513) B14579513
theorem B6479783 : Blo 1919435 6479783 := bstep (se 1 (by rfl) ⟨4859837, by rfl⟩ : syracuseStep 6479783 = 9719675) B9719675
theorem B4319855 : Blo 1919435 4319855 := bstep (se 1 (by rfl) ⟨3239891, by rfl⟩ : syracuseStep 4319855 = 6479783) B6479783
theorem B2879903 : Blo 1919435 2879903 := bstep (se 1 (by rfl) ⟨2159927, by rfl⟩ : syracuseStep 2879903 = 4319855) B4319855
theorem B1919935 : Blo 1919435 1919935 := bstep (se 1 (by rfl) ⟨1439951, by rfl⟩ : syracuseStep 1919935 = 2879903) B2879903
theorem B2879909 : Blo 1919435 2879909 := bbase (se 4 (by rfl) ⟨269991, by rfl⟩ : syracuseStep 2879909 = 539983) (by norm_num)
theorem B1919939 : Blo 1919435 1919939 := bstep (se 1 (by rfl) ⟨1439954, by rfl⟩ : syracuseStep 1919939 = 2879909) B2879909
theorem B2429929 : Blo 1919435 2429929 := bbase (se 2 (by rfl) ⟨911223, by rfl⟩ : syracuseStep 2429929 = 1822447) (by norm_num)
theorem B3239905 : Blo 1919435 3239905 := bstep (se 2 (by rfl) ⟨1214964, by rfl⟩ : syracuseStep 3239905 = 2429929) B2429929
theorem B4319873 : Blo 1919435 4319873 := bstep (se 2 (by rfl) ⟨1619952, by rfl⟩ : syracuseStep 4319873 = 3239905) B3239905
theorem B2879915 : Blo 1919435 2879915 := bstep (se 1 (by rfl) ⟨2159936, by rfl⟩ : syracuseStep 2879915 = 4319873) B4319873
theorem B1919943 : Blo 1919435 1919943 := bstep (se 1 (by rfl) ⟨1439957, by rfl⟩ : syracuseStep 1919943 = 2879915) B2879915
theorem B2159941 : Blo 1919435 2159941 := bbase (se 4 (by rfl) ⟨202494, by rfl⟩ : syracuseStep 2159941 = 404989) (by norm_num)
theorem B2879921 : Blo 1919435 2879921 := bstep (se 2 (by rfl) ⟨1079970, by rfl⟩ : syracuseStep 2879921 = 2159941) B2159941
theorem B1919947 : Blo 1919435 1919947 := bstep (se 1 (by rfl) ⟨1439960, by rfl⟩ : syracuseStep 1919947 = 2879921) B2879921
theorem B3644909 : Blo 1919435 3644909 := bbase (se 3 (by rfl) ⟨683420, by rfl⟩ : syracuseStep 3644909 = 1366841) (by norm_num)
theorem B2429939 : Blo 1919435 2429939 := bstep (se 1 (by rfl) ⟨1822454, by rfl⟩ : syracuseStep 2429939 = 3644909) B3644909
theorem B6479837 : Blo 1919435 6479837 := bstep (se 3 (by rfl) ⟨1214969, by rfl⟩ : syracuseStep 6479837 = 2429939) B2429939
theorem B4319891 : Blo 1919435 4319891 := bstep (se 1 (by rfl) ⟨3239918, by rfl⟩ : syracuseStep 4319891 = 6479837) B6479837
theorem B2879927 : Blo 1919435 2879927 := bstep (se 1 (by rfl) ⟨2159945, by rfl⟩ : syracuseStep 2879927 = 4319891) B4319891
theorem B1919951 : Blo 1919435 1919951 := bstep (se 1 (by rfl) ⟨1439963, by rfl⟩ : syracuseStep 1919951 = 2879927) B2879927
theorem B2879933 : Blo 1919435 2879933 := bbase (se 3 (by rfl) ⟨539987, by rfl⟩ : syracuseStep 2879933 = 1079975) (by norm_num)
theorem B1919955 : Blo 1919435 1919955 := bstep (se 1 (by rfl) ⟨1439966, by rfl⟩ : syracuseStep 1919955 = 2879933) B2879933
theorem B4319909 : Blo 1919435 4319909 := bbase (se 4 (by rfl) ⟨404991, by rfl⟩ : syracuseStep 4319909 = 809983) (by norm_num)
theorem B2879939 : Blo 1919435 2879939 := bstep (se 1 (by rfl) ⟨2159954, by rfl⟩ : syracuseStep 2879939 = 4319909) B4319909
theorem B1919959 : Blo 1919435 1919959 := bstep (se 1 (by rfl) ⟨1439969, by rfl⟩ : syracuseStep 1919959 = 2879939) B2879939
theorem B4859909 : Blo 1919435 4859909 := bbase (se 4 (by rfl) ⟨455616, by rfl⟩ : syracuseStep 4859909 = 911233) (by norm_num)
theorem B3239939 : Blo 1919435 3239939 := bstep (se 1 (by rfl) ⟨2429954, by rfl⟩ : syracuseStep 3239939 = 4859909) B4859909
theorem B2159959 : Blo 1919435 2159959 := bstep (se 1 (by rfl) ⟨1619969, by rfl⟩ : syracuseStep 2159959 = 3239939) B3239939
theorem B2879945 : Blo 1919435 2879945 := bstep (se 2 (by rfl) ⟨1079979, by rfl⟩ : syracuseStep 2879945 = 2159959) B2159959
theorem B1919963 : Blo 1919435 1919963 := bstep (se 1 (by rfl) ⟨1439972, by rfl⟩ : syracuseStep 1919963 = 2879945) B2879945
theorem B4100557 : Blo 1919435 4100557 := bbase (se 3 (by rfl) ⟨768854, by rfl⟩ : syracuseStep 4100557 = 1537709) (by norm_num)
theorem B5467409 : Blo 1919435 5467409 := bstep (se 2 (by rfl) ⟨2050278, by rfl⟩ : syracuseStep 5467409 = 4100557) B4100557
theorem B3644939 : Blo 1919435 3644939 := bstep (se 1 (by rfl) ⟨2733704, by rfl⟩ : syracuseStep 3644939 = 5467409) B5467409
theorem B9719837 : Blo 1919435 9719837 := bstep (se 3 (by rfl) ⟨1822469, by rfl⟩ : syracuseStep 9719837 = 3644939) B3644939
theorem B6479891 : Blo 1919435 6479891 := bstep (se 1 (by rfl) ⟨4859918, by rfl⟩ : syracuseStep 6479891 = 9719837) B9719837
theorem B4319927 : Blo 1919435 4319927 := bstep (se 1 (by rfl) ⟨3239945, by rfl⟩ : syracuseStep 4319927 = 6479891) B6479891
theorem B2879951 : Blo 1919435 2879951 := bstep (se 1 (by rfl) ⟨2159963, by rfl⟩ : syracuseStep 2879951 = 4319927) B4319927
theorem B1919967 : Blo 1919435 1919967 := bstep (se 1 (by rfl) ⟨1439975, by rfl⟩ : syracuseStep 1919967 = 2879951) B2879951
theorem B2879957 : Blo 1919435 2879957 := bbase (se 7 (by rfl) ⟨33749, by rfl⟩ : syracuseStep 2879957 = 67499) (by norm_num)
theorem B1919971 : Blo 1919435 1919971 := bstep (se 1 (by rfl) ⟨1439978, by rfl⟩ : syracuseStep 1919971 = 2879957) B2879957
theorem B7289909 : Blo 1919435 7289909 := bbase (se 5 (by rfl) ⟨341714, by rfl⟩ : syracuseStep 7289909 = 683429) (by norm_num)
theorem B4859939 : Blo 1919435 4859939 := bstep (se 1 (by rfl) ⟨3644954, by rfl⟩ : syracuseStep 4859939 = 7289909) B7289909
theorem B3239959 : Blo 1919435 3239959 := bstep (se 1 (by rfl) ⟨2429969, by rfl⟩ : syracuseStep 3239959 = 4859939) B4859939
theorem B4319945 : Blo 1919435 4319945 := bstep (se 2 (by rfl) ⟨1619979, by rfl⟩ : syracuseStep 4319945 = 3239959) B3239959
theorem B2879963 : Blo 1919435 2879963 := bstep (se 1 (by rfl) ⟨2159972, by rfl⟩ : syracuseStep 2879963 = 4319945) B4319945
theorem B1919975 : Blo 1919435 1919975 := bstep (se 1 (by rfl) ⟨1439981, by rfl⟩ : syracuseStep 1919975 = 2879963) B2879963
theorem B2159977 : Blo 1919435 2159977 := bbase (se 2 (by rfl) ⟨809991, by rfl⟩ : syracuseStep 2159977 = 1619983) (by norm_num)
theorem B2879969 : Blo 1919435 2879969 := bstep (se 2 (by rfl) ⟨1079988, by rfl⟩ : syracuseStep 2879969 = 2159977) B2159977
theorem B1919979 : Blo 1919435 1919979 := bstep (se 1 (by rfl) ⟨1439984, by rfl⟩ : syracuseStep 1919979 = 2879969) B2879969
theorem B17315989 : Blo 1919435 17315989 := bbase (se 6 (by rfl) ⟨405843, by rfl⟩ : syracuseStep 17315989 = 811687) (by norm_num)
theorem B369407765 : Blo 1919435 369407765 := bstep (se 6 (by rfl) ⟨8657994, by rfl⟩ : syracuseStep 369407765 = 17315989) B17315989
theorem B246271843 : Blo 1919435 246271843 := bstep (se 1 (by rfl) ⟨184703882, by rfl⟩ : syracuseStep 246271843 = 369407765) B369407765
theorem B328362457 : Blo 1919435 328362457 := bstep (se 2 (by rfl) ⟨123135921, by rfl⟩ : syracuseStep 328362457 = 246271843) B246271843
theorem B437816609 : Blo 1919435 437816609 := bstep (se 2 (by rfl) ⟨164181228, by rfl⟩ : syracuseStep 437816609 = 328362457) B328362457
theorem B291877739 : Blo 1919435 291877739 := bstep (se 1 (by rfl) ⟨218908304, by rfl⟩ : syracuseStep 291877739 = 437816609) B437816609
theorem B194585159 : Blo 1919435 194585159 := bstep (se 1 (by rfl) ⟨145938869, by rfl⟩ : syracuseStep 194585159 = 291877739) B291877739
theorem B129723439 : Blo 1919435 129723439 := bstep (se 1 (by rfl) ⟨97292579, by rfl⟩ : syracuseStep 129723439 = 194585159) B194585159
theorem B172964585 : Blo 1919435 172964585 := bstep (se 2 (by rfl) ⟨64861719, by rfl⟩ : syracuseStep 172964585 = 129723439) B129723439
theorem B461238893 : Blo 1919435 461238893 := bstep (se 3 (by rfl) ⟨86482292, by rfl⟩ : syracuseStep 461238893 = 172964585) B172964585
theorem B307492595 : Blo 1919435 307492595 := bstep (se 1 (by rfl) ⟨230619446, by rfl⟩ : syracuseStep 307492595 = 461238893) B461238893
theorem B204995063 : Blo 1919435 204995063 := bstep (se 1 (by rfl) ⟨153746297, by rfl⟩ : syracuseStep 204995063 = 307492595) B307492595
theorem B136663375 : Blo 1919435 136663375 := bstep (se 1 (by rfl) ⟨102497531, by rfl⟩ : syracuseStep 136663375 = 204995063) B204995063
theorem B182217833 : Blo 1919435 182217833 := bstep (se 2 (by rfl) ⟨68331687, by rfl⟩ : syracuseStep 182217833 = 136663375) B136663375
theorem B121478555 : Blo 1919435 121478555 := bstep (se 1 (by rfl) ⟨91108916, by rfl⟩ : syracuseStep 121478555 = 182217833) B182217833
theorem B80985703 : Blo 1919435 80985703 := bstep (se 1 (by rfl) ⟨60739277, by rfl⟩ : syracuseStep 80985703 = 121478555) B121478555
theorem B107980937 : Blo 1919435 107980937 := bstep (se 2 (by rfl) ⟨40492851, by rfl⟩ : syracuseStep 107980937 = 80985703) B80985703
theorem B71987291 : Blo 1919435 71987291 := bstep (se 1 (by rfl) ⟨53990468, by rfl⟩ : syracuseStep 71987291 = 107980937) B107980937
theorem B47991527 : Blo 1919435 47991527 := bstep (se 1 (by rfl) ⟨35993645, by rfl⟩ : syracuseStep 47991527 = 71987291) B71987291
theorem B31994351 : Blo 1919435 31994351 := bstep (se 1 (by rfl) ⟨23995763, by rfl⟩ : syracuseStep 31994351 = 47991527) B47991527
theorem B21329567 : Blo 1919435 21329567 := bstep (se 1 (by rfl) ⟨15997175, by rfl⟩ : syracuseStep 21329567 = 31994351) B31994351
theorem B14219711 : Blo 1919435 14219711 := bstep (se 1 (by rfl) ⟨10664783, by rfl⟩ : syracuseStep 14219711 = 21329567) B21329567
theorem B9479807 : Blo 1919435 9479807 := bstep (se 1 (by rfl) ⟨7109855, by rfl⟩ : syracuseStep 9479807 = 14219711) B14219711
theorem B6319871 : Blo 1919435 6319871 := bstep (se 1 (by rfl) ⟨4739903, by rfl⟩ : syracuseStep 6319871 = 9479807) B9479807
theorem B4213247 : Blo 1919435 4213247 := bstep (se 1 (by rfl) ⟨3159935, by rfl⟩ : syracuseStep 4213247 = 6319871) B6319871
theorem B44941301 : Blo 1919435 44941301 := bstep (se 5 (by rfl) ⟨2106623, by rfl⟩ : syracuseStep 44941301 = 4213247) B4213247
theorem B29960867 : Blo 1919435 29960867 := bstep (se 1 (by rfl) ⟨22470650, by rfl⟩ : syracuseStep 29960867 = 44941301) B44941301
theorem B79895645 : Blo 1919435 79895645 := bstep (se 3 (by rfl) ⟨14980433, by rfl⟩ : syracuseStep 79895645 = 29960867) B29960867
theorem B53263763 : Blo 1919435 53263763 := bstep (se 1 (by rfl) ⟨39947822, by rfl⟩ : syracuseStep 53263763 = 79895645) B79895645
theorem B35509175 : Blo 1919435 35509175 := bstep (se 1 (by rfl) ⟨26631881, by rfl⟩ : syracuseStep 35509175 = 53263763) B53263763
theorem B23672783 : Blo 1919435 23672783 := bstep (se 1 (by rfl) ⟨17754587, by rfl⟩ : syracuseStep 23672783 = 35509175) B35509175
theorem B63127421 : Blo 1919435 63127421 := bstep (se 3 (by rfl) ⟨11836391, by rfl⟩ : syracuseStep 63127421 = 23672783) B23672783
theorem B42084947 : Blo 1919435 42084947 := bstep (se 1 (by rfl) ⟨31563710, by rfl⟩ : syracuseStep 42084947 = 63127421) B63127421
theorem B28056631 : Blo 1919435 28056631 := bstep (se 1 (by rfl) ⟨21042473, by rfl⟩ : syracuseStep 28056631 = 42084947) B42084947
theorem B37408841 : Blo 1919435 37408841 := bstep (se 2 (by rfl) ⟨14028315, by rfl⟩ : syracuseStep 37408841 = 28056631) B28056631
theorem B24939227 : Blo 1919435 24939227 := bstep (se 1 (by rfl) ⟨18704420, by rfl⟩ : syracuseStep 24939227 = 37408841) B37408841
theorem B16626151 : Blo 1919435 16626151 := bstep (se 1 (by rfl) ⟨12469613, by rfl⟩ : syracuseStep 16626151 = 24939227) B24939227
theorem B88672805 : Blo 1919435 88672805 := bstep (se 4 (by rfl) ⟨8313075, by rfl⟩ : syracuseStep 88672805 = 16626151) B16626151
theorem B59115203 : Blo 1919435 59115203 := bstep (se 1 (by rfl) ⟨44336402, by rfl⟩ : syracuseStep 59115203 = 88672805) B88672805
theorem B39410135 : Blo 1919435 39410135 := bstep (se 1 (by rfl) ⟨29557601, by rfl⟩ : syracuseStep 39410135 = 59115203) B59115203
theorem B26273423 : Blo 1919435 26273423 := bstep (se 1 (by rfl) ⟨19705067, by rfl⟩ : syracuseStep 26273423 = 39410135) B39410135
theorem B17515615 : Blo 1919435 17515615 := bstep (se 1 (by rfl) ⟨13136711, by rfl⟩ : syracuseStep 17515615 = 26273423) B26273423
theorem B23354153 : Blo 1919435 23354153 := bstep (se 2 (by rfl) ⟨8757807, by rfl⟩ : syracuseStep 23354153 = 17515615) B17515615
theorem B15569435 : Blo 1919435 15569435 := bstep (se 1 (by rfl) ⟨11677076, by rfl⟩ : syracuseStep 15569435 = 23354153) B23354153
theorem B10379623 : Blo 1919435 10379623 := bstep (se 1 (by rfl) ⟨7784717, by rfl⟩ : syracuseStep 10379623 = 15569435) B15569435
theorem B13839497 : Blo 1919435 13839497 := bstep (se 2 (by rfl) ⟨5189811, by rfl⟩ : syracuseStep 13839497 = 10379623) B10379623
theorem B9226331 : Blo 1919435 9226331 := bstep (se 1 (by rfl) ⟨6919748, by rfl⟩ : syracuseStep 9226331 = 13839497) B13839497
theorem B6150887 : Blo 1919435 6150887 := bstep (se 1 (by rfl) ⟨4613165, by rfl⟩ : syracuseStep 6150887 = 9226331) B9226331
theorem B4100591 : Blo 1919435 4100591 := bstep (se 1 (by rfl) ⟨3075443, by rfl⟩ : syracuseStep 4100591 = 6150887) B6150887
theorem B10934909 : Blo 1919435 10934909 := bstep (se 3 (by rfl) ⟨2050295, by rfl⟩ : syracuseStep 10934909 = 4100591) B4100591
theorem B7289939 : Blo 1919435 7289939 := bstep (se 1 (by rfl) ⟨5467454, by rfl⟩ : syracuseStep 7289939 = 10934909) B10934909
theorem B4859959 : Blo 1919435 4859959 := bstep (se 1 (by rfl) ⟨3644969, by rfl⟩ : syracuseStep 4859959 = 7289939) B7289939
theorem B6479945 : Blo 1919435 6479945 := bstep (se 2 (by rfl) ⟨2429979, by rfl⟩ : syracuseStep 6479945 = 4859959) B4859959
theorem B4319963 : Blo 1919435 4319963 := bstep (se 1 (by rfl) ⟨3239972, by rfl⟩ : syracuseStep 4319963 = 6479945) B6479945
theorem B2879975 : Blo 1919435 2879975 := bstep (se 1 (by rfl) ⟨2159981, by rfl⟩ : syracuseStep 2879975 = 4319963) B4319963
theorem B1919983 : Blo 1919435 1919983 := bstep (se 1 (by rfl) ⟨1439987, by rfl⟩ : syracuseStep 1919983 = 2879975) B2879975
theorem B2879981 : Blo 1919435 2879981 := bbase (se 3 (by rfl) ⟨539996, by rfl⟩ : syracuseStep 2879981 = 1079993) (by norm_num)
theorem B1919987 : Blo 1919435 1919987 := bstep (se 1 (by rfl) ⟨1439990, by rfl⟩ : syracuseStep 1919987 = 2879981) B2879981
theorem B4319981 : Blo 1919435 4319981 := bbase (se 3 (by rfl) ⟨809996, by rfl⟩ : syracuseStep 4319981 = 1619993) (by norm_num)
theorem B2879987 : Blo 1919435 2879987 := bstep (se 1 (by rfl) ⟨2159990, by rfl⟩ : syracuseStep 2879987 = 4319981) B4319981
theorem B1919991 : Blo 1919435 1919991 := bstep (se 1 (by rfl) ⟨1439993, by rfl⟩ : syracuseStep 1919991 = 2879987) B2879987
theorem B2050309 : Blo 1919435 2050309 := bbase (se 4 (by rfl) ⟨192216, by rfl⟩ : syracuseStep 2050309 = 384433) (by norm_num)
theorem B2733745 : Blo 1919435 2733745 := bstep (se 2 (by rfl) ⟨1025154, by rfl⟩ : syracuseStep 2733745 = 2050309) B2050309
theorem B3644993 : Blo 1919435 3644993 := bstep (se 2 (by rfl) ⟨1366872, by rfl⟩ : syracuseStep 3644993 = 2733745) B2733745
theorem B2429995 : Blo 1919435 2429995 := bstep (se 1 (by rfl) ⟨1822496, by rfl⟩ : syracuseStep 2429995 = 3644993) B3644993
theorem B3239993 : Blo 1919435 3239993 := bstep (se 2 (by rfl) ⟨1214997, by rfl⟩ : syracuseStep 3239993 = 2429995) B2429995
theorem B2159995 : Blo 1919435 2159995 := bstep (se 1 (by rfl) ⟨1619996, by rfl⟩ : syracuseStep 2159995 = 3239993) B3239993
theorem B2879993 : Blo 1919435 2879993 := bstep (se 2 (by rfl) ⟨1079997, by rfl⟩ : syracuseStep 2879993 = 2159995) B2159995
theorem B1919995 : Blo 1919435 1919995 := bstep (se 1 (by rfl) ⟨1439996, by rfl⟩ : syracuseStep 1919995 = 2879993) B2879993
theorem B7389461 : Blo 1919435 7389461 := bbase (se 6 (by rfl) ⟨173190, by rfl⟩ : syracuseStep 7389461 = 346381) (by norm_num)
theorem B4926307 : Blo 1919435 4926307 := bstep (se 1 (by rfl) ⟨3694730, by rfl⟩ : syracuseStep 4926307 = 7389461) B7389461
theorem B6568409 : Blo 1919435 6568409 := bstep (se 2 (by rfl) ⟨2463153, by rfl⟩ : syracuseStep 6568409 = 4926307) B4926307
theorem B17515757 : Blo 1919435 17515757 := bstep (se 3 (by rfl) ⟨3284204, by rfl⟩ : syracuseStep 17515757 = 6568409) B6568409
theorem B11677171 : Blo 1919435 11677171 := bstep (se 1 (by rfl) ⟨8757878, by rfl⟩ : syracuseStep 11677171 = 17515757) B17515757
theorem B15569561 : Blo 1919435 15569561 := bstep (se 2 (by rfl) ⟨5838585, by rfl⟩ : syracuseStep 15569561 = 11677171) B11677171
theorem B10379707 : Blo 1919435 10379707 := bstep (se 1 (by rfl) ⟨7784780, by rfl⟩ : syracuseStep 10379707 = 15569561) B15569561
theorem B55358437 : Blo 1919435 55358437 := bstep (se 4 (by rfl) ⟨5189853, by rfl⟩ : syracuseStep 55358437 = 10379707) B10379707
theorem B73811249 : Blo 1919435 73811249 := bstep (se 2 (by rfl) ⟨27679218, by rfl⟩ : syracuseStep 73811249 = 55358437) B55358437
theorem B49207499 : Blo 1919435 49207499 := bstep (se 1 (by rfl) ⟨36905624, by rfl⟩ : syracuseStep 49207499 = 73811249) B73811249
theorem B32804999 : Blo 1919435 32804999 := bstep (se 1 (by rfl) ⟨24603749, by rfl⟩ : syracuseStep 32804999 = 49207499) B49207499
theorem B21869999 : Blo 1919435 21869999 := bstep (se 1 (by rfl) ⟨16402499, by rfl⟩ : syracuseStep 21869999 = 32804999) B32804999
theorem B14579999 : Blo 1919435 14579999 := bstep (se 1 (by rfl) ⟨10934999, by rfl⟩ : syracuseStep 14579999 = 21869999) B21869999
theorem B9719999 : Blo 1919435 9719999 := bstep (se 1 (by rfl) ⟨7289999, by rfl⟩ : syracuseStep 9719999 = 14579999) B14579999
theorem B6479999 : Blo 1919435 6479999 := bstep (se 1 (by rfl) ⟨4859999, by rfl⟩ : syracuseStep 6479999 = 9719999) B9719999
theorem B4319999 : Blo 1919435 4319999 := bstep (se 1 (by rfl) ⟨3239999, by rfl⟩ : syracuseStep 4319999 = 6479999) B6479999
theorem B2879999 : Blo 1919435 2879999 := bstep (se 1 (by rfl) ⟨2159999, by rfl⟩ : syracuseStep 2879999 = 4319999) B4319999
theorem B1919999 : Blo 1919435 1919999 := bstep (se 1 (by rfl) ⟨1439999, by rfl⟩ : syracuseStep 1919999 = 2879999) B2879999
theorem B2880005 : Blo 1919435 2880005 := bbase (se 4 (by rfl) ⟨270000, by rfl⟩ : syracuseStep 2880005 = 540001) (by norm_num)
theorem B1920003 : Blo 1919435 1920003 := bstep (se 1 (by rfl) ⟨1440002, by rfl⟩ : syracuseStep 1920003 = 2880005) B2880005
theorem B3240013 : Blo 1919435 3240013 := bbase (se 3 (by rfl) ⟨607502, by rfl⟩ : syracuseStep 3240013 = 1215005) (by norm_num)
theorem B4320017 : Blo 1919435 4320017 := bstep (se 2 (by rfl) ⟨1620006, by rfl⟩ : syracuseStep 4320017 = 3240013) B3240013
theorem B2880011 : Blo 1919435 2880011 := bstep (se 1 (by rfl) ⟨2160008, by rfl⟩ : syracuseStep 2880011 = 4320017) B4320017
theorem B1920007 : Blo 1919435 1920007 := bstep (se 1 (by rfl) ⟨1440005, by rfl⟩ : syracuseStep 1920007 = 2880011) B2880011
theorem B2160013 : Blo 1919435 2160013 := bbase (se 3 (by rfl) ⟨405002, by rfl⟩ : syracuseStep 2160013 = 810005) (by norm_num)
theorem B2880017 : Blo 1919435 2880017 := bstep (se 2 (by rfl) ⟨1080006, by rfl⟩ : syracuseStep 2880017 = 2160013) B2160013
theorem B1920011 : Blo 1919435 1920011 := bstep (se 1 (by rfl) ⟨1440008, by rfl⟩ : syracuseStep 1920011 = 2880017) B2880017
theorem B6480053 : Blo 1919435 6480053 := bbase (se 5 (by rfl) ⟨303752, by rfl⟩ : syracuseStep 6480053 = 607505) (by norm_num)
theorem B4320035 : Blo 1919435 4320035 := bstep (se 1 (by rfl) ⟨3240026, by rfl⟩ : syracuseStep 4320035 = 6480053) B6480053
theorem B2880023 : Blo 1919435 2880023 := bstep (se 1 (by rfl) ⟨2160017, by rfl⟩ : syracuseStep 2880023 = 4320035) B4320035
theorem B1920015 : Blo 1919435 1920015 := bstep (se 1 (by rfl) ⟨1440011, by rfl⟩ : syracuseStep 1920015 = 2880023) B2880023
theorem B2880029 : Blo 1919435 2880029 := bbase (se 3 (by rfl) ⟨540005, by rfl⟩ : syracuseStep 2880029 = 1080011) (by norm_num)
theorem B1920019 : Blo 1919435 1920019 := bstep (se 1 (by rfl) ⟨1440014, by rfl⟩ : syracuseStep 1920019 = 2880029) B2880029
theorem B4320053 : Blo 1919435 4320053 := bbase (se 5 (by rfl) ⟨202502, by rfl⟩ : syracuseStep 4320053 = 405005) (by norm_num)
theorem B2880035 : Blo 1919435 2880035 := bstep (se 1 (by rfl) ⟨2160026, by rfl⟩ : syracuseStep 2880035 = 4320053) B4320053
theorem B1920023 : Blo 1919435 1920023 := bstep (se 1 (by rfl) ⟨1440017, by rfl⟩ : syracuseStep 1920023 = 2880035) B2880035
theorem B13137013 : Blo 1919435 13137013 := bbase (se 5 (by rfl) ⟨615797, by rfl⟩ : syracuseStep 13137013 = 1231595) (by norm_num)
theorem B17516017 : Blo 1919435 17516017 := bstep (se 2 (by rfl) ⟨6568506, by rfl⟩ : syracuseStep 17516017 = 13137013) B13137013
theorem B23354689 : Blo 1919435 23354689 := bstep (se 2 (by rfl) ⟨8758008, by rfl⟩ : syracuseStep 23354689 = 17516017) B17516017
theorem B31139585 : Blo 1919435 31139585 := bstep (se 2 (by rfl) ⟨11677344, by rfl⟩ : syracuseStep 31139585 = 23354689) B23354689
theorem B20759723 : Blo 1919435 20759723 := bstep (se 1 (by rfl) ⟨15569792, by rfl⟩ : syracuseStep 20759723 = 31139585) B31139585
theorem B13839815 : Blo 1919435 13839815 := bstep (se 1 (by rfl) ⟨10379861, by rfl⟩ : syracuseStep 13839815 = 20759723) B20759723
theorem B9226543 : Blo 1919435 9226543 := bstep (se 1 (by rfl) ⟨6919907, by rfl⟩ : syracuseStep 9226543 = 13839815) B13839815
theorem B12302057 : Blo 1919435 12302057 := bstep (se 2 (by rfl) ⟨4613271, by rfl⟩ : syracuseStep 12302057 = 9226543) B9226543
theorem B8201371 : Blo 1919435 8201371 := bstep (se 1 (by rfl) ⟨6151028, by rfl⟩ : syracuseStep 8201371 = 12302057) B12302057
theorem B10935161 : Blo 1919435 10935161 := bstep (se 2 (by rfl) ⟨4100685, by rfl⟩ : syracuseStep 10935161 = 8201371) B8201371
theorem B7290107 : Blo 1919435 7290107 := bstep (se 1 (by rfl) ⟨5467580, by rfl⟩ : syracuseStep 7290107 = 10935161) B10935161
theorem B4860071 : Blo 1919435 4860071 := bstep (se 1 (by rfl) ⟨3645053, by rfl⟩ : syracuseStep 4860071 = 7290107) B7290107
theorem B3240047 : Blo 1919435 3240047 := bstep (se 1 (by rfl) ⟨2430035, by rfl⟩ : syracuseStep 3240047 = 4860071) B4860071
theorem B2160031 : Blo 1919435 2160031 := bstep (se 1 (by rfl) ⟨1620023, by rfl⟩ : syracuseStep 2160031 = 3240047) B3240047
theorem B2880041 : Blo 1919435 2880041 := bstep (se 2 (by rfl) ⟨1080015, by rfl⟩ : syracuseStep 2880041 = 2160031) B2160031
theorem B1920027 : Blo 1919435 1920027 := bstep (se 1 (by rfl) ⟨1440020, by rfl⟩ : syracuseStep 1920027 = 2880041) B2880041
theorem B5189941 : Blo 1919435 5189941 := bbase (se 5 (by rfl) ⟨243278, by rfl⟩ : syracuseStep 5189941 = 486557) (by norm_num)
theorem B6919921 : Blo 1919435 6919921 := bstep (se 2 (by rfl) ⟨2594970, by rfl⟩ : syracuseStep 6919921 = 5189941) B5189941
theorem B9226561 : Blo 1919435 9226561 := bstep (se 2 (by rfl) ⟨3459960, by rfl⟩ : syracuseStep 9226561 = 6919921) B6919921
theorem B12302081 : Blo 1919435 12302081 := bstep (se 2 (by rfl) ⟨4613280, by rfl⟩ : syracuseStep 12302081 = 9226561) B9226561
theorem B8201387 : Blo 1919435 8201387 := bstep (se 1 (by rfl) ⟨6151040, by rfl⟩ : syracuseStep 8201387 = 12302081) B12302081
theorem B5467591 : Blo 1919435 5467591 := bstep (se 1 (by rfl) ⟨4100693, by rfl⟩ : syracuseStep 5467591 = 8201387) B8201387
theorem B7290121 : Blo 1919435 7290121 := bstep (se 2 (by rfl) ⟨2733795, by rfl⟩ : syracuseStep 7290121 = 5467591) B5467591
theorem B9720161 : Blo 1919435 9720161 := bstep (se 2 (by rfl) ⟨3645060, by rfl⟩ : syracuseStep 9720161 = 7290121) B7290121
theorem B6480107 : Blo 1919435 6480107 := bstep (se 1 (by rfl) ⟨4860080, by rfl⟩ : syracuseStep 6480107 = 9720161) B9720161
theorem B4320071 : Blo 1919435 4320071 := bstep (se 1 (by rfl) ⟨3240053, by rfl⟩ : syracuseStep 4320071 = 6480107) B6480107
theorem B2880047 : Blo 1919435 2880047 := bstep (se 1 (by rfl) ⟨2160035, by rfl⟩ : syracuseStep 2880047 = 4320071) B4320071
theorem B1920031 : Blo 1919435 1920031 := bstep (se 1 (by rfl) ⟨1440023, by rfl⟩ : syracuseStep 1920031 = 2880047) B2880047
theorem B2880053 : Blo 1919435 2880053 := bbase (se 5 (by rfl) ⟨135002, by rfl⟩ : syracuseStep 2880053 = 270005) (by norm_num)
theorem B1920035 : Blo 1919435 1920035 := bstep (se 1 (by rfl) ⟨1440026, by rfl⟩ : syracuseStep 1920035 = 2880053) B2880053
theorem B4860101 : Blo 1919435 4860101 := bbase (se 4 (by rfl) ⟨455634, by rfl⟩ : syracuseStep 4860101 = 911269) (by norm_num)
theorem B3240067 : Blo 1919435 3240067 := bstep (se 1 (by rfl) ⟨2430050, by rfl⟩ : syracuseStep 3240067 = 4860101) B4860101
theorem B4320089 : Blo 1919435 4320089 := bstep (se 2 (by rfl) ⟨1620033, by rfl⟩ : syracuseStep 4320089 = 3240067) B3240067
theorem B2880059 : Blo 1919435 2880059 := bstep (se 1 (by rfl) ⟨2160044, by rfl⟩ : syracuseStep 2880059 = 4320089) B4320089
theorem B1920039 : Blo 1919435 1920039 := bstep (se 1 (by rfl) ⟨1440029, by rfl⟩ : syracuseStep 1920039 = 2880059) B2880059
theorem B2160049 : Blo 1919435 2160049 := bbase (se 2 (by rfl) ⟨810018, by rfl⟩ : syracuseStep 2160049 = 1620037) (by norm_num)
theorem B2880065 : Blo 1919435 2880065 := bstep (se 2 (by rfl) ⟨1080024, by rfl⟩ : syracuseStep 2880065 = 2160049) B2160049
theorem B1920043 : Blo 1919435 1920043 := bstep (se 1 (by rfl) ⟨1440032, by rfl⟩ : syracuseStep 1920043 = 2880065) B2880065
theorem B5467637 : Blo 1919435 5467637 := bbase (se 5 (by rfl) ⟨256295, by rfl⟩ : syracuseStep 5467637 = 512591) (by norm_num)
theorem B3645091 : Blo 1919435 3645091 := bstep (se 1 (by rfl) ⟨2733818, by rfl⟩ : syracuseStep 3645091 = 5467637) B5467637
theorem B4860121 : Blo 1919435 4860121 := bstep (se 2 (by rfl) ⟨1822545, by rfl⟩ : syracuseStep 4860121 = 3645091) B3645091
theorem B6480161 : Blo 1919435 6480161 := bstep (se 2 (by rfl) ⟨2430060, by rfl⟩ : syracuseStep 6480161 = 4860121) B4860121
theorem B4320107 : Blo 1919435 4320107 := bstep (se 1 (by rfl) ⟨3240080, by rfl⟩ : syracuseStep 4320107 = 6480161) B6480161
theorem B2880071 : Blo 1919435 2880071 := bstep (se 1 (by rfl) ⟨2160053, by rfl⟩ : syracuseStep 2880071 = 4320107) B4320107
theorem B1920047 : Blo 1919435 1920047 := bstep (se 1 (by rfl) ⟨1440035, by rfl⟩ : syracuseStep 1920047 = 2880071) B2880071
theorem B2880077 : Blo 1919435 2880077 := bbase (se 3 (by rfl) ⟨540014, by rfl⟩ : syracuseStep 2880077 = 1080029) (by norm_num)
theorem B1920051 : Blo 1919435 1920051 := bstep (se 1 (by rfl) ⟨1440038, by rfl⟩ : syracuseStep 1920051 = 2880077) B2880077
theorem B4320125 : Blo 1919435 4320125 := bbase (se 3 (by rfl) ⟨810023, by rfl⟩ : syracuseStep 4320125 = 1620047) (by norm_num)
theorem B2880083 : Blo 1919435 2880083 := bstep (se 1 (by rfl) ⟨2160062, by rfl⟩ : syracuseStep 2880083 = 4320125) B4320125
theorem B1920055 : Blo 1919435 1920055 := bstep (se 1 (by rfl) ⟨1440041, by rfl⟩ : syracuseStep 1920055 = 2880083) B2880083
theorem B3240101 : Blo 1919435 3240101 := bbase (se 4 (by rfl) ⟨303759, by rfl⟩ : syracuseStep 3240101 = 607519) (by norm_num)
theorem B2160067 : Blo 1919435 2160067 := bstep (se 1 (by rfl) ⟨1620050, by rfl⟩ : syracuseStep 2160067 = 3240101) B3240101
theorem B2880089 : Blo 1919435 2880089 := bstep (se 2 (by rfl) ⟨1080033, by rfl⟩ : syracuseStep 2880089 = 2160067) B2160067
theorem B1920059 : Blo 1919435 1920059 := bstep (se 1 (by rfl) ⟨1440044, by rfl⟩ : syracuseStep 1920059 = 2880089) B2880089
theorem B2050381 : Blo 1919435 2050381 := bbase (se 3 (by rfl) ⟨384446, by rfl⟩ : syracuseStep 2050381 = 768893) (by norm_num)
theorem B2733841 : Blo 1919435 2733841 := bstep (se 2 (by rfl) ⟨1025190, by rfl⟩ : syracuseStep 2733841 = 2050381) B2050381
theorem B14580485 : Blo 1919435 14580485 := bstep (se 4 (by rfl) ⟨1366920, by rfl⟩ : syracuseStep 14580485 = 2733841) B2733841
theorem B9720323 : Blo 1919435 9720323 := bstep (se 1 (by rfl) ⟨7290242, by rfl⟩ : syracuseStep 9720323 = 14580485) B14580485
theorem B6480215 : Blo 1919435 6480215 := bstep (se 1 (by rfl) ⟨4860161, by rfl⟩ : syracuseStep 6480215 = 9720323) B9720323
theorem B4320143 : Blo 1919435 4320143 := bstep (se 1 (by rfl) ⟨3240107, by rfl⟩ : syracuseStep 4320143 = 6480215) B6480215
theorem B2880095 : Blo 1919435 2880095 := bstep (se 1 (by rfl) ⟨2160071, by rfl⟩ : syracuseStep 2880095 = 4320143) B4320143
theorem B1920063 : Blo 1919435 1920063 := bstep (se 1 (by rfl) ⟨1440047, by rfl⟩ : syracuseStep 1920063 = 2880095) B2880095
theorem B2880101 : Blo 1919435 2880101 := bbase (se 4 (by rfl) ⟨270009, by rfl⟩ : syracuseStep 2880101 = 540019) (by norm_num)
theorem B1920067 : Blo 1919435 1920067 := bstep (se 1 (by rfl) ⟨1440050, by rfl⟩ : syracuseStep 1920067 = 2880101) B2880101
theorem B2733853 : Blo 1919435 2733853 := bbase (se 3 (by rfl) ⟨512597, by rfl⟩ : syracuseStep 2733853 = 1025195) (by norm_num)
theorem B3645137 : Blo 1919435 3645137 := bstep (se 2 (by rfl) ⟨1366926, by rfl⟩ : syracuseStep 3645137 = 2733853) B2733853
theorem B2430091 : Blo 1919435 2430091 := bstep (se 1 (by rfl) ⟨1822568, by rfl⟩ : syracuseStep 2430091 = 3645137) B3645137
theorem B3240121 : Blo 1919435 3240121 := bstep (se 2 (by rfl) ⟨1215045, by rfl⟩ : syracuseStep 3240121 = 2430091) B2430091
theorem B4320161 : Blo 1919435 4320161 := bstep (se 2 (by rfl) ⟨1620060, by rfl⟩ : syracuseStep 4320161 = 3240121) B3240121
theorem B2880107 : Blo 1919435 2880107 := bstep (se 1 (by rfl) ⟨2160080, by rfl⟩ : syracuseStep 2880107 = 4320161) B4320161
theorem B1920071 : Blo 1919435 1920071 := bstep (se 1 (by rfl) ⟨1440053, by rfl⟩ : syracuseStep 1920071 = 2880107) B2880107
theorem B2160085 : Blo 1919435 2160085 := bbase (se 7 (by rfl) ⟨25313, by rfl⟩ : syracuseStep 2160085 = 50627) (by norm_num)
theorem B2880113 : Blo 1919435 2880113 := bstep (se 2 (by rfl) ⟨1080042, by rfl⟩ : syracuseStep 2880113 = 2160085) B2160085
theorem B1920075 : Blo 1919435 1920075 := bstep (se 1 (by rfl) ⟨1440056, by rfl⟩ : syracuseStep 1920075 = 2880113) B2880113
theorem B2430101 : Blo 1919435 2430101 := bbase (se 6 (by rfl) ⟨56955, by rfl⟩ : syracuseStep 2430101 = 113911) (by norm_num)
theorem B6480269 : Blo 1919435 6480269 := bstep (se 3 (by rfl) ⟨1215050, by rfl⟩ : syracuseStep 6480269 = 2430101) B2430101
theorem B4320179 : Blo 1919435 4320179 := bstep (se 1 (by rfl) ⟨3240134, by rfl⟩ : syracuseStep 4320179 = 6480269) B6480269
theorem B2880119 : Blo 1919435 2880119 := bstep (se 1 (by rfl) ⟨2160089, by rfl⟩ : syracuseStep 2880119 = 4320179) B4320179
theorem B1920079 : Blo 1919435 1920079 := bstep (se 1 (by rfl) ⟨1440059, by rfl⟩ : syracuseStep 1920079 = 2880119) B2880119
theorem B2880125 : Blo 1919435 2880125 := bbase (se 3 (by rfl) ⟨540023, by rfl⟩ : syracuseStep 2880125 = 1080047) (by norm_num)
theorem B1920083 : Blo 1919435 1920083 := bstep (se 1 (by rfl) ⟨1440062, by rfl⟩ : syracuseStep 1920083 = 2880125) B2880125
theorem B4320197 : Blo 1919435 4320197 := bbase (se 4 (by rfl) ⟨405018, by rfl⟩ : syracuseStep 4320197 = 810037) (by norm_num)
theorem B2880131 : Blo 1919435 2880131 := bstep (se 1 (by rfl) ⟨2160098, by rfl⟩ : syracuseStep 2880131 = 4320197) B4320197
theorem B1920087 : Blo 1919435 1920087 := bstep (se 1 (by rfl) ⟨1440065, by rfl⟩ : syracuseStep 1920087 = 2880131) B2880131
theorem B2306713 : Blo 1919435 2306713 := bbase (se 2 (by rfl) ⟨865017, by rfl⟩ : syracuseStep 2306713 = 1730035) (by norm_num)
theorem B3075617 : Blo 1919435 3075617 := bstep (se 2 (by rfl) ⟨1153356, by rfl⟩ : syracuseStep 3075617 = 2306713) B2306713
theorem B8201645 : Blo 1919435 8201645 := bstep (se 3 (by rfl) ⟨1537808, by rfl⟩ : syracuseStep 8201645 = 3075617) B3075617
theorem B5467763 : Blo 1919435 5467763 := bstep (se 1 (by rfl) ⟨4100822, by rfl⟩ : syracuseStep 5467763 = 8201645) B8201645
theorem B3645175 : Blo 1919435 3645175 := bstep (se 1 (by rfl) ⟨2733881, by rfl⟩ : syracuseStep 3645175 = 5467763) B5467763
theorem B4860233 : Blo 1919435 4860233 := bstep (se 2 (by rfl) ⟨1822587, by rfl⟩ : syracuseStep 4860233 = 3645175) B3645175
theorem B3240155 : Blo 1919435 3240155 := bstep (se 1 (by rfl) ⟨2430116, by rfl⟩ : syracuseStep 3240155 = 4860233) B4860233
theorem B2160103 : Blo 1919435 2160103 := bstep (se 1 (by rfl) ⟨1620077, by rfl⟩ : syracuseStep 2160103 = 3240155) B3240155
theorem B2880137 : Blo 1919435 2880137 := bstep (se 2 (by rfl) ⟨1080051, by rfl⟩ : syracuseStep 2880137 = 2160103) B2160103
theorem B1920091 : Blo 1919435 1920091 := bstep (se 1 (by rfl) ⟨1440068, by rfl⟩ : syracuseStep 1920091 = 2880137) B2880137
theorem B9720485 : Blo 1919435 9720485 := bbase (se 4 (by rfl) ⟨911295, by rfl⟩ : syracuseStep 9720485 = 1822591) (by norm_num)
theorem B6480323 : Blo 1919435 6480323 := bstep (se 1 (by rfl) ⟨4860242, by rfl⟩ : syracuseStep 6480323 = 9720485) B9720485
theorem B4320215 : Blo 1919435 4320215 := bstep (se 1 (by rfl) ⟨3240161, by rfl⟩ : syracuseStep 4320215 = 6480323) B6480323
theorem B2880143 : Blo 1919435 2880143 := bstep (se 1 (by rfl) ⟨2160107, by rfl⟩ : syracuseStep 2880143 = 4320215) B4320215
theorem B1920095 : Blo 1919435 1920095 := bstep (se 1 (by rfl) ⟨1440071, by rfl⟩ : syracuseStep 1920095 = 2880143) B2880143
theorem B2880149 : Blo 1919435 2880149 := bbase (se 6 (by rfl) ⟨67503, by rfl⟩ : syracuseStep 2880149 = 135007) (by norm_num)
theorem B1920099 : Blo 1919435 1920099 := bstep (se 1 (by rfl) ⟨1440074, by rfl⟩ : syracuseStep 1920099 = 2880149) B2880149
theorem B16627189 : Blo 1919435 16627189 := bbase (se 5 (by rfl) ⟨779399, by rfl⟩ : syracuseStep 16627189 = 1558799) (by norm_num)
theorem B22169585 : Blo 1919435 22169585 := bstep (se 2 (by rfl) ⟨8313594, by rfl⟩ : syracuseStep 22169585 = 16627189) B16627189
theorem B59118893 : Blo 1919435 59118893 := bstep (se 3 (by rfl) ⟨11084792, by rfl⟩ : syracuseStep 59118893 = 22169585) B22169585
theorem B39412595 : Blo 1919435 39412595 := bstep (se 1 (by rfl) ⟨29559446, by rfl⟩ : syracuseStep 39412595 = 59118893) B59118893
theorem B26275063 : Blo 1919435 26275063 := bstep (se 1 (by rfl) ⟨19706297, by rfl⟩ : syracuseStep 26275063 = 39412595) B39412595
theorem B35033417 : Blo 1919435 35033417 := bstep (se 2 (by rfl) ⟨13137531, by rfl⟩ : syracuseStep 35033417 = 26275063) B26275063
theorem B23355611 : Blo 1919435 23355611 := bstep (se 1 (by rfl) ⟨17516708, by rfl⟩ : syracuseStep 23355611 = 35033417) B35033417
theorem B15570407 : Blo 1919435 15570407 := bstep (se 1 (by rfl) ⟨11677805, by rfl⟩ : syracuseStep 15570407 = 23355611) B23355611
theorem B41521085 : Blo 1919435 41521085 := bstep (se 3 (by rfl) ⟨7785203, by rfl⟩ : syracuseStep 41521085 = 15570407) B15570407
theorem B27680723 : Blo 1919435 27680723 := bstep (se 1 (by rfl) ⟨20760542, by rfl⟩ : syracuseStep 27680723 = 41521085) B41521085
theorem B18453815 : Blo 1919435 18453815 := bstep (se 1 (by rfl) ⟨13840361, by rfl⟩ : syracuseStep 18453815 = 27680723) B27680723
theorem B12302543 : Blo 1919435 12302543 := bstep (se 1 (by rfl) ⟨9226907, by rfl⟩ : syracuseStep 12302543 = 18453815) B18453815
theorem B8201695 : Blo 1919435 8201695 := bstep (se 1 (by rfl) ⟨6151271, by rfl⟩ : syracuseStep 8201695 = 12302543) B12302543
theorem B10935593 : Blo 1919435 10935593 := bstep (se 2 (by rfl) ⟨4100847, by rfl⟩ : syracuseStep 10935593 = 8201695) B8201695
theorem B7290395 : Blo 1919435 7290395 := bstep (se 1 (by rfl) ⟨5467796, by rfl⟩ : syracuseStep 7290395 = 10935593) B10935593
theorem B4860263 : Blo 1919435 4860263 := bstep (se 1 (by rfl) ⟨3645197, by rfl⟩ : syracuseStep 4860263 = 7290395) B7290395
theorem B3240175 : Blo 1919435 3240175 := bstep (se 1 (by rfl) ⟨2430131, by rfl⟩ : syracuseStep 3240175 = 4860263) B4860263
theorem B4320233 : Blo 1919435 4320233 := bstep (se 2 (by rfl) ⟨1620087, by rfl⟩ : syracuseStep 4320233 = 3240175) B3240175
theorem B2880155 : Blo 1919435 2880155 := bstep (se 1 (by rfl) ⟨2160116, by rfl⟩ : syracuseStep 2880155 = 4320233) B4320233
theorem B1920103 : Blo 1919435 1920103 := bstep (se 1 (by rfl) ⟨1440077, by rfl⟩ : syracuseStep 1920103 = 2880155) B2880155
theorem B2160121 : Blo 1919435 2160121 := bbase (se 2 (by rfl) ⟨810045, by rfl⟩ : syracuseStep 2160121 = 1620091) (by norm_num)
theorem B2880161 : Blo 1919435 2880161 := bstep (se 2 (by rfl) ⟨1080060, by rfl⟩ : syracuseStep 2880161 = 2160121) B2160121
theorem B1920107 : Blo 1919435 1920107 := bstep (se 1 (by rfl) ⟨1440080, by rfl⟩ : syracuseStep 1920107 = 2880161) B2880161
theorem B4379197 : Blo 1919435 4379197 := bbase (se 3 (by rfl) ⟨821099, by rfl⟩ : syracuseStep 4379197 = 1642199) (by norm_num)
theorem B5838929 : Blo 1919435 5838929 := bstep (se 2 (by rfl) ⟨2189598, by rfl⟩ : syracuseStep 5838929 = 4379197) B4379197
theorem B3892619 : Blo 1919435 3892619 := bstep (se 1 (by rfl) ⟨2919464, by rfl⟩ : syracuseStep 3892619 = 5838929) B5838929
theorem B2595079 : Blo 1919435 2595079 := bstep (se 1 (by rfl) ⟨1946309, by rfl⟩ : syracuseStep 2595079 = 3892619) B3892619
theorem B3460105 : Blo 1919435 3460105 := bstep (se 2 (by rfl) ⟨1297539, by rfl⟩ : syracuseStep 3460105 = 2595079) B2595079
theorem B4613473 : Blo 1919435 4613473 := bstep (se 2 (by rfl) ⟨1730052, by rfl⟩ : syracuseStep 4613473 = 3460105) B3460105
theorem B6151297 : Blo 1919435 6151297 := bstep (se 2 (by rfl) ⟨2306736, by rfl⟩ : syracuseStep 6151297 = 4613473) B4613473
theorem B8201729 : Blo 1919435 8201729 := bstep (se 2 (by rfl) ⟨3075648, by rfl⟩ : syracuseStep 8201729 = 6151297) B6151297
theorem B5467819 : Blo 1919435 5467819 := bstep (se 1 (by rfl) ⟨4100864, by rfl⟩ : syracuseStep 5467819 = 8201729) B8201729
theorem B7290425 : Blo 1919435 7290425 := bstep (se 2 (by rfl) ⟨2733909, by rfl⟩ : syracuseStep 7290425 = 5467819) B5467819
theorem B4860283 : Blo 1919435 4860283 := bstep (se 1 (by rfl) ⟨3645212, by rfl⟩ : syracuseStep 4860283 = 7290425) B7290425
theorem B6480377 : Blo 1919435 6480377 := bstep (se 2 (by rfl) ⟨2430141, by rfl⟩ : syracuseStep 6480377 = 4860283) B4860283
theorem B4320251 : Blo 1919435 4320251 := bstep (se 1 (by rfl) ⟨3240188, by rfl⟩ : syracuseStep 4320251 = 6480377) B6480377
theorem B2880167 : Blo 1919435 2880167 := bstep (se 1 (by rfl) ⟨2160125, by rfl⟩ : syracuseStep 2880167 = 4320251) B4320251
theorem B1920111 : Blo 1919435 1920111 := bstep (se 1 (by rfl) ⟨1440083, by rfl⟩ : syracuseStep 1920111 = 2880167) B2880167
theorem B2880173 : Blo 1919435 2880173 := bbase (se 3 (by rfl) ⟨540032, by rfl⟩ : syracuseStep 2880173 = 1080065) (by norm_num)
theorem B1920115 : Blo 1919435 1920115 := bstep (se 1 (by rfl) ⟨1440086, by rfl⟩ : syracuseStep 1920115 = 2880173) B2880173
theorem B4320269 : Blo 1919435 4320269 := bbase (se 3 (by rfl) ⟨810050, by rfl⟩ : syracuseStep 4320269 = 1620101) (by norm_num)
theorem B2880179 : Blo 1919435 2880179 := bstep (se 1 (by rfl) ⟨2160134, by rfl⟩ : syracuseStep 2880179 = 4320269) B4320269
theorem B1920119 : Blo 1919435 1920119 := bstep (se 1 (by rfl) ⟨1440089, by rfl⟩ : syracuseStep 1920119 = 2880179) B2880179
theorem B2430157 : Blo 1919435 2430157 := bbase (se 3 (by rfl) ⟨455654, by rfl⟩ : syracuseStep 2430157 = 911309) (by norm_num)
theorem B3240209 : Blo 1919435 3240209 := bstep (se 2 (by rfl) ⟨1215078, by rfl⟩ : syracuseStep 3240209 = 2430157) B2430157
theorem B2160139 : Blo 1919435 2160139 := bstep (se 1 (by rfl) ⟨1620104, by rfl⟩ : syracuseStep 2160139 = 3240209) B3240209
theorem B2880185 : Blo 1919435 2880185 := bstep (se 2 (by rfl) ⟨1080069, by rfl⟩ : syracuseStep 2880185 = 2160139) B2160139
theorem B1920123 : Blo 1919435 1920123 := bstep (se 1 (by rfl) ⟨1440092, by rfl⟩ : syracuseStep 1920123 = 2880185) B2880185
theorem B59926229 : Blo 1919435 59926229 := bbase (se 7 (by rfl) ⟨702260, by rfl⟩ : syracuseStep 59926229 = 1404521) (by norm_num)
theorem B39950819 : Blo 1919435 39950819 := bstep (se 1 (by rfl) ⟨29963114, by rfl⟩ : syracuseStep 39950819 = 59926229) B59926229
theorem B26633879 : Blo 1919435 26633879 := bstep (se 1 (by rfl) ⟨19975409, by rfl⟩ : syracuseStep 26633879 = 39950819) B39950819
theorem B17755919 : Blo 1919435 17755919 := bstep (se 1 (by rfl) ⟨13316939, by rfl⟩ : syracuseStep 17755919 = 26633879) B26633879
theorem B11837279 : Blo 1919435 11837279 := bstep (se 1 (by rfl) ⟨8877959, by rfl⟩ : syracuseStep 11837279 = 17755919) B17755919
theorem B7891519 : Blo 1919435 7891519 := bstep (se 1 (by rfl) ⟨5918639, by rfl⟩ : syracuseStep 7891519 = 11837279) B11837279
theorem B10522025 : Blo 1919435 10522025 := bstep (se 2 (by rfl) ⟨3945759, by rfl⟩ : syracuseStep 10522025 = 7891519) B7891519
theorem B7014683 : Blo 1919435 7014683 := bstep (se 1 (by rfl) ⟨5261012, by rfl⟩ : syracuseStep 7014683 = 10522025) B10522025
theorem B4676455 : Blo 1919435 4676455 := bstep (se 1 (by rfl) ⟨3507341, by rfl⟩ : syracuseStep 4676455 = 7014683) B7014683
theorem B6235273 : Blo 1919435 6235273 := bstep (se 2 (by rfl) ⟨2338227, by rfl⟩ : syracuseStep 6235273 = 4676455) B4676455
theorem B8313697 : Blo 1919435 8313697 := bstep (se 2 (by rfl) ⟨3117636, by rfl⟩ : syracuseStep 8313697 = 6235273) B6235273
theorem B44339717 : Blo 1919435 44339717 := bstep (se 4 (by rfl) ⟨4156848, by rfl⟩ : syracuseStep 44339717 = 8313697) B8313697
theorem B29559811 : Blo 1919435 29559811 := bstep (se 1 (by rfl) ⟨22169858, by rfl⟩ : syracuseStep 29559811 = 44339717) B44339717
theorem B39413081 : Blo 1919435 39413081 := bstep (se 2 (by rfl) ⟨14779905, by rfl⟩ : syracuseStep 39413081 = 29559811) B29559811
theorem B105101549 : Blo 1919435 105101549 := bstep (se 3 (by rfl) ⟨19706540, by rfl⟩ : syracuseStep 105101549 = 39413081) B39413081
theorem B70067699 : Blo 1919435 70067699 := bstep (se 1 (by rfl) ⟨52550774, by rfl⟩ : syracuseStep 70067699 = 105101549) B105101549
theorem B46711799 : Blo 1919435 46711799 := bstep (se 1 (by rfl) ⟨35033849, by rfl⟩ : syracuseStep 46711799 = 70067699) B70067699
theorem B31141199 : Blo 1919435 31141199 := bstep (se 1 (by rfl) ⟨23355899, by rfl⟩ : syracuseStep 31141199 = 46711799) B46711799
theorem B20760799 : Blo 1919435 20760799 := bstep (se 1 (by rfl) ⟨15570599, by rfl⟩ : syracuseStep 20760799 = 31141199) B31141199
theorem B27681065 : Blo 1919435 27681065 := bstep (se 2 (by rfl) ⟨10380399, by rfl⟩ : syracuseStep 27681065 = 20760799) B20760799
theorem B18454043 : Blo 1919435 18454043 := bstep (se 1 (by rfl) ⟨13840532, by rfl⟩ : syracuseStep 18454043 = 27681065) B27681065
theorem B12302695 : Blo 1919435 12302695 := bstep (se 1 (by rfl) ⟨9227021, by rfl⟩ : syracuseStep 12302695 = 18454043) B18454043
theorem B16403593 : Blo 1919435 16403593 := bstep (se 2 (by rfl) ⟨6151347, by rfl⟩ : syracuseStep 16403593 = 12302695) B12302695
theorem B21871457 : Blo 1919435 21871457 := bstep (se 2 (by rfl) ⟨8201796, by rfl⟩ : syracuseStep 21871457 = 16403593) B16403593
theorem B14580971 : Blo 1919435 14580971 := bstep (se 1 (by rfl) ⟨10935728, by rfl⟩ : syracuseStep 14580971 = 21871457) B21871457
theorem B9720647 : Blo 1919435 9720647 := bstep (se 1 (by rfl) ⟨7290485, by rfl⟩ : syracuseStep 9720647 = 14580971) B14580971
theorem B6480431 : Blo 1919435 6480431 := bstep (se 1 (by rfl) ⟨4860323, by rfl⟩ : syracuseStep 6480431 = 9720647) B9720647
theorem B4320287 : Blo 1919435 4320287 := bstep (se 1 (by rfl) ⟨3240215, by rfl⟩ : syracuseStep 4320287 = 6480431) B6480431
theorem B2880191 : Blo 1919435 2880191 := bstep (se 1 (by rfl) ⟨2160143, by rfl⟩ : syracuseStep 2880191 = 4320287) B4320287
theorem B1920127 : Blo 1919435 1920127 := bstep (se 1 (by rfl) ⟨1440095, by rfl⟩ : syracuseStep 1920127 = 2880191) B2880191
theorem B2880197 : Blo 1919435 2880197 := bbase (se 4 (by rfl) ⟨270018, by rfl⟩ : syracuseStep 2880197 = 540037) (by norm_num)
theorem B1920131 : Blo 1919435 1920131 := bstep (se 1 (by rfl) ⟨1440098, by rfl⟩ : syracuseStep 1920131 = 2880197) B2880197
theorem B3240229 : Blo 1919435 3240229 := bbase (se 4 (by rfl) ⟨303771, by rfl⟩ : syracuseStep 3240229 = 607543) (by norm_num)
theorem B4320305 : Blo 1919435 4320305 := bstep (se 2 (by rfl) ⟨1620114, by rfl⟩ : syracuseStep 4320305 = 3240229) B3240229
theorem B2880203 : Blo 1919435 2880203 := bstep (se 1 (by rfl) ⟨2160152, by rfl⟩ : syracuseStep 2880203 = 4320305) B4320305
theorem B1920135 : Blo 1919435 1920135 := bstep (se 1 (by rfl) ⟨1440101, by rfl⟩ : syracuseStep 1920135 = 2880203) B2880203
theorem B2160157 : Blo 1919435 2160157 := bbase (se 3 (by rfl) ⟨405029, by rfl⟩ : syracuseStep 2160157 = 810059) (by norm_num)
theorem B2880209 : Blo 1919435 2880209 := bstep (se 2 (by rfl) ⟨1080078, by rfl⟩ : syracuseStep 2880209 = 2160157) B2160157
theorem B1920139 : Blo 1919435 1920139 := bstep (se 1 (by rfl) ⟨1440104, by rfl⟩ : syracuseStep 1920139 = 2880209) B2880209
theorem B6480485 : Blo 1919435 6480485 := bbase (se 4 (by rfl) ⟨607545, by rfl⟩ : syracuseStep 6480485 = 1215091) (by norm_num)
theorem B4320323 : Blo 1919435 4320323 := bstep (se 1 (by rfl) ⟨3240242, by rfl⟩ : syracuseStep 4320323 = 6480485) B6480485
theorem B2880215 : Blo 1919435 2880215 := bstep (se 1 (by rfl) ⟨2160161, by rfl⟩ : syracuseStep 2880215 = 4320323) B4320323
theorem B1920143 : Blo 1919435 1920143 := bstep (se 1 (by rfl) ⟨1440107, by rfl⟩ : syracuseStep 1920143 = 2880215) B2880215
theorem B2880221 : Blo 1919435 2880221 := bbase (se 3 (by rfl) ⟨540041, by rfl⟩ : syracuseStep 2880221 = 1080083) (by norm_num)
theorem B1920147 : Blo 1919435 1920147 := bstep (se 1 (by rfl) ⟨1440110, by rfl⟩ : syracuseStep 1920147 = 2880221) B2880221
theorem B4320341 : Blo 1919435 4320341 := bbase (se 8 (by rfl) ⟨25314, by rfl⟩ : syracuseStep 4320341 = 50629) (by norm_num)
theorem B2880227 : Blo 1919435 2880227 := bstep (se 1 (by rfl) ⟨2160170, by rfl⟩ : syracuseStep 2880227 = 4320341) B4320341
theorem B1920151 : Blo 1919435 1920151 := bstep (se 1 (by rfl) ⟨1440113, by rfl⟩ : syracuseStep 1920151 = 2880227) B2880227
theorem B20761109 : Blo 1919435 20761109 := bbase (se 6 (by rfl) ⟨486588, by rfl⟩ : syracuseStep 20761109 = 973177) (by norm_num)
theorem B13840739 : Blo 1919435 13840739 := bstep (se 1 (by rfl) ⟨10380554, by rfl⟩ : syracuseStep 13840739 = 20761109) B20761109
theorem B9227159 : Blo 1919435 9227159 := bstep (se 1 (by rfl) ⟨6920369, by rfl⟩ : syracuseStep 9227159 = 13840739) B13840739
theorem B6151439 : Blo 1919435 6151439 := bstep (se 1 (by rfl) ⟨4613579, by rfl⟩ : syracuseStep 6151439 = 9227159) B9227159
theorem B4100959 : Blo 1919435 4100959 := bstep (se 1 (by rfl) ⟨3075719, by rfl⟩ : syracuseStep 4100959 = 6151439) B6151439
theorem B5467945 : Blo 1919435 5467945 := bstep (se 2 (by rfl) ⟨2050479, by rfl⟩ : syracuseStep 5467945 = 4100959) B4100959
theorem B7290593 : Blo 1919435 7290593 := bstep (se 2 (by rfl) ⟨2733972, by rfl⟩ : syracuseStep 7290593 = 5467945) B5467945
theorem B4860395 : Blo 1919435 4860395 := bstep (se 1 (by rfl) ⟨3645296, by rfl⟩ : syracuseStep 4860395 = 7290593) B7290593
theorem B3240263 : Blo 1919435 3240263 := bstep (se 1 (by rfl) ⟨2430197, by rfl⟩ : syracuseStep 3240263 = 4860395) B4860395
theorem B2160175 : Blo 1919435 2160175 := bstep (se 1 (by rfl) ⟨1620131, by rfl⟩ : syracuseStep 2160175 = 3240263) B3240263
theorem B2880233 : Blo 1919435 2880233 := bstep (se 2 (by rfl) ⟨1080087, by rfl⟩ : syracuseStep 2880233 = 2160175) B2160175
theorem B1920155 : Blo 1919435 1920155 := bstep (se 1 (by rfl) ⟨1440116, by rfl⟩ : syracuseStep 1920155 = 2880233) B2880233
theorem B18706133 : Blo 1919435 18706133 := bbase (se 7 (by rfl) ⟨219212, by rfl⟩ : syracuseStep 18706133 = 438425) (by norm_num)
theorem B12470755 : Blo 1919435 12470755 := bstep (se 1 (by rfl) ⟨9353066, by rfl⟩ : syracuseStep 12470755 = 18706133) B18706133
theorem B16627673 : Blo 1919435 16627673 := bstep (se 2 (by rfl) ⟨6235377, by rfl⟩ : syracuseStep 16627673 = 12470755) B12470755
theorem B11085115 : Blo 1919435 11085115 := bstep (se 1 (by rfl) ⟨8313836, by rfl⟩ : syracuseStep 11085115 = 16627673) B16627673
theorem B14780153 : Blo 1919435 14780153 := bstep (se 2 (by rfl) ⟨5542557, by rfl⟩ : syracuseStep 14780153 = 11085115) B11085115
theorem B9853435 : Blo 1919435 9853435 := bstep (se 1 (by rfl) ⟨7390076, by rfl⟩ : syracuseStep 9853435 = 14780153) B14780153
theorem B13137913 : Blo 1919435 13137913 := bstep (se 2 (by rfl) ⟨4926717, by rfl⟩ : syracuseStep 13137913 = 9853435) B9853435
theorem B17517217 : Blo 1919435 17517217 := bstep (se 2 (by rfl) ⟨6568956, by rfl⟩ : syracuseStep 17517217 = 13137913) B13137913
theorem B23356289 : Blo 1919435 23356289 := bstep (se 2 (by rfl) ⟨8758608, by rfl⟩ : syracuseStep 23356289 = 17517217) B17517217
theorem B62283437 : Blo 1919435 62283437 := bstep (se 3 (by rfl) ⟨11678144, by rfl⟩ : syracuseStep 62283437 = 23356289) B23356289
theorem B41522291 : Blo 1919435 41522291 := bstep (se 1 (by rfl) ⟨31141718, by rfl⟩ : syracuseStep 41522291 = 62283437) B62283437
theorem B27681527 : Blo 1919435 27681527 := bstep (se 1 (by rfl) ⟨20761145, by rfl⟩ : syracuseStep 27681527 = 41522291) B41522291
theorem B18454351 : Blo 1919435 18454351 := bstep (se 1 (by rfl) ⟨13840763, by rfl⟩ : syracuseStep 18454351 = 27681527) B27681527
theorem B24605801 : Blo 1919435 24605801 := bstep (se 2 (by rfl) ⟨9227175, by rfl⟩ : syracuseStep 24605801 = 18454351) B18454351
theorem B16403867 : Blo 1919435 16403867 := bstep (se 1 (by rfl) ⟨12302900, by rfl⟩ : syracuseStep 16403867 = 24605801) B24605801
theorem B10935911 : Blo 1919435 10935911 := bstep (se 1 (by rfl) ⟨8201933, by rfl⟩ : syracuseStep 10935911 = 16403867) B16403867
theorem B7290607 : Blo 1919435 7290607 := bstep (se 1 (by rfl) ⟨5467955, by rfl⟩ : syracuseStep 7290607 = 10935911) B10935911
theorem B9720809 : Blo 1919435 9720809 := bstep (se 2 (by rfl) ⟨3645303, by rfl⟩ : syracuseStep 9720809 = 7290607) B7290607
theorem B6480539 : Blo 1919435 6480539 := bstep (se 1 (by rfl) ⟨4860404, by rfl⟩ : syracuseStep 6480539 = 9720809) B9720809
theorem B4320359 : Blo 1919435 4320359 := bstep (se 1 (by rfl) ⟨3240269, by rfl⟩ : syracuseStep 4320359 = 6480539) B6480539
theorem B2880239 : Blo 1919435 2880239 := bstep (se 1 (by rfl) ⟨2160179, by rfl⟩ : syracuseStep 2880239 = 4320359) B4320359
theorem B1920159 : Blo 1919435 1920159 := bstep (se 1 (by rfl) ⟨1440119, by rfl⟩ : syracuseStep 1920159 = 2880239) B2880239
theorem B2880245 : Blo 1919435 2880245 := bbase (se 5 (by rfl) ⟨135011, by rfl⟩ : syracuseStep 2880245 = 270023) (by norm_num)
theorem B1920163 : Blo 1919435 1920163 := bstep (se 1 (by rfl) ⟨1440122, by rfl⟩ : syracuseStep 1920163 = 2880245) B2880245
theorem B6151477 : Blo 1919435 6151477 := bbase (se 5 (by rfl) ⟨288350, by rfl⟩ : syracuseStep 6151477 = 576701) (by norm_num)
theorem B8201969 : Blo 1919435 8201969 := bstep (se 2 (by rfl) ⟨3075738, by rfl⟩ : syracuseStep 8201969 = 6151477) B6151477
theorem B5467979 : Blo 1919435 5467979 := bstep (se 1 (by rfl) ⟨4100984, by rfl⟩ : syracuseStep 5467979 = 8201969) B8201969
theorem B3645319 : Blo 1919435 3645319 := bstep (se 1 (by rfl) ⟨2733989, by rfl⟩ : syracuseStep 3645319 = 5467979) B5467979
theorem B4860425 : Blo 1919435 4860425 := bstep (se 2 (by rfl) ⟨1822659, by rfl⟩ : syracuseStep 4860425 = 3645319) B3645319
theorem B3240283 : Blo 1919435 3240283 := bstep (se 1 (by rfl) ⟨2430212, by rfl⟩ : syracuseStep 3240283 = 4860425) B4860425
theorem B4320377 : Blo 1919435 4320377 := bstep (se 2 (by rfl) ⟨1620141, by rfl⟩ : syracuseStep 4320377 = 3240283) B3240283
theorem B2880251 : Blo 1919435 2880251 := bstep (se 1 (by rfl) ⟨2160188, by rfl⟩ : syracuseStep 2880251 = 4320377) B4320377
theorem B1920167 : Blo 1919435 1920167 := bstep (se 1 (by rfl) ⟨1440125, by rfl⟩ : syracuseStep 1920167 = 2880251) B2880251
theorem B2160193 : Blo 1919435 2160193 := bbase (se 2 (by rfl) ⟨810072, by rfl⟩ : syracuseStep 2160193 = 1620145) (by norm_num)
theorem B2880257 : Blo 1919435 2880257 := bstep (se 2 (by rfl) ⟨1080096, by rfl⟩ : syracuseStep 2880257 = 2160193) B2160193
theorem B1920171 : Blo 1919435 1920171 := bstep (se 1 (by rfl) ⟨1440128, by rfl⟩ : syracuseStep 1920171 = 2880257) B2880257
theorem B4860445 : Blo 1919435 4860445 := bbase (se 3 (by rfl) ⟨911333, by rfl⟩ : syracuseStep 4860445 = 1822667) (by norm_num)
theorem B6480593 : Blo 1919435 6480593 := bstep (se 2 (by rfl) ⟨2430222, by rfl⟩ : syracuseStep 6480593 = 4860445) B4860445
theorem B4320395 : Blo 1919435 4320395 := bstep (se 1 (by rfl) ⟨3240296, by rfl⟩ : syracuseStep 4320395 = 6480593) B6480593
theorem B2880263 : Blo 1919435 2880263 := bstep (se 1 (by rfl) ⟨2160197, by rfl⟩ : syracuseStep 2880263 = 4320395) B4320395
theorem B1920175 : Blo 1919435 1920175 := bstep (se 1 (by rfl) ⟨1440131, by rfl⟩ : syracuseStep 1920175 = 2880263) B2880263
theorem B2880269 : Blo 1919435 2880269 := bbase (se 3 (by rfl) ⟨540050, by rfl⟩ : syracuseStep 2880269 = 1080101) (by norm_num)
theorem B1920179 : Blo 1919435 1920179 := bstep (se 1 (by rfl) ⟨1440134, by rfl⟩ : syracuseStep 1920179 = 2880269) B2880269
theorem B4320413 : Blo 1919435 4320413 := bbase (se 3 (by rfl) ⟨810077, by rfl⟩ : syracuseStep 4320413 = 1620155) (by norm_num)
theorem B2880275 : Blo 1919435 2880275 := bstep (se 1 (by rfl) ⟨2160206, by rfl⟩ : syracuseStep 2880275 = 4320413) B4320413
theorem B1920183 : Blo 1919435 1920183 := bstep (se 1 (by rfl) ⟨1440137, by rfl⟩ : syracuseStep 1920183 = 2880275) B2880275
theorem B3240317 : Blo 1919435 3240317 := bbase (se 3 (by rfl) ⟨607559, by rfl⟩ : syracuseStep 3240317 = 1215119) (by norm_num)
theorem B2160211 : Blo 1919435 2160211 := bstep (se 1 (by rfl) ⟨1620158, by rfl⟩ : syracuseStep 2160211 = 3240317) B3240317
theorem B2880281 : Blo 1919435 2880281 := bstep (se 2 (by rfl) ⟨1080105, by rfl⟩ : syracuseStep 2880281 = 2160211) B2160211
theorem B1920187 : Blo 1919435 1920187 := bstep (se 1 (by rfl) ⟨1440140, by rfl⟩ : syracuseStep 1920187 = 2880281) B2880281
theorem B3892781 : Blo 1919435 3892781 := bbase (se 3 (by rfl) ⟨729896, by rfl⟩ : syracuseStep 3892781 = 1459793) (by norm_num)
theorem B2595187 : Blo 1919435 2595187 := bstep (se 1 (by rfl) ⟨1946390, by rfl⟩ : syracuseStep 2595187 = 3892781) B3892781
theorem B3460249 : Blo 1919435 3460249 := bstep (se 2 (by rfl) ⟨1297593, by rfl⟩ : syracuseStep 3460249 = 2595187) B2595187
theorem B4613665 : Blo 1919435 4613665 := bstep (se 2 (by rfl) ⟨1730124, by rfl⟩ : syracuseStep 4613665 = 3460249) B3460249
theorem B6151553 : Blo 1919435 6151553 := bstep (se 2 (by rfl) ⟨2306832, by rfl⟩ : syracuseStep 6151553 = 4613665) B4613665
theorem B4101035 : Blo 1919435 4101035 := bstep (se 1 (by rfl) ⟨3075776, by rfl⟩ : syracuseStep 4101035 = 6151553) B6151553
theorem B10936093 : Blo 1919435 10936093 := bstep (se 3 (by rfl) ⟨2050517, by rfl⟩ : syracuseStep 10936093 = 4101035) B4101035
theorem B14581457 : Blo 1919435 14581457 := bstep (se 2 (by rfl) ⟨5468046, by rfl⟩ : syracuseStep 14581457 = 10936093) B10936093
theorem B9720971 : Blo 1919435 9720971 := bstep (se 1 (by rfl) ⟨7290728, by rfl⟩ : syracuseStep 9720971 = 14581457) B14581457
theorem B6480647 : Blo 1919435 6480647 := bstep (se 1 (by rfl) ⟨4860485, by rfl⟩ : syracuseStep 6480647 = 9720971) B9720971
theorem B4320431 : Blo 1919435 4320431 := bstep (se 1 (by rfl) ⟨3240323, by rfl⟩ : syracuseStep 4320431 = 6480647) B6480647
theorem B2880287 : Blo 1919435 2880287 := bstep (se 1 (by rfl) ⟨2160215, by rfl⟩ : syracuseStep 2880287 = 4320431) B4320431
theorem B1920191 : Blo 1919435 1920191 := bstep (se 1 (by rfl) ⟨1440143, by rfl⟩ : syracuseStep 1920191 = 2880287) B2880287
theorem B2880293 : Blo 1919435 2880293 := bbase (se 4 (by rfl) ⟨270027, by rfl⟩ : syracuseStep 2880293 = 540055) (by norm_num)
theorem B1920195 : Blo 1919435 1920195 := bstep (se 1 (by rfl) ⟨1440146, by rfl⟩ : syracuseStep 1920195 = 2880293) B2880293
theorem B2430253 : Blo 1919435 2430253 := bbase (se 3 (by rfl) ⟨455672, by rfl⟩ : syracuseStep 2430253 = 911345) (by norm_num)
theorem B3240337 : Blo 1919435 3240337 := bstep (se 2 (by rfl) ⟨1215126, by rfl⟩ : syracuseStep 3240337 = 2430253) B2430253
theorem B4320449 : Blo 1919435 4320449 := bstep (se 2 (by rfl) ⟨1620168, by rfl⟩ : syracuseStep 4320449 = 3240337) B3240337
theorem B2880299 : Blo 1919435 2880299 := bstep (se 1 (by rfl) ⟨2160224, by rfl⟩ : syracuseStep 2880299 = 4320449) B4320449
theorem B1920199 : Blo 1919435 1920199 := bstep (se 1 (by rfl) ⟨1440149, by rfl⟩ : syracuseStep 1920199 = 2880299) B2880299
theorem B2160229 : Blo 1919435 2160229 := bbase (se 4 (by rfl) ⟨202521, by rfl⟩ : syracuseStep 2160229 = 405043) (by norm_num)
theorem B2880305 : Blo 1919435 2880305 := bstep (se 2 (by rfl) ⟨1080114, by rfl⟩ : syracuseStep 2880305 = 2160229) B2160229
theorem B1920203 : Blo 1919435 1920203 := bstep (se 1 (by rfl) ⟨1440152, by rfl⟩ : syracuseStep 1920203 = 2880305) B2880305
theorem B4926845 : Blo 1919435 4926845 := bbase (se 3 (by rfl) ⟨923783, by rfl⟩ : syracuseStep 4926845 = 1847567) (by norm_num)
theorem B3284563 : Blo 1919435 3284563 := bstep (se 1 (by rfl) ⟨2463422, by rfl⟩ : syracuseStep 3284563 = 4926845) B4926845
theorem B4379417 : Blo 1919435 4379417 := bstep (se 2 (by rfl) ⟨1642281, by rfl⟩ : syracuseStep 4379417 = 3284563) B3284563
theorem B2919611 : Blo 1919435 2919611 := bstep (se 1 (by rfl) ⟨2189708, by rfl⟩ : syracuseStep 2919611 = 4379417) B4379417
theorem B7785629 : Blo 1919435 7785629 := bstep (se 3 (by rfl) ⟨1459805, by rfl⟩ : syracuseStep 7785629 = 2919611) B2919611
theorem B5190419 : Blo 1919435 5190419 := bstep (se 1 (by rfl) ⟨3892814, by rfl⟩ : syracuseStep 5190419 = 7785629) B7785629
theorem B3460279 : Blo 1919435 3460279 := bstep (se 1 (by rfl) ⟨2595209, by rfl⟩ : syracuseStep 3460279 = 5190419) B5190419
theorem B4613705 : Blo 1919435 4613705 := bstep (se 2 (by rfl) ⟨1730139, by rfl⟩ : syracuseStep 4613705 = 3460279) B3460279
theorem B3075803 : Blo 1919435 3075803 := bstep (se 1 (by rfl) ⟨2306852, by rfl⟩ : syracuseStep 3075803 = 4613705) B4613705
theorem B2050535 : Blo 1919435 2050535 := bstep (se 1 (by rfl) ⟨1537901, by rfl⟩ : syracuseStep 2050535 = 3075803) B3075803
theorem B5468093 : Blo 1919435 5468093 := bstep (se 3 (by rfl) ⟨1025267, by rfl⟩ : syracuseStep 5468093 = 2050535) B2050535
theorem B3645395 : Blo 1919435 3645395 := bstep (se 1 (by rfl) ⟨2734046, by rfl⟩ : syracuseStep 3645395 = 5468093) B5468093
theorem B2430263 : Blo 1919435 2430263 := bstep (se 1 (by rfl) ⟨1822697, by rfl⟩ : syracuseStep 2430263 = 3645395) B3645395
theorem B6480701 : Blo 1919435 6480701 := bstep (se 3 (by rfl) ⟨1215131, by rfl⟩ : syracuseStep 6480701 = 2430263) B2430263
theorem B4320467 : Blo 1919435 4320467 := bstep (se 1 (by rfl) ⟨3240350, by rfl⟩ : syracuseStep 4320467 = 6480701) B6480701
theorem B2880311 : Blo 1919435 2880311 := bstep (se 1 (by rfl) ⟨2160233, by rfl⟩ : syracuseStep 2880311 = 4320467) B4320467
theorem B1920207 : Blo 1919435 1920207 := bstep (se 1 (by rfl) ⟨1440155, by rfl⟩ : syracuseStep 1920207 = 2880311) B2880311
theorem B2880317 : Blo 1919435 2880317 := bbase (se 3 (by rfl) ⟨540059, by rfl⟩ : syracuseStep 2880317 = 1080119) (by norm_num)
theorem B1920211 : Blo 1919435 1920211 := bstep (se 1 (by rfl) ⟨1440158, by rfl⟩ : syracuseStep 1920211 = 2880317) B2880317
theorem B4320485 : Blo 1919435 4320485 := bbase (se 4 (by rfl) ⟨405045, by rfl⟩ : syracuseStep 4320485 = 810091) (by norm_num)
theorem B2880323 : Blo 1919435 2880323 := bstep (se 1 (by rfl) ⟨2160242, by rfl⟩ : syracuseStep 2880323 = 4320485) B4320485
theorem B1920215 : Blo 1919435 1920215 := bstep (se 1 (by rfl) ⟨1440161, by rfl⟩ : syracuseStep 1920215 = 2880323) B2880323
theorem B4860557 : Blo 1919435 4860557 := bbase (se 3 (by rfl) ⟨911354, by rfl⟩ : syracuseStep 4860557 = 1822709) (by norm_num)
theorem B3240371 : Blo 1919435 3240371 := bstep (se 1 (by rfl) ⟨2430278, by rfl⟩ : syracuseStep 3240371 = 4860557) B4860557
theorem B2160247 : Blo 1919435 2160247 := bstep (se 1 (by rfl) ⟨1620185, by rfl⟩ : syracuseStep 2160247 = 3240371) B3240371
theorem B2880329 : Blo 1919435 2880329 := bstep (se 2 (by rfl) ⟨1080123, by rfl⟩ : syracuseStep 2880329 = 2160247) B2160247
theorem B1920219 : Blo 1919435 1920219 := bstep (se 1 (by rfl) ⟨1440164, by rfl⟩ : syracuseStep 1920219 = 2880329) B2880329
theorem B2734069 : Blo 1919435 2734069 := bbase (se 5 (by rfl) ⟨128159, by rfl⟩ : syracuseStep 2734069 = 256319) (by norm_num)
theorem B3645425 : Blo 1919435 3645425 := bstep (se 2 (by rfl) ⟨1367034, by rfl⟩ : syracuseStep 3645425 = 2734069) B2734069
theorem B9721133 : Blo 1919435 9721133 := bstep (se 3 (by rfl) ⟨1822712, by rfl⟩ : syracuseStep 9721133 = 3645425) B3645425
theorem B6480755 : Blo 1919435 6480755 := bstep (se 1 (by rfl) ⟨4860566, by rfl⟩ : syracuseStep 6480755 = 9721133) B9721133
theorem B4320503 : Blo 1919435 4320503 := bstep (se 1 (by rfl) ⟨3240377, by rfl⟩ : syracuseStep 4320503 = 6480755) B6480755
theorem B2880335 : Blo 1919435 2880335 := bstep (se 1 (by rfl) ⟨2160251, by rfl⟩ : syracuseStep 2880335 = 4320503) B4320503
theorem B1920223 : Blo 1919435 1920223 := bstep (se 1 (by rfl) ⟨1440167, by rfl⟩ : syracuseStep 1920223 = 2880335) B2880335
theorem B2880341 : Blo 1919435 2880341 := bbase (se 9 (by rfl) ⟨8438, by rfl⟩ : syracuseStep 2880341 = 16877) (by norm_num)
theorem B1920227 : Blo 1919435 1920227 := bstep (se 1 (by rfl) ⟨1440170, by rfl⟩ : syracuseStep 1920227 = 2880341) B2880341
theorem B2306881 : Blo 1919435 2306881 := bbase (se 2 (by rfl) ⟨865080, by rfl⟩ : syracuseStep 2306881 = 1730161) (by norm_num)
theorem B3075841 : Blo 1919435 3075841 := bstep (se 2 (by rfl) ⟨1153440, by rfl⟩ : syracuseStep 3075841 = 2306881) B2306881
theorem B4101121 : Blo 1919435 4101121 := bstep (se 2 (by rfl) ⟨1537920, by rfl⟩ : syracuseStep 4101121 = 3075841) B3075841
theorem B5468161 : Blo 1919435 5468161 := bstep (se 2 (by rfl) ⟨2050560, by rfl⟩ : syracuseStep 5468161 = 4101121) B4101121
theorem B7290881 : Blo 1919435 7290881 := bstep (se 2 (by rfl) ⟨2734080, by rfl⟩ : syracuseStep 7290881 = 5468161) B5468161
theorem B4860587 : Blo 1919435 4860587 := bstep (se 1 (by rfl) ⟨3645440, by rfl⟩ : syracuseStep 4860587 = 7290881) B7290881
theorem B3240391 : Blo 1919435 3240391 := bstep (se 1 (by rfl) ⟨2430293, by rfl⟩ : syracuseStep 3240391 = 4860587) B4860587
theorem B4320521 : Blo 1919435 4320521 := bstep (se 2 (by rfl) ⟨1620195, by rfl⟩ : syracuseStep 4320521 = 3240391) B3240391
theorem B2880347 : Blo 1919435 2880347 := bstep (se 1 (by rfl) ⟨2160260, by rfl⟩ : syracuseStep 2880347 = 4320521) B4320521
theorem B1920231 : Blo 1919435 1920231 := bstep (se 1 (by rfl) ⟨1440173, by rfl⟩ : syracuseStep 1920231 = 2880347) B2880347
theorem B2160265 : Blo 1919435 2160265 := bbase (se 2 (by rfl) ⟨810099, by rfl⟩ : syracuseStep 2160265 = 1620199) (by norm_num)
theorem B2880353 : Blo 1919435 2880353 := bstep (se 2 (by rfl) ⟨1080132, by rfl⟩ : syracuseStep 2880353 = 2160265) B2160265
theorem B1920235 : Blo 1919435 1920235 := bstep (se 1 (by rfl) ⟨1440176, by rfl⟩ : syracuseStep 1920235 = 2880353) B2880353
theorem B6235637 : Blo 1919435 6235637 := bbase (se 5 (by rfl) ⟨292295, by rfl⟩ : syracuseStep 6235637 = 584591) (by norm_num)
theorem B16628365 : Blo 1919435 16628365 := bstep (se 3 (by rfl) ⟨3117818, by rfl⟩ : syracuseStep 16628365 = 6235637) B6235637
theorem B22171153 : Blo 1919435 22171153 := bstep (se 2 (by rfl) ⟨8314182, by rfl⟩ : syracuseStep 22171153 = 16628365) B16628365
theorem B29561537 : Blo 1919435 29561537 := bstep (se 2 (by rfl) ⟨11085576, by rfl⟩ : syracuseStep 29561537 = 22171153) B22171153
theorem B78830765 : Blo 1919435 78830765 := bstep (se 3 (by rfl) ⟨14780768, by rfl⟩ : syracuseStep 78830765 = 29561537) B29561537
theorem B52553843 : Blo 1919435 52553843 := bstep (se 1 (by rfl) ⟨39415382, by rfl⟩ : syracuseStep 52553843 = 78830765) B78830765
theorem B35035895 : Blo 1919435 35035895 := bstep (se 1 (by rfl) ⟨26276921, by rfl⟩ : syracuseStep 35035895 = 52553843) B52553843
theorem B23357263 : Blo 1919435 23357263 := bstep (se 1 (by rfl) ⟨17517947, by rfl⟩ : syracuseStep 23357263 = 35035895) B35035895
theorem B31143017 : Blo 1919435 31143017 := bstep (se 2 (by rfl) ⟨11678631, by rfl⟩ : syracuseStep 31143017 = 23357263) B23357263
theorem B20762011 : Blo 1919435 20762011 := bstep (se 1 (by rfl) ⟨15571508, by rfl⟩ : syracuseStep 20762011 = 31143017) B31143017
theorem B27682681 : Blo 1919435 27682681 := bstep (se 2 (by rfl) ⟨10381005, by rfl⟩ : syracuseStep 27682681 = 20762011) B20762011
theorem B36910241 : Blo 1919435 36910241 := bstep (se 2 (by rfl) ⟨13841340, by rfl⟩ : syracuseStep 36910241 = 27682681) B27682681
theorem B24606827 : Blo 1919435 24606827 := bstep (se 1 (by rfl) ⟨18455120, by rfl⟩ : syracuseStep 24606827 = 36910241) B36910241
theorem B16404551 : Blo 1919435 16404551 := bstep (se 1 (by rfl) ⟨12303413, by rfl⟩ : syracuseStep 16404551 = 24606827) B24606827
theorem B10936367 : Blo 1919435 10936367 := bstep (se 1 (by rfl) ⟨8202275, by rfl⟩ : syracuseStep 10936367 = 16404551) B16404551
theorem B7290911 : Blo 1919435 7290911 := bstep (se 1 (by rfl) ⟨5468183, by rfl⟩ : syracuseStep 7290911 = 10936367) B10936367
theorem B4860607 : Blo 1919435 4860607 := bstep (se 1 (by rfl) ⟨3645455, by rfl⟩ : syracuseStep 4860607 = 7290911) B7290911
theorem B6480809 : Blo 1919435 6480809 := bstep (se 2 (by rfl) ⟨2430303, by rfl⟩ : syracuseStep 6480809 = 4860607) B4860607
theorem B4320539 : Blo 1919435 4320539 := bstep (se 1 (by rfl) ⟨3240404, by rfl⟩ : syracuseStep 4320539 = 6480809) B6480809
theorem B2880359 : Blo 1919435 2880359 := bstep (se 1 (by rfl) ⟨2160269, by rfl⟩ : syracuseStep 2880359 = 4320539) B4320539
theorem B1920239 : Blo 1919435 1920239 := bstep (se 1 (by rfl) ⟨1440179, by rfl⟩ : syracuseStep 1920239 = 2880359) B2880359
theorem B2880365 : Blo 1919435 2880365 := bbase (se 3 (by rfl) ⟨540068, by rfl⟩ : syracuseStep 2880365 = 1080137) (by norm_num)
theorem B1920243 : Blo 1919435 1920243 := bstep (se 1 (by rfl) ⟨1440182, by rfl⟩ : syracuseStep 1920243 = 2880365) B2880365
theorem B4320557 : Blo 1919435 4320557 := bbase (se 3 (by rfl) ⟨810104, by rfl⟩ : syracuseStep 4320557 = 1620209) (by norm_num)
theorem B2880371 : Blo 1919435 2880371 := bstep (se 1 (by rfl) ⟨2160278, by rfl⟩ : syracuseStep 2880371 = 4320557) B4320557
theorem B1920247 : Blo 1919435 1920247 := bstep (se 1 (by rfl) ⟨1440185, by rfl⟩ : syracuseStep 1920247 = 2880371) B2880371
theorem B9227621 : Blo 1919435 9227621 := bbase (se 4 (by rfl) ⟨865089, by rfl⟩ : syracuseStep 9227621 = 1730179) (by norm_num)
theorem B6151747 : Blo 1919435 6151747 := bstep (se 1 (by rfl) ⟨4613810, by rfl⟩ : syracuseStep 6151747 = 9227621) B9227621
theorem B8202329 : Blo 1919435 8202329 := bstep (se 2 (by rfl) ⟨3075873, by rfl⟩ : syracuseStep 8202329 = 6151747) B6151747
theorem B5468219 : Blo 1919435 5468219 := bstep (se 1 (by rfl) ⟨4101164, by rfl⟩ : syracuseStep 5468219 = 8202329) B8202329
theorem B3645479 : Blo 1919435 3645479 := bstep (se 1 (by rfl) ⟨2734109, by rfl⟩ : syracuseStep 3645479 = 5468219) B5468219
theorem B2430319 : Blo 1919435 2430319 := bstep (se 1 (by rfl) ⟨1822739, by rfl⟩ : syracuseStep 2430319 = 3645479) B3645479
theorem B3240425 : Blo 1919435 3240425 := bstep (se 2 (by rfl) ⟨1215159, by rfl⟩ : syracuseStep 3240425 = 2430319) B2430319
theorem B2160283 : Blo 1919435 2160283 := bstep (se 1 (by rfl) ⟨1620212, by rfl⟩ : syracuseStep 2160283 = 3240425) B3240425
theorem B2880377 : Blo 1919435 2880377 := bstep (se 2 (by rfl) ⟨1080141, by rfl⟩ : syracuseStep 2880377 = 2160283) B2160283
theorem B1920251 : Blo 1919435 1920251 := bstep (se 1 (by rfl) ⟨1440188, by rfl⟩ : syracuseStep 1920251 = 2880377) B2880377
theorem B2959517 : Blo 1919435 2959517 := bbase (se 3 (by rfl) ⟨554909, by rfl⟩ : syracuseStep 2959517 = 1109819) (by norm_num)
theorem B7892045 : Blo 1919435 7892045 := bstep (se 3 (by rfl) ⟨1479758, by rfl⟩ : syracuseStep 7892045 = 2959517) B2959517
theorem B5261363 : Blo 1919435 5261363 := bstep (se 1 (by rfl) ⟨3946022, by rfl⟩ : syracuseStep 5261363 = 7892045) B7892045
theorem B3507575 : Blo 1919435 3507575 := bstep (se 1 (by rfl) ⟨2630681, by rfl⟩ : syracuseStep 3507575 = 5261363) B5261363
theorem B37414133 : Blo 1919435 37414133 := bstep (se 5 (by rfl) ⟨1753787, by rfl⟩ : syracuseStep 37414133 = 3507575) B3507575
theorem B24942755 : Blo 1919435 24942755 := bstep (se 1 (by rfl) ⟨18707066, by rfl⟩ : syracuseStep 24942755 = 37414133) B37414133
theorem B16628503 : Blo 1919435 16628503 := bstep (se 1 (by rfl) ⟨12471377, by rfl⟩ : syracuseStep 16628503 = 24942755) B24942755
theorem B22171337 : Blo 1919435 22171337 := bstep (se 2 (by rfl) ⟨8314251, by rfl⟩ : syracuseStep 22171337 = 16628503) B16628503
theorem B14780891 : Blo 1919435 14780891 := bstep (se 1 (by rfl) ⟨11085668, by rfl⟩ : syracuseStep 14780891 = 22171337) B22171337
theorem B39415709 : Blo 1919435 39415709 := bstep (se 3 (by rfl) ⟨7390445, by rfl⟩ : syracuseStep 39415709 = 14780891) B14780891
theorem B26277139 : Blo 1919435 26277139 := bstep (se 1 (by rfl) ⟨19707854, by rfl⟩ : syracuseStep 26277139 = 39415709) B39415709
theorem B35036185 : Blo 1919435 35036185 := bstep (se 2 (by rfl) ⟨13138569, by rfl⟩ : syracuseStep 35036185 = 26277139) B26277139
theorem B46714913 : Blo 1919435 46714913 := bstep (se 2 (by rfl) ⟨17518092, by rfl⟩ : syracuseStep 46714913 = 35036185) B35036185
theorem B31143275 : Blo 1919435 31143275 := bstep (se 1 (by rfl) ⟨23357456, by rfl⟩ : syracuseStep 31143275 = 46714913) B46714913
theorem B20762183 : Blo 1919435 20762183 := bstep (se 1 (by rfl) ⟨15571637, by rfl⟩ : syracuseStep 20762183 = 31143275) B31143275
theorem B13841455 : Blo 1919435 13841455 := bstep (se 1 (by rfl) ⟨10381091, by rfl⟩ : syracuseStep 13841455 = 20762183) B20762183
theorem B18455273 : Blo 1919435 18455273 := bstep (se 2 (by rfl) ⟨6920727, by rfl⟩ : syracuseStep 18455273 = 13841455) B13841455
theorem B12303515 : Blo 1919435 12303515 := bstep (se 1 (by rfl) ⟨9227636, by rfl⟩ : syracuseStep 12303515 = 18455273) B18455273
theorem B32809373 : Blo 1919435 32809373 := bstep (se 3 (by rfl) ⟨6151757, by rfl⟩ : syracuseStep 32809373 = 12303515) B12303515
theorem B21872915 : Blo 1919435 21872915 := bstep (se 1 (by rfl) ⟨16404686, by rfl⟩ : syracuseStep 21872915 = 32809373) B32809373
theorem B14581943 : Blo 1919435 14581943 := bstep (se 1 (by rfl) ⟨10936457, by rfl⟩ : syracuseStep 14581943 = 21872915) B21872915
theorem B9721295 : Blo 1919435 9721295 := bstep (se 1 (by rfl) ⟨7290971, by rfl⟩ : syracuseStep 9721295 = 14581943) B14581943
theorem B6480863 : Blo 1919435 6480863 := bstep (se 1 (by rfl) ⟨4860647, by rfl⟩ : syracuseStep 6480863 = 9721295) B9721295
theorem B4320575 : Blo 1919435 4320575 := bstep (se 1 (by rfl) ⟨3240431, by rfl⟩ : syracuseStep 4320575 = 6480863) B6480863
theorem B2880383 : Blo 1919435 2880383 := bstep (se 1 (by rfl) ⟨2160287, by rfl⟩ : syracuseStep 2880383 = 4320575) B4320575
theorem B1920255 : Blo 1919435 1920255 := bstep (se 1 (by rfl) ⟨1440191, by rfl⟩ : syracuseStep 1920255 = 2880383) B2880383
theorem B2880389 : Blo 1919435 2880389 := bbase (se 4 (by rfl) ⟨270036, by rfl⟩ : syracuseStep 2880389 = 540073) (by norm_num)
theorem B1920259 : Blo 1919435 1920259 := bstep (se 1 (by rfl) ⟨1440194, by rfl⟩ : syracuseStep 1920259 = 2880389) B2880389
theorem B3240445 : Blo 1919435 3240445 := bbase (se 3 (by rfl) ⟨607583, by rfl⟩ : syracuseStep 3240445 = 1215167) (by norm_num)
theorem B4320593 : Blo 1919435 4320593 := bstep (se 2 (by rfl) ⟨1620222, by rfl⟩ : syracuseStep 4320593 = 3240445) B3240445
theorem B2880395 : Blo 1919435 2880395 := bstep (se 1 (by rfl) ⟨2160296, by rfl⟩ : syracuseStep 2880395 = 4320593) B4320593
theorem B1920263 : Blo 1919435 1920263 := bstep (se 1 (by rfl) ⟨1440197, by rfl⟩ : syracuseStep 1920263 = 2880395) B2880395
theorem B2160301 : Blo 1919435 2160301 := bbase (se 3 (by rfl) ⟨405056, by rfl⟩ : syracuseStep 2160301 = 810113) (by norm_num)
theorem B2880401 : Blo 1919435 2880401 := bstep (se 2 (by rfl) ⟨1080150, by rfl⟩ : syracuseStep 2880401 = 2160301) B2160301
theorem B1920267 : Blo 1919435 1920267 := bstep (se 1 (by rfl) ⟨1440200, by rfl⟩ : syracuseStep 1920267 = 2880401) B2880401
theorem B6480917 : Blo 1919435 6480917 := bbase (se 6 (by rfl) ⟨151896, by rfl⟩ : syracuseStep 6480917 = 303793) (by norm_num)
theorem B4320611 : Blo 1919435 4320611 := bstep (se 1 (by rfl) ⟨3240458, by rfl⟩ : syracuseStep 4320611 = 6480917) B6480917
theorem B2880407 : Blo 1919435 2880407 := bstep (se 1 (by rfl) ⟨2160305, by rfl⟩ : syracuseStep 2880407 = 4320611) B4320611
theorem B1920271 : Blo 1919435 1920271 := bstep (se 1 (by rfl) ⟨1440203, by rfl⟩ : syracuseStep 1920271 = 2880407) B2880407
theorem B2880413 : Blo 1919435 2880413 := bbase (se 3 (by rfl) ⟨540077, by rfl⟩ : syracuseStep 2880413 = 1080155) (by norm_num)
theorem B1920275 : Blo 1919435 1920275 := bstep (se 1 (by rfl) ⟨1440206, by rfl⟩ : syracuseStep 1920275 = 2880413) B2880413
theorem B4320629 : Blo 1919435 4320629 := bbase (se 5 (by rfl) ⟨202529, by rfl⟩ : syracuseStep 4320629 = 405059) (by norm_num)
theorem B2880419 : Blo 1919435 2880419 := bstep (se 1 (by rfl) ⟨2160314, by rfl⟩ : syracuseStep 2880419 = 4320629) B4320629
theorem B1920279 : Blo 1919435 1920279 := bstep (se 1 (by rfl) ⟨1440209, by rfl⟩ : syracuseStep 1920279 = 2880419) B2880419
theorem B4676837 : Blo 1919435 4676837 := bbase (se 4 (by rfl) ⟨438453, by rfl⟩ : syracuseStep 4676837 = 876907) (by norm_num)
theorem B12471565 : Blo 1919435 12471565 := bstep (se 3 (by rfl) ⟨2338418, by rfl⟩ : syracuseStep 12471565 = 4676837) B4676837
theorem B16628753 : Blo 1919435 16628753 := bstep (se 2 (by rfl) ⟨6235782, by rfl⟩ : syracuseStep 16628753 = 12471565) B12471565
theorem B11085835 : Blo 1919435 11085835 := bstep (se 1 (by rfl) ⟨8314376, by rfl⟩ : syracuseStep 11085835 = 16628753) B16628753
theorem B14781113 : Blo 1919435 14781113 := bstep (se 2 (by rfl) ⟨5542917, by rfl⟩ : syracuseStep 14781113 = 11085835) B11085835
theorem B9854075 : Blo 1919435 9854075 := bstep (se 1 (by rfl) ⟨7390556, by rfl⟩ : syracuseStep 9854075 = 14781113) B14781113
theorem B26277533 : Blo 1919435 26277533 := bstep (se 3 (by rfl) ⟨4927037, by rfl⟩ : syracuseStep 26277533 = 9854075) B9854075
theorem B17518355 : Blo 1919435 17518355 := bstep (se 1 (by rfl) ⟨13138766, by rfl⟩ : syracuseStep 17518355 = 26277533) B26277533
theorem B11678903 : Blo 1919435 11678903 := bstep (se 1 (by rfl) ⟨8759177, by rfl⟩ : syracuseStep 11678903 = 17518355) B17518355
theorem B7785935 : Blo 1919435 7785935 := bstep (se 1 (by rfl) ⟨5839451, by rfl⟩ : syracuseStep 7785935 = 11678903) B11678903
theorem B5190623 : Blo 1919435 5190623 := bstep (se 1 (by rfl) ⟨3892967, by rfl⟩ : syracuseStep 5190623 = 7785935) B7785935
theorem B3460415 : Blo 1919435 3460415 := bstep (se 1 (by rfl) ⟨2595311, by rfl⟩ : syracuseStep 3460415 = 5190623) B5190623
theorem B9227773 : Blo 1919435 9227773 := bstep (se 3 (by rfl) ⟨1730207, by rfl⟩ : syracuseStep 9227773 = 3460415) B3460415
theorem B12303697 : Blo 1919435 12303697 := bstep (se 2 (by rfl) ⟨4613886, by rfl⟩ : syracuseStep 12303697 = 9227773) B9227773
theorem B16404929 : Blo 1919435 16404929 := bstep (se 2 (by rfl) ⟨6151848, by rfl⟩ : syracuseStep 16404929 = 12303697) B12303697
theorem B10936619 : Blo 1919435 10936619 := bstep (se 1 (by rfl) ⟨8202464, by rfl⟩ : syracuseStep 10936619 = 16404929) B16404929
theorem B7291079 : Blo 1919435 7291079 := bstep (se 1 (by rfl) ⟨5468309, by rfl⟩ : syracuseStep 7291079 = 10936619) B10936619
theorem B4860719 : Blo 1919435 4860719 := bstep (se 1 (by rfl) ⟨3645539, by rfl⟩ : syracuseStep 4860719 = 7291079) B7291079
theorem B3240479 : Blo 1919435 3240479 := bstep (se 1 (by rfl) ⟨2430359, by rfl⟩ : syracuseStep 3240479 = 4860719) B4860719
theorem B2160319 : Blo 1919435 2160319 := bstep (se 1 (by rfl) ⟨1620239, by rfl⟩ : syracuseStep 2160319 = 3240479) B3240479
theorem B2880425 : Blo 1919435 2880425 := bstep (se 2 (by rfl) ⟨1080159, by rfl⟩ : syracuseStep 2880425 = 2160319) B2160319
theorem B1920283 : Blo 1919435 1920283 := bstep (se 1 (by rfl) ⟨1440212, by rfl⟩ : syracuseStep 1920283 = 2880425) B2880425
theorem B7291093 : Blo 1919435 7291093 := bbase (se 7 (by rfl) ⟨85442, by rfl⟩ : syracuseStep 7291093 = 170885) (by norm_num)
theorem B9721457 : Blo 1919435 9721457 := bstep (se 2 (by rfl) ⟨3645546, by rfl⟩ : syracuseStep 9721457 = 7291093) B7291093
theorem B6480971 : Blo 1919435 6480971 := bstep (se 1 (by rfl) ⟨4860728, by rfl⟩ : syracuseStep 6480971 = 9721457) B9721457
theorem B4320647 : Blo 1919435 4320647 := bstep (se 1 (by rfl) ⟨3240485, by rfl⟩ : syracuseStep 4320647 = 6480971) B6480971
theorem B2880431 : Blo 1919435 2880431 := bstep (se 1 (by rfl) ⟨2160323, by rfl⟩ : syracuseStep 2880431 = 4320647) B4320647
theorem B1920287 : Blo 1919435 1920287 := bstep (se 1 (by rfl) ⟨1440215, by rfl⟩ : syracuseStep 1920287 = 2880431) B2880431
theorem B2880437 : Blo 1919435 2880437 := bbase (se 5 (by rfl) ⟨135020, by rfl⟩ : syracuseStep 2880437 = 270041) (by norm_num)
theorem B1920291 : Blo 1919435 1920291 := bstep (se 1 (by rfl) ⟨1440218, by rfl⟩ : syracuseStep 1920291 = 2880437) B2880437
theorem B4860749 : Blo 1919435 4860749 := bbase (se 3 (by rfl) ⟨911390, by rfl⟩ : syracuseStep 4860749 = 1822781) (by norm_num)
theorem B3240499 : Blo 1919435 3240499 := bstep (se 1 (by rfl) ⟨2430374, by rfl⟩ : syracuseStep 3240499 = 4860749) B4860749
theorem B4320665 : Blo 1919435 4320665 := bstep (se 2 (by rfl) ⟨1620249, by rfl⟩ : syracuseStep 4320665 = 3240499) B3240499
theorem B2880443 : Blo 1919435 2880443 := bstep (se 1 (by rfl) ⟨2160332, by rfl⟩ : syracuseStep 2880443 = 4320665) B4320665
theorem B1920295 : Blo 1919435 1920295 := bstep (se 1 (by rfl) ⟨1440221, by rfl⟩ : syracuseStep 1920295 = 2880443) B2880443
theorem B2160337 : Blo 1919435 2160337 := bbase (se 2 (by rfl) ⟨810126, by rfl⟩ : syracuseStep 2160337 = 1620253) (by norm_num)
theorem B2880449 : Blo 1919435 2880449 := bstep (se 2 (by rfl) ⟨1080168, by rfl⟩ : syracuseStep 2880449 = 2160337) B2160337
theorem B1920299 : Blo 1919435 1920299 := bstep (se 1 (by rfl) ⟨1440224, by rfl⟩ : syracuseStep 1920299 = 2880449) B2880449
theorem B8759269 : Blo 1919435 8759269 := bbase (se 4 (by rfl) ⟨821181, by rfl⟩ : syracuseStep 8759269 = 1642363) (by norm_num)
theorem B11679025 : Blo 1919435 11679025 := bstep (se 2 (by rfl) ⟨4379634, by rfl⟩ : syracuseStep 11679025 = 8759269) B8759269
theorem B15572033 : Blo 1919435 15572033 := bstep (se 2 (by rfl) ⟨5839512, by rfl⟩ : syracuseStep 15572033 = 11679025) B11679025
theorem B10381355 : Blo 1919435 10381355 := bstep (se 1 (by rfl) ⟨7786016, by rfl⟩ : syracuseStep 10381355 = 15572033) B15572033
theorem B6920903 : Blo 1919435 6920903 := bstep (se 1 (by rfl) ⟨5190677, by rfl⟩ : syracuseStep 6920903 = 10381355) B10381355
theorem B4613935 : Blo 1919435 4613935 := bstep (se 1 (by rfl) ⟨3460451, by rfl⟩ : syracuseStep 4613935 = 6920903) B6920903
theorem B6151913 : Blo 1919435 6151913 := bstep (se 2 (by rfl) ⟨2306967, by rfl⟩ : syracuseStep 6151913 = 4613935) B4613935
theorem B4101275 : Blo 1919435 4101275 := bstep (se 1 (by rfl) ⟨3075956, by rfl⟩ : syracuseStep 4101275 = 6151913) B6151913
theorem B2734183 : Blo 1919435 2734183 := bstep (se 1 (by rfl) ⟨2050637, by rfl⟩ : syracuseStep 2734183 = 4101275) B4101275
theorem B3645577 : Blo 1919435 3645577 := bstep (se 2 (by rfl) ⟨1367091, by rfl⟩ : syracuseStep 3645577 = 2734183) B2734183
theorem B4860769 : Blo 1919435 4860769 := bstep (se 2 (by rfl) ⟨1822788, by rfl⟩ : syracuseStep 4860769 = 3645577) B3645577
theorem B6481025 : Blo 1919435 6481025 := bstep (se 2 (by rfl) ⟨2430384, by rfl⟩ : syracuseStep 6481025 = 4860769) B4860769
theorem B4320683 : Blo 1919435 4320683 := bstep (se 1 (by rfl) ⟨3240512, by rfl⟩ : syracuseStep 4320683 = 6481025) B6481025
theorem B2880455 : Blo 1919435 2880455 := bstep (se 1 (by rfl) ⟨2160341, by rfl⟩ : syracuseStep 2880455 = 4320683) B4320683
theorem B1920303 : Blo 1919435 1920303 := bstep (se 1 (by rfl) ⟨1440227, by rfl⟩ : syracuseStep 1920303 = 2880455) B2880455
theorem B2880461 : Blo 1919435 2880461 := bbase (se 3 (by rfl) ⟨540086, by rfl⟩ : syracuseStep 2880461 = 1080173) (by norm_num)
theorem B1920307 : Blo 1919435 1920307 := bstep (se 1 (by rfl) ⟨1440230, by rfl⟩ : syracuseStep 1920307 = 2880461) B2880461
theorem B4320701 : Blo 1919435 4320701 := bbase (se 3 (by rfl) ⟨810131, by rfl⟩ : syracuseStep 4320701 = 1620263) (by norm_num)
theorem B2880467 : Blo 1919435 2880467 := bstep (se 1 (by rfl) ⟨2160350, by rfl⟩ : syracuseStep 2880467 = 4320701) B4320701
theorem B1920311 : Blo 1919435 1920311 := bstep (se 1 (by rfl) ⟨1440233, by rfl⟩ : syracuseStep 1920311 = 2880467) B2880467
theorem B3240533 : Blo 1919435 3240533 := bbase (se 8 (by rfl) ⟨18987, by rfl⟩ : syracuseStep 3240533 = 37975) (by norm_num)
theorem B2160355 : Blo 1919435 2160355 := bstep (se 1 (by rfl) ⟨1620266, by rfl⟩ : syracuseStep 2160355 = 3240533) B3240533
theorem B2880473 : Blo 1919435 2880473 := bstep (se 2 (by rfl) ⟨1080177, by rfl⟩ : syracuseStep 2880473 = 2160355) B2160355
theorem B1920315 : Blo 1919435 1920315 := bstep (se 1 (by rfl) ⟨1440236, by rfl⟩ : syracuseStep 1920315 = 2880473) B2880473
theorem B1973077 : Blo 1919435 1973077 := bbase (se 9 (by rfl) ⟨5780, by rfl⟩ : syracuseStep 1973077 = 11561) (by norm_num)
theorem B10523077 : Blo 1919435 10523077 := bstep (se 4 (by rfl) ⟨986538, by rfl⟩ : syracuseStep 10523077 = 1973077) B1973077
theorem B56123077 : Blo 1919435 56123077 := bstep (se 4 (by rfl) ⟨5261538, by rfl⟩ : syracuseStep 56123077 = 10523077) B10523077
theorem B74830769 : Blo 1919435 74830769 := bstep (se 2 (by rfl) ⟨28061538, by rfl⟩ : syracuseStep 74830769 = 56123077) B56123077
theorem B49887179 : Blo 1919435 49887179 := bstep (se 1 (by rfl) ⟨37415384, by rfl⟩ : syracuseStep 49887179 = 74830769) B74830769
theorem B33258119 : Blo 1919435 33258119 := bstep (se 1 (by rfl) ⟨24943589, by rfl⟩ : syracuseStep 33258119 = 49887179) B49887179
theorem B88688317 : Blo 1919435 88688317 := bstep (se 3 (by rfl) ⟨16629059, by rfl⟩ : syracuseStep 88688317 = 33258119) B33258119
theorem B118251089 : Blo 1919435 118251089 := bstep (se 2 (by rfl) ⟨44344158, by rfl⟩ : syracuseStep 118251089 = 88688317) B88688317
theorem B78834059 : Blo 1919435 78834059 := bstep (se 1 (by rfl) ⟨59125544, by rfl⟩ : syracuseStep 78834059 = 118251089) B118251089
theorem B52556039 : Blo 1919435 52556039 := bstep (se 1 (by rfl) ⟨39417029, by rfl⟩ : syracuseStep 52556039 = 78834059) B78834059
theorem B35037359 : Blo 1919435 35037359 := bstep (se 1 (by rfl) ⟨26278019, by rfl⟩ : syracuseStep 35037359 = 52556039) B52556039
theorem B23358239 : Blo 1919435 23358239 := bstep (se 1 (by rfl) ⟨17518679, by rfl⟩ : syracuseStep 23358239 = 35037359) B35037359
theorem B15572159 : Blo 1919435 15572159 := bstep (se 1 (by rfl) ⟨11679119, by rfl⟩ : syracuseStep 15572159 = 23358239) B23358239
theorem B10381439 : Blo 1919435 10381439 := bstep (se 1 (by rfl) ⟨7786079, by rfl⟩ : syracuseStep 10381439 = 15572159) B15572159
theorem B6920959 : Blo 1919435 6920959 := bstep (se 1 (by rfl) ⟨5190719, by rfl⟩ : syracuseStep 6920959 = 10381439) B10381439
theorem B9227945 : Blo 1919435 9227945 := bstep (se 2 (by rfl) ⟨3460479, by rfl⟩ : syracuseStep 9227945 = 6920959) B6920959
theorem B6151963 : Blo 1919435 6151963 := bstep (se 1 (by rfl) ⟨4613972, by rfl⟩ : syracuseStep 6151963 = 9227945) B9227945
theorem B8202617 : Blo 1919435 8202617 := bstep (se 2 (by rfl) ⟨3075981, by rfl⟩ : syracuseStep 8202617 = 6151963) B6151963
theorem B5468411 : Blo 1919435 5468411 := bstep (se 1 (by rfl) ⟨4101308, by rfl⟩ : syracuseStep 5468411 = 8202617) B8202617
theorem B14582429 : Blo 1919435 14582429 := bstep (se 3 (by rfl) ⟨2734205, by rfl⟩ : syracuseStep 14582429 = 5468411) B5468411
theorem B9721619 : Blo 1919435 9721619 := bstep (se 1 (by rfl) ⟨7291214, by rfl⟩ : syracuseStep 9721619 = 14582429) B14582429
theorem B6481079 : Blo 1919435 6481079 := bstep (se 1 (by rfl) ⟨4860809, by rfl⟩ : syracuseStep 6481079 = 9721619) B9721619
theorem B4320719 : Blo 1919435 4320719 := bstep (se 1 (by rfl) ⟨3240539, by rfl⟩ : syracuseStep 4320719 = 6481079) B6481079
theorem B2880479 : Blo 1919435 2880479 := bstep (se 1 (by rfl) ⟨2160359, by rfl⟩ : syracuseStep 2880479 = 4320719) B4320719
theorem B1920319 : Blo 1919435 1920319 := bstep (se 1 (by rfl) ⟨1440239, by rfl⟩ : syracuseStep 1920319 = 2880479) B2880479
theorem B2880485 : Blo 1919435 2880485 := bbase (se 4 (by rfl) ⟨270045, by rfl⟩ : syracuseStep 2880485 = 540091) (by norm_num)
theorem B1920323 : Blo 1919435 1920323 := bstep (se 1 (by rfl) ⟨1440242, by rfl⟩ : syracuseStep 1920323 = 2880485) B2880485
theorem B2189845 : Blo 1919435 2189845 := bbase (se 6 (by rfl) ⟨51324, by rfl⟩ : syracuseStep 2189845 = 102649) (by norm_num)
theorem B11679173 : Blo 1919435 11679173 := bstep (se 4 (by rfl) ⟨1094922, by rfl⟩ : syracuseStep 11679173 = 2189845) B2189845
theorem B7786115 : Blo 1919435 7786115 := bstep (se 1 (by rfl) ⟨5839586, by rfl⟩ : syracuseStep 7786115 = 11679173) B11679173
theorem B5190743 : Blo 1919435 5190743 := bstep (se 1 (by rfl) ⟨3893057, by rfl⟩ : syracuseStep 5190743 = 7786115) B7786115
theorem B3460495 : Blo 1919435 3460495 := bstep (se 1 (by rfl) ⟨2595371, by rfl⟩ : syracuseStep 3460495 = 5190743) B5190743
theorem B4613993 : Blo 1919435 4613993 := bstep (se 2 (by rfl) ⟨1730247, by rfl⟩ : syracuseStep 4613993 = 3460495) B3460495
theorem B3075995 : Blo 1919435 3075995 := bstep (se 1 (by rfl) ⟨2306996, by rfl⟩ : syracuseStep 3075995 = 4613993) B4613993
theorem B8202653 : Blo 1919435 8202653 := bstep (se 3 (by rfl) ⟨1537997, by rfl⟩ : syracuseStep 8202653 = 3075995) B3075995
theorem B5468435 : Blo 1919435 5468435 := bstep (se 1 (by rfl) ⟨4101326, by rfl⟩ : syracuseStep 5468435 = 8202653) B8202653
theorem B3645623 : Blo 1919435 3645623 := bstep (se 1 (by rfl) ⟨2734217, by rfl⟩ : syracuseStep 3645623 = 5468435) B5468435
theorem B2430415 : Blo 1919435 2430415 := bstep (se 1 (by rfl) ⟨1822811, by rfl⟩ : syracuseStep 2430415 = 3645623) B3645623
theorem B3240553 : Blo 1919435 3240553 := bstep (se 2 (by rfl) ⟨1215207, by rfl⟩ : syracuseStep 3240553 = 2430415) B2430415
theorem B4320737 : Blo 1919435 4320737 := bstep (se 2 (by rfl) ⟨1620276, by rfl⟩ : syracuseStep 4320737 = 3240553) B3240553
theorem B2880491 : Blo 1919435 2880491 := bstep (se 1 (by rfl) ⟨2160368, by rfl⟩ : syracuseStep 2880491 = 4320737) B4320737
theorem B1920327 : Blo 1919435 1920327 := bstep (se 1 (by rfl) ⟨1440245, by rfl⟩ : syracuseStep 1920327 = 2880491) B2880491
theorem B2160373 : Blo 1919435 2160373 := bbase (se 5 (by rfl) ⟨101267, by rfl⟩ : syracuseStep 2160373 = 202535) (by norm_num)
theorem B2880497 : Blo 1919435 2880497 := bstep (se 2 (by rfl) ⟨1080186, by rfl⟩ : syracuseStep 2880497 = 2160373) B2160373
theorem B1920331 : Blo 1919435 1920331 := bstep (se 1 (by rfl) ⟨1440248, by rfl⟩ : syracuseStep 1920331 = 2880497) B2880497
theorem B2430425 : Blo 1919435 2430425 := bbase (se 2 (by rfl) ⟨911409, by rfl⟩ : syracuseStep 2430425 = 1822819) (by norm_num)
theorem B6481133 : Blo 1919435 6481133 := bstep (se 3 (by rfl) ⟨1215212, by rfl⟩ : syracuseStep 6481133 = 2430425) B2430425
theorem B4320755 : Blo 1919435 4320755 := bstep (se 1 (by rfl) ⟨3240566, by rfl⟩ : syracuseStep 4320755 = 6481133) B6481133
theorem B2880503 : Blo 1919435 2880503 := bstep (se 1 (by rfl) ⟨2160377, by rfl⟩ : syracuseStep 2880503 = 4320755) B4320755
theorem B1920335 : Blo 1919435 1920335 := bstep (se 1 (by rfl) ⟨1440251, by rfl⟩ : syracuseStep 1920335 = 2880503) B2880503
theorem B2880509 : Blo 1919435 2880509 := bbase (se 3 (by rfl) ⟨540095, by rfl⟩ : syracuseStep 2880509 = 1080191) (by norm_num)
theorem B1920339 : Blo 1919435 1920339 := bstep (se 1 (by rfl) ⟨1440254, by rfl⟩ : syracuseStep 1920339 = 2880509) B2880509
theorem B4320773 : Blo 1919435 4320773 := bbase (se 4 (by rfl) ⟨405072, by rfl⟩ : syracuseStep 4320773 = 810145) (by norm_num)
theorem B2880515 : Blo 1919435 2880515 := bstep (se 1 (by rfl) ⟨2160386, by rfl⟩ : syracuseStep 2880515 = 4320773) B4320773
theorem B1920343 : Blo 1919435 1920343 := bstep (se 1 (by rfl) ⟨1440257, by rfl⟩ : syracuseStep 1920343 = 2880515) B2880515
theorem B3645661 : Blo 1919435 3645661 := bbase (se 3 (by rfl) ⟨683561, by rfl⟩ : syracuseStep 3645661 = 1367123) (by norm_num)
theorem B4860881 : Blo 1919435 4860881 := bstep (se 2 (by rfl) ⟨1822830, by rfl⟩ : syracuseStep 4860881 = 3645661) B3645661
theorem B3240587 : Blo 1919435 3240587 := bstep (se 1 (by rfl) ⟨2430440, by rfl⟩ : syracuseStep 3240587 = 4860881) B4860881
theorem B2160391 : Blo 1919435 2160391 := bstep (se 1 (by rfl) ⟨1620293, by rfl⟩ : syracuseStep 2160391 = 3240587) B3240587
theorem B2880521 : Blo 1919435 2880521 := bstep (se 2 (by rfl) ⟨1080195, by rfl⟩ : syracuseStep 2880521 = 2160391) B2160391
theorem B1920347 : Blo 1919435 1920347 := bstep (se 1 (by rfl) ⟨1440260, by rfl⟩ : syracuseStep 1920347 = 2880521) B2880521
theorem B9721781 : Blo 1919435 9721781 := bbase (se 5 (by rfl) ⟨455708, by rfl⟩ : syracuseStep 9721781 = 911417) (by norm_num)
theorem B6481187 : Blo 1919435 6481187 := bstep (se 1 (by rfl) ⟨4860890, by rfl⟩ : syracuseStep 6481187 = 9721781) B9721781
theorem B4320791 : Blo 1919435 4320791 := bstep (se 1 (by rfl) ⟨3240593, by rfl⟩ : syracuseStep 4320791 = 6481187) B6481187
theorem B2880527 : Blo 1919435 2880527 := bstep (se 1 (by rfl) ⟨2160395, by rfl⟩ : syracuseStep 2880527 = 4320791) B4320791
theorem B1920351 : Blo 1919435 1920351 := bstep (se 1 (by rfl) ⟨1440263, by rfl⟩ : syracuseStep 1920351 = 2880527) B2880527
theorem B2880533 : Blo 1919435 2880533 := bbase (se 6 (by rfl) ⟨67512, by rfl⟩ : syracuseStep 2880533 = 135025) (by norm_num)
theorem B1920355 : Blo 1919435 1920355 := bstep (se 1 (by rfl) ⟨1440266, by rfl⟩ : syracuseStep 1920355 = 2880533) B2880533
theorem B3284821 : Blo 1919435 3284821 := bbase (se 9 (by rfl) ⟨9623, by rfl⟩ : syracuseStep 3284821 = 19247) (by norm_num)
theorem B4379761 : Blo 1919435 4379761 := bstep (se 2 (by rfl) ⟨1642410, by rfl⟩ : syracuseStep 4379761 = 3284821) B3284821
theorem B23358725 : Blo 1919435 23358725 := bstep (se 4 (by rfl) ⟨2189880, by rfl⟩ : syracuseStep 23358725 = 4379761) B4379761
theorem B15572483 : Blo 1919435 15572483 := bstep (se 1 (by rfl) ⟨11679362, by rfl⟩ : syracuseStep 15572483 = 23358725) B23358725
theorem B10381655 : Blo 1919435 10381655 := bstep (se 1 (by rfl) ⟨7786241, by rfl⟩ : syracuseStep 10381655 = 15572483) B15572483
theorem B27684413 : Blo 1919435 27684413 := bstep (se 3 (by rfl) ⟨5190827, by rfl⟩ : syracuseStep 27684413 = 10381655) B10381655
theorem B18456275 : Blo 1919435 18456275 := bstep (se 1 (by rfl) ⟨13842206, by rfl⟩ : syracuseStep 18456275 = 27684413) B27684413
theorem B12304183 : Blo 1919435 12304183 := bstep (se 1 (by rfl) ⟨9228137, by rfl⟩ : syracuseStep 12304183 = 18456275) B18456275
theorem B16405577 : Blo 1919435 16405577 := bstep (se 2 (by rfl) ⟨6152091, by rfl⟩ : syracuseStep 16405577 = 12304183) B12304183
theorem B10937051 : Blo 1919435 10937051 := bstep (se 1 (by rfl) ⟨8202788, by rfl⟩ : syracuseStep 10937051 = 16405577) B16405577
theorem B7291367 : Blo 1919435 7291367 := bstep (se 1 (by rfl) ⟨5468525, by rfl⟩ : syracuseStep 7291367 = 10937051) B10937051
theorem B4860911 : Blo 1919435 4860911 := bstep (se 1 (by rfl) ⟨3645683, by rfl⟩ : syracuseStep 4860911 = 7291367) B7291367
theorem B3240607 : Blo 1919435 3240607 := bstep (se 1 (by rfl) ⟨2430455, by rfl⟩ : syracuseStep 3240607 = 4860911) B4860911
theorem B4320809 : Blo 1919435 4320809 := bstep (se 2 (by rfl) ⟨1620303, by rfl⟩ : syracuseStep 4320809 = 3240607) B3240607
theorem B2880539 : Blo 1919435 2880539 := bstep (se 1 (by rfl) ⟨2160404, by rfl⟩ : syracuseStep 2880539 = 4320809) B4320809
theorem B1920359 : Blo 1919435 1920359 := bstep (se 1 (by rfl) ⟨1440269, by rfl⟩ : syracuseStep 1920359 = 2880539) B2880539
theorem B2160409 : Blo 1919435 2160409 := bbase (se 2 (by rfl) ⟨810153, by rfl⟩ : syracuseStep 2160409 = 1620307) (by norm_num)
theorem B2880545 : Blo 1919435 2880545 := bstep (se 2 (by rfl) ⟨1080204, by rfl⟩ : syracuseStep 2880545 = 2160409) B2160409
theorem B1920363 : Blo 1919435 1920363 := bstep (se 1 (by rfl) ⟨1440272, by rfl⟩ : syracuseStep 1920363 = 2880545) B2880545
theorem B7291397 : Blo 1919435 7291397 := bbase (se 4 (by rfl) ⟨683568, by rfl⟩ : syracuseStep 7291397 = 1367137) (by norm_num)
theorem B4860931 : Blo 1919435 4860931 := bstep (se 1 (by rfl) ⟨3645698, by rfl⟩ : syracuseStep 4860931 = 7291397) B7291397
theorem B6481241 : Blo 1919435 6481241 := bstep (se 2 (by rfl) ⟨2430465, by rfl⟩ : syracuseStep 6481241 = 4860931) B4860931
theorem B4320827 : Blo 1919435 4320827 := bstep (se 1 (by rfl) ⟨3240620, by rfl⟩ : syracuseStep 4320827 = 6481241) B6481241
theorem B2880551 : Blo 1919435 2880551 := bstep (se 1 (by rfl) ⟨2160413, by rfl⟩ : syracuseStep 2880551 = 4320827) B4320827
theorem B1920367 : Blo 1919435 1920367 := bstep (se 1 (by rfl) ⟨1440275, by rfl⟩ : syracuseStep 1920367 = 2880551) B2880551
theorem B2880557 : Blo 1919435 2880557 := bbase (se 3 (by rfl) ⟨540104, by rfl⟩ : syracuseStep 2880557 = 1080209) (by norm_num)
theorem B1920371 : Blo 1919435 1920371 := bstep (se 1 (by rfl) ⟨1440278, by rfl⟩ : syracuseStep 1920371 = 2880557) B2880557
theorem B4320845 : Blo 1919435 4320845 := bbase (se 3 (by rfl) ⟨810158, by rfl⟩ : syracuseStep 4320845 = 1620317) (by norm_num)
theorem B2880563 : Blo 1919435 2880563 := bstep (se 1 (by rfl) ⟨2160422, by rfl⟩ : syracuseStep 2880563 = 4320845) B4320845
theorem B1920375 : Blo 1919435 1920375 := bstep (se 1 (by rfl) ⟨1440281, by rfl⟩ : syracuseStep 1920375 = 2880563) B2880563
theorem B2430481 : Blo 1919435 2430481 := bbase (se 2 (by rfl) ⟨911430, by rfl⟩ : syracuseStep 2430481 = 1822861) (by norm_num)
theorem B3240641 : Blo 1919435 3240641 := bstep (se 2 (by rfl) ⟨1215240, by rfl⟩ : syracuseStep 3240641 = 2430481) B2430481
theorem B2160427 : Blo 1919435 2160427 := bstep (se 1 (by rfl) ⟨1620320, by rfl⟩ : syracuseStep 2160427 = 3240641) B3240641
theorem B2880569 : Blo 1919435 2880569 := bstep (se 2 (by rfl) ⟨1080213, by rfl⟩ : syracuseStep 2880569 = 2160427) B2160427
theorem B1920379 : Blo 1919435 1920379 := bstep (se 1 (by rfl) ⟨1440284, by rfl⟩ : syracuseStep 1920379 = 2880569) B2880569
theorem B4101445 : Blo 1919435 4101445 := bbase (se 4 (by rfl) ⟨384510, by rfl⟩ : syracuseStep 4101445 = 769021) (by norm_num)
theorem B21874373 : Blo 1919435 21874373 := bstep (se 4 (by rfl) ⟨2050722, by rfl⟩ : syracuseStep 21874373 = 4101445) B4101445
theorem B14582915 : Blo 1919435 14582915 := bstep (se 1 (by rfl) ⟨10937186, by rfl⟩ : syracuseStep 14582915 = 21874373) B21874373
theorem B9721943 : Blo 1919435 9721943 := bstep (se 1 (by rfl) ⟨7291457, by rfl⟩ : syracuseStep 9721943 = 14582915) B14582915
theorem B6481295 : Blo 1919435 6481295 := bstep (se 1 (by rfl) ⟨4860971, by rfl⟩ : syracuseStep 6481295 = 9721943) B9721943
theorem B4320863 : Blo 1919435 4320863 := bstep (se 1 (by rfl) ⟨3240647, by rfl⟩ : syracuseStep 4320863 = 6481295) B6481295
theorem B2880575 : Blo 1919435 2880575 := bstep (se 1 (by rfl) ⟨2160431, by rfl⟩ : syracuseStep 2880575 = 4320863) B4320863
theorem B1920383 : Blo 1919435 1920383 := bstep (se 1 (by rfl) ⟨1440287, by rfl⟩ : syracuseStep 1920383 = 2880575) B2880575
theorem B2880581 : Blo 1919435 2880581 := bbase (se 4 (by rfl) ⟨270054, by rfl⟩ : syracuseStep 2880581 = 540109) (by norm_num)
theorem B1920387 : Blo 1919435 1920387 := bstep (se 1 (by rfl) ⟨1440290, by rfl⟩ : syracuseStep 1920387 = 2880581) B2880581
theorem B3240661 : Blo 1919435 3240661 := bbase (se 7 (by rfl) ⟨37976, by rfl⟩ : syracuseStep 3240661 = 75953) (by norm_num)
theorem B4320881 : Blo 1919435 4320881 := bstep (se 2 (by rfl) ⟨1620330, by rfl⟩ : syracuseStep 4320881 = 3240661) B3240661
theorem B2880587 : Blo 1919435 2880587 := bstep (se 1 (by rfl) ⟨2160440, by rfl⟩ : syracuseStep 2880587 = 4320881) B4320881
theorem B1920391 : Blo 1919435 1920391 := bstep (se 1 (by rfl) ⟨1440293, by rfl⟩ : syracuseStep 1920391 = 2880587) B2880587
theorem B2160445 : Blo 1919435 2160445 := bbase (se 3 (by rfl) ⟨405083, by rfl⟩ : syracuseStep 2160445 = 810167) (by norm_num)
theorem B2880593 : Blo 1919435 2880593 := bstep (se 2 (by rfl) ⟨1080222, by rfl⟩ : syracuseStep 2880593 = 2160445) B2160445
theorem B1920395 : Blo 1919435 1920395 := bstep (se 1 (by rfl) ⟨1440296, by rfl⟩ : syracuseStep 1920395 = 2880593) B2880593
theorem B6481349 : Blo 1919435 6481349 := bbase (se 4 (by rfl) ⟨607626, by rfl⟩ : syracuseStep 6481349 = 1215253) (by norm_num)
theorem B4320899 : Blo 1919435 4320899 := bstep (se 1 (by rfl) ⟨3240674, by rfl⟩ : syracuseStep 4320899 = 6481349) B6481349
theorem B2880599 : Blo 1919435 2880599 := bstep (se 1 (by rfl) ⟨2160449, by rfl⟩ : syracuseStep 2880599 = 4320899) B4320899
theorem B1920399 : Blo 1919435 1920399 := bstep (se 1 (by rfl) ⟨1440299, by rfl⟩ : syracuseStep 1920399 = 2880599) B2880599
theorem B2880605 : Blo 1919435 2880605 := bbase (se 3 (by rfl) ⟨540113, by rfl⟩ : syracuseStep 2880605 = 1080227) (by norm_num)
theorem B1920403 : Blo 1919435 1920403 := bstep (se 1 (by rfl) ⟨1440302, by rfl⟩ : syracuseStep 1920403 = 2880605) B2880605
theorem B4320917 : Blo 1919435 4320917 := bbase (se 6 (by rfl) ⟨101271, by rfl⟩ : syracuseStep 4320917 = 202543) (by norm_num)
theorem B2880611 : Blo 1919435 2880611 := bstep (se 1 (by rfl) ⟨2160458, by rfl⟩ : syracuseStep 2880611 = 4320917) B4320917
theorem B1920407 : Blo 1919435 1920407 := bstep (se 1 (by rfl) ⟨1440305, by rfl⟩ : syracuseStep 1920407 = 2880611) B2880611
theorem B2050753 : Blo 1919435 2050753 := bbase (se 2 (by rfl) ⟨769032, by rfl⟩ : syracuseStep 2050753 = 1538065) (by norm_num)
theorem B2734337 : Blo 1919435 2734337 := bstep (se 2 (by rfl) ⟨1025376, by rfl⟩ : syracuseStep 2734337 = 2050753) B2050753
theorem B7291565 : Blo 1919435 7291565 := bstep (se 3 (by rfl) ⟨1367168, by rfl⟩ : syracuseStep 7291565 = 2734337) B2734337
theorem B4861043 : Blo 1919435 4861043 := bstep (se 1 (by rfl) ⟨3645782, by rfl⟩ : syracuseStep 4861043 = 7291565) B7291565
theorem B3240695 : Blo 1919435 3240695 := bstep (se 1 (by rfl) ⟨2430521, by rfl⟩ : syracuseStep 3240695 = 4861043) B4861043
theorem B2160463 : Blo 1919435 2160463 := bstep (se 1 (by rfl) ⟨1620347, by rfl⟩ : syracuseStep 2160463 = 3240695) B3240695
theorem B2880617 : Blo 1919435 2880617 := bstep (se 2 (by rfl) ⟨1080231, by rfl⟩ : syracuseStep 2880617 = 2160463) B2160463
theorem B1920411 : Blo 1919435 1920411 := bstep (se 1 (by rfl) ⟨1440308, by rfl⟩ : syracuseStep 1920411 = 2880617) B2880617
theorem B7786469 : Blo 1919435 7786469 := bbase (se 4 (by rfl) ⟨729981, by rfl⟩ : syracuseStep 7786469 = 1459963) (by norm_num)
theorem B5190979 : Blo 1919435 5190979 := bstep (se 1 (by rfl) ⟨3893234, by rfl⟩ : syracuseStep 5190979 = 7786469) B7786469
theorem B6921305 : Blo 1919435 6921305 := bstep (se 2 (by rfl) ⟨2595489, by rfl⟩ : syracuseStep 6921305 = 5190979) B5190979
theorem B4614203 : Blo 1919435 4614203 := bstep (se 1 (by rfl) ⟨3460652, by rfl⟩ : syracuseStep 4614203 = 6921305) B6921305
theorem B12304541 : Blo 1919435 12304541 := bstep (se 3 (by rfl) ⟨2307101, by rfl⟩ : syracuseStep 12304541 = 4614203) B4614203
theorem B8203027 : Blo 1919435 8203027 := bstep (se 1 (by rfl) ⟨6152270, by rfl⟩ : syracuseStep 8203027 = 12304541) B12304541
theorem B10937369 : Blo 1919435 10937369 := bstep (se 2 (by rfl) ⟨4101513, by rfl⟩ : syracuseStep 10937369 = 8203027) B8203027
theorem B7291579 : Blo 1919435 7291579 := bstep (se 1 (by rfl) ⟨5468684, by rfl⟩ : syracuseStep 7291579 = 10937369) B10937369
theorem B9722105 : Blo 1919435 9722105 := bstep (se 2 (by rfl) ⟨3645789, by rfl⟩ : syracuseStep 9722105 = 7291579) B7291579
theorem B6481403 : Blo 1919435 6481403 := bstep (se 1 (by rfl) ⟨4861052, by rfl⟩ : syracuseStep 6481403 = 9722105) B9722105
theorem B4320935 : Blo 1919435 4320935 := bstep (se 1 (by rfl) ⟨3240701, by rfl⟩ : syracuseStep 4320935 = 6481403) B6481403
theorem B2880623 : Blo 1919435 2880623 := bstep (se 1 (by rfl) ⟨2160467, by rfl⟩ : syracuseStep 2880623 = 4320935) B4320935
theorem B1920415 : Blo 1919435 1920415 := bstep (se 1 (by rfl) ⟨1440311, by rfl⟩ : syracuseStep 1920415 = 2880623) B2880623
theorem B2880629 : Blo 1919435 2880629 := bbase (se 5 (by rfl) ⟨135029, by rfl⟩ : syracuseStep 2880629 = 270059) (by norm_num)
theorem B1920419 : Blo 1919435 1920419 := bstep (se 1 (by rfl) ⟨1440314, by rfl⟩ : syracuseStep 1920419 = 2880629) B2880629
theorem B3645805 : Blo 1919435 3645805 := bbase (se 3 (by rfl) ⟨683588, by rfl⟩ : syracuseStep 3645805 = 1367177) (by norm_num)
theorem B4861073 : Blo 1919435 4861073 := bstep (se 2 (by rfl) ⟨1822902, by rfl⟩ : syracuseStep 4861073 = 3645805) B3645805
theorem B3240715 : Blo 1919435 3240715 := bstep (se 1 (by rfl) ⟨2430536, by rfl⟩ : syracuseStep 3240715 = 4861073) B4861073
theorem B4320953 : Blo 1919435 4320953 := bstep (se 2 (by rfl) ⟨1620357, by rfl⟩ : syracuseStep 4320953 = 3240715) B3240715
theorem B2880635 : Blo 1919435 2880635 := bstep (se 1 (by rfl) ⟨2160476, by rfl⟩ : syracuseStep 2880635 = 4320953) B4320953
theorem B1920423 : Blo 1919435 1920423 := bstep (se 1 (by rfl) ⟨1440317, by rfl⟩ : syracuseStep 1920423 = 2880635) B2880635
theorem B2160481 : Blo 1919435 2160481 := bbase (se 2 (by rfl) ⟨810180, by rfl⟩ : syracuseStep 2160481 = 1620361) (by norm_num)
theorem B2880641 : Blo 1919435 2880641 := bstep (se 2 (by rfl) ⟨1080240, by rfl⟩ : syracuseStep 2880641 = 2160481) B2160481
theorem B1920427 : Blo 1919435 1920427 := bstep (se 1 (by rfl) ⟨1440320, by rfl⟩ : syracuseStep 1920427 = 2880641) B2880641
theorem B4861093 : Blo 1919435 4861093 := bbase (se 4 (by rfl) ⟨455727, by rfl⟩ : syracuseStep 4861093 = 911455) (by norm_num)
theorem B6481457 : Blo 1919435 6481457 := bstep (se 2 (by rfl) ⟨2430546, by rfl⟩ : syracuseStep 6481457 = 4861093) B4861093
theorem B4320971 : Blo 1919435 4320971 := bstep (se 1 (by rfl) ⟨3240728, by rfl⟩ : syracuseStep 4320971 = 6481457) B6481457
theorem B2880647 : Blo 1919435 2880647 := bstep (se 1 (by rfl) ⟨2160485, by rfl⟩ : syracuseStep 2880647 = 4320971) B4320971
theorem B1920431 : Blo 1919435 1920431 := bstep (se 1 (by rfl) ⟨1440323, by rfl⟩ : syracuseStep 1920431 = 2880647) B2880647
theorem B2880653 : Blo 1919435 2880653 := bbase (se 3 (by rfl) ⟨540122, by rfl⟩ : syracuseStep 2880653 = 1080245) (by norm_num)
theorem B1920435 : Blo 1919435 1920435 := bstep (se 1 (by rfl) ⟨1440326, by rfl⟩ : syracuseStep 1920435 = 2880653) B2880653
theorem B4320989 : Blo 1919435 4320989 := bbase (se 3 (by rfl) ⟨810185, by rfl⟩ : syracuseStep 4320989 = 1620371) (by norm_num)
theorem B2880659 : Blo 1919435 2880659 := bstep (se 1 (by rfl) ⟨2160494, by rfl⟩ : syracuseStep 2880659 = 4320989) B4320989
theorem B1920439 : Blo 1919435 1920439 := bstep (se 1 (by rfl) ⟨1440329, by rfl⟩ : syracuseStep 1920439 = 2880659) B2880659
theorem B3240749 : Blo 1919435 3240749 := bbase (se 3 (by rfl) ⟨607640, by rfl⟩ : syracuseStep 3240749 = 1215281) (by norm_num)
theorem B2160499 : Blo 1919435 2160499 := bstep (se 1 (by rfl) ⟨1620374, by rfl⟩ : syracuseStep 2160499 = 3240749) B3240749
theorem B2880665 : Blo 1919435 2880665 := bstep (se 2 (by rfl) ⟨1080249, by rfl⟩ : syracuseStep 2880665 = 2160499) B2160499
theorem B1920443 : Blo 1919435 1920443 := bstep (se 1 (by rfl) ⟨1440332, by rfl⟩ : syracuseStep 1920443 = 2880665) B2880665
theorem B31146389 : Blo 1919435 31146389 := bbase (se 6 (by rfl) ⟨729993, by rfl⟩ : syracuseStep 31146389 = 1459987) (by norm_num)
theorem B20764259 : Blo 1919435 20764259 := bstep (se 1 (by rfl) ⟨15573194, by rfl⟩ : syracuseStep 20764259 = 31146389) B31146389
theorem B13842839 : Blo 1919435 13842839 := bstep (se 1 (by rfl) ⟨10382129, by rfl⟩ : syracuseStep 13842839 = 20764259) B20764259
theorem B36914237 : Blo 1919435 36914237 := bstep (se 3 (by rfl) ⟨6921419, by rfl⟩ : syracuseStep 36914237 = 13842839) B13842839
theorem B24609491 : Blo 1919435 24609491 := bstep (se 1 (by rfl) ⟨18457118, by rfl⟩ : syracuseStep 24609491 = 36914237) B36914237
theorem B16406327 : Blo 1919435 16406327 := bstep (se 1 (by rfl) ⟨12304745, by rfl⟩ : syracuseStep 16406327 = 24609491) B24609491
theorem B10937551 : Blo 1919435 10937551 := bstep (se 1 (by rfl) ⟨8203163, by rfl⟩ : syracuseStep 10937551 = 16406327) B16406327
theorem B14583401 : Blo 1919435 14583401 := bstep (se 2 (by rfl) ⟨5468775, by rfl⟩ : syracuseStep 14583401 = 10937551) B10937551
theorem B9722267 : Blo 1919435 9722267 := bstep (se 1 (by rfl) ⟨7291700, by rfl⟩ : syracuseStep 9722267 = 14583401) B14583401
theorem B6481511 : Blo 1919435 6481511 := bstep (se 1 (by rfl) ⟨4861133, by rfl⟩ : syracuseStep 6481511 = 9722267) B9722267
theorem B4321007 : Blo 1919435 4321007 := bstep (se 1 (by rfl) ⟨3240755, by rfl⟩ : syracuseStep 4321007 = 6481511) B6481511
theorem B2880671 : Blo 1919435 2880671 := bstep (se 1 (by rfl) ⟨2160503, by rfl⟩ : syracuseStep 2880671 = 4321007) B4321007
theorem B1920447 : Blo 1919435 1920447 := bstep (se 1 (by rfl) ⟨1440335, by rfl⟩ : syracuseStep 1920447 = 2880671) B2880671
theorem B2880677 : Blo 1919435 2880677 := bbase (se 4 (by rfl) ⟨270063, by rfl⟩ : syracuseStep 2880677 = 540127) (by norm_num)
theorem B1920451 : Blo 1919435 1920451 := bstep (se 1 (by rfl) ⟨1440338, by rfl⟩ : syracuseStep 1920451 = 2880677) B2880677
theorem B2430577 : Blo 1919435 2430577 := bbase (se 2 (by rfl) ⟨911466, by rfl⟩ : syracuseStep 2430577 = 1822933) (by norm_num)
theorem B3240769 : Blo 1919435 3240769 := bstep (se 2 (by rfl) ⟨1215288, by rfl⟩ : syracuseStep 3240769 = 2430577) B2430577
theorem B4321025 : Blo 1919435 4321025 := bstep (se 2 (by rfl) ⟨1620384, by rfl⟩ : syracuseStep 4321025 = 3240769) B3240769
theorem B2880683 : Blo 1919435 2880683 := bstep (se 1 (by rfl) ⟨2160512, by rfl⟩ : syracuseStep 2880683 = 4321025) B4321025
theorem B1920455 : Blo 1919435 1920455 := bstep (se 1 (by rfl) ⟨1440341, by rfl⟩ : syracuseStep 1920455 = 2880683) B2880683
theorem B2160517 : Blo 1919435 2160517 := bbase (se 4 (by rfl) ⟨202548, by rfl⟩ : syracuseStep 2160517 = 405097) (by norm_num)
theorem B2880689 : Blo 1919435 2880689 := bstep (se 2 (by rfl) ⟨1080258, by rfl⟩ : syracuseStep 2880689 = 2160517) B2160517
theorem B1920459 : Blo 1919435 1920459 := bstep (se 1 (by rfl) ⟨1440344, by rfl⟩ : syracuseStep 1920459 = 2880689) B2880689
theorem B3076213 : Blo 1919435 3076213 := bbase (se 5 (by rfl) ⟨144197, by rfl⟩ : syracuseStep 3076213 = 288395) (by norm_num)
theorem B4101617 : Blo 1919435 4101617 := bstep (se 2 (by rfl) ⟨1538106, by rfl⟩ : syracuseStep 4101617 = 3076213) B3076213
theorem B2734411 : Blo 1919435 2734411 := bstep (se 1 (by rfl) ⟨2050808, by rfl⟩ : syracuseStep 2734411 = 4101617) B4101617
theorem B3645881 : Blo 1919435 3645881 := bstep (se 2 (by rfl) ⟨1367205, by rfl⟩ : syracuseStep 3645881 = 2734411) B2734411
theorem B2430587 : Blo 1919435 2430587 := bstep (se 1 (by rfl) ⟨1822940, by rfl⟩ : syracuseStep 2430587 = 3645881) B3645881
theorem B6481565 : Blo 1919435 6481565 := bstep (se 3 (by rfl) ⟨1215293, by rfl⟩ : syracuseStep 6481565 = 2430587) B2430587
theorem B4321043 : Blo 1919435 4321043 := bstep (se 1 (by rfl) ⟨3240782, by rfl⟩ : syracuseStep 4321043 = 6481565) B6481565
theorem B2880695 : Blo 1919435 2880695 := bstep (se 1 (by rfl) ⟨2160521, by rfl⟩ : syracuseStep 2880695 = 4321043) B4321043
theorem B1920463 : Blo 1919435 1920463 := bstep (se 1 (by rfl) ⟨1440347, by rfl⟩ : syracuseStep 1920463 = 2880695) B2880695
theorem B2880701 : Blo 1919435 2880701 := bbase (se 3 (by rfl) ⟨540131, by rfl⟩ : syracuseStep 2880701 = 1080263) (by norm_num)
theorem B1920467 : Blo 1919435 1920467 := bstep (se 1 (by rfl) ⟨1440350, by rfl⟩ : syracuseStep 1920467 = 2880701) B2880701
theorem B4321061 : Blo 1919435 4321061 := bbase (se 4 (by rfl) ⟨405099, by rfl⟩ : syracuseStep 4321061 = 810199) (by norm_num)
theorem B2880707 : Blo 1919435 2880707 := bstep (se 1 (by rfl) ⟨2160530, by rfl⟩ : syracuseStep 2880707 = 4321061) B4321061
theorem B1920471 : Blo 1919435 1920471 := bstep (se 1 (by rfl) ⟨1440353, by rfl⟩ : syracuseStep 1920471 = 2880707) B2880707
theorem B4861205 : Blo 1919435 4861205 := bbase (se 6 (by rfl) ⟨113934, by rfl⟩ : syracuseStep 4861205 = 227869) (by norm_num)
theorem B3240803 : Blo 1919435 3240803 := bstep (se 1 (by rfl) ⟨2430602, by rfl⟩ : syracuseStep 3240803 = 4861205) B4861205
theorem B2160535 : Blo 1919435 2160535 := bstep (se 1 (by rfl) ⟨1620401, by rfl⟩ : syracuseStep 2160535 = 3240803) B3240803
theorem B2880713 : Blo 1919435 2880713 := bstep (se 2 (by rfl) ⟨1080267, by rfl⟩ : syracuseStep 2880713 = 2160535) B2160535
theorem B1920475 : Blo 1919435 1920475 := bstep (se 1 (by rfl) ⟨1440356, by rfl⟩ : syracuseStep 1920475 = 2880713) B2880713
theorem B8203301 : Blo 1919435 8203301 := bbase (se 4 (by rfl) ⟨769059, by rfl⟩ : syracuseStep 8203301 = 1538119) (by norm_num)
theorem B5468867 : Blo 1919435 5468867 := bstep (se 1 (by rfl) ⟨4101650, by rfl⟩ : syracuseStep 5468867 = 8203301) B8203301
theorem B3645911 : Blo 1919435 3645911 := bstep (se 1 (by rfl) ⟨2734433, by rfl⟩ : syracuseStep 3645911 = 5468867) B5468867
theorem B9722429 : Blo 1919435 9722429 := bstep (se 3 (by rfl) ⟨1822955, by rfl⟩ : syracuseStep 9722429 = 3645911) B3645911
theorem B6481619 : Blo 1919435 6481619 := bstep (se 1 (by rfl) ⟨4861214, by rfl⟩ : syracuseStep 6481619 = 9722429) B9722429
theorem B4321079 : Blo 1919435 4321079 := bstep (se 1 (by rfl) ⟨3240809, by rfl⟩ : syracuseStep 4321079 = 6481619) B6481619
theorem B2880719 : Blo 1919435 2880719 := bstep (se 1 (by rfl) ⟨2160539, by rfl⟩ : syracuseStep 2880719 = 4321079) B4321079
theorem B1920479 : Blo 1919435 1920479 := bstep (se 1 (by rfl) ⟨1440359, by rfl⟩ : syracuseStep 1920479 = 2880719) B2880719
theorem B2880725 : Blo 1919435 2880725 := bbase (se 7 (by rfl) ⟨33758, by rfl⟩ : syracuseStep 2880725 = 67517) (by norm_num)
theorem B1920483 : Blo 1919435 1920483 := bstep (se 1 (by rfl) ⟨1440362, by rfl⟩ : syracuseStep 1920483 = 2880725) B2880725
theorem B2734445 : Blo 1919435 2734445 := bbase (se 3 (by rfl) ⟨512708, by rfl⟩ : syracuseStep 2734445 = 1025417) (by norm_num)
theorem B7291853 : Blo 1919435 7291853 := bstep (se 3 (by rfl) ⟨1367222, by rfl⟩ : syracuseStep 7291853 = 2734445) B2734445
theorem B4861235 : Blo 1919435 4861235 := bstep (se 1 (by rfl) ⟨3645926, by rfl⟩ : syracuseStep 4861235 = 7291853) B7291853
theorem B3240823 : Blo 1919435 3240823 := bstep (se 1 (by rfl) ⟨2430617, by rfl⟩ : syracuseStep 3240823 = 4861235) B4861235
theorem B4321097 : Blo 1919435 4321097 := bstep (se 2 (by rfl) ⟨1620411, by rfl⟩ : syracuseStep 4321097 = 3240823) B3240823
theorem B2880731 : Blo 1919435 2880731 := bstep (se 1 (by rfl) ⟨2160548, by rfl⟩ : syracuseStep 2880731 = 4321097) B4321097
theorem B1920487 : Blo 1919435 1920487 := bstep (se 1 (by rfl) ⟨1440365, by rfl⟩ : syracuseStep 1920487 = 2880731) B2880731
theorem B2160553 : Blo 1919435 2160553 := bbase (se 2 (by rfl) ⟨810207, by rfl⟩ : syracuseStep 2160553 = 1620415) (by norm_num)
theorem B2880737 : Blo 1919435 2880737 := bstep (se 2 (by rfl) ⟨1080276, by rfl⟩ : syracuseStep 2880737 = 2160553) B2160553
theorem B1920491 : Blo 1919435 1920491 := bstep (se 1 (by rfl) ⟨1440368, by rfl⟩ : syracuseStep 1920491 = 2880737) B2880737
theorem B6659749 : Blo 1919435 6659749 := bbase (se 4 (by rfl) ⟨624351, by rfl⟩ : syracuseStep 6659749 = 1248703) (by norm_num)
theorem B8879665 : Blo 1919435 8879665 := bstep (se 2 (by rfl) ⟨3329874, by rfl⟩ : syracuseStep 8879665 = 6659749) B6659749
theorem B11839553 : Blo 1919435 11839553 := bstep (se 2 (by rfl) ⟨4439832, by rfl⟩ : syracuseStep 11839553 = 8879665) B8879665
theorem B7893035 : Blo 1919435 7893035 := bstep (se 1 (by rfl) ⟨5919776, by rfl⟩ : syracuseStep 7893035 = 11839553) B11839553
theorem B5262023 : Blo 1919435 5262023 := bstep (se 1 (by rfl) ⟨3946517, by rfl⟩ : syracuseStep 5262023 = 7893035) B7893035
theorem B3508015 : Blo 1919435 3508015 := bstep (se 1 (by rfl) ⟨2631011, by rfl⟩ : syracuseStep 3508015 = 5262023) B5262023
theorem B4677353 : Blo 1919435 4677353 := bstep (se 2 (by rfl) ⟨1754007, by rfl⟩ : syracuseStep 4677353 = 3508015) B3508015
theorem B3118235 : Blo 1919435 3118235 := bstep (se 1 (by rfl) ⟨2338676, by rfl⟩ : syracuseStep 3118235 = 4677353) B4677353
theorem B8315293 : Blo 1919435 8315293 := bstep (se 3 (by rfl) ⟨1559117, by rfl⟩ : syracuseStep 8315293 = 3118235) B3118235
theorem B11087057 : Blo 1919435 11087057 := bstep (se 2 (by rfl) ⟨4157646, by rfl⟩ : syracuseStep 11087057 = 8315293) B8315293
theorem B29565485 : Blo 1919435 29565485 := bstep (se 3 (by rfl) ⟨5543528, by rfl⟩ : syracuseStep 29565485 = 11087057) B11087057
theorem B19710323 : Blo 1919435 19710323 := bstep (se 1 (by rfl) ⟨14782742, by rfl⟩ : syracuseStep 19710323 = 29565485) B29565485
theorem B13140215 : Blo 1919435 13140215 := bstep (se 1 (by rfl) ⟨9855161, by rfl⟩ : syracuseStep 13140215 = 19710323) B19710323
theorem B8760143 : Blo 1919435 8760143 := bstep (se 1 (by rfl) ⟨6570107, by rfl⟩ : syracuseStep 8760143 = 13140215) B13140215
theorem B5840095 : Blo 1919435 5840095 := bstep (se 1 (by rfl) ⟨4380071, by rfl⟩ : syracuseStep 5840095 = 8760143) B8760143
theorem B7786793 : Blo 1919435 7786793 := bstep (se 2 (by rfl) ⟨2920047, by rfl⟩ : syracuseStep 7786793 = 5840095) B5840095
theorem B20764781 : Blo 1919435 20764781 := bstep (se 3 (by rfl) ⟨3893396, by rfl⟩ : syracuseStep 20764781 = 7786793) B7786793
theorem B13843187 : Blo 1919435 13843187 := bstep (se 1 (by rfl) ⟨10382390, by rfl⟩ : syracuseStep 13843187 = 20764781) B20764781
theorem B9228791 : Blo 1919435 9228791 := bstep (se 1 (by rfl) ⟨6921593, by rfl⟩ : syracuseStep 9228791 = 13843187) B13843187
theorem B6152527 : Blo 1919435 6152527 := bstep (se 1 (by rfl) ⟨4614395, by rfl⟩ : syracuseStep 6152527 = 9228791) B9228791
theorem B8203369 : Blo 1919435 8203369 := bstep (se 2 (by rfl) ⟨3076263, by rfl⟩ : syracuseStep 8203369 = 6152527) B6152527
theorem B10937825 : Blo 1919435 10937825 := bstep (se 2 (by rfl) ⟨4101684, by rfl⟩ : syracuseStep 10937825 = 8203369) B8203369
theorem B7291883 : Blo 1919435 7291883 := bstep (se 1 (by rfl) ⟨5468912, by rfl⟩ : syracuseStep 7291883 = 10937825) B10937825
theorem B4861255 : Blo 1919435 4861255 := bstep (se 1 (by rfl) ⟨3645941, by rfl⟩ : syracuseStep 4861255 = 7291883) B7291883
theorem B6481673 : Blo 1919435 6481673 := bstep (se 2 (by rfl) ⟨2430627, by rfl⟩ : syracuseStep 6481673 = 4861255) B4861255
theorem B4321115 : Blo 1919435 4321115 := bstep (se 1 (by rfl) ⟨3240836, by rfl⟩ : syracuseStep 4321115 = 6481673) B6481673
theorem B2880743 : Blo 1919435 2880743 := bstep (se 1 (by rfl) ⟨2160557, by rfl⟩ : syracuseStep 2880743 = 4321115) B4321115
theorem B1920495 : Blo 1919435 1920495 := bstep (se 1 (by rfl) ⟨1440371, by rfl⟩ : syracuseStep 1920495 = 2880743) B2880743
theorem B2880749 : Blo 1919435 2880749 := bbase (se 3 (by rfl) ⟨540140, by rfl⟩ : syracuseStep 2880749 = 1080281) (by norm_num)
theorem B1920499 : Blo 1919435 1920499 := bstep (se 1 (by rfl) ⟨1440374, by rfl⟩ : syracuseStep 1920499 = 2880749) B2880749
theorem B4321133 : Blo 1919435 4321133 := bbase (se 3 (by rfl) ⟨810212, by rfl⟩ : syracuseStep 4321133 = 1620425) (by norm_num)
theorem B2880755 : Blo 1919435 2880755 := bstep (se 1 (by rfl) ⟨2160566, by rfl⟩ : syracuseStep 2880755 = 4321133) B4321133
theorem B1920503 : Blo 1919435 1920503 := bstep (se 1 (by rfl) ⟨1440377, by rfl⟩ : syracuseStep 1920503 = 2880755) B2880755
theorem B3645965 : Blo 1919435 3645965 := bbase (se 3 (by rfl) ⟨683618, by rfl⟩ : syracuseStep 3645965 = 1367237) (by norm_num)
theorem B2430643 : Blo 1919435 2430643 := bstep (se 1 (by rfl) ⟨1822982, by rfl⟩ : syracuseStep 2430643 = 3645965) B3645965
theorem B3240857 : Blo 1919435 3240857 := bstep (se 2 (by rfl) ⟨1215321, by rfl⟩ : syracuseStep 3240857 = 2430643) B2430643
theorem B2160571 : Blo 1919435 2160571 := bstep (se 1 (by rfl) ⟨1620428, by rfl⟩ : syracuseStep 2160571 = 3240857) B3240857
theorem B2880761 : Blo 1919435 2880761 := bstep (se 2 (by rfl) ⟨1080285, by rfl⟩ : syracuseStep 2880761 = 2160571) B2160571
theorem B1920507 : Blo 1919435 1920507 := bstep (se 1 (by rfl) ⟨1440380, by rfl⟩ : syracuseStep 1920507 = 2880761) B2880761
theorem B3893429 : Blo 1919435 3893429 := bbase (se 5 (by rfl) ⟨182504, by rfl⟩ : syracuseStep 3893429 = 365009) (by norm_num)
theorem B2595619 : Blo 1919435 2595619 := bstep (se 1 (by rfl) ⟨1946714, by rfl⟩ : syracuseStep 2595619 = 3893429) B3893429
theorem B3460825 : Blo 1919435 3460825 := bstep (se 2 (by rfl) ⟨1297809, by rfl⟩ : syracuseStep 3460825 = 2595619) B2595619
theorem B18457733 : Blo 1919435 18457733 := bstep (se 4 (by rfl) ⟨1730412, by rfl⟩ : syracuseStep 18457733 = 3460825) B3460825
theorem B49220621 : Blo 1919435 49220621 := bstep (se 3 (by rfl) ⟨9228866, by rfl⟩ : syracuseStep 49220621 = 18457733) B18457733
theorem B32813747 : Blo 1919435 32813747 := bstep (se 1 (by rfl) ⟨24610310, by rfl⟩ : syracuseStep 32813747 = 49220621) B49220621
theorem B21875831 : Blo 1919435 21875831 := bstep (se 1 (by rfl) ⟨16406873, by rfl⟩ : syracuseStep 21875831 = 32813747) B32813747
theorem B14583887 : Blo 1919435 14583887 := bstep (se 1 (by rfl) ⟨10937915, by rfl⟩ : syracuseStep 14583887 = 21875831) B21875831
theorem B9722591 : Blo 1919435 9722591 := bstep (se 1 (by rfl) ⟨7291943, by rfl⟩ : syracuseStep 9722591 = 14583887) B14583887
theorem B6481727 : Blo 1919435 6481727 := bstep (se 1 (by rfl) ⟨4861295, by rfl⟩ : syracuseStep 6481727 = 9722591) B9722591
theorem B4321151 : Blo 1919435 4321151 := bstep (se 1 (by rfl) ⟨3240863, by rfl⟩ : syracuseStep 4321151 = 6481727) B6481727
theorem B2880767 : Blo 1919435 2880767 := bstep (se 1 (by rfl) ⟨2160575, by rfl⟩ : syracuseStep 2880767 = 4321151) B4321151
theorem B1920511 : Blo 1919435 1920511 := bstep (se 1 (by rfl) ⟨1440383, by rfl⟩ : syracuseStep 1920511 = 2880767) B2880767
theorem B2880773 : Blo 1919435 2880773 := bbase (se 4 (by rfl) ⟨270072, by rfl⟩ : syracuseStep 2880773 = 540145) (by norm_num)
theorem B1920515 : Blo 1919435 1920515 := bstep (se 1 (by rfl) ⟨1440386, by rfl⟩ : syracuseStep 1920515 = 2880773) B2880773
theorem B3240877 : Blo 1919435 3240877 := bbase (se 3 (by rfl) ⟨607664, by rfl⟩ : syracuseStep 3240877 = 1215329) (by norm_num)
theorem B4321169 : Blo 1919435 4321169 := bstep (se 2 (by rfl) ⟨1620438, by rfl⟩ : syracuseStep 4321169 = 3240877) B3240877
theorem B2880779 : Blo 1919435 2880779 := bstep (se 1 (by rfl) ⟨2160584, by rfl⟩ : syracuseStep 2880779 = 4321169) B4321169
theorem B1920519 : Blo 1919435 1920519 := bstep (se 1 (by rfl) ⟨1440389, by rfl⟩ : syracuseStep 1920519 = 2880779) B2880779
theorem B2160589 : Blo 1919435 2160589 := bbase (se 3 (by rfl) ⟨405110, by rfl⟩ : syracuseStep 2160589 = 810221) (by norm_num)
theorem B2880785 : Blo 1919435 2880785 := bstep (se 2 (by rfl) ⟨1080294, by rfl⟩ : syracuseStep 2880785 = 2160589) B2160589
theorem B1920523 : Blo 1919435 1920523 := bstep (se 1 (by rfl) ⟨1440392, by rfl⟩ : syracuseStep 1920523 = 2880785) B2880785
theorem B6481781 : Blo 1919435 6481781 := bbase (se 5 (by rfl) ⟨303833, by rfl⟩ : syracuseStep 6481781 = 607667) (by norm_num)
theorem B4321187 : Blo 1919435 4321187 := bstep (se 1 (by rfl) ⟨3240890, by rfl⟩ : syracuseStep 4321187 = 6481781) B6481781
theorem B2880791 : Blo 1919435 2880791 := bstep (se 1 (by rfl) ⟨2160593, by rfl⟩ : syracuseStep 2880791 = 4321187) B4321187
theorem B1920527 : Blo 1919435 1920527 := bstep (se 1 (by rfl) ⟨1440395, by rfl⟩ : syracuseStep 1920527 = 2880791) B2880791
theorem B2880797 : Blo 1919435 2880797 := bbase (se 3 (by rfl) ⟨540149, by rfl⟩ : syracuseStep 2880797 = 1080299) (by norm_num)
theorem B1920531 : Blo 1919435 1920531 := bstep (se 1 (by rfl) ⟨1440398, by rfl⟩ : syracuseStep 1920531 = 2880797) B2880797
theorem B4321205 : Blo 1919435 4321205 := bbase (se 5 (by rfl) ⟨202556, by rfl⟩ : syracuseStep 4321205 = 405113) (by norm_num)
theorem B2880803 : Blo 1919435 2880803 := bstep (se 1 (by rfl) ⟨2160602, by rfl⟩ : syracuseStep 2880803 = 4321205) B4321205
theorem B1920535 : Blo 1919435 1920535 := bstep (se 1 (by rfl) ⟨1440401, by rfl⟩ : syracuseStep 1920535 = 2880803) B2880803
theorem B3460877 : Blo 1919435 3460877 := bbase (se 3 (by rfl) ⟨648914, by rfl⟩ : syracuseStep 3460877 = 1297829) (by norm_num)
theorem B2307251 : Blo 1919435 2307251 := bstep (se 1 (by rfl) ⟨1730438, by rfl⟩ : syracuseStep 2307251 = 3460877) B3460877
theorem B6152669 : Blo 1919435 6152669 := bstep (se 3 (by rfl) ⟨1153625, by rfl⟩ : syracuseStep 6152669 = 2307251) B2307251
theorem B4101779 : Blo 1919435 4101779 := bstep (se 1 (by rfl) ⟨3076334, by rfl⟩ : syracuseStep 4101779 = 6152669) B6152669
theorem B10938077 : Blo 1919435 10938077 := bstep (se 3 (by rfl) ⟨2050889, by rfl⟩ : syracuseStep 10938077 = 4101779) B4101779
theorem B7292051 : Blo 1919435 7292051 := bstep (se 1 (by rfl) ⟨5469038, by rfl⟩ : syracuseStep 7292051 = 10938077) B10938077
theorem B4861367 : Blo 1919435 4861367 := bstep (se 1 (by rfl) ⟨3646025, by rfl⟩ : syracuseStep 4861367 = 7292051) B7292051
theorem B3240911 : Blo 1919435 3240911 := bstep (se 1 (by rfl) ⟨2430683, by rfl⟩ : syracuseStep 3240911 = 4861367) B4861367
theorem B2160607 : Blo 1919435 2160607 := bstep (se 1 (by rfl) ⟨1620455, by rfl⟩ : syracuseStep 2160607 = 3240911) B3240911
theorem B2880809 : Blo 1919435 2880809 := bstep (se 2 (by rfl) ⟨1080303, by rfl⟩ : syracuseStep 2880809 = 2160607) B2160607
theorem B1920539 : Blo 1919435 1920539 := bstep (se 1 (by rfl) ⟨1440404, by rfl⟩ : syracuseStep 1920539 = 2880809) B2880809
theorem B17520725 : Blo 1919435 17520725 := bbase (se 8 (by rfl) ⟨102660, by rfl⟩ : syracuseStep 17520725 = 205321) (by norm_num)
theorem B11680483 : Blo 1919435 11680483 := bstep (se 1 (by rfl) ⟨8760362, by rfl⟩ : syracuseStep 11680483 = 17520725) B17520725
theorem B15573977 : Blo 1919435 15573977 := bstep (se 2 (by rfl) ⟨5840241, by rfl⟩ : syracuseStep 15573977 = 11680483) B11680483
theorem B10382651 : Blo 1919435 10382651 := bstep (se 1 (by rfl) ⟨7786988, by rfl⟩ : syracuseStep 10382651 = 15573977) B15573977
theorem B6921767 : Blo 1919435 6921767 := bstep (se 1 (by rfl) ⟨5191325, by rfl⟩ : syracuseStep 6921767 = 10382651) B10382651
theorem B4614511 : Blo 1919435 4614511 := bstep (se 1 (by rfl) ⟨3460883, by rfl⟩ : syracuseStep 4614511 = 6921767) B6921767
theorem B6152681 : Blo 1919435 6152681 := bstep (se 2 (by rfl) ⟨2307255, by rfl⟩ : syracuseStep 6152681 = 4614511) B4614511
theorem B4101787 : Blo 1919435 4101787 := bstep (se 1 (by rfl) ⟨3076340, by rfl⟩ : syracuseStep 4101787 = 6152681) B6152681
theorem B5469049 : Blo 1919435 5469049 := bstep (se 2 (by rfl) ⟨2050893, by rfl⟩ : syracuseStep 5469049 = 4101787) B4101787
theorem B7292065 : Blo 1919435 7292065 := bstep (se 2 (by rfl) ⟨2734524, by rfl⟩ : syracuseStep 7292065 = 5469049) B5469049
theorem B9722753 : Blo 1919435 9722753 := bstep (se 2 (by rfl) ⟨3646032, by rfl⟩ : syracuseStep 9722753 = 7292065) B7292065
theorem B6481835 : Blo 1919435 6481835 := bstep (se 1 (by rfl) ⟨4861376, by rfl⟩ : syracuseStep 6481835 = 9722753) B9722753
theorem B4321223 : Blo 1919435 4321223 := bstep (se 1 (by rfl) ⟨3240917, by rfl⟩ : syracuseStep 4321223 = 6481835) B6481835
theorem B2880815 : Blo 1919435 2880815 := bstep (se 1 (by rfl) ⟨2160611, by rfl⟩ : syracuseStep 2880815 = 4321223) B4321223
theorem B1920543 : Blo 1919435 1920543 := bstep (se 1 (by rfl) ⟨1440407, by rfl⟩ : syracuseStep 1920543 = 2880815) B2880815
theorem B2880821 : Blo 1919435 2880821 := bbase (se 5 (by rfl) ⟨135038, by rfl⟩ : syracuseStep 2880821 = 270077) (by norm_num)
theorem B1920547 : Blo 1919435 1920547 := bstep (se 1 (by rfl) ⟨1440410, by rfl⟩ : syracuseStep 1920547 = 2880821) B2880821
theorem B4861397 : Blo 1919435 4861397 := bbase (se 7 (by rfl) ⟨56969, by rfl⟩ : syracuseStep 4861397 = 113939) (by norm_num)
theorem B3240931 : Blo 1919435 3240931 := bstep (se 1 (by rfl) ⟨2430698, by rfl⟩ : syracuseStep 3240931 = 4861397) B4861397
theorem B4321241 : Blo 1919435 4321241 := bstep (se 2 (by rfl) ⟨1620465, by rfl⟩ : syracuseStep 4321241 = 3240931) B3240931
theorem B2880827 : Blo 1919435 2880827 := bstep (se 1 (by rfl) ⟨2160620, by rfl⟩ : syracuseStep 2880827 = 4321241) B4321241
theorem B1920551 : Blo 1919435 1920551 := bstep (se 1 (by rfl) ⟨1440413, by rfl⟩ : syracuseStep 1920551 = 2880827) B2880827
theorem B2160625 : Blo 1919435 2160625 := bbase (se 2 (by rfl) ⟨810234, by rfl⟩ : syracuseStep 2160625 = 1620469) (by norm_num)
theorem B2880833 : Blo 1919435 2880833 := bstep (se 2 (by rfl) ⟨1080312, by rfl⟩ : syracuseStep 2880833 = 2160625) B2160625
theorem B1920555 : Blo 1919435 1920555 := bstep (se 1 (by rfl) ⟨1440416, by rfl⟩ : syracuseStep 1920555 = 2880833) B2880833
theorem B2190109 : Blo 1919435 2190109 := bbase (se 3 (by rfl) ⟨410645, by rfl⟩ : syracuseStep 2190109 = 821291) (by norm_num)
theorem B2920145 : Blo 1919435 2920145 := bstep (se 2 (by rfl) ⟨1095054, by rfl⟩ : syracuseStep 2920145 = 2190109) B2190109
theorem B7787053 : Blo 1919435 7787053 := bstep (se 3 (by rfl) ⟨1460072, by rfl⟩ : syracuseStep 7787053 = 2920145) B2920145
theorem B10382737 : Blo 1919435 10382737 := bstep (se 2 (by rfl) ⟨3893526, by rfl⟩ : syracuseStep 10382737 = 7787053) B7787053
theorem B13843649 : Blo 1919435 13843649 := bstep (se 2 (by rfl) ⟨5191368, by rfl⟩ : syracuseStep 13843649 = 10382737) B10382737
theorem B9229099 : Blo 1919435 9229099 := bstep (se 1 (by rfl) ⟨6921824, by rfl⟩ : syracuseStep 9229099 = 13843649) B13843649
theorem B12305465 : Blo 1919435 12305465 := bstep (se 2 (by rfl) ⟨4614549, by rfl⟩ : syracuseStep 12305465 = 9229099) B9229099
theorem B8203643 : Blo 1919435 8203643 := bstep (se 1 (by rfl) ⟨6152732, by rfl⟩ : syracuseStep 8203643 = 12305465) B12305465
theorem B5469095 : Blo 1919435 5469095 := bstep (se 1 (by rfl) ⟨4101821, by rfl⟩ : syracuseStep 5469095 = 8203643) B8203643
theorem B3646063 : Blo 1919435 3646063 := bstep (se 1 (by rfl) ⟨2734547, by rfl⟩ : syracuseStep 3646063 = 5469095) B5469095
theorem B4861417 : Blo 1919435 4861417 := bstep (se 2 (by rfl) ⟨1823031, by rfl⟩ : syracuseStep 4861417 = 3646063) B3646063
theorem B6481889 : Blo 1919435 6481889 := bstep (se 2 (by rfl) ⟨2430708, by rfl⟩ : syracuseStep 6481889 = 4861417) B4861417
theorem B4321259 : Blo 1919435 4321259 := bstep (se 1 (by rfl) ⟨3240944, by rfl⟩ : syracuseStep 4321259 = 6481889) B6481889
theorem B2880839 : Blo 1919435 2880839 := bstep (se 1 (by rfl) ⟨2160629, by rfl⟩ : syracuseStep 2880839 = 4321259) B4321259
theorem B1920559 : Blo 1919435 1920559 := bstep (se 1 (by rfl) ⟨1440419, by rfl⟩ : syracuseStep 1920559 = 2880839) B2880839
theorem B2880845 : Blo 1919435 2880845 := bbase (se 3 (by rfl) ⟨540158, by rfl⟩ : syracuseStep 2880845 = 1080317) (by norm_num)
theorem B1920563 : Blo 1919435 1920563 := bstep (se 1 (by rfl) ⟨1440422, by rfl⟩ : syracuseStep 1920563 = 2880845) B2880845
theorem B4321277 : Blo 1919435 4321277 := bbase (se 3 (by rfl) ⟨810239, by rfl⟩ : syracuseStep 4321277 = 1620479) (by norm_num)
theorem B2880851 : Blo 1919435 2880851 := bstep (se 1 (by rfl) ⟨2160638, by rfl⟩ : syracuseStep 2880851 = 4321277) B4321277
theorem B1920567 : Blo 1919435 1920567 := bstep (se 1 (by rfl) ⟨1440425, by rfl⟩ : syracuseStep 1920567 = 2880851) B2880851
theorem B3240965 : Blo 1919435 3240965 := bbase (se 4 (by rfl) ⟨303840, by rfl⟩ : syracuseStep 3240965 = 607681) (by norm_num)
theorem B2160643 : Blo 1919435 2160643 := bstep (se 1 (by rfl) ⟨1620482, by rfl⟩ : syracuseStep 2160643 = 3240965) B3240965
theorem B2880857 : Blo 1919435 2880857 := bstep (se 2 (by rfl) ⟨1080321, by rfl⟩ : syracuseStep 2880857 = 2160643) B2160643
theorem B1920571 : Blo 1919435 1920571 := bstep (se 1 (by rfl) ⟨1440428, by rfl⟩ : syracuseStep 1920571 = 2880857) B2880857
theorem B14584373 : Blo 1919435 14584373 := bbase (se 5 (by rfl) ⟨683642, by rfl⟩ : syracuseStep 14584373 = 1367285) (by norm_num)
theorem B9722915 : Blo 1919435 9722915 := bstep (se 1 (by rfl) ⟨7292186, by rfl⟩ : syracuseStep 9722915 = 14584373) B14584373
theorem B6481943 : Blo 1919435 6481943 := bstep (se 1 (by rfl) ⟨4861457, by rfl⟩ : syracuseStep 6481943 = 9722915) B9722915
theorem B4321295 : Blo 1919435 4321295 := bstep (se 1 (by rfl) ⟨3240971, by rfl⟩ : syracuseStep 4321295 = 6481943) B6481943
theorem B2880863 : Blo 1919435 2880863 := bstep (se 1 (by rfl) ⟨2160647, by rfl⟩ : syracuseStep 2880863 = 4321295) B4321295
theorem B1920575 : Blo 1919435 1920575 := bstep (se 1 (by rfl) ⟨1440431, by rfl⟩ : syracuseStep 1920575 = 2880863) B2880863
theorem B2880869 : Blo 1919435 2880869 := bbase (se 4 (by rfl) ⟨270081, by rfl⟩ : syracuseStep 2880869 = 540163) (by norm_num)
theorem B1920579 : Blo 1919435 1920579 := bstep (se 1 (by rfl) ⟨1440434, by rfl⟩ : syracuseStep 1920579 = 2880869) B2880869
theorem B3646109 : Blo 1919435 3646109 := bbase (se 3 (by rfl) ⟨683645, by rfl⟩ : syracuseStep 3646109 = 1367291) (by norm_num)
theorem B2430739 : Blo 1919435 2430739 := bstep (se 1 (by rfl) ⟨1823054, by rfl⟩ : syracuseStep 2430739 = 3646109) B3646109
theorem B3240985 : Blo 1919435 3240985 := bstep (se 2 (by rfl) ⟨1215369, by rfl⟩ : syracuseStep 3240985 = 2430739) B2430739
theorem B4321313 : Blo 1919435 4321313 := bstep (se 2 (by rfl) ⟨1620492, by rfl⟩ : syracuseStep 4321313 = 3240985) B3240985
theorem B2880875 : Blo 1919435 2880875 := bstep (se 1 (by rfl) ⟨2160656, by rfl⟩ : syracuseStep 2880875 = 4321313) B4321313
theorem B1920583 : Blo 1919435 1920583 := bstep (se 1 (by rfl) ⟨1440437, by rfl⟩ : syracuseStep 1920583 = 2880875) B2880875
theorem B2160661 : Blo 1919435 2160661 := bbase (se 6 (by rfl) ⟨50640, by rfl⟩ : syracuseStep 2160661 = 101281) (by norm_num)
theorem B2880881 : Blo 1919435 2880881 := bstep (se 2 (by rfl) ⟨1080330, by rfl⟩ : syracuseStep 2880881 = 2160661) B2160661
theorem B1920587 : Blo 1919435 1920587 := bstep (se 1 (by rfl) ⟨1440440, by rfl⟩ : syracuseStep 1920587 = 2880881) B2880881
theorem B2430749 : Blo 1919435 2430749 := bbase (se 3 (by rfl) ⟨455765, by rfl⟩ : syracuseStep 2430749 = 911531) (by norm_num)
theorem B6481997 : Blo 1919435 6481997 := bstep (se 3 (by rfl) ⟨1215374, by rfl⟩ : syracuseStep 6481997 = 2430749) B2430749
theorem B4321331 : Blo 1919435 4321331 := bstep (se 1 (by rfl) ⟨3240998, by rfl⟩ : syracuseStep 4321331 = 6481997) B6481997
theorem B2880887 : Blo 1919435 2880887 := bstep (se 1 (by rfl) ⟨2160665, by rfl⟩ : syracuseStep 2880887 = 4321331) B4321331
theorem B1920591 : Blo 1919435 1920591 := bstep (se 1 (by rfl) ⟨1440443, by rfl⟩ : syracuseStep 1920591 = 2880887) B2880887
theorem B2880893 : Blo 1919435 2880893 := bbase (se 3 (by rfl) ⟨540167, by rfl⟩ : syracuseStep 2880893 = 1080335) (by norm_num)
theorem B1920595 : Blo 1919435 1920595 := bstep (se 1 (by rfl) ⟨1440446, by rfl⟩ : syracuseStep 1920595 = 2880893) B2880893
theorem B4321349 : Blo 1919435 4321349 := bbase (se 4 (by rfl) ⟨405126, by rfl⟩ : syracuseStep 4321349 = 810253) (by norm_num)
theorem B2880899 : Blo 1919435 2880899 := bstep (se 1 (by rfl) ⟨2160674, by rfl⟩ : syracuseStep 2880899 = 4321349) B4321349
theorem B1920599 : Blo 1919435 1920599 := bstep (se 1 (by rfl) ⟨1440449, by rfl⟩ : syracuseStep 1920599 = 2880899) B2880899
theorem B5469221 : Blo 1919435 5469221 := bbase (se 4 (by rfl) ⟨512739, by rfl⟩ : syracuseStep 5469221 = 1025479) (by norm_num)
theorem B3646147 : Blo 1919435 3646147 := bstep (se 1 (by rfl) ⟨2734610, by rfl⟩ : syracuseStep 3646147 = 5469221) B5469221
theorem B4861529 : Blo 1919435 4861529 := bstep (se 2 (by rfl) ⟨1823073, by rfl⟩ : syracuseStep 4861529 = 3646147) B3646147
theorem B3241019 : Blo 1919435 3241019 := bstep (se 1 (by rfl) ⟨2430764, by rfl⟩ : syracuseStep 3241019 = 4861529) B4861529
theorem B2160679 : Blo 1919435 2160679 := bstep (se 1 (by rfl) ⟨1620509, by rfl⟩ : syracuseStep 2160679 = 3241019) B3241019
theorem B2880905 : Blo 1919435 2880905 := bstep (se 2 (by rfl) ⟨1080339, by rfl⟩ : syracuseStep 2880905 = 2160679) B2160679
theorem B1920603 : Blo 1919435 1920603 := bstep (se 1 (by rfl) ⟨1440452, by rfl⟩ : syracuseStep 1920603 = 2880905) B2880905
theorem B9723077 : Blo 1919435 9723077 := bbase (se 4 (by rfl) ⟨911538, by rfl⟩ : syracuseStep 9723077 = 1823077) (by norm_num)
theorem B6482051 : Blo 1919435 6482051 := bstep (se 1 (by rfl) ⟨4861538, by rfl⟩ : syracuseStep 6482051 = 9723077) B9723077
theorem B4321367 : Blo 1919435 4321367 := bstep (se 1 (by rfl) ⟨3241025, by rfl⟩ : syracuseStep 4321367 = 6482051) B6482051
theorem B2880911 : Blo 1919435 2880911 := bstep (se 1 (by rfl) ⟨2160683, by rfl⟩ : syracuseStep 2880911 = 4321367) B4321367
theorem B1920607 : Blo 1919435 1920607 := bstep (se 1 (by rfl) ⟨1440455, by rfl⟩ : syracuseStep 1920607 = 2880911) B2880911
theorem B2880917 : Blo 1919435 2880917 := bbase (se 6 (by rfl) ⟨67521, by rfl⟩ : syracuseStep 2880917 = 135043) (by norm_num)
theorem B1920611 : Blo 1919435 1920611 := bstep (se 1 (by rfl) ⟨1440458, by rfl⟩ : syracuseStep 1920611 = 2880917) B2880917
theorem B4101941 : Blo 1919435 4101941 := bbase (se 5 (by rfl) ⟨192278, by rfl⟩ : syracuseStep 4101941 = 384557) (by norm_num)
theorem B10938509 : Blo 1919435 10938509 := bstep (se 3 (by rfl) ⟨2050970, by rfl⟩ : syracuseStep 10938509 = 4101941) B4101941
theorem B7292339 : Blo 1919435 7292339 := bstep (se 1 (by rfl) ⟨5469254, by rfl⟩ : syracuseStep 7292339 = 10938509) B10938509
theorem B4861559 : Blo 1919435 4861559 := bstep (se 1 (by rfl) ⟨3646169, by rfl⟩ : syracuseStep 4861559 = 7292339) B7292339
theorem B3241039 : Blo 1919435 3241039 := bstep (se 1 (by rfl) ⟨2430779, by rfl⟩ : syracuseStep 3241039 = 4861559) B4861559
theorem B4321385 : Blo 1919435 4321385 := bstep (se 2 (by rfl) ⟨1620519, by rfl⟩ : syracuseStep 4321385 = 3241039) B3241039
theorem B2880923 : Blo 1919435 2880923 := bstep (se 1 (by rfl) ⟨2160692, by rfl⟩ : syracuseStep 2880923 = 4321385) B4321385
theorem B1920615 : Blo 1919435 1920615 := bstep (se 1 (by rfl) ⟨1440461, by rfl⟩ : syracuseStep 1920615 = 2880923) B2880923
theorem B2160697 : Blo 1919435 2160697 := bbase (se 2 (by rfl) ⟨810261, by rfl⟩ : syracuseStep 2160697 = 1620523) (by norm_num)
theorem B2880929 : Blo 1919435 2880929 := bstep (se 2 (by rfl) ⟨1080348, by rfl⟩ : syracuseStep 2880929 = 2160697) B2160697
theorem B1920619 : Blo 1919435 1920619 := bstep (se 1 (by rfl) ⟨1440464, by rfl⟩ : syracuseStep 1920619 = 2880929) B2880929
theorem B3076469 : Blo 1919435 3076469 := bbase (se 5 (by rfl) ⟨144209, by rfl⟩ : syracuseStep 3076469 = 288419) (by norm_num)
theorem B2050979 : Blo 1919435 2050979 := bstep (se 1 (by rfl) ⟨1538234, by rfl⟩ : syracuseStep 2050979 = 3076469) B3076469
theorem B5469277 : Blo 1919435 5469277 := bstep (se 3 (by rfl) ⟨1025489, by rfl⟩ : syracuseStep 5469277 = 2050979) B2050979
theorem B7292369 : Blo 1919435 7292369 := bstep (se 2 (by rfl) ⟨2734638, by rfl⟩ : syracuseStep 7292369 = 5469277) B5469277
theorem B4861579 : Blo 1919435 4861579 := bstep (se 1 (by rfl) ⟨3646184, by rfl⟩ : syracuseStep 4861579 = 7292369) B7292369
theorem B6482105 : Blo 1919435 6482105 := bstep (se 2 (by rfl) ⟨2430789, by rfl⟩ : syracuseStep 6482105 = 4861579) B4861579
theorem B4321403 : Blo 1919435 4321403 := bstep (se 1 (by rfl) ⟨3241052, by rfl⟩ : syracuseStep 4321403 = 6482105) B6482105
theorem B2880935 : Blo 1919435 2880935 := bstep (se 1 (by rfl) ⟨2160701, by rfl⟩ : syracuseStep 2880935 = 4321403) B4321403
theorem B1920623 : Blo 1919435 1920623 := bstep (se 1 (by rfl) ⟨1440467, by rfl⟩ : syracuseStep 1920623 = 2880935) B2880935
theorem B2880941 : Blo 1919435 2880941 := bbase (se 3 (by rfl) ⟨540176, by rfl⟩ : syracuseStep 2880941 = 1080353) (by norm_num)
theorem B1920627 : Blo 1919435 1920627 := bstep (se 1 (by rfl) ⟨1440470, by rfl⟩ : syracuseStep 1920627 = 2880941) B2880941
theorem B4321421 : Blo 1919435 4321421 := bbase (se 3 (by rfl) ⟨810266, by rfl⟩ : syracuseStep 4321421 = 1620533) (by norm_num)
theorem B2880947 : Blo 1919435 2880947 := bstep (se 1 (by rfl) ⟨2160710, by rfl⟩ : syracuseStep 2880947 = 4321421) B4321421
theorem B1920631 : Blo 1919435 1920631 := bstep (se 1 (by rfl) ⟨1440473, by rfl⟩ : syracuseStep 1920631 = 2880947) B2880947
theorem B2430805 : Blo 1919435 2430805 := bbase (se 9 (by rfl) ⟨7121, by rfl⟩ : syracuseStep 2430805 = 14243) (by norm_num)
theorem B3241073 : Blo 1919435 3241073 := bstep (se 2 (by rfl) ⟨1215402, by rfl⟩ : syracuseStep 3241073 = 2430805) B2430805
theorem B2160715 : Blo 1919435 2160715 := bstep (se 1 (by rfl) ⟨1620536, by rfl⟩ : syracuseStep 2160715 = 3241073) B3241073
theorem B2880953 : Blo 1919435 2880953 := bstep (se 2 (by rfl) ⟨1080357, by rfl⟩ : syracuseStep 2880953 = 2160715) B2160715
theorem B1920635 : Blo 1919435 1920635 := bstep (se 1 (by rfl) ⟨1440476, by rfl⟩ : syracuseStep 1920635 = 2880953) B2880953
theorem B6660245 : Blo 1919435 6660245 := bbase (se 6 (by rfl) ⟨156099, by rfl⟩ : syracuseStep 6660245 = 312199) (by norm_num)
theorem B4440163 : Blo 1919435 4440163 := bstep (se 1 (by rfl) ⟨3330122, by rfl⟩ : syracuseStep 4440163 = 6660245) B6660245
theorem B5920217 : Blo 1919435 5920217 := bstep (se 2 (by rfl) ⟨2220081, by rfl⟩ : syracuseStep 5920217 = 4440163) B4440163
theorem B3946811 : Blo 1919435 3946811 := bstep (se 1 (by rfl) ⟨2960108, by rfl⟩ : syracuseStep 3946811 = 5920217) B5920217
theorem B10524829 : Blo 1919435 10524829 := bstep (se 3 (by rfl) ⟨1973405, by rfl⟩ : syracuseStep 10524829 = 3946811) B3946811
theorem B14033105 : Blo 1919435 14033105 := bstep (se 2 (by rfl) ⟨5262414, by rfl⟩ : syracuseStep 14033105 = 10524829) B10524829
theorem B9355403 : Blo 1919435 9355403 := bstep (se 1 (by rfl) ⟨7016552, by rfl⟩ : syracuseStep 9355403 = 14033105) B14033105
theorem B6236935 : Blo 1919435 6236935 := bstep (se 1 (by rfl) ⟨4677701, by rfl⟩ : syracuseStep 6236935 = 9355403) B9355403
theorem B133054613 : Blo 1919435 133054613 := bstep (se 6 (by rfl) ⟨3118467, by rfl⟩ : syracuseStep 133054613 = 6236935) B6236935
theorem B88703075 : Blo 1919435 88703075 := bstep (se 1 (by rfl) ⟨66527306, by rfl⟩ : syracuseStep 88703075 = 133054613) B133054613
theorem B59135383 : Blo 1919435 59135383 := bstep (se 1 (by rfl) ⟨44351537, by rfl⟩ : syracuseStep 59135383 = 88703075) B88703075
theorem B78847177 : Blo 1919435 78847177 := bstep (se 2 (by rfl) ⟨29567691, by rfl⟩ : syracuseStep 78847177 = 59135383) B59135383
theorem B105129569 : Blo 1919435 105129569 := bstep (se 2 (by rfl) ⟨39423588, by rfl⟩ : syracuseStep 105129569 = 78847177) B78847177
theorem B70086379 : Blo 1919435 70086379 := bstep (se 1 (by rfl) ⟨52564784, by rfl⟩ : syracuseStep 70086379 = 105129569) B105129569
theorem B93448505 : Blo 1919435 93448505 := bstep (se 2 (by rfl) ⟨35043189, by rfl⟩ : syracuseStep 93448505 = 70086379) B70086379
theorem B62299003 : Blo 1919435 62299003 := bstep (se 1 (by rfl) ⟨46724252, by rfl⟩ : syracuseStep 62299003 = 93448505) B93448505
theorem B83065337 : Blo 1919435 83065337 := bstep (se 2 (by rfl) ⟨31149501, by rfl⟩ : syracuseStep 83065337 = 62299003) B62299003
theorem B55376891 : Blo 1919435 55376891 := bstep (se 1 (by rfl) ⟨41532668, by rfl⟩ : syracuseStep 55376891 = 83065337) B83065337
theorem B36917927 : Blo 1919435 36917927 := bstep (se 1 (by rfl) ⟨27688445, by rfl⟩ : syracuseStep 36917927 = 55376891) B55376891
theorem B24611951 : Blo 1919435 24611951 := bstep (se 1 (by rfl) ⟨18458963, by rfl⟩ : syracuseStep 24611951 = 36917927) B36917927
theorem B16407967 : Blo 1919435 16407967 := bstep (se 1 (by rfl) ⟨12305975, by rfl⟩ : syracuseStep 16407967 = 24611951) B24611951
theorem B21877289 : Blo 1919435 21877289 := bstep (se 2 (by rfl) ⟨8203983, by rfl⟩ : syracuseStep 21877289 = 16407967) B16407967
theorem B14584859 : Blo 1919435 14584859 := bstep (se 1 (by rfl) ⟨10938644, by rfl⟩ : syracuseStep 14584859 = 21877289) B21877289
theorem B9723239 : Blo 1919435 9723239 := bstep (se 1 (by rfl) ⟨7292429, by rfl⟩ : syracuseStep 9723239 = 14584859) B14584859
theorem B6482159 : Blo 1919435 6482159 := bstep (se 1 (by rfl) ⟨4861619, by rfl⟩ : syracuseStep 6482159 = 9723239) B9723239
theorem B4321439 : Blo 1919435 4321439 := bstep (se 1 (by rfl) ⟨3241079, by rfl⟩ : syracuseStep 4321439 = 6482159) B6482159
theorem B2880959 : Blo 1919435 2880959 := bstep (se 1 (by rfl) ⟨2160719, by rfl⟩ : syracuseStep 2880959 = 4321439) B4321439
theorem B1920639 : Blo 1919435 1920639 := bstep (se 1 (by rfl) ⟨1440479, by rfl⟩ : syracuseStep 1920639 = 2880959) B2880959
theorem B2880965 : Blo 1919435 2880965 := bbase (se 4 (by rfl) ⟨270090, by rfl⟩ : syracuseStep 2880965 = 540181) (by norm_num)
theorem B1920643 : Blo 1919435 1920643 := bstep (se 1 (by rfl) ⟨1440482, by rfl⟩ : syracuseStep 1920643 = 2880965) B2880965
theorem B3241093 : Blo 1919435 3241093 := bbase (se 4 (by rfl) ⟨303852, by rfl⟩ : syracuseStep 3241093 = 607705) (by norm_num)
theorem B4321457 : Blo 1919435 4321457 := bstep (se 2 (by rfl) ⟨1620546, by rfl⟩ : syracuseStep 4321457 = 3241093) B3241093
theorem B2880971 : Blo 1919435 2880971 := bstep (se 1 (by rfl) ⟨2160728, by rfl⟩ : syracuseStep 2880971 = 4321457) B4321457
theorem B1920647 : Blo 1919435 1920647 := bstep (se 1 (by rfl) ⟨1440485, by rfl⟩ : syracuseStep 1920647 = 2880971) B2880971
theorem B2160733 : Blo 1919435 2160733 := bbase (se 3 (by rfl) ⟨405137, by rfl⟩ : syracuseStep 2160733 = 810275) (by norm_num)
theorem B2880977 : Blo 1919435 2880977 := bstep (se 2 (by rfl) ⟨1080366, by rfl⟩ : syracuseStep 2880977 = 2160733) B2160733
theorem B1920651 : Blo 1919435 1920651 := bstep (se 1 (by rfl) ⟨1440488, by rfl⟩ : syracuseStep 1920651 = 2880977) B2880977
theorem B6482213 : Blo 1919435 6482213 := bbase (se 4 (by rfl) ⟨607707, by rfl⟩ : syracuseStep 6482213 = 1215415) (by norm_num)
theorem B4321475 : Blo 1919435 4321475 := bstep (se 1 (by rfl) ⟨3241106, by rfl⟩ : syracuseStep 4321475 = 6482213) B6482213
theorem B2880983 : Blo 1919435 2880983 := bstep (se 1 (by rfl) ⟨2160737, by rfl⟩ : syracuseStep 2880983 = 4321475) B4321475
theorem B1920655 : Blo 1919435 1920655 := bstep (se 1 (by rfl) ⟨1440491, by rfl⟩ : syracuseStep 1920655 = 2880983) B2880983
theorem B2880989 : Blo 1919435 2880989 := bbase (se 3 (by rfl) ⟨540185, by rfl⟩ : syracuseStep 2880989 = 1080371) (by norm_num)
theorem B1920659 : Blo 1919435 1920659 := bstep (se 1 (by rfl) ⟨1440494, by rfl⟩ : syracuseStep 1920659 = 2880989) B2880989
theorem B4321493 : Blo 1919435 4321493 := bbase (se 7 (by rfl) ⟨50642, by rfl⟩ : syracuseStep 4321493 = 101285) (by norm_num)
theorem B2880995 : Blo 1919435 2880995 := bstep (se 1 (by rfl) ⟨2160746, by rfl⟩ : syracuseStep 2880995 = 4321493) B4321493
theorem B1920663 : Blo 1919435 1920663 := bstep (se 1 (by rfl) ⟨1440497, by rfl⟩ : syracuseStep 1920663 = 2880995) B2880995
theorem B1946873 : Blo 1919435 1946873 := bbase (se 2 (by rfl) ⟨730077, by rfl⟩ : syracuseStep 1946873 = 1460155) (by norm_num)
theorem B5191661 : Blo 1919435 5191661 := bstep (se 3 (by rfl) ⟨973436, by rfl⟩ : syracuseStep 5191661 = 1946873) B1946873
theorem B13844429 : Blo 1919435 13844429 := bstep (se 3 (by rfl) ⟨2595830, by rfl⟩ : syracuseStep 13844429 = 5191661) B5191661
theorem B9229619 : Blo 1919435 9229619 := bstep (se 1 (by rfl) ⟨6922214, by rfl⟩ : syracuseStep 9229619 = 13844429) B13844429
theorem B6153079 : Blo 1919435 6153079 := bstep (se 1 (by rfl) ⟨4614809, by rfl⟩ : syracuseStep 6153079 = 9229619) B9229619
theorem B8204105 : Blo 1919435 8204105 := bstep (se 2 (by rfl) ⟨3076539, by rfl⟩ : syracuseStep 8204105 = 6153079) B6153079
theorem B5469403 : Blo 1919435 5469403 := bstep (se 1 (by rfl) ⟨4102052, by rfl⟩ : syracuseStep 5469403 = 8204105) B8204105
theorem B7292537 : Blo 1919435 7292537 := bstep (se 2 (by rfl) ⟨2734701, by rfl⟩ : syracuseStep 7292537 = 5469403) B5469403
theorem B4861691 : Blo 1919435 4861691 := bstep (se 1 (by rfl) ⟨3646268, by rfl⟩ : syracuseStep 4861691 = 7292537) B7292537
theorem B3241127 : Blo 1919435 3241127 := bstep (se 1 (by rfl) ⟨2430845, by rfl⟩ : syracuseStep 3241127 = 4861691) B4861691
theorem B2160751 : Blo 1919435 2160751 := bstep (se 1 (by rfl) ⟨1620563, by rfl⟩ : syracuseStep 2160751 = 3241127) B3241127
theorem B2881001 : Blo 1919435 2881001 := bstep (se 2 (by rfl) ⟨1080375, by rfl⟩ : syracuseStep 2881001 = 2160751) B2160751
theorem B1920667 : Blo 1919435 1920667 := bstep (se 1 (by rfl) ⟨1440500, by rfl⟩ : syracuseStep 1920667 = 2881001) B2881001
theorem B2307409 : Blo 1919435 2307409 := bbase (se 2 (by rfl) ⟨865278, by rfl⟩ : syracuseStep 2307409 = 1730557) (by norm_num)
theorem B12306181 : Blo 1919435 12306181 := bstep (se 4 (by rfl) ⟨1153704, by rfl⟩ : syracuseStep 12306181 = 2307409) B2307409
theorem B16408241 : Blo 1919435 16408241 := bstep (se 2 (by rfl) ⟨6153090, by rfl⟩ : syracuseStep 16408241 = 12306181) B12306181
theorem B10938827 : Blo 1919435 10938827 := bstep (se 1 (by rfl) ⟨8204120, by rfl⟩ : syracuseStep 10938827 = 16408241) B16408241
theorem B7292551 : Blo 1919435 7292551 := bstep (se 1 (by rfl) ⟨5469413, by rfl⟩ : syracuseStep 7292551 = 10938827) B10938827
theorem B9723401 : Blo 1919435 9723401 := bstep (se 2 (by rfl) ⟨3646275, by rfl⟩ : syracuseStep 9723401 = 7292551) B7292551
theorem B6482267 : Blo 1919435 6482267 := bstep (se 1 (by rfl) ⟨4861700, by rfl⟩ : syracuseStep 6482267 = 9723401) B9723401
theorem B4321511 : Blo 1919435 4321511 := bstep (se 1 (by rfl) ⟨3241133, by rfl⟩ : syracuseStep 4321511 = 6482267) B6482267
theorem B2881007 : Blo 1919435 2881007 := bstep (se 1 (by rfl) ⟨2160755, by rfl⟩ : syracuseStep 2881007 = 4321511) B4321511
theorem B1920671 : Blo 1919435 1920671 := bstep (se 1 (by rfl) ⟨1440503, by rfl⟩ : syracuseStep 1920671 = 2881007) B2881007
theorem B2881013 : Blo 1919435 2881013 := bbase (se 5 (by rfl) ⟨135047, by rfl⟩ : syracuseStep 2881013 = 270095) (by norm_num)
theorem B1920675 : Blo 1919435 1920675 := bstep (se 1 (by rfl) ⟨1440506, by rfl⟩ : syracuseStep 1920675 = 2881013) B2881013
theorem B4380493 : Blo 1919435 4380493 := bbase (se 3 (by rfl) ⟨821342, by rfl⟩ : syracuseStep 4380493 = 1642685) (by norm_num)
theorem B5840657 : Blo 1919435 5840657 := bstep (se 2 (by rfl) ⟨2190246, by rfl⟩ : syracuseStep 5840657 = 4380493) B4380493
theorem B3893771 : Blo 1919435 3893771 := bstep (se 1 (by rfl) ⟨2920328, by rfl⟩ : syracuseStep 3893771 = 5840657) B5840657
theorem B10383389 : Blo 1919435 10383389 := bstep (se 3 (by rfl) ⟨1946885, by rfl⟩ : syracuseStep 10383389 = 3893771) B3893771
theorem B6922259 : Blo 1919435 6922259 := bstep (se 1 (by rfl) ⟨5191694, by rfl⟩ : syracuseStep 6922259 = 10383389) B10383389
theorem B4614839 : Blo 1919435 4614839 := bstep (se 1 (by rfl) ⟨3461129, by rfl⟩ : syracuseStep 4614839 = 6922259) B6922259
theorem B3076559 : Blo 1919435 3076559 := bstep (se 1 (by rfl) ⟨2307419, by rfl⟩ : syracuseStep 3076559 = 4614839) B4614839
theorem B2051039 : Blo 1919435 2051039 := bstep (se 1 (by rfl) ⟨1538279, by rfl⟩ : syracuseStep 2051039 = 3076559) B3076559
theorem B5469437 : Blo 1919435 5469437 := bstep (se 3 (by rfl) ⟨1025519, by rfl⟩ : syracuseStep 5469437 = 2051039) B2051039
theorem B3646291 : Blo 1919435 3646291 := bstep (se 1 (by rfl) ⟨2734718, by rfl⟩ : syracuseStep 3646291 = 5469437) B5469437
theorem B4861721 : Blo 1919435 4861721 := bstep (se 2 (by rfl) ⟨1823145, by rfl⟩ : syracuseStep 4861721 = 3646291) B3646291
theorem B3241147 : Blo 1919435 3241147 := bstep (se 1 (by rfl) ⟨2430860, by rfl⟩ : syracuseStep 3241147 = 4861721) B4861721
theorem B4321529 : Blo 1919435 4321529 := bstep (se 2 (by rfl) ⟨1620573, by rfl⟩ : syracuseStep 4321529 = 3241147) B3241147
theorem B2881019 : Blo 1919435 2881019 := bstep (se 1 (by rfl) ⟨2160764, by rfl⟩ : syracuseStep 2881019 = 4321529) B4321529
theorem B1920679 : Blo 1919435 1920679 := bstep (se 1 (by rfl) ⟨1440509, by rfl⟩ : syracuseStep 1920679 = 2881019) B2881019
theorem B2160769 : Blo 1919435 2160769 := bbase (se 2 (by rfl) ⟨810288, by rfl⟩ : syracuseStep 2160769 = 1620577) (by norm_num)
theorem B2881025 : Blo 1919435 2881025 := bstep (se 2 (by rfl) ⟨1080384, by rfl⟩ : syracuseStep 2881025 = 2160769) B2160769
theorem B1920683 : Blo 1919435 1920683 := bstep (se 1 (by rfl) ⟨1440512, by rfl⟩ : syracuseStep 1920683 = 2881025) B2881025
theorem B4861741 : Blo 1919435 4861741 := bbase (se 3 (by rfl) ⟨911576, by rfl⟩ : syracuseStep 4861741 = 1823153) (by norm_num)
theorem B6482321 : Blo 1919435 6482321 := bstep (se 2 (by rfl) ⟨2430870, by rfl⟩ : syracuseStep 6482321 = 4861741) B4861741
theorem B4321547 : Blo 1919435 4321547 := bstep (se 1 (by rfl) ⟨3241160, by rfl⟩ : syracuseStep 4321547 = 6482321) B6482321
theorem B2881031 : Blo 1919435 2881031 := bstep (se 1 (by rfl) ⟨2160773, by rfl⟩ : syracuseStep 2881031 = 4321547) B4321547
theorem B1920687 : Blo 1919435 1920687 := bstep (se 1 (by rfl) ⟨1440515, by rfl⟩ : syracuseStep 1920687 = 2881031) B2881031
theorem B2881037 : Blo 1919435 2881037 := bbase (se 3 (by rfl) ⟨540194, by rfl⟩ : syracuseStep 2881037 = 1080389) (by norm_num)
theorem B1920691 : Blo 1919435 1920691 := bstep (se 1 (by rfl) ⟨1440518, by rfl⟩ : syracuseStep 1920691 = 2881037) B2881037
theorem B4321565 : Blo 1919435 4321565 := bbase (se 3 (by rfl) ⟨810293, by rfl⟩ : syracuseStep 4321565 = 1620587) (by norm_num)
theorem B2881043 : Blo 1919435 2881043 := bstep (se 1 (by rfl) ⟨2160782, by rfl⟩ : syracuseStep 2881043 = 4321565) B4321565
theorem B1920695 : Blo 1919435 1920695 := bstep (se 1 (by rfl) ⟨1440521, by rfl⟩ : syracuseStep 1920695 = 2881043) B2881043
theorem B3241181 : Blo 1919435 3241181 := bbase (se 3 (by rfl) ⟨607721, by rfl⟩ : syracuseStep 3241181 = 1215443) (by norm_num)
theorem B2160787 : Blo 1919435 2160787 := bstep (se 1 (by rfl) ⟨1620590, by rfl⟩ : syracuseStep 2160787 = 3241181) B3241181
theorem B2881049 : Blo 1919435 2881049 := bstep (se 2 (by rfl) ⟨1080393, by rfl⟩ : syracuseStep 2881049 = 2160787) B2160787
theorem B1920699 : Blo 1919435 1920699 := bstep (se 1 (by rfl) ⟨1440524, by rfl⟩ : syracuseStep 1920699 = 2881049) B2881049
theorem B7016789 : Blo 1919435 7016789 := bbase (se 10 (by rfl) ⟨10278, by rfl⟩ : syracuseStep 7016789 = 20557) (by norm_num)
theorem B4677859 : Blo 1919435 4677859 := bstep (se 1 (by rfl) ⟨3508394, by rfl⟩ : syracuseStep 4677859 = 7016789) B7016789
theorem B6237145 : Blo 1919435 6237145 := bstep (se 2 (by rfl) ⟨2338929, by rfl⟩ : syracuseStep 6237145 = 4677859) B4677859
theorem B8316193 : Blo 1919435 8316193 := bstep (se 2 (by rfl) ⟨3118572, by rfl⟩ : syracuseStep 8316193 = 6237145) B6237145
theorem B11088257 : Blo 1919435 11088257 := bstep (se 2 (by rfl) ⟨4158096, by rfl⟩ : syracuseStep 11088257 = 8316193) B8316193
theorem B29568685 : Blo 1919435 29568685 := bstep (se 3 (by rfl) ⟨5544128, by rfl⟩ : syracuseStep 29568685 = 11088257) B11088257
theorem B39424913 : Blo 1919435 39424913 := bstep (se 2 (by rfl) ⟨14784342, by rfl⟩ : syracuseStep 39424913 = 29568685) B29568685
theorem B26283275 : Blo 1919435 26283275 := bstep (se 1 (by rfl) ⟨19712456, by rfl⟩ : syracuseStep 26283275 = 39424913) B39424913
theorem B17522183 : Blo 1919435 17522183 := bstep (se 1 (by rfl) ⟨13141637, by rfl⟩ : syracuseStep 17522183 = 26283275) B26283275
theorem B11681455 : Blo 1919435 11681455 := bstep (se 1 (by rfl) ⟨8761091, by rfl⟩ : syracuseStep 11681455 = 17522183) B17522183
theorem B15575273 : Blo 1919435 15575273 := bstep (se 2 (by rfl) ⟨5840727, by rfl⟩ : syracuseStep 15575273 = 11681455) B11681455
theorem B10383515 : Blo 1919435 10383515 := bstep (se 1 (by rfl) ⟨7787636, by rfl⟩ : syracuseStep 10383515 = 15575273) B15575273
theorem B6922343 : Blo 1919435 6922343 := bstep (se 1 (by rfl) ⟨5191757, by rfl⟩ : syracuseStep 6922343 = 10383515) B10383515
theorem B4614895 : Blo 1919435 4614895 := bstep (se 1 (by rfl) ⟨3461171, by rfl⟩ : syracuseStep 4614895 = 6922343) B6922343
theorem B6153193 : Blo 1919435 6153193 := bstep (se 2 (by rfl) ⟨2307447, by rfl⟩ : syracuseStep 6153193 = 4614895) B4614895
theorem B8204257 : Blo 1919435 8204257 := bstep (se 2 (by rfl) ⟨3076596, by rfl⟩ : syracuseStep 8204257 = 6153193) B6153193
theorem B10939009 : Blo 1919435 10939009 := bstep (se 2 (by rfl) ⟨4102128, by rfl⟩ : syracuseStep 10939009 = 8204257) B8204257
theorem B14585345 : Blo 1919435 14585345 := bstep (se 2 (by rfl) ⟨5469504, by rfl⟩ : syracuseStep 14585345 = 10939009) B10939009
theorem B9723563 : Blo 1919435 9723563 := bstep (se 1 (by rfl) ⟨7292672, by rfl⟩ : syracuseStep 9723563 = 14585345) B14585345
theorem B6482375 : Blo 1919435 6482375 := bstep (se 1 (by rfl) ⟨4861781, by rfl⟩ : syracuseStep 6482375 = 9723563) B9723563
theorem B4321583 : Blo 1919435 4321583 := bstep (se 1 (by rfl) ⟨3241187, by rfl⟩ : syracuseStep 4321583 = 6482375) B6482375
theorem B2881055 : Blo 1919435 2881055 := bstep (se 1 (by rfl) ⟨2160791, by rfl⟩ : syracuseStep 2881055 = 4321583) B4321583
theorem B1920703 : Blo 1919435 1920703 := bstep (se 1 (by rfl) ⟨1440527, by rfl⟩ : syracuseStep 1920703 = 2881055) B2881055
theorem B2881061 : Blo 1919435 2881061 := bbase (se 4 (by rfl) ⟨270099, by rfl⟩ : syracuseStep 2881061 = 540199) (by norm_num)
theorem B1920707 : Blo 1919435 1920707 := bstep (se 1 (by rfl) ⟨1440530, by rfl⟩ : syracuseStep 1920707 = 2881061) B2881061
theorem B2430901 : Blo 1919435 2430901 := bbase (se 5 (by rfl) ⟨113948, by rfl⟩ : syracuseStep 2430901 = 227897) (by norm_num)
theorem B3241201 : Blo 1919435 3241201 := bstep (se 2 (by rfl) ⟨1215450, by rfl⟩ : syracuseStep 3241201 = 2430901) B2430901
theorem B4321601 : Blo 1919435 4321601 := bstep (se 2 (by rfl) ⟨1620600, by rfl⟩ : syracuseStep 4321601 = 3241201) B3241201
theorem B2881067 : Blo 1919435 2881067 := bstep (se 1 (by rfl) ⟨2160800, by rfl⟩ : syracuseStep 2881067 = 4321601) B4321601
theorem B1920711 : Blo 1919435 1920711 := bstep (se 1 (by rfl) ⟨1440533, by rfl⟩ : syracuseStep 1920711 = 2881067) B2881067
theorem B2160805 : Blo 1919435 2160805 := bbase (se 4 (by rfl) ⟨202575, by rfl⟩ : syracuseStep 2160805 = 405151) (by norm_num)
theorem B2881073 : Blo 1919435 2881073 := bstep (se 2 (by rfl) ⟨1080402, by rfl⟩ : syracuseStep 2881073 = 2160805) B2160805
theorem B1920715 : Blo 1919435 1920715 := bstep (se 1 (by rfl) ⟨1440536, by rfl⟩ : syracuseStep 1920715 = 2881073) B2881073
theorem B1973489 : Blo 1919435 1973489 := bbase (se 2 (by rfl) ⟨740058, by rfl⟩ : syracuseStep 1973489 = 1480117) (by norm_num)
theorem B21050549 : Blo 1919435 21050549 := bstep (se 5 (by rfl) ⟨986744, by rfl⟩ : syracuseStep 21050549 = 1973489) B1973489
theorem B14033699 : Blo 1919435 14033699 := bstep (se 1 (by rfl) ⟨10525274, by rfl⟩ : syracuseStep 14033699 = 21050549) B21050549
theorem B9355799 : Blo 1919435 9355799 := bstep (se 1 (by rfl) ⟨7016849, by rfl⟩ : syracuseStep 9355799 = 14033699) B14033699
theorem B6237199 : Blo 1919435 6237199 := bstep (se 1 (by rfl) ⟨4677899, by rfl⟩ : syracuseStep 6237199 = 9355799) B9355799
theorem B8316265 : Blo 1919435 8316265 := bstep (se 2 (by rfl) ⟨3118599, by rfl⟩ : syracuseStep 8316265 = 6237199) B6237199
theorem B11088353 : Blo 1919435 11088353 := bstep (se 2 (by rfl) ⟨4158132, by rfl⟩ : syracuseStep 11088353 = 8316265) B8316265
theorem B7392235 : Blo 1919435 7392235 := bstep (se 1 (by rfl) ⟨5544176, by rfl⟩ : syracuseStep 7392235 = 11088353) B11088353
theorem B9856313 : Blo 1919435 9856313 := bstep (se 2 (by rfl) ⟨3696117, by rfl⟩ : syracuseStep 9856313 = 7392235) B7392235
theorem B6570875 : Blo 1919435 6570875 := bstep (se 1 (by rfl) ⟨4928156, by rfl⟩ : syracuseStep 6570875 = 9856313) B9856313
theorem B4380583 : Blo 1919435 4380583 := bstep (se 1 (by rfl) ⟨3285437, by rfl⟩ : syracuseStep 4380583 = 6570875) B6570875
theorem B5840777 : Blo 1919435 5840777 := bstep (se 2 (by rfl) ⟨2190291, by rfl⟩ : syracuseStep 5840777 = 4380583) B4380583
theorem B3893851 : Blo 1919435 3893851 := bstep (se 1 (by rfl) ⟨2920388, by rfl⟩ : syracuseStep 3893851 = 5840777) B5840777
theorem B20767205 : Blo 1919435 20767205 := bstep (se 4 (by rfl) ⟨1946925, by rfl⟩ : syracuseStep 20767205 = 3893851) B3893851
theorem B13844803 : Blo 1919435 13844803 := bstep (se 1 (by rfl) ⟨10383602, by rfl⟩ : syracuseStep 13844803 = 20767205) B20767205
theorem B18459737 : Blo 1919435 18459737 := bstep (se 2 (by rfl) ⟨6922401, by rfl⟩ : syracuseStep 18459737 = 13844803) B13844803
theorem B12306491 : Blo 1919435 12306491 := bstep (se 1 (by rfl) ⟨9229868, by rfl⟩ : syracuseStep 12306491 = 18459737) B18459737
theorem B8204327 : Blo 1919435 8204327 := bstep (se 1 (by rfl) ⟨6153245, by rfl⟩ : syracuseStep 8204327 = 12306491) B12306491
theorem B5469551 : Blo 1919435 5469551 := bstep (se 1 (by rfl) ⟨4102163, by rfl⟩ : syracuseStep 5469551 = 8204327) B8204327
theorem B3646367 : Blo 1919435 3646367 := bstep (se 1 (by rfl) ⟨2734775, by rfl⟩ : syracuseStep 3646367 = 5469551) B5469551
theorem B2430911 : Blo 1919435 2430911 := bstep (se 1 (by rfl) ⟨1823183, by rfl⟩ : syracuseStep 2430911 = 3646367) B3646367
theorem B6482429 : Blo 1919435 6482429 := bstep (se 3 (by rfl) ⟨1215455, by rfl⟩ : syracuseStep 6482429 = 2430911) B2430911
theorem B4321619 : Blo 1919435 4321619 := bstep (se 1 (by rfl) ⟨3241214, by rfl⟩ : syracuseStep 4321619 = 6482429) B6482429
theorem B2881079 : Blo 1919435 2881079 := bstep (se 1 (by rfl) ⟨2160809, by rfl⟩ : syracuseStep 2881079 = 4321619) B4321619
theorem B1920719 : Blo 1919435 1920719 := bstep (se 1 (by rfl) ⟨1440539, by rfl⟩ : syracuseStep 1920719 = 2881079) B2881079
theorem B2881085 : Blo 1919435 2881085 := bbase (se 3 (by rfl) ⟨540203, by rfl⟩ : syracuseStep 2881085 = 1080407) (by norm_num)
theorem B1920723 : Blo 1919435 1920723 := bstep (se 1 (by rfl) ⟨1440542, by rfl⟩ : syracuseStep 1920723 = 2881085) B2881085
theorem B4321637 : Blo 1919435 4321637 := bbase (se 4 (by rfl) ⟨405153, by rfl⟩ : syracuseStep 4321637 = 810307) (by norm_num)
theorem B2881091 : Blo 1919435 2881091 := bstep (se 1 (by rfl) ⟨2160818, by rfl⟩ : syracuseStep 2881091 = 4321637) B4321637
theorem B1920727 : Blo 1919435 1920727 := bstep (se 1 (by rfl) ⟨1440545, by rfl⟩ : syracuseStep 1920727 = 2881091) B2881091
theorem B4861853 : Blo 1919435 4861853 := bbase (se 3 (by rfl) ⟨911597, by rfl⟩ : syracuseStep 4861853 = 1823195) (by norm_num)
theorem B3241235 : Blo 1919435 3241235 := bstep (se 1 (by rfl) ⟨2430926, by rfl⟩ : syracuseStep 3241235 = 4861853) B4861853
theorem B2160823 : Blo 1919435 2160823 := bstep (se 1 (by rfl) ⟨1620617, by rfl⟩ : syracuseStep 2160823 = 3241235) B3241235
theorem B2881097 : Blo 1919435 2881097 := bstep (se 2 (by rfl) ⟨1080411, by rfl⟩ : syracuseStep 2881097 = 2160823) B2160823
theorem B1920731 : Blo 1919435 1920731 := bstep (se 1 (by rfl) ⟨1440548, by rfl⟩ : syracuseStep 1920731 = 2881097) B2881097
theorem B3646397 : Blo 1919435 3646397 := bbase (se 3 (by rfl) ⟨683699, by rfl⟩ : syracuseStep 3646397 = 1367399) (by norm_num)
theorem B9723725 : Blo 1919435 9723725 := bstep (se 3 (by rfl) ⟨1823198, by rfl⟩ : syracuseStep 9723725 = 3646397) B3646397
theorem B6482483 : Blo 1919435 6482483 := bstep (se 1 (by rfl) ⟨4861862, by rfl⟩ : syracuseStep 6482483 = 9723725) B9723725
theorem B4321655 : Blo 1919435 4321655 := bstep (se 1 (by rfl) ⟨3241241, by rfl⟩ : syracuseStep 4321655 = 6482483) B6482483
theorem B2881103 : Blo 1919435 2881103 := bstep (se 1 (by rfl) ⟨2160827, by rfl⟩ : syracuseStep 2881103 = 4321655) B4321655
theorem B1920735 : Blo 1919435 1920735 := bstep (se 1 (by rfl) ⟨1440551, by rfl⟩ : syracuseStep 1920735 = 2881103) B2881103
theorem B2881109 : Blo 1919435 2881109 := bbase (se 8 (by rfl) ⟨16881, by rfl⟩ : syracuseStep 2881109 = 33763) (by norm_num)
theorem B1920739 : Blo 1919435 1920739 := bstep (se 1 (by rfl) ⟨1440554, by rfl⟩ : syracuseStep 1920739 = 2881109) B2881109
theorem B3076661 : Blo 1919435 3076661 := bbase (se 5 (by rfl) ⟨144218, by rfl⟩ : syracuseStep 3076661 = 288437) (by norm_num)
theorem B8204429 : Blo 1919435 8204429 := bstep (se 3 (by rfl) ⟨1538330, by rfl⟩ : syracuseStep 8204429 = 3076661) B3076661
theorem B5469619 : Blo 1919435 5469619 := bstep (se 1 (by rfl) ⟨4102214, by rfl⟩ : syracuseStep 5469619 = 8204429) B8204429
theorem B7292825 : Blo 1919435 7292825 := bstep (se 2 (by rfl) ⟨2734809, by rfl⟩ : syracuseStep 7292825 = 5469619) B5469619
theorem B4861883 : Blo 1919435 4861883 := bstep (se 1 (by rfl) ⟨3646412, by rfl⟩ : syracuseStep 4861883 = 7292825) B7292825
theorem B3241255 : Blo 1919435 3241255 := bstep (se 1 (by rfl) ⟨2430941, by rfl⟩ : syracuseStep 3241255 = 4861883) B4861883
theorem B4321673 : Blo 1919435 4321673 := bstep (se 2 (by rfl) ⟨1620627, by rfl⟩ : syracuseStep 4321673 = 3241255) B3241255
theorem B2881115 : Blo 1919435 2881115 := bstep (se 1 (by rfl) ⟨2160836, by rfl⟩ : syracuseStep 2881115 = 4321673) B4321673
theorem B1920743 : Blo 1919435 1920743 := bstep (se 1 (by rfl) ⟨1440557, by rfl⟩ : syracuseStep 1920743 = 2881115) B2881115
theorem B2160841 : Blo 1919435 2160841 := bbase (se 2 (by rfl) ⟨810315, by rfl⟩ : syracuseStep 2160841 = 1620631) (by norm_num)
theorem B2881121 : Blo 1919435 2881121 := bstep (se 2 (by rfl) ⟨1080420, by rfl⟩ : syracuseStep 2881121 = 2160841) B2160841
theorem B1920747 : Blo 1919435 1920747 := bstep (se 1 (by rfl) ⟨1440560, by rfl⟩ : syracuseStep 1920747 = 2881121) B2881121
theorem B9230021 : Blo 1919435 9230021 := bbase (se 4 (by rfl) ⟨865314, by rfl⟩ : syracuseStep 9230021 = 1730629) (by norm_num)
theorem B6153347 : Blo 1919435 6153347 := bstep (se 1 (by rfl) ⟨4615010, by rfl⟩ : syracuseStep 6153347 = 9230021) B9230021
theorem B16408925 : Blo 1919435 16408925 := bstep (se 3 (by rfl) ⟨3076673, by rfl⟩ : syracuseStep 16408925 = 6153347) B6153347
theorem B10939283 : Blo 1919435 10939283 := bstep (se 1 (by rfl) ⟨8204462, by rfl⟩ : syracuseStep 10939283 = 16408925) B16408925
theorem B7292855 : Blo 1919435 7292855 := bstep (se 1 (by rfl) ⟨5469641, by rfl⟩ : syracuseStep 7292855 = 10939283) B10939283
theorem B4861903 : Blo 1919435 4861903 := bstep (se 1 (by rfl) ⟨3646427, by rfl⟩ : syracuseStep 4861903 = 7292855) B7292855
theorem B6482537 : Blo 1919435 6482537 := bstep (se 2 (by rfl) ⟨2430951, by rfl⟩ : syracuseStep 6482537 = 4861903) B4861903
theorem B4321691 : Blo 1919435 4321691 := bstep (se 1 (by rfl) ⟨3241268, by rfl⟩ : syracuseStep 4321691 = 6482537) B6482537
theorem B2881127 : Blo 1919435 2881127 := bstep (se 1 (by rfl) ⟨2160845, by rfl⟩ : syracuseStep 2881127 = 4321691) B4321691
theorem B1920751 : Blo 1919435 1920751 := bstep (se 1 (by rfl) ⟨1440563, by rfl⟩ : syracuseStep 1920751 = 2881127) B2881127
theorem B2881133 : Blo 1919435 2881133 := bbase (se 3 (by rfl) ⟨540212, by rfl⟩ : syracuseStep 2881133 = 1080425) (by norm_num)
theorem B1920755 : Blo 1919435 1920755 := bstep (se 1 (by rfl) ⟨1440566, by rfl⟩ : syracuseStep 1920755 = 2881133) B2881133
theorem B4321709 : Blo 1919435 4321709 := bbase (se 3 (by rfl) ⟨810320, by rfl⟩ : syracuseStep 4321709 = 1620641) (by norm_num)
theorem B2881139 : Blo 1919435 2881139 := bstep (se 1 (by rfl) ⟨2160854, by rfl⟩ : syracuseStep 2881139 = 4321709) B4321709
theorem B1920759 : Blo 1919435 1920759 := bstep (se 1 (by rfl) ⟨1440569, by rfl⟩ : syracuseStep 1920759 = 2881139) B2881139
theorem B2051129 : Blo 1919435 2051129 := bbase (se 2 (by rfl) ⟨769173, by rfl⟩ : syracuseStep 2051129 = 1538347) (by norm_num)
theorem B5469677 : Blo 1919435 5469677 := bstep (se 3 (by rfl) ⟨1025564, by rfl⟩ : syracuseStep 5469677 = 2051129) B2051129
theorem B3646451 : Blo 1919435 3646451 := bstep (se 1 (by rfl) ⟨2734838, by rfl⟩ : syracuseStep 3646451 = 5469677) B5469677
theorem B2430967 : Blo 1919435 2430967 := bstep (se 1 (by rfl) ⟨1823225, by rfl⟩ : syracuseStep 2430967 = 3646451) B3646451
theorem B3241289 : Blo 1919435 3241289 := bstep (se 2 (by rfl) ⟨1215483, by rfl⟩ : syracuseStep 3241289 = 2430967) B2430967
theorem B2160859 : Blo 1919435 2160859 := bstep (se 1 (by rfl) ⟨1620644, by rfl⟩ : syracuseStep 2160859 = 3241289) B3241289
theorem B2881145 : Blo 1919435 2881145 := bstep (se 2 (by rfl) ⟨1080429, by rfl⟩ : syracuseStep 2881145 = 2160859) B2160859
theorem B1920763 : Blo 1919435 1920763 := bstep (se 1 (by rfl) ⟨1440572, by rfl⟩ : syracuseStep 1920763 = 2881145) B2881145
theorem B2772157 : Blo 1919435 2772157 := bbase (se 3 (by rfl) ⟨519779, by rfl⟩ : syracuseStep 2772157 = 1039559) (by norm_num)
theorem B3696209 : Blo 1919435 3696209 := bstep (se 2 (by rfl) ⟨1386078, by rfl⟩ : syracuseStep 3696209 = 2772157) B2772157
theorem B2464139 : Blo 1919435 2464139 := bstep (se 1 (by rfl) ⟨1848104, by rfl⟩ : syracuseStep 2464139 = 3696209) B3696209
theorem B6571037 : Blo 1919435 6571037 := bstep (se 3 (by rfl) ⟨1232069, by rfl⟩ : syracuseStep 6571037 = 2464139) B2464139
theorem B4380691 : Blo 1919435 4380691 := bstep (se 1 (by rfl) ⟨3285518, by rfl⟩ : syracuseStep 4380691 = 6571037) B6571037
theorem B5840921 : Blo 1919435 5840921 := bstep (se 2 (by rfl) ⟨2190345, by rfl⟩ : syracuseStep 5840921 = 4380691) B4380691
theorem B15575789 : Blo 1919435 15575789 := bstep (se 3 (by rfl) ⟨2920460, by rfl⟩ : syracuseStep 15575789 = 5840921) B5840921
theorem B10383859 : Blo 1919435 10383859 := bstep (se 1 (by rfl) ⟨7787894, by rfl⟩ : syracuseStep 10383859 = 15575789) B15575789
theorem B55380581 : Blo 1919435 55380581 := bstep (se 4 (by rfl) ⟨5191929, by rfl⟩ : syracuseStep 55380581 = 10383859) B10383859
theorem B36920387 : Blo 1919435 36920387 := bstep (se 1 (by rfl) ⟨27690290, by rfl⟩ : syracuseStep 36920387 = 55380581) B55380581
theorem B24613591 : Blo 1919435 24613591 := bstep (se 1 (by rfl) ⟨18460193, by rfl⟩ : syracuseStep 24613591 = 36920387) B36920387
theorem B32818121 : Blo 1919435 32818121 := bstep (se 2 (by rfl) ⟨12306795, by rfl⟩ : syracuseStep 32818121 = 24613591) B24613591
theorem B21878747 : Blo 1919435 21878747 := bstep (se 1 (by rfl) ⟨16409060, by rfl⟩ : syracuseStep 21878747 = 32818121) B32818121
theorem B14585831 : Blo 1919435 14585831 := bstep (se 1 (by rfl) ⟨10939373, by rfl⟩ : syracuseStep 14585831 = 21878747) B21878747
theorem B9723887 : Blo 1919435 9723887 := bstep (se 1 (by rfl) ⟨7292915, by rfl⟩ : syracuseStep 9723887 = 14585831) B14585831
theorem B6482591 : Blo 1919435 6482591 := bstep (se 1 (by rfl) ⟨4861943, by rfl⟩ : syracuseStep 6482591 = 9723887) B9723887
theorem B4321727 : Blo 1919435 4321727 := bstep (se 1 (by rfl) ⟨3241295, by rfl⟩ : syracuseStep 4321727 = 6482591) B6482591
theorem B2881151 : Blo 1919435 2881151 := bstep (se 1 (by rfl) ⟨2160863, by rfl⟩ : syracuseStep 2881151 = 4321727) B4321727
theorem B1920767 : Blo 1919435 1920767 := bstep (se 1 (by rfl) ⟨1440575, by rfl⟩ : syracuseStep 1920767 = 2881151) B2881151
theorem B2881157 : Blo 1919435 2881157 := bbase (se 4 (by rfl) ⟨270108, by rfl⟩ : syracuseStep 2881157 = 540217) (by norm_num)
theorem B1920771 : Blo 1919435 1920771 := bstep (se 1 (by rfl) ⟨1440578, by rfl⟩ : syracuseStep 1920771 = 2881157) B2881157
theorem B3241309 : Blo 1919435 3241309 := bbase (se 3 (by rfl) ⟨607745, by rfl⟩ : syracuseStep 3241309 = 1215491) (by norm_num)
theorem B4321745 : Blo 1919435 4321745 := bstep (se 2 (by rfl) ⟨1620654, by rfl⟩ : syracuseStep 4321745 = 3241309) B3241309
theorem B2881163 : Blo 1919435 2881163 := bstep (se 1 (by rfl) ⟨2160872, by rfl⟩ : syracuseStep 2881163 = 4321745) B4321745
theorem B1920775 : Blo 1919435 1920775 := bstep (se 1 (by rfl) ⟨1440581, by rfl⟩ : syracuseStep 1920775 = 2881163) B2881163
theorem B2160877 : Blo 1919435 2160877 := bbase (se 3 (by rfl) ⟨405164, by rfl⟩ : syracuseStep 2160877 = 810329) (by norm_num)
theorem B2881169 : Blo 1919435 2881169 := bstep (se 2 (by rfl) ⟨1080438, by rfl⟩ : syracuseStep 2881169 = 2160877) B2160877
theorem B1920779 : Blo 1919435 1920779 := bstep (se 1 (by rfl) ⟨1440584, by rfl⟩ : syracuseStep 1920779 = 2881169) B2881169
theorem B6482645 : Blo 1919435 6482645 := bbase (se 7 (by rfl) ⟨75968, by rfl⟩ : syracuseStep 6482645 = 151937) (by norm_num)
theorem B4321763 : Blo 1919435 4321763 := bstep (se 1 (by rfl) ⟨3241322, by rfl⟩ : syracuseStep 4321763 = 6482645) B6482645
theorem B2881175 : Blo 1919435 2881175 := bstep (se 1 (by rfl) ⟨2160881, by rfl⟩ : syracuseStep 2881175 = 4321763) B4321763
theorem B1920783 : Blo 1919435 1920783 := bstep (se 1 (by rfl) ⟨1440587, by rfl⟩ : syracuseStep 1920783 = 2881175) B2881175
theorem B2881181 : Blo 1919435 2881181 := bbase (se 3 (by rfl) ⟨540221, by rfl⟩ : syracuseStep 2881181 = 1080443) (by norm_num)
theorem B1920787 : Blo 1919435 1920787 := bstep (se 1 (by rfl) ⟨1440590, by rfl⟩ : syracuseStep 1920787 = 2881181) B2881181
theorem B4321781 : Blo 1919435 4321781 := bbase (se 5 (by rfl) ⟨202583, by rfl⟩ : syracuseStep 4321781 = 405167) (by norm_num)
theorem B2881187 : Blo 1919435 2881187 := bstep (se 1 (by rfl) ⟨2160890, by rfl⟩ : syracuseStep 2881187 = 4321781) B4321781
theorem B1920791 : Blo 1919435 1920791 := bstep (se 1 (by rfl) ⟨1440593, by rfl⟩ : syracuseStep 1920791 = 2881187) B2881187
theorem B3894005 : Blo 1919435 3894005 := bbase (se 5 (by rfl) ⟨182531, by rfl⟩ : syracuseStep 3894005 = 365063) (by norm_num)
theorem B10384013 : Blo 1919435 10384013 := bstep (se 3 (by rfl) ⟨1947002, by rfl⟩ : syracuseStep 10384013 = 3894005) B3894005
theorem B6922675 : Blo 1919435 6922675 := bstep (se 1 (by rfl) ⟨5192006, by rfl⟩ : syracuseStep 6922675 = 10384013) B10384013
theorem B36920933 : Blo 1919435 36920933 := bstep (se 4 (by rfl) ⟨3461337, by rfl⟩ : syracuseStep 36920933 = 6922675) B6922675
theorem B24613955 : Blo 1919435 24613955 := bstep (se 1 (by rfl) ⟨18460466, by rfl⟩ : syracuseStep 24613955 = 36920933) B36920933
theorem B16409303 : Blo 1919435 16409303 := bstep (se 1 (by rfl) ⟨12306977, by rfl⟩ : syracuseStep 16409303 = 24613955) B24613955
theorem B10939535 : Blo 1919435 10939535 := bstep (se 1 (by rfl) ⟨8204651, by rfl⟩ : syracuseStep 10939535 = 16409303) B16409303
theorem B7293023 : Blo 1919435 7293023 := bstep (se 1 (by rfl) ⟨5469767, by rfl⟩ : syracuseStep 7293023 = 10939535) B10939535
theorem B4862015 : Blo 1919435 4862015 := bstep (se 1 (by rfl) ⟨3646511, by rfl⟩ : syracuseStep 4862015 = 7293023) B7293023
theorem B3241343 : Blo 1919435 3241343 := bstep (se 1 (by rfl) ⟨2431007, by rfl⟩ : syracuseStep 3241343 = 4862015) B4862015
theorem B2160895 : Blo 1919435 2160895 := bstep (se 1 (by rfl) ⟨1620671, by rfl⟩ : syracuseStep 2160895 = 3241343) B3241343
theorem B2881193 : Blo 1919435 2881193 := bstep (se 2 (by rfl) ⟨1080447, by rfl⟩ : syracuseStep 2881193 = 2160895) B2160895
theorem B1920795 : Blo 1919435 1920795 := bstep (se 1 (by rfl) ⟨1440596, by rfl⟩ : syracuseStep 1920795 = 2881193) B2881193
theorem B6237461 : Blo 1919435 6237461 := bbase (se 6 (by rfl) ⟨146190, by rfl⟩ : syracuseStep 6237461 = 292381) (by norm_num)
theorem B4158307 : Blo 1919435 4158307 := bstep (se 1 (by rfl) ⟨3118730, by rfl⟩ : syracuseStep 4158307 = 6237461) B6237461
theorem B22177637 : Blo 1919435 22177637 := bstep (se 4 (by rfl) ⟨2079153, by rfl⟩ : syracuseStep 22177637 = 4158307) B4158307
theorem B14785091 : Blo 1919435 14785091 := bstep (se 1 (by rfl) ⟨11088818, by rfl⟩ : syracuseStep 14785091 = 22177637) B22177637
theorem B9856727 : Blo 1919435 9856727 := bstep (se 1 (by rfl) ⟨7392545, by rfl⟩ : syracuseStep 9856727 = 14785091) B14785091
theorem B6571151 : Blo 1919435 6571151 := bstep (se 1 (by rfl) ⟨4928363, by rfl⟩ : syracuseStep 6571151 = 9856727) B9856727
theorem B4380767 : Blo 1919435 4380767 := bstep (se 1 (by rfl) ⟨3285575, by rfl⟩ : syracuseStep 4380767 = 6571151) B6571151
theorem B2920511 : Blo 1919435 2920511 := bstep (se 1 (by rfl) ⟨2190383, by rfl⟩ : syracuseStep 2920511 = 4380767) B4380767
theorem B1947007 : Blo 1919435 1947007 := bstep (se 1 (by rfl) ⟨1460255, by rfl⟩ : syracuseStep 1947007 = 2920511) B2920511
theorem B10384037 : Blo 1919435 10384037 := bstep (se 4 (by rfl) ⟨973503, by rfl⟩ : syracuseStep 10384037 = 1947007) B1947007
theorem B6922691 : Blo 1919435 6922691 := bstep (se 1 (by rfl) ⟨5192018, by rfl⟩ : syracuseStep 6922691 = 10384037) B10384037
theorem B4615127 : Blo 1919435 4615127 := bstep (se 1 (by rfl) ⟨3461345, by rfl⟩ : syracuseStep 4615127 = 6922691) B6922691
theorem B3076751 : Blo 1919435 3076751 := bstep (se 1 (by rfl) ⟨2307563, by rfl⟩ : syracuseStep 3076751 = 4615127) B4615127
theorem B2051167 : Blo 1919435 2051167 := bstep (se 1 (by rfl) ⟨1538375, by rfl⟩ : syracuseStep 2051167 = 3076751) B3076751
theorem B2734889 : Blo 1919435 2734889 := bstep (se 2 (by rfl) ⟨1025583, by rfl⟩ : syracuseStep 2734889 = 2051167) B2051167
theorem B7293037 : Blo 1919435 7293037 := bstep (se 3 (by rfl) ⟨1367444, by rfl⟩ : syracuseStep 7293037 = 2734889) B2734889
theorem B9724049 : Blo 1919435 9724049 := bstep (se 2 (by rfl) ⟨3646518, by rfl⟩ : syracuseStep 9724049 = 7293037) B7293037
theorem B6482699 : Blo 1919435 6482699 := bstep (se 1 (by rfl) ⟨4862024, by rfl⟩ : syracuseStep 6482699 = 9724049) B9724049
theorem B4321799 : Blo 1919435 4321799 := bstep (se 1 (by rfl) ⟨3241349, by rfl⟩ : syracuseStep 4321799 = 6482699) B6482699
theorem B2881199 : Blo 1919435 2881199 := bstep (se 1 (by rfl) ⟨2160899, by rfl⟩ : syracuseStep 2881199 = 4321799) B4321799
theorem B1920799 : Blo 1919435 1920799 := bstep (se 1 (by rfl) ⟨1440599, by rfl⟩ : syracuseStep 1920799 = 2881199) B2881199
theorem B2881205 : Blo 1919435 2881205 := bbase (se 5 (by rfl) ⟨135056, by rfl⟩ : syracuseStep 2881205 = 270113) (by norm_num)
theorem B1920803 : Blo 1919435 1920803 := bstep (se 1 (by rfl) ⟨1440602, by rfl⟩ : syracuseStep 1920803 = 2881205) B2881205
theorem B4862045 : Blo 1919435 4862045 := bbase (se 3 (by rfl) ⟨911633, by rfl⟩ : syracuseStep 4862045 = 1823267) (by norm_num)
theorem B3241363 : Blo 1919435 3241363 := bstep (se 1 (by rfl) ⟨2431022, by rfl⟩ : syracuseStep 3241363 = 4862045) B4862045
theorem B4321817 : Blo 1919435 4321817 := bstep (se 2 (by rfl) ⟨1620681, by rfl⟩ : syracuseStep 4321817 = 3241363) B3241363
theorem B2881211 : Blo 1919435 2881211 := bstep (se 1 (by rfl) ⟨2160908, by rfl⟩ : syracuseStep 2881211 = 4321817) B4321817
theorem B1920807 : Blo 1919435 1920807 := bstep (se 1 (by rfl) ⟨1440605, by rfl⟩ : syracuseStep 1920807 = 2881211) B2881211
theorem B2160913 : Blo 1919435 2160913 := bbase (se 2 (by rfl) ⟨810342, by rfl⟩ : syracuseStep 2160913 = 1620685) (by norm_num)
theorem B2881217 : Blo 1919435 2881217 := bstep (se 2 (by rfl) ⟨1080456, by rfl⟩ : syracuseStep 2881217 = 2160913) B2160913
theorem B1920811 : Blo 1919435 1920811 := bstep (se 1 (by rfl) ⟨1440608, by rfl⟩ : syracuseStep 1920811 = 2881217) B2881217
theorem B3646549 : Blo 1919435 3646549 := bbase (se 8 (by rfl) ⟨21366, by rfl⟩ : syracuseStep 3646549 = 42733) (by norm_num)
theorem B4862065 : Blo 1919435 4862065 := bstep (se 2 (by rfl) ⟨1823274, by rfl⟩ : syracuseStep 4862065 = 3646549) B3646549
theorem B6482753 : Blo 1919435 6482753 := bstep (se 2 (by rfl) ⟨2431032, by rfl⟩ : syracuseStep 6482753 = 4862065) B4862065
theorem B4321835 : Blo 1919435 4321835 := bstep (se 1 (by rfl) ⟨3241376, by rfl⟩ : syracuseStep 4321835 = 6482753) B6482753
theorem B2881223 : Blo 1919435 2881223 := bstep (se 1 (by rfl) ⟨2160917, by rfl⟩ : syracuseStep 2881223 = 4321835) B4321835
theorem B1920815 : Blo 1919435 1920815 := bstep (se 1 (by rfl) ⟨1440611, by rfl⟩ : syracuseStep 1920815 = 2881223) B2881223
theorem B2881229 : Blo 1919435 2881229 := bbase (se 3 (by rfl) ⟨540230, by rfl⟩ : syracuseStep 2881229 = 1080461) (by norm_num)
theorem B1920819 : Blo 1919435 1920819 := bstep (se 1 (by rfl) ⟨1440614, by rfl⟩ : syracuseStep 1920819 = 2881229) B2881229
theorem B4321853 : Blo 1919435 4321853 := bbase (se 3 (by rfl) ⟨810347, by rfl⟩ : syracuseStep 4321853 = 1620695) (by norm_num)
theorem B2881235 : Blo 1919435 2881235 := bstep (se 1 (by rfl) ⟨2160926, by rfl⟩ : syracuseStep 2881235 = 4321853) B4321853
theorem B1920823 : Blo 1919435 1920823 := bstep (se 1 (by rfl) ⟨1440617, by rfl⟩ : syracuseStep 1920823 = 2881235) B2881235
theorem B3241397 : Blo 1919435 3241397 := bbase (se 5 (by rfl) ⟨151940, by rfl⟩ : syracuseStep 3241397 = 303881) (by norm_num)
theorem B2160931 : Blo 1919435 2160931 := bstep (se 1 (by rfl) ⟨1620698, by rfl⟩ : syracuseStep 2160931 = 3241397) B3241397
theorem B2881241 : Blo 1919435 2881241 := bstep (se 2 (by rfl) ⟨1080465, by rfl⟩ : syracuseStep 2881241 = 2160931) B2160931
theorem B1920827 : Blo 1919435 1920827 := bstep (se 1 (by rfl) ⟨1440620, by rfl⟩ : syracuseStep 1920827 = 2881241) B2881241
theorem B2051201 : Blo 1919435 2051201 := bbase (se 2 (by rfl) ⟨769200, by rfl⟩ : syracuseStep 2051201 = 1538401) (by norm_num)
theorem B5469869 : Blo 1919435 5469869 := bstep (se 3 (by rfl) ⟨1025600, by rfl⟩ : syracuseStep 5469869 = 2051201) B2051201
theorem B14586317 : Blo 1919435 14586317 := bstep (se 3 (by rfl) ⟨2734934, by rfl⟩ : syracuseStep 14586317 = 5469869) B5469869
theorem B9724211 : Blo 1919435 9724211 := bstep (se 1 (by rfl) ⟨7293158, by rfl⟩ : syracuseStep 9724211 = 14586317) B14586317
theorem B6482807 : Blo 1919435 6482807 := bstep (se 1 (by rfl) ⟨4862105, by rfl⟩ : syracuseStep 6482807 = 9724211) B9724211
theorem B4321871 : Blo 1919435 4321871 := bstep (se 1 (by rfl) ⟨3241403, by rfl⟩ : syracuseStep 4321871 = 6482807) B6482807
theorem B2881247 : Blo 1919435 2881247 := bstep (se 1 (by rfl) ⟨2160935, by rfl⟩ : syracuseStep 2881247 = 4321871) B4321871
theorem B1920831 : Blo 1919435 1920831 := bstep (se 1 (by rfl) ⟨1440623, by rfl⟩ : syracuseStep 1920831 = 2881247) B2881247
theorem B2881253 : Blo 1919435 2881253 := bbase (se 4 (by rfl) ⟨270117, by rfl⟩ : syracuseStep 2881253 = 540235) (by norm_num)
theorem B1920835 : Blo 1919435 1920835 := bstep (se 1 (by rfl) ⟨1440626, by rfl⟩ : syracuseStep 1920835 = 2881253) B2881253
theorem B5469893 : Blo 1919435 5469893 := bbase (se 4 (by rfl) ⟨512802, by rfl⟩ : syracuseStep 5469893 = 1025605) (by norm_num)
theorem B3646595 : Blo 1919435 3646595 := bstep (se 1 (by rfl) ⟨2734946, by rfl⟩ : syracuseStep 3646595 = 5469893) B5469893
theorem B2431063 : Blo 1919435 2431063 := bstep (se 1 (by rfl) ⟨1823297, by rfl⟩ : syracuseStep 2431063 = 3646595) B3646595
theorem B3241417 : Blo 1919435 3241417 := bstep (se 2 (by rfl) ⟨1215531, by rfl⟩ : syracuseStep 3241417 = 2431063) B2431063
theorem B4321889 : Blo 1919435 4321889 := bstep (se 2 (by rfl) ⟨1620708, by rfl⟩ : syracuseStep 4321889 = 3241417) B3241417
theorem B2881259 : Blo 1919435 2881259 := bstep (se 1 (by rfl) ⟨2160944, by rfl⟩ : syracuseStep 2881259 = 4321889) B4321889
theorem B1920839 : Blo 1919435 1920839 := bstep (se 1 (by rfl) ⟨1440629, by rfl⟩ : syracuseStep 1920839 = 2881259) B2881259
theorem B2160949 : Blo 1919435 2160949 := bbase (se 5 (by rfl) ⟨101294, by rfl⟩ : syracuseStep 2160949 = 202589) (by norm_num)
theorem B2881265 : Blo 1919435 2881265 := bstep (se 2 (by rfl) ⟨1080474, by rfl⟩ : syracuseStep 2881265 = 2160949) B2160949
theorem B1920843 : Blo 1919435 1920843 := bstep (se 1 (by rfl) ⟨1440632, by rfl⟩ : syracuseStep 1920843 = 2881265) B2881265
theorem B2431073 : Blo 1919435 2431073 := bbase (se 2 (by rfl) ⟨911652, by rfl⟩ : syracuseStep 2431073 = 1823305) (by norm_num)
theorem B6482861 : Blo 1919435 6482861 := bstep (se 3 (by rfl) ⟨1215536, by rfl⟩ : syracuseStep 6482861 = 2431073) B2431073
theorem B4321907 : Blo 1919435 4321907 := bstep (se 1 (by rfl) ⟨3241430, by rfl⟩ : syracuseStep 4321907 = 6482861) B6482861
theorem B2881271 : Blo 1919435 2881271 := bstep (se 1 (by rfl) ⟨2160953, by rfl⟩ : syracuseStep 2881271 = 4321907) B4321907
theorem B1920847 : Blo 1919435 1920847 := bstep (se 1 (by rfl) ⟨1440635, by rfl⟩ : syracuseStep 1920847 = 2881271) B2881271
theorem B2881277 : Blo 1919435 2881277 := bbase (se 3 (by rfl) ⟨540239, by rfl⟩ : syracuseStep 2881277 = 1080479) (by norm_num)
theorem B1920851 : Blo 1919435 1920851 := bstep (se 1 (by rfl) ⟨1440638, by rfl⟩ : syracuseStep 1920851 = 2881277) B2881277
theorem B4321925 : Blo 1919435 4321925 := bbase (se 4 (by rfl) ⟨405180, by rfl⟩ : syracuseStep 4321925 = 810361) (by norm_num)
theorem B2881283 : Blo 1919435 2881283 := bstep (se 1 (by rfl) ⟨2160962, by rfl⟩ : syracuseStep 2881283 = 4321925) B4321925
theorem B1920855 : Blo 1919435 1920855 := bstep (se 1 (by rfl) ⟨1440641, by rfl⟩ : syracuseStep 1920855 = 2881283) B2881283
theorem B6237653 : Blo 1919435 6237653 := bbase (se 7 (by rfl) ⟨73097, by rfl⟩ : syracuseStep 6237653 = 146195) (by norm_num)
theorem B66534965 : Blo 1919435 66534965 := bstep (se 5 (by rfl) ⟨3118826, by rfl⟩ : syracuseStep 66534965 = 6237653) B6237653
theorem B44356643 : Blo 1919435 44356643 := bstep (se 1 (by rfl) ⟨33267482, by rfl⟩ : syracuseStep 44356643 = 66534965) B66534965
theorem B29571095 : Blo 1919435 29571095 := bstep (se 1 (by rfl) ⟨22178321, by rfl⟩ : syracuseStep 29571095 = 44356643) B44356643
theorem B19714063 : Blo 1919435 19714063 := bstep (se 1 (by rfl) ⟨14785547, by rfl⟩ : syracuseStep 19714063 = 29571095) B29571095
theorem B26285417 : Blo 1919435 26285417 := bstep (se 2 (by rfl) ⟨9857031, by rfl⟩ : syracuseStep 26285417 = 19714063) B19714063
theorem B17523611 : Blo 1919435 17523611 := bstep (se 1 (by rfl) ⟨13142708, by rfl⟩ : syracuseStep 17523611 = 26285417) B26285417
theorem B11682407 : Blo 1919435 11682407 := bstep (se 1 (by rfl) ⟨8761805, by rfl⟩ : syracuseStep 11682407 = 17523611) B17523611
theorem B31153085 : Blo 1919435 31153085 := bstep (se 3 (by rfl) ⟨5841203, by rfl⟩ : syracuseStep 31153085 = 11682407) B11682407
theorem B20768723 : Blo 1919435 20768723 := bstep (se 1 (by rfl) ⟨15576542, by rfl⟩ : syracuseStep 20768723 = 31153085) B31153085
theorem B13845815 : Blo 1919435 13845815 := bstep (se 1 (by rfl) ⟨10384361, by rfl⟩ : syracuseStep 13845815 = 20768723) B20768723
theorem B9230543 : Blo 1919435 9230543 := bstep (se 1 (by rfl) ⟨6922907, by rfl⟩ : syracuseStep 9230543 = 13845815) B13845815
theorem B6153695 : Blo 1919435 6153695 := bstep (se 1 (by rfl) ⟨4615271, by rfl⟩ : syracuseStep 6153695 = 9230543) B9230543
theorem B4102463 : Blo 1919435 4102463 := bstep (se 1 (by rfl) ⟨3076847, by rfl⟩ : syracuseStep 4102463 = 6153695) B6153695
theorem B2734975 : Blo 1919435 2734975 := bstep (se 1 (by rfl) ⟨2051231, by rfl⟩ : syracuseStep 2734975 = 4102463) B4102463
theorem B3646633 : Blo 1919435 3646633 := bstep (se 2 (by rfl) ⟨1367487, by rfl⟩ : syracuseStep 3646633 = 2734975) B2734975
theorem B4862177 : Blo 1919435 4862177 := bstep (se 2 (by rfl) ⟨1823316, by rfl⟩ : syracuseStep 4862177 = 3646633) B3646633
theorem B3241451 : Blo 1919435 3241451 := bstep (se 1 (by rfl) ⟨2431088, by rfl⟩ : syracuseStep 3241451 = 4862177) B4862177
theorem B2160967 : Blo 1919435 2160967 := bstep (se 1 (by rfl) ⟨1620725, by rfl⟩ : syracuseStep 2160967 = 3241451) B3241451
theorem B2881289 : Blo 1919435 2881289 := bstep (se 2 (by rfl) ⟨1080483, by rfl⟩ : syracuseStep 2881289 = 2160967) B2160967
theorem B1920859 : Blo 1919435 1920859 := bstep (se 1 (by rfl) ⟨1440644, by rfl⟩ : syracuseStep 1920859 = 2881289) B2881289
theorem B9724373 : Blo 1919435 9724373 := bbase (se 7 (by rfl) ⟨113957, by rfl⟩ : syracuseStep 9724373 = 227915) (by norm_num)
theorem B6482915 : Blo 1919435 6482915 := bstep (se 1 (by rfl) ⟨4862186, by rfl⟩ : syracuseStep 6482915 = 9724373) B9724373
theorem B4321943 : Blo 1919435 4321943 := bstep (se 1 (by rfl) ⟨3241457, by rfl⟩ : syracuseStep 4321943 = 6482915) B6482915
theorem B2881295 : Blo 1919435 2881295 := bstep (se 1 (by rfl) ⟨2160971, by rfl⟩ : syracuseStep 2881295 = 4321943) B4321943
theorem B1920863 : Blo 1919435 1920863 := bstep (se 1 (by rfl) ⟨1440647, by rfl⟩ : syracuseStep 1920863 = 2881295) B2881295
theorem B2881301 : Blo 1919435 2881301 := bbase (se 6 (by rfl) ⟨67530, by rfl⟩ : syracuseStep 2881301 = 135061) (by norm_num)
theorem B1920867 : Blo 1919435 1920867 := bstep (se 1 (by rfl) ⟨1440650, by rfl⟩ : syracuseStep 1920867 = 2881301) B2881301
theorem B2464273 : Blo 1919435 2464273 := bbase (se 2 (by rfl) ⟨924102, by rfl⟩ : syracuseStep 2464273 = 1848205) (by norm_num)
theorem B3285697 : Blo 1919435 3285697 := bstep (se 2 (by rfl) ⟨1232136, by rfl⟩ : syracuseStep 3285697 = 2464273) B2464273
theorem B4380929 : Blo 1919435 4380929 := bstep (se 2 (by rfl) ⟨1642848, by rfl⟩ : syracuseStep 4380929 = 3285697) B3285697
theorem B2920619 : Blo 1919435 2920619 := bstep (se 1 (by rfl) ⟨2190464, by rfl⟩ : syracuseStep 2920619 = 4380929) B4380929
theorem B7788317 : Blo 1919435 7788317 := bstep (se 3 (by rfl) ⟨1460309, by rfl⟩ : syracuseStep 7788317 = 2920619) B2920619
theorem B83075381 : Blo 1919435 83075381 := bstep (se 5 (by rfl) ⟨3894158, by rfl⟩ : syracuseStep 83075381 = 7788317) B7788317
theorem B55383587 : Blo 1919435 55383587 := bstep (se 1 (by rfl) ⟨41537690, by rfl⟩ : syracuseStep 55383587 = 83075381) B83075381
theorem B36922391 : Blo 1919435 36922391 := bstep (se 1 (by rfl) ⟨27691793, by rfl⟩ : syracuseStep 36922391 = 55383587) B55383587
theorem B24614927 : Blo 1919435 24614927 := bstep (se 1 (by rfl) ⟨18461195, by rfl⟩ : syracuseStep 24614927 = 36922391) B36922391
theorem B16409951 : Blo 1919435 16409951 := bstep (se 1 (by rfl) ⟨12307463, by rfl⟩ : syracuseStep 16409951 = 24614927) B24614927
theorem B10939967 : Blo 1919435 10939967 := bstep (se 1 (by rfl) ⟨8204975, by rfl⟩ : syracuseStep 10939967 = 16409951) B16409951
theorem B7293311 : Blo 1919435 7293311 := bstep (se 1 (by rfl) ⟨5469983, by rfl⟩ : syracuseStep 7293311 = 10939967) B10939967
theorem B4862207 : Blo 1919435 4862207 := bstep (se 1 (by rfl) ⟨3646655, by rfl⟩ : syracuseStep 4862207 = 7293311) B7293311
theorem B3241471 : Blo 1919435 3241471 := bstep (se 1 (by rfl) ⟨2431103, by rfl⟩ : syracuseStep 3241471 = 4862207) B4862207
theorem B4321961 : Blo 1919435 4321961 := bstep (se 2 (by rfl) ⟨1620735, by rfl⟩ : syracuseStep 4321961 = 3241471) B3241471
theorem B2881307 : Blo 1919435 2881307 := bstep (se 1 (by rfl) ⟨2160980, by rfl⟩ : syracuseStep 2881307 = 4321961) B4321961
theorem B1920871 : Blo 1919435 1920871 := bstep (se 1 (by rfl) ⟨1440653, by rfl⟩ : syracuseStep 1920871 = 2881307) B2881307
theorem B2160985 : Blo 1919435 2160985 := bbase (se 2 (by rfl) ⟨810369, by rfl⟩ : syracuseStep 2160985 = 1620739) (by norm_num)
theorem B2881313 : Blo 1919435 2881313 := bstep (se 2 (by rfl) ⟨1080492, by rfl⟩ : syracuseStep 2881313 = 2160985) B2160985
theorem B1920875 : Blo 1919435 1920875 := bstep (se 1 (by rfl) ⟨1440656, by rfl⟩ : syracuseStep 1920875 = 2881313) B2881313
theorem B10384469 : Blo 1919435 10384469 := bbase (se 8 (by rfl) ⟨60846, by rfl⟩ : syracuseStep 10384469 = 121693) (by norm_num)
theorem B6922979 : Blo 1919435 6922979 := bstep (se 1 (by rfl) ⟨5192234, by rfl⟩ : syracuseStep 6922979 = 10384469) B10384469
theorem B4615319 : Blo 1919435 4615319 := bstep (se 1 (by rfl) ⟨3461489, by rfl⟩ : syracuseStep 4615319 = 6922979) B6922979
theorem B3076879 : Blo 1919435 3076879 := bstep (se 1 (by rfl) ⟨2307659, by rfl⟩ : syracuseStep 3076879 = 4615319) B4615319
theorem B4102505 : Blo 1919435 4102505 := bstep (se 2 (by rfl) ⟨1538439, by rfl⟩ : syracuseStep 4102505 = 3076879) B3076879
theorem B2735003 : Blo 1919435 2735003 := bstep (se 1 (by rfl) ⟨2051252, by rfl⟩ : syracuseStep 2735003 = 4102505) B4102505
theorem B7293341 : Blo 1919435 7293341 := bstep (se 3 (by rfl) ⟨1367501, by rfl⟩ : syracuseStep 7293341 = 2735003) B2735003
theorem B4862227 : Blo 1919435 4862227 := bstep (se 1 (by rfl) ⟨3646670, by rfl⟩ : syracuseStep 4862227 = 7293341) B7293341
theorem B6482969 : Blo 1919435 6482969 := bstep (se 2 (by rfl) ⟨2431113, by rfl⟩ : syracuseStep 6482969 = 4862227) B4862227
theorem B4321979 : Blo 1919435 4321979 := bstep (se 1 (by rfl) ⟨3241484, by rfl⟩ : syracuseStep 4321979 = 6482969) B6482969
theorem B2881319 : Blo 1919435 2881319 := bstep (se 1 (by rfl) ⟨2160989, by rfl⟩ : syracuseStep 2881319 = 4321979) B4321979
theorem B1920879 : Blo 1919435 1920879 := bstep (se 1 (by rfl) ⟨1440659, by rfl⟩ : syracuseStep 1920879 = 2881319) B2881319
theorem B2881325 : Blo 1919435 2881325 := bbase (se 3 (by rfl) ⟨540248, by rfl⟩ : syracuseStep 2881325 = 1080497) (by norm_num)
theorem B1920883 : Blo 1919435 1920883 := bstep (se 1 (by rfl) ⟨1440662, by rfl⟩ : syracuseStep 1920883 = 2881325) B2881325
theorem B4321997 : Blo 1919435 4321997 := bbase (se 3 (by rfl) ⟨810374, by rfl⟩ : syracuseStep 4321997 = 1620749) (by norm_num)
theorem B2881331 : Blo 1919435 2881331 := bstep (se 1 (by rfl) ⟨2160998, by rfl⟩ : syracuseStep 2881331 = 4321997) B4321997
theorem B1920887 : Blo 1919435 1920887 := bstep (se 1 (by rfl) ⟨1440665, by rfl⟩ : syracuseStep 1920887 = 2881331) B2881331
theorem B2431129 : Blo 1919435 2431129 := bbase (se 2 (by rfl) ⟨911673, by rfl⟩ : syracuseStep 2431129 = 1823347) (by norm_num)
theorem B3241505 : Blo 1919435 3241505 := bstep (se 2 (by rfl) ⟨1215564, by rfl⟩ : syracuseStep 3241505 = 2431129) B2431129
theorem B2161003 : Blo 1919435 2161003 := bstep (se 1 (by rfl) ⟨1620752, by rfl⟩ : syracuseStep 2161003 = 3241505) B3241505
theorem B2881337 : Blo 1919435 2881337 := bstep (se 2 (by rfl) ⟨1080501, by rfl⟩ : syracuseStep 2881337 = 2161003) B2161003
theorem B1920891 : Blo 1919435 1920891 := bstep (se 1 (by rfl) ⟨1440668, by rfl⟩ : syracuseStep 1920891 = 2881337) B2881337
theorem B8205077 : Blo 1919435 8205077 := bbase (se 6 (by rfl) ⟨192306, by rfl⟩ : syracuseStep 8205077 = 384613) (by norm_num)
theorem B21880205 : Blo 1919435 21880205 := bstep (se 3 (by rfl) ⟨4102538, by rfl⟩ : syracuseStep 21880205 = 8205077) B8205077
theorem B14586803 : Blo 1919435 14586803 := bstep (se 1 (by rfl) ⟨10940102, by rfl⟩ : syracuseStep 14586803 = 21880205) B21880205
theorem B9724535 : Blo 1919435 9724535 := bstep (se 1 (by rfl) ⟨7293401, by rfl⟩ : syracuseStep 9724535 = 14586803) B14586803
theorem B6483023 : Blo 1919435 6483023 := bstep (se 1 (by rfl) ⟨4862267, by rfl⟩ : syracuseStep 6483023 = 9724535) B9724535
theorem B4322015 : Blo 1919435 4322015 := bstep (se 1 (by rfl) ⟨3241511, by rfl⟩ : syracuseStep 4322015 = 6483023) B6483023
theorem B2881343 : Blo 1919435 2881343 := bstep (se 1 (by rfl) ⟨2161007, by rfl⟩ : syracuseStep 2881343 = 4322015) B4322015
theorem B1920895 : Blo 1919435 1920895 := bstep (se 1 (by rfl) ⟨1440671, by rfl⟩ : syracuseStep 1920895 = 2881343) B2881343
theorem B2881349 : Blo 1919435 2881349 := bbase (se 4 (by rfl) ⟨270126, by rfl⟩ : syracuseStep 2881349 = 540253) (by norm_num)
theorem B1920899 : Blo 1919435 1920899 := bstep (se 1 (by rfl) ⟨1440674, by rfl⟩ : syracuseStep 1920899 = 2881349) B2881349
theorem B3241525 : Blo 1919435 3241525 := bbase (se 5 (by rfl) ⟨151946, by rfl⟩ : syracuseStep 3241525 = 303893) (by norm_num)
theorem B4322033 : Blo 1919435 4322033 := bstep (se 2 (by rfl) ⟨1620762, by rfl⟩ : syracuseStep 4322033 = 3241525) B3241525
theorem B2881355 : Blo 1919435 2881355 := bstep (se 1 (by rfl) ⟨2161016, by rfl⟩ : syracuseStep 2881355 = 4322033) B4322033
theorem B1920903 : Blo 1919435 1920903 := bstep (se 1 (by rfl) ⟨1440677, by rfl⟩ : syracuseStep 1920903 = 2881355) B2881355
theorem B2161021 : Blo 1919435 2161021 := bbase (se 3 (by rfl) ⟨405191, by rfl⟩ : syracuseStep 2161021 = 810383) (by norm_num)
theorem B2881361 : Blo 1919435 2881361 := bstep (se 2 (by rfl) ⟨1080510, by rfl⟩ : syracuseStep 2881361 = 2161021) B2161021
theorem B1920907 : Blo 1919435 1920907 := bstep (se 1 (by rfl) ⟨1440680, by rfl⟩ : syracuseStep 1920907 = 2881361) B2881361
theorem B6483077 : Blo 1919435 6483077 := bbase (se 4 (by rfl) ⟨607788, by rfl⟩ : syracuseStep 6483077 = 1215577) (by norm_num)
theorem B4322051 : Blo 1919435 4322051 := bstep (se 1 (by rfl) ⟨3241538, by rfl⟩ : syracuseStep 4322051 = 6483077) B6483077
theorem B2881367 : Blo 1919435 2881367 := bstep (se 1 (by rfl) ⟨2161025, by rfl⟩ : syracuseStep 2881367 = 4322051) B4322051
theorem B1920911 : Blo 1919435 1920911 := bstep (se 1 (by rfl) ⟨1440683, by rfl⟩ : syracuseStep 1920911 = 2881367) B2881367
theorem B2881373 : Blo 1919435 2881373 := bbase (se 3 (by rfl) ⟨540257, by rfl⟩ : syracuseStep 2881373 = 1080515) (by norm_num)
theorem B1920915 : Blo 1919435 1920915 := bstep (se 1 (by rfl) ⟨1440686, by rfl⟩ : syracuseStep 1920915 = 2881373) B2881373
theorem B4322069 : Blo 1919435 4322069 := bbase (se 6 (by rfl) ⟨101298, by rfl⟩ : syracuseStep 4322069 = 202597) (by norm_num)
theorem B2881379 : Blo 1919435 2881379 := bstep (se 1 (by rfl) ⟨2161034, by rfl⟩ : syracuseStep 2881379 = 4322069) B4322069
theorem B1920919 : Blo 1919435 1920919 := bstep (se 1 (by rfl) ⟨1440689, by rfl⟩ : syracuseStep 1920919 = 2881379) B2881379
theorem B7293509 : Blo 1919435 7293509 := bbase (se 4 (by rfl) ⟨683766, by rfl⟩ : syracuseStep 7293509 = 1367533) (by norm_num)
theorem B4862339 : Blo 1919435 4862339 := bstep (se 1 (by rfl) ⟨3646754, by rfl⟩ : syracuseStep 4862339 = 7293509) B7293509
theorem B3241559 : Blo 1919435 3241559 := bstep (se 1 (by rfl) ⟨2431169, by rfl⟩ : syracuseStep 3241559 = 4862339) B4862339
theorem B2161039 : Blo 1919435 2161039 := bstep (se 1 (by rfl) ⟨1620779, by rfl⟩ : syracuseStep 2161039 = 3241559) B3241559
theorem B2881385 : Blo 1919435 2881385 := bstep (se 2 (by rfl) ⟨1080519, by rfl⟩ : syracuseStep 2881385 = 2161039) B2161039
theorem B1920923 : Blo 1919435 1920923 := bstep (se 1 (by rfl) ⟨1440692, by rfl⟩ : syracuseStep 1920923 = 2881385) B2881385
theorem B2464345 : Blo 1919435 2464345 := bbase (se 2 (by rfl) ⟨924129, by rfl⟩ : syracuseStep 2464345 = 1848259) (by norm_num)
theorem B3285793 : Blo 1919435 3285793 := bstep (se 2 (by rfl) ⟨1232172, by rfl⟩ : syracuseStep 3285793 = 2464345) B2464345
theorem B4381057 : Blo 1919435 4381057 := bstep (se 2 (by rfl) ⟨1642896, by rfl⟩ : syracuseStep 4381057 = 3285793) B3285793
theorem B5841409 : Blo 1919435 5841409 := bstep (se 2 (by rfl) ⟨2190528, by rfl⟩ : syracuseStep 5841409 = 4381057) B4381057
theorem B7788545 : Blo 1919435 7788545 := bstep (se 2 (by rfl) ⟨2920704, by rfl⟩ : syracuseStep 7788545 = 5841409) B5841409
theorem B5192363 : Blo 1919435 5192363 := bstep (se 1 (by rfl) ⟨3894272, by rfl⟩ : syracuseStep 5192363 = 7788545) B7788545
theorem B13846301 : Blo 1919435 13846301 := bstep (se 3 (by rfl) ⟨2596181, by rfl⟩ : syracuseStep 13846301 = 5192363) B5192363
theorem B9230867 : Blo 1919435 9230867 := bstep (se 1 (by rfl) ⟨6923150, by rfl⟩ : syracuseStep 9230867 = 13846301) B13846301
theorem B6153911 : Blo 1919435 6153911 := bstep (se 1 (by rfl) ⟨4615433, by rfl⟩ : syracuseStep 6153911 = 9230867) B9230867
theorem B4102607 : Blo 1919435 4102607 := bstep (se 1 (by rfl) ⟨3076955, by rfl⟩ : syracuseStep 4102607 = 6153911) B6153911
theorem B10940285 : Blo 1919435 10940285 := bstep (se 3 (by rfl) ⟨2051303, by rfl⟩ : syracuseStep 10940285 = 4102607) B4102607
theorem B7293523 : Blo 1919435 7293523 := bstep (se 1 (by rfl) ⟨5470142, by rfl⟩ : syracuseStep 7293523 = 10940285) B10940285
theorem B9724697 : Blo 1919435 9724697 := bstep (se 2 (by rfl) ⟨3646761, by rfl⟩ : syracuseStep 9724697 = 7293523) B7293523
theorem B6483131 : Blo 1919435 6483131 := bstep (se 1 (by rfl) ⟨4862348, by rfl⟩ : syracuseStep 6483131 = 9724697) B9724697
theorem B4322087 : Blo 1919435 4322087 := bstep (se 1 (by rfl) ⟨3241565, by rfl⟩ : syracuseStep 4322087 = 6483131) B6483131
theorem B2881391 : Blo 1919435 2881391 := bstep (se 1 (by rfl) ⟨2161043, by rfl⟩ : syracuseStep 2881391 = 4322087) B4322087
theorem B1920927 : Blo 1919435 1920927 := bstep (se 1 (by rfl) ⟨1440695, by rfl⟩ : syracuseStep 1920927 = 2881391) B2881391
theorem B2881397 : Blo 1919435 2881397 := bbase (se 5 (by rfl) ⟨135065, by rfl⟩ : syracuseStep 2881397 = 270131) (by norm_num)
theorem B1920931 : Blo 1919435 1920931 := bstep (se 1 (by rfl) ⟨1440698, by rfl⟩ : syracuseStep 1920931 = 2881397) B2881397
theorem B7788581 : Blo 1919435 7788581 := bbase (se 4 (by rfl) ⟨730179, by rfl⟩ : syracuseStep 7788581 = 1460359) (by norm_num)
theorem B5192387 : Blo 1919435 5192387 := bstep (se 1 (by rfl) ⟨3894290, by rfl⟩ : syracuseStep 5192387 = 7788581) B7788581
theorem B3461591 : Blo 1919435 3461591 := bstep (se 1 (by rfl) ⟨2596193, by rfl⟩ : syracuseStep 3461591 = 5192387) B5192387
theorem B2307727 : Blo 1919435 2307727 := bstep (se 1 (by rfl) ⟨1730795, by rfl⟩ : syracuseStep 2307727 = 3461591) B3461591
theorem B3076969 : Blo 1919435 3076969 := bstep (se 2 (by rfl) ⟨1153863, by rfl⟩ : syracuseStep 3076969 = 2307727) B2307727
theorem B4102625 : Blo 1919435 4102625 := bstep (se 2 (by rfl) ⟨1538484, by rfl⟩ : syracuseStep 4102625 = 3076969) B3076969
theorem B2735083 : Blo 1919435 2735083 := bstep (se 1 (by rfl) ⟨2051312, by rfl⟩ : syracuseStep 2735083 = 4102625) B4102625
theorem B3646777 : Blo 1919435 3646777 := bstep (se 2 (by rfl) ⟨1367541, by rfl⟩ : syracuseStep 3646777 = 2735083) B2735083
theorem B4862369 : Blo 1919435 4862369 := bstep (se 2 (by rfl) ⟨1823388, by rfl⟩ : syracuseStep 4862369 = 3646777) B3646777
theorem B3241579 : Blo 1919435 3241579 := bstep (se 1 (by rfl) ⟨2431184, by rfl⟩ : syracuseStep 3241579 = 4862369) B4862369
theorem B4322105 : Blo 1919435 4322105 := bstep (se 2 (by rfl) ⟨1620789, by rfl⟩ : syracuseStep 4322105 = 3241579) B3241579
theorem B2881403 : Blo 1919435 2881403 := bstep (se 1 (by rfl) ⟨2161052, by rfl⟩ : syracuseStep 2881403 = 4322105) B4322105
theorem B1920935 : Blo 1919435 1920935 := bstep (se 1 (by rfl) ⟨1440701, by rfl⟩ : syracuseStep 1920935 = 2881403) B2881403
theorem B2161057 : Blo 1919435 2161057 := bbase (se 2 (by rfl) ⟨810396, by rfl⟩ : syracuseStep 2161057 = 1620793) (by norm_num)
theorem B2881409 : Blo 1919435 2881409 := bstep (se 2 (by rfl) ⟨1080528, by rfl⟩ : syracuseStep 2881409 = 2161057) B2161057
theorem B1920939 : Blo 1919435 1920939 := bstep (se 1 (by rfl) ⟨1440704, by rfl⟩ : syracuseStep 1920939 = 2881409) B2881409
theorem B4862389 : Blo 1919435 4862389 := bbase (se 5 (by rfl) ⟨227924, by rfl⟩ : syracuseStep 4862389 = 455849) (by norm_num)
theorem B6483185 : Blo 1919435 6483185 := bstep (se 2 (by rfl) ⟨2431194, by rfl⟩ : syracuseStep 6483185 = 4862389) B4862389
theorem B4322123 : Blo 1919435 4322123 := bstep (se 1 (by rfl) ⟨3241592, by rfl⟩ : syracuseStep 4322123 = 6483185) B6483185
theorem B2881415 : Blo 1919435 2881415 := bstep (se 1 (by rfl) ⟨2161061, by rfl⟩ : syracuseStep 2881415 = 4322123) B4322123
theorem B1920943 : Blo 1919435 1920943 := bstep (se 1 (by rfl) ⟨1440707, by rfl⟩ : syracuseStep 1920943 = 2881415) B2881415
theorem B2881421 : Blo 1919435 2881421 := bbase (se 3 (by rfl) ⟨540266, by rfl⟩ : syracuseStep 2881421 = 1080533) (by norm_num)
theorem B1920947 : Blo 1919435 1920947 := bstep (se 1 (by rfl) ⟨1440710, by rfl⟩ : syracuseStep 1920947 = 2881421) B2881421
theorem B4322141 : Blo 1919435 4322141 := bbase (se 3 (by rfl) ⟨810401, by rfl⟩ : syracuseStep 4322141 = 1620803) (by norm_num)
theorem B2881427 : Blo 1919435 2881427 := bstep (se 1 (by rfl) ⟨2161070, by rfl⟩ : syracuseStep 2881427 = 4322141) B4322141
theorem B1920951 : Blo 1919435 1920951 := bstep (se 1 (by rfl) ⟨1440713, by rfl⟩ : syracuseStep 1920951 = 2881427) B2881427
theorem B3241613 : Blo 1919435 3241613 := bbase (se 3 (by rfl) ⟨607802, by rfl⟩ : syracuseStep 3241613 = 1215605) (by norm_num)
theorem B2161075 : Blo 1919435 2161075 := bstep (se 1 (by rfl) ⟨1620806, by rfl⟩ : syracuseStep 2161075 = 3241613) B3241613
theorem B2881433 : Blo 1919435 2881433 := bstep (se 2 (by rfl) ⟨1080537, by rfl⟩ : syracuseStep 2881433 = 2161075) B2161075
theorem B1920955 : Blo 1919435 1920955 := bstep (se 1 (by rfl) ⟨1440716, by rfl⟩ : syracuseStep 1920955 = 2881433) B2881433
theorem B1947169 : Blo 1919435 1947169 := bbase (se 2 (by rfl) ⟨730188, by rfl⟩ : syracuseStep 1947169 = 1460377) (by norm_num)
theorem B2596225 : Blo 1919435 2596225 := bstep (se 2 (by rfl) ⟨973584, by rfl⟩ : syracuseStep 2596225 = 1947169) B1947169
theorem B3461633 : Blo 1919435 3461633 := bstep (se 2 (by rfl) ⟨1298112, by rfl⟩ : syracuseStep 3461633 = 2596225) B2596225
theorem B2307755 : Blo 1919435 2307755 := bstep (se 1 (by rfl) ⟨1730816, by rfl⟩ : syracuseStep 2307755 = 3461633) B3461633
theorem B6154013 : Blo 1919435 6154013 := bstep (se 3 (by rfl) ⟨1153877, by rfl⟩ : syracuseStep 6154013 = 2307755) B2307755
theorem B16410701 : Blo 1919435 16410701 := bstep (se 3 (by rfl) ⟨3077006, by rfl⟩ : syracuseStep 16410701 = 6154013) B6154013
theorem B10940467 : Blo 1919435 10940467 := bstep (se 1 (by rfl) ⟨8205350, by rfl⟩ : syracuseStep 10940467 = 16410701) B16410701
theorem B14587289 : Blo 1919435 14587289 := bstep (se 2 (by rfl) ⟨5470233, by rfl⟩ : syracuseStep 14587289 = 10940467) B10940467
theorem B9724859 : Blo 1919435 9724859 := bstep (se 1 (by rfl) ⟨7293644, by rfl⟩ : syracuseStep 9724859 = 14587289) B14587289
theorem B6483239 : Blo 1919435 6483239 := bstep (se 1 (by rfl) ⟨4862429, by rfl⟩ : syracuseStep 6483239 = 9724859) B9724859
theorem B4322159 : Blo 1919435 4322159 := bstep (se 1 (by rfl) ⟨3241619, by rfl⟩ : syracuseStep 4322159 = 6483239) B6483239
theorem B2881439 : Blo 1919435 2881439 := bstep (se 1 (by rfl) ⟨2161079, by rfl⟩ : syracuseStep 2881439 = 4322159) B4322159
theorem B1920959 : Blo 1919435 1920959 := bstep (se 1 (by rfl) ⟨1440719, by rfl⟩ : syracuseStep 1920959 = 2881439) B2881439
theorem B2881445 : Blo 1919435 2881445 := bbase (se 4 (by rfl) ⟨270135, by rfl⟩ : syracuseStep 2881445 = 540271) (by norm_num)
theorem B1920963 : Blo 1919435 1920963 := bstep (se 1 (by rfl) ⟨1440722, by rfl⟩ : syracuseStep 1920963 = 2881445) B2881445
theorem B2431225 : Blo 1919435 2431225 := bbase (se 2 (by rfl) ⟨911709, by rfl⟩ : syracuseStep 2431225 = 1823419) (by norm_num)
theorem B3241633 : Blo 1919435 3241633 := bstep (se 2 (by rfl) ⟨1215612, by rfl⟩ : syracuseStep 3241633 = 2431225) B2431225
theorem B4322177 : Blo 1919435 4322177 := bstep (se 2 (by rfl) ⟨1620816, by rfl⟩ : syracuseStep 4322177 = 3241633) B3241633
theorem B2881451 : Blo 1919435 2881451 := bstep (se 1 (by rfl) ⟨2161088, by rfl⟩ : syracuseStep 2881451 = 4322177) B4322177
theorem B1920967 : Blo 1919435 1920967 := bstep (se 1 (by rfl) ⟨1440725, by rfl⟩ : syracuseStep 1920967 = 2881451) B2881451
theorem B2161093 : Blo 1919435 2161093 := bbase (se 4 (by rfl) ⟨202602, by rfl⟩ : syracuseStep 2161093 = 405205) (by norm_num)
theorem B2881457 : Blo 1919435 2881457 := bstep (se 2 (by rfl) ⟨1080546, by rfl⟩ : syracuseStep 2881457 = 2161093) B2161093
theorem B1920971 : Blo 1919435 1920971 := bstep (se 1 (by rfl) ⟨1440728, by rfl⟩ : syracuseStep 1920971 = 2881457) B2881457
theorem B3646853 : Blo 1919435 3646853 := bbase (se 4 (by rfl) ⟨341892, by rfl⟩ : syracuseStep 3646853 = 683785) (by norm_num)
theorem B2431235 : Blo 1919435 2431235 := bstep (se 1 (by rfl) ⟨1823426, by rfl⟩ : syracuseStep 2431235 = 3646853) B3646853
theorem B6483293 : Blo 1919435 6483293 := bstep (se 3 (by rfl) ⟨1215617, by rfl⟩ : syracuseStep 6483293 = 2431235) B2431235
theorem B4322195 : Blo 1919435 4322195 := bstep (se 1 (by rfl) ⟨3241646, by rfl⟩ : syracuseStep 4322195 = 6483293) B6483293
theorem B2881463 : Blo 1919435 2881463 := bstep (se 1 (by rfl) ⟨2161097, by rfl⟩ : syracuseStep 2881463 = 4322195) B4322195
theorem B1920975 : Blo 1919435 1920975 := bstep (se 1 (by rfl) ⟨1440731, by rfl⟩ : syracuseStep 1920975 = 2881463) B2881463
theorem B2881469 : Blo 1919435 2881469 := bbase (se 3 (by rfl) ⟨540275, by rfl⟩ : syracuseStep 2881469 = 1080551) (by norm_num)
theorem B1920979 : Blo 1919435 1920979 := bstep (se 1 (by rfl) ⟨1440734, by rfl⟩ : syracuseStep 1920979 = 2881469) B2881469
theorem B4322213 : Blo 1919435 4322213 := bbase (se 4 (by rfl) ⟨405207, by rfl⟩ : syracuseStep 4322213 = 810415) (by norm_num)
theorem B2881475 : Blo 1919435 2881475 := bstep (se 1 (by rfl) ⟨2161106, by rfl⟩ : syracuseStep 2881475 = 4322213) B4322213
theorem B1920983 : Blo 1919435 1920983 := bstep (se 1 (by rfl) ⟨1440737, by rfl⟩ : syracuseStep 1920983 = 2881475) B2881475
theorem B4862501 : Blo 1919435 4862501 := bbase (se 4 (by rfl) ⟨455859, by rfl⟩ : syracuseStep 4862501 = 911719) (by norm_num)
theorem B3241667 : Blo 1919435 3241667 := bstep (se 1 (by rfl) ⟨2431250, by rfl⟩ : syracuseStep 3241667 = 4862501) B4862501
theorem B2161111 : Blo 1919435 2161111 := bstep (se 1 (by rfl) ⟨1620833, by rfl⟩ : syracuseStep 2161111 = 3241667) B3241667
theorem B2881481 : Blo 1919435 2881481 := bstep (se 2 (by rfl) ⟨1080555, by rfl⟩ : syracuseStep 2881481 = 2161111) B2161111
theorem B1920987 : Blo 1919435 1920987 := bstep (se 1 (by rfl) ⟨1440740, by rfl⟩ : syracuseStep 1920987 = 2881481) B2881481
theorem B5470325 : Blo 1919435 5470325 := bbase (se 5 (by rfl) ⟨256421, by rfl⟩ : syracuseStep 5470325 = 512843) (by norm_num)
theorem B3646883 : Blo 1919435 3646883 := bstep (se 1 (by rfl) ⟨2735162, by rfl⟩ : syracuseStep 3646883 = 5470325) B5470325
theorem B9725021 : Blo 1919435 9725021 := bstep (se 3 (by rfl) ⟨1823441, by rfl⟩ : syracuseStep 9725021 = 3646883) B3646883
theorem B6483347 : Blo 1919435 6483347 := bstep (se 1 (by rfl) ⟨4862510, by rfl⟩ : syracuseStep 6483347 = 9725021) B9725021
theorem B4322231 : Blo 1919435 4322231 := bstep (se 1 (by rfl) ⟨3241673, by rfl⟩ : syracuseStep 4322231 = 6483347) B6483347
theorem B2881487 : Blo 1919435 2881487 := bstep (se 1 (by rfl) ⟨2161115, by rfl⟩ : syracuseStep 2881487 = 4322231) B4322231
theorem B1920991 : Blo 1919435 1920991 := bstep (se 1 (by rfl) ⟨1440743, by rfl⟩ : syracuseStep 1920991 = 2881487) B2881487
theorem B2881493 : Blo 1919435 2881493 := bbase (se 7 (by rfl) ⟨33767, by rfl⟩ : syracuseStep 2881493 = 67535) (by norm_num)
theorem B1920995 : Blo 1919435 1920995 := bstep (se 1 (by rfl) ⟨1440746, by rfl⟩ : syracuseStep 1920995 = 2881493) B2881493
theorem B7293797 : Blo 1919435 7293797 := bbase (se 4 (by rfl) ⟨683793, by rfl⟩ : syracuseStep 7293797 = 1367587) (by norm_num)
theorem B4862531 : Blo 1919435 4862531 := bstep (se 1 (by rfl) ⟨3646898, by rfl⟩ : syracuseStep 4862531 = 7293797) B7293797
theorem B3241687 : Blo 1919435 3241687 := bstep (se 1 (by rfl) ⟨2431265, by rfl⟩ : syracuseStep 3241687 = 4862531) B4862531
theorem B4322249 : Blo 1919435 4322249 := bstep (se 2 (by rfl) ⟨1620843, by rfl⟩ : syracuseStep 4322249 = 3241687) B3241687
theorem B2881499 : Blo 1919435 2881499 := bstep (se 1 (by rfl) ⟨2161124, by rfl⟩ : syracuseStep 2881499 = 4322249) B4322249
theorem B1920999 : Blo 1919435 1920999 := bstep (se 1 (by rfl) ⟨1440749, by rfl⟩ : syracuseStep 1920999 = 2881499) B2881499
theorem B2161129 : Blo 1919435 2161129 := bbase (se 2 (by rfl) ⟨810423, by rfl⟩ : syracuseStep 2161129 = 1620847) (by norm_num)
theorem B2881505 : Blo 1919435 2881505 := bstep (se 2 (by rfl) ⟨1080564, by rfl⟩ : syracuseStep 2881505 = 2161129) B2161129
theorem B1921003 : Blo 1919435 1921003 := bstep (se 1 (by rfl) ⟨1440752, by rfl⟩ : syracuseStep 1921003 = 2881505) B2881505
theorem B2051389 : Blo 1919435 2051389 := bbase (se 3 (by rfl) ⟨384635, by rfl⟩ : syracuseStep 2051389 = 769271) (by norm_num)
theorem B10940741 : Blo 1919435 10940741 := bstep (se 4 (by rfl) ⟨1025694, by rfl⟩ : syracuseStep 10940741 = 2051389) B2051389
theorem B7293827 : Blo 1919435 7293827 := bstep (se 1 (by rfl) ⟨5470370, by rfl⟩ : syracuseStep 7293827 = 10940741) B10940741
theorem B4862551 : Blo 1919435 4862551 := bstep (se 1 (by rfl) ⟨3646913, by rfl⟩ : syracuseStep 4862551 = 7293827) B7293827
theorem B6483401 : Blo 1919435 6483401 := bstep (se 2 (by rfl) ⟨2431275, by rfl⟩ : syracuseStep 6483401 = 4862551) B4862551
theorem B4322267 : Blo 1919435 4322267 := bstep (se 1 (by rfl) ⟨3241700, by rfl⟩ : syracuseStep 4322267 = 6483401) B6483401
theorem B2881511 : Blo 1919435 2881511 := bstep (se 1 (by rfl) ⟨2161133, by rfl⟩ : syracuseStep 2881511 = 4322267) B4322267
theorem B1921007 : Blo 1919435 1921007 := bstep (se 1 (by rfl) ⟨1440755, by rfl⟩ : syracuseStep 1921007 = 2881511) B2881511
theorem B2881517 : Blo 1919435 2881517 := bbase (se 3 (by rfl) ⟨540284, by rfl⟩ : syracuseStep 2881517 = 1080569) (by norm_num)
theorem B1921011 : Blo 1919435 1921011 := bstep (se 1 (by rfl) ⟨1440758, by rfl⟩ : syracuseStep 1921011 = 2881517) B2881517
theorem B4322285 : Blo 1919435 4322285 := bbase (se 3 (by rfl) ⟨810428, by rfl⟩ : syracuseStep 4322285 = 1620857) (by norm_num)
theorem B2881523 : Blo 1919435 2881523 := bstep (se 1 (by rfl) ⟨2161142, by rfl⟩ : syracuseStep 2881523 = 4322285) B4322285
theorem B1921015 : Blo 1919435 1921015 := bstep (se 1 (by rfl) ⟨1440761, by rfl⟩ : syracuseStep 1921015 = 2881523) B2881523
theorem B4102805 : Blo 1919435 4102805 := bbase (se 6 (by rfl) ⟨96159, by rfl⟩ : syracuseStep 4102805 = 192319) (by norm_num)
theorem B2735203 : Blo 1919435 2735203 := bstep (se 1 (by rfl) ⟨2051402, by rfl⟩ : syracuseStep 2735203 = 4102805) B4102805
theorem B3646937 : Blo 1919435 3646937 := bstep (se 2 (by rfl) ⟨1367601, by rfl⟩ : syracuseStep 3646937 = 2735203) B2735203
theorem B2431291 : Blo 1919435 2431291 := bstep (se 1 (by rfl) ⟨1823468, by rfl⟩ : syracuseStep 2431291 = 3646937) B3646937
theorem B3241721 : Blo 1919435 3241721 := bstep (se 2 (by rfl) ⟨1215645, by rfl⟩ : syracuseStep 3241721 = 2431291) B2431291
theorem B2161147 : Blo 1919435 2161147 := bstep (se 1 (by rfl) ⟨1620860, by rfl⟩ : syracuseStep 2161147 = 3241721) B3241721
theorem B2881529 : Blo 1919435 2881529 := bstep (se 2 (by rfl) ⟨1080573, by rfl⟩ : syracuseStep 2881529 = 2161147) B2161147
theorem B1921019 : Blo 1919435 1921019 := bstep (se 1 (by rfl) ⟨1440764, by rfl⟩ : syracuseStep 1921019 = 2881529) B2881529
theorem B44360405 : Blo 1919435 44360405 := bbase (se 7 (by rfl) ⟨519848, by rfl⟩ : syracuseStep 44360405 = 1039697) (by norm_num)
theorem B29573603 : Blo 1919435 29573603 := bstep (se 1 (by rfl) ⟨22180202, by rfl⟩ : syracuseStep 29573603 = 44360405) B44360405
theorem B19715735 : Blo 1919435 19715735 := bstep (se 1 (by rfl) ⟨14786801, by rfl⟩ : syracuseStep 19715735 = 29573603) B29573603
theorem B52575293 : Blo 1919435 52575293 := bstep (se 3 (by rfl) ⟨9857867, by rfl⟩ : syracuseStep 52575293 = 19715735) B19715735
theorem B35050195 : Blo 1919435 35050195 := bstep (se 1 (by rfl) ⟨26287646, by rfl⟩ : syracuseStep 35050195 = 52575293) B52575293
theorem B46733593 : Blo 1919435 46733593 := bstep (se 2 (by rfl) ⟨17525097, by rfl⟩ : syracuseStep 46733593 = 35050195) B35050195
theorem B62311457 : Blo 1919435 62311457 := bstep (se 2 (by rfl) ⟨23366796, by rfl⟩ : syracuseStep 62311457 = 46733593) B46733593
theorem B166163885 : Blo 1919435 166163885 := bstep (se 3 (by rfl) ⟨31155728, by rfl⟩ : syracuseStep 166163885 = 62311457) B62311457
theorem B110775923 : Blo 1919435 110775923 := bstep (se 1 (by rfl) ⟨83081942, by rfl⟩ : syracuseStep 110775923 = 166163885) B166163885
theorem B73850615 : Blo 1919435 73850615 := bstep (se 1 (by rfl) ⟨55387961, by rfl⟩ : syracuseStep 73850615 = 110775923) B110775923
theorem B49233743 : Blo 1919435 49233743 := bstep (se 1 (by rfl) ⟨36925307, by rfl⟩ : syracuseStep 49233743 = 73850615) B73850615
theorem B32822495 : Blo 1919435 32822495 := bstep (se 1 (by rfl) ⟨24616871, by rfl⟩ : syracuseStep 32822495 = 49233743) B49233743
theorem B21881663 : Blo 1919435 21881663 := bstep (se 1 (by rfl) ⟨16411247, by rfl⟩ : syracuseStep 21881663 = 32822495) B32822495
theorem B14587775 : Blo 1919435 14587775 := bstep (se 1 (by rfl) ⟨10940831, by rfl⟩ : syracuseStep 14587775 = 21881663) B21881663
theorem B9725183 : Blo 1919435 9725183 := bstep (se 1 (by rfl) ⟨7293887, by rfl⟩ : syracuseStep 9725183 = 14587775) B14587775
theorem B6483455 : Blo 1919435 6483455 := bstep (se 1 (by rfl) ⟨4862591, by rfl⟩ : syracuseStep 6483455 = 9725183) B9725183
theorem B4322303 : Blo 1919435 4322303 := bstep (se 1 (by rfl) ⟨3241727, by rfl⟩ : syracuseStep 4322303 = 6483455) B6483455
theorem B2881535 : Blo 1919435 2881535 := bstep (se 1 (by rfl) ⟨2161151, by rfl⟩ : syracuseStep 2881535 = 4322303) B4322303
theorem B1921023 : Blo 1919435 1921023 := bstep (se 1 (by rfl) ⟨1440767, by rfl⟩ : syracuseStep 1921023 = 2881535) B2881535
theorem B2881541 : Blo 1919435 2881541 := bbase (se 4 (by rfl) ⟨270144, by rfl⟩ : syracuseStep 2881541 = 540289) (by norm_num)
theorem B1921027 : Blo 1919435 1921027 := bstep (se 1 (by rfl) ⟨1440770, by rfl⟩ : syracuseStep 1921027 = 2881541) B2881541
theorem B3241741 : Blo 1919435 3241741 := bbase (se 3 (by rfl) ⟨607826, by rfl⟩ : syracuseStep 3241741 = 1215653) (by norm_num)
theorem B4322321 : Blo 1919435 4322321 := bstep (se 2 (by rfl) ⟨1620870, by rfl⟩ : syracuseStep 4322321 = 3241741) B3241741
theorem B2881547 : Blo 1919435 2881547 := bstep (se 1 (by rfl) ⟨2161160, by rfl⟩ : syracuseStep 2881547 = 4322321) B4322321
theorem B1921031 : Blo 1919435 1921031 := bstep (se 1 (by rfl) ⟨1440773, by rfl⟩ : syracuseStep 1921031 = 2881547) B2881547
theorem B2161165 : Blo 1919435 2161165 := bbase (se 3 (by rfl) ⟨405218, by rfl⟩ : syracuseStep 2161165 = 810437) (by norm_num)
theorem B2881553 : Blo 1919435 2881553 := bstep (se 2 (by rfl) ⟨1080582, by rfl⟩ : syracuseStep 2881553 = 2161165) B2161165
theorem B1921035 : Blo 1919435 1921035 := bstep (se 1 (by rfl) ⟨1440776, by rfl⟩ : syracuseStep 1921035 = 2881553) B2881553
theorem B6483509 : Blo 1919435 6483509 := bbase (se 5 (by rfl) ⟨303914, by rfl⟩ : syracuseStep 6483509 = 607829) (by norm_num)
theorem B4322339 : Blo 1919435 4322339 := bstep (se 1 (by rfl) ⟨3241754, by rfl⟩ : syracuseStep 4322339 = 6483509) B6483509
theorem B2881559 : Blo 1919435 2881559 := bstep (se 1 (by rfl) ⟨2161169, by rfl⟩ : syracuseStep 2881559 = 4322339) B4322339
theorem B1921039 : Blo 1919435 1921039 := bstep (se 1 (by rfl) ⟨1440779, by rfl⟩ : syracuseStep 1921039 = 2881559) B2881559
theorem B2881565 : Blo 1919435 2881565 := bbase (se 3 (by rfl) ⟨540293, by rfl⟩ : syracuseStep 2881565 = 1080587) (by norm_num)
theorem B1921043 : Blo 1919435 1921043 := bstep (se 1 (by rfl) ⟨1440782, by rfl⟩ : syracuseStep 1921043 = 2881565) B2881565
theorem B4322357 : Blo 1919435 4322357 := bbase (se 5 (by rfl) ⟨202610, by rfl⟩ : syracuseStep 4322357 = 405221) (by norm_num)
theorem B2881571 : Blo 1919435 2881571 := bstep (se 1 (by rfl) ⟨2161178, by rfl⟩ : syracuseStep 2881571 = 4322357) B4322357
theorem B1921047 : Blo 1919435 1921047 := bstep (se 1 (by rfl) ⟨1440785, by rfl⟩ : syracuseStep 1921047 = 2881571) B2881571
theorem B6154309 : Blo 1919435 6154309 := bbase (se 4 (by rfl) ⟨576966, by rfl⟩ : syracuseStep 6154309 = 1153933) (by norm_num)
theorem B8205745 : Blo 1919435 8205745 := bstep (se 2 (by rfl) ⟨3077154, by rfl⟩ : syracuseStep 8205745 = 6154309) B6154309
theorem B10940993 : Blo 1919435 10940993 := bstep (se 2 (by rfl) ⟨4102872, by rfl⟩ : syracuseStep 10940993 = 8205745) B8205745
theorem B7293995 : Blo 1919435 7293995 := bstep (se 1 (by rfl) ⟨5470496, by rfl⟩ : syracuseStep 7293995 = 10940993) B10940993
theorem B4862663 : Blo 1919435 4862663 := bstep (se 1 (by rfl) ⟨3646997, by rfl⟩ : syracuseStep 4862663 = 7293995) B7293995
theorem B3241775 : Blo 1919435 3241775 := bstep (se 1 (by rfl) ⟨2431331, by rfl⟩ : syracuseStep 3241775 = 4862663) B4862663
theorem B2161183 : Blo 1919435 2161183 := bstep (se 1 (by rfl) ⟨1620887, by rfl⟩ : syracuseStep 2161183 = 3241775) B3241775
theorem B2881577 : Blo 1919435 2881577 := bstep (se 2 (by rfl) ⟨1080591, by rfl⟩ : syracuseStep 2881577 = 2161183) B2161183
theorem B1921051 : Blo 1919435 1921051 := bstep (se 1 (by rfl) ⟨1440788, by rfl⟩ : syracuseStep 1921051 = 2881577) B2881577
theorem B4615741 : Blo 1919435 4615741 := bbase (se 3 (by rfl) ⟨865451, by rfl⟩ : syracuseStep 4615741 = 1730903) (by norm_num)
theorem B6154321 : Blo 1919435 6154321 := bstep (se 2 (by rfl) ⟨2307870, by rfl⟩ : syracuseStep 6154321 = 4615741) B4615741
theorem B8205761 : Blo 1919435 8205761 := bstep (se 2 (by rfl) ⟨3077160, by rfl⟩ : syracuseStep 8205761 = 6154321) B6154321
theorem B5470507 : Blo 1919435 5470507 := bstep (se 1 (by rfl) ⟨4102880, by rfl⟩ : syracuseStep 5470507 = 8205761) B8205761
theorem B7294009 : Blo 1919435 7294009 := bstep (se 2 (by rfl) ⟨2735253, by rfl⟩ : syracuseStep 7294009 = 5470507) B5470507
theorem B9725345 : Blo 1919435 9725345 := bstep (se 2 (by rfl) ⟨3647004, by rfl⟩ : syracuseStep 9725345 = 7294009) B7294009
theorem B6483563 : Blo 1919435 6483563 := bstep (se 1 (by rfl) ⟨4862672, by rfl⟩ : syracuseStep 6483563 = 9725345) B9725345
theorem B4322375 : Blo 1919435 4322375 := bstep (se 1 (by rfl) ⟨3241781, by rfl⟩ : syracuseStep 4322375 = 6483563) B6483563
theorem B2881583 : Blo 1919435 2881583 := bstep (se 1 (by rfl) ⟨2161187, by rfl⟩ : syracuseStep 2881583 = 4322375) B4322375
theorem B1921055 : Blo 1919435 1921055 := bstep (se 1 (by rfl) ⟨1440791, by rfl⟩ : syracuseStep 1921055 = 2881583) B2881583
theorem B2881589 : Blo 1919435 2881589 := bbase (se 5 (by rfl) ⟨135074, by rfl⟩ : syracuseStep 2881589 = 270149) (by norm_num)
theorem B1921059 : Blo 1919435 1921059 := bstep (se 1 (by rfl) ⟨1440794, by rfl⟩ : syracuseStep 1921059 = 2881589) B2881589
theorem B4862693 : Blo 1919435 4862693 := bbase (se 4 (by rfl) ⟨455877, by rfl⟩ : syracuseStep 4862693 = 911755) (by norm_num)
theorem B3241795 : Blo 1919435 3241795 := bstep (se 1 (by rfl) ⟨2431346, by rfl⟩ : syracuseStep 3241795 = 4862693) B4862693
theorem B4322393 : Blo 1919435 4322393 := bstep (se 2 (by rfl) ⟨1620897, by rfl⟩ : syracuseStep 4322393 = 3241795) B3241795
theorem B2881595 : Blo 1919435 2881595 := bstep (se 1 (by rfl) ⟨2161196, by rfl⟩ : syracuseStep 2881595 = 4322393) B4322393
theorem B1921063 : Blo 1919435 1921063 := bstep (se 1 (by rfl) ⟨1440797, by rfl⟩ : syracuseStep 1921063 = 2881595) B2881595
theorem B2161201 : Blo 1919435 2161201 := bbase (se 2 (by rfl) ⟨810450, by rfl⟩ : syracuseStep 2161201 = 1620901) (by norm_num)
theorem B2881601 : Blo 1919435 2881601 := bstep (se 2 (by rfl) ⟨1080600, by rfl⟩ : syracuseStep 2881601 = 2161201) B2161201
theorem B1921067 : Blo 1919435 1921067 := bstep (se 1 (by rfl) ⟨1440800, by rfl⟩ : syracuseStep 1921067 = 2881601) B2881601
theorem B6154373 : Blo 1919435 6154373 := bbase (se 4 (by rfl) ⟨576972, by rfl⟩ : syracuseStep 6154373 = 1153945) (by norm_num)
theorem B4102915 : Blo 1919435 4102915 := bstep (se 1 (by rfl) ⟨3077186, by rfl⟩ : syracuseStep 4102915 = 6154373) B6154373
theorem B5470553 : Blo 1919435 5470553 := bstep (se 2 (by rfl) ⟨2051457, by rfl⟩ : syracuseStep 5470553 = 4102915) B4102915
theorem B3647035 : Blo 1919435 3647035 := bstep (se 1 (by rfl) ⟨2735276, by rfl⟩ : syracuseStep 3647035 = 5470553) B5470553
theorem B4862713 : Blo 1919435 4862713 := bstep (se 2 (by rfl) ⟨1823517, by rfl⟩ : syracuseStep 4862713 = 3647035) B3647035
theorem B6483617 : Blo 1919435 6483617 := bstep (se 2 (by rfl) ⟨2431356, by rfl⟩ : syracuseStep 6483617 = 4862713) B4862713
theorem B4322411 : Blo 1919435 4322411 := bstep (se 1 (by rfl) ⟨3241808, by rfl⟩ : syracuseStep 4322411 = 6483617) B6483617
theorem B2881607 : Blo 1919435 2881607 := bstep (se 1 (by rfl) ⟨2161205, by rfl⟩ : syracuseStep 2881607 = 4322411) B4322411
theorem B1921071 : Blo 1919435 1921071 := bstep (se 1 (by rfl) ⟨1440803, by rfl⟩ : syracuseStep 1921071 = 2881607) B2881607
theorem B2881613 : Blo 1919435 2881613 := bbase (se 3 (by rfl) ⟨540302, by rfl⟩ : syracuseStep 2881613 = 1080605) (by norm_num)
theorem B1921075 : Blo 1919435 1921075 := bstep (se 1 (by rfl) ⟨1440806, by rfl⟩ : syracuseStep 1921075 = 2881613) B2881613
theorem B4322429 : Blo 1919435 4322429 := bbase (se 3 (by rfl) ⟨810455, by rfl⟩ : syracuseStep 4322429 = 1620911) (by norm_num)
theorem B2881619 : Blo 1919435 2881619 := bstep (se 1 (by rfl) ⟨2161214, by rfl⟩ : syracuseStep 2881619 = 4322429) B4322429
theorem B1921079 : Blo 1919435 1921079 := bstep (se 1 (by rfl) ⟨1440809, by rfl⟩ : syracuseStep 1921079 = 2881619) B2881619
theorem B3241829 : Blo 1919435 3241829 := bbase (se 4 (by rfl) ⟨303921, by rfl⟩ : syracuseStep 3241829 = 607843) (by norm_num)
theorem B2161219 : Blo 1919435 2161219 := bstep (se 1 (by rfl) ⟨1620914, by rfl⟩ : syracuseStep 2161219 = 3241829) B3241829
theorem B2881625 : Blo 1919435 2881625 := bstep (se 2 (by rfl) ⟨1080609, by rfl⟩ : syracuseStep 2881625 = 2161219) B2161219
theorem B1921083 : Blo 1919435 1921083 := bstep (se 1 (by rfl) ⟨1440812, by rfl⟩ : syracuseStep 1921083 = 2881625) B2881625
theorem B4102949 : Blo 1919435 4102949 := bbase (se 4 (by rfl) ⟨384651, by rfl⟩ : syracuseStep 4102949 = 769303) (by norm_num)
theorem B2735299 : Blo 1919435 2735299 := bstep (se 1 (by rfl) ⟨2051474, by rfl⟩ : syracuseStep 2735299 = 4102949) B4102949
theorem B14588261 : Blo 1919435 14588261 := bstep (se 4 (by rfl) ⟨1367649, by rfl⟩ : syracuseStep 14588261 = 2735299) B2735299
theorem B9725507 : Blo 1919435 9725507 := bstep (se 1 (by rfl) ⟨7294130, by rfl⟩ : syracuseStep 9725507 = 14588261) B14588261
theorem B6483671 : Blo 1919435 6483671 := bstep (se 1 (by rfl) ⟨4862753, by rfl⟩ : syracuseStep 6483671 = 9725507) B9725507
theorem B4322447 : Blo 1919435 4322447 := bstep (se 1 (by rfl) ⟨3241835, by rfl⟩ : syracuseStep 4322447 = 6483671) B6483671
theorem B2881631 : Blo 1919435 2881631 := bstep (se 1 (by rfl) ⟨2161223, by rfl⟩ : syracuseStep 2881631 = 4322447) B4322447
theorem B1921087 : Blo 1919435 1921087 := bstep (se 1 (by rfl) ⟨1440815, by rfl⟩ : syracuseStep 1921087 = 2881631) B2881631
theorem B2881637 : Blo 1919435 2881637 := bbase (se 4 (by rfl) ⟨270153, by rfl⟩ : syracuseStep 2881637 = 540307) (by norm_num)
theorem B1921091 : Blo 1919435 1921091 := bstep (se 1 (by rfl) ⟨1440818, by rfl⟩ : syracuseStep 1921091 = 2881637) B2881637
theorem B2190721 : Blo 1919435 2190721 := bbase (se 2 (by rfl) ⟨821520, by rfl⟩ : syracuseStep 2190721 = 1643041) (by norm_num)
theorem B2920961 : Blo 1919435 2920961 := bstep (se 2 (by rfl) ⟨1095360, by rfl⟩ : syracuseStep 2920961 = 2190721) B2190721
theorem B7789229 : Blo 1919435 7789229 := bstep (se 3 (by rfl) ⟨1460480, by rfl⟩ : syracuseStep 7789229 = 2920961) B2920961
theorem B5192819 : Blo 1919435 5192819 := bstep (se 1 (by rfl) ⟨3894614, by rfl⟩ : syracuseStep 5192819 = 7789229) B7789229
theorem B3461879 : Blo 1919435 3461879 := bstep (se 1 (by rfl) ⟨2596409, by rfl⟩ : syracuseStep 3461879 = 5192819) B5192819
theorem B9231677 : Blo 1919435 9231677 := bstep (se 3 (by rfl) ⟨1730939, by rfl⟩ : syracuseStep 9231677 = 3461879) B3461879
theorem B6154451 : Blo 1919435 6154451 := bstep (se 1 (by rfl) ⟨4615838, by rfl⟩ : syracuseStep 6154451 = 9231677) B9231677
theorem B4102967 : Blo 1919435 4102967 := bstep (se 1 (by rfl) ⟨3077225, by rfl⟩ : syracuseStep 4102967 = 6154451) B6154451
theorem B2735311 : Blo 1919435 2735311 := bstep (se 1 (by rfl) ⟨2051483, by rfl⟩ : syracuseStep 2735311 = 4102967) B4102967
theorem B3647081 : Blo 1919435 3647081 := bstep (se 2 (by rfl) ⟨1367655, by rfl⟩ : syracuseStep 3647081 = 2735311) B2735311
theorem B2431387 : Blo 1919435 2431387 := bstep (se 1 (by rfl) ⟨1823540, by rfl⟩ : syracuseStep 2431387 = 3647081) B3647081
theorem B3241849 : Blo 1919435 3241849 := bstep (se 2 (by rfl) ⟨1215693, by rfl⟩ : syracuseStep 3241849 = 2431387) B2431387
theorem B4322465 : Blo 1919435 4322465 := bstep (se 2 (by rfl) ⟨1620924, by rfl⟩ : syracuseStep 4322465 = 3241849) B3241849
theorem B2881643 : Blo 1919435 2881643 := bstep (se 1 (by rfl) ⟨2161232, by rfl⟩ : syracuseStep 2881643 = 4322465) B4322465
theorem B1921095 : Blo 1919435 1921095 := bstep (se 1 (by rfl) ⟨1440821, by rfl⟩ : syracuseStep 1921095 = 2881643) B2881643
theorem B2161237 : Blo 1919435 2161237 := bbase (se 8 (by rfl) ⟨12663, by rfl⟩ : syracuseStep 2161237 = 25327) (by norm_num)
theorem B2881649 : Blo 1919435 2881649 := bstep (se 2 (by rfl) ⟨1080618, by rfl⟩ : syracuseStep 2881649 = 2161237) B2161237
theorem B1921099 : Blo 1919435 1921099 := bstep (se 1 (by rfl) ⟨1440824, by rfl⟩ : syracuseStep 1921099 = 2881649) B2881649
theorem B2431397 : Blo 1919435 2431397 := bbase (se 4 (by rfl) ⟨227943, by rfl⟩ : syracuseStep 2431397 = 455887) (by norm_num)
theorem B6483725 : Blo 1919435 6483725 := bstep (se 3 (by rfl) ⟨1215698, by rfl⟩ : syracuseStep 6483725 = 2431397) B2431397
theorem B4322483 : Blo 1919435 4322483 := bstep (se 1 (by rfl) ⟨3241862, by rfl⟩ : syracuseStep 4322483 = 6483725) B6483725
theorem B2881655 : Blo 1919435 2881655 := bstep (se 1 (by rfl) ⟨2161241, by rfl⟩ : syracuseStep 2881655 = 4322483) B4322483
theorem B1921103 : Blo 1919435 1921103 := bstep (se 1 (by rfl) ⟨1440827, by rfl⟩ : syracuseStep 1921103 = 2881655) B2881655
theorem B2881661 : Blo 1919435 2881661 := bbase (se 3 (by rfl) ⟨540311, by rfl⟩ : syracuseStep 2881661 = 1080623) (by norm_num)
theorem B1921107 : Blo 1919435 1921107 := bstep (se 1 (by rfl) ⟨1440830, by rfl⟩ : syracuseStep 1921107 = 2881661) B2881661
theorem B4322501 : Blo 1919435 4322501 := bbase (se 4 (by rfl) ⟨405234, by rfl⟩ : syracuseStep 4322501 = 810469) (by norm_num)
theorem B2881667 : Blo 1919435 2881667 := bstep (se 1 (by rfl) ⟨2161250, by rfl⟩ : syracuseStep 2881667 = 4322501) B4322501
theorem B1921111 : Blo 1919435 1921111 := bstep (se 1 (by rfl) ⟨1440833, by rfl⟩ : syracuseStep 1921111 = 2881667) B2881667
theorem B3509149 : Blo 1919435 3509149 := bbase (se 3 (by rfl) ⟨657965, by rfl⟩ : syracuseStep 3509149 = 1315931) (by norm_num)
theorem B4678865 : Blo 1919435 4678865 := bstep (se 2 (by rfl) ⟨1754574, by rfl⟩ : syracuseStep 4678865 = 3509149) B3509149
theorem B3119243 : Blo 1919435 3119243 := bstep (se 1 (by rfl) ⟨2339432, by rfl⟩ : syracuseStep 3119243 = 4678865) B4678865
theorem B8317981 : Blo 1919435 8317981 := bstep (se 3 (by rfl) ⟨1559621, by rfl⟩ : syracuseStep 8317981 = 3119243) B3119243
theorem B44362565 : Blo 1919435 44362565 := bstep (se 4 (by rfl) ⟨4158990, by rfl⟩ : syracuseStep 44362565 = 8317981) B8317981
theorem B29575043 : Blo 1919435 29575043 := bstep (se 1 (by rfl) ⟨22181282, by rfl⟩ : syracuseStep 29575043 = 44362565) B44362565
theorem B19716695 : Blo 1919435 19716695 := bstep (se 1 (by rfl) ⟨14787521, by rfl⟩ : syracuseStep 19716695 = 29575043) B29575043
theorem B13144463 : Blo 1919435 13144463 := bstep (se 1 (by rfl) ⟨9858347, by rfl⟩ : syracuseStep 13144463 = 19716695) B19716695
theorem B8762975 : Blo 1919435 8762975 := bstep (se 1 (by rfl) ⟨6572231, by rfl⟩ : syracuseStep 8762975 = 13144463) B13144463
theorem B5841983 : Blo 1919435 5841983 := bstep (se 1 (by rfl) ⟨4381487, by rfl⟩ : syracuseStep 5841983 = 8762975) B8762975
theorem B3894655 : Blo 1919435 3894655 := bstep (se 1 (by rfl) ⟨2920991, by rfl⟩ : syracuseStep 3894655 = 5841983) B5841983
theorem B5192873 : Blo 1919435 5192873 := bstep (se 2 (by rfl) ⟨1947327, by rfl⟩ : syracuseStep 5192873 = 3894655) B3894655
theorem B3461915 : Blo 1919435 3461915 := bstep (se 1 (by rfl) ⟨2596436, by rfl⟩ : syracuseStep 3461915 = 5192873) B5192873
theorem B2307943 : Blo 1919435 2307943 := bstep (se 1 (by rfl) ⟨1730957, by rfl⟩ : syracuseStep 2307943 = 3461915) B3461915
theorem B12309029 : Blo 1919435 12309029 := bstep (se 4 (by rfl) ⟨1153971, by rfl⟩ : syracuseStep 12309029 = 2307943) B2307943
theorem B8206019 : Blo 1919435 8206019 := bstep (se 1 (by rfl) ⟨6154514, by rfl⟩ : syracuseStep 8206019 = 12309029) B12309029
theorem B5470679 : Blo 1919435 5470679 := bstep (se 1 (by rfl) ⟨4103009, by rfl⟩ : syracuseStep 5470679 = 8206019) B8206019
theorem B3647119 : Blo 1919435 3647119 := bstep (se 1 (by rfl) ⟨2735339, by rfl⟩ : syracuseStep 3647119 = 5470679) B5470679
theorem B4862825 : Blo 1919435 4862825 := bstep (se 2 (by rfl) ⟨1823559, by rfl⟩ : syracuseStep 4862825 = 3647119) B3647119
theorem B3241883 : Blo 1919435 3241883 := bstep (se 1 (by rfl) ⟨2431412, by rfl⟩ : syracuseStep 3241883 = 4862825) B4862825
theorem B2161255 : Blo 1919435 2161255 := bstep (se 1 (by rfl) ⟨1620941, by rfl⟩ : syracuseStep 2161255 = 3241883) B3241883
theorem B2881673 : Blo 1919435 2881673 := bstep (se 2 (by rfl) ⟨1080627, by rfl⟩ : syracuseStep 2881673 = 2161255) B2161255
theorem B1921115 : Blo 1919435 1921115 := bstep (se 1 (by rfl) ⟨1440836, by rfl⟩ : syracuseStep 1921115 = 2881673) B2881673
theorem B9725669 : Blo 1919435 9725669 := bbase (se 4 (by rfl) ⟨911781, by rfl⟩ : syracuseStep 9725669 = 1823563) (by norm_num)
theorem B6483779 : Blo 1919435 6483779 := bstep (se 1 (by rfl) ⟨4862834, by rfl⟩ : syracuseStep 6483779 = 9725669) B9725669
theorem B4322519 : Blo 1919435 4322519 := bstep (se 1 (by rfl) ⟨3241889, by rfl⟩ : syracuseStep 4322519 = 6483779) B6483779
theorem B2881679 : Blo 1919435 2881679 := bstep (se 1 (by rfl) ⟨2161259, by rfl⟩ : syracuseStep 2881679 = 4322519) B4322519
theorem B1921119 : Blo 1919435 1921119 := bstep (se 1 (by rfl) ⟨1440839, by rfl⟩ : syracuseStep 1921119 = 2881679) B2881679
theorem B2881685 : Blo 1919435 2881685 := bbase (se 6 (by rfl) ⟨67539, by rfl⟩ : syracuseStep 2881685 = 135079) (by norm_num)
theorem B1921123 : Blo 1919435 1921123 := bstep (se 1 (by rfl) ⟨1440842, by rfl⟩ : syracuseStep 1921123 = 2881685) B2881685
theorem B8206069 : Blo 1919435 8206069 := bbase (se 5 (by rfl) ⟨384659, by rfl⟩ : syracuseStep 8206069 = 769319) (by norm_num)
theorem B10941425 : Blo 1919435 10941425 := bstep (se 2 (by rfl) ⟨4103034, by rfl⟩ : syracuseStep 10941425 = 8206069) B8206069
theorem B7294283 : Blo 1919435 7294283 := bstep (se 1 (by rfl) ⟨5470712, by rfl⟩ : syracuseStep 7294283 = 10941425) B10941425
theorem B4862855 : Blo 1919435 4862855 := bstep (se 1 (by rfl) ⟨3647141, by rfl⟩ : syracuseStep 4862855 = 7294283) B7294283
theorem B3241903 : Blo 1919435 3241903 := bstep (se 1 (by rfl) ⟨2431427, by rfl⟩ : syracuseStep 3241903 = 4862855) B4862855
theorem B4322537 : Blo 1919435 4322537 := bstep (se 2 (by rfl) ⟨1620951, by rfl⟩ : syracuseStep 4322537 = 3241903) B3241903
theorem B2881691 : Blo 1919435 2881691 := bstep (se 1 (by rfl) ⟨2161268, by rfl⟩ : syracuseStep 2881691 = 4322537) B4322537
theorem B1921127 : Blo 1919435 1921127 := bstep (se 1 (by rfl) ⟨1440845, by rfl⟩ : syracuseStep 1921127 = 2881691) B2881691
theorem B2161273 : Blo 1919435 2161273 := bbase (se 2 (by rfl) ⟨810477, by rfl⟩ : syracuseStep 2161273 = 1620955) (by norm_num)
theorem B2881697 : Blo 1919435 2881697 := bstep (se 2 (by rfl) ⟨1080636, by rfl⟩ : syracuseStep 2881697 = 2161273) B2161273
theorem B1921131 : Blo 1919435 1921131 := bstep (se 1 (by rfl) ⟨1440848, by rfl⟩ : syracuseStep 1921131 = 2881697) B2881697
theorem B18463733 : Blo 1919435 18463733 := bbase (se 5 (by rfl) ⟨865487, by rfl⟩ : syracuseStep 18463733 = 1730975) (by norm_num)
theorem B12309155 : Blo 1919435 12309155 := bstep (se 1 (by rfl) ⟨9231866, by rfl⟩ : syracuseStep 12309155 = 18463733) B18463733
theorem B8206103 : Blo 1919435 8206103 := bstep (se 1 (by rfl) ⟨6154577, by rfl⟩ : syracuseStep 8206103 = 12309155) B12309155
theorem B5470735 : Blo 1919435 5470735 := bstep (se 1 (by rfl) ⟨4103051, by rfl⟩ : syracuseStep 5470735 = 8206103) B8206103
theorem B7294313 : Blo 1919435 7294313 := bstep (se 2 (by rfl) ⟨2735367, by rfl⟩ : syracuseStep 7294313 = 5470735) B5470735
theorem B4862875 : Blo 1919435 4862875 := bstep (se 1 (by rfl) ⟨3647156, by rfl⟩ : syracuseStep 4862875 = 7294313) B7294313
theorem B6483833 : Blo 1919435 6483833 := bstep (se 2 (by rfl) ⟨2431437, by rfl⟩ : syracuseStep 6483833 = 4862875) B4862875
theorem B4322555 : Blo 1919435 4322555 := bstep (se 1 (by rfl) ⟨3241916, by rfl⟩ : syracuseStep 4322555 = 6483833) B6483833
theorem B2881703 : Blo 1919435 2881703 := bstep (se 1 (by rfl) ⟨2161277, by rfl⟩ : syracuseStep 2881703 = 4322555) B4322555
theorem B1921135 : Blo 1919435 1921135 := bstep (se 1 (by rfl) ⟨1440851, by rfl⟩ : syracuseStep 1921135 = 2881703) B2881703
theorem B2881709 : Blo 1919435 2881709 := bbase (se 3 (by rfl) ⟨540320, by rfl⟩ : syracuseStep 2881709 = 1080641) (by norm_num)
theorem B1921139 : Blo 1919435 1921139 := bstep (se 1 (by rfl) ⟨1440854, by rfl⟩ : syracuseStep 1921139 = 2881709) B2881709
theorem B4322573 : Blo 1919435 4322573 := bbase (se 3 (by rfl) ⟨810482, by rfl⟩ : syracuseStep 4322573 = 1620965) (by norm_num)
theorem B2881715 : Blo 1919435 2881715 := bstep (se 1 (by rfl) ⟨2161286, by rfl⟩ : syracuseStep 2881715 = 4322573) B4322573
theorem B1921143 : Blo 1919435 1921143 := bstep (se 1 (by rfl) ⟨1440857, by rfl⟩ : syracuseStep 1921143 = 2881715) B2881715
theorem B2431453 : Blo 1919435 2431453 := bbase (se 3 (by rfl) ⟨455897, by rfl⟩ : syracuseStep 2431453 = 911795) (by norm_num)
theorem B3241937 : Blo 1919435 3241937 := bstep (se 2 (by rfl) ⟨1215726, by rfl⟩ : syracuseStep 3241937 = 2431453) B2431453
theorem B2161291 : Blo 1919435 2161291 := bstep (se 1 (by rfl) ⟨1620968, by rfl⟩ : syracuseStep 2161291 = 3241937) B3241937
theorem B2881721 : Blo 1919435 2881721 := bstep (se 2 (by rfl) ⟨1080645, by rfl⟩ : syracuseStep 2881721 = 2161291) B2161291
theorem B1921147 : Blo 1919435 1921147 := bstep (se 1 (by rfl) ⟨1440860, by rfl⟩ : syracuseStep 1921147 = 2881721) B2881721
theorem B16412341 : Blo 1919435 16412341 := bbase (se 5 (by rfl) ⟨769328, by rfl⟩ : syracuseStep 16412341 = 1538657) (by norm_num)
theorem B21883121 : Blo 1919435 21883121 := bstep (se 2 (by rfl) ⟨8206170, by rfl⟩ : syracuseStep 21883121 = 16412341) B16412341
theorem B14588747 : Blo 1919435 14588747 := bstep (se 1 (by rfl) ⟨10941560, by rfl⟩ : syracuseStep 14588747 = 21883121) B21883121
theorem B9725831 : Blo 1919435 9725831 := bstep (se 1 (by rfl) ⟨7294373, by rfl⟩ : syracuseStep 9725831 = 14588747) B14588747
theorem B6483887 : Blo 1919435 6483887 := bstep (se 1 (by rfl) ⟨4862915, by rfl⟩ : syracuseStep 6483887 = 9725831) B9725831
theorem B4322591 : Blo 1919435 4322591 := bstep (se 1 (by rfl) ⟨3241943, by rfl⟩ : syracuseStep 4322591 = 6483887) B6483887
theorem B2881727 : Blo 1919435 2881727 := bstep (se 1 (by rfl) ⟨2161295, by rfl⟩ : syracuseStep 2881727 = 4322591) B4322591
theorem B1921151 : Blo 1919435 1921151 := bstep (se 1 (by rfl) ⟨1440863, by rfl⟩ : syracuseStep 1921151 = 2881727) B2881727
theorem B2881733 : Blo 1919435 2881733 := bbase (se 4 (by rfl) ⟨270162, by rfl⟩ : syracuseStep 2881733 = 540325) (by norm_num)
theorem B1921155 : Blo 1919435 1921155 := bstep (se 1 (by rfl) ⟨1440866, by rfl⟩ : syracuseStep 1921155 = 2881733) B2881733
theorem B3241957 : Blo 1919435 3241957 := bbase (se 4 (by rfl) ⟨303933, by rfl⟩ : syracuseStep 3241957 = 607867) (by norm_num)
theorem B4322609 : Blo 1919435 4322609 := bstep (se 2 (by rfl) ⟨1620978, by rfl⟩ : syracuseStep 4322609 = 3241957) B3241957
theorem B2881739 : Blo 1919435 2881739 := bstep (se 1 (by rfl) ⟨2161304, by rfl⟩ : syracuseStep 2881739 = 4322609) B4322609
theorem B1921159 : Blo 1919435 1921159 := bstep (se 1 (by rfl) ⟨1440869, by rfl⟩ : syracuseStep 1921159 = 2881739) B2881739
theorem B2161309 : Blo 1919435 2161309 := bbase (se 3 (by rfl) ⟨405245, by rfl⟩ : syracuseStep 2161309 = 810491) (by norm_num)
theorem B2881745 : Blo 1919435 2881745 := bstep (se 2 (by rfl) ⟨1080654, by rfl⟩ : syracuseStep 2881745 = 2161309) B2161309
theorem B1921163 : Blo 1919435 1921163 := bstep (se 1 (by rfl) ⟨1440872, by rfl⟩ : syracuseStep 1921163 = 2881745) B2881745
theorem B6483941 : Blo 1919435 6483941 := bbase (se 4 (by rfl) ⟨607869, by rfl⟩ : syracuseStep 6483941 = 1215739) (by norm_num)
theorem B4322627 : Blo 1919435 4322627 := bstep (se 1 (by rfl) ⟨3241970, by rfl⟩ : syracuseStep 4322627 = 6483941) B6483941
theorem B2881751 : Blo 1919435 2881751 := bstep (se 1 (by rfl) ⟨2161313, by rfl⟩ : syracuseStep 2881751 = 4322627) B4322627
theorem B1921167 : Blo 1919435 1921167 := bstep (se 1 (by rfl) ⟨1440875, by rfl⟩ : syracuseStep 1921167 = 2881751) B2881751
theorem B2881757 : Blo 1919435 2881757 := bbase (se 3 (by rfl) ⟨540329, by rfl⟩ : syracuseStep 2881757 = 1080659) (by norm_num)
theorem B1921171 : Blo 1919435 1921171 := bstep (se 1 (by rfl) ⟨1440878, by rfl⟩ : syracuseStep 1921171 = 2881757) B2881757
theorem B4322645 : Blo 1919435 4322645 := bbase (se 13 (by rfl) ⟨791, by rfl⟩ : syracuseStep 4322645 = 1583) (by norm_num)
theorem B2881763 : Blo 1919435 2881763 := bstep (se 1 (by rfl) ⟨2161322, by rfl⟩ : syracuseStep 2881763 = 4322645) B4322645
theorem B1921175 : Blo 1919435 1921175 := bstep (se 1 (by rfl) ⟨1440881, by rfl⟩ : syracuseStep 1921175 = 2881763) B2881763
theorem B2051573 : Blo 1919435 2051573 := bbase (se 5 (by rfl) ⟨96167, by rfl⟩ : syracuseStep 2051573 = 192335) (by norm_num)
theorem B5470861 : Blo 1919435 5470861 := bstep (se 3 (by rfl) ⟨1025786, by rfl⟩ : syracuseStep 5470861 = 2051573) B2051573
theorem B7294481 : Blo 1919435 7294481 := bstep (se 2 (by rfl) ⟨2735430, by rfl⟩ : syracuseStep 7294481 = 5470861) B5470861
theorem B4862987 : Blo 1919435 4862987 := bstep (se 1 (by rfl) ⟨3647240, by rfl⟩ : syracuseStep 4862987 = 7294481) B7294481
theorem B3241991 : Blo 1919435 3241991 := bstep (se 1 (by rfl) ⟨2431493, by rfl⟩ : syracuseStep 3241991 = 4862987) B4862987
theorem B2161327 : Blo 1919435 2161327 := bstep (se 1 (by rfl) ⟨1620995, by rfl⟩ : syracuseStep 2161327 = 3241991) B3241991
theorem B2881769 : Blo 1919435 2881769 := bstep (se 2 (by rfl) ⟨1080663, by rfl⟩ : syracuseStep 2881769 = 2161327) B2161327
theorem B1921179 : Blo 1919435 1921179 := bstep (se 1 (by rfl) ⟨1440884, by rfl⟩ : syracuseStep 1921179 = 2881769) B2881769
theorem B4441421 : Blo 1919435 4441421 := bbase (se 3 (by rfl) ⟨832766, by rfl⟩ : syracuseStep 4441421 = 1665533) (by norm_num)
theorem B2960947 : Blo 1919435 2960947 := bstep (se 1 (by rfl) ⟨2220710, by rfl⟩ : syracuseStep 2960947 = 4441421) B4441421
theorem B3947929 : Blo 1919435 3947929 := bstep (se 2 (by rfl) ⟨1480473, by rfl⟩ : syracuseStep 3947929 = 2960947) B2960947
theorem B21055621 : Blo 1919435 21055621 := bstep (se 4 (by rfl) ⟨1973964, by rfl⟩ : syracuseStep 21055621 = 3947929) B3947929
theorem B28074161 : Blo 1919435 28074161 := bstep (se 2 (by rfl) ⟨10527810, by rfl⟩ : syracuseStep 28074161 = 21055621) B21055621
theorem B18716107 : Blo 1919435 18716107 := bstep (se 1 (by rfl) ⟨14037080, by rfl⟩ : syracuseStep 18716107 = 28074161) B28074161
theorem B24954809 : Blo 1919435 24954809 := bstep (se 2 (by rfl) ⟨9358053, by rfl⟩ : syracuseStep 24954809 = 18716107) B18716107
theorem B66546157 : Blo 1919435 66546157 := bstep (se 3 (by rfl) ⟨12477404, by rfl⟩ : syracuseStep 66546157 = 24954809) B24954809
theorem B88728209 : Blo 1919435 88728209 := bstep (se 2 (by rfl) ⟨33273078, by rfl⟩ : syracuseStep 88728209 = 66546157) B66546157
theorem B59152139 : Blo 1919435 59152139 := bstep (se 1 (by rfl) ⟨44364104, by rfl⟩ : syracuseStep 59152139 = 88728209) B88728209
theorem B39434759 : Blo 1919435 39434759 := bstep (se 1 (by rfl) ⟨29576069, by rfl⟩ : syracuseStep 39434759 = 59152139) B59152139
theorem B26289839 : Blo 1919435 26289839 := bstep (se 1 (by rfl) ⟨19717379, by rfl⟩ : syracuseStep 26289839 = 39434759) B39434759
theorem B17526559 : Blo 1919435 17526559 := bstep (se 1 (by rfl) ⟨13144919, by rfl⟩ : syracuseStep 17526559 = 26289839) B26289839
theorem B23368745 : Blo 1919435 23368745 := bstep (se 2 (by rfl) ⟨8763279, by rfl⟩ : syracuseStep 23368745 = 17526559) B17526559
theorem B15579163 : Blo 1919435 15579163 := bstep (se 1 (by rfl) ⟨11684372, by rfl⟩ : syracuseStep 15579163 = 23368745) B23368745
theorem B20772217 : Blo 1919435 20772217 := bstep (se 2 (by rfl) ⟨7789581, by rfl⟩ : syracuseStep 20772217 = 15579163) B15579163
theorem B27696289 : Blo 1919435 27696289 := bstep (se 2 (by rfl) ⟨10386108, by rfl⟩ : syracuseStep 27696289 = 20772217) B20772217
theorem B36928385 : Blo 1919435 36928385 := bstep (se 2 (by rfl) ⟨13848144, by rfl⟩ : syracuseStep 36928385 = 27696289) B27696289
theorem B24618923 : Blo 1919435 24618923 := bstep (se 1 (by rfl) ⟨18464192, by rfl⟩ : syracuseStep 24618923 = 36928385) B36928385
theorem B16412615 : Blo 1919435 16412615 := bstep (se 1 (by rfl) ⟨12309461, by rfl⟩ : syracuseStep 16412615 = 24618923) B24618923
theorem B10941743 : Blo 1919435 10941743 := bstep (se 1 (by rfl) ⟨8206307, by rfl⟩ : syracuseStep 10941743 = 16412615) B16412615
theorem B7294495 : Blo 1919435 7294495 := bstep (se 1 (by rfl) ⟨5470871, by rfl⟩ : syracuseStep 7294495 = 10941743) B10941743
theorem B9725993 : Blo 1919435 9725993 := bstep (se 2 (by rfl) ⟨3647247, by rfl⟩ : syracuseStep 9725993 = 7294495) B7294495
theorem B6483995 : Blo 1919435 6483995 := bstep (se 1 (by rfl) ⟨4862996, by rfl⟩ : syracuseStep 6483995 = 9725993) B9725993
theorem B4322663 : Blo 1919435 4322663 := bstep (se 1 (by rfl) ⟨3241997, by rfl⟩ : syracuseStep 4322663 = 6483995) B6483995
theorem B2881775 : Blo 1919435 2881775 := bstep (se 1 (by rfl) ⟨2161331, by rfl⟩ : syracuseStep 2881775 = 4322663) B4322663
theorem B1921183 : Blo 1919435 1921183 := bstep (se 1 (by rfl) ⟨1440887, by rfl⟩ : syracuseStep 1921183 = 2881775) B2881775
theorem B2881781 : Blo 1919435 2881781 := bbase (se 5 (by rfl) ⟨135083, by rfl⟩ : syracuseStep 2881781 = 270167) (by norm_num)
theorem B1921187 : Blo 1919435 1921187 := bstep (se 1 (by rfl) ⟨1440890, by rfl⟩ : syracuseStep 1921187 = 2881781) B2881781
theorem B5193077 : Blo 1919435 5193077 := bbase (se 5 (by rfl) ⟨243425, by rfl⟩ : syracuseStep 5193077 = 486851) (by norm_num)
theorem B13848205 : Blo 1919435 13848205 := bstep (se 3 (by rfl) ⟨2596538, by rfl⟩ : syracuseStep 13848205 = 5193077) B5193077
theorem B18464273 : Blo 1919435 18464273 := bstep (se 2 (by rfl) ⟨6924102, by rfl⟩ : syracuseStep 18464273 = 13848205) B13848205
theorem B12309515 : Blo 1919435 12309515 := bstep (se 1 (by rfl) ⟨9232136, by rfl⟩ : syracuseStep 12309515 = 18464273) B18464273
theorem B8206343 : Blo 1919435 8206343 := bstep (se 1 (by rfl) ⟨6154757, by rfl⟩ : syracuseStep 8206343 = 12309515) B12309515
theorem B5470895 : Blo 1919435 5470895 := bstep (se 1 (by rfl) ⟨4103171, by rfl⟩ : syracuseStep 5470895 = 8206343) B8206343
theorem B3647263 : Blo 1919435 3647263 := bstep (se 1 (by rfl) ⟨2735447, by rfl⟩ : syracuseStep 3647263 = 5470895) B5470895
theorem B4863017 : Blo 1919435 4863017 := bstep (se 2 (by rfl) ⟨1823631, by rfl⟩ : syracuseStep 4863017 = 3647263) B3647263
theorem B3242011 : Blo 1919435 3242011 := bstep (se 1 (by rfl) ⟨2431508, by rfl⟩ : syracuseStep 3242011 = 4863017) B4863017
theorem B4322681 : Blo 1919435 4322681 := bstep (se 2 (by rfl) ⟨1621005, by rfl⟩ : syracuseStep 4322681 = 3242011) B3242011
theorem B2881787 : Blo 1919435 2881787 := bstep (se 1 (by rfl) ⟨2161340, by rfl⟩ : syracuseStep 2881787 = 4322681) B4322681
theorem B1921191 : Blo 1919435 1921191 := bstep (se 1 (by rfl) ⟨1440893, by rfl⟩ : syracuseStep 1921191 = 2881787) B2881787
theorem B2161345 : Blo 1919435 2161345 := bbase (se 2 (by rfl) ⟨810504, by rfl⟩ : syracuseStep 2161345 = 1621009) (by norm_num)
theorem B2881793 : Blo 1919435 2881793 := bstep (se 2 (by rfl) ⟨1080672, by rfl⟩ : syracuseStep 2881793 = 2161345) B2161345
theorem B1921195 : Blo 1919435 1921195 := bstep (se 1 (by rfl) ⟨1440896, by rfl⟩ : syracuseStep 1921195 = 2881793) B2881793
theorem B4863037 : Blo 1919435 4863037 := bbase (se 3 (by rfl) ⟨911819, by rfl⟩ : syracuseStep 4863037 = 1823639) (by norm_num)
theorem B6484049 : Blo 1919435 6484049 := bstep (se 2 (by rfl) ⟨2431518, by rfl⟩ : syracuseStep 6484049 = 4863037) B4863037
theorem B4322699 : Blo 1919435 4322699 := bstep (se 1 (by rfl) ⟨3242024, by rfl⟩ : syracuseStep 4322699 = 6484049) B6484049
theorem B2881799 : Blo 1919435 2881799 := bstep (se 1 (by rfl) ⟨2161349, by rfl⟩ : syracuseStep 2881799 = 4322699) B4322699
theorem B1921199 : Blo 1919435 1921199 := bstep (se 1 (by rfl) ⟨1440899, by rfl⟩ : syracuseStep 1921199 = 2881799) B2881799
theorem B2881805 : Blo 1919435 2881805 := bbase (se 3 (by rfl) ⟨540338, by rfl⟩ : syracuseStep 2881805 = 1080677) (by norm_num)
theorem B1921203 : Blo 1919435 1921203 := bstep (se 1 (by rfl) ⟨1440902, by rfl⟩ : syracuseStep 1921203 = 2881805) B2881805
theorem B4322717 : Blo 1919435 4322717 := bbase (se 3 (by rfl) ⟨810509, by rfl⟩ : syracuseStep 4322717 = 1621019) (by norm_num)
theorem B2881811 : Blo 1919435 2881811 := bstep (se 1 (by rfl) ⟨2161358, by rfl⟩ : syracuseStep 2881811 = 4322717) B4322717
theorem B1921207 : Blo 1919435 1921207 := bstep (se 1 (by rfl) ⟨1440905, by rfl⟩ : syracuseStep 1921207 = 2881811) B2881811
theorem B3242045 : Blo 1919435 3242045 := bbase (se 3 (by rfl) ⟨607883, by rfl⟩ : syracuseStep 3242045 = 1215767) (by norm_num)
theorem B2161363 : Blo 1919435 2161363 := bstep (se 1 (by rfl) ⟨1621022, by rfl⟩ : syracuseStep 2161363 = 3242045) B3242045
theorem B2881817 : Blo 1919435 2881817 := bstep (se 2 (by rfl) ⟨1080681, by rfl⟩ : syracuseStep 2881817 = 2161363) B2161363
theorem B1921211 : Blo 1919435 1921211 := bstep (se 1 (by rfl) ⟨1440908, by rfl⟩ : syracuseStep 1921211 = 2881817) B2881817
theorem B2772805 : Blo 1919435 2772805 := bbase (se 4 (by rfl) ⟨259950, by rfl⟩ : syracuseStep 2772805 = 519901) (by norm_num)
theorem B3697073 : Blo 1919435 3697073 := bstep (se 2 (by rfl) ⟨1386402, by rfl⟩ : syracuseStep 3697073 = 2772805) B2772805
theorem B2464715 : Blo 1919435 2464715 := bstep (se 1 (by rfl) ⟨1848536, by rfl⟩ : syracuseStep 2464715 = 3697073) B3697073
theorem B6572573 : Blo 1919435 6572573 := bstep (se 3 (by rfl) ⟨1232357, by rfl⟩ : syracuseStep 6572573 = 2464715) B2464715
theorem B4381715 : Blo 1919435 4381715 := bstep (se 1 (by rfl) ⟨3286286, by rfl⟩ : syracuseStep 4381715 = 6572573) B6572573
theorem B11684573 : Blo 1919435 11684573 := bstep (se 3 (by rfl) ⟨2190857, by rfl⟩ : syracuseStep 11684573 = 4381715) B4381715
theorem B7789715 : Blo 1919435 7789715 := bstep (se 1 (by rfl) ⟨5842286, by rfl⟩ : syracuseStep 7789715 = 11684573) B11684573
theorem B5193143 : Blo 1919435 5193143 := bstep (se 1 (by rfl) ⟨3894857, by rfl⟩ : syracuseStep 5193143 = 7789715) B7789715
theorem B3462095 : Blo 1919435 3462095 := bstep (se 1 (by rfl) ⟨2596571, by rfl⟩ : syracuseStep 3462095 = 5193143) B5193143
theorem B2308063 : Blo 1919435 2308063 := bstep (se 1 (by rfl) ⟨1731047, by rfl⟩ : syracuseStep 2308063 = 3462095) B3462095
theorem B3077417 : Blo 1919435 3077417 := bstep (se 2 (by rfl) ⟨1154031, by rfl⟩ : syracuseStep 3077417 = 2308063) B2308063
theorem B2051611 : Blo 1919435 2051611 := bstep (se 1 (by rfl) ⟨1538708, by rfl⟩ : syracuseStep 2051611 = 3077417) B3077417
theorem B10941925 : Blo 1919435 10941925 := bstep (se 4 (by rfl) ⟨1025805, by rfl⟩ : syracuseStep 10941925 = 2051611) B2051611
theorem B14589233 : Blo 1919435 14589233 := bstep (se 2 (by rfl) ⟨5470962, by rfl⟩ : syracuseStep 14589233 = 10941925) B10941925
theorem B9726155 : Blo 1919435 9726155 := bstep (se 1 (by rfl) ⟨7294616, by rfl⟩ : syracuseStep 9726155 = 14589233) B14589233
theorem B6484103 : Blo 1919435 6484103 := bstep (se 1 (by rfl) ⟨4863077, by rfl⟩ : syracuseStep 6484103 = 9726155) B9726155
theorem B4322735 : Blo 1919435 4322735 := bstep (se 1 (by rfl) ⟨3242051, by rfl⟩ : syracuseStep 4322735 = 6484103) B6484103
theorem B2881823 : Blo 1919435 2881823 := bstep (se 1 (by rfl) ⟨2161367, by rfl⟩ : syracuseStep 2881823 = 4322735) B4322735
theorem B1921215 : Blo 1919435 1921215 := bstep (se 1 (by rfl) ⟨1440911, by rfl⟩ : syracuseStep 1921215 = 2881823) B2881823
theorem B2881829 : Blo 1919435 2881829 := bbase (se 4 (by rfl) ⟨270171, by rfl⟩ : syracuseStep 2881829 = 540343) (by norm_num)
theorem B1921219 : Blo 1919435 1921219 := bstep (se 1 (by rfl) ⟨1440914, by rfl⟩ : syracuseStep 1921219 = 2881829) B2881829
theorem B2431549 : Blo 1919435 2431549 := bbase (se 3 (by rfl) ⟨455915, by rfl⟩ : syracuseStep 2431549 = 911831) (by norm_num)
theorem B3242065 : Blo 1919435 3242065 := bstep (se 2 (by rfl) ⟨1215774, by rfl⟩ : syracuseStep 3242065 = 2431549) B2431549
theorem B4322753 : Blo 1919435 4322753 := bstep (se 2 (by rfl) ⟨1621032, by rfl⟩ : syracuseStep 4322753 = 3242065) B3242065
theorem B2881835 : Blo 1919435 2881835 := bstep (se 1 (by rfl) ⟨2161376, by rfl⟩ : syracuseStep 2881835 = 4322753) B4322753
theorem B1921223 : Blo 1919435 1921223 := bstep (se 1 (by rfl) ⟨1440917, by rfl⟩ : syracuseStep 1921223 = 2881835) B2881835
theorem B2161381 : Blo 1919435 2161381 := bbase (se 4 (by rfl) ⟨202629, by rfl⟩ : syracuseStep 2161381 = 405259) (by norm_num)
theorem B2881841 : Blo 1919435 2881841 := bstep (se 2 (by rfl) ⟨1080690, by rfl⟩ : syracuseStep 2881841 = 2161381) B2161381
theorem B1921227 : Blo 1919435 1921227 := bstep (se 1 (by rfl) ⟨1440920, by rfl⟩ : syracuseStep 1921227 = 2881841) B2881841
theorem B4616165 : Blo 1919435 4616165 := bbase (se 4 (by rfl) ⟨432765, by rfl⟩ : syracuseStep 4616165 = 865531) (by norm_num)
theorem B3077443 : Blo 1919435 3077443 := bstep (se 1 (by rfl) ⟨2308082, by rfl⟩ : syracuseStep 3077443 = 4616165) B4616165
theorem B4103257 : Blo 1919435 4103257 := bstep (se 2 (by rfl) ⟨1538721, by rfl⟩ : syracuseStep 4103257 = 3077443) B3077443
theorem B5471009 : Blo 1919435 5471009 := bstep (se 2 (by rfl) ⟨2051628, by rfl⟩ : syracuseStep 5471009 = 4103257) B4103257
theorem B3647339 : Blo 1919435 3647339 := bstep (se 1 (by rfl) ⟨2735504, by rfl⟩ : syracuseStep 3647339 = 5471009) B5471009
theorem B2431559 : Blo 1919435 2431559 := bstep (se 1 (by rfl) ⟨1823669, by rfl⟩ : syracuseStep 2431559 = 3647339) B3647339
theorem B6484157 : Blo 1919435 6484157 := bstep (se 3 (by rfl) ⟨1215779, by rfl⟩ : syracuseStep 6484157 = 2431559) B2431559
theorem B4322771 : Blo 1919435 4322771 := bstep (se 1 (by rfl) ⟨3242078, by rfl⟩ : syracuseStep 4322771 = 6484157) B6484157
theorem B2881847 : Blo 1919435 2881847 := bstep (se 1 (by rfl) ⟨2161385, by rfl⟩ : syracuseStep 2881847 = 4322771) B4322771
theorem B1921231 : Blo 1919435 1921231 := bstep (se 1 (by rfl) ⟨1440923, by rfl⟩ : syracuseStep 1921231 = 2881847) B2881847
theorem B2881853 : Blo 1919435 2881853 := bbase (se 3 (by rfl) ⟨540347, by rfl⟩ : syracuseStep 2881853 = 1080695) (by norm_num)
theorem B1921235 : Blo 1919435 1921235 := bstep (se 1 (by rfl) ⟨1440926, by rfl⟩ : syracuseStep 1921235 = 2881853) B2881853
theorem B4322789 : Blo 1919435 4322789 := bbase (se 4 (by rfl) ⟨405261, by rfl⟩ : syracuseStep 4322789 = 810523) (by norm_num)
theorem B2881859 : Blo 1919435 2881859 := bstep (se 1 (by rfl) ⟨2161394, by rfl⟩ : syracuseStep 2881859 = 4322789) B4322789
theorem B1921239 : Blo 1919435 1921239 := bstep (se 1 (by rfl) ⟨1440929, by rfl⟩ : syracuseStep 1921239 = 2881859) B2881859
theorem B4863149 : Blo 1919435 4863149 := bbase (se 3 (by rfl) ⟨911840, by rfl⟩ : syracuseStep 4863149 = 1823681) (by norm_num)
theorem B3242099 : Blo 1919435 3242099 := bstep (se 1 (by rfl) ⟨2431574, by rfl⟩ : syracuseStep 3242099 = 4863149) B4863149
theorem B2161399 : Blo 1919435 2161399 := bstep (se 1 (by rfl) ⟨1621049, by rfl⟩ : syracuseStep 2161399 = 3242099) B3242099
theorem B2881865 : Blo 1919435 2881865 := bstep (se 2 (by rfl) ⟨1080699, by rfl⟩ : syracuseStep 2881865 = 2161399) B2161399
theorem B1921243 : Blo 1919435 1921243 := bstep (se 1 (by rfl) ⟨1440932, by rfl⟩ : syracuseStep 1921243 = 2881865) B2881865
theorem B1947461 : Blo 1919435 1947461 := bbase (se 4 (by rfl) ⟨182574, by rfl⟩ : syracuseStep 1947461 = 365149) (by norm_num)
theorem B5193229 : Blo 1919435 5193229 := bstep (se 3 (by rfl) ⟨973730, by rfl⟩ : syracuseStep 5193229 = 1947461) B1947461
theorem B6924305 : Blo 1919435 6924305 := bstep (se 2 (by rfl) ⟨2596614, by rfl⟩ : syracuseStep 6924305 = 5193229) B5193229
theorem B4616203 : Blo 1919435 4616203 := bstep (se 1 (by rfl) ⟨3462152, by rfl⟩ : syracuseStep 4616203 = 6924305) B6924305
theorem B6154937 : Blo 1919435 6154937 := bstep (se 2 (by rfl) ⟨2308101, by rfl⟩ : syracuseStep 6154937 = 4616203) B4616203
theorem B4103291 : Blo 1919435 4103291 := bstep (se 1 (by rfl) ⟨3077468, by rfl⟩ : syracuseStep 4103291 = 6154937) B6154937
theorem B2735527 : Blo 1919435 2735527 := bstep (se 1 (by rfl) ⟨2051645, by rfl⟩ : syracuseStep 2735527 = 4103291) B4103291
theorem B3647369 : Blo 1919435 3647369 := bstep (se 2 (by rfl) ⟨1367763, by rfl⟩ : syracuseStep 3647369 = 2735527) B2735527
theorem B9726317 : Blo 1919435 9726317 := bstep (se 3 (by rfl) ⟨1823684, by rfl⟩ : syracuseStep 9726317 = 3647369) B3647369
theorem B6484211 : Blo 1919435 6484211 := bstep (se 1 (by rfl) ⟨4863158, by rfl⟩ : syracuseStep 6484211 = 9726317) B9726317
theorem B4322807 : Blo 1919435 4322807 := bstep (se 1 (by rfl) ⟨3242105, by rfl⟩ : syracuseStep 4322807 = 6484211) B6484211
theorem B2881871 : Blo 1919435 2881871 := bstep (se 1 (by rfl) ⟨2161403, by rfl⟩ : syracuseStep 2881871 = 4322807) B4322807
theorem B1921247 : Blo 1919435 1921247 := bstep (se 1 (by rfl) ⟨1440935, by rfl⟩ : syracuseStep 1921247 = 2881871) B2881871
theorem B2881877 : Blo 1919435 2881877 := bbase (se 10 (by rfl) ⟨4221, by rfl⟩ : syracuseStep 2881877 = 8443) (by norm_num)
theorem B1921251 : Blo 1919435 1921251 := bstep (se 1 (by rfl) ⟨1440938, by rfl⟩ : syracuseStep 1921251 = 2881877) B2881877
theorem B5471077 : Blo 1919435 5471077 := bbase (se 4 (by rfl) ⟨512913, by rfl⟩ : syracuseStep 5471077 = 1025827) (by norm_num)
theorem B7294769 : Blo 1919435 7294769 := bstep (se 2 (by rfl) ⟨2735538, by rfl⟩ : syracuseStep 7294769 = 5471077) B5471077
theorem B4863179 : Blo 1919435 4863179 := bstep (se 1 (by rfl) ⟨3647384, by rfl⟩ : syracuseStep 4863179 = 7294769) B7294769
theorem B3242119 : Blo 1919435 3242119 := bstep (se 1 (by rfl) ⟨2431589, by rfl⟩ : syracuseStep 3242119 = 4863179) B4863179
theorem B4322825 : Blo 1919435 4322825 := bstep (se 2 (by rfl) ⟨1621059, by rfl⟩ : syracuseStep 4322825 = 3242119) B3242119
theorem B2881883 : Blo 1919435 2881883 := bstep (se 1 (by rfl) ⟨2161412, by rfl⟩ : syracuseStep 2881883 = 4322825) B4322825
theorem B1921255 : Blo 1919435 1921255 := bstep (se 1 (by rfl) ⟨1440941, by rfl⟩ : syracuseStep 1921255 = 2881883) B2881883
theorem B2161417 : Blo 1919435 2161417 := bbase (se 2 (by rfl) ⟨810531, by rfl⟩ : syracuseStep 2161417 = 1621063) (by norm_num)
theorem B2881889 : Blo 1919435 2881889 := bstep (se 2 (by rfl) ⟨1080708, by rfl⟩ : syracuseStep 2881889 = 2161417) B2161417
theorem B1921259 : Blo 1919435 1921259 := bstep (se 1 (by rfl) ⟨1440944, by rfl⟩ : syracuseStep 1921259 = 2881889) B2881889
theorem B2108029 : Blo 1919435 2108029 := bbase (se 3 (by rfl) ⟨395255, by rfl⟩ : syracuseStep 2108029 = 790511) (by norm_num)
theorem B2810705 : Blo 1919435 2810705 := bstep (se 2 (by rfl) ⟨1054014, by rfl⟩ : syracuseStep 2810705 = 2108029) B2108029
theorem B7495213 : Blo 1919435 7495213 := bstep (se 3 (by rfl) ⟨1405352, by rfl⟩ : syracuseStep 7495213 = 2810705) B2810705
theorem B9993617 : Blo 1919435 9993617 := bstep (se 2 (by rfl) ⟨3747606, by rfl⟩ : syracuseStep 9993617 = 7495213) B7495213
theorem B6662411 : Blo 1919435 6662411 := bstep (se 1 (by rfl) ⟨4996808, by rfl⟩ : syracuseStep 6662411 = 9993617) B9993617
theorem B4441607 : Blo 1919435 4441607 := bstep (se 1 (by rfl) ⟨3331205, by rfl⟩ : syracuseStep 4441607 = 6662411) B6662411
theorem B2961071 : Blo 1919435 2961071 := bstep (se 1 (by rfl) ⟨2220803, by rfl⟩ : syracuseStep 2961071 = 4441607) B4441607
theorem B31584757 : Blo 1919435 31584757 := bstep (se 5 (by rfl) ⟨1480535, by rfl⟩ : syracuseStep 31584757 = 2961071) B2961071
theorem B42113009 : Blo 1919435 42113009 := bstep (se 2 (by rfl) ⟨15792378, by rfl⟩ : syracuseStep 42113009 = 31584757) B31584757
theorem B28075339 : Blo 1919435 28075339 := bstep (se 1 (by rfl) ⟨21056504, by rfl⟩ : syracuseStep 28075339 = 42113009) B42113009
theorem B37433785 : Blo 1919435 37433785 := bstep (se 2 (by rfl) ⟨14037669, by rfl⟩ : syracuseStep 37433785 = 28075339) B28075339
theorem B49911713 : Blo 1919435 49911713 := bstep (se 2 (by rfl) ⟨18716892, by rfl⟩ : syracuseStep 49911713 = 37433785) B37433785
theorem B33274475 : Blo 1919435 33274475 := bstep (se 1 (by rfl) ⟨24955856, by rfl⟩ : syracuseStep 33274475 = 49911713) B49911713
theorem B22182983 : Blo 1919435 22182983 := bstep (se 1 (by rfl) ⟨16637237, by rfl⟩ : syracuseStep 22182983 = 33274475) B33274475
theorem B14788655 : Blo 1919435 14788655 := bstep (se 1 (by rfl) ⟨11091491, by rfl⟩ : syracuseStep 14788655 = 22182983) B22182983
theorem B9859103 : Blo 1919435 9859103 := bstep (se 1 (by rfl) ⟨7394327, by rfl⟩ : syracuseStep 9859103 = 14788655) B14788655
theorem B6572735 : Blo 1919435 6572735 := bstep (se 1 (by rfl) ⟨4929551, by rfl⟩ : syracuseStep 6572735 = 9859103) B9859103
theorem B4381823 : Blo 1919435 4381823 := bstep (se 1 (by rfl) ⟨3286367, by rfl⟩ : syracuseStep 4381823 = 6572735) B6572735
theorem B11684861 : Blo 1919435 11684861 := bstep (se 3 (by rfl) ⟨2190911, by rfl⟩ : syracuseStep 11684861 = 4381823) B4381823
theorem B7789907 : Blo 1919435 7789907 := bstep (se 1 (by rfl) ⟨5842430, by rfl⟩ : syracuseStep 7789907 = 11684861) B11684861
theorem B5193271 : Blo 1919435 5193271 := bstep (se 1 (by rfl) ⟨3894953, by rfl⟩ : syracuseStep 5193271 = 7789907) B7789907
theorem B6924361 : Blo 1919435 6924361 := bstep (se 2 (by rfl) ⟨2596635, by rfl⟩ : syracuseStep 6924361 = 5193271) B5193271
theorem B9232481 : Blo 1919435 9232481 := bstep (se 2 (by rfl) ⟨3462180, by rfl⟩ : syracuseStep 9232481 = 6924361) B6924361
theorem B24619949 : Blo 1919435 24619949 := bstep (se 3 (by rfl) ⟨4616240, by rfl⟩ : syracuseStep 24619949 = 9232481) B9232481
theorem B16413299 : Blo 1919435 16413299 := bstep (se 1 (by rfl) ⟨12309974, by rfl⟩ : syracuseStep 16413299 = 24619949) B24619949
theorem B10942199 : Blo 1919435 10942199 := bstep (se 1 (by rfl) ⟨8206649, by rfl⟩ : syracuseStep 10942199 = 16413299) B16413299
theorem B7294799 : Blo 1919435 7294799 := bstep (se 1 (by rfl) ⟨5471099, by rfl⟩ : syracuseStep 7294799 = 10942199) B10942199
theorem B4863199 : Blo 1919435 4863199 := bstep (se 1 (by rfl) ⟨3647399, by rfl⟩ : syracuseStep 4863199 = 7294799) B7294799
theorem B6484265 : Blo 1919435 6484265 := bstep (se 2 (by rfl) ⟨2431599, by rfl⟩ : syracuseStep 6484265 = 4863199) B4863199
theorem B4322843 : Blo 1919435 4322843 := bstep (se 1 (by rfl) ⟨3242132, by rfl⟩ : syracuseStep 4322843 = 6484265) B6484265
theorem B2881895 : Blo 1919435 2881895 := bstep (se 1 (by rfl) ⟨2161421, by rfl⟩ : syracuseStep 2881895 = 4322843) B4322843
theorem B1921263 : Blo 1919435 1921263 := bstep (se 1 (by rfl) ⟨1440947, by rfl⟩ : syracuseStep 1921263 = 2881895) B2881895
theorem B2881901 : Blo 1919435 2881901 := bbase (se 3 (by rfl) ⟨540356, by rfl⟩ : syracuseStep 2881901 = 1080713) (by norm_num)
theorem B1921267 : Blo 1919435 1921267 := bstep (se 1 (by rfl) ⟨1440950, by rfl⟩ : syracuseStep 1921267 = 2881901) B2881901
theorem B4322861 : Blo 1919435 4322861 := bbase (se 3 (by rfl) ⟨810536, by rfl⟩ : syracuseStep 4322861 = 1621073) (by norm_num)
theorem B2881907 : Blo 1919435 2881907 := bstep (se 1 (by rfl) ⟨2161430, by rfl⟩ : syracuseStep 2881907 = 4322861) B4322861
theorem B1921271 : Blo 1919435 1921271 := bstep (se 1 (by rfl) ⟨1440953, by rfl⟩ : syracuseStep 1921271 = 2881907) B2881907
theorem B31159829 : Blo 1919435 31159829 := bbase (se 6 (by rfl) ⟨730308, by rfl⟩ : syracuseStep 31159829 = 1460617) (by norm_num)
theorem B20773219 : Blo 1919435 20773219 := bstep (se 1 (by rfl) ⟨15579914, by rfl⟩ : syracuseStep 20773219 = 31159829) B31159829
theorem B27697625 : Blo 1919435 27697625 := bstep (se 2 (by rfl) ⟨10386609, by rfl⟩ : syracuseStep 27697625 = 20773219) B20773219
theorem B18465083 : Blo 1919435 18465083 := bstep (se 1 (by rfl) ⟨13848812, by rfl⟩ : syracuseStep 18465083 = 27697625) B27697625
theorem B12310055 : Blo 1919435 12310055 := bstep (se 1 (by rfl) ⟨9232541, by rfl⟩ : syracuseStep 12310055 = 18465083) B18465083
theorem B8206703 : Blo 1919435 8206703 := bstep (se 1 (by rfl) ⟨6155027, by rfl⟩ : syracuseStep 8206703 = 12310055) B12310055
theorem B5471135 : Blo 1919435 5471135 := bstep (se 1 (by rfl) ⟨4103351, by rfl⟩ : syracuseStep 5471135 = 8206703) B8206703
theorem B3647423 : Blo 1919435 3647423 := bstep (se 1 (by rfl) ⟨2735567, by rfl⟩ : syracuseStep 3647423 = 5471135) B5471135
theorem B2431615 : Blo 1919435 2431615 := bstep (se 1 (by rfl) ⟨1823711, by rfl⟩ : syracuseStep 2431615 = 3647423) B3647423
theorem B3242153 : Blo 1919435 3242153 := bstep (se 2 (by rfl) ⟨1215807, by rfl⟩ : syracuseStep 3242153 = 2431615) B2431615
theorem B2161435 : Blo 1919435 2161435 := bstep (se 1 (by rfl) ⟨1621076, by rfl⟩ : syracuseStep 2161435 = 3242153) B3242153
theorem B2881913 : Blo 1919435 2881913 := bstep (se 2 (by rfl) ⟨1080717, by rfl⟩ : syracuseStep 2881913 = 2161435) B2161435
theorem B1921275 : Blo 1919435 1921275 := bstep (se 1 (by rfl) ⟨1440956, by rfl⟩ : syracuseStep 1921275 = 2881913) B2881913
theorem B1947493 : Blo 1919435 1947493 := bbase (se 4 (by rfl) ⟨182577, by rfl⟩ : syracuseStep 1947493 = 365155) (by norm_num)
theorem B10386629 : Blo 1919435 10386629 := bstep (se 4 (by rfl) ⟨973746, by rfl⟩ : syracuseStep 10386629 = 1947493) B1947493
theorem B6924419 : Blo 1919435 6924419 := bstep (se 1 (by rfl) ⟨5193314, by rfl⟩ : syracuseStep 6924419 = 10386629) B10386629
theorem B4616279 : Blo 1919435 4616279 := bstep (se 1 (by rfl) ⟨3462209, by rfl⟩ : syracuseStep 4616279 = 6924419) B6924419
theorem B3077519 : Blo 1919435 3077519 := bstep (se 1 (by rfl) ⟨2308139, by rfl⟩ : syracuseStep 3077519 = 4616279) B4616279
theorem B32826869 : Blo 1919435 32826869 := bstep (se 5 (by rfl) ⟨1538759, by rfl⟩ : syracuseStep 32826869 = 3077519) B3077519
theorem B21884579 : Blo 1919435 21884579 := bstep (se 1 (by rfl) ⟨16413434, by rfl⟩ : syracuseStep 21884579 = 32826869) B32826869
theorem B14589719 : Blo 1919435 14589719 := bstep (se 1 (by rfl) ⟨10942289, by rfl⟩ : syracuseStep 14589719 = 21884579) B21884579
theorem B9726479 : Blo 1919435 9726479 := bstep (se 1 (by rfl) ⟨7294859, by rfl⟩ : syracuseStep 9726479 = 14589719) B14589719
theorem B6484319 : Blo 1919435 6484319 := bstep (se 1 (by rfl) ⟨4863239, by rfl⟩ : syracuseStep 6484319 = 9726479) B9726479
theorem B4322879 : Blo 1919435 4322879 := bstep (se 1 (by rfl) ⟨3242159, by rfl⟩ : syracuseStep 4322879 = 6484319) B6484319
theorem B2881919 : Blo 1919435 2881919 := bstep (se 1 (by rfl) ⟨2161439, by rfl⟩ : syracuseStep 2881919 = 4322879) B4322879
theorem B1921279 : Blo 1919435 1921279 := bstep (se 1 (by rfl) ⟨1440959, by rfl⟩ : syracuseStep 1921279 = 2881919) B2881919
theorem B2881925 : Blo 1919435 2881925 := bbase (se 4 (by rfl) ⟨270180, by rfl⟩ : syracuseStep 2881925 = 540361) (by norm_num)
theorem B1921283 : Blo 1919435 1921283 := bstep (se 1 (by rfl) ⟨1440962, by rfl⟩ : syracuseStep 1921283 = 2881925) B2881925
theorem B3242173 : Blo 1919435 3242173 := bbase (se 3 (by rfl) ⟨607907, by rfl⟩ : syracuseStep 3242173 = 1215815) (by norm_num)
theorem B4322897 : Blo 1919435 4322897 := bstep (se 2 (by rfl) ⟨1621086, by rfl⟩ : syracuseStep 4322897 = 3242173) B3242173
theorem B2881931 : Blo 1919435 2881931 := bstep (se 1 (by rfl) ⟨2161448, by rfl⟩ : syracuseStep 2881931 = 4322897) B4322897
theorem B1921287 : Blo 1919435 1921287 := bstep (se 1 (by rfl) ⟨1440965, by rfl⟩ : syracuseStep 1921287 = 2881931) B2881931
theorem B2161453 : Blo 1919435 2161453 := bbase (se 3 (by rfl) ⟨405272, by rfl⟩ : syracuseStep 2161453 = 810545) (by norm_num)
theorem B2881937 : Blo 1919435 2881937 := bstep (se 2 (by rfl) ⟨1080726, by rfl⟩ : syracuseStep 2881937 = 2161453) B2161453
theorem B1921291 : Blo 1919435 1921291 := bstep (se 1 (by rfl) ⟨1440968, by rfl⟩ : syracuseStep 1921291 = 2881937) B2881937
theorem B6484373 : Blo 1919435 6484373 := bbase (se 6 (by rfl) ⟨151977, by rfl⟩ : syracuseStep 6484373 = 303955) (by norm_num)
theorem B4322915 : Blo 1919435 4322915 := bstep (se 1 (by rfl) ⟨3242186, by rfl⟩ : syracuseStep 4322915 = 6484373) B6484373
theorem B2881943 : Blo 1919435 2881943 := bstep (se 1 (by rfl) ⟨2161457, by rfl⟩ : syracuseStep 2881943 = 4322915) B4322915
theorem B1921295 : Blo 1919435 1921295 := bstep (se 1 (by rfl) ⟨1440971, by rfl⟩ : syracuseStep 1921295 = 2881943) B2881943
theorem B2881949 : Blo 1919435 2881949 := bbase (se 3 (by rfl) ⟨540365, by rfl⟩ : syracuseStep 2881949 = 1080731) (by norm_num)
theorem B1921299 : Blo 1919435 1921299 := bstep (se 1 (by rfl) ⟨1440974, by rfl⟩ : syracuseStep 1921299 = 2881949) B2881949
theorem B4322933 : Blo 1919435 4322933 := bbase (se 5 (by rfl) ⟨202637, by rfl⟩ : syracuseStep 4322933 = 405275) (by norm_num)
theorem B2881955 : Blo 1919435 2881955 := bstep (se 1 (by rfl) ⟨2161466, by rfl⟩ : syracuseStep 2881955 = 4322933) B4322933
theorem B1921303 : Blo 1919435 1921303 := bstep (se 1 (by rfl) ⟨1440977, by rfl⟩ : syracuseStep 1921303 = 2881955) B2881955
theorem B4679333 : Blo 1919435 4679333 := bbase (se 4 (by rfl) ⟨438687, by rfl⟩ : syracuseStep 4679333 = 877375) (by norm_num)
theorem B3119555 : Blo 1919435 3119555 := bstep (se 1 (by rfl) ⟨2339666, by rfl⟩ : syracuseStep 3119555 = 4679333) B4679333
theorem B2079703 : Blo 1919435 2079703 := bstep (se 1 (by rfl) ⟨1559777, by rfl⟩ : syracuseStep 2079703 = 3119555) B3119555
theorem B2772937 : Blo 1919435 2772937 := bstep (se 2 (by rfl) ⟨1039851, by rfl⟩ : syracuseStep 2772937 = 2079703) B2079703
theorem B3697249 : Blo 1919435 3697249 := bstep (se 2 (by rfl) ⟨1386468, by rfl⟩ : syracuseStep 3697249 = 2772937) B2772937
theorem B4929665 : Blo 1919435 4929665 := bstep (se 2 (by rfl) ⟨1848624, by rfl⟩ : syracuseStep 4929665 = 3697249) B3697249
theorem B13145773 : Blo 1919435 13145773 := bstep (se 3 (by rfl) ⟨2464832, by rfl⟩ : syracuseStep 13145773 = 4929665) B4929665
theorem B17527697 : Blo 1919435 17527697 := bstep (se 2 (by rfl) ⟨6572886, by rfl⟩ : syracuseStep 17527697 = 13145773) B13145773
theorem B11685131 : Blo 1919435 11685131 := bstep (se 1 (by rfl) ⟨8763848, by rfl⟩ : syracuseStep 11685131 = 17527697) B17527697
theorem B7790087 : Blo 1919435 7790087 := bstep (se 1 (by rfl) ⟨5842565, by rfl⟩ : syracuseStep 7790087 = 11685131) B11685131
theorem B5193391 : Blo 1919435 5193391 := bstep (se 1 (by rfl) ⟨3895043, by rfl⟩ : syracuseStep 5193391 = 7790087) B7790087
theorem B6924521 : Blo 1919435 6924521 := bstep (se 2 (by rfl) ⟨2596695, by rfl⟩ : syracuseStep 6924521 = 5193391) B5193391
theorem B4616347 : Blo 1919435 4616347 := bstep (se 1 (by rfl) ⟨3462260, by rfl⟩ : syracuseStep 4616347 = 6924521) B6924521
theorem B6155129 : Blo 1919435 6155129 := bstep (se 2 (by rfl) ⟨2308173, by rfl⟩ : syracuseStep 6155129 = 4616347) B4616347
theorem B16413677 : Blo 1919435 16413677 := bstep (se 3 (by rfl) ⟨3077564, by rfl⟩ : syracuseStep 16413677 = 6155129) B6155129
theorem B10942451 : Blo 1919435 10942451 := bstep (se 1 (by rfl) ⟨8206838, by rfl⟩ : syracuseStep 10942451 = 16413677) B16413677
theorem B7294967 : Blo 1919435 7294967 := bstep (se 1 (by rfl) ⟨5471225, by rfl⟩ : syracuseStep 7294967 = 10942451) B10942451
theorem B4863311 : Blo 1919435 4863311 := bstep (se 1 (by rfl) ⟨3647483, by rfl⟩ : syracuseStep 4863311 = 7294967) B7294967
theorem B3242207 : Blo 1919435 3242207 := bstep (se 1 (by rfl) ⟨2431655, by rfl⟩ : syracuseStep 3242207 = 4863311) B4863311
theorem B2161471 : Blo 1919435 2161471 := bstep (se 1 (by rfl) ⟨1621103, by rfl⟩ : syracuseStep 2161471 = 3242207) B3242207
theorem B2881961 : Blo 1919435 2881961 := bstep (se 2 (by rfl) ⟨1080735, by rfl⟩ : syracuseStep 2881961 = 2161471) B2161471
theorem B1921307 : Blo 1919435 1921307 := bstep (se 1 (by rfl) ⟨1440980, by rfl⟩ : syracuseStep 1921307 = 2881961) B2881961
theorem B7294981 : Blo 1919435 7294981 := bbase (se 4 (by rfl) ⟨683904, by rfl⟩ : syracuseStep 7294981 = 1367809) (by norm_num)
theorem B9726641 : Blo 1919435 9726641 := bstep (se 2 (by rfl) ⟨3647490, by rfl⟩ : syracuseStep 9726641 = 7294981) B7294981
theorem B6484427 : Blo 1919435 6484427 := bstep (se 1 (by rfl) ⟨4863320, by rfl⟩ : syracuseStep 6484427 = 9726641) B9726641
theorem B4322951 : Blo 1919435 4322951 := bstep (se 1 (by rfl) ⟨3242213, by rfl⟩ : syracuseStep 4322951 = 6484427) B6484427
theorem B2881967 : Blo 1919435 2881967 := bstep (se 1 (by rfl) ⟨2161475, by rfl⟩ : syracuseStep 2881967 = 4322951) B4322951
theorem B1921311 : Blo 1919435 1921311 := bstep (se 1 (by rfl) ⟨1440983, by rfl⟩ : syracuseStep 1921311 = 2881967) B2881967
theorem B2881973 : Blo 1919435 2881973 := bbase (se 5 (by rfl) ⟨135092, by rfl⟩ : syracuseStep 2881973 = 270185) (by norm_num)
theorem B1921315 : Blo 1919435 1921315 := bstep (se 1 (by rfl) ⟨1440986, by rfl⟩ : syracuseStep 1921315 = 2881973) B2881973
theorem B4863341 : Blo 1919435 4863341 := bbase (se 3 (by rfl) ⟨911876, by rfl⟩ : syracuseStep 4863341 = 1823753) (by norm_num)
theorem B3242227 : Blo 1919435 3242227 := bstep (se 1 (by rfl) ⟨2431670, by rfl⟩ : syracuseStep 3242227 = 4863341) B4863341
theorem B4322969 : Blo 1919435 4322969 := bstep (se 2 (by rfl) ⟨1621113, by rfl⟩ : syracuseStep 4322969 = 3242227) B3242227
theorem B2881979 : Blo 1919435 2881979 := bstep (se 1 (by rfl) ⟨2161484, by rfl⟩ : syracuseStep 2881979 = 4322969) B4322969
theorem B1921319 : Blo 1919435 1921319 := bstep (se 1 (by rfl) ⟨1440989, by rfl⟩ : syracuseStep 1921319 = 2881979) B2881979
theorem B2161489 : Blo 1919435 2161489 := bbase (se 2 (by rfl) ⟨810558, by rfl⟩ : syracuseStep 2161489 = 1621117) (by norm_num)
theorem B2881985 : Blo 1919435 2881985 := bstep (se 2 (by rfl) ⟨1080744, by rfl⟩ : syracuseStep 2881985 = 2161489) B2161489
theorem B1921323 : Blo 1919435 1921323 := bstep (se 1 (by rfl) ⟨1440992, by rfl⟩ : syracuseStep 1921323 = 2881985) B2881985
theorem B3077597 : Blo 1919435 3077597 := bbase (se 3 (by rfl) ⟨577049, by rfl⟩ : syracuseStep 3077597 = 1154099) (by norm_num)
theorem B2051731 : Blo 1919435 2051731 := bstep (se 1 (by rfl) ⟨1538798, by rfl⟩ : syracuseStep 2051731 = 3077597) B3077597
theorem B2735641 : Blo 1919435 2735641 := bstep (se 2 (by rfl) ⟨1025865, by rfl⟩ : syracuseStep 2735641 = 2051731) B2051731
theorem B3647521 : Blo 1919435 3647521 := bstep (se 2 (by rfl) ⟨1367820, by rfl⟩ : syracuseStep 3647521 = 2735641) B2735641
theorem B4863361 : Blo 1919435 4863361 := bstep (se 2 (by rfl) ⟨1823760, by rfl⟩ : syracuseStep 4863361 = 3647521) B3647521
theorem B6484481 : Blo 1919435 6484481 := bstep (se 2 (by rfl) ⟨2431680, by rfl⟩ : syracuseStep 6484481 = 4863361) B4863361
theorem B4322987 : Blo 1919435 4322987 := bstep (se 1 (by rfl) ⟨3242240, by rfl⟩ : syracuseStep 4322987 = 6484481) B6484481
theorem B2881991 : Blo 1919435 2881991 := bstep (se 1 (by rfl) ⟨2161493, by rfl⟩ : syracuseStep 2881991 = 4322987) B4322987
theorem B1921327 : Blo 1919435 1921327 := bstep (se 1 (by rfl) ⟨1440995, by rfl⟩ : syracuseStep 1921327 = 2881991) B2881991
theorem B2881997 : Blo 1919435 2881997 := bbase (se 3 (by rfl) ⟨540374, by rfl⟩ : syracuseStep 2881997 = 1080749) (by norm_num)
theorem B1921331 : Blo 1919435 1921331 := bstep (se 1 (by rfl) ⟨1440998, by rfl⟩ : syracuseStep 1921331 = 2881997) B2881997
theorem B4323005 : Blo 1919435 4323005 := bbase (se 3 (by rfl) ⟨810563, by rfl⟩ : syracuseStep 4323005 = 1621127) (by norm_num)
theorem B2882003 : Blo 1919435 2882003 := bstep (se 1 (by rfl) ⟨2161502, by rfl⟩ : syracuseStep 2882003 = 4323005) B4323005
theorem B1921335 : Blo 1919435 1921335 := bstep (se 1 (by rfl) ⟨1441001, by rfl⟩ : syracuseStep 1921335 = 2882003) B2882003
theorem B3242261 : Blo 1919435 3242261 := bbase (se 6 (by rfl) ⟨75990, by rfl⟩ : syracuseStep 3242261 = 151981) (by norm_num)
theorem B2161507 : Blo 1919435 2161507 := bstep (se 1 (by rfl) ⟨1621130, by rfl⟩ : syracuseStep 2161507 = 3242261) B3242261
theorem B2882009 : Blo 1919435 2882009 := bstep (se 2 (by rfl) ⟨1080753, by rfl⟩ : syracuseStep 2882009 = 2161507) B2161507
theorem B1921339 : Blo 1919435 1921339 := bstep (se 1 (by rfl) ⟨1441004, by rfl⟩ : syracuseStep 1921339 = 2882009) B2882009
theorem B17528021 : Blo 1919435 17528021 := bbase (se 7 (by rfl) ⟨205406, by rfl⟩ : syracuseStep 17528021 = 410813) (by norm_num)
theorem B11685347 : Blo 1919435 11685347 := bstep (se 1 (by rfl) ⟨8764010, by rfl⟩ : syracuseStep 11685347 = 17528021) B17528021
theorem B7790231 : Blo 1919435 7790231 := bstep (se 1 (by rfl) ⟨5842673, by rfl⟩ : syracuseStep 7790231 = 11685347) B11685347
theorem B5193487 : Blo 1919435 5193487 := bstep (se 1 (by rfl) ⟨3895115, by rfl⟩ : syracuseStep 5193487 = 7790231) B7790231
theorem B27698597 : Blo 1919435 27698597 := bstep (se 4 (by rfl) ⟨2596743, by rfl⟩ : syracuseStep 27698597 = 5193487) B5193487
theorem B18465731 : Blo 1919435 18465731 := bstep (se 1 (by rfl) ⟨13849298, by rfl⟩ : syracuseStep 18465731 = 27698597) B27698597
theorem B12310487 : Blo 1919435 12310487 := bstep (se 1 (by rfl) ⟨9232865, by rfl⟩ : syracuseStep 12310487 = 18465731) B18465731
theorem B8206991 : Blo 1919435 8206991 := bstep (se 1 (by rfl) ⟨6155243, by rfl⟩ : syracuseStep 8206991 = 12310487) B12310487
theorem B5471327 : Blo 1919435 5471327 := bstep (se 1 (by rfl) ⟨4103495, by rfl⟩ : syracuseStep 5471327 = 8206991) B8206991
theorem B14590205 : Blo 1919435 14590205 := bstep (se 3 (by rfl) ⟨2735663, by rfl⟩ : syracuseStep 14590205 = 5471327) B5471327
theorem B9726803 : Blo 1919435 9726803 := bstep (se 1 (by rfl) ⟨7295102, by rfl⟩ : syracuseStep 9726803 = 14590205) B14590205
theorem B6484535 : Blo 1919435 6484535 := bstep (se 1 (by rfl) ⟨4863401, by rfl⟩ : syracuseStep 6484535 = 9726803) B9726803
theorem B4323023 : Blo 1919435 4323023 := bstep (se 1 (by rfl) ⟨3242267, by rfl⟩ : syracuseStep 4323023 = 6484535) B6484535
theorem B2882015 : Blo 1919435 2882015 := bstep (se 1 (by rfl) ⟨2161511, by rfl⟩ : syracuseStep 2882015 = 4323023) B4323023
theorem B1921343 : Blo 1919435 1921343 := bstep (se 1 (by rfl) ⟨1441007, by rfl⟩ : syracuseStep 1921343 = 2882015) B2882015
theorem B2882021 : Blo 1919435 2882021 := bbase (se 4 (by rfl) ⟨270189, by rfl⟩ : syracuseStep 2882021 = 540379) (by norm_num)
theorem B1921347 : Blo 1919435 1921347 := bstep (se 1 (by rfl) ⟨1441010, by rfl⟩ : syracuseStep 1921347 = 2882021) B2882021
theorem B4616453 : Blo 1919435 4616453 := bbase (se 4 (by rfl) ⟨432792, by rfl⟩ : syracuseStep 4616453 = 865585) (by norm_num)
theorem B12310541 : Blo 1919435 12310541 := bstep (se 3 (by rfl) ⟨2308226, by rfl⟩ : syracuseStep 12310541 = 4616453) B4616453
theorem B8207027 : Blo 1919435 8207027 := bstep (se 1 (by rfl) ⟨6155270, by rfl⟩ : syracuseStep 8207027 = 12310541) B12310541
theorem B5471351 : Blo 1919435 5471351 := bstep (se 1 (by rfl) ⟨4103513, by rfl⟩ : syracuseStep 5471351 = 8207027) B8207027
theorem B3647567 : Blo 1919435 3647567 := bstep (se 1 (by rfl) ⟨2735675, by rfl⟩ : syracuseStep 3647567 = 5471351) B5471351
theorem B2431711 : Blo 1919435 2431711 := bstep (se 1 (by rfl) ⟨1823783, by rfl⟩ : syracuseStep 2431711 = 3647567) B3647567
theorem B3242281 : Blo 1919435 3242281 := bstep (se 2 (by rfl) ⟨1215855, by rfl⟩ : syracuseStep 3242281 = 2431711) B2431711
theorem B4323041 : Blo 1919435 4323041 := bstep (se 2 (by rfl) ⟨1621140, by rfl⟩ : syracuseStep 4323041 = 3242281) B3242281
theorem B2882027 : Blo 1919435 2882027 := bstep (se 1 (by rfl) ⟨2161520, by rfl⟩ : syracuseStep 2882027 = 4323041) B4323041
theorem B1921351 : Blo 1919435 1921351 := bstep (se 1 (by rfl) ⟨1441013, by rfl⟩ : syracuseStep 1921351 = 2882027) B2882027
theorem B2161525 : Blo 1919435 2161525 := bbase (se 5 (by rfl) ⟨101321, by rfl⟩ : syracuseStep 2161525 = 202643) (by norm_num)
theorem B2882033 : Blo 1919435 2882033 := bstep (se 2 (by rfl) ⟨1080762, by rfl⟩ : syracuseStep 2882033 = 2161525) B2161525
theorem B1921355 : Blo 1919435 1921355 := bstep (se 1 (by rfl) ⟨1441016, by rfl⟩ : syracuseStep 1921355 = 2882033) B2882033
theorem B2431721 : Blo 1919435 2431721 := bbase (se 2 (by rfl) ⟨911895, by rfl⟩ : syracuseStep 2431721 = 1823791) (by norm_num)
theorem B6484589 : Blo 1919435 6484589 := bstep (se 3 (by rfl) ⟨1215860, by rfl⟩ : syracuseStep 6484589 = 2431721) B2431721
theorem B4323059 : Blo 1919435 4323059 := bstep (se 1 (by rfl) ⟨3242294, by rfl⟩ : syracuseStep 4323059 = 6484589) B6484589
theorem B2882039 : Blo 1919435 2882039 := bstep (se 1 (by rfl) ⟨2161529, by rfl⟩ : syracuseStep 2882039 = 4323059) B4323059
theorem B1921359 : Blo 1919435 1921359 := bstep (se 1 (by rfl) ⟨1441019, by rfl⟩ : syracuseStep 1921359 = 2882039) B2882039
theorem B2882045 : Blo 1919435 2882045 := bbase (se 3 (by rfl) ⟨540383, by rfl⟩ : syracuseStep 2882045 = 1080767) (by norm_num)
theorem B1921363 : Blo 1919435 1921363 := bstep (se 1 (by rfl) ⟨1441022, by rfl⟩ : syracuseStep 1921363 = 2882045) B2882045
theorem B4323077 : Blo 1919435 4323077 := bbase (se 4 (by rfl) ⟨405288, by rfl⟩ : syracuseStep 4323077 = 810577) (by norm_num)
theorem B2882051 : Blo 1919435 2882051 := bstep (se 1 (by rfl) ⟨2161538, by rfl⟩ : syracuseStep 2882051 = 4323077) B4323077
theorem B1921367 : Blo 1919435 1921367 := bstep (se 1 (by rfl) ⟨1441025, by rfl⟩ : syracuseStep 1921367 = 2882051) B2882051
theorem B3647605 : Blo 1919435 3647605 := bbase (se 5 (by rfl) ⟨170981, by rfl⟩ : syracuseStep 3647605 = 341963) (by norm_num)
theorem B4863473 : Blo 1919435 4863473 := bstep (se 2 (by rfl) ⟨1823802, by rfl⟩ : syracuseStep 4863473 = 3647605) B3647605
theorem B3242315 : Blo 1919435 3242315 := bstep (se 1 (by rfl) ⟨2431736, by rfl⟩ : syracuseStep 3242315 = 4863473) B4863473
theorem B2161543 : Blo 1919435 2161543 := bstep (se 1 (by rfl) ⟨1621157, by rfl⟩ : syracuseStep 2161543 = 3242315) B3242315
theorem B2882057 : Blo 1919435 2882057 := bstep (se 2 (by rfl) ⟨1080771, by rfl⟩ : syracuseStep 2882057 = 2161543) B2161543
theorem B1921371 : Blo 1919435 1921371 := bstep (se 1 (by rfl) ⟨1441028, by rfl⟩ : syracuseStep 1921371 = 2882057) B2882057
theorem B9726965 : Blo 1919435 9726965 := bbase (se 5 (by rfl) ⟨455951, by rfl⟩ : syracuseStep 9726965 = 911903) (by norm_num)
theorem B6484643 : Blo 1919435 6484643 := bstep (se 1 (by rfl) ⟨4863482, by rfl⟩ : syracuseStep 6484643 = 9726965) B9726965
theorem B4323095 : Blo 1919435 4323095 := bstep (se 1 (by rfl) ⟨3242321, by rfl⟩ : syracuseStep 4323095 = 6484643) B6484643
theorem B2882063 : Blo 1919435 2882063 := bstep (se 1 (by rfl) ⟨2161547, by rfl⟩ : syracuseStep 2882063 = 4323095) B4323095
theorem B1921375 : Blo 1919435 1921375 := bstep (se 1 (by rfl) ⟨1441031, by rfl⟩ : syracuseStep 1921375 = 2882063) B2882063
theorem B2882069 : Blo 1919435 2882069 := bbase (se 6 (by rfl) ⟨67548, by rfl⟩ : syracuseStep 2882069 = 135097) (by norm_num)
theorem B1921379 : Blo 1919435 1921379 := bstep (se 1 (by rfl) ⟨1441034, by rfl⟩ : syracuseStep 1921379 = 2882069) B2882069
theorem B16414325 : Blo 1919435 16414325 := bbase (se 5 (by rfl) ⟨769421, by rfl⟩ : syracuseStep 16414325 = 1538843) (by norm_num)
theorem B10942883 : Blo 1919435 10942883 := bstep (se 1 (by rfl) ⟨8207162, by rfl⟩ : syracuseStep 10942883 = 16414325) B16414325
theorem B7295255 : Blo 1919435 7295255 := bstep (se 1 (by rfl) ⟨5471441, by rfl⟩ : syracuseStep 7295255 = 10942883) B10942883
theorem B4863503 : Blo 1919435 4863503 := bstep (se 1 (by rfl) ⟨3647627, by rfl⟩ : syracuseStep 4863503 = 7295255) B7295255
theorem B3242335 : Blo 1919435 3242335 := bstep (se 1 (by rfl) ⟨2431751, by rfl⟩ : syracuseStep 3242335 = 4863503) B4863503
theorem B4323113 : Blo 1919435 4323113 := bstep (se 2 (by rfl) ⟨1621167, by rfl⟩ : syracuseStep 4323113 = 3242335) B3242335
theorem B2882075 : Blo 1919435 2882075 := bstep (se 1 (by rfl) ⟨2161556, by rfl⟩ : syracuseStep 2882075 = 4323113) B4323113
theorem B1921383 : Blo 1919435 1921383 := bstep (se 1 (by rfl) ⟨1441037, by rfl⟩ : syracuseStep 1921383 = 2882075) B2882075
theorem B2161561 : Blo 1919435 2161561 := bbase (se 2 (by rfl) ⟨810585, by rfl⟩ : syracuseStep 2161561 = 1621171) (by norm_num)
theorem B2882081 : Blo 1919435 2882081 := bstep (se 2 (by rfl) ⟨1080780, by rfl⟩ : syracuseStep 2882081 = 2161561) B2161561
theorem B1921387 : Blo 1919435 1921387 := bstep (se 1 (by rfl) ⟨1441040, by rfl⟩ : syracuseStep 1921387 = 2882081) B2882081
theorem B7295285 : Blo 1919435 7295285 := bbase (se 5 (by rfl) ⟨341966, by rfl⟩ : syracuseStep 7295285 = 683933) (by norm_num)
theorem B4863523 : Blo 1919435 4863523 := bstep (se 1 (by rfl) ⟨3647642, by rfl⟩ : syracuseStep 4863523 = 7295285) B7295285
theorem B6484697 : Blo 1919435 6484697 := bstep (se 2 (by rfl) ⟨2431761, by rfl⟩ : syracuseStep 6484697 = 4863523) B4863523
theorem B4323131 : Blo 1919435 4323131 := bstep (se 1 (by rfl) ⟨3242348, by rfl⟩ : syracuseStep 4323131 = 6484697) B6484697
theorem B2882087 : Blo 1919435 2882087 := bstep (se 1 (by rfl) ⟨2161565, by rfl⟩ : syracuseStep 2882087 = 4323131) B4323131
theorem B1921391 : Blo 1919435 1921391 := bstep (se 1 (by rfl) ⟨1441043, by rfl⟩ : syracuseStep 1921391 = 2882087) B2882087
theorem B2882093 : Blo 1919435 2882093 := bbase (se 3 (by rfl) ⟨540392, by rfl⟩ : syracuseStep 2882093 = 1080785) (by norm_num)
theorem B1921395 : Blo 1919435 1921395 := bstep (se 1 (by rfl) ⟨1441046, by rfl⟩ : syracuseStep 1921395 = 2882093) B2882093
theorem B4323149 : Blo 1919435 4323149 := bbase (se 3 (by rfl) ⟨810590, by rfl⟩ : syracuseStep 4323149 = 1621181) (by norm_num)
theorem B2882099 : Blo 1919435 2882099 := bstep (se 1 (by rfl) ⟨2161574, by rfl⟩ : syracuseStep 2882099 = 4323149) B4323149
theorem B1921399 : Blo 1919435 1921399 := bstep (se 1 (by rfl) ⟨1441049, by rfl⟩ : syracuseStep 1921399 = 2882099) B2882099
theorem B2431777 : Blo 1919435 2431777 := bbase (se 2 (by rfl) ⟨911916, by rfl⟩ : syracuseStep 2431777 = 1823833) (by norm_num)
theorem B3242369 : Blo 1919435 3242369 := bstep (se 2 (by rfl) ⟨1215888, by rfl⟩ : syracuseStep 3242369 = 2431777) B2431777
theorem B2161579 : Blo 1919435 2161579 := bstep (se 1 (by rfl) ⟨1621184, by rfl⟩ : syracuseStep 2161579 = 3242369) B3242369
theorem B2882105 : Blo 1919435 2882105 := bstep (se 2 (by rfl) ⟨1080789, by rfl⟩ : syracuseStep 2882105 = 2161579) B2161579
theorem B1921403 : Blo 1919435 1921403 := bstep (se 1 (by rfl) ⟨1441052, by rfl⟩ : syracuseStep 1921403 = 2882105) B2882105
theorem B21886037 : Blo 1919435 21886037 := bbase (se 8 (by rfl) ⟨128238, by rfl⟩ : syracuseStep 21886037 = 256477) (by norm_num)
theorem B14590691 : Blo 1919435 14590691 := bstep (se 1 (by rfl) ⟨10943018, by rfl⟩ : syracuseStep 14590691 = 21886037) B21886037
theorem B9727127 : Blo 1919435 9727127 := bstep (se 1 (by rfl) ⟨7295345, by rfl⟩ : syracuseStep 9727127 = 14590691) B14590691
theorem B6484751 : Blo 1919435 6484751 := bstep (se 1 (by rfl) ⟨4863563, by rfl⟩ : syracuseStep 6484751 = 9727127) B9727127
theorem B4323167 : Blo 1919435 4323167 := bstep (se 1 (by rfl) ⟨3242375, by rfl⟩ : syracuseStep 4323167 = 6484751) B6484751
theorem B2882111 : Blo 1919435 2882111 := bstep (se 1 (by rfl) ⟨2161583, by rfl⟩ : syracuseStep 2882111 = 4323167) B4323167
theorem B1921407 : Blo 1919435 1921407 := bstep (se 1 (by rfl) ⟨1441055, by rfl⟩ : syracuseStep 1921407 = 2882111) B2882111
theorem B2882117 : Blo 1919435 2882117 := bbase (se 4 (by rfl) ⟨270198, by rfl⟩ : syracuseStep 2882117 = 540397) (by norm_num)
theorem B1921411 : Blo 1919435 1921411 := bstep (se 1 (by rfl) ⟨1441058, by rfl⟩ : syracuseStep 1921411 = 2882117) B2882117
theorem B3242389 : Blo 1919435 3242389 := bbase (se 6 (by rfl) ⟨75993, by rfl⟩ : syracuseStep 3242389 = 151987) (by norm_num)
theorem B4323185 : Blo 1919435 4323185 := bstep (se 2 (by rfl) ⟨1621194, by rfl⟩ : syracuseStep 4323185 = 3242389) B3242389
theorem B2882123 : Blo 1919435 2882123 := bstep (se 1 (by rfl) ⟨2161592, by rfl⟩ : syracuseStep 2882123 = 4323185) B4323185
theorem B1921415 : Blo 1919435 1921415 := bstep (se 1 (by rfl) ⟨1441061, by rfl⟩ : syracuseStep 1921415 = 2882123) B2882123
theorem B2161597 : Blo 1919435 2161597 := bbase (se 3 (by rfl) ⟨405299, by rfl⟩ : syracuseStep 2161597 = 810599) (by norm_num)
theorem B2882129 : Blo 1919435 2882129 := bstep (se 2 (by rfl) ⟨1080798, by rfl⟩ : syracuseStep 2882129 = 2161597) B2161597
theorem B1921419 : Blo 1919435 1921419 := bstep (se 1 (by rfl) ⟨1441064, by rfl⟩ : syracuseStep 1921419 = 2882129) B2882129
theorem B6484805 : Blo 1919435 6484805 := bbase (se 4 (by rfl) ⟨607950, by rfl⟩ : syracuseStep 6484805 = 1215901) (by norm_num)
theorem B4323203 : Blo 1919435 4323203 := bstep (se 1 (by rfl) ⟨3242402, by rfl⟩ : syracuseStep 4323203 = 6484805) B6484805
theorem B2882135 : Blo 1919435 2882135 := bstep (se 1 (by rfl) ⟨2161601, by rfl⟩ : syracuseStep 2882135 = 4323203) B4323203
theorem B1921423 : Blo 1919435 1921423 := bstep (se 1 (by rfl) ⟨1441067, by rfl⟩ : syracuseStep 1921423 = 2882135) B2882135
theorem B2882141 : Blo 1919435 2882141 := bbase (se 3 (by rfl) ⟨540401, by rfl⟩ : syracuseStep 2882141 = 1080803) (by norm_num)
theorem B1921427 : Blo 1919435 1921427 := bstep (se 1 (by rfl) ⟨1441070, by rfl⟩ : syracuseStep 1921427 = 2882141) B2882141
theorem B4323221 : Blo 1919435 4323221 := bbase (se 6 (by rfl) ⟨101325, by rfl⟩ : syracuseStep 4323221 = 202651) (by norm_num)
theorem B2882147 : Blo 1919435 2882147 := bstep (se 1 (by rfl) ⟨2161610, by rfl⟩ : syracuseStep 2882147 = 4323221) B4323221
theorem B1921431 : Blo 1919435 1921431 := bstep (se 1 (by rfl) ⟨1441073, by rfl⟩ : syracuseStep 1921431 = 2882147) B2882147
theorem B4103693 : Blo 1919435 4103693 := bbase (se 3 (by rfl) ⟨769442, by rfl⟩ : syracuseStep 4103693 = 1538885) (by norm_num)
theorem B2735795 : Blo 1919435 2735795 := bstep (se 1 (by rfl) ⟨2051846, by rfl⟩ : syracuseStep 2735795 = 4103693) B4103693
theorem B7295453 : Blo 1919435 7295453 := bstep (se 3 (by rfl) ⟨1367897, by rfl⟩ : syracuseStep 7295453 = 2735795) B2735795
theorem B4863635 : Blo 1919435 4863635 := bstep (se 1 (by rfl) ⟨3647726, by rfl⟩ : syracuseStep 4863635 = 7295453) B7295453
theorem B3242423 : Blo 1919435 3242423 := bstep (se 1 (by rfl) ⟨2431817, by rfl⟩ : syracuseStep 3242423 = 4863635) B4863635
theorem B2161615 : Blo 1919435 2161615 := bstep (se 1 (by rfl) ⟨1621211, by rfl⟩ : syracuseStep 2161615 = 3242423) B3242423
theorem B2882153 : Blo 1919435 2882153 := bstep (se 2 (by rfl) ⟨1080807, by rfl⟩ : syracuseStep 2882153 = 2161615) B2161615
theorem B1921435 : Blo 1919435 1921435 := bstep (se 1 (by rfl) ⟨1441076, by rfl⟩ : syracuseStep 1921435 = 2882153) B2882153
theorem C0 (j : ℕ) (h1 : 479858 ≤ j) (h2 : j ≤ 480358) : Blo 1919435 (4 * j + 3) := by
  interval_cases j
  · exact B1919435
  · exact B1919439
  · exact B1919443
  · exact B1919447
  · exact B1919451
  · exact B1919455
  · exact B1919459
  · exact B1919463
  · exact B1919467
  · exact B1919471
  · exact B1919475
  · exact B1919479
  · exact B1919483
  · exact B1919487
  · exact B1919491
  · exact B1919495
  · exact B1919499
  · exact B1919503
  · exact B1919507
  · exact B1919511
  · exact B1919515
  · exact B1919519
  · exact B1919523
  · exact B1919527
  · exact B1919531
  · exact B1919535
  · exact B1919539
  · exact B1919543
  · exact B1919547
  · exact B1919551
  · exact B1919555
  · exact B1919559
  · exact B1919563
  · exact B1919567
  · exact B1919571
  · exact B1919575
  · exact B1919579
  · exact B1919583
  · exact B1919587
  · exact B1919591
  · exact B1919595
  · exact B1919599
  · exact B1919603
  · exact B1919607
  · exact B1919611
  · exact B1919615
  · exact B1919619
  · exact B1919623
  · exact B1919627
  · exact B1919631
  · exact B1919635
  · exact B1919639
  · exact B1919643
  · exact B1919647
  · exact B1919651
  · exact B1919655
  · exact B1919659
  · exact B1919663
  · exact B1919667
  · exact B1919671
  · exact B1919675
  · exact B1919679
  · exact B1919683
  · exact B1919687
  · exact B1919691
  · exact B1919695
  · exact B1919699
  · exact B1919703
  · exact B1919707
  · exact B1919711
  · exact B1919715
  · exact B1919719
  · exact B1919723
  · exact B1919727
  · exact B1919731
  · exact B1919735
  · exact B1919739
  · exact B1919743
  · exact B1919747
  · exact B1919751
  · exact B1919755
  · exact B1919759
  · exact B1919763
  · exact B1919767
  · exact B1919771
  · exact B1919775
  · exact B1919779
  · exact B1919783
  · exact B1919787
  · exact B1919791
  · exact B1919795
  · exact B1919799
  · exact B1919803
  · exact B1919807
  · exact B1919811
  · exact B1919815
  · exact B1919819
  · exact B1919823
  · exact B1919827
  · exact B1919831
  · exact B1919835
  · exact B1919839
  · exact B1919843
  · exact B1919847
  · exact B1919851
  · exact B1919855
  · exact B1919859
  · exact B1919863
  · exact B1919867
  · exact B1919871
  · exact B1919875
  · exact B1919879
  · exact B1919883
  · exact B1919887
  · exact B1919891
  · exact B1919895
  · exact B1919899
  · exact B1919903
  · exact B1919907
  · exact B1919911
  · exact B1919915
  · exact B1919919
  · exact B1919923
  · exact B1919927
  · exact B1919931
  · exact B1919935
  · exact B1919939
  · exact B1919943
  · exact B1919947
  · exact B1919951
  · exact B1919955
  · exact B1919959
  · exact B1919963
  · exact B1919967
  · exact B1919971
  · exact B1919975
  · exact B1919979
  · exact B1919983
  · exact B1919987
  · exact B1919991
  · exact B1919995
  · exact B1919999
  · exact B1920003
  · exact B1920007
  · exact B1920011
  · exact B1920015
  · exact B1920019
  · exact B1920023
  · exact B1920027
  · exact B1920031
  · exact B1920035
  · exact B1920039
  · exact B1920043
  · exact B1920047
  · exact B1920051
  · exact B1920055
  · exact B1920059
  · exact B1920063
  · exact B1920067
  · exact B1920071
  · exact B1920075
  · exact B1920079
  · exact B1920083
  · exact B1920087
  · exact B1920091
  · exact B1920095
  · exact B1920099
  · exact B1920103
  · exact B1920107
  · exact B1920111
  · exact B1920115
  · exact B1920119
  · exact B1920123
  · exact B1920127
  · exact B1920131
  · exact B1920135
  · exact B1920139
  · exact B1920143
  · exact B1920147
  · exact B1920151
  · exact B1920155
  · exact B1920159
  · exact B1920163
  · exact B1920167
  · exact B1920171
  · exact B1920175
  · exact B1920179
  · exact B1920183
  · exact B1920187
  · exact B1920191
  · exact B1920195
  · exact B1920199
  · exact B1920203
  · exact B1920207
  · exact B1920211
  · exact B1920215
  · exact B1920219
  · exact B1920223
  · exact B1920227
  · exact B1920231
  · exact B1920235
  · exact B1920239
  · exact B1920243
  · exact B1920247
  · exact B1920251
  · exact B1920255
  · exact B1920259
  · exact B1920263
  · exact B1920267
  · exact B1920271
  · exact B1920275
  · exact B1920279
  · exact B1920283
  · exact B1920287
  · exact B1920291
  · exact B1920295
  · exact B1920299
  · exact B1920303
  · exact B1920307
  · exact B1920311
  · exact B1920315
  · exact B1920319
  · exact B1920323
  · exact B1920327
  · exact B1920331
  · exact B1920335
  · exact B1920339
  · exact B1920343
  · exact B1920347
  · exact B1920351
  · exact B1920355
  · exact B1920359
  · exact B1920363
  · exact B1920367
  · exact B1920371
  · exact B1920375
  · exact B1920379
  · exact B1920383
  · exact B1920387
  · exact B1920391
  · exact B1920395
  · exact B1920399
  · exact B1920403
  · exact B1920407
  · exact B1920411
  · exact B1920415
  · exact B1920419
  · exact B1920423
  · exact B1920427
  · exact B1920431
  · exact B1920435
  · exact B1920439
  · exact B1920443
  · exact B1920447
  · exact B1920451
  · exact B1920455
  · exact B1920459
  · exact B1920463
  · exact B1920467
  · exact B1920471
  · exact B1920475
  · exact B1920479
  · exact B1920483
  · exact B1920487
  · exact B1920491
  · exact B1920495
  · exact B1920499
  · exact B1920503
  · exact B1920507
  · exact B1920511
  · exact B1920515
  · exact B1920519
  · exact B1920523
  · exact B1920527
  · exact B1920531
  · exact B1920535
  · exact B1920539
  · exact B1920543
  · exact B1920547
  · exact B1920551
  · exact B1920555
  · exact B1920559
  · exact B1920563
  · exact B1920567
  · exact B1920571
  · exact B1920575
  · exact B1920579
  · exact B1920583
  · exact B1920587
  · exact B1920591
  · exact B1920595
  · exact B1920599
  · exact B1920603
  · exact B1920607
  · exact B1920611
  · exact B1920615
  · exact B1920619
  · exact B1920623
  · exact B1920627
  · exact B1920631
  · exact B1920635
  · exact B1920639
  · exact B1920643
  · exact B1920647
  · exact B1920651
  · exact B1920655
  · exact B1920659
  · exact B1920663
  · exact B1920667
  · exact B1920671
  · exact B1920675
  · exact B1920679
  · exact B1920683
  · exact B1920687
  · exact B1920691
  · exact B1920695
  · exact B1920699
  · exact B1920703
  · exact B1920707
  · exact B1920711
  · exact B1920715
  · exact B1920719
  · exact B1920723
  · exact B1920727
  · exact B1920731
  · exact B1920735
  · exact B1920739
  · exact B1920743
  · exact B1920747
  · exact B1920751
  · exact B1920755
  · exact B1920759
  · exact B1920763
  · exact B1920767
  · exact B1920771
  · exact B1920775
  · exact B1920779
  · exact B1920783
  · exact B1920787
  · exact B1920791
  · exact B1920795
  · exact B1920799
  · exact B1920803
  · exact B1920807
  · exact B1920811
  · exact B1920815
  · exact B1920819
  · exact B1920823
  · exact B1920827
  · exact B1920831
  · exact B1920835
  · exact B1920839
  · exact B1920843
  · exact B1920847
  · exact B1920851
  · exact B1920855
  · exact B1920859
  · exact B1920863
  · exact B1920867
  · exact B1920871
  · exact B1920875
  · exact B1920879
  · exact B1920883
  · exact B1920887
  · exact B1920891
  · exact B1920895
  · exact B1920899
  · exact B1920903
  · exact B1920907
  · exact B1920911
  · exact B1920915
  · exact B1920919
  · exact B1920923
  · exact B1920927
  · exact B1920931
  · exact B1920935
  · exact B1920939
  · exact B1920943
  · exact B1920947
  · exact B1920951
  · exact B1920955
  · exact B1920959
  · exact B1920963
  · exact B1920967
  · exact B1920971
  · exact B1920975
  · exact B1920979
  · exact B1920983
  · exact B1920987
  · exact B1920991
  · exact B1920995
  · exact B1920999
  · exact B1921003
  · exact B1921007
  · exact B1921011
  · exact B1921015
  · exact B1921019
  · exact B1921023
  · exact B1921027
  · exact B1921031
  · exact B1921035
  · exact B1921039
  · exact B1921043
  · exact B1921047
  · exact B1921051
  · exact B1921055
  · exact B1921059
  · exact B1921063
  · exact B1921067
  · exact B1921071
  · exact B1921075
  · exact B1921079
  · exact B1921083
  · exact B1921087
  · exact B1921091
  · exact B1921095
  · exact B1921099
  · exact B1921103
  · exact B1921107
  · exact B1921111
  · exact B1921115
  · exact B1921119
  · exact B1921123
  · exact B1921127
  · exact B1921131
  · exact B1921135
  · exact B1921139
  · exact B1921143
  · exact B1921147
  · exact B1921151
  · exact B1921155
  · exact B1921159
  · exact B1921163
  · exact B1921167
  · exact B1921171
  · exact B1921175
  · exact B1921179
  · exact B1921183
  · exact B1921187
  · exact B1921191
  · exact B1921195
  · exact B1921199
  · exact B1921203
  · exact B1921207
  · exact B1921211
  · exact B1921215
  · exact B1921219
  · exact B1921223
  · exact B1921227
  · exact B1921231
  · exact B1921235
  · exact B1921239
  · exact B1921243
  · exact B1921247
  · exact B1921251
  · exact B1921255
  · exact B1921259
  · exact B1921263
  · exact B1921267
  · exact B1921271
  · exact B1921275
  · exact B1921279
  · exact B1921283
  · exact B1921287
  · exact B1921291
  · exact B1921295
  · exact B1921299
  · exact B1921303
  · exact B1921307
  · exact B1921311
  · exact B1921315
  · exact B1921319
  · exact B1921323
  · exact B1921327
  · exact B1921331
  · exact B1921335
  · exact B1921339
  · exact B1921343
  · exact B1921347
  · exact B1921351
  · exact B1921355
  · exact B1921359
  · exact B1921363
  · exact B1921367
  · exact B1921371
  · exact B1921375
  · exact B1921379
  · exact B1921383
  · exact B1921387
  · exact B1921391
  · exact B1921395
  · exact B1921399
  · exact B1921403
  · exact B1921407
  · exact B1921411
  · exact B1921415
  · exact B1921419
  · exact B1921423
  · exact B1921427
  · exact B1921431
  · exact B1921435
theorem solution (m : ℕ) (hlo : 1919435 ≤ m) (hhi : m ≤ 1921435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 479858 ≤ j := by omega
    have hj2 : j ≤ 480358 := by omega
    have hb : Blo 1919435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
