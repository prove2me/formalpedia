-- Prove2me | solution 1 for syracuse_descends_range_2063435_2065435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:49:39.499398+00:00
-- url     : https://prove2.me/submissions/60271a1d-74d1-44f3-b488-e8d368717b9a

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

theorem B2321365 : Blo 2063435 2321365 := bbase (se 7 (by rfl) ⟨27203, by rfl⟩ : syracuseStep 2321365 = 54407) (by norm_num)
theorem B3095153 : Blo 2063435 3095153 := bstep (se 2 (by rfl) ⟨1160682, by rfl⟩ : syracuseStep 3095153 = 2321365) B2321365
theorem B2063435 : Blo 2063435 2063435 := bstep (se 1 (by rfl) ⟨1547576, by rfl⟩ : syracuseStep 2063435 = 3095153) B3095153
theorem B2611541 : Blo 2063435 2611541 := bbase (se 10 (by rfl) ⟨3825, by rfl⟩ : syracuseStep 2611541 = 7651) (by norm_num)
theorem B6964109 : Blo 2063435 6964109 := bstep (se 3 (by rfl) ⟨1305770, by rfl⟩ : syracuseStep 6964109 = 2611541) B2611541
theorem B4642739 : Blo 2063435 4642739 := bstep (se 1 (by rfl) ⟨3482054, by rfl⟩ : syracuseStep 4642739 = 6964109) B6964109
theorem B3095159 : Blo 2063435 3095159 := bstep (se 1 (by rfl) ⟨2321369, by rfl⟩ : syracuseStep 3095159 = 4642739) B4642739
theorem B2063439 : Blo 2063435 2063439 := bstep (se 1 (by rfl) ⟨1547579, by rfl⟩ : syracuseStep 2063439 = 3095159) B3095159
theorem B3095165 : Blo 2063435 3095165 := bbase (se 3 (by rfl) ⟨580343, by rfl⟩ : syracuseStep 3095165 = 1160687) (by norm_num)
theorem B2063443 : Blo 2063435 2063443 := bstep (se 1 (by rfl) ⟨1547582, by rfl⟩ : syracuseStep 2063443 = 3095165) B3095165
theorem B4642757 : Blo 2063435 4642757 := bbase (se 4 (by rfl) ⟨435258, by rfl⟩ : syracuseStep 4642757 = 870517) (by norm_num)
theorem B3095171 : Blo 2063435 3095171 := bstep (se 1 (by rfl) ⟨2321378, by rfl⟩ : syracuseStep 3095171 = 4642757) B4642757
theorem B2063447 : Blo 2063435 2063447 := bstep (se 1 (by rfl) ⟨1547585, by rfl⟩ : syracuseStep 2063447 = 3095171) B3095171
theorem B8814005 : Blo 2063435 8814005 := bbase (se 5 (by rfl) ⟨413156, by rfl⟩ : syracuseStep 8814005 = 826313) (by norm_num)
theorem B5876003 : Blo 2063435 5876003 := bstep (se 1 (by rfl) ⟨4407002, by rfl⟩ : syracuseStep 5876003 = 8814005) B8814005
theorem B3917335 : Blo 2063435 3917335 := bstep (se 1 (by rfl) ⟨2938001, by rfl⟩ : syracuseStep 3917335 = 5876003) B5876003
theorem B5223113 : Blo 2063435 5223113 := bstep (se 2 (by rfl) ⟨1958667, by rfl⟩ : syracuseStep 5223113 = 3917335) B3917335
theorem B3482075 : Blo 2063435 3482075 := bstep (se 1 (by rfl) ⟨2611556, by rfl⟩ : syracuseStep 3482075 = 5223113) B5223113
theorem B2321383 : Blo 2063435 2321383 := bstep (se 1 (by rfl) ⟨1741037, by rfl⟩ : syracuseStep 2321383 = 3482075) B3482075
theorem B3095177 : Blo 2063435 3095177 := bstep (se 2 (by rfl) ⟨1160691, by rfl⟩ : syracuseStep 3095177 = 2321383) B2321383
theorem B2063451 : Blo 2063435 2063451 := bstep (se 1 (by rfl) ⟨1547588, by rfl⟩ : syracuseStep 2063451 = 3095177) B3095177
theorem B10446245 : Blo 2063435 10446245 := bbase (se 4 (by rfl) ⟨979335, by rfl⟩ : syracuseStep 10446245 = 1958671) (by norm_num)
theorem B6964163 : Blo 2063435 6964163 := bstep (se 1 (by rfl) ⟨5223122, by rfl⟩ : syracuseStep 6964163 = 10446245) B10446245
theorem B4642775 : Blo 2063435 4642775 := bstep (se 1 (by rfl) ⟨3482081, by rfl⟩ : syracuseStep 4642775 = 6964163) B6964163
theorem B3095183 : Blo 2063435 3095183 := bstep (se 1 (by rfl) ⟨2321387, by rfl⟩ : syracuseStep 3095183 = 4642775) B4642775
theorem B2063455 : Blo 2063435 2063455 := bstep (se 1 (by rfl) ⟨1547591, by rfl⟩ : syracuseStep 2063455 = 3095183) B3095183
theorem B3095189 : Blo 2063435 3095189 := bbase (se 6 (by rfl) ⟨72543, by rfl⟩ : syracuseStep 3095189 = 145087) (by norm_num)
theorem B2063459 : Blo 2063435 2063459 := bstep (se 1 (by rfl) ⟨1547594, by rfl⟩ : syracuseStep 2063459 = 3095189) B3095189
theorem B2353069 : Blo 2063435 2353069 := bbase (se 3 (by rfl) ⟨441200, by rfl⟩ : syracuseStep 2353069 = 882401) (by norm_num)
theorem B12549701 : Blo 2063435 12549701 := bstep (se 4 (by rfl) ⟨1176534, by rfl⟩ : syracuseStep 12549701 = 2353069) B2353069
theorem B33465869 : Blo 2063435 33465869 := bstep (se 3 (by rfl) ⟨6274850, by rfl⟩ : syracuseStep 33465869 = 12549701) B12549701
theorem B22310579 : Blo 2063435 22310579 := bstep (se 1 (by rfl) ⟨16732934, by rfl⟩ : syracuseStep 22310579 = 33465869) B33465869
theorem B14873719 : Blo 2063435 14873719 := bstep (se 1 (by rfl) ⟨11155289, by rfl⟩ : syracuseStep 14873719 = 22310579) B22310579
theorem B19831625 : Blo 2063435 19831625 := bstep (se 2 (by rfl) ⟨7436859, by rfl⟩ : syracuseStep 19831625 = 14873719) B14873719
theorem B13221083 : Blo 2063435 13221083 := bstep (se 1 (by rfl) ⟨9915812, by rfl⟩ : syracuseStep 13221083 = 19831625) B19831625
theorem B8814055 : Blo 2063435 8814055 := bstep (se 1 (by rfl) ⟨6610541, by rfl⟩ : syracuseStep 8814055 = 13221083) B13221083
theorem B11752073 : Blo 2063435 11752073 := bstep (se 2 (by rfl) ⟨4407027, by rfl⟩ : syracuseStep 11752073 = 8814055) B8814055
theorem B7834715 : Blo 2063435 7834715 := bstep (se 1 (by rfl) ⟨5876036, by rfl⟩ : syracuseStep 7834715 = 11752073) B11752073
theorem B5223143 : Blo 2063435 5223143 := bstep (se 1 (by rfl) ⟨3917357, by rfl⟩ : syracuseStep 5223143 = 7834715) B7834715
theorem B3482095 : Blo 2063435 3482095 := bstep (se 1 (by rfl) ⟨2611571, by rfl⟩ : syracuseStep 3482095 = 5223143) B5223143
theorem B4642793 : Blo 2063435 4642793 := bstep (se 2 (by rfl) ⟨1741047, by rfl⟩ : syracuseStep 4642793 = 3482095) B3482095
theorem B3095195 : Blo 2063435 3095195 := bstep (se 1 (by rfl) ⟨2321396, by rfl⟩ : syracuseStep 3095195 = 4642793) B4642793
theorem B2063463 : Blo 2063435 2063463 := bstep (se 1 (by rfl) ⟨1547597, by rfl⟩ : syracuseStep 2063463 = 3095195) B3095195
theorem B2321401 : Blo 2063435 2321401 := bbase (se 2 (by rfl) ⟨870525, by rfl⟩ : syracuseStep 2321401 = 1741051) (by norm_num)
theorem B3095201 : Blo 2063435 3095201 := bstep (se 2 (by rfl) ⟨1160700, by rfl⟩ : syracuseStep 3095201 = 2321401) B2321401
theorem B2063467 : Blo 2063435 2063467 := bstep (se 1 (by rfl) ⟨1547600, by rfl⟩ : syracuseStep 2063467 = 3095201) B3095201
theorem B2091625 : Blo 2063435 2091625 := bbase (se 2 (by rfl) ⟨784359, by rfl⟩ : syracuseStep 2091625 = 1568719) (by norm_num)
theorem B11155333 : Blo 2063435 11155333 := bstep (se 4 (by rfl) ⟨1045812, by rfl⟩ : syracuseStep 11155333 = 2091625) B2091625
theorem B14873777 : Blo 2063435 14873777 := bstep (se 2 (by rfl) ⟨5577666, by rfl⟩ : syracuseStep 14873777 = 11155333) B11155333
theorem B9915851 : Blo 2063435 9915851 := bstep (se 1 (by rfl) ⟨7436888, by rfl⟩ : syracuseStep 9915851 = 14873777) B14873777
theorem B6610567 : Blo 2063435 6610567 := bstep (se 1 (by rfl) ⟨4957925, by rfl⟩ : syracuseStep 6610567 = 9915851) B9915851
theorem B8814089 : Blo 2063435 8814089 := bstep (se 2 (by rfl) ⟨3305283, by rfl⟩ : syracuseStep 8814089 = 6610567) B6610567
theorem B5876059 : Blo 2063435 5876059 := bstep (se 1 (by rfl) ⟨4407044, by rfl⟩ : syracuseStep 5876059 = 8814089) B8814089
theorem B7834745 : Blo 2063435 7834745 := bstep (se 2 (by rfl) ⟨2938029, by rfl⟩ : syracuseStep 7834745 = 5876059) B5876059
theorem B5223163 : Blo 2063435 5223163 := bstep (se 1 (by rfl) ⟨3917372, by rfl⟩ : syracuseStep 5223163 = 7834745) B7834745
theorem B6964217 : Blo 2063435 6964217 := bstep (se 2 (by rfl) ⟨2611581, by rfl⟩ : syracuseStep 6964217 = 5223163) B5223163
theorem B4642811 : Blo 2063435 4642811 := bstep (se 1 (by rfl) ⟨3482108, by rfl⟩ : syracuseStep 4642811 = 6964217) B6964217
theorem B3095207 : Blo 2063435 3095207 := bstep (se 1 (by rfl) ⟨2321405, by rfl⟩ : syracuseStep 3095207 = 4642811) B4642811
theorem B2063471 : Blo 2063435 2063471 := bstep (se 1 (by rfl) ⟨1547603, by rfl⟩ : syracuseStep 2063471 = 3095207) B3095207
theorem B3095213 : Blo 2063435 3095213 := bbase (se 3 (by rfl) ⟨580352, by rfl⟩ : syracuseStep 3095213 = 1160705) (by norm_num)
theorem B2063475 : Blo 2063435 2063475 := bstep (se 1 (by rfl) ⟨1547606, by rfl⟩ : syracuseStep 2063475 = 3095213) B3095213
theorem B4642829 : Blo 2063435 4642829 := bbase (se 3 (by rfl) ⟨870530, by rfl⟩ : syracuseStep 4642829 = 1741061) (by norm_num)
theorem B3095219 : Blo 2063435 3095219 := bstep (se 1 (by rfl) ⟨2321414, by rfl⟩ : syracuseStep 3095219 = 4642829) B4642829
theorem B2063479 : Blo 2063435 2063479 := bstep (se 1 (by rfl) ⟨1547609, by rfl⟩ : syracuseStep 2063479 = 3095219) B3095219
theorem B2611597 : Blo 2063435 2611597 := bbase (se 3 (by rfl) ⟨489674, by rfl⟩ : syracuseStep 2611597 = 979349) (by norm_num)
theorem B3482129 : Blo 2063435 3482129 := bstep (se 2 (by rfl) ⟨1305798, by rfl⟩ : syracuseStep 3482129 = 2611597) B2611597
theorem B2321419 : Blo 2063435 2321419 := bstep (se 1 (by rfl) ⟨1741064, by rfl⟩ : syracuseStep 2321419 = 3482129) B3482129
theorem B3095225 : Blo 2063435 3095225 := bstep (se 2 (by rfl) ⟨1160709, by rfl⟩ : syracuseStep 3095225 = 2321419) B2321419
theorem B2063483 : Blo 2063435 2063483 := bstep (se 1 (by rfl) ⟨1547612, by rfl⟩ : syracuseStep 2063483 = 3095225) B3095225
theorem B2091641 : Blo 2063435 2091641 := bbase (se 2 (by rfl) ⟨784365, by rfl⟩ : syracuseStep 2091641 = 1568731) (by norm_num)
theorem B5577709 : Blo 2063435 5577709 := bstep (se 3 (by rfl) ⟨1045820, by rfl⟩ : syracuseStep 5577709 = 2091641) B2091641
theorem B7436945 : Blo 2063435 7436945 := bstep (se 2 (by rfl) ⟨2788854, by rfl⟩ : syracuseStep 7436945 = 5577709) B5577709
theorem B19831853 : Blo 2063435 19831853 := bstep (se 3 (by rfl) ⟨3718472, by rfl⟩ : syracuseStep 19831853 = 7436945) B7436945
theorem B13221235 : Blo 2063435 13221235 := bstep (se 1 (by rfl) ⟨9915926, by rfl⟩ : syracuseStep 13221235 = 19831853) B19831853
theorem B17628313 : Blo 2063435 17628313 := bstep (se 2 (by rfl) ⟨6610617, by rfl⟩ : syracuseStep 17628313 = 13221235) B13221235
theorem B23504417 : Blo 2063435 23504417 := bstep (se 2 (by rfl) ⟨8814156, by rfl⟩ : syracuseStep 23504417 = 17628313) B17628313
theorem B15669611 : Blo 2063435 15669611 := bstep (se 1 (by rfl) ⟨11752208, by rfl⟩ : syracuseStep 15669611 = 23504417) B23504417
theorem B10446407 : Blo 2063435 10446407 := bstep (se 1 (by rfl) ⟨7834805, by rfl⟩ : syracuseStep 10446407 = 15669611) B15669611
theorem B6964271 : Blo 2063435 6964271 := bstep (se 1 (by rfl) ⟨5223203, by rfl⟩ : syracuseStep 6964271 = 10446407) B10446407
theorem B4642847 : Blo 2063435 4642847 := bstep (se 1 (by rfl) ⟨3482135, by rfl⟩ : syracuseStep 4642847 = 6964271) B6964271
theorem B3095231 : Blo 2063435 3095231 := bstep (se 1 (by rfl) ⟨2321423, by rfl⟩ : syracuseStep 3095231 = 4642847) B4642847
theorem B2063487 : Blo 2063435 2063487 := bstep (se 1 (by rfl) ⟨1547615, by rfl⟩ : syracuseStep 2063487 = 3095231) B3095231
theorem B3095237 : Blo 2063435 3095237 := bbase (se 4 (by rfl) ⟨290178, by rfl⟩ : syracuseStep 3095237 = 580357) (by norm_num)
theorem B2063491 : Blo 2063435 2063491 := bstep (se 1 (by rfl) ⟨1547618, by rfl⟩ : syracuseStep 2063491 = 3095237) B3095237
theorem B3482149 : Blo 2063435 3482149 := bbase (se 4 (by rfl) ⟨326451, by rfl⟩ : syracuseStep 3482149 = 652903) (by norm_num)
theorem B4642865 : Blo 2063435 4642865 := bstep (se 2 (by rfl) ⟨1741074, by rfl⟩ : syracuseStep 4642865 = 3482149) B3482149
theorem B3095243 : Blo 2063435 3095243 := bstep (se 1 (by rfl) ⟨2321432, by rfl⟩ : syracuseStep 3095243 = 4642865) B4642865
theorem B2063495 : Blo 2063435 2063495 := bstep (se 1 (by rfl) ⟨1547621, by rfl⟩ : syracuseStep 2063495 = 3095243) B3095243
theorem B2321437 : Blo 2063435 2321437 := bbase (se 3 (by rfl) ⟨435269, by rfl⟩ : syracuseStep 2321437 = 870539) (by norm_num)
theorem B3095249 : Blo 2063435 3095249 := bstep (se 2 (by rfl) ⟨1160718, by rfl⟩ : syracuseStep 3095249 = 2321437) B2321437
theorem B2063499 : Blo 2063435 2063499 := bstep (se 1 (by rfl) ⟨1547624, by rfl⟩ : syracuseStep 2063499 = 3095249) B3095249
theorem B6964325 : Blo 2063435 6964325 := bbase (se 4 (by rfl) ⟨652905, by rfl⟩ : syracuseStep 6964325 = 1305811) (by norm_num)
theorem B4642883 : Blo 2063435 4642883 := bstep (se 1 (by rfl) ⟨3482162, by rfl⟩ : syracuseStep 4642883 = 6964325) B6964325
theorem B3095255 : Blo 2063435 3095255 := bstep (se 1 (by rfl) ⟨2321441, by rfl⟩ : syracuseStep 3095255 = 4642883) B4642883
theorem B2063503 : Blo 2063435 2063503 := bstep (se 1 (by rfl) ⟨1547627, by rfl⟩ : syracuseStep 2063503 = 3095255) B3095255
theorem B3095261 : Blo 2063435 3095261 := bbase (se 3 (by rfl) ⟨580361, by rfl⟩ : syracuseStep 3095261 = 1160723) (by norm_num)
theorem B2063507 : Blo 2063435 2063507 := bstep (se 1 (by rfl) ⟨1547630, by rfl⟩ : syracuseStep 2063507 = 3095261) B3095261
theorem B4642901 : Blo 2063435 4642901 := bbase (se 8 (by rfl) ⟨27204, by rfl⟩ : syracuseStep 4642901 = 54409) (by norm_num)
theorem B3095267 : Blo 2063435 3095267 := bstep (se 1 (by rfl) ⟨2321450, by rfl⟩ : syracuseStep 3095267 = 4642901) B4642901
theorem B2063511 : Blo 2063435 2063511 := bstep (se 1 (by rfl) ⟨1547633, by rfl⟩ : syracuseStep 2063511 = 3095267) B3095267
theorem B6610709 : Blo 2063435 6610709 := bbase (se 6 (by rfl) ⟨154938, by rfl⟩ : syracuseStep 6610709 = 309877) (by norm_num)
theorem B4407139 : Blo 2063435 4407139 := bstep (se 1 (by rfl) ⟨3305354, by rfl⟩ : syracuseStep 4407139 = 6610709) B6610709
theorem B5876185 : Blo 2063435 5876185 := bstep (se 2 (by rfl) ⟨2203569, by rfl⟩ : syracuseStep 5876185 = 4407139) B4407139
theorem B7834913 : Blo 2063435 7834913 := bstep (se 2 (by rfl) ⟨2938092, by rfl⟩ : syracuseStep 7834913 = 5876185) B5876185
theorem B5223275 : Blo 2063435 5223275 := bstep (se 1 (by rfl) ⟨3917456, by rfl⟩ : syracuseStep 5223275 = 7834913) B7834913
theorem B3482183 : Blo 2063435 3482183 := bstep (se 1 (by rfl) ⟨2611637, by rfl⟩ : syracuseStep 3482183 = 5223275) B5223275
theorem B2321455 : Blo 2063435 2321455 := bstep (se 1 (by rfl) ⟨1741091, by rfl⟩ : syracuseStep 2321455 = 3482183) B3482183
theorem B3095273 : Blo 2063435 3095273 := bstep (se 2 (by rfl) ⟨1160727, by rfl⟩ : syracuseStep 3095273 = 2321455) B2321455
theorem B2063515 : Blo 2063435 2063515 := bstep (se 1 (by rfl) ⟨1547636, by rfl⟩ : syracuseStep 2063515 = 3095273) B3095273
theorem B5294549 : Blo 2063435 5294549 := bbase (se 7 (by rfl) ⟨62045, by rfl⟩ : syracuseStep 5294549 = 124091) (by norm_num)
theorem B3529699 : Blo 2063435 3529699 := bstep (se 1 (by rfl) ⟨2647274, by rfl⟩ : syracuseStep 3529699 = 5294549) B5294549
theorem B18825061 : Blo 2063435 18825061 := bstep (se 4 (by rfl) ⟨1764849, by rfl⟩ : syracuseStep 18825061 = 3529699) B3529699
theorem B25100081 : Blo 2063435 25100081 := bstep (se 2 (by rfl) ⟨9412530, by rfl⟩ : syracuseStep 25100081 = 18825061) B18825061
theorem B16733387 : Blo 2063435 16733387 := bstep (se 1 (by rfl) ⟨12550040, by rfl⟩ : syracuseStep 16733387 = 25100081) B25100081
theorem B11155591 : Blo 2063435 11155591 := bstep (se 1 (by rfl) ⟨8366693, by rfl⟩ : syracuseStep 11155591 = 16733387) B16733387
theorem B14874121 : Blo 2063435 14874121 := bstep (se 2 (by rfl) ⟨5577795, by rfl⟩ : syracuseStep 14874121 = 11155591) B11155591
theorem B19832161 : Blo 2063435 19832161 := bstep (se 2 (by rfl) ⟨7437060, by rfl⟩ : syracuseStep 19832161 = 14874121) B14874121
theorem B26442881 : Blo 2063435 26442881 := bstep (se 2 (by rfl) ⟨9916080, by rfl⟩ : syracuseStep 26442881 = 19832161) B19832161
theorem B17628587 : Blo 2063435 17628587 := bstep (se 1 (by rfl) ⟨13221440, by rfl⟩ : syracuseStep 17628587 = 26442881) B26442881
theorem B11752391 : Blo 2063435 11752391 := bstep (se 1 (by rfl) ⟨8814293, by rfl⟩ : syracuseStep 11752391 = 17628587) B17628587
theorem B7834927 : Blo 2063435 7834927 := bstep (se 1 (by rfl) ⟨5876195, by rfl⟩ : syracuseStep 7834927 = 11752391) B11752391
theorem B10446569 : Blo 2063435 10446569 := bstep (se 2 (by rfl) ⟨3917463, by rfl⟩ : syracuseStep 10446569 = 7834927) B7834927
theorem B6964379 : Blo 2063435 6964379 := bstep (se 1 (by rfl) ⟨5223284, by rfl⟩ : syracuseStep 6964379 = 10446569) B10446569
theorem B4642919 : Blo 2063435 4642919 := bstep (se 1 (by rfl) ⟨3482189, by rfl⟩ : syracuseStep 4642919 = 6964379) B6964379
theorem B3095279 : Blo 2063435 3095279 := bstep (se 1 (by rfl) ⟨2321459, by rfl⟩ : syracuseStep 3095279 = 4642919) B4642919
theorem B2063519 : Blo 2063435 2063519 := bstep (se 1 (by rfl) ⟨1547639, by rfl⟩ : syracuseStep 2063519 = 3095279) B3095279
theorem B3095285 : Blo 2063435 3095285 := bbase (se 5 (by rfl) ⟨145091, by rfl⟩ : syracuseStep 3095285 = 290183) (by norm_num)
theorem B2063523 : Blo 2063435 2063523 := bstep (se 1 (by rfl) ⟨1547642, by rfl⟩ : syracuseStep 2063523 = 3095285) B3095285
theorem B11155637 : Blo 2063435 11155637 := bbase (se 5 (by rfl) ⟨522920, by rfl⟩ : syracuseStep 11155637 = 1045841) (by norm_num)
theorem B7437091 : Blo 2063435 7437091 := bstep (se 1 (by rfl) ⟨5577818, by rfl⟩ : syracuseStep 7437091 = 11155637) B11155637
theorem B9916121 : Blo 2063435 9916121 := bstep (se 2 (by rfl) ⟨3718545, by rfl⟩ : syracuseStep 9916121 = 7437091) B7437091
theorem B6610747 : Blo 2063435 6610747 := bstep (se 1 (by rfl) ⟨4958060, by rfl⟩ : syracuseStep 6610747 = 9916121) B9916121
theorem B8814329 : Blo 2063435 8814329 := bstep (se 2 (by rfl) ⟨3305373, by rfl⟩ : syracuseStep 8814329 = 6610747) B6610747
theorem B5876219 : Blo 2063435 5876219 := bstep (se 1 (by rfl) ⟨4407164, by rfl⟩ : syracuseStep 5876219 = 8814329) B8814329
theorem B3917479 : Blo 2063435 3917479 := bstep (se 1 (by rfl) ⟨2938109, by rfl⟩ : syracuseStep 3917479 = 5876219) B5876219
theorem B5223305 : Blo 2063435 5223305 := bstep (se 2 (by rfl) ⟨1958739, by rfl⟩ : syracuseStep 5223305 = 3917479) B3917479
theorem B3482203 : Blo 2063435 3482203 := bstep (se 1 (by rfl) ⟨2611652, by rfl⟩ : syracuseStep 3482203 = 5223305) B5223305
theorem B4642937 : Blo 2063435 4642937 := bstep (se 2 (by rfl) ⟨1741101, by rfl⟩ : syracuseStep 4642937 = 3482203) B3482203
theorem B3095291 : Blo 2063435 3095291 := bstep (se 1 (by rfl) ⟨2321468, by rfl⟩ : syracuseStep 3095291 = 4642937) B4642937
theorem B2063527 : Blo 2063435 2063527 := bstep (se 1 (by rfl) ⟨1547645, by rfl⟩ : syracuseStep 2063527 = 3095291) B3095291
theorem B2321473 : Blo 2063435 2321473 := bbase (se 2 (by rfl) ⟨870552, by rfl⟩ : syracuseStep 2321473 = 1741105) (by norm_num)
theorem B3095297 : Blo 2063435 3095297 := bstep (se 2 (by rfl) ⟨1160736, by rfl⟩ : syracuseStep 3095297 = 2321473) B2321473
theorem B2063531 : Blo 2063435 2063531 := bstep (se 1 (by rfl) ⟨1547648, by rfl⟩ : syracuseStep 2063531 = 3095297) B3095297
theorem B5223325 : Blo 2063435 5223325 := bbase (se 3 (by rfl) ⟨979373, by rfl⟩ : syracuseStep 5223325 = 1958747) (by norm_num)
theorem B6964433 : Blo 2063435 6964433 := bstep (se 2 (by rfl) ⟨2611662, by rfl⟩ : syracuseStep 6964433 = 5223325) B5223325
theorem B4642955 : Blo 2063435 4642955 := bstep (se 1 (by rfl) ⟨3482216, by rfl⟩ : syracuseStep 4642955 = 6964433) B6964433
theorem B3095303 : Blo 2063435 3095303 := bstep (se 1 (by rfl) ⟨2321477, by rfl⟩ : syracuseStep 3095303 = 4642955) B4642955
theorem B2063535 : Blo 2063435 2063535 := bstep (se 1 (by rfl) ⟨1547651, by rfl⟩ : syracuseStep 2063535 = 3095303) B3095303
theorem B3095309 : Blo 2063435 3095309 := bbase (se 3 (by rfl) ⟨580370, by rfl⟩ : syracuseStep 3095309 = 1160741) (by norm_num)
theorem B2063539 : Blo 2063435 2063539 := bstep (se 1 (by rfl) ⟨1547654, by rfl⟩ : syracuseStep 2063539 = 3095309) B3095309
theorem B4642973 : Blo 2063435 4642973 := bbase (se 3 (by rfl) ⟨870557, by rfl⟩ : syracuseStep 4642973 = 1741115) (by norm_num)
theorem B3095315 : Blo 2063435 3095315 := bstep (se 1 (by rfl) ⟨2321486, by rfl⟩ : syracuseStep 3095315 = 4642973) B4642973
theorem B2063543 : Blo 2063435 2063543 := bstep (se 1 (by rfl) ⟨1547657, by rfl⟩ : syracuseStep 2063543 = 3095315) B3095315
theorem B3482237 : Blo 2063435 3482237 := bbase (se 3 (by rfl) ⟨652919, by rfl⟩ : syracuseStep 3482237 = 1305839) (by norm_num)
theorem B2321491 : Blo 2063435 2321491 := bstep (se 1 (by rfl) ⟨1741118, by rfl⟩ : syracuseStep 2321491 = 3482237) B3482237
theorem B3095321 : Blo 2063435 3095321 := bstep (se 2 (by rfl) ⟨1160745, by rfl⟩ : syracuseStep 3095321 = 2321491) B2321491
theorem B2063547 : Blo 2063435 2063547 := bstep (se 1 (by rfl) ⟨1547660, by rfl⟩ : syracuseStep 2063547 = 3095321) B3095321
theorem B11155765 : Blo 2063435 11155765 := bbase (se 5 (by rfl) ⟨522926, by rfl⟩ : syracuseStep 11155765 = 1045853) (by norm_num)
theorem B14874353 : Blo 2063435 14874353 := bstep (se 2 (by rfl) ⟨5577882, by rfl⟩ : syracuseStep 14874353 = 11155765) B11155765
theorem B9916235 : Blo 2063435 9916235 := bstep (se 1 (by rfl) ⟨7437176, by rfl⟩ : syracuseStep 9916235 = 14874353) B14874353
theorem B6610823 : Blo 2063435 6610823 := bstep (se 1 (by rfl) ⟨4958117, by rfl⟩ : syracuseStep 6610823 = 9916235) B9916235
theorem B4407215 : Blo 2063435 4407215 := bstep (se 1 (by rfl) ⟨3305411, by rfl⟩ : syracuseStep 4407215 = 6610823) B6610823
theorem B11752573 : Blo 2063435 11752573 := bstep (se 3 (by rfl) ⟨2203607, by rfl⟩ : syracuseStep 11752573 = 4407215) B4407215
theorem B15670097 : Blo 2063435 15670097 := bstep (se 2 (by rfl) ⟨5876286, by rfl⟩ : syracuseStep 15670097 = 11752573) B11752573
theorem B10446731 : Blo 2063435 10446731 := bstep (se 1 (by rfl) ⟨7835048, by rfl⟩ : syracuseStep 10446731 = 15670097) B15670097
theorem B6964487 : Blo 2063435 6964487 := bstep (se 1 (by rfl) ⟨5223365, by rfl⟩ : syracuseStep 6964487 = 10446731) B10446731
theorem B4642991 : Blo 2063435 4642991 := bstep (se 1 (by rfl) ⟨3482243, by rfl⟩ : syracuseStep 4642991 = 6964487) B6964487
theorem B3095327 : Blo 2063435 3095327 := bstep (se 1 (by rfl) ⟨2321495, by rfl⟩ : syracuseStep 3095327 = 4642991) B4642991
theorem B2063551 : Blo 2063435 2063551 := bstep (se 1 (by rfl) ⟨1547663, by rfl⟩ : syracuseStep 2063551 = 3095327) B3095327
theorem B3095333 : Blo 2063435 3095333 := bbase (se 4 (by rfl) ⟨290187, by rfl⟩ : syracuseStep 3095333 = 580375) (by norm_num)
theorem B2063555 : Blo 2063435 2063555 := bstep (se 1 (by rfl) ⟨1547666, by rfl⟩ : syracuseStep 2063555 = 3095333) B3095333
theorem B2611693 : Blo 2063435 2611693 := bbase (se 3 (by rfl) ⟨489692, by rfl⟩ : syracuseStep 2611693 = 979385) (by norm_num)
theorem B3482257 : Blo 2063435 3482257 := bstep (se 2 (by rfl) ⟨1305846, by rfl⟩ : syracuseStep 3482257 = 2611693) B2611693
theorem B4643009 : Blo 2063435 4643009 := bstep (se 2 (by rfl) ⟨1741128, by rfl⟩ : syracuseStep 4643009 = 3482257) B3482257
theorem B3095339 : Blo 2063435 3095339 := bstep (se 1 (by rfl) ⟨2321504, by rfl⟩ : syracuseStep 3095339 = 4643009) B4643009
theorem B2063559 : Blo 2063435 2063559 := bstep (se 1 (by rfl) ⟨1547669, by rfl⟩ : syracuseStep 2063559 = 3095339) B3095339
theorem B2321509 : Blo 2063435 2321509 := bbase (se 4 (by rfl) ⟨217641, by rfl⟩ : syracuseStep 2321509 = 435283) (by norm_num)
theorem B3095345 : Blo 2063435 3095345 := bstep (se 2 (by rfl) ⟨1160754, by rfl⟩ : syracuseStep 3095345 = 2321509) B2321509
theorem B2063563 : Blo 2063435 2063563 := bstep (se 1 (by rfl) ⟨1547672, by rfl⟩ : syracuseStep 2063563 = 3095345) B3095345
theorem B2203625 : Blo 2063435 2203625 := bbase (se 2 (by rfl) ⟨826359, by rfl⟩ : syracuseStep 2203625 = 1652719) (by norm_num)
theorem B5876333 : Blo 2063435 5876333 := bstep (se 3 (by rfl) ⟨1101812, by rfl⟩ : syracuseStep 5876333 = 2203625) B2203625
theorem B3917555 : Blo 2063435 3917555 := bstep (se 1 (by rfl) ⟨2938166, by rfl⟩ : syracuseStep 3917555 = 5876333) B5876333
theorem B2611703 : Blo 2063435 2611703 := bstep (se 1 (by rfl) ⟨1958777, by rfl⟩ : syracuseStep 2611703 = 3917555) B3917555
theorem B6964541 : Blo 2063435 6964541 := bstep (se 3 (by rfl) ⟨1305851, by rfl⟩ : syracuseStep 6964541 = 2611703) B2611703
theorem B4643027 : Blo 2063435 4643027 := bstep (se 1 (by rfl) ⟨3482270, by rfl⟩ : syracuseStep 4643027 = 6964541) B6964541
theorem B3095351 : Blo 2063435 3095351 := bstep (se 1 (by rfl) ⟨2321513, by rfl⟩ : syracuseStep 3095351 = 4643027) B4643027
theorem B2063567 : Blo 2063435 2063567 := bstep (se 1 (by rfl) ⟨1547675, by rfl⟩ : syracuseStep 2063567 = 3095351) B3095351
theorem B3095357 : Blo 2063435 3095357 := bbase (se 3 (by rfl) ⟨580379, by rfl⟩ : syracuseStep 3095357 = 1160759) (by norm_num)
theorem B2063571 : Blo 2063435 2063571 := bstep (se 1 (by rfl) ⟨1547678, by rfl⟩ : syracuseStep 2063571 = 3095357) B3095357
theorem B4643045 : Blo 2063435 4643045 := bbase (se 4 (by rfl) ⟨435285, by rfl⟩ : syracuseStep 4643045 = 870571) (by norm_num)
theorem B3095363 : Blo 2063435 3095363 := bstep (se 1 (by rfl) ⟨2321522, by rfl⟩ : syracuseStep 3095363 = 4643045) B4643045
theorem B2063575 : Blo 2063435 2063575 := bstep (se 1 (by rfl) ⟨1547681, by rfl⟩ : syracuseStep 2063575 = 3095363) B3095363
theorem B5223437 : Blo 2063435 5223437 := bbase (se 3 (by rfl) ⟨979394, by rfl⟩ : syracuseStep 5223437 = 1958789) (by norm_num)
theorem B3482291 : Blo 2063435 3482291 := bstep (se 1 (by rfl) ⟨2611718, by rfl⟩ : syracuseStep 3482291 = 5223437) B5223437
theorem B2321527 : Blo 2063435 2321527 := bstep (se 1 (by rfl) ⟨1741145, by rfl⟩ : syracuseStep 2321527 = 3482291) B3482291
theorem B3095369 : Blo 2063435 3095369 := bstep (se 2 (by rfl) ⟨1160763, by rfl⟩ : syracuseStep 3095369 = 2321527) B2321527
theorem B2063579 : Blo 2063435 2063579 := bstep (se 1 (by rfl) ⟨1547684, by rfl⟩ : syracuseStep 2063579 = 3095369) B3095369
theorem B2938189 : Blo 2063435 2938189 := bbase (se 3 (by rfl) ⟨550910, by rfl⟩ : syracuseStep 2938189 = 1101821) (by norm_num)
theorem B3917585 : Blo 2063435 3917585 := bstep (se 2 (by rfl) ⟨1469094, by rfl⟩ : syracuseStep 3917585 = 2938189) B2938189
theorem B10446893 : Blo 2063435 10446893 := bstep (se 3 (by rfl) ⟨1958792, by rfl⟩ : syracuseStep 10446893 = 3917585) B3917585
theorem B6964595 : Blo 2063435 6964595 := bstep (se 1 (by rfl) ⟨5223446, by rfl⟩ : syracuseStep 6964595 = 10446893) B10446893
theorem B4643063 : Blo 2063435 4643063 := bstep (se 1 (by rfl) ⟨3482297, by rfl⟩ : syracuseStep 4643063 = 6964595) B6964595
theorem B3095375 : Blo 2063435 3095375 := bstep (se 1 (by rfl) ⟨2321531, by rfl⟩ : syracuseStep 3095375 = 4643063) B4643063
theorem B2063583 : Blo 2063435 2063583 := bstep (se 1 (by rfl) ⟨1547687, by rfl⟩ : syracuseStep 2063583 = 3095375) B3095375
theorem B3095381 : Blo 2063435 3095381 := bbase (se 9 (by rfl) ⟨9068, by rfl⟩ : syracuseStep 3095381 = 18137) (by norm_num)
theorem B2063587 : Blo 2063435 2063587 := bstep (se 1 (by rfl) ⟨1547690, by rfl⟩ : syracuseStep 2063587 = 3095381) B3095381
theorem B4407301 : Blo 2063435 4407301 := bbase (se 4 (by rfl) ⟨413184, by rfl⟩ : syracuseStep 4407301 = 826369) (by norm_num)
theorem B5876401 : Blo 2063435 5876401 := bstep (se 2 (by rfl) ⟨2203650, by rfl⟩ : syracuseStep 5876401 = 4407301) B4407301
theorem B7835201 : Blo 2063435 7835201 := bstep (se 2 (by rfl) ⟨2938200, by rfl⟩ : syracuseStep 7835201 = 5876401) B5876401
theorem B5223467 : Blo 2063435 5223467 := bstep (se 1 (by rfl) ⟨3917600, by rfl⟩ : syracuseStep 5223467 = 7835201) B7835201
theorem B3482311 : Blo 2063435 3482311 := bstep (se 1 (by rfl) ⟨2611733, by rfl⟩ : syracuseStep 3482311 = 5223467) B5223467
theorem B4643081 : Blo 2063435 4643081 := bstep (se 2 (by rfl) ⟨1741155, by rfl⟩ : syracuseStep 4643081 = 3482311) B3482311
theorem B3095387 : Blo 2063435 3095387 := bstep (se 1 (by rfl) ⟨2321540, by rfl⟩ : syracuseStep 3095387 = 4643081) B4643081
theorem B2063591 : Blo 2063435 2063591 := bstep (se 1 (by rfl) ⟨1547693, by rfl⟩ : syracuseStep 2063591 = 3095387) B3095387
theorem B2321545 : Blo 2063435 2321545 := bbase (se 2 (by rfl) ⟨870579, by rfl⟩ : syracuseStep 2321545 = 1741159) (by norm_num)
theorem B3095393 : Blo 2063435 3095393 := bstep (se 2 (by rfl) ⟨1160772, by rfl⟩ : syracuseStep 3095393 = 2321545) B2321545
theorem B2063595 : Blo 2063435 2063595 := bstep (se 1 (by rfl) ⟨1547696, by rfl⟩ : syracuseStep 2063595 = 3095393) B3095393
theorem B7437349 : Blo 2063435 7437349 := bbase (se 4 (by rfl) ⟨697251, by rfl⟩ : syracuseStep 7437349 = 1394503) (by norm_num)
theorem B39665861 : Blo 2063435 39665861 := bstep (se 4 (by rfl) ⟨3718674, by rfl⟩ : syracuseStep 39665861 = 7437349) B7437349
theorem B26443907 : Blo 2063435 26443907 := bstep (se 1 (by rfl) ⟨19832930, by rfl⟩ : syracuseStep 26443907 = 39665861) B39665861
theorem B17629271 : Blo 2063435 17629271 := bstep (se 1 (by rfl) ⟨13221953, by rfl⟩ : syracuseStep 17629271 = 26443907) B26443907
theorem B11752847 : Blo 2063435 11752847 := bstep (se 1 (by rfl) ⟨8814635, by rfl⟩ : syracuseStep 11752847 = 17629271) B17629271
theorem B7835231 : Blo 2063435 7835231 := bstep (se 1 (by rfl) ⟨5876423, by rfl⟩ : syracuseStep 7835231 = 11752847) B11752847
theorem B5223487 : Blo 2063435 5223487 := bstep (se 1 (by rfl) ⟨3917615, by rfl⟩ : syracuseStep 5223487 = 7835231) B7835231
theorem B6964649 : Blo 2063435 6964649 := bstep (se 2 (by rfl) ⟨2611743, by rfl⟩ : syracuseStep 6964649 = 5223487) B5223487
theorem B4643099 : Blo 2063435 4643099 := bstep (se 1 (by rfl) ⟨3482324, by rfl⟩ : syracuseStep 4643099 = 6964649) B6964649
theorem B3095399 : Blo 2063435 3095399 := bstep (se 1 (by rfl) ⟨2321549, by rfl⟩ : syracuseStep 3095399 = 4643099) B4643099
theorem B2063599 : Blo 2063435 2063599 := bstep (se 1 (by rfl) ⟨1547699, by rfl⟩ : syracuseStep 2063599 = 3095399) B3095399
theorem B3095405 : Blo 2063435 3095405 := bbase (se 3 (by rfl) ⟨580388, by rfl⟩ : syracuseStep 3095405 = 1160777) (by norm_num)
theorem B2063603 : Blo 2063435 2063603 := bstep (se 1 (by rfl) ⟨1547702, by rfl⟩ : syracuseStep 2063603 = 3095405) B3095405
theorem B4643117 : Blo 2063435 4643117 := bbase (se 3 (by rfl) ⟨870584, by rfl⟩ : syracuseStep 4643117 = 1741169) (by norm_num)
theorem B3095411 : Blo 2063435 3095411 := bstep (se 1 (by rfl) ⟨2321558, by rfl⟩ : syracuseStep 3095411 = 4643117) B4643117
theorem B2063607 : Blo 2063435 2063607 := bstep (se 1 (by rfl) ⟨1547705, by rfl⟩ : syracuseStep 2063607 = 3095411) B3095411
theorem B17869909 : Blo 2063435 17869909 := bbase (se 8 (by rfl) ⟨104706, by rfl⟩ : syracuseStep 17869909 = 209413) (by norm_num)
theorem B23826545 : Blo 2063435 23826545 := bstep (se 2 (by rfl) ⟨8934954, by rfl⟩ : syracuseStep 23826545 = 17869909) B17869909
theorem B15884363 : Blo 2063435 15884363 := bstep (se 1 (by rfl) ⟨11913272, by rfl⟩ : syracuseStep 15884363 = 23826545) B23826545
theorem B10589575 : Blo 2063435 10589575 := bstep (se 1 (by rfl) ⟨7942181, by rfl⟩ : syracuseStep 10589575 = 15884363) B15884363
theorem B14119433 : Blo 2063435 14119433 := bstep (se 2 (by rfl) ⟨5294787, by rfl⟩ : syracuseStep 14119433 = 10589575) B10589575
theorem B9412955 : Blo 2063435 9412955 := bstep (se 1 (by rfl) ⟨7059716, by rfl⟩ : syracuseStep 9412955 = 14119433) B14119433
theorem B6275303 : Blo 2063435 6275303 := bstep (se 1 (by rfl) ⟨4706477, by rfl⟩ : syracuseStep 6275303 = 9412955) B9412955
theorem B4183535 : Blo 2063435 4183535 := bstep (se 1 (by rfl) ⟨3137651, by rfl⟩ : syracuseStep 4183535 = 6275303) B6275303
theorem B11156093 : Blo 2063435 11156093 := bstep (se 3 (by rfl) ⟨2091767, by rfl⟩ : syracuseStep 11156093 = 4183535) B4183535
theorem B7437395 : Blo 2063435 7437395 := bstep (se 1 (by rfl) ⟨5578046, by rfl⟩ : syracuseStep 7437395 = 11156093) B11156093
theorem B4958263 : Blo 2063435 4958263 := bstep (se 1 (by rfl) ⟨3718697, by rfl⟩ : syracuseStep 4958263 = 7437395) B7437395
theorem B6611017 : Blo 2063435 6611017 := bstep (se 2 (by rfl) ⟨2479131, by rfl⟩ : syracuseStep 6611017 = 4958263) B4958263
theorem B8814689 : Blo 2063435 8814689 := bstep (se 2 (by rfl) ⟨3305508, by rfl⟩ : syracuseStep 8814689 = 6611017) B6611017
theorem B5876459 : Blo 2063435 5876459 := bstep (se 1 (by rfl) ⟨4407344, by rfl⟩ : syracuseStep 5876459 = 8814689) B8814689
theorem B3917639 : Blo 2063435 3917639 := bstep (se 1 (by rfl) ⟨2938229, by rfl⟩ : syracuseStep 3917639 = 5876459) B5876459
theorem B2611759 : Blo 2063435 2611759 := bstep (se 1 (by rfl) ⟨1958819, by rfl⟩ : syracuseStep 2611759 = 3917639) B3917639
theorem B3482345 : Blo 2063435 3482345 := bstep (se 2 (by rfl) ⟨1305879, by rfl⟩ : syracuseStep 3482345 = 2611759) B2611759
theorem B2321563 : Blo 2063435 2321563 := bstep (se 1 (by rfl) ⟨1741172, by rfl⟩ : syracuseStep 2321563 = 3482345) B3482345
theorem B3095417 : Blo 2063435 3095417 := bstep (se 2 (by rfl) ⟨1160781, by rfl⟩ : syracuseStep 3095417 = 2321563) B2321563
theorem B2063611 : Blo 2063435 2063611 := bstep (se 1 (by rfl) ⟨1547708, by rfl⟩ : syracuseStep 2063611 = 3095417) B3095417
theorem B10210277 : Blo 2063435 10210277 := bbase (se 4 (by rfl) ⟨957213, by rfl⟩ : syracuseStep 10210277 = 1914427) (by norm_num)
theorem B6806851 : Blo 2063435 6806851 := bstep (se 1 (by rfl) ⟨5105138, by rfl⟩ : syracuseStep 6806851 = 10210277) B10210277
theorem B145212821 : Blo 2063435 145212821 := bstep (se 6 (by rfl) ⟨3403425, by rfl⟩ : syracuseStep 145212821 = 6806851) B6806851
theorem B96808547 : Blo 2063435 96808547 := bstep (se 1 (by rfl) ⟨72606410, by rfl⟩ : syracuseStep 96808547 = 145212821) B145212821
theorem B64539031 : Blo 2063435 64539031 := bstep (se 1 (by rfl) ⟨48404273, by rfl⟩ : syracuseStep 64539031 = 96808547) B96808547
theorem B86052041 : Blo 2063435 86052041 := bstep (se 2 (by rfl) ⟨32269515, by rfl⟩ : syracuseStep 86052041 = 64539031) B64539031
theorem B57368027 : Blo 2063435 57368027 := bstep (se 1 (by rfl) ⟨43026020, by rfl⟩ : syracuseStep 57368027 = 86052041) B86052041
theorem B38245351 : Blo 2063435 38245351 := bstep (se 1 (by rfl) ⟨28684013, by rfl⟩ : syracuseStep 38245351 = 57368027) B57368027
theorem B50993801 : Blo 2063435 50993801 := bstep (se 2 (by rfl) ⟨19122675, by rfl⟩ : syracuseStep 50993801 = 38245351) B38245351
theorem B33995867 : Blo 2063435 33995867 := bstep (se 1 (by rfl) ⟨25496900, by rfl⟩ : syracuseStep 33995867 = 50993801) B50993801
theorem B90655645 : Blo 2063435 90655645 := bstep (se 3 (by rfl) ⟨16997933, by rfl⟩ : syracuseStep 90655645 = 33995867) B33995867
theorem B120874193 : Blo 2063435 120874193 := bstep (se 2 (by rfl) ⟨45327822, by rfl⟩ : syracuseStep 120874193 = 90655645) B90655645
theorem B80582795 : Blo 2063435 80582795 := bstep (se 1 (by rfl) ⟨60437096, by rfl⟩ : syracuseStep 80582795 = 120874193) B120874193
theorem B53721863 : Blo 2063435 53721863 := bstep (se 1 (by rfl) ⟨40291397, by rfl⟩ : syracuseStep 53721863 = 80582795) B80582795
theorem B35814575 : Blo 2063435 35814575 := bstep (se 1 (by rfl) ⟨26860931, by rfl⟩ : syracuseStep 35814575 = 53721863) B53721863
theorem B23876383 : Blo 2063435 23876383 := bstep (se 1 (by rfl) ⟨17907287, by rfl⟩ : syracuseStep 23876383 = 35814575) B35814575
theorem B31835177 : Blo 2063435 31835177 := bstep (se 2 (by rfl) ⟨11938191, by rfl⟩ : syracuseStep 31835177 = 23876383) B23876383
theorem B21223451 : Blo 2063435 21223451 := bstep (se 1 (by rfl) ⟨15917588, by rfl⟩ : syracuseStep 21223451 = 31835177) B31835177
theorem B14148967 : Blo 2063435 14148967 := bstep (se 1 (by rfl) ⟨10611725, by rfl⟩ : syracuseStep 14148967 = 21223451) B21223451
theorem B18865289 : Blo 2063435 18865289 := bstep (se 2 (by rfl) ⟨7074483, by rfl⟩ : syracuseStep 18865289 = 14148967) B14148967
theorem B50307437 : Blo 2063435 50307437 := bstep (se 3 (by rfl) ⟨9432644, by rfl⟩ : syracuseStep 50307437 = 18865289) B18865289
theorem B134153165 : Blo 2063435 134153165 := bstep (se 3 (by rfl) ⟨25153718, by rfl⟩ : syracuseStep 134153165 = 50307437) B50307437
theorem B89435443 : Blo 2063435 89435443 := bstep (se 1 (by rfl) ⟨67076582, by rfl⟩ : syracuseStep 89435443 = 134153165) B134153165
theorem B119247257 : Blo 2063435 119247257 := bstep (se 2 (by rfl) ⟨44717721, by rfl⟩ : syracuseStep 119247257 = 89435443) B89435443
theorem B79498171 : Blo 2063435 79498171 := bstep (se 1 (by rfl) ⟨59623628, by rfl⟩ : syracuseStep 79498171 = 119247257) B119247257
theorem B105997561 : Blo 2063435 105997561 := bstep (se 2 (by rfl) ⟨39749085, by rfl⟩ : syracuseStep 105997561 = 79498171) B79498171
theorem B565320325 : Blo 2063435 565320325 := bstep (se 4 (by rfl) ⟨52998780, by rfl⟩ : syracuseStep 565320325 = 105997561) B105997561
theorem B753760433 : Blo 2063435 753760433 := bstep (se 2 (by rfl) ⟨282660162, by rfl⟩ : syracuseStep 753760433 = 565320325) B565320325
theorem B502506955 : Blo 2063435 502506955 := bstep (se 1 (by rfl) ⟨376880216, by rfl⟩ : syracuseStep 502506955 = 753760433) B753760433
theorem B2680037093 : Blo 2063435 2680037093 := bstep (se 4 (by rfl) ⟨251253477, by rfl⟩ : syracuseStep 2680037093 = 502506955) B502506955
theorem B1786691395 : Blo 2063435 1786691395 := bstep (se 1 (by rfl) ⟨1340018546, by rfl⟩ : syracuseStep 1786691395 = 2680037093) B2680037093
theorem B2382255193 : Blo 2063435 2382255193 := bstep (se 2 (by rfl) ⟨893345697, by rfl⟩ : syracuseStep 2382255193 = 1786691395) B1786691395
theorem B3176340257 : Blo 2063435 3176340257 := bstep (se 2 (by rfl) ⟨1191127596, by rfl⟩ : syracuseStep 3176340257 = 2382255193) B2382255193
theorem B2117560171 : Blo 2063435 2117560171 := bstep (se 1 (by rfl) ⟨1588170128, by rfl⟩ : syracuseStep 2117560171 = 3176340257) B3176340257
theorem B2823413561 : Blo 2063435 2823413561 := bstep (se 2 (by rfl) ⟨1058780085, by rfl⟩ : syracuseStep 2823413561 = 2117560171) B2117560171
theorem B1882275707 : Blo 2063435 1882275707 := bstep (se 1 (by rfl) ⟨1411706780, by rfl⟩ : syracuseStep 1882275707 = 2823413561) B2823413561
theorem B1254850471 : Blo 2063435 1254850471 := bstep (se 1 (by rfl) ⟨941137853, by rfl⟩ : syracuseStep 1254850471 = 1882275707) B1882275707
theorem B6692535845 : Blo 2063435 6692535845 := bstep (se 4 (by rfl) ⟨627425235, by rfl⟩ : syracuseStep 6692535845 = 1254850471) B1254850471
theorem B4461690563 : Blo 2063435 4461690563 := bstep (se 1 (by rfl) ⟨3346267922, by rfl⟩ : syracuseStep 4461690563 = 6692535845) B6692535845
theorem B2974460375 : Blo 2063435 2974460375 := bstep (se 1 (by rfl) ⟨2230845281, by rfl⟩ : syracuseStep 2974460375 = 4461690563) B4461690563
theorem B1982973583 : Blo 2063435 1982973583 := bstep (se 1 (by rfl) ⟨1487230187, by rfl⟩ : syracuseStep 1982973583 = 2974460375) B2974460375
theorem B2643964777 : Blo 2063435 2643964777 := bstep (se 2 (by rfl) ⟨991486791, by rfl⟩ : syracuseStep 2643964777 = 1982973583) B1982973583
theorem B3525286369 : Blo 2063435 3525286369 := bstep (se 2 (by rfl) ⟨1321982388, by rfl⟩ : syracuseStep 3525286369 = 2643964777) B2643964777
theorem B4700381825 : Blo 2063435 4700381825 := bstep (se 2 (by rfl) ⟨1762643184, by rfl⟩ : syracuseStep 4700381825 = 3525286369) B3525286369
theorem B3133587883 : Blo 2063435 3133587883 := bstep (se 1 (by rfl) ⟨2350190912, by rfl⟩ : syracuseStep 3133587883 = 4700381825) B4700381825
theorem B4178117177 : Blo 2063435 4178117177 := bstep (se 2 (by rfl) ⟨1566793941, by rfl⟩ : syracuseStep 4178117177 = 3133587883) B3133587883
theorem B2785411451 : Blo 2063435 2785411451 := bstep (se 1 (by rfl) ⟨2089058588, by rfl⟩ : syracuseStep 2785411451 = 4178117177) B4178117177
theorem B1856940967 : Blo 2063435 1856940967 := bstep (se 1 (by rfl) ⟨1392705725, by rfl⟩ : syracuseStep 1856940967 = 2785411451) B2785411451
theorem B2475921289 : Blo 2063435 2475921289 := bstep (se 2 (by rfl) ⟨928470483, by rfl⟩ : syracuseStep 2475921289 = 1856940967) B1856940967
theorem B3301228385 : Blo 2063435 3301228385 := bstep (se 2 (by rfl) ⟨1237960644, by rfl⟩ : syracuseStep 3301228385 = 2475921289) B2475921289
theorem B2200818923 : Blo 2063435 2200818923 := bstep (se 1 (by rfl) ⟨1650614192, by rfl⟩ : syracuseStep 2200818923 = 3301228385) B3301228385
theorem B1467212615 : Blo 2063435 1467212615 := bstep (se 1 (by rfl) ⟨1100409461, by rfl⟩ : syracuseStep 1467212615 = 2200818923) B2200818923
theorem B978141743 : Blo 2063435 978141743 := bstep (se 1 (by rfl) ⟨733606307, by rfl⟩ : syracuseStep 978141743 = 1467212615) B1467212615
theorem B652094495 : Blo 2063435 652094495 := bstep (se 1 (by rfl) ⟨489070871, by rfl⟩ : syracuseStep 652094495 = 978141743) B978141743
theorem B434729663 : Blo 2063435 434729663 := bstep (se 1 (by rfl) ⟨326047247, by rfl⟩ : syracuseStep 434729663 = 652094495) B652094495
theorem B289819775 : Blo 2063435 289819775 := bstep (se 1 (by rfl) ⟨217364831, by rfl⟩ : syracuseStep 289819775 = 434729663) B434729663
theorem B193213183 : Blo 2063435 193213183 := bstep (se 1 (by rfl) ⟨144909887, by rfl⟩ : syracuseStep 193213183 = 289819775) B289819775
theorem B257617577 : Blo 2063435 257617577 := bstep (se 2 (by rfl) ⟨96606591, by rfl⟩ : syracuseStep 257617577 = 193213183) B193213183
theorem B171745051 : Blo 2063435 171745051 := bstep (se 1 (by rfl) ⟨128808788, by rfl⟩ : syracuseStep 171745051 = 257617577) B257617577
theorem B228993401 : Blo 2063435 228993401 := bstep (se 2 (by rfl) ⟨85872525, by rfl⟩ : syracuseStep 228993401 = 171745051) B171745051
theorem B152662267 : Blo 2063435 152662267 := bstep (se 1 (by rfl) ⟨114496700, by rfl⟩ : syracuseStep 152662267 = 228993401) B228993401
theorem B203549689 : Blo 2063435 203549689 := bstep (se 2 (by rfl) ⟨76331133, by rfl⟩ : syracuseStep 203549689 = 152662267) B152662267
theorem B271399585 : Blo 2063435 271399585 := bstep (se 2 (by rfl) ⟨101774844, by rfl⟩ : syracuseStep 271399585 = 203549689) B203549689
theorem B361866113 : Blo 2063435 361866113 := bstep (se 2 (by rfl) ⟨135699792, by rfl⟩ : syracuseStep 361866113 = 271399585) B271399585
theorem B241244075 : Blo 2063435 241244075 := bstep (se 1 (by rfl) ⟨180933056, by rfl⟩ : syracuseStep 241244075 = 361866113) B361866113
theorem B160829383 : Blo 2063435 160829383 := bstep (se 1 (by rfl) ⟨120622037, by rfl⟩ : syracuseStep 160829383 = 241244075) B241244075
theorem B214439177 : Blo 2063435 214439177 := bstep (se 2 (by rfl) ⟨80414691, by rfl⟩ : syracuseStep 214439177 = 160829383) B160829383
theorem B142959451 : Blo 2063435 142959451 := bstep (se 1 (by rfl) ⟨107219588, by rfl⟩ : syracuseStep 142959451 = 214439177) B214439177
theorem B190612601 : Blo 2063435 190612601 := bstep (se 2 (by rfl) ⟨71479725, by rfl⟩ : syracuseStep 190612601 = 142959451) B142959451
theorem B127075067 : Blo 2063435 127075067 := bstep (se 1 (by rfl) ⟨95306300, by rfl⟩ : syracuseStep 127075067 = 190612601) B190612601
theorem B84716711 : Blo 2063435 84716711 := bstep (se 1 (by rfl) ⟨63537533, by rfl⟩ : syracuseStep 84716711 = 127075067) B127075067
theorem B56477807 : Blo 2063435 56477807 := bstep (se 1 (by rfl) ⟨42358355, by rfl⟩ : syracuseStep 56477807 = 84716711) B84716711
theorem B37651871 : Blo 2063435 37651871 := bstep (se 1 (by rfl) ⟨28238903, by rfl⟩ : syracuseStep 37651871 = 56477807) B56477807
theorem B25101247 : Blo 2063435 25101247 := bstep (se 1 (by rfl) ⟨18825935, by rfl⟩ : syracuseStep 25101247 = 37651871) B37651871
theorem B33468329 : Blo 2063435 33468329 := bstep (se 2 (by rfl) ⟨12550623, by rfl⟩ : syracuseStep 33468329 = 25101247) B25101247
theorem B22312219 : Blo 2063435 22312219 := bstep (se 1 (by rfl) ⟨16734164, by rfl⟩ : syracuseStep 22312219 = 33468329) B33468329
theorem B29749625 : Blo 2063435 29749625 := bstep (se 2 (by rfl) ⟨11156109, by rfl⟩ : syracuseStep 29749625 = 22312219) B22312219
theorem B19833083 : Blo 2063435 19833083 := bstep (se 1 (by rfl) ⟨14874812, by rfl⟩ : syracuseStep 19833083 = 29749625) B29749625
theorem B13222055 : Blo 2063435 13222055 := bstep (se 1 (by rfl) ⟨9916541, by rfl⟩ : syracuseStep 13222055 = 19833083) B19833083
theorem B35258813 : Blo 2063435 35258813 := bstep (se 3 (by rfl) ⟨6611027, by rfl⟩ : syracuseStep 35258813 = 13222055) B13222055
theorem B23505875 : Blo 2063435 23505875 := bstep (se 1 (by rfl) ⟨17629406, by rfl⟩ : syracuseStep 23505875 = 35258813) B35258813
theorem B15670583 : Blo 2063435 15670583 := bstep (se 1 (by rfl) ⟨11752937, by rfl⟩ : syracuseStep 15670583 = 23505875) B23505875
theorem B10447055 : Blo 2063435 10447055 := bstep (se 1 (by rfl) ⟨7835291, by rfl⟩ : syracuseStep 10447055 = 15670583) B15670583
theorem B6964703 : Blo 2063435 6964703 := bstep (se 1 (by rfl) ⟨5223527, by rfl⟩ : syracuseStep 6964703 = 10447055) B10447055
theorem B4643135 : Blo 2063435 4643135 := bstep (se 1 (by rfl) ⟨3482351, by rfl⟩ : syracuseStep 4643135 = 6964703) B6964703
theorem B3095423 : Blo 2063435 3095423 := bstep (se 1 (by rfl) ⟨2321567, by rfl⟩ : syracuseStep 3095423 = 4643135) B4643135
theorem B2063615 : Blo 2063435 2063615 := bstep (se 1 (by rfl) ⟨1547711, by rfl⟩ : syracuseStep 2063615 = 3095423) B3095423
theorem B3095429 : Blo 2063435 3095429 := bbase (se 4 (by rfl) ⟨290196, by rfl⟩ : syracuseStep 3095429 = 580393) (by norm_num)
theorem B2063619 : Blo 2063435 2063619 := bstep (se 1 (by rfl) ⟨1547714, by rfl⟩ : syracuseStep 2063619 = 3095429) B3095429
theorem B3482365 : Blo 2063435 3482365 := bbase (se 3 (by rfl) ⟨652943, by rfl⟩ : syracuseStep 3482365 = 1305887) (by norm_num)
theorem B4643153 : Blo 2063435 4643153 := bstep (se 2 (by rfl) ⟨1741182, by rfl⟩ : syracuseStep 4643153 = 3482365) B3482365
theorem B3095435 : Blo 2063435 3095435 := bstep (se 1 (by rfl) ⟨2321576, by rfl⟩ : syracuseStep 3095435 = 4643153) B4643153
theorem B2063623 : Blo 2063435 2063623 := bstep (se 1 (by rfl) ⟨1547717, by rfl⟩ : syracuseStep 2063623 = 3095435) B3095435
theorem B2321581 : Blo 2063435 2321581 := bbase (se 3 (by rfl) ⟨435296, by rfl⟩ : syracuseStep 2321581 = 870593) (by norm_num)
theorem B3095441 : Blo 2063435 3095441 := bstep (se 2 (by rfl) ⟨1160790, by rfl⟩ : syracuseStep 3095441 = 2321581) B2321581
theorem B2063627 : Blo 2063435 2063627 := bstep (se 1 (by rfl) ⟨1547720, by rfl⟩ : syracuseStep 2063627 = 3095441) B3095441
theorem B6964757 : Blo 2063435 6964757 := bbase (se 6 (by rfl) ⟨163236, by rfl⟩ : syracuseStep 6964757 = 326473) (by norm_num)
theorem B4643171 : Blo 2063435 4643171 := bstep (se 1 (by rfl) ⟨3482378, by rfl⟩ : syracuseStep 4643171 = 6964757) B6964757
theorem B3095447 : Blo 2063435 3095447 := bstep (se 1 (by rfl) ⟨2321585, by rfl⟩ : syracuseStep 3095447 = 4643171) B4643171
theorem B2063631 : Blo 2063435 2063631 := bstep (se 1 (by rfl) ⟨1547723, by rfl⟩ : syracuseStep 2063631 = 3095447) B3095447
theorem B3095453 : Blo 2063435 3095453 := bbase (se 3 (by rfl) ⟨580397, by rfl⟩ : syracuseStep 3095453 = 1160795) (by norm_num)
theorem B2063635 : Blo 2063435 2063635 := bstep (se 1 (by rfl) ⟨1547726, by rfl⟩ : syracuseStep 2063635 = 3095453) B3095453
theorem B4643189 : Blo 2063435 4643189 := bbase (se 5 (by rfl) ⟨217649, by rfl⟩ : syracuseStep 4643189 = 435299) (by norm_num)
theorem B3095459 : Blo 2063435 3095459 := bstep (se 1 (by rfl) ⟨2321594, by rfl⟩ : syracuseStep 3095459 = 4643189) B4643189
theorem B2063639 : Blo 2063435 2063639 := bstep (se 1 (by rfl) ⟨1547729, by rfl⟩ : syracuseStep 2063639 = 3095459) B3095459
theorem B7437509 : Blo 2063435 7437509 := bbase (se 4 (by rfl) ⟨697266, by rfl⟩ : syracuseStep 7437509 = 1394533) (by norm_num)
theorem B4958339 : Blo 2063435 4958339 := bstep (se 1 (by rfl) ⟨3718754, by rfl⟩ : syracuseStep 4958339 = 7437509) B7437509
theorem B13222237 : Blo 2063435 13222237 := bstep (se 3 (by rfl) ⟨2479169, by rfl⟩ : syracuseStep 13222237 = 4958339) B4958339
theorem B17629649 : Blo 2063435 17629649 := bstep (se 2 (by rfl) ⟨6611118, by rfl⟩ : syracuseStep 17629649 = 13222237) B13222237
theorem B11753099 : Blo 2063435 11753099 := bstep (se 1 (by rfl) ⟨8814824, by rfl⟩ : syracuseStep 11753099 = 17629649) B17629649
theorem B7835399 : Blo 2063435 7835399 := bstep (se 1 (by rfl) ⟨5876549, by rfl⟩ : syracuseStep 7835399 = 11753099) B11753099
theorem B5223599 : Blo 2063435 5223599 := bstep (se 1 (by rfl) ⟨3917699, by rfl⟩ : syracuseStep 5223599 = 7835399) B7835399
theorem B3482399 : Blo 2063435 3482399 := bstep (se 1 (by rfl) ⟨2611799, by rfl⟩ : syracuseStep 3482399 = 5223599) B5223599
theorem B2321599 : Blo 2063435 2321599 := bstep (se 1 (by rfl) ⟨1741199, by rfl⟩ : syracuseStep 2321599 = 3482399) B3482399
theorem B3095465 : Blo 2063435 3095465 := bstep (se 2 (by rfl) ⟨1160799, by rfl⟩ : syracuseStep 3095465 = 2321599) B2321599
theorem B2063643 : Blo 2063435 2063643 := bstep (se 1 (by rfl) ⟨1547732, by rfl⟩ : syracuseStep 2063643 = 3095465) B3095465
theorem B7835413 : Blo 2063435 7835413 := bbase (se 6 (by rfl) ⟨183642, by rfl⟩ : syracuseStep 7835413 = 367285) (by norm_num)
theorem B10447217 : Blo 2063435 10447217 := bstep (se 2 (by rfl) ⟨3917706, by rfl⟩ : syracuseStep 10447217 = 7835413) B7835413
theorem B6964811 : Blo 2063435 6964811 := bstep (se 1 (by rfl) ⟨5223608, by rfl⟩ : syracuseStep 6964811 = 10447217) B10447217
theorem B4643207 : Blo 2063435 4643207 := bstep (se 1 (by rfl) ⟨3482405, by rfl⟩ : syracuseStep 4643207 = 6964811) B6964811
theorem B3095471 : Blo 2063435 3095471 := bstep (se 1 (by rfl) ⟨2321603, by rfl⟩ : syracuseStep 3095471 = 4643207) B4643207
theorem B2063647 : Blo 2063435 2063647 := bstep (se 1 (by rfl) ⟨1547735, by rfl⟩ : syracuseStep 2063647 = 3095471) B3095471
theorem B3095477 : Blo 2063435 3095477 := bbase (se 5 (by rfl) ⟨145100, by rfl⟩ : syracuseStep 3095477 = 290201) (by norm_num)
theorem B2063651 : Blo 2063435 2063651 := bstep (se 1 (by rfl) ⟨1547738, by rfl⟩ : syracuseStep 2063651 = 3095477) B3095477
theorem B5223629 : Blo 2063435 5223629 := bbase (se 3 (by rfl) ⟨979430, by rfl⟩ : syracuseStep 5223629 = 1958861) (by norm_num)
theorem B3482419 : Blo 2063435 3482419 := bstep (se 1 (by rfl) ⟨2611814, by rfl⟩ : syracuseStep 3482419 = 5223629) B5223629
theorem B4643225 : Blo 2063435 4643225 := bstep (se 2 (by rfl) ⟨1741209, by rfl⟩ : syracuseStep 4643225 = 3482419) B3482419
theorem B3095483 : Blo 2063435 3095483 := bstep (se 1 (by rfl) ⟨2321612, by rfl⟩ : syracuseStep 3095483 = 4643225) B4643225
theorem B2063655 : Blo 2063435 2063655 := bstep (se 1 (by rfl) ⟨1547741, by rfl⟩ : syracuseStep 2063655 = 3095483) B3095483
theorem B2321617 : Blo 2063435 2321617 := bbase (se 2 (by rfl) ⟨870606, by rfl⟩ : syracuseStep 2321617 = 1741213) (by norm_num)
theorem B3095489 : Blo 2063435 3095489 := bstep (se 2 (by rfl) ⟨1160808, by rfl⟩ : syracuseStep 3095489 = 2321617) B2321617
theorem B2063659 : Blo 2063435 2063659 := bstep (se 1 (by rfl) ⟨1547744, by rfl⟩ : syracuseStep 2063659 = 3095489) B3095489
theorem B12895733 : Blo 2063435 12895733 := bbase (se 5 (by rfl) ⟨604487, by rfl⟩ : syracuseStep 12895733 = 1208975) (by norm_num)
theorem B34388621 : Blo 2063435 34388621 := bstep (se 3 (by rfl) ⟨6447866, by rfl⟩ : syracuseStep 34388621 = 12895733) B12895733
theorem B22925747 : Blo 2063435 22925747 := bstep (se 1 (by rfl) ⟨17194310, by rfl⟩ : syracuseStep 22925747 = 34388621) B34388621
theorem B15283831 : Blo 2063435 15283831 := bstep (se 1 (by rfl) ⟨11462873, by rfl⟩ : syracuseStep 15283831 = 22925747) B22925747
theorem B20378441 : Blo 2063435 20378441 := bstep (se 2 (by rfl) ⟨7641915, by rfl⟩ : syracuseStep 20378441 = 15283831) B15283831
theorem B13585627 : Blo 2063435 13585627 := bstep (se 1 (by rfl) ⟨10189220, by rfl⟩ : syracuseStep 13585627 = 20378441) B20378441
theorem B72456677 : Blo 2063435 72456677 := bstep (se 4 (by rfl) ⟨6792813, by rfl⟩ : syracuseStep 72456677 = 13585627) B13585627
theorem B48304451 : Blo 2063435 48304451 := bstep (se 1 (by rfl) ⟨36228338, by rfl⟩ : syracuseStep 48304451 = 72456677) B72456677
theorem B32202967 : Blo 2063435 32202967 := bstep (se 1 (by rfl) ⟨24152225, by rfl⟩ : syracuseStep 32202967 = 48304451) B48304451
theorem B42937289 : Blo 2063435 42937289 := bstep (se 2 (by rfl) ⟨16101483, by rfl⟩ : syracuseStep 42937289 = 32202967) B32202967
theorem B28624859 : Blo 2063435 28624859 := bstep (se 1 (by rfl) ⟨21468644, by rfl⟩ : syracuseStep 28624859 = 42937289) B42937289
theorem B19083239 : Blo 2063435 19083239 := bstep (se 1 (by rfl) ⟨14312429, by rfl⟩ : syracuseStep 19083239 = 28624859) B28624859
theorem B12722159 : Blo 2063435 12722159 := bstep (se 1 (by rfl) ⟨9541619, by rfl⟩ : syracuseStep 12722159 = 19083239) B19083239
theorem B8481439 : Blo 2063435 8481439 := bstep (se 1 (by rfl) ⟨6361079, by rfl⟩ : syracuseStep 8481439 = 12722159) B12722159
theorem B11308585 : Blo 2063435 11308585 := bstep (se 2 (by rfl) ⟨4240719, by rfl⟩ : syracuseStep 11308585 = 8481439) B8481439
theorem B15078113 : Blo 2063435 15078113 := bstep (se 2 (by rfl) ⟨5654292, by rfl⟩ : syracuseStep 15078113 = 11308585) B11308585
theorem B10052075 : Blo 2063435 10052075 := bstep (se 1 (by rfl) ⟨7539056, by rfl⟩ : syracuseStep 10052075 = 15078113) B15078113
theorem B6701383 : Blo 2063435 6701383 := bstep (se 1 (by rfl) ⟨5026037, by rfl⟩ : syracuseStep 6701383 = 10052075) B10052075
theorem B8935177 : Blo 2063435 8935177 := bstep (se 2 (by rfl) ⟨3350691, by rfl⟩ : syracuseStep 8935177 = 6701383) B6701383
theorem B11913569 : Blo 2063435 11913569 := bstep (se 2 (by rfl) ⟨4467588, by rfl⟩ : syracuseStep 11913569 = 8935177) B8935177
theorem B7942379 : Blo 2063435 7942379 := bstep (se 1 (by rfl) ⟨5956784, by rfl⟩ : syracuseStep 7942379 = 11913569) B11913569
theorem B84718709 : Blo 2063435 84718709 := bstep (se 5 (by rfl) ⟨3971189, by rfl⟩ : syracuseStep 84718709 = 7942379) B7942379
theorem B56479139 : Blo 2063435 56479139 := bstep (se 1 (by rfl) ⟨42359354, by rfl⟩ : syracuseStep 56479139 = 84718709) B84718709
theorem B37652759 : Blo 2063435 37652759 := bstep (se 1 (by rfl) ⟨28239569, by rfl⟩ : syracuseStep 37652759 = 56479139) B56479139
theorem B25101839 : Blo 2063435 25101839 := bstep (se 1 (by rfl) ⟨18826379, by rfl⟩ : syracuseStep 25101839 = 37652759) B37652759
theorem B16734559 : Blo 2063435 16734559 := bstep (se 1 (by rfl) ⟨12550919, by rfl⟩ : syracuseStep 16734559 = 25101839) B25101839
theorem B22312745 : Blo 2063435 22312745 := bstep (se 2 (by rfl) ⟨8367279, by rfl⟩ : syracuseStep 22312745 = 16734559) B16734559
theorem B14875163 : Blo 2063435 14875163 := bstep (se 1 (by rfl) ⟨11156372, by rfl⟩ : syracuseStep 14875163 = 22312745) B22312745
theorem B9916775 : Blo 2063435 9916775 := bstep (se 1 (by rfl) ⟨7437581, by rfl⟩ : syracuseStep 9916775 = 14875163) B14875163
theorem B6611183 : Blo 2063435 6611183 := bstep (se 1 (by rfl) ⟨4958387, by rfl⟩ : syracuseStep 6611183 = 9916775) B9916775
theorem B4407455 : Blo 2063435 4407455 := bstep (se 1 (by rfl) ⟨3305591, by rfl⟩ : syracuseStep 4407455 = 6611183) B6611183
theorem B2938303 : Blo 2063435 2938303 := bstep (se 1 (by rfl) ⟨2203727, by rfl⟩ : syracuseStep 2938303 = 4407455) B4407455
theorem B3917737 : Blo 2063435 3917737 := bstep (se 2 (by rfl) ⟨1469151, by rfl⟩ : syracuseStep 3917737 = 2938303) B2938303
theorem B5223649 : Blo 2063435 5223649 := bstep (se 2 (by rfl) ⟨1958868, by rfl⟩ : syracuseStep 5223649 = 3917737) B3917737
theorem B6964865 : Blo 2063435 6964865 := bstep (se 2 (by rfl) ⟨2611824, by rfl⟩ : syracuseStep 6964865 = 5223649) B5223649
theorem B4643243 : Blo 2063435 4643243 := bstep (se 1 (by rfl) ⟨3482432, by rfl⟩ : syracuseStep 4643243 = 6964865) B6964865
theorem B3095495 : Blo 2063435 3095495 := bstep (se 1 (by rfl) ⟨2321621, by rfl⟩ : syracuseStep 3095495 = 4643243) B4643243
theorem B2063663 : Blo 2063435 2063663 := bstep (se 1 (by rfl) ⟨1547747, by rfl⟩ : syracuseStep 2063663 = 3095495) B3095495
theorem B3095501 : Blo 2063435 3095501 := bbase (se 3 (by rfl) ⟨580406, by rfl⟩ : syracuseStep 3095501 = 1160813) (by norm_num)
theorem B2063667 : Blo 2063435 2063667 := bstep (se 1 (by rfl) ⟨1547750, by rfl⟩ : syracuseStep 2063667 = 3095501) B3095501
theorem B4643261 : Blo 2063435 4643261 := bbase (se 3 (by rfl) ⟨870611, by rfl⟩ : syracuseStep 4643261 = 1741223) (by norm_num)
theorem B3095507 : Blo 2063435 3095507 := bstep (se 1 (by rfl) ⟨2321630, by rfl⟩ : syracuseStep 3095507 = 4643261) B4643261
theorem B2063671 : Blo 2063435 2063671 := bstep (se 1 (by rfl) ⟨1547753, by rfl⟩ : syracuseStep 2063671 = 3095507) B3095507
theorem B3482453 : Blo 2063435 3482453 := bbase (se 9 (by rfl) ⟨10202, by rfl⟩ : syracuseStep 3482453 = 20405) (by norm_num)
theorem B2321635 : Blo 2063435 2321635 := bstep (se 1 (by rfl) ⟨1741226, by rfl⟩ : syracuseStep 2321635 = 3482453) B3482453
theorem B3095513 : Blo 2063435 3095513 := bstep (se 2 (by rfl) ⟨1160817, by rfl⟩ : syracuseStep 3095513 = 2321635) B2321635
theorem B2063675 : Blo 2063435 2063675 := bstep (se 1 (by rfl) ⟨1547756, by rfl⟩ : syracuseStep 2063675 = 3095513) B3095513
theorem B5578229 : Blo 2063435 5578229 := bbase (se 5 (by rfl) ⟨261479, by rfl⟩ : syracuseStep 5578229 = 522959) (by norm_num)
theorem B3718819 : Blo 2063435 3718819 := bstep (se 1 (by rfl) ⟨2789114, by rfl⟩ : syracuseStep 3718819 = 5578229) B5578229
theorem B4958425 : Blo 2063435 4958425 := bstep (se 2 (by rfl) ⟨1859409, by rfl⟩ : syracuseStep 4958425 = 3718819) B3718819
theorem B6611233 : Blo 2063435 6611233 := bstep (se 2 (by rfl) ⟨2479212, by rfl⟩ : syracuseStep 6611233 = 4958425) B4958425
theorem B8814977 : Blo 2063435 8814977 := bstep (se 2 (by rfl) ⟨3305616, by rfl⟩ : syracuseStep 8814977 = 6611233) B6611233
theorem B5876651 : Blo 2063435 5876651 := bstep (se 1 (by rfl) ⟨4407488, by rfl⟩ : syracuseStep 5876651 = 8814977) B8814977
theorem B15671069 : Blo 2063435 15671069 := bstep (se 3 (by rfl) ⟨2938325, by rfl⟩ : syracuseStep 15671069 = 5876651) B5876651
theorem B10447379 : Blo 2063435 10447379 := bstep (se 1 (by rfl) ⟨7835534, by rfl⟩ : syracuseStep 10447379 = 15671069) B15671069
theorem B6964919 : Blo 2063435 6964919 := bstep (se 1 (by rfl) ⟨5223689, by rfl⟩ : syracuseStep 6964919 = 10447379) B10447379
theorem B4643279 : Blo 2063435 4643279 := bstep (se 1 (by rfl) ⟨3482459, by rfl⟩ : syracuseStep 4643279 = 6964919) B6964919
theorem B3095519 : Blo 2063435 3095519 := bstep (se 1 (by rfl) ⟨2321639, by rfl⟩ : syracuseStep 3095519 = 4643279) B4643279
theorem B2063679 : Blo 2063435 2063679 := bstep (se 1 (by rfl) ⟨1547759, by rfl⟩ : syracuseStep 2063679 = 3095519) B3095519
theorem B3095525 : Blo 2063435 3095525 := bbase (se 4 (by rfl) ⟨290205, by rfl⟩ : syracuseStep 3095525 = 580411) (by norm_num)
theorem B2063683 : Blo 2063435 2063683 := bstep (se 1 (by rfl) ⟨1547762, by rfl⟩ : syracuseStep 2063683 = 3095525) B3095525
theorem B8815013 : Blo 2063435 8815013 := bbase (se 4 (by rfl) ⟨826407, by rfl⟩ : syracuseStep 8815013 = 1652815) (by norm_num)
theorem B5876675 : Blo 2063435 5876675 := bstep (se 1 (by rfl) ⟨4407506, by rfl⟩ : syracuseStep 5876675 = 8815013) B8815013
theorem B3917783 : Blo 2063435 3917783 := bstep (se 1 (by rfl) ⟨2938337, by rfl⟩ : syracuseStep 3917783 = 5876675) B5876675
theorem B2611855 : Blo 2063435 2611855 := bstep (se 1 (by rfl) ⟨1958891, by rfl⟩ : syracuseStep 2611855 = 3917783) B3917783
theorem B3482473 : Blo 2063435 3482473 := bstep (se 2 (by rfl) ⟨1305927, by rfl⟩ : syracuseStep 3482473 = 2611855) B2611855
theorem B4643297 : Blo 2063435 4643297 := bstep (se 2 (by rfl) ⟨1741236, by rfl⟩ : syracuseStep 4643297 = 3482473) B3482473
theorem B3095531 : Blo 2063435 3095531 := bstep (se 1 (by rfl) ⟨2321648, by rfl⟩ : syracuseStep 3095531 = 4643297) B4643297
theorem B2063687 : Blo 2063435 2063687 := bstep (se 1 (by rfl) ⟨1547765, by rfl⟩ : syracuseStep 2063687 = 3095531) B3095531
theorem B2321653 : Blo 2063435 2321653 := bbase (se 5 (by rfl) ⟨108827, by rfl⟩ : syracuseStep 2321653 = 217655) (by norm_num)
theorem B3095537 : Blo 2063435 3095537 := bstep (se 2 (by rfl) ⟨1160826, by rfl⟩ : syracuseStep 3095537 = 2321653) B2321653
theorem B2063691 : Blo 2063435 2063691 := bstep (se 1 (by rfl) ⟨1547768, by rfl⟩ : syracuseStep 2063691 = 3095537) B3095537
theorem B2611865 : Blo 2063435 2611865 := bbase (se 2 (by rfl) ⟨979449, by rfl⟩ : syracuseStep 2611865 = 1958899) (by norm_num)
theorem B6964973 : Blo 2063435 6964973 := bstep (se 3 (by rfl) ⟨1305932, by rfl⟩ : syracuseStep 6964973 = 2611865) B2611865
theorem B4643315 : Blo 2063435 4643315 := bstep (se 1 (by rfl) ⟨3482486, by rfl⟩ : syracuseStep 4643315 = 6964973) B6964973
theorem B3095543 : Blo 2063435 3095543 := bstep (se 1 (by rfl) ⟨2321657, by rfl⟩ : syracuseStep 3095543 = 4643315) B4643315
theorem B2063695 : Blo 2063435 2063695 := bstep (se 1 (by rfl) ⟨1547771, by rfl⟩ : syracuseStep 2063695 = 3095543) B3095543
theorem B3095549 : Blo 2063435 3095549 := bbase (se 3 (by rfl) ⟨580415, by rfl⟩ : syracuseStep 3095549 = 1160831) (by norm_num)
theorem B2063699 : Blo 2063435 2063699 := bstep (se 1 (by rfl) ⟨1547774, by rfl⟩ : syracuseStep 2063699 = 3095549) B3095549
theorem B4643333 : Blo 2063435 4643333 := bbase (se 4 (by rfl) ⟨435312, by rfl⟩ : syracuseStep 4643333 = 870625) (by norm_num)
theorem B3095555 : Blo 2063435 3095555 := bstep (se 1 (by rfl) ⟨2321666, by rfl⟩ : syracuseStep 3095555 = 4643333) B4643333
theorem B2063703 : Blo 2063435 2063703 := bstep (se 1 (by rfl) ⟨1547777, by rfl⟩ : syracuseStep 2063703 = 3095555) B3095555
theorem B3917821 : Blo 2063435 3917821 := bbase (se 3 (by rfl) ⟨734591, by rfl⟩ : syracuseStep 3917821 = 1469183) (by norm_num)
theorem B5223761 : Blo 2063435 5223761 := bstep (se 2 (by rfl) ⟨1958910, by rfl⟩ : syracuseStep 5223761 = 3917821) B3917821
theorem B3482507 : Blo 2063435 3482507 := bstep (se 1 (by rfl) ⟨2611880, by rfl⟩ : syracuseStep 3482507 = 5223761) B5223761
theorem B2321671 : Blo 2063435 2321671 := bstep (se 1 (by rfl) ⟨1741253, by rfl⟩ : syracuseStep 2321671 = 3482507) B3482507
theorem B3095561 : Blo 2063435 3095561 := bstep (se 2 (by rfl) ⟨1160835, by rfl⟩ : syracuseStep 3095561 = 2321671) B2321671
theorem B2063707 : Blo 2063435 2063707 := bstep (se 1 (by rfl) ⟨1547780, by rfl⟩ : syracuseStep 2063707 = 3095561) B3095561
theorem B10447541 : Blo 2063435 10447541 := bbase (se 5 (by rfl) ⟨489728, by rfl⟩ : syracuseStep 10447541 = 979457) (by norm_num)
theorem B6965027 : Blo 2063435 6965027 := bstep (se 1 (by rfl) ⟨5223770, by rfl⟩ : syracuseStep 6965027 = 10447541) B10447541
theorem B4643351 : Blo 2063435 4643351 := bstep (se 1 (by rfl) ⟨3482513, by rfl⟩ : syracuseStep 4643351 = 6965027) B6965027
theorem B3095567 : Blo 2063435 3095567 := bstep (se 1 (by rfl) ⟨2321675, by rfl⟩ : syracuseStep 3095567 = 4643351) B4643351
theorem B2063711 : Blo 2063435 2063711 := bstep (se 1 (by rfl) ⟨1547783, by rfl⟩ : syracuseStep 2063711 = 3095567) B3095567
theorem B3095573 : Blo 2063435 3095573 := bbase (se 6 (by rfl) ⟨72552, by rfl⟩ : syracuseStep 3095573 = 145105) (by norm_num)
theorem B2063715 : Blo 2063435 2063715 := bstep (se 1 (by rfl) ⟨1547786, by rfl⟩ : syracuseStep 2063715 = 3095573) B3095573
theorem B7060085 : Blo 2063435 7060085 := bbase (se 5 (by rfl) ⟨330941, by rfl⟩ : syracuseStep 7060085 = 661883) (by norm_num)
theorem B4706723 : Blo 2063435 4706723 := bstep (se 1 (by rfl) ⟨3530042, by rfl⟩ : syracuseStep 4706723 = 7060085) B7060085
theorem B3137815 : Blo 2063435 3137815 := bstep (se 1 (by rfl) ⟨2353361, by rfl⟩ : syracuseStep 3137815 = 4706723) B4706723
theorem B4183753 : Blo 2063435 4183753 := bstep (se 2 (by rfl) ⟨1568907, by rfl⟩ : syracuseStep 4183753 = 3137815) B3137815
theorem B5578337 : Blo 2063435 5578337 := bstep (se 2 (by rfl) ⟨2091876, by rfl⟩ : syracuseStep 5578337 = 4183753) B4183753
theorem B3718891 : Blo 2063435 3718891 := bstep (se 1 (by rfl) ⟨2789168, by rfl⟩ : syracuseStep 3718891 = 5578337) B5578337
theorem B19834085 : Blo 2063435 19834085 := bstep (se 4 (by rfl) ⟨1859445, by rfl⟩ : syracuseStep 19834085 = 3718891) B3718891
theorem B13222723 : Blo 2063435 13222723 := bstep (se 1 (by rfl) ⟨9917042, by rfl⟩ : syracuseStep 13222723 = 19834085) B19834085
theorem B17630297 : Blo 2063435 17630297 := bstep (se 2 (by rfl) ⟨6611361, by rfl⟩ : syracuseStep 17630297 = 13222723) B13222723
theorem B11753531 : Blo 2063435 11753531 := bstep (se 1 (by rfl) ⟨8815148, by rfl⟩ : syracuseStep 11753531 = 17630297) B17630297
theorem B7835687 : Blo 2063435 7835687 := bstep (se 1 (by rfl) ⟨5876765, by rfl⟩ : syracuseStep 7835687 = 11753531) B11753531
theorem B5223791 : Blo 2063435 5223791 := bstep (se 1 (by rfl) ⟨3917843, by rfl⟩ : syracuseStep 5223791 = 7835687) B7835687
theorem B3482527 : Blo 2063435 3482527 := bstep (se 1 (by rfl) ⟨2611895, by rfl⟩ : syracuseStep 3482527 = 5223791) B5223791
theorem B4643369 : Blo 2063435 4643369 := bstep (se 2 (by rfl) ⟨1741263, by rfl⟩ : syracuseStep 4643369 = 3482527) B3482527
theorem B3095579 : Blo 2063435 3095579 := bstep (se 1 (by rfl) ⟨2321684, by rfl⟩ : syracuseStep 3095579 = 4643369) B4643369
theorem B2063719 : Blo 2063435 2063719 := bstep (se 1 (by rfl) ⟨1547789, by rfl⟩ : syracuseStep 2063719 = 3095579) B3095579
theorem B2321689 : Blo 2063435 2321689 := bbase (se 2 (by rfl) ⟨870633, by rfl⟩ : syracuseStep 2321689 = 1741267) (by norm_num)
theorem B3095585 : Blo 2063435 3095585 := bstep (se 2 (by rfl) ⟨1160844, by rfl⟩ : syracuseStep 3095585 = 2321689) B2321689
theorem B2063723 : Blo 2063435 2063723 := bstep (se 1 (by rfl) ⟨1547792, by rfl⟩ : syracuseStep 2063723 = 3095585) B3095585
theorem B7835717 : Blo 2063435 7835717 := bbase (se 4 (by rfl) ⟨734598, by rfl⟩ : syracuseStep 7835717 = 1469197) (by norm_num)
theorem B5223811 : Blo 2063435 5223811 := bstep (se 1 (by rfl) ⟨3917858, by rfl⟩ : syracuseStep 5223811 = 7835717) B7835717
theorem B6965081 : Blo 2063435 6965081 := bstep (se 2 (by rfl) ⟨2611905, by rfl⟩ : syracuseStep 6965081 = 5223811) B5223811
theorem B4643387 : Blo 2063435 4643387 := bstep (se 1 (by rfl) ⟨3482540, by rfl⟩ : syracuseStep 4643387 = 6965081) B6965081
theorem B3095591 : Blo 2063435 3095591 := bstep (se 1 (by rfl) ⟨2321693, by rfl⟩ : syracuseStep 3095591 = 4643387) B4643387
theorem B2063727 : Blo 2063435 2063727 := bstep (se 1 (by rfl) ⟨1547795, by rfl⟩ : syracuseStep 2063727 = 3095591) B3095591
theorem B3095597 : Blo 2063435 3095597 := bbase (se 3 (by rfl) ⟨580424, by rfl⟩ : syracuseStep 3095597 = 1160849) (by norm_num)
theorem B2063731 : Blo 2063435 2063731 := bstep (se 1 (by rfl) ⟨1547798, by rfl⟩ : syracuseStep 2063731 = 3095597) B3095597
theorem B4643405 : Blo 2063435 4643405 := bbase (se 3 (by rfl) ⟨870638, by rfl⟩ : syracuseStep 4643405 = 1741277) (by norm_num)
theorem B3095603 : Blo 2063435 3095603 := bstep (se 1 (by rfl) ⟨2321702, by rfl⟩ : syracuseStep 3095603 = 4643405) B4643405
theorem B2063735 : Blo 2063435 2063735 := bstep (se 1 (by rfl) ⟨1547801, by rfl⟩ : syracuseStep 2063735 = 3095603) B3095603
theorem B2611921 : Blo 2063435 2611921 := bbase (se 2 (by rfl) ⟨979470, by rfl⟩ : syracuseStep 2611921 = 1958941) (by norm_num)
theorem B3482561 : Blo 2063435 3482561 := bstep (se 2 (by rfl) ⟨1305960, by rfl⟩ : syracuseStep 3482561 = 2611921) B2611921
theorem B2321707 : Blo 2063435 2321707 := bstep (se 1 (by rfl) ⟨1741280, by rfl⟩ : syracuseStep 2321707 = 3482561) B3482561
theorem B3095609 : Blo 2063435 3095609 := bstep (se 2 (by rfl) ⟨1160853, by rfl⟩ : syracuseStep 3095609 = 2321707) B2321707
theorem B2063739 : Blo 2063435 2063739 := bstep (se 1 (by rfl) ⟨1547804, by rfl⟩ : syracuseStep 2063739 = 3095609) B3095609
theorem B2091901 : Blo 2063435 2091901 := bbase (se 3 (by rfl) ⟨392231, by rfl⟩ : syracuseStep 2091901 = 784463) (by norm_num)
theorem B2789201 : Blo 2063435 2789201 := bstep (se 2 (by rfl) ⟨1045950, by rfl⟩ : syracuseStep 2789201 = 2091901) B2091901
theorem B7437869 : Blo 2063435 7437869 := bstep (se 3 (by rfl) ⟨1394600, by rfl⟩ : syracuseStep 7437869 = 2789201) B2789201
theorem B4958579 : Blo 2063435 4958579 := bstep (se 1 (by rfl) ⟨3718934, by rfl⟩ : syracuseStep 4958579 = 7437869) B7437869
theorem B3305719 : Blo 2063435 3305719 := bstep (se 1 (by rfl) ⟨2479289, by rfl⟩ : syracuseStep 3305719 = 4958579) B4958579
theorem B4407625 : Blo 2063435 4407625 := bstep (se 2 (by rfl) ⟨1652859, by rfl⟩ : syracuseStep 4407625 = 3305719) B3305719
theorem B23507333 : Blo 2063435 23507333 := bstep (se 4 (by rfl) ⟨2203812, by rfl⟩ : syracuseStep 23507333 = 4407625) B4407625
theorem B15671555 : Blo 2063435 15671555 := bstep (se 1 (by rfl) ⟨11753666, by rfl⟩ : syracuseStep 15671555 = 23507333) B23507333
theorem B10447703 : Blo 2063435 10447703 := bstep (se 1 (by rfl) ⟨7835777, by rfl⟩ : syracuseStep 10447703 = 15671555) B15671555
theorem B6965135 : Blo 2063435 6965135 := bstep (se 1 (by rfl) ⟨5223851, by rfl⟩ : syracuseStep 6965135 = 10447703) B10447703
theorem B4643423 : Blo 2063435 4643423 := bstep (se 1 (by rfl) ⟨3482567, by rfl⟩ : syracuseStep 4643423 = 6965135) B6965135
theorem B3095615 : Blo 2063435 3095615 := bstep (se 1 (by rfl) ⟨2321711, by rfl⟩ : syracuseStep 3095615 = 4643423) B4643423
theorem B2063743 : Blo 2063435 2063743 := bstep (se 1 (by rfl) ⟨1547807, by rfl⟩ : syracuseStep 2063743 = 3095615) B3095615
theorem B3095621 : Blo 2063435 3095621 := bbase (se 4 (by rfl) ⟨290214, by rfl⟩ : syracuseStep 3095621 = 580429) (by norm_num)
theorem B2063747 : Blo 2063435 2063747 := bstep (se 1 (by rfl) ⟨1547810, by rfl⟩ : syracuseStep 2063747 = 3095621) B3095621
theorem B3482581 : Blo 2063435 3482581 := bbase (se 7 (by rfl) ⟨40811, by rfl⟩ : syracuseStep 3482581 = 81623) (by norm_num)
theorem B4643441 : Blo 2063435 4643441 := bstep (se 2 (by rfl) ⟨1741290, by rfl⟩ : syracuseStep 4643441 = 3482581) B3482581
theorem B3095627 : Blo 2063435 3095627 := bstep (se 1 (by rfl) ⟨2321720, by rfl⟩ : syracuseStep 3095627 = 4643441) B4643441
theorem B2063751 : Blo 2063435 2063751 := bstep (se 1 (by rfl) ⟨1547813, by rfl⟩ : syracuseStep 2063751 = 3095627) B3095627
theorem B2321725 : Blo 2063435 2321725 := bbase (se 3 (by rfl) ⟨435323, by rfl⟩ : syracuseStep 2321725 = 870647) (by norm_num)
theorem B3095633 : Blo 2063435 3095633 := bstep (se 2 (by rfl) ⟨1160862, by rfl⟩ : syracuseStep 3095633 = 2321725) B2321725
theorem B2063755 : Blo 2063435 2063755 := bstep (se 1 (by rfl) ⟨1547816, by rfl⟩ : syracuseStep 2063755 = 3095633) B3095633
theorem B6965189 : Blo 2063435 6965189 := bbase (se 4 (by rfl) ⟨652986, by rfl⟩ : syracuseStep 6965189 = 1305973) (by norm_num)
theorem B4643459 : Blo 2063435 4643459 := bstep (se 1 (by rfl) ⟨3482594, by rfl⟩ : syracuseStep 4643459 = 6965189) B6965189
theorem B3095639 : Blo 2063435 3095639 := bstep (se 1 (by rfl) ⟨2321729, by rfl⟩ : syracuseStep 3095639 = 4643459) B4643459
theorem B2063759 : Blo 2063435 2063759 := bstep (se 1 (by rfl) ⟨1547819, by rfl⟩ : syracuseStep 2063759 = 3095639) B3095639
theorem B3095645 : Blo 2063435 3095645 := bbase (se 3 (by rfl) ⟨580433, by rfl⟩ : syracuseStep 3095645 = 1160867) (by norm_num)
theorem B2063763 : Blo 2063435 2063763 := bstep (se 1 (by rfl) ⟨1547822, by rfl⟩ : syracuseStep 2063763 = 3095645) B3095645
theorem B4643477 : Blo 2063435 4643477 := bbase (se 6 (by rfl) ⟨108831, by rfl⟩ : syracuseStep 4643477 = 217663) (by norm_num)
theorem B3095651 : Blo 2063435 3095651 := bstep (se 1 (by rfl) ⟨2321738, by rfl⟩ : syracuseStep 3095651 = 4643477) B4643477
theorem B2063767 : Blo 2063435 2063767 := bstep (se 1 (by rfl) ⟨1547825, by rfl⟩ : syracuseStep 2063767 = 3095651) B3095651
theorem B3305765 : Blo 2063435 3305765 := bbase (se 4 (by rfl) ⟨309915, by rfl⟩ : syracuseStep 3305765 = 619831) (by norm_num)
theorem B2203843 : Blo 2063435 2203843 := bstep (se 1 (by rfl) ⟨1652882, by rfl⟩ : syracuseStep 2203843 = 3305765) B3305765
theorem B2938457 : Blo 2063435 2938457 := bstep (se 2 (by rfl) ⟨1101921, by rfl⟩ : syracuseStep 2938457 = 2203843) B2203843
theorem B7835885 : Blo 2063435 7835885 := bstep (se 3 (by rfl) ⟨1469228, by rfl⟩ : syracuseStep 7835885 = 2938457) B2938457
theorem B5223923 : Blo 2063435 5223923 := bstep (se 1 (by rfl) ⟨3917942, by rfl⟩ : syracuseStep 5223923 = 7835885) B7835885
theorem B3482615 : Blo 2063435 3482615 := bstep (se 1 (by rfl) ⟨2611961, by rfl⟩ : syracuseStep 3482615 = 5223923) B5223923
theorem B2321743 : Blo 2063435 2321743 := bstep (se 1 (by rfl) ⟨1741307, by rfl⟩ : syracuseStep 2321743 = 3482615) B3482615
theorem B3095657 : Blo 2063435 3095657 := bstep (se 2 (by rfl) ⟨1160871, by rfl⟩ : syracuseStep 3095657 = 2321743) B2321743
theorem B2063771 : Blo 2063435 2063771 := bstep (se 1 (by rfl) ⟨1547828, by rfl⟩ : syracuseStep 2063771 = 3095657) B3095657
theorem B8597621 : Blo 2063435 8597621 := bbase (se 5 (by rfl) ⟨403013, by rfl⟩ : syracuseStep 8597621 = 806027) (by norm_num)
theorem B22926989 : Blo 2063435 22926989 := bstep (se 3 (by rfl) ⟨4298810, by rfl⟩ : syracuseStep 22926989 = 8597621) B8597621
theorem B15284659 : Blo 2063435 15284659 := bstep (se 1 (by rfl) ⟨11463494, by rfl⟩ : syracuseStep 15284659 = 22926989) B22926989
theorem B20379545 : Blo 2063435 20379545 := bstep (se 2 (by rfl) ⟨7642329, by rfl⟩ : syracuseStep 20379545 = 15284659) B15284659
theorem B13586363 : Blo 2063435 13586363 := bstep (se 1 (by rfl) ⟨10189772, by rfl⟩ : syracuseStep 13586363 = 20379545) B20379545
theorem B9057575 : Blo 2063435 9057575 := bstep (se 1 (by rfl) ⟨6793181, by rfl⟩ : syracuseStep 9057575 = 13586363) B13586363
theorem B6038383 : Blo 2063435 6038383 := bstep (se 1 (by rfl) ⟨4528787, by rfl⟩ : syracuseStep 6038383 = 9057575) B9057575
theorem B8051177 : Blo 2063435 8051177 := bstep (se 2 (by rfl) ⟨3019191, by rfl⟩ : syracuseStep 8051177 = 6038383) B6038383
theorem B5367451 : Blo 2063435 5367451 := bstep (se 1 (by rfl) ⟨4025588, by rfl⟩ : syracuseStep 5367451 = 8051177) B8051177
theorem B7156601 : Blo 2063435 7156601 := bstep (se 2 (by rfl) ⟨2683725, by rfl⟩ : syracuseStep 7156601 = 5367451) B5367451
theorem B4771067 : Blo 2063435 4771067 := bstep (se 1 (by rfl) ⟨3578300, by rfl⟩ : syracuseStep 4771067 = 7156601) B7156601
theorem B12722845 : Blo 2063435 12722845 := bstep (se 3 (by rfl) ⟨2385533, by rfl⟩ : syracuseStep 12722845 = 4771067) B4771067
theorem B16963793 : Blo 2063435 16963793 := bstep (se 2 (by rfl) ⟨6361422, by rfl⟩ : syracuseStep 16963793 = 12722845) B12722845
theorem B11309195 : Blo 2063435 11309195 := bstep (se 1 (by rfl) ⟨8481896, by rfl⟩ : syracuseStep 11309195 = 16963793) B16963793
theorem B7539463 : Blo 2063435 7539463 := bstep (se 1 (by rfl) ⟨5654597, by rfl⟩ : syracuseStep 7539463 = 11309195) B11309195
theorem B10052617 : Blo 2063435 10052617 := bstep (se 2 (by rfl) ⟨3769731, by rfl⟩ : syracuseStep 10052617 = 7539463) B7539463
theorem B13403489 : Blo 2063435 13403489 := bstep (se 2 (by rfl) ⟨5026308, by rfl⟩ : syracuseStep 13403489 = 10052617) B10052617
theorem B35742637 : Blo 2063435 35742637 := bstep (se 3 (by rfl) ⟨6701744, by rfl⟩ : syracuseStep 35742637 = 13403489) B13403489
theorem B47656849 : Blo 2063435 47656849 := bstep (se 2 (by rfl) ⟨17871318, by rfl⟩ : syracuseStep 47656849 = 35742637) B35742637
theorem B63542465 : Blo 2063435 63542465 := bstep (se 2 (by rfl) ⟨23828424, by rfl⟩ : syracuseStep 63542465 = 47656849) B47656849
theorem B42361643 : Blo 2063435 42361643 := bstep (se 1 (by rfl) ⟨31771232, by rfl⟩ : syracuseStep 42361643 = 63542465) B63542465
theorem B112964381 : Blo 2063435 112964381 := bstep (se 3 (by rfl) ⟨21180821, by rfl⟩ : syracuseStep 112964381 = 42361643) B42361643
theorem B75309587 : Blo 2063435 75309587 := bstep (se 1 (by rfl) ⟨56482190, by rfl⟩ : syracuseStep 75309587 = 112964381) B112964381
theorem B50206391 : Blo 2063435 50206391 := bstep (se 1 (by rfl) ⟨37654793, by rfl⟩ : syracuseStep 50206391 = 75309587) B75309587
theorem B33470927 : Blo 2063435 33470927 := bstep (se 1 (by rfl) ⟨25103195, by rfl⟩ : syracuseStep 33470927 = 50206391) B50206391
theorem B22313951 : Blo 2063435 22313951 := bstep (se 1 (by rfl) ⟨16735463, by rfl⟩ : syracuseStep 22313951 = 33470927) B33470927
theorem B14875967 : Blo 2063435 14875967 := bstep (se 1 (by rfl) ⟨11156975, by rfl⟩ : syracuseStep 14875967 = 22313951) B22313951
theorem B9917311 : Blo 2063435 9917311 := bstep (se 1 (by rfl) ⟨7437983, by rfl⟩ : syracuseStep 9917311 = 14875967) B14875967
theorem B13223081 : Blo 2063435 13223081 := bstep (se 2 (by rfl) ⟨4958655, by rfl⟩ : syracuseStep 13223081 = 9917311) B9917311
theorem B8815387 : Blo 2063435 8815387 := bstep (se 1 (by rfl) ⟨6611540, by rfl⟩ : syracuseStep 8815387 = 13223081) B13223081
theorem B11753849 : Blo 2063435 11753849 := bstep (se 2 (by rfl) ⟨4407693, by rfl⟩ : syracuseStep 11753849 = 8815387) B8815387
theorem B7835899 : Blo 2063435 7835899 := bstep (se 1 (by rfl) ⟨5876924, by rfl⟩ : syracuseStep 7835899 = 11753849) B11753849
theorem B10447865 : Blo 2063435 10447865 := bstep (se 2 (by rfl) ⟨3917949, by rfl⟩ : syracuseStep 10447865 = 7835899) B7835899
theorem B6965243 : Blo 2063435 6965243 := bstep (se 1 (by rfl) ⟨5223932, by rfl⟩ : syracuseStep 6965243 = 10447865) B10447865
theorem B4643495 : Blo 2063435 4643495 := bstep (se 1 (by rfl) ⟨3482621, by rfl⟩ : syracuseStep 4643495 = 6965243) B6965243
theorem B3095663 : Blo 2063435 3095663 := bstep (se 1 (by rfl) ⟨2321747, by rfl⟩ : syracuseStep 3095663 = 4643495) B4643495
theorem B2063775 : Blo 2063435 2063775 := bstep (se 1 (by rfl) ⟨1547831, by rfl⟩ : syracuseStep 2063775 = 3095663) B3095663
theorem B3095669 : Blo 2063435 3095669 := bbase (se 5 (by rfl) ⟨145109, by rfl⟩ : syracuseStep 3095669 = 290219) (by norm_num)
theorem B2063779 : Blo 2063435 2063779 := bstep (se 1 (by rfl) ⟨1547834, by rfl⟩ : syracuseStep 2063779 = 3095669) B3095669
theorem B3917965 : Blo 2063435 3917965 := bbase (se 3 (by rfl) ⟨734618, by rfl⟩ : syracuseStep 3917965 = 1469237) (by norm_num)
theorem B5223953 : Blo 2063435 5223953 := bstep (se 2 (by rfl) ⟨1958982, by rfl⟩ : syracuseStep 5223953 = 3917965) B3917965
theorem B3482635 : Blo 2063435 3482635 := bstep (se 1 (by rfl) ⟨2611976, by rfl⟩ : syracuseStep 3482635 = 5223953) B5223953
theorem B4643513 : Blo 2063435 4643513 := bstep (se 2 (by rfl) ⟨1741317, by rfl⟩ : syracuseStep 4643513 = 3482635) B3482635
theorem B3095675 : Blo 2063435 3095675 := bstep (se 1 (by rfl) ⟨2321756, by rfl⟩ : syracuseStep 3095675 = 4643513) B4643513
theorem B2063783 : Blo 2063435 2063783 := bstep (se 1 (by rfl) ⟨1547837, by rfl⟩ : syracuseStep 2063783 = 3095675) B3095675
theorem B2321761 : Blo 2063435 2321761 := bbase (se 2 (by rfl) ⟨870660, by rfl⟩ : syracuseStep 2321761 = 1741321) (by norm_num)
theorem B3095681 : Blo 2063435 3095681 := bstep (se 2 (by rfl) ⟨1160880, by rfl⟩ : syracuseStep 3095681 = 2321761) B2321761
theorem B2063787 : Blo 2063435 2063787 := bstep (se 1 (by rfl) ⟨1547840, by rfl⟩ : syracuseStep 2063787 = 3095681) B3095681
theorem B5223973 : Blo 2063435 5223973 := bbase (se 4 (by rfl) ⟨489747, by rfl⟩ : syracuseStep 5223973 = 979495) (by norm_num)
theorem B6965297 : Blo 2063435 6965297 := bstep (se 2 (by rfl) ⟨2611986, by rfl⟩ : syracuseStep 6965297 = 5223973) B5223973
theorem B4643531 : Blo 2063435 4643531 := bstep (se 1 (by rfl) ⟨3482648, by rfl⟩ : syracuseStep 4643531 = 6965297) B6965297
theorem B3095687 : Blo 2063435 3095687 := bstep (se 1 (by rfl) ⟨2321765, by rfl⟩ : syracuseStep 3095687 = 4643531) B4643531
theorem B2063791 : Blo 2063435 2063791 := bstep (se 1 (by rfl) ⟨1547843, by rfl⟩ : syracuseStep 2063791 = 3095687) B3095687
theorem B3095693 : Blo 2063435 3095693 := bbase (se 3 (by rfl) ⟨580442, by rfl⟩ : syracuseStep 3095693 = 1160885) (by norm_num)
theorem B2063795 : Blo 2063435 2063795 := bstep (se 1 (by rfl) ⟨1547846, by rfl⟩ : syracuseStep 2063795 = 3095693) B3095693
theorem B4643549 : Blo 2063435 4643549 := bbase (se 3 (by rfl) ⟨870665, by rfl⟩ : syracuseStep 4643549 = 1741331) (by norm_num)
theorem B3095699 : Blo 2063435 3095699 := bstep (se 1 (by rfl) ⟨2321774, by rfl⟩ : syracuseStep 3095699 = 4643549) B4643549
theorem B2063799 : Blo 2063435 2063799 := bstep (se 1 (by rfl) ⟨1547849, by rfl⟩ : syracuseStep 2063799 = 3095699) B3095699
theorem B3482669 : Blo 2063435 3482669 := bbase (se 3 (by rfl) ⟨653000, by rfl⟩ : syracuseStep 3482669 = 1306001) (by norm_num)
theorem B2321779 : Blo 2063435 2321779 := bstep (se 1 (by rfl) ⟨1741334, by rfl⟩ : syracuseStep 2321779 = 3482669) B3482669
theorem B3095705 : Blo 2063435 3095705 := bstep (se 2 (by rfl) ⟨1160889, by rfl⟩ : syracuseStep 3095705 = 2321779) B2321779
theorem B2063803 : Blo 2063435 2063803 := bstep (se 1 (by rfl) ⟨1547852, by rfl⟩ : syracuseStep 2063803 = 3095705) B3095705
theorem B35743189 : Blo 2063435 35743189 := bbase (se 7 (by rfl) ⟨418865, by rfl⟩ : syracuseStep 35743189 = 837731) (by norm_num)
theorem B47657585 : Blo 2063435 47657585 := bstep (se 2 (by rfl) ⟨17871594, by rfl⟩ : syracuseStep 47657585 = 35743189) B35743189
theorem B31771723 : Blo 2063435 31771723 := bstep (se 1 (by rfl) ⟨23828792, by rfl⟩ : syracuseStep 31771723 = 47657585) B47657585
theorem B42362297 : Blo 2063435 42362297 := bstep (se 2 (by rfl) ⟨15885861, by rfl⟩ : syracuseStep 42362297 = 31771723) B31771723
theorem B28241531 : Blo 2063435 28241531 := bstep (se 1 (by rfl) ⟨21181148, by rfl⟩ : syracuseStep 28241531 = 42362297) B42362297
theorem B18827687 : Blo 2063435 18827687 := bstep (se 1 (by rfl) ⟨14120765, by rfl⟩ : syracuseStep 18827687 = 28241531) B28241531
theorem B50207165 : Blo 2063435 50207165 := bstep (se 3 (by rfl) ⟨9413843, by rfl⟩ : syracuseStep 50207165 = 18827687) B18827687
theorem B33471443 : Blo 2063435 33471443 := bstep (se 1 (by rfl) ⟨25103582, by rfl⟩ : syracuseStep 33471443 = 50207165) B50207165
theorem B22314295 : Blo 2063435 22314295 := bstep (se 1 (by rfl) ⟨16735721, by rfl⟩ : syracuseStep 22314295 = 33471443) B33471443
theorem B29752393 : Blo 2063435 29752393 := bstep (se 2 (by rfl) ⟨11157147, by rfl⟩ : syracuseStep 29752393 = 22314295) B22314295
theorem B39669857 : Blo 2063435 39669857 := bstep (se 2 (by rfl) ⟨14876196, by rfl⟩ : syracuseStep 39669857 = 29752393) B29752393
theorem B26446571 : Blo 2063435 26446571 := bstep (se 1 (by rfl) ⟨19834928, by rfl⟩ : syracuseStep 26446571 = 39669857) B39669857
theorem B17631047 : Blo 2063435 17631047 := bstep (se 1 (by rfl) ⟨13223285, by rfl⟩ : syracuseStep 17631047 = 26446571) B26446571
theorem B11754031 : Blo 2063435 11754031 := bstep (se 1 (by rfl) ⟨8815523, by rfl⟩ : syracuseStep 11754031 = 17631047) B17631047
theorem B15672041 : Blo 2063435 15672041 := bstep (se 2 (by rfl) ⟨5877015, by rfl⟩ : syracuseStep 15672041 = 11754031) B11754031
theorem B10448027 : Blo 2063435 10448027 := bstep (se 1 (by rfl) ⟨7836020, by rfl⟩ : syracuseStep 10448027 = 15672041) B15672041
theorem B6965351 : Blo 2063435 6965351 := bstep (se 1 (by rfl) ⟨5224013, by rfl⟩ : syracuseStep 6965351 = 10448027) B10448027
theorem B4643567 : Blo 2063435 4643567 := bstep (se 1 (by rfl) ⟨3482675, by rfl⟩ : syracuseStep 4643567 = 6965351) B6965351
theorem B3095711 : Blo 2063435 3095711 := bstep (se 1 (by rfl) ⟨2321783, by rfl⟩ : syracuseStep 3095711 = 4643567) B4643567
theorem B2063807 : Blo 2063435 2063807 := bstep (se 1 (by rfl) ⟨1547855, by rfl⟩ : syracuseStep 2063807 = 3095711) B3095711
theorem B3095717 : Blo 2063435 3095717 := bbase (se 4 (by rfl) ⟨290223, by rfl⟩ : syracuseStep 3095717 = 580447) (by norm_num)
theorem B2063811 : Blo 2063435 2063811 := bstep (se 1 (by rfl) ⟨1547858, by rfl⟩ : syracuseStep 2063811 = 3095717) B3095717
theorem B2612017 : Blo 2063435 2612017 := bbase (se 2 (by rfl) ⟨979506, by rfl⟩ : syracuseStep 2612017 = 1959013) (by norm_num)
theorem B3482689 : Blo 2063435 3482689 := bstep (se 2 (by rfl) ⟨1306008, by rfl⟩ : syracuseStep 3482689 = 2612017) B2612017
theorem B4643585 : Blo 2063435 4643585 := bstep (se 2 (by rfl) ⟨1741344, by rfl⟩ : syracuseStep 4643585 = 3482689) B3482689
theorem B3095723 : Blo 2063435 3095723 := bstep (se 1 (by rfl) ⟨2321792, by rfl⟩ : syracuseStep 3095723 = 4643585) B4643585
theorem B2063815 : Blo 2063435 2063815 := bstep (se 1 (by rfl) ⟨1547861, by rfl⟩ : syracuseStep 2063815 = 3095723) B3095723
theorem B2321797 : Blo 2063435 2321797 := bbase (se 4 (by rfl) ⟨217668, by rfl⟩ : syracuseStep 2321797 = 435337) (by norm_num)
theorem B3095729 : Blo 2063435 3095729 := bstep (se 2 (by rfl) ⟨1160898, by rfl⟩ : syracuseStep 3095729 = 2321797) B2321797
theorem B2063819 : Blo 2063435 2063819 := bstep (se 1 (by rfl) ⟨1547864, by rfl⟩ : syracuseStep 2063819 = 3095729) B3095729
theorem B4407797 : Blo 2063435 4407797 := bbase (se 5 (by rfl) ⟨206615, by rfl⟩ : syracuseStep 4407797 = 413231) (by norm_num)
theorem B2938531 : Blo 2063435 2938531 := bstep (se 1 (by rfl) ⟨2203898, by rfl⟩ : syracuseStep 2938531 = 4407797) B4407797
theorem B3918041 : Blo 2063435 3918041 := bstep (se 2 (by rfl) ⟨1469265, by rfl⟩ : syracuseStep 3918041 = 2938531) B2938531
theorem B2612027 : Blo 2063435 2612027 := bstep (se 1 (by rfl) ⟨1959020, by rfl⟩ : syracuseStep 2612027 = 3918041) B3918041
theorem B6965405 : Blo 2063435 6965405 := bstep (se 3 (by rfl) ⟨1306013, by rfl⟩ : syracuseStep 6965405 = 2612027) B2612027
theorem B4643603 : Blo 2063435 4643603 := bstep (se 1 (by rfl) ⟨3482702, by rfl⟩ : syracuseStep 4643603 = 6965405) B6965405
theorem B3095735 : Blo 2063435 3095735 := bstep (se 1 (by rfl) ⟨2321801, by rfl⟩ : syracuseStep 3095735 = 4643603) B4643603
theorem B2063823 : Blo 2063435 2063823 := bstep (se 1 (by rfl) ⟨1547867, by rfl⟩ : syracuseStep 2063823 = 3095735) B3095735
theorem B3095741 : Blo 2063435 3095741 := bbase (se 3 (by rfl) ⟨580451, by rfl⟩ : syracuseStep 3095741 = 1160903) (by norm_num)
theorem B2063827 : Blo 2063435 2063827 := bstep (se 1 (by rfl) ⟨1547870, by rfl⟩ : syracuseStep 2063827 = 3095741) B3095741
theorem B4643621 : Blo 2063435 4643621 := bbase (se 4 (by rfl) ⟨435339, by rfl⟩ : syracuseStep 4643621 = 870679) (by norm_num)
theorem B3095747 : Blo 2063435 3095747 := bstep (se 1 (by rfl) ⟨2321810, by rfl⟩ : syracuseStep 3095747 = 4643621) B4643621
theorem B2063831 : Blo 2063435 2063831 := bstep (se 1 (by rfl) ⟨1547873, by rfl⟩ : syracuseStep 2063831 = 3095747) B3095747
theorem B5224085 : Blo 2063435 5224085 := bbase (se 6 (by rfl) ⟨122439, by rfl⟩ : syracuseStep 5224085 = 244879) (by norm_num)
theorem B3482723 : Blo 2063435 3482723 := bstep (se 1 (by rfl) ⟨2612042, by rfl⟩ : syracuseStep 3482723 = 5224085) B5224085
theorem B2321815 : Blo 2063435 2321815 := bstep (se 1 (by rfl) ⟨1741361, by rfl⟩ : syracuseStep 2321815 = 3482723) B3482723
theorem B3095753 : Blo 2063435 3095753 := bstep (se 2 (by rfl) ⟨1160907, by rfl⟩ : syracuseStep 3095753 = 2321815) B2321815
theorem B2063835 : Blo 2063435 2063835 := bstep (se 1 (by rfl) ⟨1547876, by rfl⟩ : syracuseStep 2063835 = 3095753) B3095753
theorem B2479405 : Blo 2063435 2479405 := bbase (se 3 (by rfl) ⟨464888, by rfl⟩ : syracuseStep 2479405 = 929777) (by norm_num)
theorem B3305873 : Blo 2063435 3305873 := bstep (se 2 (by rfl) ⟨1239702, by rfl⟩ : syracuseStep 3305873 = 2479405) B2479405
theorem B8815661 : Blo 2063435 8815661 := bstep (se 3 (by rfl) ⟨1652936, by rfl⟩ : syracuseStep 8815661 = 3305873) B3305873
theorem B5877107 : Blo 2063435 5877107 := bstep (se 1 (by rfl) ⟨4407830, by rfl⟩ : syracuseStep 5877107 = 8815661) B8815661
theorem B3918071 : Blo 2063435 3918071 := bstep (se 1 (by rfl) ⟨2938553, by rfl⟩ : syracuseStep 3918071 = 5877107) B5877107
theorem B10448189 : Blo 2063435 10448189 := bstep (se 3 (by rfl) ⟨1959035, by rfl⟩ : syracuseStep 10448189 = 3918071) B3918071
theorem B6965459 : Blo 2063435 6965459 := bstep (se 1 (by rfl) ⟨5224094, by rfl⟩ : syracuseStep 6965459 = 10448189) B10448189
theorem B4643639 : Blo 2063435 4643639 := bstep (se 1 (by rfl) ⟨3482729, by rfl⟩ : syracuseStep 4643639 = 6965459) B6965459
theorem B3095759 : Blo 2063435 3095759 := bstep (se 1 (by rfl) ⟨2321819, by rfl⟩ : syracuseStep 3095759 = 4643639) B4643639
theorem B2063839 : Blo 2063435 2063839 := bstep (se 1 (by rfl) ⟨1547879, by rfl⟩ : syracuseStep 2063839 = 3095759) B3095759
theorem B3095765 : Blo 2063435 3095765 := bbase (se 7 (by rfl) ⟨36278, by rfl⟩ : syracuseStep 3095765 = 72557) (by norm_num)
theorem B2063843 : Blo 2063435 2063843 := bstep (se 1 (by rfl) ⟨1547882, by rfl⟩ : syracuseStep 2063843 = 3095765) B3095765
theorem B2938565 : Blo 2063435 2938565 := bbase (se 4 (by rfl) ⟨275490, by rfl⟩ : syracuseStep 2938565 = 550981) (by norm_num)
theorem B7836173 : Blo 2063435 7836173 := bstep (se 3 (by rfl) ⟨1469282, by rfl⟩ : syracuseStep 7836173 = 2938565) B2938565
theorem B5224115 : Blo 2063435 5224115 := bstep (se 1 (by rfl) ⟨3918086, by rfl⟩ : syracuseStep 5224115 = 7836173) B7836173
theorem B3482743 : Blo 2063435 3482743 := bstep (se 1 (by rfl) ⟨2612057, by rfl⟩ : syracuseStep 3482743 = 5224115) B5224115
theorem B4643657 : Blo 2063435 4643657 := bstep (se 2 (by rfl) ⟨1741371, by rfl⟩ : syracuseStep 4643657 = 3482743) B3482743
theorem B3095771 : Blo 2063435 3095771 := bstep (se 1 (by rfl) ⟨2321828, by rfl⟩ : syracuseStep 3095771 = 4643657) B4643657
theorem B2063847 : Blo 2063435 2063847 := bstep (se 1 (by rfl) ⟨1547885, by rfl⟩ : syracuseStep 2063847 = 3095771) B3095771
theorem B2321833 : Blo 2063435 2321833 := bbase (se 2 (by rfl) ⟨870687, by rfl⟩ : syracuseStep 2321833 = 1741375) (by norm_num)
theorem B3095777 : Blo 2063435 3095777 := bstep (se 2 (by rfl) ⟨1160916, by rfl⟩ : syracuseStep 3095777 = 2321833) B2321833
theorem B2063851 : Blo 2063435 2063851 := bstep (se 1 (by rfl) ⟨1547888, by rfl⟩ : syracuseStep 2063851 = 3095777) B3095777
theorem B6611797 : Blo 2063435 6611797 := bbase (se 9 (by rfl) ⟨19370, by rfl⟩ : syracuseStep 6611797 = 38741) (by norm_num)
theorem B8815729 : Blo 2063435 8815729 := bstep (se 2 (by rfl) ⟨3305898, by rfl⟩ : syracuseStep 8815729 = 6611797) B6611797
theorem B11754305 : Blo 2063435 11754305 := bstep (se 2 (by rfl) ⟨4407864, by rfl⟩ : syracuseStep 11754305 = 8815729) B8815729
theorem B7836203 : Blo 2063435 7836203 := bstep (se 1 (by rfl) ⟨5877152, by rfl⟩ : syracuseStep 7836203 = 11754305) B11754305
theorem B5224135 : Blo 2063435 5224135 := bstep (se 1 (by rfl) ⟨3918101, by rfl⟩ : syracuseStep 5224135 = 7836203) B7836203
theorem B6965513 : Blo 2063435 6965513 := bstep (se 2 (by rfl) ⟨2612067, by rfl⟩ : syracuseStep 6965513 = 5224135) B5224135
theorem B4643675 : Blo 2063435 4643675 := bstep (se 1 (by rfl) ⟨3482756, by rfl⟩ : syracuseStep 4643675 = 6965513) B6965513
theorem B3095783 : Blo 2063435 3095783 := bstep (se 1 (by rfl) ⟨2321837, by rfl⟩ : syracuseStep 3095783 = 4643675) B4643675
theorem B2063855 : Blo 2063435 2063855 := bstep (se 1 (by rfl) ⟨1547891, by rfl⟩ : syracuseStep 2063855 = 3095783) B3095783
theorem B3095789 : Blo 2063435 3095789 := bbase (se 3 (by rfl) ⟨580460, by rfl⟩ : syracuseStep 3095789 = 1160921) (by norm_num)
theorem B2063859 : Blo 2063435 2063859 := bstep (se 1 (by rfl) ⟨1547894, by rfl⟩ : syracuseStep 2063859 = 3095789) B3095789
theorem B4643693 : Blo 2063435 4643693 := bbase (se 3 (by rfl) ⟨870692, by rfl⟩ : syracuseStep 4643693 = 1741385) (by norm_num)
theorem B3095795 : Blo 2063435 3095795 := bstep (se 1 (by rfl) ⟨2321846, by rfl⟩ : syracuseStep 3095795 = 4643693) B4643693
theorem B2063863 : Blo 2063435 2063863 := bstep (se 1 (by rfl) ⟨1547897, by rfl⟩ : syracuseStep 2063863 = 3095795) B3095795
theorem B3918125 : Blo 2063435 3918125 := bbase (se 3 (by rfl) ⟨734648, by rfl⟩ : syracuseStep 3918125 = 1469297) (by norm_num)
theorem B2612083 : Blo 2063435 2612083 := bstep (se 1 (by rfl) ⟨1959062, by rfl⟩ : syracuseStep 2612083 = 3918125) B3918125
theorem B3482777 : Blo 2063435 3482777 := bstep (se 2 (by rfl) ⟨1306041, by rfl⟩ : syracuseStep 3482777 = 2612083) B2612083
theorem B2321851 : Blo 2063435 2321851 := bstep (se 1 (by rfl) ⟨1741388, by rfl⟩ : syracuseStep 2321851 = 3482777) B3482777
theorem B3095801 : Blo 2063435 3095801 := bstep (se 2 (by rfl) ⟨1160925, by rfl⟩ : syracuseStep 3095801 = 2321851) B2321851
theorem B2063867 : Blo 2063435 2063867 := bstep (se 1 (by rfl) ⟨1547900, by rfl⟩ : syracuseStep 2063867 = 3095801) B3095801
theorem B44629973 : Blo 2063435 44629973 := bbase (se 7 (by rfl) ⟨523007, by rfl⟩ : syracuseStep 44629973 = 1046015) (by norm_num)
theorem B29753315 : Blo 2063435 29753315 := bstep (se 1 (by rfl) ⟨22314986, by rfl⟩ : syracuseStep 29753315 = 44629973) B44629973
theorem B19835543 : Blo 2063435 19835543 := bstep (se 1 (by rfl) ⟨14876657, by rfl⟩ : syracuseStep 19835543 = 29753315) B29753315
theorem B52894781 : Blo 2063435 52894781 := bstep (se 3 (by rfl) ⟨9917771, by rfl⟩ : syracuseStep 52894781 = 19835543) B19835543
theorem B35263187 : Blo 2063435 35263187 := bstep (se 1 (by rfl) ⟨26447390, by rfl⟩ : syracuseStep 35263187 = 52894781) B52894781
theorem B23508791 : Blo 2063435 23508791 := bstep (se 1 (by rfl) ⟨17631593, by rfl⟩ : syracuseStep 23508791 = 35263187) B35263187
theorem B15672527 : Blo 2063435 15672527 := bstep (se 1 (by rfl) ⟨11754395, by rfl⟩ : syracuseStep 15672527 = 23508791) B23508791
theorem B10448351 : Blo 2063435 10448351 := bstep (se 1 (by rfl) ⟨7836263, by rfl⟩ : syracuseStep 10448351 = 15672527) B15672527
theorem B6965567 : Blo 2063435 6965567 := bstep (se 1 (by rfl) ⟨5224175, by rfl⟩ : syracuseStep 6965567 = 10448351) B10448351
theorem B4643711 : Blo 2063435 4643711 := bstep (se 1 (by rfl) ⟨3482783, by rfl⟩ : syracuseStep 4643711 = 6965567) B6965567
theorem B3095807 : Blo 2063435 3095807 := bstep (se 1 (by rfl) ⟨2321855, by rfl⟩ : syracuseStep 3095807 = 4643711) B4643711
theorem B2063871 : Blo 2063435 2063871 := bstep (se 1 (by rfl) ⟨1547903, by rfl⟩ : syracuseStep 2063871 = 3095807) B3095807
theorem B3095813 : Blo 2063435 3095813 := bbase (se 4 (by rfl) ⟨290232, by rfl⟩ : syracuseStep 3095813 = 580465) (by norm_num)
theorem B2063875 : Blo 2063435 2063875 := bstep (se 1 (by rfl) ⟨1547906, by rfl⟩ : syracuseStep 2063875 = 3095813) B3095813
theorem B3482797 : Blo 2063435 3482797 := bbase (se 3 (by rfl) ⟨653024, by rfl⟩ : syracuseStep 3482797 = 1306049) (by norm_num)
theorem B4643729 : Blo 2063435 4643729 := bstep (se 2 (by rfl) ⟨1741398, by rfl⟩ : syracuseStep 4643729 = 3482797) B3482797
theorem B3095819 : Blo 2063435 3095819 := bstep (se 1 (by rfl) ⟨2321864, by rfl⟩ : syracuseStep 3095819 = 4643729) B4643729
theorem B2063879 : Blo 2063435 2063879 := bstep (se 1 (by rfl) ⟨1547909, by rfl⟩ : syracuseStep 2063879 = 3095819) B3095819
theorem B2321869 : Blo 2063435 2321869 := bbase (se 3 (by rfl) ⟨435350, by rfl⟩ : syracuseStep 2321869 = 870701) (by norm_num)
theorem B3095825 : Blo 2063435 3095825 := bstep (se 2 (by rfl) ⟨1160934, by rfl⟩ : syracuseStep 3095825 = 2321869) B2321869
theorem B2063883 : Blo 2063435 2063883 := bstep (se 1 (by rfl) ⟨1547912, by rfl⟩ : syracuseStep 2063883 = 3095825) B3095825
theorem B6965621 : Blo 2063435 6965621 := bbase (se 5 (by rfl) ⟨326513, by rfl⟩ : syracuseStep 6965621 = 653027) (by norm_num)
theorem B4643747 : Blo 2063435 4643747 := bstep (se 1 (by rfl) ⟨3482810, by rfl⟩ : syracuseStep 4643747 = 6965621) B6965621
theorem B3095831 : Blo 2063435 3095831 := bstep (se 1 (by rfl) ⟨2321873, by rfl⟩ : syracuseStep 3095831 = 4643747) B4643747
theorem B2063887 : Blo 2063435 2063887 := bstep (se 1 (by rfl) ⟨1547915, by rfl⟩ : syracuseStep 2063887 = 3095831) B3095831
theorem B3095837 : Blo 2063435 3095837 := bbase (se 3 (by rfl) ⟨580469, by rfl⟩ : syracuseStep 3095837 = 1160939) (by norm_num)
theorem B2063891 : Blo 2063435 2063891 := bstep (se 1 (by rfl) ⟨1547918, by rfl⟩ : syracuseStep 2063891 = 3095837) B3095837
theorem B4643765 : Blo 2063435 4643765 := bbase (se 5 (by rfl) ⟨217676, by rfl⟩ : syracuseStep 4643765 = 435353) (by norm_num)
theorem B3095843 : Blo 2063435 3095843 := bstep (se 1 (by rfl) ⟨2321882, by rfl⟩ : syracuseStep 3095843 = 4643765) B4643765
theorem B2063895 : Blo 2063435 2063895 := bstep (se 1 (by rfl) ⟨1547921, by rfl⟩ : syracuseStep 2063895 = 3095843) B3095843
theorem B9917909 : Blo 2063435 9917909 := bbase (se 7 (by rfl) ⟨116225, by rfl⟩ : syracuseStep 9917909 = 232451) (by norm_num)
theorem B6611939 : Blo 2063435 6611939 := bstep (se 1 (by rfl) ⟨4958954, by rfl⟩ : syracuseStep 6611939 = 9917909) B9917909
theorem B4407959 : Blo 2063435 4407959 := bstep (se 1 (by rfl) ⟨3305969, by rfl⟩ : syracuseStep 4407959 = 6611939) B6611939
theorem B11754557 : Blo 2063435 11754557 := bstep (se 3 (by rfl) ⟨2203979, by rfl⟩ : syracuseStep 11754557 = 4407959) B4407959
theorem B7836371 : Blo 2063435 7836371 := bstep (se 1 (by rfl) ⟨5877278, by rfl⟩ : syracuseStep 7836371 = 11754557) B11754557
theorem B5224247 : Blo 2063435 5224247 := bstep (se 1 (by rfl) ⟨3918185, by rfl⟩ : syracuseStep 5224247 = 7836371) B7836371
theorem B3482831 : Blo 2063435 3482831 := bstep (se 1 (by rfl) ⟨2612123, by rfl⟩ : syracuseStep 3482831 = 5224247) B5224247
theorem B2321887 : Blo 2063435 2321887 := bstep (se 1 (by rfl) ⟨1741415, by rfl⟩ : syracuseStep 2321887 = 3482831) B3482831
theorem B3095849 : Blo 2063435 3095849 := bstep (se 2 (by rfl) ⟨1160943, by rfl⟩ : syracuseStep 3095849 = 2321887) B2321887
theorem B2063899 : Blo 2063435 2063899 := bstep (se 1 (by rfl) ⟨1547924, by rfl⟩ : syracuseStep 2063899 = 3095849) B3095849
theorem B5957477 : Blo 2063435 5957477 := bbase (se 4 (by rfl) ⟨558513, by rfl⟩ : syracuseStep 5957477 = 1117027) (by norm_num)
theorem B3971651 : Blo 2063435 3971651 := bstep (se 1 (by rfl) ⟨2978738, by rfl⟩ : syracuseStep 3971651 = 5957477) B5957477
theorem B10591069 : Blo 2063435 10591069 := bstep (se 3 (by rfl) ⟨1985825, by rfl⟩ : syracuseStep 10591069 = 3971651) B3971651
theorem B14121425 : Blo 2063435 14121425 := bstep (se 2 (by rfl) ⟨5295534, by rfl⟩ : syracuseStep 14121425 = 10591069) B10591069
theorem B37657133 : Blo 2063435 37657133 := bstep (se 3 (by rfl) ⟨7060712, by rfl⟩ : syracuseStep 37657133 = 14121425) B14121425
theorem B25104755 : Blo 2063435 25104755 := bstep (se 1 (by rfl) ⟨18828566, by rfl⟩ : syracuseStep 25104755 = 37657133) B37657133
theorem B16736503 : Blo 2063435 16736503 := bstep (se 1 (by rfl) ⟨12552377, by rfl⟩ : syracuseStep 16736503 = 25104755) B25104755
theorem B22315337 : Blo 2063435 22315337 := bstep (se 2 (by rfl) ⟨8368251, by rfl⟩ : syracuseStep 22315337 = 16736503) B16736503
theorem B14876891 : Blo 2063435 14876891 := bstep (se 1 (by rfl) ⟨11157668, by rfl⟩ : syracuseStep 14876891 = 22315337) B22315337
theorem B9917927 : Blo 2063435 9917927 := bstep (se 1 (by rfl) ⟨7438445, by rfl⟩ : syracuseStep 9917927 = 14876891) B14876891
theorem B6611951 : Blo 2063435 6611951 := bstep (se 1 (by rfl) ⟨4958963, by rfl⟩ : syracuseStep 6611951 = 9917927) B9917927
theorem B4407967 : Blo 2063435 4407967 := bstep (se 1 (by rfl) ⟨3305975, by rfl⟩ : syracuseStep 4407967 = 6611951) B6611951
theorem B5877289 : Blo 2063435 5877289 := bstep (se 2 (by rfl) ⟨2203983, by rfl⟩ : syracuseStep 5877289 = 4407967) B4407967
theorem B7836385 : Blo 2063435 7836385 := bstep (se 2 (by rfl) ⟨2938644, by rfl⟩ : syracuseStep 7836385 = 5877289) B5877289
theorem B10448513 : Blo 2063435 10448513 := bstep (se 2 (by rfl) ⟨3918192, by rfl⟩ : syracuseStep 10448513 = 7836385) B7836385
theorem B6965675 : Blo 2063435 6965675 := bstep (se 1 (by rfl) ⟨5224256, by rfl⟩ : syracuseStep 6965675 = 10448513) B10448513
theorem B4643783 : Blo 2063435 4643783 := bstep (se 1 (by rfl) ⟨3482837, by rfl⟩ : syracuseStep 4643783 = 6965675) B6965675
theorem B3095855 : Blo 2063435 3095855 := bstep (se 1 (by rfl) ⟨2321891, by rfl⟩ : syracuseStep 3095855 = 4643783) B4643783
theorem B2063903 : Blo 2063435 2063903 := bstep (se 1 (by rfl) ⟨1547927, by rfl⟩ : syracuseStep 2063903 = 3095855) B3095855
theorem B3095861 : Blo 2063435 3095861 := bbase (se 5 (by rfl) ⟨145118, by rfl⟩ : syracuseStep 3095861 = 290237) (by norm_num)
theorem B2063907 : Blo 2063435 2063907 := bstep (se 1 (by rfl) ⟨1547930, by rfl⟩ : syracuseStep 2063907 = 3095861) B3095861
theorem B5224277 : Blo 2063435 5224277 := bbase (se 9 (by rfl) ⟨15305, by rfl⟩ : syracuseStep 5224277 = 30611) (by norm_num)
theorem B3482851 : Blo 2063435 3482851 := bstep (se 1 (by rfl) ⟨2612138, by rfl⟩ : syracuseStep 3482851 = 5224277) B5224277
theorem B4643801 : Blo 2063435 4643801 := bstep (se 2 (by rfl) ⟨1741425, by rfl⟩ : syracuseStep 4643801 = 3482851) B3482851
theorem B3095867 : Blo 2063435 3095867 := bstep (se 1 (by rfl) ⟨2321900, by rfl⟩ : syracuseStep 3095867 = 4643801) B4643801
theorem B2063911 : Blo 2063435 2063911 := bstep (se 1 (by rfl) ⟨1547933, by rfl⟩ : syracuseStep 2063911 = 3095867) B3095867
theorem B2321905 : Blo 2063435 2321905 := bbase (se 2 (by rfl) ⟨870714, by rfl⟩ : syracuseStep 2321905 = 1741429) (by norm_num)
theorem B3095873 : Blo 2063435 3095873 := bstep (se 2 (by rfl) ⟨1160952, by rfl⟩ : syracuseStep 3095873 = 2321905) B2321905
theorem B2063915 : Blo 2063435 2063915 := bstep (se 1 (by rfl) ⟨1547936, by rfl⟩ : syracuseStep 2063915 = 3095873) B3095873
theorem B2479501 : Blo 2063435 2479501 := bbase (se 3 (by rfl) ⟨464906, by rfl⟩ : syracuseStep 2479501 = 929813) (by norm_num)
theorem B13224005 : Blo 2063435 13224005 := bstep (se 4 (by rfl) ⟨1239750, by rfl⟩ : syracuseStep 13224005 = 2479501) B2479501
theorem B8816003 : Blo 2063435 8816003 := bstep (se 1 (by rfl) ⟨6612002, by rfl⟩ : syracuseStep 8816003 = 13224005) B13224005
theorem B5877335 : Blo 2063435 5877335 := bstep (se 1 (by rfl) ⟨4408001, by rfl⟩ : syracuseStep 5877335 = 8816003) B8816003
theorem B3918223 : Blo 2063435 3918223 := bstep (se 1 (by rfl) ⟨2938667, by rfl⟩ : syracuseStep 3918223 = 5877335) B5877335
theorem B5224297 : Blo 2063435 5224297 := bstep (se 2 (by rfl) ⟨1959111, by rfl⟩ : syracuseStep 5224297 = 3918223) B3918223
theorem B6965729 : Blo 2063435 6965729 := bstep (se 2 (by rfl) ⟨2612148, by rfl⟩ : syracuseStep 6965729 = 5224297) B5224297
theorem B4643819 : Blo 2063435 4643819 := bstep (se 1 (by rfl) ⟨3482864, by rfl⟩ : syracuseStep 4643819 = 6965729) B6965729
theorem B3095879 : Blo 2063435 3095879 := bstep (se 1 (by rfl) ⟨2321909, by rfl⟩ : syracuseStep 3095879 = 4643819) B4643819
theorem B2063919 : Blo 2063435 2063919 := bstep (se 1 (by rfl) ⟨1547939, by rfl⟩ : syracuseStep 2063919 = 3095879) B3095879
theorem B3095885 : Blo 2063435 3095885 := bbase (se 3 (by rfl) ⟨580478, by rfl⟩ : syracuseStep 3095885 = 1160957) (by norm_num)
theorem B2063923 : Blo 2063435 2063923 := bstep (se 1 (by rfl) ⟨1547942, by rfl⟩ : syracuseStep 2063923 = 3095885) B3095885
theorem B4643837 : Blo 2063435 4643837 := bbase (se 3 (by rfl) ⟨870719, by rfl⟩ : syracuseStep 4643837 = 1741439) (by norm_num)
theorem B3095891 : Blo 2063435 3095891 := bstep (se 1 (by rfl) ⟨2321918, by rfl⟩ : syracuseStep 3095891 = 4643837) B4643837
theorem B2063927 : Blo 2063435 2063927 := bstep (se 1 (by rfl) ⟨1547945, by rfl⟩ : syracuseStep 2063927 = 3095891) B3095891
theorem B3482885 : Blo 2063435 3482885 := bbase (se 4 (by rfl) ⟨326520, by rfl⟩ : syracuseStep 3482885 = 653041) (by norm_num)
theorem B2321923 : Blo 2063435 2321923 := bstep (se 1 (by rfl) ⟨1741442, by rfl⟩ : syracuseStep 2321923 = 3482885) B3482885
theorem B3095897 : Blo 2063435 3095897 := bstep (se 2 (by rfl) ⟨1160961, by rfl⟩ : syracuseStep 3095897 = 2321923) B2321923
theorem B2063931 : Blo 2063435 2063931 := bstep (se 1 (by rfl) ⟨1547948, by rfl⟩ : syracuseStep 2063931 = 3095897) B3095897
theorem B15673013 : Blo 2063435 15673013 := bbase (se 5 (by rfl) ⟨734672, by rfl⟩ : syracuseStep 15673013 = 1469345) (by norm_num)
theorem B10448675 : Blo 2063435 10448675 := bstep (se 1 (by rfl) ⟨7836506, by rfl⟩ : syracuseStep 10448675 = 15673013) B15673013
theorem B6965783 : Blo 2063435 6965783 := bstep (se 1 (by rfl) ⟨5224337, by rfl⟩ : syracuseStep 6965783 = 10448675) B10448675
theorem B4643855 : Blo 2063435 4643855 := bstep (se 1 (by rfl) ⟨3482891, by rfl⟩ : syracuseStep 4643855 = 6965783) B6965783
theorem B3095903 : Blo 2063435 3095903 := bstep (se 1 (by rfl) ⟨2321927, by rfl⟩ : syracuseStep 3095903 = 4643855) B4643855
theorem B2063935 : Blo 2063435 2063935 := bstep (se 1 (by rfl) ⟨1547951, by rfl⟩ : syracuseStep 2063935 = 3095903) B3095903
theorem B3095909 : Blo 2063435 3095909 := bbase (se 4 (by rfl) ⟨290241, by rfl⟩ : syracuseStep 3095909 = 580483) (by norm_num)
theorem B2063939 : Blo 2063435 2063939 := bstep (se 1 (by rfl) ⟨1547954, by rfl⟩ : syracuseStep 2063939 = 3095909) B3095909
theorem B3918269 : Blo 2063435 3918269 := bbase (se 3 (by rfl) ⟨734675, by rfl⟩ : syracuseStep 3918269 = 1469351) (by norm_num)
theorem B2612179 : Blo 2063435 2612179 := bstep (se 1 (by rfl) ⟨1959134, by rfl⟩ : syracuseStep 2612179 = 3918269) B3918269
theorem B3482905 : Blo 2063435 3482905 := bstep (se 2 (by rfl) ⟨1306089, by rfl⟩ : syracuseStep 3482905 = 2612179) B2612179
theorem B4643873 : Blo 2063435 4643873 := bstep (se 2 (by rfl) ⟨1741452, by rfl⟩ : syracuseStep 4643873 = 3482905) B3482905
theorem B3095915 : Blo 2063435 3095915 := bstep (se 1 (by rfl) ⟨2321936, by rfl⟩ : syracuseStep 3095915 = 4643873) B4643873
theorem B2063943 : Blo 2063435 2063943 := bstep (se 1 (by rfl) ⟨1547957, by rfl⟩ : syracuseStep 2063943 = 3095915) B3095915
theorem B2321941 : Blo 2063435 2321941 := bbase (se 6 (by rfl) ⟨54420, by rfl⟩ : syracuseStep 2321941 = 108841) (by norm_num)
theorem B3095921 : Blo 2063435 3095921 := bstep (se 2 (by rfl) ⟨1160970, by rfl⟩ : syracuseStep 3095921 = 2321941) B2321941
theorem B2063947 : Blo 2063435 2063947 := bstep (se 1 (by rfl) ⟨1547960, by rfl⟩ : syracuseStep 2063947 = 3095921) B3095921
theorem B2612189 : Blo 2063435 2612189 := bbase (se 3 (by rfl) ⟨489785, by rfl⟩ : syracuseStep 2612189 = 979571) (by norm_num)
theorem B6965837 : Blo 2063435 6965837 := bstep (se 3 (by rfl) ⟨1306094, by rfl⟩ : syracuseStep 6965837 = 2612189) B2612189
theorem B4643891 : Blo 2063435 4643891 := bstep (se 1 (by rfl) ⟨3482918, by rfl⟩ : syracuseStep 4643891 = 6965837) B6965837
theorem B3095927 : Blo 2063435 3095927 := bstep (se 1 (by rfl) ⟨2321945, by rfl⟩ : syracuseStep 3095927 = 4643891) B4643891
theorem B2063951 : Blo 2063435 2063951 := bstep (se 1 (by rfl) ⟨1547963, by rfl⟩ : syracuseStep 2063951 = 3095927) B3095927
theorem B3095933 : Blo 2063435 3095933 := bbase (se 3 (by rfl) ⟨580487, by rfl⟩ : syracuseStep 3095933 = 1160975) (by norm_num)
theorem B2063955 : Blo 2063435 2063955 := bstep (se 1 (by rfl) ⟨1547966, by rfl⟩ : syracuseStep 2063955 = 3095933) B3095933
theorem B4643909 : Blo 2063435 4643909 := bbase (se 4 (by rfl) ⟨435366, by rfl⟩ : syracuseStep 4643909 = 870733) (by norm_num)
theorem B3095939 : Blo 2063435 3095939 := bstep (se 1 (by rfl) ⟨2321954, by rfl⟩ : syracuseStep 3095939 = 4643909) B4643909
theorem B2063959 : Blo 2063435 2063959 := bstep (se 1 (by rfl) ⟨1547969, by rfl⟩ : syracuseStep 2063959 = 3095939) B3095939
theorem B5877461 : Blo 2063435 5877461 := bbase (se 7 (by rfl) ⟨68876, by rfl⟩ : syracuseStep 5877461 = 137753) (by norm_num)
theorem B3918307 : Blo 2063435 3918307 := bstep (se 1 (by rfl) ⟨2938730, by rfl⟩ : syracuseStep 3918307 = 5877461) B5877461
theorem B5224409 : Blo 2063435 5224409 := bstep (se 2 (by rfl) ⟨1959153, by rfl⟩ : syracuseStep 5224409 = 3918307) B3918307
theorem B3482939 : Blo 2063435 3482939 := bstep (se 1 (by rfl) ⟨2612204, by rfl⟩ : syracuseStep 3482939 = 5224409) B5224409
theorem B2321959 : Blo 2063435 2321959 := bstep (se 1 (by rfl) ⟨1741469, by rfl⟩ : syracuseStep 2321959 = 3482939) B3482939
theorem B3095945 : Blo 2063435 3095945 := bstep (se 2 (by rfl) ⟨1160979, by rfl⟩ : syracuseStep 3095945 = 2321959) B2321959
theorem B2063963 : Blo 2063435 2063963 := bstep (se 1 (by rfl) ⟨1547972, by rfl⟩ : syracuseStep 2063963 = 3095945) B3095945
theorem B10448837 : Blo 2063435 10448837 := bbase (se 4 (by rfl) ⟨979578, by rfl⟩ : syracuseStep 10448837 = 1959157) (by norm_num)
theorem B6965891 : Blo 2063435 6965891 := bstep (se 1 (by rfl) ⟨5224418, by rfl⟩ : syracuseStep 6965891 = 10448837) B10448837
theorem B4643927 : Blo 2063435 4643927 := bstep (se 1 (by rfl) ⟨3482945, by rfl⟩ : syracuseStep 4643927 = 6965891) B6965891
theorem B3095951 : Blo 2063435 3095951 := bstep (se 1 (by rfl) ⟨2321963, by rfl⟩ : syracuseStep 3095951 = 4643927) B4643927
theorem B2063967 : Blo 2063435 2063967 := bstep (se 1 (by rfl) ⟨1547975, by rfl⟩ : syracuseStep 2063967 = 3095951) B3095951
theorem B3095957 : Blo 2063435 3095957 := bbase (se 6 (by rfl) ⟨72561, by rfl⟩ : syracuseStep 3095957 = 145123) (by norm_num)
theorem B2063971 : Blo 2063435 2063971 := bstep (se 1 (by rfl) ⟨1547978, by rfl⟩ : syracuseStep 2063971 = 3095957) B3095957
theorem B3138205 : Blo 2063435 3138205 := bbase (se 3 (by rfl) ⟨588413, by rfl⟩ : syracuseStep 3138205 = 1176827) (by norm_num)
theorem B4184273 : Blo 2063435 4184273 := bstep (se 2 (by rfl) ⟨1569102, by rfl⟩ : syracuseStep 4184273 = 3138205) B3138205
theorem B2789515 : Blo 2063435 2789515 := bstep (se 1 (by rfl) ⟨2092136, by rfl⟩ : syracuseStep 2789515 = 4184273) B4184273
theorem B3719353 : Blo 2063435 3719353 := bstep (se 2 (by rfl) ⟨1394757, by rfl⟩ : syracuseStep 3719353 = 2789515) B2789515
theorem B4959137 : Blo 2063435 4959137 := bstep (se 2 (by rfl) ⟨1859676, by rfl⟩ : syracuseStep 4959137 = 3719353) B3719353
theorem B3306091 : Blo 2063435 3306091 := bstep (se 1 (by rfl) ⟨2479568, by rfl⟩ : syracuseStep 3306091 = 4959137) B4959137
theorem B4408121 : Blo 2063435 4408121 := bstep (se 2 (by rfl) ⟨1653045, by rfl⟩ : syracuseStep 4408121 = 3306091) B3306091
theorem B11754989 : Blo 2063435 11754989 := bstep (se 3 (by rfl) ⟨2204060, by rfl⟩ : syracuseStep 11754989 = 4408121) B4408121
theorem B7836659 : Blo 2063435 7836659 := bstep (se 1 (by rfl) ⟨5877494, by rfl⟩ : syracuseStep 7836659 = 11754989) B11754989
theorem B5224439 : Blo 2063435 5224439 := bstep (se 1 (by rfl) ⟨3918329, by rfl⟩ : syracuseStep 5224439 = 7836659) B7836659
theorem B3482959 : Blo 2063435 3482959 := bstep (se 1 (by rfl) ⟨2612219, by rfl⟩ : syracuseStep 3482959 = 5224439) B5224439
theorem B4643945 : Blo 2063435 4643945 := bstep (se 2 (by rfl) ⟨1741479, by rfl⟩ : syracuseStep 4643945 = 3482959) B3482959
theorem B3095963 : Blo 2063435 3095963 := bstep (se 1 (by rfl) ⟨2321972, by rfl⟩ : syracuseStep 3095963 = 4643945) B4643945
theorem B2063975 : Blo 2063435 2063975 := bstep (se 1 (by rfl) ⟨1547981, by rfl⟩ : syracuseStep 2063975 = 3095963) B3095963
theorem B2321977 : Blo 2063435 2321977 := bbase (se 2 (by rfl) ⟨870741, by rfl⟩ : syracuseStep 2321977 = 1741483) (by norm_num)
theorem B3095969 : Blo 2063435 3095969 := bstep (se 2 (by rfl) ⟨1160988, by rfl⟩ : syracuseStep 3095969 = 2321977) B2321977
theorem B2063979 : Blo 2063435 2063979 := bstep (se 1 (by rfl) ⟨1547984, by rfl⟩ : syracuseStep 2063979 = 3095969) B3095969
theorem B2204069 : Blo 2063435 2204069 := bbase (se 4 (by rfl) ⟨206631, by rfl⟩ : syracuseStep 2204069 = 413263) (by norm_num)
theorem B5877517 : Blo 2063435 5877517 := bstep (se 3 (by rfl) ⟨1102034, by rfl⟩ : syracuseStep 5877517 = 2204069) B2204069
theorem B7836689 : Blo 2063435 7836689 := bstep (se 2 (by rfl) ⟨2938758, by rfl⟩ : syracuseStep 7836689 = 5877517) B5877517
theorem B5224459 : Blo 2063435 5224459 := bstep (se 1 (by rfl) ⟨3918344, by rfl⟩ : syracuseStep 5224459 = 7836689) B7836689
theorem B6965945 : Blo 2063435 6965945 := bstep (se 2 (by rfl) ⟨2612229, by rfl⟩ : syracuseStep 6965945 = 5224459) B5224459
theorem B4643963 : Blo 2063435 4643963 := bstep (se 1 (by rfl) ⟨3482972, by rfl⟩ : syracuseStep 4643963 = 6965945) B6965945
theorem B3095975 : Blo 2063435 3095975 := bstep (se 1 (by rfl) ⟨2321981, by rfl⟩ : syracuseStep 3095975 = 4643963) B4643963
theorem B2063983 : Blo 2063435 2063983 := bstep (se 1 (by rfl) ⟨1547987, by rfl⟩ : syracuseStep 2063983 = 3095975) B3095975
theorem B3095981 : Blo 2063435 3095981 := bbase (se 3 (by rfl) ⟨580496, by rfl⟩ : syracuseStep 3095981 = 1160993) (by norm_num)
theorem B2063987 : Blo 2063435 2063987 := bstep (se 1 (by rfl) ⟨1547990, by rfl⟩ : syracuseStep 2063987 = 3095981) B3095981
theorem B4643981 : Blo 2063435 4643981 := bbase (se 3 (by rfl) ⟨870746, by rfl⟩ : syracuseStep 4643981 = 1741493) (by norm_num)
theorem B3095987 : Blo 2063435 3095987 := bstep (se 1 (by rfl) ⟨2321990, by rfl⟩ : syracuseStep 3095987 = 4643981) B4643981
theorem B2063991 : Blo 2063435 2063991 := bstep (se 1 (by rfl) ⟨1547993, by rfl⟩ : syracuseStep 2063991 = 3095987) B3095987
theorem B2612245 : Blo 2063435 2612245 := bbase (se 6 (by rfl) ⟨61224, by rfl⟩ : syracuseStep 2612245 = 122449) (by norm_num)
theorem B3482993 : Blo 2063435 3482993 := bstep (se 2 (by rfl) ⟨1306122, by rfl⟩ : syracuseStep 3482993 = 2612245) B2612245
theorem B2321995 : Blo 2063435 2321995 := bstep (se 1 (by rfl) ⟨1741496, by rfl⟩ : syracuseStep 2321995 = 3482993) B3482993
theorem B3095993 : Blo 2063435 3095993 := bstep (se 2 (by rfl) ⟨1160997, by rfl⟩ : syracuseStep 3095993 = 2321995) B2321995
theorem B2063995 : Blo 2063435 2063995 := bstep (se 1 (by rfl) ⟨1547996, by rfl⟩ : syracuseStep 2063995 = 3095993) B3095993
theorem B11310421 : Blo 2063435 11310421 := bbase (se 14 (by rfl) ⟨1035, by rfl⟩ : syracuseStep 11310421 = 2071) (by norm_num)
theorem B15080561 : Blo 2063435 15080561 := bstep (se 2 (by rfl) ⟨5655210, by rfl⟩ : syracuseStep 15080561 = 11310421) B11310421
theorem B160859317 : Blo 2063435 160859317 := bstep (se 5 (by rfl) ⟨7540280, by rfl⟩ : syracuseStep 160859317 = 15080561) B15080561
theorem B214479089 : Blo 2063435 214479089 := bstep (se 2 (by rfl) ⟨80429658, by rfl⟩ : syracuseStep 214479089 = 160859317) B160859317
theorem B142986059 : Blo 2063435 142986059 := bstep (se 1 (by rfl) ⟨107239544, by rfl⟩ : syracuseStep 142986059 = 214479089) B214479089
theorem B95324039 : Blo 2063435 95324039 := bstep (se 1 (by rfl) ⟨71493029, by rfl⟩ : syracuseStep 95324039 = 142986059) B142986059
theorem B63549359 : Blo 2063435 63549359 := bstep (se 1 (by rfl) ⟨47662019, by rfl⟩ : syracuseStep 63549359 = 95324039) B95324039
theorem B42366239 : Blo 2063435 42366239 := bstep (se 1 (by rfl) ⟨31774679, by rfl⟩ : syracuseStep 42366239 = 63549359) B63549359
theorem B28244159 : Blo 2063435 28244159 := bstep (se 1 (by rfl) ⟨21183119, by rfl⟩ : syracuseStep 28244159 = 42366239) B42366239
theorem B18829439 : Blo 2063435 18829439 := bstep (se 1 (by rfl) ⟨14122079, by rfl⟩ : syracuseStep 18829439 = 28244159) B28244159
theorem B12552959 : Blo 2063435 12552959 := bstep (se 1 (by rfl) ⟨9414719, by rfl⟩ : syracuseStep 12552959 = 18829439) B18829439
theorem B8368639 : Blo 2063435 8368639 := bstep (se 1 (by rfl) ⟨6276479, by rfl⟩ : syracuseStep 8368639 = 12552959) B12552959
theorem B44632741 : Blo 2063435 44632741 := bstep (se 4 (by rfl) ⟨4184319, by rfl⟩ : syracuseStep 44632741 = 8368639) B8368639
theorem B59510321 : Blo 2063435 59510321 := bstep (se 2 (by rfl) ⟨22316370, by rfl⟩ : syracuseStep 59510321 = 44632741) B44632741
theorem B39673547 : Blo 2063435 39673547 := bstep (se 1 (by rfl) ⟨29755160, by rfl⟩ : syracuseStep 39673547 = 59510321) B59510321
theorem B26449031 : Blo 2063435 26449031 := bstep (se 1 (by rfl) ⟨19836773, by rfl⟩ : syracuseStep 26449031 = 39673547) B39673547
theorem B17632687 : Blo 2063435 17632687 := bstep (se 1 (by rfl) ⟨13224515, by rfl⟩ : syracuseStep 17632687 = 26449031) B26449031
theorem B23510249 : Blo 2063435 23510249 := bstep (se 2 (by rfl) ⟨8816343, by rfl⟩ : syracuseStep 23510249 = 17632687) B17632687
theorem B15673499 : Blo 2063435 15673499 := bstep (se 1 (by rfl) ⟨11755124, by rfl⟩ : syracuseStep 15673499 = 23510249) B23510249
theorem B10448999 : Blo 2063435 10448999 := bstep (se 1 (by rfl) ⟨7836749, by rfl⟩ : syracuseStep 10448999 = 15673499) B15673499
theorem B6965999 : Blo 2063435 6965999 := bstep (se 1 (by rfl) ⟨5224499, by rfl⟩ : syracuseStep 6965999 = 10448999) B10448999
theorem B4643999 : Blo 2063435 4643999 := bstep (se 1 (by rfl) ⟨3482999, by rfl⟩ : syracuseStep 4643999 = 6965999) B6965999
theorem B3095999 : Blo 2063435 3095999 := bstep (se 1 (by rfl) ⟨2321999, by rfl⟩ : syracuseStep 3095999 = 4643999) B4643999
theorem B2063999 : Blo 2063435 2063999 := bstep (se 1 (by rfl) ⟨1547999, by rfl⟩ : syracuseStep 2063999 = 3095999) B3095999
theorem B3096005 : Blo 2063435 3096005 := bbase (se 4 (by rfl) ⟨290250, by rfl⟩ : syracuseStep 3096005 = 580501) (by norm_num)
theorem B2064003 : Blo 2063435 2064003 := bstep (se 1 (by rfl) ⟨1548002, by rfl⟩ : syracuseStep 2064003 = 3096005) B3096005
theorem B3483013 : Blo 2063435 3483013 := bbase (se 4 (by rfl) ⟨326532, by rfl⟩ : syracuseStep 3483013 = 653065) (by norm_num)
theorem B4644017 : Blo 2063435 4644017 := bstep (se 2 (by rfl) ⟨1741506, by rfl⟩ : syracuseStep 4644017 = 3483013) B3483013
theorem B3096011 : Blo 2063435 3096011 := bstep (se 1 (by rfl) ⟨2322008, by rfl⟩ : syracuseStep 3096011 = 4644017) B4644017
theorem B2064007 : Blo 2063435 2064007 := bstep (se 1 (by rfl) ⟨1548005, by rfl⟩ : syracuseStep 2064007 = 3096011) B3096011
theorem B2322013 : Blo 2063435 2322013 := bbase (se 3 (by rfl) ⟨435377, by rfl⟩ : syracuseStep 2322013 = 870755) (by norm_num)
theorem B3096017 : Blo 2063435 3096017 := bstep (se 2 (by rfl) ⟨1161006, by rfl⟩ : syracuseStep 3096017 = 2322013) B2322013
theorem B2064011 : Blo 2063435 2064011 := bstep (se 1 (by rfl) ⟨1548008, by rfl⟩ : syracuseStep 2064011 = 3096017) B3096017
theorem B6966053 : Blo 2063435 6966053 := bbase (se 4 (by rfl) ⟨653067, by rfl⟩ : syracuseStep 6966053 = 1306135) (by norm_num)
theorem B4644035 : Blo 2063435 4644035 := bstep (se 1 (by rfl) ⟨3483026, by rfl⟩ : syracuseStep 4644035 = 6966053) B6966053
theorem B3096023 : Blo 2063435 3096023 := bstep (se 1 (by rfl) ⟨2322017, by rfl⟩ : syracuseStep 3096023 = 4644035) B4644035
theorem B2064015 : Blo 2063435 2064015 := bstep (se 1 (by rfl) ⟨1548011, by rfl⟩ : syracuseStep 2064015 = 3096023) B3096023
theorem B3096029 : Blo 2063435 3096029 := bbase (se 3 (by rfl) ⟨580505, by rfl⟩ : syracuseStep 3096029 = 1161011) (by norm_num)
theorem B2064019 : Blo 2063435 2064019 := bstep (se 1 (by rfl) ⟨1548014, by rfl⟩ : syracuseStep 2064019 = 3096029) B3096029
theorem B4644053 : Blo 2063435 4644053 := bbase (se 7 (by rfl) ⟨54422, by rfl⟩ : syracuseStep 4644053 = 108845) (by norm_num)
theorem B3096035 : Blo 2063435 3096035 := bstep (se 1 (by rfl) ⟨2322026, by rfl⟩ : syracuseStep 3096035 = 4644053) B4644053
theorem B2064023 : Blo 2063435 2064023 := bstep (se 1 (by rfl) ⟨1548017, by rfl⟩ : syracuseStep 2064023 = 3096035) B3096035
theorem B8368757 : Blo 2063435 8368757 := bbase (se 5 (by rfl) ⟨392285, by rfl⟩ : syracuseStep 8368757 = 784571) (by norm_num)
theorem B5579171 : Blo 2063435 5579171 := bstep (se 1 (by rfl) ⟨4184378, by rfl⟩ : syracuseStep 5579171 = 8368757) B8368757
theorem B3719447 : Blo 2063435 3719447 := bstep (se 1 (by rfl) ⟨2789585, by rfl⟩ : syracuseStep 3719447 = 5579171) B5579171
theorem B2479631 : Blo 2063435 2479631 := bstep (se 1 (by rfl) ⟨1859723, by rfl⟩ : syracuseStep 2479631 = 3719447) B3719447
theorem B6612349 : Blo 2063435 6612349 := bstep (se 3 (by rfl) ⟨1239815, by rfl⟩ : syracuseStep 6612349 = 2479631) B2479631
theorem B8816465 : Blo 2063435 8816465 := bstep (se 2 (by rfl) ⟨3306174, by rfl⟩ : syracuseStep 8816465 = 6612349) B6612349
theorem B5877643 : Blo 2063435 5877643 := bstep (se 1 (by rfl) ⟨4408232, by rfl⟩ : syracuseStep 5877643 = 8816465) B8816465
theorem B7836857 : Blo 2063435 7836857 := bstep (se 2 (by rfl) ⟨2938821, by rfl⟩ : syracuseStep 7836857 = 5877643) B5877643
theorem B5224571 : Blo 2063435 5224571 := bstep (se 1 (by rfl) ⟨3918428, by rfl⟩ : syracuseStep 5224571 = 7836857) B7836857
theorem B3483047 : Blo 2063435 3483047 := bstep (se 1 (by rfl) ⟨2612285, by rfl⟩ : syracuseStep 3483047 = 5224571) B5224571
theorem B2322031 : Blo 2063435 2322031 := bstep (se 1 (by rfl) ⟨1741523, by rfl⟩ : syracuseStep 2322031 = 3483047) B3483047
theorem B3096041 : Blo 2063435 3096041 := bstep (se 2 (by rfl) ⟨1161015, by rfl⟩ : syracuseStep 3096041 = 2322031) B2322031
theorem B2064027 : Blo 2063435 2064027 := bstep (se 1 (by rfl) ⟨1548020, by rfl⟩ : syracuseStep 2064027 = 3096041) B3096041
theorem B3719453 : Blo 2063435 3719453 := bbase (se 3 (by rfl) ⟨697397, by rfl⟩ : syracuseStep 3719453 = 1394795) (by norm_num)
theorem B9918541 : Blo 2063435 9918541 := bstep (se 3 (by rfl) ⟨1859726, by rfl⟩ : syracuseStep 9918541 = 3719453) B3719453
theorem B13224721 : Blo 2063435 13224721 := bstep (se 2 (by rfl) ⟨4959270, by rfl⟩ : syracuseStep 13224721 = 9918541) B9918541
theorem B17632961 : Blo 2063435 17632961 := bstep (se 2 (by rfl) ⟨6612360, by rfl⟩ : syracuseStep 17632961 = 13224721) B13224721
theorem B11755307 : Blo 2063435 11755307 := bstep (se 1 (by rfl) ⟨8816480, by rfl⟩ : syracuseStep 11755307 = 17632961) B17632961
theorem B7836871 : Blo 2063435 7836871 := bstep (se 1 (by rfl) ⟨5877653, by rfl⟩ : syracuseStep 7836871 = 11755307) B11755307
theorem B10449161 : Blo 2063435 10449161 := bstep (se 2 (by rfl) ⟨3918435, by rfl⟩ : syracuseStep 10449161 = 7836871) B7836871
theorem B6966107 : Blo 2063435 6966107 := bstep (se 1 (by rfl) ⟨5224580, by rfl⟩ : syracuseStep 6966107 = 10449161) B10449161
theorem B4644071 : Blo 2063435 4644071 := bstep (se 1 (by rfl) ⟨3483053, by rfl⟩ : syracuseStep 4644071 = 6966107) B6966107
theorem B3096047 : Blo 2063435 3096047 := bstep (se 1 (by rfl) ⟨2322035, by rfl⟩ : syracuseStep 3096047 = 4644071) B4644071
theorem B2064031 : Blo 2063435 2064031 := bstep (se 1 (by rfl) ⟨1548023, by rfl⟩ : syracuseStep 2064031 = 3096047) B3096047
theorem B3096053 : Blo 2063435 3096053 := bbase (se 5 (by rfl) ⟨145127, by rfl⟩ : syracuseStep 3096053 = 290255) (by norm_num)
theorem B2064035 : Blo 2063435 2064035 := bstep (se 1 (by rfl) ⟨1548026, by rfl⟩ : syracuseStep 2064035 = 3096053) B3096053
theorem B2204129 : Blo 2063435 2204129 := bbase (se 2 (by rfl) ⟨826548, by rfl⟩ : syracuseStep 2204129 = 1653097) (by norm_num)
theorem B5877677 : Blo 2063435 5877677 := bstep (se 3 (by rfl) ⟨1102064, by rfl⟩ : syracuseStep 5877677 = 2204129) B2204129
theorem B3918451 : Blo 2063435 3918451 := bstep (se 1 (by rfl) ⟨2938838, by rfl⟩ : syracuseStep 3918451 = 5877677) B5877677
theorem B5224601 : Blo 2063435 5224601 := bstep (se 2 (by rfl) ⟨1959225, by rfl⟩ : syracuseStep 5224601 = 3918451) B3918451
theorem B3483067 : Blo 2063435 3483067 := bstep (se 1 (by rfl) ⟨2612300, by rfl⟩ : syracuseStep 3483067 = 5224601) B5224601
theorem B4644089 : Blo 2063435 4644089 := bstep (se 2 (by rfl) ⟨1741533, by rfl⟩ : syracuseStep 4644089 = 3483067) B3483067
theorem B3096059 : Blo 2063435 3096059 := bstep (se 1 (by rfl) ⟨2322044, by rfl⟩ : syracuseStep 3096059 = 4644089) B4644089
theorem B2064039 : Blo 2063435 2064039 := bstep (se 1 (by rfl) ⟨1548029, by rfl⟩ : syracuseStep 2064039 = 3096059) B3096059
theorem B2322049 : Blo 2063435 2322049 := bbase (se 2 (by rfl) ⟨870768, by rfl⟩ : syracuseStep 2322049 = 1741537) (by norm_num)
theorem B3096065 : Blo 2063435 3096065 := bstep (se 2 (by rfl) ⟨1161024, by rfl⟩ : syracuseStep 3096065 = 2322049) B2322049
theorem B2064043 : Blo 2063435 2064043 := bstep (se 1 (by rfl) ⟨1548032, by rfl⟩ : syracuseStep 2064043 = 3096065) B3096065
theorem B5224621 : Blo 2063435 5224621 := bbase (se 3 (by rfl) ⟨979616, by rfl⟩ : syracuseStep 5224621 = 1959233) (by norm_num)
theorem B6966161 : Blo 2063435 6966161 := bstep (se 2 (by rfl) ⟨2612310, by rfl⟩ : syracuseStep 6966161 = 5224621) B5224621
theorem B4644107 : Blo 2063435 4644107 := bstep (se 1 (by rfl) ⟨3483080, by rfl⟩ : syracuseStep 4644107 = 6966161) B6966161
theorem B3096071 : Blo 2063435 3096071 := bstep (se 1 (by rfl) ⟨2322053, by rfl⟩ : syracuseStep 3096071 = 4644107) B4644107
theorem B2064047 : Blo 2063435 2064047 := bstep (se 1 (by rfl) ⟨1548035, by rfl⟩ : syracuseStep 2064047 = 3096071) B3096071
theorem B3096077 : Blo 2063435 3096077 := bbase (se 3 (by rfl) ⟨580514, by rfl⟩ : syracuseStep 3096077 = 1161029) (by norm_num)
theorem B2064051 : Blo 2063435 2064051 := bstep (se 1 (by rfl) ⟨1548038, by rfl⟩ : syracuseStep 2064051 = 3096077) B3096077
theorem B4644125 : Blo 2063435 4644125 := bbase (se 3 (by rfl) ⟨870773, by rfl⟩ : syracuseStep 4644125 = 1741547) (by norm_num)
theorem B3096083 : Blo 2063435 3096083 := bstep (se 1 (by rfl) ⟨2322062, by rfl⟩ : syracuseStep 3096083 = 4644125) B4644125
theorem B2064055 : Blo 2063435 2064055 := bstep (se 1 (by rfl) ⟨1548041, by rfl⟩ : syracuseStep 2064055 = 3096083) B3096083
theorem B3483101 : Blo 2063435 3483101 := bbase (se 3 (by rfl) ⟨653081, by rfl⟩ : syracuseStep 3483101 = 1306163) (by norm_num)
theorem B2322067 : Blo 2063435 2322067 := bstep (se 1 (by rfl) ⟨1741550, by rfl⟩ : syracuseStep 2322067 = 3483101) B3483101
theorem B3096089 : Blo 2063435 3096089 := bstep (se 2 (by rfl) ⟨1161033, by rfl⟩ : syracuseStep 3096089 = 2322067) B2322067
theorem B2064059 : Blo 2063435 2064059 := bstep (se 1 (by rfl) ⟨1548044, by rfl⟩ : syracuseStep 2064059 = 3096089) B3096089
theorem B3351341 : Blo 2063435 3351341 := bbase (se 3 (by rfl) ⟨628376, by rfl⟩ : syracuseStep 3351341 = 1256753) (by norm_num)
theorem B2234227 : Blo 2063435 2234227 := bstep (se 1 (by rfl) ⟨1675670, by rfl⟩ : syracuseStep 2234227 = 3351341) B3351341
theorem B2978969 : Blo 2063435 2978969 := bstep (se 2 (by rfl) ⟨1117113, by rfl⟩ : syracuseStep 2978969 = 2234227) B2234227
theorem B7943917 : Blo 2063435 7943917 := bstep (se 3 (by rfl) ⟨1489484, by rfl⟩ : syracuseStep 7943917 = 2978969) B2978969
theorem B10591889 : Blo 2063435 10591889 := bstep (se 2 (by rfl) ⟨3971958, by rfl⟩ : syracuseStep 10591889 = 7943917) B7943917
theorem B28245037 : Blo 2063435 28245037 := bstep (se 3 (by rfl) ⟨5295944, by rfl⟩ : syracuseStep 28245037 = 10591889) B10591889
theorem B37660049 : Blo 2063435 37660049 := bstep (se 2 (by rfl) ⟨14122518, by rfl⟩ : syracuseStep 37660049 = 28245037) B28245037
theorem B25106699 : Blo 2063435 25106699 := bstep (se 1 (by rfl) ⟨18830024, by rfl⟩ : syracuseStep 25106699 = 37660049) B37660049
theorem B16737799 : Blo 2063435 16737799 := bstep (se 1 (by rfl) ⟨12553349, by rfl⟩ : syracuseStep 16737799 = 25106699) B25106699
theorem B22317065 : Blo 2063435 22317065 := bstep (se 2 (by rfl) ⟨8368899, by rfl⟩ : syracuseStep 22317065 = 16737799) B16737799
theorem B14878043 : Blo 2063435 14878043 := bstep (se 1 (by rfl) ⟨11158532, by rfl⟩ : syracuseStep 14878043 = 22317065) B22317065
theorem B9918695 : Blo 2063435 9918695 := bstep (se 1 (by rfl) ⟨7439021, by rfl⟩ : syracuseStep 9918695 = 14878043) B14878043
theorem B6612463 : Blo 2063435 6612463 := bstep (se 1 (by rfl) ⟨4959347, by rfl⟩ : syracuseStep 6612463 = 9918695) B9918695
theorem B8816617 : Blo 2063435 8816617 := bstep (se 2 (by rfl) ⟨3306231, by rfl⟩ : syracuseStep 8816617 = 6612463) B6612463
theorem B11755489 : Blo 2063435 11755489 := bstep (se 2 (by rfl) ⟨4408308, by rfl⟩ : syracuseStep 11755489 = 8816617) B8816617
theorem B15673985 : Blo 2063435 15673985 := bstep (se 2 (by rfl) ⟨5877744, by rfl⟩ : syracuseStep 15673985 = 11755489) B11755489
theorem B10449323 : Blo 2063435 10449323 := bstep (se 1 (by rfl) ⟨7836992, by rfl⟩ : syracuseStep 10449323 = 15673985) B15673985
theorem B6966215 : Blo 2063435 6966215 := bstep (se 1 (by rfl) ⟨5224661, by rfl⟩ : syracuseStep 6966215 = 10449323) B10449323
theorem B4644143 : Blo 2063435 4644143 := bstep (se 1 (by rfl) ⟨3483107, by rfl⟩ : syracuseStep 4644143 = 6966215) B6966215
theorem B3096095 : Blo 2063435 3096095 := bstep (se 1 (by rfl) ⟨2322071, by rfl⟩ : syracuseStep 3096095 = 4644143) B4644143
theorem B2064063 : Blo 2063435 2064063 := bstep (se 1 (by rfl) ⟨1548047, by rfl⟩ : syracuseStep 2064063 = 3096095) B3096095
theorem B3096101 : Blo 2063435 3096101 := bbase (se 4 (by rfl) ⟨290259, by rfl⟩ : syracuseStep 3096101 = 580519) (by norm_num)
theorem B2064067 : Blo 2063435 2064067 := bstep (se 1 (by rfl) ⟨1548050, by rfl⟩ : syracuseStep 2064067 = 3096101) B3096101
theorem B2612341 : Blo 2063435 2612341 := bbase (se 5 (by rfl) ⟨122453, by rfl⟩ : syracuseStep 2612341 = 244907) (by norm_num)
theorem B3483121 : Blo 2063435 3483121 := bstep (se 2 (by rfl) ⟨1306170, by rfl⟩ : syracuseStep 3483121 = 2612341) B2612341
theorem B4644161 : Blo 2063435 4644161 := bstep (se 2 (by rfl) ⟨1741560, by rfl⟩ : syracuseStep 4644161 = 3483121) B3483121
theorem B3096107 : Blo 2063435 3096107 := bstep (se 1 (by rfl) ⟨2322080, by rfl⟩ : syracuseStep 3096107 = 4644161) B4644161
theorem B2064071 : Blo 2063435 2064071 := bstep (se 1 (by rfl) ⟨1548053, by rfl⟩ : syracuseStep 2064071 = 3096107) B3096107
theorem B2322085 : Blo 2063435 2322085 := bbase (se 4 (by rfl) ⟨217695, by rfl⟩ : syracuseStep 2322085 = 435391) (by norm_num)
theorem B3096113 : Blo 2063435 3096113 := bstep (se 2 (by rfl) ⟨1161042, by rfl⟩ : syracuseStep 3096113 = 2322085) B2322085
theorem B2064075 : Blo 2063435 2064075 := bstep (se 1 (by rfl) ⟨1548056, by rfl⟩ : syracuseStep 2064075 = 3096113) B3096113
theorem B10591973 : Blo 2063435 10591973 := bbase (se 4 (by rfl) ⟨992997, by rfl⟩ : syracuseStep 10591973 = 1985995) (by norm_num)
theorem B7061315 : Blo 2063435 7061315 := bstep (se 1 (by rfl) ⟨5295986, by rfl⟩ : syracuseStep 7061315 = 10591973) B10591973
theorem B18830173 : Blo 2063435 18830173 := bstep (se 3 (by rfl) ⟨3530657, by rfl⟩ : syracuseStep 18830173 = 7061315) B7061315
theorem B25106897 : Blo 2063435 25106897 := bstep (se 2 (by rfl) ⟨9415086, by rfl⟩ : syracuseStep 25106897 = 18830173) B18830173
theorem B16737931 : Blo 2063435 16737931 := bstep (se 1 (by rfl) ⟨12553448, by rfl⟩ : syracuseStep 16737931 = 25106897) B25106897
theorem B22317241 : Blo 2063435 22317241 := bstep (se 2 (by rfl) ⟨8368965, by rfl⟩ : syracuseStep 22317241 = 16737931) B16737931
theorem B29756321 : Blo 2063435 29756321 := bstep (se 2 (by rfl) ⟨11158620, by rfl⟩ : syracuseStep 29756321 = 22317241) B22317241
theorem B19837547 : Blo 2063435 19837547 := bstep (se 1 (by rfl) ⟨14878160, by rfl⟩ : syracuseStep 19837547 = 29756321) B29756321
theorem B13225031 : Blo 2063435 13225031 := bstep (se 1 (by rfl) ⟨9918773, by rfl⟩ : syracuseStep 13225031 = 19837547) B19837547
theorem B8816687 : Blo 2063435 8816687 := bstep (se 1 (by rfl) ⟨6612515, by rfl⟩ : syracuseStep 8816687 = 13225031) B13225031
theorem B5877791 : Blo 2063435 5877791 := bstep (se 1 (by rfl) ⟨4408343, by rfl⟩ : syracuseStep 5877791 = 8816687) B8816687
theorem B3918527 : Blo 2063435 3918527 := bstep (se 1 (by rfl) ⟨2938895, by rfl⟩ : syracuseStep 3918527 = 5877791) B5877791
theorem B2612351 : Blo 2063435 2612351 := bstep (se 1 (by rfl) ⟨1959263, by rfl⟩ : syracuseStep 2612351 = 3918527) B3918527
theorem B6966269 : Blo 2063435 6966269 := bstep (se 3 (by rfl) ⟨1306175, by rfl⟩ : syracuseStep 6966269 = 2612351) B2612351
theorem B4644179 : Blo 2063435 4644179 := bstep (se 1 (by rfl) ⟨3483134, by rfl⟩ : syracuseStep 4644179 = 6966269) B6966269
theorem B3096119 : Blo 2063435 3096119 := bstep (se 1 (by rfl) ⟨2322089, by rfl⟩ : syracuseStep 3096119 = 4644179) B4644179
theorem B2064079 : Blo 2063435 2064079 := bstep (se 1 (by rfl) ⟨1548059, by rfl⟩ : syracuseStep 2064079 = 3096119) B3096119
theorem B3096125 : Blo 2063435 3096125 := bbase (se 3 (by rfl) ⟨580523, by rfl⟩ : syracuseStep 3096125 = 1161047) (by norm_num)
theorem B2064083 : Blo 2063435 2064083 := bstep (se 1 (by rfl) ⟨1548062, by rfl⟩ : syracuseStep 2064083 = 3096125) B3096125
theorem B4644197 : Blo 2063435 4644197 := bbase (se 4 (by rfl) ⟨435393, by rfl⟩ : syracuseStep 4644197 = 870787) (by norm_num)
theorem B3096131 : Blo 2063435 3096131 := bstep (se 1 (by rfl) ⟨2322098, by rfl⟩ : syracuseStep 3096131 = 4644197) B4644197
theorem B2064087 : Blo 2063435 2064087 := bstep (se 1 (by rfl) ⟨1548065, by rfl⟩ : syracuseStep 2064087 = 3096131) B3096131
theorem B5224733 : Blo 2063435 5224733 := bbase (se 3 (by rfl) ⟨979637, by rfl⟩ : syracuseStep 5224733 = 1959275) (by norm_num)
theorem B3483155 : Blo 2063435 3483155 := bstep (se 1 (by rfl) ⟨2612366, by rfl⟩ : syracuseStep 3483155 = 5224733) B5224733
theorem B2322103 : Blo 2063435 2322103 := bstep (se 1 (by rfl) ⟨1741577, by rfl⟩ : syracuseStep 2322103 = 3483155) B3483155
theorem B3096137 : Blo 2063435 3096137 := bstep (se 2 (by rfl) ⟨1161051, by rfl⟩ : syracuseStep 3096137 = 2322103) B2322103
theorem B2064091 : Blo 2063435 2064091 := bstep (se 1 (by rfl) ⟨1548068, by rfl⟩ : syracuseStep 2064091 = 3096137) B3096137
theorem B3918557 : Blo 2063435 3918557 := bbase (se 3 (by rfl) ⟨734729, by rfl⟩ : syracuseStep 3918557 = 1469459) (by norm_num)
theorem B10449485 : Blo 2063435 10449485 := bstep (se 3 (by rfl) ⟨1959278, by rfl⟩ : syracuseStep 10449485 = 3918557) B3918557
theorem B6966323 : Blo 2063435 6966323 := bstep (se 1 (by rfl) ⟨5224742, by rfl⟩ : syracuseStep 6966323 = 10449485) B10449485
theorem B4644215 : Blo 2063435 4644215 := bstep (se 1 (by rfl) ⟨3483161, by rfl⟩ : syracuseStep 4644215 = 6966323) B6966323
theorem B3096143 : Blo 2063435 3096143 := bstep (se 1 (by rfl) ⟨2322107, by rfl⟩ : syracuseStep 3096143 = 4644215) B4644215
theorem B2064095 : Blo 2063435 2064095 := bstep (se 1 (by rfl) ⟨1548071, by rfl⟩ : syracuseStep 2064095 = 3096143) B3096143
theorem B3096149 : Blo 2063435 3096149 := bbase (se 8 (by rfl) ⟨18141, by rfl⟩ : syracuseStep 3096149 = 36283) (by norm_num)
theorem B2064099 : Blo 2063435 2064099 := bstep (se 1 (by rfl) ⟨1548074, by rfl⟩ : syracuseStep 2064099 = 3096149) B3096149
theorem B8816789 : Blo 2063435 8816789 := bbase (se 6 (by rfl) ⟨206643, by rfl⟩ : syracuseStep 8816789 = 413287) (by norm_num)
theorem B5877859 : Blo 2063435 5877859 := bstep (se 1 (by rfl) ⟨4408394, by rfl⟩ : syracuseStep 5877859 = 8816789) B8816789
theorem B7837145 : Blo 2063435 7837145 := bstep (se 2 (by rfl) ⟨2938929, by rfl⟩ : syracuseStep 7837145 = 5877859) B5877859
theorem B5224763 : Blo 2063435 5224763 := bstep (se 1 (by rfl) ⟨3918572, by rfl⟩ : syracuseStep 5224763 = 7837145) B7837145
theorem B3483175 : Blo 2063435 3483175 := bstep (se 1 (by rfl) ⟨2612381, by rfl⟩ : syracuseStep 3483175 = 5224763) B5224763
theorem B4644233 : Blo 2063435 4644233 := bstep (se 2 (by rfl) ⟨1741587, by rfl⟩ : syracuseStep 4644233 = 3483175) B3483175
theorem B3096155 : Blo 2063435 3096155 := bstep (se 1 (by rfl) ⟨2322116, by rfl⟩ : syracuseStep 3096155 = 4644233) B4644233
theorem B2064103 : Blo 2063435 2064103 := bstep (se 1 (by rfl) ⟨1548077, by rfl⟩ : syracuseStep 2064103 = 3096155) B3096155
theorem B2322121 : Blo 2063435 2322121 := bbase (se 2 (by rfl) ⟨870795, by rfl⟩ : syracuseStep 2322121 = 1741591) (by norm_num)
theorem B3096161 : Blo 2063435 3096161 := bstep (se 2 (by rfl) ⟨1161060, by rfl⟩ : syracuseStep 3096161 = 2322121) B2322121
theorem B2064107 : Blo 2063435 2064107 := bstep (se 1 (by rfl) ⟨1548080, by rfl⟩ : syracuseStep 2064107 = 3096161) B3096161
theorem B19347797 : Blo 2063435 19347797 := bbase (se 10 (by rfl) ⟨28341, by rfl⟩ : syracuseStep 19347797 = 56683) (by norm_num)
theorem B12898531 : Blo 2063435 12898531 := bstep (se 1 (by rfl) ⟨9673898, by rfl⟩ : syracuseStep 12898531 = 19347797) B19347797
theorem B17198041 : Blo 2063435 17198041 := bstep (se 2 (by rfl) ⟨6449265, by rfl⟩ : syracuseStep 17198041 = 12898531) B12898531
theorem B22930721 : Blo 2063435 22930721 := bstep (se 2 (by rfl) ⟨8599020, by rfl⟩ : syracuseStep 22930721 = 17198041) B17198041
theorem B15287147 : Blo 2063435 15287147 := bstep (se 1 (by rfl) ⟨11465360, by rfl⟩ : syracuseStep 15287147 = 22930721) B22930721
theorem B10191431 : Blo 2063435 10191431 := bstep (se 1 (by rfl) ⟨7643573, by rfl⟩ : syracuseStep 10191431 = 15287147) B15287147
theorem B27177149 : Blo 2063435 27177149 := bstep (se 3 (by rfl) ⟨5095715, by rfl⟩ : syracuseStep 27177149 = 10191431) B10191431
theorem B18118099 : Blo 2063435 18118099 := bstep (se 1 (by rfl) ⟨13588574, by rfl⟩ : syracuseStep 18118099 = 27177149) B27177149
theorem B96629861 : Blo 2063435 96629861 := bstep (se 4 (by rfl) ⟨9059049, by rfl⟩ : syracuseStep 96629861 = 18118099) B18118099
theorem B64419907 : Blo 2063435 64419907 := bstep (se 1 (by rfl) ⟨48314930, by rfl⟩ : syracuseStep 64419907 = 96629861) B96629861
theorem B85893209 : Blo 2063435 85893209 := bstep (se 2 (by rfl) ⟨32209953, by rfl⟩ : syracuseStep 85893209 = 64419907) B64419907
theorem B57262139 : Blo 2063435 57262139 := bstep (se 1 (by rfl) ⟨42946604, by rfl⟩ : syracuseStep 57262139 = 85893209) B85893209
theorem B38174759 : Blo 2063435 38174759 := bstep (se 1 (by rfl) ⟨28631069, by rfl⟩ : syracuseStep 38174759 = 57262139) B57262139
theorem B25449839 : Blo 2063435 25449839 := bstep (se 1 (by rfl) ⟨19087379, by rfl⟩ : syracuseStep 25449839 = 38174759) B38174759
theorem B16966559 : Blo 2063435 16966559 := bstep (se 1 (by rfl) ⟨12724919, by rfl⟩ : syracuseStep 16966559 = 25449839) B25449839
theorem B11311039 : Blo 2063435 11311039 := bstep (se 1 (by rfl) ⟨8483279, by rfl⟩ : syracuseStep 11311039 = 16966559) B16966559
theorem B15081385 : Blo 2063435 15081385 := bstep (se 2 (by rfl) ⟨5655519, by rfl⟩ : syracuseStep 15081385 = 11311039) B11311039
theorem B20108513 : Blo 2063435 20108513 := bstep (se 2 (by rfl) ⟨7540692, by rfl⟩ : syracuseStep 20108513 = 15081385) B15081385
theorem B13405675 : Blo 2063435 13405675 := bstep (se 1 (by rfl) ⟨10054256, by rfl⟩ : syracuseStep 13405675 = 20108513) B20108513
theorem B17874233 : Blo 2063435 17874233 := bstep (se 2 (by rfl) ⟨6702837, by rfl⟩ : syracuseStep 17874233 = 13405675) B13405675
theorem B11916155 : Blo 2063435 11916155 := bstep (se 1 (by rfl) ⟨8937116, by rfl⟩ : syracuseStep 11916155 = 17874233) B17874233
theorem B7944103 : Blo 2063435 7944103 := bstep (se 1 (by rfl) ⟨5958077, by rfl⟩ : syracuseStep 7944103 = 11916155) B11916155
theorem B10592137 : Blo 2063435 10592137 := bstep (se 2 (by rfl) ⟨3972051, by rfl⟩ : syracuseStep 10592137 = 7944103) B7944103
theorem B14122849 : Blo 2063435 14122849 := bstep (se 2 (by rfl) ⟨5296068, by rfl⟩ : syracuseStep 14122849 = 10592137) B10592137
theorem B18830465 : Blo 2063435 18830465 := bstep (se 2 (by rfl) ⟨7061424, by rfl⟩ : syracuseStep 18830465 = 14122849) B14122849
theorem B12553643 : Blo 2063435 12553643 := bstep (se 1 (by rfl) ⟨9415232, by rfl⟩ : syracuseStep 12553643 = 18830465) B18830465
theorem B8369095 : Blo 2063435 8369095 := bstep (se 1 (by rfl) ⟨6276821, by rfl⟩ : syracuseStep 8369095 = 12553643) B12553643
theorem B11158793 : Blo 2063435 11158793 := bstep (se 2 (by rfl) ⟨4184547, by rfl⟩ : syracuseStep 11158793 = 8369095) B8369095
theorem B7439195 : Blo 2063435 7439195 := bstep (se 1 (by rfl) ⟨5579396, by rfl⟩ : syracuseStep 7439195 = 11158793) B11158793
theorem B4959463 : Blo 2063435 4959463 := bstep (se 1 (by rfl) ⟨3719597, by rfl⟩ : syracuseStep 4959463 = 7439195) B7439195
theorem B6612617 : Blo 2063435 6612617 := bstep (se 2 (by rfl) ⟨2479731, by rfl⟩ : syracuseStep 6612617 = 4959463) B4959463
theorem B17633645 : Blo 2063435 17633645 := bstep (se 3 (by rfl) ⟨3306308, by rfl⟩ : syracuseStep 17633645 = 6612617) B6612617
theorem B11755763 : Blo 2063435 11755763 := bstep (se 1 (by rfl) ⟨8816822, by rfl⟩ : syracuseStep 11755763 = 17633645) B17633645
theorem B7837175 : Blo 2063435 7837175 := bstep (se 1 (by rfl) ⟨5877881, by rfl⟩ : syracuseStep 7837175 = 11755763) B11755763
theorem B5224783 : Blo 2063435 5224783 := bstep (se 1 (by rfl) ⟨3918587, by rfl⟩ : syracuseStep 5224783 = 7837175) B7837175
theorem B6966377 : Blo 2063435 6966377 := bstep (se 2 (by rfl) ⟨2612391, by rfl⟩ : syracuseStep 6966377 = 5224783) B5224783
theorem B4644251 : Blo 2063435 4644251 := bstep (se 1 (by rfl) ⟨3483188, by rfl⟩ : syracuseStep 4644251 = 6966377) B6966377
theorem B3096167 : Blo 2063435 3096167 := bstep (se 1 (by rfl) ⟨2322125, by rfl⟩ : syracuseStep 3096167 = 4644251) B4644251
theorem B2064111 : Blo 2063435 2064111 := bstep (se 1 (by rfl) ⟨1548083, by rfl⟩ : syracuseStep 2064111 = 3096167) B3096167
theorem B3096173 : Blo 2063435 3096173 := bbase (se 3 (by rfl) ⟨580532, by rfl⟩ : syracuseStep 3096173 = 1161065) (by norm_num)
theorem B2064115 : Blo 2063435 2064115 := bstep (se 1 (by rfl) ⟨1548086, by rfl⟩ : syracuseStep 2064115 = 3096173) B3096173
theorem B4644269 : Blo 2063435 4644269 := bbase (se 3 (by rfl) ⟨870800, by rfl⟩ : syracuseStep 4644269 = 1741601) (by norm_num)
theorem B3096179 : Blo 2063435 3096179 := bstep (se 1 (by rfl) ⟨2322134, by rfl⟩ : syracuseStep 3096179 = 4644269) B4644269
theorem B2064119 : Blo 2063435 2064119 := bstep (se 1 (by rfl) ⟨1548089, by rfl⟩ : syracuseStep 2064119 = 3096179) B3096179
theorem B3719621 : Blo 2063435 3719621 := bbase (se 4 (by rfl) ⟨348714, by rfl⟩ : syracuseStep 3719621 = 697429) (by norm_num)
theorem B2479747 : Blo 2063435 2479747 := bstep (se 1 (by rfl) ⟨1859810, by rfl⟩ : syracuseStep 2479747 = 3719621) B3719621
theorem B3306329 : Blo 2063435 3306329 := bstep (se 2 (by rfl) ⟨1239873, by rfl⟩ : syracuseStep 3306329 = 2479747) B2479747
theorem B2204219 : Blo 2063435 2204219 := bstep (se 1 (by rfl) ⟨1653164, by rfl⟩ : syracuseStep 2204219 = 3306329) B3306329
theorem B5877917 : Blo 2063435 5877917 := bstep (se 3 (by rfl) ⟨1102109, by rfl⟩ : syracuseStep 5877917 = 2204219) B2204219
theorem B3918611 : Blo 2063435 3918611 := bstep (se 1 (by rfl) ⟨2938958, by rfl⟩ : syracuseStep 3918611 = 5877917) B5877917
theorem B2612407 : Blo 2063435 2612407 := bstep (se 1 (by rfl) ⟨1959305, by rfl⟩ : syracuseStep 2612407 = 3918611) B3918611
theorem B3483209 : Blo 2063435 3483209 := bstep (se 2 (by rfl) ⟨1306203, by rfl⟩ : syracuseStep 3483209 = 2612407) B2612407
theorem B2322139 : Blo 2063435 2322139 := bstep (se 1 (by rfl) ⟨1741604, by rfl⟩ : syracuseStep 2322139 = 3483209) B3483209
theorem B3096185 : Blo 2063435 3096185 := bstep (se 2 (by rfl) ⟨1161069, by rfl⟩ : syracuseStep 3096185 = 2322139) B2322139
theorem B2064123 : Blo 2063435 2064123 := bstep (se 1 (by rfl) ⟨1548092, by rfl⟩ : syracuseStep 2064123 = 3096185) B3096185
theorem B4299541 : Blo 2063435 4299541 := bbase (se 6 (by rfl) ⟨100770, by rfl⟩ : syracuseStep 4299541 = 201541) (by norm_num)
theorem B22930885 : Blo 2063435 22930885 := bstep (se 4 (by rfl) ⟨2149770, by rfl⟩ : syracuseStep 22930885 = 4299541) B4299541
theorem B30574513 : Blo 2063435 30574513 := bstep (se 2 (by rfl) ⟨11465442, by rfl⟩ : syracuseStep 30574513 = 22930885) B22930885
theorem B40766017 : Blo 2063435 40766017 := bstep (se 2 (by rfl) ⟨15287256, by rfl⟩ : syracuseStep 40766017 = 30574513) B30574513
theorem B54354689 : Blo 2063435 54354689 := bstep (se 2 (by rfl) ⟨20383008, by rfl⟩ : syracuseStep 54354689 = 40766017) B40766017
theorem B36236459 : Blo 2063435 36236459 := bstep (se 1 (by rfl) ⟨27177344, by rfl⟩ : syracuseStep 36236459 = 54354689) B54354689
theorem B24157639 : Blo 2063435 24157639 := bstep (se 1 (by rfl) ⟨18118229, by rfl⟩ : syracuseStep 24157639 = 36236459) B36236459
theorem B32210185 : Blo 2063435 32210185 := bstep (se 2 (by rfl) ⟨12078819, by rfl⟩ : syracuseStep 32210185 = 24157639) B24157639
theorem B42946913 : Blo 2063435 42946913 := bstep (se 2 (by rfl) ⟨16105092, by rfl⟩ : syracuseStep 42946913 = 32210185) B32210185
theorem B28631275 : Blo 2063435 28631275 := bstep (se 1 (by rfl) ⟨21473456, by rfl⟩ : syracuseStep 28631275 = 42946913) B42946913
theorem B610800533 : Blo 2063435 610800533 := bstep (se 6 (by rfl) ⟨14315637, by rfl⟩ : syracuseStep 610800533 = 28631275) B28631275
theorem B407200355 : Blo 2063435 407200355 := bstep (se 1 (by rfl) ⟨305400266, by rfl⟩ : syracuseStep 407200355 = 610800533) B610800533
theorem B271466903 : Blo 2063435 271466903 := bstep (se 1 (by rfl) ⟨203600177, by rfl⟩ : syracuseStep 271466903 = 407200355) B407200355
theorem B723911741 : Blo 2063435 723911741 := bstep (se 3 (by rfl) ⟨135733451, by rfl⟩ : syracuseStep 723911741 = 271466903) B271466903
theorem B482607827 : Blo 2063435 482607827 := bstep (se 1 (by rfl) ⟨361955870, by rfl⟩ : syracuseStep 482607827 = 723911741) B723911741
theorem B321738551 : Blo 2063435 321738551 := bstep (se 1 (by rfl) ⟨241303913, by rfl⟩ : syracuseStep 321738551 = 482607827) B482607827
theorem B214492367 : Blo 2063435 214492367 := bstep (se 1 (by rfl) ⟨160869275, by rfl⟩ : syracuseStep 214492367 = 321738551) B321738551
theorem B142994911 : Blo 2063435 142994911 := bstep (se 1 (by rfl) ⟨107246183, by rfl⟩ : syracuseStep 142994911 = 214492367) B214492367
theorem B190659881 : Blo 2063435 190659881 := bstep (se 2 (by rfl) ⟨71497455, by rfl⟩ : syracuseStep 190659881 = 142994911) B142994911
theorem B127106587 : Blo 2063435 127106587 := bstep (se 1 (by rfl) ⟨95329940, by rfl⟩ : syracuseStep 127106587 = 190659881) B190659881
theorem B169475449 : Blo 2063435 169475449 := bstep (se 2 (by rfl) ⟨63553293, by rfl⟩ : syracuseStep 169475449 = 127106587) B127106587
theorem B225967265 : Blo 2063435 225967265 := bstep (se 2 (by rfl) ⟨84737724, by rfl⟩ : syracuseStep 225967265 = 169475449) B169475449
theorem B150644843 : Blo 2063435 150644843 := bstep (se 1 (by rfl) ⟨112983632, by rfl⟩ : syracuseStep 150644843 = 225967265) B225967265
theorem B100429895 : Blo 2063435 100429895 := bstep (se 1 (by rfl) ⟨75322421, by rfl⟩ : syracuseStep 100429895 = 150644843) B150644843
theorem B66953263 : Blo 2063435 66953263 := bstep (se 1 (by rfl) ⟨50214947, by rfl⟩ : syracuseStep 66953263 = 100429895) B100429895
theorem B89271017 : Blo 2063435 89271017 := bstep (se 2 (by rfl) ⟨33476631, by rfl⟩ : syracuseStep 89271017 = 66953263) B66953263
theorem B59514011 : Blo 2063435 59514011 := bstep (se 1 (by rfl) ⟨44635508, by rfl⟩ : syracuseStep 59514011 = 89271017) B89271017
theorem B39676007 : Blo 2063435 39676007 := bstep (se 1 (by rfl) ⟨29757005, by rfl⟩ : syracuseStep 39676007 = 59514011) B59514011
theorem B26450671 : Blo 2063435 26450671 := bstep (se 1 (by rfl) ⟨19838003, by rfl⟩ : syracuseStep 26450671 = 39676007) B39676007
theorem B35267561 : Blo 2063435 35267561 := bstep (se 2 (by rfl) ⟨13225335, by rfl⟩ : syracuseStep 35267561 = 26450671) B26450671
theorem B23511707 : Blo 2063435 23511707 := bstep (se 1 (by rfl) ⟨17633780, by rfl⟩ : syracuseStep 23511707 = 35267561) B35267561
theorem B15674471 : Blo 2063435 15674471 := bstep (se 1 (by rfl) ⟨11755853, by rfl⟩ : syracuseStep 15674471 = 23511707) B23511707
theorem B10449647 : Blo 2063435 10449647 := bstep (se 1 (by rfl) ⟨7837235, by rfl⟩ : syracuseStep 10449647 = 15674471) B15674471
theorem B6966431 : Blo 2063435 6966431 := bstep (se 1 (by rfl) ⟨5224823, by rfl⟩ : syracuseStep 6966431 = 10449647) B10449647
theorem B4644287 : Blo 2063435 4644287 := bstep (se 1 (by rfl) ⟨3483215, by rfl⟩ : syracuseStep 4644287 = 6966431) B6966431
theorem B3096191 : Blo 2063435 3096191 := bstep (se 1 (by rfl) ⟨2322143, by rfl⟩ : syracuseStep 3096191 = 4644287) B4644287
theorem B2064127 : Blo 2063435 2064127 := bstep (se 1 (by rfl) ⟨1548095, by rfl⟩ : syracuseStep 2064127 = 3096191) B3096191
theorem B3096197 : Blo 2063435 3096197 := bbase (se 4 (by rfl) ⟨290268, by rfl⟩ : syracuseStep 3096197 = 580537) (by norm_num)
theorem B2064131 : Blo 2063435 2064131 := bstep (se 1 (by rfl) ⟨1548098, by rfl⟩ : syracuseStep 2064131 = 3096197) B3096197
theorem B3483229 : Blo 2063435 3483229 := bbase (se 3 (by rfl) ⟨653105, by rfl⟩ : syracuseStep 3483229 = 1306211) (by norm_num)
theorem B4644305 : Blo 2063435 4644305 := bstep (se 2 (by rfl) ⟨1741614, by rfl⟩ : syracuseStep 4644305 = 3483229) B3483229
theorem B3096203 : Blo 2063435 3096203 := bstep (se 1 (by rfl) ⟨2322152, by rfl⟩ : syracuseStep 3096203 = 4644305) B4644305
theorem B2064135 : Blo 2063435 2064135 := bstep (se 1 (by rfl) ⟨1548101, by rfl⟩ : syracuseStep 2064135 = 3096203) B3096203
theorem B2322157 : Blo 2063435 2322157 := bbase (se 3 (by rfl) ⟨435404, by rfl⟩ : syracuseStep 2322157 = 870809) (by norm_num)
theorem B3096209 : Blo 2063435 3096209 := bstep (se 2 (by rfl) ⟨1161078, by rfl⟩ : syracuseStep 3096209 = 2322157) B2322157
theorem B2064139 : Blo 2063435 2064139 := bstep (se 1 (by rfl) ⟨1548104, by rfl⟩ : syracuseStep 2064139 = 3096209) B3096209
theorem B6966485 : Blo 2063435 6966485 := bbase (se 7 (by rfl) ⟨81638, by rfl⟩ : syracuseStep 6966485 = 163277) (by norm_num)
theorem B4644323 : Blo 2063435 4644323 := bstep (se 1 (by rfl) ⟨3483242, by rfl⟩ : syracuseStep 4644323 = 6966485) B6966485
theorem B3096215 : Blo 2063435 3096215 := bstep (se 1 (by rfl) ⟨2322161, by rfl⟩ : syracuseStep 3096215 = 4644323) B4644323
theorem B2064143 : Blo 2063435 2064143 := bstep (se 1 (by rfl) ⟨1548107, by rfl⟩ : syracuseStep 2064143 = 3096215) B3096215
theorem B3096221 : Blo 2063435 3096221 := bbase (se 3 (by rfl) ⟨580541, by rfl⟩ : syracuseStep 3096221 = 1161083) (by norm_num)
theorem B2064147 : Blo 2063435 2064147 := bstep (se 1 (by rfl) ⟨1548110, by rfl⟩ : syracuseStep 2064147 = 3096221) B3096221
theorem B4644341 : Blo 2063435 4644341 := bbase (se 5 (by rfl) ⟨217703, by rfl⟩ : syracuseStep 4644341 = 435407) (by norm_num)
theorem B3096227 : Blo 2063435 3096227 := bstep (se 1 (by rfl) ⟨2322170, by rfl⟩ : syracuseStep 3096227 = 4644341) B4644341
theorem B2064151 : Blo 2063435 2064151 := bstep (se 1 (by rfl) ⟨1548113, by rfl⟩ : syracuseStep 2064151 = 3096227) B3096227
theorem B10054469 : Blo 2063435 10054469 := bbase (se 4 (by rfl) ⟨942606, by rfl⟩ : syracuseStep 10054469 = 1885213) (by norm_num)
theorem B26811917 : Blo 2063435 26811917 := bstep (se 3 (by rfl) ⟨5027234, by rfl⟩ : syracuseStep 26811917 = 10054469) B10054469
theorem B17874611 : Blo 2063435 17874611 := bstep (se 1 (by rfl) ⟨13405958, by rfl⟩ : syracuseStep 17874611 = 26811917) B26811917
theorem B11916407 : Blo 2063435 11916407 := bstep (se 1 (by rfl) ⟨8937305, by rfl⟩ : syracuseStep 11916407 = 17874611) B17874611
theorem B31777085 : Blo 2063435 31777085 := bstep (se 3 (by rfl) ⟨5958203, by rfl⟩ : syracuseStep 31777085 = 11916407) B11916407
theorem B21184723 : Blo 2063435 21184723 := bstep (se 1 (by rfl) ⟨15888542, by rfl⟩ : syracuseStep 21184723 = 31777085) B31777085
theorem B112985189 : Blo 2063435 112985189 := bstep (se 4 (by rfl) ⟨10592361, by rfl⟩ : syracuseStep 112985189 = 21184723) B21184723
theorem B75323459 : Blo 2063435 75323459 := bstep (se 1 (by rfl) ⟨56492594, by rfl⟩ : syracuseStep 75323459 = 112985189) B112985189
theorem B50215639 : Blo 2063435 50215639 := bstep (se 1 (by rfl) ⟨37661729, by rfl⟩ : syracuseStep 50215639 = 75323459) B75323459
theorem B66954185 : Blo 2063435 66954185 := bstep (se 2 (by rfl) ⟨25107819, by rfl⟩ : syracuseStep 66954185 = 50215639) B50215639
theorem B44636123 : Blo 2063435 44636123 := bstep (se 1 (by rfl) ⟨33477092, by rfl⟩ : syracuseStep 44636123 = 66954185) B66954185
theorem B29757415 : Blo 2063435 29757415 := bstep (se 1 (by rfl) ⟨22318061, by rfl⟩ : syracuseStep 29757415 = 44636123) B44636123
theorem B39676553 : Blo 2063435 39676553 := bstep (se 2 (by rfl) ⟨14878707, by rfl⟩ : syracuseStep 39676553 = 29757415) B29757415
theorem B26451035 : Blo 2063435 26451035 := bstep (se 1 (by rfl) ⟨19838276, by rfl⟩ : syracuseStep 26451035 = 39676553) B39676553
theorem B17634023 : Blo 2063435 17634023 := bstep (se 1 (by rfl) ⟨13225517, by rfl⟩ : syracuseStep 17634023 = 26451035) B26451035
theorem B11756015 : Blo 2063435 11756015 := bstep (se 1 (by rfl) ⟨8817011, by rfl⟩ : syracuseStep 11756015 = 17634023) B17634023
theorem B7837343 : Blo 2063435 7837343 := bstep (se 1 (by rfl) ⟨5878007, by rfl⟩ : syracuseStep 7837343 = 11756015) B11756015
theorem B5224895 : Blo 2063435 5224895 := bstep (se 1 (by rfl) ⟨3918671, by rfl⟩ : syracuseStep 5224895 = 7837343) B7837343
theorem B3483263 : Blo 2063435 3483263 := bstep (se 1 (by rfl) ⟨2612447, by rfl⟩ : syracuseStep 3483263 = 5224895) B5224895
theorem B2322175 : Blo 2063435 2322175 := bstep (se 1 (by rfl) ⟨1741631, by rfl⟩ : syracuseStep 2322175 = 3483263) B3483263
theorem B3096233 : Blo 2063435 3096233 := bstep (se 2 (by rfl) ⟨1161087, by rfl⟩ : syracuseStep 3096233 = 2322175) B2322175
theorem B2064155 : Blo 2063435 2064155 := bstep (se 1 (by rfl) ⟨1548116, by rfl⟩ : syracuseStep 2064155 = 3096233) B3096233
theorem B2204257 : Blo 2063435 2204257 := bbase (se 2 (by rfl) ⟨826596, by rfl⟩ : syracuseStep 2204257 = 1653193) (by norm_num)
theorem B2939009 : Blo 2063435 2939009 := bstep (se 2 (by rfl) ⟨1102128, by rfl⟩ : syracuseStep 2939009 = 2204257) B2204257
theorem B7837357 : Blo 2063435 7837357 := bstep (se 3 (by rfl) ⟨1469504, by rfl⟩ : syracuseStep 7837357 = 2939009) B2939009
theorem B10449809 : Blo 2063435 10449809 := bstep (se 2 (by rfl) ⟨3918678, by rfl⟩ : syracuseStep 10449809 = 7837357) B7837357
theorem B6966539 : Blo 2063435 6966539 := bstep (se 1 (by rfl) ⟨5224904, by rfl⟩ : syracuseStep 6966539 = 10449809) B10449809
theorem B4644359 : Blo 2063435 4644359 := bstep (se 1 (by rfl) ⟨3483269, by rfl⟩ : syracuseStep 4644359 = 6966539) B6966539
theorem B3096239 : Blo 2063435 3096239 := bstep (se 1 (by rfl) ⟨2322179, by rfl⟩ : syracuseStep 3096239 = 4644359) B4644359
theorem B2064159 : Blo 2063435 2064159 := bstep (se 1 (by rfl) ⟨1548119, by rfl⟩ : syracuseStep 2064159 = 3096239) B3096239
theorem B3096245 : Blo 2063435 3096245 := bbase (se 5 (by rfl) ⟨145136, by rfl⟩ : syracuseStep 3096245 = 290273) (by norm_num)
theorem B2064163 : Blo 2063435 2064163 := bstep (se 1 (by rfl) ⟨1548122, by rfl⟩ : syracuseStep 2064163 = 3096245) B3096245
theorem B5224925 : Blo 2063435 5224925 := bbase (se 3 (by rfl) ⟨979673, by rfl⟩ : syracuseStep 5224925 = 1959347) (by norm_num)
theorem B3483283 : Blo 2063435 3483283 := bstep (se 1 (by rfl) ⟨2612462, by rfl⟩ : syracuseStep 3483283 = 5224925) B5224925
theorem B4644377 : Blo 2063435 4644377 := bstep (se 2 (by rfl) ⟨1741641, by rfl⟩ : syracuseStep 4644377 = 3483283) B3483283
theorem B3096251 : Blo 2063435 3096251 := bstep (se 1 (by rfl) ⟨2322188, by rfl⟩ : syracuseStep 3096251 = 4644377) B4644377
theorem B2064167 : Blo 2063435 2064167 := bstep (se 1 (by rfl) ⟨1548125, by rfl⟩ : syracuseStep 2064167 = 3096251) B3096251
theorem B2322193 : Blo 2063435 2322193 := bbase (se 2 (by rfl) ⟨870822, by rfl⟩ : syracuseStep 2322193 = 1741645) (by norm_num)
theorem B3096257 : Blo 2063435 3096257 := bstep (se 2 (by rfl) ⟨1161096, by rfl⟩ : syracuseStep 3096257 = 2322193) B2322193
theorem B2064171 : Blo 2063435 2064171 := bstep (se 1 (by rfl) ⟨1548128, by rfl⟩ : syracuseStep 2064171 = 3096257) B3096257
theorem B3918709 : Blo 2063435 3918709 := bbase (se 5 (by rfl) ⟨183689, by rfl⟩ : syracuseStep 3918709 = 367379) (by norm_num)
theorem B5224945 : Blo 2063435 5224945 := bstep (se 2 (by rfl) ⟨1959354, by rfl⟩ : syracuseStep 5224945 = 3918709) B3918709
theorem B6966593 : Blo 2063435 6966593 := bstep (se 2 (by rfl) ⟨2612472, by rfl⟩ : syracuseStep 6966593 = 5224945) B5224945
theorem B4644395 : Blo 2063435 4644395 := bstep (se 1 (by rfl) ⟨3483296, by rfl⟩ : syracuseStep 4644395 = 6966593) B6966593
theorem B3096263 : Blo 2063435 3096263 := bstep (se 1 (by rfl) ⟨2322197, by rfl⟩ : syracuseStep 3096263 = 4644395) B4644395
theorem B2064175 : Blo 2063435 2064175 := bstep (se 1 (by rfl) ⟨1548131, by rfl⟩ : syracuseStep 2064175 = 3096263) B3096263
theorem B3096269 : Blo 2063435 3096269 := bbase (se 3 (by rfl) ⟨580550, by rfl⟩ : syracuseStep 3096269 = 1161101) (by norm_num)
theorem B2064179 : Blo 2063435 2064179 := bstep (se 1 (by rfl) ⟨1548134, by rfl⟩ : syracuseStep 2064179 = 3096269) B3096269
theorem B4644413 : Blo 2063435 4644413 := bbase (se 3 (by rfl) ⟨870827, by rfl⟩ : syracuseStep 4644413 = 1741655) (by norm_num)
theorem B3096275 : Blo 2063435 3096275 := bstep (se 1 (by rfl) ⟨2322206, by rfl⟩ : syracuseStep 3096275 = 4644413) B4644413
theorem B2064183 : Blo 2063435 2064183 := bstep (se 1 (by rfl) ⟨1548137, by rfl⟩ : syracuseStep 2064183 = 3096275) B3096275
theorem B3483317 : Blo 2063435 3483317 := bbase (se 5 (by rfl) ⟨163280, by rfl⟩ : syracuseStep 3483317 = 326561) (by norm_num)
theorem B2322211 : Blo 2063435 2322211 := bstep (se 1 (by rfl) ⟨1741658, by rfl⟩ : syracuseStep 2322211 = 3483317) B3483317
theorem B3096281 : Blo 2063435 3096281 := bstep (se 2 (by rfl) ⟨1161105, by rfl⟩ : syracuseStep 3096281 = 2322211) B2322211
theorem B2064187 : Blo 2063435 2064187 := bstep (se 1 (by rfl) ⟨1548140, by rfl⟩ : syracuseStep 2064187 = 3096281) B3096281
theorem B3306437 : Blo 2063435 3306437 := bbase (se 4 (by rfl) ⟨309978, by rfl⟩ : syracuseStep 3306437 = 619957) (by norm_num)
theorem B2204291 : Blo 2063435 2204291 := bstep (se 1 (by rfl) ⟨1653218, by rfl⟩ : syracuseStep 2204291 = 3306437) B3306437
theorem B5878109 : Blo 2063435 5878109 := bstep (se 3 (by rfl) ⟨1102145, by rfl⟩ : syracuseStep 5878109 = 2204291) B2204291
theorem B15674957 : Blo 2063435 15674957 := bstep (se 3 (by rfl) ⟨2939054, by rfl⟩ : syracuseStep 15674957 = 5878109) B5878109
theorem B10449971 : Blo 2063435 10449971 := bstep (se 1 (by rfl) ⟨7837478, by rfl⟩ : syracuseStep 10449971 = 15674957) B15674957
theorem B6966647 : Blo 2063435 6966647 := bstep (se 1 (by rfl) ⟨5224985, by rfl⟩ : syracuseStep 6966647 = 10449971) B10449971
theorem B4644431 : Blo 2063435 4644431 := bstep (se 1 (by rfl) ⟨3483323, by rfl⟩ : syracuseStep 4644431 = 6966647) B6966647
theorem B3096287 : Blo 2063435 3096287 := bstep (se 1 (by rfl) ⟨2322215, by rfl⟩ : syracuseStep 3096287 = 4644431) B4644431
theorem B2064191 : Blo 2063435 2064191 := bstep (se 1 (by rfl) ⟨1548143, by rfl⟩ : syracuseStep 2064191 = 3096287) B3096287
theorem B3096293 : Blo 2063435 3096293 := bbase (se 4 (by rfl) ⟨290277, by rfl⟩ : syracuseStep 3096293 = 580555) (by norm_num)
theorem B2064195 : Blo 2063435 2064195 := bstep (se 1 (by rfl) ⟨1548146, by rfl⟩ : syracuseStep 2064195 = 3096293) B3096293
theorem B5878133 : Blo 2063435 5878133 := bbase (se 5 (by rfl) ⟨275537, by rfl⟩ : syracuseStep 5878133 = 551075) (by norm_num)
theorem B3918755 : Blo 2063435 3918755 := bstep (se 1 (by rfl) ⟨2939066, by rfl⟩ : syracuseStep 3918755 = 5878133) B5878133
theorem B2612503 : Blo 2063435 2612503 := bstep (se 1 (by rfl) ⟨1959377, by rfl⟩ : syracuseStep 2612503 = 3918755) B3918755
theorem B3483337 : Blo 2063435 3483337 := bstep (se 2 (by rfl) ⟨1306251, by rfl⟩ : syracuseStep 3483337 = 2612503) B2612503
theorem B4644449 : Blo 2063435 4644449 := bstep (se 2 (by rfl) ⟨1741668, by rfl⟩ : syracuseStep 4644449 = 3483337) B3483337
theorem B3096299 : Blo 2063435 3096299 := bstep (se 1 (by rfl) ⟨2322224, by rfl⟩ : syracuseStep 3096299 = 4644449) B4644449
theorem B2064199 : Blo 2063435 2064199 := bstep (se 1 (by rfl) ⟨1548149, by rfl⟩ : syracuseStep 2064199 = 3096299) B3096299
theorem B2322229 : Blo 2063435 2322229 := bbase (se 5 (by rfl) ⟨108854, by rfl⟩ : syracuseStep 2322229 = 217709) (by norm_num)
theorem B3096305 : Blo 2063435 3096305 := bstep (se 2 (by rfl) ⟨1161114, by rfl⟩ : syracuseStep 3096305 = 2322229) B2322229
theorem B2064203 : Blo 2063435 2064203 := bstep (se 1 (by rfl) ⟨1548152, by rfl⟩ : syracuseStep 2064203 = 3096305) B3096305
theorem B2612513 : Blo 2063435 2612513 := bbase (se 2 (by rfl) ⟨979692, by rfl⟩ : syracuseStep 2612513 = 1959385) (by norm_num)
theorem B6966701 : Blo 2063435 6966701 := bstep (se 3 (by rfl) ⟨1306256, by rfl⟩ : syracuseStep 6966701 = 2612513) B2612513
theorem B4644467 : Blo 2063435 4644467 := bstep (se 1 (by rfl) ⟨3483350, by rfl⟩ : syracuseStep 4644467 = 6966701) B6966701
theorem B3096311 : Blo 2063435 3096311 := bstep (se 1 (by rfl) ⟨2322233, by rfl⟩ : syracuseStep 3096311 = 4644467) B4644467
theorem B2064207 : Blo 2063435 2064207 := bstep (se 1 (by rfl) ⟨1548155, by rfl⟩ : syracuseStep 2064207 = 3096311) B3096311
theorem B3096317 : Blo 2063435 3096317 := bbase (se 3 (by rfl) ⟨580559, by rfl⟩ : syracuseStep 3096317 = 1161119) (by norm_num)
theorem B2064211 : Blo 2063435 2064211 := bstep (se 1 (by rfl) ⟨1548158, by rfl⟩ : syracuseStep 2064211 = 3096317) B3096317
theorem B4644485 : Blo 2063435 4644485 := bbase (se 4 (by rfl) ⟨435420, by rfl⟩ : syracuseStep 4644485 = 870841) (by norm_num)
theorem B3096323 : Blo 2063435 3096323 := bstep (se 1 (by rfl) ⟨2322242, by rfl⟩ : syracuseStep 3096323 = 4644485) B4644485
theorem B2064215 : Blo 2063435 2064215 := bstep (se 1 (by rfl) ⟨1548161, by rfl⟩ : syracuseStep 2064215 = 3096323) B3096323
theorem B6612965 : Blo 2063435 6612965 := bbase (se 4 (by rfl) ⟨619965, by rfl⟩ : syracuseStep 6612965 = 1239931) (by norm_num)
theorem B4408643 : Blo 2063435 4408643 := bstep (se 1 (by rfl) ⟨3306482, by rfl⟩ : syracuseStep 4408643 = 6612965) B6612965
theorem B2939095 : Blo 2063435 2939095 := bstep (se 1 (by rfl) ⟨2204321, by rfl⟩ : syracuseStep 2939095 = 4408643) B4408643
theorem B3918793 : Blo 2063435 3918793 := bstep (se 2 (by rfl) ⟨1469547, by rfl⟩ : syracuseStep 3918793 = 2939095) B2939095
theorem B5225057 : Blo 2063435 5225057 := bstep (se 2 (by rfl) ⟨1959396, by rfl⟩ : syracuseStep 5225057 = 3918793) B3918793
theorem B3483371 : Blo 2063435 3483371 := bstep (se 1 (by rfl) ⟨2612528, by rfl⟩ : syracuseStep 3483371 = 5225057) B5225057
theorem B2322247 : Blo 2063435 2322247 := bstep (se 1 (by rfl) ⟨1741685, by rfl⟩ : syracuseStep 2322247 = 3483371) B3483371
theorem B3096329 : Blo 2063435 3096329 := bstep (se 2 (by rfl) ⟨1161123, by rfl⟩ : syracuseStep 3096329 = 2322247) B2322247
theorem B2064219 : Blo 2063435 2064219 := bstep (se 1 (by rfl) ⟨1548164, by rfl⟩ : syracuseStep 2064219 = 3096329) B3096329
theorem B10450133 : Blo 2063435 10450133 := bbase (se 7 (by rfl) ⟨122462, by rfl⟩ : syracuseStep 10450133 = 244925) (by norm_num)
theorem B6966755 : Blo 2063435 6966755 := bstep (se 1 (by rfl) ⟨5225066, by rfl⟩ : syracuseStep 6966755 = 10450133) B10450133
theorem B4644503 : Blo 2063435 4644503 := bstep (se 1 (by rfl) ⟨3483377, by rfl⟩ : syracuseStep 4644503 = 6966755) B6966755
theorem B3096335 : Blo 2063435 3096335 := bstep (se 1 (by rfl) ⟨2322251, by rfl⟩ : syracuseStep 3096335 = 4644503) B4644503
theorem B2064223 : Blo 2063435 2064223 := bstep (se 1 (by rfl) ⟨1548167, by rfl⟩ : syracuseStep 2064223 = 3096335) B3096335
theorem B3096341 : Blo 2063435 3096341 := bbase (se 6 (by rfl) ⟨72570, by rfl⟩ : syracuseStep 3096341 = 145141) (by norm_num)
theorem B2064227 : Blo 2063435 2064227 := bstep (se 1 (by rfl) ⟨1548170, by rfl⟩ : syracuseStep 2064227 = 3096341) B3096341
theorem B3530917 : Blo 2063435 3530917 := bbase (se 4 (by rfl) ⟨331023, by rfl⟩ : syracuseStep 3530917 = 662047) (by norm_num)
theorem B18831557 : Blo 2063435 18831557 := bstep (se 4 (by rfl) ⟨1765458, by rfl⟩ : syracuseStep 18831557 = 3530917) B3530917
theorem B12554371 : Blo 2063435 12554371 := bstep (se 1 (by rfl) ⟨9415778, by rfl⟩ : syracuseStep 12554371 = 18831557) B18831557
theorem B66956645 : Blo 2063435 66956645 := bstep (se 4 (by rfl) ⟨6277185, by rfl⟩ : syracuseStep 66956645 = 12554371) B12554371
theorem B44637763 : Blo 2063435 44637763 := bstep (se 1 (by rfl) ⟨33478322, by rfl⟩ : syracuseStep 44637763 = 66956645) B66956645
theorem B59517017 : Blo 2063435 59517017 := bstep (se 2 (by rfl) ⟨22318881, by rfl⟩ : syracuseStep 59517017 = 44637763) B44637763
theorem B39678011 : Blo 2063435 39678011 := bstep (se 1 (by rfl) ⟨29758508, by rfl⟩ : syracuseStep 39678011 = 59517017) B59517017
theorem B26452007 : Blo 2063435 26452007 := bstep (se 1 (by rfl) ⟨19839005, by rfl⟩ : syracuseStep 26452007 = 39678011) B39678011
theorem B17634671 : Blo 2063435 17634671 := bstep (se 1 (by rfl) ⟨13226003, by rfl⟩ : syracuseStep 17634671 = 26452007) B26452007
theorem B11756447 : Blo 2063435 11756447 := bstep (se 1 (by rfl) ⟨8817335, by rfl⟩ : syracuseStep 11756447 = 17634671) B17634671
theorem B7837631 : Blo 2063435 7837631 := bstep (se 1 (by rfl) ⟨5878223, by rfl⟩ : syracuseStep 7837631 = 11756447) B11756447
theorem B5225087 : Blo 2063435 5225087 := bstep (se 1 (by rfl) ⟨3918815, by rfl⟩ : syracuseStep 5225087 = 7837631) B7837631
theorem B3483391 : Blo 2063435 3483391 := bstep (se 1 (by rfl) ⟨2612543, by rfl⟩ : syracuseStep 3483391 = 5225087) B5225087
theorem B4644521 : Blo 2063435 4644521 := bstep (se 2 (by rfl) ⟨1741695, by rfl⟩ : syracuseStep 4644521 = 3483391) B3483391
theorem B3096347 : Blo 2063435 3096347 := bstep (se 1 (by rfl) ⟨2322260, by rfl⟩ : syracuseStep 3096347 = 4644521) B4644521
theorem B2064231 : Blo 2063435 2064231 := bstep (se 1 (by rfl) ⟨1548173, by rfl⟩ : syracuseStep 2064231 = 3096347) B3096347
theorem B2322265 : Blo 2063435 2322265 := bbase (se 2 (by rfl) ⟨870849, by rfl⟩ : syracuseStep 2322265 = 1741699) (by norm_num)
theorem B3096353 : Blo 2063435 3096353 := bstep (se 2 (by rfl) ⟨1161132, by rfl⟩ : syracuseStep 3096353 = 2322265) B2322265
theorem B2064235 : Blo 2063435 2064235 := bstep (se 1 (by rfl) ⟨1548176, by rfl⟩ : syracuseStep 2064235 = 3096353) B3096353
theorem B4408685 : Blo 2063435 4408685 := bbase (se 3 (by rfl) ⟨826628, by rfl⟩ : syracuseStep 4408685 = 1653257) (by norm_num)
theorem B2939123 : Blo 2063435 2939123 := bstep (se 1 (by rfl) ⟨2204342, by rfl⟩ : syracuseStep 2939123 = 4408685) B4408685
theorem B7837661 : Blo 2063435 7837661 := bstep (se 3 (by rfl) ⟨1469561, by rfl⟩ : syracuseStep 7837661 = 2939123) B2939123
theorem B5225107 : Blo 2063435 5225107 := bstep (se 1 (by rfl) ⟨3918830, by rfl⟩ : syracuseStep 5225107 = 7837661) B7837661
theorem B6966809 : Blo 2063435 6966809 := bstep (se 2 (by rfl) ⟨2612553, by rfl⟩ : syracuseStep 6966809 = 5225107) B5225107
theorem B4644539 : Blo 2063435 4644539 := bstep (se 1 (by rfl) ⟨3483404, by rfl⟩ : syracuseStep 4644539 = 6966809) B6966809
theorem B3096359 : Blo 2063435 3096359 := bstep (se 1 (by rfl) ⟨2322269, by rfl⟩ : syracuseStep 3096359 = 4644539) B4644539
theorem B2064239 : Blo 2063435 2064239 := bstep (se 1 (by rfl) ⟨1548179, by rfl⟩ : syracuseStep 2064239 = 3096359) B3096359
theorem B3096365 : Blo 2063435 3096365 := bbase (se 3 (by rfl) ⟨580568, by rfl⟩ : syracuseStep 3096365 = 1161137) (by norm_num)
theorem B2064243 : Blo 2063435 2064243 := bstep (se 1 (by rfl) ⟨1548182, by rfl⟩ : syracuseStep 2064243 = 3096365) B3096365
theorem B4644557 : Blo 2063435 4644557 := bbase (se 3 (by rfl) ⟨870854, by rfl⟩ : syracuseStep 4644557 = 1741709) (by norm_num)
theorem B3096371 : Blo 2063435 3096371 := bstep (se 1 (by rfl) ⟨2322278, by rfl⟩ : syracuseStep 3096371 = 4644557) B4644557
theorem B2064247 : Blo 2063435 2064247 := bstep (se 1 (by rfl) ⟨1548185, by rfl⟩ : syracuseStep 2064247 = 3096371) B3096371
theorem B2612569 : Blo 2063435 2612569 := bbase (se 2 (by rfl) ⟨979713, by rfl⟩ : syracuseStep 2612569 = 1959427) (by norm_num)
theorem B3483425 : Blo 2063435 3483425 := bstep (se 2 (by rfl) ⟨1306284, by rfl⟩ : syracuseStep 3483425 = 2612569) B2612569
theorem B2322283 : Blo 2063435 2322283 := bstep (se 1 (by rfl) ⟨1741712, by rfl⟩ : syracuseStep 2322283 = 3483425) B3483425
theorem B3096377 : Blo 2063435 3096377 := bstep (se 2 (by rfl) ⟨1161141, by rfl⟩ : syracuseStep 3096377 = 2322283) B2322283
theorem B2064251 : Blo 2063435 2064251 := bstep (se 1 (by rfl) ⟨1548188, by rfl⟩ : syracuseStep 2064251 = 3096377) B3096377
theorem B2789893 : Blo 2063435 2789893 := bbase (se 4 (by rfl) ⟨261552, by rfl⟩ : syracuseStep 2789893 = 523105) (by norm_num)
theorem B3719857 : Blo 2063435 3719857 := bstep (se 2 (by rfl) ⟨1394946, by rfl⟩ : syracuseStep 3719857 = 2789893) B2789893
theorem B4959809 : Blo 2063435 4959809 := bstep (se 2 (by rfl) ⟨1859928, by rfl⟩ : syracuseStep 4959809 = 3719857) B3719857
theorem B3306539 : Blo 2063435 3306539 := bstep (se 1 (by rfl) ⟨2479904, by rfl⟩ : syracuseStep 3306539 = 4959809) B4959809
theorem B8817437 : Blo 2063435 8817437 := bstep (se 3 (by rfl) ⟨1653269, by rfl⟩ : syracuseStep 8817437 = 3306539) B3306539
theorem B23513165 : Blo 2063435 23513165 := bstep (se 3 (by rfl) ⟨4408718, by rfl⟩ : syracuseStep 23513165 = 8817437) B8817437
theorem B15675443 : Blo 2063435 15675443 := bstep (se 1 (by rfl) ⟨11756582, by rfl⟩ : syracuseStep 15675443 = 23513165) B23513165
theorem B10450295 : Blo 2063435 10450295 := bstep (se 1 (by rfl) ⟨7837721, by rfl⟩ : syracuseStep 10450295 = 15675443) B15675443
theorem B6966863 : Blo 2063435 6966863 := bstep (se 1 (by rfl) ⟨5225147, by rfl⟩ : syracuseStep 6966863 = 10450295) B10450295
theorem B4644575 : Blo 2063435 4644575 := bstep (se 1 (by rfl) ⟨3483431, by rfl⟩ : syracuseStep 4644575 = 6966863) B6966863
theorem B3096383 : Blo 2063435 3096383 := bstep (se 1 (by rfl) ⟨2322287, by rfl⟩ : syracuseStep 3096383 = 4644575) B4644575
theorem B2064255 : Blo 2063435 2064255 := bstep (se 1 (by rfl) ⟨1548191, by rfl⟩ : syracuseStep 2064255 = 3096383) B3096383
theorem B3096389 : Blo 2063435 3096389 := bbase (se 4 (by rfl) ⟨290286, by rfl⟩ : syracuseStep 3096389 = 580573) (by norm_num)
theorem B2064259 : Blo 2063435 2064259 := bstep (se 1 (by rfl) ⟨1548194, by rfl⟩ : syracuseStep 2064259 = 3096389) B3096389
theorem B3483445 : Blo 2063435 3483445 := bbase (se 5 (by rfl) ⟨163286, by rfl⟩ : syracuseStep 3483445 = 326573) (by norm_num)
theorem B4644593 : Blo 2063435 4644593 := bstep (se 2 (by rfl) ⟨1741722, by rfl⟩ : syracuseStep 4644593 = 3483445) B3483445
theorem B3096395 : Blo 2063435 3096395 := bstep (se 1 (by rfl) ⟨2322296, by rfl⟩ : syracuseStep 3096395 = 4644593) B4644593
theorem B2064263 : Blo 2063435 2064263 := bstep (se 1 (by rfl) ⟨1548197, by rfl⟩ : syracuseStep 2064263 = 3096395) B3096395
theorem B2322301 : Blo 2063435 2322301 := bbase (se 3 (by rfl) ⟨435431, by rfl⟩ : syracuseStep 2322301 = 870863) (by norm_num)
theorem B3096401 : Blo 2063435 3096401 := bstep (se 2 (by rfl) ⟨1161150, by rfl⟩ : syracuseStep 3096401 = 2322301) B2322301
theorem B2064267 : Blo 2063435 2064267 := bstep (se 1 (by rfl) ⟨1548200, by rfl⟩ : syracuseStep 2064267 = 3096401) B3096401
theorem B6966917 : Blo 2063435 6966917 := bbase (se 4 (by rfl) ⟨653148, by rfl⟩ : syracuseStep 6966917 = 1306297) (by norm_num)
theorem B4644611 : Blo 2063435 4644611 := bstep (se 1 (by rfl) ⟨3483458, by rfl⟩ : syracuseStep 4644611 = 6966917) B6966917
theorem B3096407 : Blo 2063435 3096407 := bstep (se 1 (by rfl) ⟨2322305, by rfl⟩ : syracuseStep 3096407 = 4644611) B4644611
theorem B2064271 : Blo 2063435 2064271 := bstep (se 1 (by rfl) ⟨1548203, by rfl⟩ : syracuseStep 2064271 = 3096407) B3096407
theorem B3096413 : Blo 2063435 3096413 := bbase (se 3 (by rfl) ⟨580577, by rfl⟩ : syracuseStep 3096413 = 1161155) (by norm_num)
theorem B2064275 : Blo 2063435 2064275 := bstep (se 1 (by rfl) ⟨1548206, by rfl⟩ : syracuseStep 2064275 = 3096413) B3096413
theorem B4644629 : Blo 2063435 4644629 := bbase (se 6 (by rfl) ⟨108858, by rfl⟩ : syracuseStep 4644629 = 217717) (by norm_num)
theorem B3096419 : Blo 2063435 3096419 := bstep (se 1 (by rfl) ⟨2322314, by rfl⟩ : syracuseStep 3096419 = 4644629) B4644629
theorem B2064279 : Blo 2063435 2064279 := bstep (se 1 (by rfl) ⟨1548209, by rfl⟩ : syracuseStep 2064279 = 3096419) B3096419
theorem B7837829 : Blo 2063435 7837829 := bbase (se 4 (by rfl) ⟨734796, by rfl⟩ : syracuseStep 7837829 = 1469593) (by norm_num)
theorem B5225219 : Blo 2063435 5225219 := bstep (se 1 (by rfl) ⟨3918914, by rfl⟩ : syracuseStep 5225219 = 7837829) B7837829
theorem B3483479 : Blo 2063435 3483479 := bstep (se 1 (by rfl) ⟨2612609, by rfl⟩ : syracuseStep 3483479 = 5225219) B5225219
theorem B2322319 : Blo 2063435 2322319 := bstep (se 1 (by rfl) ⟨1741739, by rfl⟩ : syracuseStep 2322319 = 3483479) B3483479
theorem B3096425 : Blo 2063435 3096425 := bstep (se 2 (by rfl) ⟨1161159, by rfl⟩ : syracuseStep 3096425 = 2322319) B2322319
theorem B2064283 : Blo 2063435 2064283 := bstep (se 1 (by rfl) ⟨1548212, by rfl⟩ : syracuseStep 2064283 = 3096425) B3096425
theorem B2648261 : Blo 2063435 2648261 := bbase (se 4 (by rfl) ⟨248274, by rfl⟩ : syracuseStep 2648261 = 496549) (by norm_num)
theorem B7062029 : Blo 2063435 7062029 := bstep (se 3 (by rfl) ⟨1324130, by rfl⟩ : syracuseStep 7062029 = 2648261) B2648261
theorem B4708019 : Blo 2063435 4708019 := bstep (se 1 (by rfl) ⟨3531014, by rfl⟩ : syracuseStep 4708019 = 7062029) B7062029
theorem B3138679 : Blo 2063435 3138679 := bstep (se 1 (by rfl) ⟨2354009, by rfl⟩ : syracuseStep 3138679 = 4708019) B4708019
theorem B4184905 : Blo 2063435 4184905 := bstep (se 2 (by rfl) ⟨1569339, by rfl⟩ : syracuseStep 4184905 = 3138679) B3138679
theorem B5579873 : Blo 2063435 5579873 := bstep (se 2 (by rfl) ⟨2092452, by rfl⟩ : syracuseStep 5579873 = 4184905) B4184905
theorem B3719915 : Blo 2063435 3719915 := bstep (se 1 (by rfl) ⟨2789936, by rfl⟩ : syracuseStep 3719915 = 5579873) B5579873
theorem B2479943 : Blo 2063435 2479943 := bstep (se 1 (by rfl) ⟨1859957, by rfl⟩ : syracuseStep 2479943 = 3719915) B3719915
theorem B6613181 : Blo 2063435 6613181 := bstep (se 3 (by rfl) ⟨1239971, by rfl⟩ : syracuseStep 6613181 = 2479943) B2479943
theorem B4408787 : Blo 2063435 4408787 := bstep (se 1 (by rfl) ⟨3306590, by rfl⟩ : syracuseStep 4408787 = 6613181) B6613181
theorem B11756765 : Blo 2063435 11756765 := bstep (se 3 (by rfl) ⟨2204393, by rfl⟩ : syracuseStep 11756765 = 4408787) B4408787
theorem B7837843 : Blo 2063435 7837843 := bstep (se 1 (by rfl) ⟨5878382, by rfl⟩ : syracuseStep 7837843 = 11756765) B11756765
theorem B10450457 : Blo 2063435 10450457 := bstep (se 2 (by rfl) ⟨3918921, by rfl⟩ : syracuseStep 10450457 = 7837843) B7837843
theorem B6966971 : Blo 2063435 6966971 := bstep (se 1 (by rfl) ⟨5225228, by rfl⟩ : syracuseStep 6966971 = 10450457) B10450457
theorem B4644647 : Blo 2063435 4644647 := bstep (se 1 (by rfl) ⟨3483485, by rfl⟩ : syracuseStep 4644647 = 6966971) B6966971
theorem B3096431 : Blo 2063435 3096431 := bstep (se 1 (by rfl) ⟨2322323, by rfl⟩ : syracuseStep 3096431 = 4644647) B4644647
theorem B2064287 : Blo 2063435 2064287 := bstep (se 1 (by rfl) ⟨1548215, by rfl⟩ : syracuseStep 2064287 = 3096431) B3096431
theorem B3096437 : Blo 2063435 3096437 := bbase (se 5 (by rfl) ⟨145145, by rfl⟩ : syracuseStep 3096437 = 290291) (by norm_num)
theorem B2064291 : Blo 2063435 2064291 := bstep (se 1 (by rfl) ⟨1548218, by rfl⟩ : syracuseStep 2064291 = 3096437) B3096437
theorem B4408805 : Blo 2063435 4408805 := bbase (se 4 (by rfl) ⟨413325, by rfl⟩ : syracuseStep 4408805 = 826651) (by norm_num)
theorem B2939203 : Blo 2063435 2939203 := bstep (se 1 (by rfl) ⟨2204402, by rfl⟩ : syracuseStep 2939203 = 4408805) B4408805
theorem B3918937 : Blo 2063435 3918937 := bstep (se 2 (by rfl) ⟨1469601, by rfl⟩ : syracuseStep 3918937 = 2939203) B2939203
theorem B5225249 : Blo 2063435 5225249 := bstep (se 2 (by rfl) ⟨1959468, by rfl⟩ : syracuseStep 5225249 = 3918937) B3918937
theorem B3483499 : Blo 2063435 3483499 := bstep (se 1 (by rfl) ⟨2612624, by rfl⟩ : syracuseStep 3483499 = 5225249) B5225249
theorem B4644665 : Blo 2063435 4644665 := bstep (se 2 (by rfl) ⟨1741749, by rfl⟩ : syracuseStep 4644665 = 3483499) B3483499
theorem B3096443 : Blo 2063435 3096443 := bstep (se 1 (by rfl) ⟨2322332, by rfl⟩ : syracuseStep 3096443 = 4644665) B4644665
theorem B2064295 : Blo 2063435 2064295 := bstep (se 1 (by rfl) ⟨1548221, by rfl⟩ : syracuseStep 2064295 = 3096443) B3096443
theorem B2322337 : Blo 2063435 2322337 := bbase (se 2 (by rfl) ⟨870876, by rfl⟩ : syracuseStep 2322337 = 1741753) (by norm_num)
theorem B3096449 : Blo 2063435 3096449 := bstep (se 2 (by rfl) ⟨1161168, by rfl⟩ : syracuseStep 3096449 = 2322337) B2322337
theorem B2064299 : Blo 2063435 2064299 := bstep (se 1 (by rfl) ⟨1548224, by rfl⟩ : syracuseStep 2064299 = 3096449) B3096449
theorem B5225269 : Blo 2063435 5225269 := bbase (se 5 (by rfl) ⟨244934, by rfl⟩ : syracuseStep 5225269 = 489869) (by norm_num)
theorem B6967025 : Blo 2063435 6967025 := bstep (se 2 (by rfl) ⟨2612634, by rfl⟩ : syracuseStep 6967025 = 5225269) B5225269
theorem B4644683 : Blo 2063435 4644683 := bstep (se 1 (by rfl) ⟨3483512, by rfl⟩ : syracuseStep 4644683 = 6967025) B6967025
theorem B3096455 : Blo 2063435 3096455 := bstep (se 1 (by rfl) ⟨2322341, by rfl⟩ : syracuseStep 3096455 = 4644683) B4644683
theorem B2064303 : Blo 2063435 2064303 := bstep (se 1 (by rfl) ⟨1548227, by rfl⟩ : syracuseStep 2064303 = 3096455) B3096455
theorem B3096461 : Blo 2063435 3096461 := bbase (se 3 (by rfl) ⟨580586, by rfl⟩ : syracuseStep 3096461 = 1161173) (by norm_num)
theorem B2064307 : Blo 2063435 2064307 := bstep (se 1 (by rfl) ⟨1548230, by rfl⟩ : syracuseStep 2064307 = 3096461) B3096461
theorem B4644701 : Blo 2063435 4644701 := bbase (se 3 (by rfl) ⟨870881, by rfl⟩ : syracuseStep 4644701 = 1741763) (by norm_num)
theorem B3096467 : Blo 2063435 3096467 := bstep (se 1 (by rfl) ⟨2322350, by rfl⟩ : syracuseStep 3096467 = 4644701) B4644701
theorem B2064311 : Blo 2063435 2064311 := bstep (se 1 (by rfl) ⟨1548233, by rfl⟩ : syracuseStep 2064311 = 3096467) B3096467
theorem B3483533 : Blo 2063435 3483533 := bbase (se 3 (by rfl) ⟨653162, by rfl⟩ : syracuseStep 3483533 = 1306325) (by norm_num)
theorem B2322355 : Blo 2063435 2322355 := bstep (se 1 (by rfl) ⟨1741766, by rfl⟩ : syracuseStep 2322355 = 3483533) B3483533
theorem B3096473 : Blo 2063435 3096473 := bstep (se 2 (by rfl) ⟨1161177, by rfl⟩ : syracuseStep 3096473 = 2322355) B2322355
theorem B2064315 : Blo 2063435 2064315 := bstep (se 1 (by rfl) ⟨1548236, by rfl⟩ : syracuseStep 2064315 = 3096473) B3096473
theorem B9919925 : Blo 2063435 9919925 := bbase (se 5 (by rfl) ⟨464996, by rfl⟩ : syracuseStep 9919925 = 929993) (by norm_num)
theorem B6613283 : Blo 2063435 6613283 := bstep (se 1 (by rfl) ⟨4959962, by rfl⟩ : syracuseStep 6613283 = 9919925) B9919925
theorem B17635421 : Blo 2063435 17635421 := bstep (se 3 (by rfl) ⟨3306641, by rfl⟩ : syracuseStep 17635421 = 6613283) B6613283
theorem B11756947 : Blo 2063435 11756947 := bstep (se 1 (by rfl) ⟨8817710, by rfl⟩ : syracuseStep 11756947 = 17635421) B17635421
theorem B15675929 : Blo 2063435 15675929 := bstep (se 2 (by rfl) ⟨5878473, by rfl⟩ : syracuseStep 15675929 = 11756947) B11756947
theorem B10450619 : Blo 2063435 10450619 := bstep (se 1 (by rfl) ⟨7837964, by rfl⟩ : syracuseStep 10450619 = 15675929) B15675929
theorem B6967079 : Blo 2063435 6967079 := bstep (se 1 (by rfl) ⟨5225309, by rfl⟩ : syracuseStep 6967079 = 10450619) B10450619
theorem B4644719 : Blo 2063435 4644719 := bstep (se 1 (by rfl) ⟨3483539, by rfl⟩ : syracuseStep 4644719 = 6967079) B6967079
theorem B3096479 : Blo 2063435 3096479 := bstep (se 1 (by rfl) ⟨2322359, by rfl⟩ : syracuseStep 3096479 = 4644719) B4644719
theorem B2064319 : Blo 2063435 2064319 := bstep (se 1 (by rfl) ⟨1548239, by rfl⟩ : syracuseStep 2064319 = 3096479) B3096479
theorem B3096485 : Blo 2063435 3096485 := bbase (se 4 (by rfl) ⟨290295, by rfl⟩ : syracuseStep 3096485 = 580591) (by norm_num)
theorem B2064323 : Blo 2063435 2064323 := bstep (se 1 (by rfl) ⟨1548242, by rfl⟩ : syracuseStep 2064323 = 3096485) B3096485
theorem B2612665 : Blo 2063435 2612665 := bbase (se 2 (by rfl) ⟨979749, by rfl⟩ : syracuseStep 2612665 = 1959499) (by norm_num)
theorem B3483553 : Blo 2063435 3483553 := bstep (se 2 (by rfl) ⟨1306332, by rfl⟩ : syracuseStep 3483553 = 2612665) B2612665
theorem B4644737 : Blo 2063435 4644737 := bstep (se 2 (by rfl) ⟨1741776, by rfl⟩ : syracuseStep 4644737 = 3483553) B3483553
theorem B3096491 : Blo 2063435 3096491 := bstep (se 1 (by rfl) ⟨2322368, by rfl⟩ : syracuseStep 3096491 = 4644737) B4644737
theorem B2064327 : Blo 2063435 2064327 := bstep (se 1 (by rfl) ⟨1548245, by rfl⟩ : syracuseStep 2064327 = 3096491) B3096491
theorem B2322373 : Blo 2063435 2322373 := bbase (se 4 (by rfl) ⟨217722, by rfl⟩ : syracuseStep 2322373 = 435445) (by norm_num)
theorem B3096497 : Blo 2063435 3096497 := bstep (se 2 (by rfl) ⟨1161186, by rfl⟩ : syracuseStep 3096497 = 2322373) B2322373
theorem B2064331 : Blo 2063435 2064331 := bstep (se 1 (by rfl) ⟨1548248, by rfl⟩ : syracuseStep 2064331 = 3096497) B3096497
theorem B3919013 : Blo 2063435 3919013 := bbase (se 4 (by rfl) ⟨367407, by rfl⟩ : syracuseStep 3919013 = 734815) (by norm_num)
theorem B2612675 : Blo 2063435 2612675 := bstep (se 1 (by rfl) ⟨1959506, by rfl⟩ : syracuseStep 2612675 = 3919013) B3919013
theorem B6967133 : Blo 2063435 6967133 := bstep (se 3 (by rfl) ⟨1306337, by rfl⟩ : syracuseStep 6967133 = 2612675) B2612675
theorem B4644755 : Blo 2063435 4644755 := bstep (se 1 (by rfl) ⟨3483566, by rfl⟩ : syracuseStep 4644755 = 6967133) B6967133
theorem B3096503 : Blo 2063435 3096503 := bstep (se 1 (by rfl) ⟨2322377, by rfl⟩ : syracuseStep 3096503 = 4644755) B4644755
theorem B2064335 : Blo 2063435 2064335 := bstep (se 1 (by rfl) ⟨1548251, by rfl⟩ : syracuseStep 2064335 = 3096503) B3096503
theorem B3096509 : Blo 2063435 3096509 := bbase (se 3 (by rfl) ⟨580595, by rfl⟩ : syracuseStep 3096509 = 1161191) (by norm_num)
theorem B2064339 : Blo 2063435 2064339 := bstep (se 1 (by rfl) ⟨1548254, by rfl⟩ : syracuseStep 2064339 = 3096509) B3096509
theorem B4644773 : Blo 2063435 4644773 := bbase (se 4 (by rfl) ⟨435447, by rfl⟩ : syracuseStep 4644773 = 870895) (by norm_num)
theorem B3096515 : Blo 2063435 3096515 := bstep (se 1 (by rfl) ⟨2322386, by rfl⟩ : syracuseStep 3096515 = 4644773) B4644773
theorem B2064343 : Blo 2063435 2064343 := bstep (se 1 (by rfl) ⟨1548257, by rfl⟩ : syracuseStep 2064343 = 3096515) B3096515
theorem B5225381 : Blo 2063435 5225381 := bbase (se 4 (by rfl) ⟨489879, by rfl⟩ : syracuseStep 5225381 = 979759) (by norm_num)
theorem B3483587 : Blo 2063435 3483587 := bstep (se 1 (by rfl) ⟨2612690, by rfl⟩ : syracuseStep 3483587 = 5225381) B5225381
theorem B2322391 : Blo 2063435 2322391 := bstep (se 1 (by rfl) ⟨1741793, by rfl⟩ : syracuseStep 2322391 = 3483587) B3483587
theorem B3096521 : Blo 2063435 3096521 := bstep (se 2 (by rfl) ⟨1161195, by rfl⟩ : syracuseStep 3096521 = 2322391) B2322391
theorem B2064347 : Blo 2063435 2064347 := bstep (se 1 (by rfl) ⟨1548260, by rfl⟩ : syracuseStep 2064347 = 3096521) B3096521
theorem B5878565 : Blo 2063435 5878565 := bbase (se 4 (by rfl) ⟨551115, by rfl⟩ : syracuseStep 5878565 = 1102231) (by norm_num)
theorem B3919043 : Blo 2063435 3919043 := bstep (se 1 (by rfl) ⟨2939282, by rfl⟩ : syracuseStep 3919043 = 5878565) B5878565
theorem B10450781 : Blo 2063435 10450781 := bstep (se 3 (by rfl) ⟨1959521, by rfl⟩ : syracuseStep 10450781 = 3919043) B3919043
theorem B6967187 : Blo 2063435 6967187 := bstep (se 1 (by rfl) ⟨5225390, by rfl⟩ : syracuseStep 6967187 = 10450781) B10450781
theorem B4644791 : Blo 2063435 4644791 := bstep (se 1 (by rfl) ⟨3483593, by rfl⟩ : syracuseStep 4644791 = 6967187) B6967187
theorem B3096527 : Blo 2063435 3096527 := bstep (se 1 (by rfl) ⟨2322395, by rfl⟩ : syracuseStep 3096527 = 4644791) B4644791
theorem B2064351 : Blo 2063435 2064351 := bstep (se 1 (by rfl) ⟨1548263, by rfl⟩ : syracuseStep 2064351 = 3096527) B3096527
theorem B3096533 : Blo 2063435 3096533 := bbase (se 7 (by rfl) ⟨36287, by rfl⟩ : syracuseStep 3096533 = 72575) (by norm_num)
theorem B2064355 : Blo 2063435 2064355 := bstep (se 1 (by rfl) ⟨1548266, by rfl⟩ : syracuseStep 2064355 = 3096533) B3096533
theorem B7838117 : Blo 2063435 7838117 := bbase (se 4 (by rfl) ⟨734823, by rfl⟩ : syracuseStep 7838117 = 1469647) (by norm_num)
theorem B5225411 : Blo 2063435 5225411 := bstep (se 1 (by rfl) ⟨3919058, by rfl⟩ : syracuseStep 5225411 = 7838117) B7838117
theorem B3483607 : Blo 2063435 3483607 := bstep (se 1 (by rfl) ⟨2612705, by rfl⟩ : syracuseStep 3483607 = 5225411) B5225411
theorem B4644809 : Blo 2063435 4644809 := bstep (se 2 (by rfl) ⟨1741803, by rfl⟩ : syracuseStep 4644809 = 3483607) B3483607
theorem B3096539 : Blo 2063435 3096539 := bstep (se 1 (by rfl) ⟨2322404, by rfl⟩ : syracuseStep 3096539 = 4644809) B4644809
theorem B2064359 : Blo 2063435 2064359 := bstep (se 1 (by rfl) ⟨1548269, by rfl⟩ : syracuseStep 2064359 = 3096539) B3096539
theorem B2322409 : Blo 2063435 2322409 := bbase (se 2 (by rfl) ⟨870903, by rfl⟩ : syracuseStep 2322409 = 1741807) (by norm_num)
theorem B3096545 : Blo 2063435 3096545 := bstep (se 2 (by rfl) ⟨1161204, by rfl⟩ : syracuseStep 3096545 = 2322409) B2322409
theorem B2064363 : Blo 2063435 2064363 := bstep (se 1 (by rfl) ⟨1548272, by rfl⟩ : syracuseStep 2064363 = 3096545) B3096545
theorem B2234557 : Blo 2063435 2234557 := bbase (se 3 (by rfl) ⟨418979, by rfl⟩ : syracuseStep 2234557 = 837959) (by norm_num)
theorem B11917637 : Blo 2063435 11917637 := bstep (se 4 (by rfl) ⟨1117278, by rfl⟩ : syracuseStep 11917637 = 2234557) B2234557
theorem B7945091 : Blo 2063435 7945091 := bstep (se 1 (by rfl) ⟨5958818, by rfl⟩ : syracuseStep 7945091 = 11917637) B11917637
theorem B5296727 : Blo 2063435 5296727 := bstep (se 1 (by rfl) ⟨3972545, by rfl⟩ : syracuseStep 5296727 = 7945091) B7945091
theorem B3531151 : Blo 2063435 3531151 := bstep (se 1 (by rfl) ⟨2648363, by rfl⟩ : syracuseStep 3531151 = 5296727) B5296727
theorem B4708201 : Blo 2063435 4708201 := bstep (se 2 (by rfl) ⟨1765575, by rfl⟩ : syracuseStep 4708201 = 3531151) B3531151
theorem B6277601 : Blo 2063435 6277601 := bstep (se 2 (by rfl) ⟨2354100, by rfl⟩ : syracuseStep 6277601 = 4708201) B4708201
theorem B16740269 : Blo 2063435 16740269 := bstep (se 3 (by rfl) ⟨3138800, by rfl⟩ : syracuseStep 16740269 = 6277601) B6277601
theorem B11160179 : Blo 2063435 11160179 := bstep (se 1 (by rfl) ⟨8370134, by rfl⟩ : syracuseStep 11160179 = 16740269) B16740269
theorem B7440119 : Blo 2063435 7440119 := bstep (se 1 (by rfl) ⟨5580089, by rfl⟩ : syracuseStep 7440119 = 11160179) B11160179
theorem B4960079 : Blo 2063435 4960079 := bstep (se 1 (by rfl) ⟨3720059, by rfl⟩ : syracuseStep 4960079 = 7440119) B7440119
theorem B3306719 : Blo 2063435 3306719 := bstep (se 1 (by rfl) ⟨2480039, by rfl⟩ : syracuseStep 3306719 = 4960079) B4960079
theorem B2204479 : Blo 2063435 2204479 := bstep (se 1 (by rfl) ⟨1653359, by rfl⟩ : syracuseStep 2204479 = 3306719) B3306719
theorem B11757221 : Blo 2063435 11757221 := bstep (se 4 (by rfl) ⟨1102239, by rfl⟩ : syracuseStep 11757221 = 2204479) B2204479
theorem B7838147 : Blo 2063435 7838147 := bstep (se 1 (by rfl) ⟨5878610, by rfl⟩ : syracuseStep 7838147 = 11757221) B11757221
theorem B5225431 : Blo 2063435 5225431 := bstep (se 1 (by rfl) ⟨3919073, by rfl⟩ : syracuseStep 5225431 = 7838147) B7838147
theorem B6967241 : Blo 2063435 6967241 := bstep (se 2 (by rfl) ⟨2612715, by rfl⟩ : syracuseStep 6967241 = 5225431) B5225431
theorem B4644827 : Blo 2063435 4644827 := bstep (se 1 (by rfl) ⟨3483620, by rfl⟩ : syracuseStep 4644827 = 6967241) B6967241
theorem B3096551 : Blo 2063435 3096551 := bstep (se 1 (by rfl) ⟨2322413, by rfl⟩ : syracuseStep 3096551 = 4644827) B4644827
theorem B2064367 : Blo 2063435 2064367 := bstep (se 1 (by rfl) ⟨1548275, by rfl⟩ : syracuseStep 2064367 = 3096551) B3096551
theorem B3096557 : Blo 2063435 3096557 := bbase (se 3 (by rfl) ⟨580604, by rfl⟩ : syracuseStep 3096557 = 1161209) (by norm_num)
theorem B2064371 : Blo 2063435 2064371 := bstep (se 1 (by rfl) ⟨1548278, by rfl⟩ : syracuseStep 2064371 = 3096557) B3096557
theorem B4644845 : Blo 2063435 4644845 := bbase (se 3 (by rfl) ⟨870908, by rfl⟩ : syracuseStep 4644845 = 1741817) (by norm_num)
theorem B3096563 : Blo 2063435 3096563 := bstep (se 1 (by rfl) ⟨2322422, by rfl⟩ : syracuseStep 3096563 = 4644845) B4644845
theorem B2064375 : Blo 2063435 2064375 := bstep (se 1 (by rfl) ⟨1548281, by rfl⟩ : syracuseStep 2064375 = 3096563) B3096563
theorem B4960109 : Blo 2063435 4960109 := bbase (se 3 (by rfl) ⟨930020, by rfl⟩ : syracuseStep 4960109 = 1860041) (by norm_num)
theorem B3306739 : Blo 2063435 3306739 := bstep (se 1 (by rfl) ⟨2480054, by rfl⟩ : syracuseStep 3306739 = 4960109) B4960109
theorem B4408985 : Blo 2063435 4408985 := bstep (se 2 (by rfl) ⟨1653369, by rfl⟩ : syracuseStep 4408985 = 3306739) B3306739
theorem B2939323 : Blo 2063435 2939323 := bstep (se 1 (by rfl) ⟨2204492, by rfl⟩ : syracuseStep 2939323 = 4408985) B4408985
theorem B3919097 : Blo 2063435 3919097 := bstep (se 2 (by rfl) ⟨1469661, by rfl⟩ : syracuseStep 3919097 = 2939323) B2939323
theorem B2612731 : Blo 2063435 2612731 := bstep (se 1 (by rfl) ⟨1959548, by rfl⟩ : syracuseStep 2612731 = 3919097) B3919097
theorem B3483641 : Blo 2063435 3483641 := bstep (se 2 (by rfl) ⟨1306365, by rfl⟩ : syracuseStep 3483641 = 2612731) B2612731
theorem B2322427 : Blo 2063435 2322427 := bstep (se 1 (by rfl) ⟨1741820, by rfl⟩ : syracuseStep 2322427 = 3483641) B3483641
theorem B3096569 : Blo 2063435 3096569 := bstep (se 2 (by rfl) ⟨1161213, by rfl⟩ : syracuseStep 3096569 = 2322427) B2322427
theorem B2064379 : Blo 2063435 2064379 := bstep (se 1 (by rfl) ⟨1548284, by rfl⟩ : syracuseStep 2064379 = 3096569) B3096569
theorem B5027789 : Blo 2063435 5027789 := bbase (se 3 (by rfl) ⟨942710, by rfl⟩ : syracuseStep 5027789 = 1885421) (by norm_num)
theorem B13407437 : Blo 2063435 13407437 := bstep (se 3 (by rfl) ⟨2513894, by rfl⟩ : syracuseStep 13407437 = 5027789) B5027789
theorem B8938291 : Blo 2063435 8938291 := bstep (se 1 (by rfl) ⟨6703718, by rfl⟩ : syracuseStep 8938291 = 13407437) B13407437
theorem B11917721 : Blo 2063435 11917721 := bstep (se 2 (by rfl) ⟨4469145, by rfl⟩ : syracuseStep 11917721 = 8938291) B8938291
theorem B7945147 : Blo 2063435 7945147 := bstep (se 1 (by rfl) ⟨5958860, by rfl⟩ : syracuseStep 7945147 = 11917721) B11917721
theorem B10593529 : Blo 2063435 10593529 := bstep (se 2 (by rfl) ⟨3972573, by rfl⟩ : syracuseStep 10593529 = 7945147) B7945147
theorem B225995285 : Blo 2063435 225995285 := bstep (se 6 (by rfl) ⟨5296764, by rfl⟩ : syracuseStep 225995285 = 10593529) B10593529
theorem B602654093 : Blo 2063435 602654093 := bstep (se 3 (by rfl) ⟨112997642, by rfl⟩ : syracuseStep 602654093 = 225995285) B225995285
theorem B401769395 : Blo 2063435 401769395 := bstep (se 1 (by rfl) ⟨301327046, by rfl⟩ : syracuseStep 401769395 = 602654093) B602654093
theorem B267846263 : Blo 2063435 267846263 := bstep (se 1 (by rfl) ⟨200884697, by rfl⟩ : syracuseStep 267846263 = 401769395) B401769395
theorem B178564175 : Blo 2063435 178564175 := bstep (se 1 (by rfl) ⟨133923131, by rfl⟩ : syracuseStep 178564175 = 267846263) B267846263
theorem B119042783 : Blo 2063435 119042783 := bstep (se 1 (by rfl) ⟨89282087, by rfl⟩ : syracuseStep 119042783 = 178564175) B178564175
theorem B79361855 : Blo 2063435 79361855 := bstep (se 1 (by rfl) ⟨59521391, by rfl⟩ : syracuseStep 79361855 = 119042783) B119042783
theorem B52907903 : Blo 2063435 52907903 := bstep (se 1 (by rfl) ⟨39680927, by rfl⟩ : syracuseStep 52907903 = 79361855) B79361855
theorem B35271935 : Blo 2063435 35271935 := bstep (se 1 (by rfl) ⟨26453951, by rfl⟩ : syracuseStep 35271935 = 52907903) B52907903
theorem B23514623 : Blo 2063435 23514623 := bstep (se 1 (by rfl) ⟨17635967, by rfl⟩ : syracuseStep 23514623 = 35271935) B35271935
theorem B15676415 : Blo 2063435 15676415 := bstep (se 1 (by rfl) ⟨11757311, by rfl⟩ : syracuseStep 15676415 = 23514623) B23514623
theorem B10450943 : Blo 2063435 10450943 := bstep (se 1 (by rfl) ⟨7838207, by rfl⟩ : syracuseStep 10450943 = 15676415) B15676415
theorem B6967295 : Blo 2063435 6967295 := bstep (se 1 (by rfl) ⟨5225471, by rfl⟩ : syracuseStep 6967295 = 10450943) B10450943
theorem B4644863 : Blo 2063435 4644863 := bstep (se 1 (by rfl) ⟨3483647, by rfl⟩ : syracuseStep 4644863 = 6967295) B6967295
theorem B3096575 : Blo 2063435 3096575 := bstep (se 1 (by rfl) ⟨2322431, by rfl⟩ : syracuseStep 3096575 = 4644863) B4644863
theorem B2064383 : Blo 2063435 2064383 := bstep (se 1 (by rfl) ⟨1548287, by rfl⟩ : syracuseStep 2064383 = 3096575) B3096575
theorem B3096581 : Blo 2063435 3096581 := bbase (se 4 (by rfl) ⟨290304, by rfl⟩ : syracuseStep 3096581 = 580609) (by norm_num)
theorem B2064387 : Blo 2063435 2064387 := bstep (se 1 (by rfl) ⟨1548290, by rfl⟩ : syracuseStep 2064387 = 3096581) B3096581
theorem B3483661 : Blo 2063435 3483661 := bbase (se 3 (by rfl) ⟨653186, by rfl⟩ : syracuseStep 3483661 = 1306373) (by norm_num)
theorem B4644881 : Blo 2063435 4644881 := bstep (se 2 (by rfl) ⟨1741830, by rfl⟩ : syracuseStep 4644881 = 3483661) B3483661
theorem B3096587 : Blo 2063435 3096587 := bstep (se 1 (by rfl) ⟨2322440, by rfl⟩ : syracuseStep 3096587 = 4644881) B4644881
theorem B2064391 : Blo 2063435 2064391 := bstep (se 1 (by rfl) ⟨1548293, by rfl⟩ : syracuseStep 2064391 = 3096587) B3096587
theorem B2322445 : Blo 2063435 2322445 := bbase (se 3 (by rfl) ⟨435458, by rfl⟩ : syracuseStep 2322445 = 870917) (by norm_num)
theorem B3096593 : Blo 2063435 3096593 := bstep (se 2 (by rfl) ⟨1161222, by rfl⟩ : syracuseStep 3096593 = 2322445) B2322445
theorem B2064395 : Blo 2063435 2064395 := bstep (se 1 (by rfl) ⟨1548296, by rfl⟩ : syracuseStep 2064395 = 3096593) B3096593
theorem B6967349 : Blo 2063435 6967349 := bbase (se 5 (by rfl) ⟨326594, by rfl⟩ : syracuseStep 6967349 = 653189) (by norm_num)
theorem B4644899 : Blo 2063435 4644899 := bstep (se 1 (by rfl) ⟨3483674, by rfl⟩ : syracuseStep 4644899 = 6967349) B6967349
theorem B3096599 : Blo 2063435 3096599 := bstep (se 1 (by rfl) ⟨2322449, by rfl⟩ : syracuseStep 3096599 = 4644899) B4644899
theorem B2064399 : Blo 2063435 2064399 := bstep (se 1 (by rfl) ⟨1548299, by rfl⟩ : syracuseStep 2064399 = 3096599) B3096599
theorem B3096605 : Blo 2063435 3096605 := bbase (se 3 (by rfl) ⟨580613, by rfl⟩ : syracuseStep 3096605 = 1161227) (by norm_num)
theorem B2064403 : Blo 2063435 2064403 := bstep (se 1 (by rfl) ⟨1548302, by rfl⟩ : syracuseStep 2064403 = 3096605) B3096605
theorem B4644917 : Blo 2063435 4644917 := bbase (se 5 (by rfl) ⟨217730, by rfl⟩ : syracuseStep 4644917 = 435461) (by norm_num)
theorem B3096611 : Blo 2063435 3096611 := bstep (se 1 (by rfl) ⟨2322458, by rfl⟩ : syracuseStep 3096611 = 4644917) B4644917
theorem B2064407 : Blo 2063435 2064407 := bstep (se 1 (by rfl) ⟨1548305, by rfl⟩ : syracuseStep 2064407 = 3096611) B3096611
theorem B7440277 : Blo 2063435 7440277 := bbase (se 6 (by rfl) ⟨174381, by rfl⟩ : syracuseStep 7440277 = 348763) (by norm_num)
theorem B9920369 : Blo 2063435 9920369 := bstep (se 2 (by rfl) ⟨3720138, by rfl⟩ : syracuseStep 9920369 = 7440277) B7440277
theorem B6613579 : Blo 2063435 6613579 := bstep (se 1 (by rfl) ⟨4960184, by rfl⟩ : syracuseStep 6613579 = 9920369) B9920369
theorem B8818105 : Blo 2063435 8818105 := bstep (se 2 (by rfl) ⟨3306789, by rfl⟩ : syracuseStep 8818105 = 6613579) B6613579
theorem B11757473 : Blo 2063435 11757473 := bstep (se 2 (by rfl) ⟨4409052, by rfl⟩ : syracuseStep 11757473 = 8818105) B8818105
theorem B7838315 : Blo 2063435 7838315 := bstep (se 1 (by rfl) ⟨5878736, by rfl⟩ : syracuseStep 7838315 = 11757473) B11757473
theorem B5225543 : Blo 2063435 5225543 := bstep (se 1 (by rfl) ⟨3919157, by rfl⟩ : syracuseStep 5225543 = 7838315) B7838315
theorem B3483695 : Blo 2063435 3483695 := bstep (se 1 (by rfl) ⟨2612771, by rfl⟩ : syracuseStep 3483695 = 5225543) B5225543
theorem B2322463 : Blo 2063435 2322463 := bstep (se 1 (by rfl) ⟨1741847, by rfl⟩ : syracuseStep 2322463 = 3483695) B3483695
theorem B3096617 : Blo 2063435 3096617 := bstep (se 2 (by rfl) ⟨1161231, by rfl⟩ : syracuseStep 3096617 = 2322463) B2322463
theorem B2064411 : Blo 2063435 2064411 := bstep (se 1 (by rfl) ⟨1548308, by rfl⟩ : syracuseStep 2064411 = 3096617) B3096617
theorem B2790109 : Blo 2063435 2790109 := bbase (se 3 (by rfl) ⟨523145, by rfl⟩ : syracuseStep 2790109 = 1046291) (by norm_num)
theorem B14880581 : Blo 2063435 14880581 := bstep (se 4 (by rfl) ⟨1395054, by rfl⟩ : syracuseStep 14880581 = 2790109) B2790109
theorem B9920387 : Blo 2063435 9920387 := bstep (se 1 (by rfl) ⟨7440290, by rfl⟩ : syracuseStep 9920387 = 14880581) B14880581
theorem B6613591 : Blo 2063435 6613591 := bstep (se 1 (by rfl) ⟨4960193, by rfl⟩ : syracuseStep 6613591 = 9920387) B9920387
theorem B8818121 : Blo 2063435 8818121 := bstep (se 2 (by rfl) ⟨3306795, by rfl⟩ : syracuseStep 8818121 = 6613591) B6613591
theorem B5878747 : Blo 2063435 5878747 := bstep (se 1 (by rfl) ⟨4409060, by rfl⟩ : syracuseStep 5878747 = 8818121) B8818121
theorem B7838329 : Blo 2063435 7838329 := bstep (se 2 (by rfl) ⟨2939373, by rfl⟩ : syracuseStep 7838329 = 5878747) B5878747
theorem B10451105 : Blo 2063435 10451105 := bstep (se 2 (by rfl) ⟨3919164, by rfl⟩ : syracuseStep 10451105 = 7838329) B7838329
theorem B6967403 : Blo 2063435 6967403 := bstep (se 1 (by rfl) ⟨5225552, by rfl⟩ : syracuseStep 6967403 = 10451105) B10451105
theorem B4644935 : Blo 2063435 4644935 := bstep (se 1 (by rfl) ⟨3483701, by rfl⟩ : syracuseStep 4644935 = 6967403) B6967403
theorem B3096623 : Blo 2063435 3096623 := bstep (se 1 (by rfl) ⟨2322467, by rfl⟩ : syracuseStep 3096623 = 4644935) B4644935
theorem B2064415 : Blo 2063435 2064415 := bstep (se 1 (by rfl) ⟨1548311, by rfl⟩ : syracuseStep 2064415 = 3096623) B3096623
theorem B3096629 : Blo 2063435 3096629 := bbase (se 5 (by rfl) ⟨145154, by rfl⟩ : syracuseStep 3096629 = 290309) (by norm_num)
theorem B2064419 : Blo 2063435 2064419 := bstep (se 1 (by rfl) ⟨1548314, by rfl⟩ : syracuseStep 2064419 = 3096629) B3096629
theorem B5225573 : Blo 2063435 5225573 := bbase (se 4 (by rfl) ⟨489897, by rfl⟩ : syracuseStep 5225573 = 979795) (by norm_num)
theorem B3483715 : Blo 2063435 3483715 := bstep (se 1 (by rfl) ⟨2612786, by rfl⟩ : syracuseStep 3483715 = 5225573) B5225573
theorem B4644953 : Blo 2063435 4644953 := bstep (se 2 (by rfl) ⟨1741857, by rfl⟩ : syracuseStep 4644953 = 3483715) B3483715
theorem B3096635 : Blo 2063435 3096635 := bstep (se 1 (by rfl) ⟨2322476, by rfl⟩ : syracuseStep 3096635 = 4644953) B4644953
theorem B2064423 : Blo 2063435 2064423 := bstep (se 1 (by rfl) ⟨1548317, by rfl⟩ : syracuseStep 2064423 = 3096635) B3096635
theorem B2322481 : Blo 2063435 2322481 := bbase (se 2 (by rfl) ⟨870930, by rfl⟩ : syracuseStep 2322481 = 1741861) (by norm_num)
theorem B3096641 : Blo 2063435 3096641 := bstep (se 2 (by rfl) ⟨1161240, by rfl⟩ : syracuseStep 3096641 = 2322481) B2322481
theorem B2064427 : Blo 2063435 2064427 := bstep (se 1 (by rfl) ⟨1548320, by rfl⟩ : syracuseStep 2064427 = 3096641) B3096641
theorem B4185197 : Blo 2063435 4185197 := bbase (se 3 (by rfl) ⟨784724, by rfl⟩ : syracuseStep 4185197 = 1569449) (by norm_num)
theorem B2790131 : Blo 2063435 2790131 := bstep (se 1 (by rfl) ⟨2092598, by rfl⟩ : syracuseStep 2790131 = 4185197) B4185197
theorem B7440349 : Blo 2063435 7440349 := bstep (se 3 (by rfl) ⟨1395065, by rfl⟩ : syracuseStep 7440349 = 2790131) B2790131
theorem B9920465 : Blo 2063435 9920465 := bstep (se 2 (by rfl) ⟨3720174, by rfl⟩ : syracuseStep 9920465 = 7440349) B7440349
theorem B6613643 : Blo 2063435 6613643 := bstep (se 1 (by rfl) ⟨4960232, by rfl⟩ : syracuseStep 6613643 = 9920465) B9920465
theorem B4409095 : Blo 2063435 4409095 := bstep (se 1 (by rfl) ⟨3306821, by rfl⟩ : syracuseStep 4409095 = 6613643) B6613643
theorem B5878793 : Blo 2063435 5878793 := bstep (se 2 (by rfl) ⟨2204547, by rfl⟩ : syracuseStep 5878793 = 4409095) B4409095
theorem B3919195 : Blo 2063435 3919195 := bstep (se 1 (by rfl) ⟨2939396, by rfl⟩ : syracuseStep 3919195 = 5878793) B5878793
theorem B5225593 : Blo 2063435 5225593 := bstep (se 2 (by rfl) ⟨1959597, by rfl⟩ : syracuseStep 5225593 = 3919195) B3919195
theorem B6967457 : Blo 2063435 6967457 := bstep (se 2 (by rfl) ⟨2612796, by rfl⟩ : syracuseStep 6967457 = 5225593) B5225593
theorem B4644971 : Blo 2063435 4644971 := bstep (se 1 (by rfl) ⟨3483728, by rfl⟩ : syracuseStep 4644971 = 6967457) B6967457
theorem B3096647 : Blo 2063435 3096647 := bstep (se 1 (by rfl) ⟨2322485, by rfl⟩ : syracuseStep 3096647 = 4644971) B4644971
theorem B2064431 : Blo 2063435 2064431 := bstep (se 1 (by rfl) ⟨1548323, by rfl⟩ : syracuseStep 2064431 = 3096647) B3096647
theorem B3096653 : Blo 2063435 3096653 := bbase (se 3 (by rfl) ⟨580622, by rfl⟩ : syracuseStep 3096653 = 1161245) (by norm_num)
theorem B2064435 : Blo 2063435 2064435 := bstep (se 1 (by rfl) ⟨1548326, by rfl⟩ : syracuseStep 2064435 = 3096653) B3096653
theorem B4644989 : Blo 2063435 4644989 := bbase (se 3 (by rfl) ⟨870935, by rfl⟩ : syracuseStep 4644989 = 1741871) (by norm_num)
theorem B3096659 : Blo 2063435 3096659 := bstep (se 1 (by rfl) ⟨2322494, by rfl⟩ : syracuseStep 3096659 = 4644989) B4644989
theorem B2064439 : Blo 2063435 2064439 := bstep (se 1 (by rfl) ⟨1548329, by rfl⟩ : syracuseStep 2064439 = 3096659) B3096659
theorem B3483749 : Blo 2063435 3483749 := bbase (se 4 (by rfl) ⟨326601, by rfl⟩ : syracuseStep 3483749 = 653203) (by norm_num)
theorem B2322499 : Blo 2063435 2322499 := bstep (se 1 (by rfl) ⟨1741874, by rfl⟩ : syracuseStep 2322499 = 3483749) B3483749
theorem B3096665 : Blo 2063435 3096665 := bstep (se 2 (by rfl) ⟨1161249, by rfl⟩ : syracuseStep 3096665 = 2322499) B2322499
theorem B2064443 : Blo 2063435 2064443 := bstep (se 1 (by rfl) ⟨1548332, by rfl⟩ : syracuseStep 2064443 = 3096665) B3096665
theorem B16740917 : Blo 2063435 16740917 := bbase (se 5 (by rfl) ⟨784730, by rfl⟩ : syracuseStep 16740917 = 1569461) (by norm_num)
theorem B11160611 : Blo 2063435 11160611 := bstep (se 1 (by rfl) ⟨8370458, by rfl⟩ : syracuseStep 11160611 = 16740917) B16740917
theorem B7440407 : Blo 2063435 7440407 := bstep (se 1 (by rfl) ⟨5580305, by rfl⟩ : syracuseStep 7440407 = 11160611) B11160611
theorem B4960271 : Blo 2063435 4960271 := bstep (se 1 (by rfl) ⟨3720203, by rfl⟩ : syracuseStep 4960271 = 7440407) B7440407
theorem B3306847 : Blo 2063435 3306847 := bstep (se 1 (by rfl) ⟨2480135, by rfl⟩ : syracuseStep 3306847 = 4960271) B4960271
theorem B4409129 : Blo 2063435 4409129 := bstep (se 2 (by rfl) ⟨1653423, by rfl⟩ : syracuseStep 4409129 = 3306847) B3306847
theorem B2939419 : Blo 2063435 2939419 := bstep (se 1 (by rfl) ⟨2204564, by rfl⟩ : syracuseStep 2939419 = 4409129) B4409129
theorem B15676901 : Blo 2063435 15676901 := bstep (se 4 (by rfl) ⟨1469709, by rfl⟩ : syracuseStep 15676901 = 2939419) B2939419
theorem B10451267 : Blo 2063435 10451267 := bstep (se 1 (by rfl) ⟨7838450, by rfl⟩ : syracuseStep 10451267 = 15676901) B15676901
theorem B6967511 : Blo 2063435 6967511 := bstep (se 1 (by rfl) ⟨5225633, by rfl⟩ : syracuseStep 6967511 = 10451267) B10451267
theorem B4645007 : Blo 2063435 4645007 := bstep (se 1 (by rfl) ⟨3483755, by rfl⟩ : syracuseStep 4645007 = 6967511) B6967511
theorem B3096671 : Blo 2063435 3096671 := bstep (se 1 (by rfl) ⟨2322503, by rfl⟩ : syracuseStep 3096671 = 4645007) B4645007
theorem B2064447 : Blo 2063435 2064447 := bstep (se 1 (by rfl) ⟨1548335, by rfl⟩ : syracuseStep 2064447 = 3096671) B3096671
theorem B3096677 : Blo 2063435 3096677 := bbase (se 4 (by rfl) ⟨290313, by rfl⟩ : syracuseStep 3096677 = 580627) (by norm_num)
theorem B2064451 : Blo 2063435 2064451 := bstep (se 1 (by rfl) ⟨1548338, by rfl⟩ : syracuseStep 2064451 = 3096677) B3096677
theorem B7440437 : Blo 2063435 7440437 := bbase (se 5 (by rfl) ⟨348770, by rfl⟩ : syracuseStep 7440437 = 697541) (by norm_num)
theorem B4960291 : Blo 2063435 4960291 := bstep (se 1 (by rfl) ⟨3720218, by rfl⟩ : syracuseStep 4960291 = 7440437) B7440437
theorem B6613721 : Blo 2063435 6613721 := bstep (se 2 (by rfl) ⟨2480145, by rfl⟩ : syracuseStep 6613721 = 4960291) B4960291
theorem B4409147 : Blo 2063435 4409147 := bstep (se 1 (by rfl) ⟨3306860, by rfl⟩ : syracuseStep 4409147 = 6613721) B6613721
theorem B2939431 : Blo 2063435 2939431 := bstep (se 1 (by rfl) ⟨2204573, by rfl⟩ : syracuseStep 2939431 = 4409147) B4409147
theorem B3919241 : Blo 2063435 3919241 := bstep (se 2 (by rfl) ⟨1469715, by rfl⟩ : syracuseStep 3919241 = 2939431) B2939431
theorem B2612827 : Blo 2063435 2612827 := bstep (se 1 (by rfl) ⟨1959620, by rfl⟩ : syracuseStep 2612827 = 3919241) B3919241
theorem B3483769 : Blo 2063435 3483769 := bstep (se 2 (by rfl) ⟨1306413, by rfl⟩ : syracuseStep 3483769 = 2612827) B2612827
theorem B4645025 : Blo 2063435 4645025 := bstep (se 2 (by rfl) ⟨1741884, by rfl⟩ : syracuseStep 4645025 = 3483769) B3483769
theorem B3096683 : Blo 2063435 3096683 := bstep (se 1 (by rfl) ⟨2322512, by rfl⟩ : syracuseStep 3096683 = 4645025) B4645025
theorem B2064455 : Blo 2063435 2064455 := bstep (se 1 (by rfl) ⟨1548341, by rfl⟩ : syracuseStep 2064455 = 3096683) B3096683
theorem B2322517 : Blo 2063435 2322517 := bbase (se 8 (by rfl) ⟨13608, by rfl⟩ : syracuseStep 2322517 = 27217) (by norm_num)
theorem B3096689 : Blo 2063435 3096689 := bstep (se 2 (by rfl) ⟨1161258, by rfl⟩ : syracuseStep 3096689 = 2322517) B2322517
theorem B2064459 : Blo 2063435 2064459 := bstep (se 1 (by rfl) ⟨1548344, by rfl⟩ : syracuseStep 2064459 = 3096689) B3096689
theorem B2612837 : Blo 2063435 2612837 := bbase (se 4 (by rfl) ⟨244953, by rfl⟩ : syracuseStep 2612837 = 489907) (by norm_num)
theorem B6967565 : Blo 2063435 6967565 := bstep (se 3 (by rfl) ⟨1306418, by rfl⟩ : syracuseStep 6967565 = 2612837) B2612837
theorem B4645043 : Blo 2063435 4645043 := bstep (se 1 (by rfl) ⟨3483782, by rfl⟩ : syracuseStep 4645043 = 6967565) B6967565
theorem B3096695 : Blo 2063435 3096695 := bstep (se 1 (by rfl) ⟨2322521, by rfl⟩ : syracuseStep 3096695 = 4645043) B4645043
theorem B2064463 : Blo 2063435 2064463 := bstep (se 1 (by rfl) ⟨1548347, by rfl⟩ : syracuseStep 2064463 = 3096695) B3096695
theorem B3096701 : Blo 2063435 3096701 := bbase (se 3 (by rfl) ⟨580631, by rfl⟩ : syracuseStep 3096701 = 1161263) (by norm_num)
theorem B2064467 : Blo 2063435 2064467 := bstep (se 1 (by rfl) ⟨1548350, by rfl⟩ : syracuseStep 2064467 = 3096701) B3096701
theorem B4645061 : Blo 2063435 4645061 := bbase (se 4 (by rfl) ⟨435474, by rfl⟩ : syracuseStep 4645061 = 870949) (by norm_num)
theorem B3096707 : Blo 2063435 3096707 := bstep (se 1 (by rfl) ⟨2322530, by rfl⟩ : syracuseStep 3096707 = 4645061) B4645061
theorem B2064471 : Blo 2063435 2064471 := bstep (se 1 (by rfl) ⟨1548353, by rfl⟩ : syracuseStep 2064471 = 3096707) B3096707
theorem B9920677 : Blo 2063435 9920677 := bbase (se 4 (by rfl) ⟨930063, by rfl⟩ : syracuseStep 9920677 = 1860127) (by norm_num)
theorem B13227569 : Blo 2063435 13227569 := bstep (se 2 (by rfl) ⟨4960338, by rfl⟩ : syracuseStep 13227569 = 9920677) B9920677
theorem B8818379 : Blo 2063435 8818379 := bstep (se 1 (by rfl) ⟨6613784, by rfl⟩ : syracuseStep 8818379 = 13227569) B13227569
theorem B5878919 : Blo 2063435 5878919 := bstep (se 1 (by rfl) ⟨4409189, by rfl⟩ : syracuseStep 5878919 = 8818379) B8818379
theorem B3919279 : Blo 2063435 3919279 := bstep (se 1 (by rfl) ⟨2939459, by rfl⟩ : syracuseStep 3919279 = 5878919) B5878919
theorem B5225705 : Blo 2063435 5225705 := bstep (se 2 (by rfl) ⟨1959639, by rfl⟩ : syracuseStep 5225705 = 3919279) B3919279
theorem B3483803 : Blo 2063435 3483803 := bstep (se 1 (by rfl) ⟨2612852, by rfl⟩ : syracuseStep 3483803 = 5225705) B5225705
theorem B2322535 : Blo 2063435 2322535 := bstep (se 1 (by rfl) ⟨1741901, by rfl⟩ : syracuseStep 2322535 = 3483803) B3483803
theorem B3096713 : Blo 2063435 3096713 := bstep (se 2 (by rfl) ⟨1161267, by rfl⟩ : syracuseStep 3096713 = 2322535) B2322535
theorem B2064475 : Blo 2063435 2064475 := bstep (se 1 (by rfl) ⟨1548356, by rfl⟩ : syracuseStep 2064475 = 3096713) B3096713
theorem B10451429 : Blo 2063435 10451429 := bbase (se 4 (by rfl) ⟨979821, by rfl⟩ : syracuseStep 10451429 = 1959643) (by norm_num)
theorem B6967619 : Blo 2063435 6967619 := bstep (se 1 (by rfl) ⟨5225714, by rfl⟩ : syracuseStep 6967619 = 10451429) B10451429
theorem B4645079 : Blo 2063435 4645079 := bstep (se 1 (by rfl) ⟨3483809, by rfl⟩ : syracuseStep 4645079 = 6967619) B6967619
theorem B3096719 : Blo 2063435 3096719 := bstep (se 1 (by rfl) ⟨2322539, by rfl⟩ : syracuseStep 3096719 = 4645079) B4645079
theorem B2064479 : Blo 2063435 2064479 := bstep (se 1 (by rfl) ⟨1548359, by rfl⟩ : syracuseStep 2064479 = 3096719) B3096719
theorem B3096725 : Blo 2063435 3096725 := bbase (se 6 (by rfl) ⟨72579, by rfl⟩ : syracuseStep 3096725 = 145159) (by norm_num)
theorem B2064483 : Blo 2063435 2064483 := bstep (se 1 (by rfl) ⟨1548362, by rfl⟩ : syracuseStep 2064483 = 3096725) B3096725
theorem B53632469 : Blo 2063435 53632469 := bbase (se 7 (by rfl) ⟨628505, by rfl⟩ : syracuseStep 53632469 = 1257011) (by norm_num)
theorem B35754979 : Blo 2063435 35754979 := bstep (se 1 (by rfl) ⟨26816234, by rfl⟩ : syracuseStep 35754979 = 53632469) B53632469
theorem B47673305 : Blo 2063435 47673305 := bstep (se 2 (by rfl) ⟨17877489, by rfl⟩ : syracuseStep 47673305 = 35754979) B35754979
theorem B31782203 : Blo 2063435 31782203 := bstep (se 1 (by rfl) ⟨23836652, by rfl⟩ : syracuseStep 31782203 = 47673305) B47673305
theorem B21188135 : Blo 2063435 21188135 := bstep (se 1 (by rfl) ⟨15891101, by rfl⟩ : syracuseStep 21188135 = 31782203) B31782203
theorem B14125423 : Blo 2063435 14125423 := bstep (se 1 (by rfl) ⟨10594067, by rfl⟩ : syracuseStep 14125423 = 21188135) B21188135
theorem B18833897 : Blo 2063435 18833897 := bstep (se 2 (by rfl) ⟨7062711, by rfl⟩ : syracuseStep 18833897 = 14125423) B14125423
theorem B12555931 : Blo 2063435 12555931 := bstep (se 1 (by rfl) ⟨9416948, by rfl⟩ : syracuseStep 12555931 = 18833897) B18833897
theorem B16741241 : Blo 2063435 16741241 := bstep (se 2 (by rfl) ⟨6277965, by rfl⟩ : syracuseStep 16741241 = 12555931) B12555931
theorem B11160827 : Blo 2063435 11160827 := bstep (se 1 (by rfl) ⟨8370620, by rfl⟩ : syracuseStep 11160827 = 16741241) B16741241
theorem B7440551 : Blo 2063435 7440551 := bstep (se 1 (by rfl) ⟨5580413, by rfl⟩ : syracuseStep 7440551 = 11160827) B11160827
theorem B4960367 : Blo 2063435 4960367 := bstep (se 1 (by rfl) ⟨3720275, by rfl⟩ : syracuseStep 4960367 = 7440551) B7440551
theorem B3306911 : Blo 2063435 3306911 := bstep (se 1 (by rfl) ⟨2480183, by rfl⟩ : syracuseStep 3306911 = 4960367) B4960367
theorem B8818429 : Blo 2063435 8818429 := bstep (se 3 (by rfl) ⟨1653455, by rfl⟩ : syracuseStep 8818429 = 3306911) B3306911
theorem B11757905 : Blo 2063435 11757905 := bstep (se 2 (by rfl) ⟨4409214, by rfl⟩ : syracuseStep 11757905 = 8818429) B8818429
theorem B7838603 : Blo 2063435 7838603 := bstep (se 1 (by rfl) ⟨5878952, by rfl⟩ : syracuseStep 7838603 = 11757905) B11757905
theorem B5225735 : Blo 2063435 5225735 := bstep (se 1 (by rfl) ⟨3919301, by rfl⟩ : syracuseStep 5225735 = 7838603) B7838603
theorem B3483823 : Blo 2063435 3483823 := bstep (se 1 (by rfl) ⟨2612867, by rfl⟩ : syracuseStep 3483823 = 5225735) B5225735
theorem B4645097 : Blo 2063435 4645097 := bstep (se 2 (by rfl) ⟨1741911, by rfl⟩ : syracuseStep 4645097 = 3483823) B3483823
theorem B3096731 : Blo 2063435 3096731 := bstep (se 1 (by rfl) ⟨2322548, by rfl⟩ : syracuseStep 3096731 = 4645097) B4645097
theorem B2064487 : Blo 2063435 2064487 := bstep (se 1 (by rfl) ⟨1548365, by rfl⟩ : syracuseStep 2064487 = 3096731) B3096731
theorem B2322553 : Blo 2063435 2322553 := bbase (se 2 (by rfl) ⟨870957, by rfl⟩ : syracuseStep 2322553 = 1741915) (by norm_num)
theorem B3096737 : Blo 2063435 3096737 := bstep (se 2 (by rfl) ⟨1161276, by rfl⟩ : syracuseStep 3096737 = 2322553) B2322553
theorem B2064491 : Blo 2063435 2064491 := bstep (se 1 (by rfl) ⟨1548368, by rfl⟩ : syracuseStep 2064491 = 3096737) B3096737
theorem B21188213 : Blo 2063435 21188213 := bbase (se 5 (by rfl) ⟨993197, by rfl⟩ : syracuseStep 21188213 = 1986395) (by norm_num)
theorem B14125475 : Blo 2063435 14125475 := bstep (se 1 (by rfl) ⟨10594106, by rfl⟩ : syracuseStep 14125475 = 21188213) B21188213
theorem B9416983 : Blo 2063435 9416983 := bstep (se 1 (by rfl) ⟨7062737, by rfl⟩ : syracuseStep 9416983 = 14125475) B14125475
theorem B12555977 : Blo 2063435 12555977 := bstep (se 2 (by rfl) ⟨4708491, by rfl⟩ : syracuseStep 12555977 = 9416983) B9416983
theorem B33482605 : Blo 2063435 33482605 := bstep (se 3 (by rfl) ⟨6277988, by rfl⟩ : syracuseStep 33482605 = 12555977) B12555977
theorem B44643473 : Blo 2063435 44643473 := bstep (se 2 (by rfl) ⟨16741302, by rfl⟩ : syracuseStep 44643473 = 33482605) B33482605
theorem B29762315 : Blo 2063435 29762315 := bstep (se 1 (by rfl) ⟨22321736, by rfl⟩ : syracuseStep 29762315 = 44643473) B44643473
theorem B19841543 : Blo 2063435 19841543 := bstep (se 1 (by rfl) ⟨14881157, by rfl⟩ : syracuseStep 19841543 = 29762315) B29762315
theorem B13227695 : Blo 2063435 13227695 := bstep (se 1 (by rfl) ⟨9920771, by rfl⟩ : syracuseStep 13227695 = 19841543) B19841543
theorem B8818463 : Blo 2063435 8818463 := bstep (se 1 (by rfl) ⟨6613847, by rfl⟩ : syracuseStep 8818463 = 13227695) B13227695
theorem B5878975 : Blo 2063435 5878975 := bstep (se 1 (by rfl) ⟨4409231, by rfl⟩ : syracuseStep 5878975 = 8818463) B8818463
theorem B7838633 : Blo 2063435 7838633 := bstep (se 2 (by rfl) ⟨2939487, by rfl⟩ : syracuseStep 7838633 = 5878975) B5878975
theorem B5225755 : Blo 2063435 5225755 := bstep (se 1 (by rfl) ⟨3919316, by rfl⟩ : syracuseStep 5225755 = 7838633) B7838633
theorem B6967673 : Blo 2063435 6967673 := bstep (se 2 (by rfl) ⟨2612877, by rfl⟩ : syracuseStep 6967673 = 5225755) B5225755
theorem B4645115 : Blo 2063435 4645115 := bstep (se 1 (by rfl) ⟨3483836, by rfl⟩ : syracuseStep 4645115 = 6967673) B6967673
theorem B3096743 : Blo 2063435 3096743 := bstep (se 1 (by rfl) ⟨2322557, by rfl⟩ : syracuseStep 3096743 = 4645115) B4645115
theorem B2064495 : Blo 2063435 2064495 := bstep (se 1 (by rfl) ⟨1548371, by rfl⟩ : syracuseStep 2064495 = 3096743) B3096743
theorem B3096749 : Blo 2063435 3096749 := bbase (se 3 (by rfl) ⟨580640, by rfl⟩ : syracuseStep 3096749 = 1161281) (by norm_num)
theorem B2064499 : Blo 2063435 2064499 := bstep (se 1 (by rfl) ⟨1548374, by rfl⟩ : syracuseStep 2064499 = 3096749) B3096749
theorem B4645133 : Blo 2063435 4645133 := bbase (se 3 (by rfl) ⟨870962, by rfl⟩ : syracuseStep 4645133 = 1741925) (by norm_num)
theorem B3096755 : Blo 2063435 3096755 := bstep (se 1 (by rfl) ⟨2322566, by rfl⟩ : syracuseStep 3096755 = 4645133) B4645133
theorem B2064503 : Blo 2063435 2064503 := bstep (se 1 (by rfl) ⟨1548377, by rfl⟩ : syracuseStep 2064503 = 3096755) B3096755
theorem B2612893 : Blo 2063435 2612893 := bbase (se 3 (by rfl) ⟨489917, by rfl⟩ : syracuseStep 2612893 = 979835) (by norm_num)
theorem B3483857 : Blo 2063435 3483857 := bstep (se 2 (by rfl) ⟨1306446, by rfl⟩ : syracuseStep 3483857 = 2612893) B2612893
theorem B2322571 : Blo 2063435 2322571 := bstep (se 1 (by rfl) ⟨1741928, by rfl⟩ : syracuseStep 2322571 = 3483857) B3483857
theorem B3096761 : Blo 2063435 3096761 := bstep (se 2 (by rfl) ⟨1161285, by rfl⟩ : syracuseStep 3096761 = 2322571) B2322571
theorem B2064507 : Blo 2063435 2064507 := bstep (se 1 (by rfl) ⟨1548380, by rfl⟩ : syracuseStep 2064507 = 3096761) B3096761
theorem B3306949 : Blo 2063435 3306949 := bbase (se 4 (by rfl) ⟨310026, by rfl⟩ : syracuseStep 3306949 = 620053) (by norm_num)
theorem B17637061 : Blo 2063435 17637061 := bstep (se 4 (by rfl) ⟨1653474, by rfl⟩ : syracuseStep 17637061 = 3306949) B3306949
theorem B23516081 : Blo 2063435 23516081 := bstep (se 2 (by rfl) ⟨8818530, by rfl⟩ : syracuseStep 23516081 = 17637061) B17637061
theorem B15677387 : Blo 2063435 15677387 := bstep (se 1 (by rfl) ⟨11758040, by rfl⟩ : syracuseStep 15677387 = 23516081) B23516081
theorem B10451591 : Blo 2063435 10451591 := bstep (se 1 (by rfl) ⟨7838693, by rfl⟩ : syracuseStep 10451591 = 15677387) B15677387
theorem B6967727 : Blo 2063435 6967727 := bstep (se 1 (by rfl) ⟨5225795, by rfl⟩ : syracuseStep 6967727 = 10451591) B10451591
theorem B4645151 : Blo 2063435 4645151 := bstep (se 1 (by rfl) ⟨3483863, by rfl⟩ : syracuseStep 4645151 = 6967727) B6967727
theorem B3096767 : Blo 2063435 3096767 := bstep (se 1 (by rfl) ⟨2322575, by rfl⟩ : syracuseStep 3096767 = 4645151) B4645151
theorem B2064511 : Blo 2063435 2064511 := bstep (se 1 (by rfl) ⟨1548383, by rfl⟩ : syracuseStep 2064511 = 3096767) B3096767
theorem B3096773 : Blo 2063435 3096773 := bbase (se 4 (by rfl) ⟨290322, by rfl⟩ : syracuseStep 3096773 = 580645) (by norm_num)
theorem B2064515 : Blo 2063435 2064515 := bstep (se 1 (by rfl) ⟨1548386, by rfl⟩ : syracuseStep 2064515 = 3096773) B3096773
theorem B3483877 : Blo 2063435 3483877 := bbase (se 4 (by rfl) ⟨326613, by rfl⟩ : syracuseStep 3483877 = 653227) (by norm_num)
theorem B4645169 : Blo 2063435 4645169 := bstep (se 2 (by rfl) ⟨1741938, by rfl⟩ : syracuseStep 4645169 = 3483877) B3483877
theorem B3096779 : Blo 2063435 3096779 := bstep (se 1 (by rfl) ⟨2322584, by rfl⟩ : syracuseStep 3096779 = 4645169) B4645169
theorem B2064519 : Blo 2063435 2064519 := bstep (se 1 (by rfl) ⟨1548389, by rfl⟩ : syracuseStep 2064519 = 3096779) B3096779
theorem B2322589 : Blo 2063435 2322589 := bbase (se 3 (by rfl) ⟨435485, by rfl⟩ : syracuseStep 2322589 = 870971) (by norm_num)
theorem B3096785 : Blo 2063435 3096785 := bstep (se 2 (by rfl) ⟨1161294, by rfl⟩ : syracuseStep 3096785 = 2322589) B2322589
theorem B2064523 : Blo 2063435 2064523 := bstep (se 1 (by rfl) ⟨1548392, by rfl⟩ : syracuseStep 2064523 = 3096785) B3096785
theorem B6967781 : Blo 2063435 6967781 := bbase (se 4 (by rfl) ⟨653229, by rfl⟩ : syracuseStep 6967781 = 1306459) (by norm_num)
theorem B4645187 : Blo 2063435 4645187 := bstep (se 1 (by rfl) ⟨3483890, by rfl⟩ : syracuseStep 4645187 = 6967781) B6967781
theorem B3096791 : Blo 2063435 3096791 := bstep (se 1 (by rfl) ⟨2322593, by rfl⟩ : syracuseStep 3096791 = 4645187) B4645187
theorem B2064527 : Blo 2063435 2064527 := bstep (se 1 (by rfl) ⟨1548395, by rfl⟩ : syracuseStep 2064527 = 3096791) B3096791
theorem B3096797 : Blo 2063435 3096797 := bbase (se 3 (by rfl) ⟨580649, by rfl⟩ : syracuseStep 3096797 = 1161299) (by norm_num)
theorem B2064531 : Blo 2063435 2064531 := bstep (se 1 (by rfl) ⟨1548398, by rfl⟩ : syracuseStep 2064531 = 3096797) B3096797
theorem B4645205 : Blo 2063435 4645205 := bbase (se 10 (by rfl) ⟨6804, by rfl⟩ : syracuseStep 4645205 = 13609) (by norm_num)
theorem B3096803 : Blo 2063435 3096803 := bstep (se 1 (by rfl) ⟨2322602, by rfl⟩ : syracuseStep 3096803 = 4645205) B4645205
theorem B2064535 : Blo 2063435 2064535 := bstep (se 1 (by rfl) ⟨1548401, by rfl⟩ : syracuseStep 2064535 = 3096803) B3096803
theorem B4960493 : Blo 2063435 4960493 := bbase (se 3 (by rfl) ⟨930092, by rfl⟩ : syracuseStep 4960493 = 1860185) (by norm_num)
theorem B3306995 : Blo 2063435 3306995 := bstep (se 1 (by rfl) ⟨2480246, by rfl⟩ : syracuseStep 3306995 = 4960493) B4960493
theorem B2204663 : Blo 2063435 2204663 := bstep (se 1 (by rfl) ⟨1653497, by rfl⟩ : syracuseStep 2204663 = 3306995) B3306995
theorem B5879101 : Blo 2063435 5879101 := bstep (se 3 (by rfl) ⟨1102331, by rfl⟩ : syracuseStep 5879101 = 2204663) B2204663
theorem B7838801 : Blo 2063435 7838801 := bstep (se 2 (by rfl) ⟨2939550, by rfl⟩ : syracuseStep 7838801 = 5879101) B5879101
theorem B5225867 : Blo 2063435 5225867 := bstep (se 1 (by rfl) ⟨3919400, by rfl⟩ : syracuseStep 5225867 = 7838801) B7838801
theorem B3483911 : Blo 2063435 3483911 := bstep (se 1 (by rfl) ⟨2612933, by rfl⟩ : syracuseStep 3483911 = 5225867) B5225867
theorem B2322607 : Blo 2063435 2322607 := bstep (se 1 (by rfl) ⟨1741955, by rfl⟩ : syracuseStep 2322607 = 3483911) B3483911
theorem B3096809 : Blo 2063435 3096809 := bstep (se 2 (by rfl) ⟨1161303, by rfl⟩ : syracuseStep 3096809 = 2322607) B2322607
theorem B2064539 : Blo 2063435 2064539 := bstep (se 1 (by rfl) ⟨1548404, by rfl⟩ : syracuseStep 2064539 = 3096809) B3096809
theorem B28251605 : Blo 2063435 28251605 := bbase (se 7 (by rfl) ⟨331073, by rfl⟩ : syracuseStep 28251605 = 662147) (by norm_num)
theorem B18834403 : Blo 2063435 18834403 := bstep (se 1 (by rfl) ⟨14125802, by rfl⟩ : syracuseStep 18834403 = 28251605) B28251605
theorem B25112537 : Blo 2063435 25112537 := bstep (se 2 (by rfl) ⟨9417201, by rfl⟩ : syracuseStep 25112537 = 18834403) B18834403
theorem B16741691 : Blo 2063435 16741691 := bstep (se 1 (by rfl) ⟨12556268, by rfl⟩ : syracuseStep 16741691 = 25112537) B25112537
theorem B11161127 : Blo 2063435 11161127 := bstep (se 1 (by rfl) ⟨8370845, by rfl⟩ : syracuseStep 11161127 = 16741691) B16741691
theorem B7440751 : Blo 2063435 7440751 := bstep (se 1 (by rfl) ⟨5580563, by rfl⟩ : syracuseStep 7440751 = 11161127) B11161127
theorem B39684005 : Blo 2063435 39684005 := bstep (se 4 (by rfl) ⟨3720375, by rfl⟩ : syracuseStep 39684005 = 7440751) B7440751
theorem B26456003 : Blo 2063435 26456003 := bstep (se 1 (by rfl) ⟨19842002, by rfl⟩ : syracuseStep 26456003 = 39684005) B39684005
theorem B17637335 : Blo 2063435 17637335 := bstep (se 1 (by rfl) ⟨13228001, by rfl⟩ : syracuseStep 17637335 = 26456003) B26456003
theorem B11758223 : Blo 2063435 11758223 := bstep (se 1 (by rfl) ⟨8818667, by rfl⟩ : syracuseStep 11758223 = 17637335) B17637335
theorem B7838815 : Blo 2063435 7838815 := bstep (se 1 (by rfl) ⟨5879111, by rfl⟩ : syracuseStep 7838815 = 11758223) B11758223
theorem B10451753 : Blo 2063435 10451753 := bstep (se 2 (by rfl) ⟨3919407, by rfl⟩ : syracuseStep 10451753 = 7838815) B7838815
theorem B6967835 : Blo 2063435 6967835 := bstep (se 1 (by rfl) ⟨5225876, by rfl⟩ : syracuseStep 6967835 = 10451753) B10451753
theorem B4645223 : Blo 2063435 4645223 := bstep (se 1 (by rfl) ⟨3483917, by rfl⟩ : syracuseStep 4645223 = 6967835) B6967835
theorem B3096815 : Blo 2063435 3096815 := bstep (se 1 (by rfl) ⟨2322611, by rfl⟩ : syracuseStep 3096815 = 4645223) B4645223
theorem B2064543 : Blo 2063435 2064543 := bstep (se 1 (by rfl) ⟨1548407, by rfl⟩ : syracuseStep 2064543 = 3096815) B3096815
theorem B3096821 : Blo 2063435 3096821 := bbase (se 5 (by rfl) ⟨145163, by rfl⟩ : syracuseStep 3096821 = 290327) (by norm_num)
theorem B2064547 : Blo 2063435 2064547 := bstep (se 1 (by rfl) ⟨1548410, by rfl⟩ : syracuseStep 2064547 = 3096821) B3096821
theorem B2790293 : Blo 2063435 2790293 := bbase (se 6 (by rfl) ⟨65397, by rfl⟩ : syracuseStep 2790293 = 130795) (by norm_num)
theorem B29763125 : Blo 2063435 29763125 := bstep (se 5 (by rfl) ⟨1395146, by rfl⟩ : syracuseStep 29763125 = 2790293) B2790293
theorem B19842083 : Blo 2063435 19842083 := bstep (se 1 (by rfl) ⟨14881562, by rfl⟩ : syracuseStep 19842083 = 29763125) B29763125
theorem B13228055 : Blo 2063435 13228055 := bstep (se 1 (by rfl) ⟨9921041, by rfl⟩ : syracuseStep 13228055 = 19842083) B19842083
theorem B8818703 : Blo 2063435 8818703 := bstep (se 1 (by rfl) ⟨6614027, by rfl⟩ : syracuseStep 8818703 = 13228055) B13228055
theorem B5879135 : Blo 2063435 5879135 := bstep (se 1 (by rfl) ⟨4409351, by rfl⟩ : syracuseStep 5879135 = 8818703) B8818703
theorem B3919423 : Blo 2063435 3919423 := bstep (se 1 (by rfl) ⟨2939567, by rfl⟩ : syracuseStep 3919423 = 5879135) B5879135
theorem B5225897 : Blo 2063435 5225897 := bstep (se 2 (by rfl) ⟨1959711, by rfl⟩ : syracuseStep 5225897 = 3919423) B3919423
theorem B3483931 : Blo 2063435 3483931 := bstep (se 1 (by rfl) ⟨2612948, by rfl⟩ : syracuseStep 3483931 = 5225897) B5225897
theorem B4645241 : Blo 2063435 4645241 := bstep (se 2 (by rfl) ⟨1741965, by rfl⟩ : syracuseStep 4645241 = 3483931) B3483931
theorem B3096827 : Blo 2063435 3096827 := bstep (se 1 (by rfl) ⟨2322620, by rfl⟩ : syracuseStep 3096827 = 4645241) B4645241
theorem B2064551 : Blo 2063435 2064551 := bstep (se 1 (by rfl) ⟨1548413, by rfl⟩ : syracuseStep 2064551 = 3096827) B3096827
theorem B2322625 : Blo 2063435 2322625 := bbase (se 2 (by rfl) ⟨870984, by rfl⟩ : syracuseStep 2322625 = 1741969) (by norm_num)
theorem B3096833 : Blo 2063435 3096833 := bstep (se 2 (by rfl) ⟨1161312, by rfl⟩ : syracuseStep 3096833 = 2322625) B2322625
theorem B2064555 : Blo 2063435 2064555 := bstep (se 1 (by rfl) ⟨1548416, by rfl⟩ : syracuseStep 2064555 = 3096833) B3096833
theorem B5225917 : Blo 2063435 5225917 := bbase (se 3 (by rfl) ⟨979859, by rfl⟩ : syracuseStep 5225917 = 1959719) (by norm_num)
theorem B6967889 : Blo 2063435 6967889 := bstep (se 2 (by rfl) ⟨2612958, by rfl⟩ : syracuseStep 6967889 = 5225917) B5225917
theorem B4645259 : Blo 2063435 4645259 := bstep (se 1 (by rfl) ⟨3483944, by rfl⟩ : syracuseStep 4645259 = 6967889) B6967889
theorem B3096839 : Blo 2063435 3096839 := bstep (se 1 (by rfl) ⟨2322629, by rfl⟩ : syracuseStep 3096839 = 4645259) B4645259
theorem B2064559 : Blo 2063435 2064559 := bstep (se 1 (by rfl) ⟨1548419, by rfl⟩ : syracuseStep 2064559 = 3096839) B3096839
theorem B3096845 : Blo 2063435 3096845 := bbase (se 3 (by rfl) ⟨580658, by rfl⟩ : syracuseStep 3096845 = 1161317) (by norm_num)
theorem B2064563 : Blo 2063435 2064563 := bstep (se 1 (by rfl) ⟨1548422, by rfl⟩ : syracuseStep 2064563 = 3096845) B3096845
theorem B4645277 : Blo 2063435 4645277 := bbase (se 3 (by rfl) ⟨870989, by rfl⟩ : syracuseStep 4645277 = 1741979) (by norm_num)
theorem B3096851 : Blo 2063435 3096851 := bstep (se 1 (by rfl) ⟨2322638, by rfl⟩ : syracuseStep 3096851 = 4645277) B4645277
theorem B2064567 : Blo 2063435 2064567 := bstep (se 1 (by rfl) ⟨1548425, by rfl⟩ : syracuseStep 2064567 = 3096851) B3096851
theorem B3483965 : Blo 2063435 3483965 := bbase (se 3 (by rfl) ⟨653243, by rfl⟩ : syracuseStep 3483965 = 1306487) (by norm_num)
theorem B2322643 : Blo 2063435 2322643 := bstep (se 1 (by rfl) ⟨1741982, by rfl⟩ : syracuseStep 2322643 = 3483965) B3483965
theorem B3096857 : Blo 2063435 3096857 := bstep (se 2 (by rfl) ⟨1161321, by rfl⟩ : syracuseStep 3096857 = 2322643) B2322643
theorem B2064571 : Blo 2063435 2064571 := bstep (se 1 (by rfl) ⟨1548428, by rfl⟩ : syracuseStep 2064571 = 3096857) B3096857
theorem B2204701 : Blo 2063435 2204701 := bbase (se 3 (by rfl) ⟨413381, by rfl⟩ : syracuseStep 2204701 = 826763) (by norm_num)
theorem B11758405 : Blo 2063435 11758405 := bstep (se 4 (by rfl) ⟨1102350, by rfl⟩ : syracuseStep 11758405 = 2204701) B2204701
theorem B15677873 : Blo 2063435 15677873 := bstep (se 2 (by rfl) ⟨5879202, by rfl⟩ : syracuseStep 15677873 = 11758405) B11758405
theorem B10451915 : Blo 2063435 10451915 := bstep (se 1 (by rfl) ⟨7838936, by rfl⟩ : syracuseStep 10451915 = 15677873) B15677873
theorem B6967943 : Blo 2063435 6967943 := bstep (se 1 (by rfl) ⟨5225957, by rfl⟩ : syracuseStep 6967943 = 10451915) B10451915
theorem B4645295 : Blo 2063435 4645295 := bstep (se 1 (by rfl) ⟨3483971, by rfl⟩ : syracuseStep 4645295 = 6967943) B6967943
theorem B3096863 : Blo 2063435 3096863 := bstep (se 1 (by rfl) ⟨2322647, by rfl⟩ : syracuseStep 3096863 = 4645295) B4645295
theorem B2064575 : Blo 2063435 2064575 := bstep (se 1 (by rfl) ⟨1548431, by rfl⟩ : syracuseStep 2064575 = 3096863) B3096863
theorem B3096869 : Blo 2063435 3096869 := bbase (se 4 (by rfl) ⟨290331, by rfl⟩ : syracuseStep 3096869 = 580663) (by norm_num)
theorem B2064579 : Blo 2063435 2064579 := bstep (se 1 (by rfl) ⟨1548434, by rfl⟩ : syracuseStep 2064579 = 3096869) B3096869
theorem B2612989 : Blo 2063435 2612989 := bbase (se 3 (by rfl) ⟨489935, by rfl⟩ : syracuseStep 2612989 = 979871) (by norm_num)
theorem B3483985 : Blo 2063435 3483985 := bstep (se 2 (by rfl) ⟨1306494, by rfl⟩ : syracuseStep 3483985 = 2612989) B2612989
theorem B4645313 : Blo 2063435 4645313 := bstep (se 2 (by rfl) ⟨1741992, by rfl⟩ : syracuseStep 4645313 = 3483985) B3483985
theorem B3096875 : Blo 2063435 3096875 := bstep (se 1 (by rfl) ⟨2322656, by rfl⟩ : syracuseStep 3096875 = 4645313) B4645313
theorem B2064583 : Blo 2063435 2064583 := bstep (se 1 (by rfl) ⟨1548437, by rfl⟩ : syracuseStep 2064583 = 3096875) B3096875
theorem B2322661 : Blo 2063435 2322661 := bbase (se 4 (by rfl) ⟨217749, by rfl⟩ : syracuseStep 2322661 = 435499) (by norm_num)
theorem B3096881 : Blo 2063435 3096881 := bstep (se 2 (by rfl) ⟨1161330, by rfl⟩ : syracuseStep 3096881 = 2322661) B2322661
theorem B2064587 : Blo 2063435 2064587 := bstep (se 1 (by rfl) ⟨1548440, by rfl⟩ : syracuseStep 2064587 = 3096881) B3096881
theorem B4409437 : Blo 2063435 4409437 := bbase (se 3 (by rfl) ⟨826769, by rfl⟩ : syracuseStep 4409437 = 1653539) (by norm_num)
theorem B5879249 : Blo 2063435 5879249 := bstep (se 2 (by rfl) ⟨2204718, by rfl⟩ : syracuseStep 5879249 = 4409437) B4409437
theorem B3919499 : Blo 2063435 3919499 := bstep (se 1 (by rfl) ⟨2939624, by rfl⟩ : syracuseStep 3919499 = 5879249) B5879249
theorem B2612999 : Blo 2063435 2612999 := bstep (se 1 (by rfl) ⟨1959749, by rfl⟩ : syracuseStep 2612999 = 3919499) B3919499
theorem B6967997 : Blo 2063435 6967997 := bstep (se 3 (by rfl) ⟨1306499, by rfl⟩ : syracuseStep 6967997 = 2612999) B2612999
theorem B4645331 : Blo 2063435 4645331 := bstep (se 1 (by rfl) ⟨3483998, by rfl⟩ : syracuseStep 4645331 = 6967997) B6967997
theorem B3096887 : Blo 2063435 3096887 := bstep (se 1 (by rfl) ⟨2322665, by rfl⟩ : syracuseStep 3096887 = 4645331) B4645331
theorem B2064591 : Blo 2063435 2064591 := bstep (se 1 (by rfl) ⟨1548443, by rfl⟩ : syracuseStep 2064591 = 3096887) B3096887
theorem B3096893 : Blo 2063435 3096893 := bbase (se 3 (by rfl) ⟨580667, by rfl⟩ : syracuseStep 3096893 = 1161335) (by norm_num)
theorem B2064595 : Blo 2063435 2064595 := bstep (se 1 (by rfl) ⟨1548446, by rfl⟩ : syracuseStep 2064595 = 3096893) B3096893
theorem B4645349 : Blo 2063435 4645349 := bbase (se 4 (by rfl) ⟨435501, by rfl⟩ : syracuseStep 4645349 = 871003) (by norm_num)
theorem B3096899 : Blo 2063435 3096899 := bstep (se 1 (by rfl) ⟨2322674, by rfl⟩ : syracuseStep 3096899 = 4645349) B4645349
theorem B2064599 : Blo 2063435 2064599 := bstep (se 1 (by rfl) ⟨1548449, by rfl⟩ : syracuseStep 2064599 = 3096899) B3096899
theorem B5226029 : Blo 2063435 5226029 := bbase (se 3 (by rfl) ⟨979880, by rfl⟩ : syracuseStep 5226029 = 1959761) (by norm_num)
theorem B3484019 : Blo 2063435 3484019 := bstep (se 1 (by rfl) ⟨2613014, by rfl⟩ : syracuseStep 3484019 = 5226029) B5226029
theorem B2322679 : Blo 2063435 2322679 := bstep (se 1 (by rfl) ⟨1742009, by rfl⟩ : syracuseStep 2322679 = 3484019) B3484019
theorem B3096905 : Blo 2063435 3096905 := bstep (se 2 (by rfl) ⟨1161339, by rfl⟩ : syracuseStep 3096905 = 2322679) B2322679
theorem B2064603 : Blo 2063435 2064603 := bstep (se 1 (by rfl) ⟨1548452, by rfl⟩ : syracuseStep 2064603 = 3096905) B3096905
theorem B21189365 : Blo 2063435 21189365 := bbase (se 5 (by rfl) ⟨993251, by rfl⟩ : syracuseStep 21189365 = 1986503) (by norm_num)
theorem B14126243 : Blo 2063435 14126243 := bstep (se 1 (by rfl) ⟨10594682, by rfl⟩ : syracuseStep 14126243 = 21189365) B21189365
theorem B37669981 : Blo 2063435 37669981 := bstep (se 3 (by rfl) ⟨7063121, by rfl⟩ : syracuseStep 37669981 = 14126243) B14126243
theorem B50226641 : Blo 2063435 50226641 := bstep (se 2 (by rfl) ⟨18834990, by rfl⟩ : syracuseStep 50226641 = 37669981) B37669981
theorem B33484427 : Blo 2063435 33484427 := bstep (se 1 (by rfl) ⟨25113320, by rfl⟩ : syracuseStep 33484427 = 50226641) B50226641
theorem B22322951 : Blo 2063435 22322951 := bstep (se 1 (by rfl) ⟨16742213, by rfl⟩ : syracuseStep 22322951 = 33484427) B33484427
theorem B14881967 : Blo 2063435 14881967 := bstep (se 1 (by rfl) ⟨11161475, by rfl⟩ : syracuseStep 14881967 = 22322951) B22322951
theorem B9921311 : Blo 2063435 9921311 := bstep (se 1 (by rfl) ⟨7440983, by rfl⟩ : syracuseStep 9921311 = 14881967) B14881967
theorem B6614207 : Blo 2063435 6614207 := bstep (se 1 (by rfl) ⟨4960655, by rfl⟩ : syracuseStep 6614207 = 9921311) B9921311
theorem B4409471 : Blo 2063435 4409471 := bstep (se 1 (by rfl) ⟨3307103, by rfl⟩ : syracuseStep 4409471 = 6614207) B6614207
theorem B2939647 : Blo 2063435 2939647 := bstep (se 1 (by rfl) ⟨2204735, by rfl⟩ : syracuseStep 2939647 = 4409471) B4409471
theorem B3919529 : Blo 2063435 3919529 := bstep (se 2 (by rfl) ⟨1469823, by rfl⟩ : syracuseStep 3919529 = 2939647) B2939647
theorem B10452077 : Blo 2063435 10452077 := bstep (se 3 (by rfl) ⟨1959764, by rfl⟩ : syracuseStep 10452077 = 3919529) B3919529
theorem B6968051 : Blo 2063435 6968051 := bstep (se 1 (by rfl) ⟨5226038, by rfl⟩ : syracuseStep 6968051 = 10452077) B10452077
theorem B4645367 : Blo 2063435 4645367 := bstep (se 1 (by rfl) ⟨3484025, by rfl⟩ : syracuseStep 4645367 = 6968051) B6968051
theorem B3096911 : Blo 2063435 3096911 := bstep (se 1 (by rfl) ⟨2322683, by rfl⟩ : syracuseStep 3096911 = 4645367) B4645367
theorem B2064607 : Blo 2063435 2064607 := bstep (se 1 (by rfl) ⟨1548455, by rfl⟩ : syracuseStep 2064607 = 3096911) B3096911
theorem B3096917 : Blo 2063435 3096917 := bbase (se 10 (by rfl) ⟨4536, by rfl⟩ : syracuseStep 3096917 = 9073) (by norm_num)
theorem B2064611 : Blo 2063435 2064611 := bstep (se 1 (by rfl) ⟨1548458, by rfl⟩ : syracuseStep 2064611 = 3096917) B3096917
theorem B5879317 : Blo 2063435 5879317 := bbase (se 6 (by rfl) ⟨137796, by rfl⟩ : syracuseStep 5879317 = 275593) (by norm_num)
theorem B7839089 : Blo 2063435 7839089 := bstep (se 2 (by rfl) ⟨2939658, by rfl⟩ : syracuseStep 7839089 = 5879317) B5879317
theorem B5226059 : Blo 2063435 5226059 := bstep (se 1 (by rfl) ⟨3919544, by rfl⟩ : syracuseStep 5226059 = 7839089) B7839089
theorem B3484039 : Blo 2063435 3484039 := bstep (se 1 (by rfl) ⟨2613029, by rfl⟩ : syracuseStep 3484039 = 5226059) B5226059
theorem B4645385 : Blo 2063435 4645385 := bstep (se 2 (by rfl) ⟨1742019, by rfl⟩ : syracuseStep 4645385 = 3484039) B3484039
theorem B3096923 : Blo 2063435 3096923 := bstep (se 1 (by rfl) ⟨2322692, by rfl⟩ : syracuseStep 3096923 = 4645385) B4645385
theorem B2064615 : Blo 2063435 2064615 := bstep (se 1 (by rfl) ⟨1548461, by rfl⟩ : syracuseStep 2064615 = 3096923) B3096923
theorem B2322697 : Blo 2063435 2322697 := bbase (se 2 (by rfl) ⟨871011, by rfl⟩ : syracuseStep 2322697 = 1742023) (by norm_num)
theorem B3096929 : Blo 2063435 3096929 := bstep (se 2 (by rfl) ⟨1161348, by rfl⟩ : syracuseStep 3096929 = 2322697) B2322697
theorem B2064619 : Blo 2063435 2064619 := bstep (se 1 (by rfl) ⟨1548464, by rfl⟩ : syracuseStep 2064619 = 3096929) B3096929
theorem B4960693 : Blo 2063435 4960693 := bbase (se 5 (by rfl) ⟨232532, by rfl⟩ : syracuseStep 4960693 = 465065) (by norm_num)
theorem B26457029 : Blo 2063435 26457029 := bstep (se 4 (by rfl) ⟨2480346, by rfl⟩ : syracuseStep 26457029 = 4960693) B4960693
theorem B17638019 : Blo 2063435 17638019 := bstep (se 1 (by rfl) ⟨13228514, by rfl⟩ : syracuseStep 17638019 = 26457029) B26457029
theorem B11758679 : Blo 2063435 11758679 := bstep (se 1 (by rfl) ⟨8819009, by rfl⟩ : syracuseStep 11758679 = 17638019) B17638019
theorem B7839119 : Blo 2063435 7839119 := bstep (se 1 (by rfl) ⟨5879339, by rfl⟩ : syracuseStep 7839119 = 11758679) B11758679
theorem B5226079 : Blo 2063435 5226079 := bstep (se 1 (by rfl) ⟨3919559, by rfl⟩ : syracuseStep 5226079 = 7839119) B7839119
theorem B6968105 : Blo 2063435 6968105 := bstep (se 2 (by rfl) ⟨2613039, by rfl⟩ : syracuseStep 6968105 = 5226079) B5226079
theorem B4645403 : Blo 2063435 4645403 := bstep (se 1 (by rfl) ⟨3484052, by rfl⟩ : syracuseStep 4645403 = 6968105) B6968105
theorem B3096935 : Blo 2063435 3096935 := bstep (se 1 (by rfl) ⟨2322701, by rfl⟩ : syracuseStep 3096935 = 4645403) B4645403
theorem B2064623 : Blo 2063435 2064623 := bstep (se 1 (by rfl) ⟨1548467, by rfl⟩ : syracuseStep 2064623 = 3096935) B3096935
theorem B3096941 : Blo 2063435 3096941 := bbase (se 3 (by rfl) ⟨580676, by rfl⟩ : syracuseStep 3096941 = 1161353) (by norm_num)
theorem B2064627 : Blo 2063435 2064627 := bstep (se 1 (by rfl) ⟨1548470, by rfl⟩ : syracuseStep 2064627 = 3096941) B3096941
theorem B4645421 : Blo 2063435 4645421 := bbase (se 3 (by rfl) ⟨871016, by rfl⟩ : syracuseStep 4645421 = 1742033) (by norm_num)
theorem B3096947 : Blo 2063435 3096947 := bstep (se 1 (by rfl) ⟨2322710, by rfl⟩ : syracuseStep 3096947 = 4645421) B4645421
theorem B2064631 : Blo 2063435 2064631 := bstep (se 1 (by rfl) ⟨1548473, by rfl⟩ : syracuseStep 2064631 = 3096947) B3096947
theorem B4708813 : Blo 2063435 4708813 := bbase (se 3 (by rfl) ⟨882902, by rfl⟩ : syracuseStep 4708813 = 1765805) (by norm_num)
theorem B6278417 : Blo 2063435 6278417 := bstep (se 2 (by rfl) ⟨2354406, by rfl⟩ : syracuseStep 6278417 = 4708813) B4708813
theorem B4185611 : Blo 2063435 4185611 := bstep (se 1 (by rfl) ⟨3139208, by rfl⟩ : syracuseStep 4185611 = 6278417) B6278417
theorem B2790407 : Blo 2063435 2790407 := bstep (se 1 (by rfl) ⟨2092805, by rfl⟩ : syracuseStep 2790407 = 4185611) B4185611
theorem B7441085 : Blo 2063435 7441085 := bstep (se 3 (by rfl) ⟨1395203, by rfl⟩ : syracuseStep 7441085 = 2790407) B2790407
theorem B19842893 : Blo 2063435 19842893 := bstep (se 3 (by rfl) ⟨3720542, by rfl⟩ : syracuseStep 19842893 = 7441085) B7441085
theorem B13228595 : Blo 2063435 13228595 := bstep (se 1 (by rfl) ⟨9921446, by rfl⟩ : syracuseStep 13228595 = 19842893) B19842893
theorem B8819063 : Blo 2063435 8819063 := bstep (se 1 (by rfl) ⟨6614297, by rfl⟩ : syracuseStep 8819063 = 13228595) B13228595
theorem B5879375 : Blo 2063435 5879375 := bstep (se 1 (by rfl) ⟨4409531, by rfl⟩ : syracuseStep 5879375 = 8819063) B8819063
theorem B3919583 : Blo 2063435 3919583 := bstep (se 1 (by rfl) ⟨2939687, by rfl⟩ : syracuseStep 3919583 = 5879375) B5879375
theorem B2613055 : Blo 2063435 2613055 := bstep (se 1 (by rfl) ⟨1959791, by rfl⟩ : syracuseStep 2613055 = 3919583) B3919583
theorem B3484073 : Blo 2063435 3484073 := bstep (se 2 (by rfl) ⟨1306527, by rfl⟩ : syracuseStep 3484073 = 2613055) B2613055
theorem B2322715 : Blo 2063435 2322715 := bstep (se 1 (by rfl) ⟨1742036, by rfl⟩ : syracuseStep 2322715 = 3484073) B3484073
theorem B3096953 : Blo 2063435 3096953 := bstep (se 2 (by rfl) ⟨1161357, by rfl⟩ : syracuseStep 3096953 = 2322715) B2322715
theorem B2064635 : Blo 2063435 2064635 := bstep (se 1 (by rfl) ⟨1548476, by rfl⟩ : syracuseStep 2064635 = 3096953) B3096953
theorem B35276309 : Blo 2063435 35276309 := bbase (se 6 (by rfl) ⟨826788, by rfl⟩ : syracuseStep 35276309 = 1653577) (by norm_num)
theorem B23517539 : Blo 2063435 23517539 := bstep (se 1 (by rfl) ⟨17638154, by rfl⟩ : syracuseStep 23517539 = 35276309) B35276309
theorem B15678359 : Blo 2063435 15678359 := bstep (se 1 (by rfl) ⟨11758769, by rfl⟩ : syracuseStep 15678359 = 23517539) B23517539
theorem B10452239 : Blo 2063435 10452239 := bstep (se 1 (by rfl) ⟨7839179, by rfl⟩ : syracuseStep 10452239 = 15678359) B15678359
theorem B6968159 : Blo 2063435 6968159 := bstep (se 1 (by rfl) ⟨5226119, by rfl⟩ : syracuseStep 6968159 = 10452239) B10452239
theorem B4645439 : Blo 2063435 4645439 := bstep (se 1 (by rfl) ⟨3484079, by rfl⟩ : syracuseStep 4645439 = 6968159) B6968159
theorem B3096959 : Blo 2063435 3096959 := bstep (se 1 (by rfl) ⟨2322719, by rfl⟩ : syracuseStep 3096959 = 4645439) B4645439
theorem B2064639 : Blo 2063435 2064639 := bstep (se 1 (by rfl) ⟨1548479, by rfl⟩ : syracuseStep 2064639 = 3096959) B3096959
theorem B3096965 : Blo 2063435 3096965 := bbase (se 4 (by rfl) ⟨290340, by rfl⟩ : syracuseStep 3096965 = 580681) (by norm_num)
theorem B2064643 : Blo 2063435 2064643 := bstep (se 1 (by rfl) ⟨1548482, by rfl⟩ : syracuseStep 2064643 = 3096965) B3096965
theorem B3484093 : Blo 2063435 3484093 := bbase (se 3 (by rfl) ⟨653267, by rfl⟩ : syracuseStep 3484093 = 1306535) (by norm_num)
theorem B4645457 : Blo 2063435 4645457 := bstep (se 2 (by rfl) ⟨1742046, by rfl⟩ : syracuseStep 4645457 = 3484093) B3484093
theorem B3096971 : Blo 2063435 3096971 := bstep (se 1 (by rfl) ⟨2322728, by rfl⟩ : syracuseStep 3096971 = 4645457) B4645457
theorem B2064647 : Blo 2063435 2064647 := bstep (se 1 (by rfl) ⟨1548485, by rfl⟩ : syracuseStep 2064647 = 3096971) B3096971
theorem B2322733 : Blo 2063435 2322733 := bbase (se 3 (by rfl) ⟨435512, by rfl⟩ : syracuseStep 2322733 = 871025) (by norm_num)
theorem B3096977 : Blo 2063435 3096977 := bstep (se 2 (by rfl) ⟨1161366, by rfl⟩ : syracuseStep 3096977 = 2322733) B2322733
theorem B2064651 : Blo 2063435 2064651 := bstep (se 1 (by rfl) ⟨1548488, by rfl⟩ : syracuseStep 2064651 = 3096977) B3096977
theorem B6968213 : Blo 2063435 6968213 := bbase (se 6 (by rfl) ⟨163317, by rfl⟩ : syracuseStep 6968213 = 326635) (by norm_num)
theorem B4645475 : Blo 2063435 4645475 := bstep (se 1 (by rfl) ⟨3484106, by rfl⟩ : syracuseStep 4645475 = 6968213) B6968213
theorem B3096983 : Blo 2063435 3096983 := bstep (se 1 (by rfl) ⟨2322737, by rfl⟩ : syracuseStep 3096983 = 4645475) B4645475
theorem B2064655 : Blo 2063435 2064655 := bstep (se 1 (by rfl) ⟨1548491, by rfl⟩ : syracuseStep 2064655 = 3096983) B3096983
theorem B3096989 : Blo 2063435 3096989 := bbase (se 3 (by rfl) ⟨580685, by rfl⟩ : syracuseStep 3096989 = 1161371) (by norm_num)
theorem B2064659 : Blo 2063435 2064659 := bstep (se 1 (by rfl) ⟨1548494, by rfl⟩ : syracuseStep 2064659 = 3096989) B3096989
theorem B4645493 : Blo 2063435 4645493 := bbase (se 5 (by rfl) ⟨217757, by rfl⟩ : syracuseStep 4645493 = 435515) (by norm_num)
theorem B3096995 : Blo 2063435 3096995 := bstep (se 1 (by rfl) ⟨2322746, by rfl⟩ : syracuseStep 3096995 = 4645493) B4645493
theorem B2064663 : Blo 2063435 2064663 := bstep (se 1 (by rfl) ⟨1548497, by rfl⟩ : syracuseStep 2064663 = 3096995) B3096995
theorem B2234881 : Blo 2063435 2234881 := bbase (se 2 (by rfl) ⟨838080, by rfl⟩ : syracuseStep 2234881 = 1676161) (by norm_num)
theorem B11919365 : Blo 2063435 11919365 := bstep (se 4 (by rfl) ⟨1117440, by rfl⟩ : syracuseStep 11919365 = 2234881) B2234881
theorem B7946243 : Blo 2063435 7946243 := bstep (se 1 (by rfl) ⟨5959682, by rfl⟩ : syracuseStep 7946243 = 11919365) B11919365
theorem B5297495 : Blo 2063435 5297495 := bstep (se 1 (by rfl) ⟨3973121, by rfl⟩ : syracuseStep 5297495 = 7946243) B7946243
theorem B14126653 : Blo 2063435 14126653 := bstep (se 3 (by rfl) ⟨2648747, by rfl⟩ : syracuseStep 14126653 = 5297495) B5297495
theorem B75342149 : Blo 2063435 75342149 := bstep (se 4 (by rfl) ⟨7063326, by rfl⟩ : syracuseStep 75342149 = 14126653) B14126653
theorem B50228099 : Blo 2063435 50228099 := bstep (se 1 (by rfl) ⟨37671074, by rfl⟩ : syracuseStep 50228099 = 75342149) B75342149
theorem B33485399 : Blo 2063435 33485399 := bstep (se 1 (by rfl) ⟨25114049, by rfl⟩ : syracuseStep 33485399 = 50228099) B50228099
theorem B22323599 : Blo 2063435 22323599 := bstep (se 1 (by rfl) ⟨16742699, by rfl⟩ : syracuseStep 22323599 = 33485399) B33485399
theorem B14882399 : Blo 2063435 14882399 := bstep (se 1 (by rfl) ⟨11161799, by rfl⟩ : syracuseStep 14882399 = 22323599) B22323599
theorem B9921599 : Blo 2063435 9921599 := bstep (se 1 (by rfl) ⟨7441199, by rfl⟩ : syracuseStep 9921599 = 14882399) B14882399
theorem B6614399 : Blo 2063435 6614399 := bstep (se 1 (by rfl) ⟨4960799, by rfl⟩ : syracuseStep 6614399 = 9921599) B9921599
theorem B17638397 : Blo 2063435 17638397 := bstep (se 3 (by rfl) ⟨3307199, by rfl⟩ : syracuseStep 17638397 = 6614399) B6614399
theorem B11758931 : Blo 2063435 11758931 := bstep (se 1 (by rfl) ⟨8819198, by rfl⟩ : syracuseStep 11758931 = 17638397) B17638397
theorem B7839287 : Blo 2063435 7839287 := bstep (se 1 (by rfl) ⟨5879465, by rfl⟩ : syracuseStep 7839287 = 11758931) B11758931
theorem B5226191 : Blo 2063435 5226191 := bstep (se 1 (by rfl) ⟨3919643, by rfl⟩ : syracuseStep 5226191 = 7839287) B7839287
theorem B3484127 : Blo 2063435 3484127 := bstep (se 1 (by rfl) ⟨2613095, by rfl⟩ : syracuseStep 3484127 = 5226191) B5226191
theorem B2322751 : Blo 2063435 2322751 := bstep (se 1 (by rfl) ⟨1742063, by rfl⟩ : syracuseStep 2322751 = 3484127) B3484127
theorem B3097001 : Blo 2063435 3097001 := bstep (se 2 (by rfl) ⟨1161375, by rfl⟩ : syracuseStep 3097001 = 2322751) B2322751
theorem B2064667 : Blo 2063435 2064667 := bstep (se 1 (by rfl) ⟨1548500, by rfl⟩ : syracuseStep 2064667 = 3097001) B3097001
theorem B7839301 : Blo 2063435 7839301 := bbase (se 4 (by rfl) ⟨734934, by rfl⟩ : syracuseStep 7839301 = 1469869) (by norm_num)
theorem B10452401 : Blo 2063435 10452401 := bstep (se 2 (by rfl) ⟨3919650, by rfl⟩ : syracuseStep 10452401 = 7839301) B7839301
theorem B6968267 : Blo 2063435 6968267 := bstep (se 1 (by rfl) ⟨5226200, by rfl⟩ : syracuseStep 6968267 = 10452401) B10452401
theorem B4645511 : Blo 2063435 4645511 := bstep (se 1 (by rfl) ⟨3484133, by rfl⟩ : syracuseStep 4645511 = 6968267) B6968267
theorem B3097007 : Blo 2063435 3097007 := bstep (se 1 (by rfl) ⟨2322755, by rfl⟩ : syracuseStep 3097007 = 4645511) B4645511
theorem B2064671 : Blo 2063435 2064671 := bstep (se 1 (by rfl) ⟨1548503, by rfl⟩ : syracuseStep 2064671 = 3097007) B3097007
theorem B3097013 : Blo 2063435 3097013 := bbase (se 5 (by rfl) ⟨145172, by rfl⟩ : syracuseStep 3097013 = 290345) (by norm_num)
theorem B2064675 : Blo 2063435 2064675 := bstep (se 1 (by rfl) ⟨1548506, by rfl⟩ : syracuseStep 2064675 = 3097013) B3097013
theorem B5226221 : Blo 2063435 5226221 := bbase (se 3 (by rfl) ⟨979916, by rfl⟩ : syracuseStep 5226221 = 1959833) (by norm_num)
theorem B3484147 : Blo 2063435 3484147 := bstep (se 1 (by rfl) ⟨2613110, by rfl⟩ : syracuseStep 3484147 = 5226221) B5226221
theorem B4645529 : Blo 2063435 4645529 := bstep (se 2 (by rfl) ⟨1742073, by rfl⟩ : syracuseStep 4645529 = 3484147) B3484147
theorem B3097019 : Blo 2063435 3097019 := bstep (se 1 (by rfl) ⟨2322764, by rfl⟩ : syracuseStep 3097019 = 4645529) B4645529
theorem B2064679 : Blo 2063435 2064679 := bstep (se 1 (by rfl) ⟨1548509, by rfl⟩ : syracuseStep 2064679 = 3097019) B3097019
theorem B2322769 : Blo 2063435 2322769 := bbase (se 2 (by rfl) ⟨871038, by rfl⟩ : syracuseStep 2322769 = 1742077) (by norm_num)
theorem B3097025 : Blo 2063435 3097025 := bstep (se 2 (by rfl) ⟨1161384, by rfl⟩ : syracuseStep 3097025 = 2322769) B2322769
theorem B2064683 : Blo 2063435 2064683 := bstep (se 1 (by rfl) ⟨1548512, by rfl⟩ : syracuseStep 2064683 = 3097025) B3097025
theorem B2204821 : Blo 2063435 2204821 := bbase (se 6 (by rfl) ⟨51675, by rfl⟩ : syracuseStep 2204821 = 103351) (by norm_num)
theorem B2939761 : Blo 2063435 2939761 := bstep (se 2 (by rfl) ⟨1102410, by rfl⟩ : syracuseStep 2939761 = 2204821) B2204821
theorem B3919681 : Blo 2063435 3919681 := bstep (se 2 (by rfl) ⟨1469880, by rfl⟩ : syracuseStep 3919681 = 2939761) B2939761
theorem B5226241 : Blo 2063435 5226241 := bstep (se 2 (by rfl) ⟨1959840, by rfl⟩ : syracuseStep 5226241 = 3919681) B3919681
theorem B6968321 : Blo 2063435 6968321 := bstep (se 2 (by rfl) ⟨2613120, by rfl⟩ : syracuseStep 6968321 = 5226241) B5226241
theorem B4645547 : Blo 2063435 4645547 := bstep (se 1 (by rfl) ⟨3484160, by rfl⟩ : syracuseStep 4645547 = 6968321) B6968321
theorem B3097031 : Blo 2063435 3097031 := bstep (se 1 (by rfl) ⟨2322773, by rfl⟩ : syracuseStep 3097031 = 4645547) B4645547
theorem B2064687 : Blo 2063435 2064687 := bstep (se 1 (by rfl) ⟨1548515, by rfl⟩ : syracuseStep 2064687 = 3097031) B3097031
theorem B3097037 : Blo 2063435 3097037 := bbase (se 3 (by rfl) ⟨580694, by rfl⟩ : syracuseStep 3097037 = 1161389) (by norm_num)
theorem B2064691 : Blo 2063435 2064691 := bstep (se 1 (by rfl) ⟨1548518, by rfl⟩ : syracuseStep 2064691 = 3097037) B3097037
theorem B4645565 : Blo 2063435 4645565 := bbase (se 3 (by rfl) ⟨871043, by rfl⟩ : syracuseStep 4645565 = 1742087) (by norm_num)
theorem B3097043 : Blo 2063435 3097043 := bstep (se 1 (by rfl) ⟨2322782, by rfl⟩ : syracuseStep 3097043 = 4645565) B4645565
theorem B2064695 : Blo 2063435 2064695 := bstep (se 1 (by rfl) ⟨1548521, by rfl⟩ : syracuseStep 2064695 = 3097043) B3097043
theorem B3484181 : Blo 2063435 3484181 := bbase (se 6 (by rfl) ⟨81660, by rfl⟩ : syracuseStep 3484181 = 163321) (by norm_num)
theorem B2322787 : Blo 2063435 2322787 := bstep (se 1 (by rfl) ⟨1742090, by rfl⟩ : syracuseStep 2322787 = 3484181) B3484181
theorem B3097049 : Blo 2063435 3097049 := bstep (se 2 (by rfl) ⟨1161393, by rfl⟩ : syracuseStep 3097049 = 2322787) B2322787
theorem B2064699 : Blo 2063435 2064699 := bstep (se 1 (by rfl) ⟨1548524, by rfl⟩ : syracuseStep 2064699 = 3097049) B3097049
theorem B19843541 : Blo 2063435 19843541 := bbase (se 7 (by rfl) ⟨232541, by rfl⟩ : syracuseStep 19843541 = 465083) (by norm_num)
theorem B13229027 : Blo 2063435 13229027 := bstep (se 1 (by rfl) ⟨9921770, by rfl⟩ : syracuseStep 13229027 = 19843541) B19843541
theorem B8819351 : Blo 2063435 8819351 := bstep (se 1 (by rfl) ⟨6614513, by rfl⟩ : syracuseStep 8819351 = 13229027) B13229027
theorem B5879567 : Blo 2063435 5879567 := bstep (se 1 (by rfl) ⟨4409675, by rfl⟩ : syracuseStep 5879567 = 8819351) B8819351
theorem B15678845 : Blo 2063435 15678845 := bstep (se 3 (by rfl) ⟨2939783, by rfl⟩ : syracuseStep 15678845 = 5879567) B5879567
theorem B10452563 : Blo 2063435 10452563 := bstep (se 1 (by rfl) ⟨7839422, by rfl⟩ : syracuseStep 10452563 = 15678845) B15678845
theorem B6968375 : Blo 2063435 6968375 := bstep (se 1 (by rfl) ⟨5226281, by rfl⟩ : syracuseStep 6968375 = 10452563) B10452563
theorem B4645583 : Blo 2063435 4645583 := bstep (se 1 (by rfl) ⟨3484187, by rfl⟩ : syracuseStep 4645583 = 6968375) B6968375
theorem B3097055 : Blo 2063435 3097055 := bstep (se 1 (by rfl) ⟨2322791, by rfl⟩ : syracuseStep 3097055 = 4645583) B4645583
theorem B2064703 : Blo 2063435 2064703 := bstep (se 1 (by rfl) ⟨1548527, by rfl⟩ : syracuseStep 2064703 = 3097055) B3097055
theorem B3097061 : Blo 2063435 3097061 := bbase (se 4 (by rfl) ⟨290349, by rfl⟩ : syracuseStep 3097061 = 580699) (by norm_num)
theorem B2064707 : Blo 2063435 2064707 := bstep (se 1 (by rfl) ⟨1548530, by rfl⟩ : syracuseStep 2064707 = 3097061) B3097061
theorem B8939717 : Blo 2063435 8939717 := bbase (se 4 (by rfl) ⟨838098, by rfl⟩ : syracuseStep 8939717 = 1676197) (by norm_num)
theorem B5959811 : Blo 2063435 5959811 := bstep (se 1 (by rfl) ⟨4469858, by rfl⟩ : syracuseStep 5959811 = 8939717) B8939717
theorem B3973207 : Blo 2063435 3973207 := bstep (se 1 (by rfl) ⟨2979905, by rfl⟩ : syracuseStep 3973207 = 5959811) B5959811
theorem B5297609 : Blo 2063435 5297609 := bstep (se 2 (by rfl) ⟨1986603, by rfl⟩ : syracuseStep 5297609 = 3973207) B3973207
theorem B14126957 : Blo 2063435 14126957 := bstep (se 3 (by rfl) ⟨2648804, by rfl⟩ : syracuseStep 14126957 = 5297609) B5297609
theorem B9417971 : Blo 2063435 9417971 := bstep (se 1 (by rfl) ⟨7063478, by rfl⟩ : syracuseStep 9417971 = 14126957) B14126957
theorem B6278647 : Blo 2063435 6278647 := bstep (se 1 (by rfl) ⟨4708985, by rfl⟩ : syracuseStep 6278647 = 9417971) B9417971
theorem B8371529 : Blo 2063435 8371529 := bstep (se 2 (by rfl) ⟨3139323, by rfl⟩ : syracuseStep 8371529 = 6278647) B6278647
theorem B5581019 : Blo 2063435 5581019 := bstep (se 1 (by rfl) ⟨4185764, by rfl⟩ : syracuseStep 5581019 = 8371529) B8371529
theorem B14882717 : Blo 2063435 14882717 := bstep (se 3 (by rfl) ⟨2790509, by rfl⟩ : syracuseStep 14882717 = 5581019) B5581019
theorem B9921811 : Blo 2063435 9921811 := bstep (se 1 (by rfl) ⟨7441358, by rfl⟩ : syracuseStep 9921811 = 14882717) B14882717
theorem B13229081 : Blo 2063435 13229081 := bstep (se 2 (by rfl) ⟨4960905, by rfl⟩ : syracuseStep 13229081 = 9921811) B9921811
theorem B8819387 : Blo 2063435 8819387 := bstep (se 1 (by rfl) ⟨6614540, by rfl⟩ : syracuseStep 8819387 = 13229081) B13229081
theorem B5879591 : Blo 2063435 5879591 := bstep (se 1 (by rfl) ⟨4409693, by rfl⟩ : syracuseStep 5879591 = 8819387) B8819387
theorem B3919727 : Blo 2063435 3919727 := bstep (se 1 (by rfl) ⟨2939795, by rfl⟩ : syracuseStep 3919727 = 5879591) B5879591
theorem B2613151 : Blo 2063435 2613151 := bstep (se 1 (by rfl) ⟨1959863, by rfl⟩ : syracuseStep 2613151 = 3919727) B3919727
theorem B3484201 : Blo 2063435 3484201 := bstep (se 2 (by rfl) ⟨1306575, by rfl⟩ : syracuseStep 3484201 = 2613151) B2613151
theorem B4645601 : Blo 2063435 4645601 := bstep (se 2 (by rfl) ⟨1742100, by rfl⟩ : syracuseStep 4645601 = 3484201) B3484201
theorem B3097067 : Blo 2063435 3097067 := bstep (se 1 (by rfl) ⟨2322800, by rfl⟩ : syracuseStep 3097067 = 4645601) B4645601
theorem B2064711 : Blo 2063435 2064711 := bstep (se 1 (by rfl) ⟨1548533, by rfl⟩ : syracuseStep 2064711 = 3097067) B3097067
theorem B2322805 : Blo 2063435 2322805 := bbase (se 5 (by rfl) ⟨108881, by rfl⟩ : syracuseStep 2322805 = 217763) (by norm_num)
theorem B3097073 : Blo 2063435 3097073 := bstep (se 2 (by rfl) ⟨1161402, by rfl⟩ : syracuseStep 3097073 = 2322805) B2322805
theorem B2064715 : Blo 2063435 2064715 := bstep (se 1 (by rfl) ⟨1548536, by rfl⟩ : syracuseStep 2064715 = 3097073) B3097073
theorem B2613161 : Blo 2063435 2613161 := bbase (se 2 (by rfl) ⟨979935, by rfl⟩ : syracuseStep 2613161 = 1959871) (by norm_num)
theorem B6968429 : Blo 2063435 6968429 := bstep (se 3 (by rfl) ⟨1306580, by rfl⟩ : syracuseStep 6968429 = 2613161) B2613161
theorem B4645619 : Blo 2063435 4645619 := bstep (se 1 (by rfl) ⟨3484214, by rfl⟩ : syracuseStep 4645619 = 6968429) B6968429
theorem B3097079 : Blo 2063435 3097079 := bstep (se 1 (by rfl) ⟨2322809, by rfl⟩ : syracuseStep 3097079 = 4645619) B4645619
theorem B2064719 : Blo 2063435 2064719 := bstep (se 1 (by rfl) ⟨1548539, by rfl⟩ : syracuseStep 2064719 = 3097079) B3097079
theorem B3097085 : Blo 2063435 3097085 := bbase (se 3 (by rfl) ⟨580703, by rfl⟩ : syracuseStep 3097085 = 1161407) (by norm_num)
theorem B2064723 : Blo 2063435 2064723 := bstep (se 1 (by rfl) ⟨1548542, by rfl⟩ : syracuseStep 2064723 = 3097085) B3097085
theorem B4645637 : Blo 2063435 4645637 := bbase (se 4 (by rfl) ⟨435528, by rfl⟩ : syracuseStep 4645637 = 871057) (by norm_num)
theorem B3097091 : Blo 2063435 3097091 := bstep (se 1 (by rfl) ⟨2322818, by rfl⟩ : syracuseStep 3097091 = 4645637) B4645637
theorem B2064727 : Blo 2063435 2064727 := bstep (se 1 (by rfl) ⟨1548545, by rfl⟩ : syracuseStep 2064727 = 3097091) B3097091
theorem B3919765 : Blo 2063435 3919765 := bbase (se 6 (by rfl) ⟨91869, by rfl⟩ : syracuseStep 3919765 = 183739) (by norm_num)
theorem B5226353 : Blo 2063435 5226353 := bstep (se 2 (by rfl) ⟨1959882, by rfl⟩ : syracuseStep 5226353 = 3919765) B3919765
theorem B3484235 : Blo 2063435 3484235 := bstep (se 1 (by rfl) ⟨2613176, by rfl⟩ : syracuseStep 3484235 = 5226353) B5226353
theorem B2322823 : Blo 2063435 2322823 := bstep (se 1 (by rfl) ⟨1742117, by rfl⟩ : syracuseStep 2322823 = 3484235) B3484235
theorem B3097097 : Blo 2063435 3097097 := bstep (se 2 (by rfl) ⟨1161411, by rfl⟩ : syracuseStep 3097097 = 2322823) B2322823
theorem B2064731 : Blo 2063435 2064731 := bstep (se 1 (by rfl) ⟨1548548, by rfl⟩ : syracuseStep 2064731 = 3097097) B3097097
theorem B10452725 : Blo 2063435 10452725 := bbase (se 5 (by rfl) ⟨489971, by rfl⟩ : syracuseStep 10452725 = 979943) (by norm_num)
theorem B6968483 : Blo 2063435 6968483 := bstep (se 1 (by rfl) ⟨5226362, by rfl⟩ : syracuseStep 6968483 = 10452725) B10452725
theorem B4645655 : Blo 2063435 4645655 := bstep (se 1 (by rfl) ⟨3484241, by rfl⟩ : syracuseStep 4645655 = 6968483) B6968483
theorem B3097103 : Blo 2063435 3097103 := bstep (se 1 (by rfl) ⟨2322827, by rfl⟩ : syracuseStep 3097103 = 4645655) B4645655
theorem B2064735 : Blo 2063435 2064735 := bstep (se 1 (by rfl) ⟨1548551, by rfl⟩ : syracuseStep 2064735 = 3097103) B3097103
theorem B3097109 : Blo 2063435 3097109 := bbase (se 6 (by rfl) ⟨72588, by rfl⟩ : syracuseStep 3097109 = 145177) (by norm_num)
theorem B2064739 : Blo 2063435 2064739 := bstep (se 1 (by rfl) ⟨1548554, by rfl⟩ : syracuseStep 2064739 = 3097109) B3097109
theorem B3139373 : Blo 2063435 3139373 := bbase (se 3 (by rfl) ⟨588632, by rfl⟩ : syracuseStep 3139373 = 1177265) (by norm_num)
theorem B2092915 : Blo 2063435 2092915 := bstep (se 1 (by rfl) ⟨1569686, by rfl⟩ : syracuseStep 2092915 = 3139373) B3139373
theorem B2790553 : Blo 2063435 2790553 := bstep (se 2 (by rfl) ⟨1046457, by rfl⟩ : syracuseStep 2790553 = 2092915) B2092915
theorem B3720737 : Blo 2063435 3720737 := bstep (se 2 (by rfl) ⟨1395276, by rfl⟩ : syracuseStep 3720737 = 2790553) B2790553
theorem B2480491 : Blo 2063435 2480491 := bstep (se 1 (by rfl) ⟨1860368, by rfl⟩ : syracuseStep 2480491 = 3720737) B3720737
theorem B3307321 : Blo 2063435 3307321 := bstep (se 2 (by rfl) ⟨1240245, by rfl⟩ : syracuseStep 3307321 = 2480491) B2480491
theorem B17639045 : Blo 2063435 17639045 := bstep (se 4 (by rfl) ⟨1653660, by rfl⟩ : syracuseStep 17639045 = 3307321) B3307321
theorem B11759363 : Blo 2063435 11759363 := bstep (se 1 (by rfl) ⟨8819522, by rfl⟩ : syracuseStep 11759363 = 17639045) B17639045
theorem B7839575 : Blo 2063435 7839575 := bstep (se 1 (by rfl) ⟨5879681, by rfl⟩ : syracuseStep 7839575 = 11759363) B11759363
theorem B5226383 : Blo 2063435 5226383 := bstep (se 1 (by rfl) ⟨3919787, by rfl⟩ : syracuseStep 5226383 = 7839575) B7839575
theorem B3484255 : Blo 2063435 3484255 := bstep (se 1 (by rfl) ⟨2613191, by rfl⟩ : syracuseStep 3484255 = 5226383) B5226383
theorem B4645673 : Blo 2063435 4645673 := bstep (se 2 (by rfl) ⟨1742127, by rfl⟩ : syracuseStep 4645673 = 3484255) B3484255
theorem B3097115 : Blo 2063435 3097115 := bstep (se 1 (by rfl) ⟨2322836, by rfl⟩ : syracuseStep 3097115 = 4645673) B4645673
theorem B2064743 : Blo 2063435 2064743 := bstep (se 1 (by rfl) ⟨1548557, by rfl⟩ : syracuseStep 2064743 = 3097115) B3097115
theorem B2322841 : Blo 2063435 2322841 := bbase (se 2 (by rfl) ⟨871065, by rfl⟩ : syracuseStep 2322841 = 1742131) (by norm_num)
theorem B3097121 : Blo 2063435 3097121 := bstep (se 2 (by rfl) ⟨1161420, by rfl⟩ : syracuseStep 3097121 = 2322841) B2322841
theorem B2064747 : Blo 2063435 2064747 := bstep (se 1 (by rfl) ⟨1548560, by rfl⟩ : syracuseStep 2064747 = 3097121) B3097121
theorem B7839605 : Blo 2063435 7839605 := bbase (se 5 (by rfl) ⟨367481, by rfl⟩ : syracuseStep 7839605 = 734963) (by norm_num)
theorem B5226403 : Blo 2063435 5226403 := bstep (se 1 (by rfl) ⟨3919802, by rfl⟩ : syracuseStep 5226403 = 7839605) B7839605
theorem B6968537 : Blo 2063435 6968537 := bstep (se 2 (by rfl) ⟨2613201, by rfl⟩ : syracuseStep 6968537 = 5226403) B5226403
theorem B4645691 : Blo 2063435 4645691 := bstep (se 1 (by rfl) ⟨3484268, by rfl⟩ : syracuseStep 4645691 = 6968537) B6968537
theorem B3097127 : Blo 2063435 3097127 := bstep (se 1 (by rfl) ⟨2322845, by rfl⟩ : syracuseStep 3097127 = 4645691) B4645691
theorem B2064751 : Blo 2063435 2064751 := bstep (se 1 (by rfl) ⟨1548563, by rfl⟩ : syracuseStep 2064751 = 3097127) B3097127
theorem B3097133 : Blo 2063435 3097133 := bbase (se 3 (by rfl) ⟨580712, by rfl⟩ : syracuseStep 3097133 = 1161425) (by norm_num)
theorem B2064755 : Blo 2063435 2064755 := bstep (se 1 (by rfl) ⟨1548566, by rfl⟩ : syracuseStep 2064755 = 3097133) B3097133
theorem B4645709 : Blo 2063435 4645709 := bbase (se 3 (by rfl) ⟨871070, by rfl⟩ : syracuseStep 4645709 = 1742141) (by norm_num)
theorem B3097139 : Blo 2063435 3097139 := bstep (se 1 (by rfl) ⟨2322854, by rfl⟩ : syracuseStep 3097139 = 4645709) B4645709
theorem B2064759 : Blo 2063435 2064759 := bstep (se 1 (by rfl) ⟨1548569, by rfl⟩ : syracuseStep 2064759 = 3097139) B3097139
theorem B2613217 : Blo 2063435 2613217 := bbase (se 2 (by rfl) ⟨979956, by rfl⟩ : syracuseStep 2613217 = 1959913) (by norm_num)
theorem B3484289 : Blo 2063435 3484289 := bstep (se 2 (by rfl) ⟨1306608, by rfl⟩ : syracuseStep 3484289 = 2613217) B2613217
theorem B2322859 : Blo 2063435 2322859 := bstep (se 1 (by rfl) ⟨1742144, by rfl⟩ : syracuseStep 2322859 = 3484289) B3484289
theorem B3097145 : Blo 2063435 3097145 := bstep (se 2 (by rfl) ⟨1161429, by rfl⟩ : syracuseStep 3097145 = 2322859) B2322859
theorem B2064763 : Blo 2063435 2064763 := bstep (se 1 (by rfl) ⟨1548572, by rfl⟩ : syracuseStep 2064763 = 3097145) B3097145
theorem B23518997 : Blo 2063435 23518997 := bbase (se 6 (by rfl) ⟨551226, by rfl⟩ : syracuseStep 23518997 = 1102453) (by norm_num)
theorem B15679331 : Blo 2063435 15679331 := bstep (se 1 (by rfl) ⟨11759498, by rfl⟩ : syracuseStep 15679331 = 23518997) B23518997
theorem B10452887 : Blo 2063435 10452887 := bstep (se 1 (by rfl) ⟨7839665, by rfl⟩ : syracuseStep 10452887 = 15679331) B15679331
theorem B6968591 : Blo 2063435 6968591 := bstep (se 1 (by rfl) ⟨5226443, by rfl⟩ : syracuseStep 6968591 = 10452887) B10452887
theorem B4645727 : Blo 2063435 4645727 := bstep (se 1 (by rfl) ⟨3484295, by rfl⟩ : syracuseStep 4645727 = 6968591) B6968591
theorem B3097151 : Blo 2063435 3097151 := bstep (se 1 (by rfl) ⟨2322863, by rfl⟩ : syracuseStep 3097151 = 4645727) B4645727
theorem B2064767 : Blo 2063435 2064767 := bstep (se 1 (by rfl) ⟨1548575, by rfl⟩ : syracuseStep 2064767 = 3097151) B3097151
theorem B3097157 : Blo 2063435 3097157 := bbase (se 4 (by rfl) ⟨290358, by rfl⟩ : syracuseStep 3097157 = 580717) (by norm_num)
theorem B2064771 : Blo 2063435 2064771 := bstep (se 1 (by rfl) ⟨1548578, by rfl⟩ : syracuseStep 2064771 = 3097157) B3097157
theorem B3484309 : Blo 2063435 3484309 := bbase (se 6 (by rfl) ⟨81663, by rfl⟩ : syracuseStep 3484309 = 163327) (by norm_num)
theorem B4645745 : Blo 2063435 4645745 := bstep (se 2 (by rfl) ⟨1742154, by rfl⟩ : syracuseStep 4645745 = 3484309) B3484309
theorem B3097163 : Blo 2063435 3097163 := bstep (se 1 (by rfl) ⟨2322872, by rfl⟩ : syracuseStep 3097163 = 4645745) B4645745
theorem B2064775 : Blo 2063435 2064775 := bstep (se 1 (by rfl) ⟨1548581, by rfl⟩ : syracuseStep 2064775 = 3097163) B3097163
theorem B2322877 : Blo 2063435 2322877 := bbase (se 3 (by rfl) ⟨435539, by rfl⟩ : syracuseStep 2322877 = 871079) (by norm_num)
theorem B3097169 : Blo 2063435 3097169 := bstep (se 2 (by rfl) ⟨1161438, by rfl⟩ : syracuseStep 3097169 = 2322877) B2322877
theorem B2064779 : Blo 2063435 2064779 := bstep (se 1 (by rfl) ⟨1548584, by rfl⟩ : syracuseStep 2064779 = 3097169) B3097169
theorem B6968645 : Blo 2063435 6968645 := bbase (se 4 (by rfl) ⟨653310, by rfl⟩ : syracuseStep 6968645 = 1306621) (by norm_num)
theorem B4645763 : Blo 2063435 4645763 := bstep (se 1 (by rfl) ⟨3484322, by rfl⟩ : syracuseStep 4645763 = 6968645) B6968645
theorem B3097175 : Blo 2063435 3097175 := bstep (se 1 (by rfl) ⟨2322881, by rfl⟩ : syracuseStep 3097175 = 4645763) B4645763
theorem B2064783 : Blo 2063435 2064783 := bstep (se 1 (by rfl) ⟨1548587, by rfl⟩ : syracuseStep 2064783 = 3097175) B3097175
theorem B3097181 : Blo 2063435 3097181 := bbase (se 3 (by rfl) ⟨580721, by rfl⟩ : syracuseStep 3097181 = 1161443) (by norm_num)
theorem B2064787 : Blo 2063435 2064787 := bstep (se 1 (by rfl) ⟨1548590, by rfl⟩ : syracuseStep 2064787 = 3097181) B3097181
theorem B4645781 : Blo 2063435 4645781 := bbase (se 6 (by rfl) ⟨108885, by rfl⟩ : syracuseStep 4645781 = 217771) (by norm_num)
theorem B3097187 : Blo 2063435 3097187 := bstep (se 1 (by rfl) ⟨2322890, by rfl⟩ : syracuseStep 3097187 = 4645781) B4645781
theorem B2064791 : Blo 2063435 2064791 := bstep (se 1 (by rfl) ⟨1548593, by rfl⟩ : syracuseStep 2064791 = 3097187) B3097187
theorem B3307405 : Blo 2063435 3307405 := bbase (se 3 (by rfl) ⟨620138, by rfl⟩ : syracuseStep 3307405 = 1240277) (by norm_num)
theorem B4409873 : Blo 2063435 4409873 := bstep (se 2 (by rfl) ⟨1653702, by rfl⟩ : syracuseStep 4409873 = 3307405) B3307405
theorem B2939915 : Blo 2063435 2939915 := bstep (se 1 (by rfl) ⟨2204936, by rfl⟩ : syracuseStep 2939915 = 4409873) B4409873
theorem B7839773 : Blo 2063435 7839773 := bstep (se 3 (by rfl) ⟨1469957, by rfl⟩ : syracuseStep 7839773 = 2939915) B2939915
theorem B5226515 : Blo 2063435 5226515 := bstep (se 1 (by rfl) ⟨3919886, by rfl⟩ : syracuseStep 5226515 = 7839773) B7839773
theorem B3484343 : Blo 2063435 3484343 := bstep (se 1 (by rfl) ⟨2613257, by rfl⟩ : syracuseStep 3484343 = 5226515) B5226515
theorem B2322895 : Blo 2063435 2322895 := bstep (se 1 (by rfl) ⟨1742171, by rfl⟩ : syracuseStep 2322895 = 3484343) B3484343
theorem B3097193 : Blo 2063435 3097193 := bstep (se 2 (by rfl) ⟨1161447, by rfl⟩ : syracuseStep 3097193 = 2322895) B2322895
theorem B2064795 : Blo 2063435 2064795 := bstep (se 1 (by rfl) ⟨1548596, by rfl⟩ : syracuseStep 2064795 = 3097193) B3097193
theorem B6614821 : Blo 2063435 6614821 := bbase (se 4 (by rfl) ⟨620139, by rfl⟩ : syracuseStep 6614821 = 1240279) (by norm_num)
theorem B8819761 : Blo 2063435 8819761 := bstep (se 2 (by rfl) ⟨3307410, by rfl⟩ : syracuseStep 8819761 = 6614821) B6614821
theorem B11759681 : Blo 2063435 11759681 := bstep (se 2 (by rfl) ⟨4409880, by rfl⟩ : syracuseStep 11759681 = 8819761) B8819761
theorem B7839787 : Blo 2063435 7839787 := bstep (se 1 (by rfl) ⟨5879840, by rfl⟩ : syracuseStep 7839787 = 11759681) B11759681
theorem B10453049 : Blo 2063435 10453049 := bstep (se 2 (by rfl) ⟨3919893, by rfl⟩ : syracuseStep 10453049 = 7839787) B7839787
theorem B6968699 : Blo 2063435 6968699 := bstep (se 1 (by rfl) ⟨5226524, by rfl⟩ : syracuseStep 6968699 = 10453049) B10453049
theorem B4645799 : Blo 2063435 4645799 := bstep (se 1 (by rfl) ⟨3484349, by rfl⟩ : syracuseStep 4645799 = 6968699) B6968699
theorem B3097199 : Blo 2063435 3097199 := bstep (se 1 (by rfl) ⟨2322899, by rfl⟩ : syracuseStep 3097199 = 4645799) B4645799
theorem B2064799 : Blo 2063435 2064799 := bstep (se 1 (by rfl) ⟨1548599, by rfl⟩ : syracuseStep 2064799 = 3097199) B3097199
theorem B3097205 : Blo 2063435 3097205 := bbase (se 5 (by rfl) ⟨145181, by rfl⟩ : syracuseStep 3097205 = 290363) (by norm_num)
theorem B2064803 : Blo 2063435 2064803 := bstep (se 1 (by rfl) ⟨1548602, by rfl⟩ : syracuseStep 2064803 = 3097205) B3097205
theorem B3919909 : Blo 2063435 3919909 := bbase (se 4 (by rfl) ⟨367491, by rfl⟩ : syracuseStep 3919909 = 734983) (by norm_num)
theorem B5226545 : Blo 2063435 5226545 := bstep (se 2 (by rfl) ⟨1959954, by rfl⟩ : syracuseStep 5226545 = 3919909) B3919909
theorem B3484363 : Blo 2063435 3484363 := bstep (se 1 (by rfl) ⟨2613272, by rfl⟩ : syracuseStep 3484363 = 5226545) B5226545
theorem B4645817 : Blo 2063435 4645817 := bstep (se 2 (by rfl) ⟨1742181, by rfl⟩ : syracuseStep 4645817 = 3484363) B3484363
theorem B3097211 : Blo 2063435 3097211 := bstep (se 1 (by rfl) ⟨2322908, by rfl⟩ : syracuseStep 3097211 = 4645817) B4645817
theorem B2064807 : Blo 2063435 2064807 := bstep (se 1 (by rfl) ⟨1548605, by rfl⟩ : syracuseStep 2064807 = 3097211) B3097211
theorem B2322913 : Blo 2063435 2322913 := bbase (se 2 (by rfl) ⟨871092, by rfl⟩ : syracuseStep 2322913 = 1742185) (by norm_num)
theorem B3097217 : Blo 2063435 3097217 := bstep (se 2 (by rfl) ⟨1161456, by rfl⟩ : syracuseStep 3097217 = 2322913) B2322913
theorem B2064811 : Blo 2063435 2064811 := bstep (se 1 (by rfl) ⟨1548608, by rfl⟩ : syracuseStep 2064811 = 3097217) B3097217
theorem B5226565 : Blo 2063435 5226565 := bbase (se 4 (by rfl) ⟨489990, by rfl⟩ : syracuseStep 5226565 = 979981) (by norm_num)
theorem B6968753 : Blo 2063435 6968753 := bstep (se 2 (by rfl) ⟨2613282, by rfl⟩ : syracuseStep 6968753 = 5226565) B5226565
theorem B4645835 : Blo 2063435 4645835 := bstep (se 1 (by rfl) ⟨3484376, by rfl⟩ : syracuseStep 4645835 = 6968753) B6968753
theorem B3097223 : Blo 2063435 3097223 := bstep (se 1 (by rfl) ⟨2322917, by rfl⟩ : syracuseStep 3097223 = 4645835) B4645835
theorem B2064815 : Blo 2063435 2064815 := bstep (se 1 (by rfl) ⟨1548611, by rfl⟩ : syracuseStep 2064815 = 3097223) B3097223
theorem B3097229 : Blo 2063435 3097229 := bbase (se 3 (by rfl) ⟨580730, by rfl⟩ : syracuseStep 3097229 = 1161461) (by norm_num)
theorem B2064819 : Blo 2063435 2064819 := bstep (se 1 (by rfl) ⟨1548614, by rfl⟩ : syracuseStep 2064819 = 3097229) B3097229
theorem B4645853 : Blo 2063435 4645853 := bbase (se 3 (by rfl) ⟨871097, by rfl⟩ : syracuseStep 4645853 = 1742195) (by norm_num)
theorem B3097235 : Blo 2063435 3097235 := bstep (se 1 (by rfl) ⟨2322926, by rfl⟩ : syracuseStep 3097235 = 4645853) B4645853
theorem B2064823 : Blo 2063435 2064823 := bstep (se 1 (by rfl) ⟨1548617, by rfl⟩ : syracuseStep 2064823 = 3097235) B3097235
theorem B3484397 : Blo 2063435 3484397 := bbase (se 3 (by rfl) ⟨653324, by rfl⟩ : syracuseStep 3484397 = 1306649) (by norm_num)
theorem B2322931 : Blo 2063435 2322931 := bstep (se 1 (by rfl) ⟨1742198, by rfl⟩ : syracuseStep 2322931 = 3484397) B3484397
theorem B3097241 : Blo 2063435 3097241 := bstep (se 2 (by rfl) ⟨1161465, by rfl⟩ : syracuseStep 3097241 = 2322931) B2322931
theorem B2064827 : Blo 2063435 2064827 := bstep (se 1 (by rfl) ⟨1548620, by rfl⟩ : syracuseStep 2064827 = 3097241) B3097241
theorem B9418517 : Blo 2063435 9418517 := bbase (se 6 (by rfl) ⟨220746, by rfl⟩ : syracuseStep 9418517 = 441493) (by norm_num)
theorem B6279011 : Blo 2063435 6279011 := bstep (se 1 (by rfl) ⟨4709258, by rfl⟩ : syracuseStep 6279011 = 9418517) B9418517
theorem B4186007 : Blo 2063435 4186007 := bstep (se 1 (by rfl) ⟨3139505, by rfl⟩ : syracuseStep 4186007 = 6279011) B6279011
theorem B2790671 : Blo 2063435 2790671 := bstep (se 1 (by rfl) ⟨2093003, by rfl⟩ : syracuseStep 2790671 = 4186007) B4186007
theorem B7441789 : Blo 2063435 7441789 := bstep (se 3 (by rfl) ⟨1395335, by rfl⟩ : syracuseStep 7441789 = 2790671) B2790671
theorem B9922385 : Blo 2063435 9922385 := bstep (se 2 (by rfl) ⟨3720894, by rfl⟩ : syracuseStep 9922385 = 7441789) B7441789
theorem B26459693 : Blo 2063435 26459693 := bstep (se 3 (by rfl) ⟨4961192, by rfl⟩ : syracuseStep 26459693 = 9922385) B9922385
theorem B17639795 : Blo 2063435 17639795 := bstep (se 1 (by rfl) ⟨13229846, by rfl⟩ : syracuseStep 17639795 = 26459693) B26459693
theorem B11759863 : Blo 2063435 11759863 := bstep (se 1 (by rfl) ⟨8819897, by rfl⟩ : syracuseStep 11759863 = 17639795) B17639795
theorem B15679817 : Blo 2063435 15679817 := bstep (se 2 (by rfl) ⟨5879931, by rfl⟩ : syracuseStep 15679817 = 11759863) B11759863
theorem B10453211 : Blo 2063435 10453211 := bstep (se 1 (by rfl) ⟨7839908, by rfl⟩ : syracuseStep 10453211 = 15679817) B15679817
theorem B6968807 : Blo 2063435 6968807 := bstep (se 1 (by rfl) ⟨5226605, by rfl⟩ : syracuseStep 6968807 = 10453211) B10453211
theorem B4645871 : Blo 2063435 4645871 := bstep (se 1 (by rfl) ⟨3484403, by rfl⟩ : syracuseStep 4645871 = 6968807) B6968807
theorem B3097247 : Blo 2063435 3097247 := bstep (se 1 (by rfl) ⟨2322935, by rfl⟩ : syracuseStep 3097247 = 4645871) B4645871
theorem B2064831 : Blo 2063435 2064831 := bstep (se 1 (by rfl) ⟨1548623, by rfl⟩ : syracuseStep 2064831 = 3097247) B3097247
theorem B3097253 : Blo 2063435 3097253 := bbase (se 4 (by rfl) ⟨290367, by rfl⟩ : syracuseStep 3097253 = 580735) (by norm_num)
theorem B2064835 : Blo 2063435 2064835 := bstep (se 1 (by rfl) ⟨1548626, by rfl⟩ : syracuseStep 2064835 = 3097253) B3097253
theorem B2613313 : Blo 2063435 2613313 := bbase (se 2 (by rfl) ⟨979992, by rfl⟩ : syracuseStep 2613313 = 1959985) (by norm_num)
theorem B3484417 : Blo 2063435 3484417 := bstep (se 2 (by rfl) ⟨1306656, by rfl⟩ : syracuseStep 3484417 = 2613313) B2613313
theorem B4645889 : Blo 2063435 4645889 := bstep (se 2 (by rfl) ⟨1742208, by rfl⟩ : syracuseStep 4645889 = 3484417) B3484417
theorem B3097259 : Blo 2063435 3097259 := bstep (se 1 (by rfl) ⟨2322944, by rfl⟩ : syracuseStep 3097259 = 4645889) B4645889
theorem B2064839 : Blo 2063435 2064839 := bstep (se 1 (by rfl) ⟨1548629, by rfl⟩ : syracuseStep 2064839 = 3097259) B3097259
theorem B2322949 : Blo 2063435 2322949 := bbase (se 4 (by rfl) ⟨217776, by rfl⟩ : syracuseStep 2322949 = 435553) (by norm_num)
theorem B3097265 : Blo 2063435 3097265 := bstep (se 2 (by rfl) ⟨1161474, by rfl⟩ : syracuseStep 3097265 = 2322949) B2322949
theorem B2064843 : Blo 2063435 2064843 := bstep (se 1 (by rfl) ⟨1548632, by rfl⟩ : syracuseStep 2064843 = 3097265) B3097265
theorem B2939989 : Blo 2063435 2939989 := bbase (se 8 (by rfl) ⟨17226, by rfl⟩ : syracuseStep 2939989 = 34453) (by norm_num)
theorem B3919985 : Blo 2063435 3919985 := bstep (se 2 (by rfl) ⟨1469994, by rfl⟩ : syracuseStep 3919985 = 2939989) B2939989
theorem B2613323 : Blo 2063435 2613323 := bstep (se 1 (by rfl) ⟨1959992, by rfl⟩ : syracuseStep 2613323 = 3919985) B3919985
theorem B6968861 : Blo 2063435 6968861 := bstep (se 3 (by rfl) ⟨1306661, by rfl⟩ : syracuseStep 6968861 = 2613323) B2613323
theorem B4645907 : Blo 2063435 4645907 := bstep (se 1 (by rfl) ⟨3484430, by rfl⟩ : syracuseStep 4645907 = 6968861) B6968861
theorem B3097271 : Blo 2063435 3097271 := bstep (se 1 (by rfl) ⟨2322953, by rfl⟩ : syracuseStep 3097271 = 4645907) B4645907
theorem B2064847 : Blo 2063435 2064847 := bstep (se 1 (by rfl) ⟨1548635, by rfl⟩ : syracuseStep 2064847 = 3097271) B3097271
theorem B3097277 : Blo 2063435 3097277 := bbase (se 3 (by rfl) ⟨580739, by rfl⟩ : syracuseStep 3097277 = 1161479) (by norm_num)
theorem B2064851 : Blo 2063435 2064851 := bstep (se 1 (by rfl) ⟨1548638, by rfl⟩ : syracuseStep 2064851 = 3097277) B3097277
theorem B4645925 : Blo 2063435 4645925 := bbase (se 4 (by rfl) ⟨435555, by rfl⟩ : syracuseStep 4645925 = 871111) (by norm_num)
theorem B3097283 : Blo 2063435 3097283 := bstep (se 1 (by rfl) ⟨2322962, by rfl⟩ : syracuseStep 3097283 = 4645925) B4645925
theorem B2064855 : Blo 2063435 2064855 := bstep (se 1 (by rfl) ⟨1548641, by rfl⟩ : syracuseStep 2064855 = 3097283) B3097283
theorem B5226677 : Blo 2063435 5226677 := bbase (se 5 (by rfl) ⟨245000, by rfl⟩ : syracuseStep 5226677 = 490001) (by norm_num)
theorem B3484451 : Blo 2063435 3484451 := bstep (se 1 (by rfl) ⟨2613338, by rfl⟩ : syracuseStep 3484451 = 5226677) B5226677
theorem B2322967 : Blo 2063435 2322967 := bstep (se 1 (by rfl) ⟨1742225, by rfl⟩ : syracuseStep 2322967 = 3484451) B3484451
theorem B3097289 : Blo 2063435 3097289 := bstep (se 2 (by rfl) ⟨1161483, by rfl⟩ : syracuseStep 3097289 = 2322967) B2322967
theorem B2064859 : Blo 2063435 2064859 := bstep (se 1 (by rfl) ⟨1548644, by rfl⟩ : syracuseStep 2064859 = 3097289) B3097289
theorem B4709333 : Blo 2063435 4709333 := bbase (se 7 (by rfl) ⟨55187, by rfl⟩ : syracuseStep 4709333 = 110375) (by norm_num)
theorem B3139555 : Blo 2063435 3139555 := bstep (se 1 (by rfl) ⟨2354666, by rfl⟩ : syracuseStep 3139555 = 4709333) B4709333
theorem B4186073 : Blo 2063435 4186073 := bstep (se 2 (by rfl) ⟨1569777, by rfl⟩ : syracuseStep 4186073 = 3139555) B3139555
theorem B2790715 : Blo 2063435 2790715 := bstep (se 1 (by rfl) ⟨2093036, by rfl⟩ : syracuseStep 2790715 = 4186073) B4186073
theorem B3720953 : Blo 2063435 3720953 := bstep (se 2 (by rfl) ⟨1395357, by rfl⟩ : syracuseStep 3720953 = 2790715) B2790715
theorem B2480635 : Blo 2063435 2480635 := bstep (se 1 (by rfl) ⟨1860476, by rfl⟩ : syracuseStep 2480635 = 3720953) B3720953
theorem B13230053 : Blo 2063435 13230053 := bstep (se 4 (by rfl) ⟨1240317, by rfl⟩ : syracuseStep 13230053 = 2480635) B2480635
theorem B8820035 : Blo 2063435 8820035 := bstep (se 1 (by rfl) ⟨6615026, by rfl⟩ : syracuseStep 8820035 = 13230053) B13230053
theorem B5880023 : Blo 2063435 5880023 := bstep (se 1 (by rfl) ⟨4410017, by rfl⟩ : syracuseStep 5880023 = 8820035) B8820035
theorem B3920015 : Blo 2063435 3920015 := bstep (se 1 (by rfl) ⟨2940011, by rfl⟩ : syracuseStep 3920015 = 5880023) B5880023
theorem B10453373 : Blo 2063435 10453373 := bstep (se 3 (by rfl) ⟨1960007, by rfl⟩ : syracuseStep 10453373 = 3920015) B3920015
theorem B6968915 : Blo 2063435 6968915 := bstep (se 1 (by rfl) ⟨5226686, by rfl⟩ : syracuseStep 6968915 = 10453373) B10453373
theorem B4645943 : Blo 2063435 4645943 := bstep (se 1 (by rfl) ⟨3484457, by rfl⟩ : syracuseStep 4645943 = 6968915) B6968915
theorem B3097295 : Blo 2063435 3097295 := bstep (se 1 (by rfl) ⟨2322971, by rfl⟩ : syracuseStep 3097295 = 4645943) B4645943
theorem B2064863 : Blo 2063435 2064863 := bstep (se 1 (by rfl) ⟨1548647, by rfl⟩ : syracuseStep 2064863 = 3097295) B3097295
theorem B3097301 : Blo 2063435 3097301 := bbase (se 7 (by rfl) ⟨36296, by rfl⟩ : syracuseStep 3097301 = 72593) (by norm_num)
theorem B2064867 : Blo 2063435 2064867 := bstep (se 1 (by rfl) ⟨1548650, by rfl⟩ : syracuseStep 2064867 = 3097301) B3097301
theorem B2480645 : Blo 2063435 2480645 := bbase (se 4 (by rfl) ⟨232560, by rfl⟩ : syracuseStep 2480645 = 465121) (by norm_num)
theorem B6615053 : Blo 2063435 6615053 := bstep (se 3 (by rfl) ⟨1240322, by rfl⟩ : syracuseStep 6615053 = 2480645) B2480645
theorem B4410035 : Blo 2063435 4410035 := bstep (se 1 (by rfl) ⟨3307526, by rfl⟩ : syracuseStep 4410035 = 6615053) B6615053
theorem B2940023 : Blo 2063435 2940023 := bstep (se 1 (by rfl) ⟨2205017, by rfl⟩ : syracuseStep 2940023 = 4410035) B4410035
theorem B7840061 : Blo 2063435 7840061 := bstep (se 3 (by rfl) ⟨1470011, by rfl⟩ : syracuseStep 7840061 = 2940023) B2940023
theorem B5226707 : Blo 2063435 5226707 := bstep (se 1 (by rfl) ⟨3920030, by rfl⟩ : syracuseStep 5226707 = 7840061) B7840061
theorem B3484471 : Blo 2063435 3484471 := bstep (se 1 (by rfl) ⟨2613353, by rfl⟩ : syracuseStep 3484471 = 5226707) B5226707
theorem B4645961 : Blo 2063435 4645961 := bstep (se 2 (by rfl) ⟨1742235, by rfl⟩ : syracuseStep 4645961 = 3484471) B3484471
theorem B3097307 : Blo 2063435 3097307 := bstep (se 1 (by rfl) ⟨2322980, by rfl⟩ : syracuseStep 3097307 = 4645961) B4645961
theorem B2064871 : Blo 2063435 2064871 := bstep (se 1 (by rfl) ⟨1548653, by rfl⟩ : syracuseStep 2064871 = 3097307) B3097307
theorem B2322985 : Blo 2063435 2322985 := bbase (se 2 (by rfl) ⟨871119, by rfl⟩ : syracuseStep 2322985 = 1742239) (by norm_num)
theorem B3097313 : Blo 2063435 3097313 := bstep (se 2 (by rfl) ⟨1161492, by rfl⟩ : syracuseStep 3097313 = 2322985) B2322985
theorem B2064875 : Blo 2063435 2064875 := bstep (se 1 (by rfl) ⟨1548656, by rfl⟩ : syracuseStep 2064875 = 3097313) B3097313
theorem B14883925 : Blo 2063435 14883925 := bbase (se 8 (by rfl) ⟨87210, by rfl⟩ : syracuseStep 14883925 = 174421) (by norm_num)
theorem B19845233 : Blo 2063435 19845233 := bstep (se 2 (by rfl) ⟨7441962, by rfl⟩ : syracuseStep 19845233 = 14883925) B14883925
theorem B13230155 : Blo 2063435 13230155 := bstep (se 1 (by rfl) ⟨9922616, by rfl⟩ : syracuseStep 13230155 = 19845233) B19845233
theorem B8820103 : Blo 2063435 8820103 := bstep (se 1 (by rfl) ⟨6615077, by rfl⟩ : syracuseStep 8820103 = 13230155) B13230155
theorem B11760137 : Blo 2063435 11760137 := bstep (se 2 (by rfl) ⟨4410051, by rfl⟩ : syracuseStep 11760137 = 8820103) B8820103
theorem B7840091 : Blo 2063435 7840091 := bstep (se 1 (by rfl) ⟨5880068, by rfl⟩ : syracuseStep 7840091 = 11760137) B11760137
theorem B5226727 : Blo 2063435 5226727 := bstep (se 1 (by rfl) ⟨3920045, by rfl⟩ : syracuseStep 5226727 = 7840091) B7840091
theorem B6968969 : Blo 2063435 6968969 := bstep (se 2 (by rfl) ⟨2613363, by rfl⟩ : syracuseStep 6968969 = 5226727) B5226727
theorem B4645979 : Blo 2063435 4645979 := bstep (se 1 (by rfl) ⟨3484484, by rfl⟩ : syracuseStep 4645979 = 6968969) B6968969
theorem B3097319 : Blo 2063435 3097319 := bstep (se 1 (by rfl) ⟨2322989, by rfl⟩ : syracuseStep 3097319 = 4645979) B4645979
theorem B2064879 : Blo 2063435 2064879 := bstep (se 1 (by rfl) ⟨1548659, by rfl⟩ : syracuseStep 2064879 = 3097319) B3097319
theorem B3097325 : Blo 2063435 3097325 := bbase (se 3 (by rfl) ⟨580748, by rfl⟩ : syracuseStep 3097325 = 1161497) (by norm_num)
theorem B2064883 : Blo 2063435 2064883 := bstep (se 1 (by rfl) ⟨1548662, by rfl⟩ : syracuseStep 2064883 = 3097325) B3097325
theorem B4645997 : Blo 2063435 4645997 := bbase (se 3 (by rfl) ⟨871124, by rfl⟩ : syracuseStep 4645997 = 1742249) (by norm_num)
theorem B3097331 : Blo 2063435 3097331 := bstep (se 1 (by rfl) ⟨2322998, by rfl⟩ : syracuseStep 3097331 = 4645997) B4645997
theorem B2064887 : Blo 2063435 2064887 := bstep (se 1 (by rfl) ⟨1548665, by rfl⟩ : syracuseStep 2064887 = 3097331) B3097331
theorem B3920069 : Blo 2063435 3920069 := bbase (se 4 (by rfl) ⟨367506, by rfl⟩ : syracuseStep 3920069 = 735013) (by norm_num)
theorem B2613379 : Blo 2063435 2613379 := bstep (se 1 (by rfl) ⟨1960034, by rfl⟩ : syracuseStep 2613379 = 3920069) B3920069
theorem B3484505 : Blo 2063435 3484505 := bstep (se 2 (by rfl) ⟨1306689, by rfl⟩ : syracuseStep 3484505 = 2613379) B2613379
theorem B2323003 : Blo 2063435 2323003 := bstep (se 1 (by rfl) ⟨1742252, by rfl⟩ : syracuseStep 2323003 = 3484505) B3484505
theorem B3097337 : Blo 2063435 3097337 := bstep (se 2 (by rfl) ⟨1161501, by rfl⟩ : syracuseStep 3097337 = 2323003) B2323003
theorem B2064891 : Blo 2063435 2064891 := bstep (se 1 (by rfl) ⟨1548668, by rfl⟩ : syracuseStep 2064891 = 3097337) B3097337
theorem B11163029 : Blo 2063435 11163029 := bbase (se 6 (by rfl) ⟨261633, by rfl⟩ : syracuseStep 11163029 = 523267) (by norm_num)
theorem B29768077 : Blo 2063435 29768077 := bstep (se 3 (by rfl) ⟨5581514, by rfl⟩ : syracuseStep 29768077 = 11163029) B11163029
theorem B39690769 : Blo 2063435 39690769 := bstep (se 2 (by rfl) ⟨14884038, by rfl⟩ : syracuseStep 39690769 = 29768077) B29768077
theorem B52921025 : Blo 2063435 52921025 := bstep (se 2 (by rfl) ⟨19845384, by rfl⟩ : syracuseStep 52921025 = 39690769) B39690769
theorem B35280683 : Blo 2063435 35280683 := bstep (se 1 (by rfl) ⟨26460512, by rfl⟩ : syracuseStep 35280683 = 52921025) B52921025
theorem B23520455 : Blo 2063435 23520455 := bstep (se 1 (by rfl) ⟨17640341, by rfl⟩ : syracuseStep 23520455 = 35280683) B35280683
theorem B15680303 : Blo 2063435 15680303 := bstep (se 1 (by rfl) ⟨11760227, by rfl⟩ : syracuseStep 15680303 = 23520455) B23520455
theorem B10453535 : Blo 2063435 10453535 := bstep (se 1 (by rfl) ⟨7840151, by rfl⟩ : syracuseStep 10453535 = 15680303) B15680303
theorem B6969023 : Blo 2063435 6969023 := bstep (se 1 (by rfl) ⟨5226767, by rfl⟩ : syracuseStep 6969023 = 10453535) B10453535
theorem B4646015 : Blo 2063435 4646015 := bstep (se 1 (by rfl) ⟨3484511, by rfl⟩ : syracuseStep 4646015 = 6969023) B6969023
theorem B3097343 : Blo 2063435 3097343 := bstep (se 1 (by rfl) ⟨2323007, by rfl⟩ : syracuseStep 3097343 = 4646015) B4646015
theorem B2064895 : Blo 2063435 2064895 := bstep (se 1 (by rfl) ⟨1548671, by rfl⟩ : syracuseStep 2064895 = 3097343) B3097343
theorem B3097349 : Blo 2063435 3097349 := bbase (se 4 (by rfl) ⟨290376, by rfl⟩ : syracuseStep 3097349 = 580753) (by norm_num)
theorem B2064899 : Blo 2063435 2064899 := bstep (se 1 (by rfl) ⟨1548674, by rfl⟩ : syracuseStep 2064899 = 3097349) B3097349
theorem B3484525 : Blo 2063435 3484525 := bbase (se 3 (by rfl) ⟨653348, by rfl⟩ : syracuseStep 3484525 = 1306697) (by norm_num)
theorem B4646033 : Blo 2063435 4646033 := bstep (se 2 (by rfl) ⟨1742262, by rfl⟩ : syracuseStep 4646033 = 3484525) B3484525
theorem B3097355 : Blo 2063435 3097355 := bstep (se 1 (by rfl) ⟨2323016, by rfl⟩ : syracuseStep 3097355 = 4646033) B4646033
theorem B2064903 : Blo 2063435 2064903 := bstep (se 1 (by rfl) ⟨1548677, by rfl⟩ : syracuseStep 2064903 = 3097355) B3097355
theorem B2323021 : Blo 2063435 2323021 := bbase (se 3 (by rfl) ⟨435566, by rfl⟩ : syracuseStep 2323021 = 871133) (by norm_num)
theorem B3097361 : Blo 2063435 3097361 := bstep (se 2 (by rfl) ⟨1161510, by rfl⟩ : syracuseStep 3097361 = 2323021) B2323021
theorem B2064907 : Blo 2063435 2064907 := bstep (se 1 (by rfl) ⟨1548680, by rfl⟩ : syracuseStep 2064907 = 3097361) B3097361
theorem B6969077 : Blo 2063435 6969077 := bbase (se 5 (by rfl) ⟨326675, by rfl⟩ : syracuseStep 6969077 = 653351) (by norm_num)
theorem B4646051 : Blo 2063435 4646051 := bstep (se 1 (by rfl) ⟨3484538, by rfl⟩ : syracuseStep 4646051 = 6969077) B6969077
theorem B3097367 : Blo 2063435 3097367 := bstep (se 1 (by rfl) ⟨2323025, by rfl⟩ : syracuseStep 3097367 = 4646051) B4646051
theorem B2064911 : Blo 2063435 2064911 := bstep (se 1 (by rfl) ⟨1548683, by rfl⟩ : syracuseStep 2064911 = 3097367) B3097367
theorem B3097373 : Blo 2063435 3097373 := bbase (se 3 (by rfl) ⟨580757, by rfl⟩ : syracuseStep 3097373 = 1161515) (by norm_num)
theorem B2064915 : Blo 2063435 2064915 := bstep (se 1 (by rfl) ⟨1548686, by rfl⟩ : syracuseStep 2064915 = 3097373) B3097373
theorem B4646069 : Blo 2063435 4646069 := bbase (se 5 (by rfl) ⟨217784, by rfl⟩ : syracuseStep 4646069 = 435569) (by norm_num)
theorem B3097379 : Blo 2063435 3097379 := bstep (se 1 (by rfl) ⟨2323034, by rfl⟩ : syracuseStep 3097379 = 4646069) B4646069
theorem B2064919 : Blo 2063435 2064919 := bstep (se 1 (by rfl) ⟨1548689, by rfl⟩ : syracuseStep 2064919 = 3097379) B3097379
theorem B2205073 : Blo 2063435 2205073 := bbase (se 2 (by rfl) ⟨826902, by rfl⟩ : syracuseStep 2205073 = 1653805) (by norm_num)
theorem B11760389 : Blo 2063435 11760389 := bstep (se 4 (by rfl) ⟨1102536, by rfl⟩ : syracuseStep 11760389 = 2205073) B2205073
theorem B7840259 : Blo 2063435 7840259 := bstep (se 1 (by rfl) ⟨5880194, by rfl⟩ : syracuseStep 7840259 = 11760389) B11760389
theorem B5226839 : Blo 2063435 5226839 := bstep (se 1 (by rfl) ⟨3920129, by rfl⟩ : syracuseStep 5226839 = 7840259) B7840259
theorem B3484559 : Blo 2063435 3484559 := bstep (se 1 (by rfl) ⟨2613419, by rfl⟩ : syracuseStep 3484559 = 5226839) B5226839
theorem B2323039 : Blo 2063435 2323039 := bstep (se 1 (by rfl) ⟨1742279, by rfl⟩ : syracuseStep 2323039 = 3484559) B3484559
theorem B3097385 : Blo 2063435 3097385 := bstep (se 2 (by rfl) ⟨1161519, by rfl⟩ : syracuseStep 3097385 = 2323039) B2323039
theorem B2064923 : Blo 2063435 2064923 := bstep (se 1 (by rfl) ⟨1548692, by rfl⟩ : syracuseStep 2064923 = 3097385) B3097385
theorem B2205077 : Blo 2063435 2205077 := bbase (se 6 (by rfl) ⟨51681, by rfl⟩ : syracuseStep 2205077 = 103363) (by norm_num)
theorem B5880205 : Blo 2063435 5880205 := bstep (se 3 (by rfl) ⟨1102538, by rfl⟩ : syracuseStep 5880205 = 2205077) B2205077
theorem B7840273 : Blo 2063435 7840273 := bstep (se 2 (by rfl) ⟨2940102, by rfl⟩ : syracuseStep 7840273 = 5880205) B5880205
theorem B10453697 : Blo 2063435 10453697 := bstep (se 2 (by rfl) ⟨3920136, by rfl⟩ : syracuseStep 10453697 = 7840273) B7840273
theorem B6969131 : Blo 2063435 6969131 := bstep (se 1 (by rfl) ⟨5226848, by rfl⟩ : syracuseStep 6969131 = 10453697) B10453697
theorem B4646087 : Blo 2063435 4646087 := bstep (se 1 (by rfl) ⟨3484565, by rfl⟩ : syracuseStep 4646087 = 6969131) B6969131
theorem B3097391 : Blo 2063435 3097391 := bstep (se 1 (by rfl) ⟨2323043, by rfl⟩ : syracuseStep 3097391 = 4646087) B4646087
theorem B2064927 : Blo 2063435 2064927 := bstep (se 1 (by rfl) ⟨1548695, by rfl⟩ : syracuseStep 2064927 = 3097391) B3097391
theorem B3097397 : Blo 2063435 3097397 := bbase (se 5 (by rfl) ⟨145190, by rfl⟩ : syracuseStep 3097397 = 290381) (by norm_num)
theorem B2064931 : Blo 2063435 2064931 := bstep (se 1 (by rfl) ⟨1548698, by rfl⟩ : syracuseStep 2064931 = 3097397) B3097397
theorem B5226869 : Blo 2063435 5226869 := bbase (se 5 (by rfl) ⟨245009, by rfl⟩ : syracuseStep 5226869 = 490019) (by norm_num)
theorem B3484579 : Blo 2063435 3484579 := bstep (se 1 (by rfl) ⟨2613434, by rfl⟩ : syracuseStep 3484579 = 5226869) B5226869
theorem B4646105 : Blo 2063435 4646105 := bstep (se 2 (by rfl) ⟨1742289, by rfl⟩ : syracuseStep 4646105 = 3484579) B3484579
theorem B3097403 : Blo 2063435 3097403 := bstep (se 1 (by rfl) ⟨2323052, by rfl⟩ : syracuseStep 3097403 = 4646105) B4646105
theorem B2064935 : Blo 2063435 2064935 := bstep (se 1 (by rfl) ⟨1548701, by rfl⟩ : syracuseStep 2064935 = 3097403) B3097403
theorem B2323057 : Blo 2063435 2323057 := bbase (se 2 (by rfl) ⟨871146, by rfl⟩ : syracuseStep 2323057 = 1742293) (by norm_num)
theorem B3097409 : Blo 2063435 3097409 := bstep (se 2 (by rfl) ⟨1161528, by rfl⟩ : syracuseStep 3097409 = 2323057) B2323057
theorem B2064939 : Blo 2063435 2064939 := bstep (se 1 (by rfl) ⟨1548704, by rfl⟩ : syracuseStep 2064939 = 3097409) B3097409
theorem B5298205 : Blo 2063435 5298205 := bbase (se 3 (by rfl) ⟨993413, by rfl⟩ : syracuseStep 5298205 = 1986827) (by norm_num)
theorem B7064273 : Blo 2063435 7064273 := bstep (se 2 (by rfl) ⟨2649102, by rfl⟩ : syracuseStep 7064273 = 5298205) B5298205
theorem B4709515 : Blo 2063435 4709515 := bstep (se 1 (by rfl) ⟨3532136, by rfl⟩ : syracuseStep 4709515 = 7064273) B7064273
theorem B6279353 : Blo 2063435 6279353 := bstep (se 2 (by rfl) ⟨2354757, by rfl⟩ : syracuseStep 6279353 = 4709515) B4709515
theorem B4186235 : Blo 2063435 4186235 := bstep (se 1 (by rfl) ⟨3139676, by rfl⟩ : syracuseStep 4186235 = 6279353) B6279353
theorem B2790823 : Blo 2063435 2790823 := bstep (se 1 (by rfl) ⟨2093117, by rfl⟩ : syracuseStep 2790823 = 4186235) B4186235
theorem B3721097 : Blo 2063435 3721097 := bstep (se 2 (by rfl) ⟨1395411, by rfl⟩ : syracuseStep 3721097 = 2790823) B2790823
theorem B9922925 : Blo 2063435 9922925 := bstep (se 3 (by rfl) ⟨1860548, by rfl⟩ : syracuseStep 9922925 = 3721097) B3721097
theorem B6615283 : Blo 2063435 6615283 := bstep (se 1 (by rfl) ⟨4961462, by rfl⟩ : syracuseStep 6615283 = 9922925) B9922925
theorem B8820377 : Blo 2063435 8820377 := bstep (se 2 (by rfl) ⟨3307641, by rfl⟩ : syracuseStep 8820377 = 6615283) B6615283
theorem B5880251 : Blo 2063435 5880251 := bstep (se 1 (by rfl) ⟨4410188, by rfl⟩ : syracuseStep 5880251 = 8820377) B8820377
theorem B3920167 : Blo 2063435 3920167 := bstep (se 1 (by rfl) ⟨2940125, by rfl⟩ : syracuseStep 3920167 = 5880251) B5880251
theorem B5226889 : Blo 2063435 5226889 := bstep (se 2 (by rfl) ⟨1960083, by rfl⟩ : syracuseStep 5226889 = 3920167) B3920167
theorem B6969185 : Blo 2063435 6969185 := bstep (se 2 (by rfl) ⟨2613444, by rfl⟩ : syracuseStep 6969185 = 5226889) B5226889
theorem B4646123 : Blo 2063435 4646123 := bstep (se 1 (by rfl) ⟨3484592, by rfl⟩ : syracuseStep 4646123 = 6969185) B6969185
theorem B3097415 : Blo 2063435 3097415 := bstep (se 1 (by rfl) ⟨2323061, by rfl⟩ : syracuseStep 3097415 = 4646123) B4646123
theorem B2064943 : Blo 2063435 2064943 := bstep (se 1 (by rfl) ⟨1548707, by rfl⟩ : syracuseStep 2064943 = 3097415) B3097415
theorem B3097421 : Blo 2063435 3097421 := bbase (se 3 (by rfl) ⟨580766, by rfl⟩ : syracuseStep 3097421 = 1161533) (by norm_num)
theorem B2064947 : Blo 2063435 2064947 := bstep (se 1 (by rfl) ⟨1548710, by rfl⟩ : syracuseStep 2064947 = 3097421) B3097421
theorem B4646141 : Blo 2063435 4646141 := bbase (se 3 (by rfl) ⟨871151, by rfl⟩ : syracuseStep 4646141 = 1742303) (by norm_num)
theorem B3097427 : Blo 2063435 3097427 := bstep (se 1 (by rfl) ⟨2323070, by rfl⟩ : syracuseStep 3097427 = 4646141) B4646141
theorem B2064951 : Blo 2063435 2064951 := bstep (se 1 (by rfl) ⟨1548713, by rfl⟩ : syracuseStep 2064951 = 3097427) B3097427
theorem B3484613 : Blo 2063435 3484613 := bbase (se 4 (by rfl) ⟨326682, by rfl⟩ : syracuseStep 3484613 = 653365) (by norm_num)
theorem B2323075 : Blo 2063435 2323075 := bstep (se 1 (by rfl) ⟨1742306, by rfl⟩ : syracuseStep 2323075 = 3484613) B3484613
theorem B3097433 : Blo 2063435 3097433 := bstep (se 2 (by rfl) ⟨1161537, by rfl⟩ : syracuseStep 3097433 = 2323075) B2323075
theorem B2064955 : Blo 2063435 2064955 := bstep (se 1 (by rfl) ⟨1548716, by rfl⟩ : syracuseStep 2064955 = 3097433) B3097433
theorem B15680789 : Blo 2063435 15680789 := bbase (se 6 (by rfl) ⟨367518, by rfl⟩ : syracuseStep 15680789 = 735037) (by norm_num)
theorem B10453859 : Blo 2063435 10453859 := bstep (se 1 (by rfl) ⟨7840394, by rfl⟩ : syracuseStep 10453859 = 15680789) B15680789
theorem B6969239 : Blo 2063435 6969239 := bstep (se 1 (by rfl) ⟨5226929, by rfl⟩ : syracuseStep 6969239 = 10453859) B10453859
theorem B4646159 : Blo 2063435 4646159 := bstep (se 1 (by rfl) ⟨3484619, by rfl⟩ : syracuseStep 4646159 = 6969239) B6969239
theorem B3097439 : Blo 2063435 3097439 := bstep (se 1 (by rfl) ⟨2323079, by rfl⟩ : syracuseStep 3097439 = 4646159) B4646159
theorem B2064959 : Blo 2063435 2064959 := bstep (se 1 (by rfl) ⟨1548719, by rfl⟩ : syracuseStep 2064959 = 3097439) B3097439
theorem B3097445 : Blo 2063435 3097445 := bbase (se 4 (by rfl) ⟨290385, by rfl⟩ : syracuseStep 3097445 = 580771) (by norm_num)
theorem B2064963 : Blo 2063435 2064963 := bstep (se 1 (by rfl) ⟨1548722, by rfl⟩ : syracuseStep 2064963 = 3097445) B3097445
theorem B3920213 : Blo 2063435 3920213 := bbase (se 10 (by rfl) ⟨5742, by rfl⟩ : syracuseStep 3920213 = 11485) (by norm_num)
theorem B2613475 : Blo 2063435 2613475 := bstep (se 1 (by rfl) ⟨1960106, by rfl⟩ : syracuseStep 2613475 = 3920213) B3920213
theorem B3484633 : Blo 2063435 3484633 := bstep (se 2 (by rfl) ⟨1306737, by rfl⟩ : syracuseStep 3484633 = 2613475) B2613475
theorem B4646177 : Blo 2063435 4646177 := bstep (se 2 (by rfl) ⟨1742316, by rfl⟩ : syracuseStep 4646177 = 3484633) B3484633
theorem B3097451 : Blo 2063435 3097451 := bstep (se 1 (by rfl) ⟨2323088, by rfl⟩ : syracuseStep 3097451 = 4646177) B4646177
theorem B2064967 : Blo 2063435 2064967 := bstep (se 1 (by rfl) ⟨1548725, by rfl⟩ : syracuseStep 2064967 = 3097451) B3097451
theorem B2323093 : Blo 2063435 2323093 := bbase (se 6 (by rfl) ⟨54447, by rfl⟩ : syracuseStep 2323093 = 108895) (by norm_num)
theorem B3097457 : Blo 2063435 3097457 := bstep (se 2 (by rfl) ⟨1161546, by rfl⟩ : syracuseStep 3097457 = 2323093) B2323093
theorem B2064971 : Blo 2063435 2064971 := bstep (se 1 (by rfl) ⟨1548728, by rfl⟩ : syracuseStep 2064971 = 3097457) B3097457
theorem B2613485 : Blo 2063435 2613485 := bbase (se 3 (by rfl) ⟨490028, by rfl⟩ : syracuseStep 2613485 = 980057) (by norm_num)
theorem B6969293 : Blo 2063435 6969293 := bstep (se 3 (by rfl) ⟨1306742, by rfl⟩ : syracuseStep 6969293 = 2613485) B2613485
theorem B4646195 : Blo 2063435 4646195 := bstep (se 1 (by rfl) ⟨3484646, by rfl⟩ : syracuseStep 4646195 = 6969293) B6969293
theorem B3097463 : Blo 2063435 3097463 := bstep (se 1 (by rfl) ⟨2323097, by rfl⟩ : syracuseStep 3097463 = 4646195) B4646195
theorem B2064975 : Blo 2063435 2064975 := bstep (se 1 (by rfl) ⟨1548731, by rfl⟩ : syracuseStep 2064975 = 3097463) B3097463
theorem B3097469 : Blo 2063435 3097469 := bbase (se 3 (by rfl) ⟨580775, by rfl⟩ : syracuseStep 3097469 = 1161551) (by norm_num)
theorem B2064979 : Blo 2063435 2064979 := bstep (se 1 (by rfl) ⟨1548734, by rfl⟩ : syracuseStep 2064979 = 3097469) B3097469
theorem B4646213 : Blo 2063435 4646213 := bbase (se 4 (by rfl) ⟨435582, by rfl⟩ : syracuseStep 4646213 = 871165) (by norm_num)
theorem B3097475 : Blo 2063435 3097475 := bstep (se 1 (by rfl) ⟨2323106, by rfl⟩ : syracuseStep 3097475 = 4646213) B4646213
theorem B2064983 : Blo 2063435 2064983 := bstep (se 1 (by rfl) ⟨1548737, by rfl⟩ : syracuseStep 2064983 = 3097475) B3097475
theorem B4186325 : Blo 2063435 4186325 := bbase (se 7 (by rfl) ⟨49058, by rfl⟩ : syracuseStep 4186325 = 98117) (by norm_num)
theorem B2790883 : Blo 2063435 2790883 := bstep (se 1 (by rfl) ⟨2093162, by rfl⟩ : syracuseStep 2790883 = 4186325) B4186325
theorem B3721177 : Blo 2063435 3721177 := bstep (se 2 (by rfl) ⟨1395441, by rfl⟩ : syracuseStep 3721177 = 2790883) B2790883
theorem B4961569 : Blo 2063435 4961569 := bstep (se 2 (by rfl) ⟨1860588, by rfl⟩ : syracuseStep 4961569 = 3721177) B3721177
theorem B6615425 : Blo 2063435 6615425 := bstep (se 2 (by rfl) ⟨2480784, by rfl⟩ : syracuseStep 6615425 = 4961569) B4961569
theorem B4410283 : Blo 2063435 4410283 := bstep (se 1 (by rfl) ⟨3307712, by rfl⟩ : syracuseStep 4410283 = 6615425) B6615425
theorem B5880377 : Blo 2063435 5880377 := bstep (se 2 (by rfl) ⟨2205141, by rfl⟩ : syracuseStep 5880377 = 4410283) B4410283
theorem B3920251 : Blo 2063435 3920251 := bstep (se 1 (by rfl) ⟨2940188, by rfl⟩ : syracuseStep 3920251 = 5880377) B5880377
theorem B5227001 : Blo 2063435 5227001 := bstep (se 2 (by rfl) ⟨1960125, by rfl⟩ : syracuseStep 5227001 = 3920251) B3920251
theorem B3484667 : Blo 2063435 3484667 := bstep (se 1 (by rfl) ⟨2613500, by rfl⟩ : syracuseStep 3484667 = 5227001) B5227001
theorem B2323111 : Blo 2063435 2323111 := bstep (se 1 (by rfl) ⟨1742333, by rfl⟩ : syracuseStep 2323111 = 3484667) B3484667
theorem B3097481 : Blo 2063435 3097481 := bstep (se 2 (by rfl) ⟨1161555, by rfl⟩ : syracuseStep 3097481 = 2323111) B2323111
theorem B2064987 : Blo 2063435 2064987 := bstep (se 1 (by rfl) ⟨1548740, by rfl⟩ : syracuseStep 2064987 = 3097481) B3097481
theorem B10454021 : Blo 2063435 10454021 := bbase (se 4 (by rfl) ⟨980064, by rfl⟩ : syracuseStep 10454021 = 1960129) (by norm_num)
theorem B6969347 : Blo 2063435 6969347 := bstep (se 1 (by rfl) ⟨5227010, by rfl⟩ : syracuseStep 6969347 = 10454021) B10454021
theorem B4646231 : Blo 2063435 4646231 := bstep (se 1 (by rfl) ⟨3484673, by rfl⟩ : syracuseStep 4646231 = 6969347) B6969347
theorem B3097487 : Blo 2063435 3097487 := bstep (se 1 (by rfl) ⟨2323115, by rfl⟩ : syracuseStep 3097487 = 4646231) B4646231
theorem B2064991 : Blo 2063435 2064991 := bstep (se 1 (by rfl) ⟨1548743, by rfl⟩ : syracuseStep 2064991 = 3097487) B3097487
theorem B3097493 : Blo 2063435 3097493 := bbase (se 6 (by rfl) ⟨72597, by rfl⟩ : syracuseStep 3097493 = 145195) (by norm_num)
theorem B2064995 : Blo 2063435 2064995 := bstep (se 1 (by rfl) ⟨1548746, by rfl⟩ : syracuseStep 2064995 = 3097493) B3097493
theorem B11760821 : Blo 2063435 11760821 := bbase (se 5 (by rfl) ⟨551288, by rfl⟩ : syracuseStep 11760821 = 1102577) (by norm_num)
theorem B7840547 : Blo 2063435 7840547 := bstep (se 1 (by rfl) ⟨5880410, by rfl⟩ : syracuseStep 7840547 = 11760821) B11760821
theorem B5227031 : Blo 2063435 5227031 := bstep (se 1 (by rfl) ⟨3920273, by rfl⟩ : syracuseStep 5227031 = 7840547) B7840547
theorem B3484687 : Blo 2063435 3484687 := bstep (se 1 (by rfl) ⟨2613515, by rfl⟩ : syracuseStep 3484687 = 5227031) B5227031
theorem B4646249 : Blo 2063435 4646249 := bstep (se 2 (by rfl) ⟨1742343, by rfl⟩ : syracuseStep 4646249 = 3484687) B3484687
theorem B3097499 : Blo 2063435 3097499 := bstep (se 1 (by rfl) ⟨2323124, by rfl⟩ : syracuseStep 3097499 = 4646249) B4646249
theorem B2064999 : Blo 2063435 2064999 := bstep (se 1 (by rfl) ⟨1548749, by rfl⟩ : syracuseStep 2064999 = 3097499) B3097499
theorem B2323129 : Blo 2063435 2323129 := bbase (se 2 (by rfl) ⟨871173, by rfl⟩ : syracuseStep 2323129 = 1742347) (by norm_num)
theorem B3097505 : Blo 2063435 3097505 := bstep (se 2 (by rfl) ⟨1161564, by rfl⟩ : syracuseStep 3097505 = 2323129) B2323129
theorem B2065003 : Blo 2063435 2065003 := bstep (se 1 (by rfl) ⟨1548752, by rfl⟩ : syracuseStep 2065003 = 3097505) B3097505
theorem B4410325 : Blo 2063435 4410325 := bbase (se 7 (by rfl) ⟨51683, by rfl⟩ : syracuseStep 4410325 = 103367) (by norm_num)
theorem B5880433 : Blo 2063435 5880433 := bstep (se 2 (by rfl) ⟨2205162, by rfl⟩ : syracuseStep 5880433 = 4410325) B4410325
theorem B7840577 : Blo 2063435 7840577 := bstep (se 2 (by rfl) ⟨2940216, by rfl⟩ : syracuseStep 7840577 = 5880433) B5880433
theorem B5227051 : Blo 2063435 5227051 := bstep (se 1 (by rfl) ⟨3920288, by rfl⟩ : syracuseStep 5227051 = 7840577) B7840577
theorem B6969401 : Blo 2063435 6969401 := bstep (se 2 (by rfl) ⟨2613525, by rfl⟩ : syracuseStep 6969401 = 5227051) B5227051
theorem B4646267 : Blo 2063435 4646267 := bstep (se 1 (by rfl) ⟨3484700, by rfl⟩ : syracuseStep 4646267 = 6969401) B6969401
theorem B3097511 : Blo 2063435 3097511 := bstep (se 1 (by rfl) ⟨2323133, by rfl⟩ : syracuseStep 3097511 = 4646267) B4646267
theorem B2065007 : Blo 2063435 2065007 := bstep (se 1 (by rfl) ⟨1548755, by rfl⟩ : syracuseStep 2065007 = 3097511) B3097511
theorem B3097517 : Blo 2063435 3097517 := bbase (se 3 (by rfl) ⟨580784, by rfl⟩ : syracuseStep 3097517 = 1161569) (by norm_num)
theorem B2065011 : Blo 2063435 2065011 := bstep (se 1 (by rfl) ⟨1548758, by rfl⟩ : syracuseStep 2065011 = 3097517) B3097517
theorem B4646285 : Blo 2063435 4646285 := bbase (se 3 (by rfl) ⟨871178, by rfl⟩ : syracuseStep 4646285 = 1742357) (by norm_num)
theorem B3097523 : Blo 2063435 3097523 := bstep (se 1 (by rfl) ⟨2323142, by rfl⟩ : syracuseStep 3097523 = 4646285) B4646285
theorem B2065015 : Blo 2063435 2065015 := bstep (se 1 (by rfl) ⟨1548761, by rfl⟩ : syracuseStep 2065015 = 3097523) B3097523
theorem B2613541 : Blo 2063435 2613541 := bbase (se 4 (by rfl) ⟨245019, by rfl⟩ : syracuseStep 2613541 = 490039) (by norm_num)
theorem B3484721 : Blo 2063435 3484721 := bstep (se 2 (by rfl) ⟨1306770, by rfl⟩ : syracuseStep 3484721 = 2613541) B2613541
theorem B2323147 : Blo 2063435 2323147 := bstep (se 1 (by rfl) ⟨1742360, by rfl⟩ : syracuseStep 2323147 = 3484721) B3484721
theorem B3097529 : Blo 2063435 3097529 := bstep (se 2 (by rfl) ⟨1161573, by rfl⟩ : syracuseStep 3097529 = 2323147) B2323147
theorem B2065019 : Blo 2063435 2065019 := bstep (se 1 (by rfl) ⟨1548764, by rfl⟩ : syracuseStep 2065019 = 3097529) B3097529
theorem B2685349 : Blo 2063435 2685349 := bbase (se 4 (by rfl) ⟨251751, by rfl⟩ : syracuseStep 2685349 = 503503) (by norm_num)
theorem B3580465 : Blo 2063435 3580465 := bstep (se 2 (by rfl) ⟨1342674, by rfl⟩ : syracuseStep 3580465 = 2685349) B2685349
theorem B4773953 : Blo 2063435 4773953 := bstep (se 2 (by rfl) ⟨1790232, by rfl⟩ : syracuseStep 4773953 = 3580465) B3580465
theorem B3182635 : Blo 2063435 3182635 := bstep (se 1 (by rfl) ⟨2386976, by rfl⟩ : syracuseStep 3182635 = 4773953) B4773953
theorem B4243513 : Blo 2063435 4243513 := bstep (se 2 (by rfl) ⟨1591317, by rfl⟩ : syracuseStep 4243513 = 3182635) B3182635
theorem B5658017 : Blo 2063435 5658017 := bstep (se 2 (by rfl) ⟨2121756, by rfl⟩ : syracuseStep 5658017 = 4243513) B4243513
theorem B15088045 : Blo 2063435 15088045 := bstep (se 3 (by rfl) ⟨2829008, by rfl⟩ : syracuseStep 15088045 = 5658017) B5658017
theorem B20117393 : Blo 2063435 20117393 := bstep (se 2 (by rfl) ⟨7544022, by rfl⟩ : syracuseStep 20117393 = 15088045) B15088045
theorem B13411595 : Blo 2063435 13411595 := bstep (se 1 (by rfl) ⟨10058696, by rfl⟩ : syracuseStep 13411595 = 20117393) B20117393
theorem B35764253 : Blo 2063435 35764253 := bstep (se 3 (by rfl) ⟨6705797, by rfl⟩ : syracuseStep 35764253 = 13411595) B13411595
theorem B23842835 : Blo 2063435 23842835 := bstep (se 1 (by rfl) ⟨17882126, by rfl⟩ : syracuseStep 23842835 = 35764253) B35764253
theorem B15895223 : Blo 2063435 15895223 := bstep (se 1 (by rfl) ⟨11921417, by rfl⟩ : syracuseStep 15895223 = 23842835) B23842835
theorem B10596815 : Blo 2063435 10596815 := bstep (se 1 (by rfl) ⟨7947611, by rfl⟩ : syracuseStep 10596815 = 15895223) B15895223
theorem B7064543 : Blo 2063435 7064543 := bstep (se 1 (by rfl) ⟨5298407, by rfl⟩ : syracuseStep 7064543 = 10596815) B10596815
theorem B18838781 : Blo 2063435 18838781 := bstep (se 3 (by rfl) ⟨3532271, by rfl⟩ : syracuseStep 18838781 = 7064543) B7064543
theorem B12559187 : Blo 2063435 12559187 := bstep (se 1 (by rfl) ⟨9419390, by rfl⟩ : syracuseStep 12559187 = 18838781) B18838781
theorem B8372791 : Blo 2063435 8372791 := bstep (se 1 (by rfl) ⟨6279593, by rfl⟩ : syracuseStep 8372791 = 12559187) B12559187
theorem B44654885 : Blo 2063435 44654885 := bstep (se 4 (by rfl) ⟨4186395, by rfl⟩ : syracuseStep 44654885 = 8372791) B8372791
theorem B29769923 : Blo 2063435 29769923 := bstep (se 1 (by rfl) ⟨22327442, by rfl⟩ : syracuseStep 29769923 = 44654885) B44654885
theorem B19846615 : Blo 2063435 19846615 := bstep (se 1 (by rfl) ⟨14884961, by rfl⟩ : syracuseStep 19846615 = 29769923) B29769923
theorem B26462153 : Blo 2063435 26462153 := bstep (se 2 (by rfl) ⟨9923307, by rfl⟩ : syracuseStep 26462153 = 19846615) B19846615
theorem B17641435 : Blo 2063435 17641435 := bstep (se 1 (by rfl) ⟨13231076, by rfl⟩ : syracuseStep 17641435 = 26462153) B26462153
theorem B23521913 : Blo 2063435 23521913 := bstep (se 2 (by rfl) ⟨8820717, by rfl⟩ : syracuseStep 23521913 = 17641435) B17641435
theorem B15681275 : Blo 2063435 15681275 := bstep (se 1 (by rfl) ⟨11760956, by rfl⟩ : syracuseStep 15681275 = 23521913) B23521913
theorem B10454183 : Blo 2063435 10454183 := bstep (se 1 (by rfl) ⟨7840637, by rfl⟩ : syracuseStep 10454183 = 15681275) B15681275
theorem B6969455 : Blo 2063435 6969455 := bstep (se 1 (by rfl) ⟨5227091, by rfl⟩ : syracuseStep 6969455 = 10454183) B10454183
theorem B4646303 : Blo 2063435 4646303 := bstep (se 1 (by rfl) ⟨3484727, by rfl⟩ : syracuseStep 4646303 = 6969455) B6969455
theorem B3097535 : Blo 2063435 3097535 := bstep (se 1 (by rfl) ⟨2323151, by rfl⟩ : syracuseStep 3097535 = 4646303) B4646303
theorem B2065023 : Blo 2063435 2065023 := bstep (se 1 (by rfl) ⟨1548767, by rfl⟩ : syracuseStep 2065023 = 3097535) B3097535
theorem B3097541 : Blo 2063435 3097541 := bbase (se 4 (by rfl) ⟨290394, by rfl⟩ : syracuseStep 3097541 = 580789) (by norm_num)
theorem B2065027 : Blo 2063435 2065027 := bstep (se 1 (by rfl) ⟨1548770, by rfl⟩ : syracuseStep 2065027 = 3097541) B3097541
theorem B3484741 : Blo 2063435 3484741 := bbase (se 4 (by rfl) ⟨326694, by rfl⟩ : syracuseStep 3484741 = 653389) (by norm_num)
theorem B4646321 : Blo 2063435 4646321 := bstep (se 2 (by rfl) ⟨1742370, by rfl⟩ : syracuseStep 4646321 = 3484741) B3484741
theorem B3097547 : Blo 2063435 3097547 := bstep (se 1 (by rfl) ⟨2323160, by rfl⟩ : syracuseStep 3097547 = 4646321) B4646321
theorem B2065031 : Blo 2063435 2065031 := bstep (se 1 (by rfl) ⟨1548773, by rfl⟩ : syracuseStep 2065031 = 3097547) B3097547
theorem B2323165 : Blo 2063435 2323165 := bbase (se 3 (by rfl) ⟨435593, by rfl⟩ : syracuseStep 2323165 = 871187) (by norm_num)
theorem B3097553 : Blo 2063435 3097553 := bstep (se 2 (by rfl) ⟨1161582, by rfl⟩ : syracuseStep 3097553 = 2323165) B2323165
theorem B2065035 : Blo 2063435 2065035 := bstep (se 1 (by rfl) ⟨1548776, by rfl⟩ : syracuseStep 2065035 = 3097553) B3097553
theorem B6969509 : Blo 2063435 6969509 := bbase (se 4 (by rfl) ⟨653391, by rfl⟩ : syracuseStep 6969509 = 1306783) (by norm_num)
theorem B4646339 : Blo 2063435 4646339 := bstep (se 1 (by rfl) ⟨3484754, by rfl⟩ : syracuseStep 4646339 = 6969509) B6969509
theorem B3097559 : Blo 2063435 3097559 := bstep (se 1 (by rfl) ⟨2323169, by rfl⟩ : syracuseStep 3097559 = 4646339) B4646339
theorem B2065039 : Blo 2063435 2065039 := bstep (se 1 (by rfl) ⟨1548779, by rfl⟩ : syracuseStep 2065039 = 3097559) B3097559
theorem B3097565 : Blo 2063435 3097565 := bbase (se 3 (by rfl) ⟨580793, by rfl⟩ : syracuseStep 3097565 = 1161587) (by norm_num)
theorem B2065043 : Blo 2063435 2065043 := bstep (se 1 (by rfl) ⟨1548782, by rfl⟩ : syracuseStep 2065043 = 3097565) B3097565
theorem B4646357 : Blo 2063435 4646357 := bbase (se 7 (by rfl) ⟨54449, by rfl⟩ : syracuseStep 4646357 = 108899) (by norm_num)
theorem B3097571 : Blo 2063435 3097571 := bstep (se 1 (by rfl) ⟨2323178, by rfl⟩ : syracuseStep 3097571 = 4646357) B4646357
theorem B2065047 : Blo 2063435 2065047 := bstep (se 1 (by rfl) ⟨1548785, by rfl⟩ : syracuseStep 2065047 = 3097571) B3097571
theorem B2514709 : Blo 2063435 2514709 := bbase (se 6 (by rfl) ⟨58938, by rfl⟩ : syracuseStep 2514709 = 117877) (by norm_num)
theorem B3352945 : Blo 2063435 3352945 := bstep (se 2 (by rfl) ⟨1257354, by rfl⟩ : syracuseStep 3352945 = 2514709) B2514709
theorem B4470593 : Blo 2063435 4470593 := bstep (se 2 (by rfl) ⟨1676472, by rfl⟩ : syracuseStep 4470593 = 3352945) B3352945
theorem B11921581 : Blo 2063435 11921581 := bstep (se 3 (by rfl) ⟨2235296, by rfl⟩ : syracuseStep 11921581 = 4470593) B4470593
theorem B15895441 : Blo 2063435 15895441 := bstep (se 2 (by rfl) ⟨5960790, by rfl⟩ : syracuseStep 15895441 = 11921581) B11921581
theorem B21193921 : Blo 2063435 21193921 := bstep (se 2 (by rfl) ⟨7947720, by rfl⟩ : syracuseStep 21193921 = 15895441) B15895441
theorem B28258561 : Blo 2063435 28258561 := bstep (se 2 (by rfl) ⟨10596960, by rfl⟩ : syracuseStep 28258561 = 21193921) B21193921
theorem B37678081 : Blo 2063435 37678081 := bstep (se 2 (by rfl) ⟨14129280, by rfl⟩ : syracuseStep 37678081 = 28258561) B28258561
theorem B50237441 : Blo 2063435 50237441 := bstep (se 2 (by rfl) ⟨18839040, by rfl⟩ : syracuseStep 50237441 = 37678081) B37678081
theorem B33491627 : Blo 2063435 33491627 := bstep (se 1 (by rfl) ⟨25118720, by rfl⟩ : syracuseStep 33491627 = 50237441) B50237441
theorem B22327751 : Blo 2063435 22327751 := bstep (se 1 (by rfl) ⟨16745813, by rfl⟩ : syracuseStep 22327751 = 33491627) B33491627
theorem B14885167 : Blo 2063435 14885167 := bstep (se 1 (by rfl) ⟨11163875, by rfl⟩ : syracuseStep 14885167 = 22327751) B22327751
theorem B19846889 : Blo 2063435 19846889 := bstep (se 2 (by rfl) ⟨7442583, by rfl⟩ : syracuseStep 19846889 = 14885167) B14885167
theorem B13231259 : Blo 2063435 13231259 := bstep (se 1 (by rfl) ⟨9923444, by rfl⟩ : syracuseStep 13231259 = 19846889) B19846889
theorem B8820839 : Blo 2063435 8820839 := bstep (se 1 (by rfl) ⟨6615629, by rfl⟩ : syracuseStep 8820839 = 13231259) B13231259
theorem B5880559 : Blo 2063435 5880559 := bstep (se 1 (by rfl) ⟨4410419, by rfl⟩ : syracuseStep 5880559 = 8820839) B8820839
theorem B7840745 : Blo 2063435 7840745 := bstep (se 2 (by rfl) ⟨2940279, by rfl⟩ : syracuseStep 7840745 = 5880559) B5880559
theorem B5227163 : Blo 2063435 5227163 := bstep (se 1 (by rfl) ⟨3920372, by rfl⟩ : syracuseStep 5227163 = 7840745) B7840745
theorem B3484775 : Blo 2063435 3484775 := bstep (se 1 (by rfl) ⟨2613581, by rfl⟩ : syracuseStep 3484775 = 5227163) B5227163
theorem B2323183 : Blo 2063435 2323183 := bstep (se 1 (by rfl) ⟨1742387, by rfl⟩ : syracuseStep 2323183 = 3484775) B3484775
theorem B3097577 : Blo 2063435 3097577 := bstep (se 2 (by rfl) ⟨1161591, by rfl⟩ : syracuseStep 3097577 = 2323183) B2323183
theorem B2065051 : Blo 2063435 2065051 := bstep (se 1 (by rfl) ⟨1548788, by rfl⟩ : syracuseStep 2065051 = 3097577) B3097577
theorem B7442597 : Blo 2063435 7442597 := bbase (se 4 (by rfl) ⟨697743, by rfl⟩ : syracuseStep 7442597 = 1395487) (by norm_num)
theorem B4961731 : Blo 2063435 4961731 := bstep (se 1 (by rfl) ⟨3721298, by rfl⟩ : syracuseStep 4961731 = 7442597) B7442597
theorem B6615641 : Blo 2063435 6615641 := bstep (se 2 (by rfl) ⟨2480865, by rfl⟩ : syracuseStep 6615641 = 4961731) B4961731
theorem B17641709 : Blo 2063435 17641709 := bstep (se 3 (by rfl) ⟨3307820, by rfl⟩ : syracuseStep 17641709 = 6615641) B6615641
theorem B11761139 : Blo 2063435 11761139 := bstep (se 1 (by rfl) ⟨8820854, by rfl⟩ : syracuseStep 11761139 = 17641709) B17641709
theorem B7840759 : Blo 2063435 7840759 := bstep (se 1 (by rfl) ⟨5880569, by rfl⟩ : syracuseStep 7840759 = 11761139) B11761139
theorem B10454345 : Blo 2063435 10454345 := bstep (se 2 (by rfl) ⟨3920379, by rfl⟩ : syracuseStep 10454345 = 7840759) B7840759
theorem B6969563 : Blo 2063435 6969563 := bstep (se 1 (by rfl) ⟨5227172, by rfl⟩ : syracuseStep 6969563 = 10454345) B10454345
theorem B4646375 : Blo 2063435 4646375 := bstep (se 1 (by rfl) ⟨3484781, by rfl⟩ : syracuseStep 4646375 = 6969563) B6969563
theorem B3097583 : Blo 2063435 3097583 := bstep (se 1 (by rfl) ⟨2323187, by rfl⟩ : syracuseStep 3097583 = 4646375) B4646375
theorem B2065055 : Blo 2063435 2065055 := bstep (se 1 (by rfl) ⟨1548791, by rfl⟩ : syracuseStep 2065055 = 3097583) B3097583
theorem B3097589 : Blo 2063435 3097589 := bbase (se 5 (by rfl) ⟨145199, by rfl⟩ : syracuseStep 3097589 = 290399) (by norm_num)
theorem B2065059 : Blo 2063435 2065059 := bstep (se 1 (by rfl) ⟨1548794, by rfl⟩ : syracuseStep 2065059 = 3097589) B3097589
theorem B4410445 : Blo 2063435 4410445 := bbase (se 3 (by rfl) ⟨826958, by rfl⟩ : syracuseStep 4410445 = 1653917) (by norm_num)
theorem B5880593 : Blo 2063435 5880593 := bstep (se 2 (by rfl) ⟨2205222, by rfl⟩ : syracuseStep 5880593 = 4410445) B4410445
theorem B3920395 : Blo 2063435 3920395 := bstep (se 1 (by rfl) ⟨2940296, by rfl⟩ : syracuseStep 3920395 = 5880593) B5880593
theorem B5227193 : Blo 2063435 5227193 := bstep (se 2 (by rfl) ⟨1960197, by rfl⟩ : syracuseStep 5227193 = 3920395) B3920395
theorem B3484795 : Blo 2063435 3484795 := bstep (se 1 (by rfl) ⟨2613596, by rfl⟩ : syracuseStep 3484795 = 5227193) B5227193
theorem B4646393 : Blo 2063435 4646393 := bstep (se 2 (by rfl) ⟨1742397, by rfl⟩ : syracuseStep 4646393 = 3484795) B3484795
theorem B3097595 : Blo 2063435 3097595 := bstep (se 1 (by rfl) ⟨2323196, by rfl⟩ : syracuseStep 3097595 = 4646393) B4646393
theorem B2065063 : Blo 2063435 2065063 := bstep (se 1 (by rfl) ⟨1548797, by rfl⟩ : syracuseStep 2065063 = 3097595) B3097595
theorem B2323201 : Blo 2063435 2323201 := bbase (se 2 (by rfl) ⟨871200, by rfl⟩ : syracuseStep 2323201 = 1742401) (by norm_num)
theorem B3097601 : Blo 2063435 3097601 := bstep (se 2 (by rfl) ⟨1161600, by rfl⟩ : syracuseStep 3097601 = 2323201) B2323201
theorem B2065067 : Blo 2063435 2065067 := bstep (se 1 (by rfl) ⟨1548800, by rfl⟩ : syracuseStep 2065067 = 3097601) B3097601
theorem B5227213 : Blo 2063435 5227213 := bbase (se 3 (by rfl) ⟨980102, by rfl⟩ : syracuseStep 5227213 = 1960205) (by norm_num)
theorem B6969617 : Blo 2063435 6969617 := bstep (se 2 (by rfl) ⟨2613606, by rfl⟩ : syracuseStep 6969617 = 5227213) B5227213
theorem B4646411 : Blo 2063435 4646411 := bstep (se 1 (by rfl) ⟨3484808, by rfl⟩ : syracuseStep 4646411 = 6969617) B6969617
theorem B3097607 : Blo 2063435 3097607 := bstep (se 1 (by rfl) ⟨2323205, by rfl⟩ : syracuseStep 3097607 = 4646411) B4646411
theorem B2065071 : Blo 2063435 2065071 := bstep (se 1 (by rfl) ⟨1548803, by rfl⟩ : syracuseStep 2065071 = 3097607) B3097607
theorem B3097613 : Blo 2063435 3097613 := bbase (se 3 (by rfl) ⟨580802, by rfl⟩ : syracuseStep 3097613 = 1161605) (by norm_num)
theorem B2065075 : Blo 2063435 2065075 := bstep (se 1 (by rfl) ⟨1548806, by rfl⟩ : syracuseStep 2065075 = 3097613) B3097613
theorem B4646429 : Blo 2063435 4646429 := bbase (se 3 (by rfl) ⟨871205, by rfl⟩ : syracuseStep 4646429 = 1742411) (by norm_num)
theorem B3097619 : Blo 2063435 3097619 := bstep (se 1 (by rfl) ⟨2323214, by rfl⟩ : syracuseStep 3097619 = 4646429) B4646429
theorem B2065079 : Blo 2063435 2065079 := bstep (se 1 (by rfl) ⟨1548809, by rfl⟩ : syracuseStep 2065079 = 3097619) B3097619
theorem B3484829 : Blo 2063435 3484829 := bbase (se 3 (by rfl) ⟨653405, by rfl⟩ : syracuseStep 3484829 = 1306811) (by norm_num)
theorem B2323219 : Blo 2063435 2323219 := bstep (se 1 (by rfl) ⟨1742414, by rfl⟩ : syracuseStep 2323219 = 3484829) B3484829
theorem B3097625 : Blo 2063435 3097625 := bstep (se 2 (by rfl) ⟨1161609, by rfl⟩ : syracuseStep 3097625 = 2323219) B2323219
theorem B2065083 : Blo 2063435 2065083 := bstep (se 1 (by rfl) ⟨1548812, by rfl⟩ : syracuseStep 2065083 = 3097625) B3097625
theorem B3226157 : Blo 2063435 3226157 := bbase (se 3 (by rfl) ⟨604904, by rfl⟩ : syracuseStep 3226157 = 1209809) (by norm_num)
theorem B2150771 : Blo 2063435 2150771 := bstep (se 1 (by rfl) ⟨1613078, by rfl⟩ : syracuseStep 2150771 = 3226157) B3226157
theorem B5735389 : Blo 2063435 5735389 := bstep (se 3 (by rfl) ⟨1075385, by rfl⟩ : syracuseStep 5735389 = 2150771) B2150771
theorem B7647185 : Blo 2063435 7647185 := bstep (se 2 (by rfl) ⟨2867694, by rfl⟩ : syracuseStep 7647185 = 5735389) B5735389
theorem B5098123 : Blo 2063435 5098123 := bstep (se 1 (by rfl) ⟨3823592, by rfl⟩ : syracuseStep 5098123 = 7647185) B7647185
theorem B27189989 : Blo 2063435 27189989 := bstep (se 4 (by rfl) ⟨2549061, by rfl⟩ : syracuseStep 27189989 = 5098123) B5098123
theorem B18126659 : Blo 2063435 18126659 := bstep (se 1 (by rfl) ⟨13594994, by rfl⟩ : syracuseStep 18126659 = 27189989) B27189989
theorem B12084439 : Blo 2063435 12084439 := bstep (se 1 (by rfl) ⟨9063329, by rfl⟩ : syracuseStep 12084439 = 18126659) B18126659
theorem B16112585 : Blo 2063435 16112585 := bstep (se 2 (by rfl) ⟨6042219, by rfl⟩ : syracuseStep 16112585 = 12084439) B12084439
theorem B10741723 : Blo 2063435 10741723 := bstep (se 1 (by rfl) ⟨8056292, by rfl⟩ : syracuseStep 10741723 = 16112585) B16112585
theorem B57289189 : Blo 2063435 57289189 := bstep (se 4 (by rfl) ⟨5370861, by rfl⟩ : syracuseStep 57289189 = 10741723) B10741723
theorem B76385585 : Blo 2063435 76385585 := bstep (se 2 (by rfl) ⟨28644594, by rfl⟩ : syracuseStep 76385585 = 57289189) B57289189
theorem B50923723 : Blo 2063435 50923723 := bstep (se 1 (by rfl) ⟨38192792, by rfl⟩ : syracuseStep 50923723 = 76385585) B76385585
theorem B67898297 : Blo 2063435 67898297 := bstep (se 2 (by rfl) ⟨25461861, by rfl⟩ : syracuseStep 67898297 = 50923723) B50923723
theorem B181062125 : Blo 2063435 181062125 := bstep (se 3 (by rfl) ⟨33949148, by rfl⟩ : syracuseStep 181062125 = 67898297) B67898297
theorem B120708083 : Blo 2063435 120708083 := bstep (se 1 (by rfl) ⟨90531062, by rfl⟩ : syracuseStep 120708083 = 181062125) B181062125
theorem B80472055 : Blo 2063435 80472055 := bstep (se 1 (by rfl) ⟨60354041, by rfl⟩ : syracuseStep 80472055 = 120708083) B120708083
theorem B107296073 : Blo 2063435 107296073 := bstep (se 2 (by rfl) ⟨40236027, by rfl⟩ : syracuseStep 107296073 = 80472055) B80472055
theorem B71530715 : Blo 2063435 71530715 := bstep (se 1 (by rfl) ⟨53648036, by rfl⟩ : syracuseStep 71530715 = 107296073) B107296073
theorem B47687143 : Blo 2063435 47687143 := bstep (se 1 (by rfl) ⟨35765357, by rfl⟩ : syracuseStep 47687143 = 71530715) B71530715
theorem B63582857 : Blo 2063435 63582857 := bstep (se 2 (by rfl) ⟨23843571, by rfl⟩ : syracuseStep 63582857 = 47687143) B47687143
theorem B42388571 : Blo 2063435 42388571 := bstep (se 1 (by rfl) ⟨31791428, by rfl⟩ : syracuseStep 42388571 = 63582857) B63582857
theorem B28259047 : Blo 2063435 28259047 := bstep (se 1 (by rfl) ⟨21194285, by rfl⟩ : syracuseStep 28259047 = 42388571) B42388571
theorem B150714917 : Blo 2063435 150714917 := bstep (se 4 (by rfl) ⟨14129523, by rfl⟩ : syracuseStep 150714917 = 28259047) B28259047
theorem B100476611 : Blo 2063435 100476611 := bstep (se 1 (by rfl) ⟨75357458, by rfl⟩ : syracuseStep 100476611 = 150714917) B150714917
theorem B66984407 : Blo 2063435 66984407 := bstep (se 1 (by rfl) ⟨50238305, by rfl⟩ : syracuseStep 66984407 = 100476611) B100476611
theorem B44656271 : Blo 2063435 44656271 := bstep (se 1 (by rfl) ⟨33492203, by rfl⟩ : syracuseStep 44656271 = 66984407) B66984407
theorem B29770847 : Blo 2063435 29770847 := bstep (se 1 (by rfl) ⟨22328135, by rfl⟩ : syracuseStep 29770847 = 44656271) B44656271
theorem B19847231 : Blo 2063435 19847231 := bstep (se 1 (by rfl) ⟨14885423, by rfl⟩ : syracuseStep 19847231 = 29770847) B29770847
theorem B13231487 : Blo 2063435 13231487 := bstep (se 1 (by rfl) ⟨9923615, by rfl⟩ : syracuseStep 13231487 = 19847231) B19847231
theorem B8820991 : Blo 2063435 8820991 := bstep (se 1 (by rfl) ⟨6615743, by rfl⟩ : syracuseStep 8820991 = 13231487) B13231487
theorem B11761321 : Blo 2063435 11761321 := bstep (se 2 (by rfl) ⟨4410495, by rfl⟩ : syracuseStep 11761321 = 8820991) B8820991
theorem B15681761 : Blo 2063435 15681761 := bstep (se 2 (by rfl) ⟨5880660, by rfl⟩ : syracuseStep 15681761 = 11761321) B11761321
theorem B10454507 : Blo 2063435 10454507 := bstep (se 1 (by rfl) ⟨7840880, by rfl⟩ : syracuseStep 10454507 = 15681761) B15681761
theorem B6969671 : Blo 2063435 6969671 := bstep (se 1 (by rfl) ⟨5227253, by rfl⟩ : syracuseStep 6969671 = 10454507) B10454507
theorem B4646447 : Blo 2063435 4646447 := bstep (se 1 (by rfl) ⟨3484835, by rfl⟩ : syracuseStep 4646447 = 6969671) B6969671
theorem B3097631 : Blo 2063435 3097631 := bstep (se 1 (by rfl) ⟨2323223, by rfl⟩ : syracuseStep 3097631 = 4646447) B4646447
theorem B2065087 : Blo 2063435 2065087 := bstep (se 1 (by rfl) ⟨1548815, by rfl⟩ : syracuseStep 2065087 = 3097631) B3097631
theorem B3097637 : Blo 2063435 3097637 := bbase (se 4 (by rfl) ⟨290403, by rfl⟩ : syracuseStep 3097637 = 580807) (by norm_num)
theorem B2065091 : Blo 2063435 2065091 := bstep (se 1 (by rfl) ⟨1548818, by rfl⟩ : syracuseStep 2065091 = 3097637) B3097637
theorem B2613637 : Blo 2063435 2613637 := bbase (se 4 (by rfl) ⟨245028, by rfl⟩ : syracuseStep 2613637 = 490057) (by norm_num)
theorem B3484849 : Blo 2063435 3484849 := bstep (se 2 (by rfl) ⟨1306818, by rfl⟩ : syracuseStep 3484849 = 2613637) B2613637
theorem B4646465 : Blo 2063435 4646465 := bstep (se 2 (by rfl) ⟨1742424, by rfl⟩ : syracuseStep 4646465 = 3484849) B3484849
theorem B3097643 : Blo 2063435 3097643 := bstep (se 1 (by rfl) ⟨2323232, by rfl⟩ : syracuseStep 3097643 = 4646465) B4646465
theorem B2065095 : Blo 2063435 2065095 := bstep (se 1 (by rfl) ⟨1548821, by rfl⟩ : syracuseStep 2065095 = 3097643) B3097643
theorem B2323237 : Blo 2063435 2323237 := bbase (se 4 (by rfl) ⟨217803, by rfl⟩ : syracuseStep 2323237 = 435607) (by norm_num)
theorem B3097649 : Blo 2063435 3097649 := bstep (se 2 (by rfl) ⟨1161618, by rfl⟩ : syracuseStep 3097649 = 2323237) B2323237
theorem B2065099 : Blo 2063435 2065099 := bstep (se 1 (by rfl) ⟨1548824, by rfl⟩ : syracuseStep 2065099 = 3097649) B3097649
theorem B8821061 : Blo 2063435 8821061 := bbase (se 4 (by rfl) ⟨826974, by rfl⟩ : syracuseStep 8821061 = 1653949) (by norm_num)
theorem B5880707 : Blo 2063435 5880707 := bstep (se 1 (by rfl) ⟨4410530, by rfl⟩ : syracuseStep 5880707 = 8821061) B8821061
theorem B3920471 : Blo 2063435 3920471 := bstep (se 1 (by rfl) ⟨2940353, by rfl⟩ : syracuseStep 3920471 = 5880707) B5880707
theorem B2613647 : Blo 2063435 2613647 := bstep (se 1 (by rfl) ⟨1960235, by rfl⟩ : syracuseStep 2613647 = 3920471) B3920471
theorem B6969725 : Blo 2063435 6969725 := bstep (se 3 (by rfl) ⟨1306823, by rfl⟩ : syracuseStep 6969725 = 2613647) B2613647
theorem B4646483 : Blo 2063435 4646483 := bstep (se 1 (by rfl) ⟨3484862, by rfl⟩ : syracuseStep 4646483 = 6969725) B6969725
theorem B3097655 : Blo 2063435 3097655 := bstep (se 1 (by rfl) ⟨2323241, by rfl⟩ : syracuseStep 3097655 = 4646483) B4646483
theorem B2065103 : Blo 2063435 2065103 := bstep (se 1 (by rfl) ⟨1548827, by rfl⟩ : syracuseStep 2065103 = 3097655) B3097655
theorem B3097661 : Blo 2063435 3097661 := bbase (se 3 (by rfl) ⟨580811, by rfl⟩ : syracuseStep 3097661 = 1161623) (by norm_num)
theorem B2065107 : Blo 2063435 2065107 := bstep (se 1 (by rfl) ⟨1548830, by rfl⟩ : syracuseStep 2065107 = 3097661) B3097661
theorem B4646501 : Blo 2063435 4646501 := bbase (se 4 (by rfl) ⟨435609, by rfl⟩ : syracuseStep 4646501 = 871219) (by norm_num)
theorem B3097667 : Blo 2063435 3097667 := bstep (se 1 (by rfl) ⟨2323250, by rfl⟩ : syracuseStep 3097667 = 4646501) B4646501
theorem B2065111 : Blo 2063435 2065111 := bstep (se 1 (by rfl) ⟨1548833, by rfl⟩ : syracuseStep 2065111 = 3097667) B3097667
theorem B5227325 : Blo 2063435 5227325 := bbase (se 3 (by rfl) ⟨980123, by rfl⟩ : syracuseStep 5227325 = 1960247) (by norm_num)
theorem B3484883 : Blo 2063435 3484883 := bstep (se 1 (by rfl) ⟨2613662, by rfl⟩ : syracuseStep 3484883 = 5227325) B5227325
theorem B2323255 : Blo 2063435 2323255 := bstep (se 1 (by rfl) ⟨1742441, by rfl⟩ : syracuseStep 2323255 = 3484883) B3484883
theorem B3097673 : Blo 2063435 3097673 := bstep (se 2 (by rfl) ⟨1161627, by rfl⟩ : syracuseStep 3097673 = 2323255) B2323255
theorem B2065115 : Blo 2063435 2065115 := bstep (se 1 (by rfl) ⟨1548836, by rfl⟩ : syracuseStep 2065115 = 3097673) B3097673
theorem B3920501 : Blo 2063435 3920501 := bbase (se 5 (by rfl) ⟨183773, by rfl⟩ : syracuseStep 3920501 = 367547) (by norm_num)
theorem B10454669 : Blo 2063435 10454669 := bstep (se 3 (by rfl) ⟨1960250, by rfl⟩ : syracuseStep 10454669 = 3920501) B3920501
theorem B6969779 : Blo 2063435 6969779 := bstep (se 1 (by rfl) ⟨5227334, by rfl⟩ : syracuseStep 6969779 = 10454669) B10454669
theorem B4646519 : Blo 2063435 4646519 := bstep (se 1 (by rfl) ⟨3484889, by rfl⟩ : syracuseStep 4646519 = 6969779) B6969779
theorem B3097679 : Blo 2063435 3097679 := bstep (se 1 (by rfl) ⟨2323259, by rfl⟩ : syracuseStep 3097679 = 4646519) B4646519
theorem B2065119 : Blo 2063435 2065119 := bstep (se 1 (by rfl) ⟨1548839, by rfl⟩ : syracuseStep 2065119 = 3097679) B3097679
theorem B3097685 : Blo 2063435 3097685 := bbase (se 8 (by rfl) ⟨18150, by rfl⟩ : syracuseStep 3097685 = 36301) (by norm_num)
theorem B2065123 : Blo 2063435 2065123 := bstep (se 1 (by rfl) ⟨1548842, by rfl⟩ : syracuseStep 2065123 = 3097685) B3097685
theorem B40236821 : Blo 2063435 40236821 := bbase (se 6 (by rfl) ⟨943050, by rfl⟩ : syracuseStep 40236821 = 1886101) (by norm_num)
theorem B26824547 : Blo 2063435 26824547 := bstep (se 1 (by rfl) ⟨20118410, by rfl⟩ : syracuseStep 26824547 = 40236821) B40236821
theorem B17883031 : Blo 2063435 17883031 := bstep (se 1 (by rfl) ⟨13412273, by rfl⟩ : syracuseStep 17883031 = 26824547) B26824547
theorem B23844041 : Blo 2063435 23844041 := bstep (se 2 (by rfl) ⟨8941515, by rfl⟩ : syracuseStep 23844041 = 17883031) B17883031
theorem B15896027 : Blo 2063435 15896027 := bstep (se 1 (by rfl) ⟨11922020, by rfl⟩ : syracuseStep 15896027 = 23844041) B23844041
theorem B42389405 : Blo 2063435 42389405 := bstep (se 3 (by rfl) ⟨7948013, by rfl⟩ : syracuseStep 42389405 = 15896027) B15896027
theorem B28259603 : Blo 2063435 28259603 := bstep (se 1 (by rfl) ⟨21194702, by rfl⟩ : syracuseStep 28259603 = 42389405) B42389405
theorem B18839735 : Blo 2063435 18839735 := bstep (se 1 (by rfl) ⟨14129801, by rfl⟩ : syracuseStep 18839735 = 28259603) B28259603
theorem B12559823 : Blo 2063435 12559823 := bstep (se 1 (by rfl) ⟨9419867, by rfl⟩ : syracuseStep 12559823 = 18839735) B18839735
theorem B8373215 : Blo 2063435 8373215 := bstep (se 1 (by rfl) ⟨6279911, by rfl⟩ : syracuseStep 8373215 = 12559823) B12559823
theorem B5582143 : Blo 2063435 5582143 := bstep (se 1 (by rfl) ⟨4186607, by rfl⟩ : syracuseStep 5582143 = 8373215) B8373215
theorem B7442857 : Blo 2063435 7442857 := bstep (se 2 (by rfl) ⟨2791071, by rfl⟩ : syracuseStep 7442857 = 5582143) B5582143
theorem B9923809 : Blo 2063435 9923809 := bstep (se 2 (by rfl) ⟨3721428, by rfl⟩ : syracuseStep 9923809 = 7442857) B7442857
theorem B13231745 : Blo 2063435 13231745 := bstep (se 2 (by rfl) ⟨4961904, by rfl⟩ : syracuseStep 13231745 = 9923809) B9923809
theorem B8821163 : Blo 2063435 8821163 := bstep (se 1 (by rfl) ⟨6615872, by rfl⟩ : syracuseStep 8821163 = 13231745) B13231745
theorem B5880775 : Blo 2063435 5880775 := bstep (se 1 (by rfl) ⟨4410581, by rfl⟩ : syracuseStep 5880775 = 8821163) B8821163
theorem B7841033 : Blo 2063435 7841033 := bstep (se 2 (by rfl) ⟨2940387, by rfl⟩ : syracuseStep 7841033 = 5880775) B5880775
theorem B5227355 : Blo 2063435 5227355 := bstep (se 1 (by rfl) ⟨3920516, by rfl⟩ : syracuseStep 5227355 = 7841033) B7841033
theorem B3484903 : Blo 2063435 3484903 := bstep (se 1 (by rfl) ⟨2613677, by rfl⟩ : syracuseStep 3484903 = 5227355) B5227355
theorem B4646537 : Blo 2063435 4646537 := bstep (se 2 (by rfl) ⟨1742451, by rfl⟩ : syracuseStep 4646537 = 3484903) B3484903
theorem B3097691 : Blo 2063435 3097691 := bstep (se 1 (by rfl) ⟨2323268, by rfl⟩ : syracuseStep 3097691 = 4646537) B4646537
theorem B2065127 : Blo 2063435 2065127 := bstep (se 1 (by rfl) ⟨1548845, by rfl⟩ : syracuseStep 2065127 = 3097691) B3097691
theorem B2323273 : Blo 2063435 2323273 := bbase (se 2 (by rfl) ⟨871227, by rfl⟩ : syracuseStep 2323273 = 1742455) (by norm_num)
theorem B3097697 : Blo 2063435 3097697 := bstep (se 2 (by rfl) ⟨1161636, by rfl⟩ : syracuseStep 3097697 = 2323273) B2323273
theorem B2065131 : Blo 2063435 2065131 := bstep (se 1 (by rfl) ⟨1548848, by rfl⟩ : syracuseStep 2065131 = 3097697) B3097697
theorem B7442885 : Blo 2063435 7442885 := bbase (se 4 (by rfl) ⟨697770, by rfl⟩ : syracuseStep 7442885 = 1395541) (by norm_num)
theorem B19847693 : Blo 2063435 19847693 := bstep (se 3 (by rfl) ⟨3721442, by rfl⟩ : syracuseStep 19847693 = 7442885) B7442885
theorem B13231795 : Blo 2063435 13231795 := bstep (se 1 (by rfl) ⟨9923846, by rfl⟩ : syracuseStep 13231795 = 19847693) B19847693
theorem B17642393 : Blo 2063435 17642393 := bstep (se 2 (by rfl) ⟨6615897, by rfl⟩ : syracuseStep 17642393 = 13231795) B13231795
theorem B11761595 : Blo 2063435 11761595 := bstep (se 1 (by rfl) ⟨8821196, by rfl⟩ : syracuseStep 11761595 = 17642393) B17642393
theorem B7841063 : Blo 2063435 7841063 := bstep (se 1 (by rfl) ⟨5880797, by rfl⟩ : syracuseStep 7841063 = 11761595) B11761595
theorem B5227375 : Blo 2063435 5227375 := bstep (se 1 (by rfl) ⟨3920531, by rfl⟩ : syracuseStep 5227375 = 7841063) B7841063
theorem B6969833 : Blo 2063435 6969833 := bstep (se 2 (by rfl) ⟨2613687, by rfl⟩ : syracuseStep 6969833 = 5227375) B5227375
theorem B4646555 : Blo 2063435 4646555 := bstep (se 1 (by rfl) ⟨3484916, by rfl⟩ : syracuseStep 4646555 = 6969833) B6969833
theorem B3097703 : Blo 2063435 3097703 := bstep (se 1 (by rfl) ⟨2323277, by rfl⟩ : syracuseStep 3097703 = 4646555) B4646555
theorem B2065135 : Blo 2063435 2065135 := bstep (se 1 (by rfl) ⟨1548851, by rfl⟩ : syracuseStep 2065135 = 3097703) B3097703
theorem B3097709 : Blo 2063435 3097709 := bbase (se 3 (by rfl) ⟨580820, by rfl⟩ : syracuseStep 3097709 = 1161641) (by norm_num)
theorem B2065139 : Blo 2063435 2065139 := bstep (se 1 (by rfl) ⟨1548854, by rfl⟩ : syracuseStep 2065139 = 3097709) B3097709
theorem B4646573 : Blo 2063435 4646573 := bbase (se 3 (by rfl) ⟨871232, by rfl⟩ : syracuseStep 4646573 = 1742465) (by norm_num)
theorem B3097715 : Blo 2063435 3097715 := bstep (se 1 (by rfl) ⟨2323286, by rfl⟩ : syracuseStep 3097715 = 4646573) B4646573
theorem B2065143 : Blo 2063435 2065143 := bstep (se 1 (by rfl) ⟨1548857, by rfl⟩ : syracuseStep 2065143 = 3097715) B3097715
theorem B2480977 : Blo 2063435 2480977 := bbase (se 2 (by rfl) ⟨930366, by rfl⟩ : syracuseStep 2480977 = 1860733) (by norm_num)
theorem B3307969 : Blo 2063435 3307969 := bstep (se 2 (by rfl) ⟨1240488, by rfl⟩ : syracuseStep 3307969 = 2480977) B2480977
theorem B4410625 : Blo 2063435 4410625 := bstep (se 2 (by rfl) ⟨1653984, by rfl⟩ : syracuseStep 4410625 = 3307969) B3307969
theorem B5880833 : Blo 2063435 5880833 := bstep (se 2 (by rfl) ⟨2205312, by rfl⟩ : syracuseStep 5880833 = 4410625) B4410625
theorem B3920555 : Blo 2063435 3920555 := bstep (se 1 (by rfl) ⟨2940416, by rfl⟩ : syracuseStep 3920555 = 5880833) B5880833
theorem B2613703 : Blo 2063435 2613703 := bstep (se 1 (by rfl) ⟨1960277, by rfl⟩ : syracuseStep 2613703 = 3920555) B3920555
theorem B3484937 : Blo 2063435 3484937 := bstep (se 2 (by rfl) ⟨1306851, by rfl⟩ : syracuseStep 3484937 = 2613703) B2613703
theorem B2323291 : Blo 2063435 2323291 := bstep (se 1 (by rfl) ⟨1742468, by rfl⟩ : syracuseStep 2323291 = 3484937) B3484937
theorem B3097721 : Blo 2063435 3097721 := bstep (se 2 (by rfl) ⟨1161645, by rfl⟩ : syracuseStep 3097721 = 2323291) B2323291
theorem B2065147 : Blo 2063435 2065147 := bstep (se 1 (by rfl) ⟨1548860, by rfl⟩ : syracuseStep 2065147 = 3097721) B3097721
theorem B5029661 : Blo 2063435 5029661 := bbase (se 3 (by rfl) ⟨943061, by rfl⟩ : syracuseStep 5029661 = 1886123) (by norm_num)
theorem B3353107 : Blo 2063435 3353107 := bstep (se 1 (by rfl) ⟨2514830, by rfl⟩ : syracuseStep 3353107 = 5029661) B5029661
theorem B4470809 : Blo 2063435 4470809 := bstep (se 2 (by rfl) ⟨1676553, by rfl⟩ : syracuseStep 4470809 = 3353107) B3353107
theorem B11922157 : Blo 2063435 11922157 := bstep (se 3 (by rfl) ⟨2235404, by rfl⟩ : syracuseStep 11922157 = 4470809) B4470809
theorem B63584837 : Blo 2063435 63584837 := bstep (se 4 (by rfl) ⟨5961078, by rfl⟩ : syracuseStep 63584837 = 11922157) B11922157
theorem B42389891 : Blo 2063435 42389891 := bstep (se 1 (by rfl) ⟨31792418, by rfl⟩ : syracuseStep 42389891 = 63584837) B63584837
theorem B28259927 : Blo 2063435 28259927 := bstep (se 1 (by rfl) ⟨21194945, by rfl⟩ : syracuseStep 28259927 = 42389891) B42389891
theorem B18839951 : Blo 2063435 18839951 := bstep (se 1 (by rfl) ⟨14129963, by rfl⟩ : syracuseStep 18839951 = 28259927) B28259927
theorem B12559967 : Blo 2063435 12559967 := bstep (se 1 (by rfl) ⟨9419975, by rfl⟩ : syracuseStep 12559967 = 18839951) B18839951
theorem B8373311 : Blo 2063435 8373311 := bstep (se 1 (by rfl) ⟨6279983, by rfl⟩ : syracuseStep 8373311 = 12559967) B12559967
theorem B5582207 : Blo 2063435 5582207 := bstep (se 1 (by rfl) ⟨4186655, by rfl⟩ : syracuseStep 5582207 = 8373311) B8373311
theorem B3721471 : Blo 2063435 3721471 := bstep (se 1 (by rfl) ⟨2791103, by rfl⟩ : syracuseStep 3721471 = 5582207) B5582207
theorem B19847845 : Blo 2063435 19847845 := bstep (se 4 (by rfl) ⟨1860735, by rfl⟩ : syracuseStep 19847845 = 3721471) B3721471
theorem B26463793 : Blo 2063435 26463793 := bstep (se 2 (by rfl) ⟨9923922, by rfl⟩ : syracuseStep 26463793 = 19847845) B19847845
theorem B35285057 : Blo 2063435 35285057 := bstep (se 2 (by rfl) ⟨13231896, by rfl⟩ : syracuseStep 35285057 = 26463793) B26463793
theorem B23523371 : Blo 2063435 23523371 := bstep (se 1 (by rfl) ⟨17642528, by rfl⟩ : syracuseStep 23523371 = 35285057) B35285057
theorem B15682247 : Blo 2063435 15682247 := bstep (se 1 (by rfl) ⟨11761685, by rfl⟩ : syracuseStep 15682247 = 23523371) B23523371
theorem B10454831 : Blo 2063435 10454831 := bstep (se 1 (by rfl) ⟨7841123, by rfl⟩ : syracuseStep 10454831 = 15682247) B15682247
theorem B6969887 : Blo 2063435 6969887 := bstep (se 1 (by rfl) ⟨5227415, by rfl⟩ : syracuseStep 6969887 = 10454831) B10454831
theorem B4646591 : Blo 2063435 4646591 := bstep (se 1 (by rfl) ⟨3484943, by rfl⟩ : syracuseStep 4646591 = 6969887) B6969887
theorem B3097727 : Blo 2063435 3097727 := bstep (se 1 (by rfl) ⟨2323295, by rfl⟩ : syracuseStep 3097727 = 4646591) B4646591
theorem B2065151 : Blo 2063435 2065151 := bstep (se 1 (by rfl) ⟨1548863, by rfl⟩ : syracuseStep 2065151 = 3097727) B3097727
theorem B3097733 : Blo 2063435 3097733 := bbase (se 4 (by rfl) ⟨290412, by rfl⟩ : syracuseStep 3097733 = 580825) (by norm_num)
theorem B2065155 : Blo 2063435 2065155 := bstep (se 1 (by rfl) ⟨1548866, by rfl⟩ : syracuseStep 2065155 = 3097733) B3097733
theorem B3484957 : Blo 2063435 3484957 := bbase (se 3 (by rfl) ⟨653429, by rfl⟩ : syracuseStep 3484957 = 1306859) (by norm_num)
theorem B4646609 : Blo 2063435 4646609 := bstep (se 2 (by rfl) ⟨1742478, by rfl⟩ : syracuseStep 4646609 = 3484957) B3484957
theorem B3097739 : Blo 2063435 3097739 := bstep (se 1 (by rfl) ⟨2323304, by rfl⟩ : syracuseStep 3097739 = 4646609) B4646609
theorem B2065159 : Blo 2063435 2065159 := bstep (se 1 (by rfl) ⟨1548869, by rfl⟩ : syracuseStep 2065159 = 3097739) B3097739
theorem B2323309 : Blo 2063435 2323309 := bbase (se 3 (by rfl) ⟨435620, by rfl⟩ : syracuseStep 2323309 = 871241) (by norm_num)
theorem B3097745 : Blo 2063435 3097745 := bstep (se 2 (by rfl) ⟨1161654, by rfl⟩ : syracuseStep 3097745 = 2323309) B2323309
theorem B2065163 : Blo 2063435 2065163 := bstep (se 1 (by rfl) ⟨1548872, by rfl⟩ : syracuseStep 2065163 = 3097745) B3097745
theorem B6969941 : Blo 2063435 6969941 := bbase (se 8 (by rfl) ⟨40839, by rfl⟩ : syracuseStep 6969941 = 81679) (by norm_num)
theorem B4646627 : Blo 2063435 4646627 := bstep (se 1 (by rfl) ⟨3484970, by rfl⟩ : syracuseStep 4646627 = 6969941) B6969941
theorem B3097751 : Blo 2063435 3097751 := bstep (se 1 (by rfl) ⟨2323313, by rfl⟩ : syracuseStep 3097751 = 4646627) B4646627
theorem B2065167 : Blo 2063435 2065167 := bstep (se 1 (by rfl) ⟨1548875, by rfl⟩ : syracuseStep 2065167 = 3097751) B3097751
theorem B3097757 : Blo 2063435 3097757 := bbase (se 3 (by rfl) ⟨580829, by rfl⟩ : syracuseStep 3097757 = 1161659) (by norm_num)
theorem B2065171 : Blo 2063435 2065171 := bstep (se 1 (by rfl) ⟨1548878, by rfl⟩ : syracuseStep 2065171 = 3097757) B3097757
theorem B4646645 : Blo 2063435 4646645 := bbase (se 5 (by rfl) ⟨217811, by rfl⟩ : syracuseStep 4646645 = 435623) (by norm_num)
theorem B3097763 : Blo 2063435 3097763 := bstep (se 1 (by rfl) ⟨2323322, by rfl⟩ : syracuseStep 3097763 = 4646645) B4646645
theorem B2065175 : Blo 2063435 2065175 := bstep (se 1 (by rfl) ⟨1548881, by rfl⟩ : syracuseStep 2065175 = 3097763) B3097763
theorem B25120277 : Blo 2063435 25120277 := bbase (se 6 (by rfl) ⟨588756, by rfl⟩ : syracuseStep 25120277 = 1177513) (by norm_num)
theorem B16746851 : Blo 2063435 16746851 := bstep (se 1 (by rfl) ⟨12560138, by rfl⟩ : syracuseStep 16746851 = 25120277) B25120277
theorem B11164567 : Blo 2063435 11164567 := bstep (se 1 (by rfl) ⟨8373425, by rfl⟩ : syracuseStep 11164567 = 16746851) B16746851
theorem B14886089 : Blo 2063435 14886089 := bstep (se 2 (by rfl) ⟨5582283, by rfl⟩ : syracuseStep 14886089 = 11164567) B11164567
theorem B9924059 : Blo 2063435 9924059 := bstep (se 1 (by rfl) ⟨7443044, by rfl⟩ : syracuseStep 9924059 = 14886089) B14886089
theorem B26464157 : Blo 2063435 26464157 := bstep (se 3 (by rfl) ⟨4962029, by rfl⟩ : syracuseStep 26464157 = 9924059) B9924059
theorem B17642771 : Blo 2063435 17642771 := bstep (se 1 (by rfl) ⟨13232078, by rfl⟩ : syracuseStep 17642771 = 26464157) B26464157
theorem B11761847 : Blo 2063435 11761847 := bstep (se 1 (by rfl) ⟨8821385, by rfl⟩ : syracuseStep 11761847 = 17642771) B17642771
theorem B7841231 : Blo 2063435 7841231 := bstep (se 1 (by rfl) ⟨5880923, by rfl⟩ : syracuseStep 7841231 = 11761847) B11761847
theorem B5227487 : Blo 2063435 5227487 := bstep (se 1 (by rfl) ⟨3920615, by rfl⟩ : syracuseStep 5227487 = 7841231) B7841231
theorem B3484991 : Blo 2063435 3484991 := bstep (se 1 (by rfl) ⟨2613743, by rfl⟩ : syracuseStep 3484991 = 5227487) B5227487
theorem B2323327 : Blo 2063435 2323327 := bstep (se 1 (by rfl) ⟨1742495, by rfl⟩ : syracuseStep 2323327 = 3484991) B3484991
theorem B3097769 : Blo 2063435 3097769 := bstep (se 2 (by rfl) ⟨1161663, by rfl⟩ : syracuseStep 3097769 = 2323327) B2323327
theorem B2065179 : Blo 2063435 2065179 := bstep (se 1 (by rfl) ⟨1548884, by rfl⟩ : syracuseStep 2065179 = 3097769) B3097769
theorem B4410701 : Blo 2063435 4410701 := bbase (se 3 (by rfl) ⟨827006, by rfl⟩ : syracuseStep 4410701 = 1654013) (by norm_num)
theorem B2940467 : Blo 2063435 2940467 := bstep (se 1 (by rfl) ⟨2205350, by rfl⟩ : syracuseStep 2940467 = 4410701) B4410701
theorem B7841245 : Blo 2063435 7841245 := bstep (se 3 (by rfl) ⟨1470233, by rfl⟩ : syracuseStep 7841245 = 2940467) B2940467
theorem B10454993 : Blo 2063435 10454993 := bstep (se 2 (by rfl) ⟨3920622, by rfl⟩ : syracuseStep 10454993 = 7841245) B7841245
theorem B6969995 : Blo 2063435 6969995 := bstep (se 1 (by rfl) ⟨5227496, by rfl⟩ : syracuseStep 6969995 = 10454993) B10454993
theorem B4646663 : Blo 2063435 4646663 := bstep (se 1 (by rfl) ⟨3484997, by rfl⟩ : syracuseStep 4646663 = 6969995) B6969995
theorem B3097775 : Blo 2063435 3097775 := bstep (se 1 (by rfl) ⟨2323331, by rfl⟩ : syracuseStep 3097775 = 4646663) B4646663
theorem B2065183 : Blo 2063435 2065183 := bstep (se 1 (by rfl) ⟨1548887, by rfl⟩ : syracuseStep 2065183 = 3097775) B3097775
theorem B3097781 : Blo 2063435 3097781 := bbase (se 5 (by rfl) ⟨145208, by rfl⟩ : syracuseStep 3097781 = 290417) (by norm_num)
theorem B2065187 : Blo 2063435 2065187 := bstep (se 1 (by rfl) ⟨1548890, by rfl⟩ : syracuseStep 2065187 = 3097781) B3097781
theorem B5227517 : Blo 2063435 5227517 := bbase (se 3 (by rfl) ⟨980159, by rfl⟩ : syracuseStep 5227517 = 1960319) (by norm_num)
theorem B3485011 : Blo 2063435 3485011 := bstep (se 1 (by rfl) ⟨2613758, by rfl⟩ : syracuseStep 3485011 = 5227517) B5227517
theorem B4646681 : Blo 2063435 4646681 := bstep (se 2 (by rfl) ⟨1742505, by rfl⟩ : syracuseStep 4646681 = 3485011) B3485011
theorem B3097787 : Blo 2063435 3097787 := bstep (se 1 (by rfl) ⟨2323340, by rfl⟩ : syracuseStep 3097787 = 4646681) B4646681
theorem B2065191 : Blo 2063435 2065191 := bstep (se 1 (by rfl) ⟨1548893, by rfl⟩ : syracuseStep 2065191 = 3097787) B3097787
theorem B2323345 : Blo 2063435 2323345 := bbase (se 2 (by rfl) ⟨871254, by rfl⟩ : syracuseStep 2323345 = 1742509) (by norm_num)
theorem B3097793 : Blo 2063435 3097793 := bstep (se 2 (by rfl) ⟨1161672, by rfl⟩ : syracuseStep 3097793 = 2323345) B2323345
theorem B2065195 : Blo 2063435 2065195 := bstep (se 1 (by rfl) ⟨1548896, by rfl⟩ : syracuseStep 2065195 = 3097793) B3097793
theorem B3920653 : Blo 2063435 3920653 := bbase (se 3 (by rfl) ⟨735122, by rfl⟩ : syracuseStep 3920653 = 1470245) (by norm_num)
theorem B5227537 : Blo 2063435 5227537 := bstep (se 2 (by rfl) ⟨1960326, by rfl⟩ : syracuseStep 5227537 = 3920653) B3920653
theorem B6970049 : Blo 2063435 6970049 := bstep (se 2 (by rfl) ⟨2613768, by rfl⟩ : syracuseStep 6970049 = 5227537) B5227537
theorem B4646699 : Blo 2063435 4646699 := bstep (se 1 (by rfl) ⟨3485024, by rfl⟩ : syracuseStep 4646699 = 6970049) B6970049
theorem B3097799 : Blo 2063435 3097799 := bstep (se 1 (by rfl) ⟨2323349, by rfl⟩ : syracuseStep 3097799 = 4646699) B4646699
theorem B2065199 : Blo 2063435 2065199 := bstep (se 1 (by rfl) ⟨1548899, by rfl⟩ : syracuseStep 2065199 = 3097799) B3097799
theorem B3097805 : Blo 2063435 3097805 := bbase (se 3 (by rfl) ⟨580838, by rfl⟩ : syracuseStep 3097805 = 1161677) (by norm_num)
theorem B2065203 : Blo 2063435 2065203 := bstep (se 1 (by rfl) ⟨1548902, by rfl⟩ : syracuseStep 2065203 = 3097805) B3097805
theorem B4646717 : Blo 2063435 4646717 := bbase (se 3 (by rfl) ⟨871259, by rfl⟩ : syracuseStep 4646717 = 1742519) (by norm_num)
theorem B3097811 : Blo 2063435 3097811 := bstep (se 1 (by rfl) ⟨2323358, by rfl⟩ : syracuseStep 3097811 = 4646717) B4646717
theorem B2065207 : Blo 2063435 2065207 := bstep (se 1 (by rfl) ⟨1548905, by rfl⟩ : syracuseStep 2065207 = 3097811) B3097811
theorem B3485045 : Blo 2063435 3485045 := bbase (se 5 (by rfl) ⟨163361, by rfl⟩ : syracuseStep 3485045 = 326723) (by norm_num)
theorem B2323363 : Blo 2063435 2323363 := bstep (se 1 (by rfl) ⟨1742522, by rfl⟩ : syracuseStep 2323363 = 3485045) B3485045
theorem B3097817 : Blo 2063435 3097817 := bstep (se 2 (by rfl) ⟨1161681, by rfl⟩ : syracuseStep 3097817 = 2323363) B2323363
theorem B2065211 : Blo 2063435 2065211 := bstep (se 1 (by rfl) ⟨1548908, by rfl⟩ : syracuseStep 2065211 = 3097817) B3097817
theorem B3308077 : Blo 2063435 3308077 := bbase (se 3 (by rfl) ⟨620264, by rfl⟩ : syracuseStep 3308077 = 1240529) (by norm_num)
theorem B4410769 : Blo 2063435 4410769 := bstep (se 2 (by rfl) ⟨1654038, by rfl⟩ : syracuseStep 4410769 = 3308077) B3308077
theorem B5881025 : Blo 2063435 5881025 := bstep (se 2 (by rfl) ⟨2205384, by rfl⟩ : syracuseStep 5881025 = 4410769) B4410769
theorem B15682733 : Blo 2063435 15682733 := bstep (se 3 (by rfl) ⟨2940512, by rfl⟩ : syracuseStep 15682733 = 5881025) B5881025
theorem B10455155 : Blo 2063435 10455155 := bstep (se 1 (by rfl) ⟨7841366, by rfl⟩ : syracuseStep 10455155 = 15682733) B15682733
theorem B6970103 : Blo 2063435 6970103 := bstep (se 1 (by rfl) ⟨5227577, by rfl⟩ : syracuseStep 6970103 = 10455155) B10455155
theorem B4646735 : Blo 2063435 4646735 := bstep (se 1 (by rfl) ⟨3485051, by rfl⟩ : syracuseStep 4646735 = 6970103) B6970103
theorem B3097823 : Blo 2063435 3097823 := bstep (se 1 (by rfl) ⟨2323367, by rfl⟩ : syracuseStep 3097823 = 4646735) B4646735
theorem B2065215 : Blo 2063435 2065215 := bstep (se 1 (by rfl) ⟨1548911, by rfl⟩ : syracuseStep 2065215 = 3097823) B3097823
theorem B3097829 : Blo 2063435 3097829 := bbase (se 4 (by rfl) ⟨290421, by rfl⟩ : syracuseStep 3097829 = 580843) (by norm_num)
theorem B2065219 : Blo 2063435 2065219 := bstep (se 1 (by rfl) ⟨1548914, by rfl⟩ : syracuseStep 2065219 = 3097829) B3097829
theorem B6616181 : Blo 2063435 6616181 := bbase (se 5 (by rfl) ⟨310133, by rfl⟩ : syracuseStep 6616181 = 620267) (by norm_num)
theorem B4410787 : Blo 2063435 4410787 := bstep (se 1 (by rfl) ⟨3308090, by rfl⟩ : syracuseStep 4410787 = 6616181) B6616181
theorem B5881049 : Blo 2063435 5881049 := bstep (se 2 (by rfl) ⟨2205393, by rfl⟩ : syracuseStep 5881049 = 4410787) B4410787
theorem B3920699 : Blo 2063435 3920699 := bstep (se 1 (by rfl) ⟨2940524, by rfl⟩ : syracuseStep 3920699 = 5881049) B5881049
theorem B2613799 : Blo 2063435 2613799 := bstep (se 1 (by rfl) ⟨1960349, by rfl⟩ : syracuseStep 2613799 = 3920699) B3920699
theorem B3485065 : Blo 2063435 3485065 := bstep (se 2 (by rfl) ⟨1306899, by rfl⟩ : syracuseStep 3485065 = 2613799) B2613799
theorem B4646753 : Blo 2063435 4646753 := bstep (se 2 (by rfl) ⟨1742532, by rfl⟩ : syracuseStep 4646753 = 3485065) B3485065
theorem B3097835 : Blo 2063435 3097835 := bstep (se 1 (by rfl) ⟨2323376, by rfl⟩ : syracuseStep 3097835 = 4646753) B4646753
theorem B2065223 : Blo 2063435 2065223 := bstep (se 1 (by rfl) ⟨1548917, by rfl⟩ : syracuseStep 2065223 = 3097835) B3097835
theorem B2323381 : Blo 2063435 2323381 := bbase (se 5 (by rfl) ⟨108908, by rfl⟩ : syracuseStep 2323381 = 217817) (by norm_num)
theorem B3097841 : Blo 2063435 3097841 := bstep (se 2 (by rfl) ⟨1161690, by rfl⟩ : syracuseStep 3097841 = 2323381) B2323381
theorem B2065227 : Blo 2063435 2065227 := bstep (se 1 (by rfl) ⟨1548920, by rfl⟩ : syracuseStep 2065227 = 3097841) B3097841
theorem B2613809 : Blo 2063435 2613809 := bbase (se 2 (by rfl) ⟨980178, by rfl⟩ : syracuseStep 2613809 = 1960357) (by norm_num)
theorem B6970157 : Blo 2063435 6970157 := bstep (se 3 (by rfl) ⟨1306904, by rfl⟩ : syracuseStep 6970157 = 2613809) B2613809
theorem B4646771 : Blo 2063435 4646771 := bstep (se 1 (by rfl) ⟨3485078, by rfl⟩ : syracuseStep 4646771 = 6970157) B6970157
theorem B3097847 : Blo 2063435 3097847 := bstep (se 1 (by rfl) ⟨2323385, by rfl⟩ : syracuseStep 3097847 = 4646771) B4646771
theorem B2065231 : Blo 2063435 2065231 := bstep (se 1 (by rfl) ⟨1548923, by rfl⟩ : syracuseStep 2065231 = 3097847) B3097847
theorem B3097853 : Blo 2063435 3097853 := bbase (se 3 (by rfl) ⟨580847, by rfl⟩ : syracuseStep 3097853 = 1161695) (by norm_num)
theorem B2065235 : Blo 2063435 2065235 := bstep (se 1 (by rfl) ⟨1548926, by rfl⟩ : syracuseStep 2065235 = 3097853) B3097853
theorem B4646789 : Blo 2063435 4646789 := bbase (se 4 (by rfl) ⟨435636, by rfl⟩ : syracuseStep 4646789 = 871273) (by norm_num)
theorem B3097859 : Blo 2063435 3097859 := bstep (se 1 (by rfl) ⟨2323394, by rfl⟩ : syracuseStep 3097859 = 4646789) B4646789
theorem B2065239 : Blo 2063435 2065239 := bstep (se 1 (by rfl) ⟨1548929, by rfl⟩ : syracuseStep 2065239 = 3097859) B3097859
theorem B7065301 : Blo 2063435 7065301 := bbase (se 7 (by rfl) ⟨82796, by rfl⟩ : syracuseStep 7065301 = 165593) (by norm_num)
theorem B9420401 : Blo 2063435 9420401 := bstep (se 2 (by rfl) ⟨3532650, by rfl⟩ : syracuseStep 9420401 = 7065301) B7065301
theorem B6280267 : Blo 2063435 6280267 := bstep (se 1 (by rfl) ⟨4710200, by rfl⟩ : syracuseStep 6280267 = 9420401) B9420401
theorem B8373689 : Blo 2063435 8373689 := bstep (se 2 (by rfl) ⟨3140133, by rfl⟩ : syracuseStep 8373689 = 6280267) B6280267
theorem B5582459 : Blo 2063435 5582459 := bstep (se 1 (by rfl) ⟨4186844, by rfl⟩ : syracuseStep 5582459 = 8373689) B8373689
theorem B3721639 : Blo 2063435 3721639 := bstep (se 1 (by rfl) ⟨2791229, by rfl⟩ : syracuseStep 3721639 = 5582459) B5582459
theorem B4962185 : Blo 2063435 4962185 := bstep (se 2 (by rfl) ⟨1860819, by rfl⟩ : syracuseStep 4962185 = 3721639) B3721639
theorem B3308123 : Blo 2063435 3308123 := bstep (se 1 (by rfl) ⟨2481092, by rfl⟩ : syracuseStep 3308123 = 4962185) B4962185
theorem B2205415 : Blo 2063435 2205415 := bstep (se 1 (by rfl) ⟨1654061, by rfl⟩ : syracuseStep 2205415 = 3308123) B3308123
theorem B2940553 : Blo 2063435 2940553 := bstep (se 2 (by rfl) ⟨1102707, by rfl⟩ : syracuseStep 2940553 = 2205415) B2205415
theorem B3920737 : Blo 2063435 3920737 := bstep (se 2 (by rfl) ⟨1470276, by rfl⟩ : syracuseStep 3920737 = 2940553) B2940553
theorem B5227649 : Blo 2063435 5227649 := bstep (se 2 (by rfl) ⟨1960368, by rfl⟩ : syracuseStep 5227649 = 3920737) B3920737
theorem B3485099 : Blo 2063435 3485099 := bstep (se 1 (by rfl) ⟨2613824, by rfl⟩ : syracuseStep 3485099 = 5227649) B5227649
theorem B2323399 : Blo 2063435 2323399 := bstep (se 1 (by rfl) ⟨1742549, by rfl⟩ : syracuseStep 2323399 = 3485099) B3485099
theorem B3097865 : Blo 2063435 3097865 := bstep (se 2 (by rfl) ⟨1161699, by rfl⟩ : syracuseStep 3097865 = 2323399) B2323399
theorem B2065243 : Blo 2063435 2065243 := bstep (se 1 (by rfl) ⟨1548932, by rfl⟩ : syracuseStep 2065243 = 3097865) B3097865
theorem B10455317 : Blo 2063435 10455317 := bbase (se 6 (by rfl) ⟨245046, by rfl⟩ : syracuseStep 10455317 = 490093) (by norm_num)
theorem B6970211 : Blo 2063435 6970211 := bstep (se 1 (by rfl) ⟨5227658, by rfl⟩ : syracuseStep 6970211 = 10455317) B10455317
theorem B4646807 : Blo 2063435 4646807 := bstep (se 1 (by rfl) ⟨3485105, by rfl⟩ : syracuseStep 4646807 = 6970211) B6970211
theorem B3097871 : Blo 2063435 3097871 := bstep (se 1 (by rfl) ⟨2323403, by rfl⟩ : syracuseStep 3097871 = 4646807) B4646807
theorem B2065247 : Blo 2063435 2065247 := bstep (se 1 (by rfl) ⟨1548935, by rfl⟩ : syracuseStep 2065247 = 3097871) B3097871
theorem B3097877 : Blo 2063435 3097877 := bbase (se 6 (by rfl) ⟨72606, by rfl⟩ : syracuseStep 3097877 = 145213) (by norm_num)
theorem B2065251 : Blo 2063435 2065251 := bstep (se 1 (by rfl) ⟨1548938, by rfl⟩ : syracuseStep 2065251 = 3097877) B3097877
theorem B8942069 : Blo 2063435 8942069 := bbase (se 5 (by rfl) ⟨419159, by rfl⟩ : syracuseStep 8942069 = 838319) (by norm_num)
theorem B5961379 : Blo 2063435 5961379 := bstep (se 1 (by rfl) ⟨4471034, by rfl⟩ : syracuseStep 5961379 = 8942069) B8942069
theorem B7948505 : Blo 2063435 7948505 := bstep (se 2 (by rfl) ⟨2980689, by rfl⟩ : syracuseStep 7948505 = 5961379) B5961379
theorem B5299003 : Blo 2063435 5299003 := bstep (se 1 (by rfl) ⟨3974252, by rfl⟩ : syracuseStep 5299003 = 7948505) B7948505
theorem B28261349 : Blo 2063435 28261349 := bstep (se 4 (by rfl) ⟨2649501, by rfl⟩ : syracuseStep 28261349 = 5299003) B5299003
theorem B18840899 : Blo 2063435 18840899 := bstep (se 1 (by rfl) ⟨14130674, by rfl⟩ : syracuseStep 18840899 = 28261349) B28261349
theorem B12560599 : Blo 2063435 12560599 := bstep (se 1 (by rfl) ⟨9420449, by rfl⟩ : syracuseStep 12560599 = 18840899) B18840899
theorem B66989861 : Blo 2063435 66989861 := bstep (se 4 (by rfl) ⟨6280299, by rfl⟩ : syracuseStep 66989861 = 12560599) B12560599
theorem B44659907 : Blo 2063435 44659907 := bstep (se 1 (by rfl) ⟨33494930, by rfl⟩ : syracuseStep 44659907 = 66989861) B66989861
theorem B29773271 : Blo 2063435 29773271 := bstep (se 1 (by rfl) ⟨22329953, by rfl⟩ : syracuseStep 29773271 = 44659907) B44659907
theorem B19848847 : Blo 2063435 19848847 := bstep (se 1 (by rfl) ⟨14886635, by rfl⟩ : syracuseStep 19848847 = 29773271) B29773271
theorem B26465129 : Blo 2063435 26465129 := bstep (se 2 (by rfl) ⟨9924423, by rfl⟩ : syracuseStep 26465129 = 19848847) B19848847
theorem B17643419 : Blo 2063435 17643419 := bstep (se 1 (by rfl) ⟨13232564, by rfl⟩ : syracuseStep 17643419 = 26465129) B26465129
theorem B11762279 : Blo 2063435 11762279 := bstep (se 1 (by rfl) ⟨8821709, by rfl⟩ : syracuseStep 11762279 = 17643419) B17643419
theorem B7841519 : Blo 2063435 7841519 := bstep (se 1 (by rfl) ⟨5881139, by rfl⟩ : syracuseStep 7841519 = 11762279) B11762279
theorem B5227679 : Blo 2063435 5227679 := bstep (se 1 (by rfl) ⟨3920759, by rfl⟩ : syracuseStep 5227679 = 7841519) B7841519
theorem B3485119 : Blo 2063435 3485119 := bstep (se 1 (by rfl) ⟨2613839, by rfl⟩ : syracuseStep 3485119 = 5227679) B5227679
theorem B4646825 : Blo 2063435 4646825 := bstep (se 2 (by rfl) ⟨1742559, by rfl⟩ : syracuseStep 4646825 = 3485119) B3485119
theorem B3097883 : Blo 2063435 3097883 := bstep (se 1 (by rfl) ⟨2323412, by rfl⟩ : syracuseStep 3097883 = 4646825) B4646825
theorem B2065255 : Blo 2063435 2065255 := bstep (se 1 (by rfl) ⟨1548941, by rfl⟩ : syracuseStep 2065255 = 3097883) B3097883
theorem B2323417 : Blo 2063435 2323417 := bbase (se 2 (by rfl) ⟨871281, by rfl⟩ : syracuseStep 2323417 = 1742563) (by norm_num)
theorem B3097889 : Blo 2063435 3097889 := bstep (se 2 (by rfl) ⟨1161708, by rfl⟩ : syracuseStep 3097889 = 2323417) B2323417
theorem B2065259 : Blo 2063435 2065259 := bstep (se 1 (by rfl) ⟨1548944, by rfl⟩ : syracuseStep 2065259 = 3097889) B3097889
theorem B2940581 : Blo 2063435 2940581 := bbase (se 4 (by rfl) ⟨275679, by rfl⟩ : syracuseStep 2940581 = 551359) (by norm_num)
theorem B7841549 : Blo 2063435 7841549 := bstep (se 3 (by rfl) ⟨1470290, by rfl⟩ : syracuseStep 7841549 = 2940581) B2940581
theorem B5227699 : Blo 2063435 5227699 := bstep (se 1 (by rfl) ⟨3920774, by rfl⟩ : syracuseStep 5227699 = 7841549) B7841549
theorem B6970265 : Blo 2063435 6970265 := bstep (se 2 (by rfl) ⟨2613849, by rfl⟩ : syracuseStep 6970265 = 5227699) B5227699
theorem B4646843 : Blo 2063435 4646843 := bstep (se 1 (by rfl) ⟨3485132, by rfl⟩ : syracuseStep 4646843 = 6970265) B6970265
theorem B3097895 : Blo 2063435 3097895 := bstep (se 1 (by rfl) ⟨2323421, by rfl⟩ : syracuseStep 3097895 = 4646843) B4646843
theorem B2065263 : Blo 2063435 2065263 := bstep (se 1 (by rfl) ⟨1548947, by rfl⟩ : syracuseStep 2065263 = 3097895) B3097895
theorem B3097901 : Blo 2063435 3097901 := bbase (se 3 (by rfl) ⟨580856, by rfl⟩ : syracuseStep 3097901 = 1161713) (by norm_num)
theorem B2065267 : Blo 2063435 2065267 := bstep (se 1 (by rfl) ⟨1548950, by rfl⟩ : syracuseStep 2065267 = 3097901) B3097901
theorem B4646861 : Blo 2063435 4646861 := bbase (se 3 (by rfl) ⟨871286, by rfl⟩ : syracuseStep 4646861 = 1742573) (by norm_num)
theorem B3097907 : Blo 2063435 3097907 := bstep (se 1 (by rfl) ⟨2323430, by rfl⟩ : syracuseStep 3097907 = 4646861) B4646861
theorem B2065271 : Blo 2063435 2065271 := bstep (se 1 (by rfl) ⟨1548953, by rfl⟩ : syracuseStep 2065271 = 3097907) B3097907
theorem B2613865 : Blo 2063435 2613865 := bbase (se 2 (by rfl) ⟨980199, by rfl⟩ : syracuseStep 2613865 = 1960399) (by norm_num)
theorem B3485153 : Blo 2063435 3485153 := bstep (se 2 (by rfl) ⟨1306932, by rfl⟩ : syracuseStep 3485153 = 2613865) B2613865
theorem B2323435 : Blo 2063435 2323435 := bstep (se 1 (by rfl) ⟨1742576, by rfl⟩ : syracuseStep 2323435 = 3485153) B3485153
theorem B3097913 : Blo 2063435 3097913 := bstep (se 2 (by rfl) ⟨1161717, by rfl⟩ : syracuseStep 3097913 = 2323435) B2323435
theorem B2065275 : Blo 2063435 2065275 := bstep (se 1 (by rfl) ⟨1548956, by rfl⟩ : syracuseStep 2065275 = 3097913) B3097913
theorem B4962269 : Blo 2063435 4962269 := bbase (se 3 (by rfl) ⟨930425, by rfl⟩ : syracuseStep 4962269 = 1860851) (by norm_num)
theorem B13232717 : Blo 2063435 13232717 := bstep (se 3 (by rfl) ⟨2481134, by rfl⟩ : syracuseStep 13232717 = 4962269) B4962269
theorem B8821811 : Blo 2063435 8821811 := bstep (se 1 (by rfl) ⟨6616358, by rfl⟩ : syracuseStep 8821811 = 13232717) B13232717
theorem B23524829 : Blo 2063435 23524829 := bstep (se 3 (by rfl) ⟨4410905, by rfl⟩ : syracuseStep 23524829 = 8821811) B8821811
theorem B15683219 : Blo 2063435 15683219 := bstep (se 1 (by rfl) ⟨11762414, by rfl⟩ : syracuseStep 15683219 = 23524829) B23524829
theorem B10455479 : Blo 2063435 10455479 := bstep (se 1 (by rfl) ⟨7841609, by rfl⟩ : syracuseStep 10455479 = 15683219) B15683219
theorem B6970319 : Blo 2063435 6970319 := bstep (se 1 (by rfl) ⟨5227739, by rfl⟩ : syracuseStep 6970319 = 10455479) B10455479
theorem B4646879 : Blo 2063435 4646879 := bstep (se 1 (by rfl) ⟨3485159, by rfl⟩ : syracuseStep 4646879 = 6970319) B6970319
theorem B3097919 : Blo 2063435 3097919 := bstep (se 1 (by rfl) ⟨2323439, by rfl⟩ : syracuseStep 3097919 = 4646879) B4646879
theorem B2065279 : Blo 2063435 2065279 := bstep (se 1 (by rfl) ⟨1548959, by rfl⟩ : syracuseStep 2065279 = 3097919) B3097919
theorem B3097925 : Blo 2063435 3097925 := bbase (se 4 (by rfl) ⟨290430, by rfl⟩ : syracuseStep 3097925 = 580861) (by norm_num)
theorem B2065283 : Blo 2063435 2065283 := bstep (se 1 (by rfl) ⟨1548962, by rfl⟩ : syracuseStep 2065283 = 3097925) B3097925
theorem B3485173 : Blo 2063435 3485173 := bbase (se 5 (by rfl) ⟨163367, by rfl⟩ : syracuseStep 3485173 = 326735) (by norm_num)
theorem B4646897 : Blo 2063435 4646897 := bstep (se 2 (by rfl) ⟨1742586, by rfl⟩ : syracuseStep 4646897 = 3485173) B3485173
theorem B3097931 : Blo 2063435 3097931 := bstep (se 1 (by rfl) ⟨2323448, by rfl⟩ : syracuseStep 3097931 = 4646897) B4646897
theorem B2065287 : Blo 2063435 2065287 := bstep (se 1 (by rfl) ⟨1548965, by rfl⟩ : syracuseStep 2065287 = 3097931) B3097931
theorem B2323453 : Blo 2063435 2323453 := bbase (se 3 (by rfl) ⟨435647, by rfl⟩ : syracuseStep 2323453 = 871295) (by norm_num)
theorem B3097937 : Blo 2063435 3097937 := bstep (se 2 (by rfl) ⟨1161726, by rfl⟩ : syracuseStep 3097937 = 2323453) B2323453
theorem B2065291 : Blo 2063435 2065291 := bstep (se 1 (by rfl) ⟨1548968, by rfl⟩ : syracuseStep 2065291 = 3097937) B3097937
theorem B6970373 : Blo 2063435 6970373 := bbase (se 4 (by rfl) ⟨653472, by rfl⟩ : syracuseStep 6970373 = 1306945) (by norm_num)
theorem B4646915 : Blo 2063435 4646915 := bstep (se 1 (by rfl) ⟨3485186, by rfl⟩ : syracuseStep 4646915 = 6970373) B6970373
theorem B3097943 : Blo 2063435 3097943 := bstep (se 1 (by rfl) ⟨2323457, by rfl⟩ : syracuseStep 3097943 = 4646915) B4646915
theorem B2065295 : Blo 2063435 2065295 := bstep (se 1 (by rfl) ⟨1548971, by rfl⟩ : syracuseStep 2065295 = 3097943) B3097943
theorem B3097949 : Blo 2063435 3097949 := bbase (se 3 (by rfl) ⟨580865, by rfl⟩ : syracuseStep 3097949 = 1161731) (by norm_num)
theorem B2065299 : Blo 2063435 2065299 := bstep (se 1 (by rfl) ⟨1548974, by rfl⟩ : syracuseStep 2065299 = 3097949) B3097949
theorem B4646933 : Blo 2063435 4646933 := bbase (se 6 (by rfl) ⟨108912, by rfl⟩ : syracuseStep 4646933 = 217825) (by norm_num)
theorem B3097955 : Blo 2063435 3097955 := bstep (se 1 (by rfl) ⟨2323466, by rfl⟩ : syracuseStep 3097955 = 4646933) B4646933
theorem B2065303 : Blo 2063435 2065303 := bstep (se 1 (by rfl) ⟨1548977, by rfl⟩ : syracuseStep 2065303 = 3097955) B3097955
theorem B7841717 : Blo 2063435 7841717 := bbase (se 5 (by rfl) ⟨367580, by rfl⟩ : syracuseStep 7841717 = 735161) (by norm_num)
theorem B5227811 : Blo 2063435 5227811 := bstep (se 1 (by rfl) ⟨3920858, by rfl⟩ : syracuseStep 5227811 = 7841717) B7841717
theorem B3485207 : Blo 2063435 3485207 := bstep (se 1 (by rfl) ⟨2613905, by rfl⟩ : syracuseStep 3485207 = 5227811) B5227811
theorem B2323471 : Blo 2063435 2323471 := bstep (se 1 (by rfl) ⟨1742603, by rfl⟩ : syracuseStep 2323471 = 3485207) B3485207
theorem B3097961 : Blo 2063435 3097961 := bstep (se 2 (by rfl) ⟨1161735, by rfl⟩ : syracuseStep 3097961 = 2323471) B2323471
theorem B2065307 : Blo 2063435 2065307 := bstep (se 1 (by rfl) ⟨1548980, by rfl⟩ : syracuseStep 2065307 = 3097961) B3097961
theorem B4186981 : Blo 2063435 4186981 := bbase (se 4 (by rfl) ⟨392529, by rfl⟩ : syracuseStep 4186981 = 785059) (by norm_num)
theorem B5582641 : Blo 2063435 5582641 := bstep (se 2 (by rfl) ⟨2093490, by rfl⟩ : syracuseStep 5582641 = 4186981) B4186981
theorem B7443521 : Blo 2063435 7443521 := bstep (se 2 (by rfl) ⟨2791320, by rfl⟩ : syracuseStep 7443521 = 5582641) B5582641
theorem B4962347 : Blo 2063435 4962347 := bstep (se 1 (by rfl) ⟨3721760, by rfl⟩ : syracuseStep 4962347 = 7443521) B7443521
theorem B3308231 : Blo 2063435 3308231 := bstep (se 1 (by rfl) ⟨2481173, by rfl⟩ : syracuseStep 3308231 = 4962347) B4962347
theorem B2205487 : Blo 2063435 2205487 := bstep (se 1 (by rfl) ⟨1654115, by rfl⟩ : syracuseStep 2205487 = 3308231) B3308231
theorem B11762597 : Blo 2063435 11762597 := bstep (se 4 (by rfl) ⟨1102743, by rfl⟩ : syracuseStep 11762597 = 2205487) B2205487
theorem B7841731 : Blo 2063435 7841731 := bstep (se 1 (by rfl) ⟨5881298, by rfl⟩ : syracuseStep 7841731 = 11762597) B11762597
theorem B10455641 : Blo 2063435 10455641 := bstep (se 2 (by rfl) ⟨3920865, by rfl⟩ : syracuseStep 10455641 = 7841731) B7841731
theorem B6970427 : Blo 2063435 6970427 := bstep (se 1 (by rfl) ⟨5227820, by rfl⟩ : syracuseStep 6970427 = 10455641) B10455641
theorem B4646951 : Blo 2063435 4646951 := bstep (se 1 (by rfl) ⟨3485213, by rfl⟩ : syracuseStep 4646951 = 6970427) B6970427
theorem B3097967 : Blo 2063435 3097967 := bstep (se 1 (by rfl) ⟨2323475, by rfl⟩ : syracuseStep 3097967 = 4646951) B4646951
theorem B2065311 : Blo 2063435 2065311 := bstep (se 1 (by rfl) ⟨1548983, by rfl⟩ : syracuseStep 2065311 = 3097967) B3097967
theorem B3097973 : Blo 2063435 3097973 := bbase (se 5 (by rfl) ⟨145217, by rfl⟩ : syracuseStep 3097973 = 290435) (by norm_num)
theorem B2065315 : Blo 2063435 2065315 := bstep (se 1 (by rfl) ⟨1548986, by rfl⟩ : syracuseStep 2065315 = 3097973) B3097973
theorem B2940661 : Blo 2063435 2940661 := bbase (se 5 (by rfl) ⟨137843, by rfl⟩ : syracuseStep 2940661 = 275687) (by norm_num)
theorem B3920881 : Blo 2063435 3920881 := bstep (se 2 (by rfl) ⟨1470330, by rfl⟩ : syracuseStep 3920881 = 2940661) B2940661
theorem B5227841 : Blo 2063435 5227841 := bstep (se 2 (by rfl) ⟨1960440, by rfl⟩ : syracuseStep 5227841 = 3920881) B3920881
theorem B3485227 : Blo 2063435 3485227 := bstep (se 1 (by rfl) ⟨2613920, by rfl⟩ : syracuseStep 3485227 = 5227841) B5227841
theorem B4646969 : Blo 2063435 4646969 := bstep (se 2 (by rfl) ⟨1742613, by rfl⟩ : syracuseStep 4646969 = 3485227) B3485227
theorem B3097979 : Blo 2063435 3097979 := bstep (se 1 (by rfl) ⟨2323484, by rfl⟩ : syracuseStep 3097979 = 4646969) B4646969
theorem B2065319 : Blo 2063435 2065319 := bstep (se 1 (by rfl) ⟨1548989, by rfl⟩ : syracuseStep 2065319 = 3097979) B3097979
theorem B2323489 : Blo 2063435 2323489 := bbase (se 2 (by rfl) ⟨871308, by rfl⟩ : syracuseStep 2323489 = 1742617) (by norm_num)
theorem B3097985 : Blo 2063435 3097985 := bstep (se 2 (by rfl) ⟨1161744, by rfl⟩ : syracuseStep 3097985 = 2323489) B2323489
theorem B2065323 : Blo 2063435 2065323 := bstep (se 1 (by rfl) ⟨1548992, by rfl⟩ : syracuseStep 2065323 = 3097985) B3097985
theorem B5227861 : Blo 2063435 5227861 := bbase (se 12 (by rfl) ⟨1914, by rfl⟩ : syracuseStep 5227861 = 3829) (by norm_num)
theorem B6970481 : Blo 2063435 6970481 := bstep (se 2 (by rfl) ⟨2613930, by rfl⟩ : syracuseStep 6970481 = 5227861) B5227861
theorem B4646987 : Blo 2063435 4646987 := bstep (se 1 (by rfl) ⟨3485240, by rfl⟩ : syracuseStep 4646987 = 6970481) B6970481
theorem B3097991 : Blo 2063435 3097991 := bstep (se 1 (by rfl) ⟨2323493, by rfl⟩ : syracuseStep 3097991 = 4646987) B4646987
theorem B2065327 : Blo 2063435 2065327 := bstep (se 1 (by rfl) ⟨1548995, by rfl⟩ : syracuseStep 2065327 = 3097991) B3097991
theorem B3097997 : Blo 2063435 3097997 := bbase (se 3 (by rfl) ⟨580874, by rfl⟩ : syracuseStep 3097997 = 1161749) (by norm_num)
theorem B2065331 : Blo 2063435 2065331 := bstep (se 1 (by rfl) ⟨1548998, by rfl⟩ : syracuseStep 2065331 = 3097997) B3097997
theorem B4647005 : Blo 2063435 4647005 := bbase (se 3 (by rfl) ⟨871313, by rfl⟩ : syracuseStep 4647005 = 1742627) (by norm_num)
theorem B3098003 : Blo 2063435 3098003 := bstep (se 1 (by rfl) ⟨2323502, by rfl⟩ : syracuseStep 3098003 = 4647005) B4647005
theorem B2065335 : Blo 2063435 2065335 := bstep (se 1 (by rfl) ⟨1549001, by rfl⟩ : syracuseStep 2065335 = 3098003) B3098003
theorem B3485261 : Blo 2063435 3485261 := bbase (se 3 (by rfl) ⟨653486, by rfl⟩ : syracuseStep 3485261 = 1306973) (by norm_num)
theorem B2323507 : Blo 2063435 2323507 := bstep (se 1 (by rfl) ⟨1742630, by rfl⟩ : syracuseStep 2323507 = 3485261) B3485261
theorem B3098009 : Blo 2063435 3098009 := bstep (se 2 (by rfl) ⟨1161753, by rfl⟩ : syracuseStep 3098009 = 2323507) B2323507
theorem B2065339 : Blo 2063435 2065339 := bstep (se 1 (by rfl) ⟨1549004, by rfl⟩ : syracuseStep 2065339 = 3098009) B3098009
theorem B5299229 : Blo 2063435 5299229 := bbase (se 3 (by rfl) ⟨993605, by rfl⟩ : syracuseStep 5299229 = 1987211) (by norm_num)
theorem B3532819 : Blo 2063435 3532819 := bstep (se 1 (by rfl) ⟨2649614, by rfl⟩ : syracuseStep 3532819 = 5299229) B5299229
theorem B4710425 : Blo 2063435 4710425 := bstep (se 2 (by rfl) ⟨1766409, by rfl⟩ : syracuseStep 4710425 = 3532819) B3532819
theorem B50244533 : Blo 2063435 50244533 := bstep (se 5 (by rfl) ⟨2355212, by rfl⟩ : syracuseStep 50244533 = 4710425) B4710425
theorem B33496355 : Blo 2063435 33496355 := bstep (se 1 (by rfl) ⟨25122266, by rfl⟩ : syracuseStep 33496355 = 50244533) B50244533
theorem B22330903 : Blo 2063435 22330903 := bstep (se 1 (by rfl) ⟨16748177, by rfl⟩ : syracuseStep 22330903 = 33496355) B33496355
theorem B29774537 : Blo 2063435 29774537 := bstep (se 2 (by rfl) ⟨11165451, by rfl⟩ : syracuseStep 29774537 = 22330903) B22330903
theorem B19849691 : Blo 2063435 19849691 := bstep (se 1 (by rfl) ⟨14887268, by rfl⟩ : syracuseStep 19849691 = 29774537) B29774537
theorem B13233127 : Blo 2063435 13233127 := bstep (se 1 (by rfl) ⟨9924845, by rfl⟩ : syracuseStep 13233127 = 19849691) B19849691
theorem B17644169 : Blo 2063435 17644169 := bstep (se 2 (by rfl) ⟨6616563, by rfl⟩ : syracuseStep 17644169 = 13233127) B13233127
theorem B11762779 : Blo 2063435 11762779 := bstep (se 1 (by rfl) ⟨8822084, by rfl⟩ : syracuseStep 11762779 = 17644169) B17644169
theorem B15683705 : Blo 2063435 15683705 := bstep (se 2 (by rfl) ⟨5881389, by rfl⟩ : syracuseStep 15683705 = 11762779) B11762779
theorem B10455803 : Blo 2063435 10455803 := bstep (se 1 (by rfl) ⟨7841852, by rfl⟩ : syracuseStep 10455803 = 15683705) B15683705
theorem B6970535 : Blo 2063435 6970535 := bstep (se 1 (by rfl) ⟨5227901, by rfl⟩ : syracuseStep 6970535 = 10455803) B10455803
theorem B4647023 : Blo 2063435 4647023 := bstep (se 1 (by rfl) ⟨3485267, by rfl⟩ : syracuseStep 4647023 = 6970535) B6970535
theorem B3098015 : Blo 2063435 3098015 := bstep (se 1 (by rfl) ⟨2323511, by rfl⟩ : syracuseStep 3098015 = 4647023) B4647023
theorem B2065343 : Blo 2063435 2065343 := bstep (se 1 (by rfl) ⟨1549007, by rfl⟩ : syracuseStep 2065343 = 3098015) B3098015
theorem B3098021 : Blo 2063435 3098021 := bbase (se 4 (by rfl) ⟨290439, by rfl⟩ : syracuseStep 3098021 = 580879) (by norm_num)
theorem B2065347 : Blo 2063435 2065347 := bstep (se 1 (by rfl) ⟨1549010, by rfl⟩ : syracuseStep 2065347 = 3098021) B3098021
theorem B2613961 : Blo 2063435 2613961 := bbase (se 2 (by rfl) ⟨980235, by rfl⟩ : syracuseStep 2613961 = 1960471) (by norm_num)
theorem B3485281 : Blo 2063435 3485281 := bstep (se 2 (by rfl) ⟨1306980, by rfl⟩ : syracuseStep 3485281 = 2613961) B2613961
theorem B4647041 : Blo 2063435 4647041 := bstep (se 2 (by rfl) ⟨1742640, by rfl⟩ : syracuseStep 4647041 = 3485281) B3485281
theorem B3098027 : Blo 2063435 3098027 := bstep (se 1 (by rfl) ⟨2323520, by rfl⟩ : syracuseStep 3098027 = 4647041) B4647041
theorem B2065351 : Blo 2063435 2065351 := bstep (se 1 (by rfl) ⟨1549013, by rfl⟩ : syracuseStep 2065351 = 3098027) B3098027
theorem B2323525 : Blo 2063435 2323525 := bbase (se 4 (by rfl) ⟨217830, by rfl⟩ : syracuseStep 2323525 = 435661) (by norm_num)
theorem B3098033 : Blo 2063435 3098033 := bstep (se 2 (by rfl) ⟨1161762, by rfl⟩ : syracuseStep 3098033 = 2323525) B2323525
theorem B2065355 : Blo 2063435 2065355 := bstep (se 1 (by rfl) ⟨1549016, by rfl⟩ : syracuseStep 2065355 = 3098033) B3098033
theorem B3920957 : Blo 2063435 3920957 := bbase (se 3 (by rfl) ⟨735179, by rfl⟩ : syracuseStep 3920957 = 1470359) (by norm_num)
theorem B2613971 : Blo 2063435 2613971 := bstep (se 1 (by rfl) ⟨1960478, by rfl⟩ : syracuseStep 2613971 = 3920957) B3920957
theorem B6970589 : Blo 2063435 6970589 := bstep (se 3 (by rfl) ⟨1306985, by rfl⟩ : syracuseStep 6970589 = 2613971) B2613971
theorem B4647059 : Blo 2063435 4647059 := bstep (se 1 (by rfl) ⟨3485294, by rfl⟩ : syracuseStep 4647059 = 6970589) B6970589
theorem B3098039 : Blo 2063435 3098039 := bstep (se 1 (by rfl) ⟨2323529, by rfl⟩ : syracuseStep 3098039 = 4647059) B4647059
theorem B2065359 : Blo 2063435 2065359 := bstep (se 1 (by rfl) ⟨1549019, by rfl⟩ : syracuseStep 2065359 = 3098039) B3098039
theorem B3098045 : Blo 2063435 3098045 := bbase (se 3 (by rfl) ⟨580883, by rfl⟩ : syracuseStep 3098045 = 1161767) (by norm_num)
theorem B2065363 : Blo 2063435 2065363 := bstep (se 1 (by rfl) ⟨1549022, by rfl⟩ : syracuseStep 2065363 = 3098045) B3098045
theorem B4647077 : Blo 2063435 4647077 := bbase (se 4 (by rfl) ⟨435663, by rfl⟩ : syracuseStep 4647077 = 871327) (by norm_num)
theorem B3098051 : Blo 2063435 3098051 := bstep (se 1 (by rfl) ⟨2323538, by rfl⟩ : syracuseStep 3098051 = 4647077) B4647077
theorem B2065367 : Blo 2063435 2065367 := bstep (se 1 (by rfl) ⟨1549025, by rfl⟩ : syracuseStep 2065367 = 3098051) B3098051
theorem B5227973 : Blo 2063435 5227973 := bbase (se 4 (by rfl) ⟨490122, by rfl⟩ : syracuseStep 5227973 = 980245) (by norm_num)
theorem B3485315 : Blo 2063435 3485315 := bstep (se 1 (by rfl) ⟨2613986, by rfl⟩ : syracuseStep 3485315 = 5227973) B5227973
theorem B2323543 : Blo 2063435 2323543 := bstep (se 1 (by rfl) ⟨1742657, by rfl⟩ : syracuseStep 2323543 = 3485315) B3485315
theorem B3098057 : Blo 2063435 3098057 := bstep (se 2 (by rfl) ⟨1161771, by rfl⟩ : syracuseStep 3098057 = 2323543) B2323543
theorem B2065371 : Blo 2063435 2065371 := bstep (se 1 (by rfl) ⟨1549028, by rfl⟩ : syracuseStep 2065371 = 3098057) B3098057
theorem B7065749 : Blo 2063435 7065749 := bbase (se 6 (by rfl) ⟨165603, by rfl⟩ : syracuseStep 7065749 = 331207) (by norm_num)
theorem B18841997 : Blo 2063435 18841997 := bstep (se 3 (by rfl) ⟨3532874, by rfl⟩ : syracuseStep 18841997 = 7065749) B7065749
theorem B12561331 : Blo 2063435 12561331 := bstep (se 1 (by rfl) ⟨9420998, by rfl⟩ : syracuseStep 12561331 = 18841997) B18841997
theorem B16748441 : Blo 2063435 16748441 := bstep (se 2 (by rfl) ⟨6280665, by rfl⟩ : syracuseStep 16748441 = 12561331) B12561331
theorem B11165627 : Blo 2063435 11165627 := bstep (se 1 (by rfl) ⟨8374220, by rfl⟩ : syracuseStep 11165627 = 16748441) B16748441
theorem B7443751 : Blo 2063435 7443751 := bstep (se 1 (by rfl) ⟨5582813, by rfl⟩ : syracuseStep 7443751 = 11165627) B11165627
theorem B9925001 : Blo 2063435 9925001 := bstep (se 2 (by rfl) ⟨3721875, by rfl⟩ : syracuseStep 9925001 = 7443751) B7443751
theorem B6616667 : Blo 2063435 6616667 := bstep (se 1 (by rfl) ⟨4962500, by rfl⟩ : syracuseStep 6616667 = 9925001) B9925001
theorem B4411111 : Blo 2063435 4411111 := bstep (se 1 (by rfl) ⟨3308333, by rfl⟩ : syracuseStep 4411111 = 6616667) B6616667
theorem B5881481 : Blo 2063435 5881481 := bstep (se 2 (by rfl) ⟨2205555, by rfl⟩ : syracuseStep 5881481 = 4411111) B4411111
theorem B3920987 : Blo 2063435 3920987 := bstep (se 1 (by rfl) ⟨2940740, by rfl⟩ : syracuseStep 3920987 = 5881481) B5881481
theorem B10455965 : Blo 2063435 10455965 := bstep (se 3 (by rfl) ⟨1960493, by rfl⟩ : syracuseStep 10455965 = 3920987) B3920987
theorem B6970643 : Blo 2063435 6970643 := bstep (se 1 (by rfl) ⟨5227982, by rfl⟩ : syracuseStep 6970643 = 10455965) B10455965
theorem B4647095 : Blo 2063435 4647095 := bstep (se 1 (by rfl) ⟨3485321, by rfl⟩ : syracuseStep 4647095 = 6970643) B6970643
theorem B3098063 : Blo 2063435 3098063 := bstep (se 1 (by rfl) ⟨2323547, by rfl⟩ : syracuseStep 3098063 = 4647095) B4647095
theorem B2065375 : Blo 2063435 2065375 := bstep (se 1 (by rfl) ⟨1549031, by rfl⟩ : syracuseStep 2065375 = 3098063) B3098063
theorem B3098069 : Blo 2063435 3098069 := bbase (se 7 (by rfl) ⟨36305, by rfl⟩ : syracuseStep 3098069 = 72611) (by norm_num)
theorem B2065379 : Blo 2063435 2065379 := bstep (se 1 (by rfl) ⟨1549034, by rfl⟩ : syracuseStep 2065379 = 3098069) B3098069
theorem B7842005 : Blo 2063435 7842005 := bbase (se 7 (by rfl) ⟨91898, by rfl⟩ : syracuseStep 7842005 = 183797) (by norm_num)
theorem B5228003 : Blo 2063435 5228003 := bstep (se 1 (by rfl) ⟨3921002, by rfl⟩ : syracuseStep 5228003 = 7842005) B7842005
theorem B3485335 : Blo 2063435 3485335 := bstep (se 1 (by rfl) ⟨2614001, by rfl⟩ : syracuseStep 3485335 = 5228003) B5228003
theorem B4647113 : Blo 2063435 4647113 := bstep (se 2 (by rfl) ⟨1742667, by rfl⟩ : syracuseStep 4647113 = 3485335) B3485335
theorem B3098075 : Blo 2063435 3098075 := bstep (se 1 (by rfl) ⟨2323556, by rfl⟩ : syracuseStep 3098075 = 4647113) B4647113
theorem B2065383 : Blo 2063435 2065383 := bstep (se 1 (by rfl) ⟨1549037, by rfl⟩ : syracuseStep 2065383 = 3098075) B3098075
theorem B2323561 : Blo 2063435 2323561 := bbase (se 2 (by rfl) ⟨871335, by rfl⟩ : syracuseStep 2323561 = 1742671) (by norm_num)
theorem B3098081 : Blo 2063435 3098081 := bstep (se 2 (by rfl) ⟨1161780, by rfl⟩ : syracuseStep 3098081 = 2323561) B2323561
theorem B2065387 : Blo 2063435 2065387 := bstep (se 1 (by rfl) ⟨1549040, by rfl⟩ : syracuseStep 2065387 = 3098081) B3098081
theorem B2649677 : Blo 2063435 2649677 := bbase (se 3 (by rfl) ⟨496814, by rfl⟩ : syracuseStep 2649677 = 993629) (by norm_num)
theorem B7065805 : Blo 2063435 7065805 := bstep (se 3 (by rfl) ⟨1324838, by rfl⟩ : syracuseStep 7065805 = 2649677) B2649677
theorem B9421073 : Blo 2063435 9421073 := bstep (se 2 (by rfl) ⟨3532902, by rfl⟩ : syracuseStep 9421073 = 7065805) B7065805
theorem B6280715 : Blo 2063435 6280715 := bstep (se 1 (by rfl) ⟨4710536, by rfl⟩ : syracuseStep 6280715 = 9421073) B9421073
theorem B4187143 : Blo 2063435 4187143 := bstep (se 1 (by rfl) ⟨3140357, by rfl⟩ : syracuseStep 4187143 = 6280715) B6280715
theorem B5582857 : Blo 2063435 5582857 := bstep (se 2 (by rfl) ⟨2093571, by rfl⟩ : syracuseStep 5582857 = 4187143) B4187143
theorem B7443809 : Blo 2063435 7443809 := bstep (se 2 (by rfl) ⟨2791428, by rfl⟩ : syracuseStep 7443809 = 5582857) B5582857
theorem B4962539 : Blo 2063435 4962539 := bstep (se 1 (by rfl) ⟨3721904, by rfl⟩ : syracuseStep 4962539 = 7443809) B7443809
theorem B3308359 : Blo 2063435 3308359 := bstep (se 1 (by rfl) ⟨2481269, by rfl⟩ : syracuseStep 3308359 = 4962539) B4962539
theorem B4411145 : Blo 2063435 4411145 := bstep (se 2 (by rfl) ⟨1654179, by rfl⟩ : syracuseStep 4411145 = 3308359) B3308359
theorem B11763053 : Blo 2063435 11763053 := bstep (se 3 (by rfl) ⟨2205572, by rfl⟩ : syracuseStep 11763053 = 4411145) B4411145
theorem B7842035 : Blo 2063435 7842035 := bstep (se 1 (by rfl) ⟨5881526, by rfl⟩ : syracuseStep 7842035 = 11763053) B11763053
theorem B5228023 : Blo 2063435 5228023 := bstep (se 1 (by rfl) ⟨3921017, by rfl⟩ : syracuseStep 5228023 = 7842035) B7842035
theorem B6970697 : Blo 2063435 6970697 := bstep (se 2 (by rfl) ⟨2614011, by rfl⟩ : syracuseStep 6970697 = 5228023) B5228023
theorem B4647131 : Blo 2063435 4647131 := bstep (se 1 (by rfl) ⟨3485348, by rfl⟩ : syracuseStep 4647131 = 6970697) B6970697
theorem B3098087 : Blo 2063435 3098087 := bstep (se 1 (by rfl) ⟨2323565, by rfl⟩ : syracuseStep 3098087 = 4647131) B4647131
theorem B2065391 : Blo 2063435 2065391 := bstep (se 1 (by rfl) ⟨1549043, by rfl⟩ : syracuseStep 2065391 = 3098087) B3098087
theorem B3098093 : Blo 2063435 3098093 := bbase (se 3 (by rfl) ⟨580892, by rfl⟩ : syracuseStep 3098093 = 1161785) (by norm_num)
theorem B2065395 : Blo 2063435 2065395 := bstep (se 1 (by rfl) ⟨1549046, by rfl⟩ : syracuseStep 2065395 = 3098093) B3098093
theorem B4647149 : Blo 2063435 4647149 := bbase (se 3 (by rfl) ⟨871340, by rfl⟩ : syracuseStep 4647149 = 1742681) (by norm_num)
theorem B3098099 : Blo 2063435 3098099 := bstep (se 1 (by rfl) ⟨2323574, by rfl⟩ : syracuseStep 3098099 = 4647149) B4647149
theorem B2065399 : Blo 2063435 2065399 := bstep (se 1 (by rfl) ⟨1549049, by rfl⟩ : syracuseStep 2065399 = 3098099) B3098099
theorem B2940781 : Blo 2063435 2940781 := bbase (se 3 (by rfl) ⟨551396, by rfl⟩ : syracuseStep 2940781 = 1102793) (by norm_num)
theorem B3921041 : Blo 2063435 3921041 := bstep (se 2 (by rfl) ⟨1470390, by rfl⟩ : syracuseStep 3921041 = 2940781) B2940781
theorem B2614027 : Blo 2063435 2614027 := bstep (se 1 (by rfl) ⟨1960520, by rfl⟩ : syracuseStep 2614027 = 3921041) B3921041
theorem B3485369 : Blo 2063435 3485369 := bstep (se 2 (by rfl) ⟨1307013, by rfl⟩ : syracuseStep 3485369 = 2614027) B2614027
theorem B2323579 : Blo 2063435 2323579 := bstep (se 1 (by rfl) ⟨1742684, by rfl⟩ : syracuseStep 2323579 = 3485369) B3485369
theorem B3098105 : Blo 2063435 3098105 := bstep (se 2 (by rfl) ⟨1161789, by rfl⟩ : syracuseStep 3098105 = 2323579) B2323579
theorem B2065403 : Blo 2063435 2065403 := bstep (se 1 (by rfl) ⟨1549052, by rfl⟩ : syracuseStep 2065403 = 3098105) B3098105
theorem B3140381 : Blo 2063435 3140381 := bbase (se 3 (by rfl) ⟨588821, by rfl⟩ : syracuseStep 3140381 = 1177643) (by norm_num)
theorem B2093587 : Blo 2063435 2093587 := bstep (se 1 (by rfl) ⟨1570190, by rfl⟩ : syracuseStep 2093587 = 3140381) B3140381
theorem B11165797 : Blo 2063435 11165797 := bstep (se 4 (by rfl) ⟨1046793, by rfl⟩ : syracuseStep 11165797 = 2093587) B2093587
theorem B14887729 : Blo 2063435 14887729 := bstep (se 2 (by rfl) ⟨5582898, by rfl⟩ : syracuseStep 14887729 = 11165797) B11165797
theorem B79401221 : Blo 2063435 79401221 := bstep (se 4 (by rfl) ⟨7443864, by rfl⟩ : syracuseStep 79401221 = 14887729) B14887729
theorem B52934147 : Blo 2063435 52934147 := bstep (se 1 (by rfl) ⟨39700610, by rfl⟩ : syracuseStep 52934147 = 79401221) B79401221
theorem B35289431 : Blo 2063435 35289431 := bstep (se 1 (by rfl) ⟨26467073, by rfl⟩ : syracuseStep 35289431 = 52934147) B52934147
theorem B23526287 : Blo 2063435 23526287 := bstep (se 1 (by rfl) ⟨17644715, by rfl⟩ : syracuseStep 23526287 = 35289431) B35289431
theorem B15684191 : Blo 2063435 15684191 := bstep (se 1 (by rfl) ⟨11763143, by rfl⟩ : syracuseStep 15684191 = 23526287) B23526287
theorem B10456127 : Blo 2063435 10456127 := bstep (se 1 (by rfl) ⟨7842095, by rfl⟩ : syracuseStep 10456127 = 15684191) B15684191
theorem B6970751 : Blo 2063435 6970751 := bstep (se 1 (by rfl) ⟨5228063, by rfl⟩ : syracuseStep 6970751 = 10456127) B10456127
theorem B4647167 : Blo 2063435 4647167 := bstep (se 1 (by rfl) ⟨3485375, by rfl⟩ : syracuseStep 4647167 = 6970751) B6970751
theorem B3098111 : Blo 2063435 3098111 := bstep (se 1 (by rfl) ⟨2323583, by rfl⟩ : syracuseStep 3098111 = 4647167) B4647167
theorem B2065407 : Blo 2063435 2065407 := bstep (se 1 (by rfl) ⟨1549055, by rfl⟩ : syracuseStep 2065407 = 3098111) B3098111
theorem B3098117 : Blo 2063435 3098117 := bbase (se 4 (by rfl) ⟨290448, by rfl⟩ : syracuseStep 3098117 = 580897) (by norm_num)
theorem B2065411 : Blo 2063435 2065411 := bstep (se 1 (by rfl) ⟨1549058, by rfl⟩ : syracuseStep 2065411 = 3098117) B3098117
theorem B3485389 : Blo 2063435 3485389 := bbase (se 3 (by rfl) ⟨653510, by rfl⟩ : syracuseStep 3485389 = 1307021) (by norm_num)
theorem B4647185 : Blo 2063435 4647185 := bstep (se 2 (by rfl) ⟨1742694, by rfl⟩ : syracuseStep 4647185 = 3485389) B3485389
theorem B3098123 : Blo 2063435 3098123 := bstep (se 1 (by rfl) ⟨2323592, by rfl⟩ : syracuseStep 3098123 = 4647185) B4647185
theorem B2065415 : Blo 2063435 2065415 := bstep (se 1 (by rfl) ⟨1549061, by rfl⟩ : syracuseStep 2065415 = 3098123) B3098123
theorem B2323597 : Blo 2063435 2323597 := bbase (se 3 (by rfl) ⟨435674, by rfl⟩ : syracuseStep 2323597 = 871349) (by norm_num)
theorem B3098129 : Blo 2063435 3098129 := bstep (se 2 (by rfl) ⟨1161798, by rfl⟩ : syracuseStep 3098129 = 2323597) B2323597
theorem B2065419 : Blo 2063435 2065419 := bstep (se 1 (by rfl) ⟨1549064, by rfl⟩ : syracuseStep 2065419 = 3098129) B3098129
theorem B6970805 : Blo 2063435 6970805 := bbase (se 5 (by rfl) ⟨326756, by rfl⟩ : syracuseStep 6970805 = 653513) (by norm_num)
theorem B4647203 : Blo 2063435 4647203 := bstep (se 1 (by rfl) ⟨3485402, by rfl⟩ : syracuseStep 4647203 = 6970805) B6970805
theorem B3098135 : Blo 2063435 3098135 := bstep (se 1 (by rfl) ⟨2323601, by rfl⟩ : syracuseStep 3098135 = 4647203) B4647203
theorem B2065423 : Blo 2063435 2065423 := bstep (se 1 (by rfl) ⟨1549067, by rfl⟩ : syracuseStep 2065423 = 3098135) B3098135
theorem B3098141 : Blo 2063435 3098141 := bbase (se 3 (by rfl) ⟨580901, by rfl⟩ : syracuseStep 3098141 = 1161803) (by norm_num)
theorem B2065427 : Blo 2063435 2065427 := bstep (se 1 (by rfl) ⟨1549070, by rfl⟩ : syracuseStep 2065427 = 3098141) B3098141
theorem B4647221 : Blo 2063435 4647221 := bbase (se 5 (by rfl) ⟨217838, by rfl⟩ : syracuseStep 4647221 = 435677) (by norm_num)
theorem B3098147 : Blo 2063435 3098147 := bstep (se 1 (by rfl) ⟨2323610, by rfl⟩ : syracuseStep 3098147 = 4647221) B4647221
theorem B2065431 : Blo 2063435 2065431 := bstep (se 1 (by rfl) ⟨1549073, by rfl⟩ : syracuseStep 2065431 = 3098147) B3098147
theorem B190780757 : Blo 2063435 190780757 := bbase (se 14 (by rfl) ⟨17466, by rfl⟩ : syracuseStep 190780757 = 34933) (by norm_num)
theorem B127187171 : Blo 2063435 127187171 := bstep (se 1 (by rfl) ⟨95390378, by rfl⟩ : syracuseStep 127187171 = 190780757) B190780757
theorem B84791447 : Blo 2063435 84791447 := bstep (se 1 (by rfl) ⟨63593585, by rfl⟩ : syracuseStep 84791447 = 127187171) B127187171
theorem B56527631 : Blo 2063435 56527631 := bstep (se 1 (by rfl) ⟨42395723, by rfl⟩ : syracuseStep 56527631 = 84791447) B84791447
theorem B37685087 : Blo 2063435 37685087 := bstep (se 1 (by rfl) ⟨28263815, by rfl⟩ : syracuseStep 37685087 = 56527631) B56527631
theorem B25123391 : Blo 2063435 25123391 := bstep (se 1 (by rfl) ⟨18842543, by rfl⟩ : syracuseStep 25123391 = 37685087) B37685087
theorem B16748927 : Blo 2063435 16748927 := bstep (se 1 (by rfl) ⟨12561695, by rfl⟩ : syracuseStep 16748927 = 25123391) B25123391
theorem B11165951 : Blo 2063435 11165951 := bstep (se 1 (by rfl) ⟨8374463, by rfl⟩ : syracuseStep 11165951 = 16748927) B16748927
theorem B29775869 : Blo 2063435 29775869 := bstep (se 3 (by rfl) ⟨5582975, by rfl⟩ : syracuseStep 29775869 = 11165951) B11165951
theorem B19850579 : Blo 2063435 19850579 := bstep (se 1 (by rfl) ⟨14887934, by rfl⟩ : syracuseStep 19850579 = 29775869) B29775869
theorem B13233719 : Blo 2063435 13233719 := bstep (se 1 (by rfl) ⟨9925289, by rfl⟩ : syracuseStep 13233719 = 19850579) B19850579
theorem B8822479 : Blo 2063435 8822479 := bstep (se 1 (by rfl) ⟨6616859, by rfl⟩ : syracuseStep 8822479 = 13233719) B13233719
theorem B11763305 : Blo 2063435 11763305 := bstep (se 2 (by rfl) ⟨4411239, by rfl⟩ : syracuseStep 11763305 = 8822479) B8822479
theorem B7842203 : Blo 2063435 7842203 := bstep (se 1 (by rfl) ⟨5881652, by rfl⟩ : syracuseStep 7842203 = 11763305) B11763305
theorem B5228135 : Blo 2063435 5228135 := bstep (se 1 (by rfl) ⟨3921101, by rfl⟩ : syracuseStep 5228135 = 7842203) B7842203
theorem B3485423 : Blo 2063435 3485423 := bstep (se 1 (by rfl) ⟨2614067, by rfl⟩ : syracuseStep 3485423 = 5228135) B5228135
theorem B2323615 : Blo 2063435 2323615 := bstep (se 1 (by rfl) ⟨1742711, by rfl⟩ : syracuseStep 2323615 = 3485423) B3485423
theorem B3098153 : Blo 2063435 3098153 := bstep (se 2 (by rfl) ⟨1161807, by rfl⟩ : syracuseStep 3098153 = 2323615) B2323615
theorem B2065435 : Blo 2063435 2065435 := bstep (se 1 (by rfl) ⟨1549076, by rfl⟩ : syracuseStep 2065435 = 3098153) B3098153
theorem C0 (j : ℕ) (h1 : 515858 ≤ j) (h2 : j ≤ 516358) : Blo 2063435 (4 * j + 3) := by
  interval_cases j
  · exact B2063435
  · exact B2063439
  · exact B2063443
  · exact B2063447
  · exact B2063451
  · exact B2063455
  · exact B2063459
  · exact B2063463
  · exact B2063467
  · exact B2063471
  · exact B2063475
  · exact B2063479
  · exact B2063483
  · exact B2063487
  · exact B2063491
  · exact B2063495
  · exact B2063499
  · exact B2063503
  · exact B2063507
  · exact B2063511
  · exact B2063515
  · exact B2063519
  · exact B2063523
  · exact B2063527
  · exact B2063531
  · exact B2063535
  · exact B2063539
  · exact B2063543
  · exact B2063547
  · exact B2063551
  · exact B2063555
  · exact B2063559
  · exact B2063563
  · exact B2063567
  · exact B2063571
  · exact B2063575
  · exact B2063579
  · exact B2063583
  · exact B2063587
  · exact B2063591
  · exact B2063595
  · exact B2063599
  · exact B2063603
  · exact B2063607
  · exact B2063611
  · exact B2063615
  · exact B2063619
  · exact B2063623
  · exact B2063627
  · exact B2063631
  · exact B2063635
  · exact B2063639
  · exact B2063643
  · exact B2063647
  · exact B2063651
  · exact B2063655
  · exact B2063659
  · exact B2063663
  · exact B2063667
  · exact B2063671
  · exact B2063675
  · exact B2063679
  · exact B2063683
  · exact B2063687
  · exact B2063691
  · exact B2063695
  · exact B2063699
  · exact B2063703
  · exact B2063707
  · exact B2063711
  · exact B2063715
  · exact B2063719
  · exact B2063723
  · exact B2063727
  · exact B2063731
  · exact B2063735
  · exact B2063739
  · exact B2063743
  · exact B2063747
  · exact B2063751
  · exact B2063755
  · exact B2063759
  · exact B2063763
  · exact B2063767
  · exact B2063771
  · exact B2063775
  · exact B2063779
  · exact B2063783
  · exact B2063787
  · exact B2063791
  · exact B2063795
  · exact B2063799
  · exact B2063803
  · exact B2063807
  · exact B2063811
  · exact B2063815
  · exact B2063819
  · exact B2063823
  · exact B2063827
  · exact B2063831
  · exact B2063835
  · exact B2063839
  · exact B2063843
  · exact B2063847
  · exact B2063851
  · exact B2063855
  · exact B2063859
  · exact B2063863
  · exact B2063867
  · exact B2063871
  · exact B2063875
  · exact B2063879
  · exact B2063883
  · exact B2063887
  · exact B2063891
  · exact B2063895
  · exact B2063899
  · exact B2063903
  · exact B2063907
  · exact B2063911
  · exact B2063915
  · exact B2063919
  · exact B2063923
  · exact B2063927
  · exact B2063931
  · exact B2063935
  · exact B2063939
  · exact B2063943
  · exact B2063947
  · exact B2063951
  · exact B2063955
  · exact B2063959
  · exact B2063963
  · exact B2063967
  · exact B2063971
  · exact B2063975
  · exact B2063979
  · exact B2063983
  · exact B2063987
  · exact B2063991
  · exact B2063995
  · exact B2063999
  · exact B2064003
  · exact B2064007
  · exact B2064011
  · exact B2064015
  · exact B2064019
  · exact B2064023
  · exact B2064027
  · exact B2064031
  · exact B2064035
  · exact B2064039
  · exact B2064043
  · exact B2064047
  · exact B2064051
  · exact B2064055
  · exact B2064059
  · exact B2064063
  · exact B2064067
  · exact B2064071
  · exact B2064075
  · exact B2064079
  · exact B2064083
  · exact B2064087
  · exact B2064091
  · exact B2064095
  · exact B2064099
  · exact B2064103
  · exact B2064107
  · exact B2064111
  · exact B2064115
  · exact B2064119
  · exact B2064123
  · exact B2064127
  · exact B2064131
  · exact B2064135
  · exact B2064139
  · exact B2064143
  · exact B2064147
  · exact B2064151
  · exact B2064155
  · exact B2064159
  · exact B2064163
  · exact B2064167
  · exact B2064171
  · exact B2064175
  · exact B2064179
  · exact B2064183
  · exact B2064187
  · exact B2064191
  · exact B2064195
  · exact B2064199
  · exact B2064203
  · exact B2064207
  · exact B2064211
  · exact B2064215
  · exact B2064219
  · exact B2064223
  · exact B2064227
  · exact B2064231
  · exact B2064235
  · exact B2064239
  · exact B2064243
  · exact B2064247
  · exact B2064251
  · exact B2064255
  · exact B2064259
  · exact B2064263
  · exact B2064267
  · exact B2064271
  · exact B2064275
  · exact B2064279
  · exact B2064283
  · exact B2064287
  · exact B2064291
  · exact B2064295
  · exact B2064299
  · exact B2064303
  · exact B2064307
  · exact B2064311
  · exact B2064315
  · exact B2064319
  · exact B2064323
  · exact B2064327
  · exact B2064331
  · exact B2064335
  · exact B2064339
  · exact B2064343
  · exact B2064347
  · exact B2064351
  · exact B2064355
  · exact B2064359
  · exact B2064363
  · exact B2064367
  · exact B2064371
  · exact B2064375
  · exact B2064379
  · exact B2064383
  · exact B2064387
  · exact B2064391
  · exact B2064395
  · exact B2064399
  · exact B2064403
  · exact B2064407
  · exact B2064411
  · exact B2064415
  · exact B2064419
  · exact B2064423
  · exact B2064427
  · exact B2064431
  · exact B2064435
  · exact B2064439
  · exact B2064443
  · exact B2064447
  · exact B2064451
  · exact B2064455
  · exact B2064459
  · exact B2064463
  · exact B2064467
  · exact B2064471
  · exact B2064475
  · exact B2064479
  · exact B2064483
  · exact B2064487
  · exact B2064491
  · exact B2064495
  · exact B2064499
  · exact B2064503
  · exact B2064507
  · exact B2064511
  · exact B2064515
  · exact B2064519
  · exact B2064523
  · exact B2064527
  · exact B2064531
  · exact B2064535
  · exact B2064539
  · exact B2064543
  · exact B2064547
  · exact B2064551
  · exact B2064555
  · exact B2064559
  · exact B2064563
  · exact B2064567
  · exact B2064571
  · exact B2064575
  · exact B2064579
  · exact B2064583
  · exact B2064587
  · exact B2064591
  · exact B2064595
  · exact B2064599
  · exact B2064603
  · exact B2064607
  · exact B2064611
  · exact B2064615
  · exact B2064619
  · exact B2064623
  · exact B2064627
  · exact B2064631
  · exact B2064635
  · exact B2064639
  · exact B2064643
  · exact B2064647
  · exact B2064651
  · exact B2064655
  · exact B2064659
  · exact B2064663
  · exact B2064667
  · exact B2064671
  · exact B2064675
  · exact B2064679
  · exact B2064683
  · exact B2064687
  · exact B2064691
  · exact B2064695
  · exact B2064699
  · exact B2064703
  · exact B2064707
  · exact B2064711
  · exact B2064715
  · exact B2064719
  · exact B2064723
  · exact B2064727
  · exact B2064731
  · exact B2064735
  · exact B2064739
  · exact B2064743
  · exact B2064747
  · exact B2064751
  · exact B2064755
  · exact B2064759
  · exact B2064763
  · exact B2064767
  · exact B2064771
  · exact B2064775
  · exact B2064779
  · exact B2064783
  · exact B2064787
  · exact B2064791
  · exact B2064795
  · exact B2064799
  · exact B2064803
  · exact B2064807
  · exact B2064811
  · exact B2064815
  · exact B2064819
  · exact B2064823
  · exact B2064827
  · exact B2064831
  · exact B2064835
  · exact B2064839
  · exact B2064843
  · exact B2064847
  · exact B2064851
  · exact B2064855
  · exact B2064859
  · exact B2064863
  · exact B2064867
  · exact B2064871
  · exact B2064875
  · exact B2064879
  · exact B2064883
  · exact B2064887
  · exact B2064891
  · exact B2064895
  · exact B2064899
  · exact B2064903
  · exact B2064907
  · exact B2064911
  · exact B2064915
  · exact B2064919
  · exact B2064923
  · exact B2064927
  · exact B2064931
  · exact B2064935
  · exact B2064939
  · exact B2064943
  · exact B2064947
  · exact B2064951
  · exact B2064955
  · exact B2064959
  · exact B2064963
  · exact B2064967
  · exact B2064971
  · exact B2064975
  · exact B2064979
  · exact B2064983
  · exact B2064987
  · exact B2064991
  · exact B2064995
  · exact B2064999
  · exact B2065003
  · exact B2065007
  · exact B2065011
  · exact B2065015
  · exact B2065019
  · exact B2065023
  · exact B2065027
  · exact B2065031
  · exact B2065035
  · exact B2065039
  · exact B2065043
  · exact B2065047
  · exact B2065051
  · exact B2065055
  · exact B2065059
  · exact B2065063
  · exact B2065067
  · exact B2065071
  · exact B2065075
  · exact B2065079
  · exact B2065083
  · exact B2065087
  · exact B2065091
  · exact B2065095
  · exact B2065099
  · exact B2065103
  · exact B2065107
  · exact B2065111
  · exact B2065115
  · exact B2065119
  · exact B2065123
  · exact B2065127
  · exact B2065131
  · exact B2065135
  · exact B2065139
  · exact B2065143
  · exact B2065147
  · exact B2065151
  · exact B2065155
  · exact B2065159
  · exact B2065163
  · exact B2065167
  · exact B2065171
  · exact B2065175
  · exact B2065179
  · exact B2065183
  · exact B2065187
  · exact B2065191
  · exact B2065195
  · exact B2065199
  · exact B2065203
  · exact B2065207
  · exact B2065211
  · exact B2065215
  · exact B2065219
  · exact B2065223
  · exact B2065227
  · exact B2065231
  · exact B2065235
  · exact B2065239
  · exact B2065243
  · exact B2065247
  · exact B2065251
  · exact B2065255
  · exact B2065259
  · exact B2065263
  · exact B2065267
  · exact B2065271
  · exact B2065275
  · exact B2065279
  · exact B2065283
  · exact B2065287
  · exact B2065291
  · exact B2065295
  · exact B2065299
  · exact B2065303
  · exact B2065307
  · exact B2065311
  · exact B2065315
  · exact B2065319
  · exact B2065323
  · exact B2065327
  · exact B2065331
  · exact B2065335
  · exact B2065339
  · exact B2065343
  · exact B2065347
  · exact B2065351
  · exact B2065355
  · exact B2065359
  · exact B2065363
  · exact B2065367
  · exact B2065371
  · exact B2065375
  · exact B2065379
  · exact B2065383
  · exact B2065387
  · exact B2065391
  · exact B2065395
  · exact B2065399
  · exact B2065403
  · exact B2065407
  · exact B2065411
  · exact B2065415
  · exact B2065419
  · exact B2065423
  · exact B2065427
  · exact B2065431
  · exact B2065435
theorem solution (m : ℕ) (hlo : 2063435 ≤ m) (hhi : m ≤ 2065435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 515858 ≤ j := by omega
    have hj2 : j ≤ 516358 := by omega
    have hb : Blo 2063435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
