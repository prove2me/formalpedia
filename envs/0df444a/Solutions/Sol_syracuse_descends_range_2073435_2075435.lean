-- Prove2me | solution 1 for syracuse_descends_range_2073435_2075435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:16:08.740519+00:00
-- url     : https://prove2.me/submissions/42d44ef5-b75a-4750-92e6-00d9593336d1

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

theorem B3321245 : Blo 2073435 3321245 := bbase (se 3 (by rfl) ⟨622733, by rfl⟩ : syracuseStep 3321245 = 1245467) (by norm_num)
theorem B2214163 : Blo 2073435 2214163 := bstep (se 1 (by rfl) ⟨1660622, by rfl⟩ : syracuseStep 2214163 = 3321245) B3321245
theorem B2952217 : Blo 2073435 2952217 := bstep (se 2 (by rfl) ⟨1107081, by rfl⟩ : syracuseStep 2952217 = 2214163) B2214163
theorem B3936289 : Blo 2073435 3936289 := bstep (se 2 (by rfl) ⟨1476108, by rfl⟩ : syracuseStep 3936289 = 2952217) B2952217
theorem B5248385 : Blo 2073435 5248385 := bstep (se 2 (by rfl) ⟨1968144, by rfl⟩ : syracuseStep 5248385 = 3936289) B3936289
theorem B3498923 : Blo 2073435 3498923 := bstep (se 1 (by rfl) ⟨2624192, by rfl⟩ : syracuseStep 3498923 = 5248385) B5248385
theorem B2332615 : Blo 2073435 2332615 := bstep (se 1 (by rfl) ⟨1749461, by rfl⟩ : syracuseStep 2332615 = 3498923) B3498923
theorem B3110153 : Blo 2073435 3110153 := bstep (se 2 (by rfl) ⟨1166307, by rfl⟩ : syracuseStep 3110153 = 2332615) B2332615
theorem B2073435 : Blo 2073435 2073435 := bstep (se 1 (by rfl) ⟨1555076, by rfl⟩ : syracuseStep 2073435 = 3110153) B3110153
theorem B10496789 : Blo 2073435 10496789 := bbase (se 6 (by rfl) ⟨246018, by rfl⟩ : syracuseStep 10496789 = 492037) (by norm_num)
theorem B6997859 : Blo 2073435 6997859 := bstep (se 1 (by rfl) ⟨5248394, by rfl⟩ : syracuseStep 6997859 = 10496789) B10496789
theorem B4665239 : Blo 2073435 4665239 := bstep (se 1 (by rfl) ⟨3498929, by rfl⟩ : syracuseStep 4665239 = 6997859) B6997859
theorem B3110159 : Blo 2073435 3110159 := bstep (se 1 (by rfl) ⟨2332619, by rfl⟩ : syracuseStep 3110159 = 4665239) B4665239
theorem B2073439 : Blo 2073435 2073439 := bstep (se 1 (by rfl) ⟨1555079, by rfl⟩ : syracuseStep 2073439 = 3110159) B3110159
theorem B3110165 : Blo 2073435 3110165 := bbase (se 6 (by rfl) ⟨72894, by rfl⟩ : syracuseStep 3110165 = 145789) (by norm_num)
theorem B2073443 : Blo 2073435 2073443 := bstep (se 1 (by rfl) ⟨1555082, by rfl⟩ : syracuseStep 2073443 = 3110165) B3110165
theorem B6391237 : Blo 2073435 6391237 := bbase (se 4 (by rfl) ⟨599178, by rfl⟩ : syracuseStep 6391237 = 1198357) (by norm_num)
theorem B8521649 : Blo 2073435 8521649 := bstep (se 2 (by rfl) ⟨3195618, by rfl⟩ : syracuseStep 8521649 = 6391237) B6391237
theorem B5681099 : Blo 2073435 5681099 := bstep (se 1 (by rfl) ⟨4260824, by rfl⟩ : syracuseStep 5681099 = 8521649) B8521649
theorem B3787399 : Blo 2073435 3787399 := bstep (se 1 (by rfl) ⟨2840549, by rfl⟩ : syracuseStep 3787399 = 5681099) B5681099
theorem B5049865 : Blo 2073435 5049865 := bstep (se 2 (by rfl) ⟨1893699, by rfl⟩ : syracuseStep 5049865 = 3787399) B3787399
theorem B6733153 : Blo 2073435 6733153 := bstep (se 2 (by rfl) ⟨2524932, by rfl⟩ : syracuseStep 6733153 = 5049865) B5049865
theorem B8977537 : Blo 2073435 8977537 := bstep (se 2 (by rfl) ⟨3366576, by rfl⟩ : syracuseStep 8977537 = 6733153) B6733153
theorem B47880197 : Blo 2073435 47880197 := bstep (se 4 (by rfl) ⟨4488768, by rfl⟩ : syracuseStep 47880197 = 8977537) B8977537
theorem B31920131 : Blo 2073435 31920131 := bstep (se 1 (by rfl) ⟨23940098, by rfl⟩ : syracuseStep 31920131 = 47880197) B47880197
theorem B21280087 : Blo 2073435 21280087 := bstep (se 1 (by rfl) ⟨15960065, by rfl⟩ : syracuseStep 21280087 = 31920131) B31920131
theorem B113493797 : Blo 2073435 113493797 := bstep (se 4 (by rfl) ⟨10640043, by rfl⟩ : syracuseStep 113493797 = 21280087) B21280087
theorem B75662531 : Blo 2073435 75662531 := bstep (se 1 (by rfl) ⟨56746898, by rfl⟩ : syracuseStep 75662531 = 113493797) B113493797
theorem B50441687 : Blo 2073435 50441687 := bstep (se 1 (by rfl) ⟨37831265, by rfl⟩ : syracuseStep 50441687 = 75662531) B75662531
theorem B33627791 : Blo 2073435 33627791 := bstep (se 1 (by rfl) ⟨25220843, by rfl⟩ : syracuseStep 33627791 = 50441687) B50441687
theorem B22418527 : Blo 2073435 22418527 := bstep (se 1 (by rfl) ⟨16813895, by rfl⟩ : syracuseStep 22418527 = 33627791) B33627791
theorem B29891369 : Blo 2073435 29891369 := bstep (se 2 (by rfl) ⟨11209263, by rfl⟩ : syracuseStep 29891369 = 22418527) B22418527
theorem B19927579 : Blo 2073435 19927579 := bstep (se 1 (by rfl) ⟨14945684, by rfl⟩ : syracuseStep 19927579 = 29891369) B29891369
theorem B26570105 : Blo 2073435 26570105 := bstep (se 2 (by rfl) ⟨9963789, by rfl⟩ : syracuseStep 26570105 = 19927579) B19927579
theorem B17713403 : Blo 2073435 17713403 := bstep (se 1 (by rfl) ⟨13285052, by rfl⟩ : syracuseStep 17713403 = 26570105) B26570105
theorem B11808935 : Blo 2073435 11808935 := bstep (se 1 (by rfl) ⟨8856701, by rfl⟩ : syracuseStep 11808935 = 17713403) B17713403
theorem B7872623 : Blo 2073435 7872623 := bstep (se 1 (by rfl) ⟨5904467, by rfl⟩ : syracuseStep 7872623 = 11808935) B11808935
theorem B5248415 : Blo 2073435 5248415 := bstep (se 1 (by rfl) ⟨3936311, by rfl⟩ : syracuseStep 5248415 = 7872623) B7872623
theorem B3498943 : Blo 2073435 3498943 := bstep (se 1 (by rfl) ⟨2624207, by rfl⟩ : syracuseStep 3498943 = 5248415) B5248415
theorem B4665257 : Blo 2073435 4665257 := bstep (se 2 (by rfl) ⟨1749471, by rfl⟩ : syracuseStep 4665257 = 3498943) B3498943
theorem B3110171 : Blo 2073435 3110171 := bstep (se 1 (by rfl) ⟨2332628, by rfl⟩ : syracuseStep 3110171 = 4665257) B4665257
theorem B2073447 : Blo 2073435 2073447 := bstep (se 1 (by rfl) ⟨1555085, by rfl⟩ : syracuseStep 2073447 = 3110171) B3110171
theorem B2332633 : Blo 2073435 2332633 := bbase (se 2 (by rfl) ⟨874737, by rfl⟩ : syracuseStep 2332633 = 1749475) (by norm_num)
theorem B3110177 : Blo 2073435 3110177 := bstep (se 2 (by rfl) ⟨1166316, by rfl⟩ : syracuseStep 3110177 = 2332633) B2332633
theorem B2073451 : Blo 2073435 2073451 := bstep (se 1 (by rfl) ⟨1555088, by rfl⟩ : syracuseStep 2073451 = 3110177) B3110177
theorem B2952245 : Blo 2073435 2952245 := bbase (se 5 (by rfl) ⟨138386, by rfl⟩ : syracuseStep 2952245 = 276773) (by norm_num)
theorem B7872653 : Blo 2073435 7872653 := bstep (se 3 (by rfl) ⟨1476122, by rfl⟩ : syracuseStep 7872653 = 2952245) B2952245
theorem B5248435 : Blo 2073435 5248435 := bstep (se 1 (by rfl) ⟨3936326, by rfl⟩ : syracuseStep 5248435 = 7872653) B7872653
theorem B6997913 : Blo 2073435 6997913 := bstep (se 2 (by rfl) ⟨2624217, by rfl⟩ : syracuseStep 6997913 = 5248435) B5248435
theorem B4665275 : Blo 2073435 4665275 := bstep (se 1 (by rfl) ⟨3498956, by rfl⟩ : syracuseStep 4665275 = 6997913) B6997913
theorem B3110183 : Blo 2073435 3110183 := bstep (se 1 (by rfl) ⟨2332637, by rfl⟩ : syracuseStep 3110183 = 4665275) B4665275
theorem B2073455 : Blo 2073435 2073455 := bstep (se 1 (by rfl) ⟨1555091, by rfl⟩ : syracuseStep 2073455 = 3110183) B3110183
theorem B3110189 : Blo 2073435 3110189 := bbase (se 3 (by rfl) ⟨583160, by rfl⟩ : syracuseStep 3110189 = 1166321) (by norm_num)
theorem B2073459 : Blo 2073435 2073459 := bstep (se 1 (by rfl) ⟨1555094, by rfl⟩ : syracuseStep 2073459 = 3110189) B3110189
theorem B4665293 : Blo 2073435 4665293 := bbase (se 3 (by rfl) ⟨874742, by rfl⟩ : syracuseStep 4665293 = 1749485) (by norm_num)
theorem B3110195 : Blo 2073435 3110195 := bstep (se 1 (by rfl) ⟨2332646, by rfl⟩ : syracuseStep 3110195 = 4665293) B4665293
theorem B2073463 : Blo 2073435 2073463 := bstep (se 1 (by rfl) ⟨1555097, by rfl⟩ : syracuseStep 2073463 = 3110195) B3110195
theorem B2624233 : Blo 2073435 2624233 := bbase (se 2 (by rfl) ⟨984087, by rfl⟩ : syracuseStep 2624233 = 1968175) (by norm_num)
theorem B3498977 : Blo 2073435 3498977 := bstep (se 2 (by rfl) ⟨1312116, by rfl⟩ : syracuseStep 3498977 = 2624233) B2624233
theorem B2332651 : Blo 2073435 2332651 := bstep (se 1 (by rfl) ⟨1749488, by rfl⟩ : syracuseStep 2332651 = 3498977) B3498977
theorem B3110201 : Blo 2073435 3110201 := bstep (se 2 (by rfl) ⟨1166325, by rfl⟩ : syracuseStep 3110201 = 2332651) B2332651
theorem B2073467 : Blo 2073435 2073467 := bstep (se 1 (by rfl) ⟨1555100, by rfl⟩ : syracuseStep 2073467 = 3110201) B3110201
theorem B13285205 : Blo 2073435 13285205 := bbase (se 9 (by rfl) ⟨38921, by rfl⟩ : syracuseStep 13285205 = 77843) (by norm_num)
theorem B8856803 : Blo 2073435 8856803 := bstep (se 1 (by rfl) ⟨6642602, by rfl⟩ : syracuseStep 8856803 = 13285205) B13285205
theorem B23618141 : Blo 2073435 23618141 := bstep (se 3 (by rfl) ⟨4428401, by rfl⟩ : syracuseStep 23618141 = 8856803) B8856803
theorem B15745427 : Blo 2073435 15745427 := bstep (se 1 (by rfl) ⟨11809070, by rfl⟩ : syracuseStep 15745427 = 23618141) B23618141
theorem B10496951 : Blo 2073435 10496951 := bstep (se 1 (by rfl) ⟨7872713, by rfl⟩ : syracuseStep 10496951 = 15745427) B15745427
theorem B6997967 : Blo 2073435 6997967 := bstep (se 1 (by rfl) ⟨5248475, by rfl⟩ : syracuseStep 6997967 = 10496951) B10496951
theorem B4665311 : Blo 2073435 4665311 := bstep (se 1 (by rfl) ⟨3498983, by rfl⟩ : syracuseStep 4665311 = 6997967) B6997967
theorem B3110207 : Blo 2073435 3110207 := bstep (se 1 (by rfl) ⟨2332655, by rfl⟩ : syracuseStep 3110207 = 4665311) B4665311
theorem B2073471 : Blo 2073435 2073471 := bstep (se 1 (by rfl) ⟨1555103, by rfl⟩ : syracuseStep 2073471 = 3110207) B3110207
theorem B3110213 : Blo 2073435 3110213 := bbase (se 4 (by rfl) ⟨291582, by rfl⟩ : syracuseStep 3110213 = 583165) (by norm_num)
theorem B2073475 : Blo 2073435 2073475 := bstep (se 1 (by rfl) ⟨1555106, by rfl⟩ : syracuseStep 2073475 = 3110213) B3110213
theorem B3498997 : Blo 2073435 3498997 := bbase (se 5 (by rfl) ⟨164015, by rfl⟩ : syracuseStep 3498997 = 328031) (by norm_num)
theorem B4665329 : Blo 2073435 4665329 := bstep (se 2 (by rfl) ⟨1749498, by rfl⟩ : syracuseStep 4665329 = 3498997) B3498997
theorem B3110219 : Blo 2073435 3110219 := bstep (se 1 (by rfl) ⟨2332664, by rfl⟩ : syracuseStep 3110219 = 4665329) B4665329
theorem B2073479 : Blo 2073435 2073479 := bstep (se 1 (by rfl) ⟨1555109, by rfl⟩ : syracuseStep 2073479 = 3110219) B3110219
theorem B2332669 : Blo 2073435 2332669 := bbase (se 3 (by rfl) ⟨437375, by rfl⟩ : syracuseStep 2332669 = 874751) (by norm_num)
theorem B3110225 : Blo 2073435 3110225 := bstep (se 2 (by rfl) ⟨1166334, by rfl⟩ : syracuseStep 3110225 = 2332669) B2332669
theorem B2073483 : Blo 2073435 2073483 := bstep (se 1 (by rfl) ⟨1555112, by rfl⟩ : syracuseStep 2073483 = 3110225) B3110225
theorem B6998021 : Blo 2073435 6998021 := bbase (se 4 (by rfl) ⟨656064, by rfl⟩ : syracuseStep 6998021 = 1312129) (by norm_num)
theorem B4665347 : Blo 2073435 4665347 := bstep (se 1 (by rfl) ⟨3499010, by rfl⟩ : syracuseStep 4665347 = 6998021) B6998021
theorem B3110231 : Blo 2073435 3110231 := bstep (se 1 (by rfl) ⟨2332673, by rfl⟩ : syracuseStep 3110231 = 4665347) B4665347
theorem B2073487 : Blo 2073435 2073487 := bstep (se 1 (by rfl) ⟨1555115, by rfl⟩ : syracuseStep 2073487 = 3110231) B3110231
theorem B3110237 : Blo 2073435 3110237 := bbase (se 3 (by rfl) ⟨583169, by rfl⟩ : syracuseStep 3110237 = 1166339) (by norm_num)
theorem B2073491 : Blo 2073435 2073491 := bstep (se 1 (by rfl) ⟨1555118, by rfl⟩ : syracuseStep 2073491 = 3110237) B3110237
theorem B4665365 : Blo 2073435 4665365 := bbase (se 6 (by rfl) ⟨109344, by rfl⟩ : syracuseStep 4665365 = 218689) (by norm_num)
theorem B3110243 : Blo 2073435 3110243 := bstep (se 1 (by rfl) ⟨2332682, by rfl⟩ : syracuseStep 3110243 = 4665365) B4665365
theorem B2073495 : Blo 2073435 2073495 := bstep (se 1 (by rfl) ⟨1555121, by rfl⟩ : syracuseStep 2073495 = 3110243) B3110243
theorem B7872821 : Blo 2073435 7872821 := bbase (se 5 (by rfl) ⟨369038, by rfl⟩ : syracuseStep 7872821 = 738077) (by norm_num)
theorem B5248547 : Blo 2073435 5248547 := bstep (se 1 (by rfl) ⟨3936410, by rfl⟩ : syracuseStep 5248547 = 7872821) B7872821
theorem B3499031 : Blo 2073435 3499031 := bstep (se 1 (by rfl) ⟨2624273, by rfl⟩ : syracuseStep 3499031 = 5248547) B5248547
theorem B2332687 : Blo 2073435 2332687 := bstep (se 1 (by rfl) ⟨1749515, by rfl⟩ : syracuseStep 2332687 = 3499031) B3499031
theorem B3110249 : Blo 2073435 3110249 := bstep (se 2 (by rfl) ⟨1166343, by rfl⟩ : syracuseStep 3110249 = 2332687) B2332687
theorem B2073499 : Blo 2073435 2073499 := bstep (se 1 (by rfl) ⟨1555124, by rfl⟩ : syracuseStep 2073499 = 3110249) B3110249
theorem B4203589 : Blo 2073435 4203589 := bbase (se 4 (by rfl) ⟨394086, by rfl⟩ : syracuseStep 4203589 = 788173) (by norm_num)
theorem B5604785 : Blo 2073435 5604785 := bstep (se 2 (by rfl) ⟨2101794, by rfl⟩ : syracuseStep 5604785 = 4203589) B4203589
theorem B3736523 : Blo 2073435 3736523 := bstep (se 1 (by rfl) ⟨2802392, by rfl⟩ : syracuseStep 3736523 = 5604785) B5604785
theorem B2491015 : Blo 2073435 2491015 := bstep (se 1 (by rfl) ⟨1868261, by rfl⟩ : syracuseStep 2491015 = 3736523) B3736523
theorem B3321353 : Blo 2073435 3321353 := bstep (se 2 (by rfl) ⟨1245507, by rfl⟩ : syracuseStep 3321353 = 2491015) B2491015
theorem B2214235 : Blo 2073435 2214235 := bstep (se 1 (by rfl) ⟨1660676, by rfl⟩ : syracuseStep 2214235 = 3321353) B3321353
theorem B11809253 : Blo 2073435 11809253 := bstep (se 4 (by rfl) ⟨1107117, by rfl⟩ : syracuseStep 11809253 = 2214235) B2214235
theorem B7872835 : Blo 2073435 7872835 := bstep (se 1 (by rfl) ⟨5904626, by rfl⟩ : syracuseStep 7872835 = 11809253) B11809253
theorem B10497113 : Blo 2073435 10497113 := bstep (se 2 (by rfl) ⟨3936417, by rfl⟩ : syracuseStep 10497113 = 7872835) B7872835
theorem B6998075 : Blo 2073435 6998075 := bstep (se 1 (by rfl) ⟨5248556, by rfl⟩ : syracuseStep 6998075 = 10497113) B10497113
theorem B4665383 : Blo 2073435 4665383 := bstep (se 1 (by rfl) ⟨3499037, by rfl⟩ : syracuseStep 4665383 = 6998075) B6998075
theorem B3110255 : Blo 2073435 3110255 := bstep (se 1 (by rfl) ⟨2332691, by rfl⟩ : syracuseStep 3110255 = 4665383) B4665383
theorem B2073503 : Blo 2073435 2073503 := bstep (se 1 (by rfl) ⟨1555127, by rfl⟩ : syracuseStep 2073503 = 3110255) B3110255
theorem B3110261 : Blo 2073435 3110261 := bbase (se 5 (by rfl) ⟨145793, by rfl⟩ : syracuseStep 3110261 = 291587) (by norm_num)
theorem B2073507 : Blo 2073435 2073507 := bstep (se 1 (by rfl) ⟨1555130, by rfl⟩ : syracuseStep 2073507 = 3110261) B3110261
theorem B2952325 : Blo 2073435 2952325 := bbase (se 4 (by rfl) ⟨276780, by rfl⟩ : syracuseStep 2952325 = 553561) (by norm_num)
theorem B3936433 : Blo 2073435 3936433 := bstep (se 2 (by rfl) ⟨1476162, by rfl⟩ : syracuseStep 3936433 = 2952325) B2952325
theorem B5248577 : Blo 2073435 5248577 := bstep (se 2 (by rfl) ⟨1968216, by rfl⟩ : syracuseStep 5248577 = 3936433) B3936433
theorem B3499051 : Blo 2073435 3499051 := bstep (se 1 (by rfl) ⟨2624288, by rfl⟩ : syracuseStep 3499051 = 5248577) B5248577
theorem B4665401 : Blo 2073435 4665401 := bstep (se 2 (by rfl) ⟨1749525, by rfl⟩ : syracuseStep 4665401 = 3499051) B3499051
theorem B3110267 : Blo 2073435 3110267 := bstep (se 1 (by rfl) ⟨2332700, by rfl⟩ : syracuseStep 3110267 = 4665401) B4665401
theorem B2073511 : Blo 2073435 2073511 := bstep (se 1 (by rfl) ⟨1555133, by rfl⟩ : syracuseStep 2073511 = 3110267) B3110267
theorem B2332705 : Blo 2073435 2332705 := bbase (se 2 (by rfl) ⟨874764, by rfl⟩ : syracuseStep 2332705 = 1749529) (by norm_num)
theorem B3110273 : Blo 2073435 3110273 := bstep (se 2 (by rfl) ⟨1166352, by rfl⟩ : syracuseStep 3110273 = 2332705) B2332705
theorem B2073515 : Blo 2073435 2073515 := bstep (se 1 (by rfl) ⟨1555136, by rfl⟩ : syracuseStep 2073515 = 3110273) B3110273
theorem B5248597 : Blo 2073435 5248597 := bbase (se 8 (by rfl) ⟨30753, by rfl⟩ : syracuseStep 5248597 = 61507) (by norm_num)
theorem B6998129 : Blo 2073435 6998129 := bstep (se 2 (by rfl) ⟨2624298, by rfl⟩ : syracuseStep 6998129 = 5248597) B5248597
theorem B4665419 : Blo 2073435 4665419 := bstep (se 1 (by rfl) ⟨3499064, by rfl⟩ : syracuseStep 4665419 = 6998129) B6998129
theorem B3110279 : Blo 2073435 3110279 := bstep (se 1 (by rfl) ⟨2332709, by rfl⟩ : syracuseStep 3110279 = 4665419) B4665419
theorem B2073519 : Blo 2073435 2073519 := bstep (se 1 (by rfl) ⟨1555139, by rfl⟩ : syracuseStep 2073519 = 3110279) B3110279
theorem B3110285 : Blo 2073435 3110285 := bbase (se 3 (by rfl) ⟨583178, by rfl⟩ : syracuseStep 3110285 = 1166357) (by norm_num)
theorem B2073523 : Blo 2073435 2073523 := bstep (se 1 (by rfl) ⟨1555142, by rfl⟩ : syracuseStep 2073523 = 3110285) B3110285
theorem B4665437 : Blo 2073435 4665437 := bbase (se 3 (by rfl) ⟨874769, by rfl⟩ : syracuseStep 4665437 = 1749539) (by norm_num)
theorem B3110291 : Blo 2073435 3110291 := bstep (se 1 (by rfl) ⟨2332718, by rfl⟩ : syracuseStep 3110291 = 4665437) B4665437
theorem B2073527 : Blo 2073435 2073527 := bstep (se 1 (by rfl) ⟨1555145, by rfl⟩ : syracuseStep 2073527 = 3110291) B3110291
theorem B3499085 : Blo 2073435 3499085 := bbase (se 3 (by rfl) ⟨656078, by rfl⟩ : syracuseStep 3499085 = 1312157) (by norm_num)
theorem B2332723 : Blo 2073435 2332723 := bstep (se 1 (by rfl) ⟨1749542, by rfl⟩ : syracuseStep 2332723 = 3499085) B3499085
theorem B3110297 : Blo 2073435 3110297 := bstep (se 2 (by rfl) ⟨1166361, by rfl⟩ : syracuseStep 3110297 = 2332723) B2332723
theorem B2073531 : Blo 2073435 2073531 := bstep (se 1 (by rfl) ⟨1555148, by rfl⟩ : syracuseStep 2073531 = 3110297) B3110297
theorem B7678469 : Blo 2073435 7678469 := bbase (se 4 (by rfl) ⟨719856, by rfl⟩ : syracuseStep 7678469 = 1439713) (by norm_num)
theorem B5118979 : Blo 2073435 5118979 := bstep (se 1 (by rfl) ⟨3839234, by rfl⟩ : syracuseStep 5118979 = 7678469) B7678469
theorem B6825305 : Blo 2073435 6825305 := bstep (se 2 (by rfl) ⟨2559489, by rfl⟩ : syracuseStep 6825305 = 5118979) B5118979
theorem B4550203 : Blo 2073435 4550203 := bstep (se 1 (by rfl) ⟨3412652, by rfl⟩ : syracuseStep 4550203 = 6825305) B6825305
theorem B6066937 : Blo 2073435 6066937 := bstep (se 2 (by rfl) ⟨2275101, by rfl⟩ : syracuseStep 6066937 = 4550203) B4550203
theorem B32356997 : Blo 2073435 32356997 := bstep (se 4 (by rfl) ⟨3033468, by rfl⟩ : syracuseStep 32356997 = 6066937) B6066937
theorem B21571331 : Blo 2073435 21571331 := bstep (se 1 (by rfl) ⟨16178498, by rfl⟩ : syracuseStep 21571331 = 32356997) B32356997
theorem B57523549 : Blo 2073435 57523549 := bstep (se 3 (by rfl) ⟨10785665, by rfl⟩ : syracuseStep 57523549 = 21571331) B21571331
theorem B76698065 : Blo 2073435 76698065 := bstep (se 2 (by rfl) ⟨28761774, by rfl⟩ : syracuseStep 76698065 = 57523549) B57523549
theorem B51132043 : Blo 2073435 51132043 := bstep (se 1 (by rfl) ⟨38349032, by rfl⟩ : syracuseStep 51132043 = 76698065) B76698065
theorem B272704229 : Blo 2073435 272704229 := bstep (se 4 (by rfl) ⟨25566021, by rfl⟩ : syracuseStep 272704229 = 51132043) B51132043
theorem B181802819 : Blo 2073435 181802819 := bstep (se 1 (by rfl) ⟨136352114, by rfl⟩ : syracuseStep 181802819 = 272704229) B272704229
theorem B484807517 : Blo 2073435 484807517 := bstep (se 3 (by rfl) ⟨90901409, by rfl⟩ : syracuseStep 484807517 = 181802819) B181802819
theorem B323205011 : Blo 2073435 323205011 := bstep (se 1 (by rfl) ⟨242403758, by rfl⟩ : syracuseStep 323205011 = 484807517) B484807517
theorem B215470007 : Blo 2073435 215470007 := bstep (se 1 (by rfl) ⟨161602505, by rfl⟩ : syracuseStep 215470007 = 323205011) B323205011
theorem B143646671 : Blo 2073435 143646671 := bstep (se 1 (by rfl) ⟨107735003, by rfl⟩ : syracuseStep 143646671 = 215470007) B215470007
theorem B95764447 : Blo 2073435 95764447 := bstep (se 1 (by rfl) ⟨71823335, by rfl⟩ : syracuseStep 95764447 = 143646671) B143646671
theorem B127685929 : Blo 2073435 127685929 := bstep (se 2 (by rfl) ⟨47882223, by rfl⟩ : syracuseStep 127685929 = 95764447) B95764447
theorem B170247905 : Blo 2073435 170247905 := bstep (se 2 (by rfl) ⟨63842964, by rfl⟩ : syracuseStep 170247905 = 127685929) B127685929
theorem B113498603 : Blo 2073435 113498603 := bstep (se 1 (by rfl) ⟨85123952, by rfl⟩ : syracuseStep 113498603 = 170247905) B170247905
theorem B75665735 : Blo 2073435 75665735 := bstep (se 1 (by rfl) ⟨56749301, by rfl⟩ : syracuseStep 75665735 = 113498603) B113498603
theorem B50443823 : Blo 2073435 50443823 := bstep (se 1 (by rfl) ⟨37832867, by rfl⟩ : syracuseStep 50443823 = 75665735) B75665735
theorem B33629215 : Blo 2073435 33629215 := bstep (se 1 (by rfl) ⟨25221911, by rfl⟩ : syracuseStep 33629215 = 50443823) B50443823
theorem B44838953 : Blo 2073435 44838953 := bstep (se 2 (by rfl) ⟨16814607, by rfl⟩ : syracuseStep 44838953 = 33629215) B33629215
theorem B29892635 : Blo 2073435 29892635 := bstep (se 1 (by rfl) ⟨22419476, by rfl⟩ : syracuseStep 29892635 = 44838953) B44838953
theorem B19928423 : Blo 2073435 19928423 := bstep (se 1 (by rfl) ⟨14946317, by rfl⟩ : syracuseStep 19928423 = 29892635) B29892635
theorem B13285615 : Blo 2073435 13285615 := bstep (se 1 (by rfl) ⟨9964211, by rfl⟩ : syracuseStep 13285615 = 19928423) B19928423
theorem B17714153 : Blo 2073435 17714153 := bstep (se 2 (by rfl) ⟨6642807, by rfl⟩ : syracuseStep 17714153 = 13285615) B13285615
theorem B11809435 : Blo 2073435 11809435 := bstep (se 1 (by rfl) ⟨8857076, by rfl⟩ : syracuseStep 11809435 = 17714153) B17714153
theorem B15745913 : Blo 2073435 15745913 := bstep (se 2 (by rfl) ⟨5904717, by rfl⟩ : syracuseStep 15745913 = 11809435) B11809435
theorem B10497275 : Blo 2073435 10497275 := bstep (se 1 (by rfl) ⟨7872956, by rfl⟩ : syracuseStep 10497275 = 15745913) B15745913
theorem B6998183 : Blo 2073435 6998183 := bstep (se 1 (by rfl) ⟨5248637, by rfl⟩ : syracuseStep 6998183 = 10497275) B10497275
theorem B4665455 : Blo 2073435 4665455 := bstep (se 1 (by rfl) ⟨3499091, by rfl⟩ : syracuseStep 4665455 = 6998183) B6998183
theorem B3110303 : Blo 2073435 3110303 := bstep (se 1 (by rfl) ⟨2332727, by rfl⟩ : syracuseStep 3110303 = 4665455) B4665455
theorem B2073535 : Blo 2073435 2073535 := bstep (se 1 (by rfl) ⟨1555151, by rfl⟩ : syracuseStep 2073535 = 3110303) B3110303
theorem B3110309 : Blo 2073435 3110309 := bbase (se 4 (by rfl) ⟨291591, by rfl⟩ : syracuseStep 3110309 = 583183) (by norm_num)
theorem B2073539 : Blo 2073435 2073539 := bstep (se 1 (by rfl) ⟨1555154, by rfl⟩ : syracuseStep 2073539 = 3110309) B3110309
theorem B2624329 : Blo 2073435 2624329 := bbase (se 2 (by rfl) ⟨984123, by rfl⟩ : syracuseStep 2624329 = 1968247) (by norm_num)
theorem B3499105 : Blo 2073435 3499105 := bstep (se 2 (by rfl) ⟨1312164, by rfl⟩ : syracuseStep 3499105 = 2624329) B2624329
theorem B4665473 : Blo 2073435 4665473 := bstep (se 2 (by rfl) ⟨1749552, by rfl⟩ : syracuseStep 4665473 = 3499105) B3499105
theorem B3110315 : Blo 2073435 3110315 := bstep (se 1 (by rfl) ⟨2332736, by rfl⟩ : syracuseStep 3110315 = 4665473) B4665473
theorem B2073543 : Blo 2073435 2073543 := bstep (se 1 (by rfl) ⟨1555157, by rfl⟩ : syracuseStep 2073543 = 3110315) B3110315
theorem B2332741 : Blo 2073435 2332741 := bbase (se 4 (by rfl) ⟨218694, by rfl⟩ : syracuseStep 2332741 = 437389) (by norm_num)
theorem B3110321 : Blo 2073435 3110321 := bstep (se 2 (by rfl) ⟨1166370, by rfl⟩ : syracuseStep 3110321 = 2332741) B2332741
theorem B2073547 : Blo 2073435 2073547 := bstep (se 1 (by rfl) ⟨1555160, by rfl⟩ : syracuseStep 2073547 = 3110321) B3110321
theorem B3936509 : Blo 2073435 3936509 := bbase (se 3 (by rfl) ⟨738095, by rfl⟩ : syracuseStep 3936509 = 1476191) (by norm_num)
theorem B2624339 : Blo 2073435 2624339 := bstep (se 1 (by rfl) ⟨1968254, by rfl⟩ : syracuseStep 2624339 = 3936509) B3936509
theorem B6998237 : Blo 2073435 6998237 := bstep (se 3 (by rfl) ⟨1312169, by rfl⟩ : syracuseStep 6998237 = 2624339) B2624339
theorem B4665491 : Blo 2073435 4665491 := bstep (se 1 (by rfl) ⟨3499118, by rfl⟩ : syracuseStep 4665491 = 6998237) B6998237
theorem B3110327 : Blo 2073435 3110327 := bstep (se 1 (by rfl) ⟨2332745, by rfl⟩ : syracuseStep 3110327 = 4665491) B4665491
theorem B2073551 : Blo 2073435 2073551 := bstep (se 1 (by rfl) ⟨1555163, by rfl⟩ : syracuseStep 2073551 = 3110327) B3110327
theorem B3110333 : Blo 2073435 3110333 := bbase (se 3 (by rfl) ⟨583187, by rfl⟩ : syracuseStep 3110333 = 1166375) (by norm_num)
theorem B2073555 : Blo 2073435 2073555 := bstep (se 1 (by rfl) ⟨1555166, by rfl⟩ : syracuseStep 2073555 = 3110333) B3110333
theorem B4665509 : Blo 2073435 4665509 := bbase (se 4 (by rfl) ⟨437391, by rfl⟩ : syracuseStep 4665509 = 874783) (by norm_num)
theorem B3110339 : Blo 2073435 3110339 := bstep (se 1 (by rfl) ⟨2332754, by rfl⟩ : syracuseStep 3110339 = 4665509) B4665509
theorem B2073559 : Blo 2073435 2073559 := bstep (se 1 (by rfl) ⟨1555169, by rfl⟩ : syracuseStep 2073559 = 3110339) B3110339
theorem B5248709 : Blo 2073435 5248709 := bbase (se 4 (by rfl) ⟨492066, by rfl⟩ : syracuseStep 5248709 = 984133) (by norm_num)
theorem B3499139 : Blo 2073435 3499139 := bstep (se 1 (by rfl) ⟨2624354, by rfl⟩ : syracuseStep 3499139 = 5248709) B5248709
theorem B2332759 : Blo 2073435 2332759 := bstep (se 1 (by rfl) ⟨1749569, by rfl⟩ : syracuseStep 2332759 = 3499139) B3499139
theorem B3110345 : Blo 2073435 3110345 := bstep (se 2 (by rfl) ⟨1166379, by rfl⟩ : syracuseStep 3110345 = 2332759) B2332759
theorem B2073563 : Blo 2073435 2073563 := bstep (se 1 (by rfl) ⟨1555172, by rfl⟩ : syracuseStep 2073563 = 3110345) B3110345
theorem B3366773 : Blo 2073435 3366773 := bbase (se 5 (by rfl) ⟨157817, by rfl⟩ : syracuseStep 3366773 = 315635) (by norm_num)
theorem B2244515 : Blo 2073435 2244515 := bstep (se 1 (by rfl) ⟨1683386, by rfl⟩ : syracuseStep 2244515 = 3366773) B3366773
theorem B5985373 : Blo 2073435 5985373 := bstep (se 3 (by rfl) ⟨1122257, by rfl⟩ : syracuseStep 5985373 = 2244515) B2244515
theorem B7980497 : Blo 2073435 7980497 := bstep (se 2 (by rfl) ⟨2992686, by rfl⟩ : syracuseStep 7980497 = 5985373) B5985373
theorem B5320331 : Blo 2073435 5320331 := bstep (se 1 (by rfl) ⟨3990248, by rfl⟩ : syracuseStep 5320331 = 7980497) B7980497
theorem B3546887 : Blo 2073435 3546887 := bstep (se 1 (by rfl) ⟨2660165, by rfl⟩ : syracuseStep 3546887 = 5320331) B5320331
theorem B9458365 : Blo 2073435 9458365 := bstep (se 3 (by rfl) ⟨1773443, by rfl⟩ : syracuseStep 9458365 = 3546887) B3546887
theorem B12611153 : Blo 2073435 12611153 := bstep (se 2 (by rfl) ⟨4729182, by rfl⟩ : syracuseStep 12611153 = 9458365) B9458365
theorem B33629741 : Blo 2073435 33629741 := bstep (se 3 (by rfl) ⟨6305576, by rfl⟩ : syracuseStep 33629741 = 12611153) B12611153
theorem B22419827 : Blo 2073435 22419827 := bstep (se 1 (by rfl) ⟨16814870, by rfl⟩ : syracuseStep 22419827 = 33629741) B33629741
theorem B14946551 : Blo 2073435 14946551 := bstep (se 1 (by rfl) ⟨11209913, by rfl⟩ : syracuseStep 14946551 = 22419827) B22419827
theorem B9964367 : Blo 2073435 9964367 := bstep (se 1 (by rfl) ⟨7473275, by rfl⟩ : syracuseStep 9964367 = 14946551) B14946551
theorem B6642911 : Blo 2073435 6642911 := bstep (se 1 (by rfl) ⟨4982183, by rfl⟩ : syracuseStep 6642911 = 9964367) B9964367
theorem B4428607 : Blo 2073435 4428607 := bstep (se 1 (by rfl) ⟨3321455, by rfl⟩ : syracuseStep 4428607 = 6642911) B6642911
theorem B5904809 : Blo 2073435 5904809 := bstep (se 2 (by rfl) ⟨2214303, by rfl⟩ : syracuseStep 5904809 = 4428607) B4428607
theorem B3936539 : Blo 2073435 3936539 := bstep (se 1 (by rfl) ⟨2952404, by rfl⟩ : syracuseStep 3936539 = 5904809) B5904809
theorem B10497437 : Blo 2073435 10497437 := bstep (se 3 (by rfl) ⟨1968269, by rfl⟩ : syracuseStep 10497437 = 3936539) B3936539
theorem B6998291 : Blo 2073435 6998291 := bstep (se 1 (by rfl) ⟨5248718, by rfl⟩ : syracuseStep 6998291 = 10497437) B10497437
theorem B4665527 : Blo 2073435 4665527 := bstep (se 1 (by rfl) ⟨3499145, by rfl⟩ : syracuseStep 4665527 = 6998291) B6998291
theorem B3110351 : Blo 2073435 3110351 := bstep (se 1 (by rfl) ⟨2332763, by rfl⟩ : syracuseStep 3110351 = 4665527) B4665527
theorem B2073567 : Blo 2073435 2073567 := bstep (se 1 (by rfl) ⟨1555175, by rfl⟩ : syracuseStep 2073567 = 3110351) B3110351
theorem B3110357 : Blo 2073435 3110357 := bbase (se 7 (by rfl) ⟨36449, by rfl⟩ : syracuseStep 3110357 = 72899) (by norm_num)
theorem B2073571 : Blo 2073435 2073571 := bstep (se 1 (by rfl) ⟨1555178, by rfl⟩ : syracuseStep 2073571 = 3110357) B3110357
theorem B7873109 : Blo 2073435 7873109 := bbase (se 8 (by rfl) ⟨46131, by rfl⟩ : syracuseStep 7873109 = 92263) (by norm_num)
theorem B5248739 : Blo 2073435 5248739 := bstep (se 1 (by rfl) ⟨3936554, by rfl⟩ : syracuseStep 5248739 = 7873109) B7873109
theorem B3499159 : Blo 2073435 3499159 := bstep (se 1 (by rfl) ⟨2624369, by rfl⟩ : syracuseStep 3499159 = 5248739) B5248739
theorem B4665545 : Blo 2073435 4665545 := bstep (se 2 (by rfl) ⟨1749579, by rfl⟩ : syracuseStep 4665545 = 3499159) B3499159
theorem B3110363 : Blo 2073435 3110363 := bstep (se 1 (by rfl) ⟨2332772, by rfl⟩ : syracuseStep 3110363 = 4665545) B4665545
theorem B2073575 : Blo 2073435 2073575 := bstep (se 1 (by rfl) ⟨1555181, by rfl⟩ : syracuseStep 2073575 = 3110363) B3110363
theorem B2332777 : Blo 2073435 2332777 := bbase (se 2 (by rfl) ⟨874791, by rfl⟩ : syracuseStep 2332777 = 1749583) (by norm_num)
theorem B3110369 : Blo 2073435 3110369 := bstep (se 2 (by rfl) ⟨1166388, by rfl⟩ : syracuseStep 3110369 = 2332777) B2332777
theorem B2073579 : Blo 2073435 2073579 := bstep (se 1 (by rfl) ⟨1555184, by rfl⟩ : syracuseStep 2073579 = 3110369) B3110369
theorem B2130553 : Blo 2073435 2130553 := bbase (se 2 (by rfl) ⟨798957, by rfl⟩ : syracuseStep 2130553 = 1597915) (by norm_num)
theorem B11362949 : Blo 2073435 11362949 := bstep (se 4 (by rfl) ⟨1065276, by rfl⟩ : syracuseStep 11362949 = 2130553) B2130553
theorem B7575299 : Blo 2073435 7575299 := bstep (se 1 (by rfl) ⟨5681474, by rfl⟩ : syracuseStep 7575299 = 11362949) B11362949
theorem B5050199 : Blo 2073435 5050199 := bstep (se 1 (by rfl) ⟨3787649, by rfl⟩ : syracuseStep 5050199 = 7575299) B7575299
theorem B13467197 : Blo 2073435 13467197 := bstep (se 3 (by rfl) ⟨2525099, by rfl⟩ : syracuseStep 13467197 = 5050199) B5050199
theorem B8978131 : Blo 2073435 8978131 := bstep (se 1 (by rfl) ⟨6733598, by rfl⟩ : syracuseStep 8978131 = 13467197) B13467197
theorem B11970841 : Blo 2073435 11970841 := bstep (se 2 (by rfl) ⟨4489065, by rfl⟩ : syracuseStep 11970841 = 8978131) B8978131
theorem B15961121 : Blo 2073435 15961121 := bstep (se 2 (by rfl) ⟨5985420, by rfl⟩ : syracuseStep 15961121 = 11970841) B11970841
theorem B10640747 : Blo 2073435 10640747 := bstep (se 1 (by rfl) ⟨7980560, by rfl⟩ : syracuseStep 10640747 = 15961121) B15961121
theorem B7093831 : Blo 2073435 7093831 := bstep (se 1 (by rfl) ⟨5320373, by rfl⟩ : syracuseStep 7093831 = 10640747) B10640747
theorem B9458441 : Blo 2073435 9458441 := bstep (se 2 (by rfl) ⟨3546915, by rfl⟩ : syracuseStep 9458441 = 7093831) B7093831
theorem B6305627 : Blo 2073435 6305627 := bstep (se 1 (by rfl) ⟨4729220, by rfl⟩ : syracuseStep 6305627 = 9458441) B9458441
theorem B4203751 : Blo 2073435 4203751 := bstep (se 1 (by rfl) ⟨3152813, by rfl⟩ : syracuseStep 4203751 = 6305627) B6305627
theorem B5605001 : Blo 2073435 5605001 := bstep (se 2 (by rfl) ⟨2101875, by rfl⟩ : syracuseStep 5605001 = 4203751) B4203751
theorem B3736667 : Blo 2073435 3736667 := bstep (se 1 (by rfl) ⟨2802500, by rfl⟩ : syracuseStep 3736667 = 5605001) B5605001
theorem B2491111 : Blo 2073435 2491111 := bstep (se 1 (by rfl) ⟨1868333, by rfl⟩ : syracuseStep 2491111 = 3736667) B3736667
theorem B3321481 : Blo 2073435 3321481 := bstep (se 2 (by rfl) ⟨1245555, by rfl⟩ : syracuseStep 3321481 = 2491111) B2491111
theorem B4428641 : Blo 2073435 4428641 := bstep (se 2 (by rfl) ⟨1660740, by rfl⟩ : syracuseStep 4428641 = 3321481) B3321481
theorem B11809709 : Blo 2073435 11809709 := bstep (se 3 (by rfl) ⟨2214320, by rfl⟩ : syracuseStep 11809709 = 4428641) B4428641
theorem B7873139 : Blo 2073435 7873139 := bstep (se 1 (by rfl) ⟨5904854, by rfl⟩ : syracuseStep 7873139 = 11809709) B11809709
theorem B5248759 : Blo 2073435 5248759 := bstep (se 1 (by rfl) ⟨3936569, by rfl⟩ : syracuseStep 5248759 = 7873139) B7873139
theorem B6998345 : Blo 2073435 6998345 := bstep (se 2 (by rfl) ⟨2624379, by rfl⟩ : syracuseStep 6998345 = 5248759) B5248759
theorem B4665563 : Blo 2073435 4665563 := bstep (se 1 (by rfl) ⟨3499172, by rfl⟩ : syracuseStep 4665563 = 6998345) B6998345
theorem B3110375 : Blo 2073435 3110375 := bstep (se 1 (by rfl) ⟨2332781, by rfl⟩ : syracuseStep 3110375 = 4665563) B4665563
theorem B2073583 : Blo 2073435 2073583 := bstep (se 1 (by rfl) ⟨1555187, by rfl⟩ : syracuseStep 2073583 = 3110375) B3110375
theorem B3110381 : Blo 2073435 3110381 := bbase (se 3 (by rfl) ⟨583196, by rfl⟩ : syracuseStep 3110381 = 1166393) (by norm_num)
theorem B2073587 : Blo 2073435 2073587 := bstep (se 1 (by rfl) ⟨1555190, by rfl⟩ : syracuseStep 2073587 = 3110381) B3110381
theorem B4665581 : Blo 2073435 4665581 := bbase (se 3 (by rfl) ⟨874796, by rfl⟩ : syracuseStep 4665581 = 1749593) (by norm_num)
theorem B3110387 : Blo 2073435 3110387 := bstep (se 1 (by rfl) ⟨2332790, by rfl⟩ : syracuseStep 3110387 = 4665581) B4665581
theorem B2073591 : Blo 2073435 2073591 := bstep (se 1 (by rfl) ⟨1555193, by rfl⟩ : syracuseStep 2073591 = 3110387) B3110387
theorem B2952445 : Blo 2073435 2952445 := bbase (se 3 (by rfl) ⟨553583, by rfl⟩ : syracuseStep 2952445 = 1107167) (by norm_num)
theorem B3936593 : Blo 2073435 3936593 := bstep (se 2 (by rfl) ⟨1476222, by rfl⟩ : syracuseStep 3936593 = 2952445) B2952445
theorem B2624395 : Blo 2073435 2624395 := bstep (se 1 (by rfl) ⟨1968296, by rfl⟩ : syracuseStep 2624395 = 3936593) B3936593
theorem B3499193 : Blo 2073435 3499193 := bstep (se 2 (by rfl) ⟨1312197, by rfl⟩ : syracuseStep 3499193 = 2624395) B2624395
theorem B2332795 : Blo 2073435 2332795 := bstep (se 1 (by rfl) ⟨1749596, by rfl⟩ : syracuseStep 2332795 = 3499193) B3499193
theorem B3110393 : Blo 2073435 3110393 := bstep (se 2 (by rfl) ⟨1166397, by rfl⟩ : syracuseStep 3110393 = 2332795) B2332795
theorem B2073595 : Blo 2073435 2073595 := bstep (se 1 (by rfl) ⟨1555196, by rfl⟩ : syracuseStep 2073595 = 3110393) B3110393
theorem B3152837 : Blo 2073435 3152837 := bbase (se 4 (by rfl) ⟨295578, by rfl⟩ : syracuseStep 3152837 = 591157) (by norm_num)
theorem B2101891 : Blo 2073435 2101891 := bstep (se 1 (by rfl) ⟨1576418, by rfl⟩ : syracuseStep 2101891 = 3152837) B3152837
theorem B2802521 : Blo 2073435 2802521 := bstep (se 2 (by rfl) ⟨1050945, by rfl⟩ : syracuseStep 2802521 = 2101891) B2101891
theorem B7473389 : Blo 2073435 7473389 := bstep (se 3 (by rfl) ⟨1401260, by rfl⟩ : syracuseStep 7473389 = 2802521) B2802521
theorem B79716149 : Blo 2073435 79716149 := bstep (se 5 (by rfl) ⟨3736694, by rfl⟩ : syracuseStep 79716149 = 7473389) B7473389
theorem B53144099 : Blo 2073435 53144099 := bstep (se 1 (by rfl) ⟨39858074, by rfl⟩ : syracuseStep 53144099 = 79716149) B79716149
theorem B35429399 : Blo 2073435 35429399 := bstep (se 1 (by rfl) ⟨26572049, by rfl⟩ : syracuseStep 35429399 = 53144099) B53144099
theorem B23619599 : Blo 2073435 23619599 := bstep (se 1 (by rfl) ⟨17714699, by rfl⟩ : syracuseStep 23619599 = 35429399) B35429399
theorem B15746399 : Blo 2073435 15746399 := bstep (se 1 (by rfl) ⟨11809799, by rfl⟩ : syracuseStep 15746399 = 23619599) B23619599
theorem B10497599 : Blo 2073435 10497599 := bstep (se 1 (by rfl) ⟨7873199, by rfl⟩ : syracuseStep 10497599 = 15746399) B15746399
theorem B6998399 : Blo 2073435 6998399 := bstep (se 1 (by rfl) ⟨5248799, by rfl⟩ : syracuseStep 6998399 = 10497599) B10497599
theorem B4665599 : Blo 2073435 4665599 := bstep (se 1 (by rfl) ⟨3499199, by rfl⟩ : syracuseStep 4665599 = 6998399) B6998399
theorem B3110399 : Blo 2073435 3110399 := bstep (se 1 (by rfl) ⟨2332799, by rfl⟩ : syracuseStep 3110399 = 4665599) B4665599
theorem B2073599 : Blo 2073435 2073599 := bstep (se 1 (by rfl) ⟨1555199, by rfl⟩ : syracuseStep 2073599 = 3110399) B3110399
theorem B3110405 : Blo 2073435 3110405 := bbase (se 4 (by rfl) ⟨291600, by rfl⟩ : syracuseStep 3110405 = 583201) (by norm_num)
theorem B2073603 : Blo 2073435 2073603 := bstep (se 1 (by rfl) ⟨1555202, by rfl⟩ : syracuseStep 2073603 = 3110405) B3110405
theorem B3499213 : Blo 2073435 3499213 := bbase (se 3 (by rfl) ⟨656102, by rfl⟩ : syracuseStep 3499213 = 1312205) (by norm_num)
theorem B4665617 : Blo 2073435 4665617 := bstep (se 2 (by rfl) ⟨1749606, by rfl⟩ : syracuseStep 4665617 = 3499213) B3499213
theorem B3110411 : Blo 2073435 3110411 := bstep (se 1 (by rfl) ⟨2332808, by rfl⟩ : syracuseStep 3110411 = 4665617) B4665617
theorem B2073607 : Blo 2073435 2073607 := bstep (se 1 (by rfl) ⟨1555205, by rfl⟩ : syracuseStep 2073607 = 3110411) B3110411
theorem B2332813 : Blo 2073435 2332813 := bbase (se 3 (by rfl) ⟨437402, by rfl⟩ : syracuseStep 2332813 = 874805) (by norm_num)
theorem B3110417 : Blo 2073435 3110417 := bstep (se 2 (by rfl) ⟨1166406, by rfl⟩ : syracuseStep 3110417 = 2332813) B2332813
theorem B2073611 : Blo 2073435 2073611 := bstep (se 1 (by rfl) ⟨1555208, by rfl⟩ : syracuseStep 2073611 = 3110417) B3110417
theorem B6998453 : Blo 2073435 6998453 := bbase (se 5 (by rfl) ⟨328052, by rfl⟩ : syracuseStep 6998453 = 656105) (by norm_num)
theorem B4665635 : Blo 2073435 4665635 := bstep (se 1 (by rfl) ⟨3499226, by rfl⟩ : syracuseStep 4665635 = 6998453) B6998453
theorem B3110423 : Blo 2073435 3110423 := bstep (se 1 (by rfl) ⟨2332817, by rfl⟩ : syracuseStep 3110423 = 4665635) B4665635
theorem B2073615 : Blo 2073435 2073615 := bstep (se 1 (by rfl) ⟨1555211, by rfl⟩ : syracuseStep 2073615 = 3110423) B3110423
theorem B3110429 : Blo 2073435 3110429 := bbase (se 3 (by rfl) ⟨583205, by rfl⟩ : syracuseStep 3110429 = 1166411) (by norm_num)
theorem B2073619 : Blo 2073435 2073619 := bstep (se 1 (by rfl) ⟨1555214, by rfl⟩ : syracuseStep 2073619 = 3110429) B3110429
theorem B4665653 : Blo 2073435 4665653 := bbase (se 5 (by rfl) ⟨218702, by rfl⟩ : syracuseStep 4665653 = 437405) (by norm_num)
theorem B3110435 : Blo 2073435 3110435 := bstep (se 1 (by rfl) ⟨2332826, by rfl⟩ : syracuseStep 3110435 = 4665653) B4665653
theorem B2073623 : Blo 2073435 2073623 := bstep (se 1 (by rfl) ⟨1555217, by rfl⟩ : syracuseStep 2073623 = 3110435) B3110435
theorem B3366869 : Blo 2073435 3366869 := bbase (se 7 (by rfl) ⟨39455, by rfl⟩ : syracuseStep 3366869 = 78911) (by norm_num)
theorem B35913269 : Blo 2073435 35913269 := bstep (se 5 (by rfl) ⟨1683434, by rfl⟩ : syracuseStep 35913269 = 3366869) B3366869
theorem B23942179 : Blo 2073435 23942179 := bstep (se 1 (by rfl) ⟨17956634, by rfl⟩ : syracuseStep 23942179 = 35913269) B35913269
theorem B31922905 : Blo 2073435 31922905 := bstep (se 2 (by rfl) ⟨11971089, by rfl⟩ : syracuseStep 31922905 = 23942179) B23942179
theorem B42563873 : Blo 2073435 42563873 := bstep (se 2 (by rfl) ⟨15961452, by rfl⟩ : syracuseStep 42563873 = 31922905) B31922905
theorem B28375915 : Blo 2073435 28375915 := bstep (se 1 (by rfl) ⟨21281936, by rfl⟩ : syracuseStep 28375915 = 42563873) B42563873
theorem B37834553 : Blo 2073435 37834553 := bstep (se 2 (by rfl) ⟨14187957, by rfl⟩ : syracuseStep 37834553 = 28375915) B28375915
theorem B100892141 : Blo 2073435 100892141 := bstep (se 3 (by rfl) ⟨18917276, by rfl⟩ : syracuseStep 100892141 = 37834553) B37834553
theorem B67261427 : Blo 2073435 67261427 := bstep (se 1 (by rfl) ⟨50446070, by rfl⟩ : syracuseStep 67261427 = 100892141) B100892141
theorem B44840951 : Blo 2073435 44840951 := bstep (se 1 (by rfl) ⟨33630713, by rfl⟩ : syracuseStep 44840951 = 67261427) B67261427
theorem B29893967 : Blo 2073435 29893967 := bstep (se 1 (by rfl) ⟨22420475, by rfl⟩ : syracuseStep 29893967 = 44840951) B44840951
theorem B19929311 : Blo 2073435 19929311 := bstep (se 1 (by rfl) ⟨14946983, by rfl⟩ : syracuseStep 19929311 = 29893967) B29893967
theorem B13286207 : Blo 2073435 13286207 := bstep (se 1 (by rfl) ⟨9964655, by rfl⟩ : syracuseStep 13286207 = 19929311) B19929311
theorem B8857471 : Blo 2073435 8857471 := bstep (se 1 (by rfl) ⟨6643103, by rfl⟩ : syracuseStep 8857471 = 13286207) B13286207
theorem B11809961 : Blo 2073435 11809961 := bstep (se 2 (by rfl) ⟨4428735, by rfl⟩ : syracuseStep 11809961 = 8857471) B8857471
theorem B7873307 : Blo 2073435 7873307 := bstep (se 1 (by rfl) ⟨5904980, by rfl⟩ : syracuseStep 7873307 = 11809961) B11809961
theorem B5248871 : Blo 2073435 5248871 := bstep (se 1 (by rfl) ⟨3936653, by rfl⟩ : syracuseStep 5248871 = 7873307) B7873307
theorem B3499247 : Blo 2073435 3499247 := bstep (se 1 (by rfl) ⟨2624435, by rfl⟩ : syracuseStep 3499247 = 5248871) B5248871
theorem B2332831 : Blo 2073435 2332831 := bstep (se 1 (by rfl) ⟨1749623, by rfl⟩ : syracuseStep 2332831 = 3499247) B3499247
theorem B3110441 : Blo 2073435 3110441 := bstep (se 2 (by rfl) ⟨1166415, by rfl⟩ : syracuseStep 3110441 = 2332831) B2332831
theorem B2073627 : Blo 2073435 2073627 := bstep (se 1 (by rfl) ⟨1555220, by rfl⟩ : syracuseStep 2073627 = 3110441) B3110441
theorem B10100629 : Blo 2073435 10100629 := bbase (se 6 (by rfl) ⟨236733, by rfl⟩ : syracuseStep 10100629 = 473467) (by norm_num)
theorem B13467505 : Blo 2073435 13467505 := bstep (se 2 (by rfl) ⟨5050314, by rfl⟩ : syracuseStep 13467505 = 10100629) B10100629
theorem B17956673 : Blo 2073435 17956673 := bstep (se 2 (by rfl) ⟨6733752, by rfl⟩ : syracuseStep 17956673 = 13467505) B13467505
theorem B11971115 : Blo 2073435 11971115 := bstep (se 1 (by rfl) ⟨8978336, by rfl⟩ : syracuseStep 11971115 = 17956673) B17956673
theorem B7980743 : Blo 2073435 7980743 := bstep (se 1 (by rfl) ⟨5985557, by rfl⟩ : syracuseStep 7980743 = 11971115) B11971115
theorem B5320495 : Blo 2073435 5320495 := bstep (se 1 (by rfl) ⟨3990371, by rfl⟩ : syracuseStep 5320495 = 7980743) B7980743
theorem B7093993 : Blo 2073435 7093993 := bstep (se 2 (by rfl) ⟨2660247, by rfl⟩ : syracuseStep 7093993 = 5320495) B5320495
theorem B9458657 : Blo 2073435 9458657 := bstep (se 2 (by rfl) ⟨3546996, by rfl⟩ : syracuseStep 9458657 = 7093993) B7093993
theorem B6305771 : Blo 2073435 6305771 := bstep (se 1 (by rfl) ⟨4729328, by rfl⟩ : syracuseStep 6305771 = 9458657) B9458657
theorem B4203847 : Blo 2073435 4203847 := bstep (se 1 (by rfl) ⟨3152885, by rfl⟩ : syracuseStep 4203847 = 6305771) B6305771
theorem B5605129 : Blo 2073435 5605129 := bstep (se 2 (by rfl) ⟨2101923, by rfl⟩ : syracuseStep 5605129 = 4203847) B4203847
theorem B29894021 : Blo 2073435 29894021 := bstep (se 4 (by rfl) ⟨2802564, by rfl⟩ : syracuseStep 29894021 = 5605129) B5605129
theorem B19929347 : Blo 2073435 19929347 := bstep (se 1 (by rfl) ⟨14947010, by rfl⟩ : syracuseStep 19929347 = 29894021) B29894021
theorem B13286231 : Blo 2073435 13286231 := bstep (se 1 (by rfl) ⟨9964673, by rfl⟩ : syracuseStep 13286231 = 19929347) B19929347
theorem B8857487 : Blo 2073435 8857487 := bstep (se 1 (by rfl) ⟨6643115, by rfl⟩ : syracuseStep 8857487 = 13286231) B13286231
theorem B5904991 : Blo 2073435 5904991 := bstep (se 1 (by rfl) ⟨4428743, by rfl⟩ : syracuseStep 5904991 = 8857487) B8857487
theorem B7873321 : Blo 2073435 7873321 := bstep (se 2 (by rfl) ⟨2952495, by rfl⟩ : syracuseStep 7873321 = 5904991) B5904991
theorem B10497761 : Blo 2073435 10497761 := bstep (se 2 (by rfl) ⟨3936660, by rfl⟩ : syracuseStep 10497761 = 7873321) B7873321
theorem B6998507 : Blo 2073435 6998507 := bstep (se 1 (by rfl) ⟨5248880, by rfl⟩ : syracuseStep 6998507 = 10497761) B10497761
theorem B4665671 : Blo 2073435 4665671 := bstep (se 1 (by rfl) ⟨3499253, by rfl⟩ : syracuseStep 4665671 = 6998507) B6998507
theorem B3110447 : Blo 2073435 3110447 := bstep (se 1 (by rfl) ⟨2332835, by rfl⟩ : syracuseStep 3110447 = 4665671) B4665671
theorem B2073631 : Blo 2073435 2073631 := bstep (se 1 (by rfl) ⟨1555223, by rfl⟩ : syracuseStep 2073631 = 3110447) B3110447
theorem B3110453 : Blo 2073435 3110453 := bbase (se 5 (by rfl) ⟨145802, by rfl⟩ : syracuseStep 3110453 = 291605) (by norm_num)
theorem B2073635 : Blo 2073435 2073635 := bstep (se 1 (by rfl) ⟨1555226, by rfl⟩ : syracuseStep 2073635 = 3110453) B3110453
theorem B5248901 : Blo 2073435 5248901 := bbase (se 4 (by rfl) ⟨492084, by rfl⟩ : syracuseStep 5248901 = 984169) (by norm_num)
theorem B3499267 : Blo 2073435 3499267 := bstep (se 1 (by rfl) ⟨2624450, by rfl⟩ : syracuseStep 3499267 = 5248901) B5248901
theorem B4665689 : Blo 2073435 4665689 := bstep (se 2 (by rfl) ⟨1749633, by rfl⟩ : syracuseStep 4665689 = 3499267) B3499267
theorem B3110459 : Blo 2073435 3110459 := bstep (se 1 (by rfl) ⟨2332844, by rfl⟩ : syracuseStep 3110459 = 4665689) B4665689
theorem B2073639 : Blo 2073435 2073639 := bstep (se 1 (by rfl) ⟨1555229, by rfl⟩ : syracuseStep 2073639 = 3110459) B3110459
theorem B2332849 : Blo 2073435 2332849 := bbase (se 2 (by rfl) ⟨874818, by rfl⟩ : syracuseStep 2332849 = 1749637) (by norm_num)
theorem B3110465 : Blo 2073435 3110465 := bstep (se 2 (by rfl) ⟨1166424, by rfl⟩ : syracuseStep 3110465 = 2332849) B2332849
theorem B2073643 : Blo 2073435 2073643 := bstep (se 1 (by rfl) ⟨1555232, by rfl⟩ : syracuseStep 2073643 = 3110465) B3110465
theorem B2214389 : Blo 2073435 2214389 := bbase (se 5 (by rfl) ⟨103799, by rfl⟩ : syracuseStep 2214389 = 207599) (by norm_num)
theorem B5905037 : Blo 2073435 5905037 := bstep (se 3 (by rfl) ⟨1107194, by rfl⟩ : syracuseStep 5905037 = 2214389) B2214389
theorem B3936691 : Blo 2073435 3936691 := bstep (se 1 (by rfl) ⟨2952518, by rfl⟩ : syracuseStep 3936691 = 5905037) B5905037
theorem B5248921 : Blo 2073435 5248921 := bstep (se 2 (by rfl) ⟨1968345, by rfl⟩ : syracuseStep 5248921 = 3936691) B3936691
theorem B6998561 : Blo 2073435 6998561 := bstep (se 2 (by rfl) ⟨2624460, by rfl⟩ : syracuseStep 6998561 = 5248921) B5248921
theorem B4665707 : Blo 2073435 4665707 := bstep (se 1 (by rfl) ⟨3499280, by rfl⟩ : syracuseStep 4665707 = 6998561) B6998561
theorem B3110471 : Blo 2073435 3110471 := bstep (se 1 (by rfl) ⟨2332853, by rfl⟩ : syracuseStep 3110471 = 4665707) B4665707
theorem B2073647 : Blo 2073435 2073647 := bstep (se 1 (by rfl) ⟨1555235, by rfl⟩ : syracuseStep 2073647 = 3110471) B3110471
theorem B3110477 : Blo 2073435 3110477 := bbase (se 3 (by rfl) ⟨583214, by rfl⟩ : syracuseStep 3110477 = 1166429) (by norm_num)
theorem B2073651 : Blo 2073435 2073651 := bstep (se 1 (by rfl) ⟨1555238, by rfl⟩ : syracuseStep 2073651 = 3110477) B3110477
theorem B4665725 : Blo 2073435 4665725 := bbase (se 3 (by rfl) ⟨874823, by rfl⟩ : syracuseStep 4665725 = 1749647) (by norm_num)
theorem B3110483 : Blo 2073435 3110483 := bstep (se 1 (by rfl) ⟨2332862, by rfl⟩ : syracuseStep 3110483 = 4665725) B4665725
theorem B2073655 : Blo 2073435 2073655 := bstep (se 1 (by rfl) ⟨1555241, by rfl⟩ : syracuseStep 2073655 = 3110483) B3110483
theorem B3499301 : Blo 2073435 3499301 := bbase (se 4 (by rfl) ⟨328059, by rfl⟩ : syracuseStep 3499301 = 656119) (by norm_num)
theorem B2332867 : Blo 2073435 2332867 := bstep (se 1 (by rfl) ⟨1749650, by rfl⟩ : syracuseStep 2332867 = 3499301) B3499301
theorem B3110489 : Blo 2073435 3110489 := bstep (se 2 (by rfl) ⟨1166433, by rfl⟩ : syracuseStep 3110489 = 2332867) B2332867
theorem B2073659 : Blo 2073435 2073659 := bstep (se 1 (by rfl) ⟨1555244, by rfl⟩ : syracuseStep 2073659 = 3110489) B3110489
theorem B2952541 : Blo 2073435 2952541 := bbase (se 3 (by rfl) ⟨553601, by rfl⟩ : syracuseStep 2952541 = 1107203) (by norm_num)
theorem B15746885 : Blo 2073435 15746885 := bstep (se 4 (by rfl) ⟨1476270, by rfl⟩ : syracuseStep 15746885 = 2952541) B2952541
theorem B10497923 : Blo 2073435 10497923 := bstep (se 1 (by rfl) ⟨7873442, by rfl⟩ : syracuseStep 10497923 = 15746885) B15746885
theorem B6998615 : Blo 2073435 6998615 := bstep (se 1 (by rfl) ⟨5248961, by rfl⟩ : syracuseStep 6998615 = 10497923) B10497923
theorem B4665743 : Blo 2073435 4665743 := bstep (se 1 (by rfl) ⟨3499307, by rfl⟩ : syracuseStep 4665743 = 6998615) B6998615
theorem B3110495 : Blo 2073435 3110495 := bstep (se 1 (by rfl) ⟨2332871, by rfl⟩ : syracuseStep 3110495 = 4665743) B4665743
theorem B2073663 : Blo 2073435 2073663 := bstep (se 1 (by rfl) ⟨1555247, by rfl⟩ : syracuseStep 2073663 = 3110495) B3110495
theorem B3110501 : Blo 2073435 3110501 := bbase (se 4 (by rfl) ⟨291609, by rfl⟩ : syracuseStep 3110501 = 583219) (by norm_num)
theorem B2073667 : Blo 2073435 2073667 := bstep (se 1 (by rfl) ⟨1555250, by rfl⟩ : syracuseStep 2073667 = 3110501) B3110501
theorem B7473653 : Blo 2073435 7473653 := bbase (se 5 (by rfl) ⟨350327, by rfl⟩ : syracuseStep 7473653 = 700655) (by norm_num)
theorem B4982435 : Blo 2073435 4982435 := bstep (se 1 (by rfl) ⟨3736826, by rfl⟩ : syracuseStep 4982435 = 7473653) B7473653
theorem B3321623 : Blo 2073435 3321623 := bstep (se 1 (by rfl) ⟨2491217, by rfl⟩ : syracuseStep 3321623 = 4982435) B4982435
theorem B2214415 : Blo 2073435 2214415 := bstep (se 1 (by rfl) ⟨1660811, by rfl⟩ : syracuseStep 2214415 = 3321623) B3321623
theorem B2952553 : Blo 2073435 2952553 := bstep (se 2 (by rfl) ⟨1107207, by rfl⟩ : syracuseStep 2952553 = 2214415) B2214415
theorem B3936737 : Blo 2073435 3936737 := bstep (se 2 (by rfl) ⟨1476276, by rfl⟩ : syracuseStep 3936737 = 2952553) B2952553
theorem B2624491 : Blo 2073435 2624491 := bstep (se 1 (by rfl) ⟨1968368, by rfl⟩ : syracuseStep 2624491 = 3936737) B3936737
theorem B3499321 : Blo 2073435 3499321 := bstep (se 2 (by rfl) ⟨1312245, by rfl⟩ : syracuseStep 3499321 = 2624491) B2624491
theorem B4665761 : Blo 2073435 4665761 := bstep (se 2 (by rfl) ⟨1749660, by rfl⟩ : syracuseStep 4665761 = 3499321) B3499321
theorem B3110507 : Blo 2073435 3110507 := bstep (se 1 (by rfl) ⟨2332880, by rfl⟩ : syracuseStep 3110507 = 4665761) B4665761
theorem B2073671 : Blo 2073435 2073671 := bstep (se 1 (by rfl) ⟨1555253, by rfl⟩ : syracuseStep 2073671 = 3110507) B3110507
theorem B2332885 : Blo 2073435 2332885 := bbase (se 7 (by rfl) ⟨27338, by rfl⟩ : syracuseStep 2332885 = 54677) (by norm_num)
theorem B3110513 : Blo 2073435 3110513 := bstep (se 2 (by rfl) ⟨1166442, by rfl⟩ : syracuseStep 3110513 = 2332885) B2332885
theorem B2073675 : Blo 2073435 2073675 := bstep (se 1 (by rfl) ⟨1555256, by rfl⟩ : syracuseStep 2073675 = 3110513) B3110513
theorem B2624501 : Blo 2073435 2624501 := bbase (se 5 (by rfl) ⟨123023, by rfl⟩ : syracuseStep 2624501 = 246047) (by norm_num)
theorem B6998669 : Blo 2073435 6998669 := bstep (se 3 (by rfl) ⟨1312250, by rfl⟩ : syracuseStep 6998669 = 2624501) B2624501
theorem B4665779 : Blo 2073435 4665779 := bstep (se 1 (by rfl) ⟨3499334, by rfl⟩ : syracuseStep 4665779 = 6998669) B6998669
theorem B3110519 : Blo 2073435 3110519 := bstep (se 1 (by rfl) ⟨2332889, by rfl⟩ : syracuseStep 3110519 = 4665779) B4665779
theorem B2073679 : Blo 2073435 2073679 := bstep (se 1 (by rfl) ⟨1555259, by rfl⟩ : syracuseStep 2073679 = 3110519) B3110519
theorem B3110525 : Blo 2073435 3110525 := bbase (se 3 (by rfl) ⟨583223, by rfl⟩ : syracuseStep 3110525 = 1166447) (by norm_num)
theorem B2073683 : Blo 2073435 2073683 := bstep (se 1 (by rfl) ⟨1555262, by rfl⟩ : syracuseStep 2073683 = 3110525) B3110525
theorem B4665797 : Blo 2073435 4665797 := bbase (se 4 (by rfl) ⟨437418, by rfl⟩ : syracuseStep 4665797 = 874837) (by norm_num)
theorem B3110531 : Blo 2073435 3110531 := bstep (se 1 (by rfl) ⟨2332898, by rfl⟩ : syracuseStep 3110531 = 4665797) B4665797
theorem B2073687 : Blo 2073435 2073687 := bstep (se 1 (by rfl) ⟨1555265, by rfl⟩ : syracuseStep 2073687 = 3110531) B3110531
theorem B2491241 : Blo 2073435 2491241 := bbase (se 2 (by rfl) ⟨934215, by rfl⟩ : syracuseStep 2491241 = 1868431) (by norm_num)
theorem B6643309 : Blo 2073435 6643309 := bstep (se 3 (by rfl) ⟨1245620, by rfl⟩ : syracuseStep 6643309 = 2491241) B2491241
theorem B8857745 : Blo 2073435 8857745 := bstep (se 2 (by rfl) ⟨3321654, by rfl⟩ : syracuseStep 8857745 = 6643309) B6643309
theorem B5905163 : Blo 2073435 5905163 := bstep (se 1 (by rfl) ⟨4428872, by rfl⟩ : syracuseStep 5905163 = 8857745) B8857745
theorem B3936775 : Blo 2073435 3936775 := bstep (se 1 (by rfl) ⟨2952581, by rfl⟩ : syracuseStep 3936775 = 5905163) B5905163
theorem B5249033 : Blo 2073435 5249033 := bstep (se 2 (by rfl) ⟨1968387, by rfl⟩ : syracuseStep 5249033 = 3936775) B3936775
theorem B3499355 : Blo 2073435 3499355 := bstep (se 1 (by rfl) ⟨2624516, by rfl⟩ : syracuseStep 3499355 = 5249033) B5249033
theorem B2332903 : Blo 2073435 2332903 := bstep (se 1 (by rfl) ⟨1749677, by rfl⟩ : syracuseStep 2332903 = 3499355) B3499355
theorem B3110537 : Blo 2073435 3110537 := bstep (se 2 (by rfl) ⟨1166451, by rfl⟩ : syracuseStep 3110537 = 2332903) B2332903
theorem B2073691 : Blo 2073435 2073691 := bstep (se 1 (by rfl) ⟨1555268, by rfl⟩ : syracuseStep 2073691 = 3110537) B3110537
theorem B10498085 : Blo 2073435 10498085 := bbase (se 4 (by rfl) ⟨984195, by rfl⟩ : syracuseStep 10498085 = 1968391) (by norm_num)
theorem B6998723 : Blo 2073435 6998723 := bstep (se 1 (by rfl) ⟨5249042, by rfl⟩ : syracuseStep 6998723 = 10498085) B10498085
theorem B4665815 : Blo 2073435 4665815 := bstep (se 1 (by rfl) ⟨3499361, by rfl⟩ : syracuseStep 4665815 = 6998723) B6998723
theorem B3110543 : Blo 2073435 3110543 := bstep (se 1 (by rfl) ⟨2332907, by rfl⟩ : syracuseStep 3110543 = 4665815) B4665815
theorem B2073695 : Blo 2073435 2073695 := bstep (se 1 (by rfl) ⟨1555271, by rfl⟩ : syracuseStep 2073695 = 3110543) B3110543
theorem B3110549 : Blo 2073435 3110549 := bbase (se 6 (by rfl) ⟨72903, by rfl⟩ : syracuseStep 3110549 = 145807) (by norm_num)
theorem B2073699 : Blo 2073435 2073699 := bstep (se 1 (by rfl) ⟨1555274, by rfl⟩ : syracuseStep 2073699 = 3110549) B3110549
theorem B2101997 : Blo 2073435 2101997 := bbase (se 3 (by rfl) ⟨394124, by rfl⟩ : syracuseStep 2101997 = 788249) (by norm_num)
theorem B5605325 : Blo 2073435 5605325 := bstep (se 3 (by rfl) ⟨1050998, by rfl⟩ : syracuseStep 5605325 = 2101997) B2101997
theorem B3736883 : Blo 2073435 3736883 := bstep (se 1 (by rfl) ⟨2802662, by rfl⟩ : syracuseStep 3736883 = 5605325) B5605325
theorem B2491255 : Blo 2073435 2491255 := bstep (se 1 (by rfl) ⟨1868441, by rfl⟩ : syracuseStep 2491255 = 3736883) B3736883
theorem B13286693 : Blo 2073435 13286693 := bstep (se 4 (by rfl) ⟨1245627, by rfl⟩ : syracuseStep 13286693 = 2491255) B2491255
theorem B8857795 : Blo 2073435 8857795 := bstep (se 1 (by rfl) ⟨6643346, by rfl⟩ : syracuseStep 8857795 = 13286693) B13286693
theorem B11810393 : Blo 2073435 11810393 := bstep (se 2 (by rfl) ⟨4428897, by rfl⟩ : syracuseStep 11810393 = 8857795) B8857795
theorem B7873595 : Blo 2073435 7873595 := bstep (se 1 (by rfl) ⟨5905196, by rfl⟩ : syracuseStep 7873595 = 11810393) B11810393
theorem B5249063 : Blo 2073435 5249063 := bstep (se 1 (by rfl) ⟨3936797, by rfl⟩ : syracuseStep 5249063 = 7873595) B7873595
theorem B3499375 : Blo 2073435 3499375 := bstep (se 1 (by rfl) ⟨2624531, by rfl⟩ : syracuseStep 3499375 = 5249063) B5249063
theorem B4665833 : Blo 2073435 4665833 := bstep (se 2 (by rfl) ⟨1749687, by rfl⟩ : syracuseStep 4665833 = 3499375) B3499375
theorem B3110555 : Blo 2073435 3110555 := bstep (se 1 (by rfl) ⟨2332916, by rfl⟩ : syracuseStep 3110555 = 4665833) B4665833
theorem B2073703 : Blo 2073435 2073703 := bstep (se 1 (by rfl) ⟨1555277, by rfl⟩ : syracuseStep 2073703 = 3110555) B3110555
theorem B2332921 : Blo 2073435 2332921 := bbase (se 2 (by rfl) ⟨874845, by rfl⟩ : syracuseStep 2332921 = 1749691) (by norm_num)
theorem B3110561 : Blo 2073435 3110561 := bstep (se 2 (by rfl) ⟨1166460, by rfl⟩ : syracuseStep 3110561 = 2332921) B2332921
theorem B2073707 : Blo 2073435 2073707 := bstep (se 1 (by rfl) ⟨1555280, by rfl⟩ : syracuseStep 2073707 = 3110561) B3110561
theorem B8857829 : Blo 2073435 8857829 := bbase (se 4 (by rfl) ⟨830421, by rfl⟩ : syracuseStep 8857829 = 1660843) (by norm_num)
theorem B5905219 : Blo 2073435 5905219 := bstep (se 1 (by rfl) ⟨4428914, by rfl⟩ : syracuseStep 5905219 = 8857829) B8857829
theorem B7873625 : Blo 2073435 7873625 := bstep (se 2 (by rfl) ⟨2952609, by rfl⟩ : syracuseStep 7873625 = 5905219) B5905219
theorem B5249083 : Blo 2073435 5249083 := bstep (se 1 (by rfl) ⟨3936812, by rfl⟩ : syracuseStep 5249083 = 7873625) B7873625
theorem B6998777 : Blo 2073435 6998777 := bstep (se 2 (by rfl) ⟨2624541, by rfl⟩ : syracuseStep 6998777 = 5249083) B5249083
theorem B4665851 : Blo 2073435 4665851 := bstep (se 1 (by rfl) ⟨3499388, by rfl⟩ : syracuseStep 4665851 = 6998777) B6998777
theorem B3110567 : Blo 2073435 3110567 := bstep (se 1 (by rfl) ⟨2332925, by rfl⟩ : syracuseStep 3110567 = 4665851) B4665851
theorem B2073711 : Blo 2073435 2073711 := bstep (se 1 (by rfl) ⟨1555283, by rfl⟩ : syracuseStep 2073711 = 3110567) B3110567
theorem B3110573 : Blo 2073435 3110573 := bbase (se 3 (by rfl) ⟨583232, by rfl⟩ : syracuseStep 3110573 = 1166465) (by norm_num)
theorem B2073715 : Blo 2073435 2073715 := bstep (se 1 (by rfl) ⟨1555286, by rfl⟩ : syracuseStep 2073715 = 3110573) B3110573
theorem B4665869 : Blo 2073435 4665869 := bbase (se 3 (by rfl) ⟨874850, by rfl⟩ : syracuseStep 4665869 = 1749701) (by norm_num)
theorem B3110579 : Blo 2073435 3110579 := bstep (se 1 (by rfl) ⟨2332934, by rfl⟩ : syracuseStep 3110579 = 4665869) B4665869
theorem B2073719 : Blo 2073435 2073719 := bstep (se 1 (by rfl) ⟨1555289, by rfl⟩ : syracuseStep 2073719 = 3110579) B3110579
theorem B2624557 : Blo 2073435 2624557 := bbase (se 3 (by rfl) ⟨492104, by rfl⟩ : syracuseStep 2624557 = 984209) (by norm_num)
theorem B3499409 : Blo 2073435 3499409 := bstep (se 2 (by rfl) ⟨1312278, by rfl⟩ : syracuseStep 3499409 = 2624557) B2624557
theorem B2332939 : Blo 2073435 2332939 := bstep (se 1 (by rfl) ⟨1749704, by rfl⟩ : syracuseStep 2332939 = 3499409) B3499409
theorem B3110585 : Blo 2073435 3110585 := bstep (se 2 (by rfl) ⟨1166469, by rfl⟩ : syracuseStep 3110585 = 2332939) B2332939
theorem B2073723 : Blo 2073435 2073723 := bstep (se 1 (by rfl) ⟨1555292, by rfl⟩ : syracuseStep 2073723 = 3110585) B3110585
theorem B5320741 : Blo 2073435 5320741 := bbase (se 4 (by rfl) ⟨498819, by rfl⟩ : syracuseStep 5320741 = 997639) (by norm_num)
theorem B7094321 : Blo 2073435 7094321 := bstep (se 2 (by rfl) ⟨2660370, by rfl⟩ : syracuseStep 7094321 = 5320741) B5320741
theorem B4729547 : Blo 2073435 4729547 := bstep (se 1 (by rfl) ⟨3547160, by rfl⟩ : syracuseStep 4729547 = 7094321) B7094321
theorem B12612125 : Blo 2073435 12612125 := bstep (se 3 (by rfl) ⟨2364773, by rfl⟩ : syracuseStep 12612125 = 4729547) B4729547
theorem B8408083 : Blo 2073435 8408083 := bstep (se 1 (by rfl) ⟨6306062, by rfl⟩ : syracuseStep 8408083 = 12612125) B12612125
theorem B11210777 : Blo 2073435 11210777 := bstep (se 2 (by rfl) ⟨4204041, by rfl⟩ : syracuseStep 11210777 = 8408083) B8408083
theorem B7473851 : Blo 2073435 7473851 := bstep (se 1 (by rfl) ⟨5605388, by rfl⟩ : syracuseStep 7473851 = 11210777) B11210777
theorem B4982567 : Blo 2073435 4982567 := bstep (se 1 (by rfl) ⟨3736925, by rfl⟩ : syracuseStep 4982567 = 7473851) B7473851
theorem B13286845 : Blo 2073435 13286845 := bstep (se 3 (by rfl) ⟨2491283, by rfl⟩ : syracuseStep 13286845 = 4982567) B4982567
theorem B17715793 : Blo 2073435 17715793 := bstep (se 2 (by rfl) ⟨6643422, by rfl⟩ : syracuseStep 17715793 = 13286845) B13286845
theorem B23621057 : Blo 2073435 23621057 := bstep (se 2 (by rfl) ⟨8857896, by rfl⟩ : syracuseStep 23621057 = 17715793) B17715793
theorem B15747371 : Blo 2073435 15747371 := bstep (se 1 (by rfl) ⟨11810528, by rfl⟩ : syracuseStep 15747371 = 23621057) B23621057
theorem B10498247 : Blo 2073435 10498247 := bstep (se 1 (by rfl) ⟨7873685, by rfl⟩ : syracuseStep 10498247 = 15747371) B15747371
theorem B6998831 : Blo 2073435 6998831 := bstep (se 1 (by rfl) ⟨5249123, by rfl⟩ : syracuseStep 6998831 = 10498247) B10498247
theorem B4665887 : Blo 2073435 4665887 := bstep (se 1 (by rfl) ⟨3499415, by rfl⟩ : syracuseStep 4665887 = 6998831) B6998831
theorem B3110591 : Blo 2073435 3110591 := bstep (se 1 (by rfl) ⟨2332943, by rfl⟩ : syracuseStep 3110591 = 4665887) B4665887
theorem B2073727 : Blo 2073435 2073727 := bstep (se 1 (by rfl) ⟨1555295, by rfl⟩ : syracuseStep 2073727 = 3110591) B3110591
theorem B3110597 : Blo 2073435 3110597 := bbase (se 4 (by rfl) ⟨291618, by rfl⟩ : syracuseStep 3110597 = 583237) (by norm_num)
theorem B2073731 : Blo 2073435 2073731 := bstep (se 1 (by rfl) ⟨1555298, by rfl⟩ : syracuseStep 2073731 = 3110597) B3110597
theorem B3499429 : Blo 2073435 3499429 := bbase (se 4 (by rfl) ⟨328071, by rfl⟩ : syracuseStep 3499429 = 656143) (by norm_num)
theorem B4665905 : Blo 2073435 4665905 := bstep (se 2 (by rfl) ⟨1749714, by rfl⟩ : syracuseStep 4665905 = 3499429) B3499429
theorem B3110603 : Blo 2073435 3110603 := bstep (se 1 (by rfl) ⟨2332952, by rfl⟩ : syracuseStep 3110603 = 4665905) B4665905
theorem B2073735 : Blo 2073435 2073735 := bstep (se 1 (by rfl) ⟨1555301, by rfl⟩ : syracuseStep 2073735 = 3110603) B3110603
theorem B2332957 : Blo 2073435 2332957 := bbase (se 3 (by rfl) ⟨437429, by rfl⟩ : syracuseStep 2332957 = 874859) (by norm_num)
theorem B3110609 : Blo 2073435 3110609 := bstep (se 2 (by rfl) ⟨1166478, by rfl⟩ : syracuseStep 3110609 = 2332957) B2332957
theorem B2073739 : Blo 2073435 2073739 := bstep (se 1 (by rfl) ⟨1555304, by rfl⟩ : syracuseStep 2073739 = 3110609) B3110609
theorem B6998885 : Blo 2073435 6998885 := bbase (se 4 (by rfl) ⟨656145, by rfl⟩ : syracuseStep 6998885 = 1312291) (by norm_num)
theorem B4665923 : Blo 2073435 4665923 := bstep (se 1 (by rfl) ⟨3499442, by rfl⟩ : syracuseStep 4665923 = 6998885) B6998885
theorem B3110615 : Blo 2073435 3110615 := bstep (se 1 (by rfl) ⟨2332961, by rfl⟩ : syracuseStep 3110615 = 4665923) B4665923
theorem B2073743 : Blo 2073435 2073743 := bstep (se 1 (by rfl) ⟨1555307, by rfl⟩ : syracuseStep 2073743 = 3110615) B3110615
theorem B3110621 : Blo 2073435 3110621 := bbase (se 3 (by rfl) ⟨583241, by rfl⟩ : syracuseStep 3110621 = 1166483) (by norm_num)
theorem B2073747 : Blo 2073435 2073747 := bstep (se 1 (by rfl) ⟨1555310, by rfl⟩ : syracuseStep 2073747 = 3110621) B3110621
theorem B4665941 : Blo 2073435 4665941 := bbase (se 8 (by rfl) ⟨27339, by rfl⟩ : syracuseStep 4665941 = 54679) (by norm_num)
theorem B3110627 : Blo 2073435 3110627 := bstep (se 1 (by rfl) ⟨2332970, by rfl⟩ : syracuseStep 3110627 = 4665941) B4665941
theorem B2073751 : Blo 2073435 2073751 := bstep (se 1 (by rfl) ⟨1555313, by rfl⟩ : syracuseStep 2073751 = 3110627) B3110627
theorem B3321757 : Blo 2073435 3321757 := bbase (se 3 (by rfl) ⟨622829, by rfl⟩ : syracuseStep 3321757 = 1245659) (by norm_num)
theorem B4429009 : Blo 2073435 4429009 := bstep (se 2 (by rfl) ⟨1660878, by rfl⟩ : syracuseStep 4429009 = 3321757) B3321757
theorem B5905345 : Blo 2073435 5905345 := bstep (se 2 (by rfl) ⟨2214504, by rfl⟩ : syracuseStep 5905345 = 4429009) B4429009
theorem B7873793 : Blo 2073435 7873793 := bstep (se 2 (by rfl) ⟨2952672, by rfl⟩ : syracuseStep 7873793 = 5905345) B5905345
theorem B5249195 : Blo 2073435 5249195 := bstep (se 1 (by rfl) ⟨3936896, by rfl⟩ : syracuseStep 5249195 = 7873793) B7873793
theorem B3499463 : Blo 2073435 3499463 := bstep (se 1 (by rfl) ⟨2624597, by rfl⟩ : syracuseStep 3499463 = 5249195) B5249195
theorem B2332975 : Blo 2073435 2332975 := bstep (se 1 (by rfl) ⟨1749731, by rfl⟩ : syracuseStep 2332975 = 3499463) B3499463
theorem B3110633 : Blo 2073435 3110633 := bstep (se 2 (by rfl) ⟨1166487, by rfl⟩ : syracuseStep 3110633 = 2332975) B2332975
theorem B2073755 : Blo 2073435 2073755 := bstep (se 1 (by rfl) ⟨1555316, by rfl⟩ : syracuseStep 2073755 = 3110633) B3110633
theorem B26574101 : Blo 2073435 26574101 := bbase (se 6 (by rfl) ⟨622830, by rfl⟩ : syracuseStep 26574101 = 1245661) (by norm_num)
theorem B17716067 : Blo 2073435 17716067 := bstep (se 1 (by rfl) ⟨13287050, by rfl⟩ : syracuseStep 17716067 = 26574101) B26574101
theorem B11810711 : Blo 2073435 11810711 := bstep (se 1 (by rfl) ⟨8858033, by rfl⟩ : syracuseStep 11810711 = 17716067) B17716067
theorem B7873807 : Blo 2073435 7873807 := bstep (se 1 (by rfl) ⟨5905355, by rfl⟩ : syracuseStep 7873807 = 11810711) B11810711
theorem B10498409 : Blo 2073435 10498409 := bstep (se 2 (by rfl) ⟨3936903, by rfl⟩ : syracuseStep 10498409 = 7873807) B7873807
theorem B6998939 : Blo 2073435 6998939 := bstep (se 1 (by rfl) ⟨5249204, by rfl⟩ : syracuseStep 6998939 = 10498409) B10498409
theorem B4665959 : Blo 2073435 4665959 := bstep (se 1 (by rfl) ⟨3499469, by rfl⟩ : syracuseStep 4665959 = 6998939) B6998939
theorem B3110639 : Blo 2073435 3110639 := bstep (se 1 (by rfl) ⟨2332979, by rfl⟩ : syracuseStep 3110639 = 4665959) B4665959
theorem B2073759 : Blo 2073435 2073759 := bstep (se 1 (by rfl) ⟨1555319, by rfl⟩ : syracuseStep 2073759 = 3110639) B3110639
theorem B3110645 : Blo 2073435 3110645 := bbase (se 5 (by rfl) ⟨145811, by rfl⟩ : syracuseStep 3110645 = 291623) (by norm_num)
theorem B2073763 : Blo 2073435 2073763 := bstep (se 1 (by rfl) ⟨1555322, by rfl⟩ : syracuseStep 2073763 = 3110645) B3110645
theorem B8858069 : Blo 2073435 8858069 := bbase (se 7 (by rfl) ⟨103805, by rfl⟩ : syracuseStep 8858069 = 207611) (by norm_num)
theorem B5905379 : Blo 2073435 5905379 := bstep (se 1 (by rfl) ⟨4429034, by rfl⟩ : syracuseStep 5905379 = 8858069) B8858069
theorem B3936919 : Blo 2073435 3936919 := bstep (se 1 (by rfl) ⟨2952689, by rfl⟩ : syracuseStep 3936919 = 5905379) B5905379
theorem B5249225 : Blo 2073435 5249225 := bstep (se 2 (by rfl) ⟨1968459, by rfl⟩ : syracuseStep 5249225 = 3936919) B3936919
theorem B3499483 : Blo 2073435 3499483 := bstep (se 1 (by rfl) ⟨2624612, by rfl⟩ : syracuseStep 3499483 = 5249225) B5249225
theorem B4665977 : Blo 2073435 4665977 := bstep (se 2 (by rfl) ⟨1749741, by rfl⟩ : syracuseStep 4665977 = 3499483) B3499483
theorem B3110651 : Blo 2073435 3110651 := bstep (se 1 (by rfl) ⟨2332988, by rfl⟩ : syracuseStep 3110651 = 4665977) B4665977
theorem B2073767 : Blo 2073435 2073767 := bstep (se 1 (by rfl) ⟨1555325, by rfl⟩ : syracuseStep 2073767 = 3110651) B3110651
theorem B2332993 : Blo 2073435 2332993 := bbase (se 2 (by rfl) ⟨874872, by rfl⟩ : syracuseStep 2332993 = 1749745) (by norm_num)
theorem B3110657 : Blo 2073435 3110657 := bstep (se 2 (by rfl) ⟨1166496, by rfl⟩ : syracuseStep 3110657 = 2332993) B2332993
theorem B2073771 : Blo 2073435 2073771 := bstep (se 1 (by rfl) ⟨1555328, by rfl⟩ : syracuseStep 2073771 = 3110657) B3110657
theorem B5249245 : Blo 2073435 5249245 := bbase (se 3 (by rfl) ⟨984233, by rfl⟩ : syracuseStep 5249245 = 1968467) (by norm_num)
theorem B6998993 : Blo 2073435 6998993 := bstep (se 2 (by rfl) ⟨2624622, by rfl⟩ : syracuseStep 6998993 = 5249245) B5249245
theorem B4665995 : Blo 2073435 4665995 := bstep (se 1 (by rfl) ⟨3499496, by rfl⟩ : syracuseStep 4665995 = 6998993) B6998993
theorem B3110663 : Blo 2073435 3110663 := bstep (se 1 (by rfl) ⟨2332997, by rfl⟩ : syracuseStep 3110663 = 4665995) B4665995
theorem B2073775 : Blo 2073435 2073775 := bstep (se 1 (by rfl) ⟨1555331, by rfl⟩ : syracuseStep 2073775 = 3110663) B3110663
theorem B3110669 : Blo 2073435 3110669 := bbase (se 3 (by rfl) ⟨583250, by rfl⟩ : syracuseStep 3110669 = 1166501) (by norm_num)
theorem B2073779 : Blo 2073435 2073779 := bstep (se 1 (by rfl) ⟨1555334, by rfl⟩ : syracuseStep 2073779 = 3110669) B3110669
theorem B4666013 : Blo 2073435 4666013 := bbase (se 3 (by rfl) ⟨874877, by rfl⟩ : syracuseStep 4666013 = 1749755) (by norm_num)
theorem B3110675 : Blo 2073435 3110675 := bstep (se 1 (by rfl) ⟨2333006, by rfl⟩ : syracuseStep 3110675 = 4666013) B4666013
theorem B2073783 : Blo 2073435 2073783 := bstep (se 1 (by rfl) ⟨1555337, by rfl⟩ : syracuseStep 2073783 = 3110675) B3110675
theorem B3499517 : Blo 2073435 3499517 := bbase (se 3 (by rfl) ⟨656159, by rfl⟩ : syracuseStep 3499517 = 1312319) (by norm_num)
theorem B2333011 : Blo 2073435 2333011 := bstep (se 1 (by rfl) ⟨1749758, by rfl⟩ : syracuseStep 2333011 = 3499517) B3499517
theorem B3110681 : Blo 2073435 3110681 := bstep (se 2 (by rfl) ⟨1166505, by rfl⟩ : syracuseStep 3110681 = 2333011) B2333011
theorem B2073787 : Blo 2073435 2073787 := bstep (se 1 (by rfl) ⟨1555340, by rfl⟩ : syracuseStep 2073787 = 3110681) B3110681
theorem B4429085 : Blo 2073435 4429085 := bbase (se 3 (by rfl) ⟨830453, by rfl⟩ : syracuseStep 4429085 = 1660907) (by norm_num)
theorem B11810893 : Blo 2073435 11810893 := bstep (se 3 (by rfl) ⟨2214542, by rfl⟩ : syracuseStep 11810893 = 4429085) B4429085
theorem B15747857 : Blo 2073435 15747857 := bstep (se 2 (by rfl) ⟨5905446, by rfl⟩ : syracuseStep 15747857 = 11810893) B11810893
theorem B10498571 : Blo 2073435 10498571 := bstep (se 1 (by rfl) ⟨7873928, by rfl⟩ : syracuseStep 10498571 = 15747857) B15747857
theorem B6999047 : Blo 2073435 6999047 := bstep (se 1 (by rfl) ⟨5249285, by rfl⟩ : syracuseStep 6999047 = 10498571) B10498571
theorem B4666031 : Blo 2073435 4666031 := bstep (se 1 (by rfl) ⟨3499523, by rfl⟩ : syracuseStep 4666031 = 6999047) B6999047
theorem B3110687 : Blo 2073435 3110687 := bstep (se 1 (by rfl) ⟨2333015, by rfl⟩ : syracuseStep 3110687 = 4666031) B4666031
theorem B2073791 : Blo 2073435 2073791 := bstep (se 1 (by rfl) ⟨1555343, by rfl⟩ : syracuseStep 2073791 = 3110687) B3110687
theorem B3110693 : Blo 2073435 3110693 := bbase (se 4 (by rfl) ⟨291627, by rfl⟩ : syracuseStep 3110693 = 583255) (by norm_num)
theorem B2073795 : Blo 2073435 2073795 := bstep (se 1 (by rfl) ⟨1555346, by rfl⟩ : syracuseStep 2073795 = 3110693) B3110693
theorem B2624653 : Blo 2073435 2624653 := bbase (se 3 (by rfl) ⟨492122, by rfl⟩ : syracuseStep 2624653 = 984245) (by norm_num)
theorem B3499537 : Blo 2073435 3499537 := bstep (se 2 (by rfl) ⟨1312326, by rfl⟩ : syracuseStep 3499537 = 2624653) B2624653
theorem B4666049 : Blo 2073435 4666049 := bstep (se 2 (by rfl) ⟨1749768, by rfl⟩ : syracuseStep 4666049 = 3499537) B3499537
theorem B3110699 : Blo 2073435 3110699 := bstep (se 1 (by rfl) ⟨2333024, by rfl⟩ : syracuseStep 3110699 = 4666049) B4666049
theorem B2073799 : Blo 2073435 2073799 := bstep (se 1 (by rfl) ⟨1555349, by rfl⟩ : syracuseStep 2073799 = 3110699) B3110699
theorem B2333029 : Blo 2073435 2333029 := bbase (se 4 (by rfl) ⟨218721, by rfl⟩ : syracuseStep 2333029 = 437443) (by norm_num)
theorem B3110705 : Blo 2073435 3110705 := bstep (se 2 (by rfl) ⟨1166514, by rfl⟩ : syracuseStep 3110705 = 2333029) B2333029
theorem B2073803 : Blo 2073435 2073803 := bstep (se 1 (by rfl) ⟨1555352, by rfl⟩ : syracuseStep 2073803 = 3110705) B3110705
theorem B5905493 : Blo 2073435 5905493 := bbase (se 8 (by rfl) ⟨34602, by rfl⟩ : syracuseStep 5905493 = 69205) (by norm_num)
theorem B3936995 : Blo 2073435 3936995 := bstep (se 1 (by rfl) ⟨2952746, by rfl⟩ : syracuseStep 3936995 = 5905493) B5905493
theorem B2624663 : Blo 2073435 2624663 := bstep (se 1 (by rfl) ⟨1968497, by rfl⟩ : syracuseStep 2624663 = 3936995) B3936995
theorem B6999101 : Blo 2073435 6999101 := bstep (se 3 (by rfl) ⟨1312331, by rfl⟩ : syracuseStep 6999101 = 2624663) B2624663
theorem B4666067 : Blo 2073435 4666067 := bstep (se 1 (by rfl) ⟨3499550, by rfl⟩ : syracuseStep 4666067 = 6999101) B6999101
theorem B3110711 : Blo 2073435 3110711 := bstep (se 1 (by rfl) ⟨2333033, by rfl⟩ : syracuseStep 3110711 = 4666067) B4666067
theorem B2073807 : Blo 2073435 2073807 := bstep (se 1 (by rfl) ⟨1555355, by rfl⟩ : syracuseStep 2073807 = 3110711) B3110711
theorem B3110717 : Blo 2073435 3110717 := bbase (se 3 (by rfl) ⟨583259, by rfl⟩ : syracuseStep 3110717 = 1166519) (by norm_num)
theorem B2073811 : Blo 2073435 2073811 := bstep (se 1 (by rfl) ⟨1555358, by rfl⟩ : syracuseStep 2073811 = 3110717) B3110717
theorem B4666085 : Blo 2073435 4666085 := bbase (se 4 (by rfl) ⟨437445, by rfl⟩ : syracuseStep 4666085 = 874891) (by norm_num)
theorem B3110723 : Blo 2073435 3110723 := bstep (se 1 (by rfl) ⟨2333042, by rfl⟩ : syracuseStep 3110723 = 4666085) B4666085
theorem B2073815 : Blo 2073435 2073815 := bstep (se 1 (by rfl) ⟨1555361, by rfl⟩ : syracuseStep 2073815 = 3110723) B3110723
theorem B5249357 : Blo 2073435 5249357 := bbase (se 3 (by rfl) ⟨984254, by rfl⟩ : syracuseStep 5249357 = 1968509) (by norm_num)
theorem B3499571 : Blo 2073435 3499571 := bstep (se 1 (by rfl) ⟨2624678, by rfl⟩ : syracuseStep 3499571 = 5249357) B5249357
theorem B2333047 : Blo 2073435 2333047 := bstep (se 1 (by rfl) ⟨1749785, by rfl⟩ : syracuseStep 2333047 = 3499571) B3499571
theorem B3110729 : Blo 2073435 3110729 := bstep (se 2 (by rfl) ⟨1166523, by rfl⟩ : syracuseStep 3110729 = 2333047) B2333047
theorem B2073819 : Blo 2073435 2073819 := bstep (se 1 (by rfl) ⟨1555364, by rfl⟩ : syracuseStep 2073819 = 3110729) B3110729
theorem B2214577 : Blo 2073435 2214577 := bbase (se 2 (by rfl) ⟨830466, by rfl⟩ : syracuseStep 2214577 = 1660933) (by norm_num)
theorem B2952769 : Blo 2073435 2952769 := bstep (se 2 (by rfl) ⟨1107288, by rfl⟩ : syracuseStep 2952769 = 2214577) B2214577
theorem B3937025 : Blo 2073435 3937025 := bstep (se 2 (by rfl) ⟨1476384, by rfl⟩ : syracuseStep 3937025 = 2952769) B2952769
theorem B10498733 : Blo 2073435 10498733 := bstep (se 3 (by rfl) ⟨1968512, by rfl⟩ : syracuseStep 10498733 = 3937025) B3937025
theorem B6999155 : Blo 2073435 6999155 := bstep (se 1 (by rfl) ⟨5249366, by rfl⟩ : syracuseStep 6999155 = 10498733) B10498733
theorem B4666103 : Blo 2073435 4666103 := bstep (se 1 (by rfl) ⟨3499577, by rfl⟩ : syracuseStep 4666103 = 6999155) B6999155
theorem B3110735 : Blo 2073435 3110735 := bstep (se 1 (by rfl) ⟨2333051, by rfl⟩ : syracuseStep 3110735 = 4666103) B4666103
theorem B2073823 : Blo 2073435 2073823 := bstep (se 1 (by rfl) ⟨1555367, by rfl⟩ : syracuseStep 2073823 = 3110735) B3110735
theorem B3110741 : Blo 2073435 3110741 := bbase (se 9 (by rfl) ⟨9113, by rfl⟩ : syracuseStep 3110741 = 18227) (by norm_num)
theorem B2073827 : Blo 2073435 2073827 := bstep (se 1 (by rfl) ⟨1555370, by rfl⟩ : syracuseStep 2073827 = 3110741) B3110741
theorem B2491409 : Blo 2073435 2491409 := bbase (se 2 (by rfl) ⟨934278, by rfl⟩ : syracuseStep 2491409 = 1868557) (by norm_num)
theorem B6643757 : Blo 2073435 6643757 := bstep (se 3 (by rfl) ⟨1245704, by rfl⟩ : syracuseStep 6643757 = 2491409) B2491409
theorem B4429171 : Blo 2073435 4429171 := bstep (se 1 (by rfl) ⟨3321878, by rfl⟩ : syracuseStep 4429171 = 6643757) B6643757
theorem B5905561 : Blo 2073435 5905561 := bstep (se 2 (by rfl) ⟨2214585, by rfl⟩ : syracuseStep 5905561 = 4429171) B4429171
theorem B7874081 : Blo 2073435 7874081 := bstep (se 2 (by rfl) ⟨2952780, by rfl⟩ : syracuseStep 7874081 = 5905561) B5905561
theorem B5249387 : Blo 2073435 5249387 := bstep (se 1 (by rfl) ⟨3937040, by rfl⟩ : syracuseStep 5249387 = 7874081) B7874081
theorem B3499591 : Blo 2073435 3499591 := bstep (se 1 (by rfl) ⟨2624693, by rfl⟩ : syracuseStep 3499591 = 5249387) B5249387
theorem B4666121 : Blo 2073435 4666121 := bstep (se 2 (by rfl) ⟨1749795, by rfl⟩ : syracuseStep 4666121 = 3499591) B3499591
theorem B3110747 : Blo 2073435 3110747 := bstep (se 1 (by rfl) ⟨2333060, by rfl⟩ : syracuseStep 3110747 = 4666121) B4666121
theorem B2073831 : Blo 2073435 2073831 := bstep (se 1 (by rfl) ⟨1555373, by rfl⟩ : syracuseStep 2073831 = 3110747) B3110747
theorem B2333065 : Blo 2073435 2333065 := bbase (se 2 (by rfl) ⟨874899, by rfl⟩ : syracuseStep 2333065 = 1749799) (by norm_num)
theorem B3110753 : Blo 2073435 3110753 := bstep (se 2 (by rfl) ⟨1166532, by rfl⟩ : syracuseStep 3110753 = 2333065) B2333065
theorem B2073835 : Blo 2073435 2073835 := bstep (se 1 (by rfl) ⟨1555376, by rfl⟩ : syracuseStep 2073835 = 3110753) B3110753
theorem B9459605 : Blo 2073435 9459605 := bbase (se 6 (by rfl) ⟨221709, by rfl⟩ : syracuseStep 9459605 = 443419) (by norm_num)
theorem B6306403 : Blo 2073435 6306403 := bstep (se 1 (by rfl) ⟨4729802, by rfl⟩ : syracuseStep 6306403 = 9459605) B9459605
theorem B8408537 : Blo 2073435 8408537 := bstep (se 2 (by rfl) ⟨3153201, by rfl⟩ : syracuseStep 8408537 = 6306403) B6306403
theorem B5605691 : Blo 2073435 5605691 := bstep (se 1 (by rfl) ⟨4204268, by rfl⟩ : syracuseStep 5605691 = 8408537) B8408537
theorem B59794037 : Blo 2073435 59794037 := bstep (se 5 (by rfl) ⟨2802845, by rfl⟩ : syracuseStep 59794037 = 5605691) B5605691
theorem B39862691 : Blo 2073435 39862691 := bstep (se 1 (by rfl) ⟨29897018, by rfl⟩ : syracuseStep 39862691 = 59794037) B59794037
theorem B26575127 : Blo 2073435 26575127 := bstep (se 1 (by rfl) ⟨19931345, by rfl⟩ : syracuseStep 26575127 = 39862691) B39862691
theorem B17716751 : Blo 2073435 17716751 := bstep (se 1 (by rfl) ⟨13287563, by rfl⟩ : syracuseStep 17716751 = 26575127) B26575127
theorem B11811167 : Blo 2073435 11811167 := bstep (se 1 (by rfl) ⟨8858375, by rfl⟩ : syracuseStep 11811167 = 17716751) B17716751
theorem B7874111 : Blo 2073435 7874111 := bstep (se 1 (by rfl) ⟨5905583, by rfl⟩ : syracuseStep 7874111 = 11811167) B11811167
theorem B5249407 : Blo 2073435 5249407 := bstep (se 1 (by rfl) ⟨3937055, by rfl⟩ : syracuseStep 5249407 = 7874111) B7874111
theorem B6999209 : Blo 2073435 6999209 := bstep (se 2 (by rfl) ⟨2624703, by rfl⟩ : syracuseStep 6999209 = 5249407) B5249407
theorem B4666139 : Blo 2073435 4666139 := bstep (se 1 (by rfl) ⟨3499604, by rfl⟩ : syracuseStep 4666139 = 6999209) B6999209
theorem B3110759 : Blo 2073435 3110759 := bstep (se 1 (by rfl) ⟨2333069, by rfl⟩ : syracuseStep 3110759 = 4666139) B4666139
theorem B2073839 : Blo 2073435 2073839 := bstep (se 1 (by rfl) ⟨1555379, by rfl⟩ : syracuseStep 2073839 = 3110759) B3110759
theorem B3110765 : Blo 2073435 3110765 := bbase (se 3 (by rfl) ⟨583268, by rfl⟩ : syracuseStep 3110765 = 1166537) (by norm_num)
theorem B2073843 : Blo 2073435 2073843 := bstep (se 1 (by rfl) ⟨1555382, by rfl⟩ : syracuseStep 2073843 = 3110765) B3110765
theorem B4666157 : Blo 2073435 4666157 := bbase (se 3 (by rfl) ⟨874904, by rfl⟩ : syracuseStep 4666157 = 1749809) (by norm_num)
theorem B3110771 : Blo 2073435 3110771 := bstep (se 1 (by rfl) ⟨2333078, by rfl⟩ : syracuseStep 3110771 = 4666157) B4666157
theorem B2073847 : Blo 2073435 2073847 := bstep (se 1 (by rfl) ⟨1555385, by rfl⟩ : syracuseStep 2073847 = 3110771) B3110771
theorem B3990797 : Blo 2073435 3990797 := bbase (se 3 (by rfl) ⟨748274, by rfl⟩ : syracuseStep 3990797 = 1496549) (by norm_num)
theorem B2660531 : Blo 2073435 2660531 := bstep (se 1 (by rfl) ⟨1995398, by rfl⟩ : syracuseStep 2660531 = 3990797) B3990797
theorem B7094749 : Blo 2073435 7094749 := bstep (se 3 (by rfl) ⟨1330265, by rfl⟩ : syracuseStep 7094749 = 2660531) B2660531
theorem B9459665 : Blo 2073435 9459665 := bstep (se 2 (by rfl) ⟨3547374, by rfl⟩ : syracuseStep 9459665 = 7094749) B7094749
theorem B6306443 : Blo 2073435 6306443 := bstep (se 1 (by rfl) ⟨4729832, by rfl⟩ : syracuseStep 6306443 = 9459665) B9459665
theorem B4204295 : Blo 2073435 4204295 := bstep (se 1 (by rfl) ⟨3153221, by rfl⟩ : syracuseStep 4204295 = 6306443) B6306443
theorem B2802863 : Blo 2073435 2802863 := bstep (se 1 (by rfl) ⟨2102147, by rfl⟩ : syracuseStep 2802863 = 4204295) B4204295
theorem B7474301 : Blo 2073435 7474301 := bstep (se 3 (by rfl) ⟨1401431, by rfl⟩ : syracuseStep 7474301 = 2802863) B2802863
theorem B4982867 : Blo 2073435 4982867 := bstep (se 1 (by rfl) ⟨3737150, by rfl⟩ : syracuseStep 4982867 = 7474301) B7474301
theorem B3321911 : Blo 2073435 3321911 := bstep (se 1 (by rfl) ⟨2491433, by rfl⟩ : syracuseStep 3321911 = 4982867) B4982867
theorem B8858429 : Blo 2073435 8858429 := bstep (se 3 (by rfl) ⟨1660955, by rfl⟩ : syracuseStep 8858429 = 3321911) B3321911
theorem B5905619 : Blo 2073435 5905619 := bstep (se 1 (by rfl) ⟨4429214, by rfl⟩ : syracuseStep 5905619 = 8858429) B8858429
theorem B3937079 : Blo 2073435 3937079 := bstep (se 1 (by rfl) ⟨2952809, by rfl⟩ : syracuseStep 3937079 = 5905619) B5905619
theorem B2624719 : Blo 2073435 2624719 := bstep (se 1 (by rfl) ⟨1968539, by rfl⟩ : syracuseStep 2624719 = 3937079) B3937079
theorem B3499625 : Blo 2073435 3499625 := bstep (se 2 (by rfl) ⟨1312359, by rfl⟩ : syracuseStep 3499625 = 2624719) B2624719
theorem B2333083 : Blo 2073435 2333083 := bstep (se 1 (by rfl) ⟨1749812, by rfl⟩ : syracuseStep 2333083 = 3499625) B3499625
theorem B3110777 : Blo 2073435 3110777 := bstep (se 2 (by rfl) ⟨1166541, by rfl⟩ : syracuseStep 3110777 = 2333083) B2333083
theorem B2073851 : Blo 2073435 2073851 := bstep (se 1 (by rfl) ⟨1555388, by rfl⟩ : syracuseStep 2073851 = 3110777) B3110777
theorem B9965749 : Blo 2073435 9965749 := bbase (se 5 (by rfl) ⟨467144, by rfl⟩ : syracuseStep 9965749 = 934289) (by norm_num)
theorem B13287665 : Blo 2073435 13287665 := bstep (se 2 (by rfl) ⟨4982874, by rfl⟩ : syracuseStep 13287665 = 9965749) B9965749
theorem B35433773 : Blo 2073435 35433773 := bstep (se 3 (by rfl) ⟨6643832, by rfl⟩ : syracuseStep 35433773 = 13287665) B13287665
theorem B23622515 : Blo 2073435 23622515 := bstep (se 1 (by rfl) ⟨17716886, by rfl⟩ : syracuseStep 23622515 = 35433773) B35433773
theorem B15748343 : Blo 2073435 15748343 := bstep (se 1 (by rfl) ⟨11811257, by rfl⟩ : syracuseStep 15748343 = 23622515) B23622515
theorem B10498895 : Blo 2073435 10498895 := bstep (se 1 (by rfl) ⟨7874171, by rfl⟩ : syracuseStep 10498895 = 15748343) B15748343
theorem B6999263 : Blo 2073435 6999263 := bstep (se 1 (by rfl) ⟨5249447, by rfl⟩ : syracuseStep 6999263 = 10498895) B10498895
theorem B4666175 : Blo 2073435 4666175 := bstep (se 1 (by rfl) ⟨3499631, by rfl⟩ : syracuseStep 4666175 = 6999263) B6999263
theorem B3110783 : Blo 2073435 3110783 := bstep (se 1 (by rfl) ⟨2333087, by rfl⟩ : syracuseStep 3110783 = 4666175) B4666175
theorem B2073855 : Blo 2073435 2073855 := bstep (se 1 (by rfl) ⟨1555391, by rfl⟩ : syracuseStep 2073855 = 3110783) B3110783
theorem B3110789 : Blo 2073435 3110789 := bbase (se 4 (by rfl) ⟨291636, by rfl⟩ : syracuseStep 3110789 = 583273) (by norm_num)
theorem B2073859 : Blo 2073435 2073859 := bstep (se 1 (by rfl) ⟨1555394, by rfl⟩ : syracuseStep 2073859 = 3110789) B3110789
theorem B3499645 : Blo 2073435 3499645 := bbase (se 3 (by rfl) ⟨656183, by rfl⟩ : syracuseStep 3499645 = 1312367) (by norm_num)
theorem B4666193 : Blo 2073435 4666193 := bstep (se 2 (by rfl) ⟨1749822, by rfl⟩ : syracuseStep 4666193 = 3499645) B3499645
theorem B3110795 : Blo 2073435 3110795 := bstep (se 1 (by rfl) ⟨2333096, by rfl⟩ : syracuseStep 3110795 = 4666193) B4666193
theorem B2073863 : Blo 2073435 2073863 := bstep (se 1 (by rfl) ⟨1555397, by rfl⟩ : syracuseStep 2073863 = 3110795) B3110795
theorem B2333101 : Blo 2073435 2333101 := bbase (se 3 (by rfl) ⟨437456, by rfl⟩ : syracuseStep 2333101 = 874913) (by norm_num)
theorem B3110801 : Blo 2073435 3110801 := bstep (se 2 (by rfl) ⟨1166550, by rfl⟩ : syracuseStep 3110801 = 2333101) B2333101
theorem B2073867 : Blo 2073435 2073867 := bstep (se 1 (by rfl) ⟨1555400, by rfl⟩ : syracuseStep 2073867 = 3110801) B3110801
theorem B6999317 : Blo 2073435 6999317 := bbase (se 6 (by rfl) ⟨164046, by rfl⟩ : syracuseStep 6999317 = 328093) (by norm_num)
theorem B4666211 : Blo 2073435 4666211 := bstep (se 1 (by rfl) ⟨3499658, by rfl⟩ : syracuseStep 4666211 = 6999317) B6999317
theorem B3110807 : Blo 2073435 3110807 := bstep (se 1 (by rfl) ⟨2333105, by rfl⟩ : syracuseStep 3110807 = 4666211) B4666211
theorem B2073871 : Blo 2073435 2073871 := bstep (se 1 (by rfl) ⟨1555403, by rfl⟩ : syracuseStep 2073871 = 3110807) B3110807
theorem B3110813 : Blo 2073435 3110813 := bbase (se 3 (by rfl) ⟨583277, by rfl⟩ : syracuseStep 3110813 = 1166555) (by norm_num)
theorem B2073875 : Blo 2073435 2073875 := bstep (se 1 (by rfl) ⟨1555406, by rfl⟩ : syracuseStep 2073875 = 3110813) B3110813
theorem B4666229 : Blo 2073435 4666229 := bbase (se 5 (by rfl) ⟨218729, by rfl⟩ : syracuseStep 4666229 = 437459) (by norm_num)
theorem B3110819 : Blo 2073435 3110819 := bstep (se 1 (by rfl) ⟨2333114, by rfl⟩ : syracuseStep 3110819 = 4666229) B4666229
theorem B2073879 : Blo 2073435 2073879 := bstep (se 1 (by rfl) ⟨1555409, by rfl⟩ : syracuseStep 2073879 = 3110819) B3110819
theorem B13469141 : Blo 2073435 13469141 := bbase (se 7 (by rfl) ⟨157841, by rfl⟩ : syracuseStep 13469141 = 315683) (by norm_num)
theorem B8979427 : Blo 2073435 8979427 := bstep (se 1 (by rfl) ⟨6734570, by rfl⟩ : syracuseStep 8979427 = 13469141) B13469141
theorem B11972569 : Blo 2073435 11972569 := bstep (se 2 (by rfl) ⟨4489713, by rfl⟩ : syracuseStep 11972569 = 8979427) B8979427
theorem B15963425 : Blo 2073435 15963425 := bstep (se 2 (by rfl) ⟨5986284, by rfl⟩ : syracuseStep 15963425 = 11972569) B11972569
theorem B10642283 : Blo 2073435 10642283 := bstep (se 1 (by rfl) ⟨7981712, by rfl⟩ : syracuseStep 10642283 = 15963425) B15963425
theorem B7094855 : Blo 2073435 7094855 := bstep (se 1 (by rfl) ⟨5321141, by rfl⟩ : syracuseStep 7094855 = 10642283) B10642283
theorem B4729903 : Blo 2073435 4729903 := bstep (se 1 (by rfl) ⟨3547427, by rfl⟩ : syracuseStep 4729903 = 7094855) B7094855
theorem B25226149 : Blo 2073435 25226149 := bstep (se 4 (by rfl) ⟨2364951, by rfl⟩ : syracuseStep 25226149 = 4729903) B4729903
theorem B33634865 : Blo 2073435 33634865 := bstep (se 2 (by rfl) ⟨12613074, by rfl⟩ : syracuseStep 33634865 = 25226149) B25226149
theorem B22423243 : Blo 2073435 22423243 := bstep (se 1 (by rfl) ⟨16817432, by rfl⟩ : syracuseStep 22423243 = 33634865) B33634865
theorem B29897657 : Blo 2073435 29897657 := bstep (se 2 (by rfl) ⟨11211621, by rfl⟩ : syracuseStep 29897657 = 22423243) B22423243
theorem B19931771 : Blo 2073435 19931771 := bstep (se 1 (by rfl) ⟨14948828, by rfl⟩ : syracuseStep 19931771 = 29897657) B29897657
theorem B13287847 : Blo 2073435 13287847 := bstep (se 1 (by rfl) ⟨9965885, by rfl⟩ : syracuseStep 13287847 = 19931771) B19931771
theorem B17717129 : Blo 2073435 17717129 := bstep (se 2 (by rfl) ⟨6643923, by rfl⟩ : syracuseStep 17717129 = 13287847) B13287847
theorem B11811419 : Blo 2073435 11811419 := bstep (se 1 (by rfl) ⟨8858564, by rfl⟩ : syracuseStep 11811419 = 17717129) B17717129
theorem B7874279 : Blo 2073435 7874279 := bstep (se 1 (by rfl) ⟨5905709, by rfl⟩ : syracuseStep 7874279 = 11811419) B11811419
theorem B5249519 : Blo 2073435 5249519 := bstep (se 1 (by rfl) ⟨3937139, by rfl⟩ : syracuseStep 5249519 = 7874279) B7874279
theorem B3499679 : Blo 2073435 3499679 := bstep (se 1 (by rfl) ⟨2624759, by rfl⟩ : syracuseStep 3499679 = 5249519) B5249519
theorem B2333119 : Blo 2073435 2333119 := bstep (se 1 (by rfl) ⟨1749839, by rfl⟩ : syracuseStep 2333119 = 3499679) B3499679
theorem B3110825 : Blo 2073435 3110825 := bstep (se 2 (by rfl) ⟨1166559, by rfl⟩ : syracuseStep 3110825 = 2333119) B2333119
theorem B2073883 : Blo 2073435 2073883 := bstep (se 1 (by rfl) ⟨1555412, by rfl⟩ : syracuseStep 2073883 = 3110825) B3110825
theorem B7874293 : Blo 2073435 7874293 := bbase (se 5 (by rfl) ⟨369107, by rfl⟩ : syracuseStep 7874293 = 738215) (by norm_num)
theorem B10499057 : Blo 2073435 10499057 := bstep (se 2 (by rfl) ⟨3937146, by rfl⟩ : syracuseStep 10499057 = 7874293) B7874293
theorem B6999371 : Blo 2073435 6999371 := bstep (se 1 (by rfl) ⟨5249528, by rfl⟩ : syracuseStep 6999371 = 10499057) B10499057
theorem B4666247 : Blo 2073435 4666247 := bstep (se 1 (by rfl) ⟨3499685, by rfl⟩ : syracuseStep 4666247 = 6999371) B6999371
theorem B3110831 : Blo 2073435 3110831 := bstep (se 1 (by rfl) ⟨2333123, by rfl⟩ : syracuseStep 3110831 = 4666247) B4666247
theorem B2073887 : Blo 2073435 2073887 := bstep (se 1 (by rfl) ⟨1555415, by rfl⟩ : syracuseStep 2073887 = 3110831) B3110831
theorem B3110837 : Blo 2073435 3110837 := bbase (se 5 (by rfl) ⟨145820, by rfl⟩ : syracuseStep 3110837 = 291641) (by norm_num)
theorem B2073891 : Blo 2073435 2073891 := bstep (se 1 (by rfl) ⟨1555418, by rfl⟩ : syracuseStep 2073891 = 3110837) B3110837
theorem B5249549 : Blo 2073435 5249549 := bbase (se 3 (by rfl) ⟨984290, by rfl⟩ : syracuseStep 5249549 = 1968581) (by norm_num)
theorem B3499699 : Blo 2073435 3499699 := bstep (se 1 (by rfl) ⟨2624774, by rfl⟩ : syracuseStep 3499699 = 5249549) B5249549
theorem B4666265 : Blo 2073435 4666265 := bstep (se 2 (by rfl) ⟨1749849, by rfl⟩ : syracuseStep 4666265 = 3499699) B3499699
theorem B3110843 : Blo 2073435 3110843 := bstep (se 1 (by rfl) ⟨2333132, by rfl⟩ : syracuseStep 3110843 = 4666265) B4666265
theorem B2073895 : Blo 2073435 2073895 := bstep (se 1 (by rfl) ⟨1555421, by rfl⟩ : syracuseStep 2073895 = 3110843) B3110843
theorem B2333137 : Blo 2073435 2333137 := bbase (se 2 (by rfl) ⟨874926, by rfl⟩ : syracuseStep 2333137 = 1749853) (by norm_num)
theorem B3110849 : Blo 2073435 3110849 := bstep (se 2 (by rfl) ⟨1166568, by rfl⟩ : syracuseStep 3110849 = 2333137) B2333137
theorem B2073899 : Blo 2073435 2073899 := bstep (se 1 (by rfl) ⟨1555424, by rfl⟩ : syracuseStep 2073899 = 3110849) B3110849
theorem B4429325 : Blo 2073435 4429325 := bbase (se 3 (by rfl) ⟨830498, by rfl⟩ : syracuseStep 4429325 = 1660997) (by norm_num)
theorem B2952883 : Blo 2073435 2952883 := bstep (se 1 (by rfl) ⟨2214662, by rfl⟩ : syracuseStep 2952883 = 4429325) B4429325
theorem B3937177 : Blo 2073435 3937177 := bstep (se 2 (by rfl) ⟨1476441, by rfl⟩ : syracuseStep 3937177 = 2952883) B2952883
theorem B5249569 : Blo 2073435 5249569 := bstep (se 2 (by rfl) ⟨1968588, by rfl⟩ : syracuseStep 5249569 = 3937177) B3937177
theorem B6999425 : Blo 2073435 6999425 := bstep (se 2 (by rfl) ⟨2624784, by rfl⟩ : syracuseStep 6999425 = 5249569) B5249569
theorem B4666283 : Blo 2073435 4666283 := bstep (se 1 (by rfl) ⟨3499712, by rfl⟩ : syracuseStep 4666283 = 6999425) B6999425
theorem B3110855 : Blo 2073435 3110855 := bstep (se 1 (by rfl) ⟨2333141, by rfl⟩ : syracuseStep 3110855 = 4666283) B4666283
theorem B2073903 : Blo 2073435 2073903 := bstep (se 1 (by rfl) ⟨1555427, by rfl⟩ : syracuseStep 2073903 = 3110855) B3110855
theorem B3110861 : Blo 2073435 3110861 := bbase (se 3 (by rfl) ⟨583286, by rfl⟩ : syracuseStep 3110861 = 1166573) (by norm_num)
theorem B2073907 : Blo 2073435 2073907 := bstep (se 1 (by rfl) ⟨1555430, by rfl⟩ : syracuseStep 2073907 = 3110861) B3110861
theorem B4666301 : Blo 2073435 4666301 := bbase (se 3 (by rfl) ⟨874931, by rfl⟩ : syracuseStep 4666301 = 1749863) (by norm_num)
theorem B3110867 : Blo 2073435 3110867 := bstep (se 1 (by rfl) ⟨2333150, by rfl⟩ : syracuseStep 3110867 = 4666301) B4666301
theorem B2073911 : Blo 2073435 2073911 := bstep (se 1 (by rfl) ⟨1555433, by rfl⟩ : syracuseStep 2073911 = 3110867) B3110867
theorem B3499733 : Blo 2073435 3499733 := bbase (se 7 (by rfl) ⟨41012, by rfl⟩ : syracuseStep 3499733 = 82025) (by norm_num)
theorem B2333155 : Blo 2073435 2333155 := bstep (se 1 (by rfl) ⟨1749866, by rfl⟩ : syracuseStep 2333155 = 3499733) B3499733
theorem B3110873 : Blo 2073435 3110873 := bstep (se 2 (by rfl) ⟨1166577, by rfl⟩ : syracuseStep 3110873 = 2333155) B2333155
theorem B2073915 : Blo 2073435 2073915 := bstep (se 1 (by rfl) ⟨1555436, by rfl⟩ : syracuseStep 2073915 = 3110873) B3110873
theorem B4983029 : Blo 2073435 4983029 := bbase (se 5 (by rfl) ⟨233579, by rfl⟩ : syracuseStep 4983029 = 467159) (by norm_num)
theorem B3322019 : Blo 2073435 3322019 := bstep (se 1 (by rfl) ⟨2491514, by rfl⟩ : syracuseStep 3322019 = 4983029) B4983029
theorem B8858717 : Blo 2073435 8858717 := bstep (se 3 (by rfl) ⟨1661009, by rfl⟩ : syracuseStep 8858717 = 3322019) B3322019
theorem B5905811 : Blo 2073435 5905811 := bstep (se 1 (by rfl) ⟨4429358, by rfl⟩ : syracuseStep 5905811 = 8858717) B8858717
theorem B15748829 : Blo 2073435 15748829 := bstep (se 3 (by rfl) ⟨2952905, by rfl⟩ : syracuseStep 15748829 = 5905811) B5905811
theorem B10499219 : Blo 2073435 10499219 := bstep (se 1 (by rfl) ⟨7874414, by rfl⟩ : syracuseStep 10499219 = 15748829) B15748829
theorem B6999479 : Blo 2073435 6999479 := bstep (se 1 (by rfl) ⟨5249609, by rfl⟩ : syracuseStep 6999479 = 10499219) B10499219
theorem B4666319 : Blo 2073435 4666319 := bstep (se 1 (by rfl) ⟨3499739, by rfl⟩ : syracuseStep 4666319 = 6999479) B6999479
theorem B3110879 : Blo 2073435 3110879 := bstep (se 1 (by rfl) ⟨2333159, by rfl⟩ : syracuseStep 3110879 = 4666319) B4666319
theorem B2073919 : Blo 2073435 2073919 := bstep (se 1 (by rfl) ⟨1555439, by rfl⟩ : syracuseStep 2073919 = 3110879) B3110879
theorem B3110885 : Blo 2073435 3110885 := bbase (se 4 (by rfl) ⟨291645, by rfl⟩ : syracuseStep 3110885 = 583291) (by norm_num)
theorem B2073923 : Blo 2073435 2073923 := bstep (se 1 (by rfl) ⟨1555442, by rfl⟩ : syracuseStep 2073923 = 3110885) B3110885
theorem B4730005 : Blo 2073435 4730005 := bbase (se 6 (by rfl) ⟨110859, by rfl⟩ : syracuseStep 4730005 = 221719) (by norm_num)
theorem B6306673 : Blo 2073435 6306673 := bstep (se 2 (by rfl) ⟨2365002, by rfl⟩ : syracuseStep 6306673 = 4730005) B4730005
theorem B8408897 : Blo 2073435 8408897 := bstep (se 2 (by rfl) ⟨3153336, by rfl⟩ : syracuseStep 8408897 = 6306673) B6306673
theorem B5605931 : Blo 2073435 5605931 := bstep (se 1 (by rfl) ⟨4204448, by rfl⟩ : syracuseStep 5605931 = 8408897) B8408897
theorem B3737287 : Blo 2073435 3737287 := bstep (se 1 (by rfl) ⟨2802965, by rfl⟩ : syracuseStep 3737287 = 5605931) B5605931
theorem B4983049 : Blo 2073435 4983049 := bstep (se 2 (by rfl) ⟨1868643, by rfl⟩ : syracuseStep 4983049 = 3737287) B3737287
theorem B6644065 : Blo 2073435 6644065 := bstep (se 2 (by rfl) ⟨2491524, by rfl⟩ : syracuseStep 6644065 = 4983049) B4983049
theorem B8858753 : Blo 2073435 8858753 := bstep (se 2 (by rfl) ⟨3322032, by rfl⟩ : syracuseStep 8858753 = 6644065) B6644065
theorem B5905835 : Blo 2073435 5905835 := bstep (se 1 (by rfl) ⟨4429376, by rfl⟩ : syracuseStep 5905835 = 8858753) B8858753
theorem B3937223 : Blo 2073435 3937223 := bstep (se 1 (by rfl) ⟨2952917, by rfl⟩ : syracuseStep 3937223 = 5905835) B5905835
theorem B2624815 : Blo 2073435 2624815 := bstep (se 1 (by rfl) ⟨1968611, by rfl⟩ : syracuseStep 2624815 = 3937223) B3937223
theorem B3499753 : Blo 2073435 3499753 := bstep (se 2 (by rfl) ⟨1312407, by rfl⟩ : syracuseStep 3499753 = 2624815) B2624815
theorem B4666337 : Blo 2073435 4666337 := bstep (se 2 (by rfl) ⟨1749876, by rfl⟩ : syracuseStep 4666337 = 3499753) B3499753
theorem B3110891 : Blo 2073435 3110891 := bstep (se 1 (by rfl) ⟨2333168, by rfl⟩ : syracuseStep 3110891 = 4666337) B4666337
theorem B2073927 : Blo 2073435 2073927 := bstep (se 1 (by rfl) ⟨1555445, by rfl⟩ : syracuseStep 2073927 = 3110891) B3110891
theorem B2333173 : Blo 2073435 2333173 := bbase (se 5 (by rfl) ⟨109367, by rfl⟩ : syracuseStep 2333173 = 218735) (by norm_num)
theorem B3110897 : Blo 2073435 3110897 := bstep (se 2 (by rfl) ⟨1166586, by rfl⟩ : syracuseStep 3110897 = 2333173) B2333173
theorem B2073931 : Blo 2073435 2073931 := bstep (se 1 (by rfl) ⟨1555448, by rfl⟩ : syracuseStep 2073931 = 3110897) B3110897
theorem B2624825 : Blo 2073435 2624825 := bbase (se 2 (by rfl) ⟨984309, by rfl⟩ : syracuseStep 2624825 = 1968619) (by norm_num)
theorem B6999533 : Blo 2073435 6999533 := bstep (se 3 (by rfl) ⟨1312412, by rfl⟩ : syracuseStep 6999533 = 2624825) B2624825
theorem B4666355 : Blo 2073435 4666355 := bstep (se 1 (by rfl) ⟨3499766, by rfl⟩ : syracuseStep 4666355 = 6999533) B6999533
theorem B3110903 : Blo 2073435 3110903 := bstep (se 1 (by rfl) ⟨2333177, by rfl⟩ : syracuseStep 3110903 = 4666355) B4666355
theorem B2073935 : Blo 2073435 2073935 := bstep (se 1 (by rfl) ⟨1555451, by rfl⟩ : syracuseStep 2073935 = 3110903) B3110903
theorem B3110909 : Blo 2073435 3110909 := bbase (se 3 (by rfl) ⟨583295, by rfl⟩ : syracuseStep 3110909 = 1166591) (by norm_num)
theorem B2073939 : Blo 2073435 2073939 := bstep (se 1 (by rfl) ⟨1555454, by rfl⟩ : syracuseStep 2073939 = 3110909) B3110909
theorem B4666373 : Blo 2073435 4666373 := bbase (se 4 (by rfl) ⟨437472, by rfl⟩ : syracuseStep 4666373 = 874945) (by norm_num)
theorem B3110915 : Blo 2073435 3110915 := bstep (se 1 (by rfl) ⟨2333186, by rfl⟩ : syracuseStep 3110915 = 4666373) B4666373
theorem B2073943 : Blo 2073435 2073943 := bstep (se 1 (by rfl) ⟨1555457, by rfl⟩ : syracuseStep 2073943 = 3110915) B3110915
theorem B3937261 : Blo 2073435 3937261 := bbase (se 3 (by rfl) ⟨738236, by rfl⟩ : syracuseStep 3937261 = 1476473) (by norm_num)
theorem B5249681 : Blo 2073435 5249681 := bstep (se 2 (by rfl) ⟨1968630, by rfl⟩ : syracuseStep 5249681 = 3937261) B3937261
theorem B3499787 : Blo 2073435 3499787 := bstep (se 1 (by rfl) ⟨2624840, by rfl⟩ : syracuseStep 3499787 = 5249681) B5249681
theorem B2333191 : Blo 2073435 2333191 := bstep (se 1 (by rfl) ⟨1749893, by rfl⟩ : syracuseStep 2333191 = 3499787) B3499787
theorem B3110921 : Blo 2073435 3110921 := bstep (se 2 (by rfl) ⟨1166595, by rfl⟩ : syracuseStep 3110921 = 2333191) B2333191
theorem B2073947 : Blo 2073435 2073947 := bstep (se 1 (by rfl) ⟨1555460, by rfl⟩ : syracuseStep 2073947 = 3110921) B3110921
theorem B10499381 : Blo 2073435 10499381 := bbase (se 5 (by rfl) ⟨492158, by rfl⟩ : syracuseStep 10499381 = 984317) (by norm_num)
theorem B6999587 : Blo 2073435 6999587 := bstep (se 1 (by rfl) ⟨5249690, by rfl⟩ : syracuseStep 6999587 = 10499381) B10499381
theorem B4666391 : Blo 2073435 4666391 := bstep (se 1 (by rfl) ⟨3499793, by rfl⟩ : syracuseStep 4666391 = 6999587) B6999587
theorem B3110927 : Blo 2073435 3110927 := bstep (se 1 (by rfl) ⟨2333195, by rfl⟩ : syracuseStep 3110927 = 4666391) B4666391
theorem B2073951 : Blo 2073435 2073951 := bstep (se 1 (by rfl) ⟨1555463, by rfl⟩ : syracuseStep 2073951 = 3110927) B3110927
theorem B3110933 : Blo 2073435 3110933 := bbase (se 6 (by rfl) ⟨72912, by rfl⟩ : syracuseStep 3110933 = 145825) (by norm_num)
theorem B2073955 : Blo 2073435 2073955 := bstep (se 1 (by rfl) ⟨1555466, by rfl⟩ : syracuseStep 2073955 = 3110933) B3110933
theorem B4983125 : Blo 2073435 4983125 := bbase (se 10 (by rfl) ⟨7299, by rfl⟩ : syracuseStep 4983125 = 14599) (by norm_num)
theorem B13288333 : Blo 2073435 13288333 := bstep (se 3 (by rfl) ⟨2491562, by rfl⟩ : syracuseStep 13288333 = 4983125) B4983125
theorem B17717777 : Blo 2073435 17717777 := bstep (se 2 (by rfl) ⟨6644166, by rfl⟩ : syracuseStep 17717777 = 13288333) B13288333
theorem B11811851 : Blo 2073435 11811851 := bstep (se 1 (by rfl) ⟨8858888, by rfl⟩ : syracuseStep 11811851 = 17717777) B17717777
theorem B7874567 : Blo 2073435 7874567 := bstep (se 1 (by rfl) ⟨5905925, by rfl⟩ : syracuseStep 7874567 = 11811851) B11811851
theorem B5249711 : Blo 2073435 5249711 := bstep (se 1 (by rfl) ⟨3937283, by rfl⟩ : syracuseStep 5249711 = 7874567) B7874567
theorem B3499807 : Blo 2073435 3499807 := bstep (se 1 (by rfl) ⟨2624855, by rfl⟩ : syracuseStep 3499807 = 5249711) B5249711
theorem B4666409 : Blo 2073435 4666409 := bstep (se 2 (by rfl) ⟨1749903, by rfl⟩ : syracuseStep 4666409 = 3499807) B3499807
theorem B3110939 : Blo 2073435 3110939 := bstep (se 1 (by rfl) ⟨2333204, by rfl⟩ : syracuseStep 3110939 = 4666409) B4666409
theorem B2073959 : Blo 2073435 2073959 := bstep (se 1 (by rfl) ⟨1555469, by rfl⟩ : syracuseStep 2073959 = 3110939) B3110939
theorem B2333209 : Blo 2073435 2333209 := bbase (se 2 (by rfl) ⟨874953, by rfl⟩ : syracuseStep 2333209 = 1749907) (by norm_num)
theorem B3110945 : Blo 2073435 3110945 := bstep (se 2 (by rfl) ⟨1166604, by rfl⟩ : syracuseStep 3110945 = 2333209) B2333209
theorem B2073963 : Blo 2073435 2073963 := bstep (se 1 (by rfl) ⟨1555472, by rfl⟩ : syracuseStep 2073963 = 3110945) B3110945
theorem B7874597 : Blo 2073435 7874597 := bbase (se 4 (by rfl) ⟨738243, by rfl⟩ : syracuseStep 7874597 = 1476487) (by norm_num)
theorem B5249731 : Blo 2073435 5249731 := bstep (se 1 (by rfl) ⟨3937298, by rfl⟩ : syracuseStep 5249731 = 7874597) B7874597
theorem B6999641 : Blo 2073435 6999641 := bstep (se 2 (by rfl) ⟨2624865, by rfl⟩ : syracuseStep 6999641 = 5249731) B5249731
theorem B4666427 : Blo 2073435 4666427 := bstep (se 1 (by rfl) ⟨3499820, by rfl⟩ : syracuseStep 4666427 = 6999641) B6999641
theorem B3110951 : Blo 2073435 3110951 := bstep (se 1 (by rfl) ⟨2333213, by rfl⟩ : syracuseStep 3110951 = 4666427) B4666427
theorem B2073967 : Blo 2073435 2073967 := bstep (se 1 (by rfl) ⟨1555475, by rfl⟩ : syracuseStep 2073967 = 3110951) B3110951
theorem B3110957 : Blo 2073435 3110957 := bbase (se 3 (by rfl) ⟨583304, by rfl⟩ : syracuseStep 3110957 = 1166609) (by norm_num)
theorem B2073971 : Blo 2073435 2073971 := bstep (se 1 (by rfl) ⟨1555478, by rfl⟩ : syracuseStep 2073971 = 3110957) B3110957
theorem B4666445 : Blo 2073435 4666445 := bbase (se 3 (by rfl) ⟨874958, by rfl⟩ : syracuseStep 4666445 = 1749917) (by norm_num)
theorem B3110963 : Blo 2073435 3110963 := bstep (se 1 (by rfl) ⟨2333222, by rfl⟩ : syracuseStep 3110963 = 4666445) B4666445
theorem B2073975 : Blo 2073435 2073975 := bstep (se 1 (by rfl) ⟨1555481, by rfl⟩ : syracuseStep 2073975 = 3110963) B3110963
theorem B2624881 : Blo 2073435 2624881 := bbase (se 2 (by rfl) ⟨984330, by rfl⟩ : syracuseStep 2624881 = 1968661) (by norm_num)
theorem B3499841 : Blo 2073435 3499841 := bstep (se 2 (by rfl) ⟨1312440, by rfl⟩ : syracuseStep 3499841 = 2624881) B2624881
theorem B2333227 : Blo 2073435 2333227 := bstep (se 1 (by rfl) ⟨1749920, by rfl⟩ : syracuseStep 2333227 = 3499841) B3499841
theorem B3110969 : Blo 2073435 3110969 := bstep (se 2 (by rfl) ⟨1166613, by rfl⟩ : syracuseStep 3110969 = 2333227) B2333227
theorem B2073979 : Blo 2073435 2073979 := bstep (se 1 (by rfl) ⟨1555484, by rfl⟩ : syracuseStep 2073979 = 3110969) B3110969
theorem B3153421 : Blo 2073435 3153421 := bbase (se 3 (by rfl) ⟨591266, by rfl⟩ : syracuseStep 3153421 = 1182533) (by norm_num)
theorem B4204561 : Blo 2073435 4204561 := bstep (se 2 (by rfl) ⟨1576710, by rfl⟩ : syracuseStep 4204561 = 3153421) B3153421
theorem B5606081 : Blo 2073435 5606081 := bstep (se 2 (by rfl) ⟨2102280, by rfl⟩ : syracuseStep 5606081 = 4204561) B4204561
theorem B3737387 : Blo 2073435 3737387 := bstep (se 1 (by rfl) ⟨2803040, by rfl⟩ : syracuseStep 3737387 = 5606081) B5606081
theorem B9966365 : Blo 2073435 9966365 := bstep (se 3 (by rfl) ⟨1868693, by rfl⟩ : syracuseStep 9966365 = 3737387) B3737387
theorem B6644243 : Blo 2073435 6644243 := bstep (se 1 (by rfl) ⟨4983182, by rfl⟩ : syracuseStep 6644243 = 9966365) B9966365
theorem B4429495 : Blo 2073435 4429495 := bstep (se 1 (by rfl) ⟨3322121, by rfl⟩ : syracuseStep 4429495 = 6644243) B6644243
theorem B23623973 : Blo 2073435 23623973 := bstep (se 4 (by rfl) ⟨2214747, by rfl⟩ : syracuseStep 23623973 = 4429495) B4429495
theorem B15749315 : Blo 2073435 15749315 := bstep (se 1 (by rfl) ⟨11811986, by rfl⟩ : syracuseStep 15749315 = 23623973) B23623973
theorem B10499543 : Blo 2073435 10499543 := bstep (se 1 (by rfl) ⟨7874657, by rfl⟩ : syracuseStep 10499543 = 15749315) B15749315
theorem B6999695 : Blo 2073435 6999695 := bstep (se 1 (by rfl) ⟨5249771, by rfl⟩ : syracuseStep 6999695 = 10499543) B10499543
theorem B4666463 : Blo 2073435 4666463 := bstep (se 1 (by rfl) ⟨3499847, by rfl⟩ : syracuseStep 4666463 = 6999695) B6999695
theorem B3110975 : Blo 2073435 3110975 := bstep (se 1 (by rfl) ⟨2333231, by rfl⟩ : syracuseStep 3110975 = 4666463) B4666463
theorem B2073983 : Blo 2073435 2073983 := bstep (se 1 (by rfl) ⟨1555487, by rfl⟩ : syracuseStep 2073983 = 3110975) B3110975
theorem B3110981 : Blo 2073435 3110981 := bbase (se 4 (by rfl) ⟨291654, by rfl⟩ : syracuseStep 3110981 = 583309) (by norm_num)
theorem B2073987 : Blo 2073435 2073987 := bstep (se 1 (by rfl) ⟨1555490, by rfl⟩ : syracuseStep 2073987 = 3110981) B3110981
theorem B3499861 : Blo 2073435 3499861 := bbase (se 9 (by rfl) ⟨10253, by rfl⟩ : syracuseStep 3499861 = 20507) (by norm_num)
theorem B4666481 : Blo 2073435 4666481 := bstep (se 2 (by rfl) ⟨1749930, by rfl⟩ : syracuseStep 4666481 = 3499861) B3499861
theorem B3110987 : Blo 2073435 3110987 := bstep (se 1 (by rfl) ⟨2333240, by rfl⟩ : syracuseStep 3110987 = 4666481) B4666481
theorem B2073991 : Blo 2073435 2073991 := bstep (se 1 (by rfl) ⟨1555493, by rfl⟩ : syracuseStep 2073991 = 3110987) B3110987
theorem B2333245 : Blo 2073435 2333245 := bbase (se 3 (by rfl) ⟨437483, by rfl⟩ : syracuseStep 2333245 = 874967) (by norm_num)
theorem B3110993 : Blo 2073435 3110993 := bstep (se 2 (by rfl) ⟨1166622, by rfl⟩ : syracuseStep 3110993 = 2333245) B2333245
theorem B2073995 : Blo 2073435 2073995 := bstep (se 1 (by rfl) ⟨1555496, by rfl⟩ : syracuseStep 2073995 = 3110993) B3110993
theorem B6999749 : Blo 2073435 6999749 := bbase (se 4 (by rfl) ⟨656226, by rfl⟩ : syracuseStep 6999749 = 1312453) (by norm_num)
theorem B4666499 : Blo 2073435 4666499 := bstep (se 1 (by rfl) ⟨3499874, by rfl⟩ : syracuseStep 4666499 = 6999749) B6999749
theorem B3110999 : Blo 2073435 3110999 := bstep (se 1 (by rfl) ⟨2333249, by rfl⟩ : syracuseStep 3110999 = 4666499) B4666499
theorem B2073999 : Blo 2073435 2073999 := bstep (se 1 (by rfl) ⟨1555499, by rfl⟩ : syracuseStep 2073999 = 3110999) B3110999
theorem B3111005 : Blo 2073435 3111005 := bbase (se 3 (by rfl) ⟨583313, by rfl⟩ : syracuseStep 3111005 = 1166627) (by norm_num)
theorem B2074003 : Blo 2073435 2074003 := bstep (se 1 (by rfl) ⟨1555502, by rfl⟩ : syracuseStep 2074003 = 3111005) B3111005
theorem B4666517 : Blo 2073435 4666517 := bbase (se 6 (by rfl) ⟨109371, by rfl⟩ : syracuseStep 4666517 = 218743) (by norm_num)
theorem B3111011 : Blo 2073435 3111011 := bstep (se 1 (by rfl) ⟨2333258, by rfl⟩ : syracuseStep 3111011 = 4666517) B4666517
theorem B2074007 : Blo 2073435 2074007 := bstep (se 1 (by rfl) ⟨1555505, by rfl⟩ : syracuseStep 2074007 = 3111011) B3111011
theorem B2953037 : Blo 2073435 2953037 := bbase (se 3 (by rfl) ⟨553694, by rfl⟩ : syracuseStep 2953037 = 1107389) (by norm_num)
theorem B7874765 : Blo 2073435 7874765 := bstep (se 3 (by rfl) ⟨1476518, by rfl⟩ : syracuseStep 7874765 = 2953037) B2953037
theorem B5249843 : Blo 2073435 5249843 := bstep (se 1 (by rfl) ⟨3937382, by rfl⟩ : syracuseStep 5249843 = 7874765) B7874765
theorem B3499895 : Blo 2073435 3499895 := bstep (se 1 (by rfl) ⟨2624921, by rfl⟩ : syracuseStep 3499895 = 5249843) B5249843
theorem B2333263 : Blo 2073435 2333263 := bstep (se 1 (by rfl) ⟨1749947, by rfl⟩ : syracuseStep 2333263 = 3499895) B3499895
theorem B3111017 : Blo 2073435 3111017 := bstep (se 2 (by rfl) ⟨1166631, by rfl⟩ : syracuseStep 3111017 = 2333263) B2333263
theorem B2074011 : Blo 2073435 2074011 := bstep (se 1 (by rfl) ⟨1555508, by rfl⟩ : syracuseStep 2074011 = 3111017) B3111017
theorem B12613877 : Blo 2073435 12613877 := bbase (se 5 (by rfl) ⟨591275, by rfl⟩ : syracuseStep 12613877 = 1182551) (by norm_num)
theorem B8409251 : Blo 2073435 8409251 := bstep (se 1 (by rfl) ⟨6306938, by rfl⟩ : syracuseStep 8409251 = 12613877) B12613877
theorem B5606167 : Blo 2073435 5606167 := bstep (se 1 (by rfl) ⟨4204625, by rfl⟩ : syracuseStep 5606167 = 8409251) B8409251
theorem B7474889 : Blo 2073435 7474889 := bstep (se 2 (by rfl) ⟨2803083, by rfl⟩ : syracuseStep 7474889 = 5606167) B5606167
theorem B19933037 : Blo 2073435 19933037 := bstep (se 3 (by rfl) ⟨3737444, by rfl⟩ : syracuseStep 19933037 = 7474889) B7474889
theorem B13288691 : Blo 2073435 13288691 := bstep (se 1 (by rfl) ⟨9966518, by rfl⟩ : syracuseStep 13288691 = 19933037) B19933037
theorem B8859127 : Blo 2073435 8859127 := bstep (se 1 (by rfl) ⟨6644345, by rfl⟩ : syracuseStep 8859127 = 13288691) B13288691
theorem B11812169 : Blo 2073435 11812169 := bstep (se 2 (by rfl) ⟨4429563, by rfl⟩ : syracuseStep 11812169 = 8859127) B8859127
theorem B7874779 : Blo 2073435 7874779 := bstep (se 1 (by rfl) ⟨5906084, by rfl⟩ : syracuseStep 7874779 = 11812169) B11812169
theorem B10499705 : Blo 2073435 10499705 := bstep (se 2 (by rfl) ⟨3937389, by rfl⟩ : syracuseStep 10499705 = 7874779) B7874779
theorem B6999803 : Blo 2073435 6999803 := bstep (se 1 (by rfl) ⟨5249852, by rfl⟩ : syracuseStep 6999803 = 10499705) B10499705
theorem B4666535 : Blo 2073435 4666535 := bstep (se 1 (by rfl) ⟨3499901, by rfl⟩ : syracuseStep 4666535 = 6999803) B6999803
theorem B3111023 : Blo 2073435 3111023 := bstep (se 1 (by rfl) ⟨2333267, by rfl⟩ : syracuseStep 3111023 = 4666535) B4666535
theorem B2074015 : Blo 2073435 2074015 := bstep (se 1 (by rfl) ⟨1555511, by rfl⟩ : syracuseStep 2074015 = 3111023) B3111023
theorem B3111029 : Blo 2073435 3111029 := bbase (se 5 (by rfl) ⟨145829, by rfl⟩ : syracuseStep 3111029 = 291659) (by norm_num)
theorem B2074019 : Blo 2073435 2074019 := bstep (se 1 (by rfl) ⟨1555514, by rfl⟩ : syracuseStep 2074019 = 3111029) B3111029
theorem B3937405 : Blo 2073435 3937405 := bbase (se 3 (by rfl) ⟨738263, by rfl⟩ : syracuseStep 3937405 = 1476527) (by norm_num)
theorem B5249873 : Blo 2073435 5249873 := bstep (se 2 (by rfl) ⟨1968702, by rfl⟩ : syracuseStep 5249873 = 3937405) B3937405
theorem B3499915 : Blo 2073435 3499915 := bstep (se 1 (by rfl) ⟨2624936, by rfl⟩ : syracuseStep 3499915 = 5249873) B5249873
theorem B4666553 : Blo 2073435 4666553 := bstep (se 2 (by rfl) ⟨1749957, by rfl⟩ : syracuseStep 4666553 = 3499915) B3499915
theorem B3111035 : Blo 2073435 3111035 := bstep (se 1 (by rfl) ⟨2333276, by rfl⟩ : syracuseStep 3111035 = 4666553) B4666553
theorem B2074023 : Blo 2073435 2074023 := bstep (se 1 (by rfl) ⟨1555517, by rfl⟩ : syracuseStep 2074023 = 3111035) B3111035
theorem B2333281 : Blo 2073435 2333281 := bbase (se 2 (by rfl) ⟨874980, by rfl⟩ : syracuseStep 2333281 = 1749961) (by norm_num)
theorem B3111041 : Blo 2073435 3111041 := bstep (se 2 (by rfl) ⟨1166640, by rfl⟩ : syracuseStep 3111041 = 2333281) B2333281
theorem B2074027 : Blo 2073435 2074027 := bstep (se 1 (by rfl) ⟨1555520, by rfl⟩ : syracuseStep 2074027 = 3111041) B3111041
theorem B5249893 : Blo 2073435 5249893 := bbase (se 4 (by rfl) ⟨492177, by rfl⟩ : syracuseStep 5249893 = 984355) (by norm_num)
theorem B6999857 : Blo 2073435 6999857 := bstep (se 2 (by rfl) ⟨2624946, by rfl⟩ : syracuseStep 6999857 = 5249893) B5249893
theorem B4666571 : Blo 2073435 4666571 := bstep (se 1 (by rfl) ⟨3499928, by rfl⟩ : syracuseStep 4666571 = 6999857) B6999857
theorem B3111047 : Blo 2073435 3111047 := bstep (se 1 (by rfl) ⟨2333285, by rfl⟩ : syracuseStep 3111047 = 4666571) B4666571
theorem B2074031 : Blo 2073435 2074031 := bstep (se 1 (by rfl) ⟨1555523, by rfl⟩ : syracuseStep 2074031 = 3111047) B3111047
theorem B3111053 : Blo 2073435 3111053 := bbase (se 3 (by rfl) ⟨583322, by rfl⟩ : syracuseStep 3111053 = 1166645) (by norm_num)
theorem B2074035 : Blo 2073435 2074035 := bstep (se 1 (by rfl) ⟨1555526, by rfl⟩ : syracuseStep 2074035 = 3111053) B3111053
theorem B4666589 : Blo 2073435 4666589 := bbase (se 3 (by rfl) ⟨874985, by rfl⟩ : syracuseStep 4666589 = 1749971) (by norm_num)
theorem B3111059 : Blo 2073435 3111059 := bstep (se 1 (by rfl) ⟨2333294, by rfl⟩ : syracuseStep 3111059 = 4666589) B4666589
theorem B2074039 : Blo 2073435 2074039 := bstep (se 1 (by rfl) ⟨1555529, by rfl⟩ : syracuseStep 2074039 = 3111059) B3111059
theorem B3499949 : Blo 2073435 3499949 := bbase (se 3 (by rfl) ⟨656240, by rfl⟩ : syracuseStep 3499949 = 1312481) (by norm_num)
theorem B2333299 : Blo 2073435 2333299 := bstep (se 1 (by rfl) ⟨1749974, by rfl⟩ : syracuseStep 2333299 = 3499949) B3499949
theorem B3111065 : Blo 2073435 3111065 := bstep (se 2 (by rfl) ⟨1166649, by rfl⟩ : syracuseStep 3111065 = 2333299) B2333299
theorem B2074043 : Blo 2073435 2074043 := bstep (se 1 (by rfl) ⟨1555532, by rfl⟩ : syracuseStep 2074043 = 3111065) B3111065
theorem B574728533 : Blo 2073435 574728533 := bbase (se 10 (by rfl) ⟨841887, by rfl⟩ : syracuseStep 574728533 = 1683775) (by norm_num)
theorem B383152355 : Blo 2073435 383152355 := bstep (se 1 (by rfl) ⟨287364266, by rfl⟩ : syracuseStep 383152355 = 574728533) B574728533
theorem B255434903 : Blo 2073435 255434903 := bstep (se 1 (by rfl) ⟨191576177, by rfl⟩ : syracuseStep 255434903 = 383152355) B383152355
theorem B170289935 : Blo 2073435 170289935 := bstep (se 1 (by rfl) ⟨127717451, by rfl⟩ : syracuseStep 170289935 = 255434903) B255434903
theorem B113526623 : Blo 2073435 113526623 := bstep (se 1 (by rfl) ⟨85144967, by rfl⟩ : syracuseStep 113526623 = 170289935) B170289935
theorem B302737661 : Blo 2073435 302737661 := bstep (se 3 (by rfl) ⟨56763311, by rfl⟩ : syracuseStep 302737661 = 113526623) B113526623
theorem B201825107 : Blo 2073435 201825107 := bstep (se 1 (by rfl) ⟨151368830, by rfl⟩ : syracuseStep 201825107 = 302737661) B302737661
theorem B134550071 : Blo 2073435 134550071 := bstep (se 1 (by rfl) ⟨100912553, by rfl⟩ : syracuseStep 134550071 = 201825107) B201825107
theorem B89700047 : Blo 2073435 89700047 := bstep (se 1 (by rfl) ⟨67275035, by rfl⟩ : syracuseStep 89700047 = 134550071) B134550071
theorem B59800031 : Blo 2073435 59800031 := bstep (se 1 (by rfl) ⟨44850023, by rfl⟩ : syracuseStep 59800031 = 89700047) B89700047
theorem B39866687 : Blo 2073435 39866687 := bstep (se 1 (by rfl) ⟨29900015, by rfl⟩ : syracuseStep 39866687 = 59800031) B59800031
theorem B26577791 : Blo 2073435 26577791 := bstep (se 1 (by rfl) ⟨19933343, by rfl⟩ : syracuseStep 26577791 = 39866687) B39866687
theorem B17718527 : Blo 2073435 17718527 := bstep (se 1 (by rfl) ⟨13288895, by rfl⟩ : syracuseStep 17718527 = 26577791) B26577791
theorem B11812351 : Blo 2073435 11812351 := bstep (se 1 (by rfl) ⟨8859263, by rfl⟩ : syracuseStep 11812351 = 17718527) B17718527
theorem B15749801 : Blo 2073435 15749801 := bstep (se 2 (by rfl) ⟨5906175, by rfl⟩ : syracuseStep 15749801 = 11812351) B11812351
theorem B10499867 : Blo 2073435 10499867 := bstep (se 1 (by rfl) ⟨7874900, by rfl⟩ : syracuseStep 10499867 = 15749801) B15749801
theorem B6999911 : Blo 2073435 6999911 := bstep (se 1 (by rfl) ⟨5249933, by rfl⟩ : syracuseStep 6999911 = 10499867) B10499867
theorem B4666607 : Blo 2073435 4666607 := bstep (se 1 (by rfl) ⟨3499955, by rfl⟩ : syracuseStep 4666607 = 6999911) B6999911
theorem B3111071 : Blo 2073435 3111071 := bstep (se 1 (by rfl) ⟨2333303, by rfl⟩ : syracuseStep 3111071 = 4666607) B4666607
theorem B2074047 : Blo 2073435 2074047 := bstep (se 1 (by rfl) ⟨1555535, by rfl⟩ : syracuseStep 2074047 = 3111071) B3111071
theorem B3111077 : Blo 2073435 3111077 := bbase (se 4 (by rfl) ⟨291663, by rfl⟩ : syracuseStep 3111077 = 583327) (by norm_num)
theorem B2074051 : Blo 2073435 2074051 := bstep (se 1 (by rfl) ⟨1555538, by rfl⟩ : syracuseStep 2074051 = 3111077) B3111077
theorem B2624977 : Blo 2073435 2624977 := bbase (se 2 (by rfl) ⟨984366, by rfl⟩ : syracuseStep 2624977 = 1968733) (by norm_num)
theorem B3499969 : Blo 2073435 3499969 := bstep (se 2 (by rfl) ⟨1312488, by rfl⟩ : syracuseStep 3499969 = 2624977) B2624977
theorem B4666625 : Blo 2073435 4666625 := bstep (se 2 (by rfl) ⟨1749984, by rfl⟩ : syracuseStep 4666625 = 3499969) B3499969
theorem B3111083 : Blo 2073435 3111083 := bstep (se 1 (by rfl) ⟨2333312, by rfl⟩ : syracuseStep 3111083 = 4666625) B4666625
theorem B2074055 : Blo 2073435 2074055 := bstep (se 1 (by rfl) ⟨1555541, by rfl⟩ : syracuseStep 2074055 = 3111083) B3111083
theorem B2333317 : Blo 2073435 2333317 := bbase (se 4 (by rfl) ⟨218748, by rfl⟩ : syracuseStep 2333317 = 437497) (by norm_num)
theorem B3111089 : Blo 2073435 3111089 := bstep (se 2 (by rfl) ⟨1166658, by rfl⟩ : syracuseStep 3111089 = 2333317) B2333317
theorem B2074059 : Blo 2073435 2074059 := bstep (se 1 (by rfl) ⟨1555544, by rfl⟩ : syracuseStep 2074059 = 3111089) B3111089
theorem B6644501 : Blo 2073435 6644501 := bbase (se 6 (by rfl) ⟨155730, by rfl⟩ : syracuseStep 6644501 = 311461) (by norm_num)
theorem B4429667 : Blo 2073435 4429667 := bstep (se 1 (by rfl) ⟨3322250, by rfl⟩ : syracuseStep 4429667 = 6644501) B6644501
theorem B2953111 : Blo 2073435 2953111 := bstep (se 1 (by rfl) ⟨2214833, by rfl⟩ : syracuseStep 2953111 = 4429667) B4429667
theorem B3937481 : Blo 2073435 3937481 := bstep (se 2 (by rfl) ⟨1476555, by rfl⟩ : syracuseStep 3937481 = 2953111) B2953111
theorem B2624987 : Blo 2073435 2624987 := bstep (se 1 (by rfl) ⟨1968740, by rfl⟩ : syracuseStep 2624987 = 3937481) B3937481
theorem B6999965 : Blo 2073435 6999965 := bstep (se 3 (by rfl) ⟨1312493, by rfl⟩ : syracuseStep 6999965 = 2624987) B2624987
theorem B4666643 : Blo 2073435 4666643 := bstep (se 1 (by rfl) ⟨3499982, by rfl⟩ : syracuseStep 4666643 = 6999965) B6999965
theorem B3111095 : Blo 2073435 3111095 := bstep (se 1 (by rfl) ⟨2333321, by rfl⟩ : syracuseStep 3111095 = 4666643) B4666643
theorem B2074063 : Blo 2073435 2074063 := bstep (se 1 (by rfl) ⟨1555547, by rfl⟩ : syracuseStep 2074063 = 3111095) B3111095
theorem B3111101 : Blo 2073435 3111101 := bbase (se 3 (by rfl) ⟨583331, by rfl⟩ : syracuseStep 3111101 = 1166663) (by norm_num)
theorem B2074067 : Blo 2073435 2074067 := bstep (se 1 (by rfl) ⟨1555550, by rfl⟩ : syracuseStep 2074067 = 3111101) B3111101
theorem B4666661 : Blo 2073435 4666661 := bbase (se 4 (by rfl) ⟨437499, by rfl⟩ : syracuseStep 4666661 = 874999) (by norm_num)
theorem B3111107 : Blo 2073435 3111107 := bstep (se 1 (by rfl) ⟨2333330, by rfl⟩ : syracuseStep 3111107 = 4666661) B4666661
theorem B2074071 : Blo 2073435 2074071 := bstep (se 1 (by rfl) ⟨1555553, by rfl⟩ : syracuseStep 2074071 = 3111107) B3111107
theorem B5250005 : Blo 2073435 5250005 := bbase (se 7 (by rfl) ⟨61523, by rfl⟩ : syracuseStep 5250005 = 123047) (by norm_num)
theorem B3500003 : Blo 2073435 3500003 := bstep (se 1 (by rfl) ⟨2625002, by rfl⟩ : syracuseStep 3500003 = 5250005) B5250005
theorem B2333335 : Blo 2073435 2333335 := bstep (se 1 (by rfl) ⟨1750001, by rfl⟩ : syracuseStep 2333335 = 3500003) B3500003
theorem B3111113 : Blo 2073435 3111113 := bstep (se 2 (by rfl) ⟨1166667, by rfl⟩ : syracuseStep 3111113 = 2333335) B2333335
theorem B2074075 : Blo 2073435 2074075 := bstep (se 1 (by rfl) ⟨1555556, by rfl⟩ : syracuseStep 2074075 = 3111113) B3111113
theorem B2245069 : Blo 2073435 2245069 := bbase (se 3 (by rfl) ⟨420950, by rfl⟩ : syracuseStep 2245069 = 841901) (by norm_num)
theorem B2993425 : Blo 2073435 2993425 := bstep (se 2 (by rfl) ⟨1122534, by rfl⟩ : syracuseStep 2993425 = 2245069) B2245069
theorem B15964933 : Blo 2073435 15964933 := bstep (se 4 (by rfl) ⟨1496712, by rfl⟩ : syracuseStep 15964933 = 2993425) B2993425
theorem B21286577 : Blo 2073435 21286577 := bstep (se 2 (by rfl) ⟨7982466, by rfl⟩ : syracuseStep 21286577 = 15964933) B15964933
theorem B14191051 : Blo 2073435 14191051 := bstep (se 1 (by rfl) ⟨10643288, by rfl⟩ : syracuseStep 14191051 = 21286577) B21286577
theorem B18921401 : Blo 2073435 18921401 := bstep (se 2 (by rfl) ⟨7095525, by rfl⟩ : syracuseStep 18921401 = 14191051) B14191051
theorem B12614267 : Blo 2073435 12614267 := bstep (se 1 (by rfl) ⟨9460700, by rfl⟩ : syracuseStep 12614267 = 18921401) B18921401
theorem B8409511 : Blo 2073435 8409511 := bstep (se 1 (by rfl) ⟨6307133, by rfl⟩ : syracuseStep 8409511 = 12614267) B12614267
theorem B11212681 : Blo 2073435 11212681 := bstep (se 2 (by rfl) ⟨4204755, by rfl⟩ : syracuseStep 11212681 = 8409511) B8409511
theorem B14950241 : Blo 2073435 14950241 := bstep (se 2 (by rfl) ⟨5606340, by rfl⟩ : syracuseStep 14950241 = 11212681) B11212681
theorem B9966827 : Blo 2073435 9966827 := bstep (se 1 (by rfl) ⟨7475120, by rfl⟩ : syracuseStep 9966827 = 14950241) B14950241
theorem B6644551 : Blo 2073435 6644551 := bstep (se 1 (by rfl) ⟨4983413, by rfl⟩ : syracuseStep 6644551 = 9966827) B9966827
theorem B8859401 : Blo 2073435 8859401 := bstep (se 2 (by rfl) ⟨3322275, by rfl⟩ : syracuseStep 8859401 = 6644551) B6644551
theorem B5906267 : Blo 2073435 5906267 := bstep (se 1 (by rfl) ⟨4429700, by rfl⟩ : syracuseStep 5906267 = 8859401) B8859401
theorem B3937511 : Blo 2073435 3937511 := bstep (se 1 (by rfl) ⟨2953133, by rfl⟩ : syracuseStep 3937511 = 5906267) B5906267
theorem B10500029 : Blo 2073435 10500029 := bstep (se 3 (by rfl) ⟨1968755, by rfl⟩ : syracuseStep 10500029 = 3937511) B3937511
theorem B7000019 : Blo 2073435 7000019 := bstep (se 1 (by rfl) ⟨5250014, by rfl⟩ : syracuseStep 7000019 = 10500029) B10500029
theorem B4666679 : Blo 2073435 4666679 := bstep (se 1 (by rfl) ⟨3500009, by rfl⟩ : syracuseStep 4666679 = 7000019) B7000019
theorem B3111119 : Blo 2073435 3111119 := bstep (se 1 (by rfl) ⟨2333339, by rfl⟩ : syracuseStep 3111119 = 4666679) B4666679
theorem B2074079 : Blo 2073435 2074079 := bstep (se 1 (by rfl) ⟨1555559, by rfl⟩ : syracuseStep 2074079 = 3111119) B3111119
theorem B3111125 : Blo 2073435 3111125 := bbase (se 7 (by rfl) ⟨36458, by rfl⟩ : syracuseStep 3111125 = 72917) (by norm_num)
theorem B2074083 : Blo 2073435 2074083 := bstep (se 1 (by rfl) ⟨1555562, by rfl⟩ : syracuseStep 2074083 = 3111125) B3111125
theorem B2491717 : Blo 2073435 2491717 := bbase (se 4 (by rfl) ⟨233598, by rfl⟩ : syracuseStep 2491717 = 467197) (by norm_num)
theorem B3322289 : Blo 2073435 3322289 := bstep (se 2 (by rfl) ⟨1245858, by rfl⟩ : syracuseStep 3322289 = 2491717) B2491717
theorem B2214859 : Blo 2073435 2214859 := bstep (se 1 (by rfl) ⟨1661144, by rfl⟩ : syracuseStep 2214859 = 3322289) B3322289
theorem B2953145 : Blo 2073435 2953145 := bstep (se 2 (by rfl) ⟨1107429, by rfl⟩ : syracuseStep 2953145 = 2214859) B2214859
theorem B7875053 : Blo 2073435 7875053 := bstep (se 3 (by rfl) ⟨1476572, by rfl⟩ : syracuseStep 7875053 = 2953145) B2953145
theorem B5250035 : Blo 2073435 5250035 := bstep (se 1 (by rfl) ⟨3937526, by rfl⟩ : syracuseStep 5250035 = 7875053) B7875053
theorem B3500023 : Blo 2073435 3500023 := bstep (se 1 (by rfl) ⟨2625017, by rfl⟩ : syracuseStep 3500023 = 5250035) B5250035
theorem B4666697 : Blo 2073435 4666697 := bstep (se 2 (by rfl) ⟨1750011, by rfl⟩ : syracuseStep 4666697 = 3500023) B3500023
theorem B3111131 : Blo 2073435 3111131 := bstep (se 1 (by rfl) ⟨2333348, by rfl⟩ : syracuseStep 3111131 = 4666697) B4666697
theorem B2074087 : Blo 2073435 2074087 := bstep (se 1 (by rfl) ⟨1555565, by rfl⟩ : syracuseStep 2074087 = 3111131) B3111131
theorem B2333353 : Blo 2073435 2333353 := bbase (se 2 (by rfl) ⟨875007, by rfl⟩ : syracuseStep 2333353 = 1750015) (by norm_num)
theorem B3111137 : Blo 2073435 3111137 := bstep (se 2 (by rfl) ⟨1166676, by rfl⟩ : syracuseStep 3111137 = 2333353) B2333353
theorem B2074091 : Blo 2073435 2074091 := bstep (se 1 (by rfl) ⟨1555568, by rfl⟩ : syracuseStep 2074091 = 3111137) B3111137
theorem B3322301 : Blo 2073435 3322301 := bbase (se 3 (by rfl) ⟨622931, by rfl⟩ : syracuseStep 3322301 = 1245863) (by norm_num)
theorem B8859469 : Blo 2073435 8859469 := bstep (se 3 (by rfl) ⟨1661150, by rfl⟩ : syracuseStep 8859469 = 3322301) B3322301
theorem B11812625 : Blo 2073435 11812625 := bstep (se 2 (by rfl) ⟨4429734, by rfl⟩ : syracuseStep 11812625 = 8859469) B8859469
theorem B7875083 : Blo 2073435 7875083 := bstep (se 1 (by rfl) ⟨5906312, by rfl⟩ : syracuseStep 7875083 = 11812625) B11812625
theorem B5250055 : Blo 2073435 5250055 := bstep (se 1 (by rfl) ⟨3937541, by rfl⟩ : syracuseStep 5250055 = 7875083) B7875083
theorem B7000073 : Blo 2073435 7000073 := bstep (se 2 (by rfl) ⟨2625027, by rfl⟩ : syracuseStep 7000073 = 5250055) B5250055
theorem B4666715 : Blo 2073435 4666715 := bstep (se 1 (by rfl) ⟨3500036, by rfl⟩ : syracuseStep 4666715 = 7000073) B7000073
theorem B3111143 : Blo 2073435 3111143 := bstep (se 1 (by rfl) ⟨2333357, by rfl⟩ : syracuseStep 3111143 = 4666715) B4666715
theorem B2074095 : Blo 2073435 2074095 := bstep (se 1 (by rfl) ⟨1555571, by rfl⟩ : syracuseStep 2074095 = 3111143) B3111143
theorem B3111149 : Blo 2073435 3111149 := bbase (se 3 (by rfl) ⟨583340, by rfl⟩ : syracuseStep 3111149 = 1166681) (by norm_num)
theorem B2074099 : Blo 2073435 2074099 := bstep (se 1 (by rfl) ⟨1555574, by rfl⟩ : syracuseStep 2074099 = 3111149) B3111149
theorem B4666733 : Blo 2073435 4666733 := bbase (se 3 (by rfl) ⟨875012, by rfl⟩ : syracuseStep 4666733 = 1750025) (by norm_num)
theorem B3111155 : Blo 2073435 3111155 := bstep (se 1 (by rfl) ⟨2333366, by rfl⟩ : syracuseStep 3111155 = 4666733) B4666733
theorem B2074103 : Blo 2073435 2074103 := bstep (se 1 (by rfl) ⟨1555577, by rfl⟩ : syracuseStep 2074103 = 3111155) B3111155
theorem B3937565 : Blo 2073435 3937565 := bbase (se 3 (by rfl) ⟨738293, by rfl⟩ : syracuseStep 3937565 = 1476587) (by norm_num)
theorem B2625043 : Blo 2073435 2625043 := bstep (se 1 (by rfl) ⟨1968782, by rfl⟩ : syracuseStep 2625043 = 3937565) B3937565
theorem B3500057 : Blo 2073435 3500057 := bstep (se 2 (by rfl) ⟨1312521, by rfl⟩ : syracuseStep 3500057 = 2625043) B2625043
theorem B2333371 : Blo 2073435 2333371 := bstep (se 1 (by rfl) ⟨1750028, by rfl⟩ : syracuseStep 2333371 = 3500057) B3500057
theorem B3111161 : Blo 2073435 3111161 := bstep (se 2 (by rfl) ⟨1166685, by rfl⟩ : syracuseStep 3111161 = 2333371) B2333371
theorem B2074107 : Blo 2073435 2074107 := bstep (se 1 (by rfl) ⟨1555580, by rfl⟩ : syracuseStep 2074107 = 3111161) B3111161
theorem B2803213 : Blo 2073435 2803213 := bbase (se 3 (by rfl) ⟨525602, by rfl⟩ : syracuseStep 2803213 = 1051205) (by norm_num)
theorem B14950469 : Blo 2073435 14950469 := bstep (se 4 (by rfl) ⟨1401606, by rfl⟩ : syracuseStep 14950469 = 2803213) B2803213
theorem B9966979 : Blo 2073435 9966979 := bstep (se 1 (by rfl) ⟨7475234, by rfl⟩ : syracuseStep 9966979 = 14950469) B14950469
theorem B53157221 : Blo 2073435 53157221 := bstep (se 4 (by rfl) ⟨4983489, by rfl⟩ : syracuseStep 53157221 = 9966979) B9966979
theorem B35438147 : Blo 2073435 35438147 := bstep (se 1 (by rfl) ⟨26578610, by rfl⟩ : syracuseStep 35438147 = 53157221) B53157221
theorem B23625431 : Blo 2073435 23625431 := bstep (se 1 (by rfl) ⟨17719073, by rfl⟩ : syracuseStep 23625431 = 35438147) B35438147
theorem B15750287 : Blo 2073435 15750287 := bstep (se 1 (by rfl) ⟨11812715, by rfl⟩ : syracuseStep 15750287 = 23625431) B23625431
theorem B10500191 : Blo 2073435 10500191 := bstep (se 1 (by rfl) ⟨7875143, by rfl⟩ : syracuseStep 10500191 = 15750287) B15750287
theorem B7000127 : Blo 2073435 7000127 := bstep (se 1 (by rfl) ⟨5250095, by rfl⟩ : syracuseStep 7000127 = 10500191) B10500191
theorem B4666751 : Blo 2073435 4666751 := bstep (se 1 (by rfl) ⟨3500063, by rfl⟩ : syracuseStep 4666751 = 7000127) B7000127
theorem B3111167 : Blo 2073435 3111167 := bstep (se 1 (by rfl) ⟨2333375, by rfl⟩ : syracuseStep 3111167 = 4666751) B4666751
theorem B2074111 : Blo 2073435 2074111 := bstep (se 1 (by rfl) ⟨1555583, by rfl⟩ : syracuseStep 2074111 = 3111167) B3111167
theorem B3111173 : Blo 2073435 3111173 := bbase (se 4 (by rfl) ⟨291672, by rfl⟩ : syracuseStep 3111173 = 583345) (by norm_num)
theorem B2074115 : Blo 2073435 2074115 := bstep (se 1 (by rfl) ⟨1555586, by rfl⟩ : syracuseStep 2074115 = 3111173) B3111173
theorem B3500077 : Blo 2073435 3500077 := bbase (se 3 (by rfl) ⟨656264, by rfl⟩ : syracuseStep 3500077 = 1312529) (by norm_num)
theorem B4666769 : Blo 2073435 4666769 := bstep (se 2 (by rfl) ⟨1750038, by rfl⟩ : syracuseStep 4666769 = 3500077) B3500077
theorem B3111179 : Blo 2073435 3111179 := bstep (se 1 (by rfl) ⟨2333384, by rfl⟩ : syracuseStep 3111179 = 4666769) B4666769
theorem B2074119 : Blo 2073435 2074119 := bstep (se 1 (by rfl) ⟨1555589, by rfl⟩ : syracuseStep 2074119 = 3111179) B3111179
theorem B2333389 : Blo 2073435 2333389 := bbase (se 3 (by rfl) ⟨437510, by rfl⟩ : syracuseStep 2333389 = 875021) (by norm_num)
theorem B3111185 : Blo 2073435 3111185 := bstep (se 2 (by rfl) ⟨1166694, by rfl⟩ : syracuseStep 3111185 = 2333389) B2333389
theorem B2074123 : Blo 2073435 2074123 := bstep (se 1 (by rfl) ⟨1555592, by rfl⟩ : syracuseStep 2074123 = 3111185) B3111185
theorem B7000181 : Blo 2073435 7000181 := bbase (se 5 (by rfl) ⟨328133, by rfl⟩ : syracuseStep 7000181 = 656267) (by norm_num)
theorem B4666787 : Blo 2073435 4666787 := bstep (se 1 (by rfl) ⟨3500090, by rfl⟩ : syracuseStep 4666787 = 7000181) B7000181
theorem B3111191 : Blo 2073435 3111191 := bstep (se 1 (by rfl) ⟨2333393, by rfl⟩ : syracuseStep 3111191 = 4666787) B4666787
theorem B2074127 : Blo 2073435 2074127 := bstep (se 1 (by rfl) ⟨1555595, by rfl⟩ : syracuseStep 2074127 = 3111191) B3111191
theorem B3111197 : Blo 2073435 3111197 := bbase (se 3 (by rfl) ⟨583349, by rfl⟩ : syracuseStep 3111197 = 1166699) (by norm_num)
theorem B2074131 : Blo 2073435 2074131 := bstep (se 1 (by rfl) ⟨1555598, by rfl⟩ : syracuseStep 2074131 = 3111197) B3111197
theorem B4666805 : Blo 2073435 4666805 := bbase (se 5 (by rfl) ⟨218756, by rfl⟩ : syracuseStep 4666805 = 437513) (by norm_num)
theorem B3111203 : Blo 2073435 3111203 := bstep (se 1 (by rfl) ⟨2333402, by rfl⟩ : syracuseStep 3111203 = 4666805) B4666805
theorem B2074135 : Blo 2073435 2074135 := bstep (se 1 (by rfl) ⟨1555601, by rfl⟩ : syracuseStep 2074135 = 3111203) B3111203
theorem B4429829 : Blo 2073435 4429829 := bbase (se 4 (by rfl) ⟨415296, by rfl⟩ : syracuseStep 4429829 = 830593) (by norm_num)
theorem B11812877 : Blo 2073435 11812877 := bstep (se 3 (by rfl) ⟨2214914, by rfl⟩ : syracuseStep 11812877 = 4429829) B4429829
theorem B7875251 : Blo 2073435 7875251 := bstep (se 1 (by rfl) ⟨5906438, by rfl⟩ : syracuseStep 7875251 = 11812877) B11812877
theorem B5250167 : Blo 2073435 5250167 := bstep (se 1 (by rfl) ⟨3937625, by rfl⟩ : syracuseStep 5250167 = 7875251) B7875251
theorem B3500111 : Blo 2073435 3500111 := bstep (se 1 (by rfl) ⟨2625083, by rfl⟩ : syracuseStep 3500111 = 5250167) B5250167
theorem B2333407 : Blo 2073435 2333407 := bstep (se 1 (by rfl) ⟨1750055, by rfl⟩ : syracuseStep 2333407 = 3500111) B3500111
theorem B3111209 : Blo 2073435 3111209 := bstep (se 2 (by rfl) ⟨1166703, by rfl⟩ : syracuseStep 3111209 = 2333407) B2333407
theorem B2074139 : Blo 2073435 2074139 := bstep (se 1 (by rfl) ⟨1555604, by rfl⟩ : syracuseStep 2074139 = 3111209) B3111209
theorem B4429837 : Blo 2073435 4429837 := bbase (se 3 (by rfl) ⟨830594, by rfl⟩ : syracuseStep 4429837 = 1661189) (by norm_num)
theorem B5906449 : Blo 2073435 5906449 := bstep (se 2 (by rfl) ⟨2214918, by rfl⟩ : syracuseStep 5906449 = 4429837) B4429837
theorem B7875265 : Blo 2073435 7875265 := bstep (se 2 (by rfl) ⟨2953224, by rfl⟩ : syracuseStep 7875265 = 5906449) B5906449
theorem B10500353 : Blo 2073435 10500353 := bstep (se 2 (by rfl) ⟨3937632, by rfl⟩ : syracuseStep 10500353 = 7875265) B7875265
theorem B7000235 : Blo 2073435 7000235 := bstep (se 1 (by rfl) ⟨5250176, by rfl⟩ : syracuseStep 7000235 = 10500353) B10500353
theorem B4666823 : Blo 2073435 4666823 := bstep (se 1 (by rfl) ⟨3500117, by rfl⟩ : syracuseStep 4666823 = 7000235) B7000235
theorem B3111215 : Blo 2073435 3111215 := bstep (se 1 (by rfl) ⟨2333411, by rfl⟩ : syracuseStep 3111215 = 4666823) B4666823
theorem B2074143 : Blo 2073435 2074143 := bstep (se 1 (by rfl) ⟨1555607, by rfl⟩ : syracuseStep 2074143 = 3111215) B3111215
theorem B3111221 : Blo 2073435 3111221 := bbase (se 5 (by rfl) ⟨145838, by rfl⟩ : syracuseStep 3111221 = 291677) (by norm_num)
theorem B2074147 : Blo 2073435 2074147 := bstep (se 1 (by rfl) ⟨1555610, by rfl⟩ : syracuseStep 2074147 = 3111221) B3111221
theorem B5250197 : Blo 2073435 5250197 := bbase (se 6 (by rfl) ⟨123051, by rfl⟩ : syracuseStep 5250197 = 246103) (by norm_num)
theorem B3500131 : Blo 2073435 3500131 := bstep (se 1 (by rfl) ⟨2625098, by rfl⟩ : syracuseStep 3500131 = 5250197) B5250197
theorem B4666841 : Blo 2073435 4666841 := bstep (se 2 (by rfl) ⟨1750065, by rfl⟩ : syracuseStep 4666841 = 3500131) B3500131
theorem B3111227 : Blo 2073435 3111227 := bstep (se 1 (by rfl) ⟨2333420, by rfl⟩ : syracuseStep 3111227 = 4666841) B4666841
theorem B2074151 : Blo 2073435 2074151 := bstep (se 1 (by rfl) ⟨1555613, by rfl⟩ : syracuseStep 2074151 = 3111227) B3111227
theorem B2333425 : Blo 2073435 2333425 := bbase (se 2 (by rfl) ⟨875034, by rfl⟩ : syracuseStep 2333425 = 1750069) (by norm_num)
theorem B3111233 : Blo 2073435 3111233 := bstep (se 2 (by rfl) ⟨1166712, by rfl⟩ : syracuseStep 3111233 = 2333425) B2333425
theorem B2074155 : Blo 2073435 2074155 := bstep (se 1 (by rfl) ⟨1555616, by rfl⟩ : syracuseStep 2074155 = 3111233) B3111233
theorem B7192613 : Blo 2073435 7192613 := bbase (se 4 (by rfl) ⟨674307, by rfl⟩ : syracuseStep 7192613 = 1348615) (by norm_num)
theorem B4795075 : Blo 2073435 4795075 := bstep (se 1 (by rfl) ⟨3596306, by rfl⟩ : syracuseStep 4795075 = 7192613) B7192613
theorem B6393433 : Blo 2073435 6393433 := bstep (se 2 (by rfl) ⟨2397537, by rfl⟩ : syracuseStep 6393433 = 4795075) B4795075
theorem B8524577 : Blo 2073435 8524577 := bstep (se 2 (by rfl) ⟨3196716, by rfl⟩ : syracuseStep 8524577 = 6393433) B6393433
theorem B5683051 : Blo 2073435 5683051 := bstep (se 1 (by rfl) ⟨4262288, by rfl⟩ : syracuseStep 5683051 = 8524577) B8524577
theorem B7577401 : Blo 2073435 7577401 := bstep (se 2 (by rfl) ⟨2841525, by rfl⟩ : syracuseStep 7577401 = 5683051) B5683051
theorem B10103201 : Blo 2073435 10103201 := bstep (se 2 (by rfl) ⟨3788700, by rfl⟩ : syracuseStep 10103201 = 7577401) B7577401
theorem B6735467 : Blo 2073435 6735467 := bstep (se 1 (by rfl) ⟨5051600, by rfl⟩ : syracuseStep 6735467 = 10103201) B10103201
theorem B4490311 : Blo 2073435 4490311 := bstep (se 1 (by rfl) ⟨3367733, by rfl⟩ : syracuseStep 4490311 = 6735467) B6735467
theorem B5987081 : Blo 2073435 5987081 := bstep (se 2 (by rfl) ⟨2245155, by rfl⟩ : syracuseStep 5987081 = 4490311) B4490311
theorem B15965549 : Blo 2073435 15965549 := bstep (se 3 (by rfl) ⟨2993540, by rfl⟩ : syracuseStep 15965549 = 5987081) B5987081
theorem B10643699 : Blo 2073435 10643699 := bstep (se 1 (by rfl) ⟨7982774, by rfl⟩ : syracuseStep 10643699 = 15965549) B15965549
theorem B7095799 : Blo 2073435 7095799 := bstep (se 1 (by rfl) ⟨5321849, by rfl⟩ : syracuseStep 7095799 = 10643699) B10643699
theorem B9461065 : Blo 2073435 9461065 := bstep (se 2 (by rfl) ⟨3547899, by rfl⟩ : syracuseStep 9461065 = 7095799) B7095799
theorem B12614753 : Blo 2073435 12614753 := bstep (se 2 (by rfl) ⟨4730532, by rfl⟩ : syracuseStep 12614753 = 9461065) B9461065
theorem B8409835 : Blo 2073435 8409835 := bstep (se 1 (by rfl) ⟨6307376, by rfl⟩ : syracuseStep 8409835 = 12614753) B12614753
theorem B44852453 : Blo 2073435 44852453 := bstep (se 4 (by rfl) ⟨4204917, by rfl⟩ : syracuseStep 44852453 = 8409835) B8409835
theorem B29901635 : Blo 2073435 29901635 := bstep (se 1 (by rfl) ⟨22426226, by rfl⟩ : syracuseStep 29901635 = 44852453) B44852453
theorem B19934423 : Blo 2073435 19934423 := bstep (se 1 (by rfl) ⟨14950817, by rfl⟩ : syracuseStep 19934423 = 29901635) B29901635
theorem B13289615 : Blo 2073435 13289615 := bstep (se 1 (by rfl) ⟨9967211, by rfl⟩ : syracuseStep 13289615 = 19934423) B19934423
theorem B8859743 : Blo 2073435 8859743 := bstep (se 1 (by rfl) ⟨6644807, by rfl⟩ : syracuseStep 8859743 = 13289615) B13289615
theorem B5906495 : Blo 2073435 5906495 := bstep (se 1 (by rfl) ⟨4429871, by rfl⟩ : syracuseStep 5906495 = 8859743) B8859743
theorem B3937663 : Blo 2073435 3937663 := bstep (se 1 (by rfl) ⟨2953247, by rfl⟩ : syracuseStep 3937663 = 5906495) B5906495
theorem B5250217 : Blo 2073435 5250217 := bstep (se 2 (by rfl) ⟨1968831, by rfl⟩ : syracuseStep 5250217 = 3937663) B3937663
theorem B7000289 : Blo 2073435 7000289 := bstep (se 2 (by rfl) ⟨2625108, by rfl⟩ : syracuseStep 7000289 = 5250217) B5250217
theorem B4666859 : Blo 2073435 4666859 := bstep (se 1 (by rfl) ⟨3500144, by rfl⟩ : syracuseStep 4666859 = 7000289) B7000289
theorem B3111239 : Blo 2073435 3111239 := bstep (se 1 (by rfl) ⟨2333429, by rfl⟩ : syracuseStep 3111239 = 4666859) B4666859
theorem B2074159 : Blo 2073435 2074159 := bstep (se 1 (by rfl) ⟨1555619, by rfl⟩ : syracuseStep 2074159 = 3111239) B3111239
theorem B3111245 : Blo 2073435 3111245 := bbase (se 3 (by rfl) ⟨583358, by rfl⟩ : syracuseStep 3111245 = 1166717) (by norm_num)
theorem B2074163 : Blo 2073435 2074163 := bstep (se 1 (by rfl) ⟨1555622, by rfl⟩ : syracuseStep 2074163 = 3111245) B3111245
theorem B4666877 : Blo 2073435 4666877 := bbase (se 3 (by rfl) ⟨875039, by rfl⟩ : syracuseStep 4666877 = 1750079) (by norm_num)
theorem B3111251 : Blo 2073435 3111251 := bstep (se 1 (by rfl) ⟨2333438, by rfl⟩ : syracuseStep 3111251 = 4666877) B4666877
theorem B2074167 : Blo 2073435 2074167 := bstep (se 1 (by rfl) ⟨1555625, by rfl⟩ : syracuseStep 2074167 = 3111251) B3111251
theorem B3500165 : Blo 2073435 3500165 := bbase (se 4 (by rfl) ⟨328140, by rfl⟩ : syracuseStep 3500165 = 656281) (by norm_num)
theorem B2333443 : Blo 2073435 2333443 := bstep (se 1 (by rfl) ⟨1750082, by rfl⟩ : syracuseStep 2333443 = 3500165) B3500165
theorem B3111257 : Blo 2073435 3111257 := bstep (se 2 (by rfl) ⟨1166721, by rfl⟩ : syracuseStep 3111257 = 2333443) B2333443
theorem B2074171 : Blo 2073435 2074171 := bstep (se 1 (by rfl) ⟨1555628, by rfl⟩ : syracuseStep 2074171 = 3111257) B3111257
theorem B15750773 : Blo 2073435 15750773 := bbase (se 5 (by rfl) ⟨738317, by rfl⟩ : syracuseStep 15750773 = 1476635) (by norm_num)
theorem B10500515 : Blo 2073435 10500515 := bstep (se 1 (by rfl) ⟨7875386, by rfl⟩ : syracuseStep 10500515 = 15750773) B15750773
theorem B7000343 : Blo 2073435 7000343 := bstep (se 1 (by rfl) ⟨5250257, by rfl⟩ : syracuseStep 7000343 = 10500515) B10500515
theorem B4666895 : Blo 2073435 4666895 := bstep (se 1 (by rfl) ⟨3500171, by rfl⟩ : syracuseStep 4666895 = 7000343) B7000343
theorem B3111263 : Blo 2073435 3111263 := bstep (se 1 (by rfl) ⟨2333447, by rfl⟩ : syracuseStep 3111263 = 4666895) B4666895
theorem B2074175 : Blo 2073435 2074175 := bstep (se 1 (by rfl) ⟨1555631, by rfl⟩ : syracuseStep 2074175 = 3111263) B3111263
theorem B3111269 : Blo 2073435 3111269 := bbase (se 4 (by rfl) ⟨291681, by rfl⟩ : syracuseStep 3111269 = 583363) (by norm_num)
theorem B2074179 : Blo 2073435 2074179 := bstep (se 1 (by rfl) ⟨1555634, by rfl⟩ : syracuseStep 2074179 = 3111269) B3111269
theorem B3937709 : Blo 2073435 3937709 := bbase (se 3 (by rfl) ⟨738320, by rfl⟩ : syracuseStep 3937709 = 1476641) (by norm_num)
theorem B2625139 : Blo 2073435 2625139 := bstep (se 1 (by rfl) ⟨1968854, by rfl⟩ : syracuseStep 2625139 = 3937709) B3937709
theorem B3500185 : Blo 2073435 3500185 := bstep (se 2 (by rfl) ⟨1312569, by rfl⟩ : syracuseStep 3500185 = 2625139) B2625139
theorem B4666913 : Blo 2073435 4666913 := bstep (se 2 (by rfl) ⟨1750092, by rfl⟩ : syracuseStep 4666913 = 3500185) B3500185
theorem B3111275 : Blo 2073435 3111275 := bstep (se 1 (by rfl) ⟨2333456, by rfl⟩ : syracuseStep 3111275 = 4666913) B4666913
theorem B2074183 : Blo 2073435 2074183 := bstep (se 1 (by rfl) ⟨1555637, by rfl⟩ : syracuseStep 2074183 = 3111275) B3111275
theorem B2333461 : Blo 2073435 2333461 := bbase (se 6 (by rfl) ⟨54690, by rfl⟩ : syracuseStep 2333461 = 109381) (by norm_num)
theorem B3111281 : Blo 2073435 3111281 := bstep (se 2 (by rfl) ⟨1166730, by rfl⟩ : syracuseStep 3111281 = 2333461) B2333461
theorem B2074187 : Blo 2073435 2074187 := bstep (se 1 (by rfl) ⟨1555640, by rfl⟩ : syracuseStep 2074187 = 3111281) B3111281
theorem B2625149 : Blo 2073435 2625149 := bbase (se 3 (by rfl) ⟨492215, by rfl⟩ : syracuseStep 2625149 = 984431) (by norm_num)
theorem B7000397 : Blo 2073435 7000397 := bstep (se 3 (by rfl) ⟨1312574, by rfl⟩ : syracuseStep 7000397 = 2625149) B2625149
theorem B4666931 : Blo 2073435 4666931 := bstep (se 1 (by rfl) ⟨3500198, by rfl⟩ : syracuseStep 4666931 = 7000397) B7000397
theorem B3111287 : Blo 2073435 3111287 := bstep (se 1 (by rfl) ⟨2333465, by rfl⟩ : syracuseStep 3111287 = 4666931) B4666931
theorem B2074191 : Blo 2073435 2074191 := bstep (se 1 (by rfl) ⟨1555643, by rfl⟩ : syracuseStep 2074191 = 3111287) B3111287
theorem B3111293 : Blo 2073435 3111293 := bbase (se 3 (by rfl) ⟨583367, by rfl⟩ : syracuseStep 3111293 = 1166735) (by norm_num)
theorem B2074195 : Blo 2073435 2074195 := bstep (se 1 (by rfl) ⟨1555646, by rfl⟩ : syracuseStep 2074195 = 3111293) B3111293
theorem B4666949 : Blo 2073435 4666949 := bbase (se 4 (by rfl) ⟨437526, by rfl⟩ : syracuseStep 4666949 = 875053) (by norm_num)
theorem B3111299 : Blo 2073435 3111299 := bstep (se 1 (by rfl) ⟨2333474, by rfl⟩ : syracuseStep 3111299 = 4666949) B4666949
theorem B2074199 : Blo 2073435 2074199 := bstep (se 1 (by rfl) ⟨1555649, by rfl⟩ : syracuseStep 2074199 = 3111299) B3111299
theorem B3153757 : Blo 2073435 3153757 := bbase (se 3 (by rfl) ⟨591329, by rfl⟩ : syracuseStep 3153757 = 1182659) (by norm_num)
theorem B4205009 : Blo 2073435 4205009 := bstep (se 2 (by rfl) ⟨1576878, by rfl⟩ : syracuseStep 4205009 = 3153757) B3153757
theorem B2803339 : Blo 2073435 2803339 := bstep (se 1 (by rfl) ⟨2102504, by rfl⟩ : syracuseStep 2803339 = 4205009) B4205009
theorem B3737785 : Blo 2073435 3737785 := bstep (se 2 (by rfl) ⟨1401669, by rfl⟩ : syracuseStep 3737785 = 2803339) B2803339
theorem B4983713 : Blo 2073435 4983713 := bstep (se 2 (by rfl) ⟨1868892, by rfl⟩ : syracuseStep 4983713 = 3737785) B3737785
theorem B3322475 : Blo 2073435 3322475 := bstep (se 1 (by rfl) ⟨2491856, by rfl⟩ : syracuseStep 3322475 = 4983713) B4983713
theorem B2214983 : Blo 2073435 2214983 := bstep (se 1 (by rfl) ⟨1661237, by rfl⟩ : syracuseStep 2214983 = 3322475) B3322475
theorem B5906621 : Blo 2073435 5906621 := bstep (se 3 (by rfl) ⟨1107491, by rfl⟩ : syracuseStep 5906621 = 2214983) B2214983
theorem B3937747 : Blo 2073435 3937747 := bstep (se 1 (by rfl) ⟨2953310, by rfl⟩ : syracuseStep 3937747 = 5906621) B5906621
theorem B5250329 : Blo 2073435 5250329 := bstep (se 2 (by rfl) ⟨1968873, by rfl⟩ : syracuseStep 5250329 = 3937747) B3937747
theorem B3500219 : Blo 2073435 3500219 := bstep (se 1 (by rfl) ⟨2625164, by rfl⟩ : syracuseStep 3500219 = 5250329) B5250329
theorem B2333479 : Blo 2073435 2333479 := bstep (se 1 (by rfl) ⟨1750109, by rfl⟩ : syracuseStep 2333479 = 3500219) B3500219
theorem B3111305 : Blo 2073435 3111305 := bstep (se 2 (by rfl) ⟨1166739, by rfl⟩ : syracuseStep 3111305 = 2333479) B2333479
theorem B2074203 : Blo 2073435 2074203 := bstep (se 1 (by rfl) ⟨1555652, by rfl⟩ : syracuseStep 2074203 = 3111305) B3111305
theorem B10500677 : Blo 2073435 10500677 := bbase (se 4 (by rfl) ⟨984438, by rfl⟩ : syracuseStep 10500677 = 1968877) (by norm_num)
theorem B7000451 : Blo 2073435 7000451 := bstep (se 1 (by rfl) ⟨5250338, by rfl⟩ : syracuseStep 7000451 = 10500677) B10500677
theorem B4666967 : Blo 2073435 4666967 := bstep (se 1 (by rfl) ⟨3500225, by rfl⟩ : syracuseStep 4666967 = 7000451) B7000451
theorem B3111311 : Blo 2073435 3111311 := bstep (se 1 (by rfl) ⟨2333483, by rfl⟩ : syracuseStep 3111311 = 4666967) B4666967
theorem B2074207 : Blo 2073435 2074207 := bstep (se 1 (by rfl) ⟨1555655, by rfl⟩ : syracuseStep 2074207 = 3111311) B3111311
theorem B3111317 : Blo 2073435 3111317 := bbase (se 6 (by rfl) ⟨72921, by rfl⟩ : syracuseStep 3111317 = 145843) (by norm_num)
theorem B2074211 : Blo 2073435 2074211 := bstep (se 1 (by rfl) ⟨1555658, by rfl⟩ : syracuseStep 2074211 = 3111317) B3111317
theorem B5683205 : Blo 2073435 5683205 := bbase (se 4 (by rfl) ⟨532800, by rfl⟩ : syracuseStep 5683205 = 1065601) (by norm_num)
theorem B3788803 : Blo 2073435 3788803 := bstep (se 1 (by rfl) ⟨2841602, by rfl⟩ : syracuseStep 3788803 = 5683205) B5683205
theorem B5051737 : Blo 2073435 5051737 := bstep (se 2 (by rfl) ⟨1894401, by rfl⟩ : syracuseStep 5051737 = 3788803) B3788803
theorem B6735649 : Blo 2073435 6735649 := bstep (se 2 (by rfl) ⟨2525868, by rfl⟩ : syracuseStep 6735649 = 5051737) B5051737
theorem B8980865 : Blo 2073435 8980865 := bstep (se 2 (by rfl) ⟨3367824, by rfl⟩ : syracuseStep 8980865 = 6735649) B6735649
theorem B5987243 : Blo 2073435 5987243 := bstep (se 1 (by rfl) ⟨4490432, by rfl⟩ : syracuseStep 5987243 = 8980865) B8980865
theorem B15965981 : Blo 2073435 15965981 := bstep (se 3 (by rfl) ⟨2993621, by rfl⟩ : syracuseStep 15965981 = 5987243) B5987243
theorem B10643987 : Blo 2073435 10643987 := bstep (se 1 (by rfl) ⟨7982990, by rfl⟩ : syracuseStep 10643987 = 15965981) B15965981
theorem B28383965 : Blo 2073435 28383965 := bstep (se 3 (by rfl) ⟨5321993, by rfl⟩ : syracuseStep 28383965 = 10643987) B10643987
theorem B18922643 : Blo 2073435 18922643 := bstep (se 1 (by rfl) ⟨14191982, by rfl⟩ : syracuseStep 18922643 = 28383965) B28383965
theorem B12615095 : Blo 2073435 12615095 := bstep (se 1 (by rfl) ⟨9461321, by rfl⟩ : syracuseStep 12615095 = 18922643) B18922643
theorem B8410063 : Blo 2073435 8410063 := bstep (se 1 (by rfl) ⟨6307547, by rfl⟩ : syracuseStep 8410063 = 12615095) B12615095
theorem B11213417 : Blo 2073435 11213417 := bstep (se 2 (by rfl) ⟨4205031, by rfl⟩ : syracuseStep 11213417 = 8410063) B8410063
theorem B7475611 : Blo 2073435 7475611 := bstep (se 1 (by rfl) ⟨5606708, by rfl⟩ : syracuseStep 7475611 = 11213417) B11213417
theorem B9967481 : Blo 2073435 9967481 := bstep (se 2 (by rfl) ⟨3737805, by rfl⟩ : syracuseStep 9967481 = 7475611) B7475611
theorem B6644987 : Blo 2073435 6644987 := bstep (se 1 (by rfl) ⟨4983740, by rfl⟩ : syracuseStep 6644987 = 9967481) B9967481
theorem B4429991 : Blo 2073435 4429991 := bstep (se 1 (by rfl) ⟨3322493, by rfl⟩ : syracuseStep 4429991 = 6644987) B6644987
theorem B11813309 : Blo 2073435 11813309 := bstep (se 3 (by rfl) ⟨2214995, by rfl⟩ : syracuseStep 11813309 = 4429991) B4429991
theorem B7875539 : Blo 2073435 7875539 := bstep (se 1 (by rfl) ⟨5906654, by rfl⟩ : syracuseStep 7875539 = 11813309) B11813309
theorem B5250359 : Blo 2073435 5250359 := bstep (se 1 (by rfl) ⟨3937769, by rfl⟩ : syracuseStep 5250359 = 7875539) B7875539
theorem B3500239 : Blo 2073435 3500239 := bstep (se 1 (by rfl) ⟨2625179, by rfl⟩ : syracuseStep 3500239 = 5250359) B5250359
theorem B4666985 : Blo 2073435 4666985 := bstep (se 2 (by rfl) ⟨1750119, by rfl⟩ : syracuseStep 4666985 = 3500239) B3500239
theorem B3111323 : Blo 2073435 3111323 := bstep (se 1 (by rfl) ⟨2333492, by rfl⟩ : syracuseStep 3111323 = 4666985) B4666985
theorem B2074215 : Blo 2073435 2074215 := bstep (se 1 (by rfl) ⟨1555661, by rfl⟩ : syracuseStep 2074215 = 3111323) B3111323
theorem B2333497 : Blo 2073435 2333497 := bbase (se 2 (by rfl) ⟨875061, by rfl⟩ : syracuseStep 2333497 = 1750123) (by norm_num)
theorem B3111329 : Blo 2073435 3111329 := bstep (se 2 (by rfl) ⟨1166748, by rfl⟩ : syracuseStep 3111329 = 2333497) B2333497
theorem B2074219 : Blo 2073435 2074219 := bstep (se 1 (by rfl) ⟨1555664, by rfl⟩ : syracuseStep 2074219 = 3111329) B3111329
theorem B5906677 : Blo 2073435 5906677 := bbase (se 5 (by rfl) ⟨276875, by rfl⟩ : syracuseStep 5906677 = 553751) (by norm_num)
theorem B7875569 : Blo 2073435 7875569 := bstep (se 2 (by rfl) ⟨2953338, by rfl⟩ : syracuseStep 7875569 = 5906677) B5906677
theorem B5250379 : Blo 2073435 5250379 := bstep (se 1 (by rfl) ⟨3937784, by rfl⟩ : syracuseStep 5250379 = 7875569) B7875569
theorem B7000505 : Blo 2073435 7000505 := bstep (se 2 (by rfl) ⟨2625189, by rfl⟩ : syracuseStep 7000505 = 5250379) B5250379
theorem B4667003 : Blo 2073435 4667003 := bstep (se 1 (by rfl) ⟨3500252, by rfl⟩ : syracuseStep 4667003 = 7000505) B7000505
theorem B3111335 : Blo 2073435 3111335 := bstep (se 1 (by rfl) ⟨2333501, by rfl⟩ : syracuseStep 3111335 = 4667003) B4667003
theorem B2074223 : Blo 2073435 2074223 := bstep (se 1 (by rfl) ⟨1555667, by rfl⟩ : syracuseStep 2074223 = 3111335) B3111335
theorem B3111341 : Blo 2073435 3111341 := bbase (se 3 (by rfl) ⟨583376, by rfl⟩ : syracuseStep 3111341 = 1166753) (by norm_num)
theorem B2074227 : Blo 2073435 2074227 := bstep (se 1 (by rfl) ⟨1555670, by rfl⟩ : syracuseStep 2074227 = 3111341) B3111341
theorem B4667021 : Blo 2073435 4667021 := bbase (se 3 (by rfl) ⟨875066, by rfl⟩ : syracuseStep 4667021 = 1750133) (by norm_num)
theorem B3111347 : Blo 2073435 3111347 := bstep (se 1 (by rfl) ⟨2333510, by rfl⟩ : syracuseStep 3111347 = 4667021) B4667021
theorem B2074231 : Blo 2073435 2074231 := bstep (se 1 (by rfl) ⟨1555673, by rfl⟩ : syracuseStep 2074231 = 3111347) B3111347
theorem B2625205 : Blo 2073435 2625205 := bbase (se 5 (by rfl) ⟨123056, by rfl⟩ : syracuseStep 2625205 = 246113) (by norm_num)
theorem B3500273 : Blo 2073435 3500273 := bstep (se 2 (by rfl) ⟨1312602, by rfl⟩ : syracuseStep 3500273 = 2625205) B2625205
theorem B2333515 : Blo 2073435 2333515 := bstep (se 1 (by rfl) ⟨1750136, by rfl⟩ : syracuseStep 2333515 = 3500273) B3500273
theorem B3111353 : Blo 2073435 3111353 := bstep (se 2 (by rfl) ⟨1166757, by rfl⟩ : syracuseStep 3111353 = 2333515) B2333515
theorem B2074235 : Blo 2073435 2074235 := bstep (se 1 (by rfl) ⟨1555676, by rfl⟩ : syracuseStep 2074235 = 3111353) B3111353
theorem B8524901 : Blo 2073435 8524901 := bbase (se 4 (by rfl) ⟨799209, by rfl⟩ : syracuseStep 8524901 = 1598419) (by norm_num)
theorem B5683267 : Blo 2073435 5683267 := bstep (se 1 (by rfl) ⟨4262450, by rfl⟩ : syracuseStep 5683267 = 8524901) B8524901
theorem B30310757 : Blo 2073435 30310757 := bstep (se 4 (by rfl) ⟨2841633, by rfl⟩ : syracuseStep 30310757 = 5683267) B5683267
theorem B20207171 : Blo 2073435 20207171 := bstep (se 1 (by rfl) ⟨15155378, by rfl⟩ : syracuseStep 20207171 = 30310757) B30310757
theorem B53885789 : Blo 2073435 53885789 := bstep (se 3 (by rfl) ⟨10103585, by rfl⟩ : syracuseStep 53885789 = 20207171) B20207171
theorem B35923859 : Blo 2073435 35923859 := bstep (se 1 (by rfl) ⟨26942894, by rfl⟩ : syracuseStep 35923859 = 53885789) B53885789
theorem B23949239 : Blo 2073435 23949239 := bstep (se 1 (by rfl) ⟨17961929, by rfl⟩ : syracuseStep 23949239 = 35923859) B35923859
theorem B255458549 : Blo 2073435 255458549 := bstep (se 5 (by rfl) ⟨11974619, by rfl⟩ : syracuseStep 255458549 = 23949239) B23949239
theorem B170305699 : Blo 2073435 170305699 := bstep (se 1 (by rfl) ⟨127729274, by rfl⟩ : syracuseStep 170305699 = 255458549) B255458549
theorem B227074265 : Blo 2073435 227074265 := bstep (se 2 (by rfl) ⟨85152849, by rfl⟩ : syracuseStep 227074265 = 170305699) B170305699
theorem B151382843 : Blo 2073435 151382843 := bstep (se 1 (by rfl) ⟨113537132, by rfl⟩ : syracuseStep 151382843 = 227074265) B227074265
theorem B100921895 : Blo 2073435 100921895 := bstep (se 1 (by rfl) ⟨75691421, by rfl⟩ : syracuseStep 100921895 = 151382843) B151382843
theorem B67281263 : Blo 2073435 67281263 := bstep (se 1 (by rfl) ⟨50460947, by rfl⟩ : syracuseStep 67281263 = 100921895) B100921895
theorem B44854175 : Blo 2073435 44854175 := bstep (se 1 (by rfl) ⟨33640631, by rfl⟩ : syracuseStep 44854175 = 67281263) B67281263
theorem B29902783 : Blo 2073435 29902783 := bstep (se 1 (by rfl) ⟨22427087, by rfl⟩ : syracuseStep 29902783 = 44854175) B44854175
theorem B39870377 : Blo 2073435 39870377 := bstep (se 2 (by rfl) ⟨14951391, by rfl⟩ : syracuseStep 39870377 = 29902783) B29902783
theorem B26580251 : Blo 2073435 26580251 := bstep (se 1 (by rfl) ⟨19935188, by rfl⟩ : syracuseStep 26580251 = 39870377) B39870377
theorem B17720167 : Blo 2073435 17720167 := bstep (se 1 (by rfl) ⟨13290125, by rfl⟩ : syracuseStep 17720167 = 26580251) B26580251
theorem B23626889 : Blo 2073435 23626889 := bstep (se 2 (by rfl) ⟨8860083, by rfl⟩ : syracuseStep 23626889 = 17720167) B17720167
theorem B15751259 : Blo 2073435 15751259 := bstep (se 1 (by rfl) ⟨11813444, by rfl⟩ : syracuseStep 15751259 = 23626889) B23626889
theorem B10500839 : Blo 2073435 10500839 := bstep (se 1 (by rfl) ⟨7875629, by rfl⟩ : syracuseStep 10500839 = 15751259) B15751259
theorem B7000559 : Blo 2073435 7000559 := bstep (se 1 (by rfl) ⟨5250419, by rfl⟩ : syracuseStep 7000559 = 10500839) B10500839
theorem B4667039 : Blo 2073435 4667039 := bstep (se 1 (by rfl) ⟨3500279, by rfl⟩ : syracuseStep 4667039 = 7000559) B7000559
theorem B3111359 : Blo 2073435 3111359 := bstep (se 1 (by rfl) ⟨2333519, by rfl⟩ : syracuseStep 3111359 = 4667039) B4667039
theorem B2074239 : Blo 2073435 2074239 := bstep (se 1 (by rfl) ⟨1555679, by rfl⟩ : syracuseStep 2074239 = 3111359) B3111359
theorem B3111365 : Blo 2073435 3111365 := bbase (se 4 (by rfl) ⟨291690, by rfl⟩ : syracuseStep 3111365 = 583381) (by norm_num)
theorem B2074243 : Blo 2073435 2074243 := bstep (se 1 (by rfl) ⟨1555682, by rfl⟩ : syracuseStep 2074243 = 3111365) B3111365
theorem B3500293 : Blo 2073435 3500293 := bbase (se 4 (by rfl) ⟨328152, by rfl⟩ : syracuseStep 3500293 = 656305) (by norm_num)
theorem B4667057 : Blo 2073435 4667057 := bstep (se 2 (by rfl) ⟨1750146, by rfl⟩ : syracuseStep 4667057 = 3500293) B3500293
theorem B3111371 : Blo 2073435 3111371 := bstep (se 1 (by rfl) ⟨2333528, by rfl⟩ : syracuseStep 3111371 = 4667057) B4667057
theorem B2074247 : Blo 2073435 2074247 := bstep (se 1 (by rfl) ⟨1555685, by rfl⟩ : syracuseStep 2074247 = 3111371) B3111371
theorem B2333533 : Blo 2073435 2333533 := bbase (se 3 (by rfl) ⟨437537, by rfl⟩ : syracuseStep 2333533 = 875075) (by norm_num)
theorem B3111377 : Blo 2073435 3111377 := bstep (se 2 (by rfl) ⟨1166766, by rfl⟩ : syracuseStep 3111377 = 2333533) B2333533
theorem B2074251 : Blo 2073435 2074251 := bstep (se 1 (by rfl) ⟨1555688, by rfl⟩ : syracuseStep 2074251 = 3111377) B3111377
theorem B7000613 : Blo 2073435 7000613 := bbase (se 4 (by rfl) ⟨656307, by rfl⟩ : syracuseStep 7000613 = 1312615) (by norm_num)
theorem B4667075 : Blo 2073435 4667075 := bstep (se 1 (by rfl) ⟨3500306, by rfl⟩ : syracuseStep 4667075 = 7000613) B7000613
theorem B3111383 : Blo 2073435 3111383 := bstep (se 1 (by rfl) ⟨2333537, by rfl⟩ : syracuseStep 3111383 = 4667075) B4667075
theorem B2074255 : Blo 2073435 2074255 := bstep (se 1 (by rfl) ⟨1555691, by rfl⟩ : syracuseStep 2074255 = 3111383) B3111383
theorem B3111389 : Blo 2073435 3111389 := bbase (se 3 (by rfl) ⟨583385, by rfl⟩ : syracuseStep 3111389 = 1166771) (by norm_num)
theorem B2074259 : Blo 2073435 2074259 := bstep (se 1 (by rfl) ⟨1555694, by rfl⟩ : syracuseStep 2074259 = 3111389) B3111389
theorem B4667093 : Blo 2073435 4667093 := bbase (se 7 (by rfl) ⟨54692, by rfl⟩ : syracuseStep 4667093 = 109385) (by norm_num)
theorem B3111395 : Blo 2073435 3111395 := bstep (se 1 (by rfl) ⟨2333546, by rfl⟩ : syracuseStep 3111395 = 4667093) B4667093
theorem B2074263 : Blo 2073435 2074263 := bstep (se 1 (by rfl) ⟨1555697, by rfl⟩ : syracuseStep 2074263 = 3111395) B3111395
theorem B2491933 : Blo 2073435 2491933 := bbase (se 3 (by rfl) ⟨467237, by rfl⟩ : syracuseStep 2491933 = 934475) (by norm_num)
theorem B3322577 : Blo 2073435 3322577 := bstep (se 2 (by rfl) ⟨1245966, by rfl⟩ : syracuseStep 3322577 = 2491933) B2491933
theorem B8860205 : Blo 2073435 8860205 := bstep (se 3 (by rfl) ⟨1661288, by rfl⟩ : syracuseStep 8860205 = 3322577) B3322577
theorem B5906803 : Blo 2073435 5906803 := bstep (se 1 (by rfl) ⟨4430102, by rfl⟩ : syracuseStep 5906803 = 8860205) B8860205
theorem B7875737 : Blo 2073435 7875737 := bstep (se 2 (by rfl) ⟨2953401, by rfl⟩ : syracuseStep 7875737 = 5906803) B5906803
theorem B5250491 : Blo 2073435 5250491 := bstep (se 1 (by rfl) ⟨3937868, by rfl⟩ : syracuseStep 5250491 = 7875737) B7875737
theorem B3500327 : Blo 2073435 3500327 := bstep (se 1 (by rfl) ⟨2625245, by rfl⟩ : syracuseStep 3500327 = 5250491) B5250491
theorem B2333551 : Blo 2073435 2333551 := bstep (se 1 (by rfl) ⟨1750163, by rfl⟩ : syracuseStep 2333551 = 3500327) B3500327
theorem B3111401 : Blo 2073435 3111401 := bstep (se 2 (by rfl) ⟨1166775, by rfl⟩ : syracuseStep 3111401 = 2333551) B2333551
theorem B2074267 : Blo 2073435 2074267 := bstep (se 1 (by rfl) ⟨1555700, by rfl⟩ : syracuseStep 2074267 = 3111401) B3111401
theorem B7096181 : Blo 2073435 7096181 := bbase (se 5 (by rfl) ⟨332633, by rfl⟩ : syracuseStep 7096181 = 665267) (by norm_num)
theorem B18923149 : Blo 2073435 18923149 := bstep (se 3 (by rfl) ⟨3548090, by rfl⟩ : syracuseStep 18923149 = 7096181) B7096181
theorem B25230865 : Blo 2073435 25230865 := bstep (se 2 (by rfl) ⟨9461574, by rfl⟩ : syracuseStep 25230865 = 18923149) B18923149
theorem B33641153 : Blo 2073435 33641153 := bstep (se 2 (by rfl) ⟨12615432, by rfl⟩ : syracuseStep 33641153 = 25230865) B25230865
theorem B22427435 : Blo 2073435 22427435 := bstep (se 1 (by rfl) ⟨16820576, by rfl⟩ : syracuseStep 22427435 = 33641153) B33641153
theorem B14951623 : Blo 2073435 14951623 := bstep (se 1 (by rfl) ⟨11213717, by rfl⟩ : syracuseStep 14951623 = 22427435) B22427435
theorem B19935497 : Blo 2073435 19935497 := bstep (se 2 (by rfl) ⟨7475811, by rfl⟩ : syracuseStep 19935497 = 14951623) B14951623
theorem B13290331 : Blo 2073435 13290331 := bstep (se 1 (by rfl) ⟨9967748, by rfl⟩ : syracuseStep 13290331 = 19935497) B19935497
theorem B17720441 : Blo 2073435 17720441 := bstep (se 2 (by rfl) ⟨6645165, by rfl⟩ : syracuseStep 17720441 = 13290331) B13290331
theorem B11813627 : Blo 2073435 11813627 := bstep (se 1 (by rfl) ⟨8860220, by rfl⟩ : syracuseStep 11813627 = 17720441) B17720441
theorem B7875751 : Blo 2073435 7875751 := bstep (se 1 (by rfl) ⟨5906813, by rfl⟩ : syracuseStep 7875751 = 11813627) B11813627
theorem B10501001 : Blo 2073435 10501001 := bstep (se 2 (by rfl) ⟨3937875, by rfl⟩ : syracuseStep 10501001 = 7875751) B7875751
theorem B7000667 : Blo 2073435 7000667 := bstep (se 1 (by rfl) ⟨5250500, by rfl⟩ : syracuseStep 7000667 = 10501001) B10501001
theorem B4667111 : Blo 2073435 4667111 := bstep (se 1 (by rfl) ⟨3500333, by rfl⟩ : syracuseStep 4667111 = 7000667) B7000667
theorem B3111407 : Blo 2073435 3111407 := bstep (se 1 (by rfl) ⟨2333555, by rfl⟩ : syracuseStep 3111407 = 4667111) B4667111
theorem B2074271 : Blo 2073435 2074271 := bstep (se 1 (by rfl) ⟨1555703, by rfl⟩ : syracuseStep 2074271 = 3111407) B3111407
theorem B3111413 : Blo 2073435 3111413 := bbase (se 5 (by rfl) ⟨145847, by rfl⟩ : syracuseStep 3111413 = 291695) (by norm_num)
theorem B2074275 : Blo 2073435 2074275 := bstep (se 1 (by rfl) ⟨1555706, by rfl⟩ : syracuseStep 2074275 = 3111413) B3111413
theorem B5906837 : Blo 2073435 5906837 := bbase (se 6 (by rfl) ⟨138441, by rfl⟩ : syracuseStep 5906837 = 276883) (by norm_num)
theorem B3937891 : Blo 2073435 3937891 := bstep (se 1 (by rfl) ⟨2953418, by rfl⟩ : syracuseStep 3937891 = 5906837) B5906837
theorem B5250521 : Blo 2073435 5250521 := bstep (se 2 (by rfl) ⟨1968945, by rfl⟩ : syracuseStep 5250521 = 3937891) B3937891
theorem B3500347 : Blo 2073435 3500347 := bstep (se 1 (by rfl) ⟨2625260, by rfl⟩ : syracuseStep 3500347 = 5250521) B5250521
theorem B4667129 : Blo 2073435 4667129 := bstep (se 2 (by rfl) ⟨1750173, by rfl⟩ : syracuseStep 4667129 = 3500347) B3500347
theorem B3111419 : Blo 2073435 3111419 := bstep (se 1 (by rfl) ⟨2333564, by rfl⟩ : syracuseStep 3111419 = 4667129) B4667129
theorem B2074279 : Blo 2073435 2074279 := bstep (se 1 (by rfl) ⟨1555709, by rfl⟩ : syracuseStep 2074279 = 3111419) B3111419
theorem B2333569 : Blo 2073435 2333569 := bbase (se 2 (by rfl) ⟨875088, by rfl⟩ : syracuseStep 2333569 = 1750177) (by norm_num)
theorem B3111425 : Blo 2073435 3111425 := bstep (se 2 (by rfl) ⟨1166784, by rfl⟩ : syracuseStep 3111425 = 2333569) B2333569
theorem B2074283 : Blo 2073435 2074283 := bstep (se 1 (by rfl) ⟨1555712, by rfl⟩ : syracuseStep 2074283 = 3111425) B3111425
theorem B5250541 : Blo 2073435 5250541 := bbase (se 3 (by rfl) ⟨984476, by rfl⟩ : syracuseStep 5250541 = 1968953) (by norm_num)
theorem B7000721 : Blo 2073435 7000721 := bstep (se 2 (by rfl) ⟨2625270, by rfl⟩ : syracuseStep 7000721 = 5250541) B5250541
theorem B4667147 : Blo 2073435 4667147 := bstep (se 1 (by rfl) ⟨3500360, by rfl⟩ : syracuseStep 4667147 = 7000721) B7000721
theorem B3111431 : Blo 2073435 3111431 := bstep (se 1 (by rfl) ⟨2333573, by rfl⟩ : syracuseStep 3111431 = 4667147) B4667147
theorem B2074287 : Blo 2073435 2074287 := bstep (se 1 (by rfl) ⟨1555715, by rfl⟩ : syracuseStep 2074287 = 3111431) B3111431
theorem B3111437 : Blo 2073435 3111437 := bbase (se 3 (by rfl) ⟨583394, by rfl⟩ : syracuseStep 3111437 = 1166789) (by norm_num)
theorem B2074291 : Blo 2073435 2074291 := bstep (se 1 (by rfl) ⟨1555718, by rfl⟩ : syracuseStep 2074291 = 3111437) B3111437
theorem B4667165 : Blo 2073435 4667165 := bbase (se 3 (by rfl) ⟨875093, by rfl⟩ : syracuseStep 4667165 = 1750187) (by norm_num)
theorem B3111443 : Blo 2073435 3111443 := bstep (se 1 (by rfl) ⟨2333582, by rfl⟩ : syracuseStep 3111443 = 4667165) B4667165
theorem B2074295 : Blo 2073435 2074295 := bstep (se 1 (by rfl) ⟨1555721, by rfl⟩ : syracuseStep 2074295 = 3111443) B3111443
theorem B3500381 : Blo 2073435 3500381 := bbase (se 3 (by rfl) ⟨656321, by rfl⟩ : syracuseStep 3500381 = 1312643) (by norm_num)
theorem B2333587 : Blo 2073435 2333587 := bstep (se 1 (by rfl) ⟨1750190, by rfl⟩ : syracuseStep 2333587 = 3500381) B3500381
theorem B3111449 : Blo 2073435 3111449 := bstep (se 2 (by rfl) ⟨1166793, by rfl⟩ : syracuseStep 3111449 = 2333587) B2333587
theorem B2074299 : Blo 2073435 2074299 := bstep (se 1 (by rfl) ⟨1555724, by rfl⟩ : syracuseStep 2074299 = 3111449) B3111449
theorem B8860357 : Blo 2073435 8860357 := bbase (se 4 (by rfl) ⟨830658, by rfl⟩ : syracuseStep 8860357 = 1661317) (by norm_num)
theorem B11813809 : Blo 2073435 11813809 := bstep (se 2 (by rfl) ⟨4430178, by rfl⟩ : syracuseStep 11813809 = 8860357) B8860357
theorem B15751745 : Blo 2073435 15751745 := bstep (se 2 (by rfl) ⟨5906904, by rfl⟩ : syracuseStep 15751745 = 11813809) B11813809
theorem B10501163 : Blo 2073435 10501163 := bstep (se 1 (by rfl) ⟨7875872, by rfl⟩ : syracuseStep 10501163 = 15751745) B15751745
theorem B7000775 : Blo 2073435 7000775 := bstep (se 1 (by rfl) ⟨5250581, by rfl⟩ : syracuseStep 7000775 = 10501163) B10501163
theorem B4667183 : Blo 2073435 4667183 := bstep (se 1 (by rfl) ⟨3500387, by rfl⟩ : syracuseStep 4667183 = 7000775) B7000775
theorem B3111455 : Blo 2073435 3111455 := bstep (se 1 (by rfl) ⟨2333591, by rfl⟩ : syracuseStep 3111455 = 4667183) B4667183
theorem B2074303 : Blo 2073435 2074303 := bstep (se 1 (by rfl) ⟨1555727, by rfl⟩ : syracuseStep 2074303 = 3111455) B3111455
theorem B3111461 : Blo 2073435 3111461 := bbase (se 4 (by rfl) ⟨291699, by rfl⟩ : syracuseStep 3111461 = 583399) (by norm_num)
theorem B2074307 : Blo 2073435 2074307 := bstep (se 1 (by rfl) ⟨1555730, by rfl⟩ : syracuseStep 2074307 = 3111461) B3111461
theorem B2625301 : Blo 2073435 2625301 := bbase (se 6 (by rfl) ⟨61530, by rfl⟩ : syracuseStep 2625301 = 123061) (by norm_num)
theorem B3500401 : Blo 2073435 3500401 := bstep (se 2 (by rfl) ⟨1312650, by rfl⟩ : syracuseStep 3500401 = 2625301) B2625301
theorem B4667201 : Blo 2073435 4667201 := bstep (se 2 (by rfl) ⟨1750200, by rfl⟩ : syracuseStep 4667201 = 3500401) B3500401
theorem B3111467 : Blo 2073435 3111467 := bstep (se 1 (by rfl) ⟨2333600, by rfl⟩ : syracuseStep 3111467 = 4667201) B4667201
theorem B2074311 : Blo 2073435 2074311 := bstep (se 1 (by rfl) ⟨1555733, by rfl⟩ : syracuseStep 2074311 = 3111467) B3111467
theorem B2333605 : Blo 2073435 2333605 := bbase (se 4 (by rfl) ⟨218775, by rfl⟩ : syracuseStep 2333605 = 437551) (by norm_num)
theorem B3111473 : Blo 2073435 3111473 := bstep (se 2 (by rfl) ⟨1166802, by rfl⟩ : syracuseStep 3111473 = 2333605) B2333605
theorem B2074315 : Blo 2073435 2074315 := bstep (se 1 (by rfl) ⟨1555736, by rfl⟩ : syracuseStep 2074315 = 3111473) B3111473
theorem B2993773 : Blo 2073435 2993773 := bbase (se 3 (by rfl) ⟨561332, by rfl⟩ : syracuseStep 2993773 = 1122665) (by norm_num)
theorem B3991697 : Blo 2073435 3991697 := bstep (se 2 (by rfl) ⟨1496886, by rfl⟩ : syracuseStep 3991697 = 2993773) B2993773
theorem B2661131 : Blo 2073435 2661131 := bstep (se 1 (by rfl) ⟨1995848, by rfl⟩ : syracuseStep 2661131 = 3991697) B3991697
theorem B7096349 : Blo 2073435 7096349 := bstep (se 3 (by rfl) ⟨1330565, by rfl⟩ : syracuseStep 7096349 = 2661131) B2661131
theorem B4730899 : Blo 2073435 4730899 := bstep (se 1 (by rfl) ⟨3548174, by rfl⟩ : syracuseStep 4730899 = 7096349) B7096349
theorem B6307865 : Blo 2073435 6307865 := bstep (se 2 (by rfl) ⟨2365449, by rfl⟩ : syracuseStep 6307865 = 4730899) B4730899
theorem B4205243 : Blo 2073435 4205243 := bstep (se 1 (by rfl) ⟨3153932, by rfl⟩ : syracuseStep 4205243 = 6307865) B6307865
theorem B2803495 : Blo 2073435 2803495 := bstep (se 1 (by rfl) ⟨2102621, by rfl⟩ : syracuseStep 2803495 = 4205243) B4205243
theorem B3737993 : Blo 2073435 3737993 := bstep (se 2 (by rfl) ⟨1401747, by rfl⟩ : syracuseStep 3737993 = 2803495) B2803495
theorem B9967981 : Blo 2073435 9967981 := bstep (se 3 (by rfl) ⟨1868996, by rfl⟩ : syracuseStep 9967981 = 3737993) B3737993
theorem B13290641 : Blo 2073435 13290641 := bstep (se 2 (by rfl) ⟨4983990, by rfl⟩ : syracuseStep 13290641 = 9967981) B9967981
theorem B8860427 : Blo 2073435 8860427 := bstep (se 1 (by rfl) ⟨6645320, by rfl⟩ : syracuseStep 8860427 = 13290641) B13290641
theorem B5906951 : Blo 2073435 5906951 := bstep (se 1 (by rfl) ⟨4430213, by rfl⟩ : syracuseStep 5906951 = 8860427) B8860427
theorem B3937967 : Blo 2073435 3937967 := bstep (se 1 (by rfl) ⟨2953475, by rfl⟩ : syracuseStep 3937967 = 5906951) B5906951
theorem B2625311 : Blo 2073435 2625311 := bstep (se 1 (by rfl) ⟨1968983, by rfl⟩ : syracuseStep 2625311 = 3937967) B3937967
theorem B7000829 : Blo 2073435 7000829 := bstep (se 3 (by rfl) ⟨1312655, by rfl⟩ : syracuseStep 7000829 = 2625311) B2625311
theorem B4667219 : Blo 2073435 4667219 := bstep (se 1 (by rfl) ⟨3500414, by rfl⟩ : syracuseStep 4667219 = 7000829) B7000829
theorem B3111479 : Blo 2073435 3111479 := bstep (se 1 (by rfl) ⟨2333609, by rfl⟩ : syracuseStep 3111479 = 4667219) B4667219
theorem B2074319 : Blo 2073435 2074319 := bstep (se 1 (by rfl) ⟨1555739, by rfl⟩ : syracuseStep 2074319 = 3111479) B3111479
theorem B3111485 : Blo 2073435 3111485 := bbase (se 3 (by rfl) ⟨583403, by rfl⟩ : syracuseStep 3111485 = 1166807) (by norm_num)
theorem B2074323 : Blo 2073435 2074323 := bstep (se 1 (by rfl) ⟨1555742, by rfl⟩ : syracuseStep 2074323 = 3111485) B3111485
theorem B4667237 : Blo 2073435 4667237 := bbase (se 4 (by rfl) ⟨437553, by rfl⟩ : syracuseStep 4667237 = 875107) (by norm_num)
theorem B3111491 : Blo 2073435 3111491 := bstep (se 1 (by rfl) ⟨2333618, by rfl⟩ : syracuseStep 3111491 = 4667237) B4667237
theorem B2074327 : Blo 2073435 2074327 := bstep (se 1 (by rfl) ⟨1555745, by rfl⟩ : syracuseStep 2074327 = 3111491) B3111491
theorem B5250653 : Blo 2073435 5250653 := bbase (se 3 (by rfl) ⟨984497, by rfl⟩ : syracuseStep 5250653 = 1968995) (by norm_num)
theorem B3500435 : Blo 2073435 3500435 := bstep (se 1 (by rfl) ⟨2625326, by rfl⟩ : syracuseStep 3500435 = 5250653) B5250653
theorem B2333623 : Blo 2073435 2333623 := bstep (se 1 (by rfl) ⟨1750217, by rfl⟩ : syracuseStep 2333623 = 3500435) B3500435
theorem B3111497 : Blo 2073435 3111497 := bstep (se 2 (by rfl) ⟨1166811, by rfl⟩ : syracuseStep 3111497 = 2333623) B2333623
theorem B2074331 : Blo 2073435 2074331 := bstep (se 1 (by rfl) ⟨1555748, by rfl⟩ : syracuseStep 2074331 = 3111497) B3111497
theorem B3937997 : Blo 2073435 3937997 := bbase (se 3 (by rfl) ⟨738374, by rfl⟩ : syracuseStep 3937997 = 1476749) (by norm_num)
theorem B10501325 : Blo 2073435 10501325 := bstep (se 3 (by rfl) ⟨1968998, by rfl⟩ : syracuseStep 10501325 = 3937997) B3937997
theorem B7000883 : Blo 2073435 7000883 := bstep (se 1 (by rfl) ⟨5250662, by rfl⟩ : syracuseStep 7000883 = 10501325) B10501325
theorem B4667255 : Blo 2073435 4667255 := bstep (se 1 (by rfl) ⟨3500441, by rfl⟩ : syracuseStep 4667255 = 7000883) B7000883
theorem B3111503 : Blo 2073435 3111503 := bstep (se 1 (by rfl) ⟨2333627, by rfl⟩ : syracuseStep 3111503 = 4667255) B4667255
theorem B2074335 : Blo 2073435 2074335 := bstep (se 1 (by rfl) ⟨1555751, by rfl⟩ : syracuseStep 2074335 = 3111503) B3111503
theorem B3111509 : Blo 2073435 3111509 := bbase (se 8 (by rfl) ⟨18231, by rfl⟩ : syracuseStep 3111509 = 36463) (by norm_num)
theorem B2074339 : Blo 2073435 2074339 := bstep (se 1 (by rfl) ⟨1555754, by rfl⟩ : syracuseStep 2074339 = 3111509) B3111509
theorem B6645397 : Blo 2073435 6645397 := bbase (se 6 (by rfl) ⟨155751, by rfl⟩ : syracuseStep 6645397 = 311503) (by norm_num)
theorem B8860529 : Blo 2073435 8860529 := bstep (se 2 (by rfl) ⟨3322698, by rfl⟩ : syracuseStep 8860529 = 6645397) B6645397
theorem B5907019 : Blo 2073435 5907019 := bstep (se 1 (by rfl) ⟨4430264, by rfl⟩ : syracuseStep 5907019 = 8860529) B8860529
theorem B7876025 : Blo 2073435 7876025 := bstep (se 2 (by rfl) ⟨2953509, by rfl⟩ : syracuseStep 7876025 = 5907019) B5907019
theorem B5250683 : Blo 2073435 5250683 := bstep (se 1 (by rfl) ⟨3938012, by rfl⟩ : syracuseStep 5250683 = 7876025) B7876025
theorem B3500455 : Blo 2073435 3500455 := bstep (se 1 (by rfl) ⟨2625341, by rfl⟩ : syracuseStep 3500455 = 5250683) B5250683
theorem B4667273 : Blo 2073435 4667273 := bstep (se 2 (by rfl) ⟨1750227, by rfl⟩ : syracuseStep 4667273 = 3500455) B3500455
theorem B3111515 : Blo 2073435 3111515 := bstep (se 1 (by rfl) ⟨2333636, by rfl⟩ : syracuseStep 3111515 = 4667273) B4667273
theorem B2074343 : Blo 2073435 2074343 := bstep (se 1 (by rfl) ⟨1555757, by rfl⟩ : syracuseStep 2074343 = 3111515) B3111515
theorem B2333641 : Blo 2073435 2333641 := bbase (se 2 (by rfl) ⟨875115, by rfl⟩ : syracuseStep 2333641 = 1750231) (by norm_num)
theorem B3111521 : Blo 2073435 3111521 := bstep (se 2 (by rfl) ⟨1166820, by rfl⟩ : syracuseStep 3111521 = 2333641) B2333641
theorem B2074347 : Blo 2073435 2074347 := bstep (se 1 (by rfl) ⟨1555760, by rfl⟩ : syracuseStep 2074347 = 3111521) B3111521
theorem B7476101 : Blo 2073435 7476101 := bbase (se 4 (by rfl) ⟨700884, by rfl⟩ : syracuseStep 7476101 = 1401769) (by norm_num)
theorem B4984067 : Blo 2073435 4984067 := bstep (se 1 (by rfl) ⟨3738050, by rfl⟩ : syracuseStep 4984067 = 7476101) B7476101
theorem B3322711 : Blo 2073435 3322711 := bstep (se 1 (by rfl) ⟨2492033, by rfl⟩ : syracuseStep 3322711 = 4984067) B4984067
theorem B17721125 : Blo 2073435 17721125 := bstep (se 4 (by rfl) ⟨1661355, by rfl⟩ : syracuseStep 17721125 = 3322711) B3322711
theorem B11814083 : Blo 2073435 11814083 := bstep (se 1 (by rfl) ⟨8860562, by rfl⟩ : syracuseStep 11814083 = 17721125) B17721125
theorem B7876055 : Blo 2073435 7876055 := bstep (se 1 (by rfl) ⟨5907041, by rfl⟩ : syracuseStep 7876055 = 11814083) B11814083
theorem B5250703 : Blo 2073435 5250703 := bstep (se 1 (by rfl) ⟨3938027, by rfl⟩ : syracuseStep 5250703 = 7876055) B7876055
theorem B7000937 : Blo 2073435 7000937 := bstep (se 2 (by rfl) ⟨2625351, by rfl⟩ : syracuseStep 7000937 = 5250703) B5250703
theorem B4667291 : Blo 2073435 4667291 := bstep (se 1 (by rfl) ⟨3500468, by rfl⟩ : syracuseStep 4667291 = 7000937) B7000937
theorem B3111527 : Blo 2073435 3111527 := bstep (se 1 (by rfl) ⟨2333645, by rfl⟩ : syracuseStep 3111527 = 4667291) B4667291
theorem B2074351 : Blo 2073435 2074351 := bstep (se 1 (by rfl) ⟨1555763, by rfl⟩ : syracuseStep 2074351 = 3111527) B3111527
theorem B3111533 : Blo 2073435 3111533 := bbase (se 3 (by rfl) ⟨583412, by rfl⟩ : syracuseStep 3111533 = 1166825) (by norm_num)
theorem B2074355 : Blo 2073435 2074355 := bstep (se 1 (by rfl) ⟨1555766, by rfl⟩ : syracuseStep 2074355 = 3111533) B3111533
theorem B4667309 : Blo 2073435 4667309 := bbase (se 3 (by rfl) ⟨875120, by rfl⟩ : syracuseStep 4667309 = 1750241) (by norm_num)
theorem B3111539 : Blo 2073435 3111539 := bstep (se 1 (by rfl) ⟨2333654, by rfl⟩ : syracuseStep 3111539 = 4667309) B4667309
theorem B2074359 : Blo 2073435 2074359 := bstep (se 1 (by rfl) ⟨1555769, by rfl⟩ : syracuseStep 2074359 = 3111539) B3111539
theorem B5907077 : Blo 2073435 5907077 := bbase (se 4 (by rfl) ⟨553788, by rfl⟩ : syracuseStep 5907077 = 1107577) (by norm_num)
theorem B3938051 : Blo 2073435 3938051 := bstep (se 1 (by rfl) ⟨2953538, by rfl⟩ : syracuseStep 3938051 = 5907077) B5907077
theorem B2625367 : Blo 2073435 2625367 := bstep (se 1 (by rfl) ⟨1969025, by rfl⟩ : syracuseStep 2625367 = 3938051) B3938051
theorem B3500489 : Blo 2073435 3500489 := bstep (se 2 (by rfl) ⟨1312683, by rfl⟩ : syracuseStep 3500489 = 2625367) B2625367
theorem B2333659 : Blo 2073435 2333659 := bstep (se 1 (by rfl) ⟨1750244, by rfl⟩ : syracuseStep 2333659 = 3500489) B3500489
theorem B3111545 : Blo 2073435 3111545 := bstep (se 2 (by rfl) ⟨1166829, by rfl⟩ : syracuseStep 3111545 = 2333659) B2333659
theorem B2074363 : Blo 2073435 2074363 := bstep (se 1 (by rfl) ⟨1555772, by rfl⟩ : syracuseStep 2074363 = 3111545) B3111545
theorem B40416853 : Blo 2073435 40416853 := bbase (se 8 (by rfl) ⟨236817, by rfl⟩ : syracuseStep 40416853 = 473635) (by norm_num)
theorem B53889137 : Blo 2073435 53889137 := bstep (se 2 (by rfl) ⟨20208426, by rfl⟩ : syracuseStep 53889137 = 40416853) B40416853
theorem B35926091 : Blo 2073435 35926091 := bstep (se 1 (by rfl) ⟨26944568, by rfl⟩ : syracuseStep 35926091 = 53889137) B53889137
theorem B23950727 : Blo 2073435 23950727 := bstep (se 1 (by rfl) ⟨17963045, by rfl⟩ : syracuseStep 23950727 = 35926091) B35926091
theorem B15967151 : Blo 2073435 15967151 := bstep (se 1 (by rfl) ⟨11975363, by rfl⟩ : syracuseStep 15967151 = 23950727) B23950727
theorem B10644767 : Blo 2073435 10644767 := bstep (se 1 (by rfl) ⟨7983575, by rfl⟩ : syracuseStep 10644767 = 15967151) B15967151
theorem B7096511 : Blo 2073435 7096511 := bstep (se 1 (by rfl) ⟨5322383, by rfl⟩ : syracuseStep 7096511 = 10644767) B10644767
theorem B4731007 : Blo 2073435 4731007 := bstep (se 1 (by rfl) ⟨3548255, by rfl⟩ : syracuseStep 4731007 = 7096511) B7096511
theorem B6308009 : Blo 2073435 6308009 := bstep (se 2 (by rfl) ⟨2365503, by rfl⟩ : syracuseStep 6308009 = 4731007) B4731007
theorem B4205339 : Blo 2073435 4205339 := bstep (se 1 (by rfl) ⟨3154004, by rfl⟩ : syracuseStep 4205339 = 6308009) B6308009
theorem B2803559 : Blo 2073435 2803559 := bstep (se 1 (by rfl) ⟨2102669, by rfl⟩ : syracuseStep 2803559 = 4205339) B4205339
theorem B7476157 : Blo 2073435 7476157 := bstep (se 3 (by rfl) ⟨1401779, by rfl⟩ : syracuseStep 7476157 = 2803559) B2803559
theorem B39872837 : Blo 2073435 39872837 := bstep (se 4 (by rfl) ⟨3738078, by rfl⟩ : syracuseStep 39872837 = 7476157) B7476157
theorem B26581891 : Blo 2073435 26581891 := bstep (se 1 (by rfl) ⟨19936418, by rfl⟩ : syracuseStep 26581891 = 39872837) B39872837
theorem B35442521 : Blo 2073435 35442521 := bstep (se 2 (by rfl) ⟨13290945, by rfl⟩ : syracuseStep 35442521 = 26581891) B26581891
theorem B23628347 : Blo 2073435 23628347 := bstep (se 1 (by rfl) ⟨17721260, by rfl⟩ : syracuseStep 23628347 = 35442521) B35442521
theorem B15752231 : Blo 2073435 15752231 := bstep (se 1 (by rfl) ⟨11814173, by rfl⟩ : syracuseStep 15752231 = 23628347) B23628347
theorem B10501487 : Blo 2073435 10501487 := bstep (se 1 (by rfl) ⟨7876115, by rfl⟩ : syracuseStep 10501487 = 15752231) B15752231
theorem B7000991 : Blo 2073435 7000991 := bstep (se 1 (by rfl) ⟨5250743, by rfl⟩ : syracuseStep 7000991 = 10501487) B10501487
theorem B4667327 : Blo 2073435 4667327 := bstep (se 1 (by rfl) ⟨3500495, by rfl⟩ : syracuseStep 4667327 = 7000991) B7000991
theorem B3111551 : Blo 2073435 3111551 := bstep (se 1 (by rfl) ⟨2333663, by rfl⟩ : syracuseStep 3111551 = 4667327) B4667327
theorem B2074367 : Blo 2073435 2074367 := bstep (se 1 (by rfl) ⟨1555775, by rfl⟩ : syracuseStep 2074367 = 3111551) B3111551
theorem B3111557 : Blo 2073435 3111557 := bbase (se 4 (by rfl) ⟨291708, by rfl⟩ : syracuseStep 3111557 = 583417) (by norm_num)
theorem B2074371 : Blo 2073435 2074371 := bstep (se 1 (by rfl) ⟨1555778, by rfl⟩ : syracuseStep 2074371 = 3111557) B3111557
theorem B3500509 : Blo 2073435 3500509 := bbase (se 3 (by rfl) ⟨656345, by rfl⟩ : syracuseStep 3500509 = 1312691) (by norm_num)
theorem B4667345 : Blo 2073435 4667345 := bstep (se 2 (by rfl) ⟨1750254, by rfl⟩ : syracuseStep 4667345 = 3500509) B3500509
theorem B3111563 : Blo 2073435 3111563 := bstep (se 1 (by rfl) ⟨2333672, by rfl⟩ : syracuseStep 3111563 = 4667345) B4667345
theorem B2074375 : Blo 2073435 2074375 := bstep (se 1 (by rfl) ⟨1555781, by rfl⟩ : syracuseStep 2074375 = 3111563) B3111563
theorem B2333677 : Blo 2073435 2333677 := bbase (se 3 (by rfl) ⟨437564, by rfl⟩ : syracuseStep 2333677 = 875129) (by norm_num)
theorem B3111569 : Blo 2073435 3111569 := bstep (se 2 (by rfl) ⟨1166838, by rfl⟩ : syracuseStep 3111569 = 2333677) B2333677
theorem B2074379 : Blo 2073435 2074379 := bstep (se 1 (by rfl) ⟨1555784, by rfl⟩ : syracuseStep 2074379 = 3111569) B3111569
theorem B7001045 : Blo 2073435 7001045 := bbase (se 7 (by rfl) ⟨82043, by rfl⟩ : syracuseStep 7001045 = 164087) (by norm_num)
theorem B4667363 : Blo 2073435 4667363 := bstep (se 1 (by rfl) ⟨3500522, by rfl⟩ : syracuseStep 4667363 = 7001045) B7001045
theorem B3111575 : Blo 2073435 3111575 := bstep (se 1 (by rfl) ⟨2333681, by rfl⟩ : syracuseStep 3111575 = 4667363) B4667363
theorem B2074383 : Blo 2073435 2074383 := bstep (se 1 (by rfl) ⟨1555787, by rfl⟩ : syracuseStep 2074383 = 3111575) B3111575
theorem B3111581 : Blo 2073435 3111581 := bbase (se 3 (by rfl) ⟨583421, by rfl⟩ : syracuseStep 3111581 = 1166843) (by norm_num)
theorem B2074387 : Blo 2073435 2074387 := bstep (se 1 (by rfl) ⟨1555790, by rfl⟩ : syracuseStep 2074387 = 3111581) B3111581
theorem B4667381 : Blo 2073435 4667381 := bbase (se 5 (by rfl) ⟨218783, by rfl⟩ : syracuseStep 4667381 = 437567) (by norm_num)
theorem B3111587 : Blo 2073435 3111587 := bstep (se 1 (by rfl) ⟨2333690, by rfl⟩ : syracuseStep 3111587 = 4667381) B4667381
theorem B2074391 : Blo 2073435 2074391 := bstep (se 1 (by rfl) ⟨1555793, by rfl⟩ : syracuseStep 2074391 = 3111587) B3111587
theorem B6481397 : Blo 2073435 6481397 := bbase (se 5 (by rfl) ⟨303815, by rfl⟩ : syracuseStep 6481397 = 607631) (by norm_num)
theorem B4320931 : Blo 2073435 4320931 := bstep (se 1 (by rfl) ⟨3240698, by rfl⟩ : syracuseStep 4320931 = 6481397) B6481397
theorem B5761241 : Blo 2073435 5761241 := bstep (se 2 (by rfl) ⟨2160465, by rfl⟩ : syracuseStep 5761241 = 4320931) B4320931
theorem B3840827 : Blo 2073435 3840827 := bstep (se 1 (by rfl) ⟨2880620, by rfl⟩ : syracuseStep 3840827 = 5761241) B5761241
theorem B40968821 : Blo 2073435 40968821 := bstep (se 5 (by rfl) ⟨1920413, by rfl⟩ : syracuseStep 40968821 = 3840827) B3840827
theorem B27312547 : Blo 2073435 27312547 := bstep (se 1 (by rfl) ⟨20484410, by rfl⟩ : syracuseStep 27312547 = 40968821) B40968821
theorem B36416729 : Blo 2073435 36416729 := bstep (se 2 (by rfl) ⟨13656273, by rfl⟩ : syracuseStep 36416729 = 27312547) B27312547
theorem B24277819 : Blo 2073435 24277819 := bstep (se 1 (by rfl) ⟨18208364, by rfl⟩ : syracuseStep 24277819 = 36416729) B36416729
theorem B32370425 : Blo 2073435 32370425 := bstep (se 2 (by rfl) ⟨12138909, by rfl⟩ : syracuseStep 32370425 = 24277819) B24277819
theorem B21580283 : Blo 2073435 21580283 := bstep (se 1 (by rfl) ⟨16185212, by rfl⟩ : syracuseStep 21580283 = 32370425) B32370425
theorem B57547421 : Blo 2073435 57547421 := bstep (se 3 (by rfl) ⟨10790141, by rfl⟩ : syracuseStep 57547421 = 21580283) B21580283
theorem B38364947 : Blo 2073435 38364947 := bstep (se 1 (by rfl) ⟨28773710, by rfl⟩ : syracuseStep 38364947 = 57547421) B57547421
theorem B25576631 : Blo 2073435 25576631 := bstep (se 1 (by rfl) ⟨19182473, by rfl⟩ : syracuseStep 25576631 = 38364947) B38364947
theorem B17051087 : Blo 2073435 17051087 := bstep (se 1 (by rfl) ⟨12788315, by rfl⟩ : syracuseStep 17051087 = 25576631) B25576631
theorem B11367391 : Blo 2073435 11367391 := bstep (se 1 (by rfl) ⟨8525543, by rfl⟩ : syracuseStep 11367391 = 17051087) B17051087
theorem B15156521 : Blo 2073435 15156521 := bstep (se 2 (by rfl) ⟨5683695, by rfl⟩ : syracuseStep 15156521 = 11367391) B11367391
theorem B10104347 : Blo 2073435 10104347 := bstep (se 1 (by rfl) ⟨7578260, by rfl⟩ : syracuseStep 10104347 = 15156521) B15156521
theorem B26944925 : Blo 2073435 26944925 := bstep (se 3 (by rfl) ⟨5052173, by rfl⟩ : syracuseStep 26944925 = 10104347) B10104347
theorem B287412533 : Blo 2073435 287412533 := bstep (se 5 (by rfl) ⟨13472462, by rfl⟩ : syracuseStep 287412533 = 26944925) B26944925
theorem B191608355 : Blo 2073435 191608355 := bstep (se 1 (by rfl) ⟨143706266, by rfl⟩ : syracuseStep 191608355 = 287412533) B287412533
theorem B510955613 : Blo 2073435 510955613 := bstep (se 3 (by rfl) ⟨95804177, by rfl⟩ : syracuseStep 510955613 = 191608355) B191608355
theorem B340637075 : Blo 2073435 340637075 := bstep (se 1 (by rfl) ⟨255477806, by rfl⟩ : syracuseStep 340637075 = 510955613) B510955613
theorem B227091383 : Blo 2073435 227091383 := bstep (se 1 (by rfl) ⟨170318537, by rfl⟩ : syracuseStep 227091383 = 340637075) B340637075
theorem B151394255 : Blo 2073435 151394255 := bstep (se 1 (by rfl) ⟨113545691, by rfl⟩ : syracuseStep 151394255 = 227091383) B227091383
theorem B100929503 : Blo 2073435 100929503 := bstep (se 1 (by rfl) ⟨75697127, by rfl⟩ : syracuseStep 100929503 = 151394255) B151394255
theorem B67286335 : Blo 2073435 67286335 := bstep (se 1 (by rfl) ⟨50464751, by rfl⟩ : syracuseStep 67286335 = 100929503) B100929503
theorem B89715113 : Blo 2073435 89715113 := bstep (se 2 (by rfl) ⟨33643167, by rfl⟩ : syracuseStep 89715113 = 67286335) B67286335
theorem B59810075 : Blo 2073435 59810075 := bstep (se 1 (by rfl) ⟨44857556, by rfl⟩ : syracuseStep 59810075 = 89715113) B89715113
theorem B39873383 : Blo 2073435 39873383 := bstep (se 1 (by rfl) ⟨29905037, by rfl⟩ : syracuseStep 39873383 = 59810075) B59810075
theorem B26582255 : Blo 2073435 26582255 := bstep (se 1 (by rfl) ⟨19936691, by rfl⟩ : syracuseStep 26582255 = 39873383) B39873383
theorem B17721503 : Blo 2073435 17721503 := bstep (se 1 (by rfl) ⟨13291127, by rfl⟩ : syracuseStep 17721503 = 26582255) B26582255
theorem B11814335 : Blo 2073435 11814335 := bstep (se 1 (by rfl) ⟨8860751, by rfl⟩ : syracuseStep 11814335 = 17721503) B17721503
theorem B7876223 : Blo 2073435 7876223 := bstep (se 1 (by rfl) ⟨5907167, by rfl⟩ : syracuseStep 7876223 = 11814335) B11814335
theorem B5250815 : Blo 2073435 5250815 := bstep (se 1 (by rfl) ⟨3938111, by rfl⟩ : syracuseStep 5250815 = 7876223) B7876223
theorem B3500543 : Blo 2073435 3500543 := bstep (se 1 (by rfl) ⟨2625407, by rfl⟩ : syracuseStep 3500543 = 5250815) B5250815
theorem B2333695 : Blo 2073435 2333695 := bstep (se 1 (by rfl) ⟨1750271, by rfl⟩ : syracuseStep 2333695 = 3500543) B3500543
theorem B3111593 : Blo 2073435 3111593 := bstep (se 2 (by rfl) ⟨1166847, by rfl⟩ : syracuseStep 3111593 = 2333695) B2333695
theorem B2074395 : Blo 2073435 2074395 := bstep (se 1 (by rfl) ⟨1555796, by rfl⟩ : syracuseStep 2074395 = 3111593) B3111593
theorem B2953589 : Blo 2073435 2953589 := bbase (se 5 (by rfl) ⟨138449, by rfl⟩ : syracuseStep 2953589 = 276899) (by norm_num)
theorem B7876237 : Blo 2073435 7876237 := bstep (se 3 (by rfl) ⟨1476794, by rfl⟩ : syracuseStep 7876237 = 2953589) B2953589
theorem B10501649 : Blo 2073435 10501649 := bstep (se 2 (by rfl) ⟨3938118, by rfl⟩ : syracuseStep 10501649 = 7876237) B7876237
theorem B7001099 : Blo 2073435 7001099 := bstep (se 1 (by rfl) ⟨5250824, by rfl⟩ : syracuseStep 7001099 = 10501649) B10501649
theorem B4667399 : Blo 2073435 4667399 := bstep (se 1 (by rfl) ⟨3500549, by rfl⟩ : syracuseStep 4667399 = 7001099) B7001099
theorem B3111599 : Blo 2073435 3111599 := bstep (se 1 (by rfl) ⟨2333699, by rfl⟩ : syracuseStep 3111599 = 4667399) B4667399
theorem B2074399 : Blo 2073435 2074399 := bstep (se 1 (by rfl) ⟨1555799, by rfl⟩ : syracuseStep 2074399 = 3111599) B3111599
theorem B3111605 : Blo 2073435 3111605 := bbase (se 5 (by rfl) ⟨145856, by rfl⟩ : syracuseStep 3111605 = 291713) (by norm_num)
theorem B2074403 : Blo 2073435 2074403 := bstep (se 1 (by rfl) ⟨1555802, by rfl⟩ : syracuseStep 2074403 = 3111605) B3111605
theorem B5250845 : Blo 2073435 5250845 := bbase (se 3 (by rfl) ⟨984533, by rfl⟩ : syracuseStep 5250845 = 1969067) (by norm_num)
theorem B3500563 : Blo 2073435 3500563 := bstep (se 1 (by rfl) ⟨2625422, by rfl⟩ : syracuseStep 3500563 = 5250845) B5250845
theorem B4667417 : Blo 2073435 4667417 := bstep (se 2 (by rfl) ⟨1750281, by rfl⟩ : syracuseStep 4667417 = 3500563) B3500563
theorem B3111611 : Blo 2073435 3111611 := bstep (se 1 (by rfl) ⟨2333708, by rfl⟩ : syracuseStep 3111611 = 4667417) B4667417
theorem B2074407 : Blo 2073435 2074407 := bstep (se 1 (by rfl) ⟨1555805, by rfl⟩ : syracuseStep 2074407 = 3111611) B3111611
theorem B2333713 : Blo 2073435 2333713 := bbase (se 2 (by rfl) ⟨875142, by rfl⟩ : syracuseStep 2333713 = 1750285) (by norm_num)
theorem B3111617 : Blo 2073435 3111617 := bstep (se 2 (by rfl) ⟨1166856, by rfl⟩ : syracuseStep 3111617 = 2333713) B2333713
theorem B2074411 : Blo 2073435 2074411 := bstep (se 1 (by rfl) ⟨1555808, by rfl⟩ : syracuseStep 2074411 = 3111617) B3111617
theorem B3938149 : Blo 2073435 3938149 := bbase (se 4 (by rfl) ⟨369201, by rfl⟩ : syracuseStep 3938149 = 738403) (by norm_num)
theorem B5250865 : Blo 2073435 5250865 := bstep (se 2 (by rfl) ⟨1969074, by rfl⟩ : syracuseStep 5250865 = 3938149) B3938149
theorem B7001153 : Blo 2073435 7001153 := bstep (se 2 (by rfl) ⟨2625432, by rfl⟩ : syracuseStep 7001153 = 5250865) B5250865
theorem B4667435 : Blo 2073435 4667435 := bstep (se 1 (by rfl) ⟨3500576, by rfl⟩ : syracuseStep 4667435 = 7001153) B7001153
theorem B3111623 : Blo 2073435 3111623 := bstep (se 1 (by rfl) ⟨2333717, by rfl⟩ : syracuseStep 3111623 = 4667435) B4667435
theorem B2074415 : Blo 2073435 2074415 := bstep (se 1 (by rfl) ⟨1555811, by rfl⟩ : syracuseStep 2074415 = 3111623) B3111623
theorem B3111629 : Blo 2073435 3111629 := bbase (se 3 (by rfl) ⟨583430, by rfl⟩ : syracuseStep 3111629 = 1166861) (by norm_num)
theorem B2074419 : Blo 2073435 2074419 := bstep (se 1 (by rfl) ⟨1555814, by rfl⟩ : syracuseStep 2074419 = 3111629) B3111629
theorem B4667453 : Blo 2073435 4667453 := bbase (se 3 (by rfl) ⟨875147, by rfl⟩ : syracuseStep 4667453 = 1750295) (by norm_num)
theorem B3111635 : Blo 2073435 3111635 := bstep (se 1 (by rfl) ⟨2333726, by rfl⟩ : syracuseStep 3111635 = 4667453) B4667453
theorem B2074423 : Blo 2073435 2074423 := bstep (se 1 (by rfl) ⟨1555817, by rfl⟩ : syracuseStep 2074423 = 3111635) B3111635
theorem B3500597 : Blo 2073435 3500597 := bbase (se 5 (by rfl) ⟨164090, by rfl⟩ : syracuseStep 3500597 = 328181) (by norm_num)
theorem B2333731 : Blo 2073435 2333731 := bstep (se 1 (by rfl) ⟨1750298, by rfl⟩ : syracuseStep 2333731 = 3500597) B3500597
theorem B3111641 : Blo 2073435 3111641 := bstep (se 2 (by rfl) ⟨1166865, by rfl⟩ : syracuseStep 3111641 = 2333731) B2333731
theorem B2074427 : Blo 2073435 2074427 := bstep (se 1 (by rfl) ⟨1555820, by rfl⟩ : syracuseStep 2074427 = 3111641) B3111641
theorem B5907269 : Blo 2073435 5907269 := bbase (se 4 (by rfl) ⟨553806, by rfl⟩ : syracuseStep 5907269 = 1107613) (by norm_num)
theorem B15752717 : Blo 2073435 15752717 := bstep (se 3 (by rfl) ⟨2953634, by rfl⟩ : syracuseStep 15752717 = 5907269) B5907269
theorem B10501811 : Blo 2073435 10501811 := bstep (se 1 (by rfl) ⟨7876358, by rfl⟩ : syracuseStep 10501811 = 15752717) B15752717
theorem B7001207 : Blo 2073435 7001207 := bstep (se 1 (by rfl) ⟨5250905, by rfl⟩ : syracuseStep 7001207 = 10501811) B10501811
theorem B4667471 : Blo 2073435 4667471 := bstep (se 1 (by rfl) ⟨3500603, by rfl⟩ : syracuseStep 4667471 = 7001207) B7001207
theorem B3111647 : Blo 2073435 3111647 := bstep (se 1 (by rfl) ⟨2333735, by rfl⟩ : syracuseStep 3111647 = 4667471) B4667471
theorem B2074431 : Blo 2073435 2074431 := bstep (se 1 (by rfl) ⟨1555823, by rfl⟩ : syracuseStep 2074431 = 3111647) B3111647
theorem B3111653 : Blo 2073435 3111653 := bbase (se 4 (by rfl) ⟨291717, by rfl⟩ : syracuseStep 3111653 = 583435) (by norm_num)
theorem B2074435 : Blo 2073435 2074435 := bstep (se 1 (by rfl) ⟨1555826, by rfl⟩ : syracuseStep 2074435 = 3111653) B3111653
theorem B3322853 : Blo 2073435 3322853 := bbase (se 4 (by rfl) ⟨311517, by rfl⟩ : syracuseStep 3322853 = 623035) (by norm_num)
theorem B2215235 : Blo 2073435 2215235 := bstep (se 1 (by rfl) ⟨1661426, by rfl⟩ : syracuseStep 2215235 = 3322853) B3322853
theorem B5907293 : Blo 2073435 5907293 := bstep (se 3 (by rfl) ⟨1107617, by rfl⟩ : syracuseStep 5907293 = 2215235) B2215235
theorem B3938195 : Blo 2073435 3938195 := bstep (se 1 (by rfl) ⟨2953646, by rfl⟩ : syracuseStep 3938195 = 5907293) B5907293
theorem B2625463 : Blo 2073435 2625463 := bstep (se 1 (by rfl) ⟨1969097, by rfl⟩ : syracuseStep 2625463 = 3938195) B3938195
theorem B3500617 : Blo 2073435 3500617 := bstep (se 2 (by rfl) ⟨1312731, by rfl⟩ : syracuseStep 3500617 = 2625463) B2625463
theorem B4667489 : Blo 2073435 4667489 := bstep (se 2 (by rfl) ⟨1750308, by rfl⟩ : syracuseStep 4667489 = 3500617) B3500617
theorem B3111659 : Blo 2073435 3111659 := bstep (se 1 (by rfl) ⟨2333744, by rfl⟩ : syracuseStep 3111659 = 4667489) B4667489
theorem B2074439 : Blo 2073435 2074439 := bstep (se 1 (by rfl) ⟨1555829, by rfl⟩ : syracuseStep 2074439 = 3111659) B3111659
theorem B2333749 : Blo 2073435 2333749 := bbase (se 5 (by rfl) ⟨109394, by rfl⟩ : syracuseStep 2333749 = 218789) (by norm_num)
theorem B3111665 : Blo 2073435 3111665 := bstep (se 2 (by rfl) ⟨1166874, by rfl⟩ : syracuseStep 3111665 = 2333749) B2333749
theorem B2074443 : Blo 2073435 2074443 := bstep (se 1 (by rfl) ⟨1555832, by rfl⟩ : syracuseStep 2074443 = 3111665) B3111665
theorem B2625473 : Blo 2073435 2625473 := bbase (se 2 (by rfl) ⟨984552, by rfl⟩ : syracuseStep 2625473 = 1969105) (by norm_num)
theorem B7001261 : Blo 2073435 7001261 := bstep (se 3 (by rfl) ⟨1312736, by rfl⟩ : syracuseStep 7001261 = 2625473) B2625473
theorem B4667507 : Blo 2073435 4667507 := bstep (se 1 (by rfl) ⟨3500630, by rfl⟩ : syracuseStep 4667507 = 7001261) B7001261
theorem B3111671 : Blo 2073435 3111671 := bstep (se 1 (by rfl) ⟨2333753, by rfl⟩ : syracuseStep 3111671 = 4667507) B4667507
theorem B2074447 : Blo 2073435 2074447 := bstep (se 1 (by rfl) ⟨1555835, by rfl⟩ : syracuseStep 2074447 = 3111671) B3111671
theorem B3111677 : Blo 2073435 3111677 := bbase (se 3 (by rfl) ⟨583439, by rfl⟩ : syracuseStep 3111677 = 1166879) (by norm_num)
theorem B2074451 : Blo 2073435 2074451 := bstep (se 1 (by rfl) ⟨1555838, by rfl⟩ : syracuseStep 2074451 = 3111677) B3111677
theorem B4667525 : Blo 2073435 4667525 := bbase (se 4 (by rfl) ⟨437580, by rfl⟩ : syracuseStep 4667525 = 875161) (by norm_num)
theorem B3111683 : Blo 2073435 3111683 := bstep (se 1 (by rfl) ⟨2333762, by rfl⟩ : syracuseStep 3111683 = 4667525) B4667525
theorem B2074455 : Blo 2073435 2074455 := bstep (se 1 (by rfl) ⟨1555841, by rfl⟩ : syracuseStep 2074455 = 3111683) B3111683
theorem B3322885 : Blo 2073435 3322885 := bbase (se 4 (by rfl) ⟨311520, by rfl⟩ : syracuseStep 3322885 = 623041) (by norm_num)
theorem B4430513 : Blo 2073435 4430513 := bstep (se 2 (by rfl) ⟨1661442, by rfl⟩ : syracuseStep 4430513 = 3322885) B3322885
theorem B2953675 : Blo 2073435 2953675 := bstep (se 1 (by rfl) ⟨2215256, by rfl⟩ : syracuseStep 2953675 = 4430513) B4430513
theorem B3938233 : Blo 2073435 3938233 := bstep (se 2 (by rfl) ⟨1476837, by rfl⟩ : syracuseStep 3938233 = 2953675) B2953675
theorem B5250977 : Blo 2073435 5250977 := bstep (se 2 (by rfl) ⟨1969116, by rfl⟩ : syracuseStep 5250977 = 3938233) B3938233
theorem B3500651 : Blo 2073435 3500651 := bstep (se 1 (by rfl) ⟨2625488, by rfl⟩ : syracuseStep 3500651 = 5250977) B5250977
theorem B2333767 : Blo 2073435 2333767 := bstep (se 1 (by rfl) ⟨1750325, by rfl⟩ : syracuseStep 2333767 = 3500651) B3500651
theorem B3111689 : Blo 2073435 3111689 := bstep (se 2 (by rfl) ⟨1166883, by rfl⟩ : syracuseStep 3111689 = 2333767) B2333767
theorem B2074459 : Blo 2073435 2074459 := bstep (se 1 (by rfl) ⟨1555844, by rfl⟩ : syracuseStep 2074459 = 3111689) B3111689
theorem B10501973 : Blo 2073435 10501973 := bbase (se 9 (by rfl) ⟨30767, by rfl⟩ : syracuseStep 10501973 = 61535) (by norm_num)
theorem B7001315 : Blo 2073435 7001315 := bstep (se 1 (by rfl) ⟨5250986, by rfl⟩ : syracuseStep 7001315 = 10501973) B10501973
theorem B4667543 : Blo 2073435 4667543 := bstep (se 1 (by rfl) ⟨3500657, by rfl⟩ : syracuseStep 4667543 = 7001315) B7001315
theorem B3111695 : Blo 2073435 3111695 := bstep (se 1 (by rfl) ⟨2333771, by rfl⟩ : syracuseStep 3111695 = 4667543) B4667543
theorem B2074463 : Blo 2073435 2074463 := bstep (se 1 (by rfl) ⟨1555847, by rfl⟩ : syracuseStep 2074463 = 3111695) B3111695
theorem B3111701 : Blo 2073435 3111701 := bbase (se 6 (by rfl) ⟨72930, by rfl⟩ : syracuseStep 3111701 = 145861) (by norm_num)
theorem B2074467 : Blo 2073435 2074467 := bstep (se 1 (by rfl) ⟨1555850, by rfl⟩ : syracuseStep 2074467 = 3111701) B3111701
theorem B2245493 : Blo 2073435 2245493 := bbase (se 5 (by rfl) ⟨105257, by rfl⟩ : syracuseStep 2245493 = 210515) (by norm_num)
theorem B5987981 : Blo 2073435 5987981 := bstep (se 3 (by rfl) ⟨1122746, by rfl⟩ : syracuseStep 5987981 = 2245493) B2245493
theorem B3991987 : Blo 2073435 3991987 := bstep (se 1 (by rfl) ⟨2993990, by rfl⟩ : syracuseStep 3991987 = 5987981) B5987981
theorem B21290597 : Blo 2073435 21290597 := bstep (se 4 (by rfl) ⟨1995993, by rfl⟩ : syracuseStep 21290597 = 3991987) B3991987
theorem B14193731 : Blo 2073435 14193731 := bstep (se 1 (by rfl) ⟨10645298, by rfl⟩ : syracuseStep 14193731 = 21290597) B21290597
theorem B37849949 : Blo 2073435 37849949 := bstep (se 3 (by rfl) ⟨7096865, by rfl⟩ : syracuseStep 37849949 = 14193731) B14193731
theorem B25233299 : Blo 2073435 25233299 := bstep (se 1 (by rfl) ⟨18924974, by rfl⟩ : syracuseStep 25233299 = 37849949) B37849949
theorem B16822199 : Blo 2073435 16822199 := bstep (se 1 (by rfl) ⟨12616649, by rfl⟩ : syracuseStep 16822199 = 25233299) B25233299
theorem B44859197 : Blo 2073435 44859197 := bstep (se 3 (by rfl) ⟨8411099, by rfl⟩ : syracuseStep 44859197 = 16822199) B16822199
theorem B29906131 : Blo 2073435 29906131 := bstep (se 1 (by rfl) ⟨22429598, by rfl⟩ : syracuseStep 29906131 = 44859197) B44859197
theorem B39874841 : Blo 2073435 39874841 := bstep (se 2 (by rfl) ⟨14953065, by rfl⟩ : syracuseStep 39874841 = 29906131) B29906131
theorem B26583227 : Blo 2073435 26583227 := bstep (se 1 (by rfl) ⟨19937420, by rfl⟩ : syracuseStep 26583227 = 39874841) B39874841
theorem B17722151 : Blo 2073435 17722151 := bstep (se 1 (by rfl) ⟨13291613, by rfl⟩ : syracuseStep 17722151 = 26583227) B26583227
theorem B11814767 : Blo 2073435 11814767 := bstep (se 1 (by rfl) ⟨8861075, by rfl⟩ : syracuseStep 11814767 = 17722151) B17722151
theorem B7876511 : Blo 2073435 7876511 := bstep (se 1 (by rfl) ⟨5907383, by rfl⟩ : syracuseStep 7876511 = 11814767) B11814767
theorem B5251007 : Blo 2073435 5251007 := bstep (se 1 (by rfl) ⟨3938255, by rfl⟩ : syracuseStep 5251007 = 7876511) B7876511
theorem B3500671 : Blo 2073435 3500671 := bstep (se 1 (by rfl) ⟨2625503, by rfl⟩ : syracuseStep 3500671 = 5251007) B5251007
theorem B4667561 : Blo 2073435 4667561 := bstep (se 2 (by rfl) ⟨1750335, by rfl⟩ : syracuseStep 4667561 = 3500671) B3500671
theorem B3111707 : Blo 2073435 3111707 := bstep (se 1 (by rfl) ⟨2333780, by rfl⟩ : syracuseStep 3111707 = 4667561) B4667561
theorem B2074471 : Blo 2073435 2074471 := bstep (se 1 (by rfl) ⟨1555853, by rfl⟩ : syracuseStep 2074471 = 3111707) B3111707
theorem B2333785 : Blo 2073435 2333785 := bbase (se 2 (by rfl) ⟨875169, by rfl⟩ : syracuseStep 2333785 = 1750339) (by norm_num)
theorem B3111713 : Blo 2073435 3111713 := bstep (se 2 (by rfl) ⟨1166892, by rfl⟩ : syracuseStep 3111713 = 2333785) B2333785
theorem B2074475 : Blo 2073435 2074475 := bstep (se 1 (by rfl) ⟨1555856, by rfl⟩ : syracuseStep 2074475 = 3111713) B3111713
theorem B3460789 : Blo 2073435 3460789 := bbase (se 5 (by rfl) ⟨162224, by rfl⟩ : syracuseStep 3460789 = 324449) (by norm_num)
theorem B18457541 : Blo 2073435 18457541 := bstep (se 4 (by rfl) ⟨1730394, by rfl⟩ : syracuseStep 18457541 = 3460789) B3460789
theorem B12305027 : Blo 2073435 12305027 := bstep (se 1 (by rfl) ⟨9228770, by rfl⟩ : syracuseStep 12305027 = 18457541) B18457541
theorem B8203351 : Blo 2073435 8203351 := bstep (se 1 (by rfl) ⟨6152513, by rfl⟩ : syracuseStep 8203351 = 12305027) B12305027
theorem B10937801 : Blo 2073435 10937801 := bstep (se 2 (by rfl) ⟨4101675, by rfl⟩ : syracuseStep 10937801 = 8203351) B8203351
theorem B29167469 : Blo 2073435 29167469 := bstep (se 3 (by rfl) ⟨5468900, by rfl⟩ : syracuseStep 29167469 = 10937801) B10937801
theorem B19444979 : Blo 2073435 19444979 := bstep (se 1 (by rfl) ⟨14583734, by rfl⟩ : syracuseStep 19444979 = 29167469) B29167469
theorem B51853277 : Blo 2073435 51853277 := bstep (se 3 (by rfl) ⟨9722489, by rfl⟩ : syracuseStep 51853277 = 19444979) B19444979
theorem B34568851 : Blo 2073435 34568851 := bstep (se 1 (by rfl) ⟨25926638, by rfl⟩ : syracuseStep 34568851 = 51853277) B51853277
theorem B46091801 : Blo 2073435 46091801 := bstep (se 2 (by rfl) ⟨17284425, by rfl⟩ : syracuseStep 46091801 = 34568851) B34568851
theorem B122911469 : Blo 2073435 122911469 := bstep (se 3 (by rfl) ⟨23045900, by rfl⟩ : syracuseStep 122911469 = 46091801) B46091801
theorem B81940979 : Blo 2073435 81940979 := bstep (se 1 (by rfl) ⟨61455734, by rfl⟩ : syracuseStep 81940979 = 122911469) B122911469
theorem B54627319 : Blo 2073435 54627319 := bstep (se 1 (by rfl) ⟨40970489, by rfl⟩ : syracuseStep 54627319 = 81940979) B81940979
theorem B72836425 : Blo 2073435 72836425 := bstep (se 2 (by rfl) ⟨27313659, by rfl⟩ : syracuseStep 72836425 = 54627319) B54627319
theorem B388460933 : Blo 2073435 388460933 := bstep (se 4 (by rfl) ⟨36418212, by rfl⟩ : syracuseStep 388460933 = 72836425) B72836425
theorem B258973955 : Blo 2073435 258973955 := bstep (se 1 (by rfl) ⟨194230466, by rfl⟩ : syracuseStep 258973955 = 388460933) B388460933
theorem B172649303 : Blo 2073435 172649303 := bstep (se 1 (by rfl) ⟨129486977, by rfl⟩ : syracuseStep 172649303 = 258973955) B258973955
theorem B115099535 : Blo 2073435 115099535 := bstep (se 1 (by rfl) ⟨86324651, by rfl⟩ : syracuseStep 115099535 = 172649303) B172649303
theorem B76733023 : Blo 2073435 76733023 := bstep (se 1 (by rfl) ⟨57549767, by rfl⟩ : syracuseStep 76733023 = 115099535) B115099535
theorem B102310697 : Blo 2073435 102310697 := bstep (se 2 (by rfl) ⟨38366511, by rfl⟩ : syracuseStep 102310697 = 76733023) B76733023
theorem B68207131 : Blo 2073435 68207131 := bstep (se 1 (by rfl) ⟨51155348, by rfl⟩ : syracuseStep 68207131 = 102310697) B102310697
theorem B90942841 : Blo 2073435 90942841 := bstep (se 2 (by rfl) ⟨34103565, by rfl⟩ : syracuseStep 90942841 = 68207131) B68207131
theorem B121257121 : Blo 2073435 121257121 := bstep (se 2 (by rfl) ⟨45471420, by rfl⟩ : syracuseStep 121257121 = 90942841) B90942841
theorem B161676161 : Blo 2073435 161676161 := bstep (se 2 (by rfl) ⟨60628560, by rfl⟩ : syracuseStep 161676161 = 121257121) B121257121
theorem B107784107 : Blo 2073435 107784107 := bstep (se 1 (by rfl) ⟨80838080, by rfl⟩ : syracuseStep 107784107 = 161676161) B161676161
theorem B71856071 : Blo 2073435 71856071 := bstep (se 1 (by rfl) ⟨53892053, by rfl⟩ : syracuseStep 71856071 = 107784107) B107784107
theorem B47904047 : Blo 2073435 47904047 := bstep (se 1 (by rfl) ⟨35928035, by rfl⟩ : syracuseStep 47904047 = 71856071) B71856071
theorem B31936031 : Blo 2073435 31936031 := bstep (se 1 (by rfl) ⟨23952023, by rfl⟩ : syracuseStep 31936031 = 47904047) B47904047
theorem B21290687 : Blo 2073435 21290687 := bstep (se 1 (by rfl) ⟨15968015, by rfl⟩ : syracuseStep 21290687 = 31936031) B31936031
theorem B14193791 : Blo 2073435 14193791 := bstep (se 1 (by rfl) ⟨10645343, by rfl⟩ : syracuseStep 14193791 = 21290687) B21290687
theorem B9462527 : Blo 2073435 9462527 := bstep (se 1 (by rfl) ⟨7096895, by rfl⟩ : syracuseStep 9462527 = 14193791) B14193791
theorem B6308351 : Blo 2073435 6308351 := bstep (se 1 (by rfl) ⟨4731263, by rfl⟩ : syracuseStep 6308351 = 9462527) B9462527
theorem B4205567 : Blo 2073435 4205567 := bstep (se 1 (by rfl) ⟨3154175, by rfl⟩ : syracuseStep 4205567 = 6308351) B6308351
theorem B11214845 : Blo 2073435 11214845 := bstep (se 3 (by rfl) ⟨2102783, by rfl⟩ : syracuseStep 11214845 = 4205567) B4205567
theorem B7476563 : Blo 2073435 7476563 := bstep (se 1 (by rfl) ⟨5607422, by rfl⟩ : syracuseStep 7476563 = 11214845) B11214845
theorem B4984375 : Blo 2073435 4984375 := bstep (se 1 (by rfl) ⟨3738281, by rfl⟩ : syracuseStep 4984375 = 7476563) B7476563
theorem B6645833 : Blo 2073435 6645833 := bstep (se 2 (by rfl) ⟨2492187, by rfl⟩ : syracuseStep 6645833 = 4984375) B4984375
theorem B4430555 : Blo 2073435 4430555 := bstep (se 1 (by rfl) ⟨3322916, by rfl⟩ : syracuseStep 4430555 = 6645833) B6645833
theorem B2953703 : Blo 2073435 2953703 := bstep (se 1 (by rfl) ⟨2215277, by rfl⟩ : syracuseStep 2953703 = 4430555) B4430555
theorem B7876541 : Blo 2073435 7876541 := bstep (se 3 (by rfl) ⟨1476851, by rfl⟩ : syracuseStep 7876541 = 2953703) B2953703
theorem B5251027 : Blo 2073435 5251027 := bstep (se 1 (by rfl) ⟨3938270, by rfl⟩ : syracuseStep 5251027 = 7876541) B7876541
theorem B7001369 : Blo 2073435 7001369 := bstep (se 2 (by rfl) ⟨2625513, by rfl⟩ : syracuseStep 7001369 = 5251027) B5251027
theorem B4667579 : Blo 2073435 4667579 := bstep (se 1 (by rfl) ⟨3500684, by rfl⟩ : syracuseStep 4667579 = 7001369) B7001369
theorem B3111719 : Blo 2073435 3111719 := bstep (se 1 (by rfl) ⟨2333789, by rfl⟩ : syracuseStep 3111719 = 4667579) B4667579
theorem B2074479 : Blo 2073435 2074479 := bstep (se 1 (by rfl) ⟨1555859, by rfl⟩ : syracuseStep 2074479 = 3111719) B3111719
theorem B3111725 : Blo 2073435 3111725 := bbase (se 3 (by rfl) ⟨583448, by rfl⟩ : syracuseStep 3111725 = 1166897) (by norm_num)
theorem B2074483 : Blo 2073435 2074483 := bstep (se 1 (by rfl) ⟨1555862, by rfl⟩ : syracuseStep 2074483 = 3111725) B3111725
theorem B4667597 : Blo 2073435 4667597 := bbase (se 3 (by rfl) ⟨875174, by rfl⟩ : syracuseStep 4667597 = 1750349) (by norm_num)
theorem B3111731 : Blo 2073435 3111731 := bstep (se 1 (by rfl) ⟨2333798, by rfl⟩ : syracuseStep 3111731 = 4667597) B4667597
theorem B2074487 : Blo 2073435 2074487 := bstep (se 1 (by rfl) ⟨1555865, by rfl⟩ : syracuseStep 2074487 = 3111731) B3111731
theorem B2625529 : Blo 2073435 2625529 := bbase (se 2 (by rfl) ⟨984573, by rfl⟩ : syracuseStep 2625529 = 1969147) (by norm_num)
theorem B3500705 : Blo 2073435 3500705 := bstep (se 2 (by rfl) ⟨1312764, by rfl⟩ : syracuseStep 3500705 = 2625529) B2625529
theorem B2333803 : Blo 2073435 2333803 := bstep (se 1 (by rfl) ⟨1750352, by rfl⟩ : syracuseStep 2333803 = 3500705) B3500705
theorem B3111737 : Blo 2073435 3111737 := bstep (se 2 (by rfl) ⟨1166901, by rfl⟩ : syracuseStep 3111737 = 2333803) B2333803
theorem B2074491 : Blo 2073435 2074491 := bstep (se 1 (by rfl) ⟨1555868, by rfl⟩ : syracuseStep 2074491 = 3111737) B3111737
theorem B7096949 : Blo 2073435 7096949 := bbase (se 5 (by rfl) ⟨332669, by rfl⟩ : syracuseStep 7096949 = 665339) (by norm_num)
theorem B4731299 : Blo 2073435 4731299 := bstep (se 1 (by rfl) ⟨3548474, by rfl⟩ : syracuseStep 4731299 = 7096949) B7096949
theorem B3154199 : Blo 2073435 3154199 := bstep (se 1 (by rfl) ⟨2365649, by rfl⟩ : syracuseStep 3154199 = 4731299) B4731299
theorem B8411197 : Blo 2073435 8411197 := bstep (se 3 (by rfl) ⟨1577099, by rfl⟩ : syracuseStep 8411197 = 3154199) B3154199
theorem B11214929 : Blo 2073435 11214929 := bstep (se 2 (by rfl) ⟨4205598, by rfl⟩ : syracuseStep 11214929 = 8411197) B8411197
theorem B7476619 : Blo 2073435 7476619 := bstep (se 1 (by rfl) ⟨5607464, by rfl⟩ : syracuseStep 7476619 = 11214929) B11214929
theorem B9968825 : Blo 2073435 9968825 := bstep (se 2 (by rfl) ⟨3738309, by rfl⟩ : syracuseStep 9968825 = 7476619) B7476619
theorem B6645883 : Blo 2073435 6645883 := bstep (se 1 (by rfl) ⟨4984412, by rfl⟩ : syracuseStep 6645883 = 9968825) B9968825
theorem B8861177 : Blo 2073435 8861177 := bstep (se 2 (by rfl) ⟨3322941, by rfl⟩ : syracuseStep 8861177 = 6645883) B6645883
theorem B23629805 : Blo 2073435 23629805 := bstep (se 3 (by rfl) ⟨4430588, by rfl⟩ : syracuseStep 23629805 = 8861177) B8861177
theorem B15753203 : Blo 2073435 15753203 := bstep (se 1 (by rfl) ⟨11814902, by rfl⟩ : syracuseStep 15753203 = 23629805) B23629805
theorem B10502135 : Blo 2073435 10502135 := bstep (se 1 (by rfl) ⟨7876601, by rfl⟩ : syracuseStep 10502135 = 15753203) B15753203
theorem B7001423 : Blo 2073435 7001423 := bstep (se 1 (by rfl) ⟨5251067, by rfl⟩ : syracuseStep 7001423 = 10502135) B10502135
theorem B4667615 : Blo 2073435 4667615 := bstep (se 1 (by rfl) ⟨3500711, by rfl⟩ : syracuseStep 4667615 = 7001423) B7001423
theorem B3111743 : Blo 2073435 3111743 := bstep (se 1 (by rfl) ⟨2333807, by rfl⟩ : syracuseStep 3111743 = 4667615) B4667615
theorem B2074495 : Blo 2073435 2074495 := bstep (se 1 (by rfl) ⟨1555871, by rfl⟩ : syracuseStep 2074495 = 3111743) B3111743
theorem B3111749 : Blo 2073435 3111749 := bbase (se 4 (by rfl) ⟨291726, by rfl⟩ : syracuseStep 3111749 = 583453) (by norm_num)
theorem B2074499 : Blo 2073435 2074499 := bstep (se 1 (by rfl) ⟨1555874, by rfl⟩ : syracuseStep 2074499 = 3111749) B3111749
theorem B3500725 : Blo 2073435 3500725 := bbase (se 5 (by rfl) ⟨164096, by rfl⟩ : syracuseStep 3500725 = 328193) (by norm_num)
theorem B4667633 : Blo 2073435 4667633 := bstep (se 2 (by rfl) ⟨1750362, by rfl⟩ : syracuseStep 4667633 = 3500725) B3500725
theorem B3111755 : Blo 2073435 3111755 := bstep (se 1 (by rfl) ⟨2333816, by rfl⟩ : syracuseStep 3111755 = 4667633) B4667633
theorem B2074503 : Blo 2073435 2074503 := bstep (se 1 (by rfl) ⟨1555877, by rfl⟩ : syracuseStep 2074503 = 3111755) B3111755
theorem B2333821 : Blo 2073435 2333821 := bbase (se 3 (by rfl) ⟨437591, by rfl⟩ : syracuseStep 2333821 = 875183) (by norm_num)
theorem B3111761 : Blo 2073435 3111761 := bstep (se 2 (by rfl) ⟨1166910, by rfl⟩ : syracuseStep 3111761 = 2333821) B2333821
theorem B2074507 : Blo 2073435 2074507 := bstep (se 1 (by rfl) ⟨1555880, by rfl⟩ : syracuseStep 2074507 = 3111761) B3111761
theorem B7001477 : Blo 2073435 7001477 := bbase (se 4 (by rfl) ⟨656388, by rfl⟩ : syracuseStep 7001477 = 1312777) (by norm_num)
theorem B4667651 : Blo 2073435 4667651 := bstep (se 1 (by rfl) ⟨3500738, by rfl⟩ : syracuseStep 4667651 = 7001477) B7001477
theorem B3111767 : Blo 2073435 3111767 := bstep (se 1 (by rfl) ⟨2333825, by rfl⟩ : syracuseStep 3111767 = 4667651) B4667651
theorem B2074511 : Blo 2073435 2074511 := bstep (se 1 (by rfl) ⟨1555883, by rfl⟩ : syracuseStep 2074511 = 3111767) B3111767
theorem B3111773 : Blo 2073435 3111773 := bbase (se 3 (by rfl) ⟨583457, by rfl⟩ : syracuseStep 3111773 = 1166915) (by norm_num)
theorem B2074515 : Blo 2073435 2074515 := bstep (se 1 (by rfl) ⟨1555886, by rfl⟩ : syracuseStep 2074515 = 3111773) B3111773
theorem B4667669 : Blo 2073435 4667669 := bbase (se 6 (by rfl) ⟨109398, by rfl⟩ : syracuseStep 4667669 = 218797) (by norm_num)
theorem B3111779 : Blo 2073435 3111779 := bstep (se 1 (by rfl) ⟨2333834, by rfl⟩ : syracuseStep 3111779 = 4667669) B4667669
theorem B2074519 : Blo 2073435 2074519 := bstep (se 1 (by rfl) ⟨1555889, by rfl⟩ : syracuseStep 2074519 = 3111779) B3111779
theorem B7876709 : Blo 2073435 7876709 := bbase (se 4 (by rfl) ⟨738441, by rfl⟩ : syracuseStep 7876709 = 1476883) (by norm_num)
theorem B5251139 : Blo 2073435 5251139 := bstep (se 1 (by rfl) ⟨3938354, by rfl⟩ : syracuseStep 5251139 = 7876709) B7876709
theorem B3500759 : Blo 2073435 3500759 := bstep (se 1 (by rfl) ⟨2625569, by rfl⟩ : syracuseStep 3500759 = 5251139) B5251139
theorem B2333839 : Blo 2073435 2333839 := bstep (se 1 (by rfl) ⟨1750379, by rfl⟩ : syracuseStep 2333839 = 3500759) B3500759
theorem B3111785 : Blo 2073435 3111785 := bstep (se 2 (by rfl) ⟨1166919, by rfl⟩ : syracuseStep 3111785 = 2333839) B2333839
theorem B2074523 : Blo 2073435 2074523 := bstep (se 1 (by rfl) ⟨1555892, by rfl⟩ : syracuseStep 2074523 = 3111785) B3111785
theorem B2492245 : Blo 2073435 2492245 := bbase (se 9 (by rfl) ⟨7301, by rfl⟩ : syracuseStep 2492245 = 14603) (by norm_num)
theorem B3322993 : Blo 2073435 3322993 := bstep (se 2 (by rfl) ⟨1246122, by rfl⟩ : syracuseStep 3322993 = 2492245) B2492245
theorem B4430657 : Blo 2073435 4430657 := bstep (se 2 (by rfl) ⟨1661496, by rfl⟩ : syracuseStep 4430657 = 3322993) B3322993
theorem B11815085 : Blo 2073435 11815085 := bstep (se 3 (by rfl) ⟨2215328, by rfl⟩ : syracuseStep 11815085 = 4430657) B4430657
theorem B7876723 : Blo 2073435 7876723 := bstep (se 1 (by rfl) ⟨5907542, by rfl⟩ : syracuseStep 7876723 = 11815085) B11815085
theorem B10502297 : Blo 2073435 10502297 := bstep (se 2 (by rfl) ⟨3938361, by rfl⟩ : syracuseStep 10502297 = 7876723) B7876723
theorem B7001531 : Blo 2073435 7001531 := bstep (se 1 (by rfl) ⟨5251148, by rfl⟩ : syracuseStep 7001531 = 10502297) B10502297
theorem B4667687 : Blo 2073435 4667687 := bstep (se 1 (by rfl) ⟨3500765, by rfl⟩ : syracuseStep 4667687 = 7001531) B7001531
theorem B3111791 : Blo 2073435 3111791 := bstep (se 1 (by rfl) ⟨2333843, by rfl⟩ : syracuseStep 3111791 = 4667687) B4667687
theorem B2074527 : Blo 2073435 2074527 := bstep (se 1 (by rfl) ⟨1555895, by rfl⟩ : syracuseStep 2074527 = 3111791) B3111791
theorem B3111797 : Blo 2073435 3111797 := bbase (se 5 (by rfl) ⟨145865, by rfl⟩ : syracuseStep 3111797 = 291731) (by norm_num)
theorem B2074531 : Blo 2073435 2074531 := bstep (se 1 (by rfl) ⟨1555898, by rfl⟩ : syracuseStep 2074531 = 3111797) B3111797
theorem B12617045 : Blo 2073435 12617045 := bbase (se 12 (by rfl) ⟨4620, by rfl⟩ : syracuseStep 12617045 = 9241) (by norm_num)
theorem B8411363 : Blo 2073435 8411363 := bstep (se 1 (by rfl) ⟨6308522, by rfl⟩ : syracuseStep 8411363 = 12617045) B12617045
theorem B5607575 : Blo 2073435 5607575 := bstep (se 1 (by rfl) ⟨4205681, by rfl⟩ : syracuseStep 5607575 = 8411363) B8411363
theorem B3738383 : Blo 2073435 3738383 := bstep (se 1 (by rfl) ⟨2803787, by rfl⟩ : syracuseStep 3738383 = 5607575) B5607575
theorem B2492255 : Blo 2073435 2492255 := bstep (se 1 (by rfl) ⟨1869191, by rfl⟩ : syracuseStep 2492255 = 3738383) B3738383
theorem B6646013 : Blo 2073435 6646013 := bstep (se 3 (by rfl) ⟨1246127, by rfl⟩ : syracuseStep 6646013 = 2492255) B2492255
theorem B4430675 : Blo 2073435 4430675 := bstep (se 1 (by rfl) ⟨3323006, by rfl⟩ : syracuseStep 4430675 = 6646013) B6646013
theorem B2953783 : Blo 2073435 2953783 := bstep (se 1 (by rfl) ⟨2215337, by rfl⟩ : syracuseStep 2953783 = 4430675) B4430675
theorem B3938377 : Blo 2073435 3938377 := bstep (se 2 (by rfl) ⟨1476891, by rfl⟩ : syracuseStep 3938377 = 2953783) B2953783
theorem B5251169 : Blo 2073435 5251169 := bstep (se 2 (by rfl) ⟨1969188, by rfl⟩ : syracuseStep 5251169 = 3938377) B3938377
theorem B3500779 : Blo 2073435 3500779 := bstep (se 1 (by rfl) ⟨2625584, by rfl⟩ : syracuseStep 3500779 = 5251169) B5251169
theorem B4667705 : Blo 2073435 4667705 := bstep (se 2 (by rfl) ⟨1750389, by rfl⟩ : syracuseStep 4667705 = 3500779) B3500779
theorem B3111803 : Blo 2073435 3111803 := bstep (se 1 (by rfl) ⟨2333852, by rfl⟩ : syracuseStep 3111803 = 4667705) B4667705
theorem B2074535 : Blo 2073435 2074535 := bstep (se 1 (by rfl) ⟨1555901, by rfl⟩ : syracuseStep 2074535 = 3111803) B3111803
theorem B2333857 : Blo 2073435 2333857 := bbase (se 2 (by rfl) ⟨875196, by rfl⟩ : syracuseStep 2333857 = 1750393) (by norm_num)
theorem B3111809 : Blo 2073435 3111809 := bstep (se 2 (by rfl) ⟨1166928, by rfl⟩ : syracuseStep 3111809 = 2333857) B2333857
theorem B2074539 : Blo 2073435 2074539 := bstep (se 1 (by rfl) ⟨1555904, by rfl⟩ : syracuseStep 2074539 = 3111809) B3111809
theorem B5251189 : Blo 2073435 5251189 := bbase (se 5 (by rfl) ⟨246149, by rfl⟩ : syracuseStep 5251189 = 492299) (by norm_num)
theorem B7001585 : Blo 2073435 7001585 := bstep (se 2 (by rfl) ⟨2625594, by rfl⟩ : syracuseStep 7001585 = 5251189) B5251189
theorem B4667723 : Blo 2073435 4667723 := bstep (se 1 (by rfl) ⟨3500792, by rfl⟩ : syracuseStep 4667723 = 7001585) B7001585
theorem B3111815 : Blo 2073435 3111815 := bstep (se 1 (by rfl) ⟨2333861, by rfl⟩ : syracuseStep 3111815 = 4667723) B4667723
theorem B2074543 : Blo 2073435 2074543 := bstep (se 1 (by rfl) ⟨1555907, by rfl⟩ : syracuseStep 2074543 = 3111815) B3111815
theorem B3111821 : Blo 2073435 3111821 := bbase (se 3 (by rfl) ⟨583466, by rfl⟩ : syracuseStep 3111821 = 1166933) (by norm_num)
theorem B2074547 : Blo 2073435 2074547 := bstep (se 1 (by rfl) ⟨1555910, by rfl⟩ : syracuseStep 2074547 = 3111821) B3111821
theorem B4667741 : Blo 2073435 4667741 := bbase (se 3 (by rfl) ⟨875201, by rfl⟩ : syracuseStep 4667741 = 1750403) (by norm_num)
theorem B3111827 : Blo 2073435 3111827 := bstep (se 1 (by rfl) ⟨2333870, by rfl⟩ : syracuseStep 3111827 = 4667741) B4667741
theorem B2074551 : Blo 2073435 2074551 := bstep (se 1 (by rfl) ⟨1555913, by rfl⟩ : syracuseStep 2074551 = 3111827) B3111827
theorem B3500813 : Blo 2073435 3500813 := bbase (se 3 (by rfl) ⟨656402, by rfl⟩ : syracuseStep 3500813 = 1312805) (by norm_num)
theorem B2333875 : Blo 2073435 2333875 := bstep (se 1 (by rfl) ⟨1750406, by rfl⟩ : syracuseStep 2333875 = 3500813) B3500813
theorem B3111833 : Blo 2073435 3111833 := bstep (se 2 (by rfl) ⟨1166937, by rfl⟩ : syracuseStep 3111833 = 2333875) B2333875
theorem B2074555 : Blo 2073435 2074555 := bstep (se 1 (by rfl) ⟨1555916, by rfl⟩ : syracuseStep 2074555 = 3111833) B3111833
theorem B17722901 : Blo 2073435 17722901 := bbase (se 6 (by rfl) ⟨415380, by rfl⟩ : syracuseStep 17722901 = 830761) (by norm_num)
theorem B11815267 : Blo 2073435 11815267 := bstep (se 1 (by rfl) ⟨8861450, by rfl⟩ : syracuseStep 11815267 = 17722901) B17722901
theorem B15753689 : Blo 2073435 15753689 := bstep (se 2 (by rfl) ⟨5907633, by rfl⟩ : syracuseStep 15753689 = 11815267) B11815267
theorem B10502459 : Blo 2073435 10502459 := bstep (se 1 (by rfl) ⟨7876844, by rfl⟩ : syracuseStep 10502459 = 15753689) B15753689
theorem B7001639 : Blo 2073435 7001639 := bstep (se 1 (by rfl) ⟨5251229, by rfl⟩ : syracuseStep 7001639 = 10502459) B10502459
theorem B4667759 : Blo 2073435 4667759 := bstep (se 1 (by rfl) ⟨3500819, by rfl⟩ : syracuseStep 4667759 = 7001639) B7001639
theorem B3111839 : Blo 2073435 3111839 := bstep (se 1 (by rfl) ⟨2333879, by rfl⟩ : syracuseStep 3111839 = 4667759) B4667759
theorem B2074559 : Blo 2073435 2074559 := bstep (se 1 (by rfl) ⟨1555919, by rfl⟩ : syracuseStep 2074559 = 3111839) B3111839
theorem B3111845 : Blo 2073435 3111845 := bbase (se 4 (by rfl) ⟨291735, by rfl⟩ : syracuseStep 3111845 = 583471) (by norm_num)
theorem B2074563 : Blo 2073435 2074563 := bstep (se 1 (by rfl) ⟨1555922, by rfl⟩ : syracuseStep 2074563 = 3111845) B3111845
theorem B2625625 : Blo 2073435 2625625 := bbase (se 2 (by rfl) ⟨984609, by rfl⟩ : syracuseStep 2625625 = 1969219) (by norm_num)
theorem B3500833 : Blo 2073435 3500833 := bstep (se 2 (by rfl) ⟨1312812, by rfl⟩ : syracuseStep 3500833 = 2625625) B2625625
theorem B4667777 : Blo 2073435 4667777 := bstep (se 2 (by rfl) ⟨1750416, by rfl⟩ : syracuseStep 4667777 = 3500833) B3500833
theorem B3111851 : Blo 2073435 3111851 := bstep (se 1 (by rfl) ⟨2333888, by rfl⟩ : syracuseStep 3111851 = 4667777) B4667777
theorem B2074567 : Blo 2073435 2074567 := bstep (se 1 (by rfl) ⟨1555925, by rfl⟩ : syracuseStep 2074567 = 3111851) B3111851
theorem B2333893 : Blo 2073435 2333893 := bbase (se 4 (by rfl) ⟨218802, by rfl⟩ : syracuseStep 2333893 = 437605) (by norm_num)
theorem B3111857 : Blo 2073435 3111857 := bstep (se 2 (by rfl) ⟨1166946, by rfl⟩ : syracuseStep 3111857 = 2333893) B2333893
theorem B2074571 : Blo 2073435 2074571 := bstep (se 1 (by rfl) ⟨1555928, by rfl⟩ : syracuseStep 2074571 = 3111857) B3111857
theorem B3938453 : Blo 2073435 3938453 := bbase (se 6 (by rfl) ⟨92307, by rfl⟩ : syracuseStep 3938453 = 184615) (by norm_num)
theorem B2625635 : Blo 2073435 2625635 := bstep (se 1 (by rfl) ⟨1969226, by rfl⟩ : syracuseStep 2625635 = 3938453) B3938453
theorem B7001693 : Blo 2073435 7001693 := bstep (se 3 (by rfl) ⟨1312817, by rfl⟩ : syracuseStep 7001693 = 2625635) B2625635
theorem B4667795 : Blo 2073435 4667795 := bstep (se 1 (by rfl) ⟨3500846, by rfl⟩ : syracuseStep 4667795 = 7001693) B7001693
theorem B3111863 : Blo 2073435 3111863 := bstep (se 1 (by rfl) ⟨2333897, by rfl⟩ : syracuseStep 3111863 = 4667795) B4667795
theorem B2074575 : Blo 2073435 2074575 := bstep (se 1 (by rfl) ⟨1555931, by rfl⟩ : syracuseStep 2074575 = 3111863) B3111863
theorem B3111869 : Blo 2073435 3111869 := bbase (se 3 (by rfl) ⟨583475, by rfl⟩ : syracuseStep 3111869 = 1166951) (by norm_num)
theorem B2074579 : Blo 2073435 2074579 := bstep (se 1 (by rfl) ⟨1555934, by rfl⟩ : syracuseStep 2074579 = 3111869) B3111869
theorem B4667813 : Blo 2073435 4667813 := bbase (se 4 (by rfl) ⟨437607, by rfl⟩ : syracuseStep 4667813 = 875215) (by norm_num)
theorem B3111875 : Blo 2073435 3111875 := bstep (se 1 (by rfl) ⟨2333906, by rfl⟩ : syracuseStep 3111875 = 4667813) B4667813
theorem B2074583 : Blo 2073435 2074583 := bstep (se 1 (by rfl) ⟨1555937, by rfl⟩ : syracuseStep 2074583 = 3111875) B3111875
theorem B5251301 : Blo 2073435 5251301 := bbase (se 4 (by rfl) ⟨492309, by rfl⟩ : syracuseStep 5251301 = 984619) (by norm_num)
theorem B3500867 : Blo 2073435 3500867 := bstep (se 1 (by rfl) ⟨2625650, by rfl⟩ : syracuseStep 3500867 = 5251301) B5251301
theorem B2333911 : Blo 2073435 2333911 := bstep (se 1 (by rfl) ⟨1750433, by rfl⟩ : syracuseStep 2333911 = 3500867) B3500867
theorem B3111881 : Blo 2073435 3111881 := bstep (se 2 (by rfl) ⟨1166955, by rfl⟩ : syracuseStep 3111881 = 2333911) B2333911
theorem B2074587 : Blo 2073435 2074587 := bstep (se 1 (by rfl) ⟨1555940, by rfl⟩ : syracuseStep 2074587 = 3111881) B3111881
theorem B2215397 : Blo 2073435 2215397 := bbase (se 4 (by rfl) ⟨207693, by rfl⟩ : syracuseStep 2215397 = 415387) (by norm_num)
theorem B5907725 : Blo 2073435 5907725 := bstep (se 3 (by rfl) ⟨1107698, by rfl⟩ : syracuseStep 5907725 = 2215397) B2215397
theorem B3938483 : Blo 2073435 3938483 := bstep (se 1 (by rfl) ⟨2953862, by rfl⟩ : syracuseStep 3938483 = 5907725) B5907725
theorem B10502621 : Blo 2073435 10502621 := bstep (se 3 (by rfl) ⟨1969241, by rfl⟩ : syracuseStep 10502621 = 3938483) B3938483
theorem B7001747 : Blo 2073435 7001747 := bstep (se 1 (by rfl) ⟨5251310, by rfl⟩ : syracuseStep 7001747 = 10502621) B10502621
theorem B4667831 : Blo 2073435 4667831 := bstep (se 1 (by rfl) ⟨3500873, by rfl⟩ : syracuseStep 4667831 = 7001747) B7001747
theorem B3111887 : Blo 2073435 3111887 := bstep (se 1 (by rfl) ⟨2333915, by rfl⟩ : syracuseStep 3111887 = 4667831) B4667831
theorem B2074591 : Blo 2073435 2074591 := bstep (se 1 (by rfl) ⟨1555943, by rfl⟩ : syracuseStep 2074591 = 3111887) B3111887
theorem B3111893 : Blo 2073435 3111893 := bbase (se 7 (by rfl) ⟨36467, by rfl⟩ : syracuseStep 3111893 = 72935) (by norm_num)
theorem B2074595 : Blo 2073435 2074595 := bstep (se 1 (by rfl) ⟨1555946, by rfl⟩ : syracuseStep 2074595 = 3111893) B3111893
theorem B7876997 : Blo 2073435 7876997 := bbase (se 4 (by rfl) ⟨738468, by rfl⟩ : syracuseStep 7876997 = 1476937) (by norm_num)
theorem B5251331 : Blo 2073435 5251331 := bstep (se 1 (by rfl) ⟨3938498, by rfl⟩ : syracuseStep 5251331 = 7876997) B7876997
theorem B3500887 : Blo 2073435 3500887 := bstep (se 1 (by rfl) ⟨2625665, by rfl⟩ : syracuseStep 3500887 = 5251331) B5251331
theorem B4667849 : Blo 2073435 4667849 := bstep (se 2 (by rfl) ⟨1750443, by rfl⟩ : syracuseStep 4667849 = 3500887) B3500887
theorem B3111899 : Blo 2073435 3111899 := bstep (se 1 (by rfl) ⟨2333924, by rfl⟩ : syracuseStep 3111899 = 4667849) B4667849
theorem B2074599 : Blo 2073435 2074599 := bstep (se 1 (by rfl) ⟨1555949, by rfl⟩ : syracuseStep 2074599 = 3111899) B3111899
theorem B2333929 : Blo 2073435 2333929 := bbase (se 2 (by rfl) ⟨875223, by rfl⟩ : syracuseStep 2333929 = 1750447) (by norm_num)
theorem B3111905 : Blo 2073435 3111905 := bstep (se 2 (by rfl) ⟨1166964, by rfl⟩ : syracuseStep 3111905 = 2333929) B2333929
theorem B2074603 : Blo 2073435 2074603 := bstep (se 1 (by rfl) ⟨1555952, by rfl⟩ : syracuseStep 2074603 = 3111905) B3111905
theorem B11815541 : Blo 2073435 11815541 := bbase (se 5 (by rfl) ⟨553853, by rfl⟩ : syracuseStep 11815541 = 1107707) (by norm_num)
theorem B7877027 : Blo 2073435 7877027 := bstep (se 1 (by rfl) ⟨5907770, by rfl⟩ : syracuseStep 7877027 = 11815541) B11815541
theorem B5251351 : Blo 2073435 5251351 := bstep (se 1 (by rfl) ⟨3938513, by rfl⟩ : syracuseStep 5251351 = 7877027) B7877027
theorem B7001801 : Blo 2073435 7001801 := bstep (se 2 (by rfl) ⟨2625675, by rfl⟩ : syracuseStep 7001801 = 5251351) B5251351
theorem B4667867 : Blo 2073435 4667867 := bstep (se 1 (by rfl) ⟨3500900, by rfl⟩ : syracuseStep 4667867 = 7001801) B7001801
theorem B3111911 : Blo 2073435 3111911 := bstep (se 1 (by rfl) ⟨2333933, by rfl⟩ : syracuseStep 3111911 = 4667867) B4667867
theorem B2074607 : Blo 2073435 2074607 := bstep (se 1 (by rfl) ⟨1555955, by rfl⟩ : syracuseStep 2074607 = 3111911) B3111911
theorem B3111917 : Blo 2073435 3111917 := bbase (se 3 (by rfl) ⟨583484, by rfl⟩ : syracuseStep 3111917 = 1166969) (by norm_num)
theorem B2074611 : Blo 2073435 2074611 := bstep (se 1 (by rfl) ⟨1555958, by rfl⟩ : syracuseStep 2074611 = 3111917) B3111917
theorem B4667885 : Blo 2073435 4667885 := bbase (se 3 (by rfl) ⟨875228, by rfl⟩ : syracuseStep 4667885 = 1750457) (by norm_num)
theorem B3111923 : Blo 2073435 3111923 := bstep (se 1 (by rfl) ⟨2333942, by rfl⟩ : syracuseStep 3111923 = 4667885) B4667885
theorem B2074615 : Blo 2073435 2074615 := bstep (se 1 (by rfl) ⟨1555961, by rfl⟩ : syracuseStep 2074615 = 3111923) B3111923
theorem B2803901 : Blo 2073435 2803901 := bbase (se 3 (by rfl) ⟨525731, by rfl⟩ : syracuseStep 2803901 = 1051463) (by norm_num)
theorem B7477069 : Blo 2073435 7477069 := bstep (se 3 (by rfl) ⟨1401950, by rfl⟩ : syracuseStep 7477069 = 2803901) B2803901
theorem B9969425 : Blo 2073435 9969425 := bstep (se 2 (by rfl) ⟨3738534, by rfl⟩ : syracuseStep 9969425 = 7477069) B7477069
theorem B6646283 : Blo 2073435 6646283 := bstep (se 1 (by rfl) ⟨4984712, by rfl⟩ : syracuseStep 6646283 = 9969425) B9969425
theorem B4430855 : Blo 2073435 4430855 := bstep (se 1 (by rfl) ⟨3323141, by rfl⟩ : syracuseStep 4430855 = 6646283) B6646283
theorem B2953903 : Blo 2073435 2953903 := bstep (se 1 (by rfl) ⟨2215427, by rfl⟩ : syracuseStep 2953903 = 4430855) B4430855
theorem B3938537 : Blo 2073435 3938537 := bstep (se 2 (by rfl) ⟨1476951, by rfl⟩ : syracuseStep 3938537 = 2953903) B2953903
theorem B2625691 : Blo 2073435 2625691 := bstep (se 1 (by rfl) ⟨1969268, by rfl⟩ : syracuseStep 2625691 = 3938537) B3938537
theorem B3500921 : Blo 2073435 3500921 := bstep (se 2 (by rfl) ⟨1312845, by rfl⟩ : syracuseStep 3500921 = 2625691) B2625691
theorem B2333947 : Blo 2073435 2333947 := bstep (se 1 (by rfl) ⟨1750460, by rfl⟩ : syracuseStep 2333947 = 3500921) B3500921
theorem B3111929 : Blo 2073435 3111929 := bstep (se 2 (by rfl) ⟨1166973, by rfl⟩ : syracuseStep 3111929 = 2333947) B2333947
theorem B2074619 : Blo 2073435 2074619 := bstep (se 1 (by rfl) ⟨1555964, by rfl⟩ : syracuseStep 2074619 = 3111929) B3111929
theorem B5191541 : Blo 2073435 5191541 := bbase (se 5 (by rfl) ⟨243353, by rfl⟩ : syracuseStep 5191541 = 486707) (by norm_num)
theorem B3461027 : Blo 2073435 3461027 := bstep (se 1 (by rfl) ⟨2595770, by rfl⟩ : syracuseStep 3461027 = 5191541) B5191541
theorem B9229405 : Blo 2073435 9229405 := bstep (se 3 (by rfl) ⟨1730513, by rfl⟩ : syracuseStep 9229405 = 3461027) B3461027
theorem B12305873 : Blo 2073435 12305873 := bstep (se 2 (by rfl) ⟨4614702, by rfl⟩ : syracuseStep 12305873 = 9229405) B9229405
theorem B8203915 : Blo 2073435 8203915 := bstep (se 1 (by rfl) ⟨6152936, by rfl⟩ : syracuseStep 8203915 = 12305873) B12305873
theorem B10938553 : Blo 2073435 10938553 := bstep (se 2 (by rfl) ⟨4101957, by rfl⟩ : syracuseStep 10938553 = 8203915) B8203915
theorem B58338949 : Blo 2073435 58338949 := bstep (se 4 (by rfl) ⟨5469276, by rfl⟩ : syracuseStep 58338949 = 10938553) B10938553
theorem B77785265 : Blo 2073435 77785265 := bstep (se 2 (by rfl) ⟨29169474, by rfl⟩ : syracuseStep 77785265 = 58338949) B58338949
theorem B51856843 : Blo 2073435 51856843 := bstep (se 1 (by rfl) ⟨38892632, by rfl⟩ : syracuseStep 51856843 = 77785265) B77785265
theorem B69142457 : Blo 2073435 69142457 := bstep (se 2 (by rfl) ⟨25928421, by rfl⟩ : syracuseStep 69142457 = 51856843) B51856843
theorem B46094971 : Blo 2073435 46094971 := bstep (se 1 (by rfl) ⟨34571228, by rfl⟩ : syracuseStep 46094971 = 69142457) B69142457
theorem B61459961 : Blo 2073435 61459961 := bstep (se 2 (by rfl) ⟨23047485, by rfl⟩ : syracuseStep 61459961 = 46094971) B46094971
theorem B163893229 : Blo 2073435 163893229 := bstep (se 3 (by rfl) ⟨30729980, by rfl⟩ : syracuseStep 163893229 = 61459961) B61459961
theorem B3496388885 : Blo 2073435 3496388885 := bstep (se 6 (by rfl) ⟨81946614, by rfl⟩ : syracuseStep 3496388885 = 163893229) B163893229
theorem B2330925923 : Blo 2073435 2330925923 := bstep (se 1 (by rfl) ⟨1748194442, by rfl⟩ : syracuseStep 2330925923 = 3496388885) B3496388885
theorem B1553950615 : Blo 2073435 1553950615 := bstep (se 1 (by rfl) ⟨1165462961, by rfl⟩ : syracuseStep 1553950615 = 2330925923) B2330925923
theorem B2071934153 : Blo 2073435 2071934153 := bstep (se 2 (by rfl) ⟨776975307, by rfl⟩ : syracuseStep 2071934153 = 1553950615) B1553950615
theorem B1381289435 : Blo 2073435 1381289435 := bstep (se 1 (by rfl) ⟨1035967076, by rfl⟩ : syracuseStep 1381289435 = 2071934153) B2071934153
theorem B920859623 : Blo 2073435 920859623 := bstep (se 1 (by rfl) ⟨690644717, by rfl⟩ : syracuseStep 920859623 = 1381289435) B1381289435
theorem B613906415 : Blo 2073435 613906415 := bstep (se 1 (by rfl) ⟨460429811, by rfl⟩ : syracuseStep 613906415 = 920859623) B920859623
theorem B409270943 : Blo 2073435 409270943 := bstep (se 1 (by rfl) ⟨306953207, by rfl⟩ : syracuseStep 409270943 = 613906415) B613906415
theorem B272847295 : Blo 2073435 272847295 := bstep (se 1 (by rfl) ⟨204635471, by rfl⟩ : syracuseStep 272847295 = 409270943) B409270943
theorem B363796393 : Blo 2073435 363796393 := bstep (se 2 (by rfl) ⟨136423647, by rfl⟩ : syracuseStep 363796393 = 272847295) B272847295
theorem B485061857 : Blo 2073435 485061857 := bstep (se 2 (by rfl) ⟨181898196, by rfl⟩ : syracuseStep 485061857 = 363796393) B363796393
theorem B323374571 : Blo 2073435 323374571 := bstep (se 1 (by rfl) ⟨242530928, by rfl⟩ : syracuseStep 323374571 = 485061857) B485061857
theorem B215583047 : Blo 2073435 215583047 := bstep (se 1 (by rfl) ⟨161687285, by rfl⟩ : syracuseStep 215583047 = 323374571) B323374571
theorem B143722031 : Blo 2073435 143722031 := bstep (se 1 (by rfl) ⟨107791523, by rfl⟩ : syracuseStep 143722031 = 215583047) B215583047
theorem B383258749 : Blo 2073435 383258749 := bstep (se 3 (by rfl) ⟨71861015, by rfl⟩ : syracuseStep 383258749 = 143722031) B143722031
theorem B511011665 : Blo 2073435 511011665 := bstep (se 2 (by rfl) ⟨191629374, by rfl⟩ : syracuseStep 511011665 = 383258749) B383258749
theorem B340674443 : Blo 2073435 340674443 := bstep (se 1 (by rfl) ⟨255505832, by rfl⟩ : syracuseStep 340674443 = 511011665) B511011665
theorem B227116295 : Blo 2073435 227116295 := bstep (se 1 (by rfl) ⟨170337221, by rfl⟩ : syracuseStep 227116295 = 340674443) B340674443
theorem B151410863 : Blo 2073435 151410863 := bstep (se 1 (by rfl) ⟨113558147, by rfl⟩ : syracuseStep 151410863 = 227116295) B227116295
theorem B100940575 : Blo 2073435 100940575 := bstep (se 1 (by rfl) ⟨75705431, by rfl⟩ : syracuseStep 100940575 = 151410863) B151410863
theorem B134587433 : Blo 2073435 134587433 := bstep (se 2 (by rfl) ⟨50470287, by rfl⟩ : syracuseStep 134587433 = 100940575) B100940575
theorem B89724955 : Blo 2073435 89724955 := bstep (se 1 (by rfl) ⟨67293716, by rfl⟩ : syracuseStep 89724955 = 134587433) B134587433
theorem B119633273 : Blo 2073435 119633273 := bstep (se 2 (by rfl) ⟨44862477, by rfl⟩ : syracuseStep 119633273 = 89724955) B89724955
theorem B79755515 : Blo 2073435 79755515 := bstep (se 1 (by rfl) ⟨59816636, by rfl⟩ : syracuseStep 79755515 = 119633273) B119633273
theorem B53170343 : Blo 2073435 53170343 := bstep (se 1 (by rfl) ⟨39877757, by rfl⟩ : syracuseStep 53170343 = 79755515) B79755515
theorem B35446895 : Blo 2073435 35446895 := bstep (se 1 (by rfl) ⟨26585171, by rfl⟩ : syracuseStep 35446895 = 53170343) B53170343
theorem B23631263 : Blo 2073435 23631263 := bstep (se 1 (by rfl) ⟨17723447, by rfl⟩ : syracuseStep 23631263 = 35446895) B35446895
theorem B15754175 : Blo 2073435 15754175 := bstep (se 1 (by rfl) ⟨11815631, by rfl⟩ : syracuseStep 15754175 = 23631263) B23631263
theorem B10502783 : Blo 2073435 10502783 := bstep (se 1 (by rfl) ⟨7877087, by rfl⟩ : syracuseStep 10502783 = 15754175) B15754175
theorem B7001855 : Blo 2073435 7001855 := bstep (se 1 (by rfl) ⟨5251391, by rfl⟩ : syracuseStep 7001855 = 10502783) B10502783
theorem B4667903 : Blo 2073435 4667903 := bstep (se 1 (by rfl) ⟨3500927, by rfl⟩ : syracuseStep 4667903 = 7001855) B7001855
theorem B3111935 : Blo 2073435 3111935 := bstep (se 1 (by rfl) ⟨2333951, by rfl⟩ : syracuseStep 3111935 = 4667903) B4667903
theorem B2074623 : Blo 2073435 2074623 := bstep (se 1 (by rfl) ⟨1555967, by rfl⟩ : syracuseStep 2074623 = 3111935) B3111935
theorem B3111941 : Blo 2073435 3111941 := bbase (se 4 (by rfl) ⟨291744, by rfl⟩ : syracuseStep 3111941 = 583489) (by norm_num)
theorem B2074627 : Blo 2073435 2074627 := bstep (se 1 (by rfl) ⟨1555970, by rfl⟩ : syracuseStep 2074627 = 3111941) B3111941
theorem B3500941 : Blo 2073435 3500941 := bbase (se 3 (by rfl) ⟨656426, by rfl⟩ : syracuseStep 3500941 = 1312853) (by norm_num)
theorem B4667921 : Blo 2073435 4667921 := bstep (se 2 (by rfl) ⟨1750470, by rfl⟩ : syracuseStep 4667921 = 3500941) B3500941
theorem B3111947 : Blo 2073435 3111947 := bstep (se 1 (by rfl) ⟨2333960, by rfl⟩ : syracuseStep 3111947 = 4667921) B4667921
theorem B2074631 : Blo 2073435 2074631 := bstep (se 1 (by rfl) ⟨1555973, by rfl⟩ : syracuseStep 2074631 = 3111947) B3111947
theorem B2333965 : Blo 2073435 2333965 := bbase (se 3 (by rfl) ⟨437618, by rfl⟩ : syracuseStep 2333965 = 875237) (by norm_num)
theorem B3111953 : Blo 2073435 3111953 := bstep (se 2 (by rfl) ⟨1166982, by rfl⟩ : syracuseStep 3111953 = 2333965) B2333965
theorem B2074635 : Blo 2073435 2074635 := bstep (se 1 (by rfl) ⟨1555976, by rfl⟩ : syracuseStep 2074635 = 3111953) B3111953
theorem B7001909 : Blo 2073435 7001909 := bbase (se 5 (by rfl) ⟨328214, by rfl⟩ : syracuseStep 7001909 = 656429) (by norm_num)
theorem B4667939 : Blo 2073435 4667939 := bstep (se 1 (by rfl) ⟨3500954, by rfl⟩ : syracuseStep 4667939 = 7001909) B7001909
theorem B3111959 : Blo 2073435 3111959 := bstep (se 1 (by rfl) ⟨2333969, by rfl⟩ : syracuseStep 3111959 = 4667939) B4667939
theorem B2074639 : Blo 2073435 2074639 := bstep (se 1 (by rfl) ⟨1555979, by rfl⟩ : syracuseStep 2074639 = 3111959) B3111959
theorem B3111965 : Blo 2073435 3111965 := bbase (se 3 (by rfl) ⟨583493, by rfl⟩ : syracuseStep 3111965 = 1166987) (by norm_num)
theorem B2074643 : Blo 2073435 2074643 := bstep (se 1 (by rfl) ⟨1555982, by rfl⟩ : syracuseStep 2074643 = 3111965) B3111965
theorem B4667957 : Blo 2073435 4667957 := bbase (se 5 (by rfl) ⟨218810, by rfl⟩ : syracuseStep 4667957 = 437621) (by norm_num)
theorem B3111971 : Blo 2073435 3111971 := bstep (se 1 (by rfl) ⟨2333978, by rfl⟩ : syracuseStep 3111971 = 4667957) B4667957
theorem B2074647 : Blo 2073435 2074647 := bstep (se 1 (by rfl) ⟨1555985, by rfl⟩ : syracuseStep 2074647 = 3111971) B3111971
theorem B8861845 : Blo 2073435 8861845 := bbase (se 6 (by rfl) ⟨207699, by rfl⟩ : syracuseStep 8861845 = 415399) (by norm_num)
theorem B11815793 : Blo 2073435 11815793 := bstep (se 2 (by rfl) ⟨4430922, by rfl⟩ : syracuseStep 11815793 = 8861845) B8861845
theorem B7877195 : Blo 2073435 7877195 := bstep (se 1 (by rfl) ⟨5907896, by rfl⟩ : syracuseStep 7877195 = 11815793) B11815793
theorem B5251463 : Blo 2073435 5251463 := bstep (se 1 (by rfl) ⟨3938597, by rfl⟩ : syracuseStep 5251463 = 7877195) B7877195
theorem B3500975 : Blo 2073435 3500975 := bstep (se 1 (by rfl) ⟨2625731, by rfl⟩ : syracuseStep 3500975 = 5251463) B5251463
theorem B2333983 : Blo 2073435 2333983 := bstep (se 1 (by rfl) ⟨1750487, by rfl⟩ : syracuseStep 2333983 = 3500975) B3500975
theorem B3111977 : Blo 2073435 3111977 := bstep (se 2 (by rfl) ⟨1166991, by rfl⟩ : syracuseStep 3111977 = 2333983) B2333983
theorem B2074651 : Blo 2073435 2074651 := bstep (se 1 (by rfl) ⟨1555988, by rfl⟩ : syracuseStep 2074651 = 3111977) B3111977
theorem B8861861 : Blo 2073435 8861861 := bbase (se 4 (by rfl) ⟨830799, by rfl⟩ : syracuseStep 8861861 = 1661599) (by norm_num)
theorem B5907907 : Blo 2073435 5907907 := bstep (se 1 (by rfl) ⟨4430930, by rfl⟩ : syracuseStep 5907907 = 8861861) B8861861
theorem B7877209 : Blo 2073435 7877209 := bstep (se 2 (by rfl) ⟨2953953, by rfl⟩ : syracuseStep 7877209 = 5907907) B5907907
theorem B10502945 : Blo 2073435 10502945 := bstep (se 2 (by rfl) ⟨3938604, by rfl⟩ : syracuseStep 10502945 = 7877209) B7877209
theorem B7001963 : Blo 2073435 7001963 := bstep (se 1 (by rfl) ⟨5251472, by rfl⟩ : syracuseStep 7001963 = 10502945) B10502945
theorem B4667975 : Blo 2073435 4667975 := bstep (se 1 (by rfl) ⟨3500981, by rfl⟩ : syracuseStep 4667975 = 7001963) B7001963
theorem B3111983 : Blo 2073435 3111983 := bstep (se 1 (by rfl) ⟨2333987, by rfl⟩ : syracuseStep 3111983 = 4667975) B4667975
theorem B2074655 : Blo 2073435 2074655 := bstep (se 1 (by rfl) ⟨1555991, by rfl⟩ : syracuseStep 2074655 = 3111983) B3111983
theorem B3111989 : Blo 2073435 3111989 := bbase (se 5 (by rfl) ⟨145874, by rfl⟩ : syracuseStep 3111989 = 291749) (by norm_num)
theorem B2074659 : Blo 2073435 2074659 := bstep (se 1 (by rfl) ⟨1555994, by rfl⟩ : syracuseStep 2074659 = 3111989) B3111989
theorem B5251493 : Blo 2073435 5251493 := bbase (se 4 (by rfl) ⟨492327, by rfl⟩ : syracuseStep 5251493 = 984655) (by norm_num)
theorem B3500995 : Blo 2073435 3500995 := bstep (se 1 (by rfl) ⟨2625746, by rfl⟩ : syracuseStep 3500995 = 5251493) B5251493
theorem B4667993 : Blo 2073435 4667993 := bstep (se 2 (by rfl) ⟨1750497, by rfl⟩ : syracuseStep 4667993 = 3500995) B3500995
theorem B3111995 : Blo 2073435 3111995 := bstep (se 1 (by rfl) ⟨2333996, by rfl⟩ : syracuseStep 3111995 = 4667993) B4667993
theorem B2074663 : Blo 2073435 2074663 := bstep (se 1 (by rfl) ⟨1555997, by rfl⟩ : syracuseStep 2074663 = 3111995) B3111995
theorem B2334001 : Blo 2073435 2334001 := bbase (se 2 (by rfl) ⟨875250, by rfl⟩ : syracuseStep 2334001 = 1750501) (by norm_num)
theorem B3112001 : Blo 2073435 3112001 := bstep (se 2 (by rfl) ⟨1167000, by rfl⟩ : syracuseStep 3112001 = 2334001) B2334001
theorem B2074667 : Blo 2073435 2074667 := bstep (se 1 (by rfl) ⟨1556000, by rfl⟩ : syracuseStep 2074667 = 3112001) B3112001
theorem B4430965 : Blo 2073435 4430965 := bbase (se 5 (by rfl) ⟨207701, by rfl⟩ : syracuseStep 4430965 = 415403) (by norm_num)
theorem B5907953 : Blo 2073435 5907953 := bstep (se 2 (by rfl) ⟨2215482, by rfl⟩ : syracuseStep 5907953 = 4430965) B4430965
theorem B3938635 : Blo 2073435 3938635 := bstep (se 1 (by rfl) ⟨2953976, by rfl⟩ : syracuseStep 3938635 = 5907953) B5907953
theorem B5251513 : Blo 2073435 5251513 := bstep (se 2 (by rfl) ⟨1969317, by rfl⟩ : syracuseStep 5251513 = 3938635) B3938635
theorem B7002017 : Blo 2073435 7002017 := bstep (se 2 (by rfl) ⟨2625756, by rfl⟩ : syracuseStep 7002017 = 5251513) B5251513
theorem B4668011 : Blo 2073435 4668011 := bstep (se 1 (by rfl) ⟨3501008, by rfl⟩ : syracuseStep 4668011 = 7002017) B7002017
theorem B3112007 : Blo 2073435 3112007 := bstep (se 1 (by rfl) ⟨2334005, by rfl⟩ : syracuseStep 3112007 = 4668011) B4668011
theorem B2074671 : Blo 2073435 2074671 := bstep (se 1 (by rfl) ⟨1556003, by rfl⟩ : syracuseStep 2074671 = 3112007) B3112007
theorem B3112013 : Blo 2073435 3112013 := bbase (se 3 (by rfl) ⟨583502, by rfl⟩ : syracuseStep 3112013 = 1167005) (by norm_num)
theorem B2074675 : Blo 2073435 2074675 := bstep (se 1 (by rfl) ⟨1556006, by rfl⟩ : syracuseStep 2074675 = 3112013) B3112013
theorem B4668029 : Blo 2073435 4668029 := bbase (se 3 (by rfl) ⟨875255, by rfl⟩ : syracuseStep 4668029 = 1750511) (by norm_num)
theorem B3112019 : Blo 2073435 3112019 := bstep (se 1 (by rfl) ⟨2334014, by rfl⟩ : syracuseStep 3112019 = 4668029) B4668029
theorem B2074679 : Blo 2073435 2074679 := bstep (se 1 (by rfl) ⟨1556009, by rfl⟩ : syracuseStep 2074679 = 3112019) B3112019
theorem B3501029 : Blo 2073435 3501029 := bbase (se 4 (by rfl) ⟨328221, by rfl⟩ : syracuseStep 3501029 = 656443) (by norm_num)
theorem B2334019 : Blo 2073435 2334019 := bstep (se 1 (by rfl) ⟨1750514, by rfl⟩ : syracuseStep 2334019 = 3501029) B3501029
theorem B3112025 : Blo 2073435 3112025 := bstep (se 2 (by rfl) ⟨1167009, by rfl⟩ : syracuseStep 3112025 = 2334019) B2334019
theorem B2074683 : Blo 2073435 2074683 := bstep (se 1 (by rfl) ⟨1556012, by rfl⟩ : syracuseStep 2074683 = 3112025) B3112025
theorem B9969749 : Blo 2073435 9969749 := bbase (se 8 (by rfl) ⟨58416, by rfl⟩ : syracuseStep 9969749 = 116833) (by norm_num)
theorem B6646499 : Blo 2073435 6646499 := bstep (se 1 (by rfl) ⟨4984874, by rfl⟩ : syracuseStep 6646499 = 9969749) B9969749
theorem B4430999 : Blo 2073435 4430999 := bstep (se 1 (by rfl) ⟨3323249, by rfl⟩ : syracuseStep 4430999 = 6646499) B6646499
theorem B2953999 : Blo 2073435 2953999 := bstep (se 1 (by rfl) ⟨2215499, by rfl⟩ : syracuseStep 2953999 = 4430999) B4430999
theorem B15754661 : Blo 2073435 15754661 := bstep (se 4 (by rfl) ⟨1476999, by rfl⟩ : syracuseStep 15754661 = 2953999) B2953999
theorem B10503107 : Blo 2073435 10503107 := bstep (se 1 (by rfl) ⟨7877330, by rfl⟩ : syracuseStep 10503107 = 15754661) B15754661
theorem B7002071 : Blo 2073435 7002071 := bstep (se 1 (by rfl) ⟨5251553, by rfl⟩ : syracuseStep 7002071 = 10503107) B10503107
theorem B4668047 : Blo 2073435 4668047 := bstep (se 1 (by rfl) ⟨3501035, by rfl⟩ : syracuseStep 4668047 = 7002071) B7002071
theorem B3112031 : Blo 2073435 3112031 := bstep (se 1 (by rfl) ⟨2334023, by rfl⟩ : syracuseStep 3112031 = 4668047) B4668047
theorem B2074687 : Blo 2073435 2074687 := bstep (se 1 (by rfl) ⟨1556015, by rfl⟩ : syracuseStep 2074687 = 3112031) B3112031
theorem B3112037 : Blo 2073435 3112037 := bbase (se 4 (by rfl) ⟨291753, by rfl⟩ : syracuseStep 3112037 = 583507) (by norm_num)
theorem B2074691 : Blo 2073435 2074691 := bstep (se 1 (by rfl) ⟨1556018, by rfl⟩ : syracuseStep 2074691 = 3112037) B3112037
theorem B10646453 : Blo 2073435 10646453 := bbase (se 5 (by rfl) ⟨499052, by rfl⟩ : syracuseStep 10646453 = 998105) (by norm_num)
theorem B7097635 : Blo 2073435 7097635 := bstep (se 1 (by rfl) ⟨5323226, by rfl⟩ : syracuseStep 7097635 = 10646453) B10646453
theorem B37854053 : Blo 2073435 37854053 := bstep (se 4 (by rfl) ⟨3548817, by rfl⟩ : syracuseStep 37854053 = 7097635) B7097635
theorem B25236035 : Blo 2073435 25236035 := bstep (se 1 (by rfl) ⟨18927026, by rfl⟩ : syracuseStep 25236035 = 37854053) B37854053
theorem B16824023 : Blo 2073435 16824023 := bstep (se 1 (by rfl) ⟨12618017, by rfl⟩ : syracuseStep 16824023 = 25236035) B25236035
theorem B11216015 : Blo 2073435 11216015 := bstep (se 1 (by rfl) ⟨8412011, by rfl⟩ : syracuseStep 11216015 = 16824023) B16824023
theorem B7477343 : Blo 2073435 7477343 := bstep (se 1 (by rfl) ⟨5608007, by rfl⟩ : syracuseStep 7477343 = 11216015) B11216015
theorem B4984895 : Blo 2073435 4984895 := bstep (se 1 (by rfl) ⟨3738671, by rfl⟩ : syracuseStep 4984895 = 7477343) B7477343
theorem B3323263 : Blo 2073435 3323263 := bstep (se 1 (by rfl) ⟨2492447, by rfl⟩ : syracuseStep 3323263 = 4984895) B4984895
theorem B4431017 : Blo 2073435 4431017 := bstep (se 2 (by rfl) ⟨1661631, by rfl⟩ : syracuseStep 4431017 = 3323263) B3323263
theorem B2954011 : Blo 2073435 2954011 := bstep (se 1 (by rfl) ⟨2215508, by rfl⟩ : syracuseStep 2954011 = 4431017) B4431017
theorem B3938681 : Blo 2073435 3938681 := bstep (se 2 (by rfl) ⟨1477005, by rfl⟩ : syracuseStep 3938681 = 2954011) B2954011
theorem B2625787 : Blo 2073435 2625787 := bstep (se 1 (by rfl) ⟨1969340, by rfl⟩ : syracuseStep 2625787 = 3938681) B3938681
theorem B3501049 : Blo 2073435 3501049 := bstep (se 2 (by rfl) ⟨1312893, by rfl⟩ : syracuseStep 3501049 = 2625787) B2625787
theorem B4668065 : Blo 2073435 4668065 := bstep (se 2 (by rfl) ⟨1750524, by rfl⟩ : syracuseStep 4668065 = 3501049) B3501049
theorem B3112043 : Blo 2073435 3112043 := bstep (se 1 (by rfl) ⟨2334032, by rfl⟩ : syracuseStep 3112043 = 4668065) B4668065
theorem B2074695 : Blo 2073435 2074695 := bstep (se 1 (by rfl) ⟨1556021, by rfl⟩ : syracuseStep 2074695 = 3112043) B3112043
theorem B2334037 : Blo 2073435 2334037 := bbase (se 11 (by rfl) ⟨1709, by rfl⟩ : syracuseStep 2334037 = 3419) (by norm_num)
theorem B3112049 : Blo 2073435 3112049 := bstep (se 2 (by rfl) ⟨1167018, by rfl⟩ : syracuseStep 3112049 = 2334037) B2334037
theorem B2074699 : Blo 2073435 2074699 := bstep (se 1 (by rfl) ⟨1556024, by rfl⟩ : syracuseStep 2074699 = 3112049) B3112049
theorem B2625797 : Blo 2073435 2625797 := bbase (se 4 (by rfl) ⟨246168, by rfl⟩ : syracuseStep 2625797 = 492337) (by norm_num)
theorem B7002125 : Blo 2073435 7002125 := bstep (se 3 (by rfl) ⟨1312898, by rfl⟩ : syracuseStep 7002125 = 2625797) B2625797
theorem B4668083 : Blo 2073435 4668083 := bstep (se 1 (by rfl) ⟨3501062, by rfl⟩ : syracuseStep 4668083 = 7002125) B7002125
theorem B3112055 : Blo 2073435 3112055 := bstep (se 1 (by rfl) ⟨2334041, by rfl⟩ : syracuseStep 3112055 = 4668083) B4668083
theorem B2074703 : Blo 2073435 2074703 := bstep (se 1 (by rfl) ⟨1556027, by rfl⟩ : syracuseStep 2074703 = 3112055) B3112055
theorem B3112061 : Blo 2073435 3112061 := bbase (se 3 (by rfl) ⟨583511, by rfl⟩ : syracuseStep 3112061 = 1167023) (by norm_num)
theorem B2074707 : Blo 2073435 2074707 := bstep (se 1 (by rfl) ⟨1556030, by rfl⟩ : syracuseStep 2074707 = 3112061) B3112061
theorem B4668101 : Blo 2073435 4668101 := bbase (se 4 (by rfl) ⟨437634, by rfl⟩ : syracuseStep 4668101 = 875269) (by norm_num)
theorem B3112067 : Blo 2073435 3112067 := bstep (se 1 (by rfl) ⟨2334050, by rfl⟩ : syracuseStep 3112067 = 4668101) B4668101
theorem B2074711 : Blo 2073435 2074711 := bstep (se 1 (by rfl) ⟨1556033, by rfl⟩ : syracuseStep 2074711 = 3112067) B3112067
theorem B16824181 : Blo 2073435 16824181 := bbase (se 5 (by rfl) ⟨788633, by rfl⟩ : syracuseStep 16824181 = 1577267) (by norm_num)
theorem B22432241 : Blo 2073435 22432241 := bstep (se 2 (by rfl) ⟨8412090, by rfl⟩ : syracuseStep 22432241 = 16824181) B16824181
theorem B14954827 : Blo 2073435 14954827 := bstep (se 1 (by rfl) ⟨11216120, by rfl⟩ : syracuseStep 14954827 = 22432241) B22432241
theorem B19939769 : Blo 2073435 19939769 := bstep (se 2 (by rfl) ⟨7477413, by rfl⟩ : syracuseStep 19939769 = 14954827) B14954827
theorem B13293179 : Blo 2073435 13293179 := bstep (se 1 (by rfl) ⟨9969884, by rfl⟩ : syracuseStep 13293179 = 19939769) B19939769
theorem B8862119 : Blo 2073435 8862119 := bstep (se 1 (by rfl) ⟨6646589, by rfl⟩ : syracuseStep 8862119 = 13293179) B13293179
theorem B5908079 : Blo 2073435 5908079 := bstep (se 1 (by rfl) ⟨4431059, by rfl⟩ : syracuseStep 5908079 = 8862119) B8862119
theorem B3938719 : Blo 2073435 3938719 := bstep (se 1 (by rfl) ⟨2954039, by rfl⟩ : syracuseStep 3938719 = 5908079) B5908079
theorem B5251625 : Blo 2073435 5251625 := bstep (se 2 (by rfl) ⟨1969359, by rfl⟩ : syracuseStep 5251625 = 3938719) B3938719
theorem B3501083 : Blo 2073435 3501083 := bstep (se 1 (by rfl) ⟨2625812, by rfl⟩ : syracuseStep 3501083 = 5251625) B5251625
theorem B2334055 : Blo 2073435 2334055 := bstep (se 1 (by rfl) ⟨1750541, by rfl⟩ : syracuseStep 2334055 = 3501083) B3501083
theorem B3112073 : Blo 2073435 3112073 := bstep (se 2 (by rfl) ⟨1167027, by rfl⟩ : syracuseStep 3112073 = 2334055) B2334055
theorem B2074715 : Blo 2073435 2074715 := bstep (se 1 (by rfl) ⟨1556036, by rfl⟩ : syracuseStep 2074715 = 3112073) B3112073
theorem B10503269 : Blo 2073435 10503269 := bbase (se 4 (by rfl) ⟨984681, by rfl⟩ : syracuseStep 10503269 = 1969363) (by norm_num)
theorem B7002179 : Blo 2073435 7002179 := bstep (se 1 (by rfl) ⟨5251634, by rfl⟩ : syracuseStep 7002179 = 10503269) B10503269
theorem B4668119 : Blo 2073435 4668119 := bstep (se 1 (by rfl) ⟨3501089, by rfl⟩ : syracuseStep 4668119 = 7002179) B7002179
theorem B3112079 : Blo 2073435 3112079 := bstep (se 1 (by rfl) ⟨2334059, by rfl⟩ : syracuseStep 3112079 = 4668119) B4668119
theorem B2074719 : Blo 2073435 2074719 := bstep (se 1 (by rfl) ⟨1556039, by rfl⟩ : syracuseStep 2074719 = 3112079) B3112079
theorem B3112085 : Blo 2073435 3112085 := bbase (se 6 (by rfl) ⟨72939, by rfl⟩ : syracuseStep 3112085 = 145879) (by norm_num)
theorem B2074723 : Blo 2073435 2074723 := bstep (se 1 (by rfl) ⟨1556042, by rfl⟩ : syracuseStep 2074723 = 3112085) B3112085
theorem B9969941 : Blo 2073435 9969941 := bbase (se 6 (by rfl) ⟨233670, by rfl⟩ : syracuseStep 9969941 = 467341) (by norm_num)
theorem B6646627 : Blo 2073435 6646627 := bstep (se 1 (by rfl) ⟨4984970, by rfl⟩ : syracuseStep 6646627 = 9969941) B9969941
theorem B8862169 : Blo 2073435 8862169 := bstep (se 2 (by rfl) ⟨3323313, by rfl⟩ : syracuseStep 8862169 = 6646627) B6646627
theorem B11816225 : Blo 2073435 11816225 := bstep (se 2 (by rfl) ⟨4431084, by rfl⟩ : syracuseStep 11816225 = 8862169) B8862169
theorem B7877483 : Blo 2073435 7877483 := bstep (se 1 (by rfl) ⟨5908112, by rfl⟩ : syracuseStep 7877483 = 11816225) B11816225
theorem B5251655 : Blo 2073435 5251655 := bstep (se 1 (by rfl) ⟨3938741, by rfl⟩ : syracuseStep 5251655 = 7877483) B7877483
theorem B3501103 : Blo 2073435 3501103 := bstep (se 1 (by rfl) ⟨2625827, by rfl⟩ : syracuseStep 3501103 = 5251655) B5251655
theorem B4668137 : Blo 2073435 4668137 := bstep (se 2 (by rfl) ⟨1750551, by rfl⟩ : syracuseStep 4668137 = 3501103) B3501103
theorem B3112091 : Blo 2073435 3112091 := bstep (se 1 (by rfl) ⟨2334068, by rfl⟩ : syracuseStep 3112091 = 4668137) B4668137
theorem B2074727 : Blo 2073435 2074727 := bstep (se 1 (by rfl) ⟨1556045, by rfl⟩ : syracuseStep 2074727 = 3112091) B3112091
theorem B2334073 : Blo 2073435 2334073 := bbase (se 2 (by rfl) ⟨875277, by rfl⟩ : syracuseStep 2334073 = 1750555) (by norm_num)
theorem B3112097 : Blo 2073435 3112097 := bstep (se 2 (by rfl) ⟨1167036, by rfl⟩ : syracuseStep 3112097 = 2334073) B2334073
theorem B2074731 : Blo 2073435 2074731 := bstep (se 1 (by rfl) ⟨1556048, by rfl⟩ : syracuseStep 2074731 = 3112097) B3112097
theorem B16824341 : Blo 2073435 16824341 := bbase (se 6 (by rfl) ⟨394320, by rfl⟩ : syracuseStep 16824341 = 788641) (by norm_num)
theorem B11216227 : Blo 2073435 11216227 := bstep (se 1 (by rfl) ⟨8412170, by rfl⟩ : syracuseStep 11216227 = 16824341) B16824341
theorem B14954969 : Blo 2073435 14954969 := bstep (se 2 (by rfl) ⟨5608113, by rfl⟩ : syracuseStep 14954969 = 11216227) B11216227
theorem B9969979 : Blo 2073435 9969979 := bstep (se 1 (by rfl) ⟨7477484, by rfl⟩ : syracuseStep 9969979 = 14954969) B14954969
theorem B13293305 : Blo 2073435 13293305 := bstep (se 2 (by rfl) ⟨4984989, by rfl⟩ : syracuseStep 13293305 = 9969979) B9969979
theorem B8862203 : Blo 2073435 8862203 := bstep (se 1 (by rfl) ⟨6646652, by rfl⟩ : syracuseStep 8862203 = 13293305) B13293305
theorem B5908135 : Blo 2073435 5908135 := bstep (se 1 (by rfl) ⟨4431101, by rfl⟩ : syracuseStep 5908135 = 8862203) B8862203
theorem B7877513 : Blo 2073435 7877513 := bstep (se 2 (by rfl) ⟨2954067, by rfl⟩ : syracuseStep 7877513 = 5908135) B5908135
theorem B5251675 : Blo 2073435 5251675 := bstep (se 1 (by rfl) ⟨3938756, by rfl⟩ : syracuseStep 5251675 = 7877513) B7877513
theorem B7002233 : Blo 2073435 7002233 := bstep (se 2 (by rfl) ⟨2625837, by rfl⟩ : syracuseStep 7002233 = 5251675) B5251675
theorem B4668155 : Blo 2073435 4668155 := bstep (se 1 (by rfl) ⟨3501116, by rfl⟩ : syracuseStep 4668155 = 7002233) B7002233
theorem B3112103 : Blo 2073435 3112103 := bstep (se 1 (by rfl) ⟨2334077, by rfl⟩ : syracuseStep 3112103 = 4668155) B4668155
theorem B2074735 : Blo 2073435 2074735 := bstep (se 1 (by rfl) ⟨1556051, by rfl⟩ : syracuseStep 2074735 = 3112103) B3112103
theorem B3112109 : Blo 2073435 3112109 := bbase (se 3 (by rfl) ⟨583520, by rfl⟩ : syracuseStep 3112109 = 1167041) (by norm_num)
theorem B2074739 : Blo 2073435 2074739 := bstep (se 1 (by rfl) ⟨1556054, by rfl⟩ : syracuseStep 2074739 = 3112109) B3112109
theorem B4668173 : Blo 2073435 4668173 := bbase (se 3 (by rfl) ⟨875282, by rfl⟩ : syracuseStep 4668173 = 1750565) (by norm_num)
theorem B3112115 : Blo 2073435 3112115 := bstep (se 1 (by rfl) ⟨2334086, by rfl⟩ : syracuseStep 3112115 = 4668173) B4668173
theorem B2074743 : Blo 2073435 2074743 := bstep (se 1 (by rfl) ⟨1556057, by rfl⟩ : syracuseStep 2074743 = 3112115) B3112115
theorem B2625853 : Blo 2073435 2625853 := bbase (se 3 (by rfl) ⟨492347, by rfl⟩ : syracuseStep 2625853 = 984695) (by norm_num)
theorem B3501137 : Blo 2073435 3501137 := bstep (se 2 (by rfl) ⟨1312926, by rfl⟩ : syracuseStep 3501137 = 2625853) B2625853
theorem B2334091 : Blo 2073435 2334091 := bstep (se 1 (by rfl) ⟨1750568, by rfl⟩ : syracuseStep 2334091 = 3501137) B3501137
theorem B3112121 : Blo 2073435 3112121 := bstep (se 2 (by rfl) ⟨1167045, by rfl⟩ : syracuseStep 3112121 = 2334091) B2334091
theorem B2074747 : Blo 2073435 2074747 := bstep (se 1 (by rfl) ⟨1556060, by rfl⟩ : syracuseStep 2074747 = 3112121) B3112121
theorem B16824469 : Blo 2073435 16824469 := bbase (se 6 (by rfl) ⟨394323, by rfl⟩ : syracuseStep 16824469 = 788647) (by norm_num)
theorem B22432625 : Blo 2073435 22432625 := bstep (se 2 (by rfl) ⟨8412234, by rfl⟩ : syracuseStep 22432625 = 16824469) B16824469
theorem B14955083 : Blo 2073435 14955083 := bstep (se 1 (by rfl) ⟨11216312, by rfl⟩ : syracuseStep 14955083 = 22432625) B22432625
theorem B9970055 : Blo 2073435 9970055 := bstep (se 1 (by rfl) ⟨7477541, by rfl⟩ : syracuseStep 9970055 = 14955083) B14955083
theorem B6646703 : Blo 2073435 6646703 := bstep (se 1 (by rfl) ⟨4985027, by rfl⟩ : syracuseStep 6646703 = 9970055) B9970055
theorem B17724541 : Blo 2073435 17724541 := bstep (se 3 (by rfl) ⟨3323351, by rfl⟩ : syracuseStep 17724541 = 6646703) B6646703
theorem B23632721 : Blo 2073435 23632721 := bstep (se 2 (by rfl) ⟨8862270, by rfl⟩ : syracuseStep 23632721 = 17724541) B17724541
theorem B15755147 : Blo 2073435 15755147 := bstep (se 1 (by rfl) ⟨11816360, by rfl⟩ : syracuseStep 15755147 = 23632721) B23632721
theorem B10503431 : Blo 2073435 10503431 := bstep (se 1 (by rfl) ⟨7877573, by rfl⟩ : syracuseStep 10503431 = 15755147) B15755147
theorem B7002287 : Blo 2073435 7002287 := bstep (se 1 (by rfl) ⟨5251715, by rfl⟩ : syracuseStep 7002287 = 10503431) B10503431
theorem B4668191 : Blo 2073435 4668191 := bstep (se 1 (by rfl) ⟨3501143, by rfl⟩ : syracuseStep 4668191 = 7002287) B7002287
theorem B3112127 : Blo 2073435 3112127 := bstep (se 1 (by rfl) ⟨2334095, by rfl⟩ : syracuseStep 3112127 = 4668191) B4668191
theorem B2074751 : Blo 2073435 2074751 := bstep (se 1 (by rfl) ⟨1556063, by rfl⟩ : syracuseStep 2074751 = 3112127) B3112127
theorem B3112133 : Blo 2073435 3112133 := bbase (se 4 (by rfl) ⟨291762, by rfl⟩ : syracuseStep 3112133 = 583525) (by norm_num)
theorem B2074755 : Blo 2073435 2074755 := bstep (se 1 (by rfl) ⟨1556066, by rfl⟩ : syracuseStep 2074755 = 3112133) B3112133
theorem B3501157 : Blo 2073435 3501157 := bbase (se 4 (by rfl) ⟨328233, by rfl⟩ : syracuseStep 3501157 = 656467) (by norm_num)
theorem B4668209 : Blo 2073435 4668209 := bstep (se 2 (by rfl) ⟨1750578, by rfl⟩ : syracuseStep 4668209 = 3501157) B3501157
theorem B3112139 : Blo 2073435 3112139 := bstep (se 1 (by rfl) ⟨2334104, by rfl⟩ : syracuseStep 3112139 = 4668209) B4668209
theorem B2074759 : Blo 2073435 2074759 := bstep (se 1 (by rfl) ⟨1556069, by rfl⟩ : syracuseStep 2074759 = 3112139) B3112139
theorem B2334109 : Blo 2073435 2334109 := bbase (se 3 (by rfl) ⟨437645, by rfl⟩ : syracuseStep 2334109 = 875291) (by norm_num)
theorem B3112145 : Blo 2073435 3112145 := bstep (se 2 (by rfl) ⟨1167054, by rfl⟩ : syracuseStep 3112145 = 2334109) B2334109
theorem B2074763 : Blo 2073435 2074763 := bstep (se 1 (by rfl) ⟨1556072, by rfl⟩ : syracuseStep 2074763 = 3112145) B3112145
theorem B7002341 : Blo 2073435 7002341 := bbase (se 4 (by rfl) ⟨656469, by rfl⟩ : syracuseStep 7002341 = 1312939) (by norm_num)
theorem B4668227 : Blo 2073435 4668227 := bstep (se 1 (by rfl) ⟨3501170, by rfl⟩ : syracuseStep 4668227 = 7002341) B7002341
theorem B3112151 : Blo 2073435 3112151 := bstep (se 1 (by rfl) ⟨2334113, by rfl⟩ : syracuseStep 3112151 = 4668227) B4668227
theorem B2074767 : Blo 2073435 2074767 := bstep (se 1 (by rfl) ⟨1556075, by rfl⟩ : syracuseStep 2074767 = 3112151) B3112151
theorem B3112157 : Blo 2073435 3112157 := bbase (se 3 (by rfl) ⟨583529, by rfl⟩ : syracuseStep 3112157 = 1167059) (by norm_num)
theorem B2074771 : Blo 2073435 2074771 := bstep (se 1 (by rfl) ⟨1556078, by rfl⟩ : syracuseStep 2074771 = 3112157) B3112157
theorem B4668245 : Blo 2073435 4668245 := bbase (se 9 (by rfl) ⟨13676, by rfl⟩ : syracuseStep 4668245 = 27353) (by norm_num)
theorem B3112163 : Blo 2073435 3112163 := bstep (se 1 (by rfl) ⟨2334122, by rfl⟩ : syracuseStep 3112163 = 4668245) B4668245
theorem B2074775 : Blo 2073435 2074775 := bstep (se 1 (by rfl) ⟨1556081, by rfl⟩ : syracuseStep 2074775 = 3112163) B3112163
theorem B5908261 : Blo 2073435 5908261 := bbase (se 4 (by rfl) ⟨553899, by rfl⟩ : syracuseStep 5908261 = 1107799) (by norm_num)
theorem B7877681 : Blo 2073435 7877681 := bstep (se 2 (by rfl) ⟨2954130, by rfl⟩ : syracuseStep 7877681 = 5908261) B5908261
theorem B5251787 : Blo 2073435 5251787 := bstep (se 1 (by rfl) ⟨3938840, by rfl⟩ : syracuseStep 5251787 = 7877681) B7877681
theorem B3501191 : Blo 2073435 3501191 := bstep (se 1 (by rfl) ⟨2625893, by rfl⟩ : syracuseStep 3501191 = 5251787) B5251787
theorem B2334127 : Blo 2073435 2334127 := bstep (se 1 (by rfl) ⟨1750595, by rfl⟩ : syracuseStep 2334127 = 3501191) B3501191
theorem B3112169 : Blo 2073435 3112169 := bstep (se 2 (by rfl) ⟨1167063, by rfl⟩ : syracuseStep 3112169 = 2334127) B2334127
theorem B2074779 : Blo 2073435 2074779 := bstep (se 1 (by rfl) ⟨1556084, by rfl⟩ : syracuseStep 2074779 = 3112169) B3112169
theorem B3154637 : Blo 2073435 3154637 := bbase (se 3 (by rfl) ⟨591494, by rfl⟩ : syracuseStep 3154637 = 1182989) (by norm_num)
theorem B2103091 : Blo 2073435 2103091 := bstep (se 1 (by rfl) ⟨1577318, by rfl⟩ : syracuseStep 2103091 = 3154637) B3154637
theorem B11216485 : Blo 2073435 11216485 := bstep (se 4 (by rfl) ⟨1051545, by rfl⟩ : syracuseStep 11216485 = 2103091) B2103091
theorem B59821253 : Blo 2073435 59821253 := bstep (se 4 (by rfl) ⟨5608242, by rfl⟩ : syracuseStep 59821253 = 11216485) B11216485
theorem B39880835 : Blo 2073435 39880835 := bstep (se 1 (by rfl) ⟨29910626, by rfl⟩ : syracuseStep 39880835 = 59821253) B59821253
theorem B26587223 : Blo 2073435 26587223 := bstep (se 1 (by rfl) ⟨19940417, by rfl⟩ : syracuseStep 26587223 = 39880835) B39880835
theorem B17724815 : Blo 2073435 17724815 := bstep (se 1 (by rfl) ⟨13293611, by rfl⟩ : syracuseStep 17724815 = 26587223) B26587223
theorem B11816543 : Blo 2073435 11816543 := bstep (se 1 (by rfl) ⟨8862407, by rfl⟩ : syracuseStep 11816543 = 17724815) B17724815
theorem B7877695 : Blo 2073435 7877695 := bstep (se 1 (by rfl) ⟨5908271, by rfl⟩ : syracuseStep 7877695 = 11816543) B11816543
theorem B10503593 : Blo 2073435 10503593 := bstep (se 2 (by rfl) ⟨3938847, by rfl⟩ : syracuseStep 10503593 = 7877695) B7877695
theorem B7002395 : Blo 2073435 7002395 := bstep (se 1 (by rfl) ⟨5251796, by rfl⟩ : syracuseStep 7002395 = 10503593) B10503593
theorem B4668263 : Blo 2073435 4668263 := bstep (se 1 (by rfl) ⟨3501197, by rfl⟩ : syracuseStep 4668263 = 7002395) B7002395
theorem B3112175 : Blo 2073435 3112175 := bstep (se 1 (by rfl) ⟨2334131, by rfl⟩ : syracuseStep 3112175 = 4668263) B4668263
theorem B2074783 : Blo 2073435 2074783 := bstep (se 1 (by rfl) ⟨1556087, by rfl⟩ : syracuseStep 2074783 = 3112175) B3112175
theorem B3112181 : Blo 2073435 3112181 := bbase (se 5 (by rfl) ⟨145883, by rfl⟩ : syracuseStep 3112181 = 291767) (by norm_num)
theorem B2074787 : Blo 2073435 2074787 := bstep (se 1 (by rfl) ⟨1556090, by rfl⟩ : syracuseStep 2074787 = 3112181) B3112181
theorem B3548981 : Blo 2073435 3548981 := bbase (se 5 (by rfl) ⟨166358, by rfl⟩ : syracuseStep 3548981 = 332717) (by norm_num)
theorem B9463949 : Blo 2073435 9463949 := bstep (se 3 (by rfl) ⟨1774490, by rfl⟩ : syracuseStep 9463949 = 3548981) B3548981
theorem B6309299 : Blo 2073435 6309299 := bstep (se 1 (by rfl) ⟨4731974, by rfl⟩ : syracuseStep 6309299 = 9463949) B9463949
theorem B16824797 : Blo 2073435 16824797 := bstep (se 3 (by rfl) ⟨3154649, by rfl⟩ : syracuseStep 16824797 = 6309299) B6309299
theorem B11216531 : Blo 2073435 11216531 := bstep (se 1 (by rfl) ⟨8412398, by rfl⟩ : syracuseStep 11216531 = 16824797) B16824797
theorem B7477687 : Blo 2073435 7477687 := bstep (se 1 (by rfl) ⟨5608265, by rfl⟩ : syracuseStep 7477687 = 11216531) B11216531
theorem B9970249 : Blo 2073435 9970249 := bstep (se 2 (by rfl) ⟨3738843, by rfl⟩ : syracuseStep 9970249 = 7477687) B7477687
theorem B13293665 : Blo 2073435 13293665 := bstep (se 2 (by rfl) ⟨4985124, by rfl⟩ : syracuseStep 13293665 = 9970249) B9970249
theorem B8862443 : Blo 2073435 8862443 := bstep (se 1 (by rfl) ⟨6646832, by rfl⟩ : syracuseStep 8862443 = 13293665) B13293665
theorem B5908295 : Blo 2073435 5908295 := bstep (se 1 (by rfl) ⟨4431221, by rfl⟩ : syracuseStep 5908295 = 8862443) B8862443
theorem B3938863 : Blo 2073435 3938863 := bstep (se 1 (by rfl) ⟨2954147, by rfl⟩ : syracuseStep 3938863 = 5908295) B5908295
theorem B5251817 : Blo 2073435 5251817 := bstep (se 2 (by rfl) ⟨1969431, by rfl⟩ : syracuseStep 5251817 = 3938863) B3938863
theorem B3501211 : Blo 2073435 3501211 := bstep (se 1 (by rfl) ⟨2625908, by rfl⟩ : syracuseStep 3501211 = 5251817) B5251817
theorem B4668281 : Blo 2073435 4668281 := bstep (se 2 (by rfl) ⟨1750605, by rfl⟩ : syracuseStep 4668281 = 3501211) B3501211
theorem B3112187 : Blo 2073435 3112187 := bstep (se 1 (by rfl) ⟨2334140, by rfl⟩ : syracuseStep 3112187 = 4668281) B4668281
theorem B2074791 : Blo 2073435 2074791 := bstep (se 1 (by rfl) ⟨1556093, by rfl⟩ : syracuseStep 2074791 = 3112187) B3112187
theorem B2334145 : Blo 2073435 2334145 := bbase (se 2 (by rfl) ⟨875304, by rfl⟩ : syracuseStep 2334145 = 1750609) (by norm_num)
theorem B3112193 : Blo 2073435 3112193 := bstep (se 2 (by rfl) ⟨1167072, by rfl⟩ : syracuseStep 3112193 = 2334145) B2334145
theorem B2074795 : Blo 2073435 2074795 := bstep (se 1 (by rfl) ⟨1556096, by rfl⟩ : syracuseStep 2074795 = 3112193) B3112193
theorem B5251837 : Blo 2073435 5251837 := bbase (se 3 (by rfl) ⟨984719, by rfl⟩ : syracuseStep 5251837 = 1969439) (by norm_num)
theorem B7002449 : Blo 2073435 7002449 := bstep (se 2 (by rfl) ⟨2625918, by rfl⟩ : syracuseStep 7002449 = 5251837) B5251837
theorem B4668299 : Blo 2073435 4668299 := bstep (se 1 (by rfl) ⟨3501224, by rfl⟩ : syracuseStep 4668299 = 7002449) B7002449
theorem B3112199 : Blo 2073435 3112199 := bstep (se 1 (by rfl) ⟨2334149, by rfl⟩ : syracuseStep 3112199 = 4668299) B4668299
theorem B2074799 : Blo 2073435 2074799 := bstep (se 1 (by rfl) ⟨1556099, by rfl⟩ : syracuseStep 2074799 = 3112199) B3112199
theorem B3112205 : Blo 2073435 3112205 := bbase (se 3 (by rfl) ⟨583538, by rfl⟩ : syracuseStep 3112205 = 1167077) (by norm_num)
theorem B2074803 : Blo 2073435 2074803 := bstep (se 1 (by rfl) ⟨1556102, by rfl⟩ : syracuseStep 2074803 = 3112205) B3112205
theorem B4668317 : Blo 2073435 4668317 := bbase (se 3 (by rfl) ⟨875309, by rfl⟩ : syracuseStep 4668317 = 1750619) (by norm_num)
theorem B3112211 : Blo 2073435 3112211 := bstep (se 1 (by rfl) ⟨2334158, by rfl⟩ : syracuseStep 3112211 = 4668317) B4668317
theorem B2074807 : Blo 2073435 2074807 := bstep (se 1 (by rfl) ⟨1556105, by rfl⟩ : syracuseStep 2074807 = 3112211) B3112211
theorem B3501245 : Blo 2073435 3501245 := bbase (se 3 (by rfl) ⟨656483, by rfl⟩ : syracuseStep 3501245 = 1312967) (by norm_num)
theorem B2334163 : Blo 2073435 2334163 := bstep (se 1 (by rfl) ⟨1750622, by rfl⟩ : syracuseStep 2334163 = 3501245) B3501245
theorem B3112217 : Blo 2073435 3112217 := bstep (se 2 (by rfl) ⟨1167081, by rfl⟩ : syracuseStep 3112217 = 2334163) B2334163
theorem B2074811 : Blo 2073435 2074811 := bstep (se 1 (by rfl) ⟨1556108, by rfl⟩ : syracuseStep 2074811 = 3112217) B3112217
theorem B11816725 : Blo 2073435 11816725 := bbase (se 6 (by rfl) ⟨276954, by rfl⟩ : syracuseStep 11816725 = 553909) (by norm_num)
theorem B15755633 : Blo 2073435 15755633 := bstep (se 2 (by rfl) ⟨5908362, by rfl⟩ : syracuseStep 15755633 = 11816725) B11816725
theorem B10503755 : Blo 2073435 10503755 := bstep (se 1 (by rfl) ⟨7877816, by rfl⟩ : syracuseStep 10503755 = 15755633) B15755633
theorem B7002503 : Blo 2073435 7002503 := bstep (se 1 (by rfl) ⟨5251877, by rfl⟩ : syracuseStep 7002503 = 10503755) B10503755
theorem B4668335 : Blo 2073435 4668335 := bstep (se 1 (by rfl) ⟨3501251, by rfl⟩ : syracuseStep 4668335 = 7002503) B7002503
theorem B3112223 : Blo 2073435 3112223 := bstep (se 1 (by rfl) ⟨2334167, by rfl⟩ : syracuseStep 3112223 = 4668335) B4668335
theorem B2074815 : Blo 2073435 2074815 := bstep (se 1 (by rfl) ⟨1556111, by rfl⟩ : syracuseStep 2074815 = 3112223) B3112223
theorem B3112229 : Blo 2073435 3112229 := bbase (se 4 (by rfl) ⟨291771, by rfl⟩ : syracuseStep 3112229 = 583543) (by norm_num)
theorem B2074819 : Blo 2073435 2074819 := bstep (se 1 (by rfl) ⟨1556114, by rfl⟩ : syracuseStep 2074819 = 3112229) B3112229
theorem B2625949 : Blo 2073435 2625949 := bbase (se 3 (by rfl) ⟨492365, by rfl⟩ : syracuseStep 2625949 = 984731) (by norm_num)
theorem B3501265 : Blo 2073435 3501265 := bstep (se 2 (by rfl) ⟨1312974, by rfl⟩ : syracuseStep 3501265 = 2625949) B2625949
theorem B4668353 : Blo 2073435 4668353 := bstep (se 2 (by rfl) ⟨1750632, by rfl⟩ : syracuseStep 4668353 = 3501265) B3501265
theorem B3112235 : Blo 2073435 3112235 := bstep (se 1 (by rfl) ⟨2334176, by rfl⟩ : syracuseStep 3112235 = 4668353) B4668353
theorem B2074823 : Blo 2073435 2074823 := bstep (se 1 (by rfl) ⟨1556117, by rfl⟩ : syracuseStep 2074823 = 3112235) B3112235
theorem B2334181 : Blo 2073435 2334181 := bbase (se 4 (by rfl) ⟨218829, by rfl⟩ : syracuseStep 2334181 = 437659) (by norm_num)
theorem B3112241 : Blo 2073435 3112241 := bstep (se 2 (by rfl) ⟨1167090, by rfl⟩ : syracuseStep 3112241 = 2334181) B2334181
theorem B2074827 : Blo 2073435 2074827 := bstep (se 1 (by rfl) ⟨1556120, by rfl⟩ : syracuseStep 2074827 = 3112241) B3112241
theorem B4985221 : Blo 2073435 4985221 := bbase (se 4 (by rfl) ⟨467364, by rfl⟩ : syracuseStep 4985221 = 934729) (by norm_num)
theorem B6646961 : Blo 2073435 6646961 := bstep (se 2 (by rfl) ⟨2492610, by rfl⟩ : syracuseStep 6646961 = 4985221) B4985221
theorem B4431307 : Blo 2073435 4431307 := bstep (se 1 (by rfl) ⟨3323480, by rfl⟩ : syracuseStep 4431307 = 6646961) B6646961
theorem B5908409 : Blo 2073435 5908409 := bstep (se 2 (by rfl) ⟨2215653, by rfl⟩ : syracuseStep 5908409 = 4431307) B4431307
theorem B3938939 : Blo 2073435 3938939 := bstep (se 1 (by rfl) ⟨2954204, by rfl⟩ : syracuseStep 3938939 = 5908409) B5908409
theorem B2625959 : Blo 2073435 2625959 := bstep (se 1 (by rfl) ⟨1969469, by rfl⟩ : syracuseStep 2625959 = 3938939) B3938939
theorem B7002557 : Blo 2073435 7002557 := bstep (se 3 (by rfl) ⟨1312979, by rfl⟩ : syracuseStep 7002557 = 2625959) B2625959
theorem B4668371 : Blo 2073435 4668371 := bstep (se 1 (by rfl) ⟨3501278, by rfl⟩ : syracuseStep 4668371 = 7002557) B7002557
theorem B3112247 : Blo 2073435 3112247 := bstep (se 1 (by rfl) ⟨2334185, by rfl⟩ : syracuseStep 3112247 = 4668371) B4668371
theorem B2074831 : Blo 2073435 2074831 := bstep (se 1 (by rfl) ⟨1556123, by rfl⟩ : syracuseStep 2074831 = 3112247) B3112247
theorem B3112253 : Blo 2073435 3112253 := bbase (se 3 (by rfl) ⟨583547, by rfl⟩ : syracuseStep 3112253 = 1167095) (by norm_num)
theorem B2074835 : Blo 2073435 2074835 := bstep (se 1 (by rfl) ⟨1556126, by rfl⟩ : syracuseStep 2074835 = 3112253) B3112253
theorem B4668389 : Blo 2073435 4668389 := bbase (se 4 (by rfl) ⟨437661, by rfl⟩ : syracuseStep 4668389 = 875323) (by norm_num)
theorem B3112259 : Blo 2073435 3112259 := bstep (se 1 (by rfl) ⟨2334194, by rfl⟩ : syracuseStep 3112259 = 4668389) B4668389
theorem B2074839 : Blo 2073435 2074839 := bstep (se 1 (by rfl) ⟨1556129, by rfl⟩ : syracuseStep 2074839 = 3112259) B3112259
theorem B5251949 : Blo 2073435 5251949 := bbase (se 3 (by rfl) ⟨984740, by rfl⟩ : syracuseStep 5251949 = 1969481) (by norm_num)
theorem B3501299 : Blo 2073435 3501299 := bstep (se 1 (by rfl) ⟨2625974, by rfl⟩ : syracuseStep 3501299 = 5251949) B5251949
theorem B2334199 : Blo 2073435 2334199 := bstep (se 1 (by rfl) ⟨1750649, by rfl⟩ : syracuseStep 2334199 = 3501299) B3501299
theorem B3112265 : Blo 2073435 3112265 := bstep (se 2 (by rfl) ⟨1167099, by rfl⟩ : syracuseStep 3112265 = 2334199) B2334199
theorem B2074843 : Blo 2073435 2074843 := bstep (se 1 (by rfl) ⟨1556132, by rfl⟩ : syracuseStep 2074843 = 3112265) B3112265
theorem B4431341 : Blo 2073435 4431341 := bbase (se 3 (by rfl) ⟨830876, by rfl⟩ : syracuseStep 4431341 = 1661753) (by norm_num)
theorem B2954227 : Blo 2073435 2954227 := bstep (se 1 (by rfl) ⟨2215670, by rfl⟩ : syracuseStep 2954227 = 4431341) B4431341
theorem B3938969 : Blo 2073435 3938969 := bstep (se 2 (by rfl) ⟨1477113, by rfl⟩ : syracuseStep 3938969 = 2954227) B2954227
theorem B10503917 : Blo 2073435 10503917 := bstep (se 3 (by rfl) ⟨1969484, by rfl⟩ : syracuseStep 10503917 = 3938969) B3938969
theorem B7002611 : Blo 2073435 7002611 := bstep (se 1 (by rfl) ⟨5251958, by rfl⟩ : syracuseStep 7002611 = 10503917) B10503917
theorem B4668407 : Blo 2073435 4668407 := bstep (se 1 (by rfl) ⟨3501305, by rfl⟩ : syracuseStep 4668407 = 7002611) B7002611
theorem B3112271 : Blo 2073435 3112271 := bstep (se 1 (by rfl) ⟨2334203, by rfl⟩ : syracuseStep 3112271 = 4668407) B4668407
theorem B2074847 : Blo 2073435 2074847 := bstep (se 1 (by rfl) ⟨1556135, by rfl⟩ : syracuseStep 2074847 = 3112271) B3112271
theorem B3112277 : Blo 2073435 3112277 := bbase (se 11 (by rfl) ⟨2279, by rfl⟩ : syracuseStep 3112277 = 4559) (by norm_num)
theorem B2074851 : Blo 2073435 2074851 := bstep (se 1 (by rfl) ⟨1556138, by rfl⟩ : syracuseStep 2074851 = 3112277) B3112277
theorem B8983637 : Blo 2073435 8983637 := bbase (se 8 (by rfl) ⟨52638, by rfl⟩ : syracuseStep 8983637 = 105277) (by norm_num)
theorem B5989091 : Blo 2073435 5989091 := bstep (se 1 (by rfl) ⟨4491818, by rfl⟩ : syracuseStep 5989091 = 8983637) B8983637
theorem B63883637 : Blo 2073435 63883637 := bstep (se 5 (by rfl) ⟨2994545, by rfl⟩ : syracuseStep 63883637 = 5989091) B5989091
theorem B42589091 : Blo 2073435 42589091 := bstep (se 1 (by rfl) ⟨31941818, by rfl⟩ : syracuseStep 42589091 = 63883637) B63883637
theorem B28392727 : Blo 2073435 28392727 := bstep (se 1 (by rfl) ⟨21294545, by rfl⟩ : syracuseStep 28392727 = 42589091) B42589091
theorem B37856969 : Blo 2073435 37856969 := bstep (se 2 (by rfl) ⟨14196363, by rfl⟩ : syracuseStep 37856969 = 28392727) B28392727
theorem B25237979 : Blo 2073435 25237979 := bstep (se 1 (by rfl) ⟨18928484, by rfl⟩ : syracuseStep 25237979 = 37856969) B37856969
theorem B16825319 : Blo 2073435 16825319 := bstep (se 1 (by rfl) ⟨12618989, by rfl⟩ : syracuseStep 16825319 = 25237979) B25237979
theorem B11216879 : Blo 2073435 11216879 := bstep (se 1 (by rfl) ⟨8412659, by rfl⟩ : syracuseStep 11216879 = 16825319) B16825319
theorem B7477919 : Blo 2073435 7477919 := bstep (se 1 (by rfl) ⟨5608439, by rfl⟩ : syracuseStep 7477919 = 11216879) B11216879
theorem B4985279 : Blo 2073435 4985279 := bstep (se 1 (by rfl) ⟨3738959, by rfl⟩ : syracuseStep 4985279 = 7477919) B7477919
theorem B3323519 : Blo 2073435 3323519 := bstep (se 1 (by rfl) ⟨2492639, by rfl⟩ : syracuseStep 3323519 = 4985279) B4985279
theorem B2215679 : Blo 2073435 2215679 := bstep (se 1 (by rfl) ⟨1661759, by rfl⟩ : syracuseStep 2215679 = 3323519) B3323519
theorem B5908477 : Blo 2073435 5908477 := bstep (se 3 (by rfl) ⟨1107839, by rfl⟩ : syracuseStep 5908477 = 2215679) B2215679
theorem B7877969 : Blo 2073435 7877969 := bstep (se 2 (by rfl) ⟨2954238, by rfl⟩ : syracuseStep 7877969 = 5908477) B5908477
theorem B5251979 : Blo 2073435 5251979 := bstep (se 1 (by rfl) ⟨3938984, by rfl⟩ : syracuseStep 5251979 = 7877969) B7877969
theorem B3501319 : Blo 2073435 3501319 := bstep (se 1 (by rfl) ⟨2625989, by rfl⟩ : syracuseStep 3501319 = 5251979) B5251979
theorem B4668425 : Blo 2073435 4668425 := bstep (se 2 (by rfl) ⟨1750659, by rfl⟩ : syracuseStep 4668425 = 3501319) B3501319
theorem B3112283 : Blo 2073435 3112283 := bstep (se 1 (by rfl) ⟨2334212, by rfl⟩ : syracuseStep 3112283 = 4668425) B4668425
theorem B2074855 : Blo 2073435 2074855 := bstep (se 1 (by rfl) ⟨1556141, by rfl⟩ : syracuseStep 2074855 = 3112283) B3112283
theorem B2334217 : Blo 2073435 2334217 := bbase (se 2 (by rfl) ⟨875331, by rfl⟩ : syracuseStep 2334217 = 1750663) (by norm_num)
theorem B3112289 : Blo 2073435 3112289 := bstep (se 2 (by rfl) ⟨1167108, by rfl⟩ : syracuseStep 3112289 = 2334217) B2334217
theorem B2074859 : Blo 2073435 2074859 := bstep (se 1 (by rfl) ⟨1556144, by rfl⟩ : syracuseStep 2074859 = 3112289) B3112289
theorem B2366069 : Blo 2073435 2366069 := bbase (se 5 (by rfl) ⟨110909, by rfl⟩ : syracuseStep 2366069 = 221819) (by norm_num)
theorem B6309517 : Blo 2073435 6309517 := bstep (se 3 (by rfl) ⟨1183034, by rfl⟩ : syracuseStep 6309517 = 2366069) B2366069
theorem B8412689 : Blo 2073435 8412689 := bstep (se 2 (by rfl) ⟨3154758, by rfl⟩ : syracuseStep 8412689 = 6309517) B6309517
theorem B5608459 : Blo 2073435 5608459 := bstep (se 1 (by rfl) ⟨4206344, by rfl⟩ : syracuseStep 5608459 = 8412689) B8412689
theorem B29911781 : Blo 2073435 29911781 := bstep (se 4 (by rfl) ⟨2804229, by rfl⟩ : syracuseStep 29911781 = 5608459) B5608459
theorem B19941187 : Blo 2073435 19941187 := bstep (se 1 (by rfl) ⟨14955890, by rfl⟩ : syracuseStep 19941187 = 29911781) B29911781
theorem B26588249 : Blo 2073435 26588249 := bstep (se 2 (by rfl) ⟨9970593, by rfl⟩ : syracuseStep 26588249 = 19941187) B19941187
theorem B17725499 : Blo 2073435 17725499 := bstep (se 1 (by rfl) ⟨13294124, by rfl⟩ : syracuseStep 17725499 = 26588249) B26588249
theorem B11816999 : Blo 2073435 11816999 := bstep (se 1 (by rfl) ⟨8862749, by rfl⟩ : syracuseStep 11816999 = 17725499) B17725499
theorem B7877999 : Blo 2073435 7877999 := bstep (se 1 (by rfl) ⟨5908499, by rfl⟩ : syracuseStep 7877999 = 11816999) B11816999
theorem B5251999 : Blo 2073435 5251999 := bstep (se 1 (by rfl) ⟨3938999, by rfl⟩ : syracuseStep 5251999 = 7877999) B7877999
theorem B7002665 : Blo 2073435 7002665 := bstep (se 2 (by rfl) ⟨2625999, by rfl⟩ : syracuseStep 7002665 = 5251999) B5251999
theorem B4668443 : Blo 2073435 4668443 := bstep (se 1 (by rfl) ⟨3501332, by rfl⟩ : syracuseStep 4668443 = 7002665) B7002665
theorem B3112295 : Blo 2073435 3112295 := bstep (se 1 (by rfl) ⟨2334221, by rfl⟩ : syracuseStep 3112295 = 4668443) B4668443
theorem B2074863 : Blo 2073435 2074863 := bstep (se 1 (by rfl) ⟨1556147, by rfl⟩ : syracuseStep 2074863 = 3112295) B3112295
theorem B3112301 : Blo 2073435 3112301 := bbase (se 3 (by rfl) ⟨583556, by rfl⟩ : syracuseStep 3112301 = 1167113) (by norm_num)
theorem B2074867 : Blo 2073435 2074867 := bstep (se 1 (by rfl) ⟨1556150, by rfl⟩ : syracuseStep 2074867 = 3112301) B3112301
theorem B4668461 : Blo 2073435 4668461 := bbase (se 3 (by rfl) ⟨875336, by rfl⟩ : syracuseStep 4668461 = 1750673) (by norm_num)
theorem B3112307 : Blo 2073435 3112307 := bstep (se 1 (by rfl) ⟨2334230, by rfl⟩ : syracuseStep 3112307 = 4668461) B4668461
theorem B2074871 : Blo 2073435 2074871 := bstep (se 1 (by rfl) ⟨1556153, by rfl⟩ : syracuseStep 2074871 = 3112307) B3112307
theorem B2276573 : Blo 2073435 2276573 := bbase (se 3 (by rfl) ⟨426857, by rfl⟩ : syracuseStep 2276573 = 853715) (by norm_num)
theorem B6070861 : Blo 2073435 6070861 := bstep (se 3 (by rfl) ⟨1138286, by rfl⟩ : syracuseStep 6070861 = 2276573) B2276573
theorem B8094481 : Blo 2073435 8094481 := bstep (se 2 (by rfl) ⟨3035430, by rfl⟩ : syracuseStep 8094481 = 6070861) B6070861
theorem B43170565 : Blo 2073435 43170565 := bstep (se 4 (by rfl) ⟨4047240, by rfl⟩ : syracuseStep 43170565 = 8094481) B8094481
theorem B57560753 : Blo 2073435 57560753 := bstep (se 2 (by rfl) ⟨21585282, by rfl⟩ : syracuseStep 57560753 = 43170565) B43170565
theorem B38373835 : Blo 2073435 38373835 := bstep (se 1 (by rfl) ⟨28780376, by rfl⟩ : syracuseStep 38373835 = 57560753) B57560753
theorem B51165113 : Blo 2073435 51165113 := bstep (se 2 (by rfl) ⟨19186917, by rfl⟩ : syracuseStep 51165113 = 38373835) B38373835
theorem B136440301 : Blo 2073435 136440301 := bstep (se 3 (by rfl) ⟨25582556, by rfl⟩ : syracuseStep 136440301 = 51165113) B51165113
theorem B181920401 : Blo 2073435 181920401 := bstep (se 2 (by rfl) ⟨68220150, by rfl⟩ : syracuseStep 181920401 = 136440301) B136440301
theorem B121280267 : Blo 2073435 121280267 := bstep (se 1 (by rfl) ⟨90960200, by rfl⟩ : syracuseStep 121280267 = 181920401) B181920401
theorem B80853511 : Blo 2073435 80853511 := bstep (se 1 (by rfl) ⟨60640133, by rfl⟩ : syracuseStep 80853511 = 121280267) B121280267
theorem B107804681 : Blo 2073435 107804681 := bstep (se 2 (by rfl) ⟨40426755, by rfl⟩ : syracuseStep 107804681 = 80853511) B80853511
theorem B71869787 : Blo 2073435 71869787 := bstep (se 1 (by rfl) ⟨53902340, by rfl⟩ : syracuseStep 71869787 = 107804681) B107804681
theorem B47913191 : Blo 2073435 47913191 := bstep (se 1 (by rfl) ⟨35934893, by rfl⟩ : syracuseStep 47913191 = 71869787) B71869787
theorem B31942127 : Blo 2073435 31942127 := bstep (se 1 (by rfl) ⟨23956595, by rfl⟩ : syracuseStep 31942127 = 47913191) B47913191
theorem B21294751 : Blo 2073435 21294751 := bstep (se 1 (by rfl) ⟨15971063, by rfl⟩ : syracuseStep 21294751 = 31942127) B31942127
theorem B28393001 : Blo 2073435 28393001 := bstep (se 2 (by rfl) ⟨10647375, by rfl⟩ : syracuseStep 28393001 = 21294751) B21294751
theorem B18928667 : Blo 2073435 18928667 := bstep (se 1 (by rfl) ⟨14196500, by rfl⟩ : syracuseStep 18928667 = 28393001) B28393001
theorem B12619111 : Blo 2073435 12619111 := bstep (se 1 (by rfl) ⟨9464333, by rfl⟩ : syracuseStep 12619111 = 18928667) B18928667
theorem B16825481 : Blo 2073435 16825481 := bstep (se 2 (by rfl) ⟨6309555, by rfl⟩ : syracuseStep 16825481 = 12619111) B12619111
theorem B11216987 : Blo 2073435 11216987 := bstep (se 1 (by rfl) ⟨8412740, by rfl⟩ : syracuseStep 11216987 = 16825481) B16825481
theorem B7477991 : Blo 2073435 7477991 := bstep (se 1 (by rfl) ⟨5608493, by rfl⟩ : syracuseStep 7477991 = 11216987) B11216987
theorem B4985327 : Blo 2073435 4985327 := bstep (se 1 (by rfl) ⟨3738995, by rfl⟩ : syracuseStep 4985327 = 7477991) B7477991
theorem B13294205 : Blo 2073435 13294205 := bstep (se 3 (by rfl) ⟨2492663, by rfl⟩ : syracuseStep 13294205 = 4985327) B4985327
theorem B8862803 : Blo 2073435 8862803 := bstep (se 1 (by rfl) ⟨6647102, by rfl⟩ : syracuseStep 8862803 = 13294205) B13294205
theorem B5908535 : Blo 2073435 5908535 := bstep (se 1 (by rfl) ⟨4431401, by rfl⟩ : syracuseStep 5908535 = 8862803) B8862803
theorem B3939023 : Blo 2073435 3939023 := bstep (se 1 (by rfl) ⟨2954267, by rfl⟩ : syracuseStep 3939023 = 5908535) B5908535
theorem B2626015 : Blo 2073435 2626015 := bstep (se 1 (by rfl) ⟨1969511, by rfl⟩ : syracuseStep 2626015 = 3939023) B3939023
theorem B3501353 : Blo 2073435 3501353 := bstep (se 2 (by rfl) ⟨1313007, by rfl⟩ : syracuseStep 3501353 = 2626015) B2626015
theorem B2334235 : Blo 2073435 2334235 := bstep (se 1 (by rfl) ⟨1750676, by rfl⟩ : syracuseStep 2334235 = 3501353) B3501353
theorem B3112313 : Blo 2073435 3112313 := bstep (se 2 (by rfl) ⟨1167117, by rfl⟩ : syracuseStep 3112313 = 2334235) B2334235
theorem B2074875 : Blo 2073435 2074875 := bstep (se 1 (by rfl) ⟨1556156, by rfl⟩ : syracuseStep 2074875 = 3112313) B3112313
theorem B15971093 : Blo 2073435 15971093 := bbase (se 6 (by rfl) ⟨374322, by rfl⟩ : syracuseStep 15971093 = 748645) (by norm_num)
theorem B10647395 : Blo 2073435 10647395 := bstep (se 1 (by rfl) ⟨7985546, by rfl⟩ : syracuseStep 10647395 = 15971093) B15971093
theorem B7098263 : Blo 2073435 7098263 := bstep (se 1 (by rfl) ⟨5323697, by rfl⟩ : syracuseStep 7098263 = 10647395) B10647395
theorem B4732175 : Blo 2073435 4732175 := bstep (se 1 (by rfl) ⟨3549131, by rfl⟩ : syracuseStep 4732175 = 7098263) B7098263
theorem B3154783 : Blo 2073435 3154783 := bstep (se 1 (by rfl) ⟨2366087, by rfl⟩ : syracuseStep 3154783 = 4732175) B4732175
theorem B4206377 : Blo 2073435 4206377 := bstep (se 2 (by rfl) ⟨1577391, by rfl⟩ : syracuseStep 4206377 = 3154783) B3154783
theorem B11217005 : Blo 2073435 11217005 := bstep (se 3 (by rfl) ⟨2103188, by rfl⟩ : syracuseStep 11217005 = 4206377) B4206377
theorem B7478003 : Blo 2073435 7478003 := bstep (se 1 (by rfl) ⟨5608502, by rfl⟩ : syracuseStep 7478003 = 11217005) B11217005
theorem B4985335 : Blo 2073435 4985335 := bstep (se 1 (by rfl) ⟨3739001, by rfl⟩ : syracuseStep 4985335 = 7478003) B7478003
theorem B6647113 : Blo 2073435 6647113 := bstep (se 2 (by rfl) ⟨2492667, by rfl⟩ : syracuseStep 6647113 = 4985335) B4985335
theorem B35451269 : Blo 2073435 35451269 := bstep (se 4 (by rfl) ⟨3323556, by rfl⟩ : syracuseStep 35451269 = 6647113) B6647113
theorem B23634179 : Blo 2073435 23634179 := bstep (se 1 (by rfl) ⟨17725634, by rfl⟩ : syracuseStep 23634179 = 35451269) B35451269
theorem B15756119 : Blo 2073435 15756119 := bstep (se 1 (by rfl) ⟨11817089, by rfl⟩ : syracuseStep 15756119 = 23634179) B23634179
theorem B10504079 : Blo 2073435 10504079 := bstep (se 1 (by rfl) ⟨7878059, by rfl⟩ : syracuseStep 10504079 = 15756119) B15756119
theorem B7002719 : Blo 2073435 7002719 := bstep (se 1 (by rfl) ⟨5252039, by rfl⟩ : syracuseStep 7002719 = 10504079) B10504079
theorem B4668479 : Blo 2073435 4668479 := bstep (se 1 (by rfl) ⟨3501359, by rfl⟩ : syracuseStep 4668479 = 7002719) B7002719
theorem B3112319 : Blo 2073435 3112319 := bstep (se 1 (by rfl) ⟨2334239, by rfl⟩ : syracuseStep 3112319 = 4668479) B4668479
theorem B2074879 : Blo 2073435 2074879 := bstep (se 1 (by rfl) ⟨1556159, by rfl⟩ : syracuseStep 2074879 = 3112319) B3112319
theorem B3112325 : Blo 2073435 3112325 := bbase (se 4 (by rfl) ⟨291780, by rfl⟩ : syracuseStep 3112325 = 583561) (by norm_num)
theorem B2074883 : Blo 2073435 2074883 := bstep (se 1 (by rfl) ⟨1556162, by rfl⟩ : syracuseStep 2074883 = 3112325) B3112325
theorem B3501373 : Blo 2073435 3501373 := bbase (se 3 (by rfl) ⟨656507, by rfl⟩ : syracuseStep 3501373 = 1313015) (by norm_num)
theorem B4668497 : Blo 2073435 4668497 := bstep (se 2 (by rfl) ⟨1750686, by rfl⟩ : syracuseStep 4668497 = 3501373) B3501373
theorem B3112331 : Blo 2073435 3112331 := bstep (se 1 (by rfl) ⟨2334248, by rfl⟩ : syracuseStep 3112331 = 4668497) B4668497
theorem B2074887 : Blo 2073435 2074887 := bstep (se 1 (by rfl) ⟨1556165, by rfl⟩ : syracuseStep 2074887 = 3112331) B3112331
theorem B2334253 : Blo 2073435 2334253 := bbase (se 3 (by rfl) ⟨437672, by rfl⟩ : syracuseStep 2334253 = 875345) (by norm_num)
theorem B3112337 : Blo 2073435 3112337 := bstep (se 2 (by rfl) ⟨1167126, by rfl⟩ : syracuseStep 3112337 = 2334253) B2334253
theorem B2074891 : Blo 2073435 2074891 := bstep (se 1 (by rfl) ⟨1556168, by rfl⟩ : syracuseStep 2074891 = 3112337) B3112337
theorem B7002773 : Blo 2073435 7002773 := bbase (se 6 (by rfl) ⟨164127, by rfl⟩ : syracuseStep 7002773 = 328255) (by norm_num)
theorem B4668515 : Blo 2073435 4668515 := bstep (se 1 (by rfl) ⟨3501386, by rfl⟩ : syracuseStep 4668515 = 7002773) B7002773
theorem B3112343 : Blo 2073435 3112343 := bstep (se 1 (by rfl) ⟨2334257, by rfl⟩ : syracuseStep 3112343 = 4668515) B4668515
theorem B2074895 : Blo 2073435 2074895 := bstep (se 1 (by rfl) ⟨1556171, by rfl⟩ : syracuseStep 2074895 = 3112343) B3112343
theorem B3112349 : Blo 2073435 3112349 := bbase (se 3 (by rfl) ⟨583565, by rfl⟩ : syracuseStep 3112349 = 1167131) (by norm_num)
theorem B2074899 : Blo 2073435 2074899 := bstep (se 1 (by rfl) ⟨1556174, by rfl⟩ : syracuseStep 2074899 = 3112349) B3112349
theorem B4668533 : Blo 2073435 4668533 := bbase (se 5 (by rfl) ⟨218837, by rfl⟩ : syracuseStep 4668533 = 437675) (by norm_num)
theorem B3112355 : Blo 2073435 3112355 := bstep (se 1 (by rfl) ⟨2334266, by rfl⟩ : syracuseStep 3112355 = 4668533) B4668533
theorem B2074903 : Blo 2073435 2074903 := bstep (se 1 (by rfl) ⟨1556177, by rfl⟩ : syracuseStep 2074903 = 3112355) B3112355
theorem B17725877 : Blo 2073435 17725877 := bbase (se 5 (by rfl) ⟨830900, by rfl⟩ : syracuseStep 17725877 = 1661801) (by norm_num)
theorem B11817251 : Blo 2073435 11817251 := bstep (se 1 (by rfl) ⟨8862938, by rfl⟩ : syracuseStep 11817251 = 17725877) B17725877
theorem B7878167 : Blo 2073435 7878167 := bstep (se 1 (by rfl) ⟨5908625, by rfl⟩ : syracuseStep 7878167 = 11817251) B11817251
theorem B5252111 : Blo 2073435 5252111 := bstep (se 1 (by rfl) ⟨3939083, by rfl⟩ : syracuseStep 5252111 = 7878167) B7878167
theorem B3501407 : Blo 2073435 3501407 := bstep (se 1 (by rfl) ⟨2626055, by rfl⟩ : syracuseStep 3501407 = 5252111) B5252111
theorem B2334271 : Blo 2073435 2334271 := bstep (se 1 (by rfl) ⟨1750703, by rfl⟩ : syracuseStep 2334271 = 3501407) B3501407
theorem B3112361 : Blo 2073435 3112361 := bstep (se 2 (by rfl) ⟨1167135, by rfl⟩ : syracuseStep 3112361 = 2334271) B2334271
theorem B2074907 : Blo 2073435 2074907 := bstep (se 1 (by rfl) ⟨1556180, by rfl⟩ : syracuseStep 2074907 = 3112361) B3112361
theorem B7878181 : Blo 2073435 7878181 := bbase (se 4 (by rfl) ⟨738579, by rfl⟩ : syracuseStep 7878181 = 1477159) (by norm_num)
theorem B10504241 : Blo 2073435 10504241 := bstep (se 2 (by rfl) ⟨3939090, by rfl⟩ : syracuseStep 10504241 = 7878181) B7878181
theorem B7002827 : Blo 2073435 7002827 := bstep (se 1 (by rfl) ⟨5252120, by rfl⟩ : syracuseStep 7002827 = 10504241) B10504241
theorem B4668551 : Blo 2073435 4668551 := bstep (se 1 (by rfl) ⟨3501413, by rfl⟩ : syracuseStep 4668551 = 7002827) B7002827
theorem B3112367 : Blo 2073435 3112367 := bstep (se 1 (by rfl) ⟨2334275, by rfl⟩ : syracuseStep 3112367 = 4668551) B4668551
theorem B2074911 : Blo 2073435 2074911 := bstep (se 1 (by rfl) ⟨1556183, by rfl⟩ : syracuseStep 2074911 = 3112367) B3112367
theorem B3112373 : Blo 2073435 3112373 := bbase (se 5 (by rfl) ⟨145892, by rfl⟩ : syracuseStep 3112373 = 291785) (by norm_num)
theorem B2074915 : Blo 2073435 2074915 := bstep (se 1 (by rfl) ⟨1556186, by rfl⟩ : syracuseStep 2074915 = 3112373) B3112373
theorem B5252141 : Blo 2073435 5252141 := bbase (se 3 (by rfl) ⟨984776, by rfl⟩ : syracuseStep 5252141 = 1969553) (by norm_num)
theorem B3501427 : Blo 2073435 3501427 := bstep (se 1 (by rfl) ⟨2626070, by rfl⟩ : syracuseStep 3501427 = 5252141) B5252141
theorem B4668569 : Blo 2073435 4668569 := bstep (se 2 (by rfl) ⟨1750713, by rfl⟩ : syracuseStep 4668569 = 3501427) B3501427
theorem B3112379 : Blo 2073435 3112379 := bstep (se 1 (by rfl) ⟨2334284, by rfl⟩ : syracuseStep 3112379 = 4668569) B4668569
theorem B2074919 : Blo 2073435 2074919 := bstep (se 1 (by rfl) ⟨1556189, by rfl⟩ : syracuseStep 2074919 = 3112379) B3112379
theorem B2334289 : Blo 2073435 2334289 := bbase (se 2 (by rfl) ⟨875358, by rfl⟩ : syracuseStep 2334289 = 1750717) (by norm_num)
theorem B3112385 : Blo 2073435 3112385 := bstep (se 2 (by rfl) ⟨1167144, by rfl⟩ : syracuseStep 3112385 = 2334289) B2334289
theorem B2074923 : Blo 2073435 2074923 := bstep (se 1 (by rfl) ⟨1556192, by rfl⟩ : syracuseStep 2074923 = 3112385) B3112385
theorem B2954341 : Blo 2073435 2954341 := bbase (se 4 (by rfl) ⟨276969, by rfl⟩ : syracuseStep 2954341 = 553939) (by norm_num)
theorem B3939121 : Blo 2073435 3939121 := bstep (se 2 (by rfl) ⟨1477170, by rfl⟩ : syracuseStep 3939121 = 2954341) B2954341
theorem B5252161 : Blo 2073435 5252161 := bstep (se 2 (by rfl) ⟨1969560, by rfl⟩ : syracuseStep 5252161 = 3939121) B3939121
theorem B7002881 : Blo 2073435 7002881 := bstep (se 2 (by rfl) ⟨2626080, by rfl⟩ : syracuseStep 7002881 = 5252161) B5252161
theorem B4668587 : Blo 2073435 4668587 := bstep (se 1 (by rfl) ⟨3501440, by rfl⟩ : syracuseStep 4668587 = 7002881) B7002881
theorem B3112391 : Blo 2073435 3112391 := bstep (se 1 (by rfl) ⟨2334293, by rfl⟩ : syracuseStep 3112391 = 4668587) B4668587
theorem B2074927 : Blo 2073435 2074927 := bstep (se 1 (by rfl) ⟨1556195, by rfl⟩ : syracuseStep 2074927 = 3112391) B3112391
theorem B3112397 : Blo 2073435 3112397 := bbase (se 3 (by rfl) ⟨583574, by rfl⟩ : syracuseStep 3112397 = 1167149) (by norm_num)
theorem B2074931 : Blo 2073435 2074931 := bstep (se 1 (by rfl) ⟨1556198, by rfl⟩ : syracuseStep 2074931 = 3112397) B3112397
theorem B4668605 : Blo 2073435 4668605 := bbase (se 3 (by rfl) ⟨875363, by rfl⟩ : syracuseStep 4668605 = 1750727) (by norm_num)
theorem B3112403 : Blo 2073435 3112403 := bstep (se 1 (by rfl) ⟨2334302, by rfl⟩ : syracuseStep 3112403 = 4668605) B4668605
theorem B2074935 : Blo 2073435 2074935 := bstep (se 1 (by rfl) ⟨1556201, by rfl⟩ : syracuseStep 2074935 = 3112403) B3112403
theorem B3501461 : Blo 2073435 3501461 := bbase (se 6 (by rfl) ⟨82065, by rfl⟩ : syracuseStep 3501461 = 164131) (by norm_num)
theorem B2334307 : Blo 2073435 2334307 := bstep (se 1 (by rfl) ⟨1750730, by rfl⟩ : syracuseStep 2334307 = 3501461) B3501461
theorem B3112409 : Blo 2073435 3112409 := bstep (se 2 (by rfl) ⟨1167153, by rfl⟩ : syracuseStep 3112409 = 2334307) B2334307
theorem B2074939 : Blo 2073435 2074939 := bstep (se 1 (by rfl) ⟨1556204, by rfl⟩ : syracuseStep 2074939 = 3112409) B3112409
theorem B3739117 : Blo 2073435 3739117 := bbase (se 3 (by rfl) ⟨701084, by rfl⟩ : syracuseStep 3739117 = 1402169) (by norm_num)
theorem B4985489 : Blo 2073435 4985489 := bstep (se 2 (by rfl) ⟨1869558, by rfl⟩ : syracuseStep 4985489 = 3739117) B3739117
theorem B13294637 : Blo 2073435 13294637 := bstep (se 3 (by rfl) ⟨2492744, by rfl⟩ : syracuseStep 13294637 = 4985489) B4985489
theorem B8863091 : Blo 2073435 8863091 := bstep (se 1 (by rfl) ⟨6647318, by rfl⟩ : syracuseStep 8863091 = 13294637) B13294637
theorem B5908727 : Blo 2073435 5908727 := bstep (se 1 (by rfl) ⟨4431545, by rfl⟩ : syracuseStep 5908727 = 8863091) B8863091
theorem B15756605 : Blo 2073435 15756605 := bstep (se 3 (by rfl) ⟨2954363, by rfl⟩ : syracuseStep 15756605 = 5908727) B5908727
theorem B10504403 : Blo 2073435 10504403 := bstep (se 1 (by rfl) ⟨7878302, by rfl⟩ : syracuseStep 10504403 = 15756605) B15756605
theorem B7002935 : Blo 2073435 7002935 := bstep (se 1 (by rfl) ⟨5252201, by rfl⟩ : syracuseStep 7002935 = 10504403) B10504403
theorem B4668623 : Blo 2073435 4668623 := bstep (se 1 (by rfl) ⟨3501467, by rfl⟩ : syracuseStep 4668623 = 7002935) B7002935
theorem B3112415 : Blo 2073435 3112415 := bstep (se 1 (by rfl) ⟨2334311, by rfl⟩ : syracuseStep 3112415 = 4668623) B4668623
theorem B2074943 : Blo 2073435 2074943 := bstep (se 1 (by rfl) ⟨1556207, by rfl⟩ : syracuseStep 2074943 = 3112415) B3112415
theorem B3112421 : Blo 2073435 3112421 := bbase (se 4 (by rfl) ⟨291789, by rfl⟩ : syracuseStep 3112421 = 583579) (by norm_num)
theorem B2074947 : Blo 2073435 2074947 := bstep (se 1 (by rfl) ⟨1556210, by rfl⟩ : syracuseStep 2074947 = 3112421) B3112421
theorem B19942037 : Blo 2073435 19942037 := bbase (se 6 (by rfl) ⟨467391, by rfl⟩ : syracuseStep 19942037 = 934783) (by norm_num)
theorem B13294691 : Blo 2073435 13294691 := bstep (se 1 (by rfl) ⟨9971018, by rfl⟩ : syracuseStep 13294691 = 19942037) B19942037
theorem B8863127 : Blo 2073435 8863127 := bstep (se 1 (by rfl) ⟨6647345, by rfl⟩ : syracuseStep 8863127 = 13294691) B13294691
theorem B5908751 : Blo 2073435 5908751 := bstep (se 1 (by rfl) ⟨4431563, by rfl⟩ : syracuseStep 5908751 = 8863127) B8863127
theorem B3939167 : Blo 2073435 3939167 := bstep (se 1 (by rfl) ⟨2954375, by rfl⟩ : syracuseStep 3939167 = 5908751) B5908751
theorem B2626111 : Blo 2073435 2626111 := bstep (se 1 (by rfl) ⟨1969583, by rfl⟩ : syracuseStep 2626111 = 3939167) B3939167
theorem B3501481 : Blo 2073435 3501481 := bstep (se 2 (by rfl) ⟨1313055, by rfl⟩ : syracuseStep 3501481 = 2626111) B2626111
theorem B4668641 : Blo 2073435 4668641 := bstep (se 2 (by rfl) ⟨1750740, by rfl⟩ : syracuseStep 4668641 = 3501481) B3501481
theorem B3112427 : Blo 2073435 3112427 := bstep (se 1 (by rfl) ⟨2334320, by rfl⟩ : syracuseStep 3112427 = 4668641) B4668641
theorem B2074951 : Blo 2073435 2074951 := bstep (se 1 (by rfl) ⟨1556213, by rfl⟩ : syracuseStep 2074951 = 3112427) B3112427
theorem B2334325 : Blo 2073435 2334325 := bbase (se 5 (by rfl) ⟨109421, by rfl⟩ : syracuseStep 2334325 = 218843) (by norm_num)
theorem B3112433 : Blo 2073435 3112433 := bstep (se 2 (by rfl) ⟨1167162, by rfl⟩ : syracuseStep 3112433 = 2334325) B2334325
theorem B2074955 : Blo 2073435 2074955 := bstep (se 1 (by rfl) ⟨1556216, by rfl⟩ : syracuseStep 2074955 = 3112433) B3112433
theorem B2626121 : Blo 2073435 2626121 := bbase (se 2 (by rfl) ⟨984795, by rfl⟩ : syracuseStep 2626121 = 1969591) (by norm_num)
theorem B7002989 : Blo 2073435 7002989 := bstep (se 3 (by rfl) ⟨1313060, by rfl⟩ : syracuseStep 7002989 = 2626121) B2626121
theorem B4668659 : Blo 2073435 4668659 := bstep (se 1 (by rfl) ⟨3501494, by rfl⟩ : syracuseStep 4668659 = 7002989) B7002989
theorem B3112439 : Blo 2073435 3112439 := bstep (se 1 (by rfl) ⟨2334329, by rfl⟩ : syracuseStep 3112439 = 4668659) B4668659
theorem B2074959 : Blo 2073435 2074959 := bstep (se 1 (by rfl) ⟨1556219, by rfl⟩ : syracuseStep 2074959 = 3112439) B3112439
theorem B3112445 : Blo 2073435 3112445 := bbase (se 3 (by rfl) ⟨583583, by rfl⟩ : syracuseStep 3112445 = 1167167) (by norm_num)
theorem B2074963 : Blo 2073435 2074963 := bstep (se 1 (by rfl) ⟨1556222, by rfl⟩ : syracuseStep 2074963 = 3112445) B3112445
theorem B4668677 : Blo 2073435 4668677 := bbase (se 4 (by rfl) ⟨437688, by rfl⟩ : syracuseStep 4668677 = 875377) (by norm_num)
theorem B3112451 : Blo 2073435 3112451 := bstep (se 1 (by rfl) ⟨2334338, by rfl⟩ : syracuseStep 3112451 = 4668677) B4668677
theorem B2074967 : Blo 2073435 2074967 := bstep (se 1 (by rfl) ⟨1556225, by rfl⟩ : syracuseStep 2074967 = 3112451) B3112451
theorem B3939205 : Blo 2073435 3939205 := bbase (se 4 (by rfl) ⟨369300, by rfl⟩ : syracuseStep 3939205 = 738601) (by norm_num)
theorem B5252273 : Blo 2073435 5252273 := bstep (se 2 (by rfl) ⟨1969602, by rfl⟩ : syracuseStep 5252273 = 3939205) B3939205
theorem B3501515 : Blo 2073435 3501515 := bstep (se 1 (by rfl) ⟨2626136, by rfl⟩ : syracuseStep 3501515 = 5252273) B5252273
theorem B2334343 : Blo 2073435 2334343 := bstep (se 1 (by rfl) ⟨1750757, by rfl⟩ : syracuseStep 2334343 = 3501515) B3501515
theorem B3112457 : Blo 2073435 3112457 := bstep (se 2 (by rfl) ⟨1167171, by rfl⟩ : syracuseStep 3112457 = 2334343) B2334343
theorem B2074971 : Blo 2073435 2074971 := bstep (se 1 (by rfl) ⟨1556228, by rfl⟩ : syracuseStep 2074971 = 3112457) B3112457
theorem B10504565 : Blo 2073435 10504565 := bbase (se 5 (by rfl) ⟨492401, by rfl⟩ : syracuseStep 10504565 = 984803) (by norm_num)
theorem B7003043 : Blo 2073435 7003043 := bstep (se 1 (by rfl) ⟨5252282, by rfl⟩ : syracuseStep 7003043 = 10504565) B10504565
theorem B4668695 : Blo 2073435 4668695 := bstep (se 1 (by rfl) ⟨3501521, by rfl⟩ : syracuseStep 4668695 = 7003043) B7003043
theorem B3112463 : Blo 2073435 3112463 := bstep (se 1 (by rfl) ⟨2334347, by rfl⟩ : syracuseStep 3112463 = 4668695) B4668695
theorem B2074975 : Blo 2073435 2074975 := bstep (se 1 (by rfl) ⟨1556231, by rfl⟩ : syracuseStep 2074975 = 3112463) B3112463
theorem B3112469 : Blo 2073435 3112469 := bbase (se 6 (by rfl) ⟨72948, by rfl⟩ : syracuseStep 3112469 = 145897) (by norm_num)
theorem B2074979 : Blo 2073435 2074979 := bstep (se 1 (by rfl) ⟨1556234, by rfl⟩ : syracuseStep 2074979 = 3112469) B3112469
theorem B14956757 : Blo 2073435 14956757 := bbase (se 7 (by rfl) ⟨175274, by rfl⟩ : syracuseStep 14956757 = 350549) (by norm_num)
theorem B9971171 : Blo 2073435 9971171 := bstep (se 1 (by rfl) ⟨7478378, by rfl⟩ : syracuseStep 9971171 = 14956757) B14956757
theorem B6647447 : Blo 2073435 6647447 := bstep (se 1 (by rfl) ⟨4985585, by rfl⟩ : syracuseStep 6647447 = 9971171) B9971171
theorem B17726525 : Blo 2073435 17726525 := bstep (se 3 (by rfl) ⟨3323723, by rfl⟩ : syracuseStep 17726525 = 6647447) B6647447
theorem B11817683 : Blo 2073435 11817683 := bstep (se 1 (by rfl) ⟨8863262, by rfl⟩ : syracuseStep 11817683 = 17726525) B17726525
theorem B7878455 : Blo 2073435 7878455 := bstep (se 1 (by rfl) ⟨5908841, by rfl⟩ : syracuseStep 7878455 = 11817683) B11817683
theorem B5252303 : Blo 2073435 5252303 := bstep (se 1 (by rfl) ⟨3939227, by rfl⟩ : syracuseStep 5252303 = 7878455) B7878455
theorem B3501535 : Blo 2073435 3501535 := bstep (se 1 (by rfl) ⟨2626151, by rfl⟩ : syracuseStep 3501535 = 5252303) B5252303
theorem B4668713 : Blo 2073435 4668713 := bstep (se 2 (by rfl) ⟨1750767, by rfl⟩ : syracuseStep 4668713 = 3501535) B3501535
theorem B3112475 : Blo 2073435 3112475 := bstep (se 1 (by rfl) ⟨2334356, by rfl⟩ : syracuseStep 3112475 = 4668713) B4668713
theorem B2074983 : Blo 2073435 2074983 := bstep (se 1 (by rfl) ⟨1556237, by rfl⟩ : syracuseStep 2074983 = 3112475) B3112475
theorem B2334361 : Blo 2073435 2334361 := bbase (se 2 (by rfl) ⟨875385, by rfl⟩ : syracuseStep 2334361 = 1750771) (by norm_num)
theorem B3112481 : Blo 2073435 3112481 := bstep (se 2 (by rfl) ⟨1167180, by rfl⟩ : syracuseStep 3112481 = 2334361) B2334361
theorem B2074987 : Blo 2073435 2074987 := bstep (se 1 (by rfl) ⟨1556240, by rfl⟩ : syracuseStep 2074987 = 3112481) B3112481
theorem B7878485 : Blo 2073435 7878485 := bbase (se 9 (by rfl) ⟨23081, by rfl⟩ : syracuseStep 7878485 = 46163) (by norm_num)
theorem B5252323 : Blo 2073435 5252323 := bstep (se 1 (by rfl) ⟨3939242, by rfl⟩ : syracuseStep 5252323 = 7878485) B7878485
theorem B7003097 : Blo 2073435 7003097 := bstep (se 2 (by rfl) ⟨2626161, by rfl⟩ : syracuseStep 7003097 = 5252323) B5252323
theorem B4668731 : Blo 2073435 4668731 := bstep (se 1 (by rfl) ⟨3501548, by rfl⟩ : syracuseStep 4668731 = 7003097) B7003097
theorem B3112487 : Blo 2073435 3112487 := bstep (se 1 (by rfl) ⟨2334365, by rfl⟩ : syracuseStep 3112487 = 4668731) B4668731
theorem B2074991 : Blo 2073435 2074991 := bstep (se 1 (by rfl) ⟨1556243, by rfl⟩ : syracuseStep 2074991 = 3112487) B3112487
theorem B3112493 : Blo 2073435 3112493 := bbase (se 3 (by rfl) ⟨583592, by rfl⟩ : syracuseStep 3112493 = 1167185) (by norm_num)
theorem B2074995 : Blo 2073435 2074995 := bstep (se 1 (by rfl) ⟨1556246, by rfl⟩ : syracuseStep 2074995 = 3112493) B3112493
theorem B4668749 : Blo 2073435 4668749 := bbase (se 3 (by rfl) ⟨875390, by rfl⟩ : syracuseStep 4668749 = 1750781) (by norm_num)
theorem B3112499 : Blo 2073435 3112499 := bstep (se 1 (by rfl) ⟨2334374, by rfl⟩ : syracuseStep 3112499 = 4668749) B4668749
theorem B2074999 : Blo 2073435 2074999 := bstep (se 1 (by rfl) ⟨1556249, by rfl⟩ : syracuseStep 2074999 = 3112499) B3112499
theorem B2626177 : Blo 2073435 2626177 := bbase (se 2 (by rfl) ⟨984816, by rfl⟩ : syracuseStep 2626177 = 1969633) (by norm_num)
theorem B3501569 : Blo 2073435 3501569 := bstep (se 2 (by rfl) ⟨1313088, by rfl⟩ : syracuseStep 3501569 = 2626177) B2626177
theorem B2334379 : Blo 2073435 2334379 := bstep (se 1 (by rfl) ⟨1750784, by rfl⟩ : syracuseStep 2334379 = 3501569) B3501569
theorem B3112505 : Blo 2073435 3112505 := bstep (se 2 (by rfl) ⟨1167189, by rfl⟩ : syracuseStep 3112505 = 2334379) B2334379
theorem B2075003 : Blo 2073435 2075003 := bstep (se 1 (by rfl) ⟨1556252, by rfl⟩ : syracuseStep 2075003 = 3112505) B3112505
theorem B2215841 : Blo 2073435 2215841 := bbase (se 2 (by rfl) ⟨830940, by rfl⟩ : syracuseStep 2215841 = 1661881) (by norm_num)
theorem B23635637 : Blo 2073435 23635637 := bstep (se 5 (by rfl) ⟨1107920, by rfl⟩ : syracuseStep 23635637 = 2215841) B2215841
theorem B15757091 : Blo 2073435 15757091 := bstep (se 1 (by rfl) ⟨11817818, by rfl⟩ : syracuseStep 15757091 = 23635637) B23635637
theorem B10504727 : Blo 2073435 10504727 := bstep (se 1 (by rfl) ⟨7878545, by rfl⟩ : syracuseStep 10504727 = 15757091) B15757091
theorem B7003151 : Blo 2073435 7003151 := bstep (se 1 (by rfl) ⟨5252363, by rfl⟩ : syracuseStep 7003151 = 10504727) B10504727
theorem B4668767 : Blo 2073435 4668767 := bstep (se 1 (by rfl) ⟨3501575, by rfl⟩ : syracuseStep 4668767 = 7003151) B7003151
theorem B3112511 : Blo 2073435 3112511 := bstep (se 1 (by rfl) ⟨2334383, by rfl⟩ : syracuseStep 3112511 = 4668767) B4668767
theorem B2075007 : Blo 2073435 2075007 := bstep (se 1 (by rfl) ⟨1556255, by rfl⟩ : syracuseStep 2075007 = 3112511) B3112511
theorem B3112517 : Blo 2073435 3112517 := bbase (se 4 (by rfl) ⟨291798, by rfl⟩ : syracuseStep 3112517 = 583597) (by norm_num)
theorem B2075011 : Blo 2073435 2075011 := bstep (se 1 (by rfl) ⟨1556258, by rfl⟩ : syracuseStep 2075011 = 3112517) B3112517
theorem B3501589 : Blo 2073435 3501589 := bbase (se 6 (by rfl) ⟨82068, by rfl⟩ : syracuseStep 3501589 = 164137) (by norm_num)
theorem B4668785 : Blo 2073435 4668785 := bstep (se 2 (by rfl) ⟨1750794, by rfl⟩ : syracuseStep 4668785 = 3501589) B3501589
theorem B3112523 : Blo 2073435 3112523 := bstep (se 1 (by rfl) ⟨2334392, by rfl⟩ : syracuseStep 3112523 = 4668785) B4668785
theorem B2075015 : Blo 2073435 2075015 := bstep (se 1 (by rfl) ⟨1556261, by rfl⟩ : syracuseStep 2075015 = 3112523) B3112523
theorem B2334397 : Blo 2073435 2334397 := bbase (se 3 (by rfl) ⟨437699, by rfl⟩ : syracuseStep 2334397 = 875399) (by norm_num)
theorem B3112529 : Blo 2073435 3112529 := bstep (se 2 (by rfl) ⟨1167198, by rfl⟩ : syracuseStep 3112529 = 2334397) B2334397
theorem B2075019 : Blo 2073435 2075019 := bstep (se 1 (by rfl) ⟨1556264, by rfl⟩ : syracuseStep 2075019 = 3112529) B3112529
theorem B7003205 : Blo 2073435 7003205 := bbase (se 4 (by rfl) ⟨656550, by rfl⟩ : syracuseStep 7003205 = 1313101) (by norm_num)
theorem B4668803 : Blo 2073435 4668803 := bstep (se 1 (by rfl) ⟨3501602, by rfl⟩ : syracuseStep 4668803 = 7003205) B7003205
theorem B3112535 : Blo 2073435 3112535 := bstep (se 1 (by rfl) ⟨2334401, by rfl⟩ : syracuseStep 3112535 = 4668803) B4668803
theorem B2075023 : Blo 2073435 2075023 := bstep (se 1 (by rfl) ⟨1556267, by rfl⟩ : syracuseStep 2075023 = 3112535) B3112535
theorem B3112541 : Blo 2073435 3112541 := bbase (se 3 (by rfl) ⟨583601, by rfl⟩ : syracuseStep 3112541 = 1167203) (by norm_num)
theorem B2075027 : Blo 2073435 2075027 := bstep (se 1 (by rfl) ⟨1556270, by rfl⟩ : syracuseStep 2075027 = 3112541) B3112541
theorem B4668821 : Blo 2073435 4668821 := bbase (se 6 (by rfl) ⟨109425, by rfl⟩ : syracuseStep 4668821 = 218851) (by norm_num)
theorem B3112547 : Blo 2073435 3112547 := bstep (se 1 (by rfl) ⟨2334410, by rfl⟩ : syracuseStep 3112547 = 4668821) B4668821
theorem B2075031 : Blo 2073435 2075031 := bstep (se 1 (by rfl) ⟨1556273, by rfl⟩ : syracuseStep 2075031 = 3112547) B3112547
theorem B2662049 : Blo 2073435 2662049 := bbase (se 2 (by rfl) ⟨998268, by rfl⟩ : syracuseStep 2662049 = 1996537) (by norm_num)
theorem B7098797 : Blo 2073435 7098797 := bstep (se 3 (by rfl) ⟨1331024, by rfl⟩ : syracuseStep 7098797 = 2662049) B2662049
theorem B18930125 : Blo 2073435 18930125 := bstep (se 3 (by rfl) ⟨3549398, by rfl⟩ : syracuseStep 18930125 = 7098797) B7098797
theorem B50480333 : Blo 2073435 50480333 := bstep (se 3 (by rfl) ⟨9465062, by rfl⟩ : syracuseStep 50480333 = 18930125) B18930125
theorem B33653555 : Blo 2073435 33653555 := bstep (se 1 (by rfl) ⟨25240166, by rfl⟩ : syracuseStep 33653555 = 50480333) B50480333
theorem B22435703 : Blo 2073435 22435703 := bstep (se 1 (by rfl) ⟨16826777, by rfl⟩ : syracuseStep 22435703 = 33653555) B33653555
theorem B14957135 : Blo 2073435 14957135 := bstep (se 1 (by rfl) ⟨11217851, by rfl⟩ : syracuseStep 14957135 = 22435703) B22435703
theorem B9971423 : Blo 2073435 9971423 := bstep (se 1 (by rfl) ⟨7478567, by rfl⟩ : syracuseStep 9971423 = 14957135) B14957135
theorem B6647615 : Blo 2073435 6647615 := bstep (se 1 (by rfl) ⟨4985711, by rfl⟩ : syracuseStep 6647615 = 9971423) B9971423
theorem B4431743 : Blo 2073435 4431743 := bstep (se 1 (by rfl) ⟨3323807, by rfl⟩ : syracuseStep 4431743 = 6647615) B6647615
theorem B2954495 : Blo 2073435 2954495 := bstep (se 1 (by rfl) ⟨2215871, by rfl⟩ : syracuseStep 2954495 = 4431743) B4431743
theorem B7878653 : Blo 2073435 7878653 := bstep (se 3 (by rfl) ⟨1477247, by rfl⟩ : syracuseStep 7878653 = 2954495) B2954495
theorem B5252435 : Blo 2073435 5252435 := bstep (se 1 (by rfl) ⟨3939326, by rfl⟩ : syracuseStep 5252435 = 7878653) B7878653
theorem B3501623 : Blo 2073435 3501623 := bstep (se 1 (by rfl) ⟨2626217, by rfl⟩ : syracuseStep 3501623 = 5252435) B5252435
theorem B2334415 : Blo 2073435 2334415 := bstep (se 1 (by rfl) ⟨1750811, by rfl⟩ : syracuseStep 2334415 = 3501623) B3501623
theorem B3112553 : Blo 2073435 3112553 := bstep (se 2 (by rfl) ⟨1167207, by rfl⟩ : syracuseStep 3112553 = 2334415) B2334415
theorem B2075035 : Blo 2073435 2075035 := bstep (se 1 (by rfl) ⟨1556276, by rfl⟩ : syracuseStep 2075035 = 3112553) B3112553
theorem B3323813 : Blo 2073435 3323813 := bbase (se 4 (by rfl) ⟨311607, by rfl⟩ : syracuseStep 3323813 = 623215) (by norm_num)
theorem B8863501 : Blo 2073435 8863501 := bstep (se 3 (by rfl) ⟨1661906, by rfl⟩ : syracuseStep 8863501 = 3323813) B3323813
theorem B11818001 : Blo 2073435 11818001 := bstep (se 2 (by rfl) ⟨4431750, by rfl⟩ : syracuseStep 11818001 = 8863501) B8863501
theorem B7878667 : Blo 2073435 7878667 := bstep (se 1 (by rfl) ⟨5909000, by rfl⟩ : syracuseStep 7878667 = 11818001) B11818001
theorem B10504889 : Blo 2073435 10504889 := bstep (se 2 (by rfl) ⟨3939333, by rfl⟩ : syracuseStep 10504889 = 7878667) B7878667
theorem B7003259 : Blo 2073435 7003259 := bstep (se 1 (by rfl) ⟨5252444, by rfl⟩ : syracuseStep 7003259 = 10504889) B10504889
theorem B4668839 : Blo 2073435 4668839 := bstep (se 1 (by rfl) ⟨3501629, by rfl⟩ : syracuseStep 4668839 = 7003259) B7003259
theorem B3112559 : Blo 2073435 3112559 := bstep (se 1 (by rfl) ⟨2334419, by rfl⟩ : syracuseStep 3112559 = 4668839) B4668839
theorem B2075039 : Blo 2073435 2075039 := bstep (se 1 (by rfl) ⟨1556279, by rfl⟩ : syracuseStep 2075039 = 3112559) B3112559
theorem B3112565 : Blo 2073435 3112565 := bbase (se 5 (by rfl) ⟨145901, by rfl⟩ : syracuseStep 3112565 = 291803) (by norm_num)
theorem B2075043 : Blo 2073435 2075043 := bstep (se 1 (by rfl) ⟨1556282, by rfl⟩ : syracuseStep 2075043 = 3112565) B3112565
theorem B3939349 : Blo 2073435 3939349 := bbase (se 6 (by rfl) ⟨92328, by rfl⟩ : syracuseStep 3939349 = 184657) (by norm_num)
theorem B5252465 : Blo 2073435 5252465 := bstep (se 2 (by rfl) ⟨1969674, by rfl⟩ : syracuseStep 5252465 = 3939349) B3939349
theorem B3501643 : Blo 2073435 3501643 := bstep (se 1 (by rfl) ⟨2626232, by rfl⟩ : syracuseStep 3501643 = 5252465) B5252465
theorem B4668857 : Blo 2073435 4668857 := bstep (se 2 (by rfl) ⟨1750821, by rfl⟩ : syracuseStep 4668857 = 3501643) B3501643
theorem B3112571 : Blo 2073435 3112571 := bstep (se 1 (by rfl) ⟨2334428, by rfl⟩ : syracuseStep 3112571 = 4668857) B4668857
theorem B2075047 : Blo 2073435 2075047 := bstep (se 1 (by rfl) ⟨1556285, by rfl⟩ : syracuseStep 2075047 = 3112571) B3112571
theorem B2334433 : Blo 2073435 2334433 := bbase (se 2 (by rfl) ⟨875412, by rfl⟩ : syracuseStep 2334433 = 1750825) (by norm_num)
theorem B3112577 : Blo 2073435 3112577 := bstep (se 2 (by rfl) ⟨1167216, by rfl⟩ : syracuseStep 3112577 = 2334433) B2334433
theorem B2075051 : Blo 2073435 2075051 := bstep (se 1 (by rfl) ⟨1556288, by rfl⟩ : syracuseStep 2075051 = 3112577) B3112577
theorem B5252485 : Blo 2073435 5252485 := bbase (se 4 (by rfl) ⟨492420, by rfl⟩ : syracuseStep 5252485 = 984841) (by norm_num)
theorem B7003313 : Blo 2073435 7003313 := bstep (se 2 (by rfl) ⟨2626242, by rfl⟩ : syracuseStep 7003313 = 5252485) B5252485
theorem B4668875 : Blo 2073435 4668875 := bstep (se 1 (by rfl) ⟨3501656, by rfl⟩ : syracuseStep 4668875 = 7003313) B7003313
theorem B3112583 : Blo 2073435 3112583 := bstep (se 1 (by rfl) ⟨2334437, by rfl⟩ : syracuseStep 3112583 = 4668875) B4668875
theorem B2075055 : Blo 2073435 2075055 := bstep (se 1 (by rfl) ⟨1556291, by rfl⟩ : syracuseStep 2075055 = 3112583) B3112583
theorem B3112589 : Blo 2073435 3112589 := bbase (se 3 (by rfl) ⟨583610, by rfl⟩ : syracuseStep 3112589 = 1167221) (by norm_num)
theorem B2075059 : Blo 2073435 2075059 := bstep (se 1 (by rfl) ⟨1556294, by rfl⟩ : syracuseStep 2075059 = 3112589) B3112589
theorem B4668893 : Blo 2073435 4668893 := bbase (se 3 (by rfl) ⟨875417, by rfl⟩ : syracuseStep 4668893 = 1750835) (by norm_num)
theorem B3112595 : Blo 2073435 3112595 := bstep (se 1 (by rfl) ⟨2334446, by rfl⟩ : syracuseStep 3112595 = 4668893) B4668893
theorem B2075063 : Blo 2073435 2075063 := bstep (se 1 (by rfl) ⟨1556297, by rfl⟩ : syracuseStep 2075063 = 3112595) B3112595
theorem B3501677 : Blo 2073435 3501677 := bbase (se 3 (by rfl) ⟨656564, by rfl⟩ : syracuseStep 3501677 = 1313129) (by norm_num)
theorem B2334451 : Blo 2073435 2334451 := bstep (se 1 (by rfl) ⟨1750838, by rfl⟩ : syracuseStep 2334451 = 3501677) B3501677
theorem B3112601 : Blo 2073435 3112601 := bstep (se 2 (by rfl) ⟨1167225, by rfl⟩ : syracuseStep 3112601 = 2334451) B2334451
theorem B2075067 : Blo 2073435 2075067 := bstep (se 1 (by rfl) ⟨1556300, by rfl⟩ : syracuseStep 2075067 = 3112601) B3112601
theorem B4732613 : Blo 2073435 4732613 := bbase (se 4 (by rfl) ⟨443682, by rfl⟩ : syracuseStep 4732613 = 887365) (by norm_num)
theorem B3155075 : Blo 2073435 3155075 := bstep (se 1 (by rfl) ⟨2366306, by rfl⟩ : syracuseStep 3155075 = 4732613) B4732613
theorem B2103383 : Blo 2073435 2103383 := bstep (se 1 (by rfl) ⟨1577537, by rfl⟩ : syracuseStep 2103383 = 3155075) B3155075
theorem B5609021 : Blo 2073435 5609021 := bstep (se 3 (by rfl) ⟨1051691, by rfl⟩ : syracuseStep 5609021 = 2103383) B2103383
theorem B14957389 : Blo 2073435 14957389 := bstep (se 3 (by rfl) ⟨2804510, by rfl⟩ : syracuseStep 14957389 = 5609021) B5609021
theorem B19943185 : Blo 2073435 19943185 := bstep (se 2 (by rfl) ⟨7478694, by rfl⟩ : syracuseStep 19943185 = 14957389) B14957389
theorem B26590913 : Blo 2073435 26590913 := bstep (se 2 (by rfl) ⟨9971592, by rfl⟩ : syracuseStep 26590913 = 19943185) B19943185
theorem B17727275 : Blo 2073435 17727275 := bstep (se 1 (by rfl) ⟨13295456, by rfl⟩ : syracuseStep 17727275 = 26590913) B26590913
theorem B11818183 : Blo 2073435 11818183 := bstep (se 1 (by rfl) ⟨8863637, by rfl⟩ : syracuseStep 11818183 = 17727275) B17727275
theorem B15757577 : Blo 2073435 15757577 := bstep (se 2 (by rfl) ⟨5909091, by rfl⟩ : syracuseStep 15757577 = 11818183) B11818183
theorem B10505051 : Blo 2073435 10505051 := bstep (se 1 (by rfl) ⟨7878788, by rfl⟩ : syracuseStep 10505051 = 15757577) B15757577
theorem B7003367 : Blo 2073435 7003367 := bstep (se 1 (by rfl) ⟨5252525, by rfl⟩ : syracuseStep 7003367 = 10505051) B10505051
theorem B4668911 : Blo 2073435 4668911 := bstep (se 1 (by rfl) ⟨3501683, by rfl⟩ : syracuseStep 4668911 = 7003367) B7003367
theorem B3112607 : Blo 2073435 3112607 := bstep (se 1 (by rfl) ⟨2334455, by rfl⟩ : syracuseStep 3112607 = 4668911) B4668911
theorem B2075071 : Blo 2073435 2075071 := bstep (se 1 (by rfl) ⟨1556303, by rfl⟩ : syracuseStep 2075071 = 3112607) B3112607
theorem B3112613 : Blo 2073435 3112613 := bbase (se 4 (by rfl) ⟨291807, by rfl⟩ : syracuseStep 3112613 = 583615) (by norm_num)
theorem B2075075 : Blo 2073435 2075075 := bstep (se 1 (by rfl) ⟨1556306, by rfl⟩ : syracuseStep 2075075 = 3112613) B3112613
theorem B2626273 : Blo 2073435 2626273 := bbase (se 2 (by rfl) ⟨984852, by rfl⟩ : syracuseStep 2626273 = 1969705) (by norm_num)
theorem B3501697 : Blo 2073435 3501697 := bstep (se 2 (by rfl) ⟨1313136, by rfl⟩ : syracuseStep 3501697 = 2626273) B2626273
theorem B4668929 : Blo 2073435 4668929 := bstep (se 2 (by rfl) ⟨1750848, by rfl⟩ : syracuseStep 4668929 = 3501697) B3501697
theorem B3112619 : Blo 2073435 3112619 := bstep (se 1 (by rfl) ⟨2334464, by rfl⟩ : syracuseStep 3112619 = 4668929) B4668929
theorem B2075079 : Blo 2073435 2075079 := bstep (se 1 (by rfl) ⟨1556309, by rfl⟩ : syracuseStep 2075079 = 3112619) B3112619
theorem B2334469 : Blo 2073435 2334469 := bbase (se 4 (by rfl) ⟨218856, by rfl⟩ : syracuseStep 2334469 = 437713) (by norm_num)
theorem B3112625 : Blo 2073435 3112625 := bstep (se 2 (by rfl) ⟨1167234, by rfl⟩ : syracuseStep 3112625 = 2334469) B2334469
theorem B2075083 : Blo 2073435 2075083 := bstep (se 1 (by rfl) ⟨1556312, by rfl⟩ : syracuseStep 2075083 = 3112625) B3112625
theorem B4985837 : Blo 2073435 4985837 := bbase (se 3 (by rfl) ⟨934844, by rfl⟩ : syracuseStep 4985837 = 1869689) (by norm_num)
theorem B3323891 : Blo 2073435 3323891 := bstep (se 1 (by rfl) ⟨2492918, by rfl⟩ : syracuseStep 3323891 = 4985837) B4985837
theorem B2215927 : Blo 2073435 2215927 := bstep (se 1 (by rfl) ⟨1661945, by rfl⟩ : syracuseStep 2215927 = 3323891) B3323891
theorem B2954569 : Blo 2073435 2954569 := bstep (se 2 (by rfl) ⟨1107963, by rfl⟩ : syracuseStep 2954569 = 2215927) B2215927
theorem B3939425 : Blo 2073435 3939425 := bstep (se 2 (by rfl) ⟨1477284, by rfl⟩ : syracuseStep 3939425 = 2954569) B2954569
theorem B2626283 : Blo 2073435 2626283 := bstep (se 1 (by rfl) ⟨1969712, by rfl⟩ : syracuseStep 2626283 = 3939425) B3939425
theorem B7003421 : Blo 2073435 7003421 := bstep (se 3 (by rfl) ⟨1313141, by rfl⟩ : syracuseStep 7003421 = 2626283) B2626283
theorem B4668947 : Blo 2073435 4668947 := bstep (se 1 (by rfl) ⟨3501710, by rfl⟩ : syracuseStep 4668947 = 7003421) B7003421
theorem B3112631 : Blo 2073435 3112631 := bstep (se 1 (by rfl) ⟨2334473, by rfl⟩ : syracuseStep 3112631 = 4668947) B4668947
theorem B2075087 : Blo 2073435 2075087 := bstep (se 1 (by rfl) ⟨1556315, by rfl⟩ : syracuseStep 2075087 = 3112631) B3112631
theorem B3112637 : Blo 2073435 3112637 := bbase (se 3 (by rfl) ⟨583619, by rfl⟩ : syracuseStep 3112637 = 1167239) (by norm_num)
theorem B2075091 : Blo 2073435 2075091 := bstep (se 1 (by rfl) ⟨1556318, by rfl⟩ : syracuseStep 2075091 = 3112637) B3112637
theorem B4668965 : Blo 2073435 4668965 := bbase (se 4 (by rfl) ⟨437715, by rfl⟩ : syracuseStep 4668965 = 875431) (by norm_num)
theorem B3112643 : Blo 2073435 3112643 := bstep (se 1 (by rfl) ⟨2334482, by rfl⟩ : syracuseStep 3112643 = 4668965) B4668965
theorem B2075095 : Blo 2073435 2075095 := bstep (se 1 (by rfl) ⟨1556321, by rfl⟩ : syracuseStep 2075095 = 3112643) B3112643
theorem B5252597 : Blo 2073435 5252597 := bbase (se 5 (by rfl) ⟨246215, by rfl⟩ : syracuseStep 5252597 = 492431) (by norm_num)
theorem B3501731 : Blo 2073435 3501731 := bstep (se 1 (by rfl) ⟨2626298, by rfl⟩ : syracuseStep 3501731 = 5252597) B5252597
theorem B2334487 : Blo 2073435 2334487 := bstep (se 1 (by rfl) ⟨1750865, by rfl⟩ : syracuseStep 2334487 = 3501731) B3501731
theorem B3112649 : Blo 2073435 3112649 := bstep (se 2 (by rfl) ⟨1167243, by rfl⟩ : syracuseStep 3112649 = 2334487) B2334487
theorem B2075099 : Blo 2073435 2075099 := bstep (se 1 (by rfl) ⟨1556324, by rfl⟩ : syracuseStep 2075099 = 3112649) B3112649
theorem B2526949 : Blo 2073435 2526949 := bbase (se 4 (by rfl) ⟨236901, by rfl⟩ : syracuseStep 2526949 = 473803) (by norm_num)
theorem B13477061 : Blo 2073435 13477061 := bstep (se 4 (by rfl) ⟨1263474, by rfl⟩ : syracuseStep 13477061 = 2526949) B2526949
theorem B35938829 : Blo 2073435 35938829 := bstep (se 3 (by rfl) ⟨6738530, by rfl⟩ : syracuseStep 35938829 = 13477061) B13477061
theorem B95836877 : Blo 2073435 95836877 := bstep (se 3 (by rfl) ⟨17969414, by rfl⟩ : syracuseStep 95836877 = 35938829) B35938829
theorem B63891251 : Blo 2073435 63891251 := bstep (se 1 (by rfl) ⟨47918438, by rfl⟩ : syracuseStep 63891251 = 95836877) B95836877
theorem B42594167 : Blo 2073435 42594167 := bstep (se 1 (by rfl) ⟨31945625, by rfl⟩ : syracuseStep 42594167 = 63891251) B63891251
theorem B28396111 : Blo 2073435 28396111 := bstep (se 1 (by rfl) ⟨21297083, by rfl⟩ : syracuseStep 28396111 = 42594167) B42594167
theorem B37861481 : Blo 2073435 37861481 := bstep (se 2 (by rfl) ⟨14198055, by rfl⟩ : syracuseStep 37861481 = 28396111) B28396111
theorem B25240987 : Blo 2073435 25240987 := bstep (se 1 (by rfl) ⟨18930740, by rfl⟩ : syracuseStep 25240987 = 37861481) B37861481
theorem B33654649 : Blo 2073435 33654649 := bstep (se 2 (by rfl) ⟨12620493, by rfl⟩ : syracuseStep 33654649 = 25240987) B25240987
theorem B44872865 : Blo 2073435 44872865 := bstep (se 2 (by rfl) ⟨16827324, by rfl⟩ : syracuseStep 44872865 = 33654649) B33654649
theorem B29915243 : Blo 2073435 29915243 := bstep (se 1 (by rfl) ⟨22436432, by rfl⟩ : syracuseStep 29915243 = 44872865) B44872865
theorem B19943495 : Blo 2073435 19943495 := bstep (se 1 (by rfl) ⟨14957621, by rfl⟩ : syracuseStep 19943495 = 29915243) B29915243
theorem B13295663 : Blo 2073435 13295663 := bstep (se 1 (by rfl) ⟨9971747, by rfl⟩ : syracuseStep 13295663 = 19943495) B19943495
theorem B8863775 : Blo 2073435 8863775 := bstep (se 1 (by rfl) ⟨6647831, by rfl⟩ : syracuseStep 8863775 = 13295663) B13295663
theorem B5909183 : Blo 2073435 5909183 := bstep (se 1 (by rfl) ⟨4431887, by rfl⟩ : syracuseStep 5909183 = 8863775) B8863775
theorem B3939455 : Blo 2073435 3939455 := bstep (se 1 (by rfl) ⟨2954591, by rfl⟩ : syracuseStep 3939455 = 5909183) B5909183
theorem B10505213 : Blo 2073435 10505213 := bstep (se 3 (by rfl) ⟨1969727, by rfl⟩ : syracuseStep 10505213 = 3939455) B3939455
theorem B7003475 : Blo 2073435 7003475 := bstep (se 1 (by rfl) ⟨5252606, by rfl⟩ : syracuseStep 7003475 = 10505213) B10505213
theorem B4668983 : Blo 2073435 4668983 := bstep (se 1 (by rfl) ⟨3501737, by rfl⟩ : syracuseStep 4668983 = 7003475) B7003475
theorem B3112655 : Blo 2073435 3112655 := bstep (se 1 (by rfl) ⟨2334491, by rfl⟩ : syracuseStep 3112655 = 4668983) B4668983
theorem B2075103 : Blo 2073435 2075103 := bstep (se 1 (by rfl) ⟨1556327, by rfl⟩ : syracuseStep 2075103 = 3112655) B3112655
theorem B3112661 : Blo 2073435 3112661 := bbase (se 7 (by rfl) ⟨36476, by rfl⟩ : syracuseStep 3112661 = 72953) (by norm_num)
theorem B2075107 : Blo 2073435 2075107 := bstep (se 1 (by rfl) ⟨1556330, by rfl⟩ : syracuseStep 2075107 = 3112661) B3112661
theorem B3739421 : Blo 2073435 3739421 := bbase (se 3 (by rfl) ⟨701141, by rfl⟩ : syracuseStep 3739421 = 1402283) (by norm_num)
theorem B2492947 : Blo 2073435 2492947 := bstep (se 1 (by rfl) ⟨1869710, by rfl⟩ : syracuseStep 2492947 = 3739421) B3739421
theorem B3323929 : Blo 2073435 3323929 := bstep (se 2 (by rfl) ⟨1246473, by rfl⟩ : syracuseStep 3323929 = 2492947) B2492947
theorem B4431905 : Blo 2073435 4431905 := bstep (se 2 (by rfl) ⟨1661964, by rfl⟩ : syracuseStep 4431905 = 3323929) B3323929
theorem B2954603 : Blo 2073435 2954603 := bstep (se 1 (by rfl) ⟨2215952, by rfl⟩ : syracuseStep 2954603 = 4431905) B4431905
theorem B7878941 : Blo 2073435 7878941 := bstep (se 3 (by rfl) ⟨1477301, by rfl⟩ : syracuseStep 7878941 = 2954603) B2954603
theorem B5252627 : Blo 2073435 5252627 := bstep (se 1 (by rfl) ⟨3939470, by rfl⟩ : syracuseStep 5252627 = 7878941) B7878941
theorem B3501751 : Blo 2073435 3501751 := bstep (se 1 (by rfl) ⟨2626313, by rfl⟩ : syracuseStep 3501751 = 5252627) B5252627
theorem B4669001 : Blo 2073435 4669001 := bstep (se 2 (by rfl) ⟨1750875, by rfl⟩ : syracuseStep 4669001 = 3501751) B3501751
theorem B3112667 : Blo 2073435 3112667 := bstep (se 1 (by rfl) ⟨2334500, by rfl⟩ : syracuseStep 3112667 = 4669001) B4669001
theorem B2075111 : Blo 2073435 2075111 := bstep (se 1 (by rfl) ⟨1556333, by rfl⟩ : syracuseStep 2075111 = 3112667) B3112667
theorem B2334505 : Blo 2073435 2334505 := bbase (se 2 (by rfl) ⟨875439, by rfl⟩ : syracuseStep 2334505 = 1750879) (by norm_num)
theorem B3112673 : Blo 2073435 3112673 := bstep (se 2 (by rfl) ⟨1167252, by rfl⟩ : syracuseStep 3112673 = 2334505) B2334505
theorem B2075115 : Blo 2073435 2075115 := bstep (se 1 (by rfl) ⟨1556336, by rfl⟩ : syracuseStep 2075115 = 3112673) B3112673
theorem B13295765 : Blo 2073435 13295765 := bbase (se 6 (by rfl) ⟨311619, by rfl⟩ : syracuseStep 13295765 = 623239) (by norm_num)
theorem B8863843 : Blo 2073435 8863843 := bstep (se 1 (by rfl) ⟨6647882, by rfl⟩ : syracuseStep 8863843 = 13295765) B13295765
theorem B11818457 : Blo 2073435 11818457 := bstep (se 2 (by rfl) ⟨4431921, by rfl⟩ : syracuseStep 11818457 = 8863843) B8863843
theorem B7878971 : Blo 2073435 7878971 := bstep (se 1 (by rfl) ⟨5909228, by rfl⟩ : syracuseStep 7878971 = 11818457) B11818457
theorem B5252647 : Blo 2073435 5252647 := bstep (se 1 (by rfl) ⟨3939485, by rfl⟩ : syracuseStep 5252647 = 7878971) B7878971
theorem B7003529 : Blo 2073435 7003529 := bstep (se 2 (by rfl) ⟨2626323, by rfl⟩ : syracuseStep 7003529 = 5252647) B5252647
theorem B4669019 : Blo 2073435 4669019 := bstep (se 1 (by rfl) ⟨3501764, by rfl⟩ : syracuseStep 4669019 = 7003529) B7003529
theorem B3112679 : Blo 2073435 3112679 := bstep (se 1 (by rfl) ⟨2334509, by rfl⟩ : syracuseStep 3112679 = 4669019) B4669019
theorem B2075119 : Blo 2073435 2075119 := bstep (se 1 (by rfl) ⟨1556339, by rfl⟩ : syracuseStep 2075119 = 3112679) B3112679
theorem B3112685 : Blo 2073435 3112685 := bbase (se 3 (by rfl) ⟨583628, by rfl⟩ : syracuseStep 3112685 = 1167257) (by norm_num)
theorem B2075123 : Blo 2073435 2075123 := bstep (se 1 (by rfl) ⟨1556342, by rfl⟩ : syracuseStep 2075123 = 3112685) B3112685
theorem B4669037 : Blo 2073435 4669037 := bbase (se 3 (by rfl) ⟨875444, by rfl⟩ : syracuseStep 4669037 = 1750889) (by norm_num)
theorem B3112691 : Blo 2073435 3112691 := bstep (se 1 (by rfl) ⟨2334518, by rfl⟩ : syracuseStep 3112691 = 4669037) B4669037
theorem B2075127 : Blo 2073435 2075127 := bstep (se 1 (by rfl) ⟨1556345, by rfl⟩ : syracuseStep 2075127 = 3112691) B3112691
theorem B3939509 : Blo 2073435 3939509 := bbase (se 5 (by rfl) ⟨184664, by rfl⟩ : syracuseStep 3939509 = 369329) (by norm_num)
theorem B2626339 : Blo 2073435 2626339 := bstep (se 1 (by rfl) ⟨1969754, by rfl⟩ : syracuseStep 2626339 = 3939509) B3939509
theorem B3501785 : Blo 2073435 3501785 := bstep (se 2 (by rfl) ⟨1313169, by rfl⟩ : syracuseStep 3501785 = 2626339) B2626339
theorem B2334523 : Blo 2073435 2334523 := bstep (se 1 (by rfl) ⟨1750892, by rfl⟩ : syracuseStep 2334523 = 3501785) B3501785
theorem B3112697 : Blo 2073435 3112697 := bstep (se 2 (by rfl) ⟨1167261, by rfl⟩ : syracuseStep 3112697 = 2334523) B2334523
theorem B2075131 : Blo 2073435 2075131 := bstep (se 1 (by rfl) ⟨1556348, by rfl⟩ : syracuseStep 2075131 = 3112697) B3112697
theorem B2276857 : Blo 2073435 2276857 := bbase (se 2 (by rfl) ⟨853821, by rfl⟩ : syracuseStep 2276857 = 1707643) (by norm_num)
theorem B3035809 : Blo 2073435 3035809 := bstep (se 2 (by rfl) ⟨1138428, by rfl⟩ : syracuseStep 3035809 = 2276857) B2276857
theorem B16190981 : Blo 2073435 16190981 := bstep (se 4 (by rfl) ⟨1517904, by rfl⟩ : syracuseStep 16190981 = 3035809) B3035809
theorem B10793987 : Blo 2073435 10793987 := bstep (se 1 (by rfl) ⟨8095490, by rfl⟩ : syracuseStep 10793987 = 16190981) B16190981
theorem B460543445 : Blo 2073435 460543445 := bstep (se 7 (by rfl) ⟨5396993, by rfl⟩ : syracuseStep 460543445 = 10793987) B10793987
theorem B307028963 : Blo 2073435 307028963 := bstep (se 1 (by rfl) ⟨230271722, by rfl⟩ : syracuseStep 307028963 = 460543445) B460543445
theorem B204685975 : Blo 2073435 204685975 := bstep (se 1 (by rfl) ⟨153514481, by rfl⟩ : syracuseStep 204685975 = 307028963) B307028963
theorem B272914633 : Blo 2073435 272914633 := bstep (se 2 (by rfl) ⟨102342987, by rfl⟩ : syracuseStep 272914633 = 204685975) B204685975
theorem B363886177 : Blo 2073435 363886177 := bstep (se 2 (by rfl) ⟨136457316, by rfl⟩ : syracuseStep 363886177 = 272914633) B272914633
theorem B485181569 : Blo 2073435 485181569 := bstep (se 2 (by rfl) ⟨181943088, by rfl⟩ : syracuseStep 485181569 = 363886177) B363886177
theorem B323454379 : Blo 2073435 323454379 := bstep (se 1 (by rfl) ⟨242590784, by rfl⟩ : syracuseStep 323454379 = 485181569) B485181569
theorem B431272505 : Blo 2073435 431272505 := bstep (se 2 (by rfl) ⟨161727189, by rfl⟩ : syracuseStep 431272505 = 323454379) B323454379
theorem B287515003 : Blo 2073435 287515003 := bstep (se 1 (by rfl) ⟨215636252, by rfl⟩ : syracuseStep 287515003 = 431272505) B431272505
theorem B383353337 : Blo 2073435 383353337 := bstep (se 2 (by rfl) ⟨143757501, by rfl⟩ : syracuseStep 383353337 = 287515003) B287515003
theorem B255568891 : Blo 2073435 255568891 := bstep (se 1 (by rfl) ⟨191676668, by rfl⟩ : syracuseStep 255568891 = 383353337) B383353337
theorem B340758521 : Blo 2073435 340758521 := bstep (se 2 (by rfl) ⟨127784445, by rfl⟩ : syracuseStep 340758521 = 255568891) B255568891
theorem B227172347 : Blo 2073435 227172347 := bstep (se 1 (by rfl) ⟨170379260, by rfl⟩ : syracuseStep 227172347 = 340758521) B340758521
theorem B151448231 : Blo 2073435 151448231 := bstep (se 1 (by rfl) ⟨113586173, by rfl⟩ : syracuseStep 151448231 = 227172347) B227172347
theorem B100965487 : Blo 2073435 100965487 := bstep (se 1 (by rfl) ⟨75724115, by rfl⟩ : syracuseStep 100965487 = 151448231) B151448231
theorem B134620649 : Blo 2073435 134620649 := bstep (se 2 (by rfl) ⟨50482743, by rfl⟩ : syracuseStep 134620649 = 100965487) B100965487
theorem B89747099 : Blo 2073435 89747099 := bstep (se 1 (by rfl) ⟨67310324, by rfl⟩ : syracuseStep 89747099 = 134620649) B134620649
theorem B59831399 : Blo 2073435 59831399 := bstep (se 1 (by rfl) ⟨44873549, by rfl⟩ : syracuseStep 59831399 = 89747099) B89747099
theorem B39887599 : Blo 2073435 39887599 := bstep (se 1 (by rfl) ⟨29915699, by rfl⟩ : syracuseStep 39887599 = 59831399) B59831399
theorem B53183465 : Blo 2073435 53183465 := bstep (se 2 (by rfl) ⟨19943799, by rfl⟩ : syracuseStep 53183465 = 39887599) B39887599
theorem B35455643 : Blo 2073435 35455643 := bstep (se 1 (by rfl) ⟨26591732, by rfl⟩ : syracuseStep 35455643 = 53183465) B53183465
theorem B23637095 : Blo 2073435 23637095 := bstep (se 1 (by rfl) ⟨17727821, by rfl⟩ : syracuseStep 23637095 = 35455643) B35455643
theorem B15758063 : Blo 2073435 15758063 := bstep (se 1 (by rfl) ⟨11818547, by rfl⟩ : syracuseStep 15758063 = 23637095) B23637095
theorem B10505375 : Blo 2073435 10505375 := bstep (se 1 (by rfl) ⟨7879031, by rfl⟩ : syracuseStep 10505375 = 15758063) B15758063
theorem B7003583 : Blo 2073435 7003583 := bstep (se 1 (by rfl) ⟨5252687, by rfl⟩ : syracuseStep 7003583 = 10505375) B10505375
theorem B4669055 : Blo 2073435 4669055 := bstep (se 1 (by rfl) ⟨3501791, by rfl⟩ : syracuseStep 4669055 = 7003583) B7003583
theorem B3112703 : Blo 2073435 3112703 := bstep (se 1 (by rfl) ⟨2334527, by rfl⟩ : syracuseStep 3112703 = 4669055) B4669055
theorem B2075135 : Blo 2073435 2075135 := bstep (se 1 (by rfl) ⟨1556351, by rfl⟩ : syracuseStep 2075135 = 3112703) B3112703
theorem B3112709 : Blo 2073435 3112709 := bbase (se 4 (by rfl) ⟨291816, by rfl⟩ : syracuseStep 3112709 = 583633) (by norm_num)
theorem B2075139 : Blo 2073435 2075139 := bstep (se 1 (by rfl) ⟨1556354, by rfl⟩ : syracuseStep 2075139 = 3112709) B3112709
theorem B3501805 : Blo 2073435 3501805 := bbase (se 3 (by rfl) ⟨656588, by rfl⟩ : syracuseStep 3501805 = 1313177) (by norm_num)
theorem B4669073 : Blo 2073435 4669073 := bstep (se 2 (by rfl) ⟨1750902, by rfl⟩ : syracuseStep 4669073 = 3501805) B3501805
theorem B3112715 : Blo 2073435 3112715 := bstep (se 1 (by rfl) ⟨2334536, by rfl⟩ : syracuseStep 3112715 = 4669073) B4669073
theorem B2075143 : Blo 2073435 2075143 := bstep (se 1 (by rfl) ⟨1556357, by rfl⟩ : syracuseStep 2075143 = 3112715) B3112715
theorem B2334541 : Blo 2073435 2334541 := bbase (se 3 (by rfl) ⟨437726, by rfl⟩ : syracuseStep 2334541 = 875453) (by norm_num)
theorem B3112721 : Blo 2073435 3112721 := bstep (se 2 (by rfl) ⟨1167270, by rfl⟩ : syracuseStep 3112721 = 2334541) B2334541
theorem B2075147 : Blo 2073435 2075147 := bstep (se 1 (by rfl) ⟨1556360, by rfl⟩ : syracuseStep 2075147 = 3112721) B3112721
theorem B7003637 : Blo 2073435 7003637 := bbase (se 5 (by rfl) ⟨328295, by rfl⟩ : syracuseStep 7003637 = 656591) (by norm_num)
theorem B4669091 : Blo 2073435 4669091 := bstep (se 1 (by rfl) ⟨3501818, by rfl⟩ : syracuseStep 4669091 = 7003637) B7003637
theorem B3112727 : Blo 2073435 3112727 := bstep (se 1 (by rfl) ⟨2334545, by rfl⟩ : syracuseStep 3112727 = 4669091) B4669091
theorem B2075151 : Blo 2073435 2075151 := bstep (se 1 (by rfl) ⟨1556363, by rfl⟩ : syracuseStep 2075151 = 3112727) B3112727
theorem B3112733 : Blo 2073435 3112733 := bbase (se 3 (by rfl) ⟨583637, by rfl⟩ : syracuseStep 3112733 = 1167275) (by norm_num)
theorem B2075155 : Blo 2073435 2075155 := bstep (se 1 (by rfl) ⟨1556366, by rfl⟩ : syracuseStep 2075155 = 3112733) B3112733
theorem B4669109 : Blo 2073435 4669109 := bbase (se 5 (by rfl) ⟨218864, by rfl⟩ : syracuseStep 4669109 = 437729) (by norm_num)
theorem B3112739 : Blo 2073435 3112739 := bstep (se 1 (by rfl) ⟨2334554, by rfl⟩ : syracuseStep 3112739 = 4669109) B4669109
theorem B2075159 : Blo 2073435 2075159 := bstep (se 1 (by rfl) ⟨1556369, by rfl⟩ : syracuseStep 2075159 = 3112739) B3112739
theorem B11818709 : Blo 2073435 11818709 := bbase (se 7 (by rfl) ⟨138500, by rfl⟩ : syracuseStep 11818709 = 277001) (by norm_num)
theorem B7879139 : Blo 2073435 7879139 := bstep (se 1 (by rfl) ⟨5909354, by rfl⟩ : syracuseStep 7879139 = 11818709) B11818709
theorem B5252759 : Blo 2073435 5252759 := bstep (se 1 (by rfl) ⟨3939569, by rfl⟩ : syracuseStep 5252759 = 7879139) B7879139
theorem B3501839 : Blo 2073435 3501839 := bstep (se 1 (by rfl) ⟨2626379, by rfl⟩ : syracuseStep 3501839 = 5252759) B5252759
theorem B2334559 : Blo 2073435 2334559 := bstep (se 1 (by rfl) ⟨1750919, by rfl⟩ : syracuseStep 2334559 = 3501839) B3501839
theorem B3112745 : Blo 2073435 3112745 := bstep (se 2 (by rfl) ⟨1167279, by rfl⟩ : syracuseStep 3112745 = 2334559) B2334559
theorem B2075163 : Blo 2073435 2075163 := bstep (se 1 (by rfl) ⟨1556372, by rfl⟩ : syracuseStep 2075163 = 3112745) B3112745
theorem B5909365 : Blo 2073435 5909365 := bbase (se 5 (by rfl) ⟨277001, by rfl⟩ : syracuseStep 5909365 = 554003) (by norm_num)
theorem B7879153 : Blo 2073435 7879153 := bstep (se 2 (by rfl) ⟨2954682, by rfl⟩ : syracuseStep 7879153 = 5909365) B5909365
theorem B10505537 : Blo 2073435 10505537 := bstep (se 2 (by rfl) ⟨3939576, by rfl⟩ : syracuseStep 10505537 = 7879153) B7879153
theorem B7003691 : Blo 2073435 7003691 := bstep (se 1 (by rfl) ⟨5252768, by rfl⟩ : syracuseStep 7003691 = 10505537) B10505537
theorem B4669127 : Blo 2073435 4669127 := bstep (se 1 (by rfl) ⟨3501845, by rfl⟩ : syracuseStep 4669127 = 7003691) B7003691
theorem B3112751 : Blo 2073435 3112751 := bstep (se 1 (by rfl) ⟨2334563, by rfl⟩ : syracuseStep 3112751 = 4669127) B4669127
theorem B2075167 : Blo 2073435 2075167 := bstep (se 1 (by rfl) ⟨1556375, by rfl⟩ : syracuseStep 2075167 = 3112751) B3112751
theorem B3112757 : Blo 2073435 3112757 := bbase (se 5 (by rfl) ⟨145910, by rfl⟩ : syracuseStep 3112757 = 291821) (by norm_num)
theorem B2075171 : Blo 2073435 2075171 := bstep (se 1 (by rfl) ⟨1556378, by rfl⟩ : syracuseStep 2075171 = 3112757) B3112757
theorem B5252789 : Blo 2073435 5252789 := bbase (se 5 (by rfl) ⟨246224, by rfl⟩ : syracuseStep 5252789 = 492449) (by norm_num)
theorem B3501859 : Blo 2073435 3501859 := bstep (se 1 (by rfl) ⟨2626394, by rfl⟩ : syracuseStep 3501859 = 5252789) B5252789
theorem B4669145 : Blo 2073435 4669145 := bstep (se 2 (by rfl) ⟨1750929, by rfl⟩ : syracuseStep 4669145 = 3501859) B3501859
theorem B3112763 : Blo 2073435 3112763 := bstep (se 1 (by rfl) ⟨2334572, by rfl⟩ : syracuseStep 3112763 = 4669145) B4669145
theorem B2075175 : Blo 2073435 2075175 := bstep (se 1 (by rfl) ⟨1556381, by rfl⟩ : syracuseStep 2075175 = 3112763) B3112763
theorem B2334577 : Blo 2073435 2334577 := bbase (se 2 (by rfl) ⟨875466, by rfl⟩ : syracuseStep 2334577 = 1750933) (by norm_num)
theorem B3112769 : Blo 2073435 3112769 := bstep (se 2 (by rfl) ⟨1167288, by rfl⟩ : syracuseStep 3112769 = 2334577) B2334577
theorem B2075179 : Blo 2073435 2075179 := bstep (se 1 (by rfl) ⟨1556384, by rfl⟩ : syracuseStep 2075179 = 3112769) B3112769
theorem B8864117 : Blo 2073435 8864117 := bbase (se 5 (by rfl) ⟨415505, by rfl⟩ : syracuseStep 8864117 = 831011) (by norm_num)
theorem B5909411 : Blo 2073435 5909411 := bstep (se 1 (by rfl) ⟨4432058, by rfl⟩ : syracuseStep 5909411 = 8864117) B8864117
theorem B3939607 : Blo 2073435 3939607 := bstep (se 1 (by rfl) ⟨2954705, by rfl⟩ : syracuseStep 3939607 = 5909411) B5909411
theorem B5252809 : Blo 2073435 5252809 := bstep (se 2 (by rfl) ⟨1969803, by rfl⟩ : syracuseStep 5252809 = 3939607) B3939607
theorem B7003745 : Blo 2073435 7003745 := bstep (se 2 (by rfl) ⟨2626404, by rfl⟩ : syracuseStep 7003745 = 5252809) B5252809
theorem B4669163 : Blo 2073435 4669163 := bstep (se 1 (by rfl) ⟨3501872, by rfl⟩ : syracuseStep 4669163 = 7003745) B7003745
theorem B3112775 : Blo 2073435 3112775 := bstep (se 1 (by rfl) ⟨2334581, by rfl⟩ : syracuseStep 3112775 = 4669163) B4669163
theorem B2075183 : Blo 2073435 2075183 := bstep (se 1 (by rfl) ⟨1556387, by rfl⟩ : syracuseStep 2075183 = 3112775) B3112775
theorem B3112781 : Blo 2073435 3112781 := bbase (se 3 (by rfl) ⟨583646, by rfl⟩ : syracuseStep 3112781 = 1167293) (by norm_num)
theorem B2075187 : Blo 2073435 2075187 := bstep (se 1 (by rfl) ⟨1556390, by rfl⟩ : syracuseStep 2075187 = 3112781) B3112781
theorem B4669181 : Blo 2073435 4669181 := bbase (se 3 (by rfl) ⟨875471, by rfl⟩ : syracuseStep 4669181 = 1750943) (by norm_num)
theorem B3112787 : Blo 2073435 3112787 := bstep (se 1 (by rfl) ⟨2334590, by rfl⟩ : syracuseStep 3112787 = 4669181) B4669181
theorem B2075191 : Blo 2073435 2075191 := bstep (se 1 (by rfl) ⟨1556393, by rfl⟩ : syracuseStep 2075191 = 3112787) B3112787
theorem B3501893 : Blo 2073435 3501893 := bbase (se 4 (by rfl) ⟨328302, by rfl⟩ : syracuseStep 3501893 = 656605) (by norm_num)
theorem B2334595 : Blo 2073435 2334595 := bstep (se 1 (by rfl) ⟨1750946, by rfl⟩ : syracuseStep 2334595 = 3501893) B3501893
theorem B3112793 : Blo 2073435 3112793 := bstep (se 2 (by rfl) ⟨1167297, by rfl⟩ : syracuseStep 3112793 = 2334595) B2334595
theorem B2075195 : Blo 2073435 2075195 := bstep (se 1 (by rfl) ⟨1556396, by rfl⟩ : syracuseStep 2075195 = 3112793) B3112793
theorem B15758549 : Blo 2073435 15758549 := bbase (se 7 (by rfl) ⟨184670, by rfl⟩ : syracuseStep 15758549 = 369341) (by norm_num)
theorem B10505699 : Blo 2073435 10505699 := bstep (se 1 (by rfl) ⟨7879274, by rfl⟩ : syracuseStep 10505699 = 15758549) B15758549
theorem B7003799 : Blo 2073435 7003799 := bstep (se 1 (by rfl) ⟨5252849, by rfl⟩ : syracuseStep 7003799 = 10505699) B10505699
theorem B4669199 : Blo 2073435 4669199 := bstep (se 1 (by rfl) ⟨3501899, by rfl⟩ : syracuseStep 4669199 = 7003799) B7003799
theorem B3112799 : Blo 2073435 3112799 := bstep (se 1 (by rfl) ⟨2334599, by rfl⟩ : syracuseStep 3112799 = 4669199) B4669199
theorem B2075199 : Blo 2073435 2075199 := bstep (se 1 (by rfl) ⟨1556399, by rfl⟩ : syracuseStep 2075199 = 3112799) B3112799
theorem B3112805 : Blo 2073435 3112805 := bbase (se 4 (by rfl) ⟨291825, by rfl⟩ : syracuseStep 3112805 = 583651) (by norm_num)
theorem B2075203 : Blo 2073435 2075203 := bstep (se 1 (by rfl) ⟨1556402, by rfl⟩ : syracuseStep 2075203 = 3112805) B3112805
theorem B3939653 : Blo 2073435 3939653 := bbase (se 4 (by rfl) ⟨369342, by rfl⟩ : syracuseStep 3939653 = 738685) (by norm_num)
theorem B2626435 : Blo 2073435 2626435 := bstep (se 1 (by rfl) ⟨1969826, by rfl⟩ : syracuseStep 2626435 = 3939653) B3939653
theorem B3501913 : Blo 2073435 3501913 := bstep (se 2 (by rfl) ⟨1313217, by rfl⟩ : syracuseStep 3501913 = 2626435) B2626435
theorem B4669217 : Blo 2073435 4669217 := bstep (se 2 (by rfl) ⟨1750956, by rfl⟩ : syracuseStep 4669217 = 3501913) B3501913
theorem B3112811 : Blo 2073435 3112811 := bstep (se 1 (by rfl) ⟨2334608, by rfl⟩ : syracuseStep 3112811 = 4669217) B4669217
theorem B2075207 : Blo 2073435 2075207 := bstep (se 1 (by rfl) ⟨1556405, by rfl⟩ : syracuseStep 2075207 = 3112811) B3112811
theorem B2334613 : Blo 2073435 2334613 := bbase (se 6 (by rfl) ⟨54717, by rfl⟩ : syracuseStep 2334613 = 109435) (by norm_num)
theorem B3112817 : Blo 2073435 3112817 := bstep (se 2 (by rfl) ⟨1167306, by rfl⟩ : syracuseStep 3112817 = 2334613) B2334613
theorem B2075211 : Blo 2073435 2075211 := bstep (se 1 (by rfl) ⟨1556408, by rfl⟩ : syracuseStep 2075211 = 3112817) B3112817
theorem B2626445 : Blo 2073435 2626445 := bbase (se 3 (by rfl) ⟨492458, by rfl⟩ : syracuseStep 2626445 = 984917) (by norm_num)
theorem B7003853 : Blo 2073435 7003853 := bstep (se 3 (by rfl) ⟨1313222, by rfl⟩ : syracuseStep 7003853 = 2626445) B2626445
theorem B4669235 : Blo 2073435 4669235 := bstep (se 1 (by rfl) ⟨3501926, by rfl⟩ : syracuseStep 4669235 = 7003853) B7003853
theorem B3112823 : Blo 2073435 3112823 := bstep (se 1 (by rfl) ⟨2334617, by rfl⟩ : syracuseStep 3112823 = 4669235) B4669235
theorem B2075215 : Blo 2073435 2075215 := bstep (se 1 (by rfl) ⟨1556411, by rfl⟩ : syracuseStep 2075215 = 3112823) B3112823
theorem B3112829 : Blo 2073435 3112829 := bbase (se 3 (by rfl) ⟨583655, by rfl⟩ : syracuseStep 3112829 = 1167311) (by norm_num)
theorem B2075219 : Blo 2073435 2075219 := bstep (se 1 (by rfl) ⟨1556414, by rfl⟩ : syracuseStep 2075219 = 3112829) B3112829
theorem B4669253 : Blo 2073435 4669253 := bbase (se 4 (by rfl) ⟨437742, by rfl⟩ : syracuseStep 4669253 = 875485) (by norm_num)
theorem B3112835 : Blo 2073435 3112835 := bstep (se 1 (by rfl) ⟨2334626, by rfl⟩ : syracuseStep 3112835 = 4669253) B4669253
theorem B2075223 : Blo 2073435 2075223 := bstep (se 1 (by rfl) ⟨1556417, by rfl⟩ : syracuseStep 2075223 = 3112835) B3112835
theorem B4986173 : Blo 2073435 4986173 := bbase (se 3 (by rfl) ⟨934907, by rfl⟩ : syracuseStep 4986173 = 1869815) (by norm_num)
theorem B3324115 : Blo 2073435 3324115 := bstep (se 1 (by rfl) ⟨2493086, by rfl⟩ : syracuseStep 3324115 = 4986173) B4986173
theorem B4432153 : Blo 2073435 4432153 := bstep (se 2 (by rfl) ⟨1662057, by rfl⟩ : syracuseStep 4432153 = 3324115) B3324115
theorem B5909537 : Blo 2073435 5909537 := bstep (se 2 (by rfl) ⟨2216076, by rfl⟩ : syracuseStep 5909537 = 4432153) B4432153
theorem B3939691 : Blo 2073435 3939691 := bstep (se 1 (by rfl) ⟨2954768, by rfl⟩ : syracuseStep 3939691 = 5909537) B5909537
theorem B5252921 : Blo 2073435 5252921 := bstep (se 2 (by rfl) ⟨1969845, by rfl⟩ : syracuseStep 5252921 = 3939691) B3939691
theorem B3501947 : Blo 2073435 3501947 := bstep (se 1 (by rfl) ⟨2626460, by rfl⟩ : syracuseStep 3501947 = 5252921) B5252921
theorem B2334631 : Blo 2073435 2334631 := bstep (se 1 (by rfl) ⟨1750973, by rfl⟩ : syracuseStep 2334631 = 3501947) B3501947
theorem B3112841 : Blo 2073435 3112841 := bstep (se 2 (by rfl) ⟨1167315, by rfl⟩ : syracuseStep 3112841 = 2334631) B2334631
theorem B2075227 : Blo 2073435 2075227 := bstep (se 1 (by rfl) ⟨1556420, by rfl⟩ : syracuseStep 2075227 = 3112841) B3112841
theorem B10505861 : Blo 2073435 10505861 := bbase (se 4 (by rfl) ⟨984924, by rfl⟩ : syracuseStep 10505861 = 1969849) (by norm_num)
theorem B7003907 : Blo 2073435 7003907 := bstep (se 1 (by rfl) ⟨5252930, by rfl⟩ : syracuseStep 7003907 = 10505861) B10505861
theorem B4669271 : Blo 2073435 4669271 := bstep (se 1 (by rfl) ⟨3501953, by rfl⟩ : syracuseStep 4669271 = 7003907) B7003907
theorem B3112847 : Blo 2073435 3112847 := bstep (se 1 (by rfl) ⟨2334635, by rfl⟩ : syracuseStep 3112847 = 4669271) B4669271
theorem B2075231 : Blo 2073435 2075231 := bstep (se 1 (by rfl) ⟨1556423, by rfl⟩ : syracuseStep 2075231 = 3112847) B3112847
theorem B3112853 : Blo 2073435 3112853 := bbase (se 6 (by rfl) ⟨72957, by rfl⟩ : syracuseStep 3112853 = 145915) (by norm_num)
theorem B2075235 : Blo 2073435 2075235 := bstep (se 1 (by rfl) ⟨1556426, by rfl⟩ : syracuseStep 2075235 = 3112853) B3112853
theorem B2216089 : Blo 2073435 2216089 := bbase (se 2 (by rfl) ⟨831033, by rfl⟩ : syracuseStep 2216089 = 1662067) (by norm_num)
theorem B11819141 : Blo 2073435 11819141 := bstep (se 4 (by rfl) ⟨1108044, by rfl⟩ : syracuseStep 11819141 = 2216089) B2216089
theorem B7879427 : Blo 2073435 7879427 := bstep (se 1 (by rfl) ⟨5909570, by rfl⟩ : syracuseStep 7879427 = 11819141) B11819141
theorem B5252951 : Blo 2073435 5252951 := bstep (se 1 (by rfl) ⟨3939713, by rfl⟩ : syracuseStep 5252951 = 7879427) B7879427
theorem B3501967 : Blo 2073435 3501967 := bstep (se 1 (by rfl) ⟨2626475, by rfl⟩ : syracuseStep 3501967 = 5252951) B5252951
theorem B4669289 : Blo 2073435 4669289 := bstep (se 2 (by rfl) ⟨1750983, by rfl⟩ : syracuseStep 4669289 = 3501967) B3501967
theorem B3112859 : Blo 2073435 3112859 := bstep (se 1 (by rfl) ⟨2334644, by rfl⟩ : syracuseStep 3112859 = 4669289) B4669289
theorem B2075239 : Blo 2073435 2075239 := bstep (se 1 (by rfl) ⟨1556429, by rfl⟩ : syracuseStep 2075239 = 3112859) B3112859
theorem B2334649 : Blo 2073435 2334649 := bbase (se 2 (by rfl) ⟨875493, by rfl⟩ : syracuseStep 2334649 = 1750987) (by norm_num)
theorem B3112865 : Blo 2073435 3112865 := bstep (se 2 (by rfl) ⟨1167324, by rfl⟩ : syracuseStep 3112865 = 2334649) B2334649
theorem B2075243 : Blo 2073435 2075243 := bstep (se 1 (by rfl) ⟨1556432, by rfl⟩ : syracuseStep 2075243 = 3112865) B3112865
theorem B6648293 : Blo 2073435 6648293 := bbase (se 4 (by rfl) ⟨623277, by rfl⟩ : syracuseStep 6648293 = 1246555) (by norm_num)
theorem B4432195 : Blo 2073435 4432195 := bstep (se 1 (by rfl) ⟨3324146, by rfl⟩ : syracuseStep 4432195 = 6648293) B6648293
theorem B5909593 : Blo 2073435 5909593 := bstep (se 2 (by rfl) ⟨2216097, by rfl⟩ : syracuseStep 5909593 = 4432195) B4432195
theorem B7879457 : Blo 2073435 7879457 := bstep (se 2 (by rfl) ⟨2954796, by rfl⟩ : syracuseStep 7879457 = 5909593) B5909593
theorem B5252971 : Blo 2073435 5252971 := bstep (se 1 (by rfl) ⟨3939728, by rfl⟩ : syracuseStep 5252971 = 7879457) B7879457
theorem B7003961 : Blo 2073435 7003961 := bstep (se 2 (by rfl) ⟨2626485, by rfl⟩ : syracuseStep 7003961 = 5252971) B5252971
theorem B4669307 : Blo 2073435 4669307 := bstep (se 1 (by rfl) ⟨3501980, by rfl⟩ : syracuseStep 4669307 = 7003961) B7003961
theorem B3112871 : Blo 2073435 3112871 := bstep (se 1 (by rfl) ⟨2334653, by rfl⟩ : syracuseStep 3112871 = 4669307) B4669307
theorem B2075247 : Blo 2073435 2075247 := bstep (se 1 (by rfl) ⟨1556435, by rfl⟩ : syracuseStep 2075247 = 3112871) B3112871
theorem B3112877 : Blo 2073435 3112877 := bbase (se 3 (by rfl) ⟨583664, by rfl⟩ : syracuseStep 3112877 = 1167329) (by norm_num)
theorem B2075251 : Blo 2073435 2075251 := bstep (se 1 (by rfl) ⟨1556438, by rfl⟩ : syracuseStep 2075251 = 3112877) B3112877
theorem B4669325 : Blo 2073435 4669325 := bbase (se 3 (by rfl) ⟨875498, by rfl⟩ : syracuseStep 4669325 = 1750997) (by norm_num)
theorem B3112883 : Blo 2073435 3112883 := bstep (se 1 (by rfl) ⟨2334662, by rfl⟩ : syracuseStep 3112883 = 4669325) B4669325
theorem B2075255 : Blo 2073435 2075255 := bstep (se 1 (by rfl) ⟨1556441, by rfl⟩ : syracuseStep 2075255 = 3112883) B3112883
theorem B2626501 : Blo 2073435 2626501 := bbase (se 4 (by rfl) ⟨246234, by rfl⟩ : syracuseStep 2626501 = 492469) (by norm_num)
theorem B3502001 : Blo 2073435 3502001 := bstep (se 2 (by rfl) ⟨1313250, by rfl⟩ : syracuseStep 3502001 = 2626501) B2626501
theorem B2334667 : Blo 2073435 2334667 := bstep (se 1 (by rfl) ⟨1751000, by rfl⟩ : syracuseStep 2334667 = 3502001) B3502001
theorem B3112889 : Blo 2073435 3112889 := bstep (se 2 (by rfl) ⟨1167333, by rfl⟩ : syracuseStep 3112889 = 2334667) B2334667
theorem B2075259 : Blo 2073435 2075259 := bstep (se 1 (by rfl) ⟨1556444, by rfl⟩ : syracuseStep 2075259 = 3112889) B3112889
theorem B14958773 : Blo 2073435 14958773 := bbase (se 5 (by rfl) ⟨701192, by rfl⟩ : syracuseStep 14958773 = 1402385) (by norm_num)
theorem B9972515 : Blo 2073435 9972515 := bstep (se 1 (by rfl) ⟨7479386, by rfl⟩ : syracuseStep 9972515 = 14958773) B14958773
theorem B26593373 : Blo 2073435 26593373 := bstep (se 3 (by rfl) ⟨4986257, by rfl⟩ : syracuseStep 26593373 = 9972515) B9972515
theorem B17728915 : Blo 2073435 17728915 := bstep (se 1 (by rfl) ⟨13296686, by rfl⟩ : syracuseStep 17728915 = 26593373) B26593373
theorem B23638553 : Blo 2073435 23638553 := bstep (se 2 (by rfl) ⟨8864457, by rfl⟩ : syracuseStep 23638553 = 17728915) B17728915
theorem B15759035 : Blo 2073435 15759035 := bstep (se 1 (by rfl) ⟨11819276, by rfl⟩ : syracuseStep 15759035 = 23638553) B23638553
theorem B10506023 : Blo 2073435 10506023 := bstep (se 1 (by rfl) ⟨7879517, by rfl⟩ : syracuseStep 10506023 = 15759035) B15759035
theorem B7004015 : Blo 2073435 7004015 := bstep (se 1 (by rfl) ⟨5253011, by rfl⟩ : syracuseStep 7004015 = 10506023) B10506023
theorem B4669343 : Blo 2073435 4669343 := bstep (se 1 (by rfl) ⟨3502007, by rfl⟩ : syracuseStep 4669343 = 7004015) B7004015
theorem B3112895 : Blo 2073435 3112895 := bstep (se 1 (by rfl) ⟨2334671, by rfl⟩ : syracuseStep 3112895 = 4669343) B4669343
theorem B2075263 : Blo 2073435 2075263 := bstep (se 1 (by rfl) ⟨1556447, by rfl⟩ : syracuseStep 2075263 = 3112895) B3112895
theorem B3112901 : Blo 2073435 3112901 := bbase (se 4 (by rfl) ⟨291834, by rfl⟩ : syracuseStep 3112901 = 583669) (by norm_num)
theorem B2075267 : Blo 2073435 2075267 := bstep (se 1 (by rfl) ⟨1556450, by rfl⟩ : syracuseStep 2075267 = 3112901) B3112901
theorem B3502021 : Blo 2073435 3502021 := bbase (se 4 (by rfl) ⟨328314, by rfl⟩ : syracuseStep 3502021 = 656629) (by norm_num)
theorem B4669361 : Blo 2073435 4669361 := bstep (se 2 (by rfl) ⟨1751010, by rfl⟩ : syracuseStep 4669361 = 3502021) B3502021
theorem B3112907 : Blo 2073435 3112907 := bstep (se 1 (by rfl) ⟨2334680, by rfl⟩ : syracuseStep 3112907 = 4669361) B4669361
theorem B2075271 : Blo 2073435 2075271 := bstep (se 1 (by rfl) ⟨1556453, by rfl⟩ : syracuseStep 2075271 = 3112907) B3112907
theorem B2334685 : Blo 2073435 2334685 := bbase (se 3 (by rfl) ⟨437753, by rfl⟩ : syracuseStep 2334685 = 875507) (by norm_num)
theorem B3112913 : Blo 2073435 3112913 := bstep (se 2 (by rfl) ⟨1167342, by rfl⟩ : syracuseStep 3112913 = 2334685) B2334685
theorem B2075275 : Blo 2073435 2075275 := bstep (se 1 (by rfl) ⟨1556456, by rfl⟩ : syracuseStep 2075275 = 3112913) B3112913
theorem B7004069 : Blo 2073435 7004069 := bbase (se 4 (by rfl) ⟨656631, by rfl⟩ : syracuseStep 7004069 = 1313263) (by norm_num)
theorem B4669379 : Blo 2073435 4669379 := bstep (se 1 (by rfl) ⟨3502034, by rfl⟩ : syracuseStep 4669379 = 7004069) B7004069
theorem B3112919 : Blo 2073435 3112919 := bstep (se 1 (by rfl) ⟨2334689, by rfl⟩ : syracuseStep 3112919 = 4669379) B4669379
theorem B2075279 : Blo 2073435 2075279 := bstep (se 1 (by rfl) ⟨1556459, by rfl⟩ : syracuseStep 2075279 = 3112919) B3112919
theorem B3112925 : Blo 2073435 3112925 := bbase (se 3 (by rfl) ⟨583673, by rfl⟩ : syracuseStep 3112925 = 1167347) (by norm_num)
theorem B2075283 : Blo 2073435 2075283 := bstep (se 1 (by rfl) ⟨1556462, by rfl⟩ : syracuseStep 2075283 = 3112925) B3112925
theorem B4669397 : Blo 2073435 4669397 := bbase (se 7 (by rfl) ⟨54719, by rfl⟩ : syracuseStep 4669397 = 109439) (by norm_num)
theorem B3112931 : Blo 2073435 3112931 := bstep (se 1 (by rfl) ⟨2334698, by rfl⟩ : syracuseStep 3112931 = 4669397) B4669397
theorem B2075287 : Blo 2073435 2075287 := bstep (se 1 (by rfl) ⟨1556465, by rfl⟩ : syracuseStep 2075287 = 3112931) B3112931
theorem B4733117 : Blo 2073435 4733117 := bbase (se 3 (by rfl) ⟨887459, by rfl⟩ : syracuseStep 4733117 = 1774919) (by norm_num)
theorem B3155411 : Blo 2073435 3155411 := bstep (se 1 (by rfl) ⟨2366558, by rfl⟩ : syracuseStep 3155411 = 4733117) B4733117
theorem B2103607 : Blo 2073435 2103607 := bstep (se 1 (by rfl) ⟨1577705, by rfl⟩ : syracuseStep 2103607 = 3155411) B3155411
theorem B2804809 : Blo 2073435 2804809 := bstep (se 2 (by rfl) ⟨1051803, by rfl⟩ : syracuseStep 2804809 = 2103607) B2103607
theorem B3739745 : Blo 2073435 3739745 := bstep (se 2 (by rfl) ⟨1402404, by rfl⟩ : syracuseStep 3739745 = 2804809) B2804809
theorem B2493163 : Blo 2073435 2493163 := bstep (se 1 (by rfl) ⟨1869872, by rfl⟩ : syracuseStep 2493163 = 3739745) B3739745
theorem B13296869 : Blo 2073435 13296869 := bstep (se 4 (by rfl) ⟨1246581, by rfl⟩ : syracuseStep 13296869 = 2493163) B2493163
theorem B8864579 : Blo 2073435 8864579 := bstep (se 1 (by rfl) ⟨6648434, by rfl⟩ : syracuseStep 8864579 = 13296869) B13296869
theorem B5909719 : Blo 2073435 5909719 := bstep (se 1 (by rfl) ⟨4432289, by rfl⟩ : syracuseStep 5909719 = 8864579) B8864579
theorem B7879625 : Blo 2073435 7879625 := bstep (se 2 (by rfl) ⟨2954859, by rfl⟩ : syracuseStep 7879625 = 5909719) B5909719
theorem B5253083 : Blo 2073435 5253083 := bstep (se 1 (by rfl) ⟨3939812, by rfl⟩ : syracuseStep 5253083 = 7879625) B7879625
theorem B3502055 : Blo 2073435 3502055 := bstep (se 1 (by rfl) ⟨2626541, by rfl⟩ : syracuseStep 3502055 = 5253083) B5253083
theorem B2334703 : Blo 2073435 2334703 := bstep (se 1 (by rfl) ⟨1751027, by rfl⟩ : syracuseStep 2334703 = 3502055) B3502055
theorem B3112937 : Blo 2073435 3112937 := bstep (se 2 (by rfl) ⟨1167351, by rfl⟩ : syracuseStep 3112937 = 2334703) B2334703
theorem B2075291 : Blo 2073435 2075291 := bstep (se 1 (by rfl) ⟨1556468, by rfl⟩ : syracuseStep 2075291 = 3112937) B3112937
theorem B15974293 : Blo 2073435 15974293 := bbase (se 6 (by rfl) ⟨374397, by rfl⟩ : syracuseStep 15974293 = 748795) (by norm_num)
theorem B21299057 : Blo 2073435 21299057 := bstep (se 2 (by rfl) ⟨7987146, by rfl⟩ : syracuseStep 21299057 = 15974293) B15974293
theorem B14199371 : Blo 2073435 14199371 := bstep (se 1 (by rfl) ⟨10649528, by rfl⟩ : syracuseStep 14199371 = 21299057) B21299057
theorem B9466247 : Blo 2073435 9466247 := bstep (se 1 (by rfl) ⟨7099685, by rfl⟩ : syracuseStep 9466247 = 14199371) B14199371
theorem B25243325 : Blo 2073435 25243325 := bstep (se 3 (by rfl) ⟨4733123, by rfl⟩ : syracuseStep 25243325 = 9466247) B9466247
theorem B16828883 : Blo 2073435 16828883 := bstep (se 1 (by rfl) ⟨12621662, by rfl⟩ : syracuseStep 16828883 = 25243325) B25243325
theorem B11219255 : Blo 2073435 11219255 := bstep (se 1 (by rfl) ⟨8414441, by rfl⟩ : syracuseStep 11219255 = 16828883) B16828883
theorem B7479503 : Blo 2073435 7479503 := bstep (se 1 (by rfl) ⟨5609627, by rfl⟩ : syracuseStep 7479503 = 11219255) B11219255
theorem B4986335 : Blo 2073435 4986335 := bstep (se 1 (by rfl) ⟨3739751, by rfl⟩ : syracuseStep 4986335 = 7479503) B7479503
theorem B3324223 : Blo 2073435 3324223 := bstep (se 1 (by rfl) ⟨2493167, by rfl⟩ : syracuseStep 3324223 = 4986335) B4986335
theorem B17729189 : Blo 2073435 17729189 := bstep (se 4 (by rfl) ⟨1662111, by rfl⟩ : syracuseStep 17729189 = 3324223) B3324223
theorem B11819459 : Blo 2073435 11819459 := bstep (se 1 (by rfl) ⟨8864594, by rfl⟩ : syracuseStep 11819459 = 17729189) B17729189
theorem B7879639 : Blo 2073435 7879639 := bstep (se 1 (by rfl) ⟨5909729, by rfl⟩ : syracuseStep 7879639 = 11819459) B11819459
theorem B10506185 : Blo 2073435 10506185 := bstep (se 2 (by rfl) ⟨3939819, by rfl⟩ : syracuseStep 10506185 = 7879639) B7879639
theorem B7004123 : Blo 2073435 7004123 := bstep (se 1 (by rfl) ⟨5253092, by rfl⟩ : syracuseStep 7004123 = 10506185) B10506185
theorem B4669415 : Blo 2073435 4669415 := bstep (se 1 (by rfl) ⟨3502061, by rfl⟩ : syracuseStep 4669415 = 7004123) B7004123
theorem B3112943 : Blo 2073435 3112943 := bstep (se 1 (by rfl) ⟨2334707, by rfl⟩ : syracuseStep 3112943 = 4669415) B4669415
theorem B2075295 : Blo 2073435 2075295 := bstep (se 1 (by rfl) ⟨1556471, by rfl⟩ : syracuseStep 2075295 = 3112943) B3112943
theorem B3112949 : Blo 2073435 3112949 := bbase (se 5 (by rfl) ⟨145919, by rfl⟩ : syracuseStep 3112949 = 291839) (by norm_num)
theorem B2075299 : Blo 2073435 2075299 := bstep (se 1 (by rfl) ⟨1556474, by rfl⟩ : syracuseStep 2075299 = 3112949) B3112949
theorem B3155429 : Blo 2073435 3155429 := bbase (se 4 (by rfl) ⟨295821, by rfl⟩ : syracuseStep 3155429 = 591643) (by norm_num)
theorem B2103619 : Blo 2073435 2103619 := bstep (se 1 (by rfl) ⟨1577714, by rfl⟩ : syracuseStep 2103619 = 3155429) B3155429
theorem B2804825 : Blo 2073435 2804825 := bstep (se 2 (by rfl) ⟨1051809, by rfl⟩ : syracuseStep 2804825 = 2103619) B2103619
theorem B7479533 : Blo 2073435 7479533 := bstep (se 3 (by rfl) ⟨1402412, by rfl⟩ : syracuseStep 7479533 = 2804825) B2804825
theorem B4986355 : Blo 2073435 4986355 := bstep (se 1 (by rfl) ⟨3739766, by rfl⟩ : syracuseStep 4986355 = 7479533) B7479533
theorem B6648473 : Blo 2073435 6648473 := bstep (se 2 (by rfl) ⟨2493177, by rfl⟩ : syracuseStep 6648473 = 4986355) B4986355
theorem B4432315 : Blo 2073435 4432315 := bstep (se 1 (by rfl) ⟨3324236, by rfl⟩ : syracuseStep 4432315 = 6648473) B6648473
theorem B5909753 : Blo 2073435 5909753 := bstep (se 2 (by rfl) ⟨2216157, by rfl⟩ : syracuseStep 5909753 = 4432315) B4432315
theorem B3939835 : Blo 2073435 3939835 := bstep (se 1 (by rfl) ⟨2954876, by rfl⟩ : syracuseStep 3939835 = 5909753) B5909753
theorem B5253113 : Blo 2073435 5253113 := bstep (se 2 (by rfl) ⟨1969917, by rfl⟩ : syracuseStep 5253113 = 3939835) B3939835
theorem B3502075 : Blo 2073435 3502075 := bstep (se 1 (by rfl) ⟨2626556, by rfl⟩ : syracuseStep 3502075 = 5253113) B5253113
theorem B4669433 : Blo 2073435 4669433 := bstep (se 2 (by rfl) ⟨1751037, by rfl⟩ : syracuseStep 4669433 = 3502075) B3502075
theorem B3112955 : Blo 2073435 3112955 := bstep (se 1 (by rfl) ⟨2334716, by rfl⟩ : syracuseStep 3112955 = 4669433) B4669433
theorem B2075303 : Blo 2073435 2075303 := bstep (se 1 (by rfl) ⟨1556477, by rfl⟩ : syracuseStep 2075303 = 3112955) B3112955
theorem B2334721 : Blo 2073435 2334721 := bbase (se 2 (by rfl) ⟨875520, by rfl⟩ : syracuseStep 2334721 = 1751041) (by norm_num)
theorem B3112961 : Blo 2073435 3112961 := bstep (se 2 (by rfl) ⟨1167360, by rfl⟩ : syracuseStep 3112961 = 2334721) B2334721
theorem B2075307 : Blo 2073435 2075307 := bstep (se 1 (by rfl) ⟨1556480, by rfl⟩ : syracuseStep 2075307 = 3112961) B3112961
theorem B5253133 : Blo 2073435 5253133 := bbase (se 3 (by rfl) ⟨984962, by rfl⟩ : syracuseStep 5253133 = 1969925) (by norm_num)
theorem B7004177 : Blo 2073435 7004177 := bstep (se 2 (by rfl) ⟨2626566, by rfl⟩ : syracuseStep 7004177 = 5253133) B5253133
theorem B4669451 : Blo 2073435 4669451 := bstep (se 1 (by rfl) ⟨3502088, by rfl⟩ : syracuseStep 4669451 = 7004177) B7004177
theorem B3112967 : Blo 2073435 3112967 := bstep (se 1 (by rfl) ⟨2334725, by rfl⟩ : syracuseStep 3112967 = 4669451) B4669451
theorem B2075311 : Blo 2073435 2075311 := bstep (se 1 (by rfl) ⟨1556483, by rfl⟩ : syracuseStep 2075311 = 3112967) B3112967
theorem B3112973 : Blo 2073435 3112973 := bbase (se 3 (by rfl) ⟨583682, by rfl⟩ : syracuseStep 3112973 = 1167365) (by norm_num)
theorem B2075315 : Blo 2073435 2075315 := bstep (se 1 (by rfl) ⟨1556486, by rfl⟩ : syracuseStep 2075315 = 3112973) B3112973
theorem B4669469 : Blo 2073435 4669469 := bbase (se 3 (by rfl) ⟨875525, by rfl⟩ : syracuseStep 4669469 = 1751051) (by norm_num)
theorem B3112979 : Blo 2073435 3112979 := bstep (se 1 (by rfl) ⟨2334734, by rfl⟩ : syracuseStep 3112979 = 4669469) B4669469
theorem B2075319 : Blo 2073435 2075319 := bstep (se 1 (by rfl) ⟨1556489, by rfl⟩ : syracuseStep 2075319 = 3112979) B3112979
theorem B3502109 : Blo 2073435 3502109 := bbase (se 3 (by rfl) ⟨656645, by rfl⟩ : syracuseStep 3502109 = 1313291) (by norm_num)
theorem B2334739 : Blo 2073435 2334739 := bstep (se 1 (by rfl) ⟨1751054, by rfl⟩ : syracuseStep 2334739 = 3502109) B3502109
theorem B3112985 : Blo 2073435 3112985 := bstep (se 2 (by rfl) ⟨1167369, by rfl⟩ : syracuseStep 3112985 = 2334739) B2334739
theorem B2075323 : Blo 2073435 2075323 := bstep (se 1 (by rfl) ⟨1556492, by rfl⟩ : syracuseStep 2075323 = 3112985) B3112985
theorem B4207285 : Blo 2073435 4207285 := bbase (se 5 (by rfl) ⟨197216, by rfl⟩ : syracuseStep 4207285 = 394433) (by norm_num)
theorem B22438853 : Blo 2073435 22438853 := bstep (se 4 (by rfl) ⟨2103642, by rfl⟩ : syracuseStep 22438853 = 4207285) B4207285
theorem B14959235 : Blo 2073435 14959235 := bstep (se 1 (by rfl) ⟨11219426, by rfl⟩ : syracuseStep 14959235 = 22438853) B22438853
theorem B9972823 : Blo 2073435 9972823 := bstep (se 1 (by rfl) ⟨7479617, by rfl⟩ : syracuseStep 9972823 = 14959235) B14959235
theorem B13297097 : Blo 2073435 13297097 := bstep (se 2 (by rfl) ⟨4986411, by rfl⟩ : syracuseStep 13297097 = 9972823) B9972823
theorem B8864731 : Blo 2073435 8864731 := bstep (se 1 (by rfl) ⟨6648548, by rfl⟩ : syracuseStep 8864731 = 13297097) B13297097
theorem B11819641 : Blo 2073435 11819641 := bstep (se 2 (by rfl) ⟨4432365, by rfl⟩ : syracuseStep 11819641 = 8864731) B8864731
theorem B15759521 : Blo 2073435 15759521 := bstep (se 2 (by rfl) ⟨5909820, by rfl⟩ : syracuseStep 15759521 = 11819641) B11819641
theorem B10506347 : Blo 2073435 10506347 := bstep (se 1 (by rfl) ⟨7879760, by rfl⟩ : syracuseStep 10506347 = 15759521) B15759521
theorem B7004231 : Blo 2073435 7004231 := bstep (se 1 (by rfl) ⟨5253173, by rfl⟩ : syracuseStep 7004231 = 10506347) B10506347
theorem B4669487 : Blo 2073435 4669487 := bstep (se 1 (by rfl) ⟨3502115, by rfl⟩ : syracuseStep 4669487 = 7004231) B7004231
theorem B3112991 : Blo 2073435 3112991 := bstep (se 1 (by rfl) ⟨2334743, by rfl⟩ : syracuseStep 3112991 = 4669487) B4669487
theorem B2075327 : Blo 2073435 2075327 := bstep (se 1 (by rfl) ⟨1556495, by rfl⟩ : syracuseStep 2075327 = 3112991) B3112991
theorem B3112997 : Blo 2073435 3112997 := bbase (se 4 (by rfl) ⟨291843, by rfl⟩ : syracuseStep 3112997 = 583687) (by norm_num)
theorem B2075331 : Blo 2073435 2075331 := bstep (se 1 (by rfl) ⟨1556498, by rfl⟩ : syracuseStep 2075331 = 3112997) B3112997
theorem B2626597 : Blo 2073435 2626597 := bbase (se 4 (by rfl) ⟨246243, by rfl⟩ : syracuseStep 2626597 = 492487) (by norm_num)
theorem B3502129 : Blo 2073435 3502129 := bstep (se 2 (by rfl) ⟨1313298, by rfl⟩ : syracuseStep 3502129 = 2626597) B2626597
theorem B4669505 : Blo 2073435 4669505 := bstep (se 2 (by rfl) ⟨1751064, by rfl⟩ : syracuseStep 4669505 = 3502129) B3502129
theorem B3113003 : Blo 2073435 3113003 := bstep (se 1 (by rfl) ⟨2334752, by rfl⟩ : syracuseStep 3113003 = 4669505) B4669505
theorem B2075335 : Blo 2073435 2075335 := bstep (se 1 (by rfl) ⟨1556501, by rfl⟩ : syracuseStep 2075335 = 3113003) B3113003
theorem B2334757 : Blo 2073435 2334757 := bbase (se 4 (by rfl) ⟨218883, by rfl⟩ : syracuseStep 2334757 = 437767) (by norm_num)
theorem B3113009 : Blo 2073435 3113009 := bstep (se 2 (by rfl) ⟨1167378, by rfl⟩ : syracuseStep 3113009 = 2334757) B2334757
theorem B2075339 : Blo 2073435 2075339 := bstep (se 1 (by rfl) ⟨1556504, by rfl⟩ : syracuseStep 2075339 = 3113009) B3113009
theorem B9466469 : Blo 2073435 9466469 := bbase (se 4 (by rfl) ⟨887481, by rfl⟩ : syracuseStep 9466469 = 1774963) (by norm_num)
theorem B6310979 : Blo 2073435 6310979 := bstep (se 1 (by rfl) ⟨4733234, by rfl⟩ : syracuseStep 6310979 = 9466469) B9466469
theorem B4207319 : Blo 2073435 4207319 := bstep (se 1 (by rfl) ⟨3155489, by rfl⟩ : syracuseStep 4207319 = 6310979) B6310979
theorem B2804879 : Blo 2073435 2804879 := bstep (se 1 (by rfl) ⟨2103659, by rfl⟩ : syracuseStep 2804879 = 4207319) B4207319
theorem B7479677 : Blo 2073435 7479677 := bstep (se 3 (by rfl) ⟨1402439, by rfl⟩ : syracuseStep 7479677 = 2804879) B2804879
theorem B4986451 : Blo 2073435 4986451 := bstep (se 1 (by rfl) ⟨3739838, by rfl⟩ : syracuseStep 4986451 = 7479677) B7479677
theorem B6648601 : Blo 2073435 6648601 := bstep (se 2 (by rfl) ⟨2493225, by rfl⟩ : syracuseStep 6648601 = 4986451) B4986451
theorem B8864801 : Blo 2073435 8864801 := bstep (se 2 (by rfl) ⟨3324300, by rfl⟩ : syracuseStep 8864801 = 6648601) B6648601
theorem B5909867 : Blo 2073435 5909867 := bstep (se 1 (by rfl) ⟨4432400, by rfl⟩ : syracuseStep 5909867 = 8864801) B8864801
theorem B3939911 : Blo 2073435 3939911 := bstep (se 1 (by rfl) ⟨2954933, by rfl⟩ : syracuseStep 3939911 = 5909867) B5909867
theorem B2626607 : Blo 2073435 2626607 := bstep (se 1 (by rfl) ⟨1969955, by rfl⟩ : syracuseStep 2626607 = 3939911) B3939911
theorem B7004285 : Blo 2073435 7004285 := bstep (se 3 (by rfl) ⟨1313303, by rfl⟩ : syracuseStep 7004285 = 2626607) B2626607
theorem B4669523 : Blo 2073435 4669523 := bstep (se 1 (by rfl) ⟨3502142, by rfl⟩ : syracuseStep 4669523 = 7004285) B7004285
theorem B3113015 : Blo 2073435 3113015 := bstep (se 1 (by rfl) ⟨2334761, by rfl⟩ : syracuseStep 3113015 = 4669523) B4669523
theorem B2075343 : Blo 2073435 2075343 := bstep (se 1 (by rfl) ⟨1556507, by rfl⟩ : syracuseStep 2075343 = 3113015) B3113015
theorem B3113021 : Blo 2073435 3113021 := bbase (se 3 (by rfl) ⟨583691, by rfl⟩ : syracuseStep 3113021 = 1167383) (by norm_num)
theorem B2075347 : Blo 2073435 2075347 := bstep (se 1 (by rfl) ⟨1556510, by rfl⟩ : syracuseStep 2075347 = 3113021) B3113021
theorem B4669541 : Blo 2073435 4669541 := bbase (se 4 (by rfl) ⟨437769, by rfl⟩ : syracuseStep 4669541 = 875539) (by norm_num)
theorem B3113027 : Blo 2073435 3113027 := bstep (se 1 (by rfl) ⟨2334770, by rfl⟩ : syracuseStep 3113027 = 4669541) B4669541
theorem B2075351 : Blo 2073435 2075351 := bstep (se 1 (by rfl) ⟨1556513, by rfl⟩ : syracuseStep 2075351 = 3113027) B3113027
theorem B5253245 : Blo 2073435 5253245 := bbase (se 3 (by rfl) ⟨984983, by rfl⟩ : syracuseStep 5253245 = 1969967) (by norm_num)
theorem B3502163 : Blo 2073435 3502163 := bstep (se 1 (by rfl) ⟨2626622, by rfl⟩ : syracuseStep 3502163 = 5253245) B5253245
theorem B2334775 : Blo 2073435 2334775 := bstep (se 1 (by rfl) ⟨1751081, by rfl⟩ : syracuseStep 2334775 = 3502163) B3502163
theorem B3113033 : Blo 2073435 3113033 := bstep (se 2 (by rfl) ⟨1167387, by rfl⟩ : syracuseStep 3113033 = 2334775) B2334775
theorem B2075355 : Blo 2073435 2075355 := bstep (se 1 (by rfl) ⟨1556516, by rfl⟩ : syracuseStep 2075355 = 3113033) B3113033
theorem B3939941 : Blo 2073435 3939941 := bbase (se 4 (by rfl) ⟨369369, by rfl⟩ : syracuseStep 3939941 = 738739) (by norm_num)
theorem B10506509 : Blo 2073435 10506509 := bstep (se 3 (by rfl) ⟨1969970, by rfl⟩ : syracuseStep 10506509 = 3939941) B3939941
theorem B7004339 : Blo 2073435 7004339 := bstep (se 1 (by rfl) ⟨5253254, by rfl⟩ : syracuseStep 7004339 = 10506509) B10506509
theorem B4669559 : Blo 2073435 4669559 := bstep (se 1 (by rfl) ⟨3502169, by rfl⟩ : syracuseStep 4669559 = 7004339) B7004339
theorem B3113039 : Blo 2073435 3113039 := bstep (se 1 (by rfl) ⟨2334779, by rfl⟩ : syracuseStep 3113039 = 4669559) B4669559
theorem B2075359 : Blo 2073435 2075359 := bstep (se 1 (by rfl) ⟨1556519, by rfl⟩ : syracuseStep 2075359 = 3113039) B3113039
theorem B3113045 : Blo 2073435 3113045 := bbase (se 8 (by rfl) ⟨18240, by rfl⟩ : syracuseStep 3113045 = 36481) (by norm_num)
theorem B2075363 : Blo 2073435 2075363 := bstep (se 1 (by rfl) ⟨1556522, by rfl⟩ : syracuseStep 2075363 = 3113045) B3113045
theorem B2995285 : Blo 2073435 2995285 := bbase (se 8 (by rfl) ⟨17550, by rfl⟩ : syracuseStep 2995285 = 35101) (by norm_num)
theorem B3993713 : Blo 2073435 3993713 := bstep (se 2 (by rfl) ⟨1497642, by rfl⟩ : syracuseStep 3993713 = 2995285) B2995285
theorem B2662475 : Blo 2073435 2662475 := bstep (se 1 (by rfl) ⟨1996856, by rfl⟩ : syracuseStep 2662475 = 3993713) B3993713
theorem B7099933 : Blo 2073435 7099933 := bstep (se 3 (by rfl) ⟨1331237, by rfl⟩ : syracuseStep 7099933 = 2662475) B2662475
theorem B9466577 : Blo 2073435 9466577 := bstep (se 2 (by rfl) ⟨3549966, by rfl⟩ : syracuseStep 9466577 = 7099933) B7099933
theorem B6311051 : Blo 2073435 6311051 := bstep (se 1 (by rfl) ⟨4733288, by rfl⟩ : syracuseStep 6311051 = 9466577) B9466577
theorem B4207367 : Blo 2073435 4207367 := bstep (se 1 (by rfl) ⟨3155525, by rfl⟩ : syracuseStep 4207367 = 6311051) B6311051
theorem B2804911 : Blo 2073435 2804911 := bstep (se 1 (by rfl) ⟨2103683, by rfl⟩ : syracuseStep 2804911 = 4207367) B4207367
theorem B14959525 : Blo 2073435 14959525 := bstep (se 4 (by rfl) ⟨1402455, by rfl⟩ : syracuseStep 14959525 = 2804911) B2804911
theorem B19946033 : Blo 2073435 19946033 := bstep (se 2 (by rfl) ⟨7479762, by rfl⟩ : syracuseStep 19946033 = 14959525) B14959525
theorem B13297355 : Blo 2073435 13297355 := bstep (se 1 (by rfl) ⟨9973016, by rfl⟩ : syracuseStep 13297355 = 19946033) B19946033
theorem B8864903 : Blo 2073435 8864903 := bstep (se 1 (by rfl) ⟨6648677, by rfl⟩ : syracuseStep 8864903 = 13297355) B13297355
theorem B5909935 : Blo 2073435 5909935 := bstep (se 1 (by rfl) ⟨4432451, by rfl⟩ : syracuseStep 5909935 = 8864903) B8864903
theorem B7879913 : Blo 2073435 7879913 := bstep (se 2 (by rfl) ⟨2954967, by rfl⟩ : syracuseStep 7879913 = 5909935) B5909935
theorem B5253275 : Blo 2073435 5253275 := bstep (se 1 (by rfl) ⟨3939956, by rfl⟩ : syracuseStep 5253275 = 7879913) B7879913
theorem B3502183 : Blo 2073435 3502183 := bstep (se 1 (by rfl) ⟨2626637, by rfl⟩ : syracuseStep 3502183 = 5253275) B5253275
theorem B4669577 : Blo 2073435 4669577 := bstep (se 2 (by rfl) ⟨1751091, by rfl⟩ : syracuseStep 4669577 = 3502183) B3502183
theorem B3113051 : Blo 2073435 3113051 := bstep (se 1 (by rfl) ⟨2334788, by rfl⟩ : syracuseStep 3113051 = 4669577) B4669577
theorem B2075367 : Blo 2073435 2075367 := bstep (se 1 (by rfl) ⟨1556525, by rfl⟩ : syracuseStep 2075367 = 3113051) B3113051
theorem B2334793 : Blo 2073435 2334793 := bbase (se 2 (by rfl) ⟨875547, by rfl⟩ : syracuseStep 2334793 = 1751095) (by norm_num)
theorem B3113057 : Blo 2073435 3113057 := bstep (se 2 (by rfl) ⟨1167396, by rfl⟩ : syracuseStep 3113057 = 2334793) B2334793
theorem B2075371 : Blo 2073435 2075371 := bstep (se 1 (by rfl) ⟨1556528, by rfl⟩ : syracuseStep 2075371 = 3113057) B3113057
theorem B2132393 : Blo 2073435 2132393 := bbase (se 2 (by rfl) ⟨799647, by rfl⟩ : syracuseStep 2132393 = 1599295) (by norm_num)
theorem B5686381 : Blo 2073435 5686381 := bstep (se 3 (by rfl) ⟨1066196, by rfl⟩ : syracuseStep 5686381 = 2132393) B2132393
theorem B30327365 : Blo 2073435 30327365 := bstep (se 4 (by rfl) ⟨2843190, by rfl⟩ : syracuseStep 30327365 = 5686381) B5686381
theorem B20218243 : Blo 2073435 20218243 := bstep (se 1 (by rfl) ⟨15163682, by rfl⟩ : syracuseStep 20218243 = 30327365) B30327365
theorem B26957657 : Blo 2073435 26957657 := bstep (se 2 (by rfl) ⟨10109121, by rfl⟩ : syracuseStep 26957657 = 20218243) B20218243
theorem B71887085 : Blo 2073435 71887085 := bstep (se 3 (by rfl) ⟨13478828, by rfl⟩ : syracuseStep 71887085 = 26957657) B26957657
theorem B47924723 : Blo 2073435 47924723 := bstep (se 1 (by rfl) ⟨35943542, by rfl⟩ : syracuseStep 47924723 = 71887085) B71887085
theorem B31949815 : Blo 2073435 31949815 := bstep (se 1 (by rfl) ⟨23962361, by rfl⟩ : syracuseStep 31949815 = 47924723) B47924723
theorem B42599753 : Blo 2073435 42599753 := bstep (se 2 (by rfl) ⟨15974907, by rfl⟩ : syracuseStep 42599753 = 31949815) B31949815
theorem B28399835 : Blo 2073435 28399835 := bstep (se 1 (by rfl) ⟨21299876, by rfl⟩ : syracuseStep 28399835 = 42599753) B42599753
theorem B18933223 : Blo 2073435 18933223 := bstep (se 1 (by rfl) ⟨14199917, by rfl⟩ : syracuseStep 18933223 = 28399835) B28399835
theorem B25244297 : Blo 2073435 25244297 := bstep (se 2 (by rfl) ⟨9466611, by rfl⟩ : syracuseStep 25244297 = 18933223) B18933223
theorem B16829531 : Blo 2073435 16829531 := bstep (se 1 (by rfl) ⟨12622148, by rfl⟩ : syracuseStep 16829531 = 25244297) B25244297
theorem B11219687 : Blo 2073435 11219687 := bstep (se 1 (by rfl) ⟨8414765, by rfl⟩ : syracuseStep 11219687 = 16829531) B16829531
theorem B7479791 : Blo 2073435 7479791 := bstep (se 1 (by rfl) ⟨5609843, by rfl⟩ : syracuseStep 7479791 = 11219687) B11219687
theorem B4986527 : Blo 2073435 4986527 := bstep (se 1 (by rfl) ⟨3739895, by rfl⟩ : syracuseStep 4986527 = 7479791) B7479791
theorem B13297405 : Blo 2073435 13297405 := bstep (se 3 (by rfl) ⟨2493263, by rfl⟩ : syracuseStep 13297405 = 4986527) B4986527
theorem B17729873 : Blo 2073435 17729873 := bstep (se 2 (by rfl) ⟨6648702, by rfl⟩ : syracuseStep 17729873 = 13297405) B13297405
theorem B11819915 : Blo 2073435 11819915 := bstep (se 1 (by rfl) ⟨8864936, by rfl⟩ : syracuseStep 11819915 = 17729873) B17729873
theorem B7879943 : Blo 2073435 7879943 := bstep (se 1 (by rfl) ⟨5909957, by rfl⟩ : syracuseStep 7879943 = 11819915) B11819915
theorem B5253295 : Blo 2073435 5253295 := bstep (se 1 (by rfl) ⟨3939971, by rfl⟩ : syracuseStep 5253295 = 7879943) B7879943
theorem B7004393 : Blo 2073435 7004393 := bstep (se 2 (by rfl) ⟨2626647, by rfl⟩ : syracuseStep 7004393 = 5253295) B5253295
theorem B4669595 : Blo 2073435 4669595 := bstep (se 1 (by rfl) ⟨3502196, by rfl⟩ : syracuseStep 4669595 = 7004393) B7004393
theorem B3113063 : Blo 2073435 3113063 := bstep (se 1 (by rfl) ⟨2334797, by rfl⟩ : syracuseStep 3113063 = 4669595) B4669595
theorem B2075375 : Blo 2073435 2075375 := bstep (se 1 (by rfl) ⟨1556531, by rfl⟩ : syracuseStep 2075375 = 3113063) B3113063
theorem B3113069 : Blo 2073435 3113069 := bbase (se 3 (by rfl) ⟨583700, by rfl⟩ : syracuseStep 3113069 = 1167401) (by norm_num)
theorem B2075379 : Blo 2073435 2075379 := bstep (se 1 (by rfl) ⟨1556534, by rfl⟩ : syracuseStep 2075379 = 3113069) B3113069
theorem B4669613 : Blo 2073435 4669613 := bbase (se 3 (by rfl) ⟨875552, by rfl⟩ : syracuseStep 4669613 = 1751105) (by norm_num)
theorem B3113075 : Blo 2073435 3113075 := bstep (se 1 (by rfl) ⟨2334806, by rfl⟩ : syracuseStep 3113075 = 4669613) B4669613
theorem B2075383 : Blo 2073435 2075383 := bstep (se 1 (by rfl) ⟨1556537, by rfl⟩ : syracuseStep 2075383 = 3113075) B3113075
theorem B2662501 : Blo 2073435 2662501 := bbase (se 4 (by rfl) ⟨249609, by rfl⟩ : syracuseStep 2662501 = 499219) (by norm_num)
theorem B3550001 : Blo 2073435 3550001 := bstep (se 2 (by rfl) ⟨1331250, by rfl⟩ : syracuseStep 3550001 = 2662501) B2662501
theorem B9466669 : Blo 2073435 9466669 := bstep (se 3 (by rfl) ⟨1775000, by rfl⟩ : syracuseStep 9466669 = 3550001) B3550001
theorem B12622225 : Blo 2073435 12622225 := bstep (se 2 (by rfl) ⟨4733334, by rfl⟩ : syracuseStep 12622225 = 9466669) B9466669
theorem B16829633 : Blo 2073435 16829633 := bstep (se 2 (by rfl) ⟨6311112, by rfl⟩ : syracuseStep 16829633 = 12622225) B12622225
theorem B11219755 : Blo 2073435 11219755 := bstep (se 1 (by rfl) ⟨8414816, by rfl⟩ : syracuseStep 11219755 = 16829633) B16829633
theorem B14959673 : Blo 2073435 14959673 := bstep (se 2 (by rfl) ⟨5609877, by rfl⟩ : syracuseStep 14959673 = 11219755) B11219755
theorem B9973115 : Blo 2073435 9973115 := bstep (se 1 (by rfl) ⟨7479836, by rfl⟩ : syracuseStep 9973115 = 14959673) B14959673
theorem B6648743 : Blo 2073435 6648743 := bstep (se 1 (by rfl) ⟨4986557, by rfl⟩ : syracuseStep 6648743 = 9973115) B9973115
theorem B4432495 : Blo 2073435 4432495 := bstep (se 1 (by rfl) ⟨3324371, by rfl⟩ : syracuseStep 4432495 = 6648743) B6648743
theorem B5909993 : Blo 2073435 5909993 := bstep (se 2 (by rfl) ⟨2216247, by rfl⟩ : syracuseStep 5909993 = 4432495) B4432495
theorem B3939995 : Blo 2073435 3939995 := bstep (se 1 (by rfl) ⟨2954996, by rfl⟩ : syracuseStep 3939995 = 5909993) B5909993
theorem B2626663 : Blo 2073435 2626663 := bstep (se 1 (by rfl) ⟨1969997, by rfl⟩ : syracuseStep 2626663 = 3939995) B3939995
theorem B3502217 : Blo 2073435 3502217 := bstep (se 2 (by rfl) ⟨1313331, by rfl⟩ : syracuseStep 3502217 = 2626663) B2626663
theorem B2334811 : Blo 2073435 2334811 := bstep (se 1 (by rfl) ⟨1751108, by rfl⟩ : syracuseStep 2334811 = 3502217) B3502217
theorem B3113081 : Blo 2073435 3113081 := bstep (se 2 (by rfl) ⟨1167405, by rfl⟩ : syracuseStep 3113081 = 2334811) B2334811
theorem B2075387 : Blo 2073435 2075387 := bstep (se 1 (by rfl) ⟨1556540, by rfl⟩ : syracuseStep 2075387 = 3113081) B3113081
theorem B4986565 : Blo 2073435 4986565 := bbase (se 4 (by rfl) ⟨467490, by rfl⟩ : syracuseStep 4986565 = 934981) (by norm_num)
theorem B26595013 : Blo 2073435 26595013 := bstep (se 4 (by rfl) ⟨2493282, by rfl⟩ : syracuseStep 26595013 = 4986565) B4986565
theorem B35460017 : Blo 2073435 35460017 := bstep (se 2 (by rfl) ⟨13297506, by rfl⟩ : syracuseStep 35460017 = 26595013) B26595013
theorem B23640011 : Blo 2073435 23640011 := bstep (se 1 (by rfl) ⟨17730008, by rfl⟩ : syracuseStep 23640011 = 35460017) B35460017
theorem B15760007 : Blo 2073435 15760007 := bstep (se 1 (by rfl) ⟨11820005, by rfl⟩ : syracuseStep 15760007 = 23640011) B23640011
theorem B10506671 : Blo 2073435 10506671 := bstep (se 1 (by rfl) ⟨7880003, by rfl⟩ : syracuseStep 10506671 = 15760007) B15760007
theorem B7004447 : Blo 2073435 7004447 := bstep (se 1 (by rfl) ⟨5253335, by rfl⟩ : syracuseStep 7004447 = 10506671) B10506671
theorem B4669631 : Blo 2073435 4669631 := bstep (se 1 (by rfl) ⟨3502223, by rfl⟩ : syracuseStep 4669631 = 7004447) B7004447
theorem B3113087 : Blo 2073435 3113087 := bstep (se 1 (by rfl) ⟨2334815, by rfl⟩ : syracuseStep 3113087 = 4669631) B4669631
theorem B2075391 : Blo 2073435 2075391 := bstep (se 1 (by rfl) ⟨1556543, by rfl⟩ : syracuseStep 2075391 = 3113087) B3113087
theorem B3113093 : Blo 2073435 3113093 := bbase (se 4 (by rfl) ⟨291852, by rfl⟩ : syracuseStep 3113093 = 583705) (by norm_num)
theorem B2075395 : Blo 2073435 2075395 := bstep (se 1 (by rfl) ⟨1556546, by rfl⟩ : syracuseStep 2075395 = 3113093) B3113093
theorem B3502237 : Blo 2073435 3502237 := bbase (se 3 (by rfl) ⟨656669, by rfl⟩ : syracuseStep 3502237 = 1313339) (by norm_num)
theorem B4669649 : Blo 2073435 4669649 := bstep (se 2 (by rfl) ⟨1751118, by rfl⟩ : syracuseStep 4669649 = 3502237) B3502237
theorem B3113099 : Blo 2073435 3113099 := bstep (se 1 (by rfl) ⟨2334824, by rfl⟩ : syracuseStep 3113099 = 4669649) B4669649
theorem B2075399 : Blo 2073435 2075399 := bstep (se 1 (by rfl) ⟨1556549, by rfl⟩ : syracuseStep 2075399 = 3113099) B3113099
theorem B2334829 : Blo 2073435 2334829 := bbase (se 3 (by rfl) ⟨437780, by rfl⟩ : syracuseStep 2334829 = 875561) (by norm_num)
theorem B3113105 : Blo 2073435 3113105 := bstep (se 2 (by rfl) ⟨1167414, by rfl⟩ : syracuseStep 3113105 = 2334829) B2334829
theorem B2075403 : Blo 2073435 2075403 := bstep (se 1 (by rfl) ⟨1556552, by rfl⟩ : syracuseStep 2075403 = 3113105) B3113105
theorem B7004501 : Blo 2073435 7004501 := bbase (se 10 (by rfl) ⟨10260, by rfl⟩ : syracuseStep 7004501 = 20521) (by norm_num)
theorem B4669667 : Blo 2073435 4669667 := bstep (se 1 (by rfl) ⟨3502250, by rfl⟩ : syracuseStep 4669667 = 7004501) B7004501
theorem B3113111 : Blo 2073435 3113111 := bstep (se 1 (by rfl) ⟨2334833, by rfl⟩ : syracuseStep 3113111 = 4669667) B4669667
theorem B2075407 : Blo 2073435 2075407 := bstep (se 1 (by rfl) ⟨1556555, by rfl⟩ : syracuseStep 2075407 = 3113111) B3113111
theorem B3113117 : Blo 2073435 3113117 := bbase (se 3 (by rfl) ⟨583709, by rfl⟩ : syracuseStep 3113117 = 1167419) (by norm_num)
theorem B2075411 : Blo 2073435 2075411 := bstep (se 1 (by rfl) ⟨1556558, by rfl⟩ : syracuseStep 2075411 = 3113117) B3113117
theorem B4669685 : Blo 2073435 4669685 := bbase (se 5 (by rfl) ⟨218891, by rfl⟩ : syracuseStep 4669685 = 437783) (by norm_num)
theorem B3113123 : Blo 2073435 3113123 := bstep (se 1 (by rfl) ⟨2334842, by rfl⟩ : syracuseStep 3113123 = 4669685) B4669685
theorem B2075415 : Blo 2073435 2075415 := bstep (se 1 (by rfl) ⟨1556561, by rfl⟩ : syracuseStep 2075415 = 3113123) B3113123
theorem B3842725 : Blo 2073435 3842725 := bbase (se 4 (by rfl) ⟨360255, by rfl⟩ : syracuseStep 3842725 = 720511) (by norm_num)
theorem B5123633 : Blo 2073435 5123633 := bstep (se 2 (by rfl) ⟨1921362, by rfl⟩ : syracuseStep 5123633 = 3842725) B3842725
theorem B13663021 : Blo 2073435 13663021 := bstep (se 3 (by rfl) ⟨2561816, by rfl⟩ : syracuseStep 13663021 = 5123633) B5123633
theorem B18217361 : Blo 2073435 18217361 := bstep (se 2 (by rfl) ⟨6831510, by rfl⟩ : syracuseStep 18217361 = 13663021) B13663021
theorem B12144907 : Blo 2073435 12144907 := bstep (se 1 (by rfl) ⟨9108680, by rfl⟩ : syracuseStep 12144907 = 18217361) B18217361
theorem B16193209 : Blo 2073435 16193209 := bstep (se 2 (by rfl) ⟨6072453, by rfl⟩ : syracuseStep 16193209 = 12144907) B12144907
theorem B21590945 : Blo 2073435 21590945 := bstep (se 2 (by rfl) ⟨8096604, by rfl⟩ : syracuseStep 21590945 = 16193209) B16193209
theorem B14393963 : Blo 2073435 14393963 := bstep (se 1 (by rfl) ⟨10795472, by rfl⟩ : syracuseStep 14393963 = 21590945) B21590945
theorem B38383901 : Blo 2073435 38383901 := bstep (se 3 (by rfl) ⟨7196981, by rfl⟩ : syracuseStep 38383901 = 14393963) B14393963
theorem B25589267 : Blo 2073435 25589267 := bstep (se 1 (by rfl) ⟨19191950, by rfl⟩ : syracuseStep 25589267 = 38383901) B38383901
theorem B17059511 : Blo 2073435 17059511 := bstep (se 1 (by rfl) ⟨12794633, by rfl⟩ : syracuseStep 17059511 = 25589267) B25589267
theorem B45492029 : Blo 2073435 45492029 := bstep (se 3 (by rfl) ⟨8529755, by rfl⟩ : syracuseStep 45492029 = 17059511) B17059511
theorem B30328019 : Blo 2073435 30328019 := bstep (se 1 (by rfl) ⟨22746014, by rfl⟩ : syracuseStep 30328019 = 45492029) B45492029
theorem B20218679 : Blo 2073435 20218679 := bstep (se 1 (by rfl) ⟨15164009, by rfl⟩ : syracuseStep 20218679 = 30328019) B30328019
theorem B13479119 : Blo 2073435 13479119 := bstep (se 1 (by rfl) ⟨10109339, by rfl⟩ : syracuseStep 13479119 = 20218679) B20218679
theorem B8986079 : Blo 2073435 8986079 := bstep (se 1 (by rfl) ⟨6739559, by rfl⟩ : syracuseStep 8986079 = 13479119) B13479119
theorem B23962877 : Blo 2073435 23962877 := bstep (se 3 (by rfl) ⟨4493039, by rfl⟩ : syracuseStep 23962877 = 8986079) B8986079
theorem B15975251 : Blo 2073435 15975251 := bstep (se 1 (by rfl) ⟨11981438, by rfl⟩ : syracuseStep 15975251 = 23962877) B23962877
theorem B10650167 : Blo 2073435 10650167 := bstep (se 1 (by rfl) ⟨7987625, by rfl⟩ : syracuseStep 10650167 = 15975251) B15975251
theorem B7100111 : Blo 2073435 7100111 := bstep (se 1 (by rfl) ⟨5325083, by rfl⟩ : syracuseStep 7100111 = 10650167) B10650167
theorem B4733407 : Blo 2073435 4733407 := bstep (se 1 (by rfl) ⟨3550055, by rfl⟩ : syracuseStep 4733407 = 7100111) B7100111
theorem B6311209 : Blo 2073435 6311209 := bstep (se 2 (by rfl) ⟨2366703, by rfl⟩ : syracuseStep 6311209 = 4733407) B4733407
theorem B8414945 : Blo 2073435 8414945 := bstep (se 2 (by rfl) ⟨3155604, by rfl⟩ : syracuseStep 8414945 = 6311209) B6311209
theorem B5609963 : Blo 2073435 5609963 := bstep (se 1 (by rfl) ⟨4207472, by rfl⟩ : syracuseStep 5609963 = 8414945) B8414945
theorem B3739975 : Blo 2073435 3739975 := bstep (se 1 (by rfl) ⟨2804981, by rfl⟩ : syracuseStep 3739975 = 5609963) B5609963
theorem B19946533 : Blo 2073435 19946533 := bstep (se 4 (by rfl) ⟨1869987, by rfl⟩ : syracuseStep 19946533 = 3739975) B3739975
theorem B26595377 : Blo 2073435 26595377 := bstep (se 2 (by rfl) ⟨9973266, by rfl⟩ : syracuseStep 26595377 = 19946533) B19946533
theorem B17730251 : Blo 2073435 17730251 := bstep (se 1 (by rfl) ⟨13297688, by rfl⟩ : syracuseStep 17730251 = 26595377) B26595377
theorem B11820167 : Blo 2073435 11820167 := bstep (se 1 (by rfl) ⟨8865125, by rfl⟩ : syracuseStep 11820167 = 17730251) B17730251
theorem B7880111 : Blo 2073435 7880111 := bstep (se 1 (by rfl) ⟨5910083, by rfl⟩ : syracuseStep 7880111 = 11820167) B11820167
theorem B5253407 : Blo 2073435 5253407 := bstep (se 1 (by rfl) ⟨3940055, by rfl⟩ : syracuseStep 5253407 = 7880111) B7880111
theorem B3502271 : Blo 2073435 3502271 := bstep (se 1 (by rfl) ⟨2626703, by rfl⟩ : syracuseStep 3502271 = 5253407) B5253407
theorem B2334847 : Blo 2073435 2334847 := bstep (se 1 (by rfl) ⟨1751135, by rfl⟩ : syracuseStep 2334847 = 3502271) B3502271
theorem B3113129 : Blo 2073435 3113129 := bstep (se 2 (by rfl) ⟨1167423, by rfl⟩ : syracuseStep 3113129 = 2334847) B2334847
theorem B2075419 : Blo 2073435 2075419 := bstep (se 1 (by rfl) ⟨1556564, by rfl⟩ : syracuseStep 2075419 = 3113129) B3113129
theorem B5686517 : Blo 2073435 5686517 := bbase (se 5 (by rfl) ⟨266555, by rfl⟩ : syracuseStep 5686517 = 533111) (by norm_num)
theorem B3791011 : Blo 2073435 3791011 := bstep (se 1 (by rfl) ⟨2843258, by rfl⟩ : syracuseStep 3791011 = 5686517) B5686517
theorem B5054681 : Blo 2073435 5054681 := bstep (se 2 (by rfl) ⟨1895505, by rfl⟩ : syracuseStep 5054681 = 3791011) B3791011
theorem B13479149 : Blo 2073435 13479149 := bstep (se 3 (by rfl) ⟨2527340, by rfl⟩ : syracuseStep 13479149 = 5054681) B5054681
theorem B8986099 : Blo 2073435 8986099 := bstep (se 1 (by rfl) ⟨6739574, by rfl⟩ : syracuseStep 8986099 = 13479149) B13479149
theorem B11981465 : Blo 2073435 11981465 := bstep (se 2 (by rfl) ⟨4493049, by rfl⟩ : syracuseStep 11981465 = 8986099) B8986099
theorem B7987643 : Blo 2073435 7987643 := bstep (se 1 (by rfl) ⟨5990732, by rfl⟩ : syracuseStep 7987643 = 11981465) B11981465
theorem B5325095 : Blo 2073435 5325095 := bstep (se 1 (by rfl) ⟨3993821, by rfl⟩ : syracuseStep 5325095 = 7987643) B7987643
theorem B3550063 : Blo 2073435 3550063 := bstep (se 1 (by rfl) ⟨2662547, by rfl⟩ : syracuseStep 3550063 = 5325095) B5325095
theorem B4733417 : Blo 2073435 4733417 := bstep (se 2 (by rfl) ⟨1775031, by rfl⟩ : syracuseStep 4733417 = 3550063) B3550063
theorem B3155611 : Blo 2073435 3155611 := bstep (se 1 (by rfl) ⟨2366708, by rfl⟩ : syracuseStep 3155611 = 4733417) B4733417
theorem B4207481 : Blo 2073435 4207481 := bstep (se 2 (by rfl) ⟨1577805, by rfl⟩ : syracuseStep 4207481 = 3155611) B3155611
theorem B2804987 : Blo 2073435 2804987 := bstep (se 1 (by rfl) ⟨2103740, by rfl⟩ : syracuseStep 2804987 = 4207481) B4207481
theorem B7479965 : Blo 2073435 7479965 := bstep (se 3 (by rfl) ⟨1402493, by rfl⟩ : syracuseStep 7479965 = 2804987) B2804987
theorem B4986643 : Blo 2073435 4986643 := bstep (se 1 (by rfl) ⟨3739982, by rfl⟩ : syracuseStep 4986643 = 7479965) B7479965
theorem B6648857 : Blo 2073435 6648857 := bstep (se 2 (by rfl) ⟨2493321, by rfl⟩ : syracuseStep 6648857 = 4986643) B4986643
theorem B4432571 : Blo 2073435 4432571 := bstep (se 1 (by rfl) ⟨3324428, by rfl⟩ : syracuseStep 4432571 = 6648857) B6648857
theorem B2955047 : Blo 2073435 2955047 := bstep (se 1 (by rfl) ⟨2216285, by rfl⟩ : syracuseStep 2955047 = 4432571) B4432571
theorem B7880125 : Blo 2073435 7880125 := bstep (se 3 (by rfl) ⟨1477523, by rfl⟩ : syracuseStep 7880125 = 2955047) B2955047
theorem B10506833 : Blo 2073435 10506833 := bstep (se 2 (by rfl) ⟨3940062, by rfl⟩ : syracuseStep 10506833 = 7880125) B7880125
theorem B7004555 : Blo 2073435 7004555 := bstep (se 1 (by rfl) ⟨5253416, by rfl⟩ : syracuseStep 7004555 = 10506833) B10506833
theorem B4669703 : Blo 2073435 4669703 := bstep (se 1 (by rfl) ⟨3502277, by rfl⟩ : syracuseStep 4669703 = 7004555) B7004555
theorem B3113135 : Blo 2073435 3113135 := bstep (se 1 (by rfl) ⟨2334851, by rfl⟩ : syracuseStep 3113135 = 4669703) B4669703
theorem B2075423 : Blo 2073435 2075423 := bstep (se 1 (by rfl) ⟨1556567, by rfl⟩ : syracuseStep 2075423 = 3113135) B3113135
theorem B3113141 : Blo 2073435 3113141 := bbase (se 5 (by rfl) ⟨145928, by rfl⟩ : syracuseStep 3113141 = 291857) (by norm_num)
theorem B2075427 : Blo 2073435 2075427 := bstep (se 1 (by rfl) ⟨1556570, by rfl⟩ : syracuseStep 2075427 = 3113141) B3113141
theorem B5253437 : Blo 2073435 5253437 := bbase (se 3 (by rfl) ⟨985019, by rfl⟩ : syracuseStep 5253437 = 1970039) (by norm_num)
theorem B3502291 : Blo 2073435 3502291 := bstep (se 1 (by rfl) ⟨2626718, by rfl⟩ : syracuseStep 3502291 = 5253437) B5253437
theorem B4669721 : Blo 2073435 4669721 := bstep (se 2 (by rfl) ⟨1751145, by rfl⟩ : syracuseStep 4669721 = 3502291) B3502291
theorem B3113147 : Blo 2073435 3113147 := bstep (se 1 (by rfl) ⟨2334860, by rfl⟩ : syracuseStep 3113147 = 4669721) B4669721
theorem B2075431 : Blo 2073435 2075431 := bstep (se 1 (by rfl) ⟨1556573, by rfl⟩ : syracuseStep 2075431 = 3113147) B3113147
theorem B2334865 : Blo 2073435 2334865 := bbase (se 2 (by rfl) ⟨875574, by rfl⟩ : syracuseStep 2334865 = 1751149) (by norm_num)
theorem B3113153 : Blo 2073435 3113153 := bstep (se 2 (by rfl) ⟨1167432, by rfl⟩ : syracuseStep 3113153 = 2334865) B2334865
theorem B2075435 : Blo 2073435 2075435 := bstep (se 1 (by rfl) ⟨1556576, by rfl⟩ : syracuseStep 2075435 = 3113153) B3113153
theorem C0 (j : ℕ) (h1 : 518358 ≤ j) (h2 : j ≤ 518858) : Blo 2073435 (4 * j + 3) := by
  interval_cases j
  · exact B2073435
  · exact B2073439
  · exact B2073443
  · exact B2073447
  · exact B2073451
  · exact B2073455
  · exact B2073459
  · exact B2073463
  · exact B2073467
  · exact B2073471
  · exact B2073475
  · exact B2073479
  · exact B2073483
  · exact B2073487
  · exact B2073491
  · exact B2073495
  · exact B2073499
  · exact B2073503
  · exact B2073507
  · exact B2073511
  · exact B2073515
  · exact B2073519
  · exact B2073523
  · exact B2073527
  · exact B2073531
  · exact B2073535
  · exact B2073539
  · exact B2073543
  · exact B2073547
  · exact B2073551
  · exact B2073555
  · exact B2073559
  · exact B2073563
  · exact B2073567
  · exact B2073571
  · exact B2073575
  · exact B2073579
  · exact B2073583
  · exact B2073587
  · exact B2073591
  · exact B2073595
  · exact B2073599
  · exact B2073603
  · exact B2073607
  · exact B2073611
  · exact B2073615
  · exact B2073619
  · exact B2073623
  · exact B2073627
  · exact B2073631
  · exact B2073635
  · exact B2073639
  · exact B2073643
  · exact B2073647
  · exact B2073651
  · exact B2073655
  · exact B2073659
  · exact B2073663
  · exact B2073667
  · exact B2073671
  · exact B2073675
  · exact B2073679
  · exact B2073683
  · exact B2073687
  · exact B2073691
  · exact B2073695
  · exact B2073699
  · exact B2073703
  · exact B2073707
  · exact B2073711
  · exact B2073715
  · exact B2073719
  · exact B2073723
  · exact B2073727
  · exact B2073731
  · exact B2073735
  · exact B2073739
  · exact B2073743
  · exact B2073747
  · exact B2073751
  · exact B2073755
  · exact B2073759
  · exact B2073763
  · exact B2073767
  · exact B2073771
  · exact B2073775
  · exact B2073779
  · exact B2073783
  · exact B2073787
  · exact B2073791
  · exact B2073795
  · exact B2073799
  · exact B2073803
  · exact B2073807
  · exact B2073811
  · exact B2073815
  · exact B2073819
  · exact B2073823
  · exact B2073827
  · exact B2073831
  · exact B2073835
  · exact B2073839
  · exact B2073843
  · exact B2073847
  · exact B2073851
  · exact B2073855
  · exact B2073859
  · exact B2073863
  · exact B2073867
  · exact B2073871
  · exact B2073875
  · exact B2073879
  · exact B2073883
  · exact B2073887
  · exact B2073891
  · exact B2073895
  · exact B2073899
  · exact B2073903
  · exact B2073907
  · exact B2073911
  · exact B2073915
  · exact B2073919
  · exact B2073923
  · exact B2073927
  · exact B2073931
  · exact B2073935
  · exact B2073939
  · exact B2073943
  · exact B2073947
  · exact B2073951
  · exact B2073955
  · exact B2073959
  · exact B2073963
  · exact B2073967
  · exact B2073971
  · exact B2073975
  · exact B2073979
  · exact B2073983
  · exact B2073987
  · exact B2073991
  · exact B2073995
  · exact B2073999
  · exact B2074003
  · exact B2074007
  · exact B2074011
  · exact B2074015
  · exact B2074019
  · exact B2074023
  · exact B2074027
  · exact B2074031
  · exact B2074035
  · exact B2074039
  · exact B2074043
  · exact B2074047
  · exact B2074051
  · exact B2074055
  · exact B2074059
  · exact B2074063
  · exact B2074067
  · exact B2074071
  · exact B2074075
  · exact B2074079
  · exact B2074083
  · exact B2074087
  · exact B2074091
  · exact B2074095
  · exact B2074099
  · exact B2074103
  · exact B2074107
  · exact B2074111
  · exact B2074115
  · exact B2074119
  · exact B2074123
  · exact B2074127
  · exact B2074131
  · exact B2074135
  · exact B2074139
  · exact B2074143
  · exact B2074147
  · exact B2074151
  · exact B2074155
  · exact B2074159
  · exact B2074163
  · exact B2074167
  · exact B2074171
  · exact B2074175
  · exact B2074179
  · exact B2074183
  · exact B2074187
  · exact B2074191
  · exact B2074195
  · exact B2074199
  · exact B2074203
  · exact B2074207
  · exact B2074211
  · exact B2074215
  · exact B2074219
  · exact B2074223
  · exact B2074227
  · exact B2074231
  · exact B2074235
  · exact B2074239
  · exact B2074243
  · exact B2074247
  · exact B2074251
  · exact B2074255
  · exact B2074259
  · exact B2074263
  · exact B2074267
  · exact B2074271
  · exact B2074275
  · exact B2074279
  · exact B2074283
  · exact B2074287
  · exact B2074291
  · exact B2074295
  · exact B2074299
  · exact B2074303
  · exact B2074307
  · exact B2074311
  · exact B2074315
  · exact B2074319
  · exact B2074323
  · exact B2074327
  · exact B2074331
  · exact B2074335
  · exact B2074339
  · exact B2074343
  · exact B2074347
  · exact B2074351
  · exact B2074355
  · exact B2074359
  · exact B2074363
  · exact B2074367
  · exact B2074371
  · exact B2074375
  · exact B2074379
  · exact B2074383
  · exact B2074387
  · exact B2074391
  · exact B2074395
  · exact B2074399
  · exact B2074403
  · exact B2074407
  · exact B2074411
  · exact B2074415
  · exact B2074419
  · exact B2074423
  · exact B2074427
  · exact B2074431
  · exact B2074435
  · exact B2074439
  · exact B2074443
  · exact B2074447
  · exact B2074451
  · exact B2074455
  · exact B2074459
  · exact B2074463
  · exact B2074467
  · exact B2074471
  · exact B2074475
  · exact B2074479
  · exact B2074483
  · exact B2074487
  · exact B2074491
  · exact B2074495
  · exact B2074499
  · exact B2074503
  · exact B2074507
  · exact B2074511
  · exact B2074515
  · exact B2074519
  · exact B2074523
  · exact B2074527
  · exact B2074531
  · exact B2074535
  · exact B2074539
  · exact B2074543
  · exact B2074547
  · exact B2074551
  · exact B2074555
  · exact B2074559
  · exact B2074563
  · exact B2074567
  · exact B2074571
  · exact B2074575
  · exact B2074579
  · exact B2074583
  · exact B2074587
  · exact B2074591
  · exact B2074595
  · exact B2074599
  · exact B2074603
  · exact B2074607
  · exact B2074611
  · exact B2074615
  · exact B2074619
  · exact B2074623
  · exact B2074627
  · exact B2074631
  · exact B2074635
  · exact B2074639
  · exact B2074643
  · exact B2074647
  · exact B2074651
  · exact B2074655
  · exact B2074659
  · exact B2074663
  · exact B2074667
  · exact B2074671
  · exact B2074675
  · exact B2074679
  · exact B2074683
  · exact B2074687
  · exact B2074691
  · exact B2074695
  · exact B2074699
  · exact B2074703
  · exact B2074707
  · exact B2074711
  · exact B2074715
  · exact B2074719
  · exact B2074723
  · exact B2074727
  · exact B2074731
  · exact B2074735
  · exact B2074739
  · exact B2074743
  · exact B2074747
  · exact B2074751
  · exact B2074755
  · exact B2074759
  · exact B2074763
  · exact B2074767
  · exact B2074771
  · exact B2074775
  · exact B2074779
  · exact B2074783
  · exact B2074787
  · exact B2074791
  · exact B2074795
  · exact B2074799
  · exact B2074803
  · exact B2074807
  · exact B2074811
  · exact B2074815
  · exact B2074819
  · exact B2074823
  · exact B2074827
  · exact B2074831
  · exact B2074835
  · exact B2074839
  · exact B2074843
  · exact B2074847
  · exact B2074851
  · exact B2074855
  · exact B2074859
  · exact B2074863
  · exact B2074867
  · exact B2074871
  · exact B2074875
  · exact B2074879
  · exact B2074883
  · exact B2074887
  · exact B2074891
  · exact B2074895
  · exact B2074899
  · exact B2074903
  · exact B2074907
  · exact B2074911
  · exact B2074915
  · exact B2074919
  · exact B2074923
  · exact B2074927
  · exact B2074931
  · exact B2074935
  · exact B2074939
  · exact B2074943
  · exact B2074947
  · exact B2074951
  · exact B2074955
  · exact B2074959
  · exact B2074963
  · exact B2074967
  · exact B2074971
  · exact B2074975
  · exact B2074979
  · exact B2074983
  · exact B2074987
  · exact B2074991
  · exact B2074995
  · exact B2074999
  · exact B2075003
  · exact B2075007
  · exact B2075011
  · exact B2075015
  · exact B2075019
  · exact B2075023
  · exact B2075027
  · exact B2075031
  · exact B2075035
  · exact B2075039
  · exact B2075043
  · exact B2075047
  · exact B2075051
  · exact B2075055
  · exact B2075059
  · exact B2075063
  · exact B2075067
  · exact B2075071
  · exact B2075075
  · exact B2075079
  · exact B2075083
  · exact B2075087
  · exact B2075091
  · exact B2075095
  · exact B2075099
  · exact B2075103
  · exact B2075107
  · exact B2075111
  · exact B2075115
  · exact B2075119
  · exact B2075123
  · exact B2075127
  · exact B2075131
  · exact B2075135
  · exact B2075139
  · exact B2075143
  · exact B2075147
  · exact B2075151
  · exact B2075155
  · exact B2075159
  · exact B2075163
  · exact B2075167
  · exact B2075171
  · exact B2075175
  · exact B2075179
  · exact B2075183
  · exact B2075187
  · exact B2075191
  · exact B2075195
  · exact B2075199
  · exact B2075203
  · exact B2075207
  · exact B2075211
  · exact B2075215
  · exact B2075219
  · exact B2075223
  · exact B2075227
  · exact B2075231
  · exact B2075235
  · exact B2075239
  · exact B2075243
  · exact B2075247
  · exact B2075251
  · exact B2075255
  · exact B2075259
  · exact B2075263
  · exact B2075267
  · exact B2075271
  · exact B2075275
  · exact B2075279
  · exact B2075283
  · exact B2075287
  · exact B2075291
  · exact B2075295
  · exact B2075299
  · exact B2075303
  · exact B2075307
  · exact B2075311
  · exact B2075315
  · exact B2075319
  · exact B2075323
  · exact B2075327
  · exact B2075331
  · exact B2075335
  · exact B2075339
  · exact B2075343
  · exact B2075347
  · exact B2075351
  · exact B2075355
  · exact B2075359
  · exact B2075363
  · exact B2075367
  · exact B2075371
  · exact B2075375
  · exact B2075379
  · exact B2075383
  · exact B2075387
  · exact B2075391
  · exact B2075395
  · exact B2075399
  · exact B2075403
  · exact B2075407
  · exact B2075411
  · exact B2075415
  · exact B2075419
  · exact B2075423
  · exact B2075427
  · exact B2075431
  · exact B2075435
theorem solution (m : ℕ) (hlo : 2073435 ≤ m) (hhi : m ≤ 2075435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 518358 ≤ j := by omega
    have hj2 : j ≤ 518858 := by omega
    have hb : Blo 2073435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
